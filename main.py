from dataclasses import dataclass
from typing import List, Set, Dict


@dataclass(order=True, frozen=True)
class Literal:
    """Class for keeping track Literals in the KB"""
    name: str
    sign: bool = True

    def __neg__(self):
        """returns negated literal of same name"""
        return Literal(self.name, not self.sign)


# helpers
def get_lits(kb):
    """finds all literals in KB returns as set of positives"""
    return set().union(*kb)


def substitute(name, value, kb):
    """returns a new KB with value substituted for literals with name"""
    return [{(x if x.name != name else x.sign == value) for x in c} for c in kb]


def one_of(s):
    """returns one item from an iterable without removing it"""
    return s.__iter__().__next__()


# heuristics
def pure(lit, kb):
    """whether lit is a pure symbol in KB"""
    lits = get_lits(kb)
    return lit in lits and -lit not in lits


def unit(lit, kb):
    """whether lit is in a unit clause in KB"""
    return {lit} in kb


def degree(lit, kb):
    """the number of times lit or -lit appears in KB"""
    return sum(lit in clause or -lit in clause for clause in kb)


# dpll

def _dpll(kb, model, stuff):
    """the dpll algorithm, a recursive function for internal use"""

    h_lvl = stuff['h_lvl']

    # housekeeping
    kb = [{lit for lit in clause if lit} for clause in kb if True not in clause]

    # check if we're done
    if not kb:  # look if all clauses are resolved True (have been removed)
        stuff['model'].update(model)  # save the winning model to context variable
        return True
    elif any(not clause for clause in kb):  # look for empty clauses
        return False

    # freebie
    if h_lvl >= 2:

        # find all, sort alphabetically
        candidates = sorted([x for x in get_lits(kb) if pure(x, kb) or unit(x, kb)])

        # pick most commonly occuring candidate
        # sorted() is stable, so alphabetic order is preserved among equal degree literals
        if h_lvl == 3:
            candidates = sorted(candidates, key=lambda l: degree(l, kb), reverse=True)

        if candidates:
            # take the first by alphabetical order
            # if-statement above tells us there is at least one item
            sub = candidates[0]

            # push it to the trace and make the substitution
            stuff['trace'].append(sub)
            return _dpll(
                kb=substitute(sub.name, sub.sign, kb),
                model={**model, sub.name: sub.sign},
                stuff=stuff
            )

    # branch
    if h_lvl >= 1:
        # if allowed, use degree heuristic
        # this sorts by degree, then alphabetically
        # we know there is at least one item, since we checked earlier KB is nonempty
        sub = sorted(sorted(get_lits(kb)), key=lambda l: degree(l, kb), reverse=True)[0]

        # pretty proud of this^

    else:
        # otherwise pick an arbitrary one
        sub = one_of(get_lits(kb))

    # push it to the trace and try both substitutions
    stuff['trace'].append(sub)
    return (
            _dpll(substitute(sub.name, True, kb), {**model, sub.name: True}, stuff) or
            _dpll(substitute(sub.name, False, kb), {**model, sub.name: False}, stuff)
    )


def dpll_satisfiable(kb: List[Set[Literal]], heuristic_level: int = 0) -> (bool, Dict[Literal, bool], List[Literal]):
    """Takes in a KB and returns whether the KB is satisfiable, and the model that makes it so

    Args:
        kb: A knowledge base of clauses (CNF) consisting of a list of sets of literals e.g. [{A,B},{-A,C,D}]
        heuristic_level: which heuristics to implement, default 0

    Returns:
        satisfiable: Returns True if the KB is satisfiable, or False otherwise
        model: A dictionary that assigns a truth value to each literal for the model that satisfies KB e.g.
            {A: True, B: False}
        trace: the order in which assignments were made
    """

    # recursive calls will modify this dict as information accumulates
    stf = {'model': {}, 'trace': [], 'h_lvl': heuristic_level}

    # call algorithm
    return (
        _dpll(kb, {}, stf),
        {Literal(k): v for k, v in stf['model'].items()},
        stf['trace']
    )
