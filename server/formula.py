import logging
import re

from pyparsing import ParseException

from matcher import Bigraph
from property import PropertyFactory


class FormulaMatcher(object):

    def __init__(self, formula):
        md = create_match_dict(formula)
        self.bg2md = {formula: md}
        self.bg2pred = {formula: map_formula_from_dict(formula, md)}

    def get_bigraph_to_match_dict_iterator(self):
        return self.bg2md.items()

    def get_predicate_formula(self, formula):
        return self.bg2pred.get(formula, None)

    def get_match_dict(self, formula):
        return self.bg2md.get(formula, None)

    def add_formula(self, formula):
        md = create_match_dict(formula)
        self.bg2md[formula] = md
        self.bg2pred[formula] = map_formula_from_dict(formula, md)


def parse_formula(formula):
    bigraphs = list()
    first, last = -1, -1
    i = 0
    while i < len(formula):
        if formula[i] == '.' and formula[i + 1] == '(':
            open_br = 0
            for j in range(i + 1, len(formula)):
                if formula[j] == '(':
                    open_br += 1
                elif formula[j] == ')':
                    open_br -= 1
                if open_br == 0:
                    last = j
                    break
            k = i
            while formula[k] != ' ' and k > 0:
                k -= 1
            first = k + 1 if k > 0 else k
        i += 1
        if first != -1 and last != -1:
            bigraphs.append(formula[first:last + 1])
            first = -1
            i = last
            last = -1
    return bigraphs


def create_match_dict(formula):
    bigraphs = parse_formula(formula)
    PropertyFactory.init()
    match_dict = dict()
    for b in bigraphs:
        p = PropertyFactory.get_property(b)
        match_dict[b] = p
    return match_dict


def map_formula_from_dict(formula, match_dict):
    for b in match_dict:
        formula = formula.replace(b, match_dict[b].mfotl_name, 1)
    # monpoly parser doesn't digest '@'!
    formula = formula.replace('@', '')
    return formula


def map_formula(formula):
    re.sub('\n| +', ' ', formula)
    md = create_match_dict(formula)
    return map_formula_from_dict(formula, md)


def match_bigraph(bigraph, match_dict):
    matches = list()
    try:
        for prop in match_dict.values():
            match = prop.match_iso(bigraph)
            if match:
                if type(match) == bool:
                    pred = prop.instantiate()
                    matches.append(pred)
                else:
                    for m in match:
                        pred = prop.instantiate(m)
                        matches.append(pred)
        return matches
    except ParseException as e:
        logging.warning('Bigraph formula parsing error: {}'.format(e))



def get_signature(match_dict):
    return {p.sig_name for p in match_dict.values()}


if __name__ == '__main__':
    formula = "NOT City.(Road[@_1].(Bike[@b].(User[@u]) | $1) | $2) SINCE(30,*] City.(Road[@_1].(Bike[@b].(User[@u]) | $1) | $2)"

