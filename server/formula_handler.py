from formula import *


class FormulaHandler(object):

    def __init__(self, bg_formula):
        self.bg_formula = bg_formula
        self.match_dict = create_match_dict(bg_formula)
        self.pred_formula = map_formula_from_dict(bg_formula, self.match_dict)
        self.signature = " ".join([p.sig_name for p in self.match_dict.values()])


if __name__ == '__main__':
    bg_formula = "NOT City.(Road[@_1].(Bike[@b].(User[@u] | End) | $1) | $2) SINCE(30,*) City.(Road[@_2].(Bike[@b].(User[@u] | Start) | $1) | $2)"
    fh = FormulaHandler(bg_formula)

    print(fh.pred_formula)