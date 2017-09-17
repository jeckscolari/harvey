from .acexp import Bigraph
from . import helpers


class RxProp:
    """ class holding either redex and reactum or a redex serving as a property. """

    def __str__(self):
        if self.name:
            return self.name
        return self.redex.formula_compact + "->" + self.reactum.formula_compact

    def __init__(self, expression=None, name=None, probability=None, reward=None, appl_cond=None, who=None):
        self.name = None
        self.roots_props = []
        self.roots_res = []
        self.roots_acexp = []
        self.probability = probability
        self.reward = reward
        self.appl_cond = appl_cond
        self.who = who

        if who:
            # replace @fakedroneid with who in formula
            expression = expression.replace("@fakedroneid", who)

        # # create dummy stuff
        self.reactum = Bigraph("dummy")
        if expression:
            if '->' in expression:
                self.expression = expression
                self.is_property = False
                if expression.startswith('(') and expression.endswith(')'):
                    expression = expression[1:-1]
                redex_formula = expression.split('->')[0]
                reactum_formula = expression.split('->')[1]

                self.redex = Bigraph(redex_formula)
                self.reactum = Bigraph(reactum_formula)
            else:
                # its a property:
                self.redex = Bigraph(expression)
                # dummy reactum FIX ME
                self.reactum = Bigraph("dummy")
                self.is_property = True
        if name:
            self.name = name

        else:
            self.name = str(self)
        self.redex.reaction_name = self.name

    def get_variables(self):
        return self.redex.get_variables()

    @property
    def has_variables(self):
        return self.redex.has_variables()

    @property
    def count_variables(self):
        return self.redex.count_variables()

    @property
    def is_reflexive(self):
        return self.redex == self.reactum

    @property
    def formula(self):
        return self.redex.formula + " -> " + self.reactum.formula

    def __eq__(self, other):
        return self.redex == other.redex and self.reactum == other.reactum and self.name == other.name

    def __ne__(self, other):
        return not self.__eq__(other)


