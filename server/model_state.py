from formula import match_bigraph
from matcher import Bigraph


class ModelState(object):

    def __init__(self, bg_formula=None, derived_from=None, timestamp=-1):
        self.bg_model = Bigraph(bg_formula)
        self.derived_from = derived_from
        self.timestamp = timestamp
        self.matching_predicates = dict()

    def update_matching_predicates(self, formula):
        for fh in formula.values():
            match_dict = fh.match_dict
            bg_formula = fh.bg_formula
            if self.matching_predicates.get(bg_formula):
                self.matching_predicates[bg_formula] |= set(match_bigraph(self.bg_model, match_dict))
            else:
                self.matching_predicates[bg_formula] = set(match_bigraph(self.bg_model, match_dict))

    def __lt__(self, other):
        return self.timestamp.__lt__(other.timestamp)

    def __gt__(self, other):
        return self.timestamp.__gt__(other.timestamp)

    def __str__(self):
        return '@{} {}'.format(self.timestamp, self.bg_model)

    def __repr__(self):
        return '@{} {}'.format(self.timestamp, self.bg_model)

    def get_synthesis(self):
        return 'Bigraph: {}\n' \
               'Derived from: {}\n' \
               'Timestamp: {}\n' \
               'Matching predicates:\n' \
               '{}'.format(self.bg_model,
                           self.derived_from,
                           self.timestamp,
                           '\n'.join(['{} -> {}'.format(k, v)
                                      for k, v in self.matching_predicates.items()]))