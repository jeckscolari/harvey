from formula_handler import FormulaHandler


class MonitorsHandler(object):

    def __init__(self):
        self.monitors_to_formula_matcher = dict()
        self._add_formula_callback = None

    def set_add_formula_callback(self, callback):
        self._add_formula_callback = callback

    def get_formula_handler(self, monitor_id, bg_formula):
        if self.monitors_to_formula_matcher.get(monitor_id, None):
            if self.monitors_to_formula_matcher[monitor_id].get(bg_formula, None):
                return self.monitors_to_formula_matcher[monitor_id][bg_formula]
            else:
                self.monitors_to_formula_matcher[monitor_id][bg_formula] = FormulaHandler(bg_formula)
                self._add_formula_callback(self.monitors_to_formula_matcher[monitor_id])
                return self.monitors_to_formula_matcher[monitor_id][bg_formula]
        else:
            self.monitors_to_formula_matcher[monitor_id] = {bg_formula: FormulaHandler(bg_formula)}
            self._add_formula_callback(self.monitors_to_formula_matcher[monitor_id])
            return self.monitors_to_formula_matcher[monitor_id][bg_formula]

    def get_pred_formula(self, monitor_id, bg_formula):
        return self.get_formula_handler(monitor_id, bg_formula).pred_formula

    def get_formula_signature(self, monitor_id, bg_formula):
        return self.get_formula_handler(monitor_id, bg_formula).signature

    def match_model_state(self, model_state):
        for f in self.monitors_to_formula_matcher.values():
            model_state.update_matching_predicates(f)