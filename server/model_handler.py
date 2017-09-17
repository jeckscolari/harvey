from model_stream import ModelStream
from monitors_handler import MonitorsHandler
from reactions_handler import ReactionsHandler
import time


class ModelHandler(object):

    def __init__(self, init_state_bg_formula, reactions, safety_window=2):
        self.model_stream = ModelStream(init_state_bg_formula)
        self.monitors_handler = MonitorsHandler()
        self.reactions = ReactionsHandler(reactions)
        self.model_stream.set_insertion_callback(
            lambda new_state: self.monitors_handler.match_model_state(new_state)
        )
        self.monitors_handler.set_add_formula_callback(
            lambda formula: self.model_stream.get_current_state().update_matching_predicates(formula)
        )
        self.safety_window = safety_window

    def get_monitored_formula(self, monitor_id, bg_formula):
        return self.monitors_handler.get_pred_formula(monitor_id, bg_formula)

    def get_formula_signature(self, monitor_id, bg_formula):
        return self.monitors_handler.get_formula_signature(monitor_id, bg_formula)

    def update_model_state(self, event, timestamp, vars):
        reaction = self.reactions.get_reaction(event, vars)
        self.model_stream.update_model_state(reaction, timestamp)

    def get_trace(self, bg_formula, from_timestamp):
        # safety_window
        time.sleep(self.safety_window)
        try:
            return self.model_stream.get_trace(bg_formula, from_timestamp)
        except KeyError:
            raise ValueError('Unrecognized formula {}!'.format(bg_formula))

    def get_synthesis(self):
        return self.model_stream.get_synthesis()
