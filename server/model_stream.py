from bisect import *
from datetime import datetime
from model_state import ModelState
from matcher import match_iso


class ModelStream(object):

    def __init__(self, bg_formula):
        init_timestamp = round(datetime.now().timestamp() * 1000)
        self.model_stream = [ModelState(bg_formula=bg_formula, timestamp=init_timestamp)]
        self._insertion_callback = None

    def insort(self, new_state):
        insort(self.model_stream, new_state)
        self._insertion_callback(new_state)

    def get_current_state(self):
        return self.model_stream[-1]

    def set_insertion_callback(self, callback):
        self._insertion_callback = callback

    def update_model_state(self, reaction, timestamp):
        new_state = ModelState(timestamp=timestamp)
        index = bisect_right(self.model_stream, new_state)
        assert index > 0
        prev_state = self.model_stream[index - 1]
        match_results = match_iso(prev_state.bg_model, reaction)
        if match_results:
            new_state.bg_model = match_results[0]
            new_state.derived_from = reaction
            self.insort(new_state)
        else:
            raise ValueError('The reaction {} did not trigger any change in the model.'.format(reaction))
        #TODO: Check if newer states needs to be updated

    def get_stream_from(self, timestamp):
        if self.model_stream:
            return self.model_stream[bisect_left(self.model_stream, ModelState(timestamp=timestamp)):]
        return []

    def get_trace(self, bg_formula, from_timestamp):
        import time

        trace = ''
        while trace == '':
            stream_from = self.get_stream_from(from_timestamp)
            if stream_from:
                ts = stream_from[0].timestamp
                mp = stream_from[0].matching_predicates.get(bg_formula, set())
                for ms in stream_from[1:]:
                    if ms.timestamp == ts:
                        mp |= ms.matching_predicates[bg_formula]
                    else:
                        if mp:
                            trace += '@{} {} '.format(ts, ' '.join(mp))
                        ts = ms.timestamp
                        mp = ms.matching_predicates.get(bg_formula, set())
                if mp:
                    trace += '@{} {}\n'.format(ts, ' '.join(mp))

        return trace

    def __str__(self):
        return '\n'.join(map(str, self.model_stream))

    def get_synthesis(self):
        return '\n\n\n\n'.join(map(lambda ms: ms.get_synthesis(), self.model_stream))