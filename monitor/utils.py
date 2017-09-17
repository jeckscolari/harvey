import requests
import os

trace_endpoint = 'http://127.0.0.1:5000/trace'

formula_path = os.path.dirname(os.path.realpath(__file__)) + "/.formula.bg"
with open(formula_path, 'r') as fp:
    bg_formula = fp.readline()


def get_trace(from_timestamp=None):
    params = {'formula': bg_formula}
    if from_timestamp:
        params['from'] = from_timestamp
    r = requests.get(trace_endpoint, params=params)
    if r.status_code == 200:
        return r.text
    else:
        print(r.text)


