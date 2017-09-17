from flask import Flask, make_response, request
from model_handler import ModelHandler
from pyparsing import ParseException
import os
import re
import yaml


app = Flask(__name__)


def _clean_formula(formula):
    formula = re.sub('\n| +', ' ', formula)
    formula = formula.lstrip('"')
    formula = formula.rstrip('"')
    return formula


@app.route('/formula', methods=['GET'])
def get_pred_formula():
    bg_formula = request.args.get('formula')
    if not bg_formula:
        return make_response('No formula provided!', 400, )
    bg_formula = _clean_formula(bg_formula)
    monitor_addr = request.environ['REMOTE_ADDR']
    try:
        res = model_handler.get_monitored_formula(monitor_addr, bg_formula)
        return res
    except ParseException as e:
        return make_response(str(e), 400, )


@app.route('/signature', methods=['GET'])
def get_formula_signature():
    bg_formula = request.args.get('formula')
    if not bg_formula:
        return make_response('No formula provided!', 400, )
    bg_formula = _clean_formula(bg_formula)
    monitor_addr = request.environ['REMOTE_ADDR']
    try:
        res = model_handler.get_formula_signature(monitor_addr, bg_formula)
        return res
    except KeyError as e:
        return make_response('Unknown formula!', 400, )


@app.route('/event', methods=['POST'])
def post_event():
    data = request.json
    event = data.get('event', None)
    timestamp = data.get('timestamp', None)
    vars = data.get('vars', None)
    if not event:
        return make_response('No event provided!', 400, )
    if not timestamp:
        return make_response('No timestamp provided!', 400, )
    try:
        model_handler.update_model_state(event, int(timestamp), vars)
        return make_response('Model updated successfully!', 200, )
    except KeyError as e:
        return make_response(str(e), 400, )
    except ValueError as e:
        return make_response(str(e), 400, )


@app.route('/trace', methods=['GET'])
def get_trace():
    bg_formula = request.args.get('formula')
    from_timestamp = float(request.args.get('from'))
    if not bg_formula:
        return make_response('No formula provided!', 400, )
    bg_formula = _clean_formula(bg_formula)
    if not from_timestamp:
        from_timestamp = -1
    try:
        return model_handler.get_trace(bg_formula, from_timestamp)
    except ValueError as e:
        return make_response(str(e), 400, )


@app.route('/debug', methods = ['GET'])
def get_model_synthesis():
    return model_handler.get_synthesis()


def run():
    app.run(threaded=True)


if __name__ == '__main__':
    sfty_window = 2 # safety window of 2 seconds
    model_path = os.path.dirname(os.path.realpath(__file__)) + "/model.yaml"
    with open(model_path, 'rt') as f:
        cfg = yaml.safe_load(f)
    assert cfg is not None
    model_bg = _clean_formula(cfg['model'])
    reactions = {r['reaction']['name']: r['reaction']['formula'] for r in cfg['reactions']}
    model_handler = ModelHandler(model_bg, reactions, safety_window=sfty_window)
    run()
