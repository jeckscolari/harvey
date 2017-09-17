from datetime import datetime
import requests

event_endpoint = 'http://127.0.0.1:5000/event'


def send_event(event, vars, timestamp=None):
    if not timestamp:
        ts = round(datetime.now().timestamp() * 1000)
    else:
        ts = timestamp
    data = {'event': event, 'timestamp': ts, 'vars': vars}
    headers = {'Content-type': 'application/json'}
    r = requests.post(event_endpoint,
                  json=data, headers=headers)
    print(r.status_code)

