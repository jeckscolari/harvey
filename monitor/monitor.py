from datetime import datetime
import requests
import subprocess
import sys
import os


formula_endpoint = 'http://127.0.0.1:5000/formula'
signature_endpoint = 'http://127.0.0.1:5000/signature'


dir_path = os.path.dirname(os.path.realpath(__file__)) + "/files"


def map_formula(formula):
    params = {'formula': formula}
    r = requests.get(formula_endpoint, params=params)
    if r.status_code == 200:
        return r.text
    else:
        raise ValueError(r.text)


def get_signature(formula):
    params = {'formula': formula}
    r = requests.get(signature_endpoint, params=params)
    if r.status_code == 200:
        return r.text
    else:
        raise ValueError(r.text)


def run(formula, negate=False):
    mfotl = map_formula(formula)
    print("The MFTOL formula is:\n\n\t" + mfotl + "\n")

    sig = get_signature(formula)
    print("Its signature is:\n\n\t" + sig + "\n")


    with open(dir_path + "/files" + exec_id + '.mfotl', 'w+') as mfotl_file:
        mfotl_file.write(mfotl)

    with open(dir_path + "/files" + exec_id + '.sig', 'w+') as sig_file:
        sig_file.write(sig)

    with open(dir_path + "/files" + exec_id + '.log', 'w+') as log_file:
        log_file.write('\n')

    monitor = os.path.dirname(os.path.realpath(__file__)) + '/monpoly-2.0.0/main.native'
    args = [monitor, '-sig', dir_path + "/" + exec_id + '.sig'
            ,'-formula', dir_path + "/" + exec_id + '.mfotl'
            ,'-log', dir_path + "/" + exec_id + '.log'
            ,'-negate' if negate else '']

    subprocess.call(args)

def start(bg_formula):

    with open(dir_path + '/.formula.bg', 'w+') as f_file:
        f_file.write(bg_formula)

    exec_id = 'harvey' + str(round(datetime.now().timestamp() * 1000))

    print("Monitoring formula:\n\n\t" + bg_formula + "\n" )

    run(bg_formula, negate=False)


if __name__ == '__main__':
    formula_path = sys.argv[1]

    with open(formula_path, 'r') as fp:
        bg_formula = fp.readline()
    
    start(bg_formula)
