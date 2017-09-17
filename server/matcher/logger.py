from pprint import pprint, pformat


DEBUG=False
# DEBUG = True  


def lg(msg, msg2=None, msg3=None, msg4=None):
    if DEBUG:
        for line in pformat(msg).split('\n'):
            if msg2:
                print(line, end=' ')
            else:
                print(line)
        if msg2:
            for line in pformat(msg2).split('\n'):
                if msg3:
                    print(line, end=' ')
                else:
                    print(line)
        if msg3:
            for line in pformat(msg3).split('\n'):
                if msg4:
                    print(line, end=' ')
                else:
                    print(line)
        if msg4:
            for line in pformat(msg4).split('\n'):
                print(line)
