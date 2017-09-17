from matcher.delimiters import *


class Proposition(list):
    def __str__(self):
        pstr = str(self.id) + PROP_INT_DELIM
        if self.sp is not None:
            pstr += ','.join(self.sp) + PROP_INT_DELIM
        else:
            pstr += "None" + PROP_INT_DELIM

        if self.li is not None:
            pstr += ','.join(self.li)
        else:
            pstr += "None"
        return pstr

    # > def __init__(self):

    @property
    def is_world(self):
        return 'world' in self[0]

    @property
    def id(self):
        return self[0]

    @id.setter
    def id(self, value):
        self[0] = value

    @property
    def sp(self):
        try:
            return self[1]
        except IndexError:
            return None

    @sp.setter
    def sp(self, value):
        self[1] = value

    @property
    def li(self):
        try:
            return self[2]
        except IndexError:
            return None

    @li.setter
    def li(self, value):
        self[2] = value



        # > def as_string(self):
        # > def __hash__(self):
