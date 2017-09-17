from matcher import RxProp
import re


class ReactionsHandler(object):

    def __init__(self, reactions):
        self.reactions_by_name = reactions
        self.rx_props = dict()

    def get_reaction(self, event, vars):
        try:
            r = self.reactions_by_name[event]
        except KeyError:
            raise ValueError('The event {} is unknown and will be ignored!'.format(event))
        r = re.sub('|'.join(vars.keys()), lambda x: vars[x.group()], r)
        if not self.rx_props.get(r, None):
            self.rx_props[r] = RxProp(r)
        return self.rx_props[r]
