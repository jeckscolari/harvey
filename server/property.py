# -*- coding: utf-8 -*-
import logging
from itertools import count

from matcher import RxProp, match_iso


class _PropertyName(object):

    def __init__(self, id, vars):
        _prefix = 'P'
        _var_type = 'string'
        prefix = _prefix + str(id)
        std_vars = [w for w in vars if not w.startswith('_', 1)]
        self.sig_name = prefix + '(' + \
            ','.join([v.replace('@', '') + ':' + _var_type for v in std_vars[:]]) + \
            ')'
        self.mfotl_name = prefix + '(' + \
            ','.join([v.replace('@', '') for v in std_vars[:]]) + \
            ')'
        self.trace_name = prefix + '(' + ','.join(std_vars[:]) + ')'

    def instance(self, values_dict=None):
        instance = self.trace_name
        if values_dict:
            for k, v in values_dict.items():
                instance = instance.replace(k, '"' + v + '"')
        return instance

    def replace_names(self, sig, mfotl, trace):
        self.sig_name = sig
        self.mfotl_name = mfotl
        self.trace_name = trace


class _Property(object):

    def __init__(self, bigraph, id):
        self.bigraph = bigraph
        self.rx_prop = RxProp(self.bigraph)
        self.graph_repr = self.rx_prop.redex.graph_repr
        self.has_variable = self.rx_prop.has_variables
        '''self.nodes_ports_dict = dict()
        for k, v in self.graph_repr.node.items():
            if 'ports' in v:
                self.nodes_ports_dict[k] = v['ports']'''
        self.name = _PropertyName(id=id, vars=self.rx_prop.get_variables())

    def __eq__(self, other):
        return self.rx_prop.redex == other.rx_prop.redex

    def __ne__(self, other):
        return not self.__eq__(other)

    def is_instance_of(self, other):
        return match_iso(self.rx_prop.redex, other.rx_prop, which_variables=True)

    def instantiate(self, values_dict=None):
        instance = self.name.instance(values_dict)
        logging.debug('Instance created: %s', instance)
        return instance

    def match_iso(self, model):
        match = match_iso(model, self.rx_prop, which_variables=True)
        if type(match) == bool:
            return match
        for i in range(len(match)):
            m = match[i]
            match[i] = {k: v for k, v in m.items() if not k.startswith('_', 1)}
        return match

    def replace_names(self, sig, mfotl, trace):
        self.name.replace_names(sig, mfotl, trace)

    @property
    def sig_name(self):
        return self.name.sig_name

    @property
    def mfotl_name(self):
        return self.name.mfotl_name

    @property
    def trace_name(self):
        return self.name.trace_name


class PropertyFactory(object):

    _rx_props = list()
    _ids = count(0)

    @staticmethod
    def init():
        global _rx_props, _ids
        _rx_props = list()
        _ids = count(0)

    @staticmethod
    def get_property(bigraph):
        global _rx_props, _ids
        p = _Property(bigraph=bigraph, id=str(next(_ids)))
        _rx_props.append(p)
        return p


