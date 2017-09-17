# -*- coding: utf-8 -*-
from pyparsing import *
import pprint
import networkx as nx
import copy
import time
__version__ = 0.01
from matcher.helpers import atomset, flatten, frozendict, draw_dot
from matcher.checks2 import eq_overload_wildcard
from matcher.delimiters import PROPOSITIONS_DELIMITER
from .proposition import *
from .ast_cache import *
import random
from operator import eq

ParserElement.enablePackrat()
naming_counter = 1

class Bigraph:
    """ Main Class representing a bigraph. """
    def __init__(self, expression=None, props=None, input_graph=None):
        global AST_CACHE
        self.nodes_list = []
        self.ports_list = []
        self.sites_list = []
        self.res = None
        self.identity = {}

        graph_repr = nx.DiGraph()
        # all props of Bigraph instance, including root props (equivalent to
        # encapsulating to a world node)
        self.props = []
        # ast's of roots
        self.roots_res = []
        # props of roots, without the root props themselves TODO roots
        self.roots_props = []

        # was this bigraph created from another? if so, here is the label.
        incoming_label = None

        # hold closure space here, handle it later for now
        self.closure_space = None

        # TODO: roots support
        if isinstance(expression, str):

            # hack, fix me
            if PROPOSITIONS_DELIMITER in expression:
                self.read_props(expression)

            # roots get treated differently
            elif '||' in expression:
                if expression.startswith('(') and expression.endswith(')'):
                    expression = expression[1:-1]
                root_formulas = expression.split('||')
                for root_formula in root_formulas:
                    f = self.parse_expression(
                        '(' + root_formula + ')').asList()[0]
                    f = self.uniquify_ast(f)
                    self.roots_res.append(f)
                # create props for the roots
                for idx, root_res in enumerate(self.roots_res):
                    p = self.make_props(root_res)
                    self.roots_props.append(p)
                    # keep them also at props
                    self.props += p
                    # hack, fix me
                    self.props += [
                        ['root' + str(idx), [x for x in root_res if isinstance(x, str) and x != '.'], None]]
                # add a world prop containing the roots:
                world_id = self.node_uniquefy("world")
                self.identity[world_id] = "world"
                self.props += [[world_id, [r[0]
                                           for r in self.props if "root" in r[0]], None]]
            else:
                # embed to world
                if expression.startswith("("):
                    expression = "(world. " + expression + " )"
                else:
                    expression = "(world.( " + expression + " ))"
                if ENABLE_CACHE:
                    if expression in AST_CACHE:
                        self.res = AST_CACHE[expression][0]
                        self.ports_list = AST_CACHE[expression][1]
                        self.sites_list = AST_CACHE[expression][2]
                        self.nodes_list = AST_CACHE[expression][3]
                        self.props = copy.deepcopy(AST_CACHE[expression][4])
                        self.identity = AST_CACHE[expression][5]
                    else:
                        # parse
                        try:
                            self.res = self.parse_expression(
                                expression).asList()[0]
                        except ParseException as e:
                            print("Bigraph formula parsing error:", e)
                            print(expression)
                            # exit(0)
                        self.uniquify_ast(self.res)
                        self.props = self.make_props(self.res)
                        to_cache = copy.deepcopy(self.res)
                        AST_CACHE[expression] = [to_cache, self.ports_list, self.sites_list, self.nodes_list, copy.deepcopy(
                            self.props), copy.deepcopy(self.identity)]
                else:
                    self.res = self.parse_expression(expression).asList()[0]
                    self.uniquify_ast(self.res)
                    self.props = self.make_props(self.res)
                self.graph_repr = self.make_graph()
        elif isinstance(expression, nx.classes.digraph.DiGraph) or input_graph:
            input_graph = expression
            self.from_input_graph(expression)

    def __str__(self):
        return self.formula

    def __repr__(self):
        return self.formula

    def __eq__(self, other):
        """ this version checks for isomorphism """
        node_matcher = nx.algorithms.isomorphism.generic_node_match(
            ['control', 'ports'], [None, None], [eq, eq_overload_wildcard])
        return nx.is_isomorphic(self.graph_repr, other.graph_repr, node_match=node_matcher)

    def __ne__(self, other):
        return not self.__eq__(other)

    def get_variables(self):
        vs = {k: 1 for k in self.ports_list if "@" in k}
        return list(vs.keys())

    def has_variables(self):
        return self.count_variables() > 0

    def count_variables(self):
        return len(self.get_variables())

    @property
    def connected_ports(self):
        """ get ports that appeared more than once, so they must be connected"""
        return set([x for x in self.ports_list if self.ports_list.count(x) > 1])

    @property
    def formula(self):
        formula = self.make_formula()
        # clean up, should be elsewhere
        self.formula_graph = None
        return formula

    @property
    def sites(self):
        return set(self.sites_list)

    @property
    def formula_compact(self):
        return self.make_formula(compact=True)

    @property
    def size(self):
        """ size of the bg in nodes and ports"""
        ports = [n_d for n_d in self.graph_repr.nodes(data=True) if n_d[1].get('ports', 0)]
        return len(self.graph_repr) + len(ports)

    def control_of(self, identifier):
        try:
            return self.identity[identifier]
        except KeyError:
            return None

    def prop_with_id(self, ident):
        return next((x for x in self.props if x[0] == ident), None)

    def children_props(self, node):
        """ get a node prop and descendant props of a node.  that is,
        all children and their props, recursively till the end;
        assume that the children exist
        """
        res = []
        p = self.prop_with_id(node)
        res.append(p)
        for child in atomset(p[1]):
            rec = self.children_props(child)
            for r in rec:
                res.append(r)
        return res

    def node_uniquefy(self, node):
        global naming_counter
        naming_counter += 1
        return node + '_' + str(naming_counter)

    def port_action(self, s, l, t):
        self.ports_list.append(t[0])
        return t

    def debug_action(self, s, l, t):
        print("debug parse action", t)
        return t

    def node_action(self, s, l, t):
        if '$' in t[0]:
            t[0] = t[0].replace("$", "")
            # print 'got site', t[0]
            self.sites_list.append(t[0])
            return t
        self.nodes_list.append(t[0])
        # do not touch t as parser will fail
        return t

    def parse_expression(self,  expression):
        LPAR, RPAR, LBRK, RBRK, LBRC, RBRC = list(map(Suppress, "()[]{}"))
        alphaslower = alphanums[:26]
        alphasupper = alphanums[26:]

        allowed_chars = alphanums + '_' + '-' + '$' + '?' + "@"

        port = Word(allowed_chars).setParseAction(
            self.port_action) + Optional(Literal(",").suppress())
        portgroup = LBRK + Group(OneOrMore(port)) + RBRK

        node = Forward()
        node << (Word(allowed_chars + nums) + Optional(portgroup) + Optional(Literal(".") + Optional(LPAR) +
                                                                             Group(OneOrMore(node + Optional(Literal("|").suppress()))) + Optional(RPAR))).setParseAction(self.node_action)
        string_ = Forward()
        string_ << (node | Literal("|").suppress() | Group(
            LPAR + OneOrMore(string_) + RPAR))
        acexp = Forward()
        acexpList = Group(LPAR + ZeroOrMore(acexp) + RPAR)
        acexp << (string_ | acexpList)
        comment = cppStyleComment
        acexp.ignore(comment)
        ParserElement.enablePackrat()
        acexpr = acexp.parseString(expression, parseAll=True)
        return acexpr

    def uniquify_ast(self, ast_list):
        """ given an ast_list, replace nodes with the id function, filling the identity dict on the way """
        for idx, e in enumerate(ast_list):
            try:
                next = ast_list[idx + 1]
            except IndexError:
                next = None
            if next == '.':
                children = ast_list[idx + 2]
            else:
                children = None
            # if next is ports list
            try:
                if next[0] in self.ports_list:
                    ports = next
                else:
                    ports = None
            except TypeError:
                ports = None
            if ports:
                try:
                    if ast_list[idx + 3][0] in self.nodes_list + self.sites_list and ast_list[idx + 2] == '.':
                        # if ast_list[idx + 3][0] in self.identity.keys():
                        children = ast_list[idx + 3]
                except IndexError:
                    pass
            if e in self.nodes_list + self.sites_list:
                r = self.node_uniquefy(e)
                self.identity[r] = e
                ast_list[idx] = r

                if children:
                    self.uniquify_ast(children)
        return ast_list

    def make_props(self, ast_list):
        """ given an ast_list, derive propositions. uniquify_ast is a prerequisite. """
        props = list()
        for idx, e in enumerate(ast_list):
            attr = None
            try:
                next = ast_list[idx + 1]
            except IndexError:
                next = None
            if next == '.':
                children = ast_list[idx + 2]
            else:
                children = None
            try:
                if next[0] in self.ports_list:
                    ports = next
                else:
                    ports = None
            except TypeError:
                ports = None
            if ports:
                # check if children are next next
                try:
                    if ast_list[idx + 3][0] in list(self.identity.keys()):
                        children = ast_list[idx + 3]
                except IndexError:
                    pass
            if e in list(self.identity.keys()):
                # put as children only the top level in the children list
                if children:
                    top_children = [
                        k for k in children if k != '.' and not isinstance(k, list)]
                else:
                    top_children = children
                props.append(Proposition([e, top_children, ports]))
                if children:
                    props = props + self.make_props(children)
        return props

    def make_formula(self, parent=None, compact=False):
        """ make formula from graph """
        if parent is None:
            self.formula_graph = self.graph_repr
            parent = nx.topological_sort(self.graph_repr)[0]


        def portify(li):
            res = "["
            for l in li:
                res += str(l) + ","
            res = res[:-1]
            res += "]"
            return res

        #> def containify(node):
        g = self.formula_graph
        res = ""
        for c in g.successors(parent):
            obj = c
            if g.node[c].get('ports', False):
                obj += portify(g.node[c].get('ports', False))
            if g.successors(parent):
                ret = self.make_formula(parent=c)
                if ret:
                    obj += ".(" + ret + ")"
            res = res + ' | ' + obj
        res = res[3:]
        res2 = res
        import operator
        if 'world' in parent:
            for ident, typ in reversed(sorted(list(self.identity.items()), key=operator.itemgetter(0))):
                if typ in self.sites:
                    # workaround to add the $ to sites
                    res2 = res2.replace(ident, "$" + typ, 1)
                else:
                    res2 = res2.replace(ident, typ, 1)
        if compact:
            return res2.replace(" ", "")
        return res2

    def make_graph(self):
        """ draw_containment from props list: port names and controls are node attributes """
        g = nx.DiGraph()
        for p in self.props:
            g.add_node(p[0])
            # trick for the eq iso: store the identity as a node
            # attribute
            g.node[p[0]][self.identity[p[0]]] = 1
            g.node[p[0]]["control"] = self.identity[p[0]]
            if self.control_of(p.id) in self.sites_list:
                g.node[p[0]]["site"] = 1
            for child in atomset(p[1]):
                g.add_edge(p[0], child)
            if p.li:
                g.node[p[0]]["ports"] = p.li
            # extras for new iso matcher
            for c in atomset(p[1]):
                if self.control_of(c) in self.sites_list:
                    # g.node[p[0]].setdefault("contains_site",[]).append(c)
                    g.node[p[0]]["contains_site"] = c
            if p[1]:
                g.node[p[0]]["contains"] = frozenset(p[1])
        self.graph_repr = g
        return g

    def from_input_graph(self, g):
        # graph is as follows: every node has a unique id. node attributes are: 'ports':[list,of,ports]
        # and a key with the control name and value 1, e.g. "Controlname":1.
        self.props = []
        for n in g.nodes_iter(data=True):
            node_id = n[0]
            if g.successors(n[0]):
                sp = g.successors(n[0])
            else:
                sp = None
            prop = Proposition([n[0], sp, n[1].get("ports", None)])
            # print n,n[1]
            self.identity[prop.id] = n[1]["control"]
            if n[1].get("site", None):
                self.sites_list.append(self.control_of(prop.id))
            self.props.append(prop)
        self.graph_repr = self.make_graph()

    def update_from_graph(self):
        """ update the internal structures from the graph_repr"""
        self.formula_graph = ""
        self.from_input_graph(self.graph_repr)

    def export_gml(self, filename):
        """ export bigraph as GML file"""
        cp = self.graph_repr.copy()
        for n in cp.nodes_iter(data=True):
            try:
                del n[1]["contains"]
                del n[1]["contains_site"]
            except:
                pass
        nx.write_gml(cp, filename+".gml")

    def read_gml(self, filename):
        """ read and init from GML"""
        a = nx.read_gml(filename)

        # fix Room[b,e,d,r,o,o,m] -> Room[bedroom]
        for n in a.nodes_iter(data=True):
            if n[1].get("ports", False):
                if not isinstance(n[1]["ports"], list):
                    n[1]["ports"] = [n[1]["ports"]]
        self.from_input_graph(a)

    def get_node_by_control_and_ports(self, control, ports):
        for n in self.graph_repr.nodes_iter(data=True):
            if n[1]["control"] == control and n[1].get("ports", None) == ports:
                return n[0]
        return None

    def read_gefx(self, filename):
        """ read and init from gefx file"""
        nx.read_gefx(cp, filename)
        # fix Room[b,e,d,r,o,o,m] -> Room[bedroom]
        for n in a.nodes_iter(data=True):
            if n[1].get("ports", False):
                if not isinstance(n[1]["ports"], list):
                    n[1]["ports"] = [n[1]["ports"]]
        self.from_input_graph(a)

    def export_gefx(self, filename):
        """ export bigraph as gefx file"""
        cp = self.graph_repr.copy()
        for n in cp.nodes_iter(data=True):
            try:
                del n[1]["contains"]
                del n[1]["contains_site"]
            except:
                pass
        nx.write_gefx(cp, filename)

    def draw(self, filename):
        draw_dot(self.graph_repr, filename)

    def props_strings(self):
        """ get string of propositions representing the bigraph"""
        return PROPOSITIONS_DELIMITER.join([str(p) for p in self.props])

    def read_props(self, strin):
        """ read and init from a string of propositions """

        props = []
        identity = {}
        props_str = strin.split(PROPOSITIONS_DELIMITER)
        for pstr in props_str:
            pl = pstr.split(PROP_INT_DELIM)
            sp = [c for c in pl[1].split(",") if c != 'None']
            if not len(sp):
                sp = None
            li = [l for l in pl[2].split(",") if l != 'None']
            if not len(li):
                li = None
            newprop = Proposition([pl[0], sp, li])
            props.append(newprop)
            # quickfix: get identity control map by splitting on '_' the id
            identity[pl[0]] = pl[0].split("_")[0]
        self.props = props
        self.identity = identity
        self.graph_repr = self.make_graph()
        return props

# warning: this must be after custom classes for the pickling
# module to correctly identify the class
load_cache()
