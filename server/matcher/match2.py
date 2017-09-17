"""
matching.
"""

from matcher.acexp import *
from matcher.bigformula import *
from matcher.checks2 import *
from matcher.helpers import *
import copy

# try to import a deep logger interface, fail silently 
try:
    from matcher.logger import lg
except:
    def lg(msg, msg2=None, msg3=None, msg4=None):
        pass

# try to import the topohandler extensions
try:
    from topohandler.spacegraph import *
    imported_topohandler=True
except:
    imported_topohandler=False




def match_iso(a, r, which_nodes=False,which_variables=False):
    """ match redex/property r to model a. if which_nodes is True, instead of returning 
    the result of the match return the nodes that matched the bigraph r. """


    # if we have application condition guards in the reaction:
    if r.appl_cond:
        if not imported_topohandler:
            raise ImportError('Topohandler extensions needed for application conditions were not found.')
        who = r.who
        for cond in r.appl_cond:
            if not cond:
                continue
            if not a.closure_space:
                a.closure_space = SpacePredicatedGraph(a)

            # application conditions are positive by default. If r.appl_cond[3]
            # is True, its a negative one.
            try:
                positive_condition = cond[1]
            except IndexError:
                positive_condition = True
            spatialprop_instant = cond[0].replace("@fakedroneid", who)
            res = a.closure_space.invoke_topochecker(spatialprop=spatialprop_instant)

            if res:
                if positive_condition:
                    pass
                elif not positive_condition:
                    return []

            else:  # did not find result
                if positive_condition:
                    return []
                elif not positive_condition:
                    pass

    # remove all nodes with attribute "site"
    redex_copy_without_sites = copy.deepcopy(r.redex)
    redex_copy_without_sites.graph_repr = r.redex.graph_repr.copy()
    sites_in_redex = [n for n, attrs in list(redex_copy_without_sites.graph_repr.node.items(
    )) if attrs.get("site", False) == 1]
    redex_copy_without_sites.graph_repr.remove_nodes_from(sites_in_redex)
    node_matcher = nx.algorithms.isomorphism.generic_node_match(
        ['control', 'ports'], [None, None], [eq_overload_world, eq_overload_wildcard])
    GM = nx.algorithms.isomorphism.DiGraphMatcher(
        a.graph_repr, redex_copy_without_sites.graph_repr, node_match=node_matcher)
    if not GM.subgraph_is_isomorphic():
        if r.is_property and not which_nodes:
            return False
        else:
            return []
    # now we must look for the ones that matched of the redex, and contain sites.
    # then we go back to their node matched on the host, and match the site to the descendants.
    # new_graph= redex_copy_without_sites.graph_repr.copy()

    GMisomorphisms = GM.subgraph_isomorphisms_iter()
    # iterator gets exhausted after iterating once; for variables we must
    # iterate again for every var_mapping

    if r.has_variables:
        var_mappings = []
        for match_pairs in GMisomorphisms:
            g = nx.DiGraph()
            f = nx.DiGraph()
            # have to remove controls to get variable mappings afterwards
            controls = set()
            ports = set()
            for host_node, prop_node in list(match_pairs.items()):
                g.add_node(host_node)
                controls.add(a.graph_repr.node[host_node]['control'])
                g.node[host_node]["contains"] = set(a.control_of(c) for c in a.graph_repr.node[
                                                    host_node].get("contains", set()))
                for port in a.graph_repr.node[host_node].get("ports", []):
                    g.add_node(port)
                    ports.add(port)
                    g.add_edge(host_node, port)
                f.add_node(prop_node)
                f.node[prop_node]["contains"] = set(redex_copy_without_sites.control_of(
                    c) for c in redex_copy_without_sites.graph_repr.node[prop_node].get("contains", set()))
                if redex_copy_without_sites.graph_repr.node[prop_node].get("contains_site", False):
                    # put whatever is in the one matched here too, for the
                    # isomorphism node match to work
                    f.node[prop_node]["contains"] = set(a.control_of(c) for c in a.graph_repr.node[
                                                        host_node].get("contains", set()))
                for port in redex_copy_without_sites.graph_repr.node[prop_node].get("ports", []):
                    ports.add(port)
                    f.add_node(port)
                    f.add_edge(prop_node, port)

            node_matcher = nx.algorithms.isomorphism.generic_node_match(
                ['ports'], [None], [eq_overload_wildcard])
            LM = nx.algorithms.isomorphism.DiGraphMatcher(
                g, f, node_match=node_matcher)
            # get mappings of variables
            new_isos = []
            for iso in LM.isomorphisms_iter():
                # remove pairs that have key or value a control
                new_isos.append({k: v for k, v in iso.items() if "@" in v})
            # some may be duplicates, make them unique_sets and reverse them
            unique_sets = set(frozenset(list(d.items())) for d in new_isos if len(d))
            var_mappings += [{v: k for k, v in list(dict(s).items())} for s in unique_sets]
            var_mappings = uniquefy(var_mappings)

        # now after the matches, in the resulting matches, find occurences of
        # the variables and replace them per each var_mapping

    match_results = []
    model_all_nodes_matched = []
    # copy original ports of redex and reactum
    property_satisfied = False
    matched_to_variables=[]

    if r.has_variables:
        orig_redex_ports = copy.deepcopy(
            redex_copy_without_sites.graph_repr.node)
        orig_reactum_ports = copy.deepcopy(r.reactum.graph_repr.node)
        # build as many reactums as mappings we found and do the matching
        # normally but with concrete names for variables
        for var_mapping in var_mappings:
            # restore original ports:
            redex_copy_without_sites.graph_repr.node = copy.deepcopy(
                orig_redex_ports)
            r.reactum.graph_repr.node = copy.deepcopy(orig_reactum_ports)
            # substitute var_mappings to variable instances
            for n in redex_copy_without_sites.graph_repr.nodes():
                if redex_copy_without_sites.graph_repr.node[n].get("ports", False):
                    redex_copy_without_sites.graph_repr.node[n]['ports'] = [e if e not in list(var_mapping.keys(
                    )) else var_mapping[e] for e in redex_copy_without_sites.graph_repr.node[n]['ports']]

            for n in r.reactum.graph_repr.nodes():
                if r.reactum.graph_repr.node[n].get("ports", False):
                    r.reactum.graph_repr.node[n]['ports'] = [e if e not in list(var_mapping.keys(
                    )) else var_mapping[e] for e in r.reactum.graph_repr.node[n]['ports']]


            property_satisfied, concrete_match_results, concrete_model_all_nodes_matched = concrete_match(
                a, redex_copy_without_sites, r.reactum, r.is_property, which_nodes)
            

            if r.is_property and (not which_nodes) and which_variables and property_satisfied:
                matched_to_variables.append(var_mapping)

            if r.is_property and (not which_nodes) and (not which_variables):
                return property_satisfied



            match_results += concrete_match_results
            model_all_nodes_matched += concrete_model_all_nodes_matched
        # restore variables back in reaction
        redex_copy_without_sites.graph_repr.node = copy.deepcopy(
            orig_redex_ports)
        r.reactum.graph_repr.node = copy.deepcopy(orig_reactum_ports)
    else:
        # normal matching
        property_satisfied, match_results, model_all_nodes_matched = concrete_match(
            a, redex_copy_without_sites, r.reactum, r.is_property, which_nodes)
    # if we are looking for matching nodes, return those

    if which_variables and r.has_variables:
        # make them unique
        # uniq_d = list(map(dict, frozenset(frozenset(i.items()) for i in matched_to_variables)))
        return matched_to_variables

    if which_nodes:
        return set(model_all_nodes_matched)
    elif r.is_property:
        return property_satisfied
    else:
        return match_results


def concrete_match(model, redex, reactum, is_property, which_nodes):
    match_results = []

    # hold here all the model nodes that matched for use with which_nodes
    model_all_nodes_matched = []
    property_satisfied = False
    # make sure we matched all toplevel nodes or there is no site at the top
    # level
    world_a = nx.topological_sort(model.graph_repr)[0]
    world_r = nx.topological_sort(redex.graph_repr)[0]

    node_matcher = nx.algorithms.isomorphism.generic_node_match(
        ['control', 'ports'], [None, None], [eq_overload_world, eq_overload_wildcard])
    GM = nx.algorithms.isomorphism.DiGraphMatcher(
        model.graph_repr, redex.graph_repr, node_match=node_matcher)
    GMisomorphisms = GM.subgraph_isomorphisms_iter()

    for match_pairs in GMisomorphisms:


        new_graph = reactum.graph_repr.copy()
        map_reverse = dict((v, k) for k, v in match_pairs.items())
        matched_by_sites = []
        site_siblings_mapped = []

        site_match_failed = False
        # find ports of nodes that matched, they will be the label
        ports_label = []
        for model_node in list(match_pairs.keys()):
            [ports_label.append(ports) for ports in model.graph_repr.node[
                model_node].get("ports", []) if ports]
        # include all that matched except the one where the redex world mapped
        model_all_nodes_matched += [n for n,
                                    m in list(match_pairs.items()) if not "world" in m]
        for host_node, prop_node in list(match_pairs.items()):


            site = redex.graph_repr.node[prop_node].get("contains_site", False)
            if site:
                # check if it contains only a site
                if site and len(redex.graph_repr.node[prop_node].get("contains", set())) == 1:
                    site_id = redex.graph_repr.node[
                        prop_node]["contains_site"]
                    # get all descendants of host_node and find the whole
                    # subgraph
                    all_successors = list(
                        nx.dfs_preorder_nodes(model.graph_repr, host_node))
                    # host_node is now the root of the tree
                    site_matches = model.graph_repr.subgraph(
                        all_successors).copy()
                    matched_by_sites += site_matches

                    # due to variables, we get double matches since already one
                    # matched in a previous iter
                    if len(site_matches.nodes()) == 1:
                        # site did not match to anything, abort
                        site_match_failed = True
                        break

                    model_all_nodes_matched += matched_by_sites

                    if is_property:
                        # if which_nodes:
                            # WARNING: unhandled which nodes
                        return True, [], []

                    # match the subgraph to the site_matches
                    # will throw an exception if they are not disjoint
                    try:
                        new_graph = nx.algorithms.operators.binary.union(new_graph, site_matches)
                    except nx.exception.NetworkXError as e:
                        # abort match
                        return False,[],[]
                    site_in_reactum = list(n for n in reactum.graph_repr if reactum.graph_repr.node[
                                           n]['control'] == redex.control_of(site_id))[0]

                    # parent is the parent of the site_in_reactum
                    parent = new_graph.predecessors(site_in_reactum)[0]
                    new_graph.remove_node(site_in_reactum)

                    # first level successors of matched node, these successors
                    # should be top level
                    first_level = new_graph.successors(host_node)

                    new_graph.remove_node(host_node)
                    site_matches.remove_node(host_node)
                    for i in first_level:
                        new_graph.add_edge(parent, i)

                elif site and not len(redex.graph_repr.node[prop_node].get("contains", set())) == 1:
                    # there are siblings
                    site_siblings = [n for n in redex.graph_repr.node[
                        prop_node]["contains"] if n != site]

                    site_siblings_mapped = []
                    for site_sibling in site_siblings:
                        site_siblings_mapped.append(map_reverse[site_sibling])

                    # find the ones that are contained in the parent 'contains'
                    # in the model and take the difference with site siblings
                    difference = set(model.graph_repr.node[host_node][
                                     "contains"]) - set(site_siblings_mapped)
                    # get subgraph of difference and put it in the new_graph
                    all_successors_difference = []
                    for i in difference:
                        all_successors_difference += list(
                            nx.dfs_preorder_nodes(model.graph_repr, i))
                    site_matches = model.graph_repr.subgraph(
                        all_successors_difference).copy()
                    matched_by_sites += site_matches

                    model_all_nodes_matched += matched_by_sites


                    if len(site_matches.nodes()) == 0:
                        # site did not match to anything, abort
                        site_match_failed = True
                        break

                    if not is_property:
                        # will throw an exception if they are not disjoint
                        try:
                            new_graph = nx.algorithms.operators.binary.union(new_graph, site_matches)
                        except nx.exception.NetworkXError as e:
                            # abort match
                            return False,[],[]

                        site_id = redex.graph_repr.node[
                            prop_node]["contains_site"]
                        site_in_reactum = list(n for n in reactum.graph_repr if reactum.graph_repr.node[
                                               n]['control'] == redex.control_of(site_id))[0]
                        parent = new_graph.predecessors(site_in_reactum)[0]
                        new_graph.remove_node(site_in_reactum)

                        for i in site_matches.nodes():
                            if not site_matches.predecessors(i):
                                new_graph.add_edge(parent, i)
                    else:
                        # if which_nodes:
                            # WARNING: unhandled which nodes
                        return True, [], []
        # if world_r did not match to world_a replace the matched subgraph
        if not map_reverse[world_r] == world_a:

            reactum_nodes_in_new = new_graph.nodes()


            a_removed = model.graph_repr.copy()

            if not matched_by_sites and not site_siblings_mapped:
                # we have a pure match, no sites but completely matched.
                # make sure to remove all matched nodes from model.graph_repr
                # except the one where world matched
                pure_removals = [host_node for host_node, prop_node in list(match_pairs.items(
                )) if not 'world' in prop_node]
                a_removed.remove_nodes_from(pure_removals)

            # print 'model_all_nodes_matched', model_all_nodes_matched

            # remove siblings of sites that were found and their descendants
            if site_siblings_mapped:
                for n in site_siblings_mapped:
                    a_removed.remove_nodes_from(
                        list(nx.dfs_preorder_nodes(a_removed, n)))
            a_removed.remove_nodes_from(matched_by_sites)


            new_graph = nx.algorithms.operators.binary.union(
                new_graph, a_removed)

            prev_world = list(n for n in reactum.graph_repr if reactum.graph_repr.node[
                              n]['control'] == 'world')[0]
            first_level = new_graph.successors(prev_world)
            for i in first_level:
                new_graph.add_edge(map_reverse[world_r], i)
            new_graph.remove_node(prev_world)

        # workaround on not including siblings when there is a match on the first level
        elif not matched_by_sites and not site_siblings_mapped:

            # add siblings and successors
            prev_world = list(n for n in reactum.graph_repr if reactum.graph_repr.node[
                              n]['control'] == 'world')[0]
            # descendants of world that were not matched (do not appear in
            # match_pairs)
            # these have to be added to new_graph
            descendants_not_matched = [n for n in list(nx.dfs_preorder_nodes(
                model.graph_repr, world_a)) if n not in list(match_pairs.keys())]

            # print 'model ports', [k[1].get('ports', None) for k in model.graph_repr.node.items()]
            # print 'model',model.graph_repr.node
            a_removed = model.graph_repr.copy()
            a_removed.remove_nodes_from(
                [n for n in a_removed.nodes() if n not in descendants_not_matched])
            new_graph = nx.algorithms.operators.binary.union(
                new_graph, a_removed)

            # print 'new_graph ports', [k[1].get('ports', None) for k in new_graph.node.items()]

            first_level = [n for n in new_graph.nodes(
            ) if new_graph.in_degree(n) == 0 and n != prev_world]
            # add them as children to the world
            for i in first_level:
                new_graph.add_edge(prev_world, i)

        # if site did not match to anything, go on wth the isomorphisms
        if site_match_failed:
            continue
        # cleanup attributes
        to_clean = ["contains", "contains_site"]
        for t in to_clean:
            nx.set_node_attributes(new_graph, t, [])

        # if we are in a property check, no need to continue with all, just one
        if is_property and not which_nodes:
            return True, [], []
        elif which_nodes:
            return True, [], model_all_nodes_matched
        else:
            res = Bigraph(new_graph)
            # store label
            res.incoming_reaction_name = redex.reaction_name
            # res.incoming_label = [str(redex) + "->" + str(reactum)] + ports_label
            res.incoming_label = tuple([redex.reaction_name] + ports_label)

            match_results.append(res)

    return property_satisfied, match_results, model_all_nodes_matched

