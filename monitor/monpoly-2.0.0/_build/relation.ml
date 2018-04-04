(*
 * This file is part of MONPOLY.
 *
 * Copyright (C) 2011 Nokia Corporation and/or its subsidiary(-ies).
 * Contact:  Nokia Corporation (Debmalya Biswas: debmalya.biswas@nokia.com)
 * 
 * Copyright (C) 2012 ETH Zurich.
 * Contact:  ETH Zurich (Eugen Zalinescu: eugen.zalinescu@inf.ethz.ch)
 * 
 * 
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, version 2.1 of the
 * License.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library. If not, see
 * http://www.gnu.org/licenses/lgpl-2.1.html.
 *
 * As a special exception to the GNU Lesser General Public License,
 * you may link, statically or dynamically, a "work that uses the
 * Library" with a publicly distributed version of the Library to
 * produce an executable file containing portions of the Library, and
 * distribute that executable file under terms of your choice, without
 * any of the additional requirements listed in clause 6 of the GNU
 * Lesser General Public License. By "a publicly distributed version
 * of the Library", we mean either the unmodified Library as
 * distributed by Nokia, or a modified version of the Library that is
 * distributed under the conditions defined in clause 3 of the GNU
 * Lesser General Public License. This exception does not however
 * invalidate any other reasons why the executable file might be
 * covered by the GNU Lesser General Public License.
 *)



open Misc
open Tuple
open Predicate
open MFOTL


module Tuple_set = Set.Make (
  struct type t = tuple 
	 let compare = Tuple.compare
  end)

include Tuple_set

type relation = Tuple_set.t


(*** printing functions ***)

let string_of_rel rel =
    let rel' = Tuple_set.elements rel in
    Misc.string_of_list Tuple.string_of_tuple rel'

let string_of_rel4 rel =
    let rel' = Tuple_set.elements rel in
    Misc.string_of_list4 Tuple.string_of_tuple rel'


let print_rel str rel = 
  print_string str;
  let rel' = Tuple_set.elements rel in
  Misc.print_list Tuple.print_tuple rel'

(* let output_rel4 ch str rel =  *)
(*   output_string ch str; *)
(*   let rel' = Tuple_set.elements rel in *)
(*   Misc.output_list4 ch Tuple.output_tuple rel' *)

let print_rel4 str rel = 
  print_string str;
  let rel' = Tuple_set.elements rel in
  Misc.print_list4 Tuple.print_tuple rel'


let print_reln str rel = 
  print_rel str rel;
  print_newline()

let print_bigrel rel = 
  let rel' = Tuple_set.elements rel in
  Misc.print_list3 Tuple.print_tuple rel'

let print_orel = function
  | None -> print_string "N"
  | Some rel -> print_rel "S" rel




(********************************)


let make_relation list = 
  let rec make acc = function
  | [] -> acc
  | h::t -> make (Tuple_set.add h acc) t
  in make Tuple_set.empty list 
  
  
let map f rel =
  let res = ref (Tuple_set.empty) in
    Tuple_set.iter 
      (fun t ->
	 res := Tuple_set.add (f t) !res
      ) 
      rel


let map f rel =
  Tuple_set.fold (fun t rel' -> Tuple_set.add (f t) rel') rel Tuple_set.empty






(********************************)

let is_empty rel = 
  Tuple_set.is_empty rel


(*******************************************************************)
(*** rigid predicates ***)

(*** Not used anymore ***)

let trel = make_relation [Tuple.make_tuple []]
let frel = Tuple_set.empty

let eval_equal t1 t2 =
  match t1,t2 with
    | Var x, Cst c
    | Cst c, Var x -> make_relation [Tuple.make_tuple [c]]
    | Cst c, Cst c' when c = c' -> trel
    | Cst c, Cst c' -> frel
    | _ -> failwith "[Relation.eval_equal] (x=y)"


(* let eval_less t1 t2 =  *)
(*   match t1,t2 with  *)
(*     | Var x, Cst (Int c) -> *)
(*       let tl = Misc.map_interval   *)
(* 	(fun x -> Tuple.make_tuple [Int x])  *)
(* 	0 (c-1) *)
(*       in *)
(*       Relation.make_relation tl *)
(*     | Cst c, Cst c' ->	    *)
(*       if Predicate.cst_smaller c c' then *)
(* 	trel *)
(*       else *)
(* 	frel *)
(*     | Var x, Var y when x = y -> frel *)
(*     | _ -> failwith "[Relation.eval_less] (x<y) or (c<y)" *)


(* let eval_less_eq t1 t2 =  *)
(*   match t1,t2 with  *)
(*     | Var x, Cst (Int c) -> *)
(*       let tl = Misc.map_interval   *)
(* 	(fun x -> Tuple.make_tuple [Int x])  *)
(* 	0 c *)
(*       in *)
(*       Relation.make_relation tl *)
(*     | Cst c, Cst c' ->	    *)
(*       if Predicate.cst_smaller_eq c c' then *)
(* 	trel *)
(*       else *)
(* 	frel *)
(*     | Var x, Var y when x = y -> frel *)
(*     | _ -> failwith "[Relation.eval_less_eq] (x<=y) or (c<=y)" *)


let eval_not_equal t1 t2 =
  match t1,t2 with
    | Var x, Var y when x = y -> frel
    | Cst c, Cst c' when c = c' -> frel
    | Cst c, Cst c' -> trel
    | _ -> failwith "[Relation.eval_not_equal] (x <> y)"



(**********************************************************************)
 

(** [matches] gives the columns which should match in the two
    relations in form of a list of tuples [(pos2,pos1)]: column [pos2] in
    [rel2] should match column [pos1] in [rel1] *)
let natural_join matches1 matches2 rel1 rel2 = 
  let joinrel = ref Tuple_set.empty in
  let process_rel_tuple join_fun matches rel2 t1 =
    (* For each tuple in [rel1] we compute the columns (i.e. positions)
       in rel2 for which there should be matching values and the values
       tuples in rel2 should have at these columns.

       For instance, for [matches] = [(0,1);(1,2);(3,0)] and t1 =
       [6;7;9] we obtain [(0,7);(1,9);(3,6)]. That is, from [rel2] we
       will select all tuples which have 7 on position 0, 9 on
       position 1, and 6 on position 3.  *)
    let pv = List.map 
      (fun (pos2, pos1) -> (pos2, Tuple.get_at_pos t1 pos1))
      matches 
    in
      Tuple_set.iter 
	(fun t2 -> 
	   try 
	     let t = join_fun pv t1 t2 in
	       joinrel := Tuple_set.add t !joinrel	      
	   with
	       Not_joinable -> ()
	) 
	rel2
  in
  if Tuple_set.cardinal rel1 < Tuple_set.cardinal rel2 then
    let join_fun = Tuple.join in
    Tuple_set.iter (process_rel_tuple join_fun matches1 rel2) rel1
  else
    begin
      let pos2 = List.map fst matches1 in
      let join_fun = Tuple.join_rev pos2 in
      Tuple_set.iter (process_rel_tuple join_fun matches2 rel1) rel2
    end;
  !joinrel


let in_t2_not_in_t1 t2 matches = 
  let len  = List.length (Tuple.get_constants t2) in
  (* these are the positions in t2 which also appear in t1 *)
  let t2_pos = List.map snd matches in
  let rec get_aux pos = 
    if pos = len then []
    else if not (List.mem pos t2_pos) then
      let v = Tuple.get_at_pos t2 pos in
      v :: (get_aux (pos+1))
    else
      get_aux (pos+1)
  in
  get_aux 0
    



(* Misc.subset attr1 attr2 *)
(* Note that free_vars in (f1 AND f2) are ordered according to f1 not
   to f2!  Thus, for instance, for p(x,y) AND q(z,y,x) the fields
   should be ordered by (x,y,z).
*)
let natural_join_sc1 matches rel1 rel2 = 
  let joinrel = ref Tuple_set.empty in
  Tuple_set.iter (fun t2 -> 
    let t1_list = 
      List.map 
	(fun (pos1, pos2) -> 
	  (* x is at pos1 in t1 and at pos2 in t2 *)
	  Tuple.get_at_pos t2 pos2)
	matches
    in
    let t1 = Tuple.make_tuple t1_list in
    if Tuple_set.mem t1 rel1 then

      let t2_list = in_t2_not_in_t1 t2 matches in
      let t2' = Tuple.make_tuple (t1_list @ t2_list) in
      joinrel := Tuple_set.add t2' !joinrel
  ) rel2;
  !joinrel

(* Misc.subset attr2 attr1 *)
let natural_join_sc2 matches rel1 rel2 = 
  let joinrel = ref Tuple_set.empty in
  Tuple_set.iter (fun t1 -> 
    let t2 = Tuple.make_tuple (
      List.map 
	(* x is at pos2 in t2 and at pos1 in t1 *)
	(fun (pos2, pos1) -> Tuple.get_at_pos t1 pos1)
	matches) 
    in
    if Tuple_set.mem t2 rel2 then
      joinrel := Tuple_set.add t1 !joinrel
  ) rel1;
  !joinrel



let cross_product rel1 rel2 = 
  natural_join [] [] rel1 rel2



let reorder new_pos rel = 
  let new_rel = ref Tuple_set.empty in
  Tuple_set.iter (fun t ->
    let t' = Tuple.projections new_pos t in 
    new_rel := Tuple_set.add t' !new_rel
  ) rel;
  !new_rel

(* not set difference, but the diff operator as defined in Abiteboul, page 89 *)
let minus posl rel1 rel2 = 
  Tuple_set.filter 
    (fun t -> 
      let t' = (Tuple.projections posl t) in
      not (Tuple_set.mem t' rel2)
    ) 
    rel1


      

(* given the "predicate formula" [p] and a relation [rel] ("having the
   same signature" as [p]), obtain the relation containing those
   tuples of [rel] which satisfy [p] *)
let selectp p rel = 
  let res = ref Tuple_set.empty in
    Tuple_set.iter 
      (fun t ->
	 let b,t' = Tuple.satisfiesp p t in 
	 if b then
	   res := add t' !res
      ) rel;
    !res

(* type sterm =  *)
(*   | Pos of int *)
(*   | Val of cst *)
(*   | SPlus of sterm * sterm *)

(* type sconstraint = int * sterm *)

(* let term_to_sterm var_pos_list t =  *)
(*   let rec tf = function *)
(*     | Cst c -> Val c *)
(*     | Var x -> Pos (List.assoc x var_pos_list) *)
(*     | Plus (t1, t2) -> SPlus (tf t1, tf t2) *)
(*   in *)
(*   tf t *)



(* Note: [proj] \cup [sel] = all positions and [proj] \cap [sel] = \emptyset
   special case when sel=[]? yes, then selectp is the identity function
   special case when proj=[]? no 

   The approach below seems useless, because we have to iterate anyhow
   through all tuples and transform them individually (unless sel=[]).
   And then positions do not help us, see function [Tuple.satisfiesp].
*)
let no_constraints tlist = 
  let rec iter vars = function
    | [] -> true
      
    | (Var x) :: tlist ->
      if List.mem x vars then
	false (* there are constraints *)
      else (* new variable, we record its position *)
	iter (x :: vars) tlist
	  
    | _ :: tlist -> false  (* there are constraints *)
  in
  iter [] tlist
  

(* Given a predicate [f]=[p(t_1,\dots,t_n)], [eval_pred] returns a
   function from relations to relations; this function transforms
   [|p(x_1,\dots,x_n)|] into [|p(t_1,\dots,t_n)|] 
*)
let eval_pred p = 
  let tlist = Predicate.get_args p in
  if no_constraints tlist then
    fun rel -> rel
  else
    fun rel ->
      let res = ref Tuple_set.empty in
      Tuple_set.iter 
	(fun t ->
	  let b, t' = Tuple.satisfiesp tlist t in 
	  if b then
	    res := add t' !res;
	) rel;
      !res
  


(*** USELESS ***)
(* let eval_pred p =  *)
(*   let tlist = Predicate.get_termlist p in *)
(*   (\* The constraints refer to positions in the term list [proj] *)
(*      contains the list of positions of the free variables, that is *)
(*      what sould remain. example: for p(a,x,x+y,x,y) proj is [1;4] we *)
(*      do two passes through the term list, because for instance to *)
(*      generate the constraint corresponding to x+y, we need the *)
(*      positions of x and y, but these may not be known during the first *)
(*      pass. *)
(*   *\) *)
(*   let rec get_proj proj sel pos = function *)
(*     | [] -> proj *)

(*     | (Var x) :: tlist -> *)
(*       if List.mem_assoc x proj then *)
(* 	get_proj proj (pos + 1) tlist *)
(*       else (\* new variable, we record its position *\) *)
(* 	get_proj ((x, pos) :: proj) (pos + 1) tlist *)

(*     | _ :: tlist -> (\* we ignore it in the first pass *\) *)
(*       get_proj proj (pos+1) tlist *)
(*   in *)
(*   let proj = get_proj [] 0 tlist in *)
(*   let rec get_sel sel pos = function *)
(*     | [] -> sel *)

(*     | (Var x) :: tlist when List.assoc x proj = pos -> *)
(*       get_sel sel (pos + 1) tlist *)

(*     | term :: tlist ->  *)
(*       get_sel ((pos, term_to_sterm proj term) :: sel) (pos + 1) tlist *)
(*   in *)
(*   let sel = get_sel [] 0 tlist in *)




(* (\* selection constraints on terms are check at the end, when we know *)
(*    the binding of all variables *)
(* *\) *)
(* let pred_tf proj sel t =  *)
(*   let rec tf proj sel cst_list pos crt_tuple assign constr =  *)
(*     match cst_list with *)
(*       | [] ->  *)
(* 	assert(proj = [] && sel = []); *)
(* 	if check_constr assign constr then *)
(* 	  true, List.rev crt_tuple *)
(* 	else *)
(* 	  false, [] *)

(*       | c :: rest_cst_list -> *)
(* 	let new_tuple, new_proj, new_assign  =  *)
(* 	  match proj with *)
(* 	    | [] -> crt_tuple, proj *)
(* 	    | pos_proj :: rest_proj -> *)
(* 	      assert(pos_proj >= pos);   *)
(* 	      if pos_proj > pos then (\* we ignore this position *\) *)
(* 		crt_tuple, proj *)
(* 	      else (\* we keep this position *\) *)
(* 		c :: crt_tuple, rest_proj, (pos, c) :: assign *)
(* 	in *)
(* 	match sel with *)
(* 	  | [] -> tf new_proj sel rest_cst_list (pos+1) new_tuple *)
(* 	  | (pos_sel, sterm) :: rest_sel ->  *)
(* 	    assert(pos_sel >= pos); *)
(* 	    if pos_sel = pos then *)
(* 	      tf new_proj rest_sel rest_cst_list (pos+1) new_tuple new_assign ((c, sterm) :: constr) *)
(* 	    else  *)
(* 	      tf new_proj sel rest_cst_list (pos+1) new_tuple new_assign constr *)
(*   in *)
(*   tf proj sel t 0 [] [] *)



(* let selectf1 f pos rel =  *)
(*   Tuple_set.filter (Tuple.satisfiesf1 f pos) rel *)


(* (\* we could have special cases when x=y and f is, for instance, = or  < *\) *)
(* let selectf2 f pos1 pos2 rel =  *)
(*   Tuple_set.filter (Tuple.satisfiesf2 f pos1 pos2) rel *)




(* let duplicate_col pos rel =  *)
(*   map (Tuple.duplicate_pos pos) rel *)


    
(* let add_col pos g rel =  *)
(*   let res = ref Tuple_set.empty in *)
(*   Tuple_set.iter  *)
(*     (fun t ->  *)
(*        let relt = make_relation  *)
(* 	 (List.map (Tuple.add_last t) (g (Tuple.get_at_pos t pos))) *)
(*        in *)
(* 	 res := union !res relt  *)
(*     ) rel; *)
(*     !res *)



(* the columns in [posl] are eliminated *)
let project_away posl rel = 
  map (Tuple.project_away posl) rel









