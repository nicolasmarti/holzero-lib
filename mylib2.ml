
open Printf;;

(* misc helper function *)

let rec split_n (l: 'a list) (f: 'a -> bool) (n: int) : 'a list * 'a * 'a list =
  match l with
  | [] -> hol_fail ("split_n", "empty list")
  | hd::tl when f hd && n = 0 ->
    [], hd, tl
  | hd::tl when f hd ->
    let hd', el, tl = split_n tl f (n - 1) in 
    hd::hd', el, tl
  | hd::tl ->
    let hd', el, tl = split_n tl f n in 
    hd::hd', el, tl
;;

let split (l: 'a list) (f: 'a -> bool) : 'a list * 'a * 'a list = split_n l f 0;;


let rec partition (l: 'a list) (i: int): 'a list * 'a list =
  if i <= 0 then
    [], l
  else
    match l with
    | [] -> [], []
    | hd::tl ->
      let hd', tl' = partition tl (i-1) in
      hd::hd', tl
;;
    

let rec partitions (l: 'a list) (is: int list): 'a list list =
  match is with
  | [] -> []
  | hd::tl ->
    let hd', tl' = partition l hd in
    hd'::(partitions tl' tl)
;;

let take (l: 'a list) (i: int): 'a list = fst (partition l i);;
let drop (l: 'a list) (i: int): 'a list = snd (partition l i);;

let rec repeat (e: 'a) (i: int): 'a list =
  if i <= 0 then [] else
    e::(repeat e (i-1))
;;

(* goal, tactic and proof tree *)

type goal = term list * term;;

type tactic = goal -> goal list * (thm list -> thm);;

type proofTree = Leaf of goal
		 | Node of goal * (thm list -> thm) * (proofTree list) * (thm option);;


let is_closed (pt: proofTree) : bool =
  match pt with
  | Node (_, _, _, Some _) -> true
  | _ -> false;;

let to_thm (pt: proofTree) : thm =
  match pt with
  | Node (_, _, _, Some p) -> p
  | _ -> hol_fail ("to_thm", "proofTree not completed")


let is_opened (pt: proofTree) : bool =
  not (is_closed pt);;


open Format;;

let rec print_proofTree (pt: proofTree): unit =
  match pt with
  | Leaf (hyps, g) -> 
    let _ = List.iter (fun x -> print_string "\n"; print_term x) hyps in
    let _ = print_string "\n======================\n" in
    let _ = print_term g in
    print_string "\n"
  | Node (_, _, _, Some p) -> print_thm p
  | Node (_, _, gs, None) -> 
    let _, el, _ = split gs is_opened in
    print_proofTree el
;;

#install_printer print_proofTree;;
  
let rec apply_tactic (pt: proofTree) (tac: tactic) : proofTree =
  match pt with
  | Node (_, _, _, Some _) -> hol_fail ("apply_tactic", "closed node")
  | Leaf g ->
    let gs, f = tac g in
    if List.length gs = 0 then
      Node (g, f, [], Some (f []))
    else
      Node (g, f, map (fun g -> Leaf g) gs, None)
  | Node (g, f, gs, None) when List.exists is_opened gs ->
    let hd, el, tl = split gs is_opened in
    let el' = apply_tactic el tac in
    let gs' = hd@el'::tl in
    Node (g, f, gs', if List.for_all is_closed gs' then Some (f (map (fun (Node (_, _, _, Some p)) -> p ) gs')) else None)
;;

(* holzero helper function  *)


let term_for_goal (g: goal) (t: term) : term =
  let hyps, g = g in
  let t_vars = free_vars t in
  let g_vars = list_free_vars (g::hyps) in
  List.fold_left (fun t v ->
    try
      let _, el, _ = split g_vars (fun t -> fst (dest_var t) = fst (dest_var v)) in
      print_type (snd (dest_var v));
      tyvar_inst (type_match (snd (dest_var v)) (snd (dest_var el))) t
      
    with
    | _ -> t
  ) t t_vars
;;


let rec add_asms_rule (l: term list) (thm: thm)  : thm =
  match l with 
  | [] -> thm
  | hd::tl -> add_asms_rule tl (add_asm_rule hd thm)
;;

let rec replace_in_term (te: term) (a: term) (b: term) : term =
  if term_eq te a then
    b
  else
    if is_comb te then
      let (te1, te2) = dest_comb te in
      mk_comb (replace_in_term te1 a b, replace_in_term te2 a b)
    else
      if Term.is_abs te then
	let (te1, te2) = Term.dest_abs te in
	mk_abs (te1, replace_in_term te2 a b)	
      else
	te
;;

let rewrite_in_term (te: term) (a: term) (b: term) : term * term =
  (* te' := \ x. te[x/a] *)
  let x = genvar (Term.type_of a) in
  let te' = mk_abs (x, replace_in_term te a x) in
  (* te2 = (\ x. g[x/a]) b *)
  let te2 = mk_comb (te', b) in
  (* we get the final answer from the beta reduction thm*)
  let _, te'' = dest_eq (concl (beta_conv te2)) in
  te', te''
;;

let can_beta_reduce te : bool =
  if is_comb te then
      let (te1, te2) = dest_comb te in
      is_abs te1
  else
    false
;;

(* tacticals *)

let tac_then (tac: tactic) (tacs: tactic list) : tactic =
  fun goal ->
    let gs, f = tac goal in
    let tacs = take tacs (List.length gs) @ (repeat tac_id (List.length gs - List.length tacs)) in
    let gs', fs = List.split (List.map2 (fun f x -> f x) tacs gs) in
    List.concat gs',
    fun ps ->
      let ps' = partitions ps (List.map List.length gs') in
      let ps'' = (List.map2 (fun f x -> f x) fs ps') in
      f ps''
;;

(* tactics *)

let tac_id : tactic =
  fun goal ->
    [goal], fun [p] -> p
;;

let tac_cut (t: term) : tactic =
  fun (hyps, g) ->
    let t = term_for_goal (hyps, g) t in
    [ (hyps, t); (t::hyps, g) ],
    fun [p1; p2] ->
      prove_asm_rule p1 p2
;;

let tac_exact (p: thm) : tactic =
  fun (hyps, g) ->
    let ute, uty = term_match (concl p) g in
    let thm' = inst_type_rule uty (inst_rule ute p) in
    [], fun _ -> thm'
;;

let rec tac_asm: tactic =
  fun (hyps, g) ->
    let hd, el, tl = split hyps (term_eq g) in
    [], fun [] -> add_asms_rule (hd@tl) (assume_rule g)
;;

let tac_add_thm (t: thm) : tactic =
  tac_then (tac_cut (concl t)) [tac_exact t]
;;


let tac_remove_hyps (is: int list) : tactic =
  fun (hyps, g) ->
    let hs = List.map (List.nth hyps) is in
    let hyps' = List.filter (fun el -> List.fold_left (fun acc i -> acc && not (term_eq el (List.nth hyps i)) ) true is) hyps in
    [hyps', g], fun [p] ->
      add_asms_rule hs p
;;


(* ==> *)

let tac_intro_imp: tactic =
  fun (hyps, g) ->
    if is_imp g then
      let te1, te2 = dest_imp g in
      [ te1::hyps, te2 ], fun [p] -> disch_rule te1 p
    else
      hol_fail ("tac_intro_imp", "not an implication")
;;

let tac_elim_imp (id: int) : tactic =
  fun (hyps, g) ->
    let hd, el, tl = split_n hyps is_imp id in
    let hyps', ccl = strip_imp el in
    if not (term_eq ccl g) then 
      hol_fail ("tac_elim_imp", "the conclusion of the implication is not equal to the goal");
    let gs = map (fun g -> hyps, g) hyps' in
    gs, fun ps ->
      List.fold_left (fun g p ->
	mp_rule g p
      ) (add_asms_rule (hd@tl) (assume_rule el)) ps
;;

(* /\ *)


let tac_intro_conj : tactic =
  fun (hyps, g) ->
    if is_conj g then
      let te1, te2 = dest_conj g in
      [ (hyps, te1); (hyps, te2) ], fun [p1; p2] -> conj_rule p1 p2
    else
      hol_fail ("tac_intro_conj", "not a conj")
;;

let tac_elim_conj (id: int):tactic =
  fun (hyps, g) ->
    let hd, el, tl = split_n hyps is_conj id in
    let te1, te2 = dest_conj el in
    let g' = (hd @ te1::te2::tl, g) in
    [g'], fun [p] ->
      let thm1 = add_asm_rule el p in
      let thm2 = prove_asm_rule (conjunct1_rule (assume_rule el)) thm1 in
      let thm3 = prove_asm_rule (conjunct2_rule (assume_rule el)) thm2 in
      thm3
;;

(* \/ *)


let tac_intro_disj (left: bool) : tactic =
  fun (hyps, g) ->
    if is_disj g then
      let te1, te2 = dest_disj g in
      [ if left then (hyps, te1) else (hyps, te2) ], fun [p] -> if left then disj1_rule p te2 else disj2_rule te1 p
    else
      hol_fail ("tac_intro_disj", "not a disj")
;;

let tac_elim_disj (id: int) : tactic =
  fun (hyps, g) ->
    let hd, el, tl = split_n hyps is_disj id in
    let te1, te2 = dest_disj el in
    [ (hd @ te1::tl, g); (hd @ te2::tl, g) ],
    fun [p1; p2] ->
      let thm1 = add_asms_rule (hd@tl) (assume_rule el) in
      disj_cases_rule thm1 p1 p2
;;

(* ~ *)


let tac_intro_not: tactic =
  fun (hyps, g) ->
    if is_not g then
      let te = dest_not g in
      [ hyps, mk_imp (te, `false`) ], fun [p] -> not_intro_rule p
    else
      hol_fail ("tac_intro_disj", "not a disj")
;;

let tac_elim_not (id: int): tactic =
  fun (hyps, g) ->
    let hd, el, tl = split_n hyps is_not id in
    let te = dest_not el in
    let g' = (hd@(mk_imp (te, `false`))::tl, g) in
    [g'], fun [p] ->
      let thm1 = add_asm_rule el p in
      prove_asm_rule (not_elim_rule (assume_rule el)) thm1
;;

(* ! x. *)


let tac_intro_forall: tactic =
  fun (hyps, g) ->
    if is_forall g then
      let x, te = dest_forall g in
      [ hyps, te ], fun [p] -> gen_rule x p
    else
      hol_fail ("tac_intro_forall", "not a forall")
;;

let tac_elim_forall (id: int) (t: term): tactic =
  fun (hyps, g) ->
    let t = term_for_goal (hyps, g) t in
    let hd, el, tl = split_n hyps is_forall id in    
    let x, te = dest_forall el in
    let new_te = subst [x, t] te in
    let g' = (new_te::hyps, g) in
    [g'], fun [p] ->
      let thm1 = add_asm_rule new_te p in
      prove_asm_rule (spec_rule t (assume_rule el)) thm1
;;

(* ?x. *)

let tac_intro_exists (t: term) : tactic =
  fun (hyps, g) ->
    let t = term_for_goal (hyps, g) t in
    if is_exists g then
      let x, te = dest_exists g in
      let new_te = subst [x, t] te in
      [ hyps, new_te ], fun [p] -> exists_rule (g, t) p
    else
      hol_fail ("tac_intro_exists", "not an exists")
;;


(* should not be term -> fresh variable *)
let tac_elim_exists (id: int) (t: term) : tactic =
  fun hyps, g ->
    let hd, el, tl = split_n hyps is_exists id in    
    let x, te = dest_exists el in
    let uty = type_match (type_of x) (type_of t) in    
    let new_te = subst [tyvar_inst uty x, t] te in
    let g' = (hd @ new_te::tl, g) in
    ([g'], fun [p] ->
      let thm1 = add_asms_rule (hd@tl) (assume_rule el)  in
      choose_rule (t, thm1) p
    )
;;

(* rewriting *)

let tac_rewrite_goal (i: int) (direction: bool) =
  fun (hyps, g) ->
    let hd, el, tl = split_n hyps is_eq i in
    let a, b = (if direction then (fun x -> x) else (fun x,y -> (y, x))) (dest_eq el) in
    let g', g'' = rewrite_in_term g a b in
    [hyps, g''], fun [p] ->
      (
	let eq = (if direction then sym_rule else (fun x -> x)) (snd (tac_asm (hyps, el)) []) in
	let te1 = mk_comb (g', a) in
	let thm1 = sym_rule (beta_conv te1) in
	let thm2 = sym_rule (mk_comb2_rule g' eq) in
	let ccl2 = snd (dest_eq (concl thm2)) in
	let thm3 = beta_conv ccl2 in
	let thm4 = sym_rule (trans_rule (trans_rule thm1 thm2) thm3) in
	eq_mp_rule thm4 p
      )
;;


let tac_rewrite_hyps (i: int) (direction: bool) (j: int) =
  fun (hyps, g) ->
    let hd, el, tl = split_n hyps is_eq i in
    let te = List.nth hyps j in
    let a, b = (if direction then (fun x -> x) else (fun x,y -> (y, x))) (dest_eq el) in
    let g', g'' = rewrite_in_term te a b in
    let t =
      tac_then (tac_cut g'') [
	(tac_then (tac_rewrite_goal i (not direction)) [tac_asm]); tac_remove_hyps [j+1]
      ]
    in
    t (hyps, g)
;;

(* beta reduction *)
let tac_beta_reduce_goal (i: int) : tactic =
  fun (hyps, g) ->
    let l = find_subterms can_beta_reduce g in
    let te = List.nth l i in
    let eq_thm = beta_conv te in
    let t =
      tac_then (tac_then (tac_add_thm eq_thm) [
	tac_rewrite_goal 0 true
      ]) [tac_remove_hyps [0]]
    in
    t (hyps, g)
;;

(* example *)
let pt = Leaf ([], `? x. (\ b. b) x`);;
let pt = apply_tactic pt (tac_intro_exists `true`);;
let pt = apply_tactic pt (tac_beta_reduce_goal 0);;
let pt = apply_tactic pt (tac_exact truth_thm);;
let one_type_def_ax = to_thm pt;;

(**)

let pt = Leaf ([], `((\ b. b) true) ==> false`);;
let pt = apply_tactic pt (tac_intro_imp);;

let pt = apply_tactic pt (
  fun (hyps, g) ->
    let thm = beta_conv (List.hd hyps) in
    tac_add_thm thm (hyps, g)

);;

let pt = apply_tactic pt (tac_rewrite_hyps 0 true 1)
;;

