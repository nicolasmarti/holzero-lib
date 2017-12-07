
open Printf;;

(* misc helper function *)
let imp (b1: bool) (b2: bool) : bool =
  (not b1) || b2;;

let rec forall (f: 'a -> bool)  (l: 'a list) : bool =
  match l with
  | [] -> true
  | hd::tl when f hd -> forall f tl
  | _ -> false
;;


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
  

let rec add_asms_rule (l: term list) (thm: thm)  : thm =
  match l with 
  | [] -> thm
  | hd::tl -> add_asms_rule tl (add_asm_rule hd thm)
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
;;

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

let print_goal (g: goal) =
  let hyps, g = g in
  let _ = List.iter (fun x -> (if x != List.nth hyps 0 then print_string ", "); print_term x) hyps in
  let _ = print_string " |?- " in
  print_term g
;;
  
      
#install_printer print_proofTree;;
  
let rec current_goal (pt: proofTree): goal =
  match pt with
  | Leaf (hyps, g) -> (hyps, g)
  | Node (_, _, gs, None) ->
     let _, el, _ = split gs is_opened in
     current_goal el
;;
            
let debug = ref true;;

let rec is_permut (l1: 'a list) (l2: 'a list) (eq: 'a -> 'a -> bool): bool =
  match l1, l2 with
  | [], [] -> true
  | hd::tl, _ ->
     let l2' = List.filter (fun x ->
                   not (eq hd x)) l2 in
     if List.length l2' + 1 <> List.length l2 then false
     else
       is_permut tl l2' eq
  | _ -> false
;;
  
let rec is_included (l1: 'a list) (l2: 'a list) (eq: 'a -> 'a -> bool): bool =
  match l1, l2 with
  | [], _ -> true
  | hd::tl, _ ->
     let l2' = List.filter (fun x ->
                   not (eq hd x)) l2 in
     is_permut tl l2' eq
;;

let rec list_diff (l1: 'a list) (l2: 'a list) (eq: 'a -> 'a -> bool): ('a list * 'a list) =
  match l1, l2 with
  | hd::tl, _ ->
     let l2' =
       try
         let hd2, _, tl2 = split_n l2 (fun x -> not (eq hd x)) 0 in
         hd2 @ tl2
       with
         _ ->l2
     in
     list_diff tl l2' eq
  | _ -> l1, l2
;;

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
    Node (g, f, gs', if List.for_all is_closed gs' then Some (
                                                            let thm = f (map (fun (Node (_, _, _, Some p)) -> p ) gs') in
                                                            let is_same_concl = term_eq (concl thm) (snd g) in
                                                            let l1, l2 = list_diff (asms thm) (fst g) term_eq in
                                                            if (not is_same_concl) || List.length l1 > 0 then (
                                                              printf "\nmismatch between:\n";
                                                              print_thm thm;
                                                              print_string "\nand:\n";
                                                              print_goal g;
                                                              print_string "\n\n";
                                                              hol_fail ("apply_tactic", "debug check failed")
                                                            );
                                                            if !debug then (
                                                              printf "\nmatching goal and theorem:\n";
                                                              print_thm thm;
                                                              print_string "\nand:\n";
                                                              print_goal g;
                                                              print_string "\n\n";
                                                            );
                                                            add_asms_rule l2 thm
                                                          ) else None
         );;
  

let set_goal g = Leaf ([], g);;

(* holzero helper function  *)

let term_match_plus (te1: term) (te2: term) xs ys =
  let l = term_match te1 te2 in
  if
    forall (fun e1, e2 ->
        forall (fun x -> imp (type_eq x e1) (type_eq x e2)) ys
      ) (snd l) &&
      forall (fun e1, e2 ->
          forall (fun x -> imp (term_eq x e1) (term_eq x e2)) xs
        ) (fst l) then l
  else
    hol_fail ("term_match_plus", "wrongly unified var")
;;
             
  

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

let rec instances_in_term (te: term) (a: term) xs ys :
          ((term * term) list * (hol_type * hol_type) list) list =
  (try
     [term_match_plus a te xs ys]
   with
     _ -> []) @
    if is_comb te then
      let (te1, te2) = dest_comb te in
      instances_in_term te1 a xs ys @ instances_in_term te2 a xs ys
    else
      if is_abs te then
        let (_, te) = dest_abs te in
        instances_in_term te a xs ys
      else []
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
  
let can_beta_reduce te : bool =
  if is_comb te then
      let (te1, te2) = dest_comb te in
      is_abs te1
  else
    false
;;
  
let rec apply_iff (thm1: Thm.thm) (thm2: Thm.thm): Thm.thm =
  (* thm1: |- a <=> b, thm2: |- a or |- b *)
  try
    apply_imp (eq_imp_rule1 thm1) thm2
  with
    _ -> apply_imp (eq_imp_rule2 thm1) thm2
and apply_imp (thm1: Thm.thm) (thm2: Thm.thm): Thm.thm =
(* thm1: |- a => b or |- b => a, thm2: |- a or |- b *)
  let a, b = dest_imp (Thm.concl thm1) in
  let c = Thm.concl thm2 in
  let ute, uty = term_match a c in
  let thm1 = inst_type_rule uty (inst_rule ute thm1) in
  let thm2 = inst_type_rule uty (inst_rule ute thm2) in
  mp_rule thm1 thm2
;;
            
let make_fresh_thm (thm: thm) (g: goal) =
  let hyps, g = g in
  let tyvars = flatten (map term_tyvars (g::hyps)) in
  let reftyvars = ref (map dest_var_type tyvars) in
  let new_tyvars = map (fun x ->
                       let ns = string_variant !reftyvars (dest_var_type x) in
                       reftyvars := ns::!reftyvars;
                       mk_var_type ns
                     ) tyvars in
  inst_type_rule (zip tyvars new_tyvars) thm
;;
  
(* tacticals *)


let tac_id : tactic =
  fun goal ->
    [goal], fun [p] -> p
;;

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
    [], fun _ -> add_asms_rule hyps thm'
;;
  
let tac_add_thm (t: thm) : tactic =
  fun g ->
  let t = make_fresh_thm t g in
  tac_then (tac_cut (concl t)) [tac_exact t] g
;;


let rec tac_asm: tactic =
  fun (hyps, g) ->
    let hd, el, tl = split hyps (term_eq g) in
    [], fun [] -> add_asms_rule (hd@tl) (assume_rule g)
;;

let rec tac_asm_Expl (i:int): tactic =
  fun (hyps, g) ->
    let hd, el, tl = take hyps i, List.nth hyps i, drop hyps (i+1) in
    [], fun [] -> add_asms_rule (hd@tl) (assume_rule g)
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

(* <=> *)
let tac_intro_iff: tactic =
  fun (hyps, g) ->
  if is_eq g then
    let te1, te2 = dest_eq g in
    [ (hyps, mk_imp (te1, te2)); (hyps, mk_imp (te2, te1)) ], fun [p1; p2] -> imp_antisym_rule p1 p2
  else
    hol_fail ("tac_intro_iff", "not a iff2" )
;;

let tac_elim_iff (id: int): tactic =
  fun (hyps, g) ->
  let hd, el, tl = split_n hyps is_eq id in
  let te1, te2 = dest_eq el in
  let g' = (hd @ (mk_imp (te1, te2))::(mk_imp (te2, te1))::tl, g) in
  [g'], fun [p] ->
        let thm1 = add_asm_rule el p in
        let thm2 = prove_asm_rule (eq_imp_rule1 (assume_rule el)) thm1 in
        let thm3 = prove_asm_rule (eq_imp_rule2 (assume_rule el)) thm2 in
        thm3
;;
        

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

let rec tac_elim_thm_forall_loop (te: term) (thm: thm) (ts: term list): thm =
  match ts with
  | [] -> thm
  | hd::tl ->
     let x, te = dest_forall te in
     let unif_ty = type_match (type_of x) (type_of hd) in
     tac_elim_thm_forall_loop (tyvar_inst unif_ty te) (inst_type_rule unif_ty thm) tl
and tac_elim_thm_forall (thm: thm) (ts: term list) =
  fun g ->
  let thm = make_fresh_thm thm g in
  let ts = map (term_for_goal g)ts in
  let thm = tac_elim_thm_forall_loop (concl thm) thm ts in
  let tacs = List.fold_right (fun te tac -> tac_then (tac_elim_forall 0 te) [tac_then (tac_remove_hyps [1]) [tac]]) ts tac_id in
  tac_then (tac_cut (concl thm)) [tac_exact thm; tacs] g
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
  let el = List.nth hyps i in
  let a, b = (if direction then (fun x -> x) else (fun x,y -> y, x)) (dest_eq el) in
  let xs = (if false then intersect else union) ((free_vars g) @ flatten (map free_vars hyps)) (union (free_vars a) (free_vars b)) in
  let ys = flatten (map (fun te -> type_tyvars (type_of te)) xs) in
  let unifs = instances_in_term g a xs ys in
  let ute, uty = if List.length unifs >0 then List.nth unifs 0 else ([], []) in
  let a = tyvar_inst uty (subst ute a) in
  let b = tyvar_inst uty (subst ute b) in
  let g = tyvar_inst uty (subst ute g) in
  let x = genvar (Term.type_of a) in
  let g' = mk_abs (x, replace_in_term g a x) in
  let te2 =mk_comb (g', b) in
  let _, g'' = dest_eq (concl (beta_conv te2)) in
  [hyps, g''], fun [p] ->
               let eq = (if direction then eq_sym_rule else (fun x -> x)) (snd (tac_asm (hyps, el)) []) in
               let eq = inst_type_rule uty (inst_rule ute eq) in
               let te1 = mk_comb (g', a) in
               let thm1 = eq_sym_rule (beta_conv te1) in
               let thm2 = eq_sym_rule (mk_comb2_rule g' eq) in
               let ccl2 = snd (dest_eq (concl thm2)) in
               let thm3 = beta_conv ccl2 in
               let thm4 = eq_sym_rule (eq_trans_rule (eq_trans_rule thm1 thm2) thm3) in
               eq_mp_rule thm4 p
;;

let tac_rewrite_thm_goal (thm: thm) (direction: bool) =
  fun (hyps, g) ->
  let thm = make_fresh_thm thm (hyps, g) in
  let el = concl thm in
  let a, b = (if direction then (fun x -> x) else (fun x,y -> y, x)) (dest_eq el) in
  let xs = (if false then intersect else union) ((free_vars g) @ flatten (map free_vars hyps)) (union (free_vars a) (free_vars b)) in
  let ys = flatten (map (fun te -> type_tyvars (type_of te)) xs) in
  let unifs = instances_in_term g a xs ys in
  let ute, uty = if List.length unifs >0 then List.nth unifs 0 else ([], []) in
  let a = tyvar_inst uty (subst ute a) in
  let b = tyvar_inst uty (subst ute b) in
  let g = tyvar_inst uty (subst ute g) in
  let x = genvar (Term.type_of a) in
  let g' = mk_abs (x, replace_in_term g a x) in
  let te2 =mk_comb (g', b) in
  let _, g'' = dest_eq (concl (beta_conv te2)) in
  [hyps, g''], fun [p] ->
               let eq = (if direction then eq_sym_rule else (fun x -> x)) (add_asms_rule hyps thm) in
               let eq = inst_type_rule uty (inst_rule ute eq) in
               let te1 = mk_comb (g', a) in
               let thm1 = eq_sym_rule (beta_conv te1) in
               let thm2 = eq_sym_rule (mk_comb2_rule g' eq) in
               let ccl2 = snd (dest_eq (concl thm2)) in
               let thm3 = beta_conv ccl2 in
               let thm4 = eq_sym_rule (eq_trans_rule (eq_trans_rule thm1 thm2) thm3) in
               eq_mp_rule thm4 p
;;

let tac_rewrite_thm_hyps (thm: thm) (direction: bool) (j: int) =
  fun (hyps, g1) ->
  let g = List.nth hyps j in
  let thm = make_fresh_thm thm (hyps, g) in
  let el = concl thm in
  let a, b = (if direction then (fun x -> x) else (fun x,y -> y, x)) (dest_eq el) in
  let xs = (if false then intersect else union) ((free_vars g) @ flatten (map free_vars hyps)) (union (free_vars a) (free_vars b)) in
  let ys = flatten (map (fun te -> type_tyvars (type_of te)) xs) in
  let unifs = instances_in_term g a xs ys in
  let ute, uty = if List.length unifs >0 then List.nth unifs 0 else ([], []) in
  let a = tyvar_inst uty (subst ute a) in
  let b = tyvar_inst uty (subst ute b) in
  let g = tyvar_inst uty (subst ute g) in
  let x = genvar (Term.type_of a) in
  let g' = mk_abs (x, replace_in_term g a x) in
  let te2 = mk_comb (g', b) in
  let _, g'' = dest_eq (concl (beta_conv te2)) in
  let f_g = mk_imp (g, g'') in
  let t = tac_then (tac_cut g'') [
                     tac_then (tac_cut f_g) [
                                (tac_then (tac_rewrite_thm_goal thm direction) [
                                            tac_then (tac_intro_imp) [ tac_asm ]
                                          ]
                                );
                                tac_then (tac_elim_imp 0) [tac_asm ]
                              ];
                     tac_then (tac_remove_hyps [j+1]) [tac_id]
                   ] in
  t (hyps, g1)
;;

  let tac_rewrite_hyps (i: int) (direction: bool) (j: int) =
  fun (hyps, g1) ->
  let g = List.nth hyps j in
  let el = List.nth hyps i in
  let a, b = (if direction then (fun x -> x) else (fun x,y -> y, x)) (dest_eq el) in
  let xs = (if false then intersect else union) ((free_vars g) @ flatten (map free_vars hyps)) (union (free_vars a) (free_vars b)) in
  let ys = flatten (map (fun te -> type_tyvars (type_of te)) xs) in
  let unifs = instances_in_term g a xs ys in
  let ute, uty = if List.length unifs >0 then List.nth unifs 0 else ([], []) in
  let a = tyvar_inst uty (subst ute a) in
  let b = tyvar_inst uty (subst ute b) in
  let g = tyvar_inst uty (subst ute g) in
  let x = genvar (Term.type_of a) in
  let g' = mk_abs (x, replace_in_term g a x) in
  let te2 = mk_comb (g', b) in
  let _, g'' = dest_eq (concl (beta_conv te2)) in
  let f_g = mk_imp (g, g'') in
  let t = tac_then (tac_cut g'') [
                     tac_then (tac_cut f_g) [
                                (tac_then (tac_rewrite_goal i direction) [
                                            tac_then (tac_intro_imp) [ tac_asm ]
                                          ]
                                );
                                tac_then (tac_elim_imp 0) [tac_asm ]
                              ];
                     tac_then (tac_remove_hyps [j+1]) [tac_id]
                   ] in
  t (hyps, g1)
;;

  
(* beta reduction *)
(*
old version

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

*)
  
  
let tac_beta_reduce_goal (i: int) : tactic =
  fun (hyps, g) ->
  let l = find_subterms can_beta_reduce g in
  let te = List.nth l i in
  let eq_thm = beta_conv te in
  let t = tac_rewrite_thm_goal eq_thm true
  in
  t (hyps, g)
;;

let tac_beta_reduce_hyps (i: int) (j: int) : tactic =
  fun (hyps, g) ->
  let tres = find_subterms can_beta_reduce (List.nth hyps i) in
  let te = List.nth tres j in
  let eq_thm = beta_conv te in
  let t = tac_rewrite_thm_hyps eq_thm true i
  in
  t (hyps, g)
;;

(* unfold constante *)
let tac_unfold_constant_goal (s: string) : tactic =
  fun (hyps, g) ->
  let eq_thm = get_const_definition s in
  let t = tac_rewrite_thm_goal eq_thm true in
  t (hyps, g)
;;

let tac_unfold_constant_goal_hyps (s: string) (i: int): tactic =
  fun (hyps, g) ->
  let eq_thm = get_const_definition s in
  let t = tac_rewrite_thm_hyps eq_thm true i in
  t (hyps, g)
;;
  
