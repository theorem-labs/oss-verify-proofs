(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VAbs VStepMem VCert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Inductive mres : Type := MOk (sigma : pmap lin) | MFail (msg : string).

(* [comment removed for export] *)
Definition macc := (pmap lin * list (lin * lin))%type.

Definition unbound_vars (isv : sym -> bool) (sigma : pmap lin) (e : lin) : list (sym * Z) :=
  filter (fun t : sym * Z => isv (fst t) && negb (pm_mem (fst t) sigma)) (lt e).

Definition match_loc (isv : sym -> bool) (acc : macc) (e e' : lin) : macc :=
  let '(sigma, defer) := acc in
  match unbound_vars isv sigma e with
  | [(J, k)] =>
      if Z.eqb k 1 then
        let rest := lsub e (lsym J) in
        (pm_set J (lsub e' (lsubst sigma rest)) sigma, (e, e') :: defer)
      else (sigma, (e, e') :: defer)
  | _ => (sigma, (e, e') :: defer)
  end.

(* [comment removed for export] *)
Definition match_loc_f (isv : sym -> bool) (acc : macc) (e e' : lin) : macc :=
  match e with
  | mkLin Z0 [(J, Zpos xH)] =>
      let '(sigma, defer) := acc in
      if isv J then (if pm_mem J sigma then (sigma, (e, e') :: defer) else (pm_set J e' sigma, (e, e') :: defer))
      else (sigma, (e, e') :: defer)
  | mkLin _ [] => let '(sigma, defer) := acc in (sigma, (e, e') :: defer)
  | _ => match_loc isv acc e e'
  end.

Lemma terms_scale_1 l : terms_scale 1 l = l.
Proof. induction l as [|[s c] t IH]; cbn [terms_scale]; [reflexivity|]. rewrite IH. destruct c; reflexivity. Qed.

Lemma terms_axpy_nil_r k l : terms_axpy k l [] = l.
Proof. destruct l as [|[s c] t]; reflexivity. Qed.

Lemma lsub_lconst0 e : lsub e (lconst 0) = e.
Proof. unfold lsub, lconst. cbn [lc lt]. rewrite terms_axpy_nil_r, Z.sub_0_r. destruct e; reflexivity. Qed.

Lemma match_loc_f_eq isv acc e e' : match_loc_f isv acc e e' = match_loc isv acc e e'.
Proof.
  unfold match_loc_f. destruct e as [c l]. destruct l as [|[J k] t].
  - destruct acc as [sigma defer]. unfold match_loc, unbound_vars. cbn [lt filter]. destruct c; reflexivity.
  - destruct c; try reflexivity. destruct k as [|[k|k|]|k]; try reflexivity. destruct t; try reflexivity.
    destruct acc as [sigma defer]. unfold match_loc, unbound_vars. cbn [lt filter fst].
    destruct (isv J); cbn [andb]; [|reflexivity].
    destruct (pm_mem J sigma); cbn [negb]; [reflexivity|].
    cbn [Z.eqb Pos.eqb].
    f_equal. f_equal. symmetry. etransitivity; [|apply lsub_lconst0]. f_equal.
    unfold lsub, lsym. cbn [lc lt terms_axpy]. rewrite Pos.compare_refl. reflexivity.
Qed.

Definition zdec (z : Z) : string := "".   (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint match_regs (isv : sym -> bool) (skip : positive -> bool) (l : list (positive * lin)) (P : vstate) (acc : macc)
  : macc + string :=
  match l with
  | [] => inl acc
  | (r, e) :: t =>
      if skip r then match_regs isv skip t P acc
      else match pm_get r (vs_regs P) with
           | None => inr "match: register tracked in stored state is Top in path state"
           | Some e' => match_regs isv skip t P (match_loc isv acc e e')
           end
  end.

(* [comment removed for export] *)
Fixpoint match_regs_f (isv : sym -> bool) (skip : positive -> bool) (l : list (positive * lin)) (P : vstate) (acc : macc)
  : macc + string :=
  match l with
  | [] => inl acc
  | (r, e) :: t =>
      if skip r then match_regs_f isv skip t P acc
      else match pm_get r (vs_regs P) with
           | None => inr "match: register tracked in stored state is Top in path state"
           | Some e' => match_regs_f isv skip t P (match_loc_f isv acc e e')
           end
  end.

Lemma match_regs_f_eq isv skip P : forall l acc, match_regs_f isv skip l P acc = match_regs isv skip l P acc.
Proof.
  induction l as [|[r e] t IH]; intros acc; cbn [match_regs_f match_regs]; [reflexivity|].
  destruct (skip r); [apply IH|]. destruct (pm_get r (vs_regs P)); [|reflexivity]. rewrite match_loc_f_eq. apply IH.
Qed.

(* [comment removed for export] *)
Definition norm_w (P : vstate) (w : Z) (e : lin) : option lin :=
  if Z.leb 8 w then Some e else
  let M := 2 ^ (8 * w) in
  if lin_is_const e then Some (lconst ((lc e) mod M))
  else
    let mr := lin_cong (scong (vs_store P)) e in
    if Z.ltb 1 (fst mr) && Z.eqb (fst mr mod M) 0 then Some (lconst (snd mr mod M))
    else match lp_bounds (vs_store P) e with
         | (Some lo, Some hi) => if Z.eqb (lo / M) (hi / M) then Some (laddc e (- ((lo / M) * M))) else None
         | _ => None
         end.

Definition const_slice_cell (pm : cellmap) (k w : Z) : option lin :=
  match find (fun c : Z * cell =>
                match c with
                | (o2, (w2, Some v2)) => Z.leb o2 k && Z.leb (k + w) (o2 + w2) && lin_is_const v2
                | _ => false
                end) (cm_overlapping pm k (k + w)) with
  | Some (o2, (w2, Some v2)) => Some (lconst (const_slice (lc v2) w2 (k - o2) w))
  | _ => None
  end.

Definition path_cell (cs : bool) (P : vstate) (pm : cellmap) (k w : Z) : option lin :=
  match cm_get pm k with
  | Some (w', Some e') =>
      if Z.eqb w w' then (if cs then norm_w P w e' else Some e')
      else if cs then const_slice_cell pm k w else None
  | Some (_, None) => None
  | None => if cs then const_slice_cell pm k w else None
  end.

Fixpoint match_cells (isv : sym -> bool) (cs : bool) (P : vstate) (l : cellmap) (pm : cellmap) (acc : macc) : macc + string :=
  match l with
  | [] => inl acc
  | (k, (w, None)) :: t => match_cells isv cs P t pm acc
  | (k, (w, Some e)) :: t =>
      match path_cell cs P pm k w with
      | Some e' => match_cells isv cs P t pm (match_loc isv acc e e')
      | None => inr "match: cell tracked in stored state is absent/Top/unnormalisable in path state"
      end
  end.

Fixpoint check_defer (sigma : pmap lin) (l : list (lin * lin)) : bool :=
  match l with
  | [] => true
  | (e, e') :: t => lin_eqb (lsubst sigma e) e' && check_defer sigma t
  end.

(* [comment removed for export] *)
Fixpoint check_defer_f (sigma : pmap lin) (l : list (lin * lin)) : bool :=
  match l with
  | [] => true
  | (e, e') :: t =>
      if (match e with
          | mkLin Z0 [(J, Zpos xH)] => lin_eqb (match pm_get J sigma with Some e2 => e2 | None => e end) e'
          | mkLin _ [] => lin_eqb e e'
          | _ => lin_eqb (lsubst sigma e) e'
          end)
      then check_defer_f sigma t else false
  end.

Lemma lsubst_bare sigma J : lsubst sigma {| lc := 0; lt := [(J, 1%Z)] |} = match pm_get J sigma with Some e2 => e2 | None => {| lc := 0; lt := [(J, 1%Z)] |} end.
Proof.
  unfold lsubst. cbn [lc lt terms_subst]. destruct (pm_get J sigma) as [e2|].
  - unfold laxpy, lconst. cbn [Z.eqb lc lt terms_axpy]. rewrite terms_scale_1. destruct e2 as [c2 l2]. cbn [lc lt]. destruct c2; reflexivity.
  - reflexivity.
Qed.

Lemma check_defer_f_eq sigma l : check_defer_f sigma l = check_defer sigma l.
Proof.
  induction l as [|[e e'] t IH]; cbn [check_defer_f check_defer]; [reflexivity|]. rewrite IH.
  destruct e as [c l0]. destruct l0 as [|[J k] t0].
  - change (lsubst sigma {| lc := c; lt := [] |}) with (lconst c). unfold lconst. destruct c; reflexivity.
  - destruct c; try reflexivity. destruct k as [|[k|k|]|k]; try reflexivity. destruct t0; try reflexivity.
    rewrite lsubst_bare. reflexivity.
Qed.

(* [comment removed for export] *)
Definition nul_implied (pn : list (Z * Z)) (f : Z * Z) : bool :=
  existsb (fun g : Z * Z => Z.leb (fst f) (fst g) && Z.leb (snd g) (snd f)) pn.

Definition incl_list (a b : list Z) : bool := forallb (fun x => existsb (Z.eqb x) b) a.

(* [comment removed for export] *)
Definition sym_image (sigma : pmap lin) (s : sym) : option sym :=
  match pm_get s sigma with
  | None => Some s
  | Some e => match lin_single e with
              | Some (s', k) => if Z.eqb k 1 && Z.eqb (lc e) 0 then Some s' else None
              | None => None
              end
  end.

Definition match_valsets (sigma : pmap lin) (S P : vstate) : bool :=
  forallb (fun sv : positive * list Z =>
             match sym_image sigma (fst sv) with
             | Some s' => match pm_get s' (vs_valset P) with
                          | Some vs' => incl_list vs' (snd sv)
                          | None => false
                          end
             | None => false
             end) (pm_elements (vs_valset S)).

Definition match_conddefs (sigma : pmap lin) (S P : vstate) : bool :=
  forallb (fun bd : positive * (ckind * lin * lin) =>
             match bd with (b, (k, x, y)) =>
             match sym_image sigma b with
             | Some b' => match pm_get b' (vs_conddef P) with
                          | Some (k', x', y') => ckind_eqb k k' && lin_eqb (lsubst sigma x) x' && lin_eqb (lsubst sigma y) y'
                          | None => false
                          end
             | None => false
             end end) (pm_elements (vs_conddef S)).

Definition match_moddefs (sigma : pmap lin) (S P : vstate) : bool :=
  forallb (fun rd : positive * (lin * Z) =>
             match rd with (r, (x, m)) =>
             match sym_image sigma r with
             | Some r' => match pm_get r' (vs_moddef P) with
                          | Some (x', m') => Z.eqb m m' && lin_eqb (lsubst sigma x) x'
                          | None => false
                          end
             | None => false
             end end) (pm_elements (vs_moddef S)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition match_state_v1 (isv : sym -> bool) (skip : positive -> bool) (cs : bool) (sigma0 : pmap lin) (S P : vstate) : mres :=
  match match_regs isv skip (pm_elements (vs_regs S)) P (sigma0, []) with
  | inr m => MFail m
  | inl acc1 =>
  match match_cells isv cs P (vs_slots S) (vs_slots P) acc1 with
  | inr m => MFail m
  | inl acc2 =>
  match match_cells isv cs P (vs_globs S) (vs_globs P) acc2 with
  | inr m => MFail m
  | inl (sigma, defer) =>
      if negb (check_defer sigma defer) then MFail "match: a stored location's lin does not match the path lin under sigma"
      else if negb (forallb (nul_implied (vs_nul P)) (vs_nul S)) then MFail "match: a NUL fact of the stored state is not implied"
      else if negb (match_valsets sigma S P) then MFail "match: valset not matched"
      else if negb (match_conddefs sigma S P) then MFail "match: conddef not matched"
      else if negb (match_moddefs sigma S P) then MFail "match: moddef not matched"
      else if negb (store_entails (vs_store P) sigma (vs_store S)) then MFail "match: store facts of the stored state not entailed"
      else MOk sigma
  end end end.

Fixpoint cm_drop (pm : cellmap) (k : Z) : cellmap :=
  match pm with
  | [] => []
  | (k', c) :: t => if Z.ltb k' k then cm_drop t k else pm
  end.

Lemma cm_get_drop pm k : cm_get (cm_drop pm k) k = cm_get pm k.
Proof.
  induction pm as [|[k' c] t IH]; cbn [cm_drop]; [reflexivity|].
  destruct (Z.ltb_spec k' k) as [H|H].
  - rewrite IH. cbn [cm_get]. rewrite (proj2 (Z.compare_lt_iff k' k) H). reflexivity.
  - reflexivity.
Qed.

Lemma cm_drop_drop pm p k : p <= k -> cm_drop (cm_drop pm p) k = cm_drop pm k.
Proof.
  intros Hpk. induction pm as [|[k' c] t IH]; cbn [cm_drop]; [reflexivity|].
  destruct (Z.ltb_spec k' p) as [H|H].
  - rewrite IH. destruct (Z.ltb_spec k' k); [reflexivity|lia].
  - reflexivity.
Qed.

Definition path_cell_f (cs : bool) (P : vstate) (pm cur : cellmap) (k w : Z) : option lin :=
  match cm_get cur k with
  | Some (w', Some e') =>
      if Z.eqb w w' then (if cs then norm_w P w e' else Some e')
      else if cs then const_slice_cell pm k w else None
  | Some (_, None) => None
  | None => if cs then const_slice_cell pm k w else None
  end.

Lemma path_cell_f_eq cs P pm k w : path_cell_f cs P pm (cm_drop pm k) k w = path_cell cs P pm k w.
Proof. unfold path_cell_f, path_cell. rewrite cm_get_drop. reflexivity. Qed.

Fixpoint match_cells_f (isv : sym -> bool) (cs : bool) (P : vstate) (l : cellmap) (pm cur : cellmap) (prev : option Z)
         (acc : macc) : macc + string :=
  match l with
  | [] => inl acc
  | (k, (w, None)) :: t => match_cells_f isv cs P t pm cur prev acc
  | (k, (w, Some e)) :: t =>
      let cur1 := cm_drop (match prev with Some p => if Z.ltb k p then pm else cur | None => pm end) k in
      match path_cell_f cs P pm cur1 k w with
      | Some e' => match_cells_f isv cs P t pm cur1 (Some k) (match_loc isv acc e e')
      | None => inr "match: cell tracked in stored state is absent/Top/unnormalisable in path state"
      end
  end.

Lemma match_cells_f_eq isv cs P pm : forall l cur prev acc,
  (match prev with Some p => cur = cm_drop pm p | None => True end) ->
  match_cells_f isv cs P l pm cur prev acc = match_cells isv cs P l pm acc.
Proof.
  induction l as [|[k [w [e|]]] t IH]; intros cur prev acc Hinv; cbn [match_cells_f match_cells]; [reflexivity| |now apply IH].
  assert (Hc : cm_drop (match prev with Some p => if Z.ltb k p then pm else cur | None => pm end) k = cm_drop pm k).
  { destruct prev as [p|]; [|reflexivity]. destruct (Z.ltb_spec k p); [reflexivity|]. subst cur. apply cm_drop_drop. lia. }
  rewrite Hc, path_cell_f_eq.
  destruct (path_cell cs P pm k w) as [e'|]; [|reflexivity].
  apply IH. reflexivity.
Qed.

(* [comment removed for export] *)
Definition mc_fast (cs : bool) (cur : cellmap) (prev : option Z) (k w : Z) : option (cellmap * lin) :=
  if cs then None else
  match prev with
  | Some p =>
      match cur with
      | _ :: cur1 =>
          match cur1 with
          | (k', (w', Some e')) :: _ =>
              match Z.compare k p with
              | Gt => if Z.eqb k' k then (if Z.eqb w w' then Some (cur1, e') else None) else None
              | _ => None
              end
          | _ => None
          end
      | [] => None
      end
  | None => None
  end.

Fixpoint match_cells_h (isv : sym -> bool) (cs : bool) (P : vstate) (l : cellmap) (pm cur : cellmap) (prev : option Z)
         (acc : macc) : macc + string :=
  match l with
  | [] => inl acc
  | (k, (w, None)) :: t => match_cells_h isv cs P t pm cur prev acc
  | (k, (w, Some e)) :: t =>
      match mc_fast cs cur prev k w with
      | Some (cur1, e') => match_cells_h isv cs P t pm cur1 (Some k) (match_loc_f isv acc e e')
      | None =>
          let cur1 := cm_drop (match prev with Some p => if Z.ltb k p then pm else cur | None => pm end) k in
          match path_cell_f cs P pm cur1 k w with
          | Some e' => match_cells_h isv cs P t pm cur1 (Some k) (match_loc_f isv acc e e')
          | None => inr "match: cell tracked in stored state is absent/Top/unnormalisable in path state"
          end
      end
  end.

(* [comment removed for export] *)
Definition mc_inv (cs : bool) (prev : option Z) (cur : cellmap) : Prop :=
  cs = false -> forall p, prev = Some p -> exists c t, cur = (p, c) :: t.

Lemma cm_get_drop_head m k c : cm_get (cm_drop m k) k = Some c -> exists t, cm_drop m k = (k, c) :: t.
Proof.
  induction m as [|[k' c'] t IH]; cbn [cm_drop]; [discriminate|].
  destruct (Z.ltb_spec k' k) as [H|H]; [exact IH|].
  cbn [cm_get]. destruct (Z.compare_spec k' k) as [E|E|E]; intros X; try discriminate; [|lia].
  injection X as <-. subst k'. exists t. reflexivity.
Qed.

Lemma mc_fast_spec cs P pm cur prev k w cur1 e' :
  mc_fast cs cur prev k w = Some (cur1, e') -> mc_inv cs prev cur ->
  cs = false
  /\ cm_drop (match prev with Some p => if Z.ltb k p then pm else cur | None => pm end) k = cur1
  /\ path_cell_f cs P pm cur1 k w = Some e'
  /\ exists c t, cur1 = (k, c) :: t.
Proof.
  unfold mc_fast. destruct cs; [discriminate|]. destruct prev as [p|]; [|discriminate].
  destruct cur as [|hd c1]; [discriminate|]. destruct c1 as [|[k' [w' [e1|]]] t1]; try discriminate.
  destruct (Z.compare_spec k p) as [E|E|E]; try discriminate.
  destruct (Z.eqb_spec k' k) as [Ek|Ek]; [|discriminate]. destruct (Z.eqb_spec w w') as [Ew|Ew]; [|discriminate].
  intros X Inv. injection X as <- <-. subst k' w'.
  destruct (Inv eq_refl p eq_refl) as (c0 & t0 & Hc). injection Hc as -> _.
  split; [reflexivity|]. split; [|split].
  - destruct (Z.ltb_spec k p); [lia|]. cbn [cm_drop]. destruct (Z.ltb_spec p k); [|lia].
    destruct (Z.ltb_spec k k); [lia|]. reflexivity.
  - unfold path_cell_f. cbn [cm_get]. rewrite Z.compare_refl, Z.eqb_refl. reflexivity.
  - eauto.
Qed.

Lemma match_cells_h_eq isv cs P pm : forall l cur prev acc,
  mc_inv cs prev cur ->
  match_cells_h isv cs P l pm cur prev acc = match_cells_f isv cs P l pm cur prev acc.
Proof.
  induction l as [|[k [w [e|]]] t IH]; intros cur prev acc Inv; cbn [match_cells_h match_cells_f]; [reflexivity| |now apply IH].
  destruct (mc_fast cs cur prev k w) as [[cur1 e']|] eqn:F.
  - destruct (mc_fast_spec cs P pm cur prev k w cur1 e' F Inv) as (Hcs & Hd & Hp & c & t1 & Hc).
    rewrite Hd, Hp, match_loc_f_eq. apply IH. intros _ p Hp'. injection Hp' as <-. eauto.
  - set (cur1 := cm_drop (match prev with Some p => if Z.ltb k p then pm else cur | None => pm end) k).
    destruct (path_cell_f cs P pm cur1 k w) as [e'|] eqn:PC; [|reflexivity].
    rewrite match_loc_f_eq. apply IH. intros Hcs p Hp'. injection Hp' as <-. subst cs.
    unfold path_cell_f in PC. destruct (cm_get cur1 k) as [c|] eqn:G; [|discriminate].
    destruct (cm_get_drop_head _ _ _ G) as (t1 & Ht). exists c, t1. exact Ht.
Qed.

Definition nul_implied_l (pn : list (Z * Z)) (f : Z * Z) : bool :=
  existsb_l (fun g : Z * Z => if Z.leb (fst f) (fst g) then Z.leb (snd g) (snd f) else false) pn.

Lemma nul_implied_l_eq pn f : nul_implied_l pn f = nul_implied pn f.
Proof. unfold nul_implied_l, nul_implied. rewrite existsb_l_eq. reflexivity. Qed.

Lemma forallb_l_nul pn l : forallb_l (nul_implied_l pn) l = forallb (nul_implied pn) l.
Proof. induction l as [|f t IH]; cbn [forallb_l forallb]; [reflexivity|]. rewrite nul_implied_l_eq, IH. reflexivity. Qed.

Definition match_state (isv : sym -> bool) (skip : positive -> bool) (cs : bool) (sigma0 : pmap lin) (S P : vstate) : mres :=
  match match_regs_f isv skip (pm_elements (vs_regs S)) P (sigma0, []) with
  | inr m => MFail m
  | inl acc1 =>
  match match_cells_h isv cs P (vs_slots S) (vs_slots P) (vs_slots P) None acc1 with
  | inr m => MFail m
  | inl acc2 =>
  match match_cells_h isv cs P (vs_globs S) (vs_globs P) (vs_globs P) None acc2 with
  | inr m => MFail m
  | inl (sigma, defer) =>
      if negb (check_defer_f sigma defer) then MFail "match: a stored location's lin does not match the path lin under sigma"
      else if negb (forallb_l (nul_implied_l (vs_nul P)) (vs_nul S)) then MFail "match: a NUL fact of the stored state is not implied"
      else if negb (match_valsets sigma S P) then MFail "match: valset not matched"
      else if negb (match_conddefs sigma S P) then MFail "match: conddef not matched"
      else if negb (match_moddefs sigma S P) then MFail "match: moddef not matched"
      else if negb (store_entails (vs_store P) sigma (vs_store S)) then MFail "match: store facts of the stored state not entailed"
      else MOk sigma
  end end end.

Lemma match_state_v1_eq isv skip cs sigma0 S P : match_state isv skip cs sigma0 S P = match_state_v1 isv skip cs sigma0 S P.
Proof.
  unfold match_state, match_state_v1. rewrite match_regs_f_eq.
  destruct (match_regs isv skip (pm_elements (vs_regs S)) P (sigma0, [])) as [acc1|m]; [|reflexivity].
  assert (InvN : forall m, mc_inv cs None m) by (intros m _ p X; discriminate).
  rewrite (match_cells_h_eq isv cs P (vs_slots P) (vs_slots S) (vs_slots P) None acc1 (InvN _)).
  rewrite (match_cells_f_eq isv cs P (vs_slots P) (vs_slots S) (vs_slots P) None acc1 I).
  destruct (match_cells isv cs P (vs_slots S) (vs_slots P) acc1) as [acc2|m]; [|reflexivity].
  rewrite (match_cells_h_eq isv cs P (vs_globs P) (vs_globs S) (vs_globs P) None acc2 (InvN _)).
  rewrite (match_cells_f_eq isv cs P (vs_globs P) (vs_globs S) (vs_globs P) None acc2 I).
  destruct (match_cells isv cs P (vs_globs S) (vs_globs P) acc2) as [[sigma defer]|m]; [|reflexivity].
  rewrite forallb_l_nul, check_defer_f_eq. reflexivity.
Qed.

(* [comment removed for export] *)
Definition isv_join (s : sym) : bool := Pos.leb JOIN0 s.
(* [comment removed for export] *)
Definition isv_call (s : sym) : bool :=
  negb (Pos.eqb s SP0 || Pos.eqb s DATA || Pos.eqb s SIZE || Pos.eqb s TP || Pos.eqb s GP).

Definition no_skip (_ : positive) : bool := false.
