(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Bool String.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ASYM (i : Z) : sym := Z.to_pos (19 + i).       (* [comment removed for export] *)
Definition CSYM (k : Z) : sym := Z.to_pos (27 + k).       (* [comment removed for export] *)
Definition LAST_UFIXED : sym := 63%positive.
Definition JOIN0 : sym := 64%positive.                    (* [comment removed for export] *)
Definition is_ufixed (s : sym) : bool := Pos.leb s LAST_UFIXED.

(* [comment removed for export] *)
Record cstate := mkCS {
  cs_regs : list (Z * lin) ;                 (* [comment removed for export] *)
  cs_slots : list (Z * (Z * lin)) ;          (* [comment removed for export] *)
  cs_globs : list (Z * (Z * lin)) ;          (* [comment removed for export] *)
  cs_box : list (sym * itv) ;
  cs_cong : list (sym * (Z * Z)) ;
  cs_cons : list lin ;                       (* [comment removed for export] *)
  cs_nul : list (Z * Z) ;
  cs_valset : list (sym * list Z) ;
  cs_conddef : list (sym * (ckind * lin * lin)) ;
  cs_moddef : list (sym * (lin * Z)) ;
  cs_next : positive                         (* [comment removed for export] *)
}.

Record vcut := mkCut {
  cut_pc : Z ;
  cut_ctx : list Z ;                         (* [comment removed for export] *)
  cut_states : list cstate ;                 (* [comment removed for export] *)
  cut_ranks : list lin                       (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Record vcall := mkCall { call_pc : Z ; call_target : Z ; call_vid : Z }.

Record vunit := mkUnit {
  u_entry : Z ;                              (* [comment removed for export] *)
  u_vid : Z ;                                (* [comment removed for export] *)
  u_sp : Z ;                                 (* [comment removed for export] *)
  u_sclass : Z * Z ;                         (* [comment removed for export] *)
  u_pre : cstate ;                           (* [comment removed for export] *)
  u_cuts : list vcut ;
  u_exits : list cstate ;
  u_wstack : list (Z * Z) ;                  (* [comment removed for export] *)
  u_wglobs : list (Z * Z) ;                  (* [comment removed for export] *)
  u_errno : bool ;                           (* [comment removed for export] *)
  u_own : Z ;                                (* [comment removed for export] *)
  u_calls : list vcall ;
  u_fuel : N ;                               (* [comment removed for export] *)
  u_root : option Z ;                        (* [comment removed for export] *)
  u_prio : Z                                 (* [comment removed for export] *)
}.

Definition vcert := list vunit.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint cm_of_list (l : list (Z * (Z * lin))) : cellmap :=
  match l with
  | [] => []
  | (k, (w, e)) :: t => (k, (w, Some e)) :: cm_of_list t
  end.

Definition store_of (cs : cstate) : store :=
  mkStore (pm_of_list (cs_box cs)) (cs_cons cs) (pm_of_list (cs_cong cs)).

Definition load_cstate (cs : cstate) (pc : Z) (ctx : list Z) : vstate :=
  mkVS pc
       (pm_of_list (map (fun re : Z * lin => (Z.to_pos (fst re), snd re)) (cs_regs cs)))
       (cm_of_list (cs_slots cs))
       (cm_of_list (cs_globs cs))
       (store_of cs)
       (cs_next cs)
       (pm_of_list (cs_conddef cs))
       (pm_of_list (cs_moddef cs))
       (pm_of_list (cs_valset cs))
       (cs_nul cs)
       ctx
       pm_empty.

(* [comment removed for export] *)
Definition cells_below_b (m : cellmap) (b : positive) : bool :=
  forallb (fun c : Z * cell => match c with (_, (_, Some e)) => lin_below e b | _ => true end) m.

Definition vstate_below_b (A : vstate) : bool :=
  let b := vs_next A in
  Pos.ltb LAST_FIXED b
  && store_below (vs_store A) b
  && pm_forallb (fun _ e => lin_below e b) (vs_regs A)
  && cells_below_b (vs_slots A) b
  && cells_below_b (vs_globs A) b
  && pm_forallb (fun s d => match d with (_, x, y) => Pos.ltb s b && lin_below x b && lin_below y b end) (vs_conddef A)
  && pm_forallb (fun s d => match d with (x, _) => Pos.ltb s b && lin_below x b end) (vs_moddef A)
  && pm_forallb (fun s _ => Pos.ltb s b) (vs_valset A).

Definition cstate_wf (cs : cstate) : bool :=
  Pos.leb JOIN0 (cs_next cs) && vstate_below_b (load_cstate cs 0 []).

(* [comment removed for export] *)
Definition cstate_wf_f (cs : cstate) : bool :=
  let b := cs_next cs in
  Pos.leb JOIN0 b
  && Pos.ltb LAST_FIXED b
  && forallb (fun si : sym * itv => Pos.ltb (fst si) b) (cs_box cs)
  && forallb (fun c : lin => terms_below b (lt c)) (cs_cons cs)
  && forallb (fun si : sym * (Z * Z) => Pos.ltb (fst si) b) (cs_cong cs)
  && forallb (fun re : Z * lin => lin_below (snd re) b) (cs_regs cs)
  && forallb (fun c : Z * (Z * lin) => lin_below (snd (snd c)) b) (cs_slots cs)
  && forallb (fun c : Z * (Z * lin) => lin_below (snd (snd c)) b) (cs_globs cs)
  && forallb (fun d : sym * (ckind * lin * lin) => match d with (s, (_, x, y)) => Pos.ltb s b && lin_below x b && lin_below y b end) (cs_conddef cs)
  && forallb (fun d : sym * (lin * Z) => match d with (s, (x, _)) => Pos.ltb s b && lin_below x b end) (cs_moddef cs)
  && forallb (fun d : sym * list Z => Pos.ltb (fst d) b) (cs_valset cs).

Lemma pm_forallb_of_list {A : Type} (f : positive -> A -> bool) (l : list (positive * A)) :
  forallb (fun kv => f (fst kv) (snd kv)) l = true -> pm_forallb f (pm_of_list l) = true.
Proof.
  intros H. unfold pm_forallb. apply forallb_forall. intros [k v] Hin. cbn [fst snd].
  apply pm_elements_sound in Hin. apply pm_of_list_get_in in Hin.
  rewrite forallb_forall in H. exact (H _ Hin).
Qed.

Lemma forallb_elements_of_list {A : Type} (f : positive * A -> bool) (l : list (positive * A)) :
  forallb f l = true -> forallb f (pm_elements (pm_of_list l)) = true.
Proof.
  intros H. apply forallb_forall. intros [k v] Hin.
  apply pm_elements_sound in Hin. apply pm_of_list_get_in in Hin.
  rewrite forallb_forall in H. exact (H _ Hin).
Qed.

Lemma cells_below_b_of_list (l : list (Z * (Z * lin))) b :
  forallb (fun c : Z * (Z * lin) => lin_below (snd (snd c)) b) l = true -> cells_below_b (cm_of_list l) b = true.
Proof.
  unfold cells_below_b. induction l as [|[k [w e]] t IH]; cbn [cm_of_list forallb fst snd]; [reflexivity|].
  intros H. apply andb_prop in H as [H1 H2]. rewrite H1, (IH H2). reflexivity.
Qed.

Lemma cstate_wf_f_sound cs : cstate_wf_f cs = true -> cstate_wf cs = true.
Proof.
  unfold cstate_wf_f, cstate_wf, vstate_below_b. cbv zeta. intros H.
  repeat (apply andb_prop in H as [H ?X]).
  cbn [load_cstate vs_next vs_store vs_regs vs_slots vs_globs vs_conddef vs_moddef vs_valset].
  rewrite H, X8. cbn [andb].
  assert (SB : store_below (store_of cs) (cs_next cs) = true).
  { unfold store_below, store_of. cbn [sbox scons scong].
    apply andb_true_intro. split; [apply andb_true_intro; split|].
    - apply forallb_elements_of_list. exact X7.
    - exact X6.
    - apply forallb_elements_of_list. exact X5. }
  rewrite SB. cbn [andb].
  assert (RG : pm_forallb (fun (_ : positive) (e : lin) => lin_below e (cs_next cs))
                 (pm_of_list (map (fun re : Z * lin => (Z.to_pos (fst re), snd re)) (cs_regs cs))) = true).
  { apply pm_forallb_of_list. rewrite forallb_forall in X4 |- *. intros kv Hin.
    apply in_map_iff in Hin as (re & <- & Hre). cbn [snd]. exact (X4 _ Hre). }
  rewrite RG, (cells_below_b_of_list _ _ X3), (cells_below_b_of_list _ _ X2). cbn [andb].
  rewrite (pm_forallb_of_list (fun s d => match d with (_, x, y) => Pos.ltb s (cs_next cs) && lin_below x (cs_next cs) && lin_below y (cs_next cs) end) (cs_conddef cs)).
  2:{ rewrite forallb_forall in X1 |- *. intros [s [[k x] y]] Hin. cbn [fst snd]. exact (X1 _ Hin). }
  rewrite (pm_forallb_of_list (fun s d => match d with (x, _) => Pos.ltb s (cs_next cs) && lin_below x (cs_next cs) end) (cs_moddef cs)).
  2:{ rewrite forallb_forall in X0 |- *. intros [s [x m]] Hin. cbn [fst snd]. exact (X0 _ Hin). }
  rewrite (pm_forallb_of_list (fun s _ => Pos.ltb s (cs_next cs)) (cs_valset cs)).
  2:{ rewrite forallb_forall in X |- *. intros [s vs] Hin. cbn [fst snd]. exact (X _ Hin). }
  reflexivity.
Qed.
