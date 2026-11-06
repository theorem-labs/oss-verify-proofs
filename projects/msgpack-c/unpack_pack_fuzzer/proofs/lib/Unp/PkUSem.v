(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem State Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model OpsBridge PkOps GLib PkU PkUSwap.
Import ListNotations.
Import W64 Val Mem St Step UB HeapOp UG PK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PkUSem.
Section Sem.
Variable E : env.
Variable fs : list fact.
Hypothesis Hfs : facts_hold E fs.
Notation D := (map (wden E)).

Theorem flip_sound : forall ok fr' ws ws1, PkU.pku_flip fs ok fr' ws = Some ws1 ->
  length ws1 = length ws /\
  (forall a, in_ws (D ws1) a <-> in_ws (D ws) a) /\
  (forall LB, wins_keep LB (D ws) (D ws1)) /\
  (forall segs IMGX (A : alloc_world segs IMGX) LB ceil, ceil <= Mem.two62Z -> windows_wf (D ws) LB ceil -> windows_wf (D ws1) LB ceil) /\
  (forall g, wins_pk g (D ws) -> wins_pk g (D ws1)) /\
  (forall g, ghost_pk g (D ws) -> ghost_pk g (D ws1)) /\
  (forall u g ls u' g' ls', cost_pk u g ls (D ws) ->
     (forall fr v, ok fr = true -> np (k_tree g) ls fr (a_cf u =? 0) <= v -> np (k_tree g') ls' fr' (a_cf u' =? 0) <= v) ->
     cost_pk u' g' ls' (D ws1)).
Proof.
  intros ok fr' ws ws1 H. unfold PkU.pku_flip in H.
  destruct (PkU.scan fs ws) as [[[[pre [fr u]] post]|]|] eqn:SC; [| | discriminate].
  - destruct (ok fr) eqn:OK; [| discriminate]. injection H as <-.
    destruct (PkU.scan_some E fs Hfs ws pre fr u post SC) as (-> & UB & PV & NO).
    pose proof (PkU.mk_pku_val E fr' u UB) as PV'.
    rewrite !map_app. cbn [map].
    split; [rewrite !length_app; reflexivity|].
    split; [exact (PkUSwap.swap_in_ws (D pre) (D post) _ _ _ _ PV PV')|].
    split; [exact (PkUSwap.swap_keep (D pre) (D post) _ _ _ _ PV PV')|].
    split; [intros segs IMGX A LB ceil; exact (PkUSwap.swap_wf (D pre) (D post) _ _ _ PV' segs IMGX A LB ceil)|].
    split; [exact (PkUSwap.swap_wins_pk (D pre) (D post) _ _ _ PV')|].
    split; [exact (PkUSwap.swap_ghost (D pre) (D post) _ _ _ _ PV PV')|].
    intros u0 g ls u' g' ls' CO MONO.
    apply (PkUSwap.swap_cost (D pre) (D post) _ _ PV').
    + intros x Hx. rewrite <- map_app in Hx. apply in_map_iff in Hx as (y & <- & Hy). exact (NO y Hy).
    + cbn [fst snd]. apply (MONO fr); [exact OK|].
      exact (PkUSwap.old_cost (D pre) (D post) _ _ PV u0 g ls CO).
  - injection H as <-. pose proof (PkU.scan_none E fs Hfs ws SC) as NO.
    split; [reflexivity|]. split; [tauto|]. split; [intros LB; apply wins_keep_refl|]. split; [intros; assumption|]. split; [intros; assumption|]. split; [intros; assumption|].
    intros u0 g ls u' g' ls' _ _. apply PkUSwap.cost_none. intros x Hx. apply in_map_iff in Hx as (y & <- & Hy). exact (NO y Hy).
Qed.

Theorem move_sound : forall ok fr' u' ws uo ws1, PkU.pku_move fs ok fr' u' ws = Some (uo, ws1) ->
  bv_unsigned (ev E u') <= 2 ^ 41 ->
  length ws1 = length ws /\
  (forall a, in_ws (D ws1) a <-> in_ws (D ws) a) /\
  (forall LB, wins_keep LB (D ws) (D ws1)) /\
  (forall segs IMGX (A : alloc_world segs IMGX) LB ceil, ceil <= Mem.two62Z -> windows_wf (D ws) LB ceil -> windows_wf (D ws1) LB ceil) /\
  (forall g, wins_pk g (D ws) -> wins_pk g (D ws1)) /\
  (forall g, ghost_pk g (D ws) -> ghost_pk g (D ws1)) /\
  (forall u g ls ua' g' ls', cost_pk u g ls (D ws) ->
     (forall fr uold, uo = Some uold -> ok fr = true -> np (k_tree g) ls fr (a_cf u =? 0) <= bv_unsigned (ev E uold) ->
        np (k_tree g') ls' fr' (a_cf ua' =? 0) <= bv_unsigned (ev E u')) ->
     cost_pk ua' g' ls' (D ws1)) /\
  (uo = None -> ws1 = ws) /\
  (forall uold, uo = Some uold -> bv_unsigned (ev E uold) <= 2 ^ 41 /\ exists pre fr post, ok fr = true /\ ws = pre ++ PkU.mk_pku fr uold :: post /\ ws1 = pre ++ PkU.mk_pku fr' u' :: post).
Proof.
  intros ok fr' u' ws uo ws1 H UB'. unfold PkU.pku_move in H.
  destruct (PkU.scan fs ws) as [[[[pre [fr u]] post]|]|] eqn:SC; [| | discriminate].
  - destruct (ok fr) eqn:OK; [| discriminate]. injection H as <- <-.
    destruct (PkU.scan_some E fs Hfs ws pre fr u post SC) as (-> & UB & PV & NO).
    pose proof (PkU.mk_pku_val E fr' u' UB') as PV'.
    rewrite !map_app. cbn [map].
    split; [rewrite !length_app; reflexivity|].
    split; [exact (PkUSwap.swap_in_ws (D pre) (D post) _ _ _ _ PV PV')|].
    split; [exact (PkUSwap.swap_keep (D pre) (D post) _ _ _ _ PV PV')|].
    split; [intros segs IMGX A LB ceil; exact (PkUSwap.swap_wf (D pre) (D post) _ _ _ PV' segs IMGX A LB ceil)|].
    split; [exact (PkUSwap.swap_wins_pk (D pre) (D post) _ _ _ PV')|].
    split; [exact (PkUSwap.swap_ghost (D pre) (D post) _ _ _ _ PV PV')|].
    split.
    + intros u0 g ls ua' g' ls' CO MONO.
      apply (PkUSwap.swap_cost (D pre) (D post) _ _ PV').
      * intros x Hx. rewrite <- map_app in Hx. apply in_map_iff in Hx as (y & <- & Hy). exact (NO y Hy).
      * cbn [fst snd]. apply (MONO fr u eq_refl OK).
        exact (PkUSwap.old_cost (D pre) (D post) _ _ PV u0 g ls CO).
    + split; [discriminate|]. intros uold [= <-]. split; [exact UB|]. exists pre, fr, post. split; [exact OK|]. split; reflexivity.
  - injection H as <- <-. pose proof (PkU.scan_none E fs Hfs ws SC) as NO.
    split; [reflexivity|]. split; [tauto|]. split; [intros LB; apply wins_keep_refl|]. split; [intros; assumption|]. split; [intros; assumption|]. split; [intros; assumption|].
    split; [| split; [reflexivity| discriminate]].
    intros u0 g ls ua' g' ls' _ _. apply PkUSwap.cost_none. intros x Hx. apply in_map_iff in Hx as (y & <- & Hy). exact (NO y Hy).
Qed.

Lemma move_old : forall ok fr' u' ws uold ws1, PkU.pku_move fs ok fr' u' ws = Some (Some uold, ws1) ->
  exists pre fr post, ok fr = true /\ ws = pre ++ PkU.mk_pku fr uold :: post /\ ws1 = pre ++ PkU.mk_pku fr' u' :: post /\
    bv_unsigned (ev E uold) <= 2 ^ 41 /\ pku_val (wden E (PkU.mk_pku fr uold)) = Some (fr, bv_unsigned (ev E uold)).
Proof.
  intros ok fr' u' ws uold ws1 H. unfold PkU.pku_move in H.
  destruct (PkU.scan fs ws) as [[[[pre [fr u]] post]|]|] eqn:SC; [| discriminate| discriminate].
  destruct (ok fr) eqn:OK; [| discriminate]. injection H as <- <-.
  destruct (PkU.scan_some E fs Hfs ws pre fr u post SC) as (-> & UB & PV & NO).
  exists pre, fr, post. repeat split; assumption.
Qed.
End Sem.

Lemma flip_members : forall fs ok fr' ws ws1, PkU.pku_flip fs ok fr' ws = Some ws1 ->
  forall w, In w ws1 -> In w ws \/ exists fr u, w = PkU.mk_pku fr' u /\ In (PkU.mk_pku fr u) ws.
Proof.
  intros fs ok fr' ws ws1 H w Hw. unfold PkU.pku_flip in H.
  destruct (PkU.scan fs ws) as [[[[pre [fr u]] post]|]|] eqn:SC; [| injection H as <-; left; exact Hw| discriminate].
  destruct (ok fr); [| discriminate]. injection H as <-.
  assert (WS : ws = pre ++ PkU.mk_pku fr u :: post).
  { clear - SC. revert pre SC. induction ws as [|w0 ws IH]; intros pre SC; [discriminate|]. cbn [PkU.scan] in SC.
    destruct (PkU.not_pku fs w0).
    - destruct (PkU.scan fs ws) as [[[[pre' x'] post']|]|] eqn:S2; try discriminate. injection SC as E1 E2 E3. subst pre x' post'.
      cbn [app]. f_equal. exact (IH pre' eq_refl).
    - destruct (PkU.pku_of fs w0) as [x|] eqn:PO; [| discriminate]. destruct (forallb (PkU.not_pku fs) ws); [| discriminate]. injection SC as E1 E2 E3. subst pre x post.
      cbn [app]. f_equal. unfold PkU.pku_of in PO. destruct w0 as [[lo len] kd].
      destruct lo as [|u0 off| | | | | | | | |]; try discriminate. destruct len as [z| | | | | | | | | |]; try discriminate.
      destruct kd as [k| | | | | | | | | |]; try discriminate.
      match type of PO with (if ?c then _ else _) = _ => destruct c eqn:C; [| discriminate] end.
      apply andb_prop in C as [C _]. apply andb_prop in C as [Z0 K0]. apply (proj1 (weqb_ok _ _)) in Z0. apply (proj1 (weqb_ok _ _)) in K0. subst z k.
      destruct (weqb off (wlit PkU.BASE_F)) eqn:OF; [injection PO as EP; inversion EP; subst; apply (proj1 (weqb_ok _ _)) in OF; subst off; reflexivity|].
      destruct (weqb off (wlit PkU.BASE_N)) eqn:ON; [| discriminate]. injection PO as EP. inversion EP; subst. apply (proj1 (weqb_ok _ _)) in ON. subst off. reflexivity. }
  subst ws. apply in_app_iff in Hw as [Hw|[<-|Hw]].
  - left. apply in_app_iff. left. exact Hw.
  - right. exists fr, u. split; [reflexivity|]. apply in_app_iff. right. left. reflexivity.
  - left. apply in_app_iff. right. right. exact Hw.
Qed.

Lemma mk_pku_den : forall E E' fr fr' u, wden E' (PkU.mk_pku fr u) = wden E (PkU.mk_pku fr u) -> wden E' (PkU.mk_pku fr' u) = wden E (PkU.mk_pku fr' u).
Proof.
  intros E E' fr fr' u H. unfold PkU.mk_pku, wden in *. injection H as H.
  assert (C : forall a b : bv 64, bv_sub (bv_add a b) b = a).
  { intros a b. apply bv_eq. rewrite bv_sub_unsigned, bv_add_unsigned. unfold bv_wrap.
    pose proof (bv_unsigned_in_range _ a) as Ra. set (M := bv_modulus 64) in *.
    rewrite Zminus_mod_idemp_l. replace (bv_unsigned a + bv_unsigned b - bv_unsigned b) with (bv_unsigned a) by lia. apply Z.mod_small. lia. }
  assert (EV : ev E' u = ev E u).
  { cbn [den] in H. apply bv_eq in H. rewrite <- (C (ev E' u) (wbv (wlit (if fr then PkU.BASE_F else PkU.BASE_N)))), H. apply C. }
  cbn [den]. rewrite EV. reflexivity.
Qed.
Lemma mk_pku_ev : forall E E' fr u, wden E' (PkU.mk_pku fr u) = wden E (PkU.mk_pku fr u) -> ev E' u = ev E u.
Proof.
  intros E E' fr u H. unfold PkU.mk_pku, wden in *. injection H as H.
  assert (C : forall a b : bv 64, bv_sub (bv_add a b) b = a).
  { intros a b. apply bv_eq. rewrite bv_sub_unsigned, bv_add_unsigned. unfold bv_wrap.
    pose proof (bv_unsigned_in_range _ a) as Ra. set (M := bv_modulus 64) in *.
    rewrite Zminus_mod_idemp_l. replace (bv_unsigned a + bv_unsigned b - bv_unsigned b) with (bv_unsigned a) by lia. apply Z.mod_small. lia. }
  cbn [den] in H. apply bv_eq in H. rewrite <- (C (ev E' u) (wbv (wlit (if fr then PkU.BASE_F else PkU.BASE_N)))), H. apply C.
Qed.
Lemma flip_transport : forall E E' fs ok fr' ws ws1, PkU.pku_flip fs ok fr' ws = Some ws1 ->
  (forall w, In w ws -> wden E' w = wden E w) -> map (wden E') ws1 = map (wden E) ws1.
Proof.
  intros E E' fs ok fr' ws ws1 H OLD. apply map_ext_in. intros w Hw.
  destruct (flip_members fs ok fr' ws ws1 H w Hw) as [Hin|(fr & u & -> & Hin)]; [exact (OLD w Hin)|].
  exact (mk_pku_den E E' fr fr' u (OLD _ Hin)).
Qed.
End PkUSem.
