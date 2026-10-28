(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qv X1og X1qx X1r3
X1q8 X1po X1pv X1pm X1qn X1q5 X1pi.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qm X0px X0qn X0qc X0qp X0q7.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1ka.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation rsegs := Ubsan.M.loaded_segments.

Lemma conc_strip_eq st q : conc (strip st) q = conc st q.
Proof. reflexivity. Qed.

Theorem rfree_keeps_ptr_proof {RCEIL : RunCeiling} : rfree_keeps_ptr_stmt.
Proof.
intros s s' LB m p A n b sfH_; first [ sf_destruct 8%nat sfH_ as st LB0 PERM STRIP MREP [_ AR] _ _ | sf_fb; destruct sfH_ as (st & LB0 & PERM & STRIP & MREP & [_ AR] & _ & _) ]; intros Hp FL Hb.
first [ pose proof (areach_inv _ st LB0 AR) as sfP_; sf_destruct 8%nat sfP_ as L LS BL INV LIVE _ _ CR | sf_fb; destruct (areach_inv _ st LB0 AR) as (L & LS & BL & INV & LIVE & _ & _ & CR) ].

assert (Hp0 : In (p, A, n) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hp]).
unfold lb_remove in Hb. apply list_elem_of_In in Hb. apply list_elem_of_filter in Hb as [NEQ Hb]. apply list_elem_of_In in Hb.
assert (Hb0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb]).
destruct (Forall2_In_l _ _ _ _ CR Hp0) as (k & Hk & (C1 & C2 & C3)). cbn [blk_slot blk_size blk_addr fst snd] in C1, C2, C3.
destruct k as [[c off] nn]. cbn [bslot boff bsize fst snd] in C1, C2, C3, Hk. subst nn.
destruct (Forall2_In_l _ _ _ _ CR Hb0) as (kk & Hkk & (D1 & D2 & D3)).

assert (NE : bslot kk <> c).
{ intros E.
assert (EM : map blk_slot LB0 = map bslot BL) by (apply (Forall2_map_eq _ _ _ _ _ CR); intros ? ? (X1 & _); exact X1).
pose proof (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))) as ND. rewrite <- EM in ND. apply NoDup_ListNoDup in ND.
assert (SS : blk_slot b = blk_slot (p, A, n)) by (rewrite D1, E, C1; reflexivity).
assert (EQ : forall l (x y : block), List.NoDup (map blk_slot l) -> In x l -> In y l -> blk_slot x = blk_slot y -> x = y).
{ clear. induction l as [|z l IH]; intros x y ND Hx Hy Es; [destruct Hx|]. cbn in ND. inversion ND; subst.
destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
- reflexivity.
- exfalso. apply H1. rewrite Es. apply in_map. exact Hy.
- exfalso. apply H1. rewrite <- Es. apply in_map. exact Hx.
- exact (IH x y ltac:(assumption) Hx Hy Es). }
pose proof (EQ LB0 b (p, A, n) ND Hb0 Hp0 SS) as Eb. subst b.
unfold bptr_eqb in NEQ. cbn [blk_id fst snd] in NEQ. rewrite aptr_eqb_refl, Z.eqb_refl in NEQ. exact NEQ. }

destruct (raw_free_leaf p s s' FL) as [ans Hf]. rewrite <- STRIP in Hf. change (fst p) with (blk_slot (p, A, n)) in Hf. rewrite C1 in Hf.
pose proof (strel_follow (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk)) ans) as SF.
rewrite Hf in SF.
destruct (follow (prun pans0 pupd0 tt (free st (Some (aadd c (UNIT * off))))) ans) as [[o1 st1]|] eqn:FF; [| destruct SF].
unfold FREL in SF. cbn [snd] in SF.
destruct (free_leaf_facts pans0 pupd0 st L BL LS c off n tt ans o1 st1 INV Hk FF) as [SUB _].
first [ pose proof (free_sim pans0 pupd0 pans0_range st L BL LS c off n tt ans o1 st1 INV Hk FF) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ LS1 INV1 | sf_fb; destruct (free_sim pans0 pupd0 pans0_range st L BL LS c off n tt ans o1 st1 INV Hk FF) as (_ & _ & _ & LS1 & INV1) ].

assert (Hk2 : In kk (bl_remove c BL)).
{ rewrite (bl_remove_filter c BL (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))))).
apply list_elem_of_In. apply list_elem_of_filter. split; [| apply list_elem_of_In; exact Hkk].
rewrite (X1pv.aptr_eqb_neq _ _ NE). exact I. }
destruct (blk_region _ _ _ _ _ kk INV1 Hk2) as (r1 & Hr1 & _).
unfold ptr_addr. change (fst (blk_id b)) with (blk_slot b). rewrite D1, <- SF, <- STRIP, !conc_strip_eq.
rewrite (conc_same st st1 (bslot kk)); [reflexivity|]. exists r1. split; [exact (SUB _ _ Hr1)| exact Hr1].
Qed.

