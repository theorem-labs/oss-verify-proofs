(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto AMalloc_iface AMalloc_iface2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Actr Op.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Lemma count_inj : forall {A B} (R : A -> B -> Prop) (la : list A) (lb : list B),
  List.NoDup la -> (forall a, In a la -> exists b, In b lb /\ R a b) -> (forall a a' b, R a b -> R a' b -> a = a') ->
  (length la <= length lb)%nat.
Proof.
  intros A B R la. induction la as [|a la IH]; intros lb ND EX INJ; [cbn; lia|].
  apply List.NoDup_cons_iff in ND as [NI ND]. destruct (EX a (or_introl eq_refl)) as (b & Hb & Rab).
  apply in_split in Hb as (l1 & l2 & ->). rewrite length_app. cbn [length].
  assert (X : (length la <= length (l1 ++ l2))%nat).
  { apply IH; [exact ND| | exact INJ]. intros a' Ha'. destruct (EX a' (or_intror Ha')) as (b' & Hb' & Rab').
    exists b'. split; [| exact Rab']. apply in_app_or in Hb' as [H|[<-|H]]; [apply in_or_app; left; exact H| | apply in_or_app; right; exact H].
    exfalso. apply NI. rewrite (INJ a a' b Rab Rab'). exact Ha'. }
  rewrite length_app in X. lia.
Qed.

Definition c24b (b : ablock) : bool :=
  match ab_kind b with ABHeap _ => (5881 <=? ab_size b) && (ab_size b <=? 7936) | ABFake _ => false end.
Definition c24count (LBa : list ablock) : Z := Z.of_nat (length (List.filter c24b LBa)).

Section C24.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Hypothesis AI_fake : AI_fake_law AI.

Lemma c24count_le_windows : forall W aw LB m mo ws,
  aw_holds_w AI ACCT UNIV W aw LB m mo -> ties W ws -> c24count (w_LBa W) <= Z.of_nat (length ws).
Proof.
  intros W aw LB m mo ws HW (_ & _ & _ & _ & _ & _ & _ & _ & C24 & _). pose proof HW as (AH & _ & _ & HFA & _).
  unfold c24count. apply Nat2Z.inj_le.
  apply (count_inj (fun b w => heap_kind w /\ 0 < w_len w /\ in_iv (user_iv b) (w_lo w) /\ is_heap b /\ In b (w_LBa W))).
  - apply List.NoDup_filter. exact (AI_blocks_nodup AI _ _ _ _ _ AH).
  - intros b Hb. apply filter_In in Hb as [Hb Cb]. unfold c24b in Cb. destruct (ab_kind b) as [p|c] eqn:K; [| discriminate].
    apply andb_prop in Cb as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
    assert (HH : is_heap b) by (exists p; exact K).
    assert (Vb : vis W b). { split; [exact Hb|]. intros F. destruct (HFA b F) as [_ FK]. exact (heap_not_fake b HH FK). }
    destruct (C24 b Vb HH ltac:(unfold c24, C24_LO, C24_HI; lia)) as (w & Hw & HK & HL & HI). exists w. repeat (split; [assumption|]). exact Hb.
  - intros b b' w (_ & _ & I1 & H1 & L1) (_ & _ & I2 & H2 & L2).
    destruct (ablock_eq_dec b b') as [E|NE]; [exact E| exfalso].
    unfold in_iv, user_iv in I1, I2. cbn [fst snd] in I1, I2. rewrite (usz_heap b H1) in I1. rewrite (usz_heap b' H2) in I2.
    destruct (AI_blocks_disjoint AI _ _ _ _ _ b b' AH L1 L2 NE); lia.
Qed.
End C24.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl.
Import AProto.TwinB AMalloc_iface.TwinB AMalloc_iface2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import Ledger.TwinB Actr.TwinB Op.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Lemma count_inj : forall {A B} (R : A -> B -> Prop) (la : list A) (lb : list B),
  List.NoDup la -> (forall a, In a la -> exists b, In b lb /\ R a b) -> (forall a a' b, R a b -> R a' b -> a = a') ->
  (length la <= length lb)%nat.
Proof.
  intros A B R la. induction la as [|a la IH]; intros lb ND EX INJ; [cbn; lia|].
  apply List.NoDup_cons_iff in ND as [NI ND]. destruct (EX a (or_introl eq_refl)) as (b & Hb & Rab).
  apply in_split in Hb as (l1 & l2 & ->). rewrite length_app. cbn [length].
  assert (X : (length la <= length (l1 ++ l2))%nat).
  { apply IH; [exact ND| | exact INJ]. intros a' Ha'. destruct (EX a' (or_intror Ha')) as (b' & Hb' & Rab').
    exists b'. split; [| exact Rab']. apply in_app_or in Hb' as [H|[<-|H]]; [apply in_or_app; left; exact H| | apply in_or_app; right; exact H].
    exfalso. apply NI. rewrite (INJ a a' b Rab Rab'). exact Ha'. }
  rewrite length_app in X. lia.
Qed.

Definition c24b (b : ablock) : bool :=
  match ab_kind b with ABHeap _ => (5881 <=? ab_size b) && (ab_size b <=? 7936) | ABFake _ => false end.
Definition c24count (LBa : list ablock) : Z := Z.of_nat (length (List.filter c24b LBa)).

Section C24.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Hypothesis AI_fake : AI_fake_law AI.

Lemma c24count_le_windows : forall W aw LB m mo ws,
  aw_holds_w AI ACCT UNIV W aw LB m mo -> ties W ws -> c24count (w_LBa W) <= Z.of_nat (length ws).
Proof.
  intros W aw LB m mo ws HW (_ & _ & _ & _ & _ & _ & _ & _ & C24 & _). pose proof HW as (AH & _ & _ & HFA & _).
  unfold c24count. apply Nat2Z.inj_le.
  apply (count_inj (fun b w => heap_kind w /\ 0 < w_len w /\ in_iv (user_iv b) (w_lo w) /\ is_heap b /\ In b (w_LBa W))).
  - apply List.NoDup_filter. exact (AI_blocks_nodup AI _ _ _ _ _ AH).
  - intros b Hb. apply filter_In in Hb as [Hb Cb]. unfold c24b in Cb. destruct (ab_kind b) as [p|c] eqn:K; [| discriminate].
    apply andb_prop in Cb as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
    assert (HH : is_heap b) by (exists p; exact K).
    assert (Vb : vis W b). { split; [exact Hb|]. intros F. destruct (HFA b F) as [_ FK]. exact (heap_not_fake b HH FK). }
    destruct (C24 b Vb HH ltac:(unfold c24, C24_LO, C24_HI; lia)) as (w & Hw & HK & HL & HI). exists w. repeat (split; [assumption|]). exact Hb.
  - intros b b' w (_ & _ & I1 & H1 & L1) (_ & _ & I2 & H2 & L2).
    destruct (ablock_eq_dec b b') as [E|NE]; [exact E| exfalso].
    unfold in_iv, user_iv in I1, I2. cbn [fst snd] in I1, I2. rewrite (usz_heap b H1) in I1. rewrite (usz_heap b' H2) in I2.
    destruct (AI_blocks_disjoint AI _ _ _ _ _ b b' AH L1 L2 NE); lia.
Qed.
End C24.
End TwinB.
