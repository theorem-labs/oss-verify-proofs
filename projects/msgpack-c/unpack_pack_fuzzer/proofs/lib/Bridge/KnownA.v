(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr Mem State Step Plan ValProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require KnownT.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan CtrLib ActrA.
Open Scope Z_scope.
Unset Lia Cache.

Module KnownA.
Module KT := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.KnownT.KnownT.

Lemma known_ltu_sound : forall E fs a b, facts_hold E fs -> KT.known_ltu_t fs a b = true -> bv_unsigned (den E a) < bv_unsigned (den E b).
Proof. intros E fs a b HF H. exact (KT.known_ltu_t_sound E fs HF a b H). Qed.
Lemma known_leu_sound : forall E fs a b, facts_hold E fs -> KT.known_leu_t fs a b = true -> bv_unsigned (den E a) <= bv_unsigned (den E b).
Proof. intros E fs a b HF H. exact (KT.known_leu_t_sound E fs HF a b H). Qed.
Lemma known_eq_sound : forall E fs a b, facts_hold E fs -> KT.known_eq_t fs a b = true -> den E a = den E b.
Proof. intros E fs a b HF H. exact (KT.known_eq_t_sound E fs HF a b H). Qed.

Lemma known_leu_q_sound : forall E fs a b, facts_hold E fs -> known_leu_qt fs a b = true -> bv_unsigned (den E a) <= bv_unsigned (den E b).
Proof.
  intros E fs a b Hfs H. unfold known_leu_qt in H.
  destruct (sv_eqb a b) eqn:Q; [apply ValP.sv_eqb_eq in Q; subst; lia|].
  destruct (fact_lookup fs (is_FULe a b)) eqn:L1.
  { destruct (ValP.fact_lookup_holds E fs _ Hfs L1) as (f & HF & PF). destruct f; try discriminate PF. cbn [is_FULe] in PF.
    apply andb_prop in PF as [P1 P2]. apply ValP.sv_eqb_eq in P1, P2. subst. cbn [fact_holds] in HF. exact HF. }
  destruct (fact_lookup fs (is_FULt a b)) eqn:L2.
  { destruct (ValP.fact_lookup_holds E fs _ Hfs L2) as (f & HF & PF). destruct f; try discriminate PF. cbn [is_FULt] in PF.
    apply andb_prop in PF as [P1 P2]. apply ValP.sv_eqb_eq in P1, P2. subst. cbn [fact_holds] in HF. lia. }
  exact (known_leu_sound E fs a b Hfs H).
Qed.

Lemma stack_side_sound : forall E fs sp k, facts_hold E fs ->
  stack_side_t fs sp (sp_below_anchor_t fs sp) k = true -> bv_unsigned (den E sp) <= bv_unsigned (ev E k).
Proof.
  intros E fs sp k Hfs H. unfold stack_side_t, sp_below_anchor_t in H.
  destruct (KT.known_leu_t fs sp (VP STACK_ID wzero)) eqn:A.
  - destruct (CtrA.anchored_above fs k) eqn:AA.
    { apply (known_leu_sound E _ _ _ Hfs) in A. rewrite (HeapCtr.den_VPz E STACK_ID) in A. pose proof (HeapCtr.anchored_above_sound E fs k Hfs AA) as AB.
      change CtrA.STACK_ID with STACK_ID in AB. lia. }
    destruct (KT.known_leu_t fs (VP STACK_ID wzero) (VP k wzero)) eqn:B.
    + apply (known_leu_sound E _ _ _ Hfs) in A. apply (known_leu_sound E _ _ _ Hfs) in B. rewrite (HeapCtr.den_VPz E STACK_ID) in A, B. rewrite (HeapCtr.den_VPz E k) in B. lia.
    + apply (known_leu_sound E _ _ _ Hfs) in H. rewrite HeapCtr.den_VPz in H. exact H.
  - apply (known_leu_sound E _ _ _ Hfs) in H. rewrite HeapCtr.den_VPz in H. exact H.
Qed.
End KnownA.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Actr.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan CtrLib ActrA.
Open Scope Z_scope.
Unset Lia Cache.

Module KnownA.
Module KT := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.KnownT.KnownT.

Lemma known_ltu_sound : forall E fs a b, facts_hold E fs -> KT.known_ltu_t fs a b = true -> bv_unsigned (den E a) < bv_unsigned (den E b).
Proof. intros E fs a b HF H. exact (KT.known_ltu_t_sound E fs HF a b H). Qed.
Lemma known_leu_sound : forall E fs a b, facts_hold E fs -> KT.known_leu_t fs a b = true -> bv_unsigned (den E a) <= bv_unsigned (den E b).
Proof. intros E fs a b HF H. exact (KT.known_leu_t_sound E fs HF a b H). Qed.
Lemma known_eq_sound : forall E fs a b, facts_hold E fs -> KT.known_eq_t fs a b = true -> den E a = den E b.
Proof. intros E fs a b HF H. exact (KT.known_eq_t_sound E fs HF a b H). Qed.

Lemma known_leu_q_sound : forall E fs a b, facts_hold E fs -> known_leu_qt fs a b = true -> bv_unsigned (den E a) <= bv_unsigned (den E b).
Proof.
  intros E fs a b Hfs H. unfold known_leu_qt in H.
  destruct (sv_eqb a b) eqn:Q; [apply ValP.sv_eqb_eq in Q; subst; lia|].
  destruct (fact_lookup fs (is_FULe a b)) eqn:L1.
  { destruct (ValP.fact_lookup_holds E fs _ Hfs L1) as (f & HF & PF). destruct f; try discriminate PF. cbn [is_FULe] in PF.
    apply andb_prop in PF as [P1 P2]. apply ValP.sv_eqb_eq in P1, P2. subst. cbn [fact_holds] in HF. exact HF. }
  destruct (fact_lookup fs (is_FULt a b)) eqn:L2.
  { destruct (ValP.fact_lookup_holds E fs _ Hfs L2) as (f & HF & PF). destruct f; try discriminate PF. cbn [is_FULt] in PF.
    apply andb_prop in PF as [P1 P2]. apply ValP.sv_eqb_eq in P1, P2. subst. cbn [fact_holds] in HF. lia. }
  exact (known_leu_sound E fs a b Hfs H).
Qed.

Lemma stack_side_sound : forall E fs sp k, facts_hold E fs ->
  stack_side_t fs sp (sp_below_anchor_t fs sp) k = true -> bv_unsigned (den E sp) <= bv_unsigned (ev E k).
Proof.
  intros E fs sp k Hfs H. unfold stack_side_t, sp_below_anchor_t in H.
  destruct (KT.known_leu_t fs sp (VP STACK_ID wzero)) eqn:A.
  - destruct (CtrA.anchored_above fs k) eqn:AA.
    { apply (known_leu_sound E _ _ _ Hfs) in A. rewrite (HeapCtr.TwinB.den_VPz E STACK_ID) in A. pose proof (HeapCtr.TwinB.anchored_above_sound E fs k Hfs AA) as AB.
      change CtrA.STACK_ID with STACK_ID in AB. lia. }
    destruct (KT.known_leu_t fs (VP STACK_ID wzero) (VP k wzero)) eqn:B.
    + apply (known_leu_sound E _ _ _ Hfs) in A. apply (known_leu_sound E _ _ _ Hfs) in B. rewrite (HeapCtr.TwinB.den_VPz E STACK_ID) in A, B. rewrite (HeapCtr.TwinB.den_VPz E k) in B. lia.
    + apply (known_leu_sound E _ _ _ Hfs) in H. rewrite HeapCtr.TwinB.den_VPz in H. exact H.
  - apply (known_leu_sound E _ _ _ Hfs) in H. rewrite HeapCtr.TwinB.den_VPz in H. exact H.
Qed.
End KnownA.
End TwinB.
