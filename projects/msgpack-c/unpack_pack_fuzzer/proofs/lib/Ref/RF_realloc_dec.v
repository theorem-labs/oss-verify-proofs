(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_F_malloc_free A_F_malloc_fast A_MallocKit_AB A_MallocBlocks A_MallocHINV A_MallocFacts_B A_Malloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import STree Malloc MallocCtrl MallocInv MI_Inv MI_Read MI_Geom MI_Pres2 MI_WFree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad Prog.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import RMallocRep RMallocTree RMallocKit_B RMalloc_iface RMalloc_ifaceP RF_get_meta RF_malloc_top RMemEq.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require A_MallocFacts_inv A_MallocFacts_inv2.

Set Keyed Unification.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Section DEC.
Variables (ra1 sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (P n old G B stride E : Z) (i sc : Z) (mword : Z) (Q : machine_state -> Prop).
Hypotheses (HN : 0 <= n < 2^48) (HO : 0 <= old) (PE : P + old <= E) (EHI : E + 4 < 2^64) (P0 : 0 < P) (SC : 0 <= sc < 64) (Hsc63 : 48 <= sc -> sc = 63).

Definition dstate (pc : Z) (y7 a5v y28 y29 : word) : machine_state :=
  MS (mkR ra1 sp gp tp (Z_to_bv 64 E) (Z_to_bv 64 (B + stride * i + 16)) y7 s0 (wz G) (Z_to_bv 64 P) (Z_to_bv 64 n)
          (wz B) (Z_to_bv 64 sc) (wz mword) a5v (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - P))
          (Z_to_bv 64 (P + old)) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).

Definition move_cond : Prop :=
  ~ (n <= E - P /\ n < MMAP_THRESHOLD /\ sc <= size_to_class n + 1) /\ ~ (MMAP_THRESHOLD <= n /\ 48 <= sc).

Lemma dec_5b4 : forall (y7 y28 y29 : word),

  (forall y7' a5' y28', move_cond -> evt rsegs Q (dstate 0x49d98 y7' a5' y28' y29)) ->

  (forall y7' a5' y28', MMAP_THRESHOLD <= n -> sc = 63 -> evt rsegs Q (dstate 0x49cb0 y7' a5' y28' y29)) ->

  (forall y7' y28', n < MMAP_THRESHOLD -> n <= E - P -> evt rsegs Q (dstate 0x49c04 y7' (Z_to_bv 64 87200) y28' y29)) ->
  evt rsegs Q (dstate 0x49bf4 y7 (Z_to_bv 64 87200) y28 y29).
Proof.
  intros y7 y28 y29 KMOVE KREMAP KSTC. unfold dstate.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.

  assert (K654 : forall y28', (MMAP_THRESHOLD <= n \/ E - P < n) ->
    evt rsegs Q (MS (mkR ra1 sp gp tp (Z_to_bv 64 E) (Z_to_bv 64 (B + stride * i + 16)) (Z_to_bv 64 131072) s0 (wz G) (Z_to_bv 64 P) (Z_to_bv 64 n)
                        (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 87200) (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - P))
                        (Z_to_bv 64 (P + old)) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28' y29 t5 t6)
                   F (Z_to_bv 64 0x49c94) fc None m (seg_rom rsegs))).
  { intros y28' HD.
    st1. st1. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
    { apply KMOVE. unfold move_cond; unfold MMAP_THRESHOLD in *; lia. }
    st1. st1. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
    { apply KMOVE. unfold move_cond; unfold MMAP_THRESHOLD in *; lia. }
    st1. st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
    { apply KREMAP; unfold MMAP_THRESHOLD; lia. }
    exfalso. lia. }
  st1. st1. st1. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.
  - apply K654. unfold MMAP_THRESHOLD; lia.
  -
    st1. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia.
    + apply K654. lia.
    + apply KSTC; unfold MMAP_THRESHOLD; lia.
Qed.
End DEC.

End CEIL.

From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Image OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Decode.
Import OSSVerify.msgpack_c.unpack_pack_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_free OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_fast OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocKit_AB OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocBlocks OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocHINV OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocFacts_B OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_Malloc_iface.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Malloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocInv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Inv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Read OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Geom OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Pres2 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_WFree.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Monad OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Prog.
Import RMallocRep.TwinB RMallocTree.TwinB RMallocKit_B.TwinB RMalloc_iface.TwinB RMalloc_ifaceP.TwinB RF_get_meta.TwinB RF_malloc_top.TwinB RMemEq.TwinB.

Set Keyed Unification.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Section DEC.
Variables (ra1 sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (P n old G B stride E : Z) (i sc : Z) (mword : Z) (Q : machine_state -> Prop).
Hypotheses (HN : 0 <= n < 2^48) (HO : 0 <= old) (PE : P + old <= E) (EHI : E + 4 < 2^64) (P0 : 0 < P) (SC : 0 <= sc < 64) (Hsc63 : 48 <= sc -> sc = 63).

Definition dstate (pc : Z) (y7 a5v y28 y29 : word) : machine_state :=
  MS (mkR ra1 sp gp tp (Z_to_bv 64 E) (Z_to_bv 64 (B + stride * i + 16)) y7 s0 (wz G) (Z_to_bv 64 P) (Z_to_bv 64 n)
          (wz B) (Z_to_bv 64 sc) (wz mword) a5v (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - P))
          (Z_to_bv 64 (P + old)) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).

Definition move_cond : Prop :=
  ~ (n <= E - P /\ n < MMAP_THRESHOLD /\ sc <= size_to_class n + 1) /\ ~ (MMAP_THRESHOLD <= n /\ 48 <= sc).

Lemma dec_5b4 : forall (y7 y28 y29 : word),

  (forall y7' a5' y28', move_cond -> evt rsegs Q (dstate 0x4b59c y7' a5' y28' y29)) ->

  (forall y7' a5' y28', MMAP_THRESHOLD <= n -> sc = 63 -> evt rsegs Q (dstate 0x4b4b4 y7' a5' y28' y29)) ->

  (forall y7' y28', n < MMAP_THRESHOLD -> n <= E - P -> evt rsegs Q (dstate 0x4b408 y7' (Z_to_bv 64 87344) y28' y29)) ->
  evt rsegs Q (dstate 0x4b3f8 y7 (Z_to_bv 64 87344) y28 y29).
Proof.
  intros y7 y28 y29 KMOVE KREMAP KSTC. unfold dstate.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.

  assert (K654 : forall y28', (MMAP_THRESHOLD <= n \/ E - P < n) ->
    evt rsegs Q (MS (mkR ra1 sp gp tp (Z_to_bv 64 E) (Z_to_bv 64 (B + stride * i + 16)) (Z_to_bv 64 131072) s0 (wz G) (Z_to_bv 64 P) (Z_to_bv 64 n)
                        (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 87344) (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - P))
                        (Z_to_bv 64 (P + old)) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28' y29 t5 t6)
                   F (Z_to_bv 64 0x4b498) fc None m (seg_rom rsegs))).
  { intros y28' HD.
    st1. st1. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
    { apply KMOVE. unfold move_cond; unfold MMAP_THRESHOLD in *; lia. }
    st1. st1. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
    { apply KMOVE. unfold move_cond; unfold MMAP_THRESHOLD in *; lia. }
    st1. st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
    { apply KREMAP; unfold MMAP_THRESHOLD; lia. }
    exfalso. lia. }
  st1. st1. st1. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.
  - apply K654. unfold MMAP_THRESHOLD; lia.
  -
    st1. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia.
    + apply K654. lia.
    + apply KSTC; unfold MMAP_THRESHOLD; lia.
Qed.
End DEC.

End CEIL.
End TwinB.
