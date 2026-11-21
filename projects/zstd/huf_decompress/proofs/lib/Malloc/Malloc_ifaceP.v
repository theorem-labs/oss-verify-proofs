(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (1 recorded proof replaced by written proofs (rw_cells_app)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep MallocTree MallocFacts_A MallocKit_A Malloc_iface MallocKit_AB InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp F_malloc_top F_malloc_big.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require MallocFacts_inv2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Malloc_ifaceP () := "C47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C47Corelib4Init5Logic3iffC59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms?eq_proper_proxyC59OSSVerify5KrLib3Lib5Cells<cells_wf_appC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC59OSSVerify5KrLib3Lib3Mem<bytes_at_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5CellsBcells_bytes_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init9Datatypes6option02K47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2eq00C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphK47Corelib7Numbers7BinNums8positive01C46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega=RingMicromega7Formula01C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC47Corelib4Init5Logic8eq_ind_rC46Stdlib6ZArith:ZArith_dec8Z_lt_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib3Lib5Cells>cells_size_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells?cells_bytes_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula03C47Corelib7Classes?RelationClasses>iff_TransitiveI47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=iff_ReflexiveC46Stdlib9micromega8ZifyInst7Inj_Z_ZI46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic5False00".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] WR].
    pose proof (cells_bytes_length cs1 W1) as L1. rewrite L1 in B2.
    destruct WR as (HA & HN & HW).
    split; [split; [split; assumption|] | split; [split; assumption|]].
    + split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i)%Z with (A + (Z.of_nat (cells_size cs1) + i))%Z by lia. apply HW. lia.
  - intros [[[W1 B1] (HA1 & HN1 & HW1)] [[W2 B2] (HA2 & HN2 & HW2)]].
    pose proof (cells_bytes_length cs1 W1) as L1.
    split; [split; [split; assumption|] |].
    + split; [exact B1|]. rewrite L1. exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi. destruct (Z_lt_dec i (Z.of_nat (cells_size cs1))).
      * apply HW1. lia.
      * replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply HW2. lia.
Qed.

End CANSEC1.
