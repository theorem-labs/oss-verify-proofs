(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: changed as0_copy_spec_memcpy, as0_fill_spec_memset, as0_strlen_spec; taken in part from projects/jsoncons/fuzz_msgpack_encoder/proofs/lib/Mh_0140.v at theorem-labs/oss-verify-proofs@f92feaf8b7e6, lines 34-40, 45, 68-74. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.muslA.Mh_0068. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AsanPlanSound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module Na0Sums.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.RefMemcpyLib.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.MemsetLib.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.muslA.Mh_0068.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AsanPlanSound. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AsanPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSound.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.AsanPlanSoundSums OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SumsSpecLib.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_Na0Sums () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6to_natI47Corelib4Init5Logic2eq00C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib7Mh_00385Hoare6ret_okC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK69OSSVerify5KrLib5muslA7Mh_0068=Na0MemcpyBase3mcH01C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib5muslA7Mh_0068=Na0MemcpyBase3mcH00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib5muslA7Mh_00689Na0Memcpy:ref_memcpyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0056<RefMemcpyLib5keepsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX7kept_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib7Mh_0137;SumsSpecLib@kept_ok_of_keepsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C46Stdlib5Lists4List2InK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX9copy_specC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib4Init5Logic4True01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic5False00C59OSSVerify5KrLib7Mh_0056<RefMemcpyLib;callee_keptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib5muslA7Mh_0068=Na0SumsMemset>memset_summaryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0137;SumsSpecLibCfill_spec_of_memsetC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma as0_copy_spec_memcpy : forall fx : PropExec.FPState, @APSX.copy_spec fx RSEGS 0x148d68.
Proof.
  intros fx mem0 dst src n bs regs ret Hn Hlen Hrd Hst Hdisj Hnws Hnwd Hret R1 R10 R11 R12.
  pose proof (u64_range dst) as Hdr.
  assert (HOK : OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.muslA.Mh_0068.Na0MemcpyBase.mcH mem0 dst src n bs) by (constructor; try assumption; lia).
  destruct (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.muslA.Mh_0068.Na0Memcpy.ref_memcpy mem0 dst src n bs (seg_rom RSEGS) HOK regs ret Hret R1 R10 R11 R12) as (regs' & Hms & Hk).
  exists regs'. split; [replace (Z_to_bv 64 0x148d68) with (0x148d68%bv : word) by (apply bv_eq; reflexivity); exact Hms|].
  split; [apply kept_ok_of_keeps; exact Hk|].
  rewrite <- R10. apply Hk. unfold callee_kept. in_list.
Qed.

Lemma as0_fill_spec_memset : forall fx : PropExec.FPState, @APSX.fill_spec fx RSEGS 0x14916c AX2.two64.
Proof.
  intros fx. apply fill_spec_of_memset. intros mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1.
  exact (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.muslA.Mh_0068.Na0SumsMemset.memset_summary mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1).
Qed.

End Na0Sums.
From Stdlib Require ZArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
Module Na0SumsStrlen.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.RefMemcpyLib.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.muslA.Mh_0068. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.muslA.Mh_0068.Na0Memchr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.muslA.Mh_0068.Na0SegStrlen OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_Na0SumsStrlen () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init9Datatypes6lengthC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6to_natC45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3nthC47Corelib4Init5Peano2ltI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib7Mh_00385Hoare6ret_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib5muslA7Mh_0068<Na0SegStrlen5slenH01C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib5muslA7Mh_0068<Na0SegStrlen5slenH00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib5muslA7Mh_0068<Na0SegStrlen:ref_strlenC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib5muslA7Mh_0068<Na0SegStrlen8sl_agreeC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions5bv_eqK47Corelib4Init5Logic2eq01C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic3notK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C46Stdlib5Lists4List2InC69OSSVerify5KrLib5muslA7Mh_0068<Na0SegStrlen=sl_agree_getrC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib7Mh_01306SegRun2SR;strlen_specC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C47Corelib4Init5Logic9False_indK47Corelib4Init5Logic4True01C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1N00C69OSSVerify5KrLib5muslA7Mh_0068<Na0SegStrlen7sl_clobC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma as0_strlen_spec : SR.strlen_spec Asan.M.loaded_segments 0x103d0 0x103f0 0x149650.
Proof.
  intros fx mem s buf K rom regs ret Hbuf Hwin Hnw HK0 Hz Hnz Hro Hret H1 H10.
  assert (HOK : slenH mem s buf K) by (constructor; assumption).
  destruct (ref_strlen mem s buf K rom regs ret HOK Hret H1 H10) as (regs' & Hms & Hag & Ha0).
  exists regs'. split; [|split; [|exact Ha0]].
  - replace (Z_to_bv 64 0x149650) with (0x149650%bv : word) by (apply bv_eq; reflexivity). exact Hms.
  - intros r N10 N11 N12 N13 N14 N15 N16. apply (sl_agree_getr _ _ r Hag).
    unfold sl_clob. cbn [In]. intros [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; subst r; contradiction.
Qed.

End Na0SumsStrlen.
