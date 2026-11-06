(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA LibIface
     AsanAcct L5Defs L5DefsA L5CoreA L5CoreSpecsA L5DivLeafSpecsA L5DivSpecsA L5OpmodSpecsA L5DivInnerSpecsA L5UnwindSpecsA
     L5ACopyAS L5ADivN L5ADivO1 L5ADivO2 L5ADivQ L5AUnnorm L5AOpMod L5AOpModE3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module L5ADWIRE.
Import L5A. Import L5CA. Import L5CSA.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.
(* [comment removed for export] *)
Hypothesis Hcpa : copya_spec L ar HI.
Hypothesis Hssrc : L5ACPAS.copya_ssrc_spec L ar HI.
Hypothesis Hasg : assign_spec L ar HI.
Hypothesis Hdel : opdel_sized_spec L ar HI.
Hypothesis Hrz : resize_spec L ar HI.

(* [comment removed for export] *)
Theorem divN_of_gen : L5ADVN.gen_N L ar HI -> L5DIA.divN_specA L ar HI.
Proof. exact (L5ADVN.divN_ok L ar C HI LY HIok Hcpa Hssrc). Qed.
Theorem diveq_of_gen : L5ADVN.gen_N L ar HI -> L5DIA.diveq_specA L ar HI.
Proof. intros GN. exact (L5ADIVQ.diveq_okA L ar C HI LY HIok Hdel (divN_of_gen GN)). Qed.
Theorem unnorm_of_gen : L5ADVN.gen_N L ar HI -> L5DIA.unnorm_specA L ar HI.
Proof. intros GN. exact (L5AUNNORM.unnorm_okA L ar C HI LY HIok Hrz (diveq_of_gen GN)). Qed.

(* [comment removed for export] *)
Theorem divO1_of_gen : L5ADVO1.gen_O1 L ar HI -> L5DIA.divO1_specA L ar HI.
Proof. exact (L5ADVO1.divO1_ok L ar C HI LY HIok Hcpa Hasg Hdel Hrz). Qed.
Theorem divO2_of_gen : L5ADVO2.gen_O2 L ar HI -> L5DIA.divO2_specA L ar HI.
Proof. exact (L5ADVO2.divO2_ok L ar C HI LY HIok Hcpa Hasg Hdel). Qed.

(* [comment removed for export] *)
Theorem Hom1_of_gen :
  L5ADVO1.gen_O1 L ar HI -> L5USA.e2_chainA_spec L ar HI -> L5USA.e3_chainA_spec_of L ar HI (L5DIA.assert_throw_atA L ar) -> L5USA.as0_unw_layout L ->
  L5OMA.opmod1A_spec L ar HI L5USA.XS (L5USA.xs_pre ar) L5USA.xs_foot (L5USA.e2_landed L) (L5USA.e3_landed L) 73728 6 0 4 8 (fun c => 8 * c + 640).
Proof. intros GO1 He2 He3 UNWL. exact (L5AOME3.opmod1A_ok' L ar C HI LY HIok Hdel (divO1_of_gen GO1) He2 He3 UNWL). Qed.
Theorem Hom2_of_gen : L5ADVO2.gen_O2 L ar HI -> L5OMA.opmod2A_spec L ar HI 73728 6 0 4 8 (fun c => 24 * c + 640).
Proof. intros GO2. exact (L5AOPMOD.opmod2A_ok L ar C HI LY HIok Hdel (divO2_of_gen GO2)). Qed.

End WithIface.
End SCFG_1.
End L5ADWIRE.
