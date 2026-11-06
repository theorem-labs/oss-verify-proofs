(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require em.

(* [comment removed for export] *)
Module FpsC_a3.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nat"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st"; "T7s"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail"; "FPA"; "FQA"; "PRE_C"; "SUF_NL"; "T8"; "tailA_n"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st"; "factsS"; "@Stdlib.Lists.List"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "add"; "of_nat"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require em.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.
Import ListNotations.
Open Scope Z_scope.

Lemma okA_3 : ltac2:(tb__ "0|0|
S7S2S11S0S0SfSaR1S6A2S0SbR2R1S6A3Lr;ScSdR1S12Z12R1A2S0SeZ11R2R1S10S6A5Lr;S1S0Z0S1S0Z1S1S0Z2S1S0Z3S4S0A1A3A3A3A3A8Ln;S8S3S0S13S9U18U8A2A4A3S5A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End FpsC_a3.

(* [comment removed for export] *)
Module FpsC_a5.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nat"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st"; "T7s"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail"; "FPA"; "FQA"; "PRE_C"; "SUF_NL"; "T8"; "tailA_n"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st"; "factsS"; "@Stdlib.Lists.List"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "add"; "of_nat"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require em.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.
Import ListNotations.
Open Scope Z_scope.

Lemma okA_5 : ltac2:(tb__ "0|0|
S7S2S11S0S0SfSaR1S6A2S0SbR2R1S6A3Lr;ScSdR1S12Z12R1A2S0SeZ11R2R1S10S6A5Lr;S1S0Z0S1S0Z1S1S0Z2S1S0Z3S4S0A1A3A3A3A3A8Ln;S8S3S0S13S9U28U8A2A4A3S5A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End FpsC_a5.

(* [comment removed for export] *)
Module FpsU_a4.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st"; "T7b"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nat"; "nil"; "true"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail"; "FPA"; "FQA"; "PRE_U"; "SUF_U"; "T8"; "tailA_n"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st"; "factsB"; "@Stdlib.Lists.List"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "add"; "of_nat"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require em.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.
Import ListNotations.
Open Scope Z_scope.

Lemma okA_4 : ltac2:(tb__ "0|0|
S7S2S11S0S0SfSaR1S1A2S0SbR2R1S1A3Lr;ScSdR1S12ZeR1A2S0SeZ7R2R1S10S1A5Lr;S3S0Z0S5S0A1A3A8Ln;S8S4S0S13S9U40U1A2A4A3S6A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End FpsU_a4.

(* [comment removed for export] *)
Module FpsU_a0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st"; "T7s"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nat"; "nil"; "true"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail"; "FPA"; "FQA"; "PRE_U"; "SUF_U"; "T8"; "tailA_n"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st"; "factsS"; "@Stdlib.Lists.List"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "add"; "of_nat"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require em.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.
Import ListNotations.
Open Scope Z_scope.

Lemma okA_0 : ltac2:(tb__ "0|0|
S7S2S11S0S0SfSaR1S1A2S0SbR2R1S1A3Lr;ScSdR1S12ZeR1A2S0SeZ7R2R1S10S1A5Lr;S3S0Z0S5S0A1A3A8Ln;S8S4S0S13S9U0U10A2A4A3S6A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End FpsU_a0.

