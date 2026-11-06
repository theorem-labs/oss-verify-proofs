(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Import Od_fromch Od_arm_dbl_defs Od_arm_dbl_exit Od_arm_dbl_cf Od_arm_dbl_exp Od_arm_dbl_ftail
  Od_arm_dbl_fhead Od_arm_dbl_int.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem od_arm_dbl : forall E, od_ok E -> od_oku E -> fromchu_stmt_g usegs OD_FROMCH OD_GTOP -> arm_stmt E 0x279b0.
Proof.
  intros E OK OKU HFROMCH. unfold arm_stmt.
  intros Q st xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 xF xfc m1 HLAST HH FRM INV HK.
  pose proof (dbl_cf E OK OKU HFROMCH Q st HLAST HH HK) as HT.
  pose proof (dbl_exp E OK OKU Q st HLAST HH HK HT) as HE.
  pose proof (dbl_frac_tail E OK OKU Q st HLAST HH HK HE) as HR.
  pose proof (dbl_fhead E OK OKU Q st HLAST HH HK HR) as HF.
  exact (od_dbl_int E OK OKU Q st xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 xF xfc m1 HLAST HH FRM INV HK HF HE).
Qed.
