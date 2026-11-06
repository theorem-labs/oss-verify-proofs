(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Od_fromch Od_arm_dbl_defs Od_arm_dbl Od_arm_dbl_cf Od_arm_dbl_ftail.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem od_arm_dbl_top : forall E, od_ok E -> fromch_stmt_g psegs OD_FROMCH OD_GTOP -> dbl_frac_stmt E -> arm_stmt E 0x277e0.
Proof.
  intros E OK HFROMCH HFRAC. apply (od_arm_dbl E OK HFRAC). exact (dbl_cf E OK HFROMCH).
Qed.

Theorem dbl_frac_of_head : forall E, od_ok E -> dbl_fhead_stmt E -> dbl_frac_stmt E.
Proof.
  intros E OK HH. unfold dbl_frac_stmt. intros Q st HLAST HHO HK HE.
  apply (HH Q st HLAST HHO HK). exact (dbl_frac_tail E OK Q st HLAST HHO HK HE).
Qed.

Theorem od_arm_dbl_top2 : forall E, od_ok E -> fromch_stmt_g psegs OD_FROMCH OD_GTOP -> dbl_fhead_stmt E -> arm_stmt E 0x277e0.
Proof.
  intros E OK HFROMCH HH. apply (od_arm_dbl_top E OK HFROMCH). exact (dbl_frac_of_head E OK HH).
Qed.
