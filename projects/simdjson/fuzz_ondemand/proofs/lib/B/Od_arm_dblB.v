(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Od_defsB Od_arm_dbl_defsB Od_arm_dbl_exitB Od_arm_dbl_cfcB Od_arm_dbl_expB Od_arm_dbl_ftailB Od_arm_dbl_intB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition dbl_fhead_stmt (E : oaenv) : Prop :=
  forall (Q : machine_state -> Prop) st,
    HLASTP E -> od_head_ok (o_bs E) (o_idxs E) 1 st ->
    od_plus_k E Q st -> dbl_R_k E Q st -> dbl_F_k E Q st.

Theorem arm_dbl_evt_of_fhead : forall E, od_oka E -> dbl_fhead_stmt E -> arm_dbl_evt E.
Proof.
  intros E OK HFH. unfold arm_dbl_evt. intros Q st HLAST HH HK HS.
  pose proof (dbl_cf E OK Q st HLAST HH HK HS) as HT.
  pose proof (dbl_exp E OK Q st HLAST HH HK HT) as HE.
  pose proof (dbl_frac_tail E OK Q st HLAST HH HK HE) as HR.
  pose proof (HFH Q st HLAST HH HK HR) as HF.
  exact (od_dbl_int E OK Q st HLAST HH HK HF HE).
Qed.
