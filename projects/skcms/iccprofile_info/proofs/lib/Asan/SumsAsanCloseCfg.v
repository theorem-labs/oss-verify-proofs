(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import PropExec StoreOk Hoare AgentLib.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanPopFree AsanPlanSoundSums SumsAsanSpecs AsanIStrncpy AsanPopFreeAsan AsanPlanImages SumsAsanClose.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import SpinAlgCfg AsanPlanSoundCfg AsanPlanSoundSumsCfg.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache.
Open Scope Z_scope.

Section AsanNodesCfg.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> AP.CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis NX0_sp : APS.nx0_sp_ok nx0.
Variable FS0 : Fs.Fs.
Variable FPS : PropExec.FPState -> Prop.

#[local] Notation XSTMTC := (APSC.x_stmt_cfg ASEGS INFO_ASAN nx0 LIMIT SINV argH FS0 FPS).

#[local] Ltac img := first [ exact asan_wx | exact asan_in_hull | exact asan_res_len | exact asan_hull_ok | exact asan_segs_wr ].

Theorem asan_node_x_cfg_XIMemset : XSTMTC AP.XIMemset.
Proof. eapply APSXC.node_x_cfg_OBL_XIMemset; try eassumption; try img. intros FP _. exact asan_fill_spec_imemset. Qed.
Theorem asan_node_x_cfg_XMemset : XSTMTC AP.XMemset.
Proof. eapply APSXC.node_x_cfg_OBL_XMemset; try eassumption; try img. intros FP _. exact asan_fill_spec_memset. Qed.
Theorem asan_node_x_cfg_XIMemcpy : XSTMTC AP.XIMemcpy.
Proof. eapply APSXC.node_x_cfg_OBL_XIMemcpy; try eassumption; try img. intros FP _. exact asan_copy_spec_imemcpy. Qed.
Theorem asan_node_x_cfg_XMemcpy : XSTMTC AP.XMemcpy.
Proof. eapply APSXC.node_x_cfg_OBL_XMemcpy; try eassumption; try img. intros FP _. exact asan_copy_spec_memcpy. Qed.
Theorem asan_node_x_cfg_XMemIsZero : XSTMTC AP.XMemIsZero.
Proof. eapply APSXC.node_x_cfg_OBL_XMemIsZero; try eassumption; try img. intros FP _. exact asan_miz_spec. Qed.
Theorem asan_node_x_cfg_XIStrncpy : XSTMTC AP.XIStrncpy.
Proof. eapply APSXC.node_x_cfg_OBL_XIStrncpy; try eassumption; try img. intros FP _. exact asan_istrncpy_spec. Qed.
Theorem asan_node_x_cfg_XPopFree : XSTMTC AP.XPopFree.
Proof. eapply APSXC.node_x_cfg_OBL_XPopFree; try eassumption; try img. intros FP _. exact asan_popfree_spec'. Qed.
End AsanNodesCfg.
