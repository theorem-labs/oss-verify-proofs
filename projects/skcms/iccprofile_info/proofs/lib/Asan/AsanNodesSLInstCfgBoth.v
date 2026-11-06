(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.skcms.iccprofile_info.images Require Import AsanUbsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import SpinAlgCfg AsanAcctShapeCfg AsanPlanSoundCfg AsanPlanSoundSumsCfg.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanNodesSL AsanNodesSLSoundCfg BothAsanBySizeLogSpec BothAsanSizeLog BothAsanBySizeLog BothAsanPlanImages.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Import AX2 AX2S AP APS APSX APSXC.
Unset Lia Cache.
Open Scope Z_scope.
Section WithFP1. Context {FP : PropExec.FPState}.
Section AsanNode.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis NX0_sp : nx0_sp_ok nx0.   (* [comment removed for export] *)
Variable FS0 : Fs.Fs.

Lemma sltab_of_ASAN : SLN.sltab_of INFO_BOTH = SLN.SL_BOTH.
Proof. reflexivity. Qed.

Theorem asan_sl_ext_sound : forall id args, APSC.node1_stmt_fp ASEGS INFO_BOTH nx0 LIMIT SINV argH FS0 FP always (SLN.xn ASEGS nx0 (SLN.sltab_of INFO_BOTH) id args).
Proof.
  rewrite sltab_of_ASAN.
  exact (sl_xn_sound ASEGS INFO_BOTH nx0 LIMIT asan_wx asan_in_hull asan_hull_ok SINV argH argH_high argH_agree SINV_frame SINV_agree NX0_sp FS0
           SLN.SL_BOTH asan_sizelog asan_bysizelog).
Qed.
End AsanNode.
End WithFP1.

