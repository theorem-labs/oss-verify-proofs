(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare SpinAlg AgentLib AsanAcct.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanNodesLC AsanNodesLCTab AsanNodesLCSoundG AsanTplLib BothPlanImages SumsBothSpecs ItabBoth.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Import AX2 AX2S AP APS APSX.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition TP_BOTH : list TPL.tplp := [TPL.TP 2628 [912]; TPL.TP 2634 [912]; TPL.TP 2628 [912]].

Lemma both_lc_wf : forallb lc_wf LC_BOTH = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma both_lc_chk :
  forallb (fun PT : TPL.tplp * LCN.lctab => TPL.tpl_check BSEGS IT_both (shadow_off BOTH) (fst PT) (snd PT)) (combine TP_BOTH LC_BOTH) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma both_lc_specs : Forall (fun T => lc_wf T = true /\ lc_spec BSEGS (shadow_off BOTH) T) LC_BOTH.
Proof.
  apply (tpl_all_sound BSEGS IT_both (shadow_off BOTH) IT_both_ok ltac:(vm_compute; split; [discriminate | reflexivity]) TP_BOTH LC_BOTH
           eq_refl both_lc_wf both_lc_chk).
Qed.

Section BothNode.
Variable nx0 : N.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis nx0_ge7 : APS.nx0_ok nx0.
Variable FS0 : Fs.Fs.

Theorem both_lc_ext_sound : ext_stmt BSEGS BOTH nx0 LIMIT (LCN.xn BSEGS BOTH nx0 LC_BOTH) SINV argH FS0.
Proof.
  eapply (lc_xn_sound BSEGS BOTH nx0 LIMIT); try eassumption;
    first [ exact both_wx | exact both_in_hull | exact both_hull_ok | exact both_segs_wr | exact both_shadow_ok | exact both_lc_specs | idtac ].
Qed.
End BothNode.
