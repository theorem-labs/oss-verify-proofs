(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare SpinAlg AgentLib AsanAcct.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanNodesLC AsanNodesLCTab AsanNodesLCSoundG AsanTplLib AsanPlanImages SumsAsanSpecs ItabAsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Import AX2 AX2S AP APS APSX.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition TP_ASAN : list TPL.tplp := [TPL.TP 2628 [912]; TPL.TP 2634 [912]; TPL.TP 2628 [912]].

Lemma asan_lc_wf : forallb lc_wf LC_ASAN = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma asan_lc_chk :
  forallb (fun PT : TPL.tplp * LCN.lctab => TPL.tpl_check ASEGS IT_asan (shadow_off ASAN) (fst PT) (snd PT)) (combine TP_ASAN LC_ASAN) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma asan_lc_specs : Forall (fun T => lc_wf T = true /\ lc_spec ASEGS (shadow_off ASAN) T) LC_ASAN.
Proof.
  apply (tpl_all_sound ASEGS IT_asan (shadow_off ASAN) IT_asan_ok ltac:(vm_compute; split; [discriminate | reflexivity]) TP_ASAN LC_ASAN
           eq_refl asan_lc_wf asan_lc_chk).
Qed.

Section AsanNode.
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

Theorem asan_lc_ext_sound : ext_stmt ASEGS ASAN nx0 LIMIT (LCN.xn ASEGS ASAN nx0 LC_ASAN) SINV argH FS0.
Proof.
  eapply (lc_xn_sound ASEGS ASAN nx0 LIMIT); try eassumption;
    first [ exact asan_wx | exact asan_in_hull | exact asan_hull_ok | exact asan_segs_wr | exact asan_shadow_ok | exact asan_lc_specs | idtac ].
Qed.
End AsanNode.
