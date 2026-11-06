(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare SpinAlg AgentLib AsanAcct.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanNodesRP AsanNodesPG AsanNodesPGSoundG AsanNodesK1 AsanNodesK1SoundG AsanClzArith AsanClzWalk AsanPlanImages SumsAsanSpecs.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefReadLib Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefMemcpyLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Import AX2 AX2S AP APS APSX.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma asan_clz_spec : clz_spec ASEGS RPN.RP_ASAN.
Proof.
  intros mem rom x L v regs Hx HL Hrd H18 H9.
  destruct (clz_walk mem rom x L v Hx HL Hrd regs H18 H9) as (regs' & Hms & H19 & H14 & Hrest).
  exists regs'. split; [|split; [exact H19|split; [exact H14|exact Hrest]]].
  match type of Hms with msteps _ (mkst _ ?pp _ _) (mkst _ ?qq _ _) =>
    replace (Z_to_bv 64 (K1N.CLZ_ENTRY RPN.RP_ASAN)) with pp by (apply bv_eq; reflexivity);
    replace (Z_to_bv 64 (K1N.CLZ_EXIT RPN.RP_ASAN)) with qq by (apply bv_eq; reflexivity) end.
  exact Hms.
Qed.

(* [comment removed for export] *)
Lemma asan_bsl_spec : bsl_spec ASEGS RPN.RP_ASAN.
Proof.
  intros mem rom L idx a2w bs regs HL Hidx Hrd Hlen Hok96 HokW H9 H11 H12.
  destruct (bsl_walk mem rom L idx a2w bs HL Hidx Hrd Hlen Hok96 HokW regs H9 H11 H12) as (regs' & Hms & Hrest).
  exists regs'. split; [|exact Hrest].
  match type of Hms with msteps _ (mkst _ ?pp _ _) (mkst _ ?qq _ _) =>
    replace (Z_to_bv 64 (K1N.BSL_ENTRY RPN.RP_ASAN)) with pp by (apply bv_eq; reflexivity);
    replace (Z_to_bv 64 (K1N.BSL_EXIT RPN.RP_ASAN)) with qq by (apply bv_eq; reflexivity) end.
  exact Hms.
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section AsanNode.
Variable nx0 : N.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis nx0_ge7 : APS.nx0_ok nx0.   (* [comment removed for export] *)
Variable FS0 : Fs.Fs.

Theorem asan_k1_ext_sound : ext_stmt ASEGS ASAN nx0 LIMIT (K1N.xn ASEGS nx0 RPN.RP_ASAN) SINV argH FS0.
Proof.
  eapply (k1_xn_sound ASEGS ASAN nx0 RPN.RP_ASAN LIMIT); try eassumption;
    first [ exact asan_wx | exact asan_in_hull | exact asan_hull_ok | exact asan_segs_wr | exact asan_clz_spec | exact asan_bsl_spec | idtac ].
Qed.
End AsanNode.
