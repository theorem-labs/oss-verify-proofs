(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgB.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec StoreOk Hoare AgentLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanPopFree AsanPlanSoundSums AsanIStrncpy SumsBothInstances SumsAsanSpecs SumsBothSpecs AsanPopFreeBoth
  AsanPlanImages BothPlanImages BothTableL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section FPW. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)

Lemma istrncpy_clob_sub_B : forall r, In r istrncpy_clob -> In (AX2.ridx r) AP.caller_saved.
Proof.
  intros r H. unfold istrncpy_clob in H. cbn [In] in H.
  repeat (destruct H as [<-|H]; [cbn; tauto|]). destruct H.
Qed.

Lemma both_istrncpy_spec : APSX.istrncpy_spec BSEGS (AP.x_istrncpy BOTHL) (AP.x_sealed BOTHL).
Proof.
  intros mem0 dst regs ret Hnone Hst Hnw Hdisj Hret R1 R10 R11 R12.
  destruct (both_istrncpy_sealed mem0 dst (seg_rom BSEGS) regs ret Hnone Hst Hnw Hdisj Hret R1 R10 R11 R12)
    as (regs' & Hms & Hag).
  exists regs'. split; [|split].
  - replace APSX.SEALED_BYTES with strncpy_sealed_bytes by reflexivity.
    replace (Z_to_bv 64 (AP.x_istrncpy BOTHL)) with both_istrncpy_entry by (apply bv_eq; reflexivity). exact Hms.
  - eapply kept_ok_of_regs_agree; [apply istrncpy_clob_sub_B | exact Hag].
  - rewrite <- R10. apply Hag. unfold istrncpy_clob. cbn. intros [H|[H|[H|[H|[H|[]]]]]]; discriminate.
Qed.

Lemma both_popfree_spec' : popfree_spec BSEGS (AP.x_popfree BOTHL).
Proof. exact both_popfree_spec. Qed.

Lemma bothL_hull_okP : APSX.hull_okP BOTHL.
Proof. exact bothL_hull_ok. Qed.

Lemma bothL_fill_spec_imemset : APSX.fill_spec BSEGS (AP.x_imemset BOTHL) 256.
Proof. exact both_fill_spec_imemset. Qed.
Lemma bothL_fill_spec_memset : APSX.fill_spec BSEGS (AP.x_memset BOTHL) AX2.two64.
Proof. exact both_fill_spec_memset. Qed.
Lemma bothL_copy_spec_imemcpy : APSX.copy_spec BSEGS (AP.x_imemcpy BOTHL).
Proof. exact both_copy_spec_imemcpy. Qed.
Lemma bothL_copy_spec_memcpy : APSX.copy_spec BSEGS (AP.x_memcpy BOTHL).
Proof. exact both_copy_spec_memcpy. Qed.
Lemma bothL_miz_spec : APSX.miz_spec BSEGS (AP.x_memiszero BOTHL).
Proof. exact both_miz_spec. Qed.

(* [comment removed for export] *)

Section BothNodes.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Variable LINV : (word -> option byte) -> Prop.
Hypothesis argH_high : forall E (a : word), argH E a = true -> AP.CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis argH_top : forall E M (a : word), SINV E M -> argH E a = true -> bv_unsigned (AX2.edenot E AP.e_sp0) <= bv_unsigned a.   (* [comment removed for export] *)
Hypothesis nx0_ge : APS.nx0_ok nx0.   (* [comment removed for export] *)
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis LINV_frame : forall M M' : word -> option byte,
  (forall a : word, AP.in_lfp BOTHL (bv_unsigned a) = true -> M' a = M a) -> LINV M -> LINV M'.
Variable FS0 : Fs.Fs.

#[local] Notation XSTMT := (@APS.x_stmt BSEGS BOTHL nx0 LIMIT SINV argH LINV FS0 fx).

#[local] Ltac close_x NODE SPEC :=
  eapply (NODE fx BSEGS BOTHL nx0 LIMIT both_wx bothL_in_hull bothL_hull_okP SINV argH LINV argH_high argH_agree nx0_ge SINV_frame SINV_agree LINV_frame FS0);
  try exact SPEC; try apply both_segs_wr; try exact SPEC.

Theorem both_node_x_sound_XIMemset : XSTMT AP.XIMemset.
Proof. close_x @APSX.node_x_sound_XIMemset bothL_fill_spec_imemset. Qed.
Theorem both_node_x_sound_XMemset : XSTMT AP.XMemset.
Proof. (* [comment removed for export] *)
  eapply (@APSX.node_x_sound_XMemset fx BSEGS BOTHL nx0 LIMIT both_wx bothL_in_hull bothL_hull_okP bothL_shadow_ok SINV argH LINV argH_high argH_agree argH_top nx0_ge SINV_frame SINV_agree LINV_frame FS0);
  try exact bothL_fill_spec_memset; try apply both_segs_wr; try exact bothL_fill_spec_memset.
Qed.
Theorem both_node_x_sound_XIMemcpy : XSTMT AP.XIMemcpy.
Proof. close_x @APSX.node_x_sound_XIMemcpy bothL_copy_spec_imemcpy. Qed.
Theorem both_node_x_sound_XMemcpy : XSTMT AP.XMemcpy.
Proof. close_x @APSX.node_x_sound_XMemcpy bothL_copy_spec_memcpy. Qed.
Theorem both_node_x_sound_XMemIsZero : XSTMT AP.XMemIsZero.
Proof. close_x @APSX.node_x_sound_XMemIsZero bothL_miz_spec. Qed.
Theorem both_node_x_sound_XIStrncpy : XSTMT AP.XIStrncpy.
Proof. close_x @APSX.node_x_sound_XIStrncpy both_istrncpy_spec. Qed.
Theorem both_node_x_sound_XPopFree : XSTMT AP.XPopFree.
Proof. close_x @APSX.node_x_sound_XPopFree both_popfree_spec'. Qed.
End BothNodes.
End FPW.
