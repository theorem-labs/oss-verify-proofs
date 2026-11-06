(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgA.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec StoreOk Hoare AgentLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanPopFree AsanPlanSoundSums SumsAsanSpecs AsanIStrncpy AsanPopFreeAsan AsanPlanImages.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section FPW. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)

Lemma istrncpy_clob_sub : forall r, In r istrncpy_clob -> In (AX2.ridx r) AP.caller_saved.
Proof.
  intros r H. unfold istrncpy_clob in H. cbn [In] in H.
  repeat (destruct H as [<-|H]; [cbn; tauto|]). destruct H.
Qed.

Lemma asan_istrncpy_spec : APSX.istrncpy_spec ASEGS (AP.x_istrncpy AP.ASAN) (AP.x_sealed AP.ASAN).
Proof.
  intros mem0 dst regs ret Hnone Hst Hnw Hdisj Hret R1 R10 R11 R12.
  destruct (asan_istrncpy_sealed mem0 dst (seg_rom ASEGS) regs ret Hnone Hst Hnw Hdisj Hret R1 R10 R11 R12)
    as (regs' & Hms & Hag).
  exists regs'. split; [|split].
  - replace APSX.SEALED_BYTES with strncpy_sealed_bytes by reflexivity.
    replace (Z_to_bv 64 (AP.x_istrncpy AP.ASAN)) with asan_istrncpy_entry by (apply bv_eq; reflexivity). exact Hms.
  - eapply kept_ok_of_regs_agree; [apply istrncpy_clob_sub | exact Hag].
  - rewrite <- R10. apply Hag. unfold istrncpy_clob. cbn. intros [H|[H|[H|[H|[H|[]]]]]]; discriminate.
Qed.

Lemma asan_popfree_spec' : popfree_spec ASEGS (AP.x_popfree AP.ASAN).
Proof. exact asan_popfree_spec. Qed.

Lemma asan_hull_okP : APSX.hull_okP AP.ASAN.
Proof. exact asan_hull_ok. Qed.

(* [comment removed for export] *)

Section AsanNodes.
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
  (forall a : word, AP.in_lfp AP.ASAN (bv_unsigned a) = true -> M' a = M a) -> LINV M -> LINV M'.
Variable FS0 : Fs.Fs.

#[local] Notation XSTMT := (@APS.x_stmt ASEGS AP.ASAN nx0 LIMIT SINV argH LINV FS0 fx).

#[local] Ltac close_x NODE SPEC :=
  eapply (NODE fx ASEGS AP.ASAN nx0 LIMIT asan_wx asan_in_hull asan_hull_okP SINV argH LINV argH_high argH_agree nx0_ge SINV_frame SINV_agree LINV_frame FS0);
  try exact SPEC; try apply asan_segs_wr; try exact SPEC.

Theorem asan_node_x_sound_XIMemset : XSTMT AP.XIMemset.
Proof. close_x @APSX.node_x_sound_XIMemset asan_fill_spec_imemset. Qed.
Theorem asan_node_x_sound_XMemset : XSTMT AP.XMemset.
Proof. (* [comment removed for export] *)
  eapply (@APSX.node_x_sound_XMemset fx ASEGS AP.ASAN nx0 LIMIT asan_wx asan_in_hull asan_hull_okP asan_shadow_ok SINV argH LINV argH_high argH_agree argH_top nx0_ge SINV_frame SINV_agree LINV_frame FS0);
  try exact asan_fill_spec_memset; try apply asan_segs_wr; try exact asan_fill_spec_memset.
Qed.
Theorem asan_node_x_sound_XIMemcpy : XSTMT AP.XIMemcpy.
Proof. close_x @APSX.node_x_sound_XIMemcpy asan_copy_spec_imemcpy. Qed.
Theorem asan_node_x_sound_XMemcpy : XSTMT AP.XMemcpy.
Proof. close_x @APSX.node_x_sound_XMemcpy asan_copy_spec_memcpy. Qed.
Theorem asan_node_x_sound_XMemIsZero : XSTMT AP.XMemIsZero.
Proof. close_x @APSX.node_x_sound_XMemIsZero asan_miz_spec. Qed.
Theorem asan_node_x_sound_XIStrncpy : XSTMT AP.XIStrncpy.
Proof. close_x @APSX.node_x_sound_XIStrncpy asan_istrncpy_spec. Qed.
Theorem asan_node_x_sound_XPopFree : XSTMT AP.XPopFree.
Proof. close_x @APSX.node_x_sound_XPopFree asan_popfree_spec'. Qed.
End AsanNodes.
End FPW.
