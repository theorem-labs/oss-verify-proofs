(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk Hoare AgentLib.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanPopFree AsanPlanSoundSumsK. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import SumsAsanSpecsK_b AsanIStrncpyK_b AsanPopFreeAsanK_b Ba0PlanImagesK_b.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)

Lemma istrncpy_clob_sub : forall r, In r istrncpy_clob -> In (AX2K.ridx r) APK.caller_saved.
Proof.
  intros r H. unfold istrncpy_clob in H. cbn [In] in H.
  repeat (destruct H as [<-|H]; [cbn; tauto|]). destruct H.
Qed.

Lemma asan_istrncpy_spec : APSXK.istrncpy_spec ASEGS0 (APK.x_istrncpy ASAN0) (APK.x_sealed ASAN0).
Proof.
  intros mem0 dst regs ret Hnone Hst Hnw Hdisj Hret R1 R10 R11 R12.
  destruct (asan_istrncpy_sealed mem0 dst (seg_rom ASEGS0) regs ret Hnone Hst Hnw Hdisj Hret R1 R10 R11 R12)
    as (regs' & Hms & Hag).
  exists regs'. split; [|split].
  - replace APSXK.SEALED_BYTES with strncpy_sealed_bytes by reflexivity.
    replace (Z_to_bv 64 (APK.x_istrncpy ASAN0)) with asan_istrncpy_entry by (apply bv_eq; reflexivity). exact Hms.
  - eapply kept_ok_of_regs_agree; [apply istrncpy_clob_sub | exact Hag].
  - rewrite <- R10. apply Hag. unfold istrncpy_clob. cbn. intros [H|[H|[H|[H|[H|[]]]]]]; discriminate.
Qed.

Lemma asan_popfree_spec' : popfree_spec ASEGS0 (APK.x_popfree ASAN0).
Proof. exact asan_popfree_spec. Qed.

(* [comment removed for export] *)

Section AsanNodes.
Variable scfg : SpuriousCfg.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : AX2K.env -> (word -> option byte) -> Prop.
Variable argH : AX2K.env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> APK.CEIL <= bv_unsigned a /\ APSK.uE E APCK.e_sp0 <= bv_unsigned a.   (* [comment removed for export] *)
Hypothesis e_sp0_init : APCK.expr_vars_lt nx0 APCK.e_sp0 = true.                                                                (* [comment removed for export] *)
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Variable FS0 : Fs.Fs.

#[local] Notation XSTMT := (APSK.x_stmt ASEGS0 scfg ASAN0 nx0 LIMIT SINV argH FS0).

#[local] Ltac close_with NODE SPEC :=
  eapply NODE; try eassumption;
  first [ exact Asan0_wx_nowrap | exact asan0_in_hull | exact asan0_res_len | exact asan0_hull_ok | exact asan0_segs_wr | exact SPEC | idtac ].

Theorem asan_node_x_sound_XIMemset : XSTMT APK.XIMemset.
Proof. eapply APSXK.node_x_sound_XIMemset; try eassumption; try apply asan0_segs_wr; try apply Asan0_wx_nowrap; try apply asan0_in_hull;
       try apply asan0_res_len; try apply asan0_hull_ok. apply asan_fill_spec_imemset. Qed.
Theorem asan_node_x_sound_XMemset : XSTMT APK.XMemset.
Proof. eapply APSXK.node_x_sound_XMemset; try eassumption; try apply asan0_segs_wr; try apply Asan0_wx_nowrap; try apply asan0_in_hull;
       try apply asan0_res_len; try apply asan0_hull_ok. apply asan_fill_spec_memset. Qed.
Theorem asan_node_x_sound_XIMemcpy : XSTMT APK.XIMemcpy.
Proof. eapply APSXK.node_x_sound_XIMemcpy; try eassumption; try apply asan0_segs_wr; try apply Asan0_wx_nowrap; try apply asan0_in_hull;
       try apply asan0_res_len; try apply asan0_hull_ok. apply asan_copy_spec_imemcpy. Qed.
Theorem asan_node_x_sound_XMemcpy : XSTMT APK.XMemcpy.
Proof. eapply APSXK.node_x_sound_XMemcpy; try eassumption; try apply asan0_segs_wr; try apply Asan0_wx_nowrap; try apply asan0_in_hull;
       try apply asan0_res_len; try apply asan0_hull_ok. apply asan_copy_spec_memcpy. Qed.
Theorem asan_node_x_sound_XMemIsZero : XSTMT APK.XMemIsZero.
Proof. eapply APSXK.node_x_sound_XMemIsZero; try eassumption; try apply asan0_segs_wr; try apply Asan0_wx_nowrap; try apply asan0_in_hull;
       try apply asan0_res_len; try apply asan0_hull_ok. apply asan_miz_spec. Qed.
Theorem asan_node_x_sound_XIStrncpy : XSTMT APK.XIStrncpy.
Proof. eapply APSXK.node_x_sound_XIStrncpy; try eassumption; try apply asan0_segs_wr; try apply Asan0_wx_nowrap; try apply asan0_in_hull;
       try apply asan0_res_len; try apply asan0_hull_ok. apply asan_istrncpy_spec. Qed.
Theorem asan_node_x_sound_XPopFree : XSTMT APK.XPopFree.
Proof. eapply APSXK.node_x_sound_XPopFree; try eassumption; try apply asan0_segs_wr; try apply Asan0_wx_nowrap; try apply asan0_in_hull;
       try apply asan0_res_len; try apply asan0_hull_ok. apply asan_popfree_spec'. Qed.
End AsanNodes.
