(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PropExec StoreOk Hoare AgentLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanPopFree AsanPlanSoundSums SumsAsanSpecs AsanIStrncpy AsanPopFreeAsan AsanPlanImages.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_SumsAsanClose () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.env"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.le"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Logic.not"; "Corelib.Init.Datatypes.None"].


(* [comment removed for export] *)

Lemma istrncpy_clob_sub : forall r, In r istrncpy_clob -> In (AX2.ridx r) AP.caller_saved.
Proof.
  intros r H. unfold istrncpy_clob in H. cbn [In] in H.
  repeat (destruct H as [<-|H]; [cbn; tauto|]). destruct H.
Qed.

Lemma asan_istrncpy_spec : APSX.istrncpy_spec ASEGS (AP.x_istrncpy AP.BOTH) (AP.x_sealed AP.BOTH).
Proof.
  intros mem0 dst regs ret Hnone Hst Hnw Hdisj Hret R1 R10 R11 R12.
  destruct (asan_istrncpy_sealed mem0 dst (seg_rom ASEGS) regs ret Hnone Hst Hnw Hdisj Hret R1 R10 R11 R12)
    as (regs' & Hms & Hag).
  exists regs'. split; [|split].
  - replace APSX.SEALED_BYTES with strncpy_sealed_bytes by reflexivity.
    replace (Z_to_bv 64 (AP.x_istrncpy AP.BOTH)) with asan_istrncpy_entry by (apply bv_eq; reflexivity). exact Hms.
  - eapply kept_ok_of_regs_agree; [apply istrncpy_clob_sub | exact Hag].
  - rewrite <- R10. apply Hag. unfold istrncpy_clob. cbn. intros [H|[H|[H|[H|[H|[]]]]]]; discriminate.
Qed.

Lemma asan_popfree_spec' : popfree_spec ASEGS (AP.x_popfree AP.BOTH).
Proof. exact asan_popfree_spec. Qed.

(* [comment removed for export] *)

Section AsanNodes.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Variable SP0 : Z.                        (* [comment removed for export] *)
Hypothesis SP0_ok : APS.sp0_ok SP0.
Hypothesis argH_high : forall E (a : word), argH E a = true -> SP0 <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : ltac2:(CDefT.buildp (gd_tbl_SumsAsanClose ()) "PE,$0.PM,Px,(1.&40.)(2.(1.&8.))PM',Px,(1.&40.)(2.(1.&8.))P,Pa,(1.&40.)P,(3.$4.A2.VargH,R4.R1.$5.)(3.(2.(1.&8.))A1.R3.R2.A1.R4.R2.)P,Pa,(1.&40.)P,(6.VSP0,(7.&40.R1.))P,(8.(3.(2.(1.&8.))A1.R5.R2.(9.(1.&8.))))(8.(3.(2.(1.&8.))A1.R5.R3.(9.(1.&8.))))P,A2.VSINV,R5.R4.A2.VSINV,R6.R4.")
(* [comment removed for export] *).   (* [comment removed for export] *)
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis SINV_sp : forall E M, SINV E M -> APS.uE_sp0 E = SP0.   (* [comment removed for export] *)
Variable FS0 : Fs.Fs.

#[local] Notation XSTMT := (APS.x_stmt ASEGS AP.BOTH nx0 LIMIT SP0 SINV argH FS0).

#[local] Ltac close_with NODE SPEC :=
  eapply NODE; try eassumption;
  first [ exact asan_wx | exact asan_in_hull | exact asan_res_len | exact asan_hull_ok | exact asan_segs_wr | exact SPEC | idtac ].

#[using="SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Theorem asan_node_x_sound_XIMemset : XSTMT AP.XIMemset.
Proof. eapply APSX.node_x_sound_XIMemset; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
       try apply asan_res_len; try apply asan_hull_ok; try apply asan_hull_cov. apply asan_fill_spec_imemset. Qed.
(* [comment removed for export] *)
#[using="SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Theorem asan_node_x_sound0_XIMemset : APS.x_stmt0 ASEGS AP.BOTH nx0 LIMIT SP0 SINV argH FS0 AP.XIMemset.
Proof. eapply APSX.node_x_sound0_XIMemset; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
       try apply asan_res_len; try apply asan_hull_ok; try apply asan_hull_cov. apply asan_fill_spec_imemset. Qed.
(* [comment removed for export] *)
#[using="SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Theorem asan_node_x_sound0_all :
  forall x, APS.x_spin_ok x = true -> APS.x_stmt0 ASEGS AP.BOTH nx0 LIMIT SP0 SINV argH FS0 x.
Proof. intros [ | | | | | | | | | | ] H; try discriminate H. exact asan_node_x_sound0_XIMemset. Qed.
#[using="SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Theorem asan_node_x_sound_XMemset : XSTMT AP.XMemset.
Proof. eapply APSX.node_x_sound_XMemset; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
       try apply asan_res_len; try apply asan_hull_ok; try apply asan_hull_cov. apply asan_fill_spec_memset. Qed.
#[using="SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Theorem asan_node_x_sound_XIMemcpy : XSTMT AP.XIMemcpy.
Proof. eapply APSX.node_x_sound_XIMemcpy; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
       try apply asan_res_len; try apply asan_hull_ok; try apply asan_hull_cov. apply asan_copy_spec_imemcpy. Qed.
#[using="SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Theorem asan_node_x_sound_XMemcpy : XSTMT AP.XMemcpy.
Proof. eapply APSX.node_x_sound_XMemcpy; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
       try apply asan_res_len; try apply asan_hull_ok; try apply asan_hull_cov. apply asan_copy_spec_memcpy. Qed.
#[using="SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Theorem asan_node_x_sound_XMemIsZero : XSTMT AP.XMemIsZero.
Proof. eapply APSX.node_x_sound_XMemIsZero; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
       try apply asan_res_len; try apply asan_hull_ok; try apply asan_hull_cov. apply asan_miz_spec. Qed.
#[using="SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Theorem asan_node_x_sound_XIStrncpy : XSTMT AP.XIStrncpy.
Proof. eapply APSX.node_x_sound_XIStrncpy; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
       try apply asan_res_len; try apply asan_hull_ok; try apply asan_hull_cov. apply asan_istrncpy_spec. Qed.
#[using="SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Theorem asan_node_x_sound_XPopFree : XSTMT AP.XPopFree.
Proof. eapply APSX.node_x_sound_XPopFree; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
       try apply asan_res_len; try apply asan_hull_ok; try apply asan_hull_cov. apply asan_popfree_spec'. Qed.
End AsanNodes.
