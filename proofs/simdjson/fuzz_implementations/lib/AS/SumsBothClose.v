(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.simdjson.fuzz_implementations.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import PropExec StoreOk Hoare AgentLib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import PropExec.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AsanTablesB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AsanPopFree AsanPlanSoundSums SumsBothSpecs AsanIStrncpyB AsanPopFreeBoth AsanPlanImagesB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma istrncpy_clob_sub : forall r, In r istrncpy_clob -> In (AX2.ridx r) AP.caller_saved.
Proof.
  intros r H. unfold istrncpy_clob in H. cbn [In] in H.
  repeat (destruct H as [<-|H]; [cbn; tauto|]). destruct H.
Qed.

Lemma asan_istrncpy_spec : APSX.istrncpy_spec ASEGS (AP.x_istrncpy ASAN_B) (AP.x_sealed ASAN_B).
Proof.
  intros mem0 dst regs ret Hnone Hst Hnw Hdisj Hret R1 R10 R11 R12.
  destruct (asan_istrncpy_sealed mem0 dst (seg_rom ASEGS) regs ret Hnone Hst Hnw Hdisj Hret R1 R10 R11 R12)
    as (regs' & Hms & Hag).
  exists regs'. split; [|split].
  - replace APSX.SEALED_BYTES with strncpy_sealed_bytes by reflexivity.
    replace (Z_to_bv 64 (AP.x_istrncpy ASAN_B)) with asan_istrncpy_entry by (apply bv_eq; reflexivity). exact Hms.
  - eapply kept_ok_of_regs_agree; [apply istrncpy_clob_sub | exact Hag].
  - rewrite <- R10. apply Hag. unfold istrncpy_clob. cbn. intros [H|[H|[H|[H|[H|[]]]]]]; discriminate.
Qed.

Lemma asan_popfree_spec' : popfree_spec ASEGS (AP.x_popfree ASAN_B).
Proof. exact asan_popfree_spec. Qed.

Section AsanNodes.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> AP.CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Variable FS0 : Fs.Fs.

#[local] Notation XSTMT := (APS.x_stmt ASEGS ASAN_B nx0 LIMIT SINV argH FS0).

#[local] Ltac close_with NODE SPEC :=
  eapply NODE; try eassumption;
  first [ exact asan_wx | exact asan_in_hull | exact asan_res_len | exact asan_hull_ok | exact asan_segs_wr | exact SPEC | idtac ].

Theorem asan_node_x_sound_XIMemset : XSTMT AP.XIMemset.
Proof. eapply APSX.node_x_sound_XIMemset; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
       try apply asan_res_len; try apply asan_hull_ok. apply asan_fill_spec_imemset. Qed.
Theorem asan_node_x_sound_XMemset : XSTMT AP.XMemset.
Proof. eapply APSX.node_x_sound_XMemset; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
       try apply asan_res_len; try apply asan_hull_ok. apply asan_fill_spec_memset. Qed.
Theorem asan_node_x_sound_XIMemcpy : XSTMT AP.XIMemcpy.
Proof. eapply APSX.node_x_sound_XIMemcpy; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
       try apply asan_res_len; try apply asan_hull_ok. apply asan_copy_spec_imemcpy. Qed.
Theorem asan_node_x_sound_XMemcpy : XSTMT AP.XMemcpy.
Proof. eapply APSX.node_x_sound_XMemcpy; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
       try apply asan_res_len; try apply asan_hull_ok. apply asan_copy_spec_memcpy. Qed.
Theorem asan_node_x_sound_XMemIsZero : XSTMT AP.XMemIsZero.
Proof. eapply APSX.node_x_sound_XMemIsZero; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
       try apply asan_res_len; try apply asan_hull_ok. apply asan_miz_spec. Qed.
Theorem asan_node_x_sound_XIStrncpy : XSTMT AP.XIStrncpy.
Proof. eapply APSX.node_x_sound_XIStrncpy; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
       try apply asan_res_len; try apply asan_hull_ok. apply asan_istrncpy_spec. Qed.
Theorem asan_node_x_sound_XPopFree : XSTMT AP.XPopFree.
Proof. eapply APSX.node_x_sound_XPopFree; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
       try apply asan_res_len; try apply asan_hull_ok. apply asan_popfree_spec'. Qed.
End AsanNodes.
