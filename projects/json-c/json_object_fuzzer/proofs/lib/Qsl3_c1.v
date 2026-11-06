(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.json_c.json_object_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyaF QXVi QWTC QgpE Q3bI QU0c Q85Z Q6EJ QND5 QsSk QqZL QF1K Qt8n QWtD QDlz QOTP Q1LT QpvH QKY2 QEdo QG64 QYLF Q0yM QiyH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.
Import QyaF QXVi.
Import QWTC QgpE Q3bI QU0c Q85Z.Mq1 Q85Z Q6EJ QND5 QsSk QqZL.Mq0.
Import QF1K.Mq0.
Import Qt8n QWtD QqZL.Mq2 QDlz QOTP Q1LT QpvH.
Import QKY2.
Import QEdo.Mq0 QG64.Mq0 QYLF.Mq1 Q0yM.
Import QiyH.Mq5.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

Section AsanInstance.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 mbase : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variable stdin : InputStream.
Variable FS0 : Fs.Fs.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Variable uid : word.
Variable hw : word.
Hypothesis Hfit : entry_stack_fits sp argv envp.

Lemma Xenv_tok : 0 <= x_envscan BJO6 /\ x_envscan BJO6 + 12 < 2 ^ 64 /\ x_envscan_k BJO6 = x_envscan BJO6 + 12.
Proof. cbn [x_envscan x_envscan_k BJO6]. lia. Qed.
Lemma Xpn_tok : 8 <= x_pnscan BJO6 /\ x_pnscan BJO6 + 12 < 2 ^ 64 /\ x_pnscan_k BJO6 = x_pnscan BJO6 + 12.
Proof. cbn [x_pnscan x_pnscan_k BJO6]. lia. Qed.
Lemma Fe1_tok : fetch_word JOB6SEGS (Z_to_bv 64 (x_envscan BJO6)) = Some W_ce3d0.      Proof. exact (fetch_lit _ _ _ _ eq_refl F_ce3d0). Qed.
Lemma Fe2_tok : fetch_word JOB6SEGS (Z_to_bv 64 (x_envscan BJO6 + 4)) = Some W_ce3d4.  Proof. exact (fetch_lit _ _ _ _ eq_refl F_ce3d4). Qed.
Lemma Fe3_tok : fetch_word JOB6SEGS (Z_to_bv 64 (x_envscan BJO6 + 8)) = Some W_ce3d8.  Proof. exact (fetch_lit _ _ _ _ eq_refl F_ce3d8). Qed.
Lemma Fp0_tok : fetch_word JOB6SEGS (Z_to_bv 64 (x_pnscan BJO6 - 8)) = Some W_ce48c.   Proof. exact (fetch_lit _ _ _ _ eq_refl F_ce48c). Qed.
Lemma Fp1_tok : fetch_word JOB6SEGS (Z_to_bv 64 (x_pnscan BJO6 - 4)) = Some W_ce490.   Proof. exact (fetch_lit _ _ _ _ eq_refl F_ce490). Qed.
Lemma Fp2_tok : fetch_word JOB6SEGS (Z_to_bv 64 (x_pnscan BJO6)) = Some W_ce494.       Proof. exact (fetch_lit _ _ _ _ eq_refl F_ce494). Qed.
Lemma Fp3_tok : fetch_word JOB6SEGS (Z_to_bv 64 (x_pnscan BJO6 + 4)) = Some W_ce498.   Proof. exact (fetch_lit _ _ _ _ eq_refl F_ce498). Qed.
Lemma Fp4_tok : fetch_word JOB6SEGS (Z_to_bv 64 (x_pnscan BJO6 + 8)) = Some W_ce49c.   Proof. exact (fetch_lit _ _ _ _ eq_refl F_ce49c). Qed.
Lemma Ee_tok : is_ecall W_ce3d0 = false /\ is_ecall W_ce3d4 = false /\ is_ecall W_ce3d8 = false.
Proof. repeat split; reflexivity. Qed.
Lemma Ep_tok : is_ecall W_ce48c = false /\ is_ecall W_ce490 = false /\ is_ecall W_ce494 = false /\ is_ecall W_ce498 = false /\ is_ecall W_ce49c = false.
Proof. repeat split; reflexivity. Qed.
Lemma sp_lo_tok : sp_window_lo <= bv_unsigned sp.  Proof. destruct Hsp as [H _]. exact H. Qed.
Lemma sp_hi_tok : bv_unsigned sp <= sp_window_hi.  Proof. destruct Hsp as (_ & H & _). exact H. Qed.

Section AnySINV.

Variable nx0 : nat.
Hypothesis Hnx0 : (NX0 <= nx0)%nat.

Variable SINV : env -> (word -> option byte) -> Prop.
Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 JOB6PH sp rdraw brk0 argv envp uid hw E M.
Hypothesis SINV_frame : forall E M M', (forall a, argH0 JOB6PH sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

Lemma argH0_agree_nx0 : forall E E' (a : word), env_agree nx0 E E' -> argH0 JOB6PH sp rdraw argv envp uid hw E a = argH0 JOB6PH sp rdraw argv envp uid hw E' a.
Proof. intros E E' a Hag. apply argH0_agree. eapply env_agree_le; [exact Hag | exact Hnx0]. Qed.

Lemma nx0_ge_gen : APS.nx0_ge nx0.
Proof. unfold APS.nx0_ge. pose proof Hnx0 as H. unfold NX0 in H. lia. Qed.

#[local] Ltac init_side :=
first [ exact asan_wx | exact asan_in_hull | exact asan_hull_ok
| exact Xenv_tok | exact Xpn_tok
| exact Fe1_tok | exact Fe2_tok | exact Fe3_tok | exact Fp0_tok | exact Fp1_tok | exact Fp2_tok | exact Fp3_tok | exact Fp4_tok
| exact Ee_tok | exact Ep_tok
| exact D_ce3d0 | exact D_ce3d4 | exact D_ce3d8 | exact D_ce48c | exact D_ce490 | exact D_ce494 | exact D_ce498 | exact D_ce49c
| exact Hva | exact Hve | exact sp_lo_tok | exact sp_hi_tok
| exact (argH0_high JOB6PH sp rdraw argv envp uid hw Hsp Hva) | exact argH0_agree_nx0
| exact SINV_frame | exact SINV_agree | exact nx0_ge_gen
| intros; eapply SINV0_vals; eassumption
| intros; eapply SINV0_envp; eassumption
| intros; eapply SINV0_str0; eassumption
| assumption ].

Theorem node_x_sound_XEnvScan_asan_gen : x_stmt JOB6SEGS BJO6 nx0 LIMIT (bv_unsigned sp) SINV (argH0 JOB6PH sp rdraw argv envp uid hw) FS0 XEnvScan.
Proof.
eapply (x_sound_envscan JOB6SEGS BJO6 nx0 LIMIT sp SINV (argH0 JOB6PH sp rdraw argv envp uid hw) FS0 asan_wx asan_in_hull asan_hull_ok SINV_frame W_ce3d0 W_ce3d4 W_ce3d8);
init_side.
Qed.

Theorem node_x_sound_XPnScan_asan_gen : x_stmt JOB6SEGS BJO6 nx0 LIMIT (bv_unsigned sp) SINV (argH0 JOB6PH sp rdraw argv envp uid hw) FS0 XPnScan.
Proof.
eapply (x_sound_pnscan JOB6SEGS BJO6 nx0 LIMIT sp SINV (argH0 JOB6PH sp rdraw argv envp uid hw) FS0 asan_wx asan_in_hull asan_hull_ok
(argH0_high JOB6PH sp rdraw argv envp uid hw Hsp Hva) argH0_agree_nx0 SINV_frame SINV_agree nx0_ge_gen W_ce48c W_ce490 W_ce494 W_ce498 W_ce49c);
init_side.
Qed.

End AnySINV.

End AsanInstance.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.json_c.json_object_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCoy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCoy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLPb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLPb.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgpE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgpE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3bI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3bI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU0c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QU0c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q85Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q85Z.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q85Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q85Z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6EJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6EJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QND5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QND5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsSk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsSk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqZL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqZL.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QF1K.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QF1K.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWtD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqZL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqZL.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1LT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1LT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpvH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpvH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDRB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDRB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEdo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEdo.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG64.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYLF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYLF.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0yM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0yM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QiyH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QiyH.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

Section AsanInstance.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 mbase : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variable stdin : InputStream.
Variable FS0 : Fs.Fs.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Variable uid : word.
Variable hw : word.
Hypothesis Hfit : entry_stack_fits sp argv envp.

Lemma Xenv_tok : 0 <= x_envscan AJO6 /\ x_envscan AJO6 + 12 < 2 ^ 64 /\ x_envscan_k AJO6 = x_envscan AJO6 + 12.
Proof. cbn [x_envscan x_envscan_k AJO6]. lia. Qed.
Lemma Xpn_tok : 8 <= x_pnscan AJO6 /\ x_pnscan AJO6 + 12 < 2 ^ 64 /\ x_pnscan_k AJO6 = x_pnscan AJO6 + 12.
Proof. cbn [x_pnscan x_pnscan_k AJO6]. lia. Qed.
Lemma Fe1_tok : fetch_word JO6SEGS (Z_to_bv 64 (x_envscan AJO6)) = Some W_cbce4.      Proof. exact (fetch_lit _ _ _ _ eq_refl F_cbce4). Qed.
Lemma Fe2_tok : fetch_word JO6SEGS (Z_to_bv 64 (x_envscan AJO6 + 4)) = Some W_cbce8.  Proof. exact (fetch_lit _ _ _ _ eq_refl F_cbce8). Qed.
Lemma Fe3_tok : fetch_word JO6SEGS (Z_to_bv 64 (x_envscan AJO6 + 8)) = Some W_cbcec.  Proof. exact (fetch_lit _ _ _ _ eq_refl F_cbcec). Qed.
Lemma Fp0_tok : fetch_word JO6SEGS (Z_to_bv 64 (x_pnscan AJO6 - 8)) = Some W_cbda0.   Proof. exact (fetch_lit _ _ _ _ eq_refl F_cbda0). Qed.
Lemma Fp1_tok : fetch_word JO6SEGS (Z_to_bv 64 (x_pnscan AJO6 - 4)) = Some W_cbda4.   Proof. exact (fetch_lit _ _ _ _ eq_refl F_cbda4). Qed.
Lemma Fp2_tok : fetch_word JO6SEGS (Z_to_bv 64 (x_pnscan AJO6)) = Some W_cbda8.       Proof. exact (fetch_lit _ _ _ _ eq_refl F_cbda8). Qed.
Lemma Fp3_tok : fetch_word JO6SEGS (Z_to_bv 64 (x_pnscan AJO6 + 4)) = Some W_cbdac.   Proof. exact (fetch_lit _ _ _ _ eq_refl F_cbdac). Qed.
Lemma Fp4_tok : fetch_word JO6SEGS (Z_to_bv 64 (x_pnscan AJO6 + 8)) = Some W_cbdb0.   Proof. exact (fetch_lit _ _ _ _ eq_refl F_cbdb0). Qed.
Lemma Ee_tok : is_ecall W_cbce4 = false /\ is_ecall W_cbce8 = false /\ is_ecall W_cbcec = false.
Proof. repeat split; reflexivity. Qed.
Lemma Ep_tok : is_ecall W_cbda0 = false /\ is_ecall W_cbda4 = false /\ is_ecall W_cbda8 = false /\ is_ecall W_cbdac = false /\ is_ecall W_cbdb0 = false.
Proof. repeat split; reflexivity. Qed.
Lemma sp_lo_tok : sp_window_lo <= bv_unsigned sp.  Proof. destruct Hsp as [H _]. exact H. Qed.
Lemma sp_hi_tok : bv_unsigned sp <= sp_window_hi.  Proof. destruct Hsp as (_ & H & _). exact H. Qed.

Section AnySINV.

Variable nx0 : nat.
Hypothesis Hnx0 : (NX0 <= nx0)%nat.

Variable SINV : env -> (word -> option byte) -> Prop.
Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 JO6PH sp rdraw brk0 argv envp uid hw E M.
Hypothesis SINV_frame : forall E M M', (forall a, argH0 JO6PH sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

Lemma argH0_agree_nx0 : forall E E' (a : word), env_agree nx0 E E' -> argH0 JO6PH sp rdraw argv envp uid hw E a = argH0 JO6PH sp rdraw argv envp uid hw E' a.
Proof. intros E E' a Hag. apply argH0_agree. eapply env_agree_le; [exact Hag | exact Hnx0]. Qed.

Lemma nx0_ge_gen : APS.nx0_ge nx0.
Proof. unfold APS.nx0_ge. pose proof Hnx0 as H. unfold NX0 in H. lia. Qed.

#[local] Ltac init_side :=
first [ exact asan_wx | exact asan_in_hull | exact asan_hull_ok
| exact Xenv_tok | exact Xpn_tok
| exact Fe1_tok | exact Fe2_tok | exact Fe3_tok | exact Fp0_tok | exact Fp1_tok | exact Fp2_tok | exact Fp3_tok | exact Fp4_tok
| exact Ee_tok | exact Ep_tok
| exact D_cbce4 | exact D_cbce8 | exact D_cbcec | exact D_cbda0 | exact D_cbda4 | exact D_cbda8 | exact D_cbdac | exact D_cbdb0
| exact Hva | exact Hve | exact sp_lo_tok | exact sp_hi_tok
| exact (argH0_high JO6PH sp rdraw argv envp uid hw Hsp Hva) | exact argH0_agree_nx0
| exact SINV_frame | exact SINV_agree | exact nx0_ge_gen
| intros; eapply SINV0_vals; eassumption
| intros; eapply SINV0_envp; eassumption
| intros; eapply SINV0_str0; eassumption
| assumption ].

Theorem node_x_sound_XEnvScan_asan_gen : x_stmt JO6SEGS AJO6 nx0 LIMIT (bv_unsigned sp) SINV (argH0 JO6PH sp rdraw argv envp uid hw) FS0 XEnvScan.
Proof.
eapply (x_sound_envscan JO6SEGS AJO6 nx0 LIMIT sp SINV (argH0 JO6PH sp rdraw argv envp uid hw) FS0 asan_wx asan_in_hull asan_hull_ok SINV_frame W_cbce4 W_cbce8 W_cbcec);
init_side.
Qed.

Theorem node_x_sound_XPnScan_asan_gen : x_stmt JO6SEGS AJO6 nx0 LIMIT (bv_unsigned sp) SINV (argH0 JO6PH sp rdraw argv envp uid hw) FS0 XPnScan.
Proof.
eapply (x_sound_pnscan JO6SEGS AJO6 nx0 LIMIT sp SINV (argH0 JO6PH sp rdraw argv envp uid hw) FS0 asan_wx asan_in_hull asan_hull_ok
(argH0_high JO6PH sp rdraw argv envp uid hw Hsp Hva) argH0_agree_nx0 SINV_frame SINV_agree nx0_ge_gen W_cbda0 W_cbda4 W_cbda8 W_cbdac W_cbdb0);
init_side.
Qed.

End AnySINV.

End AsanInstance.
