(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxImg FxPlan FxLoop FxFrame FxDrv FxCall FxWork FxWorkX FxGenA FxGenX.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWorkX OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxGenA OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxGenX.
From OSSVerify.Proofs.fast_float.from_chars.lib.HX Require Import HxGen HxSem HxInt HxTm HxDot HxSw8 HxSw4 HxByte HxRules HxIntF HxDotF HxSw8F HxSw4F HxByteF HxRulesF HxTmF.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4A_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4A_kfn M4A_kfnf.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn.M4A_tmpl OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfnf.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4X Require Import SpfA.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4X Require Import FxConstGen.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma TM_eq : TM = mk_tbl ASEGS 0x995c4 2252.
Proof. vm_cast_no_check (eq_refl TM). Qed.
Lemma IMGW_eq : IMGW = mk_imgs_acc IMGR TEmpty.
Proof. vm_cast_no_check (eq_refl IMGW). Qed.
Lemma IMGW_ok : img_ok ASEGS IMGW.
Proof.
  rewrite IMGW_eq.
  apply mk_imgs_acc_ok; [unfold IMGR; repeat constructor; cbn; lia|]. intros p v Hp. rewrite tget_empty in Hp. discriminate.
Qed.
Lemma RETS_ok : Forall (is_ret ASEGS) RETS.
Proof. unfold RETS. repeat constructor. exists (Z_to_bv 32 0x00008067). (split; [|split]); vm_refl_bv. Qed.
Lemma xsites_NODES : xsites NODES = [].
Proof. reflexivity. Qed.
Lemma xhandl_NODES : xhandl NODES = [hx_fold 0x60650 11; hx_fold 0x60650 11;
                                     H_INT_F; H_DOT_F; R_NOFRAC_F; R_DIG0_F; H_SW8_F; H_SW4_F; H_BYTE_F; R_FRAC_F;
                                     hx_fold 0x60650 11; hx_fold 0x60650 11; H_TM_F; hx_fold 0x9b51c 10; hx_promote 0x9b278 17].
Proof. reflexivity. Qed.
Lemma xksites_NODES : xksites NODES = [(SM4_P0, SM4_Q); (MEMSET32_P0, MEMSET32_Q); (MEMSET27_P0, MEMSET27_Q);
                                      (MEMSET32_P0, MEMSET32_Q); (MEMSET27_P0, MEMSET27_Q);
                                      (MEMSET32_P0, MEMSET32_Q); (MEMSET27_P0, MEMSET27_Q);
                                      (MEMSET32_P0, MEMSET32_Q); (MEMSET27_P0, MEMSET27_Q); (SSF5_P0, SSF5_Q)].
Proof. reflexivity. Qed.
Lemma xfsites_NODES : xfsites NODES = [(DCF_P0f true, DCF_Qf true, 0x9b078); (DCF_P0f false, DCF_Qf false, 0x9b078)].
Proof. reflexivity. Qed.

Section Spf.
Hypothesis H_SM4 : kfn_ok ASEGS SM4_P0 SM4_Q.
Hypothesis H_MS32 : kfn_ok ASEGS MEMSET32_P0 MEMSET32_Q.
Hypothesis H_MS27 : kfn_ok ASEGS MEMSET27_P0 MEMSET27_Q.
Hypothesis H_SSF5 : kfn_ok ASEGS SSF5_P0 SSF5_Q.
Hypothesis H_DCFf : forall frac, kfrag_ok ASEGS (DCF_P0f frac) (DCF_Qf frac) 0x9b078.

#[using="H_SM4 H_MS32 H_MS27 H_SSF5 H_DCFf"] Theorem spf_ok : fn_ok ASEGS P0 SPF_Q RETS.
Proof. LiaFast.lf_pins (fun (H_SM4 H_MS32 H_MS27 H_SSF5 H_DCFf : LiaFast.U) => LiaFast.u0).
  apply (fn_ok_of_wcertx ASEGS xok_spd TM IMGW 10 P0RUN NODESC P0 SPF_Q RETS ltac:(rewrite TM_eq; apply mk_tbl_ok) IMGW_ok SPF_cert).
  - intros P0' Q' H. rewrite NODESC_xsites, xsites_NODES in H. destruct H.
  - intros f H. rewrite NODESC_xhandl, xhandl_NODES in H.
    repeat (destruct H as [H|H];
            [subst f; first [exact H_INT_F_ok | exact H_DOT_F_ok | exact R_NOFRAC_F_ok | exact R_DIG0_F_ok | exact H_SW8_F_ok | exact H_SW4_F_ok
                            | exact H_BYTE_F_ok | exact R_FRAC_F_ok | exact H_TM_F_ok | apply hx_fold_ok | apply hx_promote_ok] |]).
    destruct H.
  - intros P0' Q' H. rewrite NODESC_xksites, xksites_NODES in H.
    repeat (destruct H as [H|H]; [injection H as <- <-; assumption|]). destruct H.
  - intros P0' Q' pcQ H. rewrite NODESC_xfsites, xfsites_NODES in H.
    repeat (destruct H as [H|H]; [injection H as <- <- <-; apply H_DCFf|]). destruct H.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - exact RETS_ok.
Qed.
End Spf.
