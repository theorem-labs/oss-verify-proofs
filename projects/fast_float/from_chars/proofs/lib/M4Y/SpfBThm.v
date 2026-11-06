(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxImg FxPlan FxLoop FxFrame FxDrv FxCall FxWork FxWorkX FxGenA FxGenX.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWorkX OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxGenA OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxGenX.
From OSSVerify.Proofs.fast_float.from_chars.lib.HX Require Import HxGen.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXB Require Import HxGenFp HxRebaseB HxSemB HxBaseB HxIntBF HxDotBF HxDefsBF HxExpBF HxSw8BF HxSw4BF HxByteBF HxRulesBF HxTmBF.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn M4B_dcff FxGenB.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.M4B_tmpl OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn OSSVerify.Proofs.fast_float.from_chars.lib.M4B_dcff OSSVerify.Proofs.fast_float.from_chars.lib.FxGenB.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4Y Require Import SpfBD SpfB.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4Y Require Import FxConstGen.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma TM_eq : TM = mk_tbl BSEGS 0x9a970 2503.
Proof. vm_cast_no_check (eq_refl TM). Qed.
Lemma IMGW_eq : IMGW = mk_imgs_acc IMGR TEmpty.
Proof. vm_cast_no_check (eq_refl IMGW). Qed.
Lemma IMGW_ok : img_ok BSEGS IMGW.
Proof.
  rewrite IMGW_eq.
  apply mk_imgs_acc_ok; [unfold IMGR; repeat constructor; cbn; lia|]. intros p v Hp. rewrite tget_empty in Hp. discriminate.
Qed.
Lemma RETS_ok : Forall (is_ret BSEGS) RETS.
Proof. unfold RETS. repeat constructor. exists (Z_to_bv 32 0x00008067). (split; [|split]); vm_refl_bv. Qed.
Lemma xsites_NODES : xsites NODES = [].
Proof. reflexivity. Qed.
Lemma xhandl_NODES : xhandl NODES =
  [H_INT; H_DOT; R_NOFRAC; R_DIG0; H_SW8; hx_eqreg 0x9b700 27 16; H_SW4C; H_SW4; H_BYTE; R_FRAC; H_EXP; hx_ssplit 0x9c4e0 7; H_TM;
   hx_fold 0x60644 11; hx_fold 0x60644 11; hx_rebase 0x9bdec 14; hx_rebase 0x9b974 14; hx_rebase 0x9bd5c 14; hx_promote 0x9c498 17].
Proof. reflexivity. Qed.
Lemma xksites_NODES : xksites NODES = [(SM4_P0, SM4_Q); (MSB32_P0, MSB32_Q); (MSB27_P0, MSB27_Q); (MSB32_P0, MSB32_Q); (MSB27_P0, MSB27_Q); (SSF5_P0, SSF5_Q)].
Proof. reflexivity. Qed.
Lemma xfsites_NODES : xfsites NODES = [(DCF_P0 true, DCF_Q true, 0x9c2bc); (DCF_P0 false, DCF_Q false, 0x9c2bc)].
Proof. reflexivity. Qed.

Section Spd.
Hypothesis H_SM4 : kfn_ok BSEGS SM4_P0 SM4_Q.
Hypothesis H_MSB32 : kfn_ok BSEGS MSB32_P0 MSB32_Q.
Hypothesis H_MSB27 : kfn_ok BSEGS MSB27_P0 MSB27_Q.
Hypothesis H_SSF5 : kfn_ok BSEGS SSF5_P0 SSF5_Q.
Hypothesis H_DCF : forall frac, kfrag_ok BSEGS (DCF_P0 frac) (DCF_Q frac) 0x9c2bc.
(* [comment removed for export] *)
Let H_TM_ok' := hand_okxP_ok _ _ _ _ H_TM_ok.
Let H_SW8_ok' := hand_okxP_ok _ _ _ _ H_SW8_ok.
Let H_SW4C_ok' := hand_okxP_ok _ _ _ _ H_SW4C_ok.
Let H_SW4_ok' := hand_okxP_ok _ _ _ _ H_SW4_ok.
Let H_BYTE_ok' := hand_okxP_ok _ _ _ _ H_BYTE_ok.
Let R_NOFRAC_ok' := hand_okxP_ok _ _ _ _ R_NOFRAC_ok.
Let R_DIG0_ok' := hand_okxP_ok _ _ _ _ R_DIG0_ok.
Let R_FRAC_ok' := hand_okxP_ok _ _ _ _ R_FRAC_ok.

#[using="H_SM4 H_MSB32 H_MSB27 H_SSF5 H_DCF H_TM_ok' H_SW8_ok' H_SW4C_ok' H_SW4_ok' H_BYTE_ok' R_NOFRAC_ok' R_DIG0_ok' R_FRAC_ok'"] Theorem spf_ok : fn_ok BSEGS P0 SPF_Q RETS.
Proof. LiaFast.lf_pins (fun (H_SM4 H_MSB32 H_MSB27 H_SSF5 H_DCF H_TM_ok' H_SW8_ok' H_SW4C_ok' H_SW4_ok' H_BYTE_ok' R_NOFRAC_ok' R_DIG0_ok' R_FRAC_ok' : LiaFast.U) => LiaFast.u0).
  apply (fn_ok_of_wcertx BSEGS xok_spd TM IMGW 10 P0RUN NODESC P0 SPF_Q RETS ltac:(rewrite TM_eq; apply mk_tbl_ok) IMGW_ok SPF_cert).
  - intros P0' Q' H. rewrite NODESC_xsites, xsites_NODES in H. destruct H.
  - intros f H. rewrite NODESC_xhandl, xhandl_NODES in H.
    repeat (destruct H as [H|H];
            [subst f; first [exact (hand_okxP_ok _ _ _ _ H_INT_ok) | exact (hand_okxP_ok _ _ _ _ H_DOT_ok) | exact (hand_okxP_ok _ _ _ _ H_EXP_ok)
                            | exact H_SW8_ok' | exact H_SW4C_ok' | exact H_SW4_ok' | exact H_BYTE_ok' | exact H_TM_ok' | exact R_NOFRAC_ok' | exact R_DIG0_ok' | exact R_FRAC_ok'
                            | exact (hand_okxP_ok _ _ _ _ (hx_eqreg_ok_fp BSEGS xok_spd _ _ _)) | exact (hand_okxP_ok _ _ _ _ (hx_ssplit_ok_fp BSEGS xok_spd _ _))
                            | exact (hand_okxP_ok _ _ _ _ (hx_ssign_ok_fp BSEGS xok_spd _ _)) | apply hx_rebase_ok | apply hx_fold_ok | apply hx_promote_ok] |]).
    destruct H.
  - intros P0' Q' H. rewrite NODESC_xksites, xksites_NODES in H.
    repeat (destruct H as [H|H]; [injection H as <- <-; assumption|]). destruct H.
  - intros P0' Q' pcQ H. rewrite NODESC_xfsites, xfsites_NODES in H.
    repeat (destruct H as [H|H]; [injection H as <- <- <-; apply H_DCF|]). destruct H.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - exact RETS_ok.
Qed.
End Spd.
