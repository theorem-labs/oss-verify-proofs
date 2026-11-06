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
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn M4B_lm.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.M4B_tmpl OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn OSSVerify.Proofs.fast_float.from_chars.lib.M4B_lm.
From OSSVerify.Proofs.fast_float.from_chars.lib.LMB Require LmBD LmBA.

Module LmBB.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxImg FxPlan FxLoop FxFrame FxDrv FxCall FxWork FxWorkX FxGenA FxGenX.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWorkX OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxGenA OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxGenX.
From OSSVerify.Proofs.fast_float.from_chars.lib.HX Require Import HxGen.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn M4B_lm.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.M4B_tmpl OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn OSSVerify.Proofs.fast_float.from_chars.lib.M4B_lm.
From OSSVerify.Proofs.fast_float.from_chars.lib.LMB Require Import LmBD.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 cert_refl_vm (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl _ $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Set Default Proof Mode "Ltac2".
Lemma LMB2_cert16 : (match wstartx TM IMGW (vars_below (s_next (LM_EPI_P0 16))) 10 (LM_EPI_P0 16) P2RUN (NODES2 16) with
                     | Some l => forallb (fun X => fin_q (LM_Q 16) [0x97da0] (s_next (LM_EPI_P0 16)) (xs_st X)) l | None => false end) = true.
Proof. cert_refl_vm constr:(true). Qed.
Lemma LMB2_cert0 : (match wstartx TM IMGW (vars_below (s_next (LM_EPI_P0 0))) 10 (LM_EPI_P0 0) P2RUN (NODES2 0) with
                    | Some l => forallb (fun X => fin_q (LM_Q 0) [0x97da0] (s_next (LM_EPI_P0 0)) (xs_st X)) l | None => false end) = true.
Proof. cert_refl_vm constr:(true). Qed.
Set Default Proof Mode "Classic".
End LmBB.

Import OSSVerify.Proofs.fast_float.from_chars.lib.LMB.LmBD OSSVerify.Proofs.fast_float.from_chars.lib.LMB.LmBA OSSVerify.Proofs.fast_float.from_chars.lib.LMB.LmBThm.LmBB.
From OSSVerify.Proofs.fast_float.from_chars.lib.LMB Require Import FxConstGen.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma TM_eq : TM = mk_tbl BSEGS 0x9733c 1169.
Proof. vm_cast_no_check (eq_refl TM). Qed.
Lemma TM_nofp : tbl_nofp TM = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma IMGW_eq : IMGW = mk_imgs_acc IMGR TEmpty.
Proof. vm_cast_no_check (eq_refl IMGW). Qed.
Lemma IMGW_ok : img_ok BSEGS IMGW.
Proof.
  rewrite IMGW_eq.
  apply mk_imgs_acc_ok; [unfold IMGR; repeat constructor; cbn; lia|]. intros p v Hp. rewrite tget_empty in Hp. discriminate.
Qed.
Lemma RET2_ok : Forall (is_ret BSEGS) [0x97da0].
Proof. repeat constructor. exists (Z_to_bv 32 0x00008067). (split; [|split]); vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma sites1 : forall c, xsites (NODES c) = [] /\ xfsites (NODES c) = [] /\
  (forall f, In f (xhandl (NODES c)) -> f = hx_c2r 0x97f9c) /\
  (forall P0' Q', In (P0', Q') (xksites (NODES c)) -> (P0', Q') = (SM5_P0, SM5_Q) \/ (P0', Q') = (MMA_P0, MMA_Q) \/ (P0', Q') = (MMB_P0, MMB_Q)).
Proof.
  intros c. split; [reflexivity|]. split; [reflexivity|]. split.
  - intros f H. cbn in H. repeat (destruct H as [H|H]; [exact (eq_sym H)|]). destruct H.
  - intros P0' Q' H. cbn in H.
    repeat (destruct H as [H|H]; [first [left; exact (eq_sym H) | right; left; exact (eq_sym H) | right; right; exact (eq_sym H)]|]).
    destruct H.
Qed.

Section LMB.
Hypothesis H_SM5 : kfn_ok_fp BSEGS SM5_P0 SM5_Q.
Hypothesis H_MMA : kfn_ok_fp BSEGS MMA_P0 MMA_Q.
Hypothesis H_MMB : kfn_ok_fp BSEGS MMB_P0 MMB_Q.
Hypothesis H_SF5 : kfn_ok_fp BSEGS SF5_P0 SF5_Q.

#[using="H_SM5 H_MMA H_MMB"] Lemma c1_gen : forall c ds,
  (match wstartx TM IMGW (vars_below (s_next (LM_P0 c))) 10 (LM_P0 c) P0RUN (xconst (NODES c) ds) with
   | Some l => forallb (fun X => fin_q (LM_TAIL_Q c) [0x981cc] (s_next (LM_P0 c)) (xs_st X)) l | None => false end) = true ->
  bases_wf (s_next (LM_P0 c)) (s_rgs (LM_P0 c)) = true -> bases_ins (vars_below (s_next (LM_P0 c))) (s_rgs (LM_P0 c)) = true ->
  state_wf (LM_TAIL_Q c) = true ->
  kfrag_ok_fp BSEGS (LM_P0 c) (LM_TAIL_Q c) 0x981cc.
Proof. LiaFast.lf_pins (fun (H_SM5 H_MMA H_MMB : LiaFast.U) => LiaFast.u0).
  intros c ds Hc Hw1 Hw2 HwQ. destruct (sites1 c) as (Hs & Hf & Hh & Hk).
  apply (kfrag_ok_fp_of_wcertx BSEGS (fun _ _ _ => True) TM IMGW 10 P0RUN (xconst (NODES c) ds) (LM_P0 c) (LM_TAIL_Q c) 0x981cc
           ltac:(rewrite TM_eq; apply mk_tbl_ok) IMGW_ok TM_nofp Hc); [| | | | exact Hw1 | exact Hw2 | exact HwQ].
  - intros P0' Q' H. rewrite xconst_xsites, Hs in H. destruct H.
  - intros f H. rewrite xconst_xhandl in H. rewrite (Hh f H). apply hx_c2r_ok_fp.
  - intros P0' Q' H. rewrite xconst_xksites in H. destruct (Hk P0' Q' H) as [E|[E|E]]; injection E as -> ->; assumption.
  - intros P0' Q' pcQ H. rewrite xconst_xfsites, Hf in H. destruct H.
Qed.
#[using="H_SM5 H_MMA H_MMB"] Theorem lmb_c1_16_fp : kfrag_ok_fp BSEGS (LM_P0 16) (LM_TAIL_Q 16) 0x981cc.
Proof. LiaFast.lf_pins (fun (H_SM5 H_MMA H_MMB : LiaFast.U) => LiaFast.u0). apply (c1_gen 16 GD16); [exact LMB_cert16 | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity]. Qed.
#[using="H_SM5 H_MMA H_MMB"] Theorem lmb_c1_0_fp : kfrag_ok_fp BSEGS (LM_P0 0) (LM_TAIL_Q 0) 0x981cc.
Proof. LiaFast.lf_pins (fun (H_SM5 H_MMA H_MMB : LiaFast.U) => LiaFast.u0). apply (c1_gen 0 GD0); [exact LMB_cert0 | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity]. Qed.

#[using="H_SF5"] Lemma c2_gen : forall c,
  (match wstartx TM IMGW (vars_below (s_next (LM_EPI_P0 c))) 10 (LM_EPI_P0 c) P2RUN (NODES2 c) with
   | Some l => forallb (fun X => fin_q (LM_Q c) [0x97da0] (s_next (LM_EPI_P0 c)) (xs_st X)) l | None => false end) = true ->
  bases_wf (s_next (LM_EPI_P0 c)) (s_rgs (LM_EPI_P0 c)) = true -> bases_ins (vars_below (s_next (LM_EPI_P0 c))) (s_rgs (LM_EPI_P0 c)) = true ->
  state_wf (LM_Q c) = true ->
  fn_ok_fp BSEGS (LM_EPI_P0 c) (LM_Q c) [0x97da0].
Proof. LiaFast.lf_pins (fun (H_SF5 : LiaFast.U) => LiaFast.u0).
  intros c Hc Hw1 Hw2 HwQ.
  apply (fn_ok_fp_of_wcertx BSEGS (fun _ _ _ => True) TM IMGW 10 P2RUN (NODES2 c) (LM_EPI_P0 c) (LM_Q c) [0x97da0]
           ltac:(rewrite TM_eq; apply mk_tbl_ok) IMGW_ok TM_nofp Hc); [| | | | exact Hw1 | exact Hw2 | exact HwQ | exact RET2_ok].
  - intros P0' Q' H. destruct H.
  - intros f H. cbn in H. destruct H as [H|[]]. subst f. apply hx_promote_ok_fp.
  - intros P0' Q' H. cbn in H. destruct H as [H|[]]. injection H as <- <-. exact H_SF5.
  - intros P0' Q' pcQ H. destruct H.
Qed.
#[using="H_SF5"] Theorem lmb_c2_16_fp : fn_ok_fp BSEGS (LM_EPI_P0 16) (LM_Q 16) [0x97da0].
Proof. LiaFast.lf_pins (fun (H_SF5 : LiaFast.U) => LiaFast.u0). apply c2_gen; [exact LMB2_cert16 | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity]. Qed.
#[using="H_SF5"] Theorem lmb_c2_0_fp : fn_ok_fp BSEGS (LM_EPI_P0 0) (LM_Q 0) [0x97da0].
Proof. LiaFast.lf_pins (fun (H_SF5 : LiaFast.U) => LiaFast.u0). apply c2_gen; [exact LMB2_cert0 | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity]. Qed.
End LMB.
