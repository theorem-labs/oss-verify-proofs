(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun Stdio SjModel AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit Atp_h_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface3 RT_iface5. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_num_akit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_alloc Sj_stage2_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Atp_setcapA Atp_activewA Atp_activeA Atp_defsA Atp_kitA Atp_h_defsA Atp_pidiA Atp_pdtorA Pj_lftoi1A Pj_defsA Pj_os_defsA El_defsA El_lf1A El_lf2A El_lf2bA El_phasesA El_frontA El_parsekA El_armkitA Atp_arrlA El_haccA El_h8A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section ArmAcc.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable PMc : Model -> Prop.

Local Ltac ul := unfold FUZZ_STACK, PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Local Ltac arm_acc a k H G SPEC :=
  intros W Σ K X E sel idx jr jos t ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 F fc m
    FDO MST LK OKE LE WFS SEL IDX AL FRS LPA LVB CRB ARTg MIg STg NEED AM FRM XD AUX SPB POST;
  let NEED16 := fresh "NEED16" in
  assert (NEED16 : lf_lo X + 16 <= lf_S1 X - k) by (clear - NEED; unfold arm_needA in NEED; cbn in NEED; ul);
  pose proof (arm_entry_kit RT AF X E Σ a sel idx jr jos t m k LK OKE LE AL FRS ARTg AM ltac:(lia) NEED16) as (ARTM & SZN & AIM & SZD & SZT & SHBM);
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)];
  destruct X as [usp sp' f lo]; cbn [lf_usp lf_S1 lf_F lf_lo] in *;
  destruct LE as (EDOC & EFD & EKD & ELO & EHI); cbn [lf_usp lf_S1 lf_F lf_lo] in EDOC, EFD, EKD, ELO, EHI;
  pose proof AM as (C16 & C100 & C128 & CE & CO & CS & AI & LIB & NL & IOS); cbn [lf_usp lf_S1 lf_F lf_lo] in C16, C100, C128, CE, CO, CS;
  let SZS := fresh "SZS" in
  assert (SZS : forall m', munch [(sp' - k, sp')] m m' -> wmono asegs m m' -> shz m' (ae_SBUF E) (ae_NS E))
    by (intros m' MU WM; destruct (Atp_defsA.ok_sbuf E OKE) as (Sb16 & NS8 & _ & _ & _); destruct AL as (_ & ALS & _);
        pose proof (shz_live RT AF Σ m' (ae_SBUF E) (ae_NS E) (ARTM m' MU WM) ALS ltac:(clear - Sb16; Z.div_mod_to_equations; lia)) as XS;
        replace (8 * (ae_NS E / 8)) with (ae_NS E) in XS by (clear - NS8; Z.div_mod_to_equations; lia); exact XS);
  unfold lf_st; cbn [lf_usp lf_S1 lf_F lf_lo el_arm_pcA Z.leb Z.ltb andb nth Z.to_nat Pos.to_nat Pos.iter_op Nat.add EL_ARMS_A];
  apply (aevt_evt RT AF PMc MST);

  zstep; zstep;
  eapply evt_cut;
    [eapply (SPEC E OKE _ gp t0 t1 t2 (wz usp) (wz sp') a1 a2 a3 a4 a5 a6 a7 (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) (wz (f + 208)) (wz 0) (wz f) s9 s10 (wz (f + 120))
            t3 t4 t5 t6 F fc m sp' (f + 208));
     [rewrite ELO; exact STg| rewrite ELO; clear - NEED16; lia| rewrite EHI; clear - SPR; lia| clear - SPA'; Z.div_mod_to_equations; lia| exact MIg| exact FRM
     | exact CE| clear - FPOS; lia| left; clear - FLO LOR SPR NEED16; ul| clear - FLO LLO LOR SPR SPT; ul| exact AIM| exact SHBM| exact SZN| exact SZD| exact SZT| exact SZS]|];
  cbv beta; intros ms' (u0 & u1 & u2 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F1 & fc1 & m1 & c0 & c1 & -> & FRM1 & MU1 & WM1 & MI1 & ST1 & HG);
  rewrite ret_pc_even by (clear; lia); rewrite ELO in ST1.

Local Ltac tail_plain a k :=
  zstep; apply evt_done;
  lazymatch goal with POST : forall w : bool, _ |- aevt _ _ ?Σ _ (MS _ ?F1 _ ?fc1 _ ?m1 _) =>
    lazymatch goal with MU1 : munch _ ?m m1, WM1 : wmono asegs ?m m1, MI1 : mem_inv asegs m1, ST1 : stk asegs m1 _ _, FRM1 : frm0 fc1,
                         LK : lfA_ok _, OKE : aenvA_ok ?E, AL : a_live _ _ ?E, FRS : rt_frames _ _ = _, ARTg : ART _ _ ?m, AM : arm_memA _ ?E _ _ _ _ _ _ ?m,
                         NEED16 : _ + 16 <= _ - k, EDOC : ae_DOC ?E = _, EFD : ae_fD ?E = _, EKD : ae_kD ?E = _, ELO : ae_lo ?E = _, EHI : ae_hi ?E = _ |- _ =>
      apply (POST false (rt_credit _ Σ) Σ m1 fc1 F1);
      exact (arm_post_below RT AF _ a _ E Σ _ _ _ _ _ m m1 fc1 k LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ARTg AM ltac:(lia) NEED16
               MU1 WM1 MI1 ST1 FRM1 eq_refl)
    end end.

Theorem arm3_okA : forall W, arm_cpsA RT PMc W 3.
Proof using AF.
  intros W. exact (arm_exit_okA RT PMc W 3 eq_refl (fun _ _ _ => eq_refl)).
Qed.
Theorem arm4_okA : forall W, arm_cpsA RT PMc W 4.
Proof using AF.
  intros W. exact (arm_exit_okA RT PMc W 4 eq_refl (fun _ _ _ => eq_refl)).
Qed.
Theorem arm6_okA : forall W, arm_cpsA RT PMc W 6.
Proof using AF.
  intros W. exact (arm_exit_okA RT PMc W 6 eq_refl (fun _ _ _ => eq_refl)).
Qed.
Theorem arm7_okA : forall W, arm_cpsA RT PMc W 7.
Proof using AF.
  intros W. exact (arm_exit_okA RT PMc W 7 eq_refl (fun _ _ _ => eq_refl)).
Qed.
Theorem arm8_okA : forall W, arm_cpsA RT PMc W 8.
Proof using AF. arm_acc 8 16 0xb2524 G_dbl (fun E OKE => acc_stmt_SB E _ _ _ (gdbl_specB E OKE)). tail_plain 8 16. Qed.
Theorem arm9_okA : forall W, arm_cpsA RT PMc W 9.
Proof using AF.
  intros W. exact (arm_exit_okA RT PMc W 9 eq_refl (fun _ _ _ => eq_refl)).
Qed.
Theorem arm10_okA : forall W, arm_cpsA RT PMc W 10.
Proof using AF.
  intros W. exact (arm_exit_okA RT PMc W 10 eq_refl (fun _ _ _ => eq_refl)).
Qed.
Theorem arm11_okA : forall W, arm_cpsA RT PMc W 11.
Proof using AF.
  intros W. exact (arm_exit_okA RT PMc W 11 eq_refl (fun _ _ _ => eq_refl)).
Qed.
Theorem arm16_okA : forall W, arm_cpsA RT PMc W 16.
Proof using AF.
  intros W. exact (arm_exit_okA RT PMc W 16 eq_refl (fun _ _ _ => eq_refl)).
Qed.
Theorem arm17_okA : forall W, arm_cpsA RT PMc W 17.
Proof using AF.
  intros W. exact (arm_exit_okA RT PMc W 17 eq_refl (fun _ _ _ => eq_refl)).
Qed.
Theorem arm18_okA : forall W, arm_cpsA RT PMc W 18.
Proof using AF.
  intros W. exact (arm_exit_okA RT PMc W 18 eq_refl (fun _ _ _ => eq_refl)).
Qed.

Theorem arm13_okA : forall W, arm_cpsA RT PMc W 13.
Proof using AF.
  intros W. exact (arm_exit_okA RT PMc W 13 eq_refl (fun _ _ _ => eq_refl)).
Qed.

Theorem arm14_okA : forall W, arm_cpsA RT PMc W 14.
Proof using AF.
  intros W. exact (arm_exit_okA RT PMc W 14 eq_refl (fun _ _ _ => eq_refl)).
Qed.

Theorem arm15_okA : forall W, arm_cpsA RT PMc W 15.
Proof using AF.
  intros W. exact (arm_exit_okA RT PMc W 15 eq_refl (fun _ _ _ => eq_refl)).
Qed.
End ArmAcc.
