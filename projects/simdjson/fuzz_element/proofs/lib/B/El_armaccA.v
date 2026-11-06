(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun Stdio SjModel AtpModel.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit Atp_h_defs.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 RT_iface5 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2
     Sj_num_akit Sj_h_alloc Sj_stage2_iface Atp_fzwA Atp_setcapA Atp_activewA Atp_activeA Atp_defsA Atp_kitA Atp_h_defsA Atp_pidiA Atp_pdtorA
     Pj_lftoi1A Pj_defsA Pj_os_defsA El_defsA El_lf1A El_lf2A El_lf2bA El_phasesA El_frontA El_parsekA El_armkitA Atp_arrlA El_haccA El_h3A El_h6A El_h7A El_h8A El_h10A El_h16A El_h17A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma land_c16_small : forall c, 0 <= c < 64 -> Z.land c 4294967232 = 0.
Proof.
  intros c Hc. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases n 6) as [L|G].
  - replace (Z.testbit 4294967232 n) with false; [apply Bool.andb_false_r|].
    symmetry. change 4294967232 with (67108863 * 2 ^ 6). apply Z.mul_pow2_bits_low. exact L.
  - replace (Z.testbit c n) with false; [reflexivity|]. symmetry. apply Z.bits_above_log2; [lia|].
    assert (Z.log2 c < 6) by (destruct (Z.eq_dec c 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia]). lia.
Qed.

Section ArmAcc.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable PMc : Model -> Prop.

Local Ltac ul := unfold FUZZ_STACK, PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Local Ltac arm_acc a k H G SPEC :=
  intros W Σ K X E sel idx jr jos t ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 t6 F fc m
    FDO MST LK OKE LE WFS SEL IDX AL FRS LPA LVB CRB ARTg MIg STg NEED AM FRM XD AUX SPB POST;
  let NEED16 := fresh "NEED16" in
  assert (NEED16 : lf_lo X + 16 <= lf_S1 X - k) by (clear - NEED; unfold arm_needA in NEED; cbn in NEED; ul);
  pose proof (arm_entry_kit RT AF X E Σ a sel idx jr jos t m k LK OKE LE AL FRS ARTg AM ltac:(lia) NEED16) as (ARTM & SZN & AIM & SZD & SZT & SHBM);
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)];
  destruct X as [usp sp' f lo]; cbn [lf_usp lf_S1 lf_F lf_lo] in *;
  destruct LE as (EDOC & EFD & EKD & ELO & EHI); cbn [lf_usp lf_S1 lf_F lf_lo] in EDOC, EFD, EKD, ELO, EHI;
  pose proof AM as (C16 & C100 & C128 & CE & CO & CS & AI & LIB & NL & IOS); cbn [lf_usp lf_S1 lf_F lf_lo] in C16, C100, C128, CE, CO, CS;
  let SZS := fresh "SZS" in
  assert (SZS : forall m', munch [(sp' - k, sp')] m m' -> wmono bsegs m m' -> shz m' (ae_SBUF E) (ae_NS E))
    by (intros m' MU WM; destruct (Atp_defsA.ok_sbuf E OKE) as (Sb16 & NS8 & _ & _ & _); destruct AL as (_ & ALS & _);
        pose proof (shz_live RT AF Σ m' (ae_SBUF E) (ae_NS E) (ARTM m' MU WM) ALS ltac:(clear - Sb16; Z.div_mod_to_equations; lia)) as XS;
        replace (8 * (ae_NS E / 8)) with (ae_NS E) in XS by (clear - NS8; Z.div_mod_to_equations; lia); exact XS);
  unfold lf_st; cbn [lf_usp lf_S1 lf_F lf_lo el_arm_pcA Z.leb Z.ltb andb nth Z.to_nat Pos.to_nat Pos.iter_op Nat.add EL_ARMS_A];
  apply (aevt_evt RT AF PMc MST);

  zstep; zstep;
  eapply evt_cut;
    [eapply (SPEC E OKE _ gp t0 t1 t2 (wz usp) (wz sp') a1 a2 a3 a4 a5 a6 a7 (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) s6 s7 (wz (ae_PTR E)) (wz 0) (wz (zlength (ae_p1 E))) (wz (f + 120))
            t3 t4 t5 t6 F fc m sp' (f + 208));
     [rewrite ELO; exact STg| rewrite ELO; clear - NEED16; lia| rewrite EHI; clear - SPR; lia| clear - SPA'; Z.div_mod_to_equations; lia| exact MIg| exact FRM
     | exact CE| clear - FPOS; lia| left; clear - FLO LOR SPR NEED16; ul| clear - FLO LLO LOR SPR SPT; ul| exact AIM| exact SHBM| exact SZN| exact SZD| exact SZT| exact SZS]|];
  cbv beta; intros ms' (u0 & u1 & u2 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F1 & fc1 & m1 & c0 & c1 & -> & FRM1 & MU1 & WM1 & MI1 & ST1 & HG);
  rewrite ret_pc_even by (clear; lia); rewrite ELO in ST1.

Local Ltac tail_plain a k :=
  zstep; apply evt_done;
  lazymatch goal with POST : forall w : bool, _ |- aevt _ _ ?Σ _ (MS _ ?F1 _ ?fc1 _ ?m1 _) =>
    lazymatch goal with MU1 : munch _ ?m m1, WM1 : wmono bsegs ?m m1, MI1 : mem_inv bsegs m1, ST1 : stk bsegs m1 _ _, FRM1 : frm0 fc1,
                         LK : lfA_ok _, OKE : aenvA_ok ?E, AL : a_live _ _ ?E, FRS : rt_frames _ _ = _, ARTg : ART _ _ ?m, AM : arm_memA _ ?E _ _ _ _ _ _ ?m,
                         NEED16 : _ + 16 <= _ - k, EDOC : ae_DOC ?E = _, EFD : ae_fD ?E = _, EKD : ae_kD ?E = _, ELO : ae_lo ?E = _, EHI : ae_hi ?E = _ |- _ =>
      apply (POST false (rt_credit _ Σ) Σ m1 fc1 F1);
      exact (arm_post_below RT AF _ a _ E Σ _ _ _ _ _ m m1 fc1 k LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ARTg AM ltac:(lia) NEED16
               MU1 WM1 MI1 ST1 FRM1 eq_refl)
    end end.

Theorem arm3_okA : forall W, arm_cpsA RT PMc W 3.
Proof using AF. arm_acc 3 64 0xb2fac G_any (fun E OKE => acc_stmt_SB E _ _ _ (getcstr_specB E OKE)). tail_plain 3 64. Qed.
Theorem arm4_okA : forall W, arm_cpsA RT PMc W 4.
Proof using AF. arm_acc 4 64 0xb3124 G_any getslen_specB. tail_plain 4 64. Qed.
Theorem arm6_okA : forall W, arm_cpsA RT PMc W 6.
Proof using AF. arm_acc 6 64 0xb3624 G_int (fun E OKE => acc_stmt_SB E _ _ _ (gi64_specB E OKE)). tail_plain 6 64. Qed.
Theorem arm7_okA : forall W, arm_cpsA RT PMc W 7.
Proof using AF. arm_acc 7 64 0xb3800 G_int (fun E OKE => acc_stmt_SB E _ _ _ (gu64_specB E OKE)). tail_plain 7 64. Qed.
Theorem arm8_okA : forall W, arm_cpsA RT PMc W 8.
Proof using AF. arm_acc 8 64 0xb39dc G_dbl (fun E OKE => acc_stmt_SB E _ _ _ (gdbl_specB E OKE)). tail_plain 8 64. Qed.
Theorem arm9_okA : forall W, arm_cpsA RT PMc W 9.
Proof using AF. arm_acc 9 64 0xb3c68 G_any (fun E OKE => acc_stmt_SB E _ _ _ (getbool_specB E OKE)). tail_plain 9 64. Qed.
Theorem arm10_okA : forall W, arm_cpsA RT PMc W 10.
Proof using AF. arm_acc 10 32 0xb3da0 G_any (fun E OKE => acc_stmt_SB E _ _ _ (isarr_specB E OKE)). tail_plain 10 32. Qed.
Theorem arm11_okA : forall W, arm_cpsA RT PMc W 11.
Proof using AF. arm_acc 11 32 0xb3e34 G_any (fun E OKE => acc_stmt_SB E _ _ _ (isobj_specB E OKE)). tail_plain 11 32. Qed.
Theorem arm16_okA : forall W, arm_cpsA RT PMc W 16.
Proof using AF. arm_acc 16 96 0xb3ec8 G_any (fun E OKE => acc_stmt_SB E _ _ _ (isnum_specB E OKE)). tail_plain 16 96. Qed.
Theorem arm17_okA : forall W, arm_cpsA RT PMc W 17.
Proof using AF. arm_acc 17 64 0xb3f40 G_any (fun E OKE => acc_stmt_SB E _ _ _ (isbool_specB E OKE)). tail_plain 17 64. Qed.
Theorem arm18_okA : forall W, arm_cpsA RT PMc W 18.
Proof using AF. arm_acc 18 32 0xb4068 G_any (fun E OKE => acc_stmt_SB E _ _ _ (isnull_specB E OKE)). tail_plain 18 32. Qed.

Local Ltac tail_and c1 HG MU1 C16 :=
  let C16' := fresh "C16'" in let HG0 := fresh "HG0" in let HG1 := fresh "HG1" in
  unfold G_int in HG; destruct HG as [HG0 HG1]; unfold EL_C16_A in C16;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    lazymatch type of C16 with rw_cells _ ?m ?a ?cs => assert (C16' : rw_cells bsegs m1 a cs)
      by (eapply rw_cells_agree_nw; [exact C16|]; apply (agree_of_munch _ _ _ _ MU1); intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; lia) end end;
  change (2 ^ 32 - 64) with 4294967232 in C16';
  step; astep; rewrite (land_c16_small c1) by (clear - HG1; lia);
  step; if_false.

Theorem arm13_okA : forall W, arm_cpsA RT PMc W 13.
Proof using AF.
  arm_acc 13 64 0xb3624 G_int (fun E OKE => acc_stmt_SB E _ _ _ (gi64_specB E OKE)).

  zstep. tail_and c1 HG MU1 C16. tail_plain 13 64.
Qed.

Theorem arm14_okA : forall W, arm_cpsA RT PMc W 14.
Proof using AF.
  arm_acc 14 64 0xb3800 G_int (fun E OKE => acc_stmt_SB E _ _ _ (gu64_specB E OKE)).
  tail_and c1 HG MU1 C16. tail_plain 14 64.
Qed.

Theorem arm15_okA : forall W, arm_cpsA RT PMc W 15.
Proof using AF.
  arm_acc 15 64 0xb39dc G_dbl (fun E OKE => acc_stmt_SB E _ _ _ (gdbl_specB E OKE)).

  unfold G_dbl in HG. destruct HG as [HG0 HG1].
  astep. astep. step. if_cases Kc; zify_cond Kc; [exfalso; rewrite ?a_sx32_small, ?a_u64_small in Kc by lia; clear - Kc HG0; lia| clear Kc].
  tail_plain 15 64.
Qed.
End ArmAcc.
