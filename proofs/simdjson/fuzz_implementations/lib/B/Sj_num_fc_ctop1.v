(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber SjNumU SjNumN.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit I_lkit Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_abig Sj_num_acall Sj_num_acall2 Sj_num_aframe Sj_num_lits Sj_num_bkit Sj_num_bdefs Sj_num_lm_kit
  Sj_num_fc_stmt Sj_num_fc_defs Sj_num_fc_rel Sj_num_fc_pro Sj_num_fc_pro2 Sj_num_fc_tail Sj_num_fc_k14 Sj_num_fc_dc Sj_num_fc_top14 Sj_num_fc_tkit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Ltac fcb_at_simpl :=
  repeat match goal with
  | H : context [fcb_W (fcb_at ?E0 ?m0)] |- _ => change (fcb_W (fcb_at E0 m0)) with (fcb_W E0) in H
  | |- context [fcb_W (fcb_at ?E0 ?m0)] => change (fcb_W (fcb_at E0 m0)) with (fcb_W E0)
  | H : context [fcb_saved (fcb_at ?E0 ?m0)] |- _ => change (fcb_saved (fcb_at E0 m0)) with (fcb_saved E0) in H
  | |- context [fcb_saved (fcb_at ?E0 ?m0)] => change (fcb_saved (fcb_at E0 m0)) with (fcb_saved E0)
  end;
  cbn [fcb_at q_ra q_sp q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_A q_FIRST q_LAST q_OUT q_lo q_spq q_f q_txt q_m0] in *.

Ltac fc_close_at :=
  unfold FCINV; fcb_at_simpl;
  split; [unfold fcb_spill; fcb_at_simpl; eassumption|]; split; [do 4 eexists; unfold fcb_pns; eassumption|]; split; [lia|]; split; [lia|];
  split; [fcp_forget_obj|]; split; [fcp_forget_obj|];
  split; [first [ intros BGF; discriminate BGF | intros _; fcp_forget_obj ]|];
  split; [eassumption|]; split; [eexists; eassumption|];
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption.

Section FCTOP.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RTF : rt_contracts_f RT.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Hypothesis HPDC : pdcb_stmt RT PMc.
  Hypothesis HNDC : ndcb_stmt RT PMc.

  Variables (Σ0 : rts RT) (K : config -> Prop).

  Variable E : fcbenv.
  Variables (p n : Z) (me : mem).
  Notation SP := (q_SP E).
  Notation S := (q_S E).
  Notation f := (q_f E).
  Notation lo := (q_lo E).
  Notation spq := (q_spq E).
  Notation OUT := (q_OUT E).
  Notation A := (q_A E).
  Notation FIRST := (q_FIRST E).
  Notation LAST := (q_LAST E).
  Notation TL := (q_TL E).
  Hypothesis OK : fcb_ok E.
  Hypothesis ETP : q_tp E = Z_to_bv 64 B_TP.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis LOR : (rt_sp0 RT Σ0 - STACK_WIN <= lo)%Z.
  Hypothesis FRL : (length (rt_frames RT Σ0) + FFB_FRAMES <= FRAMES_MAX)%nat.
  Hypothesis CRD : (FFB_CREDIT <= rt_credit RT Σ0)%Z.

  Hypothesis PIN : In (p, n) (rt_live RT Σ0).
  Hypothesis PCH : (p mod 8 = 0 /\ p <= A /\ LAST + 8 <= p + n /\ A + TL <= p + n)%Z.

  Hypothesis HK : forall (Σ' : rts RT) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' (v : word), frm0 fc' ->
     rt_after RT Σ' SP lo me m' -> rt_pres_ex (rt_live RT Σ0) (rt_frames RT Σ0) SP OUT 8 me m' ->
     rw_cells bsegs m' OUT [C8 v] ->
     rt_frames RT Σ' = rt_frames RT Σ0 -> rt_live RT Σ' = rt_live RT Σ0 -> rt_sp0 RT Σ' = rt_sp0 RT Σ0 ->
     (rt_credit RT Σ0 - FFB_CREDIT <= rt_credit RT Σ')%Z ->
     aevt RT PMc Σ' K (MS (mkR (q_ra E) (q_sp E) (q_gp E) (q_tp E) t0' t1' t2' (q_s0 E) (q_s1 E) a0' a1' a2' a3' a4' a5' a6' a7'
                               (q_s2 E) (q_s3 E) (q_s4 E) (q_s5 E) (q_s6 E) (q_s7 E) (q_s8 E) (q_s9 E) (q_s10 E) (q_s11 E) t3' t4' t5' t6')
                          F' (ret_pc (q_ra E)) fc' None m' (seg_rom bsegs)).
  Collection TOPH := AF RTF FDO MST HPDC HNDC OK ETP SP16 LOR FRL CRD PIN PCH HK.

  Notation MREL := (fc_mrel RT Σ0 E me).
  Notation PARK := (fc_park E).
  Notation W := (fcb_W E).
  Notation QΣ Σ := (fun ms' => aevt RT PMc Σ K ms').
  Notation EB mb := (fcb_at E mb).

  Definition fc_srel (Σ : rts RT) (used : Z) : Prop :=
    rt_frames RT Σ = (f, 4%nat) :: rt_frames RT Σ0 /\ rt_live RT Σ = rt_live RT Σ0 /\ rt_sp0 RT Σ = rt_sp0 RT Σ0
    /\ (rt_credit RT Σ0 - 1 - used <= rt_credit RT Σ)%Z.

  Definition fc_ctx (Σ : rts RT) (used : Z) (fc : bv 32) (mb : mem) : Prop :=
    fc_srel Σ used /\ (0 <= used <= 9)%Z /\ frm0 fc /\ ART RT Σ mb /\ MREL mb /\ PARK mb.

  Notation TK L Σ SR := (L RT AF Σ0 Σ E OK LOR (proj1 SR) (proj1 (proj2 SR)) (proj1 (proj2 (proj2 SR)))) (only parsing).
  Notation TKm L Σ SR := (L RT AF Σ0 Σ E me OK LOR (proj1 SR) (proj1 (proj2 SR)) (proj1 (proj2 (proj2 SR)))) (only parsing).

  Lemma top_okb : forall mb, fcb_ok (EB mb).
  Proof using TOPH. intros mb. exact (fcb_ok_at E mb OK). Qed.
  Lemma top_lor1 : forall Σ used, fc_srel Σ used -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z.
  Proof using TOPH. intros Σ used (_ & _ & ES & _). rewrite ES. exact LOR. Qed.
  Lemma top_inF : forall Σ used, fc_srel Σ used -> In (f, 4%nat) (rt_frames RT Σ).
  Proof using TOPH. intros Σ used (EF & _). rewrite EF. left. reflexivity. Qed.
  Lemma top_inP : forall Σ used, fc_srel Σ used -> In (p, n) (rt_live RT Σ).
  Proof using TOPH. intros Σ used (_ & EL & _). rewrite EL. exact PIN. Qed.
  Lemma top_fpok : forall Σ used, fc_srel Σ used -> fp_ok RT Σ lo W.
  Proof using TOPH. intros Σ used SR. exact (TK tk_fpok Σ SR _ (TK tk_wf_W Σ SR)). Qed.
  Lemma top_art : forall Σ used W' (mb mm : mem), fc_srel Σ used -> tk_wf E W' -> ART RT Σ mb -> munch W' mb mm -> wmono bsegs mb mm -> ART RT Σ mm.
  Proof using TOPH. intros Σ used W' mb mm SR HW HA MU WM. exact (art_of_munch RT AF Σ mb mm lo W' HA (top_lor1 Σ used SR) (TK tk_fpok Σ SR W' HW) MU WM). Qed.
  Lemma top_mrel : forall Σ used W' (mb mm : mem), fc_srel Σ used -> tk_wf E W' -> ART RT Σ mb -> MREL mb -> munch W' mb mm -> wmono bsegs mb mm -> MREL mm.
  Proof using TOPH. intros Σ used W' mb mm SR. exact (TKm fc_mrel_munch Σ SR W' mb mm). Qed.

  Lemma top_ctx_step : forall Σ used fc (mb mm : mem), fc_ctx Σ used fc mb -> munch W mb mm -> wmono bsegs mb mm -> fc_ctx Σ used fc mm.
  Proof using TOPH.
    intros Σ used fc mb mm (SR & HU & FRM & HA & MR & PK) MU WM. split; [exact SR|]. split; [exact HU|]. split; [exact FRM|].
    split; [exact (top_art Σ used _ mb mm SR (TK tk_wf_W Σ SR) HA MU WM)|].
    split; [exact (top_mrel Σ used _ mb mm SR (TK tk_wf_W Σ SR) HA MR MU WM)|].
    exact (TK fc_park_munch Σ SR _ mb mm (TK tk_wfp_W Σ SR) PK MU WM).
  Qed.
  Lemma top_cok : forall Σ used (mm : mem), fc_srel Σ used -> stk bsegs mm lo spq -> call_ok RT Σ mm (Z_to_bv 64 spq) lo.
  Proof using TOPH.
    intros Σ used mm SR ST. pose proof (stk_lo_nonneg bsegs _ _ _ ST) as LO0. pose proof OK as OK'. fcb_env OK'. destruct SPQ as [SPQ1 SPQ2].
    unfold call_ok. rewrite unsigned_lit by lia. split; [exact ST|]. split; [exact (top_lor1 Σ used SR)|]. unfold RT_STACK, USTACK_TOP.
    split; [lia|]. split; [lia| Z.div_mod_to_equations; lia].
  Qed.

  Lemma top_prov : forall Σ used (mb : mem), fc_srel Σ used -> ART RT Σ mb -> fcb_prov (EB mb).
  Proof using TOPH.
    intros Σ used mb SR HA. pose proof (top_lor1 Σ used SR) as L1. pose proof (top_fpok Σ used SR) as FPK.
    pose proof OK as OK'. fcb_env OK'. destruct SPQ as [SPQ1 SPQ2]. destruct OUTR as (O8 & O1 & O2). destruct PCH as (P8 & PA & PL & PT). destruct FLR as (R1 & R2 & R3).
    pose proof (af_sp0_range RT AF Σ mb HA) as SP0R. unfold STACK_WIN, USTACK_TOP in *.
    unfold fcb_prov. fcb_at_simpl.
    assert (LIT : forall a k, In (a, k) ACC_LITS -> (a mod 8 = 0)%Z -> (0 <= a)%Z -> (k mod 8 = 0)%Z -> forall m', munch W mb m' -> wmono bsegs mb m' -> shz m' a k).
    { intros a k Hin A8 A0 K8 m' MU WM. pose proof (art_of_munch RT AF Σ mb m' lo W HA L1 FPK MU WM) as HA'.
      replace k with (8 * (k / 8))%Z by (Z.div_mod_to_equations; lia). apply shz_of_acc; [| exact A8 | exact A0]. exact (acc_lit RT AF Σ m' _ _ HA' Hin). }
    split; [| split; [| split; [| split; [| split]]]].
    - intros m' MU WM. pose proof (shzp_live RT AF Σ mb lo W p n HA L1 FPK (top_inP Σ used SR) P8 m' MU WM) as H.
      eapply shz_sub; [exact H | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia].
    - intros m' MU WM. exact (shzp_stack RT AF Σ mb lo W OUT 8 HA L1 FPK ltac:(unfold STACK_WIN; lia) ltac:(unfold USTACK_TOP; lia) O8 m' MU WM).
    - intros m' MU WM. exact (shzp_stack RT AF Σ mb lo W spq 152 HA L1 FPK ltac:(unfold STACK_WIN; lia) ltac:(unfold USTACK_TOP; lia) ltac:(Z.div_mod_to_equations; lia) m' MU WM).
    - apply LIT; [unfold ACC_LITS; repeat (first [left; reflexivity | right]) | reflexivity | lia | reflexivity].
    - apply LIT; [unfold ACC_LITS; repeat (first [left; reflexivity | right]) | reflexivity | lia | reflexivity].
    - apply LIT; [unfold ACC_LITS; repeat (first [left; reflexivity | right]) | reflexivity | lia | reflexivity].
  Qed.
  Lemma top_bcp : forall Σ (mm : mem), ART RT Σ mm -> b_consts mm.
  Proof using TOPH. intros Σ mm HA. exact (b_consts_of mm (af_client_consts RT AF Σ mm HA)). Qed.
End FCTOP.
