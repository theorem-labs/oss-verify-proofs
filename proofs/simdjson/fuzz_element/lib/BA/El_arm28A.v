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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Atp_h_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface3 RT_iface5. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_num_akit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_alloc Sj_stage2_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Atp_setcapA Atp_activewA Atp_activeA Atp_defsA Atp_kitA Atp_arrlA Atp_arratA Atp_h_defsA Atp_pidiA Atp_pdtorA Pj_rtkA Pj_lftoi1A Pj_defsA Pj_os_defsA El_defsA El_lf1A El_lf2A El_lf2bA El_phasesA El_frontA El_parsekA El_armkitA El_callsA El_arm28wA El_atixA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section Arm28.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.

Local Ltac ul := unfold FUZZ_STACK, PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Theorem arm28_okA : forall W, arm_cpsA RT PMc W 28.
Proof using AF RC.
  intros W Σ K X E sel idx jr jos t ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 F fc m
    FDO MST LK OKE LE WFS SEL IDX AL FRS LPA LVB CRB ARTg MIg STg NEED AM FRM XD AUX SPB POST.
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  destruct LE as (EDOC & EFD & EKD & ELO & EHI). cbn [lf_usp lf_S1 lf_F lf_lo] in EDOC, EFD, EKD, ELO, EHI.
  pose proof AM as (C24 & C124 & C96 & CE & CO & CS & AI & LIB & NL & IOS). cbn [lf_usp lf_S1 lf_F lf_lo] in C24, C124, C96, CE, CO, CS.
  pose proof AL as (ALT & ALS & ALP & ALF & WLO).
  change (el_arm_pcA 28) with 0xb1c44. unfold lf_st. cbn [lf_usp lf_S1 lf_F lf_lo].
  assert (EU : bv_unsigned (wz sp') = sp') by (apply unsigned_lit; ul).
  assert (FLO64 : f + 1024 <= sp' - 80) by (clear - FLO LOR SPR; ul).
  assert (SLO : shad f + 128 <= sp' - 80) by (clear - SHT LOR SPR; ul).
  assert (NEED' : lo + EL_CALL_NEED_A <= sp')
    by (clear - NEED; unfold arm_needA in NEED; cbn [Z.eqb Pos.eqb orb] in NEED; unfold EL_CALL_NEED_A, RT_STACK, EL_DUMP_STACK_A, EL_THROW_STACK_A, ATP_ROOT_STACK_A in *; lia).
  assert (STAT : forall x, client_static x -> x < sp' - 80) by (intros x Hx; pose proof (client_static_range _ Hx); clear - H LLO LOR SPR; ul).

  pose proof (ael_root_elem E OKE) as [EL NR].
  assert (PRE : el_callpreA RT E Σ m sp' (sp' + 96) (f + 208) 1 jr).
  { unfold el_callpreA. rewrite ELO, EHI.
    split; [exact CE|]. split; [clear - FPOS; lia|]. split; [clear - FLO; lia|]. split; [clear - F64; Z.div_mod_to_equations; lia|].
    split; [apply (el_elem_fobj RT Σ m f 0 0 (-8) t); [exact CS| exact FRS| exact FPOS| exact F64]|].
    split; [exact C96|]. split; [clear; lia|]. split; [clear - SPR; lia|]. split; [clear - SPA'; Z.div_mod_to_equations; lia|].
    split; [exact ARTg|]. split; [exact MIg|]. split; [exact STg|]. split; [exact NEED'|]. clear - SPA'; Z.div_mod_to_equations; lia. }

  assert (FIN : forall (Σ' : rts RT) (m' : mem) (fc' : bv 32) (F' : bvmap 5 word) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (jr' : list byte),
    ART RT Σ' m' -> mem_inv asegs m' -> stk asegs m' lo sp' -> frm0 fc' ->
    rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
    rt_credit RT Σ - 0 <= rt_credit RT Σ' ->
    (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) sp' (bv_unsigned a) -> ~ (sp' + 96 <= bv_unsigned a < sp' + 120) -> m' a = m a) ->
    rw_cells asegs m' (sp' + 96) [CB 24 jr'] ->
    aevt RT PMc Σ' K (MS (mkR (wz 0xb1c54) (wz sp') gp (wz TPV) t0' t1' t2' (wz usp) (wz sp') a0' a1' a2' a3' a4' a5' a6' a7'
                           (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) (wz (f + 208)) (wz 0) (wz f) s9 s10 (wz (f + 120)) t3' t4' t5' t6')
                      F' (ret_pc (wz 0xb1c54)) fc' None m' (seg_rom asegs))).
  { intros Σ' m' fc' F' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' jr' ART' MI' ST' FRM' LV' FRS' SP' CR' AGm OUT'.
    rewrite (ret_pc_even 0xb1c54) by lia. apply (aevt_evt RT AF PMc MST). zstep. apply evt_done.
    assert (AG : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x /\ ~ (sp' + 96 <= x < sp' + 120)) -> agree_on P m m').
    { intros P HP a Ha. destruct (HP _ Ha) as [H N]. exact (AGm a H N). }
    assert (INS : forall x, sp' <= x < usp -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x) by (intros x Hx; left; clear - Hx SPT; ul).
    assert (INF : forall x, f <= x < f + 1016 -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x).
    { intros x Hx. right; right; right; left. exists f, 4%nat. rewrite FRS. split; [left; reflexivity| change (fs_size 4) with 1024; lia]. }
    assert (INSH : forall x, shad f <= x < shad f + 128 -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x).
    { intros x Hx. right; right; right; right. exists f, 4%nat. rewrite FRS. split; [left; reflexivity| change (fs_size 4) with 1024; unfold shad in *; Z.div_mod_to_equations; lia]. }
    apply (POST false (rt_credit RT Σ') Σ' m' fc' F'). unfold arm_postA, artxA. cbn [lf_usp lf_S1 lf_F lf_lo].
    split; [split; [exact ART'| reflexivity]|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact FRM'|].
    split; [exact LV'|]. split; [exact FRS'|]. split; [exact SP'|].
    split; [clear - CR'; unfold arm_costA; cbn [Z.eqb Pos.eqb orb]; lia|].
    split; [intros a Ha Ho; apply (AGm a Ha); unfold arm_WA in Ho; cbn [outside app lf_usp lf_S1 lf_F lf_lo] in Ho; clear - Ho; lia|].
    split; [| intros X; discriminate X].
    exists jr', jos. unfold arm_memA. cbn [lf_usp lf_S1 lf_F lf_lo].
    split; [eapply rw_cells_agree_nw; [exact C24|]; apply AG; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [apply INS; lia| lia]|].
    split; [eapply rw_cells_agree_nw; [exact C124|]; apply AG; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [apply INS; lia| lia]|].
    split; [exact OUT'|].
    split; [eapply rw_cells_agree_nw; [exact CE|]; apply AG; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [apply INF; lia| lia]|].
    split; [eapply rw_cells_agree_nw; [exact CO|]; apply AG; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [apply INF; lia| lia]|].
    split; [eapply rw_cells_agree_nw; [exact CS|]; apply AG; intros x Hx; unfold el_shadow_armA in Hx; rewrite el_shadowA_size in Hx; split; [apply INSH; lia| clear - Hx SLO; lia]|].
    split; [apply (AINV_A_agree E m m' AI); apply AG; intros x Hx; split; [exact (ainv_rng_aclient RT Σ E sp' x AL OKE Hx)| pose proof (ainv_rng_lo E x OKE Hx); clear - H ELO LOR SPR; ul]|].
    split; [apply (el_libA_agree m m' LIB); apply AG; intros x Hx; pose proof (el_lib_rng_static x Hx) as [CSx _]; split; [right; left; exact CSx| pose proof (STAT _ CSx); lia]|].
    split; [apply (libc_nl_agree m m' NL); apply AG; intros x Hx; pose proof (libc_nl_static _ Hx) as CSx; split; [right; left; exact CSx| pose proof (STAT _ CSx); lia]|].
    destruct IOS as (g & G1 & G2). exists g. split; [exact (proj1 (af_got_lib RT AF Σ' m' ART'))|]. apply (ro_cells_agree asegs m m' _ _ G2). apply AG. intros x Hx.
    cbn [cells_size csize Nat.add] in Hx. split; [right; left; apply client_static_intro; lia| clear - Hx LLO LOR SPR; ul]. }

  apply (aevt_evt RT AF PMc MST).
  assert (EQ : bv_unsigned (wz sp') = sp') by exact EU.
  zstep. zstep. step. zstep. apply evt_done. change TPV_A with TPV.
  eapply (aevt_rt RT PMc Σ K _ _
           (el_atixA RT AF RC E OKE Σ PMc TAPE_MAX_DEPTH 1 (ae_n E - 1) idx sp' (sp' + 96) (f + 208)
              (wz 0xb1c54) gp t0 t1 t2 (wz usp) (wz sp') a3 a4 a5 a6 a7 (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) (wz (f + 208)) (wz 0) (wz f) s9 s10 (wz (f + 120)) t3 t4 t5 t6
              F fc m jr FDO MST AL AI EL ltac:(clear; lia) ltac:(clear; lia) IDX PRE FRM)); [exact FRM|].
  intros c (Σ2 & HA & LV2 & FRS2 & SP2 & CR2). eexists Σ2, _. split; [exact HA|].
  intros ms' (v & m2 & RS & (ART2 & MI2 & ST2) & PRES2 & OREC2 & AI2) FRM2. destruct OREC2 as [jo' OUT2].
  destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->). cbn [ms_fcsr MS] in FRM2. rewrite ELO in ST2.
  apply (FIN Σ2 m2 fc2 F2 u0 u1 u2 v b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 jo' ART2 MI2 ST2 FRM2 LV2 FRS2 SP2 CR2); [| exact OUT2].
  intros a Ha Hn. apply (PRES2 a Ha). cbn [outside]. split; [clear - Hn; lia| exact I].
Qed.
End Arm28.
