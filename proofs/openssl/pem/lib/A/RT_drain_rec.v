(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState ITree Nodes.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs R_cache_defs R_prim_defs R_glue_defs R_m2s R_thread R_poison R_prim_kit R_depot_defs R_quar_defs R_qrec_defs R_qput R_qrecycle R_qdorec R_qcbrec R_cdealloc RT_state RT_rep RT_frame RT_trans RT_sep RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeE RT_sys_stmt RT_drain_defs RT_drain_pure RT_drain_led RT_drain_start RT_drain_kit RT_drain_geo RT_drain_ldefs RT_drain_istmt RT_drain_art4 RT_drain_loop RT_drain_itemp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section DRec.
Variable p : dlp.
Hypothesis HOK : dl_ok p.
Hypothesis ITEM : item_stmt p.
Hypothesis BATCH : batch_stmt p.
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation lo := (dl_lo p).
#[local] Notation PMc := (dl_PMc p).
#[local] Notation C := (dl_usp p - 2288).
#[local] Notation T := (l_T (lay (dl_Σ0 p))).
#[local] Notation SB := (l_SB (lay (dl_Σ0 p))).

(* [comment removed for export] *)
Definition dl_E (tmp : list batch) (Σk : rtsA) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
    ms = MS (mkR (Z_to_bv 64 0x19cd54) (Z_to_bv 64 C) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (dl_r0 p) (dl_r1 p) (Z_to_bv 64 QUAR)
                 (Z_to_bv 64 C) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (dl_stk p)) a4 a5 a6 a7 (dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p)
                 (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p) (dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
            (dl_F p) (Z_to_bv 64 qdorec_entry) (dl_fc p) None m (seg_rom asegs)
    /\ ARTc Σk m /\ qcache_rep m C tmp /\ stk asegs m lo C /\ mem_inv asegs m
    /\ (exists G, wmono_out G (dl_m0 p) m /\ dl_gone p G) /\ rt_pres (live Σ0) (frames Σ0) (C + 32) (dl_m0 p) m.

(* [comment removed for export] *)
Lemma dl_mem_entry : forall j Σk rest (m m' : mem) (W : list ivl), ARTc Σk m -> (exists G, wmono_out G (dl_m0 p) m /\ dl_gone p G) ->
  rt_pres (live Σ0) (frames Σ0) (C + 32) (dl_m0 p) m -> geo_ok Σk -> dl_sig p Σk ->
  live_wf Σk -> depot_ok (dep Σk) (l_DNB (lay Σk)) (l_SSB (lay Σk)) (l_ACEIL (lay Σk)) ->
  Forall (fun b => exists j, nth_error (r_st (pr Σk 24)) j = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σk)) 24 j) (ql Σk ++ qg Σk) ->
  Forall (fun iv => lo <= fst iv /\ snd iv <= C + 32) W -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
  stk asegs m' lo (C - 112) ->
  drec_mem m' C SB j (T + 208) (dl_stk p) (Z_to_bv 64 0x19cd54) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p)
    (dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p) rest ->
  dl_mem p j Σk rest m'.
Proof using HOK.
  intros j Σk rest m m' W A WM0 RP HG (El & Elv & Efr & _) Hlive Hdep HQB HW MU WM MI' ST' (FR' & _ & QR').
  pose proof HOK as (_ & _ & HLO & HLO2 & HSP & HG0).
  pose proof (dl_nums p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
  assert (HL : l_ACEIL (lay Σk) <= lo) by (rewrite El; exact N9).
  split; [exact (artc_stk Σk m m' W lo (C + 32) HG HL HW A Hdep HQB MU WM)|].
  split; [exact MI'|]. split; [exact ST'|].
  split; [destruct WM0 as (G & WG & HGo); exists G; split; [exact (wmono_out_wmono G _ m m' WG WM) | exact HGo]|].
  split; [|split; [exact FR' | exact QR']].
  pose proof (client_stk Σk m m' W lo (C + 32) HG HL ltac:(lia) HW Hlive MU) as RP'. rewrite Elv, Efr in RP'.
  exact (rt_pres_trans _ _ _ _ m m' RP RP').
Qed.

(* [comment removed for export] *)
Theorem dl_from_E : forall Σk tmp, rt_wfP Σk tmp -> dl_sig p Σk -> cps asegs (ASTA RTA Σk PMc (dl_E tmp Σk)) (dl_fin p).
Proof using HOK ITEM BATCH.
  intros Σk tmp HWP HS.
  pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
  pose proof (dl_nums p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
  pose proof HS as (El & Elv & Efr & _).
  pose proof (geo_of_wfP _ _ HWP) as HG. pose proof HWP as (_ & _ & Hlive & _ & _ & _ & _ & Hdep & _).
  pose proof (hqb_of_wfP _ _ HWP) as HQB.
  assert (HL : l_ACEIL (lay Σk) <= lo) by (rewrite El; exact N9).
  destruct tmp as [|[b ents] rest].
  - (* [comment removed for export] *)
    eapply (cps_seq asegs).
    + apply (dl_evt Σk PMc _ (dl_R p Σk) MST).
      intros ms (t0 & t1 & t2 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & -> & A & QR & ST & MI & WM0 & RP).
      eapply evt_mono; [apply (drec_empty_spec (Z_to_bv 64 0x19cd54) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (dl_r0 p) (dl_r1 p) a4 a5 a6 a7
                                 (dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p) (dl_s10 p) (dl_s11 p)
                                 t3 t4 t5 t6 (dl_F p) (dl_fc p) m C lo (T + 208) (dl_stk p))|].
      1: exact QR. 1: exact ST. 1: lia. 1: exact N4. 1: exact N6. 1: exact N7. 1: exact N8. 1: exact MI.
      intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & QR' & ST').
      exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [reflexivity|].
      assert (HW : Forall (fun iv => lo <= fst iv /\ snd iv <= C + 32) [(C - 112, C)]) by (repeat constructor; cbn [fst snd]; lia).
      split; [exact (artc_stk Σk m m' _ lo (C + 32) HG HL HW A Hdep HQB MU WM)|].
      split; [exact MI'|]. split; [exact ST'|].
      split; [destruct WM0 as (G & WG & HGo); exists G; split; [exact (wmono_out_wmono G _ m m' WG WM) | exact HGo]|].
      split; [|exact QR'].
      pose proof (client_stk Σk m m' _ lo (C + 32) HG HL ltac:(lia) HW Hlive MU) as RP'. rewrite Elv, Efr in RP'.
      exact (rt_pres_trans _ _ _ _ m m' RP RP').
    + intros T0 cf Hcf Hk. apply Hk. exists Σk. split; [exact Hcf | split; [exact HWP | exact HS]].
  - destruct (dl_batch_of Σk b ents rest HWP) as (ib & Hib & Eb).
    pose proof (dl_bslot p HLO HLO2 HSP HG0 Σk ib HG El Hib) as (B1 & B2 & B3 & B4).
    assert (QW : qwf SB ((b, ents) :: rest)) by (pose proof (qwf_of_wfP _ _ HWP) as X; rewrite El in X; exact X).
    assert (QB : RT_state.qbytes ((b, ents) :: rest) <= 2 ^ 40) by (destruct HWP as (_ & _ & _ & _ & (_ & _ & X & _) & _); exact X).
    rewrite qbytes_eq in QB.
    assert (HW : Forall (fun iv => lo <= fst iv /\ snd iv <= C + 32) [(C - 112, C + 32)]) by (repeat constructor; cbn [fst snd]; lia).
    destruct ents as [|e es].
    + (* [comment removed for export] *)
      eapply (cps_seq asegs).
      * apply (dl_evt Σk PMc _ (fun ms => exists j, dl_D p j b [] rest Σk ms) MST).
        intros ms (t0 & t1 & t2 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & -> & A & QR & ST & MI & WM0 & RP).
        pose proof (proj1 (proj1 A)) as (IC1 & _). rewrite El in IC1.
        apply (proj1 (rwc_app asegs m _ [C8 (Z_to_bv 64 SB)] [C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 (RIS_of SB))])) in IC1.
        destruct IC1 as (SBC & _).
        eapply evt_mono; [apply (drec_first_deal_spec (Z_to_bv 64 0x19cd54) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (dl_r0 p) (dl_r1 p) a4 a5 a6 a7
                                   (dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p) (dl_s10 p) (dl_s11 p)
                                   t3 t4 t5 t6 (dl_F p) (dl_fc p) m (l_ACEIL (lay Σ0)) C SB lo (T + 208) (dl_stk p) b rest)|].
        1: exact QW. 1: lia. 1: exact N2. 1: exact QR. 1: exact SBC. 1: exact ST. 1: lia. 1: exact N3. 1: exact N4. 1: exact N6.
        1: exact N7. 1: exact N8. 1: exact MI.
        intros ms' (j & t0' & t1' & t2' & a4' & a5' & a6' & a7' & s6' & s7' & s8' & s9' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & DM' & QB' & ST').
        exists j, t0', t1', t2', a4', a5', a6', a7', s6', s7', s8', s9', t3', t4', t5', t6', m'. split; [reflexivity|]. split; [|exact QB'].
        exact (dl_mem_entry j Σk rest m m' _ A WM0 RP HG HS Hlive Hdep HQB HW MU WM MI' ST' DM').
      * apply cps_pointwise. intros ms (j & X).
        eapply (cps_seq asegs).
        -- eapply (cps_conseq asegs); [exact (BATCH j Σk b ib [] rest HWP HS Hib Eb) | | intros cf Hcf; exact Hcf].
           intros cf Hcf. unfold ASTA in *. eapply AST_conseq; [exact Hcf | intros ms' <-; exact X | intros mo Y; exact Y].
        -- apply dl_cps_ex. intros Σk' (HWP' & HS'). exact (dl_from_B p MST HLO HLO2 HSP HG0 ITEM BATCH j rest Σk' HWP' HS').
    + (* [comment removed for export] *)
      eapply (cps_seq asegs).
      * apply (dl_evt Σk PMc _ (fun ms => exists j, dl_Q p j b (e :: es) 0 rest Σk ms) MST).
        intros ms (t0 & t1 & t2 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & -> & A & QR & ST & MI & WM0 & RP).
        pose proof (proj1 (proj1 A)) as (IC1 & _). rewrite El in IC1.
        apply (proj1 (rwc_app asegs m _ [C8 (Z_to_bv 64 SB)] [C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 (RIS_of SB))])) in IC1.
        destruct IC1 as (SBC & _).
        eapply evt_mono; [apply (drec_first_qcb_spec (Z_to_bv 64 0x19cd54) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (dl_r0 p) (dl_r1 p) a4 a5 a6 a7
                                   (dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p) (dl_s10 p) (dl_s11 p)
                                   t3 t4 t5 t6 (dl_F p) (dl_fc p) m C SB lo (T + 208) (dl_stk p) b (e :: es) rest)|].
        1: discriminate. 1: exact QW. 1: lia. 1: exact N1. 1: exact QR. 1: exact SBC. 1: exact ST. 1: lia. 1: exact N3. 1: exact N4. 1: exact N6.
        1: exact N7. 1: exact N8. 1: exact MI.
        intros ms' (j & t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & DM' & QB' & ST').
        exists j, t0', t1', t2', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [reflexivity|]. split; [|exact QB'].
        exact (dl_mem_entry j Σk rest m m' _ A WM0 RP HG HS Hlive Hdep HQB HW MU WM MI' ST' DM').
      * apply cps_pointwise. intros ms (j & X).
        eapply (cps_seq asegs).
        -- eapply (cps_conseq asegs); [exact (dl_from_Q0 p MST HLO HLO2 HSP HG0 ITEM BATCH j Σk b ib (e :: es) rest ltac:(discriminate) HWP HS Hib Eb)
                                      | | intros cf Hcf; exact Hcf].
           intros cf Hcf. unfold ASTA in *. eapply AST_conseq; [exact Hcf | intros ms' <-; exact X | intros mo Y; exact Y].
        -- apply dl_cps_ex. intros Σk' (HWP' & HS'). exact (dl_from_B p MST HLO HLO2 HSP HG0 ITEM BATCH j rest Σk' HWP' HS').
Qed.

End DRec.
