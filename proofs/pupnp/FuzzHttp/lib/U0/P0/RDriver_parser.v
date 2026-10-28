(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import base list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Agree Ceiling.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach AllocIF SReach AllocSpec.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs RMallocRep RMallocTree RMalloc_iface AllocInst H_fuzz_stmt.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Stdio_base Printf_lib Startup RefImpl Stdio_iface RDriver_kit RDriver_ctx RDriver_iface RDriver_seams.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require RF_main_A RF_main_T.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog KStep.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Section PS.
  Context {HGW : HasGuard} {HCEIL : HasCeiling}.
  Variables (sp0 : word) (argv : list (list byte)) (TID : Z) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : alloc_ceiling = LO sp0.
  Hypothesis FZ : fuzz_one_stmt AI_P0.
  Notation usp0 := (bv_unsigned sp0).

  #[using="Type"] Lemma heap_pres_agree : forall LB SP m m', heap_pres AI_P0 LB SP m m' -> agree_on rsegs (client_addr AI_P0 LB SP) m m'.
  Proof. intros LB SP m m' H a Ha Hc. exact (H a Ha Hc). Qed.

  #[using="Type"] Lemma client_static : forall LB SP a,
    (rstat_addr a \/ stderr_addr a \/ RF_main_A.cj0_addr a \/ stdout_addr a) -> client_addr AI_P0 LB SP a.
  Proof.
    intros LB SP a Ha. right; left. cbn [ai_L AI_P0 P0L al_client_static].
    unfold rstat_addr, stderr_addr, RF_main_A.cj0_addr, stdout_addr in Ha.
    unfold p0_client_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK.
    assert (E : exists lo, lo <= a < lo + 1 /\ 0x2a000 <= lo /\ lo + 1 <= 0x5d000
              /\ (lo + 1 <= 375464 \/ 375584 + 928 <= lo) /\ (lo + 1 <= 243580 \/ 243580 + 4 <= lo)
              /\ (lo + 1 <= 375432 \/ 375432 + 8 <= lo) /\ (lo + 1 <= 172368 \/ 172368 + 8 <= lo)
              /\ (lo + 1 <= 377592 \/ 377592 + 8 <= lo)) by (exists a; lia).
    destruct E as (lo & H0 & H). exists lo, (lo + 1). split; [exact H| lia].
  Qed.

  #[using="VSP CEIL FZ"] Theorem parser_seam : forall k fl ap d s LB m ms,
    rat_call sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 k fl ap d s LB m ms ->
    SREACH AI_P0 (fun s' LB' ms' => exists m', rat_ret sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 k 0 fl ap d s' LB' m' ms') ms s LB.
  Proof.
    intros k fl ap d s LB m ms (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & x19 & t3 & t4 & t5 & t6 & F & fc & -> & FRM & HK & SM).
    pose proof (valid_sp_facts sp0 VSP) as SF. destruct VSP as (VLO & VHI & V16). unfold sp_window_lo, sp_window_hi in VLO, VHI.
    destruct SM as (OK & DM & DB & DBL & HP & SOF & [errv ERR] & ST).
    pose proof OK as (HC & HL & HCNT & HK4 & LEN & CAPM & LR & SCR & BR & OWN). unfold MAX_INPUT in CAPM.
    pose proof DM as (TF & FR & MI & RS & AUX & SE & CJ). pose proof CJ as (C1 & C2 & C3 & G).
    pose proof DB as [B1 B2]. pose proof DBL as [L1 L2].
    pose proof (RHEAP_ssp _ _ _ HP) as [SS1 SS2]. unfold got_ssp, ssp_guard in SS1, SS2.
    assert (ELEN : zlength (ap_content ap) = Z.of_nat (length (d_DATA d))) by (rewrite HC; unfold zlength; rewrite length_map; reflexivity).
    assert (EPL : ap_payload_len ap = Z.of_nat (length (d_DATA d)) - 6 - d_L d) by (unfold ap_payload_len; rewrite ELEN, HL; unfold HDR_MIN; lia).

    assert (INP : exists data, bytes_at rsegs m (d_AL d) data /\ Z.of_nat (length data) = ap_payload_len ap
                   /\ ((ap_payload_len ap = 0 /\ d_AL d = EMPTY_OBJ) \/ (exists q, In (q, d_AL d, ap_payload_len ap) LB))).
    { destruct (ap_owned ap) as [p|] eqn:EO.
      - destruct OWN as (PL & EOW & BR2). specialize (B2 eq_refl). specialize (L2 eq_refl).
        exists (skipn (Z.to_nat (6 + d_L d)) (d_DATA d)). split; [| split; [rewrite length_skipn; lia| right; exists p; exact L2]].
        pose proof (rw_cells_bytes_at _ _ _ _ B2) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X.
      - destruct OWN as (PL & EAL & EOW). exists []. rewrite EAL. split; [apply bytes_at_nil; lia|]. split; [cbn; lia|]. left. split; [exact PL| reflexivity]. }
    destruct INP as (data & IB & ILEN & IOR).
    unfold fuzz_one_stmt in FZ.
    eapply sreach_mono_keep.
    { eapply (FZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m s LB (d_AL d) (ap_payload_len ap) (usp0 - 8388608) usp0 errv guard_word data);
        cbn [ai_L AI_P0 P0L al_errno al_tp RENV RHEAP];
        first [ exact IB | exact ILEN | exact IOR | exact HP | exact AUX | exact MI | exact G | exact SS1 | exact SS2 | exact FRM | reflexivity
              | rewrite unsigned_lit by lia; first [exact ST | unfold RERRNO in ERR; exact ERR | unfold PARSER_STACK; lia | lia]
              | exact ERR | rewrite CEIL; unfold LO; lia | lia
              | rewrite unsigned_lit by lia; replace (usp0 + -208) with (usp0 + (-13) * 16) by lia; rewrite Z_mod_plus_full; lia ]. }
    cbv beta. intros s' LB' ms' KEEP PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & AF & HP' & SUB & G' & SS1' & SS2').
    destruct AF as (MI' & ST' & AUX' & [errv' ERR'] & HPRES). cbn [ai_L AI_P0 P0L al_errno RENV] in AUX', ERR', HPRES.
    rewrite unsigned_lit in ST' by lia. rewrite unsigned_lit in HPRES by lia.
    destruct KEEP as [KFA KSO]. cbn in KFA, KSO.
    pose proof (heap_pres_agree _ _ _ _ HPRES) as AG.
    exists m'. unfold rat_ret. do 18 eexists.
    split; [replace (ret_pc (Z_to_bv 64 0x13eb8)) with (Z_to_bv 64 0x13eb8) by (symmetry; rpc); reflexivity|].
    split; [exact FRM|]. split; [exact HK|]. split; [lia|].
    split; [exact OK|].
    split. { eapply (DMEM_agree sp0 argv TID S4 S5 S6 S7 _ _ ap d m m' AG); [| exact MI'| exact AUX'| exact DM].
             intros a [Ha|Ha]; [left; lia| apply client_static; LiaTuning.ctauto]. }
    split. { eapply (DBYTES_agree _ true ap d m m' AG OK); [| | exact DB].
             - intros a Ha. right; right. exists (ap_buf ap, d_A d, d_cap d). split; [exact L1|]. cbn. lia.
             - intros _ a Ha. destruct (ap_owned ap) as [p|]; [| destruct OWN as (PL0 & _); lia].
               right; right. exists (p, d_AL d, ap_payload_len ap). split; [exact (L2 eq_refl)|]. cbn. lia. }
    split. { split; [apply SUB; exact L1|]. intros E. specialize (L2 E). destruct (ap_owned ap); [apply SUB; exact L2| exact I]. }
    split; [exact HP'|].
    split. { rewrite KSO. eapply (stdout_file_agree _ _ _ _ AG); [| exact SOF]. intros a Ha. apply client_static. LiaTuning.ctauto. }
    split; [exists errv'; exact ERR'|].
    exact ST'.
  Qed.

  #[using="Type"] Lemma in_lb_remove : forall (p : bptr) (b : block) (LB : list block),
    In b LB -> blk_id b <> p -> In b (AllocIF.lb_remove (ai_K_eqb rsegs AI_P0) p LB).
  Proof.
    intros p b LB Hin Hne. unfold AllocIF.lb_remove. cbn [ai_K_eqb AI_P0].
    induction LB as [|c LB IH]; [destruct Hin|]. rewrite filter_cons. destruct Hin as [->|Hin].
    - destruct (decide _) as [Y|N]; [left; reflexivity|]. exfalso. apply N.
      destruct (bptr_eqb (AllocIF.blk_id b) p) eqn:E; [| rewrite E; exact I]. exfalso. apply Hne. apply (proj1 (AllocInst.bptr_eqb_eq _ _)). exact E.
    - destruct (decide _) as [Y|N]; [right|]; apply IH; exact Hin.
  Qed.

  #[using="VSP CEIL"] Theorem free_owned_seam : forall fl ap d s LB m ms,
    rat_free_owned sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 fl ap d s LB m ms ->
    SREACH AI_P0 (fun s' LB' ms' => exists m', rat_owned_ret sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 fl ap d s' LB' m' ms') ms s LB.
  Proof.
    intros fl ap d s LB m ms (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x19 & t3 & t4 & t5 & t6 & F & fc & -> & FRM & SM).
    pose proof (valid_sp_facts sp0 VSP) as SF. destruct VSP as (VLO & VHI & V16). unfold sp_window_lo, sp_window_hi in VLO, VHI.
    destruct SM as (OK & DM & DB & DBL & HP & SOF & [errv ERR] & ST).
    pose proof OK as (HC & HL & HCNT & HK4 & LEN & CAPM & LR & SCR & BR & OWN). unfold MAX_INPUT in CAPM.
    pose proof DM as (TF & FR & MI & RS & AUX & SE & CJ).
    pose proof DB as [B1 B2]. pose proof DBL as [L1 L2].
    assert (EPL : ap_payload_len ap = zlength (ap_content ap) - 6 - d_L d) by (unfold ap_payload_len; rewrite HL; unfold HDR_MIN; lia).
    assert (ELEN : zlength (ap_content ap) = Z.of_nat (length (d_DATA d))) by (rewrite HC; unfold zlength; rewrite length_map; reflexivity).
    destruct (ap_owned ap) as [p|] eqn:EO.
    -
      destruct OWN as (PL & EOW & BR2). specialize (L2 eq_refl).
      pose proof P0_free_contract as FC. unfold free_contract_at in FC. cbn [ai_L AI_P0 P0L al_free_pc al_errno al_tp al_stack RENV RHEAP] in FC.
      eapply sreach_mono_keep.
      { eapply (FC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m s LB p (d_AL d) (ap_payload_len ap) (usp0 - 8388608) usp0 errv);
          first [ exact HP | exact L2 | exact AUX | exact MI | exact ERR | rewrite EOW; reflexivity
                | rewrite unsigned_lit by lia; first [exact ST | lia]
                | rewrite CEIL; unfold LO; lia | lia ]. }
      cbv beta. intros s' LB' ms' [KFA KSO] PO. cbn in KFA, KSO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & AF & -> & HP').
      destruct AF as (MI' & ST' & AUX' & [errv' ERR'] & HPRES). cbn [ai_L AI_P0 P0L al_errno RENV] in AUX', ERR', HPRES.
      rewrite unsigned_lit in ST' by lia. rewrite unsigned_lit in HPRES by lia.
      pose proof (heap_pres_agree _ _ _ _ HPRES) as AG.
      assert (INB : In (ap_buf ap, d_A d, d_cap d) (AllocIF.lb_remove (ai_K_eqb rsegs AI_P0) p LB)).
      { apply in_lb_remove; [exact L1|]. cbn. intros E.
        pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HP) as ND.
        assert (NEQ : (p, d_AL d, ap_payload_len ap) <> (ap_buf ap, d_A d, d_cap d)) by (intros X; injection X; intros; lia).
        apply NEQ. eapply (AllocInst.nodup_map_eq blk_id); [exact ND| exact L2| exact L1| cbn; symmetry; exact E]. }
      exists m'. unfold rat_owned_ret. do 19 eexists.
      split; [replace (ret_pc (Z_to_bv 64 0x13ee4)) with (Z_to_bv 64 0x13ee4) by (symmetry; rpc); reflexivity|].
      split; [exact FRM|].
      split; [exact OK|].
      split. { eapply (DMEM_agree sp0 argv TID S4 S5 S6 S7 _ _ ap d m m' AG); [| exact MI'| exact AUX'| exact DM].
               intros a [Ha|Ha]; [left; lia| apply client_static; LiaTuning.ctauto]. }
      split. { eapply (DBYTES_agree _ false ap d m m' AG OK); [| intros X; discriminate X| apply DBYTES_drop; exact DB].
               intros a Ha. right; right. exists (ap_buf ap, d_A d, d_cap d). split; [exact INB|]. cbn. lia. }
      split; [split; [exact INB| intros X; discriminate X]|].
      split; [exact HP'|].
      split. { rewrite KSO. eapply (stdout_file_agree _ _ _ _ AG); [| exact SOF]. intros a Ha. apply client_static. LiaTuning.ctauto. }
      split; [exists errv'; exact ERR'| exact ST'].
    -
      destruct OWN as (PL & EAL & EOW).
      pose proof P0_free_null_contract as FN. unfold free_null_contract_at in FN. cbn [ai_L AI_P0 P0L al_free_pc] in FN.
      eapply sreach_evt; [apply FN; rewrite EOW; reflexivity|].
      cbv beta. intros ms' (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & ->).
      apply sreach_ret. exists m. unfold rat_owned_ret. do 19 eexists.
      split; [replace (ret_pc (Z_to_bv 64 0x13ee4)) with (Z_to_bv 64 0x13ee4) by (symmetry; rpc); reflexivity|].
      split; [exact FRM|].
      split; [exact OK|]. split; [exact DM|]. split; [apply DBYTES_drop; exact DB|]. split; [apply DBLOCKS_drop; exact DBL|].
      split; [exact HP|]. split; [exact SOF|]. split; [exists errv; exact ERR| exact ST].
  Qed.

  #[using="VSP CEIL"] Theorem free_buf_seam : forall st ap d s LB m ms,
    rat_free_buf sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 st ap d s LB m ms ->
    SREACH AI_P0 (fun s' LB' ms' => exists m', rat_main_ret sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 st s' LB' m' ms') ms s LB.
  Proof.
    intros st ap d s LB m ms (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & -> & FRM & HST
                              & OK & FR & MI & RS & AUX & SE & CJ & DB & DBL & HP & SOF & [errv ERR] & ST).
    pose proof (valid_sp_facts sp0 VSP) as SF. destruct VSP as (VLO & VHI & V16). unfold sp_window_lo, sp_window_hi in VLO, VHI.
    pose proof DBL as [L1 _].
    pose proof P0_free_contract as FC. unfold free_contract_at in FC. cbn [ai_L AI_P0 P0L al_free_pc al_errno al_tp al_stack RENV RHEAP] in FC.
    eapply sreach_mono_keep.
    { eapply (FC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m s LB (ap_buf ap) (d_A d) (d_cap d) (usp0 - 8388608) usp0 errv);
        first [ exact HP | exact L1 | exact AUX | exact MI | exact ERR | reflexivity
              | rewrite unsigned_lit by lia; first [exact ST | lia]
              | rewrite CEIL; unfold LO; lia | lia ]. }
    cbv beta. intros s' LB' ms' [KFA KSO] PO. cbn in KFA, KSO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & AF & -> & HP').
    destruct AF as (MI' & ST' & AUX' & [errv' ERR'] & HPRES). cbn [ai_L AI_P0 P0L al_errno RENV] in AUX', ERR', HPRES.
    rewrite unsigned_lit in ST' by lia. rewrite unsigned_lit in HPRES by lia.
    pose proof (heap_pres_agree _ _ _ _ HPRES) as AG.
    exists m'. unfold rat_main_ret. do 24 eexists.
    split; [replace (ret_pc (Z_to_bv 64 0x13d18)) with (Z_to_bv 64 0x13d18) by (symmetry; rpc); reflexivity|].
    split; [exact HST|].
    split. { unfold MFRAME in *. eapply rw_cells_agree; [exact AG| exact FR|]. intros a Ha. left. cbn in Ha. lia. }
    split; [exact MI'|].
    split. { eapply (RSTAT_agree TID _ _ _ AG); [| exact RS]. intros a Ha. apply client_static. LiaTuning.ctauto. }
    split; [exact HP'|].
    split. { rewrite KSO. eapply (stdout_file_agree _ _ _ _ AG); [| exact SOF]. intros a Ha. apply client_static. LiaTuning.ctauto. }
    split. { eapply (stderr_wfile0_agree _ _ _ AG); [| exact SE]. intros a Ha. apply client_static. LiaTuning.ctauto. }
    exact ST'.
  Qed.
End PS.
