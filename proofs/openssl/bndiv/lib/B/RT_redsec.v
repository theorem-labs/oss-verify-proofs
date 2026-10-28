(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState ITree Nodes PropExec.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_defs R_sizeclass R_cache_defs R_prim_defs R_glue_defs R_m2s R_thread R_poison R_prim_kit R_depot_defs R_quar_defs R_qrec_defs R_qrecycle R_qdorec R_qcbrec R_mmapordie R_flushshadow R_secdealloc_p3 RT_state RT_rep RT_frame RT_trans RT_sep RT_freelift RT_geo0 RT_fkit RT_freestate RT_sys_stmt RT_drain_defs RT_drain_pure RT_drain_led RT_drain_kit RT_drain_geo RT_drain_ldefs RT_drain_loop RT_drain_istmt RT_drain_itemp RT_facts0 RT_freeA RT_malsec_rev RT_dsec_defs RT_dsec_art2 RT_dsec_runA RT_dsec_ret RT_dsec RT_refreeG RT_redrain_ldefs RT_redrain_istmt RT_redrain_loop RT_redrain_itemp RT_redrain_batch RT_redsec_defs RT_redsec_ret RT_redsec_runA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ISec.
Variable p : dlp.
Hypothesis MN : munmap_node.
Hypothesis AN : madvise_node.
Hypothesis HOK : dl_ok p.
#[local] Notation PMc := (dl_PMc p).

(* [comment removed for export] *)
Lemma ds_mun_r : forall j Σk b ib ents i rest k s, rt_wfP Σk ((b, skipn i ents) :: rest) -> dl_sig_r p Σk ->
  nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib -> nth_error (sec Σk) k = Some s -> s_quar s = true ->
  cps bsegs (ASTA RTA Σk PMc (svc_mun_r p j b ents i rest Σk k s)) (ASTA RTA (recs Σk k) PMc (dl_N_r p j b ents i rest (recs Σk k))).
Proof using MN HOK.
  intros j Σk b ib ents i rest k s HWP HS Hib Eb Hk Hq.
  pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
  pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit).
  pose proof (geo_of_wfP _ _ HWP) as HG.
  pose proof HWP as (HL & HR & _ & HSW & _ & _ & HB & _).
  pose proof HB as (B1 & B2 & B3 & B4 & B5).
  pose proof (dk_map Σk HG k s Hk) as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
  pose proof HSW as (_ & _ & _ & SW4 & _). pose proof (proj1 (Forall_forall _ _) SW4 s (nth_error_In _ _ Hk)) as (_ & (G1 & G2 & _) & _).
  eapply cps_seq.
  - intros T cf Hcf HK. pose proof Hcf as (_ & _ & (HAM & _) & _). cbn [ARTM RTA] in HAM.
    apply (MN Σk (recs Σk k) PMc (svc_mun_r p j b ents i rest Σk k s) (fun ms => exists ms0, svc_mun_r p j b ents i rest Σk k s ms0 /\ ms = nretA ms0 (mun_eff_r s))
             (s_mb s) (smsz (s_n s)) FDO MST eq_refl eq_refl); [| | | exact HL | clear - B1 B3; lia | exact B4 | exact M8 | | clear - M1; lia | exact G2 | exact M2 | | exact Hcf | exact HK].
    + change (In (secmap s) (map secmap (rev (sec Σk)))). apply in_map. apply (proj1 (in_rev _ _)). exact (nth_error_In _ _ Hk).
    + exact (ds_perm Σk k s (cfg_model cf) Hk HG HAM).
    + pose proof (secsum_recs Σk k s Hk) as E. unfold rt_eager. change (secsum Σk) with (fold_right (fun s0 acc => smsz (s_n s0) + acc) 0 (sec Σk)) in E.
      change (fold_right (fun s0 acc => smsz (s_n s0) + acc) 0 (sec (recs Σk k))) with (secsum (recs Σk k)).
      change (sum_cls (fun c => r_muser (pr (recs Σk k) c) + r_mfa (pr (recs Σk k) c)) 31) with (sum_cls (fun c => r_muser (pr Σk c) + r_mfa (pr Σk c)) 31).
      change (sec_nres (recs Σk k)) with (sec_nres Σk). rewrite E. clear; lia.
    + unfold smsz, pg_up. apply Z.mod_divide; [clear; lia|]. exists (((needed (s_n s) + rz_size (s_n s) + 4095) / 4096) + 1). clear; lia.
    + intros ms Hms. pose proof Hms as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & t3' & t4' & t5' & t6' & m' & -> & _).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exists (MSsvc (uod_regs (Z_to_bv 64 0x197fcc) (Z_to_bv 64 (dl_usp p - 2288 - 112))
        (dl_gp p) (Z_to_bv 64 tpA) t0' t1' t2' (s_mb s) (smsz (s_n s)) a2' a3' a4' a5' a6' (Z_to_bv 64 6948424) (Z_to_bv 64 b) (Z_to_bv 64 (2^37))
        (Z_to_bv 64 (Z.of_nat (length ents))) (Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16))
        (Z_to_bv 64 (16 + Z.of_nat i)) (dl_s10 p) (dl_s11 p) t3' t4' t5' t6') (dl_F p) (Z_to_bv 64 sec_munmap_ecall) (Z_to_bv 64 215)
        (dl_fc p) None m' (seg_rom bsegs)). split; [exact Hms | reflexivity].
  - apply (dl_evt (recs Σk k) PMc _ _ MST). intros ms (ms0 & Hms0 & ->).
    exact (ds_ret_r p j b ib ents i rest Σk k s HOK HWP HS Hk Hq Hib Eb ms0 Hms0).
Qed.

(* [comment removed for export] *)
Theorem item_sec_ok_r : item_sec_stmt_r p.
Proof using MN AN HOK.
  intros j Σk b ib ents i rest k s Hi HWP HS Hib Eb Hk Hq Hent.
  pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
  pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit).
  assert (Esk : skipn i ents = (s_mb s + 6128, s_n s) :: skipn (S i) ents)
    by (rewrite (skipn_nth_cons ents i (0, 0) Hi), Hent; reflexivity).
  assert (HWPc : rt_wfP Σk ((b, (s_mb s + 6128, s_n s) :: skipn (S i) ents) :: rest)) by (rewrite <- Esk; exact HWP).
  pose proof (rt_wfP_recs Σk b _ _ (skipn (S i) ents) rest k s HWPc Hk Hq eq_refl eq_refl) as HWP'.
  eapply (cps_conseq bsegs); [| intros cf Hcf; exact Hcf |].
  2:{ intros cf Hcf. exists (recs Σk k). split; [exact Hcf|]. split; [exact HWP'|].
      pose proof (recs_fields Σk k) as (X1 & X2 & _ & X4 & _ & _ & _ & X8 & _ & _ & X11 & X12 & X13).
      split; [split; [rewrite X1; exact El|]; split; [rewrite X12; exact Elv|]; split; [rewrite X13; exact Efr|];
              split; [rewrite X11; exact Ecr|]; split; [rewrite X8; exact Eql | rewrite X4; exact Einit]|].
      rewrite X2. exact Hib. }
  apply cps_pointwise. intros ms (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & -> & DM & QB).
  rewrite Hent. cbn [fst].
  change (MS (mkR (Z_to_bv 64 0x197fcc) (Z_to_bv 64 (dl_usp p - 2288 - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 (dl_usp p - 2288))
                  (Z_to_bv 64 INST) (Z_to_bv 64 (dl_usp p - 2288 - 104)) (Z_to_bv 64 (s_mb s + 6128)) a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 6947800) (Z_to_bv 64 6948424) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
                  (Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
                  (dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
              (dl_F p) (Z_to_bv 64 qcbrec_entry) (dl_fc p) None m (seg_rom bsegs))
    with (ds_ms_r p b ents i s m t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
  (* [comment removed for export] *)
  apply (cps_seq bsegs _ (ASTA RTA Σk PMc (svc_mad_r p b ents i Σk k s m))).
  { apply (dl_evt Σk PMc _ _ MST). intros ms0 <-.
    exact (ds_run1_r p j b ib ents i rest Σk k s m t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HOK HWP HS Hk Hq DM QB Hib Eb). }
  apply (cps_seq bsegs _ (ASTA RTA Σk PMc (fun ms => exists ms0, svc_mad_r p b ents i Σk k s m ms0 /\ ms = nretA ms0 (mad_eff_r s)))).
  2:{ apply (cps_seq bsegs _ (ASTA RTA Σk PMc (svc_mun_r p j b ents i rest Σk k s))).
      - apply (dl_evt Σk PMc _ _ MST). intros ms (ms0 & Hms0 & ->).
        exact (ds_run2_r p j b ib ents i rest Σk k s m HOK HWP HS Hk Hq DM QB Hib Eb ms0 Hms0).
      - exact (ds_mun_r j Σk b ib ents i rest k s HWP HS Hib Eb Hk Hq). }
  (* [comment removed for export] *)
  pose proof (geo_of_wfP _ _ HWP) as HG.
  pose proof HWP as (HL & _).
  pose proof (ds_mad_geo Σk k s HG Hk) as (R1 & R2 & R3 & R5 & R6).
  apply (AN Σk PMc (svc_mad_r p b ents i Σk k s m) (fun ms => exists ms0, svc_mad_r p b ents i Σk k s m ms0 /\ ms = nretA ms0 (mad_eff_r s))
           (pbeg (shad (s_mb s))) (pend (shad (s_mb s + smsz (s_n s)))) FDO MST HL R1 R2 R3 R5 R6).
  intros ms Hms. pose proof Hms as (t0' & t1' & t2' & a4' & a5' & a6' & t3' & t4' & t5' & t6' & mA & ws & lst & muw & mudw & -> & _).
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  eexists. split; [exact Hms | reflexivity].
Qed.

End ISec.
