(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState ITree Nodes.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs D_kit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_thread R_m2s. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_refill R_refill_ic R_getfrom R_getfrom_A R_popfree R_popfree_B R_popfree_T R_mmapfixed R_prim_lists R_prim_kit R_ensurefa R_ensurefa_B R_getfrom_M R_getfrom_B1 R_getfrom_B2 R_prim_poison RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeC RT_freeA2 RT_refillstmt RT_refillst RT_refillwf RT_rfkit RT_refillart RT_rfbytes RT_refillrun RT_refillslow RT_refillnew RT_refillslowB RT_refillslowM RT_refillslowB2 RT_count RT_sys_stmt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.
Lemma artm_eager : forall Σ Σ' mo, lay Σ' = lay Σ -> sec Σ' = sec Σ -> rt_eager Σ <= rt_eager Σ' -> ARTM_A Σ mo -> ARTM_A Σ' mo.
Proof.
  intros Σ Σ' mo E1 E2 HE (A1 & A2 & A3 & A4 & A5). unfold ARTM_A, rt_maps, artm_sys, confined0 in *. rewrite E1, E2.
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [lia | exact A5].
Qed.

Section RfCps.
Variables (Σ : rtsA) (PMc : Model -> Prop) (m : mem) (c lo : Z) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
          (F : bvmap 5 word) (fc : bv 32) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word).
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis HW0 : rt_wf0 Σ.
Hypothesis HA : ARTc Σ m.
Hypothesis Hc : 1 <= c <= 30.
Hypothesis Hca : ca Σ c = [].
Hypothesis HROOM : refill_room Σ c.
Hypothesis MI : mem_inv asegs m.
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis HLO : l_ACEIL (lay Σ) <= lo.
Hypothesis HLO2 : lo + 0x400 <= bv_unsigned sp.
Hypothesis HSP : bv_unsigned sp <= 2 ^ 47.
Hypothesis FC : fixed_commit_node.
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation r := (pr Σ c).
#[local] Notation S := (ClassSize c).
#[local] Notation au := (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
#[local] Notation mu := (r_muser (pr Σ c)).
#[local] Notation nf := (Z.of_nat (length (r_fl (pr Σ c)))).
#[local] Notation n := (MaxCount c / 2).
#[local] Notation msz := (rf_msz (pr Σ c) c).
#[local] Notation newc := (rf_newc (pr Σ c) c).
#[local] Notation new := (round_fa (4 * (Z.of_nat (length (r_fl (pr Σ c))) + rf_newc (pr Σ c) c))).
#[local] Notation entry := (refill_entry_st ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                             (l_T (lay Σ)) c m).
#[local] Notation post := (rf_post fc Σ c lo ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m).
#[local] Notation svc1 := (rr_svc1 Σ m c lo ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc).
#[local] Notation svc2 := (rr_svc2 Σ m c lo ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc).

Lemma rc_c31 : 1 <= c <= 31. Proof using Hc. clear - Hc. lia. Qed.

Definition rfΣ1 : rtsA := set_reg Σ c (mkReg (r_muser (pr Σ c) + rf_msz (pr Σ c) c) (r_mfa (pr Σ c)) (r_st (pr Σ c)) (r_fl (pr Σ c))).

Definition K1 (ms' : machine_state) : Prop := exists ms0, svc1 ms0 /\ ms' = nretA ms0 (rr_eff1 Σ c).
Definition K2 (ms' : machine_state) : Prop := exists ms0, svc2 ms0 /\ ms' = nretA ms0 (rr_eff2 Σ c).

Lemma rc_budget : layout_ok (lay Σ) /\ A_bytes (aw Σ) <= CREDIT0 /\ rt_eager (refillΣ Σ c) <= 2 ^ 38.
Proof using HW0 Hc Hca HROOM.
  pose proof rc_c31 as Hc31.
  pose proof HW0 as (HL & _ & _ & _ & _ & _ & (B1 & _ & B3 & _) & _).
  pose proof (refill_wf0 Σ c Hc31 HW0 Hca HROOM) as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & B4 & _) & _).
  split; [exact HL|]. split; [lia | exact B4].
Qed.

Lemma rc_slow_nums : nf < n -> 0 < msz /\ msz mod 4096 = 0 /\ (rb SB c + mu) mod 4096 = 0 /\ SB <= rb SB c + mu
  /\ rb SB c + mu + msz <= SB + 2 ^ 37 /\ rt_eager (refillΣ Σ c) = rt_eager Σ + msz + (rf_mfa r c - r_mfa r)
  /\ r_mfa r <= rf_mfa r c /\ r_mfa r mod 4096 = 0 /\ 0 <= r_mfa r.
Proof using HW0 Hc HROOM.
  pose proof rc_c31 as Hc31.
  intros Hslow. pose proof (rr_slow_nums Σ c HW0 Hc HROOM Hslow) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11).
  pose proof (rn_regwf Σ c HW0 Hc31) as HWc. pose proof (rf_mfa_facts r c HWc) as (A1 & _).
  pose proof (rr_geo Σ HW0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G12 & _).
  destruct (rf_slow r c Hc31 HWc Hslow) as (E1 & _).
  pose proof (rt_eager_refill Σ c Hc31) as ER. rewrite E1 in ER. cbn [r_muser r_mfa] in ER.
  unfold rb. split; [lia|]. split; [clear - N2; lia|]. split; [clear - G12 N9; lia|]. split; [clear - N7 Hc31; lia|].
  split; [clear - N3 Hc31; lia|]. split; [clear - ER; lia|]. split; [exact A1|]. split; [clear - N11; lia | clear - N10; lia].
Qed.

Lemma rc_fast : n <= nf -> cps asegs (ASTA RTA Σ PMc (eq entry)) (ASTA RTA (refillΣ Σ c) PMc post).
Proof using FDO MST HW0 HA Hc Hca HROOM MI ST HLO HLO2 HSP.
  pose proof rc_c31 as Hc31.
  intros Hfast.
  assert (W1 : forall ms, eq entry ms -> evt asegs post ms)
    by (intros ms <-; exact (rr_fast Σ m c lo ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc HW0 HA Hc Hca HROOM MI ST HLO HLO2 HSP
                               t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 Hfast)).
  eapply (cps_conseq asegs); [exact (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1)
                             | intros cf Hcf; exact Hcf |].
  intros cf Hcf. unfold ASTA. cbn [rt_allow ARTM RTA]. eapply AST_conseq; [exact Hcf | intros ms X; exact X |].
  intros mo (HM & HP). split; [|exact HP]. apply (artm_eager Σ); [reflexivity | reflexivity | | exact HM].
  rewrite (rt_eager_refill Σ c Hc31). destruct (rf_fast r c Hfast) as (E1 & _). rewrite E1. cbn [r_muser r_mfa]. lia.
Qed.

Lemma rc_front : nf < n -> cps asegs (ASTA RTA Σ PMc (eq entry)) (ASTA RTA Σ PMc svc1).
Proof using MST HW0 HA Hc Hca HROOM MI ST HLO HLO2 HSP.
  intros Hslow.
  assert (W1 : forall ms, eq entry ms -> evt asegs svc1 ms)
    by (intros ms <-; exact (rr_slowA Σ m c lo ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc HW0 HA Hc Hca HROOM MI ST HLO HLO2 HSP Hslow
                               t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6)).
  exact (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1).
Qed.

Lemma rc_svc1_regs : forall ms, svc1 ms -> ms_svc_pending ms = Some (Z_to_bv 64 222)
  /\ areg ms 10 = Z_to_bv 64 (rb SB c + mu) /\ areg ms 11 = Z_to_bv 64 msz /\ areg ms 12 = Z_to_bv 64 3 /\ areg ms 13 = Z_to_bv 64 50
  /\ areg ms 15 = Z_to_bv 64 0 /\ K1 (nretA ms (mkEffect (Z_to_bv 64 (rb SB c + mu)) [] [(Z_to_bv 64 (rb SB c + mu), Z_to_bv 64 msz)])).
Proof.
  intros ms H. pose proof H as (t0' & t1' & t2' & a6' & t3' & t4' & t5' & t6' & m1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & -> & _).
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  exists (MSsvc (mfi_regs (Z_to_bv 64 pfa_retB1) (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (usp - 32)) - 128)) - 64))
                          gp (Z_to_bv 64 tpA) t0' t1' t2' a6' (rb SB c + mu) msz (Z_to_bv 64 str_regiondata) (Z_to_bv 64 (ClassSize c))
                          (Z_to_bv 64 INST) (Z_to_bv 64 1152921504606846976) (Z_to_bv 64 1500)
                          (Z_to_bv 64 16140901064495857663) s10 s11 t3' t4' t5' t6') F
                (Z_to_bv 64 mmap_ecall_pc) (Z_to_bv 64 222) fc None m1 (seg_rom asegs)).
  split; [exact H | reflexivity].
Qed.

Lemma rc_svc2_regs : forall ms, svc2 ms -> ms_svc_pending ms = Some (Z_to_bv 64 222)
  /\ areg ms 10 = Z_to_bv 64 (fa SB c + r_mfa r) /\ areg ms 11 = Z_to_bv 64 (new - r_mfa r) /\ areg ms 12 = Z_to_bv 64 3
  /\ areg ms 13 = Z_to_bv 64 50 /\ areg ms 15 = Z_to_bv 64 0
  /\ K2 (nretA ms (mkEffect (Z_to_bv 64 (fa SB c + r_mfa r)) [] [(Z_to_bv 64 (fa SB c + r_mfa r), Z_to_bv 64 (new - r_mfa r))])).
Proof.
  intros ms H. pose proof H as (t0' & t1' & t2' & a6' & t3' & t4' & t5' & t6' & m2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & -> & _).
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  exists (MSsvc (mfi_regs (Z_to_bv 64 efs_retB) (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (usp - 32)) - 128 - 64)) - 48))
                          gp (Z_to_bv 64 tpA) t0' t1' t2' a6' (fa SB c + r_mfa r) (new - r_mfa r)
                          (Z_to_bv 64 str_freearray) (Z_to_bv 64 S) (Z_to_bv 64 INST) (Z_to_bv 64 1152921504606846976) (Z_to_bv 64 1500)
                          (Z_to_bv 64 16140901064495857663) s10 s11 t3' t4' t5' t6') F
                (Z_to_bv 64 mmap_ecall_pc) (Z_to_bv 64 222) fc None m2 (seg_rom asegs)).
  split; [exact H | reflexivity].
Qed.

Lemma rc_slow1 : nf < n -> 4 * (nf + newc) <= r_mfa r ->
  cps asegs (ASTA RTA Σ PMc svc1) (ASTA RTA (refillΣ Σ c) PMc post).
Proof using FDO MST HW0 HA Hc Hca HROOM MI ST HLO HLO2 HSP FC.
  intros Hslow Hno. pose proof rc_budget as (B1 & B2 & B3). pose proof (rc_slow_nums Hslow) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
  assert (EMF : rf_mfa r c = r_mfa r) by (unfold rf_mfa; rewrite (proj2 (Z.ltb_ge _ _) Hno); reflexivity).
  eapply (cps_seq asegs).
  - apply (FC Σ (refillΣ Σ c) PMc svc1 K1 (rb SB c + mu) msz FDO MST eq_refl eq_refl eq_refl eq_refl); try assumption.
    + rewrite N6, EMF. clear. lia.
    + exact rc_svc1_regs.
  - assert (W1 : forall ms, K1 ms -> evt asegs post ms)
      by (intros ms (ms0 & H & ->); exact (rr_slowB1 Σ m c lo ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc HW0 HA Hc Hca HROOM MI ST
                                             HLO HLO2 HSP Hslow Hno ms0 H)).
    exact (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow (refillΣ Σ c)) _ _ _ (fl_ASTA_mat_stable (refillΣ Σ c) PMc MST) W1).
Qed.

Lemma rc_slow2 : nf < n -> r_mfa r < 4 * (nf + newc) ->
  cps asegs (ASTA RTA Σ PMc svc1) (ASTA RTA (refillΣ Σ c) PMc post).
Proof using FDO MST HW0 HA Hc Hca HROOM MI ST HLO HLO2 HSP FC.
  pose proof rc_c31 as Hc31.
  intros Hslow Hgrow. pose proof rc_budget as (B1 & B2 & B3). pose proof (rc_slow_nums Hslow) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
  pose proof (rm_new Σ c HW0 Hc HROOM Hslow Hgrow) as (NW1 & NW2 & NW3 & NW4 & NW5).
  assert (E1 : rt_eager rfΣ1 = rt_eager Σ + msz) by (unfold rfΣ1; rewrite (rt_eager_set_reg Σ c _ Hc31); cbn [r_muser r_mfa]; lia).
  assert (HFA : fa SB c = rb SB c + 0xE0000000) by reflexivity.
  pose proof (rr_geo Σ HW0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G12 & _).
  eapply (cps_seq asegs).
  - apply (FC Σ rfΣ1 PMc svc1 K1 (rb SB c + mu) msz FDO MST eq_refl eq_refl eq_refl eq_refl); try assumption.
    + rewrite E1. clear. lia.
    + rewrite E1. rewrite N6, NW1 in B3. clear - B3 NW3. lia.
    + exact rc_svc1_regs.
  - eapply (cps_seq asegs).
    + assert (W1 : forall ms, K1 ms -> evt asegs svc2 ms)
        by (intros ms (ms0 & H & ->); exact (rr_slowM Σ m c lo ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc HW0 HA Hc Hca HROOM MI ST
                                               HLO HLO2 HSP Hslow Hgrow ms0 H)).
      exact (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow rfΣ1) _ _ _ (fl_ASTA_mat_stable rfΣ1 PMc MST) W1).
    + eapply (cps_seq asegs).
      * apply (FC rfΣ1 (refillΣ Σ c) PMc svc2 K2 (fa SB c + r_mfa r) (new - r_mfa r) FDO MST eq_refl eq_refl eq_refl eq_refl).
        all: change (lay rfΣ1) with (lay Σ) in *; change (aw rfΣ1) with (aw Σ) in *; try assumption.
        all: try (rewrite E1, N6, NW1; clear; lia).
        all: try (clear - NW3; lia). all: try (clear - NW4 N8; lia).
        all: try (unfold rb in HFA; rewrite HFA; clear - G12 N8 N9 Hc31; lia).
        all: try (rewrite HFA; unfold rb; clear - Hc31 NW2 N9; lia).
        exact rc_svc2_regs.
      * assert (W1 : forall ms, K2 ms -> evt asegs post ms)
          by (intros ms (ms0 & H & ->); exact (rr_slowB2 Σ m c lo ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc HW0 HA Hc Hca HROOM MI ST
                                                 HLO HLO2 HSP Hslow Hgrow ms0 H)).
        exact (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow (refillΣ Σ c)) _ _ _ (fl_ASTA_mat_stable (refillΣ Σ c) PMc MST) W1).
Qed.

Theorem refill_core : cps asegs (ASTA RTA Σ PMc (eq entry)) (ASTA RTA (refillΣ Σ c) PMc post).
Proof using FDO MST HW0 HA Hc Hca HROOM MI ST HLO HLO2 HSP FC.
  destruct (Z_lt_ge_dec nf n) as [Hslow|Hfast]; [|apply rc_fast; lia].
  eapply (cps_seq asegs); [exact (rc_front Hslow)|].
  destruct (Z_lt_ge_dec (r_mfa r) (4 * (nf + newc))) as [Hgrow|Hno]; [exact (rc_slow2 Hslow Hgrow) | exact (rc_slow1 Hslow ltac:(lia))].
Qed.

End RfCps.

Theorem refill_ok : fixed_commit_node -> refill_stmt.
Proof.
  intros FC Σ PMc ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m c lo
    FDO MST Hc Hca HA MI ST HLO HLO2 HSP.
  pose proof (ART_wf Σ m HA) as HW. pose proof (proj1 (rt_wf_split Σ) HW) as (HW0 & HRC).
  pose proof (carved_room Σ c HW ltac:(lia) Hca) as HROOM.
  pose proof (ART_c Σ m HA) as HAc.
  eapply (cps_conseq asegs); [exact (refill_core Σ PMc m c lo ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6
                                       FDO MST HW0 HAc Hc Hca HROOM MI ST HLO HLO2 HSP FC) | intros cf Hcf; exact Hcf |].
  intros cf Hcf. unfold ASTA in *. eapply AST_conseq; [exact Hcf | | intros mo X; exact X].
  intros ms (m' & RET & AC & MI' & WM' & ST' & MW).
  exists m'. split; [exact RET|].
  split; [apply c_ART; [apply (proj2 (rt_wf_split (refillΣ Σ c))); split;
                          [exact (refill_wf0 Σ c ltac:(lia) HW0 Hca HROOM) | exact (refill_count Σ c ltac:(lia) HW0 HRC)] | exact AC]|].
  split; [exact MI'|]. split; [exact WM'|]. split; [exact ST'|].

  pose proof (geo_of_wf0 Σ HW0) as HG. pose proof (rr_sp Σ lo sp HLO HLO2) as Hsp. assert (Hc31 : 1 <= c <= 31) by lia.
  intros a Ha. apply MW.
  refine (kv_client Σ (W_R (l_T (lay Σ)) (l_SB (lay Σ)) c (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) (bv_unsigned sp)) [] [] []
           (bv_unsigned sp) HG (rz_img Σ c _ HG Hc31 Hsp) (rz_grant Σ c _ HG Hc31 Hsp) (rz_slot Σ c _ HG Hc31 Hsp)
           (rz_shad_app Σ c _ HG Hc31 Hsp) (rz_secmap Σ c _ HG Hc31 Hsp) (rz_stack Σ c _ HG Hc31 Hsp) _ (live Σ) _ _ Ha).
  - apply Forall_forall. intros x _. exact I.
  - intros p n Hin. pose proof HW0 as (_ & _ & (_ & _ & V3 & _) & _). destruct (V3 p n Hin) as [(c' & i' & Hc' & Hn & Ep)|(s & Hs & Hq & Hn & Ep)].
    + left. exists c', i'. split; [exact Hc'|]. split; [exact Hn|]. split; [exact Ep|]. intros [].
    + right. destruct (In_nth_error _ _ Hs) as (k & Hk). exists k, s. split; [exact Hk|]. split; [exact Hq|]. split; [exact Hn|].
      split; [exact Ep | intros []].
Qed.

End GWIN.
