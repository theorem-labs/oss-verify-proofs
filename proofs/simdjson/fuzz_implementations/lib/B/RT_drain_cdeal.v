(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState ITree Nodes.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs R_cache_defs R_prim_defs R_glue_defs R_m2s R_thread R_poison R_prim_kit R_depot_defs R_quar_defs R_cdealloc R_mmapfixed R_ensurefa R_return R_return_A RT_state RT_rep RT_frame RT_trans RT_sep RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeE RT_sys_stmt RT_drain_defs RT_drain_pure RT_drain_led RT_drain_kit RT_drain_art3 RT_drain_geo RT_drain_cdk RT_drain_cfast RT_drain_cslow RT_drain_cslowB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GW}.
Lemma dd_evt_cps : forall (Σ Σ' : rtsA) (PMc : Model -> Prop) (ms : machine_state) (Q : machine_state -> Prop),
  mat_stable PMc -> lay Σ' = lay Σ -> sec Σ' = sec Σ -> rt_eager Σ' = rt_eager Σ -> aw Σ' = aw Σ ->
  evt bsegs Q ms -> cps bsegs (ASTA RTA Σ PMc (eq ms)) (ASTA RTA Σ' PMc Q).
Proof.
  intros Σ Σ' PMc ms Q MST El Es Ee Ea HE.
  assert (W1 : forall ms', eq ms ms' -> evt bsegs Q ms') by (intros ms' <-; exact HE).
  eapply (cps_conseq bsegs); [exact (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1)
                             | intros cf Hcf; exact Hcf |].
  intros cf Hcf. unfold ASTA. cbn [rt_allow ARTM RTA].
  replace (rtA_allow Σ') with (rtA_allow Σ) by (unfold rtA_allow; rewrite El, Ea; reflexivity).
  eapply AST_conseq; [exact Hcf | intros ms' X; exact X |].
  intros mo (HM & HP). split; [|exact HP]. exact (artm_eq Σ Σ' mo El Es Ee HM).
Qed.

Section CDeal.
Variables (Σ : rtsA) (PMc : Model -> Prop) (m : mem) (c : Z) (i : nat) (st : ckst) (lo : Z)
  (ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis FC : fixed_commit_node.
Hypothesis HG : geo_ok Σ.
Hypothesis HA : ARTc (set_st Σ c i CkIdle) m.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hi : nth_error (r_st (pr Σ c)) i = Some st.
Hypothesis Hinit : ca_init Σ = true.
Hypothesis HRW : reg_wf c (pr Σ c).
Hypothesis Hcl : Forall (fun x => 0 <= x < Z.of_nat (length (r_st (pr Σ c)))) (ca Σ c).
Hypothesis Hcnt : Z.of_nat (length (ca Σ c)) <= MaxCount c.
Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
Hypothesis HLO : l_ACEIL (lay Σ) <= lo.
Hypothesis HLO2 : lo + 0x400 <= bv_unsigned sp.
Hypothesis HSP : bv_unsigned sp <= 2 ^ 47.
Hypothesis MI : mem_inv bsegs m.
Hypothesis Hlive : live_wf Σ.
Hypothesis Hdep : depot_ok (dep Σ) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)).
Hypothesis HQB : Forall (fun b => exists j, nth_error (r_st (pr Σ 24)) j = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σ)) 24 j) (ql Σ ++ qg Σ).
Hypothesis HLay : layout_ok (lay Σ).
Hypothesis HAw : A_bytes (aw Σ) <= CREDIT0.
Hypothesis HEg : rt_eager (recp Σ c i) <= 2 ^ 38.
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation r := (pr Σ c).
#[local] Notation mc := (MaxCount c).
#[local] Notation nf := (Z.of_nat (length (r_fl (pr Σ c)))).
#[local] Notation mfa := (r_mfa (pr Σ c)).
#[local] Notation new := (round_fa (4 * (Z.of_nat (length (r_fl (pr Σ c))) + MaxCount c / 2))).
#[local] Notation cd_ms := (cd_msD Σ c i ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
#[local] Notation cd_post := (cd_postD Σ m c lo ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc).
#[local] Notation svc := (cs_svc Σ m c i lo ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc).

Definition dd_K (ms' : machine_state) : Prop := exists ms0, svc ms0 /\ ms' = nretA ms0 (cs_eff Σ c).

Lemma dd_svc_regs : forall ms, svc ms -> ms_svc_pending ms = Some (Z_to_bv 64 222)
  /\ areg ms 10 = Z_to_bv 64 (fa SB c + mfa) /\ areg ms 11 = Z_to_bv 64 (new - mfa) /\ areg ms 12 = Z_to_bv 64 3
  /\ areg ms 13 = Z_to_bv 64 50 /\ areg ms 15 = Z_to_bv 64 0
  /\ dd_K (nretA ms (mkEffect (Z_to_bv 64 (fa SB c + mfa)) [] [(Z_to_bv 64 (fa SB c + mfa), Z_to_bv 64 (new - mfa))])).
Proof.
  intros ms H. pose proof H as (t0' & t1' & t2' & a6' & t3' & t4' & t5' & t6' & m1 & jr & junk & shj & mm0 & md0 & stj & ws & chs & rand
                                & exh & pad & nal & nfr & q0 & q1 & q2 & q3 & -> & _).
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  eexists. split; [exact H | reflexivity].
Qed.

Theorem cd_lift : cps bsegs (ASTA RTA Σ PMc (eq cd_ms)) (ASTA RTA (recp Σ c i) PMc (cd_post (recp Σ c i))).
Proof using FDO MST FC HG HA Hc Hi Hinit HRW Hcl Hcnt ST HLO HLO2 HSP MI Hlive Hdep HQB HLay HAw HEg.
  destruct (Z_lt_ge_dec (Z.of_nat (length (ca Σ c))) mc) as [Hlt|Hge].
  -
    apply (dd_evt_cps Σ (recp Σ c i) PMc _ _ MST eq_refl eq_refl); [| reflexivity |].
    + rewrite (rt_eager_recp Σ c i Hc), recp_mfa, Z.eqb_refl, (cd_full_false c (ca Σ c) Hlt). lia.
    + exact (cd_push_evt Σ m c i st lo ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
               HG HA Hc Hi Hinit ST HLO HLO2 HSP MI Hlive Hdep HQB Hlt).
  - assert (Hfull : Z.of_nat (length (ca Σ c)) = mc) by lia.
    destruct (Z_le_gt_dec (4 * (nf + mc / 2)) mfa) as [Hfast|Hgrow].
    +
      apply (dd_evt_cps Σ (recp Σ c i) PMc _ _ MST eq_refl eq_refl); [| reflexivity |].
      * rewrite (rt_eager_recp Σ c i Hc), recp_mfa, Z.eqb_refl, (cd_full_true c (ca Σ c) Hfull).
        unfold dh_mfa, dh_grow, dh_nf, ureg. cbn [r_mfa r_fl]. rewrite (proj2 (Z.ltb_ge _ _) Hfast). lia.
      * exact (cd_fast_evt Σ m c i st lo ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                 HG HA Hc Hi Hinit HRW Hcl ST HLO HLO2 HSP MI Hlive Hdep HQB Hfull Hfast).
    +
      assert (Hgrow' : mfa < 4 * (nf + mc / 2)) by lia.
      pose proof (cs_nums Σ c Hc HRW Hgrow') as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14).
      pose proof (cs_eager Σ c i Hc Hfull Hgrow') as EG.
      pose proof (dk_rb Σ HG c Hc) as (B1 & B2 & B3 & B4).
      pose proof (dk_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
      pose proof HG as (_ & (HR & _) & _).
      assert (Hfam : (fa SB c + mfa) mod 4096 = 0).
      { pose proof (cd_geo Σ HG) as (_ & (_ & X2 & _) & _). unfold fa, rb. pose proof N6 as X6.
        apply Z.mod_divide in X6; [|lia]. destruct X6 as (q & Eq).
        apply Z.mod_divide in X2; [|lia]. destruct X2 as (q2 & E2).
        rewrite Eq, E2. apply Z.mod_divide; [lia|]. exists (q2 * 16 + c * 2 ^ 20 + 0xE0000 + q * 64). lia. }
      eapply (cps_seq bsegs).
      * assert (W1 : forall ms, eq cd_ms ms -> evt bsegs svc ms)
          by (intros ms <-; exact (cs_A Σ m c i st lo ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                                     HG HA Hc Hi Hinit HRW Hcl ST HLO HLO2 HSP MI Hfull Hgrow')).
        exact (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1).
      * eapply (cps_seq bsegs).
        -- apply (FC Σ (recp Σ c i) PMc svc dd_K (fa SB c + mfa) (new - mfa) FDO MST eq_refl eq_refl eq_refl eq_refl).
           ++ rewrite EG. lia.
           ++ exact HEg.
           ++ exact HLay.
           ++ exact HAw.
           ++ lia.
           ++ exact N11.
           ++ exact Hfam.
           ++ unfold fa, rb in *. lia.
           ++ unfold fa, rb in *. lia.
           ++ exact dd_svc_regs.
        -- assert (W1 : forall ms, dd_K ms -> evt bsegs (cd_post (recp Σ c i)) ms)
             by (intros ms (ms0 & H & ->); exact (cs_B Σ m c i st lo ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                                                     HG HA Hc Hi Hinit HRW Hcl ST HLO HLO2 HSP MI Hlive Hdep HQB Hfull Hgrow' ms0 H)).
           exact (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow (recp Σ c i)) _ _ _ (fl_ASTA_mat_stable (recp Σ c i) PMc MST) W1).
Qed.

End CDeal.

End GWIN.
