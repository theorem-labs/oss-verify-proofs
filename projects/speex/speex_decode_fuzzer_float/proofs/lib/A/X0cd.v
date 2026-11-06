(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cy X1cp X1cj X1dd X1cg X1cs X1cm X1da X1cx X1cq X1d0.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X0j1 X0gi X0hr X0hb
X0hi X0j3 X0hn X0hs X0gp X0id X0gj X0hl X0gv X0ig X0ih
X0fy X0fg X0da X0g4 X0fq X0e4 X0e8 X0d9 X0e5 X0df X0g3
X0ci X0cr X0cp X0cn X0ca X0ck X0ce X0cf X0cg X0ch.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X173 X18c X17w X183 X19m X188 X18d X17a X18y X174 X186 X17g X191 X192 X16j X161 X13v X16p X16b X14p X14t X13u X14q X140 X16o X133 X13c X13a X138 X12v X135 X12z X130 X131 X132.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X188 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18d OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X174 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X186 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17g OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X191 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X192 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13v OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13u OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X140 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X133 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X138 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12v OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X135 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12z OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X130 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X131 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X132.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

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
End B_TWIN.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Lemma dd_evt_cps : forall (Σ Σ' : rtsA) (PMc : Model -> Prop) (ms : machine_state) (Q : machine_state -> Prop),
mat_stable PMc -> lay Σ' = lay Σ -> sec Σ' = sec Σ -> rt_eager Σ' = rt_eager Σ -> aw Σ' = aw Σ ->
evt asegs Q ms -> cps asegs (ASTA RTA Σ PMc (eq ms)) (ASTA RTA Σ' PMc Q).
Proof.
intros Σ Σ' PMc ms Q MST El Es Ee Ea HE.
assert (W1 : forall ms', eq ms ms' -> evt asegs Q ms') by (intros ms' <-; exact HE).
eapply (cps_conseq asegs); [exact (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1)
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
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis HLO : l_ACEIL (lay Σ) <= lo.
Hypothesis HLO2 : lo + 0x400 <= bv_unsigned sp.
Hypothesis HSP : bv_unsigned sp <= 2 ^ 47.
Hypothesis MI : mem_inv asegs m.
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

Theorem cd_lift : cps asegs (ASTA RTA Σ PMc (eq cd_ms)) (ASTA RTA (recp Σ c i) PMc (cd_post (recp Σ c i))).
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
eapply (cps_seq asegs).
* assert (W1 : forall ms, eq cd_ms ms -> evt asegs svc ms)
by (intros ms <-; exact (cs_A Σ m c i st lo ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
HG HA Hc Hi Hinit HRW Hcl ST HLO HLO2 HSP MI Hfull Hgrow')).
exact (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1).
* eapply (cps_seq asegs).
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
-- assert (W1 : forall ms, dd_K ms -> evt asegs (cd_post (recp Σ c i)) ms)
by (intros ms (ms0 & H & ->); exact (cs_B Σ m c i st lo ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
HG HA Hc Hi Hinit HRW Hcl ST HLO HLO2 HSP MI Hlive Hdep HQB Hfull Hgrow' ms0 H)).
exact (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow (recp Σ c i)) _ _ _ (fl_ASTA_mat_stable (recp Σ c i) PMc MST) W1).
Qed.

End CDeal.
