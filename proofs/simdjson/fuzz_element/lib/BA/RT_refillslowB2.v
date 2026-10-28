(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState ITree.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs D_kit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_thread R_m2s. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_refill R_refill_ic R_getfrom R_getfrom_A R_popfree R_popfree_B R_popfree_T R_mmapfixed R_prim_lists R_prim_kit R_ensurefa R_ensurefa_B R_getfrom_M R_getfrom_B2 R_prim_poison RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeC RT_freeA2 RT_refillstmt RT_refillst RT_refillwf RT_rfkit RT_refillart RT_rfbytes RT_refillrun RT_refillslow RT_refillnew RT_refillslowB RT_refillslowM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.
Section RfSlowB2.
Variables (Σ : rtsA) (m : mem) (c lo : Z) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
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
Hypothesis Hslow : Z.of_nat (length (r_fl (pr Σ c))) < MaxCount c / 2.
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation TCX := (l_TCX (lay Σ)).
#[local] Notation PRB := (l_PRB (lay Σ)).
#[local] Notation R := (rinfo (RIS_of (l_SB (lay Σ))) c).
#[local] Notation r := (pr Σ c).
#[local] Notation S := (ClassSize c).
#[local] Notation au := (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
#[local] Notation mu := (r_muser (pr Σ c)).
#[local] Notation nf := (Z.of_nat (length (r_fl (pr Σ c)))).
#[local] Notation n := (MaxCount c / 2).
#[local] Notation P := (pc_addr (l_T (lay Σ)) c).
#[local] Notation msz := (rf_msz (pr Σ c) c).
#[local] Notation newc := (rf_newc (pr Σ c) c).
#[local] Notation new := (round_fa (4 * (Z.of_nat (length (r_fl (pr Σ c))) + rf_newc (pr Σ c) c))).
#[local] Notation WR := (W_R (l_T (lay Σ)) (l_SB (lay Σ)) c (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) (bv_unsigned sp)).

Lemma rsb2_c31 : 1 <= c <= 31. Proof using Hc. clear - Hc. lia. Qed.

Definition rr_eff2 : SyscallEffect :=
  mkEffect (Z_to_bv 64 (fa (l_SB (lay Σ)) c + r_mfa (pr Σ c))) []
    [(Z_to_bv 64 (fa (l_SB (lay Σ)) c + r_mfa (pr Σ c)),
      Z_to_bv 64 (round_fa (4 * (Z.of_nat (length (r_fl (pr Σ c))) + rf_newc (pr Σ c) c)) - r_mfa (pr Σ c)))].

Lemma rr_slowB2 : r_mfa r < 4 * (nf + newc) ->
  forall ms, rr_svc2 Σ m c lo ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
  evt asegs (rf_post fc Σ c lo ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m) (nretA ms rr_eff2).
Proof using HW0 HA Hc Hca HROOM MI ST HLO HLO2 HSP Hslow.
  pose proof rsb2_c31 as Hc31.
  intros Hgrow ms P1.
  destruct P1 as (t0' & t1' & t2' & a6' & t3' & t4' & t5' & t6' & m1 & junk & gjunk & ws & chs1 & rand & exh & pad & nal & nfr
                  & q0 & q1 & q2 & q3 & mm0 & md0 & -> & MU1 & WM1 & MI1 & MC1 & Hnal & Hpad & CHL1 & Hws & Hpre
                  & FR1 & PC1 & K1 & SU1 & SH1 & SS1).
  pose proof (rr_T Σ HW0) as HT. pose proof (rr_SB Σ HW0) as HSB. pose proof (rr_lo Σ lo HW0 HLO) as HLOH.
  pose proof (rr_tsep Σ HW0) as HTS.
  pose proof (rr_usp Σ lo sp HW0 HLO HLO2 HSP) as (U1 & U2 & U3).
  pose proof (rr_geo Σ HW0) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
  pose proof (rn_regwf Σ c HW0 Hc31) as HWc. pose proof HWc as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11).
  pose proof (rr_slow_nums Σ c HW0 Hc HROOM Hslow) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11).
  pose proof (rb_nums Σ c HW0 Hc HROOM Hslow) as (K1' & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14).
  pose proof (rm_new Σ c HW0 Hc HROOM Hslow Hgrow) as (NW1 & NW2 & NW3 & NW4 & NW5).
  assert (RS : 0 <= usp - 32 < 2 ^ 64) by (clear - U1 U3; lia).
  assert (HSB0 : 0 <= SB) by (clear - G9 G10; unfold K_HIGH_SHADOW_hi in *; lia).
  set (sa := shad (rb SB c + mu)) in *. set (sn := msz / 8) in *.
  assert (EA0 : rb SB c + mu = (rb SB c + au) + 8 * ((mu - au) / 8)) by (clear - K7 K8 K12 K2; lia).
  assert (Esa : sa = shad (rb SB c + au) + (mu - au) / 8) by (unfold sa; rewrite EA0; apply shad_add8).
  assert (SAR : shad (rb SB c) <= shad (rb SB c + au) /\ shad (rb SB c + au) <= sa /\ sa + sn <= shad (fa SB c) /\ 0 <= sn).
  { pose proof (shad_mono' (rb SB c) (rb SB c + au) ltac:(lia)) as Q1.
    assert (E2 : rb SB c + mu + msz = rb SB c + mu + 8 * sn) by (unfold sn; clear - K9; lia).
    pose proof (shad_mono' (rb SB c + mu + msz) (fa SB c) ltac:(unfold fa; clear - N3; unfold kUserCap in *; lia)) as Q3.
    rewrite E2, shad_add8 in Q3. fold sa in Q3.
    assert (0 <= (mu - au) / 8) by (apply Z.div_pos; clear - K2; lia). assert (0 <= sn) by (unfold sn; apply Z.div_pos; clear - N1; lia).
    clear - Q1 Q3 Esa H H0. lia. }
  destruct SAR as (SAR1 & SAR2 & SAR3 & SAR4).

  set (esa := shad (fa SB c + r_mfa r)). set (esn := (new - r_mfa r) / 8).
  assert (HFA : fa SB c = rb SB c + 0xE0000000) by reflexivity.
  assert (EAR : shad (fa SB c) <= esa /\ esa + esn <= shad (rb SB c + 2 ^ 32) /\ 0 <= esn).
  { assert (EF : fa SB c + r_mfa r = fa SB c + 8 * (r_mfa r / 8)) by (clear - W6; unfold kUMap in *; lia).
    assert (EN : fa SB c + new = fa SB c + r_mfa r + 8 * esn) by (unfold esn; clear - NW3 NW4 W6; unfold kUMap in *; lia).
    pose proof (shad_mono' (fa SB c + new) (rb SB c + 2 ^ 32) ltac:(rewrite HFA; clear - NW2; lia)) as Q3.
    rewrite EN, shad_add8 in Q3. fold esa in Q3.
    pose proof (shad_mono' (fa SB c) (fa SB c + r_mfa r) ltac:(clear - W5; lia)) as Q1. fold esa in Q1.
    assert (0 <= esn) by (unfold esn; apply Z.div_pos; clear - NW3; lia). clear - Q1 Q3 H. lia. }
  destruct EAR as (EAR1 & EAR2 & EAR3).
  assert (SHR : SHB <= shad (rb SB c) /\ shad (rb SB c + 2 ^ 32) <= 2 ^ 44 + SHB).
  { split; [apply shad_lo; unfold rb; clear - HSB0 Hc31; lia | apply shad_hi; unfold rb; clear - G4 G10 G11 G13 Hc31; lia]. }
  assert (SFA : shad (rb SB c + au) <= shad (fa SB c)) by (clear - SAR2 SAR3 SAR4; lia).
  destruct (stk_split asegs m1 (shad (rb SB c)) esa (shad (rb SB c + 2 ^ 32)) SS1 ltac:(clear - SAR1 SFA EAR1 EAR2 EAR3; lia)) as (_ & Y1).
  destruct (stk_split asegs m1 esa (esa + esn) (shad (rb SB c + 2 ^ 32)) Y1 ltac:(clear - EAR2 EAR3; lia)) as (Y2 & _).
  destruct (stk_carve asegs m1 esa (esa + esn) (Z.to_nat esn) Y2 ltac:(clear - EAR3; lia)) as (_ & (shj & SHJ)).
  replace (esa + esn - Z.of_nat (Z.to_nat esn)) with esa in SHJ by (clear - EAR3; lia).

  eapply evt_cut.
  { apply (gfa_B2_spec PCP PCP_stmt PCP_framed (Z_to_bv 64 refill_retB) (Z_to_bv 64 (usp - 32)) gp t0' t1' t2' a6' (Z_to_bv 64 P) (Z_to_bv 64 n)
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m1 (l_ACEIL L) SB c R (P + 16) n nf (r_mfa r) new au mu msz sa sn
             esa esn T TCX mm0 md0 shj ws chs1 rand exh pad nal nfr q0 q1 q2 q3 lo gjunk); rewrite ?(unsigned_lit (usp - 32)) by exact RS.
    all: try assumption. all: try reflexivity.
    all: try (clear - K10; lia). all: try (clear - Hslow; lia). all: try (clear - N7 N8 N9; lia).
    all: try (clear - N3; lia). all: try (clear - N10; lia). all: try (clear - N11; lia).
    all: try (clear - Hgrow; unfold rf_newc in Hgrow; exact Hgrow). all: try (clear - NW2; unfold rf_newc in NW2; exact NW2).
    all: try (unfold pc_addr; clear - Hc31; lia). all: try (clear - HLO2; lia). all: try (clear - U3; lia). }
  intros ms2 P2. destruct P2 as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m2 & -> & MU2 & WM2 & MI2
                                 & LK2 & RC2 & RT2 & FL2 & CH2 & ZU2 & SN2 & EN2 & MM2 & WW2 & MG2 & TC2 & PC2' & ST2).
  rewrite (ret_pc_even refill_retB) by (unfold refill_retB; first [reflexivity | lia]).
  change (pfa_newc au mu msz S) with newc in *.
  rewrite (unsigned_lit (usp - 32)) in ST2 by exact RS. unfold gfa_B2_W in MU2. rewrite (unsigned_lit (usp - 32)) in MU2 by exact RS.
  assert (HR0 : SB + 2 ^ 37 <= R /\ R + 128 <= SB + 2 ^ 37 + 4096) by (unfold rinfo, RIS_of; clear - Hc31; lia).
  assert (HRB : SB + 2 ^ 32 <= rb SB c /\ rb SB c + 2 ^ 32 <= SB + 2 ^ 37) by (unfold rb; clear - Hc31; lia).
  assert (HMU : mu + msz <= 0xE0000000 /\ new <= 2 ^ 29) by (clear - N3 NW2; lia).
  assert (HPP : T + 208 <= P /\ P + 80 <= T + 2768) by (unfold pc_addr; clear - Hc31; lia).
  assert (TSEP : (T + 4096 <= 0x10000 \/ SEGTOP_A <= T) /\ (T + 4096 <= SHB \/ 2 ^ 44 + SHB <= T) /\ (T + 4096 <= PRB \/ PRB + 0x2000011000 <= T)).
  { unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. clear - G6 G7 G8. split; [exact G6|]. split; [lia | exact G8]. }
  assert (PSEP : 2 ^ 44 + SHB <= PRB /\ PRB + 0x2000011000 <= l_ACEIL L /\ l_ACEIL L + 0x400 <= usp) by (unfold K_HIGH_SHADOW_hi, SHB in *; clear - G9 G13 U2; lia).
  set (W3' := [(R, R + 8); (R + 16, R + 56); (R + 68, R + 69); (R + 72, R + 80); (fa SB c, fa SB c + new); (esa, esa + esn);
               (T + 2872, T + 2888); (P + 16, P + 16 + 4 * n); (usp - 32 - 640, usp - 32)]) in MU2.
  assert (FR2 : rw_cells asegs m2 (usp - 32) [CB 8 junk; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_transport asegs _ m1 m2 _ _ FR1 MU2 WM2). unfold W3'. cbn [disjoint_from cells_size csize Nat.add].
    clear - HR0 HRB HFA HMU HPP PSEP G3 G10 G11 EAR2 SHR K10. unfold SHB in *. repeat split; lia. }
  assert (PC2 : pc_cells m2 P 0 (MaxCount c) S).
  { apply (rw_cells_transport asegs _ m1 m2 _ _ PC1 MU2 WM2). unfold W3'. cbn [disjoint_from cells_size csize Nat.add].
    clear - HR0 HRB HFA HMU HPP PSEP G3 G10 G11 SAR1 SAR2 SAR3 EAR1 EAR2 SFA SHR TSEP K10 K1' K2. unfold SHB, SEGTOP_A in *. repeat split; lia. }
  assert (KO2 : forall j, 1 <= j <= 31 -> j <> c -> pclass_rep T j true (ca Σ j) m2).
  { intros j Hj Hne. apply (pclass_rep_transport _ T j true _ m1 m2 (K1 j Hj Hne) MU2 WM2). unfold pclass_avoid, W3'. cbn [disjoint_from].
    assert (HPJ : T + 208 <= pc_addr T j /\ pc_addr T j + 80 <= T + 2768 /\ (pc_addr T j + 80 <= P \/ P + 80 <= pc_addr T j))
      by (unfold pc_addr; clear - Hj Hne Hc31; split; [lia|]; split; [lia|]; destruct (Z_lt_ge_dec j c); [left | right]; lia).
    clear - HR0 HRB HFA HMU HPP PSEP G3 G10 G11 SAR1 SAR2 SAR3 EAR1 EAR2 SFA SHR TSEP K10 K1' K2 HPJ. unfold SHB, SEGTOP_A in *. repeat split; lia. }
  assert (SH2 : bytes_at asegs m2 (shad (rb SB c + au)) (farun ((mu - au) / 8))).
  { apply (bytes_at_transport asegs _ m1 m2 _ _ SH1 MU2). rewrite farun_len. unfold W3'. cbn [disjoint_from].
    assert (0 <= (mu - au) / 8) by (apply Z.div_pos; clear - K2; lia). rewrite Z.max_r by exact H.
    clear - HR0 HRB HFA HMU HPP PSEP G3 G10 G11 SAR1 SAR2 SAR3 SAR4 EAR1 EAR2 EAR3 SHR TSEP Esa H K10 K1' K2. unfold SHB, SEGTOP_A in *. repeat split; lia. }

  assert (SU2 : stk asegs m2 (rb SB c + au) (rb SB c + (mu + msz))).
  { apply (stk_merge asegs m2 (rb SB c + au) (rb SB c + mu) (rb SB c + (mu + msz))).
    - exact (stk_wmono m1 m2 _ _ SU1 WM2).
    - pose proof (stk_of_rw_cells asegs m2 _ _ ZU2) as Z2. cbn [cells_size csize Nat.add] in Z2.
      rewrite Nat.add_0_r, Z2Nat.id in Z2 by (clear - N1; lia). replace (rb SB c + (mu + msz)) with (rb SB c + mu + msz) by ring. exact Z2.
    - clear - K2 N1. lia. }
  assert (SHN : bytes_at asegs m2 (shad (rb SB c + au)) (farun ((mu + msz - au) / 8))).
  { replace ((mu + msz - au) / 8) with ((mu - au) / 8 + sn) by (unfold sn; clear - K7 K8 K9 K12 K2; lia).
    apply (proj2 (bytes_farun_split m2 (shad (rb SB c + au)) ((mu - au) / 8) sn ltac:(apply Z.div_pos; clear - K2; lia) SAR4)).
    split; [exact SH2|]. rewrite <- Esa. exact (farun_of_cells m2 sa sn SAR4 SN2). }
  assert (SS2 : stk asegs m2 (shad (rb SB c)) (shad (rb SB c + 2 ^ 32))) by exact (stk_wmono m1 m2 _ _ SS1 WM2).
  set (ws0 := ws ++ repeat (Z_to_bv 64 0) (Z.to_nat ((new - r_mfa r) / 4))) in *.
  assert (Hws0 : 4 * Z.of_nat (length ws0) = rf_mfa r c).
  { unfold ws0. rewrite length_app, repeat_length, Nat2Z.inj_add, Z2Nat.id by (apply Z.div_pos; clear - NW3; lia). rewrite NW1.
    clear - Hws NW3 NW4 W6. unfold kUMap in *. lia. }
  assert (Hpre0 : firstn (length (r_fl r)) ws0 = map (cpw c) (r_fl r)).
  { unfold ws0. rewrite firstn_app. replace (length (r_fl r) - length ws)%nat with 0%nat by (clear - Hws W7; lia).
    rewrite firstn_O, app_nil_r. exact Hpre. }
  rewrite <- NW1 in RC2.
  destruct (rr_newreg Σ c HW0 Hc31 Hslow m2 ws0 LK2 RC2 ltac:(exists rand, (Z_to_bv 8 0), pad, (nal + n), nfr, q0, q1, q2, q3; exact RT2)
              FL2 Hws0 Hpre0 SU2 SHN SS2) as (REG & NEW).

  assert (CHS : exists chs', u32arr asegs m2 (P + 16) chs' /\ length chs' = 16%nat /\ firstn (Z.to_nat n) chs' = map (cpw c) (refill_ca r c)).
  { destruct (rf_slow r c Hc31 HWc Hslow) as (_ & E2).
    assert (HLW : (length (r_fl r) + Z.to_nat newc <= length ws0)%nat) by (clear - Hws0 NW1 K6 K4; lia).
    pose proof (carve_prefix (r_fl r) ws0 (length (r_st r)) (Z.to_nat newc) c Hpre0 HLW) as CP.
    replace (Z.of_nat (length (r_fl r) + Z.to_nat newc)) with (nf + newc) in CP by (clear - K4; lia).
    assert (Hfl : length (rf_fl r c) = (length (r_fl r) + Z.to_nat newc)%nat).
    { pose proof (rf_fl_len r c K4) as X. unfold rf_nf in X. clear - X K4. lia. }
    rewrite <- Hfl in CP.
    exists (dest (carve ws0 (nf + newc) au S (Z.to_nat newc)) chs1 (nf + newc - n) (Z.to_nat n)).
    split; [exact CH2|]. split; [rewrite dest_length; exact CHL1|]. rewrite E2.
    replace (nf + newc - n) with (Z.of_nat (length (rf_fl r c) - Z.to_nat n)) by (clear - Hfl K3 K4 K10; lia).
    apply (dest_prefix (rf_fl r c) _ chs1 c (length (rf_fl r c) - Z.to_nat n) (Z.to_nat n) CP ltac:(clear - Hfl K3 K4 K10; lia)
             ltac:(rewrite CHL1; clear - K10; lia)).
    intros i Hi. unfold rf_fl in Hi. apply in_app_or in Hi as [Hi|Hi].
    - pose proof (proj1 (Forall_forall _ _) W9 i Hi) as (Xi & _).
      split; [apply Z.div_pos; clear - Xi K11; nia|]. apply Z.div_lt_upper_bound; [lia|]. clear - Xi K13 K4 K11. nia.
    - apply (proj2 (in_rev _ _)) in Hi. apply in_map_iff in Hi as (j & <- & Hj). apply in_seq in Hj.
      split; [apply Z.div_pos; clear - Hj K11; nia|]. apply Z.div_lt_upper_bound; [lia|]. clear - Hj K13 K4 K11. nia. }

  apply (rr_finish Σ m c lo ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc HW0 HA Hc Hca HROOM MI ST HLO HLO2 HSP
           z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 m2 junk).
  - apply (munch_trans WR m m1 m2 MU1). apply (munch_weaken W3' WR m1 m2); [|exact MU2].
    unfold W3', W_R. clear - HR0 HRB HFA HMU HPP SAR1 SAR2 SAR3 SAR4 SFA EAR1 EAR2 EAR3 K2 K10 N1 U1. solve_sub_fp.
  - exact (wmono_trans asegs _ _ _ WM1 WM2).
  - exact MI2.
  - exact REG.
  - exact CHS.
  - exact PC2.
  - exact KO2.
  - exact NEW.
  - exact FR2.
  - exact ST2.
Qed.

End RfSlowB2.

End GWIN.
