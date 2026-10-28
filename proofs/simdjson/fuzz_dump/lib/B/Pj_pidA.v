(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import SjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjS1Out SjTape.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2 Sj_new Sj_h_dtor Sj_h_alloc Atp_setcapA Sj_h_setmd Atp_fzwA Sj_h_deldtor Atp_pdtorA Sj_h_layout Atp_hkit3A Sj_stage2_iface Sj_h_parsew Atp_parseA Atp_createA Atp_activewA Atp_activeA Atp_pidiA Pj_defsA Pj_hdefsA Pj_pdtor2A Pj_pidwA Pj_pidw2A Pj_pidw3A Atp_hkit4A Atp_hkit5A Pj_pid1A Pj_pid2A Pj_pid3A Pj_pid4A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Pid.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTF : rt_contracts_f RT.
Hypothesis PARSE : parse_cps RT.
Hypothesis ALLOC : allocate_cps RT.
Hypothesis CREATE : create_cps RT.
Hypothesis NEWA : new_cps RT e_newarr_nt.
Hypothesis AFC : forall Σ m, ART RT Σ m -> cli_got_nothrow m.
Hypothesis AFV : forall Σ m, ART RT Σ m -> vt_dpi m.
Hypothesis AFI : forall Σ m, ART RT Σ m -> vt_impl m.

Lemma pj_statics_keep : forall (m m' : mem) (live : list (Z * Z)) (frames : list (Z * nat)) (sp P RES : Z),
  SEGTOP_A <= P -> SEGTOP_A <= RES ->
  (forall a : word, aclient live frames sp (bv_unsigned a) -> outside (pid_XA P RES) (bv_unsigned a) -> m' a = m a) ->
  pj_locA m -> lockwA m -> pj_locA m' /\ lockwA m'.
Proof.
  intros m m' live frames sp P RES HP HR PRES LOC LK.
  assert (AG : agree_on (fun x => PJ_LOC_LO_A <= x < PJ_LOC_HI_A \/ PJ_LOCKW_A <= x < PJ_LOCKW_A + 4) m m').
  { intros a Ha. apply PRES.
    - right; left. apply client_static_intro. unfold PJ_LOC_LO_A, PJ_LOC_HI_A, PJ_LOCKW_A in Ha. lia.
    - unfold pid_XA, SJ_W. cbn [outside]. unfold PJ_LOC_LO_A, PJ_LOC_HI_A, PJ_LOCKW_A, SEGTOP_A in *. repeat split; try exact I; lia. }
  split; [apply (pj_locA_agree m m' LOC)| apply (lockwA_agree m m' LK)]; intros a Ha; apply AG; [left| right]; exact Ha.
Qed.

Theorem pj_pid_okA : pj_pid_cpsA RT (pj_libA sj_lib) (pdone2 RT).
Proof using AF RTF PARSE ALLOC CREATE NEWA AFC AFV AFI.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P RES d bs p1 p17 p57 jr lo
    FDO MST -> -> -> -> -> -> -> D0 BSL BS INLV FOBJ0 PINIT RLO RHI RAL RC0 LVPOS LVB FRB CR0 (LIB0 & LOC0 & LK0) ART0 MI0 ST0 LOW LOR SPT SPA FRM.
  cbv zeta. set (len := Z.of_nat (length bs)) in *. set (cap := Z.max len 32) in *.
  assert (LEN0 : 0 <= len) by (subst len; lia).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof (mcost_nonneg (len + 64) ltac:(lia)) as MC0. pose proof (mcost_nonneg (len + 64 + 64) ltac:(lia)) as MC1.
  assert (SC0 : 0 <= S2A_COST len) by (unfold S2A_COST, Sj_num_iface.NUMA_CREDIT; lia).
  unfold pj_pid_costA in CR0. change Atp_pid1A.pid_cost6 with pid_cost6 in CR0. fold len in CR0. fold cap in CR0.
  assert (CB1 : pid_cost6 cap <= rt_credit RT Σ) by lia.
  pose proof FOBJ0 as (_ & _ & (f0 & k0 & INF0 & FLO0 & _) & _). pose proof (af_frames_align RT AF Σ m f0 k0 ART0 INF0) as (_ & FSEG0).
  intros T c HcF Hk.
  apply (pid_front RT AF ALLOC CREATE AFI Σ PMc ra sp gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P RES d bs p1 p17 p57 jr lo
           FDO MST D0 BSL BS INLV FOBJ0 PINIT RLO ltac:(lia) RC0 ltac:(unfold LIVE_MAX in *; lia) CB1 LIB0 ART0 MI0 ST0 LOW LOR SPT SPA FRM T c HcF).
  intros c2 ((Σ2 & impl & idx & oc & ia & tape & sbuf & Hc2 & LV2 & FRS2 & SP2 & CR2 & (IM0 & IM16) & (IX0 & IX16) & (OC0 & OC16) & (IA0 & IA16) & (TP0 & TP16) & (SB0 & SB16)) & FC2).
  destruct (ASTA_unpack_f RT Σ2 _ _ c2 Hc2 FC2) as (ms2 & (m2 & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & j & q1 & q17 & q57 & q12 & q28 & q50
                                                    & -> & ART2 & MI2 & ST2 & FR2 & PC2 & FOBJ2 & IC2 & RC2 & BS2 & LIB2 & CH2) & FRM2 & Hc2'). clear Hc2.
  cbn [ms_fcsr] in FRM2. fold len in Hc2'. fold cap in Hc2', PC2, IC2, LV2, CR2.
  assert (LOW2 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SP2; exact LOW).

  assert (FIN : forall cost (CP : list (Z * Z) -> Prop), pid_cost6 cap + cost <= pid_cost6 cap + mcost (len + 64) + S2A_COST len ->
            (forall cp, CP cp -> (exists COPY, cp = [(COPY, len + 64)] /\ 0 < COPY /\ len <= SJ_PADMAX) \/ cp = []) ->
            forall c', (pid_post RT Σ2 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo RES P (rt_live RT Σ) impl idx oc ia tape sbuf cap len CP cost m2 c' /\ cfrm0 c') ->
            realizes bsegs c' T).
  { intros cost CP CC HCP c' ((Σ' & cp & Hc' & LV' & CP' & FRS' & SP' & CR') & FC'). apply Hk. split; [| exact FC'].
    exists Σ', cp, impl, idx, oc, ia, tape, sbuf. cbv zeta. fold len. fold cap.
    split; [| split; [rewrite LV', LV2; reflexivity| split; [exact (HCP cp CP')| split; [repeat split; assumption|
            split; [rewrite FRS'; exact FRS2| split; [rewrite SP'; exact SP2|]]]]]].
    2:{ unfold pj_pid_costA. change Atp_pid1A.pid_cost6 with pid_cost6. fold len. fold cap. rewrite CR2 in CR'. fold len in CR'. fold cap in CR'. lia. }
    eapply ASTA_conseq; [exact Hc'|]. intros ms (v & m' & RS' & AFT' & PRES' & (r & j20 & RC' & R64 & OK' & RZ) & LIB' & PD' & FO' & (p1' & p17' & p57' & lb & lbc & PC')). exists v, m'.
    assert (CH : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (bv_unsigned a) -> outside (pid_XA P RES) (bv_unsigned a) -> m' a = m a).
    { intros a Ha Hout. rewrite (PRES' a); [exact (CH2 a Ha Hout)| rewrite FRS2; exact Ha| exact Hout]. }
    split; [exact RS'|]. split; [exact AFT'|]. split; [exact CH|].
    split; [exists r, j20; split; [exact RC'| split; [exact R64| split; [exact OK'| intros E; unfold SJ_PADMAX; exact (RZ E)]]]|].
    split; [| split; [exact PD'| split; [exact FO'|]]].
    - split; [exact LIB'|]. exact (pj_statics_keep m m' _ _ _ P RES ltac:(clear - FSEG0 FLO0; lia) ltac:(clear - SP0R LOW LOR RLO; unfold PID_STACK, SEGTOP_A, STACK_WIN, USTACK_TOP in *; lia) CH LOC0 LK0).
    - pose proof PC' as X. unfold pid_cells in X.
      change ([C1 z8; CB 7 p1'; C8 (Z_to_bv 64 impl); C1 z8; CB 3 p17'; C4 (Z_to_bv 64 12); C8 (Z_to_bv 64 tape); C8 (Z_to_bv 64 sbuf); C8 (Z_to_bv 64 cap);
               C8 (Z_to_bv 64 4294967295); C1 z8; CB 7 p57'; C8 lb; C8 lbc])
        with ([C1 z8; CB 7 p1'; C8 (Z_to_bv 64 impl); C1 z8; CB 3 p17'; C4 (Z_to_bv 64 12)] ++ [C8 (Z_to_bv 64 tape); C8 (Z_to_bv 64 sbuf)] ++
              [C8 (Z_to_bv 64 cap); C8 (Z_to_bv 64 4294967295); C1 z8; CB 7 p57'; C8 lb; C8 lbc]) in X.
      apply Sj_stage1_kit.rw_cells_app in X. destruct X as [_ X]. apply Sj_stage1_kit.rw_cells_app in X. destruct X as [X _].
      cbn [cells_size csize Nat.add] in X. replace (P + Z.of_nat 24) with (P + 24) in X by lia. exact X. }
  destruct (Z_le_dec len 1048512) as [LE|GT].
  - apply (pid_main RT AF NEWA (rf_asan_memset RT RTF) (rf_asan_memcpy RT RTF) (rf_memcmp RT RTF) PARSE AFC AFV
             Σ2 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 m2 lo RES P d cap impl idx oc ia tape sbuf bs
             (rt_live RT Σ) jr j q1 q17 q57 q12 q28 q50 FDO MST LE eq_refl D0 BS2 INLV ART2 MI2 ST2 FR2 PC2 FOBJ2 IC2 RC2 LIB2 LV2 LVPOS IM16 IX16 OC16 IA16 TP16 SB16);
      [rewrite FRS2; unfold S2A_FRAMES, Sj_num_iface.NUMA_FRAMES, PID_FRAMES in *; lia| rewrite CR2; unfold cap, len in *; lia
      | rewrite LV2; cbn [length]; unfold LIVE_MAX in *; lia| exact RLO| exact RHI| exact LOW2| exact LOR| exact SPT| exact SPA| exact FRM2
      | split; [exact Hc2'| apply (cfrm0_of_asta RT Σ2 PMc (eq _) c2 Hc2'); intros ms0 <-; exact FRM2] |].
    apply FIN; [fold len; lia|]. intros cp (COPY & -> & CPOS). left. exists COPY. unfold SJ_PADMAX. split; [reflexivity| split; [exact CPOS| exact LE]].
  - apply (pid_big RT AF (rf_asan_memset RT RTF)
             Σ2 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 m2 lo RES P d len cap impl idx oc ia tape sbuf
             (rt_live RT Σ) jr j q1 q17 q57 q12 q28 q50 FDO MST ltac:(lia) ART2 MI2 ST2 FR2 PC2 FOBJ2 IC2 RC2 LIB2 LV2 LVPOS
             ltac:(subst cap; change (2^26) with 67108864 in *; lia) IM16 RLO RHI LOW2 LOR SPT SPA FRM2);
      [split; [exact Hc2'| apply (cfrm0_of_asta RT Σ2 PMc (eq _) c2 Hc2'); intros ms0 <-; exact FRM2] |].
    apply FIN; [lia|].
    intros cp ->. right. reflexivity.
Qed.

Lemma pdone2_fp : pdone_fpA RT (pdone2 RT).
Proof using AF.
  intros Σ Σ' m m' P L PD ARTm FRS LV EQ. destruct PD as [PD|PD].
  - left.
    destruct PD as (impl & tape & sbuf & idx & oc & ia & nt & ns & nidx & noc & nia & dcap & pre8 & mid & mid2 & rest & ipre8 & imid & irest
                    & FOBJ & PC & INM & I8 & IC & INS & INT & INA & INO & INX & NS0 & NT0 & NA0 & NO0 & NX0 & ND6 & EL).
    exists impl, tape, sbuf, idx, oc, ia, nt, ns, nidx, noc, nia, dcap, pre8, mid, mid2, rest, ipre8, imid, irest.
    pose proof FOBJ as (_ & _ & _ & _).
    split. { apply (fobj_agree RT AF Σ Σ' m m' P 80 ARTm FOBJ FRS). intros a Ha. cbv beta in Ha. change ((80 + 7) / 8) with 10 in Ha. apply EQ. right; left. exact Ha. }
    split. { apply (rw_cells_agree_nw bsegs m m' _ _ PC). intros a Ha. unfold pd_cells in Ha. cbn [cells_size csize Nat.add] in Ha. apply EQ. left. lia. }
    rewrite LV. split; [exact INM|]. split; [exact I8|].
    split. { apply (rw_cells_agree_nw bsegs m m' _ _ IC). intros a Ha. unfold dl_cells in Ha. cbn [cells_size csize Nat.add] in Ha. apply EQ. right; right. exists impl, 96. split; [exact INM| lia]. }
    repeat (split; [assumption|]). exact EL.
  - right.
    destruct PD as (impl & tape & sbuf & idx & oc & ia & nt & ns & nidx & noc & nia & copy & ncopy & dcap & pre8 & mid & mid2 & rest & ipre8 & imid & irest
                    & FOBJ & PC & INM & I8 & IC & INS & INT & INA & INO & INX & INC & NS0 & NT0 & NA0 & NO0 & NX0 & NC0 & ND6 & NIC & EL).
    exists impl, tape, sbuf, idx, oc, ia, nt, ns, nidx, noc, nia, copy, ncopy, dcap, pre8, mid, mid2, rest, ipre8, imid, irest.
    split. { apply (fobj_agree RT AF Σ Σ' m m' P 80 ARTm FOBJ FRS). intros a Ha. cbv beta in Ha. change ((80 + 7) / 8) with 10 in Ha. apply EQ. right; left. exact Ha. }
    split. { apply (rw_cells_agree_nw bsegs m m' _ _ PC). intros a Ha. unfold pd_cells in Ha. cbn [cells_size csize Nat.add] in Ha. apply EQ. left. lia. }
    rewrite LV. split; [exact INM|]. split; [exact I8|].
    split. { apply (rw_cells_agree_nw bsegs m m' _ _ IC). intros a Ha. unfold dl_cells in Ha. cbn [cells_size csize Nat.add] in Ha. apply EQ. right; right. exists impl, 96. split; [exact INM| lia]. }
    repeat (split; [assumption|]). exact EL.
Qed.

End Pid.
