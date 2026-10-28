(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSymDrive BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX BLFrame BMem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel BReach BazyRestrict BazyLedger BazySR BazyNodes.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsDriverLaws BsSR BsChain BakeStackRep BllocWf BllocKit BllocRep BllocRepFacts BllocRepX BecLazy BsDepotInv BsDepotHash BG_Malloc2 BG_MallocLarge3 BG_MallocAll BS_InstDefs RtB_Iface.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section Laws3.
  Context {HCEIL : HeapCeil}.
  Variable p : iparams.

  Lemma stk_of_S : forall (s : ast) m lo hi,
    awin_vis s m -> (forall y, lo <= y < hi -> in_rangesb (wa y) (a_S s) = true) ->
    AIMG_TOP <= lo -> hi <= 2 ^ 64 -> stk asegs m lo hi.
  Proof.
    intros s m lo hi AWV IN LO HI. split; [unfold AIMG_TOP in LO; lia|]. split; [exact HI|].
    intros a Ha. assert (AU : bv_unsigned (wa a) = a) by (apply wa_unsigned; unfold AIMG_TOP in LO; lia).
    pose proof (AWV (wa a) (IN a Ha)) as V.
    assert (FS : find_segment asegs (bv_unsigned (wa a)) 1 = None) by (apply asegs_find_segment_none_high; unfold AIMG_TOP in LO; lia).
    unfold wview, mrd in *. rewrite FS in V |- *.
    destruct (m (wa a)) as [b|]; [| exfalso; exact (V eq_refl)].
    split; [discriminate| exists b; reflexivity].
  Qed.

  Lemma hull_lo_ge_aligned : forall R A, 0 <= R -> R mod 64 = 0 -> R <= A -> R <= hull_lo A.
  Proof. intros R A H0 HM HLE. unfold hull_lo. Z.div_mod_to_equations. lia. Qed.
  Lemma hull_hi_le_aligned : forall T B, 0 <= B -> T mod 64 = 0 -> B <= T -> hull_hi B <= T.
  Proof. intros T B H0 HM HLE. unfold hull_hi. Z.div_mod_to_equations. lia. Qed.

  Lemma chunk_class_range : forall st ch, WF st -> In ch (chunk_list st) -> ch_primary ch = true -> 0 <= ch_class ch < kNumClasses.
  Proof.
    intros st ch W Hin PR. pose proof (WF_chunk st ch W Hin) as (U1 & U2 & U3 & U4 & REST). rewrite PR in REST.
    destruct REST as (P1 & P2 & P3 & _). rewrite P3. unfold class_of_addr.
    pose proof (Z.land_ones (Z.shiftr (ch_alloc_beg ch - as_space_beg st) kRegionSizeLog) 5) as E.
    change (Z.ones 5) with 31 in E. rewrite E by lia. unfold kNumClasses. apply Z.mod_pos_bound. lia.
  Qed.

  Lemma inst_RHEAP_shvis : RHEAP_shvis (KHp p).
  Proof.
    intros x LB m q A n R IN.
    pose proof R as (HA & IDS & LEN & AWV & FLX & DEP0 & DPL & DTR & DJ1 & DJ2 & EF & MF & DJD & TH & TLS & ASV & DAP & DSEC & PINV & AHM). pose proof (proj1 DAP) as DSB.
    destruct HA as (AR & ND & EQ). pose proof (proj1 AR) as OK. pose proof (proj1 OK) as PL. pose proof (proj2 OK) as W.
    pose proof PL as (S1 & _).
    assert (INp : In (A, n) (lbp LB)) by (unfold lbp; apply in_map_iff; exists (q, A, n); auto).
    apply EQ in INp. destruct (alb_In _ _ _ INp) as (ch & Hch & STA & U0 & N0).
    pose proof (chunk_geom _ OK ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    pose proof (ext_facts _ OK ch Hch) as (E1 & E2 & E3 & _). acb.
    assert (A0 : 0 <= A) by (clear - E1 E3 G1 G2 U0; unfold AIMG_TOP in E1; lia).
    assert (TOP : A + n <= aceil) by (clear - E2 G4 G5 G2 U0 N0; lia).
    pose proof (hull_lo_le A A0) as HL. pose proof (hull_hi_ge (A + n) ltac:(clear - A0 G3 N0; lia)) as HH.
    unfold shvis. apply (stk_of_S (i_s x)); [exact AWV| | |].
    2:{ unfold sh, ASHADOW_BASE, AIMG_TOP. clear - HL A0. Z.div_mod_to_equations. lia. }
    2:{ unfold sh, ASHADOW_BASE. clear - HH TOP ACEILB A0 G3 N0. Z.div_mod_to_equations. lia. }
    intros y Hy.
    assert (YU : bv_unsigned (wa y) = y).
    { apply wa_unsigned. unfold sh, ASHADOW_BASE in Hy. clear - Hy HL HH A0 TOP ACEILB G3 N0. Z.div_mod_to_equations. lia. }
    destruct ASV as [ASV1 ASV2].
    destruct (ch_primary ch) eqn:PR.
    -
      pose proof (chunk_class_range _ ch W Hch PR) as HC.
      pose proof (WF_chunk _ ch W Hch) as (V1 & V2 & V3 & V4 & REST). rewrite PR in REST. destruct REST as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
      pose proof (WF_region _ _ W HC) as RO. pose proof (ro_alloc_le _ _ RO) as R1. pose proof (ro_mapped_mod _ _ RO) as R2.
      pose proof (region_beg_eq (a_st (i_s x)) (ch_class ch)) as RBE.
      apply (ASV1 (ch_class ch) (wa y) HC). rewrite YU. unfold RB.
      assert (RB64 : region_beg (a_st (i_s x)) (ch_class ch) mod 64 = 0).
      { rewrite RBE. unfold a_sb in S1. clear - S1. Z.div_mod_to_equations. nia. }
      pose proof (region_in_space (a_st (i_s x)) (ch_class ch) HC) as RIS.
      assert (HLO : region_beg (a_st (i_s x)) (ch_class ch) <= hull_lo A).
      { apply hull_lo_ge_aligned; [| exact RB64|].
        - pose proof PL as (_ & S2 & _). unfold a_sb in S2. clear - S2 RIS. acb. unfold AHI_LO in *. lia.
        - clear - P6 G1 G2 U0. lia. }
      assert (HHI : hull_hi (A + n) <= region_beg (a_st (i_s x)) (ch_class ch) + rg_mapped_user (get_region (a_st (i_s x)) (ch_class ch))).
      { apply hull_hi_le_aligned; [clear - A0 G3 N0; lia| unfold kUserMapSize in R2; clear - RB64 R2; Z.div_mod_to_equations; lia|].
        unfold ch_end in G4. rewrite PR in G4. clear - G4 G5 G2 U0 N0 P7 R1. lia. }
      unfold sh in *. unfold kUserMapSize in R2. clear - Hy HLO HHI RB64 R2. Z.div_mod_to_equations. lia.
    -
      pose proof (WF_chunk _ ch W Hch) as (V1 & V2 & V3 & V4 & REST). rewrite PR in REST. destruct REST as (P1 & P2 & i & h & Hi & Hb & Hsz & Hms).
      pose proof (nth_error_In _ _ Hi) as Hh.
      pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC & _).
      pose proof (SEC h Hh) as (Q1 & Q2 & Q3 & Q4 & _).
      apply (ASV2 h (wa y) Hh). rewrite YU.
      pose proof (aapp_env _ _ Q2 ltac:(clear - Q4; unfold kPageSize in *; lia)) as [QE1 QE2].
      assert (HLO : sc_map_beg h <= hull_lo A).
      { apply hull_lo_ge_aligned; [clear - QE1; lia| unfold kPageSize in Q1; clear - Q1; Z.div_mod_to_equations; lia| unfold kPageSize in Hb; clear - Hb G1 G2 U0; lia]. }
      assert (HHI : hull_hi (A + n) <= sc_map_beg h + sc_map_size h).
      { apply hull_hi_le_aligned; [clear - A0 G3 N0; lia| rewrite Hms; unfold round_up, kPageSize in *; clear - Q1; Z.div_mod_to_equations; lia|].
        unfold ch_end in G4. rewrite PR in G4. rewrite Hms, Hsz. unfold kPageSize in *. clear - G4 G5 G2 U0 N0 Hb. lia. }
      assert (MS8 : (sc_map_beg h + sc_map_size h) mod 8 = 0).
      { rewrite Hms. unfold round_up, kPageSize in *. clear - Q1. Z.div_mod_to_equations. lia. }
      unfold sh in *. clear - Hy HLO HHI Q1 MS8. unfold kPageSize in *. Z.div_mod_to_equations. lia.
  Qed.

  Section Loc.
    Variable s : ast.
    Hypothesis OK : ast_ok s.
    Let W : WF (a_st s). Proof. exact (proj2 OK). Qed.
    Let PL : placed_ok s. Proof. exact (proj1 OK). Qed.

    Lemma chunk_loc : forall ch, In ch (chunk_list (a_st s)) ->
      (a_sb s <= ch_lo ch /\ ch_end ch <= a_sb s + kSpaceSize + kPageSize)
      \/ (exists sc, In sc (as_sec (a_st s)) /\ sc_map_beg sc <= ch_lo ch /\ ch_end ch <= sc_map_beg sc + sc_map_size sc).
    Proof.
      intros ch Hch. pose proof (ext_facts s OK ch Hch) as (X1 & X2 & X3 & XP & XS). unfold ch_lo in *.
      destruct (ch_primary ch) eqn:PR.
      - left. destruct (XP eq_refl) as (_ & _ & B1 & B2). unfold kSpaceSize, kPageSize in *. lia.
      - right. destruct (XS eq_refl) as (h & Hh & L1 & L2 & L3). exists h. split; [exact Hh|]. lia.
    Qed.

    Lemma spiece_loc : forall lo hi, spiece s lo hi ->
      (a_sb s <= lo /\ hi <= a_sb s + kSpaceSize + kPageSize)
      \/ (exists sc, In sc (as_sec (a_st s)) /\ sc_map_beg sc <= lo /\ hi <= sc_map_beg sc + sc_map_size sc).
    Proof.
      intros lo hi P.
      destruct P as [c Hc|c Hc|c cp Hc Hin|ch Hch|ch Hch|ch Hch Hq|ch Hch Hp|b Hb].
      - left. pose proof (WF_region _ c W Hc) as RO. pose proof (ro_fa_bound _ _ RO) as FB.
        pose proof (region_in_space (a_st s) c Hc) as [RS1 RS2]. unfold FA, BllocRep.FA. rewrite free_array_base_eq.
        unfold kFreeArrayOffset, kFreeArraySize, kSpaceSize, kPageSize, a_sb in *. clear - FB RS1 RS2. lia.
      - left. pose proof (WF_region _ c W Hc) as RO. pose proof (ro_mapped_bound _ _ RO) as MB. pose proof (ro_alloc_nonneg _ _ RO) as AN.
        pose proof (region_in_space (a_st s) c Hc) as [RS1 RS2]. unfold RB, BllocRep.RB.
        unfold kFreeArrayOffset, kUserMapSize, kSpaceSize, kPageSize, a_sb in *. clear - MB AN RS1 RS2. lia.
      - left. assert (C0 : carved (a_st s) c (compact_to_addr (a_st s) c cp)) by (destruct Hin; [apply carved_free| apply carved_cache]; assumption).
        pose proof (carved_in_space s OK _ _ C0) as (CS1 & CS2 & CS3). unfold kSpaceSize, kPageSize in *. clear - CS1 CS2 CS3. lia.
      - pose proof (chunk_geom s OK ch Hch) as (G1 & G2 & G3 & G4 & G5 & _). pose proof (ext_facts s OK ch Hch) as (X1 & X2 & X3 & _).
        destruct (chunk_loc ch Hch) as [[B1 B2]|(sc & Hsc & B1 & B2)];
          [left; clear - G1 G2 G3 G4 G5 X3 B1 B2; lia| right; exists sc; split; [exact Hsc| clear - G1 G2 G3 G4 G5 X3 B1 B2; lia]].
      - pose proof (chunk_geom s OK ch Hch) as (G1 & G2 & G3 & G4 & G5 & _). pose proof (ext_facts s OK ch Hch) as (X1 & X2 & X3 & _).
        destruct (chunk_loc ch Hch) as [[B1 B2]|(sc & Hsc & B1 & B2)];
          [left; clear - G1 G2 G3 G4 G5 X3 B1 B2; lia| right; exists sc; split; [exact Hsc| clear - G1 G2 G3 G4 G5 X3 B1 B2; lia]].
      - pose proof (chunk_geom s OK ch Hch) as (G1 & G2 & G3 & G4 & G5 & _). pose proof (ext_facts s OK ch Hch) as (X1 & X2 & X3 & _).
        destruct (chunk_loc ch Hch) as [[B1 B2]|(sc & Hsc & B1 & B2)];
          [left; clear - G1 G2 G3 G4 G5 X3 B1 B2; lia| right; exists sc; split; [exact Hsc| clear - G1 G2 G3 G4 G5 X3 B1 B2; lia]].
      - right. pose proof (ext_facts s OK ch Hch) as (X1 & X2 & X3 & _ & XS). destruct (XS Hp) as (h & Hh & L1 & L2 & L3).
        exists h. split; [exact Hh|].
        pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC & _).
        pose proof (SEC h Hh) as (_ & _ & _ & Q4 & _). unfold kPageSize in *. clear - L1 L2 L3 Q4. lia.
      - left. pose proof (batch_carved s OK b Hb) as (C0 & _). pose proof (carved_in_space s OK _ _ C0) as (CS1 & CS2 & CS3).
        change (class_size kBatchClass) with kBatchSize in CS2. unfold kSpaceSize, kPageSize in *. clear - CS1 CS2 CS3. lia.
    Qed.

    Lemma shadow_windows_not_afoot : forall a,
      (sh aceil <= a < AHI_LO) \/ (sh (a_fsb s) <= a < sh (a_fsb s + AFS_SIZE)) -> ~ afoot s a.
    Proof.
      intros a Ha AF. pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
      pose proof (aapp_env _ _ F1 ltac:(unfold AFS_SIZE; lia)) as [FE1 FE2]. acb.
      assert (SHR : ALOWSH_LO < a < AHI_LO).
      { pose proof (sh_mono (a_fsb s + AFS_SIZE) aceil FE2) as SM0. unfold sh, ASHADOW_BASE, ALOWSH_LO, AHI_LO, AFS_SIZE in *. clear - Ha SM0 FE1 ACEILB.
        Z.div_mod_to_equations. lia. }
      destruct (afoot_cases s OK a AF) as [(lo & hi & P & R)|[(ch & Hch & R)|[[R _]|(lo & hi & P & R)]]].
      - pose proof (apiece_noshadow s OK lo hi P) as NS. clear - SHR R NS. lia.
      - pose proof (ext_band s OK ch Hch) as EB. pose proof (chunk_geom s OK ch Hch) as (G1 & G2 & G3 & G4 & _).
        pose proof (ext_facts s OK ch Hch) as (E1 & E2 & E3 & _).
        clear - SHR R EB G1 G2 G3 G4 E1 E2 E3 ACEILB. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in *. lia.
      - clear - SHR R. unfold AIMG_TOP, ALOWSH_LO in *. lia.
      - pose proof (spiece_bounds s OK lo hi P) as (B1 & B2 & B3 & B4 & B5).
        destruct Ha as [Ha|Ha].
        + pose proof (sh_mono hi aceil B3) as SM. clear - Ha R SM B1 B2 B4. unfold sh in *. Z.div_mod_to_equations. lia.
        + destruct (spiece_loc lo hi P) as [[L1 L2]|(sc & Hsc & L1 & L2)].
          *   unfold disj in D6.
            destruct D6 as [D|D].
            -- pose proof (sh_mono hi (a_fsb s) ltac:(lia)) as SM. clear - Ha R SM B4 B1 B2. unfold sh in *. Z.div_mod_to_equations. lia.
            -- pose proof (sh_mono (a_fsb s + AFS_SIZE) lo ltac:(lia)) as SM. clear - Ha R SM B4 B1 B2. unfold sh in *. Z.div_mod_to_equations. lia.
          * pose proof (SEC sc Hsc) as (_ & _ & _ & _ & _ & _ & _ & _ & DF). unfold disj in DF.
            destruct DF as [D|D].
            -- pose proof (sh_mono hi (a_fsb s) ltac:(lia)) as SM. clear - Ha R SM B4 B1 B2. unfold sh in *. Z.div_mod_to_equations. lia.
            -- pose proof (sh_mono (a_fsb s + AFS_SIZE) lo ltac:(lia)) as SM. clear - Ha R SM B4 B1 B2. unfold sh in *. Z.div_mod_to_equations. lia.
    Qed.
  End Loc.

  Lemma aimg_client_w_img : forall lo hi a, aimg_client_w lo hi -> lo <= a < hi -> ARW_LO <= a < AIMG_TOP /\ ~ astatic a.
  Proof.
    intros lo hi a W Ha. unfold aimg_client_w, ATLS_PRIV_LO, ATLS_PRIV_HI, ALIBC_PGSZ, ATSD0, BsIface.ATP in W.
    unfold ARW_LO, AIMG_TOP, astatic, AINST, AFLAGS, ACFLAGS, ASHBASE_CELL, AHIGHMEMEND, ACANPOISON, AINITED, AALLOCFLAGS, AIAINIT, AHOOKS,
      AREALMEMSET, AIAINST, AGOT_LO, APAGESZ, ASECNAME, APRIMNAME, ATLSSLOT, ATSD, ALSANDIS, AGOT2, OI_MISMATCH.
    split; [lia|]. intros X. repeat (destruct X as [X|X]); lia.
  Qed.

  Lemma client_window_bridge : forall x LB m iv,
    as_RHEAP (KHp p) x LB m -> BsIface.aclient_write_ok (KHp p) LB iv -> BllocRep.aclient_write_ok (i_s x) (lbp LB) iv.
  Proof.
    intros x LB m [lo hi] R CW.
    pose proof R as (HA & IDS & LEN & AWV & FLX & DEP0 & DPL & DTR & DJ1 & DJ2 & EF & MF & DJD & TH & TLS & ASV & DAP & DSEC & PINV & AHM). pose proof (proj1 DAP) as DSB.
    destruct HA as (AR & ND & EQ). pose proof (proj1 AR) as OK.
    unfold BsIface.aclient_write_ok in CW. cbn [fst snd] in CW.
    destruct CW as [C|[C|[(b & Hb & C1 & C2)|[(b & Hb & C1 & C2)|[C|[C|C]]]]]]; cbn [as_FSB KHp] in *; unfold BsIface.AFS_SIZE, BllocRep.AFS_SIZE in *.
    - left. exact C.
    - right; right; right; left. cbn [fst snd].
      pose proof C as C'. unfold aimg_client_w, ATLS_PRIV_LO, ATLS_PRIV_HI, ALIBC_PGSZ, ATSD0, BsIface.ATP in C'. unfold ARW_LO, AIMG_TOP.
      split; [lia|]. split; [lia|]. intros a Ha. exact (proj2 (aimg_client_w_img lo hi a C Ha)).
    - right; left. exists (blk_addr b, blk_size b). split; [unfold lbp; apply in_map_iff; exists b; auto|]. cbn [fst snd]. lia.
    - right; right; left. exists (blk_addr b, blk_size b). split; [unfold lbp; apply in_map_iff; exists b; auto|]. cbn [fst snd]. lia.
    - right; right; right; right. cbn [fst snd]. intros a Ha. apply (fakestack_not_afoot _ OK). rewrite EF. unfold BllocRep.AFS_SIZE, BsIface.AFS_SIZE in *. lia.
    - right; right; right; right. cbn [fst snd]. intros a Ha. apply (shadow_windows_not_afoot _ OK). right. rewrite EF. unfold BllocRep.AFS_SIZE, BsIface.AFS_SIZE in *. lia.
    - right; right; right; right. cbn [fst snd]. intros a Ha. apply (shadow_windows_not_afoot _ OK). left. lia.
  Qed.

  Definition iprotected0 (x : ist) (a : Z) : Prop :=
       (ALIBCPGSZ <= a < ALIBCPGSZ + 8) \/ (AGOT_SSP <= a < AGOT_SSP + 8)
    \/ (ACFLAGS + 219 <= a < ACFLAGS + 220) \/ (ACFLAGS + 244 <= a < ACFLAGS + 245)
    \/ (BsIface.ATP + 8 <= a < BsIface.ATP + 16) \/ (ip_D p + 24 <= a < ip_D p + 32)
    \/ (2567960 <= a < 6762280 + 8) \/ (2502408 <= a < 2502408 + 28)
    \/ (d_nb (i_d x) <= a < d_nb (i_d x) + 16 * 65536) \/ (d_sb (i_d x) <= a < d_sb (i_d x) + 8 * 32768)
    \/ (a_thr (i_s x) + 48 <= a < a_thr (i_s x) + 64).

  Definition iprotected (x : ist) (a : Z) : Prop :=
    iprotected0 x a \/ (AIMM_OBJ <= a < AIMM_OBJ + 8) \/ (ip_TB p <= a < ip_TB p + AHM_SIZE).

  Lemma client_window_protected0 : forall x LB m lo hi a,
    as_RHEAP (KHp p) x LB m -> BsIface.aclient_write_ok (KHp p) LB (lo, hi) -> lo <= a < hi -> iprotected0 x a -> False.
  Proof.
    intros x LB m lo hi a R CW Ha PR.
    pose proof R as (HA & IDS & LEN & AWV & FLX & DEP0 & DPL & DTR & DJ1 & DJ2 & EF & MF & DJD & TH & TLS & ASV & DAP & DSEC & PINV & AHM). pose proof (proj1 DAP) as DSB.
    destruct HA as (AR & ND & EQ). pose proof (proj1 AR) as OK.
    pose proof (proj1 OK) as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    pose proof (aapp_env _ _ F1 ltac:(unfold AFS_SIZE; lia)) as [FE1 FE2]. acb.
    destruct TH as (_ & _ & DB0 & DB8 & DB32 & DKO). unfold kPageSize in DKO.
    pose proof T2 as TKO. unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, AIMG_TOP, ALOWSH_LO, AHI_LO, kPageSize in TKO. unfold kPageSize in T3.
    pose proof DPL as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & QSEC & QA1 & QA2 & QA3 & QA4).
    pose proof (aapp_env _ _ QA1 ltac:(lia)) as [NB1 NB2]. pose proof (aapp_env _ _ QA3 ltac:(lia)) as [SB1 SB2].
    pose proof (proj1 DEP0) as DWF. pose proof (wf_nbsb _ DWF) as NBSB.

    unfold BsIface.aclient_write_ok in CW. cbn [fst snd as_FSB KHp] in CW.
    unfold iprotected0, ALIBCPGSZ, AGOT_SSP, ACFLAGS, BsIface.ATP in PR.
    destruct CW as [C|[C|[(b & Hb & B1 & B2)|[(b & Hb & B1 & B2)|[C|[C|C]]]]]]; cbn [as_FSB KHp] in *; unfold BsIface.AFS_SIZE, BllocRep.AFS_SIZE in *.
    -
      unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, AIMG_TOP, ALOWSH_LO, AHI_LO in DKO.
      clear - C Ha PR DB32 NB2 SB2 T3 ACEILB. lia.
    -
      unfold aimg_client_w, ATLS_PRIV_LO, ATLS_PRIV_HI, ALIBC_PGSZ, ATSD0, BsIface.ATP in C.
      unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, AIMG_TOP, ALOWSH_LO, AHI_LO in DKO.
      clear - C Ha PR DKO NB1 SB1 TKO. lia.
    -
      assert (INp : In (blk_addr b, blk_size b) (lbp LB)) by (unfold lbp; apply in_map_iff; exists b; auto).
      pose proof (ARHEAP_block_range_ok _ _ _ _ _ (conj AR (conj ND EQ)) INp) as (R1 & _ & R3 & R4 & _).
      pose proof INp as INa. apply EQ in INa. destruct (alb_In _ _ _ INa) as (ch & Hch & _ & U0 & N0).
      pose proof (chunk_geom _ OK ch Hch) as (G1 & G2 & G3 & G4 & G5 & _). pose proof (ext_facts _ OK ch Hch) as (E1 & E2 & E3 & _).
      destruct (chunk_loc _ OK ch Hch) as [[L1 L2]|(sc & Hsc & L1 & L2)].
      + unfold disj, kSpaceSize, kPageSize in DSB, Q3, Q4, D2. unfold AIMG_TOP in R1. unfold kSpaceSize, kPageSize in L2.
        clear - Ha PR B1 B2 U0 N0 G1 G2 G3 G4 G5 E3 L1 L2 DSB Q3 Q4 D2 R1. lia.
      + pose proof (DSEC sc Hsc) as DS. pose proof (QSEC sc Hsc) as [QS1 QS2]. pose proof (SEC sc Hsc) as (_ & _ & _ & _ & _ & _ & ST7 & _).
        unfold disj, kPageSize in DS, QS1, QS2, ST7. unfold AIMG_TOP in R1.
        clear - Ha PR B1 B2 U0 N0 G1 G2 G3 G4 G5 E3 L1 L2 DS QS1 QS2 ST7 R1. lia.
    -
      assert (INp : In (blk_addr b, blk_size b) (lbp LB)) by (unfold lbp; apply in_map_iff; exists b; auto).
      pose proof (ARHEAP_block_range_ok _ _ _ _ _ (conj AR (conj ND EQ)) INp) as (R1 & _ & R3 & R4 & _).
      pose proof (sh_mono AIMG_TOP (blk_addr b) R1) as SM1.
      unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, AIMG_TOP, ALOWSH_LO, AHI_LO in DKO, QA1, QA3.
      unfold nsh, sh, ASHADOW_BASE, AIMG_TOP in *. clear - Ha PR B1 B2 SM1 R3 R4 DKO QA1 QA3 TKO ACEILB. Z.div_mod_to_equations. lia.
    -
      rewrite <- EF in C. unfold disj, kPageSize in DJ1, DJ2, DJD, D8.
      clear - C Ha PR DJ1 DJ2 DJD D8 FE1. unfold AIMG_TOP in *. lia.
    -
      rewrite <- EF in C. pose proof (sh_mono AIMG_TOP (a_fsb (i_s x)) ltac:(unfold AIMG_TOP; lia)) as SM1. pose proof (sh_mono (a_fsb (i_s x) + 11571200) aceil F2) as SM2.
      unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, AIMG_TOP, ALOWSH_LO, AHI_LO in DKO, QA1, QA3.
      unfold sh, ASHADOW_BASE, AIMG_TOP in *. clear - C Ha PR SM1 SM2 DKO QA1 QA3 TKO ACEILB. Z.div_mod_to_equations. lia.
    -
      unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, AIMG_TOP, ALOWSH_LO, AHI_LO in DKO, QA1, QA3. unfold AHI_LO in C.
      unfold sh, ASHADOW_BASE, AIMG_TOP in *. clear - C Ha PR DKO QA1 QA3 TKO ACEILB. Z.div_mod_to_equations. lia.
  Qed.

  Lemma client_window_ahm : forall x LB m lo hi a,
    as_RHEAP (KHp p) x LB m -> BsIface.aclient_write_ok (KHp p) LB (lo, hi) -> lo <= a < hi ->
    (AIMM_OBJ <= a < AIMM_OBJ + 8) \/ (ip_TB p <= a < ip_TB p + AHM_SIZE) -> False.
  Proof.
    intros x LB m lo hi a R CW Ha PR.
    pose proof R as (HA & IDS & LEN & AWV & FLX & DEP0 & DPL & DTR & DJ1 & DJ2 & EF & MF & DJD & TH & TLS & ASV & DAP & DSEC & PINV & AHM).
    pose proof AHM as (AH1 & AH2 & AH3 & AHP & AHA & AHK & AHC & AT1 & AT2 & AT3 & AT4 & AT5 & AT6 & AT7 & ATS).
    destruct HA as (AR & ND & EQ). pose proof (proj1 AR) as OK.
    pose proof (proj1 OK) as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    pose proof (aapp_env _ _ F1 ltac:(unfold AFS_SIZE; lia)) as [FE1 FE2]. acb.
    assert (TKO : 4096 <= ip_TB p /\ (ip_TB p + AHM_SIZE <= AIMG_LO \/ AIMG_TOP <= ip_TB p) /\ ~ (ALOWSH_LO <= ip_TB p + AHM_SIZE - 1 /\ ip_TB p < AHI_LO)).
    { clear - AHK AHC ACEILB. unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, AIMG_TOP, ALOWSH_LO, AHI_LO, AHM_SIZE in *. lia. }
    unfold AIMM_OBJ, AHM_SIZE in PR. unfold AHM_SIZE in AHC, TKO, AT1, ATS, AT6.
    unfold BsIface.aclient_write_ok in CW. cbn [fst snd as_FSB KHp] in CW.
    destruct CW as [C|[C|[(b & Hb & B1 & B2)|[(b & Hb & B1 & B2)|[C|[C|C]]]]]]; cbn [as_FSB KHp] in *; unfold BsIface.AFS_SIZE, BllocRep.AFS_SIZE in *.
    -   clear - C Ha PR AHC ACEILB. lia.
    -
      unfold aimg_client_w, ATLS_PRIV_LO, ATLS_PRIV_HI, ALIBC_PGSZ, ATSD0, BsIface.ATP in C.
      unfold AIMG_LO, AIMG_TOP in TKO. clear - C Ha PR TKO. lia.
    -
      assert (INp : In (blk_addr b, blk_size b) (lbp LB)) by (unfold lbp; apply in_map_iff; exists b; auto).
      pose proof (ARHEAP_block_range_ok _ _ _ _ _ (conj AR (conj ND EQ)) INp) as (R1 & _ & R3 & R4 & _).
      pose proof INp as INa. apply EQ in INa. destruct (alb_In _ _ _ INa) as (ch & Hch & _ & U0 & N0).
      pose proof (chunk_geom _ OK ch Hch) as (G1 & G2 & G3 & G4 & G5 & _). pose proof (ext_facts _ OK ch Hch) as (E1 & E2 & E3 & _).
      destruct (chunk_loc _ OK ch Hch) as [[L1 L2]|(sc & Hsc & L1 & L2)].
      + unfold disj, kSpaceSize, kPageSize in AT1. unfold AIMG_TOP in R1. unfold kSpaceSize, kPageSize in L2.
        clear - Ha PR B1 B2 U0 N0 G1 G2 G3 G4 G5 E3 L1 L2 AT1 R1. lia.
      + pose proof (ATS sc Hsc) as DS. unfold disj in DS. unfold AIMG_TOP in R1.
        clear - Ha PR B1 B2 U0 N0 G1 G2 G3 G4 G5 E3 L1 L2 DS R1. lia.
    -
      assert (INp : In (blk_addr b, blk_size b) (lbp LB)) by (unfold lbp; apply in_map_iff; exists b; auto).
      pose proof (ARHEAP_block_range_ok _ _ _ _ _ (conj AR (conj ND EQ)) INp) as (R1 & _ & R3 & R4 & _).
      pose proof (sh_mono AIMG_TOP (blk_addr b) R1) as SM1.
      unfold nsh, sh, ASHADOW_BASE, AIMG_TOP, AIMG_LO, ALOWSH_LO, AHI_LO in *. clear - Ha PR B1 B2 SM1 R3 R4 TKO ACEILB. Z.div_mod_to_equations. lia.
    -
      rewrite <- EF in C. unfold disj in AT6. unfold AIMG_TOP in FE1. clear - C Ha PR AT6 FE1. lia.
    -
      rewrite <- EF in C. pose proof (sh_mono AIMG_TOP (a_fsb (i_s x)) ltac:(unfold AIMG_TOP; lia)) as SM1. pose proof (sh_mono (a_fsb (i_s x) + 11571200) aceil F2) as SM2.
      unfold sh, ASHADOW_BASE, AIMG_TOP, AIMG_LO, ALOWSH_LO, AHI_LO in *. clear - C Ha PR SM1 SM2 TKO ACEILB. Z.div_mod_to_equations. lia.
    -
      unfold AHI_LO in C. unfold sh, ASHADOW_BASE, AIMG_TOP, AIMG_LO, ALOWSH_LO, AHI_LO in *. clear - C Ha PR TKO ACEILB. Z.div_mod_to_equations. lia.
  Qed.

  Lemma client_window_protected : forall x LB m lo hi a,
    as_RHEAP (KHp p) x LB m -> BsIface.aclient_write_ok (KHp p) LB (lo, hi) -> lo <= a < hi -> iprotected x a -> False.
  Proof.
    intros x LB m lo hi a R CW Ha [PR|PR]; [exact (client_window_protected0 x LB m lo hi a R CW Ha PR)| exact (client_window_ahm x LB m lo hi a R CW Ha PR)].
  Qed.

  Lemma sspguard_rw_any : forall m, exists g : word, rw_cells asegs m ASSPGUARD [C8 g].
  Proof.
    intros m. unfold ASSPGUARD.
    assert (RD : forall i, 0 <= i < 8 -> exists b, mrd asegs m (wa (0x6e5898 + i)) = Some b).
    { intros i Hi. unfold mrd. destruct (m (wa (0x6e5898 + i))) as [b|]; [exists b; reflexivity|].
      assert (H8 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
      destruct H8 as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; eexists; reflexivity. }
    destruct (RD 0 ltac:(lia)) as [b0 H0]. destruct (RD 1 ltac:(lia)) as [b1 H1].
    destruct (RD 2 ltac:(lia)) as [b2 H2]. destruct (RD 3 ltac:(lia)) as [b3 H3].
    destruct (RD 4 ltac:(lia)) as [b4 H4]. destruct (RD 5 ltac:(lia)) as [b5 H5].
    destruct (RD 6 ltac:(lia)) as [b6 H6]. destruct (RD 7 ltac:(lia)) as [b7 H7].
    exists (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3; b4; b5; b6; b7])).
    split.
    - split; [cbn; repeat split; exact I|]. cbn [cells_bytes cbytes app].
      change (le8 ?v) with (word_to_le_bytes 8 v). rewrite word_to_le_bytes_of_lez by (reflexivity || (cbn; lia)).
      rewrite app_nil_r. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
      destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ]; [ | | | | | | | | lia].
      + rewrite Z.add_0_r in H0. exact H0. + exact H1. + exact H2. + exact H3. + exact H4. + exact H5. + exact H6. + exact H7.
    - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn [cells_size csize Nat.add] in Hi.
      unfold wview. destruct (m (wa (0x6e5898 + i))) as [b|]; [discriminate|].
      assert (H8 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
      destruct H8 as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; discriminate.
  Qed.

  Lemma depot_mem_frame : forall x d m m',
    d_wf d -> depot_mem asegs d m -> agree_on (iprotected x) m m' -> wmono asegs m m' ->
    d_nb d = d_nb (i_d x) -> d_sb d = d_sb (i_d x) ->
    depot_mem asegs d m'.
  Proof.
    intros x d m m' W DM AG WM Enb Esb.
    pose proof (wf_ids d W) as I1. pose proof (wf_frames d W) as I2.
    destruct DM as [T1 T2 T3 T4 T5 T6 T7 T8 T9 T10].
    assert (PROT : forall A k, (2567960 <= A /\ A + k <= 6762280 + 8) \/ (2502408 <= A /\ A + k <= 2502408 + 28)
                     \/ (d_nb d <= A /\ A + k <= d_nb d + 16 * 65536) \/ (d_sb d <= A /\ A + k <= d_sb d + 8 * 32768) ->
                   forall a, A <= a < A + k -> iprotected x a).
    { intros A k HA a Ha. unfold iprotected, iprotected0. rewrite <- Enb, <- Esb. lia. }
    constructor.
    - intros b Hb. eapply (rw_cells_transport_pt _ _ _ AG WM); [apply T1; exact Hb|]. apply PROT. cbn. lia.
    - eapply (rw_cells_transport_pt _ _ _ AG WM); [exact T2|]. apply PROT. cbn. lia.
    - eapply (rw_cells_transport_pt _ _ _ AG WM); [exact T3|]. apply PROT. cbn. lia.
    - intros id Hid. eapply (rw_cells_transport_pt _ _ _ AG WM); [apply T4; exact Hid|]. apply PROT. cbn. lia.
    - intros id Hid. destruct (T5 id Hid) as [sid H]. exists sid. eapply (rw_cells_transport_pt _ _ _ AG WM); [exact H|]. apply PROT. cbn. lia.
    - intros id Hid. destruct (T6 id Hid) as (j1 & j2 & j3 & H). exists j1, j2, j3. eapply (rw_cells_transport_pt _ _ _ AG WM); [exact H|]. apply PROT. cbn. lia.
    - eapply (rw_cells_transport_pt _ _ _ AG WM); [exact T7|]. apply PROT. cbn. lia.
    - eapply (rw_cells_transport_pt _ _ _ AG WM); [exact T8|]. apply PROT. cbn. lia.
    - eapply (rw_cells_transport_pt _ _ _ AG WM); [exact T9|]. apply PROT. cbn. lia.
    - destruct T10 as (junk & U & L). exists junk. split; [|exact L]. eapply (u8arr_transport_pt _ _ _ AG WM); [exact U|]. apply PROT. lia.
  Qed.

  Theorem inst_RHEAP_frame : RHEAP_frame (KHp p).
  Proof.
    intros x LB m m' W R MU WM FW.
    pose proof R as (HA & IDS & LEN & AWV & FLX & DEP0 & DPL & DTR & DJ1 & DJ2 & EF & MF & DJD & TH & TLS & ASV & DAP & DSEC & PINV & AHM). pose proof (proj1 DAP) as DSB.
    assert (AG : agree_on (iprotected x) m m').
    { intros a Pa Ha. apply MU. rewrite wa_unsigned by lia.
      clear - FW Pa R. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
      inversion FW as [|iv l CW FW']; subst. split; [| apply IH; exact FW'].
      intros K. exact (client_window_protected x LB m lo hi a R CW K Pa). }
    cbn [as_RHEAP KHp]. unfold IRHEAP. cbv zeta.
    split.
    {   eapply (ARHEAP_frame_ok _ _ _ _ _ HA MU WM). eapply Forall_impl; [| exact FW].
      intros iv CW. exact (client_window_bridge x LB m iv R CW). }
    split; [exact IDS|]. split; [exact LEN|].
    split; [exact (awin_vis_wmono _ _ _ AWV WM)|].
    split.
    {   destruct FLX as (F1 & F2 & (g & F3) & F4 & (b & F5)).
      split; [| split; [| split; [| split]]].
      - eapply (rw_cells_transport_pt _ _ _ AG WM); [exact F1|]. intros a Ha. unfold iprotected, iprotected0. cbn in Ha. lia.
      - eapply (rw_cells_transport_pt _ _ _ AG WM); [exact F2|]. intros a Ha. unfold iprotected, iprotected0. cbn in Ha. lia.
      - exact (sspguard_rw_any m').
      - eapply (rw_cells_transport_pt _ _ _ AG WM); [exact F4|]. intros a Ha. unfold iprotected, iprotected0. cbn in Ha. lia.
      - exists b. eapply (rw_cells_transport_pt _ _ _ AG WM); [exact F5|]. intros a Ha. unfold iprotected, iprotected0. cbn in Ha. lia. }
    split.
    {   destruct DEP0 as [DWF DM]. split; [exact DWF|]. exact (depot_mem_frame x _ m m' DWF DM AG WM eq_refl eq_refl). }
    split; [exact DPL|]. split; [exact DTR|]. split; [exact DJ1|]. split; [exact DJ2|]. split; [exact EF|]. split; [exact MF|]. split; [exact DJD|].
    split.
    {   destruct TH as (A1 & A2 & A3). split; [| split; [| exact A3]].
      - eapply (rw_cells_transport_pt _ _ _ AG WM); [exact A1|]. intros a Ha. unfold iprotected, iprotected0, BsIface.ATP, BllocRep.ATP in *. cbn in Ha. lia.
      - eapply (rw_cells_transport_pt _ _ _ AG WM); [exact A2|]. intros a Ha. unfold iprotected, iprotected0, BsIface.ATP, BllocRep.ATP in *. cbn in Ha. lia. }
    split.
    {   destruct TLS as (tb & te & T48). exists tb, te.
      eapply (rw_cells_transport_pt _ _ _ AG WM); [exact T48|]. intros a Ha. unfold iprotected, iprotected0. cbn in Ha. lia. }
    split; [exact ASV|]. split; [exact DAP|]. split; [exact DSEC|]. split; [exact PINV|].
    {
      pose proof AHM as (AH1 & AH2 & AH3 & AHREST).
      split; [eapply (rw_cells_transport_pt _ _ _ AG WM); [exact AH1|]; intros a Ha; unfold iprotected; cbn in Ha; right; left; exact Ha|].
      split; [eapply (rw_cells_transport_pt _ _ _ AG WM); [exact AH2|]; intros a Ha; unfold iprotected; cbn in Ha; right; right; unfold AHM_SIZE, AHM_B1 in *; lia|].
      split; [eapply (rw_cells_transport_pt _ _ _ AG WM); [exact AH3|]; intros a Ha; unfold iprotected; cbn in Ha; right; right; unfold AHM_SIZE, AHM_B2 in *; lia|].
      exact AHREST. }
  Qed.

  Lemma inst_RHEAP_ahm : RHEAP_ahm (KHp p).
  Proof.
    intros x LB m R. cbn [as_RHEAP KHp] in R.
    pose proof R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AHM).
    destruct AHM as (AH1 & AH2 & AH3 & AHP & AHA & AHK & AHC & _).
    exists (ip_TB p). unfold AIMM_OBJ, AHM_B1, AHM_B2, AHM_SIZE, wz in *.
    split; [exact AH1|]. split; [unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_TOP, AIMG_LO in AHK; lia|].
    split; [exact AHA|]. split; [exact AHC|].
    split; [destruct AHK as [[X1 X2]|AP]; [unfold AIMG_LO in X2; lia| exact AP]|].
    split; [exact AH2| exact AH3].
  Qed.
End Laws3.
