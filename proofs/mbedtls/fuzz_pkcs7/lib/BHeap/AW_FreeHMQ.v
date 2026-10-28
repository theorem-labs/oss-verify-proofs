(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX APop AW_FreeP AW_FreeK AW_FreeG AW_FreeR.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Blist AW_FakeDefs AW_FakeRep HMLib HM HMFrame AW_FreeHM AW_FreeHMS AW_RecStep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
Section ARUN_1. Context {hAR : arun}.

Definition quar_zone (h : ahst) (a : Z) : Prop :=
  (l_stk_lo (h_L h) <= a < l_stk_hi (h_L h)) \/ in_rangesZ quar_img_ranges a \/ (l_T (h_L h) + 80 <= a < l_T (h_L h) + 112)
  \/ (exists b, In b (q_batches (h_tq h) ++ q_batches (h_gq h)) /\ b_addr b <= a < b_addr b + 8192).

#[using="Type"] Lemma quar_img_where : forall a, in_rangesZ quar_img_ranges a -> 0x106708 <= a < 0x106730.
Proof. intros a H. unfold quar_img_ranges in H. cbn in H. lia. Qed.

Section KeepQ.
  Variables (h : ahst) (m m' : mem) (LF : list (Z * Z)).
  Hypothesis WL' : wf_L' (h_L h).
  Hypothesis WR : wf_region h.
  Hypothesis WK : wf_chunks' h.
  Hypothesis WS : wf_sec h.
  Hypothesis WD : wf_depot' h.
  Hypothesis GEO : hgeom h.
  Hypothesis BS : forall b, In b (q_batches (h_tq h) ++ q_batches (h_gq h)) -> exists i, 0 <= i < carved h kBatchClass /\ b_addr b = chunk_at (h_L h) kBatchClass i.
  Hypothesis WM : wmono asegs m m'.
  Hypothesis KO : forall A n, (forall a, A <= a < A + n -> ~ quar_zone h a) -> kept m m' A n.

  Let WL : wf_L (h_L h). Proof. exact (proj1 WL'). Qed.

  (* [comment removed for export] *)
  #[using="hAR WR WK BS"] Lemma batch_vs_chunk' : forall k b, In k (h_chunks h) -> ck_prim k = true -> In b (q_batches (h_tq h) ++ q_batches (h_gq h)) ->
    b_addr b + 8192 <= ck_ab k \/ ck_ab k + class_size (ck_cls k) <= b_addr b.
  Proof.
    intros k b Hk P Hb. dpose WK as (WKF & _ & _).
    ddestruct (BS b Hb) as (i & Hi & EB).
    pose proof (proj1 (Forall_forall _ _) WKF k Hk) as (_ & _ & _ & WX). rewrite P in WX. ddestruct WX as (_ & C30 & j & Hj & EK).
    unfold kBatchClass in *.
    destruct (Z.eq_dec (ck_cls k) 24) as [E24|N24].
    - rewrite E24 in *. assert (NIJ : i <> j).
      { intros ->. pose proof (WR 24 ltac:(unfold kNumClasses; lia)) as W. cbn zeta in W. ddestruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDO & _).
        apply (owned_chunk_not_batch h 24 (compact (h_L h) 24 (ck_ab k)) NDO).
        + unfold chunk_set. apply in_map_iff. exists k. split; [reflexivity|]. apply filter_In. split; [exact Hk|]. rewrite P, E24. reflexivity.
        + unfold batch_set, kBatchClass. rewrite Z.eqb_refl. apply in_map_iff. exists b. split; [rewrite EB, EK; reflexivity| exact Hb]. }
      rewrite EB, EK. unfold chunk_at. change (class_size 24) with 8192.
      assert (i + 1 <= j \/ j + 1 <= i) as [LE|GT] by lia; [left| right]; lia.
    - destruct (slot_le h 24 i WR ltac:(lia) Hi) as [A1 A2]. destruct (slot_le h (ck_cls k) j WR ltac:(lia) Hj) as [B1 B2].
      pose proof (user_vs_user h (ck_cls k) 24 WR ltac:(lia) ltac:(lia) N24) as UU.
      pose proof (WR 24 ltac:(unfold kNumClasses; lia)) as W. cbn zeta in W. ddestruct W as (_ & AUMU1 & _).
      pose proof (WR (ck_cls k) ltac:(unfold kNumClasses; lia)) as W. cbn zeta in W. ddestruct W as (_ & AUMU2 & _).
      rewrite EB, EK. change (class_size 24) with 8192 in *. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="WR BS"] Lemma batch_where : forall b, In b (q_batches (h_tq h) ++ q_batches (h_gq h)) ->
    region_beg (h_L h) 24 <= b_addr b /\ b_addr b + 8192 <= region_beg (h_L h) 24 + r_alloc_user (h_reg h 24).
  Proof.
    intros b Hb. ddestruct (BS b Hb) as (i & Hi & EB). destruct (slot_le h 24 i WR ltac:(lia) Hi) as [A1 A2].
    rewrite EB. change (class_size 24) with 8192 in A2. unfold kBatchClass in *. clear - A1 A2. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="WR BS KO"] Lemma KOZ : forall A n,
    (A + n <= l_stk_lo (h_L h) \/ l_stk_hi (h_L h) <= A) -> (A + n <= 0x106708 \/ 0x106730 <= A) -> (A + n <= l_T (h_L h) + 80 \/ l_T (h_L h) + 112 <= A) ->
    (A + n <= region_beg (h_L h) 24 \/ region_beg (h_L h) 24 + r_alloc_user (h_reg h 24) <= A) -> kept m m' A n.
  Proof.
    intros A n Z1 Z2 Z3 Z4. apply KO. intros a Ha [Q|[Q|[Q|(b & Hb & Q)]]].
    - clear - Ha Z1 Q. lia.
    - apply quar_img_where in Q. clear - Ha Z2 Q. lia.
    - clear - Ha Z3 Q. lia.
    - destruct (batch_where b Hb) as [B1 B2]. clear - Ha Z4 Q B1 B2. lia.
  Qed.

  #[using="WL' WR WK WS WD GEO BS WM KO WL"] Theorem HMq_keepQ : HMq h LF m -> HMq h LF m'.
  Proof.
    (intros dd_H; ddestruct dd_H as (G0 & G1 & G2 & G3 & G4 & G5 & G7 & G8 & G9 & GE)).
    dpose WL' as (_ & WL24 & WLD). pose proof WL as WL0.
    ddestruct (L_GSB (h_L h) WL0) as (SB0 & _ & RIE & RIH). ddestruct (L_GT (h_L h) WL0) as ((T0 & T1) & T2 & _). ddestruct (L_GCTX (h_L h) WL0) as ((C0 & C1) & C2 & CXL).
    dpose WL0 as (_ & B6a & B6b & _ & B6c & B6d & B6e & _ & _ & _ & _ & _ & _ & _ & _ & _ & STK0 & STKH & _ & _ & FS0 & FS1 & _ & _ & _ & _ & _ & _ & _ & _ & PA0 & PA1 & _).
    pose proof aceil_bounds as ACB. unfold lowhigh, kHighMemBeg in FS0, PA0. unfold kHighMemBeg in B6c.
    pose proof (z_T_stk h GEO) as ZT. pose proof (z_ctx_stk h GEO) as ZC. pose proof (z_fs_stk h GEO) as ZF. pose proof (z_pa_stk h GEO) as ZP.
    pose proof (z_hull_stk h GEO) as ZH. pose proof (z_stk_dtls h GEO) as ZD.
    pose proof (z_T_hull h GEO) as ZTH. pose proof (z_ctx_hull h GEO) as ZCH. pose proof (z_fs_hull h GEO) as ZFH. pose proof (z_pa_hull h GEO) as ZPH.
    pose proof (z_hull_dtls h GEO) as ZDH. pose proof (z_T_ctx h GEO) as ZTC. pose proof (z_T_fs h GEO) as ZTF. pose proof (z_T_pa h GEO) as ZTP. pose proof (z_T_dtls h GEO) as ZTD.
    unfold zapart in ZT, ZC, ZF, ZP, ZH, ZD, ZTH, ZCH, ZFH, ZPH, ZDH, ZTC, ZTF, ZTP, ZTD.
    cbn [fst snd] in ZT, ZC, ZF, ZP, ZH, ZD, ZTH, ZCH, ZFH, ZPH, ZDH, ZTC, ZTF, ZTP, ZTD.
    rewrite CXL in ZC, ZCH, ZTC.
    dpose WLD as (DL & DL1 & _). unfold lowhigh, kHighMemBeg in DL.
    (* [comment removed for export] *)
    dpose (user_vs_ri h 24 WL0 WR ltac:(clear; lia)) as (U1 & U2 & U3 & U4).
    pose proof (WR 24 ltac:(unfold kNumClasses; clear; lia)) as W24. cbn zeta in W24. ddestruct W24 as (_ & AUMU24 & _).
    (* [comment removed for export] *)
    assert (IMGK : forall x : word, 0x10000 <= bv_unsigned x < 0x65f000 -> ~ in_rangesZ quar_img_ranges (bv_unsigned x) -> m' x = m x).
    { intros x Hx NQ. apply (KO (bv_unsigned x) 1); [| clear; lia]. intros a Ha [Q|[Q|[Q|(b & Hb & Q)]]].
      - clear - Ha Hx Q STK0 ACB. lia.
      - apply NQ. replace (bv_unsigned x) with a by (clear - Ha; lia). exact Q.
      - clear - Ha Hx Q T0. lia.
      - destruct (batch_where b Hb) as [B1 B2]. unfold region_beg, kRegionSize in *. clear - Ha Hx Q B1 B2 U2 B6c. lia. }
    assert (IAG : forall RS, ranges_apart_b RS quar_img_ranges = true -> ranges_within_b RS 0x10000 0x65f000 = true -> iagree RS m m').
    { intros RS H1 H2. exact (iagree_of_windows2 RS _ 0x10000 0x65f000 m m' H1 H2 IMGK). }
    (* [comment removed for export] *)
    assert (KH : forall A n, l_b6 (h_L h) <= A -> A + n <= l_b6 (h_L h) + 0x2000011000 ->
                 (A + n <= region_beg (h_L h) 24 \/ region_beg (h_L h) 24 + r_alloc_user (h_reg h 24) <= A) -> kept m m' A n).
    { intros A n H1 H2 H3. apply KOZ; [clear - H1 H2 ZH; lia| clear - H1 B6c; lia| clear - H1 H2 ZTH; lia| exact H3]. }
    split; [exact (hm_maps_frame _ _ _ G0 WM)|].
    split. { apply (hm_statics_frame m m' WM _ G1); [apply IAG; vm_compute; reflexivity| apply IAG; vm_compute; reflexivity| | | |].
             - apply KOZ; [clear - ZT; lia| clear - T0; lia| clear; lia| unfold region_beg, kRegionSize in *; clear - ZTH U2 AUMU24 U1 U4; lia].
             - apply KOZ; [clear - ZC; lia| clear - C0; lia| clear - ZTC; lia| unfold region_beg, kRegionSize in *; clear - ZCH U2 AUMU24 U1 U4; lia].
             - apply KOZ; [clear - ZC; lia| clear - C0; lia| clear - ZTC; lia| unfold region_beg, kRegionSize in *; clear - ZCH U2 AUMU24 U1 U4; lia].
             - apply KOZ; [clear - ZD; lia| clear - DL; lia| clear - ZTD; lia| unfold region_beg, kRegionSize in *; clear - ZDH U2 AUMU24 U1 U4; lia]. }
    split. { apply (hm_thread_frame m m' WM h G2); fold (h_L h); [| | | ddestruct G0 as (_ & _ & _ & WT & _); exact WT| exact T0].
             - apply KOZ; [clear - ZT; lia| clear - T0; lia| clear; lia| unfold region_beg, kRegionSize in *; clear - ZTH U2 AUMU24 U1 U4; lia].
             - intros c Hc. apply KOZ; [clear - ZT Hc; lia| clear - T0 Hc; lia| clear - Hc; lia| unfold region_beg, kRegionSize in *; clear - Hc ZTH U2 AUMU24 U1 U4; lia].
             - apply KOZ; [clear - ZT; lia| clear - T0; lia| clear; lia| unfold region_beg, kRegionSize in *; clear - ZTH U2 AUMU24 U1 U4; lia]. }
    split. { apply (hm_depot_frame h m m' G3 WM); [apply IAG; vm_compute; reflexivity| |].
             - intros b Hb. destruct (In_nth_error _ _ Hb) as [jb Hjb].
               pose proof (z_node_stk h GEO jb b Hjb) as Y1. pose proof (z_node_hull h GEO jb b Hjb) as Y2. pose proof (z_node_T h GEO jb b Hjb) as Y3.
               unfold zapart in Y1, Y2, Y3. cbn [fst snd] in Y1, Y2, Y3.
               pose proof (proj1 (Forall_forall _ _) (proj1 (proj2 (proj2 WD))) b Hb) as (NB0 & _).
               apply KOZ; [clear - Y1; lia| clear - NB0; lia| clear - Y3; lia| unfold region_beg, kRegionSize in *; clear - Y2 U2 AUMU24 U1 U4; lia].
             - intros b Hb. destruct (In_nth_error _ _ Hb) as [jb Hjb].
               pose proof (z_store_stk h GEO jb b Hjb) as Y1. pose proof (z_store_hull h GEO jb b Hjb) as Y2. pose proof (z_store_T h GEO jb b Hjb) as Y3.
               unfold zapart in Y1, Y2, Y3. cbn [fst snd] in Y1, Y2, Y3.
               pose proof (proj1 (Forall_forall _ _) (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 WD)))))) b Hb) as (NB0 & _).
               apply KOZ; [clear - Y1; lia| clear - NB0; lia| clear - Y3; lia| unfold region_beg, kRegionSize in *; clear - Y2 U2 AUMU24 U1 U4; lia]. }
    split. { unfold hm_chunks in *. apply Forall_forall. intros k' Hk'.
             ddestruct (chunk_geom' h k' WL0 WR WK Hk') as (RZ' & N0' & U8').
             apply (hm_chunk_frame m m' WM k' (proj1 (Forall_forall _ _) G4 k' Hk') RZ' N0' U8').
             ddestruct (chunk_ext' h k' WL0 WR WK Hk') as (_ & F1 & F2 & F3 & F4 & F5 & F6 & FC).
             assert (XAB : ext_lo k' <= ck_ab k') by (unfold ext_lo, ck_map_beg; destruct (ck_prim k'); clear; lia).
             assert (UIN : ck_ab k' + ck_rz k' = ck_user k') by reflexivity.
             assert (NFX' : 0 <= nfix (ck_n k') /\ nfix (ck_n k') <= Z.max (ck_n k') 8) by (unfold nfix; clear -N0'; lia).
             assert (KX : forall A n', ext_lo k' <= A -> A + n' <= ext_hi k' -> kept m m' A n').
             { intros A n' HA HB'. destruct FC as [(P' & C' & RL' & RH' & (i' & Hi' & EL' & EH'))|(P' & i' & N' & EL' & EH')].
               - (* [comment removed for export] *)
                 apply KO. intros a Ha [Q|[Q|[Q|(b & Hb & Q)]]].
                 + dpose (user_vs_ri h (ck_cls k') WL0 WR ltac:(clear -C'; lia)) as (Q1 & Q2 & _ & Q4).
                   pose proof (WR (ck_cls k') ltac:(unfold kNumClasses; clear -C'; lia)) as X. cbn zeta in X. ddestruct X as (_ & AUMU' & _).
                   unfold region_beg, kRegionSize in Q1, Q2, RL', RH'. clear - Ha HA HB' RL' RH' Q1 Q2 Q4 AUMU' ZH Q; lia.
                 + apply quar_img_where in Q. destruct F5 as [F5 _]. clear - Ha HA HB' F5 Q XAB. lia.
                 + dpose (user_vs_ri h (ck_cls k') WL0 WR ltac:(clear -C'; lia)) as (Q1 & Q2 & _ & Q4).
                   pose proof (WR (ck_cls k') ltac:(unfold kNumClasses; clear -C'; lia)) as X. cbn zeta in X. ddestruct X as (_ & AUMU' & _).
                   unfold region_beg, kRegionSize in Q1, Q2, RL', RH'. clear - Ha HA HB' RL' RH' Q1 Q2 Q4 AUMU' ZTH Q; lia.
                 + pose proof (batch_vs_chunk' k' b Hk' P' Hb) as AP. unfold ext_lo, ext_hi, ck_end in EL', EH', HA, HB'. rewrite P' in HA, HB'.
                   clear - Ha HA HB' AP Q. lia.
               - pose proof (z_sec_stk h GEO i' _ N') as Y1. pose proof (z_sec_hull h GEO i' _ N') as Y2. pose proof (z_sec_T h GEO i' _ N') as Y3.
                 unfold zapart in Y1, Y2, Y3. cbn [fst snd s_map_beg s_map_size] in Y1, Y2, Y3. destruct F5 as [F5 _].
                 apply KOZ; [clear - HA HB' Y1 EL' EH'; lia| clear - HA HB' F5 EL'; lia| clear - HA HB' Y3 EL' EH'; lia| unfold region_beg, kRegionSize in *; clear - HA HB' Y2 EL' EH' U2 AUMU24 U1 U4; lia]. }
             unfold chunk_kept. split; [apply KX; [exact XAB| clear - UIN F4; lia]|]. split.
             - intros AK. unfold shad. pose proof (Z.div_mod (ck_user k') 8 ltac:(clear; lia)) as D1.
               pose proof (Z.div_mod (nfix (ck_n k') + 7) 8 ltac:(clear; lia)) as D2. pose proof (Z.mod_pos_bound (nfix (ck_n k') + 7) 8 ltac:(clear; lia)) as D3.
               destruct F5 as [F5 F5']. unfold kHighMemBeg in F5'.
               apply KOZ; unfold region_beg, kRegionSize in *; [clear - D1 D2 D3 F3 F5 F5' F6 XAB UIN RZ' NFX' STK0 STKH ACB; lia| clear - D1 D2 D3 F3 F5 F5' F6 XAB UIN RZ' NFX' ACB; lia
                          | clear - D1 D2 D3 F3 F5 F5' F6 XAB UIN RZ' NFX' ACB T1; lia| clear - D1 D2 D3 F3 F5 F5' F6 XAB UIN RZ' NFX' ACB U2 B6a B6b SB0; lia].
             - intros NAK. apply KX; [clear - XAB UIN RZ'; lia| clear - F3; lia]. }
    split. { intros c' Hc'. pose proof (WR c' ltac:(unfold kNumClasses; clear -Hc'; lia)) as X. cbn zeta in X. ddestruct X as (_ & AUMU' & _ & _ & MULIM' & _ & _ & MFB' & NF4c & _).
             apply (hm_region_frame m m' WM (h_L h) c' (h_reg h c') _ (G5 c' Hc') AUMU' NF4c).
             dpose (user_vs_ri h c' WL0 WR Hc') as (Q1 & Q2 & Q3 & Q4).
             pose proof (user_vs_fa h c' 24 WR Hc' ltac:(clear; lia)) as Q5.
             unfold fa_beg, kFreeArrayOffset, kFreeArraySize, region_beg, kRegionSize in Q1, Q2, Q3, Q5. unfold kUserLimit in MULIM'. unfold kFreeArraySize in MFB'.
             unfold region_kept. split; [| split; [| split]].
             + apply KH; unfold ri_addr; unfold ri_base, space_end, kSpaceSize, region_beg, kRegionSize in *; [clear - Hc' Q4 SB0 B6a B6b; lia| clear - Hc' Q4 SB0 B6a B6b; lia| clear - Hc' U1 AUMU24; lia].
             + apply KH; unfold fa_beg, region_beg, kRegionSize, kFreeArrayOffset in *; [clear - Hc' Q3 Q4 Q2 MFB'; lia| clear - Hc' Q3 Q4 Q2 MFB'; lia| clear - Hc' Q5 MFB' AUMU24; lia].
             + apply KOZ; unfold shad, region_beg, kRegionSize in *; [clear - Hc' STK0 ACB Q1 Q2 Q4 AUMU' B6d SB0 B6a B6b B6c; lia| clear - Hc' ACB Q1 Q2 Q4 AUMU' B6d SB0 B6a B6b B6c; lia| clear - Hc' T1 ACB Q1 Q2 Q4 AUMU' B6d SB0 B6a B6b B6c; lia| clear - Hc' ACB Q1 Q2 Q4 AUMU' B6d U2 SB0 B6a B6b B6c; lia].
             + intros k0 Hk0. destruct (slot_le h c' k0 WR Hc' ltac:(unfold carved; exact Hk0)) as [S1 S2]. unfold region_beg, kRegionSize in S1, S2.
               pose proof (class_size_range c' Hc') as CSR'.
               apply KOZ; unfold shad, region_beg, kRegionSize in *; [clear - Hc' STK0 ACB S1 S2 CSR' Q1 Q2 Q4 AUMU' B6d SB0 B6a B6b B6c; lia| clear - Hc' ACB S1 S2 CSR' Q1 Q2 Q4 AUMU' B6d SB0 B6a B6b B6c; lia
                          | clear - Hc' T1 ACB S1 S2 CSR' Q1 Q2 Q4 AUMU' B6d SB0 B6a B6b B6c; lia| clear - Hc' ACB S1 S2 CSR' Q1 Q2 Q4 AUMU' B6d U2 SB0 B6a B6b B6c; lia]. }
    split. { apply (hm_sec_frame m m' WM h G7 WS); [apply IAG; vm_compute; reflexivity| |].
             - dpose WS as (_ & _ & S3 & S4 & S5 & _). rewrite S5.
               apply KOZ; [clear - ZP S3 S4; lia| clear - PA0 S3 S4; lia| clear - ZTP S3 S4; lia| unfold region_beg, kRegionSize in *; clear - ZPH S3 S4 U2 AUMU24 U1 U4; lia].
             - intros sh Hsh. destruct (In_nth_error _ _ Hsh) as [i' N'].
               pose proof (proj1 (Forall_forall _ _) (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 WS))))))) sh Hsh) as (_ & SZ & _).
               pose proof (z_sec_stk h GEO i' _ N') as Y1. pose proof (z_sec_hull h GEO i' _ N') as Y2. pose proof (z_sec_T h GEO i' _ N') as Y3.
               unfold zapart in Y1, Y2, Y3. cbn [fst snd] in Y1, Y2, Y3.
               (* [comment removed for export] *)
               dpose WK as (_ & _ & WKSEC). ddestruct (WKSEC i' sh N') as (k0 & Hk0 & P0 & MB0 & MS0).
               ddestruct (chunk_ext' h k0 WL0 WR WK Hk0) as (_ & _ & _ & _ & _ & [E5 _] & _ & _). unfold ext_lo in E5. rewrite P0, MB0 in E5.
               apply KOZ; [clear - Y1 SZ; lia| clear - E5 SZ; lia| clear - Y3 SZ; lia| unfold region_beg, kRegionSize in *; clear - Y2 SZ U2 AUMU24 U1 U4; lia]. }
    split. { unfold hm_fake in *.
             apply (fake_rep_frame m m' WM (l_fs (h_L h)) LF G8); [clear -FS0; lia| apply KOZ; unfold kFakeBytes in *; [clear -ZF; lia| clear - FS0; lia| clear - ZTF; lia| unfold region_beg, kRegionSize in *; clear - ZFH U2 AUMU24 U1 U4; lia]|].
             intros FB nB HFB. ddestruct G8 as (_ & _ & _ & LFW & _). destruct (LFW _ HFB) as (kf & ii & Hkf & Hii & EFB).
             pose proof (fsk_frame_inside (l_fs (h_L h)) kf ii Hkf Hii) as [I1 I2]. pose proof (fsk_sizes kf Hkf) as (SZ1 & _).
             assert (EF1 : FB = fsk_frame (l_fs (h_L h)) kf ii) by (clear -EFB; congruence). assert (EF2 : nB = fsk_bytes kf) by (clear -EFB; congruence).
             rewrite EF1, EF2. apply KOZ; unfold kFakeBytes in *; [clear - I1 I2 SZ1 ZF; lia| clear - I1 I2 SZ1 FS0; lia| clear - I1 I2 SZ1 ZTF; lia| unfold region_beg, kRegionSize in *; clear - I1 I2 SZ1 ZFH U2 AUMU24 U1 U4; lia]. }
    split; [apply (hm_ia_frame m m' WM h G9); apply IAG; vm_compute; reflexivity|].
    apply (hm_emb_frame_i m m' WM h h GE); [reflexivity| reflexivity| apply IAG; vm_compute; reflexivity].   (* [comment removed for export] *)
  Qed.
End KeepQ.

End ARUN_1.
