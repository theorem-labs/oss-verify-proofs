(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsDriverLaws AsSR AsChain FakeStackRep AllocWf AllocKit AllocRep AllocRepFacts AllocRepX SecLazy AsDepotInv AsDepotHash AG_Malloc2 AG_MallocLarge3 AG_MallocAll AS_InstDefs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Laws2.
  Context {HCEIL : HeapCeil}.
  Variable p : iparams.

  (* [comment removed for export] *)
  Lemma irheap_arheap : forall x LB m, as_RHEAP (KHp p) x LB m -> ARHEAP (i_s x) (lbp LB) m.
  Proof. intros x LB m R. exact (proj1 R). Qed.
  Lemma irheap_ids : forall x LB m, as_RHEAP (KHp p) x LB m -> Forall (fun b => blk_id b = blk_addr b /\ 1 <= blk_size b <= 2 ^ 28) LB.
  Proof. intros x LB m R. exact (proj1 (proj2 R)). Qed.
  Lemma irheap_ok : forall x LB m, as_RHEAP (KHp p) x LB m -> ast_ok (i_s x).
  Proof. intros x LB m R. exact (proj1 (proj1 (proj1 R))). Qed.
  Lemma lbp_In : forall b LB, In b LB -> In (blk_addr b, blk_size b) (lbp LB).
  Proof. intros b LB IN. unfold lbp. apply in_map_iff. exists b. auto. Qed.

  Lemma inst_RHEAP_blocks_disjoint : RHEAP_blocks_disjoint (KHp p).
  Proof.
    intros x LB m b1 b2 R I1 I2 NE.
    pose proof (irheap_ids _ _ _ R) as IDS.
    pose proof (proj1 (Forall_forall _ _) IDS b1 I1) as [E1 _]. pose proof (proj1 (Forall_forall _ _) IDS b2 I2) as [E2 _].
    assert (NEA : blk_addr b1 <> blk_addr b2) by congruence.
    pose proof (ARHEAP_blocks_disjoint_ok _ _ _ _ _ _ _ (irheap_arheap _ _ _ R) (lbp_In _ _ I1) (lbp_In _ _ I2) NEA) as D.
    assert (R1 : blk_size b1 <= round_up (blk_size b1) 8) by (unfold round_up; Z.div_mod_to_equations; lia).
    assert (R2 : blk_size b2 <= round_up (blk_size b2) 8) by (unfold round_up; Z.div_mod_to_equations; lia). lia.
  Qed.

  Lemma NoDup_map_fst_inj : forall (l : list (Z * Z)),
    List.NoDup l -> (forall a b, In a l -> In b l -> fst a = fst b -> a = b) -> List.NoDup (map fst l).
  Proof.
    intros l ND INJ. induction l as [|x l IH]; [constructor|].
    inversion ND as [|x' l' NI ND']; subst. cbn. constructor.
    - intros IN. apply in_map_iff in IN. destruct IN as (y & E & INy).
      assert (y = x) by (apply INJ; [right; exact INy| left; reflexivity| exact E]). subst y. exact (NI INy).
    - apply IH; [exact ND'|]. intros a b Ha Hb E. apply INJ; [right; exact Ha| right; exact Hb| exact E].
  Qed.

  Lemma inst_RHEAP_blocks_nodup : RHEAP_blocks_nodup (KHp p).
  Proof.
    intros x LB m R. pose proof (irheap_ids _ _ _ R) as IDS. pose proof (irheap_arheap _ _ _ R) as (HA & ND & EQ).
    pose proof (irheap_ok _ _ _ R) as OK.
    replace (map blk_id LB) with (map fst (lbp LB)).
    2:{ unfold lbp. rewrite map_map. apply map_ext_in. intros b Hb. cbn. symmetry. exact (proj1 (proj1 (Forall_forall _ _) IDS b Hb)). }
    apply NoDup_map_fst_inj; [exact ND|].
    intros [A1 n1] [A2 n2] I1 I2 E. cbn in E. subst A2.
    apply EQ in I1. apply EQ in I2.
    destruct (alb_In _ _ _ I1) as (ch1 & C1 & S1 & U1 & N1). destruct (alb_In _ _ _ I2) as (ch2 & C2 & S2 & U2 & N2).
    assert (ch1 = ch2) by (apply (proj1 (proj2 (proj2 (proj2 (proj2 OK))))); [exact C1| exact C2| congruence]).
    subst ch2. congruence.
  Qed.

  (* [comment removed for export] *)
  Lemma irheap_placed : forall x LB m, as_RHEAP (KHp p) x LB m -> placed_ok (i_s x).
  Proof. intros x LB m R. exact (proj1 (irheap_ok _ _ _ R)). Qed.

  Lemma inst_RHEAP_fsb : RHEAP_fsb (KHp p).
  Proof.
    intros x LB m R. pose proof (irheap_placed _ _ _ R) as PL.
    pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    pose proof R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EF & MF & _).
    unfold afsb_ok. cbn [as_FSB KHp]. rewrite <- EF.
    pose proof (aapp_env _ _ F1 ltac:(unfold AFS_SIZE; lia)) as [E1 E2].
    split; [unfold AIMG_TOP; lia|]. split; [exact F2|]. split; [rewrite EF; exact MF| exact F1].
  Qed.

  Lemma inst_RHEAP_thr : RHEAP_thr (KHp p).
  Proof.
    intros x LB m R. pose proof (irheap_placed _ _ _ R) as PL.
    pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    pose proof R as (HA & _ & _ & _ & _ & _ & _ & _ & _ & _ & EF & MF & DD & TH & (tb & te & TLS) & _).
    destruct HA as ((_ & _ & FL & TR & _) & _ & _).
    pose proof FL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TSD & _ & _).
    pose proof TR as (_ & _ & CT & _).
    destruct TH as (T1' & T2' & DB1 & DB2 & DB3 & DB4).
    pose proof (aapp_env _ _ X2 ltac:(lia)) as [C1 C2]. pose proof (akobj_env _ _ T2 ltac:(unfold kPageSize; lia)) as [K1 K2].
    exists (a_ctx (i_s x)), (a_thr (i_s x)), (ip_D p), tb, te.
    split; [exact TSD|]. split; [exact CT|]. split; [exact TLS|]. split; [exact T1'|]. split; [exact T2'|].
    unfold kPageSize in *. repeat split; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sec_chunk_slack : forall st ch, WF st -> In ch (chunk_list st) -> ch_primary ch = false ->
    ch_user_beg ch + ch_used ch + 16 <= ch_end ch.
  Proof.
    intros st ch W Hin NP. pose proof (WF_chunk st ch W Hin) as (U1 & U2 & U3 & U4 & REST). rewrite NP in REST.
    destruct REST as (P1 & _).
    pose proof (rz_size_facts (ch_used ch)) as (RZ1 & RZ2 & _).
    unfold ch_end. rewrite NP. rewrite U4, U3.
    assert (ND : rq_needed (compute_req (ch_used ch)) = round_up (Z.max (ch_used ch) 8) 8 + rz_size (ch_used ch) + rz_size (ch_used ch)
                 /\ rq_rz (compute_req (ch_used ch)) = rz_size (ch_used ch)).
    { revert P1. unfold compute_req. cbn -[Z.add Z.mul Z.max round_up rz_size Z.leb Z.eqb kMaxSize].
      destruct (round_up (Z.max (ch_used ch) 8) 8 + rz_size (ch_used ch) <=? kMaxSize); cbn; [congruence| intros _; split; reflexivity]. }
    destruct ND as [ND RZ]. rewrite ND, RZ.
    unfold round_up, kPageSize. Z.div_mod_to_equations. nia.
  Qed.

  Lemma inst_RHEAP_block_range : RHEAP_block_range (KHp p).
  Proof.
    intros x LB m b R IN. pose proof (irheap_placed _ _ _ R) as PL. pose proof (irheap_ok _ _ _ R) as OK.
    pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    pose proof R as (HA & _ & _ & _ & _ & _ & _ & _ & _ & _ & EF & _).
    pose proof (ARHEAP_block_range_ok _ _ _ _ _ HA (lbp_In _ _ IN)) as (B1 & B2 & B3 & B4 & B5).
    unfold ablock_range. cbn [as_FSB KHp]. rewrite <- EF.
    split; [unfold AIMG_TOP in B1; lia|]. split; [exact B2|]. split; [lia|]. split; [exact B1|]. split; [exact B4|]. split; [| exact B5].
    (* [comment removed for export] *)
    destruct HA as (HA & ND & EQ). pose proof (lbp_In _ _ IN) as INp. apply EQ in INp.
    destruct (alb_In _ _ _ INp) as (ch & Hch & _ & U0 & N0).
    pose proof (chunk_geom _ OK ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & G7). pose proof (ext_facts _ OK ch Hch) as (E1 & E2 & E3 & EP & ES).
    rewrite <- U0, <- N0. unfold disj, AFS_SIZE, AsIface.AFS_SIZE, kSpaceSize, kPageSize in *.
    destruct (ch_primary ch) eqn:PR.
    - destruct (EP eq_refl) as (_ & EE & SB1 & SB2). clear - G1 G2 G4 G5 SB1 SB2 D6. lia.
    - destruct (ES eq_refl) as (h & Hh & HL & HE & HB). pose proof (SEC h Hh) as (_ & _ & _ & _ & _ & _ & _ & _ & DF).
      pose proof (sec_chunk_slack _ ch (proj2 OK) Hch PR) as SL. unfold disj in DF. unfold AsIface.AFS_SIZE in *.
      clear - G1 G2 SL HL HE HB DF E3. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma inst_rheap_perm : forall x LB LB' m, as_RHEAP (KHp p) x LB m -> Permutation LB LB' -> as_RHEAP (KHp p) x LB' m.
  Proof.
    intros x LB LB' m R P. pose proof R as ((HA & ND & EQ) & IDS & CNT & REST).
    assert (PP : Permutation (lbp LB) (lbp LB')) by (unfold lbp; apply Permutation_map; exact P).
    split; [| split; [| split; [| exact REST]]].
    - split; [exact HA|]. split; [eapply Permutation_NoDup; [exact PP| exact ND]|].
      intros b. rewrite <- (EQ b). split; intros K; [eapply Permutation_in; [apply Permutation_sym; exact PP| exact K]| eapply Permutation_in; [exact PP| exact K]].
    - eapply Permutation_Forall; [exact P| exact IDS].
    - rewrite <- (Permutation_length P). exact CNT.
  Qed.

  Lemma inst_slack_law : forall x LB m pid A n,
    as_RHEAP (KHp p) x LB m -> In (pid, A, n) LB -> wr_at asegs m (A + n) ((- (A + n)) mod 8).
  Proof.
    intros x LB m pid A n R IN. pose proof (irheap_ok _ _ _ R) as OK.
    pose proof R as (HA0 & _).
    pose proof (ARHEAP_block_range_ok _ _ _ _ _ HA0 (lbp_In _ _ IN)) as (B1 & B2 & B3 & B4 & B5). cbn [blk_addr blk_size fst snd] in B1, B2, B3, B4, B5.
    destruct HA0 as (HA & ND & EQ). pose proof (lbp_In _ _ IN) as INp. cbn [blk_addr blk_size fst snd] in INp. apply EQ in INp.
    destruct (alb_In _ _ _ INp) as (ch & Hch & STc & U0 & N0).
    pose proof (chunk_geom _ OK ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    pose proof HA as (_ & _ & _ & _ & _ & _ & _ & CR & _). specialize (CR ch Hch).
    destruct CR as (_ & _ & ALLOC & JK & _). rewrite STc in ALLOC. destruct ALLOC as [WRu _].
    rewrite U0, N0 in *. destruct WRu as (W1 & W2 & W3).
    assert (SL : (- (A + n)) mod 8 = round_up n 8 - n).
    { unfold round_up in *. acb. Z.div_mod_to_equations. nia. }
    split; [lia|]. split.
    - pose proof aceil_range. lia.
    - intros i Hi. unfold junk in JK. specialize (JK ltac:(lia)). destruct JK as (_ & _ & JK). apply (proj1 (JK (A + n + i) ltac:(lia))).
  Qed.

  (* [comment removed for export] *)
  Lemma inst_canary_law : forall x LB m, as_RHEAP (KHp p) x LB m ->
    exists can : Z, rw_cells asegs m AGOT_SSP [C8 (Z_to_bv 64 ASSPGUARD)] /\ rw_cells asegs m ASSPGUARD [C8 (Z_to_bv 64 can)] /\ 0 <= can < 2^64.
  Proof.
    intros x LB m R. pose proof R as (_ & _ & _ & _ & FLX & _). destruct FLX as (_ & GOT & [g CAN] & _).
    exists (bv_unsigned g). pose proof (bv_unsigned_in_range _ g) as GR.
    split; [exact GOT|]. split; [rewrite Z_to_bv_bv_unsigned; exact CAN| exact GR].
  Qed.
End Laws2.
