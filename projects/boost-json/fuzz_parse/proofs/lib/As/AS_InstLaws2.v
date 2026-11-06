(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AsConst AsIface AsDriverLaws AsSR AsChain FakeStackRep AllocWf AllocKit AllocRep AllocRepFacts AllocRepX SecLazy AsDepotInv AsDepotHash AG_Malloc2 AG_MallocLarge3 AG_MallocAll AS_InstDefs.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAS_InstDefs~~~~~~03KHp37Corelib4Init9Datatypesk64list03i_s03lbp79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AllocRep~~~~~~mf6ARHEAP79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsIface~~~~~~r68as_RHEAPr65as_Str65blockr63mem37Corelib4Init5Logichh43andr68blk_size46Stdlib6ZArith6BinInt1Zhja2lehh42eq37Corelib5Lists7ListDefhle6Forallr68blk_addrr66blk_idr64bptrhja3powmf6ast_ok37Corelib7Numbers7BinNumshqa1Z36Stdlib5Lists4Lisths82Ink64pairk64prodr6h5RHEAP_blocks_disjointk63fsths85NoDuphle3mapr6h2RHEAP_blocks_nodupmf9placed_okr69RHEAP_fsbr69RHEAP_thr69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~il85chunkhja3addk64boolk65falsemf6ch_end79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AllocWf~~~~~~is12WFil86astateil8ach_primaryil87ch_usedil8bch_user_begil8achunk_listr6h1RHEAP_block_ranger6bclass_bytes36Stdlib7SortingbPermutationjm7bPermutationr6aRHEAP_perm07iparams" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Laws2.
  Context {HCEIL : HeapCeil}.
  Variable p : ltac2:(zQ "10!jpf$0").

  (* [comment removed for export] *)
  Lemma irheap_arheap : ltac2:(zQ "90!k1!le!m5!ma!qd!v3!ve!hg6!hge>1x@1$6@2$0?5HCEIL?1p>2LB@1$1$7>1m$8>0@4$5@2$0?5HCEIL?1p^3^2^1@4$4?5HCEIL@2$2?5HCEIL^4@1$3^3^2").
  Proof. intros x LB m R. exact (proj1 R). Qed.
  Lemma irheap_ids : ltac2:(zQ "f0!hg6!hi8!k1!hif!hl2!le!hl8!hn5!v3!ve!hnf!hoa!hp3!hge!hpa>1x@1$9@2$2?5HCEIL?1p>2LB@1$5$0>1m$d>0@4$8@2$2?5HCEIL?1p^3^2^1@3$7$0\1b$0@2$1@3$6$c@1$b^1@1$a^1@2$1@2$4+1@1$3^1@2$4@1$3^1@2$e+2+hf^3").
  Proof. intros x LB m R. exact (proj1 (proj2 R)). Qed.
  Lemma irheap_ok : ltac2:(zQ "80!k1!le!m5!hq1!v3!ve!hg6!hge>1x@1$5@2$0?5HCEIL?1p>2LB@1$1$6>1m$7>0@4$4@2$0?5HCEIL?1p^3^2^1@2$3?5HCEIL@2$2?5HCEIL^4").
  Proof. intros x LB m R. exact (proj1 (proj1 (proj1 R))). Qed.
  Lemma lbp_In : ltac2:(zQ "90!hs3!hg6!htb!le!hu1!hu8!ma!hnf!hif>1b$1>2LB@1$3$1>0@3$2$1^2^1@3$2@2$5$0$0@4$4$0$0@1$7^3@1$8^3@1$6^2").
  Proof. intros b LB IN. unfold lbp. apply in_map_iff. exists b. auto. Qed.

  Lemma inst_RHEAP_blocks_disjoint : ltac2:(zQ "20!k1!huf@1$1@2$0?5HCEIL?1p").
  Proof.
    intros x LB m b1 b2 R I1 I2 NE.
    pose proof (irheap_ids _ _ _ R) as IDS.
    pose proof (proj1 (Forall_forall _ _) IDS b1 I1) as [E1 _]. pose proof (proj1 (Forall_forall _ _) IDS b2 I2) as [E2 _].
    assert (NEA : blk_addr b1 <> blk_addr b2) by congruence.
    pose proof (ARHEAP_blocks_disjoint_ok _ _ _ _ _ _ _ (irheap_arheap _ _ _ R) (lbp_In _ _ I1) (lbp_In _ _ I2) NEA) as D.
    assert (R1 : blk_size b1 <= round_up (blk_size b1) 8) by (unfold round_up; Z.div_mod_to_equations; lia).
    assert (R2 : blk_size b2 <= round_up (blk_size b2) 8) by (unfold round_up; Z.div_mod_to_equations; lia). lia.
  Qed.

  Lemma NoDup_map_fst_inj : ltac2:(zQ "80!hs3!hu8!ig8!hl8!htb!ige!le!ih7>1l@1$6@2$1$0$0>0@2$5@2$1$0$0^1>0>1a@2$1$0$0>1b@2$1$0$0>0@3$4@2$1$0$0^2^4>0@3$4@2$1$0$0^2^5>0@3$3$0@3$2$0$0^4@3$2$0$0^3@3$3@2$1$0$0^5^4@2$5$0@4$7@2$1$0$0$0@2$2$0$0^3").
  Proof.
    intros l ND INJ. induction l as [|x l IH]; [constructor|].
    inversion ND as [|x' l' NI ND']; subst. cbn. constructor.
    - intros IN. apply in_map_iff in IN. ndestruct IN as (y & E & INy).
      assert (y = x) by (apply INJ; [right; exact INy| left; reflexivity| exact E]). subst y. exact (NI INy).
    - apply IH; [exact ND'|]. intros a b Ha Hb E. apply INJ; [right; exact Ha| right; exact Hb| exact E].
  Qed.

  Lemma inst_RHEAP_blocks_nodup : ltac2:(zQ "20!k1!ihe@1$1@2$0?5HCEIL?1p").
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
  Lemma irheap_placed : ltac2:(zQ "80!k1!le!m5!ij4!v3!ve!hg6!hge>1x@1$5@2$0?5HCEIL?1p>2LB@1$1$6>1m$7>0@4$4@2$0?5HCEIL?1p^3^2^1@2$3?5HCEIL@2$2?5HCEIL^4").
  Proof. intros x LB m R. exact (proj1 (irheap_ok _ _ _ R)). Qed.

  Lemma inst_RHEAP_fsb : ltac2:(zQ "20!k1!ik0@2$1?5HCEIL@2$0?5HCEIL?1p").
  Proof.
    intros x LB m R. pose proof (irheap_placed _ _ _ R) as PL.
    npose PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    npose R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EF & MF & _).
    unfold afsb_ok. cbn [as_FSB KHp]. rewrite <- EF.
    pose proof (aapp_env _ _ F1 ltac:(unfold AFS_SIZE; lia)) as [E1 E2].
    split; [unfold AIMG_TOP; lia|]. split; [exact F2|]. split; [rewrite EF; exact MF| exact F1].
  Qed.

  Lemma inst_RHEAP_thr : ltac2:(zQ "20!k1!ikc@2$1?5HCEIL@2$0?5HCEIL?1p").
  Proof.
    intros x LB m R. pose proof (irheap_placed _ _ _ R) as PL.
    npose PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    npose R as (HA & _ & _ & _ & _ & _ & _ & _ & _ & _ & EF & MF & DD & TH & (tb & te & TLS) & _).
    ndestruct HA as ((_ & _ & FL & TR & _) & _ & _).
    npose FL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TSD & _ & _).
    npose TR as (_ & _ & CT & _).
    ndestruct TH as (T1' & T2' & DB1 & DB2 & DB3 & DB4).
    pose proof (aapp_env _ _ X2 ltac:(lia)) as [C1 C2]. pose proof (akobj_env _ _ T2 ltac:(unfold kPageSize; lia)) as [K1 K2].
    nexists (a_ctx (i_s x)), (a_thr (i_s x)), (ip_D p), tb, te.
    split; [exact TSD|]. split; [exact CT|]. split; [exact TLS|]. split; [exact T1'|]. split; [exact T2'|].
    unfold kPageSize in *. repeat split; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sec_chunk_slack : ltac2:(zQ "e0!ip9!iq2!iq9!ir0!hl8!ir8!ive!jg4!jge!jhc!ji7!jj6!htb!hl2>2st$7>2ch$0>0@1$6^2>0@3$c$0^2@1$b^3>0@3$4$2@1$8^3$3@2$d@2$1@2$1@1$a^4@1$9^4+h0@1$5^4").
  Proof.
    intros st ch W Hin NP. npose (WF_chunk st ch W Hin) as (U1 & U2 & U3 & U4 & REST). rewrite NP in REST.
    destruct REST as (P1 & _).
    npose (rz_size_facts (ch_used ch)) as (RZ1 & RZ2 & _).
    unfold ch_end. rewrite NP. rewrite U4, U3.
    assert (ND : rq_needed (compute_req (ch_used ch)) = round_up (Z.max (ch_used ch) 8) 8 + rz_size (ch_used ch) + rz_size (ch_used ch)
                 /\ rq_rz (compute_req (ch_used ch)) = rz_size (ch_used ch)).
    { revert P1. unfold compute_req. cbn -[Z.add Z.mul Z.max round_up rz_size Z.leb Z.eqb kMaxSize].
      destruct (round_up (Z.max (ch_used ch) 8) 8 + rz_size (ch_used ch) <=? kMaxSize); cbn; [congruence| intros _; split; reflexivity]. }
    destruct ND as [ND RZ]. rewrite ND, RZ.
    unfold round_up, kPageSize. Z.div_mod_to_equations. nia.
  Qed.

  Lemma inst_RHEAP_block_range : ltac2:(zQ "20!k1!jk4@2$1?5HCEIL@2$0?5HCEIL?1p").
  Proof.
    intros x LB m b R IN. pose proof (irheap_placed _ _ _ R) as PL. pose proof (irheap_ok _ _ _ R) as OK.
    npose PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    npose R as (HA & _ & _ & _ & _ & _ & _ & _ & _ & _ & EF & _).
    pose proof (ARHEAP_block_range_ok _ _ _ _ _ HA (lbp_In _ _ IN)) as (B1 & B2 & B3 & B4 & B5).
    unfold ablock_range. cbn [as_FSB KHp]. rewrite <- EF.
    split; [unfold AIMG_TOP in B1; lia|]. split; [exact B2|]. split; [lia|]. split; [exact B1|]. split; [exact B4|]. split; [| exact B5].
    (* [comment removed for export] *)
    ndestruct HA as (HA & ND & EQ). pose proof (lbp_In _ _ IN) as INp. apply EQ in INp.
    destruct (alb_In _ _ _ INp) as (ch & Hch & _ & U0 & N0).
    pose proof (chunk_geom _ OK ch Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & G7). pose proof (ext_facts _ OK ch Hch) as (E1 & E2 & E3 & EP & ES).
    rewrite <- U0, <- N0. unfold disj, AFS_SIZE, AsIface.AFS_SIZE, kSpaceSize, kPageSize in *.
    destruct (ch_primary ch) eqn:PR.
    - ndestruct (EP eq_refl) as (_ & EE & SB1 & SB2). clear - G1 G2 G4 G5 SB1 SB2 D6. lia.
    - ndestruct (ES eq_refl) as (h & Hh & HL & HE & HB). npose (SEC h Hh) as (_ & _ & _ & _ & _ & _ & _ & _ & DF).
      pose proof (sec_chunk_slack _ ch (proj2 OK) Hch PR) as SL. unfold disj in DF. unfold AsIface.AFS_SIZE in *.
      clear - G1 G2 SL HL HE HB DF E3. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma class_bytes_perm : ltac2:(zQ "60!hg6!le!hs3!jl9!hl8!jo3>2LB@1$1$0>3LB'@1$1$0>1c$2>0@3$5$0^3^2@3$4$2@2$3^4^2@2$3^3^2").
  Proof. intros LB LB' c P. unfold class_bytes. induction P; cbn [fold_right] in *; lia. Qed.
  Lemma inst_RHEAP_perm : ltac2:(zQ "20!k1!jp2@1$1@2$0?5HCEIL?1p").
  Proof.
    intros x LB LB' m R P. cbn [as_RHEAP KHp] in *. unfold IRHEAP in *. cbv zeta in R. cbv zeta.
    ndestruct R as ((HA & ND & EQ) & IDS & LEN & REST).
    assert (PL : Permutation (lbp LB) (lbp LB')) by (unfold lbp; apply Permutation_map; exact P).
    split; [| split; [| split]].
    - split; [exact HA|]. split; [exact (Permutation_NoDup PL ND)|].
      intros b. rewrite <- (EQ b). split; intros Hb; [apply (Permutation_in b (Permutation_sym PL) Hb)| apply (Permutation_in b PL Hb)].
    - apply Forall_forall. intros b Hb. apply (proj1 (Forall_forall _ _) IDS). apply (Permutation_in b (Permutation_sym P) Hb).
    - rewrite <- (Permutation_length P). exact LEN.
    - repeat match type of REST with _ /\ _ => let H := fresh "C" in destruct REST as [H REST]; split; [exact H|] end.
      intros c Hc. rewrite <- (class_bytes_perm LB LB' c P). exact (REST c Hc).
  Qed.
End Laws2.
(* [comment removed for export] *)
