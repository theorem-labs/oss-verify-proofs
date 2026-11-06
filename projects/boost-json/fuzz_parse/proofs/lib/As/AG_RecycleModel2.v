(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil AsanAllocModel AsanAllocCons.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AW_MergeBatches AW_Recycle.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~06qbatch37Corelib4Init9Datatypesk94list37Corelib7Numbers7BinNumsm81Zk94prod37Corelib4Init5Logicoc2exk94pair0akBatchSize07qb_size46Stdlib6ZArith6BinInt1Zs12lek94Somek96lengthk93natk96optionoc2eq37Corelib4Init5Peanohg22lt37Corelib5Lists7ListDefhhc6Forall0h1merge_batches_aux79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsfAW_MergeBatches~~~~~~hl14bsum09pop_while06astateoc3and05as_gq0aas_regions0cas_space_beg05as_tq06qcache06region79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Ash0AG_RecycleModel2~~~~~~huf2qq69OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanAllocCons~~~~~~ijc9same_core06effect0dcache_dealloc0acb_recycle0fcb_recycle_list0ado_recycle0|41m1k1Q1Chl13bok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAW_Recycle~~~~~~itb6rsplit" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma merge_batches_aux_total : ltac2:(zQ "h10!k1!m1!o1!o5!q0!q5!qc!r8!t9!te!u5!ue!v4!vd!hh6!hj3!hjd>4fuel$b>3cur$0>4rest@1$1$0>5rdone@1$1$0>3rex@1$1$0>2xb$2>0@2$e@2$a$0^4^6>0@2$8$6@1$7^6>0@3$f$0\1b$0@2$8$6@1$7^1^6@2$4@1$1$0\2l'@1$1$0@2$4@1$1$0\2ex@1$1$0@2$4$2\3xb'$2@3$d@1$c@2$3@2$3@1$1$0@1$1$0$2@6$h0^c^b^a^9^8^7@2$9@2$3@2$3@1$1$0@1$1$0$2@4$5@2$3@1$1$0@1$1$0$2@4$5@1$1$0@1$1$0^3^2^1").
Proof.
  intros fuel. induction fuel as [|fuel IH]; intros cur rest rdone rex xb FU SC SR; [exfalso; lia|].
  cbn [merge_batches_aux]. destruct rest as [|nx rest'].
  - neexists 3. reflexivity.
  - apply Forall_cons_iff in SR. destruct SR as [SN SR']. cbn [length] in FU.
    destruct (qb_count cur + qb_count nx <=? kBatchCount).
    + replace (qb_size cur <? kBatchSize) with false by (symmetry; apply Z.ltb_ge; exact SC).
      apply IH; [lia| cbn [qb_size]; lia| exact SR'].
    + apply IH; [lia| exact SN| exact SR'].
Qed.

Lemma pop_while_total : ltac2:(zQ "h20!k1!m1!o1!o5!q0!q5!vd!t9!te!u5!ue!v4!hh6!hj3!hp6!qc!hpe!r8>4fuel$a>1l@1$1$0>5bytes$2>8min_size$2>3acc@1$1$0>0@2$c@2$9$0^4^5>0@2$7Z^3>0@3$6$2^5@1$e^6>0@3$d$0\1b$0@2$7$f@1$h1^1^7@2$4@1$1$0\2l2@1$1$0@2$4$2\2b2$2@2$4@1$1$0\1r@1$1$0@3$6@1$b@2$3@2$3@1$1$0$2@1$1$0@5$h0^c^b^a^9^8@2$8@2$3@2$3@1$1$0$2@1$1$0@4$5@2$3@1$1$0$2@1$1$0@4$5@1$1$0$2^3^2^1").
Proof.
  intros fuel. induction fuel as [|fuel IH]; intros l bytes min_size acc FU MN BY SZ; [exfalso; lia|].
  rewrite pop_while_step. destruct (Z.leb_spec bytes min_size) as [LE|GT]; [neexists 3; reflexivity|].
  destruct l as [|b r].
  - exfalso. rewrite bsum_nil in BY. lia.
  - apply Forall_cons_iff in SZ. destruct SZ as [SB SR]. cbn [length] in FU. rewrite bsum_cons in BY.
    apply IH; [lia| exact MN| lia| exact SR].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition qq : ltac2:(zQ "10!hq9>2st$0>3st'$0P") := ltac2:(zQ "c0!vd!hr1!u5!hr7!hre!hsa!ht8!hq9!htf!hu7!ue!o1\2st$7\3st'$7@2$1@3$0$8@1$6^1@1$6^2@2$1@3$0$8@1$3^1@1$3^2@2$1@3$0$b@1$5^1@1$5^2@3$0$a@2$2$9@1$4^1@2$2$9@1$4^2").
Lemma qq_refl : ltac2:(zQ "20!ij6!hq9>2st$1@2$0^1^1"). Proof. intros; repeat split; reflexivity. Qed.
Lemma qq_trans : ltac2:(zQ "20!ij6!hq9>1a$1>1b$1>1c$1>0@2$0^3^2>0@2$0^3^2@2$0^5^3").
Proof. (intros a b c nd_i1 nd_i2; ndestruct nd_i1 as (A1 & A2 & A3 & A4); ndestruct nd_i2 as (B1 & B2 & B3 & B4)). unfold qq. rewrite B1, B2, B3, B4. repeat split; assumption. Qed.
Lemma qq_of_core : ltac2:(zQ "30!hq9!ij6!inc>1a$0>1b$0>0@2$2^2^1@2$1^2^3").
Proof. intros a b H. ndestruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & _). unfold qq. rewrite H3. repeat split; assumption || reflexivity. Qed.

Lemma cache_dealloc_qq : ltac2:(zQ "h00!hq9!m1!io9!o5!vd!o1!te!u5!ue!v4!q5!ij6!hre!ip1!hu7!t9>2st$0>1c$5>1p$5>3st'$0>2ev@1$1$2>0@3$4$8@2$7$e@1$c^5Ni0>0@2$fZ^5>0@3$4@1$9@2$3$0@1$1$2@3$d^7^6^5@2$6@2$3$0@1$1$2@4$a$0@1$1$2^4^3@2$b^8^5").
Proof.
  intros st c p st' ev L C H. ndestruct (cache_dealloc_frame st c p st' ev L C H) as (_ & SB & LR & _ & TQ & GQ & _).
  unfold qq. rewrite L. repeat split; assumption.
Qed.

Lemma cb_recycle_qq : ltac2:(zQ "f0!hq9!m1!io9!o5!vd!te!u5!ue!v4!q5!o1!ij6!hre!iq0!hu7>2st$0>1m$a>3st'$0>2ev@1$1$2>0@3$4$7@2$6$e@1$c^4Ni0>0@3$4@1$8@2$3$0@1$1$2@2$d^5^4@2$5@2$3$0@1$1$2@4$9$0@1$1$2^3^2@2$b^6^4").
Proof.
  intros st m st' ev L H. unfold cb_recycle in H.
  destruct (find_chunk (as_chunks st) (m + kChunkHeaderSize)) as [ch|]; [| discriminate H].
  destruct (ch_state ch); [discriminate H|]. destruct (in_primary st m).
  - cbv zeta in H. destruct (class_of_addr st m =? 0); [discriminate H|].
    destruct (rg_mapped_user _ <? _); [discriminate H|]. destruct (negb _); [discriminate H|].
    destruct (poison_shadow st _ _ _) as [[st1 ev1]|] eqn:P; [| discriminate H].
    destruct (cache_dealloc _ _ _) as [[st3 ev3]|] eqn:CD; [| discriminate H]. injection H as <- _.
    pose proof (qq_of_core _ _ (poison_shadow_core _ _ _ _ _ _ P)) as Q1.
    assert (Q2 : qq st1 (set_chunks st1 (remove_chunk (as_chunks st1) (ch_user_beg ch)))) by (repeat split; reflexivity).
    assert (L2 : length (as_regions (set_chunks st1 (remove_chunk (as_chunks st1) (ch_user_beg ch)))) = 32%nat).
    { ndestruct Q1 as (_ & _ & _ & E1). cbn [as_regions set_chunks]. rewrite E1. exact L. }
    assert (C0 : 0 <= class_of_addr st m) by (unfold class_of_addr; apply (proj2 (Z.land_nonneg _ _)); right; lia).
    pose proof (cache_dealloc_qq _ _ _ _ _ L2 C0 CD) as Q3.
    eapply qq_trans; [exact Q1| eapply qq_trans; [exact Q2| exact Q3]].
  - destruct (large_get_block_begin st m) as [p|]; [| discriminate H]. destruct (p =? 0); [discriminate H|].
    destruct (in_primary st p); [discriminate H|]. destruct (negb _); [discriminate H|].
    destruct (large_deallocate _ p) as [[st2 ev2]|] eqn:LD; [| discriminate H]. injection H as <- <-.
    destruct (large_deallocate_core _ _ _ _ LD) as [_ C]. apply qq_of_core in C.
    ndestruct C as (C1 & C2 & C3 & C4). cbn [as_tq as_gq as_space_beg as_regions set_sec set_chunks] in C1, C2, C3, C4.
    unfold qq. rewrite <- C1, <- C2, <- C3, <- C4. repeat split; reflexivity.
Qed.

Lemma cb_recycle_list_qq : ltac2:(zQ "f0!m1!hq9!io9!o5!vd!te!u5!ue!v4!q5!o1!ij6!hre!iqc!hu7>2ms@1$0$a>2st$1>4racc@1$0$2>3st'$1>5racc'@1$0$2>0@3$4$7@2$6$e@1$c^4Ni0>0@3$4@1$8@2$3$1@1$0$2@3$d^5^6^4@2$5@2$3$1@1$0$2@4$9$1@1$0$2^3^2@2$b^6^4").
Proof.
  induction ms as [|m ms IH]; intros st racc st' racc' L H; cbn [cb_recycle_list] in H.
  - injection H as <- _. apply qq_refl.
  - destruct (cb_recycle st m) as [[st1 ev1]|] eqn:R; [| discriminate H].
    pose proof (cb_recycle_qq _ _ _ _ L R) as Q1. npose Q1 as (_ & _ & _ & L1). rewrite L in L1.
    eapply qq_trans; [exact Q1| exact (IH st1 _ _ _ L1 H)].
Qed.

Lemma do_recycle_qq : ltac2:(zQ "f0!m1!hq9!io9!o5!vd!te!u5!ue!v4!q5!ij6!hre!ird!k1!hu7>2bs@1$0$d>2st$1>4racc@1$0$2>3st'$1>5racc'@1$0$2>0@3$4$7@2$6$e@1$b^4Ni0>0@3$4@1$8@2$3$1@1$0$2@3$c^5^6^4@2$5@2$3$1@1$0$2@4$9$1@1$0$2^3^2@2$a^6^4").
Proof.
  induction bs as [|b r IH]; intros st racc st' racc' L H; cbn [do_recycle] in H.
  - injection H as <- _. apply qq_refl.
  - destruct (cb_recycle_list st (qb_chunks b) racc) as [[st1 racc1]|] eqn:CL; [| discriminate H].
    pose proof (cb_recycle_list_qq _ _ _ _ _ L CL) as Q1. npose Q1 as (_ & _ & _ & L1). rewrite L in L1.
    destruct (negb (in_primary st1 (qb_addr b))); [discriminate H|].
    destruct (cache_dealloc st1 _ _) as [[st2 ev2]|] eqn:CD; [| discriminate H].
    assert (C0 : 0 <= class_of_addr st1 (qb_addr b)) by (unfold class_of_addr; apply (proj2 (Z.land_nonneg _ _)); right; lia).
    pose proof (cache_dealloc_qq _ _ _ _ _ L1 C0 CD) as Q2. npose Q2 as (_ & _ & _ & L2). rewrite L1 in L2.
    eapply qq_trans; [exact Q1| eapply qq_trans; [exact Q2| exact (IH st2 _ _ _ L2 H)]].
Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.

  Theorem rsplit_total : ltac2:(zQ "h00!k1!m1!o5!o1!q0!htf!q5!vd!is9!te!v4!hj3!it4!hp6!jhb!t9>1l@1$1$0>6qbytes$3>4qmin$3>0@3$b$0@1$c?5HCEIL^3>0@3$7$3^3@1$d^4>0@2$fZ^3@2$4@1$1$0\2l2@1$1$0@2$4$3\2b2$3@2$4@1$1$0\2ex@1$1$0@2$4@1$1$0\2rp@1$1$0@3$7@1$a@2$2@2$2$5@1$1$0@1$1$0@2$e@2$8^a^9^8@2$9@2$2@2$2$5@1$1$0@1$1$0@4$6@2$2$5@1$1$0@1$1$0@4$6$5@1$1$0@2$8^4^3^2^1").
  Proof.
    intros l qbytes qmin OKL QB QM.
    assert (SZ : Forall (fun b => kBatchSize <= qb_size b) l).
    { apply Forall_forall. intros b Hb. pose proof (proj1 (Forall_forall _ _) OKL b Hb) as (_ & _ & _ & _ & _ & K & _). exact K. }
    pose proof (bsum_len l OKL) as BL.
    unfold rsplit. cbn [qc_list qc_bytes].
    replace (qbytes <? zlen l * kBatchSize) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct ((zlen l * kBatchSize <? qbytes) && (qbytes * 100 <? zlen l * kBatchSize * 200)).
    - (* [comment removed for export] *)
      destruct l as [|b r].
      + unfold merge_batches. cbn [qc_list qc_bytes length pop_while].
        replace (qbytes <=? qmin) with true by (symmetry; apply Z.leb_le; rewrite bsum_nil in QB; lia).
        neexists 4. reflexivity.
      + apply Forall_cons_iff in SZ. destruct SZ as [SB SR].
        ndestruct (merge_batches_aux_total (S (length r)) b r [] [] 0 ltac:(lia) SB SR) as (l' & ex & xb' & E).
        unfold merge_batches. cbn [qc_list qc_bytes]. rewrite E.
        pose proof (merge_batches_bsum (b :: r) qbytes l' (qbytes - xb') ex xb') as MB.
        unfold merge_batches in MB. cbn [qc_list qc_bytes] in MB. rewrite E in MB. specialize (MB eq_refl). ndestruct MB as (M1 & M2 & M3 & M4).
        assert (SZ' : Forall (fun b0 => kBatchSize <= qb_size b0) l').
        { (* [comment removed for export] *)
          clear - E SB SR.
          assert (G : forall fuel cur rest rdone rex xb l1 ex1 xb1,
                     kBatchSize <= qb_size cur -> Forall (fun b0 => kBatchSize <= qb_size b0) rest -> Forall (fun b0 => kBatchSize <= qb_size b0) rdone ->
                     merge_batches_aux fuel cur rest rdone rex xb = Some (l1, ex1, xb1) -> Forall (fun b0 => kBatchSize <= qb_size b0) l1).
          { intros fuel. induction fuel as [|fuel IH]; intros cur rest rdone rex xb l1 ex1 xb1 SC SRR SD H; [discriminate H|].
            cbn [merge_batches_aux] in H. destruct rest as [|nx rest'].
            - injection H as <- _ _. change (rev rdone ++ [cur]) with (rev (cur :: rdone)). apply Forall_rev. constructor; [exact SC| exact SD].
            - apply Forall_cons_iff in SRR. destruct SRR as [SN SRR'].
              destruct (qb_count cur + qb_count nx <=? kBatchCount).
              + destruct (qb_size cur <? kBatchSize); [discriminate H|].
                eapply (IH (mkQB (qb_addr cur) (qb_size cur + (qb_size nx - kBatchSize)) (qb_count cur + qb_count nx) (qb_chunks cur ++ qb_chunks nx)) rest' rdone _ _ l1 ex1 xb1);
                  [cbn [qb_size]; lia| exact SRR'| exact SD| exact H].
              + eapply (IH nx rest' (cur :: rdone) _ _ l1 ex1 xb1); [exact SN| exact SRR'| constructor; [exact SC| exact SD]| exact H]. }
          eapply (G (S (length r)) b r [] [] 0 l' ex xb'); [exact SB| exact SR| constructor| exact E]. }
        cbn [qc_list qc_bytes].
        ndestruct (pop_while_total (S (length l')) l' (qbytes - xb') qmin [] ltac:(lia) QM ltac:(lia) SZ') as (l2 & b2 & rp & P).
        rewrite P. neexists 4. reflexivity.
    - (* [comment removed for export] *)
      cbn [qc_list qc_bytes].
      ndestruct (pop_while_total (S (length l)) l qbytes qmin [] ltac:(lia) QM QB SZ) as (l2 & b2 & rp & P).
      rewrite P. neexists 4. reflexivity.
  Qed.
End HCW.
