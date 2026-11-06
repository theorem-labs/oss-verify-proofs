(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FMapPositive.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil AsanAllocModel BothAllocCons.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AllocWf AllocKit AllocRep AW_MergeBatches AW_Recycle AG_RecycleModel2.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~06astate05chunk0achunk_list36Stdlib5Lists4Listlc2In79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bsh0AG_RecycleModel3~~~~~~n44csub37Corelib4Init5Logics22eq09as_chunks37Corelib4Init9Datatypesu64list46Stdlib5FSetscFMapPositivebPositiveMaphg51t37Corelib7Numbers7BinNumshj11Z0cremove_chunk0aset_chunks06effectu64produ64Someu66lengthu63natu66optionu64pair0aas_regions0acb_recycle06region0fcb_recycle_list0ado_recycle06qbatch06qcache0|41m1k1Q1C79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAW_Recycle~~~~~~hv66rsplit46Stdlib6ZArith6BinInt1Zik02les23and05as_tq05as_gq08qc_bytes0h2quarantine_recycle" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition csub : ltac2:(zQ "10!k1>2st$0>3st'$0P") := ltac2:(zQ "40!k9!k1!l0!mf\2st$1\3st'$1>2ch$0>0@3$3$0^1@1$2^2@3$3$0^2@1$2^4").
Lemma csub_refl : ltac2:(zQ "20!k1!rb>2st$0@2$1^1^1"). Proof. intros st ch H. exact H. Qed.
Lemma csub_trans : ltac2:(zQ "20!k1!rb>1a$0>1b$0>1c$0>0@2$1^3^2>0@2$1^3^2@2$1^5^3").
Proof. intros a b c A B ch H. exact (A ch (B ch H)). Qed.
Lemma chunk_list_ext : ltac2:(zQ "70!t6!tb!k1!k9!l0!ve!hic>1a$2>1b$2>0@3$0@1$6$3@1$1^2@1$1^1@3$0@1$5$3@1$4^3@1$4^2").
Proof. intros a b E. unfold chunk_list. rewrite E. reflexivity. Qed.
Lemma csub_ext : ltac2:(zQ "60!tb!k1!t6!k9!rb!hic>2st$1>3st'$1>0@3$2@1$5$3@1$0^1@1$0^2@2$4^3^2").
Proof. intros st st' E ch H. rewrite (chunk_list_ext st' st E) in H. exact H. Qed.
Lemma csub_remove : ltac2:(zQ "60!hka!tb!k1!hkf!hld!rb>2st$2>1u$0@2$5^2@2$4^2@2$3@1$1^2^1").
Proof. intros st u ch H. exact (proj1 (proj1 (chunk_list_remove_iff st u ch) H)). Qed.

Lemma cb_recycle_csub : ltac2:(zQ "f0!k1!ve!hm9!hn1!t6!hn8!hnf!ho8!hoe!hp7!hka!hpe!hqa!hr6!rb>2st$0>1m$a>3st'$0>2ev@1$1$2>0@3$4$7@2$6$d@1$b^4Ni0>0@3$4@1$8@2$3$0@1$1$2@2$c^5^4@2$5@2$3$0@1$1$2@4$9$0@1$1$2^3^2@2$e^6^4").
Proof.
  intros st m st' ev L H. unfold cb_recycle in H.
  destruct (find_chunk (as_chunks st) (m + kChunkHeaderSize)) as [ch|]; [| discriminate H].
  destruct (ch_state ch); [discriminate H|]. destruct (in_primary st m).
  - cbv zeta in H. destruct (class_of_addr st m =? 0); [discriminate H|].
    destruct (rg_mapped_user _ <? _); [discriminate H|]. destruct (negb _); [discriminate H|].
    destruct (poison_shadow st _ _ _) as [[st1 ev1]|] eqn:P; [| discriminate H].
    destruct (cache_dealloc _ _ _) as [[st3 ev3]|] eqn:CD; [| discriminate H]. injection H as <- _.
    pose proof (poison_shadow_core _ _ _ _ _ _ P) as C1.
    assert (CH1 : as_chunks st1 = as_chunks st) by (ndestruct C1 as (_ & _ & _ & _ & _ & _ & _ & E & _); exact E).
    assert (L2 : length (as_regions (set_chunks st1 (remove_chunk (as_chunks st1) (ch_user_beg ch)))) = 32%nat).
    { pose proof (qq_of_core _ _ C1) as (_ & _ & _ & E1). cbn [as_regions set_chunks]. rewrite E1. exact L. }
    assert (C0 : 0 <= class_of_addr st m) by (unfold class_of_addr; apply (proj2 (Z.land_nonneg _ _)); right; lia).
    destruct (cache_dealloc_frame _ _ _ _ _ L2 C0 CD) as (CH3 & _).
    eapply csub_trans; [apply (csub_ext st st1 CH1)|]. eapply csub_trans; [apply (csub_remove st1 (ch_user_beg ch))|]. exact (csub_ext _ _ CH3).
  - destruct (large_get_block_begin st m) as [p|]; [| discriminate H]. destruct (p =? 0); [discriminate H|].
    destruct (in_primary st p); [discriminate H|]. destruct (negb _); [discriminate H|].
    destruct (large_deallocate_core _ _ _ _ H) as [CV _].
    assert (CH3 : as_chunks st' = as_chunks (set_chunks st (remove_chunk (as_chunks st) (ch_user_beg ch)))).
    { unfold cview in CV. injection CV as _ _ _ E _ _. exact E. }
    eapply csub_trans; [apply (csub_remove st (ch_user_beg ch))|]. exact (csub_ext _ _ CH3).
Qed.

Lemma cb_recycle_list_csub : ltac2:(zQ "f0!ve!k1!hm9!hn1!t6!hn8!hnf!ho8!hoe!hp7!hka!hpe!hre!hr6!rb>2ms@1$0$a>2st$1>4racc@1$0$2>3st'$1>5racc'@1$0$2>0@3$4$7@2$6$d@1$b^4Ni0>0@3$4@1$8@2$3$1@1$0$2@3$c^5^6^4@2$5@2$3$1@1$0$2@4$9$1@1$0$2^3^2@2$e^6^4").
Proof.
  induction ms as [|m ms IH]; intros st racc st' racc' L H; cbn [cb_recycle_list] in H.
  - injection H as <- _. apply csub_refl.
  - destruct (cb_recycle st m) as [[st1 ev1]|] eqn:R; [| discriminate H].
    pose proof (cb_recycle_qq _ _ _ _ L R) as (_ & _ & _ & L1). rewrite L in L1.
    eapply csub_trans; [exact (cb_recycle_csub _ _ _ _ L R)| exact (IH st1 _ _ _ L1 H)].
Qed.

Lemma do_recycle_csub : ltac2:(zQ "f0!ve!k1!hm9!hn1!t6!hn8!hnf!ho8!hoe!hp7!hpe!hsf!htb!hr6!rb>2bs@1$0$c>2st$1>4racc@1$0$2>3st'$1>5racc'@1$0$2>0@3$4$7@2$6$d@1$a^4Ni0>0@3$4@1$8@2$3$1@1$0$2@3$b^5^6^4@2$5@2$3$1@1$0$2@4$9$1@1$0$2^3^2@2$e^6^4").
Proof.
  induction bs as [|b r IH]; intros st racc st' racc' L H; cbn [do_recycle] in H.
  - injection H as <- _. apply csub_refl.
  - destruct (cb_recycle_list st (qb_chunks b) racc) as [[st1 racc1]|] eqn:CL; [| discriminate H].
    pose proof (cb_recycle_list_qq _ _ _ _ _ L CL) as (_ & _ & _ & L1). rewrite L in L1.
    destruct (negb (in_primary st1 (qb_addr b))); [discriminate H|].
    destruct (cache_dealloc st1 _ _) as [[st2 ev2]|] eqn:CD; [| discriminate H].
    assert (C0 : 0 <= class_of_addr st1 (qb_addr b)) by (unfold class_of_addr; apply (proj2 (Z.land_nonneg _ _)); right; lia).
    pose proof (cache_dealloc_qq _ _ _ _ _ L1 C0 CD) as (_ & _ & _ & L2). rewrite L1 in L2.
    destruct (cache_dealloc_frame _ _ _ _ _ L1 C0 CD) as (CH2 & _).
    eapply csub_trans; [exact (cb_recycle_list_csub _ _ _ _ _ L CL)|]. eapply csub_trans; [exact (csub_ext _ _ CH2)| exact (IH st2 _ _ _ L2 H)].
Qed.

(* [comment removed for export] *)
Lemma rsplit_le : ltac2:(zQ "c0!ve!htb!hn1!hu3!hp7!hka!hn8!hoe!t6!hub!ij6!il8>1g$3>4qmin$5>2l2@1$0$1>2b2$5>2ex@1$0$1>2rp@1$0$1>0@3$8@1$7@2$2@2$2$3@1$0$1@1$0$1@2$a^6^5@2$6@2$2@2$2$3@1$0$1@1$0$1@4$4@2$2$3@1$0$1@1$0$1@4$4$3@1$0$1@2$9^4^3^2^1@2$b^4^6").
Proof.
  intros g qmin l2 b2 ex rp R. unfold rsplit in R.
  destruct (qc_bytes g <? zlen (qc_list g) * kBatchSize); [discriminate R|].
  destruct ((zlen (qc_list g) * kBatchSize <? qc_bytes g) && (qc_bytes g * 100 <? zlen (qc_list g) * kBatchSize * 200)).
  - destruct (merge_batches g) as [[[g' ex'] xb]|]; [| discriminate R].
    destruct (pop_while (S (length (qc_list g'))) (qc_list g') (qc_bytes g') qmin []) as [[[l2' b2'] rp']|] eqn:PW; [| discriminate R].
    injection R as _ <- _ _. pose proof (pop_while_shape _ _ _ _ _ _ _ _ PW) as (popped & _ & _ & _ & LE). exact LE.
  - destruct (pop_while (S (length (qc_list g))) (qc_list g) (qc_bytes g) qmin []) as [[[l2' b2'] rp']|] eqn:PW; [| discriminate R].
    injection R as _ <- _ _. pose proof (pop_while_shape _ _ _ _ _ _ _ _ PW) as (popped & _ & _ & _ & LE). exact LE.
Qed.

(* [comment removed for export] *)
Theorem quarantine_recycle_final : ltac2:(zQ "h50!k1!ve!hm9!t6!hn1!ile!im4!hn8!hnf!ho8!hoe!hp7!hka!imb!hpe!in2!hu3!inc!hr6!rb!il8>2st$0>4qmin$c>3stR$0>3evR@1$1$2>0@3$3$9@2$8$h2@1$e^4Ni0>0@3$3@1$a@2$4$0@1$1$2@2$h1^5^4@2$7@2$4$0@1$1$2@4$b$0@1$1$2^3^2@2$5@2$h3^6^4@2$5@3$3$h0@1$6^4@1$6^6@2$h4@1$f@1$d^4^5").
Proof.
  intros st qmin stR evR L H. rewrite quarantine_recycle_rsplit in H.
  destruct (rsplit (as_gq st) qmin) as [[[g2 ex] rp]|] eqn:RS; [| discriminate H].
  destruct (do_recycle (set_gq st g2) (ex ++ rev rp) []) as [[st2 racc]|] eqn:DR; [| discriminate H]. injection H as <- _.
  assert (L1 : length (as_regions (set_gq st g2)) = 32%nat) by exact L.
  pose proof (do_recycle_qq _ _ _ _ _ L1 DR) as (Q1 & Q2 & _).
  pose proof (do_recycle_csub _ _ _ _ _ L1 DR) as CS.
  split; [intros ch Hch; exact (CS ch Hch)|]. split; [rewrite Q1; reflexivity|].
  rewrite Q2. cbn [as_gq set_gq]. destruct g2 as [l2 b2]. cbn [qc_bytes]. exact (rsplit_le _ _ _ _ _ _ RS).
Qed.
