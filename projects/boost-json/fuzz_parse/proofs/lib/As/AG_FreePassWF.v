(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From Stdlib Require Import FMapPositive.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel AsanAllocCons.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import AllocWf AllocKit AG_MallocModel AG_WFHit AG_FreeModel AG_WFFree AG_RepQ AG_FreePassModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc3nil69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~ja5chunkhc4cons37Corelib4Init5Logicoa2eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Ash0AG_FreePassModel~~~~~~q37flip_st79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AG_RepQ~~~~~~v43WFQ79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AllocWf~~~~~~hj72WFjaaCAllocatedja6astatejacch_chunk_begja8ch_statejaachunk_listja6cstate36Stdlib5Lists4Lisths02In" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Flip.
  Variables (st : astate) (ch : chunk).
  Let U := ch_user_beg ch.
  Let m := ch_chunk_beg ch.
  Let st1 := upd_chunk st (qch ch).
  Hypothesis W : ltac2:(zQ "10!hn4@1$0?2st").
  Hypothesis IN : ltac2:(zQ "30!nb!hqa!ht3@3$2$0?2ch@1$1?2st").
  Hypothesis ALLOC : ltac2:(zQ "40!pe!hna!hpf!hr7@3$0$3@1$2?2ch$1").

  Let KEYS : keys_ok (as_chunks st). Proof. apply WF_keys. exact W. Qed.
  Let UPOS : 0 < U. Proof. exact (proj2 (KEYS _ _ (proj1 (chunk_list_find st ch KEYS) IN))). Qed.
  Let MU : m + kChunkHeaderSize = U. Proof. subst m U. unfold ch_chunk_beg. lia. Qed.
  Let PERM0 : Permutation (chunk_list st) (ch :: others st ch). Proof. exact (free_chunks_perm0 st ch W IN). Qed.
  Let PERM1 : Permutation (chunk_list st1) (qch ch :: others st ch). Proof. exact (free_chunks_perm1 st ch W IN). Qed.
  Let IN1 : forall y, In y (chunk_list st1) <-> y = qch ch \/ (In y (chunk_list st) /\ ch_user_beg y <> U).
  Proof. exact (free_chunks_in st ch W IN). Qed.
  Let F1same : find_chunk (as_chunks st1) U = Some (qch ch). Proof. exact (free_find_same st ch W IN). Qed.
  Let FCB : forall b q, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> In q (qb_chunks b) ->
    find_chunk (as_chunks st1) (q + kChunkHeaderSize) = find_chunk (as_chunks st) (q + kChunkHeaderSize).
  Proof. intros b q Hb Hq. apply (free_find_other st ch W IN). exact (free_oldq st ch W IN ALLOC b q Hb Hq). Qed.
  Let MNEW : ~ In m (flat_map qb_chunks (qc_list (as_tq st) ++ qc_list (as_gq st))).
  Proof. intros H. apply in_flat_map in H as [b [Hb Hq]]. exact (free_oldq st ch W IN ALLOC b m Hb Hq MU). Qed.

  Theorem WFQ_flip : WFQ st1 [m] [].
  Proof.
    pose proof W as WW.
    ndestruct WW as (Wrc & Wnd & Wch & Winj & Wsec & Wsnd & Wres1 & Wres2 & Wtq & Wgq & Wtqb & Wgqb & Wndb & Wq & Wm0 & Wm31 & Wpc0 & Wpc31 & WlenR & WlenC & Wqmax & Wqmin & Wqc & Wkeys).
    unfold WFQ. rewrite !app_nil_r.
    change (as_sec st1) with (as_sec st). change (as_n_reserved st1) with (as_n_reserved st).
    change (as_gq st1) with (as_gq st). change (as_tq st1) with (as_tq st). change (as_qcache st1) with (as_qcache st).
    change (as_qmax st1) with (as_qmax st). change (as_qmin st1) with (as_qmin st).
    change (as_regions st1) with (as_regions st). change (as_cache st1) with (as_cache st).
    split. { intros c Hc. destruct (Wrc c Hc) as [R0 C0]. split; [destruct R0; constructor; assumption| destruct C0; constructor; assumption]. }
    split. { (* [comment removed for export] *)
      apply (Permutation_NoDup (l := carved_addr_list st)); [| exact Wnd]. apply Permutation_sym. unfold carved_addr_list.
      apply Permutation_app; [apply Permutation_refl|]. apply Permutation_app; [| apply Permutation_refl].
      eapply Permutation_trans; [apply Permutation_map; apply Permutation_filter; exact PERM1|].
      eapply Permutation_trans; [| apply Permutation_map; apply Permutation_filter; apply Permutation_sym; exact PERM0].
      cbn [filter]. change (ch_primary (qch ch)) with (ch_primary ch). destruct (ch_primary ch); cbn [map]; apply Permutation_refl. }
    split. { intros y Hy. apply IN1 in Hy as [->|[Hy _]].
      - apply chunk_ok_qch. apply (chunk_ok_geom st st1); try reflexivity. exact (Wch ch IN).
      - apply (chunk_ok_geom st st1); try reflexivity. exact (Wch y Hy). }
    split. { intros a b Ha Hb E. apply IN1 in Ha as [->|[Ha NA]]; apply IN1 in Hb as [->|[Hb NB]]; [reflexivity| exfalso; apply NB; rewrite <- E; reflexivity| exfalso; apply NA; exact E| exact (Winj a b Ha Hb E)]. }
    split. { unfold zlen in *. rewrite (Permutation_length (Permutation_filter _ _ _ PERM1)), <- Wsec, (Permutation_length (Permutation_filter _ _ _ PERM0)).
             cbn [filter]. change (ch_primary (qch ch)) with (ch_primary ch). destruct (ch_primary ch); reflexivity. }
    split; [exact Wsnd|]. split; [exact Wres1|]. split; [exact Wres2|].
    split. { split; [| exact (proj2 Wtq)]. intros b Hb. apply (batch_ok_old st ch W IN ALLOC st1); try reflexivity; [apply in_app_iff; left; exact Hb| exact (proj1 Wtq b Hb)]. }
    split. { split; [| exact (proj2 Wgq)]. intros b Hb. apply (batch_ok_old st ch W IN ALLOC st1); try reflexivity; [apply in_app_iff; right; exact Hb| exact (proj1 Wgq b Hb)]. }
    split. { (* [comment removed for export] *)
      apply (Permutation_NoDup (l := m :: flat_map qb_chunks (qc_list (as_tq st) ++ qc_list (as_gq st)))); [| constructor; [exact MNEW| exact Wndb]].
      first [apply Permutation_cons_append | apply Permutation_sym; apply Permutation_cons_append]. }
    split. { intros y Hy Q. apply IN1 in Hy as [->|[Hy NE]].
      - right. left. reflexivity.
      - destruct (Wq y Hy Q) as [b [Hb Hq]]. left. exists b. split; [exact Hb| exact Hq]. }
    split; [exact Wm0|]. split; [exact Wm31|]. split; [exact Wpc0|]. split; [exact Wpc31|]. split; [exact WlenR|]. split; [exact WlenC|].
    split; [exact Wqmax|]. split; [exact Wqmin|]. split; [exact Wqc|].
    split; [apply keys_ok_upd; [exact KEYS| exact UPOS]|].
    split.
    - (* [comment removed for export] *)
      intros q [<-|[]]. exists (qch ch). rewrite MU. split; [exact F1same| reflexivity].
    - intros B0 [].
  Qed.
End Flip.

(* [comment removed for export] *)
Theorem WFQ_flip_st : ltac2:(zQ "f0!h9!j4!nb!o3!pe!ua!hj1!hn4!hna!ho7!hp0!hpf!hqa!hr7!ht3>2st$9>2ch$2>0@1$7^2>0@3$e$2^2@1$c^3>0@3$4$d@1$b^3$8@3$6@2$5^5^4@3$3$0@1$a^4@1$1$0@1$1$0").
Proof.
  intros st ch W IN AL. unfold flip_st.
  assert (W0 : WF (set_internal_init st)) by (eapply WF_ext; [ .. | exact W]; reflexivity).
  apply (WFQ_flip (set_internal_init st) ch W0); [exact IN| exact AL].
Qed.
