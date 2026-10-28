From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import HufPure_FseDecomp HufPure_FseDecompRT HufPure_HufStats HufPure_HufStatsRT.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import HufPure_FseReadBridge ZdHufStats.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma all_bytes_of_Forall (src : list Z) :
  Forall (fun c => 0 <= c < 256) src -> all_bytes src.
Proof.
  intros HF i. unfold Znth.
  destruct (nth_in_or_default (Z.to_nat i) src 0) as [I|D].
  - rewrite Forall_forall in HF. apply HF. exact I.
  - rewrite D. lia.
Qed.

Lemma ksum_hw_total (l : list Z) : ksum l = hw_total l.
Proof.
  induction l as [|w t IH]; cbn [ksum hw_total]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma stats_ok_huf_stats_ok (h : hstats) :
  stats_ok h ->
  huf_stats_ok (hs_weights h) (hs_rank h) (hs_tableLog h) /\ Z.of_nat (length (hs_weights h)) = hs_nbSymbols h.
Proof.
  intros (TL & LEN & NB & FA & RL & RK & KS).
  unfold HUF_TABLELOG_MAX, HUF_SYMBOLVALUE_MAX in *.
  split.
  - unfold huf_stats_ok. split; [lia|]. split; [lia|]. split; [exact FA|].
    split; [lia|]. split.
    + intros w Hw. unfold hcount. apply RK. exact Hw.
    + rewrite <- ksum_hw_total. exact KS.
  - rewrite <- LEN. reflexivity.
Qed.

Lemma read_stats_okB : forall (src : list Z) (h : hstats),
  Forall (fun c => 0 <= c < 256) src -> read_stats src = Ok h ->
  huf_stats_ok (hs_weights h) (hs_rank h) (hs_tableLog h) /\ Z.of_nat (length (hs_weights h)) = hs_nbSymbols h.
Proof.
  intros src h HF HR.
  destruct (read_stats_safe src read_ncount_safe (all_bytes_of_Forall src HF)) as [[h' [E S]] | [e E]];
    rewrite HR in E; [|discriminate E].
  injection E as <-. apply stats_ok_huf_stats_ok. exact S.
Qed.
