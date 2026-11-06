From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import check_reject_clean_starved_c CrsRoom PjWriteHyp check_round_trip_c check_round_trip_m EntryDefs EntrySR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Definition esq_wl1 : Prop :=
  forall (x : list Z) (t : jv), json_read jr_strtod x = Some t -> Z.of_nat (length x) <= 3 * 2 ^ 20 ->
    wlen t false <= 3 * Z.of_nat (length x).

Definition esq_wl2 : Prop :=
  forall (x : list Z) (t : jv), json_read jr_strtod x = Some t -> Z.of_nat (length x) <= 3 * 2 ^ 20 ->
    wlen t true <= 56 * Z.of_nat (length x) - 54.

Definition esq_esz : Prop :=
  forall (x : list Z) (t : jv), json_read jr_strtod x = Some t -> Z.of_nat (length x) <= 3 * 2 ^ 20 ->
    forall e, In e (PjRoundTrip.ttrace t) \/ In e (PjRoundTrip.ttrace (crt_tree t)) -> is_call e = true ->
      Z.of_nat (esize e) + 16 <= 2 ^ 27.

Lemma esq_zb_len : forall pl, Z.of_nat (length (zb pl)) = ent_n pl.
Proof. intros pl. unfold zb, ent_n. rewrite length_map. reflexivity. Qed.

Lemma esq_took : forall pl, 0 <= ent_took pl <= 2 * ent_n pl + 2.
Proof.
  intros pl. unfold ent_took, ncalls. pose proof (G7_4 jr_strtod (zb pl) []) as H.
  pose proof (esq_zb_len pl) as E. lia.
Qed.

Lemma esq_c3 : forall cnt0 pl (j : nat), 0 <= cnt0 <= Z.of_nat j * 2 ^ 60 -> (j < 4)%nat -> ent_n pl <= 0x300000 ->
  0 <= ent_c3 cnt0 pl < 2 ^ 62 - 2 ^ 30.
Proof. intros cnt0 pl j Hc Hj Hn. pose proof (esq_took pl). unfold ent_c3. lia. Qed.

Lemma esq_wcalls : forall t p, wlen t p + 1 <= 2 ^ 62 -> 0 <= CF.PjWriteHyp.wcalls t p <= wlen t p + 1.
Proof.
  intros t p H. unfold CF.PjWriteHyp.wcalls, wlen, wdoc in *. split; [lia|]. exact (crs_wcalls_le (wdpieces t p) H).
Qed.

Lemma esq_wN : forall t p, wN t p = CF.PjWriteHyp.wcalls t p.
Proof. reflexivity. Qed.

Lemma esq_tcalls : forall t p, PjRoundTrip.pj_wf jr_strtod t -> Z.of_nat (PjRoundTrip.tcalls t) <= 2 * wlen t p + 2.
Proof.
  intros t p H. rewrite <- (PjRoundTrip.G9_calls jr_strtod t H p). unfold ncalls, wlen.
  pose proof (G7_4 jr_strtod (wdoc t p) []) as G. lia.
Qed.

Lemma esq_pick : forall x n, 0 <= n -> 0 <= pick x n <= n.
Proof.
  intros x n H. unfold pick. destruct (Z.eqb_spec n 0) as [E|E]; [lia|].
  pose proof (Z.mod_pos_bound (djb2 5381 x) n ltac:(lia)). lia.
Qed.

Section C.
Hypothesis HWL1 : esq_wl1.
Hypothesis HWL2 : esq_wl2.

Lemma esq_wlen : forall pl t, json_read jr_strtod (zb pl) = Some t -> ent_n pl <= 0x300000 ->
  0 <= wlen t false <= 3 * ent_n pl /\ 0 <= wlen t true <= 56 * ent_n pl - 54 /\
  0 <= wlen (crt_tree t) true <= 56 * ent_n pl - 14.
Proof.
  intros pl t HJ HN. pose proof (esq_zb_len pl) as E.
  pose proof (HWL1 (zb pl) t HJ ltac:(lia)) as W1. pose proof (HWL2 (zb pl) t HJ ltac:(lia)) as W2.
  pose proof (crt_len t) as W3. unfold wlen in *. lia.
Qed.

Lemma esq_wdoc : forall pl t, json_read jr_strtod (zb pl) = Some t -> ent_n pl <= 0x300000 ->
  Z.of_nat (length (wdoc t false)) + 1 < 2 ^ 24 /\ Z.of_nat (length (wdoc t true)) + 1 < 2 ^ 28.
Proof.
  intros pl t HJ HN. pose proof (esq_wlen pl t HJ HN) as (W1 & W2 & _). unfold wlen in *. lia.
Qed.

Lemma esq_cc : forall pl t cset, json_read jr_strtod (zb pl) = Some t -> ent_n pl <= 0x300000 -> 0 <= cset <= 3 ->
  0 <= crt_count t cset <= 2 ^ 30.
Proof.
  intros pl t cset HJ HN HC. pose proof (esq_wlen pl t HJ HN) as (W1 & W2 & W3).
  pose proof (PjRoundTrip.wf_read jr_strtod (zb pl) t HJ) as WF.
  pose proof (crt_wf (zb pl) t HJ) as WF'.
  pose proof (esq_tcalls t false WF) as T1.
  pose proof (esq_tcalls (crt_tree t) true WF') as T2.
  pose proof (esq_wcalls t false ltac:(lia)) as C1.
  pose proof (esq_wcalls t true ltac:(lia)) as C2.
  pose proof (esq_wcalls (crt_tree t) true ltac:(lia)) as C3.
  unfold crt_count. destruct t; lia.
Qed.

Lemma esq_gr : forall pl t, json_read jr_strtod (zb pl) = Some t -> ent_n pl <= 0x300000 ->
  0 <= crcs_growth (zb pl) (ent_took pl) 1 t <= 2 ^ 30.
Proof.
  intros pl t HJ HN. pose proof (esq_wlen pl t HJ HN) as (W1 & W2 & _). pose proof (esq_took pl) as HT.
  pose proof (esq_wcalls t false ltac:(lia)) as C1. pose proof (esq_wcalls t true ltac:(lia)) as C2.
  rewrite <- esq_wN in C1, C2.
  pose proof (esq_pick (zb pl) (ent_took pl) ltac:(lia)) as P0.
  pose proof (esq_pick (zb pl) (wN t true) ltac:(lia)) as P1.
  pose proof (esq_pick (zb pl) (wN t false) ltac:(lia)) as P2.
  unfold crcs_growth. change (1 =? 0) with false. cbv iota.
  destruct (ent_took pl =? 0); lia.
Qed.

Lemma esq_cnt : forall cnt0 pl t cset (j : nat), 0 <= cnt0 <= Z.of_nat j * 2 ^ 60 -> (j < 4)%nat ->
  json_read jr_strtod (zb pl) = Some t -> ent_n pl <= 0x300000 -> 0 <= cset <= 3 ->
  0 <= ent_c4 cnt0 pl t cset < 2 ^ 62 - 2 ^ 30 /\
  ent_c4 cnt0 pl t cset + crcs_growth (zb pl) (ent_took pl) 1 t <= Z.of_nat (S j) * 2 ^ 60.
Proof.
  intros cnt0 pl t cset j Hc Hj HJ HN HC.
  pose proof (esq_c3 cnt0 pl j Hc Hj HN) as H3. pose proof (esq_took pl) as HT.
  pose proof (esq_cc pl t cset HJ HN HC) as H4. pose proof (esq_gr pl t HJ HN) as H5.
  unfold ent_c4, ent_c3 in *. lia.
Qed.

End C.
