(* fuzz_preset, program walks (slice S7a, a Theorem Labs lane; the ONE copy, imported by S7b's writer walks): the capacity
   chain of a run of puts. Pure lemmas over the writer model (prhWriter_putN, WriterSpec.newcap); no machine state.
   - prhWriter_putN_len_le: a run appends at most its pieces' bytes to the text.
   - prhWriter_newcap_step: the capacity the rest P2 of a run asks from the state after P1 is at most what the whole run
     P1 ++ P2 asks from the first state (the capacities of a run stay in one doubling chain from the entry capacity).
   The batch kit's e45217a4c7ba removed the kit's entry sums prhWriter_live / LIVE_<fn> (PRH_FnWriter.v's note above
   prhWriter_out: a per-event live room prh_live_evs replaces them), so this file's prhWriter_live_mono /
   prhWriter_live_arith are gone; the live room now composes in S7a_WriterRet.v (prhWriter_live_evs_at).
   Numerals: 4096, 51, 2 ^ 28 (LENGTH: the model's capacity grid and WMAX, PRH_FnWriter.v / prhWriter_out). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec WriterApp WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YI5b.
#[global] Remove Hints YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Local Open Scope Z_scope.

(* the writer's capacity grid (prhWriter_out's cap clause) *)
Definition prhWriter_capgrid (c : Z) : Prop := c = 0 \/ exists j, 0 <= j <= 51 /\ c = 4096 * 2 ^ j.

(* ---- newcap over one doubling chain: newcap c y = dbl 64 (prhWL_base c) y ---- *)
Definition prhWL_base (c : Z) : Z := if c =? 0 then 4096 else c.

Lemma prhWL_newcap_eq : forall c y, WriterSpec.newcap c y = WriterSpec.dbl 64%nat (prhWL_base c) y.
Proof. reflexivity. Qed.

Lemma prhWL_base_id : forall c, 0 < c -> prhWL_base c = c.
Proof. intros c Hc. unfold prhWL_base. destruct (Z.eqb_spec c 0); cbv iota; lia. Qed.

Lemma prhWL_capgrid_base : forall c, prhWriter_capgrid c -> 4096 <= prhWL_base c.
Proof.
  intros c Hg. unfold prhWL_base. destruct (Z.eqb_spec c 0) as [_|Hn]; cbv iota; [lia|].
  destruct Hg as [Hc|[j [Hj Hc]]]; [lia|].
  pose proof (Z.pow_pos_nonneg 2 j ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma prhWL_pos_of_mul : forall a n, 0 < a * 2 ^ Z.of_nat n -> 0 < a.
Proof. intros a n H. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat n) ltac:(lia) ltac:(lia)). nia. Qed.

Lemma prhWL_le_mul_pow : forall a n, 0 <= a -> a <= a * 2 ^ Z.of_nat n.
Proof. intros a n H. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat n) ltac:(lia) ltac:(lia)). nia. Qed.

Lemma prhWL_dbl_O : forall c y, WriterSpec.dbl O c y = c.
Proof. reflexivity. Qed.

Lemma prhWL_dbl_S_le : forall f c y, y <= c -> WriterSpec.dbl (S f) c y = c.
Proof. intros f c y H. cbn [WriterSpec.dbl]. destruct (Z.leb_spec y c); [reflexivity | lia]. Qed.

Lemma prhWL_dbl_S_gt : forall f c y, c < y -> WriterSpec.dbl (S f) c y = WriterSpec.dbl f (2 * c) y.
Proof. intros f c y H. cbn [WriterSpec.dbl]. destruct (Z.leb_spec y c); [lia | reflexivity]. Qed.

(* dbl never goes below its start *)
Lemma prhWL_dbl_ge_c : forall f c y, 0 <= c -> c <= WriterSpec.dbl f c y.
Proof.
  induction f as [|f IH]; intros c y Hc; [rewrite prhWL_dbl_O; lia|].
  destruct (Z.le_gt_cases y c).
  - rewrite prhWL_dbl_S_le by lia. lia.
  - rewrite prhWL_dbl_S_gt by lia. specialize (IH (2 * c) y ltac:(lia)). lia.
Qed.

(* dbl is monotone in the need *)
Lemma prhWL_dbl_mono : forall f c y1 y2, 0 <= c -> y1 <= y2 ->
  WriterSpec.dbl f c y1 <= WriterSpec.dbl f c y2.
Proof.
  induction f as [|f IH]; intros c y1 y2 Hc Hy; [rewrite (prhWL_dbl_O c y1), (prhWL_dbl_O c y2); lia|].
  destruct (Z.le_gt_cases y1 c), (Z.le_gt_cases y2 c).
  - rewrite (prhWL_dbl_S_le f c y1), (prhWL_dbl_S_le f c y2) by lia. lia.
  - rewrite prhWL_dbl_S_le, prhWL_dbl_S_gt by lia.
    pose proof (prhWL_dbl_ge_c f (2 * c) y2 ltac:(lia)). lia.
  - lia.
  - rewrite (prhWL_dbl_S_gt f c y1), (prhWL_dbl_S_gt f c y2) by lia. apply IH; lia.
Qed.

(* newcap is monotone in the need; stated on newcap and closed by conversion, so no caller rewrites with
   prhWL_newcap_eq under `!` *)
Lemma prhWL_newcap_mono : forall c y1 y2, 0 <= prhWL_base c -> y1 <= y2 ->
  WriterSpec.newcap c y1 <= WriterSpec.newcap c y2.
Proof. intros c y1 y2 Hc Hy. exact (prhWL_dbl_mono 64 (prhWL_base c) y1 y2 Hc Hy). Qed.

(* with enough fuel dbl reaches the need *)
Lemma prhWL_dbl_ge_y : forall f c y, 0 < c -> y <= c * 2 ^ Z.of_nat f -> y <= WriterSpec.dbl f c y.
Proof.
  induction f as [|f IH]; intros c y Hc Hy.
  - rewrite prhWL_dbl_O. simpl in Hy. lia.
  - destruct (Z.le_gt_cases y c).
    + rewrite prhWL_dbl_S_le by lia. lia.
    + rewrite prhWL_dbl_S_gt by lia. apply IH; [lia|].
      rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hy by lia.
      replace (2 * c * 2 ^ Z.of_nat f) with (c * (2 * 2 ^ Z.of_nat f)) by ring. exact Hy.
Qed.

(* dbl stays in the doubling chain of its start *)
Lemma prhWL_dbl_pow : forall f c y, exists k : nat, WriterSpec.dbl f c y = c * 2 ^ Z.of_nat k.
Proof.
  induction f as [|f IH]; intros c y.
  - exists O. rewrite prhWL_dbl_O. simpl. lia.
  - destruct (Z.le_gt_cases y c).
    + exists O. rewrite prhWL_dbl_S_le by lia. simpl. lia.
    + rewrite prhWL_dbl_S_gt by lia. destruct (IH (2 * c) y) as [k Hk]. exists (S k).
      rewrite Hk, Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

(* a chain element at or above the need is a doubling of dbl's result *)
Lemma prhWL_dbl_div : forall f m c y, 0 < c -> y <= c * 2 ^ Z.of_nat m ->
  exists m' : nat, c * 2 ^ Z.of_nat m = WriterSpec.dbl f c y * 2 ^ Z.of_nat m'.
Proof.
  induction f as [|f IH]; intros m c y Hc Hy.
  - exists m. rewrite prhWL_dbl_O. reflexivity.
  - destruct (Z.le_gt_cases y c).
    + exists m. rewrite prhWL_dbl_S_le by lia. reflexivity.
    + rewrite prhWL_dbl_S_gt by lia. destruct m as [|m].
      * simpl in Hy. lia.
      * rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hy by lia.
        assert (Hy2 : y <= 2 * c * 2 ^ Z.of_nat m)
          by (replace (2 * c * 2 ^ Z.of_nat m) with (c * (2 * 2 ^ Z.of_nat m)) by ring; exact Hy).
        destruct (IH m (2 * c) y ltac:(lia) Hy2) as [m' Hm'].
        exists m'. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. rewrite <- Hm'. ring.
Qed.

(* ---- a run's first put ---- *)
Lemma prhWL_putN_g : forall ok st b P, prhWriter_grows st b = true ->
  prhWriter_putN ok st (b :: P) = prhWriter_putN (tl ok) (prhWriter_put1 (hd true ok) st b) P.
Proof. intros ok st b P E. cbn [prhWriter_putN]. rewrite E. reflexivity. Qed.

Lemma prhWL_putN_ng : forall ok st b P, prhWriter_grows st b = false ->
  prhWriter_putN ok st (b :: P) = prhWriter_putN ok (WriterApp.put1 st b) P.
Proof. intros ok st b P E. cbn [prhWriter_putN]. rewrite E. reflexivity. Qed.

(* ---- one put of a run: the text is kept or extended by b; the capacity is kept or grown to newcap ---- *)
Definition prhWL_step (st st' : WriterApp.wst) (b : list Z) : Prop :=
  (WriterApp.w_text st' = WriterApp.w_text st \/ WriterApp.w_text st' = WriterApp.w_text st ++ b) /\
  (WriterApp.w_cap st' = WriterApp.w_cap st \/
   WriterApp.w_cap st' = WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st b)).

Ltac prhWL_stepfin := split; first [left; reflexivity | right; reflexivity].

Lemma prhWL_put1_step : forall st b, prhWL_step st (WriterApp.put1 st b) b.
Proof.
  intros st b. unfold prhWL_step, WriterApp.put1, prhWriter_need. cbv zeta.
  destruct (WriterApp.w_failed st =? 0); [|prhWL_stepfin].
  destruct (Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length b) + 1 <=? WriterApp.w_cap st);
    [prhWL_stepfin|].
  destruct (WriterApp.w_cnt st =? WriterApp.w_fail st); prhWL_stepfin.
Qed.

Lemma prhWL_hput1_step : forall okb st b, prhWL_step st (prhWriter_put1 okb st b) b.
Proof.
  intros okb st b. unfold prhWriter_put1.
  destruct (prhWriter_grows st b); [|apply prhWL_put1_step].
  unfold prhWL_step. cbv zeta.
  destruct (WriterApp.w_cnt st =? WriterApp.w_fail st); [prhWL_stepfin|].
  destruct okb; prhWL_stepfin.
Qed.

Lemma prhWL_step_len : forall st st' b, prhWL_step st st' b ->
  (length (WriterApp.w_text st') <= length (WriterApp.w_text st) + length b)%nat.
Proof. intros st st' b [[Ht|Ht] _]; rewrite Ht; [|rewrite length_app]; lia. Qed.

Lemma prhWriter_putN_len_le : forall ok st P,
  (length (WriterApp.w_text (prhWriter_putN ok st P)) <= length (WriterApp.w_text st) + length (concat P))%nat.
Proof.
  intros ok st P. revert ok st.
  induction P as [|b P IH]; intros ok st; [cbn [prhWriter_putN concat]; lia|].
  cbn [concat]. rewrite length_app.
  destruct (prhWriter_grows st b) eqn:E.
  - rewrite (prhWL_putN_g ok st b P E). pose proof (IH (tl ok) (prhWriter_put1 (hd true ok) st b)).
    pose proof (prhWL_step_len _ _ _ (prhWL_hput1_step (hd true ok) st b)). lia.
  - rewrite (prhWL_putN_ng ok st b P E). pose proof (IH ok (WriterApp.put1 st b)).
    pose proof (prhWL_step_len _ _ _ (prhWL_put1_step st b)). lia.
Qed.

(* ---- the chain invariant along a run: R is a doubling of the current base, and the text plus the rest fits R ---- *)
Lemma prhWL_chain_step : forall R K st st' b Q, 0 < R -> 1 <= K ->
  (exists m : nat, R = prhWL_base (WriterApp.w_cap st) * 2 ^ Z.of_nat m) /\
    Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length (concat (b :: Q))) + K <= R ->
  prhWL_step st st' b ->
  (exists m : nat, R = prhWL_base (WriterApp.w_cap st') * 2 ^ Z.of_nat m) /\
    Z.of_nat (length (WriterApp.w_text st')) + Z.of_nat (length (concat Q)) + K <= R.
Proof.
  intros R K st st' b Q HR HK [[m Hm] Hl] [Ht Hc].
  cbn [concat] in Hl. rewrite length_app in Hl.
  split.
  - destruct Hc as [Hc|Hc]; rewrite Hc; [exists m; exact Hm|].
    rewrite prhWL_newcap_eq.
    assert (Hb : 0 < prhWL_base (WriterApp.w_cap st)) by (apply (prhWL_pos_of_mul _ m); rewrite <- Hm; exact HR).
    assert (Hn : prhWriter_need st b <= prhWL_base (WriterApp.w_cap st) * 2 ^ Z.of_nat m)
      by (rewrite <- Hm; unfold prhWriter_need; lia).
    destruct (prhWL_dbl_div 64 m _ _ Hb Hn) as [m' Hm'].
    pose proof (prhWL_dbl_ge_c 64 (prhWL_base (WriterApp.w_cap st)) (prhWriter_need st b) ltac:(lia)).
    rewrite (prhWL_base_id (WriterSpec.dbl 64 (prhWL_base (WriterApp.w_cap st)) (prhWriter_need st b))) by lia.
    exists m'. rewrite Hm. exact Hm'.
  - destruct Ht as [Ht|Ht]; rewrite Ht.
    + lia.
    + rewrite length_app. lia.
Qed.

Lemma prhWL_chain_run : forall R K ok P st, 0 < R -> 1 <= K ->
  (exists m : nat, R = prhWL_base (WriterApp.w_cap st) * 2 ^ Z.of_nat m) /\
    Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length (concat P)) + K <= R ->
  (exists m : nat, R = prhWL_base (WriterApp.w_cap (prhWriter_putN ok st P)) * 2 ^ Z.of_nat m) /\
    Z.of_nat (length (WriterApp.w_text (prhWriter_putN ok st P))) + K <= R.
Proof.
  intros R K ok P. revert ok.
  induction P as [|b P IH]; intros ok st HR HK H.
  - cbn [prhWriter_putN]. destruct H as [Hm Hl]. split; [exact Hm|]. cbn [concat length] in Hl. lia.
  - destruct (prhWriter_grows st b) eqn:E;
      [rewrite (prhWL_putN_g ok st b P E) | rewrite (prhWL_putN_ng ok st b P E)]; apply IH; try assumption.
    + exact (prhWL_chain_step R K st _ b P HR HK H (prhWL_hput1_step _ st b)).
    + exact (prhWL_chain_step R K st _ b P HR HK H (prhWL_put1_step st b)).
Qed.

Lemma prhWriter_newcap_step : forall ok st P1 P2,
  prhWriter_capgrid (WriterApp.w_cap st) ->
  Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length (concat (P1 ++ P2))) + 1 <= prhWriter_WMAX ->
  WriterSpec.newcap (WriterApp.w_cap (prhWriter_putN ok st P1))
    (Z.of_nat (length (WriterApp.w_text (prhWriter_putN ok st P1))) + Z.of_nat (length (concat P2)) + 1)
  <= WriterSpec.newcap (WriterApp.w_cap st)
       (Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length (concat (P1 ++ P2))) + 1).
Proof.
  intros ok st P1 P2 Hg HW.
  pose proof (prhWL_capgrid_base _ Hg) as Hb.
  rewrite (prhWL_newcap_eq (WriterApp.w_cap st)).
  set (y := Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length (concat (P1 ++ P2))) + 1) in *.
  assert (Hy : y = Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length (concat P1))
                   + Z.of_nat (length (concat P2)) + 1)
    by (unfold y; rewrite concat_app, length_app; lia).
  clearbody y.
  assert (HyN : y <= prhWL_base (WriterApp.w_cap st) * 2 ^ Z.of_nat 64).
  { change (2 ^ Z.of_nat 64) with 18446744073709551616. change prhWriter_WMAX with 268435456 in HW. lia. }
  assert (Hbpos : 0 < prhWL_base (WriterApp.w_cap st)) by lia.
  pose proof (prhWL_dbl_ge_y 64 _ y Hbpos HyN) as HRy.
  destruct (prhWL_dbl_pow 64 (prhWL_base (WriterApp.w_cap st)) y) as [k Hk].
  set (R := WriterSpec.dbl 64 (prhWL_base (WriterApp.w_cap st)) y) in *.
  clearbody R.
  assert (HR0 : 0 < R) by lia.
  assert (HK : 1 <= Z.of_nat (length (concat P2)) + 1) by lia.
  assert (Hin : (exists m : nat, R = prhWL_base (WriterApp.w_cap st) * 2 ^ Z.of_nat m) /\
    Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length (concat P1))
      + (Z.of_nat (length (concat P2)) + 1) <= R)
    by (split; [exists k; exact Hk | lia]).
  destruct (prhWL_chain_run R _ ok P1 st HR0 HK Hin) as [[m Hm] Hl].
  set (st1 := prhWriter_putN ok st P1) in *.
  set (y1 := Z.of_nat (length (WriterApp.w_text st1)) + Z.of_nat (length (concat P2)) + 1).
  rewrite prhWL_newcap_eq.
  assert (Hb1 : 0 < prhWL_base (WriterApp.w_cap st1))
    by (apply (prhWL_pos_of_mul _ m); rewrite <- Hm; exact HR0).
  assert (Hy1 : y1 <= prhWL_base (WriterApp.w_cap st1) * 2 ^ Z.of_nat m) by (rewrite <- Hm; unfold y1; lia).
  destruct (prhWL_dbl_div 64 m _ _ Hb1 Hy1) as [m' Hm'].
  pose proof (prhWL_dbl_ge_c 64 (prhWL_base (WriterApp.w_cap st1)) y1 ltac:(lia)) as Hd.
  pose proof (prhWL_le_mul_pow (WriterSpec.dbl 64 (prhWL_base (WriterApp.w_cap st1)) y1) m' ltac:(lia)).
  rewrite <- Hm in Hm'. lia.
Qed.
