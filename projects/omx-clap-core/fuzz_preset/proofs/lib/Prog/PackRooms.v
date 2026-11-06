From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract Img0 FrameAPI SlotPack AllocPack AllocPackRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar PjGrowUp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import Ledger PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterApp WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterRet.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import
pj_parse_c check_no_overread_c check_reject_clean_starved_c round_trip_text_c check_round_trip_c EntryDefs
LLVMFuzzerTestOneInput_c EntrySR TxCalls TxModel pj_set_c PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PackFit PackOwn PackReparse PackVec PackBand PackBig.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require SlotSizes PackFold PackTraceT PackTraceR.

Lemma room_run_of (F : ResForm) : forall tr b,
  (forall P e R, tr = P ++ e :: R -> is_call e = true ->
     rf_room F (rf_run F b P) (Z.of_nat (esize e) + 16) /\ Z.of_nat (esize e) + 16 <= 2 ^ 28) ->
  room_run F b tr.
Proof.
  induction tr as [|e r IH]; intros b H; cbn [room_run]; [exact I|]. split.
  - intros Hc. exact (H [] e r eq_refl Hc).
  - apply IH. intros P e' R E Hc. exact (H (e :: P) e' R ltac:(rewrite E; reflexivity) Hc).
Qed.

Lemma wr_rooms_of (F : ResForm) : forall P b st,
  (forall Q bs R, P = Q ++ bs :: R -> w_failed (putN st Q) = 0 ->
     w_cap (putN st Q) < Z.of_nat (length (w_text (putN st Q))) + Z.of_nat (length bs) + 1 ->
     rf_room F (WriterRet.wfold F b st Q)
       (newcap (w_cap (putN st Q)) (Z.of_nat (length (w_text (putN st Q))) + Z.of_nat (length bs) + 1) + 16)) ->
  WriterRet.wr_rooms F b st P.
Proof.
  induction P as [|bs P IH]; intros b st H; cbn [WriterRet.wr_rooms]; [exact I|]. split.
  - intros Hf Hc. exact (H [] bs P eq_refl Hf Hc).
  - apply IH. intros Q bs' R E Hf Hc. exact (H (bs :: Q) bs' R ltac:(rewrite E; reflexivity) Hf Hc).
Qed.

Lemma tx_rooms_of (F : ResForm) : forall ns b len cap,
  (forall Q m R, ns = Q ++ m :: R -> tx_capf len cap Q < len + zsum Q + m + 1 ->
     rf_room F (tx_fold F b len cap Q) (2 * (len + zsum Q + m + 1))) ->
  tx_rooms F b len cap ns.
Proof.
  induction ns as [|m ns IH]; intros b len cap H; cbn [tx_rooms]; [exact I|]. split.
  - intros Hc. pose proof (H [] m ns eq_refl) as H0. cbn [tx_capf zsum tx_fold] in H0.
    rewrite Z.add_0_r in H0. exact (H0 Hc).
  - apply IH. intros Q m' R E Hc. pose proof (H (m :: Q) m' R ltac:(rewrite E; reflexivity)) as H1.
    cbn [tx_capf zsum tx_fold] in H1.
    replace (len + (m + zsum Q) + m' + 1) with (len + m + zsum Q + m' + 1) in H1 by lia. exact (H1 Hc).
Qed.

Lemma pq_bi_01 : forall k n, 0 <= pq_bi k n <= 1.
Proof. intros k n. unfold pq_bi. destruct (band n =? k); lia. Qed.

Lemma pq_ev_le1 : forall k e, pq_ev k e <= 1.
Proof.
  intros k e. destruct e as [n|m n|n|n]; cbn [pq_ev].
  - apply pq_bi_01.
  - destruct (Nat.eqb m 0); [apply pq_bi_01|].
    destruct (band (Z.of_nat n + 16) <? band (Z.of_nat m + 16));
      pose proof (pq_bi_01 k (Z.of_nat n + 16)); pose proof (pq_bi_01 k (Z.of_nat m + 16)); lia.
  - lia.
  - pose proof (pq_bi_01 k (Z.of_nat n + 16)). lia.
Qed.

Lemma pq_run_len : forall k tr, pq_run k tr <= Z.of_nat (length tr).
Proof.
  intros k tr. induction tr as [|e r IH]; cbn [pq_run length]; [lia|].
  pose proof (pq_ev_le1 k e). lia.
Qed.

Lemma pq_run_app : forall k a b, pq_run k (a ++ b) = pq_run k a + pq_run k b.
Proof. intros k a b. induction a as [|e r IH]; cbn [pq_run app]; lia. Qed.

Lemma held_nlive_le : forall P M, 0 <= M -> (forall e, In e P -> Z.of_nat (esize e) <= M) ->
  held P + 16 * nlive P <= Z.of_nat (length P) * (M + 16).
Proof.
  induction P as [|e r IH]; intros M HM H; cbn [held nlive length]; [lia|].
  assert (He : Z.of_nat (esize e) <= M) by (apply H; left; reflexivity).
  assert (Hr : held r + 16 * nlive r <= Z.of_nat (length r) * (M + 16)) by (apply IH; [exact HM | intros e' He'; apply H; right; exact He']).
  assert (Hs : held_ev e + 16 * nlive_ev e <= M + 16).
  { destruct e as [n|[|m] n|n|n]; cbn [held_ev nlive_ev esize] in *; lia. }
  rewrite Nat2Z.inj_succ. nia.
Qed.

Lemma po_bcnt_app : forall a b k, po_bcnt (a ++ b) k = po_bcnt a k + po_bcnt b k.
Proof. intros a b k. unfold po_bcnt. rewrite filter_app, length_app. lia. Qed.

Lemma po_bcnt_nn : forall a k, 0 <= po_bcnt a k.
Proof. intros a k. unfold po_bcnt. lia. Qed.

Lemma po_bcnt_perm : forall a b k, Permutation a b -> po_bcnt a k = po_bcnt b k.
Proof.
  intros a b k H. unfold po_bcnt.
  assert (P : Permutation (List.filter (fun s => band (Z.of_nat s + 16) =? k) a) (List.filter (fun s => band (Z.of_nat s + 16) =? k) b)).
  { induction H as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2]; cbn [List.filter].
    - constructor.
    - destruct (band (Z.of_nat x + 16) =? k); cbv iota; [apply perm_skip|]; exact IH.
    - destruct (band (Z.of_nat x + 16) =? k), (band (Z.of_nat y + 16) =? k); cbv iota;
        try apply perm_swap; try apply perm_skip; apply Permutation_refl.
    - eapply Permutation_trans; [exact IH1 | exact IH2]. }
  rewrite (Permutation_length P). reflexivity.
Qed.

Lemma zl_perm_nat : forall a b, Permutation a b -> zl (map Z.of_nat a) = zl (map Z.of_nat b).
Proof. intros a b H. apply zl_perm, Permutation_map, H. Qed.

Lemma zl_app_nat : forall a b, zl (map Z.of_nat (a ++ b)) = zl (map Z.of_nat a) + zl (map Z.of_nat b).
Proof. intros a b. rewrite map_app. apply zl_app. Qed.

Lemma zl_nat_nn : forall a, 0 <= zl (map Z.of_nat a).
Proof. induction a as [|x a IH]; cbn [map zl]; lia. Qed.

Lemma rpos_zl : forall B A, Forall2 rpos B A -> zl (map Z.of_nat B) <= 3 * zl (map Z.of_nat A).
Proof.
  intros B A H. induction H as [|b a B A Hr _ IH]; cbn [map zl]; [lia|].
  destruct Hr as [->|(E & q & -> & -> & Hq)]; lia.
Qed.

Lemma newcap_ge : forall c need, 0 <= c -> 0 <= newcap c need.
Proof.
  intros c need Hc. unfold newcap.
  assert (G : forall f c0, 0 <= c0 -> 0 <= dbl f c0 need).
  { induction f as [|f IH]; intros c0 H0; cbn [dbl]; [exact H0|].
    destruct (need <=? c0); [exact H0 | apply IH; lia]. }
  apply G. destruct (c =? 0); lia.
Qed.

Definition rm_ind (k c : Z) : Z := if c =? 0 then 0 else pq_bi k (c + 16).
Definition rm_indb (c : Z) : Z := if c =? 0 then 0 else c + 16.
Definition rm_indr (k c : Z) : Z := if c =? 0 then 0 else pq_bi k c.
Definition rm_indrb (c : Z) : Z := if c =? 0 then 0 else c.

Lemma rm_ind_01 : forall k c, 0 <= rm_ind k c <= 1.
Proof. intros k c. unfold rm_ind. destruct (c =? 0); [lia | apply pq_bi_01]. Qed.

Lemma rm_indr_01 : forall k c, 0 <= rm_indr k c <= 1.
Proof. intros k c. unfold rm_indr. destruct (c =? 0); [lia | apply pq_bi_01]. Qed.

Lemma rm_indb_le : forall c, 0 <= c -> 0 <= rm_indb c <= c + 16.
Proof. intros c H. unfold rm_indb. destruct (c =? 0); lia. Qed.

Lemma rm_indrb_le : forall c, 0 <= c -> 0 <= rm_indrb c <= c.
Proof. intros c H. unfold rm_indrb. destruct (c =? 0); lia. Qed.

Section Dom.

Variable b0 : pbound.
Variable beta : Z -> Z.
Hypothesis Hl0 : length (pb_live b0) = 49%nat.
Hypothesis Hlive0 : forall k, 0 <= k < 49 -> znth k (pb_live b0) <= 2.
Hypothesis Hbytes0 : pb_bytes b0 <= 2 ^ 28.
Hypothesis Hcap0 : forall k, 0 <= k < 49 -> znth k (pb_cap b0) = 3 * beta k + 271.
Hypothesis HC0 : CAPOK2 (GALL (pb_cap b0)) (GMAP (pb_cap b0)) pq_BMAX pq_NMAX.

Lemma H_run : forall b tr, length (pb_live b) = 49%nat ->
  length (pb_live (rf_run pack_form b tr)) = 49%nat /\
  (forall k, 0 <= k < 49 -> znth k (pb_live (rf_run pack_form b tr)) = znth k (pb_live b) + pq_run k tr) /\
  pb_bytes (rf_run pack_form b tr) = pb_bytes b + held tr + 16 * nlive tr /\
  pb_cap (rf_run pack_form b tr) = pb_cap b.
Proof. exact PackFold.pk_run. Qed.

Lemma H_frees_le : forall b D, length (pb_live b) = 49%nat -> (forall ak, In ak D -> 0 <= snd ak) ->
  length (pb_live (rf_frees pack_form b D)) = 49%nat /\
  (forall k, 0 <= k < 49 -> znth k (pb_live (rf_frees pack_form b D)) <= znth k (pb_live b)) /\
  pb_bytes (rf_frees pack_form b D) <= pb_bytes b /\
  pb_cap (rf_frees pack_form b D) = pb_cap b.
Proof. exact PackFold.pk_frees_le. Qed.

Lemma H_wfold : forall b st P, length (pb_live b) = 49%nat -> 0 <= w_cap st ->
  length (pb_live (WriterRet.wfold pack_form b st P)) = 49%nat /\
  (forall k, 0 <= k < 49 -> znth k (pb_live (WriterRet.wfold pack_form b st P)) =
     znth k (pb_live b) + rm_ind k (w_cap (putN st P)) - rm_ind k (w_cap st)) /\
  pb_bytes (WriterRet.wfold pack_form b st P) = pb_bytes b + rm_indb (w_cap (putN st P)) - rm_indb (w_cap st) /\
  pb_cap (WriterRet.wfold pack_form b st P) = pb_cap b.
Proof. exact PackFold.pk_wfold. Qed.

Lemma H_txfold : forall b len cap ns, length (pb_live b) = 49%nat -> 0 <= cap -> 0 <= len ->
  Forall (fun m => 0 <= m) ns ->
  length (pb_live (tx_fold pack_form b len cap ns)) = 49%nat /\
  (forall k, 0 <= k < 49 -> znth k (pb_live (tx_fold pack_form b len cap ns)) =
     znth k (pb_live b) + rm_indr k (tx_capf len cap ns) - rm_indr k cap) /\
  pb_bytes (tx_fold pack_form b len cap ns) = pb_bytes b + rm_indrb (tx_capf len cap ns) - rm_indrb cap /\
  pb_cap (tx_fold pack_form b len cap ns) = pb_cap b.
Proof. intros b len cap ns HL Hc _ _. exact (PackFold.pk_txfold b len cap ns HL Hc). Qed.

Definition dom (b : pbound) (V : Z -> Z) (y : Z) : Prop :=
  length (pb_live b) = 49%nat /\ pb_cap b = pb_cap b0 /\
  (forall k, 0 <= k < 49 -> znth k (pb_live b) <= znth k (pb_live b0) + V k) /\ pb_bytes b <= pb_bytes b0 + y.

Lemma dom0 : dom b0 (fun _ => 0) 0.
Proof. split; [exact Hl0|]. split; [reflexivity|]. split; [intros; lia | lia]. Qed.

Lemma dom_mono : forall b V V' y y', dom b V y -> (forall k, 0 <= k < 49 -> V k <= V' k) -> y <= y' -> dom b V' y'.
Proof.
  intros b V V' y y' (H1 & H2 & H3 & H4) HV Hy. split; [exact H1|]. split; [exact H2|].
  split; [intros k Hk; specialize (H3 k Hk); specialize (HV k Hk); lia | lia].
Qed.

Lemma dom_run : forall b V y tr, dom b V y ->
  dom (rf_run pack_form b tr) (fun k => V k + pq_run k tr) (y + (held tr + 16 * nlive tr)).
Proof.
  intros b V y tr (H1 & H2 & H3 & H4). destruct (H_run b tr H1) as (R1 & R2 & R3 & R4).
  split; [exact R1|]. split; [rewrite R4; exact H2|].
  split; [intros k Hk; rewrite (R2 k Hk); specialize (H3 k Hk); lia | rewrite R3; lia].
Qed.

Lemma dom_frees : forall b V y D, dom b V y -> (forall ak, In ak D -> 0 <= snd ak) -> dom (rf_frees pack_form b D) V y.
Proof.
  intros b V y D (H1 & H2 & H3 & H4) HD. destruct (H_frees_le b D H1 HD) as (R1 & R2 & R3 & R4).
  split; [exact R1|]. split; [rewrite R4; exact H2|].
  split; [intros k Hk; specialize (R2 k Hk); specialize (H3 k Hk); lia | lia].
Qed.

Lemma dom_wfold : forall b V y st Q, dom b V y -> w_cap st = 0 -> 0 <= w_cap (putN st Q) ->
  dom (WriterRet.wfold pack_form b st Q) (fun k => V k + 1) (y + (w_cap (putN st Q) + 16)).
Proof.
  intros b V y st Q (H1 & H2 & H3 & H4) H0 Hc. destruct (H_wfold b st Q H1 ltac:(lia)) as (R1 & R2 & R3 & R4).
  rewrite H0 in R2, R3. split; [exact R1|]. split; [rewrite R4; exact H2|]. split.
  - intros k Hk. rewrite (R2 k Hk). specialize (H3 k Hk). pose proof (rm_ind_01 k (w_cap (putN st Q))).
    unfold rm_ind at 2. cbn. lia.
  - rewrite R3. pose proof (rm_indb_le (w_cap (putN st Q)) Hc). unfold rm_indb at 2. cbn. lia.
Qed.

Lemma dom_txfold : forall b V y ns, dom b V y -> Forall (fun m => 0 <= m) ns -> 0 <= tx_capf 0 0 ns ->
  dom (tx_fold pack_form b 0 0 ns) (fun k => V k + 1) (y + tx_capf 0 0 ns).
Proof.
  intros b V y ns (H1 & H2 & H3 & H4) Hn Hc.
  destruct (H_txfold b 0 0 ns H1 ltac:(lia) ltac:(lia) Hn) as (R1 & R2 & R3 & R4).
  split; [exact R1|]. split; [rewrite R4; exact H2|]. split.
  - intros k Hk. rewrite (R2 k Hk). specialize (H3 k Hk). pose proof (rm_indr_01 k (tx_capf 0 0 ns)).
    unfold rm_indr at 2. cbn. lia.
  - rewrite R3. pose proof (rm_indrb_le (tx_capf 0 0 ns) Hc). unfold rm_indrb at 2. cbn. lia.
Qed.

Lemma room_dom : forall b V y r, dom b V y -> 0 <= r <= pq_NMAX -> y <= 2 ^ 42 ->
  V (band r) <= 3 * beta (band r) + 268 -> room_pack b r.
Proof.
  intros b V y r (H1 & H2 & H3 & H4) Hr Hy HV.
  assert (Hb : 0 <= band r < 49) by (pose proof (band_nonneg r ltac:(lia)); pose proof (band_le48 r ltac:(lia)); lia).
  apply room_pack_big.
  - rewrite H2. exact HC0.
  - exact Hr.
  - assert (E1 : pq_BMAX = 17592186044416) by reflexivity. assert (E2 : pq_NMAX = 536862720) by reflexivity.
    assert (E3 : 2 ^ 42 = 4398046511104) by reflexivity. assert (E4 : 2 ^ 28 = 268435456) by reflexivity.
    rewrite E2 in Hr. rewrite E3 in Hy. rewrite E4 in Hbytes0. rewrite E1. lia.
  - rewrite H2. specialize (H3 _ Hb). pose proof (Hlive0 _ Hb). rewrite (Hcap0 _ Hb). lia.
Qed.

Lemma rr_dom : forall b V y tr, dom b V y ->
  (forall P R, tr = P ++ R -> forall k, 0 <= k < 49 -> V k + pq_run k P <= 3 * beta k + 268) ->
  (forall P R, tr = P ++ R -> y + (held P + 16 * nlive P) <= 2 ^ 42) ->
  (forall e, In e tr -> is_call e = true -> Z.of_nat (esize e) + 16 <= 2 ^ 28) ->
  room_run pack_form b tr.
Proof.
  intros b V y tr HD HV Hy He. apply room_run_of. intros P e R E Hc.
  assert (Hin : In e tr) by (rewrite E; apply in_or_app; right; left; reflexivity).
  pose proof (He e Hin Hc) as Hs. split; [|exact Hs].
  change (room_pack (rf_run pack_form b P) (Z.of_nat (esize e) + 16)).
  assert (Hb : 0 <= band (Z.of_nat (esize e) + 16) < 49)
    by (pose proof (band_nonneg (Z.of_nat (esize e) + 16) ltac:(lia));
        pose proof (band_le48 (Z.of_nat (esize e) + 16) ltac:(lia)); lia).
  apply (room_dom (rf_run pack_form b P) (fun k => V k + pq_run k P) (y + (held P + 16 * nlive P))).
  - apply dom_run, HD.
  - assert (E2 : pq_NMAX = 536862720) by reflexivity. assert (E4 : 2 ^ 28 = 268435456) by reflexivity.
    rewrite E2. rewrite E4 in Hs. lia.
  - exact (Hy P (e :: R) E).
  - exact (HV P (e :: R) E _ Hb).
Qed.

Lemma wr_dom : forall b V y t p c f, dom b V y ->
  (forall k, 0 <= k < 49 -> V k + 1 <= 3 * beta k + 268) ->
  y + (2 * wlen t p + 4112) <= 2 ^ 42 -> 2 * wlen t p + 4112 <= pq_NMAX ->
  (forall Q bs R, wdpieces t p = Q ++ bs :: R ->
     w_cap (putN (w0 c f) Q) < Z.of_nat (length (w_text (putN (w0 c f) Q))) + Z.of_nat (length bs) + 1 ->
     newcap (w_cap (putN (w0 c f) Q)) (Z.of_nat (length (w_text (putN (w0 c f) Q))) + Z.of_nat (length bs) + 1)
       <= 2 * wlen t p + 4096) ->
  (forall Q R, wdpieces t p = Q ++ R -> 0 <= w_cap (putN (w0 c f) Q) <= 2 * wlen t p + 4096) ->
  WriterRet.wr_rooms pack_form b (w0 c f) (wdpieces t p).
Proof.
  intros b V y t p c f HD HV Hy HN HS HC. apply wr_rooms_of. intros Q bs R E _ Hlt.
  pose proof (HS Q bs R E Hlt) as Hn. pose proof (HC Q (bs :: R) E) as Hc.
  pose proof (newcap_ge (w_cap (putN (w0 c f) Q))
    (Z.of_nat (length (w_text (putN (w0 c f) Q))) + Z.of_nat (length bs) + 1) ltac:(lia)) as Hg.
  change (room_pack (WriterRet.wfold pack_form b (w0 c f) Q)
    (newcap (w_cap (putN (w0 c f) Q)) (Z.of_nat (length (w_text (putN (w0 c f) Q))) + Z.of_nat (length bs) + 1) + 16)).
  set (r := newcap _ _ + 16).
  assert (Hb : 0 <= band r < 49) by (pose proof (band_nonneg r ltac:(lia)); pose proof (band_le48 r ltac:(lia)); lia).
  apply (room_dom _ (fun k => V k + 1) (y + (w_cap (putN (w0 c f) Q) + 16))).
  - apply dom_wfold; [exact HD | reflexivity | lia].
  - lia.
  - lia.
  - exact (HV _ Hb).
Qed.

Lemma tx_dom : forall b V y t p, dom b V y ->
  (forall k, 0 <= k < 49 -> V k + 1 <= 3 * beta k + 268) ->
  y + (2 * wlen t p + 8) <= 2 ^ 42 -> 2 * wlen t p + 8 <= pq_NMAX ->
  Forall (fun m => 0 <= m) (rtt_ns t p) ->
  (forall Q m R, rtt_ns t p = Q ++ m :: R -> 2 * (zsum Q + m + 1) <= 2 * wlen t p + 8) ->
  (forall Q R, rtt_ns t p = Q ++ R -> 0 <= tx_capf 0 0 Q <= 2 * wlen t p + 8) ->
  tx_rooms pack_form b 0 0 (rtt_ns t p).
Proof.
  intros b V y t p HD HV Hy HN Hnn HS HC. apply tx_rooms_of. intros Q m R E _.
  pose proof (HS Q m R E) as Hs. pose proof (HC Q (m :: R) E) as Hc.
  assert (HnnQ : Forall (fun m => 0 <= m) Q) by (rewrite E in Hnn; apply Forall_app in Hnn; exact (proj1 Hnn)).
  assert (Hm : 0 <= m) by (rewrite E in Hnn; apply Forall_app in Hnn; destruct Hnn as [_ Hnn]; inversion Hnn; assumption).
  assert (HzQ : 0 <= zsum Q).
  { clear -HnnQ. induction HnnQ as [|a l Ha _ IH]; cbn [zsum]; lia. }
  change (room_pack (tx_fold pack_form b 0 0 Q) (2 * (0 + zsum Q + m + 1))).
  rewrite Z.add_0_l.
  set (r := 2 * (zsum Q + m + 1)).
  assert (Hb : 0 <= band r < 49) by (pose proof (band_nonneg r ltac:(lia)); pose proof (band_le48 r ltac:(lia)); lia).
  apply (room_dom _ (fun k => V k + 1) (y + tx_capf 0 0 Q)).
  - apply dom_txfold; [exact HD | exact HnnQ | lia].
  - lia.
  - lia.
  - exact (HV _ Hb).
Qed.

Lemma room_b : forall b c a y r, dom b (fun k => c + a * beta k) y -> 0 <= a <= 3 -> c <= 268 ->
  (forall k, 0 <= beta k) -> 0 <= r <= 536862720 -> y <= 4398046511104 -> room_pack b r.
Proof.
  intros b c a y r HD Ha Hc Hb Hr Hy. apply (room_dom b _ y r HD).
  - change pq_NMAX with (2 ^ 29 - 8192). change (2 ^ 29) with 536870912. lia.
  - change (2 ^ 42) with 4398046511104. exact Hy.
  - pose proof (Hb (band r)). nia.
Qed.

Lemma rr_b : forall b c a y tr c' a' yb, dom b (fun k => c + a * beta k) y ->
  (forall k, 0 <= beta k) ->
  (forall P R, tr = P ++ R -> forall k, 0 <= k < 49 -> pq_run k P <= c' + a' * beta k) ->
  (forall P R, tr = P ++ R -> held P + 16 * nlive P <= yb) ->
  0 <= a -> 0 <= a' -> a + a' <= 3 -> c + c' <= 268 -> y + yb <= 4398046511104 ->
  (forall e, In e tr -> is_call e = true -> Z.of_nat (esize e) + 16 <= 268435456) ->
  room_run pack_form b tr.
Proof.
  intros b c a y tr c' a' yb HD Hb HP HB Ha Ha' Haa Hcc Hy He. apply (rr_dom b _ y tr HD).
  - intros P R E k Hk. pose proof (HP P R E k Hk). pose proof (Hb k). nia.
  - intros P R E. pose proof (HB P R E). change (2 ^ 42) with 4398046511104. lia.
  - intros e Hi Hc. change (2 ^ 28) with 268435456. exact (He e Hi Hc).
Qed.

Lemma dom_rb : forall b c a y tr c' a' yt, dom b (fun k => c + a * beta k) y ->
  (forall k, 0 <= k < 49 -> pq_run k tr <= c' + a' * beta k) -> held tr + 16 * nlive tr <= yt ->
  dom (rf_run pack_form b tr) (fun k => (c + c') + (a + a') * beta k) (y + yt).
Proof.
  intros b c a y tr c' a' yt HD HP HB. eapply dom_mono; [apply dom_run, HD | |].
  - intros k Hk. cbv beta. pose proof (HP k Hk). nia.
  - lia.
Qed.

Lemma dom_fb : forall b V y D, dom b V y -> (forall ak, In ak D -> 0 <= snd ak) ->
  dom (rf_frees pack_form b D) V y.
Proof. intros b V y D HD HN. exact (dom_frees b V y D HD HN). Qed.

Variable x : list byte.
Variable cnt0 : Z.
Hypothesis Hbeta : beta = beta2_x (zb x).
Hypothesis Hcnt : 0 <= cnt0 <= 3 * 2 ^ 60.
Hypothesis Hn : ent_n x <= 0x300000.

Lemma H_lsz : forall tr k, grow_up tr -> pq_run k tr <= po_bcnt (lsz tr) k.
Proof. exact PackTraceT.pq_lsz0. Qed.
Lemma H_rbytes : forall sm y ok P R, snd (jr_run sm y ok) = P ++ R ->
  held P + 16 * nlive P <= 256 * Z.of_nat (length y) + 16448.
Proof. exact PackTraceT.run_bytes. Qed.
Lemma H_resize : forall sm y ok e, In e (snd (jr_run sm y ok)) -> is_call e = true ->
  Z.of_nat (esize e) <= 56 * Z.of_nat (length y) + 448.
Proof. exact PackTraceT.run_esize. Qed.
Lemma H_rprefix : forall sm y ok P R, snd (jr_run sm y ok) = P ++ R ->
  forall k, pq_run k P <= pq_run k (snd (jr_run sm y ok)) + 100.
Proof. exact PackTraceT.run_prefix. Qed.
Lemma H_rcb : forall sm y t, json_read sm y = Some t ->
  exists I, Permutation (lsz (snd (jr_run sm y []))) (pq_cb t ++ I).
Proof. exact PackTraceT.run_cb. Qed.
Lemma H_tcount : forall u k, pq_run k (PjRoundTrip.ttrace u) = po_bcnt (rtsz u) k.
Proof. exact PackTraceR.tt_count. Qed.
Lemma H_tsplit : forall u, Permutation (rtsz u) (pq_cb u ++ po_rs u).
Proof. exact PackTraceR.tt_split. Qed.
Lemma H_tprefix : forall u P R k, PjRoundTrip.ttrace u = P ++ R ->
  pq_run k P <= pq_run k (PjRoundTrip.ttrace u) + 2 * Z.of_nat (depth u).
Proof. exact PackTraceR.tt_prefix. Qed.
Lemma H_tbytes : forall u P R, PjRoundTrip.ttrace u = P ++ R ->
  held P + 16 * nlive P <= zl (map Z.of_nat (rtsz u)) + 16 * Z.of_nat (length (rtsz u)).
Proof. exact PackTraceR.tt_bytes. Qed.
Lemma H_crt_cnt : forall t k, po_bcnt (rtsz (crt_tree t)) k <= po_bcnt (rtsz t) k + 4.
Proof. exact PackTraceR.crt_bcnt. Qed.
Lemma H_crt_zl : forall t, zl (map Z.of_nat (rtsz (crt_tree t))) <= 2 * zl (map Z.of_nat (rtsz t)) + 544.
Proof. exact PackTraceR.crt_zl. Qed.
Lemma H_crt_len : forall t, (length (rtsz (crt_tree t)) <= length (rtsz t) + 4)%nat.
Proof. exact PackTraceR.crt_len. Qed.
Lemma H_crt_depth : forall t, (depth (crt_tree t) <= Nat.max 1 (depth t))%nat.
Proof. exact PackTraceR.crt_depth. Qed.
Lemma H_set_esize : forall n cap e, 0 <= n <= cap -> In e (set_trace n cap 10) -> is_call e = true ->
  Z.of_nat (esize e) <= 112 * n + 448.
Proof. intros n cap e Hn' Hi Hc. exact (PackTraceR.set_esize n cap e (proj1 Hn') Hi Hc). Qed.
Lemma H_wsize : forall t p c f Q bs R, wdpieces t p = Q ++ bs :: R ->
  w_cap (putN (w0 c f) Q) < Z.of_nat (length (w_text (putN (w0 c f) Q))) + Z.of_nat (length bs) + 1 ->
  newcap (w_cap (putN (w0 c f) Q)) (Z.of_nat (length (w_text (putN (w0 c f) Q))) + Z.of_nat (length bs) + 1)
    <= 2 * wlen t p + 4096.
Proof. exact PackTraceR.wr_newcap. Qed.
Lemma H_wcap : forall t p c f Q R, wdpieces t p = Q ++ R -> 0 <= w_cap (putN (w0 c f) Q) <= 2 * wlen t p + 4096.
Proof. intros t p c f Q R E. split; [apply PackTraceR.wr_cap_nn | exact (PackTraceR.wr_cap t p c f Q R E)]. Qed.
Lemma H_txsize : forall t p Q m R, rtt_ns t p = Q ++ m :: R -> 2 * (zsum Q + m + 1) <= 2 * wlen t p + 8.
Proof. exact PackTraceR.tx_req. Qed.
Lemma H_txcap : forall t p Q R, rtt_ns t p = Q ++ R -> 0 <= tx_capf 0 0 Q <= 2 * wlen t p + 8.
Proof. exact PackTraceR.tx_cap. Qed.
Lemma H_txnn : forall t p, Forall (fun m => 0 <= m) (rtt_ns t p).
Proof. exact PackTraceR.rtt_ns_nn. Qed.
Lemma H_wlen_crt : forall t, wlen (crt_tree t) true <= wlen t true + 256.
Proof. intros t. pose proof (PackTraceR.crt_wlen t true). lia. Qed.
Lemma H_cnt_bounds : forall t p, json_read jr_strtod (zb x) = Some t ->
  0 <= wcalls t p <= 2 ^ 30 /\ 0 <= wcalls (crt_tree t) true <= 2 ^ 30 /\
  Z.of_nat (PjRoundTrip.tcalls t) <= 2 ^ 30 /\ Z.of_nat (PjRoundTrip.tcalls (crt_tree t)) <= 2 ^ 30 /\
  0 <= wN t p <= 2 ^ 30.
Proof.
  intros t p Ht.
  assert (L : Z.of_nat (length (zb x)) <= 3 * 2 ^ 20)
    by (unfold zb; rewrite length_map; unfold ent_n in Hn; change (3 * 2 ^ 20) with 3145728; lia).
  split; [exact (PackTraceR.wcalls_read (zb x) t p Ht L)|].
  split; [exact (PackTraceR.wcalls_crt_read (zb x) t Ht L)|].
  split; [exact (PackTraceR.tcalls_read (zb x) t Ht L)|].
  split; [exact (PackTraceR.tcalls_crt_read (zb x) t Ht L)|].
  exact (PackTraceR.wN_read (zb x) t p Ht L).
Qed.

Lemma H_cancel : forall b tr D, length (pb_live b) = 49%nat -> grow_up tr ->
  Permutation (map snd D) (map Z.of_nat (lsz tr)) -> Z.of_nat (length D) = nlive tr ->
  rf_frees pack_form (rf_run pack_form b tr) D = b.
Proof. exact PackFold.pk_cancel. Qed.
Lemma H_cno_fold : forall b n T ok E1 E2 E3, length (pb_live b) = 49%nat ->
  cno_dl T E1 -> cno_dl T E2 -> cno_dl T E3 -> grow_up T ->
  cno_free3 pack_form (cno_mid pack_form b n T ok E1 E2 E3) n = b.
Proof. exact PackFold.cno_fold_eq. Qed.
Lemma H_b3 : forall b y E1 E2 E3 Dp, length (pb_live b) = 49%nat ->
  ent_b3 pack_form b y E1 E2 E3 Dp = ent_b2 pack_form b y E1 E2 E3 Dp.
Proof. exact PackFold.ent_b3_eq. Qed.
Lemma H_rtt_bf : forall b cnt t p, length (pb_live b) = 49%nat -> 0 <= cnt <= 2 ^ 62 ->
  wlen t p + 1 <= 2 ^ 28 -> rtt_bf pack_form b cnt t p = rf_run pack_form b (PjRoundTrip.ttrace t).
Proof. exact PackFold.rtt_bf_eq. Qed.
Lemma H_crt_b2 : forall b cnt t Df y, length (pb_live b) = 49%nat -> 0 <= cnt <= 2 ^ 62 ->
  json_read jr_strtod y = Some t -> Z.of_nat (length y) <= 3 * 2 ^ 20 ->
  crt_dl (PjRoundTrip.ttrace t) Df -> crt_b2 pack_form b cnt t Df = rf_run pack_form b (PjRoundTrip.ttrace t).
Proof. exact PackFold.crt_b2_eq. Qed.
Lemma H_crt_fin : forall b cnt t cset bf y, length (pb_live b) = 49%nat -> 0 <= cnt <= 2 ^ 62 ->
  json_read jr_strtod y = Some t -> Z.of_nat (length y) <= 3 * 2 ^ 20 ->
  crt_fin pack_form b cnt t cset bf -> bf = b.
Proof. exact PackFold.crt_fin_eq. Qed.
Lemma H_wfull : forall b c t p, length (pb_live b) = 49%nat -> 0 <= c <= 2 ^ 62 -> wfull pack_form b c t p = b.
Proof. exact PackFold.wfull_eq. Qed.
Lemma H_crs_pass_fold : forall b c y t p, length (pb_live b) = 49%nat -> 0 <= c <= 2 ^ 62 ->
  crs_pass_fold pack_form b c y t p = b.
Proof. exact PackFold.crs_pass_fold_eq. Qed.

Lemma zb_len : length (zb x) = length x.
Proof. unfold zb. apply length_map. Qed.

Lemma n_rng : 0 <= ent_n x <= 3145728.
Proof. unfold ent_n in *. lia. Qed.

Lemma zb_small : Z.of_nat (length (zb x)) <= 3 * 2 ^ 20.
Proof. rewrite zb_len. pose proof n_rng. unfold ent_n in *. change (3 * 2 ^ 20) with 3145728. lia. Qed.

Lemma beta_nn : forall k, 0 <= beta k.
Proof. intros k. rewrite Hbeta. apply (proj1 (beta2_x_own (zb x))). Qed.

Lemma T_grow : grow_up (ent_T x).
Proof. exact (jr_grow_up jr_strtod (zb x) []). Qed.

Lemma T_le : forall k, 0 <= k < 49 -> pq_run k (ent_T x) <= 0 + 1 * beta k.
Proof.
  intros k _. pose proof (H_lsz (ent_T x) k T_grow) as H. rewrite Hbeta. unfold beta2_x.
  rewrite po_bcnt_app.
  pose proof (po_bcnt_nn (match json_read jr_strtod (zb x) with Some t => po_rs t | None => [] end) k).
  unfold ent_T in *. lia.
Qed.

Lemma T_prefix : forall P R, ent_T x = P ++ R -> forall k, 0 <= k < 49 -> pq_run k P <= 100 + 1 * beta k.
Proof.
  intros P R E k Hk. pose proof (H_rprefix jr_strtod (zb x) [] P R E k). pose proof (T_le k Hk).
  unfold ent_T in *. lia.
Qed.

Lemma T_bytes : forall P R, ent_T x = P ++ R -> held P + 16 * nlive P <= 256 * ent_n x + 16448.
Proof.
  intros P R E. pose proof (H_rbytes jr_strtod (zb x) [] P R E) as H. rewrite zb_len in H. unfold ent_n. exact H.
Qed.

Lemma T_full : held (ent_T x) + 16 * nlive (ent_T x) <= 256 * ent_n x + 16448.
Proof. apply (T_bytes (ent_T x) []). rewrite app_nil_r. reflexivity. Qed.

Lemma T_esize : forall e, In e (ent_T x) -> is_call e = true -> Z.of_nat (esize e) + 16 <= 268435456.
Proof.
  intros e Hi Hc. pose proof (H_resize jr_strtod (zb x) [] e Hi Hc) as H. rewrite zb_len in H.
  pose proof n_rng. unfold ent_n in *. lia.
Qed.

Lemma took_rng : 0 <= ent_took x <= 2 * ent_n x + 2.
Proof.
  unfold ent_took, ent_n, ncalls. pose proof (G7_4 jr_strtod (zb x) []) as H. rewrite zb_len in H. lia.
Qed.

Lemma c3_rng : 0 <= ent_c3 cnt0 x <= 3 * 2 ^ 60 + 8 * ent_n x + 8.
Proof. unfold ent_c3. pose proof took_rng. lia. Qed.

Lemma len_dl : forall T E, cno_dl T E -> Z.of_nat (length (lsz T)) = nlive T.
Proof.
  intros T E (HP & HL). rewrite <- HL. f_equal. apply Permutation_length in HP.
  rewrite !length_map in HP. symmetry. exact HP.
Qed.

Lemma dl_nn : forall T (E : list (Z * Z)) (ak : Z * Z), Permutation (map snd E) (map Z.of_nat (lsz T)) -> In ak E -> 0 <= snd ak.
Proof.
  intros T E ak HP Hi. assert (H : In (snd ak) (map Z.of_nat (lsz T))).
  { apply (Permutation_in _ HP). apply in_map, Hi. }
  apply in_map_iff in H. destruct H as (s & Es & _). lia.
Qed.

Section Some.
Variable t : jv.
Hypothesis Ht : json_read jr_strtod (zb x) = Some t.

Lemma C_le : forall k, po_bcnt (rtsz t) k <= beta k.
Proof.
  intros k. destruct (H_rcb jr_strtod (zb x) t Ht) as (I & HI).
  rewrite (po_bcnt_perm _ _ k (H_tsplit t)), po_bcnt_app.
  rewrite Hbeta. unfold beta2_x. rewrite Ht, po_bcnt_app, (po_bcnt_perm _ _ k HI), po_bcnt_app.
  pose proof (po_bcnt_nn I k). lia.
Qed.

Lemma tt_le : forall k, 0 <= k < 49 -> pq_run k (PjRoundTrip.ttrace t) <= 0 + 1 * beta k.
Proof. intros k _. rewrite H_tcount. pose proof (C_le k). lia. Qed.

Lemma depth_t : (Z.of_nat (depth t) <= 32).
Proof. pose proof (json_read_depth jr_strtod (zb x) t Ht) as H. unfold MAXD in H. lia. Qed.

Lemma tt_prefix : forall P R, PjRoundTrip.ttrace t = P ++ R -> forall k, 0 <= k < 49 ->
  pq_run k P <= 64 + 1 * beta k.
Proof.
  intros P R E k Hk. pose proof (H_tprefix t P R k E). pose proof (tt_le k Hk). pose proof depth_t. lia.
Qed.

Lemma crt_prefix : forall P R, PjRoundTrip.ttrace (crt_tree t) = P ++ R -> forall k, 0 <= k < 49 ->
  pq_run k P <= 68 + 1 * beta k.
Proof.
  intros P R E k Hk. pose proof (H_tprefix (crt_tree t) P R k E) as H. rewrite H_tcount in H.
  pose proof (H_crt_cnt t k). pose proof (C_le k). pose proof depth_t. pose proof (H_crt_depth t). lia.
Qed.

Lemma C_bytes : Z.of_nat (length (lsz (ent_T x))) = nlive (ent_T x) ->
  zl (map Z.of_nat (rtsz t)) + 16 * Z.of_nat (length (rtsz t)) <= 3 * (256 * ent_n x + 16448).
Proof.
  intros HL. destruct (input_render_blocks jr_strtod (zb x) t Ht) as (A & B & PA & PB & F2).
  pose proof (lsz_ttrace t) as PT.
  assert (PB' : Permutation (rtsz t) B) by (eapply Permutation_trans; [apply Permutation_sym, PT | exact PB]).
  rewrite (zl_perm_nat _ _ PB'), (Permutation_length PB'), (Forall2_length F2).
  pose proof (rpos_zl B A F2) as R.
  assert (E4 : length (lsz (ent_T x)) = length A) by exact (Permutation_length PA).
  assert (E5 : zl (map Z.of_nat (lsz (ent_T x))) = zl (map Z.of_nat A)) by (apply zl_perm_nat; exact PA).
  pose proof (lsz_held (ent_T x) HL) as HH. pose proof T_full. pose proof (zl_nat_nn A).
  rewrite <- E4. lia.
Qed.

Lemma tt_bytes : Z.of_nat (length (lsz (ent_T x))) = nlive (ent_T x) ->
  forall P R, PjRoundTrip.ttrace t = P ++ R -> held P + 16 * nlive P <= 3 * (256 * ent_n x + 16448).
Proof. intros HL P R E. pose proof (H_tbytes t P R E). pose proof (C_bytes HL). lia. Qed.

Lemma crt_bytes : Z.of_nat (length (lsz (ent_T x))) = nlive (ent_T x) ->
  forall P R, PjRoundTrip.ttrace (crt_tree t) = P ++ R -> held P + 16 * nlive P <= 6 * (256 * ent_n x + 16448) + 608.
Proof.
  intros HL P R E. pose proof (H_tbytes (crt_tree t) P R E). pose proof (C_bytes HL).
  pose proof (H_crt_zl t). pose proof (H_crt_len t). lia.
Qed.

Lemma wl_false : wlen t false <= 3 * ent_n x.
Proof. pose proof (SlotSizes.wlen_false_read jr_strtod (zb x) t Ht) as H. rewrite zb_len in H. exact H. Qed.

Lemma wl_true : wlen t true <= 56 * ent_n x - 54.
Proof. pose proof (SlotSizes.wlen_true_read jr_strtod (zb x) t Ht) as H. rewrite zb_len in H. exact H. Qed.

Lemma wl_nn : forall p, 0 <= wlen t p.
Proof. intros p. unfold wlen. lia. Qed.

Lemma tt_esize : forall e, In e (PjRoundTrip.ttrace t) \/ In e (PjRoundTrip.ttrace (crt_tree t)) ->
  is_call e = true -> Z.of_nat (esize e) + 16 <= 268435456.
Proof.
  intros e Hi Hc. pose proof (SlotSizes.crt_esz jr_strtod (zb x) t Ht zb_small e Hi Hc) as H.
  change (2 ^ 27) with 134217728 in H. lia.
Qed.
End Some.

Lemma D00 : dom b0 (fun k => 0 + 0 * beta k) 0.
Proof. eapply dom_mono; [exact dom0 | intros k _; cbv beta; lia | lia]. Qed.

Lemma cpy_le : forall j k, pq_run k (repeat (EAlloc (length x)) j) <= Z.of_nat j + 0 * beta k.
Proof. intros j k. pose proof (pq_run_len k (repeat (EAlloc (length x)) j)). rewrite repeat_length in H. lia. Qed.

Lemma cpy_bytes : forall j, held (repeat (EAlloc (length x)) j) + 16 * nlive (repeat (EAlloc (length x)) j) =
  Z.of_nat j * (ent_n x + 16).
Proof.
  induction j as [|j IH]; cbn [repeat held nlive held_ev nlive_ev]; [lia|]. unfold ent_n in *.
  rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma Dcpy : forall j, dom (rf_run pack_form b0 (repeat (EAlloc (length x)) j))
  (fun k => (0 + Z.of_nat j) + (0 + 0) * beta k) (0 + Z.of_nat j * (ent_n x + 16)).
Proof.
  intros j. apply dom_rb; [exact D00 | intros k _; apply cpy_le | rewrite cpy_bytes; lia].
Qed.

Lemma RT : forall b c a y, dom b (fun k => c + a * beta k) y -> 0 <= a <= 2 -> c <= 168 -> y <= 1099511627776 ->
  room_run pack_form b (ent_T x).
Proof.
  intros b c a y HD Ha Hc Hy. pose proof n_rng.
  apply (rr_b b c a y (ent_T x) 100 1 (256 * ent_n x + 16448) HD beta_nn); try lia.
  - exact T_prefix.
  - exact T_bytes.
  - exact T_esize.
Qed.

Lemma cno_part : cno_room pack_form b0 (ent_n x) (ent_T x) (cno_ok x).
Proof.
  pose proof n_rng as NR. pose proof beta_nn as BN. unfold cno_room.
  assert (R0 : forall j, (j <= 2)%nat ->
    room_pack (rf_run pack_form b0 (repeat (EAlloc (length x)) j)) (ent_n x + 16)).
  { intros j Hj. apply (room_b _ (0 + Z.of_nat j) (0 + 0) (0 + Z.of_nat j * (ent_n x + 16)) _ (Dcpy j)); first [exact BN | nia]. }
  split; [exact (R0 0%nat ltac:(lia))|].
  split; [exact (R0 1%nat ltac:(lia))|].
  split; [exact (R0 2%nat ltac:(lia))|].
  change (cno_b3 pack_form b0 (ent_n x)) with (rf_run pack_form b0 (repeat (EAlloc (length x)) 3)).
  pose proof (Dcpy 3) as D3. pose proof (proj1 D3) as L3.
  split; [apply (RT _ _ _ _ D3); cbn; lia|].
  destruct (cno_ok x).
  - pose proof (dom_rb _ _ _ _ (ent_T x) 0 1 _ D3 T_le T_full) as D4.
    pose proof (dom_rb _ _ _ _ (ent_T x) 0 1 _ D4 T_le T_full) as D5.
    split; [apply (RT _ _ _ _ D4); cbn; lia | apply (RT _ _ _ _ D5); cbn; lia].
  - intros E1 [P1 L1]. rewrite (H_cancel _ (ent_T x) E1 L3 T_grow P1 L1).
    split; [apply (RT _ _ _ _ D3); cbn; lia|].
    intros E2 [P2 L2]. rewrite (H_cancel _ (ent_T x) E2 L3 T_grow P2 L2).
    apply (RT _ _ _ _ D3); cbn; lia.
Qed.

Lemma WR : forall b c a y t' p c0 f, dom b (fun k => c + a * beta k) y -> 0 <= a <= 3 -> c <= 267 ->
  y <= 2199023255552 -> 0 <= wlen t' p <= 200000000 ->
  WriterRet.wr_rooms pack_form b (w0 c0 f) (wdpieces t' p).
Proof.
  intros b c a y t' p c0 f HD Ha Hc Hy Hw. apply (wr_dom b _ y t' p c0 f HD).
  - intros k Hk. pose proof (beta_nn k). nia.
  - change (2 ^ 42) with 4398046511104. lia.
  - change pq_NMAX with (2 ^ 29 - 8192). change (2 ^ 29) with 536870912. lia.
  - intros Q bs R E Hlt. exact (H_wsize t' p c0 f Q bs R E Hlt).
  - intros Q R E. exact (H_wcap t' p c0 f Q R E).
Qed.

Lemma TX : forall b c a y t' p, dom b (fun k => c + a * beta k) y -> 0 <= a <= 3 -> c <= 267 ->
  y <= 2199023255552 -> 0 <= wlen t' p <= 200000000 ->
  tx_rooms pack_form b 0 0 (rtt_ns t' p).
Proof.
  intros b c a y t' p HD Ha Hc Hy Hw. apply (tx_dom b _ y t' p HD).
  - intros k Hk. pose proof (beta_nn k). nia.
  - change (2 ^ 42) with 4398046511104. lia.
  - change pq_NMAX with (2 ^ 29 - 8192). change (2 ^ 29) with 536870912. lia.
  - apply H_txnn.
  - intros Q m R E. exact (H_txsize t' p Q m R E).
  - intros Q R E. exact (H_txcap t' p Q R E).
Qed.

Lemma D_bw : forall b c a y cnt t' p, dom b (fun k => c + a * beta k) y ->
  dom (rtt_bw pack_form b cnt t' p) (fun k => (c + 1) + a * beta k) (y + (2 * wlen t' p + 4112)).
Proof.
  intros b c a y cnt t' p HD. unfold rtt_bw.
  pose proof (H_wcap t' p cnt (2 ^ 64 - 1) (wdpieces t' p) [] ltac:(rewrite app_nil_r; reflexivity)) as W.
  eapply dom_mono; [apply dom_wfold; [exact HD | reflexivity | lia] | intros k _; cbv beta; lia | lia].
Qed.

Lemma D_bt : forall b c a y cnt t' p, dom b (fun k => c + a * beta k) y ->
  dom (rtt_bt pack_form b cnt t' p) (fun k => (c + 2) + a * beta k) (y + (2 * wlen t' p + 4112) + (2 * wlen t' p + 8)).
Proof.
  intros b c a y cnt t' p HD. unfold rtt_bt.
  pose proof (H_txcap t' p (rtt_ns t' p) [] ltac:(rewrite app_nil_r; reflexivity)) as W.
  eapply dom_mono; [apply dom_txfold; [apply D_bw, HD | apply H_txnn | lia] | intros k _; cbv beta; lia | lia].
Qed.

Lemma pick_rng : forall y n, 0 <= n -> 0 <= pick y n <= n.
Proof.
  intros y n Hn0. unfold pick. destruct (Z.eqb_spec n 0) as [->|Hne]; [lia|].
  pose proof (Z.mod_pos_bound (djb2 5381 y) n ltac:(lia)). lia.
Qed.

Lemma set_len : forall n cap, (length (set_trace n cap 10) <= 3)%nat.
Proof. intros n cap. unfold set_trace. rewrite length_app. destruct (n =? cap); cbn; lia. Qed.

Lemma set_calls : forall n cap e, In e (set_trace n cap 10) -> is_call e = true.
Proof.
  intros n cap e H. unfold set_trace in H. apply in_app_or in H.
  destruct H as [H|[H|[]]]; [destruct (n =? cap); cbn in H; [destruct H as [<-|[<-|[]]]; reflexivity | destruct H] | subst e; reflexivity].
Qed.

Section Some2.
Variable t : jv.
Hypothesis Ht : json_read jr_strtod (zb x) = Some t.
Hypothesis HL : Z.of_nat (length (lsz (ent_T x))) = nlive (ent_T x).

Let YT := 256 * ent_n x + 16448.

Lemma RTT : forall b c a y p cnt, dom b (fun k => c + a * beta k) y -> 0 <= a <= 2 -> c <= 200 ->
  y <= 1099511627776 -> wlen t p <= 200000000 -> rtt_rooms pack_form b cnt t p.
Proof.
  intros b c a y p cnt HD Ha Hc Hy Hw. pose proof n_rng. pose proof (wl_nn t p).
  unfold rtt_rooms. split; [|split].
  - apply (WR b c a y); try lia; exact HD.
  - apply (TX _ (c + 1) a (y + (2 * wlen t p + 4112))); try lia. apply D_bw, HD.
  - apply (rr_b _ (c + 2) a (y + (2 * wlen t p + 4112) + (2 * wlen t p + 8)) _ 64 1 (3 * YT) (D_bt b c a y cnt t p HD) beta_nn);
      try (unfold YT; lia).
    + exact (tt_prefix t Ht).
    + exact (tt_bytes t Ht HL).
    + intros e Hi Hc'. exact (tt_esize t Ht e (or_introl Hi) Hc').
Qed.

Lemma set_prefix : forall n cap P R, set_trace n cap 10 = P ++ R -> forall k, 0 <= k < 49 -> pq_run k P <= 3 + 0 * beta k.
Proof.
  intros n cap P R E k _. pose proof (pq_run_len k P). pose proof (set_len n cap).
  assert (Hl : (length P <= length (set_trace n cap 10))%nat) by (rewrite E, length_app; lia). lia.
Qed.

Lemma set_bytes : forall n cap P R, 0 <= n <= cap -> n <= 2 ^ 21 -> set_trace n cap 10 = P ++ R ->
  held P + 16 * nlive P <= 3 * (112 * 2 ^ 21 + 464).
Proof.
  intros n cap P R Hn' Hm E.
  assert (HM : forall e, In e P -> Z.of_nat (esize e) <= 112 * 2 ^ 21 + 448).
  { intros e Hi. assert (Hi' : In e (set_trace n cap 10)) by (rewrite E; apply in_or_app; left; exact Hi).
    pose proof (H_set_esize n cap e Hn' Hi' (set_calls n cap e Hi')). lia. }
  pose proof (held_nlive_le P (112 * 2 ^ 21 + 448) ltac:(lia) HM) as H.
  assert (Hl : (length P <= 3)%nat) by (pose proof (set_len n cap); assert (length P <= length (set_trace n cap 10))%nat by (rewrite E, length_app; lia); lia).
  nia.
Qed.

Lemma ms_small : forall ms, t = JObj ms -> Z.of_nat (length ms) <= 2 ^ 21.
Proof.
  intros ms E. pose proof (SlotSizes.read_ez jr_strtod (zb x) t Ht zb_small) as Hz. rewrite E in Hz.
  exact (proj1 (SlotSizes.ez_obj_inv ms Hz)).
Qed.

Lemma dom_set : forall B2 V y n b4 cset Do, dom (rf_malloc pack_form B2 37) V y -> 0 <= n <= 2 ^ 21 ->
  crt_set_res pack_form (rf_malloc pack_form B2 37) n (PjRoundTrip.ttrace t) b4 cset Do ->
  dom b4 (fun k => V k + 3) (y + 3 * (112 * 2 ^ 21 + 464)) /\ 0 <= cset <= 3.
Proof.
  intros B2 V y n b4 cset Do HD Hn' Hset.
  destruct Hset as (Db & (HP & _) & [(Hc0 & Di & Dr & Di' & a & HP1 & HP2 & Eb4 & _) |
                                     (cap & Dold & Dnew & Dr & a & a' & Hcap & Hcs & Eb4 & _)]).
  - subst b4. split; [|lia]. eapply dom_mono; [apply dom_fb; [exact HD|] | intros k _; cbv beta; lia | lia].
    intros ak Hi. apply (dl_nn (PjRoundTrip.ttrace t) Db ak HP).
    apply (Permutation_in _ (Permutation_sym HP1)). apply in_or_app. left.
    exact (Permutation_in _ (Permutation_sym HP2) Hi).
  - subst b4. split; [| rewrite Hcs; pose proof (set_len n cap); lia].
    eapply dom_mono; [apply dom_run, HD | intros k Hk; cbv beta | ].
    + pose proof (set_prefix n cap (set_trace n cap 10) [] ltac:(rewrite app_nil_r; reflexivity) k Hk). lia.
    + pose proof (set_bytes n cap (set_trace n cap 10) [] ltac:(lia) ltac:(lia) ltac:(rewrite app_nil_r; reflexivity)). lia.
Qed.

Lemma DB3 : dom (rf_run pack_form b0 (ent_T x)) (fun k => (0 + 0) + (0 + 1) * beta k) (0 + (256 * ent_n x + 16448)).
Proof. exact (dom_rb _ _ _ _ (ent_T x) 0 1 _ D00 T_le T_full). Qed.

Lemma c3_62 : 0 <= ent_c3 cnt0 x <= 2 ^ 62.
Proof. pose proof c3_rng. pose proof n_rng. change (2 ^ 62) with 4611686018427387904. change (2 ^ 60) with 1152921504606846976 in *. lia. Qed.

Lemma crt_part : crt_pre_rooms pack_form (rf_run pack_form b0 (ent_T x)) (ent_c3 cnt0 x) t.
Proof.
  pose proof n_rng as NR. pose proof (wl_false t Ht) as WF. pose proof (wl_true t Ht) as WT.
  pose proof (wl_nn t false). pose proof (wl_nn t true). pose proof DB3 as D3.
  pose proof (H_wlen_crt t) as WC. pose proof (wl_nn (crt_tree t) true).
  assert (DB : dom (rf_run pack_form (rf_run pack_form b0 (ent_T x)) (PjRoundTrip.ttrace t))
                 (fun k => ((0 + 0) + 0) + ((0 + 1) + 1) * beta k) ((0 + (256 * ent_n x + 16448)) + 3 * YT)).
  { apply (dom_rb _ _ _ _ _ 0 1 _ D3 (tt_le t Ht)). apply (tt_bytes t Ht HL (PjRoundTrip.ttrace t) []). rewrite app_nil_r. reflexivity. }
  unfold crt_pre_rooms. split; [|split].
  - apply (RTT _ _ _ _ false _ D3); unfold YT in *; lia.
  - unfold crt_b1. rewrite (H_rtt_bf _ (ent_c3 cnt0 x) t false (proj1 D3) c3_62 ltac:(change (2 ^ 28) with 268435456; lia)).
    apply (RTT _ _ _ _ true _ DB); unfold YT in *; lia.
  - intros ms Hms Df HDf. rewrite (H_crt_b2 _ (ent_c3 cnt0 x) t Df (zb x) (proj1 D3) c3_62 Ht zb_small HDf).
    pose proof (ms_small ms Hms) as MS. change (2 ^ 21) with 2097152 in MS.
    assert (DM : dom (rf_run pack_form (rf_run pack_form (rf_run pack_form b0 (ent_T x)) (PjRoundTrip.ttrace t)) [EAlloc 21])
                   (fun k => (((0 + 0) + 0) + 1) + (((0 + 1) + 1) + 0) * beta k)
                   (((0 + (256 * ent_n x + 16448)) + 3 * YT) + 37)).
    { apply (dom_rb _ _ _ _ _ 1 0 _ DB); [intros k _; pose proof (pq_run_len k [EAlloc 21]); cbn [length] in *; lia | cbn; lia]. }
    unfold crt_obj_rooms. split; [|split].
    + apply (room_b _ _ _ _ 37 DB); first [exact beta_nn | unfold YT in *; lia].
    + intros cap Hcap.
      change (room_run pack_form (rf_run pack_form (rf_run pack_form (rf_run pack_form b0 (ent_T x)) (PjRoundTrip.ttrace t)) [EAlloc 21])
                (set_trace (Z.of_nat (length ms)) cap 10)).
      apply (rr_b _ _ _ _ _ 3 0 (3 * (112 * 2 ^ 21 + 464)) DM beta_nn).
      * intros P R E k Hk. exact (set_prefix _ _ P R E k Hk).
      * intros P R E. exact (set_bytes (Z.of_nat (length ms)) cap P R ltac:(lia) ltac:(change (2 ^ 21) with 2097152; lia) E).
      * lia.
      * lia.
      * lia.
      * lia.
      * unfold YT in *. change (2 ^ 21) with 2097152. lia.
      * intros e Hi Hc. pose proof (H_set_esize (Z.of_nat (length ms)) cap e ltac:(lia) Hi Hc). lia.
    + intros b4 cset Do Hset.
      destruct (dom_set _ _ _ (Z.of_nat (length ms)) b4 cset Do DM ltac:(change (2 ^ 21) with 2097152; lia) Hset) as (D4 & Hcs).
      set (y4 := (((0 + (256 * ent_n x + 16448)) + 3 * YT) + 37) + 3 * (112 * 2 ^ 21 + 464)) in D4.
      assert (D4' : dom b4 (fun k => 4 + 2 * beta k) y4) by (eapply dom_mono; [exact D4 | intros k _; cbv beta; lia | lia]).
      assert (Hy4 : y4 <= 30000000000) by (unfold y4, YT; change (2 ^ 21) with 2097152; lia).
      split.
      * apply (WR _ 4 2 y4 (crt_tree t) true _ _ D4'); lia.
      * unfold crt_b5.
        pose proof (H_wcap (crt_tree t) true (crt_cnt2 (ent_c3 cnt0 x) t + 1 + cset) (2 ^ 64 - 1)
                      (wdpieces (crt_tree t) true) [] ltac:(rewrite app_nil_r; reflexivity)) as W.
        pose proof (dom_wfold _ _ _ (w0 (crt_cnt2 (ent_c3 cnt0 x) t + 1 + cset) (2 ^ 64 - 1))
                      (wdpieces (crt_tree t) true) D4' eq_refl ltac:(lia)) as D5.
        assert (D5' : dom (WriterRet.wfold pack_form b4 (w0 (crt_cnt2 (ent_c3 cnt0 x) t + 1 + cset) (2 ^ 64 - 1))
                            (wdpieces (crt_tree t) true))
                        (fun k => 5 + 2 * beta k) (y4 + (2 * wlen (crt_tree t) true + 4112)))
          by (eapply dom_mono; [exact D5 | intros k _; cbv beta; lia | lia]).
        apply (rr_b _ 5 2 _ _ 68 1 (6 * YT + 608) D5' beta_nn).
        -- exact (crt_prefix t Ht).
        -- exact (crt_bytes t Ht HL).
        -- lia.
        -- lia.
        -- lia.
        -- lia.
        -- unfold YT in *. lia.
        -- intros e Hi Hc. exact (tt_esize t Ht e (or_intror Hi) Hc).
Qed.

Lemma crs_doc_ok : forall c, 0 <= c <= 4611686018427387904 - 8589934592 ->
  crs_doc_rooms pack_form (rf_run pack_form b0 (ent_T x)) c (zb x) t.
Proof.
  intros c Hc. pose proof DB3 as D3. pose proof n_rng as NR. pose proof (wl_false t Ht). pose proof (wl_true t Ht).
  pose proof (wl_nn t false). pose proof (wl_nn t true).
  destruct (H_cnt_bounds t true Ht) as (_ & _ & _ & _ & WN).
  pose proof (pick_rng (zb x) (wN t true) (proj1 WN)) as PK.
  change (2 ^ 30) with 1073741824 in WN.
  unfold crs_doc_rooms.
  rewrite (H_crs_pass_fold _ c (zb x) t true (proj1 D3) ltac:(change (2 ^ 62) with 4611686018427387904; lia)).
  unfold crs_pass_rooms.
  rewrite (H_wfull _ c t true (proj1 D3) ltac:(change (2 ^ 62) with 4611686018427387904; lia)).
  rewrite (H_wfull _ (crs_pass_cnt c (zb x) t true) t false (proj1 D3)
             ltac:(unfold crs_pass_cnt; change (2 ^ 62) with 4611686018427387904; lia)).
  split; split; apply (WR _ _ _ _ _ _ _ _ D3); lia.
Qed.

Lemma crs_part : forall c, 0 <= c <= 4611686018427387904 - 17179869184 -> crs_rooms pack_form (rf_run pack_form b0 (ent_T x)) c x 1 t.
Proof.
  intros c Hc. pose proof DB3 as D3. pose proof n_rng as NR.
  idtac.
  unfold crs_rooms. split; [|split].
  - intros _. apply (RT _ _ _ _ D3); lia.
  - intros _ _. apply crs_doc_ok. lia.
  - intros _ _ tr D' Hpl. destruct Hpl as (ok & res & Ejr & _ & HP & HLn).
    assert (G : grow_up tr) by (pose proof (jr_grow_up jr_strtod (zb x) ok) as G; rewrite Ejr in G; exact G).
    rewrite (H_cancel _ tr D' (proj1 D3) G HP HLn).
    assert (Hct : Z.of_nat (calls tr) <= 2 * ent_n x + 2).
    { pose proof (G7_4 jr_strtod (zb x) ok) as H. rewrite Ejr in H. cbn [snd] in H. rewrite zb_len in H. unfold ent_n. lia. }
    apply crs_doc_ok. lia.
Qed.

End Some2.

Lemma crt_match_rng : forall t B c cset bf,
  0 <= wcalls (crt_tree t) true <= 2 ^ 30 -> Z.of_nat (PjRoundTrip.tcalls (crt_tree t)) <= 2 ^ 30 ->
  crt_fin pack_form B c t cset bf ->
  0 <= match t with
       | JObj _ => 1 + cset + wcalls (crt_tree t) true + Z.of_nat (PjRoundTrip.tcalls (crt_tree t))
       | _ => 0
       end <= 2147483652.
Proof.
  intros t B c cset bf W T Hfin. change (2 ^ 30) with 1073741824 in *.
  destruct t as [| | | txt bits | s | items | ms]; try (cbn; lia).
  destruct Hfin as (Df & _ & b4' & Do & Dp & Dp' & Do' & Hset & _).
  destruct Hset as (Db & _ & [(Hc0 & _) | (cap & Dold & Dnew & Dr & a & a' & Hcap & Hcs & _)]).
  - subst cset. lia.
  - rewrite Hcs. pose proof (set_len (Z.of_nat (length ms)) cap). lia.
Qed.

Lemma none_part : json_read jr_strtod (zb x) = None -> forall E1 E2 E3 D Dp,
  ent_b1 pack_form b0 x E1 E2 E3 = b0 -> Permutation D Dp -> ent_tree_dl x D ->
  rf_room pack_form (ent_b2 pack_form b0 x E1 E2 E3 Dp) (ent_n x + 1) /\
  crs_rooms pack_form (ent_b3 pack_form b0 x E1 E2 E3 Dp) (ent_c3 cnt0 x) x 0 JNull.
Proof.
  intros Hnone E1 E2 E3 D Dp Eb1 HP [HD HDl]. pose proof n_rng as NR.
  assert (Hok : cno_ok x = false) by (unfold cno_ok; rewrite Hnone; reflexivity).
  assert (HPp : Permutation (map snd Dp) (map Z.of_nat (lsz (ent_T x))))
    by (eapply Permutation_trans; [apply Permutation_sym, Permutation_map, HP | exact HD]).
  assert (HLp : Z.of_nat (length Dp) = nlive (ent_T x)) by (rewrite <- (Permutation_length HP); exact HDl).
  assert (Eb2 : ent_b2 pack_form b0 x E1 E2 E3 Dp = b0).
  { unfold ent_b2. rewrite Hok, Eb1. exact (H_cancel b0 (ent_T x) Dp Hl0 T_grow HPp HLp). }
  rewrite (H_b3 b0 x E1 E2 E3 Dp Hl0), Eb2.
  split; [apply (room_b _ _ _ _ _ D00); first [exact beta_nn | lia]|].
  unfold crs_rooms. split; [intros _; apply (RT _ _ _ _ D00); lia|].
  split; intros _ H0; exfalso; exact (H0 eq_refl).
Qed.

Theorem rooms : entry_rooms pack_form b0 cnt0 x.
Proof.
  intros _. split; [exact cno_part|]. intros E1 E2 E3 HE1 HE2 HE3.
  assert (Eb1 : ent_b1 pack_form b0 x E1 E2 E3 = b0).
  { unfold ent_b1. exact (H_cno_fold b0 (ent_n x) (ent_T x) (cno_ok x) E1 E2 E3 Hl0 HE1 HE2 HE3 T_grow). }
  pose proof DB3 as D3. pose proof n_rng as NR.
  split; [rewrite Eb1; apply (RT _ _ _ _ D00); lia|].
  pose proof (len_dl _ _ HE1) as HL.
  case_eq (json_read jr_strtod (zb x)); [intros t Ht | intros Ht].
  - assert (Hok : cno_ok x = true) by (unfold cno_ok; rewrite Ht; reflexivity).
    assert (Eb2 : ent_b2 pack_form b0 x E1 E2 E3 [] = rf_run pack_form b0 (ent_T x)).
    { unfold ent_b2. rewrite Hok, Eb1. reflexivity. }
    rewrite (H_b3 b0 x E1 E2 E3 [] Hl0), Eb2.
    split; [apply (room_b _ _ _ _ _ D3); first [exact beta_nn | lia]|].
    split; [exact (crt_part t Ht HL)|].
    intros cset b4 Hfin.
    pose proof (H_crt_fin _ _ t cset b4 (zb x) (proj1 D3) c3_62 Ht zb_small Hfin) as Eb4. subst b4.
    apply (crs_part t Ht).
    destruct (H_cnt_bounds t false Ht) as (W1 & W2 & T1 & T2 & _).
    destruct (H_cnt_bounds t true Ht) as (W3 & _ & _ & _ & _).
    pose proof (crt_match_rng t _ _ cset _ W2 T2 Hfin) as HM. pose proof c3_rng.
    unfold ent_c4, crt_count.
    change (2 ^ 60) with 1152921504606846976 in *.
    change (2 ^ 30) with 1073741824 in *. lia.
  - intros D Dp HP HD. exact (none_part Ht E1 E2 E3 D Dp Eb1 HP HD).
Qed.

End Dom.
