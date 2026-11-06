(* omx-clap-core/fuzz_preset, Spec: P8 part D5, the 768-byte class 17 has room at every consumer allocation of the
   harness model (h-hpreset-7's port of asan_halts / agrees, piece P8; c-frame-alloc).

   TWO KINDS OF SITE (PresetSite17).
   - Not a read-back position (room17_other): the live class-17 count is at most 2 M17 + 6 (live17_two), M17 the
     class-17 requests of one parse of x or of the trace of x's tree, bounded by the input length with PresetGate's
     per-class charges (g_reads: a class-17 kids-array grow charges 2 input bytes). The quarantine's most,
     QT / (lo 17 + 8), fits beside it: room_ok.
   - A read-back of round trip 2 or 3 (room17_rb): the free history is pre ++ F ++ X (rt_site17), F the writer chain
     of the text read back; the live class-17 count plus X's is D3's joint count N; the quarantine holds at most X's
     class-17 chunks plus the window QT - bytes F - bytes X leaves (PresetRoom.quar17_flush_raw). N is bounded by D1's
     weights (PjWeight.wt_rt3_live2 / wt_rt2b and wt_nf, through PresetSite17.wsum_n17), F's bytes by PresetFlush
     (w_flush_ge / w_flush_nopiece, with PresetPiece.maxpiece_lmax), R's (round trip 2) by r_flush_ge; the sum is
     checked at each of the 17 band tops of the pretty length (rt3_arith, rt2_arith). The tightest band is round
     trip 3 with the copy's pretty length in (32 MiB, 64 MiB]: 3,008 slots spare of 4,893,354.
   room17 joins the two (room_at is decidable, so no classical axiom).

  Nothing here is a function's proof (rule 24). *)
(* Modified by Theorem Labs, 2026-10-30, for the kit: the accounted free
  history is H0 ++ PresetRunQ.hfrees_q, the model's frees that enter the quarantine (a free above kQuarantineMax is
  recycled at once, free_cf's size test). room17_rb's flush still holds: the writer chain F and rendered ()'s chain
  free capacities below the text's length, so they all enter the quarantine (w_chain_small, r_chain_small); of the
  read-back parse's frees X keeps those that enter it, which only lowers its class-17 count. *)
From Stdlib Require Import ZArith List Lia Bool Arith Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import
  PjTree PjGrammar PjRoundTrip PresetReqAt PresetReqAtNoMiss PjCharge PresetRun PresetRoom PresetGate PresetSite17.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetFlush PresetPiece PjWeight.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require SlotSizes PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRunQ.
Import ListNotations.
Local Open Scope Z_scope.

(* ================================================================ the sites that are not a read-back *)

(* PresetGate's charges for class 17: the least grow charge, the least allocation charge, their min *)
Definition mG17 : nat := g_mG 17.
Definition mS17 : nat := Nat.max (Z.to_nat (lo 17) - 17) 1.
Definition mA17 : nat := Nat.min mG17 mS17.

(* M17: the class-17 requests of one reading of x, or of the trace of x's tree *)
Definition M17 : Z := Z.max ((MAXB + 96) / Z.of_nat mA17) ((MAXB + 96) / Z.of_nat mG17 + (3 * MAXB + 96) / Z.of_nat mS17).

Lemma c17_chk : chk_minG (g_pcl 17) mG17 g_hi 9%nat = true.
Proof. vm_compute. reflexivity. Qed.
Lemma mA17_eq : mA17 = 2%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma M17_eq : M17 = 1594757.
Proof. vm_compute. reflexivity. Qed.
Lemma M17_parts : (MAXB + 96) / Z.of_nat mA17 = 1572912 /\
  (MAXB + 96) / Z.of_nat mG17 + (3 * MAXB + 96) / Z.of_nat mS17 = 1594757.
Proof. split; vm_compute; reflexivity. Qed.
Lemma c17_room : 2 * M17 + 6 + DRV + QT / (lo 17 + 8) + (if 17 =? K_BATCH_CLASS then QT / Q_BATCH_BYTES else 0) +
  refill 17 <= cap 17.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Theorem room17_other : forall sm x os i, Z.of_nat (length x) <= MAXB ->
  nth i (hcons sm x os) false = true -> alloc_at (hruns sm x os) i -> ~ rb_pos sm x os i ->
  room_ok 17 (Z.of_nat (cnt (in_cls 17) (hlive (firstn i (hruns sm x os)))) + DRV).
Proof.
  intros sm x os i Hx Hc Ha Hn.
  assert (Hpos : (0 < mA17)%nat) by (rewrite mA17_eq; lia).
  destruct (g_reads sm x 17 mG17 mS17 mA17 Hx c17_chk Hpos (Nat.le_min_l _ _) (Nat.le_min_r _ _) (Nat.le_refl _))
    as [HA HB].
  destruct M17_parts as [EA EB].
  assert (H1 : forall ok, (nprodR is17 (rd_hevs (rtr sm ok x)) <= Z.to_nat M17)%nat).
  { intros ok. specialize (HA ok). rewrite EA in HA. rewrite M17_eq.
    change (nprodR is17) with (nprodR (in_cls 17)). lia. }
  assert (H2 : forall t, fst (jr_run sm x []) = Some t -> (nprodR is17 (rd_hevs (ttrace t)) <= Z.to_nat M17)%nat).
  { intros t Ht. specialize (HB t Ht). rewrite EB in HB. rewrite M17_eq.
    change (nprodR is17) with (nprodR (in_cls 17)). lia. }
  pose proof (live17_two sm x os (Z.to_nat M17) i H1 H2 Hc Ha Hn) as L.
  apply (g_room_le 17 _ (2 * M17 + 6 + DRV) c17_room).
  change (cnt is17 (hlive (firstn i (hruns sm x os)))) with (cnt (in_cls 17) (hlive (firstn i (hruns sm x os)))) in L.
  rewrite M17_eq in L |- *. unfold DRV. lia.
Qed.

(* ================================================================ the read-back sites: the arithmetic

   At a read-back of round trip 3 (t = JObj ms, t' = copy_set ms, P the copy's pretty length) N is D3's joint count
   n17t t + n17t t + n17t t' + nc9 t' + nk65 t' (live class-17 requests plus the class-17 frees after the flush);
   lm is lmax t'. N is bounded twice: by D1's joint L-P weight (wt_rt3_live2, the doc twice and the copy once,
   20910 per counted node and 9129 per byte of the longest piece if it is >= 4096 long), and by the no-flush weight
   (wt_nf, 192 per node, 128 per container of 9 or more, 92 per byte of a long piece; the copy's counts within 4 of
   the doc's). The flush F is pj_write (copy, 1)'s chain: at least T - 4096 bytes, T = pow4k (P + 1), or
   T - 3 lm when a piece is >= 4096 long (a piece is at most max 6 lm, PresetPiece). The window left in the
   quarantine is Q chunks of at least 457 accounted bytes. Round trip 2 is the same with t' = t, D1's any-root
   weight (wt_rt2b) and rendered ()'s chain R after F. The close is checked at the 17 band tops T = 4096 * 2 ^ j,
   j <= 16 (P <= 56 |x| bounds T by 2 ^ 28). *)

Definition CAP17 : Z := 4893354.

Lemma cap17_eq : cap 17 = CAP17.
Proof. vm_compute. reflexivity. Qed.
Lemma refill17_eq : refill 17 = 1.
Proof. vm_compute. reflexivity. Qed.
Lemma lo17_eq : lo 17 + 8 = 457.
Proof. vm_compute. reflexivity. Qed.

Lemma pow_band : forall T, PresetFlush.ispow T -> T < 536870912 ->
  T = 4096 \/ T = 8192 \/ T = 16384 \/ T = 32768 \/ T = 65536 \/ T = 131072 \/ T = 262144 \/ T = 524288 \/
  T = 1048576 \/ T = 2097152 \/ T = 4194304 \/ T = 8388608 \/ T = 16777216 \/ T = 33554432 \/ T = 67108864 \/
  T = 134217728 \/ T = 268435456.
Proof.
  intros T (j & Hj & ->) HT.
  assert (Hj17 : j < 17).
  { destruct (Z.lt_ge_cases j 17) as [H|H]; [exact H|]. exfalso.
    pose proof (Z.pow_le_mono_r 2 17 j ltac:(lia) H) as H2.
    change 536870912 with (4096 * 2 ^ 17) in HT. lia. }
  assert (H : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/
              j = 11 \/ j = 12 \/ j = 13 \/ j = 14 \/ j = 15 \/ j = 16) by lia.
  repeat (destruct H as [->|H]; [cbn; lia|]). subst j. cbn. lia.
Qed.

Ltac band_close B := repeat (destruct B as [B|B]; [subst; unfold CAP17, QT, Q_MAX, Q_CACHE, MAXB in *; lia|]);
  subst; unfold CAP17, QT, Q_MAX, Q_CACHE, MAXB in *; lia.

Lemma rt3_arith : forall L P T N Q lm zF,
  0 <= L <= MAXB -> 0 <= P <= 56 * MAXB - 14 -> P + 1 <= T -> (T = 4096 \/ T < 2 * (P + 1)) ->
  PresetFlush.ispow T -> 0 <= N -> 0 <= Q -> 0 <= lm ->
  20910 * N + (if 4096 <=? lm then 9129 * lm else 0) <= 27387 * L + 102 * P - 38250 ->
  192 * (N - 4) + (if 4096 <=? lm then 276 * lm else 0) <= 3 * (93 * L + 99) ->
  zF >= T - (if 4096 <=? lm then 3 * lm else 4096) ->
  457 * Q <= Z.max 0 (QT - zF) ->
  N + Q + 8 <= CAP17.
Proof.
  intros L P T N Q lm zF HL HP HT1 HT2 Hp HN HQ Hlm HW HNF HF HW8.
  assert (HT : T < 536870912) by (unfold MAXB in HP; lia).
  pose proof (pow_band T Hp HT) as B.
  destruct (4096 <=? lm) eqn:E; [apply Z.leb_le in E|apply Z.leb_gt in E]; band_close B.
Qed.

Lemma rt2_arith : forall L P T N Q lm zF zR,
  0 <= L <= MAXB -> 0 <= P <= 56 * MAXB - 54 -> P + 1 <= T -> (T = 4096 \/ T < 2 * (P + 1)) ->
  PresetFlush.ispow T -> 0 <= N -> 0 <= Q -> 0 <= lm ->
  100000 * N + (if 4096 <=? lm then 132930 * lm else 0) <= 132930 * L + 438 * P + 165792 ->
  192 * N + (if 4096 <=? lm then 276 * lm else 0) <= 3 * (93 * L + 99) ->
  zF >= T - (if 4096 <=? lm then 3 * lm else 4096) ->
  zR >= P - 1 - 52 * Z.max 6 lm ->
  457 * Q <= Z.max 0 (QT - zF - zR) ->
  N + Q + 8 <= CAP17.
Proof.
  intros L P T N Q lm zF zR HL HP HT1 HT2 Hp HN HQ Hlm HW HNF HF HR HW8.
  assert (HT : T < 536870912) by (unfold MAXB in HP; lia).
  pose proof (pow_band T Hp HT) as B.
  destruct (4096 <=? lm) eqn:E; [apply Z.leb_le in E|apply Z.leb_gt in E]; band_close B.
Qed.

(* ================================================================ the read-back sites: the weights and the flushes *)

Ltac wcst := apply Z.leb_le; vm_compute; reflexivity.

Lemma leb4096 : forall n, Nat.leb 4096 n = (4096 <=? Z.of_nat n).
Proof.
  intros n. destruct (Nat.leb_spec 4096 n), (Z.leb_spec 4096 (Z.of_nat n)); first [reflexivity | exfalso; lia].
Qed.

(* D3's count under D1's three weights (PresetSite17.wsum_n17) *)
Lemma n17_rt3 : forall u, 20910 * Z.of_nat (n17t u + PresetFlush.nk65 u) + 20910 * Z.of_nat (PresetFlush.nc9 u) +
  (if 4096 <=? Z.of_nat (PresetPiece.lmax u) then 9129 * Z.of_nat (PresetPiece.lmax u) else 0) <=
  PjWeight.wsum PjWeight.W_rt3 u.
Proof.
  intros u. rewrite <- leb4096.
  exact (wsum_n17 PjWeight.W_rt3 20910 20910 ltac:(lia) ltac:(lia) ltac:(wcst) ltac:(wcst) ltac:(wcst) ltac:(wcst)
           ltac:(wcst) ltac:(wcst) u).
Qed.

Lemma n17_rt2b : forall u, 100000 * Z.of_nat (n17t u + PresetFlush.nk65 u) + 100000 * Z.of_nat (PresetFlush.nc9 u) +
  (if 4096 <=? Z.of_nat (PresetPiece.lmax u) then 44310 * Z.of_nat (PresetPiece.lmax u) else 0) <=
  PjWeight.wsum PjWeight.W_rt2b u.
Proof.
  intros u. rewrite <- leb4096.
  exact (wsum_n17 PjWeight.W_rt2b 100000 100000 ltac:(lia) ltac:(lia) ltac:(wcst) ltac:(wcst) ltac:(wcst) ltac:(wcst)
           ltac:(wcst) ltac:(wcst) u).
Qed.

Lemma n17_nf : forall u, 192 * Z.of_nat (n17t u + PresetFlush.nk65 u) + 128 * Z.of_nat (PresetFlush.nc9 u) +
  (if 4096 <=? Z.of_nat (PresetPiece.lmax u) then 92 * Z.of_nat (PresetPiece.lmax u) else 0) <=
  PjWeight.wsum PjWeight.W_nf u.
Proof.
  intros u. rewrite <- leb4096.
  exact (wsum_n17 PjWeight.W_nf 192 128 ltac:(lia) ltac:(lia) ltac:(wcst) ltac:(wcst) ltac:(wcst) ltac:(wcst)
           ltac:(wcst) ltac:(wcst) u).
Qed.

Lemma zsum_fl : forall l, zsum l = PresetFlush.zsum l.
Proof. induction l as [|q l IH]; cbn; [reflexivity|]. unfold PresetFlush.zsum in IH. lia. Qed.

Lemma zsum_le8 : forall l, zsum l <= zsum8 l.
Proof. intros l. unfold zsum8. rewrite zsum_map8. lia. Qed.

Lemma pow76 : forall P, P <= 56 * MAXB -> P + 1 <= 2 ^ 76.
Proof.
  intros P HP. assert (H : 2 ^ 28 <= 2 ^ 76) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 28) with 268435456 in H. unfold MAXB in HP. lia.
Qed.

(* pj_write (u, 1)'s chain frees at least pow4k (P + 1) - 4096 bytes, or - 3 lmax u when a piece is that long *)
Lemma flush_lmax : forall u, PjWriteHyp.wlen u true + 1 <= 2 ^ 76 ->
  PresetFlush.zsum (hfrees (w_evs u true)) >= PresetFlush.pow4k (PjWriteHyp.wlen u true + 1) -
    (if 4096 <=? Z.of_nat (PresetPiece.lmax u) then 3 * Z.of_nat (PresetPiece.lmax u) else 4096).
Proof.
  intros u H76. pose proof (PresetPiece.maxpiece_lmax u true) as Hm.
  destruct (Z.leb_spec 4096 (Z.of_nat (PresetPiece.lmax u))) as [E|E].
  - pose proof (PresetFlush.w_flush_ge u true H76) as G. lia.
  - apply (PresetFlush.w_flush_nopiece u true H76). lia.
Qed.

(* rendered (u, 1)'s chain frees at least P - 1 - 52 max 6 (lmax u) bytes, P <= 56 MAXB *)
Lemma rflush_lmax : forall u, PjWriteHyp.wlen u true <= 56 * MAXB ->
  PresetFlush.zsum (hfrees (r_evs u true)) >= PjWriteHyp.wlen u true - 1 - 52 * Z.max 6 (Z.of_nat (PresetPiece.lmax u)).
Proof.
  intros u HP. pose proof (PresetFlush.r_flush_ge u true) as G. pose proof (PresetPiece.rmaxpiece_lmax u true) as Hm.
  unfold PjWriteHyp.wlen in *. set (P := Z.of_nat (length (wdoc u true))) in *.
  set (M := Z.max 6 (Z.of_nat (PresetPiece.lmax u))) in *.
  assert (HM : 6 <= M) by (unfold M; lia).
  assert (Hlg1 : 1 <= Z.log2 (P + 2)) by (change 1 with (Z.log2 2); apply Z.log2_le_mono; lia).
  assert (Hlg2 : Z.log2 (P + 2) < 28).
  { apply Z.log2_lt_pow2; [lia|]. change (2 ^ 28) with 268435456. unfold MAXB in HP. lia. }
  set (lg := Z.log2 (P + 2)) in *. set (r := PresetFlush.rmaxpiece u true) in *.
  assert (Hrl : r * (lg - 1) <= 26 * M) by nia.
  lia.
Qed.
(* ================================================================ the chains' frees enter the quarantine *)

(* a capacity is replaced only when the text outgrows it, so each freed capacity is at most the text's length *)
Lemma gc_ne : forall ls x c, Forall (fun l => 0 <= l) ls -> grow_calls x c ls <> [] -> c <= x + PresetFlush.zsum ls.
Proof.
  induction ls as [|l ls IH]; intros x c Hl H; cbn [grow_calls] in H; [contradiction|].
  apply Forall_cons_iff in Hl as [H0 Hl]. rewrite PresetFlush.zsum_cons.
  pose proof (PresetFlush.zsum_nonneg ls Hl) as Z0.
  destruct (c <? x + l + 1) eqn:E; cbv beta iota in H.
  - apply Z.ltb_lt in E. lia.
  - pose proof (IH (x + l) c Hl H). lia.
Qed.

Lemma gc_rl_le : forall ls x c, Forall (fun l => 0 <= l) ls ->
  Forall (fun d => d <= x + PresetFlush.zsum ls) (removelast (grow_calls x c ls)).
Proof.
  induction ls as [|l ls IH]; intros x c Hl; cbn [grow_calls]; [constructor|].
  apply Forall_cons_iff in Hl as [H0 Hl]. rewrite PresetFlush.zsum_cons.
  pose proof (PresetFlush.zsum_nonneg ls Hl) as Z0.
  destruct (c <? x + l + 1) eqn:E; cbv beta iota.
  - pose proof (IH (x + l) (newcap c (x + l + 1)) Hl) as IH'.
    pose proof (gc_ne ls (x + l) (newcap c (x + l + 1)) Hl) as NE.
    destruct (grow_calls (x + l) (newcap c (x + l + 1)) ls) as [|g gs] eqn:G; [constructor|].
    rewrite ?G in IH'. rewrite PresetFlush.removelast_cons2. constructor.
    + specialize (NE ltac:(rewrite ?G; discriminate)). cbv beta. lia.
    + eapply Forall_impl; [|exact IH']. intros d Hd. cbv beta in Hd |- *. lia.
  - eapply Forall_impl; [|exact (IH (x + l) c Hl)]. intros d Hd. cbv beta in Hd |- *. lia.
Qed.

Lemma tx_ne : forall ls n cap, Forall (fun l => 0 <= l) ls -> tx_caps n cap ls <> [] -> cap <= n + PresetFlush.zsum ls.
Proof.
  induction ls as [|k ls IH]; intros n cap Hl H; cbn [tx_caps] in H; [contradiction|].
  apply Forall_cons_iff in Hl as [H0 Hl]. rewrite PresetFlush.zsum_cons.
  pose proof (PresetFlush.zsum_nonneg ls Hl) as Z0.
  destruct (cap <? n + k + 1) eqn:E; cbv beta iota in H.
  - apply Z.ltb_lt in E. lia.
  - pose proof (IH (n + k) cap Hl H). lia.
Qed.

Lemma tx_rl_le : forall ls n cap, Forall (fun l => 0 <= l) ls ->
  Forall (fun d => d <= n + PresetFlush.zsum ls) (removelast (tx_caps n cap ls)).
Proof.
  induction ls as [|k ls IH]; intros n cap Hl; cbn [tx_caps]; [constructor|].
  apply Forall_cons_iff in Hl as [H0 Hl]. rewrite PresetFlush.zsum_cons.
  pose proof (PresetFlush.zsum_nonneg ls Hl) as Z0.
  destruct (cap <? n + k + 1) eqn:E; cbv beta iota.
  - pose proof (IH (n + k) ((n + k + 1) * 2) Hl) as IH'.
    pose proof (tx_ne ls (n + k) ((n + k + 1) * 2) Hl) as NE.
    destruct (tx_caps (n + k) ((n + k + 1) * 2) ls) as [|g gs] eqn:G; [constructor|].
    rewrite ?G in IH'. rewrite PresetFlush.removelast_cons2. constructor.
    + specialize (NE ltac:(rewrite ?G; discriminate)). cbv beta. lia.
    + eapply Forall_impl; [|exact IH']. intros d Hd. cbv beta in Hd |- *. lia.
  - eapply Forall_impl; [|exact (IH (n + k) cap Hl)]. intros d Hd. cbv beta in Hd |- *. lia.
Qed.

(* pj_write's chain: every freed capacity (+ HEAD) enters the quarantine when the text and HEAD fit kQuarantineMax *)
Lemma w_chain_small : forall t p, PjWriteHyp.wlen t p + HEAD <= YG00.kQuarantineMax ->
  Forall (fun q => YG00.req_size q <= YG00.kQuarantineMax) (hfrees (w_evs t p)).
Proof.
  intros t p H. rewrite hfrees_w_evs. apply Forall_map. unfold wcaps.
  pose proof (gc_rl_le (piece_lens (wdpieces t p)) 0 0 (PresetFlush.piece_lens_nng _)) as G.
  rewrite PresetFlush.zsum_piece_lens in G. unfold PjWriteHyp.wlen, wdoc in H.
  eapply Forall_impl; [|exact G]. intros d Hd. cbv beta in Hd |- *. apply PresetRunQ.req_size_le. lia.
Qed.

(* rendered ()'s chain: every freed capacity enters the quarantine when the text fits kQuarantineMax *)
Lemma r_chain_small : forall t p, PjWriteHyp.wlen t p <= YG00.kQuarantineMax ->
  Forall (fun q => YG00.req_size q <= YG00.kQuarantineMax) (hfrees (r_evs t p)).
Proof.
  intros t p H. rewrite hfrees_r_evs, PresetFlush.rcaps_eq.
  pose proof (tx_rl_le (PresetFlush.rpieces t p) 0 2 (PresetFlush.rpieces_nng t p)) as G.
  pose proof (PresetFlush.rpieces_len t p) as E. unfold PjWriteHyp.wlen in H.
  destruct (tx_caps 0 2 (PresetFlush.rpieces t p)) as [|g gs] eqn:T; [constructor|].
  rewrite ?T in G. rewrite PresetFlush.removelast_cons2. constructor.
  - cbv beta. apply PresetRunQ.req_size_le. unfold YG00.kQuarantineMax. lia.
  - eapply Forall_impl; [|exact G]. intros d Hd. cbv beta in Hd |- *. apply PresetRunQ.req_size_le. lia.
Qed.

(* ================================================================ the read-back sites *)

Theorem room17_rb : forall sm x os i s H0, Z.of_nat (length x) <= MAXB -> rb_pos sm x os i ->
  (exists d, (length d <= 3)%nat /\ Permutation (rs_live s) (hlive (firstn i (hruns sm x os)) ++ d)) ->
  quar_bytes_ok s -> fifo_ok (map acct_size (H0 ++ PresetRunQ.hfrees_q (firstn i (hruns sm x os)))) (rs_quar s) ->
  room_at s 17.
Proof.
  intros sm x os i s H0 Hx Hrb (d & Hd & Hp) Hq Hf.
  destruct (rt_site17 sm x os i Hrb)
    as (t & t' & k & pre & F & X0 & Ht & Hwf & Hk & Hcase0 & Hh & HFd & HF17 & HX170 & HJ0).
  (* hfrees_q: F (the writer chain of the text read back) and rendered ()'s chain enter the quarantine whole; of the
     read-back parse's frees, X keeps those that enter it *)
  assert (HWt : PjWriteHyp.wlen t' true + HEAD <= YG00.kQuarantineMax).
  { destruct Hcase0 as [(Et & _) | (ms & Etm & Etc & _)].
    - subst t'. pose proof (SlotSizes.wlen_true_read sm x t Ht). unfold MAXB, HEAD, YG00.kQuarantineMax in *. lia.
    - subst t t'. pose proof (SlotSizes.wlen_true_read sm x (JObj ms) Ht).
      pose proof (PresetPiece.wlen_copy_set ms true). unfold MAXB, HEAD, YG00.kQuarantineMax in *. lia. }
  assert (HFs : PresetRunQ.qfilter F = F) by (rewrite HFd; apply PresetRunQ.qfilter_all, w_chain_small; exact HWt).
  pose proof (PresetRunQ.qfilter_filter_le is17 X0) as QL.
  pose proof (Nat.le_trans _ _ _ QL HX170) as HX17.
  pose proof (Nat.le_trans _ _ _ (proj1 (Nat.add_le_mono_l _ _ (cnt is17 (hlive (firstn i (hruns sm x os))))) QL) HJ0) as HJ.
  set (X := PresetRunQ.qfilter X0) in *.
  assert (Hh' : PresetRunQ.hfrees_q (firstn i (hruns sm x os)) = PresetRunQ.qfilter pre ++ F ++ X).
  { unfold X. rewrite PresetRunQ.hfrees_q_eq, Hh, !PresetRunQ.qfilter_app, HFs. reflexivity. }
  assert (Hcase : (t' = t /\ X = hfrees (r_evs t true) ++ PresetRunQ.qfilter (hfrees (firstn k (rd_hevs (ttrace t))))) \/
                  (exists ms, t = JObj ms /\ t' = copy_set ms /\ X = PresetRunQ.qfilter (hfrees (firstn k (rd_hevs (ttrace t')))))).
  { destruct Hcase0 as [(Et & EX0) | (ms & Etm & Etc & EX0)]; [left | right].
    - split; [exact Et|]. unfold X. rewrite EX0, PresetRunQ.qfilter_app, (PresetRunQ.qfilter_all (hfrees (r_evs t true)));
        [reflexivity|].
      apply r_chain_small. subst t'. unfold HEAD in HWt. lia.
    - exists ms. split; [exact Etm|]. split; [exact Etc|]. unfold X. rewrite EX0. reflexivity. }
  clearbody X. clear Hcase0 Hh HX170 HJ0 QL.
  (* the instance's quarantine: the flush lemma over the accounted history H0 ++ qfilter pre ++ F ++ X *)
  pose proof (quar17_flush_raw (H0 ++ PresetRunQ.hfrees_q (firstn i (hruns sm x os))) (rs_quar s) (H0 ++ PresetRunQ.qfilter pre)
                F X Hf (quar_zsum8 s Hq) ltac:(rewrite Hh'; apply app_assoc) HF17) as HQ.
  (* the instance's live chunks: the model's plus the driver's at most 3 *)
  assert (HLv : Z.of_nat (ccnt 17 (rs_live s)) <= Z.of_nat (cnt is17 (hlive (firstn i (hruns sm x os)))) + 3).
  { rewrite (ccnt_perm 17 _ _ Hp), ccnt_app. pose proof (g_ccnt_len 17 d).
    change (ccnt 17 (hlive (firstn i (hruns sm x os)))) with (cnt is17 (hlive (firstn i (hruns sm x os)))). lia. }
  rewrite lo17_eq in HQ.
  assert (HQ0 : 0 <= Z.max 0 (QT - zsum8 F - zsum8 (map acct_size X)) / 457) by (apply Z.div_pos; lia).
  assert (HQ8 : 457 * (Z.max 0 (QT - zsum8 F - zsum8 (map acct_size X)) / 457) <=
                Z.max 0 (QT - zsum8 F - zsum8 (map acct_size X))) by (apply Z.mul_div_le; lia).
  set (Q := Z.max 0 (QT - zsum8 F - zsum8 (map acct_size X)) / 457) in *.
  change (ccnt 17 X) with (length (filter is17 X)) in HQ.
  unfold room_at. rewrite cap17_eq, refill17_eq.
  replace (if 17 =? K_BATCH_CLASS then rs_batches s else 0) with 0 by reflexivity.
  pose proof (zsum_le8 F) as HZF. rewrite zsum_fl in HZF.
  pose proof (zsum8_acct_nonneg X) as HX0.
  destruct Hcase as [(Et & EX) | (ms & Etm & Etc & EX)].
  - (* round trip 2: the doc read back *)
    subst t'.
    pose proof (SlotSizes.wlen_true_read sm x t Ht) as HP.
    assert (HP0 : 0 <= PjWriteHyp.wlen t true) by (unfold PjWriteHyp.wlen; lia).
    pose proof (pow76 (PjWriteHyp.wlen t true) ltac:(lia)) as H76.
    destruct (PresetFlush.winv_first _ HP0 H76) as (_ & HT1 & HT2 & Hpow).
    pose proof (n17_rt2b t) as W1. pose proof (PjWeight.wt_rt2b sm x t Ht) as W2.
    pose proof (n17_nf t) as N1. pose proof (PjWeight.wt_nf sm x t Ht) as N2.
    pose proof (flush_lmax t H76) as HF. rewrite <- HFd in HF.
    pose proof (rflush_lmax t ltac:(lia)) as HR.
    assert (HXR : zsum (hfrees (r_evs t true)) <= zsum8 (map acct_size X)).
    { rewrite EX, map_app, zsum8_app. pose proof (zsum8_acct_nonneg (PresetRunQ.qfilter (hfrees (firstn k (rd_hevs (ttrace t)))))).
      pose proof (zsum8_acct_ge (hfrees (r_evs t true))). pose proof (zsum_le8 (hfrees (r_evs t true))). lia. }
    rewrite zsum_fl in HXR.
    assert (A : Z.of_nat (n17t t + n17t t + n17t t + PresetFlush.nc9 t + PresetFlush.nk65 t) + Q + 8 <= CAP17).
    { destruct (4096 <=? Z.of_nat (PresetPiece.lmax t)) eqn:E; cbv iota in W1, N1, HF;
      (apply (rt2_arith (Z.of_nat (length x)) (PjWriteHyp.wlen t true) (PresetFlush.pow4k (PjWriteHyp.wlen t true + 1))
               _ Q (Z.of_nat (PresetPiece.lmax t)) (zsum8 F) (zsum8 (map acct_size X)));
       rewrite ?E; cbv iota; first [exact Hpow | lia]). }
    lia.
  - (* round trip 3: the copy read back *)
    subst t t'.
    pose proof (SlotSizes.wlen_true_read sm x (JObj ms) Ht) as HPd.
    pose proof (PresetPiece.wlen_copy_set ms true) as HPc.
    assert (HP0 : 0 <= PjWriteHyp.wlen (copy_set ms) true) by (unfold PjWriteHyp.wlen; lia).
    pose proof (pow76 (PjWriteHyp.wlen (copy_set ms) true) ltac:(lia)) as H76.
    destruct (PresetFlush.winv_first _ HP0 H76) as (_ & HT1 & HT2 & Hpow).
    pose proof (n17_rt3 (JObj ms)) as W1. pose proof (n17_rt3 (copy_set ms)) as W1'.
    pose proof (PjWeight.wt_rt3_live2 sm x ms Ht) as W2.
    pose proof (n17_nf (JObj ms)) as N1. pose proof (PjWeight.wt_nf sm x (JObj ms) Ht) as N2.
    pose proof (n17t_copy_set ms) as C1. pose proof (PresetPiece.nc9_copy_set ms) as C2.
    pose proof (PresetPiece.nk65_copy_set ms) as C3. pose proof (PresetPiece.lmax_copy_set ms) as C4.
    change (Nat.max (length MOD_KEY) (length MOD_VAL)) with 20%nat in C4.
    pose proof (flush_lmax (copy_set ms) H76) as HF. rewrite <- HFd in HF.
    assert (A : Z.of_nat (n17t (JObj ms) + n17t (JObj ms) + n17t (copy_set ms) + PresetFlush.nc9 (copy_set ms) +
                          PresetFlush.nk65 (copy_set ms)) + Q + 8 <= CAP17).
    { destruct (4096 <=? Z.of_nat (PresetPiece.lmax (copy_set ms))) eqn:E;
      destruct (4096 <=? Z.of_nat (PresetPiece.lmax (JObj ms))) eqn:E2;
      cbv iota in W1, W1', N1, HF;
      (apply (rt3_arith (Z.of_nat (length x)) (PjWriteHyp.wlen (copy_set ms) true)
               (PresetFlush.pow4k (PjWriteHyp.wlen (copy_set ms) true + 1)) _ Q
               (Z.of_nat (PresetPiece.lmax (copy_set ms))) (zsum8 F + zsum8 (map acct_size X)));
       rewrite ?E; cbv iota; try apply Z.leb_le in E; try apply Z.leb_gt in E;
       try apply Z.leb_le in E2; try apply Z.leb_gt in E2; first [exact Hpow | lia]). }
    lia.
Qed.

(* ================================================================ every consumer allocation *)

Lemma room_at_dec : forall s c, {room_at s c} + {~ room_at s c}.
Proof. intros s c. unfold room_at. apply Z_le_dec. Qed.

(* THE CLASS-17 ROOM: at every consumer allocation of the harness model, the instance's state (its live chunks the
   model's plus at most 3 of the driver's; its quarantine quar_bytes_ok, a FIFO window of its accounted free history,
   which ends with the model's frees) has a free class-17 slot *)
Theorem room17 : forall sm x os i s H0, Z.of_nat (length x) <= MAXB ->
  nth i (hcons sm x os) false = true -> alloc_at (hruns sm x os) i ->
  (exists d, (length d <= 3)%nat /\ Permutation (rs_live s) (hlive (firstn i (hruns sm x os)) ++ d)) ->
  quar_bytes_ok s -> fifo_ok (map acct_size (H0 ++ PresetRunQ.hfrees_q (firstn i (hruns sm x os)))) (rs_quar s) ->
  room_at s 17.
Proof.
  intros sm x os i s H0 Hx Hc Ha Hd Hq Hf.
  destruct (room_at_dec s 17) as [R|R]; [exact R|exfalso].
  assert (Hn : ~ rb_pos sm x os i) by (intros Hrb; exact (R (room17_rb sm x os i s H0 Hx Hrb Hd Hq Hf))).
  apply R, room_at_of_room_ok; [exact Hq|].
  pose proof (room17_other sm x os i Hx Hc Ha Hn) as G.
  destruct Hd as (d & Hdl & Hp). apply (g_room_mono 17 _ _ G).
  rewrite (ccnt_perm 17 _ _ Hp), ccnt_app. pose proof (g_ccnt_len 17 d).
  change (ccnt 17 (hlive (firstn i (hruns sm x os)))) with (cnt (in_cls 17) (hlive (firstn i (hruns sm x os)))).
  unfold DRV. lia.
Qed.
