From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel pcap_source_struct
  pcap_source_struct_next.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require Import PWalkDef.
Import ListNotations.
Open Scope Z_scope.

(* The reader's record chain (psn_chain) against the slot's walk over the file: the chain from a position
   passes exactly the records of skips, and the output of the slot is the concatenation of the chain outputs
   of the walk's calls (walk_out, OUT). This file needs no machine files. *)

Lemma pw_fb_range : forall F i, 0 <= fb F i < 256.
Proof.
  intros F i. unfold fb. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) F (Z_to_bv 8 0))) as R.
  unfold bv_modulus in R. exact R.
Qed.

Lemma pw_hw_range : forall sw F q j, 0 <= hw sw F q j < 2 ^ 32.
Proof.
  intros sw F q j. pose proof (pw_fb_range F (q + j)). pose proof (pw_fb_range F (q + j + 1)).
  pose proof (pw_fb_range F (q + j + 2)). pose proof (pw_fb_range F (q + j + 3)).
  unfold hw, w32le. destruct sw; lia.
Qed.

Lemma pw_chain_empty : forall sw F cap f q lh, kind sw F cap q = KEmpty ->
  chain sw F cap (S f) q lh = chain sw F cap f (q + 16) lh.
Proof. intros sw F cap f q lh K. cbn [chain]. rewrite K. reflexivity. Qed.

Lemma pw_chain_big : forall sw F cap f q lh, kind sw F cap q = KBig ->
  chain sw F cap (S f) q lh =
  (fst (fst (chain sw F cap f (q + 16 + incl sw F q) (Some q))),
   snd (fst (chain sw F cap f (q + 16 + incl sw F q) (Some q))),
   snd (chain sw F cap f (q + 16 + incl sw F q) (Some q))).
Proof.
  intros sw F cap f q lh K. cbn [chain]. rewrite K.
  destruct (chain sw F cap f (q + 16 + incl sw F q) (Some q)) as [[Q o] l]. reflexivity.
Qed.

Section Walk.
Variables (sw : bool) (F : list byte) (cap : Z).

Lemma incl_nonneg : forall q, 0 <= incl sw F q.
Proof. intros q. unfold incl. pose proof (pw_hw_range sw F q 8). lia. Qed.

Lemma kind_cuth : forall q, flen F < q -> kind sw F cap q = KCutH.
Proof.
  intros q H. unfold kind.
  destruct (Z.eqb_spec (flen F - q) 0); [exfalso; lia|].
  destruct (Z.ltb_spec (flen F - q) 16); [reflexivity | exfalso; lia].
Qed.

Lemma chain_ge : forall f q lh, q <= fst (fst (chain sw F cap f q lh)).
Proof.
  induction f as [|f IH]; intros q lh; [cbn; lia|].
  destruct (kind sw F cap q) eqn:K.
  all: try (cbn [chain]; rewrite K; cbn [fst]; lia).
  - rewrite (pw_chain_empty sw F cap f q lh K). specialize (IH (q + 16) lh). lia.
  - rewrite (pw_chain_big sw F cap f q lh K). cbn [fst].
    specialize (IH (q + 16 + incl sw F q) (Some q)). pose proof (incl_nonneg q). lia.
Qed.

(* Each step of the chain moves at least 16 bytes and only while 16 bytes remain, so fuel f with
   flen - q < 16 * f is enough from q. *)
Lemma chain_fuel : forall f q lh, flen F - q < 16 * Z.of_nat f ->
  chain sw F cap (S f) q lh = chain sw F cap f q lh.
Proof.
  induction f as [|f IH]; intros q lh H.
  - cbn [chain]. rewrite kind_cuth by lia. reflexivity.
  - destruct (kind sw F cap q) eqn:K.
    all: try (cbn [chain]; rewrite K; reflexivity).
    + rewrite (pw_chain_empty sw F cap (S f) q lh K), (pw_chain_empty sw F cap f q lh K). apply IH. lia.
    + rewrite (pw_chain_big sw F cap (S f) q lh K), (pw_chain_big sw F cap f q lh K).
      pose proof (incl_nonneg q). rewrite (IH (q + 16 + incl sw F q) (Some q)) by lia. reflexivity.
Qed.

Lemma chain_fuel_le : forall k f q lh, flen F - q < 16 * Z.of_nat f ->
  chain sw F cap (k + f) q lh = chain sw F cap f q lh.
Proof.
  induction k as [|k IH]; intros f q lh H; [reflexivity|].
  cbn [Nat.add]. rewrite chain_fuel by lia. apply IH. exact H.
Qed.

Lemma chain_skips : forall f q lh, flen F - q < 16 * Z.of_nat f ->
  skips sw F cap q (fst (fst (chain sw F cap f q lh))).
Proof.
  induction f as [|f IH]; intros q lh H.
  - cbn [chain fst]. apply skips_stop; rewrite kind_cuth by lia; discriminate.
  - destruct (kind sw F cap q) eqn:K.
    all: try (cbn [chain]; rewrite K; cbn [fst]; apply skips_stop; rewrite K; discriminate).
    + rewrite (pw_chain_empty sw F cap f q lh K). apply skips_empty; [exact K|]. apply IH. lia.
    + rewrite (pw_chain_big sw F cap f q lh K). cbn [fst]. apply skips_big; [exact K|].
      pose proof (incl_nonneg q). apply IH. lia.
Qed.

Lemma chain_fit : forall f q lh, flen F - q < 16 * Z.of_nat f ->
  kind sw F cap (fst (fst (chain sw F cap f q lh))) = KFit ->
  snd (chain sw F cap f q lh) = Some (fst (fst (chain sw F cap f q lh))).
Proof.
  induction f as [|f IH]; intros q lh H HK.
  - cbn [chain fst] in HK. rewrite kind_cuth in HK by lia. discriminate.
  - destruct (kind sw F cap q) eqn:K.
    all: try (cbn [chain] in HK |- *; rewrite K in HK; rewrite K; cbn [fst snd] in HK |- *;
              first [reflexivity | rewrite K in HK; discriminate]).
    + rewrite (pw_chain_empty sw F cap f q lh K) in HK |- *. apply IH; [lia | exact HK].
    + rewrite (pw_chain_big sw F cap f q lh K) in HK |- *. cbn [fst snd] in HK |- *.
      pose proof (incl_nonneg q). apply IH; [lia | exact HK].
Qed.

Lemma psn_q_ge : forall p, p <= psn_q sw F cap p.
Proof. intros p. apply chain_ge. Qed.

(* W1 *)
Lemma psn_q_skips : forall p, 0 <= p -> skips sw F cap p (psn_q sw F cap p).
Proof. intros p Hp. unfold psn_q, psn_chain. apply chain_skips. unfold flen. lia. Qed.

(* W2 *)
Lemma skips_le : forall q Q, skips sw F cap q Q -> q <= Q.
Proof.
  intros q Q H. induction H as [q _ _|q Q _ _ IH|q Q _ _ IH]; [lia | lia |].
  pose proof (incl_nonneg q). lia.
Qed.

(* The three ways a skips derivation can start at q. *)
Lemma skips_exit : forall q Q, skips sw F cap q Q -> kind sw F cap q <> KEmpty -> kind sw F cap q <> KBig -> Q = q.
Proof. intros q Q H K1 K2. inversion H; subst; first [reflexivity | congruence]. Qed.

Lemma skips_empty_inv : forall q Q, skips sw F cap q Q -> kind sw F cap q = KEmpty -> skips sw F cap (q + 16) Q.
Proof. intros q Q H K. inversion H; subst; first [assumption | congruence]. Qed.

Lemma skips_big_inv : forall q Q, skips sw F cap q Q -> kind sw F cap q = KBig ->
  skips sw F cap (q + 16 + incl sw F q) Q.
Proof. intros q Q H K. inversion H; subst; first [assumption | congruence]. Qed.

(* W3 *)
Lemma psn_lh_fit : forall p, 0 <= p -> kind sw F cap (psn_q sw F cap p) = KFit ->
  psn_lh sw F cap p = Some (psn_q sw F cap p).
Proof. intros p Hp HK. unfold psn_lh, psn_q, psn_chain in *. apply chain_fit; [unfold flen; lia | exact HK]. Qed.

Lemma lol_of_fit : forall p lol, 0 <= p -> kind sw F cap (psn_q sw F cap p) = KFit ->
  lol_of sw F (psn_lh sw F cap p) lol = wz (orig sw F (psn_q sw F cap p)).
Proof. intros p lol Hp HK. rewrite psn_lh_fit by assumption. reflexivity. Qed.

Lemma vt_of_fit : forall Q lvt, kind sw F cap Q = KFit ->
  vt_of sw F cap Q lvt = (if tagged sw F Q then wz 1 else wz 0).
Proof. intros Q lvt HK. unfold vt_of. rewrite HK. reflexivity. Qed.

Lemma vid_of_fit : forall Q lvid, kind sw F cap Q = KFit ->
  vid_of sw F cap Q lvid = (if tagged sw F Q then wz (rec_vid F Q) else wz 0).
Proof. intros Q lvid HK. unfold vid_of. rewrite HK. reflexivity. Qed.

Lemma ts_of_fit : forall Q tsv, kind sw F cap Q = KFit -> ts_of sw F cap Q tsv = wz (rec_ts sw F Q).
Proof. intros Q tsv HK. unfold ts_of. rewrite HK. reflexivity. Qed.

(* W4 *)
Lemma kind_fit : forall Q, kind sw F cap Q = KFit ->
  res_of sw F cap Q = rec_len sw F Q /\ 0 < rec_len sw F Q <= cap /\
  pos_of sw F cap Q = Q + 16 + incl sw F Q /\ Q + 16 + incl sw F Q <= flen F /\ 1 <= incl sw F Q <= cap.
Proof.
  intros Q K.
  assert (H : incl sw F Q <> 0 /\ incl sw F Q <= cap /\ Q + 16 + incl sw F Q <= flen F).
  { unfold kind in K.
    destruct (Z.eqb_spec (flen F - Q) 0); [discriminate|].
    destruct (Z.ltb_spec (flen F - Q) 16); [discriminate|].
    destruct (Z.eqb_spec (incl sw F Q) 0); [discriminate|].
    destruct (Z.leb_spec (incl sw F Q) cap);
      [|destruct (cap =? 0); [|destruct (Q + 16 + incl sw F Q <=? flen F)]; discriminate].
    destruct (Z.leb_spec (Q + 16 + incl sw F Q) (flen F)); [|discriminate]. repeat split; assumption. }
  destruct H as (H0 & H1 & H2). pose proof (incl_nonneg Q) as HI.
  unfold res_of, pos_of. rewrite K.
  assert (HR : 0 < rec_len sw F Q <= cap).
  { unfold rec_len. destruct (tagged sw F Q) eqn:T; [|lia].
    unfold tagged in T. apply andb_prop in T as [T _]. apply andb_prop in T as [T _].
    apply Z.leb_le in T. lia. }
  split; [reflexivity|]. split; [exact HR|]. split; [reflexivity|]. split; [exact H2|]. lia.
Qed.

Lemma kind_nfit : forall Q, kind sw F cap Q <> KFit ->
  res_of sw F cap Q = want_of sw F cap Q /\ (res_of sw F cap Q = 0 \/ res_of sw F cap Q = -1).
Proof.
  intros Q K. unfold res_of, want_of.
  destruct (kind sw F cap Q); try (exfalso; apply K; reflexivity);
    (split; [reflexivity | first [left; reflexivity | right; reflexivity]]).
Qed.

Lemma psn_out_past : forall p, flen F < p -> snd (fst (psn_chain sw F cap p)) = [].
Proof. intros p H. unfold psn_chain. cbn [chain]. rewrite kind_cuth by lia. reflexivity. Qed.

End Walk.

Lemma is_fit_true : forall k, is_fit k = true -> k = KFit.
Proof. intros k H. destruct k; try discriminate H. reflexivity. Qed.

(* W5: the output of the walk's calls of pcap_source_next from file position p: each call outputs the
   chain's messages, and the walk goes on after a fit record. *)
Fixpoint walk_out (fuel : nat) (sw : bool) (F : list byte) (cap p : Z) : list byte :=
  match fuel with
  | O => []
  | S k =>
      let Q := psn_q sw F cap p in
      snd (fst (psn_chain sw F cap p)) ++
      (if is_fit (kind sw F cap Q) then walk_out k sw F cap (pos_of sw F cap Q) else [])
  end.

Definition OUT (pl : list byte) : list byte :=
  if 2 ^ 26 <=? Z.of_nat (length pl) then []
  else match pl with
       | [] => []
       | d :: F =>
           if pcap_good F then
             let sw := (pcap_sw F =? 1) in
             let cap := 8 * bv_unsigned d in
             walk_out (S (length F)) sw F cap 24 ++ snd (fst (psn_chain sw F cap 24))
           else []
       end.

Lemma OUT_big : forall pl, 2 ^ 26 <= Z.of_nat (length pl) -> OUT pl = [].
Proof. intros pl H. unfold OUT. rewrite (proj2 (Z.leb_le _ _) H). reflexivity. Qed.

Lemma OUT_cons : forall d F, Z.of_nat (length (d :: F)) < 2 ^ 26 ->
  OUT (d :: F) =
  if pcap_good F then
    walk_out (S (length F)) (pcap_sw F =? 1) F (8 * bv_unsigned d) 24 ++
    snd (fst (psn_chain (pcap_sw F =? 1) F (8 * bv_unsigned d) 24))
  else [].
Proof. intros d F H. unfold OUT. rewrite (proj2 (Z.leb_gt _ _) H). reflexivity. Qed.

Lemma walk_out_S : forall k sw F cap p,
  walk_out (S k) sw F cap p =
  snd (fst (psn_chain sw F cap p)) ++
  (if is_fit (kind sw F cap (psn_q sw F cap p)) then walk_out k sw F cap (pos_of sw F cap (psn_q sw F cap p))
   else []).
Proof. reflexivity. Qed.

(* A fit record moves the walk by 16 + incl >= 17 bytes, and past the end of the file a call outputs
   nothing, so fuel f with flen - p < 17 * f is enough from p. *)
Lemma walk_fuel : forall f sw F cap p, flen F - p < 17 * Z.of_nat f ->
  walk_out (S f) sw F cap p = walk_out f sw F cap p.
Proof.
  induction f as [|f IH]; intros sw F cap p H.
  - rewrite walk_out_S. rewrite psn_out_past by lia. cbn [walk_out].
    destruct (is_fit (kind sw F cap (psn_q sw F cap p))); reflexivity.
  - rewrite (walk_out_S (S f) sw F cap p), (walk_out_S f sw F cap p).
    destruct (is_fit (kind sw F cap (psn_q sw F cap p))) eqn:K; [|reflexivity].
    apply is_fit_true in K. f_equal. apply IH.
    destruct (kind_fit sw F cap _ K) as (_ & _ & EP & _ & HI).
    pose proof (psn_q_ge sw F cap p). rewrite EP. lia.
Qed.

Lemma walk_fuel_le : forall k f sw F cap p, flen F - p < 17 * Z.of_nat f ->
  walk_out (k + f) sw F cap p = walk_out f sw F cap p.
Proof.
  induction k as [|k IH]; intros f sw F cap p H; [reflexivity|].
  cbn [Nat.add]. rewrite walk_fuel by lia. apply IH. exact H.
Qed.

Lemma walk_unfold : forall f sw F cap p, flen F - p < 17 * Z.of_nat f ->
  walk_out f sw F cap p =
  snd (fst (psn_chain sw F cap p)) ++
  (if is_fit (kind sw F cap (psn_q sw F cap p)) then walk_out f sw F cap (pos_of sw F cap (psn_q sw F cap p))
   else []).
Proof. intros f sw F cap p H. rewrite <- (walk_fuel f sw F cap p H). apply walk_out_S. Qed.

(* The fuel of OUT is enough from every position p >= 0. *)
Lemma walk_unfold_len : forall sw F cap p, 0 <= p ->
  walk_out (S (length F)) sw F cap p =
  snd (fst (psn_chain sw F cap p)) ++
  (if is_fit (kind sw F cap (psn_q sw F cap p))
   then walk_out (S (length F)) sw F cap (pos_of sw F cap (psn_q sw F cap p)) else []).
Proof. intros sw F cap p Hp. apply walk_unfold. unfold flen. lia. Qed.

Lemma walk_pos_step : forall sw F cap p i, 24 + 17 * i <= p ->
  kind sw F cap (psn_q sw F cap p) = KFit ->
  24 + 17 * (i + 1) <= pos_of sw F cap (psn_q sw F cap p).
Proof.
  intros sw F cap p i H K. destruct (kind_fit sw F cap _ K) as (_ & _ & EP & _ & HI).
  pose proof (psn_q_ge sw F cap p). rewrite EP. lia.
Qed.
