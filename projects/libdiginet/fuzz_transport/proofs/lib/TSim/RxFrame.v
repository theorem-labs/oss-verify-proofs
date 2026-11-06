(* m_rx (FT:283) reads the heap frame with spec_read_frame over its first n bytes; diginet_session_rx (DS:268)
   parses the n bytes it is handed, rxbuf fr n. L1 says the two reads agree; this file states the consequences
   the rx simulation uses: the fields, the MACs the filters compare (FT:285-297 / DS:273-291), and the body. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links RxDefs RxBase RxList.
Import ListNotations.
Open Scope Z_scope.

Lemma rx_length_rxbuf : forall fr n, 0 <= n <= Z.of_nat (length (tf_bytes fr)) ->
  length (rxbuf fr n) = Z.to_nat n.
Proof. intros fr n H. unfold rxbuf. rewrite length_firstn. lia. Qed.

(* the parse fails on both sides together *)
Lemma rx_frame_bad : forall (HL : links) fr n, 0 <= n <= Z.of_nat (length (tf_bytes fr)) ->
  fr_code (rxbuf fr n) <> DIGINET_OK -> sf_code (spec_read_frame (zs (tf_bytes fr)) n) <> SPEC_OK.
Proof.
  intros HL fr n Hn Hc E. destruct HL as [L1 _]. destruct (L1 (tf_bytes fr) n Hn) as [[_ H] _].
  apply Hc. exact (H E).
Qed.

(* an accepted parse: the fields, the MACs and the body, read on either side *)
Record rx_frame_facts (fr : tframe) (n : Z) : Prop := {
  rf_code : sf_code (spec_read_frame (zs (tf_bytes fr)) n) = SPEC_OK;
  rf_src : sf_src (spec_read_frame (zs (tf_bytes fr)) n) = 6;
  rf_dst : sf_dst (spec_read_frame (zs (tf_bytes fr)) n) = 0;
  rf_cmd : sf_cmd (spec_read_frame (zs (tf_bytes fr)) n) = fr_cmd (rxbuf fr n);
  rf_send : sf_send (spec_read_frame (zs (tf_bytes fr)) n) = fr_send (rxbuf fr n);
  rf_ack : sf_ack (spec_read_frame (zs (tf_bytes fr)) n) = fr_ack (rxbuf fr n);
  rf_retry : sf_retry (spec_read_frame (zs (tf_bytes fr)) n) = fr_retry (rxbuf fr n);
  rf_body : sf_body (spec_read_frame (zs (tf_bytes fr)) n) = 30;
  rf_body_len : sf_body_len (spec_read_frame (zs (tf_bytes fr)) n) = fr_body_len (rxbuf fr n);
  rf_src_bytes : sub (tf_bytes fr) 6 6 = fr_src (rxbuf fr n);
  rf_dst_bytes : sub (tf_bytes fr) 0 6 = fr_dst (rxbuf fr n);
  rf_src_len : length (fr_src (rxbuf fr n)) = 6%nat;
  rf_dst_len : length (fr_dst (rxbuf fr n)) = 6%nat;
  rf_blen : 0 <= fr_body_len (rxbuf fr n) /\ 30 + fr_body_len (rxbuf fr n) <= n;
  rf_body_bytes : firstn (Z.to_nat (fr_body_len (rxbuf fr n))) (skipn 30 (tf_bytes fr)) = fr_body (rxbuf fr n);
  rf_body_length : length (fr_body (rxbuf fr n)) = Z.to_nat (fr_body_len (rxbuf fr n));
}.

Lemma rx_frame_ok : forall (HL : links) fr n, 0 <= n <= Z.of_nat (length (tf_bytes fr)) ->
  fr_code (rxbuf fr n) = DIGINET_OK -> rx_frame_facts fr n.
Proof.
  intros HL fr n Hn Hc. pose proof HL as [L1 _]. destruct (L1 (tf_bytes fr) n Hn) as [[H1 _] H2].
  fold (rxbuf fr n) in H1, H2. specialize (H1 Hc). specialize (H2 Hc).
  destruct H2 as (Hdst & Hsrc & Hcmd & Hsend & Hack & Hretry & Hncmds & Hbody & Hblen & _).
  pose proof (fr_body_len_ok _ Hc) as (B0 & P0 & Ln). rewrite rx_length_rxbuf in Ln by exact Hn.
  pose proof (fr_code_ok _ Hc) as (L30 & _). rewrite rx_length_rxbuf in L30 by exact Hn.
  constructor; try assumption.
  - unfold sub, fr_src, rxbuf. rewrite rx_firstn_skipn_firstn by lia. reflexivity.
  - unfold sub, fr_dst, rxbuf. change (skipn (Z.to_nat 0) (tf_bytes fr)) with (skipn 0 (tf_bytes fr)).
    rewrite skipn_O, firstn_firstn, Nat.min_l by lia. reflexivity.
  - unfold fr_src. rewrite length_firstn, length_skipn. pose proof (rx_length_rxbuf fr n Hn). lia.
  - unfold fr_dst. rewrite length_firstn. pose proof (rx_length_rxbuf fr n Hn). lia.
  - lia.
  - unfold fr_body. set (bl := fr_body_len (rxbuf fr n)) in *. clearbody bl. unfold rxbuf.
    rewrite rx_firstn_skipn_firstn by lia. reflexivity.
  - apply length_fr_body. exact Hc.
Qed.

(* the filters' MAC compares: the library's memeq against the model's beq_bytes (A2: S_cfg_host_mac = HOST) *)
Lemma rx_memeq_src : forall fr n mac, 0 <= n <= Z.of_nat (length (tf_bytes fr)) ->
  fr_code (rxbuf fr n) = DIGINET_OK -> length mac = 6%nat ->
  memeq 6 (fr_src (rxbuf fr n)) mac = beq_bytes (fr_src (rxbuf fr n)) mac.
Proof.
  intros fr n mac Hn Hc Hm. apply memeq6_beq; [|exact Hm].
  pose proof (fr_code_ok _ Hc) as (L30 & _). unfold fr_src. rewrite length_firstn, length_skipn. lia.
Qed.

Lemma rx_memeq_dst : forall fr n mac, 0 <= n <= Z.of_nat (length (tf_bytes fr)) ->
  fr_code (rxbuf fr n) = DIGINET_OK -> length mac = 6%nat ->
  memeq 6 (fr_dst (rxbuf fr n)) mac = beq_bytes (fr_dst (rxbuf fr n)) mac.
Proof.
  intros fr n mac Hn Hc Hm. apply memeq6_beq; [|exact Hm].
  pose proof (fr_code_ok _ Hc) as (L30 & _). unfold fr_dst. rewrite length_firstn. lia.
Qed.

Lemma rx_broadcast : BROADCAST = SPEC_BCAST.
Proof. reflexivity. Qed.

Lemma rx_oui : forall (HL : links) fr n, 0 <= n <= Z.of_nat (length (tf_bytes fr)) ->
  fr_code (rxbuf fr n) = DIGINET_OK ->
  oui_of (fr_src (rxbuf fr n)) = beq_bytes (firstn 3 (fr_src (rxbuf fr n))) SPEC_OUI.
Proof.
  intros HL fr n Hn Hc. destruct HL as (_ & _ & _ & _ & _ & [_ L6] & _).
  assert (Hl : (3 <= length (fr_src (rxbuf fr n)))%nat).
  { pose proof (fr_code_ok _ Hc) as (L30 & _). unfold fr_src. rewrite length_firstn, length_skipn. lia. }
  specialize (L6 _ Hl). destruct (oui_of _), (beq_bytes _ _); try reflexivity.
  - symmetry. apply L6. reflexivity.
  - apply L6. reflexivity.
Qed.
