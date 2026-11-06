(* Segment B2 of the op_write arm: the two facts about the model that the checks need.
   check_write compares the library's code with the model's on whole registers, so the codes must
   be small enough for the 64-bit words to tell them apart: every code the library can answer lies
   in [-2 ^ 31, 2 ^ 31). check_requests compares the fake kernel's request list with the model's,
   so equal lists plus the two well-formedness bounds give `requests_are`. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import
  PropExec MState Mem Cells Exec Frame Step Tac Bytes Arr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC1B2Lib.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. A four-byte read of a chunk
   ========================================================================== *)

Lemma c1b2_rd32_rng : forall c off, 0 <= rd32 c off < 2 ^ 32.
Proof.
  intros c off. unfold rd32, rdn.
  split; [apply bytes_le_to_Z_nonneg|].
  pose proof (bytes_le_to_Z_bound (slice c off 4)) as B.
  assert (L : (length (slice c off 4) <= 4)%nat).
  { unfold slice. rewrite length_firstn. change (Z.to_nat 4) with 4%nat. lia. }
  eapply Z.lt_le_trans; [exact B|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma c1b2_rd32s_rng : forall c off, - 2 ^ 31 <= rd32s c off < 2 ^ 31.
Proof.
  intros c off. unfold rd32s. cbv zeta. pose proof (c1b2_rd32_rng c off) as H.
  destruct (Z.ltb_spec (rd32 c off) (2 ^ 31)); lia.
Qed.

(* ==========================================================================
   2. The netlink walk answers a small code
   ========================================================================== *)

Definition c1b2_nlv_ok (v : nlv) : Prop :=
  match v with NlErr code => - 2 ^ 31 <= code < 2 ^ 31 | _ => True end.

Lemma c1b2_msg_rng : forall f c off left, c1b2_nlv_ok (msg_scan f c off left).
Proof.
  induction f as [|f IH]; intros c off left; [exact I|].
  cbn [msg_scan]. cbv zeta.
  destruct (left <? NL_HDR); [exact I|].
  destruct ((rd32 c off <? NL_HDR) || (left <? rd32 c off)); [exact I|].
  destruct (rd16 c (off + 4) =? NL_ERROR).
  - destruct (rd32 c off <? NL_HDR + NL_ERR_BODY); [exact I|].
    unfold c1b2_nlv_ok. apply c1b2_rd32s_rng.
  - destruct (rd16 c (off + 4) =? RTM_NEWLINK); [exact I|]. apply IH.
Qed.

Lemma c1b2_loop_rng : forall f cs i, c1b2_nlv_ok (fst (chunk_loop f cs i)).
Proof.
  induction f as [|f IH]; intros cs i; [exact I|].
  cbn [chunk_loop]. destruct (nth_error cs i) as [c|]; [|exact I].
  destruct (chunk_walk c) eqn:E; cbn [fst]; try exact I.
  - apply IH.
  - pose proof (c1b2_msg_rng (S (length c)) c 0 (Z.of_nat (length c))) as H.
    unfold chunk_walk in E. rewrite E in H. exact H.
Qed.

Lemma c1b2_talk_rng : forall K,
  0 <= k_sock K < 2 ^ 31 -> 0 <= k_send K < 2 ^ 31 -> 0 <= k_end K < 2 ^ 31 ->
  - 2 ^ 31 <= talk_rc_lib K < 2 ^ 31.
Proof.
  intros K Hs Hd He. unfold talk_rc_lib, talk_core.
  destruct (negb (k_sock K =? 0)); [cbn [fst]; lia|].
  destruct (negb (k_send K =? 0)); [cbn [fst]; lia|].
  pose proof (c1b2_loop_rng (S (length (k_chunks K))) (k_chunks K) (k_next K)) as H.
  destruct (chunk_loop (S (length (k_chunks K))) (k_chunks K) (k_next K)) as [v j].
  cbn [fst] in H. cbv zeta.
  destruct v; cbn [fst]; unfold E_IO; unfold c1b2_nlv_ok in H; lia.
Qed.

Lemma c1b2_kst_rng : forall kbs, nlk_wf kbs ->
  0 <= k_sock (nk_kstate kbs) < 2 ^ 31 /\ 0 <= k_send (nk_kstate kbs) < 2 ^ 31 /\
  0 <= k_end (nk_kstate kbs) < 2 ^ 31.
Proof.
  intros kbs H. unfold nk_kstate. cbn [k_sock k_send k_end].
  unfold nlk_wf in H. repeat split; lia.
Qed.

(* ==========================================================================
   3. Every code the library answers for a write is small
   ========================================================================== *)

Lemma c1b2_wrc_rng : forall tab nm al reqs K,
  0 <= k_sock K < 2 ^ 31 -> 0 <= k_send K < 2 ^ 31 -> 0 <= k_end K < 2 ^ 31 ->
  - 2 ^ 31 <= w_rc (write_core tab nm al reqs K) < 2 ^ 31.
Proof.
  intros tab nm al reqs K Hs Hd He. unfold write_core.
  destruct nm as [s|]; [|cbn [w_rc]; unfold E_INVAL; lia].
  destruct al as [a|]; [|cbn [w_rc]; unfold E_INVAL; lia].
  destruct (Nat.eqb (length s) 0); [cbn [w_rc]; unfold E_INVAL; lia|].
  destruct (ALIAS_MAX <=? Z.of_nat (length a)); [cbn [w_rc]; unfold E_NAMETOOLONG; lia|].
  cbv zeta. destruct (index_of tab s =? 0); [cbn [w_rc]; unfold E_NODEV; lia|].
  cbv zeta. cbn [w_rc]. apply c1b2_talk_rng; assumption.
Qed.

(* ==========================================================================
   4. same_rc, read on whole registers
   ========================================================================== *)

Lemma c1b2_same_rc_vals : forall got, - 2 ^ 31 <= got < 2 ^ 31 ->
  (wz (norm_rc got) = wz RC_FAILS -> wz got <> wz 0)
  /\ (wz (norm_rc got) <> wz RC_FAILS -> wz got = wz (norm_rc got)).
Proof.
  intros got H. unfold norm_rc, RC_FAILS.
  destruct (Z.ltb_spec 0 got) as [Hp|Hn]; cbv beta iota.
  - split.
    + intros _. apply c1b2_wz_ne; lia.
    + intros Hne. exfalso. apply Hne. reflexivity.
  - split.
    + intros HE. exfalso. apply c1b2_wz_mod in HE.
      rewrite (Z.mod_small 1000000) in HE by lia.
      revert HE. Z.div_mod_to_equations. lia.
    + intros _. reflexivity.
Qed.

(* ==========================================================================
   5. The request lists
   ========================================================================== *)

Lemma c1b2_sent_nil : forall kbs, nk_n_sent kbs = 0 -> nk_sent kbs = [].
Proof. intros kbs H. unfold nk_sent. rewrite H. reflexivity. Qed.

Lemma c1b2_nth_map_seq : forall (A : Type) (f : nat -> A) n k (d : A), (k < n)%nat ->
  nth k (map f (seq 0 n)) d = f k.
Proof.
  intros A f n k d Hk.
  rewrite (nth_indep _ _ (f 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite (map_nth f (seq 0 n) 0%nat k). f_equal.
  rewrite seq_nth by lia. reflexivity.
Qed.

Lemma c1b2_requests_are : forall kbs mbs,
  nlk_wf kbs -> model_wf mbs ->
  Z.of_nat (length kbs) = NK_SIZE -> Z.of_nat (length mbs) = MD_SIZE ->
  nk_n_sent kbs = md_n_req mbs -> nk_sent kbs = md_reqs mbs ->
  requests_are kbs mbs.
Proof.
  intros kbs mbs HK HM LK LM HN HL. split; [exact HN|]. intros i Hi.
  unfold nlk_wf in HK. destruct HK as (_ & _ & HKN & _ & _ & _ & _ & _ & _ & _ & _ & _ & HKB).
  unfold model_wf in HM. destruct HM as (_ & _ & _ & _ & HMB & _).
  pose proof (HKB i Hi) as BK. pose proof (HMB i ltac:(lia)) as BM.
  (* the two slices are the same list *)
  assert (HE : nk_sent_one kbs i = md_req_one mbs i).
  { assert (K1 : nth (Z.to_nat i) (nk_sent kbs) nil = nk_sent_one kbs i).
    { unfold nk_sent.
      rewrite (c1b2_nth_map_seq _ _ (Z.to_nat (nk_n_sent kbs)) (Z.to_nat i) nil ltac:(lia)).
      rewrite Z2Nat.id by lia. reflexivity. }
    assert (K2 : nth (Z.to_nat i) (md_reqs mbs) nil = md_req_one mbs i).
    { unfold md_reqs.
      rewrite (c1b2_nth_map_seq _ _ (Z.to_nat (md_n_req mbs)) (Z.to_nat i) nil ltac:(lia)).
      rewrite Z2Nat.id by lia. reflexivity. }
    rewrite <- K1, <- K2, HL. reflexivity. }
  split; [|exact HE].
  assert (LK1 : length (nk_sent_one kbs i) = Z.to_nat (fld_u64 kbs (NK_SENT_LEN + 8 * i))).
  { unfold nk_sent_one. apply c1b2_slice_len; unfold NK_SENT, NL_SENT_LEN, NK_SIZE, NL_SENT_MAX in *; lia. }
  assert (LM1 : length (md_req_one mbs i) = Z.to_nat (fld_u64 mbs (MD_REQ_LEN + 8 * i))).
  { unfold md_req_one. apply c1b2_slice_len; unfold MD_REQ, NL_SENT_LEN, MD_SIZE, NL_SENT_MAX in *; lia. }
  rewrite HE in LK1. rewrite LM1 in LK1. lia.
Qed.
