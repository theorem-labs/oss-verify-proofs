(* Arm c2 (op_mark), piece HEAD: the byte lists model_begin (fuzz_link.c:668-675, 0x13d50 - 0x13d6c) leaves.
   It copies the fake kernel's two failure errnos into the model block (md+0, md+4), clears the model's
   cursor (md+8) and its request count (md+8336), and clears g_nl.n_sent (g_nl+271016). c2h_mbs and
   c2h_kbs are the two blocks after those five 4-byte stores; the lemmas read their fields. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC2Defs LC2HeadA.
Local Open Scope Z_scope.

Definition c2h_mbs (mbs : list byte) (v0 v1 : word) : list byte :=
  upd_bytes (upd_bytes (upd_bytes (upd_bytes mbs (Z.to_nat 0) (le4 v0)) (Z.to_nat 8) (le4 (Z_to_bv 64 0)))
                       (Z.to_nat 4) (le4 v1))
            (Z.to_nat 8336) (le4 (Z_to_bv 64 0)).

Definition c2h_kbs (kbs : list byte) : list byte := upd_bytes kbs (Z.to_nat 271016) (le4 (Z_to_bv 64 0)).

(* lw then sw keeps the 32 bits *)
Lemma c2h_sx32_low : forall x, bv_unsigned (sx32 (Z_to_bv 64 x)) mod 2 ^ 32 = x mod 2 ^ 32.
Proof.
  intros x. unfold sx32. rewrite !unsigned_lit_wrap.
  unfold bv_swrap. change (bv_half_modulus 32) with 2147483648. unfold bv_wrap. change (bv_modulus 32) with 4294967296.
  Z.div_mod_to_equations. lia.
Qed.

Lemma c2h_upd_fld_other : forall bs k xs off, (k + length xs <= length bs)%nat -> 0 <= off ->
  (off + 4 <= Z.of_nat k \/ Z.of_nat k + Z.of_nat (length xs) <= off) ->
  fld_u32 (upd_bytes bs k xs) off = fld_u32 bs off.
Proof. intros bs k xs off H1 H2 H3. unfold fld_u32. apply c2h_rdn_upd_other; [exact H1 | exact H2 | lia | exact H3]. Qed.

Lemma c2h_upd_fld64_other : forall bs k xs off, (k + length xs <= length bs)%nat -> 0 <= off ->
  (off + 8 <= Z.of_nat k \/ Z.of_nat k + Z.of_nat (length xs) <= off) ->
  fld_u64 (upd_bytes bs k xs) off = fld_u64 bs off.
Proof. intros bs k xs off H1 H2 H3. unfold fld_u64. apply c2h_rdn_upd_other; [exact H1 | exact H2 | lia | exact H3]. Qed.

Lemma c2h_zero32 : bv_unsigned (Z_to_bv 64 0) mod 2 ^ 32 = 0.
Proof. reflexivity. Qed.

(* ==========================================================================
   g_nl after `sw zero, 0x2a8(a0)` (n_sent := 0)
   ========================================================================== *)

Lemma c2h_kbs_facts : forall kbs, Z.of_nat (length kbs) = NK_SIZE -> nlk_wf kbs ->
  Z.of_nat (length (c2h_kbs kbs)) = NK_SIZE /\ nlk_wf (c2h_kbs kbs) /\ nk_n_sent (c2h_kbs kbs) = 0 /\
  nk_next (c2h_kbs kbs) = nk_next kbs /\ nk_open (c2h_kbs kbs) = nk_open kbs /\
  nk_opened (c2h_kbs kbs) = nk_opened kbs /\ nk_closed (c2h_kbs kbs) = nk_closed kbs /\
  nk_misuse (c2h_kbs kbs) = nk_misuse kbs /\ nk_n_if (c2h_kbs kbs) = nk_n_if kbs /\
  nk_socket_errno (c2h_kbs kbs) = nk_socket_errno kbs /\ nk_send_errno (c2h_kbs kbs) = nk_send_errno kbs.
Proof.
  intros kbs HL HW. unfold NK_SIZE in HL.
  assert (L4 : forall v : word, (Z.to_nat 271016 + length (le4 v) <= length kbs)%nat)
    by (intros v; rewrite length_le4; lia).
  assert (FO : forall off, 0 <= off -> off + 4 <= 271016 \/ 271020 <= off -> fld_u32 (c2h_kbs kbs) off = fld_u32 kbs off).
  { intros off H0 H1. unfold c2h_kbs. apply c2h_upd_fld_other; [apply L4 | exact H0 |]. rewrite length_le4. lia. }
  assert (F8 : forall off, 0 <= off -> off + 8 <= 271016 -> fld_u64 (c2h_kbs kbs) off = fld_u64 kbs off).
  { intros off H0 H1. unfold c2h_kbs. apply c2h_upd_fld64_other; [apply L4 | exact H0 |]. lia. }
  assert (NS : nk_n_sent (c2h_kbs kbs) = 0).
  { unfold nk_n_sent, c2h_kbs, NK_N_SENT.
    pose proof (c2h_fld_u32_upd_same kbs (Z.to_nat 271016) (Z_to_bv 64 0) ltac:(lia)) as X.
    rewrite Z2Nat.id in X by lia. rewrite X. exact c2h_zero32. }
  assert (EC : nk_n_chunks (c2h_kbs kbs) = nk_n_chunks kbs) by (unfold nk_n_chunks; apply FO; unfold NK_N_CHUNKS; lia).
  assert (EX : nk_next (c2h_kbs kbs) = nk_next kbs) by (unfold nk_next; apply FO; unfold NK_NEXT; lia).
  assert (EI : nk_n_if (c2h_kbs kbs) = nk_n_if kbs) by (unfold nk_n_if; apply FO; unfold NK_N_IF; lia).
  assert (EO : nk_open (c2h_kbs kbs) = nk_open kbs) by (unfold nk_open; apply FO; unfold NK_OPEN; lia).
  assert (EOD : nk_opened (c2h_kbs kbs) = nk_opened kbs) by (unfold nk_opened; apply FO; unfold NK_OPENED; lia).
  assert (ECL : nk_closed (c2h_kbs kbs) = nk_closed kbs) by (unfold nk_closed; apply FO; unfold NK_CLOSED; lia).
  assert (EM : nk_misuse (c2h_kbs kbs) = nk_misuse kbs) by (unfold nk_misuse; apply FO; unfold NK_MISUSE; lia).
  assert (EE : nk_end_errno (c2h_kbs kbs) = nk_end_errno kbs)
    by (unfold nk_end_errno; apply FO; unfold NK_END_ERRNO; lia).
  assert (ES : nk_socket_errno (c2h_kbs kbs) = nk_socket_errno kbs)
    by (unfold nk_socket_errno; apply FO; unfold NK_SOCKET_ERRNO; lia).
  assert (ED : nk_send_errno (c2h_kbs kbs) = nk_send_errno kbs)
    by (unfold nk_send_errno; apply FO; unfold NK_SEND_ERRNO; lia).
  split; [unfold c2h_kbs; rewrite upd_bytes_length by (apply L4); unfold NK_SIZE; lia|].
  split.
  - destruct HW as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13).
    unfold nlk_wf. rewrite EC, EX, NS, EI, EO, EOD, ECL, EM, EE, ES, ED.
    split; [exact W1|]. split; [exact W2|]. split; [unfold NL_SENT_MAX; lia|]. split; [exact W4|].
    split; [exact W5|]. split; [exact W6|]. split; [exact W7|]. split; [exact W8|]. split; [exact W9|].
    split; [exact W10|]. split; [exact W11|]. split.
    + intros j Hj. rewrite F8 by (unfold NK_CHUNK_LEN, NL_CHUNKS in *; lia).
      exact (W12 j Hj).
    + intros j Hj. lia.
  - split; [exact NS|]. split; [exact EX|]. split; [exact EO|]. split; [exact EOD|]. split; [exact ECL|].
    split; [exact EM|]. split; [exact EI|]. split; [exact ES | exact ED].
Qed.

(* ==========================================================================
   The model block after the four stores of model_begin
   ========================================================================== *)

Lemma c2h_mbs_facts : forall mbs gbs (v0 v1 : word) se de,
  Z.of_nat (length mbs) = MD_SIZE -> model_wf mbs -> marks_are gbs mbs ->
  0 <= se < 2 ^ 31 -> 0 <= de < 2 ^ 31 ->
  bv_unsigned v0 mod 2 ^ 32 = se -> bv_unsigned v1 mod 2 ^ 32 = de ->
  Z.of_nat (length (c2h_mbs mbs v0 v1)) = MD_SIZE /\ model_wf (c2h_mbs mbs v0 v1) /\
  marks_are gbs (c2h_mbs mbs v0 v1) /\
  md_socket_errno (c2h_mbs mbs v0 v1) = se /\ md_send_errno (c2h_mbs mbs v0 v1) = de /\
  md_next (c2h_mbs mbs v0 v1) = 0 /\ md_n_req (c2h_mbs mbs v0 v1) = 0.
Proof.
  intros mbs gbs v0 v1 se de HL HW HA Hse Hde E0 E1. unfold MD_SIZE in HL. unfold c2h_mbs.
  set (b1 := upd_bytes mbs (Z.to_nat 0) (le4 v0)).
  set (b2 := upd_bytes b1 (Z.to_nat 8) (le4 (Z_to_bv 64 0))).
  set (b3 := upd_bytes b2 (Z.to_nat 4) (le4 v1)).
  set (b4 := upd_bytes b3 (Z.to_nat 8336) (le4 (Z_to_bv 64 0))).
  assert (L1 : length b1 = length mbs) by (unfold b1; apply upd_bytes_length; rewrite length_le4; lia).
  assert (L2 : length b2 = length mbs)
    by (unfold b2; rewrite upd_bytes_length; [exact L1 | rewrite length_le4, L1; lia]).
  assert (L3 : length b3 = length mbs)
    by (unfold b3; rewrite upd_bytes_length; [exact L2 | rewrite length_le4, L2; lia]).
  assert (L4 : length b4 = length mbs)
    by (unfold b4; rewrite upd_bytes_length; [exact L3 | rewrite length_le4, L3; lia]).
  assert (SL : forall off n, 8340 <= off -> 0 <= n -> slice b4 off n = slice mbs off n).
  { intros off n H1 H2.
    unfold b4. rewrite c2h_slice_upd_other by (rewrite ?length_le4, ?L3; lia).
    unfold b3. rewrite c2h_slice_upd_other by (rewrite ?length_le4, ?L2; lia).
    unfold b2. rewrite c2h_slice_upd_other by (rewrite ?length_le4, ?L1; lia).
    unfold b1. rewrite c2h_slice_upd_other by (rewrite ?length_le4; lia). reflexivity. }
  assert (F0 : fld_u32 b4 0 = se).
  { unfold b4. rewrite c2h_upd_fld_other by (rewrite ?length_le4, ?L3; lia).
    unfold b3. rewrite c2h_upd_fld_other by (rewrite ?length_le4, ?L2; lia).
    unfold b2. rewrite c2h_upd_fld_other by (rewrite ?length_le4, ?L1; lia).
    unfold b1. pose proof (c2h_fld_u32_upd_same mbs (Z.to_nat 0) v0 ltac:(lia)) as X.
    change (Z.of_nat (Z.to_nat 0)) with 0 in X. rewrite X. exact E0. }
  assert (F4 : fld_u32 b4 4 = de).
  { unfold b4. rewrite c2h_upd_fld_other by (rewrite ?length_le4, ?L3; lia).
    unfold b3. pose proof (c2h_fld_u32_upd_same b2 (Z.to_nat 4) v1 ltac:(rewrite L2; lia)) as X.
    change (Z.of_nat (Z.to_nat 4)) with 4 in X. rewrite X. exact E1. }
  assert (F8 : fld_u32 b4 8 = 0).
  { unfold b4. rewrite c2h_upd_fld_other by (rewrite ?length_le4, ?L3; lia).
    unfold b3. rewrite c2h_upd_fld_other by (rewrite ?length_le4, ?L2; lia).
    unfold b2. pose proof (c2h_fld_u32_upd_same b1 (Z.to_nat 8) (Z_to_bv 64 0) ltac:(rewrite L1; lia)) as X.
    change (Z.of_nat (Z.to_nat 8)) with 8 in X. rewrite X. exact c2h_zero32. }
  assert (FN : fld_u32 b4 8336 = 0).
  { unfold b4. pose proof (c2h_fld_u32_upd_same b3 (Z.to_nat 8336) (Z_to_bv 64 0) ltac:(rewrite L3; lia)) as X.
    rewrite Z2Nat.id in X by lia. rewrite X. exact c2h_zero32. }
  assert (FM : md_n_mark b4 = md_n_mark mbs).
  { unfold md_n_mark, fld_u32, link_spec.rdn, MD_N_MARK. rewrite SL by lia. reflexivity. }
  assert (MM : md_marks b4 = md_marks mbs).
  { unfold md_marks. rewrite FM. apply map_ext. intros j. unfold MD_MARK, MARK_LEN. rewrite SL by lia. reflexivity. }
  assert (MW : model_marks_wf b4).
  { destruct HW as (_ & _ & _ & _ & _ & (W1 & W2)). split; [rewrite FM; exact W1|].
    intros j Hj. rewrite FM in Hj. unfold MD_MARK, MARK_LEN in *. rewrite SL by lia. exact (W2 j Hj). }
  assert (NR : md_n_req b4 = 0) by (unfold md_n_req, MD_N_REQ; exact FN).
  split; [rewrite L4; exact HL|].
  split.
  { split; [rewrite NR; unfold NL_SENT_MAX; lia|].
    split; [unfold md_next, MD_NEXT; rewrite F8; lia|].
    split; [unfold md_socket_errno, MD_SOCKET_ERRNO; rewrite F0; lia|].
    split; [unfold md_send_errno, MD_SEND_ERRNO; rewrite F4; lia|].
    split; [intros j Hj; rewrite NR in Hj; lia|].
    exact MW. }
  split.
  { destruct HA as [A1 A2]. split; [rewrite FM; exact A1 | rewrite MM; exact A2]. }
  split; [unfold md_socket_errno, MD_SOCKET_ERRNO; exact F0|].
  split; [unfold md_send_errno, MD_SEND_ERRNO; exact F4|].
  split; [unfold md_next, MD_NEXT; exact F8 | exact NR].
Qed.
