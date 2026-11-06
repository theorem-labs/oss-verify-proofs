(* Case 6 of the op loop, 0x13a64-0x13b24 and the shared tail 0x13c4c-0x13c50 (fuzz_transport.c:1197-1202
   `case 6: op_begin(); m_close(); diginet_session_close(&g_s, g_now); settle(0); break;`): the two memsets of
   op_begin, m_close inline (its three tests and m_set's event record), then the two calls. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import memset_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract
  diginet_session_close_c settle_c LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr.
Import ListNotations.
Open Scope Z_scope.

(* a 32-bit field against a small literal, as the zified branch states it *)
Lemma op6_s32_eq : forall x c, -2^31 <= x < 2^31 -> 0 <= c < 2^31 ->
  (x mod 18446744073709551616 = c <-> x = c).
Proof.
  intros x c Hx Hc. split; intros E; [|subst; apply Z.mod_small; lia].
  destruct (Z_le_gt_dec 0 x) as [P|N]; [rewrite Z.mod_small in E by lia; lia|].
  rewrite <- (Z.mod_add x 1 18446744073709551616) in E by lia. rewrite Z.mod_small in E by lia. lia.
Qed.

(* writing a span and reading a field inside it: the field is the span's bytes *)
Lemma op6_sub_upd_in : forall (bs v : list byte) k i (n : nat), 0 <= k -> 0 <= i ->
  (Z.to_nat i + n <= length v)%nat -> k + Z.of_nat (length v) <= Z.of_nat (length bs) ->
  sub (upd bs k v) (k + i) n = sub v i n.
Proof.
  intros bs v k i n Hk Hi Hn Hl. apply nth_error_ext. intros j.
  destruct (Nat.lt_ge_cases j n) as [Hj|Hj].
  - rewrite !ne_sub by lia. rewrite ne_upd by lia.
    replace (Z.to_nat (k + i) + j - Z.to_nat k)%nat with (Z.to_nat i + j)%nat by lia.
    destruct ((Z.to_nat k <=? Z.to_nat (k + i) + j) && (Z.to_nat (k + i) + j <? Z.to_nat k + length v))%nat
      eqn:C; [reflexivity|].
    exfalso. apply andb_false_iff in C. destruct C as [C|C];
      [apply Nat.leb_gt in C | apply Nat.ltb_ge in C]; lia.
  - assert (A1 : nth_error (sub (upd bs k v) (k + i) n) j = None)
      by (apply nth_error_None; unfold sub; rewrite length_firstn, length_skipn; lia).
    assert (A2 : nth_error (sub v i n) j = None)
      by (apply nth_error_None; unfold sub; rewrite length_firstn, length_skipn; lia).
    rewrite A1, A2. reflexivity.
Qed.

(* a field inside a span of equal bytes *)
Lemma op6_sub_repeat : forall (z : byte) (N : nat) i (n : nat), 0 <= i -> (Z.to_nat i + n <= N)%nat ->
  sub (repeat z N) i n = repeat z n.
Proof.
  intros z N i n Hi Hn. apply nth_error_ext. intros j.
  destruct (Nat.lt_ge_cases j n) as [Hj|Hj].
  - rewrite ne_sub by lia. rewrite !nth_error_repeat by lia.
    destruct (Nat.ltb_spec j n); [reflexivity | lia].
  - assert (A1 : nth_error (sub (repeat z N) i n) j = None)
      by (apply nth_error_None; unfold sub; rewrite length_firstn, length_skipn, repeat_length; lia).
    assert (A2 : nth_error (repeat z n) j = None)
      by (apply nth_error_None; rewrite repeat_length; lia).
    rewrite A1, A2. reflexivity.
Qed.

(* list surgery, as Prog/T/m_wake.v states it: writing v ++ w is writing v then w *)
Lemma op6_firstn_app_add : forall (l1 l2 : list byte) n, firstn (length l1 + n) (l1 ++ l2) = l1 ++ firstn n l2.
Proof. induction l1 as [|x l1 IH]; intros l2 n; cbn; [reflexivity | f_equal; apply IH]. Qed.

Lemma op6_skipn_app_add : forall (l1 l2 : list byte) n, skipn (length l1 + n) (l1 ++ l2) = skipn n l2.
Proof. induction l1 as [|x l1 IH]; intros l2 n; cbn; [reflexivity | apply IH]. Qed.

Lemma op6_firstn_app_self : forall (l1 l2 : list byte), firstn (length l1) (l1 ++ l2) = l1.
Proof. induction l1 as [|x l1 IH]; intros l2; cbn; [reflexivity | f_equal; apply IH]. Qed.

Lemma op6_upd_app : forall (bs v w : list byte) k,
  0 <= k -> (Z.to_nat k + length v <= length bs)%nat ->
  upd bs k (v ++ w) = upd (upd bs k v) (k + Z.of_nat (length v)) w.
Proof.
  intros bs v w k Hk Hl.
  assert (LL : length (firstn (Z.to_nat k) bs) = Z.to_nat k) by (rewrite length_firstn; lia).
  unfold upd. rewrite length_app.
  replace (Z.to_nat (k + Z.of_nat (length v))) with (Z.to_nat k + length v)%nat by lia.
  replace (Z.to_nat k + length v)%nat with (length (firstn (Z.to_nat k) bs) + length v)%nat by lia.
  rewrite op6_firstn_app_add, op6_firstn_app_self.
  replace (length (firstn (Z.to_nat k) bs) + length v + length w)%nat
    with (length (firstn (Z.to_nat k) bs) + (length v + length w))%nat by lia.
  rewrite op6_skipn_app_add, op6_skipn_app_add, skipn_skipn.
  replace (length w + (length (firstn (Z.to_nat k) bs) + length v))%nat
    with (Z.to_nat k + (length v + length w))%nat by lia.
  rewrite <- !app_assoc. reflexivity.
Qed.

(* a write that misses g_fail_next leaves it *)
Lemma op6_fn_upd : forall (Bx v : list byte) k, 0 <= k ->
  k + Z.of_nat (length v) <= Z.of_nat (length Bx) ->
  (k + Z.of_nat (length v) <= OFF_g_fail_next \/ OFF_g_fail_next + 1 <= k) ->
  g_fail_next (upd Bx k v) = g_fail_next Bx.
Proof.
  intros Bx v k Hk Hl Hd. unfold g_fail_next.
  rewrite u_at_upd_out; [reflexivity | lia | unfold OFF_g_fail_next; lia | cbn [Z.of_nat]; lia | lia].
Qed.

(* a put-write inside the world keeps its length *)
Lemma op6_len_put : forall (u : list byte) k n v, Z.of_nat (length u) = W_LEN -> 0 <= k ->
  k + Z.of_nat n <= W_LEN -> Z.of_nat (length (upd u k (put n v))) = W_LEN.
Proof. intros u k n v Hu Hk Hn. rewrite length_upd_put; [exact Hu | lia | rewrite Hu; lia]. Qed.

(* a put-write that misses g_fail_next leaves it *)
Lemma op6_fn_put : forall (u : list byte) k n v, Z.of_nat (length u) = W_LEN -> 0 <= k ->
  k + Z.of_nat n <= W_LEN -> (k + Z.of_nat n <= OFF_g_fail_next \/ OFF_g_fail_next + 1 <= k) ->
  g_fail_next (upd u k (put n v)) = g_fail_next u.
Proof. intros u k n v Hu Hk Hn Hd. apply op6_fn_upd; rewrite ?length_put; [lia | rewrite Hu; lia | lia]. Qed.

(* m_set's record misses g_fail_next (OW is at 0xff20, M.state at 12, g_fail_next at 0xfdc8) *)
Lemma op6_fn_mset : forall (Bx : list byte) st, Z.of_nat (length Bx) = W_LEN ->
  g_fail_next (set_M_state (set_OW_n (set_OW_t_reason (set_OW_t_old (set_OW_t_state Bx 0 3) 0 st) 0 8) 1) 3)
  = g_fail_next Bx.
Proof.
  intros Bx st HL.
  assert (EOW : OFF_OW = 65312) by reflexivity.
  assert (EWL : W_LEN = 65616) by reflexivity.
  assert (EFN : OFF_g_fail_next = 64968) by reflexivity.
  assert (EM : OFF_M = 0) by reflexivity.
  assert (LP : forall (u : list byte) k n v, Z.of_nat (length u) = W_LEN -> 0 <= k -> k + Z.of_nat n <= W_LEN ->
                 Z.of_nat (length (upd u k (put n v))) = W_LEN).
  { intros u k n v Hu Hk Hn. rewrite length_upd_put; [exact Hu | lia | rewrite Hu; lia]. }
  assert (FP : forall (u : list byte) k n v, Z.of_nat (length u) = W_LEN -> 0 <= k -> k + Z.of_nat n <= W_LEN ->
                 (k + Z.of_nat n <= OFF_g_fail_next \/ OFF_g_fail_next + 1 <= k) ->
                 g_fail_next (upd u k (put n v)) = g_fail_next u).
  { intros u k n v Hu Hk Hn Hd. apply op6_fn_upd; rewrite ?length_put; [lia | rewrite Hu; lia | lia]. }
  unfold set_M_state, set_OW_n, set_OW_t_reason, set_OW_t_old, set_OW_t_state,
         A_OW_t_state, A_OW_t_old, A_OW_t_reason, A_OW_n, A_M_state.
  assert (L1 : Z.of_nat (length (upd Bx (OFF_OW + 4 + 12 * 0 + 0) (put 4 3))) = W_LEN)
    by (apply LP; [exact HL | lia | cbn [Z.of_nat]; lia]).
  assert (L2 : Z.of_nat (length (upd (upd Bx (OFF_OW + 4 + 12 * 0 + 0) (put 4 3))
                                     (OFF_OW + 4 + 12 * 0 + 4) (put 4 st))) = W_LEN)
    by (apply LP; [exact L1 | lia | cbn [Z.of_nat]; lia]).
  assert (L3 : Z.of_nat (length (upd (upd (upd Bx (OFF_OW + 4 + 12 * 0 + 0) (put 4 3))
                                          (OFF_OW + 4 + 12 * 0 + 4) (put 4 st))
                                     (OFF_OW + 4 + 12 * 0 + 8) (put 4 8))) = W_LEN)
    by (apply LP; [exact L2 | lia | cbn [Z.of_nat]; lia]).
  assert (L4 : Z.of_nat (length (upd (upd (upd (upd Bx (OFF_OW + 4 + 12 * 0 + 0) (put 4 3))
                                               (OFF_OW + 4 + 12 * 0 + 4) (put 4 st))
                                          (OFF_OW + 4 + 12 * 0 + 8) (put 4 8))
                                     (OFF_OW + 0) (put 4 1))) = W_LEN)
    by (apply LP; [exact L3 | lia | cbn [Z.of_nat]; lia]).
  rewrite (FP _ _ _ _ L4) by (cbn [Z.of_nat]; lia).
  rewrite (FP _ _ _ _ L3) by (cbn [Z.of_nat]; lia).
  rewrite (FP _ _ _ _ L2) by (cbn [Z.of_nat]; lia).
  rewrite (FP _ _ _ _ L1) by (cbn [Z.of_nat]; lia).
  rewrite (FP _ _ _ _ HL) by (cbn [Z.of_nat]; lia).
  reflexivity.
Qed.

(* op_begin (fuzz_transport.c:388-394): the machine writes M.fail before OW.desk_off, the model after; the two
   spans are disjoint, and OW.desk_off's write does not move g_fail_next. *)
Lemma op6_begin_world : forall (Bx Bz : list byte), Z.of_nat (length Bx) = W_LEN ->
  Bz = upd (upd Bx 65312 (repeat (Z_to_bv 8 0) 304)) 65084 (repeat (Z_to_bv 8 0) 224) ->
  op_begin_m Bx = Some (upd (upd Bz 88 (put 4 (u_at Bz OFF_g_fail_next 1))) 65544 (put 4 (-1)), tt).
Proof.
  intros Bx Bz HL EZ.
  assert (EWL : W_LEN = 65616) by reflexivity.
  assert (R304 : Z.of_nat (length (repeat (Z_to_bv 8 0) 304)) = 304) by (rewrite repeat_length; lia).
  assert (R224 : Z.of_nat (length (repeat (Z_to_bv 8 0) 224)) = 224) by (rewrite repeat_length; lia).
  assert (P4 : forall v : Z, Z.of_nat (length (put 4 v)) = 4) by (intros; rewrite length_put; lia).
  assert (L1 : Z.of_nat (length (upd Bx 65312 (repeat (Z_to_bv 8 0) 304))) = W_LEN)
    by (rewrite length_upd; [exact HL | lia | rewrite R304; lia]).
  assert (LZ : Z.of_nat (length Bz) = W_LEN)
    by (rewrite EZ, length_upd; [exact L1 | lia | rewrite R224, L1; lia]).
  unfold op_begin_m, set_M_fail, set_OW_desk_off, A_M_fail, A_OW_desk_off, OFF_M, OFF_OW, OFF_GOT.
  change (Z.to_nat SZ_OW) with 304%nat. change (Z.to_nat SZ_GOT) with 224%nat.
  change (b8 0) with (Z_to_bv 8 0).
  rewrite <- EZ.
  replace (65312 + 232) with 65544 by lia. replace (0 + 88) with 88 by lia.
  assert (EFN : g_fail_next (upd Bz 65544 (put 4 (-1))) = u_at Bz OFF_g_fail_next 1).
  { change (u_at Bz OFF_g_fail_next 1) with (g_fail_next Bz).
    apply op6_fn_upd; [lia | rewrite P4, LZ; lia | rewrite P4; unfold OFF_g_fail_next; lia]. }
  rewrite EFN. f_equal. f_equal.
  apply upd_upd_comm; rewrite ?P4, ?LZ; lia.
Qed.

(* the 8-byte store of OW.n = 1 and OW.t[0].state = 3 is the model's two 4-byte writes *)
Lemma op6_put8_13 : put 8 12884901889 = put 4 1 ++ put 4 3.
Proof. apply bytes_eq_of_zs. vm_compute. reflexivity. Qed.

(* m_set's event record: the machine writes OW.n and OW.t[0].state in one 8-byte store (0x13af0-0x13afc),
   the model in two 4-byte writes, and it writes OW.n last. *)
Lemma op6_mset_world : forall (Bx : list byte) st, Z.of_nat (length Bx) = W_LEN ->
  upd (upd (upd (upd Bx 65312 (put 8 12884901889)) 65320 (put 4 st)) 65324 (put 4 8)) 12 (put 4 3)
  = set_M_state (set_OW_n (set_OW_t_reason (set_OW_t_old (set_OW_t_state Bx 0 3) 0 st) 0 8) 1) 3.
Proof.
  intros Bx st HL.
  assert (EOWa : OFF_OW = 65312) by reflexivity.
  assert (EMa : OFF_M = 0) by reflexivity.
  unfold set_M_state, set_OW_n, set_OW_t_reason, set_OW_t_old, set_OW_t_state,
         A_OW_t_state, A_OW_t_old, A_OW_t_reason, A_OW_n, A_M_state.
  rewrite EOWa, EMa.
  replace (65312 + 4 + 12 * 0 + 0) with 65316 by lia.
  replace (65312 + 4 + 12 * 0 + 4) with 65320 by lia.
  replace (65312 + 4 + 12 * 0 + 8) with 65324 by lia.
  replace (65312 + 0) with 65312 by lia.
  replace (0 + 12) with 12 by lia.
  assert (EOW : OFF_OW = 65312) by reflexivity.
  assert (EWL : W_LEN = 65616) by reflexivity.
  assert (EMS : A_M_state = 12) by reflexivity.
  assert (P4 : forall v : Z, Z.of_nat (length (put 4 v)) = 4) by (intros; rewrite length_put; lia).
  assert (L1 : Z.of_nat (length (upd Bx 65316 (put 4 3))) = W_LEN).
  { rewrite length_upd; [exact HL | lia | rewrite P4; lia]. }
  assert (L2 : Z.of_nat (length (upd (upd Bx 65316 (put 4 3)) 65320 (put 4 st))) = W_LEN).
  { rewrite length_upd; [exact L1 | lia | rewrite P4, L1; lia]. }
  assert (L3 : Z.of_nat (length (upd (upd (upd Bx 65316 (put 4 3)) 65320 (put 4 st))
                                     65324 (put 4 8))) = W_LEN).
  { rewrite length_upd; [exact L2 | lia | rewrite P4, L2; lia]. }
  f_equal.
  rewrite (upd_upd_comm _ (put 4 8) (put 4 1) 65324 65312)
    by (rewrite ?P4, ?L1, ?L2, ?L3; lia).
  rewrite (upd_upd_comm _ (put 4 st) (put 4 1) 65320 65312)
    by (rewrite ?P4, ?L1, ?L2, ?L3; lia).
  rewrite (upd_upd_comm _ (put 4 3) (put 4 1) 65316 65312)
    by (rewrite ?P4, ?L1, ?L2, ?L3; lia).
  f_equal. f_equal.
  rewrite op6_put8_13.
  rewrite (op6_upd_app Bx (put 4 1) (put 4 3) 65312) by (rewrite ?length_put; lia).
  replace (65312 + Z.of_nat (length (put 4 1))) with 65316 by (rewrite P4; lia).
  reflexivity.
Qed.

(* m_set (fuzz_transport.c:196-207) at a fresh event log (OW.n = 0) and a state other than CLOSED: one record *)
Lemma op6_mset_model : forall X, OW_n X = 0 -> M_state X <> S_CLOSED ->
  m_set_m X S_CLOSED R_CLOSED =
  Some (set_M_state (set_OW_n (set_OW_t_reason (set_OW_t_old (set_OW_t_state X 0 3) 0 (M_state X)) 0 8) 1) 3,
        tt).
Proof.
  intros X Hn Hs. unfold m_set_m.
  destruct (Z.eqb_spec (M_state X) S_CLOSED) as [E|_]; [contradiction|].
  rewrite Hn. reflexivity.
Qed.

(* m_set at the state it sets: nothing *)
Lemma op6_mset_closed : forall X, M_state X = S_CLOSED -> m_set_m X S_CLOSED R_CLOSED = Some (X, tt).
Proof. intros X Hs. unfold m_set_m. rewrite Hs, Z.eqb_refl. reflexivity. Qed.

(* a 4-byte field read after a put-write that misses it *)
Lemma op6_s32_put : forall (u : list byte) k n v k', Z.of_nat (length u) = W_LEN -> 0 <= k -> 0 <= k' ->
  k + Z.of_nat n <= W_LEN -> (k' + 4 <= k \/ k + Z.of_nat n <= k') ->
  s32_at (upd u k (put n v)) k' = s32_at u k'.
Proof. intros u k n v k' Hu Hk Hk' Hn Hd. apply s32_at_upd_out; rewrite ?length_put; lia. Qed.

Section OP6.
Context (data : Z) (D : list byte).

(* 0x13b10-0x13b24 and the shared tail 0x13c4c-0x13c50: diginet_session_close(&g_s, g_now), settle(0), the latch.
   At 0x13b10 only the saved registers and the world are live. *)
Lemma llvm_op6_tail : forall Sp lo ops c c1 B2 B3 B4 rr
    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q m0 m j10 j28
    gp tp q0 q1 q2 q3 q4 q5 q6 q7 r8 e0 e1 e2 e3 e4 e5 e6 rz,
  diginet_session_close_contract -> settle_contract ->
  llvm_mem data D Sp lo B2 m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 ->
  llvm_cursor D c1 -> 0 <= ops < OPS_MAX ->
  diginet_session_close_m timg_plain None B2 (g_now B2) = Some (B3, rr) ->
  settle_m B3 0 = Some (B4, tt) ->
  (forall ms', llvm_latch data D m0 gp tp Sp lo ops c1 B4
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q
    (MS (mkR rz (Z_to_bv 64 Sp) gp tp e0 e1 e2 r8 (Z_to_bv 64 7) q0 q1 q2 q3 q4 q5 q6 q7
             (Z_to_bv 64 0x39) (Z_to_bv 64 (data + fi_off c1)) (Z_to_bv 64 (data + fi_off c))
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) (Z_to_bv 64 (fi_n c1)) (Z_to_bv 64 (fi_n c))
             (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) e3 e4 e5 e6)
        F (Z_to_bv 64 0x13b10) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo ops c c1 B2 B3 B4 rr ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q m0 m j10 j28
    gp tp q0 q1 q2 q3 q4 q5 q6 q7 r8 e0 e1 e2 e3 e4 e5 e6 rz DSC STC HM HC1 HOPS HB3 HB4 HK.
  pose proof HM as HM0. unfold llvm_mem in HM.
  destruct HM as (_ & _ & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HJ1 & HJ2 & HRW).
  pose proof (wm_len _ _ _ _ HWM) as LB.
  assert (LBz : Z.of_nat (length B2) = W_LEN) by (rewrite LB, Z2Nat.id; [reflexivity | unfold W_LEN; lia]).
  unfold LLVM_LOOP_K in HLO. unfold LLVM_FRAME in HSP2.
  wk_facts. wk_eq_fact OFF_g_fail_next. wk_eq_fact OFF_g_now. wk_eq_fact OFF_g_s.
  assert (HNOW : 0 <= g_now B2 < 2 ^ 64).
  { unfold g_now. pose proof (u_at_range B2 OFF_g_now 8) as R. cbn in R. lia. }
  (* 0x13b10 ld a1, g_now; 0x13b14-0x13b18 a0 = &g_s; 0x13b1c jal diginet_session_close *)
  do 4 zstep.
  eapply evt_cut.
  { eapply DSC with (B := B2) (TF := None) (lo := lo).
    - reflexivity.
    - reflexivity.
    - exact HNOW.
    - exact HWM.
    - exact HFN.
    - exact HB3.
    - exact I.
    - exact HRO.
    - rewrite unsigned_lit by lia. exact HSP.
    - rewrite unsigned_lit by lia. exact HSTK.
    - rewrite unsigned_lit by lia. unfold diginet_session_close_FRAME. lia.
    - unfold w_off_stack. rewrite unsigned_lit by lia. unfold diginet_session_close_FRAME. lia.
    - exact HMI. }
  intros ms' Hpost.
  destruct Hpost as (c0 & cc1 & c2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & f3 & f4 & f5 & f6 & m3 &
                     -> & MU3 & WMO3 & MI3 & ST3 & WM3 & FN3).
  rewrite unsigned_lit in MU3, ST3 by lia.
  assert (HM3 : llvm_mem data D Sp lo B3 m0 m3 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28).
  { eapply (llvm_mem_after_call data D Sp lo diginet_session_close_FRAME B2 B3 m0 m m3);
      [ exact HM0 | unfold diginet_session_close_FRAME, LLVM_LOOP_K; lia | exact MU3 | exact WMO3
      | exact MI3 | exact ST3 | exact WM3 | exact FN3 ]. }
  clear HD HSTK HMI HRO HWM HRW HFN MU3 WMO3 MI3 ST3 WM3 HM0.
  pose proof HM3 as HM3c. unfold llvm_mem in HM3c.
  destruct HM3c as (_ & _ & HD & _ & HSTK & _ & _ & _ & _ & _ & _ & HMI & HRO & HWM & HFN & _ & _ & HRW).
  (* 0x13b20 mv a0, zero; 0x13b24 j 0x13c4c; 0x13c4c jal settle *)
  rewrite (ret_pc_even 0x13b20) by (first [lia | reflexivity]).
  do 3 zstep.
  eapply evt_cut.
  { eapply STC with (B := B3) (ticked := 0) (lo := lo).
    - reflexivity.
    - lia.
    - exact HWM.
    - exact HB4.
    - rewrite unsigned_lit by lia. exact HSP.
    - rewrite unsigned_lit by lia. exact HSTK.
    - rewrite unsigned_lit by lia. unfold settle_FRAME. lia.
    - unfold w_off_stack. rewrite unsigned_lit by lia. unfold settle_FRAME. lia.
    - exact HMI. }
  intros ms' Hpost.
  destruct Hpost as (g0 & g1 & g2 & h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & i3 & i4 & i5 & i6 & m4 &
                     -> & MU4 & WMO4 & MI4 & ST4 & EB & WM4).
  rewrite unsigned_lit in MU4, ST4 by lia.
  subst B4.
  assert (HM4 : llvm_mem data D Sp lo B3 m0 m4 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28).
  { eapply (llvm_mem_after_call data D Sp lo settle_FRAME B3 B3 m0 m3 m4);
      [ exact HM3 | unfold settle_FRAME, LLVM_LOOP_K; lia | apply munch_add_world; exact MU4
      | exact WMO4 | exact MI4 | exact ST4 | exact WM4 | exact HFN ]. }
  (* 0x13c50 j 0x1428c *)
  rewrite (ret_pc_even 0x13c50) by (first [lia | reflexivity]).
  zstep.
  apply HK. unfold llvm_latch. do 22 eexists. split; [reflexivity|].
  split; [exact HOPS|]. split; [exact HC1|]. exact HM4.
Qed.

Lemma llvm_op6 : forall Sp lo ops c c1 B B1 B2 B3 B4 rr
    m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q,
  memset_contract -> diginet_session_close_contract -> settle_contract ->
  llvm_case data D m0 gp tp 6 Sp lo ops c c1 B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
  op_begin_m B = Some (B1, tt) ->
  m_close_m B1 = Some (B2, tt) ->
  diginet_session_close_m timg_plain None B2 (g_now B2) = Some (B3, rr) ->
  settle_m B3 0 = Some (B4, tt) ->
  (forall ms', llvm_latch data D m0 gp tp Sp lo ops c1 B4
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros Sp lo ops c c1 B B1 B2 B3 B4 rr m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q
    MSC DSC STC H HB1 HB2 HB3 HB4 HK.
  destruct H as (rz & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 &
                 t3 & t4 & t5 & t6 & m & j10 & j28 & -> & HOPS & HN & HC & HC1 & HM).
  pose proof HM as HM0.
  unfold llvm_mem in HM.
  destruct HM as (_ & _ & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HJ1 & HJ2 & HRW).
  pose proof (wm_len _ _ _ _ HWM) as LB.
  assert (LBz : Z.of_nat (length B) = W_LEN) by (rewrite LB, Z2Nat.id; [reflexivity | unfold W_LEN; lia]).
  unfold LLVM_CASE. cbn [Z.eqb Pos.eqb].
  wk_facts. wk_eq_fact OFF_g_fail_next. wk_eq_fact OFF_OW. wk_eq_fact OFF_GOT.
  wk_eq_fact OFF_M. wk_eq_fact A_M_fail. wk_eq_fact A_OW_desk_off. wk_eq_fact A_M_state.
  wk_eq_fact A_OW_e3. wk_eq_fact A_OW_n. wk_eq_fact A_M_fly_on. wk_eq_fact OFF_g_now.
  wk_eq_fact A_M_desk_known. wk_eq_fact A_M_foreign. wk_eq_fact SZ_OW. wk_eq_fact SZ_GOT.
  (* ---- 0x13a64-0x13a70: memset(&OW, 0, 0x130) ---- *)
  do 4 zstep.
  assert (CW1 : rw_cells rsegs m (W_BASE_PLAIN + OFF_OW) [CB (Z.to_nat 304) (sub B OFF_OW 304)]).
  { pose proof (wm_cell rsegs W_BASE_PLAIN m B OFF_OW 304 (W_BASE_PLAIN + OFF_OW) HWM eq_refl
                  ltac:(lia) ltac:(lia)) as P.
    rewrite length_sub in P by lia. exact P. }
  eapply evt_cut.
  { eapply MSC with (junk := sub B OFF_OW 304).
    - rewrite !unsigned_lit by lia.
      replace (W_BASE_PLAIN + OFF_g_fail_next + 344) with (W_BASE_PLAIN + OFF_OW) by lia. exact CW1.
    - exact HMI. }
  intros ms' Hpost. unfold memset_post in Hpost.
  destruct Hpost as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z3 & z4 & z5 & z6 & m1 &
                     -> & MU1 & WMO1 & MI1 & CZ1).
  rewrite !unsigned_lit in MU1, CZ1 by lia.
  replace (W_BASE_PLAIN + OFF_g_fail_next + 344) with (W_BASE_PLAIN + OFF_OW) in MU1, CZ1 by lia.
  cbn [Z.to_nat] in CZ1.
  assert (HM1 : llvm_mem data D Sp lo (upd B OFF_OW (repeat (Z_to_bv 8 0) 304)) m0 m1
                  ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28).
  { eapply (llvm_mem_after_fill data D Sp lo B m0 m m1);
      [ exact HM0 | exact MU1 | exact WMO1 | exact MI1 | exact CZ1 | lia | lia | lia | ].
    unfold g_fail_next.
    rewrite u_at_upd_out by (rewrite ?repeat_length; unfold OFF_g_fail_next, OFF_OW in *; lia).
    exact HFN. }
  clear HM0 HD HSTK HMI HRO HWM HRW HFN CW1 CZ1 MU1 WMO1 MI1.
  (* ---- 0x13a74-0x13a80: memset(&GOT, 0, 0xe0) ---- *)
  pose proof HM1 as HM1c. unfold llvm_mem in HM1c.
  destruct HM1c as (_ & _ & HD & _ & HSTK & _ & _ & _ & _ & _ & _ & HMI & HRO & HWM & HFN & _ & _ & HRW).
  set (Ba := upd B OFF_OW (repeat (Z_to_bv 8 0) 304)) in *.
  assert (LBa : Z.of_nat (length Ba) = W_LEN)
    by (unfold Ba; rewrite length_upd; [exact LBz | lia | rewrite repeat_length; lia]).
  rewrite (ret_pc_even 0x13a74) by (first [lia | reflexivity]).
  do 4 zstep.
  assert (CW2 : rw_cells rsegs m1 (W_BASE_PLAIN + OFF_GOT) [CB (Z.to_nat 224) (sub Ba OFF_GOT 224)]).
  { pose proof (wm_cell rsegs W_BASE_PLAIN m1 Ba OFF_GOT 224 (W_BASE_PLAIN + OFF_GOT) HWM eq_refl
                  ltac:(lia) ltac:(lia)) as P.
    rewrite length_sub in P by lia. exact P. }
  eapply evt_cut.
  { eapply MSC with (junk := sub Ba OFF_GOT 224).
    - rewrite !unsigned_lit by lia.
      replace (W_BASE_PLAIN + OFF_g_fail_next + 116) with (W_BASE_PLAIN + OFF_GOT) by lia. exact CW2.
    - exact HMI. }
  intros ms' Hpost. unfold memset_post in Hpost.
  destruct Hpost as (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 &
                     -> & MU2 & WMO2 & MI2 & CZ2).
  rewrite !unsigned_lit in MU2, CZ2 by lia.
  replace (W_BASE_PLAIN + OFF_g_fail_next + 116) with (W_BASE_PLAIN + OFF_GOT) in MU2, CZ2 by lia.
  cbn [Z.to_nat] in CZ2.
  assert (HM2 : llvm_mem data D Sp lo (upd Ba OFF_GOT (repeat (Z_to_bv 8 0) 224)) m0 m2
                  ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28).
  { eapply (llvm_mem_after_fill data D Sp lo Ba m0 m1 m2);
      [ exact HM1 | exact MU2 | exact WMO2 | exact MI2 | exact CZ2 | lia | lia | lia | ].
    unfold g_fail_next.
    rewrite u_at_upd_out by (rewrite ?repeat_length; unfold OFF_g_fail_next, OFF_GOT in *; lia).
    exact HFN. }
  clear HD HSTK HMI HRO HWM HRW HFN CW2 CZ2 MU2 WMO2 MI2 HM1.
  pose proof HM2 as HM2c. unfold llvm_mem in HM2c.
  destruct HM2c as (_ & _ & HD & _ & HSTK & _ & _ & _ & _ & _ & _ & HMI & HRO & HWM & HFN & _ & _ & HRW).
  set (Bb := upd Ba OFF_GOT (repeat (Z_to_bv 8 0) 224)) in *.
  assert (LBb : Z.of_nat (length Bb) = W_LEN)
    by (unfold Bb; rewrite length_upd; [exact LBa | lia | rewrite repeat_length; lia]).
  (* the fields op_begin zeroed, as the folded constants the code uses *)
  assert (ZOW : forall i (n : nat), 0 <= i -> (Z.to_nat i + n <= 304)%nat ->
                  sub Bb (OFF_OW + i) n = repeat (Z_to_bv 8 0) n).
  { intros i n Hi Hn. unfold Bb.
    rewrite sub_upd_out by (rewrite ?repeat_length; lia).
    unfold Ba. rewrite op6_sub_upd_in by (rewrite ?repeat_length; lia).
    apply op6_sub_repeat; lia. }
  assert (E3z : OW_e3 Bb = 0).
  { unfold OW_e3, A_OW_e3, s32_at, u_at. rewrite (ZOW 200 4%nat) by lia. reflexivity. }
  assert (ENz : OW_n Bb = 0).
  { unfold OW_n, A_OW_n, s32_at, u_at. rewrite (ZOW 0 4%nat) by lia. reflexivity. }
  rewrite (ret_pc_even 0x13a84) by (first [lia | reflexivity]).
  (* ---- 0x13a84-0x13a98: M.fail = g_fail_next, OW.desk_off = -1 (op_begin's last two writes) ---- *)
  unfold off_world in HOW. unfold off_window in HOWIN.
  unfold LLVM_LOOP_K, LLVM_FRAME in *.
  unfold llvm_frame_consts, llvm_saved in HRW.
  pose proof (munch_refl [(Sp - 0, Sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m2) as MU6.
  pose proof (wmono_refl rsegs m2) as WMO6.
  do 6 zstep.
  (* the world is now op_begin's result, the model's B1 *)
  assert (EB1 : upd (upd Bb 88 (put 4 (u_at Bb OFF_g_fail_next 1))) 65544 (put 4 (-1)) = B1).
  { rewrite (op6_begin_world B Bb LBz eq_refl) in HB1. congruence. }
  lazymatch goal with H : rw_cells rsegs ?mm W_BASE_PLAIN _ |- _ => rewrite EB1 in H end.
  assert (EFNa : OFF_g_fail_next = 64968) by reflexivity.
  assert (EWLa : W_LEN = 65616) by reflexivity.
  assert (LB1a : Z.of_nat (length (upd Bb 88 (put 4 (u_at Bb OFF_g_fail_next 1)))) = W_LEN)
    by (apply op6_len_put; [exact LBb | lia | cbn [Z.of_nat]; lia]).
  assert (LB1 : Z.of_nat (length B1) = W_LEN)
    by (rewrite <- EB1; apply op6_len_put; [exact LB1a | lia | cbn [Z.of_nat]; lia]).
  assert (FN1 : g_fail_next B1 = g_fail_next Bb).
  { rewrite <- EB1.
    rewrite op6_fn_put by (first [exact LB1a | cbn [Z.of_nat]; lia]).
    rewrite op6_fn_put by (first [exact LBb | cbn [Z.of_nat]; lia]).
    reflexivity. }
  lazymatch goal with H : rw_cells rsegs ?m6 W_BASE_PLAIN [CB _ B1] |- _ =>
    assert (HM6 : llvm_mem data D Sp lo B1 m0 m6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28) end.
  { eapply (llvm_mem_after_call data D Sp lo 0 Bb B1 m0 m2);
      [ exact HM2 | unfold LLVM_LOOP_K; lia | exact MU6 | exact WMO6 | assumption | assumption
      | assumption | rewrite FN1; exact HFN ]. }
  assert (HCc1 : llvm_cursor D c1).
  { rewrite HC1. unfold llvm_cursor, fuzz_u8_m in *.
    destruct (Z.eqb_spec (fi_n c) 0); [lia|]. cbn. lia. }
  (* ---- 0x13af0-0x13b0c: m_set's event record, for either arm ---- *)
  assert (MSET : forall mm Bx st (p1 p2 p3 p4 p5 p6 p7 n0 n1 n2 n3 n4 n5 n6 rz' : word),
    llvm_mem data D Sp lo Bx m0 mm ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 ->
    OW_n Bx = 0 -> M_state Bx = st -> -2^31 <= st < 2^31 ->
    diginet_session_close_m timg_plain None
      (set_M_state (set_OW_n (set_OW_t_reason (set_OW_t_old (set_OW_t_state Bx 0 3) 0 st) 0 8) 1) 3)
      (g_now (set_M_state (set_OW_n (set_OW_t_reason (set_OW_t_old (set_OW_t_state Bx 0 3) 0 st) 0 8) 1) 3))
      = Some (B3, rr) ->
    settle_m B3 0 = Some (B4, tt) ->
    evt rsegs Q
      (MS (mkR rz' (Z_to_bv 64 Sp) gp tp n0 n1 n2 r8 (Z_to_bv 64 7) (Z_to_bv 64 st) p1 p2 p3 p4 p5 p6 p7
               (Z_to_bv 64 0x39) (Z_to_bv 64 (data + fi_off c1)) (Z_to_bv 64 (data + fi_off c))
               (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) (Z_to_bv 64 (fi_n c1)) (Z_to_bv 64 (fi_n c))
               (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
               (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) n3 n4 n5 n6)
          F (Z_to_bv 64 0x13af0) fc None mm (seg_rom rsegs))).
  { intros mm Bx st p1 p2 p3 p4 p5 p6 p7 n0 n1 n2 n3 n4 n5 n6 rz' HMx HNx HSx HSTr HB3' HB4'.
    pose proof HMx as HMx0. unfold llvm_mem in HMx.
    destruct HMx as (_ & _ & HDx & HSPx & HSTKx & HLOx & HSP2x & HWOSx & HOWSx & HOWx & HOWINx & HMIx & HROx & HWMx
                     & HFNx & HJ1x & HJ2x & HRWx).
    pose proof (wm_len _ _ _ _ HWMx) as LBx.
    assert (LBxz : Z.of_nat (length Bx) = W_LEN)
      by (rewrite LBx, Z2Nat.id; [reflexivity | unfold W_LEN; lia]).
    unfold llvm_frame_consts, llvm_saved in HRWx.
    unfold off_world in HOWx. unfold off_window in HOWINx.
    unfold LLVM_LOOP_K, LLVM_FRAME in *.
    pose proof (munch_refl [(Sp - 0, Sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] mm) as MUx.
    pose proof (wmono_refl rsegs mm) as WMOx.
    do 8 zstep.
    (* the four stores are m_set's record, in the model's form *)
    lazymatch goal with H : rw_cells rsegs ?mm' W_BASE_PLAIN _ |- _ =>
      rewrite (op6_mset_world Bx st LBxz) in H end.
    eapply llvm_op6_tail with (B2 := set_M_state (set_OW_n (set_OW_t_reason
              (set_OW_t_old (set_OW_t_state Bx 0 3) 0 st) 0 8) 1) 3);
      [ exact DSC | exact STC | | exact HCc1 | exact HOPS | exact HB3' | exact HB4' | exact HK ].
    eapply (llvm_mem_after_call data D Sp lo 0 Bx _ m0 mm);
      [ exact HMx0 | unfold LLVM_LOOP_K; lia | exact MUx | exact WMOx | assumption | assumption
      | assumption | ].
    rewrite op6_fn_mset by exact LBxz. exact HFNx. }
  (* the three fields m_close tests: the first two were read before op_begin's last two writes *)
  assert (EOFM : OFF_M = 0) by reflexivity.
  assert (EDK : s32_at Bb 0 = M_desk_known B1).
  { unfold M_desk_known, A_M_desk_known, OFF_M. rewrite <- EB1.
    rewrite (op6_s32_put _ 65544 4 (-1) (0 + 0)) by (first [exact LB1a | cbn [Z.of_nat]; lia]).
    rewrite (op6_s32_put _ 88 4 (u_at Bb OFF_g_fail_next 1) (0 + 0))
      by (first [exact LBb | cbn [Z.of_nat]; lia]).
    first [reflexivity | (f_equal; lia)]. }
  assert (EST : s32_at Bb 12 = M_state B1).
  { unfold M_state, A_M_state, OFF_M. rewrite <- EB1.
    rewrite (op6_s32_put _ 65544 4 (-1) (0 + 12)) by (first [exact LB1a | cbn [Z.of_nat]; lia]).
    rewrite (op6_s32_put _ 88 4 (u_at Bb OFF_g_fail_next 1) (0 + 12))
      by (first [exact LBb | cbn [Z.of_nat]; lia]).
    first [reflexivity | (f_equal; lia)]. }
  assert (EN1 : OW_n B1 = 0).
  { unfold OW_n, A_OW_n, OFF_OW. rewrite <- EB1.
    rewrite (op6_s32_put _ 65544 4 (-1) (65312 + 0)) by (first [exact LB1a | cbn [Z.of_nat]; lia]).
    rewrite (op6_s32_put _ 88 4 (u_at Bb OFF_g_fail_next 1) (65312 + 0))
      by (first [exact LBb | cbn [Z.of_nat]; lia]).
    replace (65312 + 0) with 65312 by lia.
    unfold OW_n, A_OW_n, OFF_OW in ENz. rewrite <- ENz. first [reflexivity | (f_equal; lia)]. }
  assert (E31 : OW_e3 B1 = 0).
  { unfold OW_e3, A_OW_e3, OFF_OW. rewrite <- EB1.
    rewrite (op6_s32_put _ 65544 4 (-1) (65312 + 200)) by (first [exact LB1a | cbn [Z.of_nat]; lia]).
    rewrite (op6_s32_put _ 88 4 (u_at Bb OFF_g_fail_next 1) (65312 + 200))
      by (first [exact LBb | cbn [Z.of_nat]; lia]).
    unfold OW_e3, A_OW_e3, OFF_OW in E3z. rewrite <- E3z. first [reflexivity | (f_equal; lia)]. }
  pose proof (s32_range B1 12) as RST.
  pose proof (s32_range Bb 0) as RDK.
  pose proof (s32_range Bb 12) as RDS.
  pose proof (s32_range B1 24) as RFO.
  (* ---- 0x13ae4-0x13aec: the arm m_close takes when its test fails: only M.fly_on = 0 ---- *)
  assert (ELSE : forall (p1 p2 p3 p4 p5 p6 p7 n0 n1 n2 n3 n4 n5 n6 rz' : word) mm,
    llvm_mem data D Sp lo B1 m0 mm ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 ->
    truth (M_desk_known B1) && negb (truth (M_foreign B1)) && negb (M_state B1 =? S_CLOSED) = false ->
    evt rsegs Q
      (MS (mkR rz' (Z_to_bv 64 Sp) gp tp n0 n1 n2 r8 (Z_to_bv 64 7) (Z_to_bv 64 (M_state B1))
               p1 p2 p3 p4 p5 p6 p7
               (Z_to_bv 64 0x39) (Z_to_bv 64 (data + fi_off c1)) (Z_to_bv 64 (data + fi_off c))
               (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) (Z_to_bv 64 (fi_n c1)) (Z_to_bv 64 (fi_n c))
               (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
               (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) n3 n4 n5 n6)
          F (Z_to_bv 64 0x13ae4) fc None mm (seg_rom rsegs))).
  { intros p1 p2 p3 p4 p5 p6 p7 n0 n1 n2 n3 n4 n5 n6 rz' mm HMe HTe.
    pose proof HMe as HMe0. unfold llvm_mem in HMe.
    destruct HMe as (_ & _ & HDe & HSPe & HSTKe & HLOe & HSP2e & HWOSe & HOWSe & _ & _ & HMIe & HROe & HWMe
                     & HFNe & _ & _ & HRWe).
    pose proof (wm_len _ _ _ _ HWMe) as LBe.
    assert (LBez : Z.of_nat (length B1) = W_LEN)
      by (rewrite LBe, Z2Nat.id; [reflexivity | unfold W_LEN; lia]).
    unfold llvm_frame_consts, llvm_saved in HRWe.
    unfold LLVM_LOOP_K, LLVM_FRAME in *.
    pose proof (munch_refl [(Sp - 0, Sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] mm) as MUe.
    pose proof (wmono_refl rsegs mm) as WMOe.
    unfold m_close_m in HB2. rewrite HTe in HB2. cbv beta iota in HB2.
    (* 0x13ae4 sw zero, M.fly_on; 0x13ae8 li a1, 3; 0x13aec beq a0, a1 *)
    do 3 zstep.
    assert (EFLY : upd B1 96 (put 4 0) = set_M_fly_on B1 0)
      by (unfold set_M_fly_on, A_M_fly_on, OFF_M; f_equal; lia).
    lazymatch goal with H : rw_cells rsegs ?mm' W_BASE_PLAIN _ |- _ => rewrite EFLY in H end.
    assert (LFLY : Z.of_nat (length (set_M_fly_on B1 0)) = W_LEN)
      by (unfold set_M_fly_on, A_M_fly_on, OFF_M; apply op6_len_put;
          [exact LBez | lia | cbn [Z.of_nat]; lia]).
    assert (SFLY : M_state (set_M_fly_on B1 0) = M_state B1)
      by (unfold M_state, A_M_state, set_M_fly_on, A_M_fly_on, OFF_M;
          rewrite (op6_s32_put _ (0 + 96) 4 0 (0 + 12));
          [reflexivity | exact LBez | lia | lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia]).
    assert (NFLY : OW_n (set_M_fly_on B1 0) = 0).
    { unfold OW_n, A_OW_n, OFF_OW, set_M_fly_on, A_M_fly_on, OFF_M.
      rewrite (op6_s32_put _ (0 + 96) 4 0 (65312 + 0));
        [| exact LBez | lia | lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia].
      unfold OW_n, A_OW_n, OFF_OW in EN1. rewrite <- EN1. first [reflexivity | (f_equal; lia)]. }
    assert (FFLY : g_fail_next (set_M_fly_on B1 0) = g_fail_next B1)
      by (unfold set_M_fly_on, A_M_fly_on, OFF_M; apply op6_fn_put;
          [exact LBez | lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia]).
    lazymatch goal with H : rw_cells rsegs ?mf W_BASE_PLAIN _ |- _ =>
      assert (HMf : llvm_mem data D Sp lo (set_M_fly_on B1 0) m0 mf
                      ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28) end.
    { eapply (llvm_mem_after_call data D Sp lo 0 B1 (set_M_fly_on B1 0) m0 mm);
        [ exact HMe0 | unfold LLVM_LOOP_K; lia | exact MUe | exact WMOe | assumption | assumption
        | assumption | rewrite FFLY; exact HFNe ]. }
    if_cases K4; zify_cond K4.
    - (* M.state is already CLOSED: m_set writes nothing, straight to 0x13b10 *)
      assert (ECL : M_state B1 = S_CLOSED)
        by (apply (proj1 (op6_s32_eq (M_state B1) 3 (s32_range B1 12) ltac:(lia))); exact K4).
      rewrite (op6_mset_closed _ ltac:(rewrite SFLY; exact ECL)) in HB2.
      injection HB2 as EB2. rewrite <- EB2 in HB3.
      eapply llvm_op6_tail;
        [ exact DSC | exact STC | exact HMf | exact HCc1 | exact HOPS | exact HB3 | exact HB4 | exact HK ].
    - (* a state other than CLOSED: m_set's record *)
      assert (ECL : M_state B1 <> S_CLOSED).
      { intros E. apply K4. rewrite E. apply Z.mod_small. unfold S_CLOSED. lia. }
      rewrite (op6_mset_model _ NFLY ltac:(rewrite SFLY; exact ECL)) in HB2.
      injection HB2 as EB2. rewrite <- EB2 in HB3.
      rewrite SFLY in HB3.
      eapply (MSET _ (set_M_fly_on B1 0) (M_state B1));
        [ exact HMf | exact NFLY | exact SFLY | exact (s32_range B1 12) | exact HB3 | exact HB4 ]. }
  (* ---- 0x13a9c-0x13abc: m_close's three tests ---- *)
  zstep.
  if_cases K1; zify_cond K1; rewrite EOFM in K1; rewrite EDK in K1.
  { (* M.desk_known = 0 *)
    assert (EZ1 : M_desk_known B1 = 0)
      by (apply (proj1 (op6_s32_eq (M_desk_known B1) 0 (s32_range B1 0) ltac:(lia))); exact K1).
    rewrite EST. apply ELSE; [exact HM6|].
    unfold truth. rewrite EZ1. reflexivity. }
  do 2 zstep.
  if_cases K2; zify_cond K2.
  { (* M.foreign <> 0 *)
    assert (EFO : s32_at B1 24 = M_foreign B1)
      by (unfold M_foreign, A_M_foreign, OFF_M; f_equal; lia).
    rewrite EFO in K2.
    assert (EZ2 : M_foreign B1 <> 0) by (intros E; apply K2; rewrite E; reflexivity).
    rewrite EST. apply ELSE; [exact HM6|].
    replace (negb (truth (M_foreign B1))) with false
      by (unfold truth; rewrite (proj2 (Z.eqb_neq (M_foreign B1) 0) EZ2); reflexivity).
    rewrite andb_false_r. reflexivity. }
  do 2 zstep.
  if_cases K3; zify_cond K3; rewrite EST in K3.
  { (* M.state is CLOSED *)
    assert (EZ3 : M_state B1 = S_CLOSED)
      by (apply (proj1 (op6_s32_eq (M_state B1) 3 (s32_range B1 12) ltac:(lia))); exact K3).
    rewrite EST. apply ELSE; [exact HM6|].
    rewrite EZ3, Z.eqb_refl. rewrite andb_false_r. reflexivity. }
  (* ---- the main arm, 0x13ab0-0x13abc: OW.e3 = 1, M.fail = 0, M.fly_on = 0 ---- *)
  assert (EZ1 : M_desk_known B1 <> 0) by (intros E; apply K1; rewrite E; reflexivity).
  assert (EFO : s32_at B1 24 = M_foreign B1)
    by (unfold M_foreign, A_M_foreign, OFF_M; f_equal; lia).
  rewrite EFO in K2.
  assert (EZ2 : M_foreign B1 = 0)
    by (apply (proj1 (op6_s32_eq (M_foreign B1) 0 (s32_range B1 24) ltac:(lia))); exact K2).
  assert (EZ3 : M_state B1 <> S_CLOSED).
  { intros E. apply K3. rewrite E. apply Z.mod_small. unfold S_CLOSED. lia. }
  (* the model takes the then arm, and OW.e3 was zeroed by op_begin, so the increment is 1 *)
  unfold m_close_m in HB2.
  replace (truth (M_desk_known B1) && negb (truth (M_foreign B1)) && negb (M_state B1 =? S_CLOSED))
    with true in HB2
    by (unfold truth; rewrite EZ2, (proj2 (Z.eqb_neq (M_desk_known B1) 0) EZ1),
          (proj2 (Z.eqb_neq (M_state B1) S_CLOSED) EZ3); reflexivity).
  cbv beta iota in HB2. rewrite E31 in HB2.
  assert (EINC : int_inc 0 = Some 1) by (vm_compute; reflexivity).
  rewrite EINC in HB2. cbv beta iota in HB2.
  do 4 zstep.
  (* the three stores are m_close's then arm and m_set's fly_on clear, in the model's order *)
  assert (EMAIN : upd (upd (upd B1 65512 (put 4 1)) 88 (put 4 0)) 96 (put 4 0)
                  = set_M_fly_on (set_M_fail (set_OW_e3 B1 1) 0) 0).
  { unfold set_M_fly_on, set_M_fail, set_OW_e3, A_M_fly_on, A_M_fail, A_OW_e3, OFF_M, OFF_OW.
    replace (65312 + 200) with 65512 by lia. replace (0 + 88) with 88 by lia.
    replace (0 + 96 + 0) with 96 by lia. reflexivity. }
  lazymatch goal with H : rw_cells rsegs ?mm W_BASE_PLAIN _ |- _ => rewrite EMAIN in H end.
  assert (LM1 : Z.of_nat (length (set_OW_e3 B1 1)) = W_LEN)
    by (unfold set_OW_e3, A_OW_e3, OFF_OW; apply op6_len_put;
        [exact LB1 | lia | cbn [Z.of_nat]; lia]).
  assert (LM2 : Z.of_nat (length (set_M_fail (set_OW_e3 B1 1) 0)) = W_LEN)
    by (unfold set_M_fail, A_M_fail, OFF_M; apply op6_len_put; [exact LM1 | lia | cbn [Z.of_nat]; lia]).
  assert (LM3 : Z.of_nat (length (set_M_fly_on (set_M_fail (set_OW_e3 B1 1) 0) 0)) = W_LEN)
    by (unfold set_M_fly_on, A_M_fly_on, OFF_M; apply op6_len_put;
        [exact LM2 | lia | cbn [Z.of_nat]; lia]).
  assert (SMAIN : M_state (set_M_fly_on (set_M_fail (set_OW_e3 B1 1) 0) 0) = M_state B1).
  { unfold M_state, A_M_state, set_M_fly_on, set_M_fail, set_OW_e3,
           A_M_fly_on, A_M_fail, A_OW_e3, OFF_M, OFF_OW.
    rewrite (op6_s32_put _ (0 + 96 + 0) 4 0 (0 + 12)) by (first [exact LM2 | cbn [Z.of_nat]; lia]).
    rewrite (op6_s32_put _ (0 + 88) 4 0 (0 + 12)) by (first [exact LM1 | cbn [Z.of_nat]; lia]).
    rewrite (op6_s32_put _ (65312 + 200) 4 1 (0 + 12)) by (first [exact LB1 | cbn [Z.of_nat]; lia]).
    reflexivity. }
  assert (NMAIN : OW_n (set_M_fly_on (set_M_fail (set_OW_e3 B1 1) 0) 0) = 0).
  { unfold OW_n, A_OW_n, set_M_fly_on, set_M_fail, set_OW_e3,
           A_M_fly_on, A_M_fail, A_OW_e3, OFF_M, OFF_OW.
    rewrite (op6_s32_put _ (0 + 96 + 0) 4 0 (65312 + 0)) by (first [exact LM2 | cbn [Z.of_nat]; lia]).
    rewrite (op6_s32_put _ (0 + 88) 4 0 (65312 + 0)) by (first [exact LM1 | cbn [Z.of_nat]; lia]).
    rewrite (op6_s32_put _ (65312 + 200) 4 1 (65312 + 0)) by (first [exact LB1 | cbn [Z.of_nat]; lia]).
    unfold OW_n, A_OW_n, OFF_OW in EN1. rewrite <- EN1. first [reflexivity | (f_equal; lia)]. }
  assert (FMAIN : g_fail_next (set_M_fly_on (set_M_fail (set_OW_e3 B1 1) 0) 0) = g_fail_next B1).
  { unfold set_M_fly_on, set_M_fail, set_OW_e3, A_M_fly_on, A_M_fail, A_OW_e3, OFF_M, OFF_OW.
    rewrite op6_fn_put by (first [exact LM2 | cbn [Z.of_nat]; lia]).
    rewrite op6_fn_put by (first [exact LM1 | cbn [Z.of_nat]; lia]).
    rewrite op6_fn_put by (first [exact LB1 | cbn [Z.of_nat]; lia]).
    reflexivity. }
  lazymatch goal with H : rw_cells rsegs ?mf W_BASE_PLAIN _ |- _ =>
    assert (HMm : llvm_mem data D Sp lo (set_M_fly_on (set_M_fail (set_OW_e3 B1 1) 0) 0) m0 mf
                    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28) end.
  { eapply (llvm_mem_after_call data D Sp lo 0 Bb _ m0 m2);
      [ exact HM2 | unfold LLVM_LOOP_K; lia | exact MU6 | exact WMO6 | assumption | assumption
      | assumption | rewrite FMAIN, FN1; exact HFN ]. }
  rewrite (op6_mset_model _ NMAIN ltac:(rewrite SMAIN; exact EZ3)) in HB2.
  injection HB2 as EB2. rewrite <- EB2 in HB3. rewrite SMAIN in HB3.
  rewrite EST.
  eapply (MSET _ (set_M_fly_on (set_M_fail (set_OW_e3 B1 1) 0) 0) (M_state B1));
    [ exact HMm | exact NMAIN | exact SMAIN | exact (s32_range B1 12) | exact HB3 | exact HB4 ].
Qed.

End OP6.
