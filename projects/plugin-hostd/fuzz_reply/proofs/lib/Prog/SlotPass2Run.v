From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayRep ListStep SlotHead
  pthread_mutex_lock_c pthread_mutex_unlock_c drain_b_c check_no_loss_read_c check_no_loss_c check_shape_done_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma op2_seg_drain : forall
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  evt rsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x1402c) x2 x3 x4 x5 x6 x7 x8 x9 x18 x11 x12 x13 x14 x15 x16 x17
      x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 DRAIN) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
      x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14024) fc None m ro).
Proof.
  intros. step. step. apply evt_done. reflexivity.
Qed.

Lemma op2_seg_unlock : forall (SP : Z)
    (x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  evt rsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x14038) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x19 x11 x12 x13 x14 x15
      x16 x17 x18 (Z_to_bv 64 (SP + 32)) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F
      (Z_to_bv 64 PTHREAD_MUTEX_UNLOCK) fc None m ro)
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
      x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x1402c) fc None m ro).
Proof.
  intros. step. step. step. apply evt_done. reflexivity.
Qed.

Lemma op2_seg_cnlr : forall
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  evt rsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x14040) x2 x3 x4 x5 x6 x7 x8 x9 x9 x11 x12 x13 x14 x15 x16 x17
      x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 CHECK_NO_LOSS_READ) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
      x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14038) fc None m ro).
Proof.
  intros. step. step. apply evt_done. reflexivity.
Qed.

Lemma op2_seg_cnl : forall (SP : Z)
    (x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  evt rsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x1404c) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x9 (Z_to_bv 64 (SP + 40))
      x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F
      (Z_to_bv 64 CHECK_NO_LOSS) fc None m ro)
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
      x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14040) fc None m ro).
Proof.
  intros. step. step. step. apply evt_done. reflexivity.
Qed.

Lemma op2_seg_done : forall (SP : Z) (v : word)
    (x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  ov_read_bytes rsegs m (Z_to_bv 64 (SP + 40)) 8 = Some (le8 v) ->
  evt rsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x14054) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 v x11
      x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F
      (Z_to_bv 64 CHECK_SHAPE_DONE) fc None m ro)
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
      x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x1404c) fc None m ro).
Proof.
  intros. step. step. apply evt_done. reflexivity.
Qed.

Lemma op2_seg_tail : forall
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  evt rsegs (fun ms => ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
      x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 TAIL_CHECK) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
      x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14054) fc None m ro).
Proof.
  intros. step. apply evt_done. reflexivity.
Qed.

Lemma p2_rd4 : forall m a (v : word), bytes_at rsegs m a (le4 v) ->
  ov_read_bytes rsegs m (Z_to_bv 64 a) 4 = Some (le4 v).
Proof.
  intros m a v H. change (Z_to_bv 64 a) with (wa a).
  replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m a (le4 v) 0 4 H ltac:(lia)) by (rewrite length_le4; lia).
  reflexivity.
Qed.

Lemma p2_entry_len : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  length (entry_bytes e) = 56%nat.
Proof.
  intros e H1 H2. unfold entry_bytes. rewrite !length_app, !length_le4, !length_le8, H1, H2. reflexivity.
Qed.

Lemma p2_head : forall m K e es, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  bytes_at rsegs m K (concat (map entry_bytes (e :: es))) ->
  bytes_at rsegs m K (le4 (Z_to_bv 64 (re_fd e))) /\ bytes_at rsegs m (K + 4) (le4 (Z_to_bv 64 (re_eof e))) /\
  bytes_at rsegs m (K + 56) (concat (map entry_bytes es)).
Proof.
  intros m K e es H1 H2 H. cbn [map concat] in H. apply bytes_at_app in H. destruct H as [HE HR].
  rewrite p2_entry_len in HR by assumption.
  unfold entry_bytes in HE. apply bytes_at_app in HE. destruct HE as [HF HE].
  apply bytes_at_app in HE. destruct HE as [HE _]. rewrite length_le4 in HE.
  split; [exact HF|]. split; [exact HE|exact HR].
Qed.

Lemma p2_eqb : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma p2_lts0 : forall N, 0 <= N < 2 ^ 63 -> bv_lts (Z_to_bv 64 0) (Z_to_bv 64 N) = (0 <? N).
Proof.
  intros N HN. rewrite bv_lts_zero_l, unsigned_lit by lia.
  destruct (Z.ltb_spec 0 N), (Z.ltb_spec N (2 ^ 63)); cbn; lia.
Qed.

Lemma p2_nth : forall (T : Type) (l : list T) x l', nth_error (l ++ x :: l') (length l) = Some x.
Proof. intros T l. induction l as [|a l IH]; intros x l'; cbn; [reflexivity|apply IH]. Qed.

Lemma p2_firstn : forall (T : Type) (l l' : list T), firstn (length l) (l ++ l') = l.
Proof. intros T l. induction l as [|a l IH]; intros l'; cbn; [reflexivity|f_equal; apply IH]. Qed.

Lemma p2_entry_scan : forall rc B L A m e, RelayRep.entry_ok (rc := rc) B L A m e ->
  length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\ 0 <= re_fd e < 2 ^ 31 /\
  (re_eof e = 0 \/ re_eof e = 1).
Proof. intros rc B L A m e (EF & _ & P1 & P2 & FD & _). tauto. Qed.

Definition op2_post (es : list rentry) (G SP S fd : Z)
    (x1 x3 x4 x5 x6 x7 x8 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (ms : machine_state) : Prop :=
  (Forall (fun e => re_fd e <> fd) es /\
   exists a0 a1 a2 s2 : word,
     ms = MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S) a0 a1 a2 x13 x14 x15 x16 x17 s2 x19
                  (Z_to_bv 64 0x30fc0) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 TAIL_CHECK) fc None
             m ro) \/
  (exists (i : nat) (e : rentry),
     nth_error es i = Some e /\ re_fd e = fd /\ Forall (fun e' => re_fd e' <> fd) (firstn i es) /\
     ((re_eof e = 1 /\
       exists a0 a1 a2 : word,
         ms = MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S) a0 a1 a2 x13 x14 x15 x16 x17
                      (Z_to_bv 64 (G + 56 * Z.of_nat i)) x19 (Z_to_bv 64 0x30fc0) x21 x22 x23 x24 x25 x26 x27 x28 x29
                      x30 x31) F (Z_to_bv 64 TAIL_CHECK) fc None
                 (write_to_mem m (Z_to_bv 64 (SP + 40)) (le8 (Z_to_bv 64 0))) ro) \/
      (re_eof e = 0 /\
       exists a1 a2 : word,
         ms = MS (mkR (Z_to_bv 64 0x14024) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S) (Z_to_bv 64 0x31018) a1 a2
                      x13 x14 x15 x16 x17 (Z_to_bv 64 (G + 56 * Z.of_nat i)) (Z_to_bv 64 0x31018)
                      (Z_to_bv 64 0x30fc0) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F
                 (Z_to_bv 64 PTHREAD_MUTEX_LOCK) fc None
                 (write_to_mem m (Z_to_bv 64 (SP + 40)) (le8 (Z_to_bv 64 0))) ro))).

Lemma op2_loop : forall (rest pre es : list rentry) (G K SP S fd n : Z)
    (x1 x3 x4 x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  es = pre ++ rest -> rest <> [] -> (length es <= 4)%nat ->
  K = G + 56 * Z.of_nat (length pre) -> n = Z.of_nat (length rest) ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\ 0 <= re_fd e < 2 ^ 31 /\
                   (re_eof e = 0 \/ re_eof e = 1)) rest ->
  bytes_at rsegs m K (concat (map entry_bytes rest)) ->
  Forall (fun e => re_fd e <> fd) pre -> 0 <= fd < 2 ^ 31 ->
  store_ok rsegs m (Z_to_bv 64 (SP + 40)) 8 = true ->
  evt rsegs (op2_post es G SP S fd x1 x3 x4 x5 x6 x7 x8 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29
      x30 x31 F fc m ro)
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S) (Z_to_bv 64 n) (Z_to_bv 64 fd) x12 x13 x14 x15 x16
      x17 (Z_to_bv 64 K) x19 (Z_to_bv 64 0x30fc0) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F
      (Z_to_bv 64 0x13da0) fc None m ro).
Proof.
  induction rest as [|e rest IH];
    intros pre es G K SP S fd n x1 x3 x4 x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28
      x29 x30 x31 F fc m ro Hes Hne Hlen HK Hn HW HB HP Hfd HS; [congruence|].
  apply Forall_cons_iff in HW. destruct HW as [(P1 & P2 & Rfd & Reof) HW].
  destruct (p2_head m K e rest P1 P2 HB) as (BF & BE & BR).
  pose proof (bytes_at_bound _ _ _ _ BR) as BDR.
  assert (HL : (length (pre ++ e :: rest) <= 4)%nat) by (rewrite <- Hes; exact Hlen).
  rewrite length_app in HL. cbn [length] in HL, Hn.
  pose proof (p2_rd4 m K _ BF) as RF.
  step. rewrite (ls_sx32 (re_fd e)) by lia.
  step.
  destruct (Z.eq_dec (re_fd e) fd) as [Hq|Hq].
  - rewrite Hq. if_true. clear RF.
    pose proof (p2_rd4 m (K + 4) _ BE) as RE.
    step. rewrite (ls_sx32 (re_eof e)) by lia.
    step. step.
    destruct Reof as [E0|E1].
    + rewrite E0. if_false. step. step. step.
      apply evt_done. unfold op2_post. right. exists (length pre), e.
      split; [rewrite Hes; apply p2_nth|]. split; [exact Hq|]. split; [rewrite Hes, p2_firstn; exact HP|].
      right. split; [exact E0|]. do 2 eexists. rewrite <- HK. reflexivity.
    + rewrite E1. if_true.
      apply evt_done. unfold op2_post. right. exists (length pre), e.
      split; [rewrite Hes; apply p2_nth|]. split; [exact Hq|]. split; [rewrite Hes, p2_firstn; exact HP|].
      left. split; [exact E1|]. do 3 eexists. rewrite <- HK. reflexivity.
  - if_false_by (eq_trans (p2_eqb (re_fd e) fd ltac:(lia) ltac:(lia)) (proj2 (Z.eqb_neq _ _) Hq)).
    step. step. step.
    if_cases HC; rewrite p2_eqb in HC by lia.
    + apply Z.eqb_eq in HC. destruct rest as [|e2 rest2]; [|cbn [length] in Hn; lia].
      apply evt_done. unfold op2_post. left. split.
      * rewrite Hes. apply Forall_app. split; [exact HP|]. constructor; [exact Hq|constructor].
      * do 4 eexists. reflexivity.
    + apply Z.eqb_neq in HC. destruct rest as [|e2 rest2]; [cbn [length] in Hn; lia|].
      step.
      eapply (IH (pre ++ [e]) es G (K + 56) SP S fd (n + -1));
        first [ exact HW | exact BR | exact Hfd | exact HS | exact Hlen | congruence
              | (rewrite Hes, <- app_assoc; reflexivity)
              | (rewrite length_app; cbn [length]; lia)
              | (cbn [length] in Hn |- *; lia)
              | (apply Forall_app; split; [exact HP|constructor; [exact Hq|constructor]])
              | idtac ].
Qed.

Lemma op2_scan : forall (es : list rentry) (tail : list byte) (G SP S fd : Z)
    (x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  ov_read_bytes rsegs m (Z_to_bv 64 0x30fd8) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat (length es)))) ->
  ov_read_bytes rsegs m (Z_to_bv 64 S) 4 = Some (le4 (Z_to_bv 64 fd)) ->
  ov_read_bytes rsegs m (Z_to_bv 64 0x30ff0) 8 = Some (le8 (Z_to_bv 64 G)) ->
  rw_cells rsegs m G [CB 896 (concat (map entry_bytes es) ++ tail)] ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\ 0 <= re_fd e < 2 ^ 31 /\
                   (re_eof e = 0 \/ re_eof e = 1)) es ->
  (length es <= 4)%nat -> 0 <= fd < 2 ^ 31 ->
  store_ok rsegs m (Z_to_bv 64 (SP + 40)) 8 = true ->
  evt rsegs (op2_post es G SP S fd x1 x3 x4 x5 x6 x7 x8 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29
      x30 x31 F fc m ro)
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
      (Z_to_bv 64 0x30fc0) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13d90) fc None m ro).
Proof.
  intros es tail G SP S fd x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 F fc m ro RN RF RG TB HW Hlen Hfd HS.
  destruct TB as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  apply bytes_at_app in HB. destruct HB as [HB _].
  step. rewrite (ls_sx32 (Z.of_nat (length es))) by lia.
  step. rewrite p2_lts0 by lia.
  if_cases HC.
  - apply Bool.negb_true_iff, Z.ltb_ge in HC.
    destruct es as [|e0 es0]; [|cbn [length] in HC; lia].
    apply evt_done. unfold op2_post. left. split; [constructor|]. do 4 eexists. reflexivity.
  - apply Bool.negb_false_iff, Z.ltb_lt in HC.
    assert (NE : es <> []) by (destruct es as [|e0 es0]; [cbn [length] in HC; lia|discriminate]).
    step. rewrite (ls_sx32 fd) by lia.
    step.
    eapply (op2_loop es [] es G G SP S fd (Z.of_nat (length es)));
      first [ exact HW | exact HB | exact Hfd | exact HS | exact Hlen | exact NE | reflexivity | constructor
            | (cbn [length]; lia) | idtac ].
Qed.
