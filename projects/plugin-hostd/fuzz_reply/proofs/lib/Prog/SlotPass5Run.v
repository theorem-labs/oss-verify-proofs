From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayRep ListStep HarnessRep SlotPass2Run.
Import ListNotations.
Local Open Scope Z_scope.

Lemma op5_seg_a : forall (P N K SP : Z)
    (x1 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (b : byte),
  0 <= K <= N -> N < 2 ^ 26 ->
  (K < N -> ov_read_bytes rsegs m (Z_to_bv 64 (P + K)) 1 = Some [b]) ->
  store_ok rsegs m (Z_to_bv 64 (SP + 32)) 8 = true ->
  evt rsegs (fun ms => exists (s0 s1 s7 : word) (K' : Z),
      ms = MS (mkR (Z_to_bv 64 0x13e80) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 s0 s1 (Z_to_bv 64 (SP + 40)) (Z_to_bv 64 48)
        (Z_to_bv 64 0x102a2) (Z_to_bv 64 0x103e6) s1 x15 x16 x17 x18 x19 x20 x21 x22 s7 x24 x25 x26 x27 x28 x29 x30
        x31) F (Z_to_bv 64 0x17f10) fc None (write_to_mem m (Z_to_bv 64 (SP + 32)) (le8 (Z_to_bv 64 0))) ro /\
      s0 = Z_to_bv 64 (P + K') /\ s7 = Z_to_bv 64 (N - K') /\
      ((K < N /\ K' = K + 1 /\ s1 = zxb b) \/ (K = N /\ K' = K /\ s1 = Z_to_bv 64 0)))
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 (Z_to_bv 64 (P + K)) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
      x21 x22 (Z_to_bv 64 (N - K)) x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13ddc) fc None m ro).
Proof.
  intros P N K SP x1 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29
    x30 x31 F fc m ro b HK HN RB HS.
  step. if_cases HC.
  - assert (HKN : K = N).
    { unfold bv_eqb in HC. rewrite !unsigned_lit in HC by lia. apply Z.eqb_eq in HC. lia. }
    step. step. step. step. step. step. step. step. step. step.
    apply evt_done. do 3 eexists. exists K. split; [reflexivity|].
    split; [f_equal; lia|]. split; [f_equal; lia|]. right. split; [exact HKN|]. split; reflexivity.
  - assert (HKN : K < N).
    { unfold bv_eqb in HC. rewrite !unsigned_lit in HC by lia. apply Z.eqb_neq in HC. lia. }
    specialize (RB HKN).
    step. step. step. step. step. step. step. step. step. step. step. step. step.
    apply evt_done. do 3 eexists. exists (K + 1). split; [reflexivity|].
    split; [f_equal; lia|]. split; [f_equal; lia|]. left. split; [exact HKN|]. split; reflexivity.
Qed.

Fixpoint op5_hit (fd : Z) (es : list rentry) : Z :=
  match es with
  | [] => 0
  | e :: es' => if re_fd e =? fd then (if re_eof e =? 0 then 1 else 0) else op5_hit fd es'
  end.

Definition op5_rec (es : list rentry) (fd op : Z) : Z := if op =? 0 then 0 else op5_hit fd es.

Fixpoint op5_mem (m : word -> option byte) (S8 : Z) (r : nat -> Z) (n : nat) : word -> option byte :=
  match n with
  | O => m
  | S n' => write_to_mem (op5_mem m S8 r n') (Z_to_bv 64 (S8 + 4 * Z.of_nat n')) (le4 (Z_to_bv 64 (r n')))
  end.

Definition op5_post (es : list rentry) (sfd sop : nat -> Z) (S8 : Z)
    (x2 x3 x4 x5 x6 x7 x8 x9 x18 x19 x21 x22 x23 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (ms : machine_state) : Prop :=
  exists a1 a2 a3 a4 a5 a6 a7 : word,
    ms = MS (mkR (Z_to_bv 64 0x13f00) x2 x3 x4 x5 x6 x7 x8 x9 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 (Z_to_bv 64 0x30fc0)
               x21 x22 x23 (Z_to_bv 64 S8) (Z_to_bv 64 4) x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13450) fc None
            (op5_mem m S8 (fun i => op5_rec es (sfd i) (sop i)) 4) ro.

Lemma op5_sl2 : forall z, 0 <= z < 2 ^ 40 -> Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 z)) 2) = Z_to_bv 64 (4 * z).
Proof. intros z Hz. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia. Qed.

Lemma op5_idx : forall i, 0 <= i < 4 ->
  Z_to_bv 64 (0x30fc0 + (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 i)) 7)) -
                         bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 i)) 5)))) =
  Z_to_bv 64 (0x30fc0 + 96 * i).
Proof.
  intros i Hi. rewrite (unsigned_lit i) by lia. rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite !unsigned_lit by lia. f_equal. lia.
Qed.

Lemma op5_seqz : forall z, 0 <= z < 2 ^ 64 -> v_sltiu (Z_to_bv 64 z) 1 = Z_to_bv 64 (if z =? 0 then 1 else 0).
Proof.
  intros z Hz. unfold v_sltiu. rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.eqb_spec z 0), (Z.ltb_spec z 1); try lia; reflexivity.
Qed.

Lemma op5_len : forall es, Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\ 0 <= re_fd e < 2 ^ 31 /\
                   (re_eof e = 0 \/ re_eof e = 1)) es ->
  length (concat (map entry_bytes es)) = (56 * length es)%nat.
Proof.
  induction es as [|e es IH]; intros H; [reflexivity|]. apply Forall_cons_iff in H. destruct H as [(P1 & P2 & _) H].
  cbn [map concat length]. rewrite length_app, p2_entry_len by assumption. rewrite IH by assumption. lia.
Qed.

Lemma op5_mem_keep : forall m S8 r n A bs, (n <= 4)%nat -> 0 <= S8 -> S8 + 16 <= 2 ^ 64 ->
  (S8 + 16 <= A \/ A + Z.of_nat (length bs) <= S8) ->
  bytes_at rsegs m A bs -> bytes_at rsegs (op5_mem m S8 r n) A bs.
Proof.
  intros m S8 r n. induction n as [|n IH]; intros A bs Hn H0 H1 HD HB; cbn [op5_mem]; [exact HB|].
  apply bytes_at_write_other; [apply IH; [lia|lia|lia|exact HD|exact HB] | lia | rewrite length_le4; lia
                              | rewrite length_le4; lia].
Qed.

Lemma op5_mem_wr : forall m S8 r n, wr_at rsegs m S8 16 -> wr_at rsegs (op5_mem m S8 r n) S8 16.
Proof. intros m S8 r n H. induction n as [|n IH]; cbn [op5_mem]; [exact H|]. apply wr_at_write. exact IH. Qed.

Lemma op5_slot_rd : forall m i fd op, bytes_at rsegs m (G_S + 96 * i) (le4 (Z_to_bv 64 fd) ++ le4 (Z_to_bv 64 op)) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (0x30fc0 + 96 * i + 128)) 4 = Some (le4 (Z_to_bv 64 fd)) /\
  ov_read_bytes rsegs m (Z_to_bv 64 (0x30fc0 + 96 * i + 132)) 4 = Some (le4 (Z_to_bv 64 op)).
Proof.
  intros m i fd op H. apply bytes_at_app in H. destruct H as [H1 H2]. rewrite length_le4 in H2. split.
  - replace (0x30fc0 + 96 * i + 128) with (G_S + 96 * i) by (unfold G_S; lia). apply p2_rd4. exact H1.
  - replace (0x30fc0 + 96 * i + 132) with (G_S + 96 * i + Z.of_nat 4) by (unfold G_S; lia). apply p2_rd4. exact H2.
Qed.

Lemma op5_scan : forall (rest : list rentry) (K fd n : Z)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  rest <> [] -> n = Z.of_nat (length rest) -> n < 2 ^ 31 ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\ 0 <= re_fd e < 2 ^ 31 /\
                   (re_eof e = 0 \/ re_eof e = 1)) rest ->
  bytes_at rsegs m K (concat (map entry_bytes rest)) -> 0 <= fd < 2 ^ 31 ->
  evt rsegs (fun ms => exists a6 a7 : word,
      ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 (Z_to_bv 64 (op5_hit fd rest)) (Z_to_bv 64 fd) a6 a7
        x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13ed4) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 (Z_to_bv 64 (K + 4)) (Z_to_bv 64 fd) (Z_to_bv 64 n) x17
      x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13ebc) fc None m ro).
Proof.
  induction rest as [|e rest IH];
    intros K fd n x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
      x30 x31 F fc m ro Hne Hn HN HW HB Hfd; [congruence|].
  apply Forall_cons_iff in HW. destruct HW as [(P1 & P2 & Rfd & Reof) HW].
  destruct (p2_head m K e rest P1 P2 HB) as (BF & BE & BR).
  cbn [length] in Hn.
  pose proof (p2_rd4 m K _ BF) as RF.
  pose proof (p2_rd4 m (K + 4) _ BE) as RE.
  step. rewrite (ls_sx32 (re_fd e)) by lia.
  step.
  destruct (Z.eq_dec (re_fd e) fd) as [Hq|Hq].
  - rewrite Hq. if_true.
    step. rewrite (ls_sx32 (re_eof e)) by lia.
    step. rewrite op5_seqz by lia.
    step.
    apply evt_done. exists (Z_to_bv 64 n), (Z_to_bv 64 fd). cbn [op5_hit]. rewrite Hq, Z.eqb_refl. reflexivity.
  - if_false_by (eq_trans (p2_eqb (re_fd e) fd ltac:(lia) ltac:(lia)) (proj2 (Z.eqb_neq _ _) Hq)).
    step. step. step.
    if_cases HC; rewrite p2_eqb in HC by lia.
    + apply Bool.negb_true_iff, Z.eqb_neq in HC. destruct rest as [|e2 rest2]; [cbn [length] in Hn; lia|].
      replace (op5_hit fd (e :: e2 :: rest2)) with (op5_hit fd (e2 :: rest2))
        by (cbn [op5_hit]; rewrite (proj2 (Z.eqb_neq _ _) Hq); reflexivity).
      replace (Z_to_bv 64 (K + 60)) with (Z_to_bv 64 (K + 56 + 4)) by (f_equal; lia).
      apply (IH (K + 56) fd (n + -1));
        first [ discriminate | exact HW | exact BR | exact Hfd | (cbn [length] in Hn |- *; lia) ].
    + apply Bool.negb_false_iff, Z.eqb_eq in HC. destruct rest as [|e2 rest2]; [|cbn [length] in Hn; lia].
      step. apply evt_done. exists (Z_to_bv 64 (n + -1)), (Z_to_bv 64 (re_fd e)). cbn [op5_hit].
      rewrite (proj2 (Z.eqb_neq _ _) Hq). reflexivity.
Qed.

Lemma op5_body : forall (es : list rentry) (i G fd op : Z)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  0 <= i < 4 -> Z.of_nat (length es) < 2 ^ 31 ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\ 0 <= re_fd e < 2 ^ 31 /\
                   (re_eof e = 0 \/ re_eof e = 1)) es ->
  bytes_at rsegs m G (concat (map entry_bytes es)) ->
  bytes_at rsegs m (G_S + 96 * i) (le4 (Z_to_bv 64 fd) ++ le4 (Z_to_bv 64 op)) ->
  0 <= fd < 2 ^ 31 -> 0 <= op < 2 ^ 31 ->
  evt rsegs (fun ms => exists a5 a6 a7 : word,
      ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 i) (Z_to_bv 64 (Z.of_nat (length es)))
        (Z_to_bv 64 (Z.of_nat (length es))) (Z_to_bv 64 (G + 4)) (Z_to_bv 64 (op5_rec es fd op)) a5 a6 a7 x18 x19
        (Z_to_bv 64 0x30fc0) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13ed4) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 i) (Z_to_bv 64 (Z.of_nat (length es)))
      (Z_to_bv 64 (Z.of_nat (length es))) (Z_to_bv 64 (G + 4)) x14 x15 x16 x17 x18 x19 (Z_to_bv 64 0x30fc0) x21 x22
      x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13e94) fc None m ro).
Proof.
  intros es i G fd op x1 x2 x3 x4 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m ro HI HC HW HB HS Hfd Hop.
  destruct (op5_slot_rd m i fd op HS) as [RF RO].
  step. step. step. step. rewrite (op5_idx i) by lia.
  step. rewrite (ls_sx32 op) by lia.
  step. if_cases H0; rewrite p2_eqb in H0 by lia.
  - step. apply evt_done. unfold op5_rec. rewrite H0. do 3 eexists. reflexivity.
  - step. rewrite p2_lts0 by lia. if_cases H1.
    + apply Bool.negb_true_iff, Z.ltb_ge in H1. destruct es as [|e0 es0]; [|cbn [length] in H1; lia].
      step. apply evt_done. unfold op5_rec. rewrite H0. do 3 eexists. reflexivity.
    + apply Bool.negb_false_iff, Z.ltb_lt in H1.
      assert (NE : es <> []) by (destruct es as [|e0 es0]; [cbn [length] in H1; lia|discriminate]).
      step. rewrite (ls_sx32 fd) by lia.
      step. step.
      eapply evt_mono.
      { apply (op5_scan es G fd (Z.of_nat (length es)));
          first [ exact NE | reflexivity | exact HW | exact HB | exact Hfd | lia ]. }
      intros ms' (a6 & a7 & ->). unfold op5_rec. rewrite H0. exists (Z_to_bv 64 fd), a6, a7. reflexivity.
Qed.

Lemma op5_loop : forall (k i : nat) (es : list rentry) (G S8 : Z) (sfd sop : nat -> Z)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x21 x22 x23 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  (i + k = 4)%nat -> (0 < k)%nat -> Z.of_nat (length es) < 2 ^ 31 ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\ 0 <= re_fd e < 2 ^ 31 /\
                   (re_eof e = 0 \/ re_eof e = 1)) es ->
  bytes_at rsegs m G (concat (map entry_bytes es)) ->
  (forall j, (j < 4)%nat ->
     bytes_at rsegs m (G_S + 96 * Z.of_nat j) (le4 (Z_to_bv 64 (sfd j)) ++ le4 (Z_to_bv 64 (sop j)))) ->
  (forall j, (j < 4)%nat -> 0 <= sfd j < 2 ^ 31 /\ 0 <= sop j < 2 ^ 31) ->
  wr_at rsegs m S8 16 ->
  (S8 + 16 <= G \/ G + 56 * Z.of_nat (length es) <= S8) ->
  (S8 + 16 <= G_S \/ G_S + 384 <= S8) ->
  evt rsegs (op5_post es sfd sop S8 x2 x3 x4 x5 x6 x7 x8 x9 x18 x19 x21 x22 x23 x26 x27 x28 x29 x30 x31 F fc m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length es)))
      (Z_to_bv 64 (Z.of_nat (length es))) (Z_to_bv 64 (G + 4)) x14 x15 x16 x17 x18 x19 (Z_to_bv 64 0x30fc0) x21 x22
      x23 (Z_to_bv 64 S8) (Z_to_bv 64 4) x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13e94) fc None
      (op5_mem m S8 (fun j => op5_rec es (sfd j) (sop j)) i) ro).
Proof.
  induction k as [|k IH];
    intros i es G S8 sfd sop x1 x2 x3 x4 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x21 x22 x23 x26 x27 x28 x29 x30 x31
      F fc m ro Hik Hk HC HW HB HSL HSB WR DG DS; [lia|].
  assert (Hi : (i < 4)%nat) by lia.
  pose proof (op5_len es HW) as HL.
  destruct (HSB i Hi) as [Hfd Hop].
  pose proof WR as (W0 & W1 & _).
  eapply evt_cut.
  { apply (op5_body es (Z.of_nat i) G (sfd i) (sop i) x1 x2 x3 x4 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x21 x22 x23
      (Z_to_bv 64 S8) (Z_to_bv 64 4) x26 x27 x28 x29 x30 x31 F fc
      (op5_mem m S8 (fun j => op5_rec es (sfd j) (sop j)) i) ro); try lia; try exact HW.
    - apply op5_mem_keep; [lia|lia|lia| |exact HB]. rewrite HL. lia.
    - apply op5_mem_keep; [lia|lia|lia| |exact (HSL i Hi)].
      rewrite length_app, !length_le4. unfold G_S in *. lia. }
  intros ms' (a5 & a6 & a7 & ->).
  pose proof (wr_at_store_ok rsegs (op5_mem m S8 (fun j => op5_rec es (sfd j) (sop j)) i) S8 16 (4 * Z.of_nat i) 4
    (op5_mem_wr m S8 _ i WR) ltac:(lia) ltac:(change (Z.of_nat 4) with 4; lia)) as HS.
  step. rewrite (op5_sl2 (Z.of_nat i)) by lia.
  step. step. step. step.
  if_cases HE; rewrite p2_eqb in HE by lia.
  - apply Bool.negb_true_iff, Z.eqb_neq in HE.
    replace (Z_to_bv 64 (Z.of_nat i + 1)) with (Z_to_bv 64 (Z.of_nat (S i))) by (f_equal; lia).
    apply (IH (S i) es G S8 sfd sop);
      first [ exact HW | exact HB | exact HSL | exact HSB | exact WR | exact DG | exact DS | lia ].
  - apply Bool.negb_false_iff, Z.eqb_eq in HE. assert (E3 : i = 3%nat) by lia. subst i.
    step. step. step. apply evt_done. unfold op5_post. do 7 eexists. reflexivity.
Qed.

Lemma op5_seg_b : forall (es : list rentry) (tail : list byte) (G S8 : Z) (sfd sop : nat -> Z)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  ov_read_bytes rsegs m (Z_to_bv 64 0x30fd8) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat (length es)))) ->
  ov_read_bytes rsegs m (Z_to_bv 64 0x30ff0) 8 = Some (le8 (Z_to_bv 64 G)) ->
  rw_cells rsegs m G [CB 896 (concat (map entry_bytes es) ++ tail)] ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\ 0 <= re_fd e < 2 ^ 31 /\
                   (re_eof e = 0 \/ re_eof e = 1)) es ->
  (forall i, (i < 4)%nat ->
     rw_cells rsegs m (G_S + 96 * Z.of_nat i) [C4 (Z_to_bv 64 (sfd i)); C4 (Z_to_bv 64 (sop i))]) ->
  (forall i, (i < 4)%nat -> 0 <= sfd i < 2 ^ 31 /\ 0 <= sop i < 2 ^ 31) ->
  wr_at rsegs m S8 16 ->
  S8 + 16 <= G \/ G + 896 <= S8 ->
  S8 + 16 <= G_S \/ G_S + 384 <= S8 ->
  evt rsegs (op5_post es sfd sop S8 x2 x3 x4 x5 x6 x7 x8 x9 x18 x19 x21 x22 x23 x26 x27 x28 x29 x30 x31 F fc m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 0x30fc0) x21 x22 x23
      (Z_to_bv 64 S8) (Z_to_bv 64 4) x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13e80) fc None m ro).
Proof.
  intros es tail G S8 sfd sop x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x26 x27
    x28 x29 x30 x31 F fc m ro RN RG TB HW HSL HSB WR DG DS.
  pose proof (op5_len es HW) as HL.
  destruct TB as [[TW HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  cbn [cells_wf cell_wf] in TW. destruct TW as [TL _]. rewrite length_app, HL in TL.
  apply bytes_at_app in HB. destruct HB as [HB _].
  assert (HSB' : forall j, (j < 4)%nat ->
    bytes_at rsegs m (G_S + 96 * Z.of_nat j) (le4 (Z_to_bv 64 (sfd j)) ++ le4 (Z_to_bv 64 (sop j)))).
  { intros j Hj. destruct (HSL j Hj) as [[_ HJ] _]. cbn [cells_bytes cbytes] in HJ. rewrite app_nil_r in HJ.
    exact HJ. }
  step. step. rewrite DA_Myrk.zx32_small by lia.
  step. step. rewrite (unsigned_lit (Z.of_nat (length es))) by lia. rewrite DA_Myrk.swrap32_small0 by lia.
  step.
  apply (op5_loop 4 0 es G S8 sfd sop);
    first [ exact HW | exact HB | exact HSB' | exact HSB | exact WR | exact DS | lia ].
Qed.
