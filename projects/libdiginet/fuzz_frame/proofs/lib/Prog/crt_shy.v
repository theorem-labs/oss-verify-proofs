(* The segment crt_shy of check_round_trip in fuzz_frame.plain, stated in crt_defs.v: from
   0x13464 (after the malloc of shy) to the jal of free at 0x134c4. memset fills the n_want - 1
   bytes of shy with 0x5a; diginet_frame_build with the cap n_want - 1 answers -5 (SPACE) and
   writes no byte of shy; the loop at 0x134ac reads each byte of shy and finds 0x5a.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac
  Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog Require Import check_parse_fields_c memset_c
  diginet_frame_build_c crt_defs.
Import ListNotations.
Open Scope Z_scope.

Ltac shy_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.

Ltac shy_usub :=
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia end.

Ltac shy_usub_in H :=
  repeat match type of H with context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) in H by lia end.

Ltac shy_w := shy_usub; first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; f_equal; lia ].

(* Decide a branch whose condition the context fixes. *)
Ltac shy_take b :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b; [cbv iota | symmetry; unfold_cond; shy_usub; fold_lit_ux; solve_cond_rec]
  end.

(* Decide a branch whose condition is a closed term. *)
Ltac shy_takec b :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b by (vm_compute; reflexivity); cbv iota
  end.

Ltac shy_lits :=
  repeat match goal with
  | |- context [Z.add ?a ?b] => is_Zlit a; is_Zlit b;
      let v := eval vm_compute in (a + b) in change (a + b) with v
  end.

(* sub_fp of two footprints, by arithmetic. *)
Ltac shy_sfp LOJ :=
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [outside] in *; rewrite ?LOJ in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat split; lia.

(** * Bytes *)

Lemma shy_ba_sub : forall m a (l : list byte) k len, bytes_at rsegs m a l -> (k + len <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn len (skipn k l)).
Proof.
  intros m a l k len H Hk.
  rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length l)) with k in H by lia.
  rewrite <- (firstn_skipn len (skipn k l)) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

(* The 12 bytes at sp + 0x1c of the frame cells. *)
Lemma shy_hb_at : forall m A (j h : list byte) sv,
  rw_cells rsegs m A (CB 28 j :: CB 12 h :: sv) -> bytes_at rsegs m (A + 28) h.
Proof.
  intros m A j h sv [[WF BA] _].
  cbn [cells_wf cell_wf] in WF. destruct WF as (Lj & Lh & _).
  cbn [cells_bytes cbytes] in BA.
  apply bytes_at_app in BA. destruct BA as [_ BA]. rewrite Lj in BA.
  apply bytes_at_app in BA. exact (proj1 BA).
Qed.

Lemma shy_f1_rep : forall (x : byte) N k, (k < N)%nat -> firstn 1 (skipn k (repeat x N)) = [x].
Proof.
  intros x N k. revert N. induction k as [|k IH]; intros [|N] Hk; try lia.
  - reflexivity.
  - change (skipn (S k) (repeat x (S N))) with (skipn k (repeat x N)). apply IH. lia.
Qed.

Lemma shy_rd_rep : forall m A (x : byte) N jj, bytes_at rsegs m A (repeat x N) -> 0 <= jj < Z.of_nat N ->
  ov_read_bytes rsegs m (wa (A + jj)) 1 = Some [x].
Proof.
  intros m A x N jj H Hj.
  rewrite (bytes_at_read rsegs m A (repeat x N) jj 1 H) by (rewrite ?repeat_length; lia).
  rewrite shy_f1_rep by lia. reflexivity.
Qed.

(** * The loop 0x134ac .. 0x134bc, then mv a0, s4 and jal free *)

Definition shy_end (sp gp tp s1 s2 s6 : word) (F : bvmap 5 word) (fc : bv 32) (shy : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    ms' = MS (mkR (Z_to_bv 64 0x134c8) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 shy) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
               s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 CRT_FREE) fc None m (seg_rom rsegs).

(* i bytes read, S k left: a0 = shy + i, s3 = S k, s4 = shy, s0 = 0x5a. *)
Lemma shy_loop : forall (sp gp tp s1 s2 s6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (shy N : Z),
  0 < shy -> shy + N < 2 ^ 64 ->
  (forall jj, 0 <= jj < N -> ov_read_bytes rsegs m (wa (shy + jj)) 1 = Some [b8 0x5a]) ->
  forall (k i : nat) (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (v0 v3 v4 v8 : Z),
  Z.of_nat (i + S k) = N -> v0 = shy + Z.of_nat i -> v3 = Z.of_nat (S k) -> v4 = shy -> v8 = 0x5a ->
  evt rsegs (shy_end sp gp tp s1 s2 s6 F fc shy m)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 v8) s1 (Z_to_bv 64 v0) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 v3)
             (Z_to_bv 64 v4) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x134ac) fc None m (seg_rom rsegs)).
Proof.
  intros sp gp tp s1 s2 s6 F fc m shy N H0 H1 RD k.
  induction k as [|k IH]; intros i ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 v0 v3 v4 v8
    Hk -> -> -> ->.
  - pose proof (RD (Z.of_nat i) ltac:(lia)) as HR.
    step. step. shy_takec false.
    step. step. step. shy_takec false.
    step. step.
    apply evt_done. unfold shy_end. do 23 eexists. f_equal; shy_regs; shy_w.
  - pose proof (RD (Z.of_nat i) ltac:(lia)) as HR.
    step. step. shy_takec false.
    step. step. step. shy_take true.
    shy_lits.
    eapply (IH (S i)); lia.
Qed.

(** * 0x13464 .. jal free (0x134c4) *)

Theorem crt_shy_ok : crt_shy_stmt.
Proof.
  unfold crt_shy_stmt.
  intros HMS HFB ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    w buf shy want out n b j sv HC HL HN HOK LAY RO BA STY STK HSV FR MI.
  destruct (fr_body_len_ok b HC) as (BL0 & PL0 & BLe).
  assert (NB : Z.of_nat (length (fr_body b)) = fr_body_len b) by (rewrite (length_fr_body b HC); lia).
  unfold crt_ok in HOK. apply andb_prop in HOK. destruct HOK as [HOK1 HOK2].
  apply Z.leb_le in HOK1. apply negb_true_iff in HOK2.
  assert (BC5 : build_code (fr_body b) (n - 1) = -5).
  { unfold build_code. rewrite HOK2.
    destruct (1484 <? Z.of_nat (length (fr_body b))) eqn:E1; [apply Z.ltb_lt in E1; lia|].
    destruct (n - 1 <? frame_len (length (fr_body b))) eqn:E2; [reflexivity|].
    apply Z.ltb_ge in E2. rewrite <- HN in E2. lia. }
  assert (N60 : 60 <= n) by (rewrite HN; unfold frame_len; lia).
  destruct LAY as (LB0 & LB1 & LS0 & LS1 & LD & LW0 & LW1).
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (LOJ : Z.of_nat (length (repeat (b8 0x5a) (Z.to_nat (n - 1)))) = n - 1) by (rewrite repeat_length; lia).
  assert (RS : 0 <= fr_send b < 2 ^ 32) by apply be32_range.
  assert (RA : 0 <= fr_ack b < 2 ^ 32) by apply be32_range.
  assert (RR : 0 <= fr_retry b < 2 ^ 16) by apply be16_range.
  assert (RC : 0 <= fr_cmd b < 2 ^ 8) by apply at8_range.
  assert (RN : 0 <= fr_ncmds b < 2 ^ 8) by apply at8_range.
  assert (LD6 : length (fr_dst b) = 6%nat) by (unfold fr_dst; rewrite length_firstn; lia).
  assert (LS6 : length (fr_src b) = 6%nat) by (unfold fr_src; rewrite length_firstn, length_skipn; lia).
  (* 0x13464 beqz a0: shy is not 0 *)
  step. shy_take false.
  (* mv s4, a0; li a1, 0x5a; li s0, 0x5a; mv a2, s3; jal memset *)
  do 5 step.
  destruct (stk_carve rsegs m shy (shy + (n - 1)) (Z.to_nat (n - 1)) STY ltac:(lia)) as [_ [junk FRS]].
  replace (shy + (n - 1) - Z.of_nat (Z.to_nat (n - 1))) with shy in FRS by lia.
  eapply evt_cut.
  { eapply HMS with (junk := junk).
    - shy_usub. match goal with |- rw_cells _ _ _ [CB (Z.to_nat ?x) _] => replace x with (n - 1) by lia end.
      exact FRS.
    - exact MI. }
  intros ms1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> &
    MU1 & WM1 & MI1 & RW1).
  rewrite ret_pc_even by first [lia | reflexivity].
  shy_usub_in MU1. shy_usub_in RW1.
  assert (RW1' : rw_cells rsegs m1 shy [CB (Z.to_nat (n - 1)) (repeat (b8 0x5a) (Z.to_nat (n - 1)))]).
  { match type of RW1 with rw_cells _ _ _ [CB (Z.to_nat ?x) (repeat (Z_to_bv 8 ?y) _)] =>
      replace x with (n - 1) in RW1 by lia;
      replace (Z_to_bv 8 y) with (b8 0x5a) in RW1 by (vm_compute; reflexivity) end.
    exact RW1. }
  clear RW1.
  assert (FR1 : rw_cells rsegs m1 (bv_unsigned sp) (CB 28 j :: CB 12 (crt_hb b) :: sv)).
  { apply (rw_cells_transport rsegs _ m m1 _ _ FR MU1 WM1). cbn [disjoint_from cells_size csize]. rewrite HSV.
    repeat split; lia. }
  assert (RO1 : ro_cells rsegs m1 w (spec_cells buf b)).
  { apply (ro_cells_transport rsegs _ m m1 _ _ RO MU1). change (cells_size (spec_cells buf b)) with 80%nat.
    cbn [disjoint_from]. repeat split; lia. }
  assert (BA1 : bytes_at rsegs m1 buf b).
  { apply (bytes_at_transport rsegs _ m m1 _ _ BA MU1). cbn [disjoint_from]. repeat split; lia. }
  assert (STK1 : stk rsegs m1 (bv_unsigned sp - 240) (bv_unsigned sp)).
  { apply (stk_transport_disjoint rsegs _ m m1 _ _ STK MU1 WM1). cbn [disjoint_from]. repeat split; lia. }
  assert (BD : bytes_at rsegs m1 buf (fr_dst b)).
  { unfold fr_dst. pose proof (shy_ba_sub m1 buf b 0 6 BA1 ltac:(lia)) as H. cbn [skipn] in H.
    replace (buf + Z.of_nat 0) with buf in H by lia. exact H. }
  assert (BS : bytes_at rsegs m1 (buf + 6) (fr_src b)).
  { unfold fr_src. exact (shy_ba_sub m1 buf b 6 6 BA1 ltac:(lia)). }
  assert (BB : bytes_at rsegs m1 (buf + 30) (fr_body b)).
  { unfold fr_body. exact (shy_ba_sub m1 buf b 30 (Z.to_nat (fr_body_len b)) BA1 ltac:(lia)). }
  assert (BH : bytes_at rsegs m1 (bv_unsigned sp + 24 + 4) (crt_hb b)).
  { replace (bv_unsigned sp + 24 + 4) with (bv_unsigned sp + 28) by lia. exact (shy_hb_at m1 _ j (crt_hb b) sv FR1). }
  unfold spec_cells in RO1.
  (* ld a2, a3, a5, a6 from w; addi a4, sp, 0x18; mv a0, s4; mv a1, s3; li a7, 0; jal diginet_frame_build *)
  do 9 step.
  eapply evt_eq; [ | eapply evt_cut; [ eapply HFB with (sp := sp) (m := m1) (out := shy) (dst := buf)
      (src := buf + 6) (hp := bv_unsigned sp + 24) (body := buf + 30) (mode := 0) (lo := bv_unsigned sp - 240)
      (send := fr_send b) (ack := fr_ack b) (retry := fr_retry b) (cmd := fr_cmd b) (ncmds := fr_ncmds b)
      (dmac := fr_dst b) (smac := fr_src b) (bb := fr_body b) (oj := repeat (b8 0x5a) (Z.to_nat (n - 1))) | ] ].
  { f_equal; shy_regs; rewrite ?LOJ, ?NB; shy_w. }
  all: try solve [ exact RS | exact RA | exact RR | exact RC | exact RN | exact LD6 | exact BD | exact LS6
                 | exact BS | exact BH | exact BB | exact STK1 | exact MI1
                 | (rewrite repeat_length; exact RW1') | (left; reflexivity) | (rewrite ?LOJ, ?NB; lia) ].
  intros ms2 (t0x & t1x & t2x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m2 & -> &
    MU2 & WM2 & MI2 & STK2 & RW2).
  rewrite ret_pc_even by first [lia | reflexivity].
  rewrite LOJ, BC5.
  (* li a1, -5; bne a0, a1: the answer is -5 *)
  step. step. shy_takec false.
  (* mv a0, s4 *)
  step.
  assert (BO : build_out (fr_dst b) (fr_src b) (fr_send b) (fr_ack b) (fr_retry b) (fr_cmd b) (fr_ncmds b)
                 (fr_body b) 0 (repeat (b8 0x5a) (Z.to_nat (n - 1))) = repeat (b8 0x5a) (Z.to_nat (n - 1))).
  { unfold build_out. cbv zeta. rewrite LOJ, BC5. reflexivity. }
  assert (RD : forall jj, 0 <= jj < n - 1 -> ov_read_bytes rsegs m2 (wa (shy + jj)) 1 = Some [b8 0x5a]).
  { intros jj Hj. destruct RW2 as [[_ HB2] _]. rewrite BO in HB2. cbn [cells_bytes cbytes] in HB2.
    rewrite app_nil_r in HB2. apply (shy_rd_rep m2 shy (b8 0x5a) (Z.to_nat (n - 1)) jj HB2). lia. }
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp) (CB 28 j :: CB 12 (crt_hb b) :: sv)).
  { apply (rw_cells_transport rsegs _ m1 m2 _ _ FR1 MU2 WM2). cbn [disjoint_from cells_size csize].
    rewrite HSV, ?LOJ. repeat split; lia. }
  shy_lits.
  eapply evt_mono.
  { eapply (shy_loop sp gp tp (Z_to_bv 64 want) (Z_to_bv 64 w) (Z_to_bv 64 out) F fc m2 shy (n - 1)
      ltac:(lia) ltac:(lia) RD (Z.to_nat (n - 1) - 1) 0).
    all: lia. }
  intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & u15 & u16 & u17 &
    u18 & u19 & u20 & u21 & u22 & ->).
  unfold crt_shy_post. do 24 eexists. split; [reflexivity|].
  split.
  { apply (munch_trans _ m m1 m2).
    - refine (munch_weaken _ _ m m1 _ MU1). shy_sfp LOJ.
    - refine (munch_weaken _ _ m1 m2 _ MU2). shy_sfp LOJ. }
  split; [exact (wmono_trans rsegs m m1 m2 WM1 WM2)|].
  split; [exact MI2 | exact FR2].
Qed.
