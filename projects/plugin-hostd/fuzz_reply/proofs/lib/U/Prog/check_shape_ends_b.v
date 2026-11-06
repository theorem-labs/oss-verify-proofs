From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import has_prefix_c next_line_c list_find_c RelayModel HarnessRep CheckRep check_shape_ends_a.
Import ListNotations.
Open Scope Z_scope.

Lemma ce_g2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (i : Z),
  s3 = Z_to_bv 64 i -> 0 <= i < 2 ^ 26 ->
  evt rsegs (fun ms' =>
      (0 < i /\ ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                              t3 t4 t5 t6)
                         F (Z_to_bv 64 0x14b4c) fc None m (seg_rom rsegs)) \/
      (i = 0 /\ ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                              t3 t4 t5 t6)
                         F (Z_to_bv 64 0x14ba0) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14b9c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    i -> Hi.
  step. if_cases Q.
  - zify_cond Q. apply evt_done. left. split; [lia | reflexivity].
  - zify_cond Q. apply evt_done. right. split; [lia | reflexivity].
Qed.

Lemma ce_e2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (w : Z),
  s8 = Z_to_bv 64 (w - 1) -> 1 <= w < 2 ^ 26 ->
  evt rsegs (fun ms' =>
      (1 < w /\ ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (w - 2)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4
                              (Z_to_bv 64 (w - 1)) s6 s7 (Z_to_bv 64 (w - 2)) s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x14bf4) fc None m (seg_rom rsegs)) \/
      (w = 1 /\ ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (w - 2)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4
                              (Z_to_bv 64 (w - 1)) s6 s7 (Z_to_bv 64 (w - 1)) s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x14ba0) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14c88) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    w -> Hw.
  step. rewrite (unsigned_lit (w - 1)), ce_swrap by lia. replace (w - 1 + -1) with (w - 2) by lia.
  step. step. if_cases Q; [|exfalso; unfold bv_lts in Q; rewrite !ce_signed in Q by lia; zify_bool Q; lia].
  step. if_cases Q2.
  - zify_cond Q2. apply evt_done. right. split; [lia | reflexivity].
  - zify_cond Q2. step. apply evt_done. left. split; [lia | reflexivity].
Qed.

Lemma ce_g1 : has_prefix_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo V N CAP i q : Z) (S P slack : list byte),
  rw_cells rsegs m (bv_unsigned s1) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 CAP)] ->
  ro_cells rsegs m (V + 16 * i) [C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 (Z.of_nat (length S)))] ->
  bytes_at rsegs m q S -> 0 <= q -> q + Z.of_nat (length S) < 2 ^ 64 ->
  0 <= i < 2 ^ 26 -> 0 < V -> V mod 8 = 0 -> V + 16 * i + 16 <= 2 ^ 64 ->
  bytes_at rsegs m (bv_unsigned s0) (P ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) P ->
  (- (bv_unsigned s0 + Z.of_nat (length P) + 1)) mod 8 <= Z.of_nat (length slack) ->
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp ->
  (q + Z.of_nat (length S) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= q) ->
  (bv_unsigned s0 + Z.of_nat (length P + 1 + length slack) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned s0) ->
  s3 = Z_to_bv 64 (i + 1) ->
  evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      stk rsegs m' lo (bv_unsigned sp) /\
      ((prefix_of P S /\
        ms' = MS (mkR (Z_to_bv 64 0x14b9c) sp gp tp t0' t1' t2' s0 s1 s1 (Z_to_bv 64 i) a2' a3' a4' a5' a6' a7'
                      s2 (Z_to_bv 64 i) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x14d58) fc None m' (seg_rom rsegs)) \/
       (~ prefix_of P S /\ 0 < i /\
        ms' = MS (mkR (Z_to_bv 64 0x14b8c) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                      s2 (Z_to_bv 64 i) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x14b4c) fc None m' (seg_rom rsegs)) \/
       (~ prefix_of P S /\ i = 0 /\
        ms' = MS (mkR (Z_to_bv 64 0x14b8c) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                      s2 (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x14ba0) fc None m' (seg_rom rsegs))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14b4c) fc None m (seg_rom rsegs)).
Proof.
  intros HP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo V N CAP i q S P slack HC RC HS Hq0 Hq1 Hi HV0 HV8 HV1 HPB NZ SL MI ST LO D1 D2 ->.
  pose proof (zr_word s0) as R0. unfold inr64 in R0.
  pose proof (zr_word s1) as R1. unfold inr64 in R1.
  step. step. rewrite (unsigned_lit (i + 1)), ce_swrap by lia. replace (i + 1 + -1) with i by lia.
  step. rewrite ce_shl4 by lia. step.
  remember (V + 16 * i) as R eqn:ER.
  step. ce_trap.
  step. rewrite (ce_sltu_pos (Z_to_bv 64 V)) by (rewrite unsigned_lit; lia).
  step. rewrite (ce_sltiu1 (Z_to_bv 64 R)) by (rewrite unsigned_lit; lia).
  step. step. ce_if.
  step. ce_trap.
  step. step. ce_trap.
  step. step. step. step.
  assert (Uq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (UL : bv_unsigned (Z_to_bv 64 (Z.of_nat (length S))) = Z.of_nat (length S)) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply HP with (lo := lo) (S := S) (P := P) (slack := slack); rewrite ?Uq, ?UL;
      [exact HS | reflexivity | exact HPB | exact NZ | exact SL | exact MI | exact ST | unfold HAS_PREFIX_K; lia
      | unfold HAS_PREFIX_K; exact D1 | unfold HAS_PREFIX_K; exact D2]. }
  intros ms1 (u0 & u1 & u2 & b0 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m1 &
    -> & MU1 & WM1 & MI1 & ST1 & PR).
  unfold HAS_PREFIX_K in MU1.
  replace (ret_pc (Z_to_bv 64 0x14b8c)) with (Z_to_bv 64 0x14b8c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct PR as [(PO & ->)|(PO & ->)].
  - step. ce_if. step. step. step.
    apply evt_done. do 3 eexists. exists u3. do 11 eexists.
    split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|].
    split; [exact ST1|]. left. split; [exact PO | reflexivity].
  - step. ce_if. step. if_cases Q2.
    + zify_cond Q2. apply evt_done. do 15 eexists. split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|].
      split; [exact ST1|]. right. left. split; [exact PO|]. split; [lia | reflexivity].
    + zify_cond Q2. assert (Hi0 : i = 0) by lia. subst i.
      apply evt_done. do 15 eexists. split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|].
      split; [exact ST1|]. right. right. split; [exact PO|]. split; reflexivity.
Qed.
