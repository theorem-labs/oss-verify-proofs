(* walks of the prologue and the epilogue of fuzz_frame's LLVMFuzzerTestOneInput in fuzz_frame.ubsan, on Exec.evt. *)
(* LLVMFuzzerTestOneInput (fuzz_frame.c:265-284) in fuzz_frame.ubsan, 0x12d48: the prologue up to the call of
   malloc (0x12d48-0x12d74) and the return after the call of free (0x12fdc-0x12ff4). The frame is 176 bytes
   (addi sp, sp, -0xb0); ra, s0, s1 and s2 are saved at sp + 0xa8, 0xa0, 0x98 and 0x90, that is the cells
   [s2; s1; s0; ra] at sp + 144. These instructions have no UBSan check. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(* The size test is not taken below 2 ^ 26. *)
Lemma lt_a_cond : forall u, 0 <= u < 2 ^ 26 ->
  negb (bv_eqb (Z_to_bv 64 (Z.shiftr u 26)) (Z_to_bv 64 0)) = false.
Proof.
  intros u Hu. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

(* Drop a prefix of a cell list. *)
Lemma lt_rw_cells_tail : forall segs m A pre post,
  rw_cells segs m A (pre ++ post) -> rw_cells segs m (A + Z.of_nat (cells_size pre)) post.
Proof.
  intros segs m A pre post [[Hwf Hb] (Ha & Hn & Hw)].
  apply cells_wf_app in Hwf as [Hw1 Hw2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [_ Hb2].
  rewrite cells_bytes_length in Hb2 by exact Hw1.
  rewrite cells_size_app in Hn, Hw.
  split; [split; [exact Hw2 | exact Hb2]|].
  split; [lia|]. split; [lia|]. intros i Hi.
  replace (A + Z.of_nat (cells_size pre) + i) with (A + (Z.of_nat (cells_size pre) + i)) by lia.
  apply Hw. lia.
Qed.

(* seqz on a value below 2 ^ 64. *)
Lemma lt_seqz : forall n, 0 <= n < 2 ^ 64 ->
  bv_unsigned (v_sltiu (Z_to_bv 64 n) 1) = if n =? 0 then 1 else 0.
Proof.
  intros n Hn. unfold v_sltiu. rewrite (unsigned_lit n) by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.eqb_spec n 0) as [E|E].
  - subst n. vm_compute. reflexivity.
  - replace (n <? 1) with false by (symmetry; apply Z.ltb_ge; lia). vm_compute. reflexivity.
Qed.

(* 0x12d48-0x12d74: the frame, the size test (size < 2 ^ 26 here), s1 = data, s2 = size,
   a0 = size + (size == 0), then jal malloc. *)
Lemma lt_a :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo n : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 176 <= bv_unsigned sp -> mem_inv rsegs m ->
    a1 = Z_to_bv 64 n -> 0 <= n < 2 ^ 26 ->
    evt rsegs
      (fun ms' => exists (a1' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x12d78) (Z_to_bv 64 (bv_unsigned sp - 176)) gp tp t0 t1 t2 s0 a0
                       (Z_to_bv 64 (n + (if n =? 0 then 1 else 0))) a1' a2 a3 a4 a5 a6 a7 (Z_to_bv 64 n)
                       s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x14f2c) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 176, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         rw_cells rsegs m' (bv_unsigned sp - 32) [C8 s2; C8 s1; C8 s0; C8 ra])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12d48) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo n ST LO MI -> Hn.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  carve_frame 176%nat ST.
  do 8 step.
  rewrite (unsigned_lit n) by lia.
  if_false_by (lt_a_cond n Hn).
  do 4 step.
  rewrite (lt_seqz n ltac:(lia)).
  pose proof (lt_rw_cells_tail rsegs m1 _ [_] _ FR) as FR2. cbn [cells_size csize Nat.add] in FR2.
  replace (bv_unsigned sp + -176 + Z.of_nat 144) with (bv_unsigned sp - 32) in FR2 by lia.
  finish.
Qed.

(* 0x12fdc-0x12ff4: a0 = 0, ra, s0, s1, s2 back from the cells at sp + 144, the frame released, ret. *)
Lemma lt_d :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (vra vs0 vs1 vs2 : word),
    rw_cells rsegs m (bv_unsigned sp + 144) [C8 vs2; C8 vs1; C8 vs0; C8 vra] ->
    bv_unsigned sp + 176 < 2 ^ 64 ->
    evt rsegs
      (fun ms' => exists a0' : word,
         a0' = Z_to_bv 64 0 /\
         ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 176)) gp tp t0 t1 t2 vs0 vs1 a0' a1 a2 a3 a4 a5 a6 a7
                       vs2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc vra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12fdc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m vra vs0 vs1 vs2 HC Hsp.
  do 7 step.
  apply evt_done. exists (Z_to_bv 64 0). split; reflexivity.
Qed.
