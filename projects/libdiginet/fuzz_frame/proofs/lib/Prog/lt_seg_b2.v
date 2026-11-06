(* Walk of fuzz_frame's LLVMFuzzerTestOneInput in fuzz_frame.plain from the return of the second memset
   (0x12d04) to the call of check_round_trip (0x13058) or of free (0x148ac), on Exec.evt
   (fuzz_frame.c:275-283). It is the inlined spec_read_frame (fuzz/spec.h:199-223) of the frame bytes b at
   buf into the struct spec_frame w at sp, then check_parse_refusal (r, w), and when w.code is SPEC_OK
   check_parse_fields (buf, f, w); check_round_trip (w) is the next call:
   - fewer than 30 bytes (0x12d08), an EtherType other than 0x885F (0x12d30), numbytes under 16
     (0x12d50) or past the buffer (0x12d58): the code -2, -3 or -4 is stored at w (0x12e6c), then
     check_parse_refusal (0x12e78), then mv a0, s0 and jal free (0x12e7c);
   - else the fields are stored, the body sum is computed by the loop 0x12e20-0x12e2c, then
     check_parse_refusal (0x12e3c), check_parse_fields (0x12e4c), and mv a0, sp; jal check_round_trip.
   w is then spec_cells buf b (check_parse_fields_c.v). check_parse_refusal and check_parse_fields are
   taken through their contracts (Section hypotheses).
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog Require Import diginet_frame_parse_c check_parse_refusal_c
  check_parse_fields_c FrameBytes lt_seg_b2_lib lt_seg_b2_tail lt_seg_b2_loop.
Import ListNotations.
Open Scope Z_scope.

Section B2.
Hypothesis CPR : check_parse_refusal_contract.
Hypothesis CPF : check_parse_fields_contract.

Lemma lt_b2 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo buf : Z) (b : list byte)
         (x1 x2 x3 x4 : word),
    stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> bv_unsigned sp + 176 < 2 ^ 63 ->
    mem_inv rsegs m ->
    s0 = Z_to_bv 64 buf -> s1 = Z_to_bv 64 (fr_code b) -> s2 = Z_to_bv 64 (Z.of_nat (length b)) ->
    Z.of_nat (length b) < 2 ^ 26 -> 4096 <= buf -> buf + Z.of_nat (length b) <= lo ->
    bytes_at rsegs m buf b ->
    rw_cells rsegs m (bv_unsigned sp) [CB 80 (repeat (b8 0) 80)] ->
    rw_cells rsegs m (bv_unsigned sp + 80)
      (if fr_code b =? 0 then parse_cells buf b (repeat (b8 0) 64) else [CB 64 (repeat (b8 0) 64)]) ->
    rw_cells rsegs m (bv_unsigned sp + 144) [C8 x1; C8 x2; C8 x3; C8 x4] ->
    evt rsegs
      (fun ms' =>
         (fr_code b = 0 /\
          exists (t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' s2' t3' t4' t5' t6' : word) (m' : word -> option byte),
            ms' = MS (mkR (Z_to_bv 64 0x12e58) sp gp tp t0' t1' t2' (Z_to_bv 64 buf) s1' sp a1' a2' a3' a4' a5' a6'
                          a7' s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 0x13058) fc None m' (seg_rom rsegs) /\
            munch [(bv_unsigned sp - 48, bv_unsigned sp + 80)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
            bytes_at rsegs m' buf b /\
            ro_cells rsegs m' (bv_unsigned sp + 80) (parse_cells buf b (repeat (b8 0) 64)) /\
            ro_cells rsegs m' (bv_unsigned sp) (spec_cells buf b) /\
            rw_cells rsegs m' (bv_unsigned sp + 144) [C8 x1; C8 x2; C8 x3; C8 x4]) \/
         (exists (t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' s2' t3' t4' t5' t6' : word) (m' : word -> option byte),
            ms' = MS (mkR (Z_to_bv 64 0x12e84) sp gp tp t0' t1' t2' (Z_to_bv 64 buf) s1' (Z_to_bv 64 buf) a1' a2' a3'
                          a4' a5' a6' a7' s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 0x148ac) fc None m' (seg_rom rsegs) /\
            munch [(bv_unsigned sp - 48, bv_unsigned sp + 80)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
            rw_cells rsegs m' (bv_unsigned sp + 144) [C8 x1; C8 x2; C8 x3; C8 x4]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12d04) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo buf b
    x1 x2 x3 x4 ST LO SPB MI -> -> -> NL BUF4 BL BB W PF SV.
  lazymatch goal with |- evt _ _ ?ms =>
    change (evt rsegs (b2_post sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m buf b x1 x2 x3 x4) ms) end.
  pose proof (bytes_at_bound _ _ _ _ BB) as BBb.
  pose proof (u64_range sp) as Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp + 80)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  apply w0_shape in W. unfold w0_cells in W.
  (* 0x12d04: size >= 30 *)
  step. step.
  destruct (Nat.ltb_spec (length b) 30) as [L30|L30].
  { b2_br false. step. step. clear PF.
    eapply b2_refuse; try eassumption; try lia. rewrite (fr_code_short b L30). reflexivity. }
  b2_br true.
  pose proof (be16_range b 12) as R12. pose proof (be16_range b 14) as R14.
  (* 0x12d14: the EtherType *)
  rdb BB 12. step. clear HR. rdb BB 13. step. clear HR.
  step. step. rewrite be16_reg. do 4 step.
  destruct (Z.eq_dec (be16 b 12) 0x885f) as [ET|ET].
  2: { b2_br true. step. clear PF.
       eapply b2_refuse; try eassumption; try lia. rewrite (fr_code_eth b L30 ET). reflexivity. }
  b2_br false.
  (* 0x12d34: numbytes *)
  rdb BB 14. step. clear HR. rdb BB 15. step. clear HR.
  do 3 step. rewrite be16_reg. do 3 step.
  destruct (Z_lt_le_dec (be16 b 14) 16) as [NB|NB].
  { b2_br true. clear PF. eapply b2_refuse; try eassumption; try lia.
    rewrite (fr_code_len b L30 ET (or_introl NB)). reflexivity. }
  b2_br false. do 2 step.
  destruct (Z_lt_le_dec (Z.of_nat (length b) - 14) (be16 b 14)) as [NL2|NL2].
  { b2_br true. clear PF. eapply b2_refuse; try eassumption; try lia.
    rewrite (fr_code_len b L30 ET (or_intror NL2)). reflexivity. }
  b2_br false.
  assert (C0 : fr_code b = 0) by exact (fr_code_zero b L30 ET NB NL2).
  replace (fr_code b =? 0) with true in PF by (rewrite C0; reflexivity). cbv iota in PF.
  (* 0x12d5c: the header fields *)
  rdb BB 16. rdb BB 17. rdb BB 18. rdb BB 19. rdb BB 20. rdb BB 21. rdb BB 22.
  rdb BB 23. rdb BB 24. rdb BB 25. rdb BB 26. rdb BB 27. rdb BB 28. rdb BB 29.
  do 32 step.
  repeat match goal with H : ov_read_bytes _ _ _ _ = _ |- _ => clear H end.
  rewrite !be32_reg, !be16_reg.
  (* 0x12ddc: the stores into w *)
  do 6 step.
  (* sub a5, s2, a0: pad_len *)
  rewrite (unsigned_lit (Z.of_nat (length b) + -14)), (unsigned_lit (be16 b 14)) by lia.
  replace (Z.of_nat (length b) + -14 - be16 b 14) with (fr_pad_len b)
    by (unfold fr_pad_len, fr_body_len, fr_numbytes; lia).
  (* sw a3, sw a4; sb t0, sb t1: the step leaves le1 (zxb x) for the byte x *)
  do 3 step. rewrite le1_zxb. mem_after_store.
  step. rewrite le1_zxb. mem_after_store.
  do 3 step.
  (* 0x12e10: an empty body *)
  step.
  destruct (Z.eq_dec (be16 b 14) 16) as [E16|E16].
  { b2_br true.
    eapply b2_ok; try eassumption; try lia.
    assert (FB : fr_body b = []) by (unfold fr_body, fr_body_len, fr_numbytes; rewrite E16; reflexivity).
    rewrite FB. cbn [sum_bytes]. f_equal. lia. }
  b2_br false. do 3 step.
  (* 0x12e20: the body sum *)
  pose proof (length_fr_body b C0) as LB.
  b2_curmem ltac:(fun mm => pose proof (b2_bytes_sub mm buf b 30 (Z.to_nat (fr_body_len b)) BB L30) as BDY).
  change (Z.of_nat 30) with 30 in BDY.
  eapply b2_loop with (A := buf + 30) (bd := fr_body b) (r := (length (fr_body b) - 1)%nat) (i := 0%nat).
  - lia.
  - rewrite LB. unfold fr_body_len, fr_numbytes. lia.
  - f_equal. rewrite LB. unfold fr_body_len, fr_numbytes. lia.
  - exact BDY.
  - rewrite LB. unfold fr_body_len, fr_numbytes. lia.
  - lia.
  - reflexivity.
  - intros a3' w1 w2 -> ->.
    eapply b2_ok; try eassumption; try lia.
    reflexivity.
Qed.

End B2.
