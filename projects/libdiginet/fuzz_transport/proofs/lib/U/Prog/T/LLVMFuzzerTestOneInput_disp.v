(* The op loop's dispatch in the ubsan image, 0x139dc-0x13a20 (fuzz_transport.c:1169-1170
   `switch (fuzz_u8(&in) % 9)`): UBSan's pointer-overflow check of p + 1 (addi s3, s5, 1; bgeu s1, s3 -> trap, not
   taken since 0 < data + off and data + off + 1 < 2^64), the byte at the cursor (lbu), the remainder by a multiply:
   q = (b * 57) >> 9 is b / 9 for every byte b (dsp_div) and the code keeps b - q - 8 * q, the count left minus one
   in s6. Op 8 branches to 0x13c44 (bltu s4, a0), ops 0 to 7 jump through the table at 0x10418 (lw a0, 0(a0) of the
   read-only image; the eight words, added to 0x10418, are LH_CASE 0 .. LH_CASE 7). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh.
Import ListNotations.
Open Scope Z_scope.

(* one byte of the input buffer, as bytes_at reads it *)
Lemma dsp_sub1 : forall (D : list byte) k, (k < length D)%nat -> firstn 1 (skipn k D) = [nth k D (b8 0)].
Proof.
  induction D as [|d D IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k]; cbn; [reflexivity|]. apply IH. lia.
Qed.

(* the compiler's quotient: (b * 57) >> 9 = b / 9 on a byte *)
Lemma dsp_div : forall b, 0 <= b < 256 -> b * 57 / 512 = b / 9.
Proof.
  intros b Hb.
  assert (Hr : 0 <= b mod 9 < 9) by (apply Z.mod_pos_bound; lia).
  pose proof (Z.div_mod b 9 ltac:(lia)) as E.
  assert (Hq : 0 <= b / 9 <= 28).
  { split; [apply Z.div_pos; lia|].
    assert (b / 9 < 29) by (apply Z.div_lt_upper_bound; lia). lia. }
  replace (b * 57) with (512 * (b / 9) + (b / 9 + 57 * (b mod 9))) by lia.
  rewrite Z.mul_comm, Z.div_add_l by lia.
  rewrite (Z.div_small (b / 9 + 57 * (b mod 9)) 512) by lia. lia.
Qed.

Lemma dsp_swrap32 : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. apply bv_swrap_small.
  assert (E : bv_half_modulus 32 = 2 ^ 31) by reflexivity. rewrite E. lia.
Qed.

(* the value the switch tests: Z.land (b - q - 8 q) 255 with q = b / 9 *)
Lemma dsp_sel_val : forall b, 0 <= b < 256 ->
  Z.land (bv_swrap 32 (bv_swrap 32 (b - Z.shiftr (b * 57 mod 18446744073709551616) 9)
                          mod 18446744073709551616 -
                       Z.shiftl (Z.shiftr (b * 57 mod 18446744073709551616) 9) 3
                          mod 18446744073709551616)
            mod 18446744073709551616) 255
  = b mod 9.
Proof.
  intros b Hb.
  rewrite (Z.mod_small (b * 57) 18446744073709551616) by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 9) with 512.
  rewrite dsp_div by exact Hb.
  assert (Hq : 0 <= b / 9 <= 28).
  { split; [apply Z.div_pos; lia|].
    assert (b / 9 < 29) by (apply Z.div_lt_upper_bound; lia). lia. }
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  assert (Hr : 0 <= b mod 9 < 9) by (apply Z.mod_pos_bound; lia).
  pose proof (Z.div_mod b 9 ltac:(lia)) as E.
  rewrite (dsp_swrap32 (b - b / 9)) by lia.
  rewrite (Z.mod_small (b - b / 9) 18446744073709551616) by lia.
  rewrite (Z.mod_small (b / 9 * 8) 18446744073709551616) by lia.
  rewrite (dsp_swrap32 (b - b / 9 - b / 9 * 8)) by lia.
  rewrite (Z.mod_small (b - b / 9 - b / 9 * 8) 18446744073709551616) by lia.
  replace (b - b / 9 - b / 9 * 8) with (b mod 9) by lia.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  apply Z.mod_small. change (2 ^ 8) with 256. lia.
Qed.

Theorem llvm_disp_holds : llvm_disp_stmt.
Proof.
  unfold llvm_disp_stmt.
  intros data D regs0 m0 Sp lo ops c B F fc ms Q H HK.
  destruct H as (ra & t0 & t1 & t2 & s0 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s6 & t3 & t4 & t5 & t6 &
                 m & j10 & jio & j60 & -> & HOPS & HN & HC & HM).
  pose proof HM as HM0. unfold llvm_mem in HM.
  destruct HM as (HD0 & HDL & HOW & HD & HSP & HSTK & HLO & HSP2 & HWL & HMI & HRO & HWM & HFN & HMU & HWMO &
                  HJ1 & HJ2 & HJ3 & HRW).
  pose proof HC as HC0. unfold llvm_cursor in HC.
  unfold LH_K, LH_FRAME in HLO, HSP2.
  pose proof (bytes_at_bound rsegs m data D HD) as HDB.
  assert (HK1 : (Z.to_nat (fi_off c) + 1 <= length D)%nat) by lia.
  pose proof (bytes_at_read rsegs m data D (fi_off c) 1 HD ltac:(lia) HK1) as HR.
  rewrite dsp_sub1 in HR by lia.
  (* the model's read of the same byte *)
  assert (HU : fuzz_u8_m D c = (FuzzIn (fi_off c + 1) (fi_n c - 1), at8 D (Z.to_nat (fi_off c)))).
  { unfold fuzz_u8_m. destruct (Z.eqb_spec (fi_n c) 0); [lia|reflexivity]. }
  rewrite HU in HK. cbn [fst snd] in HK.
  unfold at8, bz in HK.
  unfold LH_HEAD.
  zstep.                                       (* 0x139dc addi s3, s5, 1 *)
  zstep.                                       (* 0x139e0 bgeu s1, s3 -> 0x14820: UBSan, not taken *)
  if_cases KT; zify_cond KT; try (exfalso; lia).
  do 8 zstep.                                  (* 0x139e4 lbu .. 0x13a00 addi s6, s7, -1 *)
  zstep.                                       (* 0x13a04 bltu s4, a0 -> 0x13c44 *)
  set (b := bv_unsigned (nth (Z.to_nat (fi_off c)) D (b8 0))) in *.
  assert (HB : 0 <= b < 256).
  { unfold b. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (fi_off c)) D (b8 0))) as R.
    unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia. }
  pose proof (Z.mod_pos_bound b 9 ltac:(lia)) as HR9.
  replace (data + fi_off c + 1) with (data + (fi_off c + 1)) by lia.
  replace (fi_n c + -1) with (fi_n c - 1) by lia.
  if_cases KS; zify_cond KS; rewrite (dsp_sel_val b HB) in KS; rewrite (dsp_sel_val b HB).
  - (* 7 < op: op = 8, the branch at 0x13a04 to 0x13c44 *)
    assert (E : b mod 9 = 8) by lia.
    rewrite E in HK. apply HK. unfold llvm_case. cbn [fi_off fi_n].
    do 21 eexists. split; [reflexivity|].
    split; [exact HOPS|]. split; [exact HN|]. split; [exact HC0|].
    split; [rewrite HU; reflexivity|].
    split; [rewrite HU; cbn [snd]; exact E|]. exact HM0.
  - (* op <= 7: the jump table at 0x10418 *)
    assert (HO : b mod 9 = 0 \/ b mod 9 = 1 \/ b mod 9 = 2 \/ b mod 9 = 3 \/ b mod 9 = 4 \/
                 b mod 9 = 5 \/ b mod 9 = 6 \/ b mod 9 = 7) by lia.
    destruct HO as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; rewrite E in HK;
      do 7 zstep;                              (* 0x13a08 slli .. 0x13a20 jr a0 *)
      apply HK; unfold llvm_case; cbn [fi_off fi_n];
      (do 21 eexists; split; [reflexivity|]);
      (split; [exact HOPS|]); (split; [exact HN|]); (split; [exact HC0|]);
      (split; [rewrite HU; reflexivity|]);
      (split; [rewrite HU; cbn [snd]; exact E|]); exact HM0.
Qed.
