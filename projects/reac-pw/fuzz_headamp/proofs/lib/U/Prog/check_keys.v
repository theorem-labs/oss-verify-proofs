From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import check_keys_c.
Import ListNotations.
Open Scope Z_scope.

(** check_keys of the UBSan image (0x14a88, 12 instructions), walked with Lib/Tac.v and Lib/Step.v:
    `or a2, a0, a1; andi a2, a2, 3` is 0 since res and x are 4-aligned ([or_andi3_zero]), so `bnez a2` (to the
    trap 0x14aa4) is not taken; then the plain text: `lw a0, 4(a0)` and `lw a1, 0x80(a1)` read the same four bytes
    w, so `bne a0, a1` (to the abort frame at 0x14aa8) is not taken; then `ret`. *)

Lemma land3_lor_aligned : forall x y, 0 <= x -> 0 <= y -> x mod 4 = 0 -> y mod 4 = 0 -> Z.land (Z.lor x y) 3 = 0.
Proof.
  intros x y Hx Hy Hmx Hmy.
  assert (Ex : x = Z.shiftl (x / 4) 2).
  { rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. pose proof (Z.div_mod x 4 ltac:(lia)). lia. }
  assert (Ey : y = Z.shiftl (y / 4) 2).
  { rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. pose proof (Z.div_mod y 4 ltac:(lia)). lia. }
  rewrite Ex, Ey, <- Z.shiftl_lor.
  change 3 with (Z.ones 2). rewrite Z.land_ones by lia. rewrite Z.shiftl_mul_pow2 by lia.
  apply Z.mod_mul. change (2 ^ 2) with 4. lia.
Qed.

(** The word `or a2, a0, a1; andi a2, a2, 3` leaves, in the form the step tactics write it. *)
Lemma or_andi3_zero : forall x y : word, bv_unsigned x mod 4 = 0 -> bv_unsigned y mod 4 = 0 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned x) (bv_unsigned y)))) 3) = Z_to_bv 64 0.
Proof.
  intros x y Hx Hy. f_equal.
  pose proof (u64_range x) as Rx. pose proof (u64_range y) as Ry.
  rewrite unsigned_lit by (apply Z_lor_range; lia).
  apply land3_lor_aligned; lia.
Qed.

Theorem check_keys_holds : check_keys_contract.
Proof.
  unfold check_keys_contract, CHECK_KEYS.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m w HA0 HA1 HL HR HX.
  unfold X_KEYS_OFF in HX.
  pose proof (bytes_at_ov_read rsegs m _ w 0 4 HR ltac:(lia)) as R0.
  pose proof (bytes_at_ov_read rsegs m _ w 0 4 HX ltac:(lia)) as R1.
  change (Z.of_nat 0) with 0 in R0, R1. change (skipn 0 w) with w in R0, R1.
  rewrite Z.add_0_r in R0, R1. rewrite firstn_all2 in R0, R1 by lia.
  (* or a2, a0, a1; andi a2, a2, 3: 0 *)
  step. step.
  rewrite (or_andi3_zero a0 a1 HA0 HA1).
  (* bnez a2: not taken *)
  step.
  let K := fresh "K" in
  if_cases K; [ first [ exfalso; zify_cond K; lia | idtac ] .. ].
  (* lw a0, 4(a0); lw a1, 0x80(a1) *)
  step. step.
  (* bne a0, a1: not taken (the same word); then ret *)
  step.
  let K := fresh "K" in
  if_cases K;
    first [ exfalso; zify_cond K; lia
          | zstep; finish ].
Qed.
