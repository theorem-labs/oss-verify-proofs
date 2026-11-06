(* The op loop's dispatch, 0x138ac-0x138ec: read the byte at the cursor, take it mod 9 and enter the case.
   fuzz_transport.c:1167-1168 `switch (fuzz_u8(&in) % 9)`. The compiler computes the remainder with a multiply:
   q = (b * 57) >> 9 is b / 9 for every byte b (dis_div), and the code returns b - q - 8 * q. Cases 0 to 7 go
   through the jump table at 0x10408, case 8 through the branch at 0x138d0. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract LLVMFuzzerTestOneInput_lh.
Import ListNotations.
Open Scope Z_scope.

(* one byte of the input buffer, as bytes_at reads it *)
Lemma disp_sub1 : forall (D : list byte) k, (k < length D)%nat -> firstn 1 (skipn k D) = [nth k D (b8 0)].
Proof.
  induction D as [|d D IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k]; cbn; [reflexivity|]. apply IH. lia.
Qed.

(* the compiler's remainder: (b * 57) >> 9 = b / 9 on a byte *)
Lemma dis_div : forall b, 0 <= b < 256 -> b * 57 / 512 = b / 9.
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

Lemma swrap32_small : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. apply bv_swrap_small.
  assert (E : bv_half_modulus 32 = 2 ^ 31) by reflexivity. rewrite E. lia.
Qed.

(* the value the switch tests: Z.land (b - q - 8 q) 255 with q = b / 9 *)
Lemma op_sel_val : forall b, 0 <= b < 256 ->
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
  rewrite dis_div by exact Hb.
  assert (Hq : 0 <= b / 9 <= 28).
  { split; [apply Z.div_pos; lia|].
    assert (b / 9 < 29) by (apply Z.div_lt_upper_bound; lia). lia. }
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  assert (Hr : 0 <= b mod 9 < 9) by (apply Z.mod_pos_bound; lia).
  pose proof (Z.div_mod b 9 ltac:(lia)) as E.
  rewrite (swrap32_small (b - b / 9)) by lia.
  rewrite (Z.mod_small (b - b / 9) 18446744073709551616) by lia.
  rewrite (Z.mod_small (b / 9 * 8) 18446744073709551616) by lia.
  rewrite (swrap32_small (b - b / 9 - b / 9 * 8)) by lia.
  rewrite (Z.mod_small (b - b / 9 - b / 9 * 8) 18446744073709551616) by lia.
  replace (b - b / 9 - b / 9 * 8) with (b mod 9) by lia.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  apply Z.mod_small. change (2 ^ 8) with 256. lia.
Qed.

Section DISP.
Context (data : Z) (D : list byte).

(* The dispatch: from the head, the machine enters the case of op = the byte at the cursor mod 9, with the
   cursor advanced by one byte in s3 / s6 (fuzz_u8_m's result) and memory untouched. *)
Lemma llvm_dispatch : forall Sp lo ops c B m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q,
  llvm_head data D m0 gp tp Sp lo ops c B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
  (forall ms', llvm_case data D m0 gp tp (snd (fuzz_u8_m D c) mod 9) Sp lo ops c (fst (fuzz_u8_m D c)) B
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros Sp lo ops c B m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q H HK.
  destruct H as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & r19 & r22 &
                 t3 & t4 & t5 & t6 & m & j10 & j28 & -> & HOPS & HN & HC & HM).
  pose proof HM as HM0. unfold llvm_mem in HM.
  destruct HM as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HJ1 & HJ2 & HRW).
  unfold llvm_cursor in HC.
  pose proof (bytes_at_bound rsegs m data D HD) as HDB.
  assert (HK1 : (Z.to_nat (fi_off c) + 1 <= length D)%nat) by lia.
  pose proof (bytes_at_read rsegs m data D (fi_off c) 1 HD ltac:(lia) HK1) as HR.
  rewrite disp_sub1 in HR by lia.
  (* the model's read of the same byte *)
  assert (HU : fuzz_u8_m D c = (FuzzIn (fi_off c + 1) (fi_n c - 1), at8 D (Z.to_nat (fi_off c)))).
  { unfold fuzz_u8_m. destruct (Z.eqb_spec (fi_n c) 0); [lia|reflexivity]. }
  rewrite HU in HK. cbn [fst snd] in HK.
  unfold at8, bz in HK.
  unfold LLVM_HEAD_PC.
  do 10 zstep.
  set (b := bv_unsigned (nth (Z.to_nat (fi_off c)) D (b8 0))) in *.
  assert (HB : 0 <= b < 256).
  { unfold b. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (fi_off c)) D (b8 0))) as R.
    unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia. }
  pose proof (Z.mod_pos_bound b 9 ltac:(lia)) as HR9.
  replace (data + fi_off c + 1) with (data + (fi_off c + 1)) by lia.
  replace (fi_n c + -1) with (fi_n c - 1) by lia.
  if_cases KS; zify_cond KS; rewrite (op_sel_val b HB) in KS; rewrite (op_sel_val b HB).
  - (* 7 < op: op = 8, the branch at 0x138d0 to 0x13ac0 *)
    assert (E8 : b mod 9 = 8) by lia.
    apply HK. rewrite E8. unfold llvm_case. cbn [fi_off fi_n].
    do 20 eexists. split; [reflexivity|].
    split; [lia|]. split; [lia|]. split; [unfold llvm_cursor; cbn; lia|].
    split; [rewrite HU; reflexivity|]. exact HM0.
  - (* op <= 7: the jump table at 0x10408 *)
    assert (HO : b mod 9 = 0 \/ b mod 9 = 1 \/ b mod 9 = 2 \/ b mod 9 = 3 \/ b mod 9 = 4 \/
                 b mod 9 = 5 \/ b mod 9 = 6 \/ b mod 9 = 7) by lia.
    destruct HO as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; rewrite E in HK; clear E;
      do 7 zstep;
      apply HK; unfold llvm_case; cbn [fi_off fi_n];
      (do 20 eexists; split; [reflexivity|]);
      (split; [lia|]); (split; [lia|]); (split; [unfold llvm_cursor; cbn; lia|]);
      (split; [rewrite HU; reflexivity|]); exact HM0.
Qed.

End DISP.
