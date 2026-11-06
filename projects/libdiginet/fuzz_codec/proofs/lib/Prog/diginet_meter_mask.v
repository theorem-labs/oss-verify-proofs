(** diginet_meter_mask (diginet_codec.c:202-207; the leaf at 0x15740, 7 instructions, no memory access).
    0x15744 `bltu a0, a1(14)` skips 0x15748 `li a0, 14` when n < 14 (the caller passes n sign-extended from 32 bits,
    so the unsigned compare is n < 14); then 0x15750 `sllw` and 0x15754 `not` give ~(-1 << min(n, 14)) =
    2^min(n, 14) - 1 (meter_mask_lo for n < 14, the constant 16383 for n >= 14). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_cells diginet_meter_mask_c.
Import ListNotations.
Open Scope Z_scope.

(* an unsigned n >= k (k < 2^31) passed as s32 n reads as at least k unsigned; below k it reads as n *)
Lemma s32_mod_ge : forall k n, 0 <= k < 2 ^ 31 -> k <= n < 2 ^ 32 -> k <= s32 n mod 18446744073709551616.
Proof.
  intros k n Hk Hn. unfold s32. destruct (Z.ltb_spec n (2 ^ 31)) as [L|L].
  - rewrite Z.mod_small; lia.
  - Z.div_mod_to_equations. lia.
Qed.

Lemma s32_mod_lt : forall k n, 0 <= k < 2 ^ 31 -> 0 <= n < 2 ^ 32 -> s32 n mod 18446744073709551616 < k -> n < k.
Proof.
  intros k n Hk Hn H. destruct (Z.ltb_spec n k) as [L|L]; [exact L|].
  pose proof (s32_mod_ge k n Hk ltac:(lia)). lia.
Qed.

(* n < 14: the value 0x15750-0x15754 leave in a0 *)
Lemma meter_mask_lo : forall n, 0 <= n < 14 ->
  Z.lxor (bv_swrap 32 (18446744073709551615 ≪ ((s32 n mod 18446744073709551616) mod 32)) mod 18446744073709551616)
    18446744073709551615 = meter_mask_spec n.
Proof.
  intros n Hn. replace n with (Z.of_nat (Z.to_nat n)) by lia.
  assert (K : (Z.to_nat n < 14)%nat) by lia.
  generalize (Z.to_nat n) K. clear. intros k K.
  do 14 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.

(* n >= 14: the clamp *)
Lemma meter_mask_hi : forall n, 14 <= n -> meter_mask_spec n = 16383.
Proof. intros n Hn. unfold meter_mask_spec. rewrite Z.min_r by lia. reflexivity. Qed.

Theorem diginet_meter_mask_holds : diginet_meter_mask_contract.
Proof.
  unfold diginet_meter_mask_contract, diginet_meter_mask_pre, arg_u32, DIGINET_METER_MASK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n
         [HN ->].
  zstep. zstep. if_cases K1.
  - (* n < 14: 0x15744 taken *)
    zify_cond K1. pose proof (s32_mod_lt 14 n ltac:(lia) HN K1) as L.
    zstep. zstep. zstep. zstep.
    rewrite (meter_mask_lo n ltac:(lia)).
    finish.
  - (* n >= 14: a0 := 14 *)
    zify_cond K1.
    assert (L : 14 <= n).
    { destruct (Z.ltb_spec n 14) as [L|L]; [|exact L].
      unfold s32 in K1. rewrite (proj2 (Z.ltb_lt n (2 ^ 31))) in K1 by lia.
      rewrite Z.mod_small in K1 by lia. lia. }
    zstep. zstep. zstep. zstep. zstep.
    rewrite (meter_mask_hi n L).
    finish.
Qed.
