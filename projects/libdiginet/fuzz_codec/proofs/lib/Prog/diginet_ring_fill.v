(** diginet_ring_fill (diginet_codec.c:174-177; the leaf at 0x15600, 9 instructions, no branch, no memory access).
    0x15600 `sltiu a1, a0, 0x10` and 0x15610 `negw` form the mask n < 16 ? -1 : 0, 0x15608 `sllw` and 0x1560c
    `not` the word ~(-1 << (n mod 32)), 0x15614 `and` joins them and 0x15618-0x1561c `slli` / `srli` 48 zero-extend
    the uint16_t. The caller passes n sign-extended from 32 bits, so the unsigned compare with 16 is n < 16
    (ring_fill_val). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_cells diginet_ring_fill_c.
Import ListNotations.
Open Scope Z_scope.

(* an unsigned n >= k (k < 2^31) passed as s32 n reads as at least k unsigned *)
Lemma s32_mod_ge : forall k n, 0 <= k < 2 ^ 31 -> k <= n < 2 ^ 32 -> k <= s32 n mod 18446744073709551616.
Proof.
  intros k n Hk Hn. unfold s32. destruct (Z.ltb_spec n (2 ^ 31)) as [L|L].
  - rewrite Z.mod_small; lia.
  - Z.div_mod_to_equations. lia.
Qed.

(* the value the nine instructions leave in a0 *)
Lemma ring_fill_val : forall n, 0 <= n < 2 ^ 32 ->
  Z.land (bv_swrap 32 (0 - Z.b2z (s32 n mod 18446744073709551616 <? 16)) mod 18446744073709551616)
         (Z.lxor (bv_swrap 32 (18446744073709551615 ≪ ((s32 n mod 18446744073709551616) mod 32))
                    mod 18446744073709551616) 18446744073709551615) mod 65536
  = ring_fill_spec n.
Proof.
  intros n Hn. unfold ring_fill_spec.
  destruct (Z.ltb_spec n 16) as [L|L].
  - replace n with (Z.of_nat (Z.to_nat n)) by lia.
    assert (K : (Z.to_nat n < 16)%nat) by lia.
    generalize (Z.to_nat n) K. clear. intros k K.
    do 16 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
  - rewrite (proj2 (Z.ltb_ge _ _) (s32_mod_ge 16 n ltac:(lia) ltac:(lia))).
    rewrite (proj2 (Z.leb_gt n 15)) by lia.
    replace (bv_swrap 32 (0 - Z.b2z false) mod 18446744073709551616) with 0 by (vm_compute; reflexivity).
    rewrite Z.land_0_l. reflexivity.
Qed.

Theorem diginet_ring_fill_holds : diginet_ring_fill_contract.
Proof.
  unfold diginet_ring_fill_contract, diginet_ring_fill_pre, arg_u32, DIGINET_RING_FILL.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n
         [HN ->].
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  rewrite (ring_fill_val n HN).
  finish.
Qed.
