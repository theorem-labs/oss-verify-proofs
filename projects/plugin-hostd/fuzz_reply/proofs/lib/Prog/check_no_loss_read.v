From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import check_no_loss_read_c.
Open Scope Z_scope.

Lemma sx32_lit : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma signed_lit : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit_wrap.
  change (2^64) with 18446744073709551616. change (2^63) with 9223372036854775808 in *.
  destruct (Z.ltb_spec (z mod 18446744073709551616) 9223372036854775808); cbv iota;
    Z.div_mod_to_equations; lia.
Qed.

Theorem check_no_loss_read_holds : check_no_loss_read_contract.
Proof.
  unfold check_no_loss_read_contract, CHECK_NO_LOSS_READ.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n Hn HB.
  assert (RD : ov_read_bytes rsegs m (wa (bv_unsigned a0 + 24)) 4 = Some (le4 (Z_to_bv 64 n))).
  { rewrite <- (Z.add_0_r (bv_unsigned a0 + 24)).
    rewrite (bytes_at_read rsegs m (bv_unsigned a0 + 24) (le4 (Z_to_bv 64 n)) 0 4 HB ltac:(lia)) by (rewrite length_le4; lia).
    reflexivity. }
  step. rewrite (sx32_lit n) by lia.
  step. if_cases C.
  - exfalso. unfold bv_lts in C. rewrite (signed_lit 0), (signed_lit n) in C by lia.
    apply Z.ltb_lt in C. lia.
  - step. apply evt_done. eexists. reflexivity.
Qed.
