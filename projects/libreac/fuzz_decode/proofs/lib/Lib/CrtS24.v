(* CrtS24: the 24-bit PCM sample of check_round_trip: s24 (three bytes, sign-extended), byte_range, and the three
   bytes of a sample back (rb_byte, s24_mod, z8_self, s24_byte). No item names an image, a segment list or an
   address.

   This file loads neither lib/Prog/RcBraid.v nor lib/Prog/RcBraidLib.v. RcBraidLib.v:18 and :48 redefine Step.v's
   exec_pre and post_step globally (`Ltac ... ::=`), in every file that loads it, also without Import. With that
   post_step, step does not rename the fcsr after an FP instruction, and the next FP step fails. A file with FP
   steps (lib/A/Prog/crtA_conv.v) therefore Requires this file, not lib/Lib/CrtEnc.v; CrtEnc.v re-exports it.

   PORT of a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_convert.v:11-13,58-59 (s24, byte_range) and a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_enc.v:45,230-260 (rb_byte, s24_mod,
   z8_self, s24_byte); each block below cites its lines. Names, statements and proofs are the record's. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem.
Import ListNotations.
Open Scope Z_scope.

(* s24: verbatim from a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_convert.v:11-13. *)
Definition s24 (b0 b1 b2 : byte) : Z :=
  bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2
  - (if 128 <=? bv_unsigned b2 then 16777216 else 0).

(* byte_range: verbatim from a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_convert.v:58-59. *)
Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. exact H. Qed.

(* rb_byte: verbatim from a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_enc.v:45-45. *)
Definition rb_byte (x j : Z) : Z := if j =? 0 then x mod 256 else if j =? 1 then x / 256 mod 256 else x / 65536.

(* s24_mod, z8_self, s24_byte: verbatim from a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_enc.v:230-260. *)
Lemma s24_mod : forall b0 b1 b2, s24 b0 b1 b2 mod 2^24 = bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2.
Proof.
  intros b0 b1 b2. unfold s24. pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2).
  destruct (128 <=? bv_unsigned b2).
  - replace (bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 - 16777216)
      with ((bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2) + (-1) * 2^24) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.sub_0_r. apply Z.mod_small. lia.
Qed.

Lemma z8_self : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof.
  intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. pose proof (byte_range b).
  change (bv_modulus 8) with 256. lia.
Qed.

Lemma s24_byte : forall (b0 b1 b2 : byte) j, 0 <= j < 3 ->
  Z_to_bv 8 (rb_byte (s24 b0 b1 b2 mod 2^24) j) = if j =? 0 then b0 else if j =? 1 then b1 else b2.
Proof.
  intros b0 b1 b2 j Hj. rewrite s24_mod. pose proof (byte_range b0) as R0. pose proof (byte_range b1) as R1.
  pose proof (byte_range b2) as R2. unfold rb_byte.
  set (u0 := bv_unsigned b0) in *. set (u1 := bv_unsigned b1) in *. set (u2 := bv_unsigned b2) in *.
  assert (C : j = 0 \/ j = 1 \/ j = 2) by lia.
  destruct C as [-> | [-> | ->]]; cbn [Z.eqb].
  - replace ((u0 + 256 * u1 + 65536 * u2) mod 256) with u0 by (clearbody u0 u1 u2; Z.div_mod_to_equations; lia).
    apply z8_self.
  - replace ((u0 + 256 * u1 + 65536 * u2) / 256 mod 256) with u1 by (clearbody u0 u1 u2; Z.div_mod_to_equations; lia).
    apply z8_self.
  - replace ((u0 + 256 * u1 + 65536 * u2) / 65536) with u2 by (clearbody u0 u1 u2; Z.div_mod_to_equations; lia).
    apply z8_self.
Qed.
