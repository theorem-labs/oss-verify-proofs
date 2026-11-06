(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cg X1dj.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j2 X0gi X0ir.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19l X173.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173.
Import ListNotations.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Section CLZ.
Variables (ra sp gp tp t0 t1 t2 s0 a0 a3 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (w : word) (k nres : Z) (Q : machine_state -> Prop).
Hypothesis NR : rw_cells bsegs m 1057992 [C8 (Z_to_bv 64 nres)].
Hypothesis Hk : (0 <= k < 64)%Z.
Hypothesis Hx : (2 ^ k <= bv_unsigned w < 2 ^ (k + 1))%Z.
Hypothesis K : forall (a1 a2 a5 a6 : word),
evt bsegs Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 1057944) a0 a1 a2 a3 (Z_to_bv 64 nres) a5 a6 a7 w
(Z_to_bv 64 (63 - k)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x4a95c) fc None m (seg_rom bsegs)).

Lemma clz_block : forall a1 a2 a4 a5 a6 s3,
evt bsegs Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 1057944) a0 a1 a2 a3 a4 a5 a6 a7 w s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6) F (Z_to_bv 64 0x4a8b4) fc None m (seg_rom bsegs)).
Proof using NR Hk Hx K.
intros.
do 5 zstep.
remember (Z_to_bv 64 (Z.lor (bv_unsigned w) (bv_unsigned w ≫ 1))) as w1 eqn:E1.
do 5 zstep.
remember (Z_to_bv 64 (Z.lor (bv_unsigned w1) (bv_unsigned w1 ≫ 2))) as w2 eqn:E2.
do 8 zstep.
remember (Z_to_bv 64 (Z.lor (bv_unsigned w2) (bv_unsigned w2 ≫ 4))) as w3 eqn:E3.
do 2 zstep.
remember (Z_to_bv 64 (Z.lor (bv_unsigned w3) (bv_unsigned w3 ≫ 8))) as w4 eqn:E4.
do 2 zstep.
remember (Z_to_bv 64 (Z.lor (bv_unsigned w4) (bv_unsigned w4 ≫ 16))) as w5 eqn:E5.
do 2 zstep.
remember (Z_to_bv 64 (Z.lor (bv_unsigned w5) (bv_unsigned w5 ≫ 32))) as w6 eqn:E6.
zstep.
remember (Z_to_bv 64 (Z.lxor (bv_unsigned w6) 18446744073709551615)) as ny eqn:E7.
do 17 zstep.
pose proof (bv_unsigned_in_range 64 w) as RW. unfold bv_modulus in RW. cbn [Z.of_N] in RW.
assert (W6 : bv_unsigned w6 = Z.ones (k + 1)).
{ assert (U : bv_unsigned w6 = smj64 (bv_unsigned w) 6).
{ subst w6 w5 w4 w3 w2 w1. rewrite !Z_to_bv_unsigned. reflexivity. }
rewrite U, smj64_smj by lia. apply smear_ones; assumption. }
assert (NY : bv_unsigned ny = (Z.lxor (Z.ones (k + 1)) 18446744073709551615) mod 18446744073709551616).
{ subst ny. rewrite Z_to_bv_unsigned, W6. reflexivity. }
lazymatch goal with |- context [Z_to_bv 64 (Z.shiftr ?T 56)] =>
change (Z.shiftr T 56) with (pc_chain (bv_unsigned ny)) end.
rewrite NY, (pc_chain_clz k Hk).
apply K.
Qed.
End CLZ.
End B_TWIN.

Import ListNotations.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Section CLZ.
Variables (ra sp gp tp t0 t1 t2 s0 a0 a3 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (w : word) (k nres : Z) (Q : machine_state -> Prop).
Hypothesis NR : rw_cells asegs m 1023112 [C8 (Z_to_bv 64 nres)].
Hypothesis Hk : (0 <= k < 64)%Z.
Hypothesis Hx : (2 ^ k <= bv_unsigned w < 2 ^ (k + 1))%Z.
Hypothesis K : forall (a1 a2 a5 a6 : word),
evt asegs Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 1023064) a0 a1 a2 a3 (Z_to_bv 64 nres) a5 a6 a7 w
(Z_to_bv 64 (63 - k)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x4a870) fc None m (seg_rom asegs)).

Lemma clz_block : forall a1 a2 a4 a5 a6 s3,
evt asegs Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 1023064) a0 a1 a2 a3 a4 a5 a6 a7 w s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6) F (Z_to_bv 64 0x4a7c8) fc None m (seg_rom asegs)).
Proof using NR Hk Hx K.
intros.
do 5 zstep.
remember (Z_to_bv 64 (Z.lor (bv_unsigned w) (bv_unsigned w ≫ 1))) as w1 eqn:E1.
do 5 zstep.
remember (Z_to_bv 64 (Z.lor (bv_unsigned w1) (bv_unsigned w1 ≫ 2))) as w2 eqn:E2.
do 8 zstep.
remember (Z_to_bv 64 (Z.lor (bv_unsigned w2) (bv_unsigned w2 ≫ 4))) as w3 eqn:E3.
do 2 zstep.
remember (Z_to_bv 64 (Z.lor (bv_unsigned w3) (bv_unsigned w3 ≫ 8))) as w4 eqn:E4.
do 2 zstep.
remember (Z_to_bv 64 (Z.lor (bv_unsigned w4) (bv_unsigned w4 ≫ 16))) as w5 eqn:E5.
do 2 zstep.
remember (Z_to_bv 64 (Z.lor (bv_unsigned w5) (bv_unsigned w5 ≫ 32))) as w6 eqn:E6.
zstep.
remember (Z_to_bv 64 (Z.lxor (bv_unsigned w6) 18446744073709551615)) as ny eqn:E7.
do 17 zstep.
pose proof (bv_unsigned_in_range 64 w) as RW. unfold bv_modulus in RW. cbn [Z.of_N] in RW.
assert (W6 : bv_unsigned w6 = Z.ones (k + 1)).
{ assert (U : bv_unsigned w6 = smj64 (bv_unsigned w) 6).
{ subst w6 w5 w4 w3 w2 w1. rewrite !Z_to_bv_unsigned. reflexivity. }
rewrite U, smj64_smj by lia. apply smear_ones; assumption. }
assert (NY : bv_unsigned ny = (Z.lxor (Z.ones (k + 1)) 18446744073709551615) mod 18446744073709551616).
{ subst ny. rewrite Z_to_bv_unsigned, W6. reflexivity. }
lazymatch goal with |- context [Z_to_bv 64 (Z.shiftr ?T 56)] =>
change (Z.shiftr T 56) with (pc_chain (bv_unsigned ny)) end.
rewrite NY, (pc_chain_clz k Hk).
apply K.
Qed.
End CLZ.
