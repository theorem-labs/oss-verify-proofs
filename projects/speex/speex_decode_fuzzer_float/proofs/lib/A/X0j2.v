(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c.
Import ListNotations.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Definition leaf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(v : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'.

Definition asan_inited_entry := 0x6e88c%Z.

Lemma asan_inited_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem),
rw_cells bsegs m g_asan_inited [C1 (Z_to_bv 8 1)] ->
mem_inv bsegs m ->
evt bsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 1 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x6e88c) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros CI MI. unfold g_asan_inited in CI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
do 6 zstep.
finish.
Qed.

Lemma sx32_small_A : forall z, (0 <= z < 2^31)%Z -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N].
rewrite Z.mod_small by lia. lia.
Qed.

Definition malloc_ctx_size_entry := 0x70524%Z.
Lemma malloc_ctx_size_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (cs : Z),
rw_cells bsegs m g_malloc_context_size_cell [C4 (Z_to_bv 64 cs)] -> (0 <= cs < 2^31)%Z ->
mem_inv bsegs m ->
evt bsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc cs m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x70524) fc None m (seg_rom bsegs)).
Proof.
intros until cs. intros CI CR MI. unfold g_malloc_context_size_cell in CI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
do 4 zstep.
rewrite (sx32_small_A cs CR). finish.
Qed.
End B_TWIN.

Import ListNotations.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Definition leaf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(v : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m'.

Definition asan_inited_entry := 0x6e7a0%Z.

Lemma asan_inited_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem),
rw_cells asegs m g_asan_inited [C1 (Z_to_bv 8 1)] ->
mem_inv asegs m ->
evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 1 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x6e7a0) fc None m (seg_rom asegs)).
Proof.
intros until m. intros CI MI. unfold g_asan_inited in CI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
do 6 zstep.
finish.
Qed.

Lemma sx32_small_A : forall z, (0 <= z < 2^31)%Z -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N].
rewrite Z.mod_small by lia. lia.
Qed.

Definition malloc_ctx_size_entry := 0x70438%Z.
Lemma malloc_ctx_size_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (cs : Z),
rw_cells asegs m g_malloc_context_size_cell [C4 (Z_to_bv 64 cs)] -> (0 <= cs < 2^31)%Z ->
mem_inv asegs m ->
evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc cs m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x70438) fc None m (seg_rom asegs)).
Proof.
intros until cs. intros CI CR MI. unfold g_malloc_context_size_cell in CI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
do 4 zstep.
rewrite (sx32_small_A cs CR). finish.
Qed.
