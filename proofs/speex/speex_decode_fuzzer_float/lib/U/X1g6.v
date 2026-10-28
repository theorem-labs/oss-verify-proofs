(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bk X1bj X1cf.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.

Definition A_speex_bits_remaining : Z := 0x1ce94.

Section F.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.

Definition speex_bits_remaining_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(A D : Z) (b : bits_st ptr) (m : mem) : machine_state -> Prop :=
fun ms' => exists a0 a1 a2 a3 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ a0 = Z_to_bv 64 (speex_bits_remaining b)
/\ bits_rep rsegs m' A D b.

Variables (A D : Z) (b : bits_st ptr).
Variables ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m : mem.

Ltac ntk := let K := fresh "K" in if_cases K; zify_cond K; [exfalso; lia | clear K].

#[using="Type"] Lemma speex_bits_remaining_spec :
bits_rep rsegs m A D b -> bits_ok b -> mem_inv rsegs m ->
evt rsegs (speex_bits_remaining_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 F fc A D b m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_bits_remaining) fc None m (seg_rom rsegs)).
Proof.
intros REP OK MI. unfold A_speex_bits_remaining.
pose proof REP as ((rj & Lrj & OBJ) & DAT & SIDE).
pose proof (bits_ints A D b OK SIDE) as sfP_; first [ sf_destruct 13%nat sfP_ as In Ic Ib Io Iv Is Rc Rb Rp Rn Rs R1 Rov | sf_fb; destruct sfP_ as (In & Ic & Ib & Io & Iv & Is & Rc & Rb & Rp & Rn & Rs & R1 & Rov) ].
pose proof SIDE as sfP_; first [ sf_destruct 6%nat sfP_ as AL Apos Dpos _ _ SEP | sf_fb; destruct sfP_ as (AL & Apos & Dpos & _ & _ & SEP) ].
unfold bits_pos in Rp. unfold int31, BITS_BUF_MAX in *.
unfold bits_cells in OBJ.
pose proof (rw_cells_bound _ _ _ _ OBJ) as GB. cbn [cells_size csize Nat.add length] in GB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
zstep. ntk.
zstep. rewrite land7_mod8, AL.
zstep. ntk.
zstep. rewrite sx32_small by exact Iv.
zstep. if_cases K; zify_cond K.
-
zstep. rewrite zx32_small by lia.
zstep. rewrite (Z.shiftr_div_pow2 _ 28), (Z.div_small _ (2^28)) by lia.
zstep. ntk.
zstep. rewrite sx32_small by exact Ib.
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8. rewrite swrap32_small by lia.
zstep. zstep. nswrap.
zstep. ntk.
zstep. rewrite sx32_small by exact In.
zstep. nswrap.
zstep. zstep. nswrap.
zstep. ntk.
zstep. nswrap.
zstep.
unfold speex_bits_remaining_post. finish.
unfold speex_bits_remaining, bits_pos. rewrite K. cbn [Z.eqb negb]. f_equal; lia.
-
zstep. zstep. zstep. nswrap. zstep.
unfold speex_bits_remaining_post. finish.
unfold speex_bits_remaining. destruct (Z.eqb_spec (sb_overflow b) 0); [lia| reflexivity].
Qed.
End F.
