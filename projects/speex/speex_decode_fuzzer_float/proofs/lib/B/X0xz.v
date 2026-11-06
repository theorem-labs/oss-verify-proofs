(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1nt X1rg X1rh X1re X1od X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X071.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12c X14x X0r0 X0ra X0v9 X0wl X0xn X0xm.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation mem := (word -> option byte).
Local Notation Z64 := (Z_to_bv 64).

Lemma hpx_w : forall (S1 brem d st F : Z) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(w0 w8 w16 w32 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w200 w208 w224 w232 w240 : word) Fr fc (m : mem),
rw_cells bsegs m S1 (hsp w0 w8 w16 (Z64 d) w32 (Z64 brem) w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184
(Z64 (F + 8400)) w200 w208 (Z64 st) w224 w232 w240) ->
0 <= S1 < 2^62 -> 0 <= brem <= 4096 -> mem_inv bsegs m ->
evt bsegs (fun ms =>
(0 < brem /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z64 S1) (Z64 brem) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 (Z64 brem) (Z64 d) s10 s11 t3 t4 t5 t6) Fr (Z64 A_CH) fc None m (seg_rom bsegs))
\/ (brem <= 0 /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z64 S1) (Z64 st) (Z64 (F + 8400)) s5 s7 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 (Z64 brem) (Z64 d) s10 s11 t3 t4 t5 t6) Fr (Z64 A_CL) fc None m (seg_rom bsegs)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z64 A_PX) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SP S1R BR MI. unfold hsp in SP. unfold A_PX, A_CH, A_CL.
ato 0x97424.
destruct (Z_lt_le_dec 0 brem) as [POS|NPOS]; astep; sh_if.
- apply evt_done. left. split; [lia| reflexivity].
- ato 0x974a8. apply evt_done. right. split; [lia| reflexivity].
Qed.

Section PExit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable X : hinv.
Variable F0 : list (word * FdEntry).
Variable fs0 : Fs.Fs.

Theorem h_pexit_ok : h_pexit_cps RT OUT_rep ERR_rep IO_FP X F0 fs0.
Proof using AF.
intros HX h nbr brem0 T c Hc Hk.
destruct Hc as (Σ1 & a & Fx & fc & m & ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r2 & r8 & r9 & t3 & t4 & t5 & t6 & v48 & v56 & v88 & j224 & j232 & ogc & opc
& Hc & FRM & HS & HIT & HR & OGJ & OPJ).
pose proof HR as HR'. destruct HR' as (_ & MI & _ & _ & _ & _ & _ & SP & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP).
unfold h_spill in SP. unfold h_regs in Hc.
pose proof HIT as (E1 & NB & BR).
assert (S1R : 0 <= x_S1 X < 2^62) by (destruct (hi_usp _ _ _ HX) as (_ & U1 & U2); destruct (hi_S1 _ _ _ HX) as (_ & _ & U3); unfold USTACK_TOP in U2; lia).
assert (BR' : 0 <= h_bytes_remaining h <= 4096) by (destruct (hi_pay _ _ _ HX) as (_ & PZ & _); unfold x_size, MAX_FUZZ_SIZE in *; unfold CHUNK in NB; lia).
refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply hpx_w; [exact SP | exact S1R | exact BR' | exact MI]. }
intros ms' c' [(POS & ->) | (NPOS & ->)] Hc'; apply Hk.
- left. split; [lia|].
exists Σ1, a, Fx, fc, m, ra, t0, t1, t2, (Z64 (h_bytes_remaining h)), a1, a2, a3, a4, a5, a6, a7, r2, (Z64 (x_F X + HO_OS)), t3, t4, t5, t6,
(Z64 (h_bytes_remaining h)), v48, v56, v88, j224, j232, ogc, opc.
split; [| split; [exact FRM| split; [exact HS| split; [exact HR| split; [exact OGJ| exact OPJ]]]]].
unfold h_regs. exact Hc'.
- right. split; [lia|].
exists Σ1, a, Fx, fc, m, ra, t0, t1, t2, a4, a5, a6, a7, r2, (Z64 (h_stream_init h)), (Z64 (x_F X + HO_OS)), (Z64 (h_bytes_remaining h)), (Z64 (x_d X)), (Z64 (h_eos h)),
t3, t4, t5, t6, (Z64 (h_bytes_remaining h)), v48, v56, v88, j224, j232, (Z64 (h_last_granule h)), ogc, opc.
split; [| split; [exact FRM| split; [exact HS| split; [exact HR| split; [exact OGJ| exact OPJ]]]]].
unfold h_regs. exact Hc'.
Qed.
End PExit.
