(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bk.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qn X0px X0qc X0qp.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qv X1qx X1r3 X1r4 X1nt.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition A_speex_bits_destroy : Z := 0x1c8a8.

Section F.
Context {RCEIL : RunCeiling}.
Hypothesis HF : rfree_stmt.

Ltac ntk := let K := fresh "K" in if_cases K; zify_cond K; [exfalso; lia | clear K].

#[using="HF"] Lemma speex_bits_destroy_spec :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (b : bits_st bptr) (A D nD lo B : Z) (errv : word),
RHEAP s LB m -> In (sb_chars b, D, nD) LB ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 A -> bits_rep rsegs m A D b -> bits_ok b -> sb_owner b = 1 ->
implM rsegs (speex_bits_destroy raw_free b) s
(rfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB (sb_chars b) lo B errv m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_bits_destroy) fc None m (seg_rom rsegs)).
Proof.
intros until errv. intros HP HIN AUX SPB ST CEIL LO ERR MI TP -> REP OK OWN.
unfold A_speex_bits_destroy.
pose proof REP as ((rj & Lrj & OBJ) & DAT & SIDE).
pose proof (bits_ints A D b OK SIDE) as sfP_; first [ sf_destruct 13%nat sfP_ as In Ic Ib Io Iv Is Rc Rb Rp Rn Rs R1 Rov | sf_fb; destruct sfP_ as (In & Ic & Ib & Io & Iv & Is & Rc & Rb & Rp & Rn & Rs & R1 & Rov) ].
pose proof SIDE as sfP_; first [ sf_destruct 6%nat sfP_ as AL Apos Dpos _ _ SEP | sf_fb; destruct sfP_ as (AL & Apos & Dpos & _ & _ & SEP) ].
unfold bits_cells in OBJ. unfold int31 in *.
pose proof (rw_cells_bound _ _ _ _ OBJ) as GB. cbn [cells_size csize Nat.add length] in GB.
unfold speex_bits_destroy. rewrite OWN. cbn [Z.eqb negb].
unfold implM. iprefix.
zstep. ntk.
zstep. rewrite land7_mod8, AL.
zstep. ntk.
step. rewrite sx32_small by (unfold int31; lia). rewrite OWN.
step. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
step. step.
apply evt_done.
eapply HF; try eassumption; reflexivity.
Qed.
End F.
