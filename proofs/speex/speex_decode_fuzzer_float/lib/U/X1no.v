(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c8 X1bj X1bs X1c2 X1bn.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1ri.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ff X1fd X1en X1fl X1ei X1ea X1fr.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Notation rsegs := X1ff.rsegs.
Notation mem := (word -> option byte).

Definition stderr_wfile0 (m : mem) : Prop :=
exists (flags mode : word) (e wend : Z) (tail : list byte),
rw_cells rsegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x6db18 0 2 mode 0xffffffff tail)
/\ Z.land (bv_unsigned flags) 40 = 0
/\ (wend = 0 \/ (wend = 0x6db18 /\ e = 0x6db18))
/\ 0 <= e < 2^63.

Lemma stderr_wfile0_wfile : forall m, stderr_wfile0 m -> stderr_wfile m.
Proof. intros m sfH_; first [ sf_destruct 9%nat sfH_ as flags mode e wend tail H FL _ _ | sf_fb; destruct sfH_ as (flags & mode & e & wend & tail & H & FL & _ & _) ]. first [ unshelve sf_eexists 5%nat; [ exact (flags) | exact (mode) | exact (e) | exact (wend) | exact (tail) | ] | sf_fb; exists flags, mode, e, wend, tail ]. split; [exact H| exact FL]. Qed.
Lemma stderr_wfile0_file : forall m, stderr_wfile0 m -> stderr_file m.
Proof. intros m H. apply stderr_wfile_file, stderr_wfile0_wfile, H. Qed.

Definition FWRITE_DEPTH : Z := 240.

Section Fwrite.
Context {RCEIL : RunCeiling}.
Context {St : Type}.

Definition fwrite_diag_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ stderr_wfile0 m'
/\ ssp_cells m' canary
/\ st' = st.

Definition fwrite_diag_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word) (s : list Z),
towrite_stmt ->
stderr_wfile0 m ->
bytes_at rsegs m (bv_unsigned a0) (zb s) -> Forall (fun c => 0 <= c < 256) s -> 0 < zlength s < 2^31 ->
a1 = Z_to_bv 64 (zlength s) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 RSTDERR ->
stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FWRITE_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned a0 + zlength s <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
(bv_unsigned a0 + zlength s <= RSTDERR \/ RSTDERR + 232 <= bv_unsigned a0) ->
ssp_cells m canary -> mem_inv rsegs m ->
implM rsegs (stderr_fwrite s : M St unit) st
(fwrite_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m st)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x34e40) fc None m (seg_rom rsegs)).
End Fwrite.
