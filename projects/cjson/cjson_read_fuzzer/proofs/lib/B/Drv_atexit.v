(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes Decode RegsEquiv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.Startup_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs CJ_iface AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

Definition ATEXIT_STACK : Z := 48.

Definition atexit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo fn : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - ATEXIT_STACK, bv_unsigned sp); (A_ATEXIT + 8, A_ATEXIT + 12); (A_ATEXIT + 40, A_ATEXIT + 48);
              (A_ATEXIT + 296, A_ATEXIT + 304)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ (exists (f1 f2 f3 : bv 8) (pad : word),
          rw_cells bsegs m' A_ATEXIT (atex_cells 2 (Z_to_bv 8 0) f1 f2 f3 pad [C8 (Z_to_bv 64 A_ATEXIT_CALL); C8 (Z_to_bv 64 A_ATEXIT_CALL)]))
    /\ rw_cells bsegs m' (A_ATEXIT + 296) [C8 (Z_to_bv 64 fn)].

Lemma atexit_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo fn : Z) (f1 f2 f3 : bv 8) (pad j1 j2 : word) (cdt thr sec : bv 8) (tm1 : word),
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + ATEXIT_STACK <= bv_unsigned sp -> bv_unsigned sp < 2^47 ->
  a0 = Z_to_bv 64 fn -> 0 <= fn < 2^64 ->
  rw_cells bsegs m A_ATEXIT (atex_cells 1 (Z_to_bv 8 0) f1 f2 f3 pad [C8 (Z_to_bv 64 A_ATEXIT_CALL); C8 j1]) ->   (* [comment removed for export] *)
  rw_cells bsegs m (A_ATEXIT + 296) [C8 j2] ->                                                                (* [comment removed for export] *)
  rw_cells bsegs m A_LIBC [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->                                (* [comment removed for export] *)
  mem_inv bsegs m ->
  evt bsegs (atexit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo fn m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 A_ATEXITF) fc None m (seg_rom bsegs)).
Proof.
  intros until tm1. intros ST CEIL LO SPH -> FN AT A1 LIBC MI. try rewrite alloc_ceiling_lit in CEIL.
  unfold ATEXIT_STACK in LO. unfold atex_cells in AT. cbn [app] in AT. unfold A_ATEXITF, A_ATEXIT, A_LIBC, A_ATEXIT_CALL in *.
  change (6277568 + 24) with 6277592 in AT. change (6277568 + 296) with 6277864 in A1.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (6277576, 6277580); (6277608, 6277616); (6277864, 6277872)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 48%nat ST.
  do 6 lstep. (* [comment removed for export] *)
  do 5 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) lstep. lstep. lstep. if_true. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. if_false. (* [comment removed for export] *)
  lstep. lstep. if_true. (* [comment removed for export] *)
  lstep. fl. lstep. lstep. if_true. (* [comment removed for export] *)
  do 5 lstep. (* [comment removed for export] *) fl.
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) lstep. lstep. if_false. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  do 6 lstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  lstep. (* [comment removed for export] *)
  apply evt_done. unfold atexit_post, ATEXIT_STACK, A_ATEXIT, A_ATEXIT_CALL, atex_cells. cbn [app].
  change (6277568 + 8) with 6277576. change (6277568 + 12) with 6277580. change (6277568 + 40) with 6277608. change (6277568 + 48) with 6277616.
  change (6277568 + 296) with 6277864. change (6277568 + 304) with 6277872. change (6277568 + 24) with 6277592.
  change (bv_unsigned sp - 48) with (bv_unsigned sp + -48).
  repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [exists f1, f2, f3, pad; exact AT| exact A1].
Time Qed.
(* [comment removed for export] *)

End CeilWrap.
Notation mem := (word -> option byte).
