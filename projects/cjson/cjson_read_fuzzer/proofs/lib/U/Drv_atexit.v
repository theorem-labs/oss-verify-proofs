(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg CJ_iface Exit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

Definition ATEXIT_STACK : Z := 48.
Definition P_ATEXITF : Z := 0x15fe0.    (* [comment removed for export] *)
Definition P_ATEX : Z := 0x54a10.       (* [comment removed for export] *)
Definition P_ATEX_GUARD : Z := 0x13594. (* [comment removed for export] *)

Lemma atex_cells_false : atex_cells false =
  [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 z64; C4 (Z_to_bv 64 0); C4 z64; C8 (Z_to_bv 64 0); C8 z64; C8 (Z_to_bv 64 0)].
Proof. reflexivity. Qed.
Lemma atex_cells_true : atex_cells true =
  [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 z64; C4 (Z_to_bv 64 1); C4 z64; C8 (Z_to_bv 64 (0x54a10 + 24)); C8 z64; C8 (Z_to_bv 64 0x160a4)].
Proof. reflexivity. Qed.

Definition atexit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - ATEXIT_STACK, bv_unsigned sp); (P_ATEX + 8, P_ATEX + 12); (P_ATEX + 16, P_ATEX + 24); (P_ATEX + 32, P_ATEX + 40);
              (P_ATEX + 288, P_ATEX + 296)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ ATEX true m'.

(* [comment removed for export] *)
Lemma atexit_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (cdt thr sec : byte) (tm1 : word),
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + ATEXIT_STACK <= bv_unsigned sp -> bv_unsigned sp < 2^47 ->
  a0 = Z_to_bv 64 P_ATEX_GUARD ->
  ATEX false m ->                                                                                              (* [comment removed for export] *)
  rw_cells usegs m PLIBC [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->                                 (* [comment removed for export] *)
  mem_inv usegs m ->
  evt usegs (atexit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 P_ATEXITF) fc None m (seg_rom usegs)).
Proof.
  intros until tm1. intros ST CEIL LO SPH -> [AT A0] LIBC MI. try rewrite alloc_ceiling_lit in CEIL.
  rewrite atex_cells_false in AT. change (0x54a10 + 288) with 0x54b30 in A0.
  unfold ATEXIT_STACK in LO. unfold P_ATEXITF, P_ATEX, P_ATEX_GUARD, PLIBC in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - ATEXIT_STACK, bv_unsigned sp); (P_ATEX + 8, P_ATEX + 12); (P_ATEX + 16, P_ATEX + 24); (P_ATEX + 32, P_ATEX + 40);
              (P_ATEX + 288, P_ATEX + 296)] m) as MU.
  unfold ATEXIT_STACK, P_ATEX in MU.
  change (346640 + 8) with 346648 in MU. change (346640 + 12) with 346652 in MU. change (346640 + 16) with 346656 in MU. change (346640 + 24) with 346664 in MU.
  change (346640 + 32) with 346672 in MU. change (346640 + 40) with 346680 in MU. change (346640 + 288) with 346928 in MU. change (346640 + 296) with 346936 in MU.
  pose proof (wmono_refl usegs m) as WM.
  carve_frame 48%nat ST.
  do 6 lstep. (* [comment removed for export] *)
  do 5 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) lstep. lstep. change (sxb (Z_to_bv 8 0)) with z64. lstep. if_true. lstep. (* [comment removed for export] *)
  lstep. lstep. cbv beta. change (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 0))) with z64. lstep. if_false. (* [comment removed for export] *)
  lstep. lstep. if_false. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. change (sx32 z64) with z64. lstep. lstep. if_true. (* [comment removed for export] *)
  do 5 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) lstep. change (sx32 z64) with z64. lstep. if_false. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  do 6 lstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  lstep. (* [comment removed for export] *)
  apply evt_done. unfold atexit_post, ATEXIT_STACK, P_ATEX, ATEX. rewrite atex_cells_true.
  change (346640 + 8) with 346648. change (346640 + 12) with 346652. change (346640 + 16) with 346656. change (346640 + 24) with 346664.
  change (346640 + 32) with 346672. change (346640 + 40) with 346680. change (346640 + 288) with 346928. change (346640 + 296) with 346936. change (0x54a10 + 24) with 0x54a28.

  change (bv_unsigned sp - 48) with (bv_unsigned sp + -48).
  repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [exact AT| exact A0].
Time Qed.

End CeilWrap.
