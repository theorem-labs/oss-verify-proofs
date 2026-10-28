(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Notation mem := (word -> option byte).

Definition NUMU_STACK : Z := 2608.

Definition numwu_post_g (segs : list Segment) (r1 r0 : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (OUT lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (v : word) (flag : bool),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if flag then r1 else r0)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom segs)
    /\ frm0 fc'
    /\ munch [(bv_unsigned sp - NUMU_STACK, bv_unsigned sp); (OUT, OUT + 8)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ rw_cells segs m' OUT [C8 v] /\ stk segs m' lo (bv_unsigned sp).

Definition numwu_stmt_g (segs : list Segment) (entry gtop r1 r0 : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (A off stop OUT lo : Z) (txt : list byte) (b : byte) (junk : list byte),
  mem_inv segs m -> frm0 fc ->
  stk segs m lo (bv_unsigned sp) -> (lo + NUMU_STACK <= bv_unsigned sp)%Z -> (gtop <= lo)%Z ->
  (bv_unsigned sp mod 16 = 0)%Z ->
  bytes_at segs m A txt -> (A + Z.of_nat (length txt) <= lo)%Z -> (Z.of_nat (length txt) < 2147483648)%Z -> (0 < A)%Z ->
  (0 <= off <= stop)%Z -> nth_error txt (Z.to_nat stop) = Some b -> numchar (bv_unsigned b) = false ->
  rw_cells segs m OUT [CB 8 junk] -> (bv_unsigned sp <= OUT)%Z -> (OUT mod 8 = 0)%Z ->
  evt segs (numwu_post_g segs r1 r0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 OUT lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (A + off)) (Z_to_bv 64 OUT) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Definition slowfu_stmt_g (segs : list Segment) (entry gtop : Z) : Prop := numwu_stmt_g segs entry gtop 9 0.
Definition pffu_stmt_g (segs : list Segment) (entry gtop : Z) : Prop := numwu_stmt_g segs entry gtop 0 1.
