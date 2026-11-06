(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.fast_float.from_chars.lib.Ox.F112_002.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

Notation USEGS := Ubsan.M.loaded_segments.

Definition from_chars_int_entry : Z := 0x2adb8.
Definition from_chars_int_FR : Z := 112.
(* [comment removed for export] *)
Definition FCI_FMT : Z := 5.
Definition FCI_OPT2 : Z := 42949673006.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition from_chars_int_W (sp res : word) : list ivl :=
  [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned res, bv_unsigned res + 4)]%Z.

Definition from_chars_int_post_hw
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (res : word)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (r' : word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom USEGS)
    /\ munch (from_chars_int_W sp res) m m'
    /\ wmono USEGS m m'
    /\ rw_cells USEGS m' (bv_unsigned res) [C4 r']
    /\ stk USEGS m' (bv_unsigned sp - 112) (bv_unsigned sp).

Definition from_chars_int_stmt_hw : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (bs : list byte) (rold : word),
    (* [comment removed for export] *)
    a3 = Z_to_bv 64 FCI_FMT ->
    a4 = Z_to_bv 64 FCI_OPT2 ->
    (* [comment removed for export] *)
    bytes_at USEGS m (bv_unsigned a0) bs ->
    (0 < bv_unsigned a0)%Z ->
    (Z.of_nat (length bs) = bv_unsigned a1 - bv_unsigned a0)%Z ->
    (bv_unsigned a0 <= bv_unsigned a1)%Z ->
    (* [comment removed for export] *)
    rw_cells USEGS m (bv_unsigned a2) [C4 rold] ->
    stk USEGS m (bv_unsigned sp - 112) (bv_unsigned sp) ->
    pristine m 0x10000 0x22000 ->
    (* [comment removed for export] *)
    (bv_unsigned a2 + 4 <= bv_unsigned a0 \/ bv_unsigned a1 <= bv_unsigned a2)%Z ->
    (bv_unsigned sp <= bv_unsigned a2 \/ bv_unsigned a2 + 4 <= bv_unsigned sp - 112)%Z ->
    (bv_unsigned sp <= bv_unsigned a0 \/ bv_unsigned a1 <= bv_unsigned sp - 112)%Z ->
    (bv_unsigned a2 + 4 <= 0x10000 \/ 0x22000 <= bv_unsigned a2)%Z ->
    (0x22000 <= bv_unsigned sp - 112)%Z ->
    evt USEGS (from_chars_int_post_hw ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a2 m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x2adb8) fc None m (seg_rom USEGS)).

(* [comment removed for export] *)
Definition from_chars_int_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (res : word)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (r' : word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom USEGS)
    /\ munch (from_chars_int_W sp res) m m'
    /\ wmono USEGS m m'
    /\ frm0 fc'
    /\ rw_cells USEGS m' (bv_unsigned res) [C4 r']
    /\ stk USEGS m' (bv_unsigned sp - 112) (bv_unsigned sp).

Definition from_chars_int_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (bs : list byte) (rold : word),
    (* [comment removed for export] *)
    a3 = Z_to_bv 64 FCI_FMT ->
    a4 = Z_to_bv 64 FCI_OPT2 ->
    (* [comment removed for export] *)
    bytes_at USEGS m (bv_unsigned a0) bs ->
    (0 < bv_unsigned a0)%Z ->
    (Z.of_nat (length bs) = bv_unsigned a1 - bv_unsigned a0)%Z ->
    (bv_unsigned a0 <= bv_unsigned a1)%Z ->
    (* [comment removed for export] *)
    rw_cells USEGS m (bv_unsigned a2) [C4 rold] ->
    stk USEGS m (bv_unsigned sp - 112) (bv_unsigned sp) ->
    pristine m 0x10000 0x22000 ->
    (* [comment removed for export] *)
    (bv_unsigned a2 + 4 <= bv_unsigned a0 \/ bv_unsigned a1 <= bv_unsigned a2)%Z ->
    (bv_unsigned sp <= bv_unsigned a2 \/ bv_unsigned a2 + 4 <= bv_unsigned sp - 112)%Z ->
    (bv_unsigned sp <= bv_unsigned a0 \/ bv_unsigned a1 <= bv_unsigned sp - 112)%Z ->
    (bv_unsigned a2 + 4 <= 0x10000 \/ 0x22000 <= bv_unsigned a2)%Z ->
    (0x22000 <= bv_unsigned sp - 112)%Z ->
        frm0 fc ->
    evt USEGS (from_chars_int_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x2adb8) fc None m (seg_rom USEGS)).

Lemma from_chars_int_stmt_of_hw : from_chars_int_stmt_hw -> from_chars_int_stmt.
Proof.
  intros HW. unfold from_chars_int_stmt_hw in HW. unfold from_chars_int_stmt. intros until rold. intros.
  match goal with Hf : frm0 fc |- _ => rename Hf into FRM end.
  apply (evt_mono USEGS (from_chars_int_post_hw ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a2 m)); [apply (HW ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs rold); assumption|].
  unfold from_chars_int_post_hw, from_chars_int_post.
  intros ms' (q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & q14 & q15 & r' & m' & E & A & B & C & D).
  exists q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, F, fc, r', m'.
  split; [exact E|]. split; [exact A|]. split; [exact B|]. split; [exact FRM|]. split; [exact C | exact D].
Qed.
