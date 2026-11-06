(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bs X1c2.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1ho X1hm X1hu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Plain.M.loaded_segments.

Section Cuts2.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Variable X : nbinv ptr.
Local Notation ST := (x_st X). Local Notation OUT := (x_out X). Local Notation A := (x_A X).
Local Notation gp := (x_gp X). Local Notation tp := (x_tp X).
Local Notation usp := (bv_unsigned (x_sp X)).
Local Notation st0 := (x_st0 X).

Definition at_F (r : smrec) (mo olp bp : Z) (st : nb_state ptr) (b : bits_st ptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : iclob) (xra xa0 xs3 xs6 xs7 : word)
(j : nb_junk) (ows iws sws : list word) (fr : frame),
ms = MS (mkR xra (Z_to_bv 64 (usp + -896)) gp tp (c_t0 k) (c_t1 k) (c_t2 k) (Z_to_bv 64 4) (Z_to_bv 64 (ST + 2120)) xa0
(c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
(Z_to_bv 64 40) xs3 (Z_to_bv 64 bp) (Z_to_bv 64 bp) xs6 xs7 (Z_to_bv 64 (usp + -256)) (Z_to_bv 64 (usp + -576)) (Z_to_bv 64 olp) (Z_to_bv 64 4)
(c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k))
Fx (Z_to_bv 64 0x1f914) fc None m (seg_rom rsegs)
/\ frm0 fc /\ nbctx X m st b j ows iws sws /\ frame_ok fr /\ frame_at X m fr
/\ f_v48 fr = Z_to_bv 64 (ST + 2047) /\ f_v56 fr = Z_to_bv 64 OUT /\ f_v64 fr = Z_to_bv 64 0x1008c
/\ f_v80 fr = Z_to_bv 64 (ST + 2228) /\ f_v88 fr = Z_to_bv 64 ST
/\ f_v104 fr = Z_to_bv 64 A /\ f_v112 fr = Z_to_bv 64 0
/\ j_exc j = ST + 1368 /\ smrec_at mo = Some r /\ nb_submodeID st = mo /\ 17 <= bp <= 144.

Definition at_G (i : Z) (st : nb_state ptr) (b : bits_st ptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : iclob) (xra xa0 : word)
(j : nb_junk) (ows iws sws : list word) (fr : frame),
ms = MS (mkR xra (Z_to_bv 64 (usp + -896)) gp tp (c_t0 k) (c_t1 k) (c_t2 k) (Z_to_bv 64 (ST + 2168)) (Z_to_bv 64 (ST + 2120)) xa0
(c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
(Z_to_bv 64 0) (Z_to_bv 64 (usp + -692)) (Z_to_bv 64 (ST + 2040)) (Z_to_bv 64 4) (Z_to_bv 64 i) (Z_to_bv 64 (ST + 2080))
(Z_to_bv 64 (ST + 2120)) (Z_to_bv 64 160) (Z_to_bv 64 (usp + -732)) (Z_to_bv 64 OUT)
(c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k))
Fx (Z_to_bv 64 0x1fa04) fc None m (seg_rom rsegs)
/\ frm0 fc /\ nbctx X m st b j ows iws sws /\ frame_ok fr /\ frame_at X m fr
/\ f_v48 fr = Z_to_bv 64 (ST + 2047) /\ f_v88 fr = Z_to_bv 64 ST /\ f_v112 fr = Z_to_bv 64 0
/\ j_exc j = ST + 1368 /\ 0 <= i <= 4.

Definition at_H (st : nb_state ptr) (b : bits_st ptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : iclob) (xra xa0 : word)
(j : nb_junk) (ows iws sws : list word) (fr : frame),
ms = MS (mkR xra (Z_to_bv 64 (usp + -896)) gp tp (c_t0 k) (c_t1 k) (c_t2 k) (Z_to_bv 64 (ST + 2168)) (Z_to_bv 64 (ST + 2120)) xa0
(c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
(Z_to_bv 64 0) (Z_to_bv 64 (usp + -692)) (Z_to_bv 64 (ST + 2040)) (Z_to_bv 64 4) (Z_to_bv 64 4) (Z_to_bv 64 (ST + 2080))
(Z_to_bv 64 (ST + 2120)) (Z_to_bv 64 160) (Z_to_bv 64 (usp + -732)) (Z_to_bv 64 OUT)
(c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k))
Fx (Z_to_bv 64 0x1faa4) fc None m (seg_rom rsegs)
/\ frm0 fc /\ nbctx X m st b j ows iws sws /\ frame_ok fr /\ frame_at X m fr
/\ f_v48 fr = Z_to_bv 64 (ST + 2047) /\ f_v88 fr = Z_to_bv 64 ST /\ f_v112 fr = Z_to_bv 64 0
/\ j_exc j = ST + 1368.
End Cuts2.
