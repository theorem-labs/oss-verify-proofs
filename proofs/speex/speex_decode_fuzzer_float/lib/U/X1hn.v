(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bs X1c2.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm X1hu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.

Section Cuts2.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Variable X : nbinv ptr.
Local Notation ST := (x_st X). Local Notation OUT := (x_out X). Local Notation A := (x_A X).
Local Notation gp := (x_gp X). Local Notation tp := (x_tp X).
Local Notation usp := (bv_unsigned (x_sp X)).
Local Notation st0 := (x_st0 X).

Definition at_F (r : smrec) (mo olp bp : Z) (st : nb_state ptr) (b : bits_st ptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : iclob) (xra xa0 xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs11 : word)
(j : nb_junk) (ows iws sws : list word) (fr : frame),
ms = MS (mkR xra (Z_to_bv 64 (usp + -912)) gp tp (c_t0 k) (c_t1 k) (c_t2 k) xs0 xs1 xa0
(c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
xs2 xs3 xs4 xs5 xs6 xs7 xs8 (Z_to_bv 64 (ST + 2184)) (Z_to_bv 64 bp) xs11
(c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k))
Fx (Z_to_bv 64 0x21b88) fc None m (seg_rom rsegs)
/\ frm0 fc /\ nbctx X m st b j ows iws sws /\ frame_ok fr /\ frame_at X m fr
/\ f_v48 fr = Z_to_bv 64 (ST + 2047) /\ f_v80 fr = Z_to_bv 64 OUT /\ f_v88 fr = Z_to_bv 64 ST
/\ f_v104 fr = Z_to_bv 64 (ST + 2040) /\ f_v112 fr = Z_to_bv 64 A /\ f_v120 fr = Z_to_bv 64 0
/\ j_exc j = ST + 1368 /\ smrec_at mo = Some r /\ nb_submodeID st = mo /\ 17 <= bp <= 144.

Definition at_G (i : Z) (st : nb_state ptr) (b : bits_st ptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : iclob) (xra xa0 xs8 xs10 : word)
(j : nb_junk) (ows iws sws : list word) (fr : frame),
ms = MS (mkR xra (Z_to_bv 64 (usp + -912)) gp tp (c_t0 k) (c_t1 k) (c_t2 k)
(Z_to_bv 64 (ST + 2168)) (Z_to_bv 64 (18446744073709551615 - (ST + 2080))) xa0
(c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
(Z_to_bv 64 (usp + -692)) (Z_to_bv 64 (usp + -736)) (Z_to_bv 64 i) (Z_to_bv 64 40) (Z_to_bv 64 (ST + 2080)) (Z_to_bv 64 (ST + 2120))
xs8 (Z_to_bv 64 (ST + 2184)) xs10 (Z_to_bv 64 (18446744073709551615 - (ST + 2168)))
(c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k))
Fx (Z_to_bv 64 0x21d38) fc None m (seg_rom rsegs)
/\ frm0 fc /\ nbctx X m st b j ows iws sws /\ frame_ok fr /\ frame_at X m fr
/\ f_v48 fr = Z_to_bv 64 (ST + 2047) /\ f_v80 fr = Z_to_bv 64 OUT /\ f_v88 fr = Z_to_bv 64 ST
/\ f_v104 fr = Z_to_bv 64 (ST + 2040) /\ f_v112 fr = Z_to_bv 64 A /\ f_v120 fr = Z_to_bv 64 0
/\ j_exc j = ST + 1368 /\ 0 <= i <= 4.

Definition at_H (st : nb_state ptr) (b : bits_st ptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : iclob) (xra xa0 xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs10 xs11 : word)
(j : nb_junk) (ows iws sws : list word) (fr : frame),
ms = MS (mkR xra (Z_to_bv 64 (usp + -912)) gp tp (c_t0 k) (c_t1 k) (c_t2 k) xs0 xs1 xa0
(c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
xs2 xs3 xs4 xs5 xs6 xs7 xs8 (Z_to_bv 64 (ST + 2184)) xs10 xs11
(c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k))
Fx (Z_to_bv 64 0x21e00) fc None m (seg_rom rsegs)
/\ frm0 fc /\ nbctx X m st b j ows iws sws /\ frame_ok fr /\ frame_at X m fr
/\ f_v48 fr = Z_to_bv 64 (ST + 2047) /\ f_v80 fr = Z_to_bv 64 OUT /\ f_v88 fr = Z_to_bv 64 ST
/\ f_v104 fr = Z_to_bv 64 (ST + 2040) /\ f_v112 fr = Z_to_bv 64 A /\ f_v120 fr = Z_to_bv 64 0
/\ j_exc j = ST + 1368.
End Cuts2.
