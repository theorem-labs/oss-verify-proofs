(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1ch X1cg X1dk X1cs X1dg X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X0ae.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X110.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition RA_be_realloc : Z := 0xc1550.
Definition RA_le_realloc1 : Z := 0xc15fc.
Definition RA_le_realloc2 : Z := 0xc1614.

Lemma lxor_ones63 : forall a, 0 <= a < 2^63 -> Z.lxor a 9223372036854775807 = 9223372036854775807 - a.
Proof.
intros a Ha.
assert (E : 9223372036854775807 - a = (Z.lnot a) mod 2^63).
{ unfold Z.lnot. apply Z.mod_unique with (q := -1); [left; lia| lia]. }
rewrite E. apply Z.bits_inj'. intros i Hi.
rewrite Z.lxor_spec. change 9223372036854775807 with (Z.ones 63).
destruct (Z.lt_ge_cases i 63).
- rewrite Z.ones_spec_low by lia. rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lnot_spec by lia. apply xorb_true_r.
- rewrite Z.ones_spec_high by lia. rewrite Z.mod_pow2_bits_high by lia. rewrite xorb_false_r.
apply Z.bits_above_log2; [lia|]. destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|].
apply Z.lt_le_trans with 63; [apply Z.log2_lt_pow2; lia| lia].
Qed.

Definition exp_frame (ra s0 s1 s2 : word) : list cell := [C8 s2; C8 s1; C8 s0; C8 ra].

Definition stream_cells_x (Bd bst L G lst : Z) (hdr : list byte) (os : stream_st bptr) : list cell :=
[C8 (wz Bd); C8 (wz bst); C8 (wz (os_body_fill os)); C8 (wz (os_body_returned os));
C8 (wz L); C8 (wz G); C8 (wz lst); C8 (wz (os_lacing_fill os));
C8 (wz (os_lacing_packet os)); C8 (wz (os_lacing_returned os));
CB 284 hdr;
C4 (wz (os_header_fill os)); C4 (wz (os_e_o_s os)); C4 (wz (os_b_o_s os));
C8 (wz (os_serialno os)); C8 (wz (os_pageno os)); C8 (wz (os_packetno os)); C8 (wz (os_granulepos os))].

Lemma be_w0 : forall (A Bd bst L G lst needed usp lo : Z) (hdr : list byte) (os : stream_st bptr)
(ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m A (stream_cells_x Bd bst L G lst hdr os) -> length hdr = 284%nat ->
0 <= bst < 2^61 -> 0 <= os_body_fill os < 2^61 -> 0 <= needed < 2^61 -> os_body_fill os < bst - needed ->
stk bsegs m lo usp -> lo <= usp - 32 -> A + 408 <= lo -> 0 < A -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (a1' a2' a3' : word),
ms = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -32, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 needed) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_os_body_expand) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros OS LH Hst Hfl Hnd ROOM ST LO ALO A0 MI.
unfold A_os_body_expand, stream_cells_x, wz in *.
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
carve_frame 32%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xc1504. astep. sh_if.
ato 0xc1584. release_frame FR ST usp. astep. astep.
apply evt_done. do 4 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
Qed.

Lemma be_w1 : forall (A Bd bst L G lst needed usp lo : Z) (hdr : list byte) (os : stream_st bptr)
(ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m A (stream_cells_x Bd bst L G lst hdr os) -> length hdr = 284%nat ->
0 <= bst < 2^61 -> 0 <= os_body_fill os < 2^61 -> 0 <= needed < 2^61 -> bst - needed <= os_body_fill os ->
stk bsegs m lo usp -> lo <= usp - 32 -> A + 408 <= lo -> 0 < A -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (s1' a2' a3' : word),
ms = MS (mkR (Z_to_bv 64 RA_be_realloc) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) s1'
(Z_to_bv 64 Bd) (Z_to_bv 64 (bst + needed + 1024)) a2' a3' a4 a5 a6 a7 (Z_to_bv 64 (bst + needed + 1024)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_realloc) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -32, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -32)
/\ rw_cells bsegs m1 (usp + -32) (exp_frame ra s0 s1 s2))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 needed) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_os_body_expand) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros OS LH Hst Hfl Hnd GROW ST LO ALO A0 MI.
unfold A_os_body_expand, RA_be_realloc, oe_realloc, exp_frame, stream_cells_x, wz in *.
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
carve_frame 32%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xc1504. astep. sh_if.
ato 0xc151c. rewrite (lxor_ones63 needed) by lia. astep. sh_if.
ato 0xc153c. astep.
replace (Z.lxor (bst + needed) 9223372036854775808 <? 18446744073709550591) with true
by (symmetry; apply Z.ltb_lt; change 9223372036854775808 with (2^63); rewrite (zb_lxor_pow2_small (bst + needed) 63) by lia; lia).
cbn [Z.b2z].
ato 0x67f8c.
apply evt_done. do 4 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact FR].
Qed.

Lemma be_w2 : forall (A Bd bst L G lst q ns usp lo : Z) (hdr : list byte) (os : stream_st bptr)
(gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 cra c0 c1 c2 : word) F fc (m : mem),
rw_cells bsegs m A (stream_cells_x Bd bst L G lst hdr os) -> length hdr = 284%nat -> 0 < q < 2^64 ->
rw_cells bsegs m (usp + -32) (exp_frame cra c0 c1 c2) -> stk bsegs m lo (usp + -32) -> lo <= usp + -32 -> A + 408 <= lo -> 0 < A -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 c2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom bsegs)
/\ munch [(A, A + 408); (usp + -32, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp
/\ rw_cells bsegs m1 A (stream_cells_x q ns L G lst hdr os))
(MS (mkR (Z_to_bv 64 RA_be_realloc) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) s1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 ns) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_be_realloc)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros OS LH Q0 FR ST LO ALO A0 MI.
unfold RA_be_realloc, exp_frame, stream_cells_x, wz in *.
replace (ret_pc (Z_to_bv 64 0xc1550)) with (Z_to_bv 64 0xc1550) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(A, A + 408); (usp + -32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
astep. sh_if.
ato 0xc1584. release_frame FR ST usp. astep. astep.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact OS].
Qed.

Lemma le_w0 : forall (A Bd bst L G lst needed usp lo : Z) (hdr : list byte) (os : stream_st bptr)
(ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m A (stream_cells_x Bd bst L G lst hdr os) -> length hdr = 284%nat ->
0 <= lst < 2^61 -> 0 <= os_lacing_fill os < 2^61 -> 0 <= needed < 2^61 -> os_lacing_fill os < lst - needed ->
stk bsegs m lo usp -> lo <= usp - 32 -> A + 408 <= lo -> 0 < A -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (a1' a2' a3' : word),
ms = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -32, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 needed) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_os_lacing_expand) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros OS LH Hst Hfl Hnd ROOM ST LO ALO A0 MI.
unfold A_os_lacing_expand, stream_cells_x, wz in *.
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
carve_frame 32%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xc15b0. astep. sh_if.
ato 0xc1648. release_frame FR ST usp. astep. astep.
apply evt_done. do 4 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
Qed.

Lemma le_w1 : forall (A Bd bst L G lst needed usp lo : Z) (hdr : list byte) (os : stream_st bptr)
(ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m A (stream_cells_x Bd bst L G lst hdr os) -> length hdr = 284%nat ->
0 <= lst < 2^58 -> 0 <= os_lacing_fill os < 2^58 -> 0 <= needed < 2^58 -> lst - needed <= os_lacing_fill os ->
stk bsegs m lo usp -> lo <= usp - 32 -> A + 408 <= lo -> 0 < A -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (s1' a2' a3' : word),
ms = MS (mkR (Z_to_bv 64 RA_le_realloc1) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) s1'
(Z_to_bv 64 L) (Z_to_bv 64 (4 * (lst + needed + 32))) a2' a3' a4 a5 a6 a7 (Z_to_bv 64 (lst + needed + 32)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_realloc) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -32, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -32)
/\ rw_cells bsegs m1 (usp + -32) (exp_frame ra s0 s1 s2))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 needed) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_os_lacing_expand) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros OS LH Hst Hfl Hnd GROW ST LO ALO A0 MI.
unfold A_os_lacing_expand, RA_le_realloc1, oe_realloc, exp_frame, stream_cells_x, wz in *.
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
carve_frame 32%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xc15b0. astep. sh_if.
ato 0xc15c8. rewrite (lxor_ones63 needed) by lia. astep. sh_if.
ato 0xc15e8.
replace (Z.lxor (lst + needed) 9223372036854775808 <? 18446744073709551583) with true
by (symmetry; apply Z.ltb_lt; change 9223372036854775808 with (2^63); rewrite (zb_lxor_pow2_small (lst + needed) 63) by lia; lia).
cbn [Z.b2z].
ato 0x67f8c.
rewrite Z.shiftl_mul_pow2 by lia. replace ((lst + needed + 32) * 2 ^ 2) with (4 * (lst + needed + 32)) by lia.
apply evt_done. do 4 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact FR].
Qed.

Lemma le_w2 : forall (A Bd bst L G lst q ns : Z) (hdr : list byte) (os : stream_st bptr)
(sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m A (stream_cells_x Bd bst L G lst hdr os) -> length hdr = 284%nat -> 0 < q < 2^64 -> 0 <= ns < 2^58 -> 0 < A -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (a2' : word),
ms = MS (mkR (Z_to_bv 64 RA_le_realloc2) sp gp tp t0 t1 t2 (Z_to_bv 64 A) s1 (Z_to_bv 64 G) (Z_to_bv 64 (8 * ns)) a2' a3 a4 a5 a6 a7
(Z_to_bv 64 ns) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_realloc) fc None m1 (seg_rom bsegs)
/\ munch [(A, A + 408)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 A (stream_cells_x Bd bst q G lst hdr os))
(MS (mkR (Z_to_bv 64 RA_le_realloc1) sp gp tp t0 t1 t2 (Z_to_bv 64 A) s1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 ns) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_le_realloc1)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros OS LH Q0 NS A0 MI.
unfold RA_le_realloc1, RA_le_realloc2, oe_realloc, stream_cells_x, wz in *.
replace (ret_pc (Z_to_bv 64 0xc15fc)) with (Z_to_bv 64 0xc15fc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (munch_refl [(A, A + 408)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
astep. sh_if.
ato 0x67f8c.
rewrite Z.shiftl_mul_pow2 by lia. replace (ns * 2 ^ 3) with (8 * ns) by lia.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact OS].
Qed.

Lemma le_w3 : forall (A Bd bst L G lst q ns usp lo : Z) (hdr : list byte) (os : stream_st bptr)
(gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 cra c0 c1 c2 : word) F fc (m : mem),
rw_cells bsegs m A (stream_cells_x Bd bst L G lst hdr os) -> length hdr = 284%nat -> 0 < q < 2^64 ->
rw_cells bsegs m (usp + -32) (exp_frame cra c0 c1 c2) -> stk bsegs m lo (usp + -32) -> lo <= usp + -32 -> A + 408 <= lo -> 0 < A -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 c2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom bsegs)
/\ munch [(A, A + 408); (usp + -32, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp
/\ rw_cells bsegs m1 A (stream_cells_x Bd bst L q ns hdr os))
(MS (mkR (Z_to_bv 64 RA_le_realloc2) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) s1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 ns) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_le_realloc2)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros OS LH Q0 FR ST LO ALO A0 MI.
unfold RA_le_realloc2, exp_frame, stream_cells_x, wz in *.
replace (ret_pc (Z_to_bv 64 0xc1614)) with (Z_to_bv 64 0xc1614) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(A, A + 408); (usp + -32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
astep. sh_if.
ato 0xc1648. release_frame FR ST usp. astep. astep.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact OS].
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition RA_be_realloc : Z := 0xb8e20.
Definition RA_le_realloc1 : Z := 0xb8ecc.
Definition RA_le_realloc2 : Z := 0xb8ee4.

Lemma lxor_ones63 : forall a, 0 <= a < 2^63 -> Z.lxor a 9223372036854775807 = 9223372036854775807 - a.
Proof.
intros a Ha.
assert (E : 9223372036854775807 - a = (Z.lnot a) mod 2^63).
{ unfold Z.lnot. apply Z.mod_unique with (q := -1); [left; lia| lia]. }
rewrite E. apply Z.bits_inj'. intros i Hi.
rewrite Z.lxor_spec. change 9223372036854775807 with (Z.ones 63).
destruct (Z.lt_ge_cases i 63).
- rewrite Z.ones_spec_low by lia. rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lnot_spec by lia. apply xorb_true_r.
- rewrite Z.ones_spec_high by lia. rewrite Z.mod_pow2_bits_high by lia. rewrite xorb_false_r.
apply Z.bits_above_log2; [lia|]. destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|].
apply Z.lt_le_trans with 63; [apply Z.log2_lt_pow2; lia| lia].
Qed.

Definition exp_frame (ra s0 s1 s2 : word) : list cell := [C8 s2; C8 s1; C8 s0; C8 ra].

Definition stream_cells_x (Bd bst L G lst : Z) (hdr : list byte) (os : stream_st bptr) : list cell :=
[C8 (wz Bd); C8 (wz bst); C8 (wz (os_body_fill os)); C8 (wz (os_body_returned os));
C8 (wz L); C8 (wz G); C8 (wz lst); C8 (wz (os_lacing_fill os));
C8 (wz (os_lacing_packet os)); C8 (wz (os_lacing_returned os));
CB 284 hdr;
C4 (wz (os_header_fill os)); C4 (wz (os_e_o_s os)); C4 (wz (os_b_o_s os));
C8 (wz (os_serialno os)); C8 (wz (os_pageno os)); C8 (wz (os_packetno os)); C8 (wz (os_granulepos os))].

Lemma be_w0 : forall (A Bd bst L G lst needed usp lo : Z) (hdr : list byte) (os : stream_st bptr)
(ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m A (stream_cells_x Bd bst L G lst hdr os) -> length hdr = 284%nat ->
0 <= bst < 2^61 -> 0 <= os_body_fill os < 2^61 -> 0 <= needed < 2^61 -> os_body_fill os < bst - needed ->
stk asegs m lo usp -> lo <= usp - 32 -> A + 408 <= lo -> 0 < A -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (a1' a2' a3' : word),
ms = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m1 (seg_rom asegs)
/\ munch [(usp + -32, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 needed) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_os_body_expand) fc None m (seg_rom asegs)).
Proof.
intros until m. intros OS LH Hst Hfl Hnd ROOM ST LO ALO A0 MI.
unfold A_os_body_expand, stream_cells_x, wz in *.
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -32, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 32%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xb8dd4. astep. sh_if.
ato 0xb8e54. release_frame FR ST usp. astep. astep.
apply evt_done. do 4 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
Qed.

Lemma be_w1 : forall (A Bd bst L G lst needed usp lo : Z) (hdr : list byte) (os : stream_st bptr)
(ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m A (stream_cells_x Bd bst L G lst hdr os) -> length hdr = 284%nat ->
0 <= bst < 2^61 -> 0 <= os_body_fill os < 2^61 -> 0 <= needed < 2^61 -> bst - needed <= os_body_fill os ->
stk asegs m lo usp -> lo <= usp - 32 -> A + 408 <= lo -> 0 < A -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (s1' a2' a3' : word),
ms = MS (mkR (Z_to_bv 64 RA_be_realloc) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) s1'
(Z_to_bv 64 Bd) (Z_to_bv 64 (bst + needed + 1024)) a2' a3' a4 a5 a6 a7 (Z_to_bv 64 (bst + needed + 1024)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_realloc) fc None m1 (seg_rom asegs)
/\ munch [(usp + -32, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -32)
/\ rw_cells asegs m1 (usp + -32) (exp_frame ra s0 s1 s2))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 needed) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_os_body_expand) fc None m (seg_rom asegs)).
Proof.
intros until m. intros OS LH Hst Hfl Hnd GROW ST LO ALO A0 MI.
unfold A_os_body_expand, RA_be_realloc, oe_realloc, exp_frame, stream_cells_x, wz in *.
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -32, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 32%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xb8dd4. astep. sh_if.
ato 0xb8dec. rewrite (lxor_ones63 needed) by lia. astep. sh_if.
ato 0xb8e0c. astep.
replace (Z.lxor (bst + needed) 9223372036854775808 <? 18446744073709550591) with true
by (symmetry; apply Z.ltb_lt; change 9223372036854775808 with (2^63); rewrite (zb_lxor_pow2_small (bst + needed) 63) by lia; lia).
cbn [Z.b2z].
ato 0x67ea0.
apply evt_done. do 4 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact FR].
Qed.

Lemma be_w2 : forall (A Bd bst L G lst q ns usp lo : Z) (hdr : list byte) (os : stream_st bptr)
(gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 cra c0 c1 c2 : word) F fc (m : mem),
rw_cells asegs m A (stream_cells_x Bd bst L G lst hdr os) -> length hdr = 284%nat -> 0 < q < 2^64 ->
rw_cells asegs m (usp + -32) (exp_frame cra c0 c1 c2) -> stk asegs m lo (usp + -32) -> lo <= usp + -32 -> A + 408 <= lo -> 0 < A -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 c2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom asegs)
/\ munch [(A, A + 408); (usp + -32, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp
/\ rw_cells asegs m1 A (stream_cells_x q ns L G lst hdr os))
(MS (mkR (Z_to_bv 64 RA_be_realloc) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) s1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 ns) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_be_realloc)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros OS LH Q0 FR ST LO ALO A0 MI.
unfold RA_be_realloc, exp_frame, stream_cells_x, wz in *.
replace (ret_pc (Z_to_bv 64 0xb8e20)) with (Z_to_bv 64 0xb8e20) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(A, A + 408); (usp + -32, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
astep. sh_if.
ato 0xb8e54. release_frame FR ST usp. astep. astep.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact OS].
Qed.

Lemma le_w0 : forall (A Bd bst L G lst needed usp lo : Z) (hdr : list byte) (os : stream_st bptr)
(ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m A (stream_cells_x Bd bst L G lst hdr os) -> length hdr = 284%nat ->
0 <= lst < 2^61 -> 0 <= os_lacing_fill os < 2^61 -> 0 <= needed < 2^61 -> os_lacing_fill os < lst - needed ->
stk asegs m lo usp -> lo <= usp - 32 -> A + 408 <= lo -> 0 < A -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (a1' a2' a3' : word),
ms = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m1 (seg_rom asegs)
/\ munch [(usp + -32, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 needed) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_os_lacing_expand) fc None m (seg_rom asegs)).
Proof.
intros until m. intros OS LH Hst Hfl Hnd ROOM ST LO ALO A0 MI.
unfold A_os_lacing_expand, stream_cells_x, wz in *.
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -32, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 32%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xb8e80. astep. sh_if.
ato 0xb8f18. release_frame FR ST usp. astep. astep.
apply evt_done. do 4 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
Qed.

Lemma le_w1 : forall (A Bd bst L G lst needed usp lo : Z) (hdr : list byte) (os : stream_st bptr)
(ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m A (stream_cells_x Bd bst L G lst hdr os) -> length hdr = 284%nat ->
0 <= lst < 2^58 -> 0 <= os_lacing_fill os < 2^58 -> 0 <= needed < 2^58 -> lst - needed <= os_lacing_fill os ->
stk asegs m lo usp -> lo <= usp - 32 -> A + 408 <= lo -> 0 < A -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (s1' a2' a3' : word),
ms = MS (mkR (Z_to_bv 64 RA_le_realloc1) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) s1'
(Z_to_bv 64 L) (Z_to_bv 64 (4 * (lst + needed + 32))) a2' a3' a4 a5 a6 a7 (Z_to_bv 64 (lst + needed + 32)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_realloc) fc None m1 (seg_rom asegs)
/\ munch [(usp + -32, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -32)
/\ rw_cells asegs m1 (usp + -32) (exp_frame ra s0 s1 s2))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 needed) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_os_lacing_expand) fc None m (seg_rom asegs)).
Proof.
intros until m. intros OS LH Hst Hfl Hnd GROW ST LO ALO A0 MI.
unfold A_os_lacing_expand, RA_le_realloc1, oe_realloc, exp_frame, stream_cells_x, wz in *.
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -32, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 32%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xb8e80. astep. sh_if.
ato 0xb8e98. rewrite (lxor_ones63 needed) by lia. astep. sh_if.
ato 0xb8eb8.
replace (Z.lxor (lst + needed) 9223372036854775808 <? 18446744073709551583) with true
by (symmetry; apply Z.ltb_lt; change 9223372036854775808 with (2^63); rewrite (zb_lxor_pow2_small (lst + needed) 63) by lia; lia).
cbn [Z.b2z].
ato 0x67ea0.
rewrite Z.shiftl_mul_pow2 by lia. replace ((lst + needed + 32) * 2 ^ 2) with (4 * (lst + needed + 32)) by lia.
apply evt_done. do 4 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact FR].
Qed.

Lemma le_w2 : forall (A Bd bst L G lst q ns : Z) (hdr : list byte) (os : stream_st bptr)
(sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m A (stream_cells_x Bd bst L G lst hdr os) -> length hdr = 284%nat -> 0 < q < 2^64 -> 0 <= ns < 2^58 -> 0 < A -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (a2' : word),
ms = MS (mkR (Z_to_bv 64 RA_le_realloc2) sp gp tp t0 t1 t2 (Z_to_bv 64 A) s1 (Z_to_bv 64 G) (Z_to_bv 64 (8 * ns)) a2' a3 a4 a5 a6 a7
(Z_to_bv 64 ns) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_realloc) fc None m1 (seg_rom asegs)
/\ munch [(A, A + 408)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 A (stream_cells_x Bd bst q G lst hdr os))
(MS (mkR (Z_to_bv 64 RA_le_realloc1) sp gp tp t0 t1 t2 (Z_to_bv 64 A) s1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 ns) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_le_realloc1)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros OS LH Q0 NS A0 MI.
unfold RA_le_realloc1, RA_le_realloc2, oe_realloc, stream_cells_x, wz in *.
replace (ret_pc (Z_to_bv 64 0xb8ecc)) with (Z_to_bv 64 0xb8ecc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (munch_refl [(A, A + 408)] m) as MU. pose proof (wmono_refl asegs m) as WM.
astep. sh_if.
ato 0x67ea0.
rewrite Z.shiftl_mul_pow2 by lia. replace (ns * 2 ^ 3) with (8 * ns) by lia.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact OS].
Qed.

Lemma le_w3 : forall (A Bd bst L G lst q ns usp lo : Z) (hdr : list byte) (os : stream_st bptr)
(gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 cra c0 c1 c2 : word) F fc (m : mem),
rw_cells asegs m A (stream_cells_x Bd bst L G lst hdr os) -> length hdr = 284%nat -> 0 < q < 2^64 ->
rw_cells asegs m (usp + -32) (exp_frame cra c0 c1 c2) -> stk asegs m lo (usp + -32) -> lo <= usp + -32 -> A + 408 <= lo -> 0 < A -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 c2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom asegs)
/\ munch [(A, A + 408); (usp + -32, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp
/\ rw_cells asegs m1 A (stream_cells_x Bd bst L q ns hdr os))
(MS (mkR (Z_to_bv 64 RA_le_realloc2) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) s1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 ns) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_le_realloc2)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros OS LH Q0 FR ST LO ALO A0 MI.
unfold RA_le_realloc2, exp_frame, stream_cells_x, wz in *.
replace (ret_pc (Z_to_bv 64 0xb8ee4)) with (Z_to_bv 64 0xb8ee4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(A, A + 408); (usp + -32, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
astep. sh_if.
ato 0xb8f18. release_frame FR ST usp. astep. astep.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact OS].
Qed.
