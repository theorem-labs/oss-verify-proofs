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

Definition RA_buf_memmove : Z := 0xc16f4.
Definition RA_buf_realloc : Z := 0xc1734.
Definition RA_buf_malloc : Z := 0xc1764.
Definition PC_buf_p2 : Z := 0xc16fc.

Definition buf_frame (ra s0 s1 : word) (j8 : list byte) : list cell := [CB 8 j8; C8 s1; C8 s0; C8 ra].

Lemma buf_w1a : forall (A D size usp lo : Z) (sy : sync_st bptr)
(ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m A (sync_cells D sy) -> sync_fields_ok sy -> sy_returned sy = 0 ->
stk bsegs m lo usp -> lo <= usp - 32 -> A + 32 <= lo -> 0 < A -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (j8 : list byte) (a1' : word),
ms = MS (mkR ra (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 size)
(Z_to_bv 64 (sy_storage sy)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PC_buf_p2) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -32, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -32)
/\ rw_cells bsegs m1 (usp + -32) (buf_frame ra s0 s1 j8))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_sync_buffer) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SY FOK RET0 ST LO ALO A0 MI.
unfold A_ogg_sync_buffer, PC_buf_p2, buf_frame. unfold sync_cells, wz in SY.
pose proof FOK as (Fs & Ff & Fr & Fu & Fh & Fb). unfold int31 in Fs, Ff, Fr, Fu, Fh, Fb.
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
carve_frame 32%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xc16c8. rewrite (sx32_lit (sy_storage sy)) by (unfold int31; lia). astep. sh_if.
ato 0xc16d4. rewrite (sx32_lit (sy_returned sy)) by (unfold int31; lia). rewrite RET0. astep.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.

Definition sync_cells_c (D st fill' ret' : Z) (sy : sync_st bptr) : list cell :=
[C8 (wz D); C4 (wz st); C4 (wz fill'); C4 (wz ret');
C4 (wz (sy_unsynced sy)); C4 (wz (sy_headerbytes sy)); C4 (wz (sy_bodybytes sy))].

Lemma buf_w1b : forall (A D size usp lo : Z) (sy : sync_st bptr)
(ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m A (sync_cells D sy) -> sync_fields_ok sy -> sy_returned sy <> 0 -> sy_fill sy - sy_returned sy <= 0 -> sy_returned sy <= sy_fill sy ->
stk bsegs m lo usp -> lo <= usp - 32 -> A + 32 <= lo -> 0 < A -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (j8 : list byte) (a1' a2' : word),
ms = MS (mkR ra (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 size)
(Z_to_bv 64 (sy_storage sy)) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PC_buf_p2) fc None m1 (seg_rom bsegs)
/\ munch [(A, A + 32); (usp + -32, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -32)
/\ rw_cells bsegs m1 (usp + -32) (buf_frame ra s0 s1 j8)
/\ rw_cells bsegs m1 A (sync_cells_c D (sy_storage sy) (sy_fill sy - sy_returned sy) 0 sy))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_sync_buffer) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SY FOK RET0 FILL0 RF ST LO ALO A0 MI.
unfold A_ogg_sync_buffer, PC_buf_p2, buf_frame, sync_cells_c. unfold sync_cells, wz in *.
pose proof FOK as (Fs & Ff & Fr & Fu & Fh & Fb). unfold int31 in Fs, Ff, Fr, Fu, Fh, Fb.
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(A, A + 32); (usp + -32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
carve_frame 32%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xc16c8. rewrite (sx32_lit (sy_storage sy)) by (unfold int31; lia). astep. sh_if.
ato 0xc16d4. rewrite (sx32_lit (sy_returned sy)) by (unfold int31; lia). astep. sh_if.
ato 0xc16dc. rewrite (sx32_lit (sy_fill sy)) by (unfold int31; lia). astep.
rewrite (swrap32_small (sy_fill sy - sy_returned sy)) by lia.
astep. astep. sh_if.
ato 0xc16fc.
apply evt_done. do 4 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact SY].
Qed.

Lemma buf_w1c : forall (A D size usp lo : Z) (sy : sync_st bptr)
(ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m A (sync_cells D sy) -> sync_fields_ok sy -> sy_returned sy <> 0 -> 0 < sy_fill sy - sy_returned sy -> 0 <= D -> D + sy_returned sy < 2^64 ->
stk bsegs m lo usp -> lo <= usp - 32 -> A + 32 <= lo -> 0 < A -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (j8 : list byte),
ms = MS (mkR (Z_to_bv 64 RA_buf_memmove) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 size)
(Z_to_bv 64 D) (Z_to_bv 64 (D + sy_returned sy)) (Z_to_bv 64 (sy_fill sy - sy_returned sy)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_memmove) fc None m1 (seg_rom bsegs)
/\ munch [(A, A + 32); (usp + -32, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -32)
/\ rw_cells bsegs m1 (usp + -32) (buf_frame ra s0 s1 j8)
/\ rw_cells bsegs m1 A (sync_cells_c D (sy_storage sy) (sy_fill sy - sy_returned sy) (sy_returned sy) sy))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_sync_buffer) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SY FOK RET0 FILL0 D0 DR ST LO ALO A0 MI.
unfold A_ogg_sync_buffer, RA_buf_memmove, oe_memmove, buf_frame, sync_cells_c. unfold sync_cells, wz in *.
pose proof FOK as (Fs & Ff & Fr & Fu & Fh & Fb). unfold int31 in Fs, Ff, Fr, Fu, Fh, Fb.
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(A, A + 32); (usp + -32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
carve_frame 32%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xc16c8. rewrite (sx32_lit (sy_storage sy)) by (unfold int31; lia). astep. sh_if.
ato 0xc16d4. rewrite (sx32_lit (sy_returned sy)) by (unfold int31; lia). astep. sh_if.
ato 0xc16dc. rewrite (sx32_lit (sy_fill sy)) by (unfold int31; lia). astep.
rewrite (swrap32_small (sy_fill sy - sy_returned sy)) by lia.
astep. astep. sh_if.
ato 0x663f8.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact SY].
Qed.

Lemma buf_w1d : forall (A D size : Z) (sy : sync_st bptr) (fill' ret' : Z)
(ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m A (sync_cells_c D (sy_storage sy) fill' ret' sy) -> sync_fields_ok sy -> 0 < A -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 size)
(Z_to_bv 64 (sy_storage sy)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PC_buf_p2) fc None m1 (seg_rom bsegs)
/\ munch [(A, A + 32)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 A (sync_cells_c D (sy_storage sy) fill' 0 sy))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 size) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_buf_memmove)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SY FOK A0 MI.
unfold RA_buf_memmove, PC_buf_p2, sync_cells_c, wz in *.
replace (ret_pc (Z_to_bv 64 0xc16f4)) with (Z_to_bv 64 0xc16f4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof FOK as (Fs & Ff & Fr & Fu & Fh & Fb). unfold int31 in Fs, Ff, Fr, Fu, Fh, Fb.
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (munch_refl [(A, A + 32)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
astep. rewrite (sx32_lit (sy_storage sy)) by (unfold int31; lia). astep.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact SY.
Qed.

Lemma buf_w2a : forall (A D st fl rt size usp lo : Z) (sy : sync_st bptr) (j8 : list byte)
(ra0 gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 cra c0 c1 : word) F fc (m : mem),
rw_cells bsegs m A (sync_cells_c D st fl rt sy) -> 0 <= st < 2^31 -> 0 <= fl <= st -> 0 <= size < 2^31 -> size <= st - fl ->
rw_cells bsegs m (usp + -32) (buf_frame cra c0 c1 j8) -> stk bsegs m lo (usp + -32) -> lo <= usp + -32 -> A + 32 <= lo -> 0 < A -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (a1' : word),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 (D + fl)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -32, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp)
(MS (mkR ra0 (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 size) (Z_to_bv 64 st) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PC_buf_p2) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SY Hst Hfl Hsz FITS FR ST LO ALO A0 MI.
unfold PC_buf_p2, buf_frame, sync_cells_c, wz in *.
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
astep. rewrite (sx32_lit fl) by (unfold int31; lia). astep. rewrite (swrap32_small (st - fl)) by lia.
astep. sh_if.
ato 0xc1794. release_frame FR ST usp. astep. astep.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
Qed.

Lemma buf_w2b : forall (A D st fl rt size : Z) (sy : sync_st bptr)
(ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m A (sync_cells_c D st fl rt sy) -> 0 <= st < 2^31 -> 0 <= fl <= st -> 0 <= size < 2^31 -> st - fl < size -> size + fl + 4096 < 2^31 ->
0 < D < 2^64 -> 0 < A -> mem_inv bsegs m ->
evt bsegs (fun ms =>
ms = MS (mkR (Z_to_bv 64 RA_buf_realloc) sp gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 (size + fl + 4096))
(Z_to_bv 64 D) (Z_to_bv 64 (size + fl + 4096)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_realloc) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 size) (Z_to_bv 64 st) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PC_buf_p2) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SY Hst Hfl Hsz GROW NB D0 A0 MI.
unfold PC_buf_p2, RA_buf_realloc, oe_realloc, sync_cells_c, wz in *.
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
astep. rewrite (sx32_lit fl) by (unfold int31; lia). astep. rewrite (swrap32_small (st - fl)) by lia.
astep. sh_if.
ato 0xc1714. astep. sh_if.
ato 0xc1728. astep. sh_if.
ato 0x67f8c.
apply evt_done. reflexivity.
Qed.

Lemma buf_w2c : forall (A st fl rt size : Z) (sy : sync_st bptr)
(ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m A (sync_cells_c 0 st fl rt sy) -> 0 <= st < 2^31 -> 0 <= fl <= st -> 0 <= size < 2^31 -> st - fl < size -> size + fl + 4096 < 2^31 ->
0 < A -> mem_inv bsegs m ->
evt bsegs (fun ms => exists a1' : word,
ms = MS (mkR (Z_to_bv 64 RA_buf_malloc) sp gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 (size + fl + 4096))
(Z_to_bv 64 (size + fl + 4096)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_malloc) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 size) (Z_to_bv 64 st) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PC_buf_p2) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SY Hst Hfl Hsz GROW NB A0 MI.
unfold PC_buf_p2, RA_buf_malloc, oe_malloc, sync_cells_c, wz in *.
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
astep. rewrite (sx32_lit fl) by (unfold int31; lia). astep. rewrite (swrap32_small (st - fl)) by lia.
astep. sh_if.
ato 0xc1714. astep. sh_if.
ato 0x67f84.
apply evt_done. eexists. reflexivity.
Qed.

Lemma buf_w3b : forall (A D q st fl rt ns usp lo : Z) (sy : sync_st bptr) (j8 : list byte)
(gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 cra c0 c1 : word) F fc (m : mem),
rw_cells bsegs m A (sync_cells_c D st fl rt sy) -> 0 <= fl < 2^31 -> 0 < q < 2^64 ->
rw_cells bsegs m (usp + -32) (buf_frame cra c0 c1 j8) -> stk bsegs m lo (usp + -32) -> lo <= usp + -32 -> A + 32 <= lo -> 0 < A -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (a1' : word),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 (q + fl)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom bsegs)
/\ munch [(A, A + 32); (usp + -32, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp
/\ rw_cells bsegs m1 A (sync_cells_c q ns fl rt sy))
(MS (mkR (Z_to_bv 64 RA_buf_realloc) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 ns) (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_buf_realloc)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SY Hfl Q0 FR ST LO ALO A0 MI.
unfold RA_buf_realloc, buf_frame, sync_cells_c, wz in *.
replace (ret_pc (Z_to_bv 64 0xc1734)) with (Z_to_bv 64 0xc1734) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(A, A + 32); (usp + -32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
astep. sh_if.
astep. rewrite (sx32_lit fl) by (unfold int31; lia).
ato 0xc1794. release_frame FR ST usp. astep. astep.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact SY].
Qed.

Lemma buf_w3c : forall (A D q st fl rt ns usp lo : Z) (sy : sync_st bptr) (j8 : list byte)
(gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 cra c0 c1 : word) F fc (m : mem),
rw_cells bsegs m A (sync_cells_c D st fl rt sy) -> 0 <= fl < 2^31 -> 0 < q < 2^64 ->
rw_cells bsegs m (usp + -32) (buf_frame cra c0 c1 j8) -> stk bsegs m lo (usp + -32) -> lo <= usp + -32 -> A + 32 <= lo -> 0 < A -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (a1' : word),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 (q + fl)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom bsegs)
/\ munch [(A, A + 32); (usp + -32, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp
/\ rw_cells bsegs m1 A (sync_cells_c q ns fl rt sy))
(MS (mkR (Z_to_bv 64 RA_buf_malloc) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 ns) (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_buf_malloc)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SY Hfl Q0 FR ST LO ALO A0 MI.
unfold RA_buf_malloc, buf_frame, sync_cells_c, wz in *.
replace (ret_pc (Z_to_bv 64 0xc1764)) with (Z_to_bv 64 0xc1764) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(A, A + 32); (usp + -32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
astep. sh_if.
astep. rewrite (sx32_lit fl) by (unfold int31; lia).
ato 0xc1794. release_frame FR ST usp. astep. astep.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact SY].
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition RA_buf_memmove : Z := 0xb8fc4.
Definition RA_buf_realloc : Z := 0xb9004.
Definition RA_buf_malloc : Z := 0xb9034.
Definition PC_buf_p2 : Z := 0xb8fcc.

Definition buf_frame (ra s0 s1 : word) (j8 : list byte) : list cell := [CB 8 j8; C8 s1; C8 s0; C8 ra].

Lemma buf_w1a : forall (A D size usp lo : Z) (sy : sync_st bptr)
(ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m A (sync_cells D sy) -> sync_fields_ok sy -> sy_returned sy = 0 ->
stk asegs m lo usp -> lo <= usp - 32 -> A + 32 <= lo -> 0 < A -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (j8 : list byte) (a1' : word),
ms = MS (mkR ra (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 size)
(Z_to_bv 64 (sy_storage sy)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PC_buf_p2) fc None m1 (seg_rom asegs)
/\ munch [(usp + -32, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -32)
/\ rw_cells asegs m1 (usp + -32) (buf_frame ra s0 s1 j8))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_sync_buffer) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SY FOK RET0 ST LO ALO A0 MI.
unfold A_ogg_sync_buffer, PC_buf_p2, buf_frame. unfold sync_cells, wz in SY.
pose proof FOK as (Fs & Ff & Fr & Fu & Fh & Fb). unfold int31 in Fs, Ff, Fr, Fu, Fh, Fb.
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -32, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 32%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xb8f98. rewrite (sx32_lit (sy_storage sy)) by (unfold int31; lia). astep. sh_if.
ato 0xb8fa4. rewrite (sx32_lit (sy_returned sy)) by (unfold int31; lia). rewrite RET0. astep.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.

Definition sync_cells_c (D st fill' ret' : Z) (sy : sync_st bptr) : list cell :=
[C8 (wz D); C4 (wz st); C4 (wz fill'); C4 (wz ret');
C4 (wz (sy_unsynced sy)); C4 (wz (sy_headerbytes sy)); C4 (wz (sy_bodybytes sy))].

Lemma buf_w1b : forall (A D size usp lo : Z) (sy : sync_st bptr)
(ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m A (sync_cells D sy) -> sync_fields_ok sy -> sy_returned sy <> 0 -> sy_fill sy - sy_returned sy <= 0 -> sy_returned sy <= sy_fill sy ->
stk asegs m lo usp -> lo <= usp - 32 -> A + 32 <= lo -> 0 < A -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (j8 : list byte) (a1' a2' : word),
ms = MS (mkR ra (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 size)
(Z_to_bv 64 (sy_storage sy)) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PC_buf_p2) fc None m1 (seg_rom asegs)
/\ munch [(A, A + 32); (usp + -32, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -32)
/\ rw_cells asegs m1 (usp + -32) (buf_frame ra s0 s1 j8)
/\ rw_cells asegs m1 A (sync_cells_c D (sy_storage sy) (sy_fill sy - sy_returned sy) 0 sy))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_sync_buffer) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SY FOK RET0 FILL0 RF ST LO ALO A0 MI.
unfold A_ogg_sync_buffer, PC_buf_p2, buf_frame, sync_cells_c. unfold sync_cells, wz in *.
pose proof FOK as (Fs & Ff & Fr & Fu & Fh & Fb). unfold int31 in Fs, Ff, Fr, Fu, Fh, Fb.
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(A, A + 32); (usp + -32, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 32%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xb8f98. rewrite (sx32_lit (sy_storage sy)) by (unfold int31; lia). astep. sh_if.
ato 0xb8fa4. rewrite (sx32_lit (sy_returned sy)) by (unfold int31; lia). astep. sh_if.
ato 0xb8fac. rewrite (sx32_lit (sy_fill sy)) by (unfold int31; lia). astep.
rewrite (swrap32_small (sy_fill sy - sy_returned sy)) by lia.
astep. astep. sh_if.
ato 0xb8fcc.
apply evt_done. do 4 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact SY].
Qed.

Lemma buf_w1c : forall (A D size usp lo : Z) (sy : sync_st bptr)
(ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m A (sync_cells D sy) -> sync_fields_ok sy -> sy_returned sy <> 0 -> 0 < sy_fill sy - sy_returned sy -> 0 <= D -> D + sy_returned sy < 2^64 ->
stk asegs m lo usp -> lo <= usp - 32 -> A + 32 <= lo -> 0 < A -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (j8 : list byte),
ms = MS (mkR (Z_to_bv 64 RA_buf_memmove) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 size)
(Z_to_bv 64 D) (Z_to_bv 64 (D + sy_returned sy)) (Z_to_bv 64 (sy_fill sy - sy_returned sy)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_memmove) fc None m1 (seg_rom asegs)
/\ munch [(A, A + 32); (usp + -32, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -32)
/\ rw_cells asegs m1 (usp + -32) (buf_frame ra s0 s1 j8)
/\ rw_cells asegs m1 A (sync_cells_c D (sy_storage sy) (sy_fill sy - sy_returned sy) (sy_returned sy) sy))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_sync_buffer) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SY FOK RET0 FILL0 D0 DR ST LO ALO A0 MI.
unfold A_ogg_sync_buffer, RA_buf_memmove, oe_memmove, buf_frame, sync_cells_c. unfold sync_cells, wz in *.
pose proof FOK as (Fs & Ff & Fr & Fu & Fh & Fb). unfold int31 in Fs, Ff, Fr, Fu, Fh, Fb.
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(A, A + 32); (usp + -32, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 32%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xb8f98. rewrite (sx32_lit (sy_storage sy)) by (unfold int31; lia). astep. sh_if.
ato 0xb8fa4. rewrite (sx32_lit (sy_returned sy)) by (unfold int31; lia). astep. sh_if.
ato 0xb8fac. rewrite (sx32_lit (sy_fill sy)) by (unfold int31; lia). astep.
rewrite (swrap32_small (sy_fill sy - sy_returned sy)) by lia.
astep. astep. sh_if.
ato 0x6630c.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact SY].
Qed.

Lemma buf_w1d : forall (A D size : Z) (sy : sync_st bptr) (fill' ret' : Z)
(ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m A (sync_cells_c D (sy_storage sy) fill' ret' sy) -> sync_fields_ok sy -> 0 < A -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 size)
(Z_to_bv 64 (sy_storage sy)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PC_buf_p2) fc None m1 (seg_rom asegs)
/\ munch [(A, A + 32)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 A (sync_cells_c D (sy_storage sy) fill' 0 sy))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 size) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_buf_memmove)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SY FOK A0 MI.
unfold RA_buf_memmove, PC_buf_p2, sync_cells_c, wz in *.
replace (ret_pc (Z_to_bv 64 0xb8fc4)) with (Z_to_bv 64 0xb8fc4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof FOK as (Fs & Ff & Fr & Fu & Fh & Fb). unfold int31 in Fs, Ff, Fr, Fu, Fh, Fb.
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (munch_refl [(A, A + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
astep. rewrite (sx32_lit (sy_storage sy)) by (unfold int31; lia). astep.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact SY.
Qed.

Lemma buf_w2a : forall (A D st fl rt size usp lo : Z) (sy : sync_st bptr) (j8 : list byte)
(ra0 gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 cra c0 c1 : word) F fc (m : mem),
rw_cells asegs m A (sync_cells_c D st fl rt sy) -> 0 <= st < 2^31 -> 0 <= fl <= st -> 0 <= size < 2^31 -> size <= st - fl ->
rw_cells asegs m (usp + -32) (buf_frame cra c0 c1 j8) -> stk asegs m lo (usp + -32) -> lo <= usp + -32 -> A + 32 <= lo -> 0 < A -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (a1' : word),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 (D + fl)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom asegs)
/\ munch [(usp + -32, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp)
(MS (mkR ra0 (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 size) (Z_to_bv 64 st) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PC_buf_p2) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SY Hst Hfl Hsz FITS FR ST LO ALO A0 MI.
unfold PC_buf_p2, buf_frame, sync_cells_c, wz in *.
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -32, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
astep. rewrite (sx32_lit fl) by (unfold int31; lia). astep. rewrite (swrap32_small (st - fl)) by lia.
astep. sh_if.
ato 0xb9064. release_frame FR ST usp. astep. astep.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
Qed.

Lemma buf_w2b : forall (A D st fl rt size : Z) (sy : sync_st bptr)
(ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m A (sync_cells_c D st fl rt sy) -> 0 <= st < 2^31 -> 0 <= fl <= st -> 0 <= size < 2^31 -> st - fl < size -> size + fl + 4096 < 2^31 ->
0 < D < 2^64 -> 0 < A -> mem_inv asegs m ->
evt asegs (fun ms =>
ms = MS (mkR (Z_to_bv 64 RA_buf_realloc) sp gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 (size + fl + 4096))
(Z_to_bv 64 D) (Z_to_bv 64 (size + fl + 4096)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_realloc) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 size) (Z_to_bv 64 st) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PC_buf_p2) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SY Hst Hfl Hsz GROW NB D0 A0 MI.
unfold PC_buf_p2, RA_buf_realloc, oe_realloc, sync_cells_c, wz in *.
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
astep. rewrite (sx32_lit fl) by (unfold int31; lia). astep. rewrite (swrap32_small (st - fl)) by lia.
astep. sh_if.
ato 0xb8fe4. astep. sh_if.
ato 0xb8ff8. astep. sh_if.
ato 0x67ea0.
apply evt_done. reflexivity.
Qed.

Lemma buf_w2c : forall (A st fl rt size : Z) (sy : sync_st bptr)
(ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m A (sync_cells_c 0 st fl rt sy) -> 0 <= st < 2^31 -> 0 <= fl <= st -> 0 <= size < 2^31 -> st - fl < size -> size + fl + 4096 < 2^31 ->
0 < A -> mem_inv asegs m ->
evt asegs (fun ms => exists a1' : word,
ms = MS (mkR (Z_to_bv 64 RA_buf_malloc) sp gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 (size + fl + 4096))
(Z_to_bv 64 (size + fl + 4096)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_malloc) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 size) (Z_to_bv 64 st) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PC_buf_p2) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SY Hst Hfl Hsz GROW NB A0 MI.
unfold PC_buf_p2, RA_buf_malloc, oe_malloc, sync_cells_c, wz in *.
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
astep. rewrite (sx32_lit fl) by (unfold int31; lia). astep. rewrite (swrap32_small (st - fl)) by lia.
astep. sh_if.
ato 0xb8fe4. astep. sh_if.
ato 0x67e98.
apply evt_done. eexists. reflexivity.
Qed.

Lemma buf_w3b : forall (A D q st fl rt ns usp lo : Z) (sy : sync_st bptr) (j8 : list byte)
(gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 cra c0 c1 : word) F fc (m : mem),
rw_cells asegs m A (sync_cells_c D st fl rt sy) -> 0 <= fl < 2^31 -> 0 < q < 2^64 ->
rw_cells asegs m (usp + -32) (buf_frame cra c0 c1 j8) -> stk asegs m lo (usp + -32) -> lo <= usp + -32 -> A + 32 <= lo -> 0 < A -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (a1' : word),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 (q + fl)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom asegs)
/\ munch [(A, A + 32); (usp + -32, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp
/\ rw_cells asegs m1 A (sync_cells_c q ns fl rt sy))
(MS (mkR (Z_to_bv 64 RA_buf_realloc) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 ns) (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_buf_realloc)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SY Hfl Q0 FR ST LO ALO A0 MI.
unfold RA_buf_realloc, buf_frame, sync_cells_c, wz in *.
replace (ret_pc (Z_to_bv 64 0xb9004)) with (Z_to_bv 64 0xb9004) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(A, A + 32); (usp + -32, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
astep. sh_if.
astep. rewrite (sx32_lit fl) by (unfold int31; lia).
ato 0xb9064. release_frame FR ST usp. astep. astep.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact SY].
Qed.

Lemma buf_w3c : forall (A D q st fl rt ns usp lo : Z) (sy : sync_st bptr) (j8 : list byte)
(gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 cra c0 c1 : word) F fc (m : mem),
rw_cells asegs m A (sync_cells_c D st fl rt sy) -> 0 <= fl < 2^31 -> 0 < q < 2^64 ->
rw_cells asegs m (usp + -32) (buf_frame cra c0 c1 j8) -> stk asegs m lo (usp + -32) -> lo <= usp + -32 -> A + 32 <= lo -> 0 < A -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (a1' : word),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 (q + fl)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom asegs)
/\ munch [(A, A + 32); (usp + -32, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp
/\ rw_cells asegs m1 A (sync_cells_c q ns fl rt sy))
(MS (mkR (Z_to_bv 64 RA_buf_malloc) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 ns) (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_buf_malloc)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SY Hfl Q0 FR ST LO ALO A0 MI.
unfold RA_buf_malloc, buf_frame, sync_cells_c, wz in *.
replace (ret_pc (Z_to_bv 64 0xb9034)) with (Z_to_bv 64 0xb9034) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(A, A + 32); (usp + -32, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
astep. sh_if.
astep. rewrite (sx32_lit fl) by (unfold int31; lia).
ato 0xb9064. release_frame FR ST usp. astep. astep.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact SY].
Qed.
