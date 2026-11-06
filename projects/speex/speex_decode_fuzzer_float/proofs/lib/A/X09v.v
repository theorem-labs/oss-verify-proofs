(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1ch X1cg X1dk X1cs X1dg X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X0ae X09n.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X110 X10a.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10a.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition RA_stream_init_memset : Z := 0xc1218.
Definition RA_stream_init_malloc1 : Z := 0xc122c.
Definition RA_stream_init_malloc2 : Z := 0xc123c.
Definition RA_stream_init_malloc3 : Z := 0xc124c.

Definition init_os (b l g : option bptr) (ser : Z) : stream_st bptr :=
mkStream b [] 16384 0 0 l [] g [] 1024 0 0 0 0 0 0 ser 0 0 0.

Lemma stream_cells_init : forall m A Bd L Gv ser (z16 z320 z24 : list byte),
z16 = repeat (Z_to_bv 8 0) 16 -> z320 = repeat (Z_to_bv 8 0) 320 -> z24 = repeat (Z_to_bv 8 0) 24 ->
rw_cells bsegs m A [C8 (Z_to_bv 64 Bd); C8 (Z_to_bv 64 16384); CB 16 z16; C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 Gv); C8 (Z_to_bv 64 1024);
CB 320 z320; C8 (Z_to_bv 64 ser); CB 24 z24] ->
forall b l g, rw_cells bsegs m A (stream_cells Bd L Gv zero_hdr (init_os b l g ser)).
Proof.
intros m A Bd L Gv ser z16 z320 z24 -> -> -> H b l g.
eapply rw_cells_recell; [exact H| vm_compute; repeat split; reflexivity| | reflexivity].
unfold stream_cells, wz, zero_hdr, init_os. cbn [os_body_storage os_body_fill os_body_returned os_lacing_storage os_lacing_fill os_lacing_packet os_lacing_returned
os_header_fill os_e_o_s os_b_o_s os_serialno os_pageno os_packetno os_granulepos].
cbn [cells_bytes cbytes].
generalize (le8 (Z_to_bv 64 Bd)) (le8 (Z_to_bv 64 L)) (le8 (Z_to_bv 64 Gv)) (le8 (Z_to_bv 64 ser)). intros lb ll lg ls.
vm_compute. reflexivity.
Qed.

Definition init_frame (ra s0 s1 s2 s3 s4 : word) : list cell := [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma stream_init_w1 : forall (A ser usp lo : Z)
(ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
0 < A < 2^64 -> stk bsegs m lo usp -> lo <= usp - 48 -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 RA_stream_init_memset) (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 (-1)) (Z_to_bv 64 A)
(Z_to_bv 64 (A + 16)) (Z_to_bv 64 0) (Z_to_bv 64 392) a3 a4 a5 a6 a7 (Z_to_bv 64 ser) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_memset) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -48, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -48)
/\ rw_cells bsegs m1 (usp + -48) (init_frame ra s0 s1 s2 s3 s4))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 ser) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_stream_init) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros A0 ST LO MI.
unfold A_ogg_stream_init, RA_stream_init_memset, oe_memset, init_frame.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -48, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
carve_frame 48%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xc11fc. astep. sh_if.
ato 0x663f4.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.

Definition zb (n : nat) : list byte := repeat (Z_to_bv 8 0) n.

Lemma stream_init_w2 : forall (A : Z) (j16 : list byte)
(sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m A [CB 16 j16] -> rw_cells bsegs m (A + 16) [CB 392 (zb 392)] -> 0 < A -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (j8 : list byte),
ms = MS (mkR (Z_to_bv 64 RA_stream_init_malloc1) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
(Z_to_bv 64 16384) (Z_to_bv 64 1024) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_malloc) fc None m1 (seg_rom bsegs)
/\ munch [(A, A + 408)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 A [CB 8 j8; C8 (Z_to_bv 64 16384); CB 16 (zb 16); CB 8 (zb 8); CB 8 (zb 8); C8 (Z_to_bv 64 1024); CB 320 (zb 320); CB 8 (zb 8); CB 24 (zb 24)])
(MS (mkR (Z_to_bv 64 RA_stream_init_memset) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_stream_init_memset)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros HD ZR A0 MI.
unfold RA_stream_init_memset, RA_stream_init_malloc1, oe_malloc.
replace (ret_pc (Z_to_bv 64 0xc1218)) with (Z_to_bv 64 0xc1218) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ ZR) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (munch_refl [(A, A + 408)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in HD; [| reflexivity]. cbn [mk_CB_cells app] in HD.
apply (rw_cells_split_CB bsegs _ _ [] 392 _ [] [16; 8; 8; 8; 320; 8; 24]%nat) in ZR; [| reflexivity]. cbn [mk_CB_cells app] in ZR.
ato 0x67f84.
chunk_cat HD ZR.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact HD.
Qed.

Lemma stream_init_w3 : forall (A Bd : Z) (j8 : list byte)
(sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m A [CB 8 j8; C8 (Z_to_bv 64 16384); CB 16 (zb 16); CB 8 (zb 8); CB 8 (zb 8); C8 (Z_to_bv 64 1024); CB 320 (zb 320); CB 8 (zb 8); CB 24 (zb 24)] ->
0 < A -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 RA_stream_init_malloc2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
(Z_to_bv 64 4096) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 Bd) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_malloc) fc None m1 (seg_rom bsegs)
/\ munch [(A, A + 408)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 A [C8 (Z_to_bv 64 Bd); C8 (Z_to_bv 64 16384); CB 16 (zb 16); CB 8 (zb 8); CB 8 (zb 8); C8 (Z_to_bv 64 1024); CB 320 (zb 320); CB 8 (zb 8); CB 24 (zb 24)])
(MS (mkR (Z_to_bv 64 RA_stream_init_malloc1) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 Bd) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_stream_init_malloc1)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros OS A0 MI.
unfold RA_stream_init_malloc1, RA_stream_init_malloc2, oe_malloc.
replace (ret_pc (Z_to_bv 64 0xc122c)) with (Z_to_bv 64 0xc122c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (munch_refl [(A, A + 408)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
ato 0x67f84.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact OS.
Qed.

Lemma stream_init_w4 : forall (A Bd L : Z)
(sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m A [C8 (Z_to_bv 64 Bd); C8 (Z_to_bv 64 16384); CB 16 (zb 16); CB 8 (zb 8); CB 8 (zb 8); C8 (Z_to_bv 64 1024); CB 320 (zb 320); CB 8 (zb 8); CB 24 (zb 24)] ->
0 < A -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 RA_stream_init_malloc3) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
(Z_to_bv 64 8192) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 L) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_malloc) fc None m1 (seg_rom bsegs)
/\ munch [(A, A + 408)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 A [C8 (Z_to_bv 64 Bd); C8 (Z_to_bv 64 16384); CB 16 (zb 16); C8 (Z_to_bv 64 L); CB 8 (zb 8); C8 (Z_to_bv 64 1024); CB 320 (zb 320); CB 8 (zb 8); CB 24 (zb 24)])
(MS (mkR (Z_to_bv 64 RA_stream_init_malloc2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 L) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_stream_init_malloc2)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros OS A0 MI.
unfold RA_stream_init_malloc2, RA_stream_init_malloc3, oe_malloc.
replace (ret_pc (Z_to_bv 64 0xc123c)) with (Z_to_bv 64 0xc123c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (munch_refl [(A, A + 408)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
ato 0x67f84.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact OS.
Qed.

Lemma stream_init_w5 : forall (A Bd L G ser usp lo : Z)
(gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 cra c0 c1 c2 c3 c4 : word) F fc (m : mem),
rw_cells bsegs m A [C8 (Z_to_bv 64 Bd); C8 (Z_to_bv 64 16384); CB 16 (zb 16); C8 (Z_to_bv 64 L); CB 8 (zb 8); C8 (Z_to_bv 64 1024); CB 320 (zb 320); CB 8 (zb 8); CB 24 (zb 24)] ->
rw_cells bsegs m (usp + -48) (init_frame cra c0 c1 c2 c3 c4) -> stk bsegs m lo (usp + -48) -> lo <= usp + -48 -> A + 408 <= lo ->
0 < A -> 0 < Bd < 2^64 -> 0 < L < 2^64 -> 0 < G < 2^64 -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 c2 c3 c4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom bsegs)
/\ munch [(A, A + 408); (usp + -48, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp
/\ forall b l g, rw_cells bsegs m1 A (stream_cells Bd L G zero_hdr (init_os b l g ser)))
(MS (mkR (Z_to_bv 64 RA_stream_init_malloc3) (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 G) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 ser) (Z_to_bv 64 L) (Z_to_bv 64 Bd) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_stream_init_malloc3)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros OS FR ST LO ALO A0 B0 L0 G0 MI.
unfold RA_stream_init_malloc3, init_frame in *.
replace (ret_pc (Z_to_bv 64 0xc124c)) with (Z_to_bv 64 0xc124c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(A, A + 408); (usp + -48, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
ato 0xc1250. astep. sh_if. astep. sh_if. astep. sh_if.
ato 0xc128c. release_frame FR ST usp. astep. astep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
lazymatch goal with OSx : rw_cells bsegs mx A _ |- _ =>
pose proof (stream_cells_init mx A Bd L G ser _ _ _ eq_refl eq_refl eq_refl OSx) as OSI; clear OSx end end.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact OSI].
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition RA_stream_init_memset : Z := 0xb8ae8.
Definition RA_stream_init_malloc1 : Z := 0xb8afc.
Definition RA_stream_init_malloc2 : Z := 0xb8b0c.
Definition RA_stream_init_malloc3 : Z := 0xb8b1c.

Definition init_os (b l g : option bptr) (ser : Z) : stream_st bptr :=
mkStream b [] 16384 0 0 l [] g [] 1024 0 0 0 0 0 0 ser 0 0 0.

Lemma stream_cells_init : forall m A Bd L Gv ser (z16 z320 z24 : list byte),
z16 = repeat (Z_to_bv 8 0) 16 -> z320 = repeat (Z_to_bv 8 0) 320 -> z24 = repeat (Z_to_bv 8 0) 24 ->
rw_cells asegs m A [C8 (Z_to_bv 64 Bd); C8 (Z_to_bv 64 16384); CB 16 z16; C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 Gv); C8 (Z_to_bv 64 1024);
CB 320 z320; C8 (Z_to_bv 64 ser); CB 24 z24] ->
forall b l g, rw_cells asegs m A (stream_cells Bd L Gv zero_hdr (init_os b l g ser)).
Proof.
intros m A Bd L Gv ser z16 z320 z24 -> -> -> H b l g.
eapply rw_cells_recell; [exact H| vm_compute; repeat split; reflexivity| | reflexivity].
unfold stream_cells, wz, zero_hdr, init_os. cbn [os_body_storage os_body_fill os_body_returned os_lacing_storage os_lacing_fill os_lacing_packet os_lacing_returned
os_header_fill os_e_o_s os_b_o_s os_serialno os_pageno os_packetno os_granulepos].
cbn [cells_bytes cbytes].
generalize (le8 (Z_to_bv 64 Bd)) (le8 (Z_to_bv 64 L)) (le8 (Z_to_bv 64 Gv)) (le8 (Z_to_bv 64 ser)). intros lb ll lg ls.
vm_compute. reflexivity.
Qed.

Definition init_frame (ra s0 s1 s2 s3 s4 : word) : list cell := [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma stream_init_w1 : forall (A ser usp lo : Z)
(ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
0 < A < 2^64 -> stk asegs m lo usp -> lo <= usp - 48 -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 RA_stream_init_memset) (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 (-1)) (Z_to_bv 64 A)
(Z_to_bv 64 (A + 16)) (Z_to_bv 64 0) (Z_to_bv 64 392) a3 a4 a5 a6 a7 (Z_to_bv 64 ser) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_memset) fc None m1 (seg_rom asegs)
/\ munch [(usp + -48, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -48)
/\ rw_cells asegs m1 (usp + -48) (init_frame ra s0 s1 s2 s3 s4))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 ser) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_stream_init) fc None m (seg_rom asegs)).
Proof.
intros until m. intros A0 ST LO MI.
unfold A_ogg_stream_init, RA_stream_init_memset, oe_memset, init_frame.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -48, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 48%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xb8acc. astep. sh_if.
ato 0x66308.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.

Definition zb (n : nat) : list byte := repeat (Z_to_bv 8 0) n.

Lemma stream_init_w2 : forall (A : Z) (j16 : list byte)
(sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m A [CB 16 j16] -> rw_cells asegs m (A + 16) [CB 392 (zb 392)] -> 0 < A -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (j8 : list byte),
ms = MS (mkR (Z_to_bv 64 RA_stream_init_malloc1) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
(Z_to_bv 64 16384) (Z_to_bv 64 1024) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_malloc) fc None m1 (seg_rom asegs)
/\ munch [(A, A + 408)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 A [CB 8 j8; C8 (Z_to_bv 64 16384); CB 16 (zb 16); CB 8 (zb 8); CB 8 (zb 8); C8 (Z_to_bv 64 1024); CB 320 (zb 320); CB 8 (zb 8); CB 24 (zb 24)])
(MS (mkR (Z_to_bv 64 RA_stream_init_memset) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_stream_init_memset)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros HD ZR A0 MI.
unfold RA_stream_init_memset, RA_stream_init_malloc1, oe_malloc.
replace (ret_pc (Z_to_bv 64 0xb8ae8)) with (Z_to_bv 64 0xb8ae8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ ZR) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (munch_refl [(A, A + 408)] m) as MU. pose proof (wmono_refl asegs m) as WM.
apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in HD; [| reflexivity]. cbn [mk_CB_cells app] in HD.
apply (rw_cells_split_CB asegs _ _ [] 392 _ [] [16; 8; 8; 8; 320; 8; 24]%nat) in ZR; [| reflexivity]. cbn [mk_CB_cells app] in ZR.
ato 0x67e98.
chunk_cat HD ZR.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact HD.
Qed.

Lemma stream_init_w3 : forall (A Bd : Z) (j8 : list byte)
(sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m A [CB 8 j8; C8 (Z_to_bv 64 16384); CB 16 (zb 16); CB 8 (zb 8); CB 8 (zb 8); C8 (Z_to_bv 64 1024); CB 320 (zb 320); CB 8 (zb 8); CB 24 (zb 24)] ->
0 < A -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 RA_stream_init_malloc2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
(Z_to_bv 64 4096) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 Bd) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_malloc) fc None m1 (seg_rom asegs)
/\ munch [(A, A + 408)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 A [C8 (Z_to_bv 64 Bd); C8 (Z_to_bv 64 16384); CB 16 (zb 16); CB 8 (zb 8); CB 8 (zb 8); C8 (Z_to_bv 64 1024); CB 320 (zb 320); CB 8 (zb 8); CB 24 (zb 24)])
(MS (mkR (Z_to_bv 64 RA_stream_init_malloc1) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 Bd) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_stream_init_malloc1)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros OS A0 MI.
unfold RA_stream_init_malloc1, RA_stream_init_malloc2, oe_malloc.
replace (ret_pc (Z_to_bv 64 0xb8afc)) with (Z_to_bv 64 0xb8afc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (munch_refl [(A, A + 408)] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0x67e98.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact OS.
Qed.

Lemma stream_init_w4 : forall (A Bd L : Z)
(sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m A [C8 (Z_to_bv 64 Bd); C8 (Z_to_bv 64 16384); CB 16 (zb 16); CB 8 (zb 8); CB 8 (zb 8); C8 (Z_to_bv 64 1024); CB 320 (zb 320); CB 8 (zb 8); CB 24 (zb 24)] ->
0 < A -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 RA_stream_init_malloc3) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
(Z_to_bv 64 8192) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 L) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_malloc) fc None m1 (seg_rom asegs)
/\ munch [(A, A + 408)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 A [C8 (Z_to_bv 64 Bd); C8 (Z_to_bv 64 16384); CB 16 (zb 16); C8 (Z_to_bv 64 L); CB 8 (zb 8); C8 (Z_to_bv 64 1024); CB 320 (zb 320); CB 8 (zb 8); CB 24 (zb 24)])
(MS (mkR (Z_to_bv 64 RA_stream_init_malloc2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 L) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_stream_init_malloc2)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros OS A0 MI.
unfold RA_stream_init_malloc2, RA_stream_init_malloc3, oe_malloc.
replace (ret_pc (Z_to_bv 64 0xb8b0c)) with (Z_to_bv 64 0xb8b0c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (munch_refl [(A, A + 408)] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0x67e98.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact OS.
Qed.

Lemma stream_init_w5 : forall (A Bd L G ser usp lo : Z)
(gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 cra c0 c1 c2 c3 c4 : word) F fc (m : mem),
rw_cells asegs m A [C8 (Z_to_bv 64 Bd); C8 (Z_to_bv 64 16384); CB 16 (zb 16); C8 (Z_to_bv 64 L); CB 8 (zb 8); C8 (Z_to_bv 64 1024); CB 320 (zb 320); CB 8 (zb 8); CB 24 (zb 24)] ->
rw_cells asegs m (usp + -48) (init_frame cra c0 c1 c2 c3 c4) -> stk asegs m lo (usp + -48) -> lo <= usp + -48 -> A + 408 <= lo ->
0 < A -> 0 < Bd < 2^64 -> 0 < L < 2^64 -> 0 < G < 2^64 -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 c2 c3 c4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom asegs)
/\ munch [(A, A + 408); (usp + -48, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp
/\ forall b l g, rw_cells asegs m1 A (stream_cells Bd L G zero_hdr (init_os b l g ser)))
(MS (mkR (Z_to_bv 64 RA_stream_init_malloc3) (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 G) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 ser) (Z_to_bv 64 L) (Z_to_bv 64 Bd) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_stream_init_malloc3)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros OS FR ST LO ALO A0 B0 L0 G0 MI.
unfold RA_stream_init_malloc3, init_frame in *.
replace (ret_pc (Z_to_bv 64 0xb8b1c)) with (Z_to_bv 64 0xb8b1c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(A, A + 408); (usp + -48, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0xb8b20. astep. sh_if. astep. sh_if. astep. sh_if.
ato 0xb8b5c. release_frame FR ST usp. astep. astep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
lazymatch goal with OSx : rw_cells asegs mx A _ |- _ =>
pose proof (stream_cells_init mx A Bd L G ser _ _ _ eq_refl eq_refl eq_refl OSx) as OSI; clear OSx end end.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact OSI].
Qed.
