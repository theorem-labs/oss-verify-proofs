(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1ch X1cg X1dk X1cs X1dg.
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

Lemma sync_cells_raw : forall m A D (sy : sync_st bptr),
rw_cells bsegs m A (sync_cells D sy) -> exists j24, rw_cells bsegs m A [C8 (wz D); CB 24 j24].
Proof.
intros m A D sy H. unfold sync_cells in H.
eexists. apply (rw_cells_merge bsegs m A [C8 (wz D)] [C4 (wz (sy_storage sy)); C4 (wz (sy_fill sy)); C4 (wz (sy_returned sy));
C4 (wz (sy_unsynced sy)); C4 (wz (sy_headerbytes sy)); C4 (wz (sy_bodybytes sy))] []). exact H.
Qed.
Lemma sync_cells_zero : forall m A,
rw_cells bsegs m A [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
rw_cells bsegs m A (sync_cells 0 ogg_sync_init).
Proof.
intros m A H. eapply rw_cells_recell; [exact H| cbn; repeat split; reflexivity| vm_compute; reflexivity| reflexivity].
Qed.

Definition RA_sync_clear_free : Z := 0xc168c.

Lemma sync_clear_w1 : forall (A D usp lo : Z) (sy : sync_st bptr)
(ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
0 < A -> 0 < D < 2^64 -> rw_cells bsegs m A (sync_cells D sy) ->
stk bsegs m lo usp -> lo <= usp - 16 -> A + 32 <= lo -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 RA_sync_clear_free) (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 A) s1
(Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_free) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -16, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -16)
/\ rw_cells bsegs m1 (usp + -16) [C8 s0; C8 ra])
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_sync_clear) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros A0 D0 SY ST LO ALO MI.
unfold A_ogg_sync_clear, RA_sync_clear_free, oe_free. unfold sync_cells, wz in SY.
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -16, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
astep. sh_if.
carve_frame 16%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xc1684. astep. sh_if.
ato 0x67f80.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.

Lemma sync_clear_w2 : forall (A D usp lo : Z) (sy : sync_st bptr)
(gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c0 cra : word) F fc (m : mem),
rw_cells bsegs m A (sync_cells D sy) -> rw_cells bsegs m (usp + -16) [C8 c0; C8 cra] ->
stk bsegs m lo (usp + -16) -> lo <= usp + -16 -> A + 32 <= lo -> 0 < A -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom bsegs)
/\ munch [(A, A + 32); (usp + -16, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp
/\ rw_cells bsegs m1 A (sync_cells 0 ogg_sync_init))
(MS (mkR (Z_to_bv 64 RA_sync_clear_free) (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 A) s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sync_clear_free)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SY FR ST LO ALO A0 MI. unfold RA_sync_clear_free.
replace (ret_pc (Z_to_bv 64 0xc168c)) with (Z_to_bv 64 0xc168c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(A, A + 32); (usp + -16, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
destruct (sync_cells_raw _ _ _ _ SY) as [j24 SYR]. clear SY. unfold wz in SYR.
apply (rw_cells_split_CB bsegs _ _ [C8 (Z_to_bv 64 D)] 24 _ [] [8; 8; 8]%nat) in SYR; [| reflexivity]. cbn [mk_CB_cells app] in SYR.
ato 0xc16a4. release_frame FR ST usp. astep. astep. astep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
lazymatch goal with SYx : rw_cells bsegs mx A _ |- _ => pose proof (sync_cells_zero mx A SYx) as SYZ; clear SYx end end.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact SYZ].
Qed.

Lemma sync_clear_nodata : forall (A usp lo : Z) (sy : sync_st bptr)
(ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
0 < A -> rw_cells bsegs m A (sync_cells 0 sy) ->
stk bsegs m lo usp -> lo <= usp - 16 -> A + 32 <= lo -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m1 (seg_rom bsegs)
/\ munch [(A, A + 32); (usp + -16, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp
/\ rw_cells bsegs m1 A (sync_cells 0 ogg_sync_init))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_sync_clear) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros A0 SY ST LO ALO MI. unfold A_ogg_sync_clear.
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(A, A + 32); (usp + -16, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
destruct (sync_cells_raw _ _ _ _ SY) as [j24 SYR]. clear SY. unfold wz in SYR.
apply (rw_cells_split_CB bsegs _ _ [C8 (Z_to_bv 64 0)] 24 _ [] [8; 8; 8]%nat) in SYR; [| reflexivity]. cbn [mk_CB_cells app] in SYR.
astep. sh_if.
carve_frame 16%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xc16a4. release_frame FR ST usp. astep. astep. astep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
lazymatch goal with SYx : rw_cells bsegs mx A _ |- _ => pose proof (sync_cells_zero mx A SYx) as SYZ; clear SYx end end.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact SYZ].
Qed.

Definition RA_stream_clear_free1 : Z := 0xc12b4.
Definition RA_stream_clear_free2 : Z := 0xc12c0.
Definition RA_stream_clear_free3 : Z := 0xc12cc.
Definition RA_stream_clear_memset : Z := 0xc12dc.

Definition zero_hdr : list byte := repeat (Z_to_bv 8 0) 284.
Lemma stream_cells_zero : forall m A,
rw_cells bsegs m A [CB 408 (repeat (Z_to_bv 8 0) 408)] -> rw_cells bsegs m A (stream_cells 0 0 0 zero_hdr stream_zero).
Proof.
intros m A H. eapply rw_cells_recell; [exact H| vm_compute; repeat split; reflexivity| vm_compute; reflexivity| reflexivity].
Qed.

Lemma stream_clear_w1 : forall (A Bd L G usp lo : Z) (hdr : list byte) (os : stream_st bptr)
(ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
0 < A -> 0 < Bd < 2^64 -> rw_cells bsegs m A (stream_cells Bd L G hdr os) -> length hdr = 284%nat ->
stk bsegs m lo usp -> lo <= usp - 16 -> A + 408 <= lo -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 RA_stream_clear_free1) (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 A) s1
(Z_to_bv 64 Bd) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_free) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -16, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -16)
/\ rw_cells bsegs m1 (usp + -16) [C8 s0; C8 ra])
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_stream_clear) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros A0 B0 OS LH ST LO ALO MI.
unfold A_ogg_stream_clear, RA_stream_clear_free1, oe_free. unfold stream_cells, wz in OS.
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -16, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
astep. sh_if.
carve_frame 16%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xc12ac. astep. sh_if.
ato 0x67f80.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.

Lemma stream_clear_w2 : forall (A Bd L G : Z) (hdr : list byte) (os : stream_st bptr)
(sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
0 < L < 2^64 -> rw_cells bsegs m A (stream_cells Bd L G hdr os) -> length hdr = 284%nat -> mem_inv bsegs m ->
evt bsegs (fun ms =>
ms = MS (mkR (Z_to_bv 64 RA_stream_clear_free2) sp gp tp t0 t1 t2 (Z_to_bv 64 A) s1
(Z_to_bv 64 L) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_free) fc None m (seg_rom bsegs))
(MS (mkR (Z_to_bv 64 RA_stream_clear_free1) sp gp tp t0 t1 t2 (Z_to_bv 64 A) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_stream_clear_free1)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros L0 OS LH MI.
unfold RA_stream_clear_free1, RA_stream_clear_free2, oe_free. unfold stream_cells, wz in OS.
replace (ret_pc (Z_to_bv 64 0xc12b4)) with (Z_to_bv 64 0xc12b4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
ato 0xc12b8. astep. sh_if.
ato 0x67f80.
apply evt_done. reflexivity.
Qed.

Lemma stream_clear_w3 : forall (A Bd L G : Z) (hdr : list byte) (os : stream_st bptr)
(sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
0 < G < 2^64 -> rw_cells bsegs m A (stream_cells Bd L G hdr os) -> length hdr = 284%nat -> mem_inv bsegs m ->
evt bsegs (fun ms =>
ms = MS (mkR (Z_to_bv 64 RA_stream_clear_free3) sp gp tp t0 t1 t2 (Z_to_bv 64 A) s1
(Z_to_bv 64 G) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_free) fc None m (seg_rom bsegs))
(MS (mkR (Z_to_bv 64 RA_stream_clear_free2) sp gp tp t0 t1 t2 (Z_to_bv 64 A) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_stream_clear_free2)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros G0 OS LH MI.
unfold RA_stream_clear_free2, RA_stream_clear_free3, oe_free. unfold stream_cells, wz in OS.
replace (ret_pc (Z_to_bv 64 0xc12c0)) with (Z_to_bv 64 0xc12c0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
ato 0xc12c4. astep. sh_if.
ato 0x67f80.
apply evt_done. reflexivity.
Qed.

Lemma stream_clear_w4 : forall (A : Z)
(sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
evt bsegs (fun ms =>
ms = MS (mkR (Z_to_bv 64 RA_stream_clear_memset) sp gp tp t0 t1 t2 (Z_to_bv 64 A) s1
(Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 408) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_memset) fc None m (seg_rom bsegs))
(MS (mkR (Z_to_bv 64 RA_stream_clear_free3) sp gp tp t0 t1 t2 (Z_to_bv 64 A) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_stream_clear_free3)) fc None m (seg_rom bsegs)).
Proof.
intros until m.
unfold RA_stream_clear_free3, RA_stream_clear_memset, oe_memset.
replace (ret_pc (Z_to_bv 64 0xc12cc)) with (Z_to_bv 64 0xc12cc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0x663f4.
apply evt_done. reflexivity.
Qed.

Lemma stream_clear_w5 : forall (A usp lo : Z)
(gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c0 cra : word) F fc (m : mem),
rw_cells bsegs m (usp + -16) [C8 c0; C8 cra] -> stk bsegs m lo (usp + -16) -> lo <= usp + -16 -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -16, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp)
(MS (mkR (Z_to_bv 64 RA_stream_clear_memset) (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_stream_clear_memset)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR ST LO MI. unfold RA_stream_clear_memset.
replace (ret_pc (Z_to_bv 64 0xc12dc)) with (Z_to_bv 64 0xc12dc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -16, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
ato 0xc12e4. release_frame FR ST usp. astep. astep. astep.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
Qed.

Lemma stream_clear_w1_null : forall (A usp lo : Z) (hdr : list byte) (os : stream_st bptr)
(ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
0 < A -> rw_cells bsegs m A (stream_cells 0 0 0 hdr os) -> length hdr = 284%nat ->
stk bsegs m lo usp -> lo <= usp - 16 -> A + 408 <= lo -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 RA_stream_clear_memset) (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 A) s1
(Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 408) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_memset) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -16, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -16)
/\ rw_cells bsegs m1 (usp + -16) [C8 s0; C8 ra])
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_stream_clear) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros A0 OS LH ST LO ALO MI.
unfold A_ogg_stream_clear, RA_stream_clear_memset, oe_memset. unfold stream_cells, wz in OS.
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -16, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
astep. sh_if.
carve_frame 16%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0x663f4.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma sync_cells_raw : forall m A D (sy : sync_st bptr),
rw_cells asegs m A (sync_cells D sy) -> exists j24, rw_cells asegs m A [C8 (wz D); CB 24 j24].
Proof.
intros m A D sy H. unfold sync_cells in H.
eexists. apply (rw_cells_merge asegs m A [C8 (wz D)] [C4 (wz (sy_storage sy)); C4 (wz (sy_fill sy)); C4 (wz (sy_returned sy));
C4 (wz (sy_unsynced sy)); C4 (wz (sy_headerbytes sy)); C4 (wz (sy_bodybytes sy))] []). exact H.
Qed.
Lemma sync_cells_zero : forall m A,
rw_cells asegs m A [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
rw_cells asegs m A (sync_cells 0 ogg_sync_init).
Proof.
intros m A H. eapply rw_cells_recell; [exact H| cbn; repeat split; reflexivity| vm_compute; reflexivity| reflexivity].
Qed.

Definition RA_sync_clear_free : Z := 0xb8f5c.

Lemma sync_clear_w1 : forall (A D usp lo : Z) (sy : sync_st bptr)
(ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
0 < A -> 0 < D < 2^64 -> rw_cells asegs m A (sync_cells D sy) ->
stk asegs m lo usp -> lo <= usp - 16 -> A + 32 <= lo -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 RA_sync_clear_free) (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 A) s1
(Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_free) fc None m1 (seg_rom asegs)
/\ munch [(usp + -16, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -16)
/\ rw_cells asegs m1 (usp + -16) [C8 s0; C8 ra])
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_sync_clear) fc None m (seg_rom asegs)).
Proof.
intros until m. intros A0 D0 SY ST LO ALO MI.
unfold A_ogg_sync_clear, RA_sync_clear_free, oe_free. unfold sync_cells, wz in SY.
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -16, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
astep. sh_if.
carve_frame 16%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xb8f54. astep. sh_if.
ato 0x67e94.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.

Lemma sync_clear_w2 : forall (A D usp lo : Z) (sy : sync_st bptr)
(gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c0 cra : word) F fc (m : mem),
rw_cells asegs m A (sync_cells D sy) -> rw_cells asegs m (usp + -16) [C8 c0; C8 cra] ->
stk asegs m lo (usp + -16) -> lo <= usp + -16 -> A + 32 <= lo -> 0 < A -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom asegs)
/\ munch [(A, A + 32); (usp + -16, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp
/\ rw_cells asegs m1 A (sync_cells 0 ogg_sync_init))
(MS (mkR (Z_to_bv 64 RA_sync_clear_free) (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 A) s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sync_clear_free)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SY FR ST LO ALO A0 MI. unfold RA_sync_clear_free.
replace (ret_pc (Z_to_bv 64 0xb8f5c)) with (Z_to_bv 64 0xb8f5c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(A, A + 32); (usp + -16, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
destruct (sync_cells_raw _ _ _ _ SY) as [j24 SYR]. clear SY. unfold wz in SYR.
apply (rw_cells_split_CB asegs _ _ [C8 (Z_to_bv 64 D)] 24 _ [] [8; 8; 8]%nat) in SYR; [| reflexivity]. cbn [mk_CB_cells app] in SYR.
ato 0xb8f74. release_frame FR ST usp. astep. astep. astep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
lazymatch goal with SYx : rw_cells asegs mx A _ |- _ => pose proof (sync_cells_zero mx A SYx) as SYZ; clear SYx end end.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact SYZ].
Qed.

Lemma sync_clear_nodata : forall (A usp lo : Z) (sy : sync_st bptr)
(ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
0 < A -> rw_cells asegs m A (sync_cells 0 sy) ->
stk asegs m lo usp -> lo <= usp - 16 -> A + 32 <= lo -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m1 (seg_rom asegs)
/\ munch [(A, A + 32); (usp + -16, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp
/\ rw_cells asegs m1 A (sync_cells 0 ogg_sync_init))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_sync_clear) fc None m (seg_rom asegs)).
Proof.
intros until m. intros A0 SY ST LO ALO MI. unfold A_ogg_sync_clear.
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(A, A + 32); (usp + -16, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
destruct (sync_cells_raw _ _ _ _ SY) as [j24 SYR]. clear SY. unfold wz in SYR.
apply (rw_cells_split_CB asegs _ _ [C8 (Z_to_bv 64 0)] 24 _ [] [8; 8; 8]%nat) in SYR; [| reflexivity]. cbn [mk_CB_cells app] in SYR.
astep. sh_if.
carve_frame 16%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xb8f74. release_frame FR ST usp. astep. astep. astep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
lazymatch goal with SYx : rw_cells asegs mx A _ |- _ => pose proof (sync_cells_zero mx A SYx) as SYZ; clear SYx end end.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact SYZ].
Qed.

Definition RA_stream_clear_free1 : Z := 0xb8b84.
Definition RA_stream_clear_free2 : Z := 0xb8b90.
Definition RA_stream_clear_free3 : Z := 0xb8b9c.
Definition RA_stream_clear_memset : Z := 0xb8bac.

Definition zero_hdr : list byte := repeat (Z_to_bv 8 0) 284.
Lemma stream_cells_zero : forall m A,
rw_cells asegs m A [CB 408 (repeat (Z_to_bv 8 0) 408)] -> rw_cells asegs m A (stream_cells 0 0 0 zero_hdr stream_zero).
Proof.
intros m A H. eapply rw_cells_recell; [exact H| vm_compute; repeat split; reflexivity| vm_compute; reflexivity| reflexivity].
Qed.

Lemma stream_clear_w1 : forall (A Bd L G usp lo : Z) (hdr : list byte) (os : stream_st bptr)
(ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
0 < A -> 0 < Bd < 2^64 -> rw_cells asegs m A (stream_cells Bd L G hdr os) -> length hdr = 284%nat ->
stk asegs m lo usp -> lo <= usp - 16 -> A + 408 <= lo -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 RA_stream_clear_free1) (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 A) s1
(Z_to_bv 64 Bd) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_free) fc None m1 (seg_rom asegs)
/\ munch [(usp + -16, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -16)
/\ rw_cells asegs m1 (usp + -16) [C8 s0; C8 ra])
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_stream_clear) fc None m (seg_rom asegs)).
Proof.
intros until m. intros A0 B0 OS LH ST LO ALO MI.
unfold A_ogg_stream_clear, RA_stream_clear_free1, oe_free. unfold stream_cells, wz in OS.
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -16, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
astep. sh_if.
carve_frame 16%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xb8b7c. astep. sh_if.
ato 0x67e94.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.

Lemma stream_clear_w2 : forall (A Bd L G : Z) (hdr : list byte) (os : stream_st bptr)
(sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
0 < L < 2^64 -> rw_cells asegs m A (stream_cells Bd L G hdr os) -> length hdr = 284%nat -> mem_inv asegs m ->
evt asegs (fun ms =>
ms = MS (mkR (Z_to_bv 64 RA_stream_clear_free2) sp gp tp t0 t1 t2 (Z_to_bv 64 A) s1
(Z_to_bv 64 L) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_free) fc None m (seg_rom asegs))
(MS (mkR (Z_to_bv 64 RA_stream_clear_free1) sp gp tp t0 t1 t2 (Z_to_bv 64 A) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_stream_clear_free1)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros L0 OS LH MI.
unfold RA_stream_clear_free1, RA_stream_clear_free2, oe_free. unfold stream_cells, wz in OS.
replace (ret_pc (Z_to_bv 64 0xb8b84)) with (Z_to_bv 64 0xb8b84) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0xb8b88. astep. sh_if.
ato 0x67e94.
apply evt_done. reflexivity.
Qed.

Lemma stream_clear_w3 : forall (A Bd L G : Z) (hdr : list byte) (os : stream_st bptr)
(sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
0 < G < 2^64 -> rw_cells asegs m A (stream_cells Bd L G hdr os) -> length hdr = 284%nat -> mem_inv asegs m ->
evt asegs (fun ms =>
ms = MS (mkR (Z_to_bv 64 RA_stream_clear_free3) sp gp tp t0 t1 t2 (Z_to_bv 64 A) s1
(Z_to_bv 64 G) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_free) fc None m (seg_rom asegs))
(MS (mkR (Z_to_bv 64 RA_stream_clear_free2) sp gp tp t0 t1 t2 (Z_to_bv 64 A) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_stream_clear_free2)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros G0 OS LH MI.
unfold RA_stream_clear_free2, RA_stream_clear_free3, oe_free. unfold stream_cells, wz in OS.
replace (ret_pc (Z_to_bv 64 0xb8b90)) with (Z_to_bv 64 0xb8b90) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0xb8b94. astep. sh_if.
ato 0x67e94.
apply evt_done. reflexivity.
Qed.

Lemma stream_clear_w4 : forall (A : Z)
(sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
evt asegs (fun ms =>
ms = MS (mkR (Z_to_bv 64 RA_stream_clear_memset) sp gp tp t0 t1 t2 (Z_to_bv 64 A) s1
(Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 408) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_memset) fc None m (seg_rom asegs))
(MS (mkR (Z_to_bv 64 RA_stream_clear_free3) sp gp tp t0 t1 t2 (Z_to_bv 64 A) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_stream_clear_free3)) fc None m (seg_rom asegs)).
Proof.
intros until m.
unfold RA_stream_clear_free3, RA_stream_clear_memset, oe_memset.
replace (ret_pc (Z_to_bv 64 0xb8b9c)) with (Z_to_bv 64 0xb8b9c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0x66308.
apply evt_done. reflexivity.
Qed.

Lemma stream_clear_w5 : forall (A usp lo : Z)
(gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c0 cra : word) F fc (m : mem),
rw_cells asegs m (usp + -16) [C8 c0; C8 cra] -> stk asegs m lo (usp + -16) -> lo <= usp + -16 -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom asegs)
/\ munch [(usp + -16, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp)
(MS (mkR (Z_to_bv 64 RA_stream_clear_memset) (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_stream_clear_memset)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FR ST LO MI. unfold RA_stream_clear_memset.
replace (ret_pc (Z_to_bv 64 0xb8bac)) with (Z_to_bv 64 0xb8bac) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -16, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0xb8bb4. release_frame FR ST usp. astep. astep. astep.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
Qed.

Lemma stream_clear_w1_null : forall (A usp lo : Z) (hdr : list byte) (os : stream_st bptr)
(ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
0 < A -> rw_cells asegs m A (stream_cells 0 0 0 hdr os) -> length hdr = 284%nat ->
stk asegs m lo usp -> lo <= usp - 16 -> A + 408 <= lo -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 RA_stream_clear_memset) (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 A) s1
(Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 408) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_memset) fc None m1 (seg_rom asegs)
/\ munch [(usp + -16, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -16)
/\ rw_cells asegs m1 (usp + -16) [C8 s0; C8 ra])
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_stream_clear) fc None m (seg_rom asegs)).
Proof.
intros until m. intros A0 OS LH ST LO ALO MI.
unfold A_ogg_stream_clear, RA_stream_clear_memset, oe_memset. unfold stream_cells, wz in OS.
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -16, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
astep. sh_if.
carve_frame 16%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0x66308.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.
