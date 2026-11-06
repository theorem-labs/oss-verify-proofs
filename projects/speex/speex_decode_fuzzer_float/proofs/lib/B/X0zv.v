(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1df X1ck X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05l X09f X09e.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0z5 X0x2 X0zp.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation mem := (word -> option byte).

Definition SC_DEAD : nbscope := NBSC false false false false false.
Definition PC_stack_free_5 : Z := 0x519c0.
Definition RA_nbd_sfree : Z := 0xa4480.

Lemma nbd_x1 : forall (usp f sf rv : Z) (ra gp tp t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(h8 h16 : word) (rs : list byte) (s : nbslots) F fc (m : mem),
0 < f < 2^47 -> f mod 64 = 0 -> hidp (f + 24 <= sf \/ sf + 256 <= f) -> 0 <= sf -> usp < 2^63 ->
f + 24 <= usp + -576 -> sf + 256 <= usp + -576 ->
v48 s = Z_to_bv 64 f -> v56 s = Z_to_bv 64 f -> rw_cells bsegs m (usp + -576) (slot_cells s) ->
rw_cells bsegs m f [C8 (Z_to_bv 64 0x41b58ab3); C8 h8; C8 h16] -> rw_cells bsegs m sf (nbd_shadow SC_X rs) -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 RA_nbd_sfree) (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576))
(Z_to_bv 64 f) (Z_to_bv 64 1088) (Z_to_bv 64 sf) a3 a4 a5 a6 a7
(Z_to_bv 64 rv) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PC_stack_free_5) fc None m1 (seg_rom bsegs)
/\ munch [(f, f + 8); (sf, sf + 8)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 f [C8 (Z_to_bv 64 0x45e0360e); C8 h8; C8 h16] /\ rw_cells bsegs m1 sf (nbd_shadow SC_DEAD rs)
/\ rw_cells bsegs m1 (usp + -576) (slot_cells s))
(MS (mkR ra (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 (Z_to_bv 64 sf) a3 a4 a5 a6 a7
(Z_to_bv 64 rv) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PC_NBD_X) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros F0 F64 FSA SF0 SPH FU SFU E48 E56 SL HDR SH MI.
unfold PC_NBD_X, PC_stack_free_5, RA_nbd_sfree, nbd_shadow, nbd_shadow_bytes, SC_X, SC_DEAD, sh_run, bF1, bF2, bF3, bF8, b04, z8 in *.
cbn [sc_top sc_lpc sc_main sc_innov2 sc_iq map repeat app] in *.
pose proof (rw_cells_bound _ _ _ _ SH) as BS. cbn [cells_size csize Nat.add] in BS.
pose proof (FSA : _ \/ _) as FSA'.
unfold slot_cells in SL. rewrite E48, E56 in SL.
pose proof (rw_cells_bound _ _ _ _ SL) as BL. cbn [cells_size csize Nat.add] in BL.
pose proof (munch_refl [(f, f + 8); (sf, sf + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
bato 0xa4474. astep. sh_if.
bato 0x519c0.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact HDR|]. split; [exact SH|].
unfold slot_cells. rewrite E48, E56. exact SL.
Qed.

Lemma nbd_x2 : forall (usp lo rv : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 : word) (js : list byte) F fc (m : mem),
stk bsegs m lo (usp + -576) -> lo <= usp + -576 -> SH_HI <= lo -> usp < 2^63 ->
rw_cells bsegs m (usp + -576) [CB 376 js] ->
rw_cells bsegs m (usp + -200) [C8 f11; C8 f10; C8 f9; C8 f8; C8 f7; C8 f6; C8 f5; C8 f4; C8 f3; C8 f2; C8 f1; C8 f0;
C8 c11; C8 c10; C8 c9; C8 c8; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra] ->
mem_inv bsegs m -> frm0 fc ->
evt bsegs (fun ms => exists (F' : bvmap 5 word),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 t3 t4 t5 t6)
F' (ret_pc cra) fc None m (seg_rom bsegs)
/\ stk bsegs m lo usp)
(MS (mkR (Z_to_bv 64 RA_nbd_sfree) (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 rv) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_nbd_sfree)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST LO LOS SPH SL SV MI FRM.
unfold RA_nbd_sfree in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof ST as (STa & STb & _).
replace (ret_pc (Z_to_bv 64 0xa4480)) with (Z_to_bv 64 0xa4480) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bato 0xa44fc.
chunk_cat SL SV. release_frame SL ST usp.
astep. astep.
apply evt_done. eexists. split; [reflexivity| exact ST].
Qed.
