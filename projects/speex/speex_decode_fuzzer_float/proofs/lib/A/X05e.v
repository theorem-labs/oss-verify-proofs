(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05l.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition A_speex_bits_init : Z := 0x97774.
Definition e_wrap_calloc : Z := 0x67f88.
Definition RA_bits_init_calloc : Z := 0x977a0.

Definition bits_fresh : bits_st unit := speex_bits_reset (mkBits tt (zrepeat 0 MAX_CHARS_PER_FRAME) 0 0 0 1 0 MAX_CHARS_PER_FRAME).

Lemma bits_init_w1 : forall (A usp lo : Z) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem),
stk bsegs m lo usp -> lo <= usp - 32 -> SH_HI <= lo -> usp < 2^63 -> client_constsB m -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (j0 : list byte),
ms = MS (mkR (Z_to_bv 64 RA_bits_init_calloc) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 SHB)
(Z_to_bv 64 2000) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_wrap_calloc) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -32, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -32)
/\ rw_cells bsegs m1 (usp + -32) [CB 8 j0; C8 s1; C8 s0; C8 ra])
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_bits_init) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST LO LOS SPH CC MI. destruct CC as (G1 & G2 & _).
unfold A_speex_bits_init, RA_bits_init_calloc, e_wrap_calloc, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
carve_frame 32%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0x67f88.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.

Lemma bits_init_w2 : forall (A D usp lo : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(c0 c1 cra : word) (j0 junk : list byte) F fc (m : mem),
stk bsegs m lo (usp + -32) -> lo <= usp + -32 -> SH_HI <= lo -> usp < 2^63 ->
rw_cells bsegs m (usp + -32) [CB 8 j0; C8 c1; C8 c0; C8 cra] ->
rw_cells bsegs m A [CB 48 junk] -> aobj bsegs m A BITS_SIZEOF -> A mod 8 = 0 -> 0 < A -> A + BITS_SIZEOF <= lo -> (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A) ->
rw_cells bsegs m D [CB 2000 (repeat z8 2000)] -> aobj bsegs m D 2000 -> D mod 16 = 0 -> 0 < D -> D + 2000 <= lo -> (D + 2000 <= SH_LO \/ SH_HI <= D) ->
(D + 2000 <= A \/ A + BITS_SIZEOF <= D) ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (a0' a1' a2' : word),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 a0' a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom bsegs)
/\ munch [(A, A + 48); (D, D + 2000); (usp + -32, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp
/\ bits_rep bsegs m1 A D bits_fresh /\ bits_ok bits_fresh)
(MS (mkR (Z_to_bv 64 RA_bits_init_calloc) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 SHB)
(Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_bits_init_calloc)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST LO LOS SPH FR OBJ OBA A8 A0 ALO ASH BLK OBD D16 D0 DLO DSH SEP MI.
unfold RA_bits_init_calloc, BITS_SIZEOF in *.
pose proof LOS as LOS'. pose proof ASH as ASH'. pose proof DSH as DSH'. unfold SH_LO, SH_HI in LOS', ASH', DSH'.
pose proof ST as (STa & STb & _).
assert (D8 : D mod 8 = 0) by (clear - D16; Z.div_mod_to_equations; lia).
pose proof (munch_refl [(A, A + 48); (D, D + 2000); (usp + -32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(A, A + 48); (D, D + 2000); (usp + -32, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
replace (ret_pc (Z_to_bv 64 0x977a0)) with (Z_to_bv 64 0x977a0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
apply (rw_cells_split_CB bsegs _ _ [] 48 _ [] [8; 4; 4; 4; 4; 4; 4; 16]%nat) in OBJ; [| reflexivity]. cbn [mk_CB_cells app] in OBJ.
apply (rw_cells_split_CB bsegs _ _ [] 2000 _ [] [1; 1999]%nat) in BLK; [| reflexivity]. cbn [mk_CB_cells app] in BLK.
ato 0x977a0. astep. sh_if.
ato 0x977a8. astep. sh_if.
ato 0x977c0. astep. sh_if.
ato 0x97870.
ato 0x9787c. release_frame FR ST usp. astep. astep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => set (mF := mx) in * end.
apply evt_done. do 4 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
split.
- unfold bits_rep, bits_fresh, speex_bits_reset; cbn. split; [|split].
+ lazymatch type of OBJ with rw_cells _ _ _ [_; _; _; _; _; _; _; CB 16 ?jj] => exists jj end.
pose proof (proj1 (proj1 OBJ)) as WF2. cbn [cells_wf cell_wf] in WF2.
split; [tauto|]. unfold bits_cells; cbn.
eapply rw_cells_samebytes; [exact OBJ| cbn [cells_wf cell_wf]; tauto| | reflexivity]. reflexivity.
+ exists (repeat z8 2000). split.
* apply (u8arr_of_rw_cells bsegs mF D 2000).
eapply rw_cells_samebytes; [exact BLK| split; [apply repeat_length| exact I]| vm_compute; reflexivity| reflexivity].
* vm_compute. reflexivity.
+ unfold bits_side, BITS_BUF_MAX, BITS_SIZEOF, MAX_CHARS_PER_FRAME. cbn. lia.
- unfold bits_ok, bits_fresh, speex_bits_reset, bits_pos; cbn [sb_data sb_nbBits sb_charPtr sb_bitPtr sb_owner sb_overflow sb_buf_size].
rewrite zlength_zupd, zlength_zrepeat by (unfold MAX_CHARS_PER_FRAME; lia). unfold MAX_CHARS_PER_FRAME. lia.
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition A_speex_bits_init : Z := 0x974c0.
Definition e_wrap_calloc : Z := 0x67e9c.
Definition RA_bits_init_calloc : Z := 0x974ec.

Definition bits_fresh : bits_st unit := speex_bits_reset (mkBits tt (zrepeat 0 MAX_CHARS_PER_FRAME) 0 0 0 1 0 MAX_CHARS_PER_FRAME).

Lemma bits_init_w1 : forall (A usp lo : Z) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem),
stk asegs m lo usp -> lo <= usp - 32 -> SH_HI <= lo -> usp < 2^63 -> client_consts m -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (j0 : list byte),
ms = MS (mkR (Z_to_bv 64 RA_bits_init_calloc) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 SHB)
(Z_to_bv 64 2000) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_wrap_calloc) fc None m1 (seg_rom asegs)
/\ munch [(usp + -32, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -32)
/\ rw_cells asegs m1 (usp + -32) [CB 8 j0; C8 s1; C8 s0; C8 ra])
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_bits_init) fc None m (seg_rom asegs)).
Proof.
intros until m. intros ST LO LOS SPH CC MI. destruct CC as (G1 & G2 & _).
unfold A_speex_bits_init, RA_bits_init_calloc, e_wrap_calloc, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -32, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 32%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0x67e9c.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.

Lemma bits_init_w2 : forall (A D usp lo : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(c0 c1 cra : word) (j0 junk : list byte) F fc (m : mem),
stk asegs m lo (usp + -32) -> lo <= usp + -32 -> SH_HI <= lo -> usp < 2^63 ->
rw_cells asegs m (usp + -32) [CB 8 j0; C8 c1; C8 c0; C8 cra] ->
rw_cells asegs m A [CB 48 junk] -> aobj asegs m A BITS_SIZEOF -> A mod 8 = 0 -> 0 < A -> A + BITS_SIZEOF <= lo -> (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A) ->
rw_cells asegs m D [CB 2000 (repeat z8 2000)] -> aobj asegs m D 2000 -> D mod 16 = 0 -> 0 < D -> D + 2000 <= lo -> (D + 2000 <= SH_LO \/ SH_HI <= D) ->
(D + 2000 <= A \/ A + BITS_SIZEOF <= D) ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (a0' a1' a2' : word),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 a0' a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom asegs)
/\ munch [(A, A + 48); (D, D + 2000); (usp + -32, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp
/\ bits_rep asegs m1 A D bits_fresh /\ bits_ok bits_fresh)
(MS (mkR (Z_to_bv 64 RA_bits_init_calloc) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 SHB)
(Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_bits_init_calloc)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros ST LO LOS SPH FR OBJ OBA A8 A0 ALO ASH BLK OBD D16 D0 DLO DSH SEP MI.
unfold RA_bits_init_calloc, BITS_SIZEOF in *.
pose proof LOS as LOS'. pose proof ASH as ASH'. pose proof DSH as DSH'. unfold SH_LO, SH_HI in LOS', ASH', DSH'.
pose proof ST as (STa & STb & _).
assert (D8 : D mod 8 = 0) by (clear - D16; Z.div_mod_to_equations; lia).
pose proof (munch_refl [(A, A + 48); (D, D + 2000); (usp + -32, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(A, A + 48); (D, D + 2000); (usp + -32, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
replace (ret_pc (Z_to_bv 64 0x974ec)) with (Z_to_bv 64 0x974ec) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
apply (rw_cells_split_CB asegs _ _ [] 48 _ [] [8; 4; 4; 4; 4; 4; 4; 16]%nat) in OBJ; [| reflexivity]. cbn [mk_CB_cells app] in OBJ.
apply (rw_cells_split_CB asegs _ _ [] 2000 _ [] [1; 1999]%nat) in BLK; [| reflexivity]. cbn [mk_CB_cells app] in BLK.
ato 0x97500. astep. sh_if.
ato 0x975b0.
ato 0x975bc. release_frame FR ST usp. astep. astep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => set (mF := mx) in * end.
apply evt_done. do 4 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
split.
- unfold bits_rep, bits_fresh, speex_bits_reset; cbn. split; [|split].
+ lazymatch type of OBJ with rw_cells _ _ _ [_; _; _; _; _; _; _; CB 16 ?jj] => exists jj end.
pose proof (proj1 (proj1 OBJ)) as WF2. cbn [cells_wf cell_wf] in WF2.
split; [tauto|]. unfold bits_cells; cbn.
eapply rw_cells_samebytes; [exact OBJ| cbn [cells_wf cell_wf]; tauto| | reflexivity]. reflexivity.
+ exists (repeat z8 2000). split.
* apply (u8arr_of_rw_cells asegs mF D 2000).
eapply rw_cells_samebytes; [exact BLK| split; [apply repeat_length| exact I]| vm_compute; reflexivity| reflexivity].
* vm_compute. reflexivity.
+ unfold bits_side, BITS_BUF_MAX, BITS_SIZEOF, MAX_CHARS_PER_FRAME. cbn. lia.
- unfold bits_ok, bits_fresh, speex_bits_reset, bits_pos; cbn [sb_data sb_nbBits sb_charPtr sb_bitPtr sb_owner sb_overflow sb_buf_size].
rewrite zlength_zupd, zlength_zrepeat by (unfold MAX_CHARS_PER_FRAME; lia). unfold MAX_CHARS_PER_FRAME. lia.
Qed.
