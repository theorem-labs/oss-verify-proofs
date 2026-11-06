(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg.
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

Definition A_speex_bits_remaining : Z := 0x98808.

Section F.
Context {ptr : Type}.

Definition speex_bits_remaining_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(A D usp lo : Z) (b : bits_st ptr) (m : mem) : machine_state -> Prop :=
fun ms' => exists a0 a1 a2 a3 a4 a5 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(usp + -16, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp
/\ a0 = Z_to_bv 64 (speex_bits_remaining b)
/\ bits_rep bsegs m' A D b.

Variables (A D usp lo : Z) (b : bits_st ptr).
Variables ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m : mem.

Lemma speex_bits_remaining_walk :
bits_rep bsegs m A D b -> bits_ok b ->
aobj bsegs m A BITS_SIZEOF ->
stk bsegs m lo usp -> lo <= usp - 16 -> SH_HI <= lo -> usp < 2^63 -> A + BITS_SIZEOF <= lo -> D + sb_buf_size b <= lo ->
client_constsB m -> mem_inv bsegs m ->
evt bsegs (speex_bits_remaining_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a6 a7 t0 t1 t2 t3 t4 t5 t6 F fc A D usp lo b m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_bits_remaining) fc None m (seg_rom bsegs)).
Proof.
intros REP OK OBA ST LO LOS SPH ALO DLO (G1 & G2 & _) MI.
unfold A_speex_bits_remaining, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address in *.
pose proof REP as ((rj & Lrj & OBJ) & (bs & ARR & Hbs) & SIDE).
pose proof (bits_ints A D b OK SIDE) as (In & Ic & Ib & Io & Iv & Is & Rc & Rb & Rp & Rn & Rs & R1 & Rov).
pose proof SIDE as (AL & Apos & Dpos & _ & _ & SEP).
unfold bits_pos in Rp. unfold int31, BITS_BUF_MAX, BITS_SIZEOF in *.
unfold bits_cells in OBJ.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (u8arr_bound _ _ _ _ ARR) as DB.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b) by (pose proof OK as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; lia).
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -16, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -16, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 16%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0x98810. astep. sh_if.
ato 0x98818. astep. sh_if.
ato 0x98840. rewrite sx32_small by (unfold int31; lia).
astep. if_cases K; zify_cond K.
-
ato 0x98874. rewrite sx32_small by (unfold int31; lia).
ato 0x9887c. rewrite zx32_small by lia.
assert (CP28 : Z.shiftr (sb_charPtr b) 28 = 0) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
ato 0x98880. astep. sh_if.
ato 0x9889c. rewrite sx32_small by (unfold int31; lia).
ato 0x988a8.
rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
rewrite !(swrap32_small (sb_charPtr b * 8)) by lia.
rewrite !Z.mod_small by lia. rewrite swrap32_small by lia.
astep. sh_if.
ato 0x988b8.
rewrite Z.add_0_r. rewrite !(swrap32_small (sb_charPtr b * 8 + sb_bitPtr b)) by lia.
rewrite !Z.mod_small by lia. rewrite swrap32_small by lia.
astep. sh_if.
ato 0x988c4. release_frame FR ST usp. astep. astep.
unfold speex_bits_remaining_post. finish.
+ unfold speex_bits_remaining, bits_pos. rewrite K. cbn [Z.eqb negb].
rewrite Z.add_0_r, swrap32_small by lia. reflexivity.
+ exact (conj (ex_intro _ rj (conj Lrj OBJ)) (conj (ex_intro _ bs (conj ARR Hbs)) SIDE)).
-
ato 0x988c4. release_frame FR ST usp. astep. astep.
unfold speex_bits_remaining_post. finish.
+ unfold speex_bits_remaining. destruct (Z.eqb_spec (sb_overflow b) 0); [lia| reflexivity].
+ exact (conj (ex_intro _ rj (conj Lrj OBJ)) (conj (ex_intro _ bs (conj ARR Hbs)) SIDE)).
Qed.
End F.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition A_speex_bits_remaining : Z := 0x982c0.

Section F.
Context {ptr : Type}.

Definition speex_bits_remaining_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(A D usp lo : Z) (b : bits_st ptr) (m : mem) : machine_state -> Prop :=
fun ms' => exists a0 a1 a2 a3 a4 a5 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(usp + -16, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
/\ a0 = Z_to_bv 64 (speex_bits_remaining b)
/\ bits_rep asegs m' A D b.

Variables (A D usp lo : Z) (b : bits_st ptr).
Variables ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m : mem.

Lemma speex_bits_remaining_walk :
bits_rep asegs m A D b -> bits_ok b ->
aobj asegs m A BITS_SIZEOF ->
stk asegs m lo usp -> lo <= usp - 16 -> SH_HI <= lo -> usp < 2^63 -> A + BITS_SIZEOF <= lo -> D + sb_buf_size b <= lo ->
client_consts m -> mem_inv asegs m ->
evt asegs (speex_bits_remaining_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a6 a7 t0 t1 t2 t3 t4 t5 t6 F fc A D usp lo b m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_bits_remaining) fc None m (seg_rom asegs)).
Proof.
intros REP OK OBA ST LO LOS SPH ALO DLO (G1 & G2 & _) MI.
unfold A_speex_bits_remaining, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof REP as ((rj & Lrj & OBJ) & (bs & ARR & Hbs) & SIDE).
pose proof (bits_ints A D b OK SIDE) as (In & Ic & Ib & Io & Iv & Is & Rc & Rb & Rp & Rn & Rs & R1 & Rov).
pose proof SIDE as (AL & Apos & Dpos & _ & _ & SEP).
unfold bits_pos in Rp. unfold int31, BITS_BUF_MAX, BITS_SIZEOF in *.
unfold bits_cells in OBJ.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (u8arr_bound _ _ _ _ ARR) as DB.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b) by (pose proof OK as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; lia).
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -16, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -16, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 16%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0x982ec. rewrite sx32_small by (unfold int31; lia).
astep. if_cases K; zify_cond K.
-
ato 0x98320. rewrite sx32_small by (unfold int31; lia).
ato 0x98338. rewrite sx32_small by (unfold int31; lia).
ato 0x98340. rewrite sx32_small by (unfold int31; lia).
ato 0x98350. release_frame FR ST usp. astep. astep.
unfold speex_bits_remaining_post. finish.
+ unfold speex_bits_remaining, bits_pos. rewrite K. cbn [Z.eqb negb].
rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
rewrite !Z.mod_small by lia. rewrite swrap32_small by lia. f_equal. lia.
+ exact (conj (ex_intro _ rj (conj Lrj OBJ)) (conj (ex_intro _ bs (conj ARR Hbs)) SIDE)).
-
ato 0x98350. release_frame FR ST usp. astep. astep.
unfold speex_bits_remaining_post. finish.
+ unfold speex_bits_remaining. destruct (Z.eqb_spec (sb_overflow b) 0); [lia| reflexivity].
+ exact (conj (ex_intro _ rj (conj Lrj OBJ)) (conj (ex_intro _ bs (conj ARR Hbs)) SIDE)).
Qed.
End F.
