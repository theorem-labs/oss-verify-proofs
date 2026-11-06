(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05l.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition A_speex_bits_advance : Z := 0x98164.

Section F.
Context {ptr : Type}.

Definition speex_bits_advance_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(A D usp lo : Z) (b : bits_st ptr) (n : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(A, A + BITS_SIZEOF); (usp + -16, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
/\ bits_rep asegs m' A D (speex_bits_advance b n).

Variables (A D usp lo : Z) (b : bits_st ptr) (n : Z).
Variables ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m : mem.

Lemma speex_bits_advance_walk :
bits_rep asegs m A D b -> bits_ok b -> - 2^20 <= n <= 2^20 ->
aobj asegs m A BITS_SIZEOF -> (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A) ->
stk asegs m lo usp -> lo <= usp - 16 -> SH_HI <= lo -> usp < 2^63 -> A + BITS_SIZEOF <= lo -> D + sb_buf_size b <= lo ->
client_consts m -> mem_inv asegs m ->
evt asegs (speex_bits_advance_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc A D usp lo b n m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_bits_advance) fc None m (seg_rom asegs)).
Proof.
intros REP OK Hn OBA OFA ST LO LOS SPH ALO DLO (G1 & G2 & _) MI.
unfold A_speex_bits_advance, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof REP as ((rj & Lrj & OBJ) & (bs & ARR & Hbs) & SIDE).
pose proof (bits_ints A D b OK SIDE) as (In & Ic & Ib & Io & Iv & Is & Rc & Rb & Rp & Rn & Rs & R1 & Rov).
pose proof SIDE as (AL & Apos & Dpos & _ & _ & SEP).
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. lia. }
unfold bits_pos in Rp. unfold int31, BITS_BUF_MAX, BITS_SIZEOF in *.
unfold bits_cells in OBJ.
pose proof LOS as LOS'. pose proof OFA as OFA'. unfold SH_LO, SH_HI in LOS', OFA'.
pose proof (u8arr_bound _ _ _ _ ARR) as DB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(A, A + 48); (usp + -16, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(A, A + 48); (usp + -16, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 16%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.

assert (FIN : forall m1 (b1 : bits_st ptr) x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 (j0 : list byte),
b1 = speex_bits_advance b n ->
rw_cells asegs m1 A (bits_cells D b1 rj) -> u8arr asegs m1 D bs -> munch [(A, A + 48); (usp + -16, usp)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
stk asegs m1 lo (usp + -16) -> rw_cells asegs m1 (usp + -16) [CB 8 j0; C8 ra] ->
evt asegs (speex_bits_advance_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc A D usp lo b n m)
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp y0 y1 y2 s0 s1 x0 x1 x2 x3 x4 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x98208) fc None m1 (seg_rom asegs))).
{ intros m1 b1 x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 j0 -> OBJ1 ARR1 MU1 WM1 MI1 ST1 FR1.
astep. release_frame FR1 ST1 usp. astep. astep.
unfold speex_bits_advance_post. finish.
split; [exists rj; split; [exact Lrj| exact OBJ1]|].
split.
- exists bs. split; [exact ARR1|]. unfold speex_bits_advance, set_overflow, set_pos. destruct (_ || _); cbn; exact Hbs.
- unfold bits_side in *. unfold speex_bits_advance, set_overflow, set_pos. destruct (_ || _); cbn; tauto. }
ato 0x981a4. rewrite sx32_small by (unfold int31; lia).
ato 0x981bc. rewrite sx32_small by (unfold int31; lia).
ato 0x981c4. rewrite sx32_small by (unfold int31; lia).
astep. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
astep. rewrite ?swrap32_plus_mod64, ?swrap32_mod64_plus. rewrite (swrap32_small (sb_bitPtr b + n)) by lia.
astep. rewrite ?swrap32_plus_mod64, ?swrap32_mod64_plus. rewrite (swrap32_small (_ + _)) by lia.
astep. astep.
if_cases K1; zify_cond K1; rewrite ?signed_lit_small in K1 by lia.
-
ato 0x98208.
eapply (FIN _ (set_overflow b)); [| unfold bits_cells, set_overflow; cbn; exact OBJ| exact ARR | exact MU| exact WM| exact MI | exact ST | exact FR].
unfold speex_bits_advance, bits_pos. destruct (Z.ltb_spec (sb_nbBits b) (sb_charPtr b * 8 + sb_bitPtr b + n)); [|lia].
cbn [orb]. reflexivity.
- ato 0x981ec. rewrite sx32_small by (unfold int31; lia).
astep. if_cases K2; zify_cond K2.
+
ato 0x98208.
eapply (FIN _ (set_pos b (bits_pos b + n))); [| | exact ARR | exact MU| exact WM| exact MI | exact ST | exact FR].
* unfold speex_bits_advance. destruct (Z.ltb_spec (sb_nbBits b) (bits_pos b + n)); [unfold bits_pos in *; lia|].
rewrite K2. cbn [orb negb Z.eqb]. reflexivity.
* unfold set_pos, bits_cells; cbn.
eapply rw_cells_samebytes; [exact OBJ| cbn; tauto| | reflexivity].
cbn [cells_bytes cbytes app]. f_equal. f_equal. f_equal.
-- apply le4_lit_eqm. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
rewrite adv_char_eqm by lia. f_equal. unfold bits_pos.
pose proof (advance_C_arith (sb_charPtr b) (sb_bitPtr b) n) as [E _]. symmetry. exact E.
-- f_equal. apply le4_lit_eqm. rewrite ?land7_mod64, ?land7_mod8. f_equal. unfold bits_pos.
pose proof (advance_C_arith (sb_charPtr b) (sb_bitPtr b) n) as [_ E]. symmetry. exact E.
+
ato 0x98208.
eapply (FIN _ (set_overflow b)); [| unfold bits_cells, set_overflow; cbn; exact OBJ| exact ARR | exact MU| exact WM| exact MI | exact ST | exact FR].
unfold speex_bits_advance, bits_pos. destruct (Z.ltb_spec (sb_nbBits b) (sb_charPtr b * 8 + sb_bitPtr b + n)); [lia|].
destruct (Z.eqb_spec (sb_overflow b) 0); [lia|]. cbn [orb negb]. reflexivity.
Qed.
End F.
