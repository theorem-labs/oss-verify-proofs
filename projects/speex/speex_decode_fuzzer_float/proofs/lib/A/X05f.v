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

Definition A_speex_bits_peek : Z := 0x984b8.

Section F.
Context {ptr : Type}.

Definition speex_bits_peek_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(a7 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(A D usp lo : Z) (b : bits_st ptr) (m : mem) : machine_state -> Prop :=
fun ms' => exists a0 a1 a2 a3 a4 a5 a6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(A, A + BITS_SIZEOF); (usp + -16, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp
/\ a0 = Z_to_bv 64 (fst (speex_bits_peek b))
/\ bits_rep bsegs m' A D (snd (speex_bits_peek b)).

Variables (A D usp lo : Z) (b : bits_st ptr).
Variables ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m : mem.

Lemma speex_bits_peek_walk :
bits_rep bsegs m A D b -> bits_ok b ->
aobj bsegs m A BITS_SIZEOF -> aobj bsegs m D (sb_buf_size b) -> (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A) ->
stk bsegs m lo usp -> lo <= usp - 16 -> SH_HI <= lo -> usp < 2^63 -> A + BITS_SIZEOF <= lo -> D + sb_buf_size b <= lo ->
client_constsB m -> mem_inv bsegs m ->
evt bsegs (speex_bits_peek_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a7 t0 t1 t2 t3 t4 t5 t6 F fc A D usp lo b m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_bits_peek) fc None m (seg_rom bsegs)).

Proof.
intros REP OK OBA OBD OFA ST LO LOS SPH ALO DLO (G1 & G2 & _) MI.
unfold A_speex_bits_peek, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address in *.
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
pose proof (munch_refl [(A, A + 48); (usp + -16, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(A, A + 48); (usp + -16, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 16%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.

assert (FIN : forall m1 (b1 : bits_st ptr) (v : Z) x1 x2 x3 x4 x5 x6 (j0 : list byte),
(v, b1) = speex_bits_peek b ->
rw_cells bsegs m1 A (bits_cells D b1 rj) -> u8arr bsegs m1 D bs -> munch [(A, A + 48); (usp + -16, usp)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
stk bsegs m1 lo (usp + -16) -> rw_cells bsegs m1 (usp + -16) [CB 8 j0; C8 ra] ->
evt bsegs (speex_bits_peek_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a7 t0 t1 t2 t3 t4 t5 t6 F fc A D usp lo b m)
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) x1 x2 x3 x4 x5 x6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x985ec) fc None m1 (seg_rom bsegs))).
{ intros m1 b1 v x1 x2 x3 x4 x5 x6 j0 E OBJ1 ARR1 MU1 WM1 MI1 ST1 FR1.
astep. release_frame FR1 ST1 usp. astep. astep.
unfold speex_bits_peek_post. finish.
- rewrite <- E. reflexivity.
- rewrite <- E. cbn [snd].
split; [exists rj; split; [exact Lrj| exact OBJ1]|].
assert (Hb1 : b1 = b \/ b1 = set_overflow b).
{ unfold speex_bits_peek in E. destruct (_ || _); injection E as _ <-; auto. }
split.
+ exists bs. split; [exact ARR1|]. destruct Hb1 as [-> | ->]; [exact Hbs| unfold set_overflow; cbn; exact Hbs].
+ unfold bits_side in *. destruct Hb1 as [-> | ->]; [tauto| unfold set_overflow; cbn; tauto]. }
ato 0x984c0. astep. sh_if.
ato 0x984c8. astep. sh_if.
ato 0x984f0. rewrite sx32_small by (unfold int31; lia).
assert (CP28 : Z.shiftr (sb_charPtr b) 28 = 0) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
ato 0x984f4. rewrite wrap32_small by lia. rewrite CP28. change (bv_swrap 32 0) with 0.
ato 0x98510. rewrite sx32_small by (unfold int31; lia).
ato 0x9851c. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
rewrite !(swrap32_small (sb_charPtr b * 8)) by lia. rewrite !Z.mod_small by lia. rewrite swrap32_small by lia.
astep. sh_if.
ato 0x98528. rewrite Z.add_0_r. rewrite !swrap32_small by lia.
astep. sh_if.
ato 0x98544. rewrite sx32_small by (unfold int31; lia).
ato 0x98548. astep.
if_cases K1; zify_cond K1; rewrite ?signed_lit_small in K1 by lia.
-
ato 0x98578. rewrite sx32_small by (unfold int31; lia).
astep. if_cases K2; zify_cond K2.
+
ato 0x9859c. astep. sh_if.
ato 0x985ac. replace (0 <? D) with true by (symmetry; apply Z.ltb_lt; lia).
replace (D + sb_charPtr b <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.lxor].
ato 0x985b0. astep. sh_if.
ato 0x985c0.
assert (Hnth : nth_error bs (Z.to_nat (sb_charPtr b)) = Some (nth (Z.to_nat (sb_charPtr b)) bs (Z_to_bv 8 0))) by (apply nth_error_nth'; lia).
pose proof (u8arr_read _ _ _ _ (sb_charPtr b) _ _ ARR Hnth ltac:(lia) eq_refl) as RD.
pose proof (byte_range (nth (Z.to_nat (sb_charPtr b)) bs (Z_to_bv 8 0))) as BR.
pose proof (shiftr_byte_range _ (7 - sb_bitPtr b) BR ltac:(lia)) as SR.
astep. chk_merge OBD 1.
ato 0x985d0. rewrite (swrap32_small (7 - sb_bitPtr b)) by lia. astep. sh_if.
ato 0x985dc. rewrite Z.add_0_r, (swrap32_small (7 - sb_bitPtr b)) by lia. astep. sh_if.
ato 0x985ec.
rewrite wrap32_small by lia. rewrite (Z.mod_small (7 - sb_bitPtr b) 32) by lia. rewrite swrap32_small by lia. rewrite !Z.mod_small by lia.
eapply (FIN _ b); [| unfold bits_cells; exact OBJ| exact ARR | exact MU| exact WM| exact MI | exact ST | exact FR].
unfold speex_bits_peek, bits_pos. destruct (Z.ltb_spec (sb_nbBits b) (sb_charPtr b * 8 + sb_bitPtr b + 1)); [lia|].
rewrite K2. cbn [orb negb Z.eqb]. f_equal. apply (bit_at_code bs); [exact Hbs| lia| lia| lia].
+
ato 0x985ec.
eapply (FIN _ (set_overflow b) 0); [| unfold bits_cells, set_overflow; cbn; replace (sb_overflow b) with 1 in OBJ by lia; exact OBJ| exact ARR | exact MU| exact WM| exact MI | exact ST | exact FR].
unfold speex_bits_peek, bits_pos. destruct (Z.ltb_spec (sb_nbBits b) (sb_charPtr b * 8 + sb_bitPtr b + 1)); [lia|].
destruct (Z.eqb_spec (sb_overflow b) 0); [lia|]. cbn [orb negb]. reflexivity.
-
ato 0x98578. rewrite sx32_small by (unfold int31; lia).
ato 0x985ec.
eapply (FIN _ (set_overflow b) 0); [| unfold bits_cells, set_overflow; cbn; exact OBJ| exact ARR | exact MU| exact WM| exact MI | exact ST | exact FR].
unfold speex_bits_peek, bits_pos. destruct (Z.ltb_spec (sb_nbBits b) (sb_charPtr b * 8 + sb_bitPtr b + 1)); [|lia].
cbn [orb]. reflexivity.
Qed.
End F.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition A_speex_bits_peek : Z := 0x98004.

Section F.
Context {ptr : Type}.

Definition speex_bits_peek_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(a7 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(A D usp lo : Z) (b : bits_st ptr) (m : mem) : machine_state -> Prop :=
fun ms' => exists a0 a1 a2 a3 a4 a5 a6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(A, A + BITS_SIZEOF); (usp + -16, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
/\ a0 = Z_to_bv 64 (fst (speex_bits_peek b))
/\ bits_rep asegs m' A D (snd (speex_bits_peek b)).

Variables (A D usp lo : Z) (b : bits_st ptr).
Variables ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m : mem.

Lemma speex_bits_peek_walk :
bits_rep asegs m A D b -> bits_ok b ->
aobj asegs m A BITS_SIZEOF -> aobj asegs m D (sb_buf_size b) -> (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A) ->
stk asegs m lo usp -> lo <= usp - 16 -> SH_HI <= lo -> usp < 2^63 -> A + BITS_SIZEOF <= lo -> D + sb_buf_size b <= lo ->
client_consts m -> mem_inv asegs m ->
evt asegs (speex_bits_peek_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a7 t0 t1 t2 t3 t4 t5 t6 F fc A D usp lo b m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_bits_peek) fc None m (seg_rom asegs)).
Proof.
intros REP OK OBA OBD OFA ST LO LOS SPH ALO DLO (G1 & G2 & _) MI.
unfold A_speex_bits_peek, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
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

assert (FIN : forall m1 (b1 : bits_st ptr) (v : Z) x1 x2 x3 x4 x5 x6 (j0 : list byte),
(v, b1) = speex_bits_peek b ->
rw_cells asegs m1 A (bits_cells D b1 rj) -> u8arr asegs m1 D bs -> munch [(A, A + 48); (usp + -16, usp)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
stk asegs m1 lo (usp + -16) -> rw_cells asegs m1 (usp + -16) [CB 8 j0; C8 ra] ->
evt asegs (speex_bits_peek_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a7 t0 t1 t2 t3 t4 t5 t6 F fc A D usp lo b m)
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) x1 x2 x3 x4 x5 x6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x980e4) fc None m1 (seg_rom asegs))).
{ intros m1 b1 v x1 x2 x3 x4 x5 x6 j0 E OBJ1 ARR1 MU1 WM1 MI1 ST1 FR1.
astep. release_frame FR1 ST1 usp. astep. astep.
unfold speex_bits_peek_post. finish.
- rewrite <- E. reflexivity.
- rewrite <- E. cbn [snd].
split; [exists rj; split; [exact Lrj| exact OBJ1]|].
assert (Hb1 : b1 = b \/ b1 = set_overflow b).
{ unfold speex_bits_peek in E. destruct (_ || _); injection E as _ <-; auto. }
split.
+ exists bs. split; [exact ARR1|]. destruct Hb1 as [-> | ->]; [exact Hbs| unfold set_overflow; cbn; exact Hbs].
+ unfold bits_side in *. destruct Hb1 as [-> | ->]; [tauto| unfold set_overflow; cbn; tauto]. }
ato 0x98040. rewrite sx32_small by (unfold int31; lia).
ato 0x98058. rewrite sx32_small by (unfold int31; lia).
ato 0x98060. rewrite sx32_small by (unfold int31; lia).
astep. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
astep. nswrap. astep. astep.
if_cases K1; zify_cond K1; rewrite ?signed_lit_small in K1 by lia.
-
ato 0x9809c. rewrite sx32_small by (unfold int31; lia).
astep. if_cases K2; zify_cond K2.
+
ato 0x980cc.
assert (Hnth : nth_error bs (Z.to_nat (sb_charPtr b)) = Some (nth (Z.to_nat (sb_charPtr b)) bs (Z_to_bv 8 0))) by (apply nth_error_nth'; lia).
pose proof (u8arr_read _ _ _ _ (sb_charPtr b) _ _ ARR Hnth ltac:(lia) eq_refl) as RD.
pose proof (byte_range (nth (Z.to_nat (sb_charPtr b)) bs (Z_to_bv 8 0))) as BR.
pose proof (shiftr_byte_range _ (7 - sb_bitPtr b) BR ltac:(lia)) as SR.
astep. chk_merge OBD 1.
astep. astep. astep. nswrap.
astep. rewrite wrap32_small by lia. repeat (rewrite Z.mod_small by lia). nswrap. repeat (rewrite Z.mod_small by lia).
astep.
eapply (FIN _ b); [| unfold bits_cells; exact OBJ| exact ARR | exact MU| exact WM| exact MI | exact ST | exact FR].
unfold speex_bits_peek, bits_pos. destruct (Z.ltb_spec (sb_nbBits b) (sb_charPtr b * 8 + sb_bitPtr b + 1)); [lia|].
rewrite K2. cbn [orb negb Z.eqb]. f_equal. apply (bit_at_code bs); [exact Hbs| lia| lia| lia].
+
ato 0x980e4.
eapply (FIN _ (set_overflow b) 0); [| unfold bits_cells, set_overflow; cbn; replace (sb_overflow b) with 1 in OBJ by lia; exact OBJ| exact ARR | exact MU| exact WM| exact MI | exact ST | exact FR].
unfold speex_bits_peek, bits_pos. destruct (Z.ltb_spec (sb_nbBits b) (sb_charPtr b * 8 + sb_bitPtr b + 1)); [lia|].
destruct (Z.eqb_spec (sb_overflow b) 0); [lia|]. cbn [orb negb]. reflexivity.
-
ato 0x9809c. astep. sh_if.
ato 0x980e4.
eapply (FIN _ (set_overflow b) 0); [| unfold bits_cells, set_overflow; cbn; exact OBJ| exact ARR | exact MU| exact WM| exact MI | exact ST | exact FR].
unfold speex_bits_peek, bits_pos. destruct (Z.ltb_spec (sb_nbBits b) (sb_charPtr b * 8 + sb_bitPtr b + 1)); [|lia].
cbn [orb]. reflexivity.
Qed.
End F.
