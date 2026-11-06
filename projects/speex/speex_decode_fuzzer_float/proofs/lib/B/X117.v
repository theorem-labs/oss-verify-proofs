(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1df X1ck X1cg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05l X09e.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0z5 X0wh.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation mem := (word -> option byte).
Local Ltac slia ::= (try unfold BITS_SIZEOF in * ); first [ exact I | lia | split; [lia|exact I] ].

Definition A_pitch_unquant_3tap : Z := 0xac9c4.

Definition p3_frameB (j0 : list byte) (cpv : word) (j16 : list byte) (g0 g1 g2 cfs0 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) : list cell :=
[CB 8 j0; C8 cpv; CB 4 j16; C4 g0; C4 g1; C4 g2; C8 cfs0; C8 c11; C8 c10; C8 c9; C8 c8; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra].

Section W1.
Context {ptr : Type}.
Variables (A D EB e0 e32 pv pg usp lo start fin PAR G GN gbits pbits off : Z) (b : bits_st ptr).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable m : mem.
Local Notation exc := (EB + 4 * e0).
Hypothesis REP : bits_rep bsegs m A D b.
Hypothesis OK : bits_ok b.
Hypothesis OBA : aobj bsegs m A BITS_SIZEOF.
Hypothesis OBD : aobj bsegs m D (sb_buf_size b).
Hypothesis OBPAR : aobj bsegs m PAR 16.
Hypothesis PAR8 : PAR mod 8 = 0.
Hypothesis PARI : PAR + 16 <= IMG_TOP_B.
Hypothesis PARLO : 0x10000 <= PAR.
Hypothesis OBG : aobj bsegs m G GN.
Hypothesis GNE : GN = 4 * 2 ^ gbits.
Hypothesis GTI : G + GN <= IMG_TOP_B.
Hypothesis GLO : 0x10000 <= G.
Hypothesis ST17 : 17 <= start <= 144.
Hypothesis LO : lo <= usp - 144 - 48.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp + 40 < 2^63.
Hypothesis ASH : hidp (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A).
Hypothesis ATOP : IMG_TOP_B <= A.
Hypothesis ALO : A + BITS_SIZEOF <= lo.
Hypothesis DLO : D + sb_buf_size b <= lo.

Lemma p3_w1a : forall (stk8 : word) (gtab : list byte) (t0 t1 t2 t3 t4 t5 t6 : word) F fc,
u8ro bsegs m G gtab -> Z.of_nat (length gtab) = GN ->
ro_cells bsegs m PAR [C8 (Z_to_bv 64 G); C4 (Z_to_bv 64 gbits); C4 (Z_to_bv 64 pbits)] ->
rw_cells bsegs m usp [C8 (Z_to_bv 64 A); C8 stk8; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 off); C8 (Z_to_bv 64 0)] ->
0 <= gbits <= 7 -> 0 <= pbits <= 7 ->
frm0 fc -> stk bsegs m lo usp -> client_constsB m -> mem_inv bsegs m ->
evt bsegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a7' s3' s4' s5' s7' s10' s11' t3' t4' t5' t6' g0 g1 g2 : word) (j0 j16 : list byte) F' fc' m',
let b1 := snd (speex_bits_unpack_unsigned b pbits) in let v1 := fst (speex_bits_unpack_unsigned b pbits) in
let b2 := snd (speex_bits_unpack_unsigned b1 gbits) in
ms' = MS (mkR ra' (Z_to_bv 64 (usp + -144)) gp tp t0' t1' t2' (Z_to_bv 64 40) (Z_to_bv 64 e32) a0' a1' a2' a3' a4' a5' (Z_to_bv 64 pv) a7'
(Z_to_bv 64 exc) s3' s4' s5' (Z_to_bv 64 pg) s7' (Z_to_bv 64 SHB) (Z_to_bv 64 (v1 + start)) s10' s11' t3' t4' t5' t6')
F' (Z_to_bv 64 0xaccbc) fc' None m' (seg_rom bsegs)
/\ munch [(A, A + 48); (usp + -192, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp + -144) /\ frm0 fc'
/\ rw_cells bsegs m' (usp + -144) (p3_frameB j0 (Z_to_bv 64 pv) j16 g0 g1 g2 (reg_get F 8) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
/\ bits_rep bsegs m' A D b2 /\ bits_ok b2 /\ sb_buf_size b2 = sb_buf_size b /\ 0 <= v1 < 2 ^ pbits)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 exc) (Z_to_bv 64 e32) (Z_to_bv 64 start) (Z_to_bv 64 fin) (Z_to_bv 64 PAR)
(Z_to_bv 64 40) (Z_to_bv 64 pv) (Z_to_bv 64 pg) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_pitch_unquant_3tap) fc None m (seg_rom bsegs)).
Proof.
intros stk8 gtab t0 t1 t2 t3 t4 t5 t6 F fc GT LGT XPAR ARGS GB PB FRM ST CC MI.
assert (P2 : 1 <= 2 ^ gbits <= 2 ^ 7) by (split; [apply (Z.pow_le_mono_r 2 0 gbits); lia | apply Z.pow_le_mono_r; lia]). change (2^7) with 128 in P2.
pose proof OBG as (OG0 & OG1 & _). pose proof GTI as GTI'. unfold IMG_TOP_B in GTI'.
pose proof CC as (G1 & G2 & G3 & G4).
unfold A_pitch_unquant_3tap, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof REP as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE). unfold bits_cells in OBJ.
pose proof (bits_ints A D b OK SIDE) as (In_ & Ic & Ib & Io & Iv & Is & Rc & Rb & Rp & Rn & Rs & R1 & Rov).
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. lia. }
pose proof (u8arr_bound _ _ _ _ DAT) as DB.
pose proof OBA as (OA0 & OA1 & _). pose proof OBD as (OD0 & OD1 & _). pose proof OBPAR as (OP0 & OP1 & _). unfold APP_TOP, BITS_SIZEOF in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof PARI as PARI'. unfold IMG_TOP_B in PARI'. pose proof ATOP as ATOP'. unfold IMG_TOP_B in ATOP'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(A, A + 48); (usp + -192, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(A, A + 48); (usp + -192, usp)]) by (pose proof (ASH : _ \/ _) as Y1; cbn; unfold SH_LO, SH_HI, BITS_SIZEOF in *; lia).
carve_frame 144%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 144 _ [] [8; 8; 4; 4; 4; 4; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
bato 0xaca44. rewrite sx32_small by (unfold int31; lia).

bato 0xacad0.
rewrite sx32_small by (unfold int31; lia). rewrite Z.mul_0_r, Z.add_0_r.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (REP1 : bits_rep bsegs mc A D b)
by (split; [exists rj; split; [exact Lrj| exact OBJ]| split; [exists bs; split; [exact DAT| exact Hbs]| exact SIDE]]);
pose proof (aobj_munch bsegs _ m mc A 48 OBA MU (shfree_of_aobj bsegs _ m A 48 OF OBA)) as OBA1;
pose proof (aobj_munch bsegs _ m mc D _ OBD MU (shfree_of_aobj bsegs _ m D _ OF OBD)) as OBD1;
assert (CC1 : client_constsB mc) by (unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))))
end.
clear OBJ DAT.
astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -144) lo b pbits _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK ltac:(lia) OBA1 OBD1 ASH ltac:(lia) LOS ltac:(lia) ALO DLO).
all: try eassumption.
subst x. set (v1 := fst (speex_bits_unpack_unsigned b pbits)) in *. set (b1 := snd (speex_bits_unpack_unsigned b pbits)) in *.
assert (UE1 : speex_bits_unpack_unsigned b pbits = (v1, b1)) by (unfold v1, b1; destruct (speex_bits_unpack_unsigned b pbits); reflexivity).
pose proof (speex_bits_unpack_unsigned_ok b pbits v1 b1 OK ltac:(lia) UE1) as (OK1 & V1R & _ & _ & SZ1 & _).
assert (P3 : 2 ^ pbits <= 2 ^ 7) by (apply Z.pow_le_mono_r; lia). change (2^7) with 128 in P3.
clear REP1 OBA1 OBD1 CC1.
bato 0xacaf4.
rewrite sx32_small by (unfold int31; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch bsegs _ m mc A 48 OBA MU (shfree_of_aobj bsegs _ m A 48 OF OBA)) as OBA1;
pose proof (aobj_munch bsegs _ m mc D _ OBD MU (shfree_of_aobj bsegs _ m D _ OF OBD)) as OBD1;
assert (CC1 : client_constsB mc) by (unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))))
end.
rewrite <- SZ1 in OBD1.
astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -144) lo b1 gbits _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ POST OK1 ltac:(lia) OBA1 OBD1 ASH ltac:(lia) LOS ltac:(lia) ALO ltac:(rewrite SZ1; exact DLO)).
all: try eassumption.
subst x. set (v2 := fst (speex_bits_unpack_unsigned b1 gbits)) in *. set (b2 := snd (speex_bits_unpack_unsigned b1 gbits)) in *.
assert (UE2 : speex_bits_unpack_unsigned b1 gbits = (v2, b2)) by (unfold v2, b2; destruct (speex_bits_unpack_unsigned b1 gbits); reflexivity).
pose proof (speex_bits_unpack_unsigned_ok b1 gbits v2 b2 OK1 ltac:(lia) UE2) as (OK2 & V2R & _ & _ & SZ2 & _).
clear OBA1 OBD1 CC1.
match goal with H : bits_rep bsegs _ A D b2 |- _ => destruct H as ((rj2 & Lrj2 & OBJ2) & (bs2 & DAT2 & Hbs2) & SIDE2); unfold bits_cells in OBJ2 end.
assert (Lbs2 : Z.of_nat (length bs2) = sb_buf_size b).
{ pose proof OK2 as OK'. unfold bits_ok in OK'. rewrite Hbs2, zlength_map_unsigned in OK'. lia. }
pose proof (u8arr_bound _ _ _ _ DAT2) as DB2.
bato 0xacb08.
replace (bv_swrap 32 (bv_wrap 32 (v2 + 536870912) ≫ 30)) with 0
by (unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 32) with 4294967296; rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; rewrite Z.div_small by lia; reflexivity).
bato 0xacb40.
assert (N0 : nth_error gtab (Z.to_nat (v2 * 4)) = Some (nth (Z.to_nat (v2 * 4)) gtab (Z_to_bv 8 0))) by (apply nth_error_nth'; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (u8ro_read bsegs mc G gtab (v2 * 4) _ _ GT N0 ltac:(lia) eq_refl) as RD0 end.
astep. chk_merge OBG 1.
bato 0xacb4c.
astep.
bato 0xacb84.
replace (v2 * 4 + 1 + G) with (G + v2 * 4 + 1) by lia.
assert (N1 : nth_error gtab (Z.to_nat (v2 * 4 + 1)) = Some (nth (Z.to_nat (v2 * 4 + 1)) gtab (Z_to_bv 8 0))) by (apply nth_error_nth'; lia).
assert (N2 : nth_error gtab (Z.to_nat (v2 * 4 + 2)) = Some (nth (Z.to_nat (v2 * 4 + 2)) gtab (Z_to_bv 8 0))) by (apply nth_error_nth'; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u8ro_read bsegs mc G gtab (v2 * 4 + 1) _ (wa (G + v2 * 4 + 1)) GT N1 ltac:(lia) ltac:(f_equal; lia)) as RD1 end.
bato 0xacb90. astep. chk_merge OBG 1.
bato 0xacbd0.
replace (v2 * 4 + 2 + G) with (G + v2 * 4 + 2) by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u8ro_read bsegs mc G gtab (v2 * 4 + 2) _ (wa (G + v2 * 4 + 2)) GT N2 ltac:(lia) ltac:(f_equal; lia)) as RD2 end.
bato 0xacbdc. astep. chk_merge OBG 1.
bato 0xacc04.
astep.
unfold p3_frameB. finish.
- eassumption.
- split; [exists rj2; split; [exact Lrj2| exact OBJ2]| split; [exists bs2; split; [exact DAT2| exact Hbs2]| exact SIDE2]].
- lia.
- lia.
- lia.
Qed.
End W1.

Section W1b.
Variables (pv pg usp lo e32 pitch : Z).
Variables gp tp s2 s3 s4 s5 s7 s10 s11 : word.
Variable m : mem.
Hypothesis OBPV : aobj bsegs m pv 4.
Hypothesis OBPG : aobj bsegs m pg 12.
Hypothesis PV4 : pv mod 4 = 0.
Hypothesis PG4 : pg mod 4 = 0.
Hypothesis LO : lo <= usp - 144.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis VSH : hidp (pv + 4 <= SH_LO \/ SH_HI <= pv).
Hypothesis GSH : hidp (pg + 12 <= SH_LO \/ SH_HI <= pg).
Hypothesis VAP : pv + 4 <= lo.
Hypothesis GAP : pg + 12 <= lo.
Hypothesis VG : pv + 4 <= pg \/ pg + 12 <= pv.
Hypothesis PIT : 0 <= pitch < 2^31.
Hypothesis VPOS : 0 < pv.
Hypothesis GPOS : 0 < pg.
Local Notation W := [(pv, pv + 4); (pg, pg + 12)].

Lemma p3_w1b : forall (j0 j16 : list byte) (cpv g0 g1 g2 cfs0 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra opv q0 q1 q2 : word)
(ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a7 t3 t4 t5 t6 : word) F fc,
frm0 fc -> mem_inv bsegs m -> stk bsegs m lo (usp + -144) ->
rw_cells bsegs m (usp + -144) (p3_frameB j0 cpv j16 g0 g1 g2 cfs0 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
rw_cells bsegs m pv [C4 opv] -> rw_cells bsegs m pg (f32 [q0; q1; q2]) ->
evt bsegs (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc' m' (pg' : list word),
ms' = MS (mkR (Z_to_bv 64 0xacd64) (Z_to_bv 64 (usp + -144)) gp tp t0' t1' t2' (Z_to_bv 64 40) (Z_to_bv 64 e32)
(Z_to_bv 64 e32) (Z_to_bv 64 0) (Z_to_bv 64 160) a3' a4' a5' a6' a7'
s2 s3 s4 s5 (Z_to_bv 64 pg) s7 (Z_to_bv 64 SHB) (Z_to_bv 64 pitch) s10 s11 t3' t4' t5' t6')
F' (Z_to_bv 64 0x6689c) fc' None m' (seg_rom bsegs)
/\ munch W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp + -144) /\ frm0 fc'
/\ rw_cells bsegs m' (usp + -144) (p3_frameB j0 cpv j16 g0 g1 g2 cfs0 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra)
/\ rw_cells bsegs m' pv [C4 (Z_to_bv 64 pitch)] /\ rw_cells bsegs m' pg (f32 pg') /\ length pg' = 3%nat)
(MS (mkR ra (Z_to_bv 64 (usp + -144)) gp tp t0 t1 t2 (Z_to_bv 64 40) (Z_to_bv 64 e32) a0 a1 a2 a3 a4 a5 (Z_to_bv 64 pv) a7
s2 s3 s4 s5 (Z_to_bv 64 pg) s7 (Z_to_bv 64 SHB) (Z_to_bv 64 pitch) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xaccbc) fc None m (seg_rom bsegs)).
Proof using OBPV OBPG PV4 PG4 LO LOS SPH VSH GSH VAP GAP VG PIT VPOS GPOS.
intros j0 j16 cpv g0 g1 g2 cfs0 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra opv q0 q1 q2 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a7 t3 t4 t5 t6 F fc FRM MI ST FR XPV XPG.
pose proof OBPV as (OV0 & OV1 & _). pose proof OBPG as (OG0 & OG1 & _). unfold APP_TOP in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh W) by (pose proof (VSH : _ \/ _) as Y1; pose proof (GSH : _ \/ _) as Y2; cbn; unfold SH_LO, SH_HI in *; lia).
assert (PG84 : (pg + 8) mod 4 = 0) by (clear - PG4; Z.div_mod_to_equations; lia).
assert (PG44 : (pg + 4) mod 4 = 0) by (clear - PG4; Z.div_mod_to_equations; lia).
unfold p3_frameB in FR. rewrite !f32_cons, ?f32_nil in XPG.
bato 0xaccd4. astep. chk_merge OBPV 4.
bato 0xaccf8. astep. chk_merge OBPG 4.
bato 0xacd1c. astep. chk_merge OBPG 4.
bato 0xacd4c. astep. chk_merge OBPG 4.
bato 0xacd60. astep.
unfold p3_frameB. finish.
- lazymatch goal with H : rw_cells bsegs ?mm pg [C4 ?a; C4 ?b; C4 ?c] |- rw_cells bsegs ?mm pg _ => change (rw_cells bsegs mm pg (f32 [a; b; c])) in H; exact H end.
- reflexivity.
Qed.
End W1b.

