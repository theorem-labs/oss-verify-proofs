(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1df X1ck X1cg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05l X05k X09e.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation mem := (word -> option byte).

Local Ltac slia ::= (try unfold BITS_SIZEOF in * ); first [ exact I | lia | split; [lia|exact I] ].

Definition A_pitch_unquant_3tap : Z := 0xa7ff4.

Definition p3_frame (j0 : list byte) (g0 g1 g2 cfs0 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) : list cell :=
[CB 4 j0; C4 g0; C4 g1; C4 g2; C8 cfs0; C8 c11; C8 c10; C8 c9; C8 c8; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra].

Section W1.
Context {ptr : Type}.
Variables (A D EB e0 e32 pv pg usp lo start fin PAR G GN gbits pbits off : Z) (b : bits_st ptr).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable m : mem.
Local Notation exc := (EB + 4 * e0).
Hypothesis REP : bits_rep asegs m A D b.
Hypothesis OK : bits_ok b.
Hypothesis OBA : aobj asegs m A BITS_SIZEOF.
Hypothesis OBD : aobj asegs m D (sb_buf_size b).
Hypothesis OBPAR : aobj asegs m PAR 16.
Hypothesis PAR8 : PAR mod 8 = 0.
Hypothesis PARI : PAR + 16 <= IMG_TOP.
Hypothesis OBG : aobj asegs m G GN.
Hypothesis GNE : GN = 4 * 2 ^ gbits.
Hypothesis GTI : G + GN <= IMG_TOP.
Hypothesis ST17 : 17 <= start <= 144.
Hypothesis LO : lo <= usp - 128 - 32.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp + 40 < 2^63.
Hypothesis ASH : hidp (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A).
Hypothesis ATOP : IMG_TOP <= A.
Hypothesis ALO : A + BITS_SIZEOF <= lo.
Hypothesis DLO : D + sb_buf_size b <= lo.

Lemma p3_w1a : forall (stk8 : word) (gtab : list byte) (t0 t1 t2 t3 t4 t5 t6 : word) F fc,
u8ro asegs m G gtab -> Z.of_nat (length gtab) = GN ->
ro_cells asegs m PAR [C8 (Z_to_bv 64 G); C4 (Z_to_bv 64 gbits); C4 (Z_to_bv 64 pbits)] ->
rw_cells asegs m usp [C8 (Z_to_bv 64 A); C8 stk8; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 off); C8 (Z_to_bv 64 0)] ->
0 <= gbits <= 7 -> 0 <= pbits <= 7 ->
frm0 fc -> stk asegs m lo usp -> client_consts m -> mem_inv asegs m ->
evt asegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' g0 g1 g2 : word) (j0 : list byte) F' fc' m',
let b1 := snd (speex_bits_unpack_unsigned b pbits) in let v1 := fst (speex_bits_unpack_unsigned b pbits) in
let b2 := snd (speex_bits_unpack_unsigned b1 gbits) in
ms' = MS (mkR ra' (Z_to_bv 64 (usp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 40) (Z_to_bv 64 e32) a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 exc) (Z_to_bv 64 start) (Z_to_bv 64 pg) (Z_to_bv 64 v1) (Z_to_bv 64 pv) (Z_to_bv 64 (v1 + start)) (Z_to_bv 64 A) (Z_to_bv 64 SHB)
(Z_to_bv 64 G) (Z_to_bv 64 gbits) t3' t4' t5' t6')
F' (Z_to_bv 64 0xa8214) fc' None m' (seg_rom asegs)
/\ munch [(A, A + 48); (usp + -160, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -128) /\ frm0 fc'
/\ rw_cells asegs m' (usp + -128) (p3_frame j0 g0 g1 g2 (reg_get F 8) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
/\ bits_rep asegs m' A D b2 /\ bits_ok b2 /\ sb_buf_size b2 = sb_buf_size b /\ 0 <= v1 < 2 ^ pbits)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 exc) (Z_to_bv 64 e32) (Z_to_bv 64 start) (Z_to_bv 64 fin) (Z_to_bv 64 PAR)
(Z_to_bv 64 40) (Z_to_bv 64 pv) (Z_to_bv 64 pg) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_pitch_unquant_3tap) fc None m (seg_rom asegs)).
Proof.
intros stk8 gtab t0 t1 t2 t3 t4 t5 t6 F fc GT LGT XPAR ARGS GB PB FRM ST CC MI.
assert (P2 : 1 <= 2 ^ gbits <= 2 ^ 7) by (split; [apply (Z.pow_le_mono_r 2 0 gbits); lia | apply Z.pow_le_mono_r; lia]). change (2^7) with 128 in P2.
pose proof OBG as (OG0 & OG1 & _). pose proof GTI as GTI'. unfold IMG_TOP in GTI'.
pose proof CC as (G1 & G2 & G3 & G4).
unfold A_pitch_unquant_3tap, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof REP as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE). unfold bits_cells in OBJ.
pose proof (bits_ints A D b OK SIDE) as (In_ & Ic & Ib & Io & Iv & Is & Rc & Rb & Rp & Rn & Rs & R1 & Rov).
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. lia. }
pose proof (u8arr_bound _ _ _ _ DAT) as DB.
pose proof OBA as (OA0 & OA1 & _). pose proof OBD as (OD0 & OD1 & _). pose proof OBPAR as (OP0 & OP1 & _). unfold APP_TOP, BITS_SIZEOF in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof PARI as PARI'. unfold IMG_TOP in PARI'. pose proof ATOP as ATOP'. unfold IMG_TOP in ATOP'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(A, A + 48); (usp + -160, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(A, A + 48); (usp + -160, usp)]) by (pose proof (ASH : _ \/ _) as Y1; cbn; unfold SH_LO, SH_HI, BITS_SIZEOF in *; lia).
carve_frame 128%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 128 _ [] [4; 4; 4; 4; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xa80a4. rewrite sx32_small by (unfold int31; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (REP1 : bits_rep asegs mc A D b)
by (split; [exists rj; split; [exact Lrj| exact OBJ]| split; [exists bs; split; [exact DAT| exact Hbs]| exact SIDE]]);
pose proof (aobj_munch asegs _ m mc A 48 OBA MU (shfree_of_aobj asegs _ m A 48 OF OBA)) as OBA1;
pose proof (aobj_munch asegs _ m mc D _ OBD MU (shfree_of_aobj asegs _ m D _ OF OBD)) as OBD1;
assert (CC1 : client_consts mc) by (unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))))
end.
clear OBJ DAT.
astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -128) lo b pbits _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK ltac:(lia) OBA1 OBD1 ASH ltac:(lia) LOS ltac:(lia) ALO DLO).
all: try eassumption.

subst x. set (v1 := fst (speex_bits_unpack_unsigned b pbits)) in *. set (b1 := snd (speex_bits_unpack_unsigned b pbits)) in *.
assert (UE1 : speex_bits_unpack_unsigned b pbits = (v1, b1)) by (unfold v1, b1; destruct (speex_bits_unpack_unsigned b pbits); reflexivity).
pose proof (speex_bits_unpack_unsigned_ok b pbits v1 b1 OK ltac:(lia) UE1) as (OK1 & V1R & _ & _ & SZ1 & _).
clear REP1 OBA1 OBD1 CC1.
ato 0xa80d0. rewrite Z.mul_0_r. change (bv_swrap 32 0) with 0. rewrite Z.add_0_r. rewrite sx32_small by (unfold int31; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch asegs _ m mc A 48 OBA MU (shfree_of_aobj asegs _ m A 48 OF OBA)) as OBA1;
pose proof (aobj_munch asegs _ m mc D _ OBD MU (shfree_of_aobj asegs _ m D _ OF OBD)) as OBD1;
assert (CC1 : client_consts mc) by (unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))))
end.
rewrite <- SZ1 in OBD1.
astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -128) lo b1 gbits _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ POST OK1 ltac:(lia) OBA1 OBD1 ASH ltac:(lia) LOS ltac:(lia) ALO ltac:(rewrite SZ1; exact DLO)).
all: try eassumption.
subst x. set (v2 := fst (speex_bits_unpack_unsigned b1 gbits)) in *. set (b2 := snd (speex_bits_unpack_unsigned b1 gbits)) in *.
assert (UE2 : speex_bits_unpack_unsigned b1 gbits = (v2, b2)) by (unfold v2, b2; destruct (speex_bits_unpack_unsigned b1 gbits); reflexivity).
pose proof (speex_bits_unpack_unsigned_ok b1 gbits v2 b2 OK1 ltac:(lia) UE2) as (OK2 & V2R & _ & _ & SZ2 & _).
clear OBA1 OBD1 CC1.
match goal with H : bits_rep asegs _ A D b2 |- _ => destruct H as ((rj2 & Lrj2 & OBJ2) & (bs2 & DAT2 & Hbs2) & SIDE2); unfold bits_cells in OBJ2 end.
assert (Lbs2 : Z.of_nat (length bs2) = sb_buf_size b).
{ pose proof OK2 as OK'. unfold bits_ok in OK'. rewrite Hbs2, zlength_map_unsigned in OK'. lia. }
pose proof (u8arr_bound _ _ _ _ DAT2) as DB2.
ato 0xa80dc. rewrite ?(Z.mod_small v2) by lia. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^2) with 4. rewrite ?swrap32_small by lia.
assert (N0 : nth_error gtab (Z.to_nat (v2 * 4)) = Some (nth (Z.to_nat (v2 * 4)) gtab (Z_to_bv 8 0))) by (apply nth_error_nth'; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (u8ro_read asegs mc G gtab (v2 * 4) _ _ GT N0 ltac:(lia) eq_refl) as RD0 end.
ato 0xa80e8. astep. chk_merge OBG 1.
assert (N1 : nth_error gtab (Z.to_nat (v2 * 4 + 1)) = Some (nth (Z.to_nat (v2 * 4 + 1)) gtab (Z_to_bv 8 0))) by (apply nth_error_nth'; lia).
assert (N2 : nth_error gtab (Z.to_nat (v2 * 4 + 2)) = Some (nth (Z.to_nat (v2 * 4 + 2)) gtab (Z_to_bv 8 0))) by (apply nth_error_nth'; lia).
ato 0xa8120.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u8ro_read asegs mc G gtab (v2 * 4 + 1) _ (wa (G + v2 * 4 + 1)) GT N1 ltac:(lia) ltac:(f_equal; lia)) as RD1 end.
astep. chk_merge OBG 1.
ato 0xa8148.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u8ro_read asegs mc G gtab (v2 * 4 + 2) _ (wa (G + v2 * 4 + 2)) GT N2 ltac:(lia) ltac:(f_equal; lia)) as RD2 end.
astep. chk_merge OBG 1.
ato 0xa8168. astep.
assert (P3 : 2 ^ pbits <= 2 ^ 7) by (apply Z.pow_le_mono_r; lia). change (2^7) with 128 in P3.
rewrite ?(Z.mod_small v1), ?(Z.mod_small start) by lia. rewrite ?swrap32_small by lia.
unfold p3_frame. finish.
- eassumption.
- split; [exists rj2; split; [exact Lrj2| exact OBJ2]| split; [exists bs2; split; [exact DAT2| exact Hbs2]| exact SIDE2]].
- lia.
- lia.
- lia.
Qed.
End W1.

Section W1b.
Variables (pv pg usp lo e32 pitch : Z).
Variables ra gp tp s2 s3 s5 s8 s10 s11 : word.
Variable m : mem.
Hypothesis OBPV : aobj asegs m pv 4.
Hypothesis OBPG : aobj asegs m pg 12.
Hypothesis PV4 : pv mod 4 = 0.
Hypothesis PG4 : pg mod 4 = 0.
Hypothesis LO : lo <= usp - 128.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis VSH : hidp (pv + 4 <= SH_LO \/ SH_HI <= pv).
Hypothesis GSH : hidp (pg + 12 <= SH_LO \/ SH_HI <= pg).
Hypothesis VAP : pv + 4 <= lo.
Hypothesis GAP : pg + 12 <= lo.
Hypothesis VG : pv + 4 <= pg \/ pg + 12 <= pv.
Hypothesis PIT : 0 <= pitch < 2^31.
Local Notation W := [(pv, pv + 4); (pg, pg + 12)].

Lemma p3_w1b : forall (j0 : list byte) (g0 g1 g2 cfs0 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra opv q0 q1 q2 : word)
(t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc,
frm0 fc -> mem_inv asegs m -> stk asegs m lo (usp + -128) ->
rw_cells asegs m (usp + -128) (p3_frame j0 g0 g1 g2 cfs0 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
rw_cells asegs m pv [C4 opv] -> rw_cells asegs m pg (f32 [q0; q1; q2]) ->
evt asegs (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc' m' (pg' : list word),
ms' = MS (mkR (Z_to_bv 64 0xa8288) (Z_to_bv 64 (usp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 40) (Z_to_bv 64 e32)
(Z_to_bv 64 e32) (Z_to_bv 64 0) (Z_to_bv 64 160) a3' a4' a5' a6' a7'
s2 s3 (Z_to_bv 64 pg) s5 (Z_to_bv 64 pv) (Z_to_bv 64 pitch) s8 (Z_to_bv 64 SHB) s10 s11 t3' t4' t5' t6')
F' (Z_to_bv 64 0x667b0) fc' None m' (seg_rom asegs)
/\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -128) /\ frm0 fc'
/\ rw_cells asegs m' (usp + -128) (p3_frame j0 g0 g1 g2 cfs0 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra)
/\ rw_cells asegs m' pv [C4 (Z_to_bv 64 pitch)] /\ rw_cells asegs m' pg (f32 pg') /\ length pg' = 3%nat)
(MS (mkR ra (Z_to_bv 64 (usp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 40) (Z_to_bv 64 e32) a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 (Z_to_bv 64 pg) s5 (Z_to_bv 64 pv) (Z_to_bv 64 pitch) s8 (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa8214) fc None m (seg_rom asegs)).
Proof.
intros j0 g0 g1 g2 cfs0 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra opv q0 q1 q2 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc FRM MI ST FR XPV XPG.
pose proof OBPV as (OV0 & OV1 & _). pose proof OBPG as (OG0 & OG1 & _). unfold APP_TOP in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh W) by (pose proof (VSH : _ \/ _) as Y1; pose proof (GSH : _ \/ _) as Y2; cbn; unfold SH_LO, SH_HI in *; lia).
unfold p3_frame in FR. rewrite !f32_cons, ?f32_nil in XPG.
ato 0xa8220. astep. chk_merge OBPV 4.
ato 0xa8238. astep. chk_merge OBPG 4.
ato 0xa8254. astep. chk_merge OBPG 4.
ato 0xa8270. astep. chk_merge OBPG 4.
ato 0xa8284. astep.
unfold p3_frame. finish.
- lazymatch goal with H : rw_cells asegs ?mm pg [C4 ?a; C4 ?b; C4 ?c] |- rw_cells asegs ?mm pg _ => change (rw_cells asegs mm pg (f32 [a; b; c])) in H; exact H end.
- reflexivity.
Qed.
End W1b.
