(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1ch X1cg X1cr X1cs X1dg X1df X1ck X1co X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05l X05k X05b X081 X082
X05m X09f X06d X069 X06n.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require X020.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X12b X0z5 X0wh X0w8 X0ys X0yt X0x2 X0xf.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0sz.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0z5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wh OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w8 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xf.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac tlia ::= (try unfold BITS_SIZEOF in * ); tlia_one.
Local Ltac slia ::= (try unfold BITS_SIZEOF in * ); first [ exact I | lia | split; [lia|exact I] ].

Definition exp_postZ (elo eq : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (mm : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra (Z_to_bv 64 eq) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (ret_pc ra) fc' None m' (seg_rom bsegs)
/\ munch [(elo, eq)] mm m' /\ wmono bsegs mm m' /\ mem_inv bsegs m' /\ frm0 fc' /\ stk bsegs m' elo eq.
Lemma exp_specZ : forall (elo eq : Z)
(ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (FF : bvmap 5 word) (fcc : bv 32) (mm : mem),
stk bsegs mm elo eq -> elo + 16 <= eq -> 0 <= eq < 2^64 -> mem_inv bsegs mm -> frm0 fcc ->
evt bsegs (exp_postZ elo eq ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mm)
(MS (mkR ra (Z_to_bv 64 eq) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FF (Z_to_bv 64 X0sz.A_exp) fcc None mm (seg_rom bsegs)).
Proof.
intros until mm. intros XSTK XLO XHq XMI XFRM.
pose proof (X0sz.exp_proofA elo ra (Z_to_bv 64 eq) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FF fcc mm) as H.
rewrite !unsigned_lit in H by lia. unfold X0sz.EXP_DEPTH in H. specialize (H XSTK XLO XMI XFRM).
eapply evt_mono; [exact H|]. intros ms' P. unfold X0sz.exp_postA in P. rewrite !unsigned_lit in P by lia.
destruct P as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & F' & fc' & m' & E & MU & WM & MI' & FRM' & STK' & _).
unfold exp_postZ. do 18 eexists. split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact FRM'| exact STK'].
Qed.

Section UserH.
Context {ptr : Type}.
Variables (A D ST usp lo : Z) (b : bits_st ptr).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable m : mem.
Hypothesis REP : bits_rep bsegs m A D b.
Hypothesis OK : bits_ok b.
Hypothesis OBA : aobj bsegs m A BITS_SIZEOF.
Hypothesis OBD : aobj bsegs m D (sb_buf_size b).
Hypothesis ASH : hidp (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A).
Hypothesis ATOP : IMG_TOP_B <= A.
Hypothesis ALO : A + BITS_SIZEOF <= lo.
Hypothesis DLO : D + sb_buf_size b <= lo.
Hypothesis LO : lo <= usp - USERH_DEPTH.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Local Notation W := [(A, A + 48); (usp + -64, usp)].

Lemma user_handler_walk : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc,
client_constsB m -> stk bsegs m lo usp -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (user_handler_postA A D usp lo b ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 ST) (Z_to_bv 64 0) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_default_user_handler) fc None m (seg_rom bsegs)).
Proof.
intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc CC ST0 MI FRM.
pose proof CC as (G1 & G2 & G3 & G4).
unfold A_speex_default_user_handler, USERH_DEPTH, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof REP as ((rj0 & Lrj0 & OBJ) & (bs0 & DAT & Hbs0) & SIDE0). unfold bits_cells in OBJ.
assert (Lbs0 : Z.of_nat (length bs0) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs0, zlength_map_unsigned in OK'. lia. }
pose proof OBA as (OA0 & OA1 & _). pose proof OBD as (OD0 & OD1 & _). unfold APP_TOP, BITS_SIZEOF in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. unfold IMG_TOP_B in ATOP.
pose proof ST0 as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh W).
{ pose proof (ASH : _ \/ _) as Y1. clear - Y1 LOS LO. cbn. unfold SH_LO, SH_HI in *. lia. }
carve_frame 16%nat ST0.
apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
bato 0xb2c7c.
rebase_bits A D b rj0 bs0.
astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -16) lo b 4 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK ltac:(lia) OBA1 OBD1 (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO DLO).
all: try eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
match goal with H : stk bsegs _ lo _ |- _ => rename H into STK end.
change (snd (speex_bits_unpack_unsigned b 4)) with (ub b 4) in *. change (fst (speex_bits_unpack_unsigned b 4)) with (uv b 4) in *.
pose proof (ub_ok b 4 OK ltac:(lia)) as (OK1 & SZ1 & V1R). change (2 ^ 4) with 16 in V1R.
clear REP1 OBA1 OBD1 CC1.
match goal with H : bits_rep bsegs _ A D (ub b 4) |- _ => destruct H as ((rj1 & Lrj1 & OBJ) & (bs1 & DAT & Hbs1) & SIDE1); unfold bits_cells in OBJ end.
assert (Lbs1 : Z.of_nat (length bs1) = sb_buf_size b).
{ pose proof OK1 as OK'. unfold bits_ok in OK'. rewrite Hbs1, zlength_map_unsigned in OK'. lia. }
bato 0xb2c8c.
assert (SG : bv_swrap 32 (Z.shiftr (bv_wrap 32 (uv b 4 + 268435456)) 29) = 0).
{ unfold bv_wrap, bv_modulus. rewrite Z.mod_small by (change (2 ^ Z.of_N 32) with 4294967296; lia).
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by (change (2^29) with 536870912; lia). reflexivity. }
rewrite SG.
bato 0xb2c9c.
replace (bv_swrap 32 (Z.shiftl (uv b 4) 3) + 5) with (5 + 8 * uv b 4)
by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 3) with 8; rewrite swrap32_small by lia; lia).
rebase_bits A D (ub b 4) rj1 bs1. rewrite <- SZ1 in OBD1.
astep.
call (speex_bits_advance_walk A D (usp + -16) lo (ub b 4) (5 + 8 * uv b 4) _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK1 ltac:(lia) OBA1 (ASH : _ \/ _)).
all: try eassumption; try lia.
match goal with H : bits_rep bsegs _ A D (speex_bits_advance (ub b 4) _) |- _ => rename H into REP2 end.
match goal with H : stk bsegs _ lo (usp + -16) |- _ => rename H into STK2 end.
pose proof (speex_bits_advance_ok (ub b 4) (5 + 8 * uv b 4) OK1) as AOK.
bato 0xb2cb0. release_frame FR STK2 usp. astep.
apply evt_done. unfold user_handler_postA, USERH_DEPTH, BITS_SIZEOF. do 17 eexists.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK2|]. split; [exact FRM|].
unfold user_handler_bits. split; [exact REP2|].
apply AOK. unfold bits_ok, bits_pos in OK1 |- *. lia.
Qed.
End UserH.

Section StereoH.
Context {ptr : Type}.
Variables (A D STP STEREO usp lo : Z) (b : bits_st ptr).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable m : mem.
Hypothesis REP : bits_rep bsegs m A D b.
Hypothesis OK : bits_ok b.
Hypothesis OBA : aobj bsegs m A BITS_SIZEOF.
Hypothesis OBD : aobj bsegs m D (sb_buf_size b).
Hypothesis OBS : aobj bsegs m STEREO 8.
Hypothesis OBT : aobj bsegs m A_e_ratio_quant 16.
Hypothesis S4 : STEREO mod 4 = 0.
Hypothesis ASH : hidp (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A).
Hypothesis SSH : hidp (STEREO + 8 <= SH_LO \/ SH_HI <= STEREO).
Hypothesis ATOP : IMG_TOP_B <= A.
Hypothesis STOP : IMG_TOP_B <= STEREO.
Hypothesis ALO : A + BITS_SIZEOF <= lo.
Hypothesis DLO : D + sb_buf_size b <= lo.
Hypothesis SLO : STEREO + 8 <= lo.
Hypothesis SEPSA : hidp (STEREO + 8 <= A \/ A + BITS_SIZEOF <= STEREO).
Hypothesis SEPSD : hidp (STEREO + 8 <= D \/ D + sb_buf_size b <= STEREO).
Hypothesis LO : lo <= usp - STEREOH_DEPTH.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Local Notation W := [(A, A + 48); (STEREO, STEREO + 8); (usp + -96, usp)].

Lemma stereo_handler_walk : forall (sws : list word) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc,
rw_cells bsegs m STEREO (f32 sws) -> length sws = 2%nat ->
client_constsB m -> stk bsegs m lo usp -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (stereo_handler_postA A D STEREO usp lo b ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 STP) (Z_to_bv 64 STEREO) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_std_stereo_request_handler) fc None m (seg_rom bsegs)).
Proof.
intros sws t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc SW LSW CC ST0 MI FRM.
pose proof CC as (G1 & G2 & G3 & G4).
unfold A_speex_std_stereo_request_handler, A_e_ratio_quant, STEREOH_DEPTH, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof REP as ((rj0 & Lrj0 & OBJ) & (bs0 & DAT & Hbs0) & SIDE0). unfold bits_cells in OBJ.
assert (Lbs0 : Z.of_nat (length bs0) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs0, zlength_map_unsigned in OK'. lia. }
pose proof OBA as (OA0 & OA1 & _). pose proof OBD as (OD0 & OD1 & _). pose proof OBS as (OS0 & OS1 & _). unfold APP_TOP, BITS_SIZEOF in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. unfold IMG_TOP_B in ATOP, STOP.
pose proof ST0 as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh W).
{ pose proof (ASH : _ \/ _) as Y1. pose proof (SSH : _ \/ _) as Y2. clear - Y1 Y2 LOS LO. cbn. unfold SH_LO, SH_HI in *. lia. }
pose proof (SEPSA : _ \/ _) as SEPSA'. pose proof (SEPSD : _ \/ _) as SEPSD'. hide_disj.
destruct sws as [|w0 [|w1 [|]]]; cbn [length] in LSW; try lia. rewrite f32_cons, f32_cons, f32_nil in SW.
carve_frame 48%nat ST0.
apply (rw_cells_split_CB bsegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
bato 0x99220.

rebase_bits A D b rj0 bs0.
astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -48) lo b 1 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK ltac:(lia) OBA1 OBD1 (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO DLO).
all: try eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
match goal with H : stk bsegs _ lo _ |- _ => rename H into STK end.
change (snd (speex_bits_unpack_unsigned b 1)) with (ub b 1) in *. change (fst (speex_bits_unpack_unsigned b 1)) with (uv b 1) in *.
pose proof (ub_ok b 1 OK ltac:(lia)) as (OK1 & SZ1 & V1R). change (2 ^ 1) with 2 in V1R.
clear REP1 OBA1 OBD1 CC1.
match goal with H : bits_rep bsegs _ A D (ub b 1) |- _ => destruct H as ((rj1 & Lrj1 & OBJ) & (bs1 & DAT & Hbs1) & SIDE1); unfold bits_cells in OBJ end.
assert (Lbs1 : Z.of_nat (length bs1) = sb_buf_size b).
{ pose proof OK1 as OK'. unfold bits_ok in OK'. rewrite Hbs1, zlength_map_unsigned in OK'. lia. }
bato 0x99230.

rebase_bits A D (ub b 1) rj1 bs1. rewrite <- SZ1 in OBD1.
astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -48) lo (ub b 1) 5 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK1 ltac:(lia) OBA1 OBD1 (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO ltac:(rewrite SZ1; exact DLO)).
all: try eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
match goal with H : stk bsegs _ lo _ |- _ => rename H into STK2 end.
change (snd (speex_bits_unpack_unsigned (ub b 1) 5)) with (ub (ub b 1) 5) in *. change (fst (speex_bits_unpack_unsigned (ub b 1) 5)) with (uv (ub b 1) 5) in *.
pose proof (ub_ok (ub b 1) 5 OK1 ltac:(lia)) as (OK2 & SZ2 & V2R). change (2 ^ 5) with 32 in V2R. rewrite SZ1 in SZ2.
clear REP1 OBA1 OBD1 CC1.
match goal with H : bits_rep bsegs _ A D (ub (ub b 1) 5) |- _ => destruct H as ((rj2 & Lrj2 & OBJ) & (bs2 & DAT & Hbs2) & SIDE2); unfold bits_cells in OBJ end.
assert (Lbs2 : Z.of_nat (length bs2) = sb_buf_size b).
{ pose proof OK2 as OK'. unfold bits_ok in OK'. rewrite Hbs2, zlength_map_unsigned in OK'. lia. }
bato 0x99240.

assert (SGN : uv b 1 = 0 \/ uv b 1 = 1) by lia.
destruct SGN as [SG|SG]; rewrite SG.
all: bato 0x99254.
all: lazymatch goal with |- context [Z_to_bv 64 (145208 + ?e)] => let v := eval vm_compute in (145208 + e) in change (145208 + e) with v end.
all: bato 0x99264.
1: {

destruct (stk_split bsegs _ lo (usp + -64) (usp + -48) STK2 ltac:(lia)) as [STKa STKb]. clear STK2.
astep.
call (exp_specZ (usp + -64) (usp + -48)).
1: exact STKb. 1: lia. 1: lia. 1: eassumption. 1: exact FRM.
match goal with H : stk bsegs _ (usp + -64) (usp + -48) |- _ => pose proof (stk_merge bsegs _ lo (usp + -64) (usp + -48) STKa H ltac:(lia)) as STK3; clear H STKa end.
clear FRM. match goal with H : frm0 _ |- _ => rename H into FRM3 end.
replace (ret_pc (Z_to_bv 64 627304)) with (Z_to_bv 64 627304) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

bato 0x99274. astep. chk_merge OBS 4.
bato 0x99288.

rebase_bits A D (ub (ub b 1) 5) rj2 bs2. rewrite <- SZ2 in OBD1.
astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -48) lo (ub (ub b 1) 5) 2 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK2 ltac:(lia) OBA1 OBD1 (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO ltac:(rewrite SZ2; exact DLO)).
all: try eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
match goal with H : stk bsegs _ lo _ |- _ => rename H into STK4 end.
change (snd (speex_bits_unpack_unsigned (ub (ub b 1) 5) 2)) with (ub (ub (ub b 1) 5) 2) in *.
change (fst (speex_bits_unpack_unsigned (ub (ub b 1) 5) 2)) with (uv (ub (ub b 1) 5) 2) in *.
pose proof (ub_ok (ub (ub b 1) 5) 2 OK2 ltac:(lia)) as (OK3 & SZ3 & V3R). change (2 ^ 2) with 4 in V3R. rewrite SZ2 in SZ3.
clear REP1 OBA1 OBD1 CC1.
match goal with H : bits_rep bsegs _ A D (ub (ub (ub b 1) 5) 2) |- _ => destruct H as ((rj3 & Lrj3 & OBJ) & (bs3 & DAT & Hbs3) & SIDE3); unfold bits_cells in OBJ end.
assert (Lbs3 : Z.of_nat (length bs3) = sb_buf_size b).
{ pose proof OK3 as OK'. unfold bits_ok in OK'. rewrite Hbs3, zlength_map_unsigned in OK'. lia. }

assert (V8 : 145248 mod 8 = 0) by reflexivity.
assert (CASES : uv (ub (ub b 1) 5) 2 = 0 \/ uv (ub (ub b 1) 5) 2 = 1 \/ uv (ub (ub b 1) 5) 2 = 2 \/ uv (ub (ub b 1) 5) 2 = 3) by lia.
destruct CASES as [T|[T|[T|T]]]; rewrite T.
all: bato 0x992d4.
all: astep.
all: chk_merge OBS 4.
all: bato 0x992f8.
all: release_frame FR STK4 usp.
all: astep.
all: apply evt_done; unfold stereo_handler_postA, STEREOH_DEPTH, BITS_SIZEOF; do 17 eexists; eexists [_; _];
split; [reflexivity|];
split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact STK4|]; split; [eassumption|];
split; [rewrite f32_cons, f32_cons, f32_nil; exact SW|]; split; [reflexivity|];
split; [| exact OK3];
(split; [exists rj3; split; [exact Lrj3| unfold bits_cells; exact OBJ]| split; [exists bs3; split; [exact DAT| exact Hbs3]| exact SIDE3]]).
}
1: {

destruct (stk_split bsegs _ lo (usp + -64) (usp + -48) STK2 ltac:(lia)) as [STKa STKb]. clear STK2.
astep.
call (exp_specZ (usp + -64) (usp + -48)).
1: exact STKb. 1: lia. 1: lia. 1: eassumption. 1: exact FRM.
match goal with H : stk bsegs _ (usp + -64) (usp + -48) |- _ => pose proof (stk_merge bsegs _ lo (usp + -64) (usp + -48) STKa H ltac:(lia)) as STK3; clear H STKa end.
clear FRM. match goal with H : frm0 _ |- _ => rename H into FRM3 end.
replace (ret_pc (Z_to_bv 64 627304)) with (Z_to_bv 64 627304) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

bato 0x99274. astep. chk_merge OBS 4.
bato 0x99288.

rebase_bits A D (ub (ub b 1) 5) rj2 bs2. rewrite <- SZ2 in OBD1.
astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -48) lo (ub (ub b 1) 5) 2 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK2 ltac:(lia) OBA1 OBD1 (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO ltac:(rewrite SZ2; exact DLO)).
all: try eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
match goal with H : stk bsegs _ lo _ |- _ => rename H into STK4 end.
change (snd (speex_bits_unpack_unsigned (ub (ub b 1) 5) 2)) with (ub (ub (ub b 1) 5) 2) in *.
change (fst (speex_bits_unpack_unsigned (ub (ub b 1) 5) 2)) with (uv (ub (ub b 1) 5) 2) in *.
pose proof (ub_ok (ub (ub b 1) 5) 2 OK2 ltac:(lia)) as (OK3 & SZ3 & V3R). change (2 ^ 2) with 4 in V3R. rewrite SZ2 in SZ3.
clear REP1 OBA1 OBD1 CC1.
match goal with H : bits_rep bsegs _ A D (ub (ub (ub b 1) 5) 2) |- _ => destruct H as ((rj3 & Lrj3 & OBJ) & (bs3 & DAT & Hbs3) & SIDE3); unfold bits_cells in OBJ end.
assert (Lbs3 : Z.of_nat (length bs3) = sb_buf_size b).
{ pose proof OK3 as OK'. unfold bits_ok in OK'. rewrite Hbs3, zlength_map_unsigned in OK'. lia. }

assert (V8 : 145248 mod 8 = 0) by reflexivity.
assert (CASES : uv (ub (ub b 1) 5) 2 = 0 \/ uv (ub (ub b 1) 5) 2 = 1 \/ uv (ub (ub b 1) 5) 2 = 2 \/ uv (ub (ub b 1) 5) 2 = 3) by lia.
destruct CASES as [T|[T|[T|T]]]; rewrite T.
all: bato 0x992d4.
all: astep.
all: chk_merge OBS 4.
all: bato 0x992f8.
all: release_frame FR STK4 usp.
all: astep.
all: apply evt_done; unfold stereo_handler_postA, STEREOH_DEPTH, BITS_SIZEOF; do 17 eexists; eexists [_; _];
split; [reflexivity|];
split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact STK4|]; split; [eassumption|];
split; [rewrite f32_cons, f32_cons, f32_nil; exact SW|]; split; [reflexivity|];
split; [| exact OK3];
(split; [exists rj3; split; [exact Lrj3| unfold bits_cells; exact OBJ]| split; [exists bs3; split; [exact DAT| exact Hbs3]| exact SIDE3]]).
}
Qed.
End StereoH.

Ltac decide_ltbs :=
repeat match goal with
| |- context [?x <? ?y] =>
first [ replace (x <? y) with true by (symmetry; apply Z.ltb_lt; lia)
| replace (x <? y) with false by (symmetry; apply Z.ltb_ge; lia) ]
end.

Lemma cbs_cells_split : forall k f d sc js n, (n < k)%nat -> (k <= length js)%nat ->
exists pre post,
cbs_cells k f d sc js
= pre ++ (if (16 - Z.of_nat k + Z.of_nat n =? 9) && sc then cb_cells f d (nth n js ([], [])) else cb_cells 0 0 (nth n js ([], [])))
++ post
/\ cells_size pre = (40 * n)%nat.
Proof.
induction k as [|k IH]; intros f d sc js n Hn Hk; [lia|].
destruct js as [|j js']; [cbn in Hk; lia|]. cbn [length] in Hk.
destruct n as [|n'].
- exists [], (cbs_cells k f d sc js'). split; [|reflexivity].
cbn [cbs_cells nth app]. cbv zeta.
replace (16 - Z.of_nat (S k) + Z.of_nat 0) with (16 - Z.of_nat (S k)) by lia. reflexivity.
- destruct (IH f d sc js' n' ltac:(lia) ltac:(lia)) as (pre & post & E & SZ).
exists ((if (16 - Z.of_nat (S k) =? 9) && sc then cb_cells f d j else cb_cells 0 0 j) ++ pre), post.
split.
+ cbn [cbs_cells nth]. cbv zeta. rewrite E.
replace (16 - Z.of_nat k + Z.of_nat n') with (16 - Z.of_nat (S k) + Z.of_nat (S n')) by lia.
rewrite <- app_assoc. reflexivity.
+ rewrite cells_size_app, SZ. destruct ((16 - Z.of_nat (S k) =? 9) && sc); rewrite cb_cells_size; lia.
Qed.

Section InbandH.
Context {ptr : Type}.
Variables (A D CBA STP STEREO usp lo : Z) (b : bits_st ptr) (sc : bool) (js : list (list byte * list byte)).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable m : mem.
Hypothesis REP : bits_rep bsegs m A D b.
Hypothesis OK : bits_ok b.
Hypothesis Ljs : length js = 16%nat.
Hypothesis Fjs : Forall (fun p => length (fst p) = 8%nat /\ length (snd p) = 16%nat) js.
Hypothesis OBA : aobj bsegs m A BITS_SIZEOF.
Hypothesis OBD : aobj bsegs m D (sb_buf_size b).
Hypothesis OBC : aobj bsegs m CBA 640.
Hypothesis OBS : aobj bsegs m STEREO 8.
Hypothesis OBT : aobj bsegs m A_e_ratio_quant 16.
Hypothesis C8a : CBA mod 8 = 0.
Hypothesis CPOS : 0 < CBA.
Hypothesis S4 : STEREO mod 4 = 0.
Hypothesis ASH : hidp (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A).
Hypothesis SSH : hidp (STEREO + 8 <= SH_LO \/ SH_HI <= STEREO).
Hypothesis ATOP : IMG_TOP_B <= A.
Hypothesis STOP : IMG_TOP_B <= STEREO.
Hypothesis ALO : A + BITS_SIZEOF <= lo.
Hypothesis DLO : D + sb_buf_size b <= lo.
Hypothesis CLO : CBA + 640 <= lo.
Hypothesis SLO : STEREO + 8 <= lo.
Hypothesis SEPCA : hidp (CBA + 640 <= A \/ A + BITS_SIZEOF <= CBA).
Hypothesis SEPCS : hidp (CBA + 640 <= STEREO \/ STEREO + 8 <= CBA).
Hypothesis SEPSA : hidp (STEREO + 8 <= A \/ A + BITS_SIZEOF <= STEREO).
Hypothesis SEPSD : hidp (STEREO + 8 <= D \/ D + sb_buf_size b <= STEREO).
Hypothesis LO : lo <= usp - INBAND_DEPTH.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Local Notation W := [(A, A + 48); (STEREO, STEREO + 8); (usp + -96, usp)].

Lemma inband_handler_walk : forall (sws : list word) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc,
rw_cells bsegs m CBA (cbs_cells 16 A_speex_std_stereo_request_handler STEREO sc js) ->
rw_cells bsegs m STEREO (f32 sws) -> length sws = 2%nat ->
client_constsB m -> stk bsegs m lo usp -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (inband_postA sc A D STEREO usp lo b ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 CBA) (Z_to_bv 64 STP) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_inband_handler) fc None m (seg_rom bsegs)).
Proof.
intros sws t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc CBS SW LSW CC ST0 MI FRM.
pose proof CC as (G1 & G2 & G3 & G4).
unfold A_speex_inband_handler, INBAND_DEPTH, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof REP as ((rj0 & Lrj0 & OBJ) & (bs0 & DAT & Hbs0) & SIDE0). unfold bits_cells in OBJ.
assert (Lbs0 : Z.of_nat (length bs0) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs0, zlength_map_unsigned in OK'. lia. }
pose proof OBA as (OA0 & OA1 & _). pose proof OBD as (OD0 & OD1 & _). pose proof OBS as (OS0 & OS1 & _). pose proof OBC as (OC0 & OC1 & _). unfold APP_TOP, BITS_SIZEOF in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. unfold IMG_TOP_B in ATOP, STOP.
pose proof ST0 as (STa & STb & _).

pose proof (proj1 (proj1 CBS)) as WFC.
assert (CBSB : rw_cells bsegs m CBA [CB 640 (cells_bytes (cbs_cells 16 A_speex_std_stereo_request_handler STEREO sc js))]).
{ eapply rw_cells_samebytes; [exact CBS| | |].
- cbn [cells_wf cell_wf]. split; [|exact I]. rewrite cells_bytes_length by exact WFC. rewrite cbs_cells_size by lia. reflexivity.
- cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
- cbn [cells_size csize]. rewrite cbs_cells_size by lia. reflexivity. }
clear CBS.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh W).
{ pose proof (ASH : _ \/ _) as Y1. pose proof (SSH : _ \/ _) as Y2. clear - Y1 Y2 LOS LO. cbn. unfold SH_LO, SH_HI in *. lia. }
pose proof (SEPSA : _ \/ _) as SEPSA'. pose proof (SEPSD : _ \/ _) as SEPSD'. pose proof (SEPCA : _ \/ _) as SEPCA'. pose proof (SEPCS : _ \/ _) as SEPCS'. hide_disj.
carve_frame 48%nat ST0.
apply (rw_cells_split_CB bsegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
bato 0xb2b50.

rebase_bits A D b rj0 bs0.
astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -48) lo b 4 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK ltac:(lia) OBA1 OBD1 (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO DLO).
all: try eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
match goal with H : stk bsegs _ lo _ |- _ => rename H into STK end.
change (snd (speex_bits_unpack_unsigned b 4)) with (ub b 4) in *. change (fst (speex_bits_unpack_unsigned b 4)) with (uv b 4) in *.
pose proof (ub_ok b 4 OK ltac:(lia)) as (OK1 & SZ1 & V1R). change (2 ^ 4) with 16 in V1R.
clear REP1 OBA1 OBD1 CC1.
match goal with H : bits_rep bsegs _ A D (ub b 4) |- _ => destruct H as ((rj1 & Lrj1 & OBJ) & (bs1 & DAT & Hbs1) & SIDE1); unfold bits_cells in OBJ end.
assert (Lbs1 : Z.of_nat (length bs1) = sb_buf_size b).
{ pose proof OK1 as OK'. unfold bits_ok in OK'. rewrite Hbs1, zlength_map_unsigned in OK'. lia. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (CBS : rw_cells bsegs mc CBA (cbs_cells 16 A_speex_std_stereo_request_handler STEREO sc js)) end.
{ eapply rw_cells_samebytes; [exact CBSB| exact WFC| |].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
- cbn [cells_size csize]. rewrite cbs_cells_size by lia. reflexivity. }
clear CBSB.
destruct (cbs_cells_split 16 A_speex_std_stereo_request_handler STEREO sc js (Z.to_nat (uv b 4)) ltac:(lia) ltac:(lia)) as (pre & post & E & SZ).
rewrite E in CBS. apply rw_cells_app in CBS. destruct CBS as [PRE CBS]. apply rw_cells_app in CBS. destruct CBS as [ENT POST].
rewrite SZ in ENT.
replace (16 - Z.of_nat 16 + Z.of_nat (Z.to_nat (uv b 4))) with (uv b 4) in ENT by lia.
replace (CBA + Z.of_nat (40 * Z.to_nat (uv b 4))) with (CBA + uv b 4 * 40) in ENT by lia.
clear PRE POST E SZ.
bato 0xb2b9c.
astep.
rewrite (shb_zero bsegs m CBA 640 (CBA + uv b 4 * 40 + 8) (proj2 (proj2 OBC)) ltac:(lia) ltac:(clear - C8a V1R; Z.div_mod_to_equations; lia)).
lit_if.
destruct ((uv b 4 =? 9) && sc) eqn:C9.
-
apply andb_prop in C9. destruct C9 as [C9a C9b]. apply Z.eqb_eq in C9a.
unfold cb_cells in ENT. unfold A_speex_std_stereo_request_handler in ENT.
bato 0xb2ba4. astep.
bato 0xb2bb8. astep.
rewrite (shb_zero bsegs m CBA 640 (CBA + uv b 4 * 40 + 16) (proj2 (proj2 OBC)) ltac:(lia) ltac:(clear - C8a V1R; Z.div_mod_to_equations; lia)).
lit_if.
bato 0xb2be0.
release_frame FR STK usp. astep.
rebase_bits A D (ub b 4) rj1 bs1. rewrite <- SZ1 in OBD1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch bsegs _ m mc STEREO 8 OBS MU (shfree_of_aobj bsegs _ m STEREO 8 OF OBS)) as OBS1;
pose proof (aobj_munch bsegs _ m mc A_e_ratio_quant 16 OBT MU (shfree_of_aobj bsegs _ m A_e_ratio_quant 16 OF OBT)) as OBT1
end.
eapply evt_mono.
+ eapply (stereo_handler_walk A D STP STEREO usp lo (ub b 4) ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ REP1 OK1 OBA1 OBD1 OBS1 OBT1 S4 ASH SSH
ltac:(unfold IMG_TOP_B; lia) ltac:(unfold IMG_TOP_B; lia) ALO ltac:(rewrite SZ1; exact DLO) SLO SEPSA ltac:(rewrite SZ1; exact SEPSD)
ltac:(unfold STEREOH_DEPTH; lia) LOS SPH sws); try eassumption.
+ cbv beta. intros ms' (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F' & fc' & m' & sws' & -> & MU2 & WM2 & MI2 & STK2 & FRM2 & SW2 & LSW2 & REP2 & OK2).
unfold inband_postA, INBAND_DEPTH, STEREOH_DEPTH, BITS_SIZEOF in *. do 18 eexists.
split; [reflexivity|].
split; [eapply munch_trans; [exact MU| exact MU2]|]. split; [eapply wmono_trans; [exact WM| exact WM2]|].
split; [exact MI2|]. split; [exact STK2|]. split; [exact FRM2|]. split; [exact SW2|]. split; [exact LSW2|].
unfold inband_bits. cbv zeta. unfold SPEEX_INBAND_STEREO. rewrite C9b, C9a. cbn [Z.eqb andb Pos.eqb].
split; [exact REP2| exact OK2].
-
assert (C9' : sc && (uv b 4 =? SPEEX_INBAND_STEREO) = false) by (unfold SPEEX_INBAND_STEREO; rewrite andb_comm; exact C9).
unfold cb_cells in ENT.
bato 0xb2ba4. astep.

bato 0xb2be8. astep. if_cases K1; zify_cond K1; rewrite ?signed_lit_small in K1 by lia.
+
bato 0xb2bf8. astep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
*
bato 0xb2c08. astep. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
--

bato 0xb2c34.
rebase_bits A D (ub b 4) rj1 bs1. rewrite <- SZ1 in OBD1.
astep.
call (speex_bits_advance_walk A D (usp + -48) lo (ub b 4)).
all: try eassumption; try lia; try exact (ASH : _ \/ _).
match goal with H : bits_rep bsegs _ A D (speex_bits_advance (ub b 4) _) |- _ => rename H into REP2 end.
match goal with H : stk bsegs _ lo (usp + -48) |- _ => rename H into STK2 end.
bato 0xb2c54. release_frame FR STK2 usp. astep.
apply evt_done. unfold inband_postA, INBAND_DEPTH, BITS_SIZEOF. do 18 eexists.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK2|]. split; [exact FRM|]. split; [exact SW|]. split; [exact LSW|].
unfold inband_bits. cbv zeta. rewrite C9'.
match type of REP2 with bits_rep _ _ _ _ (speex_bits_advance _ ?n) =>
replace (inband_skip_bits (uv b 4)) with n by (unfold inband_skip_bits; decide_ltbs; reflexivity);
split; [exact REP2|]; apply (speex_bits_advance_ok (ub b 4) n OK1); unfold bits_ok, bits_pos in OK1 |- *; lia
end.
--
bato 0xb2c10. astep. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia.
++
bato 0xb2c20. astep. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia.
**

bato 0xb2c34.
rebase_bits A D (ub b 4) rj1 bs1. rewrite <- SZ1 in OBD1.
astep.
call (speex_bits_advance_walk A D (usp + -48) lo (ub b 4)).
all: try eassumption; try lia; try exact (ASH : _ \/ _).
match goal with H : bits_rep bsegs _ A D (speex_bits_advance (ub b 4) _) |- _ => rename H into REP2 end.
match goal with H : stk bsegs _ lo (usp + -48) |- _ => rename H into STK2 end.
bato 0xb2c54. release_frame FR STK2 usp. astep.
apply evt_done. unfold inband_postA, INBAND_DEPTH, BITS_SIZEOF. do 18 eexists.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK2|]. split; [exact FRM|]. split; [exact SW|]. split; [exact LSW|].
unfold inband_bits. cbv zeta. rewrite C9'.
match type of REP2 with bits_rep _ _ _ _ (speex_bits_advance _ ?n) =>
replace (inband_skip_bits (uv b 4)) with n by (unfold inband_skip_bits; decide_ltbs; reflexivity);
split; [exact REP2|]; apply (speex_bits_advance_ok (ub b 4) n OK1); unfold bits_ok, bits_pos in OK1 |- *; lia
end.
**

bato 0xb2c34.
rebase_bits A D (ub b 4) rj1 bs1. rewrite <- SZ1 in OBD1.
astep.
call (speex_bits_advance_walk A D (usp + -48) lo (ub b 4)).
all: try eassumption; try lia; try exact (ASH : _ \/ _).
match goal with H : bits_rep bsegs _ A D (speex_bits_advance (ub b 4) _) |- _ => rename H into REP2 end.
match goal with H : stk bsegs _ lo (usp + -48) |- _ => rename H into STK2 end.
bato 0xb2c54. release_frame FR STK2 usp. astep.
apply evt_done. unfold inband_postA, INBAND_DEPTH, BITS_SIZEOF. do 18 eexists.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK2|]. split; [exact FRM|]. split; [exact SW|]. split; [exact LSW|].
unfold inband_bits. cbv zeta. rewrite C9'.
match type of REP2 with bits_rep _ _ _ _ (speex_bits_advance _ ?n) =>
replace (inband_skip_bits (uv b 4)) with n by (unfold inband_skip_bits; decide_ltbs; reflexivity);
split; [exact REP2|]; apply (speex_bits_advance_ok (ub b 4) n OK1); unfold bits_ok, bits_pos in OK1 |- *; lia
end.
++

bato 0xb2c34.
rebase_bits A D (ub b 4) rj1 bs1. rewrite <- SZ1 in OBD1.
astep.
call (speex_bits_advance_walk A D (usp + -48) lo (ub b 4)).
all: try eassumption; try lia; try exact (ASH : _ \/ _).
match goal with H : bits_rep bsegs _ A D (speex_bits_advance (ub b 4) _) |- _ => rename H into REP2 end.
match goal with H : stk bsegs _ lo (usp + -48) |- _ => rename H into STK2 end.
bato 0xb2c54. release_frame FR STK2 usp. astep.
apply evt_done. unfold inband_postA, INBAND_DEPTH, BITS_SIZEOF. do 18 eexists.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK2|]. split; [exact FRM|]. split; [exact SW|]. split; [exact LSW|].
unfold inband_bits. cbv zeta. rewrite C9'.
match type of REP2 with bits_rep _ _ _ _ (speex_bits_advance _ ?n) =>
replace (inband_skip_bits (uv b 4)) with n by (unfold inband_skip_bits; decide_ltbs; reflexivity);
split; [exact REP2|]; apply (speex_bits_advance_ok (ub b 4) n OK1); unfold bits_ok, bits_pos in OK1 |- *; lia
end.
*

bato 0xb2c34.
rebase_bits A D (ub b 4) rj1 bs1. rewrite <- SZ1 in OBD1.
astep.
call (speex_bits_advance_walk A D (usp + -48) lo (ub b 4)).
all: try eassumption; try lia; try exact (ASH : _ \/ _).
match goal with H : bits_rep bsegs _ A D (speex_bits_advance (ub b 4) _) |- _ => rename H into REP2 end.
match goal with H : stk bsegs _ lo (usp + -48) |- _ => rename H into STK2 end.
bato 0xb2c54. release_frame FR STK2 usp. astep.
apply evt_done. unfold inband_postA, INBAND_DEPTH, BITS_SIZEOF. do 18 eexists.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK2|]. split; [exact FRM|]. split; [exact SW|]. split; [exact LSW|].
unfold inband_bits. cbv zeta. rewrite C9'.
match type of REP2 with bits_rep _ _ _ _ (speex_bits_advance _ ?n) =>
replace (inband_skip_bits (uv b 4)) with n by (unfold inband_skip_bits; decide_ltbs; reflexivity);
split; [exact REP2|]; apply (speex_bits_advance_ok (ub b 4) n OK1); unfold bits_ok, bits_pos in OK1 |- *; lia
end.
+

bato 0xb2c34.
rebase_bits A D (ub b 4) rj1 bs1. rewrite <- SZ1 in OBD1.
astep.
call (speex_bits_advance_walk A D (usp + -48) lo (ub b 4)).
all: try eassumption; try lia; try exact (ASH : _ \/ _).
match goal with H : bits_rep bsegs _ A D (speex_bits_advance (ub b 4) _) |- _ => rename H into REP2 end.
match goal with H : stk bsegs _ lo (usp + -48) |- _ => rename H into STK2 end.
bato 0xb2c54. release_frame FR STK2 usp. astep.
apply evt_done. unfold inband_postA, INBAND_DEPTH, BITS_SIZEOF. do 18 eexists.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK2|]. split; [exact FRM|]. split; [exact SW|]. split; [exact LSW|].
unfold inband_bits. cbv zeta. rewrite C9'.
match type of REP2 with bits_rep _ _ _ _ (speex_bits_advance _ ?n) =>
replace (inband_skip_bits (uv b 4)) with n by (unfold inband_skip_bits; decide_ltbs; reflexivity);
split; [exact REP2|]; apply (speex_bits_advance_ok (ub b 4) n OK1); unfold bits_ok, bits_pos in OK1 |- *; lia
end.
Qed.
End InbandH.

Theorem user_handler_proofA : forall ptr, @user_handler_stmtA ptr.
Proof.
intros ptr A D ST usp lo b ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
REP OK OBA OBD ASH ATOP ALO DLO STK LO LOS SPH CC MI FRM.
eapply user_handler_walk; eassumption.
Qed.
Theorem inband_handler_proofA : forall ptr, @inband_handler_stmtA ptr.
Proof.
intros ptr sc A D CBA ST STEREO usp lo b js sws ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
REP OK CBS Ljs Fjs SW LSW OBA OBD OBC OBS OBT C8a S4 ASH SSH ATOP STOP ALO DLO CLO SLO SEPCA SEPCS SEPSA SEPSD STK LO LOS SPH CC MI FRM CPOS.
eapply inband_handler_walk; eassumption.
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac tlia ::= (try unfold BITS_SIZEOF in * ); tlia_one.
Local Ltac slia ::= (try unfold BITS_SIZEOF in * ); first [ exact I | lia | split; [lia|exact I] ].

Definition exp_postZ (elo eq : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (mm : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra (Z_to_bv 64 eq) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(elo, eq)] mm m' /\ wmono asegs mm m' /\ mem_inv asegs m' /\ frm0 fc' /\ stk asegs m' elo eq.
Lemma exp_specZ : forall (elo eq : Z)
(ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (FF : bvmap 5 word) (fcc : bv 32) (mm : mem),
stk asegs mm elo eq -> elo + 16 <= eq -> 0 <= eq < 2^64 -> mem_inv asegs mm -> frm0 fcc ->
evt asegs (exp_postZ elo eq ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mm)
(MS (mkR ra (Z_to_bv 64 eq) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FF (Z_to_bv 64 X020.A_exp) fcc None mm (seg_rom asegs)).
Proof.
intros until mm. intros XSTK XLO XHq XMI XFRM.
pose proof (X020.exp_proofA elo ra (Z_to_bv 64 eq) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FF fcc mm) as H.
rewrite !unsigned_lit in H by lia. unfold X020.EXP_DEPTH in H. specialize (H XSTK XLO XMI XFRM).
eapply evt_mono; [exact H|]. intros ms' P. unfold X020.exp_postA in P. rewrite !unsigned_lit in P by lia.
destruct P as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & F' & fc' & m' & E & MU & WM & MI' & FRM' & STK' & _).
unfold exp_postZ. do 18 eexists. split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact FRM'| exact STK'].
Qed.

Section UserH.
Context {ptr : Type}.
Variables (A D ST usp lo : Z) (b : bits_st ptr).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable m : mem.
Hypothesis REP : bits_rep asegs m A D b.
Hypothesis OK : bits_ok b.
Hypothesis OBA : aobj asegs m A BITS_SIZEOF.
Hypothesis OBD : aobj asegs m D (sb_buf_size b).
Hypothesis ASH : hidp (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A).
Hypothesis ATOP : IMG_TOP <= A.
Hypothesis ALO : A + BITS_SIZEOF <= lo.
Hypothesis DLO : D + sb_buf_size b <= lo.
Hypothesis LO : lo <= usp - USERH_DEPTH.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Local Notation W := [(A, A + 48); (usp + -48, usp)].

Lemma user_handler_walk : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc,
client_consts m -> stk asegs m lo usp -> mem_inv asegs m -> frm0 fc ->
evt asegs (user_handler_postA A D usp lo b ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 ST) (Z_to_bv 64 0) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_default_user_handler) fc None m (seg_rom asegs)).
Proof.
intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc CC ST0 MI FRM.
pose proof CC as (G1 & G2 & G3 & G4).
unfold A_speex_default_user_handler, USERH_DEPTH, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof REP as ((rj0 & Lrj0 & OBJ) & (bs0 & DAT & Hbs0) & SIDE0). unfold bits_cells in OBJ.
assert (Lbs0 : Z.of_nat (length bs0) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs0, zlength_map_unsigned in OK'. lia. }
pose proof OBA as (OA0 & OA1 & _). pose proof OBD as (OD0 & OD1 & _). unfold APP_TOP, BITS_SIZEOF in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. unfold IMG_TOP in ATOP.
pose proof ST0 as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh W).
{ pose proof (ASH : _ \/ _) as Y1. clear - Y1 LOS LO. cbn. unfold SH_LO, SH_HI in *. lia. }
carve_frame 16%nat ST0.
apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xacee4.
rebase_bits A D b rj0 bs0.
astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -16) lo b 4 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK ltac:(lia) OBA1 OBD1 (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO DLO).
all: try eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
match goal with H : stk asegs _ lo _ |- _ => rename H into STK end.
change (snd (speex_bits_unpack_unsigned b 4)) with (ub b 4) in *. change (fst (speex_bits_unpack_unsigned b 4)) with (uv b 4) in *.
pose proof (ub_ok b 4 OK ltac:(lia)) as (OK1 & SZ1 & V1R). change (2 ^ 4) with 16 in V1R.
clear REP1 OBA1 OBD1 CC1.
match goal with H : bits_rep asegs _ A D (ub b 4) |- _ => destruct H as ((rj1 & Lrj1 & OBJ) & (bs1 & DAT & Hbs1) & SIDE1); unfold bits_cells in OBJ end.
assert (Lbs1 : Z.of_nat (length bs1) = sb_buf_size b).
{ pose proof OK1 as OK'. unfold bits_ok in OK'. rewrite Hbs1, zlength_map_unsigned in OK'. lia. }
ato 0xacef4.
replace (bv_swrap 32 (Z.shiftl (uv b 4) 3) + 5) with (5 + 8 * uv b 4)
by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 3) with 8; rewrite swrap32_small by lia; lia).
rebase_bits A D (ub b 4) rj1 bs1. rewrite <- SZ1 in OBD1.
astep.
call (speex_bits_advance_walk A D (usp + -16) lo (ub b 4) (5 + 8 * uv b 4) _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK1 ltac:(lia) OBA1 (ASH : _ \/ _)).
all: try eassumption; try lia.
match goal with H : bits_rep asegs _ A D (speex_bits_advance (ub b 4) _) |- _ => rename H into REP2 end.
match goal with H : stk asegs _ lo (usp + -16) |- _ => rename H into STK2 end.
pose proof (speex_bits_advance_ok (ub b 4) (5 + 8 * uv b 4) OK1) as AOK.
ato 0xacf08. release_frame FR STK2 usp. astep.
apply evt_done. unfold user_handler_postA, USERH_DEPTH, BITS_SIZEOF. do 17 eexists.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK2|]. split; [exact FRM|].
unfold user_handler_bits. split; [exact REP2|].
apply AOK. unfold bits_ok, bits_pos in OK1 |- *. lia.
Qed.
End UserH.

Section StereoH.
Context {ptr : Type}.
Variables (A D STP STEREO usp lo : Z) (b : bits_st ptr).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable m : mem.
Hypothesis REP : bits_rep asegs m A D b.
Hypothesis OK : bits_ok b.
Hypothesis OBA : aobj asegs m A BITS_SIZEOF.
Hypothesis OBD : aobj asegs m D (sb_buf_size b).
Hypothesis OBS : aobj asegs m STEREO 8.
Hypothesis OBT : aobj asegs m A_e_ratio_quant 16.
Hypothesis S4 : STEREO mod 4 = 0.
Hypothesis ASH : hidp (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A).
Hypothesis SSH : hidp (STEREO + 8 <= SH_LO \/ SH_HI <= STEREO).
Hypothesis ATOP : IMG_TOP <= A.
Hypothesis STOP : IMG_TOP <= STEREO.
Hypothesis ALO : A + BITS_SIZEOF <= lo.
Hypothesis DLO : D + sb_buf_size b <= lo.
Hypothesis SLO : STEREO + 8 <= lo.
Hypothesis SEPSA : hidp (STEREO + 8 <= A \/ A + BITS_SIZEOF <= STEREO).
Hypothesis SEPSD : hidp (STEREO + 8 <= D \/ D + sb_buf_size b <= STEREO).
Hypothesis LO : lo <= usp - STEREOH_DEPTH.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Local Notation W := [(A, A + 48); (STEREO, STEREO + 8); (usp + -80, usp)].

Lemma stereo_handler_walk : forall (sws : list word) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc,
rw_cells asegs m STEREO (f32 sws) -> length sws = 2%nat ->
client_consts m -> stk asegs m lo usp -> mem_inv asegs m -> frm0 fc ->
evt asegs (stereo_handler_postA A D STEREO usp lo b ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 STP) (Z_to_bv 64 STEREO) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_std_stereo_request_handler) fc None m (seg_rom asegs)).
Proof.
intros sws t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc SW LSW CC ST0 MI FRM.
pose proof CC as (G1 & G2 & G3 & G4).
unfold A_speex_std_stereo_request_handler, A_e_ratio_quant, STEREOH_DEPTH, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof REP as ((rj0 & Lrj0 & OBJ) & (bs0 & DAT & Hbs0) & SIDE0). unfold bits_cells in OBJ.
assert (Lbs0 : Z.of_nat (length bs0) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs0, zlength_map_unsigned in OK'. lia. }
pose proof OBA as (OA0 & OA1 & _). pose proof OBD as (OD0 & OD1 & _). pose proof OBS as (OS0 & OS1 & _). unfold APP_TOP, BITS_SIZEOF in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. unfold IMG_TOP in ATOP, STOP.
pose proof ST0 as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh W).
{ pose proof (ASH : _ \/ _) as Y1. pose proof (SSH : _ \/ _) as Y2. clear - Y1 Y2 LOS LO. cbn. unfold SH_LO, SH_HI in *. lia. }
pose proof (SEPSA : _ \/ _) as SEPSA'. pose proof (SEPSD : _ \/ _) as SEPSD'. hide_disj.
destruct sws as [|w0 [|w1 [|]]]; cbn [length] in LSW; try lia. rewrite f32_cons, f32_cons, f32_nil in SW.
carve_frame 48%nat ST0.
apply (rw_cells_split_CB asegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0x98aac.

rebase_bits A D b rj0 bs0.
astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -48) lo b 1 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK ltac:(lia) OBA1 OBD1 (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO DLO).
all: try eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
match goal with H : stk asegs _ lo _ |- _ => rename H into STK end.
change (snd (speex_bits_unpack_unsigned b 1)) with (ub b 1) in *. change (fst (speex_bits_unpack_unsigned b 1)) with (uv b 1) in *.
pose proof (ub_ok b 1 OK ltac:(lia)) as (OK1 & SZ1 & V1R). change (2 ^ 1) with 2 in V1R.
clear REP1 OBA1 OBD1 CC1.
match goal with H : bits_rep asegs _ A D (ub b 1) |- _ => destruct H as ((rj1 & Lrj1 & OBJ) & (bs1 & DAT & Hbs1) & SIDE1); unfold bits_cells in OBJ end.
assert (Lbs1 : Z.of_nat (length bs1) = sb_buf_size b).
{ pose proof OK1 as OK'. unfold bits_ok in OK'. rewrite Hbs1, zlength_map_unsigned in OK'. lia. }

assert (SGN : uv b 1 = 0 \/ uv b 1 = 1) by lia.
destruct SGN as [SG|SG]; rewrite SG.
all: ato 0x98ac4.
all: lazymatch goal with |- context [Z_to_bv 64 (145144 + ?e)] => let v := eval vm_compute in (145144 + e) in change (145144 + e) with v end.
all: ato 0x98ad0.
{

rebase_bits A D (ub b 1) rj1 bs1. rewrite <- SZ1 in OBD1.
astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -48) lo (ub b 1) 5 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK1 ltac:(lia) OBA1 OBD1 (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO ltac:(rewrite SZ1; exact DLO)).
all: try eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
match goal with H : stk asegs _ lo _ |- _ => rename H into STK2 end.
change (snd (speex_bits_unpack_unsigned (ub b 1) 5)) with (ub (ub b 1) 5) in *. change (fst (speex_bits_unpack_unsigned (ub b 1) 5)) with (uv (ub b 1) 5) in *.
pose proof (ub_ok (ub b 1) 5 OK1 ltac:(lia)) as (OK2 & SZ2 & V2R). change (2 ^ 5) with 32 in V2R. rewrite SZ1 in SZ2.
clear REP1 OBA1 OBD1 CC1.
match goal with H : bits_rep asegs _ A D (ub (ub b 1) 5) |- _ => destruct H as ((rj2 & Lrj2 & OBJ) & (bs2 & DAT & Hbs2) & SIDE2); unfold bits_cells in OBJ end.
assert (Lbs2 : Z.of_nat (length bs2) = sb_buf_size b).
{ pose proof OK2 as OK'. unfold bits_ok in OK'. rewrite Hbs2, zlength_map_unsigned in OK'. lia. }

ato 0x98ae0.
destruct (stk_split asegs _ lo (usp + -64) (usp + -48) STK2 ltac:(lia)) as [STKa STKb]. clear STK2.
astep.
call (exp_specZ (usp + -64) (usp + -48)).
1: exact STKb. 1: lia. 1: lia. 1: eassumption. 1: exact FRM.
match goal with H : stk asegs _ (usp + -64) (usp + -48) |- _ => pose proof (stk_merge asegs _ lo (usp + -64) (usp + -48) STKa H ltac:(lia)) as STK3; clear H STKa end.
clear FRM. match goal with H : frm0 _ |- _ => rename H into FRM3 end.

ato 0x98af0. astep. chk_merge OBS 4.
ato 0x98b04.

rebase_bits A D (ub (ub b 1) 5) rj2 bs2. rewrite <- SZ2 in OBD1.
astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -48) lo (ub (ub b 1) 5) 2 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK2 ltac:(lia) OBA1 OBD1 (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO ltac:(rewrite SZ2; exact DLO)).
all: try eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
match goal with H : stk asegs _ lo _ |- _ => rename H into STK4 end.
change (snd (speex_bits_unpack_unsigned (ub (ub b 1) 5) 2)) with (ub (ub (ub b 1) 5) 2) in *.
change (fst (speex_bits_unpack_unsigned (ub (ub b 1) 5) 2)) with (uv (ub (ub b 1) 5) 2) in *.
pose proof (ub_ok (ub (ub b 1) 5) 2 OK2 ltac:(lia)) as (OK3 & SZ3 & V3R). change (2 ^ 2) with 4 in V3R. rewrite SZ2 in SZ3.
clear REP1 OBA1 OBD1 CC1.
match goal with H : bits_rep asegs _ A D (ub (ub (ub b 1) 5) 2) |- _ => destruct H as ((rj3 & Lrj3 & OBJ) & (bs3 & DAT & Hbs3) & SIDE3); unfold bits_cells in OBJ end.
assert (Lbs3 : Z.of_nat (length bs3) = sb_buf_size b).
{ pose proof OK3 as OK'. unfold bits_ok in OK'. rewrite Hbs3, zlength_map_unsigned in OK'. lia. }

assert (V8 : 145184 mod 8 = 0) by reflexivity.
assert (CASES : uv (ub (ub b 1) 5) 2 = 0 \/ uv (ub (ub b 1) 5) 2 = 1 \/ uv (ub (ub b 1) 5) 2 = 2 \/ uv (ub (ub b 1) 5) 2 = 3) by lia.
destruct CASES as [T|[T|[T|T]]]; rewrite T.
all: ato 0x98b14.
all: astep.
all: ato 0x98b3c.
all: astep.
all: chk_merge OBS 4.
all: ato 0x98b60.
all: release_frame FR STK4 usp.
all: astep.
all: apply evt_done; unfold stereo_handler_postA, STEREOH_DEPTH, BITS_SIZEOF; do 17 eexists; eexists [_; _];
split; [reflexivity|];
split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact STK4|]; split; [eassumption|];
split; [rewrite f32_cons, f32_cons, f32_nil; exact SW|]; split; [reflexivity|];
split; [| exact OK3];
(split; [exists rj3; split; [exact Lrj3| unfold bits_cells; exact OBJ]| split; [exists bs3; split; [exact DAT| exact Hbs3]| exact SIDE3]]).
}
{

rebase_bits A D (ub b 1) rj1 bs1. rewrite <- SZ1 in OBD1.
astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -48) lo (ub b 1) 5 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK1 ltac:(lia) OBA1 OBD1 (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO ltac:(rewrite SZ1; exact DLO)).
all: try eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
match goal with H : stk asegs _ lo _ |- _ => rename H into STK2 end.
change (snd (speex_bits_unpack_unsigned (ub b 1) 5)) with (ub (ub b 1) 5) in *. change (fst (speex_bits_unpack_unsigned (ub b 1) 5)) with (uv (ub b 1) 5) in *.
pose proof (ub_ok (ub b 1) 5 OK1 ltac:(lia)) as (OK2 & SZ2 & V2R). change (2 ^ 5) with 32 in V2R. rewrite SZ1 in SZ2.
clear REP1 OBA1 OBD1 CC1.
match goal with H : bits_rep asegs _ A D (ub (ub b 1) 5) |- _ => destruct H as ((rj2 & Lrj2 & OBJ) & (bs2 & DAT & Hbs2) & SIDE2); unfold bits_cells in OBJ end.
assert (Lbs2 : Z.of_nat (length bs2) = sb_buf_size b).
{ pose proof OK2 as OK'. unfold bits_ok in OK'. rewrite Hbs2, zlength_map_unsigned in OK'. lia. }

ato 0x98ae0.
destruct (stk_split asegs _ lo (usp + -64) (usp + -48) STK2 ltac:(lia)) as [STKa STKb]. clear STK2.
astep.
call (exp_specZ (usp + -64) (usp + -48)).
1: exact STKb. 1: lia. 1: lia. 1: eassumption. 1: exact FRM.
match goal with H : stk asegs _ (usp + -64) (usp + -48) |- _ => pose proof (stk_merge asegs _ lo (usp + -64) (usp + -48) STKa H ltac:(lia)) as STK3; clear H STKa end.
clear FRM. match goal with H : frm0 _ |- _ => rename H into FRM3 end.

ato 0x98af0. astep. chk_merge OBS 4.
ato 0x98b04.

rebase_bits A D (ub (ub b 1) 5) rj2 bs2. rewrite <- SZ2 in OBD1.
astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -48) lo (ub (ub b 1) 5) 2 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK2 ltac:(lia) OBA1 OBD1 (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO ltac:(rewrite SZ2; exact DLO)).
all: try eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
match goal with H : stk asegs _ lo _ |- _ => rename H into STK4 end.
change (snd (speex_bits_unpack_unsigned (ub (ub b 1) 5) 2)) with (ub (ub (ub b 1) 5) 2) in *.
change (fst (speex_bits_unpack_unsigned (ub (ub b 1) 5) 2)) with (uv (ub (ub b 1) 5) 2) in *.
pose proof (ub_ok (ub (ub b 1) 5) 2 OK2 ltac:(lia)) as (OK3 & SZ3 & V3R). change (2 ^ 2) with 4 in V3R. rewrite SZ2 in SZ3.
clear REP1 OBA1 OBD1 CC1.
match goal with H : bits_rep asegs _ A D (ub (ub (ub b 1) 5) 2) |- _ => destruct H as ((rj3 & Lrj3 & OBJ) & (bs3 & DAT & Hbs3) & SIDE3); unfold bits_cells in OBJ end.
assert (Lbs3 : Z.of_nat (length bs3) = sb_buf_size b).
{ pose proof OK3 as OK'. unfold bits_ok in OK'. rewrite Hbs3, zlength_map_unsigned in OK'. lia. }

assert (V8 : 145184 mod 8 = 0) by reflexivity.
assert (CASES : uv (ub (ub b 1) 5) 2 = 0 \/ uv (ub (ub b 1) 5) 2 = 1 \/ uv (ub (ub b 1) 5) 2 = 2 \/ uv (ub (ub b 1) 5) 2 = 3) by lia.
destruct CASES as [T|[T|[T|T]]]; rewrite T.
all: ato 0x98b14.
all: astep.
all: ato 0x98b3c.
all: astep.
all: chk_merge OBS 4.
all: ato 0x98b60.
all: release_frame FR STK4 usp.
all: astep.
all: apply evt_done; unfold stereo_handler_postA, STEREOH_DEPTH, BITS_SIZEOF; do 17 eexists; eexists [_; _];
split; [reflexivity|];
split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact STK4|]; split; [eassumption|];
split; [rewrite f32_cons, f32_cons, f32_nil; exact SW|]; split; [reflexivity|];
split; [| exact OK3];
(split; [exists rj3; split; [exact Lrj3| unfold bits_cells; exact OBJ]| split; [exists bs3; split; [exact DAT| exact Hbs3]| exact SIDE3]]).
}
Qed.
End StereoH.

Ltac decide_ltbs :=
repeat match goal with
| |- context [?x <? ?y] =>
first [ replace (x <? y) with true by (symmetry; apply Z.ltb_lt; lia)
| replace (x <? y) with false by (symmetry; apply Z.ltb_ge; lia) ]
end.

Lemma cbs_cells_split : forall k f d sc js n, (n < k)%nat -> (k <= length js)%nat ->
exists pre post,
cbs_cells k f d sc js
= pre ++ (if (16 - Z.of_nat k + Z.of_nat n =? 9) && sc then cb_cells f d (nth n js ([], [])) else cb_cells 0 0 (nth n js ([], [])))
++ post
/\ cells_size pre = (40 * n)%nat.
Proof.
induction k as [|k IH]; intros f d sc js n Hn Hk; [lia|].
destruct js as [|j js']; [cbn in Hk; lia|]. cbn [length] in Hk.
destruct n as [|n'].
- exists [], (cbs_cells k f d sc js'). split; [|reflexivity].
cbn [cbs_cells nth app]. cbv zeta.
replace (16 - Z.of_nat (S k) + Z.of_nat 0) with (16 - Z.of_nat (S k)) by lia. reflexivity.
- destruct (IH f d sc js' n' ltac:(lia) ltac:(lia)) as (pre & post & E & SZ).
exists ((if (16 - Z.of_nat (S k) =? 9) && sc then cb_cells f d j else cb_cells 0 0 j) ++ pre), post.
split.
+ cbn [cbs_cells nth]. cbv zeta. rewrite E.
replace (16 - Z.of_nat k + Z.of_nat n') with (16 - Z.of_nat (S k) + Z.of_nat (S n')) by lia.
rewrite <- app_assoc. reflexivity.
+ rewrite cells_size_app, SZ. destruct ((16 - Z.of_nat (S k) =? 9) && sc); rewrite cb_cells_size; lia.
Qed.

Section InbandH.
Context {ptr : Type}.
Variables (A D CBA STP STEREO usp lo : Z) (b : bits_st ptr) (sc : bool) (js : list (list byte * list byte)).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable m : mem.
Hypothesis REP : bits_rep asegs m A D b.
Hypothesis OK : bits_ok b.
Hypothesis Ljs : length js = 16%nat.
Hypothesis Fjs : Forall (fun p => length (fst p) = 8%nat /\ length (snd p) = 16%nat) js.
Hypothesis OBA : aobj asegs m A BITS_SIZEOF.
Hypothesis OBD : aobj asegs m D (sb_buf_size b).
Hypothesis OBC : aobj asegs m CBA 640.
Hypothesis OBS : aobj asegs m STEREO 8.
Hypothesis OBT : aobj asegs m A_e_ratio_quant 16.
Hypothesis C8a : CBA mod 8 = 0.
Hypothesis S4 : STEREO mod 4 = 0.
Hypothesis ASH : hidp (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A).
Hypothesis SSH : hidp (STEREO + 8 <= SH_LO \/ SH_HI <= STEREO).
Hypothesis ATOP : IMG_TOP <= A.
Hypothesis STOP : IMG_TOP <= STEREO.
Hypothesis ALO : A + BITS_SIZEOF <= lo.
Hypothesis DLO : D + sb_buf_size b <= lo.
Hypothesis CLO : CBA + 640 <= lo.
Hypothesis SLO : STEREO + 8 <= lo.
Hypothesis SEPCA : hidp (CBA + 640 <= A \/ A + BITS_SIZEOF <= CBA).
Hypothesis SEPCS : hidp (CBA + 640 <= STEREO \/ STEREO + 8 <= CBA).
Hypothesis SEPSA : hidp (STEREO + 8 <= A \/ A + BITS_SIZEOF <= STEREO).
Hypothesis SEPSD : hidp (STEREO + 8 <= D \/ D + sb_buf_size b <= STEREO).
Hypothesis LO : lo <= usp - INBAND_DEPTH.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Local Notation W := [(A, A + 48); (STEREO, STEREO + 8); (usp + -80, usp)].

Lemma inband_handler_walk : forall (sws : list word) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc,
rw_cells asegs m CBA (cbs_cells 16 A_speex_std_stereo_request_handler STEREO sc js) ->
rw_cells asegs m STEREO (f32 sws) -> length sws = 2%nat ->
client_consts m -> stk asegs m lo usp -> mem_inv asegs m -> frm0 fc ->
evt asegs (inband_postA sc A D STEREO usp lo b ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 CBA) (Z_to_bv 64 STP) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_inband_handler) fc None m (seg_rom asegs)).
Proof.
intros sws t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc CBS SW LSW CC ST0 MI FRM.
pose proof CC as (G1 & G2 & G3 & G4).
unfold A_speex_inband_handler, INBAND_DEPTH, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof REP as ((rj0 & Lrj0 & OBJ) & (bs0 & DAT & Hbs0) & SIDE0). unfold bits_cells in OBJ.
assert (Lbs0 : Z.of_nat (length bs0) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs0, zlength_map_unsigned in OK'. lia. }
pose proof OBA as (OA0 & OA1 & _). pose proof OBD as (OD0 & OD1 & _). pose proof OBS as (OS0 & OS1 & _). pose proof OBC as (OC0 & OC1 & _). unfold APP_TOP, BITS_SIZEOF in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. unfold IMG_TOP in ATOP, STOP.
pose proof ST0 as (STa & STb & _).

pose proof (proj1 (proj1 CBS)) as WFC.
assert (CBSB : rw_cells asegs m CBA [CB 640 (cells_bytes (cbs_cells 16 A_speex_std_stereo_request_handler STEREO sc js))]).
{ eapply rw_cells_samebytes; [exact CBS| | |].
- cbn [cells_wf cell_wf]. split; [|exact I]. rewrite cells_bytes_length by exact WFC. rewrite cbs_cells_size by lia. reflexivity.
- cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
- cbn [cells_size csize]. rewrite cbs_cells_size by lia. reflexivity. }
clear CBS.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh W).
{ pose proof (ASH : _ \/ _) as Y1. pose proof (SSH : _ \/ _) as Y2. clear - Y1 Y2 LOS LO. cbn. unfold SH_LO, SH_HI in *. lia. }
pose proof (SEPSA : _ \/ _) as SEPSA'. pose proof (SEPSD : _ \/ _) as SEPSD'. pose proof (SEPCA : _ \/ _) as SEPCA'. pose proof (SEPCS : _ \/ _) as SEPCS'. hide_disj.
carve_frame 48%nat ST0.
apply (rw_cells_split_CB asegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xacde8.

rebase_bits A D b rj0 bs0.
astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -48) lo b 4 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK ltac:(lia) OBA1 OBD1 (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO DLO).
all: try eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
match goal with H : stk asegs _ lo _ |- _ => rename H into STK end.
change (snd (speex_bits_unpack_unsigned b 4)) with (ub b 4) in *. change (fst (speex_bits_unpack_unsigned b 4)) with (uv b 4) in *.
pose proof (ub_ok b 4 OK ltac:(lia)) as (OK1 & SZ1 & V1R). change (2 ^ 4) with 16 in V1R.
clear REP1 OBA1 OBD1 CC1.
match goal with H : bits_rep asegs _ A D (ub b 4) |- _ => destruct H as ((rj1 & Lrj1 & OBJ) & (bs1 & DAT & Hbs1) & SIDE1); unfold bits_cells in OBJ end.
assert (Lbs1 : Z.of_nat (length bs1) = sb_buf_size b).
{ pose proof OK1 as OK'. unfold bits_ok in OK'. rewrite Hbs1, zlength_map_unsigned in OK'. lia. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (CBS : rw_cells asegs mc CBA (cbs_cells 16 A_speex_std_stereo_request_handler STEREO sc js)) end.
{ eapply rw_cells_samebytes; [exact CBSB| exact WFC| |].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
- cbn [cells_size csize]. rewrite cbs_cells_size by lia. reflexivity. }
clear CBSB.
destruct (cbs_cells_split 16 A_speex_std_stereo_request_handler STEREO sc js (Z.to_nat (uv b 4)) ltac:(lia) ltac:(lia)) as (pre & post & E & SZ).
rewrite E in CBS. apply rw_cells_app in CBS. destruct CBS as [PRE CBS]. apply rw_cells_app in CBS. destruct CBS as [ENT POST].
rewrite SZ in ENT.
replace (16 - Z.of_nat 16 + Z.of_nat (Z.to_nat (uv b 4))) with (uv b 4) in ENT by lia.
replace (CBA + Z.of_nat (40 * Z.to_nat (uv b 4))) with (CBA + uv b 4 * 40) in ENT by lia.
clear PRE POST E SZ.
ato 0xace08.
astep.
rewrite (shb_zero asegs m CBA 640 (CBA + uv b 4 * 40 + 8) (proj2 (proj2 OBC)) ltac:(lia) ltac:(clear - C8a V1R; Z.div_mod_to_equations; lia)).
lit_if.
destruct ((uv b 4 =? 9) && sc) eqn:C9.
-
apply andb_prop in C9. destruct C9 as [C9a C9b]. apply Z.eqb_eq in C9a.
unfold cb_cells in ENT. unfold A_speex_std_stereo_request_handler in ENT.
ato 0xace10. astep.
ato 0xace24. astep.
rewrite (shb_zero asegs m CBA 640 (CBA + uv b 4 * 40 + 16) (proj2 (proj2 OBC)) ltac:(lia) ltac:(clear - C8a V1R; Z.div_mod_to_equations; lia)).
lit_if.
ato 0xace4c.
release_frame FR STK usp. astep.
rebase_bits A D (ub b 4) rj1 bs1. rewrite <- SZ1 in OBD1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch asegs _ m mc STEREO 8 OBS MU (shfree_of_aobj asegs _ m STEREO 8 OF OBS)) as OBS1;
pose proof (aobj_munch asegs _ m mc A_e_ratio_quant 16 OBT MU (shfree_of_aobj asegs _ m A_e_ratio_quant 16 OF OBT)) as OBT1
end.
eapply evt_mono.
+ eapply (stereo_handler_walk A D STP STEREO usp lo (ub b 4) ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ REP1 OK1 OBA1 OBD1 OBS1 OBT1 S4 ASH SSH
ltac:(unfold IMG_TOP; lia) ltac:(unfold IMG_TOP; lia) ALO ltac:(rewrite SZ1; exact DLO) SLO SEPSA ltac:(rewrite SZ1; exact SEPSD)
ltac:(unfold STEREOH_DEPTH; lia) LOS SPH sws); try eassumption.
+ cbv beta. intros ms' (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F' & fc' & m' & sws' & -> & MU2 & WM2 & MI2 & STK2 & FRM2 & SW2 & LSW2 & REP2 & OK2).
unfold inband_postA, INBAND_DEPTH, STEREOH_DEPTH, BITS_SIZEOF in *. do 18 eexists.
split; [reflexivity|].
split; [eapply munch_trans; [exact MU| exact MU2]|]. split; [eapply wmono_trans; [exact WM| exact WM2]|].
split; [exact MI2|]. split; [exact STK2|]. split; [exact FRM2|]. split; [exact SW2|]. split; [exact LSW2|].
unfold inband_bits. cbv zeta. unfold SPEEX_INBAND_STEREO. rewrite C9b, C9a. cbn [Z.eqb andb Pos.eqb].
split; [exact REP2| exact OK2].
-
assert (C9' : sc && (uv b 4 =? SPEEX_INBAND_STEREO) = false) by (unfold SPEEX_INBAND_STEREO; rewrite andb_comm; exact C9).
unfold cb_cells in ENT.
ato 0xace10. astep.

ato 0xace54. astep. if_cases K1; zify_cond K1; rewrite ?signed_lit_small in K1 by lia.
+
ato 0xace64. astep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
*
ato 0xace74. astep. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
--

ato 0xacea0.
rebase_bits A D (ub b 4) rj1 bs1. rewrite <- SZ1 in OBD1.
astep.
call (speex_bits_advance_walk A D (usp + -48) lo (ub b 4)).
all: try eassumption; try lia; try exact (ASH : _ \/ _).
match goal with H : bits_rep asegs _ A D (speex_bits_advance (ub b 4) _) |- _ => rename H into REP2 end.
match goal with H : stk asegs _ lo (usp + -48) |- _ => rename H into STK2 end.
ato 0xacec0. release_frame FR STK2 usp. astep.
apply evt_done. unfold inband_postA, INBAND_DEPTH, BITS_SIZEOF. do 18 eexists.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK2|]. split; [exact FRM|]. split; [exact SW|]. split; [exact LSW|].
unfold inband_bits. cbv zeta. rewrite C9'.
match type of REP2 with bits_rep _ _ _ _ (speex_bits_advance _ ?n) =>
replace (inband_skip_bits (uv b 4)) with n by (unfold inband_skip_bits; decide_ltbs; reflexivity);
split; [exact REP2|]; apply (speex_bits_advance_ok (ub b 4) n OK1); unfold bits_ok, bits_pos in OK1 |- *; lia
end.
--
ato 0xace7c. astep. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia.
++
ato 0xace8c. astep. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia.
**

ato 0xacea0.
rebase_bits A D (ub b 4) rj1 bs1. rewrite <- SZ1 in OBD1.
astep.
call (speex_bits_advance_walk A D (usp + -48) lo (ub b 4)).
all: try eassumption; try lia; try exact (ASH : _ \/ _).
match goal with H : bits_rep asegs _ A D (speex_bits_advance (ub b 4) _) |- _ => rename H into REP2 end.
match goal with H : stk asegs _ lo (usp + -48) |- _ => rename H into STK2 end.
ato 0xacec0. release_frame FR STK2 usp. astep.
apply evt_done. unfold inband_postA, INBAND_DEPTH, BITS_SIZEOF. do 18 eexists.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK2|]. split; [exact FRM|]. split; [exact SW|]. split; [exact LSW|].
unfold inband_bits. cbv zeta. rewrite C9'.
match type of REP2 with bits_rep _ _ _ _ (speex_bits_advance _ ?n) =>
replace (inband_skip_bits (uv b 4)) with n by (unfold inband_skip_bits; decide_ltbs; reflexivity);
split; [exact REP2|]; apply (speex_bits_advance_ok (ub b 4) n OK1); unfold bits_ok, bits_pos in OK1 |- *; lia
end.
**

ato 0xacea0.
rebase_bits A D (ub b 4) rj1 bs1. rewrite <- SZ1 in OBD1.
astep.
call (speex_bits_advance_walk A D (usp + -48) lo (ub b 4)).
all: try eassumption; try lia; try exact (ASH : _ \/ _).
match goal with H : bits_rep asegs _ A D (speex_bits_advance (ub b 4) _) |- _ => rename H into REP2 end.
match goal with H : stk asegs _ lo (usp + -48) |- _ => rename H into STK2 end.
ato 0xacec0. release_frame FR STK2 usp. astep.
apply evt_done. unfold inband_postA, INBAND_DEPTH, BITS_SIZEOF. do 18 eexists.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK2|]. split; [exact FRM|]. split; [exact SW|]. split; [exact LSW|].
unfold inband_bits. cbv zeta. rewrite C9'.
match type of REP2 with bits_rep _ _ _ _ (speex_bits_advance _ ?n) =>
replace (inband_skip_bits (uv b 4)) with n by (unfold inband_skip_bits; decide_ltbs; reflexivity);
split; [exact REP2|]; apply (speex_bits_advance_ok (ub b 4) n OK1); unfold bits_ok, bits_pos in OK1 |- *; lia
end.
++

ato 0xacea0.
rebase_bits A D (ub b 4) rj1 bs1. rewrite <- SZ1 in OBD1.
astep.
call (speex_bits_advance_walk A D (usp + -48) lo (ub b 4)).
all: try eassumption; try lia; try exact (ASH : _ \/ _).
match goal with H : bits_rep asegs _ A D (speex_bits_advance (ub b 4) _) |- _ => rename H into REP2 end.
match goal with H : stk asegs _ lo (usp + -48) |- _ => rename H into STK2 end.
ato 0xacec0. release_frame FR STK2 usp. astep.
apply evt_done. unfold inband_postA, INBAND_DEPTH, BITS_SIZEOF. do 18 eexists.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK2|]. split; [exact FRM|]. split; [exact SW|]. split; [exact LSW|].
unfold inband_bits. cbv zeta. rewrite C9'.
match type of REP2 with bits_rep _ _ _ _ (speex_bits_advance _ ?n) =>
replace (inband_skip_bits (uv b 4)) with n by (unfold inband_skip_bits; decide_ltbs; reflexivity);
split; [exact REP2|]; apply (speex_bits_advance_ok (ub b 4) n OK1); unfold bits_ok, bits_pos in OK1 |- *; lia
end.
*

ato 0xacea0.
rebase_bits A D (ub b 4) rj1 bs1. rewrite <- SZ1 in OBD1.
astep.
call (speex_bits_advance_walk A D (usp + -48) lo (ub b 4)).
all: try eassumption; try lia; try exact (ASH : _ \/ _).
match goal with H : bits_rep asegs _ A D (speex_bits_advance (ub b 4) _) |- _ => rename H into REP2 end.
match goal with H : stk asegs _ lo (usp + -48) |- _ => rename H into STK2 end.
ato 0xacec0. release_frame FR STK2 usp. astep.
apply evt_done. unfold inband_postA, INBAND_DEPTH, BITS_SIZEOF. do 18 eexists.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK2|]. split; [exact FRM|]. split; [exact SW|]. split; [exact LSW|].
unfold inband_bits. cbv zeta. rewrite C9'.
match type of REP2 with bits_rep _ _ _ _ (speex_bits_advance _ ?n) =>
replace (inband_skip_bits (uv b 4)) with n by (unfold inband_skip_bits; decide_ltbs; reflexivity);
split; [exact REP2|]; apply (speex_bits_advance_ok (ub b 4) n OK1); unfold bits_ok, bits_pos in OK1 |- *; lia
end.
+

ato 0xacea0.
rebase_bits A D (ub b 4) rj1 bs1. rewrite <- SZ1 in OBD1.
astep.
call (speex_bits_advance_walk A D (usp + -48) lo (ub b 4)).
all: try eassumption; try lia; try exact (ASH : _ \/ _).
match goal with H : bits_rep asegs _ A D (speex_bits_advance (ub b 4) _) |- _ => rename H into REP2 end.
match goal with H : stk asegs _ lo (usp + -48) |- _ => rename H into STK2 end.
ato 0xacec0. release_frame FR STK2 usp. astep.
apply evt_done. unfold inband_postA, INBAND_DEPTH, BITS_SIZEOF. do 18 eexists.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK2|]. split; [exact FRM|]. split; [exact SW|]. split; [exact LSW|].
unfold inband_bits. cbv zeta. rewrite C9'.
match type of REP2 with bits_rep _ _ _ _ (speex_bits_advance _ ?n) =>
replace (inband_skip_bits (uv b 4)) with n by (unfold inband_skip_bits; decide_ltbs; reflexivity);
split; [exact REP2|]; apply (speex_bits_advance_ok (ub b 4) n OK1); unfold bits_ok, bits_pos in OK1 |- *; lia
end.
Qed.
End InbandH.

Theorem user_handler_proofA : forall ptr, @user_handler_stmtA ptr.
Proof.
intros ptr A D ST usp lo b ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
REP OK OBA OBD ASH ATOP ALO DLO STK LO LOS SPH CC MI FRM.
eapply user_handler_walk; eassumption.
Qed.
Theorem inband_handler_proofA : forall ptr, @inband_handler_stmtA ptr.
Proof.
intros ptr sc A D CBA ST STEREO usp lo b js sws ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
REP OK CBS Ljs Fjs SW LSW OBA OBD OBC OBS OBT C8a S4 ASH SSH ATOP STOP ALO DLO CLO SLO SEPCA SEPCS SEPSA SEPSD STK LO LOS SPH CC MI FRM.
eapply inband_handler_walk; eassumption.
Qed.
