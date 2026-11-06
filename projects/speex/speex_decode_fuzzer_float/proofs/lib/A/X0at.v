(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X089 X0ap X0as.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation mem := (word -> option byte).

Lemma land_m32_16 : forall x, 16 <= x < 2^64 -> x mod 32 = 16 -> Z.land x 18446744073709551584 = x - 16.
Proof.
intros x Hx H. change 18446744073709551584 with (Z.ldiff (Z.ones 64) (Z.ones 5)).
rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
change (2^5) with 32. Z.div_mod_to_equations. lia.
Qed.

Definition qmf_frame16 (top x1 x2 g0 : word) (j0 j1 j2 j3 j4 : list byte) (c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) : list cell :=
[CB 8 j0; C8 x1; C8 x2; C8 g0; C8 top; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; C8 c11; C8 c10; C8 c9; C8 c8; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra].

Definition qmf_w1_16_stmt (N VS H S8 X1o : Z) : Prop :=
forall (Y G0 G1 usp lo : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
stk asegs m lo usp -> lo <= usp - 5744 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 16 ->
client_consts m -> mem_inv asegs m ->
evt asegs (fun ms' => exists (j0 j1 j2 j3 j4 jh : list byte) (m1 : mem),
ms' = MS (mkR (Z_to_bv 64 RA_qmf_pois1) (Z_to_bv 64 (usp + S8)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -176))
(Z_to_bv 64 (usp + X1o)) (Z_to_bv 64 VS) (Z_to_bv 64 68719476720) (Z_to_bv 64 0) (Z_to_bv 64 N) (Z_to_bv 64 64) (Z_to_bv 64 G0) (Z_to_bv 64 G1)
(Z_to_bv 64 H) (Z_to_bv 64 (usp + X1o)) (Z_to_bv 64 32) (Z_to_bv 64 (N / 2)) (Z_to_bv 64 Y) (Z_to_bv 64 A_H0) (Z_to_bv 64 (usp + S8)) (Z_to_bv 64 G1)
(Z_to_bv 64 VS) (Z_to_bv 64 SHB) t3 t4 t5 t6)
F (Z_to_bv 64 e_alloca_poison) fc None m1 (seg_rom asegs)
/\ munch [(usp + -4272, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + S8)
/\ rw_cells asegs m1 (usp + -176) (qmf_frame16 (Z_to_bv 64 0) (Z_to_bv 64 Y) (Z_to_bv 64 (Y + 2 * N)) (Z_to_bv 64 G0) j0 j1 j2 j3 j4 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
/\ rw_cells asegs m1 (usp + S8) [CB (Z.to_nat H) jh])
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Y) (Z_to_bv 64 (Y + 2 * N)) (Z_to_bv 64 A_H0) (Z_to_bv 64 Y) (Z_to_bv 64 N) (Z_to_bv 64 64)
(Z_to_bv 64 G0) (Z_to_bv 64 G1) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_qmf_synth) fc None m (seg_rom asegs)).

Definition qmf_w2_16_stmt (N VS H S8 X1o S8b X2o PR2 : Z) : Prop :=
forall (Y G0 G1 usp lo : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j0 j1 j2 j3 j4 : list byte) (c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells asegs m (usp + -176) (qmf_frame16 (Z_to_bv 64 0) (Z_to_bv 64 Y) (Z_to_bv 64 (Y + 2 * N)) (Z_to_bv 64 G0) j0 j1 j2 j3 j4 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
stk asegs m lo (usp + S8) -> lo <= usp - 5744 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 16 -> mem_inv asegs m ->
evt asegs (fun ms' => exists (jh : list byte) (m1 : mem),
ms' = MS (mkR (Z_to_bv 64 RA_qmf_pois2) (Z_to_bv 64 (usp + S8b)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -176))
(Z_to_bv 64 (usp + X2o)) (Z_to_bv 64 VS) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (usp + X2o)) (Z_to_bv 64 (usp + X1o)) (Z_to_bv 64 32) (Z_to_bv 64 (N / 2)) (Z_to_bv 64 Y) (Z_to_bv 64 A_H0) (Z_to_bv 64 (usp + S8b)) (Z_to_bv 64 G1)
(Z_to_bv 64 VS) (Z_to_bv 64 SHB) t3 t4 t5 t6)
F (Z_to_bv 64 e_alloca_poison) fc None m1 (seg_rom asegs)
/\ munch [(usp + PR2, usp + S8); (usp + -144, usp + -136)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + S8b)
/\ rw_cells asegs m1 (usp + -176) (qmf_frame16 (Z_to_bv 64 (usp + S8)) (Z_to_bv 64 Y) (Z_to_bv 64 (Y + 2 * N)) (Z_to_bv 64 G0) j0 j1 j2 j3 j4 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra)
/\ rw_cells asegs m1 (usp + S8b) [CB (Z.to_nat H) jh])
(MS (mkR (Z_to_bv 64 RA_qmf_pois1) (Z_to_bv 64 (usp + S8)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -176)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 H) (Z_to_bv 64 (usp + X1o)) (Z_to_bv 64 32) (Z_to_bv 64 (N / 2)) (Z_to_bv 64 Y) (Z_to_bv 64 A_H0) (Z_to_bv 64 (usp + S8)) (Z_to_bv 64 G1)
(Z_to_bv 64 VS) (Z_to_bv 64 SHB) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_qmf_pois1)) fc None m (seg_rom asegs)).

Lemma qmf_w5_16 : forall (usp lo top : Z) (gp tp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 sp x1 x2 g0 : word)
(j0 j1 j2 j3 j4 : list byte) (c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells asegs m (usp + -176) (qmf_frame16 (Z_to_bv 64 top) x1 x2 g0 j0 j1 j2 j3 j4 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
lo <= usp - 5744 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m ->
evt asegs (fun ms' =>
ms' = MS (mkR (Z_to_bv 64 RA_qmf_unpois) sp gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -176))
(Z_to_bv 64 top) (Z_to_bv 64 (usp + -144)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_allocas_unpoison) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -176)) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_qmf_epi) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FR LO LOS SPH MI.
unfold RA_qmf_unpois, A_qmf_epi, e_allocas_unpoison, qmf_frame16 in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
ato 0x51e64. apply evt_done. reflexivity.
Qed.

Definition qmf_w6_16_stmt (H S8 S8b : Z) : Prop :=
forall (usp lo : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 sp top x1 x2 g0 : word)
(j0 j1 j2 j3 j4 jh1 jh2 : list byte) (c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells asegs m (usp + -176) (qmf_frame16 top x1 x2 g0 j0 j1 j2 j3 j4 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
rw_cells asegs m (usp + S8) [CB (Z.to_nat H) jh1] -> rw_cells asegs m (usp + S8b) [CB (Z.to_nat H) jh2] ->
stk asegs m lo (usp + S8b) ->
lo <= usp - 5744 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m ->
evt asegs (fun ms' =>
ms' = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 a0 a1 a2 a3 a4 a5 a6 a7 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 t3 t4 t5 t6)
F (ret_pc cra) fc None m (seg_rom asegs)
/\ stk asegs m lo usp)
(MS (mkR (Z_to_bv 64 RA_qmf_unpois) sp gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -176)) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_qmf_unpois)) fc None m (seg_rom asegs)).

Lemma qmf_w1_16_320 : qmf_w1_16_stmt 320 768 832 (-1008) (-976).
Proof.
unfold qmf_w1_16_stmt.
intros Y G0 G1 usp lo ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ST LO LOS SPH U32 (G1c & G2c & _) MI.
unfold A_qmf_synth, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -4272, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -4272, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 176%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 176 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
replace (usp + -176 + 8 + 8) with (usp + -160) in * by lia.
ato 0xa4b98. astep.
rewrite (land_m32_16 (usp + -160)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
replace (usp + -160 - 16) with (usp + -176) by lia.
carve_frame 832%nat ST. rename FR0 into HULL1.
carve_frame 3256%nat ST. rename FR0 into JK1.
carve_frame 8%nat ST. rename FR0 into P1.
apply (rw_cells_split_CB asegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
ato 0xa4c10. alits. astep.
replace (usp + -176 - 832) with (usp + -1008) by lia. rewrite ?Z.mod_small by lia.
astep. rewrite (land_m32_al (usp + -1008)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. astep. replace (usp + -176 - 4096) with (usp + -4272) by lia.
astep. astep. sh_if.
ato 0x51d38.
release_frame P1 ST (usp + -4264). release_frame JK1 ST (usp + -1008).
apply evt_done. unfold qmf_frame16, RA_qmf_pois1, e_alloca_poison. do 7 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR| exact HULL1].
Qed.

Lemma qmf_w2_16_320 : qmf_w2_16_stmt 320 768 832 (-1008) (-976) (-1840) (-1808) (-5104).
Proof.
unfold qmf_w2_16_stmt. intros until m. intros FR ST LO LOS SPH U32 MI.
unfold RA_qmf_pois1, RA_qmf_pois2, e_alloca_poison, qmf_frame16 in *.
replace (ret_pc (Z_to_bv 64 0xa4c3c)) with (Z_to_bv 64 0xa4c3c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -5104, usp + -1008); (usp + -144, usp + -136)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -5104, usp + -1008); (usp + -144, usp + -136)]) by (cbn; unfold SH_LO, SH_HI; lia).
astep.
carve_frame 832%nat ST. rename FR0 into HULL2.
carve_frame 3256%nat ST. rename FR0 into JK1.
carve_frame 8%nat ST. rename FR0 into P1.
apply (rw_cells_split_CB asegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
astep. replace (usp + -1008 - 832) with (usp + -1840) by lia. rewrite ?Z.mod_small by lia.
astep. rewrite (land_m32_al (usp + -1840)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. astep. replace (usp + -1008 - 4096) with (usp + -5104) by lia.
astep. astep. sh_if.
ato 0x51d38.
release_frame P1 ST (usp + -5096). release_frame JK1 ST (usp + -1840).
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR| exact HULL2].
Qed.

Lemma qmf_w6_16_320 : qmf_w6_16_stmt 832 (-1008) (-1840).
Proof.
unfold qmf_w6_16_stmt. intros until m. intros FR H1 H2 ST LO LOS SPH MI.
unfold RA_qmf_unpois, qmf_frame16 in *. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in H1, H2.
replace (ret_pc (Z_to_bv 64 0xa52c0)) with (Z_to_bv 64 0xa52c0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
ato 0xa52f8. astep.
release_frame H2 ST (usp + -1008). release_frame H1 ST (usp + -176). release_frame FR ST usp.
astep. apply evt_done. split; [reflexivity| exact ST].
Qed.

Lemma qmf_w1_16_640 : qmf_w1_16_stmt 640 1408 1472 (-1648) (-1616).
Proof.
unfold qmf_w1_16_stmt.
intros Y G0 G1 usp lo ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ST LO LOS SPH U32 (G1c & G2c & _) MI.
unfold A_qmf_synth, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -4272, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -4272, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 176%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 176 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
replace (usp + -176 + 8 + 8) with (usp + -160) in * by lia.
ato 0xa4b98. astep.
rewrite (land_m32_16 (usp + -160)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
replace (usp + -160 - 16) with (usp + -176) by lia.
carve_frame 1472%nat ST. rename FR0 into HULL1.
carve_frame 2616%nat ST. rename FR0 into JK1.
carve_frame 8%nat ST. rename FR0 into P1.
apply (rw_cells_split_CB asegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
ato 0xa4c10. alits. astep.
replace (usp + -176 - 1472) with (usp + -1648) by lia. rewrite ?Z.mod_small by lia.
astep. rewrite (land_m32_al (usp + -1648)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. astep. replace (usp + -176 - 4096) with (usp + -4272) by lia.
astep. astep. sh_if.
ato 0x51d38.
release_frame P1 ST (usp + -4264). release_frame JK1 ST (usp + -1648).
apply evt_done. unfold qmf_frame16, RA_qmf_pois1, e_alloca_poison. do 7 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR| exact HULL1].
Qed.

Lemma qmf_w2_16_640 : qmf_w2_16_stmt 640 1408 1472 (-1648) (-1616) (-3120) (-3088) (-5744).
Proof.
unfold qmf_w2_16_stmt. intros until m. intros FR ST LO LOS SPH U32 MI.
unfold RA_qmf_pois1, RA_qmf_pois2, e_alloca_poison, qmf_frame16 in *.
replace (ret_pc (Z_to_bv 64 0xa4c3c)) with (Z_to_bv 64 0xa4c3c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -5744, usp + -1648); (usp + -144, usp + -136)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -5744, usp + -1648); (usp + -144, usp + -136)]) by (cbn; unfold SH_LO, SH_HI; lia).
astep.
carve_frame 1472%nat ST. rename FR0 into HULL2.
carve_frame 2616%nat ST. rename FR0 into JK1.
carve_frame 8%nat ST. rename FR0 into P1.
apply (rw_cells_split_CB asegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
astep. replace (usp + -1648 - 1472) with (usp + -3120) by lia. rewrite ?Z.mod_small by lia.
astep. rewrite (land_m32_al (usp + -3120)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. astep. replace (usp + -1648 - 4096) with (usp + -5744) by lia.
astep. astep. sh_if.
ato 0x51d38.
release_frame P1 ST (usp + -5736). release_frame JK1 ST (usp + -3120).
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR| exact HULL2].
Qed.

Lemma qmf_w6_16_640 : qmf_w6_16_stmt 1472 (-1648) (-3120).
Proof.
unfold qmf_w6_16_stmt. intros until m. intros FR H1 H2 ST LO LOS SPH MI.
unfold RA_qmf_unpois, qmf_frame16 in *. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in H1, H2.
replace (ret_pc (Z_to_bv 64 0xa52c0)) with (Z_to_bv 64 0xa52c0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
ato 0xa52f8. astep.
release_frame H2 ST (usp + -1648). release_frame H1 ST (usp + -176). release_frame FR ST usp.
astep. apply evt_done. split; [reflexivity| exact ST].
Qed.
