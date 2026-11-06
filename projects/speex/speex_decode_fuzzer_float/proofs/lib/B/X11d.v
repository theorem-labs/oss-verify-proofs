(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05q X05l.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0z5 X12a.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation mem := (word -> option byte).

Definition A_qmf_synth : Z := 0xa8508.
Definition RA_qmf_pois1 : Z := 0xa85e8.
Definition RA_qmf_pois2 : Z := 0xa8618.
Definition A_qmf_epi : Z := 0xa8eb8.
Definition RA_qmf_unpois : Z := 0xa8ec4.
Definition A_H0 : Z := 0x27000.

Definition qmf_frameB (k0 k8 k16 : cell) (vs g1 g0 y m2 top : word) (j72 j80 j88 j96 : list byte) (c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) : list cell :=
[k0; k8; k16; C8 vs; C8 g1; C8 g0; C8 y; C8 m2; C8 top; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96;
C8 c11; C8 c10; C8 c9; C8 c8; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra].

Definition qmf_w1B_stmt (N VS H S4 X1o : Z) : Prop :=
forall (Y G0 G1 usp lo : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
stk bsegs m lo usp -> lo <= usp - 5776 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 16 ->
client_constsB m -> mem_inv bsegs m ->
evt bsegs (fun ms' => exists (j0 j1 j72 j80 j88 j96 jh : list byte) (m1 : mem),
ms' = MS (mkR (Z_to_bv 64 RA_qmf_pois1) (Z_to_bv 64 (usp + S4)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -208))
(Z_to_bv 64 (usp + X1o)) (Z_to_bv 64 VS) (Z_to_bv 64 0) (Z_to_bv 64 VS) (Z_to_bv 64 N) (Z_to_bv 64 32) (Z_to_bv 64 G0) (Z_to_bv 64 G1)
(Z_to_bv 64 (N / 2)) (Z_to_bv 64 (32 + N / 2)) (Z_to_bv 64 (usp + S4)) (Z_to_bv 64 (usp + X1o)) (Z_to_bv 64 H) s7 (Z_to_bv 64 A_H0)
(Z_to_bv 64 (Y + 2 * N)) (Z_to_bv 64 Y) (Z_to_bv 64 SHB) t3 t4 t5 t6)
F (Z_to_bv 64 e_alloca_poison) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -4304, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + S4)
/\ rw_cells bsegs m1 (usp + -208) (qmf_frameB (CB 8 j0) (CB 8 j1) (C8 (Z_to_bv 64 0)) (Z_to_bv 64 VS) (Z_to_bv 64 G1) (Z_to_bv 64 G0) (Z_to_bv 64 Y) (Z_to_bv 64 32)
(Z_to_bv 64 0) j72 j80 j88 j96 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
/\ rw_cells bsegs m1 (usp + S4) [CB (Z.to_nat H) jh])
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Y) (Z_to_bv 64 (Y + 2 * N)) (Z_to_bv 64 A_H0) (Z_to_bv 64 Y) (Z_to_bv 64 N) (Z_to_bv 64 64)
(Z_to_bv 64 G0) (Z_to_bv 64 G1) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_qmf_synth) fc None m (seg_rom bsegs)).

Lemma qmf_w1B_320 : qmf_w1B_stmt 320 768 832 (-1040) (-1008).
Proof.
unfold qmf_w1B_stmt.
intros until m. intros ST LO LOS SPH U32 (G1c & G2c & _) MI.
unfold A_qmf_synth, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -4304, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -4304, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 208%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 208 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xa8548. astep. rewrite (land_m32_16 (usp + -192)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
replace (usp + -192 - 16) with (usp + -208) by lia.
bato 0xa85bc.
carve_frame 832%nat ST. rename FR0 into HULL1.
carve_frame 3256%nat ST. rename FR0 into JK1.
carve_frame 8%nat ST. rename FR0 into P1.
apply (rw_cells_split_CB bsegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
alits. astep. replace (usp + -208 - 832) with (usp + -1040) by lia. rewrite ?Z.mod_small by lia.
astep. rewrite (land_m32_al (usp + -1040)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. astep. replace (usp + -208 - 4096) with (usp + -4304) by lia.
astep. astep. sh_if.
ato 0x51e24.
release_frame P1 ST (usp + -4296). release_frame JK1 ST (usp + -1040).
apply evt_done. unfold qmf_frameB, RA_qmf_pois1, e_alloca_poison. do 8 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR| exact HULL1].
Qed.

Lemma qmf_w1B_640 : qmf_w1B_stmt 640 1408 1472 (-1680) (-1648).
Proof.
unfold qmf_w1B_stmt.
intros until m. intros ST LO LOS SPH U32 (G1c & G2c & _) MI.
unfold A_qmf_synth, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -4304, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -4304, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 208%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 208 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xa8548. astep. rewrite (land_m32_16 (usp + -192)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
replace (usp + -192 - 16) with (usp + -208) by lia.
bato 0xa85bc.
carve_frame 1472%nat ST. rename FR0 into HULL1.
carve_frame 2616%nat ST. rename FR0 into JK1.
carve_frame 8%nat ST. rename FR0 into P1.
apply (rw_cells_split_CB bsegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
alits. astep. replace (usp + -208 - 1472) with (usp + -1680) by lia. rewrite ?Z.mod_small by lia.
astep. rewrite (land_m32_al (usp + -1680)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. astep. replace (usp + -208 - 4096) with (usp + -4304) by lia.
astep. astep. sh_if.
ato 0x51e24.
release_frame P1 ST (usp + -4296). release_frame JK1 ST (usp + -1680).
apply evt_done. unfold qmf_frameB, RA_qmf_pois1, e_alloca_poison. do 8 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR| exact HULL1].
Qed.

Definition qmf_w2B_stmt (N VS H S4 X1o S4b X2o PR2 : Z) : Prop :=
forall (Y G0 G1 usp lo : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word) (j0 j1 j72 j80 j88 j96 : list byte)
(c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells bsegs m (usp + -208) (qmf_frameB (CB 8 j0) (CB 8 j1) (C8 (Z_to_bv 64 0)) (Z_to_bv 64 VS) (Z_to_bv 64 G1) (Z_to_bv 64 G0) (Z_to_bv 64 Y) (Z_to_bv 64 32)
(Z_to_bv 64 0) j72 j80 j88 j96 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
stk bsegs m lo (usp + S4) -> lo <= usp - 5776 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 16 -> mem_inv bsegs m ->
evt bsegs (fun ms' => exists (jh : list byte) (m1 : mem),
ms' = MS (mkR (Z_to_bv 64 RA_qmf_pois2) (Z_to_bv 64 (usp + S4b)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -208))
(Z_to_bv 64 (usp + X2o)) (Z_to_bv 64 VS) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (N / 2)) (Z_to_bv 64 (32 + N / 2)) (Z_to_bv 64 (usp + X2o)) (Z_to_bv 64 (usp + X1o)) (Z_to_bv 64 H) (Z_to_bv 64 (usp + S4b)) (Z_to_bv 64 A_H0)
(Z_to_bv 64 (Y + 2 * N)) (Z_to_bv 64 Y) (Z_to_bv 64 SHB) t3 t4 t5 t6)
F (Z_to_bv 64 e_alloca_poison) fc None m1 (seg_rom bsegs)
/\ munch [(usp + PR2, usp + S4); (usp + -144, usp + -136)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + S4b)
/\ rw_cells bsegs m1 (usp + -208) (qmf_frameB (CB 8 j0) (CB 8 j1) (C8 (Z_to_bv 64 0)) (Z_to_bv 64 VS) (Z_to_bv 64 G1) (Z_to_bv 64 G0) (Z_to_bv 64 Y) (Z_to_bv 64 32)
(Z_to_bv 64 (usp + S4)) j72 j80 j88 j96 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra)
/\ rw_cells bsegs m1 (usp + S4b) [CB (Z.to_nat H) jh])
(MS (mkR (Z_to_bv 64 RA_qmf_pois1) (Z_to_bv 64 (usp + S4)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -208)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (N / 2)) (Z_to_bv 64 (32 + N / 2)) (Z_to_bv 64 (usp + S4)) (Z_to_bv 64 (usp + X1o)) (Z_to_bv 64 H) s7 (Z_to_bv 64 A_H0)
(Z_to_bv 64 (Y + 2 * N)) (Z_to_bv 64 Y) (Z_to_bv 64 SHB) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_qmf_pois1)) fc None m (seg_rom bsegs)).
Lemma qmf_w2B_320 : qmf_w2B_stmt 320 768 832 (-1040) (-1008) (-1872) (-1840) (-5136).
Proof.
unfold qmf_w2B_stmt.
intros until m. intros FR ST LO LOS SPH U32 MI.
unfold RA_qmf_pois1, RA_qmf_pois2, e_alloca_poison, qmf_frameB in *.
replace (ret_pc (Z_to_bv 64 0xa85e8)) with (Z_to_bv 64 0xa85e8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -5136, usp + -1040); (usp + -144, usp + -136)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -5136, usp + -1040); (usp + -144, usp + -136)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 832%nat ST. rename FR0 into HULL2.
carve_frame 3256%nat ST. rename FR0 into JK2.
carve_frame 8%nat ST. rename FR0 into P2.
apply (rw_cells_split_CB bsegs _ _ [] 8 _ [] [8]%nat) in P2; [| reflexivity]. cbn [mk_CB_cells app] in P2.
ato 0xa85ec. astep. replace (usp + -1040 - 832) with (usp + -1872) by lia. rewrite ?Z.mod_small by lia.
astep. rewrite (land_m32_al (usp + -1872)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. astep. replace (usp + -1040 - 4096) with (usp + -5136) by lia.
astep. astep. sh_if.
ato 0x51e24.
release_frame P2 ST (usp + -5128). release_frame JK2 ST (usp + -1872).
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR| exact HULL2].
Qed.

Lemma qmf_w2B_640 : qmf_w2B_stmt 640 1408 1472 (-1680) (-1648) (-3152) (-3120) (-5776).
Proof.
unfold qmf_w2B_stmt.
intros until m. intros FR ST LO LOS SPH U32 MI.
unfold RA_qmf_pois1, RA_qmf_pois2, e_alloca_poison, qmf_frameB in *.
replace (ret_pc (Z_to_bv 64 0xa85e8)) with (Z_to_bv 64 0xa85e8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -5776, usp + -1680); (usp + -144, usp + -136)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -5776, usp + -1680); (usp + -144, usp + -136)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 1472%nat ST. rename FR0 into HULL2.
carve_frame 2616%nat ST. rename FR0 into JK2.
carve_frame 8%nat ST. rename FR0 into P2.
apply (rw_cells_split_CB bsegs _ _ [] 8 _ [] [8]%nat) in P2; [| reflexivity]. cbn [mk_CB_cells app] in P2.
ato 0xa85ec. astep. replace (usp + -1680 - 1472) with (usp + -3152) by lia. rewrite ?Z.mod_small by lia.
astep. rewrite (land_m32_al (usp + -3152)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. astep. replace (usp + -1680 - 4096) with (usp + -5776) by lia.
astep. astep. sh_if.
ato 0x51e24.
release_frame P2 ST (usp + -5768). release_frame JK2 ST (usp + -3152).
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR| exact HULL2].
Qed.

Lemma qmf_w5B : forall (usp lo top : Z) (gp tp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 sp vs g1 g0 y m2 : word)
(w8 w16 : word) (j0 j72 j80 j88 j96 : list byte) (c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells bsegs m (usp + -208) (qmf_frameB (CB 8 j0) (C8 w8) (C8 w16) vs g1 g0 y m2 (Z_to_bv 64 top) j72 j80 j88 j96 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
lo <= usp - 5776 -> SH_HI <= lo -> usp < 2^63 -> mem_inv bsegs m ->
evt bsegs (fun ms' =>
ms' = MS (mkR (Z_to_bv 64 RA_qmf_unpois) sp gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -208))
(Z_to_bv 64 top) (Z_to_bv 64 (usp + -144)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_allocas_unpoison) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -208)) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_qmf_epi) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR LO LOS SPH MI.
unfold RA_qmf_unpois, A_qmf_epi, e_allocas_unpoison, qmf_frameB in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
ato 0x51f50. replace (usp + -208 + 64) with (usp + -144) by lia. apply evt_done. reflexivity.
Qed.

Definition qmf_w6B_stmt (H S4 S4b : Z) : Prop :=
forall (usp lo : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 sp vs g1 g0 y m2 top w8 w16 : word)
(j0 j72 j80 j88 j96 jh1 jh2 : list byte) (c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells bsegs m (usp + -208) (qmf_frameB (CB 8 j0) (C8 w8) (C8 w16) vs g1 g0 y m2 top j72 j80 j88 j96 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
rw_cells bsegs m (usp + S4) [CB (Z.to_nat H) jh1] -> rw_cells bsegs m (usp + S4b) [CB (Z.to_nat H) jh2] ->
stk bsegs m lo (usp + S4b) ->
lo <= usp - 5776 -> SH_HI <= lo -> usp < 2^63 -> mem_inv bsegs m ->
evt bsegs (fun ms' =>
ms' = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 a0 a1 a2 a3 a4 a5 a6 a7 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 t3 t4 t5 t6)
F (ret_pc cra) fc None m (seg_rom bsegs)
/\ stk bsegs m lo usp)
(MS (mkR (Z_to_bv 64 RA_qmf_unpois) sp gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -208)) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_qmf_unpois)) fc None m (seg_rom bsegs)).
Lemma qmf_w6B_320 : qmf_w6B_stmt 832 (-1040) (-1872).
Proof.
unfold qmf_w6B_stmt.
intros until m. intros FR H1 H2 ST LO LOS SPH MI.
unfold RA_qmf_unpois, qmf_frameB in *. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in H1, H2.
replace (ret_pc (Z_to_bv 64 0xa8ec4)) with (Z_to_bv 64 0xa8ec4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
ato 0xa8efc. astep.
release_frame H2 ST (usp + -1040). release_frame H1 ST (usp + -208). release_frame FR ST usp.
astep. apply evt_done. split; [reflexivity| exact ST].
Qed.

Lemma qmf_w6B_640 : qmf_w6B_stmt 1472 (-1680) (-3152).
Proof.
unfold qmf_w6B_stmt.
intros until m. intros FR H1 H2 ST LO LOS SPH MI.
unfold RA_qmf_unpois, qmf_frameB in *. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in H1, H2.
replace (ret_pc (Z_to_bv 64 0xa8ec4)) with (Z_to_bv 64 0xa8ec4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
ato 0xa8efc. astep.
release_frame H2 ST (usp + -1680). release_frame H1 ST (usp + -208). release_frame FR ST usp.
astep. apply evt_done. split; [reflexivity| exact ST].
Qed.

