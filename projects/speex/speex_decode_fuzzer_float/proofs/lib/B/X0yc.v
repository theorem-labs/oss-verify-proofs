(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1dg X1df X1ck X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05q X05l.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0z5.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation mem := (word -> option byte).

Definition B_highpass : Z := 0xa5d3c.
Definition eB_stack_malloc_2 : Z := 0x51618.
Definition eB_asan_memcpy : Z := 0x66400.
Definition RA_hp_smalloc : Z := 0xa5dbc.
Definition RA_hp_cpy1 : Z := 0xa5ec0.
Definition RA_hp_cpy2 : Z := 0xa5ef4.
Definition HP_PCOEF : Z := 0x24720.
Definition HP_ZCOEF : Z := 0x24780.
Definition HP_EPI : Z := 0xa6200.

Definition hp_frame (c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c144 : cell) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
[c0; c8; c16; c24; c32; c40; c48; c56; c64; c72; c80; c88; c96; c104; c112; c120; c128; c136; c144;
C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma hp_w1 : forall (usp lo X Y n filt PM : Z) (ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem),
stk bsegs m lo usp -> lo <= usp - 256 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
client_constsB m -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j128 j136 j144 : list byte),
ms = MS (mkR (Z_to_bv 64 RA_hp_smalloc) (Z_to_bv 64 (usp + -256)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -256))
(Z_to_bv 64 224) (Z_to_bv 64 gB_shadow_memory_dynamic_address) (Z_to_bv 64 1) (Z_to_bv 64 filt) (Z_to_bv 64 PM) a5 a6 a7
s2 (Z_to_bv 64 PM) (Z_to_bv 64 SHB) s5 (Z_to_bv 64 n) (Z_to_bv 64 filt) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 eB_stack_malloc_2) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -256, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -256)
/\ rw_cells bsegs m1 (usp + -256)
(hp_frame (C8 (Z_to_bv 64 0)) (CB 8 j8) (CB 8 j16) (CB 8 j24) (CB 8 j32) (CB 8 j40) (CB 8 j48) (CB 8 j56) (CB 8 j64) (CB 8 j72) (CB 8 j80) (CB 8 j88)
(CB 8 j96) (CB 8 j104) (C8 (Z_to_bv 64 Y)) (C8 (Z_to_bv 64 X)) (CB 8 j128) (CB 8 j136) (CB 8 j144) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 n) (Z_to_bv 64 filt) (Z_to_bv 64 PM) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 B_highpass) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST LO LOS SPH SP32 (G1 & G2 & G3 & G4) MI.
unfold B_highpass, RA_hp_smalloc, eB_stack_malloc_2, hp_frame,
gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -256, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
carve_frame 256%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 256 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
cbn [mk_CB_cells app] in FR.
ato 0xa5d80. astep. rewrite land_m32_al by lia.
bato 0xa5da8. rewrite sx32_small by (unfold int31; lia).
bato 0x51618.
apply evt_done. do 17 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.

Definition hp_fhdr (rest : list byte) : list cell :=
[C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1179b); C8 (Z_to_bv 64 0xa5d3c); CB 224 rest].
Definition hF1 : byte := Z_to_bv 8 (-15).  Definition hF2 : byte := Z_to_bv 8 (-14).  Definition hF3 : byte := Z_to_bv 8 (-13).
Definition hF5 : byte := Z_to_bv 8 (-11).  Definition hF8 : byte := Z_to_bv 8 (-8).   Definition hb4 : byte := Z_to_bv 8 4.

Definition hp_shadow_w2 (rest : list byte) : list cell :=
map C1 (repeat hF1 4 ++ repeat z8 7 ++ [hb4] ++ repeat hF2 4 ++ repeat hF8 8 ++ repeat hF3 4) ++ [CB 4 rest].

Definition hp_shadow_live (rest : list byte) : list cell :=
map C1 (repeat hF1 4 ++ repeat z8 7 ++ [hb4] ++ repeat hF2 4 ++ repeat z8 7 ++ [hb4] ++ repeat hF3 4) ++ [CB 4 rest].

Definition hp_shadow_scope (rest : list byte) : list cell :=
map C1 (repeat hF1 4 ++ repeat hF8 8 ++ repeat hF2 4 ++ repeat hF8 8 ++ repeat hF3 4) ++ [CB 4 rest].
Definition hp_shadow_dead : list cell := map C1 (repeat hF5 32).

Lemma hp_w2 : forall (usp lo X Y n filt PM f sf : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) (j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j128 j136 j144 jb js : list byte) F fc (m : mem),
stk bsegs m lo (usp + -256) -> lo <= usp + -256 -> SH_HI <= lo -> usp < 2^63 ->
0 < f -> f mod 64 = 0 -> f + 256 <= lo -> f + 256 <= APP_TOP -> (f + 256 <= SH_LO \/ SH_HI <= f) -> sf = Z.shiftr f 3 + SHB ->
rw_cells bsegs m (usp + -256)
(hp_frame (C8 (Z_to_bv 64 0)) (CB 8 j8) (CB 8 j16) (CB 8 j24) (CB 8 j32) (CB 8 j40) (CB 8 j48) (CB 8 j56) (CB 8 j64) (CB 8 j72) (CB 8 j80) (CB 8 j88)
(CB 8 j96) (CB 8 j104) (C8 (Z_to_bv 64 Y)) (C8 (Z_to_bv 64 X)) (CB 8 j128) (CB 8 j136) (CB 8 j144) c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
rw_cells bsegs m f [CB 248 jb] -> rw_cells bsegs m sf [CB 32 js] ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (rb rs : list byte),
ms = MS (mkR (Z_to_bv 64 RA_hp_cpy1) (Z_to_bv 64 (usp + -256)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -256))
(Z_to_bv 64 (f + 32)) (Z_to_bv 64 HP_PCOEF) (Z_to_bv 64 60) (Z_to_bv 64 f) a4 a5 a6 a7
(Z_to_bv 64 4) (Z_to_bv 64 PM) (Z_to_bv 64 SHB) s5 (Z_to_bv 64 n) (Z_to_bv 64 filt) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 128)) (Z_to_bv 64 sf) s11
t3 t4 t5 t6)
F (Z_to_bv 64 eB_asan_memcpy) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -256, usp); (f, f + 248); (sf, sf + 32)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -256)
/\ rw_cells bsegs m1 (usp + -256)
(hp_frame (C8 (Z_to_bv 64 0)) (CB 8 j8) (CB 8 j16) (CB 8 j24) (CB 8 j32) (CB 8 j40) (CB 8 j48) (CB 8 j56) (C8 (Z_to_bv 64 f)) (C8 (Z_to_bv 64 f)) (CB 8 j80) (CB 8 j88)
(CB 8 j96) (CB 8 j104) (C8 (Z_to_bv 64 Y)) (C8 (Z_to_bv 64 X)) (CB 8 j128) (CB 8 j136) (C8 (Z_to_bv 64 f)) c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra)
/\ rw_cells bsegs m1 f (hp_fhdr rb) /\ rw_cells bsegs m1 sf (hp_shadow_w2 rs))
(MS (mkR (Z_to_bv 64 RA_hp_smalloc) (Z_to_bv 64 (usp + -256)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -256)) (Z_to_bv 64 f)
a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 PM) (Z_to_bv 64 SHB) s5 (Z_to_bv 64 n) (Z_to_bv 64 filt) s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_hp_smalloc)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST LO LOS SPH F0 F64 FLO FTOP FSH Esf FR FRB FRS MI.
unfold hp_frame, hp_fhdr, hp_shadow_w2, RA_hp_smalloc, RA_hp_cpy1, eB_asan_memcpy, HP_PCOEF, hF1, hF2, hF3, hF8, hb4, z8 in *. cbn [map repeat app]. unfold APP_TOP in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FSH as FSH'. unfold SH_LO, SH_HI in FSH'.
pose proof (shad_range_al f 256 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) ltac:(unfold APP_TOP; lia)) as SW.
rewrite <- shad_shiftr, <- Esf in SW. change (256 / 8) with 32 in SW. unfold SH_LO, SH_HI in SW.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -256, usp); (f, f + 248); (sf, sf + 32)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
replace (ret_pc (Z_to_bv 64 0xa5dbc)) with (Z_to_bv 64 0xa5dbc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
apply (rw_cells_split_CB bsegs _ _ [] 248 _ [] [8; 8; 8; 224]%nat) in FRB; [| reflexivity]. cbn [mk_CB_cells app] in FRB.
apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 4]%nat) in FRS; [| reflexivity].
cbn [mk_CB_cells app] in FRS.
astep. astep. astep. sh_if.
bato 0xa5e28. astep. rewrite <- Esf.
bato 0x66400.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|]. split; [exact FRB| exact FRS].
Qed.

Lemma hp_w3 : forall (usp n filt PM f sf : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s11 t3 t4 t5 t6 : word) (rs : list byte) F fc (m : mem),
rw_cells bsegs m sf (hp_shadow_w2 rs) -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 RA_hp_cpy2) (Z_to_bv 64 (usp + -256)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -256))
(Z_to_bv 64 (f + 128)) (Z_to_bv 64 HP_ZCOEF) (Z_to_bv 64 60) a3 a4 a5 a6 a7
(Z_to_bv 64 4) (Z_to_bv 64 PM) (Z_to_bv 64 SHB) s5 (Z_to_bv 64 n) (Z_to_bv 64 filt) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 128)) (Z_to_bv 64 sf) s11
t3 t4 t5 t6)
F (Z_to_bv 64 eB_asan_memcpy) fc None m1 (seg_rom bsegs)
/\ munch [(sf, sf + 32)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ rw_cells bsegs m1 sf (hp_shadow_live rs))
(MS (mkR (Z_to_bv 64 RA_hp_cpy1) (Z_to_bv 64 (usp + -256)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -256)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 4) (Z_to_bv 64 PM) (Z_to_bv 64 SHB) s5 (Z_to_bv 64 n) (Z_to_bv 64 filt) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 128)) (Z_to_bv 64 sf) s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_hp_cpy1)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FRS MI.
unfold hp_shadow_w2, hp_shadow_live, RA_hp_cpy1, RA_hp_cpy2, eB_asan_memcpy, HP_ZCOEF, hF1, hF2, hF3, hF8, hb4, z8 in *. cbn [map repeat app] in *.
pose proof (rw_cells_bound _ _ _ _ FRS) as BS. cbn [cells_size csize Nat.add] in BS.
replace (ret_pc (Z_to_bv 64 0xa5ec0)) with (Z_to_bv 64 0xa5ec0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(sf, sf + 32)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
bato 0x66400.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact FRS].
Qed.

Lemma hp_tabs_acc : forall (m : mem) (f sf : Z) (rs : list byte),
rw_cells bsegs m sf (hp_shadow_live rs) -> sf = Z.shiftr f 3 + SHB -> f mod 64 = 0 -> 0 <= f ->
acc bsegs m (f + 32) 60 /\ acc bsegs m (f + 128) 60.
Proof.
intros m f sf rs [[_ B] _] Esf F64 F0. unfold hp_shadow_live in B.
rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B _].
assert (E : cells_bytes (map C1 (repeat hF1 4 ++ repeat z8 7 ++ [hb4] ++ repeat hF2 4 ++ repeat z8 7 ++ [hb4] ++ repeat hF3 4))
= repeat hF1 4 ++ (repeat z8 7 ++ [hb4]) ++ repeat hF2 4 ++ (repeat z8 7 ++ [hb4]) ++ repeat hF3 4) by reflexivity.
rewrite E in B. apply bytes_at_app in B. destruct B as [_ B]. apply bytes_at_app in B. destruct B as [BD B].
apply bytes_at_app in B. destruct B as [_ B]. apply bytes_at_app in B. destruct B as [BN _].
cbn [length repeat app] in BD, BN.
assert (SH1 : shad (f + 32) = sf + 4) by (rewrite Esf, shad_shiftr; unfold shad; clear - F64; Z.div_mod_to_equations; lia).
assert (SH2 : shad (f + 128) = sf + 16) by (rewrite Esf, shad_shiftr; unfold shad; clear - F64; Z.div_mod_to_equations; lia).
split.
- apply acc_ushadow; [clear - F64; Z.div_mod_to_equations; lia | lia | lia |]. rewrite SH1. exact BD.
- apply acc_ushadow; [clear - F64; Z.div_mod_to_equations; lia | lia | lia |]. rewrite SH2.
replace (sf + 16) with (sf + Z.of_nat 4 + Z.of_nat 8 + Z.of_nat 4) by lia. exact BN.
Qed.

Section HPL.
Variables (X PM f sf r usp : Z).
Variables (gp tp : word).
Variables (w0 w64 w72 w144 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra : word).
Variables (j8 j128 j136 : list byte).
Variable m : mem.
Hypothesis OBX : aobj bsegs m X 640.
Hypothesis OBM : aobj bsegs m PM 8.
Hypothesis OBD : aobj bsegs m (f + 32) 60.
Hypothesis OBN : aobj bsegs m (f + 128) 60.
Hypothesis X4 : X mod 4 = 0.
Hypothesis XPOS : 0 < X.
Hypothesis M8 : PM mod 8 = 0.
Hypothesis MPOS : 0 < PM.
Hypothesis F64 : f mod 64 = 0.
Hypothesis FPOS : 0 < f.
Hypothesis RR : r = 12 \/ r = 36.
Hypothesis XSH : X + 640 <= SH_LO \/ SH_HI <= X.
Hypothesis MSH : PM + 8 <= SH_LO \/ SH_HI <= PM.
Hypothesis XM : X + 640 <= PM \/ PM + 8 <= X.
Hypothesis XB : X + 640 < 2^63.
Hypothesis MB : PM + 8 < 2^63.
Hypothesis FB : f + 256 < 2^63.
Hypothesis XF : X + 640 <= f \/ f + 256 <= X.
Hypothesis MF : PM + 8 <= f \/ f + 256 <= PM.
Hypothesis XSA : X + 640 <= usp + -256 \/ usp <= X.
Hypothesis MSA : PM + 8 <= usp + -256 \/ usp <= PM.
Hypothesis SB : SH_HI <= usp + -256.
Hypothesis SPH : usp < 2^63.

Definition RHP (kz : Z) (t0 t1 a3 a6 a7 s11 t3 : word) : bvmap 5 word :=
mkR (Z_to_bv 64 (Z.shiftr (f + 132 + r) 3 + SHB)) (Z_to_bv 64 (usp + -256)) gp tp t0 t1 (Z_to_bv 64 (Z.shiftr (f + 36 + r) 3 + SHB))
(Z_to_bv 64 usp) (Z_to_bv 64 (usp + -256))
(Z_to_bv 64 (f + 128 + r)) (Z_to_bv 64 (PM + 4)) (Z_to_bv 64 (Z.shiftr (f + 40 + r) 3 + SHB)) a3 (Z_to_bv 64 1) (Z_to_bv 64 1) a6 a7
(Z_to_bv 64 (Z.shiftr (PM + 4) 3 + SHB)) (Z_to_bv 64 PM) (Z_to_bv 64 SHB) (Z_to_bv 64 (-9)) (Z_to_bv 64 (f + 36 + r)) (Z_to_bv 64 (f + 40 + r))
(Z_to_bv 64 (f + 32 + r)) (Z_to_bv 64 1) (Z_to_bv 64 sf) s11 t3 (Z_to_bv 64 kz) (Z_to_bv 64 (Z.shiftr PM 3 + SHB)) (Z_to_bv 64 (Z.shiftr (f + 136 + r) 3 + SHB)).
Local Notation FRL := (hp_frame (C8 w0) (CB 8 j8) (C8 (Z_to_bv 64 7)) (C8 (Z_to_bv 64 3)) (C8 (Z_to_bv 64 7)) (C8 (Z_to_bv 64 3)) (C8 (Z_to_bv 64 7)) (C8 (Z_to_bv 64 3)) (C8 w64) (C8 w72) (C8 (Z_to_bv 64 (f + 136 + r))) (C8 (Z_to_bv 64 (f + 132 + r)))
(C8 (Z_to_bv 64 1)) (C8 (Z_to_bv 64 1)) (C8 (Z_to_bv 64 X)) (C8 (Z_to_bv 64 X)) (CB 8 j128) (CB 8 j136) (C8 w144) q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra).
Local Notation W := [(X, X + 640); (PM, PM + 8)].
Definition hp_loop_post : machine_state -> Prop :=
fun ms => exists (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (t0' t1' a3' a6' a7' s11' t3' kz' : word) (xs' : list word) (u0 u1 : word),
ms = MS (mkR (Z_to_bv 64 (Z.shiftr (f + 132 + r) 3 + SHB)) (Z_to_bv 64 (usp + -256)) gp tp t0' t1' (Z_to_bv 64 (Z.shiftr (f + 36 + r) 3 + SHB))
(Z_to_bv 64 usp) (Z_to_bv 64 (usp + -256))
(Z_to_bv 64 (f + 128 + r)) (Z_to_bv 64 (PM + 4)) (Z_to_bv 64 (Z.shiftr (f + 40 + r) 3 + SHB)) a3' (Z_to_bv 64 1) (Z_to_bv 64 1) a6' a7'
(Z_to_bv 64 (Z.shiftr (PM + 4) 3 + SHB)) (Z_to_bv 64 PM) (Z_to_bv 64 SHB) (Z_to_bv 64 (-9)) (Z_to_bv 64 (f + 36 + r)) (Z_to_bv 64 (f + 40 + r))
(Z_to_bv 64 (f + 32 + r)) (Z_to_bv 64 1) (Z_to_bv 64 sf) s11' t3' kz' (Z_to_bv 64 (Z.shiftr PM 3 + SHB)) (Z_to_bv 64 (Z.shiftr (f + 136 + r) 3 + SHB)))
F' (Z_to_bv 64 HP_EPI) fc' None m' (seg_rom bsegs)
/\ frm0 fc' /\ munch W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ rw_cells bsegs m' X (f32 xs') /\ length xs' = 160%nat /\ rw_cells bsegs m' PM [C4 u0; C4 u1].

Lemma hp_loop : forall (rest dn : list word) (x d1 d2 n1 n2 v0 v1 : word) (kz off : Z) (a3 s11 t3 : word) (Fz : bvmap 5 word) fc m1,
(length dn + S (length rest) = 160)%nat -> kz = Z.of_nat (S (length rest)) -> off = 4 * Z.of_nat (length dn) ->
frm0 fc -> munch W m m1 -> offsh W -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
rw_cells bsegs m1 (usp + -256) FRL ->
rw_cells bsegs m1 (f + 36 + r) [C4 d1] -> rw_cells bsegs m1 (f + 40 + r) [C4 d2] -> rw_cells bsegs m1 (f + 132 + r) [C4 n1] -> rw_cells bsegs m1 (f + 136 + r) [C4 n2] ->
rw_cells bsegs m1 PM [C4 v0; C4 v1] ->
rw_cells bsegs m1 X (f32 dn) -> rw_cells bsegs m1 (X + off) (f32 (x :: rest)) ->
evt bsegs hp_loop_post
(MS (RHP kz (Z_to_bv 64 (X + off)) (Z_to_bv 64 (X + off)) a3 (Z_to_bv 64 (X + off)) (Z_to_bv 64 (X + off)) s11 t3) Fz (Z_to_bv 64 0xa6040) fc None m1 (seg_rom bsegs)).
Proof using OBX OBM OBD OBN X4 XPOS M8 MPOS F64 FPOS RR XSH MSH XM XB MB FB XF MF XSA MSA SB SPH.
induction rest as [|x' rest IH]; intros dn x d1 d2 n1 n2 v0 v1 kz off a3 s11 t3 Fz fc m1 Hn Hkz Hoff FRM MU OF WM MI FR D1 D2 N1 N2 PMC DONE XC;
pose proof (rw_cells_bound _ _ _ _ XC) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof OBX as (OX0 & OX1 & _); pose proof OBM as (OM0 & OM1 & _); unfold APP_TOP in *;
pose proof SB as SB'; unfold SH_HI in SB'; pose proof XSH as XSH'; pose proof MSH as MSH'; unfold SH_LO, SH_HI in XSH', MSH';
subst kz;
assert (NZ : (X + off <? 1) = false) by (apply Z.ltb_ge; lia);
unfold RHP, hp_frame in *; rewrite f32_cons in XC; chunk_uncons XC as X1; cbn [length] in *.
-
bato 0xa604c. rewrite NZ. cbn [Z.b2z].
bato 0xa6068. astep. chk_merge OBX 4.
chk_hint OBM.
bato 0xa6098. chk_hint OBN.
bato 0xa60a0. astep. chk_merge OBN 4.
chk_hint OBM.
bato 0xa60b4. chk_hint OBD.
bato 0xa60bc. astep. chk_merge OBD 4.
chk_hint OBM.
bato 0xa60e8. astep. chk_merge OBX 4.
bato 0xa60ec. chk_hint OBN.
bato 0xa60f4. astep. chk_merge OBN 4.
bato 0xa60f8. chk_hint OBD.
bato 0xa6104. astep. chk_merge OBD 4.
chk_hint OBM.
bato 0xa6148. astep. chk_merge OBX 4.
bato 0xa6164.
astep. cbn [Z.of_nat Pos.of_succ_nat] in *. try sh_if. bato 0xa6200.
rewrite f32_nil in XC.
chunk_snoc DONE X1.
lazymatch type of DONE with rw_cells _ _ _ (f32 dn ++ [C4 ?w]) => change [C4 w] with (f32 [w]) in DONE; rewrite <- f32_app in DONE end.
lazymatch goal with H : rw_cells bsegs ?mc PM [C4 ?u0; C4 ?u1] |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
apply evt_done; unfold hp_loop_post; do 12 eexists; exists u0, u1;
split; [reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
split; [exact DONE|]; split; [rewrite length_app; cbn [length] in *; lia| exact H] end.
-
bato 0xa604c. rewrite NZ. cbn [Z.b2z].
bato 0xa6068. astep. chk_merge OBX 4.
chk_hint OBM.
bato 0xa6098. chk_hint OBN.
bato 0xa60a0. astep. chk_merge OBN 4.
chk_hint OBM.
bato 0xa60b4. chk_hint OBD.
bato 0xa60bc. astep. chk_merge OBD 4.
chk_hint OBM.
bato 0xa60e8. astep. chk_merge OBX 4.
bato 0xa60ec. chk_hint OBN.
bato 0xa60f4. astep. chk_merge OBN 4.
bato 0xa60f8. chk_hint OBD.
bato 0xa6104. astep. chk_merge OBD 4.
chk_hint OBM.
bato 0xa6148. astep. chk_merge OBX 4.
bato 0xa6164.
astep. cbn [length] in *. sh_if.
rewrite f32_cons in XC.
chunk_snoc DONE X1.
lazymatch type of DONE with rw_cells _ _ _ (f32 dn ++ [C4 ?w]) => change [C4 w] with (f32 [w]) in DONE; rewrite <- f32_app in DONE;
rewrite <- f32_cons in XC;
replace (X + off + 4) with (X + (off + 4)) in * by lia;
replace (Z.of_nat (S (S (length rest))) + -1) with (Z.of_nat (S (length rest))) by lia;
eapply (IH (dn ++ [w]) x' d1 d2 n1 n2 _ _ _ (off + 4)); try eassumption; try reflexivity; try (rewrite ?length_app; cbn [length] in *; lia) end.
Qed.
End HPL.

Lemma hp_rw_f32_nth : forall (m : mem) A ws i, rw_cells bsegs m A (f32 ws) -> 0 <= i < Z.of_nat (length ws) -> exists w : word, rw_cells bsegs m (A + 4 * i) [C4 w].
Proof.
intros m A ws i H Hi. pose proof (rw_cells_f32_mid bsegs m A ws (Z.to_nat i) 1 H ltac:(lia)) as W.
replace (Z.of_nat (Z.to_nat i)) with i in W by lia.
destruct (skipn (Z.to_nat i) ws) as [|w r] eqn:E.
- exfalso. assert (L : length (skipn (Z.to_nat i) ws) = 0%nat) by (rewrite E; reflexivity). rewrite length_skipn in L. lia.
- exists w. exact W.
Qed.
Lemma land7_mod8 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Definition hp_body_post (usp lo X PM f sf : Z) (gp tp : word) (j8 j128 j136 : list byte) (c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) (m : mem)
: machine_state -> Prop :=
fun ms => exists (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
(w16 w24 w32 w40 w48 w56 w80 w88 w96 w104 : word) (xs' : list word) (u0 u1 : word),
ms = MS (mkR xra (Z_to_bv 64 (usp + -256)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -256)) a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 sf) s11 t3 t4 t5 t6) F' (Z_to_bv 64 HP_EPI) fc' None m' (seg_rom bsegs)
/\ munch [(X, X + 640); (PM, PM + 8); (usp + -256, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ frm0 fc' /\ stk bsegs m' lo (usp + -256)
/\ rw_cells bsegs m' (usp + -256)
(hp_frame (C8 (Z_to_bv 64 0)) (CB 8 j8) (C8 w16) (C8 w24) (C8 w32) (C8 w40) (C8 w48) (C8 w56) (C8 (Z_to_bv 64 f)) (C8 (Z_to_bv 64 f)) (C8 w80) (C8 w88)
(C8 w96) (C8 w104) (C8 (Z_to_bv 64 X)) (C8 (Z_to_bv 64 X)) (CB 8 j128) (CB 8 j136) (C8 (Z_to_bv 64 f)) c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra)
/\ rw_cells bsegs m' X (f32 xs') /\ length xs' = 160%nat /\ rw_cells bsegs m' PM (f32 [u0; u1]).

Lemma hp_body : forall (usp lo X PM f sf filt : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s11 t3 t4 t5 t6 : word)
(c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) (j8 j16 j24 j32 j40 j48 j56 j80 j88 j96 j104 j128 j136 rs : list byte) (den num xs ms0 : list word) F fc (m : mem),
filt = 1 \/ filt = 3 ->
stk bsegs m lo (usp + -256) -> lo <= usp + -256 -> SH_HI <= lo -> usp < 2^63 ->
0 < f -> f mod 64 = 0 -> f + 256 <= lo -> f + 256 <= APP_TOP -> (f + 256 <= SH_LO \/ SH_HI <= f) -> sf = Z.shiftr f 3 + SHB ->
rw_cells bsegs m (usp + -256)
(hp_frame (C8 (Z_to_bv 64 0)) (CB 8 j8) (CB 8 j16) (CB 8 j24) (CB 8 j32) (CB 8 j40) (CB 8 j48) (CB 8 j56) (C8 (Z_to_bv 64 f)) (C8 (Z_to_bv 64 f)) (CB 8 j80) (CB 8 j88)
(CB 8 j96) (CB 8 j104) (C8 (Z_to_bv 64 X)) (C8 (Z_to_bv 64 X)) (CB 8 j128) (CB 8 j136) (C8 (Z_to_bv 64 f)) c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
rw_cells bsegs m sf (hp_shadow_live rs) ->
rw_cells bsegs m (f + 32) (f32 den) -> length den = 15%nat -> rw_cells bsegs m (f + 128) (f32 num) -> length num = 15%nat ->
rw_cells bsegs m X (f32 xs) -> length xs = 160%nat -> aobj bsegs m X 640 -> X mod 4 = 0 -> 0 < X -> X + 640 < 2^63 ->
(X + 640 <= SH_LO \/ SH_HI <= X) -> (X + 640 <= f \/ f + 256 <= X) -> (X + 640 <= lo \/ usp <= X) ->
rw_cells bsegs m PM (f32 ms0) -> length ms0 = 2%nat -> aobj bsegs m PM 8 -> PM mod 8 = 0 -> 0 < PM -> PM + 8 < 2^63 ->
(PM + 8 <= SH_LO \/ SH_HI <= PM) -> (PM + 8 <= f \/ f + 256 <= PM) -> (PM + 8 <= lo \/ usp <= PM) -> (X + 640 <= PM \/ PM + 8 <= X) ->
mem_inv bsegs m -> frm0 fc ->
evt bsegs (hp_body_post usp lo X PM f sf gp tp j8 j128 j136 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra m)
(MS (mkR (Z_to_bv 64 RA_hp_cpy2) (Z_to_bv 64 (usp + -256)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -256)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 4) (Z_to_bv 64 PM) (Z_to_bv 64 SHB) s5 (Z_to_bv 64 160) (Z_to_bv 64 filt) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 128)) (Z_to_bv 64 sf) s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_hp_cpy2)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros HF ST LO LOS SPH F0 F64 FLO FTOP FSH Esf FR FRS DEN LDEN NUM LNUM XS LXS OBX X4 XP XB XSH XF XSA MS0 LMS OBM M8 MP MB MSH MF MSA XM MI FRM.
unfold hp_frame, RA_hp_cpy2 in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FSH as FSH'. unfold SH_LO, SH_HI in FSH'.
replace (ret_pc (Z_to_bv 64 0xa5ef4)) with (Z_to_bv 64 0xa5ef4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(X, X + 640); (PM, PM + 8); (usp + -256, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(X, X + 640); (PM, PM + 8); (usp + -256, usp)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
destruct (hp_tabs_acc m f sf rs FRS Esf F64 ltac:(lia)) as (ACD & ACN).
assert (OBD : aobj bsegs m (f + 32) 60) by (split; [lia|]; split; [unfold APP_TOP in *; lia| exact ACD]).
assert (OBN : aobj bsegs m (f + 128) 60) by (split; [lia|]; split; [unfold APP_TOP in *; lia| exact ACN]).
do 2 (destruct ms0 as [|? ms0]; [discriminate LMS|]). destruct ms0; [| discriminate LMS]. cbn [f32 map] in MS0.
assert (X4' : Z.land X 3 = 0) by (apply land3_al; exact X4).
pose proof (land3_al PM ltac:(clear - M8; Z.div_mod_to_equations; lia)) as M4'.
destruct xs as [|x rest]; [discriminate LXS|]. cbn [length] in LXS. injection LXS as LXS.
destruct HF as [-> | ->].
-
destruct (hp_rw_f32_nth m (f + 128) num 3 NUM ltac:(lia)) as (n0 & N0).
destruct (hp_rw_f32_nth m (f + 128) num 4 NUM ltac:(lia)) as (n1 & N1).
destruct (hp_rw_f32_nth m (f + 128) num 5 NUM ltac:(lia)) as (n2 & N2).
destruct (hp_rw_f32_nth m (f + 32) den 4 DEN ltac:(lia)) as (d1 & D1).
destruct (hp_rw_f32_nth m (f + 32) den 5 DEN ltac:(lia)) as (d2 & D2).
clear DEN NUM.
replace (f + 128 + 4 * 3) with (f + 140) in N0 by lia.
replace (f + 128 + 4 * 4) with (f + 144) in N1 by lia.
replace (f + 128 + 4 * 5) with (f + 148) in N2 by lia.
replace (f + 32 + 4 * 4) with (f + 48) in D1 by lia.
replace (f + 32 + 4 * 5) with (f + 52) in D2 by lia.
chk_hint OBN.
bato 0xa5f34. astep. try chk_merge OBN 4.
bato 0xa6040.
replace (0 <? X) with true in * by (symmetry; apply Z.ltb_lt; lia).
replace (0 <? PM) with true in * by (symmetry; apply Z.ltb_lt; lia).
rewrite X4', M4' in *.
change (Z.land (Z.b2z true) (Z.b2z (0 <? 1))) with 1 in *.
change (Z.land (Z.b2z (0 <? 1)) (Z.b2z true)) with 1 in *.
change (Z.b2z true) with 1 in *.
repeat match type of FR with
| context [Z.land (?b + ?k) 7 + 3] => is_Zlit k; let v := eval vm_compute in (Z.modulo k 8 + 3) in
replace (Z.land (b + k) 7 + 3) with v in FR by (rewrite land7_mod8 by lia; clear - F64 M8; Z.div_mod_to_equations; lia)
| context [Z.land PM 7 + 3] => replace (Z.land PM 7 + 3) with 3 in FR by (rewrite land7_mod8 by lia; clear - M8; Z.div_mod_to_equations; lia)
end.
replace (f + 148) with (f + 136 + 12) in * by lia.
replace (f + 144) with (f + 132 + 12) in * by lia.
replace (f + 140) with (f + 128 + 12) in * by lia.
replace (f + 52) with (f + 40 + 12) in * by lia.
replace (f + 48) with (f + 36 + 12) in * by lia.
replace (f + 44) with (f + 32 + 12) in * by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch bsegs _ m mc X 640 OBX MU (shfree_of_aobj bsegs _ m X 640 OF OBX)) as OBX1;
pose proof (aobj_munch bsegs _ m mc PM 8 OBM MU (shfree_of_aobj bsegs _ m PM 8 OF OBM)) as OBM1;
pose proof (aobj_munch bsegs _ m mc (f + 32) 60 OBD MU (shfree_of_aobj bsegs _ m (f + 32) 60 OF OBD)) as OBD1;
pose proof (aobj_munch bsegs _ m mc (f + 128) 60 OBN MU (shfree_of_aobj bsegs _ m (f + 128) 60 OF OBN)) as OBN1;
eapply evt_cut;
[ replace (Z_to_bv 64 X) with (Z_to_bv 64 (X + 4 * Z.of_nat (length (@nil word)))) by (cbn [length Z.of_nat]; f_equal; lia);
eapply (hp_loop X PM f sf 12 usp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc OBX1 OBM1 OBD1 OBN1 X4 XP M8 MP F64 F0 (or_introl eq_refl)
XSH MSH XM XB MB ltac:(lia) XF MF ltac:(lia) ltac:(lia) ltac:(lia) SPH rest [] x d1 d2 n1 n2 _ _ 160 _ _ _ _ _ _ mc)
| ]
end.
all: try (cbn [length]; lia).
all: try reflexivity.
all: try (apply munch_refl).
all: try (apply wmono_refl).
all: try (cbn [offsh]; unfold SH_LO, SH_HI in *; lia).
1: exact FRM.
1: eassumption.
1: exact FR.
1: exact D1.
1: exact D2.
1: exact N1.
1: exact N2.
1: exact MS0.
1: (apply rw_cells_nil; lia).
1: (replace (X + 4 * Z.of_nat (length (@nil word))) with X by (cbn [length Z.of_nat]; lia); exact XS).
intros ms' PO. unfold hp_loop_post in PO.
destruct PO as (m' & F' & fc' & t0' & t1' & a3' & a6' & a7' & s11' & t3' & kz' & xs' & u0 & u1 & -> & FRM' & MU' & WM' & MI' & XS' & LXS' & PMC').
transport_after_call bsegs m1 m' MU' WM'.
apply evt_done. unfold hp_body_post.
do 41 eexists.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact FRM'|]. split; [exact ST|].
split; [exact FR|]. split; [exact XS'|]. split; [exact LXS'| exact PMC'].
-
destruct (hp_rw_f32_nth m (f + 128) num 9 NUM ltac:(lia)) as (n0 & N0).
destruct (hp_rw_f32_nth m (f + 128) num 10 NUM ltac:(lia)) as (n1 & N1).
destruct (hp_rw_f32_nth m (f + 128) num 11 NUM ltac:(lia)) as (n2 & N2).
destruct (hp_rw_f32_nth m (f + 32) den 10 DEN ltac:(lia)) as (d1 & D1).
destruct (hp_rw_f32_nth m (f + 32) den 11 DEN ltac:(lia)) as (d2 & D2).
clear DEN NUM.
replace (f + 128 + 4 * 9) with (f + 164) in N0 by lia.
replace (f + 128 + 4 * 10) with (f + 168) in N1 by lia.
replace (f + 128 + 4 * 11) with (f + 172) in N2 by lia.
replace (f + 32 + 4 * 10) with (f + 72) in D1 by lia.
replace (f + 32 + 4 * 11) with (f + 76) in D2 by lia.
chk_hint OBN.
bato 0xa5f34. astep. try chk_merge OBN 4.
bato 0xa6040.
replace (0 <? X) with true in * by (symmetry; apply Z.ltb_lt; lia).
replace (0 <? PM) with true in * by (symmetry; apply Z.ltb_lt; lia).
rewrite X4', M4' in *.
change (Z.land (Z.b2z true) (Z.b2z (0 <? 1))) with 1 in *.
change (Z.land (Z.b2z (0 <? 1)) (Z.b2z true)) with 1 in *.
change (Z.b2z true) with 1 in *.
repeat match type of FR with
| context [Z.land (?b + ?k) 7 + 3] => is_Zlit k; let v := eval vm_compute in (Z.modulo k 8 + 3) in
replace (Z.land (b + k) 7 + 3) with v in FR by (rewrite land7_mod8 by lia; clear - F64 M8; Z.div_mod_to_equations; lia)
| context [Z.land PM 7 + 3] => replace (Z.land PM 7 + 3) with 3 in FR by (rewrite land7_mod8 by lia; clear - M8; Z.div_mod_to_equations; lia)
end.
replace (f + 172) with (f + 136 + 36) in * by lia.
replace (f + 168) with (f + 132 + 36) in * by lia.
replace (f + 164) with (f + 128 + 36) in * by lia.
replace (f + 76) with (f + 40 + 36) in * by lia.
replace (f + 72) with (f + 36 + 36) in * by lia.
replace (f + 68) with (f + 32 + 36) in * by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch bsegs _ m mc X 640 OBX MU (shfree_of_aobj bsegs _ m X 640 OF OBX)) as OBX1;
pose proof (aobj_munch bsegs _ m mc PM 8 OBM MU (shfree_of_aobj bsegs _ m PM 8 OF OBM)) as OBM1;
pose proof (aobj_munch bsegs _ m mc (f + 32) 60 OBD MU (shfree_of_aobj bsegs _ m (f + 32) 60 OF OBD)) as OBD1;
pose proof (aobj_munch bsegs _ m mc (f + 128) 60 OBN MU (shfree_of_aobj bsegs _ m (f + 128) 60 OF OBN)) as OBN1;
eapply evt_cut;
[ replace (Z_to_bv 64 X) with (Z_to_bv 64 (X + 4 * Z.of_nat (length (@nil word)))) by (cbn [length Z.of_nat]; f_equal; lia);
eapply (hp_loop X PM f sf 36 usp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc OBX1 OBM1 OBD1 OBN1 X4 XP M8 MP F64 F0 (or_intror eq_refl)
XSH MSH XM XB MB ltac:(lia) XF MF ltac:(lia) ltac:(lia) ltac:(lia) SPH rest [] x d1 d2 n1 n2 _ _ 160 _ _ _ _ _ _ mc)
| ]
end.
all: try (cbn [length]; lia).
all: try reflexivity.
all: try (apply munch_refl).
all: try (apply wmono_refl).
all: try (cbn [offsh]; unfold SH_LO, SH_HI in *; lia).
1: exact FRM.
1: eassumption.
1: exact FR.
1: exact D1.
1: exact D2.
1: exact N1.
1: exact N2.
1: exact MS0.
1: (apply rw_cells_nil; lia).
1: (replace (X + 4 * Z.of_nat (length (@nil word))) with X by (cbn [length Z.of_nat]; lia); exact XS).
intros ms' PO. unfold hp_loop_post in PO.
destruct PO as (m' & F' & fc' & t0' & t1' & a3' & a6' & a7' & s11' & t3' & kz' & xs' & u0 & u1 & -> & FRM' & MU' & WM' & MI' & XS' & LXS' & PMC').
transport_after_call bsegs m1 m' MU' WM'.
apply evt_done. unfold hp_body_post.
do 41 eexists.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact FRM'|]. split; [exact ST|].
split; [exact FR|]. split; [exact XS'|]. split; [exact LXS'| exact PMC'].
Qed.

Definition HP_EPI_B : Z := 0xa62e0.

Lemma hp_epi_a : forall (usp f sf : Z) (xra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
(w0 w16 w24 w32 w40 w48 w56 w80 w88 w96 w104 w112 w120 : word) (c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra hd : word) (j8 j128 j136 rs : list byte) F fc (m : mem),
0 < f -> f mod 64 = 0 -> f + 256 <= usp + -256 -> f + 256 <= APP_TOP -> (f + 256 <= SH_LO \/ SH_HI <= f) -> sf = Z.shiftr f 3 + SHB ->
SH_HI <= usp + -256 -> usp < 2^63 ->
rw_cells bsegs m (usp + -256)
(hp_frame (C8 w0) (CB 8 j8) (C8 w16) (C8 w24) (C8 w32) (C8 w40) (C8 w48) (C8 w56) (C8 (Z_to_bv 64 f)) (C8 (Z_to_bv 64 f)) (C8 w80) (C8 w88)
(C8 w96) (C8 w104) (C8 w112) (C8 w120) (CB 8 j128) (CB 8 j136) (C8 (Z_to_bv 64 f)) c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
rw_cells bsegs m f [C8 hd] -> rw_cells bsegs m sf (hp_shadow_live rs) ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR xra (Z_to_bv 64 (usp + -256)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -256)) (Z_to_bv 64 (-11)) (Z_to_bv 64 f) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 sf) s11 t3 t4 t5 t6)
F (Z_to_bv 64 HP_EPI_B) fc None m1 (seg_rom bsegs)
/\ munch [(f, f + 248); (sf, sf + 32)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 (usp + -256)
(hp_frame (C8 w0) (CB 8 j8) (C8 w16) (C8 w24) (C8 w32) (C8 w40) (C8 w48) (C8 w56) (C8 (Z_to_bv 64 f)) (C8 (Z_to_bv 64 f)) (C8 w80) (C8 w88)
(C8 w96) (C8 w104) (C8 w112) (C8 w120) (CB 8 j128) (CB 8 j136) (C8 (Z_to_bv 64 f)) c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra)
/\ rw_cells bsegs m1 sf hp_shadow_dead)
(MS (mkR xra (Z_to_bv 64 (usp + -256)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -256)) a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 sf) s11 t3 t4 t5 t6)
F (Z_to_bv 64 HP_EPI) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros F0 F64 FLO FTOP FSH Esf LOS SPH FR FRB FRS MI.
unfold hp_shadow_live in FRS. apply (rw_cells_split_CB bsegs _ _ _ 4 _ [] [1; 1; 1; 1]%nat) in FRS; [| reflexivity].
unfold hp_frame, hp_shadow_dead, HP_EPI, HP_EPI_B, hF1, hF2, hF3, hF5, hF8, hb4, z8 in *. cbn [map repeat app mk_CB_cells firstn skipn] in *. unfold APP_TOP in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FSH as FSH'. unfold SH_LO, SH_HI in FSH'.
pose proof (shad_range_al f 256 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) ltac:(unfold APP_TOP; lia)) as SW.
rewrite <- shad_shiftr, <- Esf in SW. change (256 / 8) with 32 in SW. unfold SH_LO, SH_HI in SW.
pose proof (munch_refl [(f, f + 248); (sf, sf + 32)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
bato 0xa6258. astep. sh_if.
bato 0xa62e0.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FR| exact FRS].
Qed.

Lemma hp_epi_b : forall (usp lo f fl : Z) (xra gp tp t0 t1 t2 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(w0 w16 w24 w32 w40 w48 w56 w80 w88 w96 w104 w112 w120 : word) (c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) (j8 j128 j136 : list byte) F fc (m : mem),
stk bsegs m lo (usp + -256) -> lo <= usp + -256 -> usp < 2^63 -> 0 < f -> f + 256 <= lo ->
0 < fl -> fl + 1 <= lo ->
rw_cells bsegs m (usp + -256)
(hp_frame (C8 w0) (CB 8 j8) (C8 w16) (C8 w24) (C8 w32) (C8 w40) (C8 w48) (C8 w56) (C8 (Z_to_bv 64 f)) (C8 (Z_to_bv 64 f)) (C8 w80) (C8 w88)
(C8 w96) (C8 w104) (C8 w112) (C8 w120) (CB 8 j128) (CB 8 j136) (C8 (Z_to_bv 64 f)) c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
ro_cells bsegs m (f + 248) [C8 (Z_to_bv 64 fl)] -> rw_cells bsegs m fl [C1 (Z_to_bv 8 1)] ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (a0' : word),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 a0' (Z_to_bv 64 f) a2 a3 a4 a5 a6 a7 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom bsegs)
/\ munch [(fl, fl + 1)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp
/\ rw_cells bsegs m1 fl [C1 z8])
(MS (mkR xra (Z_to_bv 64 (usp + -256)) gp tp t0 t1 t2 (Z_to_bv 64 usp) s1 a0 (Z_to_bv 64 f) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 HP_EPI_B) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST LO SPH F0 FLO L0 LLO FR FLP FLG MI.
unfold hp_frame, HP_EPI_B, z8 in *.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
bato 0xa6398. release_frame FR ST usp. astep.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact FLG].
Qed.

