(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05l.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition A_interp_pitch : Z := 0xa5934.
Definition e_stack_malloc_2 : Z := 0x5152c.
Definition RA_ip_smalloc : Z := 0xa59ac.
Definition A_ip_body : Z := 0xa5a84.
Definition A_ip_epi : Z := 0xa5d88.

Lemma sub_shift2m : forall base x,
Z_to_bv 64 (base mod 18446744073709551616 - (Z.shiftl (x mod 18446744073709551616) 2) mod 18446744073709551616) = Z_to_bv 64 (base - 4 * x).
Proof.
intros base x. apply Z_to_bv_eqm. change (2^64) with 18446744073709551616.
rewrite Zminus_mod_idemp_r, Zminus_mod_idemp_l. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
rewrite Zminus_mod, Zmult_mod_idemp_l, <- Zminus_mod. f_equal. lia.
Qed.

Definition ip_frame (c0 c8 c16 c24 c32 c40 c48 : cell) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
[c0; c8; c16; c24; c32; c40; c48; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition ip_fhdr (rest : list byte) : list cell :=
[C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x219d9); C8 (Z_to_bv 64 0xa5934); CB 224 rest].
Definition bF1 : byte := Z_to_bv 8 (-15).  Definition bF3 : byte := Z_to_bv 8 (-13).
Definition bF5 : byte := Z_to_bv 8 (-11).  Definition bF8 : byte := Z_to_bv 8 (-8).
Definition ip_shadow_live (rest : list byte) : list cell :=
map C1 (repeat bF1 4 ++ repeat z8 14 ++ repeat bF3 6) ++ [CB 8 rest].

Lemma ip_w1 : forall (usp lo E IP p : Z) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem),
stk asegs m lo usp -> lo <= usp - 160 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
client_consts m -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (j8 j16 j24 j32 j40 j48 : list byte),
ms = MS (mkR (Z_to_bv 64 RA_ip_smalloc) (Z_to_bv 64 (usp + -160)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -160))
(Z_to_bv 64 192) (Z_to_bv 64 g_shadow_memory_dynamic_address) (Z_to_bv 64 1) a3 a4 a5 a6 a7
s2 (Z_to_bv 64 IP) (Z_to_bv 64 E) s5 (Z_to_bv 64 p) s7 s8 (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_stack_malloc_2) fc None m1 (seg_rom asegs)
/\ munch [(usp + -160, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -160)
/\ rw_cells asegs m1 (usp + -160)
(ip_frame (C8 (Z_to_bv 64 0)) (CB 8 j8) (CB 8 j16) (CB 8 j24) (CB 8 j32) (CB 8 j40) (CB 8 j48) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) (Z_to_bv 64 IP) (Z_to_bv 64 p) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_interp_pitch) fc None m (seg_rom asegs)).
Proof.
intros until m. intros ST LO LOS SPH SP32 (G1 & G2 & G3 & G4) MI.
unfold A_interp_pitch, RA_ip_smalloc, e_stack_malloc_2, ip_frame,
g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -160, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 160%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 160 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
cbn [mk_CB_cells app] in FR.
ato 0xa5974. astep. rewrite land_m32_al by lia.
ato 0xa5998. rewrite sx32_small by (unfold int31; lia).
ato 0x5152c.
apply evt_done. do 7 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.

Lemma ip_seg_poison : forall (sf : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(js : list byte) F fc (m : mem),
rw_cells asegs m sf [CB 32 js] -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (rs : list byte),
ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 (-15)) (Z_to_bv 64 (-13)) a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 sf) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ip_body) fc None m1 (seg_rom asegs)
/\ munch [(sf, sf + 32)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ rw_cells asegs m1 sf (ip_shadow_live rs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 (-15)) (Z_to_bv 64 (-13)) a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 sf) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa5a24) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FRS MI.
unfold ip_shadow_live, A_ip_body, bF1, bF3, z8 in *. cbn [map repeat app] in *.
pose proof (rw_cells_bound _ _ _ _ FRS) as BS. cbn [cells_size csize Nat.add] in BS.
pose proof (munch_refl [(sf, sf + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0xa5a84.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact FRS].
Qed.

Lemma ip_w2 : forall (usp lo E IP p f sf : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word)
(c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) (j8 j16 j24 j32 j40 j48 jb js : list byte) F fc (m : mem),
stk asegs m lo (usp + -160) -> lo <= usp + -160 -> SH_HI <= lo -> usp < 2^63 ->
0 < f -> f mod 64 = 0 -> f + 256 <= lo -> f + 256 <= APP_TOP -> (f + 256 <= SH_LO \/ SH_HI <= f) -> sf = Z.shiftr f 3 + SHB ->
rw_cells asegs m (usp + -160)
(ip_frame (C8 (Z_to_bv 64 0)) (CB 8 j8) (CB 8 j16) (CB 8 j24) (CB 8 j32) (CB 8 j40) (CB 8 j48) c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
rw_cells asegs m f [CB 248 jb] -> rw_cells asegs m sf [CB 32 js] ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (a0' a1' a2' : word) (rb rs : list byte),
ms = MS (mkR (Z_to_bv 64 RA_ip_smalloc) (Z_to_bv 64 (usp + -160)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -160))
a0' a1' a2' (Z_to_bv 64 (-15)) (Z_to_bv 64 (-13)) a5 a6 a7
(Z_to_bv 64 p) (Z_to_bv 64 IP) (Z_to_bv 64 E) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (E - 4 * p)) (Z_to_bv 64 sf) (Z_to_bv 64 f)
(Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ip_body) fc None m1 (seg_rom asegs)
/\ munch [(usp + -160, usp); (f, f + 248); (sf, sf + 32)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -160)
/\ rw_cells asegs m1 (usp + -160)
(ip_frame (C8 (Z_to_bv 64 0)) (CB 8 j8) (CB 8 j16) (C8 (Z_to_bv 64 f)) (CB 8 j32) (CB 8 j40) (C8 (Z_to_bv 64 f))
c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra)
/\ rw_cells asegs m1 f (ip_fhdr rb) /\ rw_cells asegs m1 sf (ip_shadow_live rs))
(MS (mkR (Z_to_bv 64 RA_ip_smalloc) (Z_to_bv 64 (usp + -160)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -160)) (Z_to_bv 64 f)
a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 IP) (Z_to_bv 64 E) s5 (Z_to_bv 64 p) s7 s8 (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_ip_smalloc)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros ST LO LOS SPH F0 F64 FLO FTOP FSH Esf FR FRB FRS MI.
unfold ip_frame, ip_fhdr, ip_shadow_live, RA_ip_smalloc, A_ip_body, bF1, bF3 in *. unfold APP_TOP in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FSH as FSH'. unfold SH_LO, SH_HI in FSH'.
pose proof (shad_range_al f 256 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) ltac:(unfold APP_TOP; lia)) as SW.
rewrite <- shad_shiftr, <- Esf in SW. change (256 / 8) with 32 in SW. unfold SH_LO, SH_HI in SW.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -160, usp); (f, f + 248); (sf, sf + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
replace (ret_pc (Z_to_bv 64 0xa59ac)) with (Z_to_bv 64 0xa59ac) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
apply (rw_cells_split_CB asegs _ _ [] 248 _ [] [8; 8; 8; 224]%nat) in FRB; [| reflexivity]. cbn [mk_CB_cells app] in FRB.
astep. astep. astep. sh_if.
ato 0xa5a1c. astep. rewrite <- Esf. astep. rewrite sub_shift2m.
call (ip_seg_poison sf). { exact FRS. } { assumption. } rename POST into FRS'.
apply evt_done. do 6 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|]. split; [exact FRB| exact FRS'].
Qed.

Definition ip_shadow_scope (rest : list byte) : list cell :=
map C1 (repeat bF1 4 ++ repeat bF8 14 ++ repeat bF3 6) ++ [CB 8 rest].

Lemma ip_seg_f8 : forall (sf : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(rs : list byte) F fc (m : mem),
rw_cells asegs m sf (ip_shadow_live rs) -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-8)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 sf) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa5dc4) fc None m1 (seg_rom asegs)
/\ munch [(sf, sf + 32)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ rw_cells asegs m1 sf (ip_shadow_scope rs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 sf) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ip_epi) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FRS MI.
unfold ip_shadow_live, ip_shadow_scope, A_ip_epi, bF1, bF3, bF8, z8 in *. cbn [map repeat app] in *.
pose proof (rw_cells_bound _ _ _ _ FRS) as BS. cbn [cells_size csize Nat.add] in BS.
pose proof (munch_refl [(sf, sf + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0xa5dc4.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact FRS].
Qed.

Lemma ip_seg_f5 : forall (sf : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(rs : list byte) F fc (m : mem),
rw_cells asegs m sf (ip_shadow_scope rs) -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-11)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 sf) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa5e5c) fc None m1 (seg_rom asegs)
/\ munch [(sf, sf + 32)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ rw_cells asegs m1 sf (map C1 (repeat bF5 32)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 sf) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa5dd8) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FRS MI.
unfold ip_shadow_scope, bF1, bF3, bF5, bF8 in *. cbn [map repeat app] in *.
pose proof (rw_cells_bound _ _ _ _ FRS) as BS. cbn [cells_size csize Nat.add] in BS.
pose proof (munch_refl [(sf, sf + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0xa5e5c.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact FRS].
Qed.

Definition ip_shadow_dead : list cell := map C1 (repeat bF5 32).

Lemma ip_epi_a : forall (usp f sf : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s9 s10 s11 t3 t4 t5 t6 : word)
(c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra hd : word) (j8 j16 j32 j40 rs : list byte) F fc (m : mem),
0 < f -> f mod 64 = 0 -> f + 256 <= usp + -160 -> f + 256 <= APP_TOP -> (f + 256 <= SH_LO \/ SH_HI <= f) -> sf = Z.shiftr f 3 + SHB ->
SH_HI <= usp + -160 -> usp < 2^63 ->
rw_cells asegs m (usp + -160)
(ip_frame (C8 (Z_to_bv 64 0)) (CB 8 j8) (CB 8 j16) (C8 (Z_to_bv 64 f)) (CB 8 j32) (CB 8 j40) (C8 (Z_to_bv 64 f)) c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
rw_cells asegs m f [C8 hd] -> rw_cells asegs m sf (ip_shadow_live rs) ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR ra (Z_to_bv 64 (usp + -160)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -160)) (Z_to_bv 64 (-11)) (Z_to_bv 64 f) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 (Z_to_bv 64 sf) (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa5e5c) fc None m1 (seg_rom asegs)
/\ munch [(f, f + 248); (sf, sf + 32)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 (usp + -160)
(ip_frame (C8 (Z_to_bv 64 0)) (CB 8 j8) (CB 8 j16) (C8 (Z_to_bv 64 f)) (CB 8 j32) (CB 8 j40) (C8 (Z_to_bv 64 f)) c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra)
/\ rw_cells asegs m1 sf ip_shadow_dead)
(MS (mkR ra (Z_to_bv 64 (usp + -160)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -160)) a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 (Z_to_bv 64 sf) (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ip_epi) fc None m (seg_rom asegs)).
Proof.
intros until m. intros F0 F64 FLO FTOP FSH Esf LOS SPH FR FRB FRS MI.
unfold ip_frame, ip_shadow_live, ip_shadow_dead, A_ip_epi, bF1, bF3, bF5, z8 in *. cbn [map repeat app] in *. unfold APP_TOP in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FSH as FSH'. unfold SH_LO, SH_HI in FSH'.
pose proof (shad_range_al f 256 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) ltac:(unfold APP_TOP; lia)) as SW.
rewrite <- shad_shiftr, <- Esf in SW. change (256 / 8) with 32 in SW. unfold SH_LO, SH_HI in SW.
pose proof (munch_refl [(f, f + 248); (sf, sf + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
call (ip_seg_f8 sf). { exact FRS. } { assumption. } rename POST into FRS. unfold ip_shadow_scope, bF1, bF3, bF8 in FRS. cbn [map repeat app] in FRS.
ato 0xa5dd4. astep. sh_if.
call (ip_seg_f5 sf). { unfold ip_shadow_scope, bF1, bF3, bF8. cbn [map repeat app]. exact FRS. } { assumption. } rename POST into FRS. unfold bF5 in FRS. cbn [map repeat] in FRS.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FR| exact FRS].
Qed.

Lemma ip_epi_b : forall (usp lo f fl : Z) (ra gp tp t0 t1 t2 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) (j8 j16 j32 j40 : list byte) F fc (m : mem),
stk asegs m lo (usp + -160) -> lo <= usp + -160 -> usp < 2^63 -> 0 < f -> f + 256 <= lo ->
0 < fl -> fl + 1 <= lo ->
rw_cells asegs m (usp + -160)
(ip_frame (C8 (Z_to_bv 64 0)) (CB 8 j8) (CB 8 j16) (C8 (Z_to_bv 64 f)) (CB 8 j32) (CB 8 j40) (C8 (Z_to_bv 64 f)) c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
ro_cells asegs m (f + 248) [C8 (Z_to_bv 64 fl)] -> rw_cells asegs m fl [C1 (Z_to_bv 8 1)] ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (a0' : word),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 a0' (Z_to_bv 64 f) a2 a3 a4 a5 a6 a7 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom asegs)
/\ munch [(fl, fl + 1)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp
/\ rw_cells asegs m1 fl [C1 z8])
(MS (mkR ra (Z_to_bv 64 (usp + -160)) gp tp t0 t1 t2 (Z_to_bv 64 usp) s1 a0 (Z_to_bv 64 f) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa5e5c) fc None m (seg_rom asegs)).
Proof.
intros until m. intros ST LO SPH F0 FLO L0 LLO FR FLP FLG MI.
unfold ip_frame, z8 in *.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0xa5f04. release_frame FR ST usp. astep.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact FLG].
Qed.

Lemma ip_corr_acc : forall (m : mem) (f sf : Z) (rs : list byte),
rw_cells asegs m sf (ip_shadow_live rs) -> sf = Z.shiftr f 3 + SHB -> f mod 64 = 0 -> 0 <= f -> acc asegs m (f + 32) 112.
Proof.
intros m f sf rs [[_ B] _] Esf F64 F0. unfold ip_shadow_live in B.
rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B _].
assert (E : cells_bytes (map C1 (repeat bF1 4 ++ repeat z8 14 ++ repeat bF3 6)) = repeat bF1 4 ++ repeat z8 14 ++ repeat bF3 6) by reflexivity.
rewrite E in B. apply bytes_at_app in B. destruct B as [_ B]. apply bytes_at_app in B. destruct B as [B _].
change (Z.of_nat (length (repeat bF1 4))) with 4 in B.
change 112 with (8 * Z.of_nat 14). apply acc_zero_run; [clear - F64; Z.div_mod_to_equations; lia | lia |].
replace (shad (f + 32)) with (sf + 4); [exact B|].
rewrite Esf, shad_shiftr. unfold shad. clear - F64. Z.div_mod_to_equations. lia.
Qed.
