(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05q X05l.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0z5.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation mem := (word -> option byte).

Definition A_interp_pitch : Z := 0xa954c.
Definition e_stack_malloc_2 : Z := 0x51618.
Definition RA_ip_smalloc : Z := 0xa95c4.
Definition A_ip_body : Z := 0xa96dc.
Definition A_ip_epi : Z := 0xa9b10.

Definition ip_frame (c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 : cell) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
[c0; c8; c16; c24; c32; c40; c48; c56; c64; c72; c80; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition ip_fhdr (rest : list byte) : list cell :=
[C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x21a13); C8 (Z_to_bv 64 0xa954c); CB 224 rest].
Definition bF1 : byte := Z_to_bv 8 (-15).  Definition bF3 : byte := Z_to_bv 8 (-13).
Definition bF5 : byte := Z_to_bv 8 (-11).  Definition bF8 : byte := Z_to_bv 8 (-8).
Definition ip_shadow_live (rest : list byte) : list cell :=
map C1 (repeat bF1 4 ++ repeat z8 14 ++ repeat bF3 6) ++ [CB 8 rest].

Lemma ip_w1 : forall (usp lo E IP p : Z) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem),
stk bsegs m lo usp -> lo <= usp - 192 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
client_constsB m -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (j8 j16 j24 j32 j40 j48 j64 j72 j80 : list byte),
ms = MS (mkR (Z_to_bv 64 RA_ip_smalloc) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 192) (Z_to_bv 64 gB_shadow_memory_dynamic_address) (Z_to_bv 64 1) a3 a4 a5 a6 a7
(Z_to_bv 64 p) s3 (Z_to_bv 64 E) s5 s6 s7 (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_stack_malloc_2) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -192, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -192)
/\ rw_cells bsegs m1 (usp + -192)
(ip_frame (C8 (Z_to_bv 64 0)) (CB 8 j8) (CB 8 j16) (CB 8 j24) (CB 8 j32) (CB 8 j40) (CB 8 j48) (C8 (Z_to_bv 64 IP)) (CB 8 j64) (CB 8 j72) (CB 8 j80)
s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) (Z_to_bv 64 IP) (Z_to_bv 64 p) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_interp_pitch) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST LO LOS SPH SP32 (G1 & G2 & G3 & G4) MI.
unfold A_interp_pitch, RA_ip_smalloc, e_stack_malloc_2, ip_frame,
gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -192, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
carve_frame 192%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 192 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
cbn [mk_CB_cells app] in FR.
ato 0xa958c. astep. rewrite land_m32_al by lia.

ato 0xa95b0. rewrite sx32_small by (unfold int31; lia).
ato 0x51618.

apply evt_done. do 10 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.

Lemma sub_shift2 : forall base x,
Z_to_bv 64 (base - (Z.shiftl (x mod 18446744073709551616) 2) mod 18446744073709551616) = Z_to_bv 64 (base - 4 * x).
Proof.
intros base x. apply Z_to_bv_eqm. change (2^64) with 18446744073709551616.
rewrite Zminus_mod_idemp_r. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
rewrite Zminus_mod, Zmult_mod_idemp_l, <- Zminus_mod. f_equal. lia.
Qed.

Lemma lxor_sign_mod : forall p, -2^63 <= p < 2^63 -> Z.lxor (p mod 18446744073709551616) 9223372036854775808 = p + 9223372036854775808.
Proof.
intros p Hp. change 9223372036854775808 with (2^63). rewrite zb_lxor_sign by (split; [apply Z.mod_pos_bound | apply Z.mod_pos_bound]; lia).
change 18446744073709551616 with (2^64). rewrite Zplus_mod_idemp_l. apply Z.mod_small. lia.
Qed.

Lemma ip_sgn_guard : forall E p, Z.lxor (Z.lxor (Z.b2z (E - 4 * p <? E)) (Z.b2z (p + 9223372036854775808 <? 9223372036854775809))) 1 = 0.
Proof.
intros E p. destruct (E - 4 * p <? E) eqn:H1; destruct (p + 9223372036854775808 <? 9223372036854775809) eqn:H2;
try apply Z.ltb_lt in H1; try apply Z.ltb_lt in H2; try apply Z.ltb_ge in H1; try apply Z.ltb_ge in H2; try lia; reflexivity.
Qed.

Lemma ip_w2 : forall (usp lo E IP p f sf : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
(c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) (j8 j16 j24 j32 j40 j48 j64 j72 j80 jb js : list byte) F fc (m : mem),
stk bsegs m lo (usp + -192) -> lo <= usp + -192 -> SH_HI <= lo -> usp < 2^63 ->
0 < f -> f mod 64 = 0 -> f + 256 <= lo -> f + 256 <= APP_TOP -> (f + 256 <= SH_LO \/ SH_HI <= f) -> sf = Z.shiftr f 3 + SHB ->
0 < E -> E < 2^62 -> 12 < E - 4 * p -> E - 4 * p < 2^62 -> -2^20 <= p <= 2^20 ->
rw_cells bsegs m (usp + -192)
(ip_frame (C8 (Z_to_bv 64 0)) (CB 8 j8) (CB 8 j16) (CB 8 j24) (CB 8 j32) (CB 8 j40) (CB 8 j48) (C8 (Z_to_bv 64 IP)) (CB 8 j64) (CB 8 j72) (CB 8 j80)
c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
rw_cells bsegs m f [CB 248 jb] -> rw_cells bsegs m sf [CB 32 js] ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (a0' a1' a2' : word) (rb rs : list byte),
ms = MS (mkR (Z_to_bv 64 RA_ip_smalloc) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
a0' a1' a2' (Z_to_bv 64 sf) (Z_to_bv 64 (-15)) (Z_to_bv 64 (-13)) (Z_to_bv 64 f) a7
(Z_to_bv 64 (E - 4 * p - 12)) s3 (Z_to_bv 64 E) s5 s6 s7 (Z_to_bv 64 SHB) (Z_to_bv 64 1) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ip_body) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -192, usp); (f, f + 248); (sf, sf + 32)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -192)
/\ rw_cells bsegs m1 (usp + -192)
(ip_frame (C8 (Z_to_bv 64 0)) (CB 8 j8) (C8 (Z_to_bv 64 sf)) (C8 (Z_to_bv 64 f)) (C8 (Z_to_bv 64 f)) (C8 (Z_to_bv 64 p)) (CB 8 j48) (C8 (Z_to_bv 64 IP))
(CB 8 j64) (CB 8 j72) (C8 (Z_to_bv 64 f)) c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra)
/\ rw_cells bsegs m1 f (ip_fhdr rb) /\ rw_cells bsegs m1 sf (ip_shadow_live rs))
(MS (mkR (Z_to_bv 64 RA_ip_smalloc) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192)) (Z_to_bv 64 f)
a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 p) s3 (Z_to_bv 64 E) s5 s6 s7 (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_ip_smalloc)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST LO LOS SPH F0 F64 FLO FTOP FSH Esf E0 E62 EP12 EP62 PR FR FRB FRS MI.
unfold ip_frame, ip_fhdr, ip_shadow_live, RA_ip_smalloc, A_ip_body, bF1, bF3 in *. unfold APP_TOP in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FSH as FSH'. unfold SH_LO, SH_HI in FSH'.
pose proof (shad_range_al f 256 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) ltac:(unfold APP_TOP; lia)) as SW.
rewrite <- shad_shiftr, <- Esf in SW. change (256 / 8) with 32 in SW. unfold SH_LO, SH_HI in SW.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -192, usp); (f, f + 248); (sf, sf + 32)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
replace (ret_pc (Z_to_bv 64 0xa95c4)) with (Z_to_bv 64 0xa95c4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
apply (rw_cells_split_CB bsegs _ _ [] 248 _ [] [8; 8; 8; 224]%nat) in FRB; [| reflexivity]. cbn [mk_CB_cells app] in FRB.
apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 8]%nat) in FRS; [| reflexivity].
cbn [mk_CB_cells app] in FRS.
astep. astep. astep. sh_if.
ato 0xa9630. astep. rewrite <- Esf.

replace (0 <? E) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
ato 0xa9650. rewrite sub_shift2.
bato 0xa96c0. rewrite (lxor_sign_mod p) by lia. rewrite ip_sgn_guard.
bato 0xa96dc.

replace (E - 4 * p + -12) with (E - 4 * p - 12) by lia.
apply evt_done. do 6 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|]. split; [exact FRB|].
cbn [map repeat app]. exact FRS.
Qed.

Definition ip_shadow_scope (rest : list byte) : list cell :=
map C1 (repeat bF1 4 ++ repeat bF8 14 ++ repeat bF3 6) ++ [CB 8 rest].

Lemma ip_seg_f8 : forall (sf : Z) (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(rs : list byte) F fc (m : mem),
rw_cells bsegs m sf (ip_shadow_live rs) -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-8)) a1 (Z_to_bv 64 sf) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa9b50) fc None m1 (seg_rom bsegs)
/\ munch [(sf, sf + 32)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ rw_cells bsegs m1 sf (ip_shadow_scope rs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-8)) a1 (Z_to_bv 64 sf) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa9b18) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FRS MI.
unfold ip_shadow_live, ip_shadow_scope, bF1, bF3, bF8, z8 in *. cbn [map repeat app] in *.
pose proof (rw_cells_bound _ _ _ _ FRS) as BS. cbn [cells_size csize Nat.add] in BS.
pose proof (munch_refl [(sf, sf + 32)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
ato 0xa9b50.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact FRS].
Qed.

Lemma ip_seg_f5 : forall (sf : Z) (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(rs : list byte) F fc (m : mem),
rw_cells bsegs m sf (ip_shadow_scope rs) -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-11)) a1 (Z_to_bv 64 sf) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa9bec) fc None m1 (seg_rom bsegs)
/\ munch [(sf, sf + 32)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ rw_cells bsegs m1 sf (map C1 (repeat bF5 32)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-11)) a1 (Z_to_bv 64 sf) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa9b6c) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FRS MI.
unfold ip_shadow_scope, bF1, bF3, bF5, bF8 in *. cbn [map repeat app] in *.
pose proof (rw_cells_bound _ _ _ _ FRS) as BS. cbn [cells_size csize Nat.add] in BS.
pose proof (munch_refl [(sf, sf + 32)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
ato 0xa9bec.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact FRS].
Qed.

Definition ip_shadow_dead : list cell := map C1 (repeat bF5 32).

Lemma ip_epi_a : forall (usp f sf : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra hd : word) (w40 w48 w56 w80 : word) (j8 j64 j72 rs : list byte) F fc (m : mem),
0 < f -> f mod 64 = 0 -> f + 256 <= usp + -192 -> f + 256 <= APP_TOP -> (f + 256 <= SH_LO \/ SH_HI <= f) -> sf = Z.shiftr f 3 + SHB ->
SH_HI <= usp + -192 -> usp < 2^63 ->
rw_cells bsegs m (usp + -192)
(ip_frame (C8 (Z_to_bv 64 0)) (CB 8 j8) (C8 (Z_to_bv 64 sf)) (C8 (Z_to_bv 64 f)) (C8 (Z_to_bv 64 f)) (C8 w40) (C8 w48) (C8 w56) (CB 8 j64) (CB 8 j72) (C8 w80) c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
rw_cells bsegs m f [C8 hd] -> rw_cells bsegs m sf (ip_shadow_live rs) ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR ra (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192)) (Z_to_bv 64 (-11)) (Z_to_bv 64 f) (Z_to_bv 64 sf) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa9bec) fc None m1 (seg_rom bsegs)
/\ munch [(f, f + 248); (sf, sf + 32)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 (usp + -192)
(ip_frame (C8 (Z_to_bv 64 0)) (CB 8 j8) (C8 (Z_to_bv 64 sf)) (C8 (Z_to_bv 64 f)) (C8 (Z_to_bv 64 f)) (C8 w40) (C8 w48) (C8 w56) (CB 8 j64) (CB 8 j72) (C8 w80) c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra)
/\ rw_cells bsegs m1 sf ip_shadow_dead)
(MS (mkR ra (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192)) a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ip_epi) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros F0 F64 FLO FTOP FSH Esf LOS SPH FR FRB FRS MI.
unfold ip_frame, ip_shadow_dead, A_ip_epi in *. unfold APP_TOP in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FSH as FSH'. unfold SH_LO, SH_HI in FSH'.
pose proof (shad_range_al f 256 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) ltac:(unfold APP_TOP; lia)) as SW.
rewrite <- shad_shiftr, <- Esf in SW. change (256 / 8) with 32 in SW. unfold SH_LO, SH_HI in SW.
pose proof (munch_refl [(f, f + 248); (sf, sf + 32)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
ato 0xa9b18.
call (ip_seg_f8 sf). { exact FRS. } { assumption. } rename POST into FRS. unfold ip_shadow_scope, bF1, bF3, bF8 in FRS. cbn [map repeat app] in FRS.
ato 0xa9b64. astep. sh_if.
ato 0xa9b6c.
call (ip_seg_f5 sf). { unfold ip_shadow_scope, bF1, bF3, bF8. cbn [map repeat app]. exact FRS. } { assumption. } rename POST into FRS. unfold bF5 in FRS. cbn [map repeat] in FRS.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FR| exact FRS].
Qed.

Lemma ip_epi_b : forall (usp lo f fl : Z) (ra gp tp t0 t1 t2 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) (k16 k24 k32 k40 k48 k56 k80 : word) (j8 j64 j72 : list byte) F fc (m : mem),
stk bsegs m lo (usp + -192) -> lo <= usp + -192 -> usp < 2^63 -> 0 < f -> f + 256 <= lo ->
0 < fl -> fl + 1 <= lo ->
rw_cells bsegs m (usp + -192)
(ip_frame (C8 (Z_to_bv 64 0)) (CB 8 j8) (C8 k16) (C8 k24) (C8 k32) (C8 k40) (C8 k48) (C8 k56) (CB 8 j64) (CB 8 j72) (C8 k80)
c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
ro_cells bsegs m (f + 248) [C8 (Z_to_bv 64 fl)] -> rw_cells bsegs m fl [C1 (Z_to_bv 8 1)] ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 fl) (Z_to_bv 64 f) a2 a3 a4 a5 a6 a7 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom bsegs)
/\ munch [(fl, fl + 1)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp
/\ rw_cells bsegs m1 fl [C1 z8])
(MS (mkR ra (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) s1 a0 (Z_to_bv 64 f) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa9bec) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST LO SPH F0 FLO L0 LLO FR FLP FLG MI.
unfold ip_frame, z8 in *.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
ato 0xa9c90. release_frame FR ST usp. astep. astep.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact FLG].
Qed.

Lemma ip_corr_acc : forall (m : mem) (f sf : Z) (rs : list byte),
rw_cells bsegs m sf (ip_shadow_live rs) -> sf = Z.shiftr f 3 + SHB -> f mod 64 = 0 -> 0 <= f -> acc bsegs m (f + 32) 112.
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

