(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1dg X1df X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X081 X05l X07y X05m X09f X06d X069.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X12b X0z5 X0ys X0yq X0x2.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0z5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_stack_malloc_0i : Z := 0x51314.
Definition e_calloc_i : Z := 0x67f88.
Definition RA_sbinit_smalloc : Z := 0xbcc80.
Definition RA_sbinit_calloc0 : Z := 0xbcd18.
Definition A_sbinit_epi : Z := 0xbd14c.

Notation sbi_desc_cells c0 c1 c2 c3 c4 c5 c6 c7 c9 c10 c11 c12 :=
[C8 c0; C8 c1; C8 c2; C4 c3; C4 c4; C8 c5; C8 c6; C8 c7; C8 (Z_to_bv 64 A_sb_decoder_init); C8 c9; C8 c10; C8 c11; C8 c12] (only parsing).

Notation sbi_frame c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra :=
[C8 (Z_to_bv 64 0); c8; c16; c24; c32; c40; c48; c56; c64; c72; c80; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
(only parsing).

Lemma sbinit_w1 : forall (usp lo MP : Z) (c0 c1 c2 c3 c4 c5 c6 c7 c9 c10 c11 c12 : word)
(ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
ro_cells bsegs m MP (sbi_desc_cells c0 c1 c2 c3 c4 c5 c6 c7 c9 c10 c11 c12) -> aobj bsegs m MP 96 -> MP mod 8 = 0 -> 0x10000 <= MP -> MP + 104 <= 0x65a180 ->
stk bsegs m lo usp -> lo <= usp - 192 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
client_constsB m -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 : list byte) (xt1 xa3 : word),
ms = MS (mkR (Z_to_bv 64 RA_sbinit_smalloc) (Z_to_bv 64 (usp + -192)) gp tp t0 xt1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 64) (Z_to_bv 64 gB_shadow_memory_dynamic_address) (Z_to_bv 64 1) xa3 a4 a5 a6 a7
s2 s3 (Z_to_bv 64 MP) s5 s6 s7 s8 s9 (Z_to_bv 64 SHB) s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_stack_malloc_0i) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -192, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -192)
/\ rw_cells bsegs m1 (usp + -192)
(sbi_frame (CB 8 j8) (CB 8 j16) (CB 8 j24) (CB 8 j32) (CB 8 j40) (CB 8 j48) (CB 8 j56) (CB 8 j64) (CB 8 j72) (CB 8 j80) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 MP) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_speex_decoder_init) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ND OBM AL8 MPLO MPHI ST LO LOS SPH SP32 (G1 & G2 & G3 & G4) MI.
unfold A_speex_decoder_init, RA_sbinit_smalloc, e_stack_malloc_0i, A_sb_decoder_init,
gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'.
pose proof (munch_refl [(usp + -192, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -192, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 192%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 192 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
bato 0xbcc10.
bato 0xbcc50. astep. rewrite land_m32_al by lia.
bato 0xbcc6c. rewrite sx32_small by (unfold int31; lia).
bato 0x51314.
apply evt_done. do 13 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.

Notation sbi_fhdr j24 l32 j36 j40 :=
[C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x10d89); C8 (Z_to_bv 64 0xbcc10); CB 8 j24; CB 4 l32; CB 4 j36; CB 16 j40] (only parsing).
Notation sbi_shadow b4 :=
[C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 b4; C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))]
(only parsing).

Lemma sbinit_w2 : forall (usp lo MP f sf : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
(c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) (j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 jb js : list byte) F fc (m : mem),
stk bsegs m lo (usp + -192) -> lo <= usp + -192 -> SH_HI <= lo -> usp < 2^63 ->
0 < f -> f mod 64 = 0 -> f + 64 <= lo -> f + 64 <= APP_TOP -> (f + 64 <= SH_LO \/ SH_HI <= f) -> sf = Z.shiftr f 3 + SHB ->
rw_cells bsegs m (usp + -192)
(sbi_frame (CB 8 j8) (CB 8 j16) (CB 8 j24) (CB 8 j32) (CB 8 j40) (CB 8 j48) (CB 8 j56) (CB 8 j64) (CB 8 j72) (CB 8 j80) c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
rw_cells bsegs m f [CB 56 jb] -> rw_cells bsegs m sf [CB 8 js] ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (xa2 xa3 : word) (k24 l32 k36 k40 : list byte),
ms = MS (mkR (Z_to_bv 64 RA_sbinit_calloc0) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 160) (Z_to_bv 64 1) xa2 xa3 a4 a5 a6 a7
(Z_to_bv 64 f) s3 (Z_to_bv 64 MP) (Z_to_bv 64 sf) s6 s7 s8 s9 (Z_to_bv 64 SHB) (Z_to_bv 64 f) t3 t4 t5 t6)
F (Z_to_bv 64 e_calloc_i) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -192, usp); (f, f + 56); (sf, sf + 8)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -192)
/\ rw_cells bsegs m1 (usp + -192)
(sbi_frame (CB 8 j8) (CB 8 j16) (CB 8 j24) (CB 8 j32) (CB 8 j40) (CB 8 j48) (CB 8 j56) (CB 8 j64) (CB 8 j72) (C8 (Z_to_bv 64 f)) c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra)
/\ rw_cells bsegs m1 f (sbi_fhdr k24 l32 k36 k40) /\ rw_cells bsegs m1 sf (sbi_shadow (Z_to_bv 8 4)))
(MS (mkR (Z_to_bv 64 RA_sbinit_smalloc) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192)) (Z_to_bv 64 f)
a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 MP) s5 s6 s7 s8 s9 (Z_to_bv 64 SHB) s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbinit_smalloc)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST LO LOS SPH F0 F64 FLO FTOP FSH Esf FR FRB FRS MI.
unfold RA_sbinit_smalloc, RA_sbinit_calloc0, e_calloc_i in *.
replace (ret_pc (Z_to_bv 64 0xbcc80)) with (Z_to_bv 64 0xbcc80) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'.
assert (SFR : SH_LO <= sf /\ sf + 8 <= SH_HI) by (subst sf; pose proof (shad_range_al f 64 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) FTOP) as X; rewrite shad_shiftr; unfold shad in *; change (64 / 8) with 8 in X; lia).
pose proof (munch_refl [(usp + -192, usp); (f, f + 56); (sf, sf + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
apply (rw_cells_split_CB bsegs _ _ [] 56 _ [] [8; 8; 8; 8; 4; 4; 16]%nat) in FRB; [| reflexivity]. cbn [mk_CB_cells app] in FRB.
apply (rw_cells_split_CB bsegs _ _ [] 8 _ [] [1; 1; 1; 1; 1; 1; 1; 1]%nat) in FRS; [| reflexivity]. cbn [mk_CB_cells app] in FRS.
astep. astep. astep. astep. sh_if.
bato 0xbcce4. astep. rewrite <- Esf.
bato 0x67f88.
apply evt_done. do 7 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|]. split; [exact FRB| exact FRS].
Qed.

Lemma sbinit_epi_a : forall (usp f sf : Z) (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
(hd : word) (b4 : byte) F fc (m : mem),
0 < f -> f mod 64 = 0 -> f + 64 <= usp + -192 -> f + 64 <= APP_TOP -> (f + 64 <= SH_LO \/ SH_HI <= f) -> sf = Z.shiftr f 3 + SHB ->
SH_HI <= usp + -192 -> usp < 2^63 ->
rw_cells bsegs m f [C8 hd] -> rw_cells bsegs m sf (sbi_shadow b4) ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR ra (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) s1 (Z_to_bv 64 (-11)) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 f) s3 s4 (Z_to_bv 64 sf) s6 s7 s8 s9 s10 (Z_to_bv 64 f) t3 t4 t5 t6)
F (Z_to_bv 64 0xbd188) fc None m1 (seg_rom bsegs)
/\ munch [(f, f + 56); (sf, sf + 8)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 sf (map C1 (repeat bF5 8)))
(MS (mkR ra (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 f) s3 s4 (Z_to_bv 64 sf) s6 s7 s8 s9 s10 (Z_to_bv 64 f) t3 t4 t5 t6)
F (Z_to_bv 64 A_sbinit_epi) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros F0 F64 FLO FTOP FSH Esf LOS SPH FRB FRS MI.
unfold A_sbinit_epi, bF5 in *. cbn [map repeat] in *. unfold APP_TOP in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FSH as FSH'. unfold SH_LO, SH_HI in FSH'.
pose proof (shad_range_al f 64 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) ltac:(unfold APP_TOP; lia)) as SW.
rewrite <- shad_shiftr, <- Esf in SW. change (64 / 8) with 8 in SW. unfold SH_LO, SH_HI in SW.
pose proof (munch_refl [(f, f + 56); (sf, sf + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
bato 0xbd160. astep. sh_if.
bato 0xbd188.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact FRS].
Qed.

Lemma sbinit_epi_b : forall (usp lo f fl S : Z) (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(j8 j16 j64 j72 : list byte) (w24 w32 w40 w48 w56 w80 : word) (c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) F fc (m : mem),
stk bsegs m lo (usp + -192) -> lo <= usp + -192 -> usp < 2^63 -> 0 < f -> f + 64 <= lo ->
0 < fl -> fl + 1 <= lo ->
rw_cells bsegs m (usp + -192) (sbi_frame (CB 8 j8) (CB 8 j16) (C8 w24) (C8 w32) (C8 w40) (C8 w48) (C8 w56) (CB 8 j64) (CB 8 j72) (C8 w80) c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
ro_cells bsegs m (f + 56) [C8 (Z_to_bv 64 fl)] -> rw_cells bsegs m fl [C1 (Z_to_bv 8 1)] ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom bsegs)
/\ munch [(fl, fl + 1)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp
/\ rw_cells bsegs m1 fl [C1 z8])
(MS (mkR ra (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 f) (Z_to_bv 64 S) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xbd188) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST LO SPH F0 FLO L0 LLO FR FLP FLG MI.
unfold z8 in *.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
bato 0xbd1f4. release_frame FR ST usp. astep.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact FLG].
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_stack_malloc_0i : Z := 0x51228.
Definition e_calloc_i : Z := 0x67e9c.
Definition RA_sbinit_smalloc : Z := 0xb5210.
Definition RA_sbinit_calloc0 : Z := 0xb52a8.
Definition A_sbinit_epi : Z := 0xb568c.

Notation sbi_desc_cells c0 c1 c2 c3 c4 c5 c6 c7 c9 c10 c11 c12 :=
[C8 c0; C8 c1; C8 c2; C4 c3; C4 c4; C8 c5; C8 c6; C8 c7; C8 (Z_to_bv 64 A_sb_decoder_init); C8 c9; C8 c10; C8 c11; C8 c12] (only parsing).

Notation sbi_frame c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra :=
[C8 (Z_to_bv 64 0); c8; c16; c24; c32; c40; c48; c56; c64; c72; c80; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
(only parsing).

Lemma sbinit_w1 : forall (usp lo MP : Z) (c0 c1 c2 c3 c4 c5 c6 c7 c9 c10 c11 c12 : word)
(ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
ro_cells asegs m MP (sbi_desc_cells c0 c1 c2 c3 c4 c5 c6 c7 c9 c10 c11 c12) -> aobj asegs m MP 96 -> MP mod 8 = 0 -> 0x10000 <= MP -> MP + 104 <= 0x652000 ->
stk asegs m lo usp -> lo <= usp - 192 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
client_consts m -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 : list byte) (xt1 xa3 : word),
ms = MS (mkR (Z_to_bv 64 RA_sbinit_smalloc) (Z_to_bv 64 (usp + -192)) gp tp t0 xt1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 64) (Z_to_bv 64 g_shadow_memory_dynamic_address) (Z_to_bv 64 1) xa3 a4 a5 a6 a7
s2 s3 (Z_to_bv 64 MP) s5 s6 s7 s8 s9 (Z_to_bv 64 SHB) s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_stack_malloc_0i) fc None m1 (seg_rom asegs)
/\ munch [(usp + -192, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -192)
/\ rw_cells asegs m1 (usp + -192)
(sbi_frame (CB 8 j8) (CB 8 j16) (CB 8 j24) (CB 8 j32) (CB 8 j40) (CB 8 j48) (CB 8 j56) (CB 8 j64) (CB 8 j72) (CB 8 j80) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 MP) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_speex_decoder_init) fc None m (seg_rom asegs)).
Proof.
intros until m. intros ND OBM AL8 MPLO MPHI ST LO LOS SPH SP32 (G1 & G2 & G3 & G4) MI.
unfold A_speex_decoder_init, RA_sbinit_smalloc, e_stack_malloc_0i, A_sb_decoder_init,
g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'.
pose proof (munch_refl [(usp + -192, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -192, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 192%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 192 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xb51a0.
ato 0xb51e0. astep. rewrite land_m32_al by lia.
ato 0xb51fc. rewrite sx32_small by (unfold int31; lia).
ato 0x51228.
apply evt_done. do 13 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.

Notation sbi_fhdr j24 l32 j36 j40 :=
[C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x10d71); C8 (Z_to_bv 64 0xb51a0); CB 8 j24; CB 4 l32; CB 4 j36; CB 16 j40] (only parsing).
Notation sbi_shadow b4 :=
[C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 b4; C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))]
(only parsing).

Lemma sbinit_w2 : forall (usp lo MP f sf : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
(c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) (j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 jb js : list byte) F fc (m : mem),
stk asegs m lo (usp + -192) -> lo <= usp + -192 -> SH_HI <= lo -> usp < 2^63 ->
0 < f -> f mod 64 = 0 -> f + 64 <= lo -> f + 64 <= APP_TOP -> (f + 64 <= SH_LO \/ SH_HI <= f) -> sf = Z.shiftr f 3 + SHB ->
rw_cells asegs m (usp + -192)
(sbi_frame (CB 8 j8) (CB 8 j16) (CB 8 j24) (CB 8 j32) (CB 8 j40) (CB 8 j48) (CB 8 j56) (CB 8 j64) (CB 8 j72) (CB 8 j80) c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
rw_cells asegs m f [CB 56 jb] -> rw_cells asegs m sf [CB 8 js] ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (xa2 xa3 : word) (k24 l32 k36 k40 : list byte),
ms = MS (mkR (Z_to_bv 64 RA_sbinit_calloc0) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 160) (Z_to_bv 64 1) xa2 xa3 a4 a5 a6 a7
s2 s3 (Z_to_bv 64 MP) (Z_to_bv 64 f) s6 (Z_to_bv 64 sf) s8 s9 (Z_to_bv 64 SHB) (Z_to_bv 64 f) t3 t4 t5 t6)
F (Z_to_bv 64 e_calloc_i) fc None m1 (seg_rom asegs)
/\ munch [(usp + -192, usp); (f, f + 56); (sf, sf + 8)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -192)
/\ rw_cells asegs m1 (usp + -192)
(sbi_frame (CB 8 j8) (CB 8 j16) (CB 8 j24) (CB 8 j32) (CB 8 j40) (CB 8 j48) (CB 8 j56) (CB 8 j64) (CB 8 j72) (C8 (Z_to_bv 64 f)) c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra)
/\ rw_cells asegs m1 f (sbi_fhdr k24 l32 k36 k40) /\ rw_cells asegs m1 sf (sbi_shadow (Z_to_bv 8 4)))
(MS (mkR (Z_to_bv 64 RA_sbinit_smalloc) (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192)) (Z_to_bv 64 f)
a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 MP) s5 s6 s7 s8 s9 (Z_to_bv 64 SHB) s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbinit_smalloc)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros ST LO LOS SPH F0 F64 FLO FTOP FSH Esf FR FRB FRS MI.
unfold RA_sbinit_smalloc, RA_sbinit_calloc0, e_calloc_i in *.
replace (ret_pc (Z_to_bv 64 0xb5210)) with (Z_to_bv 64 0xb5210) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'.
assert (SFR : SH_LO <= sf /\ sf + 8 <= SH_HI) by (subst sf; pose proof (shad_range_al f 64 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) FTOP) as X; rewrite shad_shiftr; unfold shad in *; change (64 / 8) with 8 in X; lia).
pose proof (munch_refl [(usp + -192, usp); (f, f + 56); (sf, sf + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
apply (rw_cells_split_CB asegs _ _ [] 56 _ [] [8; 8; 8; 8; 4; 4; 16]%nat) in FRB; [| reflexivity]. cbn [mk_CB_cells app] in FRB.
apply (rw_cells_split_CB asegs _ _ [] 8 _ [] [1; 1; 1; 1; 1; 1; 1; 1]%nat) in FRS; [| reflexivity]. cbn [mk_CB_cells app] in FRS.
astep. astep. astep. astep. sh_if.
ato 0xb5274. astep. rewrite <- Esf.
ato 0x67e9c.
apply evt_done. do 7 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|]. split; [exact FRB| exact FRS].
Qed.

Lemma sbinit_epi_a : forall (usp f sf : Z) (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s9 s10 t3 t4 t5 t6 : word)
(hd : word) (b4 : byte) F fc (m : mem),
0 < f -> f mod 64 = 0 -> f + 64 <= usp + -192 -> f + 64 <= APP_TOP -> (f + 64 <= SH_LO \/ SH_HI <= f) -> sf = Z.shiftr f 3 + SHB ->
SH_HI <= usp + -192 -> usp < 2^63 ->
rw_cells asegs m f [C8 hd] -> rw_cells asegs m sf (sbi_shadow b4) ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR ra (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) s1 (Z_to_bv 64 (-11)) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 (Z_to_bv 64 f) s6 (Z_to_bv 64 sf) s8 s9 s10 (Z_to_bv 64 f) t3 t4 t5 t6)
F (Z_to_bv 64 0xb56c8) fc None m1 (seg_rom asegs)
/\ munch [(f, f + 56); (sf, sf + 8)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 sf (map C1 (repeat bF5 8)))
(MS (mkR ra (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 (Z_to_bv 64 f) s6 (Z_to_bv 64 sf) s8 s9 s10 (Z_to_bv 64 f) t3 t4 t5 t6)
F (Z_to_bv 64 A_sbinit_epi) fc None m (seg_rom asegs)).
Proof.
intros until m. intros F0 F64 FLO FTOP FSH Esf LOS SPH FRB FRS MI.
unfold A_sbinit_epi, bF5 in *. cbn [map repeat] in *. unfold APP_TOP in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FSH as FSH'. unfold SH_LO, SH_HI in FSH'.
pose proof (shad_range_al f 64 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) ltac:(unfold APP_TOP; lia)) as SW.
rewrite <- shad_shiftr, <- Esf in SW. change (64 / 8) with 8 in SW. unfold SH_LO, SH_HI in SW.
pose proof (munch_refl [(f, f + 56); (sf, sf + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0xb56a0. astep. sh_if.
ato 0xb56c8.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact FRS].
Qed.

Lemma sbinit_epi_b : forall (usp lo f fl S : Z) (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(j8 j16 j64 j72 : list byte) (w24 w32 w40 w48 w56 w80 : word) (c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) F fc (m : mem),
stk asegs m lo (usp + -192) -> lo <= usp + -192 -> usp < 2^63 -> 0 < f -> f + 64 <= lo ->
0 < fl -> fl + 1 <= lo ->
rw_cells asegs m (usp + -192) (sbi_frame (CB 8 j8) (CB 8 j16) (C8 w24) (C8 w32) (C8 w40) (C8 w48) (C8 w56) (CB 8 j64) (CB 8 j72) (C8 w80) c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
ro_cells asegs m (f + 56) [C8 (Z_to_bv 64 fl)] -> rw_cells asegs m fl [C1 (Z_to_bv 8 1)] ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom asegs)
/\ munch [(fl, fl + 1)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp
/\ rw_cells asegs m1 fl [C1 z8])
(MS (mkR ra (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 usp) s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 S) s4 (Z_to_bv 64 f) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xb56c8) fc None m (seg_rom asegs)).
Proof.
intros until m. intros ST LO SPH F0 FLO L0 LLO FR FLP FLG MI.
unfold z8 in *.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0xb5734. release_frame FR ST usp. astep.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact FLG].
Qed.
