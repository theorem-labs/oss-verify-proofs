(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1dg X1df X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X081 X05l X07y X05m X09f X06d X069.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require X1dk.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X12b X0z5 X0ys X0yq X0x2.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1dk.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec.X1r2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec.X1nt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec.X1rh OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec.X1re.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X0j9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X09f OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X06d.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0z5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation mem := (word -> option byte).

Definition e_stack_malloc_0 : Z := 0x51314.
Definition RA_sbctl_smalloc : Z := 0xbd5fc.
Definition A_sbctl_epi : Z := 0xbe340.

Definition sbctl_frame (c8 : cell) (s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
[C8 (Z_to_bv 64 0); c8; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition sb_desc_cells (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : word) : list cell :=
[C8 c0; C8 c1; C8 c2; C4 c3; C4 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 (Z_to_bv 64 A_sb_decoder_ctl)].

Lemma sbctl_w1 : forall (usp lo S MP P c : Z) (hrest : list cell) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : word)
(ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m S (C8 (Z_to_bv 64 MP) :: hrest) -> Z.of_nat (cells_size hrest) = 40 ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 < 2^63 -> (S + 160 <= lo \/ usp <= S) ->
ro_cells bsegs m MP (sb_desc_cells c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11) -> aobj bsegs m MP 96 -> MP mod 8 = 0 -> 0x10000 <= MP -> MP + 104 <= 0x65a180 ->
0 <= c < 2^31 -> 0 <= P < 2^63 ->
stk bsegs m lo usp -> lo <= usp - 96 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
client_constsB m -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (j8 : list byte) (xt1 xa3 xa4 xa5 : word),
ms = MS (mkR (Z_to_bv 64 RA_sbctl_smalloc) (Z_to_bv 64 (usp + -96)) gp tp t0 xt1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -96))
(Z_to_bv 64 64) (Z_to_bv 64 gB_shadow_memory_dynamic_address) (Z_to_bv 64 1) xa3 xa4 xa5 a6 a7
s2 (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 c) s6 s7 (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_stack_malloc_0) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -96, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -96)
/\ rw_cells bsegs m1 (usp + -96) (sbctl_frame (CB 8 j8) s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 c) (Z_to_bv 64 P) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_speex_decoder_ctl) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros P0 HR OBS S8 S0 SHI AP ND OBM AL8 MPLO MPHI CR PR ST LO LOS SPH SP32 (G1 & G2 & G3 & G4) MI.
unfold A_speex_decoder_ctl, RA_sbctl_smalloc, e_stack_malloc_0, sbctl_frame, sb_desc_cells, A_sb_decoder_ctl,
gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'.
pose proof (munch_refl [(usp + -96, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -96, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 96%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 96 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
bato 0xbd590.
bato 0xbd5c4. astep. rewrite land_m32_al by lia.
bato 0xbd5f0. rewrite sx32_small by (unfold int31; lia).
bato 0x51314.
apply evt_done. do 6 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.

Definition sbctl_armpc (c : Z) : Z :=
if c =? 0 then 0xbdb78 else if c =? 3 then 0xbdb24 else if c =? 20 then 0xbda4c else if c =? 24 then 0xbde6c
else if c =? 25 then 0xbdf20 else if c =? 39 then 0xbd988 else if c =? 100 then 0xbd804 else if c =? 101 then 0xbe1b4
else if c =? 103 then 0xbe150 else if c =? 104 then 0xbe128 else 0xbe17c.
Definition sbctl_code_ok (c : Z) : Prop :=
c = 0 \/ c = 3 \/ c = 20 \/ c = 24 \/ c = 25 \/ c = 39 \/ c = 100 \/ c = 101 \/ c = 103 \/ c = 104 \/ c = 105.

Definition sbctl_fhdr (j24 l32 j36 j40 l48 j52 : list byte) : list cell :=
[C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x21034); C8 (Z_to_bv 64 0xbd590); CB 8 j24; CB 4 l32; CB 4 j36; CB 8 j40; CB 4 l48; CB 4 j52].
Definition sbctl_shadow (b4 b6 : byte) : list cell :=
[C1 bF1; C1 bF1; C1 bF1; C1 bF1; C1 b4; C1 (Z_to_bv 8 (-14)); C1 b6; C1 bF3].

Lemma sbctl_w2 : forall (usp lo S P c f sf : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
(c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) (j8 jb js : list byte) F fc (m : mem),
stk bsegs m lo (usp + -96) -> lo <= usp + -96 -> SH_HI <= lo -> usp < 2^63 ->
0 < f -> f mod 64 = 0 -> f + 64 <= lo -> f + 64 <= APP_TOP -> (f + 64 <= SH_LO \/ SH_HI <= f) -> sf = Z.shiftr f 3 + SHB ->
rw_cells bsegs m (usp + -96) (sbctl_frame (CB 8 j8) c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
rw_cells bsegs m f [CB 56 jb] -> rw_cells bsegs m sf [CB 8 js] ->
sbctl_code_ok c ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (a0' a1' a2' : word) (j24 l32 j36 j40 l48 j52 : list byte),
ms = MS (mkR (Z_to_bv 64 RA_sbctl_smalloc) (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -96))
a0' a1' a2' (Z_to_bv 64 (-13)) (Z_to_bv 64 (-8)) (Z_to_bv 64 (-14)) a6 a7
(Z_to_bv 64 f) (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 c) (Z_to_bv 64 f) (Z_to_bv 64 sf) (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (sbctl_armpc c)) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -96, usp); (f, f + 56); (sf, sf + 8)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -96)
/\ rw_cells bsegs m1 (usp + -96) (sbctl_frame (C8 (Z_to_bv 64 f)) c8 c7 c6 c5 c4 c3 c2 c1 c0 cra)
/\ rw_cells bsegs m1 f (sbctl_fhdr j24 l32 j36 j40 l48 j52) /\ rw_cells bsegs m1 sf (sbctl_shadow bF8 bF8))
(MS (mkR (Z_to_bv 64 RA_sbctl_smalloc) (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -96)) (Z_to_bv 64 f)
a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 c) s6 s7 (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbctl_smalloc)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST LO LOS SPH F0 F64 FLO FTOP FSH Esf FR FRB FRS CODE MI.
unfold RA_sbctl_smalloc, sbctl_frame, sbctl_fhdr, sbctl_shadow, bF1, bF3, bF8 in *.
replace (ret_pc (Z_to_bv 64 0xbd5fc)) with (Z_to_bv 64 0xbd5fc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'.
assert (SFR : SH_LO <= sf /\ sf + 8 <= SH_HI) by (subst sf; pose proof (shad_range_al f 64 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) FTOP) as X; rewrite shad_shiftr; unfold shad in *; change (64 / 8) with 8 in X; lia).
pose proof (munch_refl [(usp + -96, usp); (f, f + 56); (sf, sf + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
apply (rw_cells_split_CB bsegs _ _ [] 56 _ [] [8; 8; 8; 8; 4; 4; 8; 4; 4]%nat) in FRB; [| reflexivity]. cbn [mk_CB_cells app] in FRB.
apply (rw_cells_split_CB bsegs _ _ [] 8 _ [] [1; 1; 1; 1; 1; 1; 1; 1]%nat) in FRS; [| reflexivity]. cbn [mk_CB_cells app] in FRS.
astep. astep. astep. astep. sh_if.
bato 0xbd668. astep. rewrite <- Esf.
bato 0xbd690.
destruct CODE as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]].
1: bato 0xbdb78. 2: bato 0xbdb24. 3: bato 0xbda4c. 4: bato 0xbde6c. 5: bato 0xbdf20. 6: bato 0xbd988.
7: bato 0xbd804. 8: bato 0xbe1b4. 9: bato 0xbe150. 10: bato 0xbe128. 11: bato 0xbe17c.
all: apply evt_done; unfold sbctl_armpc; cbn [Z.eqb Pos.eqb]; do 10 eexists; split; [reflexivity|];
split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact ST|]; split; [exact FR|]; split; [exact FRB| exact FRS].
Qed.

Definition sbctl_shadow_dead : list cell := map C1 (repeat bF5 8).

Lemma sbctl_epi_a : forall (usp f sf : Z) (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(hd : word) (b4 b6 : byte) F fc (m : mem),
0 < f -> f mod 64 = 0 -> f + 64 <= usp + -96 -> f + 64 <= APP_TOP -> (f + 64 <= SH_LO \/ SH_HI <= f) -> sf = Z.shiftr f 3 + SHB ->
SH_HI <= usp + -96 -> usp < 2^63 ->
rw_cells bsegs m f [C8 hd] -> rw_cells bsegs m sf (sbctl_shadow b4 b6) ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR ra (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 usp) s1 a0 (Z_to_bv 64 (-11)) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 f) s3 s4 s5 (Z_to_bv 64 f) (Z_to_bv 64 sf) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xbe374) fc None m1 (seg_rom bsegs)
/\ munch [(f, f + 56); (sf, sf + 8)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 sf sbctl_shadow_dead)
(MS (mkR ra (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 usp) s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 f) s3 s4 s5 (Z_to_bv 64 f) (Z_to_bv 64 sf) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_sbctl_epi) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros F0 F64 FLO FTOP FSH Esf LOS SPH FRB FRS MI.
unfold sbctl_shadow, sbctl_shadow_dead, A_sbctl_epi, bF1, bF3, bF5 in *. cbn [map repeat] in *. unfold APP_TOP in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FSH as FSH'. unfold SH_LO, SH_HI in FSH'.
pose proof (shad_range_al f 64 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) ltac:(unfold APP_TOP; lia)) as SW.
rewrite <- shad_shiftr, <- Esf in SW. change (64 / 8) with 8 in SW. unfold SH_LO, SH_HI in SW.
pose proof (munch_refl [(f, f + 56); (sf, sf + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
bato 0xbe34c. astep. sh_if.
bato 0xbe374.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact FRS].
Qed.

Lemma sbctl_epi_b : forall (usp lo f fl : Z) (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) F fc (m : mem),
stk bsegs m lo (usp + -96) -> lo <= usp + -96 -> usp < 2^63 -> 0 < f -> f + 64 <= lo ->
0 < fl -> fl + 1 <= lo ->
rw_cells bsegs m (usp + -96) (sbctl_frame (C8 (Z_to_bv 64 f)) c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
ro_cells bsegs m (f + 56) [C8 (Z_to_bv 64 fl)] -> rw_cells bsegs m fl [C1 (Z_to_bv 8 1)] ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 a0 (Z_to_bv 64 fl) a2 a3 a4 a5 a6 a7 c2 c3 c4 c5 c6 c7 c8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom bsegs)
/\ munch [(fl, fl + 1)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp
/\ rw_cells bsegs m1 fl [C1 z8])
(MS (mkR ra (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 usp) s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 f) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xbe374) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST LO SPH F0 FLO L0 LLO FR FLP FLG MI.
unfold sbctl_frame, z8 in *.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
bato 0xbe3cc. release_frame FR ST usp. astep. astep.
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

Definition e_stack_malloc_0 : Z := 0x51228.
Definition RA_sbctl_smalloc : Z := 0xb5b24.
Definition A_sbctl_epi : Z := 0xb6374.

Definition sbctl_frame (c8 : cell) (s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
[C8 (Z_to_bv 64 0); c8; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition sb_desc_cells (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : word) : list cell :=
[C8 c0; C8 c1; C8 c2; C4 c3; C4 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 (Z_to_bv 64 A_sb_decoder_ctl)].

Lemma sbctl_w1 : forall (usp lo S MP P c : Z) (hrest : list cell) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : word)
(ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m S (C8 (Z_to_bv 64 MP) :: hrest) -> Z.of_nat (cells_size hrest) = 40 ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 < 2^63 -> (S + 160 <= lo \/ usp <= S) ->
ro_cells asegs m MP (sb_desc_cells c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11) -> aobj asegs m MP 96 -> MP mod 8 = 0 -> 0x10000 <= MP -> MP + 104 <= 0x652000 ->
0 <= c < 2^31 -> 0 <= P < 2^63 ->
stk asegs m lo usp -> lo <= usp - 96 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
client_consts m -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (j8 : list byte) (xt1 xa3 xa4 xa5 : word),
ms = MS (mkR (Z_to_bv 64 RA_sbctl_smalloc) (Z_to_bv 64 (usp + -96)) gp tp t0 xt1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -96))
(Z_to_bv 64 64) (Z_to_bv 64 g_shadow_memory_dynamic_address) (Z_to_bv 64 1) xa3 xa4 xa5 a6 a7
s2 (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 c) s6 s7 (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_stack_malloc_0) fc None m1 (seg_rom asegs)
/\ munch [(usp + -96, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -96)
/\ rw_cells asegs m1 (usp + -96) (sbctl_frame (CB 8 j8) s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 c) (Z_to_bv 64 P) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_speex_decoder_ctl) fc None m (seg_rom asegs)).
Proof.
intros until m. intros P0 HR OBS S8 S0 SHI AP ND OBM AL8 MPLO MPHI CR PR ST LO LOS SPH SP32 (G1 & G2 & G3 & G4) MI.
unfold A_speex_decoder_ctl, RA_sbctl_smalloc, e_stack_malloc_0, sbctl_frame, sb_desc_cells, A_sb_decoder_ctl,
g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'.
pose proof (munch_refl [(usp + -96, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -96, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 96%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 96 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xb5ab8.
ato 0xb5aec. astep. rewrite land_m32_al by lia.
ato 0xb5b10. rewrite sx32_small by (unfold int31; lia).
ato 0x51228.
apply evt_done. do 6 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.

Definition sbctl_armpc (c : Z) : Z :=
if c =? 0 then 0xb5f48 else if c =? 3 then 0xb5f0c else if c =? 20 then 0xb5e70 else if c =? 24 then 0xb61b0
else if c =? 25 then 0xb6240 else if c =? 39 then 0xb5df0 else if c =? 100 then 0xb5ce8 else if c =? 101 then 0xb6408
else if c =? 103 then 0xb632c else if c =? 104 then 0xb6310 else 0xb634c.
Definition sbctl_code_ok (c : Z) : Prop :=
c = 0 \/ c = 3 \/ c = 20 \/ c = 24 \/ c = 25 \/ c = 39 \/ c = 100 \/ c = 101 \/ c = 103 \/ c = 104 \/ c = 105.

Definition sbctl_fhdr (j24 l32 j36 j40 l48 j52 : list byte) : list cell :=
[C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x20ffa); C8 (Z_to_bv 64 0xb5ab8); CB 8 j24; CB 4 l32; CB 4 j36; CB 8 j40; CB 4 l48; CB 4 j52].
Definition sbctl_shadow (b4 b6 : byte) : list cell :=
[C1 bF1; C1 bF1; C1 bF1; C1 bF1; C1 b4; C1 (Z_to_bv 8 (-14)); C1 b6; C1 bF3].

Lemma sbctl_w2 : forall (usp lo S P c f sf : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
(c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) (j8 jb js : list byte) F fc (m : mem),
stk asegs m lo (usp + -96) -> lo <= usp + -96 -> SH_HI <= lo -> usp < 2^63 ->
0 < f -> f mod 64 = 0 -> f + 64 <= lo -> f + 64 <= APP_TOP -> (f + 64 <= SH_LO \/ SH_HI <= f) -> sf = Z.shiftr f 3 + SHB ->
rw_cells asegs m (usp + -96) (sbctl_frame (CB 8 j8) c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
rw_cells asegs m f [CB 56 jb] -> rw_cells asegs m sf [CB 8 js] ->
sbctl_code_ok c ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (a0' a1' a2' : word) (j24 l32 j36 j40 l48 j52 : list byte),
ms = MS (mkR (Z_to_bv 64 RA_sbctl_smalloc) (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -96))
a0' a1' a2' (Z_to_bv 64 (-13)) (Z_to_bv 64 (-8)) (Z_to_bv 64 (-14)) a6 a7
(Z_to_bv 64 f) (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 c) (Z_to_bv 64 f) (Z_to_bv 64 sf) (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (sbctl_armpc c)) fc None m1 (seg_rom asegs)
/\ munch [(usp + -96, usp); (f, f + 56); (sf, sf + 8)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -96)
/\ rw_cells asegs m1 (usp + -96) (sbctl_frame (C8 (Z_to_bv 64 f)) c8 c7 c6 c5 c4 c3 c2 c1 c0 cra)
/\ rw_cells asegs m1 f (sbctl_fhdr j24 l32 j36 j40 l48 j52) /\ rw_cells asegs m1 sf (sbctl_shadow bF8 bF8))
(MS (mkR (Z_to_bv 64 RA_sbctl_smalloc) (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -96)) (Z_to_bv 64 f)
a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 c) s6 s7 (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbctl_smalloc)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros ST LO LOS SPH F0 F64 FLO FTOP FSH Esf FR FRB FRS CODE MI.
unfold RA_sbctl_smalloc, sbctl_frame, sbctl_fhdr, sbctl_shadow, bF1, bF3, bF8 in *.
replace (ret_pc (Z_to_bv 64 0xb5b24)) with (Z_to_bv 64 0xb5b24) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'.
assert (SFR : SH_LO <= sf /\ sf + 8 <= SH_HI) by (subst sf; pose proof (shad_range_al f 64 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) FTOP) as X; rewrite shad_shiftr; unfold shad in *; change (64 / 8) with 8 in X; lia).
pose proof (munch_refl [(usp + -96, usp); (f, f + 56); (sf, sf + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
apply (rw_cells_split_CB asegs _ _ [] 56 _ [] [8; 8; 8; 8; 4; 4; 8; 4; 4]%nat) in FRB; [| reflexivity]. cbn [mk_CB_cells app] in FRB.
apply (rw_cells_split_CB asegs _ _ [] 8 _ [] [1; 1; 1; 1; 1; 1; 1; 1]%nat) in FRS; [| reflexivity]. cbn [mk_CB_cells app] in FRS.
astep. astep. astep. astep. sh_if.
ato 0xb5b90. astep. rewrite <- Esf.
ato 0xb5bb8.
destruct CODE as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]].
1: ato 0xb5f48. 2: ato 0xb5f0c. 3: ato 0xb5e70. 4: ato 0xb61b0. 5: ato 0xb6240. 6: ato 0xb5df0.
7: ato 0xb5ce8. 8: ato 0xb6408. 9: ato 0xb632c. 10: ato 0xb6310. 11: ato 0xb634c.
all: apply evt_done; unfold sbctl_armpc; cbn [Z.eqb Pos.eqb]; do 10 eexists; split; [reflexivity|];
split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact ST|]; split; [exact FR|]; split; [exact FRB| exact FRS].
Qed.

Definition sbctl_shadow_dead : list cell := map C1 (repeat bF5 8).

Lemma sbctl_epi_a : forall (usp f sf : Z) (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(hd : word) (b4 b6 : byte) F fc (m : mem),
0 < f -> f mod 64 = 0 -> f + 64 <= usp + -96 -> f + 64 <= APP_TOP -> (f + 64 <= SH_LO \/ SH_HI <= f) -> sf = Z.shiftr f 3 + SHB ->
SH_HI <= usp + -96 -> usp < 2^63 ->
rw_cells asegs m f [C8 hd] -> rw_cells asegs m sf (sbctl_shadow b4 b6) ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR ra (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 usp) s1 a0 (Z_to_bv 64 (-11)) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 f) s3 s4 s5 (Z_to_bv 64 f) (Z_to_bv 64 sf) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xb63a8) fc None m1 (seg_rom asegs)
/\ munch [(f, f + 56); (sf, sf + 8)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 sf sbctl_shadow_dead)
(MS (mkR ra (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 usp) s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 f) s3 s4 s5 (Z_to_bv 64 f) (Z_to_bv 64 sf) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_sbctl_epi) fc None m (seg_rom asegs)).
Proof.
intros until m. intros F0 F64 FLO FTOP FSH Esf LOS SPH FRB FRS MI.
unfold sbctl_shadow, sbctl_shadow_dead, A_sbctl_epi, bF1, bF3, bF5 in *. cbn [map repeat] in *. unfold APP_TOP in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof FSH as FSH'. unfold SH_LO, SH_HI in FSH'.
pose proof (shad_range_al f 64 ltac:(lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) ltac:(unfold APP_TOP; lia)) as SW.
rewrite <- shad_shiftr, <- Esf in SW. change (64 / 8) with 8 in SW. unfold SH_LO, SH_HI in SW.
pose proof (munch_refl [(f, f + 56); (sf, sf + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0xb6380. astep. sh_if.
ato 0xb63a8.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact FRS].
Qed.

Lemma sbctl_epi_b : forall (usp lo f fl : Z) (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) F fc (m : mem),
stk asegs m lo (usp + -96) -> lo <= usp + -96 -> usp < 2^63 -> 0 < f -> f + 64 <= lo ->
0 < fl -> fl + 1 <= lo ->
rw_cells asegs m (usp + -96) (sbctl_frame (C8 (Z_to_bv 64 f)) c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
ro_cells asegs m (f + 56) [C8 (Z_to_bv 64 fl)] -> rw_cells asegs m fl [C1 (Z_to_bv 8 1)] ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 a0 (Z_to_bv 64 fl) a2 a3 a4 a5 a6 a7 c2 c3 c4 c5 c6 c7 c8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc cra) fc None m1 (seg_rom asegs)
/\ munch [(fl, fl + 1)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp
/\ rw_cells asegs m1 fl [C1 z8])
(MS (mkR ra (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 usp) s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 f) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xb63a8) fc None m (seg_rom asegs)).
Proof.
intros until m. intros ST LO SPH F0 FLO L0 LLO FR FLP FLG MI.
unfold sbctl_frame, z8 in *.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0xb6404. release_frame FR ST usp. astep.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact FLG].
Qed.
