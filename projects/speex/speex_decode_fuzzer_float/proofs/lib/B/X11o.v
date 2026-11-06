(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1dg X1df X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05l X05m X09f X06d.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0z5 X0ys X0yq X0x2 X0yt X11l X0wg X0wc X0wh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X11n.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac tlia ::= (try unfold BITS_SIZEOF in * ); tlia_one.
Local Ltac slia ::= (try unfold BITS_SIZEOF in * ); first [ exact I | lia | split; [lia|exact I] ].
Definition RA_sbd_pois5 : Z := 0xbef80.

Lemma sbd_v8 : forall (usp lo S OUT A f MODE Q OQ : Z) (g : nat -> word) (s : sbd_state bptr) (a : sb_addrs) (lq voq : list word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_fr g) -> g 40%nat = Z_to_bv 64 S -> g 55%nat = Z_to_bv 64 (Z.shiftr (S + 32) 3 + SHB) -> g 53%nat = Z_to_bv 64 (usp + -992) ->
g 41%nat = Z_to_bv 64 32 ->
rw_cells bsegs m S (sbp_hdr s a) -> rw_cells bsegs m (S + 36) [C4 (Z_to_bv 64 (sbd_first s))] -> rw_cells bsegs m (S + 40) (sbp_ptrs s a OUT) ->
sbd_lpcSize s = 8 -> (sbd_first s = 0 \/ sbd_first s = 1) -> OQ = a_oq a ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= lo -> (S + 160 <= SH_LO \/ SH_HI <= S) ->
Q = usp + -992 -> rw_cells bsegs m Q (f32 lq) -> length lq = 8%nat -> aobj bsegs m Q 32 ->
rw_cells bsegs m OQ (f32 voq) -> length voq = 8%nat -> aobj bsegs m OQ 32 -> OQ mod 8 = 0 -> 0 < OQ -> OQ + 32 <= lo -> (OQ + 32 <= SH_LO \/ SH_HI <= OQ) ->
(S + 160 <= OQ \/ OQ + 32 <= S) ->
stk bsegs m lo (usp + -1120) -> lo <= usp + -1120 - 4192 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
mem_inv bsegs m -> X1cn.frm0 fc ->
evt bsegs (fun ms => exists (m1 : mem) (xt0 xa2 xa3 xa4 xa5 xa6 xa7 : word) (F' : bvmap 5 word) (jh : list byte) (voq' : list word),
ms = MS (mkR (Z_to_bv 64 RA_sbd_pois5) (Z_to_bv 64 (usp + -1216)) gp tp xt0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736))
(Z_to_bv 64 (usp + -1184)) (Z_to_bv 64 32) xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 (usp + -1216)) (Z_to_bv 64 (S + 32)) (Z_to_bv 64 (S + 152)) (Z_to_bv 64 MODE) (Z_to_bv 64 SHB) (Z_to_bv 64 (usp + -1088))
(Z_to_bv 64 f) (Z_to_bv 64 (S + 152)) (Z_to_bv 64 A) (Z_to_bv 64 (usp + -1184)) t3 t4 t5 t6)
F' (Z_to_bv 64 sb_e_alloca_poison) fc None m1 (seg_rom bsegs)
/\ munch [(OQ, OQ + 32); (usp + -5216, usp + -160)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -1216)
/\ rw_cells bsegs m1 (usp + -736)
(sb_fr (fupds g [(7%nat, Z_to_bv 64 (Z.shiftr (S + 36) 3 + SHB)); (8%nat, Z_to_bv 64 (S + 36)); (50%nat, Z_to_bv 64 (S + 80));
(39%nat, Z_to_bv 64 (18446744073709551615 - (usp + -992))); (29%nat, Z_to_bv 64 8); (28%nat, Z_to_bv 64 32)]))
/\ rw_cells bsegs m1 (usp + -1216) [CB 96 jh]
/\ rw_cells bsegs m1 OQ (f32 voq') /\ length voq' = 8%nat)
(MS (R_V5 usp (usp + -1120) S A f MODE gp tp (Z_to_bv 64 RA_sbd_lspq) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (S + 32)) (Z_to_bv 64 (S + 152)) (Z_to_bv 64 (usp + -1088)) s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_lspq)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR E40 E55 E53 E41 HD FST PT ELPC HFST EOQ OBS S8 SPOS SLO SOFF EQ QC LQ OBQ OQC LOQ OBOQ OQ8 OQPOS OQLO OQOFF SOQ ST LO LOS SPH U32 MI FRM.
unfold R_V5, RA_sbd_lspq, RA_sbd_pois5, sb_e_alloca_poison in *. unfold SH_LO, SH_HI in SOFF, OQOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xbede4)) with (Z_to_bv 64 0xbede4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(OQ, OQ + 32); (usp + -5216, usp + -160)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(OQ, OQ + 32); (usp + -5216, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; lia).
assert (Q8 : Q mod 8 = 0) by (subst Q; clear - U32; Z.div_mod_to_equations; lia).
unfold sb_fr in FR. cbn [map seq] in FR. rewrite E40, E55, E53, E41 in FR. rewrite <- EQ in FR. unfold sbp_hdr in HD. rewrite ELPC in HD. unfold sbp_ptrs in PT. rewrite <- EOQ in PT.
do 8 (destruct lq as [|? lq]; [discriminate LQ|]). destruct lq; [| discriminate LQ]. cbn [f32 map] in QC.
do 8 (destruct voq as [|? voq]; [discriminate LOQ|]). destruct voq; [| discriminate LOQ]. cbn [f32 map] in OQC.
carve_frame 96%nat ST. rename FR0 into HULL.
carve_frame 3992%nat ST. rename FR0 into JK1.
carve_frame 8%nat ST. rename FR0 into P1.
apply (rw_cells_split_CB bsegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
bato 0xbee14.
destruct HFST as [E0|E0]; rewrite E0 in *; rewrite sx32_small by (unfold int31; lia).
all: bato 0xbee20; rewrite sx32_small by (unfold int31; lia).
2: { assert (AL0 : (0 + OQ) mod 4 = 0) by (clear - OQ8; Z.div_mod_to_equations; lia). assert (AL4 : (4 + OQ) mod 4 = 0) by (clear - OQ8; Z.div_mod_to_equations; lia). assert (AL8 : (8 + OQ) mod 4 = 0) by (clear - OQ8; Z.div_mod_to_equations; lia). assert (AL12 : (12 + OQ) mod 4 = 0) by (clear - OQ8; Z.div_mod_to_equations; lia). assert (AL16 : (16 + OQ) mod 4 = 0) by (clear - OQ8; Z.div_mod_to_equations; lia). assert (AL20 : (20 + OQ) mod 4 = 0) by (clear - OQ8; Z.div_mod_to_equations; lia). assert (AL24 : (24 + OQ) mod 4 = 0) by (clear - OQ8; Z.div_mod_to_equations; lia). assert (AL28 : (28 + OQ) mod 4 = 0) by (clear - OQ8; Z.div_mod_to_equations; lia).
bato 0xbef18.
bato 0xbef50. bdec. alits.
astep. astep.
replace (usp + -1120 - 96) with (usp + -1216) by lia. rewrite ?Z.mod_small by lia.
rewrite (land_m32_al (usp + -1216)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. astep. replace (usp + -1120 - 4096) with (usp + -5216) by lia.
astep. astep. sh_if.
bato 0x51e24.
release_frame P1 ST (usp + -5208). release_frame JK1 ST (usp + -1216).
replace (usp + -1216 + 32) with (usp + -1184) in * by lia.
rewrite <- E40, <- E55, <- E41 in FR. rewrite EQ in FR. rewrite (zb_lxor_ones (usp + -992)) in FR by lia. rewrite <- E53 in FR.
apply evt_done. lazymatch type of OQC with rw_cells _ _ _ [C4 ?w0; C4 ?w1; C4 ?w2; C4 ?w3; C4 ?w4; C4 ?w5; C4 ?w6; C4 ?w7] => do 10 eexists; exists [w0; w1; w2; w3; w4; w5; w6; w7] end. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
split; [unfold sb_fr; cbn [map seq fupds Nat.eqb]; rewrite E41; rewrite E41 in FR; exact FR|]. split; [exact HULL|]. split; [exact OQC| reflexivity]. }
bato 0xbef18.
bato 0xbef50. bdec. alits.
astep. astep.
replace (usp + -1120 - 96) with (usp + -1216) by lia. rewrite ?Z.mod_small by lia.
rewrite (land_m32_al (usp + -1216)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. astep. replace (usp + -1120 - 4096) with (usp + -5216) by lia.
astep. astep. sh_if.
bato 0x51e24.
release_frame P1 ST (usp + -5208). release_frame JK1 ST (usp + -1216).
replace (usp + -1216 + 32) with (usp + -1184) in * by lia.
rewrite <- E40, <- E55, <- E41 in FR. rewrite EQ in FR. rewrite (zb_lxor_ones (usp + -992)) in FR by lia. rewrite <- E53 in FR.
apply evt_done. lazymatch type of OQC with rw_cells _ _ _ [C4 ?w0; C4 ?w1; C4 ?w2; C4 ?w3; C4 ?w4; C4 ?w5; C4 ?w6; C4 ?w7] => do 10 eexists; exists [w0; w1; w2; w3; w4; w5; w6; w7] end. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
split; [unfold sb_fr; cbn [map seq fupds Nat.eqb]; rewrite E41; rewrite E41 in FR; exact FR|]. split; [exact HULL|]. split; [exact OQC| reflexivity].
Qed.

Definition sb_v9_upd (usp S OUT f MODE fsz : Z) : list (nat * word) :=
[(68%nat, Z_to_bv 64 (usp + -1216)); (6%nat, Z_to_bv 64 (Z.shiftr (S + 80) 3)); (60%nat, Z_to_bv 64 0);
(26%nat, Z_to_bv 64 (S + 104)); (27%nat, Z_to_bv 64 (S + 132)); (22%nat, Z_to_bv 64 (S + 96)); (21%nat, Z_to_bv 64 (S + 112));
(23%nat, Z_to_bv 64 (18446744073709551615 - (usp + -800))); (12%nat, Z_to_bv 64 (18446744073709551615 - (usp + -896)));
(2%nat, Z_to_bv 64 7); (10%nat, Z_to_bv 64 0); (38%nat, Z_to_bv 64 (S + 120)); (4%nat, Z_to_bv 64 3); (3%nat, Z_to_bv 64 7);
(20%nat, Z_to_bv 64 2147483647); (63%nat, Z_to_bv 64 4294967296); (5%nat, Z_to_bv 64 3); (37%nat, Z_to_bv 64 (sha (S + 120)));
(24%nat, Z_to_bv 64 (sha (S + 80))); (59%nat, Z_to_bv 64 (S + 24)); (43%nat, Z_to_bv 64 (S + 72)); (11%nat, Z_to_bv 64 (MODE + 32));
(42%nat, Z_to_bv 64 (S + 88)); (25%nat, Z_to_bv 64 (usp + -1180)); (58%nat, Z_to_bv 64 (sha (S + 24)))].
Lemma sbd_v9 : forall (usp S OUT A f MODE fsz : Z) (g : nat -> word) (s : sbd_state bptr) (a : sb_addrs)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_fr g) -> g 51%nat = Z_to_bv 64 (Z.shiftr (S + 28) 3 + SHB) -> g 52%nat = Z_to_bv 64 (S + 28) ->
g 50%nat = Z_to_bv 64 (S + 80) -> g 40%nat = Z_to_bv 64 S -> g 32%nat = Z_to_bv 64 (usp + -800) -> g 17%nat = Z_to_bv 64 (usp + -896) ->
g 34%nat = Z_to_bv 64 (S + 20) -> g 56%nat = Z_to_bv 64 (S + 32) ->
rw_cells bsegs m S (sbp_hdr s a) -> sbd_nbSubframes s = 4 ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= usp + -1216 -> (S + 160 <= SH_LO \/ SH_HI <= S) ->
0 < MODE -> MODE mod 8 = 0 -> MODE + 216 <= 0x65b000 ->
SH_HI <= usp + -1216 -> usp < 2^63 ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (k : sb_rjunk) (F' : bvmap 5 word),
ms = MS (R_LA usp S OUT MODE 0 gp tp k) F' (Z_to_bv 64 SB_LA_PC) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -736, usp + -160)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 (usp + -736) (sb_fr (fupds g (sb_v9_upd usp S OUT f MODE fsz))))
(MS (mkR (Z_to_bv 64 RA_sbd_pois5) (Z_to_bv 64 (usp + -1216)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736))
a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (usp + -1216)) (Z_to_bv 64 (S + 32)) (Z_to_bv 64 (S + 152)) (Z_to_bv 64 MODE) (Z_to_bv 64 SHB) (Z_to_bv 64 (usp + -1088))
(Z_to_bv 64 f) (Z_to_bv 64 (S + 152)) (Z_to_bv 64 A) (Z_to_bv 64 (usp + -1184)) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_pois5)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR E51 E52 E50 E40 E32 E17 E34 E56 HD ENS OBS S8 SPOS SLO SOFF M0 M8 MHI LOS SPH MI.
unfold RA_sbd_pois5, SB_LA_PC in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xbef80)) with (Z_to_bv 64 0xbef80) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(usp + -736, usp + -160)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -736, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_fr in FR. cbn [map seq] in FR. rewrite E51, E52, E50, E40, E32, E17, E34, E56 in FR. unfold sbp_hdr in HD. rewrite ENS in HD.
bato 0xbef9c. rewrite sx32_small by (unfold int31; lia).
bato 0xbf0bc.
assert (L20 : Z.land (S + 20) 7 = 4) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; clear - S8; Z.div_mod_to_equations; lia).
assert (L28 : Z.land (S + 28) 7 = 4) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; clear - S8; Z.div_mod_to_equations; lia).
assert (L32 : Z.land (S + 32) 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; clear - S8; Z.div_mod_to_equations; lia).
assert (L24 : Z.land (S + 24) 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; clear - S8; Z.div_mod_to_equations; lia).
assert (LM : Z.land MODE 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; exact M8).
rewrite L20, L28, L32, L24, LM in FR. change (4 + 3) with 7 in FR. change (0 + 3) with 3 in FR.
replace (MODE <? 1) with false in FR by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.ltb Z.compare Z.lor] in FR.
rewrite (zb_lxor_ones (usp + -896)) in FR by lia. rewrite (zb_lxor_ones (usp + -800)) in FR by lia.
rewrite (zb_lxor_ones (usp + -1184)) by lia.
rewrite <- E51, <- E52, <- E50, <- E40, <- E32, <- E17, <- E34, <- E56 in FR.
apply evt_done. eexists. eexists (SBRJ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _). eexists.
split; [unfold R_LA, sha; cbn [j_ra j_t0 j_t1 j_t2 j_a0 j_a1 j_a2 j_a3 j_a4 j_a5 j_a6 j_a7 j_s2 j_s3 j_s4 j_s5 j_s7 j_s8 j_s9 j_s10 j_s11 j_t3 j_t4 j_t5 j_t6]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. unfold sb_v9_upd. exact FR.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Definition sb_A_qmf_synth : Z := 0xa8508.
Definition sb_A_H0 : Z := 0x27000.
Definition RA_sbd_qmf_t : Z := 0xc0358.

Lemma sbd_t1 : forall (usp lo S OUT A f sf MODE fsz : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs) (le : word) (k : sb_rjunk)
(gp tp : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_slots usp S OUT A f sf MODE fsz v) ->
rw_cells bsegs m S (sbp_hdr s a) -> rw_cells bsegs m (S + 40) (sbp_ptrs s a OUT) -> rw_cells bsegs m (S + 128) [C4 le] ->
sbd_frame_size s = fsz -> sbd_full_frame_size s = 2 * fsz -> (fsz = 160 \/ fsz = 320) ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= lo -> (S + 160 <= SH_LO \/ SH_HI <= S) -> IMG_TOP_B <= S ->
0 < OUT -> OUT + 8000 < 2^63 ->
stk bsegs m lo (usp + -1216) -> lo <= usp + -1216 - 16 -> SH_HI <= lo -> usp < 2^63 ->
mem_inv bsegs m -> X1cn.frm0 fc ->
evt bsegs (fun ms => exists (m1 : mem) (xt0 xt1 xt2 xt3 xt4 xt5 xt6 : word) (xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 : word) (F' : bvmap 5 word) (fc' : bv 32) (le' : word) (ja : list byte),
ms = MS (mkR (Z_to_bv 64 RA_sbd_qmf_t) (Z_to_bv 64 (usp + -1232)) gp tp xt0 xt1 xt2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736))
(Z_to_bv 64 OUT) (Z_to_bv 64 (OUT + 4 * fsz)) (Z_to_bv 64 sb_A_H0) (Z_to_bv 64 OUT) (Z_to_bv 64 (2 * fsz)) (Z_to_bv 64 64)
(Z_to_bv 64 (a_g0 a)) (Z_to_bv 64 (a_g1 a))
(Z_to_bv 64 (S + 32)) xs3 xs4 xs5 (Z_to_bv 64 SHB) xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
F' (Z_to_bv 64 sb_A_qmf_synth) fc' None m1 (seg_rom bsegs)
/\ munch [(S + 128, S + 132); (usp + -1232, usp + -1216)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -1232)
/\ X1cn.frm0 fc' /\ rw_cells bsegs m1 (S + 128) [C4 le'] /\ rw_cells bsegs m1 (usp + -1232) [C8 (Z_to_bv 64 0); CB 8 ja])
(MS (R_TA usp S OUT gp tp k) F (Z_to_bv 64 SB_TA_PC) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL HD PT LE EFS EFFS HFS OBS S8 SPOS SLO SOFF SIMG O0 O1 ST LO LOS SPH MI FRM.
unfold R_TA, SB_TA_PC, RA_sbd_qmf_t, sb_A_qmf_synth, sb_A_H0 in *. unfold SH_LO, SH_HI in SOFF. unfold IMG_TOP_B in SIMG. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(S + 128, S + 132); (usp + -1232, usp + -1216)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(S + 128, S + 132); (usp + -1232, usp + -1216)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_slots, sha in SL. unfold sbp_hdr in HD. rewrite EFS, EFFS in HD. unfold sbp_ptrs in PT.
carve_frame 16%nat ST. rename FR into ARG.
apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in ARG; [| reflexivity]. cbn [mk_CB_cells app] in ARG.
bato 0xc02b4.
rewrite sx32_small by (unfold int31; lia).
bato 0xc0334. rewrite sx32_small by (unfold int31; lia).
bato 0xa8508.
replace (fsz * 4 + OUT) with (OUT + 4 * fsz) by lia.
apply evt_done. do 20 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [assumption|]. split; [exact LE| exact ARG].
Qed.
Definition RA_sbd_unpoison_t : Z := 0xc0450.

Lemma sbd_t2 : forall (usp lo S OUT A f sf MODE fsz Q OQ : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs) (fst0 : word) (lq voq : list word) (ja : list byte)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_slots usp S OUT A f sf MODE fsz v) ->
rw_cells bsegs m S (sbp_hdr s a) -> rw_cells bsegs m (S + 36) [C4 fst0] -> rw_cells bsegs m (S + 40) (sbp_ptrs s a OUT) ->
sbd_lpcSize s = 8 -> OQ = a_oq a ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= lo -> (S + 160 <= SH_LO \/ SH_HI <= S) ->
Q = usp + -992 -> rw_cells bsegs m Q (f32 lq) -> length lq = 8%nat -> aobj bsegs m Q 32 ->
rw_cells bsegs m OQ (f32 voq) -> length voq = 8%nat -> aobj bsegs m OQ 32 -> OQ mod 8 = 0 -> 0 < OQ -> OQ + 32 <= lo -> (OQ + 32 <= SH_LO \/ SH_HI <= OQ) ->
(S + 160 <= OQ \/ OQ + 32 <= S) ->
rw_cells bsegs m (usp + -1232) [C8 (Z_to_bv 64 0); CB 8 ja] ->
stk bsegs m lo (usp + -1232) -> lo <= usp + -1232 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
mem_inv bsegs m -> X1cn.frm0 fc ->
evt bsegs (fun ms => exists (m1 : mem) (xa2 xa3 xa4 xa5 xa6 xa7 : word) (F' : bvmap 5 word) (voq' : list word),
ms = MS (mkR (Z_to_bv 64 RA_sbd_unpoison_t) (Z_to_bv 64 (usp + -1216)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736))
(v_544 v) (Z_to_bv 64 (usp + -736)) xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 (usp + -736)) s3 s4 s5 (Z_to_bv 64 SHB) s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 sb_e_allocas_unpoison) fc None m1 (seg_rom bsegs)
/\ munch [(S + 36, S + 40); (OQ, OQ + 32)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -1216)
/\ rw_cells bsegs m1 (S + 36) [C4 (Z_to_bv 64 0)] /\ rw_cells bsegs m1 OQ (f32 voq') /\ length voq' = 8%nat)
(MS (mkR (Z_to_bv 64 RA_sbd_qmf_t) (Z_to_bv 64 (usp + -1232)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736))
a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (S + 32)) s3 s4 s5 (Z_to_bv 64 SHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_qmf_t)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL HD FST PT ELPC EOQ OBS S8 SPOS SLO SOFF EQ QC LQ OBQ OQC LOQ OBOQ OQ8 OQPOS OQLO OQOFF SOQ ARG ST LO LOS SPH U32 MI FRM.
unfold RA_sbd_qmf_t, RA_sbd_unpoison_t, sb_e_allocas_unpoison in *. unfold SH_LO, SH_HI in SOFF, OQOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xc0358)) with (Z_to_bv 64 0xc0358) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(S + 36, S + 40); (OQ, OQ + 32)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(S + 36, S + 40); (OQ, OQ + 32)]) by (cbn; unfold SH_LO, SH_HI; lia).
assert (Q8 : Q mod 8 = 0) by (subst Q; clear - U32; Z.div_mod_to_equations; lia).
unfold sb_slots, sha in SL. rewrite <- EQ in SL. unfold sbp_hdr in HD. rewrite ELPC in HD. unfold sbp_ptrs in PT. rewrite <- EOQ in PT.
do 8 (destruct lq as [|? lq]; [discriminate LQ|]). destruct lq; [| discriminate LQ]. cbn [f32 map] in QC.
do 8 (destruct voq as [|? voq]; [discriminate LOQ|]). destruct voq; [| discriminate LOQ]. cbn [f32 map] in OQC.
astep. replace (usp + -1232 + 16) with (usp + -1216) by lia.
release_frame ARG ST (usp + -1216).
bato 0xc036c. rewrite sx32_small by (unfold int31; lia).
assert (AL0 : (0 + OQ) mod 4 = 0) by (clear - OQ8; Z.div_mod_to_equations; lia). assert (AL4 : (4 + OQ) mod 4 = 0) by (clear - OQ8; Z.div_mod_to_equations; lia). assert (AL8 : (8 + OQ) mod 4 = 0) by (clear - OQ8; Z.div_mod_to_equations; lia). assert (AL12 : (12 + OQ) mod 4 = 0) by (clear - OQ8; Z.div_mod_to_equations; lia). assert (AL16 : (16 + OQ) mod 4 = 0) by (clear - OQ8; Z.div_mod_to_equations; lia). assert (AL20 : (20 + OQ) mod 4 = 0) by (clear - OQ8; Z.div_mod_to_equations; lia). assert (AL24 : (24 + OQ) mod 4 = 0) by (clear - OQ8; Z.div_mod_to_equations; lia). assert (AL28 : (28 + OQ) mod 4 = 0) by (clear - OQ8; Z.div_mod_to_equations; lia).
bato 0x51f50.
apply evt_done. lazymatch type of OQC with rw_cells _ _ _ [C4 ?w0; C4 ?w1; C4 ?w2; C4 ?w3; C4 ?w4; C4 ?w5; C4 ?w6; C4 ?w7] => do 8 eexists; exists [w0; w1; w2; w3; w4; w5; w6; w7] end.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FST|]. split; [exact OQC| reflexivity].
Qed.

Lemma sbd_t3 : forall (usp lo f : Z) (jh : list byte)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -1216) [CB 480 jh] ->
stk bsegs m lo (usp + -1216) -> lo <= usp + -1216 -> usp < 2^63 ->
mem_inv bsegs m ->
evt bsegs (fun ms =>
ms = MS (mkR (Z_to_bv 64 RA_sbd_unpoison_t) (Z_to_bv 64 (usp + -736)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736))
a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (usp + -736)) s3 (Z_to_bv 64 0) s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xc0458) fc None m (seg_rom bsegs)
/\ stk bsegs m lo (usp + -736))
(MS (mkR (Z_to_bv 64 RA_sbd_unpoison_t) (Z_to_bv 64 (usp + -1216)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736))
a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (usp + -736)) s3 s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_unpoison_t)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros HULLS ST LO SPH MI.
unfold RA_sbd_unpoison_t in *.
replace (ret_pc (Z_to_bv 64 0xc0450)) with (Z_to_bv 64 0xc0450) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof ST as (STa & STb & _).
astep. release_frame HULLS ST (usp + -736).
ato 0xc0458.
apply evt_done. split; [reflexivity| exact ST].
Qed.

Definition sb_e_asan_memset : Z := 0x6689c.
Definition RA_sbd_memset_n : Z := 0xc025c.

Definition R_N (usp S A f MODE : Z) (gp tp : word) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs11 xt3 xt4 xt5 xt6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -736)) gp tp xt0 xt1 xt2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 (S + 20)) xs3 xs4 (Z_to_bv 64 MODE) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.shiftr (S + 8) 3 + SHB)) (Z_to_bv 64 f)
(Z_to_bv 64 (S + 152)) (Z_to_bv 64 A) xs11 xt3 xt4 xt5 xt6.

Lemma sbd_n1 : forall (usp S OUT A f MODE : Z) (g : nat -> word) (s : sbd_state bptr) (a : sb_addrs)
(gp tp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_fr g) -> g 19%nat = Z_to_bv 64 f -> g 34%nat = Z_to_bv 64 (S + 20) ->
rw_cells bsegs m S (sbp_hdr s a) -> rw_cells bsegs m (S + 40) (sbp_ptrs s a OUT) ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 < 2^63 ->
0 < OUT -> OUT + 8000 < 2^63 -> match sbd_innov_save s with None => True | Some k => 0 <= k <= 2000 end -> 0 <= sbd_full_frame_size s <= 640 ->
mem_inv bsegs m ->
evt bsegs (fun ms =>
match sbd_innov_save s with
| None => exists (xa0 xa1 : word), ms = MS (R_N usp S A f MODE gp tp ra t0 t1 t2 xa0 xa1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 S) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xc025c) fc None m (seg_rom bsegs)
| Some k => ms = MS (R_N usp S A f MODE gp tp (Z_to_bv 64 RA_sbd_memset_n) t0 t1 t2 (Z_to_bv 64 (OUT + 4 * k)) (Z_to_bv 64 0)
(Z_to_bv 64 (4 * sbd_full_frame_size s)) a3 a4 a5 a6 a7 s3 (Z_to_bv 64 S) s11 t3 t4 t5 t6) F (Z_to_bv 64 sb_e_asan_memset) fc None m (seg_rom bsegs)
end)
(MS (R_J4 usp S A f MODE gp tp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 S) s11 t3 t4 t5 t6) F (Z_to_bv 64 0xc0214) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR E19 E34 HD PT OBS S8 SPOS SHI O0 O1 HK FFS MI.
unfold R_N, R_J4, RA_sbd_memset_n, sb_e_asan_memset in *.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM. assert (OF : offsh []) by exact I.
unfold sb_fr in FR. cbn [map seq] in FR. rewrite E19, E34 in FR.
unfold sbp_hdr in HD. unfold sbp_ptrs, sb_isave_ptr in PT.
destruct (sbd_innov_save s) as [k|].
- bato 0xc0234. astep. sh_if.
bato 0xc0250. rewrite sx32_small by (unfold int31; lia).
bato 0x6689c.
replace (sbd_full_frame_size s ≪ 2) with (4 * sbd_full_frame_size s) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
apply evt_done. reflexivity.
- bato 0xc025c. apply evt_done. do 2 eexists. reflexivity.
Qed.

Definition RA_sbd_lost : Z := 0xc0278.

Lemma sbd_n2 : forall (usp S OUT A f MODE dtx : Z) (g : nat -> word) (stk8 : word) (j24 j36 : list byte)
(gp tp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_fr g) -> g 62%nat = Z_to_bv 64 OUT -> g 54%nat = stk8 ->
rw_cells bsegs m f (sb_fhdr j24 (Z_to_bv 64 dtx) j36) -> (dtx = 0 \/ dtx = 1) -> 0 < f -> f + 64 < 2^63 ->
mem_inv bsegs m ->
evt bsegs (fun ms =>
(dtx = 0 /\ exists xa0 : word, ms = MS (R_N usp S A f MODE gp tp ra t0 t1 t2 xa0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 S) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xc0534) fc None m (seg_rom bsegs))
\/ (dtx = 1 /\ ms = MS (R_N usp S A f MODE gp tp (Z_to_bv 64 RA_sbd_lost) t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 OUT) (Z_to_bv 64 1) stk8 a4 a5 a6 a7
(Z_to_bv 64 (f + 32)) (Z_to_bv 64 S) s11 t3 t4 t5 t6) F (Z_to_bv 64 A_sb_decode_lost) fc None m (seg_rom bsegs)))
(MS (R_N usp S A f MODE gp tp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 S) s11 t3 t4 t5 t6) F (Z_to_bv 64 0xc025c) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR E62 E54 FRB HD F0 F1 MI.
unfold R_N, RA_sbd_lost, A_sb_decode_lost in *.
unfold sb_fr in FR. cbn [map seq] in FR. rewrite E62, E54 in FR. unfold sb_fhdr in FRB.
destruct HD as [-> | ->].
- ato 0xc0534. apply evt_done. left. split; [reflexivity|]. eexists. reflexivity.
- ato 0xc0bd8. apply evt_done. right. split; reflexivity.
Qed.

Lemma sbd_n3 : forall (usp S OUT A f MODE : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s11 t3 t4 t5 t6 : word) F fc (m : mem),
evt bsegs (fun ms => ms = MS (R_N usp S A f MODE gp tp (Z_to_bv 64 RA_sbd_lost) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 0) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xc0458) fc None m (seg_rom bsegs))
(MS (R_N usp S A f MODE gp tp (Z_to_bv 64 RA_sbd_lost) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_lost)) fc None m (seg_rom bsegs)).
Proof.
intros until m. unfold R_N, RA_sbd_lost.
replace (ret_pc (Z_to_bv 64 0xc0278)) with (Z_to_bv 64 0xc0278) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0xc0458. apply evt_done. reflexivity.
Qed.

Lemma sb_f32_snoc l x : f32 l ++ [C4 x] = f32 (l ++ [x]).
Proof. rewrite f32_app, f32_cons, f32_nil. reflexivity. Qed.
Section SIL.
Variables (usp OUT Y NW : Z) (g : nat -> word).
Variables rav spv gp tp t0v t1v t2v s0v a6v a7v s2v s3v s4v s5v s7v s8v s9v s10v s11v t3v t4v t5v t6v : word.
Hypothesis Y4 : Y mod 4 = 0.
Hypothesis YI : IMG_TOP_B <= Y.
Hypothesis EY : Y = OUT + 4 * NW.
Hypothesis O0 : 0 < OUT.
Hypothesis E62 : g 62%nat = Z_to_bv 64 OUT.
Definition RSIL (i : Z) (a0v a4v a5v : word) : bvmap 5 word :=
mkR rav spv gp tp t0v t1v t2v s0v (Z_to_bv 64 (usp + -736)) a0v (Z_to_bv 64 i) (Z_to_bv 64 0x26901d7d) (Z_to_bv 64 NW) a4v a5v a6v a7v
s2v s3v s4v s5v (Z_to_bv 64 SHB) s7v s8v s9v s10v s11v t3v t4v t5v t6v.
Definition sil_post (F : bvmap 5 word) (fc : bv 32) (mI : mem) : machine_state -> Prop :=
fun ms' => exists a0' a4' a5' m' (ys' : list word),
ms' = MS (RSIL NW a0' a4' a5') F (Z_to_bv 64 0xc05cc) fc None m' (seg_rom bsegs)
/\ munch [(Y, Y + 4 * NW)] mI m' /\ wmono bsegs mI m' /\ mem_inv bsegs m'
/\ Z.of_nat (length ys') = NW /\ rw_cells bsegs m' Y (f32 ys').
Lemma sb_silence_loop : forall (mI : mem) (rest done : list word) (cw : word) (i : Z) (a0v a4v a5v : word) F fc mc,
i = Z.of_nat (length done) -> i + 1 + Z.of_nat (length rest) = NW -> NW <= 320 -> OUT + 8000 < 2^63 ->
aobj bsegs mI Y (4 * NW) -> offsh [(Y, Y + 4 * NW)] ->
mem_inv bsegs mc -> munch [(Y, Y + 4 * NW)] mI mc -> wmono bsegs mI mc ->
rw_cells bsegs mc (usp + -736) (sb_fr g) -> (Y + 4 * NW <= usp + -736 \/ usp + -160 <= Y) ->
rw_cells bsegs mc Y (f32 done) -> rw_cells bsegs mc (Y + 4 * i) (f32 (cw :: rest)) ->
evt bsegs (sil_post F fc mI) (MS (RSIL i a0v a4v a5v) F (Z_to_bv 64 0xc0554) fc None mc (seg_rom bsegs)).
Proof using Y4 YI EY O0 E62.
intros mI rest.
induction rest as [|cw' rest IH]; intros done cw i a0v a4v a5v F fc mc Hi HN HNW O1 OBY OF MI MU WM FR FRY XD XC;
pose proof OBY as (OY0 & OY1 & _); unfold APP_TOP in *; pose proof YI as YI'; unfold IMG_TOP_B in YI';
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
unfold RSIL; rewrite !f32_cons in XC; cbn [length] in *;
unfold sb_fr in FR; cbn [map seq] in FR; rewrite E62 in FR.
- rewrite f32_nil in XC.
bato 0xc0594.
replace (OUT + (NW + i + 0) * 4) with (Y + 4 * i) by lia.
assert (YA : (Y + 4 * i) mod 4 = 0) by (clear - Y4; Z.div_mod_to_equations; lia).
bato 0xc05a8. astep. chk_merge OBY 4.
bato 0xc05b4.
rewrite (swrap32_small (i + 1)) by lia.
astep. sh_if.
bato 0xc05cc.
chunk_snoc XD XC. rewrite sb_f32_snoc in XD.
replace (i + 1) with NW by lia.
unfold sil_post, RSIL. rewrite <- E62 in FR. finish; [ | exact XD ]. rewrite length_app; cbn [length]; lia.
- bato 0xc0594.
replace (OUT + (NW + i + 0) * 4) with (Y + 4 * i) by lia.
assert (YA : (Y + 4 * i) mod 4 = 0) by (clear - Y4; Z.div_mod_to_equations; lia).
bato 0xc05a8. astep. chk_merge OBY 4.
bato 0xc05b4.
rewrite (swrap32_small (i + 1)) by lia.
astep. sh_if.
(let X1c := fresh "X1c" in chunk_uncons XC as X1c; chunk_snoc XD X1c). rewrite sb_f32_snoc in XD. rewrite <- ?f32_cons in XC.
replace (Y + 4 * i + 4) with (Y + 4 * (i + 1)) in * by lia.
rewrite <- E62 in FR.
eapply (IH _ cw' (i + 1)); try eassumption; try reflexivity;
try (rewrite length_app; cbn [length] in *; lia); try (cbn [length] in *; lia).
Qed.
End SIL.
Definition sb_A_iir_mem16 : Z := 0xa6ad8.
Definition RA_sbd_iir_n : Z := 0xc0678.

Lemma sbd_n4 : forall (usp S OUT A f MODE fsz Y : Z) (g : nat -> word) (stk8 fst0 : word) (s : sbd_state bptr) (a : sb_addrs) (cw : word) (rest : list word)
(gp tp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_fr g) -> g 33%nat = Z_to_bv 64 (Z.shiftr (S + 20) 3 + SHB) -> g 34%nat = Z_to_bv 64 (S + 20) -> g 54%nat = stk8 ->
g 62%nat = Z_to_bv 64 OUT -> g 40%nat = Z_to_bv 64 S -> g 61%nat = Z_to_bv 64 1 ->
rw_cells bsegs m S (sbp_hdr s a) -> rw_cells bsegs m (S + 36) [C4 fst0] -> rw_cells bsegs m (S + 40) (sbp_ptrs s a OUT) ->
sbd_frame_size s = fsz -> sbd_lpcSize s = 8 -> 1 <= fsz <= 320 -> Z.of_nat (length rest) + 1 = fsz ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= usp + -736 -> (S + 160 <= SH_LO \/ SH_HI <= S) -> IMG_TOP_B <= S ->
0 < OUT -> OUT + 8000 < 2^63 ->
Y = OUT + 4 * fsz -> rw_cells bsegs m Y (f32 (cw :: rest)) -> aobj bsegs m Y (4 * fsz) -> Y mod 4 = 0 -> IMG_TOP_B <= Y -> (Y + 4 * fsz <= SH_LO \/ SH_HI <= Y) ->
(S + 160 <= Y \/ Y + 4 * fsz <= S) -> Y + 4 * fsz <= usp + -736 ->
SH_HI <= usp + -736 -> usp < 2^63 ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (xa7 : word) (ys' : list word),
ms = MS (R_N usp S A f MODE gp tp (Z_to_bv 64 RA_sbd_iir_n) t0 t1 t2 (Z_to_bv 64 Y) (Z_to_bv 64 (a_iq a)) (Z_to_bv 64 Y) (Z_to_bv 64 fsz) (Z_to_bv 64 8)
(Z_to_bv 64 (a_msp a)) stk8 xa7 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 S) s11 t3 t4 t5 t6)
F (Z_to_bv 64 sb_A_iir_mem16) fc None m1 (seg_rom bsegs)
/\ munch [(S + 36, S + 40); (Y, Y + 4 * fsz)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 (S + 36) [C4 (Z_to_bv 64 1)] /\ rw_cells bsegs m1 Y (f32 ys') /\ Z.of_nat (length ys') = fsz)
(MS (R_N usp S A f MODE gp tp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 S) s11 t3 t4 t5 t6) F (Z_to_bv 64 0xc0534) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR E33 E34 E54 E62 E40 E61 HD FST PT EFS ELPC HFS LR OBS S8 SPOS SLO SOFF SIMG O0 O1 EY YC OBY Y4 YI YOFF SY YLO LOS SPH MI.
unfold R_N, RA_sbd_iir_n, sb_A_iir_mem16 in *. unfold SH_LO, SH_HI in SOFF, YOFF. unfold IMG_TOP_B in SIMG. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof OBY as (OY0 & OY1 & _). unfold APP_TOP in OY1.
pose proof (munch_refl [(S + 36, S + 40); (Y, Y + 4 * fsz)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(S + 36, S + 40); (Y, Y + 4 * fsz)]) by (cbn; unfold SH_LO, SH_HI; lia).
pose proof FR as FR0.
unfold sb_fr in FR. cbn [map seq] in FR. rewrite E33, E34, E54, E40, E61 in FR. unfold sbp_hdr in HD. rewrite EFS, ELPC in HD. unfold sbp_ptrs in PT.
bato 0xc0544. rewrite sx32_small by (unfold int31; lia). astep. sh_if.
bato 0xc0554.
pose proof (aobj_munch bsegs _ m _ Y (4 * fsz) OBY MU (shfree_of_aobj bsegs _ m Y (4 * fsz) OF OBY)) as OBYc.
lazymatch type of MU with munch _ _ ?mc =>
pose proof (munch_refl [(Y, Y + 4 * fsz)] mc) as MU0; pose proof (wmono_refl bsegs mc) as WM0;
assert (OF0 : offsh [(Y, Y + 4 * fsz)]) by (cbn; unfold SH_LO, SH_HI; lia);
assert (XD0 : rw_cells bsegs mc Y (f32 [])) by (apply rw_cells_nil; lia);
call (sb_silence_loop usp OUT Y fsz g _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Y4 YI EY O0 E62 mc rest [] cw 0 _ _ _ _ _ mc eq_refl ltac:(cbn [length]; lia) ltac:(lia) O1 OBYc OF0)
end.
all: try eassumption.
{ lia. }
{ replace (Y + 4 * 0) with Y by lia. exact YC. }
clear MU0 WM0 OF0 FR0 XD0 OBYc. unfold RSIL. rewrite E62 in FR.
bato 0xc0668. rewrite ?sx32_small by (unfold int31; lia).
bato 0xa6ad8.
replace (fsz * 4 + OUT) with Y by lia.
apply evt_done. lazymatch type of POST with rw_cells _ _ _ (f32 ?l) => eexists; eexists; exists l end. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FST|]. split; [exact POST| exact PC].
Qed.
Definition RA_sbd_qmf_n : Z := 0xc072c.

Lemma sbd_n4b : forall (usp lo S OUT A f MODE fsz : Z) (g : nat -> word) (stk8 : word) (s : sbd_state bptr) (a : sb_addrs)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_fr g) -> g 33%nat = Z_to_bv 64 (Z.shiftr (S + 20) 3 + SHB) -> g 54%nat = stk8 ->
g 62%nat = Z_to_bv 64 OUT -> g 40%nat = Z_to_bv 64 S -> g 61%nat = Z_to_bv 64 1 -> g 19%nat = Z_to_bv 64 f ->
rw_cells bsegs m S (sbp_hdr s a) -> rw_cells bsegs m (S + 40) (sbp_ptrs s a OUT) ->
sbd_frame_size s = fsz -> sbd_full_frame_size s = 2 * fsz -> 1 <= fsz <= 320 ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= lo -> (S + 160 <= SH_LO \/ SH_HI <= S) ->
0 < OUT -> OUT + 8000 < 2^63 ->
stk bsegs m lo (usp + -736) -> lo <= usp + -736 - 16 -> SH_HI <= lo -> usp < 2^63 ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (ja : list byte),
ms = MS (mkR (Z_to_bv 64 RA_sbd_qmf_n) (Z_to_bv 64 (usp + -752)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736))
(Z_to_bv 64 OUT) (Z_to_bv 64 (OUT + 4 * fsz)) (Z_to_bv 64 sb_A_H0) (Z_to_bv 64 OUT) (Z_to_bv 64 (2 * fsz)) (Z_to_bv 64 64)
(Z_to_bv 64 (a_g0 a)) (Z_to_bv 64 (a_g1 a))
(Z_to_bv 64 (S + 20)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 S) (Z_to_bv 64 MODE) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.shiftr (S + 8) 3 + SHB))
(Z_to_bv 64 f) (Z_to_bv 64 (S + 152)) (Z_to_bv 64 A) s11 t3 t4 t5 t6)
F (Z_to_bv 64 sb_A_qmf_synth) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -752, usp + -736)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -752)
/\ rw_cells bsegs m1 (usp + -752) [C8 stk8; CB 8 ja])
(MS (R_N usp S A f MODE gp tp (Z_to_bv 64 RA_sbd_iir_n) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 S) s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_iir_n)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR E33 E54 E62 E40 E61 E19 HD PT EFS EFFS HFS OBS S8 SPOS SLO SOFF O0 O1 ST LO LOS SPH MI.
unfold R_N, RA_sbd_iir_n, RA_sbd_qmf_n, sb_A_qmf_synth, sb_A_H0 in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xc0678)) with (Z_to_bv 64 0xc0678) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -752, usp + -736)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -752, usp + -736)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_fr in FR. cbn [map seq] in FR. rewrite E33, E54, E62, E40, E61, E19 in FR. unfold sbp_hdr in HD. rewrite EFS, EFFS in HD. unfold sbp_ptrs in PT.
carve_frame 16%nat ST. rename FR0 into ARG.
apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in ARG; [| reflexivity]. cbn [mk_CB_cells app] in ARG.
bato 0xc0688. rewrite ?sx32_small by (unfold int31; lia).
bato 0xc0708. rewrite ?sx32_small by (unfold int31; lia).
bato 0xa8508.
replace (fsz * 4 + OUT) with (OUT + 4 * fsz) by lia.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact ARG].
Qed.

Lemma sbd_n5 : forall (usp lo S OUT A f MODE : Z) (stk8 : word) (ja : list byte)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -752) [C8 stk8; CB 8 ja] -> stk bsegs m lo (usp + -752) -> lo <= usp + -752 -> usp < 2^63 ->
mem_inv bsegs m ->
evt bsegs (fun ms => ms = MS (R_N usp S A f MODE gp tp (Z_to_bv 64 RA_sbd_qmf_n) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 0) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xc0458) fc None m (seg_rom bsegs) /\ stk bsegs m lo (usp + -736))
(MS (mkR (Z_to_bv 64 RA_sbd_qmf_n) (Z_to_bv 64 (usp + -752)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736))
a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (S + 20)) s3 s4 (Z_to_bv 64 MODE) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.shiftr (S + 8) 3 + SHB))
(Z_to_bv 64 f) (Z_to_bv 64 (S + 152)) (Z_to_bv 64 A) s11 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbd_qmf_n)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ARG ST LO SPH MI. unfold R_N, RA_sbd_qmf_n in *.
replace (ret_pc (Z_to_bv 64 0xc072c)) with (Z_to_bv 64 0xc072c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof ST as (STa & STb & _).
astep. replace (usp + -752 + 16) with (usp + -736) by lia. release_frame ARG ST (usp + -736).
ato 0xc0458.
apply evt_done. split; [reflexivity| exact ST].
Qed.
