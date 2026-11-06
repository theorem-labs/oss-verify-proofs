(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1dg X1df X1ck X1cu X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05q X05l X05m X09f X06d.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0z5 X0ys X0x2 X0yt X0zq X11l
X0wh X0yu X124 X0yd X0wk.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition sblB_e_alloca_poison : Z := 0x51e24.
Definition sblB_e_allocas_unpoison : Z := 0x51f50.
Definition sblB_e_asan_memset : Z := 0x6689c.

Definition R_LB (usp sp : Z) (gp tp : word) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs8 xs9 xs10 xt3 xt4 xt5 xt6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 sp) gp tp xt0 xt1 xt2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
xs2 xs3 xs4 xs5 (Z_to_bv 64 SHB) (Z_to_bv 64 (18446744073709551615 - (usp + -1184))) xs8 xs9 xs10 (Z_to_bv 64 (usp + -1184)) xt3 xt4 xt5 xt6.

Definition sbvB_e1 (v : sb_vslots) (w392 w288 : word) : sb_vslots :=
SBV (v_8 v) (v_144 v) (v_280 v) w288 w392 (v_456 v) (v_480 v) (v_512 v) (v_520 v) (v_528 v) (v_544 v) (v_552 v) (v_560 v) (v_568 v).

Definition RA_sblB_pois1 : Z := 0xbf1c4.

Lemma sblB_Z_to_le_bytes_app : forall n k z, 0 <= z ->
Z_to_le_bytes (n + k) z = Z_to_le_bytes n z ++ Z_to_le_bytes k (Z.shiftr z (8 * Z.of_nat n)).
Proof.
induction n as [|n IH]; intros k z Hz; cbn [Nat.add Z_to_le_bytes app].
- rewrite Z.shiftr_0_r. reflexivity.
- f_equal. rewrite IH by (apply Z.shiftr_nonneg; lia). rewrite Z.shiftr_shiftr by lia.
replace (8 + 8 * Z.of_nat n) with (8 * Z.of_nat (S n)) by lia. reflexivity.
Qed.
Lemma sblB_le8_small : forall v, 0 <= v < 2 ^ 32 -> le8 (Z_to_bv 64 v) = le4 (Z_to_bv 64 v) ++ le4 (Z_to_bv 64 0).
Proof.
intros v Hv. unfold le8, le4, word_to_le_bytes. rewrite !unsigned_lit by lia.
change 8%nat with (4 + 4)%nat. rewrite sblB_Z_to_le_bytes_app by lia. f_equal. f_equal.
rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. cbn. lia.
Qed.
Lemma sblB_c8_split : forall (m : mem) A pre post v, 0 <= v < 2 ^ 32 ->
rw_cells bsegs m A (pre ++ C8 (Z_to_bv 64 v) :: post) -> rw_cells bsegs m A (pre ++ C4 (Z_to_bv 64 v) :: C4 (Z_to_bv 64 0) :: post).
Proof.
intros m A pre post v Hv [[W B] R]. apply cells_wf_app in W. destruct W as [W1 [_ W2]].
split; [split|].
- apply cells_wf_app. split; [exact W1| split; [exact I| split; [exact I| exact W2]]].
- rewrite cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite sblB_le8_small in B by exact Hv.
rewrite <- app_assoc in B. exact B.
- rewrite cells_size_app in *. cbn [cells_size csize] in *. exact R.
Qed.
Lemma sblB_c8_join : forall (m : mem) A pre post v, 0 <= v < 2 ^ 32 ->
rw_cells bsegs m A (pre ++ C4 (Z_to_bv 64 v) :: C4 (Z_to_bv 64 0) :: post) -> rw_cells bsegs m A (pre ++ C8 (Z_to_bv 64 v) :: post).
Proof.
intros m A pre post v Hv [[W B] R]. apply cells_wf_app in W. destruct W as [W1 [_ [_ W2]]].
split; [split|].
- apply cells_wf_app. split; [exact W1| split; [exact I| exact W2]].
- rewrite cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite sblB_le8_small by exact Hv.
rewrite <- app_assoc. exact B.
- rewrite cells_size_app in *. cbn [cells_size csize] in *. exact R.
Qed.

Definition sb_slotsS (usp S OUT A f sf MODE fsz : Z) (v : sb_vslots) (sub : Z) : list cell :=
firstn 60 (sb_slots usp S OUT A f sf MODE fsz v) ++ C4 (Z_to_bv 64 sub) :: C4 (Z_to_bv 64 0) :: skipn 61 (sb_slots usp S OUT A f sf MODE fsz v).
Lemma sblB_slots_split : forall (m : mem) usp S OUT A f sf MODE fsz v sub, v_480 v = Z_to_bv 64 sub -> 0 <= sub < 2 ^ 32 ->
rw_cells bsegs m (usp + -736) (sb_slots usp S OUT A f sf MODE fsz v) -> rw_cells bsegs m (usp + -736) (sb_slotsS usp S OUT A f sf MODE fsz v sub).
Proof.
intros m usp S OUT A f sf MODE fsz v sub E Hs H. unfold sb_slotsS. apply sblB_c8_split; [exact Hs|].
destruct v as [w8 w144 w280 w288 w392 w456 w480 w512 w520 w528 w544 w552 w560 w568]. cbn [v_480] in E. subst w480. exact H.
Qed.
Lemma sblB_slots_join : forall (m : mem) usp S OUT A f sf MODE fsz v sub, v_480 v = Z_to_bv 64 sub -> 0 <= sub < 2 ^ 32 ->
rw_cells bsegs m (usp + -736) (sb_slotsS usp S OUT A f sf MODE fsz v sub) -> rw_cells bsegs m (usp + -736) (sb_slots usp S OUT A f sf MODE fsz v).
Proof.
intros m usp S OUT A f sf MODE fsz v sub E Hs H. unfold sb_slotsS in H. apply sblB_c8_join in H; [| exact Hs].
destruct v as [w8 w144 w280 w288 w392 w456 w480 w512 w520 w528 w544 w552 w560 w568]. cbn [v_480] in E. subst w480. exact H.
Qed.
Lemma cells_size_sb_slotsS : forall usp S OUT A f sf MODE fsz v sub, cells_size (sb_slotsS usp S OUT A f sf MODE fsz v sub) = 576%nat.
Proof. reflexivity. Qed.

Lemma sblB_e1 : forall (usp lo S OUT A f sf MODE fsz FS hull sub : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs) (k : sb_rjunk)
(gp tp : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_slots usp S OUT A f sf MODE fsz v) -> v_480 v = Z_to_bv 64 sub ->
rw_cells bsegs m S (sbp_hdr s a) -> sbd_subframeSize s = FS -> sbd_frame_size s = fsz ->
((FS = 40 /\ hull = 224) \/ (FS = 80 /\ hull = 384)) -> (fsz = 160 \/ fsz = 320) -> 0 <= sub < 4 ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= lo -> (S + 160 <= SH_LO \/ SH_HI <= S) ->
0 < OUT -> OUT + 8000 < 2^63 ->
stk bsegs m lo (usp + -1216) -> lo <= usp + -1216 - 384 - 4192 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (jh : list byte),
ms = MS (R_LB usp (usp + -1216 - hull) gp tp (Z_to_bv 64 RA_sblB_pois1) (Z_to_bv 64 (sha (S + 24))) (j_t1 k) (j_t2 k)
(Z_to_bv 64 (usp + -1216 - hull + 32)) (Z_to_bv 64 (4 * FS)) (Z_to_bv 64 1) (Z_to_bv 64 1) (j_a4 k) (j_a5 k) (j_a6 k) (j_a7 k)
(Z_to_bv 64 (FS * sub)) (Z_to_bv 64 (usp + -1216 - hull + 32)) (Z_to_bv 64 (usp + -1216 - hull)) (Z_to_bv 64 0)
(Z_to_bv 64 (4 * FS)) (Z_to_bv 64 FS) (j_s10 k) (j_t3 k) (j_t4 k) (j_t5 k) (j_t6 k))
F (Z_to_bv 64 sblB_e_alloca_poison) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -5312, usp + -5304); (usp + -736, usp + -160)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -1216 - hull)
/\ rw_cells bsegs m1 (usp + -736) (sb_slots usp S OUT A f sf MODE fsz (sbvB_e1 v (Z_to_bv 64 (OUT + 4 * fsz + 4 * (FS * sub))) (Z_to_bv 64 (usp + -1216))))
/\ rw_cells bsegs m1 (usp + -1216 - hull) [CB (Z.to_nat hull) jh])
(MS (R_LA usp S OUT MODE sub gp tp k) F (Z_to_bv 64 SB_LA_PC) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL E480 HD EFS EFSZ HM HFSZ SUB OBS S8 SPOS SLO SOFF O0 O1 ST LO LOS SPH U32 MI.
unfold R_LA, R_LB, SB_LA_PC, RA_sblB_pois1, sblB_e_alloca_poison in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -5312, usp + -5304); (usp + -736, usp + -160)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -5312, usp + -5304); (usp + -736, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; lia).
pose proof (sblB_slots_split m usp S OUT A f sf MODE fsz v sub E480 ltac:(lia) SL) as SLc.
destruct v as [w8 w144 w280 w288 w392 w456 w480 w512 w520 w528 w544 w552 w560 w568]. cbn [v_480] in E480. subst w480.
unfold sb_slots, sha in SL. unfold sb_slotsS, sb_slots, sha in SLc. cbn [v_8 v_144 v_280 v_288 v_392 v_456 v_480 v_512 v_520 v_528 v_544 v_552 v_560 v_568 firstn skipn app] in SL, SLc.
unfold sbp_hdr in HD. rewrite EFS, EFSZ in HD. unfold sbvB_e1, sb_slots, sha.
cbn [v_8 v_144 v_280 v_288 v_392 v_456 v_480 v_512 v_520 v_528 v_544 v_552 v_560 v_568 firstn skipn app].
destruct HM as [(-> & ->) | (-> & ->)].
- carve_frame 224%nat ST. rename FR into HULL.
carve_frame 3864%nat ST. rename FR into JK1.
carve_frame 8%nat ST. rename FR into P1.
apply (rw_cells_split_CB bsegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
bato 0xbf0c8. rewrite sx32_small by (unfold int31; lia).
astep. clear SLc.
bato 0xbf0d0. rewrite sx32_small by (unfold int31; lia). rewrite unsigned_lit by lia. rewrite swrap32_small by lia.
bato 0xbf0f0. rewrite sx32_small by (unfold int31; lia).
bato 0xbf130. rewrite (Z.shiftl_mul_pow2 (40 * sub) 2) by lia. replace (fsz * 4 + OUT + 40 * sub * 2 ^ 2) with (OUT + 4 * fsz + 4 * (40 * sub)) by lia.
bato 0xbf1a0.
alits. replace (usp + -1216 - 224) with (usp + -1440) by lia. rewrite ?Z.mod_small by lia.
rewrite (land_m32_al (usp + -1440)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. astep. replace (usp + -1216 - 4096) with (usp + -5312) by lia.
astep. astep. sh_if.
bato 0x51e24.
release_frame P1 ST (usp + -5304). release_frame JK1 ST (usp + -1440).
replace (usp + -1440 + 32) with (usp + -1408) in * by lia.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact SL| exact HULL].
- carve_frame 384%nat ST. rename FR into HULL.
carve_frame 3704%nat ST. rename FR into JK1.
carve_frame 8%nat ST. rename FR into P1.
apply (rw_cells_split_CB bsegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
bato 0xbf0c8. rewrite sx32_small by (unfold int31; lia).
astep. clear SLc.
bato 0xbf0d0. rewrite sx32_small by (unfold int31; lia). rewrite unsigned_lit by lia. rewrite swrap32_small by lia.
bato 0xbf0f0. rewrite sx32_small by (unfold int31; lia).
bato 0xbf130. rewrite (Z.shiftl_mul_pow2 (80 * sub) 2) by lia. replace (fsz * 4 + OUT + 80 * sub * 2 ^ 2) with (OUT + 4 * fsz + 4 * (80 * sub)) by lia.
bato 0xbf1a0.
alits. replace (usp + -1216 - 384) with (usp + -1600) by lia. rewrite ?Z.mod_small by lia.
rewrite (land_m32_al (usp + -1600)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. astep. replace (usp + -1216 - 4096) with (usp + -5312) by lia.
astep. astep. sh_if.
bato 0x51e24.
release_frame P1 ST (usp + -5304). release_frame JK1 ST (usp + -1600).
replace (usp + -1600 + 32) with (usp + -1568) in * by lia.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact SL| exact HULL].
Qed.

Definition sbvB_544 (v : sb_vslots) (w : word) : sb_vslots :=
SBV (v_8 v) (v_144 v) (v_280 v) (v_288 v) (v_392 v) (v_456 v) (v_480 v) (v_512 v) (v_520 v) (v_528 v) w (v_552 v) (v_560 v) (v_568 v).
Definition RA_sblB_memset1 : Z := 0xbf24c.
Definition SBLB_PC_B : Z := 0xbf254.

Lemma sblB_e2 : forall (usp lo hb S OUT A f sf MODE fsz FS sub IS : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs10 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_slots usp S OUT A f sf MODE fsz v) ->
rw_cells bsegs m S (sbp_hdr s a) -> rw_cells bsegs m (S + 40) (sbp_ptrs s a OUT) -> sbd_subframeSize s = FS -> sb_isave_ptr OUT s = IS ->
(FS = 40 \/ FS = 80) -> (fsz = 160 \/ fsz = 320) -> 0 <= sub < 4 -> (IS = 0 \/ IS = OUT + 8 * fsz) ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo -> lo <= usp + -1216 ->
0 < OUT -> OUT + 8000 < 2^63 -> SH_HI <= lo -> usp < 2^63 ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (b0 b1 b2 : word),
((IS = 0 /\ ms = MS (R_LB usp hb gp tp (Z_to_bv 64 RA_sblB_pois1) t0 t1 t2 b0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (FS * sub)) (Z_to_bv 64 (hb + 32)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (4 * FS)) (Z_to_bv 64 FS) xs10
t3 t4 t5 t6) F (Z_to_bv 64 SBLB_PC_B) fc None m1 (seg_rom bsegs))
\/ (IS <> 0 /\ ms = MS (R_LB usp hb gp tp (Z_to_bv 64 RA_sblB_memset1) t0 t1 t2
(Z_to_bv 64 (IS + 8 * (FS * sub))) (Z_to_bv 64 0) (Z_to_bv 64 (8 * FS)) b1 a4 a5 a6 a7
(Z_to_bv 64 (FS * sub)) (Z_to_bv 64 (hb + 32)) (Z_to_bv 64 (IS + 8 * (FS * sub))) b2 (Z_to_bv 64 (4 * FS)) (Z_to_bv 64 FS) xs10
t3 t4 t5 t6) F (Z_to_bv 64 sblB_e_asan_memset) fc None m1 (seg_rom bsegs)))
/\ munch [(usp + -736, usp + -160)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 (usp + -736) (sb_slots usp S OUT A f sf MODE fsz (sbvB_544 v (Z_to_bv 64 hb))))
(MS (R_LB usp hb gp tp (Z_to_bv 64 RA_sblB_pois1) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (FS * sub)) (Z_to_bv 64 (hb + 32)) (Z_to_bv 64 hb) (Z_to_bv 64 0) (Z_to_bv 64 (4 * FS)) (Z_to_bv 64 FS) xs10 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sblB_pois1)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL HD PT EFS EIS HFS HFSZ SUB HIS OBS S8 SPOS SOFF SLO LO O0 O1 LOS SPH MI.
unfold R_LB, RA_sblB_pois1, RA_sblB_memset1, SBLB_PC_B, sblB_e_asan_memset in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xbf1c4)) with (Z_to_bv 64 0xbf1c4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(usp + -736, usp + -160)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -736, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; lia).
destruct v as [w8 w144 w280 w288 w392 w456 w480 w512 w520 w528 w544 w552 w560 w568].
unfold sb_slots, sha in SL. cbn [v_8 v_144 v_280 v_288 v_392 v_456 v_480 v_512 v_520 v_528 v_544 v_552 v_560 v_568 firstn skipn app] in SL.
unfold sbvB_544, sb_slots, sha. cbn [v_8 v_144 v_280 v_288 v_392 v_456 v_480 v_512 v_520 v_528 v_544 v_552 v_560 v_568 firstn skipn app].
unfold sbp_hdr in HD. unfold sbp_ptrs in PT. rewrite EFS in HD. rewrite EIS in PT. unfold sha.
bato 0xbf1e0.
destruct HIS as [-> | ->].
- bato 0xbf254.
apply evt_done. do 4 eexists. split; [left; split; [reflexivity| reflexivity]|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact SL].
- bato 0xbf228.
replace (OUT + 8 * fsz + FS * sub * 8) with (OUT + 8 * fsz + 8 * (FS * sub)) by lia.
bato 0xbf22c. rewrite sx32_small by (unfold int31; lia).
bato 0x6689c. rewrite (Z.shiftl_mul_pow2 FS 3) by lia. replace (FS * 2 ^ 3) with (8 * FS) by lia.
apply evt_done. do 4 eexists. split; [right; split; [lia| reflexivity]|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact SL].
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Lemma sblB_lspi8 : forall (OLD NEW IQ usp lo sub : Z) (os ns qs : list word)
(ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
aobj bsegs m OLD 32 -> aobj bsegs m NEW 32 -> aobj bsegs m IQ 32 ->
OLD mod 4 = 0 -> NEW mod 4 = 0 -> IQ mod 4 = 0 -> 0 < OLD -> 0 < NEW ->
rw_cells bsegs m OLD (f32 os) -> length os = 8%nat -> rw_cells bsegs m NEW (f32 ns) -> length ns = 8%nat ->
rw_cells bsegs m IQ (f32 qs) -> length qs = 8%nat ->
(IQ + 32 <= SH_LO \/ SH_HI <= IQ) -> IMG_TOP_B <= IQ ->
(IQ + 32 <= lo \/ usp <= IQ) -> (OLD + 32 <= lo \/ usp <= OLD) -> (NEW + 32 <= lo \/ usp <= NEW) ->
(IQ + 32 <= OLD \/ OLD + 32 <= IQ) -> (IQ + 32 <= NEW \/ NEW + 32 <= IQ) ->
client_constsB m -> stk bsegs m lo usp -> lo <= usp - 64 -> SH_HI <= lo -> usp < 2^63 -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (qs' : list word),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom bsegs)
/\ munch [(IQ, IQ + 32); (usp + -64, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp
/\ frm0 fc' /\ rw_cells bsegs m' IQ (f32 qs') /\ length qs' = 8%nat)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OLD) (Z_to_bv 64 NEW) (Z_to_bv 64 IQ) (Z_to_bv 64 8) (Z_to_bv 64 sub) (Z_to_bv 64 4) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_lsp_interpolate) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros O1 O2 O3 A1 A2 A3 P1 P2 C1 L1 C2 L2 C3 L3 SH IMG D1 D2 D3 D4 D5 CC ST LO LOS SPH MI FRM.
eapply evt_mono.
- eapply (lsp_interpolate_stmt OLD NEW IQ usp lo sub 8%nat os ns qs); try eassumption; try (cbn; lia); try (unfold LSPI_DEPTH; lia).
- intros ms' POST. exact POST.
Qed.

Lemma sblB_e2b : forall (usp hb : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s8 s9 s10 t3 t4 t5 t6 : word) F fc (m : mem),
usp < 2^63 ->
evt bsegs (fun ms => ms = MS (R_LB usp hb gp tp (Z_to_bv 64 RA_sblB_memset1) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s8 s9 s10 t3 t4 t5 t6)
F (Z_to_bv 64 SBLB_PC_B) fc None m (seg_rom bsegs))
(MS (R_LB usp hb gp tp (Z_to_bv 64 RA_sblB_memset1) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s8 s9 s10 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sblB_memset1)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SPH.
unfold R_LB, RA_sblB_memset1, SBLB_PC_B in *.
replace (ret_pc (Z_to_bv 64 0xbf24c)) with (Z_to_bv 64 0xbf24c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bato 0xbf254.
apply evt_done. reflexivity.
Qed.

Definition RA_sblB_l2l : Z := 0xbf2d4.
Definition sblB_A_lsp_to_lpc : Z := 0xae6d8.

Lemma sblB_e3 : forall (usp lo hb S OUT A f sf MODE fsz FS sub OQ : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs) (voq lq liq : list word) (xra xs4 xs5 xs10 : word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_slots usp S OUT A f sf MODE fsz v) -> v_480 v = Z_to_bv 64 sub ->
rw_cells bsegs m S (sbp_hdr s a) -> rw_cells bsegs m (S + 40) (sbp_ptrs s a OUT) -> sbd_lpcSize s = 8 -> sbd_nbSubframes s = 4 -> OQ = a_oq a -> 0 <= sub < 4 ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
rw_cells bsegs m OQ (f32 voq) -> length voq = 8%nat -> aobj bsegs m OQ 32 -> OQ mod 4 = 0 -> 0 < OQ -> OQ + 32 <= lo ->
rw_cells bsegs m (usp + -992) (f32 lq) -> length lq = 8%nat -> aobj bsegs m (usp + -992) 32 ->
rw_cells bsegs m (usp + -1088) (f32 liq) -> length liq = 8%nat -> aobj bsegs m (usp + -1088) 32 ->
client_constsB m -> stk bsegs m lo hb -> lo <= hb - 64 -> hb <= usp + -1216 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
mem_inv bsegs m -> frm0 fc ->
evt bsegs (fun ms => exists (m1 : mem) (xt0 xt1 xt2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (F' : bvmap 5 word) (fc' : bv 32) (liq' : list word),
ms = MS (R_LB usp hb gp tp (Z_to_bv 64 RA_sblB_l2l) xt0 xt1 xt2
(Z_to_bv 64 (usp + -1088)) (Z_to_bv 64 (usp + -1184)) (Z_to_bv 64 8) (Z_to_bv 64 0) xa4 xa5 xa6 xa7
(Z_to_bv 64 (FS * sub)) (Z_to_bv 64 (hb + 32)) xs4 (Z_to_bv 64 (usp + -1088)) (Z_to_bv 64 (4 * FS)) (Z_to_bv 64 FS) xs10
xt3 xt4 xt5 xt6) F' (Z_to_bv 64 sblB_A_lsp_to_lpc) fc' None m1 (seg_rom bsegs)
/\ munch [(usp + -1088, usp + -1056); (hb + -64, hb)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo hb /\ frm0 fc'
/\ rw_cells bsegs m1 (usp + -736) (sb_slots usp S OUT A f sf MODE fsz v)
/\ rw_cells bsegs m1 (usp + -1088) (f32 liq') /\ length liq' = 8%nat)
(MS (R_LB usp hb gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (FS * sub)) (Z_to_bv 64 (hb + 32)) xs4 xs5 (Z_to_bv 64 (4 * FS)) (Z_to_bv 64 FS) xs10 t3 t4 t5 t6)
F (Z_to_bv 64 SBLB_PC_B) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL E480 HD PT ELPC ENSF EOQ SUB OBS S8 SPOS SOFF SLO OQC LOQ OBOQ OQ4 OQPOS OQLO QC LQ OBQ IQC LIQ OBIQ CC ST LO HB LOS SPH U32 MI FRM.
unfold R_LB, RA_sblB_l2l, sblB_A_lsp_to_lpc, SBLB_PC_B in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _). pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof (munch_refl [(usp + -1088, usp + -1056); (hb + -64, hb)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -1088, usp + -1056); (hb + -64, hb)]) by (cbn; unfold SH_LO, SH_HI; lia).
destruct v as [w8 w144 w280 w288 w392 w456 w480 w512 w520 w528 w544 w552 w560 w568]. cbn [v_480] in E480. subst w480.
unfold sb_slots, sha in SL. cbn [v_8 v_144 v_280 v_288 v_392 v_456 v_480 v_512 v_520 v_528 v_544 v_552 v_560 v_568] in SL.
unfold sbp_hdr in HD. unfold sbp_ptrs in PT. rewrite ELPC, ENSF in HD. rewrite <- EOQ in PT. unfold sha.
bato 0xbf2ac.
rewrite !sx32_small by (unfold int31; lia).
astep.
call (sblB_lspi8 OQ (usp + -992) (usp + -1088) hb lo sub voq lq liq).
all: try eassumption.
all: try (unfold IMG_TOP_B, SH_LO, SH_HI in *; clear - U32 OQ4 OQPOS OQLO LO HB LOS' SPH STa; first [lia | Z.div_mod_to_equations; lia]).
bato 0xbf2c4. rewrite sx32_small by (unfold int31; lia).
bato 0xae6d8.
apply evt_done. do 14 eexists. exists x17. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact PC|]. split; [exact PC0|]. split; [exact SL|]. split; [exact PC1| exact POST].
Qed.

Definition RA_sblB_memset2 : Z := 0xbf4b8.
Definition sbvB_456 (v : sb_vslots) (w : word) : sb_vslots :=
SBV (v_8 v) (v_144 v) (v_280 v) (v_288 v) (v_392 v) w (v_480 v) (v_512 v) (v_520 v) (v_528 v) (v_544 v) (v_552 v) (v_560 v) (v_568 v).

Lemma sblB_e4 : forall (usp lo hb S OUT A f sf MODE fsz FS sub PG AK LPI : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs) (vpg lak lpi : list word) (xs4 xs10 : word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_slots usp S OUT A f sf MODE fsz v) -> v_480 v = Z_to_bv 64 sub ->
rw_cells bsegs m S (sbp_hdr s a) -> rw_cells bsegs m (S + 40) (sbp_ptrs s a OUT) -> sbd_lpcSize s = 8 -> sbd_subframeSize s = FS -> PG = a_pg a ->
(FS = 40 \/ FS = 80) -> 0 <= sub < 4 ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
rw_cells bsegs m PG (f32 vpg) -> length vpg = 4%nat -> aobj bsegs m PG 16 -> PG mod 4 = 0 -> 0 < PG -> PG + 16 <= lo -> (PG + 16 <= SH_LO \/ SH_HI <= PG) -> IMG_TOP_B <= PG ->
(S + 160 <= PG \/ PG + 16 <= S) ->
AK = usp + -1184 -> rw_cells bsegs m AK (f32 lak) -> length lak = 8%nat -> aobj bsegs m AK 32 ->
LPI = usp + -800 -> rw_cells bsegs m LPI (f32 lpi) -> length lpi = 4%nat -> aobj bsegs m LPI 16 ->
lo <= hb -> hb <= usp + -1216 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
mem_inv bsegs m -> frm0 fc ->
evt bsegs (fun ms => exists (m1 : mem) (xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 : word) (F' : bvmap 5 word) (fc' : bv 32) (vpg' : list word),
ms = MS (R_LB usp hb gp tp (Z_to_bv 64 RA_sblB_memset2) xt0 xt1 xt2
(Z_to_bv 64 (hb + 32)) (Z_to_bv 64 0) (Z_to_bv 64 (4 * FS)) xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 (FS * sub)) (Z_to_bv 64 (hb + 32)) xs4 (Z_to_bv 64 0x10360) (Z_to_bv 64 (4 * FS)) (Z_to_bv 64 FS) xs10
t3 t4 t5 t6) F' (Z_to_bv 64 sblB_e_asan_memset) fc' None m1 (seg_rom bsegs)
/\ munch [(PG, PG + 16); (usp + -736, usp + -160)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ frm0 fc'
/\ rw_cells bsegs m1 (usp + -736) (sb_slots usp S OUT A f sf MODE fsz (sbvB_456 v (Z_to_bv 64 (4 * sub))))
/\ rw_cells bsegs m1 PG (f32 vpg') /\ length vpg' = 4%nat)
(MS (R_LB usp hb gp tp (Z_to_bv 64 RA_sblB_l2l) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (FS * sub)) (Z_to_bv 64 (hb + 32)) xs4 (Z_to_bv 64 (usp + -1088)) (Z_to_bv 64 (4 * FS)) (Z_to_bv 64 FS) xs10 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sblB_l2l)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL E480 HD PT ELPC EFS EPG HFS SUB OBS S8 SPOS SOFF SLO PGC LPG OBPG PG4 PGPOS PGLO PGOFF PGIMG SPG EAK AKC LAK OBAK ELPI LPC LLP OBLP LO HB LOS SPH U32 MI FRM.
unfold R_LB, RA_sblB_l2l, RA_sblB_memset2, sblB_e_asan_memset in *. unfold SH_LO, SH_HI in SOFF, PGOFF. unfold IMG_TOP_B in PGIMG. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xbf2d4)) with (Z_to_bv 64 0xbf2d4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(PG, PG + 16); (usp + -736, usp + -160)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(PG, PG + 16); (usp + -736, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; lia).
destruct v as [w8 w144 w280 w288 w392 w456 w480 w512 w520 w528 w544 w552 w560 w568]. cbn [v_480] in E480. subst w480.
unfold sb_slots, sha in SL. cbn [v_8 v_144 v_280 v_288 v_392 v_456 v_480 v_512 v_520 v_528 v_544 v_552 v_560 v_568] in SL.
unfold sbvB_456, sb_slots, sha. cbn [v_8 v_144 v_280 v_288 v_392 v_456 v_480 v_512 v_520 v_528 v_544 v_552 v_560 v_568].
unfold sbp_hdr in HD. unfold sbp_ptrs in PT. rewrite ELPC, EFS in HD. rewrite <- EPG in PT. unfold sha.
do 4 (destruct vpg as [|? vpg]; [discriminate LPG|]). destruct vpg; [| discriminate LPG]. cbn [f32 map] in PGC.
do 8 (destruct lak as [|? lak]; [discriminate LAK|]). destruct lak; [| discriminate LAK]. cbn [f32 map] in AKC.
do 4 (destruct lpi as [|? lpi]; [discriminate LLP|]). destruct lpi; [| discriminate LLP]. cbn [f32 map] in LPC.
assert (AK8 : AK mod 8 = 0) by (subst AK; clear - U32; Z.div_mod_to_equations; lia).
assert (LPI8 : LPI mod 8 = 0) by (subst LPI; clear - U32; Z.div_mod_to_equations; lia).
replace (usp + -1180) with (AK + 4) in SL by lia. replace (usp + -1184) with AK in SL by lia. replace (usp + -800) with LPI in SL by lia.
replace (18446744073709551615 - (usp + -1184)) with (18446744073709551615 - AK) by lia. replace (usp + -1184) with AK by lia.
assert (SC : sub = 0 \/ sub = 1 \/ sub = 2 \/ sub = 3) by lia.
destruct SC as [-> | [-> | [-> | ->]]].
- bato 0xbf340. astep. chk_merge OBPG 4.
bato 0xbf360. rewrite sx32_small by (unfold int31; lia).
bato 0xbf3d0. astep. chk_merge OBPG 4. bato 0xbf378.
bato 0xbf3d0. astep. chk_merge OBPG 4. bato 0xbf378.
bato 0xbf3d0. astep. chk_merge OBPG 4. bato 0xbf378.
bato 0xbf3d0. astep. chk_merge OBPG 4. bato 0xbf43c.
bato 0xbf4a8. rewrite sx32_small by (unfold int31; lia).
bato 0x6689c.
rewrite (Z.shiftl_mul_pow2 FS 2) by lia. replace (FS * 2 ^ 2) with (4 * FS) by lia.
apply evt_done. lazymatch type of PGC with rw_cells _ _ _ [C4 ?w0; C4 ?w1; C4 ?w2; C4 ?w3] => do 11 eexists; exists [w0; w1; w2; w3] end.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
split; [replace (AK + 4) with (usp + -1180) in SL by lia; replace LPI with (usp + -800) in SL by lia; exact SL|]. split; [exact PGC| reflexivity].
- assert (PGk : (PG + 4) mod 4 = 0) by (clear - PG4; Z.div_mod_to_equations; lia).
bato 0xbf340. astep. chk_merge OBPG 4.
bato 0xbf360. rewrite sx32_small by (unfold int31; lia).
bato 0xbf3d0. astep. chk_merge OBPG 4. bato 0xbf378.
bato 0xbf3d0. astep. chk_merge OBPG 4. bato 0xbf378.
bato 0xbf3d0. astep. chk_merge OBPG 4. bato 0xbf378.
bato 0xbf3d0. astep. chk_merge OBPG 4. bato 0xbf43c.
bato 0xbf4a8. rewrite sx32_small by (unfold int31; lia).
bato 0x6689c.
rewrite (Z.shiftl_mul_pow2 FS 2) by lia. replace (FS * 2 ^ 2) with (4 * FS) by lia.
apply evt_done. lazymatch type of PGC with rw_cells _ _ _ [C4 ?w0; C4 ?w1; C4 ?w2; C4 ?w3] => do 11 eexists; exists [w0; w1; w2; w3] end.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
split; [replace (AK + 4) with (usp + -1180) in SL by lia; replace LPI with (usp + -800) in SL by lia; exact SL|]. split; [exact PGC| reflexivity].
- assert (PGk : (PG + 8) mod 4 = 0) by (clear - PG4; Z.div_mod_to_equations; lia).
bato 0xbf340. astep. chk_merge OBPG 4.
bato 0xbf360. rewrite sx32_small by (unfold int31; lia).
bato 0xbf3d0. astep. chk_merge OBPG 4. bato 0xbf378.
bato 0xbf3d0. astep. chk_merge OBPG 4. bato 0xbf378.
bato 0xbf3d0. astep. chk_merge OBPG 4. bato 0xbf378.
bato 0xbf3d0. astep. chk_merge OBPG 4. bato 0xbf43c.
bato 0xbf4a8. rewrite sx32_small by (unfold int31; lia).
bato 0x6689c.
rewrite (Z.shiftl_mul_pow2 FS 2) by lia. replace (FS * 2 ^ 2) with (4 * FS) by lia.
apply evt_done. lazymatch type of PGC with rw_cells _ _ _ [C4 ?w0; C4 ?w1; C4 ?w2; C4 ?w3] => do 11 eexists; exists [w0; w1; w2; w3] end.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
split; [replace (AK + 4) with (usp + -1180) in SL by lia; replace LPI with (usp + -800) in SL by lia; exact SL|]. split; [exact PGC| reflexivity].
- assert (PGk : (PG + 12) mod 4 = 0) by (clear - PG4; Z.div_mod_to_equations; lia).
bato 0xbf340. astep. chk_merge OBPG 4.
bato 0xbf360. rewrite sx32_small by (unfold int31; lia).
bato 0xbf3d0. astep. chk_merge OBPG 4. bato 0xbf378.
bato 0xbf3d0. astep. chk_merge OBPG 4. bato 0xbf378.
bato 0xbf3d0. astep. chk_merge OBPG 4. bato 0xbf378.
bato 0xbf3d0. astep. chk_merge OBPG 4. bato 0xbf43c.
bato 0xbf4a8. rewrite sx32_small by (unfold int31; lia).
bato 0x6689c.
rewrite (Z.shiftl_mul_pow2 FS 2) by lia. replace (FS * 2 ^ 2) with (4 * FS) by lia.
apply evt_done. lazymatch type of PGC with rw_cells _ _ _ [C4 ?w0; C4 ?w1; C4 ?w2; C4 ?w3] => do 11 eexists; exists [w0; w1; w2; w3] end.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
split; [replace (AK + 4) with (usp + -1180) in SL by lia; replace LPI with (usp + -800) in SL by lia; exact SL|]. split; [exact PGC| reflexivity].
Qed.

Definition JYB (pc : Z) (m : mem) (R : bvmap 5 word) : machine_state -> Prop :=
fun ms => exists (F' : bvmap 5 word) (fc' : bv 32), ms = MS R F' (Z_to_bv 64 pc) fc' None m (seg_rom bsegs) /\ frm0 fc'.
Ltac jyb_done := apply evt_done; do 2 eexists; split; [reflexivity| assumption].
Tactic Notation "joinyb" constr(pcJ) integer(n1) integer(n2) :=
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
eapply (evt_cut segs (JYB pcJ mc _));
[ let B := fresh "B" in if_cases B;
[ do n1 astep; jyb_done | do n2 astep; jyb_done ]
| try match goal with H : frm0 _ |- _ => clear H end;
let FRM := fresh "FRM" in intros ? (? & ? & -> & FRM) ]
end.
Definition RA_sblB_innov1 : Z := 0xbf75c.
Definition sblB_PAR (id : Z) : Z := if id =? 2 then A_split_cb_high_lbr else A_split_cb_high.

Lemma sblB_rw_f32_nth : forall (m : mem) A ws i, rw_cells bsegs m A (f32 ws) -> 0 <= i < Z.of_nat (length ws) -> exists w : word, rw_cells bsegs m (A + 4 * i) [C4 w].
Proof.
intros m A ws i H Hi. pose proof (rw_cells_f32_mid bsegs m A ws (Z.to_nat i) 1 H ltac:(lia)) as W.
replace (Z.of_nat (Z.to_nat i)) with i in W by lia.
destruct (skipn (Z.to_nat i) ws) as [|w r] eqn:E.
- exfalso. assert (L : length (skipn (Z.to_nat i) ws) = 0%nat) by (rewrite E; reflexivity). rewrite length_skipn in L. lia.
- exists w. exact W.
Qed.
Lemma sblB_ro_f32_nth : forall (m : mem) A ws i, ro_cells bsegs m A (f32 ws) -> 0 <= i < Z.of_nat (length ws) -> exists w : word, ro_cells bsegs m (A + 4 * i) [C4 w].
Proof.
intros m A ws i H Hi. pose proof (ro_f32_mid bsegs m A ws (Z.to_nat i) 1 H ltac:(lia)) as W.
replace (Z.of_nat (Z.to_nat i)) with i in W by lia.
destruct (skipn (Z.to_nat i) ws) as [|w r] eqn:E.
- exfalso. assert (L : length (skipn (Z.to_nat i) ws) = 0%nat) by (rewrite E; reflexivity). rewrite length_skipn in L. lia.
- exists w. exact W.
Qed.

Definition sbvB_280 (v : sb_vslots) (w : word) : sb_vslots :=
SBV (v_8 v) (v_144 v) w (v_288 v) (v_392 v) (v_456 v) (v_480 v) (v_512 v) (v_520 v) (v_528 v) (v_544 v) (v_552 v) (v_560 v) (v_568 v).
Lemma sblB_u8arr_rw_CB : forall (m : mem) A bs, u8arr bsegs m A bs <-> rw_cells bsegs m A [CB (length bs) bs].
Proof.
intros m A bs. unfold u8arr, rw_cells, cells_at. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize]. rewrite app_nil_r, Nat.add_0_r. tauto.
Qed.

Lemma sblB_e5c : forall (usp lo hb S OUT A D f sf MODE fsz sub id LER : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs) (pad1 : list byte) (sm : submode)
(b : bits_st bptr) (ler tab : list word) (xs4 xs10 : word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_slots usp S OUT A f sf MODE fsz v) -> v_480 v = Z_to_bv 64 sub -> v_456 v = Z_to_bv 64 (4 * sub) ->
rw_cells bsegs m S (sbp_hdr s a) -> sbd_subframeSize s = 40 ->
rw_cells bsegs m (S + 136) (sbp_cfg s pad1) -> rw_cells bsegs m (S + 152) [C4 (Z_to_bv 64 id)] ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
sbd_mode s = ModeWB -> MODE = sbmode_struct (sbd_mode s) -> aobj bsegs m MODE 216 -> (id = 2 \/ id = 3 \/ id = 4) -> aobj bsegs m (sb_sub_addr id) 88 -> lib_consts m ->
0 <= sub < 4 ->
bits_rep bsegs m A D b -> bits_ok b -> aobj bsegs m A BITS_SIZEOF -> aobj bsegs m D (sb_buf_size b) ->
(A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A) -> A + BITS_SIZEOF <= lo -> D + sb_buf_size b <= lo -> IMG_TOP_B <= A -> (S + 160 <= A \/ A + BITS_SIZEOF <= S) ->
LER = usp + -896 -> rw_cells bsegs m LER (f32 ler) -> length ler = 4%nat -> aobj bsegs m LER 16 ->
ro_cells bsegs m A_gc_quant_bound (f32 tab) -> length tab = 16%nat -> aobj bsegs m A_gc_quant_bound 64 ->
client_constsB m -> stk bsegs m lo hb -> lo <= hb - 48 -> hb <= usp + -1216 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
mem_inv bsegs m -> frm0 fc ->
evt bsegs (fun ms => exists (m1 : mem) (xt0 xt1 xt2 xa7 xt3 xt4 xt5 xt6 : word) (F' : bvmap 5 word) (fc' : bv 32),
ms = MS (R_LB usp hb gp tp (Z_to_bv 64 RA_sblB_innov1) xt0 xt1 xt2
(Z_to_bv 64 (hb + 32)) (Z_to_bv 64 (sblB_PAR id)) (Z_to_bv 64 40) (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 (S + 132)) (Z_to_bv 64 A_split_cb_shape_sign_unquant) xa7
(Z_to_bv 64 (S + 24)) (Z_to_bv 64 (hb + 32)) (Z_to_bv 64 (sha (S + 24))) (Z_to_bv 64 0x10360) (Z_to_bv 64 (4 * 40)) (Z_to_bv 64 40) xs10
xt3 xt4 xt5 xt6) F' (Z_to_bv 64 A_split_cb_shape_sign_unquant) fc' None m1 (seg_rom bsegs)
/\ munch [(A, A + BITS_SIZEOF); (hb + -48, hb); (usp + -736, usp + -160)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo hb /\ frm0 fc'
/\ rw_cells bsegs m1 (usp + -736) (sb_slots usp S OUT A f sf MODE fsz (sbvB_280 v xs4))
/\ bits_rep bsegs m1 A D (ub b 4))
(MS (R_LB usp hb gp tp (Z_to_bv 64 RA_sblB_memset2) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (40 * sub)) (Z_to_bv 64 (hb + 32)) xs4 (Z_to_bv 64 0x10360) (Z_to_bv 64 (4 * 40)) (Z_to_bv 64 40) xs10 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sblB_memset2)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL E480 E456 HD EFS CFG IDC OBS S8 SPOS SOFF SLO EMO EMODE OBM HID OBSM LC SUB REP OK OBA OBD ASH ALO DLO ATOP SEPSA ELER LERC LLER OBLER TAB LTAB OBT CC ST LO HB LOS SPH U32 MI FRM.
unfold R_LB, RA_sblB_memset2, RA_sblB_innov1, A_split_cb_shape_sign_unquant in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xbf4b8)) with (Z_to_bv 64 0xbf4b8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold IMG_TOP_B in ATOP. unfold A_gc_quant_bound in *. pose proof SEPSA as SEPSA'. unfold BITS_SIZEOF in SEPSA'.
pose proof ST as (STa & STb & _). pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof (munch_refl [(A, A + BITS_SIZEOF); (hb + -48, hb); (usp + -736, usp + -160)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(A, A + BITS_SIZEOF); (hb + -48, hb); (usp + -736, usp + -160)]) by (pose proof ASH as Y; clear - Y LOS LO HB; cbn; unfold SH_LO, SH_HI, BITS_SIZEOF in *; lia).
destruct v as [w8 w144 w280 w288 w392 w456 w480 w512 w520 w528 w544 w552 w560 w568]. cbn [v_480 v_456] in E480, E456. subst w480 w456.
unfold sb_slots, sha in SL. cbn [v_8 v_144 v_280 v_288 v_392 v_456 v_480 v_512 v_520 v_528 v_544 v_552 v_560 v_568] in SL.
unfold sbvB_280, sb_slots, sha. cbn [v_8 v_144 v_280 v_288 v_392 v_456 v_480 v_512 v_520 v_528 v_544 v_552 v_560 v_568].
unfold sbp_hdr in HD. rewrite EFS in HD. unfold sbp_cfg in CFG. unfold sha.
rewrite EMO in *. cbn [sbmode_struct] in EMODE.
assert (ESUB : sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR ModeWB = MODE + 40) by (subst MODE; reflexivity).
rewrite ESUB in CFG.
assert (M8 : MODE mod 8 = 0) by (subst MODE; reflexivity).
assert (LER8 : LER mod 8 = 0) by (subst LER; clear - U32; Z.div_mod_to_equations; lia).
replace (usp + -896) with LER in SL by lia. replace (18446744073709551615 - LER) with (18446744073709551615 - (usp + -896)) in SL by lia.
pose proof (lib_const m A_sb_wb_mode LC_sb_wb_mode LC ltac:(lc_in)) as MTAB. rewrite <- EMODE in MTAB. unfold LC_sb_wb_mode in MTAB. unfold A_sb_wb_mode in EMODE.
pose proof (lib_const m A_wb_submode2 LC_wb_submode2 LC ltac:(lc_in)) as T2.
pose proof (lib_const m A_wb_submode3 LC_wb_submode3 LC ltac:(lc_in)) as T3. pose proof (lib_const m A_wb_submode4 LC_wb_submode4 LC ltac:(lc_in)) as T4.
unfold LC_wb_submode2 in T2. unfold LC_wb_submode3 in T3. unfold LC_wb_submode4 in T4.
destruct HID as [-> | [-> | ->]]; cbn [sb_sub_addr Z.eqb Pos.eqb] in OBSM; cbn [sblB_PAR Z.eqb Pos.eqb]; unfold A_split_cb_high_lbr, A_split_cb_high.
- set (SM := A_wb_submode2) in *. assert (ESM : SM = 0xf8cc0) by reflexivity. assert (SM8 : SM mod 8 = 0) by reflexivity. clear T3 T4. clearbody SM.
bato 0xbf4e4. rewrite sx32_small by (unfold int31; lia). bato 0xbf540. rewrite <- ESM. bato 0xbf590.
astep.
call (speex_bits_unpack_unsigned_walk A D hb lo b 4 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP OK ltac:(lia) OBA OBD ASH ltac:(lia) LOS ltac:(lia) ALO DLO).
1: exact ST. 1: exact CC. 1: exact MI.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
change (snd (speex_bits_unpack_unsigned b 4)) with (ub b 4) in *. change (fst (speex_bits_unpack_unsigned b 4)) with (uv b 4) in *.
pose proof (ub_ok b 4 OK ltac:(lia)) as (OK1 & SZ1 & V1R). change (2 ^ 4) with 16 in V1R.
destruct POST as ((rjb & Lrjb & BOBJ) & (bsb & BDAT & Hbsb) & BSIDE). unfold bits_cells in BOBJ. apply (proj1 (sblB_u8arr_rw_CB _ D bsb)) in BDAT. pose proof ALO as ALO'. unfold BITS_SIZEOF in ALO'.
assert (LBSB : Z.of_nat (length bsb) = sb_buf_size b)
by (pose proof OK1 as (ZL & _); change (Z.of_nat (length (sb_data (ub b 4))) = sb_buf_size (ub b 4)) in ZL; rewrite Hbsb, length_map in ZL; rewrite ZL; exact SZ1).
destruct (sblB_rw_f32_nth _ LER ler sub LERC ltac:(lia)) as (wel & WEL).
destruct (sblB_ro_f32_nth _ 160224 tab (uv b 4) TAB ltac:(lia)) as (wgc & WGC).
bato 0xbf5d0. astep. chk_merge OBLER 4.
bato 0xbf600. rewrite (Z.shiftl_mul_pow2 (uv b 4) 2) by lia. replace (160224 + uv b 4 * 2 ^ 2) with (160224 + 4 * uv b 4) by lia.
bato 0xbf610. astep. chk_merge OBT 4.
bato 0xbf630. clear WEL WGC. astep. rewrite sx32_small by (unfold int31; lia).
bato 0xbf660. astep. joinyb 0xbf668 0 1.
bato 0xbf694. rewrite sx32_small by (unfold int31; lia).
bato 0xbf6f0. rewrite <- ESM.
bato 0xb22a8.
apply evt_done. do 11 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact PC|]. split; [assumption|]. split; [replace LER with (usp + -896) in SL by lia; exact SL|].
split; [exists rjb; split; [exact Lrjb| unfold bits_cells; exact BOBJ]|].
split; [exists bsb; split; [apply (proj2 (sblB_u8arr_rw_CB _ D bsb)); exact BDAT| exact Hbsb]| exact BSIDE].
- set (SM := A_wb_submode3) in *. assert (ESM : SM = 0xf8d40) by reflexivity. assert (SM8 : SM mod 8 = 0) by reflexivity. clear T2 T4. clearbody SM.
bato 0xbf4e4. rewrite sx32_small by (unfold int31; lia). bato 0xbf540. rewrite <- ESM. bato 0xbf590.
astep.
call (speex_bits_unpack_unsigned_walk A D hb lo b 4 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP OK ltac:(lia) OBA OBD ASH ltac:(lia) LOS ltac:(lia) ALO DLO).
1: exact ST. 1: exact CC. 1: exact MI.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
change (snd (speex_bits_unpack_unsigned b 4)) with (ub b 4) in *. change (fst (speex_bits_unpack_unsigned b 4)) with (uv b 4) in *.
pose proof (ub_ok b 4 OK ltac:(lia)) as (OK1 & SZ1 & V1R). change (2 ^ 4) with 16 in V1R.
destruct POST as ((rjb & Lrjb & BOBJ) & (bsb & BDAT & Hbsb) & BSIDE). unfold bits_cells in BOBJ. apply (proj1 (sblB_u8arr_rw_CB _ D bsb)) in BDAT. pose proof ALO as ALO'. unfold BITS_SIZEOF in ALO'.
assert (LBSB : Z.of_nat (length bsb) = sb_buf_size b)
by (pose proof OK1 as (ZL & _); change (Z.of_nat (length (sb_data (ub b 4))) = sb_buf_size (ub b 4)) in ZL; rewrite Hbsb, length_map in ZL; rewrite ZL; exact SZ1).
destruct (sblB_rw_f32_nth _ LER ler sub LERC ltac:(lia)) as (wel & WEL).
destruct (sblB_ro_f32_nth _ 160224 tab (uv b 4) TAB ltac:(lia)) as (wgc & WGC).
bato 0xbf5d0. astep. chk_merge OBLER 4.
bato 0xbf600. rewrite (Z.shiftl_mul_pow2 (uv b 4) 2) by lia. replace (160224 + uv b 4 * 2 ^ 2) with (160224 + 4 * uv b 4) by lia.
bato 0xbf610. astep. chk_merge OBT 4.
bato 0xbf630. clear WEL WGC. astep. rewrite sx32_small by (unfold int31; lia).
bato 0xbf660. astep. joinyb 0xbf668 0 1.
bato 0xbf694. rewrite sx32_small by (unfold int31; lia).
bato 0xbf6f0. rewrite <- ESM.
bato 0xb22a8.
apply evt_done. do 11 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact PC|]. split; [assumption|]. split; [replace LER with (usp + -896) in SL by lia; exact SL|].
split; [exists rjb; split; [exact Lrjb| unfold bits_cells; exact BOBJ]|].
split; [exists bsb; split; [apply (proj2 (sblB_u8arr_rw_CB _ D bsb)); exact BDAT| exact Hbsb]| exact BSIDE].
- set (SM := A_wb_submode4) in *. assert (ESM : SM = 0xf8dc0) by reflexivity. assert (SM8 : SM mod 8 = 0) by reflexivity. clear T2 T3. clearbody SM.
bato 0xbf4e4. rewrite sx32_small by (unfold int31; lia). bato 0xbf540. rewrite <- ESM. bato 0xbf590.
astep.
call (speex_bits_unpack_unsigned_walk A D hb lo b 4 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP OK ltac:(lia) OBA OBD ASH ltac:(lia) LOS ltac:(lia) ALO DLO).
1: exact ST. 1: exact CC. 1: exact MI.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
change (snd (speex_bits_unpack_unsigned b 4)) with (ub b 4) in *. change (fst (speex_bits_unpack_unsigned b 4)) with (uv b 4) in *.
pose proof (ub_ok b 4 OK ltac:(lia)) as (OK1 & SZ1 & V1R). change (2 ^ 4) with 16 in V1R.
destruct POST as ((rjb & Lrjb & BOBJ) & (bsb & BDAT & Hbsb) & BSIDE). unfold bits_cells in BOBJ. apply (proj1 (sblB_u8arr_rw_CB _ D bsb)) in BDAT. pose proof ALO as ALO'. unfold BITS_SIZEOF in ALO'.
assert (LBSB : Z.of_nat (length bsb) = sb_buf_size b)
by (pose proof OK1 as (ZL & _); change (Z.of_nat (length (sb_data (ub b 4))) = sb_buf_size (ub b 4)) in ZL; rewrite Hbsb, length_map in ZL; rewrite ZL; exact SZ1).
destruct (sblB_rw_f32_nth _ LER ler sub LERC ltac:(lia)) as (wel & WEL).
destruct (sblB_ro_f32_nth _ 160224 tab (uv b 4) TAB ltac:(lia)) as (wgc & WGC).
bato 0xbf5d0. astep. chk_merge OBLER 4.
bato 0xbf600. rewrite (Z.shiftl_mul_pow2 (uv b 4) 2) by lia. replace (160224 + uv b 4 * 2 ^ 2) with (160224 + 4 * uv b 4) by lia.
bato 0xbf610. astep. chk_merge OBT 4.
bato 0xbf630. clear WEL WGC. astep. rewrite sx32_small by (unfold int31; lia).
bato 0xbf660. astep. joinyb 0xbf668 0 1.
bato 0xbf694. rewrite sx32_small by (unfold int31; lia).
bato 0xbf6f0. rewrite <- ESM.
bato 0xb22a8.
apply evt_done. do 11 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact PC|]. split; [assumption|]. split; [replace LER with (usp + -896) in SL by lia; exact SL|].
split; [exists rjb; split; [exact Lrjb| unfold bits_cells; exact BOBJ]|].
split; [exists bsb; split; [apply (proj2 (sblB_u8arr_rw_CB _ D bsb)); exact BDAT| exact Hbsb]| exact BSIDE].
Qed.

Lemma sblB_signal_mul40 : forall (xs : list word) (p usp lo : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (m : mem)
(t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) fc,
length xs = 40%nat -> aobj bsegs m p 160 -> p mod 4 = 0 -> lo <= usp - 16 -> SH_HI <= lo -> usp < 2^63 ->
(p + 160 <= SH_LO \/ SH_HI <= p) -> (p + 160 <= lo \/ usp <= p) ->
rw_cells bsegs m p (f32 xs) -> frm0 fc -> stk bsegs m lo usp -> IMG_TOP_B <= p -> client_constsB m -> mem_inv bsegs m ->
evt bsegs (fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (xs' : list word),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom bsegs)
/\ munch [(p, p + 160); (usp + -16, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp
/\ frm0 fc' /\ rw_cells bsegs m' p (f32 xs') /\ length xs' = 40%nat)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 p) (Z_to_bv 64 40) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 B_signal_mul) fc None m (seg_rom bsegs)).
Proof.
intros until fc. intros L OB P4 LO LOS SPH XSH XAP X FRM ST PTOP CC MI.
eapply evt_mono.
- eapply (signal_mul_walk xs p usp lo ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m); rewrite ?L; try eassumption; try (cbn; lia); try reflexivity.
- intros ms' (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & f15 & fc' & m' & E & MU & WM & MI' & ST' & FRM' & X').
rewrite L in MU. do 19 eexists. split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
split; [exact FRM'|]. split; [exact X'|]. rewrite length_map. exact L.
Qed.
Definition SBLB_PC_J : Z := 0xbfcc4.

Lemma sblB_e7a : forall (usp lo hb S OUT A f sf MODE fsz sub id EX : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs) (pad1 : list byte)
(ex : list word) (xs10 : word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_slots usp S OUT A f sf MODE fsz v) ->
rw_cells bsegs m S (sbp_hdr s a) -> sbd_subframeSize s = 40 ->
rw_cells bsegs m (S + 136) (sbp_cfg s pad1) -> rw_cells bsegs m (S + 152) [C4 (Z_to_bv 64 id)] ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
sbd_mode s = ModeWB -> MODE = sbmode_struct (sbd_mode s) -> aobj bsegs m MODE 216 -> (id = 2 \/ id = 3) -> aobj bsegs m (sb_sub_addr id) 88 -> lib_consts m ->
EX = hb + 32 -> rw_cells bsegs m EX (f32 ex) -> length ex = 40%nat -> aobj bsegs m EX 160 ->
client_constsB m -> stk bsegs m lo hb -> lo <= hb - 16 -> hb <= usp + -1216 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 -> hb mod 32 = 0 ->
mem_inv bsegs m -> frm0 fc ->
evt bsegs (fun ms => exists (m1 : mem) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt5 : word) (F' : bvmap 5 word) (fc' : bv 32) (ex' : list word),
ms = MS (R_LB usp hb gp tp xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 (S + 24)) (Z_to_bv 64 EX) (v_280 v) (Z_to_bv 64 0x10360) (Z_to_bv 64 160) (Z_to_bv 64 40) xs10
xt3 (Z_to_bv 64 (S + 72)) xt5 (Z_to_bv 64 (S + 88))) F' (Z_to_bv 64 SBLB_PC_J) fc' None m1 (seg_rom bsegs)
/\ munch [(EX, EX + 160); (hb + -16, hb)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo hb /\ frm0 fc'
/\ rw_cells bsegs m1 EX (f32 ex') /\ length ex' = 40%nat)
(MS (R_LB usp hb gp tp (Z_to_bv 64 RA_sblB_innov1) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (S + 24)) (Z_to_bv 64 EX) (Z_to_bv 64 (sha (S + 24))) (Z_to_bv 64 0x10360) (Z_to_bv 64 160) (Z_to_bv 64 40) xs10 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sblB_innov1)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL HD EFS CFG IDC OBS S8 SPOS SOFF SLO EMO EMODE OBM HID OBSM LC EEX EXC LEX OBEX CC ST LO HB LOS SPH U32 HB32 MI FRM.
unfold R_LB, RA_sblB_innov1, SBLB_PC_J in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xbf75c)) with (Z_to_bv 64 0xbf75c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof ST as (STa & STb & _). pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof (munch_refl [(EX, EX + 160); (hb + -16, hb)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(EX, EX + 160); (hb + -16, hb)]) by (clear - EEX LOS LO HB SPH; cbn; unfold SH_LO, SH_HI in *; lia).
destruct v as [w8 w144 w280 w288 w392 w456 w480 w512 w520 w528 w544 w552 w560 w568]. cbn [v_280].
unfold sb_slots, sha in SL. cbn [v_8 v_144 v_280 v_288 v_392 v_456 v_480 v_512 v_520 v_528 v_544 v_552 v_560 v_568] in SL.
unfold sbp_hdr in HD. rewrite EFS in HD. unfold sbp_cfg in CFG. unfold sha.
rewrite EMO in *. cbn [sbmode_struct] in EMODE.
assert (ESUB : sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR ModeWB = MODE + 40) by (subst MODE; reflexivity).
rewrite ESUB in CFG.
assert (M8 : MODE mod 8 = 0) by (subst MODE; reflexivity).
assert (EX8 : EX mod 8 = 0) by (subst EX; clear - HB32; Z.div_mod_to_equations; lia).
pose proof (lib_const m A_sb_wb_mode LC_sb_wb_mode LC ltac:(lc_in)) as MTAB. rewrite <- EMODE in MTAB. unfold LC_sb_wb_mode in MTAB. unfold A_sb_wb_mode in EMODE.
pose proof (lib_const m A_wb_submode2 LC_wb_submode2 LC ltac:(lc_in)) as T2.
pose proof (lib_const m A_wb_submode3 LC_wb_submode3 LC ltac:(lc_in)) as T3.
unfold LC_wb_submode2 in T2. unfold LC_wb_submode3 in T3.
destruct HID as [-> | ->]; cbn [sb_sub_addr Z.eqb Pos.eqb] in OBSM.
- set (SM := A_wb_submode2) in *. assert (ESM : SM = 0xf8cc0) by reflexivity. assert (SM8 : SM mod 8 = 0) by reflexivity. clear T3. clearbody SM.
bato 0xbf768. rewrite sx32_small by (unfold int31; lia).
bato 0xbf77c. astep.
call (sblB_signal_mul40 ex EX hb lo).
all: try eassumption.
all: try (unfold IMG_TOP_B, SH_LO, SH_HI in *; clear - EEX EX8 LO HB LOS' SPH STa; first [lia | Z.div_mod_to_equations; lia]).
bato 0xbf7b8. rewrite sx32_small by (unfold int31; lia).
bato 0xbf804. rewrite <- ESM.
bato 0xbf828. rewrite sx32_small by (unfold int31; lia).
bato 0xbfcc4.
apply evt_done. do 18 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact PC|]. split; [exact PC0|]. split; [exact PC1| exact POST].
- set (SM := A_wb_submode3) in *. assert (ESM : SM = 0xf8d40) by reflexivity. assert (SM8 : SM mod 8 = 0) by reflexivity. clear T2. clearbody SM.
bato 0xbf768. rewrite sx32_small by (unfold int31; lia).
bato 0xbf77c. astep.
call (sblB_signal_mul40 ex EX hb lo).
all: try eassumption.
all: try (unfold IMG_TOP_B, SH_LO, SH_HI in *; clear - EEX EX8 LO HB LOS' SPH STa; first [lia | Z.div_mod_to_equations; lia]).
bato 0xbf7b8. rewrite sx32_small by (unfold int31; lia).
bato 0xbf804. rewrite <- ESM.
bato 0xbf828. rewrite sx32_small by (unfold int31; lia).
bato 0xbfcc4.
apply evt_done. do 18 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact PC|]. split; [exact PC0|]. split; [exact PC1| exact POST].
Qed.
Definition RA_sblB_pois2 : Z := 0xbf89c.

Lemma sblB_e7b : forall (usp lo hb S OUT A f sf MODE fsz sub EX : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs) (pad1 : list byte)
(ex : list word) (xs10 : word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_slots usp S OUT A f sf MODE fsz v) ->
rw_cells bsegs m S (sbp_hdr s a) -> sbd_subframeSize s = 40 ->
rw_cells bsegs m (S + 136) (sbp_cfg s pad1) -> rw_cells bsegs m (S + 152) [C4 (Z_to_bv 64 4)] ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
sbd_mode s = ModeWB -> MODE = sbmode_struct (sbd_mode s) -> aobj bsegs m MODE 216 -> aobj bsegs m (sb_sub_addr 4) 88 -> lib_consts m ->
EX = hb + 32 -> rw_cells bsegs m EX (f32 ex) -> length ex = 40%nat -> aobj bsegs m EX 160 ->
client_constsB m -> stk bsegs m lo hb -> lo <= hb - 224 - 4192 -> hb <= usp + -1216 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 -> hb mod 32 = 0 ->
mem_inv bsegs m -> frm0 fc ->
evt bsegs (fun ms => exists (m1 : mem) (xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt5 : word) (F' : bvmap 5 word) (fc' : bv 32) (ex' : list word) (jh : list byte),
ms = MS (R_LB usp (hb + -224) gp tp (Z_to_bv 64 RA_sblB_pois2) xt0 xt1 xt2 (Z_to_bv 64 (hb + -192)) (Z_to_bv 64 160) xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 (hb + -192)) (Z_to_bv 64 EX) (Z_to_bv 64 hb) (Z_to_bv 64 (hb + -224)) (Z_to_bv 64 160) (Z_to_bv 64 40) (Z_to_bv 64 40)
xt3 (Z_to_bv 64 (S + 72)) xt5 (Z_to_bv 64 (S + 88))) F' (Z_to_bv 64 sblB_e_alloca_poison) fc' None m1 (seg_rom bsegs)
/\ munch [(EX, EX + 160); (hb + -16, hb); (hb + -4096, hb + -4088)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ stk bsegs m1 lo (hb + -224) /\ frm0 fc'
/\ rw_cells bsegs m1 EX (f32 ex') /\ length ex' = 40%nat
/\ rw_cells bsegs m1 (hb + -224) [CB 224 jh])
(MS (R_LB usp hb gp tp (Z_to_bv 64 RA_sblB_innov1) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (S + 24)) (Z_to_bv 64 EX) (Z_to_bv 64 (sha (S + 24))) (Z_to_bv 64 0x10360) (Z_to_bv 64 160) (Z_to_bv 64 40) xs10 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sblB_innov1)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL HD EFS CFG IDC OBS S8 SPOS SOFF SLO EMO EMODE OBM OBSM LC EEX EXC LEX OBEX CC ST LO HB LOS SPH U32 HB32 MI FRM.
unfold R_LB, RA_sblB_innov1, RA_sblB_pois2, sblB_e_alloca_poison in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xbf75c)) with (Z_to_bv 64 0xbf75c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof ST as (STa & STb & _). pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof (munch_refl [(EX, EX + 160); (hb + -16, hb); (hb + -4096, hb + -4088)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(EX, EX + 160); (hb + -16, hb); (hb + -4096, hb + -4088)]) by (clear - EEX LOS LO HB SPH; cbn; unfold SH_LO, SH_HI in *; lia).
destruct v as [w8 w144 w280 w288 w392 w456 w480 w512 w520 w528 w544 w552 w560 w568].
unfold sb_slots, sha in SL. cbn [v_8 v_144 v_280 v_288 v_392 v_456 v_480 v_512 v_520 v_528 v_544 v_552 v_560 v_568] in SL.
unfold sbp_hdr in HD. rewrite EFS in HD. unfold sbp_cfg in CFG. unfold sha.
rewrite EMO in *. cbn [sbmode_struct] in EMODE.
assert (ESUB : sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR ModeWB = MODE + 40) by (subst MODE; reflexivity).
rewrite ESUB in CFG.
assert (M8 : MODE mod 8 = 0) by (subst MODE; reflexivity).
assert (EX8 : EX mod 8 = 0) by (subst EX; clear - HB32; Z.div_mod_to_equations; lia).
pose proof (lib_const m A_sb_wb_mode LC_sb_wb_mode LC ltac:(lc_in)) as MTAB. rewrite <- EMODE in MTAB. unfold LC_sb_wb_mode in MTAB. unfold A_sb_wb_mode in EMODE.
pose proof (lib_const m A_wb_submode4 LC_wb_submode4 LC ltac:(lc_in)) as T4. unfold LC_wb_submode4 in T4.
cbn [sb_sub_addr Z.eqb Pos.eqb] in OBSM.
set (SM := A_wb_submode4) in *. assert (ESM : SM = 0xf8dc0) by reflexivity. assert (SM8 : SM mod 8 = 0) by reflexivity. clearbody SM.
bato 0xbf768. rewrite sx32_small by (unfold int31; lia).
bato 0xbf77c. astep.
call (sblB_signal_mul40 ex EX hb lo).
all: try eassumption.
all: try (unfold IMG_TOP_B, SH_LO, SH_HI in *; clear - EEX EX8 LO HB LOS' SPH STa; first [lia | Z.div_mod_to_equations; lia]).
bato 0xbf7b8. rewrite sx32_small by (unfold int31; lia).
bato 0xbf804. rewrite <- ESM.
bato 0xbf828. rewrite sx32_small by (unfold int31; lia).
bato 0xbf840. rewrite sx32_small by (unfold int31; lia).
carve_frame 224%nat PC. rename FR into HULL.
carve_frame 3864%nat PC. rename FR into JK1.
carve_frame 8%nat PC. rename FR into P1.
apply (rw_cells_split_CB bsegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
bato 0xbf87c. alits.
replace (hb - 224) with (hb + -224) by lia. rewrite ?Z.mod_small by lia.
rewrite (land_m32_al (hb + -224)) by (clear - STa SPH LO HB HB32; first [lia | Z.div_mod_to_equations; lia]).
astep. astep. replace (hb - 4096) with (hb + -4096) by lia.
astep. astep. sh_if.
bato 0x51e24.
release_frame P1 PC (hb + -4088). release_frame JK1 PC (hb + -224).
replace (hb + -224 + 32) with (hb + -192) in * by lia.
apply evt_done. do 14 eexists. lazymatch goal with H : rw_cells _ _ EX (f32 ?l) |- _ => exists l end. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact PC|]. split; [assumption|]. split; [exact PC1|]. split; [exact POST| exact HULL].
Qed.
Definition RA_sblB_memset3 : Z := 0xbf8c4.
Definition RA_sblB_innov2 : Z := 0xbf99c.
Definition sbvB_144 (v : sb_vslots) (w : word) : sb_vslots :=
SBV (v_8 v) w (v_280 v) (v_288 v) (v_392 v) (v_456 v) (v_480 v) (v_512 v) (v_520 v) (v_528 v) (v_544 v) (v_552 v) (v_560 v) (v_568 v).

Lemma sblB_e8 : forall (usp lo hb2 S OUT A f sf MODE fsz I2 EX HB : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_slots usp S OUT A f sf MODE fsz v) ->
rw_cells bsegs m S (sbp_hdr s a) -> sbd_subframeSize s = 40 ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
lo <= hb2 -> hb2 <= usp + -1216 -> SH_HI <= lo -> usp < 2^63 ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (R_LB usp hb2 gp tp (Z_to_bv 64 RA_sblB_memset3) t0 t1 t2 (Z_to_bv 64 I2) (Z_to_bv 64 0) (Z_to_bv 64 160) a3 a4 a5 a6 a7
(Z_to_bv 64 I2) (Z_to_bv 64 EX) (Z_to_bv 64 HB) (Z_to_bv 64 40) (Z_to_bv 64 160) (Z_to_bv 64 40) (Z_to_bv 64 40)
t3 t4 t5 t6) F (Z_to_bv 64 sblB_e_asan_memset) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -736, usp + -160)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 (usp + -736) (sb_slots usp S OUT A f sf MODE fsz (sbvB_544 v (Z_to_bv 64 hb2))))
(MS (R_LB usp hb2 gp tp (Z_to_bv 64 RA_sblB_pois2) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 I2) (Z_to_bv 64 EX) (Z_to_bv 64 HB) (Z_to_bv 64 hb2) (Z_to_bv 64 160) (Z_to_bv 64 40) (Z_to_bv 64 40)
t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sblB_pois2)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL HD EFS OBS S8 SPOS SOFF SLO LO HB2 LOS SPH MI.
unfold R_LB, RA_sblB_pois2, RA_sblB_memset3, sblB_e_asan_memset in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xbf89c)) with (Z_to_bv 64 0xbf89c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(usp + -736, usp + -160)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -736, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; lia).
destruct v as [w8 w144 w280 w288 w392 w456 w480 w512 w520 w528 w544 w552 w560 w568].
unfold sb_slots, sha in SL. cbn [v_8 v_144 v_280 v_288 v_392 v_456 v_480 v_512 v_520 v_528 v_544 v_552 v_560 v_568] in SL.
unfold sbvB_544, sb_slots, sha. cbn [v_8 v_144 v_280 v_288 v_392 v_456 v_480 v_512 v_520 v_528 v_544 v_552 v_560 v_568].
unfold sbp_hdr in HD. rewrite EFS in HD. unfold sha.
bato 0xbf8b4. rewrite sx32_small by (unfold int31; lia).
bato 0x6689c. alits.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact SL].
Qed.

Lemma sblB_e9 : forall (usp lo hb2 S OUT A f sf MODE fsz I2 EX HB : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs) (pad1 : list byte)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_slots usp S OUT A f sf MODE fsz v) ->
rw_cells bsegs m (S + 136) (sbp_cfg s pad1) -> rw_cells bsegs m (S + 152) [C4 (Z_to_bv 64 4)] ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
sbd_mode s = ModeWB -> MODE = sbmode_struct (sbd_mode s) -> aobj bsegs m MODE 216 -> aobj bsegs m (sb_sub_addr 4) 88 -> lib_consts m ->
lo <= hb2 -> hb2 <= usp + -1216 -> SH_HI <= lo -> usp < 2^63 ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (xa7 : word),
ms = MS (R_LB usp hb2 gp tp (Z_to_bv 64 RA_sblB_innov2) t0 t1 t2
(Z_to_bv 64 I2) (Z_to_bv 64 A_split_cb_high) (Z_to_bv 64 40) (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 (S + 132)) (Z_to_bv 64 A_split_cb_shape_sign_unquant) xa7
(Z_to_bv 64 I2) (Z_to_bv 64 EX) (Z_to_bv 64 HB) (Z_to_bv 64 40) (Z_to_bv 64 160) (Z_to_bv 64 40) (Z_to_bv 64 40)
t3 t4 t5 t6) F (Z_to_bv 64 A_split_cb_shape_sign_unquant) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -736, usp + -160)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 (usp + -736) (sb_slots usp S OUT A f sf MODE fsz (sbvB_144 v (Z_to_bv 64 HB))))
(MS (R_LB usp hb2 gp tp (Z_to_bv 64 RA_sblB_memset3) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 I2) (Z_to_bv 64 EX) (Z_to_bv 64 HB) (Z_to_bv 64 40) (Z_to_bv 64 160) (Z_to_bv 64 40) (Z_to_bv 64 40)
t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sblB_memset3)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL CFG IDC OBS S8 SPOS SOFF SLO EMO EMODE OBM OBSM LC LO HB2 LOS SPH MI.
unfold R_LB, RA_sblB_memset3, RA_sblB_innov2, A_split_cb_shape_sign_unquant, A_split_cb_high in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xbf8c4)) with (Z_to_bv 64 0xbf8c4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(usp + -736, usp + -160)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -736, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; lia).
destruct v as [w8 w144 w280 w288 w392 w456 w480 w512 w520 w528 w544 w552 w560 w568].
unfold sb_slots, sha in SL. cbn [v_8 v_144 v_280 v_288 v_392 v_456 v_480 v_512 v_520 v_528 v_544 v_552 v_560 v_568] in SL.
unfold sbvB_144, sb_slots, sha. cbn [v_8 v_144 v_280 v_288 v_392 v_456 v_480 v_512 v_520 v_528 v_544 v_552 v_560 v_568].
unfold sbp_cfg in CFG. unfold sha.
rewrite EMO in *. cbn [sbmode_struct] in EMODE.
assert (ESUB : sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR ModeWB = MODE + 40) by (subst MODE; reflexivity).
rewrite ESUB in CFG.
assert (M8 : MODE mod 8 = 0) by (subst MODE; reflexivity).
pose proof (lib_const m A_sb_wb_mode LC_sb_wb_mode LC ltac:(lc_in)) as MTAB. rewrite <- EMODE in MTAB. unfold LC_sb_wb_mode in MTAB. unfold A_sb_wb_mode in EMODE.
pose proof (lib_const m A_wb_submode4 LC_wb_submode4 LC ltac:(lc_in)) as T4. unfold LC_wb_submode4 in T4.
cbn [sb_sub_addr Z.eqb Pos.eqb] in OBSM.
set (SM := A_wb_submode4) in *. assert (ESM : SM = 0xf8dc0) by reflexivity. assert (SM8 : SM mod 8 = 0) by reflexivity. clearbody SM.
bato 0xbf8f4. rewrite sx32_small by (unfold int31; lia). bato 0xbf940. rewrite <- ESM.
bato 0xb22a8.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact SL].
Qed.
Definition RA_sblB_unpois1 : Z := 0xbfaa4.

Lemma sblB_e10 : forall (usp lo hb2 S OUT A f sf MODE fsz I2 EX : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs)
(ex i2 : list word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_slots usp S OUT A f sf MODE fsz v) -> v_544 v = Z_to_bv 64 hb2 -> v_144 v = Z_to_bv 64 (hb2 + 224) ->
rw_cells bsegs m S (sbp_hdr s a) -> sbd_subframeSize s = 40 ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
I2 = hb2 + 32 -> rw_cells bsegs m I2 (f32 i2) -> length i2 = 40%nat -> aobj bsegs m I2 160 ->
EX = hb2 + 256 -> rw_cells bsegs m EX (f32 ex) -> length ex = 40%nat -> aobj bsegs m EX 160 ->
client_constsB m -> stk bsegs m lo hb2 -> lo <= hb2 - 16 -> hb2 + 224 <= usp + -1216 -> SH_HI <= lo -> usp < 2^63 -> hb2 mod 32 = 0 ->
mem_inv bsegs m -> frm0 fc ->
evt bsegs (fun ms => exists (m1 : mem) (xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (F' : bvmap 5 word) (fc' : bv 32) (ex' i2' : list word),
ms = MS (R_LB usp hb2 gp tp (Z_to_bv 64 RA_sblB_unpois1) xt0 xt1 xt2 (Z_to_bv 64 hb2) (Z_to_bv 64 (hb2 + 224)) xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 (hb2 + 224)) (Z_to_bv 64 EX) (v_280 v) (Z_to_bv 64 (S + 24)) (Z_to_bv 64 160) (Z_to_bv 64 0) (Z_to_bv 64 0)
xt3 xt4 xt5 xt6) F' (Z_to_bv 64 sblB_e_allocas_unpoison) fc' None m1 (seg_rom bsegs)
/\ munch [(I2, I2 + 160); (EX, EX + 160); (hb2 + -16, hb2)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo hb2 /\ frm0 fc'
/\ rw_cells bsegs m1 EX (f32 ex') /\ length ex' = 40%nat /\ rw_cells bsegs m1 I2 (f32 i2') /\ length i2' = 40%nat)
(MS (R_LB usp hb2 gp tp (Z_to_bv 64 RA_sblB_innov2) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 I2) (Z_to_bv 64 EX) (Z_to_bv 64 (hb2 + 224)) (Z_to_bv 64 40) (Z_to_bv 64 160) (Z_to_bv 64 40) (Z_to_bv 64 40)
t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sblB_innov2)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL V544 V144 HD EFS OBS S8 SPOS SOFF SLO EI2 I2C LI2 OBI2 EEX EXC LEX OBEX CC ST LO HB LOS SPH HB32 MI FRM.
unfold R_LB, RA_sblB_innov2, RA_sblB_unpois1, sblB_e_allocas_unpoison in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xbf99c)) with (Z_to_bv 64 0xbf99c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof ST as (STa & STb & _). pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof (munch_refl [(I2, I2 + 160); (EX, EX + 160); (hb2 + -16, hb2)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(I2, I2 + 160); (EX, EX + 160); (hb2 + -16, hb2)]) by (clear - EI2 EEX LOS LO HB SPH; cbn; unfold SH_LO, SH_HI in *; lia).
destruct v as [w8 w144 w280 w288 w392 w456 w480 w512 w520 w528 w544 w552 w560 w568]. cbn [v_544 v_144 v_280] in V544, V144 |- *. subst w544 w144.
unfold sb_slots, sha in SL. cbn [v_8 v_144 v_280 v_288 v_392 v_456 v_480 v_512 v_520 v_528 v_544 v_552 v_560 v_568] in SL.
unfold sbp_hdr in HD. rewrite EFS in HD. unfold sha.
assert (EX8 : EX mod 8 = 0) by (subst EX; clear - HB32; Z.div_mod_to_equations; lia).
assert (I28 : I2 mod 8 = 0) by (subst I2; clear - HB32; Z.div_mod_to_equations; lia).
bato 0xbf9b8. rewrite sx32_small by (unfold int31; lia).
bato 0xbf9c4. astep.
call (sblB_signal_mul40 i2 I2 hb2 lo).
all: try eassumption.
all: try (unfold IMG_TOP_B, SH_LO, SH_HI in *; clear - EI2 I28 LO HB LOS' SPH STa; first [lia | Z.div_mod_to_equations; lia]).
rename PC1 into I2C'. rename POST into LI2'.
lazymatch type of LI2' with length ?l = _ => do 40 (destruct l as [|? l]; [discriminate LI2'|]); destruct l; [| discriminate LI2'] end. cbn [f32 map] in I2C'.
do 40 (destruct ex as [|? ex]; [discriminate LEX|]). destruct ex; [| discriminate LEX]. cbn [f32 map] in EXC.
bato 0xbf9d4. rewrite sx32_small by (unfold int31; lia).
bato 0xbf9dc.
bato 0xbfa94.
bato 0x51f50.
apply evt_done. do 16 eexists.
lazymatch type of EXC with rw_cells _ _ _ ?cs => let l := eval cbv beta iota zeta delta [map] in (map (fun c => match c with C4 w => w | _ => Z_to_bv 64 0 end) cs) in exists l end.
lazymatch type of I2C' with rw_cells _ _ _ ?cs => let l := eval cbv beta iota zeta delta [map] in (map (fun c => match c with C4 w => w | _ => Z_to_bv 64 0 end) cs) in exists l end.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact PC|]. split; [assumption|]. split; [exact EXC|]. split; [reflexivity|]. split; [exact I2C'| reflexivity].
Qed.

Lemma sblB_e11 : forall (usp lo hb2 S OUT A f sf MODE fsz EX : Z) (v : sb_vslots) (jh : list byte) (xs4 xs5 xs8 xs9 xs10 : word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_slots usp S OUT A f sf MODE fsz v) ->
rw_cells bsegs m hb2 [CB 224 jh] -> stk bsegs m lo hb2 -> lo <= hb2 -> hb2 + 224 <= usp + -1216 -> usp < 2^63 -> SH_HI <= lo ->
evt bsegs (fun ms =>
ms = MS (R_LB usp (hb2 + 224) gp tp (Z_to_bv 64 RA_sblB_unpois1) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (hb2 + 224)) (Z_to_bv 64 EX) xs4 xs5 xs8 xs9 xs10
t3 (Z_to_bv 64 (S + 72)) t5 (Z_to_bv 64 (S + 88))) F (Z_to_bv 64 SBLB_PC_J) fc None m (seg_rom bsegs)
/\ stk bsegs m lo (hb2 + 224))
(MS (R_LB usp hb2 gp tp (Z_to_bv 64 RA_sblB_unpois1) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (hb2 + 224)) (Z_to_bv 64 EX) xs4 xs5 xs8 xs9 xs10 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sblB_unpois1)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL HULL ST LO0 HB SPH LOS.
unfold R_LB, RA_sblB_unpois1, SBLB_PC_J in *.
replace (ret_pc (Z_to_bv 64 0xbfaa4)) with (Z_to_bv 64 0xbfaa4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold sb_slots, sha in SL.
bato 0xbfcc4.
release_frame HULL ST (hb2 + 224).
apply evt_done. split; [reflexivity| exact ST].
Qed.
Lemma sblB_f32_snoc l x : f32 l ++ [C4 x] = f32 (l ++ [x]).
Proof. rewrite f32_app, f32_cons, f32_nil. reflexivity. Qed.

Section ISLB.
Variables (usp S OUT A f sf MODE fsz : Z) (v : sb_vslots).
Variables (EX Y NW : Z) (exs : list word).
Variable spv : Z.
Variables rav gp tp t2v s2v s5v s9v s10v t3v t4v t5v t6v : word.
Hypothesis Y4 : Y mod 4 = 0.
Hypothesis YI : IMG_TOP_B <= Y.
Hypothesis YP : 0 < Y.
Hypothesis EX4 : EX mod 4 = 0.
Hypothesis YSL : Y + 8 * NW <= usp + -736.
Hypothesis USP : usp < 2^63.
Definition RISB (i : Z) (t0v t1v a1v : word) : bvmap 5 word :=
R_LB usp spv gp tp rav t0v t1v t2v (Z_to_bv 64 (Y + 8 * i)) a1v (Z_to_bv 64 (4 * i)) (Z_to_bv 64 (18446744073709551615 - EX)) (Z_to_bv 64 1) (Z_to_bv 64 1)
(Z_to_bv 64 (4 * NW)) (Z_to_bv 64 (Y + 8 * i)) s2v (Z_to_bv 64 EX) (Z_to_bv 64 Y) s5v (Z_to_bv 64 (4 * NW)) s9v s10v t3v t4v t5v t6v.
Definition islB_post (fc : bv 32) (mI : mem) : machine_state -> Prop :=
fun ms' => exists t0' t1' a1' F' m' (ys' : list word),
ms' = MS (RISB NW t0' t1' a1') F' (Z_to_bv 64 0xbfd9c) fc None m' (seg_rom bsegs)
/\ munch [(Y, Y + 8 * NW)] mI m' /\ wmono bsegs mI m' /\ mem_inv bsegs m'
/\ Z.of_nat (length ys') = 2 * NW /\ rw_cells bsegs m' Y (f32 ys') /\ rw_cells bsegs m' EX (f32 exs).
Lemma sblB_is_loop : forall (n : nat) (mI : mem) (rest done : list word) (i : Z) (t0v t1v a1v : word) F fc mc,
length rest = (2 * n + 2)%nat -> 2 * i = Z.of_nat (length done) -> i + 1 + Z.of_nat n = NW -> NW < 2^29 -> Z.of_nat (length exs) = NW ->
aobj bsegs mI Y (8 * NW) -> aobj bsegs mI EX (4 * NW) -> offsh [(Y, Y + 8 * NW)] -> (Y + 8 * NW <= EX \/ EX + 4 * NW <= Y) ->
mem_inv bsegs mc -> munch [(Y, Y + 8 * NW)] mI mc -> wmono bsegs mI mc ->
rw_cells bsegs mc (usp + -736) (sb_slots usp S OUT A f sf MODE fsz v) ->
rw_cells bsegs mc Y (f32 done) -> rw_cells bsegs mc (Y + 8 * i) (f32 rest) -> rw_cells bsegs mc EX (f32 exs) ->
evt bsegs (islB_post fc mI) (MS (RISB i t0v t1v a1v) F (Z_to_bv 64 0xbfd18) fc None mc (seg_rom bsegs)).
Proof using Y4 YI YP EX4 YSL USP.
induction n as [|n IH]; intros mI rest done i t0v t1v a1v F fc mc LR Hi HN HNW LEX OBY OBX OF SEP MI MU WM SL XD XC EXC;
(destruct rest as [|cw [|c1 rest]]; [exfalso; cbn [length] in LR; lia | exfalso; cbn [length] in LR; lia |]);
pose proof OBY as (OY0 & OY1 & _); pose proof OBX as (OX0 & OX1 & _); unfold APP_TOP in *; pose proof YI as YI'; unfold IMG_TOP_B in YI';
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
destruct (sblB_rw_f32_nth mc EX exs i EXC ltac:(cbn [length] in *; lia)) as (wx & WIN);
pose proof SL as SL0; unfold sb_slots, sha in SL;
unfold RISB, R_LB; rewrite !f32_cons in XC; cbn [length] in *.
- destruct rest; [| exfalso; cbn [length] in LR; lia]. rewrite f32_nil in XC.
bato 0xbfd30. astep. chk_merge OBX 4.
bato 0xbfd60. astep. chk_merge OBY 4.
bato 0xbfd74. astep. sh_if.
bato 0xbfd9c.
(let X1c := fresh "X1c" in chunk_uncons XC as X1c; chunk_snoc XD X1c). rewrite sblB_f32_snoc in XD.
chunk_snoc XD XC. rewrite sblB_f32_snoc in XD.
replace (Y + 8 * i + 8) with (Y + 8 * NW) by lia. replace (4 * i + 4) with (4 * NW) by lia.
apply evt_done. unfold islB_post, RISB, R_LB. do 5 eexists. lazymatch type of XD with rw_cells _ _ _ (f32 ?l) => exists l end.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [rewrite !length_app; cbn [length]; lia|]. split; [exact XD| exact EXC].
- bato 0xbfd30. astep. chk_merge OBX 4.
bato 0xbfd60. astep. chk_merge OBY 4.
bato 0xbfd74. astep. sh_if.
(let X1c := fresh "X1c" in chunk_uncons XC as X1c; chunk_snoc XD X1c). rewrite sblB_f32_snoc in XD.
(let X2c := fresh "X2c" in chunk_uncons XC as X2c; chunk_snoc XD X2c). rewrite sblB_f32_snoc in XD. rewrite <- ?f32_cons in XC.
replace (Y + 8 * i + 4 + 4) with (Y + 8 * (i + 1)) in * by lia. replace (Y + 8 * i + 8) with (Y + 8 * (i + 1)) in * by lia.
replace (4 * i + 4) with (4 * (i + 1)) by lia.
clear WIN. clear SL. rename SL0 into SL.
eapply (IH mI rest _ (i + 1)); try eassumption; try reflexivity;
try (rewrite !length_app; cbn [length] in *; lia); try (cbn [length] in *; lia).
Qed.
End ISLB.

Section XBLB.
Variables (usp S OUT : Z) (s : sbd_state bptr) (a : sb_addrs).
Variables (EX NW : Z) (exs : list word).
Variable spv : Z.
Variables rav gp tp t1v t3v t4v t5v t6v s4v s5v s9v s10v a1v : word.
Hypothesis XB4 : a_exc a mod 4 = 0.
Hypothesis XBI : IMG_TOP_B <= a_exc a.
Hypothesis XBP : 0 < a_exc a.
Hypothesis EX4 : EX mod 4 = 0.
Hypothesis S8 : S mod 8 = 0.
Hypothesis USP : usp < 2^63.
Definition RXBB (i : Z) (t0v a0v a2v a6v a7v : word) : bvmap 5 word :=
R_LB usp spv gp tp rav t0v t1v (Z_to_bv 64 (S + 72)) a0v a1v a2v (Z_to_bv 64 (4 * i)) (Z_to_bv 64 (18446744073709551615 - EX)) (Z_to_bv 64 (4 * NW)) a6v a7v
(Z_to_bv 64 (sha (S + 72))) (Z_to_bv 64 EX) s4v s5v (Z_to_bv 64 (4 * NW)) s9v s10v t3v t4v t5v t6v.
Definition xblB_post (fc : bv 32) (mI : mem) : machine_state -> Prop :=
fun ms' => exists t0' a0' a2' a6' a7' F' m' (ys' : list word),
ms' = MS (RXBB NW t0' a0' a2' a6' a7') F' (Z_to_bv 64 0xbfecc) fc None m' (seg_rom bsegs)
/\ munch [(a_exc a, a_exc a + 4 * NW)] mI m' /\ wmono bsegs mI m' /\ mem_inv bsegs m'
/\ Z.of_nat (length ys') = NW /\ rw_cells bsegs m' (a_exc a) (f32 ys') /\ rw_cells bsegs m' EX (f32 exs).
Lemma sblB_xb_loop : forall (mI : mem) (rest done : list word) (cw : word) (i : Z) (t0v a0v a2v a6v a7v : word) F fc mc,
i = Z.of_nat (length done) -> i + 1 + Z.of_nat (length rest) = NW -> NW < 2^29 -> Z.of_nat (length exs) = NW ->
aobj bsegs mI (a_exc a) (4 * NW) -> aobj bsegs mI EX (4 * NW) -> aobj bsegs mI S 160 -> offsh [(a_exc a, a_exc a + 4 * NW)] ->
(a_exc a + 4 * NW <= EX \/ EX + 4 * NW <= a_exc a) -> (a_exc a + 4 * NW <= S \/ S + 160 <= a_exc a) ->
mem_inv bsegs mc -> munch [(a_exc a, a_exc a + 4 * NW)] mI mc -> wmono bsegs mI mc ->
rw_cells bsegs mc (S + 40) (sbp_ptrs s a OUT) ->
rw_cells bsegs mc (a_exc a) (f32 done) -> rw_cells bsegs mc (a_exc a + 4 * i) (f32 (cw :: rest)) -> rw_cells bsegs mc EX (f32 exs) ->
evt bsegs (xblB_post fc mI) (MS (RXBB i t0v a0v a2v a6v a7v) F (Z_to_bv 64 0xbfe38) fc None mc (seg_rom bsegs)).
Proof using XB4 XBI XBP EX4 S8 USP.
intros mI rest.
induction rest as [|cw' rest IH]; intros done cw i t0v a0v a2v a6v a7v F fc mc Hi HN HNW LEX OBY OBX OBS OF SEP SEPS MI MU WM PT XD XC EXC;
pose proof OBY as (OY0 & OY1 & _); pose proof OBX as (OX0 & OX1 & _); pose proof OBS as (OS0 & OS1 & _); unfold APP_TOP in *;
pose proof XBI as YI'; unfold IMG_TOP_B in YI';
pose proof (aobj_munch bsegs _ mI mc S 160 OBS MU (shfree_of_aobj bsegs _ mI S 160 OF OBS)) as OBSc;
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
destruct (sblB_rw_f32_nth mc EX exs i EXC ltac:(cbn [length] in *; lia)) as (wx & WIN);
unfold sbp_ptrs in PT;
assert (AL : (4 * i + a_exc a) mod 4 = 0) by (rewrite Z.add_comm, Z.mul_comm, Z_mod_plus_full; exact XB4);
unfold RXBB, R_LB, sha; rewrite !f32_cons in XC; cbn [length] in *.
- rewrite f32_nil in XC.
bato 0xbfe50. astep. chk_merge OBX 4.
bato 0xbfe98. astep. chk_merge OBY 4.
bato 0xbfea4. astep. sh_if.
bato 0xbfecc.
chunk_snoc XD XC. rewrite sblB_f32_snoc in XD.
replace (4 * i + 4) with (4 * NW) by lia.
apply evt_done. unfold xblB_post, RXBB, R_LB, sha. do 7 eexists. lazymatch type of XD with rw_cells _ _ _ (f32 ?l) => exists l end.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [rewrite length_app; cbn [length]; lia|]. split; [exact XD| exact EXC].
- bato 0xbfe50. astep. chk_merge OBX 4.
bato 0xbfe98. astep. chk_merge OBY 4.
bato 0xbfea4. astep. sh_if.
(let X1c := fresh "X1c" in chunk_uncons XC as X1c; chunk_snoc XD X1c). rewrite sblB_f32_snoc in XD. rewrite <- ?f32_cons in XC.
replace (a_exc a + 4 * i + 4) with (a_exc a + 4 * (i + 1)) in * by lia.
replace (4 * i + 4) with (4 * (i + 1)) by lia.
clear WIN OBSc AL. lazymatch type of PT with rw_cells ?sg ?mm _ _ => change (rw_cells sg mm (S + 40) (sbp_ptrs s a OUT)) in PT end. fold (sha (S + 72)).
eapply (IH _ cw' (i + 1)); try eassumption; try reflexivity;
try (rewrite length_app; cbn [length] in *; lia); try (cbn [length] in *; lia).
Qed.
End XBLB.
Definition SBLB_PC_K : Z := 0xbfd9c.

Lemma sblB_e12a0 : forall (usp lo hb S OUT A f sf MODE fsz EX : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs) (xs2 xs4 xs5 xs8 xs9 xs10 xra : word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_slots usp S OUT A f sf MODE fsz v) ->
rw_cells bsegs m (S + 40) (sbp_ptrs s a OUT) -> sb_isave_ptr OUT s = 0 ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
lo <= hb -> hb <= usp + -1216 -> SH_HI <= lo -> usp < 2^63 -> mem_inv bsegs m ->
evt bsegs (fun ms =>
ms = MS (R_LB usp hb gp tp xra t0 t1 t2 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
xs2 (Z_to_bv 64 EX) xs4 xs5 xs8 xs9 xs10 t3 t4 t5 t6) F (Z_to_bv 64 SBLB_PC_K) fc None m (seg_rom bsegs))
(MS (R_LB usp hb gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
xs2 (Z_to_bv 64 EX) xs4 xs5 xs8 xs9 xs10 t3 t4 t5 t6)
F (Z_to_bv 64 SBLB_PC_J) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL PT EIS OBS S8 SPOS SOFF SLO LO HB LOS SPH MI.
unfold R_LB, SBLB_PC_J, SBLB_PC_K in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
unfold sb_slots, sha in SL. unfold sbp_ptrs in PT. rewrite EIS in PT. unfold sha.
bato 0xbfd9c.
apply evt_done. reflexivity.
Qed.

Lemma sblB_e12a1 : forall (usp lo hb S OUT A f sf MODE fsz FS EX Y : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs) (exs yw : list word) (xs2 xs5 xs9 xs10 xra : word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_slots usp S OUT A f sf MODE fsz v) ->
rw_cells bsegs m S (sbp_hdr s a) -> sbd_subframeSize s = FS -> (FS = 40 \/ FS = 80) ->
rw_cells bsegs m (S + 40) (sbp_ptrs s a OUT) -> sb_isave_ptr OUT s <> 0 -> 0 < sb_isave_ptr OUT s < 2^63 ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
rw_cells bsegs m EX (f32 exs) -> Z.of_nat (length exs) = FS -> aobj bsegs m EX (4 * FS) -> EX mod 4 = 0 -> hb <= EX ->
rw_cells bsegs m Y (f32 yw) -> Z.of_nat (length yw) = 2 * FS -> aobj bsegs m Y (8 * FS) -> Y mod 4 = 0 -> IMG_TOP_B <= Y -> Y + 8 * FS <= lo -> 0 < Y ->
(Y + 8 * FS <= SH_LO \/ SH_HI <= Y) -> (S + 160 <= Y \/ Y + 8 * FS <= S) ->
lo <= hb -> hb <= usp + -1216 -> SH_HI <= lo -> usp < 2^63 -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (xt0 xt1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 : word) (F' : bvmap 5 word) (yw' : list word),
ms = MS (R_LB usp hb gp tp xra xt0 xt1 t2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
xs2 (Z_to_bv 64 EX) (Z_to_bv 64 Y) xs5 (Z_to_bv 64 (4 * FS)) xs9 xs10 t3 t4 t5 t6) F' (Z_to_bv 64 SBLB_PC_K) fc None m1 (seg_rom bsegs)
/\ munch [(Y, Y + 8 * FS)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 Y (f32 yw') /\ Z.of_nat (length yw') = 2 * FS)
(MS (R_LB usp hb gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
xs2 (Z_to_bv 64 EX) (Z_to_bv 64 Y) xs5 (Z_to_bv 64 (4 * FS)) xs9 xs10 t3 t4 t5 t6)
F (Z_to_bv 64 SBLB_PC_J) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL HD EFS HFS PT NIS RIS OBS S8 SPOS SOFF SLO EXC LEX OBEX EX4 HBEX YC LY OBY Y4 YI YLO YP YOFF SEPSY LO HB LOS SPH MI.
unfold R_LB, SBLB_PC_J, SBLB_PC_K in *. unfold SH_LO, SH_HI in SOFF, YOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(Y, Y + 8 * FS)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(Y, Y + 8 * FS)]) by (cbn; unfold SH_LO, SH_HI; lia).
pose proof SL as SL0. unfold sb_slots, sha in SL. unfold sbp_hdr in HD. rewrite EFS in HD. pose proof PT as PT0. unfold sbp_ptrs in PT. unfold sha.
bato 0xbfcf0. rewrite sx32_small by (unfold int31; lia).
bato 0xbfd18.
pose proof OBEX as (OE0 & OE1 & _). unfold APP_TOP in OE1.
assert (LX : Z.lxor (EX mod 18446744073709551616) 18446744073709551615 = 18446744073709551615 - EX).
{ rewrite Z.mod_small by lia. rewrite OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1ch.lnot_mod64 by lia. unfold Z.lnot. rewrite <- Z.sub_1_r.
replace (- EX - 1) with ((18446744073709551615 - EX) + (-1) * 2^64) by (cbn; lia). rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
rewrite LX. clear LX.
rewrite (proj2 (Z.ltb_lt 0 Y) YP). rewrite (land3_al Y Y4). cbn [Z.b2z Z.ltb Z.compare Z.land].
rewrite (Z.shiftl_mul_pow2 FS 2) by lia. replace (FS * 2 ^ 2) with (4 * FS) by lia.
assert (XD0 : rw_cells bsegs m Y (f32 [])) by (apply rw_cells_nil; pose proof OBY as (OY0 & OY1 & _); unfold APP_TOP in OY1; lia).
replace (Z_to_bv 64 Y) with (Z_to_bv 64 (Y + 8 * 0)) at 1 by (f_equal; lia). replace (Z_to_bv 64 Y) with (Z_to_bv 64 (Y + 8 * 0)) at 2 by (f_equal; lia).
replace (Z_to_bv 64 0) with (Z_to_bv 64 (4 * 0)) at 1 by (f_equal; lia).
change (Z.land 1 1) with 1.
call (sblB_is_loop usp S OUT A f sf MODE fsz v EX Y FS exs hb xra gp tp t2 xs2 xs5 xs9 xs10 t3 t4 t5 t6 Y4 YI YP EX4 ltac:(lia) SPH (Z.to_nat (FS - 1)) m yw [] 0 t0 t1 a1 F fc m).
all: try eassumption.
all: try (cbn [length]; lia).
{ replace (Y + 8 * 0) with Y by lia. exact YC. }
apply evt_done. do 12 eexists. lazymatch type of PC0 with rw_cells _ _ _ (f32 ?l) => exists l end.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact PC0| exact PC].
Qed.

Lemma sblB_iir8 : forall (XB IQP YP MSP hb lo FS : Z) (vexc viq vm8 yp : list word)
(ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
Z.of_nat (length vexc) = FS -> (FS = 40 \/ FS = 80) -> length viq = 8%nat -> length vm8 = 8%nat -> Z.of_nat (length yp) = FS ->
aobj bsegs m XB (4 * FS) -> aobj bsegs m IQP 32 -> aobj bsegs m MSP 32 -> aobj bsegs m YP (4 * FS) ->
XB mod 4 = 0 -> IQP mod 4 = 0 -> MSP mod 4 = 0 -> YP mod 4 = 0 -> 0 < XB -> 0 < IQP -> 0 < MSP -> 0 < YP ->
lo <= hb - 128 -> SH_HI <= lo -> hb < 2^63 ->
(MSP + 32 <= SH_LO \/ SH_HI <= MSP) -> (YP + 4 * FS <= SH_LO \/ SH_HI <= YP) ->
(XB + 4 * FS <= lo \/ hb <= XB) -> (MSP + 32 <= lo \/ hb <= MSP) -> (IQP + 32 <= lo \/ hb <= IQP) -> (YP + 4 * FS <= lo \/ hb <= YP) ->
(IQP + 32 <= MSP \/ MSP + 32 <= IQP) -> (XB + 4 * FS <= MSP \/ MSP + 32 <= XB) -> (XB + 4 * FS <= IQP \/ IQP + 32 <= XB) ->
(XB + 4 * FS <= YP \/ YP + 4 * FS <= XB) -> (YP + 4 * FS <= MSP \/ MSP + 32 <= YP) -> (YP + 4 * FS <= IQP \/ IQP + 32 <= YP) ->
rw_cells bsegs m XB (f32 vexc) -> rw_cells bsegs m IQP (f32 viq) -> rw_cells bsegs m MSP (f32 vm8) -> rw_cells bsegs m YP (f32 yp) ->
frm0 fc -> stk bsegs m lo hb -> IMG_TOP_B <= YP -> IMG_TOP_B <= MSP -> client_constsB m -> mem_inv bsegs m ->
evt bsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' (ys mv : list word),
ms' = MS (mkR ra (Z_to_bv 64 hb) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (ret_pc ra) fc' None m' (seg_rom bsegs)
/\ munch [(YP, YP + 4 * FS); (MSP, MSP + 32); (hb + -128, hb)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo hb
/\ frm0 fc' /\ Z.of_nat (length ys) = FS /\ rw_cells bsegs m' YP (f32 ys)
/\ length mv = 8%nat /\ rw_cells bsegs m' MSP (f32 mv)
/\ rw_cells bsegs m' IQP (f32 viq) /\ rw_cells bsegs m' XB (f32 vexc))
(MS (mkR ra (Z_to_bv 64 hb) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 XB) (Z_to_bv 64 IQP) (Z_to_bv 64 YP) (Z_to_bv 64 FS) (Z_to_bv 64 8) (Z_to_bv 64 MSP) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 B_iir_mem16) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros LX HFS LQ LM LY OX OQ OM OY X4 Q4 M4 Y4 XP QP MP YP0 LO LOS SPH MSH YSH XAP MAP QAP YAP SQM SXM SXQ SXY SYM SYQ CX CQ CM CY FRM ST YI MI' CC MI.
assert (EQ8 : Z.of_nat (length viq) = 8) by (rewrite LQ; reflexivity).
assert (N1 : 1 <= Z.of_nat (length vexc) < 2^31) by (rewrite LX; destruct HFS; subst; lia).
assert (ORD : 2 <= Z.of_nat (length viq) < 2^31) by (rewrite EQ8; lia).
assert (LMEM : length vm8 = length viq) by (rewrite LM, LQ; reflexivity).
assert (LYS : length yp = length vexc) by (apply Nat2Z.inj; rewrite LY, LX; reflexivity).
assert (E32 : 4 * Z.of_nat (length viq) = 32) by (rewrite EQ8; reflexivity).
pose proof (iir_mem16_walk_dj vexc viq vm8 XB IQP MSP hb lo ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m LMEM N1 ORD
ltac:(rewrite LX; exact OX) ltac:(rewrite E32; exact OQ) ltac:(rewrite E32; exact OM) X4 Q4 M4 XP QP MP LO LOS SPH
ltac:(rewrite E32; exact MSH) ltac:(rewrite LX; exact XAP) ltac:(rewrite E32; exact MAP) ltac:(rewrite E32; exact QAP)
ltac:(rewrite E32; exact SQM) ltac:(rewrite LX, E32; exact SXM) ltac:(rewrite LX, E32; exact SXQ)
YP ltac:(rewrite LX; exact OY) Y4 YP0 ltac:(rewrite LX; exact YSH) ltac:(rewrite LX; exact YAP) ltac:(rewrite LX; exact SXY)
ltac:(rewrite LX, E32; exact SYM) ltac:(rewrite LX, E32; exact SYQ)
yp F t0 t1 t2 a6 a7 t3 t4 t5 t6 fc CX CQ CM CY LYS FRM ST YI MI' CC MI) as W.
rewrite LX, EQ8 in W.
eapply evt_mono; [exact W|].
intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & m' & ys & mv & EQ & MU & WM & MI2 & ST2 & FR2 & LYS' & CY2 & LMV & CM2 & CQ2 & CX2).
exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F', fc', m', ys, mv.
replace (MSP + 4 * 8) with (MSP + 32) in MU by lia.
split; [exact EQ|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact FR2|].
split; [rewrite LYS'; exact LX|]. split; [exact CY2|]. split; [rewrite LMV; exact LQ|]. split; [exact CM2|]. split; [exact CQ2|]. exact (CX2 eq_refl).
Qed.
Definition SBLB_PC_M : Z := 0xbfecc.

Lemma sblB_e12b : forall (usp lo hb S OUT A f sf MODE fsz FS EX XB IQP MSP YP : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs)
(exs vexc viq vm8 yp : list word) (xs2 xs4 xs5 xs9 xs10 xra : word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_slots usp S OUT A f sf MODE fsz v) -> v_392 v = Z_to_bv 64 YP ->
rw_cells bsegs m S (sbp_hdr s a) -> sbd_subframeSize s = FS -> sbd_lpcSize s = 8 -> (FS = 40 \/ FS = 80) ->
rw_cells bsegs m (S + 40) (sbp_ptrs s a OUT) -> XB = a_exc a -> IQP = a_iq a -> MSP = a_msp a ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
rw_cells bsegs m EX (f32 exs) -> Z.of_nat (length exs) = FS -> aobj bsegs m EX (4 * FS) -> EX mod 4 = 0 -> hb <= EX -> EX + 4 * FS <= usp ->
rw_cells bsegs m XB (f32 vexc) -> Z.of_nat (length vexc) = FS -> aobj bsegs m XB (4 * FS) -> XB mod 4 = 0 -> IMG_TOP_B <= XB -> XB + 4 * FS <= lo -> (XB + 4 * FS <= SH_LO \/ SH_HI <= XB) ->
rw_cells bsegs m IQP (f32 viq) -> length viq = 8%nat -> aobj bsegs m IQP 32 -> IQP mod 4 = 0 -> IQP + 32 <= lo -> 0 < IQP ->
rw_cells bsegs m MSP (f32 vm8) -> length vm8 = 8%nat -> aobj bsegs m MSP 32 -> MSP mod 4 = 0 -> IMG_TOP_B <= MSP -> MSP + 32 <= lo -> (MSP + 32 <= SH_LO \/ SH_HI <= MSP) ->
rw_cells bsegs m YP (f32 yp) -> Z.of_nat (length yp) = FS -> aobj bsegs m YP (4 * FS) -> YP mod 4 = 0 -> IMG_TOP_B <= YP -> YP + 4 * FS <= lo -> (YP + 4 * FS <= SH_LO \/ SH_HI <= YP) ->
(IQP + 32 <= MSP \/ MSP + 32 <= IQP) -> (XB + 4 * FS <= MSP \/ MSP + 32 <= XB) -> (XB + 4 * FS <= IQP \/ IQP + 32 <= XB) ->
(XB + 4 * FS <= YP \/ YP + 4 * FS <= XB) -> (YP + 4 * FS <= MSP \/ MSP + 32 <= YP) -> (YP + 4 * FS <= IQP \/ IQP + 32 <= YP) ->
(S + 160 <= XB \/ XB + 4 * FS <= S) -> (S + 160 <= MSP \/ MSP + 32 <= S) -> (S + 160 <= YP \/ YP + 4 * FS <= S) ->
client_constsB m -> stk bsegs m lo hb -> lo <= hb - 128 -> hb <= usp + -1216 -> SH_HI <= lo -> usp < 2^63 -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (fun ms => exists (m1 : mem) (xra' xt0 xa0 xa2 xa6 xa7 xt4 xt5 xt6 : word) (F' : bvmap 5 word) (fc' : bv 32) (vexc' vm8' yp' : list word),
ms = MS (R_LB usp hb gp tp xra' xt0 (Z_to_bv 64 32) (Z_to_bv 64 (S + 72)) xa0 (Z_to_bv 64 FS) xa2 (Z_to_bv 64 (4 * FS)) (Z_to_bv 64 (18446744073709551615 - EX))
(Z_to_bv 64 (4 * FS)) xa6 xa7
(Z_to_bv 64 (sha (S + 72))) (Z_to_bv 64 EX) (Z_to_bv 64 (sha (S + 88))) (Z_to_bv 64 (S + 24)) (Z_to_bv 64 (4 * FS)) (Z_to_bv 64 (sha (S + 24))) xs10
(Z_to_bv 64 (S + 88)) xt4 xt5 xt6) F' (Z_to_bv 64 SBLB_PC_M) fc' None m1 (seg_rom bsegs)
/\ munch [(YP, YP + 4 * FS); (MSP, MSP + 32); (hb + -128, hb); (XB, XB + 4 * FS)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo hb /\ frm0 fc'
/\ rw_cells bsegs m1 XB (f32 vexc') /\ Z.of_nat (length vexc') = FS
/\ rw_cells bsegs m1 MSP (f32 vm8') /\ length vm8' = 8%nat
/\ rw_cells bsegs m1 YP (f32 yp') /\ Z.of_nat (length yp') = FS)
(MS (R_LB usp hb gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
xs2 (Z_to_bv 64 EX) xs4 xs5 (Z_to_bv 64 (4 * FS)) xs9 xs10 t3 (Z_to_bv 64 (S + 72)) t5 (Z_to_bv 64 (S + 88)))
F (Z_to_bv 64 SBLB_PC_K) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL V392 HD EFS ELPC HFS PT EXB EIQ EMSP OBS S8 SPOS SOFF SLO EXC LEX OBEX EX4 HBEX EXU
XBC LXB OBXB XB4 XBI XBLO XBOFF IQC LIQ OBIQ IQ4 IQLO IQP0 MSC LMS OBMS MS4 MSI MSLO MSOFF YPC LYP OBYP YP4 YPI YPLO YPOFF
SEPDM SEPXM SEPXD SEPXY SEPYM SEPYD SEPSX SEPSM SEPSY CC ST LO HB LOS SPH MI FRM.
unfold R_LB, SBLB_PC_K, SBLB_PC_M in *.
unfold SH_LO, SH_HI in SOFF, XBOFF, MSOFF, YPOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof XBI as XBI'. pose proof MSI as MSI'. pose proof YPI as YPI'. unfold IMG_TOP_B in XBI', MSI', YPI'.
pose proof ST as (STa & STb & _). pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof (munch_refl [(YP, YP + 4 * FS); (MSP, MSP + 32); (hb + -128, hb); (XB, XB + 4 * FS)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(YP, YP + 4 * FS); (MSP, MSP + 32); (hb + -128, hb); (XB, XB + 4 * FS)]) by (clear - YPOFF MSOFF XBOFF LOS' LO HB SPH HFS; cbn; unfold SH_LO, SH_HI; lia).
assert (FSB : 40 <= FS <= 80) by (clear - HFS; lia).
pose proof OBXB as (OX0 & OX1 & _). pose proof OBMS as (OM0 & OM1 & _). pose proof OBYP as (OY0 & OY1 & _). unfold APP_TOP in OX1, OM1, OY1.
hide_disj.
assert (LIQz : Z.of_nat (length viq) = 8) by (rewrite LIQ; reflexivity). assert (LMSz : Z.of_nat (length vm8) = 8) by (rewrite LMS; reflexivity).
destruct v as [w8 w144 w280 w288 w392 w456 w480 w512 w520 w528 w544 w552 w560 w568]. cbn [v_392] in V392. subst w392.
unfold sb_slots, sha in SL. cbn [v_8 v_144 v_280 v_288 v_392 v_456 v_480 v_512 v_520 v_528 v_544 v_552 v_560 v_568] in SL.
unfold sbp_hdr in HD. rewrite EFS, ELPC in HD. pose proof PT as PT0. unfold sbp_ptrs in PT. rewrite <- EXB, <- EIQ, <- EMSP in PT. unfold sha.
bato 0xbfdd0. rewrite sx32_small by (unfold int31; lia).
bato 0xbfdfc. rewrite sx32_small by (unfold int31; lia).
bato 0xbfe0c. astep.
unfold hid in SEPSX, SEPSM, SEPSY.
call (sblB_iir8 XB IQP YP MSP hb lo FS vexc viq vm8 yp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LXB HFS LIQ LMS LYP OBXB OBIQ OBMS OBYP XB4 IQ4 MS4 YP4
ltac:(lia) IQP0 ltac:(lia) ltac:(lia) LO LOS ltac:(clear - HB SPH; lia)
MSOFF YPOFF (or_introl XBLO) (or_introl MSLO) (or_introl IQLO) (or_introl YPLO) SEPDM SEPXM SEPXD SEPXY SEPYM SEPYD XBC IQC MSC YPC FRM ST YPI MSI CC MI).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch bsegs _ m mc S 160 OBS MU (shfree_of_aobj bsegs _ m S 160 OF OBS)) as OBS1;
pose proof (aobj_munch bsegs _ m mc EX (4 * FS) OBEX MU (shfree_of_aobj bsegs _ m EX (4 * FS) OF OBEX)) as OBEX1;
pose proof (aobj_munch bsegs _ m mc XB (4 * FS) OBXB MU (shfree_of_aobj bsegs _ m XB (4 * FS) OF OBXB)) as OBXB1
end.
bato 0xbfe1c. rewrite sx32_small by (unfold int31; lia).
bato 0xbfe38.
pose proof OBEX as (OE0 & OE1 & _). unfold APP_TOP in OE1.
rewrite OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1ch.lnot_mod64 by lia. unfold Z.lnot.
replace (Z.pred (- EX) mod 2 ^ 64) with (18446744073709551615 - EX)
by (rewrite <- Z.sub_1_r; replace (- EX - 1) with ((18446744073709551615 - EX) + (-1) * 2^64) by (cbn; lia); rewrite Z_mod_plus_full; symmetry; apply Z.mod_small; lia).
rewrite (Z.shiftl_mul_pow2 FS 2) by lia. replace (FS * 2 ^ 2) with (4 * FS) by lia.
replace (Z_to_bv 64 0) with (Z_to_bv 64 (4 * 0)) at 2 by (f_equal; lia).
subst XB IQP MSP.
destruct vexc as [|cw rest]; [cbn [length] in LXB; lia|].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (XD0 : rw_cells bsegs mc (a_exc a) (f32 [])) by (apply rw_cells_nil; pose proof OBXB1 as (OZ0 & OZ1 & _); unfold APP_TOP in OZ1; lia);
assert (OFX : offsh [(a_exc a, a_exc a + 4 * FS)]) by (unfold hid in XBOFF; cbn; unfold SH_LO, SH_HI; lia);
pose proof (munch_refl [(a_exc a, a_exc a + 4 * FS)] mc) as MUX; pose proof (wmono_refl bsegs mc) as WMX
end.
unfold hid in SEPXY, SEPXM, SEPSX.
lazymatch type of PT with rw_cells ?sg ?mm _ _ => change (rw_cells sg mm (S + 40) (sbp_ptrs s a OUT)) in PT end.
call (sblB_xb_loop usp S OUT s a EX FS exs hb _ gp tp _ _ _ _ _ _ _ _ _ _ XB4 XBI ltac:(lia) EX4 S8 SPH x16 rest [] cw 0 _ _ _ _ _ _ _ x16
eq_refl ltac:(cbn [length] in LXB; cbn [length]; lia) ltac:(lia) LEX OBXB1 OBEX1 OBS1 OFX ltac:(left; lia) ltac:(destruct SEPSX; [right|left]; lia)
MI0 MUX WMX PT XD0 ltac:(replace (a_exc a + 4 * 0) with (a_exc a) by lia; exact POST) EXC).
apply evt_done. do 10 eexists. exists x24, x15, x26, x18, x17.
split; [unfold R_LB, sha; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact PC|]. split; [exact PC0|].
split; [exact PC6|]. split; [exact PC5|]. split; [exact PC4|]. split; [exact PC3|]. split; [exact PC2| exact PC1].
Qed.
Definition RA_sblB_e12 : Z := 0xc000c.
Lemma sblB_f32_split3 : forall (m : mem) A (ws : list word) i, rw_cells bsegs m A (f32 ws) -> 0 <= i < Z.of_nat (length ws) ->
rw_cells bsegs m A (f32 (firstn (Z.to_nat i) ws)) /\ rw_cells bsegs m (A + 4 * i) [C4 (nth (Z.to_nat i) ws (Z_to_bv 64 0))]
/\ rw_cells bsegs m (A + 4 * i + 4) (f32 (skipn (S (Z.to_nat i)) ws)).
Proof.
intros m A ws i H Hi.
rewrite <- (firstn_skipn (Z.to_nat i) ws) in H. rewrite f32_app in H. apply rw_cells_app in H as [H1 H2].
rewrite cells_size_f32, length_firstn in H2. replace (Z.of_nat (4 * Nat.min (Z.to_nat i) (length ws))) with (4 * i) in H2 by lia.
destruct (skipn (Z.to_nat i) ws) as [|w r] eqn:E.
- exfalso. assert (L : length (skipn (Z.to_nat i) ws) = 0%nat) by (rewrite E; reflexivity). rewrite length_skipn in L. lia.
- rewrite f32_cons in H2. apply rw_cells_uncons in H2 as [H3 H4]. cbn [csize] in H4.
assert (EN : nth (Z.to_nat i) ws (Z_to_bv 64 0) = w).
{ rewrite <- (firstn_skipn (Z.to_nat i) ws), E. rewrite app_nth2; rewrite length_firstn; [|lia]. replace (Z.to_nat i - Nat.min (Z.to_nat i) (length ws))%nat with 0%nat by lia. reflexivity. }
assert (ES : skipn (S (Z.to_nat i)) ws = r).
{ rewrite <- (skipn_skipn 1 (Z.to_nat i)), E. reflexivity. }
rewrite EN, ES. refine (conj H1 (conj H3 _)). replace (A + 4 * i + 4) with (A + 4 * i + Z.of_nat 4) by lia. exact H4.
Qed.
Lemma sblB_f32_join3 : forall (m : mem) A (l1 l2 : list word) (x : word),
rw_cells bsegs m A (f32 l1) -> rw_cells bsegs m (A + 4 * Z.of_nat (length l1)) [C4 x] -> rw_cells bsegs m (A + 4 * Z.of_nat (length l1) + 4) (f32 l2) ->
rw_cells bsegs m A (f32 (l1 ++ x :: l2)).
Proof.
intros m A l1 l2 x H1 H2 H3. rewrite f32_app, f32_cons. apply rw_cells_join; [exact H1|].
rewrite cells_size_f32. replace (Z.of_nat (4 * length l1)) with (4 * Z.of_nat (length l1)) by lia.
change (C4 x :: f32 l2) with ([C4 x] ++ f32 l2). apply rw_cells_join; [exact H2|]. cbn [cells_size csize]. replace (A + 4 * Z.of_nat (length l1) + Z.of_nat (4 + 0)) with (A + 4 * Z.of_nat (length l1) + 4) by lia. exact H3.
Qed.

Lemma sblB_rms16 : forall (xs : list word) (p usp lo FS : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (m : mem)
(t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) fc,
Z.of_nat (length xs) = FS -> 1 <= FS < 2^31 -> aobj bsegs m p (4 * FS) -> p mod 4 = 0 -> 0 < p -> lo <= usp - 16 -> SH_HI <= lo -> usp < 2^63 ->
(p + 4 * FS <= lo \/ usp <= p) ->
rw_cells bsegs m p (f32 xs) -> frm0 fc -> stk bsegs m lo usp -> client_constsB m -> mem_inv bsegs m ->
evt bsegs (fun ms' => exists t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) fc' m',
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 FS) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom bsegs)
/\ munch [(usp + -16, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp /\ frm0 fc')
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 FS) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 B_compute_rms16) fc None m (seg_rom bsegs)).
Proof.
intros until fc. intros LX N1 OB X4 XP LO LOS SPH XAP XC FRM ST CC MI.
pose proof (compute_rms16_walk xs p usp lo ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m ltac:(rewrite LX; exact N1) ltac:(rewrite LX; exact OB) X4 XP LO LOS SPH
ltac:(rewrite LX; exact XAP) t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc XC FRM ST CC MI) as W.
rewrite LX in W. eapply evt_mono; [exact W|].
intros ms' (t0' & t1' & t2' & a0' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & g13 & g14 & g15 & fc' & m' & EQ & REST).
do 15 eexists. exists fc', m'.
split; [exact EQ| exact REST].
Qed.

Lemma sblB_e12c : forall (usp lo hb S OUT A f sf MODE fsz FS sub XB IQP ER AK : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs)
(vexc viq ers lak : list word) (xra xs3 xs5 xs8 xs9 xs10 : word)
(gp tp t0 a0 a2 a3 a4 a5 a6 a7 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_slots usp S OUT A f sf MODE fsz v) -> v_456 v = Z_to_bv 64 (4 * sub) ->
rw_cells bsegs m S (sbp_hdr s a) -> sbd_subframeSize s = FS -> sbd_lpcSize s = 8 -> sbd_nbSubframes s = 4 -> (FS = 40 \/ FS = 80) -> 0 <= sub < 4 ->
rw_cells bsegs m (S + 40) (sbp_ptrs s a OUT) -> XB = a_exc a -> IQP = a_iq a -> ER = a_er a ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
rw_cells bsegs m XB (f32 vexc) -> Z.of_nat (length vexc) = FS -> aobj bsegs m XB (4 * FS) -> XB mod 4 = 0 -> XB + 4 * FS <= lo -> 0 < XB ->
rw_cells bsegs m IQP (f32 viq) -> length viq = 8%nat -> aobj bsegs m IQP 32 -> IQP mod 4 = 0 -> IMG_TOP_B <= IQP -> IQP + 32 <= lo -> (IQP + 32 <= SH_LO \/ SH_HI <= IQP) ->
rw_cells bsegs m ER (f32 ers) -> length ers = 4%nat -> aobj bsegs m ER 16 -> ER mod 4 = 0 -> IMG_TOP_B <= ER -> ER + 16 <= lo -> (ER + 16 <= SH_LO \/ SH_HI <= ER) ->
(IQP + 32 <= ER \/ ER + 16 <= IQP) -> (S + 160 <= IQP \/ IQP + 32 <= S) -> (S + 160 <= ER \/ ER + 16 <= S) ->
(XB + 4 * FS <= IQP \/ IQP + 32 <= XB) -> (XB + 4 * FS <= ER \/ ER + 16 <= XB) ->
AK = usp + -1184 -> rw_cells bsegs m AK (f32 lak) -> length lak = 8%nat -> aobj bsegs m AK 32 ->
client_constsB m -> stk bsegs m lo hb -> lo <= hb - 16 -> hb <= usp + -1216 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (fun ms => exists (m1 : mem) (xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (F' : bvmap 5 word) (fc' : bv 32) (viq' ers' : list word),
ms = MS (R_LB usp hb gp tp (Z_to_bv 64 RA_sblB_e12) xt0 xt1 xt2 (v_544 v) (v_288 v) xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 4) (v_288 v) (Z_to_bv 64 (sha (S + 88))) xs5 xs8 xs9 xs10
xt3 xt4 xt5 xt6) F' (Z_to_bv 64 sblB_e_allocas_unpoison) fc' None m1 (seg_rom bsegs)
/\ munch [(IQP, IQP + 32); (ER, ER + 16); (hb + -16, hb)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo hb /\ frm0 fc'
/\ rw_cells bsegs m1 IQP (f32 viq') /\ length viq' = 8%nat /\ rw_cells bsegs m1 ER (f32 ers') /\ length ers' = 4%nat)
(MS (R_LB usp hb gp tp xra t0 (Z_to_bv 64 32) (Z_to_bv 64 (S + 72)) a0 (Z_to_bv 64 FS) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (sha (S + 72))) xs3 (Z_to_bv 64 (sha (S + 88))) xs5 xs8 xs9 xs10 (Z_to_bv 64 (S + 88)) t4 t5 t6)
F (Z_to_bv 64 SBLB_PC_M) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL V456 HD EFS ELPC ENSF HFS SUB PT EXB EIQ EER OBS S8 SPOS SOFF SLO XBC LXB OBXB XB4 XBLO XBP IQC LIQ OBIQ IQ4 IQI IQLO IQOFF
ERC LER OBER ER4 ERI ERLO EROFF SEPQE SEPSQ SEPSE SEPXQ SEPXE EAK AKC LAK OBAK CC ST LO HB LOS SPH U32 MI FRM.
unfold R_LB, RA_sblB_e12, SBLB_PC_M, sblB_e_allocas_unpoison in *.
unfold SH_LO, SH_HI in SOFF, IQOFF, EROFF. pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof IQI as IQI'. pose proof ERI as ERI'. unfold IMG_TOP_B in IQI', ERI'.
pose proof ST as (STa & STb & _). pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof (munch_refl [(IQP, IQP + 32); (ER, ER + 16); (hb + -16, hb)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(IQP, IQP + 32); (ER, ER + 16); (hb + -16, hb)]) by (clear - IQOFF EROFF LOS' LO HB SPH; cbn; unfold SH_LO, SH_HI; lia).
assert (FSB : 40 <= FS <= 80) by (clear - HFS; lia).
assert (LIQz : Z.of_nat (length viq) = 8) by (rewrite LIQ; reflexivity). assert (LAKz : Z.of_nat (length lak) = 8) by (rewrite LAK; reflexivity).
assert (LERz : Z.of_nat (length ers) = 4) by (rewrite LER; reflexivity).
pose proof OBIQ as (OQ0 & OQ1 & _). pose proof OBER as (OR0 & OR1 & _). unfold APP_TOP in OQ1, OR1.
hide_disj. unfold hid in SEPSQ, SEPXQ, SEPQE.
destruct v as [w8 w144 w280 w288 w392 w456 w480 w512 w520 w528 w544 w552 w560 w568]. cbn [v_456 v_544 v_288] in V456 |- *. subst w456.
unfold sb_slots, sha in SL. cbn [v_8 v_144 v_280 v_288 v_392 v_456 v_480 v_512 v_520 v_528 v_544 v_552 v_560 v_568] in SL.
unfold sbp_hdr in HD. rewrite EFS, ELPC, ENSF in HD. unfold sbp_ptrs in PT. rewrite <- EXB, <- EIQ, <- EER in PT. unfold sha.
assert (AK8 : AK mod 8 = 0) by (subst AK; clear - U32; Z.div_mod_to_equations; lia).
do 8 (destruct lak as [|? lak]; [discriminate LAK|]). destruct lak; [| discriminate LAK]. cbn [f32 map] in AKC.
do 8 (destruct viq as [|? viq]; [discriminate LIQ|]). destruct viq; [| discriminate LIQ]. cbn [f32 map] in IQC.
bato 0xbfee0. rewrite ?sx32_small by (unfold int31; lia).
bato 0xbfeec.
rewrite <- EAK. assert (AQ1 : (4 + IQP) mod 4 = 0) by (rewrite Z.add_comm; replace (IQP + 4) with (IQP + 1 * 4) by lia; rewrite Z_mod_plus_full; exact IQ4). assert (AQ2 : (8 + IQP) mod 4 = 0) by (rewrite Z.add_comm; replace (IQP + 8) with (IQP + 2 * 4) by lia; rewrite Z_mod_plus_full; exact IQ4). assert (AQ3 : (12 + IQP) mod 4 = 0) by (rewrite Z.add_comm; replace (IQP + 12) with (IQP + 3 * 4) by lia; rewrite Z_mod_plus_full; exact IQ4). assert (AQ4 : (16 + IQP) mod 4 = 0) by (rewrite Z.add_comm; replace (IQP + 16) with (IQP + 4 * 4) by lia; rewrite Z_mod_plus_full; exact IQ4). assert (AQ5 : (20 + IQP) mod 4 = 0) by (rewrite Z.add_comm; replace (IQP + 20) with (IQP + 5 * 4) by lia; rewrite Z_mod_plus_full; exact IQ4). assert (AQ6 : (24 + IQP) mod 4 = 0) by (rewrite Z.add_comm; replace (IQP + 24) with (IQP + 6 * 4) by lia; rewrite Z_mod_plus_full; exact IQ4). assert (AQ7 : (28 + IQP) mod 4 = 0) by (rewrite Z.add_comm; replace (IQP + 28) with (IQP + 7 * 4) by lia; rewrite Z_mod_plus_full; exact IQ4).
do 8 (bato 0xbff4c; astep; chk_merge OBIQ 4).
bato 0xbff8c. astep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (CC1 : client_constsB mc) by (unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))));
pose proof (aobj_munch bsegs _ m mc XB (4 * FS) OBXB MU (shfree_of_aobj bsegs _ m XB (4 * FS) OF OBXB)) as OBXBc
end.
unfold hid in SEPXE.
call (sblB_rms16 vexc XB hb lo FS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
LXB ltac:(lia) OBXBc XB4 XBP LO LOS ltac:(clear - HB SPH; lia) (or_introl XBLO) XBC FRM ST CC1 MI).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch bsegs _ m mc S 160 OBS MU (shfree_of_aobj bsegs _ m S 160 OF OBS)) as OBS1;
pose proof (aobj_munch bsegs _ m mc ER 16 OBER MU (shfree_of_aobj bsegs _ m ER 16 OF OBER)) as OBER1
end.
assert (AER : (ER + 4 * sub) mod 4 = 0) by (rewrite Z.mul_comm, Z_mod_plus_full; exact ER4).
bato 0xbffdc. astep. chk_merge OBER 4.
destruct (sblB_f32_split3 _ ER ers sub ERC ltac:(lia)) as (ER1 & ER2 & ER3). clear ERC.
assert (LL1 : Z.of_nat (length (firstn (Z.to_nat sub) ers)) = sub) by (rewrite length_firstn; lia).
assert (LL2 : Z.of_nat (length (skipn (Datatypes.S (Z.to_nat sub)) ers)) = 3 - sub) by (rewrite length_skipn; lia).
remember (firstn (Z.to_nat sub) ers) as l1 eqn:EL1. remember (skipn (Datatypes.S (Z.to_nat sub)) ers) as l2 eqn:EL2.
remember (nth (Z.to_nat sub) ers (Z_to_bv 64 0)) as w1 eqn:EW1.
unfold hid in SEPSE.
bato 0xbffe4.
bato 0xbfffc. rewrite sx32_small by (unfold int31; lia).
bato 0x51f50.
assert (ERJ : rw_cells bsegs m0 ER (f32 (l1 ++ fmv_s (reg_get x21 10) :: l2))).
{ apply sblB_f32_join3; [exact ER1| rewrite LL1; exact ER2| rewrite LL1; exact ER3]. }
apply evt_done. do 16 eexists.
lazymatch type of IQC with rw_cells _ _ _ ?cs => let l := eval cbv beta iota zeta delta [map] in (map (fun c => match c with C4 w => w | _ => Z_to_bv 64 0 end) cs) in exists l end.
exists (l1 ++ fmv_s (reg_get x21 10) :: l2).
split; [unfold R_LB, sha; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [cbn [f32 map]; exact IQC|]. split; [reflexivity|]. split; [exact ERJ|].
apply Nat2Z.inj. rewrite length_app. cbn [length]. lia.
Qed.
Definition sbvB_480 (v : sb_vslots) (w : word) : sb_vslots :=
SBV (v_8 v) (v_144 v) (v_280 v) (v_288 v) (v_392 v) (v_456 v) w (v_512 v) (v_520 v) (v_528 v) (v_544 v) (v_552 v) (v_560 v) (v_568 v).

Lemma sblB_e13 : forall (usp hb lo S OUT A f sf MODE fsz sub : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs)
(gp tp : word) (xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs5 xs8 xs9 xs10 xt3 xt4 xt5 xt6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_slots usp S OUT A f sf MODE fsz v) -> v_288 v = Z_to_bv 64 (usp + -1216) -> v_480 v = Z_to_bv 64 sub ->
rw_cells bsegs m S (sbp_hdr s a) -> sbd_nbSubframes s = 4 -> 0 <= sub < 4 ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
lo <= usp + -1216 -> SH_HI <= lo -> usp < 2^63 -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (fun ms => exists (m1 : mem) (k : sb_rjunk) (F' : bvmap 5 word) (fc' : bv 32),
((sub < 3 /\ ms = MS (R_LA usp S OUT MODE (sub + 1) gp tp k) F' (Z_to_bv 64 SB_LA_PC) fc' None m1 (seg_rom bsegs))
\/ (sub = 3 /\ ms = MS (R_TA usp S OUT gp tp k) F' (Z_to_bv 64 SB_TA_PC) fc' None m1 (seg_rom bsegs)))
/\ munch [(usp + -256, usp + -248)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ frm0 fc'
/\ rw_cells bsegs m1 (usp + -736) (sb_slots usp S OUT A f sf MODE fsz (sbvB_480 v (Z_to_bv 64 (sub + 1)))))
(MS (R_LB usp hb gp tp (Z_to_bv 64 RA_sblB_e12) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 4) (v_288 v) xs4 xs5 xs8 xs9 xs10 xt3 xt4 xt5 xt6)
F (ret_pc (Z_to_bv 64 RA_sblB_e12)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL V288 V480 HD ENSF SUB OBS S8 SPOS SOFF SLO LO LOS SPH MI FRM.
unfold R_LB, RA_sblB_e12 in *. rewrite V288.
replace (ret_pc (Z_to_bv 64 0xc000c)) with (Z_to_bv 64 0xc000c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(usp + -256, usp + -248)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -256, usp + -248)]) by (clear - LOS' LO SPH; cbn; unfold SH_LO, SH_HI; lia).
destruct v as [w8 w144 w280 w288 w392 w456 w480 w512 w520 w528 w544 w552 w560 w568]. cbn [v_288 v_480] in V288, V480. subst w288 w480.
unfold sb_slots, sha in SL. cbn [v_8 v_144 v_280 v_288 v_392 v_456 v_480 v_512 v_520 v_528 v_544 v_552 v_560 v_568] in SL.
unfold sbp_hdr in HD. rewrite ENSF in HD. unfold sha.
bato 0xc0034. rewrite sx32_small by (unfold int31; lia).
bato 0xc0054.
assert (SC : sub < 3 \/ sub = 3) by lia. destruct SC as [SL3 | E3].
- astep. sh_if.
apply evt_done. exists m0, (SBRJ (Z_to_bv 64 786444) (Z_to_bv 64 0) xt1 xt2 (Z_to_bv 64 0) (Z_to_bv 64 4) (Z_to_bv 64 (sub + 1)) xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 4) (Z_to_bv 64 (usp + -1216)) xs4 xs5 (Z_to_bv 64 0) xs8 xs9 xs10 (Z_to_bv 64 0) xt3 xt4 xt5 xt6).
do 2 eexists. split; [left; split; [exact SL3| unfold R_LA, SB_LA_PC, sha; reflexivity]|].
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
unfold sb_slots, sbvB_480, sha; cbn [v_8 v_144 v_280 v_288 v_392 v_456 v_480 v_512 v_520 v_528 v_544 v_552 v_560 v_568]. exact SL.
- subst sub. astep. bato 0xc0280.
apply evt_done. exists m0, (SBRJ (Z_to_bv 64 786444) (Z_to_bv 64 (sha (S + 24))) xt1 xt2 (Z_to_bv 64 (S + 24)) (Z_to_bv 64 4) (Z_to_bv 64 (3 + 1)) xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 4) (Z_to_bv 64 (usp + -1216)) xs4 xs5 (Z_to_bv 64 (18446744073709551615 - (usp + -1184))) xs8 xs9 xs10 (Z_to_bv 64 (usp + -1184))
xt3 xt4 xt5 xt6).
do 2 eexists. split; [right; split; [reflexivity| unfold R_TA, SB_TA_PC, sha; reflexivity]|].
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
unfold sb_slots, sbvB_480, sha; cbn [v_8 v_144 v_280 v_288 v_392 v_456 v_480 v_512 v_520 v_528 v_544 v_552 v_560 v_568]. exact SL.
Qed.
