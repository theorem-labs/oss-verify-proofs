(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1dg X1df X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05q X081 X05l X07y X05m X09f X06d X069 X082 X08y X0b1 X05k X083 X0bh X07l X05r.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition sbl_e_alloca_poison : Z := 0x51d38.
Definition sbl_e_allocas_unpoison : Z := 0x51e64.
Definition sbl_e_asan_memset : Z := 0x667b0.

Definition R_L (usp sp S sub : Z) (gp tp : word) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 sp) gp tp xt0 xt1 xt2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -608)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 (sha (S + 24))) xs3 xs4 (Z_to_bv 64 sub) (Z_to_bv 64 (S + 24)) xs7 xs8 (Z_to_bv 64 SHB) xs10 xs11 xt3 xt4 xt5 xt6.

Definition sbv_e1 (v : sb_vslots) (w256 w264 : word) : sb_vslots :=
SBV (v_8 v) (v_120 v) (v_248 v) w256 w264 (v_296 v) (v_384 v) (v_392 v) (v_400 v) (v_416 v) (v_424 v) (v_432 v) (v_440 v).

Definition RA_sbl_pois1 : Z := 0xb7060.

Lemma sbl_e1 : forall (usp lo S OUT A f sf MODE fsz FS hull sub : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs) (k : sb_rjunk)
(gp tp : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_slots usp S OUT A f sf MODE fsz v) ->
rw_cells asegs m S (sbp_hdr s a) -> sbd_subframeSize s = FS -> sbd_frame_size s = fsz ->
((FS = 40 /\ hull = 224) \/ (FS = 80 /\ hull = 384)) -> (fsz = 160 \/ fsz = 320) -> 0 <= sub < 4 ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 <= lo -> (S + 160 <= SH_LO \/ SH_HI <= S) ->
0 <= OUT -> OUT + 8000 < 2^63 ->
stk asegs m lo (usp + -1088) -> lo <= usp + -1088 - 384 - 4192 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (jh : list byte),
ms = MS (R_L usp (usp + -1088 - hull) S sub gp tp (Z_to_bv 64 RA_sbl_pois1) (j_t0 k) (j_t1 k) (j_t2 k)
(Z_to_bv 64 (usp + -1088 - hull + 32)) (Z_to_bv 64 (4 * FS)) (Z_to_bv 64 (2^36 - 16)) (Z_to_bv 64 32) (Z_to_bv 64 32) (j_a5 k) (Z_to_bv 64 4096) (j_a7 k)
(Z_to_bv 64 (FS * sub)) (Z_to_bv 64 FS) (Z_to_bv 64 (usp + -1088 - hull)) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 OUT) (Z_to_bv 64 (usp + -1088 - hull + 32))
(j_t3 k) (j_t4 k) (j_t5 k) (j_t6 k))
F (Z_to_bv 64 sbl_e_alloca_poison) fc None m1 (seg_rom asegs)
/\ munch [(usp + -5184, usp + -5176); (usp + -608, usp + -160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -1088 - hull)
/\ rw_cells asegs m1 (usp + -608) (sb_slots usp S OUT A f sf MODE fsz (sbv_e1 v (Z_to_bv 64 (OUT + 4 * fsz + 4 * (FS * sub))) (Z_to_bv 64 (usp + -1088))))
/\ rw_cells asegs m1 (usp + -1088 - hull) [CB (Z.to_nat hull) jh])
(MS (R_LA usp S OUT MODE sub gp tp k) F (Z_to_bv 64 SB_LA_PC) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL HD EFS EFSZ HM HFSZ SUB OBS S8 SPOS SLO SOFF O0 O1 ST LO LOS SPH U32 MI.
unfold R_LA, R_L, SB_LA_PC, RA_sbl_pois1, sbl_e_alloca_poison in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -5184, usp + -5176); (usp + -608, usp + -160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -5184, usp + -5176); (usp + -608, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_slots, sha in SL. unfold sbp_hdr in HD. rewrite EFS, EFSZ in HD. unfold sha.
destruct HM as [(-> & ->) | (-> & ->)].
- carve_frame 224%nat ST. rename FR into HULL.
carve_frame 3864%nat ST. rename FR into JK1.
carve_frame 8%nat ST. rename FR into P1.
apply (rw_cells_split_CB asegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
ato 0xb6fe4. rewrite zx32_small by lia.
ato 0xb6ff0. rewrite swrap32_small by lia.
ato 0xb6ff8. rewrite sx32_small by (unfold int31; lia).
ato 0xb7018. alits. rewrite ?Z.mod_small by lia. rewrite !Z.shiftl_mul_pow2 by lia.
replace (OUT + fsz * 2 ^ 2 + 40 * sub * 2 ^ 2) with (OUT + 4 * fsz + 4 * (40 * sub)) by lia.
ato 0xb7044. alits.
replace (usp + -1088 - 224) with (usp + -1312) by lia. rewrite ?Z.mod_small by lia.
rewrite (land_m32_al (usp + -1312)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. replace (usp + -1088 - 4096) with (usp + -5184) by lia.
astep. astep. sh_if.
ato 0x51d38.
release_frame P1 ST (usp + -5176). release_frame JK1 ST (usp + -1312).
replace (usp + -1312 + 32) with (usp + -1280) in * by lia.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact SL| exact HULL].
- carve_frame 384%nat ST. rename FR into HULL.
carve_frame 3704%nat ST. rename FR into JK1.
carve_frame 8%nat ST. rename FR into P1.
apply (rw_cells_split_CB asegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
ato 0xb6fe4. rewrite zx32_small by lia.
ato 0xb6ff0. rewrite swrap32_small by lia.
ato 0xb6ff8. rewrite sx32_small by (unfold int31; lia).
ato 0xb7018. alits. rewrite ?Z.mod_small by lia. rewrite !Z.shiftl_mul_pow2 by lia.
replace (OUT + fsz * 2 ^ 2 + 80 * sub * 2 ^ 2) with (OUT + 4 * fsz + 4 * (80 * sub)) by lia.
ato 0xb7044. alits.
replace (usp + -1088 - 384) with (usp + -1472) by lia. rewrite ?Z.mod_small by lia.
rewrite (land_m32_al (usp + -1472)) by (clear - STa SPH LO U32; first [lia | Z.div_mod_to_equations; lia]).
astep. replace (usp + -1088 - 4096) with (usp + -5184) by lia.
astep. astep. sh_if.
ato 0x51d38.
release_frame P1 ST (usp + -5176). release_frame JK1 ST (usp + -1472).
replace (usp + -1472 + 32) with (usp + -1440) in * by lia.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact SL| exact HULL].
Qed.
Definition sbv_416 (v : sb_vslots) (w : word) : sb_vslots :=
SBV (v_8 v) (v_120 v) (v_248 v) (v_256 v) (v_264 v) (v_296 v) (v_384 v) (v_392 v) (v_400 v) w (v_424 v) (v_432 v) (v_440 v).
Definition RA_sbl_memset1 : Z := 0xb70b0.
Definition SBL_PC_B : Z := 0xb70bc.

Lemma sbl_e2 : forall (usp lo hb S OUT A f sf MODE fsz FS sub IS : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_slots usp S OUT A f sf MODE fsz v) ->
rw_cells asegs m S (sbp_hdr s a) -> rw_cells asegs m (S + 40) (sbp_ptrs s a OUT) -> sbd_subframeSize s = FS -> sb_isave_ptr OUT s = IS ->
(FS = 40 \/ FS = 80) -> (fsz = 160 \/ fsz = 320) -> 0 <= sub < 4 -> (IS = 0 \/ IS = OUT + 8 * fsz) ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo -> lo <= usp + -1088 ->
0 < OUT -> OUT + 8000 < 2^63 -> SH_HI <= lo -> usp < 2^63 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
((IS = 0 /\ ms = MS (R_L usp hb S sub gp tp (Z_to_bv 64 RA_sbl_pois1) t0 t1 t2
(Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (S + 80)) a3 a4 a5 a6 a7
(Z_to_bv 64 0) (Z_to_bv 64 FS) (Z_to_bv 64 (sha (S + 120))) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 (S + 32)) (Z_to_bv 64 (hb + 32))
t3 t4 t5 t6) F (Z_to_bv 64 SBL_PC_B) fc None m1 (seg_rom asegs))
\/ (IS <> 0 /\ ms = MS (R_L usp hb S sub gp tp (Z_to_bv 64 RA_sbl_memset1) t0 t1 t2
(Z_to_bv 64 (IS + 8 * (FS * sub))) (Z_to_bv 64 0) (Z_to_bv 64 (8 * FS)) a3 a4 a5 a6 a7
(Z_to_bv 64 (IS + 8 * (FS * sub))) (Z_to_bv 64 FS) (Z_to_bv 64 (sha (S + 120))) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 (S + 32)) (Z_to_bv 64 (hb + 32))
t3 t4 t5 t6) F (Z_to_bv 64 sbl_e_asan_memset) fc None m1 (seg_rom asegs)))
/\ munch [(usp + -608, usp + -160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 (usp + -608) (sb_slots usp S OUT A f sf MODE fsz (sbv_416 v (Z_to_bv 64 hb))))
(MS (R_L usp hb S sub gp tp (Z_to_bv 64 RA_sbl_pois1) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (FS * sub)) (Z_to_bv 64 FS) (Z_to_bv 64 hb) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 OUT) (Z_to_bv 64 (hb + 32)) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbl_pois1)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL HD PT EFS EIS HFS HFSZ SUB HIS OBS S8 SPOS SOFF SLO LO O0 O1 LOS SPH MI.
unfold R_L, RA_sbl_pois1, RA_sbl_memset1, SBL_PC_B, sbl_e_asan_memset in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xb7060)) with (Z_to_bv 64 0xb7060) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(usp + -608, usp + -160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -608, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_slots, sha in SL. unfold sbp_hdr in HD. unfold sbp_ptrs in PT. rewrite EFS in HD. rewrite EIS in PT. unfold sha.

ato 0xb7088.
destruct HIS as [-> | ->].
- ato 0xb70bc.
apply evt_done. eexists. split; [left; split; [reflexivity| reflexivity]|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact SL].
- astep. sh_if.
ato 0xb7098.
rewrite sx32_small by (unfold int31; lia).
ato 0x667b0.
rewrite !Z.shiftl_mul_pow2 by lia.
replace (OUT + 8 * fsz + FS * sub * 2 ^ 3) with (OUT + 8 * fsz + 8 * (FS * sub)) by lia. replace (FS * 2 ^ 3) with (8 * FS) by lia.
apply evt_done. eexists. split; [right; split; [lia| reflexivity]|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact SL].
Qed.

Lemma sbl_e2b : forall (usp hb S OUT A f sf MODE fsz FS sub : Z) (v : sb_vslots) (xs3 : word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_slots usp S OUT A f sf MODE fsz v) ->
SH_HI <= usp + -608 -> usp < 2^63 -> mem_inv asegs m ->
evt asegs (fun ms =>
ms = MS (R_L usp hb S sub gp tp (Z_to_bv 64 RA_sbl_memset1) t0 t1 t2
a0 a1 (Z_to_bv 64 (S + 80)) a3 a4 a5 a6 a7
xs3 (Z_to_bv 64 FS) (Z_to_bv 64 (sha (S + 120))) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 (S + 32)) (Z_to_bv 64 (hb + 32))
t3 t4 t5 t6) F (Z_to_bv 64 SBL_PC_B) fc None m (seg_rom asegs))
(MS (R_L usp hb S sub gp tp (Z_to_bv 64 RA_sbl_memset1) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
xs3 (Z_to_bv 64 FS) (Z_to_bv 64 (sha (S + 120))) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 (S + 32)) (Z_to_bv 64 (hb + 32)) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbl_memset1)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL LOS SPH MI.
unfold R_L, RA_sbl_memset1, SBL_PC_B in *. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xb70b0)) with (Z_to_bv 64 0xb70b0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold sb_slots, sha in SL. unfold sha.
ato 0xb70bc.
apply evt_done. reflexivity.
Qed.
Definition sbv_248 (v : sb_vslots) (w : word) : sb_vslots :=
SBV (v_8 v) (v_120 v) w (v_256 v) (v_264 v) (v_296 v) (v_384 v) (v_392 v) (v_400 v) (v_416 v) (v_424 v) (v_432 v) (v_440 v).
Definition RA_sbl_l2l : Z := 0xb7138.
Definition sbl_A_lsp_to_lpc : Z := 0xa95ec.

Lemma sbl_lspi8 : forall (OLD NEW IQ usp lo sub : Z) (os ns qs : list word)
(ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
aobj asegs m OLD 32 -> aobj asegs m NEW 32 -> aobj asegs m IQ 32 ->
OLD mod 4 = 0 -> NEW mod 4 = 0 -> IQ mod 4 = 0 -> 0 < OLD -> 0 < NEW ->
rw_cells asegs m OLD (f32 os) -> length os = 8%nat -> rw_cells asegs m NEW (f32 ns) -> length ns = 8%nat ->
rw_cells asegs m IQ (f32 qs) -> length qs = 8%nat ->
(IQ + 32 <= SH_LO \/ SH_HI <= IQ) -> IMG_TOP <= IQ ->
(IQ + 32 <= lo \/ usp <= IQ) -> (OLD + 32 <= lo \/ usp <= OLD) -> (NEW + 32 <= lo \/ usp <= NEW) ->
(IQ + 32 <= OLD \/ OLD + 32 <= IQ) -> (IQ + 32 <= NEW \/ NEW + 32 <= IQ) ->
client_consts m -> stk asegs m lo usp -> lo <= usp - 64 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (qs' : list word),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(IQ, IQ + 32); (usp + -64, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
/\ frm0 fc' /\ rw_cells asegs m' IQ (f32 qs') /\ length qs' = 8%nat)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OLD) (Z_to_bv 64 NEW) (Z_to_bv 64 IQ) (Z_to_bv 64 8) (Z_to_bv 64 sub) (Z_to_bv 64 4) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_lsp_interpolate) fc None m (seg_rom asegs)).
Proof.
intros until m. intros O1 O2 O3 A1 A2 A3 P1 P2 C1 L1 C2 L2 C3 L3 SH IMG D1 D2 D3 D4 D5 CC ST LO LOS SPH MI FRM.
eapply evt_mono.
- eapply (lsp_interpolate_stmt OLD NEW IQ usp lo sub 8%nat os ns qs); try eassumption; try (cbn; lia).
- intros ms' POST. exact POST.
Qed.

Lemma sbl_e3 : forall (usp lo hb S OUT A f sf MODE fsz FS sub OQ : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs) (voq lq liq : list word) (xs3 xra : word)
(gp tp t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_slots usp S OUT A f sf MODE fsz v) ->
rw_cells asegs m S (sbp_hdr s a) -> rw_cells asegs m (S + 40) (sbp_ptrs s a OUT) -> sbd_lpcSize s = 8 -> sbd_nbSubframes s = 4 -> OQ = a_oq a -> 0 <= sub < 4 ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
rw_cells asegs m OQ (f32 voq) -> length voq = 8%nat -> aobj asegs m OQ 32 -> OQ mod 4 = 0 -> 0 < OQ -> OQ + 32 <= lo ->
rw_cells asegs m (usp + -864) (f32 lq) -> length lq = 8%nat -> aobj asegs m (usp + -864) 32 ->
rw_cells asegs m (usp + -960) (f32 liq) -> length liq = 8%nat -> aobj asegs m (usp + -960) 32 ->
client_consts m -> stk asegs m lo hb -> lo <= hb - 64 -> hb <= usp + -1088 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (m1 : mem) (xt0 xt1 xt2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (F' : bvmap 5 word) (fc' : bv 32) (liq' : list word),
ms = MS (R_L usp hb S sub gp tp (Z_to_bv 64 RA_sbl_l2l) xt0 xt1 xt2
(Z_to_bv 64 (usp + -960)) (Z_to_bv 64 (usp + -1056)) (Z_to_bv 64 8) (Z_to_bv 64 0) xa4 xa5 xa6 xa7
xs3 (Z_to_bv 64 FS) (Z_to_bv 64 (usp + -960)) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 (S + 32)) (Z_to_bv 64 (hb + 32))
xt3 xt4 xt5 xt6) F' (Z_to_bv 64 sbl_A_lsp_to_lpc) fc' None m1 (seg_rom asegs)
/\ munch [(usp + -960, usp + -928); (hb + -64, hb); (usp + -608, usp + -160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo hb /\ frm0 fc'
/\ rw_cells asegs m1 (usp + -608) (sb_slots usp S OUT A f sf MODE fsz (sbv_248 v (Z_to_bv 64 (sha (S + 120)))))
/\ rw_cells asegs m1 (usp + -960) (f32 liq') /\ length liq' = 8%nat)
(MS (R_L usp hb S sub gp tp xra t0 t1 t2 a0 a1 (Z_to_bv 64 (S + 80)) a3 a4 a5 a6 a7
xs3 (Z_to_bv 64 FS) (Z_to_bv 64 (sha (S + 120))) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 (S + 32)) (Z_to_bv 64 (hb + 32)) t3 t4 t5 t6)
F (Z_to_bv 64 SBL_PC_B) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL HD PT ELPC ENSF EOQ SUB OBS S8 SPOS SOFF SLO OQC LOQ OBOQ OQ4 OQPOS OQLO QC LQ OBQ IQC LIQ OBIQ CC ST LO HB LOS SPH U32 MI FRM.
unfold R_L, RA_sbl_l2l, sbl_A_lsp_to_lpc, SBL_PC_B in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _). pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof (munch_refl [(usp + -960, usp + -928); (hb + -64, hb); (usp + -608, usp + -160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -960, usp + -928); (hb + -64, hb); (usp + -608, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_slots, sha in SL. unfold sbp_hdr in HD. unfold sbp_ptrs in PT. rewrite ELPC, ENSF in HD. rewrite <- EOQ in PT. unfold sha.
ato 0xb70f0.
rewrite sx32_small by (unfold int31; lia).
ato 0xb70fc. rewrite sx32_small by (unfold int31; lia).
ato 0xb7114.
astep.
call (sbl_lspi8 OQ (usp + -864) (usp + -960) hb lo sub voq lq liq).
all: try eassumption.
all: try (unfold IMG_TOP, SH_LO, SH_HI in *; clear - U32 OQ4 OQPOS OQLO LO HB LOS' SPH STa; first [lia | Z.div_mod_to_equations; lia]).
{ exact (aobj_munch asegs _ m m0 OQ 32 OBOQ MU (shfree_of_aobj asegs _ m OQ 32 OF OBOQ)). }
{ exact (aobj_munch asegs _ m m0 _ 32 OBQ MU (shfree_of_aobj asegs _ m _ 32 OF OBQ)). }
{ exact (aobj_munch asegs _ m m0 _ 32 OBIQ MU (shfree_of_aobj asegs _ m _ 32 OF OBIQ)). }
{ unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))). }
ato 0xb7128. rewrite sx32_small by (unfold int31; lia).
ato 0xa95ec.
apply evt_done. do 14 eexists. exists x17. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact PC|]. split; [exact PC0|]. split; [exact SL|]. split; [exact PC1| exact POST].
Qed.
Definition RA_sbl_memset2 : Z := 0xb7284.

Lemma sbl_shr3_al : forall a c, a mod 8 = 0 -> (a + c) ≫ 3 = a ≫ 3 + c / 8.
Proof. intros a c H. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. Qed.

Lemma sbl_e4 : forall (usp lo hb S OUT A f sf MODE fsz FS sub PG AK LPI : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs) (vpg lak lpi : list word) (xs3 : word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_slots usp S OUT A f sf MODE fsz v) ->
rw_cells asegs m S (sbp_hdr s a) -> rw_cells asegs m (S + 40) (sbp_ptrs s a OUT) -> sbd_lpcSize s = 8 -> sbd_subframeSize s = FS -> PG = a_pg a ->
(FS = 40 \/ FS = 80) -> 0 <= sub < 4 ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
rw_cells asegs m PG (f32 vpg) -> length vpg = 4%nat -> aobj asegs m PG 16 -> PG mod 4 = 0 -> 0 < PG -> PG + 16 <= lo -> (PG + 16 <= SH_LO \/ SH_HI <= PG) -> IMG_TOP <= PG ->
(S + 160 <= PG \/ PG + 16 <= S) ->
AK = usp + -1056 -> rw_cells asegs m AK (f32 lak) -> length lak = 8%nat -> aobj asegs m AK 32 ->
LPI = usp + -672 -> rw_cells asegs m LPI (f32 lpi) -> length lpi = 4%nat -> aobj asegs m LPI 16 ->
lo <= hb -> hb <= usp + -1088 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (m1 : mem) (xt0 xa3 xa4 xa5 xa6 xa7 : word) (F' : bvmap 5 word) (fc' : bv 32) (vpg' : list word),
ms = MS (R_L usp hb S sub gp tp (Z_to_bv 64 RA_sbl_memset2) xt0 t1 t2
(Z_to_bv 64 (hb + 32)) (Z_to_bv 64 0) (Z_to_bv 64 (4 * FS)) xa3 xa4 xa5 xa6 xa7
xs3 (Z_to_bv 64 FS) (Z_to_bv 64 (4 * sub)) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 0x10184) (Z_to_bv 64 (hb + 32))
t3 t4 t5 t6) F' (Z_to_bv 64 sbl_e_asan_memset) fc' None m1 (seg_rom asegs)
/\ munch [(PG, PG + 16)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ frm0 fc'
/\ rw_cells asegs m1 PG (f32 vpg') /\ length vpg' = 4%nat)
(MS (R_L usp hb S sub gp tp (Z_to_bv 64 RA_sbl_l2l) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
xs3 (Z_to_bv 64 FS) (Z_to_bv 64 (usp + -960)) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 (S + 32)) (Z_to_bv 64 (hb + 32)) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbl_l2l)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL HD PT ELPC EFS EPG HFS SUB OBS S8 SPOS SOFF SLO PGC LPG OBPG PG4 PGPOS PGLO PGOFF PGIMG SPG EAK AKC LAK OBAK ELPI LPC LLP OBLP LO HB LOS SPH U32 MI FRM.
unfold R_L, RA_sbl_l2l, RA_sbl_memset2, sbl_e_asan_memset in *. unfold SH_LO, SH_HI in SOFF, PGOFF. unfold IMG_TOP in PGIMG. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xb7138)) with (Z_to_bv 64 0xb7138) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(PG, PG + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(PG, PG + 16)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_slots, sha in SL. unfold sbp_hdr in HD. unfold sbp_ptrs in PT. rewrite ELPC, EFS in HD. rewrite <- EPG in PT. unfold sha.
do 4 (destruct vpg as [|? vpg]; [discriminate LPG|]). destruct vpg; [| discriminate LPG]. cbn [f32 map] in PGC.
do 8 (destruct lak as [|? lak]; [discriminate LAK|]). destruct lak; [| discriminate LAK]. cbn [f32 map] in AKC.
do 4 (destruct lpi as [|? lpi]; [discriminate LLP|]). destruct lpi; [| discriminate LLP]. cbn [f32 map] in LPC.
assert (AK8 : AK mod 8 = 0) by (subst AK; clear - U32; Z.div_mod_to_equations; lia).
assert (LPI8 : LPI mod 8 = 0) by (subst LPI; clear - U32; Z.div_mod_to_equations; lia).
replace (usp + -1052) with (AK + 4) in SL by lia. replace (usp + -1056) with AK in SL by lia. replace (usp + -672) with LPI in SL by lia.
assert (SC : sub = 0 \/ sub = 1 \/ sub = 2 \/ sub = 3) by lia.
destruct SC as [-> | [-> | [-> | ->]]].
- ato 0xb7168. astep. chk_merge OBPG 4.
ato 0xb7184. rewrite sx32_small by (unfold int31; lia).
ato 0xb7190. astep. chk_merge OBPG 4.
ato 0xb71d0. astep. chk_merge OBPG 4.
ato 0xb71ac.
replace ((AK + 4) ≫ 3 + SHB + 1) with ((AK + 12) ≫ 3 + SHB) by (rewrite !(sbl_shr3_al AK) by exact AK8; change (4 / 8) with 0; change (12 / 8) with 1; lia).
ato 0xb71d0. astep. chk_merge OBPG 4.
ato 0xb71ac.
replace ((AK + 12) ≫ 3 + SHB + 1) with ((AK + 20) ≫ 3 + SHB) by (rewrite !(sbl_shr3_al AK) by exact AK8; change (12 / 8) with 1; change (20 / 8) with 2; lia).
ato 0xb71d0. astep. chk_merge OBPG 4.
ato 0xb71ac.
replace ((AK + 20) ≫ 3 + SHB + 1) with ((AK + 28) ≫ 3 + SHB) by (rewrite !(sbl_shr3_al AK) by exact AK8; change (20 / 8) with 2; change (28 / 8) with 3; lia).
ato 0xb71d0. astep. chk_merge OBPG 4.
ato 0xb7260.
ato 0xb7274. rewrite sx32_small by (unfold int31; lia).
ato 0x667b0.
rewrite Z.shiftl_mul_pow2 by lia. replace (FS * 2 ^ 2) with (4 * FS) by lia.
apply evt_done. lazymatch type of PGC with rw_cells _ _ _ [C4 ?w0; C4 ?w1; C4 ?w2; C4 ?w3] => do 9 eexists; exists [w0; w1; w2; w3] end.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact PGC| reflexivity].
- ato 0xb7168. astep. chk_merge OBPG 4.
ato 0xb7184. rewrite sx32_small by (unfold int31; lia).
ato 0xb7190. astep. chk_merge OBPG 4.
ato 0xb71d0. astep. chk_merge OBPG 4.
ato 0xb71ac.
replace ((AK + 4) ≫ 3 + SHB + 1) with ((AK + 12) ≫ 3 + SHB) by (rewrite !(sbl_shr3_al AK) by exact AK8; change (4 / 8) with 0; change (12 / 8) with 1; lia).
ato 0xb71d0. astep. chk_merge OBPG 4.
ato 0xb71ac.
replace ((AK + 12) ≫ 3 + SHB + 1) with ((AK + 20) ≫ 3 + SHB) by (rewrite !(sbl_shr3_al AK) by exact AK8; change (12 / 8) with 1; change (20 / 8) with 2; lia).
ato 0xb71d0. astep. chk_merge OBPG 4.
ato 0xb71ac.
replace ((AK + 20) ≫ 3 + SHB + 1) with ((AK + 28) ≫ 3 + SHB) by (rewrite !(sbl_shr3_al AK) by exact AK8; change (20 / 8) with 2; change (28 / 8) with 3; lia).
ato 0xb71d0. astep. chk_merge OBPG 4.
ato 0xb7260.
ato 0xb7274. rewrite sx32_small by (unfold int31; lia).
ato 0x667b0.
rewrite Z.shiftl_mul_pow2 by lia. replace (FS * 2 ^ 2) with (4 * FS) by lia.
apply evt_done. lazymatch type of PGC with rw_cells _ _ _ [C4 ?w0; C4 ?w1; C4 ?w2; C4 ?w3] => do 9 eexists; exists [w0; w1; w2; w3] end.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact PGC| reflexivity].
- ato 0xb7168. astep. chk_merge OBPG 4.
ato 0xb7184. rewrite sx32_small by (unfold int31; lia).
ato 0xb7190. astep. chk_merge OBPG 4.
ato 0xb71d0. astep. chk_merge OBPG 4.
ato 0xb71ac.
replace ((AK + 4) ≫ 3 + SHB + 1) with ((AK + 12) ≫ 3 + SHB) by (rewrite !(sbl_shr3_al AK) by exact AK8; change (4 / 8) with 0; change (12 / 8) with 1; lia).
ato 0xb71d0. astep. chk_merge OBPG 4.
ato 0xb71ac.
replace ((AK + 12) ≫ 3 + SHB + 1) with ((AK + 20) ≫ 3 + SHB) by (rewrite !(sbl_shr3_al AK) by exact AK8; change (12 / 8) with 1; change (20 / 8) with 2; lia).
ato 0xb71d0. astep. chk_merge OBPG 4.
ato 0xb71ac.
replace ((AK + 20) ≫ 3 + SHB + 1) with ((AK + 28) ≫ 3 + SHB) by (rewrite !(sbl_shr3_al AK) by exact AK8; change (20 / 8) with 2; change (28 / 8) with 3; lia).
ato 0xb71d0. astep. chk_merge OBPG 4.
ato 0xb7260.
ato 0xb7274. rewrite sx32_small by (unfold int31; lia).
ato 0x667b0.
rewrite Z.shiftl_mul_pow2 by lia. replace (FS * 2 ^ 2) with (4 * FS) by lia.
apply evt_done. lazymatch type of PGC with rw_cells _ _ _ [C4 ?w0; C4 ?w1; C4 ?w2; C4 ?w3] => do 9 eexists; exists [w0; w1; w2; w3] end.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact PGC| reflexivity].
- ato 0xb7168. astep. chk_merge OBPG 4.
ato 0xb7184. rewrite sx32_small by (unfold int31; lia).
ato 0xb7190. astep. chk_merge OBPG 4.
ato 0xb71d0. astep. chk_merge OBPG 4.
ato 0xb71ac.
replace ((AK + 4) ≫ 3 + SHB + 1) with ((AK + 12) ≫ 3 + SHB) by (rewrite !(sbl_shr3_al AK) by exact AK8; change (4 / 8) with 0; change (12 / 8) with 1; lia).
ato 0xb71d0. astep. chk_merge OBPG 4.
ato 0xb71ac.
replace ((AK + 12) ≫ 3 + SHB + 1) with ((AK + 20) ≫ 3 + SHB) by (rewrite !(sbl_shr3_al AK) by exact AK8; change (12 / 8) with 1; change (20 / 8) with 2; lia).
ato 0xb71d0. astep. chk_merge OBPG 4.
ato 0xb71ac.
replace ((AK + 20) ≫ 3 + SHB + 1) with ((AK + 28) ≫ 3 + SHB) by (rewrite !(sbl_shr3_al AK) by exact AK8; change (20 / 8) with 2; change (28 / 8) with 3; lia).
ato 0xb71d0. astep. chk_merge OBPG 4.
ato 0xb7260.
ato 0xb7274. rewrite sx32_small by (unfold int31; lia).
ato 0x667b0.
rewrite Z.shiftl_mul_pow2 by lia. replace (FS * 2 ^ 2) with (4 * FS) by lia.
apply evt_done. lazymatch type of PGC with rw_cells _ _ _ [C4 ?w0; C4 ?w1; C4 ?w2; C4 ?w3] => do 9 eexists; exists [w0; w1; w2; w3] end.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact PGC| reflexivity].
Qed.

Definition JY (pc : Z) (m : mem) (R : bvmap 5 word) : machine_state -> Prop :=
fun ms => exists (F' : bvmap 5 word) (fc' : bv 32), ms = MS R F' (Z_to_bv 64 pc) fc' None m (seg_rom asegs) /\ frm0 fc'.
Ltac jy_done := apply evt_done; do 2 eexists; split; [reflexivity| assumption].
Tactic Notation "joiny" constr(pcJ) integer(n1) integer(n2) :=
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
eapply (evt_cut segs (JY pcJ mc _));
[ let B := fresh "B" in if_cases B;
[ do n1 astep; jy_done | do n2 astep; jy_done ]
| try match goal with H : frm0 _ |- _ => clear H end;
let FRM := fresh "FRM" in intros ? (? & ? & -> & FRM) ]
end.
Definition RA_sbl_innov1 : Z := 0xb7438.
Definition sbl_PAR (id : Z) : Z := if id =? 2 then A_split_cb_high_lbr else A_split_cb_high.

Lemma sbl_rw_f32_nth : forall (m : mem) A ws i, rw_cells asegs m A (f32 ws) -> 0 <= i < Z.of_nat (length ws) -> exists w : word, rw_cells asegs m (A + 4 * i) [C4 w].
Proof.
intros m A ws i H Hi. pose proof (rw_cells_f32_mid asegs m A ws (Z.to_nat i) 1 H ltac:(lia)) as W.
replace (Z.of_nat (Z.to_nat i)) with i in W by lia.
destruct (skipn (Z.to_nat i) ws) as [|w r] eqn:E.
- exfalso. assert (L : length (skipn (Z.to_nat i) ws) = 0%nat) by (rewrite E; reflexivity). rewrite length_skipn in L. lia.
- exists w. exact W.
Qed.
Lemma sbl_ro_f32_nth : forall (m : mem) A ws i, ro_cells asegs m A (f32 ws) -> 0 <= i < Z.of_nat (length ws) -> exists w : word, ro_cells asegs m (A + 4 * i) [C4 w].
Proof.
intros m A ws i H Hi. pose proof (ro_f32_mid asegs m A ws (Z.to_nat i) 1 H ltac:(lia)) as W.
replace (Z.of_nat (Z.to_nat i)) with i in W by lia.
destruct (skipn (Z.to_nat i) ws) as [|w r] eqn:E.
- exfalso. assert (L : length (skipn (Z.to_nat i) ws) = 0%nat) by (rewrite E; reflexivity). rewrite length_skipn in L. lia.
- exists w. exact W.
Qed.

Lemma sbl_e5c : forall (usp lo hb S OUT A D f sf MODE fsz sub id LER : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs) (pad1 : list byte) (sm : submode)
(b : bits_st bptr) (ler tab : list word) (xs3 : word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_slots usp S OUT A f sf MODE fsz v) ->
rw_cells asegs m S (sbp_hdr s a) -> sbd_subframeSize s = 40 ->
rw_cells asegs m (S + 136) (sbp_cfg s pad1) -> rw_cells asegs m (S + 152) [C4 (Z_to_bv 64 id)] ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
sbd_mode s = ModeWB -> MODE = sbmode_struct (sbd_mode s) -> aobj asegs m MODE 216 -> (id = 2 \/ id = 3 \/ id = 4) -> aobj asegs m (sb_sub_addr id) 88 -> lib_consts m ->
0 <= sub < 4 ->
bits_rep asegs m A D b -> bits_ok b -> aobj asegs m A BITS_SIZEOF -> aobj asegs m D (sb_buf_size b) ->
(A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A) -> A + BITS_SIZEOF <= lo -> D + sb_buf_size b <= lo -> IMG_TOP <= A -> (S + 160 <= A \/ A + BITS_SIZEOF <= S) ->
LER = usp + -768 -> rw_cells asegs m LER (f32 ler) -> length ler = 4%nat -> aobj asegs m LER 16 ->
ro_cells asegs m A_gc_quant_bound (f32 tab) -> length tab = 16%nat -> aobj asegs m A_gc_quant_bound 64 ->
client_consts m -> stk asegs m lo hb -> lo <= hb - 32 -> hb <= usp + -1088 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (m1 : mem) (xt0 xt1 xt2 xa7 xt3 xt4 xt5 xt6 : word) (F' : bvmap 5 word) (fc' : bv 32),
ms = MS (R_L usp hb S sub gp tp (Z_to_bv 64 RA_sbl_innov1) xt0 xt1 xt2
(Z_to_bv 64 (hb + 32)) (Z_to_bv 64 (sbl_PAR id)) (Z_to_bv 64 40) (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 (S + 132)) (Z_to_bv 64 A_split_cb_shape_sign_unquant) xa7
xs3 (Z_to_bv 64 A) (Z_to_bv 64 (4 * sub)) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 (S + 32)) (Z_to_bv 64 (hb + 32))
xt3 xt4 xt5 xt6) F' (Z_to_bv 64 A_split_cb_shape_sign_unquant) fc' None m1 (seg_rom asegs)
/\ munch [(A, A + BITS_SIZEOF); (hb + -32, hb)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo hb /\ frm0 fc'
/\ bits_rep asegs m1 A D (ub b 4))
(MS (R_L usp hb S sub gp tp (Z_to_bv 64 RA_sbl_memset2) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
xs3 (Z_to_bv 64 40) (Z_to_bv 64 (4 * sub)) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 0x10184) (Z_to_bv 64 (hb + 32)) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbl_memset2)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL HD EFS CFG IDC OBS S8 SPOS SOFF SLO EMO EMODE OBM HID OBSM LC SUB REP OK OBA OBD ASH ALO DLO ATOP SEPSA ELER LERC LLER OBLER TAB LTAB OBT CC ST LO HB LOS SPH U32 MI FRM.
unfold R_L, RA_sbl_memset2, RA_sbl_innov1, A_split_cb_shape_sign_unquant in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xb7284)) with (Z_to_bv 64 0xb7284) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold IMG_TOP in ATOP. unfold A_gc_quant_bound in *. pose proof SEPSA as SEPSA'. unfold BITS_SIZEOF in SEPSA'.
pose proof ST as (STa & STb & _). pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof (munch_refl [(A, A + BITS_SIZEOF); (hb + -32, hb)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(A, A + BITS_SIZEOF); (hb + -32, hb)]) by (pose proof ASH as Y; clear - Y LOS LO; cbn; unfold SH_LO, SH_HI, BITS_SIZEOF in *; lia).
unfold sb_slots, sha in SL. unfold sbp_hdr in HD. rewrite EFS in HD. unfold sbp_cfg in CFG. unfold sha.
rewrite EMO in *. cbn [sbmode_struct] in EMODE.
assert (ESUB : sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR ModeWB = MODE + 40) by (subst MODE; reflexivity).
rewrite ESUB in CFG.
assert (M8 : MODE mod 8 = 0) by (subst MODE; reflexivity).
assert (LER8 : LER mod 8 = 0) by (subst LER; clear - U32; Z.div_mod_to_equations; lia).
replace (usp + -768) with LER in SL by lia.
pose proof (lib_const m A_sb_wb_mode LC_sb_wb_mode LC ltac:(lc_in)) as MTAB. rewrite <- EMODE in MTAB. unfold LC_sb_wb_mode in MTAB. unfold A_sb_wb_mode in EMODE.
pose proof (lib_const m A_wb_submode2 LC_wb_submode2 LC ltac:(lc_in)) as T2.
pose proof (lib_const m A_wb_submode3 LC_wb_submode3 LC ltac:(lc_in)) as T3. pose proof (lib_const m A_wb_submode4 LC_wb_submode4 LC ltac:(lc_in)) as T4.
unfold LC_wb_submode2 in T2. unfold LC_wb_submode3 in T3. unfold LC_wb_submode4 in T4.
destruct HID as [-> | [-> | ->]]; cbn [sb_sub_addr Z.eqb Pos.eqb] in OBSM; cbn [sbl_PAR Z.eqb Pos.eqb]; unfold A_split_cb_high_lbr, A_split_cb_high.
- set (SM := A_wb_submode2) in *. assert (ESM : SM = 0xf0440) by reflexivity. assert (SM8 : SM mod 8 = 0) by reflexivity. clear T3 T4. clearbody SM.
ato 0xb72b0. rewrite sx32_small by (unfold int31; lia). ato 0xb72d0. rewrite <- ESM.
ato 0xb7300.
ato 0xb7310. astep.
call (speex_bits_unpack_unsigned_walk A D hb lo b 4 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP OK ltac:(lia) OBA OBD ASH ltac:(lia) LOS ltac:(lia) ALO DLO).
1: exact ST. 1: exact CC. 1: exact MI.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
change (snd (speex_bits_unpack_unsigned b 4)) with (ub b 4) in *. change (fst (speex_bits_unpack_unsigned b 4)) with (uv b 4) in *.
pose proof (ub_ok b 4 OK ltac:(lia)) as (OK1 & SZ1 & V1R). change (2 ^ 4) with 16 in V1R.
destruct (sbl_rw_f32_nth _ LER ler sub LERC ltac:(lia)) as (wel & WEL).
destruct (sbl_ro_f32_nth _ 160224 tab (uv b 4) TAB ltac:(lia)) as (wgc & WGC).
ato 0xb732c.
astep. chk_merge OBLER 4.
ato 0xb7340. rewrite Z.shiftl_mul_pow2 by lia. replace (160224 + uv b 4 * 2 ^ 2) with (160224 + 4 * uv b 4) by lia.
ato 0xb7350. astep. chk_merge OBT 4.
ato 0xb7370.
clear WEL WGC.
astep. rewrite sx32_small by (unfold int31; lia).
ato 0xb73a0. astep.
joiny 0xb73ac 1 2.
ato 0xb73cc. rewrite sx32_small by (unfold int31; lia). ato 0xb73ec. rewrite <- ESM.
ato 0xac694.
apply evt_done. do 11 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact PC|]. split; [assumption| exact POST].
- set (SM := A_wb_submode3) in *. assert (ESM : SM = 0xf04c0) by reflexivity. assert (SM8 : SM mod 8 = 0) by reflexivity. clear T2 T4. clearbody SM.
ato 0xb72b0. rewrite sx32_small by (unfold int31; lia). ato 0xb72d0. rewrite <- ESM.
ato 0xb7300.
ato 0xb7310. astep.
call (speex_bits_unpack_unsigned_walk A D hb lo b 4 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP OK ltac:(lia) OBA OBD ASH ltac:(lia) LOS ltac:(lia) ALO DLO).
1: exact ST. 1: exact CC. 1: exact MI.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
change (snd (speex_bits_unpack_unsigned b 4)) with (ub b 4) in *. change (fst (speex_bits_unpack_unsigned b 4)) with (uv b 4) in *.
pose proof (ub_ok b 4 OK ltac:(lia)) as (OK1 & SZ1 & V1R). change (2 ^ 4) with 16 in V1R.
destruct (sbl_rw_f32_nth _ LER ler sub LERC ltac:(lia)) as (wel & WEL).
destruct (sbl_ro_f32_nth _ 160224 tab (uv b 4) TAB ltac:(lia)) as (wgc & WGC).
ato 0xb732c.
astep. chk_merge OBLER 4.
ato 0xb7340. rewrite Z.shiftl_mul_pow2 by lia. replace (160224 + uv b 4 * 2 ^ 2) with (160224 + 4 * uv b 4) by lia.
ato 0xb7350. astep. chk_merge OBT 4.
ato 0xb7370.
clear WEL WGC.
astep. rewrite sx32_small by (unfold int31; lia).
ato 0xb73a0. astep.
joiny 0xb73ac 1 2.
ato 0xb73cc. rewrite sx32_small by (unfold int31; lia). ato 0xb73ec. rewrite <- ESM.
ato 0xac694.
apply evt_done. do 11 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact PC|]. split; [assumption| exact POST].
- set (SM := A_wb_submode4) in *. assert (ESM : SM = 0xf0540) by reflexivity. assert (SM8 : SM mod 8 = 0) by reflexivity. clear T2 T3. clearbody SM.
ato 0xb72b0. rewrite sx32_small by (unfold int31; lia). ato 0xb72d0. rewrite <- ESM.
ato 0xb7300.
ato 0xb7310. astep.
call (speex_bits_unpack_unsigned_walk A D hb lo b 4 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP OK ltac:(lia) OBA OBD ASH ltac:(lia) LOS ltac:(lia) ALO DLO).
1: exact ST. 1: exact CC. 1: exact MI.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
change (snd (speex_bits_unpack_unsigned b 4)) with (ub b 4) in *. change (fst (speex_bits_unpack_unsigned b 4)) with (uv b 4) in *.
pose proof (ub_ok b 4 OK ltac:(lia)) as (OK1 & SZ1 & V1R). change (2 ^ 4) with 16 in V1R.
destruct (sbl_rw_f32_nth _ LER ler sub LERC ltac:(lia)) as (wel & WEL).
destruct (sbl_ro_f32_nth _ 160224 tab (uv b 4) TAB ltac:(lia)) as (wgc & WGC).
ato 0xb732c.
astep. chk_merge OBLER 4.
ato 0xb7340. rewrite Z.shiftl_mul_pow2 by lia. replace (160224 + uv b 4 * 2 ^ 2) with (160224 + 4 * uv b 4) by lia.
ato 0xb7350. astep. chk_merge OBT 4.
ato 0xb7370.
clear WEL WGC.
astep. rewrite sx32_small by (unfold int31; lia).
ato 0xb73a0. astep.
joiny 0xb73ac 1 2.
ato 0xb73cc. rewrite sx32_small by (unfold int31; lia). ato 0xb73ec. rewrite <- ESM.
ato 0xac694.
apply evt_done. do 11 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact PC|]. split; [assumption| exact POST].
Qed.

Lemma sbl_signal_mul40 : forall (xs : list word) (p usp lo : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (m : mem)
(t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) fc,
length xs = 40%nat -> aobj asegs m p 160 -> p mod 4 = 0 -> lo <= usp - 16 -> SH_HI <= lo -> usp < 2^63 ->
(p + 160 <= SH_LO \/ SH_HI <= p) -> (p + 160 <= lo \/ usp <= p) ->
rw_cells asegs m p (f32 xs) -> frm0 fc -> stk asegs m lo usp -> IMG_TOP <= p -> client_consts m -> mem_inv asegs m ->
evt asegs (fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (xs' : list word),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(p, p + 160); (usp + -16, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
/\ frm0 fc' /\ rw_cells asegs m' p (f32 xs') /\ length xs' = 40%nat)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 p) (Z_to_bv 64 40) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_signal_mul) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros L OB P4 LO LOS SPH XSH XAP X FRM ST PTOP CC MI.
eapply evt_mono.
- eapply (signal_mul_walk xs p usp lo ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m); rewrite ?L; try eassumption; try (cbn; lia); try reflexivity.
- intros ms' (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & f15 & fc' & m' & E & MU & WM & MI' & ST' & FRM' & X').
rewrite L in MU. do 18 eexists. exists (map (smul (reg_get F (Z_to_bv 5 10))) xs). split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
split; [exact FRM'|]. split; [exact X'|]. rewrite length_map. exact L.
Qed.
Definition SBL_PC_J : Z := 0xb7808.

Lemma sbl_e7a : forall (usp lo hb S OUT A f sf MODE fsz sub id EX : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs) (pad1 : list byte)
(ex : list word) (xs3 : word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_slots usp S OUT A f sf MODE fsz v) ->
rw_cells asegs m S (sbp_hdr s a) -> sbd_subframeSize s = 40 ->
rw_cells asegs m (S + 136) (sbp_cfg s pad1) -> rw_cells asegs m (S + 152) [C4 (Z_to_bv 64 id)] ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
sbd_mode s = ModeWB -> MODE = sbmode_struct (sbd_mode s) -> aobj asegs m MODE 216 -> (id = 2 \/ id = 3) -> aobj asegs m (sb_sub_addr id) 88 -> lib_consts m ->
EX = hb + 32 -> rw_cells asegs m EX (f32 ex) -> length ex = 40%nat -> aobj asegs m EX 160 ->
client_consts m -> stk asegs m lo hb -> lo <= hb - 16 -> hb <= usp + -1088 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 -> hb mod 32 = 0 ->
mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (m1 : mem) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (F' : bvmap 5 word) (fc' : bv 32) (ex' : list word),
ms = MS (R_L usp hb S sub gp tp xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
xs3 (Z_to_bv 64 A) (Z_to_bv 64 (4 * sub)) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 (S + 32)) (Z_to_bv 64 EX)
xt3 xt4 xt5 xt6) F' (Z_to_bv 64 SBL_PC_J) fc' None m1 (seg_rom asegs)
/\ munch [(EX, EX + 160); (hb + -16, hb)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo hb /\ frm0 fc'
/\ rw_cells asegs m1 EX (f32 ex') /\ length ex' = 40%nat)
(MS (R_L usp hb S sub gp tp (Z_to_bv 64 RA_sbl_innov1) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
xs3 (Z_to_bv 64 A) (Z_to_bv 64 (4 * sub)) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 (S + 32)) (Z_to_bv 64 EX) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbl_innov1)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL HD EFS CFG IDC OBS S8 SPOS SOFF SLO EMO EMODE OBM HID OBSM LC EEX EXC LEX OBEX CC ST LO HB LOS SPH U32 HB32 MI FRM.
unfold R_L, RA_sbl_innov1, SBL_PC_J in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xb7438)) with (Z_to_bv 64 0xb7438) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof ST as (STa & STb & _). pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof (munch_refl [(EX, EX + 160); (hb + -16, hb)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(EX, EX + 160); (hb + -16, hb)]) by (clear - EEX LOS LO HB SPH; cbn; unfold SH_LO, SH_HI in *; lia).
unfold sb_slots, sha in SL. unfold sbp_hdr in HD. rewrite EFS in HD. unfold sbp_cfg in CFG. unfold sha.
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
- set (SM := A_wb_submode2) in *. assert (ESM : SM = 0xf0440) by reflexivity. assert (SM8 : SM mod 8 = 0) by reflexivity. clear T3. clearbody SM.
ato 0xb7444. rewrite sx32_small by (unfold int31; lia).
ato 0xb7458. astep.
call (sbl_signal_mul40 ex EX hb lo).
all: try eassumption.
all: try (unfold IMG_TOP, SH_LO, SH_HI in *; clear - EEX EX8 LO HB LOS' SPH STa; first [lia | Z.div_mod_to_equations; lia]).
ato 0xb7488. rewrite sx32_small by (unfold int31; lia). ato 0xb74a8. rewrite <- ESM.
ato 0xb74c0.
rewrite sx32_small by (unfold int31; lia).
ato 0xb7808.
apply evt_done. do 20 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact PC|]. split; [exact PC0|]. split; [exact PC1| exact POST].
- set (SM := A_wb_submode3) in *. assert (ESM : SM = 0xf04c0) by reflexivity. assert (SM8 : SM mod 8 = 0) by reflexivity. clear T2. clearbody SM.
ato 0xb7444. rewrite sx32_small by (unfold int31; lia).
ato 0xb7458. astep.
call (sbl_signal_mul40 ex EX hb lo).
all: try eassumption.
all: try (unfold IMG_TOP, SH_LO, SH_HI in *; clear - EEX EX8 LO HB LOS' SPH STa; first [lia | Z.div_mod_to_equations; lia]).
ato 0xb7488. rewrite sx32_small by (unfold int31; lia). ato 0xb74a8. rewrite <- ESM.
ato 0xb74c0.
rewrite sx32_small by (unfold int31; lia).
ato 0xb7808.
apply evt_done. do 20 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact PC|]. split; [exact PC0|]. split; [exact PC1| exact POST].
Qed.
Definition sbv_120 (v : sb_vslots) (w : word) : sb_vslots :=
SBV (v_8 v) w (v_248 v) (v_256 v) (v_264 v) (v_296 v) (v_384 v) (v_392 v) (v_400 v) (v_416 v) (v_424 v) (v_432 v) (v_440 v).
Definition RA_sbl_pois2 : Z := 0xb752c.

Lemma sbl_e7b : forall (usp lo hb S OUT A f sf MODE fsz sub EX : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs) (pad1 : list byte)
(ex : list word) (xs3 : word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_slots usp S OUT A f sf MODE fsz v) ->
rw_cells asegs m S (sbp_hdr s a) -> sbd_subframeSize s = 40 ->
rw_cells asegs m (S + 136) (sbp_cfg s pad1) -> rw_cells asegs m (S + 152) [C4 (Z_to_bv 64 4)] ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
sbd_mode s = ModeWB -> MODE = sbmode_struct (sbd_mode s) -> aobj asegs m MODE 216 -> aobj asegs m (sb_sub_addr 4) 88 -> lib_consts m ->
EX = hb + 32 -> rw_cells asegs m EX (f32 ex) -> length ex = 40%nat -> aobj asegs m EX 160 ->
client_consts m -> stk asegs m lo hb -> lo <= hb - 224 - 4192 -> hb <= usp + -1088 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 -> hb mod 32 = 0 ->
mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (m1 : mem) (xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (F' : bvmap 5 word) (fc' : bv 32) (ex' : list word) (jh : list byte),
ms = MS (R_L usp (hb + -224) S sub gp tp (Z_to_bv 64 RA_sbl_pois2) xt0 xt1 xt2 (Z_to_bv 64 (hb + -192)) (Z_to_bv 64 160) xa2 xa3 xa4 xa5 xa6 xa7
xs3 (Z_to_bv 64 (hb + -192)) (Z_to_bv 64 (4 * sub)) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 (hb + -224)) (Z_to_bv 64 EX)
xt3 xt4 xt5 xt6) F' (Z_to_bv 64 sbl_e_alloca_poison) fc' None m1 (seg_rom asegs)
/\ munch [(EX, EX + 160); (hb + -16, hb); (hb + -4096, hb + -4088); (usp + -608, usp + -160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ stk asegs m1 lo (hb + -224) /\ frm0 fc'
/\ rw_cells asegs m1 (usp + -608) (sb_slots usp S OUT A f sf MODE fsz (sbv_120 v (Z_to_bv 64 hb)))
/\ rw_cells asegs m1 EX (f32 ex') /\ length ex' = 40%nat
/\ rw_cells asegs m1 (hb + -224) [CB 224 jh])
(MS (R_L usp hb S sub gp tp (Z_to_bv 64 RA_sbl_innov1) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
xs3 (Z_to_bv 64 A) (Z_to_bv 64 (4 * sub)) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 (S + 32)) (Z_to_bv 64 EX) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbl_innov1)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL HD EFS CFG IDC OBS S8 SPOS SOFF SLO EMO EMODE OBM OBSM LC EEX EXC LEX OBEX CC ST LO HB LOS SPH U32 HB32 MI FRM.
unfold R_L, RA_sbl_innov1, RA_sbl_pois2, sbl_e_alloca_poison in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xb7438)) with (Z_to_bv 64 0xb7438) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof ST as (STa & STb & _). pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof (munch_refl [(EX, EX + 160); (hb + -16, hb); (hb + -4096, hb + -4088); (usp + -608, usp + -160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(EX, EX + 160); (hb + -16, hb); (hb + -4096, hb + -4088); (usp + -608, usp + -160)]) by (clear - EEX LOS LO HB SPH; cbn; unfold SH_LO, SH_HI in *; lia).
unfold sb_slots, sha in SL. unfold sbp_hdr in HD. rewrite EFS in HD. unfold sbp_cfg in CFG. unfold sha.
rewrite EMO in *. cbn [sbmode_struct] in EMODE.
assert (ESUB : sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR ModeWB = MODE + 40) by (subst MODE; reflexivity).
rewrite ESUB in CFG.
assert (M8 : MODE mod 8 = 0) by (subst MODE; reflexivity).
assert (EX8 : EX mod 8 = 0) by (subst EX; clear - HB32; Z.div_mod_to_equations; lia).
pose proof (lib_const m A_sb_wb_mode LC_sb_wb_mode LC ltac:(lc_in)) as MTAB. rewrite <- EMODE in MTAB. unfold LC_sb_wb_mode in MTAB. unfold A_sb_wb_mode in EMODE.
pose proof (lib_const m A_wb_submode4 LC_wb_submode4 LC ltac:(lc_in)) as T4. unfold LC_wb_submode4 in T4.
cbn [sb_sub_addr Z.eqb Pos.eqb] in OBSM.
set (SM := A_wb_submode4) in *. assert (ESM : SM = 0xf0540) by reflexivity. assert (SM8 : SM mod 8 = 0) by reflexivity. clearbody SM.
ato 0xb7444. rewrite sx32_small by (unfold int31; lia).
ato 0xb7458. astep.
call (sbl_signal_mul40 ex EX hb lo).
all: try eassumption.
all: try (unfold IMG_TOP, SH_LO, SH_HI in *; clear - EEX EX8 LO HB LOS' SPH STa; first [lia | Z.div_mod_to_equations; lia]).
ato 0xb7488. rewrite sx32_small by (unfold int31; lia). ato 0xb74a8. rewrite <- ESM.
ato 0xb74c0. rewrite sx32_small by (unfold int31; lia).
ato 0xb74cc.
carve_frame 224%nat PC. rename FR into HULL.
carve_frame 3864%nat PC. rename FR into JK1.
carve_frame 8%nat PC. rename FR into P1.
apply (rw_cells_split_CB asegs _ _ [] 8 _ [] [8]%nat) in P1; [| reflexivity]. cbn [mk_CB_cells app] in P1.
ato 0xb74d4. rewrite zx32_small by lia.
ato 0xb750c. alits.
replace (hb - 224) with (hb + -224) by lia. rewrite ?Z.mod_small by lia.
rewrite (land_m32_al (hb + -224)) by (clear - STa SPH LO HB HB32; first [lia | Z.div_mod_to_equations; lia]).
astep. astep. replace (hb - 4096) with (hb + -4096) by lia.
astep. astep. sh_if.
ato 0x51d38.
release_frame P1 PC (hb + -4088). release_frame JK1 PC (hb + -224).
replace (hb + -224 + 32) with (hb + -192) in * by lia.
apply evt_done. do 16 eexists. lazymatch goal with H : rw_cells _ _ EX (f32 ?l) |- _ => exists l end. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact PC|]. split; [assumption|]. split; [exact SL|]. split; [exact PC1|]. split; [exact POST| exact HULL].
Qed.
Definition RA_sbl_memset3 : Z := 0xb754c.
Definition RA_sbl_innov2 : Z := 0xb75dc.

Lemma sbl_e8 : forall (usp lo hb2 S OUT A f sf MODE fsz sub I2 EX : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs) (xs3 : word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_slots usp S OUT A f sf MODE fsz v) ->
rw_cells asegs m S (sbp_hdr s a) -> sbd_subframeSize s = 40 ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
lo <= hb2 -> hb2 <= usp + -1088 -> SH_HI <= lo -> usp < 2^63 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (R_L usp hb2 S sub gp tp (Z_to_bv 64 RA_sbl_memset3) t0 t1 t2 (Z_to_bv 64 I2) (Z_to_bv 64 0) (Z_to_bv 64 160) a3 a4 a5 a6 a7
xs3 (Z_to_bv 64 I2) (Z_to_bv 64 (4 * sub)) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 40) (Z_to_bv 64 EX)
t3 t4 t5 t6) F (Z_to_bv 64 sbl_e_asan_memset) fc None m1 (seg_rom asegs)
/\ munch [(usp + -608, usp + -160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 (usp + -608) (sb_slots usp S OUT A f sf MODE fsz (sbv_416 v (Z_to_bv 64 hb2))))
(MS (R_L usp hb2 S sub gp tp (Z_to_bv 64 RA_sbl_pois2) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
xs3 (Z_to_bv 64 I2) (Z_to_bv 64 (4 * sub)) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 hb2) (Z_to_bv 64 EX) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbl_pois2)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL HD EFS OBS S8 SPOS SOFF SLO LO HB LOS SPH MI.
unfold R_L, RA_sbl_pois2, RA_sbl_memset3, sbl_e_asan_memset in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xb752c)) with (Z_to_bv 64 0xb752c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(usp + -608, usp + -160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -608, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_slots, sha in SL. unfold sbp_hdr in HD. rewrite EFS in HD. unfold sha.
ato 0xb753c. rewrite sx32_small by (unfold int31; lia).
ato 0x667b0. alits.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact SL].
Qed.

Lemma sbl_e9 : forall (usp lo hb2 S OUT A f sf MODE fsz sub I2 EX : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs) (pad1 : list byte) (xs3 : word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_slots usp S OUT A f sf MODE fsz v) ->
rw_cells asegs m (S + 136) (sbp_cfg s pad1) -> rw_cells asegs m (S + 152) [C4 (Z_to_bv 64 4)] ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
sbd_mode s = ModeWB -> MODE = sbmode_struct (sbd_mode s) -> aobj asegs m MODE 216 -> aobj asegs m (sb_sub_addr 4) 88 -> lib_consts m ->
lo <= hb2 -> hb2 <= usp + -1088 -> SH_HI <= lo -> usp < 2^63 ->
mem_inv asegs m ->
evt asegs (fun ms => exists (xa7 : word),
ms = MS (R_L usp hb2 S sub gp tp (Z_to_bv 64 RA_sbl_innov2) t0 t1 t2
(Z_to_bv 64 I2) (Z_to_bv 64 A_split_cb_high) (Z_to_bv 64 40) (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 (S + 132)) (Z_to_bv 64 A_split_cb_shape_sign_unquant) xa7
xs3 (Z_to_bv 64 I2) (Z_to_bv 64 (4 * sub)) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 40) (Z_to_bv 64 EX)
t3 t4 t5 t6) F (Z_to_bv 64 A_split_cb_shape_sign_unquant) fc None m (seg_rom asegs))
(MS (R_L usp hb2 S sub gp tp (Z_to_bv 64 RA_sbl_memset3) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
xs3 (Z_to_bv 64 I2) (Z_to_bv 64 (4 * sub)) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 40) (Z_to_bv 64 EX) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbl_memset3)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL CFG IDC OBS S8 SPOS SOFF SLO EMO EMODE OBM OBSM LC LO HB LOS SPH MI.
unfold R_L, RA_sbl_memset3, RA_sbl_innov2, A_split_cb_shape_sign_unquant, A_split_cb_high in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xb754c)) with (Z_to_bv 64 0xb754c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold sb_slots, sha in SL. unfold sbp_cfg in CFG. unfold sha.
rewrite EMO in *. cbn [sbmode_struct] in EMODE.
assert (ESUB : sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR ModeWB = MODE + 40) by (subst MODE; reflexivity).
rewrite ESUB in CFG.
assert (M8 : MODE mod 8 = 0) by (subst MODE; reflexivity).
pose proof (lib_const m A_sb_wb_mode LC_sb_wb_mode LC ltac:(lc_in)) as MTAB. rewrite <- EMODE in MTAB. unfold LC_sb_wb_mode in MTAB. unfold A_sb_wb_mode in EMODE.
pose proof (lib_const m A_wb_submode4 LC_wb_submode4 LC ltac:(lc_in)) as T4. unfold LC_wb_submode4 in T4.
cbn [sb_sub_addr Z.eqb Pos.eqb] in OBSM.
set (SM := A_wb_submode4) in *. assert (ESM : SM = 0xf0540) by reflexivity. assert (SM8 : SM mod 8 = 0) by reflexivity. clearbody SM.
ato 0xb7578. rewrite sx32_small by (unfold int31; lia). ato 0xb7594. rewrite <- ESM.
ato 0xac694.
apply evt_done. eexists. reflexivity.
Qed.
Definition RA_sbl_unpois1 : Z := 0xb769c.

Lemma sbl_e10 : forall (usp lo hb2 S OUT A f sf MODE fsz sub I2 EX : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs)
(ex i2 : list word) (xs3 : word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_slots usp S OUT A f sf MODE fsz v) -> v_416 v = Z_to_bv 64 hb2 -> v_120 v = Z_to_bv 64 (hb2 + 224) ->
rw_cells asegs m S (sbp_hdr s a) -> sbd_subframeSize s = 40 ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
I2 = hb2 + 32 -> rw_cells asegs m I2 (f32 i2) -> length i2 = 40%nat -> aobj asegs m I2 160 ->
EX = hb2 + 256 -> rw_cells asegs m EX (f32 ex) -> length ex = 40%nat -> aobj asegs m EX 160 ->
client_consts m -> stk asegs m lo hb2 -> lo <= hb2 - 16 -> hb2 + 224 <= usp + -1088 -> SH_HI <= lo -> usp < 2^63 -> hb2 mod 32 = 0 ->
mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (m1 : mem) (xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (F' : bvmap 5 word) (fc' : bv 32) (ex' i2' : list word),
ms = MS (R_L usp hb2 S sub gp tp (Z_to_bv 64 RA_sbl_unpois1) xt0 xt1 xt2 (Z_to_bv 64 hb2) (Z_to_bv 64 (hb2 + 224)) xa2 xa3 xa4 xa5 xa6 xa7
xs3 (Z_to_bv 64 (hb2 + 224)) (Z_to_bv 64 (4 * sub)) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 (S + 32)) (Z_to_bv 64 EX)
xt3 xt4 xt5 xt6) F' (Z_to_bv 64 sbl_e_allocas_unpoison) fc' None m1 (seg_rom asegs)
/\ munch [(I2, I2 + 160); (EX, EX + 160); (hb2 + -16, hb2)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo hb2 /\ frm0 fc'
/\ rw_cells asegs m1 EX (f32 ex') /\ length ex' = 40%nat /\ rw_cells asegs m1 I2 (f32 i2') /\ length i2' = 40%nat)
(MS (R_L usp hb2 S sub gp tp (Z_to_bv 64 RA_sbl_innov2) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
xs3 (Z_to_bv 64 I2) (Z_to_bv 64 (4 * sub)) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 40) (Z_to_bv 64 EX) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbl_innov2)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL V416 V120 HD EFS OBS S8 SPOS SOFF SLO EI2 I2C LI2 OBI2 EEX EXC LEX OBEX CC ST LO HB LOS SPH HB32 MI FRM.
unfold R_L, RA_sbl_innov2, RA_sbl_unpois1, sbl_e_allocas_unpoison in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xb75dc)) with (Z_to_bv 64 0xb75dc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof ST as (STa & STb & _). pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof (munch_refl [(I2, I2 + 160); (EX, EX + 160); (hb2 + -16, hb2)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(I2, I2 + 160); (EX, EX + 160); (hb2 + -16, hb2)]) by (clear - EI2 EEX LOS LO HB SPH; cbn; unfold SH_LO, SH_HI in *; lia).
unfold sb_slots, sha in SL. rewrite V416, V120 in SL. unfold sbp_hdr in HD. rewrite EFS in HD. unfold sha.
assert (EX8 : EX mod 8 = 0) by (subst EX; clear - HB32; Z.div_mod_to_equations; lia).
assert (I28 : I2 mod 8 = 0) by (subst I2; clear - HB32; Z.div_mod_to_equations; lia).
ato 0xb75f0. rewrite sx32_small by (unfold int31; lia).
ato 0xb75fc. astep.
call (sbl_signal_mul40 i2 I2 hb2 lo).
all: try eassumption.
all: try (unfold IMG_TOP, SH_LO, SH_HI in *; clear - EI2 I28 LO HB LOS' SPH STa; first [lia | Z.div_mod_to_equations; lia]).
rename PC1 into I2C'. rename POST into LI2'.
lazymatch type of LI2' with length ?l = _ => do 40 (destruct l as [|? l]; [discriminate LI2'|]); destruct l; [| discriminate LI2'] end. cbn [f32 map] in I2C'.
do 40 (destruct ex as [|? ex]; [discriminate LEX|]). destruct ex; [| discriminate LEX]. cbn [f32 map] in EXC.
ato 0xb7610. rewrite sx32_small by (unfold int31; lia).
ato 0xb7620.
ato 0xb7664.
ato 0xb768c.
ato 0x51e64.
apply evt_done. do 16 eexists.
lazymatch type of EXC with rw_cells _ _ _ ?cs => let l := eval cbv beta iota zeta delta [map] in (map (fun c => match c with C4 w => w | _ => Z_to_bv 64 0 end) cs) in exists l end.
lazymatch type of I2C' with rw_cells _ _ _ ?cs => let l := eval cbv beta iota zeta delta [map] in (map (fun c => match c with C4 w => w | _ => Z_to_bv 64 0 end) cs) in exists l end.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact PC|]. split; [assumption|]. split; [exact EXC|]. split; [reflexivity|]. split; [exact I2C'| reflexivity].
Qed.

Lemma sbl_e11 : forall (usp lo hb2 S sub EX MODE : Z) (jh : list byte) (xs3 : word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m hb2 [CB 224 jh] -> stk asegs m lo hb2 -> lo <= hb2 -> hb2 + 224 <= usp -> usp < 2^63 ->
evt asegs (fun ms =>
ms = MS (R_L usp (hb2 + 224) S sub gp tp (Z_to_bv 64 RA_sbl_unpois1) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
xs3 (Z_to_bv 64 (hb2 + 224)) (Z_to_bv 64 (4 * sub)) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 (S + 32)) (Z_to_bv 64 EX)
t3 t4 t5 t6) F (Z_to_bv 64 SBL_PC_J) fc None m (seg_rom asegs)
/\ stk asegs m lo (hb2 + 224))
(MS (R_L usp hb2 S sub gp tp (Z_to_bv 64 RA_sbl_unpois1) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
xs3 (Z_to_bv 64 (hb2 + 224)) (Z_to_bv 64 (4 * sub)) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 (S + 32)) (Z_to_bv 64 EX) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbl_unpois1)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros HULL ST LO0 HB SPH.
unfold R_L, RA_sbl_unpois1, SBL_PC_J in *.
replace (ret_pc (Z_to_bv 64 0xb769c)) with (Z_to_bv 64 0xb769c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0xb7808.
release_frame HULL ST (hb2 + 224).
apply evt_done. split; [reflexivity| exact ST].
Qed.
Lemma sbl_f32_snoc l x : f32 l ++ [C4 x] = f32 (l ++ [x]).
Proof. rewrite f32_app, f32_cons, f32_nil. reflexivity. Qed.

Section XBL.
Variables (EX XB NW : Z) (exs : list word).
Variables rav spv gp tp t0v t1v t2v s0v s1v a1v s2v s3v s4v s5v s6v s7v s8v s10v t3v t4v t5v t6v : word.
Hypothesis XB4 : XB mod 4 = 0.
Hypothesis XBI : IMG_TOP <= XB.
Hypothesis EX4 : EX mod 4 = 0.
Definition RXB (i cnt : Z) (a5v a6v a7v : word) : bvmap 5 word :=
mkR rav spv gp tp t0v t1v t2v s0v s1v (Z_to_bv 64 (XB + 4 * i)) a1v (Z_to_bv 64 (XB + 4 * i)) (Z_to_bv 64 cnt) (Z_to_bv 64 (EX + 4 * i)) a5v a6v a7v
s2v s3v s4v s5v s6v s7v s8v (Z_to_bv 64 SHB) s10v (Z_to_bv 64 (EX + 4 * i)) t3v t4v t5v t6v.
Definition xbl_post (fc : bv 32) (mI : mem) : machine_state -> Prop :=
fun ms' => exists a5' a6' a7' F' m' (ys' : list word),
ms' = MS (RXB NW 0 a5' a6' a7') F' (Z_to_bv 64 0xb79ac) fc None m' (seg_rom asegs)
/\ munch [(XB, XB + 4 * NW)] mI m' /\ wmono asegs mI m' /\ mem_inv asegs m'
/\ Z.of_nat (length ys') = NW /\ rw_cells asegs m' XB (f32 ys') /\ rw_cells asegs m' EX (f32 exs).
Lemma sbl_xb_loop : forall (mI : mem) (rest done : list word) (cw : word) (i cnt : Z) (a5v a6v a7v : word) F fc mc,
cnt = 1 + Z.of_nat (length rest) -> i = Z.of_nat (length done) -> i + 1 + Z.of_nat (length rest) = NW -> NW < 2^31 -> Z.of_nat (length exs) = NW ->
aobj asegs mI XB (4 * NW) -> aobj asegs mI EX (4 * NW) -> offsh [(XB, XB + 4 * NW)] -> (XB + 4 * NW <= EX \/ EX + 4 * NW <= XB) ->
mem_inv asegs mc -> munch [(XB, XB + 4 * NW)] mI mc -> wmono asegs mI mc ->
rw_cells asegs mc XB (f32 done) -> rw_cells asegs mc (XB + 4 * i) (f32 (cw :: rest)) -> rw_cells asegs mc EX (f32 exs) ->
evt asegs (xbl_post fc mI) (MS (RXB i cnt a5v a6v a7v) F (Z_to_bv 64 0xb7948) fc None mc (seg_rom asegs)).
Proof using XB4 XBI EX4.
intros mI rest.
induction rest as [|cw' rest IH]; intros done cw i cnt a5v a6v a7v F fc mc -> Hi HN HNW LEX OBY OBX OF SEP MI MU WM XD XC EXC;
pose proof OBY as (OY0 & OY1 & _); pose proof OBX as (OX0 & OX1 & _); unfold APP_TOP in *; pose proof XBI as YI'; unfold IMG_TOP in YI';
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
destruct (sbl_rw_f32_nth mc EX exs i EXC ltac:(cbn [length] in *; lia)) as (wx & WIN);
unfold RXB; rewrite !f32_cons in XC; cbn [length] in *.
- rewrite f32_nil in XC.
ato 0xb7954. astep. chk_merge OBX 4.
ato 0xb7968. astep. chk_merge OBY 4.
ato 0xb7984. astep. sh_if.
astep.
chunk_snoc XD XC. rewrite sbl_f32_snoc in XD.
replace (XB + 4 * i + 4) with (XB + 4 * NW) by lia. replace (EX + 4 * i + 4) with (EX + 4 * NW) by lia.
replace (1 + Z.of_nat 0 + -1) with 0 by lia.
apply evt_done. unfold xbl_post, RXB. do 5 eexists. lazymatch type of XD with rw_cells _ _ _ (f32 ?l) => exists l end.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [rewrite length_app; cbn [length]; lia|]. split; [exact XD| exact EXC].
- ato 0xb7954. astep. chk_merge OBX 4.
ato 0xb7968. astep. chk_merge OBY 4.
ato 0xb7984. astep. sh_if.
(let X1c := fresh "X1c" in chunk_uncons XC as X1c; chunk_snoc XD X1c). rewrite sbl_f32_snoc in XD. rewrite <- ?f32_cons in XC.
replace (XB + 4 * i + 4) with (XB + 4 * (i + 1)) in * by lia. replace (EX + 4 * i + 4) with (EX + 4 * (i + 1)) by lia.
replace (1 + Z.of_nat (S (length rest)) + -1) with (1 + Z.of_nat (length rest)) by lia.
clear WIN.
eapply (IH _ cw' (i + 1)); try eassumption; try reflexivity;
try (rewrite length_app; cbn [length] in *; lia); try (cbn [length] in *; lia).
Qed.
End XBL.

Section ISL.
Variables (EX Y NW : Z) (exs : list word).
Variables rav spv gp tp t0v t1v t2v s0v s1v a6v a7v s2v s4v s5v s6v s7v s8v s10v s11v t3v t4v t5v t6v : word.
Hypothesis Y4 : Y mod 4 = 0.
Hypothesis YI : IMG_TOP <= Y.
Hypothesis EX4 : EX mod 4 = 0.
Definition RIS (i cnt : Z) (a4v a5v : word) : bvmap 5 word :=
mkR rav spv gp tp t0v t1v t2v s0v s1v (Z_to_bv 64 (EX + 4 * i)) (Z_to_bv 64 (Y + 8 * i)) (Z_to_bv 64 cnt) (Z_to_bv 64 (EX + 4 * i)) a4v a5v a6v a7v
s2v (Z_to_bv 64 (Y + 8 * i)) s4v s5v s6v s7v s8v (Z_to_bv 64 SHB) s10v s11v t3v t4v t5v t6v.
Definition isl_post (fc : bv 32) (mI : mem) : machine_state -> Prop :=
fun ms' => exists a4' a5' F' m' (ys' : list word),
ms' = MS (RIS NW 0 a4' a5') F' (Z_to_bv 64 0xb78a4) fc None m' (seg_rom asegs)
/\ munch [(Y, Y + 8 * NW)] mI m' /\ wmono asegs mI m' /\ mem_inv asegs m'
/\ Z.of_nat (length ys') = 2 * NW /\ rw_cells asegs m' Y (f32 ys') /\ rw_cells asegs m' EX (f32 exs).
Lemma sbl_is_loop : forall (n : nat) (mI : mem) (rest done : list word) (i cnt : Z) (a4v a5v : word) F fc mc,
length rest = (2 * n + 2)%nat -> cnt = 1 + Z.of_nat n -> 2 * i = Z.of_nat (length done) -> i + 1 + Z.of_nat n = NW -> NW < 2^31 -> Z.of_nat (length exs) = NW ->
aobj asegs mI Y (8 * NW) -> aobj asegs mI EX (4 * NW) -> offsh [(Y, Y + 8 * NW)] -> (Y + 8 * NW <= EX \/ EX + 4 * NW <= Y) ->
mem_inv asegs mc -> munch [(Y, Y + 8 * NW)] mI mc -> wmono asegs mI mc ->
rw_cells asegs mc Y (f32 done) -> rw_cells asegs mc (Y + 8 * i) (f32 rest) -> rw_cells asegs mc EX (f32 exs) ->
evt asegs (isl_post fc mI) (MS (RIS i cnt a4v a5v) F (Z_to_bv 64 0xb7840) fc None mc (seg_rom asegs)).
Proof using Y4 YI EX4.
induction n as [|n IH]; intros mI rest done i cnt a4v a5v F fc mc LR -> Hi HN HNW LEX OBY OBX OF SEP MI MU WM XD XC EXC;
(destruct rest as [|cw [|c1 rest]]; [exfalso; cbn [length] in LR; lia | exfalso; cbn [length] in LR; lia |]);
pose proof OBY as (OY0 & OY1 & _); pose proof OBX as (OX0 & OX1 & _); unfold APP_TOP in *; pose proof YI as YI'; unfold IMG_TOP in YI';
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
destruct (sbl_rw_f32_nth mc EX exs i EXC ltac:(cbn [length] in *; lia)) as (wx & WIN);
unfold RIS; rewrite !f32_cons in XC; cbn [length] in *.
- destruct rest; [| exfalso; cbn [length] in LR; lia]. rewrite f32_nil in XC.
ato 0xb784c. astep. chk_merge OBX 4.
ato 0xb7860. astep. chk_merge OBY 4.
ato 0xb787c. astep. sh_if.
astep.
(let X1c := fresh "X1c" in chunk_uncons XC as X1c; chunk_snoc XD X1c). rewrite sbl_f32_snoc in XD.
chunk_snoc XD XC. rewrite sbl_f32_snoc in XD.
replace (Y + 8 * i + 8) with (Y + 8 * NW) by lia. replace (EX + 4 * i + 4) with (EX + 4 * NW) by lia.
replace (1 + Z.of_nat 0 + -1) with 0 by lia.
apply evt_done. unfold isl_post, RIS. do 4 eexists. lazymatch type of XD with rw_cells _ _ _ (f32 ?l) => exists l end.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [rewrite !length_app; cbn [length]; lia|]. split; [exact XD| exact EXC].
- ato 0xb784c. astep. chk_merge OBX 4.
ato 0xb7860. astep. chk_merge OBY 4.
ato 0xb787c. astep. sh_if.
(let X1c := fresh "X1c" in chunk_uncons XC as X1c; chunk_snoc XD X1c). rewrite sbl_f32_snoc in XD.
(let X2c := fresh "X2c" in chunk_uncons XC as X2c; chunk_snoc XD X2c). rewrite sbl_f32_snoc in XD. rewrite <- ?f32_cons in XC.
replace (Y + 8 * i + 4 + 4) with (Y + 8 * (i + 1)) in * by lia. replace (Y + 8 * i + 8) with (Y + 8 * (i + 1)) in * by lia. replace (EX + 4 * i + 4) with (EX + 4 * (i + 1)) by lia.
replace (1 + Z.of_nat (S n) + -1) with (1 + Z.of_nat n) by lia.
clear WIN.
eapply (IH mI rest _ (i + 1)); try eassumption; try reflexivity;
try (rewrite !length_app; cbn [length] in *; lia); try (cbn [length] in *; lia).
Qed.
End ISL.
Definition SBL_PC_K : Z := 0xb78a4.

Lemma sbl_e12a0 : forall (usp lo hb S OUT A f sf MODE fsz sub EX : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs) (xs3 xs4 xra : word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_slots usp S OUT A f sf MODE fsz v) -> v_248 v = Z_to_bv 64 (sha (S + 120)) ->
rw_cells asegs m (S + 40) (sbp_ptrs s a OUT) -> sb_isave_ptr OUT s = 0 ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
lo <= hb -> hb <= usp + -1088 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m ->
evt asegs (fun ms =>
ms = MS (R_L usp hb S sub gp tp xra t0 t1 t2 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
xs3 xs4 (Z_to_bv 64 (4 * sub)) (Z_to_bv 64 (sha (S + 28))) (Z_to_bv 64 (S + 32)) (Z_to_bv 64 EX)
t3 t4 t5 t6) F (Z_to_bv 64 SBL_PC_K) fc None m (seg_rom asegs))
(MS (R_L usp hb S sub gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
xs3 xs4 (Z_to_bv 64 (4 * sub)) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 (S + 32)) (Z_to_bv 64 EX) t3 t4 t5 t6)
F (Z_to_bv 64 SBL_PC_J) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL V248 PT EIS OBS S8 SPOS SOFF SLO LO HB LOS SPH MI.
unfold R_L, SBL_PC_J, SBL_PC_K in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh []) by (cbn; exact I).
unfold sb_slots, sha in SL. rewrite V248 in SL. unfold sha in SL. unfold sbp_ptrs in PT. rewrite EIS in PT. unfold sha.
ato 0xb78a4.
apply evt_done. reflexivity.
Qed.

Lemma sbl_e12a1 : forall (usp lo hb S OUT A f sf MODE fsz FS sub EX Y : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs) (exs yw : list word) (xs4 xra : word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_slots usp S OUT A f sf MODE fsz v) -> v_248 v = Z_to_bv 64 (sha (S + 120)) ->
rw_cells asegs m S (sbp_hdr s a) -> sbd_subframeSize s = FS -> (FS = 40 \/ FS = 80) ->
rw_cells asegs m (S + 40) (sbp_ptrs s a OUT) -> sb_isave_ptr OUT s <> 0 -> 0 < sb_isave_ptr OUT s < 2^63 ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
rw_cells asegs m EX (f32 exs) -> Z.of_nat (length exs) = FS -> aobj asegs m EX (4 * FS) -> EX mod 4 = 0 -> hb <= EX ->
rw_cells asegs m Y (f32 yw) -> Z.of_nat (length yw) = 2 * FS -> aobj asegs m Y (8 * FS) -> Y mod 4 = 0 -> IMG_TOP <= Y -> Y + 8 * FS <= lo ->
(Y + 8 * FS <= SH_LO \/ SH_HI <= Y) -> (S + 160 <= Y \/ Y + 8 * FS <= S) ->
lo <= hb -> hb <= usp + -1088 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (xa0 xa1 xa2 xa3 xa4 xa5 xs3' : word) (F' : bvmap 5 word) (yw' : list word),
ms = MS (R_L usp hb S sub gp tp xra t0 t1 t2 xa0 xa1 xa2 xa3 xa4 xa5 a6 a7
xs3' xs4 (Z_to_bv 64 (4 * sub)) (Z_to_bv 64 (sha (S + 28))) (Z_to_bv 64 (S + 32)) (Z_to_bv 64 EX)
t3 t4 t5 t6) F' (Z_to_bv 64 SBL_PC_K) fc None m1 (seg_rom asegs)
/\ munch [(Y, Y + 8 * FS)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 Y (f32 yw') /\ Z.of_nat (length yw') = 2 * FS)
(MS (R_L usp hb S sub gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 Y) xs4 (Z_to_bv 64 (4 * sub)) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 (S + 32)) (Z_to_bv 64 EX) t3 t4 t5 t6)
F (Z_to_bv 64 SBL_PC_J) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL V248 HD EFS HFS PT NIS RIS OBS S8 SPOS SOFF SLO EXC LEX OBEX EX4 HBEX YC LY OBY Y4 YI YLO YOFF SEPSY LO HB LOS SPH MI.
unfold R_L, SBL_PC_J, SBL_PC_K in *. unfold SH_LO, SH_HI in SOFF, YOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(Y, Y + 8 * FS)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(Y, Y + 8 * FS)]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold sb_slots, sha in SL. rewrite V248 in SL. unfold sha in SL. unfold sbp_hdr in HD. rewrite EFS in HD. unfold sbp_ptrs in PT. unfold sha.
ato 0xb7820. astep. sh_if.
ato 0xb7830.
rewrite sx32_small by (unfold int31; lia). astep. sh_if.
ato 0xb7840.
assert (XD0 : rw_cells asegs m Y (f32 [])) by (apply rw_cells_nil; pose proof OBY as (OY0 & OY1 & _); unfold APP_TOP in OY1; lia).
replace (Z_to_bv 64 EX) with (Z_to_bv 64 (EX + 4 * 0)) by (f_equal; lia). replace (Z_to_bv 64 Y) with (Z_to_bv 64 (Y + 8 * 0)) by (f_equal; lia).
call (sbl_is_loop EX Y FS exs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Y4 YI EX4 (Z.to_nat (FS - 1)) m yw [] 0 FS _ _ _ _ m).
all: try eassumption.
all: try (cbn [length]; lia).
{ replace (Y + 8 * 0) with Y by lia. exact YC. }
replace (EX + 4 * 0) with EX by lia.
apply evt_done. do 9 eexists. lazymatch type of PC0 with rw_cells _ _ _ (f32 ?l) => exists l end.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact PC0| exact PC].
Qed.

Lemma sbl_iir8 : forall (XB IQP YP MSP hb lo FS : Z) (vexc viq vm8 yp : list word)
(ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
Z.of_nat (length vexc) = FS -> (FS = 40 \/ FS = 80) -> length viq = 8%nat -> length vm8 = 8%nat -> Z.of_nat (length yp) = FS ->
aobj asegs m XB (4 * FS) -> aobj asegs m IQP 32 -> aobj asegs m MSP 32 -> aobj asegs m YP (4 * FS) ->
XB mod 4 = 0 -> IQP mod 4 = 0 -> MSP mod 4 = 0 -> YP mod 4 = 0 ->
lo <= hb - 80 -> SH_HI <= lo -> hb < 2^63 ->
(MSP + 32 <= SH_LO \/ SH_HI <= MSP) -> (YP + 4 * FS <= SH_LO \/ SH_HI <= YP) ->
(XB + 4 * FS <= lo \/ hb <= XB) -> (MSP + 32 <= lo \/ hb <= MSP) -> (IQP + 32 <= lo \/ hb <= IQP) -> (YP + 4 * FS <= lo \/ hb <= YP) ->
(IQP + 32 <= MSP \/ MSP + 32 <= IQP) -> (XB + 4 * FS <= MSP \/ MSP + 32 <= XB) -> (XB + 4 * FS <= IQP \/ IQP + 32 <= XB) ->
(XB + 4 * FS <= YP \/ YP + 4 * FS <= XB) -> (YP + 4 * FS <= MSP \/ MSP + 32 <= YP) -> (YP + 4 * FS <= IQP \/ IQP + 32 <= YP) ->
rw_cells asegs m XB (f32 vexc) -> rw_cells asegs m IQP (f32 viq) -> rw_cells asegs m MSP (f32 vm8) -> rw_cells asegs m YP (f32 yp) ->
frm0 fc -> stk asegs m lo hb -> IMG_TOP <= YP -> IMG_TOP <= MSP -> client_consts m -> mem_inv asegs m ->
evt asegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' (ys mv : list word),
ms' = MS (mkR ra (Z_to_bv 64 hb) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(YP, YP + 4 * FS); (MSP, MSP + 32); (hb + -80, hb)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo hb
/\ frm0 fc' /\ Z.of_nat (length ys) = FS /\ rw_cells asegs m' YP (f32 ys)
/\ length mv = 8%nat /\ rw_cells asegs m' MSP (f32 mv)
/\ rw_cells asegs m' IQP (f32 viq) /\ rw_cells asegs m' XB (f32 vexc))
(MS (mkR ra (Z_to_bv 64 hb) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 XB) (Z_to_bv 64 IQP) (Z_to_bv 64 YP) (Z_to_bv 64 FS) (Z_to_bv 64 8) (Z_to_bv 64 MSP) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_iir_mem16) fc None m (seg_rom asegs)).
Proof.
intros until m. intros LX HFS LQ LM LY OX OQ OM OY X4 Q4 M4 Y4 LO LOS SPH MSH YSH XAP MAP QAP YAP SQM SXM SXQ SXY SYM SYQ CX CQ CM CY FRM ST YI MI' CC MI.
assert (EQ8 : Z.of_nat (length viq) = 8) by (rewrite LQ; reflexivity).
assert (N1 : 1 <= Z.of_nat (length vexc) < 2^31) by (rewrite LX; destruct HFS; subst; lia).
assert (ORD : 2 <= Z.of_nat (length viq) < 2^31) by (rewrite EQ8; lia).
assert (LMEM : length vm8 = length viq) by (rewrite LM, LQ; reflexivity).
assert (LYS : length yp = length vexc) by (apply Nat2Z.inj; rewrite LY, LX; reflexivity).
assert (E32 : 4 * Z.of_nat (length viq) = 32) by (rewrite EQ8; reflexivity).
pose proof (iir_mem16_walk_dj vexc viq vm8 XB IQP MSP hb lo ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m LMEM N1 ORD
ltac:(rewrite LX; exact OX) ltac:(rewrite E32; exact OQ) ltac:(rewrite E32; exact OM) X4 Q4 M4 LO LOS SPH
ltac:(rewrite E32; exact MSH) ltac:(rewrite LX; exact XAP) ltac:(rewrite E32; exact MAP) ltac:(rewrite E32; exact QAP)
ltac:(rewrite E32; exact SQM) ltac:(rewrite LX, E32; exact SXM) ltac:(rewrite LX, E32; exact SXQ)
YP ltac:(rewrite LX; exact OY) Y4 ltac:(rewrite LX; exact YSH) ltac:(rewrite LX; exact YAP) ltac:(rewrite LX; exact SXY)
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
Definition SBL_PC_M : Z := 0xb79ac.

Lemma sbl_e12b : forall (usp lo hb S OUT A f sf MODE fsz FS sub EX XB IQP MSP YP : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs)
(exs vexc viq vm8 yp : list word) (xs3 xs4 xra : word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_slots usp S OUT A f sf MODE fsz v) -> v_256 v = Z_to_bv 64 YP ->
rw_cells asegs m S (sbp_hdr s a) -> sbd_subframeSize s = FS -> sbd_lpcSize s = 8 -> (FS = 40 \/ FS = 80) ->
rw_cells asegs m (S + 40) (sbp_ptrs s a OUT) -> XB = a_exc a -> IQP = a_iq a -> MSP = a_msp a ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
rw_cells asegs m EX (f32 exs) -> Z.of_nat (length exs) = FS -> aobj asegs m EX (4 * FS) -> EX mod 4 = 0 -> hb <= EX -> EX + 4 * FS <= usp ->
rw_cells asegs m XB (f32 vexc) -> Z.of_nat (length vexc) = FS -> aobj asegs m XB (4 * FS) -> XB mod 4 = 0 -> IMG_TOP <= XB -> XB + 4 * FS <= lo -> (XB + 4 * FS <= SH_LO \/ SH_HI <= XB) ->
rw_cells asegs m IQP (f32 viq) -> length viq = 8%nat -> aobj asegs m IQP 32 -> IQP mod 4 = 0 -> IQP + 32 <= lo ->
rw_cells asegs m MSP (f32 vm8) -> length vm8 = 8%nat -> aobj asegs m MSP 32 -> MSP mod 4 = 0 -> IMG_TOP <= MSP -> MSP + 32 <= lo -> (MSP + 32 <= SH_LO \/ SH_HI <= MSP) ->
rw_cells asegs m YP (f32 yp) -> Z.of_nat (length yp) = FS -> aobj asegs m YP (4 * FS) -> YP mod 4 = 0 -> IMG_TOP <= YP -> YP + 4 * FS <= lo -> (YP + 4 * FS <= SH_LO \/ SH_HI <= YP) ->
(IQP + 32 <= MSP \/ MSP + 32 <= IQP) -> (XB + 4 * FS <= MSP \/ MSP + 32 <= XB) -> (XB + 4 * FS <= IQP \/ IQP + 32 <= XB) ->
(XB + 4 * FS <= YP \/ YP + 4 * FS <= XB) -> (YP + 4 * FS <= MSP \/ MSP + 32 <= YP) -> (YP + 4 * FS <= IQP \/ IQP + 32 <= YP) ->
(S + 160 <= XB \/ XB + 4 * FS <= S) -> (S + 160 <= MSP \/ MSP + 32 <= S) -> (S + 160 <= YP \/ YP + 4 * FS <= S) ->
client_consts m -> stk asegs m lo hb -> lo <= hb - 80 -> hb <= usp + -1088 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (m1 : mem) (xra' xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (F' : bvmap 5 word) (fc' : bv 32) (vexc' vm8' yp' : list word),
ms = MS (R_L usp hb S sub gp tp xra' xt0 xt1 xt2 xa0 (Z_to_bv 64 FS) xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 (sha (S + 72))) (Z_to_bv 64 (sha (S + 88))) (Z_to_bv 64 (4 * sub)) (Z_to_bv 64 (sha (S + 28))) (Z_to_bv 64 (S + 32)) (Z_to_bv 64 (EX + 4 * FS))
xt3 xt4 xt5 xt6) F' (Z_to_bv 64 SBL_PC_M) fc' None m1 (seg_rom asegs)
/\ munch [(YP, YP + 4 * FS); (MSP, MSP + 32); (hb + -80, hb); (XB, XB + 4 * FS)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo hb /\ frm0 fc'
/\ rw_cells asegs m1 XB (f32 vexc') /\ Z.of_nat (length vexc') = FS
/\ rw_cells asegs m1 MSP (f32 vm8') /\ length vm8' = 8%nat
/\ rw_cells asegs m1 YP (f32 yp') /\ Z.of_nat (length yp') = FS)
(MS (R_L usp hb S sub gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
xs3 xs4 (Z_to_bv 64 (4 * sub)) (Z_to_bv 64 (sha (S + 28))) (Z_to_bv 64 (S + 32)) (Z_to_bv 64 EX) t3 t4 t5 t6)
F (Z_to_bv 64 SBL_PC_K) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL V256 HD EFS ELPC HFS PT EXB EIQ EMSP OBS S8 SPOS SOFF SLO EXC LEX OBEX EX4 HBEX EXU
XBC LXB OBXB XB4 XBI XBLO XBOFF IQC LIQ OBIQ IQ4 IQLO MSC LMS OBMS MS4 MSI MSLO MSOFF YPC LYP OBYP YP4 YPI YPLO YPOFF
SEPDM SEPXM SEPXD SEPXY SEPYM SEPYD SEPSX SEPSM SEPSY CC ST LO HB LOS SPH MI FRM.
unfold R_L, SBL_PC_K, SBL_PC_M in *.
unfold SH_LO, SH_HI in SOFF, XBOFF, MSOFF, YPOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof XBI as XBI'. pose proof MSI as MSI'. pose proof YPI as YPI'. unfold IMG_TOP in XBI', MSI', YPI'.
pose proof ST as (STa & STb & _). pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof (munch_refl [(YP, YP + 4 * FS); (MSP, MSP + 32); (hb + -80, hb); (XB, XB + 4 * FS)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(YP, YP + 4 * FS); (MSP, MSP + 32); (hb + -80, hb); (XB, XB + 4 * FS)]) by (clear - YPOFF MSOFF XBOFF LOS' LO HB SPH HFS; cbn; unfold SH_LO, SH_HI; lia).
assert (FSB : 40 <= FS <= 80) by (clear - HFS; lia).
hide_disj.
assert (LIQz : Z.of_nat (length viq) = 8) by (rewrite LIQ; reflexivity). assert (LMSz : Z.of_nat (length vm8) = 8) by (rewrite LMS; reflexivity).
unfold sb_slots, sha in SL. rewrite V256 in SL. unfold sbp_hdr in HD. rewrite EFS, ELPC in HD. unfold sbp_ptrs in PT. rewrite <- EXB, <- EIQ, <- EMSP in PT. unfold sha.
ato 0xb78f0. rewrite sx32_small by (unfold int31; lia).
ato 0xb7908. rewrite sx32_small by (unfold int31; lia).
ato 0xb7914. astep.
unfold lhide in SEPSX, SEPSM, SEPSY.
call (sbl_iir8 XB IQP YP MSP hb lo FS vexc viq vm8 yp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LXB HFS LIQ LMS LYP OBXB OBIQ OBMS OBYP XB4 IQ4 MS4 YP4 LO LOS ltac:(clear - HB SPH; lia)
MSOFF YPOFF (or_introl XBLO) (or_introl MSLO) (or_introl IQLO) (or_introl YPLO) SEPDM SEPXM SEPXD SEPXY SEPYM SEPYD XBC IQC MSC YPC FRM ST YPI MSI CC MI).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch asegs _ m mc S 160 OBS MU (shfree_of_aobj asegs _ m S 160 OF OBS)) as OBS1;
pose proof (aobj_munch asegs _ m mc EX (4 * FS) OBEX MU (shfree_of_aobj asegs _ m EX (4 * FS) OF OBEX)) as OBEX1;
pose proof (aobj_munch asegs _ m mc XB (4 * FS) OBXB MU (shfree_of_aobj asegs _ m XB (4 * FS) OF OBXB)) as OBXB1
end.
astep.
ato 0xb7924.
rewrite sx32_small by (unfold int31; lia). astep. sh_if.
ato 0xb7948.
rewrite (Z.mod_small FS 4294967296) by lia.
destruct vexc as [|cw rest]; [cbn [length] in LXB; lia|].
replace (Z_to_bv 64 EX) with (Z_to_bv 64 (EX + 4 * 0)) by (f_equal; lia).
replace (Z_to_bv 64 XB) with (Z_to_bv 64 (XB + 4 * 0)) by (f_equal; lia).
assert (XD0 : rw_cells asegs x16 XB (f32 [])) by (apply rw_cells_nil; pose proof OBXB1 as (OY0 & OY1 & _); unfold APP_TOP in OY1; lia).
assert (OFX : offsh [(XB, XB + 4 * FS)]) by (unfold lhide in XBOFF; cbn; unfold SH_LO, SH_HI; lia).
pose proof (munch_refl [(XB, XB + 4 * FS)] x16) as MUX. pose proof (wmono_refl asegs x16) as WMX.
unfold lhide in SEPXY, SEPXM.
call (sbl_xb_loop EX XB FS exs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XB4 XBI EX4 x16 rest [] cw 0 FS _ _ _ _ _ x16
ltac:(cbn [length] in LXB; lia) eq_refl ltac:(cbn [length] in LXB; cbn [length]; lia) ltac:(lia) LEX OBXB1 OBEX1 OFX ltac:(left; lia)
MI0 MUX WMX XD0 ltac:(replace (XB + 4 * 0) with XB by lia; exact POST) EXC).
apply evt_done. do 16 eexists. exists x22, x15, x24, x18, x17.
split; [unfold R_L, sha; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact PC|]. split; [exact PC0|].
split; [exact PC6|]. split; [exact PC5|]. split; [exact PC4|]. split; [exact PC3|]. split; [exact PC2| exact PC1].
Qed.

Lemma sbl_rms16 : forall (xs : list word) (p usp lo FS : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (m : mem)
(t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) fc,
Z.of_nat (length xs) = FS -> 1 <= FS < 2^31 -> aobj asegs m p (4 * FS) -> p mod 4 = 0 -> lo <= usp - 16 -> SH_HI <= lo -> usp < 2^63 ->
(p + 4 * FS <= lo \/ usp <= p) ->
rw_cells asegs m p (f32 xs) -> frm0 fc -> stk asegs m lo usp -> client_consts m -> mem_inv asegs m ->
evt asegs (fun ms' => exists t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) fc' m',
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 FS) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(usp + -16, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp /\ frm0 fc')
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 FS) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_compute_rms16) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros LX N1 OB X4 LO LOS SPH XAP XC FRM ST CC MI.
pose proof (compute_rms16_walk xs p usp lo ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m ltac:(rewrite LX; exact N1) ltac:(rewrite LX; exact OB) X4 LO LOS SPH
ltac:(rewrite LX; exact XAP) t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc XC FRM ST CC MI) as W.
rewrite LX in W. eapply evt_mono; [exact W|].
intros ms' (t0' & t1' & t2' & a0' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & g13 & g14 & g15 & fc' & m' & EQ & REST).
do 14 eexists. exists (bvmap_set 10 (rms_result (rms_sum fzero_s xs) (Z_to_bv 64 FS)) (bvmap_set 13 g13 (bvmap_set 14 g14 (bvmap_set 15 g15 F)))), fc', m'.
split; [exact EQ| exact REST].
Qed.
Definition RA_sbl_e12 : Z := 0xb7ac4.
Lemma sbl_f32_split3 : forall (m : mem) A (ws : list word) i, rw_cells asegs m A (f32 ws) -> 0 <= i < Z.of_nat (length ws) ->
rw_cells asegs m A (f32 (firstn (Z.to_nat i) ws)) /\ rw_cells asegs m (A + 4 * i) [C4 (nth (Z.to_nat i) ws (Z_to_bv 64 0))]
/\ rw_cells asegs m (A + 4 * i + 4) (f32 (skipn (S (Z.to_nat i)) ws)).
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
Lemma sbl_f32_join3 : forall (m : mem) A (l1 l2 : list word) (x : word),
rw_cells asegs m A (f32 l1) -> rw_cells asegs m (A + 4 * Z.of_nat (length l1)) [C4 x] -> rw_cells asegs m (A + 4 * Z.of_nat (length l1) + 4) (f32 l2) ->
rw_cells asegs m A (f32 (l1 ++ x :: l2)).
Proof.
intros m A l1 l2 x H1 H2 H3. rewrite f32_app, f32_cons. apply rw_cells_join; [exact H1|].
rewrite cells_size_f32. replace (Z.of_nat (4 * length l1)) with (4 * Z.of_nat (length l1)) by lia.
change (C4 x :: f32 l2) with ([C4 x] ++ f32 l2). apply rw_cells_join; [exact H2|]. cbn [cells_size csize]. replace (A + 4 * Z.of_nat (length l1) + Z.of_nat (4 + 0)) with (A + 4 * Z.of_nat (length l1) + 4) by lia. exact H3.
Qed.

Lemma sbl_e12c : forall (usp lo hb S OUT A f sf MODE fsz FS sub XB IQP ER AK : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs)
(vexc viq ers lak : list word) (xra xs11 : word)
(gp tp t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_slots usp S OUT A f sf MODE fsz v) ->
rw_cells asegs m S (sbp_hdr s a) -> sbd_subframeSize s = FS -> sbd_lpcSize s = 8 -> sbd_nbSubframes s = 4 -> (FS = 40 \/ FS = 80) -> 0 <= sub < 4 ->
rw_cells asegs m (S + 40) (sbp_ptrs s a OUT) -> XB = a_exc a -> IQP = a_iq a -> ER = a_er a ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
rw_cells asegs m XB (f32 vexc) -> Z.of_nat (length vexc) = FS -> aobj asegs m XB (4 * FS) -> XB mod 4 = 0 -> XB + 4 * FS <= lo ->
rw_cells asegs m IQP (f32 viq) -> length viq = 8%nat -> aobj asegs m IQP 32 -> IQP mod 4 = 0 -> IMG_TOP <= IQP -> IQP + 32 <= lo -> (IQP + 32 <= SH_LO \/ SH_HI <= IQP) ->
rw_cells asegs m ER (f32 ers) -> length ers = 4%nat -> aobj asegs m ER 16 -> ER mod 4 = 0 -> IMG_TOP <= ER -> ER + 16 <= lo -> (ER + 16 <= SH_LO \/ SH_HI <= ER) ->
(IQP + 32 <= ER \/ ER + 16 <= IQP) -> (S + 160 <= IQP \/ IQP + 32 <= S) -> (S + 160 <= ER \/ ER + 16 <= S) ->
(XB + 4 * FS <= IQP \/ IQP + 32 <= XB) -> (XB + 4 * FS <= ER \/ ER + 16 <= XB) ->
AK = usp + -1056 -> rw_cells asegs m AK (f32 lak) -> length lak = 8%nat -> aobj asegs m AK 32 ->
client_consts m -> stk asegs m lo hb -> lo <= hb - 16 -> hb <= usp + -1088 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 -> mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (m1 : mem) (xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (F' : bvmap 5 word) (fc' : bv 32) (viq' ers' : list word),
ms = MS (R_L usp hb S sub gp tp (Z_to_bv 64 RA_sbl_e12) xt0 xt1 xt2 (v_416 v) (v_264 v) xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 4) (Z_to_bv 64 (S + 28)) (Z_to_bv 64 S) (Z_to_bv 64 (sha (S + 28))) (v_264 v) (Z_to_bv 64 OUT)
xt3 xt4 xt5 xt6) F' (Z_to_bv 64 sbl_e_allocas_unpoison) fc' None m1 (seg_rom asegs)
/\ munch [(IQP, IQP + 32); (ER, ER + 16); (hb + -16, hb)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo hb /\ frm0 fc'
/\ rw_cells asegs m1 IQP (f32 viq') /\ length viq' = 8%nat /\ rw_cells asegs m1 ER (f32 ers') /\ length ers' = 4%nat)
(MS (R_L usp hb S sub gp tp xra t0 t1 t2 a0 (Z_to_bv 64 FS) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (sha (S + 72))) (Z_to_bv 64 (sha (S + 88))) (Z_to_bv 64 (4 * sub)) (Z_to_bv 64 (sha (S + 28))) (Z_to_bv 64 (S + 32)) xs11 t3 t4 t5 t6)
F (Z_to_bv 64 SBL_PC_M) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL HD EFS ELPC ENSF HFS SUB PT EXB EIQ EER OBS S8 SPOS SOFF SLO XBC LXB OBXB XB4 XBLO IQC LIQ OBIQ IQ4 IQI IQLO IQOFF
ERC LER OBER ER4 ERI ERLO EROFF SEPQE SEPSQ SEPSE SEPXQ SEPXE EAK AKC LAK OBAK CC ST LO HB LOS SPH U32 MI FRM.
unfold R_L, RA_sbl_e12, SBL_PC_M, sbl_e_allocas_unpoison in *.
unfold SH_LO, SH_HI in SOFF, IQOFF, EROFF. pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof IQI as IQI'. pose proof ERI as ERI'. unfold IMG_TOP in IQI', ERI'.
pose proof ST as (STa & STb & _). pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof (munch_refl [(IQP, IQP + 32); (ER, ER + 16); (hb + -16, hb)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(IQP, IQP + 32); (ER, ER + 16); (hb + -16, hb)]) by (clear - IQOFF EROFF LOS' LO HB SPH; cbn; unfold SH_LO, SH_HI; lia).
assert (FSB : 40 <= FS <= 80) by (clear - HFS; lia).
assert (LIQz : Z.of_nat (length viq) = 8) by (rewrite LIQ; reflexivity). assert (LAKz : Z.of_nat (length lak) = 8) by (rewrite LAK; reflexivity).
assert (LERz : Z.of_nat (length ers) = 4) by (rewrite LER; reflexivity).
hide_disj. unfold lhide in SEPSQ, SEPXQ, SEPQE.
unfold sb_slots, sha in SL. unfold sbp_hdr in HD. rewrite EFS, ELPC, ENSF in HD. unfold sbp_ptrs in PT. rewrite <- EXB, <- EIQ, <- EER in PT. unfold sha.
rewrite <- EAK in SL.
assert (AK8 : AK mod 8 = 0) by (subst AK; clear - U32; Z.div_mod_to_equations; lia).
do 8 (destruct lak as [|? lak]; [discriminate LAK|]). destruct lak; [| discriminate LAK]. cbn [f32 map] in AKC.
do 8 (destruct viq as [|? viq]; [discriminate LIQ|]). destruct viq; [| discriminate LIQ]. cbn [f32 map] in IQC.
ato 0xb79b8.
ato 0xb79c4. rewrite ?sx32_small by (unfold int31; lia). astep.
ato 0xb79ec.
ato 0xb79f8.
astep. ato 0xb7a0c. astep. chk_merge OBIQ 4.
ato 0xb7a28. astep.
do 7 (ato 0xb79f8; astep; ato 0xb7a0c; astep; chk_merge OBIQ 4; ato 0xb7a28; astep).
ato 0xb7a64. astep.
assert (CC1 : client_consts m1) by (unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4)))).
unfold lhide in SEPXE.
call (sbl_rms16 vexc XB hb lo FS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
LXB ltac:(lia) (aobj_munch asegs _ m m1 XB (4 * FS) OBXB MU (shfree_of_aobj asegs _ m XB (4 * FS) OF OBXB)) XB4 LO LOS ltac:(clear - HB SPH; lia)
(or_introl XBLO) XBC FRM ST CC1 MI).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch asegs _ m mc S 160 OBS MU (shfree_of_aobj asegs _ m S 160 OF OBS)) as OBS1;
pose proof (aobj_munch asegs _ m mc ER 16 OBER MU (shfree_of_aobj asegs _ m ER 16 OF OBER)) as OBER1
end.
ato 0xb7a9c.
astep. chk_merge OBER 4.
destruct (sbl_f32_split3 _ ER ers sub ERC ltac:(lia)) as (ER1 & ER2 & ER3). clear ERC.
assert (LL1 : Z.of_nat (length (firstn (Z.to_nat sub) ers)) = sub) by (rewrite length_firstn; lia).
assert (LL2 : Z.of_nat (length (skipn (Datatypes.S (Z.to_nat sub)) ers)) = 3 - sub) by (rewrite length_skipn; lia).
remember (firstn (Z.to_nat sub) ers) as l1 eqn:EL1. remember (skipn (Datatypes.S (Z.to_nat sub)) ers) as l2 eqn:EL2.
remember (nth (Z.to_nat sub) ers (Z_to_bv 64 0)) as w1 eqn:EW1.
unfold lhide in SEPSE.
ato 0xb7aa8.
ato 0xb7ac0.
rewrite sx32_small by (unfold int31; lia). astep.
assert (ERJ : rw_cells asegs m0 ER (f32 (l1 ++ fmv_s (reg_get x21 10) :: l2))).
{ apply sbl_f32_join3; [exact ER1| rewrite LL1; exact ER2| rewrite LL1; exact ER3]. }
apply evt_done. do 16 eexists. exists [nan_box (low32 b); nan_box (low32 b0); nan_box (low32 b1); nan_box (low32 b2); nan_box (low32 b3); nan_box (low32 b4); nan_box (low32 b5); nan_box (low32 b6)], (l1 ++ fmv_s (reg_get x21 10) :: l2).
split; [unfold R_L, sha; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [cbn [f32 map]; exact IQC|]. split; [reflexivity|]. split; [exact ERJ|].
apply Nat2Z.inj. rewrite length_app. cbn [length]. lia.
Qed.
Definition sbv_296 (v : sb_vslots) (w : word) : sb_vslots :=
SBV (v_8 v) (v_120 v) (v_248 v) (v_256 v) (v_264 v) w (v_384 v) (v_392 v) (v_400 v) (v_416 v) (v_424 v) (v_432 v) (v_440 v).

Lemma sbl_e13 : forall (usp hb lo S OUT A f sf MODE fsz sub : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs)
(gp tp : word) (xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_slots usp S OUT A f sf MODE fsz v) -> v_264 v = Z_to_bv 64 (usp + -1088) -> v_296 v = Z_to_bv 64 sub ->
rw_cells asegs m S (sbp_hdr s a) -> sbd_nbSubframes s = 4 -> 0 <= sub < 4 ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
lo <= usp + -1088 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (m1 : mem) (k : sb_rjunk) (F' : bvmap 5 word) (fc' : bv 32),
((sub < 3 /\ ms = MS (R_LA usp S OUT MODE (sub + 1) gp tp k) F' (Z_to_bv 64 SB_LA_PC) fc' None m1 (seg_rom asegs))
\/ (sub = 3 /\ ms = MS (R_TA usp S OUT gp tp k) F' (Z_to_bv 64 SB_TA_PC) fc' None m1 (seg_rom asegs)))
/\ munch [(usp + -312, usp + -304)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ frm0 fc'
/\ rw_cells asegs m1 (usp + -608) (sb_slots usp S OUT A f sf MODE fsz (sbv_296 v (Z_to_bv 64 (sub + 1)))))
(MS (R_L usp hb S sub gp tp (Z_to_bv 64 RA_sbl_e12) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 4) (Z_to_bv 64 (S + 28)) (Z_to_bv 64 S) (Z_to_bv 64 (sha (S + 28))) (v_264 v) (Z_to_bv 64 OUT) xt3 xt4 xt5 xt6)
F (ret_pc (Z_to_bv 64 RA_sbl_e12)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL V264 V296 HD ENSF SUB OBS S8 SPOS SOFF SLO LO LOS SPH MI FRM.
unfold R_L, RA_sbl_e12 in *. rewrite V264.
replace (ret_pc (Z_to_bv 64 0xb7ac4)) with (Z_to_bv 64 0xb7ac4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(usp + -312, usp + -304)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -312, usp + -304)]) by (clear - LOS' LO SPH; cbn; unfold SH_LO, SH_HI; lia).
unfold sb_slots, sha in SL. rewrite V264, V296 in SL. unfold sbp_hdr in HD. rewrite ENSF in HD. unfold sha.
ato 0xb7b04.
rewrite sx32_small by (unfold int31; lia).
assert (SC : sub < 3 \/ sub = 3) by lia. destruct SC as [SL3 | E3].
- astep. sh_if.
apply evt_done. exists m0, (SBRJ (Z_to_bv 64 752324) xt0 xt1 xt2 (Z_to_bv 64 4) (Z_to_bv 64 (sub + 1)) xa2 xa3 xa4 xa5 (Z_to_bv 64 0) xa7
(Z_to_bv 64 0) (Z_to_bv 64 4) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 S) xt3 xt4 xt5 xt6).
do 2 eexists. split; [left; split; [exact SL3| unfold R_LA, SB_LA_PC, sha; reflexivity]|].
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
unfold sb_slots, sbv_296, sha; cbn [v_8 v_120 v_248 v_256 v_264 v_296 v_384 v_392 v_400 v_416 v_424 v_432 v_440]; rewrite V264. exact SL.
- subst sub. astep. ato 0xb7d50.
apply evt_done. exists m0, (SBRJ (Z_to_bv 64 752324) xt0 xt1 xt2 (Z_to_bv 64 4) (Z_to_bv 64 (3 + 1)) xa2 xa3 xa4 xa5 (Z_to_bv 64 4096) xa7
(Z_to_bv 64 (sha (S + 24))) (Z_to_bv 64 4) (Z_to_bv 64 (S + 28)) (Z_to_bv 64 (3 + 1)) (Z_to_bv 64 (S + 24)) (Z_to_bv 64 S) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 S) xt3 xt4 xt5 xt6).
do 2 eexists. split; [right; split; [reflexivity| unfold R_TA, SB_TA_PC, sha; reflexivity]|].
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
unfold sb_slots, sbv_296, sha; cbn [v_8 v_120 v_248 v_256 v_264 v_296 v_384 v_392 v_400 v_416 v_424 v_432 v_440]; rewrite V264. exact SL.
Qed.

Section FLD.
Variables (EX LI FG NW : Z) (lis : list word).
Variables rav spv gp tp t1v t2v s0v s1v s2v s3v s4v s5v s6v s7v s10v s11v t3v t4v t5v t6v : word.
Hypothesis EX8 : EX mod 8 = 0.
Hypothesis LI4 : LI mod 4 = 0.
Hypothesis FG8 : FG mod 8 = 0.
Hypothesis LIL : Z.of_nat (length lis) = NW.
Hypothesis NWB : 0 < NW < 2^31.
Definition RFL (i : Z) (t0x a2v a7v : word) : bvmap 5 word :=
mkR rav spv gp tp t0x t1v t2v s0v s1v (Z_to_bv 64 (LI + 4 * i)) (Z_to_bv 64 (EX + 4 * i)) a2v (Z_to_bv 64 NW) (Z_to_bv 64 i)
(Z_to_bv 64 (LI + 4 * i + 4)) (Z_to_bv 64 (EX + 4 * i + 4)) a7v
s2v s3v s4v s5v s6v s7v (Z_to_bv 64 FG) (Z_to_bv 64 SHB) s10v s11v t3v t4v t5v t6v.
Definition fld_post (mI : mem) : machine_state -> Prop :=
fun ms' => exists t0' a2' a7' F' (fc' : bv 32) m' (ys' : list word),
ms' = MS (RFL NW t0' a2' a7') F' (Z_to_bv 64 0xb7808) fc' None m' (seg_rom asegs)
/\ munch [(EX, EX + 4 * NW)] mI m' /\ wmono asegs mI m' /\ mem_inv asegs m' /\ frm0 fc'
/\ Z.of_nat (length ys') = NW /\ rw_cells asegs m' EX (f32 ys') /\ rw_cells asegs m' LI (f32 lis).
Lemma sbl_fold_loop : forall (k : nat) (mI : mem) (rest done : list word) (fgw : word) (i : Z) (t0x a2v a7v : word) F fc mc,
length rest = (2 * S k)%nat -> i = Z.of_nat (length done) -> i + Z.of_nat (length rest) = NW ->
aobj asegs mI EX (4 * NW) -> aobj asegs mI LI (4 * NW) -> aobj asegs mI FG 4 -> offsh [(EX, EX + 4 * NW)] ->
(EX + 4 * NW <= LI \/ LI + 4 * NW <= EX) -> (EX + 4 * NW <= FG \/ FG + 4 <= EX) ->
mem_inv asegs mc -> munch [(EX, EX + 4 * NW)] mI mc -> wmono asegs mI mc -> frm0 fc ->
rw_cells asegs mc EX (f32 done) -> rw_cells asegs mc (EX + 4 * i) (f32 rest) -> rw_cells asegs mc LI (f32 lis) -> ro_cells asegs mc FG [C4 fgw] ->
evt asegs (fld_post mI) (MS (RFL i t0x a2v a7v) F (Z_to_bv 64 0xb7720) fc None mc (seg_rom asegs)).
Proof using EX8 LI4 FG8 LIL NWB.
induction k as [|k IH]; intros mI rest done fgw i t0x a2v a7v F fc mc LR Hi HN OBX OBL OBF OF SEPL SEPF MI MU WM FRM XD XC LC FGC;
pose proof OBX as (OX0 & OX1 & _); pose proof OBL as (OL0 & OL1 & _); pose proof OBF as (OF0 & OF1 & _); unfold APP_TOP in *;
destruct rest as [|c0 [|c1 rest']]; cbn [length] in LR, HN; try lia;
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
destruct (sbl_rw_f32_nth mc LI lis i LC ltac:(cbn [length] in *; lia)) as (wl0 & WL0);
destruct (sbl_rw_f32_nth mc LI lis (i + 1) LC ltac:(cbn [length] in *; lia)) as (wl1 & WL1);
unfold RFL; rewrite !f32_cons in XC;
(let X0 := fresh "X0c" in chunk_uncons XC as X0);
(let X1 := fresh "X1c" in chunk_uncons XC as X1).
- replace (LI + 4 * (i + 1)) with (LI + 4 * i + 4) in WL1 by lia.
ato 0xb772c. astep. chk_merge OBF 4.
ato 0xb7738.
astep. ato 0xb7740. astep. chk_merge OBL 4.
ato 0xb7754. astep. chk_merge OBX 4.
ato 0xb7774. astep. chk_merge OBL 4.
ato 0xb778c. astep. chk_merge OBX 4.
ato 0xb77b0.
astep. sh_if.
astep.
chunk_snoc XD X0c. rewrite sbl_f32_snoc in XD. chunk_snoc XD X1c. rewrite sbl_f32_snoc in XD.
replace (LI + 4 * i + 8) with (LI + 4 * NW) by lia. replace (EX + 4 * i + 8) with (EX + 4 * NW) by lia.
replace (LI + 4 * i + 12) with (LI + 4 * NW + 4) by lia. replace (EX + 4 * i + 12) with (EX + 4 * NW + 4) by lia.
replace (i + 2) with NW by lia.
apply evt_done. unfold fld_post, RFL. do 6 eexists. lazymatch type of XD with rw_cells _ _ _ (f32 ?l) => exists l end.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
split; [rewrite !length_app; cbn [length]; lia|]. split; [exact XD| exact LC].
- replace (LI + 4 * (i + 1)) with (LI + 4 * i + 4) in WL1 by lia.
ato 0xb772c. astep. chk_merge OBF 4.
astep. ato 0xb7740. astep. chk_merge OBL 4.
ato 0xb7754. astep. chk_merge OBX 4.
ato 0xb7774. astep. chk_merge OBL 4.
ato 0xb778c. astep. chk_merge OBX 4.
ato 0xb77b0. astep. sh_if.
chunk_snoc XD X0c. rewrite sbl_f32_snoc in XD. chunk_snoc XD X1c. rewrite sbl_f32_snoc in XD.
clear WL0 WL1.
replace (LI + 4 * i + 8) with (LI + 4 * (i + 2)) by lia. replace (EX + 4 * i + 8) with (EX + 4 * (i + 2)) by lia.
replace (LI + 4 * i + 12) with (LI + 4 * (i + 2) + 4) by lia. replace (EX + 4 * i + 12) with (EX + 4 * (i + 2) + 4) by lia.
replace (EX + 4 * i + 4 + 4) with (EX + 4 * (i + 2)) in XC by lia.
eapply (IH mI rest' _ fgw (i + 2)); try eassumption; try reflexivity;
try (rewrite ?length_app; cbn [length] in *; lia).
Qed.
End FLD.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X06m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma sbl_ro_cell_at : forall (m : mem) A (cs : list cell) (k : nat) (d : cell), ro_cells asegs m A cs -> (k < length cs)%nat ->
ro_cells asegs m (A + Z.of_nat (cells_size (firstn k cs))) [nth k cs d].
Proof.
intros m A cs k d H Hk. rewrite <- (firstn_skipn k cs) in H. apply ro_cells_app in H as [_ H2].
destruct (skipn k cs) as [|c r] eqn:E.
- exfalso. assert (L : length (skipn k cs) = 0%nat) by (rewrite E; reflexivity). rewrite length_skipn in L. lia.
- assert (EN : nth k cs d = c).
{ rewrite <- (firstn_skipn k cs), E. rewrite app_nth2; rewrite length_firstn; [|lia]. replace (k - Nat.min k (length cs))%nat with 0%nat by lia. reflexivity. }
rewrite EN. change (c :: r) with ([c] ++ r) in H2. apply ro_cells_app in H2 as [H3 _]. exact H3.
Qed.

Lemma sbl_e5n : forall (usp lo hb S OUT A D f sf MODE fsz FS sub LI : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs) (pad1 : list byte)
(b : bits_st bptr) (lis exs : list word) (xs3 : word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_slots usp S OUT A f sf MODE fsz v) -> v_296 v = Z_to_bv 64 sub ->
rw_cells asegs m S (sbp_hdr s a) -> sbd_subframeSize s = FS ->
rw_cells asegs m (S + 136) (sbp_cfg s pad1) -> rw_cells asegs m (S + 152) [C4 (Z_to_bv 64 1)] ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
((sbd_mode s = ModeWB /\ FS = 40) \/ (sbd_mode s = ModeUWB /\ FS = 80)) -> MODE = sbmode_struct (sbd_mode s) -> aobj asegs m MODE 216 ->
aobj asegs m (sb_sub_addr 1) 88 -> lib_consts m -> 0 <= sub < 4 ->
bits_rep asegs m A D b -> bits_ok b -> aobj asegs m A BITS_SIZEOF -> aobj asegs m D (sb_buf_size b) ->
(A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A) -> A + BITS_SIZEOF <= lo -> D + sb_buf_size b <= lo -> IMG_TOP <= A -> (S + 160 <= A \/ A + BITS_SIZEOF <= S) ->
LI = OUT + 4 * fsz + 4 * (FS * sub) -> rw_cells asegs m LI (f32 lis) -> Z.of_nat (length lis) = FS -> aobj asegs m LI (4 * FS) -> LI mod 4 = 0 -> LI + 4 * FS <= lo ->
(S + 160 <= LI \/ LI + 4 * FS <= S) -> (A + BITS_SIZEOF <= LI \/ LI + 4 * FS <= A) ->
rw_cells asegs m (hb + 32) (f32 exs) -> Z.of_nat (length exs) = FS -> aobj asegs m (hb + 32) (4 * FS) ->
client_consts m -> stk asegs m lo hb -> lo <= hb - 32 -> hb + 32 + 4 * FS <= usp + -1088 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 -> hb mod 32 = 0 ->
mem_inv asegs m -> frm0 fc ->
evt asegs (fun ms => exists (m1 : mem) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (F' : bvmap 5 word) (fc' : bv 32) (exs' : list word),
ms = MS (R_L usp hb S sub gp tp xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
xs3 (Z_to_bv 64 FS) (Z_to_bv 64 (4 * sub)) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 (S + 32)) (Z_to_bv 64 (hb + 32))
xt3 xt4 xt5 xt6) F' (Z_to_bv 64 SBL_PC_J) fc' None m1 (seg_rom asegs)
/\ munch [(A, A + BITS_SIZEOF); (hb + -32, hb); (hb + 32, hb + 32 + 4 * FS)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo hb /\ frm0 fc'
/\ bits_rep asegs m1 A D (ub b 5) /\ rw_cells asegs m1 (hb + 32) (f32 exs') /\ Z.of_nat (length exs') = FS)
(MS (R_L usp hb S sub gp tp (Z_to_bv 64 RA_sbl_memset2) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
xs3 (Z_to_bv 64 FS) (Z_to_bv 64 (4 * sub)) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 0x10184) (Z_to_bv 64 (hb + 32)) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbl_memset2)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL V296 HD EFS CFG IDC OBS S8 SPOS SOFF SLO HMO EMODE OBM OBSM LC SUB REP OK OBA OBD ASH ALO DLO ATOP SEPSA
ELI LIC LLI OBLI LI4 LILO SEPSL SEPAL EXC LEX OBEX CC ST LO HB LOS SPH U32 HB32 MI FRM.
unfold R_L, RA_sbl_memset2, SBL_PC_J in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xb7284)) with (Z_to_bv 64 0xb7284) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold IMG_TOP in ATOP. pose proof SEPSA as SEPSA'. unfold BITS_SIZEOF in SEPSA'.
pose proof ST as (STa & STb & _). pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof (munch_refl [(A, A + BITS_SIZEOF); (hb + -32, hb); (hb + 32, hb + 32 + 4 * FS)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (FSB : 40 <= FS <= 80) by (clear - HMO; lia).
assert (OF : offsh [(A, A + BITS_SIZEOF); (hb + -32, hb); (hb + 32, hb + 32 + 4 * FS)]) by (pose proof ASH as Y; clear - Y LOS LO FSB; cbn; unfold SH_LO, SH_HI, BITS_SIZEOF in *; lia).
unfold sb_slots, sha in SL. rewrite V296 in SL. unfold sbp_hdr in HD. rewrite EFS in HD. unfold sbp_cfg in CFG. unfold sha.
assert (EX8 : (hb + 32) mod 8 = 0) by (clear - HB32; Z.div_mod_to_equations; lia).
remember (hb + 32) as EX eqn:EEX.
destruct HMO as [[EMO EFS'] | [EMO EFS']]; rewrite EMO in *; cbn [sbmode_struct] in EMODE; subst FS.
- assert (ESUB : sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR ModeWB = MODE + 40) by (subst MODE; reflexivity).
rewrite ESUB in CFG.
assert (M8 : MODE mod 8 = 0) by (subst MODE; reflexivity).
pose proof (lib_const m A_sb_wb_mode LC_sb_wb_mode LC ltac:(lc_in)) as MTAB. rewrite <- EMODE in MTAB. unfold LC_sb_wb_mode in MTAB. unfold A_sb_wb_mode in EMODE.
pose proof (sbl_ro_cell_at m MODE _ 7 (C1 (Z_to_bv 8 0)) MTAB ltac:(cbn; lia)) as FGC0.
lazymatch type of FGC0 with ro_cells _ _ (MODE + ?t) [?c] => let t' := eval vm_compute in t in let c' := eval cbn [nth] in c in change t with t' in FGC0; change c with c' in FGC0 end.
pose proof (lib_const m A_wb_submode1 LC_wb_submode1 LC ltac:(lc_in)) as T1. unfold LC_wb_submode1 in T1.
cbn [sb_sub_addr Z.eqb Pos.eqb] in OBSM.
set (SM := A_wb_submode1) in *. assert (ESM : SM = 0xf03c0) by reflexivity. assert (SM8 : SM mod 8 = 0) by reflexivity. clearbody SM.
ato 0xb72b0.
rewrite sx32_small by (unfold int31; lia). ato 0xb72d0. rewrite <- ESM.
ato 0xb7300. astep.
rewrite ?EFS' in *.
ato 0xb76ac. astep.
call (speex_bits_unpack_unsigned_walk A D hb lo b 5 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP OK ltac:(lia) OBA OBD ASH ltac:(lia) LOS ltac:(lia) ALO DLO).
1: exact ST. 1: exact CC. 1: exact MI.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
change (snd (speex_bits_unpack_unsigned b 5)) with (ub b 5) in *. change (fst (speex_bits_unpack_unsigned b 5)) with (uv b 5) in *.
pose proof (ub_ok b 5 OK ltac:(lia)) as (OK1 & SZ1 & V1R). change (2 ^ 5) with 32 in V1R.
ato 0xb76c0.
destruct POST as ((rj2 & Lrj2 & OBJ) & (bs2 & DAT & Hbs2) & SIDE2). unfold bits_cells in OBJ.
assert (Lbs2 : Z.of_nat (length bs2) = sb_buf_size (ub b 5)).
{ pose proof OK1 as OK'. unfold bits_ok in OK'. rewrite Hbs2, zlength_map_unsigned in OK'. lia. }
rewrite SZ1 in Lbs2.
pose proof ALO as ALO'. unfold BITS_SIZEOF in ALO'.
destruct (stk_split asegs _ lo (hb + -16) hb PC ltac:(lia)) as [STKa STKb]. clear PC.
astep.
call (exp_specZ (hb + -16) hb).
1: exact STKb. 1: lia. 1: lia. 1: eassumption. 1: eassumption.
match goal with H : stk asegs _ (hb + -16) hb |- _ => pose proof (stk_merge asegs _ lo (hb + -16) hb STKa H ltac:(lia)) as STK3; clear H STKa end.
ato 0xb76d4.
astep. joiny 0xb76dc 0 1.
ato 0xb76e4.
ato 0xb76e8. rewrite ?sx32_small by (unfold int31; lia). ato 0xb7720.
rewrite (swrap32_small (40 * sub)) by lia. rewrite (Z.mod_small (40 * sub) 18446744073709551616) by lia. rewrite !Z.shiftl_mul_pow2 by lia.
replace (OUT + 4 * fsz + 40 * sub * 2 ^ 2) with (LI + 4 * 0) by (rewrite ELI; lia).
replace (OUT + 4 * fsz + 4 + 40 * sub * 2 ^ 2) with (LI + 4 * 0 + 4) by (rewrite ELI; lia).
replace (Z_to_bv 64 (EX + 4)) with (Z_to_bv 64 (EX + 4 * 0 + 4)) by (f_equal; lia).
replace (Z_to_bv 64 EX) with (Z_to_bv 64 (EX + 4 * 0)) by (f_equal; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch asegs _ m mc EX (4 * 40) OBEX MU (shfree_of_aobj asegs _ m EX (4 * 40) OF OBEX)) as OBEX1;
pose proof (aobj_munch asegs _ m mc LI (4 * 40) OBLI MU (shfree_of_aobj asegs _ m LI (4 * 40) OF OBLI)) as OBLI1;
let OBF0 := fresh in pose proof (aobj_sub asegs m MODE 216 (MODE + 32) 4 OBM ltac:(lia) ltac:(lia)) as OBF0; pose proof (aobj_munch asegs _ m mc (MODE + 32) 4 OBF0 MU (shfree_of_aobj asegs _ m (MODE + 32) 4 OF OBF0)) as OBFG1;
pose proof (munch_refl [(EX, EX + 4 * 40)] mc) as MUL; pose proof (wmono_refl asegs mc) as WML;
assert (XD0 : rw_cells asegs mc EX (f32 [])) by (apply rw_cells_nil; pose proof OBEX1 as (OY0 & OY1 & _); unfold APP_TOP in OY1; lia)
end.
assert (OFL : offsh [(EX, EX + 4 * 40)]) by (cbn; unfold SH_LO, SH_HI; lia).
rewrite <- (Z.add_0_r EX) in EXC at 1. replace (EX + 0) with (EX + 4 * 0) in EXC by lia.
unfold lhide in *.
call (sbl_fold_loop EX LI (MODE + 32) 40 lis _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EX8 LI4 ltac:(lia) LLI ltac:(lia)
19 _ exs [] (Z_to_bv 64 1063675494) 0 _ _ _ _ _ _
ltac:(lia) eq_refl ltac:(cbn [length]; lia) OBEX1 OBLI1 OBFG1 OFL ltac:(right; lia) ltac:(right; rewrite EMODE; lia)
MI MUL WML FRM XD0 EXC LIC FGC0).
replace (EX + 4 * 0) with EX by lia.
assert (REP2 : bits_rep asegs x38 A D (ub b 5)) by (split; [exists rj2; split; [assumption| exact OBJ]| split; [exists bs2; split; [exact DAT| assumption]| assumption]]).
apply evt_done. do 19 eexists. exists x39.
split; [unfold R_L, sha; reflexivity|].
split; [exact MU|]. split; [eassumption|]. split; [eassumption|]. split; [exact STK3|]. split; [exact PC|].
split; [exact REP2|]. split; [exact PC1| exact PC0].
- assert (ESUB : sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR ModeUWB = MODE + 40) by (subst MODE; reflexivity).
rewrite ESUB in CFG.
assert (M8 : MODE mod 8 = 0) by (subst MODE; reflexivity).
pose proof (lib_const m A_sb_uwb_mode LC_sb_uwb_mode LC ltac:(lc_in)) as MTAB. rewrite <- EMODE in MTAB. unfold LC_sb_uwb_mode in MTAB. unfold A_sb_uwb_mode in EMODE.
pose proof (sbl_ro_cell_at m MODE _ 7 (C1 (Z_to_bv 8 0)) MTAB ltac:(cbn; lia)) as FGC0.
lazymatch type of FGC0 with ro_cells _ _ (MODE + ?t) [?c] => let t' := eval vm_compute in t in let c' := eval cbn [nth] in c in change t with t' in FGC0; change c with c' in FGC0 end.
pose proof (lib_const m A_wb_submode1 LC_wb_submode1 LC ltac:(lc_in)) as T1. unfold LC_wb_submode1 in T1.
cbn [sb_sub_addr Z.eqb Pos.eqb] in OBSM.
set (SM := A_wb_submode1) in *. assert (ESM : SM = 0xf03c0) by reflexivity. assert (SM8 : SM mod 8 = 0) by reflexivity. clearbody SM.
ato 0xb72b0.
rewrite sx32_small by (unfold int31; lia). ato 0xb72d0. rewrite <- ESM.
ato 0xb7300. astep.
rewrite ?EFS' in *.
ato 0xb76ac. astep.
call (speex_bits_unpack_unsigned_walk A D hb lo b 5 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP OK ltac:(lia) OBA OBD ASH ltac:(lia) LOS ltac:(lia) ALO DLO).
1: exact ST. 1: exact CC. 1: exact MI.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
change (snd (speex_bits_unpack_unsigned b 5)) with (ub b 5) in *. change (fst (speex_bits_unpack_unsigned b 5)) with (uv b 5) in *.
pose proof (ub_ok b 5 OK ltac:(lia)) as (OK1 & SZ1 & V1R). change (2 ^ 5) with 32 in V1R.
ato 0xb76c0.
destruct POST as ((rj2 & Lrj2 & OBJ) & (bs2 & DAT & Hbs2) & SIDE2). unfold bits_cells in OBJ.
assert (Lbs2 : Z.of_nat (length bs2) = sb_buf_size (ub b 5)).
{ pose proof OK1 as OK'. unfold bits_ok in OK'. rewrite Hbs2, zlength_map_unsigned in OK'. lia. }
rewrite SZ1 in Lbs2.
pose proof ALO as ALO'. unfold BITS_SIZEOF in ALO'.
destruct (stk_split asegs _ lo (hb + -16) hb PC ltac:(lia)) as [STKa STKb]. clear PC.
astep.
call (exp_specZ (hb + -16) hb).
1: exact STKb. 1: lia. 1: lia. 1: eassumption. 1: eassumption.
match goal with H : stk asegs _ (hb + -16) hb |- _ => pose proof (stk_merge asegs _ lo (hb + -16) hb STKa H ltac:(lia)) as STK3; clear H STKa end.
ato 0xb76d4.
astep. joiny 0xb76dc 0 1.
ato 0xb76e4.
ato 0xb76e8. rewrite ?sx32_small by (unfold int31; lia). ato 0xb7720.
rewrite (swrap32_small (80 * sub)) by lia. rewrite (Z.mod_small (80 * sub) 18446744073709551616) by lia. rewrite !Z.shiftl_mul_pow2 by lia.
replace (OUT + 4 * fsz + 80 * sub * 2 ^ 2) with (LI + 4 * 0) by (rewrite ELI; lia).
replace (OUT + 4 * fsz + 4 + 80 * sub * 2 ^ 2) with (LI + 4 * 0 + 4) by (rewrite ELI; lia).
replace (Z_to_bv 64 (EX + 4)) with (Z_to_bv 64 (EX + 4 * 0 + 4)) by (f_equal; lia).
replace (Z_to_bv 64 EX) with (Z_to_bv 64 (EX + 4 * 0)) by (f_equal; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch asegs _ m mc EX (4 * 80) OBEX MU (shfree_of_aobj asegs _ m EX (4 * 80) OF OBEX)) as OBEX1;
pose proof (aobj_munch asegs _ m mc LI (4 * 80) OBLI MU (shfree_of_aobj asegs _ m LI (4 * 80) OF OBLI)) as OBLI1;
let OBF0 := fresh in pose proof (aobj_sub asegs m MODE 216 (MODE + 32) 4 OBM ltac:(lia) ltac:(lia)) as OBF0; pose proof (aobj_munch asegs _ m mc (MODE + 32) 4 OBF0 MU (shfree_of_aobj asegs _ m (MODE + 32) 4 OF OBF0)) as OBFG1;
pose proof (munch_refl [(EX, EX + 4 * 80)] mc) as MUL; pose proof (wmono_refl asegs mc) as WML;
assert (XD0 : rw_cells asegs mc EX (f32 [])) by (apply rw_cells_nil; pose proof OBEX1 as (OY0 & OY1 & _); unfold APP_TOP in OY1; lia)
end.
assert (OFL : offsh [(EX, EX + 4 * 80)]) by (cbn; unfold SH_LO, SH_HI; lia).
rewrite <- (Z.add_0_r EX) in EXC at 1. replace (EX + 0) with (EX + 4 * 0) in EXC by lia.
unfold lhide in *.
call (sbl_fold_loop EX LI (MODE + 32) 80 lis _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EX8 LI4 ltac:(lia) LLI ltac:(lia)
39 _ exs [] (Z_to_bv 64 1060320051) 0 _ _ _ _ _ _
ltac:(lia) eq_refl ltac:(cbn [length]; lia) OBEX1 OBLI1 OBFG1 OFL ltac:(right; lia) ltac:(right; rewrite EMODE; lia)
MI MUL WML FRM XD0 EXC LIC FGC0).
replace (EX + 4 * 0) with EX by lia.
assert (REP2 : bits_rep asegs x38 A D (ub b 5)) by (split; [exists rj2; split; [assumption| exact OBJ]| split; [exists bs2; split; [exact DAT| assumption]| assumption]]).
apply evt_done. do 19 eexists. exists x39.
split; [unfold R_L, sha; reflexivity|].
split; [exact MU|]. split; [eassumption|]. split; [eassumption|]. split; [exact STK3|]. split; [exact PC|].
split; [exact REP2|]. split; [exact PC1| exact PC0].
Qed.
