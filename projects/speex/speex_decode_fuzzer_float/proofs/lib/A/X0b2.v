(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require X1nu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s X05u X05t
X081 X05l X05m X09f X06d X069 X05w X063 X082 X08y X0b1 X0b0 X068 X05a
X07y X0b3 X0az.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0yr X0wl X0wn X0wm X0ys X0x2 X0wp X0yt X0zq X11l X11k X0x1 X0w7 X0yq X11n X11j.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wp OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w7 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11j.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section SbDecodeExit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis AUN_lo : allocas_unpoison_lo_contract RT.
Hypothesis AUN_nop : allocas_unpoison_nop_contract RT.

Lemma fp_local_nonclient : forall (P : mem -> Prop) (Σ : rts RT) W (m m' : mem),
fp_local IO_FP P -> munch W m m' -> (forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) USTACK_TOP x -> outside W x) -> P m -> P m'.
Proof using IO_img.
intros P Σ W m m' L MU NC Pm. apply (L m m' Pm). intros a Ha. apply MU. apply NC. right; left. exact (IO_img _ Ha).
Qed.

Theorem sbd_exit_cps : forall (Σ Σx : rts RT) (F0 : list (word * FdEntry)) (fs0 : Fs)
(ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word) (Fx : bvmap 5 word) (fcx : bv 32)
(m mX : mem) (lo S OUT STEREO A D f fh PD ND : Z) (kh : nat) (LBD : list block) (g : nat -> word) (topv ret : Z)
(d' : dec_state bptr) (b' : bits_st bptr) (ows' : list word) (stb' : list byte) (j24 j36 : list byte) (dtx : word),
let usp := bv_unsigned sp in let sf := Z.shiftr f 3 + SHB in

rt_frames RT Σx = (f, 0%nat) :: rt_frames RT Σ -> rt_live RT Σx = rt_live RT Σ -> rt_sp0 RT Σx = rt_sp0 RT Σ -> rt_pois RT Σx = rt_pois RT Σ ->
ART RT Σ m -> pois_above (rt_pois RT Σ) usp ->
(forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) usp a -> ~ f <= a < f + 64 /\ ~ sf <= a < sf + 8) ->

(forall x, In x LBD -> In (blk_addr x, blk_size x) (rt_live RT Σ)) ->
In (PD, ND) (rt_live RT Σ) -> PD <= D -> D + sb_buf_size b' <= PD + ND ->
In (fh, kh) (rt_frames RT Σ) ->
fh <= A -> A + BITS_SIZEOF <= fh + fs_size kh - 8 -> acc bsegs m A BITS_SIZEOF ->
fh <= OUT -> OUT + 8000 <= fh + fs_size kh - 8 -> acc bsegs m OUT 8000 ->
fh <= STEREO -> STEREO + 24 <= fh + fs_size kh - 8 -> acc bsegs m STEREO 24 ->

ART RT Σx mX -> mem_inv bsegs mX -> X1cn.frm0 fcx -> stk bsegs mX lo (usp + -736) ->
rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK <= usp + -736 -> usp + 16 <= USTACK_TOP -> usp mod 32 = 0 ->
rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp (dec_W IO_FP A OUT STEREO LBD) m mX -> wmono bsegs m mX ->
rw_cells bsegs mX (usp + -736) (sb_fr g) -> g 13%nat = Z_to_bv 64 sf -> g 68%nat = Z_to_bv 64 topv -> g 14%nat = Z_to_bv 64 f ->
(topv = 0 \/ (lo <= topv /\ 0 < topv <= usp + -192 /\ topv mod 8 = 0)) ->
rw_cells bsegs mX (usp + -160) (sb_saves F ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
rw_cells bsegs mX f (sb_fhdr j24 dtx j36) -> rw_cells bsegs mX sf sb_fshadow ->

DREP OUT STEREO mX S d' LBD -> (ret = 0 -> EXCREADY mX S d') ->
bits_rep bsegs mX A D b' -> bits_ok b' ->
rw_cells bsegs mX OUT (f32 ows') -> length ows' = 2000%nat -> rw_cells bsegs mX STEREO [CB 24 stb'] ->
ERR_rep mX -> (forall so, OUT_rep so m -> OUT_rep so mX) ->
cps bsegs
(ASTA RT Σx (PMfd F0 fs0)
(eq (MS (mkR xra (Z_to_bv 64 (usp + -736)) gp (Z_to_bv 64 0x638c98) xt0 xt1 xt2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736))
xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 (Z_to_bv 64 ret) xs5 xs6 xs7 (Z_to_bv 64 f) xs9 xs10 xs11 xt3 xt4 xt5 xt6)
Fx (Z_to_bv 64 0xc0458) fcx None mX (seg_rom bsegs))))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' (PMfd F0 fs0) (fun ms => exists m' (ows2 : list word) (stb2 : list byte),
ret_stL (fun _ fc' => X1cn.frm0 fc') ra sp gp (Z_to_bv 64 0x638c98) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 ret) m' ms
/\ rt_after RT Σ' usp lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp (dec_W IO_FP A OUT STEREO LBD) m m'
/\ DREP OUT STEREO m' S d' LBD /\ (ret = 0 -> EXCREADY m' S d')
/\ bits_rep bsegs m' A D b' /\ bits_ok b'
/\ rw_cells bsegs m' OUT (f32 ows2) /\ length ows2 = 2000%nat /\ rw_cells bsegs m' STEREO [CB 24 stb2]
/\ acc bsegs m' A BITS_SIZEOF /\ acc bsegs m' OUT 8000 /\ acc bsegs m' STEREO 24
/\ ERR_rep m' /\ (forall so, OUT_rep so m -> OUT_rep so m')) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σx /\ rt_pois RT Σ' = rt_pois RT Σ).
Proof using AF ERR_loc OUT_loc IO_img AUN_lo AUN_nop.
intros Σ Σx F0 fs0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 Fx fcx
m mX lo S OUT STEREO A D f fh PD ND kh LBD g topv ret d' b' ows' stb' j24 j36 dtx usp sf
FRSx LVx SPx POx ART0 POA NAF LIVE INPD PD1 PD2 INFH FA1 FA2 ACA FO1 FO2 ACO FS1 FS2 ACST
ARTX MIX FRMX STX LOW LOR SPT SPA PF WM0 FR G13 G52 G14 TOPC SV FRB FRS REPX EXRX BREPX BOKX OCX LOWSX STBX ERRX OUTX.
intros T c Hc Hk.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
pose proof (PMfd_mat_stable F0 fs0) as MST. pose proof (PMfd_fdfs_only F0 fs0) as FDO.

assert (INFX : In (f, 0%nat) (rt_frames RT Σx)) by (rewrite FRSx; left; reflexivity).
assert (INFHX : In (fh, kh) (rt_frames RT Σx)) by (rewrite FRSx; right; exact INFH).
assert (LOWX : rt_sp0 RT Σx - STACK_WIN <= lo) by (rewrite SPx; exact LOW).
assert (INPDX : In (PD, ND) (rt_live RT Σx)) by (rewrite LVx; exact INPD).
destruct (frame_below_lo RT AF Σx mX f 0%nat lo ARTX INFX LOWX) as (BF & BF0 & LOS).
pose proof (frame_facts RT AF Σx mX f 0%nat ARTX INFX) as (F1 & F64 & FIMG & _ & FHI & SHF & SHF0 & SHF1 & SHF2 & SHF3).
destruct (frame_below_lo RT AF Σx mX fh kh lo ARTX INFHX LOWX) as (BH1 & BH2 & _).
pose proof (frame_facts RT AF Σx mX fh kh ARTX INFHX) as (FP0 & FP64 & FPIMG & _ & FPHI & _ & _ & _ & _ & _).
destruct (live_below_lo RT AF Σx mX PD ND lo ARTX INPDX LOWX) as (PD0 & BLPD & _).
destruct (frame_live_apart RT AF Σx mX f 0%nat PD ND ARTX INFX INPDX) as (FLP1 & FLP2).
change (fs_size 0) with 64 in *. change (64 / 8) with 8 in *.
fold sf in SHF. rewrite <- SHF in *. rewrite SHF0 in *.
assert (FSZ : 0 <= fs_size kh) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (FS64 : fs_size kh mod 64 = 0 /\ 64 <= fs_size kh).
{ unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat kh) ltac:(lia) ltac:(lia)). split; [rewrite Z.mul_comm; apply Z_mod_mult | lia]. }
assert (CLH : forall x, fh <= x < fh + fs_size kh - 8 -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x)
by (intros x Hx; right; right; right; left; exists fh, kh; split; [exact INFH | exact Hx]).
assert (FFA : fh + fs_size kh <= f \/ f + 64 <= fh).
{ destruct FS64 as (M64 & G64). destruct (Z_le_gt_dec (f + 64) fh) as [C1|C1]; [right; exact C1|]. left.
destruct (Z_lt_le_dec f fh) as [C2|C2]; [exfalso; destruct (NAF fh (CLH fh ltac:(clear - G64; lia))) as (N1 & _); apply N1; clear - C1 C2; lia|].
destruct (Z_lt_le_dec f (fh + fs_size kh - 8)) as [C3|C3]; [exfalso; destruct (NAF f (CLH f ltac:(clear - C2 C3; lia))) as (N1 & _); apply N1; clear; lia|].
clear - C3 M64 FP64 F64. Z.div_mod_to_equations. lia. }
unfold BITS_SIZEOF in *.
assert (AFA : A + 48 <= f \/ f + 64 <= A) by (clear - FFA FA1 FA2; lia).
assert (OFA : OUT + 8000 <= f \/ f + 64 <= OUT) by (clear - FFA FO1 FO2; lia).
assert (TFA : STEREO + 24 <= f \/ f + 64 <= STEREO) by (clear - FFA FS1 FS2; lia).
assert (ASA : A + 48 <= sf \/ sf + 8 <= A) by (clear - FPHI SHF1 SHF2 FA1 FA2; unfold SH_LO, SH_HI in *; lia).
assert (OSA : OUT + 8000 <= sf \/ sf + 8 <= OUT) by (clear - FPHI SHF1 SHF2 FO1 FO2; unfold SH_LO, SH_HI in *; lia).
assert (TSA : STEREO + 24 <= sf \/ sf + 8 <= STEREO) by (clear - FPHI SHF1 SHF2 FS1 FS2; unfold SH_LO, SH_HI in *; lia).
assert (LIVEX : forall x, In x LBD -> In (blk_addr x, blk_size x) (rt_live RT Σx)) by (intros x Hx; rewrite LVx; exact (LIVE x Hx)).
assert (BGEO : forall b x, In b LBD -> blk_addr b <= x < blk_addr b + blk_size b -> x < lo /\ (x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)).
{ intros b x Hb Hx. destruct (live_below_lo RT AF Σx mX _ _ lo ARTX (LIVEX b Hb) LOWX) as (_ & B1 & _).
destruct (frame_live_apart RT AF Σx mX f 0%nat _ _ ARTX INFX (LIVEX b Hb)) as (B2 & B3).
change (fs_size 0) with 64 in B2, B3. rewrite SHF0, <- SHF in B3. clear - B1 B2 B3 Hx. lia. }
assert (LO608 : lo <= usp + -736) by (clear - LOR; unfold RT_STACK in LOR; lia).

destruct BREPX as ((rjb & Lrjb & BOBJ) & (bsb & BDAT & Hbsb) & BSIDE). unfold bits_cells in BOBJ. apply (proj1 (u8arr_rw_CB mX D bsb)) in BDAT.
assert (Lbsb : Z.of_nat (length bsb) = sb_buf_size b') by (pose proof BOKX as OK'; unfold bits_ok in OK'; rewrite Hbsb, zlength_map_unsigned in OK'; clear - OK'; lia).
assert (LOWZ : Z.of_nat (length ows') = 2000) by (rewrite LOWSX; reflexivity).
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
cps_norm. cps_hide.

cps_seg (sbd_x1 usp f sf g (Z_to_bv 64 topv)).
{ ulc. }
destruct POST as (m1 & -> & MU1 & WM1 & MI1 & FRS1).
clear FRS.
pk_munch MU1 WM1 LBD ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BGEO b x Hb Hx) as H1; clear - H1; cbn [outside]; split; [lia| exact I])
ltac:(fun x Hx => clear - Hx SHF1; cbn [outside]; split; [lia| exact I]).
unfold sb_fhdr in FRB.
assert (BDLO : D + Z.of_nat (length bsb) <= lo) by (clear - Lbsb PD2 BLPD; lia).
assert (BDF : D + Z.of_nat (length bsb) <= f \/ f + 64 <= D) by (clear - Lbsb PD1 PD2 FLP1; unfold hid in FLP1; lia).
assert (BDS : D + Z.of_nat (length bsb) <= sf \/ sf + 8 <= D) by (clear - Lbsb PD1 PD2 FLP2; unfold hid in FLP2; lia).
cps_hide.
cps_seg_post.

assert (POAX : pois_above (rt_pois RT Σx) usp) by (rewrite POx; exact POA).
assert (KX : forall (Σ2 : rts RT) (m2 : mem) (v2 r r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : word) (cc2 : config),
ASTA RT Σ2 (PMfd F0 fs0)
(eq (MS (mkR (Z_to_bv 64 RA_sbd_unpoison_x) (Z_to_bv 64 (usp + -736)) gp (Z_to_bv 64 6524056) r r0 r1 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736))
v2 r2 r3 r4 r5 r6 r7 r8 (Z_to_bv 64 sf) xs3 (Z_to_bv 64 ret) xs5 xs6 xs7 (Z_to_bv 64 f) xs9 xs10 xs11 r9 r10 r11 r12)
Fx (ret_pc (Z_to_bv 64 RA_sbd_unpoison_x)) fcx None m2 (seg_rom bsegs))) cc2 ->
rt_pois RT Σ2 = rt_pois RT Σx -> rt_live RT Σ2 = rt_live RT Σx -> rt_frames RT Σ2 = rt_frames RT Σx -> rt_sp0 RT Σ2 = rt_sp0 RT Σx ->
rt_credit RT Σ2 = rt_credit RT Σx ->
X14x.ART RT Σ2 m2 -> mem_inv bsegs m2 -> wmono bsegs m1 m2 -> stk bsegs m2 lo (usp + -736) ->
rw_cells bsegs m2 sf sb_fshadow_x -> rw_cells bsegs m2 STEREO [CB 24 stb'] -> rw_cells bsegs m2 OUT (f32 ows') ->
rw_cells bsegs m2 D [CB (length bsb) bsb] -> rw_cells bsegs m2 A (bits_cells D b' rjb) -> rw_cells bsegs m2 f (sb_fhdr j24 dtx j36) ->
rw_cells bsegs m2 (usp + -160) (sb_saves F ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) -> rw_cells bsegs m2 (usp + -736) (sb_fr g) ->
rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp (dec_W IO_FP A OUT STEREO LBD) m m2 ->
DREP OUT STEREO m2 S d' LBD -> (ret = 0 -> EXCREADY m2 S d') -> ERR_rep m2 -> (forall so, OUT_rep so m -> OUT_rep so m2) ->
realizes bsegs cc2 T).
{ clear Hc0 FRS1 STBX OCX BDAT BOBJ FRB SV FR PF REPX ERRX MI1.
repeat match goal with H : _ -> EXCREADY m1 _ _ |- _ => clear H end.
repeat match goal with H : forall so, OUT_rep so m -> OUT_rep so m1 |- _ => clear H end.
repeat match goal with H : X14x.ART RT Σx m1 |- _ => clear H end.
repeat match goal with H : stk bsegs m1 _ _ |- _ => clear H end.
intros Σ2 m2 v2 r r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 cc2 Hc PO2 LV2 FRS2 SP2 CR2 ART2 MI2 WM2 ST2 FRS1 STBX OCX BDAT BOBJ FRB SV FR PF REPX EXRX ERRX OUTX.
unfold bits_cells in BOBJ. unfold sb_fhdr in FRB.
assert (LIVE2 : forall x, In x LBD -> In (blk_addr x, blk_size x) (rt_live RT Σ2)) by (intros x Hx; rewrite LV2; exact (LIVEX x Hx)).
cps_sigma LV2 FRS2 SP2.

chunk_uncons FRB as FH.
assert (FSH : f + 64 <= SH_LO \/ SH_HI <= f) by (clear - FHI; unfold hid in FHI; unfold SH_LO, SH_HI; lia).
cps_seg (sbd_x2 usp f sf g).
{ ulc. }
destruct POST as (m3 & -> & MU3 & WM3 & MI3 & FRS3).
clear FH FRS1 FSH FRB.
pk_munch MU3 WM3 LBD ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BGEO b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia)
ltac:(fun x Hx => clear - Hx SHF1 FIMG; cbn [outside]; repeat split; lia).
cbn [map repeat] in FRS3. unfold bF5 in FRS3.
cps_seg_post.

assert (EF2 : rt_frames RT Σ2 = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRS2; exact FRSx).
assert (EL2 : rt_live RT Σ2 = rt_live RT Σ) by (rewrite LV2; exact LVx).
lazymatch goal with A : X14x.ART RT Σ2 _ |- _ => rename A into ARTR end.
cps_release_intro ARTR EF2 EL2 (fun E : rt_frames RT Σ = [] => False_ind (rt_pois RT Σ2 = []) (in_nil (eq_ind _ (fun l => In (fh, kh) l) INFH _ E))) Σ3 fl.
cps_seg (sbd_x3 usp lo f fl g).
destruct POST as (m4 & F4 & -> & MU4 & WM4 & MI4 & ST4 & FLG4).
assert (AG4 : agree_blocks bsegs m3 m4 LBD).
{ apply (agree_blocks_of_munch bsegs _ m3 m4 LBD MU4 WM4). intros b x Hb Hx. cbn [outside]. split; [| exact I]. intros Hfl. apply NAC.
right; right; left. exists (blk_addr b), (blk_size b). split; [exact (LIVE2 b Hb)| clear - Hx Hfl; lia]. }
pk_blocks AG4. clear AG4.
assert (KEEP4 : forall P, fp_local IO_FP P -> P m3 -> P m4).
{ intros P L Pm. apply (fp_local_nonclient P Σ2 _ m3 m4 L MU4); [| exact Pm]. intros x Hx. cbn [outside]. split; [| exact I]. intros Hfl. apply NAC.
replace fl with x by (clear - Hfl; lia). exact Hx. }
pk_io ERR_rep OUT_rep KEEP4. clear KEEP4.

assert (FLH : fl < fh \/ fh + fs_size kh - 8 <= fl).
{ destruct (Z_lt_dec fl fh) as [L|L]; [left; exact L|]. destruct (Z_le_dec (fh + fs_size kh - 8) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; right; left. exists fh, kh. split; [exact INFHX| clear - L G; lia]. }
assert (FLA : fl < A \/ A + 48 <= fl) by (clear - FLH FA1 FA2; lia).
assert (FLO : fl < OUT \/ OUT + 8000 <= fl) by (clear - FLH FO1 FO2; lia).
assert (FLT : fl < STEREO \/ STEREO + 24 <= fl) by (clear - FLH FS1 FS2; lia).
assert (FLD : fl < D \/ D + Z.of_nat (length bsb) <= fl).
{ destruct (Z_lt_dec fl PD) as [L|L]; [left; clear - L PD1; lia|]. destruct (Z_le_dec (PD + ND) fl) as [G|G]; [right; clear - G PD2 Lbsb; lia|]. exfalso. apply NAC.
right; right; left. exists PD, ND. split; [exact INPDX| clear - L G; lia]. }
clear FLH. cps_hide.
clear FR SV FRS3.
cps_release_done REL MU4 WM4 FLG4.

assert (OFFW : forall x, SH_LO <= x < SH_HI -> outside (dec_W IO_FP A OUT STEREO LBD) x).
{ intros x Hx. unfold dec_W. cbn [outside]. unfold BITS_SIZEOF.
split; [clear - Hx FPHI FA1 FA2 FSZ; unfold hid, SH_LO, SH_HI in *; lia|]. split; [clear - Hx FPHI FO1 FO2 FSZ; unfold hid, SH_LO, SH_HI in *; lia|].
split; [clear - Hx FPHI FS1 FS2 FSZ; unfold hid, SH_LO, SH_HI in *; lia|].
apply sb_outside_app; [exact (outside_blocks_shadow RT AF Σ m LBD x ART0 LIVE Hx)|].
apply (outside_img IO_FP x IO_img). clear - Hx. unfold SH_LO, SH_HI, SEGTOP_A in *. lia. }
apply Hk. exists Σ3.
split; [| split; [congruence|]; split; [congruence|]; split; [congruence|]; split; [congruence|];
rewrite EP, PO2; exact POx].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m4, ows', stb'.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRMX]|].
split. { split; [assumption|]. split; [exact MI4|]. split; [cps_wmono| exact ST4]. }
split; [exact PF|]. split; [exact REPX|]. split; [assumption|].
split. { split; [exists rjb; split; [exact Lrjb| exact BOBJ]|]. split; [exists bsb; split; [apply u8arr_rw_CB; exact BDAT| exact Hbsb]| exact BSIDE]. }
split; [exact BOKX|]. split; [exact OCX|]. split; [exact LOWSX|]. split; [exact STBX|].
split; [exact (acc_of_pres_fp RT AF Σ m m m4 usp _ fh kh A 48 ART0 INFH FA1 FA2 PF OFFW ACA)|].
split; [exact (acc_of_pres_fp RT AF Σ m m m4 usp _ fh kh OUT 8000 ART0 INFH FO1 FO2 PF OFFW ACO)|].
split; [exact (acc_of_pres_fp RT AF Σ m m m4 usp _ fh kh STEREO 24 ART0 INFH FS1 FS2 PF OFFW ACST)|].
split; [exact ERRX| assumption]. }

pose proof (TOPC : _ \/ _) as TOPC2. destruct TOPC2 as [TOP0 | (TOP1 & TOP2 & TOP3)].
- cps_rt (AUN_nop Σx (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1).
{ left. rewrite TOP0. reflexivity. }
intros cc2 Hc2.
cps_unpack Hc2 as (v2 & RS2).
eapply (KX Σx m1); try eassumption; try reflexivity.
apply wmono_refl.
- cps_rt (AUN_lo Σx (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 topv (usp + -192) lo).
{ intros e He. right. specialize (POAX e He). clear - POAX. lia. }
{ cps_callok. }
intros cc2 (Σ2 & Hc2 & PO2 & LV2 & FRS2 & SP2 & CR2).
cps_unpack Hc2 as (m2 & v2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ACT2).
pk_pres RT PRES2 WM2 LBD LIVEX ERR_rep OUT_rep IO_FP IO_img.
assert (PDX : pois_drop (usp + -192) (rt_pois RT Σx) = rt_pois RT Σx) by (apply pois_drop_above; eapply pois_above_le; [exact POAX| clear; lia]).
rewrite PDX in PO2.
eapply (KX Σ2 m2); try eassumption; try reflexivity.
Qed.
End SbDecodeExit.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section SbDecodeExit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis AUN_lo : allocas_unpoison_lo_contract RT.
Hypothesis AUN_nop : allocas_unpoison_nop_contract RT.

Lemma fp_local_nonclient : forall (P : mem -> Prop) (Σ : rts RT) W (m m' : mem),
fp_local IO_FP P -> munch W m m' -> (forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) USTACK_TOP x -> outside W x) -> P m -> P m'.
Proof using IO_img.
intros P Σ W m m' L MU NC Pm. apply (L m m' Pm). intros a Ha. apply MU. apply NC. right; left. exact (IO_img _ Ha).
Qed.

Theorem sbd_exit_cps : forall (Σ Σx : rts RT) (F0 : list (word * FdEntry)) (fs0 : Fs)
(ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word) (Fx : bvmap 5 word) (fcx : bv 32)
(m mX : mem) (lo S OUT STEREO A D f fh PD ND : Z) (kh : nat) (LBD : list block) (g : nat -> word) (topv ret : Z)
(d' : dec_state bptr) (b' : bits_st bptr) (ows' : list word) (stb' : list byte) (j24 j36 : list byte) (dtx : word),
let usp := bv_unsigned sp in let sf := Z.shiftr f 3 + SHB in

rt_frames RT Σx = (f, 0%nat) :: rt_frames RT Σ -> rt_live RT Σx = rt_live RT Σ -> rt_sp0 RT Σx = rt_sp0 RT Σ -> rt_pois RT Σx = rt_pois RT Σ ->
ART RT Σ m -> pois_above (rt_pois RT Σ) usp ->
(forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) usp a -> ~ f <= a < f + 64 /\ ~ sf <= a < sf + 8) ->

(forall x, In x LBD -> In (blk_addr x, blk_size x) (rt_live RT Σ)) ->
In (PD, ND) (rt_live RT Σ) -> PD <= D -> D + sb_buf_size b' <= PD + ND ->
In (fh, kh) (rt_frames RT Σ) ->
fh <= A -> A + BITS_SIZEOF <= fh + fs_size kh - 8 -> acc asegs m A BITS_SIZEOF ->
fh <= OUT -> OUT + 8000 <= fh + fs_size kh - 8 -> acc asegs m OUT 8000 ->
fh <= STEREO -> STEREO + 24 <= fh + fs_size kh - 8 -> acc asegs m STEREO 24 ->

ART RT Σx mX -> mem_inv asegs mX -> X1cn.frm0 fcx -> stk asegs mX lo (usp + -608) ->
rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK <= usp + -608 -> usp + 16 <= USTACK_TOP -> usp mod 32 = 0 ->
rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp (dec_W IO_FP A OUT STEREO LBD) m mX -> wmono asegs m mX ->
rw_cells asegs mX (usp + -608) (sb_fr g) -> g 13%nat = Z_to_bv 64 sf -> g 52%nat = Z_to_bv 64 topv ->
(topv = 0 \/ (lo <= topv /\ 0 < topv <= usp + -192 /\ topv mod 8 = 0)) ->
rw_cells asegs mX (usp + -160) (sb_saves F ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
rw_cells asegs mX f (sb_fhdr j24 dtx j36) -> rw_cells asegs mX sf sb_fshadow ->

DREP OUT STEREO mX S d' LBD -> (ret = 0 -> EXCREADY mX S d') ->
bits_rep asegs mX A D b' -> bits_ok b' ->
rw_cells asegs mX OUT (f32 ows') -> length ows' = 2000%nat -> rw_cells asegs mX STEREO [CB 24 stb'] ->
ERR_rep mX -> (forall so, OUT_rep so m -> OUT_rep so mX) ->
cps asegs
(ASTA RT Σx (PMfd F0 fs0)
(eq (MS (mkR xra (Z_to_bv 64 (usp + -608)) gp (Z_to_bv 64 0x630458) xt0 xt1 xt2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -608))
xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 (Z_to_bv 64 ret) xs5 (Z_to_bv 64 f) xs7 (Z_to_bv 64 f) xs9 xs10 xs11 xt3 xt4 xt5 xt6)
Fx (Z_to_bv 64 0xb7ed0) fcx None mX (seg_rom asegs))))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' (PMfd F0 fs0) (fun ms => exists m' (ows2 : list word) (stb2 : list byte),
ret_stL (fun _ fc' => X1cn.frm0 fc') ra sp gp (Z_to_bv 64 0x630458) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 ret) m' ms
/\ rt_after RT Σ' usp lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp (dec_W IO_FP A OUT STEREO LBD) m m'
/\ DREP OUT STEREO m' S d' LBD /\ (ret = 0 -> EXCREADY m' S d')
/\ bits_rep asegs m' A D b' /\ bits_ok b'
/\ rw_cells asegs m' OUT (f32 ows2) /\ length ows2 = 2000%nat /\ rw_cells asegs m' STEREO [CB 24 stb2]
/\ acc asegs m' A BITS_SIZEOF /\ acc asegs m' OUT 8000 /\ acc asegs m' STEREO 24
/\ ERR_rep m' /\ (forall so, OUT_rep so m -> OUT_rep so m')) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σx /\ rt_pois RT Σ' = rt_pois RT Σ).
Proof using AF ERR_loc OUT_loc IO_img AUN_lo AUN_nop.
intros Σ Σx F0 fs0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 Fx fcx
m mX lo S OUT STEREO A D f fh PD ND kh LBD g topv ret d' b' ows' stb' j24 j36 dtx usp sf
FRSx LVx SPx POx ART0 POA NAF LIVE INPD PD1 PD2 INFH FA1 FA2 ACA FO1 FO2 ACO FS1 FS2 ACST
ARTX MIX FRMX STX LOW LOR SPT SPA PF WM0 FR G13 G52 TOPC SV FRB FRS REPX EXRX BREPX BOKX OCX LOWSX STBX ERRX OUTX.
intros T c Hc Hk.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
pose proof (PMfd_mat_stable F0 fs0) as MST. pose proof (PMfd_fdfs_only F0 fs0) as FDO.

assert (INFX : In (f, 0%nat) (rt_frames RT Σx)) by (rewrite FRSx; left; reflexivity).
assert (INFHX : In (fh, kh) (rt_frames RT Σx)) by (rewrite FRSx; right; exact INFH).
assert (LOWX : rt_sp0 RT Σx - STACK_WIN <= lo) by (rewrite SPx; exact LOW).
assert (INPDX : In (PD, ND) (rt_live RT Σx)) by (rewrite LVx; exact INPD).
destruct (frame_below_lo RT AF Σx mX f 0%nat lo ARTX INFX LOWX) as (BF & BF0 & LOS).
pose proof (frame_facts RT AF Σx mX f 0%nat ARTX INFX) as (F1 & F64 & FIMG & _ & FHI & SHF & SHF0 & SHF1 & SHF2 & SHF3).
destruct (frame_below_lo RT AF Σx mX fh kh lo ARTX INFHX LOWX) as (BH1 & BH2 & _).
pose proof (frame_facts RT AF Σx mX fh kh ARTX INFHX) as (FP0 & FP64 & FPIMG & _ & FPHI & _ & _ & _ & _ & _).
destruct (live_below_lo RT AF Σx mX PD ND lo ARTX INPDX LOWX) as (PD0 & BLPD & _).
destruct (frame_live_apart RT AF Σx mX f 0%nat PD ND ARTX INFX INPDX) as (FLP1 & FLP2).
change (fs_size 0) with 64 in *. change (64 / 8) with 8 in *.
fold sf in SHF. rewrite <- SHF in *. rewrite SHF0 in *.
assert (FSZ : 0 <= fs_size kh) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (FS64 : fs_size kh mod 64 = 0 /\ 64 <= fs_size kh).
{ unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat kh) ltac:(lia) ltac:(lia)). split; [rewrite Z.mul_comm; apply Z_mod_mult | lia]. }
assert (CLH : forall x, fh <= x < fh + fs_size kh - 8 -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x)
by (intros x Hx; right; right; right; left; exists fh, kh; split; [exact INFH | exact Hx]).
assert (FFA : fh + fs_size kh <= f \/ f + 64 <= fh).
{ destruct FS64 as (M64 & G64). destruct (Z_le_gt_dec (f + 64) fh) as [C1|C1]; [right; exact C1|]. left.
destruct (Z_lt_le_dec f fh) as [C2|C2]; [exfalso; destruct (NAF fh (CLH fh ltac:(clear - G64; lia))) as (N1 & _); apply N1; clear - C1 C2; lia|].
destruct (Z_lt_le_dec f (fh + fs_size kh - 8)) as [C3|C3]; [exfalso; destruct (NAF f (CLH f ltac:(clear - C2 C3; lia))) as (N1 & _); apply N1; clear; lia|].
clear - C3 M64 FP64 F64. Z.div_mod_to_equations. lia. }
unfold BITS_SIZEOF in *.
assert (AFA : A + 48 <= f \/ f + 64 <= A) by (clear - FFA FA1 FA2; lia).
assert (OFA : OUT + 8000 <= f \/ f + 64 <= OUT) by (clear - FFA FO1 FO2; lia).
assert (TFA : STEREO + 24 <= f \/ f + 64 <= STEREO) by (clear - FFA FS1 FS2; lia).
assert (ASA : A + 48 <= sf \/ sf + 8 <= A) by (clear - FPHI SHF1 SHF2 FA1 FA2; unfold SH_LO, SH_HI in *; lia).
assert (OSA : OUT + 8000 <= sf \/ sf + 8 <= OUT) by (clear - FPHI SHF1 SHF2 FO1 FO2; unfold SH_LO, SH_HI in *; lia).
assert (TSA : STEREO + 24 <= sf \/ sf + 8 <= STEREO) by (clear - FPHI SHF1 SHF2 FS1 FS2; unfold SH_LO, SH_HI in *; lia).
assert (LIVEX : forall x, In x LBD -> In (blk_addr x, blk_size x) (rt_live RT Σx)) by (intros x Hx; rewrite LVx; exact (LIVE x Hx)).
assert (BGEO : forall b x, In b LBD -> blk_addr b <= x < blk_addr b + blk_size b -> x < lo /\ (x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)).
{ intros b x Hb Hx. destruct (live_below_lo RT AF Σx mX _ _ lo ARTX (LIVEX b Hb) LOWX) as (_ & B1 & _).
destruct (frame_live_apart RT AF Σx mX f 0%nat _ _ ARTX INFX (LIVEX b Hb)) as (B2 & B3).
change (fs_size 0) with 64 in B2, B3. rewrite SHF0, <- SHF in B3. clear - B1 B2 B3 Hx. lia. }
assert (LO608 : lo <= usp + -608) by (clear - LOR; unfold RT_STACK in LOR; lia).

destruct BREPX as ((rjb & Lrjb & BOBJ) & (bsb & BDAT & Hbsb) & BSIDE). unfold bits_cells in BOBJ. apply (proj1 (u8arr_rw_CB mX D bsb)) in BDAT.
assert (Lbsb : Z.of_nat (length bsb) = sb_buf_size b') by (pose proof BOKX as OK'; unfold bits_ok in OK'; rewrite Hbsb, zlength_map_unsigned in OK'; clear - OK'; lia).
assert (LOWZ : Z.of_nat (length ows') = 2000) by (rewrite LOWSX; reflexivity).
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
cps_norm. cps_hide.

cps_seg (sbd_x1 usp f sf g (Z_to_bv 64 topv)).
{ ulc. }
destruct POST as (m1 & -> & MU1 & WM1 & MI1 & FRS1).
clear FRS.
pk_munch MU1 WM1 LBD ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BGEO b x Hb Hx) as H1; clear - H1; cbn [outside]; split; [lia| exact I])
ltac:(fun x Hx => clear - Hx SHF1; cbn [outside]; split; [lia| exact I]).
unfold sb_fhdr in FRB.
assert (BDLO : D + Z.of_nat (length bsb) <= lo) by (clear - Lbsb PD2 BLPD; lia).
assert (BDF : D + Z.of_nat (length bsb) <= f \/ f + 64 <= D) by (clear - Lbsb PD1 PD2 FLP1; unfold hid in FLP1; lia).
assert (BDS : D + Z.of_nat (length bsb) <= sf \/ sf + 8 <= D) by (clear - Lbsb PD1 PD2 FLP2; unfold hid in FLP2; lia).
cps_hide.
cps_seg_post.

assert (POAX : pois_above (rt_pois RT Σx) usp) by (rewrite POx; exact POA).
assert (KX : forall (Σ2 : rts RT) (m2 : mem) (v2 r r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : word) (cc2 : config),
ASTA RT Σ2 (PMfd F0 fs0)
(eq (MS (mkR (Z_to_bv 64 RA_sbd_unpoison_x) (Z_to_bv 64 (usp + -608)) gp (Z_to_bv 64 6489176) r r0 r1 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -608))
v2 r2 r3 r4 r5 r6 r7 r8 (Z_to_bv 64 sf) xs3 (Z_to_bv 64 ret) xs5 (Z_to_bv 64 f) xs7 (Z_to_bv 64 f) xs9 xs10 xs11 r9 r10 r11 r12)
Fx (ret_pc (Z_to_bv 64 RA_sbd_unpoison_x)) fcx None m2 (seg_rom asegs))) cc2 ->
rt_pois RT Σ2 = rt_pois RT Σx -> rt_live RT Σ2 = rt_live RT Σx -> rt_frames RT Σ2 = rt_frames RT Σx -> rt_sp0 RT Σ2 = rt_sp0 RT Σx ->
rt_credit RT Σ2 = rt_credit RT Σx ->
X0ec.ART RT Σ2 m2 -> mem_inv asegs m2 -> wmono asegs m1 m2 -> stk asegs m2 lo (usp + -608) ->
rw_cells asegs m2 sf sb_fshadow_x -> rw_cells asegs m2 STEREO [CB 24 stb'] -> rw_cells asegs m2 OUT (f32 ows') ->
rw_cells asegs m2 D [CB (length bsb) bsb] -> rw_cells asegs m2 A (bits_cells D b' rjb) -> rw_cells asegs m2 f (sb_fhdr j24 dtx j36) ->
rw_cells asegs m2 (usp + -160) (sb_saves F ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) -> rw_cells asegs m2 (usp + -608) (sb_fr g) ->
rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp (dec_W IO_FP A OUT STEREO LBD) m m2 ->
DREP OUT STEREO m2 S d' LBD -> (ret = 0 -> EXCREADY m2 S d') -> ERR_rep m2 -> (forall so, OUT_rep so m -> OUT_rep so m2) ->
realizes asegs cc2 T).
{ clear Hc0 FRS1 STBX OCX BDAT BOBJ FRB SV FR PF REPX ERRX MI1.
repeat match goal with H : _ -> EXCREADY m1 _ _ |- _ => clear H end.
repeat match goal with H : forall so, OUT_rep so m -> OUT_rep so m1 |- _ => clear H end.
repeat match goal with H : X0ec.ART RT Σx m1 |- _ => clear H end.
repeat match goal with H : stk asegs m1 _ _ |- _ => clear H end.
intros Σ2 m2 v2 r r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 cc2 Hc PO2 LV2 FRS2 SP2 CR2 ART2 MI2 WM2 ST2 FRS1 STBX OCX BDAT BOBJ FRB SV FR PF REPX EXRX ERRX OUTX.
unfold bits_cells in BOBJ. unfold sb_fhdr in FRB.
assert (LIVE2 : forall x, In x LBD -> In (blk_addr x, blk_size x) (rt_live RT Σ2)) by (intros x Hx; rewrite LV2; exact (LIVEX x Hx)).
cps_sigma LV2 FRS2 SP2.

chunk_uncons FRB as FH.
assert (FSH : f + 64 <= SH_LO \/ SH_HI <= f) by (clear - FHI; unfold hid in FHI; unfold SH_LO, SH_HI; lia).
cps_seg (sbd_x2 usp f sf).
{ ulc. }
destruct POST as (m3 & -> & MU3 & WM3 & MI3 & FRS3).
clear FH FRS1 FSH FRB.
pk_munch MU3 WM3 LBD ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BGEO b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia)
ltac:(fun x Hx => clear - Hx SHF1 FIMG; cbn [outside]; repeat split; lia).
cbn [map repeat] in FRS3. unfold bF5 in FRS3.
cps_seg_post.

assert (EF2 : rt_frames RT Σ2 = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRS2; exact FRSx).
assert (EL2 : rt_live RT Σ2 = rt_live RT Σ) by (rewrite LV2; exact LVx).
lazymatch goal with A : X0ec.ART RT Σ2 _ |- _ => rename A into ARTR end.
cps_release_intro ARTR EF2 EL2 (fun E : rt_frames RT Σ = [] => False_ind (rt_pois RT Σ2 = []) (in_nil (eq_ind _ (fun l => In (fh, kh) l) INFH _ E))) Σ3 fl.
cps_seg (sbd_x3 usp lo f fl g).
destruct POST as (m4 & F4 & -> & MU4 & WM4 & MI4 & ST4 & FLG4).
assert (AG4 : agree_blocks asegs m3 m4 LBD).
{ apply (agree_blocks_of_munch asegs _ m3 m4 LBD MU4 WM4). intros b x Hb Hx. cbn [outside]. split; [| exact I]. intros Hfl. apply NAC.
right; right; left. exists (blk_addr b), (blk_size b). split; [exact (LIVE2 b Hb)| clear - Hx Hfl; lia]. }
pk_blocks AG4. clear AG4.
assert (KEEP4 : forall P, fp_local IO_FP P -> P m3 -> P m4).
{ intros P L Pm. apply (fp_local_nonclient P Σ2 _ m3 m4 L MU4); [| exact Pm]. intros x Hx. cbn [outside]. split; [| exact I]. intros Hfl. apply NAC.
replace fl with x by (clear - Hfl; lia). exact Hx. }
pk_io ERR_rep OUT_rep KEEP4. clear KEEP4.

assert (FLH : fl < fh \/ fh + fs_size kh - 8 <= fl).
{ destruct (Z_lt_dec fl fh) as [L|L]; [left; exact L|]. destruct (Z_le_dec (fh + fs_size kh - 8) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; right; left. exists fh, kh. split; [exact INFHX| clear - L G; lia]. }
assert (FLA : fl < A \/ A + 48 <= fl) by (clear - FLH FA1 FA2; lia).
assert (FLO : fl < OUT \/ OUT + 8000 <= fl) by (clear - FLH FO1 FO2; lia).
assert (FLT : fl < STEREO \/ STEREO + 24 <= fl) by (clear - FLH FS1 FS2; lia).
assert (FLD : fl < D \/ D + Z.of_nat (length bsb) <= fl).
{ destruct (Z_lt_dec fl PD) as [L|L]; [left; clear - L PD1; lia|]. destruct (Z_le_dec (PD + ND) fl) as [G|G]; [right; clear - G PD2 Lbsb; lia|]. exfalso. apply NAC.
right; right; left. exists PD, ND. split; [exact INPDX| clear - L G; lia]. }
clear FLH. cps_hide.
clear FR SV FRS3.
cps_release_done REL MU4 WM4 FLG4.

assert (OFFW : forall x, SH_LO <= x < SH_HI -> outside (dec_W IO_FP A OUT STEREO LBD) x).
{ intros x Hx. unfold dec_W. cbn [outside]. unfold BITS_SIZEOF.
split; [clear - Hx FPHI FA1 FA2 FSZ; unfold hid, SH_LO, SH_HI in *; lia|]. split; [clear - Hx FPHI FO1 FO2 FSZ; unfold hid, SH_LO, SH_HI in *; lia|].
split; [clear - Hx FPHI FS1 FS2 FSZ; unfold hid, SH_LO, SH_HI in *; lia|].
apply sb_outside_app; [exact (outside_blocks_shadow RT AF Σ m LBD x ART0 LIVE Hx)|].
apply (outside_img IO_FP x IO_img). clear - Hx. unfold SH_LO, SH_HI, SEGTOP_A in *. lia. }
apply Hk. exists Σ3.
split; [| split; [congruence|]; split; [congruence|]; split; [congruence|]; split; [congruence|];
rewrite EP, PO2; exact POx].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m4, ows', stb'.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRMX]|].
split. { split; [assumption|]. split; [exact MI4|]. split; [cps_wmono| exact ST4]. }
split; [exact PF|]. split; [exact REPX|]. split; [assumption|].
split. { split; [exists rjb; split; [exact Lrjb| exact BOBJ]|]. split; [exists bsb; split; [apply u8arr_rw_CB; exact BDAT| exact Hbsb]| exact BSIDE]. }
split; [exact BOKX|]. split; [exact OCX|]. split; [exact LOWSX|]. split; [exact STBX|].
split; [exact (acc_of_pres_fp RT AF Σ m m m4 usp _ fh kh A 48 ART0 INFH FA1 FA2 PF OFFW ACA)|].
split; [exact (acc_of_pres_fp RT AF Σ m m m4 usp _ fh kh OUT 8000 ART0 INFH FO1 FO2 PF OFFW ACO)|].
split; [exact (acc_of_pres_fp RT AF Σ m m m4 usp _ fh kh STEREO 24 ART0 INFH FS1 FS2 PF OFFW ACST)|].
split; [exact ERRX| assumption]. }

pose proof (TOPC : _ \/ _) as TOPC2. destruct TOPC2 as [TOP0 | (TOP1 & TOP2 & TOP3)].
- cps_rt (AUN_nop Σx (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1).
{ left. rewrite TOP0. reflexivity. }
intros cc2 Hc2.
cps_unpack Hc2 as (v2 & RS2).
eapply (KX Σx m1); try eassumption; try reflexivity.
apply wmono_refl.
- cps_rt (AUN_lo Σx (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 topv (usp + -192) lo).
{ intros e He. right. specialize (POAX e He). clear - POAX. lia. }
{ cps_callok. }
intros cc2 (Σ2 & Hc2 & PO2 & LV2 & FRS2 & SP2 & CR2).
cps_unpack Hc2 as (m2 & v2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ACT2).
pk_pres RT PRES2 WM2 LBD LIVEX ERR_rep OUT_rep IO_FP IO_img.
assert (PDX : pois_drop (usp + -192) (rt_pois RT Σx) = rt_pois RT Σx) by (apply pois_drop_above; eapply pois_above_le; [exact POAX| clear; lia]).
rewrite PDX in PO2.
eapply (KX Σ2 m2); try eassumption; try reflexivity.
Qed.
End SbDecodeExit.
