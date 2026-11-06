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
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require X00a X000.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s X05u X05t
X081 X05l X05m X09f X06d X069 X05w X063 X082 X08y X0b1 X0b0 X068 X05a
X0ay X0bf X07y X0b3 X0az X0b2 X0ar X07l X08b X0b5.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0r9 X0qz.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0yr X0wl X0wn X0wm X0ys X0x2 X0wp X0yt X0zq X11l X11k X0x1 X0w7 X11i X122 X0yq X11n X11o X11j X11m X11c X0yd X0z2 X11q.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X0j9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X09f OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X06d.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wp OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w7 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11i OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X122 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yd OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0z2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11q.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac simpl_sizes ::=
rewrite ?X06d.sb_cells_size, ?cells_size_sb_fhdr, ?cells_size_sb_fshadow, ?cells_size_sb_fr, ?cells_size_sb_saves, ?cells_size_sb_slots,
?cells_size_sbp_hdr, ?cells_size_sbp_ptrs, ?cells_size_sbp_cfg, ?app_length, ?cells_size_app, ?cells_size_f32, ?length_f32;
cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length, ?cells_size_f32, ?length_f32; cbn [length].

Definition sbd_inv_bytes (s : sbd_state bptr) (b1 : bits_st bptr) : list Z :=
match submode_at (sbm_submodes (sbd_mode s)) (sbw_id b1) with
| Some _ => []
| None => if sbw_id b1 =? 0 then [] else notify_bytes MSG_INVALID_MODE
end.

Section SbDecodeWph.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis IO_ssp : forall y, in_ranges IO_FP y -> ~ (X0r9.SSP_GUARD <= y < X0r9.SSP_GUARD + 8).
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis AF_ERRV : forall Σ m, ART RT Σ m -> acc bsegs m STDERR_VAR 8.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.
Hypothesis FPL : fprintf_lib_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis APO : alloca_poison_contract RT.
Hypothesis AUN_lo : allocas_unpoison_lo_contract RT.
Hypothesis AUN_nop : allocas_unpoison_nop_contract RT.
Hypothesis MEMS : memset_icontract RT e_asan_memset.
Hypothesis QMF16 : forall N, N = 320 \/ N = 640 -> qmf_synth_cps16 RT N.
Hypothesis LOST : sb_decode_lost_cps RT.
Hypothesis LOOP : sb_subframe_cps RT.

Theorem sbd_wph_cps : forall (Σ Σx : rts RT) (F0 : list (word * FdEntry)) (fs0 : Fs)
(ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (Fx : bvmap 5 word) (fcx : bv 32)
(m mX : mem) (lo S OUT STEREO A D f fh PD ND : Z) (kh : nat) (LBD LBL : list block) (g : nat -> word)
(s : sbd_state bptr) (a : sb_addrs) (j : sb_junk) (low low3 : dec_state bptr) (b b1 : bits_st bptr) (ows : list word) (stb : list byte)
(j24 j36 : list byte) (dtx : Z) (q1 q' : pst) (ret : Z) (d' : dec_state bptr) (b' : bits_st bptr),
let usp := bv_unsigned sp in let sf := Z.shiftr f 3 + SHB in

sb_outcome s low3 b1 q1 ret d' b' q' ->
dec_depth low3 = dec_depth low -> dec_mode low3 = sbm_nb_mode (sbd_mode s) -> dec_nestedR low3 -> (dec_depth low <= 2)%nat ->
sb_owner b1 = sb_owner b -> sb_chars b1 = sb_chars b -> sb_buf_size b1 = sb_buf_size b ->
(forall d : dec_state bptr, dec_depth d = dec_depth low -> ctl2_cps_at RT d) ->

LBD = sb_blocks s S a ++ LBL -> List.NoDup (map blk_id LBD) -> blocks_al8 LBD -> S mod 8 = 0 -> 0 < S -> sb_inv s -> sb_junk_ok s j ->
match sbd_innov_save s with None => True | Some k => k = 2 * sbd_frame_size s end ->

rt_frames RT Σx = (f, 0%nat) :: rt_frames RT Σ -> rt_live RT Σx = rt_live RT Σ -> rt_sp0 RT Σx = rt_sp0 RT Σ -> rt_pois RT Σx = rt_pois RT Σ ->
rt_credit RT Σ - 1 - 2 * (Z.of_nat (dec_depth low) - 1) - dec_credit low <= rt_credit RT Σx <= rt_credit RT Σ - 1 ->
1 + 4 * (Z.of_nat (dec_depth low) - 1) + dec_credit low <= rt_credit RT Σ ->
(length (rt_frames RT Σ) + Datatypes.S (dec_frames low) <= FRAMES_MAX)%nat ->

ART RT Σ m -> pois_above (rt_pois RT Σ) usp ->
(forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) usp a -> ~ f <= a < f + 64 /\ ~ sf <= a < sf + 8) ->
(forall x, In x LBD -> In (blk_addr x, blk_size x) (rt_live RT Σ)) ->
In (PD, ND) (rt_live RT Σ) -> PD <= D -> D + sb_buf_size b1 <= PD + ND -> (forall x, In x LBD -> blk_addr x <> PD) ->
In (fh, kh) (rt_frames RT Σ) ->
fh <= A -> A + BITS_SIZEOF <= fh + fs_size kh - 8 -> acc bsegs m A BITS_SIZEOF -> A mod 4 = 0 ->
fh <= OUT -> OUT + 8000 <= fh + fs_size kh - 8 -> acc bsegs m OUT 8000 -> OUT mod 4 = 0 ->
fh <= STEREO -> STEREO + 24 <= fh + fs_size kh - 8 -> acc bsegs m STEREO 24 -> STEREO mod 4 = 0 ->
hidp (A + BITS_SIZEOF <= OUT \/ OUT + 8000 <= A) -> hidp (A + BITS_SIZEOF <= STEREO \/ STEREO + 24 <= A) -> hidp (OUT + 8000 <= STEREO \/ STEREO + 24 <= OUT) ->
fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + SB_OWN_STACK + dec_stack low <= usp -> usp + 16 <= USTACK_TOP -> usp mod 32 = 0 ->

ART RT Σx mX -> mem_inv bsegs mX -> X1cn.frm0 fcx -> stk bsegs mX lo (usp + -736) ->
rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp (dec_W IO_FP A OUT STEREO LBD) m mX -> wmono bsegs m mX ->
rw_cells bsegs mX (usp + -736) (sb_fr g) ->
g 0%nat = Z_to_bv 64 0 -> g 16%nat = Z_to_bv 64 (OUT + 4 * sbd_frame_size s) -> g 13%nat = Z_to_bv 64 sf -> g 34%nat = Z_to_bv 64 (S + 20) ->
g 33%nat = Z_to_bv 64 (Z.shiftr (S + 20) 3 + SHB) -> g 46%nat = Z_to_bv 64 A -> g 54%nat = Z_to_bv 64 0 ->
g 14%nat = Z_to_bv 64 f -> g 68%nat = Z_to_bv 64 0 ->
g 19%nat = Z_to_bv 64 f -> g 67%nat = Z_to_bv 64 f -> g 40%nat = Z_to_bv 64 S -> g 61%nat = Z_to_bv 64 1 -> g 62%nat = Z_to_bv 64 OUT ->
rw_cells bsegs mX (usp + -160) (sb_saves F ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
rw_cells bsegs mX f (sb_fhdr j24 (Z_to_bv 64 dtx) j36) -> (dtx = 0 \/ dtx = 1) -> rw_cells bsegs mX sf sb_fshadow ->
rw_cells bsegs mX S (SBCELLS s a OUT j) -> sb_bufs bsegs mX a j ->
DREP OUT STEREO mX (a_low a) low3 LBL -> EXCREADY mX (a_low a) low3 ->
bits_rep bsegs mX A D b1 -> bits_ok b1 ->
rw_cells bsegs mX OUT (f32 ows) -> length ows = 2000%nat -> rw_cells bsegs mX STEREO [CB 24 stb] ->
acc bsegs mX A BITS_SIZEOF -> acc bsegs mX OUT 8000 -> acc bsegs mX STEREO 24 ->
ERR_rep mX -> (forall so, OUT_rep so m -> OUT_rep so mX) -> io_ssp mX ->
cpsE bsegs
(ASTA RT Σx (PMfd F0 fs0)
(eq (MS (R_P usp S A f (sbmode_struct (sbd_mode s)) gp (Z_to_bv 64 0x638c98) (Z_to_bv 64 RA_sbd_ctl103) xt0 xt1 xt2 (Z_to_bv 64 0) xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 (f + 32)) (Z_to_bv 64 0) s11 xt3 xt4 xt5 xt6) Fx (ret_pc (Z_to_bv 64 RA_sbd_ctl103)) fcx None mX (seg_rom bsegs))))
(Spec.X1nu.evw 2 (sbd_inv_bytes s b1))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' (PMfd F0 fs0) (fun ms => exists m' (ows' : list word) (stb' : list byte),
ret_stL (fun _ fc' => X1cn.frm0 fc') ra sp gp (Z_to_bv 64 0x638c98) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 ret) m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (dec_W IO_FP A OUT STEREO LBD) m m'
/\ DREP OUT STEREO m' S d' LBD /\ (ret = 0 -> EXCREADY m' S d')
/\ bits_rep bsegs m' A D b' /\ bits_ok b'
/\ rw_cells bsegs m' OUT (f32 ows') /\ length ows' = 2000%nat /\ rw_cells bsegs m' STEREO [CB 24 stb']
/\ acc bsegs m' A BITS_SIZEOF /\ acc bsegs m' OUT 8000 /\ acc bsegs m' STEREO 24
/\ ERR_rep m' /\ (forall so, OUT_rep so m -> OUT_rep so m')) c
/\ -2 <= ret <= 0 /\ dec_depth d' = dec_depth (DecSB s low) /\ dec_mode d' = dec_mode (DecSB s low) /\ dec_nestedR d'
/\ sb_owner b' = sb_owner b /\ sb_chars b' = sb_chars b /\ sb_buf_size b' = sb_buf_size b
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ - dec_credit (DecSB s low) <= rt_credit RT Σ' <= rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).
Proof using AF ERR_loc OUT_loc IO_img IO_ssp AF_DRV AF_ERRV AF_LIB FPL APO AUN_lo AUN_nop MEMS QMF16 LOST LOOP.
intros Σ Σx F0 fs0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 Fx fcx
m mX lo S OUT STEREO A D f fh PD ND kh LBD LBL g s a j low low3 b b1 ows stb j24 j36 dtx q1 q' ret d' b' usp sf
PZ DL3 NM3 NEST3 DEPL OWN1 CHR1 BSZ1 CTL3 ELBD NDUP LAL8 S8 SPOS INV JOK ISV
EFX ELX ESX EPX CBX CRD FRM ART0 POA NAF LIVE INPD PD1 PD2 PDB INFH FA1 FA2 ACA AAL FO1 FO2 ACO OAL FS1 FS2 ACST SAL HAO HAS HOS FD2
LOW LOR SPT SPA ARTX MIX FRMX STX PF WM0 FR G0 G10 G13 G26 G27 G38 G45 G51 G52 G19 G67 G40 G61 G62 SV FRB DTXV FRS X BUFS RLOW EXR BREP BOK OC LOWS STB ACAX ACOX ACTX ERRX OUTK SSPX.
intros T c Hc Hk.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
pose proof (PMfd_mat_stable F0 fs0) as MST. pose proof (PMfd_fdfs_only F0 fs0) as FDO.
assert (DSP : 0 <= dec_stack low) by (clear; induction low; cbn [dec_stack]; unfold NBDEC_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK; lia).
assert (LO736 : lo <= usp - 736) by (clear - LOR DSP; unfold RT_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in LOR; lia).

assert (INL : In (S, 160) (rt_live RT Σ)).
{ specialize (LIVE (sbd_blk s, S, SBSTATE_SIZEOF)). rewrite ELBD in LIVE. exact (LIVE ltac:(left; reflexivity)). }
assert (INLX : In (S, 160) (rt_live RT Σx)) by (rewrite ELX; exact INL).
assert (INPDX : In (PD, ND) (rt_live RT Σx)) by (rewrite ELX; exact INPD).
assert (INF : In (f, 0%nat) (rt_frames RT Σx)) by (rewrite EFX; left; reflexivity).
assert (INFHX : In (fh, kh) (rt_frames RT Σx)) by (rewrite EFX; right; exact INFH).
assert (LOWX : rt_sp0 RT Σx - STACK_WIN <= lo) by (rewrite ESX; exact LOW).
destruct (live_below_lo RT AF Σx mX S 160 lo ARTX INLX LOWX) as (_ & BS1 & LOS).
pose proof (af_live_small RT AF Σx mX S 160 ARTX INLX ltac:(lia)) as SIMG.
destruct (live_below_lo RT AF Σx mX PD ND lo ARTX INPDX LOWX) as (PDP & BLPD & _).
destruct (frame_below_lo RT AF Σx mX fh kh lo ARTX INFHX LOWX) as (BF1 & BF2 & _).
pose proof (frame_facts RT AF Σx mX fh kh ARTX INFHX) as (FP0 & FP64 & FPIMG & _ & FPHI & _).
destruct (frame_below_lo RT AF Σx mX f 0%nat lo ARTX INF LOWX) as (BF & BF0 & _).
pose proof (frame_facts RT AF Σx mX f 0%nat ARTX INF) as (F1 & F64 & FIMG & _ & FHI & SHF & SHF0 & SHF1 & SHF2 & SHF3).
change (fs_size 0) with 64 in *. change (64 / 8) with 8 in *.
fold sf in SHF. rewrite <- SHF in *.
assert (FSZ : 0 <= fs_size kh) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (FS64 : fs_size kh mod 64 = 0 /\ 64 <= fs_size kh).
{ unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat kh) ltac:(lia) ltac:(lia)). split; [rewrite Z.mul_comm; apply Z_mod_mult | lia]. }
assert (FPHI' : fh + fs_size kh <= SH_LO \/ SH_HI <= fh) by (clear - FPHI; unfold SH_LO, SH_HI; lia).
assert (FHI' : f + 64 <= SH_LO \/ SH_HI <= f) by (clear - FHI; unfold SH_LO, SH_HI; lia).
assert (CLH : forall x, fh <= x < fh + fs_size kh - 8 -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x)
by (intros x Hx; right; right; right; left; exists fh, kh; split; [exact INFH | exact Hx]).
assert (FFA : fh + fs_size kh <= f \/ f + 64 <= fh).
{ destruct FS64 as (M64 & G64). destruct (Z_le_gt_dec (f + 64) fh) as [C1|C1]; [right; exact C1|]. left.
destruct (Z_lt_le_dec f fh) as [C2|C2]; [exfalso; destruct (NAF fh (CLH fh ltac:(clear - G64; lia))) as (N1 & _); apply N1; clear - C1 C2; lia|].
destruct (Z_lt_le_dec f (fh + fs_size kh - 8)) as [C3|C3]; [exfalso; destruct (NAF f (CLH f ltac:(clear - C2 C3; lia))) as (N1 & _); apply N1; clear; lia|].
clear - C3 M64 FP64 F64. Z.div_mod_to_equations. lia. }
unfold BITS_SIZEOF in *.
destruct (frame_live_apart RT AF Σx mX f 0%nat S 160 ARTX INF INLX) as (SFA & SFS).
change (fs_size 0) with 64 in SFA, SFS. rewrite SHF0 in SFS.
destruct (frame_live_apart RT AF Σx mX fh kh S 160 ARTX INFHX INLX) as (SFH & _).
assert (HAO' : A + 48 <= OUT \/ OUT + 8000 <= A) by (clear - HAO; unfold hidp in HAO; exact HAO).
assert (HAS' : A + 48 <= STEREO \/ STEREO + 24 <= A) by (clear - HAS; unfold hidp in HAS; exact HAS).
assert (HOS' : OUT + 8000 <= STEREO \/ STEREO + 24 <= OUT) by (clear - HOS; unfold hidp in HOS; exact HOS).
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
set (LALL := tl (sb_blocks s S a) ++ LBL).
assert (LALLD : forall x, In x LALL -> In x LBD) by (intros x Hx; rewrite ELBD; cbn [sb_blocks tl app] in Hx |- *; right; exact Hx).
assert (LIVEA : forall x, In x LALL -> In (blk_addr x, blk_size x) (rt_live RT Σx)) by (intros x Hx; rewrite ELX; exact (LIVE x (LALLD x Hx))).
assert (LIVEL : forall x, In x LBL -> In (blk_addr x, blk_size x) (rt_live RT Σx)) by (intros x Hx; rewrite ELX; apply LIVE; rewrite ELBD; apply in_app_iff; right; exact Hx).
assert (LIVED : forall x, In x LBD -> In (blk_addr x, blk_size x) (rt_live RT Σx)) by (intros x Hx; rewrite ELX; exact (LIVE x Hx)).
assert (BOUT : forall bk x, In bk LALL -> blk_addr bk <= x < blk_addr bk + blk_size bk ->
x < lo /\ (x < S \/ S + 160 <= x) /\ (x < fh \/ fh + fs_size kh <= x) /\ (x < PD \/ PD + ND <= x) /\ (x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)
/\ (x < 65536 \/ 6664192 <= x)).
{ intros bk x Hb Hx. pose proof (LIVEA bk Hb) as LB.
destruct (live_below_lo RT AF Σx mX _ _ lo ARTX LB LOWX) as (_ & B1 & _).
destruct (frame_live_apart RT AF Σx mX fh kh _ _ ARTX INFHX LB) as (B2 & _).
destruct (frame_live_apart RT AF Σx mX f 0%nat _ _ ARTX INF LB) as (B5 & B6). change (fs_size 0) with 64 in B5, B6. rewrite SHF0, <- SHF in B6.
pose proof (live_facts RT AF Σx mX _ _ ARTX LB) as (_ & _ & B7 & _).
assert (NE : blk_addr bk <> S).
{ pose proof NDUP as ND'. rewrite ELBD in ND'. cbn [sb_blocks app map blk_id blk_addr fst snd] in ND'. apply List.NoDup_cons_iff in ND'. destruct ND' as [NI _].
intros E. apply NI. rewrite <- E. unfold LALL in Hb. cbn [sb_blocks tl app] in Hb. exact (in_map blk_id _ _ Hb). }
pose proof (live_apart RT AF Σx mX _ _ _ _ ARTX LB INLX NE) as B3.
pose proof (live_apart RT AF Σx mX _ _ _ _ ARTX LB INPDX (PDB bk (LALLD bk Hb))) as B4.
unfold SEGTOP_A in B7. clear - B1 B2 B3 B4 B5 B6 B7 Hx. lia. }
assert (OUTB : forall x, (lo <= x \/ S <= x < S + 160 \/ fh <= x < fh + fs_size kh \/ PD <= x < PD + ND \/ f <= x < f + 64 \/ sf <= x < sf + 8
\/ 65536 <= x < 6664192) -> outside (blocks_ivs LBL) x).
{ intros x Hx. apply outside_blocks_ivs. intros bk Hb Hin.
pose proof (BOUT bk x ltac:(unfold LALL; apply in_app_iff; right; exact Hb) Hin) as H1. clear - Hx H1. lia. }
assert (APL : forall bk x, In bk (tl (sb_blocks s S a)) -> blk_addr bk <= x < blk_addr bk + blk_size bk -> outside (blocks_ivs LBL) x).
{ intros bk x Hb Hx. apply outside_blocks_ivs. intros b2 Hb2 Hin.
assert (NE : blk_addr bk <> blk_addr b2).
{ pose proof NDUP as ND'. rewrite ELBD, map_app in ND'. apply (NoDup_app_in_neq _ _ (blk_id bk) (blk_id b2) ND'); [apply in_map; cbn [sb_blocks tl] in Hb |- *; right; exact Hb| apply in_map; exact Hb2]. }
pose proof (live_apart RT AF Σx mX _ _ _ _ ARTX (LIVEA bk ltac:(unfold LALL; apply in_app_iff; left; exact Hb)) (LIVEL b2 Hb2) NE) as AP.
clear - AP Hx Hin. lia. }
pose proof (proj2 (decst_rep_pos _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RLOW)) as SL8.

pose proof (af_client_consts RT AF Σx mX ARTX) as CCX.
pose proof (AF_LIB Σx mX ARTX) as LCX.
assert (OBA : aobj bsegs mX A 48) by (split; [clear - FA1 FP0; lia|]; split; [clear - FA2 BF1 LO736 SPT; unfold APP_TOP, USTACK_TOP in *; lia| exact ACAX]).
destruct (af_acc_live RT AF Σx mX PD ND ARTX INPDX) as (_ & ACPD).
assert (OBD : aobj bsegs mX D (sb_buf_size b1))
by (split; [clear - PDP PD1; lia|]; split; [clear - PD2 BLPD LO736 SPT; unfold APP_TOP, USTACK_TOP in *; lia|
exact (acc_sub bsegs mX PD ND D (sb_buf_size b1) ACPD PD1 PD2)]).
assert (ASH : A + 48 <= SH_LO \/ SH_HI <= A) by (clear - FPHI' FA1 FA2; lia).
assert (AIMG : IMG_TOP_B <= A) by (clear - FPIMG FA1; unfold IMG_TOP_B, SEGTOP_A in *; lia).
assert (ALO : A + 48 <= lo) by (clear - FA2 BF1; lia).
assert (DLO : D + sb_buf_size b1 <= lo) by (clear - PD2 BLPD; lia).
assert (LO672 : lo <= usp + -736 - 64) by (clear - LOR DSP; unfold RT_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
pose proof (live_facts RT AF Σx mX S 160 ARTX INLX) as (_ & _ & _ & SHI).
assert (SOFF : S + 160 <= SH_LO \/ SH_HI <= S) by (clear - SHI; unfold SH_LO, SH_HI in *; lia).
assert (SPH : usp < 2^63) by (clear - SPT; unfold USTACK_TOP in *; lia).
destruct (af_acc_live RT AF Σx mX S 160 ARTX INLX) as (_ & ACS).
assert (OBS : aobj bsegs mX S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO736 SPT; unfold APP_TOP, USTACK_TOP in *; lia| exact ACS]).
pose proof INV as (IMODE & IFS & IFFS & ISFS & INS & ILPC & IFST & _ & _ & IES & IID & IISV).
sb_unpack X as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_w5 usp lo S OUT A D f (sbmode_struct (sbd_mode s)) g s b1 (sj_pad1 j) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
FR CFG IES OBS S8 SPOS BS1 SOFF BREP BOK OBA OBD ASH AIMG ALO DLO STX LO672 LOS SPH CCX MIX).
cps_norm. cps_hide.
destruct POST as (m8 & xra8 & xt08 & xt18 & xt28 & xa18 & xa28 & xa38 & xa48 & xa58 & xa68 & xa78 & xt38 & xt48 & xt58 & xt68
& -> & MU8 & WM8 & MI8 & ST8 & FR8 & BREP8 & BOK8 & BSZ8 & IDR).
clear FR BREP HD FST PT LE SEED CFG IDC PAD CCX LCX OBA OBD OBS ACS ACPD.
assert (EXR' : 0 = 0 -> EXCREADY mX (a_low a) low3) by (intros _; exact EXR). clear EXR.
Time pk_munch_all MU8 WM8 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LO672 FA1 FA2; unfold BITS_SIZEOF; cbn [outside]; split; [lia| split; [lia| exact I]])
ltac:(fun x Hx => clear - Hx FA1 FPIMG LO672 LOS; unfold BITS_SIZEOF; cbn [outside]; split; [lia| split; [lia| exact I]]).
unfold BITS_SIZEOF in MU8. unfold dec_W, BITS_SIZEOF in PF.
Time cps_seg_post.

assert (OF8 : offsh [(A, A + 48); (usp + -800, usp + -160)]) by (cbn [offsh]; clear - ASH LOS LO672; unfold hid, SH_LO, SH_HI in *; lia).
assert (ACC8 : forall o n, acc bsegs mX o n -> 0 <= o -> o + n <= 140737488355328 -> acc bsegs m8 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch bsegs _ mX m8 o n (conj H0 (conj H1 H)) MU8 (shfree_of_offsh _ o n OF8 H0 H1)))). }
assert (ACA8 : acc bsegs m8 A 48) by (apply ACC8; [exact ACAX| clear - FA1 FP0; lia| clear - FA2 BF1 LO736 SPT; lia]).
assert (ACO8 : acc bsegs m8 OUT 8000) by (apply ACC8; [exact ACOX| clear - FO1 FP0; lia| clear - FO2 BF1 LO736 SPT; lia]).
assert (ACT8 : acc bsegs m8 STEREO 24) by (apply ACC8; [exact ACTX| clear - FS1 FP0; lia| clear - FS2 BF1 LO736 SPT; lia]).
clear ACAX ACOX ACTX ACC8.
assert (SSP8 : io_ssp mX -> io_ssp m8).
{ intros H. apply (sbd_io_ssp_agree mX m8 H (AF_DRV Σx m8 ART)). intros a0 Ha. apply MU8. unfold X0r9.SSP_GUARD in Ha. cbn [outside].
clear - Ha FA1 FPIMG LO672 LOS. split; [lia| split; [lia| exact I]]. }
apply SSP8 in SSPX. clear SSP8.

apply sb_pieces_iff in X. destruct X as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
destruct (af_acc_live RT AF Σx m8 S 160 ART INLX) as (_ & ACS8).
assert (OBS8 : aobj bsegs m8 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO736 SPT; unfold APP_TOP; lia| exact ACS8]).
pose proof (AF_LIB Σx m8 ART) as LC8.
assert (OBM : aobj bsegs m8 (sbmode_struct (sbd_mode s)) 216).
{ destruct IMODE as [E|E]; rewrite E; cbn [sbmode_struct]; (apply (aobj_lit RT AF Σx m8 _ 216 ART);
[ unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_sb_wb_mode, A_sb_uwb_mode; lia | unfold A_sb_wb_mode, A_sb_uwb_mode, APP_TOP; lia]). }
assert (SLO8 : S + 160 <= usp + -736) by (clear - BS1 LO736; lia).
assert (SHL : 17594333495296 <= usp + -736) by (clear - LOS LO736; lia).
Time cps_seg (sbd_w6 usp S OUT A f (sbmode_struct (sbd_mode s)) (sbw_id b1) (fupds g [(47%nat, Z_to_bv 64 (S + 144)); (48%nat, Z_to_bv 64 (S + 152))]) s (sj_pad1 j)
(Z_to_bv 64 (sbd_submodeID s)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
FR8 ltac:(cbn [fupds Nat.eqb]; reflexivity) ltac:(cbn [fupds Nat.eqb]; reflexivity) ltac:(gslot) CFG IDC OBS8 S8 SPOS SLO8 SOFF SIMG IMODE eq_refl OBM LC8 IDR SHL SPH MI8).
destruct POST as (m9 & xa09 & xa19 & xa29 & -> & MU9 & WM9 & MI9 & IDC9).
clear IDC.
destruct BREP8 as ((rj8 & Lrj8 & BOBJ8) & (bs8 & BDAT8 & Hbs8) & BSIDE8). unfold bits_cells in BOBJ8. apply (proj1 (u8arr_rw_CB m8 D bs8)) in BDAT8.
assert (Lbs8 : Z.of_nat (length bs8) = sb_buf_size b1) by (pose proof BOK8 as OK'; unfold bits_ok in OK'; rewrite Hbs8, zlength_map_unsigned, BSZ8 in OK'; clear - OK'; lia).
assert (BD8 : D + Z.of_nat (length bs8) <= lo) by (rewrite Lbs8; exact DLO).
Time pk_munch_all MU9 WM9 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1; cbn [outside]; split; [lia| exact I])
ltac:(fun x Hx => clear - Hx SIMG; unfold SEGTOP_A in *; cbn [outside]; split; [lia| exact I]).
assert (OUTS : forall x, outside (blocks_ivs LBD) x -> ~ (S <= x < S + 160)).
{ intros x Ho. rewrite ELBD in Ho. cbn [sb_blocks app blocks_ivs map outside blk_addr blk_size fst snd] in Ho. destruct Ho as [Ho _]. unfold SBSTATE_SIZEOF in Ho. exact Ho. }
assert (ART9 : X14x.ART RT Σx m9).
{ apply (af_frame RT AF Σx m8 m9 lo ART LOWX); [| exact WM9]. intros a0 Ha. apply MU9. cbn [outside]. split; [| exact I].
intros Hin. apply Ha. right; right; left. exists S, 160. split; [exact INLX | clear - Hin; lia]. }
assert (PF9 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m9).
{ apply (pres_fp_trans _ _ _ _ m m8 m9 PF). apply (pres_fp_of_munch _ _ _ _ _ m8 m9 MU9). intros x Hx Ho. cbn [outside] in Ho |- *.
destruct Ho as (_ & _ & _ & Ho). apply sb_outside_app_inv in Ho. destruct Ho as [Hb _]. split; [intros Hin; apply (OUTS x Hb); clear - Hin; lia | exact I]. }
clear PF. rename PF9 into PF.
assert (SPDN : S <> PD) by (apply (PDB (sbd_blk s, S, SBSTATE_SIZEOF)); rewrite ELBD; left; reflexivity).
pose proof (live_apart RT AF Σx m8 S 160 PD ND ART INLX INPDX SPDN) as SPD.
assert (BDS : D + Z.of_nat (length bs8) <= S \/ S + 160 <= D) by (clear - SPD PD1 PD2 Lbs8; lia).
Time seg_transport m8 m9 MU9 WM9.
clear ART. rename ART9 into ART.

assert (OF9 : offsh [(S + 152, S + 156)]) by (cbn [offsh]; clear - SOFF; unfold hid, SH_LO, SH_HI in *; lia).
assert (ACC9 : forall o n, acc bsegs m8 o n -> 0 <= o -> o + n <= 140737488355328 -> acc bsegs m9 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch bsegs _ m8 m9 o n (conj H0 (conj H1 H)) MU9 (shfree_of_offsh _ o n OF9 H0 H1)))). }
assert (ACA9 : acc bsegs m9 A 48) by (apply ACC9; [exact ACA8| clear - FA1 FP0; lia| clear - FA2 BF1 LO736 SPT; lia]).
assert (ACO9 : acc bsegs m9 OUT 8000) by (apply ACC9; [exact ACO8| clear - FO1 FP0; lia| clear - FO2 BF1 LO736 SPT; lia]).
assert (ACT9 : acc bsegs m9 STEREO 24) by (apply ACC9; [exact ACT8| clear - FS1 FP0; lia| clear - FS2 BF1 LO736 SPT; lia]).
clear ACA8 ACO8 ACT8 ACC9.
assert (SSP9 : io_ssp m8 -> io_ssp m9).
{ intros H. apply (sbd_io_ssp_agree m8 m9 H (AF_DRV Σx m9 ART)). intros a0 Ha. apply MU9. unfold X0r9.SSP_GUARD in Ha. cbn [outside].
clear - Ha SIMG. unfold SEGTOP_A in *. split; [lia| exact I]. }
apply SSP9 in SSPX. clear SSP9.

set (id := sbw_id b1) in *.
set (sI := set_sbd_submodeID s id).
assert (X9 : rw_cells bsegs m9 S (SBCELLS sI a OUT j)).
{ apply sb_pieces_iff. exact (conj HD (conj FST (conj PT (conj LE (conj SEED (conj CFG (conj IDC9 PAD))))))). }
clear HD FST PT LE SEED CFG IDC9 PAD.
assert (INV1 : sb_inv sI).
{ destruct INV as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12). unfold sb_inv. cbn [sI set_sbd_submodeID sbd_mode sbd_frame_size sbd_full_frame_size
sbd_subframeSize sbd_nbSubframes sbd_lpcSize sbd_first sbd_sampling_rate sbd_lpc_enh_enabled sbd_encode_submode sbd_submodeID sbd_innov_save].
refine (conj I1 (conj I2 (conj I3 (conj I4 (conj I5 (conj I6 (conj I7 (conj I8 (conj I9 (conj I10 (conj _ I12))))))))))). clear - IDR. lia. }
assert (JOK1 : sb_junk_ok sI j) by (exact JOK).
assert (ELBD1 : LBD = sb_blocks sI S a ++ LBL) by (exact ELBD).
unfold sb_outcome in PZ. cbv zeta in PZ. fold id sI in PZ.
destruct (submode_at (sbm_submodes (sbd_mode s)) id) as [sm|] eqn:ESM.
2: destruct (id =? 0) eqn:EID.

3: {
destruct PZ as (-> & -> & -> & _).
assert (EB : sbd_inv_bytes s b1 = notify_bytes MSG_INVALID_MODE) by (unfold sbd_inv_bytes; fold id; rewrite ESM, EID; reflexivity).
rewrite EB.
assert (EV : sb_id_valid (sbd_mode s) id = false) by (unfold sb_id_valid; rewrite ESM, EID; reflexivity).
rewrite EV in Hc.
pose proof (AF_DRV Σx m9 ART) as ((GOTE & VARE) & _).
assert (OBV : aobj bsegs m9 SB_STDERR_VAR 8) by (split; [unfold SB_STDERR_VAR; lia|]; split; [unfold SB_STDERR_VAR, APP_TOP; lia| exact (AF_ERRV Σx m9 ART)]).
cps_seg (sbd_w7 usp S OUT A f (sbmode_struct (sbd_mode s)) STDERR_FILE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OBV GOTE VARE MI9).
subst ms.

rewrite <- sb_msg_invalid_unsigned, <- sb_fpl_notify_bytes.
change (Spec.X1nu.evw 2 (fpl_msg FLnotify sb_msg_invalid 0)) with (SpecA.X1rn.evw 2 (fpl_msg FLnotify sb_msg_invalid 0)).
assert (EU608 : bv_unsigned (Z_to_bv 64 (usp + -736)) = usp + -736) by (apply unsigned_lit; clear - SPT LO736 LOS; lia).
cps_rtE (FPL Σx F0 fs0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m9 FLnotify SB_FMT_NOTIFY SB_MSG_INVALID 0 sb_msg_invalid STDERR_FILE lo).
{ intros E; discriminate E. }
{ unfold SB_FMT_NOTIFY. cbn [fpl_fmts In]. right; right; right; left; reflexivity. }
{ exists 51. split; [unfold ACC_LITS, SB_MSG_INVALID; cbn [In]; repeat (first [left; reflexivity | right])| vm_compute; intros XX; discriminate XX]. }
{ exact (sb_msg_invalid_at m9 MI9). }
{ exact sb_msg_invalid_nonul. }
{ unfold call_ok. rewrite EU608. split; [exact ST8|]. split; [exact LOWX|]. split; [clear - LOR DSP; unfold RT_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia|].
split; [clear - SPT; unfold USTACK_TOP in *; lia| clear - SPA; Z.div_mod_to_equations; lia]. }
{ rewrite EU608. apply (pois_above_le _ usp); [rewrite EPX; exact POA | clear; lia]. }
intros cf10 Hc10.
Time cps_unpack_lib Hc10 as (rv & m10 & RS10 & (ART10 & MI10 & WM10 & ST10) & PRES10 & ERR10 & OUT10).
Ltac tr1 PRES WM H tacA tacO :=
lazymatch type of PRES with
| rt_pres_fp ?live ?frames ?sp ?W ?m ?m' =>
lazymatch type of H with
| rw_cells bsegs m ?A0 ?cs =>
let H' := fresh "T" in
assert (H' : rw_cells bsegs m' A0 cs)
by (apply (rw_cells_agree bsegs m m' A0 cs H);
[ apply (agree_of_pres_fp live frames sp W m m' _ PRES); let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; cps_sizes Hx; split; [ tacA x Hx | tacO x Hx ]
| exact WM ]);
clear H; rename H' into H
end
end.
assert (LOWZ : Z.of_nat (length ows) = 2000) by (rewrite LOWS; reflexivity).
assert (CLF : forall x, fh <= x < fh + fs_size kh - 8 -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -736) x)
by (intros x Hx; right; right; right; left; exists fh, kh; split; [exact INFHX| exact Hx]).
assert (CLS : forall x, usp + -736 <= x < usp -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -736) x)
by (intros x Hx; left; clear - Hx SPT; unfold USTACK_TOP in *; lia).
assert (CLL : forall p n x, In (p, n) (rt_live RT Σx) -> p <= x < p + n -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -736) x)
by (intros p n x Hp Hx; right; right; left; exists p, n; split; [exact Hp| exact Hx]).
assert (CLF0 : forall x, f <= x < f + 56 -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -736) x)
by (intros x Hx; right; right; right; left; exists f, 0%nat; split; [exact INF| change (fs_size 0) with 64; lia]).
assert (CLSF : forall x, sf <= x < sf + 8 -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -736) x)
by (intros x Hx; right; right; right; right; exists f, 0%nat; split; [exact INF| change (fs_size 0) with 64; rewrite <- SHF, SHF0; lia]).
assert (OIO : forall x, (x < 65536 \/ 6664192 <= x) -> outside IO_FP x) by (intros x Hx; apply (outside_img IO_FP x IO_img); unfold SEGTOP_A; exact Hx).
tr1 PRES10 WM10 OC ltac:(fun x Hx => apply CLF; clear - Hx FO1 FO2 LOWZ; lia) ltac:(fun x Hx => apply OIO; clear - Hx FO1 FPIMG; unfold SEGTOP_A in *; lia).
tr1 PRES10 WM10 STB ltac:(fun x Hx => apply CLF; clear - Hx FS1 FS2; lia) ltac:(fun x Hx => apply OIO; clear - Hx FS1 FPIMG; unfold SEGTOP_A in *; lia).
tr1 PRES10 WM10 BOBJ8 ltac:(fun x Hx => apply CLF; clear - Hx FA1 FA2; lia) ltac:(fun x Hx => apply OIO; clear - Hx FA1 FPIMG; unfold SEGTOP_A in *; lia).
tr1 PRES10 WM10 BDAT8 ltac:(fun x Hx => apply (CLL PD ND x INPDX); clear - Hx PD1 PD2 Lbs8; lia)
ltac:(fun x Hx => apply OIO; pose proof (live_facts RT AF Σx m9 PD ND ART INPDX) as (_ & _ & IM & _); clear - Hx IM PD1 PD2 Lbs8; unfold SEGTOP_A in *; lia).
tr1 PRES10 WM10 FR8 ltac:(fun x Hx => apply CLS; clear - Hx; lia) ltac:(fun x Hx => apply OIO; clear - Hx LO736 LOS; lia).
tr1 PRES10 WM10 SV ltac:(fun x Hx => apply CLS; clear - Hx; lia) ltac:(fun x Hx => apply OIO; clear - Hx LO736 LOS; lia).
tr1 PRES10 WM10 X9 ltac:(fun x Hx => apply (CLL S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => apply OIO; clear - Hx SIMG; unfold SEGTOP_A in *; lia).
tr1 PRES10 WM10 FRB ltac:(fun x Hx => apply CLF0; clear - Hx; lia) ltac:(fun x Hx => apply OIO; clear - Hx FIMG; unfold SEGTOP_A in *; lia).
tr1 PRES10 WM10 FRS ltac:(fun x Hx => apply CLSF; clear - Hx; lia) ltac:(fun x Hx => apply OIO; clear - Hx SHF1; lia).
cps_ret RS10.

assert (AG10 : agree_blocks bsegs m9 m10 LALL).
{ apply (agree_blocks_of_pres_fp RT Σx _ _ _ m9 m10 LALL PRES10 WM10); [exact LIVEA|].
intros bk x Hb Hx. apply OIO. pose proof (BOUT bk x Hb Hx) as H1. clear - H1. tauto. }
unfold LALL in AG10. pk_all AG10. clear AG10.
assert (SHO : forall o n, fh <= o -> o + n <= fh + fs_size kh -> forall i, 0 <= i < n -> outside IO_FP (shad (o + i))).
{ intros o n H1 H2 i Hi. apply OIO. right. unfold shad, SHB. assert (0 <= (o + i) / 8) by (apply Z.div_pos; lia). lia. }
assert (FH8 : fh mod 8 = 0) by (clear - FP64; Z.div_mod_to_equations; lia).
assert (FK8 : fs_size kh mod 8 = 0) by (destruct FS64 as (M64 & _); clear - M64; Z.div_mod_to_equations; lia).
assert (ACA10 : acc bsegs m10 A 48)
by (apply (acc_pres_fp_frame _ _ _ _ m9 m10 fh kh A 48 PRES10 INFHX FH8 FK8 ltac:(lia) FA1 ltac:(lia) (SHO A 48 FA1 ltac:(lia)) ACA9)).
assert (ACO10 : acc bsegs m10 OUT 8000)
by (apply (acc_pres_fp_frame _ _ _ _ m9 m10 fh kh OUT 8000 PRES10 INFHX FH8 FK8 ltac:(lia) FO1 ltac:(lia) (SHO OUT 8000 FO1 ltac:(lia)) ACO9)).
assert (ACT10 : acc bsegs m10 STEREO 24)
by (apply (acc_pres_fp_frame _ _ _ _ m9 m10 fh kh STEREO 24 PRES10 INFHX FH8 FK8 ltac:(lia) FS1 ltac:(lia) (SHO STEREO 24 FS1 ltac:(lia)) ACT9)).
assert (SSP10 : io_ssp m10).
{ apply (sbd_io_ssp_agree m9 m10 SSPX (AF_DRV Σx m10 ART10)). intros a0 Ha. apply PRES10; [right; left; exact (sbd_ssp_static _ Ha)|].
apply X0qz.outside_of_not_in_ranges'. intros Hin. exact (IO_ssp _ Hin Ha). }
assert (PF10 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m10).
{ apply (pres_fp_trans _ _ _ _ m m9 m10 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σx) (rt_frames RT Σx) (usp + -736) _ m9 m10 PRES10).
- intros e He. rewrite ELX. exact He.
- intros e He. rewrite EFX. right. exact He.
- clear; lia.
- intros x Hx Ho. cbn [outside] in Ho. destruct Ho as (_ & _ & _ & Ho). apply sb_outside_app_inv in Ho. exact (proj2 Ho). }
clear PF ACA9 ACO9 ACT9 SSPX ERRX PRES10. rename PF10 into PF.
assert (OUTK10 : forall so, OUT_rep so m -> OUT_rep so m10) by (intros so H; exact (OUT10 so (OUTK so H))). clear OUTK OUT10.

cps_seg (sbd_w8 usp S OUT A f (sbmode_struct (sbd_mode s)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
subst ms.
assert (REPX : DREP OUT STEREO m10 S (DecSB sI low3) LBD).
{ cbn [decst_rep]. exists a, j, LBL. split; [exact ELBD1|]. split; [exact S8|]. split; [exact SPOS|]. split; [exact INV1|]. split; [exact JOK1|].
split; [exact X9|]. split; [exact BUFS|]. exists OUT. exact RLOW. }
assert (BREPX : bits_rep bsegs m10 A D (sbw_bits b1)).
{ split; [exists rj8; split; [exact Lrj8| unfold bits_cells; exact BOBJ8]|].
split; [exists bs8; split; [apply (proj2 (u8arr_rw_CB m10 D bs8)); exact BDAT8| exact Hbs8]| exact BSIDE8]. }
assert (PD2X : D + sb_buf_size (sbw_bits b1) <= PD + ND) by (rewrite BSZ8; exact PD2).
assert (WMX : wmono bsegs m m10) by (eapply wmono_trans; [exact WM0|]; eapply wmono_trans; [exact WM8|]; eapply wmono_trans; [exact WM9| exact WM10]).
cps_rt (sbd_exit_cps RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AUN_lo AUN_nop Σ Σx F0 fs0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m m10 lo S OUT STEREO A D f fh PD ND kh LBD
(fupds g [(47%nat, Z_to_bv 64 (S + 144)); (48%nat, Z_to_bv 64 (S + 152))]) 0 (-2) (DecSB sI low3) (sbw_bits b1) ows stb j24 j36 (Z_to_bv 64 dtx)
EFX ELX ESX EPX ART0 POA NAF LIVE INPD PD1 PD2X INFH FA1 FA2 ACA FO1 FO2 ACO FS1 FS2 ACST ART10 MI10 ltac:(auto) ST10 LOW
ltac:(clear - LOR DSP; unfold RT_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia) SPT SPA PF WMX FR8
ltac:(cbn [fupds Nat.eqb]; exact G13) ltac:(cbn [fupds Nat.eqb]; exact G52) ltac:(cbn [fupds Nat.eqb]; exact G51)
(or_introl eq_refl) SV FRB FRS REPX (fun E => False_ind _ ltac:(clear - E; lia)) BREPX BOK8 OC LOWS STB ERR10 OUTK10).
intros c' (Σ' & Hc' & E1 & E2 & E3 & E4 & E5).
apply Hk. exists Σ'. split; [exact Hc'|].
pose proof (bkeep_sbw b1) as (K1 & K2 & K3).
cbn [dec_depth dec_mode dec_nestedR dec_credit sI set_sbd_submodeID sbd_mode].
split; [clear; lia|]. split; [rewrite DL3; reflexivity|]. split; [reflexivity|]. split; [split; [exact NM3| exact NEST3]|].
split; [rewrite K2; exact OWN1|]. split; [rewrite K1; exact CHR1|]. split; [rewrite K3; exact BSZ1|].
split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [| exact E5].
rewrite E4. pose proof (dec_depth_pos low) as DP. clear - CBX DP. lia. }
2: {
destruct PZ as (-> & -> & -> & _).
assert (EB : sbd_inv_bytes s b1 = []) by (unfold sbd_inv_bytes; fold id; rewrite ESM, EID; reflexivity).
rewrite EB. apply rz_emit_nil.
assert (EV : sb_id_valid (sbd_mode s) id = true) by (unfold sb_id_valid; rewrite EID; reflexivity).
rewrite EV in Hc.

destruct (af_acc_live RT AF Σx m9 S 160 ART INLX) as (_ & ACS9).
assert (OBS9 : aobj bsegs m9 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO736 SPT; unfold APP_TOP; lia| exact ACS9]).
pose proof (AF_LIB Σx m9 ART) as LC9.
assert (OBM9 : aobj bsegs m9 (sbmode_struct (sbd_mode s)) 216).
{ destruct IMODE as [E|E]; rewrite E; cbn [sbmode_struct]; (apply (aobj_lit RT AF Σx m9 _ 216 ART);
[ unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_sb_wb_mode, A_sb_uwb_mode; lia | unfold A_sb_wb_mode, A_sb_uwb_mode, APP_TOP; lia]). }
sb_unpack X9 as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_m usp S OUT A f (sbmode_struct (sbd_mode s)) id (fupds g [(47%nat, Z_to_bv 64 (S + 144)); (48%nat, Z_to_bv 64 (S + 152))]) s (sj_pad1 j)
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR8 ltac:(gslot) CFG IDC OBS9 S8 SPOS SLO8 SOFF IMODE eq_refl OBM9 LC9 IDR SHL SPH MI9).
destruct POST as (m11 & xa011 & xa111 & xa211 & xa311 & xa411 & -> & MU11 & WM11 & MI11 & FR11).
match goal with H : ASTA _ _ _ _ _ |- _ => rewrite ESM in H end.
clear FR8 HD FST PT LE SEED CFG IDC PAD OBS9 ACS9 LC9.
Time pk_munch_all MU11 WM11 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LO736; cbn [outside]; split; [lia| exact I])
ltac:(fun x Hx => clear - Hx LO736 LOS; cbn [outside]; split; [lia| exact I]).
Time cps_seg_post.
match goal with H : X14x.ART RT Σx m11 |- _ => rename H into ART11 end.
assert (OF11 : offsh [(usp + -736, usp + -160)]) by (cbn [offsh]; clear - LOS LO736; unfold SH_LO, SH_HI in *; lia).
assert (ACC11 : forall o n, acc bsegs m9 o n -> 0 <= o -> o + n <= 140737488355328 -> acc bsegs m11 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch bsegs _ m9 m11 o n (conj H0 (conj H1 H)) MU11 (shfree_of_offsh _ o n OF11 H0 H1)))). }
assert (ACA11 : acc bsegs m11 A 48) by (apply ACC11; [exact ACA9| clear - FA1 FP0; lia| clear - FA2 BF1 LO736 SPT; lia]).
assert (ACO11 : acc bsegs m11 OUT 8000) by (apply ACC11; [exact ACO9| clear - FO1 FP0; lia| clear - FO2 BF1 LO736 SPT; lia]).
assert (ACT11 : acc bsegs m11 STEREO 24) by (apply ACC11; [exact ACT9| clear - FS1 FP0; lia| clear - FS2 BF1 LO736 SPT; lia]).
assert (SSP11 : io_ssp m11).
{ apply (sbd_io_ssp_agree m9 m11 SSPX (AF_DRV Σx m11 ART11)). intros a0 Ha. apply MU11. unfold X0r9.SSP_GUARD in Ha. cbn [outside].
clear - Ha LO736 LOS. split; [lia| exact I]. }
clear ACA9 ACO9 ACT9 ACC11 SSPX OBM9.

destruct (af_acc_live RT AF Σx m11 S 160 ART11 INLX) as (_ & ACS11).
assert (OBS11 : aobj bsegs m11 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO736 SPT; unfold APP_TOP; lia| exact ACS11]).
sb_unpack X9 as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
assert (FSV : sbd_frame_size s = 160 \/ sbd_frame_size s = 320) by (rewrite IFS; destruct IMODE as [E|E]; rewrite E; cbn; [left| right]; reflexivity).
assert (ISVR : match sbd_innov_save sI with None => True | Some k => 0 <= k <= 2000 end)
by (cbn [sI set_sbd_submodeID sbd_innov_save]; destruct (sbd_innov_save s); [rewrite ISV; clear - FSV; lia| exact I]).
assert (FFR : 0 <= sbd_full_frame_size sI <= 640) by (cbn [sI set_sbd_submodeID sbd_full_frame_size]; rewrite IFFS; clear - FSV; lia).
cps_seg (sbd_n1 usp S OUT A f (sbmode_struct (sbd_mode s)) _ sI a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR11 ltac:(gslot) ltac:(gslot) HD PT OBS11 S8 SPOS ltac:(clear - BS1 LO736 SPT; lia)
ltac:(clear - FO1 FP0; lia) ltac:(clear - FO2 BF1 LO736 SPT; lia) ISVR FFR MI11).
clear HD FST PT LE SEED CFG IDC PAD.

assert (TAILN : forall (m11 : mem) (ows : list word) (r_ra r_t0 r_t1 r_t2 r_a0 r_a1 r_a2 r_a3 r_a4 r_a5 r_a6 r_a7 r_t3 r_t4 r_t5 r_t6 : word) (c3 : config),
rw_cells bsegs m11 (usp + -160) (sb_saves F ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
rw_cells bsegs m11 f (sb_fhdr j24 (Z_to_bv 64 dtx) j36) ->
rw_cells bsegs m11 sf sb_fshadow ->
sb_bufs bsegs m11 a j ->
rw_cells bsegs m11 OUT (f32 ows) -> length ows = 2000%nat ->
rw_cells bsegs m11 STEREO [CB 24 stb] ->
ERR_rep m11 ->
stk bsegs m11 lo (usp + -736) ->
rw_cells bsegs m11 A [C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 (sb_nbBits (sbw_bits b1))); C4 (Z_to_bv 64 (sb_charPtr (sbw_bits b1))); C4 (Z_to_bv 64 (sb_bitPtr (sbw_bits b1)));
C4 (Z_to_bv 64 (sb_owner (sbw_bits b1))); C4 (Z_to_bv 64 (sb_overflow (sbw_bits b1))); C4 (Z_to_bv 64 (sb_buf_size (sbw_bits b1))); CB 16 rj8] ->
rw_cells bsegs m11 D [CB (length bs8) bs8] ->
rw_cells bsegs m11 S (SBCELLS sI a OUT j) ->
wmono bsegs m9 m11 -> mem_inv bsegs m11 ->
rw_cells bsegs m11 (usp + -736) (sb_fr (fupds (fupds g [(47%nat, Z_to_bv 64 (S + 144)); (48%nat, Z_to_bv 64 (S + 152))])
[(45%nat, Z_to_bv 64 (Z.shiftr (S + 144) 3 + SHB)); (44%nat, Z_to_bv 64 (Z.shiftr (S + 152) 3 + SHB))])) ->
DREP OUT STEREO m11 (a_low a) low3 LBL ->
(forall so, OUT_rep so m -> OUT_rep so m11) ->
ART RT Σx m11 ->
rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m11 ->
acc bsegs m11 A 48 -> acc bsegs m11 OUT 8000 -> acc bsegs m11 STEREO 24 -> io_ssp m11 -> acc bsegs m11 S 160 -> aobj bsegs m11 S 160 ->
ASTA RT Σx (PMfd F0 fs0) (eq (MS (R_N usp S A f (sbmode_struct (sbd_mode s)) gp (Z_to_bv 64 6524056) r_ra r_t0 r_t1 r_t2 r_a0 r_a1 r_a2 r_a3 r_a4 r_a5 r_a6 r_a7
(Z_to_bv 64 (f + 32)) (Z_to_bv 64 S) s11 r_t3 r_t4 r_t5 r_t6) Fx (Z_to_bv 64 0xc025c) fcx None m11 (seg_rom bsegs))) c3 ->
realizes bsegs c3 T).
{ clear SV FRB FRS BUFS OC LOWS STB ERRX ST8 BOBJ8 BDAT8 X9 MU11 WM11 MI11 FR11 EXR RLOW OUTK0 ART11 PF ACA11 ACO11 ACT11 SSP11 ACS11 OBS11 POST Hc.
clear c3 ms m11 ows.
intros m11 ows r_ra r_t0 r_t1 r_t2 r_a0 r_a1 r_a2 r_a3 r_a4 r_a5 r_a6 r_a7 r_t3 r_t4 r_t5 r_t6 c3
SV FRB FRS BUFS OC LOWS STB ERRX ST8 BOBJ8 BDAT8 X9 WM11 MI11 FR11 RLOW OUTK0 ART11 PF ACA11 ACO11 ACT11 SSP11 ACS11 OBS11 Hc.

cps_seg (sbd_n2 usp S OUT A f (sbmode_struct (sbd_mode s)) dtx
(fupds (fupds g [(47%nat, Z_to_bv 64 (S + 144)); (48%nat, Z_to_bv 64 (S + 152))]) [(45%nat, Z_to_bv 64 (Z.shiftr (S + 144) 3 + SHB)); (44%nat, Z_to_bv 64 (Z.shiftr (S + 152) 3 + SHB))])
(Z_to_bv 64 0) j24 j36 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
FR11 ltac:(gslot) ltac:(cbn [fupds Nat.eqb]; exact G45) FRB DTXV ltac:(clear - F1; lia) ltac:(clear - FIMG BF LO736 SPT; lia) MI11).
destruct POST as [(DT0 & xa0n & ->) | (DT1 & ->)].
2: {
assert (AL : sb_addrs_al a)
by (apply (sb_addrs_al_of_blocks s S a); intros bk Hb; apply LAL8; rewrite ELBD; apply in_app_iff; left; exact Hb).
assert (NDB : List.NoDup (map blk_id (sb_blocks sI S a))) by (pose proof NDUP as ND'; rewrite ELBD, map_app in ND'; exact (List.NoDup_app_remove_r _ _ ND')).
assert (LIVEB : forall bk, In bk (sb_blocks sI S a) -> In (blk_addr bk, blk_size bk) (rt_live RT Σx))
by (intros bk Hb; apply LIVED; rewrite ELBD; apply in_app_iff; left; exact Hb).
assert (IFO : in_frame_obj RT Σx m11 fh kh OUT 8000) by (exact (conj FO1 (conj FO2 (conj ACO11 OAL)))).
assert (EU608 : bv_unsigned (Z_to_bv 64 (usp + -736)) = usp + -736) by (apply unsigned_lit; clear - SPT LO736 LOS; lia).
assert (POA608 : pois_above (rt_pois RT Σx) (bv_unsigned (Z_to_bv 64 (usp + -736)))) by (rewrite EU608; apply (pois_above_le _ usp); [rewrite EPX; exact POA| clear; lia]).
assert (ST608 : stk bsegs m11 lo (bv_unsigned (Z_to_bv 64 (usp + -736)))) by (rewrite EU608; exact ST8).
assert (LOR608 : lo + RT_STACK + SBLOST_STACK <= bv_unsigned (Z_to_bv 64 (usp + -736)))
by (rewrite EU608; clear - LOR DSP; unfold RT_STACK, SBLOST_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
assert (SPT608 : bv_unsigned (Z_to_bv 64 (usp + -736)) + 16 <= USTACK_TOP) by (rewrite EU608; clear - SPT; unfold USTACK_TOP in *; lia).
assert (SPA608 : bv_unsigned (Z_to_bv 64 (usp + -736)) mod 32 = 0) by (rewrite EU608; clear - SPA; Z.div_mod_to_equations; lia).
cps_rt (LOST Σx (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m11 S OUT lo fh kh sI a j ows
FDO MST eq_refl eq_refl eq_refl eq_refl X9 JOK1 INV1 BUFS S8 SPOS AL NDB LIVEB OC LOWS INFHX IFO POA608 ART11 MI11 FRMX ST608 LOWX LOR608 SPT608 SPA608).
intros cl (Σl & Hcl & LVl & FRl & SPl & CRl & POl).
cps_unpack_lib Hcl as (vl & m13 & j' & ows' & RSl & (ART13 & MI13 & WM13 & ST13) & PRES13 & X13 & JOK13 & BUFS13 & OC13 & LOWS13 & ACO13).
try rewrite EU608 in PRES13. try rewrite EU608 in ST13.
clear X9 BUFS OC LOWS ACO11 IFO.

assert (OUTL13 : forall x, (x < OUT \/ OUT + 8000 <= x) -> (x < S \/ S + 160 <= x) -> outside (blocks_ivs (tl (sb_blocks sI S a))) x ->
outside ((OUT, OUT + 8000) :: blocks_ivs (sb_blocks sI S a)) x).
{ intros x H1 H2 H3. cbn [outside blocks_ivs sb_blocks map blk_addr blk_size fst snd]. unfold SBSTATE_SIZEOF.
split; [clear - H1; lia|]. split; [clear - H2; lia|]. exact H3. }
assert (OTB : forall x, (lo <= x \/ fh <= x < fh + fs_size kh \/ PD <= x < PD + ND \/ f <= x < f + 64 \/ sf <= x < sf + 8) ->
outside (blocks_ivs (tl (sb_blocks sI S a))) x).
{ intros x Hx. apply outside_blocks_ivs. intros bk Hb Hin.
pose proof (BOUT bk x ltac:(unfold LALL; apply in_app_iff; left; exact Hb) Hin) as H1. clear - Hx H1. lia. }
assert (CLF : forall x, fh <= x < fh + fs_size kh - 8 -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -736) x)
by (intros x Hx; right; right; right; left; exists fh, kh; split; [exact INFHX| exact Hx]).
assert (CLS : forall x, usp + -736 <= x < usp -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -736) x)
by (intros x Hx; left; clear - Hx SPT; unfold USTACK_TOP in *; lia).
assert (CLL : forall p n x, In (p, n) (rt_live RT Σx) -> p <= x < p + n -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -736) x)
by (intros p n x Hp Hx; right; right; left; exists p, n; split; [exact Hp| exact Hx]).
assert (CLF0 : forall x, f <= x < f + 56 -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -736) x)
by (intros x Hx; right; right; right; left; exists f, 0%nat; split; [exact INF| change (fs_size 0) with 64; lia]).
assert (CLSF : forall x, sf <= x < sf + 8 -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -736) x)
by (intros x Hx; right; right; right; right; exists f, 0%nat; split; [exact INF| change (fs_size 0) with 64; rewrite <- SHF, SHF0; lia]).
destruct (frame_live_apart RT AF Σx m11 fh kh PD ND ART11 INFHX INPDX) as (FLPD & _).
assert (SPD' : S + 160 <= PD \/ PD + ND <= S) by (clear - SPD; unfold hid in *; lia).
assert (SFH' : S + 160 <= fh \/ fh + fs_size kh <= S) by (clear - SFH; unfold hid in *; lia).
assert (SFA' : S + 160 <= f \/ f + 64 <= S) by (clear - SFA; unfold hid in *; lia).
assert (SFS' : S + 160 <= sf \/ sf + 8 <= S) by (clear - SFS SHF; unfold hid in *; subst sf; lia).
assert (FFA' : fh + fs_size kh <= f \/ f + 64 <= fh) by (clear - FFA; unfold hid in *; lia).
assert (FPHI2 : fh + fs_size kh <= SH_LO \/ SH_HI <= fh) by (clear - FPHI'; unfold hid, SH_LO, SH_HI in *; lia).
tr1 PRES13 WM13 STB ltac:(fun x Hx => apply CLF; clear - Hx FS1 FS2; lia)
ltac:(fun x Hx => apply OUTL13; [clear - Hx HOS'; unfold hid in *; lia | clear - Hx FS1 FS2 SFH'; lia | apply OTB; right; left; clear - Hx FS1 FS2; lia]).
tr1 PRES13 WM13 BOBJ8 ltac:(fun x Hx => apply CLF; clear - Hx FA1 FA2; lia)
ltac:(fun x Hx => apply OUTL13; [clear - Hx HAO'; unfold hid in *; lia | clear - Hx FA1 FA2 SFH'; lia | apply OTB; right; left; clear - Hx FA1 FA2; lia]).
tr1 PRES13 WM13 BDAT8 ltac:(fun x Hx => apply (CLL PD ND x INPDX); clear - Hx PD1 PD2 Lbs8; lia)
ltac:(fun x Hx => apply OUTL13; [clear - Hx PD1 PD2 Lbs8 FLPD FO1 FO2; lia | clear - Hx PD1 PD2 Lbs8 SPD'; lia | apply OTB; right; right; left; clear - Hx PD1 PD2 Lbs8; lia]).
tr1 PRES13 WM13 FR11 ltac:(fun x Hx => apply CLS; clear - Hx; lia)
ltac:(fun x Hx => apply OUTL13; [clear - Hx BF1 LO736 FO1 FO2; lia | clear - Hx BS1 LO736; lia | apply OTB; left; clear - Hx LO736; lia]).
tr1 PRES13 WM13 SV ltac:(fun x Hx => apply CLS; clear - Hx; lia)
ltac:(fun x Hx => apply OUTL13; [clear - Hx BF1 LO736 FO1 FO2; lia | clear - Hx BS1 LO736; lia | apply OTB; left; clear - Hx LO736; lia]).
tr1 PRES13 WM13 FRB ltac:(fun x Hx => apply CLF0; clear - Hx; lia)
ltac:(fun x Hx => apply OUTL13; [clear - Hx FFA' FO1 FO2; lia | clear - Hx SFA'; lia | apply OTB; right; right; right; left; clear - Hx; lia]).
tr1 PRES13 WM13 FRS ltac:(fun x Hx => apply CLSF; clear - Hx; lia)
ltac:(fun x Hx => apply OUTL13; [clear - Hx FPHI2 SHF1 SHF2 FO1 FO2; unfold SH_LO, SH_HI in *; lia | clear - Hx SFS'; lia | apply OTB; right; right; right; right; clear - Hx; lia]).
assert (AGL13 : agree_blocks bsegs m11 m13 LBL).
{ apply (agree_blocks_of_pres_fp RT Σx _ _ _ m11 m13 _ PRES13 WM13); [exact LIVEL|].
intros bk x Hb Hx. pose proof (BOUT bk x ltac:(unfold LALL; apply in_app_iff; right; exact Hb) Hx) as H1.
destruct (frame_live_apart RT AF Σx m11 fh kh _ _ ART11 INFHX (LIVEL bk Hb)) as (FB & _).
apply OUTL13; [clear - H1 FB Hx FO1 FO2; lia | clear - H1; lia |]. apply outside_blocks_ivs. intros b2 Hb2 Hin.
assert (NE : blk_addr b2 <> blk_addr bk).
{ pose proof NDUP as ND'. rewrite ELBD, map_app in ND'. apply (NoDup_app_in_neq _ _ (blk_id b2) (blk_id bk) ND'); [apply in_map; cbn [sb_blocks tl] in Hb2 |- *; right; exact Hb2| apply in_map; exact Hb]. }
pose proof (live_apart RT AF Σx m11 _ _ _ _ ART11 (LIVEA b2 ltac:(unfold LALL; apply in_app_iff; left; exact Hb2)) (LIVEL bk Hb) NE) as AP.
clear - AP Hx Hin. lia. }
pk_blocks AGL13. clear AGL13.
assert (OIO13 : forall y, 65536 <= y < 6664192 -> outside ((OUT, OUT + 8000) :: blocks_ivs (sb_blocks sI S a)) y).
{ intros y Hy. apply OUTL13; [clear - Hy FO1 FPIMG; unfold SEGTOP_A in *; lia | clear - Hy SIMG; unfold SEGTOP_A in *; lia |].
apply outside_blocks_ivs. intros bk Hb Hin. pose proof (BOUT bk y ltac:(unfold LALL; apply in_app_iff; left; exact Hb) Hin) as H1. clear - H1 Hy. lia. }
pk_io_fp PRES13 ERR_rep OUT_rep IO_FP IO_img ltac:(fun y Hy => apply OIO13; exact Hy).
assert (SSP13 : io_ssp m13).
{ apply (sbd_io_ssp_agree m11 m13 SSP11 (AF_DRV Σl m13 ART13)). intros a0 Ha. apply PRES13; [right; left; exact (sbd_ssp_static _ Ha)|].
unfold X0r9.SSP_GUARD in Ha. apply OIO13. lia. }
assert (SHW13 : forall o n, fh <= o -> o + n <= fh + fs_size kh -> forall i, 0 <= i < n -> outside ((OUT, OUT + 8000) :: blocks_ivs (sb_blocks sI S a)) (shad (o + i))).
{ intros o n H1 H2 i Hi.
assert (SR : SH_LO <= shad (o + i) < SH_HI).
{ pose proof (frame_facts RT AF Σx m11 fh kh ART11 INFHX) as (_ & _ & _ & _ & _ & _ & SA & SL & SH & _). split.
- unfold shad, SH_LO, SHB in *. assert (0 <= (o + i) / 8) by (apply Z.div_pos; lia). lia.
- assert (shad (o + i) < shad (fh + fs_size kh)); [| lia].
unfold shad. apply Z.add_lt_mono_r. apply Z.div_lt_upper_bound; [lia|].
assert (FH8 : fh mod 8 = 0) by (clear - FP64; Z.div_mod_to_equations; lia).
assert (FK8 : fs_size kh mod 8 = 0) by (destruct FS64 as (M64 & _); clear - M64; Z.div_mod_to_equations; lia).
assert (E : fh + fs_size kh = 8 * ((fh + fs_size kh) / 8)).
{ pose proof (Z.div_mod (fh + fs_size kh) 8 ltac:(lia)) as XD. rewrite Zplus_mod, FH8, FK8 in XD. cbn in XD. lia. }
lia. }
cbn [outside]. split; [clear - SR FPHI2 FO1 FO2; unfold SH_LO, SH_HI in *; lia|].
exact (outside_blocks_shadow RT AF Σx m11 (sb_blocks sI S a) _ ART11 ltac:(intros bk Hb; apply LIVED; rewrite ELBD; apply in_app_iff; left; exact Hb) SR). }
assert (FH8 : fh mod 8 = 0) by (clear - FP64; Z.div_mod_to_equations; lia).
assert (FK8 : fs_size kh mod 8 = 0) by (destruct FS64 as (M64 & _); clear - M64; Z.div_mod_to_equations; lia).
assert (ACA13 : acc bsegs m13 A 48)
by (apply (acc_pres_fp_frame _ _ _ _ m11 m13 fh kh A 48 PRES13 INFHX FH8 FK8 ltac:(lia) FA1 ltac:(lia) (SHW13 A 48 FA1 ltac:(lia)) ACA11)).
assert (ACT13 : acc bsegs m13 STEREO 24)
by (apply (acc_pres_fp_frame _ _ _ _ m11 m13 fh kh STEREO 24 PRES13 INFHX FH8 FK8 ltac:(lia) FS1 ltac:(lia) (SHW13 STEREO 24 FS1 ltac:(lia)) ACT11)).
assert (PF13 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m13).
{ apply (pres_fp_trans _ _ _ _ m m11 m13 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σx) (rt_frames RT Σx) (usp + -736) _ m11 m13 PRES13).
- intros e He. rewrite ELX. exact He.
- intros e He. rewrite EFX. right. exact He.
- clear; lia.
- intros x Hx Ho. cbn [outside] in Ho. destruct Ho as (_ & HO & _ & Ho). apply sb_outside_app_inv in Ho. destruct Ho as [Hb _].
rewrite ELBD1 in Hb. cbn [outside]. split; [exact HO| exact (outside_blocks_app_l _ _ x Hb)]. }
clear PF PRES13 ACA11 ACT11 SSP11 SHW13. rename PF13 into PF.
clear Hc0.

cps_seg (sbd_n3 usp S OUT A f (sbmode_struct (sbd_mode s)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
subst ms.
assert (EFl : rt_frames RT Σl = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRl; exact EFX).
assert (ELl : rt_live RT Σl = rt_live RT Σ) by (rewrite LVl; exact ELX).
assert (ESl : rt_sp0 RT Σl = rt_sp0 RT Σ) by (rewrite SPl; exact ESX).
assert (EPl : rt_pois RT Σl = rt_pois RT Σ) by (rewrite POl; exact EPX).
assert (INV13 : sb_inv (set_sbd_first sI 1)).
{ destruct INV1 as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12). unfold sb_inv. cbn [set_sbd_first sbd_mode sbd_frame_size sbd_full_frame_size
sbd_subframeSize sbd_nbSubframes sbd_lpcSize sbd_first sbd_sampling_rate sbd_lpc_enh_enabled sbd_encode_submode sbd_submodeID sbd_innov_save].
refine (conj I1 (conj I2 (conj I3 (conj I4 (conj I5 (conj I6 (conj (or_intror eq_refl) (conj I8 (conj I9 (conj I10 (conj I11 I12))))))))))). }
assert (REPX : DREP OUT STEREO m13 S (DecSB (set_sbd_first sI 1) low3) LBD).
{ cbn [decst_rep]. exists a, j', LBL. split; [exact ELBD1|]. split; [exact S8|]. split; [exact SPOS|]. split; [exact INV13|]. split; [exact JOK13|].
split; [exact X13|]. split; [exact BUFS13|]. exists OUT. exact RLOW. }
assert (BREPX : bits_rep bsegs m13 A D (sbw_bits b1)).
{ split; [exists rj8; split; [exact Lrj8| unfold bits_cells; exact BOBJ8]|].
split; [exists bs8; split; [apply (proj2 (u8arr_rw_CB m13 D bs8)); exact BDAT8| exact Hbs8]| exact BSIDE8]. }
assert (PD2X : D + sb_buf_size (sbw_bits b1) <= PD + ND) by (rewrite BSZ8; exact PD2).
assert (WMX : wmono bsegs m m13) by (eapply wmono_trans; [exact WM0|]; eapply wmono_trans; [exact WM8|]; eapply wmono_trans; [exact WM9|];
eapply wmono_trans; [exact WM11| exact WM13]).
cps_rt (sbd_exit_cps RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AUN_lo AUN_nop Σ Σl F0 fs0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m m13 lo S OUT STEREO A D f fh PD ND kh LBD
(fupds (fupds g [(47%nat, Z_to_bv 64 (S + 144)); (48%nat, Z_to_bv 64 (S + 152))]) [(45%nat, Z_to_bv 64 (Z.shiftr (S + 144) 3 + SHB)); (44%nat, Z_to_bv 64 (Z.shiftr (S + 152) 3 + SHB))])
0 0 (DecSB (set_sbd_first sI 1) low3) (sbw_bits b1) ows' stb j24 j36 (Z_to_bv 64 dtx)
EFl ELl ESl EPl ART0 POA NAF LIVE INPD PD1 PD2X INFH FA1 FA2 ACA FO1 FO2 ACO FS1 FS2 ACST ART13 MI13 RSl ST13 LOW
ltac:(clear - LOR DSP; unfold RT_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia) SPT SPA PF WMX FR11
ltac:(cbn [fupds Nat.eqb]; exact G13) ltac:(cbn [fupds Nat.eqb]; exact G52) ltac:(cbn [fupds Nat.eqb]; exact G51)
(or_introl eq_refl) SV FRB FRS REPX (fun _ => I) BREPX BOK8 OC13 LOWS13 STB ERRX OUTK).
intros c' (Σ' & Hc' & E1 & E2 & E3 & E4 & E5).
apply Hk. exists Σ'. split; [exact Hc'|].
pose proof (bkeep_sbw b1) as (K1 & K2 & K3).
cbn [dec_depth dec_mode dec_nestedR dec_credit sI set_sbd_submodeID set_sbd_first sbd_mode].
split; [clear; lia|]. split; [rewrite DL3; reflexivity|]. split; [reflexivity|]. split; [split; [exact NM3| exact NEST3]|].
split; [rewrite K2; exact OWN1|]. split; [rewrite K1; exact CHR1|]. split; [rewrite K3; exact BSZ1|].
split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [| exact E5].
rewrite E4, CRl. pose proof (dec_depth_pos low) as DP. clear - CBX DP. lia. }

set (fsz := sbd_frame_size s) in *.
set (Y := OUT + 4 * fsz).
assert (FSN : (Z.of_nat (Z.to_nat fsz) = fsz)%Z) by (clear - FSV; lia).
apply (f32_split bsegs m11 OUT ows (Z.to_nat fsz)) in OC; [| rewrite LOWS; clear - FSV; lia].
destruct OC as (OCa & OCb). rewrite FSN in OCb.
apply (f32_split bsegs m11 (OUT + 4 * fsz) (skipn (Z.to_nat fsz) ows) (Z.to_nat fsz)) in OCb; [| rewrite length_skipn, LOWS; clear - FSV; lia].
destruct OCb as (OCy & OCc). rewrite FSN in OCc. fold Y in OCy.
assert (LYW : length (firstn (Z.to_nat fsz) (skipn (Z.to_nat fsz) ows)) = Z.to_nat fsz)
by (rewrite length_firstn, length_skipn, LOWS; clear - FSV; lia).
destruct (firstn (Z.to_nat fsz) (skipn (Z.to_nat fsz) ows)) as [|cw rest] eqn:EYW; [cbn [length] in LYW; clear - LYW FSV; lia|].
assert (LREST : Z.of_nat (length rest) + 1 = fsz) by (cbn [length] in LYW; clear - LYW FSV; lia).
assert (OBY : aobj bsegs m11 Y (4 * fsz)).
{ split; [unfold Y; clear - FO1 FP0 FSV; lia|]. split; [unfold Y; clear - FO2 BF1 LO736 SPT FSV; unfold APP_TOP; lia|].
apply (acc_sub bsegs m11 OUT 8000 Y (4 * fsz) ACO11); unfold Y; clear - FSV; lia. }
sb_unpack X9 as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_n4 usp S OUT A f (sbmode_struct (sbd_mode s)) fsz Y
(fupds (fupds g [(47%nat, Z_to_bv 64 (S + 144)); (48%nat, Z_to_bv 64 (S + 152))]) [(45%nat, Z_to_bv 64 (Z.shiftr (S + 144) 3 + SHB)); (44%nat, Z_to_bv 64 (Z.shiftr (S + 152) 3 + SHB))])
(Z_to_bv 64 0) (Z_to_bv 64 (sbd_first sI)) sI a cw rest _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
FR11 ltac:(cbn [fupds Nat.eqb]; exact G27) ltac:(cbn [fupds Nat.eqb]; exact G26) ltac:(cbn [fupds Nat.eqb]; exact G45)
ltac:(gslot) ltac:(gslot) ltac:(gslot)
HD FST PT eq_refl ILPC ltac:(clear - FSV; lia) LREST OBS11 S8 SPOS SLO8 SOFF SIMG ltac:(clear - FO1 FP0; lia) ltac:(clear - FO2 BF1 LO736 SPT; lia) eq_refl OCy OBY
ltac:(unfold Y; clear - OAL; Z.div_mod_to_equations; lia) ltac:(unfold Y, IMG_TOP_B; clear - FPIMG FO1 FSV; unfold SEGTOP_A in *; lia)
ltac:(unfold Y; clear - FPHI' FO1 FO2 FSV; unfold hid, SH_LO, SH_HI in *; lia)
ltac:(unfold Y; clear - SFH FO1 FO2 FSV; unfold hid in *; lia) ltac:(unfold Y; clear - FO2 BF1 LO736 FSV; lia) SHL SPH MI11).
destruct POST as (m14 & xa7s & ys' & -> & MU14 & WM14 & MI14 & FST14 & YS14 & LYS14).
clear X9 OCy FST.
assert (OUTSB : forall x, outside (blocks_ivs LBD) x -> ~ (S <= x < S + 160)).
{ intros x Ho. rewrite ELBD in Ho. cbn [sb_blocks app blocks_ivs map outside blk_addr blk_size fst snd] in Ho. destruct Ho as [Ho _]. unfold SBSTATE_SIZEOF in Ho. exact Ho. }
assert (ART14 : X14x.ART RT Σx m14).
{ apply (af_frame RT AF Σx m11 m14 lo ART11 LOWX); [| exact WM14]. intros a0 Ha. apply MU14. cbn [outside]. split; [| split; [| exact I]].
- intros Hin. apply Ha. right; right; left. exists S, 160. split; [exact INLX | clear - Hin; lia].
- intros Hin. apply Ha. right; right; right; left. exists fh, kh. split; [exact INFHX | unfold Y in Hin; clear - Hin FO1 FO2 FSV; lia]. }
assert (PF14 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m14).
{ apply (pres_fp_trans _ _ _ _ m m11 m14 PF). apply (pres_fp_of_munch _ _ _ _ _ m11 m14 MU14). intros x Hx Ho. cbn [outside] in Ho |- *.
destruct Ho as (_ & HO & _ & Ho). apply sb_outside_app_inv in Ho. destruct Ho as [Hb _].
split; [intros Hin; apply (OUTSB x Hb); clear - Hin; lia|]. split; [intros Hin; apply HO; unfold Y in Hin; clear - Hin FSV; lia| exact I]. }
clear PF. rename PF14 into PF.
pk_munch_all MU14 WM14 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1;
destruct (frame_live_apart RT AF Σx m11 fh kh _ _ ART11 INFHX (LIVEA b Hb)) as (FB & _);
clear - H1 FB Hx FO1 FO2 FSV; unfold Y; cbn [outside]; split; [lia| split; [lia| exact I]])
ltac:(fun x Hx => clear - Hx SIMG FO1 FPIMG FSV; unfold Y, SEGTOP_A in *; cbn [outside]; split; [lia| split; [lia| exact I]]).
destruct (frame_live_apart RT AF Σx m11 fh kh PD ND ART11 INFHX INPDX) as (FLPD & _).
assert (SPD' : S + 160 <= PD \/ PD + ND <= S) by (clear - SPD; unfold hid in *; lia).
assert (SFH' : S + 160 <= fh \/ fh + fs_size kh <= S) by (clear - SFH; unfold hid in *; lia).
assert (SFA' : S + 160 <= f \/ f + 64 <= S) by (clear - SFA; unfold hid in *; lia).
assert (SFS' : S + 160 <= sf \/ sf + 8 <= S) by (clear - SFS SHF; unfold hid in *; subst sf; lia).
assert (FFA' : fh + fs_size kh <= f \/ f + 64 <= fh) by (clear - FFA; unfold hid in *; lia).
assert (FPHI2 : fh + fs_size kh <= SH_LO \/ SH_HI <= fh) by (clear - FPHI'; unfold hid, SH_LO, SH_HI in *; lia).
assert (YR : OUT <= Y /\ Y + 4 * fsz <= OUT + 8000) by (unfold Y; clear - FSV; lia).
Ltac trm MU WM H tacD :=
lazymatch type of MU with
| munch ?W ?m ?m' =>
lazymatch type of H with
| rw_cells bsegs m ?A0 ?cs =>
let H' := fresh "T" in
assert (H' : rw_cells bsegs m' A0 cs)
by (apply (rw_cells_transport bsegs W m m' A0 cs H MU WM); cbn [disjoint_from]; simpl_sizes; tacD);
clear H; rename H' into H
end
end.
set (wa := firstn (Z.to_nat fsz) ows) in OCa. set (wc := skipn (Z.to_nat fsz) (skipn (Z.to_nat fsz) ows)) in OCc.
assert (LWA : Z.of_nat (length wa) = fsz) by (unfold wa; rewrite length_firstn, LOWS; clear - FSV; lia).
assert (LWC : Z.of_nat (length wc) = 2000 - 2 * fsz) by (unfold wc; rewrite !length_skipn, LOWS; clear - FSV; lia).
trm MU14 WM14 OCa ltac:(unfold Y; clear - LWA SFH' FO1 FO2 FSV; lia).
trm MU14 WM14 OCc ltac:(unfold Y; clear - LWC SFH' FO1 FO2 FSV; lia).
trm MU14 WM14 SV ltac:(unfold Y; clear - BS1 LO736 FO2 BF1 FSV; lia).
trm MU14 WM14 FR11 ltac:(unfold Y; clear - BS1 LO736 FO2 BF1 FSV; lia).
trm MU14 WM14 FRB ltac:(unfold Y; clear - SFA' FFA' FO1 FO2 FSV; lia).
trm MU14 WM14 FRS ltac:(unfold Y; clear - SFS' FPHI2 SHF1 SHF2 FO1 FO2 FSV; unfold SH_LO, SH_HI in *; lia).
trm MU14 WM14 STB ltac:(unfold Y; clear - SFH' HOS' FS1 FS2 FO1 FO2 FSV; unfold hid in *; lia).
trm MU14 WM14 BOBJ8 ltac:(unfold Y; clear - SFH' HAO' FA1 FA2 FO1 FO2 FSV; unfold hid in *; lia).
trm MU14 WM14 BDAT8 ltac:(unfold Y; clear - SPD' FLPD PD1 PD2 Lbs8 FO1 FO2 FSV; lia).
trm MU14 WM14 HD ltac:(unfold Y; clear - SFH' FO1 FO2 FSV; lia).
trm MU14 WM14 PT ltac:(unfold Y; clear - SFH' FO1 FO2 FSV; lia).
trm MU14 WM14 LE ltac:(unfold Y; clear - SFH' FO1 FO2 FSV; lia).
trm MU14 WM14 SEED ltac:(unfold Y; clear - SFH' FO1 FO2 FSV; lia).
trm MU14 WM14 CFG ltac:(unfold Y; clear - SFH' FO1 FO2 FSV; lia).
trm MU14 WM14 IDC ltac:(unfold Y; clear - SFH' FO1 FO2 FSV; lia).
trm MU14 WM14 PAD ltac:(unfold Y; clear - SFH' FO1 FO2 FSV; lia).
apply (stk_transport_disjoint bsegs [(S + 36, S + 40); (Y, Y + 4 * fsz)] m11 m14 lo (usp + -736)) in ST8; [| exact MU14 | exact WM14 | cbn [disjoint_from]; unfold Y; clear - BS1 FO2 BF1 FSV; lia].
clear ART11.
cps_hide.

assert (OF14 : offsh [(S + 36, S + 40); (Y, Y + 4 * fsz)]) by (cbn [offsh]; unfold Y; clear - SOFF FPHI2 FO1 FO2 FSV; try unfold hid in *; unfold hid, SH_LO, SH_HI in *; lia).
assert (ACC14 : forall o n, acc bsegs m11 o n -> 0 <= o -> o + n <= 140737488355328 -> acc bsegs m14 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch bsegs _ m11 m14 o n (conj H0 (conj H1 H)) MU14 (shfree_of_offsh _ o n OF14 H0 H1)))). }
assert (ACA14 : acc bsegs m14 A 48) by (apply ACC14; [exact ACA11| clear - FA1 FP0; try unfold hid in *; lia| clear - FA2 BF1 LO736 SPT; try unfold hid in *; lia]).
assert (ACO14 : acc bsegs m14 OUT 8000) by (apply ACC14; [exact ACO11| clear - FO1 FP0; try unfold hid in *; lia| clear - FO2 BF1 LO736 SPT; try unfold hid in *; lia]).
assert (ACT14 : acc bsegs m14 STEREO 24) by (apply ACC14; [exact ACT11| clear - FS1 FP0; try unfold hid in *; lia| clear - FS2 BF1 LO736 SPT; try unfold hid in *; lia]).
assert (SSP14 : io_ssp m14).
{ apply (sbd_io_ssp_agree m11 m14 SSP11 (AF_DRV Σx m14 ART14)). intros a0 Ha. apply MU14. unfold X0r9.SSP_GUARD in Ha. cbn [outside].
unfold Y. clear - Ha SIMG FO1 FPIMG FSV. unfold SEGTOP_A in *. split; [lia| split; [lia| exact I]]. }
clear ACA11 ACO11 ACT11 SSP11 ACC14 OBS11 ACS11 OBY.

destruct BUFS as (G0C & G1C & EXC & OQC & IQC & MSPC & PGC & ERC).
pose proof JOK as (JP1 & JP2 & JG0 & JG1 & JEXC & JOQ & JIQ & JMSP & JPG & JER).
apply (f32_split bsegs m14 (a_msp a) (sj_msp j) 8) in MSPC; [| rewrite JMSP; clear; lia]. destruct MSPC as (MSP1 & MSP2).
assert (LMEM : length (firstn 8 (sj_msp j)) = length (sj_iq j)) by (rewrite length_firstn, JMSP, JIQ; reflexivity).
assert (INIQ : In (a_iq a, 32) (rt_live RT Σx)) by (apply (LIVED (sbd_interp_qlpc s, a_iq a, 32)); rewrite ELBD; apply in_app_iff; left; cbn [sb_blocks In]; do 5 right; left; reflexivity).
assert (INMSP : In (a_msp a, 64) (rt_live RT Σx)) by (apply (LIVED (sbd_mem_sp s, a_msp a, 64)); rewrite ELBD; apply in_app_iff; left; cbn [sb_blocks In]; do 8 right; left; reflexivity).
destruct (af_acc_live RT AF Σx m14 _ _ ART14 INIQ) as (_ & ACIQ). destruct (af_acc_live RT AF Σx m14 _ _ ART14 INMSP) as (_ & ACMSP).
destruct (live_below_lo RT AF Σx m14 _ _ lo ART14 INIQ LOWX) as (IQP & IQLO & _). destruct (live_below_lo RT AF Σx m14 _ _ lo ART14 INMSP LOWX) as (MSPP & MSPLO & _).
pose proof (live_facts RT AF Σx m14 _ _ ART14 INIQ) as (_ & _ & _ & IQSH). pose proof (live_facts RT AF Σx m14 _ _ ART14 INMSP) as (_ & _ & _ & MSPSH).
pose proof (af_live_small RT AF Σx m14 _ _ ART14 INMSP ltac:(clear; lia)) as MSPIMG.
destruct (frame_live_apart RT AF Σx m14 fh kh _ _ ART14 INFHX INIQ) as (FIQ & _). destruct (frame_live_apart RT AF Σx m14 fh kh _ _ ART14 INFHX INMSP) as (FMSP & _).
assert (NEIM : a_iq a <> a_msp a).
{ intros E. pose proof NDUP as ND'. rewrite ELBD, map_app in ND'. apply List.NoDup_app_remove_r in ND'.
cbn [sb_blocks map blk_id blk_addr fst snd] in ND'.
do 5 (apply List.NoDup_cons_iff in ND'; destruct ND' as [_ ND']).
apply List.NoDup_cons_iff in ND'. destruct ND' as [NI _]. apply NI. rewrite E. cbn [In]. right; right; left; reflexivity. }
pose proof (live_apart RT AF Σx m14 _ _ _ _ ART14 INIQ INMSP NEIM) as IQMSP.
assert (AL8a : sb_addrs_al a) by (apply (sb_addrs_al_of_blocks s S a); intros bk Hb; apply LAL8; rewrite ELBD; apply in_app_iff; left; exact Hb).
assert (LYS' : 1 <= Z.of_nat (length ys') < 2^31) by (rewrite LYS14; clear - FSV; try unfold hid in *; lia).
assert (ORD8 : 2 <= Z.of_nat (length (sj_iq j)) < 2^31) by (rewrite JIQ; cbn; lia).
assert (OBX14 : aobj bsegs m14 Y (4 * Z.of_nat (length ys'))).
{ rewrite LYS14. split; [unfold Y; clear - FO1 FP0 FSV; try unfold hid in *; lia|]. split; [unfold Y; clear - FO2 BF1 LO736 SPT FSV; try unfold hid in *; unfold APP_TOP; lia|].
apply (acc_sub bsegs m14 OUT 8000 Y (4 * fsz) ACO14); unfold Y; clear - FSV; try unfold hid in *; lia. }
assert (OBD14 : aobj bsegs m14 (a_iq a) (4 * Z.of_nat (length (sj_iq j)))) by (rewrite JIQ; split; [lia|]; split; [clear - IQLO LO736 SPT; try unfold hid in *; unfold APP_TOP; cbn; lia| exact ACIQ]).
assert (OBM14 : aobj bsegs m14 (a_msp a) (4 * Z.of_nat (length (sj_iq j))))
by (rewrite JIQ; split; [lia|]; split; [clear - MSPLO LO736 SPT; try unfold hid in *; unfold APP_TOP; cbn; lia| exact (acc_sub bsegs m14 (a_msp a) 64 (a_msp a) 32 ACMSP ltac:(clear; lia) ltac:(clear; lia))]).
destruct AL8a as (_ & _ & _ & _ & IQ8 & MSP8 & _).
rewrite <- LYS14 in Hc.
replace (Z_to_bv 64 8) with (Z_to_bv 64 (Z.of_nat (length (sj_iq j)))) in Hc by (rewrite JIQ; reflexivity).
pose proof (af_client_consts RT AF Σx m14 ART14) as CC14.
assert (X4 : Y mod 4 = 0) by (unfold Y; clear - OAL; Z.div_mod_to_equations; lia).
assert (D4 : a_iq a mod 4 = 0) by (clear - IQ8; Z.div_mod_to_equations; lia).
assert (M4 : a_msp a mod 4 = 0) by (clear - MSP8; Z.div_mod_to_equations; lia).
assert (LO80 : lo <= usp + -736 - 128) by (clear - LO736 LOR DSP; unfold RT_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
assert (SPH6 : usp + -736 < 2 ^ 63) by (clear - SPT; lia).
assert (XSH14 : Y + 4 * Z.of_nat (length ys') <= SH_LO \/ SH_HI <= Y) by (rewrite LYS14; unfold Y; clear - FPHI2 FO1 FO2 FSV; unfold hid, SH_LO, SH_HI in *; lia).
assert (MSH14 : a_msp a + 4 * Z.of_nat (length (sj_iq j)) <= SH_LO \/ SH_HI <= a_msp a) by (rewrite JIQ; clear - MSPSH; unfold SH_LO, SH_HI in *; cbn; lia).
assert (XAP14 : Y + 4 * Z.of_nat (length ys') <= lo \/ usp + -736 <= Y) by (rewrite LYS14; unfold Y; left; clear - FO2 BF1 FSV; unfold hid in *; lia).
assert (MAP14 : a_msp a + 4 * Z.of_nat (length (sj_iq j)) <= lo \/ usp + -736 <= a_msp a) by (rewrite JIQ; left; clear - MSPLO; cbn; lia).
assert (DAP14 : a_iq a + 4 * Z.of_nat (length (sj_iq j)) <= lo \/ usp + -736 <= a_iq a) by (rewrite JIQ; left; clear - IQLO; cbn; lia).
assert (SEPDM14 : a_iq a + 4 * Z.of_nat (length (sj_iq j)) <= a_msp a \/ a_msp a + 4 * Z.of_nat (length (sj_iq j)) <= a_iq a) by (rewrite JIQ; clear - IQMSP; cbn; lia).
assert (SEPXM14 : Y + 4 * Z.of_nat (length ys') <= a_msp a \/ a_msp a + 4 * Z.of_nat (length (sj_iq j)) <= Y) by (rewrite LYS14, JIQ; unfold Y; clear - FMSP FO1 FO2 FSV; unfold hid in *; cbn; lia).
assert (SEPXD14 : Y + 4 * Z.of_nat (length ys') <= a_iq a \/ a_iq a + 4 * Z.of_nat (length (sj_iq j)) <= Y) by (rewrite LYS14, JIQ; unfold Y; clear - FIQ FO1 FO2 FSV; unfold hid in *; cbn; lia).
assert (PTOP : IMG_TOP_B <= Y) by (unfold Y, IMG_TOP_B; clear - FPIMG FO1 FSV; unfold hid, SEGTOP_A in *; lia).
assert (MTOP : IMG_TOP_B <= a_msp a) by (unfold IMG_TOP_B; clear - MSPIMG; unfold SEGTOP_A in *; lia).
Time cps_seg (iir_mem16_walk_ip ys' (sj_iq j) (firstn 8 (sj_msp j)) Y (a_iq a) (a_msp a) (usp + -736) lo
(Z_to_bv 64 RA_sbd_iir_n) gp (Z_to_bv 64 0x638c98) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736)) (Z_to_bv 64 (S + 20)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 S)
(Z_to_bv 64 (sbmode_struct (sbd_mode s))) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.shiftr (S + 8) 3 + SHB)) (Z_to_bv 64 f) (Z_to_bv 64 (S + 152)) (Z_to_bv 64 A) s11
m14 LMEM LYS' ORD8 OBX14 OBD14 OBM14 X4 D4 M4 ltac:(unfold Y; clear - FO1 FP0 FSV; unfold hid in *; lia) IQP MSPP LO80 LOS SPH6 XSH14 MSH14 XAP14 MAP14 DAP14 SEPDM14 SEPXM14 SEPXD14
_ _ _ _ _ _ _ _ _ _ _ YS14 IQC MSP1 FRMX ST8 PTOP MTOP CC14 MI14).
destruct POST as (t0i & t1i & t2i & a0i & a1i & a2i & a3i & a4i & a5i & a6i & a7i & t3i & t4i & t5i & t6i & Fi & fci & m15 & ysi & mvi
& -> & MU15 & WM15 & MI15 & ST15 & FRM15 & LYSI & YSI & LMVI & MVI & IQI & _).
clear YS14 MSP1 IQC ST8.

set (sF := set_sbd_first sI 1).
assert (X14 : rw_cells bsegs m14 S (SBCELLS sF a OUT j)).
{ apply sb_pieces_iff. exact (conj HD (conj FST14 (conj PT (conj LE (conj SEED (conj CFG (conj IDC PAD))))))). }
clear HD FST14 PT LE SEED CFG IDC PAD.

set (LNM := firstn 8 (sb_blocks sI S a) ++ LBL).
assert (ELNM : LBD = firstn 8 (sb_blocks sI S a) ++ (sbd_mem_sp s, a_msp a, 64) :: LBL) by (rewrite ELBD1; reflexivity).
assert (LIVNM : forall bk, In bk LNM -> In (blk_addr bk, blk_size bk) (rt_live RT Σx)).
{ intros bk Hb. apply LIVED. rewrite ELNM. apply in_app_iff. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [left; exact Hb| right; right; exact Hb]. }
assert (NMSP : forall bk, In bk LNM -> blk_addr bk <> a_msp a).
{ intros bk Hb E. pose proof NDUP as ND'. rewrite ELNM, map_app in ND'. cbn [map] in ND'. apply List.NoDup_remove_2 in ND'.
apply ND'. rewrite <- map_app. change (blk_id (sbd_mem_sp s, a_msp a, 64)) with (a_msp a). rewrite <- E. exact (in_map blk_id LNM bk Hb). }
assert (AG15 : agree_blocks bsegs m14 m15 LNM).
{ apply (agree_blocks_of_munch bsegs _ m14 m15 LNM MU15 WM15). intros bk x Hb Hx.
pose proof (LIVNM bk Hb) as LB.
destruct (frame_live_apart RT AF Σx m14 fh kh _ _ ART14 INFHX LB) as (FB & _).
destruct (live_below_lo RT AF Σx m14 _ _ lo ART14 LB LOWX) as (_ & BL & _).
pose proof (live_apart RT AF Σx m14 _ _ _ _ ART14 LB INMSP (NMSP bk Hb)) as AMS.
rewrite JIQ, LYS14. cbn [outside]. unfold Y. clear - FB BL AMS Hx FO1 FO2 FSV LO80. unfold hid in *.
split; [lia| split; [lia| split; [lia| exact I]]]. }
Ltac tra AG H bk tacR :=
lazymatch type of AG with
| agree_blocks _ ?m ?m' ?L =>
lazymatch type of H with
| rw_cells _ m ?A0 ?cs =>
let H' := fresh "T" in
assert (H' : rw_cells bsegs m' A0 cs)
by (apply (rw_cells_agree_at bsegs m m' A0 cs H); apply (agree_blocks_at bsegs m m' L bk A0 cs AG);
[ apply in_app_iff; left; cbn [sb_blocks firstn skipn In]; repeat (first [left; reflexivity | right]) | exact H | unfold blk_addr, blk_size; cbn [fst snd]; simpl_sizes; tacR | unfold blk_addr, blk_size; cbn [fst snd]; simpl_sizes; tacR ]);
clear H; rename H' into H
end
end.
unfold LNM in AG15.
tra AG15 X14 (sbd_blk sI, S, SBSTATE_SIZEOF) ltac:(unfold SBSTATE_SIZEOF; clear; lia).
tra AG15 G0C (sbd_g0_mem sI, a_g0 a, 256) ltac:(clear - JG0; lia).
tra AG15 G1C (sbd_g1_mem sI, a_g1 a, 256) ltac:(clear - JG1; lia).
tra AG15 EXC (sbd_excBuf sI, a_exc a, 4 * sbd_subframeSize sI) ltac:(cbn [sI set_sbd_submodeID sbd_subframeSize]; clear - JEXC; lia).
tra AG15 OQC (sbd_old_qlsp sI, a_oq a, 32) ltac:(clear - JOQ; lia).
tra AG15 PGC (sbd_pi_gain sI, a_pg a, 16) ltac:(clear - JPG; lia).
tra AG15 ERC (sbd_exc_rms sI, a_er a, 16) ltac:(clear - JER; lia).
assert (AGL15 : agree_blocks bsegs m14 m15 LBL) by (apply (agree_blocks_sub bsegs _ _ _ _ AG15); intros bk Hb; apply in_app_iff; right; exact Hb).
pk_blocks AGL15. clear AGL15 AG15.
destruct (frame_live_apart RT AF Σx m14 f 0%nat _ _ ART14 INF INMSP) as (FMSPf & _). change (fs_size 0) with 64 in FMSPf.
assert (PDMN : PD <> a_msp a) by (intros E; apply (PDB (sbd_mem_sp s, a_msp a, 64)); [rewrite ELBD; apply in_app_iff; left; cbn [sb_blocks In]; do 8 right; left; reflexivity| exact (eq_sym E)]).
pose proof (live_apart RT AF Σx m14 _ _ _ _ ART14 INPDX INMSP PDMN) as PDMSP.
trm MU15 WM15 OCa ltac:(rewrite LYS14, JIQ; unfold Y; cbn; clear - LWA FMSP FO1 FO2 BF1 LO80 FSV; unfold hid in *; lia).
trm MU15 WM15 OCc ltac:(rewrite LYS14, JIQ; unfold Y; cbn; clear - LWC FMSP FO1 FO2 BF1 LO80 FSV; unfold hid in *; lia).
trm MU15 WM15 SV ltac:(rewrite LYS14, JIQ; unfold Y; cbn; clear - BF1 FO2 MSPLO LO80 LO736 FSV; unfold hid in *; lia).
trm MU15 WM15 FR11 ltac:(rewrite LYS14, JIQ; unfold Y; cbn; clear - BF1 FO2 MSPLO LO80 LO736 FSV; unfold hid in *; lia).
trm MU15 WM15 FRB ltac:(rewrite LYS14, JIQ; unfold Y; cbn; clear - FFA' FO1 FO2 FMSPf BF LO80 FSV; unfold hid in *; lia).
trm MU15 WM15 FRS ltac:(rewrite LYS14, JIQ; unfold Y; cbn; clear - FPHI2 SHF1 SHF2 FO1 FO2 MSPSH BF0 LO80 FSV; unfold hid, SH_LO, SH_HI in *; lia).
trm MU15 WM15 STB ltac:(rewrite LYS14, JIQ; unfold Y; cbn; clear - HOS' FO1 FO2 FS1 FS2 FMSP BF1 LO80 FSV; unfold hid, hidp in *; lia).
trm MU15 WM15 BOBJ8 ltac:(rewrite LYS14, JIQ; unfold Y; cbn; clear - HAO' FO1 FO2 FA1 FA2 FMSP BF1 LO80 FSV; unfold hid, hidp in *; lia).
trm MU15 WM15 BDAT8 ltac:(rewrite LYS14, JIQ; unfold Y; cbn; clear - FLPD PD1 PD2 Lbs8 FO1 FO2 PDMSP BLPD LO80 FSV; unfold hid in *; lia).
trm MU15 WM15 MSP2 ltac:(rewrite LYS14, JIQ; unfold Y; cbn; rewrite length_skipn, JMSP; cbn; clear - FMSP FO1 FO2 MSPLO LO80 FSV; unfold hid in *; lia).

set (j2 := SBJ (sj_last_ener j) (sj_seed j) (sj_pad1 j) (sj_pad2 j) (sj_g0 j) (sj_g1 j) (sj_exc j) (sj_oq j) (sj_iq j) (mvi ++ skipn 8 (sj_msp j)) (sj_pg j) (sj_er j)).
assert (MSPX : rw_cells bsegs m15 (a_msp a) (f32 (mvi ++ skipn 8 (sj_msp j)))).
{ apply f32_join; [exact MVI|]. rewrite LMVI, JIQ. exact MSP2. }
assert (BUFS15 : sb_bufs bsegs m15 a j2) by (exact (conj G0C (conj G1C (conj EXC (conj OQC (conj IQI (conj MSPX (conj PGC ERC)))))))).
assert (JOK2 : sb_junk_ok sF j2).
{ unfold sb_junk_ok. repeat split; cbn [j2 sj_pad1 sj_pad2 sj_g0 sj_g1 sj_exc sj_oq sj_iq sj_msp sj_pg sj_er];
first [ assumption
| rewrite length_app, length_skipn, LMVI, JIQ, JMSP; reflexivity
| unfold sF, sI; cbn [set_sbd_first set_sbd_submodeID sbd_subframeSize]; exact JEXC ]. }
assert (X15 : rw_cells bsegs m15 S (SBCELLS sF a OUT j2)) by (exact X14).
clear G0C G1C EXC OQC IQI MSPX MVI MSP2 PGC ERC X14.

assert (ART15 : X14x.ART RT Σx m15).
{ apply (af_frame RT AF Σx m14 m15 lo ART14 LOWX); [| exact WM15]. intros a0 Ha. apply MU15. rewrite LYS14, JIQ. cbn [outside]. unfold Y.
split; [| split; [| split; [| exact I]]].
- intros Hin. apply Ha. right; right; right; left. exists fh, kh. split; [exact INFHX | clear - Hin FO1 FO2 FSV; unfold hid in *; lia].
- intros Hin. apply Ha. right; right; left. exists (a_msp a), 64. split; [exact INMSP | clear - Hin; lia].
- intros Hin. apply Ha. left. clear - Hin LO80 SPT; unfold USTACK_TOP in *; lia. }
assert (PF15 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m15).
{ apply (pres_fp_trans _ _ _ _ m m14 m15 PF). apply (pres_fp_of_munch _ _ _ _ _ m14 m15 MU15). intros x Hx Ho. rewrite LYS14, JIQ. cbn [outside] in Ho |- *.
destruct Ho as (_ & HO & _ & Ho). apply sb_outside_app_inv in Ho. destruct Ho as [Hb _].
assert (HM : ~ (a_msp a <= x < a_msp a + 64)).
{ rewrite ELNM in Hb. apply outside_blocks_app_r in Hb. cbn [blocks_ivs map outside blk_addr blk_size fst snd] in Hb. exact (proj1 Hb). }
pose proof (SPL x Hx) as SPX.
split; [intros Hin; apply HO; unfold Y in Hin; clear - Hin FSV; unfold hid in *; lia|].
split; [intros Hin; apply HM; clear - Hin; lia|]. split; [| exact I]. clear - SPX LOW LO80. intros Hin. destruct SPX as [SX|SX]; lia. }
clear PF. rename PF15 into PF.
assert (OF15 : offsh [(Y, Y + 4 * Z.of_nat (length ys')); (a_msp a, a_msp a + 4 * Z.of_nat (length (sj_iq j))); (usp + -736 + -128, usp + -736)]).
{ rewrite LYS14, JIQ. cbn [offsh]. unfold Y. clear - FPHI2 FO1 FO2 MSPSH LOS LO80 FSV. unfold hid, SH_LO, SH_HI in *. cbn. lia. }
assert (ACC15 : forall o n, acc bsegs m14 o n -> 0 <= o -> o + n <= 140737488355328 -> acc bsegs m15 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch bsegs _ m14 m15 o n (conj H0 (conj H1 H)) MU15 (shfree_of_offsh _ o n OF15 H0 H1)))). }
assert (ACA15 : acc bsegs m15 A 48) by (apply ACC15; [exact ACA14| clear - FA1 FP0; lia| clear - FA2 BF1 LO736 SPT; lia]).
assert (ACO15 : acc bsegs m15 OUT 8000) by (apply ACC15; [exact ACO14| clear - FO1 FP0; lia| clear - FO2 BF1 LO736 SPT; lia]).
assert (ACT15 : acc bsegs m15 STEREO 24) by (apply ACC15; [exact ACT14| clear - FS1 FP0; lia| clear - FS2 BF1 LO736 SPT; lia]).
assert (SSP15 : io_ssp m15).
{ apply (sbd_io_ssp_agree m14 m15 SSP14 (AF_DRV Σx m15 ART15)). intros a0 Ha. apply MU15. unfold X0r9.SSP_GUARD in Ha. rewrite LYS14, JIQ. cbn [outside]. unfold Y.
clear - Ha FO1 FPIMG MSPIMG LO80 LOS FSV. unfold hid, SEGTOP_A in *. split; [lia| split; [cbn; lia| split; [lia| exact I]]]. }
assert (KEEP : forall P, fp_local IO_FP P -> P m14 -> P m15).
{ intros P L Pm. apply (fp_local_munch IO_FP P _ m14 m15 L IO_img MU15); [| exact Pm]. intros x Hx. unfold SEGTOP_A in Hx. rewrite LYS14, JIQ. cbn [outside]. unfold Y.
clear - Hx FO1 FPIMG MSPIMG LO80 LOS FSV. unfold hid, SEGTOP_A in *. split; [lia| split; [cbn; lia| split; [lia| exact I]]]. }
pk_io ERR_rep OUT_rep KEEP. clear KEEP ACA14 ACO14 ACT14 SSP14 ACC15 ART14.

destruct (af_acc_live RT AF Σx m15 S 160 ART15 INLX) as (_ & ACS15).
assert (OBS15 : aobj bsegs m15 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO736 SPT; unfold APP_TOP; lia| exact ACS15]).
sb_unpack X15 as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
assert (LO624 : lo <= usp + -736 - 16) by (clear - LO80; lia).
cps_seg (sbd_n4b usp lo S OUT A f (sbmode_struct (sbd_mode s)) fsz
(fupds (fupds g [(47%nat, Z_to_bv 64 (S + 144)); (48%nat, Z_to_bv 64 (S + 152))]) [(45%nat, Z_to_bv 64 (Z.shiftr (S + 144) 3 + SHB)); (44%nat, Z_to_bv 64 (Z.shiftr (S + 152) 3 + SHB))])
(Z_to_bv 64 0) sF a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
FR11 ltac:(cbn [fupds Nat.eqb]; exact G27) ltac:(cbn [fupds Nat.eqb]; exact G45) ltac:(gslot) ltac:(gslot) ltac:(gslot) ltac:(gslot) HD PT eq_refl
ltac:(unfold sF, sI; cbn [set_sbd_first set_sbd_submodeID sbd_full_frame_size]; exact IFFS) ltac:(clear - FSV; unfold hid in *; lia)
OBS15 S8 SPOS BS1 SOFF ltac:(clear - FO1 FP0; lia) ltac:(clear - FO2 BF1 LO736 SPT; lia) ST15 LO624 LOS SPH MI15).
destruct POST as (m16 & ja & -> & MU16 & WM16 & MI16 & ST16 & ARG16).
clear HD FST PT LE SEED CFG IDC PAD OBS15 ACS15 ST15 MI15.
pk_munch_all MU16 WM16 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LO624; cbn [outside]; split; [lia| exact I])
ltac:(fun x Hx => clear - Hx LO624 LOS; cbn [outside]; split; [lia| exact I]).
trm MU16 WM16 OCa ltac:(clear - LWA FO1 FO2 BF1 LO624 FSV; unfold hid in *; lia).
trm MU16 WM16 YSI ltac:(unfold Y; clear - LYSI LYS14 FO1 FO2 BF1 LO624 FSV; unfold hid in *; lia).
trm MU16 WM16 OCc ltac:(clear - LWC FO1 FO2 BF1 LO624 FSV; unfold hid in *; lia).
trm MU16 WM16 SV ltac:(clear; lia).
trm MU16 WM16 FR11 ltac:(clear; lia).
trm MU16 WM16 FRB ltac:(clear - BF LO624; lia).
trm MU16 WM16 FRS ltac:(clear - BF0 LO624; lia).
trm MU16 WM16 STB ltac:(clear - FS1 FS2 BF1 LO624; lia).
trm MU16 WM16 BOBJ8 ltac:(clear - FA1 FA2 BF1 LO624; lia).
trm MU16 WM16 BDAT8 ltac:(clear - BLPD PD1 PD2 Lbs8 LO624; lia).
trm MU16 WM16 X15 ltac:(clear - BS1 LO624; lia).
assert (ART16 : X14x.ART RT Σx m16).
{ apply (af_frame RT AF Σx m15 m16 lo ART15 LOWX); [| exact WM16]. intros a0 Ha. apply MU16. cbn [outside]. split; [| exact I].
intros Hin. apply Ha. left. clear - Hin LO624 SPT; unfold USTACK_TOP in *; lia. }
assert (PF16 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m16).
{ apply (pres_fp_trans _ _ _ _ m m15 m16 PF). apply (pres_fp_of_munch _ _ _ _ _ m15 m16 MU16). intros x Hx _. cbn [outside].
pose proof (SPL x Hx) as SPX. split; [| exact I]. clear - SPX LOW LO624. intros Hin. destruct SPX as [SX|SX]; lia. }
clear PF ART15. rename PF16 into PF.
assert (OF16 : offsh [(usp + -752, usp + -736)]) by (cbn [offsh]; clear - LOS LO624; unfold SH_LO, SH_HI in *; lia).
assert (ACC16 : forall o n, acc bsegs m15 o n -> 0 <= o -> o + n <= 140737488355328 -> acc bsegs m16 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch bsegs _ m15 m16 o n (conj H0 (conj H1 H)) MU16 (shfree_of_offsh _ o n OF16 H0 H1)))). }
assert (ACA16 : acc bsegs m16 A 48) by (apply ACC16; [exact ACA15| clear - FA1 FP0; lia| clear - FA2 BF1 LO736 SPT; lia]).
assert (ACO16 : acc bsegs m16 OUT 8000) by (apply ACC16; [exact ACO15| clear - FO1 FP0; lia| clear - FO2 BF1 LO736 SPT; lia]).
assert (ACT16 : acc bsegs m16 STEREO 24) by (apply ACC16; [exact ACT15| clear - FS1 FP0; lia| clear - FS2 BF1 LO736 SPT; lia]).
assert (SSP16 : io_ssp m16).
{ apply (sbd_io_ssp_agree m15 m16 SSP15 (AF_DRV Σx m16 ART16)). intros a0 Ha. apply MU16. unfold X0r9.SSP_GUARD in Ha. cbn [outside].
clear - Ha LO624 LOS. split; [lia| exact I]. }
clear ACA15 ACO15 ACT15 SSP15 ACC16.

destruct BUFS15 as (G0C & G1C & EXC & OQC & IQC & MSPC & PGC & ERC).
assert (YJ : rw_cells bsegs m16 OUT (f32 (wa ++ ysi))).
{ apply f32_join; [exact OCa|]. replace (OUT + 4 * Z.of_nat (length wa)) with Y by (unfold Y; rewrite LWA; reflexivity). exact YSI. }
assert (LYJ : Z.of_nat (length (wa ++ ysi)) = 2 * fsz) by (rewrite length_app, LYSI; clear - LWA LYS14; lia).
clear OCa YSI.
assert (ING0 : In (a_g0 a, 256) (rt_live RT Σx)) by (apply (LIVED (sbd_g0_mem s, a_g0 a, 256)); rewrite ELBD; apply in_app_iff; left; cbn [sb_blocks In]; do 1 right; left; reflexivity).
assert (ING1 : In (a_g1 a, 256) (rt_live RT Σx)) by (apply (LIVED (sbd_g1_mem s, a_g1 a, 256)); rewrite ELBD; apply in_app_iff; left; cbn [sb_blocks In]; do 2 right; left; reflexivity).
assert (NEG01 : a_g0 a <> a_g1 a).
{ intros E. pose proof NDUP as ND'. rewrite ELBD, map_app in ND'. apply List.NoDup_app_remove_r in ND'.
cbn [sb_blocks map blk_id blk_addr fst snd] in ND'. do 1 (apply List.NoDup_cons_iff in ND'; destruct ND' as [_ ND']).
apply List.NoDup_cons_iff in ND'. destruct ND' as [NI _]. apply NI. rewrite E. cbn [In]. left; reflexivity. }
pose proof (live_apart RT AF Σx m16 _ _ _ _ ART16 ING0 ING1 NEG01) as G01.
assert (AL8b : sb_addrs_al a) by (apply (sb_addrs_al_of_blocks s S a); intros bk Hb; apply LAL8; rewrite ELBD; apply in_app_iff; left; exact Hb).
destruct AL8b as (G08 & G18 & _).
assert (EU624 : bv_unsigned (Z_to_bv 64 (usp + -752)) = usp + -752) by (apply unsigned_lit; clear - SPT LO624 LOS; lia).
assert (QN : 2 * fsz = 320 \/ 2 * fsz = 640) by (clear - FSV; unfold hid in *; lia).
assert (EA1 : Z_to_bv 64 (OUT + 4 * fsz) = Z_to_bv 64 (OUT + 2 * (2 * fsz))) by (f_equal; clear; lia).
assert (EA2 : Z_to_bv 64 sb_A_H0 = Z_to_bv 64 0x27000) by reflexivity.
cps_rt (QMF16 (2 * fsz) QN Σx (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m16
OUT (a_g0 a) (a_g1 a) lo fh (a_g0 a) 256 (a_g1 a) 256 kh (wa ++ ysi) (sj_g0 j2) (sj_g1 j2)
FDO MST eq_refl EA1 EA2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
YJ LYJ INFHX FO1 ltac:(clear - FO2 FSV; unfold hid in *; lia)
(acc_sub bsegs m16 OUT 8000 OUT (4 * (2 * fsz)) ACO16 ltac:(clear; lia) ltac:(clear - FSV; unfold hid in *; lia)) OAL
G0C JG0 ING0 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - G08; Z.div_mod_to_equations; lia)
G1C JG1 ING1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - G18; Z.div_mod_to_equations; lia)
ltac:(clear - G01; lia)
ltac:(rewrite EU624; apply (pois_above_le _ usp); [rewrite EPX; exact POA| clear; lia]) FRM15 ART16 MI16
ltac:(rewrite EU624; exact ST16) LOWX
ltac:(rewrite EU624; clear - LOR DSP; unfold RT_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)
ltac:(rewrite EU624; clear - SPT; unfold USTACK_TOP in *; lia)
ltac:(rewrite EU624; clear - SPA; Z.div_mod_to_equations; lia)).
intros cq (Σq & Hcq & LVq & FRq & SPq & CRq & POq).
cps_unpack_lib Hcq as (vq & m17 & ysq & g0q & g1q & RSq & (ART17 & MI17 & WM17 & ST17) & PRES17 & YSQ & LYSQ & G0Q & LG0Q & G1Q & LG1Q & ACQ).
try rewrite EU624 in PRES17. try rewrite EU624 in ST17.
clear YJ G0C G1C.
assert (CLF : forall x, fh <= x < fh + fs_size kh - 8 -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -752) x)
by (intros x Hx; right; right; right; left; exists fh, kh; split; [exact INFHX| exact Hx]).
assert (CLS : forall x, usp + -752 <= x < usp -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -752) x)
by (intros x Hx; left; clear - Hx SPT; unfold USTACK_TOP in *; lia).
assert (CLL : forall p n x, In (p, n) (rt_live RT Σx) -> p <= x < p + n -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -752) x)
by (intros p n x Hp Hx; right; right; left; exists p, n; split; [exact Hp| exact Hx]).
assert (CLF0 : forall x, f <= x < f + 56 -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -752) x)
by (intros x Hx; right; right; right; left; exists f, 0%nat; split; [exact INF| change (fs_size 0) with 64; clear - Hx; lia]).
assert (CLSF : forall x, sf <= x < sf + 8 -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -752) x)
by (intros x Hx; right; right; right; right; exists f, 0%nat; split; [exact INF| change (fs_size 0) with 64; rewrite <- SHF, SHF0; clear - Hx; lia]).
destruct (frame_live_apart RT AF Σx m16 fh kh _ _ ART16 INFHX ING0) as (FG0 & _). destruct (frame_live_apart RT AF Σx m16 fh kh _ _ ART16 INFHX ING1) as (FG1 & _).
destruct (frame_live_apart RT AF Σx m16 f 0%nat _ _ ART16 INF ING0) as (FG0f & FG0s). destruct (frame_live_apart RT AF Σx m16 f 0%nat _ _ ART16 INF ING1) as (FG1f & FG1s).
change (fs_size 0) with 64 in FG0f, FG0s, FG1f, FG1s. rewrite SHF0, <- SHF in FG0s, FG1s.
destruct (live_below_lo RT AF Σx m16 _ _ lo ART16 ING0 LOWX) as (_ & G0LO & _). destruct (live_below_lo RT AF Σx m16 _ _ lo ART16 ING1 LOWX) as (_ & G1LO & _).
assert (SG0N : S <> a_g0 a).
{ intros E. pose proof NDUP as ND'. rewrite ELBD, map_app in ND'. apply List.NoDup_app_remove_r in ND'.
cbn [sb_blocks map blk_id blk_addr fst snd] in ND'. apply List.NoDup_cons_iff in ND'. destruct ND' as [NI _]. apply NI. rewrite E. cbn [In]. left; reflexivity. }
assert (SG1N : S <> a_g1 a).
{ intros E. pose proof NDUP as ND'. rewrite ELBD, map_app in ND'. apply List.NoDup_app_remove_r in ND'.
cbn [sb_blocks map blk_id blk_addr fst snd] in ND'. apply List.NoDup_cons_iff in ND'. destruct ND' as [NI _]. apply NI. rewrite E. cbn [In]. right; left; reflexivity. }
pose proof (live_apart RT AF Σx m16 _ _ _ _ ART16 INLX ING0 SG0N) as SG0. pose proof (live_apart RT AF Σx m16 _ _ _ _ ART16 INLX ING1 SG1N) as SG1.
assert (PDG0N : PD <> a_g0 a) by (intros E; apply (PDB (sbd_g0_mem s, a_g0 a, 256)); [rewrite ELBD; apply in_app_iff; left; cbn [sb_blocks In]; do 1 right; left; reflexivity| exact (eq_sym E)]).
assert (PDG1N : PD <> a_g1 a) by (intros E; apply (PDB (sbd_g1_mem s, a_g1 a, 256)); [rewrite ELBD; apply in_app_iff; left; cbn [sb_blocks In]; do 2 right; left; reflexivity| exact (eq_sym E)]).
pose proof (live_apart RT AF Σx m16 _ _ _ _ ART16 INPDX ING0 PDG0N) as PDG0. pose proof (live_apart RT AF Σx m16 _ _ _ _ ART16 INPDX ING1 PDG1N) as PDG1.
assert (OUTQ : forall x, (x < OUT \/ OUT + 8 * fsz <= x) -> (x < a_g0 a \/ a_g0 a + 256 <= x) -> (x < a_g1 a \/ a_g1 a + 256 <= x) ->
outside [(OUT, OUT + 4 * (2 * fsz)); (a_g0 a, a_g0 a + 256); (a_g1 a, a_g1 a + 256)] x)
by (intros x H1 H2 H3; cbn [outside]; split; [clear - H1; lia| split; [clear - H2; lia| split; [clear - H3; lia| exact I]]]).
tr1 PRES17 WM17 OCc ltac:(fun x Hx => apply CLF; clear - Hx LWC FO1 FO2 FSV; unfold hid in *; lia)
ltac:(fun x Hx => apply OUTQ; [clear - Hx LWC FSV; unfold hid in *; lia | clear - Hx LWC FO1 FO2 FG0 FSV; unfold hid in *; lia | clear - Hx LWC FO1 FO2 FG1 FSV; unfold hid in *; lia]).
tr1 PRES17 WM17 SV ltac:(fun x Hx => apply CLS; clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; [clear - Hx BF1 FO2 LO736 FSV; unfold hid in *; lia | clear - Hx G0LO LO736; lia | clear - Hx G1LO LO736; lia]).
tr1 PRES17 WM17 FR11 ltac:(fun x Hx => apply CLS; clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; [clear - Hx BF1 FO2 LO736 FSV; unfold hid in *; lia | clear - Hx G0LO LO736; lia | clear - Hx G1LO LO736; lia]).
tr1 PRES17 WM17 ARG16 ltac:(fun x Hx => apply CLS; clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; [clear - Hx BF1 FO2 LO624 FSV; unfold hid in *; lia | clear - Hx G0LO LO624; lia | clear - Hx G1LO LO624; lia]).
tr1 PRES17 WM17 FRB ltac:(fun x Hx => apply CLF0; clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; [clear - Hx FFA' FO1 FO2 FSV; unfold hid in *; lia | clear - Hx FG0f; lia | clear - Hx FG1f; lia]).
tr1 PRES17 WM17 FRS ltac:(fun x Hx => apply CLSF; clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; [clear - Hx FPHI2 SHF1 SHF2 FO1 FO2 FSV; unfold hid, SH_LO, SH_HI in *; lia | clear - Hx FG0s; lia | clear - Hx FG1s; lia]).
tr1 PRES17 WM17 STB ltac:(fun x Hx => apply CLF; clear - Hx FS1 FS2; lia)
ltac:(fun x Hx => apply OUTQ; [clear - Hx HOS' FO1 FO2 FS1 FS2 FSV; unfold hid, hidp in *; lia | clear - Hx FS1 FS2 FG0; lia | clear - Hx FS1 FS2 FG1; lia]).
tr1 PRES17 WM17 BOBJ8 ltac:(fun x Hx => apply CLF; clear - Hx FA1 FA2; lia)
ltac:(fun x Hx => apply OUTQ; [clear - Hx HAO' FO1 FO2 FA1 FA2 FSV; unfold hid, hidp in *; lia | clear - Hx FA1 FA2 FG0; lia | clear - Hx FA1 FA2 FG1; lia]).
tr1 PRES17 WM17 BDAT8 ltac:(fun x Hx => apply (CLL PD ND x INPDX); clear - Hx PD1 PD2 Lbs8; lia)
ltac:(fun x Hx => apply OUTQ; [clear - Hx FLPD FO1 FO2 PD1 PD2 Lbs8 FSV; unfold hid in *; lia | clear - Hx PDG0 PD1 PD2 Lbs8; lia | clear - Hx PDG1 PD1 PD2 Lbs8; lia]).
tr1 PRES17 WM17 X15 ltac:(fun x Hx => apply (CLL S 160 x INLX); clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; [clear - Hx SFH' FO1 FO2 FSV; unfold hid in *; lia | clear - Hx SG0; lia | clear - Hx SG1; lia]).
Ltac tra AG H bk tacR ::=
lazymatch type of AG with
| agree_blocks _ ?m ?m' ?L =>
lazymatch type of H with
| rw_cells _ m ?A0 ?cs =>
let H' := fresh "T" in
assert (H' : rw_cells bsegs m' A0 cs)
by (apply (rw_cells_agree_at bsegs m m' A0 cs H); apply (agree_blocks_at bsegs m m' L bk A0 cs AG);
[ apply in_app_iff; left; cbn [sb_blocks firstn skipn In]; repeat (first [left; reflexivity | right]) | exact H | unfold blk_addr, blk_size; cbn [fst snd]; simpl_sizes; tacR | unfold blk_addr, blk_size; cbn [fst snd]; simpl_sizes; tacR ]);
clear H; rename H' into H
end
end.

set (LNG := skipn 3 (sb_blocks sI S a) ++ LBL).
assert (ELNG : LBD = (sbd_blk sI, S, SBSTATE_SIZEOF) :: (sbd_g0_mem sI, a_g0 a, 256) :: (sbd_g1_mem sI, a_g1 a, 256) :: LNG) by (rewrite ELBD1; reflexivity).
assert (NG : forall bk, In bk LNG -> blk_addr bk <> a_g0 a /\ blk_addr bk <> a_g1 a).
{ intros bk Hb. pose proof NDUP as ND'. rewrite ELNG in ND'. cbn [map] in ND'.
apply List.NoDup_cons_iff in ND'. destruct ND' as [_ ND']. apply List.NoDup_cons_iff in ND'. destruct ND' as [N0 ND']. apply List.NoDup_cons_iff in ND'. destruct ND' as [N1 _].
cbn [blk_id blk_addr fst snd] in N0, N1.
split; intros E; [apply N0; right| apply N1]; rewrite <- E; exact (in_map blk_id LNG bk Hb). }
assert (LIVNG : forall bk, In bk LNG -> In (blk_addr bk, blk_size bk) (rt_live RT Σx))
by (intros bk Hb; apply LIVED; rewrite ELNG; right; right; right; exact Hb).
assert (AG17 : agree_blocks bsegs m16 m17 LNG).
{ apply (agree_blocks_of_pres_fp RT Σx _ _ _ m16 m17 LNG PRES17 WM17 LIVNG). intros bk x Hb Hx. pose proof (LIVNG bk Hb) as LB.
destruct (frame_live_apart RT AF Σx m16 fh kh _ _ ART16 INFHX LB) as (FB & _).
destruct (NG bk Hb) as (N0 & N1).
pose proof (live_apart RT AF Σx m16 _ _ _ _ ART16 LB ING0 N0) as A0. pose proof (live_apart RT AF Σx m16 _ _ _ _ ART16 LB ING1 N1) as A1.
apply OUTQ; [clear - FB Hx FO1 FO2 FSV; unfold hid in *; lia | clear - A0 Hx; lia | clear - A1 Hx; lia]. }
unfold LNG in AG17.
tra AG17 EXC (sbd_excBuf sI, a_exc a, 4 * sbd_subframeSize sI) ltac:(unfold j2, sI; cbn [sj_exc set_sbd_submodeID sbd_subframeSize]; clear - JEXC; lia).
tra AG17 OQC (sbd_old_qlsp sI, a_oq a, 32) ltac:(unfold j2; cbn [sj_oq]; clear - JOQ; lia).
tra AG17 IQC (sbd_interp_qlpc sI, a_iq a, 32) ltac:(unfold j2; cbn [sj_iq]; clear - JIQ; lia).
tra AG17 MSPC (sbd_mem_sp sI, a_msp a, 64) ltac:(unfold j2; cbn [sj_msp]; rewrite ?length_app, ?length_skipn, ?LMVI, ?JIQ, ?JMSP; cbn; clear; lia).
tra AG17 PGC (sbd_pi_gain sI, a_pg a, 16) ltac:(unfold j2; cbn [sj_pg]; clear - JPG; lia).
tra AG17 ERC (sbd_exc_rms sI, a_er a, 16) ltac:(unfold j2; cbn [sj_er]; clear - JER; lia).
assert (AGL17 : agree_blocks bsegs m16 m17 LBL) by (apply (agree_blocks_sub bsegs _ _ _ _ AG17); intros bk Hb; apply in_app_iff; right; exact Hb).
pk_blocks AGL17. clear AGL17 AG17.

set (j3 := SBJ (sj_last_ener j) (sj_seed j) (sj_pad1 j) (sj_pad2 j) g0q g1q (sj_exc j) (sj_oq j) (sj_iq j) (mvi ++ skipn 8 (sj_msp j)) (sj_pg j) (sj_er j)).
assert (BUFS17 : sb_bufs bsegs m17 a j3) by (exact (conj G0Q (conj G1Q (conj EXC (conj OQC (conj IQC (conj MSPC (conj PGC ERC)))))))).
assert (JOK3 : sb_junk_ok sF j3).
{ unfold sb_junk_ok. repeat split; cbn [j3 sj_pad1 sj_pad2 sj_g0 sj_g1 sj_exc sj_oq sj_iq sj_msp sj_pg sj_er];
first [ assumption
| rewrite length_app, length_skipn, LMVI, JIQ, JMSP; reflexivity
| unfold sF, sI; cbn [set_sbd_first set_sbd_submodeID sbd_subframeSize]; exact JEXC ]. }
assert (X17 : rw_cells bsegs m17 S (SBCELLS sF a OUT j3)) by (exact X15).
clear G0Q G1Q EXC OQC IQC MSPC PGC ERC X15.
assert (OC17 : rw_cells bsegs m17 OUT (f32 (ysq ++ wc))).
{ apply f32_join; [exact YSQ|]. replace (OUT + 4 * Z.of_nat (length ysq)) with (OUT + 4 * fsz + 4 * fsz) by (rewrite LYSQ; clear; lia). exact OCc. }
assert (LOWS17 : length (ysq ++ wc) = 2000%nat) by (rewrite length_app; clear - LYSQ LWC FSV; unfold hid in *; lia).
clear YSQ OCc.

assert (PF17 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m17).
{ apply (pres_fp_trans _ _ _ _ m m16 m17 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σx) (rt_frames RT Σx) (usp + -752) _ m16 m17 PRES17).
- intros e He. rewrite ELX. exact He.
- intros e He. rewrite EFX. right. exact He.
- clear; lia.
- intros x Hx Ho. cbn [outside] in Ho. destruct Ho as (_ & HO & _ & Ho). apply sb_outside_app_inv in Ho. destruct Ho as [Hb _].
rewrite ELNG in Hb. cbn [blocks_ivs map outside blk_addr blk_size fst snd] in Hb. destruct Hb as (_ & H0 & H1 & _).
apply OUTQ; [clear - HO FSV; unfold hid in *; lia | clear - H0; lia | clear - H1; lia]. }
clear PF. rename PF17 into PF.
assert (SHQ : forall o n, fh <= o -> o + n <= fh + fs_size kh -> forall i, 0 <= i < n -> outside [(OUT, OUT + 4 * (2 * fsz)); (a_g0 a, a_g0 a + 256); (a_g1 a, a_g1 a + 256)] (shad (o + i))).
{ intros o n H1 H2 i Hi.
assert (SR : SH_LO <= shad (o + i) < SH_HI).
{ pose proof (frame_facts RT AF Σx m16 fh kh ART16 INFHX) as (_ & _ & _ & _ & _ & _ & SA & SL & SH & _). split.
- unfold shad, SH_LO, SHB in *. assert (0 <= (o + i) / 8) by (apply Z.div_pos; lia). lia.
- assert (shad (o + i) < shad (fh + fs_size kh)); [| lia].
unfold shad. apply Z.add_lt_mono_r. apply Z.div_lt_upper_bound; [lia|].
assert (FH8 : fh mod 8 = 0) by (clear - FP64; Z.div_mod_to_equations; lia).
assert (FK8 : fs_size kh mod 8 = 0) by (destruct FS64 as (M64 & _); clear - M64; Z.div_mod_to_equations; lia).
assert (E : fh + fs_size kh = 8 * ((fh + fs_size kh) / 8)).
{ pose proof (Z.div_mod (fh + fs_size kh) 8 ltac:(lia)) as XD. rewrite Zplus_mod, FH8, FK8 in XD. cbn in XD. lia. }
lia. }
pose proof (live_facts RT AF Σx m16 _ _ ART16 ING0) as (_ & _ & _ & G0SH). pose proof (live_facts RT AF Σx m16 _ _ ART16 ING1) as (_ & _ & _ & G1SH).
apply OUTQ; [clear - SR FPHI2 FO1 FO2 FSV; unfold hid, SH_LO, SH_HI in *; lia | clear - SR G0SH; unfold SH_LO, SH_HI in *; lia | clear - SR G1SH; unfold SH_LO, SH_HI in *; lia]. }
assert (FH8 : fh mod 8 = 0) by (clear - FP64; Z.div_mod_to_equations; lia).
assert (FK8 : fs_size kh mod 8 = 0) by (destruct FS64 as (M64 & _); clear - M64; Z.div_mod_to_equations; lia).
assert (ACA17 : acc bsegs m17 A 48)
by (apply (acc_pres_fp_frame _ _ _ _ m16 m17 fh kh A 48 PRES17 INFHX FH8 FK8 ltac:(clear - FP0; lia) FA1 ltac:(clear - FA2; lia) (SHQ A 48 FA1 ltac:(clear - FA2; lia)) ACA16)).
assert (ACO17 : acc bsegs m17 OUT 8000)
by (apply (acc_pres_fp_frame _ _ _ _ m16 m17 fh kh OUT 8000 PRES17 INFHX FH8 FK8 ltac:(clear - FP0; lia) FO1 ltac:(clear - FO2; lia) (SHQ OUT 8000 FO1 ltac:(clear - FO2; lia)) ACO16)).
assert (ACT17 : acc bsegs m17 STEREO 24)
by (apply (acc_pres_fp_frame _ _ _ _ m16 m17 fh kh STEREO 24 PRES17 INFHX FH8 FK8 ltac:(clear - FP0; lia) FS1 ltac:(clear - FS2; lia) (SHQ STEREO 24 FS1 ltac:(clear - FS2; lia)) ACT16)).
assert (SSP17 : io_ssp m17).
{ apply (sbd_io_ssp_agree m16 m17 SSP16 (AF_DRV Σq m17 ART17)). intros a0 Ha. apply PRES17; [right; left; exact (sbd_ssp_static _ Ha)|].
unfold X0r9.SSP_GUARD in Ha. pose proof (af_live_small RT AF Σx m16 _ _ ART16 ING0 ltac:(clear; lia)) as G0I. pose proof (af_live_small RT AF Σx m16 _ _ ART16 ING1 ltac:(clear; lia)) as G1I.
apply OUTQ; [clear - Ha FO1 FPIMG; unfold SEGTOP_A in *; lia | clear - Ha G0I; unfold SEGTOP_A in *; lia | clear - Ha G1I; unfold SEGTOP_A in *; lia]. }
pk_io_fp PRES17 ERR_rep OUT_rep IO_FP IO_img ltac:(fun y Hy => pose proof (af_live_small RT AF Σx m16 _ _ ART16 ING0 ltac:(clear; lia)) as G0I;
pose proof (af_live_small RT AF Σx m16 _ _ ART16 ING1 ltac:(clear; lia)) as G1I;
apply OUTQ; [clear - Hy FO1 FPIMG; unfold SEGTOP_A in *; lia | clear - Hy G0I; unfold SEGTOP_A in *; lia | clear - Hy G1I; unfold SEGTOP_A in *; lia]).
clear ACA16 ACO16 ACT16 SSP16 PRES17 ART16 SHQ.
clear Hc.

cps_seg (sbd_n5 usp lo S OUT A f (sbmode_struct (sbd_mode s)) (Z_to_bv 64 0) ja _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ARG16 ST17 ltac:(clear - LO624; lia) SPH MI17).
destruct POST as (-> & ST17').
assert (EFq : rt_frames RT Σq = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRq; exact EFX).
assert (ELq : rt_live RT Σq = rt_live RT Σ) by (rewrite LVq; exact ELX).
assert (ESq : rt_sp0 RT Σq = rt_sp0 RT Σ) by (rewrite SPq; exact ESX).
assert (EPq : rt_pois RT Σq = rt_pois RT Σ) by (rewrite POq; exact EPX).
assert (INVF : sb_inv sF).
{ destruct INV1 as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12). unfold sb_inv, sF. cbn [set_sbd_first sbd_mode sbd_frame_size sbd_full_frame_size
sbd_subframeSize sbd_nbSubframes sbd_lpcSize sbd_first sbd_sampling_rate sbd_lpc_enh_enabled sbd_encode_submode sbd_submodeID sbd_innov_save].
refine (conj I1 (conj I2 (conj I3 (conj I4 (conj I5 (conj I6 (conj (or_intror eq_refl) (conj I8 (conj I9 (conj I10 (conj I11 I12))))))))))). }
assert (REPX : DREP OUT STEREO m17 S (DecSB sF low3) LBD).
{ cbn [decst_rep]. exists a, j3, LBL. split; [exact ELBD1|]. split; [exact S8|]. split; [exact SPOS|]. split; [exact INVF|]. split; [exact JOK3|].
split; [exact X17|]. split; [exact BUFS17|]. exists OUT. exact RLOW. }
assert (BREPX : bits_rep bsegs m17 A D (sbw_bits b1)).
{ split; [exists rj8; split; [exact Lrj8| unfold bits_cells; exact BOBJ8]|].
split; [exists bs8; split; [apply (proj2 (u8arr_rw_CB m17 D bs8)); exact BDAT8| exact Hbs8]| exact BSIDE8]. }
assert (PD2X : D + sb_buf_size (sbw_bits b1) <= PD + ND) by (rewrite BSZ8; exact PD2).
assert (WMX : wmono bsegs m m17) by (eapply wmono_trans; [exact WM0|]; eapply wmono_trans; [exact WM8|]; eapply wmono_trans; [exact WM9|];
eapply wmono_trans; [exact WM11|]; eapply wmono_trans; [exact WM14|]; eapply wmono_trans; [exact WM15|];
eapply wmono_trans; [exact WM16| exact WM17]).
cps_rt (sbd_exit_cps RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AUN_lo AUN_nop Σ Σq F0 fs0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m m17 lo S OUT STEREO A D f fh PD ND kh LBD
(fupds (fupds g [(47%nat, Z_to_bv 64 (S + 144)); (48%nat, Z_to_bv 64 (S + 152))]) [(45%nat, Z_to_bv 64 (Z.shiftr (S + 144) 3 + SHB)); (44%nat, Z_to_bv 64 (Z.shiftr (S + 152) 3 + SHB))])
0 0 (DecSB sF low3) (sbw_bits b1) (ysq ++ wc) stb j24 j36 (Z_to_bv 64 dtx)
EFq ELq ESq EPq ART0 POA NAF LIVE INPD PD1 PD2X INFH FA1 FA2 ACA FO1 FO2 ACO FS1 FS2 ACST ART17 MI17 RSq ST17' LOW
ltac:(clear - LOR DSP; unfold RT_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia) SPT SPA PF WMX FR11
ltac:(cbn [fupds Nat.eqb]; exact G13) ltac:(cbn [fupds Nat.eqb]; exact G52) ltac:(cbn [fupds Nat.eqb]; exact G51)
(or_introl eq_refl) SV FRB FRS REPX (fun _ => I) BREPX BOK8 OC17 LOWS17 STB ERRX OUTK0).
intros c' (Σ' & Hc' & E1 & E2 & E3 & E4 & E5).
apply Hk. exists Σ'. split; [exact Hc'|].
pose proof (bkeep_sbw b1) as (K1 & K2 & K3).
cbn [dec_depth dec_mode dec_nestedR dec_credit sF sI set_sbd_submodeID set_sbd_first sbd_mode].
split; [clear; lia|]. split; [rewrite DL3; reflexivity|]. split; [reflexivity|]. split; [split; [exact NM3| exact NEST3]|].
split; [rewrite K2; exact OWN1|]. split; [rewrite K1; exact CHR1|]. split; [rewrite K3; exact BSZ1|].
split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [| exact E5].
rewrite E4, CRq. pose proof (dec_depth_pos low) as DP. clear - CBX DP. lia. }
destruct (sbd_innov_save s) as [k|] eqn:EIS.
2: {
cbn [sI set_sbd_submodeID sbd_innov_save] in POST. rewrite EIS in POST. destruct POST as (xa012 & xa112 & ->).
exact (TAILN m11 ows _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c3 SV FRB FRS BUFS OC LOWS STB ERRX ST8 BOBJ8 BDAT8 X9 WM11 MI11 FR11 RLOW OUTK0 ART11 PF
ACA11 ACO11 ACT11 SSP11 ACS11 OBS11 Hc). }

cbn [sI set_sbd_submodeID sbd_innov_save] in POST. rewrite EIS in POST. subst ms.
assert (EFF : sbd_full_frame_size sI = 2 * sbd_frame_size s) by (cbn [sI set_sbd_submodeID sbd_full_frame_size]; exact IFFS).

assert (FSN2 : Z.of_nat (Z.to_nat (2 * sbd_frame_size s)) = 2 * sbd_frame_size s) by (clear - FSV; lia).
apply (f32_split bsegs m11 OUT ows (Z.to_nat (2 * sbd_frame_size s))) in OC; [| rewrite LOWS; clear - FSV; lia].
destruct OC as (OCa & OCb). rewrite FSN2 in OCb.
apply (f32_split bsegs m11 (OUT + 4 * (2 * sbd_frame_size s)) (skipn (Z.to_nat (2 * sbd_frame_size s)) ows) (Z.to_nat (2 * sbd_frame_size s))) in OCb;
[| rewrite length_skipn, LOWS; clear - FSV; lia].
destruct OCb as (OCm & OCc). rewrite FSN2 in OCc.
assert (Lowa : length (firstn (Z.to_nat (2 * sbd_frame_size s)) ows) = Z.to_nat (2 * sbd_frame_size s)) by (rewrite length_firstn, LOWS; clear - FSV; lia).
assert (Lowc : length (skipn (Z.to_nat (2 * sbd_frame_size s)) (skipn (Z.to_nat (2 * sbd_frame_size s)) ows)) = (2000 - 2 * Z.to_nat (2 * sbd_frame_size s))%nat)
by (rewrite !length_skipn, LOWS; clear - FSV; lia).
pose proof (proj2 OCm) as WRM. rewrite cells_size_f32, length_firstn, length_skipn, LOWS in WRM.
replace (Z.of_nat (4 * Nat.min (Z.to_nat (2 * sbd_frame_size s)) (2000 - Z.to_nat (2 * sbd_frame_size s)))) with (4 * sbd_full_frame_size sI) in WRM
by (rewrite EFF; clear - FSV; lia).
replace (OUT + 4 * (2 * sbd_frame_size s)) with (OUT + 4 * k) in WRM, OCc by (rewrite ISV; reflexivity).
clear OCm.
generalize dependent (firstn (Z.to_nat (2 * sbd_frame_size s)) ows). intros owa OCa Lowa.
generalize dependent (skipn (Z.to_nat (2 * sbd_frame_size s)) (skipn (Z.to_nat (2 * sbd_frame_size s)) ows)). intros owc OCc Lowc.

assert (EU608 : bv_unsigned (Z_to_bv 64 (usp + -736)) = usp + -736) by (apply unsigned_lit; clear - SPT LO736 LOS; lia).
assert (MD0 : 0 <= OUT + 4 * k <= 2^47) by (rewrite ISV; clear - FP0 FO1 FO2 BF1 LO736 SPT FSV; unfold USTACK_TOP in *; lia).
assert (MN0 : 0 <= 4 * sbd_full_frame_size sI < 2^40) by (rewrite EFF; clear - FSV; lia).
assert (CHK : checked_dst RT Σx m11 (Z_to_bv 64 (usp + -736)) (OUT + 4 * k) (4 * sbd_full_frame_size sI)).
{ split; [intros _; split|].
- apply (acc_sub bsegs m11 OUT 8000 (OUT + 4 * k) (4 * sbd_full_frame_size sI) ACO11); rewrite ?EFF, ?ISV; clear - FSV; lia.
- right; left. exists fh, kh. split; [exact INFHX| rewrite ?EFF, ?ISV; clear - FO1 FO2 FSV; lia].
- split; [| exact WRM]. intros i Hi. rewrite EU608. right; right; right; left. exists fh, kh. split; [exact INFHX| rewrite EFF in Hi; rewrite ISV; clear - FO1 FO2 FSV Hi; lia]. }
assert (COK : call_ok RT Σx m11 (Z_to_bv 64 (usp + -736)) lo).
{ unfold call_ok. rewrite EU608. split; [exact ST8|]. split; [exact LOWX|].
split; [clear - LOR DSP; unfold RT_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia|].
split; [clear - SPT; unfold USTACK_TOP in *; lia| clear - SPA; Z.div_mod_to_equations; lia]. }
refine (rz_cps RT Σx (PMfd F0 fs0) _ _ T c3 Hc _ _);
[ refine (MEMS Σx (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m11 (OUT + 4 * k) (4 * sbd_full_frame_size sI) (Z_to_bv 8 0) lo
FDO MST eq_refl eq_refl eq_refl MD0 MN0 CHK ART11 MI11 COK) | ].
intros c4 Hc4. unfold icpt_postF in Hc4.
destruct (ASTA_unpack RT Σx (PMfd F0 fs0) _ c4 Hc4) as (ms4 & PO4 & Hc4'); clear Hc4; cbv beta in PO4.
destruct PO4 as (m12 & RS12 & (ART12 & MI12 & WM12 & ST12) & PRES12 & BY12).
cps_ret RS12.
rewrite EU608 in PRES12, ST12.
rewrite (ret_pc_even RA_sbd_memset_n ltac:(unfold RA_sbd_memset_n; lia) eq_refl) in Hc4'.
clear MD0 MN0 CHK COK.

assert (PRESF : rt_pres_fp (rt_live RT Σx) (rt_frames RT Σx) (usp + -736) [(OUT + 4 * k, OUT + 4 * k + 4 * sbd_full_frame_size sI)] m11 m12).
{ apply (pres_fp_of_pres_ex_gen _ _ _ _ (rt_live RT Σx) (rt_frames RT Σx) (usp + -736) (OUT + 4 * k) (4 * sbd_full_frame_size sI) m11 m12 PRES12);
[intros e He; exact He | intros e He; exact He | clear; lia |].
intros x _ Ho. cbn [outside] in Ho. destruct Ho as (Ho & _). exact Ho. }
assert (OWM : forall x, (x < OUT + 4 * k \/ OUT + 4 * k + 4 * sbd_full_frame_size sI <= x) -> outside [(OUT + 4 * k, OUT + 4 * k + 4 * sbd_full_frame_size sI)] x)
by (intros x Hx; cbn [outside]; split; [clear - Hx; lia| exact I]).
assert (WIN : OUT <= OUT + 4 * k /\ OUT + 4 * k + 4 * sbd_full_frame_size sI <= OUT + 8000) by (rewrite EFF, ISV; clear - FSV; lia).
assert (CLF : forall x, fh <= x < fh + fs_size kh - 8 -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -736) x)
by (intros x Hx; right; right; right; left; exists fh, kh; split; [exact INFHX| exact Hx]).
assert (CLS : forall x, usp + -736 <= x < usp -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -736) x)
by (intros x Hx; left; clear - Hx SPT; unfold USTACK_TOP in *; lia).
assert (CLL : forall p n x, In (p, n) (rt_live RT Σx) -> p <= x < p + n -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -736) x)
by (intros p n x Hp Hx; right; right; left; exists p, n; split; [exact Hp| exact Hx]).
assert (CLF0 : forall x, f <= x < f + 56 -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -736) x)
by (intros x Hx; right; right; right; left; exists f, 0%nat; split; [exact INF| change (fs_size 0) with 64; lia]).
assert (CLSF : forall x, sf <= x < sf + 8 -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -736) x)
by (intros x Hx; right; right; right; right; exists f, 0%nat; split; [exact INF| change (fs_size 0) with 64; rewrite <- SHF, SHF0; lia]).
destruct (frame_live_apart RT AF Σx m11 fh kh PD ND ART11 INFHX INPDX) as (FLPD & _).
assert (SFH' : S + 160 <= fh \/ fh + fs_size kh <= S) by (clear - SFH; unfold hid in *; lia).
assert (FFA' : fh + fs_size kh <= f \/ f + 64 <= fh) by (clear - FFA; unfold hid in *; lia).
assert (FPHI2 : fh + fs_size kh <= SH_LO \/ SH_HI <= fh) by (clear - FPHI'; unfold hid, SH_LO, SH_HI in *; lia).
assert (HOS2 : OUT + 8000 <= STEREO \/ STEREO + 24 <= OUT) by (clear - HOS'; unfold hid in *; lia).
assert (HAO2 : A + 48 <= OUT \/ OUT + 8000 <= A) by (clear - HAO'; unfold hid in *; lia).
tr1 PRESF WM12 SV ltac:(fun x Hx => apply CLS; clear - Hx; lia) ltac:(fun x Hx => apply OWM; right; clear - Hx WIN FO2 BF1 LO736; lia).
tr1 PRESF WM12 FR11 ltac:(fun x Hx => apply CLS; clear - Hx; lia) ltac:(fun x Hx => apply OWM; right; clear - Hx WIN FO2 BF1 LO736; lia).
tr1 PRESF WM12 FRB ltac:(fun x Hx => apply CLF0; clear - Hx; lia) ltac:(fun x Hx => apply OWM; clear - Hx WIN FO1 FO2 FFA'; lia).
tr1 PRESF WM12 FRS ltac:(fun x Hx => apply CLSF; clear - Hx; lia)
ltac:(fun x Hx => apply OWM; clear - Hx WIN FO1 FO2 FPHI2 SHF1 SHF2; unfold SH_LO, SH_HI in *; lia).
tr1 PRESF WM12 STB ltac:(fun x Hx => apply CLF; clear - Hx FS1 FS2; lia) ltac:(fun x Hx => apply OWM; clear - Hx WIN HOS2; lia).
tr1 PRESF WM12 BOBJ8 ltac:(fun x Hx => apply CLF; clear - Hx FA1 FA2; lia) ltac:(fun x Hx => apply OWM; clear - Hx WIN HAO2; lia).
tr1 PRESF WM12 BDAT8 ltac:(fun x Hx => apply (CLL PD ND x INPDX); clear - Hx PD1 PD2 Lbs8; lia)
ltac:(fun x Hx => apply OWM; clear - Hx WIN PD1 PD2 Lbs8 FLPD FO1 FO2; lia).
tr1 PRESF WM12 X9 ltac:(fun x Hx => apply (CLL S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => apply OWM; clear - Hx WIN FO1 FO2 SFH'; lia).
tr1 PRESF WM12 OCa ltac:(fun x Hx => apply CLF; rewrite Lowa in Hx; clear - Hx FO1 FO2 FSV; lia)
ltac:(fun x Hx => apply OWM; left; rewrite Lowa in Hx; rewrite ISV; clear - Hx FSV; lia).
tr1 PRESF WM12 OCc ltac:(fun x Hx => apply CLF; rewrite Lowc in Hx; rewrite ISV in Hx; clear - Hx FO1 FO2 FSV; lia)
ltac:(fun x Hx => apply OWM; right; rewrite EFF; clear - Hx; lia).

assert (AGA : agree_blocks bsegs m11 m12 LALL).
{ apply (agree_blocks_of_pres_fp RT Σx _ _ _ m11 m12 LALL PRESF WM12); [exact LIVEA|]. intros bk x Hb Hx.
pose proof (BOUT bk x Hb Hx) as H1. destruct (frame_live_apart RT AF Σx m11 fh kh _ _ ART11 INFHX (LIVEA bk Hb)) as (FB & _).
apply OWM. clear - H1 FB Hx WIN FO1 FO2. lia. }
unfold LALL in AGA. pk_all AGA. clear AGA.
pk_io_fp PRESF ERR_rep OUT_rep IO_FP IO_img ltac:(fun y Hy => apply OWM; left; clear - Hy WIN FO1 FPIMG; lia).
assert (SSP12 : io_ssp m12).
{ apply (sbd_io_ssp_agree m11 m12 SSP11 (AF_DRV Σx m12 ART12)). intros a0 Ha. apply PRESF; [right; left; exact (sbd_ssp_static _ Ha)|].
unfold X0r9.SSP_GUARD in Ha. apply OWM. left. clear - Ha WIN FO1 FPIMG. lia. }
assert (SHW12 : forall o n, fh <= o -> o + n <= fh + fs_size kh -> forall i, 0 <= i < n -> outside [(OUT + 4 * k, OUT + 4 * k + 4 * sbd_full_frame_size sI)] (shad (o + i))).
{ intros o n H1 H2 i Hi.
assert (SR : SH_LO <= shad (o + i) < SH_HI).
{ pose proof (frame_facts RT AF Σx m11 fh kh ART11 INFHX) as (_ & _ & _ & _ & _ & _ & SA & SL & SH & _). split.
- unfold shad, SH_LO, SHB in *. assert (0 <= (o + i) / 8) by (apply Z.div_pos; lia). lia.
- assert (shad (o + i) < shad (fh + fs_size kh)); [| lia].
unfold shad. apply Z.add_lt_mono_r. apply Z.div_lt_upper_bound; [lia|].
assert (FH8 : fh mod 8 = 0) by (clear - FP64; Z.div_mod_to_equations; lia).
assert (FK8 : fs_size kh mod 8 = 0) by (destruct FS64 as (M64 & _); clear - M64; Z.div_mod_to_equations; lia).
assert (E : fh + fs_size kh = 8 * ((fh + fs_size kh) / 8)).
{ pose proof (Z.div_mod (fh + fs_size kh) 8 ltac:(lia)) as XD. rewrite Zplus_mod, FH8, FK8 in XD. cbn in XD. lia. }
lia. }
apply OWM. clear - SR FPHI2 WIN FO1 FO2. unfold SH_LO, SH_HI in *. lia. }
assert (FH8 : fh mod 8 = 0) by (clear - FP64; Z.div_mod_to_equations; lia).
assert (FK8 : fs_size kh mod 8 = 0) by (destruct FS64 as (M64 & _); clear - M64; Z.div_mod_to_equations; lia).
assert (ACA12 : acc bsegs m12 A 48)
by (apply (acc_pres_fp_frame _ _ _ _ m11 m12 fh kh A 48 PRESF INFHX FH8 FK8 ltac:(lia) FA1 ltac:(lia) (SHW12 A 48 FA1 ltac:(lia)) ACA11)).
assert (ACO12 : acc bsegs m12 OUT 8000)
by (apply (acc_pres_fp_frame _ _ _ _ m11 m12 fh kh OUT 8000 PRESF INFHX FH8 FK8 ltac:(lia) FO1 ltac:(lia) (SHW12 OUT 8000 FO1 ltac:(lia)) ACO11)).
assert (ACT12 : acc bsegs m12 STEREO 24)
by (apply (acc_pres_fp_frame _ _ _ _ m11 m12 fh kh STEREO 24 PRESF INFHX FH8 FK8 ltac:(lia) FS1 ltac:(lia) (SHW12 STEREO 24 FS1 ltac:(lia)) ACT11)).
assert (PF12 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m12).
{ apply (pres_fp_trans _ _ _ _ m m11 m12 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σx) (rt_frames RT Σx) (usp + -736) _ m11 m12 PRESF).
- intros e He. rewrite ELX. exact He.
- intros e He. rewrite EFX. right. exact He.
- clear; lia.
- intros x Hx Ho. cbn [outside] in Ho. destruct Ho as (_ & HO & _). apply OWM. clear - HO WIN. lia. }
destruct (af_acc_live RT AF Σx m12 S 160 ART12 INLX) as (_ & ACS12).
assert (OBS12 : aobj bsegs m12 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO736 SPT; unfold APP_TOP; lia| exact ACS12]).
assert (WM12' : wmono bsegs m9 m12) by (eapply wmono_trans; [exact WM11| exact WM12]).

assert (ZB : rw_cells bsegs m12 (OUT + 4 * k) [CB (length (repeat (Z_to_bv 8 0) (Z.to_nat (4 * sbd_full_frame_size sI)))) (repeat (Z_to_bv 8 0) (Z.to_nat (4 * sbd_full_frame_size sI)))]).
{ split; [split; [split; [reflexivity| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BY12]|].
cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, repeat_length. rewrite Z2Nat.id by (rewrite EFF; clear - FSV; lia).
exact (wr_at_transport bsegs m11 m12 _ _ WRM WM12). }
rewrite repeat_length in ZB.
replace (Z.to_nat (4 * sbd_full_frame_size sI)) with (4 * Z.to_nat (2 * sbd_frame_size s))%nat in ZB by (rewrite EFF; clear - FSV; lia).
destruct (rw_cells_CB_f32 bsegs m12 (OUT + 4 * k) (Z.to_nat (2 * sbd_frame_size s)) _ ZB) as (zw & Lzw & ZW). clear ZB.
assert (OC12 : rw_cells bsegs m12 OUT (f32 (owa ++ zw ++ owc))).
{ apply (f32_join bsegs m12 OUT _ _ OCa). replace (OUT + 4 * Z.of_nat (length owa)) with (OUT + 4 * k) by (rewrite Lowa, ISV; clear - FSV; lia).
apply (f32_join bsegs m12 (OUT + 4 * k) _ _ ZW). replace (OUT + 4 * k + 4 * Z.of_nat (length zw)) with (OUT + 4 * k + 4 * (2 * sbd_frame_size s)) by (rewrite Lzw; clear - FSV; lia).
exact OCc. }
assert (LOWS12 : length (owa ++ zw ++ owc) = 2000%nat) by (rewrite !length_app, Lowa, Lzw, Lowc; clear - FSV; lia).
unfold RA_sbd_memset_n in Hc4'.
exact (TAILN m12 (owa ++ zw ++ owc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c4 SV FRB FRS BUFS OC12 LOWS12 STB ERRX ST12 BOBJ8 BDAT8 X9 WM12' MI12 FR11 RLOW OUTK ART12 PF12
ACA12 ACO12 ACT12 SSP12 ACS12 OBS12 Hc4').
}

destruct PZ as (-> & -> & -> & ->).
assert (EB : sbd_inv_bytes s b1 = []) by (unfold sbd_inv_bytes; fold id; rewrite ESM; reflexivity).
rewrite EB. apply rz_emit_nil.
assert (EV : sb_id_valid (sbd_mode s) id = true) by (unfold sb_id_valid; rewrite ESM; apply Bool.orb_true_r).
rewrite EV in Hc.

destruct (af_acc_live RT AF Σx m9 S 160 ART INLX) as (_ & ACS9).
assert (OBS9 : aobj bsegs m9 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO736 SPT; unfold APP_TOP; lia| exact ACS9]).
pose proof (AF_LIB Σx m9 ART) as LC9.
assert (OBM9 : aobj bsegs m9 (sbmode_struct (sbd_mode s)) 216).
{ destruct IMODE as [E|E]; rewrite E; cbn [sbmode_struct]; (apply (aobj_lit RT AF Σx m9 _ 216 ART);
[ unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_sb_wb_mode, A_sb_uwb_mode; lia | unfold A_sb_wb_mode, A_sb_uwb_mode, APP_TOP; lia]). }
sb_unpack X9 as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_m usp S OUT A f (sbmode_struct (sbd_mode s)) id (fupds g [(47%nat, Z_to_bv 64 (S + 144)); (48%nat, Z_to_bv 64 (S + 152))]) s (sj_pad1 j)
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR8 ltac:(gslot) CFG IDC OBS9 S8 SPOS SLO8 SOFF IMODE eq_refl OBM9 LC9 IDR SHL SPH MI9).
destruct POST as (m11 & xa011 & xa111 & xa211 & xa311 & xa411 & -> & MU11 & WM11 & MI11 & FR11).
match goal with H : ASTA _ _ _ _ _ |- _ => rewrite ESM in H end.
clear FR8 HD FST PT LE SEED CFG IDC PAD OBS9 ACS9 LC9.
Time pk_munch_all MU11 WM11 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LO736; cbn [outside]; split; [lia| exact I])
ltac:(fun x Hx => clear - Hx LO736 LOS; cbn [outside]; split; [lia| exact I]).
Time cps_seg_post.
match goal with H : X14x.ART RT Σx m11 |- _ => rename H into ART11 end.
assert (OF11 : offsh [(usp + -736, usp + -160)]) by (cbn [offsh]; clear - LOS LO736; unfold SH_LO, SH_HI in *; lia).
assert (ACC11 : forall o n, acc bsegs m9 o n -> 0 <= o -> o + n <= 140737488355328 -> acc bsegs m11 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch bsegs _ m9 m11 o n (conj H0 (conj H1 H)) MU11 (shfree_of_offsh _ o n OF11 H0 H1)))). }
assert (ACA11 : acc bsegs m11 A 48) by (apply ACC11; [exact ACA9| clear - FA1 FP0; lia| clear - FA2 BF1 LO736 SPT; lia]).
assert (ACO11 : acc bsegs m11 OUT 8000) by (apply ACC11; [exact ACO9| clear - FO1 FP0; lia| clear - FO2 BF1 LO736 SPT; lia]).
assert (ACT11 : acc bsegs m11 STEREO 24) by (apply ACC11; [exact ACT9| clear - FS1 FP0; lia| clear - FS2 BF1 LO736 SPT; lia]).
assert (SSP11 : io_ssp m11).
{ apply (sbd_io_ssp_agree m9 m11 SSPX (AF_DRV Σx m11 ART11)). intros a0 Ha. apply MU11. unfold X0r9.SSP_GUARD in Ha. cbn [outside].
clear - Ha LO736 LOS. split; [lia| exact I]. }
clear ACA9 ACO9 ACT9 ACC11 SSPX.
destruct (af_acc_live RT AF Σx m11 S 160 ART11 INLX) as (_ & ACS11).
assert (OBS11 : aobj bsegs m11 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO736 SPT; unfold APP_TOP; lia| exact ACS11]).

sb_unpack X9 as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_v1 usp lo S OUT A f (sbmode_struct (sbd_mode s))
(fupds (fupds g [(47%nat, Z_to_bv 64 (S + 144)); (48%nat, Z_to_bv 64 (S + 152))]) [(45%nat, Z_to_bv 64 (Z.shiftr (S + 144) 3 + SHB)); (44%nat, Z_to_bv 64 (Z.shiftr (S + 152) 3 + SHB))])
sI a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
FR11 HD INS OBS11 S8 SPOS BS1 SOFF ST8 ltac:(clear - LOR DSP; unfold SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia) LOS SPH SPA MI11).
clear HD FST PT LE SEED CFG IDC PAD.
destruct POST as (m12 & xa212 & jh1 & -> & MU12 & WM12 & MI12 & ST12 & FR12 & HU1).
clear FR11.

assert (LOV : lo + RT_STACK + SB_LOOP_STACK <= usp + -1216) by (clear - LOR DSP; unfold RT_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
assert (LOV' : lo <= usp + -5248) by (clear - LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
assert (ART12 : X14x.ART RT Σx m12).
{ apply (af_frame RT AF Σx m11 m12 lo ART11 LOWX); [| exact WM12]. intros a0 Ha. apply MU12. cbn [outside]. split; [| exact I].
intros Hin. apply Ha. left. clear - Hin LOV' SPT. unfold USTACK_TOP. lia. }
assert (PF12 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m12).
{ apply (pres_fp_trans _ _ _ _ m m11 m12 PF). apply (pres_fp_of_munch _ _ _ _ _ m11 m12 MU12). intros x Hx Ho. cbn [outside]. split; [| exact I].
intros Hin. destruct (SPL x Hx) as [H1 | H1]; clear - H1 Hin LOW LOV'; lia. }
clear PF. rename PF12 into PF.
pk_munch_all MU12 WM12 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LOV'; cbn [outside]; split; [lia| exact I])
ltac:(fun x Hx => clear - Hx LOV' LOS; cbn [outside]; split; [lia| exact I]).
trm MU12 WM12 SV ltac:(clear; lia).
trm MU12 WM12 FRB ltac:(clear - BF LOV'; lia).
trm MU12 WM12 FRS ltac:(clear - BF0 LOV'; lia).
trm MU12 WM12 OC ltac:(rewrite LOWS; clear - FO2 BF1 LOV'; lia).
trm MU12 WM12 STB ltac:(clear - FS2 BF1 LOV'; lia).
trm MU12 WM12 BOBJ8 ltac:(clear - FA2 BF1 LOV'; lia).
trm MU12 WM12 BDAT8 ltac:(clear - BD8 LOV'; lia).
trm MU12 WM12 X9 ltac:(clear - BS1 LOV'; lia).
clear ST8.
assert (OF12 : offsh [(usp + -4832, usp + -160)]) by (cbn [offsh]; clear - LOS LOV'; unfold SH_LO, SH_HI in *; lia).
assert (ACC12 : forall o n, acc bsegs m11 o n -> 0 <= o -> o + n <= 140737488355328 -> acc bsegs m12 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch bsegs _ m11 m12 o n (conj H0 (conj H1 H)) MU12 (shfree_of_offsh _ o n OF12 H0 H1)))). }
assert (ACA12 : acc bsegs m12 A 48) by (apply ACC12; [exact ACA11| clear - FA1 FP0; lia| clear - FA2 BF1 LO736 SPT; lia]).
assert (ACO12 : acc bsegs m12 OUT 8000) by (apply ACC12; [exact ACO11| clear - FO1 FP0; lia| clear - FO2 BF1 LO736 SPT; lia]).
assert (ACT12 : acc bsegs m12 STEREO 24) by (apply ACC12; [exact ACT11| clear - FS1 FP0; lia| clear - FS2 BF1 LO736 SPT; lia]).
assert (SSP12 : io_ssp m12).
{ apply (sbd_io_ssp_agree m11 m12 SSP11 (AF_DRV Σx m12 ART12)). intros a0 Ha. apply MU12. unfold X0r9.SSP_GUARD in Ha. cbn [outside].
clear - Ha LOV' LOS. split; [lia| exact I]. }
destruct (af_acc_live RT AF Σx m12 S 160 ART12 INLX) as (_ & ACS12).
assert (OBS12 : aobj bsegs m12 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO736 SPT; unfold APP_TOP; lia| exact ACS12]).
clear ACA11 ACO11 ACT11 ACC12 SSP11 ACS11 OBS11 ART11 MI11 OF11.

assert (EU704 : bv_unsigned (Z_to_bv 64 (usp + -832)) = usp + -832) by (apply unsigned_lit; clear - SPT LOV' LOS; lia).
assert (POA1 : pois_above (rt_pois RT Σx) (alloca_rr (usp + -800) 16)).
{ apply (pois_above_le _ usp); [rewrite EPX; exact POA|]. unfold alloca_rr. clear - SPA. Z.div_mod_to_equations. lia. }
assert (COK1 : call_ok RT Σx m12 (Z_to_bv 64 (usp + -832)) lo).
{ unfold call_ok. rewrite EU704. split; [exact ST12|]. split; [exact LOWX|]. split; [clear - LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia|].
split; [clear - SPT; unfold USTACK_TOP in *; lia| clear - SPA; Z.div_mod_to_equations; lia]. }
cps_rt (APO Σx (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m12 (usp + -800) 16 lo FDO MST eq_refl eq_refl
ltac:(clear - SPA; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(rewrite EU704; lia)
ltac:(unfold alloca_rr, USTACK_TOP; clear - SPA SPT; Z.div_mod_to_equations; lia)
POA1 ltac:(rewrite EFX; discriminate) ART12 MI12 COK1).
intros c5 (Σ1 & Hc5 & EP1 & EL1 & EF1 & ES1 & EC1).
destruct (ASTA_unpack RT Σ1 (PMfd F0 fs0) _ c5 Hc5) as (ms5 & PO5 & Hc5'); clear Hc5; cbv beta in PO5.
destruct PO5 as (m13 & v13 & RS13 & (ART13 & MI13 & WM13 & ST13) & PRES13 & ACV13 & ACK13).
cps_ret RS13.
rewrite EU704 in PRES13, ST13.
clear POA1 COK1.

assert (CLFg : forall L Fr sp' x, In (fh, kh) Fr -> fh <= x < fh + fs_size kh - 8 -> aclient L Fr sp' x)
by (intros L Fr sp' x HF Hx; right; right; right; left; exists fh, kh; split; [exact HF| exact Hx]).
assert (CLLg : forall L Fr sp' p n x, In (p, n) L -> p <= x < p + n -> aclient L Fr sp' x)
by (intros L Fr sp' p n x Hp Hx; right; right; left; exists p, n; split; [exact Hp| exact Hx]).
assert (CLF0g : forall L Fr sp' x, In (f, 0%nat) Fr -> f <= x < f + 56 -> aclient L Fr sp' x)
by (intros L Fr sp' x HF Hx; right; right; right; left; exists f, 0%nat; split; [exact HF| change (fs_size 0) with 64; lia]).
assert (CLSFg : forall L Fr sp' x, In (f, 0%nat) Fr -> sf <= x < sf + 8 -> aclient L Fr sp' x)
by (intros L Fr sp' x HF Hx; right; right; right; right; exists f, 0%nat; split; [exact HF| change (fs_size 0) with 64; rewrite <- SHF, SHF0; lia]).
assert (CLSg : forall L Fr sp' x, sp' <= x < usp -> aclient L Fr sp' x)
by (intros L Fr sp' x Hx; left; clear - Hx SPT; unfold USTACK_TOP in *; lia).

pose proof (pres_fp_of_pres _ _ _ [] _ _ PRES13) as PF13.
tr1 PF13 WM13 SV ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF13 WM13 FR12 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF13 WM13 HU1 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF13 WM13 FRB ltac:(fun x Hx => apply (CLF0g _ _ _ x INF); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF13 WM13 FRS ltac:(fun x Hx => apply (CLSFg _ _ _ x INF); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF13 WM13 OC ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); rewrite LOWS in Hx; clear - Hx FO1 FO2; lia) ltac:(fun x Hx => exact I).
tr1 PF13 WM13 STB ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FS1 FS2; lia) ltac:(fun x Hx => exact I).
tr1 PF13 WM13 BOBJ8 ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FA1 FA2; lia) ltac:(fun x Hx => exact I).
tr1 PF13 WM13 BDAT8 ltac:(fun x Hx => apply (CLLg _ _ _ PD ND x INPDX); clear - Hx PD1 PD2 Lbs8; lia) ltac:(fun x Hx => exact I).
tr1 PF13 WM13 X9 ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => exact I).
pk_pres_all RT PRES13 WM13 LALL LIVEA ERR_rep OUT_rep IO_FP IO_img.
assert (ACA13 : acc bsegs m13 A 48) by (apply ACK13; [exact ACA12| clear - FA2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FA2 BF1 LOV'; lia]).
assert (ACO13 : acc bsegs m13 OUT 8000) by (apply ACK13; [exact ACO12| clear - FO2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FO2 BF1 LOV'; lia]).
assert (ACT13 : acc bsegs m13 STEREO 24) by (apply ACK13; [exact ACT12| clear - FS2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FS2 BF1 LOV'; lia]).
assert (ACS13 : acc bsegs m13 S 160) by (apply ACK13; [exact ACS12| clear - BS1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - BS1 LOV'; lia]).
assert (OBS13 : aobj bsegs m13 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO736 SPT; unfold APP_TOP; lia| exact ACS13]).
assert (SSP13 : io_ssp m13).
{ apply (sbd_io_ssp_agree m12 m13 SSP12 (AF_DRV Σ1 m13 ART13)). intros a0 Ha. apply PRES13. right; left. exact (sbd_ssp_static _ Ha). }
assert (PF13' : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m13).
{ apply (pres_fp_trans _ _ _ _ m m12 m13 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σx) (rt_frames RT Σx) (usp + -832) [] m12 m13 PF13).
- intros e He. rewrite ELX. exact He.
- intros e He. rewrite EFX. right. exact He.
- clear; lia.
- intros x _ _. exact I. }
clear PF. rename PF13' into PF.
clear ACA12 ACO12 ACT12 ACS12 OBS12 SSP12 ART12 MI12 ST12 PF13 PRES13 ACK13.

rewrite <- EL1 in LIVEA, LIVEL, LIVED, INLX, INPDX. rewrite <- EF1 in INF, INFHX. rewrite <- ES1 in LOWX.

sb_unpack X9 as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_v2 usp lo S OUT A f (sbmode_struct (sbd_mode s)) _ sI a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
FR12 ltac:(gslot) ltac:(gslot) HD INS OBS13 S8 SPOS BS1 SOFF ST13 ltac:(clear - LOV'; lia) LOS SPH SPA MI13).
clear HD FST PT LE SEED CFG IDC PAD.
destruct POST as (m14 & xa214 & jh2 & -> & MU14 & WM14 & MI14 & ST14 & FR14 & HU2).
clear FR12 ST13.
assert (ART14 : X14x.ART RT Σ1 m14).
{ apply (af_frame RT AF Σ1 m13 m14 lo ART13 LOWX); [| exact WM14]. intros a0 Ha. apply MU14. cbn [outside]. split; [| exact I].
intros Hin. apply Ha. left. clear - Hin LOV' SPT. unfold USTACK_TOP. lia. }
assert (PF14 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m14).
{ apply (pres_fp_trans _ _ _ _ m m13 m14 PF). apply (pres_fp_of_munch _ _ _ _ _ m13 m14 MU14). intros x Hx Ho. cbn [outside]. split; [| exact I].
intros Hin. destruct (SPL x Hx) as [H1 | H1]; clear - H1 Hin LOW LOV'; lia. }
clear PF. rename PF14 into PF.
pk_munch_all MU14 WM14 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LOV'; cbn [outside]; split; [lia| exact I])
ltac:(fun x Hx => clear - Hx LOV' LOS; cbn [outside]; split; [lia| exact I]).
trm MU14 WM14 SV ltac:(clear; lia).
trm MU14 WM14 FRB ltac:(clear - BF LOV'; lia).
trm MU14 WM14 FRS ltac:(clear - BF0 LOV'; lia).
trm MU14 WM14 OC ltac:(rewrite LOWS; clear - FO2 BF1 LOV'; lia).
trm MU14 WM14 STB ltac:(clear - FS2 BF1 LOV'; lia).
trm MU14 WM14 BOBJ8 ltac:(clear - FA2 BF1 LOV'; lia).
trm MU14 WM14 BDAT8 ltac:(clear - BD8 LOV'; lia).
trm MU14 WM14 X9 ltac:(clear - BS1 LOV'; lia).

destruct (wr_at_rw_CB m14 (usp + -832) 96 (wr_at_transport bsegs m13 m14 _ _ (proj2 HU1) WM14) ltac:(lia)) as (jh1' & HU1'). clear HU1 jh1. rename HU1' into HU1. rename jh1' into jh1.
assert (OF14 : offsh [(usp + -4928, usp + -160)]) by (cbn [offsh]; clear - LOS LOV'; unfold SH_LO, SH_HI in *; lia).
assert (ACC14 : forall o n, acc bsegs m13 o n -> 0 <= o -> o + n <= 140737488355328 -> acc bsegs m14 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch bsegs _ m13 m14 o n (conj H0 (conj H1 H)) MU14 (shfree_of_offsh _ o n OF14 H0 H1)))). }
assert (ACA14 : acc bsegs m14 A 48) by (apply ACC14; [exact ACA13| clear - FA1 FP0; lia| clear - FA2 BF1 LO736 SPT; lia]).
assert (ACO14 : acc bsegs m14 OUT 8000) by (apply ACC14; [exact ACO13| clear - FO1 FP0; lia| clear - FO2 BF1 LO736 SPT; lia]).
assert (ACT14 : acc bsegs m14 STEREO 24) by (apply ACC14; [exact ACT13| clear - FS1 FP0; lia| clear - FS2 BF1 LO736 SPT; lia]).
assert (ACV14 : acc bsegs m14 (usp + -800) 16) by (apply ACC14; [exact ACV13| clear - LOV' LOS; lia| clear - SPT; lia]).
assert (SSP14 : io_ssp m14).
{ apply (sbd_io_ssp_agree m13 m14 SSP13 (AF_DRV Σ1 m14 ART14)). intros a0 Ha. apply MU14. unfold X0r9.SSP_GUARD in Ha. cbn [outside].
clear - Ha LOV' LOS. split; [lia| exact I]. }
destruct (af_acc_live RT AF Σ1 m14 S 160 ART14 INLX) as (_ & ACS14).
assert (OBS14 : aobj bsegs m14 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO736 SPT; unfold APP_TOP; lia| exact ACS14]).
clear ACA13 ACO13 ACT13 ACV13 ACC14 SSP13 ACS13 OBS13 ART13 MI13 OF14 MU14.

assert (EU800 : bv_unsigned (Z_to_bv 64 (usp + -928)) = usp + -928) by (apply unsigned_lit; clear - SPT LOV' LOS; lia).
assert (POA2 : pois_above (rt_pois RT Σ1) (alloca_rr (usp + -896) 16)).
{ intros e He. rewrite EP1 in He. destruct He as [<- | He].
- unfold pz_lo, alloca_rr. cbn [fst]. clear - SPA. Z.div_mod_to_equations. lia.
- rewrite EPX in He. pose proof (POA e He) as H1. unfold alloca_rr. clear - H1 SPA. Z.div_mod_to_equations. lia. }
assert (COK2 : call_ok RT Σ1 m14 (Z_to_bv 64 (usp + -928)) lo).
{ unfold call_ok. rewrite EU800. split; [exact ST14|]. split; [exact LOWX|]. split; [clear - LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia|].
split; [clear - SPT; unfold USTACK_TOP in *; lia| clear - SPA; Z.div_mod_to_equations; lia]. }
cps_rt (APO Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m14 (usp + -896) 16 lo FDO MST eq_refl eq_refl
ltac:(clear - SPA; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(rewrite EU800; lia)
ltac:(unfold alloca_rr, USTACK_TOP; clear - SPA SPT; Z.div_mod_to_equations; lia)
POA2 ltac:(rewrite EF1, EFX; discriminate) ART14 MI14 COK2).
intros c6 (Σ2 & Hc6 & EP2 & EL2 & EF2 & ES2 & EC2).
destruct (ASTA_unpack RT Σ2 (PMfd F0 fs0) _ c6 Hc6) as (ms6 & PO6 & Hc6'); clear Hc6; cbv beta in PO6.
destruct PO6 as (m15 & v15 & RS15 & (ART15 & MI15 & WM15 & ST15) & PRES15 & ACV15 & ACK15).
cps_ret RS15.
rewrite EU800 in PRES15, ST15.
clear POA2 COK2.
pose proof (pres_fp_of_pres _ _ _ [] _ _ PRES15) as PF15.
tr1 PF15 WM15 SV ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF15 WM15 FR14 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF15 WM15 HU1 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF15 WM15 HU2 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF15 WM15 FRB ltac:(fun x Hx => apply (CLF0g _ _ _ x INF); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF15 WM15 FRS ltac:(fun x Hx => apply (CLSFg _ _ _ x INF); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF15 WM15 OC ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); rewrite LOWS in Hx; clear - Hx FO1 FO2; lia) ltac:(fun x Hx => exact I).
tr1 PF15 WM15 STB ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FS1 FS2; lia) ltac:(fun x Hx => exact I).
tr1 PF15 WM15 BOBJ8 ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FA1 FA2; lia) ltac:(fun x Hx => exact I).
tr1 PF15 WM15 BDAT8 ltac:(fun x Hx => apply (CLLg _ _ _ PD ND x INPDX); clear - Hx PD1 PD2 Lbs8; lia) ltac:(fun x Hx => exact I).
tr1 PF15 WM15 X9 ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => exact I).
pk_pres_all RT PRES15 WM15 LALL LIVEA ERR_rep OUT_rep IO_FP IO_img.
assert (ACA15 : acc bsegs m15 A 48) by (apply ACK15; [exact ACA14| clear - FA2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FA2 BF1 LOV'; lia]).
assert (ACO15 : acc bsegs m15 OUT 8000) by (apply ACK15; [exact ACO14| clear - FO2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FO2 BF1 LOV'; lia]).
assert (ACT15 : acc bsegs m15 STEREO 24) by (apply ACK15; [exact ACT14| clear - FS2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FS2 BF1 LOV'; lia]).
assert (ACS15 : acc bsegs m15 S 160) by (apply ACK15; [exact ACS14| clear - BS1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - BS1 LOV'; lia]).
assert (ACV15a : acc bsegs m15 (usp + -800) 16)
by (apply ACK15; [exact ACV14| clear - SPT; unfold USTACK_TOP; lia| right; unfold alloca_rr; clear - SPA; Z.div_mod_to_equations; lia]).
assert (OBS15 : aobj bsegs m15 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO736 SPT; unfold APP_TOP; lia| exact ACS15]).
assert (SSP15 : io_ssp m15).
{ apply (sbd_io_ssp_agree m14 m15 SSP14 (AF_DRV Σ2 m15 ART15)). intros a0 Ha. apply PRES15. right; left. exact (sbd_ssp_static _ Ha). }
assert (PF15' : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m15).
{ apply (pres_fp_trans _ _ _ _ m m14 m15 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -928) [] m14 m15 PF15).
- intros e He. rewrite EL1, ELX. exact He.
- intros e He. rewrite EF1, EFX. right. exact He.
- clear; lia.
- intros x _ _. exact I. }
clear PF. rename PF15' into PF.
clear ACA14 ACO14 ACT14 ACS14 ACV14 OBS14 SSP14 ART14 MI14 ST14 PF15 PRES15 ACK15.
rename ACV15 into ACW15. rename ACV15a into ACV15.
rewrite <- EL2 in LIVEA, LIVEL, LIVED, INLX, INPDX. rewrite <- EF2 in INF, INFHX. rewrite <- ES2 in LOWX.

sb_unpack X9 as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_v3 usp S OUT A f (sbmode_struct (sbd_mode s)) _ sI a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
FR14 ltac:(gslot) ltac:(gslot) HD OBS15 S8 SPOS ltac:(clear - BS1 LOV'; lia) SOFF ltac:(clear - LOS LOV'; unfold SH_HI in *; lia) SPH MI15).
clear HD FST PT LE SEED CFG IDC PAD.
destruct POST as (m16 & -> & MU16 & WM16 & MI16 & FR16).
clear FR14.
assert (ART16 : X14x.ART RT Σ2 m16).
{ apply (af_frame RT AF Σ2 m15 m16 lo ART15 LOWX); [| exact WM16]. intros a0 Ha. apply MU16. cbn [outside]. split; [| exact I].
intros Hin. apply Ha. left. clear - Hin LOV' SPT. unfold USTACK_TOP. lia. }
assert (PF16 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m16).
{ apply (pres_fp_trans _ _ _ _ m m15 m16 PF). apply (pres_fp_of_munch _ _ _ _ _ m15 m16 MU16). intros x Hx Ho. cbn [outside]. split; [| exact I].
intros Hin. destruct (SPL x Hx) as [H1 | H1]; clear - H1 Hin LOW LOV'; lia. }
clear PF. rename PF16 into PF.
pk_munch_all MU16 WM16 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LOV'; cbn [outside]; split; [lia| exact I])
ltac:(fun x Hx => clear - Hx LOV' LOS; cbn [outside]; split; [lia| exact I]).
trm MU16 WM16 SV ltac:(clear; lia).
trm MU16 WM16 HU1 ltac:(clear; lia).
trm MU16 WM16 HU2 ltac:(clear; lia).
trm MU16 WM16 FRB ltac:(clear - BF LOV'; lia).
trm MU16 WM16 FRS ltac:(clear - BF0 LOV'; lia).
trm MU16 WM16 OC ltac:(rewrite LOWS; clear - FO2 BF1 LOV'; lia).
trm MU16 WM16 STB ltac:(clear - FS2 BF1 LOV'; lia).
trm MU16 WM16 BOBJ8 ltac:(clear - FA2 BF1 LOV'; lia).
trm MU16 WM16 BDAT8 ltac:(clear - BD8 LOV'; lia).
trm MU16 WM16 X9 ltac:(clear - BS1 LOV'; lia).
apply (stk_transport_disjoint bsegs [(usp + -736, usp + -160)] m15 m16 lo (usp + -928)) in ST15; [| exact MU16 | exact WM16 | cbn [disjoint_from]; clear; lia].
assert (OF16 : offsh [(usp + -736, usp + -160)]) by (cbn [offsh]; clear - LOS LOV'; unfold SH_LO, SH_HI in *; lia).
assert (ACC16 : forall o n, acc bsegs m15 o n -> 0 <= o -> o + n <= 140737488355328 -> acc bsegs m16 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch bsegs _ m15 m16 o n (conj H0 (conj H1 H)) MU16 (shfree_of_offsh _ o n OF16 H0 H1)))). }
assert (ACA16 : acc bsegs m16 A 48) by (apply ACC16; [exact ACA15| clear - FA1 FP0; lia| clear - FA2 BF1 LO736 SPT; lia]).
assert (ACO16 : acc bsegs m16 OUT 8000) by (apply ACC16; [exact ACO15| clear - FO1 FP0; lia| clear - FO2 BF1 LO736 SPT; lia]).
assert (ACT16 : acc bsegs m16 STEREO 24) by (apply ACC16; [exact ACT15| clear - FS1 FP0; lia| clear - FS2 BF1 LO736 SPT; lia]).
assert (ACV16 : acc bsegs m16 (usp + -800) 16) by (apply ACC16; [exact ACV15| clear - LOV' LOS; lia| clear - SPT; lia]).
assert (ACW16 : acc bsegs m16 (usp + -896) 16) by (apply ACC16; [exact ACW15| clear - LOV' LOS; lia| clear - SPT; lia]).
assert (SSP16 : io_ssp m16).
{ apply (sbd_io_ssp_agree m15 m16 SSP15 (AF_DRV Σ2 m16 ART16)). intros a0 Ha. apply MU16. unfold X0r9.SSP_GUARD in Ha. cbn [outside].
clear - Ha LOV' LOS. split; [lia| exact I]. }
destruct (af_acc_live RT AF Σ2 m16 S 160 ART16 INLX) as (_ & ACS16).
assert (OBS16 : aobj bsegs m16 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO736 SPT; unfold APP_TOP; lia| exact ACS16]).
clear ACA15 ACO15 ACT15 ACV15 ACW15 ACC16 SSP15 ACS15 OBS15 ART15 MI15 OF16 MU16.
clear Hc Hc0.

apply (rw_cells_split_CB bsegs _ _ [] 96 _ [] [32; 16; 48]%nat) in HU1; [| reflexivity]. cbn [mk_CB_cells app] in HU1.
apply rw_cells_uncons in HU1. destruct HU1 as (RZ1a & HU1). apply rw_cells_uncons in HU1. destruct HU1 as (PG1 & RZ1b).
cbn [csize] in PG1, RZ1b.
replace (usp + -832 + Z.of_nat 32) with (usp + -800) in PG1, RZ1b by lia. replace (usp + -800 + Z.of_nat 16) with (usp + -784) in RZ1b by lia.
destruct (rw_cells_CB_f32 bsegs m16 (usp + -800) 4 _ PG1) as (pg0 & Lpg0 & PGW). clear PG1.

assert (NDL : List.NoDup (map blk_id LBL)) by (pose proof NDUP as ND'; rewrite ELBD, map_app in ND'; exact (List.NoDup_app_remove_l _ _ ND')).
assert (AL8L : blocks_al8 LBL) by (intros bk Hb; apply LAL8; rewrite ELBD; apply in_app_iff; right; exact Hb).
assert (DEP3 : (dec_depth low3 <= 3)%nat) by (rewrite DL3; clear - DEPL; lia).
assert (FRM3 : (length (rt_frames RT Σ2) + dec_depth low3 <= FRAMES_MAX)%nat)
by (rewrite EF2, EF1, EFX, DL3; cbn [length]; pose proof (dec_depth_le_frames low) as DF; clear - FRM DF; lia).
assert (CRL3 : Z.of_nat (dec_depth low3) <= rt_credit RT Σ2 + 1)
by (rewrite EC2, EC1, DL3; pose proof (dec_credit_pos low) as DP; pose proof (dec_depth_pos low) as DP2; clear - CBX CRD DP DP2; lia).
assert (POA3 : pois_above (rt_pois RT Σ2) (bv_unsigned (Z_to_bv 64 (usp + -928)))).
{ rewrite EU800. intros e He. rewrite EP2, EP1 in He. destruct He as [<- | [<- | He]]; [unfold pz_lo; cbn [fst]; clear; lia| unfold pz_lo; cbn [fst]; clear; lia|].
rewrite EPX in He. pose proof (POA e He) as H1. clear - H1. lia. }
assert (ST800 : stk bsegs m16 lo (bv_unsigned (Z_to_bv 64 (usp + -928)))) by (rewrite EU800; exact ST15).
assert (LORC : lo + RT_STACK + ctl_stack low3 <= bv_unsigned (Z_to_bv 64 (usp + -928))).
{ rewrite EU800. destruct (dec_res_depth low3 low DL3) as (_ & _ & _ & RT3). rewrite RT3. pose proof (ctl_stack_le_dec low) as CL. clear - LOR CL. unfold RT_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in *. lia. }
assert (SPT800 : bv_unsigned (Z_to_bv 64 (usp + -928)) + 16 <= USTACK_TOP) by (rewrite EU800; clear - SPT; unfold USTACK_TOP in *; lia).
assert (SPA800 : bv_unsigned (Z_to_bv 64 (usp + -928)) mod 32 = 0) by (rewrite EU800; clear - SPA; Z.div_mod_to_equations; lia).
assert (DSTO : dst_obj RT Σ2 m16 (usp + -800) (creq_size CtlGetPiGain)) by (right; rewrite EP2, EP1; right; left; reflexivity).
cps_rt (CTL3 low3 DL3 Σ2 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m16 OUT OUT STEREO (a_low a) LBL CtlGetPiGain (usp + -800) lo
FDO MST eq_refl eq_refl eq_refl eq_refl eq_refl RLOW eq_refl DEP3 NDL AL8L I (ex_intro _ pg0 (conj PGW Lpg0)) LIVEL DSTO FRM3 CRL3 POA3
ART16 MI16 FRMX ST800 LOWX LORC SPT800 SPA800).
intros c8 (Σ3 & Hc8 & EL3 & EF3 & ES3 & EC3 & EP3).
cps_unpack_lib Hc8 as (m17 & RS17 & (ART17 & MI17 & WM17 & ST17) & PRES17 & RLOW17 & CP17 & EXK17 & DST17).
try rewrite EU800 in PRES17. try rewrite EU800 in ST17.
cbn [creq_ivs creq_size app] in PRES17. cbn [creq_post] in CP17. destruct CP17 as (pg1 & PGW1 & Lpg1).
clear DST17 DSTO PGW Lpg0 pg0 POA3 ST800 LORC SPT800 SPA800 FRM3 CRL3.

assert (OLB : forall x, (lo <= x \/ S <= x < S + 160 \/ fh <= x < fh + fs_size kh \/ PD <= x < PD + ND \/ f <= x < f + 64 \/ sf <= x < sf + 8 \/ 65536 <= x < 6664192) ->
(x < usp + -800 \/ usp + -784 <= x) -> outside ((usp + -800, usp + -800 + 16) :: blocks_ivs LBL) x).
{ intros x H1 H2. cbn [outside]. split; [clear - H2; lia| exact (OUTB x H1)]. }
tr1 PRES17 WM17 SV ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => apply OLB; [left; clear - Hx LO736; lia| clear - Hx; lia]).
tr1 PRES17 WM17 FR16 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => apply OLB; [left; clear - Hx LO736; lia| clear - Hx; lia]).
tr1 PRES17 WM17 RZ1a ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => apply OLB; [left; clear - Hx LOV'; lia| clear - Hx; lia]).
tr1 PRES17 WM17 RZ1b ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => apply OLB; [left; clear - Hx LOV'; lia| clear - Hx; lia]).
tr1 PRES17 WM17 HU2 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => apply OLB; [left; clear - Hx LOV'; lia| clear - Hx; lia]).
tr1 PRES17 WM17 FRB ltac:(fun x Hx => apply (CLF0g _ _ _ x INF); clear - Hx; lia)
ltac:(fun x Hx => apply OLB; [right; right; right; right; left; clear - Hx; lia| clear - Hx BF LOV'; lia]).
tr1 PRES17 WM17 FRS ltac:(fun x Hx => apply (CLSFg _ _ _ x INF); clear - Hx; lia)
ltac:(fun x Hx => apply OLB; [right; right; right; right; right; left; clear - Hx; lia| clear - Hx BF0 LOV'; lia]).
tr1 PRES17 WM17 OC ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); rewrite LOWS in Hx; clear - Hx FO1 FO2; lia)
ltac:(fun x Hx => apply OLB; [right; right; left; rewrite LOWS in Hx; clear - Hx FO1 FO2; lia| rewrite LOWS in Hx; clear - Hx FO2 BF1 LOV'; lia]).
tr1 PRES17 WM17 STB ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FS1 FS2; lia)
ltac:(fun x Hx => apply OLB; [right; right; left; clear - Hx FS1 FS2; lia| clear - Hx FS2 BF1 LOV'; lia]).
tr1 PRES17 WM17 BOBJ8 ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FA1 FA2; lia)
ltac:(fun x Hx => apply OLB; [right; right; left; clear - Hx FA1 FA2; lia| clear - Hx FA2 BF1 LOV'; lia]).
tr1 PRES17 WM17 BDAT8 ltac:(fun x Hx => apply (CLLg _ _ _ PD ND x INPDX); clear - Hx PD1 PD2 Lbs8; lia)
ltac:(fun x Hx => apply OLB; [right; right; right; left; clear - Hx PD1 PD2 Lbs8; lia| clear - Hx BD8 LOV'; lia]).
tr1 PRES17 WM17 X9 ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia)
ltac:(fun x Hx => apply OLB; [right; left; clear - Hx; lia| clear - Hx BS1 LOV'; lia]).
assert (AGB17 : agree_blocks bsegs m16 m17 (tl (sb_blocks s S a))).
{ apply (agree_blocks_of_pres_fp RT Σ2 _ _ _ m16 m17 _ PRES17 WM17); [intros bk Hb; apply LIVEA; unfold LALL; apply in_app_iff; left; exact Hb|].
intros bk x Hb Hx. pose proof (BOUT bk x ltac:(unfold LALL; apply in_app_iff; left; exact Hb) Hx) as H1. cbn [outside].
split; [clear - H1 LOV'; lia| exact (APL bk x Hb Hx)]. }
apply (sb_bufs_agree s S a j m16 m17) in BUFS; [| exact JOK | exact AGB17]. clear AGB17.
pk_io_fp PRES17 ERR_rep OUT_rep IO_FP IO_img ltac:(fun y Hy => apply OLB; [right; right; right; right; right; right; clear - Hy; lia| clear - Hy LOV' LOS; lia]).
assert (SSP17 : io_ssp m17).
{ apply (sbd_io_ssp_agree m16 m17 SSP16 (AF_DRV Σ3 m17 ART17)). intros a0 Ha. apply PRES17; [right; left; exact (sbd_ssp_static _ Ha)|].
unfold X0r9.SSP_GUARD in Ha. apply OLB; [right; right; right; right; right; right; clear - Ha; lia| clear - Ha LOV' LOS; lia]. }
assert (SHW17 : forall o n, fh <= o -> o + n <= fh + fs_size kh -> forall i, 0 <= i < n -> outside ((usp + -800, usp + -800 + 16) :: blocks_ivs LBL) (shad (o + i))).
{ intros o n H1 H2 i Hi.
assert (SR : SH_LO <= shad (o + i) < SH_HI).
{ pose proof (frame_facts RT AF Σ2 m16 fh kh ART16 INFHX) as (_ & _ & _ & _ & _ & _ & SA & SL & SH & _). split.
- unfold shad, SH_LO, SHB in *. assert (0 <= (o + i) / 8) by (apply Z.div_pos; lia). lia.
- assert (shad (o + i) < shad (fh + fs_size kh)); [| lia].
unfold shad. apply Z.add_lt_mono_r. apply Z.div_lt_upper_bound; [lia|].
assert (FH8 : fh mod 8 = 0) by (clear - FP64; Z.div_mod_to_equations; lia).
assert (FK8 : fs_size kh mod 8 = 0) by (destruct FS64 as (M64 & _); clear - M64; Z.div_mod_to_equations; lia).
assert (E : fh + fs_size kh = 8 * ((fh + fs_size kh) / 8)).
{ pose proof (Z.div_mod (fh + fs_size kh) 8 ltac:(lia)) as XD. rewrite Zplus_mod, FH8, FK8 in XD. cbn in XD. lia. }
lia. }
cbn [outside]. split; [clear - SR LOS LOV'; unfold SH_LO, SH_HI in *; lia|].
exact (outside_blocks_shadow RT AF Σ2 m16 LBL _ ART16 LIVEL SR). }
assert (FH8 : fh mod 8 = 0) by (clear - FP64; Z.div_mod_to_equations; lia).
assert (FK8 : fs_size kh mod 8 = 0) by (destruct FS64 as (M64 & _); clear - M64; Z.div_mod_to_equations; lia).
assert (ACA17 : acc bsegs m17 A 48)
by (apply (acc_pres_fp_frame _ _ _ _ m16 m17 fh kh A 48 PRES17 INFHX FH8 FK8 ltac:(lia) FA1 ltac:(lia) (SHW17 A 48 FA1 ltac:(lia)) ACA16)).
assert (ACO17 : acc bsegs m17 OUT 8000)
by (apply (acc_pres_fp_frame _ _ _ _ m16 m17 fh kh OUT 8000 PRES17 INFHX FH8 FK8 ltac:(lia) FO1 ltac:(lia) (SHW17 OUT 8000 FO1 ltac:(lia)) ACO16)).
assert (ACT17 : acc bsegs m17 STEREO 24)
by (apply (acc_pres_fp_frame _ _ _ _ m16 m17 fh kh STEREO 24 PRES17 INFHX FH8 FK8 ltac:(lia) FS1 ltac:(lia) (SHW17 STEREO 24 FS1 ltac:(lia)) ACT16)).
assert (PF17 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m17).
{ apply (pres_fp_trans _ _ _ _ m m16 m17 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ2) (rt_frames RT Σ2) (usp + -928) _ m16 m17 PRES17).
- intros e He. rewrite EL2, EL1, ELX. exact He.
- intros e He. rewrite EF2, EF1, EFX. right. exact He.
- clear; lia.
- intros x Hx Ho. cbn [outside] in Ho. destruct Ho as (_ & _ & _ & Ho). apply sb_outside_app_inv in Ho. destruct Ho as [Hb _].
rewrite ELBD in Hb. cbn [outside]. split; [destruct (SPL x Hx) as [H1 | H1]; clear - H1 LOW LOV'; lia| exact (outside_blocks_app_r _ _ x Hb)]. }
clear PF. rename PF17 into PF.
destruct (af_acc_live RT AF Σ3 m17 S 160 ART17 ltac:(rewrite EL3; exact INLX)) as (_ & ACS17).
assert (OBS17 : aobj bsegs m17 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO736 SPT; unfold APP_TOP; lia| exact ACS17]).
assert (EXR17 : EXCREADY m17 (a_low a) (speex_decoder_ctl low3 CtlGetPiGain).2) by (apply EXK17; apply EXR0; reflexivity).
clear EXK17 EXR0 RLOW SHW17 ACA16 ACO16 ACT16 ACV16 ACW16 SSP16 ACS16 OBS16 ART16 MI16 ST15 PRES17 OLB.
rename RLOW17 into RLOW.
rewrite <- EL3 in LIVEA, LIVEL, LIVED, INLX, INPDX. rewrite <- EF3 in INF, INFHX. rewrite <- ES3 in LOWX.

assert (EXR0 : 0 = 0 -> EXCREADY m17 (a_low a) (speex_decoder_ctl low3 CtlGetPiGain).2) by (intros _; exact EXR17). clear EXR17.
sb_unpack X9 as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_v4 usp S OUT A f (sbmode_struct (sbd_mode s)) _ sI a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
FR16 ltac:(gslot) HD OBS17 S8 SPOS ltac:(clear - BS1 LOV'; lia) SOFF ltac:(clear - LOS LOV'; unfold SH_HI in *; lia) SPH MI17).
clear HD FST PT LE SEED CFG IDC PAD.

subst ms.
set (m18 := m17) in *. clearbody m18. clear m17.
rename FR16 into FR18. rename ART17 into ART18. rename MI17 into MI18.
rename ACA17 into ACA18. rename ACO17 into ACO18. rename ACT17 into ACT18. rename SSP17 into SSP18. rename ACS17 into ACS18. rename OBS17 into OBS18.
rename EXR0 into EXR.

apply (rw_cells_split_CB bsegs _ _ [] 96 _ [] [32; 16; 48]%nat) in HU2; [| reflexivity]. cbn [mk_CB_cells app] in HU2.
apply rw_cells_uncons in HU2. destruct HU2 as (RZ2a & HU2). apply rw_cells_uncons in HU2. destruct HU2 as (ER2 & RZ2b).
cbn [csize] in ER2, RZ2b.
replace (usp + -928 + Z.of_nat 32) with (usp + -896) in ER2, RZ2b by lia. replace (usp + -896 + Z.of_nat 16) with (usp + -880) in RZ2b by lia.
destruct (rw_cells_CB_f32 bsegs m18 (usp + -896) 4 _ ER2) as (er0 & Ler0 & ERW). clear ER2.

assert (DL4 : dec_depth (speex_decoder_ctl low3 CtlGetPiGain).2 = dec_depth low) by (rewrite ctl_keeps_depth; exact DL3).
assert (DEP4 : (dec_depth (speex_decoder_ctl low3 CtlGetPiGain).2 <= 3)%nat) by (rewrite DL4; clear - DEPL; lia).
assert (FRM4 : (length (rt_frames RT Σ3) + dec_depth (speex_decoder_ctl low3 CtlGetPiGain).2 <= FRAMES_MAX)%nat)
by (rewrite EF3, EF2, EF1, EFX, DL4; cbn [length]; pose proof (dec_depth_le_frames low) as DF; clear - FRM DF; lia).
assert (CRL4 : Z.of_nat (dec_depth (speex_decoder_ctl low3 CtlGetPiGain).2) <= rt_credit RT Σ3 + 1).
{ rewrite DL4. rewrite DL3 in EC3. rewrite EC2, EC1 in EC3. pose proof (dec_credit_pos low) as DP. pose proof (dec_depth_pos low) as DP2. clear - CBX CRD DP DP2 EC3. lia. }
assert (POA4 : pois_above (rt_pois RT Σ3) (bv_unsigned (Z_to_bv 64 (usp + -928)))).
{ rewrite EU800. intros e He. rewrite EP3, EP2, EP1 in He. destruct He as [<- | [<- | He]]; [unfold pz_lo; cbn [fst]; clear; lia| unfold pz_lo; cbn [fst]; clear; lia|].
rewrite EPX in He. pose proof (POA e He) as H1. clear - H1. lia. }
assert (ST800 : stk bsegs m18 lo (bv_unsigned (Z_to_bv 64 (usp + -928)))) by (rewrite EU800; exact ST17).
assert (LORC : lo + RT_STACK + ctl_stack (speex_decoder_ctl low3 CtlGetPiGain).2 <= bv_unsigned (Z_to_bv 64 (usp + -928))).
{ rewrite EU800. destruct (dec_res_depth _ low DL4) as (_ & _ & _ & RT4). rewrite RT4. pose proof (ctl_stack_le_dec low) as CL. clear - LOR CL.
unfold RT_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in *. lia. }
assert (SPT800 : bv_unsigned (Z_to_bv 64 (usp + -928)) + 16 <= USTACK_TOP) by (rewrite EU800; clear - SPT; unfold USTACK_TOP in *; lia).
assert (SPA800 : bv_unsigned (Z_to_bv 64 (usp + -928)) mod 32 = 0) by (rewrite EU800; clear - SPA; Z.div_mod_to_equations; lia).
assert (DSTO : dst_obj RT Σ3 m18 (usp + -896) (creq_size CtlGetExc)) by (right; rewrite EP3, EP2; left; reflexivity).
cps_rt (CTL3 _ DL4 Σ3 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m18 OUT OUT STEREO (a_low a) LBL CtlGetExc (usp + -896) lo
FDO MST eq_refl eq_refl eq_refl eq_refl eq_refl RLOW eq_refl DEP4 NDL AL8L I (conj (ex_intro _ er0 (conj ERW Ler0)) (EXR eq_refl)) LIVEL DSTO FRM4 CRL4 POA4
ART18 MI18 RS17 ST800 LOWX LORC SPT800 SPA800).
intros c10 (Σ4 & Hc10 & EL4 & EF4 & ES4 & EC4 & EP4).
cps_unpack_lib Hc10 as (m19 & RS19 & (ART19 & MI19 & WM19 & ST19) & PRES19 & RLOW19 & CP19 & EXK19 & DST19).
try rewrite EU800 in PRES19. try rewrite EU800 in ST19.
cbn [creq_ivs creq_size app] in PRES19. cbn [creq_post] in CP19. destruct CP19 as (er1 & ERW1 & Ler1).
clear DST19 DSTO ERW Ler0 er0 POA4 ST800 LORC SPT800 SPA800 FRM4 CRL4.

assert (OLB : forall x, (lo <= x \/ S <= x < S + 160 \/ fh <= x < fh + fs_size kh \/ PD <= x < PD + ND \/ f <= x < f + 64 \/ sf <= x < sf + 8 \/ 65536 <= x < 6664192) ->
(x < usp + -896 \/ usp + -880 <= x) -> outside ((usp + -896, usp + -896 + 16) :: blocks_ivs LBL) x).
{ intros x H1 H2. cbn [outside]. split; [clear - H2; lia| exact (OUTB x H1)]. }
tr1 PRES19 WM19 SV ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => apply OLB; [left; clear - Hx LO736; lia| clear - Hx; lia]).
tr1 PRES19 WM19 FR18 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => apply OLB; [left; clear - Hx LO736; lia| clear - Hx; lia]).
tr1 PRES19 WM19 RZ1a ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => apply OLB; [left; clear - Hx LOV'; lia| clear - Hx; lia]).
tr1 PRES19 WM19 RZ1b ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => apply OLB; [left; clear - Hx LOV'; lia| clear - Hx; lia]).
tr1 PRES19 WM19 RZ2a ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => apply OLB; [left; clear - Hx LOV'; lia| clear - Hx; lia]).
tr1 PRES19 WM19 RZ2b ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => apply OLB; [left; clear - Hx LOV'; lia| clear - Hx; lia]).
tr1 PRES19 WM19 PGW1 ltac:(fun x Hx => apply CLSg; rewrite Lpg1 in Hx; clear - Hx; lia) ltac:(fun x Hx => apply OLB; [left; rewrite Lpg1 in Hx; clear - Hx LOV'; lia| rewrite Lpg1 in Hx; clear - Hx; lia]).
tr1 PRES19 WM19 FRB ltac:(fun x Hx => apply (CLF0g _ _ _ x INF); clear - Hx; lia)
ltac:(fun x Hx => apply OLB; [right; right; right; right; left; clear - Hx; lia| clear - Hx BF LOV'; lia]).
tr1 PRES19 WM19 FRS ltac:(fun x Hx => apply (CLSFg _ _ _ x INF); clear - Hx; lia)
ltac:(fun x Hx => apply OLB; [right; right; right; right; right; left; clear - Hx; lia| clear - Hx BF0 LOV'; lia]).
tr1 PRES19 WM19 OC ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); rewrite LOWS in Hx; clear - Hx FO1 FO2; lia)
ltac:(fun x Hx => apply OLB; [right; right; left; rewrite LOWS in Hx; clear - Hx FO1 FO2; lia| rewrite LOWS in Hx; clear - Hx FO2 BF1 LOV'; lia]).
tr1 PRES19 WM19 STB ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FS1 FS2; lia)
ltac:(fun x Hx => apply OLB; [right; right; left; clear - Hx FS1 FS2; lia| clear - Hx FS2 BF1 LOV'; lia]).
tr1 PRES19 WM19 BOBJ8 ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FA1 FA2; lia)
ltac:(fun x Hx => apply OLB; [right; right; left; clear - Hx FA1 FA2; lia| clear - Hx FA2 BF1 LOV'; lia]).
tr1 PRES19 WM19 BDAT8 ltac:(fun x Hx => apply (CLLg _ _ _ PD ND x INPDX); clear - Hx PD1 PD2 Lbs8; lia)
ltac:(fun x Hx => apply OLB; [right; right; right; left; clear - Hx PD1 PD2 Lbs8; lia| clear - Hx BD8 LOV'; lia]).
tr1 PRES19 WM19 X9 ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia)
ltac:(fun x Hx => apply OLB; [right; left; clear - Hx; lia| clear - Hx BS1 LOV'; lia]).
assert (AGB19 : agree_blocks bsegs m18 m19 (tl (sb_blocks s S a))).
{ apply (agree_blocks_of_pres_fp RT Σ3 _ _ _ m18 m19 _ PRES19 WM19); [intros bk Hb; apply LIVEA; unfold LALL; apply in_app_iff; left; exact Hb|].
intros bk x Hb Hx. pose proof (BOUT bk x ltac:(unfold LALL; apply in_app_iff; left; exact Hb) Hx) as H1. cbn [outside].
split; [clear - H1 LOV'; lia| exact (APL bk x Hb Hx)]. }
apply (sb_bufs_agree s S a j m18 m19) in BUFS; [| exact JOK | exact AGB19]. clear AGB19.
pk_io_fp PRES19 ERR_rep OUT_rep IO_FP IO_img ltac:(fun y Hy => apply OLB; [right; right; right; right; right; right; clear - Hy; lia| clear - Hy LOV' LOS; lia]).
assert (SSP19 : io_ssp m19).
{ apply (sbd_io_ssp_agree m18 m19 SSP18 (AF_DRV Σ4 m19 ART19)). intros a0 Ha. apply PRES19; [right; left; exact (sbd_ssp_static _ Ha)|].
unfold X0r9.SSP_GUARD in Ha. apply OLB; [right; right; right; right; right; right; clear - Ha; lia| clear - Ha LOV' LOS; lia]. }
assert (SHW19 : forall o n, fh <= o -> o + n <= fh + fs_size kh -> forall i, 0 <= i < n -> outside ((usp + -896, usp + -896 + 16) :: blocks_ivs LBL) (shad (o + i))).
{ intros o n H1 H2 i Hi.
assert (SR : SH_LO <= shad (o + i) < SH_HI).
{ pose proof (frame_facts RT AF Σ3 m18 fh kh ART18 INFHX) as (_ & _ & _ & _ & _ & _ & SA & SL & SH & _). split.
- unfold shad, SH_LO, SHB in *. assert (0 <= (o + i) / 8) by (apply Z.div_pos; lia). lia.
- assert (shad (o + i) < shad (fh + fs_size kh)); [| lia].
unfold shad. apply Z.add_lt_mono_r. apply Z.div_lt_upper_bound; [lia|].
assert (E : fh + fs_size kh = 8 * ((fh + fs_size kh) / 8)).
{ pose proof (Z.div_mod (fh + fs_size kh) 8 ltac:(lia)) as XD. rewrite Zplus_mod, FH8, FK8 in XD. cbn in XD. lia. }
lia. }
cbn [outside]. split; [clear - SR LOS LOV'; unfold SH_LO, SH_HI in *; lia|].
exact (outside_blocks_shadow RT AF Σ3 m18 LBL _ ART18 LIVEL SR). }
assert (ACA19 : acc bsegs m19 A 48)
by (apply (acc_pres_fp_frame _ _ _ _ m18 m19 fh kh A 48 PRES19 INFHX FH8 FK8 ltac:(lia) FA1 ltac:(lia) (SHW19 A 48 FA1 ltac:(lia)) ACA18)).
assert (ACO19 : acc bsegs m19 OUT 8000)
by (apply (acc_pres_fp_frame _ _ _ _ m18 m19 fh kh OUT 8000 PRES19 INFHX FH8 FK8 ltac:(lia) FO1 ltac:(lia) (SHW19 OUT 8000 FO1 ltac:(lia)) ACO18)).
assert (ACT19 : acc bsegs m19 STEREO 24)
by (apply (acc_pres_fp_frame _ _ _ _ m18 m19 fh kh STEREO 24 PRES19 INFHX FH8 FK8 ltac:(lia) FS1 ltac:(lia) (SHW19 STEREO 24 FS1 ltac:(lia)) ACT18)).
assert (PF19 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m19).
{ apply (pres_fp_trans _ _ _ _ m m18 m19 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ3) (rt_frames RT Σ3) (usp + -928) _ m18 m19 PRES19).
- intros e He. rewrite EL3, EL2, EL1, ELX. exact He.
- intros e He. rewrite EF3, EF2, EF1, EFX. right. exact He.
- clear; lia.
- intros x Hx Ho. cbn [outside] in Ho. destruct Ho as (_ & _ & _ & Ho). apply sb_outside_app_inv in Ho. destruct Ho as [Hb _].
rewrite ELBD in Hb. cbn [outside]. split; [destruct (SPL x Hx) as [H1 | H1]; clear - H1 LOW LOV'; lia| exact (outside_blocks_app_r _ _ x Hb)]. }
clear PF. rename PF19 into PF.
destruct (af_acc_live RT AF Σ4 m19 S 160 ART19 ltac:(rewrite EL4; exact INLX)) as (_ & ACS19).
assert (OBS19 : aobj bsegs m19 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO736 SPT; unfold APP_TOP; lia| exact ACS19]).
assert (EXR19 : EXCREADY m19 (a_low a) (speex_decoder_ctl (speex_decoder_ctl low3 CtlGetPiGain).2 CtlGetExc).2) by (apply EXK19; apply EXR; reflexivity).
clear EXK19 EXR RLOW SHW19 ACA18 ACO18 ACT18 SSP18 ACS18 OBS18 ART18 MI18 ST17 PRES19 OLB.
rename RLOW19 into RLOW.
rewrite <- EL4 in LIVEA, LIVEL, LIVED, INLX, INPDX. rewrite <- EF4 in INF, INFHX. rewrite <- ES4 in LOWX.

assert (WH1 : wr_at bsegs m19 (usp + -832) 96).
{ assert (J1 : rw_cells bsegs m19 (usp + -832) ([CB 32 (firstn 32 jh1)] ++ f32 pg1)).
{ apply rw_cells_join; [exact RZ1a|]. replace (usp + -832 + Z.of_nat (cells_size [CB 32 (firstn 32 jh1)])) with (usp + -800); [exact PGW1| cbn; lia]. }
assert (J2 : rw_cells bsegs m19 (usp + -832) (([CB 32 (firstn 32 jh1)] ++ f32 pg1) ++ [CB 48 (firstn 48 (skipn 16 (skipn 32 jh1)))])).
{ apply rw_cells_join; [exact J1|]. replace (usp + -832 + Z.of_nat (cells_size ([CB 32 (firstn 32 jh1)] ++ f32 pg1))) with (usp + -784); [exact RZ1b|].
rewrite cells_size_app, cells_size_f32, Lpg1. cbn. lia. }
pose proof (proj2 J2) as W. rewrite !cells_size_app, cells_size_f32, Lpg1 in W. exact W. }
assert (WH2 : wr_at bsegs m19 (usp + -928) 96).
{ assert (J1 : rw_cells bsegs m19 (usp + -928) ([CB 32 (firstn 32 jh2)] ++ f32 er1)).
{ apply rw_cells_join; [exact RZ2a|]. replace (usp + -928 + Z.of_nat (cells_size [CB 32 (firstn 32 jh2)])) with (usp + -896); [exact ERW1| cbn; lia]. }
assert (J2 : rw_cells bsegs m19 (usp + -928) (([CB 32 (firstn 32 jh2)] ++ f32 er1) ++ [CB 48 (firstn 48 (skipn 16 (skipn 32 jh2)))])).
{ apply rw_cells_join; [exact J1|]. replace (usp + -928 + Z.of_nat (cells_size ([CB 32 (firstn 32 jh2)] ++ f32 er1))) with (usp + -880); [exact RZ2b|].
rewrite cells_size_app, cells_size_f32, Ler1. cbn. lia. }
pose proof (proj2 J2) as W. rewrite !cells_size_app, cells_size_f32, Ler1 in W. exact W. }
clear RZ1a PGW1 RZ1b RZ2a ERW1 RZ2b Lpg1 Ler1 pg1 er1.
sb_unpack X9 as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_v5 usp lo S OUT A f (sbmode_struct (sbd_mode s)) _ sI a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
FR18 HD ILPC OBS19 S8 SPOS BS1 SOFF ST19 ltac:(clear - LOV'; lia) LOS SPH SPA MI19).
clear HD FST PT LE SEED CFG IDC PAD.
destruct POST as (m20 & xa220 & jh3 & -> & MU20 & WM20 & MI20 & ST20 & FR20 & HU3).
clear FR18 ST19.
assert (ART20 : X14x.ART RT Σ4 m20).
{ apply (af_frame RT AF Σ4 m19 m20 lo ART19 LOWX); [| exact WM20]. intros a0 Ha. apply MU20. cbn [outside]. split; [| exact I].
intros Hin. apply Ha. left. clear - Hin LOV' SPT. unfold USTACK_TOP. lia. }
assert (PF20 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m20).
{ apply (pres_fp_trans _ _ _ _ m m19 m20 PF). apply (pres_fp_of_munch _ _ _ _ _ m19 m20 MU20). intros x Hx Ho. cbn [outside]. split; [| exact I].
intros Hin. destruct (SPL x Hx) as [H1 | H1]; clear - H1 Hin LOW LOV'; lia. }
clear PF. rename PF20 into PF.
pk_munch_all MU20 WM20 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LOV'; cbn [outside]; split; [lia| exact I])
ltac:(fun x Hx => clear - Hx LOV' LOS; cbn [outside]; split; [lia| exact I]).
trm MU20 WM20 SV ltac:(clear; lia).
trm MU20 WM20 FRB ltac:(clear - BF LOV'; lia).
trm MU20 WM20 FRS ltac:(clear - BF0 LOV'; lia).
trm MU20 WM20 OC ltac:(rewrite LOWS; clear - FO2 BF1 LOV'; lia).
trm MU20 WM20 STB ltac:(clear - FS2 BF1 LOV'; lia).
trm MU20 WM20 BOBJ8 ltac:(clear - FA2 BF1 LOV'; lia).
trm MU20 WM20 BDAT8 ltac:(clear - BD8 LOV'; lia).
trm MU20 WM20 X9 ltac:(clear - BS1 LOV'; lia).
apply (wr_at_transport bsegs m19 m20 _ _) in WH1; [| exact WM20]. apply (wr_at_transport bsegs m19 m20 _ _) in WH2; [| exact WM20].
assert (OF20 : offsh [(usp + -5024, usp + -160)]) by (cbn [offsh]; clear - LOS LOV'; unfold SH_LO, SH_HI in *; lia).
assert (ACC20 : forall o n, acc bsegs m19 o n -> 0 <= o -> o + n <= 140737488355328 -> acc bsegs m20 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch bsegs _ m19 m20 o n (conj H0 (conj H1 H)) MU20 (shfree_of_offsh _ o n OF20 H0 H1)))). }
assert (ACA20 : acc bsegs m20 A 48) by (apply ACC20; [exact ACA19| clear - FA1 FP0; lia| clear - FA2 BF1 LO736 SPT; lia]).
assert (ACO20 : acc bsegs m20 OUT 8000) by (apply ACC20; [exact ACO19| clear - FO1 FP0; lia| clear - FO2 BF1 LO736 SPT; lia]).
assert (ACT20 : acc bsegs m20 STEREO 24) by (apply ACC20; [exact ACT19| clear - FS1 FP0; lia| clear - FS2 BF1 LO736 SPT; lia]).
assert (SSP20 : io_ssp m20).
{ apply (sbd_io_ssp_agree m19 m20 SSP19 (AF_DRV Σ4 m20 ART20)). intros a0 Ha. apply MU20. unfold X0r9.SSP_GUARD in Ha. cbn [outside].
clear - Ha LOV' LOS. split; [lia| exact I]. }
destruct (af_acc_live RT AF Σ4 m20 S 160 ART20 INLX) as (_ & ACS20).
assert (OBS20 : aobj bsegs m20 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO736 SPT; unfold APP_TOP; lia| exact ACS20]).
clear ACA19 ACO19 ACT19 ACC20 SSP19 ACS19 OBS19 ART19 MI19 OF20 MU20.

assert (EU896 : bv_unsigned (Z_to_bv 64 (usp + -1024)) = usp + -1024) by (apply unsigned_lit; clear - SPT LOV' LOS; lia).
assert (POA5 : pois_above (rt_pois RT Σ4) (alloca_rr (usp + -992) 32)).
{ intros e He. rewrite EP4, EP3, EP2, EP1 in He. destruct He as [<- | [<- | He]].
- unfold pz_lo, alloca_rr. cbn [fst]. clear - SPA. Z.div_mod_to_equations. lia.
- unfold pz_lo, alloca_rr. cbn [fst]. clear - SPA. Z.div_mod_to_equations. lia.
- rewrite EPX in He. pose proof (POA e He) as H1. unfold alloca_rr. clear - H1 SPA. Z.div_mod_to_equations. lia. }
assert (COK5 : call_ok RT Σ4 m20 (Z_to_bv 64 (usp + -1024)) lo).
{ unfold call_ok. rewrite EU896. split; [exact ST20|]. split; [exact LOWX|]. split; [clear - LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia|].
split; [clear - SPT; unfold USTACK_TOP in *; lia| clear - SPA; Z.div_mod_to_equations; lia]. }
cps_rt (APO Σ4 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m20 (usp + -992) 32 lo FDO MST eq_refl eq_refl
ltac:(clear - SPA; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(rewrite EU896; lia)
ltac:(unfold alloca_rr, USTACK_TOP; clear - SPA SPT; Z.div_mod_to_equations; lia)
POA5 ltac:(rewrite EF4, EF3, EF2, EF1, EFX; discriminate) ART20 MI20 COK5).
intros c12 (Σ5 & Hc12 & EP5 & EL5 & EF5 & ES5 & EC5).
destruct (ASTA_unpack RT Σ5 (PMfd F0 fs0) _ c12 Hc12) as (ms12 & PO12 & Hc12'); clear Hc12; cbv beta in PO12.
destruct PO12 as (m21 & v21 & RS21 & (ART21 & MI21 & WM21 & ST21) & PRES21 & ACV21 & ACK21).
cps_ret RS21.
rewrite EU896 in PRES21, ST21.
clear POA5 COK5.
pose proof (pres_fp_of_pres _ _ _ [] _ _ PRES21) as PF21.
tr1 PF21 WM21 SV ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF21 WM21 FR20 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF21 WM21 HU3 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF21 WM21 FRB ltac:(fun x Hx => apply (CLF0g _ _ _ x INF); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF21 WM21 FRS ltac:(fun x Hx => apply (CLSFg _ _ _ x INF); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF21 WM21 OC ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); rewrite LOWS in Hx; clear - Hx FO1 FO2; lia) ltac:(fun x Hx => exact I).
tr1 PF21 WM21 STB ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FS1 FS2; lia) ltac:(fun x Hx => exact I).
tr1 PF21 WM21 BOBJ8 ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FA1 FA2; lia) ltac:(fun x Hx => exact I).
tr1 PF21 WM21 BDAT8 ltac:(fun x Hx => apply (CLLg _ _ _ PD ND x INPDX); clear - Hx PD1 PD2 Lbs8; lia) ltac:(fun x Hx => exact I).
tr1 PF21 WM21 X9 ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => exact I).
apply (wr_at_transport bsegs m20 m21 _ _) in WH1; [| exact WM21]. apply (wr_at_transport bsegs m20 m21 _ _) in WH2; [| exact WM21].
pk_pres_all RT PRES21 WM21 LALL LIVEA ERR_rep OUT_rep IO_FP IO_img.
assert (ACA21 : acc bsegs m21 A 48) by (apply ACK21; [exact ACA20| clear - FA2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FA2 BF1 LOV'; lia]).
assert (ACO21 : acc bsegs m21 OUT 8000) by (apply ACK21; [exact ACO20| clear - FO2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FO2 BF1 LOV'; lia]).
assert (ACT21 : acc bsegs m21 STEREO 24) by (apply ACK21; [exact ACT20| clear - FS2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FS2 BF1 LOV'; lia]).
assert (ACS21 : acc bsegs m21 S 160) by (apply ACK21; [exact ACS20| clear - BS1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - BS1 LOV'; lia]).
assert (OBS21 : aobj bsegs m21 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO736 SPT; unfold APP_TOP; lia| exact ACS21]).
assert (SSP21 : io_ssp m21).
{ apply (sbd_io_ssp_agree m20 m21 SSP20 (AF_DRV Σ5 m21 ART21)). intros a0 Ha. apply PRES21. right; left. exact (sbd_ssp_static _ Ha). }
assert (PF21' : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m21).
{ apply (pres_fp_trans _ _ _ _ m m20 m21 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ4) (rt_frames RT Σ4) (usp + -1024) [] m20 m21 PF21).
- intros e He. rewrite EL4, EL3, EL2, EL1, ELX. exact He.
- intros e He. rewrite EF4, EF3, EF2, EF1, EFX. right. exact He.
- clear; lia.
- intros x _ _. exact I. }
clear PF. rename PF21' into PF.
clear ACA20 ACO20 ACT20 ACS20 OBS20 SSP20 ART20 MI20 ST20 PF21 PRES21 ACK21 ACV21.
rewrite <- EL5 in LIVEA, LIVEL, LIVED, INLX, INPDX. rewrite <- EF5 in INF, INFHX. rewrite <- ES5 in LOWX.

assert (WH3 : wr_at bsegs m21 (usp + -1024) 96) by (exact (proj2 HU3)). clear HU3.
cps_seg (sbd_v6 usp lo S OUT A f (sbmode_struct (sbd_mode s)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
FR20 ltac:(gslot) ltac:(gslot) ST21 ltac:(clear - LOV'; lia) LOS SPH SPA MI21).
destruct POST as (m22 & jh4 & -> & MU22 & WM22 & MI22 & ST22 & FR22 & HU4).
clear FR20 ST21.
assert (ART22 : X14x.ART RT Σ5 m22).
{ apply (af_frame RT AF Σ5 m21 m22 lo ART21 LOWX); [| exact WM22]. intros a0 Ha. apply MU22. cbn [outside]. split; [| exact I].
intros Hin. apply Ha. left. clear - Hin LOV' SPT. unfold USTACK_TOP. lia. }
assert (PF22 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m22).
{ apply (pres_fp_trans _ _ _ _ m m21 m22 PF). apply (pres_fp_of_munch _ _ _ _ _ m21 m22 MU22). intros x Hx Ho. cbn [outside]. split; [| exact I].
intros Hin. destruct (SPL x Hx) as [H1 | H1]; clear - H1 Hin LOW LOV'; lia. }
clear PF. rename PF22 into PF.
pk_munch_all MU22 WM22 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LOV'; cbn [outside]; split; [lia| exact I])
ltac:(fun x Hx => clear - Hx LOV' LOS; cbn [outside]; split; [lia| exact I]).
trm MU22 WM22 SV ltac:(clear; lia).
trm MU22 WM22 FRB ltac:(clear - BF LOV'; lia).
trm MU22 WM22 FRS ltac:(clear - BF0 LOV'; lia).
trm MU22 WM22 OC ltac:(rewrite LOWS; clear - FO2 BF1 LOV'; lia).
trm MU22 WM22 STB ltac:(clear - FS2 BF1 LOV'; lia).
trm MU22 WM22 BOBJ8 ltac:(clear - FA2 BF1 LOV'; lia).
trm MU22 WM22 BDAT8 ltac:(clear - BD8 LOV'; lia).
trm MU22 WM22 X9 ltac:(clear - BS1 LOV'; lia).
apply (wr_at_transport bsegs m21 m22 _ _) in WH1; [| exact WM22]. apply (wr_at_transport bsegs m21 m22 _ _) in WH2; [| exact WM22].
apply (wr_at_transport bsegs m21 m22 _ _) in WH3; [| exact WM22].
assert (OF22 : offsh [(usp + -5120, usp + -160)]) by (cbn [offsh]; clear - LOS LOV'; unfold SH_LO, SH_HI in *; lia).
assert (ACC22 : forall o n, acc bsegs m21 o n -> 0 <= o -> o + n <= 140737488355328 -> acc bsegs m22 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch bsegs _ m21 m22 o n (conj H0 (conj H1 H)) MU22 (shfree_of_offsh _ o n OF22 H0 H1)))). }
assert (ACA22 : acc bsegs m22 A 48) by (apply ACC22; [exact ACA21| clear - FA1 FP0; lia| clear - FA2 BF1 LO736 SPT; lia]).
assert (ACO22 : acc bsegs m22 OUT 8000) by (apply ACC22; [exact ACO21| clear - FO1 FP0; lia| clear - FO2 BF1 LO736 SPT; lia]).
assert (ACT22 : acc bsegs m22 STEREO 24) by (apply ACC22; [exact ACT21| clear - FS1 FP0; lia| clear - FS2 BF1 LO736 SPT; lia]).
assert (SSP22 : io_ssp m22).
{ apply (sbd_io_ssp_agree m21 m22 SSP21 (AF_DRV Σ5 m22 ART22)). intros a0 Ha. apply MU22. unfold X0r9.SSP_GUARD in Ha. cbn [outside].
clear - Ha LOV' LOS. split; [lia| exact I]. }
destruct (af_acc_live RT AF Σ5 m22 S 160 ART22 INLX) as (_ & ACS22).
assert (OBS22 : aobj bsegs m22 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO736 SPT; unfold APP_TOP; lia| exact ACS22]).
clear ACA21 ACO21 ACT21 ACC22 SSP21 ACS21 OBS21 ART21 MI21 OF22 MU22.

assert (EU992 : bv_unsigned (Z_to_bv 64 (usp + -1120)) = usp + -1120) by (apply unsigned_lit; clear - SPT LOV' LOS; lia).
assert (POA6 : pois_above (rt_pois RT Σ5) (alloca_rr (usp + -1088) 32)).
{ intros e He. rewrite EP5, EP4, EP3, EP2, EP1 in He. destruct He as [<- | [<- | [<- | He]]].
- unfold pz_lo, alloca_rr. cbn [fst]. clear - SPA. Z.div_mod_to_equations. lia.
- unfold pz_lo, alloca_rr. cbn [fst]. clear - SPA. Z.div_mod_to_equations. lia.
- unfold pz_lo, alloca_rr. cbn [fst]. clear - SPA. Z.div_mod_to_equations. lia.
- rewrite EPX in He. pose proof (POA e He) as H1. unfold alloca_rr. clear - H1 SPA. Z.div_mod_to_equations. lia. }
assert (COK6 : call_ok RT Σ5 m22 (Z_to_bv 64 (usp + -1120)) lo).
{ unfold call_ok. rewrite EU992. split; [exact ST22|]. split; [exact LOWX|]. split; [clear - LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia|].
split; [clear - SPT; unfold USTACK_TOP in *; lia| clear - SPA; Z.div_mod_to_equations; lia]. }
cps_rt (APO Σ5 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m22 (usp + -1088) 32 lo FDO MST eq_refl eq_refl
ltac:(clear - SPA; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(rewrite EU992; lia)
ltac:(unfold alloca_rr, USTACK_TOP; clear - SPA SPT; Z.div_mod_to_equations; lia)
POA6 ltac:(rewrite EF5, EF4, EF3, EF2, EF1, EFX; discriminate) ART22 MI22 COK6).
intros c14 (Σ6 & Hc14 & EP6 & EL6 & EF6 & ES6 & EC6).
destruct (ASTA_unpack RT Σ6 (PMfd F0 fs0) _ c14 Hc14) as (ms14 & PO14 & Hc14'); clear Hc14; cbv beta in PO14.
destruct PO14 as (m23 & v23 & RS23 & (ART23 & MI23 & WM23 & ST23) & PRES23 & ACV23 & ACK23).
cps_ret RS23.
rewrite EU992 in PRES23, ST23.
clear POA6 COK6.
pose proof (pres_fp_of_pres _ _ _ [] _ _ PRES23) as PF23.
tr1 PF23 WM23 SV ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF23 WM23 FR22 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF23 WM23 HU4 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF23 WM23 FRB ltac:(fun x Hx => apply (CLF0g _ _ _ x INF); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF23 WM23 FRS ltac:(fun x Hx => apply (CLSFg _ _ _ x INF); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF23 WM23 OC ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); rewrite LOWS in Hx; clear - Hx FO1 FO2; lia) ltac:(fun x Hx => exact I).
tr1 PF23 WM23 STB ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FS1 FS2; lia) ltac:(fun x Hx => exact I).
tr1 PF23 WM23 BOBJ8 ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FA1 FA2; lia) ltac:(fun x Hx => exact I).
tr1 PF23 WM23 BDAT8 ltac:(fun x Hx => apply (CLLg _ _ _ PD ND x INPDX); clear - Hx PD1 PD2 Lbs8; lia) ltac:(fun x Hx => exact I).
tr1 PF23 WM23 X9 ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => exact I).
apply (wr_at_transport bsegs m22 m23 _ _) in WH1; [| exact WM23]. apply (wr_at_transport bsegs m22 m23 _ _) in WH2; [| exact WM23].
apply (wr_at_transport bsegs m22 m23 _ _) in WH3; [| exact WM23].
pk_pres_all RT PRES23 WM23 LALL LIVEA ERR_rep OUT_rep IO_FP IO_img.
assert (ACA23 : acc bsegs m23 A 48) by (apply ACK23; [exact ACA22| clear - FA2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FA2 BF1 LOV'; lia]).
assert (ACO23 : acc bsegs m23 OUT 8000) by (apply ACK23; [exact ACO22| clear - FO2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FO2 BF1 LOV'; lia]).
assert (ACT23 : acc bsegs m23 STEREO 24) by (apply ACK23; [exact ACT22| clear - FS2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FS2 BF1 LOV'; lia]).
assert (ACS23 : acc bsegs m23 S 160) by (apply ACK23; [exact ACS22| clear - BS1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - BS1 LOV'; lia]).
assert (OBS23 : aobj bsegs m23 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO736 SPT; unfold APP_TOP; lia| exact ACS23]).
assert (SSP23 : io_ssp m23).
{ apply (sbd_io_ssp_agree m22 m23 SSP22 (AF_DRV Σ6 m23 ART23)). intros a0 Ha. apply PRES23. right; left. exact (sbd_ssp_static _ Ha). }
assert (PF23' : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m23).
{ apply (pres_fp_trans _ _ _ _ m m22 m23 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ5) (rt_frames RT Σ5) (usp + -1120) [] m22 m23 PF23).
- intros e He. rewrite EL5, EL4, EL3, EL2, EL1, ELX. exact He.
- intros e He. rewrite EF5, EF4, EF3, EF2, EF1, EFX. right. exact He.
- clear; lia.
- intros x _ _. exact I. }
clear PF. rename PF23' into PF.
clear ACA22 ACO22 ACT22 ACS22 OBS22 SSP22 ART22 MI22 ST22 PF23 PRES23 ACK23 ACV23.
rewrite <- EL6 in LIVEA, LIVEL, LIVED, INLX, INPDX. rewrite <- EF6 in INF, INFHX. rewrite <- ES6 in LOWX.

assert (HMO' : sbd_mode s = ModeWB \/ sbd_mode s = ModeUWB) by (clear - IMODE; unfold hid in *; exact IMODE).
pose proof (sb_submode_cases (sbd_mode s) id sm HMO' ltac:(clear - IDR; lia) ESM) as SMC.
assert (IDC4 : id = 1 \/ id = 2 \/ id = 3 \/ id = 4) by (clear - SMC; destruct SMC as [(_ & [(-> & _)|[(-> & _)|[(-> & _)|(-> & _)]]])|(_ & -> & _)]; lia).
assert (ELQ : sm_lsp_unquant sm = LspUnquantHigh)
by (clear - SMC; destruct SMC as [(_ & [(_ & ->)|[(_ & ->)|[(_ & ->)|(_ & ->)]]])|(_ & _ & ->)]; reflexivity).
pose proof (AF_LIB Σ6 m23 ART23) as LC23.
assert (OBSM : aobj bsegs m23 (sb_sub_addr id) 88).
{ destruct IDC4 as [E|[E|[E|E]]]; rewrite E; cbn [sb_sub_addr Z.eqb Pos.eqb]; (apply (aobj_lit RT AF Σ6 m23 _ 88 ART23);
[ unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_wb_submode1, A_wb_submode2, A_wb_submode3, A_wb_submode4; lia
| unfold A_wb_submode1, A_wb_submode2, A_wb_submode3, A_wb_submode4, APP_TOP; lia]). }
assert (OBM23 : aobj bsegs m23 (sbmode_struct (sbd_mode s)) 216).
{ destruct IMODE as [E|E]; rewrite E; cbn [sbmode_struct]; (apply (aobj_lit RT AF Σ6 m23 _ 216 ART23);
[ unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_sb_wb_mode, A_sb_uwb_mode; lia | unfold A_sb_wb_mode, A_sb_uwb_mode, APP_TOP; lia]). }
sb_unpack X9 as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_v7 usp S OUT A f (sbmode_struct (sbd_mode s)) (sb_sub_addr id) id _ s (sj_pad1 j) sm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
FR22 ltac:(gslot) ltac:(gslot) ltac:(gslot) ltac:(gslot) ltac:(gslot) ltac:(gslot)
CFG IDC OBS23 S8 SPOS ltac:(clear - BS1 LOV'; lia) SOFF HMO' eq_refl OBM23 ESM ltac:(clear - IDR; lia) eq_refl OBSM LC23
ltac:(clear - LOS LOV'; unfold SH_HI in *; lia) SPH MI23).
clear HD FST PT LE SEED CFG IDC PAD OBSM OBM23 LC23.
destruct POST as (m24 & xa324 & -> & MU24 & WM24 & MI24 & FR24).
clear FR22.
assert (ART24 : X14x.ART RT Σ6 m24).
{ apply (af_frame RT AF Σ6 m23 m24 lo ART23 LOWX); [| exact WM24]. intros a0 Ha. apply MU24. cbn [outside]. split; [| exact I].
intros Hin. apply Ha. left. clear - Hin LOV' SPT. unfold USTACK_TOP. lia. }
assert (PF24 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m24).
{ apply (pres_fp_trans _ _ _ _ m m23 m24 PF). apply (pres_fp_of_munch _ _ _ _ _ m23 m24 MU24). intros x Hx Ho. cbn [outside]. split; [| exact I].
intros Hin. destruct (SPL x Hx) as [H1 | H1]; clear - H1 Hin LOW LOV'; lia. }
clear PF. rename PF24 into PF.
pk_munch_all MU24 WM24 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LOV'; cbn [outside]; split; [lia| exact I])
ltac:(fun x Hx => clear - Hx LOV' LOS; cbn [outside]; split; [lia| exact I]).
trm MU24 WM24 SV ltac:(clear; lia).
trm MU24 WM24 HU4 ltac:(clear; lia).
trm MU24 WM24 FRB ltac:(clear - BF LOV'; lia).
trm MU24 WM24 FRS ltac:(clear - BF0 LOV'; lia).
trm MU24 WM24 OC ltac:(rewrite LOWS; clear - FO2 BF1 LOV'; lia).
trm MU24 WM24 STB ltac:(clear - FS2 BF1 LOV'; lia).
trm MU24 WM24 BOBJ8 ltac:(clear - FA2 BF1 LOV'; lia).
trm MU24 WM24 BDAT8 ltac:(clear - BD8 LOV'; lia).
trm MU24 WM24 X9 ltac:(clear - BS1 LOV'; lia).
apply (stk_transport_disjoint bsegs [(usp + -736, usp + -160)] m23 m24 lo (usp + -1120)) in ST23; [| exact MU24 | exact WM24 | cbn [disjoint_from]; clear; lia].
apply (wr_at_transport bsegs m23 m24 _ _) in WH1; [| exact WM24]. apply (wr_at_transport bsegs m23 m24 _ _) in WH2; [| exact WM24].
apply (wr_at_transport bsegs m23 m24 _ _) in WH3; [| exact WM24].
assert (OF24 : offsh [(usp + -736, usp + -160)]) by (cbn [offsh]; clear - LOS LOV'; unfold SH_LO, SH_HI in *; lia).
assert (ACC24 : forall o n, acc bsegs m23 o n -> 0 <= o -> o + n <= 140737488355328 -> acc bsegs m24 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch bsegs _ m23 m24 o n (conj H0 (conj H1 H)) MU24 (shfree_of_offsh _ o n OF24 H0 H1)))). }
assert (ACA24 : acc bsegs m24 A 48) by (apply ACC24; [exact ACA23| clear - FA1 FP0; lia| clear - FA2 BF1 LO736 SPT; lia]).
assert (ACO24 : acc bsegs m24 OUT 8000) by (apply ACC24; [exact ACO23| clear - FO1 FP0; lia| clear - FO2 BF1 LO736 SPT; lia]).
assert (ACT24 : acc bsegs m24 STEREO 24) by (apply ACC24; [exact ACT23| clear - FS1 FP0; lia| clear - FS2 BF1 LO736 SPT; lia]).
assert (SSP24 : io_ssp m24).
{ apply (sbd_io_ssp_agree m23 m24 SSP23 (AF_DRV Σ6 m24 ART24)). intros a0 Ha. apply MU24. unfold X0r9.SSP_GUARD in Ha. cbn [outside].
clear - Ha LOV' LOS. split; [lia| exact I]. }
destruct (af_acc_live RT AF Σ6 m24 S 160 ART24 INLX) as (_ & ACS24).
assert (OBS24 : aobj bsegs m24 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO736 SPT; unfold APP_TOP; lia| exact ACS24]).
clear ACA23 ACO23 ACT23 ACC24 SSP23 ACS23 OBS23 ART23 MI23 OF24 MU24.

destruct (wr_at_rw_CB m24 (usp + -1024) 96 WH3 ltac:(lia)) as (jh3' & HU3). clear WH3. change (Z.to_nat 96) with 96%nat in HU3.
apply (rw_cells_split_CB bsegs _ _ [] 96 _ [] [32; 32; 32]%nat) in HU3; [| reflexivity]. cbn [mk_CB_cells app] in HU3.
apply rw_cells_uncons in HU3. destruct HU3 as (RZ3a & HU3). apply rw_cells_uncons in HU3. destruct HU3 as (QL3 & RZ3b).
cbn [csize] in QL3, RZ3b.
replace (usp + -1024 + Z.of_nat 32) with (usp + -992) in QL3, RZ3b by lia. replace (usp + -992 + Z.of_nat 32) with (usp + -960) in RZ3b by lia.
destruct (rw_cells_CB_f32 bsegs m24 (usp + -992) 8 _ QL3) as (ql0 & Lql0 & QLW). clear QL3.
assert (BREP24 : bits_rep bsegs m24 A D (sbw_bits b1)).
{ split; [exists rj8; split; [exact Lrj8| unfold bits_cells; exact BOBJ8]|].
split; [exists bs8; split; [apply (proj2 (u8arr_rw_CB m24 D bs8)); exact BDAT8| exact Hbs8]| exact BSIDE8]. }
assert (OBA24 : aobj bsegs m24 A BITS_SIZEOF) by (split; [clear - AIMG; unfold IMG_TOP_B in *; lia|]; split; [clear - ALO LO736 SPT; unfold APP_TOP, BITS_SIZEOF in *; lia| exact ACA24]).
assert (OBD24 : aobj bsegs m24 D (sb_buf_size (sbw_bits b1))).
{ rewrite BSZ8. destruct (af_acc_live RT AF Σ6 m24 PD ND ART24 INPDX) as (_ & ACPD).
split; [clear - PD1 PDP; lia|]. split; [clear - DLO LO736 SPT; unfold APP_TOP; lia|].
apply (acc_sub bsegs m24 PD ND D (sb_buf_size b1) ACPD); clear - PD1 PD2; lia. }
assert (INQ : In (usp + -992, 32) (rt_pois RT Σ6)) by (rewrite EP6, EP5; right; left; reflexivity).
assert (OBQ24 : aobj bsegs m24 (usp + -992) (4 * lsp_order LspUnquantHigh))
by (cbn [lsp_order]; split; [clear - LOV' LOS; lia|]; split; [clear - SPT; unfold APP_TOP, USTACK_TOP in *; lia| exact (af_acc_pois RT AF Σ6 m24 _ _ ART24 INQ)]).
assert (LT24 : lsp_tabs m24).
{ assert (K : forall a n, In (a, n) ACC_LITS -> 0 <= a -> a + n <= APP_TOP -> aobj bsegs m24 a n) by (intros a0 n; exact (aobj_lit RT AF Σ6 m24 a0 n ART24)).
unfold lsp_tabs, A_cdbk_nb, A_cdbk_nb_low1, A_cdbk_nb_low2, A_cdbk_nb_high1, A_cdbk_nb_high2, A_high_lsp_cdbk, A_high_lsp_cdbk2.
repeat match goal with |- _ /\ _ => split end;
(apply K; [unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | lia | unfold APP_TOP; lia]). }
pose proof (AF_LIB Σ6 m24 ART24) as LC24. pose proof (af_client_consts RT AF Σ6 m24 ART24) as CC24.
cps_seg (lsp_unquant_high_stmt bptr A D (usp + -992) (usp + -1120) lo (sbw_bits b1) ql0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m24
BREP24 BOK8 OBA24 OBD24 OBQ24 LT24 LC24 CC24 QLW Lql0 ltac:(clear - SPA; Z.div_mod_to_equations; lia) ASH
ltac:(right; clear - LOS LOV'; unfold SH_HI in *; lia) ltac:(unfold IMG_TOP_B; clear - AIMG; unfold IMG_TOP_B in *; lia) ltac:(unfold IMG_TOP_B; clear - LOV' LOS; lia)
ltac:(unfold BITS_SIZEOF; exact ALO) ltac:(rewrite BSZ8; exact DLO) ltac:(right; clear; lia)
ltac:(right; clear - ALO LOV'; unfold BITS_SIZEOF; lia) ltac:(right; rewrite BSZ8; clear - DLO LOV'; lia)
ST23 ltac:(unfold LSPQ_DEPTH; clear - LOV'; lia) LOS ltac:(clear - SPH; lia) MI24 RS19).
clear BREP24 OBA24 OBD24 OBQ24 LT24 LC24 CC24 QLW Lql0 ql0 INQ.
destruct POST as (t025 & t125 & t225 & a025 & a125 & a225 & a325 & a425 & a525 & a625 & a725 & t325 & t425 & t525 & t625 & F25 & fc25 & m25 & ql1 &
-> & MU25 & WM25 & MI25 & ST25 & FRM25 & QLW1 & Lql1 & BREP25 & BOK25).
clear ST23.

rewrite ELQ in Hk.
assert (BSZ25 : sb_buf_size (lsp_bits LspUnquantHigh (sbw_bits b1)) = sb_buf_size b1)
by (pose proof (bkeep_lsp LspUnquantHigh (sbw_bits b1)) as (_ & _ & K3); rewrite K3; exact BSZ8).
destruct BREP25 as ((rj25 & Lrj25 & BOBJ25) & (bs25 & BDAT25 & Hbs25) & BSIDE25). apply u8arr_rw_CB in BDAT25. unfold bits_cells in BOBJ25.
assert (Lbs25 : Z.of_nat (length bs25) = sb_buf_size b1)
by (pose proof BOK25 as OK'; unfold bits_ok in OK'; rewrite Hbs25, zlength_map_unsigned, BSZ25 in OK'; clear - OK'; lia).
clear BOBJ8 BDAT8 Hbs8 BSIDE8 BOK8 Lrj8 Lbs8 BD8 BDS BSZ8 rj8 bs8.
rename BOBJ25 into BOBJ8, BDAT25 into BDAT8, Hbs25 into Hbs8, BSIDE25 into BSIDE8, BOK25 into BOK8, Lrj25 into Lrj8, Lbs25 into Lbs8, BSZ25 into BSZ8, rj25 into rj8, bs25 into bs8.
assert (BD8 : D + Z.of_nat (length bs8) <= lo) by (rewrite Lbs8; exact DLO).
assert (BDS : D + Z.of_nat (length bs8) <= S \/ S + 160 <= D) by (clear - SPD PD1 PD2 Lbs8; lia).
assert (ART25 : X14x.ART RT Σ6 m25).
{ apply (af_frame RT AF Σ6 m24 m25 lo ART24 LOWX); [| exact WM25]. intros a0 Ha. apply MU25. cbn [outside]. unfold BITS_SIZEOF, LSPQ_DEPTH; cbn [lsp_order].
split; [| split; [| split; [| exact I]]]; intros Hin; apply Ha.
- right; right; right; left. exists fh, kh. split; [exact INFHX| clear - Hin FA1 FA2; lia].
- left. clear - Hin LOV' SPT. unfold USTACK_TOP. lia.
- left. clear - Hin LOV' SPT. unfold USTACK_TOP. lia. }
assert (PF25 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m25).
{ apply (pres_fp_trans _ _ _ _ m m24 m25 PF). apply (pres_fp_of_munch _ _ _ _ _ m24 m25 MU25). intros x Hx Ho. cbn [outside] in Ho |- *.
unfold BITS_SIZEOF, LSPQ_DEPTH; cbn [lsp_order]. destruct Ho as (HA & _).
split; [exact HA|]. split; [| split; [| exact I]]; intros Hin; destruct (SPL x Hx) as [H1 | H1]; clear - H1 Hin LOW LOV'; lia. }
clear PF. rename PF25 into PF.
pk_munch_all MU25 WM25 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LOV' FA1 FA2; cbn [outside]; unfold BITS_SIZEOF, LSPQ_DEPTH; cbn [lsp_order];
split; [lia| split; [lia| split; [lia| exact I]]])
ltac:(fun x Hx => clear - Hx LOV' LOS AIMG; unfold IMG_TOP_B in *; cbn [outside]; unfold BITS_SIZEOF, LSPQ_DEPTH; cbn [lsp_order]; split; [lia| split; [lia| split; [lia| exact I]]]).
trm MU25 WM25 SV ltac:(unfold BITS_SIZEOF, LSPQ_DEPTH; cbn [lsp_order]; clear - ALO LO736; lia).
trm MU25 WM25 FR24 ltac:(unfold BITS_SIZEOF, LSPQ_DEPTH; cbn [lsp_order]; clear - ALO LO736; lia).
trm MU25 WM25 HU4 ltac:(unfold BITS_SIZEOF, LSPQ_DEPTH; cbn [lsp_order]; clear - ALO LOV'; lia).
trm MU25 WM25 RZ3a ltac:(unfold BITS_SIZEOF, LSPQ_DEPTH; cbn [lsp_order]; clear - ALO LOV'; lia).
trm MU25 WM25 RZ3b ltac:(unfold BITS_SIZEOF, LSPQ_DEPTH; cbn [lsp_order]; clear - ALO LOV'; lia).
trm MU25 WM25 FRB ltac:(unfold BITS_SIZEOF, LSPQ_DEPTH; cbn [lsp_order]; clear - BF LOV' FFA FA1 FA2; unfold hid in *; lia).
trm MU25 WM25 FRS ltac:(unfold BITS_SIZEOF, LSPQ_DEPTH; cbn [lsp_order]; clear - BF0 LOV' ASH SHF1 SHF2 FA1 FA2; unfold hid in *; lia).
trm MU25 WM25 OC ltac:(unfold BITS_SIZEOF, LSPQ_DEPTH; cbn [lsp_order]; rewrite LOWS; clear - FO2 BF1 LOV' HAO'; unfold hid in *; lia).
trm MU25 WM25 STB ltac:(unfold BITS_SIZEOF, LSPQ_DEPTH; cbn [lsp_order]; clear - FS2 BF1 LOV' HAS'; unfold hid in *; lia).
trm MU25 WM25 X9 ltac:(unfold BITS_SIZEOF, LSPQ_DEPTH; cbn [lsp_order]; clear - BS1 LOV' SFH FA1 FA2; unfold hid in *; lia).
apply (wr_at_transport bsegs m24 m25 _ _) in WH1; [| exact WM25]. apply (wr_at_transport bsegs m24 m25 _ _) in WH2; [| exact WM25].
assert (OF25 : offsh [(A, A + BITS_SIZEOF); (usp + -992, usp + -992 + 4 * lsp_order LspUnquantHigh); (usp + -1120 + - LSPQ_DEPTH, usp + -1120)])
by (cbn [offsh lsp_order]; unfold BITS_SIZEOF, LSPQ_DEPTH; clear - LOS LOV' ASH; unfold hid, SH_LO, SH_HI in *; lia).
assert (ACC25 : forall o n, acc bsegs m24 o n -> 0 <= o -> o + n <= 140737488355328 -> acc bsegs m25 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch bsegs _ m24 m25 o n (conj H0 (conj H1 H)) MU25 (shfree_of_offsh _ o n OF25 H0 H1)))). }
assert (ACA25 : acc bsegs m25 A 48) by (apply ACC25; [exact ACA24| clear - FA1 FP0; lia| clear - FA2 BF1 LO736 SPT; lia]).
assert (ACO25 : acc bsegs m25 OUT 8000) by (apply ACC25; [exact ACO24| clear - FO1 FP0; lia| clear - FO2 BF1 LO736 SPT; lia]).
assert (ACT25 : acc bsegs m25 STEREO 24) by (apply ACC25; [exact ACT24| clear - FS1 FP0; lia| clear - FS2 BF1 LO736 SPT; lia]).
assert (SSP25 : io_ssp m25).
{ apply (sbd_io_ssp_agree m24 m25 SSP24 (AF_DRV Σ6 m25 ART25)). intros a0 Ha. apply MU25. unfold X0r9.SSP_GUARD in Ha. cbn [outside lsp_order].
unfold BITS_SIZEOF, LSPQ_DEPTH. clear - Ha LOV' LOS AIMG. unfold IMG_TOP_B in *. split; [lia| split; [lia| split; [lia| exact I]]]. }
destruct (af_acc_live RT AF Σ6 m25 S 160 ART25 INLX) as (_ & ACS25).
assert (OBS25 : aobj bsegs m25 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO736 SPT; unfold APP_TOP; lia| exact ACS25]).
clear ACA24 ACO24 ACT24 ACC25 SSP24 ACS24 OBS24 ART24 MI24 OF25 MU25.

destruct BUFS as (G0C & G1C & EXC & OQC & IQC & MSPC & PGC & ERC).
pose proof JOK1 as (JP1 & JP2 & JG0 & JG1 & JEXC & JOQ & JIQ & JMSP & JPG & JER).
assert (AL : sb_addrs_al a) by (apply (sb_addrs_al_of_blocks s S a); intros bk Hb; apply LAL8; rewrite ELBD; apply in_app_iff; left; exact Hb).
assert (NDA : List.NoDup [S; a_g0 a; a_g1 a; a_exc a; a_oq a; a_iq a; a_pg a; a_er a; a_msp a]).
{ pose proof NDUP as ND'. rewrite ELBD, map_app in ND'. apply List.NoDup_app_remove_r in ND'. exact ND'. }
repeat rewrite List.NoDup_cons_iff in NDA. cbn [In] in NDA.
assert (INOQ : In (a_oq a, 32) (rt_live RT Σ6)) by (apply (LIVEA (sbd_old_qlsp s, a_oq a, 32)); unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; do 3 right; left; reflexivity).
destruct (live_facts RT AF Σ6 m25 _ _ ART25 INOQ) as (OQP & _ & _ & OQSH).
destruct (live_below_lo RT AF Σ6 m25 _ _ lo ART25 INOQ LOWX) as (_ & OQLO & _).
destruct (af_acc_live RT AF Σ6 m25 _ _ ART25 INOQ) as (_ & ACOQ).
assert (OBOQ : aobj bsegs m25 (a_oq a) 32) by (split; [clear - OQP; lia|]; split; [clear - OQLO LO736 SPT; unfold APP_TOP; lia| exact ACOQ]).
assert (OQ8 : a_oq a mod 8 = 0) by (destruct AL as (_ & _ & _ & X8 & _); exact X8).
pose proof (BOUT (sbd_old_qlsp s, a_oq a, 32) (a_oq a) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; do 3 right; left; reflexivity)
ltac:(unfold blk_addr, blk_size; cbn [fst snd]; clear; lia)) as BOQ0.
pose proof (BOUT (sbd_old_qlsp s, a_oq a, 32) (a_oq a + 31) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; do 3 right; left; reflexivity)
ltac:(unfold blk_addr, blk_size; cbn [fst snd]; clear; lia)) as BOQ1.
assert (OQS : S + 160 <= a_oq a \/ a_oq a + 32 <= S) by (clear - BOQ0 BOQ1; lia).
assert (EQL : Z.to_nat (lsp_order LspUnquantHigh) = 8%nat) by reflexivity. rewrite EQL in Lql1.
assert (INQ : In (usp + -992, 32) (rt_pois RT Σ6)) by (rewrite EP6, EP5; right; left; reflexivity).
assert (OBQ : aobj bsegs m25 (usp + -992) 32)
by (split; [clear - LOV' LOS; lia|]; split; [clear - SPT; unfold APP_TOP, USTACK_TOP in *; lia| exact (af_acc_pois RT AF Σ6 m25 _ _ ART25 INQ)]).
sb_unpack X9 as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_v8 usp lo S OUT A f (sbmode_struct (sbd_mode s)) (usp + -992) (a_oq a) _ sI a ql1 (sj_oq j) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
FR24 ltac:(gslot) ltac:(gslot) ltac:(gslot) ltac:(gslot) HD FST PT ILPC IFST eq_refl OBS25 S8 SPOS BS1 SOFF eq_refl QLW1 Lql1 OBQ OQC JOQ OBOQ OQ8 OQP OQLO
ltac:(clear - OQSH; unfold SH_LO, SH_HI; lia) OQS ST25 ltac:(clear - LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia) LOS SPH SPA MI25 FRM25).
clear HD FST PT LE SEED CFG IDC PAD OBQ OBOQ.
destruct POST as (m26 & xt026 & xa226 & xa326 & xa426 & xa526 & xa626 & xa726 & F26 & jh5 & voq1 & -> & MU26 & WM26 & MI26 & ST26 & FR26 & HU5 & OQW1 & Lvoq1).
clear FR24 ST25 OQC.

assert (WH3 : wr_at bsegs m25 (usp + -1024) 96).
{ assert (J1 : rw_cells bsegs m25 (usp + -1024) ([CB 32 (firstn 32 jh3')] ++ f32 ql1)).
{ apply rw_cells_join; [exact RZ3a|]. replace (usp + -1024 + Z.of_nat (cells_size [CB 32 (firstn 32 jh3')])) with (usp + -992); [exact QLW1| cbn; lia]. }
assert (J2 : rw_cells bsegs m25 (usp + -1024) (([CB 32 (firstn 32 jh3')] ++ f32 ql1) ++ [CB 32 (firstn 32 (skipn 32 (skipn 32 jh3')))])).
{ apply rw_cells_join; [exact J1|]. replace (usp + -1024 + Z.of_nat (cells_size ([CB 32 (firstn 32 jh3')] ++ f32 ql1))) with (usp + -960); [exact RZ3b|].
rewrite cells_size_app, cells_size_f32, Lql1. cbn. lia. }
pose proof (proj2 J2) as W. rewrite !cells_size_app, cells_size_f32, Lql1 in W. exact W. }
assert (WH4 : wr_at bsegs m25 (usp + -1120) 96) by (exact (proj2 HU4)).
clear RZ3a QLW1 RZ3b HU4 Lql1 ql1 jh3' jh4.
set (LNO := [(sbd_g0_mem s, a_g0 a, 256); (sbd_g1_mem s, a_g1 a, 256); (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s); (sbd_interp_qlpc s, a_iq a, 32);
(sbd_pi_gain s, a_pg a, 16); (sbd_exc_rms s, a_er a, 16); (sbd_mem_sp s, a_msp a, 64)] ++ LBL).
assert (LNOA : forall bk, In bk LNO -> In bk LALL).
{ intros bk Hb. unfold LNO in Hb. unfold LALL. apply in_app_iff. apply in_app_iff in Hb. destruct Hb as [Hb | Hb]; [left| right; exact Hb].
clear - Hb. cbn [sb_blocks tl In] in Hb |- *. tauto. }
assert (LNOQ : forall bk x, In bk LNO -> blk_addr bk <= x < blk_addr bk + blk_size bk -> x < a_oq a \/ a_oq a + 32 <= x).
{ intros bk x Hb Hx. unfold LNO in Hb. apply in_app_iff in Hb. destruct Hb as [Hb | Hb].
- assert (NE : blk_addr bk <> a_oq a).
{ cbn [In] in Hb. unfold blk_addr. destruct Hb as [<- |[<- |[<- |[<- |[<- |[<- |[<- | []]]]]]]]; cbn [fst snd]; intros E; rewrite E in NDA; clear - NDA; tauto. }
pose proof (live_apart RT AF Σ6 m25 _ _ _ _ ART25 (LIVEA bk (LNOA bk ltac:(unfold LNO; apply in_app_iff; left; exact Hb))) INOQ NE) as AP. clear - AP Hx. lia.
- destruct (Z_lt_le_dec x (a_oq a)) as [H|H]; [left; exact H|]. destruct (Z_lt_le_dec x (a_oq a + 32)) as [H'|H']; [|right; exact H'].
exfalso. pose proof (APL (sbd_old_qlsp s, a_oq a, 32) x ltac:(cbn [sb_blocks tl In]; do 3 right; left; reflexivity)
ltac:(unfold blk_addr, blk_size; cbn [fst snd]; clear - H H'; lia)) as H2.
rewrite outside_blocks_ivs in H2. exact (H2 bk Hb Hx). }
assert (AGO : agree_blocks bsegs m25 m26 LNO).
{ apply (agree_blocks_of_munch bsegs _ m25 m26 LNO MU26 WM26). intros bk x Hb Hx. pose proof (BOUT bk x (LNOA bk Hb) Hx) as H1. pose proof (LNOQ bk x Hb Hx) as H2.
cbn [outside]. split; [clear - H2; lia| split; [clear - H1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact I]]. }
tra AGO G0C (sbd_g0_mem s, a_g0 a, 256) ltac:(clear - JG0; lia).
tra AGO G1C (sbd_g1_mem s, a_g1 a, 256) ltac:(clear - JG1; lia).
tra AGO EXC (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s) ltac:(cbn [sI set_sbd_submodeID sbd_subframeSize] in JEXC; clear - JEXC; lia).
tra AGO IQC (sbd_interp_qlpc s, a_iq a, 32) ltac:(clear - JIQ; lia).
tra AGO PGC (sbd_pi_gain s, a_pg a, 16) ltac:(clear - JPG; lia).
tra AGO ERC (sbd_exc_rms s, a_er a, 16) ltac:(clear - JER; lia).
tra AGO MSPC (sbd_mem_sp s, a_msp a, 64) ltac:(clear - JMSP; lia).
assert (AGL26 : agree_blocks bsegs m25 m26 LBL) by (apply (agree_blocks_sub bsegs _ _ _ _ AGO); intros bk Hb; unfold LNO; apply in_app_iff; right; exact Hb).
pk_blocks AGL26. clear AGL26 AGO.
assert (KEEP : forall P, fp_local IO_FP P -> P m25 -> P m26).
{ intros P L Pm. apply (fp_local_munch IO_FP P _ m25 m26 L IO_img MU26); [| exact Pm]. intros x Hx. unfold SEGTOP_A in Hx. cbn [outside].
split; [clear - Hx BOQ0 BOQ1; lia| split; [clear - Hx LOV LOS; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact I]]. }
pk_io ERR_rep OUT_rep KEEP. clear KEEP.
assert (ART26 : X14x.ART RT Σ6 m26).
{ apply (af_frame RT AF Σ6 m25 m26 lo ART25 LOWX); [| exact WM26]. intros a0 Ha. apply MU26. cbn [outside].
split; [| split; [| exact I]]; intros Hin; apply Ha.
- right; right; left. exists (a_oq a), 32. split; [exact INOQ| clear - Hin; lia].
- left. clear - Hin LOV SPT. unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK, USTACK_TOP in *. lia. }
assert (PF26 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m26).
{ apply (pres_fp_trans _ _ _ _ m m25 m26 PF). apply (pres_fp_of_munch _ _ _ _ _ m25 m26 MU26). intros x Hx Ho. cbn [outside] in Ho |- *.
destruct Ho as (_ & _ & _ & Ho). apply sb_outside_app_inv in Ho. destruct Ho as [Hb _]. rewrite outside_blocks_ivs in Hb.
split; [exact (Hb (sbd_old_qlsp s, a_oq a, 32) ltac:(rewrite ELBD; apply in_app_iff; left; cbn [sb_blocks In]; do 4 right; left; reflexivity))|].
split; [| exact I]. intros Hin. destruct (SPL x Hx) as [H1 | H1]; clear - H1 Hin LOW LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia. }
clear PF. rename PF26 into PF.
destruct (frame_live_apart RT AF Σ6 m25 fh kh _ _ ART25 INFHX INOQ) as (FOQ & _).
assert (POQ : a_oq a + 32 <= PD \/ PD + ND <= a_oq a)
by (apply (live_apart RT AF Σ6 m25 _ _ _ _ ART25 INOQ INPDX); exact (PDB (sbd_old_qlsp s, a_oq a, 32) ltac:(rewrite ELBD; apply in_app_iff; left; cbn [sb_blocks In]; do 4 right; left; reflexivity))).
trm MU26 WM26 SV ltac:(clear - BOQ0 BOQ1 LO736; lia).
trm MU26 WM26 FRB ltac:(clear - BOQ0 BOQ1 BF LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU26 WM26 FRS ltac:(clear - OQSH SHF1 SHF2 BF0 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU26 WM26 OC ltac:(rewrite LOWS; clear - BOQ0 BOQ1 FO1 FO2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU26 WM26 STB ltac:(clear - FOQ FS1 FS2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU26 WM26 BOBJ8 ltac:(clear - BOQ0 BOQ1 FA1 FA2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU26 WM26 BDAT8 ltac:(clear - POQ PD1 PD2 Lbs8 BD8 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU26 WM26 X9 ltac:(clear - OQS BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
apply (wr_at_transport bsegs m25 m26 _ _) in WH1; [| exact WM26]. apply (wr_at_transport bsegs m25 m26 _ _) in WH2; [| exact WM26].
apply (wr_at_transport bsegs m25 m26 _ _) in WH3; [| exact WM26]. apply (wr_at_transport bsegs m25 m26 _ _) in WH4; [| exact WM26].
assert (OF26 : offsh [(a_oq a, a_oq a + 32); (usp + -5216, usp + -160)])
by (cbn [offsh]; clear - LOS LOV OQSH; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK, SH_LO, SH_HI in *; lia).
assert (ACC26 : forall o n, acc bsegs m25 o n -> 0 <= o -> o + n <= 140737488355328 -> acc bsegs m26 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch bsegs _ m25 m26 o n (conj H0 (conj H1 H)) MU26 (shfree_of_offsh _ o n OF26 H0 H1)))). }
assert (ACA26 : acc bsegs m26 A 48) by (apply ACC26; [exact ACA25| clear - FA1 FP0; lia| clear - FA2 BF1 LO736 SPT; lia]).
assert (ACO26 : acc bsegs m26 OUT 8000) by (apply ACC26; [exact ACO25| clear - FO1 FP0; lia| clear - FO2 BF1 LO736 SPT; lia]).
assert (ACT26 : acc bsegs m26 STEREO 24) by (apply ACC26; [exact ACT25| clear - FS1 FP0; lia| clear - FS2 BF1 LO736 SPT; lia]).
assert (SSP26 : io_ssp m26).
{ apply (sbd_io_ssp_agree m25 m26 SSP25 (AF_DRV Σ6 m26 ART26)). intros a0 Ha. apply MU26. unfold X0r9.SSP_GUARD in Ha. cbn [outside].
clear - Ha BOQ0 BOQ1 LOV LOS. unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *. split; [lia| split; [lia| exact I]]. }
destruct (af_acc_live RT AF Σ6 m26 S 160 ART26 INLX) as (_ & ACS26).
assert (OBS26 : aobj bsegs m26 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO736 SPT; unfold APP_TOP; lia| exact ACS26]).
clear ACA25 ACO25 ACT25 ACC26 SSP25 ACS25 OBS25 ART25 MI25 OF26 MU26.

set (jV := SBJ (sj_last_ener j) (sj_seed j) (sj_pad1 j) (sj_pad2 j) (sj_g0 j) (sj_g1 j) (sj_exc j) voq1 (sj_iq j) (sj_msp j) (sj_pg j) (sj_er j)).
assert (JOKV : sb_junk_ok sI jV) by (exact (conj JP1 (conj JP2 (conj JG0 (conj JG1 (conj JEXC (conj Lvoq1 (conj JIQ (conj JMSP (conj JPG JER)))))))))).
assert (BUFS : sb_bufs bsegs m26 a jV) by (exact (conj G0C (conj G1C (conj EXC (conj OQW1 (conj IQC (conj MSPC (conj PGC ERC)))))))).

assert (EU1088 : bv_unsigned (Z_to_bv 64 (usp + -1216)) = usp + -1216) by (apply unsigned_lit; clear - SPT LOV LOS; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
assert (POA7 : pois_above (rt_pois RT Σ6) (alloca_rr (usp + -1184) 32)).
{ intros e He. rewrite EP6, EP5, EP4, EP3, EP2, EP1 in He. destruct He as [<- | [<- | [<- | [<- | He]]]].
1-4: unfold pz_lo, alloca_rr; cbn [fst]; clear - SPA; Z.div_mod_to_equations; lia.
rewrite EPX in He. pose proof (POA e He) as H1. unfold alloca_rr. clear - H1 SPA. Z.div_mod_to_equations. lia. }
assert (COK7 : call_ok RT Σ6 m26 (Z_to_bv 64 (usp + -1216)) lo).
{ unfold call_ok. rewrite EU1088. split; [exact ST26|]. split; [exact LOWX|]. split; [clear - LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia|].
split; [clear - SPT; unfold USTACK_TOP in *; lia| clear - SPA; Z.div_mod_to_equations; lia]. }
cps_rt (APO Σ6 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m26 (usp + -1184) 32 lo FDO MST eq_refl eq_refl
ltac:(clear - SPA; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(rewrite EU1088; lia)
ltac:(unfold alloca_rr, USTACK_TOP; clear - SPA SPT; Z.div_mod_to_equations; lia)
POA7 ltac:(rewrite EF6, EF5, EF4, EF3, EF2, EF1, EFX; discriminate) ART26 MI26 COK7).
intros c18 (Σ7 & Hc18 & EP7 & EL7 & EF7 & ES7 & EC7).
destruct (ASTA_unpack RT Σ7 (PMfd F0 fs0) _ c18 Hc18) as (ms18 & PO18 & Hc18'); clear Hc18; cbv beta in PO18.
destruct PO18 as (m27 & v27 & RS27 & (ART27 & MI27 & WM27 & ST27) & PRES27 & ACV27 & ACK27).
cps_ret RS27.
rewrite EU1088 in PRES27, ST27.
clear POA7 COK7.
pose proof (pres_fp_of_pres _ _ _ [] _ _ PRES27) as PF27.
tr1 PF27 WM27 SV ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF27 WM27 FR26 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF27 WM27 HU5 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF27 WM27 FRB ltac:(fun x Hx => apply (CLF0g _ _ _ x INF); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF27 WM27 FRS ltac:(fun x Hx => apply (CLSFg _ _ _ x INF); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF27 WM27 OC ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); rewrite LOWS in Hx; clear - Hx FO1 FO2; lia) ltac:(fun x Hx => exact I).
tr1 PF27 WM27 STB ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FS1 FS2; lia) ltac:(fun x Hx => exact I).
tr1 PF27 WM27 BOBJ8 ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FA1 FA2; lia) ltac:(fun x Hx => exact I).
tr1 PF27 WM27 BDAT8 ltac:(fun x Hx => apply (CLLg _ _ _ PD ND x INPDX); clear - Hx PD1 PD2 Lbs8; lia) ltac:(fun x Hx => exact I).
tr1 PF27 WM27 X9 ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => exact I).
apply (wr_at_transport bsegs m26 m27 _ _) in WH1; [| exact WM27]. apply (wr_at_transport bsegs m26 m27 _ _) in WH2; [| exact WM27].
apply (wr_at_transport bsegs m26 m27 _ _) in WH3; [| exact WM27]. apply (wr_at_transport bsegs m26 m27 _ _) in WH4; [| exact WM27].
pk_pres_all RT PRES27 WM27 LALL LIVEA ERR_rep OUT_rep IO_FP IO_img.
assert (ACA27 : acc bsegs m27 A 48) by (apply ACK27; [exact ACA26| clear - FA2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FA2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia]).
assert (ACO27 : acc bsegs m27 OUT 8000) by (apply ACK27; [exact ACO26| clear - FO2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FO2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia]).
assert (ACT27 : acc bsegs m27 STEREO 24) by (apply ACK27; [exact ACT26| clear - FS2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FS2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia]).
assert (ACS27 : acc bsegs m27 S 160) by (apply ACK27; [exact ACS26| clear - BS1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia]).
assert (OBS27 : aobj bsegs m27 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO736 SPT; unfold APP_TOP; lia| exact ACS27]).
assert (SSP27 : io_ssp m27).
{ apply (sbd_io_ssp_agree m26 m27 SSP26 (AF_DRV Σ7 m27 ART27)). intros a0 Ha. apply PRES27. right; left. exact (sbd_ssp_static _ Ha). }
assert (PF27' : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m27).
{ apply (pres_fp_trans _ _ _ _ m m26 m27 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ6) (rt_frames RT Σ6) (usp + -1216) [] m26 m27 PF27).
- intros e He. rewrite EL6, EL5, EL4, EL3, EL2, EL1, ELX. exact He.
- intros e He. rewrite EF6, EF5, EF4, EF3, EF2, EF1, EFX. right. exact He.
- clear; lia.
- intros x _ _. exact I. }
clear PF. rename PF27' into PF.
clear ACA26 ACO26 ACT26 ACS26 OBS26 SSP26 ART26 MI26 ST26 PF27 PRES27 ACK27 ACV27.
rewrite <- EL7 in LIVEA, LIVEL, LIVED, INLX, INPDX. rewrite <- EF7 in INF, INFHX. rewrite <- ES7 in LOWX.

assert (FSV : sbd_frame_size s = 160 \/ sbd_frame_size s = 320) by (rewrite IFS; destruct IMODE as [E|E]; rewrite E; cbn; [left| right]; reflexivity).
sb_unpack X9 as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_v9 usp S OUT A f (sbmode_struct (sbd_mode s)) (sbd_frame_size s) _ sI a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
FR26 ltac:(gslot) ltac:(gslot) ltac:(gslot) ltac:(gslot) ltac:(gslot) ltac:(gslot) ltac:(gslot) ltac:(gslot)
HD INS OBS27 S8 SPOS ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia) SOFF
ltac:(clear - IMODE; destruct IMODE as [E|E]; rewrite E; cbn [sbmode_struct]; unfold A_sb_wb_mode, A_sb_uwb_mode; lia)
ltac:(clear - IMODE; destruct IMODE as [E|E]; rewrite E; reflexivity)
ltac:(clear - IMODE; destruct IMODE as [E|E]; rewrite E; cbn [sbmode_struct]; unfold A_sb_wb_mode, A_sb_uwb_mode; lia)
ltac:(clear - LOS LOV; unfold SH_HI, RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia) SPH MI27).
clear HD FST PT LE SEED CFG IDC PAD.
destruct POST as (m28 & k28 & F28 & -> & MU28 & WM28 & MI28 & FR28).
clear FR26.
assert (ART28 : X14x.ART RT Σ7 m28).
{ apply (af_frame RT AF Σ7 m27 m28 lo ART27 LOWX); [| exact WM28]. intros a0 Ha. apply MU28. cbn [outside]. split; [| exact I].
intros Hin. apply Ha. left. clear - Hin LOV' SPT. unfold USTACK_TOP. lia. }
assert (PF28 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m28).
{ apply (pres_fp_trans _ _ _ _ m m27 m28 PF). apply (pres_fp_of_munch _ _ _ _ _ m27 m28 MU28). intros x Hx Ho. cbn [outside]. split; [| exact I].
intros Hin. destruct (SPL x Hx) as [H1 | H1]; clear - H1 Hin LOW LOV'; lia. }
clear PF. rename PF28 into PF.
pk_munch_all MU28 WM28 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LOV'; cbn [outside]; split; [lia| exact I])
ltac:(fun x Hx => clear - Hx LOV' LOS; cbn [outside]; split; [lia| exact I]).
trm MU28 WM28 SV ltac:(clear; lia).
trm MU28 WM28 HU5 ltac:(clear; lia).
trm MU28 WM28 FRB ltac:(clear - BF LOV'; lia).
trm MU28 WM28 FRS ltac:(clear - BF0 LOV'; lia).
trm MU28 WM28 OC ltac:(rewrite LOWS; clear - FO2 BF1 LOV'; lia).
trm MU28 WM28 STB ltac:(clear - FS2 BF1 LOV'; lia).
trm MU28 WM28 BOBJ8 ltac:(clear - FA2 BF1 LOV'; lia).
trm MU28 WM28 BDAT8 ltac:(clear - BD8 LOV'; lia).
trm MU28 WM28 X9 ltac:(clear - BS1 LOV'; lia).
apply (stk_transport_disjoint bsegs [(usp + -736, usp + -160)] m27 m28 lo (usp + -1216)) in ST27; [| exact MU28 | exact WM28 | cbn [disjoint_from]; clear; lia].
apply (wr_at_transport bsegs m27 m28 _ _) in WH1; [| exact WM28]. apply (wr_at_transport bsegs m27 m28 _ _) in WH2; [| exact WM28].
apply (wr_at_transport bsegs m27 m28 _ _) in WH3; [| exact WM28]. apply (wr_at_transport bsegs m27 m28 _ _) in WH4; [| exact WM28].
assert (OF28 : offsh [(usp + -736, usp + -160)]) by (cbn [offsh]; clear - LOS LOV'; unfold SH_LO, SH_HI in *; lia).
assert (ACC28 : forall o n, acc bsegs m27 o n -> 0 <= o -> o + n <= 140737488355328 -> acc bsegs m28 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch bsegs _ m27 m28 o n (conj H0 (conj H1 H)) MU28 (shfree_of_offsh _ o n OF28 H0 H1)))). }
assert (ACA28 : acc bsegs m28 A 48) by (apply ACC28; [exact ACA27| clear - FA1 FP0; lia| clear - FA2 BF1 LO736 SPT; lia]).
assert (ACO28 : acc bsegs m28 OUT 8000) by (apply ACC28; [exact ACO27| clear - FO1 FP0; lia| clear - FO2 BF1 LO736 SPT; lia]).
assert (ACT28 : acc bsegs m28 STEREO 24) by (apply ACC28; [exact ACT27| clear - FS1 FP0; lia| clear - FS2 BF1 LO736 SPT; lia]).
assert (SSP28 : io_ssp m28).
{ apply (sbd_io_ssp_agree m27 m28 SSP27 (AF_DRV Σ7 m28 ART28)). intros a0 Ha. apply MU28. unfold X0r9.SSP_GUARD in Ha. cbn [outside].
clear - Ha LOV' LOS. split; [lia| exact I]. }
clear ACA27 ACO27 ACT27 ACC28 SSP27 ACS27 OBS27 ART27 MI27 OF28 MU28.

clear Hc Hc0 Hc1 Hc2 Hc3 EXR19 OQW1.

destruct (wr_at_rw_CB m28 (usp + -832) 96 WH1 ltac:(lia)) as (jk1 & HH1). clear WH1. change (Z.to_nat 96) with 96%nat in HH1.
apply (rw_cells_split_CB bsegs _ _ [] 96 _ [] [32; 16; 48]%nat) in HH1; [| reflexivity]. cbn [mk_CB_cells app] in HH1.
apply rw_cells_uncons in HH1. destruct HH1 as (RZ1a & HH1). apply rw_cells_uncons in HH1. destruct HH1 as (BY1 & RZ1b).
cbn [csize] in BY1, RZ1b.
replace (usp + -832 + Z.of_nat 32) with (usp + -800) in BY1, RZ1b by lia.
replace (usp + -800 + Z.of_nat 16) with (usp + -784) in RZ1b by lia.
destruct (rw_cells_CB_f32 bsegs m28 (usp + -800) 4 _ BY1) as (lpi & Llpi & LPI). clear BY1.
destruct (wr_at_rw_CB m28 (usp + -928) 96 WH2 ltac:(lia)) as (jk2 & HH2). clear WH2. change (Z.to_nat 96) with 96%nat in HH2.
apply (rw_cells_split_CB bsegs _ _ [] 96 _ [] [32; 16; 48]%nat) in HH2; [| reflexivity]. cbn [mk_CB_cells app] in HH2.
apply rw_cells_uncons in HH2. destruct HH2 as (RZ2a & HH2). apply rw_cells_uncons in HH2. destruct HH2 as (BY2 & RZ2b).
cbn [csize] in BY2, RZ2b.
replace (usp + -928 + Z.of_nat 32) with (usp + -896) in BY2, RZ2b by lia.
replace (usp + -896 + Z.of_nat 16) with (usp + -880) in RZ2b by lia.
destruct (rw_cells_CB_f32 bsegs m28 (usp + -896) 4 _ BY2) as (ler & Ller & LER). clear BY2.
destruct (wr_at_rw_CB m28 (usp + -1024) 96 WH3 ltac:(lia)) as (jk3 & HH3). clear WH3. change (Z.to_nat 96) with 96%nat in HH3.
apply (rw_cells_split_CB bsegs _ _ [] 96 _ [] [32; 32; 32]%nat) in HH3; [| reflexivity]. cbn [mk_CB_cells app] in HH3.
apply rw_cells_uncons in HH3. destruct HH3 as (RZ3a & HH3). apply rw_cells_uncons in HH3. destruct HH3 as (BY3 & RZ3b).
cbn [csize] in BY3, RZ3b.
replace (usp + -1024 + Z.of_nat 32) with (usp + -992) in BY3, RZ3b by lia.
replace (usp + -992 + Z.of_nat 32) with (usp + -960) in RZ3b by lia.
destruct (rw_cells_CB_f32 bsegs m28 (usp + -992) 8 _ BY3) as (lq & Llq & LQ). clear BY3.
destruct (wr_at_rw_CB m28 (usp + -1120) 96 WH4 ltac:(lia)) as (jk4 & HH4). clear WH4. change (Z.to_nat 96) with 96%nat in HH4.
apply (rw_cells_split_CB bsegs _ _ [] 96 _ [] [32; 32; 32]%nat) in HH4; [| reflexivity]. cbn [mk_CB_cells app] in HH4.
apply rw_cells_uncons in HH4. destruct HH4 as (RZ4a & HH4). apply rw_cells_uncons in HH4. destruct HH4 as (BY4 & RZ4b).
cbn [csize] in BY4, RZ4b.
replace (usp + -1120 + Z.of_nat 32) with (usp + -1088) in BY4, RZ4b by lia.
replace (usp + -1088 + Z.of_nat 32) with (usp + -1056) in RZ4b by lia.
destruct (rw_cells_CB_f32 bsegs m28 (usp + -1088) 8 _ BY4) as (liq & Lliq & LIQ). clear BY4.
apply (rw_cells_split_CB bsegs _ _ [] 96 _ [] [32; 32; 32]%nat) in HU5; [| reflexivity]. cbn [mk_CB_cells app] in HU5.
apply rw_cells_uncons in HU5. destruct HU5 as (RZ5a & HU5). apply rw_cells_uncons in HU5. destruct HU5 as (BY5 & RZ5b).
cbn [csize] in BY5, RZ5b.
replace (usp + -1216 + Z.of_nat 32) with (usp + -1184) in BY5, RZ5b by lia.
replace (usp + -1184 + Z.of_nat 32) with (usp + -1152) in RZ5b by lia.
destruct (rw_cells_CB_f32 bsegs m28 (usp + -1184) 8 _ BY5) as (lak & Llak & LAK). clear BY5.

set (vLA := SBV (g 1%nat) (g 18%nat) (g 35%nat) (g 36%nat) (g 49%nat) (g 57%nat) (Z_to_bv 64 0) (g 64%nat) (g 65%nat) (g 66%nat) (Z_to_bv 64 (usp + -1216))
(g 69%nat) (g 70%nat) (g 71%nat)).
assert (SLA : rw_cells bsegs m28 (usp + -736) (sb_slots usp S OUT A f sf (sbmode_struct (sbd_mode sI)) (sbd_frame_size sI) vLA)).
{ unfold sb_fr in FR28. cbn [map seq] in FR28. cbn [fupds Nat.eqb sb_v9_upd] in FR28. rewrite G0, G10, G13, G26, G27, G38, G45, G51, G19, G67, G40, G61, G62 in FR28.
unfold sb_slots, sha, vLA. cbn [v_8 v_144 v_280 v_288 v_392 v_456 v_480 v_512 v_520 v_528 v_544 v_552 v_560 v_568 sI set_sbd_submodeID sbd_mode sbd_frame_size].
exact FR28. }

set (X := SBI usp lo gp S OUT A D sI a (sb_buf_size b1) f sf fh kh PD ND (rt_live RT Σ) (rt_frames RT Σ) (rt_sp0 RT Σ) (rt_credit RT Σ7) (rt_pois RT Σ)).
assert (IH : sb_ihyps X).
{ constructor; cbn [x_usp x_lo x_gp x_S x_OUT x_A x_D x_s x_a x_bsz x_f x_sf x_fh x_kh x_PD x_ND x_live x_frames x_sp0 x_cr x_pois X].
- exact SPA.
- exact SPT.
- exact LOW.
- exact LOV.
- exact SPOS.
- exact S8.
- exact INV1.
- exact ISV.
- intros bk Hb. apply LIVE. rewrite ELBD. apply in_app_iff. left. exact Hb.
- pose proof NDUP as ND'. rewrite ELBD, map_app in ND'. exact (List.NoDup_app_remove_r _ _ ND').
- exact INFH.
- exact (conj FA1 (conj FA2 AAL)).
- exact (conj FO1 (conj FO2 OAL)).
- exact HAO.
- exact (conj INPD (conj PD1 PD2)).
- intros bk Hb. apply PDB. rewrite ELBD. apply in_app_iff. left. exact Hb.
- exact POA.
- reflexivity.
- exact AL. }
assert (BREP28 : bits_rep bsegs m28 A D (lsp_bits LspUnquantHigh (sbw_bits b1))).
{ split; [exists rj8; split; [exact Lrj8| unfold bits_cells; exact BOBJ8]|].
split; [exists bs8; split; [apply (proj2 (u8arr_rw_CB m28 D bs8)); exact BDAT8| exact Hbs8]| exact BSIDE8]. }
assert (HLA : at_LA RT X (PMfd F0 fs0) m28 0 (lsp_bits LspUnquantHigh (sbw_bits b1)) c19).
{ exists Σ7, F28, fc25, m28, k28, vLA.
split; [exact Hc4|]. split; [exact FRM25|].
split.
{ unfold sb_sigma. cbn [x_live x_frames x_sp0 x_cr x_pois x_usp x_f X].
split; [rewrite EL7, EL6, EL5, EL4, EL3, EL2, EL1, ELX; reflexivity|].
split; [rewrite EF7, EF6, EF5, EF4, EF3, EF2, EF1, EFX; reflexivity|].
split; [rewrite ES7, ES6, ES5, ES4, ES3, ES2, ES1, ESX; reflexivity|].
split; [reflexivity|].
rewrite EP7, EP6, EP5, EP4, EP3, EP2, EP1, EPX. reflexivity. }
split; [| reflexivity].
exists (sj_last_ener j), (sj_seed j), (sj_pad1 j), (sj_pad2 j), lpi, ler, lq, liq, lak, (sj_exc j), voq1, (sj_iq j), (sj_msp j), (sj_pg j), (sj_er j), ows.
destruct BUFS as (_ & _ & EXC' & OQC' & IQC' & MSPC' & PGC' & ERC').
pose proof (proj1 (sb_pieces_iff m28 S sI a OUT j) X9) as PCS.
refine (conj ART28 (conj MI28 (conj ST27 (conj _ (conj (wmono_refl bsegs m28) (conj SLA (conj LPI (conj Llpi (conj LER (conj Ller (conj LQ (conj Llq
(conj LIQ (conj Lliq (conj LAK (conj Llak (conj PCS (conj JP1 (conj JP2 (conj EXC' (conj JEXC (conj OQC' (conj Lvoq1 (conj IQC' (conj JIQ
(conj MSPC' (conj JMSP (conj PGC' (conj JPG (conj ERC' (conj JER (conj OC (conj LOWS (conj BREP28 (conj BOK8 (conj BSZ8 (conj ACA28 ACO28))))))))))))))))))))))))))))))))))))).
intros a0 _ _. reflexivity. }

refine (cps_realizes bsegs _ _ T c19 (LOOP X (PMfd F0 fs0) m28 0 _ sm FDO MST IH ltac:(lia) ESM) HLA _).
intros c20 [(_ & HLA1) | (E & _)]; [| exfalso; clear - E; lia].
refine (cps_realizes bsegs _ _ T c20 (LOOP X (PMfd F0 fs0) m28 (0 + 1) _ sm FDO MST IH ltac:(lia) ESM) HLA1 _).
intros c21 [(_ & HLA2) | (E & _)]; [| exfalso; clear - E; lia].
refine (cps_realizes bsegs _ _ T c21 (LOOP X (PMfd F0 fs0) m28 (0 + 1 + 1) _ sm FDO MST IH ltac:(lia) ESM) HLA2 _).
intros c22 [(_ & HLA3) | (E & _)]; [| exfalso; clear - E; lia].
refine (cps_realizes bsegs _ _ T c22 (LOOP X (PMfd F0 fs0) m28 (0 + 1 + 1 + 1) _ sm FDO MST IH ltac:(lia) ESM) HLA3 _).
intros c23 [(E & _) | (_ & HTA)]; [exfalso; clear - E; lia|].
clear HLA HLA1 HLA2 HLA3 Hc4.

destruct HTA as (Σ8 & F29 & fc29 & m29 & k29 & v29 & Hc29 & FRM29 & SIG29 & LM29 & V416).
destruct SIG29 as (EL8 & EF8 & ES8 & EC8 & EP8). cbn [x_live x_frames x_sp0 x_cr x_pois x_usp x_f X] in EL8, EF8, ES8, EC8, EP8.
destruct LM29 as (le29 & seed29 & pad129 & pad229 & lpi29 & ler29 & lq29 & liq29 & lak29 & vexc29 & voq29 & viq29 & vmsp29 & vpg29 & ver29 & ows29 &
ART29 & MI29 & ST29 & PF29 & WM29 & SL29 & LPI29 & Llpi29 & LER29 & Ller29 & LQ29 & Llq29 & LIQ29 & Lliq29 & LAK29 & Llak29 &
PCS29 & Lp129 & Lp229 & EXC29 & Lexc29 & OQ29 & Loq29 & IQ29 & Liq29 & MSP29 & Lmsp29 & PG29 & Lpg29 & ER29 & Ler29 &
OC29 & LOWS29 & BREP29 & BOK29 & BSZ29 & ACA29 & ACO29).
cbn [x_live x_frames x_f x_usp x_lo x_S x_OUT x_A x_D x_s x_a x_bsz x_gp x_sf X] in *.
unfold sb_WL in PF29. cbn [x_usp x_S x_OUT x_A x_a x_s X] in PF29.
clear G0C G1C EXC IQC MSPC PGC ERC.
destruct BUFS as (G0C & G1C & _ & _ & _ & _ & _ & _).
clear LPI LER LQ LIQ LAK Llpi Ller Llq Lliq Llak lpi ler lq liq lak SLA X9 OC LOWS BOBJ8 BDAT8.

assert (EL87 : rt_live RT Σ8 = rt_live RT Σ7) by (rewrite EL8, EL7, EL6, EL5, EL4, EL3, EL2, EL1, ELX; reflexivity).
assert (EF87 : rt_frames RT Σ8 = rt_frames RT Σ7) by (rewrite EF8, EF7, EF6, EF5, EF4, EF3, EF2, EF1, EFX; reflexivity).
assert (ES87 : rt_sp0 RT Σ8 = rt_sp0 RT Σ7) by (rewrite ES8, ES7, ES6, ES5, ES4, ES3, ES2, ES1, ESX; reflexivity).

assert (LAP : forall bk1 bk2, In bk1 LALL -> In bk2 LALL -> blk_addr bk1 <> blk_addr bk2 ->
blk_addr bk1 + blk_size bk1 <= blk_addr bk2 \/ blk_addr bk2 + blk_size bk2 <= blk_addr bk1)
by (intros bk1 bk2 H1 H2 NE; exact (live_apart RT AF Σ7 m28 _ _ _ _ ART28 (LIVEA bk1 H1) (LIVEA bk2 H2) NE)).

assert (OWL : forall x, (forall bk, In bk LALL -> ~ (blk_addr bk <= x < blk_addr bk + blk_size bk)) ->
(x < S + 132 \/ S + 136 <= x) -> (x < OUT \/ OUT + 8000 <= x) -> (x < A \/ A + 48 <= x) ->
(x < usp + -736 \/ usp + -160 <= x) -> (x < usp + -1088 \/ usp + -1056 <= x) -> (x < usp + -1184 \/ usp + -1152 <= x) ->
outside [(usp + -736, usp + -160); (usp + -1088, usp + -1056); (usp + -1184, usp + -1152); (S + 132, S + 136);
(a_exc a, a_exc a + 4 * sbd_subframeSize sI); (a_iq a, a_iq a + 32); (a_msp a, a_msp a + 64); (a_pg a, a_pg a + 16);
(a_er a, a_er a + 16); (OUT, OUT + 8000); (A, A + BITS_SIZEOF)] x).
{ intros x HB H1 H2 H3 H4 H5 H6.
pose proof (HB (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; do 2 right; left; reflexivity)) as B1.
pose proof (HB (sbd_interp_qlpc s, a_iq a, 32) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; do 4 right; left; reflexivity)) as B2.
pose proof (HB (sbd_pi_gain s, a_pg a, 16) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; do 5 right; left; reflexivity)) as B3.
pose proof (HB (sbd_exc_rms s, a_er a, 16) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; do 6 right; left; reflexivity)) as B4.
pose proof (HB (sbd_mem_sp s, a_msp a, 64) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; do 7 right; left; reflexivity)) as B5.
unfold blk_addr, blk_size in B1, B2, B3, B4, B5. cbn [fst snd] in B1, B2, B3, B4, B5. cbn [sI set_sbd_submodeID sbd_subframeSize].
cbn [outside]. unfold BITS_SIZEOF. clear - H1 H2 H3 H4 H5 H6 B1 B2 B3 B4 B5.
repeat split; lia. }

assert (NLB : forall x, (lo <= x \/ S <= x < S + 160 \/ fh <= x < fh + fs_size kh \/ PD <= x < PD + ND \/ f <= x < f + 64 \/ sf <= x < sf + 8) ->
forall bk, In bk LALL -> ~ (blk_addr bk <= x < blk_addr bk + blk_size bk)).
{ intros x Hx bk Hb Hin. pose proof (BOUT bk x Hb Hin) as H1. clear - Hx H1. lia. }
assert (INF8 : In (f, 0%nat) ((f, 0%nat) :: rt_frames RT Σ)) by (left; reflexivity).
assert (INFH8 : In (fh, kh) ((f, 0%nat) :: rt_frames RT Σ)) by (right; exact INFH).
tr1 PF29 WM29 SV ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => apply OWL; [apply NLB; left; clear - Hx LO736; lia| clear - Hx BS1 LO736; lia| clear - Hx FO2 BF1 LO736; lia| clear - Hx ALO LO736; lia| clear - Hx; lia..]).
tr1 PF29 WM29 FRB ltac:(fun x Hx => apply (CLF0g _ _ _ x INF8); clear - Hx; lia)
ltac:(fun x Hx => apply OWL; [apply NLB; right; right; right; right; left; clear - Hx; lia| clear - Hx SFA; unfold hid in *; lia
| clear - Hx FFA FO1 FO2; unfold hid in *; lia| clear - Hx FFA FA1 FA2; unfold hid in *; lia| clear - Hx BF LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia..]).
tr1 PF29 WM29 FRS ltac:(fun x Hx => apply (CLSFg _ _ _ x INF8); clear - Hx; lia)
ltac:(fun x Hx => apply OWL; [apply NLB; right; right; right; right; right; clear - Hx; lia| clear - Hx SFS SHF; unfold hid in *; subst sf; lia
| clear - Hx FPHI' SHF1 SHF2 FO1 FO2; unfold hid in *; lia| clear - Hx FPHI' SHF1 SHF2 FA1 FA2; unfold hid in *; lia
| clear - Hx BF0 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia..]).
tr1 PF29 WM29 STB ltac:(fun x Hx => apply (CLFg _ _ _ x INFH8); clear - Hx FS1 FS2; lia)
ltac:(fun x Hx => apply OWL; [apply NLB; right; right; left; clear - Hx FS1 FS2; lia| clear - Hx SFH FS1 FS2; unfold hid in *; lia
| clear - Hx HOS'; unfold hid in *; lia| clear - Hx HAS'; unfold hid in *; lia| clear - Hx FS2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia..]).
tr1 PF29 WM29 RZ1a ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => apply OWL; [apply NLB; left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx FO2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx ALO LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx; lia..]).
tr1 PF29 WM29 RZ1b ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => apply OWL; [apply NLB; left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx FO2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx ALO LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx; lia..]).
tr1 PF29 WM29 RZ2a ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => apply OWL; [apply NLB; left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx FO2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx ALO LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx; lia..]).
tr1 PF29 WM29 RZ2b ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => apply OWL; [apply NLB; left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx FO2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx ALO LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx; lia..]).
tr1 PF29 WM29 RZ3a ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => apply OWL; [apply NLB; left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx FO2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx ALO LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx; lia..]).
tr1 PF29 WM29 RZ3b ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => apply OWL; [apply NLB; left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx FO2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx ALO LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx; lia..]).
tr1 PF29 WM29 RZ4a ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => apply OWL; [apply NLB; left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx FO2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx ALO LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx; lia..]).
tr1 PF29 WM29 RZ4b ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => apply OWL; [apply NLB; left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx FO2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx ALO LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx; lia..]).
tr1 PF29 WM29 RZ5a ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => apply OWL; [apply NLB; left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx FO2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx ALO LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx; lia..]).
tr1 PF29 WM29 RZ5b ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => apply OWL; [apply NLB; left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx FO2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx ALO LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx; lia..]).

assert (NDA0 : List.NoDup [S; a_g0 a; a_g1 a; a_exc a; a_oq a; a_iq a; a_pg a; a_er a; a_msp a])
by (pose proof NDUP as ND'; rewrite ELBD, map_app in ND'; exact (List.NoDup_app_remove_r _ _ ND')).
assert (NDN : forall i0 j0 : nat, (i0 < 9)%nat -> (j0 < 9)%nat -> i0 <> j0 ->
nth i0 [S; a_g0 a; a_g1 a; a_exc a; a_oq a; a_iq a; a_pg a; a_er a; a_msp a] 0 <> nth j0 [S; a_g0 a; a_g1 a; a_exc a; a_oq a; a_iq a; a_pg a; a_er a; a_msp a] 0)
by (intros i0 j0 Hi Hj Hne E; apply Hne; exact (proj1 (NoDup_nth _ 0) NDA0 i0 j0 Hi Hj E)).

assert (WOUT : forall bk x, In bk ([(sbd_g0_mem s, a_g0 a, 256); (sbd_g1_mem s, a_g1 a, 256)] ++ LBL) ->
blk_addr bk <= x < blk_addr bk + blk_size bk ->
outside [(usp + -736, usp + -160); (usp + -1088, usp + -1056); (usp + -1184, usp + -1152); (S + 132, S + 136);
(a_exc a, a_exc a + 4 * sbd_subframeSize sI); (a_iq a, a_iq a + 32); (a_msp a, a_msp a + 64); (a_pg a, a_pg a + 16);
(a_er a, a_er a + 16); (OUT, OUT + 8000); (A, A + BITS_SIZEOF)] x).
{ intros bk x Hb Hx.
assert (HbA : In bk LALL).
{ unfold LALL. apply in_app_iff. apply in_app_iff in Hb. destruct Hb as [Hb | Hb]; [left| right; exact Hb].
clear - Hb. cbn [sb_blocks tl In] in Hb |- *. tauto. }
pose proof (BOUT bk x HbA Hx) as H1.

assert (WB : forall wb, In wb [(sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s); (sbd_interp_qlpc s, a_iq a, 32); (sbd_pi_gain s, a_pg a, 16);
(sbd_exc_rms s, a_er a, 16); (sbd_mem_sp s, a_msp a, 64)] -> ~ (blk_addr wb <= x < blk_addr wb + blk_size wb)).
{ intros wb Hw Hin.
assert (HwA : In wb (tl (sb_blocks s S a))) by (clear - Hw; cbn [sb_blocks tl In] in Hw |- *; tauto).
apply in_app_iff in Hb. destruct Hb as [Hb | Hb].
- assert (NE : blk_addr bk <> blk_addr wb).
{ clear - Hb Hw NDN. cbn [In] in Hb, Hw. unfold blk_addr.
destruct Hb as [<- |[<- | []]]; destruct Hw as [<- |[<- |[<- |[<- |[<- | []]]]]]; cbn [fst snd];
solve [ exact (NDN 1%nat 3%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) | exact (NDN 1%nat 5%nat ltac:(lia) ltac:(lia) ltac:(discriminate))
| exact (NDN 1%nat 6%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) | exact (NDN 1%nat 7%nat ltac:(lia) ltac:(lia) ltac:(discriminate))
| exact (NDN 1%nat 8%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) | exact (NDN 2%nat 3%nat ltac:(lia) ltac:(lia) ltac:(discriminate))
| exact (NDN 2%nat 5%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) | exact (NDN 2%nat 6%nat ltac:(lia) ltac:(lia) ltac:(discriminate))
| exact (NDN 2%nat 7%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) | exact (NDN 2%nat 8%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) ]. }
pose proof (LAP bk wb HbA ltac:(unfold LALL; apply in_app_iff; left; exact HwA) NE) as AP. clear - AP Hx Hin. lia.
- pose proof (APL wb x HwA Hin) as H2. rewrite outside_blocks_ivs in H2. exact (H2 bk Hb Hx). }
pose proof (WB (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s) ltac:(cbn [In]; left; reflexivity)) as W1.
pose proof (WB (sbd_interp_qlpc s, a_iq a, 32) ltac:(cbn [In]; right; left; reflexivity)) as W2.
pose proof (WB (sbd_pi_gain s, a_pg a, 16) ltac:(cbn [In]; do 2 right; left; reflexivity)) as W3.
pose proof (WB (sbd_exc_rms s, a_er a, 16) ltac:(cbn [In]; do 3 right; left; reflexivity)) as W4.
pose proof (WB (sbd_mem_sp s, a_msp a, 64) ltac:(cbn [In]; do 4 right; left; reflexivity)) as W5.
unfold blk_addr, blk_size in W1, W2, W3, W4, W5. cbn [fst snd] in W1, W2, W3, W4, W5. cbn [sI set_sbd_submodeID sbd_subframeSize].
cbn [outside]. unfold BITS_SIZEOF. clear - H1 W1 W2 W3 W4 W5 LOV FO1 FO2 FA1 FA2.
unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in LOV. repeat split; lia. }
assert (LIVEg : forall bk, In bk ([(sbd_g0_mem s, a_g0 a, 256); (sbd_g1_mem s, a_g1 a, 256)] ++ LBL) ->
In (blk_addr bk, blk_size bk) (rt_live RT Σ)).
{ intros bk Hb. apply LIVE. rewrite ELBD. apply in_app_iff. apply in_app_iff in Hb. destruct Hb as [Hb | Hb]; [left| right; exact Hb].
clear - Hb. cbn [sb_blocks In] in Hb |- *. tauto. }
assert (AG29 : agree_blocks bsegs m28 m29 ([(sbd_g0_mem s, a_g0 a, 256); (sbd_g1_mem s, a_g1 a, 256)] ++ LBL))
by (apply (agree_blocks_of_pres_fp RT Σ _ _ _ m28 m29 _ PF29 WM29 LIVEg); exact WOUT).
change (sj_g0 jV) with (sj_g0 j) in G0C. change (sj_g1 jV) with (sj_g1 j) in G1C.
tra AG29 G0C (sbd_g0_mem s, a_g0 a, 256) ltac:(clear - JG0; lia).
tra AG29 G1C (sbd_g1_mem s, a_g1 a, 256) ltac:(clear - JG1; lia).
assert (AGL29 : agree_blocks bsegs m28 m29 LBL) by (apply (agree_blocks_sub bsegs _ _ _ _ AG29); intros bk Hb; apply in_app_iff; right; exact Hb).
pk_blocks AGL29. clear AGL29 AG29.
assert (OIMG : forall y, 65536 <= y < 6664192 ->
outside [(usp + -736, usp + -160); (usp + -1088, usp + -1056); (usp + -1184, usp + -1152); (S + 132, S + 136);
(a_exc a, a_exc a + 4 * sbd_subframeSize sI); (a_iq a, a_iq a + 32); (a_msp a, a_msp a + 64); (a_pg a, a_pg a + 16);
(a_er a, a_er a + 16); (OUT, OUT + 8000); (A, A + BITS_SIZEOF)] y).
{ intros y Hy. apply OWL; [intros bk Hb Hin; pose proof (BOUT bk y Hb Hin) as H1; clear - H1 Hy; lia| clear - Hy SIMG; lia| clear - Hy FO1 FPIMG; lia
| clear - Hy AIMG; unfold IMG_TOP_B in *; lia| clear - Hy LOV LOS; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia..]. }
pk_io_fp PF29 ERR_rep OUT_rep IO_FP IO_img ltac:(fun y Hy => apply OIMG; exact Hy).
assert (SSP29 : io_ssp m29).
{ apply (sbd_io_ssp_agree m28 m29 SSP28 (AF_DRV Σ8 m29 ART29)). intros a0 Ha. apply PF29; [right; left; exact (sbd_ssp_static _ Ha)|].
unfold X0r9.SSP_GUARD in Ha. apply OIMG. clear - Ha. lia. }

assert (PF29' : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m29).
{ apply (pres_fp_trans _ _ _ _ m m28 m29 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ) ((f, 0%nat) :: rt_frames RT Σ) (usp + -1216) _ m28 m29 PF29).
- intros e He. exact He.
- intros e He. right. exact He.
- clear; lia.
- intros x Hx Ho. cbn [outside] in Ho. destruct Ho as (HA & HO & _ & Ho). apply sb_outside_app_inv in Ho. destruct Ho as [Hb _].
rewrite ELBD in Hb. pose proof (outside_blocks_app_l _ _ x Hb) as Hb1. rewrite outside_blocks_ivs in Hb1.
pose proof (Hb1 (sbd_blk s, S, SBSTATE_SIZEOF) ltac:(cbn [sb_blocks In]; left; reflexivity)) as N0.
pose proof (Hb1 (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s) ltac:(cbn [sb_blocks In]; do 3 right; left; reflexivity)) as N1.
pose proof (Hb1 (sbd_interp_qlpc s, a_iq a, 32) ltac:(cbn [sb_blocks In]; do 5 right; left; reflexivity)) as N2.
pose proof (Hb1 (sbd_pi_gain s, a_pg a, 16) ltac:(cbn [sb_blocks In]; do 6 right; left; reflexivity)) as N3.
pose proof (Hb1 (sbd_exc_rms s, a_er a, 16) ltac:(cbn [sb_blocks In]; do 7 right; left; reflexivity)) as N4.
pose proof (Hb1 (sbd_mem_sp s, a_msp a, 64) ltac:(cbn [sb_blocks In]; do 8 right; left; reflexivity)) as N5.
unfold blk_addr, blk_size, SBSTATE_SIZEOF in N0, N1, N2, N3, N4, N5. cbn [fst snd] in N0, N1, N2, N3, N4, N5. cbn [sI set_sbd_submodeID sbd_subframeSize].
pose proof (SPL x Hx) as HSP.
cbn [outside]. unfold BITS_SIZEOF. clear - HA HO N0 N1 N2 N3 N4 N5 HSP LOW LOV.
unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in LOV. repeat split; lia. }
clear PF. rename PF29' into PF.

destruct PCS29 as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
destruct BREP29 as ((rj29 & Lrj29 & BOBJ29) & (bs29 & BDAT29 & Hbs29) & BSIDE29). apply u8arr_rw_CB in BDAT29. unfold bits_cells in BOBJ29.
assert (BSZ29' : sb_buf_size (sbsub_bits sm (sbsub_bits sm (sbsub_bits sm (sbsub_bits sm (lsp_bits LspUnquantHigh (sbw_bits b1)))))) = sb_buf_size b1) by exact BSZ29.
assert (Lbs29 : Z.of_nat (length bs29) = sb_buf_size b1)
by (pose proof BOK29 as OK'; unfold bits_ok in OK'; rewrite Hbs29, zlength_map_unsigned, BSZ29' in OK'; clear - OK'; lia).
assert (BD29 : D + Z.of_nat (length bs29) <= lo) by (rewrite Lbs29; exact DLO).
destruct (af_acc_live RT AF Σ8 m29 S 160 ART29 ltac:(rewrite EL8; exact INL)) as (_ & ACS29).
assert (OBS29 : aobj bsegs m29 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO736 SPT; unfold APP_TOP; lia| exact ACS29]).
cps_seg (sbd_t1 usp lo S OUT A f sf (sbmode_struct (sbd_mode sI)) (sbd_frame_size sI) v29 sI a le29 k29 _ _ _ _ _
SL29 HD PT LE eq_refl ltac:(cbn [sI set_sbd_submodeID sbd_full_frame_size sbd_frame_size]; exact IFFS) ltac:(cbn [sI set_sbd_submodeID sbd_frame_size]; exact FSV)
OBS29 S8 SPOS BS1 SOFF ltac:(unfold IMG_TOP_B; clear - SIMG; lia) ltac:(clear - FO1 FP0; lia) ltac:(clear - FO2 BF1 LO736 SPT; lia)
ST29 ltac:(clear - LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia) LOS ltac:(clear - SPH; lia) MI29 FRM29).
clear LE OBS29 ACS29.
destruct POST as (m30 & xt030 & xt130 & xt230 & xt330 & xt430 & xt530 & xt630 & xs330 & xs430 & xs530 & xs730 & xs830 & xs930 & xs1030 & xs1130 & F30 & fc30 & le30 & ja30 &
-> & MU30 & WM30 & MI30 & ST30 & FRM30 & LE30 & STK30).
clear ST29.

rewrite <- EL87 in LIVEA, LIVEL, LIVED, INLX, INPDX. rewrite <- EF87 in INF, INFHX. rewrite <- ES87 in LOWX.

set (BL := [(S, 160); (a_g0 a, 256); (a_g1 a, 256); (a_exc a, 4 * sbd_subframeSize s); (a_oq a, 32); (a_iq a, 32); (a_pg a, 16); (a_er a, 16); (a_msp a, 64)]).
assert (LIVBL : forall e, In e BL -> In e (rt_live RT Σ8)).
{ intros e He. unfold BL in He. cbn [In] in He.
destruct He as [<- |[<- |[<- |[<- |[<- |[<- |[<- |[<- |[<- | []]]]]]]]]].
1: exact INLX.
1: exact (LIVEA (sbd_g0_mem s, a_g0 a, 256) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; left; reflexivity)).
1: exact (LIVEA (sbd_g1_mem s, a_g1 a, 256) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; right; left; reflexivity)).
1: exact (LIVEA (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; do 2 right; left; reflexivity)).
1: exact (LIVEA (sbd_old_qlsp s, a_oq a, 32) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; do 3 right; left; reflexivity)).
1: exact (LIVEA (sbd_interp_qlpc s, a_iq a, 32) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; do 4 right; left; reflexivity)).
1: exact (LIVEA (sbd_pi_gain s, a_pg a, 16) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; do 5 right; left; reflexivity)).
1: exact (LIVEA (sbd_exc_rms s, a_er a, 16) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; do 6 right; left; reflexivity)).
1: exact (LIVEA (sbd_mem_sp s, a_msp a, 64) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; do 7 right; left; reflexivity)). }
assert (SBAP : forall i0 j0 : nat, (i0 < 9)%nat -> (j0 < 9)%nat -> i0 <> j0 ->
fst (nth i0 BL (0, 0)) + snd (nth i0 BL (0, 0)) <= fst (nth j0 BL (0, 0)) \/ fst (nth j0 BL (0, 0)) + snd (nth j0 BL (0, 0)) <= fst (nth i0 BL (0, 0))).
{ intros i0 j0 Hi Hj Hne.
assert (Ei : nth i0 BL (0, 0) = (fst (nth i0 BL (0, 0)), snd (nth i0 BL (0, 0)))) by (destruct (nth i0 BL (0, 0)); reflexivity).
assert (Ej : nth j0 BL (0, 0) = (fst (nth j0 BL (0, 0)), snd (nth j0 BL (0, 0)))) by (destruct (nth j0 BL (0, 0)); reflexivity).
apply (live_apart RT AF Σ8 m29 _ _ _ _ ART29).
- rewrite <- Ei. apply LIVBL. apply nth_In. exact Hi.
- rewrite <- Ej. apply LIVBL. apply nth_In. exact Hj.
- rewrite <- (map_nth fst BL (0, 0) i0), <- (map_nth fst BL (0, 0) j0). exact (NDN i0 j0 Hi Hj Hne). }
pose proof (SBAP 1%nat 0%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AP10. pose proof (SBAP 2%nat 0%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AP20.
pose proof (SBAP 3%nat 0%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AP30. pose proof (SBAP 4%nat 0%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AP40.
pose proof (SBAP 5%nat 0%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AP50. pose proof (SBAP 6%nat 0%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AP60.
pose proof (SBAP 7%nat 0%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AP70. pose proof (SBAP 8%nat 0%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AP80.
cbn [nth BL fst snd] in AP10, AP20, AP30, AP40, AP50, AP60, AP70, AP80.

destruct (live_below_lo RT AF Σ8 m29 _ _ lo ART29 (LIVBL (a_g0 a, 256) ltac:(unfold BL; cbn [In]; do 1 right; left; reflexivity)) LOWX) as (_ & LOG0 & _).
destruct (live_below_lo RT AF Σ8 m29 _ _ lo ART29 (LIVBL (a_g1 a, 256) ltac:(unfold BL; cbn [In]; do 2 right; left; reflexivity)) LOWX) as (_ & LOG1 & _).
destruct (live_below_lo RT AF Σ8 m29 _ _ lo ART29 (LIVBL (a_exc a, 4 * sbd_subframeSize s) ltac:(unfold BL; cbn [In]; do 3 right; left; reflexivity)) LOWX) as (_ & LOEX & _).
destruct (live_below_lo RT AF Σ8 m29 _ _ lo ART29 (LIVBL (a_oq a, 32) ltac:(unfold BL; cbn [In]; do 4 right; left; reflexivity)) LOWX) as (_ & LOOQ & _).
destruct (live_below_lo RT AF Σ8 m29 _ _ lo ART29 (LIVBL (a_iq a, 32) ltac:(unfold BL; cbn [In]; do 5 right; left; reflexivity)) LOWX) as (_ & LOIQ & _).
destruct (live_below_lo RT AF Σ8 m29 _ _ lo ART29 (LIVBL (a_pg a, 16) ltac:(unfold BL; cbn [In]; do 6 right; left; reflexivity)) LOWX) as (_ & LOPG & _).
destruct (live_below_lo RT AF Σ8 m29 _ _ lo ART29 (LIVBL (a_er a, 16) ltac:(unfold BL; cbn [In]; do 7 right; left; reflexivity)) LOWX) as (_ & LOER & _).
destruct (live_below_lo RT AF Σ8 m29 _ _ lo ART29 (LIVBL (a_msp a, 64) ltac:(unfold BL; cbn [In]; do 8 right; left; reflexivity)) LOWX) as (_ & LOMS & _).

assert (ART30 : X14x.ART RT Σ8 m30).
{ apply (af_frame RT AF Σ8 m29 m30 lo ART29 LOWX); [| exact WM30]. intros a0 Ha. apply MU30. cbn [outside].
split; [| split; [| exact I]]; intros Hin; apply Ha.
- right; right; left. exists S, 160. split; [exact INLX| clear - Hin; lia].
- left. clear - Hin LOV SPT. unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK, USTACK_TOP in *. lia. }
assert (PF30 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m30).
{ apply (pres_fp_trans _ _ _ _ m m29 m30 PF). apply (pres_fp_of_munch _ _ _ _ _ m29 m30 MU30). intros x Hx Ho. cbn [outside] in Ho |- *.
destruct Ho as (_ & _ & _ & Ho). apply sb_outside_app_inv in Ho. destruct Ho as [Hb _]. rewrite outside_blocks_ivs in Hb.
pose proof (Hb (sbd_blk s, S, SBSTATE_SIZEOF) ltac:(rewrite ELBD; apply in_app_iff; left; cbn [sb_blocks In]; left; reflexivity)) as N0.
unfold blk_addr, blk_size, SBSTATE_SIZEOF in N0. cbn [fst snd] in N0.
split; [clear - N0; lia|]. split; [| exact I]. intros Hin. destruct (SPL x Hx) as [H1 | H1]; clear - H1 Hin LOW LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia. }
clear PF. rename PF30 into PF.
pk_munch_all MU30 WM30 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LOV; cbn [outside]; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in LOV;
split; [lia| split; [lia| exact I]])
ltac:(fun x Hx => clear - Hx LOV LOS SIMG; cbn [outside]; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in LOV; split; [lia| split; [lia| exact I]]).
trm MU30 WM30 SV ltac:(clear - BS1 LO736; lia).
trm MU30 WM30 SL29 ltac:(clear - BS1 LO736; lia).
trm MU30 WM30 LPI29 ltac:(rewrite Llpi29; clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 LER29 ltac:(rewrite Ller29; clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 LQ29 ltac:(rewrite Llq29; clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 LIQ29 ltac:(rewrite Lliq29; clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 LAK29 ltac:(rewrite Llak29; clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 RZ1a ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 RZ1b ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 RZ2a ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 RZ2b ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 RZ3a ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 RZ3b ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 RZ4a ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 RZ4b ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 RZ5a ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 RZ5b ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 FRB ltac:(clear - SFA BF LOV; unfold hid, RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 FRS ltac:(clear - SFS SHF BF0 LOV; unfold hid, RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; subst sf; lia).
trm MU30 WM30 STB ltac:(clear - SFH FS1 FS2 BF1 LOV; unfold hid, RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 OC29 ltac:(rewrite LOWS29; clear - SFH FO1 FO2 BF1 LOV; unfold hid, RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 BOBJ29 ltac:(clear - SFH FA1 FA2 BF1 LOV; unfold hid, RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 BDAT29 ltac:(clear - SPD PD1 PD2 Lbs29 BD29 LOV; unfold hid, RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 G0C ltac:(rewrite JG0; clear - AP10 LOG0 LOV BS1; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 G1C ltac:(rewrite JG1; clear - AP20 LOG1 LOV BS1; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 EXC29 ltac:(clear - AP30 LOEX Lexc29 LOV BS1; cbn [sI set_sbd_submodeID sbd_subframeSize] in Lexc29; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 OQ29 ltac:(rewrite Loq29; clear - AP40 LOOQ LOV BS1; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 IQ29 ltac:(rewrite Liq29; clear - AP50 LOIQ LOV BS1; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 PG29 ltac:(rewrite Lpg29; clear - AP60 LOPG LOV BS1; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 ER29 ltac:(rewrite Ler29; clear - AP70 LOER LOV BS1; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 MSP29 ltac:(rewrite Lmsp29; clear - AP80 LOMS LOV BS1; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 HD ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 FST ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 PT ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 SEED ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 CFG ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 IDC ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 PAD ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
assert (OF30 : offsh [(S + 128, S + 132); (usp + -1232, usp + -1216)]) by (cbn [offsh]; clear - LOS LOV SOFF; unfold hid, RT_STACK, SB_LOOP_STACK, INNOV_STACK, SH_LO, SH_HI in *; lia).
assert (ACC30 : forall o n, acc bsegs m29 o n -> 0 <= o -> o + n <= 140737488355328 -> acc bsegs m30 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch bsegs _ m29 m30 o n (conj H0 (conj H1 H)) MU30 (shfree_of_offsh _ o n OF30 H0 H1)))). }
assert (ACO30 : acc bsegs m30 OUT 8000) by (apply ACC30; [exact ACO29| clear - FO1 FP0; lia| clear - FO2 BF1 LO736 SPT; lia]).
assert (SSP30 : io_ssp m30).
{ apply (sbd_io_ssp_agree m29 m30 SSP29 (AF_DRV Σ8 m30 ART30)). intros a0 Ha. apply MU30. unfold X0r9.SSP_GUARD in Ha. cbn [outside].
clear - Ha LOV LOS SIMG. unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *. split; [lia| split; [lia| exact I]]. }
clear ACA29 ACO29 ACC30 SSP29 ART29 MI29 OF30 MU30.

set (fsz := sbd_frame_size sI) in *.
assert (FSN2 : Z.of_nat (Z.to_nat (2 * fsz)) = 2 * fsz) by (unfold fsz; cbn [sI set_sbd_submodeID sbd_frame_size]; clear - FSV; lia).
apply (f32_split bsegs m30 OUT ows29 (Z.to_nat (2 * fsz))) in OC29; [| rewrite LOWS29; unfold fsz; cbn [sI set_sbd_submodeID sbd_frame_size]; clear - FSV; lia].
destruct OC29 as (OCq & OCr). rewrite FSN2 in OCr.
assert (LOCq : Z.of_nat (length (firstn (Z.to_nat (2 * fsz)) ows29)) = 2 * fsz)
by (rewrite length_firstn, LOWS29; unfold fsz; cbn [sI set_sbd_submodeID sbd_frame_size]; clear - FSV; lia).
assert (LOCr : length (skipn (Z.to_nat (2 * fsz)) ows29) = (2000 - Z.to_nat (2 * fsz))%nat) by (rewrite length_skipn, LOWS29; reflexivity).
generalize dependent (firstn (Z.to_nat (2 * fsz)) ows29). intros owq OCq LOCq.
generalize dependent (skipn (Z.to_nat (2 * fsz)) ows29). intros owr OCr LOCr.
assert (FSQ : fsz = 160 \/ fsz = 320) by (unfold fsz; cbn [sI set_sbd_submodeID sbd_frame_size]; exact FSV).
assert (QN : 2 * fsz = 320 \/ 2 * fsz = 640) by (clear - FSQ; lia).
assert (EA1 : Z_to_bv 64 (OUT + 4 * fsz) = Z_to_bv 64 (OUT + 2 * (2 * fsz))) by (f_equal; clear; lia).
assert (EA2 : Z_to_bv 64 sb_A_H0 = Z_to_bv 64 0x27000) by reflexivity.
assert (EU1104 : bv_unsigned (Z_to_bv 64 (usp + -1232)) = usp + -1232) by (apply unsigned_lit; clear - SPT LOV LOS; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
assert (ING0 : In (a_g0 a, 256) (rt_live RT Σ8)) by (apply LIVBL; unfold BL; cbn [In]; do 1 right; left; reflexivity).
assert (ING1 : In (a_g1 a, 256) (rt_live RT Σ8)) by (apply LIVBL; unfold BL; cbn [In]; do 2 right; left; reflexivity).
pose proof (SBAP 1%nat 2%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as G01. cbn [nth BL fst snd] in G01.
pose proof AL as (G08 & G18 & _).
assert (POAq : pois_above (rt_pois RT Σ8) (bv_unsigned (Z_to_bv 64 (usp + -1232)))).
{ rewrite EU1104. intros e He. rewrite EP8 in He. cbn [sb_pois x_usp X app] in He.
destruct He as [<- |[<- |[<- |[<- |[<- | He]]]]]; [unfold pz_lo; cbn [fst]; clear; lia ..|].
pose proof (POA e He) as H1. clear - H1. lia. }
cps_rt (QMF16 (2 * fsz) QN Σ8 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m30
OUT (a_g0 a) (a_g1 a) lo fh (a_g0 a) 256 (a_g1 a) 256 kh owq (sj_g0 j) (sj_g1 j)
FDO MST eq_refl EA1 EA2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
OCq LOCq INFHX FO1 ltac:(clear - FO2 FSQ; lia)
(acc_sub bsegs m30 OUT 8000 OUT (4 * (2 * fsz)) ACO30 ltac:(clear; lia) ltac:(clear - FSQ; lia)) OAL
G0C JG0 ING0 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - G08; Z.div_mod_to_equations; lia)
G1C JG1 ING1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - G18; Z.div_mod_to_equations; lia)
G01 POAq FRM30 ART30 MI30 ltac:(rewrite EU1104; exact ST30) LOWX
ltac:(rewrite EU1104; clear - LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)
ltac:(rewrite EU1104; clear - SPT; unfold USTACK_TOP in *; lia)
ltac:(rewrite EU1104; clear - SPA; Z.div_mod_to_equations; lia)).
intros cq (Σ9 & Hcq & EL9 & EF9 & ES9 & EC9 & EP9).
cps_unpack_lib Hcq as (v31 & m31 & owq' & g0q & g1q & RS31 & (ART31 & MI31 & WM31 & ST31) & PRES31 & OCq' & LOCq' & G0Q & LG0Q & G1Q & LG1Q & ACQ).
try rewrite EU1104 in PRES31. try rewrite EU1104 in ST31.
clear OCq G0C G1C POAq.

pose proof (SBAP 3%nat 1%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AEX1. pose proof (SBAP 3%nat 2%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AEX2.
pose proof (SBAP 4%nat 1%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AOQ1. pose proof (SBAP 4%nat 2%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AOQ2.
pose proof (SBAP 5%nat 1%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AIQ1. pose proof (SBAP 5%nat 2%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AIQ2.
pose proof (SBAP 6%nat 1%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as APG1. pose proof (SBAP 6%nat 2%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as APG2.
pose proof (SBAP 7%nat 1%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AER1. pose proof (SBAP 7%nat 2%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AER2.
pose proof (SBAP 8%nat 1%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AMS1. pose proof (SBAP 8%nat 2%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AMS2.
cbn [nth BL fst snd] in AEX1, AEX2, AOQ1, AOQ2, AIQ1, AIQ2, APG1, APG2, AER1, AER2, AMS1, AMS2.
destruct (frame_live_apart RT AF Σ8 m30 fh kh PD ND ART30 INFHX INPDX) as (FLPD & _).
assert (G0IN : In (sbd_g0_mem s, a_g0 a, 256) LALL) by (unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; left; reflexivity).
assert (G1IN : In (sbd_g1_mem s, a_g1 a, 256) LALL) by (unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; right; left; reflexivity).

assert (OG : forall x, (lo <= x \/ S <= x < S + 160 \/ fh <= x < fh + fs_size kh \/ PD <= x < PD + ND \/ f <= x < f + 64 \/ sf <= x < sf + 8) ->
~ (a_g0 a <= x < a_g0 a + 256) /\ ~ (a_g1 a <= x < a_g1 a + 256)).
{ intros x Hx. split; intros Hin.
- pose proof (BOUT _ x G0IN ltac:(unfold blk_addr, blk_size; cbn [fst snd]; exact Hin)) as H1. clear - Hx H1. lia.
- pose proof (BOUT _ x G1IN ltac:(unfold blk_addr, blk_size; cbn [fst snd]; exact Hin)) as H1. clear - Hx H1. lia. }
assert (OQF : forall x, ~ (OUT <= x < OUT + 4 * (2 * fsz)) -> ~ (a_g0 a <= x < a_g0 a + 256) -> ~ (a_g1 a <= x < a_g1 a + 256) ->
outside [(OUT, OUT + 4 * (2 * fsz)); (a_g0 a, a_g0 a + 256); (a_g1 a, a_g1 a + 256)] x)
by (intros x H1 H2 H3; cbn [outside]; exact (conj H1 (conj H2 (conj H3 I)))).
tr1 PRES31 WM31 SV ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 SL29 ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 LPI29 ltac:(fun x Hx => apply CLSg; rewrite Llpi29 in Hx; clear - Hx; lia)
ltac:(fun x Hx => rewrite Llpi29 in Hx; destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 LER29 ltac:(fun x Hx => apply CLSg; rewrite Ller29 in Hx; clear - Hx; lia)
ltac:(fun x Hx => rewrite Ller29 in Hx; destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 LQ29 ltac:(fun x Hx => apply CLSg; rewrite Llq29 in Hx; clear - Hx; lia)
ltac:(fun x Hx => rewrite Llq29 in Hx; destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 LIQ29 ltac:(fun x Hx => apply CLSg; rewrite Lliq29 in Hx; clear - Hx; lia)
ltac:(fun x Hx => rewrite Lliq29 in Hx; destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 LAK29 ltac:(fun x Hx => apply CLSg; rewrite Llak29 in Hx; clear - Hx; lia)
ltac:(fun x Hx => rewrite Llak29 in Hx; destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 STK30 ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 RZ1a ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 RZ1b ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 RZ2a ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 RZ2b ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 RZ3a ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 RZ3b ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 RZ4a ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 RZ4b ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 RZ5a ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 RZ5b ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 FRB ltac:(fun x Hx => apply (CLF0g _ _ _ x INF); clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(right; right; right; right; left; clear - Hx; lia)) as (O1 & O2); apply OQF; [clear - Hx FFA FO1 FO2 FSQ; unfold hid in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 FRS ltac:(fun x Hx => apply (CLSFg _ _ _ x INF); clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(right; right; right; right; right; clear - Hx; lia)) as (O1 & O2); apply OQF; [clear - Hx FPHI' SHF1 SHF2 FO1 FO2 FSQ; unfold hid in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 STB ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FS1 FS2; lia)
ltac:(fun x Hx => destruct (OG x ltac:(right; right; left; clear - Hx FS1 FS2; lia)) as (O1 & O2); apply OQF; [clear - Hx HOS' FSQ; unfold hid in *; lia| exact O1| exact O2]).
assert (LOCr' : length owr = (2000 - Z.to_nat (2 * sbd_frame_size s))%nat) by exact LOCr.
tr1 PRES31 WM31 OCr ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FO1 FO2 FSV LOCr'; lia)
ltac:(fun x Hx => destruct (OG x ltac:(right; right; left; clear - Hx FO1 FO2 FSV LOCr'; lia)) as (O1 & O2); apply OQF;
[unfold fsz; cbn [sI set_sbd_submodeID sbd_frame_size]; clear - Hx FSV; lia| exact O1| exact O2]).
tr1 PRES31 WM31 BOBJ29 ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FA1 FA2; lia)
ltac:(fun x Hx => destruct (OG x ltac:(right; right; left; clear - Hx FA1 FA2; lia)) as (O1 & O2); apply OQF; [clear - Hx HAO' FSQ; unfold hid in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 BDAT29 ltac:(fun x Hx => apply (CLLg _ _ _ PD ND x INPDX); clear - Hx PD1 PD2 Lbs29; lia)
ltac:(fun x Hx => destruct (OG x ltac:(right; right; right; left; clear - Hx PD1 PD2 Lbs29; lia)) as (O1 & O2); apply OQF; [clear - Hx FLPD PD1 PD2 Lbs29 FO1 FO2 FSQ; lia| exact O1| exact O2]).
tr1 PRES31 WM31 EXC29 ltac:(fun x Hx => apply (CLLg _ _ _ (a_exc a) (4 * sbd_subframeSize s) x (LIVBL (a_exc a, 4 * sbd_subframeSize s) ltac:(unfold BL; cbn [In]; repeat (first [left; reflexivity | right])))); cbn [sI set_sbd_submodeID sbd_subframeSize] in Lexc29; rewrite ?cells_size_f32 in Hx; clear - Hx Lexc29; lia)
ltac:(fun x Hx => cbn [sI set_sbd_submodeID sbd_subframeSize] in Lexc29; rewrite ?cells_size_f32 in Hx; apply OQF; [intro Hin; pose proof (BOUT (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s) x ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; repeat (first [left; reflexivity | right])) ltac:(unfold blk_addr, blk_size; cbn [fst snd]; clear - Hx Lexc29; lia)) as H1; clear - H1 Hin FO1 FO2 FSQ; lia
| clear - Hx Lexc29 AEX1; lia| clear - Hx Lexc29 AEX2; lia]).
tr1 PRES31 WM31 OQ29 ltac:(fun x Hx => apply (CLLg _ _ _ (a_oq a) (32) x (LIVBL (a_oq a, 32) ltac:(unfold BL; cbn [In]; repeat (first [left; reflexivity | right])))); rewrite Loq29 in Hx; clear - Hx Loq29; lia)
ltac:(fun x Hx => rewrite Loq29 in Hx; apply OQF; [intro Hin; pose proof (BOUT (sbd_old_qlsp s, a_oq a, 32) x ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; repeat (first [left; reflexivity | right])) ltac:(unfold blk_addr, blk_size; cbn [fst snd]; clear - Hx Loq29; lia)) as H1; clear - H1 Hin FO1 FO2 FSQ; lia
| clear - Hx Loq29 AOQ1; lia| clear - Hx Loq29 AOQ2; lia]).
tr1 PRES31 WM31 IQ29 ltac:(fun x Hx => apply (CLLg _ _ _ (a_iq a) (32) x (LIVBL (a_iq a, 32) ltac:(unfold BL; cbn [In]; repeat (first [left; reflexivity | right])))); rewrite Liq29 in Hx; clear - Hx Liq29; lia)
ltac:(fun x Hx => rewrite Liq29 in Hx; apply OQF; [intro Hin; pose proof (BOUT (sbd_interp_qlpc s, a_iq a, 32) x ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; repeat (first [left; reflexivity | right])) ltac:(unfold blk_addr, blk_size; cbn [fst snd]; clear - Hx Liq29; lia)) as H1; clear - H1 Hin FO1 FO2 FSQ; lia
| clear - Hx Liq29 AIQ1; lia| clear - Hx Liq29 AIQ2; lia]).
tr1 PRES31 WM31 PG29 ltac:(fun x Hx => apply (CLLg _ _ _ (a_pg a) (16) x (LIVBL (a_pg a, 16) ltac:(unfold BL; cbn [In]; repeat (first [left; reflexivity | right])))); rewrite Lpg29 in Hx; clear - Hx Lpg29; lia)
ltac:(fun x Hx => rewrite Lpg29 in Hx; apply OQF; [intro Hin; pose proof (BOUT (sbd_pi_gain s, a_pg a, 16) x ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; repeat (first [left; reflexivity | right])) ltac:(unfold blk_addr, blk_size; cbn [fst snd]; clear - Hx Lpg29; lia)) as H1; clear - H1 Hin FO1 FO2 FSQ; lia
| clear - Hx Lpg29 APG1; lia| clear - Hx Lpg29 APG2; lia]).
tr1 PRES31 WM31 ER29 ltac:(fun x Hx => apply (CLLg _ _ _ (a_er a) (16) x (LIVBL (a_er a, 16) ltac:(unfold BL; cbn [In]; repeat (first [left; reflexivity | right])))); rewrite Ler29 in Hx; clear - Hx Ler29; lia)
ltac:(fun x Hx => rewrite Ler29 in Hx; apply OQF; [intro Hin; pose proof (BOUT (sbd_exc_rms s, a_er a, 16) x ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; repeat (first [left; reflexivity | right])) ltac:(unfold blk_addr, blk_size; cbn [fst snd]; clear - Hx Ler29; lia)) as H1; clear - H1 Hin FO1 FO2 FSQ; lia
| clear - Hx Ler29 AER1; lia| clear - Hx Ler29 AER2; lia]).
tr1 PRES31 WM31 MSP29 ltac:(fun x Hx => apply (CLLg _ _ _ (a_msp a) (64) x (LIVBL (a_msp a, 64) ltac:(unfold BL; cbn [In]; repeat (first [left; reflexivity | right])))); rewrite Lmsp29 in Hx; clear - Hx Lmsp29; lia)
ltac:(fun x Hx => rewrite Lmsp29 in Hx; apply OQF; [intro Hin; pose proof (BOUT (sbd_mem_sp s, a_msp a, 64) x ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; repeat (first [left; reflexivity | right])) ltac:(unfold blk_addr, blk_size; cbn [fst snd]; clear - Hx Lmsp29; lia)) as H1; clear - H1 Hin FO1 FO2 FSQ; lia
| clear - Hx Lmsp29 AMS1; lia| clear - Hx Lmsp29 AMS2; lia]).
tr1 PRES31 WM31 HD ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia)
ltac:(fun x Hx => apply OQF; [clear - Hx SFH FO1 FO2 FSQ; unfold hid in *; lia| clear - Hx AP10; lia| clear - Hx AP20; lia]).
tr1 PRES31 WM31 FST ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia)
ltac:(fun x Hx => apply OQF; [clear - Hx SFH FO1 FO2 FSQ; unfold hid in *; lia| clear - Hx AP10; lia| clear - Hx AP20; lia]).
tr1 PRES31 WM31 PT ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia)
ltac:(fun x Hx => apply OQF; [clear - Hx SFH FO1 FO2 FSQ; unfold hid in *; lia| clear - Hx AP10; lia| clear - Hx AP20; lia]).
tr1 PRES31 WM31 SEED ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia)
ltac:(fun x Hx => apply OQF; [clear - Hx SFH FO1 FO2 FSQ; unfold hid in *; lia| clear - Hx AP10; lia| clear - Hx AP20; lia]).
tr1 PRES31 WM31 CFG ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia)
ltac:(fun x Hx => apply OQF; [clear - Hx SFH FO1 FO2 FSQ; unfold hid in *; lia| clear - Hx AP10; lia| clear - Hx AP20; lia]).
tr1 PRES31 WM31 IDC ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia)
ltac:(fun x Hx => apply OQF; [clear - Hx SFH FO1 FO2 FSQ; unfold hid in *; lia| clear - Hx AP10; lia| clear - Hx AP20; lia]).
tr1 PRES31 WM31 PAD ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia)
ltac:(fun x Hx => apply OQF; [clear - Hx SFH FO1 FO2 FSQ; unfold hid in *; lia| clear - Hx AP10; lia| clear - Hx AP20; lia]).
tr1 PRES31 WM31 LE30 ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia)
ltac:(fun x Hx => apply OQF; [clear - Hx SFH FO1 FO2 FSQ; unfold hid in *; lia| clear - Hx AP10; lia| clear - Hx AP20; lia]).
assert (AGL31 : agree_blocks bsegs m30 m31 LBL).
{ apply (agree_blocks_of_pres_fp RT Σ8 _ _ _ m30 m31 LBL PRES31 WM31 LIVEL). intros bk x Hb Hx.
pose proof (BOUT bk x ltac:(unfold LALL; apply in_app_iff; right; exact Hb) Hx) as H1.
apply OQF.
- clear - H1 FO1 FO2 FSQ. lia.
- intros Hin. pose proof (APL (sbd_g0_mem s, a_g0 a, 256) x ltac:(cbn [sb_blocks tl In]; left; reflexivity) ltac:(unfold blk_addr, blk_size; cbn [fst snd]; exact Hin)) as H2.
rewrite outside_blocks_ivs in H2. exact (H2 bk Hb Hx).
- intros Hin. pose proof (APL (sbd_g1_mem s, a_g1 a, 256) x ltac:(cbn [sb_blocks tl In]; right; left; reflexivity) ltac:(unfold blk_addr, blk_size; cbn [fst snd]; exact Hin)) as H2.
rewrite outside_blocks_ivs in H2. exact (H2 bk Hb Hx). }
pk_blocks AGL31. clear AGL31.
assert (OIMG31 : forall y, 65536 <= y < 6664192 -> outside [(OUT, OUT + 4 * (2 * fsz)); (a_g0 a, a_g0 a + 256); (a_g1 a, a_g1 a + 256)] y).
{ intros y Hy. apply OQF; [clear - Hy FO1 FPIMG; lia| |].
- intros Hin. pose proof (BOUT _ y G0IN ltac:(unfold blk_addr, blk_size; cbn [fst snd]; exact Hin)) as H1. clear - H1 Hy. lia.
- intros Hin. pose proof (BOUT _ y G1IN ltac:(unfold blk_addr, blk_size; cbn [fst snd]; exact Hin)) as H1. clear - H1 Hy. lia. }
pk_io_fp PRES31 ERR_rep OUT_rep IO_FP IO_img ltac:(fun y Hy => apply OIMG31; exact Hy).
assert (SSP31 : io_ssp m31).
{ apply (sbd_io_ssp_agree m30 m31 SSP30 (AF_DRV Σ9 m31 ART31)). intros a0 Ha. apply PRES31; [right; left; exact (sbd_ssp_static _ Ha)|].
unfold X0r9.SSP_GUARD in Ha. apply OIMG31. clear - Ha. lia. }
assert (PF31 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m31).
{ apply (pres_fp_trans _ _ _ _ m m30 m31 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ8) (rt_frames RT Σ8) (usp + -1232) _ m30 m31 PRES31).
- intros e He. rewrite EL8. exact He.
- intros e He. rewrite EF8. right. exact He.
- clear; lia.
- intros x Hx Ho. cbn [outside] in Ho. destruct Ho as (_ & HO & _ & Ho). apply sb_outside_app_inv in Ho. destruct Ho as [Hb _].
rewrite ELBD in Hb. pose proof (outside_blocks_app_l _ _ x Hb) as Hb1. rewrite outside_blocks_ivs in Hb1.
pose proof (Hb1 (sbd_g0_mem s, a_g0 a, 256) ltac:(cbn [sb_blocks In]; do 1 right; left; reflexivity)) as N1.
pose proof (Hb1 (sbd_g1_mem s, a_g1 a, 256) ltac:(cbn [sb_blocks In]; do 2 right; left; reflexivity)) as N2.
unfold blk_addr, blk_size in N1, N2. cbn [fst snd] in N1, N2.
apply OQF; [clear - HO FSQ; lia| exact N1| exact N2]. }
clear PF. rename PF31 into PF.
clear ART30 MI30 ST30 SSP30 ACO30 PRES31.
assert (EL98 : rt_live RT Σ9 = rt_live RT Σ8) by exact EL9. assert (EF98 : rt_frames RT Σ9 = rt_frames RT Σ8) by exact EF9.
rewrite <- EL98 in LIVEA, LIVEL, LIVED, LIVBL, INLX, INPDX, ING0, ING1. rewrite <- EF98 in INF, INFHX. rewrite <- ES9 in LOWX.

destruct (af_acc_live RT AF Σ9 m31 S 160 ART31 INLX) as (_ & ACS31).
assert (OBS31 : aobj bsegs m31 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO736 SPT; unfold APP_TOP; lia| exact ACS31]).
assert (INQ9 : In (usp + -992, 32) (rt_pois RT Σ9)) by (rewrite EP9, EP8; cbn [sb_pois x_usp X app]; do 2 right; left; reflexivity).
assert (OBQ31 : aobj bsegs m31 (usp + -992) 32)
by (split; [clear - LOV LOS; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia|]; split; [clear - SPT; unfold APP_TOP, USTACK_TOP in *; lia| exact (af_acc_pois RT AF Σ9 m31 _ _ ART31 INQ9)]).
assert (INOQ9 : In (a_oq a, 32) (rt_live RT Σ9)) by (apply LIVBL; unfold BL; cbn [In]; do 4 right; left; reflexivity).
destruct (af_acc_live RT AF Σ9 m31 _ _ ART31 INOQ9) as (_ & ACOQ31).
assert (OBOQ31 : aobj bsegs m31 (a_oq a) 32) by (split; [clear - OQP; lia|]; split; [clear - OQLO LO736 SPT; unfold APP_TOP; lia| exact ACOQ31]).
cps_seg (sbd_t2 usp lo S OUT A f sf (sbmode_struct (sbd_mode sI)) (sbd_frame_size sI) (usp + -992) (a_oq a) v29 sI a (Z_to_bv 64 (sbd_first sI)) lq29 voq29 ja30
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
SL29 HD FST PT ILPC eq_refl OBS31 S8 SPOS BS1 SOFF eq_refl LQ29 Llq29 OBQ31 OQ29 Loq29 OBOQ31 OQ8 OQP OQLO
ltac:(clear - OQSH; unfold SH_LO, SH_HI; lia) OQS STK30 ST31 ltac:(clear - LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)
LOS ltac:(clear - SPH; lia) SPA MI31 RS31).
clear OBS31 ACS31 OBQ31 OBOQ31 ACOQ31.
destruct POST as (m32 & xa232 & xa332 & xa432 & xa532 & xa632 & xa732 & F32 & voq2 & -> & MU32 & WM32 & MI32 & ST32 & FST32 & OQW2 & Lvoq2).
clear ST31 FST OQ29 Loq29.

pose proof (SBAP 1%nat 4%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AG04. pose proof (SBAP 2%nat 4%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AG14.
pose proof (SBAP 3%nat 4%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AEX4. pose proof (SBAP 5%nat 4%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AIQ4.
pose proof (SBAP 6%nat 4%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as APG4. pose proof (SBAP 7%nat 4%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AER4.
pose proof (SBAP 8%nat 4%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AMS4.
cbn [nth BL fst snd] in AG04, AG14, AEX4, AIQ4, APG4, AER4, AMS4.
assert (ART32 : X14x.ART RT Σ9 m32).
{ apply (af_frame RT AF Σ9 m31 m32 lo ART31 LOWX); [| exact WM32]. intros a0 Ha. apply MU32. cbn [outside].
split; [| split; [| exact I]]; intros Hin; apply Ha.
- right; right; left. exists S, 160. split; [exact INLX| clear - Hin; lia].
- right; right; left. exists (a_oq a), 32. split; [exact INOQ9| clear - Hin; lia]. }
assert (PF32 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m32).
{ apply (pres_fp_trans _ _ _ _ m m31 m32 PF). apply (pres_fp_of_munch _ _ _ _ _ m31 m32 MU32). intros x Hx Ho. cbn [outside] in Ho |- *.
destruct Ho as (_ & _ & _ & Ho). apply sb_outside_app_inv in Ho. destruct Ho as [Hb _]. rewrite outside_blocks_ivs in Hb.
pose proof (Hb (sbd_blk s, S, SBSTATE_SIZEOF) ltac:(rewrite ELBD; apply in_app_iff; left; cbn [sb_blocks In]; left; reflexivity)) as N0.
pose proof (Hb (sbd_old_qlsp s, a_oq a, 32) ltac:(rewrite ELBD; apply in_app_iff; left; cbn [sb_blocks In]; do 4 right; left; reflexivity)) as N4.
unfold blk_addr, blk_size, SBSTATE_SIZEOF in N0, N4. cbn [fst snd] in N0, N4.
split; [clear - N0; lia| split; [exact N4| exact I]]. }
clear PF. rename PF32 into PF.
assert (AGL32 : agree_blocks bsegs m31 m32 LBL).
{ apply (agree_blocks_of_munch bsegs _ m31 m32 LBL MU32 WM32). intros bk x Hb Hx.
pose proof (BOUT bk x ltac:(unfold LALL; apply in_app_iff; right; exact Hb) Hx) as H1. cbn [outside].
split; [clear - H1; lia| split; [| exact I]]. intros Hin.
pose proof (APL (sbd_old_qlsp s, a_oq a, 32) x ltac:(cbn [sb_blocks tl In]; do 3 right; left; reflexivity) ltac:(unfold blk_addr, blk_size; cbn [fst snd]; exact Hin)) as H2.
rewrite outside_blocks_ivs in H2. exact (H2 bk Hb Hx). }
pk_blocks AGL32. clear AGL32.
assert (KEEP : forall P, fp_local IO_FP P -> P m31 -> P m32).
{ intros P L Pm. apply (fp_local_munch IO_FP P _ m31 m32 L IO_img MU32); [| exact Pm]. intros x Hx. unfold SEGTOP_A in Hx. cbn [outside].
split; [clear - Hx SIMG; lia| split; [clear - Hx BOQ0 BOQ1; lia| exact I]]. }
pk_io ERR_rep OUT_rep KEEP. clear KEEP.
assert (SSP32 : io_ssp m32).
{ apply (sbd_io_ssp_agree m31 m32 SSP31 (AF_DRV Σ9 m32 ART32)). intros a0 Ha. apply MU32. unfold X0r9.SSP_GUARD in Ha. cbn [outside].
clear - Ha BOQ0 BOQ1 SIMG. split; [lia| split; [lia| exact I]]. }
trm MU32 WM32 SV ltac:(clear - OQLO BS1 LOV LO736; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 SL29 ltac:(clear - OQLO BS1 LOV LO736; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 STK30 ltac:(clear - OQLO BS1 LOV LO736; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 LPI29 ltac:(rewrite ?Llpi29; clear - OQLO BS1 LOV LO736; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 LER29 ltac:(rewrite ?Ller29; clear - OQLO BS1 LOV LO736; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 LQ29 ltac:(rewrite ?Llq29; clear - OQLO BS1 LOV LO736; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 LIQ29 ltac:(rewrite ?Lliq29; clear - OQLO BS1 LOV LO736; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 LAK29 ltac:(rewrite ?Llak29; clear - OQLO BS1 LOV LO736; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 RZ1a ltac:(clear - OQLO BS1 LOV LO736; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 RZ1b ltac:(clear - OQLO BS1 LOV LO736; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 RZ2a ltac:(clear - OQLO BS1 LOV LO736; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 RZ2b ltac:(clear - OQLO BS1 LOV LO736; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 RZ3a ltac:(clear - OQLO BS1 LOV LO736; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 RZ3b ltac:(clear - OQLO BS1 LOV LO736; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 RZ4a ltac:(clear - OQLO BS1 LOV LO736; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 RZ4b ltac:(clear - OQLO BS1 LOV LO736; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 RZ5a ltac:(clear - OQLO BS1 LOV LO736; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 RZ5b ltac:(clear - OQLO BS1 LOV LO736; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 FRB ltac:(clear - SFA BOQ0 BOQ1 BF; unfold hid in *; lia).
trm MU32 WM32 FRS ltac:(clear - SFS SHF OQSH SHF1 SHF2; unfold hid in *; subst sf; lia).
trm MU32 WM32 STB ltac:(clear - SFH FOQ FS1 FS2; unfold hid in *; lia).
assert (LOCq2 : Z.of_nat (length owq') = 2 * sbd_frame_size s) by exact LOCq'.
trm MU32 WM32 OCq' ltac:(clear - SFH FOQ FO1 FO2 LOCq' LOCq2 FSV FSQ; unfold hid in *; lia).
trm MU32 WM32 OCr ltac:(clear - SFH FOQ FO1 FO2 LOCr LOCr' FSV FSQ; unfold hid in *; lia).
trm MU32 WM32 BOBJ29 ltac:(clear - SFH FOQ FA1 FA2; unfold hid in *; lia).
trm MU32 WM32 BDAT29 ltac:(clear - SPD POQ PD1 PD2 Lbs29; unfold hid in *; lia).
trm MU32 WM32 G0Q ltac:(rewrite ?LG0Q; clear - AP10 AG04; lia).
trm MU32 WM32 G1Q ltac:(rewrite ?LG1Q; clear - AP20 AG14; lia).
assert (Lexc29' : Z.of_nat (length vexc29) = sbd_subframeSize s) by exact Lexc29.
trm MU32 WM32 EXC29 ltac:(clear - AP30 AEX4 Lexc29'; lia).
trm MU32 WM32 IQ29 ltac:(rewrite ?Liq29; clear - AP50 AIQ4; lia).
trm MU32 WM32 PG29 ltac:(rewrite ?Lpg29; clear - AP60 APG4; lia).
trm MU32 WM32 ER29 ltac:(rewrite ?Ler29; clear - AP70 AER4; lia).
trm MU32 WM32 MSP29 ltac:(rewrite ?Lmsp29; clear - AP80 AMS4; lia).
trm MU32 WM32 HD ltac:(clear - OQS; lia).
trm MU32 WM32 PT ltac:(clear - OQS; lia).
trm MU32 WM32 SEED ltac:(clear - OQS; lia).
trm MU32 WM32 CFG ltac:(clear - OQS; lia).
trm MU32 WM32 IDC ltac:(clear - OQS; lia).
trm MU32 WM32 PAD ltac:(clear - OQS; lia).
trm MU32 WM32 LE30 ltac:(clear - OQS; lia).
clear ART31 MI31 SSP31 MU32.

assert (TOP8 : sb_top_stale usp (sbd_mode sI) sm mod 8 = 0)
by (unfold sb_top_stale, sb_exc_hull; destruct (sbd_mode sI); destruct (sm_double_codebook sm =? 0); clear - SPA; Z.div_mod_to_equations; lia).
assert (TOPR : lo <= sb_top_stale usp (sbd_mode sI) sm <= usp + -1216)
by (unfold sb_top_stale, sb_exc_hull; destruct (sbd_mode sI); destruct (sm_double_codebook sm =? 0); clear - LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
assert (POAU : forall e, In e (rt_pois RT Σ9) ->
(sb_top_stale usp (sbd_mode sI) sm <= pz_lo e /\ pz_hi e <= usp + -736) \/ usp + -736 <= pz_lo e).
{ intros e He. rewrite EP9, EP8 in He. cbn [sb_pois x_usp X app] in He.
destruct He as [<- |[<- |[<- |[<- |[<- | He]]]]];
[left; unfold pz_lo, pz_hi, alloca_rr; cbn [fst snd]; split; [clear - TOPR; lia| clear - SPA; Z.div_mod_to_equations; lia] ..|].
right. pose proof (POA e He) as H1. clear - H1. lia. }
assert (COKU : call_ok RT Σ9 m32 (Z_to_bv 64 (usp + -1216)) lo).
{ unfold call_ok. rewrite EU1088. split; [exact ST32|]. split; [exact LOWX|]. split; [clear - LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia|].
split; [clear - SPT; unfold USTACK_TOP in *; lia| clear - SPA; Z.div_mod_to_equations; lia]. }
cps_rt (AUN_lo Σ9 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m32 (sb_top_stale usp (sbd_mode sI) sm) (usp + -736) lo FDO MST V416 eq_refl
ltac:(clear - TOPR LOS; lia) TOP8 ltac:(clear - SPA; Z.div_mod_to_equations; lia) ltac:(clear - TOPR; lia)
ltac:(clear - SPT; unfold USTACK_TOP in *; lia) POAU ART32 MI32 COKU).
intros cu (Σ10 & Hcu & EP10 & EL10 & EF10 & ES10 & EC10).
destruct (ASTA_unpack RT Σ10 (PMfd F0 fs0) _ cu Hcu) as (msu & POU & Hcu'); clear Hcu; cbv beta in POU.
destruct POU as (m33 & v33 & RS33 & (ART33 & MI33 & WM33 & ST33) & PRES33 & ACK33).
cps_ret RS33.
rewrite EU1088 in PRES33, ST33.
clear POAU COKU.
assert (EP10' : rt_pois RT Σ10 = rt_pois RT Σ).
{ rewrite EP10, EP9, EP8. cbn [sb_pois x_usp X app]. unfold pois_drop. cbn [List.filter].
rewrite !(proj2 (Z.leb_gt _ _)) by (unfold pz_lo; cbn [fst]; clear; lia).
fold (pois_drop (usp + -736) (rt_pois RT Σ)). apply pois_drop_above. apply (pois_above_le _ usp); [exact POA| clear; lia]. }
clear STK30.
pose proof (pres_fp_of_pres _ _ _ [] _ _ PRES33) as PF33.
tr1 PF33 WM33 SV ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 SL29 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 RZ1a ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 RZ1b ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 RZ2a ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 RZ2b ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 RZ3a ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 RZ3b ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 RZ4a ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 RZ4b ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 RZ5a ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 RZ5b ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 LPI29 ltac:(fun x Hx => apply CLSg; rewrite ?Llpi29 in Hx; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 LER29 ltac:(fun x Hx => apply CLSg; rewrite ?Ller29 in Hx; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 LQ29 ltac:(fun x Hx => apply CLSg; rewrite ?Llq29 in Hx; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 LIQ29 ltac:(fun x Hx => apply CLSg; rewrite ?Lliq29 in Hx; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 LAK29 ltac:(fun x Hx => apply CLSg; rewrite ?Llak29 in Hx; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 FRB ltac:(fun x Hx => apply (CLF0g _ _ _ x INF); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 FRS ltac:(fun x Hx => apply (CLSFg _ _ _ x INF); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 STB ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FS1 FS2; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 OCq' ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FO1 FO2 LOCq' LOCq2 FSV FSQ; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 OCr ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FO1 FO2 LOCr LOCr' FSV FSQ; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 BOBJ29 ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FA1 FA2; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 BDAT29 ltac:(fun x Hx => apply (CLLg _ _ _ PD ND x INPDX); clear - Hx PD1 PD2 Lbs29; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 G0Q ltac:(fun x Hx => apply (CLLg _ _ _ (a_g0 a) (256) x (LIVBL (a_g0 a, 256) ltac:(unfold BL; cbn [In]; repeat (first [left; reflexivity | right])))); clear - Hx LG0Q; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 G1Q ltac:(fun x Hx => apply (CLLg _ _ _ (a_g1 a) (256) x (LIVBL (a_g1 a, 256) ltac:(unfold BL; cbn [In]; repeat (first [left; reflexivity | right])))); clear - Hx LG1Q; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 EXC29 ltac:(fun x Hx => apply (CLLg _ _ _ (a_exc a) (4 * sbd_subframeSize s) x (LIVBL (a_exc a, 4 * sbd_subframeSize s) ltac:(unfold BL; cbn [In]; repeat (first [left; reflexivity | right])))); clear - Hx Lexc29'; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 OQW2 ltac:(fun x Hx => apply (CLLg _ _ _ (a_oq a) (32) x (LIVBL (a_oq a, 32) ltac:(unfold BL; cbn [In]; repeat (first [left; reflexivity | right])))); clear - Hx Lvoq2; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 IQ29 ltac:(fun x Hx => apply (CLLg _ _ _ (a_iq a) (32) x (LIVBL (a_iq a, 32) ltac:(unfold BL; cbn [In]; repeat (first [left; reflexivity | right])))); clear - Hx Liq29; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 PG29 ltac:(fun x Hx => apply (CLLg _ _ _ (a_pg a) (16) x (LIVBL (a_pg a, 16) ltac:(unfold BL; cbn [In]; repeat (first [left; reflexivity | right])))); clear - Hx Lpg29; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 ER29 ltac:(fun x Hx => apply (CLLg _ _ _ (a_er a) (16) x (LIVBL (a_er a, 16) ltac:(unfold BL; cbn [In]; repeat (first [left; reflexivity | right])))); clear - Hx Ler29; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 MSP29 ltac:(fun x Hx => apply (CLLg _ _ _ (a_msp a) (64) x (LIVBL (a_msp a, 64) ltac:(unfold BL; cbn [In]; repeat (first [left; reflexivity | right])))); clear - Hx Lmsp29; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 HD ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 FST32 ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 PT ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 SEED ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 CFG ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 IDC ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 PAD ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 LE30 ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => exact I).
assert (AGL33 : agree_blocks bsegs m32 m33 LBL) by (exact (agree_blocks_of_pres RT Σ9 _ _ m32 m33 LBL PRES33 WM33 LIVEL)).
pk_blocks AGL33. clear AGL33.
assert (KEEP : forall P, fp_local IO_FP P -> P m32 -> P m33)
by (intros P L Pm; exact (fp_local_pres IO_FP P (rt_live RT Σ9) _ _ m32 m33 L IO_img PRES33 Pm)).
pk_io ERR_rep OUT_rep KEEP. clear KEEP.
assert (PF33' : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m33).
{ apply (pres_fp_trans _ _ _ _ m m32 m33 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ9) (rt_frames RT Σ9) (usp + -1216) [] m32 m33 PF33).
- intros e He. rewrite EL9, EL8. exact He.
- intros e He. rewrite EF9, EF8. right. exact He.
- clear; lia.
- intros x _ _. exact I. }
clear PF. rename PF33' into PF.
clear ART32 MI32 ST32 SSP32 PF33 PRES33 ACK33.

assert (WJ : forall a0 n1 n2, 0 <= n1 -> 0 <= n2 -> wr_at bsegs m33 a0 n1 -> wr_at bsegs m33 (a0 + n1) n2 -> wr_at bsegs m33 a0 (n1 + n2))
by (intros a0 n1 n2 H1 H2 W1 W2; exact (proj2 (wr_at_app bsegs m33 a0 n1 n2 H1 H2) (conj W1 W2))).
assert (WAT : forall a0 n cs, rw_cells bsegs m33 a0 cs -> Z.of_nat (cells_size cs) = n -> wr_at bsegs m33 a0 n)
by (intros a0 n cs H E; rewrite <- E; exact (proj2 H)).
pose proof (WAT _ 32 _ RZ5a eq_refl) as WP0.
pose proof (WAT _ 32 _ LAK29 ltac:(rewrite cells_size_f32, Llak29; reflexivity)) as WP1.
pose proof (WAT _ 32 _ RZ5b eq_refl) as WP2.
pose proof (WAT _ 32 _ RZ4a eq_refl) as WP3.
pose proof (WAT _ 32 _ LIQ29 ltac:(rewrite cells_size_f32, Lliq29; reflexivity)) as WP4.
pose proof (WAT _ 32 _ RZ4b eq_refl) as WP5.
pose proof (WAT _ 32 _ RZ3a eq_refl) as WP6.
pose proof (WAT _ 32 _ LQ29 ltac:(rewrite cells_size_f32, Llq29; reflexivity)) as WP7.
pose proof (WAT _ 32 _ RZ3b eq_refl) as WP8.
pose proof (WAT _ 32 _ RZ2a eq_refl) as WP9.
pose proof (WAT _ 16 _ LER29 ltac:(rewrite cells_size_f32, Ller29; reflexivity)) as WP10.
pose proof (WAT _ 48 _ RZ2b eq_refl) as WP11.
pose proof (WAT _ 32 _ RZ1a eq_refl) as WP12.
pose proof (WAT _ 16 _ LPI29 ltac:(rewrite cells_size_f32, Llpi29; reflexivity)) as WP13.
pose proof (WAT _ 48 _ RZ1b eq_refl) as WP14.
assert (WA1 : wr_at bsegs m33 (usp + -1216) 64) by (exact (WJ _ 32 32 ltac:(lia) ltac:(lia) WP0 ltac:(replace (usp + -1216 + 32) with (usp + -1184) by lia; exact WP1))).
assert (WA2 : wr_at bsegs m33 (usp + -1216) 96) by (exact (WJ _ 64 32 ltac:(lia) ltac:(lia) WA1 ltac:(replace (usp + -1216 + 64) with (usp + -1152) by lia; exact WP2))).
assert (WA3 : wr_at bsegs m33 (usp + -1216) 128) by (exact (WJ _ 96 32 ltac:(lia) ltac:(lia) WA2 ltac:(replace (usp + -1216 + 96) with (usp + -1120) by lia; exact WP3))).
assert (WA4 : wr_at bsegs m33 (usp + -1216) 160) by (exact (WJ _ 128 32 ltac:(lia) ltac:(lia) WA3 ltac:(replace (usp + -1216 + 128) with (usp + -1088) by lia; exact WP4))).
assert (WA5 : wr_at bsegs m33 (usp + -1216) 192) by (exact (WJ _ 160 32 ltac:(lia) ltac:(lia) WA4 ltac:(replace (usp + -1216 + 160) with (usp + -1056) by lia; exact WP5))).
assert (WA6 : wr_at bsegs m33 (usp + -1216) 224) by (exact (WJ _ 192 32 ltac:(lia) ltac:(lia) WA5 ltac:(replace (usp + -1216 + 192) with (usp + -1024) by lia; exact WP6))).
assert (WA7 : wr_at bsegs m33 (usp + -1216) 256) by (exact (WJ _ 224 32 ltac:(lia) ltac:(lia) WA6 ltac:(replace (usp + -1216 + 224) with (usp + -992) by lia; exact WP7))).
assert (WA8 : wr_at bsegs m33 (usp + -1216) 288) by (exact (WJ _ 256 32 ltac:(lia) ltac:(lia) WA7 ltac:(replace (usp + -1216 + 256) with (usp + -960) by lia; exact WP8))).
assert (WA9 : wr_at bsegs m33 (usp + -1216) 320) by (exact (WJ _ 288 32 ltac:(lia) ltac:(lia) WA8 ltac:(replace (usp + -1216 + 288) with (usp + -928) by lia; exact WP9))).
assert (WA10 : wr_at bsegs m33 (usp + -1216) 336) by (exact (WJ _ 320 16 ltac:(lia) ltac:(lia) WA9 ltac:(replace (usp + -1216 + 320) with (usp + -896) by lia; exact WP10))).
assert (WA11 : wr_at bsegs m33 (usp + -1216) 384) by (exact (WJ _ 336 48 ltac:(lia) ltac:(lia) WA10 ltac:(replace (usp + -1216 + 336) with (usp + -880) by lia; exact WP11))).
assert (WA12 : wr_at bsegs m33 (usp + -1216) 416) by (exact (WJ _ 384 32 ltac:(lia) ltac:(lia) WA11 ltac:(replace (usp + -1216 + 384) with (usp + -832) by lia; exact WP12))).
assert (WA13 : wr_at bsegs m33 (usp + -1216) 432) by (exact (WJ _ 416 16 ltac:(lia) ltac:(lia) WA12 ltac:(replace (usp + -1216 + 416) with (usp + -800) by lia; exact WP13))).
assert (WA14 : wr_at bsegs m33 (usp + -1216) 480) by (exact (WJ _ 432 48 ltac:(lia) ltac:(lia) WA13 ltac:(replace (usp + -1216 + 432) with (usp + -784) by lia; exact WP14))).
clear WJ WAT WP0 WP1 WP2 WP3 WP4 WP5 WP6 WP7 WP8 WP9 WP10 WP11 WP12 WP13 WP14 WA1 WA2 WA3 WA4 WA5 WA6 WA7 WA8 WA9 WA10 WA11 WA12 WA13.
clear RZ5a LAK29 RZ5b RZ4a LIQ29 RZ4b RZ3a LQ29 RZ3b RZ2a LER29 RZ2b RZ1a LPI29 RZ1b.
destruct (wr_at_rw_CB m33 (usp + -1216) 480 WA14 ltac:(lia)) as (jh480 & HH480). change (Z.to_nat 480) with 480%nat in HH480. clear WA14.
cps_seg (sbd_t3 usp lo f jh480 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
HH480 ST33 ltac:(clear - LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia) ltac:(clear - SPH; lia) MI33).
destruct POST as (-> & ST34).
clear ST33 HH480.

assert (EFq : rt_frames RT Σ10 = (f, 0%nat) :: rt_frames RT Σ) by (rewrite EF10, EF9, EF8; reflexivity).
assert (ELq : rt_live RT Σ10 = rt_live RT Σ) by (rewrite EL10, EL9, EL8; reflexivity).
assert (ESq : rt_sp0 RT Σ10 = rt_sp0 RT Σ) by (rewrite ES10, ES9, ES8; reflexivity).
set (sF := set_sbd_first sI 0).
set (dF := (speex_decoder_ctl (speex_decoder_ctl low3 CtlGetPiGain).2 CtlGetExc).2).
assert (INVF : sb_inv sF).
{ destruct INV1 as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12). unfold sb_inv, sF. cbn [set_sbd_first sbd_mode sbd_frame_size sbd_full_frame_size
sbd_subframeSize sbd_nbSubframes sbd_lpcSize sbd_first sbd_sampling_rate sbd_lpc_enh_enabled sbd_encode_submode sbd_submodeID sbd_innov_save].
refine (conj I1 (conj I2 (conj I3 (conj I4 (conj I5 (conj I6 (conj (or_introl eq_refl) (conj I8 (conj I9 (conj I10 (conj I11 I12))))))))))). }
set (jF := SBJ le30 seed29 pad129 pad229 g0q g1q vexc29 voq2 viq29 vmsp29 vpg29 ver29).
assert (JOKF : sb_junk_ok sF jF) by (exact (conj Lp129 (conj Lp229 (conj LG0Q (conj LG1Q (conj Lexc29 (conj Lvoq2 (conj Liq29 (conj Lmsp29 (conj Lpg29 Ler29)))))))))).
assert (XF : rw_cells bsegs m33 S (SBCELLS sF a OUT jF))
by (apply sb_pieces_iff; exact (conj HD (conj FST32 (conj PT (conj LE30 (conj SEED (conj CFG (conj IDC PAD)))))))).
assert (BUFSF : sb_bufs bsegs m33 a jF) by (exact (conj G0Q (conj G1Q (conj EXC29 (conj OQW2 (conj IQ29 (conj MSP29 (conj PG29 ER29)))))))).
assert (REPX : DREP OUT STEREO m33 S (DecSB sF dF) LBD).
{ cbn [decst_rep]. exists a, jF, LBL. split; [exact ELBD1|]. split; [exact S8|]. split; [exact SPOS|]. split; [exact INVF|]. split; [exact JOKF|].
split; [exact XF|]. split; [exact BUFSF|]. exists OUT. exact RLOW. }
set (bF := sbsub_bits sm (sbsub_bits sm (sbsub_bits sm (sbsub_bits sm (lsp_bits LspUnquantHigh (sbw_bits b1)))))).
assert (BREPX : bits_rep bsegs m33 A D bF).
{ split; [exists rj29; split; [exact Lrj29| unfold bits_cells; exact BOBJ29]|].
split; [exists bs29; split; [apply (proj2 (u8arr_rw_CB m33 D bs29)); exact BDAT29| exact Hbs29]| exact BSIDE29]. }
assert (PD2X : D + sb_buf_size bF <= PD + ND) by (unfold bF; rewrite BSZ29; exact PD2).
assert (OCF : rw_cells bsegs m33 OUT (f32 (owq' ++ owr))).
{ apply (f32_join bsegs m33 OUT _ _ OCq'). replace (OUT + 4 * Z.of_nat (length owq')) with (OUT + 4 * (2 * fsz)) by (rewrite LOCq'; reflexivity). exact OCr. }
assert (LOCF : length (owq' ++ owr) = 2000%nat) by (rewrite length_app, LOCr; clear - LOCq' FSQ; lia).
assert (WMX : wmono bsegs m m33) by (eapply wmono_trans; [exact WM0|]; eapply wmono_trans; [exact WM8|]; eapply wmono_trans; [exact WM9|]; eapply wmono_trans; [exact WM11|]; eapply wmono_trans; [exact WM12|]; eapply wmono_trans; [exact WM13|]; eapply wmono_trans; [exact WM14|]; eapply wmono_trans; [exact WM15|]; eapply wmono_trans; [exact WM16|]; eapply wmono_trans; [exact WM17|]; eapply wmono_trans; [exact WM19|]; eapply wmono_trans; [exact WM20|]; eapply wmono_trans; [exact WM21|]; eapply wmono_trans; [exact WM22|]; eapply wmono_trans; [exact WM23|]; eapply wmono_trans; [exact WM24|]; eapply wmono_trans; [exact WM25|]; eapply wmono_trans; [exact WM26|]; eapply wmono_trans; [exact WM27|]; eapply wmono_trans; [exact WM28|]; eapply wmono_trans; [exact WM29|]; eapply wmono_trans; [exact WM30|]; eapply wmono_trans; [exact WM31|]; eapply wmono_trans; [exact WM32|]; exact WM33).
assert (FRX : rw_cells bsegs m33 (usp + -736) (sb_fr (fun i => nth i [(Z_to_bv 64 0); (v_8 v29); (Z_to_bv 64 7); (Z_to_bv 64 7); (Z_to_bv 64 3); (Z_to_bv 64 3); (Z_to_bv 64 (Z.shiftr (S + 80) 3)); (Z_to_bv 64 (sha (S + 36))); (Z_to_bv 64 (S + 36)); (Z_to_bv 64 (usp + -736)); (Z_to_bv 64 0); (Z_to_bv 64 ((sbmode_struct (sbd_mode sI)) + 32)); (Z_to_bv 64 (18446744073709551615 - (usp + -896))); (Z_to_bv 64 sf); (Z_to_bv 64 f); (Z_to_bv 64 4); (Z_to_bv 64 (OUT + 4 * (sbd_frame_size sI))); (Z_to_bv 64 (usp + -896)); (v_144 v29); (Z_to_bv 64 f); (Z_to_bv 64 2147483647); (Z_to_bv 64 (S + 112)); (Z_to_bv 64 (S + 96)); (Z_to_bv 64 (18446744073709551615 - (usp + -800))); (Z_to_bv 64 (sha (S + 80))); (Z_to_bv 64 (usp + -1180)); (Z_to_bv 64 (S + 104)); (Z_to_bv 64 (S + 132)); (Z_to_bv 64 32); (Z_to_bv 64 8); (Z_to_bv 64 (usp + -1088)); (Z_to_bv 64 4); (Z_to_bv 64 (usp + -800)); (Z_to_bv 64 (sha (S + 20))); (Z_to_bv 64 (S + 20)); (v_280 v29); (v_288 v29); (Z_to_bv 64 (sha (S + 120))); (Z_to_bv 64 (S + 120)); (Z_to_bv 64 (18446744073709551615 - (usp + -992))); (Z_to_bv 64 S); (Z_to_bv 64 32); (Z_to_bv 64 (S + 88)); (Z_to_bv 64 (S + 72)); (Z_to_bv 64 (sha (S + 152))); (Z_to_bv 64 (sha (S + 144))); (Z_to_bv 64 A); (Z_to_bv 64 (S + 144)); (Z_to_bv 64 (S + 152)); (v_392 v29); (Z_to_bv 64 (S + 80)); (Z_to_bv 64 (sha (S + 28))); (Z_to_bv 64 (S + 28)); (Z_to_bv 64 (usp + -992)); (Z_to_bv 64 0); (Z_to_bv 64 (sha (S + 32))); (Z_to_bv 64 (S + 32)); (v_456 v29); (Z_to_bv 64 (sha (S + 24))); (Z_to_bv 64 (S + 24)); (v_480 v29); (Z_to_bv 64 1); (Z_to_bv 64 OUT); (Z_to_bv 64 4294967296); (v_512 v29); (v_520 v29); (v_528 v29); (Z_to_bv 64 f); (v_544 v29); (v_552 v29); (v_560 v29); (v_568 v29)] (Z_to_bv 64 0)))).
{ rewrite <- sb_fr_of_list by reflexivity. exact SL29. }
assert (TOPX : sb_top_stale usp (sbd_mode sI) sm = 0 \/ (lo <= sb_top_stale usp (sbd_mode sI) sm /\ 0 < sb_top_stale usp (sbd_mode sI) sm <= usp + -192
/\ sb_top_stale usp (sbd_mode sI) sm mod 8 = 0)) by (right; clear - TOPR TOP8 LOS; lia).
cps_rt (sbd_exit_cps RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AUN_lo AUN_nop Σ Σ10 F0 fs0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m m33 lo S OUT STEREO A D f fh PD ND kh LBD
(fun i => nth i [(Z_to_bv 64 0); (v_8 v29); (Z_to_bv 64 7); (Z_to_bv 64 7); (Z_to_bv 64 3); (Z_to_bv 64 3); (Z_to_bv 64 (Z.shiftr (S + 80) 3)); (Z_to_bv 64 (sha (S + 36))); (Z_to_bv 64 (S + 36)); (Z_to_bv 64 (usp + -736)); (Z_to_bv 64 0); (Z_to_bv 64 ((sbmode_struct (sbd_mode sI)) + 32)); (Z_to_bv 64 (18446744073709551615 - (usp + -896))); (Z_to_bv 64 sf); (Z_to_bv 64 f); (Z_to_bv 64 4); (Z_to_bv 64 (OUT + 4 * (sbd_frame_size sI))); (Z_to_bv 64 (usp + -896)); (v_144 v29); (Z_to_bv 64 f); (Z_to_bv 64 2147483647); (Z_to_bv 64 (S + 112)); (Z_to_bv 64 (S + 96)); (Z_to_bv 64 (18446744073709551615 - (usp + -800))); (Z_to_bv 64 (sha (S + 80))); (Z_to_bv 64 (usp + -1180)); (Z_to_bv 64 (S + 104)); (Z_to_bv 64 (S + 132)); (Z_to_bv 64 32); (Z_to_bv 64 8); (Z_to_bv 64 (usp + -1088)); (Z_to_bv 64 4); (Z_to_bv 64 (usp + -800)); (Z_to_bv 64 (sha (S + 20))); (Z_to_bv 64 (S + 20)); (v_280 v29); (v_288 v29); (Z_to_bv 64 (sha (S + 120))); (Z_to_bv 64 (S + 120)); (Z_to_bv 64 (18446744073709551615 - (usp + -992))); (Z_to_bv 64 S); (Z_to_bv 64 32); (Z_to_bv 64 (S + 88)); (Z_to_bv 64 (S + 72)); (Z_to_bv 64 (sha (S + 152))); (Z_to_bv 64 (sha (S + 144))); (Z_to_bv 64 A); (Z_to_bv 64 (S + 144)); (Z_to_bv 64 (S + 152)); (v_392 v29); (Z_to_bv 64 (S + 80)); (Z_to_bv 64 (sha (S + 28))); (Z_to_bv 64 (S + 28)); (Z_to_bv 64 (usp + -992)); (Z_to_bv 64 0); (Z_to_bv 64 (sha (S + 32))); (Z_to_bv 64 (S + 32)); (v_456 v29); (Z_to_bv 64 (sha (S + 24))); (Z_to_bv 64 (S + 24)); (v_480 v29); (Z_to_bv 64 1); (Z_to_bv 64 OUT); (Z_to_bv 64 4294967296); (v_512 v29); (v_520 v29); (v_528 v29); (Z_to_bv 64 f); (v_544 v29); (v_552 v29); (v_560 v29); (v_568 v29)] (Z_to_bv 64 0))
(sb_top_stale usp (sbd_mode sI) sm) 0 (DecSB sF dF) bF (owq' ++ owr) stb j24 j36 (Z_to_bv 64 dtx)
EFq ELq ESq EP10' ART0 POA NAF LIVE INPD PD1 PD2X INFH FA1 FA2 ACA FO1 FO2 ACO FS1 FS2 ACST ART33 MI33 RS31 ST34 LOW
ltac:(clear - LOR DSP; unfold RT_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia) SPT SPA PF WMX FRX
eq_refl V416 eq_refl TOPX SV FRB FRS REPX (fun _ => I) BREPX BOK29 OCF LOCF STB ERRX OUTK).
intros c' (Σ' & Hc' & E1 & E2 & E3 & E4 & E5).
apply Hk. rewrite INS. change (Z.to_nat 4) with 4%nat. cbn [sbsubs_bits]. exists Σ'. split; [exact Hc'|].
pose proof (bkeep_sbsubs 4 sm (lsp_bits LspUnquantHigh (sbw_bits b1))) as BK1. pose proof (bkeep_lsp LspUnquantHigh (sbw_bits b1)) as BK2. pose proof (bkeep_sbw b1) as BK3.
pose proof (bkeep_trans _ _ _ BK3 (bkeep_trans _ _ _ BK2 BK1)) as (K1 & K2 & K3).
cbn [sbsubs_bits] in K1, K2, K3.
destruct (ctl_keeps_mode_nest low3 CtlGetPiGain) as (M1 & N1). destruct (ctl_keeps_mode_nest (speex_decoder_ctl low3 CtlGetPiGain).2 CtlGetExc) as (M2 & N2).
cbn [dec_depth dec_mode dec_nestedR dec_credit sF sI set_sbd_submodeID set_sbd_first sbd_mode].
split; [clear; lia|]. split; [unfold dF; rewrite ctl_keeps_depth, ctl_keeps_depth, DL3; reflexivity|]. split; [reflexivity|].
split; [split; [unfold dF; rewrite M2, M1; exact NM3| exact (N2 (N1 NEST3))]|].
split; [rewrite K2; exact OWN1|]. split; [rewrite K1; exact CHR1|]. split; [rewrite K3; exact BSZ1|].
split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [| exact E5].
rewrite E4, EC10, EC9, EC8, EC7, EC6, EC5. rewrite DL4 in EC4. rewrite DL3 in EC3. rewrite EC2, EC1 in EC3.
pose proof (dec_depth_pos low) as DP. clear - CBX DP EC3 EC4. lia.
Qed.
End SbDecodeWph.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac simpl_sizes ::=
rewrite ?X06d.sb_cells_size, ?cells_size_sb_fhdr, ?cells_size_sb_fshadow, ?cells_size_sb_fr, ?cells_size_sb_saves, ?cells_size_sb_slots,
?cells_size_sbp_hdr, ?cells_size_sbp_ptrs, ?cells_size_sbp_cfg, ?app_length, ?cells_size_app, ?cells_size_f32, ?length_f32;
cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length, ?cells_size_f32, ?length_f32; cbn [length].

Definition sbd_inv_bytes (s : sbd_state bptr) (b1 : bits_st bptr) : list Z :=
match submode_at (sbm_submodes (sbd_mode s)) (sbw_id b1) with
| Some _ => []
| None => if sbw_id b1 =? 0 then [] else notify_bytes MSG_INVALID_MODE
end.

Section SbDecodeWph.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis IO_ssp : forall y, in_ranges IO_FP y -> ~ (X00a.SSP_GUARD <= y < X00a.SSP_GUARD + 8).
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis AF_ERRV : forall Σ m, ART RT Σ m -> acc asegs m STDERR_VAR 8.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.
Hypothesis FPL : fprintf_lib_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis APO : alloca_poison_contract RT.
Hypothesis AUN_lo : allocas_unpoison_lo_contract RT.
Hypothesis AUN_nop : allocas_unpoison_nop_contract RT.
Hypothesis MEMS : memset_icontract RT e_asan_memset.
Hypothesis QMF16 : forall N, N = 320 \/ N = 640 -> qmf_synth_cps16 RT N.
Hypothesis LOST : sb_decode_lost_cps RT.
Hypothesis LOOP : sb_subframe_cps RT.

Theorem sbd_wph_cps : forall (Σ Σx : rts RT) (F0 : list (word * FdEntry)) (fs0 : Fs)
(ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (Fx : bvmap 5 word) (fcx : bv 32)
(m mX : mem) (lo S OUT STEREO A D f fh PD ND : Z) (kh : nat) (LBD LBL : list block) (g : nat -> word)
(s : sbd_state bptr) (a : sb_addrs) (j : sb_junk) (low low3 : dec_state bptr) (b b1 : bits_st bptr) (ows : list word) (stb : list byte)
(j24 j36 : list byte) (dtx : Z) (q1 q' : pst) (ret : Z) (d' : dec_state bptr) (b' : bits_st bptr),
let usp := bv_unsigned sp in let sf := Z.shiftr f 3 + SHB in

sb_outcome s low3 b1 q1 ret d' b' q' ->
dec_depth low3 = dec_depth low -> dec_mode low3 = sbm_nb_mode (sbd_mode s) -> dec_nestedR low3 -> (dec_depth low <= 2)%nat ->
sb_owner b1 = sb_owner b -> sb_chars b1 = sb_chars b -> sb_buf_size b1 = sb_buf_size b ->
(forall d : dec_state bptr, dec_depth d = dec_depth low -> ctl2_cps_at RT d) ->

LBD = sb_blocks s S a ++ LBL -> List.NoDup (map blk_id LBD) -> blocks_al8 LBD -> S mod 8 = 0 -> 0 < S -> sb_inv s -> sb_junk_ok s j ->
match sbd_innov_save s with None => True | Some k => k = 2 * sbd_frame_size s end ->

rt_frames RT Σx = (f, 0%nat) :: rt_frames RT Σ -> rt_live RT Σx = rt_live RT Σ -> rt_sp0 RT Σx = rt_sp0 RT Σ -> rt_pois RT Σx = rt_pois RT Σ ->
rt_credit RT Σ - 1 - 2 * (Z.of_nat (dec_depth low) - 1) - dec_credit low <= rt_credit RT Σx <= rt_credit RT Σ - 1 ->
1 + 4 * (Z.of_nat (dec_depth low) - 1) + dec_credit low <= rt_credit RT Σ ->
(length (rt_frames RT Σ) + Datatypes.S (dec_frames low) <= FRAMES_MAX)%nat ->

ART RT Σ m -> pois_above (rt_pois RT Σ) usp ->
(forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) usp a -> ~ f <= a < f + 64 /\ ~ sf <= a < sf + 8) ->
(forall x, In x LBD -> In (blk_addr x, blk_size x) (rt_live RT Σ)) ->
In (PD, ND) (rt_live RT Σ) -> PD <= D -> D + sb_buf_size b1 <= PD + ND -> (forall x, In x LBD -> blk_addr x <> PD) ->
In (fh, kh) (rt_frames RT Σ) ->
fh <= A -> A + BITS_SIZEOF <= fh + fs_size kh - 8 -> acc asegs m A BITS_SIZEOF -> A mod 4 = 0 ->
fh <= OUT -> OUT + 8000 <= fh + fs_size kh - 8 -> acc asegs m OUT 8000 -> OUT mod 4 = 0 ->
fh <= STEREO -> STEREO + 24 <= fh + fs_size kh - 8 -> acc asegs m STEREO 24 -> STEREO mod 4 = 0 ->
hidp (A + BITS_SIZEOF <= OUT \/ OUT + 8000 <= A) -> hidp (A + BITS_SIZEOF <= STEREO \/ STEREO + 24 <= A) -> hidp (OUT + 8000 <= STEREO \/ STEREO + 24 <= OUT) ->
fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + SB_OWN_STACK + dec_stack low <= usp -> usp + 16 <= USTACK_TOP -> usp mod 32 = 0 ->

ART RT Σx mX -> mem_inv asegs mX -> X1cn.frm0 fcx -> stk asegs mX lo (usp + -608) ->
rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp (dec_W IO_FP A OUT STEREO LBD) m mX -> wmono asegs m mX ->
rw_cells asegs mX (usp + -608) (sb_fr g) ->
g 0%nat = Z_to_bv 64 0 -> g 10%nat = Z_to_bv 64 (OUT + 4 * sbd_frame_size s) -> g 13%nat = Z_to_bv 64 sf -> g 26%nat = Z_to_bv 64 (S + 20) ->
g 27%nat = Z_to_bv 64 (Z.shiftr (S + 20) 3 + SHB) -> g 38%nat = Z_to_bv 64 A -> g 45%nat = Z_to_bv 64 0 ->
g 51%nat = Z_to_bv 64 f -> g 52%nat = Z_to_bv 64 0 ->
rw_cells asegs mX (usp + -160) (sb_saves F ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
rw_cells asegs mX f (sb_fhdr j24 (Z_to_bv 64 dtx) j36) -> (dtx = 0 \/ dtx = 1) -> rw_cells asegs mX sf sb_fshadow ->
rw_cells asegs mX S (SBCELLS s a OUT j) -> sb_bufs asegs mX a j ->
DREP OUT STEREO mX (a_low a) low3 LBL -> EXCREADY mX (a_low a) low3 ->
bits_rep asegs mX A D b1 -> bits_ok b1 ->
rw_cells asegs mX OUT (f32 ows) -> length ows = 2000%nat -> rw_cells asegs mX STEREO [CB 24 stb] ->
acc asegs mX A BITS_SIZEOF -> acc asegs mX OUT 8000 -> acc asegs mX STEREO 24 ->
ERR_rep mX -> (forall so, OUT_rep so m -> OUT_rep so mX) -> io_ssp mX ->
cpsE asegs
(ASTA RT Σx (PMfd F0 fs0)
(eq (MS (R_P usp S OUT f (sbmode_struct (sbd_mode s)) gp (Z_to_bv 64 0x630458) (Z_to_bv 64 RA_sbd_ctl103) xt0 xt1 xt2 (Z_to_bv 64 0) xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 (f + 32)) (Z_to_bv 64 0) xt3 xt4 xt5 xt6) Fx (ret_pc (Z_to_bv 64 RA_sbd_ctl103)) fcx None mX (seg_rom asegs))))
(Spec.X1nu.evw 2 (sbd_inv_bytes s b1))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' (PMfd F0 fs0) (fun ms => exists m' (ows' : list word) (stb' : list byte),
ret_stL (fun _ fc' => X1cn.frm0 fc') ra sp gp (Z_to_bv 64 0x630458) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 ret) m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (dec_W IO_FP A OUT STEREO LBD) m m'
/\ DREP OUT STEREO m' S d' LBD /\ (ret = 0 -> EXCREADY m' S d')
/\ bits_rep asegs m' A D b' /\ bits_ok b'
/\ rw_cells asegs m' OUT (f32 ows') /\ length ows' = 2000%nat /\ rw_cells asegs m' STEREO [CB 24 stb']
/\ acc asegs m' A BITS_SIZEOF /\ acc asegs m' OUT 8000 /\ acc asegs m' STEREO 24
/\ ERR_rep m' /\ (forall so, OUT_rep so m -> OUT_rep so m')) c
/\ -2 <= ret <= 0 /\ dec_depth d' = dec_depth (DecSB s low) /\ dec_mode d' = dec_mode (DecSB s low) /\ dec_nestedR d'
/\ sb_owner b' = sb_owner b /\ sb_chars b' = sb_chars b /\ sb_buf_size b' = sb_buf_size b
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ - dec_credit (DecSB s low) <= rt_credit RT Σ' <= rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).
Proof using AF ERR_loc OUT_loc IO_img IO_ssp AF_DRV AF_ERRV AF_LIB FPL APO AUN_lo AUN_nop MEMS QMF16 LOST LOOP.
intros Σ Σx F0 fs0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 Fx fcx
m mX lo S OUT STEREO A D f fh PD ND kh LBD LBL g s a j low low3 b b1 ows stb j24 j36 dtx q1 q' ret d' b' usp sf
PZ DL3 NM3 NEST3 DEPL OWN1 CHR1 BSZ1 CTL3 ELBD NDUP LAL8 S8 SPOS INV JOK ISV
EFX ELX ESX EPX CBX CRD FRM ART0 POA NAF LIVE INPD PD1 PD2 PDB INFH FA1 FA2 ACA AAL FO1 FO2 ACO OAL FS1 FS2 ACST SAL HAO HAS HOS FD2
LOW LOR SPT SPA ARTX MIX FRMX STX PF WM0 FR G0 G10 G13 G26 G27 G38 G45 G51 G52 SV FRB DTXV FRS X BUFS RLOW EXR BREP BOK OC LOWS STB ACAX ACOX ACTX ERRX OUTK SSPX.
intros T c Hc Hk.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
pose proof (PMfd_mat_stable F0 fs0) as MST. pose proof (PMfd_fdfs_only F0 fs0) as FDO.
assert (DSP : 0 <= dec_stack low) by (clear; induction low; cbn [dec_stack]; unfold NBDEC_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK; lia).
assert (LO608 : lo <= usp - 608) by (clear - LOR DSP; unfold RT_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in LOR; lia).

assert (INL : In (S, 160) (rt_live RT Σ)).
{ specialize (LIVE (sbd_blk s, S, SBSTATE_SIZEOF)). rewrite ELBD in LIVE. exact (LIVE ltac:(left; reflexivity)). }
assert (INLX : In (S, 160) (rt_live RT Σx)) by (rewrite ELX; exact INL).
assert (INPDX : In (PD, ND) (rt_live RT Σx)) by (rewrite ELX; exact INPD).
assert (INF : In (f, 0%nat) (rt_frames RT Σx)) by (rewrite EFX; left; reflexivity).
assert (INFHX : In (fh, kh) (rt_frames RT Σx)) by (rewrite EFX; right; exact INFH).
assert (LOWX : rt_sp0 RT Σx - STACK_WIN <= lo) by (rewrite ESX; exact LOW).
destruct (live_below_lo RT AF Σx mX S 160 lo ARTX INLX LOWX) as (_ & BS1 & LOS).
pose proof (af_live_small RT AF Σx mX S 160 ARTX INLX ltac:(lia)) as SIMG.
destruct (live_below_lo RT AF Σx mX PD ND lo ARTX INPDX LOWX) as (PDP & BLPD & _).
destruct (frame_below_lo RT AF Σx mX fh kh lo ARTX INFHX LOWX) as (BF1 & BF2 & _).
pose proof (frame_facts RT AF Σx mX fh kh ARTX INFHX) as (FP0 & FP64 & FPIMG & _ & FPHI & _).
destruct (frame_below_lo RT AF Σx mX f 0%nat lo ARTX INF LOWX) as (BF & BF0 & _).
pose proof (frame_facts RT AF Σx mX f 0%nat ARTX INF) as (F1 & F64 & FIMG & _ & FHI & SHF & SHF0 & SHF1 & SHF2 & SHF3).
change (fs_size 0) with 64 in *. change (64 / 8) with 8 in *.
fold sf in SHF. rewrite <- SHF in *.
assert (FSZ : 0 <= fs_size kh) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (FS64 : fs_size kh mod 64 = 0 /\ 64 <= fs_size kh).
{ unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat kh) ltac:(lia) ltac:(lia)). split; [rewrite Z.mul_comm; apply Z_mod_mult | lia]. }
assert (FPHI' : fh + fs_size kh <= SH_LO \/ SH_HI <= fh) by (clear - FPHI; unfold SH_LO, SH_HI; lia).
assert (FHI' : f + 64 <= SH_LO \/ SH_HI <= f) by (clear - FHI; unfold SH_LO, SH_HI; lia).
assert (CLH : forall x, fh <= x < fh + fs_size kh - 8 -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x)
by (intros x Hx; right; right; right; left; exists fh, kh; split; [exact INFH | exact Hx]).
assert (FFA : fh + fs_size kh <= f \/ f + 64 <= fh).
{ destruct FS64 as (M64 & G64). destruct (Z_le_gt_dec (f + 64) fh) as [C1|C1]; [right; exact C1|]. left.
destruct (Z_lt_le_dec f fh) as [C2|C2]; [exfalso; destruct (NAF fh (CLH fh ltac:(clear - G64; lia))) as (N1 & _); apply N1; clear - C1 C2; lia|].
destruct (Z_lt_le_dec f (fh + fs_size kh - 8)) as [C3|C3]; [exfalso; destruct (NAF f (CLH f ltac:(clear - C2 C3; lia))) as (N1 & _); apply N1; clear; lia|].
clear - C3 M64 FP64 F64. Z.div_mod_to_equations. lia. }
unfold BITS_SIZEOF in *.
destruct (frame_live_apart RT AF Σx mX f 0%nat S 160 ARTX INF INLX) as (SFA & SFS).
change (fs_size 0) with 64 in SFA, SFS. rewrite SHF0 in SFS.
destruct (frame_live_apart RT AF Σx mX fh kh S 160 ARTX INFHX INLX) as (SFH & _).
assert (HAO' : A + 48 <= OUT \/ OUT + 8000 <= A) by (clear - HAO; unfold hidp in HAO; exact HAO).
assert (HAS' : A + 48 <= STEREO \/ STEREO + 24 <= A) by (clear - HAS; unfold hidp in HAS; exact HAS).
assert (HOS' : OUT + 8000 <= STEREO \/ STEREO + 24 <= OUT) by (clear - HOS; unfold hidp in HOS; exact HOS).
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
set (LALL := tl (sb_blocks s S a) ++ LBL).
assert (LALLD : forall x, In x LALL -> In x LBD) by (intros x Hx; rewrite ELBD; cbn [sb_blocks tl app] in Hx |- *; right; exact Hx).
assert (LIVEA : forall x, In x LALL -> In (blk_addr x, blk_size x) (rt_live RT Σx)) by (intros x Hx; rewrite ELX; exact (LIVE x (LALLD x Hx))).
assert (LIVEL : forall x, In x LBL -> In (blk_addr x, blk_size x) (rt_live RT Σx)) by (intros x Hx; rewrite ELX; apply LIVE; rewrite ELBD; apply in_app_iff; right; exact Hx).
assert (LIVED : forall x, In x LBD -> In (blk_addr x, blk_size x) (rt_live RT Σx)) by (intros x Hx; rewrite ELX; exact (LIVE x Hx)).
assert (BOUT : forall bk x, In bk LALL -> blk_addr bk <= x < blk_addr bk + blk_size bk ->
x < lo /\ (x < S \/ S + 160 <= x) /\ (x < fh \/ fh + fs_size kh <= x) /\ (x < PD \/ PD + ND <= x) /\ (x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)
/\ (x < 65536 \/ 6627328 <= x)).
{ intros bk x Hb Hx. pose proof (LIVEA bk Hb) as LB.
destruct (live_below_lo RT AF Σx mX _ _ lo ARTX LB LOWX) as (_ & B1 & _).
destruct (frame_live_apart RT AF Σx mX fh kh _ _ ARTX INFHX LB) as (B2 & _).
destruct (frame_live_apart RT AF Σx mX f 0%nat _ _ ARTX INF LB) as (B5 & B6). change (fs_size 0) with 64 in B5, B6. rewrite SHF0, <- SHF in B6.
pose proof (live_facts RT AF Σx mX _ _ ARTX LB) as (_ & _ & B7 & _).
assert (NE : blk_addr bk <> S).
{ pose proof NDUP as ND'. rewrite ELBD in ND'. cbn [sb_blocks app map blk_id blk_addr fst snd] in ND'. apply List.NoDup_cons_iff in ND'. destruct ND' as [NI _].
intros E. apply NI. rewrite <- E. unfold LALL in Hb. cbn [sb_blocks tl app] in Hb. exact (in_map blk_id _ _ Hb). }
pose proof (live_apart RT AF Σx mX _ _ _ _ ARTX LB INLX NE) as B3.
pose proof (live_apart RT AF Σx mX _ _ _ _ ARTX LB INPDX (PDB bk (LALLD bk Hb))) as B4.
unfold SEGTOP_A in B7. clear - B1 B2 B3 B4 B5 B6 B7 Hx. lia. }
assert (OUTB : forall x, (lo <= x \/ S <= x < S + 160 \/ fh <= x < fh + fs_size kh \/ PD <= x < PD + ND \/ f <= x < f + 64 \/ sf <= x < sf + 8
\/ 65536 <= x < 6627328) -> outside (blocks_ivs LBL) x).
{ intros x Hx. apply outside_blocks_ivs. intros bk Hb Hin.
pose proof (BOUT bk x ltac:(unfold LALL; apply in_app_iff; right; exact Hb) Hin) as H1. clear - Hx H1. lia. }
assert (APL : forall bk x, In bk (tl (sb_blocks s S a)) -> blk_addr bk <= x < blk_addr bk + blk_size bk -> outside (blocks_ivs LBL) x).
{ intros bk x Hb Hx. apply outside_blocks_ivs. intros b2 Hb2 Hin.
assert (NE : blk_addr bk <> blk_addr b2).
{ pose proof NDUP as ND'. rewrite ELBD, map_app in ND'. apply (NoDup_app_in_neq _ _ (blk_id bk) (blk_id b2) ND'); [apply in_map; cbn [sb_blocks tl] in Hb |- *; right; exact Hb| apply in_map; exact Hb2]. }
pose proof (live_apart RT AF Σx mX _ _ _ _ ARTX (LIVEA bk ltac:(unfold LALL; apply in_app_iff; left; exact Hb)) (LIVEL b2 Hb2) NE) as AP.
clear - AP Hx Hin. lia. }
pose proof (proj2 (decst_rep_pos _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RLOW)) as SL8.

pose proof (af_client_consts RT AF Σx mX ARTX) as CCX.
pose proof (AF_LIB Σx mX ARTX) as LCX.
assert (OBA : aobj asegs mX A 48) by (split; [clear - FA1 FP0; lia|]; split; [clear - FA2 BF1 LO608 SPT; unfold APP_TOP, USTACK_TOP in *; lia| exact ACAX]).
destruct (af_acc_live RT AF Σx mX PD ND ARTX INPDX) as (_ & ACPD).
assert (OBD : aobj asegs mX D (sb_buf_size b1))
by (split; [clear - PDP PD1; lia|]; split; [clear - PD2 BLPD LO608 SPT; unfold APP_TOP, USTACK_TOP in *; lia|
exact (acc_sub asegs mX PD ND D (sb_buf_size b1) ACPD PD1 PD2)]).
assert (ASH : A + 48 <= SH_LO \/ SH_HI <= A) by (clear - FPHI' FA1 FA2; lia).
assert (AIMG : IMG_TOP <= A) by (clear - FPIMG FA1; unfold IMG_TOP, SEGTOP_A in *; lia).
assert (ALO : A + 48 <= lo) by (clear - FA2 BF1; lia).
assert (DLO : D + sb_buf_size b1 <= lo) by (clear - PD2 BLPD; lia).
assert (LO672 : lo <= usp + -608 - 64) by (clear - LOR DSP; unfold RT_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
pose proof (live_facts RT AF Σx mX S 160 ARTX INLX) as (_ & _ & _ & SHI).
assert (SOFF : S + 160 <= SH_LO \/ SH_HI <= S) by (clear - SHI; unfold SH_LO, SH_HI in *; lia).
assert (SPH : usp < 2^63) by (clear - SPT; unfold USTACK_TOP in *; lia).
destruct (af_acc_live RT AF Σx mX S 160 ARTX INLX) as (_ & ACS).
assert (OBS : aobj asegs mX S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO608 SPT; unfold APP_TOP, USTACK_TOP in *; lia| exact ACS]).
pose proof INV as (IMODE & IFS & IFFS & ISFS & INS & ILPC & IFST & _ & _ & IES & IID & IISV).
sb_unpack X as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_w5 usp lo S OUT A D f (sbmode_struct (sbd_mode s)) g s b1 (sj_pad1 j) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
FR G38 CFG IES OBS S8 SPOS BS1 SOFF BREP BOK OBA OBD ASH AIMG ALO DLO STX LO672 LOS SPH CCX MIX).
cps_norm. cps_hide.
destruct POST as (m8 & xra8 & xt08 & xt18 & xt28 & xa18 & xa28 & xa38 & xa48 & xa58 & xa68 & xa78 & xt38 & xt48 & xt58 & xt68
& -> & MU8 & WM8 & MI8 & ST8 & FR8 & BREP8 & BOK8 & BSZ8 & IDR).
clear FR BREP HD FST PT LE SEED CFG IDC PAD CCX LCX OBA OBD OBS ACS ACPD.
assert (EXR' : 0 = 0 -> EXCREADY mX (a_low a) low3) by (intros _; exact EXR). clear EXR.
Time pk_munch_all MU8 WM8 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LO672 FA1 FA2; unfold BITS_SIZEOF; cbn [outside]; split; [lia| split; [lia| exact I]])
ltac:(fun x Hx => clear - Hx FA1 FPIMG LO672 LOS; unfold BITS_SIZEOF; cbn [outside]; split; [lia| split; [lia| exact I]]).
unfold BITS_SIZEOF in MU8. unfold dec_W, BITS_SIZEOF in PF.
Time cps_seg_post.

assert (OF8 : offsh [(A, A + 48); (usp + -672, usp + -160)]) by (cbn [offsh]; clear - ASH LOS LO672; unfold hid, SH_LO, SH_HI in *; lia).
assert (ACC8 : forall o n, acc asegs mX o n -> 0 <= o -> o + n <= 140737488355328 -> acc asegs m8 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch asegs _ mX m8 o n (conj H0 (conj H1 H)) MU8 (shfree_of_offsh _ o n OF8 H0 H1)))). }
assert (ACA8 : acc asegs m8 A 48) by (apply ACC8; [exact ACAX| clear - FA1 FP0; lia| clear - FA2 BF1 LO608 SPT; lia]).
assert (ACO8 : acc asegs m8 OUT 8000) by (apply ACC8; [exact ACOX| clear - FO1 FP0; lia| clear - FO2 BF1 LO608 SPT; lia]).
assert (ACT8 : acc asegs m8 STEREO 24) by (apply ACC8; [exact ACTX| clear - FS1 FP0; lia| clear - FS2 BF1 LO608 SPT; lia]).
clear ACAX ACOX ACTX ACC8.
assert (SSP8 : io_ssp mX -> io_ssp m8).
{ intros H. apply (sbd_io_ssp_agree mX m8 H (AF_DRV Σx m8 ART)). intros a0 Ha. apply MU8. unfold X00a.SSP_GUARD in Ha. cbn [outside].
clear - Ha FA1 FPIMG LO672 LOS. split; [lia| split; [lia| exact I]]. }
apply SSP8 in SSPX. clear SSP8.

apply sb_pieces_iff in X. destruct X as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
destruct (af_acc_live RT AF Σx m8 S 160 ART INLX) as (_ & ACS8).
assert (OBS8 : aobj asegs m8 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO608 SPT; unfold APP_TOP; lia| exact ACS8]).
pose proof (AF_LIB Σx m8 ART) as LC8.
assert (OBM : aobj asegs m8 (sbmode_struct (sbd_mode s)) 216).
{ destruct IMODE as [E|E]; rewrite E; cbn [sbmode_struct]; (apply (aobj_lit RT AF Σx m8 _ 216 ART);
[ unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_sb_wb_mode, A_sb_uwb_mode; lia | unfold A_sb_wb_mode, A_sb_uwb_mode, APP_TOP; lia]). }
assert (SLO8 : S + 160 <= usp + -608) by (clear - BS1 LO608; lia).
assert (SHL : 17594333495296 <= usp + -608) by (clear - LOS LO608; lia).
Time cps_seg (sbd_w6 usp S OUT A f (sbmode_struct (sbd_mode s)) (sbw_id b1) (fupds g [(44%nat, Z_to_bv 64 (S + 144)); (43%nat, Z_to_bv 64 (S + 152))]) s (sj_pad1 j)
(Z_to_bv 64 (sbd_submodeID s)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
FR8 ltac:(cbn [fupds Nat.eqb]; reflexivity) ltac:(cbn [fupds Nat.eqb]; reflexivity) CFG IDC OBS8 S8 SPOS SLO8 SOFF SIMG IMODE eq_refl OBM LC8 IDR SHL SPH MI8).
destruct POST as (m9 & xa09 & xa19 & -> & MU9 & WM9 & MI9 & IDC9).
clear IDC.
destruct BREP8 as ((rj8 & Lrj8 & BOBJ8) & (bs8 & BDAT8 & Hbs8) & BSIDE8). unfold bits_cells in BOBJ8. apply (proj1 (u8arr_rw_CB m8 D bs8)) in BDAT8.
assert (Lbs8 : Z.of_nat (length bs8) = sb_buf_size b1) by (pose proof BOK8 as OK'; unfold bits_ok in OK'; rewrite Hbs8, zlength_map_unsigned, BSZ8 in OK'; clear - OK'; lia).
assert (BD8 : D + Z.of_nat (length bs8) <= lo) by (rewrite Lbs8; exact DLO).
Time pk_munch_all MU9 WM9 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1; cbn [outside]; split; [lia| exact I])
ltac:(fun x Hx => clear - Hx SIMG; unfold SEGTOP_A in *; cbn [outside]; split; [lia| exact I]).
assert (OUTS : forall x, outside (blocks_ivs LBD) x -> ~ (S <= x < S + 160)).
{ intros x Ho. rewrite ELBD in Ho. cbn [sb_blocks app blocks_ivs map outside blk_addr blk_size fst snd] in Ho. destruct Ho as [Ho _]. unfold SBSTATE_SIZEOF in Ho. exact Ho. }
assert (ART9 : X0ec.ART RT Σx m9).
{ apply (af_frame RT AF Σx m8 m9 lo ART LOWX); [| exact WM9]. intros a0 Ha. apply MU9. cbn [outside]. split; [| exact I].
intros Hin. apply Ha. right; right; left. exists S, 160. split; [exact INLX | clear - Hin; lia]. }
assert (PF9 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m9).
{ apply (pres_fp_trans _ _ _ _ m m8 m9 PF). apply (pres_fp_of_munch _ _ _ _ _ m8 m9 MU9). intros x Hx Ho. cbn [outside] in Ho |- *.
destruct Ho as (_ & _ & _ & Ho). apply sb_outside_app_inv in Ho. destruct Ho as [Hb _]. split; [intros Hin; apply (OUTS x Hb); clear - Hin; lia | exact I]. }
clear PF. rename PF9 into PF.
assert (SPDN : S <> PD) by (apply (PDB (sbd_blk s, S, SBSTATE_SIZEOF)); rewrite ELBD; left; reflexivity).
pose proof (live_apart RT AF Σx m8 S 160 PD ND ART INLX INPDX SPDN) as SPD.
assert (BDS : D + Z.of_nat (length bs8) <= S \/ S + 160 <= D) by (clear - SPD PD1 PD2 Lbs8; lia).
Time seg_transport m8 m9 MU9 WM9.
clear ART. rename ART9 into ART.

assert (OF9 : offsh [(S + 152, S + 156)]) by (cbn [offsh]; clear - SOFF; unfold hid, SH_LO, SH_HI in *; lia).
assert (ACC9 : forall o n, acc asegs m8 o n -> 0 <= o -> o + n <= 140737488355328 -> acc asegs m9 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch asegs _ m8 m9 o n (conj H0 (conj H1 H)) MU9 (shfree_of_offsh _ o n OF9 H0 H1)))). }
assert (ACA9 : acc asegs m9 A 48) by (apply ACC9; [exact ACA8| clear - FA1 FP0; lia| clear - FA2 BF1 LO608 SPT; lia]).
assert (ACO9 : acc asegs m9 OUT 8000) by (apply ACC9; [exact ACO8| clear - FO1 FP0; lia| clear - FO2 BF1 LO608 SPT; lia]).
assert (ACT9 : acc asegs m9 STEREO 24) by (apply ACC9; [exact ACT8| clear - FS1 FP0; lia| clear - FS2 BF1 LO608 SPT; lia]).
clear ACA8 ACO8 ACT8 ACC9.
assert (SSP9 : io_ssp m8 -> io_ssp m9).
{ intros H. apply (sbd_io_ssp_agree m8 m9 H (AF_DRV Σx m9 ART)). intros a0 Ha. apply MU9. unfold X00a.SSP_GUARD in Ha. cbn [outside].
clear - Ha SIMG. unfold SEGTOP_A in *. split; [lia| exact I]. }
apply SSP9 in SSPX. clear SSP9.

set (id := sbw_id b1) in *.
set (sI := set_sbd_submodeID s id).
assert (X9 : rw_cells asegs m9 S (SBCELLS sI a OUT j)).
{ apply sb_pieces_iff. exact (conj HD (conj FST (conj PT (conj LE (conj SEED (conj CFG (conj IDC9 PAD))))))). }
clear HD FST PT LE SEED CFG IDC9 PAD.
assert (INV1 : sb_inv sI).
{ destruct INV as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12). unfold sb_inv. cbn [sI set_sbd_submodeID sbd_mode sbd_frame_size sbd_full_frame_size
sbd_subframeSize sbd_nbSubframes sbd_lpcSize sbd_first sbd_sampling_rate sbd_lpc_enh_enabled sbd_encode_submode sbd_submodeID sbd_innov_save].
refine (conj I1 (conj I2 (conj I3 (conj I4 (conj I5 (conj I6 (conj I7 (conj I8 (conj I9 (conj I10 (conj _ I12))))))))))). clear - IDR. lia. }
assert (JOK1 : sb_junk_ok sI j) by (exact JOK).
assert (ELBD1 : LBD = sb_blocks sI S a ++ LBL) by (exact ELBD).
unfold sb_outcome in PZ. cbv zeta in PZ. fold id sI in PZ.
destruct (submode_at (sbm_submodes (sbd_mode s)) id) as [sm|] eqn:ESM.
2: destruct (id =? 0) eqn:EID.

3: {
destruct PZ as (-> & -> & -> & _).
assert (EB : sbd_inv_bytes s b1 = notify_bytes MSG_INVALID_MODE) by (unfold sbd_inv_bytes; fold id; rewrite ESM, EID; reflexivity).
rewrite EB.
assert (EV : sb_id_valid (sbd_mode s) id = false) by (unfold sb_id_valid; rewrite ESM, EID; reflexivity).
rewrite EV in Hc.
pose proof (AF_DRV Σx m9 ART) as ((GOTE & VARE) & _).
assert (OBV : aobj asegs m9 SB_STDERR_VAR 8) by (split; [unfold SB_STDERR_VAR; lia|]; split; [unfold SB_STDERR_VAR, APP_TOP; lia| exact (AF_ERRV Σx m9 ART)]).
cps_seg (sbd_w7 usp S OUT f (sbmode_struct (sbd_mode s)) STDERR_FILE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OBV GOTE VARE MI9).
subst ms.

rewrite <- sb_msg_invalid_unsigned, <- sb_fpl_notify_bytes.
change (Spec.X1nu.evw 2 (fpl_msg FLnotify sb_msg_invalid 0)) with (SpecA.X1rn.evw 2 (fpl_msg FLnotify sb_msg_invalid 0)).
assert (EU608 : bv_unsigned (Z_to_bv 64 (usp + -608)) = usp + -608) by (apply unsigned_lit; clear - SPT LO608 LOS; lia).
cps_rtE (FPL Σx F0 fs0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m9 FLnotify SB_FMT_NOTIFY SB_MSG_INVALID 0 sb_msg_invalid STDERR_FILE lo).
{ intros E; discriminate E. }
{ unfold SB_FMT_NOTIFY. cbn [fpl_fmts In]. right; right; right; left; reflexivity. }
{ exists 51. split; [unfold ACC_LITS, SB_MSG_INVALID; cbn [In]; repeat (first [left; reflexivity | right])| vm_compute; intros XX; discriminate XX]. }
{ exact (sb_msg_invalid_at m9 MI9). }
{ exact sb_msg_invalid_nonul. }
{ unfold call_ok. rewrite EU608. split; [exact ST8|]. split; [exact LOWX|]. split; [clear - LOR DSP; unfold RT_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia|].
split; [clear - SPT; unfold USTACK_TOP in *; lia| clear - SPA; Z.div_mod_to_equations; lia]. }
{ rewrite EU608. apply (pois_above_le _ usp); [rewrite EPX; exact POA | clear; lia]. }
intros cf10 Hc10.
Time cps_unpack_lib Hc10 as (rv & m10 & RS10 & (ART10 & MI10 & WM10 & ST10) & PRES10 & ERR10 & OUT10).
Ltac tr1 PRES WM H tacA tacO :=
lazymatch type of PRES with
| rt_pres_fp ?live ?frames ?sp ?W ?m ?m' =>
lazymatch type of H with
| rw_cells asegs m ?A0 ?cs =>
let H' := fresh "T" in
assert (H' : rw_cells asegs m' A0 cs)
by (apply (rw_cells_agree asegs m m' A0 cs H);
[ apply (agree_of_pres_fp live frames sp W m m' _ PRES); let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; cps_sizes Hx; split; [ tacA x Hx | tacO x Hx ]
| exact WM ]);
clear H; rename H' into H
end
end.
assert (LOWZ : Z.of_nat (length ows) = 2000) by (rewrite LOWS; reflexivity).
assert (CLF : forall x, fh <= x < fh + fs_size kh - 8 -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -608) x)
by (intros x Hx; right; right; right; left; exists fh, kh; split; [exact INFHX| exact Hx]).
assert (CLS : forall x, usp + -608 <= x < usp -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -608) x)
by (intros x Hx; left; clear - Hx SPT; unfold USTACK_TOP in *; lia).
assert (CLL : forall p n x, In (p, n) (rt_live RT Σx) -> p <= x < p + n -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -608) x)
by (intros p n x Hp Hx; right; right; left; exists p, n; split; [exact Hp| exact Hx]).
assert (CLF0 : forall x, f <= x < f + 56 -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -608) x)
by (intros x Hx; right; right; right; left; exists f, 0%nat; split; [exact INF| change (fs_size 0) with 64; lia]).
assert (CLSF : forall x, sf <= x < sf + 8 -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -608) x)
by (intros x Hx; right; right; right; right; exists f, 0%nat; split; [exact INF| change (fs_size 0) with 64; rewrite <- SHF, SHF0; lia]).
assert (OIO : forall x, (x < 65536 \/ 6627328 <= x) -> outside IO_FP x) by (intros x Hx; apply (outside_img IO_FP x IO_img); unfold SEGTOP_A; exact Hx).
tr1 PRES10 WM10 OC ltac:(fun x Hx => apply CLF; clear - Hx FO1 FO2 LOWZ; lia) ltac:(fun x Hx => apply OIO; clear - Hx FO1 FPIMG; unfold SEGTOP_A in *; lia).
tr1 PRES10 WM10 STB ltac:(fun x Hx => apply CLF; clear - Hx FS1 FS2; lia) ltac:(fun x Hx => apply OIO; clear - Hx FS1 FPIMG; unfold SEGTOP_A in *; lia).
tr1 PRES10 WM10 BOBJ8 ltac:(fun x Hx => apply CLF; clear - Hx FA1 FA2; lia) ltac:(fun x Hx => apply OIO; clear - Hx FA1 FPIMG; unfold SEGTOP_A in *; lia).
tr1 PRES10 WM10 BDAT8 ltac:(fun x Hx => apply (CLL PD ND x INPDX); clear - Hx PD1 PD2 Lbs8; lia)
ltac:(fun x Hx => apply OIO; pose proof (live_facts RT AF Σx m9 PD ND ART INPDX) as (_ & _ & IM & _); clear - Hx IM PD1 PD2 Lbs8; unfold SEGTOP_A in *; lia).
tr1 PRES10 WM10 FR8 ltac:(fun x Hx => apply CLS; clear - Hx; lia) ltac:(fun x Hx => apply OIO; clear - Hx LO608 LOS; lia).
tr1 PRES10 WM10 SV ltac:(fun x Hx => apply CLS; clear - Hx; lia) ltac:(fun x Hx => apply OIO; clear - Hx LO608 LOS; lia).
tr1 PRES10 WM10 X9 ltac:(fun x Hx => apply (CLL S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => apply OIO; clear - Hx SIMG; unfold SEGTOP_A in *; lia).
tr1 PRES10 WM10 FRB ltac:(fun x Hx => apply CLF0; clear - Hx; lia) ltac:(fun x Hx => apply OIO; clear - Hx FIMG; unfold SEGTOP_A in *; lia).
tr1 PRES10 WM10 FRS ltac:(fun x Hx => apply CLSF; clear - Hx; lia) ltac:(fun x Hx => apply OIO; clear - Hx SHF1; lia).
cps_ret RS10.

assert (AG10 : agree_blocks asegs m9 m10 LALL).
{ apply (agree_blocks_of_pres_fp RT Σx _ _ _ m9 m10 LALL PRES10 WM10); [exact LIVEA|].
intros bk x Hb Hx. apply OIO. pose proof (BOUT bk x Hb Hx) as H1. clear - H1. tauto. }
unfold LALL in AG10. pk_all AG10. clear AG10.
assert (SHO : forall o n, fh <= o -> o + n <= fh + fs_size kh -> forall i, 0 <= i < n -> outside IO_FP (shad (o + i))).
{ intros o n H1 H2 i Hi. apply OIO. right. unfold shad, SHB. assert (0 <= (o + i) / 8) by (apply Z.div_pos; lia). lia. }
assert (FH8 : fh mod 8 = 0) by (clear - FP64; Z.div_mod_to_equations; lia).
assert (FK8 : fs_size kh mod 8 = 0) by (destruct FS64 as (M64 & _); clear - M64; Z.div_mod_to_equations; lia).
assert (ACA10 : acc asegs m10 A 48)
by (apply (acc_pres_fp_frame _ _ _ _ m9 m10 fh kh A 48 PRES10 INFHX FH8 FK8 ltac:(lia) FA1 ltac:(lia) (SHO A 48 FA1 ltac:(lia)) ACA9)).
assert (ACO10 : acc asegs m10 OUT 8000)
by (apply (acc_pres_fp_frame _ _ _ _ m9 m10 fh kh OUT 8000 PRES10 INFHX FH8 FK8 ltac:(lia) FO1 ltac:(lia) (SHO OUT 8000 FO1 ltac:(lia)) ACO9)).
assert (ACT10 : acc asegs m10 STEREO 24)
by (apply (acc_pres_fp_frame _ _ _ _ m9 m10 fh kh STEREO 24 PRES10 INFHX FH8 FK8 ltac:(lia) FS1 ltac:(lia) (SHO STEREO 24 FS1 ltac:(lia)) ACT9)).
assert (SSP10 : io_ssp m10).
{ apply (sbd_io_ssp_agree m9 m10 SSPX (AF_DRV Σx m10 ART10)). intros a0 Ha. apply PRES10; [right; left; exact (sbd_ssp_static _ Ha)|].
apply X000.outside_of_not_in_ranges'. intros Hin. exact (IO_ssp _ Hin Ha). }
assert (PF10 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m10).
{ apply (pres_fp_trans _ _ _ _ m m9 m10 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σx) (rt_frames RT Σx) (usp + -608) _ m9 m10 PRES10).
- intros e He. rewrite ELX. exact He.
- intros e He. rewrite EFX. right. exact He.
- clear; lia.
- intros x Hx Ho. cbn [outside] in Ho. destruct Ho as (_ & _ & _ & Ho). apply sb_outside_app_inv in Ho. exact (proj2 Ho). }
clear PF ACA9 ACO9 ACT9 SSPX ERRX PRES10. rename PF10 into PF.
assert (OUTK10 : forall so, OUT_rep so m -> OUT_rep so m10) by (intros so H; exact (OUT10 so (OUTK so H))). clear OUTK OUT10.

cps_seg (sbd_w8 usp S OUT f (sbmode_struct (sbd_mode s)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
subst ms.
assert (REPX : DREP OUT STEREO m10 S (DecSB sI low3) LBD).
{ cbn [decst_rep]. exists a, j, LBL. split; [exact ELBD1|]. split; [exact S8|]. split; [exact SPOS|]. split; [exact INV1|]. split; [exact JOK1|].
split; [exact X9|]. split; [exact BUFS|]. exists OUT. exact RLOW. }
assert (BREPX : bits_rep asegs m10 A D (sbw_bits b1)).
{ split; [exists rj8; split; [exact Lrj8| unfold bits_cells; exact BOBJ8]|].
split; [exists bs8; split; [apply (proj2 (u8arr_rw_CB m10 D bs8)); exact BDAT8| exact Hbs8]| exact BSIDE8]. }
assert (PD2X : D + sb_buf_size (sbw_bits b1) <= PD + ND) by (rewrite BSZ8; exact PD2).
assert (WMX : wmono asegs m m10) by (eapply wmono_trans; [exact WM0|]; eapply wmono_trans; [exact WM8|]; eapply wmono_trans; [exact WM9| exact WM10]).
cps_rt (sbd_exit_cps RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AUN_lo AUN_nop Σ Σx F0 fs0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m m10 lo S OUT STEREO A D f fh PD ND kh LBD
(fupds g [(44%nat, Z_to_bv 64 (S + 144)); (43%nat, Z_to_bv 64 (S + 152))]) 0 (-2) (DecSB sI low3) (sbw_bits b1) ows stb j24 j36 (Z_to_bv 64 dtx)
EFX ELX ESX EPX ART0 POA NAF LIVE INPD PD1 PD2X INFH FA1 FA2 ACA FO1 FO2 ACO FS1 FS2 ACST ART10 MI10 ltac:(auto) ST10 LOW
ltac:(clear - LOR DSP; unfold RT_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia) SPT SPA PF WMX FR8
ltac:(cbn [fupds Nat.eqb]; exact G13) ltac:(cbn [fupds Nat.eqb]; exact G52)
(or_introl eq_refl) SV FRB FRS REPX (fun E => False_ind _ ltac:(clear - E; lia)) BREPX BOK8 OC LOWS STB ERR10 OUTK10).
intros c' (Σ' & Hc' & E1 & E2 & E3 & E4 & E5).
apply Hk. exists Σ'. split; [exact Hc'|].
pose proof (bkeep_sbw b1) as (K1 & K2 & K3).
cbn [dec_depth dec_mode dec_nestedR dec_credit sI set_sbd_submodeID sbd_mode].
split; [clear; lia|]. split; [rewrite DL3; reflexivity|]. split; [reflexivity|]. split; [split; [exact NM3| exact NEST3]|].
split; [rewrite K2; exact OWN1|]. split; [rewrite K1; exact CHR1|]. split; [rewrite K3; exact BSZ1|].
split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [| exact E5].
rewrite E4. pose proof (dec_depth_pos low) as DP. clear - CBX DP. lia. }
2: {
destruct PZ as (-> & -> & -> & _).
assert (EB : sbd_inv_bytes s b1 = []) by (unfold sbd_inv_bytes; fold id; rewrite ESM, EID; reflexivity).
rewrite EB. apply rz_emit_nil.
assert (EV : sb_id_valid (sbd_mode s) id = true) by (unfold sb_id_valid; rewrite EID; reflexivity).
rewrite EV in Hc.

destruct (af_acc_live RT AF Σx m9 S 160 ART INLX) as (_ & ACS9).
assert (OBS9 : aobj asegs m9 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO608 SPT; unfold APP_TOP; lia| exact ACS9]).
pose proof (AF_LIB Σx m9 ART) as LC9.
assert (OBM9 : aobj asegs m9 (sbmode_struct (sbd_mode s)) 216).
{ destruct IMODE as [E|E]; rewrite E; cbn [sbmode_struct]; (apply (aobj_lit RT AF Σx m9 _ 216 ART);
[ unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_sb_wb_mode, A_sb_uwb_mode; lia | unfold A_sb_wb_mode, A_sb_uwb_mode, APP_TOP; lia]). }
sb_unpack X9 as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_m usp S OUT f (sbmode_struct (sbd_mode s)) id (fupds g [(44%nat, Z_to_bv 64 (S + 144)); (43%nat, Z_to_bv 64 (S + 152))]) s (sj_pad1 j)
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR8 CFG IDC OBS9 S8 SPOS SLO8 SOFF IMODE eq_refl OBM9 LC9 IDR SHL SPH MI9).
destruct POST as (m11 & xa011 & xa111 & -> & MU11 & WM11 & MI11 & FR11).
match goal with H : ASTA _ _ _ _ _ |- _ => rewrite ESM in H end.
clear FR8 HD FST PT LE SEED CFG IDC PAD OBS9 ACS9 LC9.
Time pk_munch_all MU11 WM11 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LO608; cbn [outside]; split; [lia| exact I])
ltac:(fun x Hx => clear - Hx LO608 LOS; cbn [outside]; split; [lia| exact I]).
Time cps_seg_post.
match goal with H : X0ec.ART RT Σx m11 |- _ => rename H into ART11 end.
assert (OF11 : offsh [(usp + -608, usp + -160)]) by (cbn [offsh]; clear - LOS LO608; unfold SH_LO, SH_HI in *; lia).
assert (ACC11 : forall o n, acc asegs m9 o n -> 0 <= o -> o + n <= 140737488355328 -> acc asegs m11 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch asegs _ m9 m11 o n (conj H0 (conj H1 H)) MU11 (shfree_of_offsh _ o n OF11 H0 H1)))). }
assert (ACA11 : acc asegs m11 A 48) by (apply ACC11; [exact ACA9| clear - FA1 FP0; lia| clear - FA2 BF1 LO608 SPT; lia]).
assert (ACO11 : acc asegs m11 OUT 8000) by (apply ACC11; [exact ACO9| clear - FO1 FP0; lia| clear - FO2 BF1 LO608 SPT; lia]).
assert (ACT11 : acc asegs m11 STEREO 24) by (apply ACC11; [exact ACT9| clear - FS1 FP0; lia| clear - FS2 BF1 LO608 SPT; lia]).
assert (SSP11 : io_ssp m11).
{ apply (sbd_io_ssp_agree m9 m11 SSPX (AF_DRV Σx m11 ART11)). intros a0 Ha. apply MU11. unfold X00a.SSP_GUARD in Ha. cbn [outside].
clear - Ha LO608 LOS. split; [lia| exact I]. }
clear ACA9 ACO9 ACT9 ACC11 SSPX OBM9.

destruct (af_acc_live RT AF Σx m11 S 160 ART11 INLX) as (_ & ACS11).
assert (OBS11 : aobj asegs m11 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO608 SPT; unfold APP_TOP; lia| exact ACS11]).
sb_unpack X9 as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
assert (FSV : sbd_frame_size s = 160 \/ sbd_frame_size s = 320) by (rewrite IFS; destruct IMODE as [E|E]; rewrite E; cbn; [left| right]; reflexivity).
assert (ISVR : match sbd_innov_save sI with None => True | Some k => 0 <= k <= 2000 end)
by (cbn [sI set_sbd_submodeID sbd_innov_save]; destruct (sbd_innov_save s); [rewrite ISV; clear - FSV; lia| exact I]).
assert (FFR : 0 <= sbd_full_frame_size sI <= 640) by (cbn [sI set_sbd_submodeID sbd_full_frame_size]; rewrite IFFS; clear - FSV; lia).
cps_seg (sbd_n1 usp S OUT f (sbmode_struct (sbd_mode s)) sI a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HD PT OBS11 S8 SPOS ltac:(clear - BS1 LO608 SPT; lia)
ltac:(clear - FO1 FP0; lia) ltac:(clear - FO2 BF1 LO608 SPT; lia) ISVR FFR MI11).
clear HD FST PT LE SEED CFG IDC PAD.

assert (TAILN : forall (m11 : mem) (ows : list word) (r_ra r_t0 r_t1 r_t2 r_a0 r_a1 r_a2 r_a3 r_a4 r_a5 r_a6 r_a7 r_t3 r_t4 r_t5 r_t6 : word) (c3 : config),
rw_cells asegs m11 (usp + -160) (sb_saves F ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
rw_cells asegs m11 f (sb_fhdr j24 (Z_to_bv 64 dtx) j36) ->
rw_cells asegs m11 sf sb_fshadow ->
sb_bufs asegs m11 a j ->
rw_cells asegs m11 OUT (f32 ows) -> length ows = 2000%nat ->
rw_cells asegs m11 STEREO [CB 24 stb] ->
ERR_rep m11 ->
stk asegs m11 lo (usp + -608) ->
rw_cells asegs m11 A [C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 (sb_nbBits (sbw_bits b1))); C4 (Z_to_bv 64 (sb_charPtr (sbw_bits b1))); C4 (Z_to_bv 64 (sb_bitPtr (sbw_bits b1)));
C4 (Z_to_bv 64 (sb_owner (sbw_bits b1))); C4 (Z_to_bv 64 (sb_overflow (sbw_bits b1))); C4 (Z_to_bv 64 (sb_buf_size (sbw_bits b1))); CB 16 rj8] ->
rw_cells asegs m11 D [CB (length bs8) bs8] ->
rw_cells asegs m11 S (SBCELLS sI a OUT j) ->
wmono asegs m9 m11 -> mem_inv asegs m11 ->
rw_cells asegs m11 (usp + -608) (sb_fr (fupds (fupds g [(44%nat, Z_to_bv 64 (S + 144)); (43%nat, Z_to_bv 64 (S + 152))])
[(42%nat, Z_to_bv 64 (Z.shiftr (S + 144) 3 + SHB)); (41%nat, Z_to_bv 64 (Z.shiftr (S + 152) 3 + SHB))])) ->
DREP OUT STEREO m11 (a_low a) low3 LBL ->
(forall so, OUT_rep so m -> OUT_rep so m11) ->
ART RT Σx m11 ->
rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m11 ->
acc asegs m11 A 48 -> acc asegs m11 OUT 8000 -> acc asegs m11 STEREO 24 -> io_ssp m11 -> acc asegs m11 S 160 -> aobj asegs m11 S 160 ->
ASTA RT Σx (PMfd F0 fs0) (eq (MS (R_P usp S OUT f (sbmode_struct (sbd_mode s)) gp (Z_to_bv 64 6489176) r_ra r_t0 r_t1 r_t2 r_a0 r_a1 r_a2 r_a3 r_a4 r_a5 r_a6 r_a7
(Z_to_bv 64 (f + 32)) (Z_to_bv 64 A) r_t3 r_t4 r_t5 r_t6) Fx (Z_to_bv 64 0xb7d2c) fcx None m11 (seg_rom asegs))) c3 ->
realizes asegs c3 T).
{ clear SV FRB FRS BUFS OC LOWS STB ERRX ST8 BOBJ8 BDAT8 X9 MU11 WM11 MI11 FR11 EXR RLOW OUTK0 ART11 PF ACA11 ACO11 ACT11 SSP11 ACS11 OBS11 POST Hc.
clear c3 ms m11 ows.
intros m11 ows r_ra r_t0 r_t1 r_t2 r_a0 r_a1 r_a2 r_a3 r_a4 r_a5 r_a6 r_a7 r_t3 r_t4 r_t5 r_t6 c3
SV FRB FRS BUFS OC LOWS STB ERRX ST8 BOBJ8 BDAT8 X9 WM11 MI11 FR11 RLOW OUTK0 ART11 PF ACA11 ACO11 ACT11 SSP11 ACS11 OBS11 Hc.

cps_seg (sbd_n2 usp S OUT f (sbmode_struct (sbd_mode s)) dtx
(fupds (fupds g [(44%nat, Z_to_bv 64 (S + 144)); (43%nat, Z_to_bv 64 (S + 152))]) [(42%nat, Z_to_bv 64 (Z.shiftr (S + 144) 3 + SHB)); (41%nat, Z_to_bv 64 (Z.shiftr (S + 152) 3 + SHB))])
(Z_to_bv 64 0) j24 j36 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
FR11 ltac:(cbn [fupds Nat.eqb]; exact G45) FRB DTXV ltac:(clear - F1; lia) ltac:(clear - FIMG BF LO608 SPT; lia) MI11).
destruct POST as [(DT0 & xa0n & ->) | (DT1 & ->)].
2: {
assert (AL : sb_addrs_al a)
by (apply (sb_addrs_al_of_blocks s S a); intros bk Hb; apply LAL8; rewrite ELBD; apply in_app_iff; left; exact Hb).
assert (NDB : List.NoDup (map blk_id (sb_blocks sI S a))) by (pose proof NDUP as ND'; rewrite ELBD, map_app in ND'; exact (List.NoDup_app_remove_r _ _ ND')).
assert (LIVEB : forall bk, In bk (sb_blocks sI S a) -> In (blk_addr bk, blk_size bk) (rt_live RT Σx))
by (intros bk Hb; apply LIVED; rewrite ELBD; apply in_app_iff; left; exact Hb).
assert (IFO : in_frame_obj RT Σx m11 fh kh OUT 8000) by (exact (conj FO1 (conj FO2 (conj ACO11 OAL)))).
assert (EU608 : bv_unsigned (Z_to_bv 64 (usp + -608)) = usp + -608) by (apply unsigned_lit; clear - SPT LO608 LOS; lia).
assert (POA608 : pois_above (rt_pois RT Σx) (bv_unsigned (Z_to_bv 64 (usp + -608)))) by (rewrite EU608; apply (pois_above_le _ usp); [rewrite EPX; exact POA| clear; lia]).
assert (ST608 : stk asegs m11 lo (bv_unsigned (Z_to_bv 64 (usp + -608)))) by (rewrite EU608; exact ST8).
assert (LOR608 : lo + RT_STACK + SBLOST_STACK <= bv_unsigned (Z_to_bv 64 (usp + -608)))
by (rewrite EU608; clear - LOR DSP; unfold RT_STACK, SBLOST_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
assert (SPT608 : bv_unsigned (Z_to_bv 64 (usp + -608)) + 16 <= USTACK_TOP) by (rewrite EU608; clear - SPT; unfold USTACK_TOP in *; lia).
assert (SPA608 : bv_unsigned (Z_to_bv 64 (usp + -608)) mod 32 = 0) by (rewrite EU608; clear - SPA; Z.div_mod_to_equations; lia).
cps_rt (LOST Σx (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m11 S OUT lo fh kh sI a j ows
FDO MST eq_refl eq_refl eq_refl eq_refl X9 JOK1 INV1 BUFS S8 SPOS AL NDB LIVEB OC LOWS INFHX IFO POA608 ART11 MI11 FRMX ST608 LOWX LOR608 SPT608 SPA608).
intros cl (Σl & Hcl & LVl & FRl & SPl & CRl & POl).
cps_unpack_lib Hcl as (vl & m13 & j' & ows' & RSl & (ART13 & MI13 & WM13 & ST13) & PRES13 & X13 & JOK13 & BUFS13 & OC13 & LOWS13 & ACO13).
try rewrite EU608 in PRES13. try rewrite EU608 in ST13.
clear X9 BUFS OC LOWS ACO11 IFO.

assert (OUTL13 : forall x, (x < OUT \/ OUT + 8000 <= x) -> (x < S \/ S + 160 <= x) -> outside (blocks_ivs (tl (sb_blocks sI S a))) x ->
outside ((OUT, OUT + 8000) :: blocks_ivs (sb_blocks sI S a)) x).
{ intros x H1 H2 H3. cbn [outside blocks_ivs sb_blocks map blk_addr blk_size fst snd]. unfold SBSTATE_SIZEOF.
split; [clear - H1; lia|]. split; [clear - H2; lia|]. exact H3. }
assert (OTB : forall x, (lo <= x \/ fh <= x < fh + fs_size kh \/ PD <= x < PD + ND \/ f <= x < f + 64 \/ sf <= x < sf + 8) ->
outside (blocks_ivs (tl (sb_blocks sI S a))) x).
{ intros x Hx. apply outside_blocks_ivs. intros bk Hb Hin.
pose proof (BOUT bk x ltac:(unfold LALL; apply in_app_iff; left; exact Hb) Hin) as H1. clear - Hx H1. lia. }
assert (CLF : forall x, fh <= x < fh + fs_size kh - 8 -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -608) x)
by (intros x Hx; right; right; right; left; exists fh, kh; split; [exact INFHX| exact Hx]).
assert (CLS : forall x, usp + -608 <= x < usp -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -608) x)
by (intros x Hx; left; clear - Hx SPT; unfold USTACK_TOP in *; lia).
assert (CLL : forall p n x, In (p, n) (rt_live RT Σx) -> p <= x < p + n -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -608) x)
by (intros p n x Hp Hx; right; right; left; exists p, n; split; [exact Hp| exact Hx]).
assert (CLF0 : forall x, f <= x < f + 56 -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -608) x)
by (intros x Hx; right; right; right; left; exists f, 0%nat; split; [exact INF| change (fs_size 0) with 64; lia]).
assert (CLSF : forall x, sf <= x < sf + 8 -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -608) x)
by (intros x Hx; right; right; right; right; exists f, 0%nat; split; [exact INF| change (fs_size 0) with 64; rewrite <- SHF, SHF0; lia]).
destruct (frame_live_apart RT AF Σx m11 fh kh PD ND ART11 INFHX INPDX) as (FLPD & _).
assert (SPD' : S + 160 <= PD \/ PD + ND <= S) by (clear - SPD; unfold hid in *; lia).
assert (SFH' : S + 160 <= fh \/ fh + fs_size kh <= S) by (clear - SFH; unfold hid in *; lia).
assert (SFA' : S + 160 <= f \/ f + 64 <= S) by (clear - SFA; unfold hid in *; lia).
assert (SFS' : S + 160 <= sf \/ sf + 8 <= S) by (clear - SFS SHF; unfold hid in *; subst sf; lia).
assert (FFA' : fh + fs_size kh <= f \/ f + 64 <= fh) by (clear - FFA; unfold hid in *; lia).
assert (FPHI2 : fh + fs_size kh <= SH_LO \/ SH_HI <= fh) by (clear - FPHI'; unfold hid, SH_LO, SH_HI in *; lia).
tr1 PRES13 WM13 STB ltac:(fun x Hx => apply CLF; clear - Hx FS1 FS2; lia)
ltac:(fun x Hx => apply OUTL13; [clear - Hx HOS'; unfold hid in *; lia | clear - Hx FS1 FS2 SFH'; lia | apply OTB; right; left; clear - Hx FS1 FS2; lia]).
tr1 PRES13 WM13 BOBJ8 ltac:(fun x Hx => apply CLF; clear - Hx FA1 FA2; lia)
ltac:(fun x Hx => apply OUTL13; [clear - Hx HAO'; unfold hid in *; lia | clear - Hx FA1 FA2 SFH'; lia | apply OTB; right; left; clear - Hx FA1 FA2; lia]).
tr1 PRES13 WM13 BDAT8 ltac:(fun x Hx => apply (CLL PD ND x INPDX); clear - Hx PD1 PD2 Lbs8; lia)
ltac:(fun x Hx => apply OUTL13; [clear - Hx PD1 PD2 Lbs8 FLPD FO1 FO2; lia | clear - Hx PD1 PD2 Lbs8 SPD'; lia | apply OTB; right; right; left; clear - Hx PD1 PD2 Lbs8; lia]).
tr1 PRES13 WM13 FR11 ltac:(fun x Hx => apply CLS; clear - Hx; lia)
ltac:(fun x Hx => apply OUTL13; [clear - Hx BF1 LO608 FO1 FO2; lia | clear - Hx BS1 LO608; lia | apply OTB; left; clear - Hx LO608; lia]).
tr1 PRES13 WM13 SV ltac:(fun x Hx => apply CLS; clear - Hx; lia)
ltac:(fun x Hx => apply OUTL13; [clear - Hx BF1 LO608 FO1 FO2; lia | clear - Hx BS1 LO608; lia | apply OTB; left; clear - Hx LO608; lia]).
tr1 PRES13 WM13 FRB ltac:(fun x Hx => apply CLF0; clear - Hx; lia)
ltac:(fun x Hx => apply OUTL13; [clear - Hx FFA' FO1 FO2; lia | clear - Hx SFA'; lia | apply OTB; right; right; right; left; clear - Hx; lia]).
tr1 PRES13 WM13 FRS ltac:(fun x Hx => apply CLSF; clear - Hx; lia)
ltac:(fun x Hx => apply OUTL13; [clear - Hx FPHI2 SHF1 SHF2 FO1 FO2; unfold SH_LO, SH_HI in *; lia | clear - Hx SFS'; lia | apply OTB; right; right; right; right; clear - Hx; lia]).
assert (AGL13 : agree_blocks asegs m11 m13 LBL).
{ apply (agree_blocks_of_pres_fp RT Σx _ _ _ m11 m13 _ PRES13 WM13); [exact LIVEL|].
intros bk x Hb Hx. pose proof (BOUT bk x ltac:(unfold LALL; apply in_app_iff; right; exact Hb) Hx) as H1.
destruct (frame_live_apart RT AF Σx m11 fh kh _ _ ART11 INFHX (LIVEL bk Hb)) as (FB & _).
apply OUTL13; [clear - H1 FB Hx FO1 FO2; lia | clear - H1; lia |]. apply outside_blocks_ivs. intros b2 Hb2 Hin.
assert (NE : blk_addr b2 <> blk_addr bk).
{ pose proof NDUP as ND'. rewrite ELBD, map_app in ND'. apply (NoDup_app_in_neq _ _ (blk_id b2) (blk_id bk) ND'); [apply in_map; cbn [sb_blocks tl] in Hb2 |- *; right; exact Hb2| apply in_map; exact Hb]. }
pose proof (live_apart RT AF Σx m11 _ _ _ _ ART11 (LIVEA b2 ltac:(unfold LALL; apply in_app_iff; left; exact Hb2)) (LIVEL bk Hb) NE) as AP.
clear - AP Hx Hin. lia. }
pk_blocks AGL13. clear AGL13.
assert (OIO13 : forall y, 65536 <= y < 6627328 -> outside ((OUT, OUT + 8000) :: blocks_ivs (sb_blocks sI S a)) y).
{ intros y Hy. apply OUTL13; [clear - Hy FO1 FPIMG; unfold SEGTOP_A in *; lia | clear - Hy SIMG; unfold SEGTOP_A in *; lia |].
apply outside_blocks_ivs. intros bk Hb Hin. pose proof (BOUT bk y ltac:(unfold LALL; apply in_app_iff; left; exact Hb) Hin) as H1. clear - H1 Hy. lia. }
pk_io_fp PRES13 ERR_rep OUT_rep IO_FP IO_img ltac:(fun y Hy => apply OIO13; exact Hy).
assert (SSP13 : io_ssp m13).
{ apply (sbd_io_ssp_agree m11 m13 SSP11 (AF_DRV Σl m13 ART13)). intros a0 Ha. apply PRES13; [right; left; exact (sbd_ssp_static _ Ha)|].
unfold X00a.SSP_GUARD in Ha. apply OIO13. lia. }
assert (SHW13 : forall o n, fh <= o -> o + n <= fh + fs_size kh -> forall i, 0 <= i < n -> outside ((OUT, OUT + 8000) :: blocks_ivs (sb_blocks sI S a)) (shad (o + i))).
{ intros o n H1 H2 i Hi.
assert (SR : SH_LO <= shad (o + i) < SH_HI).
{ pose proof (frame_facts RT AF Σx m11 fh kh ART11 INFHX) as (_ & _ & _ & _ & _ & _ & SA & SL & SH & _). split.
- unfold shad, SH_LO, SHB in *. assert (0 <= (o + i) / 8) by (apply Z.div_pos; lia). lia.
- assert (shad (o + i) < shad (fh + fs_size kh)); [| lia].
unfold shad. apply Z.add_lt_mono_r. apply Z.div_lt_upper_bound; [lia|].
assert (FH8 : fh mod 8 = 0) by (clear - FP64; Z.div_mod_to_equations; lia).
assert (FK8 : fs_size kh mod 8 = 0) by (destruct FS64 as (M64 & _); clear - M64; Z.div_mod_to_equations; lia).
assert (E : fh + fs_size kh = 8 * ((fh + fs_size kh) / 8)).
{ pose proof (Z.div_mod (fh + fs_size kh) 8 ltac:(lia)) as XD. rewrite Zplus_mod, FH8, FK8 in XD. cbn in XD. lia. }
lia. }
cbn [outside]. split; [clear - SR FPHI2 FO1 FO2; unfold SH_LO, SH_HI in *; lia|].
exact (outside_blocks_shadow RT AF Σx m11 (sb_blocks sI S a) _ ART11 ltac:(intros bk Hb; apply LIVED; rewrite ELBD; apply in_app_iff; left; exact Hb) SR). }
assert (FH8 : fh mod 8 = 0) by (clear - FP64; Z.div_mod_to_equations; lia).
assert (FK8 : fs_size kh mod 8 = 0) by (destruct FS64 as (M64 & _); clear - M64; Z.div_mod_to_equations; lia).
assert (ACA13 : acc asegs m13 A 48)
by (apply (acc_pres_fp_frame _ _ _ _ m11 m13 fh kh A 48 PRES13 INFHX FH8 FK8 ltac:(lia) FA1 ltac:(lia) (SHW13 A 48 FA1 ltac:(lia)) ACA11)).
assert (ACT13 : acc asegs m13 STEREO 24)
by (apply (acc_pres_fp_frame _ _ _ _ m11 m13 fh kh STEREO 24 PRES13 INFHX FH8 FK8 ltac:(lia) FS1 ltac:(lia) (SHW13 STEREO 24 FS1 ltac:(lia)) ACT11)).
assert (PF13 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m13).
{ apply (pres_fp_trans _ _ _ _ m m11 m13 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σx) (rt_frames RT Σx) (usp + -608) _ m11 m13 PRES13).
- intros e He. rewrite ELX. exact He.
- intros e He. rewrite EFX. right. exact He.
- clear; lia.
- intros x Hx Ho. cbn [outside] in Ho. destruct Ho as (_ & HO & _ & Ho). apply sb_outside_app_inv in Ho. destruct Ho as [Hb _].
rewrite ELBD1 in Hb. cbn [outside]. split; [exact HO| exact (outside_blocks_app_l _ _ x Hb)]. }
clear PF PRES13 ACA11 ACT11 SSP11 SHW13. rename PF13 into PF.
clear Hc0.

cps_seg (sbd_n3 usp S OUT f (sbmode_struct (sbd_mode s)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
subst ms.
assert (EFl : rt_frames RT Σl = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRl; exact EFX).
assert (ELl : rt_live RT Σl = rt_live RT Σ) by (rewrite LVl; exact ELX).
assert (ESl : rt_sp0 RT Σl = rt_sp0 RT Σ) by (rewrite SPl; exact ESX).
assert (EPl : rt_pois RT Σl = rt_pois RT Σ) by (rewrite POl; exact EPX).
assert (INV13 : sb_inv (set_sbd_first sI 1)).
{ destruct INV1 as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12). unfold sb_inv. cbn [set_sbd_first sbd_mode sbd_frame_size sbd_full_frame_size
sbd_subframeSize sbd_nbSubframes sbd_lpcSize sbd_first sbd_sampling_rate sbd_lpc_enh_enabled sbd_encode_submode sbd_submodeID sbd_innov_save].
refine (conj I1 (conj I2 (conj I3 (conj I4 (conj I5 (conj I6 (conj (or_intror eq_refl) (conj I8 (conj I9 (conj I10 (conj I11 I12))))))))))). }
assert (REPX : DREP OUT STEREO m13 S (DecSB (set_sbd_first sI 1) low3) LBD).
{ cbn [decst_rep]. exists a, j', LBL. split; [exact ELBD1|]. split; [exact S8|]. split; [exact SPOS|]. split; [exact INV13|]. split; [exact JOK13|].
split; [exact X13|]. split; [exact BUFS13|]. exists OUT. exact RLOW. }
assert (BREPX : bits_rep asegs m13 A D (sbw_bits b1)).
{ split; [exists rj8; split; [exact Lrj8| unfold bits_cells; exact BOBJ8]|].
split; [exists bs8; split; [apply (proj2 (u8arr_rw_CB m13 D bs8)); exact BDAT8| exact Hbs8]| exact BSIDE8]. }
assert (PD2X : D + sb_buf_size (sbw_bits b1) <= PD + ND) by (rewrite BSZ8; exact PD2).
assert (WMX : wmono asegs m m13) by (eapply wmono_trans; [exact WM0|]; eapply wmono_trans; [exact WM8|]; eapply wmono_trans; [exact WM9|];
eapply wmono_trans; [exact WM11| exact WM13]).
cps_rt (sbd_exit_cps RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AUN_lo AUN_nop Σ Σl F0 fs0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m m13 lo S OUT STEREO A D f fh PD ND kh LBD
(fupds (fupds g [(44%nat, Z_to_bv 64 (S + 144)); (43%nat, Z_to_bv 64 (S + 152))]) [(42%nat, Z_to_bv 64 (Z.shiftr (S + 144) 3 + SHB)); (41%nat, Z_to_bv 64 (Z.shiftr (S + 152) 3 + SHB))])
0 0 (DecSB (set_sbd_first sI 1) low3) (sbw_bits b1) ows' stb j24 j36 (Z_to_bv 64 dtx)
EFl ELl ESl EPl ART0 POA NAF LIVE INPD PD1 PD2X INFH FA1 FA2 ACA FO1 FO2 ACO FS1 FS2 ACST ART13 MI13 RSl ST13 LOW
ltac:(clear - LOR DSP; unfold RT_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia) SPT SPA PF WMX FR11
ltac:(cbn [fupds Nat.eqb]; exact G13) ltac:(cbn [fupds Nat.eqb]; exact G52)
(or_introl eq_refl) SV FRB FRS REPX (fun _ => I) BREPX BOK8 OC13 LOWS13 STB ERRX OUTK).
intros c' (Σ' & Hc' & E1 & E2 & E3 & E4 & E5).
apply Hk. exists Σ'. split; [exact Hc'|].
pose proof (bkeep_sbw b1) as (K1 & K2 & K3).
cbn [dec_depth dec_mode dec_nestedR dec_credit sI set_sbd_submodeID set_sbd_first sbd_mode].
split; [clear; lia|]. split; [rewrite DL3; reflexivity|]. split; [reflexivity|]. split; [split; [exact NM3| exact NEST3]|].
split; [rewrite K2; exact OWN1|]. split; [rewrite K1; exact CHR1|]. split; [rewrite K3; exact BSZ1|].
split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [| exact E5].
rewrite E4, CRl. pose proof (dec_depth_pos low) as DP. clear - CBX DP. lia. }

set (fsz := sbd_frame_size s) in *.
set (Y := OUT + 4 * fsz).
assert (FSN : (Z.of_nat (Z.to_nat fsz) = fsz)%Z) by (clear - FSV; lia).
apply (f32_split asegs m11 OUT ows (Z.to_nat fsz)) in OC; [| rewrite LOWS; clear - FSV; lia].
destruct OC as (OCa & OCb). rewrite FSN in OCb.
apply (f32_split asegs m11 (OUT + 4 * fsz) (skipn (Z.to_nat fsz) ows) (Z.to_nat fsz)) in OCb; [| rewrite length_skipn, LOWS; clear - FSV; lia].
destruct OCb as (OCy & OCc). rewrite FSN in OCc. fold Y in OCy.
assert (LYW : length (firstn (Z.to_nat fsz) (skipn (Z.to_nat fsz) ows)) = Z.to_nat fsz)
by (rewrite length_firstn, length_skipn, LOWS; clear - FSV; lia).
destruct (firstn (Z.to_nat fsz) (skipn (Z.to_nat fsz) ows)) as [|cw rest] eqn:EYW; [cbn [length] in LYW; clear - LYW FSV; lia|].
assert (LREST : Z.of_nat (length rest) + 1 = fsz) by (cbn [length] in LYW; clear - LYW FSV; lia).
assert (OBY : aobj asegs m11 Y (4 * fsz)).
{ split; [unfold Y; clear - FO1 FP0 FSV; lia|]. split; [unfold Y; clear - FO2 BF1 LO608 SPT FSV; unfold APP_TOP; lia|].
apply (acc_sub asegs m11 OUT 8000 Y (4 * fsz) ACO11); unfold Y; clear - FSV; lia. }
sb_unpack X9 as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_n4 usp S OUT f (sbmode_struct (sbd_mode s)) fsz Y
(fupds (fupds g [(44%nat, Z_to_bv 64 (S + 144)); (43%nat, Z_to_bv 64 (S + 152))]) [(42%nat, Z_to_bv 64 (Z.shiftr (S + 144) 3 + SHB)); (41%nat, Z_to_bv 64 (Z.shiftr (S + 152) 3 + SHB))])
(Z_to_bv 64 0) (Z_to_bv 64 (sbd_first sI)) sI a cw rest _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
FR11 ltac:(cbn [fupds Nat.eqb]; exact G27) ltac:(cbn [fupds Nat.eqb]; exact G26) ltac:(cbn [fupds Nat.eqb]; exact G45)
HD FST PT eq_refl ILPC ltac:(clear - FSV; lia) LREST OBS11 S8 SPOS SLO8 SOFF SIMG eq_refl OCy OBY
ltac:(unfold Y; clear - OAL; Z.div_mod_to_equations; lia) ltac:(unfold Y, IMG_TOP; clear - FPIMG FO1 FSV; unfold SEGTOP_A in *; lia)
ltac:(unfold Y; clear - FPHI' FO1 FO2 FSV; unfold hid, SH_LO, SH_HI in *; lia)
ltac:(unfold Y; clear - SFH FO1 FO2 FSV; unfold hid in *; lia) ltac:(unfold Y; clear - FO2 BF1 LO608 FSV; lia) SHL SPH MI11).
destruct POST as (m14 & xa7s & ys' & -> & MU14 & WM14 & MI14 & FST14 & YS14 & LYS14).
clear X9 OCy FST.
assert (OUTSB : forall x, outside (blocks_ivs LBD) x -> ~ (S <= x < S + 160)).
{ intros x Ho. rewrite ELBD in Ho. cbn [sb_blocks app blocks_ivs map outside blk_addr blk_size fst snd] in Ho. destruct Ho as [Ho _]. unfold SBSTATE_SIZEOF in Ho. exact Ho. }
assert (ART14 : X0ec.ART RT Σx m14).
{ apply (af_frame RT AF Σx m11 m14 lo ART11 LOWX); [| exact WM14]. intros a0 Ha. apply MU14. cbn [outside]. split; [| split; [| exact I]].
- intros Hin. apply Ha. right; right; left. exists S, 160. split; [exact INLX | clear - Hin; lia].
- intros Hin. apply Ha. right; right; right; left. exists fh, kh. split; [exact INFHX | unfold Y in Hin; clear - Hin FO1 FO2 FSV; lia]. }
assert (PF14 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m14).
{ apply (pres_fp_trans _ _ _ _ m m11 m14 PF). apply (pres_fp_of_munch _ _ _ _ _ m11 m14 MU14). intros x Hx Ho. cbn [outside] in Ho |- *.
destruct Ho as (_ & HO & _ & Ho). apply sb_outside_app_inv in Ho. destruct Ho as [Hb _].
split; [intros Hin; apply (OUTSB x Hb); clear - Hin; lia|]. split; [intros Hin; apply HO; unfold Y in Hin; clear - Hin FSV; lia| exact I]. }
clear PF. rename PF14 into PF.
pk_munch_all MU14 WM14 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1;
destruct (frame_live_apart RT AF Σx m11 fh kh _ _ ART11 INFHX (LIVEA b Hb)) as (FB & _);
clear - H1 FB Hx FO1 FO2 FSV; unfold Y; cbn [outside]; split; [lia| split; [lia| exact I]])
ltac:(fun x Hx => clear - Hx SIMG FO1 FPIMG FSV; unfold Y, SEGTOP_A in *; cbn [outside]; split; [lia| split; [lia| exact I]]).
destruct (frame_live_apart RT AF Σx m11 fh kh PD ND ART11 INFHX INPDX) as (FLPD & _).
assert (SPD' : S + 160 <= PD \/ PD + ND <= S) by (clear - SPD; unfold hid in *; lia).
assert (SFH' : S + 160 <= fh \/ fh + fs_size kh <= S) by (clear - SFH; unfold hid in *; lia).
assert (SFA' : S + 160 <= f \/ f + 64 <= S) by (clear - SFA; unfold hid in *; lia).
assert (SFS' : S + 160 <= sf \/ sf + 8 <= S) by (clear - SFS SHF; unfold hid in *; subst sf; lia).
assert (FFA' : fh + fs_size kh <= f \/ f + 64 <= fh) by (clear - FFA; unfold hid in *; lia).
assert (FPHI2 : fh + fs_size kh <= SH_LO \/ SH_HI <= fh) by (clear - FPHI'; unfold hid, SH_LO, SH_HI in *; lia).
assert (YR : OUT <= Y /\ Y + 4 * fsz <= OUT + 8000) by (unfold Y; clear - FSV; lia).
Ltac trm MU WM H tacD :=
lazymatch type of MU with
| munch ?W ?m ?m' =>
lazymatch type of H with
| rw_cells asegs m ?A0 ?cs =>
let H' := fresh "T" in
assert (H' : rw_cells asegs m' A0 cs)
by (apply (rw_cells_transport asegs W m m' A0 cs H MU WM); cbn [disjoint_from]; simpl_sizes; tacD);
clear H; rename H' into H
end
end.
set (wa := firstn (Z.to_nat fsz) ows) in OCa. set (wc := skipn (Z.to_nat fsz) (skipn (Z.to_nat fsz) ows)) in OCc.
assert (LWA : Z.of_nat (length wa) = fsz) by (unfold wa; rewrite length_firstn, LOWS; clear - FSV; lia).
assert (LWC : Z.of_nat (length wc) = 2000 - 2 * fsz) by (unfold wc; rewrite !length_skipn, LOWS; clear - FSV; lia).
trm MU14 WM14 OCa ltac:(unfold Y; clear - LWA SFH' FO1 FO2 FSV; lia).
trm MU14 WM14 OCc ltac:(unfold Y; clear - LWC SFH' FO1 FO2 FSV; lia).
trm MU14 WM14 SV ltac:(unfold Y; clear - BS1 LO608 FO2 BF1 FSV; lia).
trm MU14 WM14 FR11 ltac:(unfold Y; clear - BS1 LO608 FO2 BF1 FSV; lia).
trm MU14 WM14 FRB ltac:(unfold Y; clear - SFA' FFA' FO1 FO2 FSV; lia).
trm MU14 WM14 FRS ltac:(unfold Y; clear - SFS' FPHI2 SHF1 SHF2 FO1 FO2 FSV; unfold SH_LO, SH_HI in *; lia).
trm MU14 WM14 STB ltac:(unfold Y; clear - SFH' HOS' FS1 FS2 FO1 FO2 FSV; unfold hid in *; lia).
trm MU14 WM14 BOBJ8 ltac:(unfold Y; clear - SFH' HAO' FA1 FA2 FO1 FO2 FSV; unfold hid in *; lia).
trm MU14 WM14 BDAT8 ltac:(unfold Y; clear - SPD' FLPD PD1 PD2 Lbs8 FO1 FO2 FSV; lia).
trm MU14 WM14 HD ltac:(unfold Y; clear - SFH' FO1 FO2 FSV; lia).
trm MU14 WM14 PT ltac:(unfold Y; clear - SFH' FO1 FO2 FSV; lia).
trm MU14 WM14 LE ltac:(unfold Y; clear - SFH' FO1 FO2 FSV; lia).
trm MU14 WM14 SEED ltac:(unfold Y; clear - SFH' FO1 FO2 FSV; lia).
trm MU14 WM14 CFG ltac:(unfold Y; clear - SFH' FO1 FO2 FSV; lia).
trm MU14 WM14 IDC ltac:(unfold Y; clear - SFH' FO1 FO2 FSV; lia).
trm MU14 WM14 PAD ltac:(unfold Y; clear - SFH' FO1 FO2 FSV; lia).
apply (stk_transport_disjoint asegs [(S + 36, S + 40); (Y, Y + 4 * fsz)] m11 m14 lo (usp + -608)) in ST8; [| exact MU14 | exact WM14 | cbn [disjoint_from]; unfold Y; clear - BS1 FO2 BF1 FSV; lia].
clear ART11.
cps_hide.

assert (OF14 : offsh [(S + 36, S + 40); (Y, Y + 4 * fsz)]) by (cbn [offsh]; unfold Y; clear - SOFF FPHI2 FO1 FO2 FSV; try unfold hid in *; unfold hid, SH_LO, SH_HI in *; lia).
assert (ACC14 : forall o n, acc asegs m11 o n -> 0 <= o -> o + n <= 140737488355328 -> acc asegs m14 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch asegs _ m11 m14 o n (conj H0 (conj H1 H)) MU14 (shfree_of_offsh _ o n OF14 H0 H1)))). }
assert (ACA14 : acc asegs m14 A 48) by (apply ACC14; [exact ACA11| clear - FA1 FP0; try unfold hid in *; lia| clear - FA2 BF1 LO608 SPT; try unfold hid in *; lia]).
assert (ACO14 : acc asegs m14 OUT 8000) by (apply ACC14; [exact ACO11| clear - FO1 FP0; try unfold hid in *; lia| clear - FO2 BF1 LO608 SPT; try unfold hid in *; lia]).
assert (ACT14 : acc asegs m14 STEREO 24) by (apply ACC14; [exact ACT11| clear - FS1 FP0; try unfold hid in *; lia| clear - FS2 BF1 LO608 SPT; try unfold hid in *; lia]).
assert (SSP14 : io_ssp m14).
{ apply (sbd_io_ssp_agree m11 m14 SSP11 (AF_DRV Σx m14 ART14)). intros a0 Ha. apply MU14. unfold X00a.SSP_GUARD in Ha. cbn [outside].
unfold Y. clear - Ha SIMG FO1 FPIMG FSV. unfold SEGTOP_A in *. split; [lia| split; [lia| exact I]]. }
clear ACA11 ACO11 ACT11 SSP11 ACC14 OBS11 ACS11 OBY.

destruct BUFS as (G0C & G1C & EXC & OQC & IQC & MSPC & PGC & ERC).
pose proof JOK as (JP1 & JP2 & JG0 & JG1 & JEXC & JOQ & JIQ & JMSP & JPG & JER).
apply (f32_split asegs m14 (a_msp a) (sj_msp j) 8) in MSPC; [| rewrite JMSP; clear; lia]. destruct MSPC as (MSP1 & MSP2).
assert (LMEM : length (firstn 8 (sj_msp j)) = length (sj_iq j)) by (rewrite length_firstn, JMSP, JIQ; reflexivity).
assert (INIQ : In (a_iq a, 32) (rt_live RT Σx)) by (apply (LIVED (sbd_interp_qlpc s, a_iq a, 32)); rewrite ELBD; apply in_app_iff; left; cbn [sb_blocks In]; do 5 right; left; reflexivity).
assert (INMSP : In (a_msp a, 64) (rt_live RT Σx)) by (apply (LIVED (sbd_mem_sp s, a_msp a, 64)); rewrite ELBD; apply in_app_iff; left; cbn [sb_blocks In]; do 8 right; left; reflexivity).
destruct (af_acc_live RT AF Σx m14 _ _ ART14 INIQ) as (_ & ACIQ). destruct (af_acc_live RT AF Σx m14 _ _ ART14 INMSP) as (_ & ACMSP).
destruct (live_below_lo RT AF Σx m14 _ _ lo ART14 INIQ LOWX) as (IQP & IQLO & _). destruct (live_below_lo RT AF Σx m14 _ _ lo ART14 INMSP LOWX) as (MSPP & MSPLO & _).
pose proof (live_facts RT AF Σx m14 _ _ ART14 INIQ) as (_ & _ & _ & IQSH). pose proof (live_facts RT AF Σx m14 _ _ ART14 INMSP) as (_ & _ & _ & MSPSH).
pose proof (af_live_small RT AF Σx m14 _ _ ART14 INMSP ltac:(clear; lia)) as MSPIMG.
destruct (frame_live_apart RT AF Σx m14 fh kh _ _ ART14 INFHX INIQ) as (FIQ & _). destruct (frame_live_apart RT AF Σx m14 fh kh _ _ ART14 INFHX INMSP) as (FMSP & _).
assert (NEIM : a_iq a <> a_msp a).
{ intros E. pose proof NDUP as ND'. rewrite ELBD, map_app in ND'. apply List.NoDup_app_remove_r in ND'.
cbn [sb_blocks map blk_id blk_addr fst snd] in ND'.
do 5 (apply List.NoDup_cons_iff in ND'; destruct ND' as [_ ND']).
apply List.NoDup_cons_iff in ND'. destruct ND' as [NI _]. apply NI. rewrite E. cbn [In]. right; right; left; reflexivity. }
pose proof (live_apart RT AF Σx m14 _ _ _ _ ART14 INIQ INMSP NEIM) as IQMSP.
assert (AL8a : sb_addrs_al a) by (apply (sb_addrs_al_of_blocks s S a); intros bk Hb; apply LAL8; rewrite ELBD; apply in_app_iff; left; exact Hb).
assert (LYS' : 1 <= Z.of_nat (length ys') < 2^31) by (rewrite LYS14; clear - FSV; try unfold hid in *; lia).
assert (ORD8 : 2 <= Z.of_nat (length (sj_iq j)) < 2^31) by (rewrite JIQ; cbn; lia).
assert (OBX14 : aobj asegs m14 Y (4 * Z.of_nat (length ys'))).
{ rewrite LYS14. split; [unfold Y; clear - FO1 FP0 FSV; try unfold hid in *; lia|]. split; [unfold Y; clear - FO2 BF1 LO608 SPT FSV; try unfold hid in *; unfold APP_TOP; lia|].
apply (acc_sub asegs m14 OUT 8000 Y (4 * fsz) ACO14); unfold Y; clear - FSV; try unfold hid in *; lia. }
assert (OBD14 : aobj asegs m14 (a_iq a) (4 * Z.of_nat (length (sj_iq j)))) by (rewrite JIQ; split; [lia|]; split; [clear - IQLO LO608 SPT; try unfold hid in *; unfold APP_TOP; cbn; lia| exact ACIQ]).
assert (OBM14 : aobj asegs m14 (a_msp a) (4 * Z.of_nat (length (sj_iq j))))
by (rewrite JIQ; split; [lia|]; split; [clear - MSPLO LO608 SPT; try unfold hid in *; unfold APP_TOP; cbn; lia| exact (acc_sub asegs m14 (a_msp a) 64 (a_msp a) 32 ACMSP ltac:(clear; lia) ltac:(clear; lia))]).
destruct AL8a as (_ & _ & _ & _ & IQ8 & MSP8 & _).
rewrite <- LYS14 in Hc.
replace (Z_to_bv 64 8) with (Z_to_bv 64 (Z.of_nat (length (sj_iq j)))) in Hc by (rewrite JIQ; reflexivity).
pose proof (af_client_consts RT AF Σx m14 ART14) as CC14.
assert (X4 : Y mod 4 = 0) by (unfold Y; clear - OAL; Z.div_mod_to_equations; lia).
assert (D4 : a_iq a mod 4 = 0) by (clear - IQ8; Z.div_mod_to_equations; lia).
assert (M4 : a_msp a mod 4 = 0) by (clear - MSP8; Z.div_mod_to_equations; lia).
assert (LO80 : lo <= usp + -608 - 80) by (clear - LO608 LOR DSP; unfold RT_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
assert (SPH6 : usp + -608 < 2 ^ 63) by (clear - SPT; lia).
assert (XSH14 : Y + 4 * Z.of_nat (length ys') <= SH_LO \/ SH_HI <= Y) by (rewrite LYS14; unfold Y; clear - FPHI2 FO1 FO2 FSV; unfold hid, SH_LO, SH_HI in *; lia).
assert (MSH14 : a_msp a + 4 * Z.of_nat (length (sj_iq j)) <= SH_LO \/ SH_HI <= a_msp a) by (rewrite JIQ; clear - MSPSH; unfold SH_LO, SH_HI in *; cbn; lia).
assert (XAP14 : Y + 4 * Z.of_nat (length ys') <= lo \/ usp + -608 <= Y) by (rewrite LYS14; unfold Y; left; clear - FO2 BF1 FSV; unfold hid in *; lia).
assert (MAP14 : a_msp a + 4 * Z.of_nat (length (sj_iq j)) <= lo \/ usp + -608 <= a_msp a) by (rewrite JIQ; left; clear - MSPLO; cbn; lia).
assert (DAP14 : a_iq a + 4 * Z.of_nat (length (sj_iq j)) <= lo \/ usp + -608 <= a_iq a) by (rewrite JIQ; left; clear - IQLO; cbn; lia).
assert (SEPDM14 : a_iq a + 4 * Z.of_nat (length (sj_iq j)) <= a_msp a \/ a_msp a + 4 * Z.of_nat (length (sj_iq j)) <= a_iq a) by (rewrite JIQ; clear - IQMSP; cbn; lia).
assert (SEPXM14 : Y + 4 * Z.of_nat (length ys') <= a_msp a \/ a_msp a + 4 * Z.of_nat (length (sj_iq j)) <= Y) by (rewrite LYS14, JIQ; unfold Y; clear - FMSP FO1 FO2 FSV; unfold hid in *; cbn; lia).
assert (SEPXD14 : Y + 4 * Z.of_nat (length ys') <= a_iq a \/ a_iq a + 4 * Z.of_nat (length (sj_iq j)) <= Y) by (rewrite LYS14, JIQ; unfold Y; clear - FIQ FO1 FO2 FSV; unfold hid in *; cbn; lia).
assert (PTOP : IMG_TOP <= Y) by (unfold Y, IMG_TOP; clear - FPIMG FO1 FSV; unfold hid, SEGTOP_A in *; lia).
assert (MTOP : IMG_TOP <= a_msp a) by (unfold IMG_TOP; clear - MSPIMG; unfold SEGTOP_A in *; lia).
Time cps_seg (iir_mem16_walk_ip ys' (sj_iq j) (firstn 8 (sj_msp j)) Y (a_iq a) (a_msp a) (usp + -608) lo
(Z_to_bv 64 RA_sbd_iir_n) gp (Z_to_bv 64 0x630458) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -608)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 A)
(Z_to_bv 64 (Z.shiftr (S + 8) 3 + SHB)) (Z_to_bv 64 f) (Z_to_bv 64 (sbmode_struct (sbd_mode s))) (Z_to_bv 64 f) (Z_to_bv 64 SHB) (Z_to_bv 64 OUT) (Z_to_bv 64 S)
m14 LMEM LYS' ORD8 OBX14 OBD14 OBM14 X4 D4 M4 LO80 LOS SPH6 XSH14 MSH14 XAP14 MAP14 DAP14 SEPDM14 SEPXM14 SEPXD14
_ _ _ _ _ _ _ _ _ _ _ YS14 IQC MSP1 FRMX ST8 PTOP MTOP CC14 MI14).
destruct POST as (t0i & t1i & t2i & a0i & a1i & a2i & a3i & a4i & a5i & a6i & a7i & t3i & t4i & t5i & t6i & Fi & fci & m15 & ysi & mvi
& -> & MU15 & WM15 & MI15 & ST15 & FRM15 & LYSI & YSI & LMVI & MVI & IQI & _).
clear YS14 MSP1 IQC ST8.

set (sF := set_sbd_first sI 1).
assert (X14 : rw_cells asegs m14 S (SBCELLS sF a OUT j)).
{ apply sb_pieces_iff. exact (conj HD (conj FST14 (conj PT (conj LE (conj SEED (conj CFG (conj IDC PAD))))))). }
clear HD FST14 PT LE SEED CFG IDC PAD.

set (LNM := firstn 8 (sb_blocks sI S a) ++ LBL).
assert (ELNM : LBD = firstn 8 (sb_blocks sI S a) ++ (sbd_mem_sp s, a_msp a, 64) :: LBL) by (rewrite ELBD1; reflexivity).
assert (LIVNM : forall bk, In bk LNM -> In (blk_addr bk, blk_size bk) (rt_live RT Σx)).
{ intros bk Hb. apply LIVED. rewrite ELNM. apply in_app_iff. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [left; exact Hb| right; right; exact Hb]. }
assert (NMSP : forall bk, In bk LNM -> blk_addr bk <> a_msp a).
{ intros bk Hb E. pose proof NDUP as ND'. rewrite ELNM, map_app in ND'. cbn [map] in ND'. apply List.NoDup_remove_2 in ND'.
apply ND'. rewrite <- map_app. change (blk_id (sbd_mem_sp s, a_msp a, 64)) with (a_msp a). rewrite <- E. exact (in_map blk_id LNM bk Hb). }
assert (AG15 : agree_blocks asegs m14 m15 LNM).
{ apply (agree_blocks_of_munch asegs _ m14 m15 LNM MU15 WM15). intros bk x Hb Hx.
pose proof (LIVNM bk Hb) as LB.
destruct (frame_live_apart RT AF Σx m14 fh kh _ _ ART14 INFHX LB) as (FB & _).
destruct (live_below_lo RT AF Σx m14 _ _ lo ART14 LB LOWX) as (_ & BL & _).
pose proof (live_apart RT AF Σx m14 _ _ _ _ ART14 LB INMSP (NMSP bk Hb)) as AMS.
rewrite JIQ, LYS14. cbn [outside]. unfold Y. clear - FB BL AMS Hx FO1 FO2 FSV LO80. unfold hid in *.
split; [lia| split; [lia| split; [lia| exact I]]]. }
Ltac tra AG H bk tacR :=
lazymatch type of AG with
| agree_blocks _ ?m ?m' ?L =>
lazymatch type of H with
| rw_cells _ m ?A0 ?cs =>
let H' := fresh "T" in
assert (H' : rw_cells asegs m' A0 cs)
by (apply (rw_cells_agree_at asegs m m' A0 cs H); apply (agree_blocks_at asegs m m' L bk A0 cs AG);
[ apply in_app_iff; left; cbn [sb_blocks firstn skipn In]; repeat (first [left; reflexivity | right]) | exact H | unfold blk_addr, blk_size; cbn [fst snd]; simpl_sizes; tacR | unfold blk_addr, blk_size; cbn [fst snd]; simpl_sizes; tacR ]);
clear H; rename H' into H
end
end.
unfold LNM in AG15.
tra AG15 X14 (sbd_blk sI, S, SBSTATE_SIZEOF) ltac:(unfold SBSTATE_SIZEOF; clear; lia).
tra AG15 G0C (sbd_g0_mem sI, a_g0 a, 256) ltac:(clear - JG0; lia).
tra AG15 G1C (sbd_g1_mem sI, a_g1 a, 256) ltac:(clear - JG1; lia).
tra AG15 EXC (sbd_excBuf sI, a_exc a, 4 * sbd_subframeSize sI) ltac:(cbn [sI set_sbd_submodeID sbd_subframeSize]; clear - JEXC; lia).
tra AG15 OQC (sbd_old_qlsp sI, a_oq a, 32) ltac:(clear - JOQ; lia).
tra AG15 PGC (sbd_pi_gain sI, a_pg a, 16) ltac:(clear - JPG; lia).
tra AG15 ERC (sbd_exc_rms sI, a_er a, 16) ltac:(clear - JER; lia).
assert (AGL15 : agree_blocks asegs m14 m15 LBL) by (apply (agree_blocks_sub asegs _ _ _ _ AG15); intros bk Hb; apply in_app_iff; right; exact Hb).
pk_blocks AGL15. clear AGL15 AG15.
destruct (frame_live_apart RT AF Σx m14 f 0%nat _ _ ART14 INF INMSP) as (FMSPf & _). change (fs_size 0) with 64 in FMSPf.
assert (PDMN : PD <> a_msp a) by (intros E; apply (PDB (sbd_mem_sp s, a_msp a, 64)); [rewrite ELBD; apply in_app_iff; left; cbn [sb_blocks In]; do 8 right; left; reflexivity| exact (eq_sym E)]).
pose proof (live_apart RT AF Σx m14 _ _ _ _ ART14 INPDX INMSP PDMN) as PDMSP.
trm MU15 WM15 OCa ltac:(rewrite LYS14, JIQ; unfold Y; cbn; clear - LWA FMSP FO1 FO2 BF1 LO80 FSV; unfold hid in *; lia).
trm MU15 WM15 OCc ltac:(rewrite LYS14, JIQ; unfold Y; cbn; clear - LWC FMSP FO1 FO2 BF1 LO80 FSV; unfold hid in *; lia).
trm MU15 WM15 SV ltac:(rewrite LYS14, JIQ; unfold Y; cbn; clear - BF1 FO2 MSPLO LO80 LO608 FSV; unfold hid in *; lia).
trm MU15 WM15 FR11 ltac:(rewrite LYS14, JIQ; unfold Y; cbn; clear - BF1 FO2 MSPLO LO80 LO608 FSV; unfold hid in *; lia).
trm MU15 WM15 FRB ltac:(rewrite LYS14, JIQ; unfold Y; cbn; clear - FFA' FO1 FO2 FMSPf BF LO80 FSV; unfold hid in *; lia).
trm MU15 WM15 FRS ltac:(rewrite LYS14, JIQ; unfold Y; cbn; clear - FPHI2 SHF1 SHF2 FO1 FO2 MSPSH BF0 LO80 FSV; unfold hid, SH_LO, SH_HI in *; lia).
trm MU15 WM15 STB ltac:(rewrite LYS14, JIQ; unfold Y; cbn; clear - HOS' FO1 FO2 FS1 FS2 FMSP BF1 LO80 FSV; unfold hid, hidp in *; lia).
trm MU15 WM15 BOBJ8 ltac:(rewrite LYS14, JIQ; unfold Y; cbn; clear - HAO' FO1 FO2 FA1 FA2 FMSP BF1 LO80 FSV; unfold hid, hidp in *; lia).
trm MU15 WM15 BDAT8 ltac:(rewrite LYS14, JIQ; unfold Y; cbn; clear - FLPD PD1 PD2 Lbs8 FO1 FO2 PDMSP BLPD LO80 FSV; unfold hid in *; lia).
trm MU15 WM15 MSP2 ltac:(rewrite LYS14, JIQ; unfold Y; cbn; rewrite length_skipn, JMSP; cbn; clear - FMSP FO1 FO2 MSPLO LO80 FSV; unfold hid in *; lia).

set (j2 := SBJ (sj_last_ener j) (sj_seed j) (sj_pad1 j) (sj_pad2 j) (sj_g0 j) (sj_g1 j) (sj_exc j) (sj_oq j) (sj_iq j) (mvi ++ skipn 8 (sj_msp j)) (sj_pg j) (sj_er j)).
assert (MSPX : rw_cells asegs m15 (a_msp a) (f32 (mvi ++ skipn 8 (sj_msp j)))).
{ apply f32_join; [exact MVI|]. rewrite LMVI, JIQ. exact MSP2. }
assert (BUFS15 : sb_bufs asegs m15 a j2) by (exact (conj G0C (conj G1C (conj EXC (conj OQC (conj IQI (conj MSPX (conj PGC ERC)))))))).
assert (JOK2 : sb_junk_ok sF j2).
{ unfold sb_junk_ok. repeat split; cbn [j2 sj_pad1 sj_pad2 sj_g0 sj_g1 sj_exc sj_oq sj_iq sj_msp sj_pg sj_er];
first [ assumption
| rewrite length_app, length_skipn, LMVI, JIQ, JMSP; reflexivity
| unfold sF, sI; cbn [set_sbd_first set_sbd_submodeID sbd_subframeSize]; exact JEXC ]. }
assert (X15 : rw_cells asegs m15 S (SBCELLS sF a OUT j2)) by (exact X14).
clear G0C G1C EXC OQC IQI MSPX MVI MSP2 PGC ERC X14.

assert (ART15 : X0ec.ART RT Σx m15).
{ apply (af_frame RT AF Σx m14 m15 lo ART14 LOWX); [| exact WM15]. intros a0 Ha. apply MU15. rewrite LYS14, JIQ. cbn [outside]. unfold Y.
split; [| split; [| split; [| exact I]]].
- intros Hin. apply Ha. right; right; right; left. exists fh, kh. split; [exact INFHX | clear - Hin FO1 FO2 FSV; unfold hid in *; lia].
- intros Hin. apply Ha. right; right; left. exists (a_msp a), 64. split; [exact INMSP | clear - Hin; lia].
- intros Hin. apply Ha. left. clear - Hin LO80 SPT; unfold USTACK_TOP in *; lia. }
assert (PF15 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m15).
{ apply (pres_fp_trans _ _ _ _ m m14 m15 PF). apply (pres_fp_of_munch _ _ _ _ _ m14 m15 MU15). intros x Hx Ho. rewrite LYS14, JIQ. cbn [outside] in Ho |- *.
destruct Ho as (_ & HO & _ & Ho). apply sb_outside_app_inv in Ho. destruct Ho as [Hb _].
assert (HM : ~ (a_msp a <= x < a_msp a + 64)).
{ rewrite ELNM in Hb. apply outside_blocks_app_r in Hb. cbn [blocks_ivs map outside blk_addr blk_size fst snd] in Hb. exact (proj1 Hb). }
pose proof (SPL x Hx) as SPX.
split; [intros Hin; apply HO; unfold Y in Hin; clear - Hin FSV; unfold hid in *; lia|].
split; [intros Hin; apply HM; clear - Hin; lia|]. split; [| exact I]. clear - SPX LOW LO80. intros Hin. destruct SPX as [SX|SX]; lia. }
clear PF. rename PF15 into PF.
assert (OF15 : offsh [(Y, Y + 4 * Z.of_nat (length ys')); (a_msp a, a_msp a + 4 * Z.of_nat (length (sj_iq j))); (usp + -608 + -80, usp + -608)]).
{ rewrite LYS14, JIQ. cbn [offsh]. unfold Y. clear - FPHI2 FO1 FO2 MSPSH LOS LO80 FSV. unfold hid, SH_LO, SH_HI in *. cbn. lia. }
assert (ACC15 : forall o n, acc asegs m14 o n -> 0 <= o -> o + n <= 140737488355328 -> acc asegs m15 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch asegs _ m14 m15 o n (conj H0 (conj H1 H)) MU15 (shfree_of_offsh _ o n OF15 H0 H1)))). }
assert (ACA15 : acc asegs m15 A 48) by (apply ACC15; [exact ACA14| clear - FA1 FP0; lia| clear - FA2 BF1 LO608 SPT; lia]).
assert (ACO15 : acc asegs m15 OUT 8000) by (apply ACC15; [exact ACO14| clear - FO1 FP0; lia| clear - FO2 BF1 LO608 SPT; lia]).
assert (ACT15 : acc asegs m15 STEREO 24) by (apply ACC15; [exact ACT14| clear - FS1 FP0; lia| clear - FS2 BF1 LO608 SPT; lia]).
assert (SSP15 : io_ssp m15).
{ apply (sbd_io_ssp_agree m14 m15 SSP14 (AF_DRV Σx m15 ART15)). intros a0 Ha. apply MU15. unfold X00a.SSP_GUARD in Ha. rewrite LYS14, JIQ. cbn [outside]. unfold Y.
clear - Ha FO1 FPIMG MSPIMG LO80 LOS FSV. unfold hid, SEGTOP_A in *. split; [lia| split; [cbn; lia| split; [lia| exact I]]]. }
assert (KEEP : forall P, fp_local IO_FP P -> P m14 -> P m15).
{ intros P L Pm. apply (fp_local_munch IO_FP P _ m14 m15 L IO_img MU15); [| exact Pm]. intros x Hx. unfold SEGTOP_A in Hx. rewrite LYS14, JIQ. cbn [outside]. unfold Y.
clear - Hx FO1 FPIMG MSPIMG LO80 LOS FSV. unfold hid, SEGTOP_A in *. split; [lia| split; [cbn; lia| split; [lia| exact I]]]. }
pk_io ERR_rep OUT_rep KEEP. clear KEEP ACA14 ACO14 ACT14 SSP14 ACC15 ART14.

destruct (af_acc_live RT AF Σx m15 S 160 ART15 INLX) as (_ & ACS15).
assert (OBS15 : aobj asegs m15 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO608 SPT; unfold APP_TOP; lia| exact ACS15]).
sb_unpack X15 as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
assert (LO624 : lo <= usp + -608 - 16) by (clear - LO80; lia).
cps_seg (sbd_n4b usp lo S OUT f (sbmode_struct (sbd_mode s)) fsz
(fupds (fupds g [(44%nat, Z_to_bv 64 (S + 144)); (43%nat, Z_to_bv 64 (S + 152))]) [(42%nat, Z_to_bv 64 (Z.shiftr (S + 144) 3 + SHB)); (41%nat, Z_to_bv 64 (Z.shiftr (S + 152) 3 + SHB))])
(Z_to_bv 64 0) sF a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
FR11 ltac:(cbn [fupds Nat.eqb]; exact G27) ltac:(cbn [fupds Nat.eqb]; exact G45) HD PT eq_refl
ltac:(unfold sF, sI; cbn [set_sbd_first set_sbd_submodeID sbd_full_frame_size]; exact IFFS) ltac:(clear - FSV; unfold hid in *; lia)
OBS15 S8 SPOS BS1 SOFF ltac:(clear - FO1 FP0; lia) ltac:(clear - FO2 BF1 LO608 SPT; lia) ST15 LO624 LOS SPH MI15).
destruct POST as (m16 & ja & -> & MU16 & WM16 & MI16 & ST16 & ARG16).
clear HD FST PT LE SEED CFG IDC PAD OBS15 ACS15 ST15 MI15.
pk_munch_all MU16 WM16 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LO624; cbn [outside]; split; [lia| exact I])
ltac:(fun x Hx => clear - Hx LO624 LOS; cbn [outside]; split; [lia| exact I]).
trm MU16 WM16 OCa ltac:(clear - LWA FO1 FO2 BF1 LO624 FSV; unfold hid in *; lia).
trm MU16 WM16 YSI ltac:(unfold Y; clear - LYSI LYS14 FO1 FO2 BF1 LO624 FSV; unfold hid in *; lia).
trm MU16 WM16 OCc ltac:(clear - LWC FO1 FO2 BF1 LO624 FSV; unfold hid in *; lia).
trm MU16 WM16 SV ltac:(clear; lia).
trm MU16 WM16 FR11 ltac:(clear; lia).
trm MU16 WM16 FRB ltac:(clear - BF LO624; lia).
trm MU16 WM16 FRS ltac:(clear - BF0 LO624; lia).
trm MU16 WM16 STB ltac:(clear - FS1 FS2 BF1 LO624; lia).
trm MU16 WM16 BOBJ8 ltac:(clear - FA1 FA2 BF1 LO624; lia).
trm MU16 WM16 BDAT8 ltac:(clear - BLPD PD1 PD2 Lbs8 LO624; lia).
trm MU16 WM16 X15 ltac:(clear - BS1 LO624; lia).
assert (ART16 : X0ec.ART RT Σx m16).
{ apply (af_frame RT AF Σx m15 m16 lo ART15 LOWX); [| exact WM16]. intros a0 Ha. apply MU16. cbn [outside]. split; [| exact I].
intros Hin. apply Ha. left. clear - Hin LO624 SPT; unfold USTACK_TOP in *; lia. }
assert (PF16 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m16).
{ apply (pres_fp_trans _ _ _ _ m m15 m16 PF). apply (pres_fp_of_munch _ _ _ _ _ m15 m16 MU16). intros x Hx _. cbn [outside].
pose proof (SPL x Hx) as SPX. split; [| exact I]. clear - SPX LOW LO624. intros Hin. destruct SPX as [SX|SX]; lia. }
clear PF ART15. rename PF16 into PF.
assert (OF16 : offsh [(usp + -624, usp + -608)]) by (cbn [offsh]; clear - LOS LO624; unfold SH_LO, SH_HI in *; lia).
assert (ACC16 : forall o n, acc asegs m15 o n -> 0 <= o -> o + n <= 140737488355328 -> acc asegs m16 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch asegs _ m15 m16 o n (conj H0 (conj H1 H)) MU16 (shfree_of_offsh _ o n OF16 H0 H1)))). }
assert (ACA16 : acc asegs m16 A 48) by (apply ACC16; [exact ACA15| clear - FA1 FP0; lia| clear - FA2 BF1 LO608 SPT; lia]).
assert (ACO16 : acc asegs m16 OUT 8000) by (apply ACC16; [exact ACO15| clear - FO1 FP0; lia| clear - FO2 BF1 LO608 SPT; lia]).
assert (ACT16 : acc asegs m16 STEREO 24) by (apply ACC16; [exact ACT15| clear - FS1 FP0; lia| clear - FS2 BF1 LO608 SPT; lia]).
assert (SSP16 : io_ssp m16).
{ apply (sbd_io_ssp_agree m15 m16 SSP15 (AF_DRV Σx m16 ART16)). intros a0 Ha. apply MU16. unfold X00a.SSP_GUARD in Ha. cbn [outside].
clear - Ha LO624 LOS. split; [lia| exact I]. }
clear ACA15 ACO15 ACT15 SSP15 ACC16.

destruct BUFS15 as (G0C & G1C & EXC & OQC & IQC & MSPC & PGC & ERC).
assert (YJ : rw_cells asegs m16 OUT (f32 (wa ++ ysi))).
{ apply f32_join; [exact OCa|]. replace (OUT + 4 * Z.of_nat (length wa)) with Y by (unfold Y; rewrite LWA; reflexivity). exact YSI. }
assert (LYJ : Z.of_nat (length (wa ++ ysi)) = 2 * fsz) by (rewrite length_app, LYSI; clear - LWA LYS14; lia).
clear OCa YSI.
assert (ING0 : In (a_g0 a, 256) (rt_live RT Σx)) by (apply (LIVED (sbd_g0_mem s, a_g0 a, 256)); rewrite ELBD; apply in_app_iff; left; cbn [sb_blocks In]; do 1 right; left; reflexivity).
assert (ING1 : In (a_g1 a, 256) (rt_live RT Σx)) by (apply (LIVED (sbd_g1_mem s, a_g1 a, 256)); rewrite ELBD; apply in_app_iff; left; cbn [sb_blocks In]; do 2 right; left; reflexivity).
assert (NEG01 : a_g0 a <> a_g1 a).
{ intros E. pose proof NDUP as ND'. rewrite ELBD, map_app in ND'. apply List.NoDup_app_remove_r in ND'.
cbn [sb_blocks map blk_id blk_addr fst snd] in ND'. do 1 (apply List.NoDup_cons_iff in ND'; destruct ND' as [_ ND']).
apply List.NoDup_cons_iff in ND'. destruct ND' as [NI _]. apply NI. rewrite E. cbn [In]. left; reflexivity. }
pose proof (live_apart RT AF Σx m16 _ _ _ _ ART16 ING0 ING1 NEG01) as G01.
assert (AL8b : sb_addrs_al a) by (apply (sb_addrs_al_of_blocks s S a); intros bk Hb; apply LAL8; rewrite ELBD; apply in_app_iff; left; exact Hb).
destruct AL8b as (G08 & G18 & _).
assert (EU624 : bv_unsigned (Z_to_bv 64 (usp + -624)) = usp + -624) by (apply unsigned_lit; clear - SPT LO624 LOS; lia).
assert (QN : 2 * fsz = 320 \/ 2 * fsz = 640) by (clear - FSV; unfold hid in *; lia).
assert (EA1 : Z_to_bv 64 (OUT + 4 * fsz) = Z_to_bv 64 (OUT + 2 * (2 * fsz))) by (f_equal; clear; lia).
assert (EA2 : Z_to_bv 64 sb_A_H0 = Z_to_bv 64 0x27000) by reflexivity.
cps_rt (QMF16 (2 * fsz) QN Σx (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m16
OUT (a_g0 a) (a_g1 a) lo fh (a_g0 a) 256 (a_g1 a) 256 kh (wa ++ ysi) (sj_g0 j2) (sj_g1 j2)
FDO MST eq_refl EA1 EA2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
YJ LYJ INFHX FO1 ltac:(clear - FO2 FSV; unfold hid in *; lia)
(acc_sub asegs m16 OUT 8000 OUT (4 * (2 * fsz)) ACO16 ltac:(clear; lia) ltac:(clear - FSV; unfold hid in *; lia)) OAL
G0C JG0 ING0 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - G08; Z.div_mod_to_equations; lia)
G1C JG1 ING1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - G18; Z.div_mod_to_equations; lia)
ltac:(clear - G01; lia)
ltac:(rewrite EU624; apply (pois_above_le _ usp); [rewrite EPX; exact POA| clear; lia]) FRM15 ART16 MI16
ltac:(rewrite EU624; exact ST16) LOWX
ltac:(rewrite EU624; clear - LOR DSP; unfold RT_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)
ltac:(rewrite EU624; clear - SPT; unfold USTACK_TOP in *; lia)
ltac:(rewrite EU624; clear - SPA; Z.div_mod_to_equations; lia)).
intros cq (Σq & Hcq & LVq & FRq & SPq & CRq & POq).
cps_unpack_lib Hcq as (vq & m17 & ysq & g0q & g1q & RSq & (ART17 & MI17 & WM17 & ST17) & PRES17 & YSQ & LYSQ & G0Q & LG0Q & G1Q & LG1Q & ACQ).
try rewrite EU624 in PRES17. try rewrite EU624 in ST17.
clear YJ G0C G1C.
assert (CLF : forall x, fh <= x < fh + fs_size kh - 8 -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -624) x)
by (intros x Hx; right; right; right; left; exists fh, kh; split; [exact INFHX| exact Hx]).
assert (CLS : forall x, usp + -624 <= x < usp -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -624) x)
by (intros x Hx; left; clear - Hx SPT; unfold USTACK_TOP in *; lia).
assert (CLL : forall p n x, In (p, n) (rt_live RT Σx) -> p <= x < p + n -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -624) x)
by (intros p n x Hp Hx; right; right; left; exists p, n; split; [exact Hp| exact Hx]).
assert (CLF0 : forall x, f <= x < f + 56 -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -624) x)
by (intros x Hx; right; right; right; left; exists f, 0%nat; split; [exact INF| change (fs_size 0) with 64; clear - Hx; lia]).
assert (CLSF : forall x, sf <= x < sf + 8 -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -624) x)
by (intros x Hx; right; right; right; right; exists f, 0%nat; split; [exact INF| change (fs_size 0) with 64; rewrite <- SHF, SHF0; clear - Hx; lia]).
destruct (frame_live_apart RT AF Σx m16 fh kh _ _ ART16 INFHX ING0) as (FG0 & _). destruct (frame_live_apart RT AF Σx m16 fh kh _ _ ART16 INFHX ING1) as (FG1 & _).
destruct (frame_live_apart RT AF Σx m16 f 0%nat _ _ ART16 INF ING0) as (FG0f & FG0s). destruct (frame_live_apart RT AF Σx m16 f 0%nat _ _ ART16 INF ING1) as (FG1f & FG1s).
change (fs_size 0) with 64 in FG0f, FG0s, FG1f, FG1s. rewrite SHF0, <- SHF in FG0s, FG1s.
destruct (live_below_lo RT AF Σx m16 _ _ lo ART16 ING0 LOWX) as (_ & G0LO & _). destruct (live_below_lo RT AF Σx m16 _ _ lo ART16 ING1 LOWX) as (_ & G1LO & _).
assert (SG0N : S <> a_g0 a).
{ intros E. pose proof NDUP as ND'. rewrite ELBD, map_app in ND'. apply List.NoDup_app_remove_r in ND'.
cbn [sb_blocks map blk_id blk_addr fst snd] in ND'. apply List.NoDup_cons_iff in ND'. destruct ND' as [NI _]. apply NI. rewrite E. cbn [In]. left; reflexivity. }
assert (SG1N : S <> a_g1 a).
{ intros E. pose proof NDUP as ND'. rewrite ELBD, map_app in ND'. apply List.NoDup_app_remove_r in ND'.
cbn [sb_blocks map blk_id blk_addr fst snd] in ND'. apply List.NoDup_cons_iff in ND'. destruct ND' as [NI _]. apply NI. rewrite E. cbn [In]. right; left; reflexivity. }
pose proof (live_apart RT AF Σx m16 _ _ _ _ ART16 INLX ING0 SG0N) as SG0. pose proof (live_apart RT AF Σx m16 _ _ _ _ ART16 INLX ING1 SG1N) as SG1.
assert (PDG0N : PD <> a_g0 a) by (intros E; apply (PDB (sbd_g0_mem s, a_g0 a, 256)); [rewrite ELBD; apply in_app_iff; left; cbn [sb_blocks In]; do 1 right; left; reflexivity| exact (eq_sym E)]).
assert (PDG1N : PD <> a_g1 a) by (intros E; apply (PDB (sbd_g1_mem s, a_g1 a, 256)); [rewrite ELBD; apply in_app_iff; left; cbn [sb_blocks In]; do 2 right; left; reflexivity| exact (eq_sym E)]).
pose proof (live_apart RT AF Σx m16 _ _ _ _ ART16 INPDX ING0 PDG0N) as PDG0. pose proof (live_apart RT AF Σx m16 _ _ _ _ ART16 INPDX ING1 PDG1N) as PDG1.
assert (OUTQ : forall x, (x < OUT \/ OUT + 8 * fsz <= x) -> (x < a_g0 a \/ a_g0 a + 256 <= x) -> (x < a_g1 a \/ a_g1 a + 256 <= x) ->
outside [(OUT, OUT + 4 * (2 * fsz)); (a_g0 a, a_g0 a + 256); (a_g1 a, a_g1 a + 256)] x)
by (intros x H1 H2 H3; cbn [outside]; split; [clear - H1; lia| split; [clear - H2; lia| split; [clear - H3; lia| exact I]]]).
tr1 PRES17 WM17 OCc ltac:(fun x Hx => apply CLF; clear - Hx LWC FO1 FO2 FSV; unfold hid in *; lia)
ltac:(fun x Hx => apply OUTQ; [clear - Hx LWC FSV; unfold hid in *; lia | clear - Hx LWC FO1 FO2 FG0 FSV; unfold hid in *; lia | clear - Hx LWC FO1 FO2 FG1 FSV; unfold hid in *; lia]).
tr1 PRES17 WM17 SV ltac:(fun x Hx => apply CLS; clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; [clear - Hx BF1 FO2 LO608 FSV; unfold hid in *; lia | clear - Hx G0LO LO608; lia | clear - Hx G1LO LO608; lia]).
tr1 PRES17 WM17 FR11 ltac:(fun x Hx => apply CLS; clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; [clear - Hx BF1 FO2 LO608 FSV; unfold hid in *; lia | clear - Hx G0LO LO608; lia | clear - Hx G1LO LO608; lia]).
tr1 PRES17 WM17 ARG16 ltac:(fun x Hx => apply CLS; clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; [clear - Hx BF1 FO2 LO624 FSV; unfold hid in *; lia | clear - Hx G0LO LO624; lia | clear - Hx G1LO LO624; lia]).
tr1 PRES17 WM17 FRB ltac:(fun x Hx => apply CLF0; clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; [clear - Hx FFA' FO1 FO2 FSV; unfold hid in *; lia | clear - Hx FG0f; lia | clear - Hx FG1f; lia]).
tr1 PRES17 WM17 FRS ltac:(fun x Hx => apply CLSF; clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; [clear - Hx FPHI2 SHF1 SHF2 FO1 FO2 FSV; unfold hid, SH_LO, SH_HI in *; lia | clear - Hx FG0s; lia | clear - Hx FG1s; lia]).
tr1 PRES17 WM17 STB ltac:(fun x Hx => apply CLF; clear - Hx FS1 FS2; lia)
ltac:(fun x Hx => apply OUTQ; [clear - Hx HOS' FO1 FO2 FS1 FS2 FSV; unfold hid, hidp in *; lia | clear - Hx FS1 FS2 FG0; lia | clear - Hx FS1 FS2 FG1; lia]).
tr1 PRES17 WM17 BOBJ8 ltac:(fun x Hx => apply CLF; clear - Hx FA1 FA2; lia)
ltac:(fun x Hx => apply OUTQ; [clear - Hx HAO' FO1 FO2 FA1 FA2 FSV; unfold hid, hidp in *; lia | clear - Hx FA1 FA2 FG0; lia | clear - Hx FA1 FA2 FG1; lia]).
tr1 PRES17 WM17 BDAT8 ltac:(fun x Hx => apply (CLL PD ND x INPDX); clear - Hx PD1 PD2 Lbs8; lia)
ltac:(fun x Hx => apply OUTQ; [clear - Hx FLPD FO1 FO2 PD1 PD2 Lbs8 FSV; unfold hid in *; lia | clear - Hx PDG0 PD1 PD2 Lbs8; lia | clear - Hx PDG1 PD1 PD2 Lbs8; lia]).
tr1 PRES17 WM17 X15 ltac:(fun x Hx => apply (CLL S 160 x INLX); clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; [clear - Hx SFH' FO1 FO2 FSV; unfold hid in *; lia | clear - Hx SG0; lia | clear - Hx SG1; lia]).
Ltac tra AG H bk tacR ::=
lazymatch type of AG with
| agree_blocks _ ?m ?m' ?L =>
lazymatch type of H with
| rw_cells _ m ?A0 ?cs =>
let H' := fresh "T" in
assert (H' : rw_cells asegs m' A0 cs)
by (apply (rw_cells_agree_at asegs m m' A0 cs H); apply (agree_blocks_at asegs m m' L bk A0 cs AG);
[ apply in_app_iff; left; cbn [sb_blocks firstn skipn In]; repeat (first [left; reflexivity | right]) | exact H | unfold blk_addr, blk_size; cbn [fst snd]; simpl_sizes; tacR | unfold blk_addr, blk_size; cbn [fst snd]; simpl_sizes; tacR ]);
clear H; rename H' into H
end
end.

set (LNG := skipn 3 (sb_blocks sI S a) ++ LBL).
assert (ELNG : LBD = (sbd_blk sI, S, SBSTATE_SIZEOF) :: (sbd_g0_mem sI, a_g0 a, 256) :: (sbd_g1_mem sI, a_g1 a, 256) :: LNG) by (rewrite ELBD1; reflexivity).
assert (NG : forall bk, In bk LNG -> blk_addr bk <> a_g0 a /\ blk_addr bk <> a_g1 a).
{ intros bk Hb. pose proof NDUP as ND'. rewrite ELNG in ND'. cbn [map] in ND'.
apply List.NoDup_cons_iff in ND'. destruct ND' as [_ ND']. apply List.NoDup_cons_iff in ND'. destruct ND' as [N0 ND']. apply List.NoDup_cons_iff in ND'. destruct ND' as [N1 _].
cbn [blk_id blk_addr fst snd] in N0, N1.
split; intros E; [apply N0; right| apply N1]; rewrite <- E; exact (in_map blk_id LNG bk Hb). }
assert (LIVNG : forall bk, In bk LNG -> In (blk_addr bk, blk_size bk) (rt_live RT Σx))
by (intros bk Hb; apply LIVED; rewrite ELNG; right; right; right; exact Hb).
assert (AG17 : agree_blocks asegs m16 m17 LNG).
{ apply (agree_blocks_of_pres_fp RT Σx _ _ _ m16 m17 LNG PRES17 WM17 LIVNG). intros bk x Hb Hx. pose proof (LIVNG bk Hb) as LB.
destruct (frame_live_apart RT AF Σx m16 fh kh _ _ ART16 INFHX LB) as (FB & _).
destruct (NG bk Hb) as (N0 & N1).
pose proof (live_apart RT AF Σx m16 _ _ _ _ ART16 LB ING0 N0) as A0. pose proof (live_apart RT AF Σx m16 _ _ _ _ ART16 LB ING1 N1) as A1.
apply OUTQ; [clear - FB Hx FO1 FO2 FSV; unfold hid in *; lia | clear - A0 Hx; lia | clear - A1 Hx; lia]. }
unfold LNG in AG17.
tra AG17 EXC (sbd_excBuf sI, a_exc a, 4 * sbd_subframeSize sI) ltac:(unfold j2, sI; cbn [sj_exc set_sbd_submodeID sbd_subframeSize]; clear - JEXC; lia).
tra AG17 OQC (sbd_old_qlsp sI, a_oq a, 32) ltac:(unfold j2; cbn [sj_oq]; clear - JOQ; lia).
tra AG17 IQC (sbd_interp_qlpc sI, a_iq a, 32) ltac:(unfold j2; cbn [sj_iq]; clear - JIQ; lia).
tra AG17 MSPC (sbd_mem_sp sI, a_msp a, 64) ltac:(unfold j2; cbn [sj_msp]; rewrite ?length_app, ?length_skipn, ?LMVI, ?JIQ, ?JMSP; cbn; clear; lia).
tra AG17 PGC (sbd_pi_gain sI, a_pg a, 16) ltac:(unfold j2; cbn [sj_pg]; clear - JPG; lia).
tra AG17 ERC (sbd_exc_rms sI, a_er a, 16) ltac:(unfold j2; cbn [sj_er]; clear - JER; lia).
assert (AGL17 : agree_blocks asegs m16 m17 LBL) by (apply (agree_blocks_sub asegs _ _ _ _ AG17); intros bk Hb; apply in_app_iff; right; exact Hb).
pk_blocks AGL17. clear AGL17 AG17.

set (j3 := SBJ (sj_last_ener j) (sj_seed j) (sj_pad1 j) (sj_pad2 j) g0q g1q (sj_exc j) (sj_oq j) (sj_iq j) (mvi ++ skipn 8 (sj_msp j)) (sj_pg j) (sj_er j)).
assert (BUFS17 : sb_bufs asegs m17 a j3) by (exact (conj G0Q (conj G1Q (conj EXC (conj OQC (conj IQC (conj MSPC (conj PGC ERC)))))))).
assert (JOK3 : sb_junk_ok sF j3).
{ unfold sb_junk_ok. repeat split; cbn [j3 sj_pad1 sj_pad2 sj_g0 sj_g1 sj_exc sj_oq sj_iq sj_msp sj_pg sj_er];
first [ assumption
| rewrite length_app, length_skipn, LMVI, JIQ, JMSP; reflexivity
| unfold sF, sI; cbn [set_sbd_first set_sbd_submodeID sbd_subframeSize]; exact JEXC ]. }
assert (X17 : rw_cells asegs m17 S (SBCELLS sF a OUT j3)) by (exact X15).
clear G0Q G1Q EXC OQC IQC MSPC PGC ERC X15.
assert (OC17 : rw_cells asegs m17 OUT (f32 (ysq ++ wc))).
{ apply f32_join; [exact YSQ|]. replace (OUT + 4 * Z.of_nat (length ysq)) with (OUT + 4 * fsz + 4 * fsz) by (rewrite LYSQ; clear; lia). exact OCc. }
assert (LOWS17 : length (ysq ++ wc) = 2000%nat) by (rewrite length_app; clear - LYSQ LWC FSV; unfold hid in *; lia).
clear YSQ OCc.

assert (PF17 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m17).
{ apply (pres_fp_trans _ _ _ _ m m16 m17 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σx) (rt_frames RT Σx) (usp + -624) _ m16 m17 PRES17).
- intros e He. rewrite ELX. exact He.
- intros e He. rewrite EFX. right. exact He.
- clear; lia.
- intros x Hx Ho. cbn [outside] in Ho. destruct Ho as (_ & HO & _ & Ho). apply sb_outside_app_inv in Ho. destruct Ho as [Hb _].
rewrite ELNG in Hb. cbn [blocks_ivs map outside blk_addr blk_size fst snd] in Hb. destruct Hb as (_ & H0 & H1 & _).
apply OUTQ; [clear - HO FSV; unfold hid in *; lia | clear - H0; lia | clear - H1; lia]. }
clear PF. rename PF17 into PF.
assert (SHQ : forall o n, fh <= o -> o + n <= fh + fs_size kh -> forall i, 0 <= i < n -> outside [(OUT, OUT + 4 * (2 * fsz)); (a_g0 a, a_g0 a + 256); (a_g1 a, a_g1 a + 256)] (shad (o + i))).
{ intros o n H1 H2 i Hi.
assert (SR : SH_LO <= shad (o + i) < SH_HI).
{ pose proof (frame_facts RT AF Σx m16 fh kh ART16 INFHX) as (_ & _ & _ & _ & _ & _ & SA & SL & SH & _). split.
- unfold shad, SH_LO, SHB in *. assert (0 <= (o + i) / 8) by (apply Z.div_pos; lia). lia.
- assert (shad (o + i) < shad (fh + fs_size kh)); [| lia].
unfold shad. apply Z.add_lt_mono_r. apply Z.div_lt_upper_bound; [lia|].
assert (FH8 : fh mod 8 = 0) by (clear - FP64; Z.div_mod_to_equations; lia).
assert (FK8 : fs_size kh mod 8 = 0) by (destruct FS64 as (M64 & _); clear - M64; Z.div_mod_to_equations; lia).
assert (E : fh + fs_size kh = 8 * ((fh + fs_size kh) / 8)).
{ pose proof (Z.div_mod (fh + fs_size kh) 8 ltac:(lia)) as XD. rewrite Zplus_mod, FH8, FK8 in XD. cbn in XD. lia. }
lia. }
pose proof (live_facts RT AF Σx m16 _ _ ART16 ING0) as (_ & _ & _ & G0SH). pose proof (live_facts RT AF Σx m16 _ _ ART16 ING1) as (_ & _ & _ & G1SH).
apply OUTQ; [clear - SR FPHI2 FO1 FO2 FSV; unfold hid, SH_LO, SH_HI in *; lia | clear - SR G0SH; unfold SH_LO, SH_HI in *; lia | clear - SR G1SH; unfold SH_LO, SH_HI in *; lia]. }
assert (FH8 : fh mod 8 = 0) by (clear - FP64; Z.div_mod_to_equations; lia).
assert (FK8 : fs_size kh mod 8 = 0) by (destruct FS64 as (M64 & _); clear - M64; Z.div_mod_to_equations; lia).
assert (ACA17 : acc asegs m17 A 48)
by (apply (acc_pres_fp_frame _ _ _ _ m16 m17 fh kh A 48 PRES17 INFHX FH8 FK8 ltac:(clear - FP0; lia) FA1 ltac:(clear - FA2; lia) (SHQ A 48 FA1 ltac:(clear - FA2; lia)) ACA16)).
assert (ACO17 : acc asegs m17 OUT 8000)
by (apply (acc_pres_fp_frame _ _ _ _ m16 m17 fh kh OUT 8000 PRES17 INFHX FH8 FK8 ltac:(clear - FP0; lia) FO1 ltac:(clear - FO2; lia) (SHQ OUT 8000 FO1 ltac:(clear - FO2; lia)) ACO16)).
assert (ACT17 : acc asegs m17 STEREO 24)
by (apply (acc_pres_fp_frame _ _ _ _ m16 m17 fh kh STEREO 24 PRES17 INFHX FH8 FK8 ltac:(clear - FP0; lia) FS1 ltac:(clear - FS2; lia) (SHQ STEREO 24 FS1 ltac:(clear - FS2; lia)) ACT16)).
assert (SSP17 : io_ssp m17).
{ apply (sbd_io_ssp_agree m16 m17 SSP16 (AF_DRV Σq m17 ART17)). intros a0 Ha. apply PRES17; [right; left; exact (sbd_ssp_static _ Ha)|].
unfold X00a.SSP_GUARD in Ha. pose proof (af_live_small RT AF Σx m16 _ _ ART16 ING0 ltac:(clear; lia)) as G0I. pose proof (af_live_small RT AF Σx m16 _ _ ART16 ING1 ltac:(clear; lia)) as G1I.
apply OUTQ; [clear - Ha FO1 FPIMG; unfold SEGTOP_A in *; lia | clear - Ha G0I; unfold SEGTOP_A in *; lia | clear - Ha G1I; unfold SEGTOP_A in *; lia]. }
pk_io_fp PRES17 ERR_rep OUT_rep IO_FP IO_img ltac:(fun y Hy => pose proof (af_live_small RT AF Σx m16 _ _ ART16 ING0 ltac:(clear; lia)) as G0I;
pose proof (af_live_small RT AF Σx m16 _ _ ART16 ING1 ltac:(clear; lia)) as G1I;
apply OUTQ; [clear - Hy FO1 FPIMG; unfold SEGTOP_A in *; lia | clear - Hy G0I; unfold SEGTOP_A in *; lia | clear - Hy G1I; unfold SEGTOP_A in *; lia]).
clear ACA16 ACO16 ACT16 SSP16 PRES17 ART16 SHQ.
clear Hc.

cps_seg (sbd_n5 usp lo S OUT f (sbmode_struct (sbd_mode s)) (Z_to_bv 64 0) ja _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ARG16 ST17 ltac:(clear - LO624; lia) SPH MI17).
destruct POST as (-> & ST17').
assert (EFq : rt_frames RT Σq = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRq; exact EFX).
assert (ELq : rt_live RT Σq = rt_live RT Σ) by (rewrite LVq; exact ELX).
assert (ESq : rt_sp0 RT Σq = rt_sp0 RT Σ) by (rewrite SPq; exact ESX).
assert (EPq : rt_pois RT Σq = rt_pois RT Σ) by (rewrite POq; exact EPX).
assert (INVF : sb_inv sF).
{ destruct INV1 as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12). unfold sb_inv, sF. cbn [set_sbd_first sbd_mode sbd_frame_size sbd_full_frame_size
sbd_subframeSize sbd_nbSubframes sbd_lpcSize sbd_first sbd_sampling_rate sbd_lpc_enh_enabled sbd_encode_submode sbd_submodeID sbd_innov_save].
refine (conj I1 (conj I2 (conj I3 (conj I4 (conj I5 (conj I6 (conj (or_intror eq_refl) (conj I8 (conj I9 (conj I10 (conj I11 I12))))))))))). }
assert (REPX : DREP OUT STEREO m17 S (DecSB sF low3) LBD).
{ cbn [decst_rep]. exists a, j3, LBL. split; [exact ELBD1|]. split; [exact S8|]. split; [exact SPOS|]. split; [exact INVF|]. split; [exact JOK3|].
split; [exact X17|]. split; [exact BUFS17|]. exists OUT. exact RLOW. }
assert (BREPX : bits_rep asegs m17 A D (sbw_bits b1)).
{ split; [exists rj8; split; [exact Lrj8| unfold bits_cells; exact BOBJ8]|].
split; [exists bs8; split; [apply (proj2 (u8arr_rw_CB m17 D bs8)); exact BDAT8| exact Hbs8]| exact BSIDE8]. }
assert (PD2X : D + sb_buf_size (sbw_bits b1) <= PD + ND) by (rewrite BSZ8; exact PD2).
assert (WMX : wmono asegs m m17) by (eapply wmono_trans; [exact WM0|]; eapply wmono_trans; [exact WM8|]; eapply wmono_trans; [exact WM9|];
eapply wmono_trans; [exact WM11|]; eapply wmono_trans; [exact WM14|]; eapply wmono_trans; [exact WM15|];
eapply wmono_trans; [exact WM16| exact WM17]).
cps_rt (sbd_exit_cps RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AUN_lo AUN_nop Σ Σq F0 fs0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m m17 lo S OUT STEREO A D f fh PD ND kh LBD
(fupds (fupds g [(44%nat, Z_to_bv 64 (S + 144)); (43%nat, Z_to_bv 64 (S + 152))]) [(42%nat, Z_to_bv 64 (Z.shiftr (S + 144) 3 + SHB)); (41%nat, Z_to_bv 64 (Z.shiftr (S + 152) 3 + SHB))])
0 0 (DecSB sF low3) (sbw_bits b1) (ysq ++ wc) stb j24 j36 (Z_to_bv 64 dtx)
EFq ELq ESq EPq ART0 POA NAF LIVE INPD PD1 PD2X INFH FA1 FA2 ACA FO1 FO2 ACO FS1 FS2 ACST ART17 MI17 RSq ST17' LOW
ltac:(clear - LOR DSP; unfold RT_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia) SPT SPA PF WMX FR11
ltac:(cbn [fupds Nat.eqb]; exact G13) ltac:(cbn [fupds Nat.eqb]; exact G52)
(or_introl eq_refl) SV FRB FRS REPX (fun _ => I) BREPX BOK8 OC17 LOWS17 STB ERRX OUTK0).
intros c' (Σ' & Hc' & E1 & E2 & E3 & E4 & E5).
apply Hk. exists Σ'. split; [exact Hc'|].
pose proof (bkeep_sbw b1) as (K1 & K2 & K3).
cbn [dec_depth dec_mode dec_nestedR dec_credit sF sI set_sbd_submodeID set_sbd_first sbd_mode].
split; [clear; lia|]. split; [rewrite DL3; reflexivity|]. split; [reflexivity|]. split; [split; [exact NM3| exact NEST3]|].
split; [rewrite K2; exact OWN1|]. split; [rewrite K1; exact CHR1|]. split; [rewrite K3; exact BSZ1|].
split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [| exact E5].
rewrite E4, CRq. pose proof (dec_depth_pos low) as DP. clear - CBX DP. lia. }
destruct (sbd_innov_save s) as [k|] eqn:EIS.
2: {
cbn [sI set_sbd_submodeID sbd_innov_save] in POST. rewrite EIS in POST. destruct POST as (xa012 & xa112 & ->).
exact (TAILN m11 ows _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c3 SV FRB FRS BUFS OC LOWS STB ERRX ST8 BOBJ8 BDAT8 X9 WM11 MI11 FR11 RLOW OUTK0 ART11 PF
ACA11 ACO11 ACT11 SSP11 ACS11 OBS11 Hc). }

cbn [sI set_sbd_submodeID sbd_innov_save] in POST. rewrite EIS in POST. subst ms.
assert (EFF : sbd_full_frame_size sI = 2 * sbd_frame_size s) by (cbn [sI set_sbd_submodeID sbd_full_frame_size]; exact IFFS).

assert (FSN2 : Z.of_nat (Z.to_nat (2 * sbd_frame_size s)) = 2 * sbd_frame_size s) by (clear - FSV; lia).
apply (f32_split asegs m11 OUT ows (Z.to_nat (2 * sbd_frame_size s))) in OC; [| rewrite LOWS; clear - FSV; lia].
destruct OC as (OCa & OCb). rewrite FSN2 in OCb.
apply (f32_split asegs m11 (OUT + 4 * (2 * sbd_frame_size s)) (skipn (Z.to_nat (2 * sbd_frame_size s)) ows) (Z.to_nat (2 * sbd_frame_size s))) in OCb;
[| rewrite length_skipn, LOWS; clear - FSV; lia].
destruct OCb as (OCm & OCc). rewrite FSN2 in OCc.
assert (Lowa : length (firstn (Z.to_nat (2 * sbd_frame_size s)) ows) = Z.to_nat (2 * sbd_frame_size s)) by (rewrite length_firstn, LOWS; clear - FSV; lia).
assert (Lowc : length (skipn (Z.to_nat (2 * sbd_frame_size s)) (skipn (Z.to_nat (2 * sbd_frame_size s)) ows)) = (2000 - 2 * Z.to_nat (2 * sbd_frame_size s))%nat)
by (rewrite !length_skipn, LOWS; clear - FSV; lia).
pose proof (proj2 OCm) as WRM. rewrite cells_size_f32, length_firstn, length_skipn, LOWS in WRM.
replace (Z.of_nat (4 * Nat.min (Z.to_nat (2 * sbd_frame_size s)) (2000 - Z.to_nat (2 * sbd_frame_size s)))) with (4 * sbd_full_frame_size sI) in WRM
by (rewrite EFF; clear - FSV; lia).
replace (OUT + 4 * (2 * sbd_frame_size s)) with (OUT + 4 * k) in WRM, OCc by (rewrite ISV; reflexivity).
clear OCm.
generalize dependent (firstn (Z.to_nat (2 * sbd_frame_size s)) ows). intros owa OCa Lowa.
generalize dependent (skipn (Z.to_nat (2 * sbd_frame_size s)) (skipn (Z.to_nat (2 * sbd_frame_size s)) ows)). intros owc OCc Lowc.
assert (EU608 : bv_unsigned (Z_to_bv 64 (usp + -608)) = usp + -608) by (apply unsigned_lit; clear - SPT LO608 LOS; lia).
assert (MD0 : 0 <= OUT + 4 * k <= 2^47) by (rewrite ISV; clear - FP0 FO1 FO2 BF1 LO608 SPT FSV; unfold USTACK_TOP in *; lia).
assert (MN0 : 0 <= 4 * sbd_full_frame_size sI < 2^40) by (rewrite EFF; clear - FSV; lia).
assert (CHK : checked_dst RT Σx m11 (Z_to_bv 64 (usp + -608)) (OUT + 4 * k) (4 * sbd_full_frame_size sI)).
{ split; [intros _; split|].
- apply (acc_sub asegs m11 OUT 8000 (OUT + 4 * k) (4 * sbd_full_frame_size sI) ACO11); rewrite ?EFF, ?ISV; clear - FSV; lia.
- right; left. exists fh, kh. split; [exact INFHX| rewrite ?EFF, ?ISV; clear - FO1 FO2 FSV; lia].
- split; [| exact WRM]. intros i Hi. rewrite EU608. right; right; right; left. exists fh, kh. split; [exact INFHX| rewrite EFF in Hi; rewrite ISV; clear - FO1 FO2 FSV Hi; lia]. }
assert (COK : call_ok RT Σx m11 (Z_to_bv 64 (usp + -608)) lo).
{ unfold call_ok. rewrite EU608. split; [exact ST8|]. split; [exact LOWX|].
split; [clear - LOR DSP; unfold RT_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia|].
split; [clear - SPT; unfold USTACK_TOP in *; lia| clear - SPA; Z.div_mod_to_equations; lia]. }
refine (rz_cps RT Σx (PMfd F0 fs0) _ _ T c3 Hc _ _);
[ refine (MEMS Σx (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m11 (OUT + 4 * k) (4 * sbd_full_frame_size sI) (Z_to_bv 8 0) lo
FDO MST eq_refl eq_refl eq_refl MD0 MN0 CHK ART11 MI11 COK) | ].
intros c4 Hc4. unfold icpt_postF in Hc4.
destruct (ASTA_unpack RT Σx (PMfd F0 fs0) _ c4 Hc4) as (ms4 & PO4 & Hc4'); clear Hc4; cbv beta in PO4.
destruct PO4 as (m12 & RS12 & (ART12 & MI12 & WM12 & ST12) & PRES12 & BY12).
cps_ret RS12.
rewrite EU608 in PRES12, ST12.
rewrite (ret_pc_even RA_sbd_memset_n ltac:(unfold RA_sbd_memset_n; lia) eq_refl) in Hc4'.
clear MD0 MN0 CHK COK.

assert (PRESF : rt_pres_fp (rt_live RT Σx) (rt_frames RT Σx) (usp + -608) [(OUT + 4 * k, OUT + 4 * k + 4 * sbd_full_frame_size sI)] m11 m12).
{ apply (pres_fp_of_pres_ex_gen _ _ _ _ (rt_live RT Σx) (rt_frames RT Σx) (usp + -608) (OUT + 4 * k) (4 * sbd_full_frame_size sI) m11 m12 PRES12);
[intros e He; exact He | intros e He; exact He | clear; lia |].
intros x _ Ho. cbn [outside] in Ho. destruct Ho as (Ho & _). exact Ho. }
assert (OWM : forall x, (x < OUT + 4 * k \/ OUT + 4 * k + 4 * sbd_full_frame_size sI <= x) -> outside [(OUT + 4 * k, OUT + 4 * k + 4 * sbd_full_frame_size sI)] x)
by (intros x Hx; cbn [outside]; split; [clear - Hx; lia| exact I]).
assert (WIN : OUT <= OUT + 4 * k /\ OUT + 4 * k + 4 * sbd_full_frame_size sI <= OUT + 8000) by (rewrite EFF, ISV; clear - FSV; lia).
assert (CLF : forall x, fh <= x < fh + fs_size kh - 8 -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -608) x)
by (intros x Hx; right; right; right; left; exists fh, kh; split; [exact INFHX| exact Hx]).
assert (CLS : forall x, usp + -608 <= x < usp -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -608) x)
by (intros x Hx; left; clear - Hx SPT; unfold USTACK_TOP in *; lia).
assert (CLL : forall p n x, In (p, n) (rt_live RT Σx) -> p <= x < p + n -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -608) x)
by (intros p n x Hp Hx; right; right; left; exists p, n; split; [exact Hp| exact Hx]).
assert (CLF0 : forall x, f <= x < f + 56 -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -608) x)
by (intros x Hx; right; right; right; left; exists f, 0%nat; split; [exact INF| change (fs_size 0) with 64; lia]).
assert (CLSF : forall x, sf <= x < sf + 8 -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -608) x)
by (intros x Hx; right; right; right; right; exists f, 0%nat; split; [exact INF| change (fs_size 0) with 64; rewrite <- SHF, SHF0; lia]).
destruct (frame_live_apart RT AF Σx m11 fh kh PD ND ART11 INFHX INPDX) as (FLPD & _).
assert (SFH' : S + 160 <= fh \/ fh + fs_size kh <= S) by (clear - SFH; unfold hid in *; lia).
assert (FFA' : fh + fs_size kh <= f \/ f + 64 <= fh) by (clear - FFA; unfold hid in *; lia).
assert (FPHI2 : fh + fs_size kh <= SH_LO \/ SH_HI <= fh) by (clear - FPHI'; unfold hid, SH_LO, SH_HI in *; lia).
assert (HOS2 : OUT + 8000 <= STEREO \/ STEREO + 24 <= OUT) by (clear - HOS'; unfold hid in *; lia).
assert (HAO2 : A + 48 <= OUT \/ OUT + 8000 <= A) by (clear - HAO'; unfold hid in *; lia).
tr1 PRESF WM12 SV ltac:(fun x Hx => apply CLS; clear - Hx; lia) ltac:(fun x Hx => apply OWM; right; clear - Hx WIN FO2 BF1 LO608; lia).
tr1 PRESF WM12 FR11 ltac:(fun x Hx => apply CLS; clear - Hx; lia) ltac:(fun x Hx => apply OWM; right; clear - Hx WIN FO2 BF1 LO608; lia).
tr1 PRESF WM12 FRB ltac:(fun x Hx => apply CLF0; clear - Hx; lia) ltac:(fun x Hx => apply OWM; clear - Hx WIN FO1 FO2 FFA'; lia).
tr1 PRESF WM12 FRS ltac:(fun x Hx => apply CLSF; clear - Hx; lia)
ltac:(fun x Hx => apply OWM; clear - Hx WIN FO1 FO2 FPHI2 SHF1 SHF2; unfold SH_LO, SH_HI in *; lia).
tr1 PRESF WM12 STB ltac:(fun x Hx => apply CLF; clear - Hx FS1 FS2; lia) ltac:(fun x Hx => apply OWM; clear - Hx WIN HOS2; lia).
tr1 PRESF WM12 BOBJ8 ltac:(fun x Hx => apply CLF; clear - Hx FA1 FA2; lia) ltac:(fun x Hx => apply OWM; clear - Hx WIN HAO2; lia).
tr1 PRESF WM12 BDAT8 ltac:(fun x Hx => apply (CLL PD ND x INPDX); clear - Hx PD1 PD2 Lbs8; lia)
ltac:(fun x Hx => apply OWM; clear - Hx WIN PD1 PD2 Lbs8 FLPD FO1 FO2; lia).
tr1 PRESF WM12 X9 ltac:(fun x Hx => apply (CLL S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => apply OWM; clear - Hx WIN FO1 FO2 SFH'; lia).
tr1 PRESF WM12 OCa ltac:(fun x Hx => apply CLF; rewrite Lowa in Hx; clear - Hx FO1 FO2 FSV; lia)
ltac:(fun x Hx => apply OWM; left; rewrite Lowa in Hx; rewrite ISV; clear - Hx FSV; lia).
tr1 PRESF WM12 OCc ltac:(fun x Hx => apply CLF; rewrite Lowc in Hx; rewrite ISV in Hx; clear - Hx FO1 FO2 FSV; lia)
ltac:(fun x Hx => apply OWM; right; rewrite EFF; clear - Hx; lia).

assert (AGA : agree_blocks asegs m11 m12 LALL).
{ apply (agree_blocks_of_pres_fp RT Σx _ _ _ m11 m12 LALL PRESF WM12); [exact LIVEA|]. intros bk x Hb Hx.
pose proof (BOUT bk x Hb Hx) as H1. destruct (frame_live_apart RT AF Σx m11 fh kh _ _ ART11 INFHX (LIVEA bk Hb)) as (FB & _).
apply OWM. clear - H1 FB Hx WIN FO1 FO2. lia. }
unfold LALL in AGA. pk_all AGA. clear AGA.
pk_io_fp PRESF ERR_rep OUT_rep IO_FP IO_img ltac:(fun y Hy => apply OWM; left; clear - Hy WIN FO1 FPIMG; lia).
assert (SSP12 : io_ssp m12).
{ apply (sbd_io_ssp_agree m11 m12 SSP11 (AF_DRV Σx m12 ART12)). intros a0 Ha. apply PRESF; [right; left; exact (sbd_ssp_static _ Ha)|].
unfold X00a.SSP_GUARD in Ha. apply OWM. left. clear - Ha WIN FO1 FPIMG. lia. }
assert (SHW12 : forall o n, fh <= o -> o + n <= fh + fs_size kh -> forall i, 0 <= i < n -> outside [(OUT + 4 * k, OUT + 4 * k + 4 * sbd_full_frame_size sI)] (shad (o + i))).
{ intros o n H1 H2 i Hi.
assert (SR : SH_LO <= shad (o + i) < SH_HI).
{ pose proof (frame_facts RT AF Σx m11 fh kh ART11 INFHX) as (_ & _ & _ & _ & _ & _ & SA & SL & SH & _). split.
- unfold shad, SH_LO, SHB in *. assert (0 <= (o + i) / 8) by (apply Z.div_pos; lia). lia.
- assert (shad (o + i) < shad (fh + fs_size kh)); [| lia].
unfold shad. apply Z.add_lt_mono_r. apply Z.div_lt_upper_bound; [lia|].
assert (FH8 : fh mod 8 = 0) by (clear - FP64; Z.div_mod_to_equations; lia).
assert (FK8 : fs_size kh mod 8 = 0) by (destruct FS64 as (M64 & _); clear - M64; Z.div_mod_to_equations; lia).
assert (E : fh + fs_size kh = 8 * ((fh + fs_size kh) / 8)).
{ pose proof (Z.div_mod (fh + fs_size kh) 8 ltac:(lia)) as XD. rewrite Zplus_mod, FH8, FK8 in XD. cbn in XD. lia. }
lia. }
apply OWM. clear - SR FPHI2 WIN FO1 FO2. unfold SH_LO, SH_HI in *. lia. }
assert (FH8 : fh mod 8 = 0) by (clear - FP64; Z.div_mod_to_equations; lia).
assert (FK8 : fs_size kh mod 8 = 0) by (destruct FS64 as (M64 & _); clear - M64; Z.div_mod_to_equations; lia).
assert (ACA12 : acc asegs m12 A 48)
by (apply (acc_pres_fp_frame _ _ _ _ m11 m12 fh kh A 48 PRESF INFHX FH8 FK8 ltac:(lia) FA1 ltac:(lia) (SHW12 A 48 FA1 ltac:(lia)) ACA11)).
assert (ACO12 : acc asegs m12 OUT 8000)
by (apply (acc_pres_fp_frame _ _ _ _ m11 m12 fh kh OUT 8000 PRESF INFHX FH8 FK8 ltac:(lia) FO1 ltac:(lia) (SHW12 OUT 8000 FO1 ltac:(lia)) ACO11)).
assert (ACT12 : acc asegs m12 STEREO 24)
by (apply (acc_pres_fp_frame _ _ _ _ m11 m12 fh kh STEREO 24 PRESF INFHX FH8 FK8 ltac:(lia) FS1 ltac:(lia) (SHW12 STEREO 24 FS1 ltac:(lia)) ACT11)).
assert (PF12 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m12).
{ apply (pres_fp_trans _ _ _ _ m m11 m12 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σx) (rt_frames RT Σx) (usp + -608) _ m11 m12 PRESF).
- intros e He. rewrite ELX. exact He.
- intros e He. rewrite EFX. right. exact He.
- clear; lia.
- intros x Hx Ho. cbn [outside] in Ho. destruct Ho as (_ & HO & _). apply OWM. clear - HO WIN. lia. }
destruct (af_acc_live RT AF Σx m12 S 160 ART12 INLX) as (_ & ACS12).
assert (OBS12 : aobj asegs m12 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO608 SPT; unfold APP_TOP; lia| exact ACS12]).
assert (WM12' : wmono asegs m9 m12) by (eapply wmono_trans; [exact WM11| exact WM12]).

assert (ZB : rw_cells asegs m12 (OUT + 4 * k) [CB (length (repeat (Z_to_bv 8 0) (Z.to_nat (4 * sbd_full_frame_size sI)))) (repeat (Z_to_bv 8 0) (Z.to_nat (4 * sbd_full_frame_size sI)))]).
{ split; [split; [split; [reflexivity| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BY12]|].
cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, repeat_length. rewrite Z2Nat.id by (rewrite EFF; clear - FSV; lia).
exact (wr_at_transport asegs m11 m12 _ _ WRM WM12). }
rewrite repeat_length in ZB.
replace (Z.to_nat (4 * sbd_full_frame_size sI)) with (4 * Z.to_nat (2 * sbd_frame_size s))%nat in ZB by (rewrite EFF; clear - FSV; lia).
destruct (rw_cells_CB_f32 asegs m12 (OUT + 4 * k) (Z.to_nat (2 * sbd_frame_size s)) _ ZB) as (zw & Lzw & ZW). clear ZB.
assert (OC12 : rw_cells asegs m12 OUT (f32 (owa ++ zw ++ owc))).
{ apply (f32_join asegs m12 OUT _ _ OCa). replace (OUT + 4 * Z.of_nat (length owa)) with (OUT + 4 * k) by (rewrite Lowa, ISV; clear - FSV; lia).
apply (f32_join asegs m12 (OUT + 4 * k) _ _ ZW). replace (OUT + 4 * k + 4 * Z.of_nat (length zw)) with (OUT + 4 * k + 4 * (2 * sbd_frame_size s)) by (rewrite Lzw; clear - FSV; lia).
exact OCc. }
assert (LOWS12 : length (owa ++ zw ++ owc) = 2000%nat) by (rewrite !length_app, Lowa, Lzw, Lowc; clear - FSV; lia).
unfold RA_sbd_memset_n in Hc4'.
exact (TAILN m12 (owa ++ zw ++ owc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c4 SV FRB FRS BUFS OC12 LOWS12 STB ERRX ST12 BOBJ8 BDAT8 X9 WM12' MI12 FR11 RLOW OUTK ART12 PF12
ACA12 ACO12 ACT12 SSP12 ACS12 OBS12 Hc4').
}

destruct PZ as (-> & -> & -> & ->).
assert (EB : sbd_inv_bytes s b1 = []) by (unfold sbd_inv_bytes; fold id; rewrite ESM; reflexivity).
rewrite EB. apply rz_emit_nil.
assert (EV : sb_id_valid (sbd_mode s) id = true) by (unfold sb_id_valid; rewrite ESM; apply Bool.orb_true_r).
rewrite EV in Hc.

destruct (af_acc_live RT AF Σx m9 S 160 ART INLX) as (_ & ACS9).
assert (OBS9 : aobj asegs m9 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO608 SPT; unfold APP_TOP; lia| exact ACS9]).
pose proof (AF_LIB Σx m9 ART) as LC9.
assert (OBM9 : aobj asegs m9 (sbmode_struct (sbd_mode s)) 216).
{ destruct IMODE as [E|E]; rewrite E; cbn [sbmode_struct]; (apply (aobj_lit RT AF Σx m9 _ 216 ART);
[ unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_sb_wb_mode, A_sb_uwb_mode; lia | unfold A_sb_wb_mode, A_sb_uwb_mode, APP_TOP; lia]). }
sb_unpack X9 as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_m usp S OUT f (sbmode_struct (sbd_mode s)) id (fupds g [(44%nat, Z_to_bv 64 (S + 144)); (43%nat, Z_to_bv 64 (S + 152))]) s (sj_pad1 j)
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR8 CFG IDC OBS9 S8 SPOS SLO8 SOFF IMODE eq_refl OBM9 LC9 IDR SHL SPH MI9).
destruct POST as (m11 & xa011 & xa111 & -> & MU11 & WM11 & MI11 & FR11).
match goal with H : ASTA _ _ _ _ _ |- _ => rewrite ESM in H end.
clear FR8 HD FST PT LE SEED CFG IDC PAD OBS9 ACS9 LC9.
Time pk_munch_all MU11 WM11 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LO608; cbn [outside]; split; [lia| exact I])
ltac:(fun x Hx => clear - Hx LO608 LOS; cbn [outside]; split; [lia| exact I]).
Time cps_seg_post.
match goal with H : X0ec.ART RT Σx m11 |- _ => rename H into ART11 end.
assert (OF11 : offsh [(usp + -608, usp + -160)]) by (cbn [offsh]; clear - LOS LO608; unfold SH_LO, SH_HI in *; lia).
assert (ACC11 : forall o n, acc asegs m9 o n -> 0 <= o -> o + n <= 140737488355328 -> acc asegs m11 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch asegs _ m9 m11 o n (conj H0 (conj H1 H)) MU11 (shfree_of_offsh _ o n OF11 H0 H1)))). }
assert (ACA11 : acc asegs m11 A 48) by (apply ACC11; [exact ACA9| clear - FA1 FP0; lia| clear - FA2 BF1 LO608 SPT; lia]).
assert (ACO11 : acc asegs m11 OUT 8000) by (apply ACC11; [exact ACO9| clear - FO1 FP0; lia| clear - FO2 BF1 LO608 SPT; lia]).
assert (ACT11 : acc asegs m11 STEREO 24) by (apply ACC11; [exact ACT9| clear - FS1 FP0; lia| clear - FS2 BF1 LO608 SPT; lia]).
assert (SSP11 : io_ssp m11).
{ apply (sbd_io_ssp_agree m9 m11 SSPX (AF_DRV Σx m11 ART11)). intros a0 Ha. apply MU11. unfold X00a.SSP_GUARD in Ha. cbn [outside].
clear - Ha LO608 LOS. split; [lia| exact I]. }
clear ACA9 ACO9 ACT9 ACC11 SSPX.
destruct (af_acc_live RT AF Σx m11 S 160 ART11 INLX) as (_ & ACS11).
assert (OBS11 : aobj asegs m11 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO608 SPT; unfold APP_TOP; lia| exact ACS11]).

sb_unpack X9 as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_v1 usp lo S OUT f (sbmode_struct (sbd_mode s))
(fupds (fupds g [(44%nat, Z_to_bv 64 (S + 144)); (43%nat, Z_to_bv 64 (S + 152))]) [(42%nat, Z_to_bv 64 (Z.shiftr (S + 144) 3 + SHB)); (41%nat, Z_to_bv 64 (Z.shiftr (S + 152) 3 + SHB))])
sI a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
FR11 HD INS OBS11 S8 SPOS BS1 SOFF ST8 ltac:(clear - LOR DSP; unfold SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia) LOS SPH SPA MI11).
clear HD FST PT LE SEED CFG IDC PAD.
destruct POST as (m12 & xa212 & jh1 & -> & MU12 & WM12 & MI12 & ST12 & FR12 & HU1).
clear FR11.

assert (LOV : lo + RT_STACK + SB_LOOP_STACK <= usp + -1088) by (clear - LOR DSP; unfold RT_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
assert (LOV' : lo <= usp + -5120) by (clear - LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
assert (ART12 : X0ec.ART RT Σx m12).
{ apply (af_frame RT AF Σx m11 m12 lo ART11 LOWX); [| exact WM12]. intros a0 Ha. apply MU12. cbn [outside]. split; [| exact I].
intros Hin. apply Ha. left. clear - Hin LOV' SPT. unfold USTACK_TOP. lia. }
assert (PF12 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m12).
{ apply (pres_fp_trans _ _ _ _ m m11 m12 PF). apply (pres_fp_of_munch _ _ _ _ _ m11 m12 MU12). intros x Hx Ho. cbn [outside]. split; [| exact I].
intros Hin. destruct (SPL x Hx) as [H1 | H1]; clear - H1 Hin LOW LOV'; lia. }
clear PF. rename PF12 into PF.
pk_munch_all MU12 WM12 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LOV'; cbn [outside]; split; [lia| exact I])
ltac:(fun x Hx => clear - Hx LOV' LOS; cbn [outside]; split; [lia| exact I]).
trm MU12 WM12 SV ltac:(clear; lia).
trm MU12 WM12 FRB ltac:(clear - BF LOV'; lia).
trm MU12 WM12 FRS ltac:(clear - BF0 LOV'; lia).
trm MU12 WM12 OC ltac:(rewrite LOWS; clear - FO2 BF1 LOV'; lia).
trm MU12 WM12 STB ltac:(clear - FS2 BF1 LOV'; lia).
trm MU12 WM12 BOBJ8 ltac:(clear - FA2 BF1 LOV'; lia).
trm MU12 WM12 BDAT8 ltac:(clear - BD8 LOV'; lia).
trm MU12 WM12 X9 ltac:(clear - BS1 LOV'; lia).
clear ST8.
assert (OF12 : offsh [(usp + -4704, usp + -160)]) by (cbn [offsh]; clear - LOS LOV'; unfold SH_LO, SH_HI in *; lia).
assert (ACC12 : forall o n, acc asegs m11 o n -> 0 <= o -> o + n <= 140737488355328 -> acc asegs m12 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch asegs _ m11 m12 o n (conj H0 (conj H1 H)) MU12 (shfree_of_offsh _ o n OF12 H0 H1)))). }
assert (ACA12 : acc asegs m12 A 48) by (apply ACC12; [exact ACA11| clear - FA1 FP0; lia| clear - FA2 BF1 LO608 SPT; lia]).
assert (ACO12 : acc asegs m12 OUT 8000) by (apply ACC12; [exact ACO11| clear - FO1 FP0; lia| clear - FO2 BF1 LO608 SPT; lia]).
assert (ACT12 : acc asegs m12 STEREO 24) by (apply ACC12; [exact ACT11| clear - FS1 FP0; lia| clear - FS2 BF1 LO608 SPT; lia]).
assert (SSP12 : io_ssp m12).
{ apply (sbd_io_ssp_agree m11 m12 SSP11 (AF_DRV Σx m12 ART12)). intros a0 Ha. apply MU12. unfold X00a.SSP_GUARD in Ha. cbn [outside].
clear - Ha LOV' LOS. split; [lia| exact I]. }
destruct (af_acc_live RT AF Σx m12 S 160 ART12 INLX) as (_ & ACS12).
assert (OBS12 : aobj asegs m12 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO608 SPT; unfold APP_TOP; lia| exact ACS12]).
clear ACA11 ACO11 ACT11 ACC12 SSP11 ACS11 OBS11 ART11 MI11 OF11.

assert (EU704 : bv_unsigned (Z_to_bv 64 (usp + -704)) = usp + -704) by (apply unsigned_lit; clear - SPT LOV' LOS; lia).
assert (POA1 : pois_above (rt_pois RT Σx) (alloca_rr (usp + -672) 16)).
{ apply (pois_above_le _ usp); [rewrite EPX; exact POA|]. unfold alloca_rr. clear - SPA. Z.div_mod_to_equations. lia. }
assert (COK1 : call_ok RT Σx m12 (Z_to_bv 64 (usp + -704)) lo).
{ unfold call_ok. rewrite EU704. split; [exact ST12|]. split; [exact LOWX|]. split; [clear - LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia|].
split; [clear - SPT; unfold USTACK_TOP in *; lia| clear - SPA; Z.div_mod_to_equations; lia]. }
cps_rt (APO Σx (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m12 (usp + -672) 16 lo FDO MST eq_refl eq_refl
ltac:(clear - SPA; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(rewrite EU704; lia)
ltac:(unfold alloca_rr, USTACK_TOP; clear - SPA SPT; Z.div_mod_to_equations; lia)
POA1 ltac:(rewrite EFX; discriminate) ART12 MI12 COK1).
intros c5 (Σ1 & Hc5 & EP1 & EL1 & EF1 & ES1 & EC1).
destruct (ASTA_unpack RT Σ1 (PMfd F0 fs0) _ c5 Hc5) as (ms5 & PO5 & Hc5'); clear Hc5; cbv beta in PO5.
destruct PO5 as (m13 & v13 & RS13 & (ART13 & MI13 & WM13 & ST13) & PRES13 & ACV13 & ACK13).
cps_ret RS13.
rewrite EU704 in PRES13, ST13.
clear POA1 COK1.

assert (CLFg : forall L Fr sp' x, In (fh, kh) Fr -> fh <= x < fh + fs_size kh - 8 -> aclient L Fr sp' x)
by (intros L Fr sp' x HF Hx; right; right; right; left; exists fh, kh; split; [exact HF| exact Hx]).
assert (CLLg : forall L Fr sp' p n x, In (p, n) L -> p <= x < p + n -> aclient L Fr sp' x)
by (intros L Fr sp' p n x Hp Hx; right; right; left; exists p, n; split; [exact Hp| exact Hx]).
assert (CLF0g : forall L Fr sp' x, In (f, 0%nat) Fr -> f <= x < f + 56 -> aclient L Fr sp' x)
by (intros L Fr sp' x HF Hx; right; right; right; left; exists f, 0%nat; split; [exact HF| change (fs_size 0) with 64; lia]).
assert (CLSFg : forall L Fr sp' x, In (f, 0%nat) Fr -> sf <= x < sf + 8 -> aclient L Fr sp' x)
by (intros L Fr sp' x HF Hx; right; right; right; right; exists f, 0%nat; split; [exact HF| change (fs_size 0) with 64; rewrite <- SHF, SHF0; lia]).
assert (CLSg : forall L Fr sp' x, sp' <= x < usp -> aclient L Fr sp' x)
by (intros L Fr sp' x Hx; left; clear - Hx SPT; unfold USTACK_TOP in *; lia).

pose proof (pres_fp_of_pres _ _ _ [] _ _ PRES13) as PF13.
tr1 PF13 WM13 SV ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF13 WM13 FR12 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF13 WM13 HU1 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF13 WM13 FRB ltac:(fun x Hx => apply (CLF0g _ _ _ x INF); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF13 WM13 FRS ltac:(fun x Hx => apply (CLSFg _ _ _ x INF); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF13 WM13 OC ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); rewrite LOWS in Hx; clear - Hx FO1 FO2; lia) ltac:(fun x Hx => exact I).
tr1 PF13 WM13 STB ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FS1 FS2; lia) ltac:(fun x Hx => exact I).
tr1 PF13 WM13 BOBJ8 ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FA1 FA2; lia) ltac:(fun x Hx => exact I).
tr1 PF13 WM13 BDAT8 ltac:(fun x Hx => apply (CLLg _ _ _ PD ND x INPDX); clear - Hx PD1 PD2 Lbs8; lia) ltac:(fun x Hx => exact I).
tr1 PF13 WM13 X9 ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => exact I).
pk_pres_all RT PRES13 WM13 LALL LIVEA ERR_rep OUT_rep IO_FP IO_img.
assert (ACA13 : acc asegs m13 A 48) by (apply ACK13; [exact ACA12| clear - FA2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FA2 BF1 LOV'; lia]).
assert (ACO13 : acc asegs m13 OUT 8000) by (apply ACK13; [exact ACO12| clear - FO2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FO2 BF1 LOV'; lia]).
assert (ACT13 : acc asegs m13 STEREO 24) by (apply ACK13; [exact ACT12| clear - FS2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FS2 BF1 LOV'; lia]).
assert (ACS13 : acc asegs m13 S 160) by (apply ACK13; [exact ACS12| clear - BS1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - BS1 LOV'; lia]).
assert (OBS13 : aobj asegs m13 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO608 SPT; unfold APP_TOP; lia| exact ACS13]).
assert (SSP13 : io_ssp m13).
{ apply (sbd_io_ssp_agree m12 m13 SSP12 (AF_DRV Σ1 m13 ART13)). intros a0 Ha. apply PRES13. right; left. exact (sbd_ssp_static _ Ha). }
assert (PF13' : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m13).
{ apply (pres_fp_trans _ _ _ _ m m12 m13 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σx) (rt_frames RT Σx) (usp + -704) [] m12 m13 PF13).
- intros e He. rewrite ELX. exact He.
- intros e He. rewrite EFX. right. exact He.
- clear; lia.
- intros x _ _. exact I. }
clear PF. rename PF13' into PF.
clear ACA12 ACO12 ACT12 ACS12 OBS12 SSP12 ART12 MI12 ST12 PF13 PRES13 ACK13.

rewrite <- EL1 in LIVEA, LIVEL, LIVED, INLX, INPDX. rewrite <- EF1 in INF, INFHX. rewrite <- ES1 in LOWX.

sb_unpack X9 as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_v2 usp lo S OUT f (sbmode_struct (sbd_mode s)) _ sI a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
FR12 ltac:(gslot) HD INS OBS13 S8 SPOS BS1 SOFF ST13 ltac:(clear - LOV'; lia) LOS SPH SPA MI13).
clear HD FST PT LE SEED CFG IDC PAD.
destruct POST as (m14 & xa214 & jh2 & -> & MU14 & WM14 & MI14 & ST14 & FR14 & HU2).
clear FR12 ST13.
assert (ART14 : X0ec.ART RT Σ1 m14).
{ apply (af_frame RT AF Σ1 m13 m14 lo ART13 LOWX); [| exact WM14]. intros a0 Ha. apply MU14. cbn [outside]. split; [| exact I].
intros Hin. apply Ha. left. clear - Hin LOV' SPT. unfold USTACK_TOP. lia. }
assert (PF14 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m14).
{ apply (pres_fp_trans _ _ _ _ m m13 m14 PF). apply (pres_fp_of_munch _ _ _ _ _ m13 m14 MU14). intros x Hx Ho. cbn [outside]. split; [| exact I].
intros Hin. destruct (SPL x Hx) as [H1 | H1]; clear - H1 Hin LOW LOV'; lia. }
clear PF. rename PF14 into PF.
pk_munch_all MU14 WM14 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LOV'; cbn [outside]; split; [lia| exact I])
ltac:(fun x Hx => clear - Hx LOV' LOS; cbn [outside]; split; [lia| exact I]).
trm MU14 WM14 SV ltac:(clear; lia).
trm MU14 WM14 FRB ltac:(clear - BF LOV'; lia).
trm MU14 WM14 FRS ltac:(clear - BF0 LOV'; lia).
trm MU14 WM14 OC ltac:(rewrite LOWS; clear - FO2 BF1 LOV'; lia).
trm MU14 WM14 STB ltac:(clear - FS2 BF1 LOV'; lia).
trm MU14 WM14 BOBJ8 ltac:(clear - FA2 BF1 LOV'; lia).
trm MU14 WM14 BDAT8 ltac:(clear - BD8 LOV'; lia).
trm MU14 WM14 X9 ltac:(clear - BS1 LOV'; lia).

destruct (wr_at_rw_CB m14 (usp + -704) 96 (wr_at_transport asegs m13 m14 _ _ (proj2 HU1) WM14) ltac:(lia)) as (jh1' & HU1'). clear HU1 jh1. rename HU1' into HU1. rename jh1' into jh1.
assert (OF14 : offsh [(usp + -4800, usp + -160)]) by (cbn [offsh]; clear - LOS LOV'; unfold SH_LO, SH_HI in *; lia).
assert (ACC14 : forall o n, acc asegs m13 o n -> 0 <= o -> o + n <= 140737488355328 -> acc asegs m14 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch asegs _ m13 m14 o n (conj H0 (conj H1 H)) MU14 (shfree_of_offsh _ o n OF14 H0 H1)))). }
assert (ACA14 : acc asegs m14 A 48) by (apply ACC14; [exact ACA13| clear - FA1 FP0; lia| clear - FA2 BF1 LO608 SPT; lia]).
assert (ACO14 : acc asegs m14 OUT 8000) by (apply ACC14; [exact ACO13| clear - FO1 FP0; lia| clear - FO2 BF1 LO608 SPT; lia]).
assert (ACT14 : acc asegs m14 STEREO 24) by (apply ACC14; [exact ACT13| clear - FS1 FP0; lia| clear - FS2 BF1 LO608 SPT; lia]).
assert (ACV14 : acc asegs m14 (usp + -672) 16) by (apply ACC14; [exact ACV13| clear - LOV' LOS; lia| clear - SPT; lia]).
assert (SSP14 : io_ssp m14).
{ apply (sbd_io_ssp_agree m13 m14 SSP13 (AF_DRV Σ1 m14 ART14)). intros a0 Ha. apply MU14. unfold X00a.SSP_GUARD in Ha. cbn [outside].
clear - Ha LOV' LOS. split; [lia| exact I]. }
destruct (af_acc_live RT AF Σ1 m14 S 160 ART14 INLX) as (_ & ACS14).
assert (OBS14 : aobj asegs m14 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO608 SPT; unfold APP_TOP; lia| exact ACS14]).
clear ACA13 ACO13 ACT13 ACV13 ACC14 SSP13 ACS13 OBS13 ART13 MI13 OF14 MU14.

assert (EU800 : bv_unsigned (Z_to_bv 64 (usp + -800)) = usp + -800) by (apply unsigned_lit; clear - SPT LOV' LOS; lia).
assert (POA2 : pois_above (rt_pois RT Σ1) (alloca_rr (usp + -768) 16)).
{ intros e He. rewrite EP1 in He. destruct He as [<- | He].
- unfold pz_lo, alloca_rr. cbn [fst]. clear - SPA. Z.div_mod_to_equations. lia.
- rewrite EPX in He. pose proof (POA e He) as H1. unfold alloca_rr. clear - H1 SPA. Z.div_mod_to_equations. lia. }
assert (COK2 : call_ok RT Σ1 m14 (Z_to_bv 64 (usp + -800)) lo).
{ unfold call_ok. rewrite EU800. split; [exact ST14|]. split; [exact LOWX|]. split; [clear - LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia|].
split; [clear - SPT; unfold USTACK_TOP in *; lia| clear - SPA; Z.div_mod_to_equations; lia]. }
cps_rt (APO Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m14 (usp + -768) 16 lo FDO MST eq_refl eq_refl
ltac:(clear - SPA; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(rewrite EU800; lia)
ltac:(unfold alloca_rr, USTACK_TOP; clear - SPA SPT; Z.div_mod_to_equations; lia)
POA2 ltac:(rewrite EF1, EFX; discriminate) ART14 MI14 COK2).
intros c6 (Σ2 & Hc6 & EP2 & EL2 & EF2 & ES2 & EC2).
destruct (ASTA_unpack RT Σ2 (PMfd F0 fs0) _ c6 Hc6) as (ms6 & PO6 & Hc6'); clear Hc6; cbv beta in PO6.
destruct PO6 as (m15 & v15 & RS15 & (ART15 & MI15 & WM15 & ST15) & PRES15 & ACV15 & ACK15).
cps_ret RS15.
rewrite EU800 in PRES15, ST15.
clear POA2 COK2.
pose proof (pres_fp_of_pres _ _ _ [] _ _ PRES15) as PF15.
tr1 PF15 WM15 SV ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF15 WM15 FR14 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF15 WM15 HU1 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF15 WM15 HU2 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF15 WM15 FRB ltac:(fun x Hx => apply (CLF0g _ _ _ x INF); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF15 WM15 FRS ltac:(fun x Hx => apply (CLSFg _ _ _ x INF); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF15 WM15 OC ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); rewrite LOWS in Hx; clear - Hx FO1 FO2; lia) ltac:(fun x Hx => exact I).
tr1 PF15 WM15 STB ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FS1 FS2; lia) ltac:(fun x Hx => exact I).
tr1 PF15 WM15 BOBJ8 ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FA1 FA2; lia) ltac:(fun x Hx => exact I).
tr1 PF15 WM15 BDAT8 ltac:(fun x Hx => apply (CLLg _ _ _ PD ND x INPDX); clear - Hx PD1 PD2 Lbs8; lia) ltac:(fun x Hx => exact I).
tr1 PF15 WM15 X9 ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => exact I).
pk_pres_all RT PRES15 WM15 LALL LIVEA ERR_rep OUT_rep IO_FP IO_img.
assert (ACA15 : acc asegs m15 A 48) by (apply ACK15; [exact ACA14| clear - FA2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FA2 BF1 LOV'; lia]).
assert (ACO15 : acc asegs m15 OUT 8000) by (apply ACK15; [exact ACO14| clear - FO2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FO2 BF1 LOV'; lia]).
assert (ACT15 : acc asegs m15 STEREO 24) by (apply ACK15; [exact ACT14| clear - FS2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FS2 BF1 LOV'; lia]).
assert (ACS15 : acc asegs m15 S 160) by (apply ACK15; [exact ACS14| clear - BS1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - BS1 LOV'; lia]).
assert (ACV15a : acc asegs m15 (usp + -672) 16)
by (apply ACK15; [exact ACV14| clear - SPT; unfold USTACK_TOP; lia| right; unfold alloca_rr; clear - SPA; Z.div_mod_to_equations; lia]).
assert (OBS15 : aobj asegs m15 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO608 SPT; unfold APP_TOP; lia| exact ACS15]).
assert (SSP15 : io_ssp m15).
{ apply (sbd_io_ssp_agree m14 m15 SSP14 (AF_DRV Σ2 m15 ART15)). intros a0 Ha. apply PRES15. right; left. exact (sbd_ssp_static _ Ha). }
assert (PF15' : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m15).
{ apply (pres_fp_trans _ _ _ _ m m14 m15 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -800) [] m14 m15 PF15).
- intros e He. rewrite EL1, ELX. exact He.
- intros e He. rewrite EF1, EFX. right. exact He.
- clear; lia.
- intros x _ _. exact I. }
clear PF. rename PF15' into PF.
clear ACA14 ACO14 ACT14 ACS14 ACV14 OBS14 SSP14 ART14 MI14 ST14 PF15 PRES15 ACK15.
rename ACV15 into ACW15. rename ACV15a into ACV15.
rewrite <- EL2 in LIVEA, LIVEL, LIVED, INLX, INPDX. rewrite <- EF2 in INF, INFHX. rewrite <- ES2 in LOWX.

sb_unpack X9 as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_v3 usp S OUT f (sbmode_struct (sbd_mode s)) _ sI a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
FR14 ltac:(gslot) HD OBS15 S8 SPOS ltac:(clear - BS1 LOV'; lia) SOFF ltac:(clear - LOS LOV'; unfold SH_HI in *; lia) SPH MI15).
clear HD FST PT LE SEED CFG IDC PAD.
destruct POST as (m16 & -> & MU16 & WM16 & MI16 & FR16).
clear FR14.
assert (ART16 : X0ec.ART RT Σ2 m16).
{ apply (af_frame RT AF Σ2 m15 m16 lo ART15 LOWX); [| exact WM16]. intros a0 Ha. apply MU16. cbn [outside]. split; [| exact I].
intros Hin. apply Ha. left. clear - Hin LOV' SPT. unfold USTACK_TOP. lia. }
assert (PF16 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m16).
{ apply (pres_fp_trans _ _ _ _ m m15 m16 PF). apply (pres_fp_of_munch _ _ _ _ _ m15 m16 MU16). intros x Hx Ho. cbn [outside]. split; [| exact I].
intros Hin. destruct (SPL x Hx) as [H1 | H1]; clear - H1 Hin LOW LOV'; lia. }
clear PF. rename PF16 into PF.
pk_munch_all MU16 WM16 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LOV'; cbn [outside]; split; [lia| exact I])
ltac:(fun x Hx => clear - Hx LOV' LOS; cbn [outside]; split; [lia| exact I]).
trm MU16 WM16 SV ltac:(clear; lia).
trm MU16 WM16 HU1 ltac:(clear; lia).
trm MU16 WM16 HU2 ltac:(clear; lia).
trm MU16 WM16 FRB ltac:(clear - BF LOV'; lia).
trm MU16 WM16 FRS ltac:(clear - BF0 LOV'; lia).
trm MU16 WM16 OC ltac:(rewrite LOWS; clear - FO2 BF1 LOV'; lia).
trm MU16 WM16 STB ltac:(clear - FS2 BF1 LOV'; lia).
trm MU16 WM16 BOBJ8 ltac:(clear - FA2 BF1 LOV'; lia).
trm MU16 WM16 BDAT8 ltac:(clear - BD8 LOV'; lia).
trm MU16 WM16 X9 ltac:(clear - BS1 LOV'; lia).
apply (stk_transport_disjoint asegs [(usp + -608, usp + -160)] m15 m16 lo (usp + -800)) in ST15; [| exact MU16 | exact WM16 | cbn [disjoint_from]; clear; lia].
assert (OF16 : offsh [(usp + -608, usp + -160)]) by (cbn [offsh]; clear - LOS LOV'; unfold SH_LO, SH_HI in *; lia).
assert (ACC16 : forall o n, acc asegs m15 o n -> 0 <= o -> o + n <= 140737488355328 -> acc asegs m16 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch asegs _ m15 m16 o n (conj H0 (conj H1 H)) MU16 (shfree_of_offsh _ o n OF16 H0 H1)))). }
assert (ACA16 : acc asegs m16 A 48) by (apply ACC16; [exact ACA15| clear - FA1 FP0; lia| clear - FA2 BF1 LO608 SPT; lia]).
assert (ACO16 : acc asegs m16 OUT 8000) by (apply ACC16; [exact ACO15| clear - FO1 FP0; lia| clear - FO2 BF1 LO608 SPT; lia]).
assert (ACT16 : acc asegs m16 STEREO 24) by (apply ACC16; [exact ACT15| clear - FS1 FP0; lia| clear - FS2 BF1 LO608 SPT; lia]).
assert (ACV16 : acc asegs m16 (usp + -672) 16) by (apply ACC16; [exact ACV15| clear - LOV' LOS; lia| clear - SPT; lia]).
assert (ACW16 : acc asegs m16 (usp + -768) 16) by (apply ACC16; [exact ACW15| clear - LOV' LOS; lia| clear - SPT; lia]).
assert (SSP16 : io_ssp m16).
{ apply (sbd_io_ssp_agree m15 m16 SSP15 (AF_DRV Σ2 m16 ART16)). intros a0 Ha. apply MU16. unfold X00a.SSP_GUARD in Ha. cbn [outside].
clear - Ha LOV' LOS. split; [lia| exact I]. }
destruct (af_acc_live RT AF Σ2 m16 S 160 ART16 INLX) as (_ & ACS16).
assert (OBS16 : aobj asegs m16 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO608 SPT; unfold APP_TOP; lia| exact ACS16]).
clear ACA15 ACO15 ACT15 ACV15 ACW15 ACC16 SSP15 ACS15 OBS15 ART15 MI15 OF16 MU16.
clear Hc Hc0.

apply (rw_cells_split_CB asegs _ _ [] 96 _ [] [32; 16; 48]%nat) in HU1; [| reflexivity]. cbn [mk_CB_cells app] in HU1.
apply rw_cells_uncons in HU1. destruct HU1 as (RZ1a & HU1). apply rw_cells_uncons in HU1. destruct HU1 as (PG1 & RZ1b).
cbn [csize] in PG1, RZ1b.
replace (usp + -704 + Z.of_nat 32) with (usp + -672) in PG1, RZ1b by lia. replace (usp + -672 + Z.of_nat 16) with (usp + -656) in RZ1b by lia.
destruct (rw_cells_CB_f32 asegs m16 (usp + -672) 4 _ PG1) as (pg0 & Lpg0 & PGW). clear PG1.

assert (NDL : List.NoDup (map blk_id LBL)) by (pose proof NDUP as ND'; rewrite ELBD, map_app in ND'; exact (List.NoDup_app_remove_l _ _ ND')).
assert (AL8L : blocks_al8 LBL) by (intros bk Hb; apply LAL8; rewrite ELBD; apply in_app_iff; right; exact Hb).
assert (DEP3 : (dec_depth low3 <= 3)%nat) by (rewrite DL3; clear - DEPL; lia).
assert (FRM3 : (length (rt_frames RT Σ2) + dec_depth low3 <= FRAMES_MAX)%nat)
by (rewrite EF2, EF1, EFX, DL3; cbn [length]; pose proof (dec_depth_le_frames low) as DF; clear - FRM DF; lia).
assert (CRL3 : Z.of_nat (dec_depth low3) <= rt_credit RT Σ2 + 1)
by (rewrite EC2, EC1, DL3; pose proof (dec_credit_pos low) as DP; pose proof (dec_depth_pos low) as DP2; clear - CBX CRD DP DP2; lia).
assert (POA3 : pois_above (rt_pois RT Σ2) (bv_unsigned (Z_to_bv 64 (usp + -800)))).
{ rewrite EU800. intros e He. rewrite EP2, EP1 in He. destruct He as [<- | [<- | He]]; [unfold pz_lo; cbn [fst]; clear; lia| unfold pz_lo; cbn [fst]; clear; lia|].
rewrite EPX in He. pose proof (POA e He) as H1. clear - H1. lia. }
assert (ST800 : stk asegs m16 lo (bv_unsigned (Z_to_bv 64 (usp + -800)))) by (rewrite EU800; exact ST15).
assert (LORC : lo + RT_STACK + ctl_stack low3 <= bv_unsigned (Z_to_bv 64 (usp + -800))).
{ rewrite EU800. destruct (dec_res_depth low3 low DL3) as (_ & _ & _ & RT3). rewrite RT3. pose proof (ctl_stack_le_dec low) as CL. clear - LOR CL. unfold RT_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in *. lia. }
assert (SPT800 : bv_unsigned (Z_to_bv 64 (usp + -800)) + 16 <= USTACK_TOP) by (rewrite EU800; clear - SPT; unfold USTACK_TOP in *; lia).
assert (SPA800 : bv_unsigned (Z_to_bv 64 (usp + -800)) mod 32 = 0) by (rewrite EU800; clear - SPA; Z.div_mod_to_equations; lia).
assert (DSTO : dst_obj RT Σ2 m16 (usp + -672) (creq_size CtlGetPiGain)) by (right; rewrite EP2, EP1; right; left; reflexivity).
cps_rt (CTL3 low3 DL3 Σ2 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m16 OUT OUT STEREO (a_low a) LBL CtlGetPiGain (usp + -672) lo
FDO MST eq_refl eq_refl eq_refl eq_refl eq_refl RLOW eq_refl DEP3 NDL AL8L I (ex_intro _ pg0 (conj PGW Lpg0)) LIVEL DSTO FRM3 CRL3 POA3
ART16 MI16 FRMX ST800 LOWX LORC SPT800 SPA800).
intros c8 (Σ3 & Hc8 & EL3 & EF3 & ES3 & EC3 & EP3).
cps_unpack_lib Hc8 as (m17 & RS17 & (ART17 & MI17 & WM17 & ST17) & PRES17 & RLOW17 & CP17 & EXK17 & DST17).
try rewrite EU800 in PRES17. try rewrite EU800 in ST17.
cbn [creq_ivs creq_size app] in PRES17. cbn [creq_post] in CP17. destruct CP17 as (pg1 & PGW1 & Lpg1).
clear DST17 DSTO PGW Lpg0 pg0 POA3 ST800 LORC SPT800 SPA800 FRM3 CRL3.

assert (OLB : forall x, (lo <= x \/ S <= x < S + 160 \/ fh <= x < fh + fs_size kh \/ PD <= x < PD + ND \/ f <= x < f + 64 \/ sf <= x < sf + 8 \/ 65536 <= x < 6627328) ->
(x < usp + -672 \/ usp + -656 <= x) -> outside ((usp + -672, usp + -672 + 16) :: blocks_ivs LBL) x).
{ intros x H1 H2. cbn [outside]. split; [clear - H2; lia| exact (OUTB x H1)]. }
tr1 PRES17 WM17 SV ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => apply OLB; [left; clear - Hx LO608; lia| clear - Hx; lia]).
tr1 PRES17 WM17 FR16 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => apply OLB; [left; clear - Hx LO608; lia| clear - Hx; lia]).
tr1 PRES17 WM17 RZ1a ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => apply OLB; [left; clear - Hx LOV'; lia| clear - Hx; lia]).
tr1 PRES17 WM17 RZ1b ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => apply OLB; [left; clear - Hx LOV'; lia| clear - Hx; lia]).
tr1 PRES17 WM17 HU2 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => apply OLB; [left; clear - Hx LOV'; lia| clear - Hx; lia]).
tr1 PRES17 WM17 FRB ltac:(fun x Hx => apply (CLF0g _ _ _ x INF); clear - Hx; lia)
ltac:(fun x Hx => apply OLB; [right; right; right; right; left; clear - Hx; lia| clear - Hx BF LOV'; lia]).
tr1 PRES17 WM17 FRS ltac:(fun x Hx => apply (CLSFg _ _ _ x INF); clear - Hx; lia)
ltac:(fun x Hx => apply OLB; [right; right; right; right; right; left; clear - Hx; lia| clear - Hx BF0 LOV'; lia]).
tr1 PRES17 WM17 OC ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); rewrite LOWS in Hx; clear - Hx FO1 FO2; lia)
ltac:(fun x Hx => apply OLB; [right; right; left; rewrite LOWS in Hx; clear - Hx FO1 FO2; lia| rewrite LOWS in Hx; clear - Hx FO2 BF1 LOV'; lia]).
tr1 PRES17 WM17 STB ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FS1 FS2; lia)
ltac:(fun x Hx => apply OLB; [right; right; left; clear - Hx FS1 FS2; lia| clear - Hx FS2 BF1 LOV'; lia]).
tr1 PRES17 WM17 BOBJ8 ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FA1 FA2; lia)
ltac:(fun x Hx => apply OLB; [right; right; left; clear - Hx FA1 FA2; lia| clear - Hx FA2 BF1 LOV'; lia]).
tr1 PRES17 WM17 BDAT8 ltac:(fun x Hx => apply (CLLg _ _ _ PD ND x INPDX); clear - Hx PD1 PD2 Lbs8; lia)
ltac:(fun x Hx => apply OLB; [right; right; right; left; clear - Hx PD1 PD2 Lbs8; lia| clear - Hx BD8 LOV'; lia]).
tr1 PRES17 WM17 X9 ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia)
ltac:(fun x Hx => apply OLB; [right; left; clear - Hx; lia| clear - Hx BS1 LOV'; lia]).
assert (AGB17 : agree_blocks asegs m16 m17 (tl (sb_blocks s S a))).
{ apply (agree_blocks_of_pres_fp RT Σ2 _ _ _ m16 m17 _ PRES17 WM17); [intros bk Hb; apply LIVEA; unfold LALL; apply in_app_iff; left; exact Hb|].
intros bk x Hb Hx. pose proof (BOUT bk x ltac:(unfold LALL; apply in_app_iff; left; exact Hb) Hx) as H1. cbn [outside].
split; [clear - H1 LOV'; lia| exact (APL bk x Hb Hx)]. }
apply (sb_bufs_agree s S a j m16 m17) in BUFS; [| exact JOK | exact AGB17]. clear AGB17.
pk_io_fp PRES17 ERR_rep OUT_rep IO_FP IO_img ltac:(fun y Hy => apply OLB; [right; right; right; right; right; right; clear - Hy; lia| clear - Hy LOV' LOS; lia]).
assert (SSP17 : io_ssp m17).
{ apply (sbd_io_ssp_agree m16 m17 SSP16 (AF_DRV Σ3 m17 ART17)). intros a0 Ha. apply PRES17; [right; left; exact (sbd_ssp_static _ Ha)|].
unfold X00a.SSP_GUARD in Ha. apply OLB; [right; right; right; right; right; right; clear - Ha; lia| clear - Ha LOV' LOS; lia]. }
assert (SHW17 : forall o n, fh <= o -> o + n <= fh + fs_size kh -> forall i, 0 <= i < n -> outside ((usp + -672, usp + -672 + 16) :: blocks_ivs LBL) (shad (o + i))).
{ intros o n H1 H2 i Hi.
assert (SR : SH_LO <= shad (o + i) < SH_HI).
{ pose proof (frame_facts RT AF Σ2 m16 fh kh ART16 INFHX) as (_ & _ & _ & _ & _ & _ & SA & SL & SH & _). split.
- unfold shad, SH_LO, SHB in *. assert (0 <= (o + i) / 8) by (apply Z.div_pos; lia). lia.
- assert (shad (o + i) < shad (fh + fs_size kh)); [| lia].
unfold shad. apply Z.add_lt_mono_r. apply Z.div_lt_upper_bound; [lia|].
assert (FH8 : fh mod 8 = 0) by (clear - FP64; Z.div_mod_to_equations; lia).
assert (FK8 : fs_size kh mod 8 = 0) by (destruct FS64 as (M64 & _); clear - M64; Z.div_mod_to_equations; lia).
assert (E : fh + fs_size kh = 8 * ((fh + fs_size kh) / 8)).
{ pose proof (Z.div_mod (fh + fs_size kh) 8 ltac:(lia)) as XD. rewrite Zplus_mod, FH8, FK8 in XD. cbn in XD. lia. }
lia. }
cbn [outside]. split; [clear - SR LOS LOV'; unfold SH_LO, SH_HI in *; lia|].
exact (outside_blocks_shadow RT AF Σ2 m16 LBL _ ART16 LIVEL SR). }
assert (FH8 : fh mod 8 = 0) by (clear - FP64; Z.div_mod_to_equations; lia).
assert (FK8 : fs_size kh mod 8 = 0) by (destruct FS64 as (M64 & _); clear - M64; Z.div_mod_to_equations; lia).
assert (ACA17 : acc asegs m17 A 48)
by (apply (acc_pres_fp_frame _ _ _ _ m16 m17 fh kh A 48 PRES17 INFHX FH8 FK8 ltac:(lia) FA1 ltac:(lia) (SHW17 A 48 FA1 ltac:(lia)) ACA16)).
assert (ACO17 : acc asegs m17 OUT 8000)
by (apply (acc_pres_fp_frame _ _ _ _ m16 m17 fh kh OUT 8000 PRES17 INFHX FH8 FK8 ltac:(lia) FO1 ltac:(lia) (SHW17 OUT 8000 FO1 ltac:(lia)) ACO16)).
assert (ACT17 : acc asegs m17 STEREO 24)
by (apply (acc_pres_fp_frame _ _ _ _ m16 m17 fh kh STEREO 24 PRES17 INFHX FH8 FK8 ltac:(lia) FS1 ltac:(lia) (SHW17 STEREO 24 FS1 ltac:(lia)) ACT16)).
assert (PF17 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m17).
{ apply (pres_fp_trans _ _ _ _ m m16 m17 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ2) (rt_frames RT Σ2) (usp + -800) _ m16 m17 PRES17).
- intros e He. rewrite EL2, EL1, ELX. exact He.
- intros e He. rewrite EF2, EF1, EFX. right. exact He.
- clear; lia.
- intros x Hx Ho. cbn [outside] in Ho. destruct Ho as (_ & _ & _ & Ho). apply sb_outside_app_inv in Ho. destruct Ho as [Hb _].
rewrite ELBD in Hb. cbn [outside]. split; [destruct (SPL x Hx) as [H1 | H1]; clear - H1 LOW LOV'; lia| exact (outside_blocks_app_r _ _ x Hb)]. }
clear PF. rename PF17 into PF.
destruct (af_acc_live RT AF Σ3 m17 S 160 ART17 ltac:(rewrite EL3; exact INLX)) as (_ & ACS17).
assert (OBS17 : aobj asegs m17 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO608 SPT; unfold APP_TOP; lia| exact ACS17]).
assert (EXR17 : EXCREADY m17 (a_low a) (speex_decoder_ctl low3 CtlGetPiGain).2) by (apply EXK17; apply EXR0; reflexivity).
clear EXK17 EXR0 RLOW SHW17 ACA16 ACO16 ACT16 ACV16 ACW16 SSP16 ACS16 OBS16 ART16 MI16 ST15 PRES17 OLB.
rename RLOW17 into RLOW.
rewrite <- EL3 in LIVEA, LIVEL, LIVED, INLX, INPDX. rewrite <- EF3 in INF, INFHX. rewrite <- ES3 in LOWX.

assert (EXR0 : 0 = 0 -> EXCREADY m17 (a_low a) (speex_decoder_ctl low3 CtlGetPiGain).2) by (intros _; exact EXR17). clear EXR17.
sb_unpack X9 as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_v4 usp S OUT f (sbmode_struct (sbd_mode s)) _ sI a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
FR16 ltac:(gslot) HD OBS17 S8 SPOS ltac:(clear - BS1 LOV'; lia) SOFF ltac:(clear - LOS LOV'; unfold SH_HI in *; lia) SPH MI17).
clear HD FST PT LE SEED CFG IDC PAD.
destruct POST as (m18 & -> & MU18 & WM18 & MI18 & FR18).
clear FR16.
assert (ART18 : X0ec.ART RT Σ3 m18).
{ apply (af_frame RT AF Σ3 m17 m18 lo ART17 LOWX); [| exact WM18]. intros a0 Ha. apply MU18. cbn [outside]. split; [| exact I].
intros Hin. apply Ha. left. clear - Hin LOV' SPT. unfold USTACK_TOP. lia. }
assert (PF18 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m18).
{ apply (pres_fp_trans _ _ _ _ m m17 m18 PF). apply (pres_fp_of_munch _ _ _ _ _ m17 m18 MU18). intros x Hx Ho. cbn [outside]. split; [| exact I].
intros Hin. destruct (SPL x Hx) as [H1 | H1]; clear - H1 Hin LOW LOV'; lia. }
clear PF. rename PF18 into PF.
pk_munch_all MU18 WM18 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LOV'; cbn [outside]; split; [lia| exact I])
ltac:(fun x Hx => clear - Hx LOV' LOS; cbn [outside]; split; [lia| exact I]).
trm MU18 WM18 SV ltac:(clear; lia).
trm MU18 WM18 RZ1a ltac:(clear; lia).
trm MU18 WM18 PGW1 ltac:(rewrite Lpg1; clear; lia).
trm MU18 WM18 RZ1b ltac:(clear; lia).
trm MU18 WM18 HU2 ltac:(clear; lia).
trm MU18 WM18 FRB ltac:(clear - BF LOV'; lia).
trm MU18 WM18 FRS ltac:(clear - BF0 LOV'; lia).
trm MU18 WM18 OC ltac:(rewrite LOWS; clear - FO2 BF1 LOV'; lia).
trm MU18 WM18 STB ltac:(clear - FS2 BF1 LOV'; lia).
trm MU18 WM18 BOBJ8 ltac:(clear - FA2 BF1 LOV'; lia).
trm MU18 WM18 BDAT8 ltac:(clear - BD8 LOV'; lia).
trm MU18 WM18 X9 ltac:(clear - BS1 LOV'; lia).
apply (stk_transport_disjoint asegs [(usp + -608, usp + -160)] m17 m18 lo (usp + -800)) in ST17; [| exact MU18 | exact WM18 | cbn [disjoint_from]; clear; lia].
assert (OF18 : offsh [(usp + -608, usp + -160)]) by (cbn [offsh]; clear - LOS LOV'; unfold SH_LO, SH_HI in *; lia).
assert (ACC18 : forall o n, acc asegs m17 o n -> 0 <= o -> o + n <= 140737488355328 -> acc asegs m18 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch asegs _ m17 m18 o n (conj H0 (conj H1 H)) MU18 (shfree_of_offsh _ o n OF18 H0 H1)))). }
assert (ACA18 : acc asegs m18 A 48) by (apply ACC18; [exact ACA17| clear - FA1 FP0; lia| clear - FA2 BF1 LO608 SPT; lia]).
assert (ACO18 : acc asegs m18 OUT 8000) by (apply ACC18; [exact ACO17| clear - FO1 FP0; lia| clear - FO2 BF1 LO608 SPT; lia]).
assert (ACT18 : acc asegs m18 STEREO 24) by (apply ACC18; [exact ACT17| clear - FS1 FP0; lia| clear - FS2 BF1 LO608 SPT; lia]).
assert (SSP18 : io_ssp m18).
{ apply (sbd_io_ssp_agree m17 m18 SSP17 (AF_DRV Σ3 m18 ART18)). intros a0 Ha. apply MU18. unfold X00a.SSP_GUARD in Ha. cbn [outside].
clear - Ha LOV' LOS. split; [lia| exact I]. }
destruct (af_acc_live RT AF Σ3 m18 S 160 ART18 INLX) as (_ & ACS18).
assert (OBS18 : aobj asegs m18 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO608 SPT; unfold APP_TOP; lia| exact ACS18]).
clear ACA17 ACO17 ACT17 ACC18 SSP17 ACS17 OBS17 ART17 MI17 OF18 MU18.

apply (rw_cells_split_CB asegs _ _ [] 96 _ [] [32; 16; 48]%nat) in HU2; [| reflexivity]. cbn [mk_CB_cells app] in HU2.
apply rw_cells_uncons in HU2. destruct HU2 as (RZ2a & HU2). apply rw_cells_uncons in HU2. destruct HU2 as (ER2 & RZ2b).
cbn [csize] in ER2, RZ2b.
replace (usp + -800 + Z.of_nat 32) with (usp + -768) in ER2, RZ2b by lia. replace (usp + -768 + Z.of_nat 16) with (usp + -752) in RZ2b by lia.
destruct (rw_cells_CB_f32 asegs m18 (usp + -768) 4 _ ER2) as (er0 & Ler0 & ERW). clear ER2.

assert (DL4 : dec_depth (speex_decoder_ctl low3 CtlGetPiGain).2 = dec_depth low) by (rewrite ctl_keeps_depth; exact DL3).
assert (DEP4 : (dec_depth (speex_decoder_ctl low3 CtlGetPiGain).2 <= 3)%nat) by (rewrite DL4; clear - DEPL; lia).
assert (FRM4 : (length (rt_frames RT Σ3) + dec_depth (speex_decoder_ctl low3 CtlGetPiGain).2 <= FRAMES_MAX)%nat)
by (rewrite EF3, EF2, EF1, EFX, DL4; cbn [length]; pose proof (dec_depth_le_frames low) as DF; clear - FRM DF; lia).
assert (CRL4 : Z.of_nat (dec_depth (speex_decoder_ctl low3 CtlGetPiGain).2) <= rt_credit RT Σ3 + 1).
{ rewrite DL4. rewrite DL3 in EC3. rewrite EC2, EC1 in EC3. pose proof (dec_credit_pos low) as DP. pose proof (dec_depth_pos low) as DP2. clear - CBX CRD DP DP2 EC3. lia. }
assert (POA4 : pois_above (rt_pois RT Σ3) (bv_unsigned (Z_to_bv 64 (usp + -800)))).
{ rewrite EU800. intros e He. rewrite EP3, EP2, EP1 in He. destruct He as [<- | [<- | He]]; [unfold pz_lo; cbn [fst]; clear; lia| unfold pz_lo; cbn [fst]; clear; lia|].
rewrite EPX in He. pose proof (POA e He) as H1. clear - H1. lia. }
assert (ST800 : stk asegs m18 lo (bv_unsigned (Z_to_bv 64 (usp + -800)))) by (rewrite EU800; exact ST17).
assert (LORC : lo + RT_STACK + ctl_stack (speex_decoder_ctl low3 CtlGetPiGain).2 <= bv_unsigned (Z_to_bv 64 (usp + -800))).
{ rewrite EU800. destruct (dec_res_depth _ low DL4) as (_ & _ & _ & RT4). rewrite RT4. pose proof (ctl_stack_le_dec low) as CL. clear - LOR CL.
unfold RT_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in *. lia. }
assert (SPT800 : bv_unsigned (Z_to_bv 64 (usp + -800)) + 16 <= USTACK_TOP) by (rewrite EU800; clear - SPT; unfold USTACK_TOP in *; lia).
assert (SPA800 : bv_unsigned (Z_to_bv 64 (usp + -800)) mod 32 = 0) by (rewrite EU800; clear - SPA; Z.div_mod_to_equations; lia).
assert (DSTO : dst_obj RT Σ3 m18 (usp + -768) (creq_size CtlGetExc)) by (right; rewrite EP3, EP2; left; reflexivity).
cps_rt (CTL3 _ DL4 Σ3 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m18 OUT OUT STEREO (a_low a) LBL CtlGetExc (usp + -768) lo
FDO MST eq_refl eq_refl eq_refl eq_refl eq_refl RLOW eq_refl DEP4 NDL AL8L I (conj (ex_intro _ er0 (conj ERW Ler0)) (EXR eq_refl)) LIVEL DSTO FRM4 CRL4 POA4
ART18 MI18 RS17 ST800 LOWX LORC SPT800 SPA800).
intros c10 (Σ4 & Hc10 & EL4 & EF4 & ES4 & EC4 & EP4).
cps_unpack_lib Hc10 as (m19 & RS19 & (ART19 & MI19 & WM19 & ST19) & PRES19 & RLOW19 & CP19 & EXK19 & DST19).
try rewrite EU800 in PRES19. try rewrite EU800 in ST19.
cbn [creq_ivs creq_size app] in PRES19. cbn [creq_post] in CP19. destruct CP19 as (er1 & ERW1 & Ler1).
clear DST19 DSTO ERW Ler0 er0 POA4 ST800 LORC SPT800 SPA800 FRM4 CRL4.

assert (OLB : forall x, (lo <= x \/ S <= x < S + 160 \/ fh <= x < fh + fs_size kh \/ PD <= x < PD + ND \/ f <= x < f + 64 \/ sf <= x < sf + 8 \/ 65536 <= x < 6627328) ->
(x < usp + -768 \/ usp + -752 <= x) -> outside ((usp + -768, usp + -768 + 16) :: blocks_ivs LBL) x).
{ intros x H1 H2. cbn [outside]. split; [clear - H2; lia| exact (OUTB x H1)]. }
tr1 PRES19 WM19 SV ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => apply OLB; [left; clear - Hx LO608; lia| clear - Hx; lia]).
tr1 PRES19 WM19 FR18 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => apply OLB; [left; clear - Hx LO608; lia| clear - Hx; lia]).
tr1 PRES19 WM19 RZ1a ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => apply OLB; [left; clear - Hx LOV'; lia| clear - Hx; lia]).
tr1 PRES19 WM19 RZ1b ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => apply OLB; [left; clear - Hx LOV'; lia| clear - Hx; lia]).
tr1 PRES19 WM19 RZ2a ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => apply OLB; [left; clear - Hx LOV'; lia| clear - Hx; lia]).
tr1 PRES19 WM19 RZ2b ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => apply OLB; [left; clear - Hx LOV'; lia| clear - Hx; lia]).
tr1 PRES19 WM19 PGW1 ltac:(fun x Hx => apply CLSg; rewrite Lpg1 in Hx; clear - Hx; lia) ltac:(fun x Hx => apply OLB; [left; rewrite Lpg1 in Hx; clear - Hx LOV'; lia| rewrite Lpg1 in Hx; clear - Hx; lia]).
tr1 PRES19 WM19 FRB ltac:(fun x Hx => apply (CLF0g _ _ _ x INF); clear - Hx; lia)
ltac:(fun x Hx => apply OLB; [right; right; right; right; left; clear - Hx; lia| clear - Hx BF LOV'; lia]).
tr1 PRES19 WM19 FRS ltac:(fun x Hx => apply (CLSFg _ _ _ x INF); clear - Hx; lia)
ltac:(fun x Hx => apply OLB; [right; right; right; right; right; left; clear - Hx; lia| clear - Hx BF0 LOV'; lia]).
tr1 PRES19 WM19 OC ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); rewrite LOWS in Hx; clear - Hx FO1 FO2; lia)
ltac:(fun x Hx => apply OLB; [right; right; left; rewrite LOWS in Hx; clear - Hx FO1 FO2; lia| rewrite LOWS in Hx; clear - Hx FO2 BF1 LOV'; lia]).
tr1 PRES19 WM19 STB ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FS1 FS2; lia)
ltac:(fun x Hx => apply OLB; [right; right; left; clear - Hx FS1 FS2; lia| clear - Hx FS2 BF1 LOV'; lia]).
tr1 PRES19 WM19 BOBJ8 ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FA1 FA2; lia)
ltac:(fun x Hx => apply OLB; [right; right; left; clear - Hx FA1 FA2; lia| clear - Hx FA2 BF1 LOV'; lia]).
tr1 PRES19 WM19 BDAT8 ltac:(fun x Hx => apply (CLLg _ _ _ PD ND x INPDX); clear - Hx PD1 PD2 Lbs8; lia)
ltac:(fun x Hx => apply OLB; [right; right; right; left; clear - Hx PD1 PD2 Lbs8; lia| clear - Hx BD8 LOV'; lia]).
tr1 PRES19 WM19 X9 ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia)
ltac:(fun x Hx => apply OLB; [right; left; clear - Hx; lia| clear - Hx BS1 LOV'; lia]).
assert (AGB19 : agree_blocks asegs m18 m19 (tl (sb_blocks s S a))).
{ apply (agree_blocks_of_pres_fp RT Σ3 _ _ _ m18 m19 _ PRES19 WM19); [intros bk Hb; apply LIVEA; unfold LALL; apply in_app_iff; left; exact Hb|].
intros bk x Hb Hx. pose proof (BOUT bk x ltac:(unfold LALL; apply in_app_iff; left; exact Hb) Hx) as H1. cbn [outside].
split; [clear - H1 LOV'; lia| exact (APL bk x Hb Hx)]. }
apply (sb_bufs_agree s S a j m18 m19) in BUFS; [| exact JOK | exact AGB19]. clear AGB19.
pk_io_fp PRES19 ERR_rep OUT_rep IO_FP IO_img ltac:(fun y Hy => apply OLB; [right; right; right; right; right; right; clear - Hy; lia| clear - Hy LOV' LOS; lia]).
assert (SSP19 : io_ssp m19).
{ apply (sbd_io_ssp_agree m18 m19 SSP18 (AF_DRV Σ4 m19 ART19)). intros a0 Ha. apply PRES19; [right; left; exact (sbd_ssp_static _ Ha)|].
unfold X00a.SSP_GUARD in Ha. apply OLB; [right; right; right; right; right; right; clear - Ha; lia| clear - Ha LOV' LOS; lia]. }
assert (SHW19 : forall o n, fh <= o -> o + n <= fh + fs_size kh -> forall i, 0 <= i < n -> outside ((usp + -768, usp + -768 + 16) :: blocks_ivs LBL) (shad (o + i))).
{ intros o n H1 H2 i Hi.
assert (SR : SH_LO <= shad (o + i) < SH_HI).
{ pose proof (frame_facts RT AF Σ3 m18 fh kh ART18 INFHX) as (_ & _ & _ & _ & _ & _ & SA & SL & SH & _). split.
- unfold shad, SH_LO, SHB in *. assert (0 <= (o + i) / 8) by (apply Z.div_pos; lia). lia.
- assert (shad (o + i) < shad (fh + fs_size kh)); [| lia].
unfold shad. apply Z.add_lt_mono_r. apply Z.div_lt_upper_bound; [lia|].
assert (E : fh + fs_size kh = 8 * ((fh + fs_size kh) / 8)).
{ pose proof (Z.div_mod (fh + fs_size kh) 8 ltac:(lia)) as XD. rewrite Zplus_mod, FH8, FK8 in XD. cbn in XD. lia. }
lia. }
cbn [outside]. split; [clear - SR LOS LOV'; unfold SH_LO, SH_HI in *; lia|].
exact (outside_blocks_shadow RT AF Σ3 m18 LBL _ ART18 LIVEL SR). }
assert (ACA19 : acc asegs m19 A 48)
by (apply (acc_pres_fp_frame _ _ _ _ m18 m19 fh kh A 48 PRES19 INFHX FH8 FK8 ltac:(lia) FA1 ltac:(lia) (SHW19 A 48 FA1 ltac:(lia)) ACA18)).
assert (ACO19 : acc asegs m19 OUT 8000)
by (apply (acc_pres_fp_frame _ _ _ _ m18 m19 fh kh OUT 8000 PRES19 INFHX FH8 FK8 ltac:(lia) FO1 ltac:(lia) (SHW19 OUT 8000 FO1 ltac:(lia)) ACO18)).
assert (ACT19 : acc asegs m19 STEREO 24)
by (apply (acc_pres_fp_frame _ _ _ _ m18 m19 fh kh STEREO 24 PRES19 INFHX FH8 FK8 ltac:(lia) FS1 ltac:(lia) (SHW19 STEREO 24 FS1 ltac:(lia)) ACT18)).
assert (PF19 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m19).
{ apply (pres_fp_trans _ _ _ _ m m18 m19 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ3) (rt_frames RT Σ3) (usp + -800) _ m18 m19 PRES19).
- intros e He. rewrite EL3, EL2, EL1, ELX. exact He.
- intros e He. rewrite EF3, EF2, EF1, EFX. right. exact He.
- clear; lia.
- intros x Hx Ho. cbn [outside] in Ho. destruct Ho as (_ & _ & _ & Ho). apply sb_outside_app_inv in Ho. destruct Ho as [Hb _].
rewrite ELBD in Hb. cbn [outside]. split; [destruct (SPL x Hx) as [H1 | H1]; clear - H1 LOW LOV'; lia| exact (outside_blocks_app_r _ _ x Hb)]. }
clear PF. rename PF19 into PF.
destruct (af_acc_live RT AF Σ4 m19 S 160 ART19 ltac:(rewrite EL4; exact INLX)) as (_ & ACS19).
assert (OBS19 : aobj asegs m19 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO608 SPT; unfold APP_TOP; lia| exact ACS19]).
assert (EXR19 : EXCREADY m19 (a_low a) (speex_decoder_ctl (speex_decoder_ctl low3 CtlGetPiGain).2 CtlGetExc).2) by (apply EXK19; apply EXR; reflexivity).
clear EXK19 EXR RLOW SHW19 ACA18 ACO18 ACT18 SSP18 ACS18 OBS18 ART18 MI18 ST17 PRES19 OLB.
rename RLOW19 into RLOW.
rewrite <- EL4 in LIVEA, LIVEL, LIVED, INLX, INPDX. rewrite <- EF4 in INF, INFHX. rewrite <- ES4 in LOWX.

assert (WH1 : wr_at asegs m19 (usp + -704) 96).
{ assert (J1 : rw_cells asegs m19 (usp + -704) ([CB 32 (firstn 32 jh1)] ++ f32 pg1)).
{ apply rw_cells_join; [exact RZ1a|]. replace (usp + -704 + Z.of_nat (cells_size [CB 32 (firstn 32 jh1)])) with (usp + -672); [exact PGW1| cbn; lia]. }
assert (J2 : rw_cells asegs m19 (usp + -704) (([CB 32 (firstn 32 jh1)] ++ f32 pg1) ++ [CB 48 (firstn 48 (skipn 16 (skipn 32 jh1)))])).
{ apply rw_cells_join; [exact J1|]. replace (usp + -704 + Z.of_nat (cells_size ([CB 32 (firstn 32 jh1)] ++ f32 pg1))) with (usp + -656); [exact RZ1b|].
rewrite cells_size_app, cells_size_f32, Lpg1. cbn. lia. }
pose proof (proj2 J2) as W. rewrite !cells_size_app, cells_size_f32, Lpg1 in W. exact W. }
assert (WH2 : wr_at asegs m19 (usp + -800) 96).
{ assert (J1 : rw_cells asegs m19 (usp + -800) ([CB 32 (firstn 32 jh2)] ++ f32 er1)).
{ apply rw_cells_join; [exact RZ2a|]. replace (usp + -800 + Z.of_nat (cells_size [CB 32 (firstn 32 jh2)])) with (usp + -768); [exact ERW1| cbn; lia]. }
assert (J2 : rw_cells asegs m19 (usp + -800) (([CB 32 (firstn 32 jh2)] ++ f32 er1) ++ [CB 48 (firstn 48 (skipn 16 (skipn 32 jh2)))])).
{ apply rw_cells_join; [exact J1|]. replace (usp + -800 + Z.of_nat (cells_size ([CB 32 (firstn 32 jh2)] ++ f32 er1))) with (usp + -752); [exact RZ2b|].
rewrite cells_size_app, cells_size_f32, Ler1. cbn. lia. }
pose proof (proj2 J2) as W. rewrite !cells_size_app, cells_size_f32, Ler1 in W. exact W. }
clear RZ1a PGW1 RZ1b RZ2a ERW1 RZ2b Lpg1 Ler1 pg1 er1.
sb_unpack X9 as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_v5 usp lo S OUT f (sbmode_struct (sbd_mode s)) _ sI a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
FR18 HD ILPC OBS19 S8 SPOS BS1 SOFF ST19 ltac:(clear - LOV'; lia) LOS SPH SPA MI19).
clear HD FST PT LE SEED CFG IDC PAD.
destruct POST as (m20 & xa220 & jh3 & -> & MU20 & WM20 & MI20 & ST20 & FR20 & HU3).
clear FR18 ST19.
assert (ART20 : X0ec.ART RT Σ4 m20).
{ apply (af_frame RT AF Σ4 m19 m20 lo ART19 LOWX); [| exact WM20]. intros a0 Ha. apply MU20. cbn [outside]. split; [| exact I].
intros Hin. apply Ha. left. clear - Hin LOV' SPT. unfold USTACK_TOP. lia. }
assert (PF20 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m20).
{ apply (pres_fp_trans _ _ _ _ m m19 m20 PF). apply (pres_fp_of_munch _ _ _ _ _ m19 m20 MU20). intros x Hx Ho. cbn [outside]. split; [| exact I].
intros Hin. destruct (SPL x Hx) as [H1 | H1]; clear - H1 Hin LOW LOV'; lia. }
clear PF. rename PF20 into PF.
pk_munch_all MU20 WM20 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LOV'; cbn [outside]; split; [lia| exact I])
ltac:(fun x Hx => clear - Hx LOV' LOS; cbn [outside]; split; [lia| exact I]).
trm MU20 WM20 SV ltac:(clear; lia).
trm MU20 WM20 FRB ltac:(clear - BF LOV'; lia).
trm MU20 WM20 FRS ltac:(clear - BF0 LOV'; lia).
trm MU20 WM20 OC ltac:(rewrite LOWS; clear - FO2 BF1 LOV'; lia).
trm MU20 WM20 STB ltac:(clear - FS2 BF1 LOV'; lia).
trm MU20 WM20 BOBJ8 ltac:(clear - FA2 BF1 LOV'; lia).
trm MU20 WM20 BDAT8 ltac:(clear - BD8 LOV'; lia).
trm MU20 WM20 X9 ltac:(clear - BS1 LOV'; lia).
apply (wr_at_transport asegs m19 m20 _ _) in WH1; [| exact WM20]. apply (wr_at_transport asegs m19 m20 _ _) in WH2; [| exact WM20].
assert (OF20 : offsh [(usp + -4896, usp + -160)]) by (cbn [offsh]; clear - LOS LOV'; unfold SH_LO, SH_HI in *; lia).
assert (ACC20 : forall o n, acc asegs m19 o n -> 0 <= o -> o + n <= 140737488355328 -> acc asegs m20 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch asegs _ m19 m20 o n (conj H0 (conj H1 H)) MU20 (shfree_of_offsh _ o n OF20 H0 H1)))). }
assert (ACA20 : acc asegs m20 A 48) by (apply ACC20; [exact ACA19| clear - FA1 FP0; lia| clear - FA2 BF1 LO608 SPT; lia]).
assert (ACO20 : acc asegs m20 OUT 8000) by (apply ACC20; [exact ACO19| clear - FO1 FP0; lia| clear - FO2 BF1 LO608 SPT; lia]).
assert (ACT20 : acc asegs m20 STEREO 24) by (apply ACC20; [exact ACT19| clear - FS1 FP0; lia| clear - FS2 BF1 LO608 SPT; lia]).
assert (SSP20 : io_ssp m20).
{ apply (sbd_io_ssp_agree m19 m20 SSP19 (AF_DRV Σ4 m20 ART20)). intros a0 Ha. apply MU20. unfold X00a.SSP_GUARD in Ha. cbn [outside].
clear - Ha LOV' LOS. split; [lia| exact I]. }
destruct (af_acc_live RT AF Σ4 m20 S 160 ART20 INLX) as (_ & ACS20).
assert (OBS20 : aobj asegs m20 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO608 SPT; unfold APP_TOP; lia| exact ACS20]).
clear ACA19 ACO19 ACT19 ACC20 SSP19 ACS19 OBS19 ART19 MI19 OF20 MU20.

assert (EU896 : bv_unsigned (Z_to_bv 64 (usp + -896)) = usp + -896) by (apply unsigned_lit; clear - SPT LOV' LOS; lia).
assert (POA5 : pois_above (rt_pois RT Σ4) (alloca_rr (usp + -864) 32)).
{ intros e He. rewrite EP4, EP3, EP2, EP1 in He. destruct He as [<- | [<- | He]].
- unfold pz_lo, alloca_rr. cbn [fst]. clear - SPA. Z.div_mod_to_equations. lia.
- unfold pz_lo, alloca_rr. cbn [fst]. clear - SPA. Z.div_mod_to_equations. lia.
- rewrite EPX in He. pose proof (POA e He) as H1. unfold alloca_rr. clear - H1 SPA. Z.div_mod_to_equations. lia. }
assert (COK5 : call_ok RT Σ4 m20 (Z_to_bv 64 (usp + -896)) lo).
{ unfold call_ok. rewrite EU896. split; [exact ST20|]. split; [exact LOWX|]. split; [clear - LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia|].
split; [clear - SPT; unfold USTACK_TOP in *; lia| clear - SPA; Z.div_mod_to_equations; lia]. }
cps_rt (APO Σ4 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m20 (usp + -864) 32 lo FDO MST eq_refl eq_refl
ltac:(clear - SPA; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(rewrite EU896; lia)
ltac:(unfold alloca_rr, USTACK_TOP; clear - SPA SPT; Z.div_mod_to_equations; lia)
POA5 ltac:(rewrite EF4, EF3, EF2, EF1, EFX; discriminate) ART20 MI20 COK5).
intros c12 (Σ5 & Hc12 & EP5 & EL5 & EF5 & ES5 & EC5).
destruct (ASTA_unpack RT Σ5 (PMfd F0 fs0) _ c12 Hc12) as (ms12 & PO12 & Hc12'); clear Hc12; cbv beta in PO12.
destruct PO12 as (m21 & v21 & RS21 & (ART21 & MI21 & WM21 & ST21) & PRES21 & ACV21 & ACK21).
cps_ret RS21.
rewrite EU896 in PRES21, ST21.
clear POA5 COK5.
pose proof (pres_fp_of_pres _ _ _ [] _ _ PRES21) as PF21.
tr1 PF21 WM21 SV ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF21 WM21 FR20 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF21 WM21 HU3 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF21 WM21 FRB ltac:(fun x Hx => apply (CLF0g _ _ _ x INF); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF21 WM21 FRS ltac:(fun x Hx => apply (CLSFg _ _ _ x INF); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF21 WM21 OC ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); rewrite LOWS in Hx; clear - Hx FO1 FO2; lia) ltac:(fun x Hx => exact I).
tr1 PF21 WM21 STB ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FS1 FS2; lia) ltac:(fun x Hx => exact I).
tr1 PF21 WM21 BOBJ8 ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FA1 FA2; lia) ltac:(fun x Hx => exact I).
tr1 PF21 WM21 BDAT8 ltac:(fun x Hx => apply (CLLg _ _ _ PD ND x INPDX); clear - Hx PD1 PD2 Lbs8; lia) ltac:(fun x Hx => exact I).
tr1 PF21 WM21 X9 ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => exact I).
apply (wr_at_transport asegs m20 m21 _ _) in WH1; [| exact WM21]. apply (wr_at_transport asegs m20 m21 _ _) in WH2; [| exact WM21].
pk_pres_all RT PRES21 WM21 LALL LIVEA ERR_rep OUT_rep IO_FP IO_img.
assert (ACA21 : acc asegs m21 A 48) by (apply ACK21; [exact ACA20| clear - FA2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FA2 BF1 LOV'; lia]).
assert (ACO21 : acc asegs m21 OUT 8000) by (apply ACK21; [exact ACO20| clear - FO2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FO2 BF1 LOV'; lia]).
assert (ACT21 : acc asegs m21 STEREO 24) by (apply ACK21; [exact ACT20| clear - FS2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FS2 BF1 LOV'; lia]).
assert (ACS21 : acc asegs m21 S 160) by (apply ACK21; [exact ACS20| clear - BS1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - BS1 LOV'; lia]).
assert (OBS21 : aobj asegs m21 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO608 SPT; unfold APP_TOP; lia| exact ACS21]).
assert (SSP21 : io_ssp m21).
{ apply (sbd_io_ssp_agree m20 m21 SSP20 (AF_DRV Σ5 m21 ART21)). intros a0 Ha. apply PRES21. right; left. exact (sbd_ssp_static _ Ha). }
assert (PF21' : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m21).
{ apply (pres_fp_trans _ _ _ _ m m20 m21 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ4) (rt_frames RT Σ4) (usp + -896) [] m20 m21 PF21).
- intros e He. rewrite EL4, EL3, EL2, EL1, ELX. exact He.
- intros e He. rewrite EF4, EF3, EF2, EF1, EFX. right. exact He.
- clear; lia.
- intros x _ _. exact I. }
clear PF. rename PF21' into PF.
clear ACA20 ACO20 ACT20 ACS20 OBS20 SSP20 ART20 MI20 ST20 PF21 PRES21 ACK21 ACV21.
rewrite <- EL5 in LIVEA, LIVEL, LIVED, INLX, INPDX. rewrite <- EF5 in INF, INFHX. rewrite <- ES5 in LOWX.

assert (WH3 : wr_at asegs m21 (usp + -896) 96) by (exact (proj2 HU3)). clear HU3.
cps_seg (sbd_v6 usp lo S OUT f (sbmode_struct (sbd_mode s)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
FR20 ST21 ltac:(clear - LOV'; lia) LOS SPH SPA MI21).
destruct POST as (m22 & jh4 & -> & MU22 & WM22 & MI22 & ST22 & FR22 & HU4).
clear FR20 ST21.
assert (ART22 : X0ec.ART RT Σ5 m22).
{ apply (af_frame RT AF Σ5 m21 m22 lo ART21 LOWX); [| exact WM22]. intros a0 Ha. apply MU22. cbn [outside]. split; [| exact I].
intros Hin. apply Ha. left. clear - Hin LOV' SPT. unfold USTACK_TOP. lia. }
assert (PF22 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m22).
{ apply (pres_fp_trans _ _ _ _ m m21 m22 PF). apply (pres_fp_of_munch _ _ _ _ _ m21 m22 MU22). intros x Hx Ho. cbn [outside]. split; [| exact I].
intros Hin. destruct (SPL x Hx) as [H1 | H1]; clear - H1 Hin LOW LOV'; lia. }
clear PF. rename PF22 into PF.
pk_munch_all MU22 WM22 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LOV'; cbn [outside]; split; [lia| exact I])
ltac:(fun x Hx => clear - Hx LOV' LOS; cbn [outside]; split; [lia| exact I]).
trm MU22 WM22 SV ltac:(clear; lia).
trm MU22 WM22 FRB ltac:(clear - BF LOV'; lia).
trm MU22 WM22 FRS ltac:(clear - BF0 LOV'; lia).
trm MU22 WM22 OC ltac:(rewrite LOWS; clear - FO2 BF1 LOV'; lia).
trm MU22 WM22 STB ltac:(clear - FS2 BF1 LOV'; lia).
trm MU22 WM22 BOBJ8 ltac:(clear - FA2 BF1 LOV'; lia).
trm MU22 WM22 BDAT8 ltac:(clear - BD8 LOV'; lia).
trm MU22 WM22 X9 ltac:(clear - BS1 LOV'; lia).
apply (wr_at_transport asegs m21 m22 _ _) in WH1; [| exact WM22]. apply (wr_at_transport asegs m21 m22 _ _) in WH2; [| exact WM22].
apply (wr_at_transport asegs m21 m22 _ _) in WH3; [| exact WM22].
assert (OF22 : offsh [(usp + -4992, usp + -160)]) by (cbn [offsh]; clear - LOS LOV'; unfold SH_LO, SH_HI in *; lia).
assert (ACC22 : forall o n, acc asegs m21 o n -> 0 <= o -> o + n <= 140737488355328 -> acc asegs m22 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch asegs _ m21 m22 o n (conj H0 (conj H1 H)) MU22 (shfree_of_offsh _ o n OF22 H0 H1)))). }
assert (ACA22 : acc asegs m22 A 48) by (apply ACC22; [exact ACA21| clear - FA1 FP0; lia| clear - FA2 BF1 LO608 SPT; lia]).
assert (ACO22 : acc asegs m22 OUT 8000) by (apply ACC22; [exact ACO21| clear - FO1 FP0; lia| clear - FO2 BF1 LO608 SPT; lia]).
assert (ACT22 : acc asegs m22 STEREO 24) by (apply ACC22; [exact ACT21| clear - FS1 FP0; lia| clear - FS2 BF1 LO608 SPT; lia]).
assert (SSP22 : io_ssp m22).
{ apply (sbd_io_ssp_agree m21 m22 SSP21 (AF_DRV Σ5 m22 ART22)). intros a0 Ha. apply MU22. unfold X00a.SSP_GUARD in Ha. cbn [outside].
clear - Ha LOV' LOS. split; [lia| exact I]. }
destruct (af_acc_live RT AF Σ5 m22 S 160 ART22 INLX) as (_ & ACS22).
assert (OBS22 : aobj asegs m22 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO608 SPT; unfold APP_TOP; lia| exact ACS22]).
clear ACA21 ACO21 ACT21 ACC22 SSP21 ACS21 OBS21 ART21 MI21 OF22 MU22.

assert (EU992 : bv_unsigned (Z_to_bv 64 (usp + -992)) = usp + -992) by (apply unsigned_lit; clear - SPT LOV' LOS; lia).
assert (POA6 : pois_above (rt_pois RT Σ5) (alloca_rr (usp + -960) 32)).
{ intros e He. rewrite EP5, EP4, EP3, EP2, EP1 in He. destruct He as [<- | [<- | [<- | He]]].
- unfold pz_lo, alloca_rr. cbn [fst]. clear - SPA. Z.div_mod_to_equations. lia.
- unfold pz_lo, alloca_rr. cbn [fst]. clear - SPA. Z.div_mod_to_equations. lia.
- unfold pz_lo, alloca_rr. cbn [fst]. clear - SPA. Z.div_mod_to_equations. lia.
- rewrite EPX in He. pose proof (POA e He) as H1. unfold alloca_rr. clear - H1 SPA. Z.div_mod_to_equations. lia. }
assert (COK6 : call_ok RT Σ5 m22 (Z_to_bv 64 (usp + -992)) lo).
{ unfold call_ok. rewrite EU992. split; [exact ST22|]. split; [exact LOWX|]. split; [clear - LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia|].
split; [clear - SPT; unfold USTACK_TOP in *; lia| clear - SPA; Z.div_mod_to_equations; lia]. }
cps_rt (APO Σ5 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m22 (usp + -960) 32 lo FDO MST eq_refl eq_refl
ltac:(clear - SPA; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(rewrite EU992; lia)
ltac:(unfold alloca_rr, USTACK_TOP; clear - SPA SPT; Z.div_mod_to_equations; lia)
POA6 ltac:(rewrite EF5, EF4, EF3, EF2, EF1, EFX; discriminate) ART22 MI22 COK6).
intros c14 (Σ6 & Hc14 & EP6 & EL6 & EF6 & ES6 & EC6).
destruct (ASTA_unpack RT Σ6 (PMfd F0 fs0) _ c14 Hc14) as (ms14 & PO14 & Hc14'); clear Hc14; cbv beta in PO14.
destruct PO14 as (m23 & v23 & RS23 & (ART23 & MI23 & WM23 & ST23) & PRES23 & ACV23 & ACK23).
cps_ret RS23.
rewrite EU992 in PRES23, ST23.
clear POA6 COK6.
pose proof (pres_fp_of_pres _ _ _ [] _ _ PRES23) as PF23.
tr1 PF23 WM23 SV ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF23 WM23 FR22 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF23 WM23 HU4 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF23 WM23 FRB ltac:(fun x Hx => apply (CLF0g _ _ _ x INF); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF23 WM23 FRS ltac:(fun x Hx => apply (CLSFg _ _ _ x INF); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF23 WM23 OC ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); rewrite LOWS in Hx; clear - Hx FO1 FO2; lia) ltac:(fun x Hx => exact I).
tr1 PF23 WM23 STB ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FS1 FS2; lia) ltac:(fun x Hx => exact I).
tr1 PF23 WM23 BOBJ8 ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FA1 FA2; lia) ltac:(fun x Hx => exact I).
tr1 PF23 WM23 BDAT8 ltac:(fun x Hx => apply (CLLg _ _ _ PD ND x INPDX); clear - Hx PD1 PD2 Lbs8; lia) ltac:(fun x Hx => exact I).
tr1 PF23 WM23 X9 ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => exact I).
apply (wr_at_transport asegs m22 m23 _ _) in WH1; [| exact WM23]. apply (wr_at_transport asegs m22 m23 _ _) in WH2; [| exact WM23].
apply (wr_at_transport asegs m22 m23 _ _) in WH3; [| exact WM23].
pk_pres_all RT PRES23 WM23 LALL LIVEA ERR_rep OUT_rep IO_FP IO_img.
assert (ACA23 : acc asegs m23 A 48) by (apply ACK23; [exact ACA22| clear - FA2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FA2 BF1 LOV'; lia]).
assert (ACO23 : acc asegs m23 OUT 8000) by (apply ACK23; [exact ACO22| clear - FO2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FO2 BF1 LOV'; lia]).
assert (ACT23 : acc asegs m23 STEREO 24) by (apply ACK23; [exact ACT22| clear - FS2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FS2 BF1 LOV'; lia]).
assert (ACS23 : acc asegs m23 S 160) by (apply ACK23; [exact ACS22| clear - BS1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - BS1 LOV'; lia]).
assert (OBS23 : aobj asegs m23 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO608 SPT; unfold APP_TOP; lia| exact ACS23]).
assert (SSP23 : io_ssp m23).
{ apply (sbd_io_ssp_agree m22 m23 SSP22 (AF_DRV Σ6 m23 ART23)). intros a0 Ha. apply PRES23. right; left. exact (sbd_ssp_static _ Ha). }
assert (PF23' : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m23).
{ apply (pres_fp_trans _ _ _ _ m m22 m23 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ5) (rt_frames RT Σ5) (usp + -992) [] m22 m23 PF23).
- intros e He. rewrite EL5, EL4, EL3, EL2, EL1, ELX. exact He.
- intros e He. rewrite EF5, EF4, EF3, EF2, EF1, EFX. right. exact He.
- clear; lia.
- intros x _ _. exact I. }
clear PF. rename PF23' into PF.
clear ACA22 ACO22 ACT22 ACS22 OBS22 SSP22 ART22 MI22 ST22 PF23 PRES23 ACK23 ACV23.
rewrite <- EL6 in LIVEA, LIVEL, LIVED, INLX, INPDX. rewrite <- EF6 in INF, INFHX. rewrite <- ES6 in LOWX.

assert (HMO' : sbd_mode s = ModeWB \/ sbd_mode s = ModeUWB) by (clear - IMODE; unfold hid in *; exact IMODE).
pose proof (sb_submode_cases (sbd_mode s) id sm HMO' ltac:(clear - IDR; lia) ESM) as SMC.
assert (IDC4 : id = 1 \/ id = 2 \/ id = 3 \/ id = 4) by (clear - SMC; destruct SMC as [(_ & [(-> & _)|[(-> & _)|[(-> & _)|(-> & _)]]])|(_ & -> & _)]; lia).
assert (ELQ : sm_lsp_unquant sm = LspUnquantHigh)
by (clear - SMC; destruct SMC as [(_ & [(_ & ->)|[(_ & ->)|[(_ & ->)|(_ & ->)]]])|(_ & _ & ->)]; reflexivity).
pose proof (AF_LIB Σ6 m23 ART23) as LC23.
assert (OBSM : aobj asegs m23 (sb_sub_addr id) 88).
{ destruct IDC4 as [E|[E|[E|E]]]; rewrite E; cbn [sb_sub_addr Z.eqb Pos.eqb]; (apply (aobj_lit RT AF Σ6 m23 _ 88 ART23);
[ unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_wb_submode1, A_wb_submode2, A_wb_submode3, A_wb_submode4; lia
| unfold A_wb_submode1, A_wb_submode2, A_wb_submode3, A_wb_submode4, APP_TOP; lia]). }
assert (OBM23 : aobj asegs m23 (sbmode_struct (sbd_mode s)) 216).
{ destruct IMODE as [E|E]; rewrite E; cbn [sbmode_struct]; (apply (aobj_lit RT AF Σ6 m23 _ 216 ART23);
[ unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_sb_wb_mode, A_sb_uwb_mode; lia | unfold A_sb_wb_mode, A_sb_uwb_mode, APP_TOP; lia]). }
sb_unpack X9 as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_v7 usp S OUT A f (sbmode_struct (sbd_mode s)) (sb_sub_addr id) id _ s (sj_pad1 j) sm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
FR22 ltac:(gslot) ltac:(gslot) ltac:(gslot) ltac:(gslot) ltac:(gslot) ltac:(gslot) ltac:(gslot)
CFG IDC OBS23 S8 SPOS ltac:(clear - BS1 LOV'; lia) SOFF HMO' eq_refl OBM23 ESM ltac:(clear - IDR; lia) eq_refl OBSM LC23
ltac:(clear - LOS LOV'; unfold SH_HI in *; lia) SPH MI23).
clear HD FST PT LE SEED CFG IDC PAD OBSM OBM23 LC23.
destruct POST as (m24 & xa324 & -> & MU24 & WM24 & MI24 & FR24).
clear FR22.
assert (ART24 : X0ec.ART RT Σ6 m24).
{ apply (af_frame RT AF Σ6 m23 m24 lo ART23 LOWX); [| exact WM24]. intros a0 Ha. apply MU24. cbn [outside]. split; [| exact I].
intros Hin. apply Ha. left. clear - Hin LOV' SPT. unfold USTACK_TOP. lia. }
assert (PF24 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m24).
{ apply (pres_fp_trans _ _ _ _ m m23 m24 PF). apply (pres_fp_of_munch _ _ _ _ _ m23 m24 MU24). intros x Hx Ho. cbn [outside]. split; [| exact I].
intros Hin. destruct (SPL x Hx) as [H1 | H1]; clear - H1 Hin LOW LOV'; lia. }
clear PF. rename PF24 into PF.
pk_munch_all MU24 WM24 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LOV'; cbn [outside]; split; [lia| exact I])
ltac:(fun x Hx => clear - Hx LOV' LOS; cbn [outside]; split; [lia| exact I]).
trm MU24 WM24 SV ltac:(clear; lia).
trm MU24 WM24 HU4 ltac:(clear; lia).
trm MU24 WM24 FRB ltac:(clear - BF LOV'; lia).
trm MU24 WM24 FRS ltac:(clear - BF0 LOV'; lia).
trm MU24 WM24 OC ltac:(rewrite LOWS; clear - FO2 BF1 LOV'; lia).
trm MU24 WM24 STB ltac:(clear - FS2 BF1 LOV'; lia).
trm MU24 WM24 BOBJ8 ltac:(clear - FA2 BF1 LOV'; lia).
trm MU24 WM24 BDAT8 ltac:(clear - BD8 LOV'; lia).
trm MU24 WM24 X9 ltac:(clear - BS1 LOV'; lia).
apply (stk_transport_disjoint asegs [(usp + -608, usp + -160)] m23 m24 lo (usp + -992)) in ST23; [| exact MU24 | exact WM24 | cbn [disjoint_from]; clear; lia].
apply (wr_at_transport asegs m23 m24 _ _) in WH1; [| exact WM24]. apply (wr_at_transport asegs m23 m24 _ _) in WH2; [| exact WM24].
apply (wr_at_transport asegs m23 m24 _ _) in WH3; [| exact WM24].
assert (OF24 : offsh [(usp + -608, usp + -160)]) by (cbn [offsh]; clear - LOS LOV'; unfold SH_LO, SH_HI in *; lia).
assert (ACC24 : forall o n, acc asegs m23 o n -> 0 <= o -> o + n <= 140737488355328 -> acc asegs m24 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch asegs _ m23 m24 o n (conj H0 (conj H1 H)) MU24 (shfree_of_offsh _ o n OF24 H0 H1)))). }
assert (ACA24 : acc asegs m24 A 48) by (apply ACC24; [exact ACA23| clear - FA1 FP0; lia| clear - FA2 BF1 LO608 SPT; lia]).
assert (ACO24 : acc asegs m24 OUT 8000) by (apply ACC24; [exact ACO23| clear - FO1 FP0; lia| clear - FO2 BF1 LO608 SPT; lia]).
assert (ACT24 : acc asegs m24 STEREO 24) by (apply ACC24; [exact ACT23| clear - FS1 FP0; lia| clear - FS2 BF1 LO608 SPT; lia]).
assert (SSP24 : io_ssp m24).
{ apply (sbd_io_ssp_agree m23 m24 SSP23 (AF_DRV Σ6 m24 ART24)). intros a0 Ha. apply MU24. unfold X00a.SSP_GUARD in Ha. cbn [outside].
clear - Ha LOV' LOS. split; [lia| exact I]. }
destruct (af_acc_live RT AF Σ6 m24 S 160 ART24 INLX) as (_ & ACS24).
assert (OBS24 : aobj asegs m24 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO608 SPT; unfold APP_TOP; lia| exact ACS24]).
clear ACA23 ACO23 ACT23 ACC24 SSP23 ACS23 OBS23 ART23 MI23 OF24 MU24.

destruct (wr_at_rw_CB m24 (usp + -896) 96 WH3 ltac:(lia)) as (jh3' & HU3). clear WH3. change (Z.to_nat 96) with 96%nat in HU3.
apply (rw_cells_split_CB asegs _ _ [] 96 _ [] [32; 32; 32]%nat) in HU3; [| reflexivity]. cbn [mk_CB_cells app] in HU3.
apply rw_cells_uncons in HU3. destruct HU3 as (RZ3a & HU3). apply rw_cells_uncons in HU3. destruct HU3 as (QL3 & RZ3b).
cbn [csize] in QL3, RZ3b.
replace (usp + -896 + Z.of_nat 32) with (usp + -864) in QL3, RZ3b by lia. replace (usp + -864 + Z.of_nat 32) with (usp + -832) in RZ3b by lia.
destruct (rw_cells_CB_f32 asegs m24 (usp + -864) 8 _ QL3) as (ql0 & Lql0 & QLW). clear QL3.
assert (BREP24 : bits_rep asegs m24 A D (sbw_bits b1)).
{ split; [exists rj8; split; [exact Lrj8| unfold bits_cells; exact BOBJ8]|].
split; [exists bs8; split; [apply (proj2 (u8arr_rw_CB m24 D bs8)); exact BDAT8| exact Hbs8]| exact BSIDE8]. }
assert (OBA24 : aobj asegs m24 A BITS_SIZEOF) by (split; [clear - AIMG; lia|]; split; [clear - ALO LO608 SPT; unfold APP_TOP, BITS_SIZEOF in *; lia| exact ACA24]).
assert (OBD24 : aobj asegs m24 D (sb_buf_size (sbw_bits b1))).
{ rewrite BSZ8. destruct (af_acc_live RT AF Σ6 m24 PD ND ART24 INPDX) as (_ & ACPD).
split; [clear - PD1 PDP; lia|]. split; [clear - DLO LO608 SPT; unfold APP_TOP; lia|].
apply (acc_sub asegs m24 PD ND D (sb_buf_size b1) ACPD); clear - PD1 PD2; lia. }
assert (INQ : In (usp + -864, 32) (rt_pois RT Σ6)) by (rewrite EP6, EP5; right; left; reflexivity).
assert (OBQ24 : aobj asegs m24 (usp + -864) (4 * lsp_order LspUnquantHigh))
by (cbn [lsp_order]; split; [clear - LOV' LOS; lia|]; split; [clear - SPT; unfold APP_TOP, USTACK_TOP in *; lia| exact (af_acc_pois RT AF Σ6 m24 _ _ ART24 INQ)]).
assert (LT24 : lsp_tabs m24).
{ assert (K : forall a n, In (a, n) ACC_LITS -> 0 <= a -> a + n <= APP_TOP -> aobj asegs m24 a n) by (intros a0 n; exact (aobj_lit RT AF Σ6 m24 a0 n ART24)).
unfold lsp_tabs, A_cdbk_nb, A_cdbk_nb_low1, A_cdbk_nb_low2, A_cdbk_nb_high1, A_cdbk_nb_high2, A_high_lsp_cdbk, A_high_lsp_cdbk2.
repeat match goal with |- _ /\ _ => split end;
(apply K; [unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | lia | unfold APP_TOP; lia]). }
pose proof (AF_LIB Σ6 m24 ART24) as LC24. pose proof (af_client_consts RT AF Σ6 m24 ART24) as CC24.
cps_seg (lsp_unquant_high_stmt bptr A D (usp + -864) (usp + -992) lo (sbw_bits b1) ql0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m24
BREP24 BOK8 OBA24 OBD24 OBQ24 LT24 LC24 CC24 QLW Lql0 ltac:(clear - SPA; Z.div_mod_to_equations; lia) ASH
ltac:(right; clear - LOS LOV'; unfold SH_HI in *; lia) ltac:(unfold IMG_TOP; clear - AIMG; lia) ltac:(unfold IMG_TOP; clear - LOV' LOS; lia)
ltac:(unfold BITS_SIZEOF; exact ALO) ltac:(rewrite BSZ8; exact DLO) ltac:(right; clear; lia)
ltac:(right; clear - ALO LOV'; unfold BITS_SIZEOF; lia) ltac:(right; rewrite BSZ8; clear - DLO LOV'; lia)
ST23 ltac:(unfold LSPQ_DEPTH; clear - LOV'; lia) LOS ltac:(clear - SPH; lia) MI24 RS19).
clear BREP24 OBA24 OBD24 OBQ24 LT24 LC24 CC24 QLW Lql0 ql0 INQ.
destruct POST as (t025 & t125 & t225 & a025 & a125 & a225 & a325 & a425 & a525 & a625 & a725 & t325 & t425 & t525 & t625 & F25 & fc25 & m25 & ql1 &
-> & MU25 & WM25 & MI25 & ST25 & FRM25 & QLW1 & Lql1 & BREP25 & BOK25).
clear ST23.

rewrite ELQ in Hk.
assert (BSZ25 : sb_buf_size (lsp_bits LspUnquantHigh (sbw_bits b1)) = sb_buf_size b1)
by (pose proof (bkeep_lsp LspUnquantHigh (sbw_bits b1)) as (_ & _ & K3); rewrite K3; exact BSZ8).
destruct BREP25 as ((rj25 & Lrj25 & BOBJ25) & (bs25 & BDAT25 & Hbs25) & BSIDE25). apply u8arr_rw_CB in BDAT25. unfold bits_cells in BOBJ25.
assert (Lbs25 : Z.of_nat (length bs25) = sb_buf_size b1)
by (pose proof BOK25 as OK'; unfold bits_ok in OK'; rewrite Hbs25, zlength_map_unsigned, BSZ25 in OK'; clear - OK'; lia).
clear BOBJ8 BDAT8 Hbs8 BSIDE8 BOK8 Lrj8 Lbs8 BD8 BDS BSZ8 rj8 bs8.
rename BOBJ25 into BOBJ8, BDAT25 into BDAT8, Hbs25 into Hbs8, BSIDE25 into BSIDE8, BOK25 into BOK8, Lrj25 into Lrj8, Lbs25 into Lbs8, BSZ25 into BSZ8, rj25 into rj8, bs25 into bs8.
assert (BD8 : D + Z.of_nat (length bs8) <= lo) by (rewrite Lbs8; exact DLO).
assert (BDS : D + Z.of_nat (length bs8) <= S \/ S + 160 <= D) by (clear - SPD PD1 PD2 Lbs8; lia).
assert (ART25 : X0ec.ART RT Σ6 m25).
{ apply (af_frame RT AF Σ6 m24 m25 lo ART24 LOWX); [| exact WM25]. intros a0 Ha. apply MU25. cbn [outside]. unfold BITS_SIZEOF, LSPQ_DEPTH; cbn [lsp_order].
split; [| split; [| split; [| exact I]]]; intros Hin; apply Ha.
- right; right; right; left. exists fh, kh. split; [exact INFHX| clear - Hin FA1 FA2; lia].
- left. clear - Hin LOV' SPT. unfold USTACK_TOP. lia.
- left. clear - Hin LOV' SPT. unfold USTACK_TOP. lia. }
assert (PF25 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m25).
{ apply (pres_fp_trans _ _ _ _ m m24 m25 PF). apply (pres_fp_of_munch _ _ _ _ _ m24 m25 MU25). intros x Hx Ho. cbn [outside] in Ho |- *.
unfold BITS_SIZEOF, LSPQ_DEPTH; cbn [lsp_order]. destruct Ho as (HA & _).
split; [exact HA|]. split; [| split; [| exact I]]; intros Hin; destruct (SPL x Hx) as [H1 | H1]; clear - H1 Hin LOW LOV'; lia. }
clear PF. rename PF25 into PF.
pk_munch_all MU25 WM25 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LOV' FA1 FA2; cbn [outside]; unfold BITS_SIZEOF, LSPQ_DEPTH; cbn [lsp_order];
split; [lia| split; [lia| split; [lia| exact I]]])
ltac:(fun x Hx => clear - Hx LOV' LOS AIMG; cbn [outside]; unfold BITS_SIZEOF, LSPQ_DEPTH; cbn [lsp_order]; split; [lia| split; [lia| split; [lia| exact I]]]).
trm MU25 WM25 SV ltac:(unfold BITS_SIZEOF, LSPQ_DEPTH; cbn [lsp_order]; clear - ALO LO608; lia).
trm MU25 WM25 FR24 ltac:(unfold BITS_SIZEOF, LSPQ_DEPTH; cbn [lsp_order]; clear - ALO LO608; lia).
trm MU25 WM25 HU4 ltac:(unfold BITS_SIZEOF, LSPQ_DEPTH; cbn [lsp_order]; clear - ALO LOV'; lia).
trm MU25 WM25 RZ3a ltac:(unfold BITS_SIZEOF, LSPQ_DEPTH; cbn [lsp_order]; clear - ALO LOV'; lia).
trm MU25 WM25 RZ3b ltac:(unfold BITS_SIZEOF, LSPQ_DEPTH; cbn [lsp_order]; clear - ALO LOV'; lia).
trm MU25 WM25 FRB ltac:(unfold BITS_SIZEOF, LSPQ_DEPTH; cbn [lsp_order]; clear - BF LOV' FFA FA1 FA2; unfold hid in *; lia).
trm MU25 WM25 FRS ltac:(unfold BITS_SIZEOF, LSPQ_DEPTH; cbn [lsp_order]; clear - BF0 LOV' ASH SHF1 SHF2 FA1 FA2; unfold hid in *; lia).
trm MU25 WM25 OC ltac:(unfold BITS_SIZEOF, LSPQ_DEPTH; cbn [lsp_order]; rewrite LOWS; clear - FO2 BF1 LOV' HAO'; unfold hid in *; lia).
trm MU25 WM25 STB ltac:(unfold BITS_SIZEOF, LSPQ_DEPTH; cbn [lsp_order]; clear - FS2 BF1 LOV' HAS'; unfold hid in *; lia).
trm MU25 WM25 X9 ltac:(unfold BITS_SIZEOF, LSPQ_DEPTH; cbn [lsp_order]; clear - BS1 LOV' SFH FA1 FA2; unfold hid in *; lia).
apply (wr_at_transport asegs m24 m25 _ _) in WH1; [| exact WM25]. apply (wr_at_transport asegs m24 m25 _ _) in WH2; [| exact WM25].
assert (OF25 : offsh [(A, A + BITS_SIZEOF); (usp + -864, usp + -864 + 4 * lsp_order LspUnquantHigh); (usp + -992 + - LSPQ_DEPTH, usp + -992)])
by (cbn [offsh lsp_order]; unfold BITS_SIZEOF, LSPQ_DEPTH; clear - LOS LOV' ASH; unfold hid, SH_LO, SH_HI in *; lia).
assert (ACC25 : forall o n, acc asegs m24 o n -> 0 <= o -> o + n <= 140737488355328 -> acc asegs m25 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch asegs _ m24 m25 o n (conj H0 (conj H1 H)) MU25 (shfree_of_offsh _ o n OF25 H0 H1)))). }
assert (ACA25 : acc asegs m25 A 48) by (apply ACC25; [exact ACA24| clear - FA1 FP0; lia| clear - FA2 BF1 LO608 SPT; lia]).
assert (ACO25 : acc asegs m25 OUT 8000) by (apply ACC25; [exact ACO24| clear - FO1 FP0; lia| clear - FO2 BF1 LO608 SPT; lia]).
assert (ACT25 : acc asegs m25 STEREO 24) by (apply ACC25; [exact ACT24| clear - FS1 FP0; lia| clear - FS2 BF1 LO608 SPT; lia]).
assert (SSP25 : io_ssp m25).
{ apply (sbd_io_ssp_agree m24 m25 SSP24 (AF_DRV Σ6 m25 ART25)). intros a0 Ha. apply MU25. unfold X00a.SSP_GUARD in Ha. cbn [outside lsp_order].
unfold BITS_SIZEOF, LSPQ_DEPTH. clear - Ha LOV' LOS AIMG. split; [lia| split; [lia| split; [lia| exact I]]]. }
destruct (af_acc_live RT AF Σ6 m25 S 160 ART25 INLX) as (_ & ACS25).
assert (OBS25 : aobj asegs m25 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO608 SPT; unfold APP_TOP; lia| exact ACS25]).
clear ACA24 ACO24 ACT24 ACC25 SSP24 ACS24 OBS24 ART24 MI24 OF25 MU25.

destruct BUFS as (G0C & G1C & EXC & OQC & IQC & MSPC & PGC & ERC).
pose proof JOK1 as (JP1 & JP2 & JG0 & JG1 & JEXC & JOQ & JIQ & JMSP & JPG & JER).
assert (AL : sb_addrs_al a) by (apply (sb_addrs_al_of_blocks s S a); intros bk Hb; apply LAL8; rewrite ELBD; apply in_app_iff; left; exact Hb).
assert (NDA : List.NoDup [S; a_g0 a; a_g1 a; a_exc a; a_oq a; a_iq a; a_pg a; a_er a; a_msp a]).
{ pose proof NDUP as ND'. rewrite ELBD, map_app in ND'. apply List.NoDup_app_remove_r in ND'. exact ND'. }
repeat rewrite List.NoDup_cons_iff in NDA. cbn [In] in NDA.
assert (INOQ : In (a_oq a, 32) (rt_live RT Σ6)) by (apply (LIVEA (sbd_old_qlsp s, a_oq a, 32)); unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; do 3 right; left; reflexivity).
destruct (live_facts RT AF Σ6 m25 _ _ ART25 INOQ) as (OQP & _ & _ & OQSH).
destruct (live_below_lo RT AF Σ6 m25 _ _ lo ART25 INOQ LOWX) as (_ & OQLO & _).
destruct (af_acc_live RT AF Σ6 m25 _ _ ART25 INOQ) as (_ & ACOQ).
assert (OBOQ : aobj asegs m25 (a_oq a) 32) by (split; [clear - OQP; lia|]; split; [clear - OQLO LO608 SPT; unfold APP_TOP; lia| exact ACOQ]).
assert (OQ8 : a_oq a mod 8 = 0) by (destruct AL as (_ & _ & _ & X8 & _); exact X8).
pose proof (BOUT (sbd_old_qlsp s, a_oq a, 32) (a_oq a) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; do 3 right; left; reflexivity)
ltac:(unfold blk_addr, blk_size; cbn [fst snd]; clear; lia)) as BOQ0.
pose proof (BOUT (sbd_old_qlsp s, a_oq a, 32) (a_oq a + 31) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; do 3 right; left; reflexivity)
ltac:(unfold blk_addr, blk_size; cbn [fst snd]; clear; lia)) as BOQ1.
assert (OQS : S + 160 <= a_oq a \/ a_oq a + 32 <= S) by (clear - BOQ0 BOQ1; lia).
assert (EQL : Z.to_nat (lsp_order LspUnquantHigh) = 8%nat) by reflexivity. rewrite EQL in Lql1.
assert (INQ : In (usp + -864, 32) (rt_pois RT Σ6)) by (rewrite EP6, EP5; right; left; reflexivity).
assert (OBQ : aobj asegs m25 (usp + -864) 32)
by (split; [clear - LOV' LOS; lia|]; split; [clear - SPT; unfold APP_TOP, USTACK_TOP in *; lia| exact (af_acc_pois RT AF Σ6 m25 _ _ ART25 INQ)]).
sb_unpack X9 as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_v8 usp lo S OUT f (sbmode_struct (sbd_mode s)) (usp + -864) (a_oq a) _ sI a ql1 (sj_oq j) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
FR24 ltac:(gslot) ltac:(gslot) HD FST PT ILPC IFST eq_refl OBS25 S8 SPOS BS1 SOFF eq_refl QLW1 Lql1 OBQ OQC JOQ OBOQ OQ8 OQP OQLO
ltac:(clear - OQSH; unfold SH_LO, SH_HI; lia) OQS ST25 ltac:(clear - LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia) LOS SPH SPA MI25 FRM25).
clear HD FST PT LE SEED CFG IDC PAD OBQ OBOQ.
destruct POST as (m26 & xt026 & xa226 & xa326 & xa426 & xa526 & xa726 & F26 & jh5 & voq1 & -> & MU26 & WM26 & MI26 & ST26 & FR26 & HU5 & OQW1 & Lvoq1).
clear FR24 ST25 OQC.

assert (WH3 : wr_at asegs m25 (usp + -896) 96).
{ assert (J1 : rw_cells asegs m25 (usp + -896) ([CB 32 (firstn 32 jh3')] ++ f32 ql1)).
{ apply rw_cells_join; [exact RZ3a|]. replace (usp + -896 + Z.of_nat (cells_size [CB 32 (firstn 32 jh3')])) with (usp + -864); [exact QLW1| cbn; lia]. }
assert (J2 : rw_cells asegs m25 (usp + -896) (([CB 32 (firstn 32 jh3')] ++ f32 ql1) ++ [CB 32 (firstn 32 (skipn 32 (skipn 32 jh3')))])).
{ apply rw_cells_join; [exact J1|]. replace (usp + -896 + Z.of_nat (cells_size ([CB 32 (firstn 32 jh3')] ++ f32 ql1))) with (usp + -832); [exact RZ3b|].
rewrite cells_size_app, cells_size_f32, Lql1. cbn. lia. }
pose proof (proj2 J2) as W. rewrite !cells_size_app, cells_size_f32, Lql1 in W. exact W. }
assert (WH4 : wr_at asegs m25 (usp + -992) 96) by (exact (proj2 HU4)).
clear RZ3a QLW1 RZ3b HU4 Lql1 ql1 jh3' jh4.
set (LNO := [(sbd_g0_mem s, a_g0 a, 256); (sbd_g1_mem s, a_g1 a, 256); (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s); (sbd_interp_qlpc s, a_iq a, 32);
(sbd_pi_gain s, a_pg a, 16); (sbd_exc_rms s, a_er a, 16); (sbd_mem_sp s, a_msp a, 64)] ++ LBL).
assert (LNOA : forall bk, In bk LNO -> In bk LALL).
{ intros bk Hb. unfold LNO in Hb. unfold LALL. apply in_app_iff. apply in_app_iff in Hb. destruct Hb as [Hb | Hb]; [left| right; exact Hb].
clear - Hb. cbn [sb_blocks tl In] in Hb |- *. tauto. }
assert (LNOQ : forall bk x, In bk LNO -> blk_addr bk <= x < blk_addr bk + blk_size bk -> x < a_oq a \/ a_oq a + 32 <= x).
{ intros bk x Hb Hx. unfold LNO in Hb. apply in_app_iff in Hb. destruct Hb as [Hb | Hb].
- assert (NE : blk_addr bk <> a_oq a).
{ cbn [In] in Hb. unfold blk_addr. destruct Hb as [<- |[<- |[<- |[<- |[<- |[<- |[<- | []]]]]]]]; cbn [fst snd]; intros E; rewrite E in NDA; clear - NDA; tauto. }
pose proof (live_apart RT AF Σ6 m25 _ _ _ _ ART25 (LIVEA bk (LNOA bk ltac:(unfold LNO; apply in_app_iff; left; exact Hb))) INOQ NE) as AP. clear - AP Hx. lia.
- destruct (Z_lt_le_dec x (a_oq a)) as [H|H]; [left; exact H|]. destruct (Z_lt_le_dec x (a_oq a + 32)) as [H'|H']; [|right; exact H'].
exfalso. pose proof (APL (sbd_old_qlsp s, a_oq a, 32) x ltac:(cbn [sb_blocks tl In]; do 3 right; left; reflexivity)
ltac:(unfold blk_addr, blk_size; cbn [fst snd]; clear - H H'; lia)) as H2.
rewrite outside_blocks_ivs in H2. exact (H2 bk Hb Hx). }
assert (AGO : agree_blocks asegs m25 m26 LNO).
{ apply (agree_blocks_of_munch asegs _ m25 m26 LNO MU26 WM26). intros bk x Hb Hx. pose proof (BOUT bk x (LNOA bk Hb) Hx) as H1. pose proof (LNOQ bk x Hb Hx) as H2.
cbn [outside]. split; [clear - H2; lia| split; [clear - H1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact I]]. }
tra AGO G0C (sbd_g0_mem s, a_g0 a, 256) ltac:(clear - JG0; lia).
tra AGO G1C (sbd_g1_mem s, a_g1 a, 256) ltac:(clear - JG1; lia).
tra AGO EXC (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s) ltac:(cbn [sI set_sbd_submodeID sbd_subframeSize] in JEXC; clear - JEXC; lia).
tra AGO IQC (sbd_interp_qlpc s, a_iq a, 32) ltac:(clear - JIQ; lia).
tra AGO PGC (sbd_pi_gain s, a_pg a, 16) ltac:(clear - JPG; lia).
tra AGO ERC (sbd_exc_rms s, a_er a, 16) ltac:(clear - JER; lia).
tra AGO MSPC (sbd_mem_sp s, a_msp a, 64) ltac:(clear - JMSP; lia).
assert (AGL26 : agree_blocks asegs m25 m26 LBL) by (apply (agree_blocks_sub asegs _ _ _ _ AGO); intros bk Hb; unfold LNO; apply in_app_iff; right; exact Hb).
pk_blocks AGL26. clear AGL26 AGO.
assert (KEEP : forall P, fp_local IO_FP P -> P m25 -> P m26).
{ intros P L Pm. apply (fp_local_munch IO_FP P _ m25 m26 L IO_img MU26); [| exact Pm]. intros x Hx. unfold SEGTOP_A in Hx. cbn [outside].
split; [clear - Hx BOQ0 BOQ1; lia| split; [clear - Hx LOV LOS; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact I]]. }
pk_io ERR_rep OUT_rep KEEP. clear KEEP.
assert (ART26 : X0ec.ART RT Σ6 m26).
{ apply (af_frame RT AF Σ6 m25 m26 lo ART25 LOWX); [| exact WM26]. intros a0 Ha. apply MU26. cbn [outside].
split; [| split; [| exact I]]; intros Hin; apply Ha.
- right; right; left. exists (a_oq a), 32. split; [exact INOQ| clear - Hin; lia].
- left. clear - Hin LOV SPT. unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK, USTACK_TOP in *. lia. }
assert (PF26 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m26).
{ apply (pres_fp_trans _ _ _ _ m m25 m26 PF). apply (pres_fp_of_munch _ _ _ _ _ m25 m26 MU26). intros x Hx Ho. cbn [outside] in Ho |- *.
destruct Ho as (_ & _ & _ & Ho). apply sb_outside_app_inv in Ho. destruct Ho as [Hb _]. rewrite outside_blocks_ivs in Hb.
split; [exact (Hb (sbd_old_qlsp s, a_oq a, 32) ltac:(rewrite ELBD; apply in_app_iff; left; cbn [sb_blocks In]; do 4 right; left; reflexivity))|].
split; [| exact I]. intros Hin. destruct (SPL x Hx) as [H1 | H1]; clear - H1 Hin LOW LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia. }
clear PF. rename PF26 into PF.
destruct (frame_live_apart RT AF Σ6 m25 fh kh _ _ ART25 INFHX INOQ) as (FOQ & _).
assert (POQ : a_oq a + 32 <= PD \/ PD + ND <= a_oq a)
by (apply (live_apart RT AF Σ6 m25 _ _ _ _ ART25 INOQ INPDX); exact (PDB (sbd_old_qlsp s, a_oq a, 32) ltac:(rewrite ELBD; apply in_app_iff; left; cbn [sb_blocks In]; do 4 right; left; reflexivity))).
trm MU26 WM26 SV ltac:(clear - BOQ0 BOQ1 LO608; lia).
trm MU26 WM26 FRB ltac:(clear - BOQ0 BOQ1 BF LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU26 WM26 FRS ltac:(clear - OQSH SHF1 SHF2 BF0 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU26 WM26 OC ltac:(rewrite LOWS; clear - BOQ0 BOQ1 FO1 FO2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU26 WM26 STB ltac:(clear - FOQ FS1 FS2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU26 WM26 BOBJ8 ltac:(clear - BOQ0 BOQ1 FA1 FA2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU26 WM26 BDAT8 ltac:(clear - POQ PD1 PD2 Lbs8 BD8 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU26 WM26 X9 ltac:(clear - OQS BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
apply (wr_at_transport asegs m25 m26 _ _) in WH1; [| exact WM26]. apply (wr_at_transport asegs m25 m26 _ _) in WH2; [| exact WM26].
apply (wr_at_transport asegs m25 m26 _ _) in WH3; [| exact WM26]. apply (wr_at_transport asegs m25 m26 _ _) in WH4; [| exact WM26].
assert (OF26 : offsh [(a_oq a, a_oq a + 32); (usp + -5088, usp + -160)])
by (cbn [offsh]; clear - LOS LOV OQSH; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK, SH_LO, SH_HI in *; lia).
assert (ACC26 : forall o n, acc asegs m25 o n -> 0 <= o -> o + n <= 140737488355328 -> acc asegs m26 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch asegs _ m25 m26 o n (conj H0 (conj H1 H)) MU26 (shfree_of_offsh _ o n OF26 H0 H1)))). }
assert (ACA26 : acc asegs m26 A 48) by (apply ACC26; [exact ACA25| clear - FA1 FP0; lia| clear - FA2 BF1 LO608 SPT; lia]).
assert (ACO26 : acc asegs m26 OUT 8000) by (apply ACC26; [exact ACO25| clear - FO1 FP0; lia| clear - FO2 BF1 LO608 SPT; lia]).
assert (ACT26 : acc asegs m26 STEREO 24) by (apply ACC26; [exact ACT25| clear - FS1 FP0; lia| clear - FS2 BF1 LO608 SPT; lia]).
assert (SSP26 : io_ssp m26).
{ apply (sbd_io_ssp_agree m25 m26 SSP25 (AF_DRV Σ6 m26 ART26)). intros a0 Ha. apply MU26. unfold X00a.SSP_GUARD in Ha. cbn [outside].
clear - Ha BOQ0 BOQ1 LOV LOS. unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *. split; [lia| split; [lia| exact I]]. }
destruct (af_acc_live RT AF Σ6 m26 S 160 ART26 INLX) as (_ & ACS26).
assert (OBS26 : aobj asegs m26 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO608 SPT; unfold APP_TOP; lia| exact ACS26]).
clear ACA25 ACO25 ACT25 ACC26 SSP25 ACS25 OBS25 ART25 MI25 OF26 MU26.

set (jV := SBJ (sj_last_ener j) (sj_seed j) (sj_pad1 j) (sj_pad2 j) (sj_g0 j) (sj_g1 j) (sj_exc j) voq1 (sj_iq j) (sj_msp j) (sj_pg j) (sj_er j)).
assert (JOKV : sb_junk_ok sI jV) by (exact (conj JP1 (conj JP2 (conj JG0 (conj JG1 (conj JEXC (conj Lvoq1 (conj JIQ (conj JMSP (conj JPG JER)))))))))).
assert (BUFS : sb_bufs asegs m26 a jV) by (exact (conj G0C (conj G1C (conj EXC (conj OQW1 (conj IQC (conj MSPC (conj PGC ERC)))))))).

assert (EU1088 : bv_unsigned (Z_to_bv 64 (usp + -1088)) = usp + -1088) by (apply unsigned_lit; clear - SPT LOV LOS; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
assert (POA7 : pois_above (rt_pois RT Σ6) (alloca_rr (usp + -1056) 32)).
{ intros e He. rewrite EP6, EP5, EP4, EP3, EP2, EP1 in He. destruct He as [<- | [<- | [<- | [<- | He]]]].
1-4: unfold pz_lo, alloca_rr; cbn [fst]; clear - SPA; Z.div_mod_to_equations; lia.
rewrite EPX in He. pose proof (POA e He) as H1. unfold alloca_rr. clear - H1 SPA. Z.div_mod_to_equations. lia. }
assert (COK7 : call_ok RT Σ6 m26 (Z_to_bv 64 (usp + -1088)) lo).
{ unfold call_ok. rewrite EU1088. split; [exact ST26|]. split; [exact LOWX|]. split; [clear - LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia|].
split; [clear - SPT; unfold USTACK_TOP in *; lia| clear - SPA; Z.div_mod_to_equations; lia]. }
cps_rt (APO Σ6 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m26 (usp + -1056) 32 lo FDO MST eq_refl eq_refl
ltac:(clear - SPA; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(rewrite EU1088; lia)
ltac:(unfold alloca_rr, USTACK_TOP; clear - SPA SPT; Z.div_mod_to_equations; lia)
POA7 ltac:(rewrite EF6, EF5, EF4, EF3, EF2, EF1, EFX; discriminate) ART26 MI26 COK7).
intros c18 (Σ7 & Hc18 & EP7 & EL7 & EF7 & ES7 & EC7).
destruct (ASTA_unpack RT Σ7 (PMfd F0 fs0) _ c18 Hc18) as (ms18 & PO18 & Hc18'); clear Hc18; cbv beta in PO18.
destruct PO18 as (m27 & v27 & RS27 & (ART27 & MI27 & WM27 & ST27) & PRES27 & ACV27 & ACK27).
cps_ret RS27.
rewrite EU1088 in PRES27, ST27.
clear POA7 COK7.
pose proof (pres_fp_of_pres _ _ _ [] _ _ PRES27) as PF27.
tr1 PF27 WM27 SV ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF27 WM27 FR26 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF27 WM27 HU5 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF27 WM27 FRB ltac:(fun x Hx => apply (CLF0g _ _ _ x INF); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF27 WM27 FRS ltac:(fun x Hx => apply (CLSFg _ _ _ x INF); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF27 WM27 OC ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); rewrite LOWS in Hx; clear - Hx FO1 FO2; lia) ltac:(fun x Hx => exact I).
tr1 PF27 WM27 STB ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FS1 FS2; lia) ltac:(fun x Hx => exact I).
tr1 PF27 WM27 BOBJ8 ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FA1 FA2; lia) ltac:(fun x Hx => exact I).
tr1 PF27 WM27 BDAT8 ltac:(fun x Hx => apply (CLLg _ _ _ PD ND x INPDX); clear - Hx PD1 PD2 Lbs8; lia) ltac:(fun x Hx => exact I).
tr1 PF27 WM27 X9 ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => exact I).
apply (wr_at_transport asegs m26 m27 _ _) in WH1; [| exact WM27]. apply (wr_at_transport asegs m26 m27 _ _) in WH2; [| exact WM27].
apply (wr_at_transport asegs m26 m27 _ _) in WH3; [| exact WM27]. apply (wr_at_transport asegs m26 m27 _ _) in WH4; [| exact WM27].
pk_pres_all RT PRES27 WM27 LALL LIVEA ERR_rep OUT_rep IO_FP IO_img.
assert (ACA27 : acc asegs m27 A 48) by (apply ACK27; [exact ACA26| clear - FA2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FA2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia]).
assert (ACO27 : acc asegs m27 OUT 8000) by (apply ACK27; [exact ACO26| clear - FO2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FO2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia]).
assert (ACT27 : acc asegs m27 STEREO 24) by (apply ACK27; [exact ACT26| clear - FS2 BF1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - FS2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia]).
assert (ACS27 : acc asegs m27 S 160) by (apply ACK27; [exact ACS26| clear - BS1 LOV' SPT; unfold USTACK_TOP; lia| left; clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia]).
assert (OBS27 : aobj asegs m27 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO608 SPT; unfold APP_TOP; lia| exact ACS27]).
assert (SSP27 : io_ssp m27).
{ apply (sbd_io_ssp_agree m26 m27 SSP26 (AF_DRV Σ7 m27 ART27)). intros a0 Ha. apply PRES27. right; left. exact (sbd_ssp_static _ Ha). }
assert (PF27' : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m27).
{ apply (pres_fp_trans _ _ _ _ m m26 m27 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ6) (rt_frames RT Σ6) (usp + -1088) [] m26 m27 PF27).
- intros e He. rewrite EL6, EL5, EL4, EL3, EL2, EL1, ELX. exact He.
- intros e He. rewrite EF6, EF5, EF4, EF3, EF2, EF1, EFX. right. exact He.
- clear; lia.
- intros x _ _. exact I. }
clear PF. rename PF27' into PF.
clear ACA26 ACO26 ACT26 ACS26 OBS26 SSP26 ART26 MI26 ST26 PF27 PRES27 ACK27 ACV27.
rewrite <- EL7 in LIVEA, LIVEL, LIVED, INLX, INPDX. rewrite <- EF7 in INF, INFHX. rewrite <- ES7 in LOWX.

assert (FSV : sbd_frame_size s = 160 \/ sbd_frame_size s = 320) by (rewrite IFS; destruct IMODE as [E|E]; rewrite E; cbn; [left| right]; reflexivity).
sb_unpack X9 as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_v9 usp S OUT f (sbmode_struct (sbd_mode s)) (sbd_frame_size s) _ sI a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
FR26 ltac:(gslot) ltac:(gslot) ltac:(gslot) ltac:(gslot) HD INS OBS27 S8 SPOS ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia) SOFF
ltac:(clear - FO1 FP0; lia) ltac:(clear - FSV; lia) ltac:(clear - FO2 BF1 LO608 SPT; lia)
ltac:(clear - LOS LOV; unfold SH_HI, RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia) SPH MI27).
clear HD FST PT LE SEED CFG IDC PAD.
destruct POST as (m28 & k28 & F28 & -> & MU28 & WM28 & MI28 & FR28).
clear FR26.
assert (ART28 : X0ec.ART RT Σ7 m28).
{ apply (af_frame RT AF Σ7 m27 m28 lo ART27 LOWX); [| exact WM28]. intros a0 Ha. apply MU28. cbn [outside]. split; [| exact I].
intros Hin. apply Ha. left. clear - Hin LOV' SPT. unfold USTACK_TOP. lia. }
assert (PF28 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m28).
{ apply (pres_fp_trans _ _ _ _ m m27 m28 PF). apply (pres_fp_of_munch _ _ _ _ _ m27 m28 MU28). intros x Hx Ho. cbn [outside]. split; [| exact I].
intros Hin. destruct (SPL x Hx) as [H1 | H1]; clear - H1 Hin LOW LOV'; lia. }
clear PF. rename PF28 into PF.
pk_munch_all MU28 WM28 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LOV'; cbn [outside]; split; [lia| exact I])
ltac:(fun x Hx => clear - Hx LOV' LOS; cbn [outside]; split; [lia| exact I]).
trm MU28 WM28 SV ltac:(clear; lia).
trm MU28 WM28 HU5 ltac:(clear; lia).
trm MU28 WM28 FRB ltac:(clear - BF LOV'; lia).
trm MU28 WM28 FRS ltac:(clear - BF0 LOV'; lia).
trm MU28 WM28 OC ltac:(rewrite LOWS; clear - FO2 BF1 LOV'; lia).
trm MU28 WM28 STB ltac:(clear - FS2 BF1 LOV'; lia).
trm MU28 WM28 BOBJ8 ltac:(clear - FA2 BF1 LOV'; lia).
trm MU28 WM28 BDAT8 ltac:(clear - BD8 LOV'; lia).
trm MU28 WM28 X9 ltac:(clear - BS1 LOV'; lia).
apply (stk_transport_disjoint asegs [(usp + -608, usp + -160)] m27 m28 lo (usp + -1088)) in ST27; [| exact MU28 | exact WM28 | cbn [disjoint_from]; clear; lia].
apply (wr_at_transport asegs m27 m28 _ _) in WH1; [| exact WM28]. apply (wr_at_transport asegs m27 m28 _ _) in WH2; [| exact WM28].
apply (wr_at_transport asegs m27 m28 _ _) in WH3; [| exact WM28]. apply (wr_at_transport asegs m27 m28 _ _) in WH4; [| exact WM28].
assert (OF28 : offsh [(usp + -608, usp + -160)]) by (cbn [offsh]; clear - LOS LOV'; unfold SH_LO, SH_HI in *; lia).
assert (ACC28 : forall o n, acc asegs m27 o n -> 0 <= o -> o + n <= 140737488355328 -> acc asegs m28 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch asegs _ m27 m28 o n (conj H0 (conj H1 H)) MU28 (shfree_of_offsh _ o n OF28 H0 H1)))). }
assert (ACA28 : acc asegs m28 A 48) by (apply ACC28; [exact ACA27| clear - FA1 FP0; lia| clear - FA2 BF1 LO608 SPT; lia]).
assert (ACO28 : acc asegs m28 OUT 8000) by (apply ACC28; [exact ACO27| clear - FO1 FP0; lia| clear - FO2 BF1 LO608 SPT; lia]).
assert (ACT28 : acc asegs m28 STEREO 24) by (apply ACC28; [exact ACT27| clear - FS1 FP0; lia| clear - FS2 BF1 LO608 SPT; lia]).
assert (SSP28 : io_ssp m28).
{ apply (sbd_io_ssp_agree m27 m28 SSP27 (AF_DRV Σ7 m28 ART28)). intros a0 Ha. apply MU28. unfold X00a.SSP_GUARD in Ha. cbn [outside].
clear - Ha LOV' LOS. split; [lia| exact I]. }
clear ACA27 ACO27 ACT27 ACC28 SSP27 ACS27 OBS27 ART27 MI27 OF28 MU28.

clear Hc Hc0 Hc1 Hc2 Hc3 EXR19 OQW1.

destruct (wr_at_rw_CB m28 (usp + -704) 96 WH1 ltac:(lia)) as (jk1 & HH1). clear WH1. change (Z.to_nat 96) with 96%nat in HH1.
apply (rw_cells_split_CB asegs _ _ [] 96 _ [] [32; 16; 48]%nat) in HH1; [| reflexivity]. cbn [mk_CB_cells app] in HH1.
apply rw_cells_uncons in HH1. destruct HH1 as (RZ1a & HH1). apply rw_cells_uncons in HH1. destruct HH1 as (BY1 & RZ1b).
cbn [csize] in BY1, RZ1b.
replace (usp + -704 + Z.of_nat 32) with (usp + -672) in BY1, RZ1b by lia.
replace (usp + -672 + Z.of_nat 16) with (usp + -656) in RZ1b by lia.
destruct (rw_cells_CB_f32 asegs m28 (usp + -672) 4 _ BY1) as (lpi & Llpi & LPI). clear BY1.
destruct (wr_at_rw_CB m28 (usp + -800) 96 WH2 ltac:(lia)) as (jk2 & HH2). clear WH2. change (Z.to_nat 96) with 96%nat in HH2.
apply (rw_cells_split_CB asegs _ _ [] 96 _ [] [32; 16; 48]%nat) in HH2; [| reflexivity]. cbn [mk_CB_cells app] in HH2.
apply rw_cells_uncons in HH2. destruct HH2 as (RZ2a & HH2). apply rw_cells_uncons in HH2. destruct HH2 as (BY2 & RZ2b).
cbn [csize] in BY2, RZ2b.
replace (usp + -800 + Z.of_nat 32) with (usp + -768) in BY2, RZ2b by lia.
replace (usp + -768 + Z.of_nat 16) with (usp + -752) in RZ2b by lia.
destruct (rw_cells_CB_f32 asegs m28 (usp + -768) 4 _ BY2) as (ler & Ller & LER). clear BY2.
destruct (wr_at_rw_CB m28 (usp + -896) 96 WH3 ltac:(lia)) as (jk3 & HH3). clear WH3. change (Z.to_nat 96) with 96%nat in HH3.
apply (rw_cells_split_CB asegs _ _ [] 96 _ [] [32; 32; 32]%nat) in HH3; [| reflexivity]. cbn [mk_CB_cells app] in HH3.
apply rw_cells_uncons in HH3. destruct HH3 as (RZ3a & HH3). apply rw_cells_uncons in HH3. destruct HH3 as (BY3 & RZ3b).
cbn [csize] in BY3, RZ3b.
replace (usp + -896 + Z.of_nat 32) with (usp + -864) in BY3, RZ3b by lia.
replace (usp + -864 + Z.of_nat 32) with (usp + -832) in RZ3b by lia.
destruct (rw_cells_CB_f32 asegs m28 (usp + -864) 8 _ BY3) as (lq & Llq & LQ). clear BY3.
destruct (wr_at_rw_CB m28 (usp + -992) 96 WH4 ltac:(lia)) as (jk4 & HH4). clear WH4. change (Z.to_nat 96) with 96%nat in HH4.
apply (rw_cells_split_CB asegs _ _ [] 96 _ [] [32; 32; 32]%nat) in HH4; [| reflexivity]. cbn [mk_CB_cells app] in HH4.
apply rw_cells_uncons in HH4. destruct HH4 as (RZ4a & HH4). apply rw_cells_uncons in HH4. destruct HH4 as (BY4 & RZ4b).
cbn [csize] in BY4, RZ4b.
replace (usp + -992 + Z.of_nat 32) with (usp + -960) in BY4, RZ4b by lia.
replace (usp + -960 + Z.of_nat 32) with (usp + -928) in RZ4b by lia.
destruct (rw_cells_CB_f32 asegs m28 (usp + -960) 8 _ BY4) as (liq & Lliq & LIQ). clear BY4.
apply (rw_cells_split_CB asegs _ _ [] 96 _ [] [32; 32; 32]%nat) in HU5; [| reflexivity]. cbn [mk_CB_cells app] in HU5.
apply rw_cells_uncons in HU5. destruct HU5 as (RZ5a & HU5). apply rw_cells_uncons in HU5. destruct HU5 as (BY5 & RZ5b).
cbn [csize] in BY5, RZ5b.
replace (usp + -1088 + Z.of_nat 32) with (usp + -1056) in BY5, RZ5b by lia.
replace (usp + -1056 + Z.of_nat 32) with (usp + -1024) in RZ5b by lia.
destruct (rw_cells_CB_f32 asegs m28 (usp + -1056) 8 _ BY5) as (lak & Llak & LAK). clear BY5.

set (vLA := SBV (g 1%nat) (g 15%nat) (g 31%nat) (g 32%nat) (g 33%nat) (Z_to_bv 64 0) (g 48%nat) (g 49%nat) (g 50%nat) (Z_to_bv 64 (usp + -1088))
(g 53%nat) (g 54%nat) (g 55%nat)).
assert (SLA : rw_cells asegs m28 (usp + -608) (sb_slots usp S OUT A f sf (sbmode_struct (sbd_mode sI)) (sbd_frame_size sI) vLA)).
{ unfold sb_fr in FR28. cbn [map seq] in FR28. cbn [fupds Nat.eqb sb_v9_upd] in FR28. rewrite G0, G10, G13, G26, G27, G38, G45, G51 in FR28.
unfold sb_slots, sha, vLA. cbn [v_8 v_120 v_248 v_256 v_264 v_296 v_384 v_392 v_400 v_416 v_424 v_432 v_440 sI set_sbd_submodeID sbd_mode sbd_frame_size].
exact FR28. }

set (X := SBI usp lo gp S OUT A D sI a (sb_buf_size b1) f sf fh kh PD ND (rt_live RT Σ) (rt_frames RT Σ) (rt_sp0 RT Σ) (rt_credit RT Σ7) (rt_pois RT Σ)).
assert (IH : sb_ihyps X).
{ constructor; cbn [x_usp x_lo x_gp x_S x_OUT x_A x_D x_s x_a x_bsz x_f x_sf x_fh x_kh x_PD x_ND x_live x_frames x_sp0 x_cr x_pois X].
- exact SPA.
- exact SPT.
- exact LOW.
- exact LOV.
- exact SPOS.
- exact S8.
- exact INV1.
- exact ISV.
- intros bk Hb. apply LIVE. rewrite ELBD. apply in_app_iff. left. exact Hb.
- pose proof NDUP as ND'. rewrite ELBD, map_app in ND'. exact (List.NoDup_app_remove_r _ _ ND').
- exact INFH.
- exact (conj FA1 (conj FA2 AAL)).
- exact (conj FO1 (conj FO2 OAL)).
- exact HAO.
- exact (conj INPD (conj PD1 PD2)).
- intros bk Hb. apply PDB. rewrite ELBD. apply in_app_iff. left. exact Hb.
- exact POA.
- reflexivity.
- exact AL. }
assert (BREP28 : bits_rep asegs m28 A D (lsp_bits LspUnquantHigh (sbw_bits b1))).
{ split; [exists rj8; split; [exact Lrj8| unfold bits_cells; exact BOBJ8]|].
split; [exists bs8; split; [apply (proj2 (u8arr_rw_CB m28 D bs8)); exact BDAT8| exact Hbs8]| exact BSIDE8]. }
assert (HLA : at_LA RT X (PMfd F0 fs0) m28 0 (lsp_bits LspUnquantHigh (sbw_bits b1)) c19).
{ exists Σ7, F28, fc25, m28, k28, vLA.
split; [exact Hc4|]. split; [exact FRM25|].
split.
{ unfold sb_sigma. cbn [x_live x_frames x_sp0 x_cr x_pois x_usp x_f X].
split; [rewrite EL7, EL6, EL5, EL4, EL3, EL2, EL1, ELX; reflexivity|].
split; [rewrite EF7, EF6, EF5, EF4, EF3, EF2, EF1, EFX; reflexivity|].
split; [rewrite ES7, ES6, ES5, ES4, ES3, ES2, ES1, ESX; reflexivity|].
split; [reflexivity|].
rewrite EP7, EP6, EP5, EP4, EP3, EP2, EP1, EPX. reflexivity. }
split; [| reflexivity].
exists (sj_last_ener j), (sj_seed j), (sj_pad1 j), (sj_pad2 j), lpi, ler, lq, liq, lak, (sj_exc j), voq1, (sj_iq j), (sj_msp j), (sj_pg j), (sj_er j), ows.
destruct BUFS as (_ & _ & EXC' & OQC' & IQC' & MSPC' & PGC' & ERC').
pose proof (proj1 (sb_pieces_iff m28 S sI a OUT j) X9) as PCS.
refine (conj ART28 (conj MI28 (conj ST27 (conj _ (conj (wmono_refl asegs m28) (conj SLA (conj LPI (conj Llpi (conj LER (conj Ller (conj LQ (conj Llq
(conj LIQ (conj Lliq (conj LAK (conj Llak (conj PCS (conj JP1 (conj JP2 (conj EXC' (conj JEXC (conj OQC' (conj Lvoq1 (conj IQC' (conj JIQ
(conj MSPC' (conj JMSP (conj PGC' (conj JPG (conj ERC' (conj JER (conj OC (conj LOWS (conj BREP28 (conj BOK8 (conj BSZ8 (conj ACA28 ACO28))))))))))))))))))))))))))))))))))))).
intros a0 _ _. reflexivity. }

refine (cps_realizes asegs _ _ T c19 (LOOP X (PMfd F0 fs0) m28 0 _ sm FDO MST IH ltac:(lia) ESM) HLA _).
intros c20 [(_ & HLA1) | (E & _)]; [| exfalso; clear - E; lia].
refine (cps_realizes asegs _ _ T c20 (LOOP X (PMfd F0 fs0) m28 (0 + 1) _ sm FDO MST IH ltac:(lia) ESM) HLA1 _).
intros c21 [(_ & HLA2) | (E & _)]; [| exfalso; clear - E; lia].
refine (cps_realizes asegs _ _ T c21 (LOOP X (PMfd F0 fs0) m28 (0 + 1 + 1) _ sm FDO MST IH ltac:(lia) ESM) HLA2 _).
intros c22 [(_ & HLA3) | (E & _)]; [| exfalso; clear - E; lia].
refine (cps_realizes asegs _ _ T c22 (LOOP X (PMfd F0 fs0) m28 (0 + 1 + 1 + 1) _ sm FDO MST IH ltac:(lia) ESM) HLA3 _).
intros c23 [(E & _) | (_ & HTA)]; [exfalso; clear - E; lia|].
clear HLA HLA1 HLA2 HLA3 Hc4.

destruct HTA as (Σ8 & F29 & fc29 & m29 & k29 & v29 & Hc29 & FRM29 & SIG29 & LM29 & V416).
destruct SIG29 as (EL8 & EF8 & ES8 & EC8 & EP8). cbn [x_live x_frames x_sp0 x_cr x_pois x_usp x_f X] in EL8, EF8, ES8, EC8, EP8.
destruct LM29 as (le29 & seed29 & pad129 & pad229 & lpi29 & ler29 & lq29 & liq29 & lak29 & vexc29 & voq29 & viq29 & vmsp29 & vpg29 & ver29 & ows29 &
ART29 & MI29 & ST29 & PF29 & WM29 & SL29 & LPI29 & Llpi29 & LER29 & Ller29 & LQ29 & Llq29 & LIQ29 & Lliq29 & LAK29 & Llak29 &
PCS29 & Lp129 & Lp229 & EXC29 & Lexc29 & OQ29 & Loq29 & IQ29 & Liq29 & MSP29 & Lmsp29 & PG29 & Lpg29 & ER29 & Ler29 &
OC29 & LOWS29 & BREP29 & BOK29 & BSZ29 & ACA29 & ACO29).
cbn [x_live x_frames x_f x_usp x_lo x_S x_OUT x_A x_D x_s x_a x_bsz x_gp x_sf X] in *.
unfold sb_WL in PF29. cbn [x_usp x_S x_OUT x_A x_a x_s X] in PF29.
clear G0C G1C EXC IQC MSPC PGC ERC.
destruct BUFS as (G0C & G1C & _ & _ & _ & _ & _ & _).
clear LPI LER LQ LIQ LAK Llpi Ller Llq Lliq Llak lpi ler lq liq lak SLA X9 OC LOWS BOBJ8 BDAT8.

assert (EL87 : rt_live RT Σ8 = rt_live RT Σ7) by (rewrite EL8, EL7, EL6, EL5, EL4, EL3, EL2, EL1, ELX; reflexivity).
assert (EF87 : rt_frames RT Σ8 = rt_frames RT Σ7) by (rewrite EF8, EF7, EF6, EF5, EF4, EF3, EF2, EF1, EFX; reflexivity).
assert (ES87 : rt_sp0 RT Σ8 = rt_sp0 RT Σ7) by (rewrite ES8, ES7, ES6, ES5, ES4, ES3, ES2, ES1, ESX; reflexivity).

assert (LAP : forall bk1 bk2, In bk1 LALL -> In bk2 LALL -> blk_addr bk1 <> blk_addr bk2 ->
blk_addr bk1 + blk_size bk1 <= blk_addr bk2 \/ blk_addr bk2 + blk_size bk2 <= blk_addr bk1)
by (intros bk1 bk2 H1 H2 NE; exact (live_apart RT AF Σ7 m28 _ _ _ _ ART28 (LIVEA bk1 H1) (LIVEA bk2 H2) NE)).

assert (OWL : forall x, (forall bk, In bk LALL -> ~ (blk_addr bk <= x < blk_addr bk + blk_size bk)) ->
(x < S + 132 \/ S + 136 <= x) -> (x < OUT \/ OUT + 8000 <= x) -> (x < A \/ A + 48 <= x) ->
(x < usp + -608 \/ usp + -160 <= x) -> (x < usp + -960 \/ usp + -928 <= x) -> (x < usp + -1056 \/ usp + -1024 <= x) ->
outside [(usp + -608, usp + -160); (usp + -960, usp + -928); (usp + -1056, usp + -1024); (S + 132, S + 136);
(a_exc a, a_exc a + 4 * sbd_subframeSize sI); (a_iq a, a_iq a + 32); (a_msp a, a_msp a + 64); (a_pg a, a_pg a + 16);
(a_er a, a_er a + 16); (OUT, OUT + 8000); (A, A + BITS_SIZEOF)] x).
{ intros x HB H1 H2 H3 H4 H5 H6.
pose proof (HB (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; do 2 right; left; reflexivity)) as B1.
pose proof (HB (sbd_interp_qlpc s, a_iq a, 32) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; do 4 right; left; reflexivity)) as B2.
pose proof (HB (sbd_pi_gain s, a_pg a, 16) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; do 5 right; left; reflexivity)) as B3.
pose proof (HB (sbd_exc_rms s, a_er a, 16) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; do 6 right; left; reflexivity)) as B4.
pose proof (HB (sbd_mem_sp s, a_msp a, 64) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; do 7 right; left; reflexivity)) as B5.
unfold blk_addr, blk_size in B1, B2, B3, B4, B5. cbn [fst snd] in B1, B2, B3, B4, B5. cbn [sI set_sbd_submodeID sbd_subframeSize].
cbn [outside]. unfold BITS_SIZEOF. clear - H1 H2 H3 H4 H5 H6 B1 B2 B3 B4 B5.
repeat split; lia. }

assert (NLB : forall x, (lo <= x \/ S <= x < S + 160 \/ fh <= x < fh + fs_size kh \/ PD <= x < PD + ND \/ f <= x < f + 64 \/ sf <= x < sf + 8) ->
forall bk, In bk LALL -> ~ (blk_addr bk <= x < blk_addr bk + blk_size bk)).
{ intros x Hx bk Hb Hin. pose proof (BOUT bk x Hb Hin) as H1. clear - Hx H1. lia. }
assert (INF8 : In (f, 0%nat) ((f, 0%nat) :: rt_frames RT Σ)) by (left; reflexivity).
assert (INFH8 : In (fh, kh) ((f, 0%nat) :: rt_frames RT Σ)) by (right; exact INFH).
tr1 PF29 WM29 SV ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => apply OWL; [apply NLB; left; clear - Hx LO608; lia| clear - Hx BS1 LO608; lia| clear - Hx FO2 BF1 LO608; lia| clear - Hx ALO LO608; lia| clear - Hx; lia..]).
tr1 PF29 WM29 FRB ltac:(fun x Hx => apply (CLF0g _ _ _ x INF8); clear - Hx; lia)
ltac:(fun x Hx => apply OWL; [apply NLB; right; right; right; right; left; clear - Hx; lia| clear - Hx SFA; unfold hid in *; lia
| clear - Hx FFA FO1 FO2; unfold hid in *; lia| clear - Hx FFA FA1 FA2; unfold hid in *; lia| clear - Hx BF LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia..]).
tr1 PF29 WM29 FRS ltac:(fun x Hx => apply (CLSFg _ _ _ x INF8); clear - Hx; lia)
ltac:(fun x Hx => apply OWL; [apply NLB; right; right; right; right; right; clear - Hx; lia| clear - Hx SFS SHF; unfold hid in *; subst sf; lia
| clear - Hx FPHI' SHF1 SHF2 FO1 FO2; unfold hid in *; lia| clear - Hx FPHI' SHF1 SHF2 FA1 FA2; unfold hid in *; lia
| clear - Hx BF0 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia..]).
tr1 PF29 WM29 STB ltac:(fun x Hx => apply (CLFg _ _ _ x INFH8); clear - Hx FS1 FS2; lia)
ltac:(fun x Hx => apply OWL; [apply NLB; right; right; left; clear - Hx FS1 FS2; lia| clear - Hx SFH FS1 FS2; unfold hid in *; lia
| clear - Hx HOS'; unfold hid in *; lia| clear - Hx HAS'; unfold hid in *; lia| clear - Hx FS2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia..]).
tr1 PF29 WM29 RZ1a ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => apply OWL; [apply NLB; left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx FO2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx ALO LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx; lia..]).
tr1 PF29 WM29 RZ1b ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => apply OWL; [apply NLB; left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx FO2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx ALO LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx; lia..]).
tr1 PF29 WM29 RZ2a ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => apply OWL; [apply NLB; left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx FO2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx ALO LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx; lia..]).
tr1 PF29 WM29 RZ2b ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => apply OWL; [apply NLB; left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx FO2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx ALO LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx; lia..]).
tr1 PF29 WM29 RZ3a ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => apply OWL; [apply NLB; left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx FO2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx ALO LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx; lia..]).
tr1 PF29 WM29 RZ3b ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => apply OWL; [apply NLB; left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx FO2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx ALO LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx; lia..]).
tr1 PF29 WM29 RZ4a ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => apply OWL; [apply NLB; left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx FO2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx ALO LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx; lia..]).
tr1 PF29 WM29 RZ4b ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => apply OWL; [apply NLB; left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx FO2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx ALO LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx; lia..]).
tr1 PF29 WM29 RZ5a ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => apply OWL; [apply NLB; left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx FO2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx ALO LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx; lia..]).
tr1 PF29 WM29 RZ5b ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => apply OWL; [apply NLB; left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx FO2 BF1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx ALO LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| clear - Hx; lia..]).

assert (NDA0 : List.NoDup [S; a_g0 a; a_g1 a; a_exc a; a_oq a; a_iq a; a_pg a; a_er a; a_msp a])
by (pose proof NDUP as ND'; rewrite ELBD, map_app in ND'; exact (List.NoDup_app_remove_r _ _ ND')).
assert (NDN : forall i0 j0 : nat, (i0 < 9)%nat -> (j0 < 9)%nat -> i0 <> j0 ->
nth i0 [S; a_g0 a; a_g1 a; a_exc a; a_oq a; a_iq a; a_pg a; a_er a; a_msp a] 0 <> nth j0 [S; a_g0 a; a_g1 a; a_exc a; a_oq a; a_iq a; a_pg a; a_er a; a_msp a] 0)
by (intros i0 j0 Hi Hj Hne E; apply Hne; exact (proj1 (NoDup_nth _ 0) NDA0 i0 j0 Hi Hj E)).

assert (WOUT : forall bk x, In bk ([(sbd_g0_mem s, a_g0 a, 256); (sbd_g1_mem s, a_g1 a, 256)] ++ LBL) ->
blk_addr bk <= x < blk_addr bk + blk_size bk ->
outside [(usp + -608, usp + -160); (usp + -960, usp + -928); (usp + -1056, usp + -1024); (S + 132, S + 136);
(a_exc a, a_exc a + 4 * sbd_subframeSize sI); (a_iq a, a_iq a + 32); (a_msp a, a_msp a + 64); (a_pg a, a_pg a + 16);
(a_er a, a_er a + 16); (OUT, OUT + 8000); (A, A + BITS_SIZEOF)] x).
{ intros bk x Hb Hx.
assert (HbA : In bk LALL).
{ unfold LALL. apply in_app_iff. apply in_app_iff in Hb. destruct Hb as [Hb | Hb]; [left| right; exact Hb].
clear - Hb. cbn [sb_blocks tl In] in Hb |- *. tauto. }
pose proof (BOUT bk x HbA Hx) as H1.

assert (WB : forall wb, In wb [(sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s); (sbd_interp_qlpc s, a_iq a, 32); (sbd_pi_gain s, a_pg a, 16);
(sbd_exc_rms s, a_er a, 16); (sbd_mem_sp s, a_msp a, 64)] -> ~ (blk_addr wb <= x < blk_addr wb + blk_size wb)).
{ intros wb Hw Hin.
assert (HwA : In wb (tl (sb_blocks s S a))) by (clear - Hw; cbn [sb_blocks tl In] in Hw |- *; tauto).
apply in_app_iff in Hb. destruct Hb as [Hb | Hb].
- assert (NE : blk_addr bk <> blk_addr wb).
{ clear - Hb Hw NDN. cbn [In] in Hb, Hw. unfold blk_addr.
destruct Hb as [<- |[<- | []]]; destruct Hw as [<- |[<- |[<- |[<- |[<- | []]]]]]; cbn [fst snd];
solve [ exact (NDN 1%nat 3%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) | exact (NDN 1%nat 5%nat ltac:(lia) ltac:(lia) ltac:(discriminate))
| exact (NDN 1%nat 6%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) | exact (NDN 1%nat 7%nat ltac:(lia) ltac:(lia) ltac:(discriminate))
| exact (NDN 1%nat 8%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) | exact (NDN 2%nat 3%nat ltac:(lia) ltac:(lia) ltac:(discriminate))
| exact (NDN 2%nat 5%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) | exact (NDN 2%nat 6%nat ltac:(lia) ltac:(lia) ltac:(discriminate))
| exact (NDN 2%nat 7%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) | exact (NDN 2%nat 8%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) ]. }
pose proof (LAP bk wb HbA ltac:(unfold LALL; apply in_app_iff; left; exact HwA) NE) as AP. clear - AP Hx Hin. lia.
- pose proof (APL wb x HwA Hin) as H2. rewrite outside_blocks_ivs in H2. exact (H2 bk Hb Hx). }
pose proof (WB (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s) ltac:(cbn [In]; left; reflexivity)) as W1.
pose proof (WB (sbd_interp_qlpc s, a_iq a, 32) ltac:(cbn [In]; right; left; reflexivity)) as W2.
pose proof (WB (sbd_pi_gain s, a_pg a, 16) ltac:(cbn [In]; do 2 right; left; reflexivity)) as W3.
pose proof (WB (sbd_exc_rms s, a_er a, 16) ltac:(cbn [In]; do 3 right; left; reflexivity)) as W4.
pose proof (WB (sbd_mem_sp s, a_msp a, 64) ltac:(cbn [In]; do 4 right; left; reflexivity)) as W5.
unfold blk_addr, blk_size in W1, W2, W3, W4, W5. cbn [fst snd] in W1, W2, W3, W4, W5. cbn [sI set_sbd_submodeID sbd_subframeSize].
cbn [outside]. unfold BITS_SIZEOF. clear - H1 W1 W2 W3 W4 W5 LOV FO1 FO2 FA1 FA2.
unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in LOV. repeat split; lia. }
assert (LIVEg : forall bk, In bk ([(sbd_g0_mem s, a_g0 a, 256); (sbd_g1_mem s, a_g1 a, 256)] ++ LBL) ->
In (blk_addr bk, blk_size bk) (rt_live RT Σ)).
{ intros bk Hb. apply LIVE. rewrite ELBD. apply in_app_iff. apply in_app_iff in Hb. destruct Hb as [Hb | Hb]; [left| right; exact Hb].
clear - Hb. cbn [sb_blocks In] in Hb |- *. tauto. }
assert (AG29 : agree_blocks asegs m28 m29 ([(sbd_g0_mem s, a_g0 a, 256); (sbd_g1_mem s, a_g1 a, 256)] ++ LBL))
by (apply (agree_blocks_of_pres_fp RT Σ _ _ _ m28 m29 _ PF29 WM29 LIVEg); exact WOUT).
change (sj_g0 jV) with (sj_g0 j) in G0C. change (sj_g1 jV) with (sj_g1 j) in G1C.
tra AG29 G0C (sbd_g0_mem s, a_g0 a, 256) ltac:(clear - JG0; lia).
tra AG29 G1C (sbd_g1_mem s, a_g1 a, 256) ltac:(clear - JG1; lia).
assert (AGL29 : agree_blocks asegs m28 m29 LBL) by (apply (agree_blocks_sub asegs _ _ _ _ AG29); intros bk Hb; apply in_app_iff; right; exact Hb).
pk_blocks AGL29. clear AGL29 AG29.
assert (OIMG : forall y, 65536 <= y < 6627328 ->
outside [(usp + -608, usp + -160); (usp + -960, usp + -928); (usp + -1056, usp + -1024); (S + 132, S + 136);
(a_exc a, a_exc a + 4 * sbd_subframeSize sI); (a_iq a, a_iq a + 32); (a_msp a, a_msp a + 64); (a_pg a, a_pg a + 16);
(a_er a, a_er a + 16); (OUT, OUT + 8000); (A, A + BITS_SIZEOF)] y).
{ intros y Hy. apply OWL; [intros bk Hb Hin; pose proof (BOUT bk y Hb Hin) as H1; clear - H1 Hy; lia| clear - Hy SIMG; lia| clear - Hy FO1 FPIMG; lia
| clear - Hy AIMG; lia| clear - Hy LOV LOS; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia..]. }
pk_io_fp PF29 ERR_rep OUT_rep IO_FP IO_img ltac:(fun y Hy => apply OIMG; exact Hy).
assert (SSP29 : io_ssp m29).
{ apply (sbd_io_ssp_agree m28 m29 SSP28 (AF_DRV Σ8 m29 ART29)). intros a0 Ha. apply PF29; [right; left; exact (sbd_ssp_static _ Ha)|].
unfold X00a.SSP_GUARD in Ha. apply OIMG. clear - Ha. lia. }

assert (PF29' : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m29).
{ apply (pres_fp_trans _ _ _ _ m m28 m29 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ) ((f, 0%nat) :: rt_frames RT Σ) (usp + -1088) _ m28 m29 PF29).
- intros e He. exact He.
- intros e He. right. exact He.
- clear; lia.
- intros x Hx Ho. cbn [outside] in Ho. destruct Ho as (HA & HO & _ & Ho). apply sb_outside_app_inv in Ho. destruct Ho as [Hb _].
rewrite ELBD in Hb. pose proof (outside_blocks_app_l _ _ x Hb) as Hb1. rewrite outside_blocks_ivs in Hb1.
pose proof (Hb1 (sbd_blk s, S, SBSTATE_SIZEOF) ltac:(cbn [sb_blocks In]; left; reflexivity)) as N0.
pose proof (Hb1 (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s) ltac:(cbn [sb_blocks In]; do 3 right; left; reflexivity)) as N1.
pose proof (Hb1 (sbd_interp_qlpc s, a_iq a, 32) ltac:(cbn [sb_blocks In]; do 5 right; left; reflexivity)) as N2.
pose proof (Hb1 (sbd_pi_gain s, a_pg a, 16) ltac:(cbn [sb_blocks In]; do 6 right; left; reflexivity)) as N3.
pose proof (Hb1 (sbd_exc_rms s, a_er a, 16) ltac:(cbn [sb_blocks In]; do 7 right; left; reflexivity)) as N4.
pose proof (Hb1 (sbd_mem_sp s, a_msp a, 64) ltac:(cbn [sb_blocks In]; do 8 right; left; reflexivity)) as N5.
unfold blk_addr, blk_size, SBSTATE_SIZEOF in N0, N1, N2, N3, N4, N5. cbn [fst snd] in N0, N1, N2, N3, N4, N5. cbn [sI set_sbd_submodeID sbd_subframeSize].
pose proof (SPL x Hx) as HSP.
cbn [outside]. unfold BITS_SIZEOF. clear - HA HO N0 N1 N2 N3 N4 N5 HSP LOW LOV.
unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in LOV. repeat split; lia. }
clear PF. rename PF29' into PF.

destruct PCS29 as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
destruct BREP29 as ((rj29 & Lrj29 & BOBJ29) & (bs29 & BDAT29 & Hbs29) & BSIDE29). apply u8arr_rw_CB in BDAT29. unfold bits_cells in BOBJ29.
assert (BSZ29' : sb_buf_size (sbsub_bits sm (sbsub_bits sm (sbsub_bits sm (sbsub_bits sm (lsp_bits LspUnquantHigh (sbw_bits b1)))))) = sb_buf_size b1) by exact BSZ29.
assert (Lbs29 : Z.of_nat (length bs29) = sb_buf_size b1)
by (pose proof BOK29 as OK'; unfold bits_ok in OK'; rewrite Hbs29, zlength_map_unsigned, BSZ29' in OK'; clear - OK'; lia).
assert (BD29 : D + Z.of_nat (length bs29) <= lo) by (rewrite Lbs29; exact DLO).
destruct (af_acc_live RT AF Σ8 m29 S 160 ART29 ltac:(rewrite EL8; exact INL)) as (_ & ACS29).
assert (OBS29 : aobj asegs m29 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO608 SPT; unfold APP_TOP; lia| exact ACS29]).
cps_seg (sbd_t1 usp lo S OUT A f sf (sbmode_struct (sbd_mode sI)) (sbd_frame_size sI) v29 sI a le29 k29 _ _ _ _ _
SL29 HD PT LE eq_refl ltac:(cbn [sI set_sbd_submodeID sbd_full_frame_size sbd_frame_size]; exact IFFS) ltac:(cbn [sI set_sbd_submodeID sbd_frame_size]; exact FSV)
OBS29 S8 SPOS BS1 SOFF ltac:(unfold IMG_TOP; clear - SIMG; lia) ltac:(clear - FO1 FP0; lia) ltac:(clear - FO2 BF1 LO608 SPT; lia)
ST29 ltac:(clear - LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia) LOS ltac:(clear - SPH; lia) MI29 FRM29).
clear LE OBS29 ACS29.
destruct POST as (m30 & xt030 & xt130 & xt230 & xt330 & xt430 & xt530 & xt630 & xs330 & xs430 & xs530 & xs730 & F30 & fc30 & le30 & ja30 &
-> & MU30 & WM30 & MI30 & ST30 & FRM30 & LE30 & STK30).
clear ST29.

rewrite <- EL87 in LIVEA, LIVEL, LIVED, INLX, INPDX. rewrite <- EF87 in INF, INFHX. rewrite <- ES87 in LOWX.

set (BL := [(S, 160); (a_g0 a, 256); (a_g1 a, 256); (a_exc a, 4 * sbd_subframeSize s); (a_oq a, 32); (a_iq a, 32); (a_pg a, 16); (a_er a, 16); (a_msp a, 64)]).
assert (LIVBL : forall e, In e BL -> In e (rt_live RT Σ8)).
{ intros e He. unfold BL in He. cbn [In] in He.
destruct He as [<- |[<- |[<- |[<- |[<- |[<- |[<- |[<- |[<- | []]]]]]]]]].
1: exact INLX.
1: exact (LIVEA (sbd_g0_mem s, a_g0 a, 256) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; left; reflexivity)).
1: exact (LIVEA (sbd_g1_mem s, a_g1 a, 256) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; right; left; reflexivity)).
1: exact (LIVEA (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; do 2 right; left; reflexivity)).
1: exact (LIVEA (sbd_old_qlsp s, a_oq a, 32) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; do 3 right; left; reflexivity)).
1: exact (LIVEA (sbd_interp_qlpc s, a_iq a, 32) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; do 4 right; left; reflexivity)).
1: exact (LIVEA (sbd_pi_gain s, a_pg a, 16) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; do 5 right; left; reflexivity)).
1: exact (LIVEA (sbd_exc_rms s, a_er a, 16) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; do 6 right; left; reflexivity)).
1: exact (LIVEA (sbd_mem_sp s, a_msp a, 64) ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; do 7 right; left; reflexivity)). }
assert (SBAP : forall i0 j0 : nat, (i0 < 9)%nat -> (j0 < 9)%nat -> i0 <> j0 ->
fst (nth i0 BL (0, 0)) + snd (nth i0 BL (0, 0)) <= fst (nth j0 BL (0, 0)) \/ fst (nth j0 BL (0, 0)) + snd (nth j0 BL (0, 0)) <= fst (nth i0 BL (0, 0))).
{ intros i0 j0 Hi Hj Hne.
assert (Ei : nth i0 BL (0, 0) = (fst (nth i0 BL (0, 0)), snd (nth i0 BL (0, 0)))) by (destruct (nth i0 BL (0, 0)); reflexivity).
assert (Ej : nth j0 BL (0, 0) = (fst (nth j0 BL (0, 0)), snd (nth j0 BL (0, 0)))) by (destruct (nth j0 BL (0, 0)); reflexivity).
apply (live_apart RT AF Σ8 m29 _ _ _ _ ART29).
- rewrite <- Ei. apply LIVBL. apply nth_In. exact Hi.
- rewrite <- Ej. apply LIVBL. apply nth_In. exact Hj.
- rewrite <- (map_nth fst BL (0, 0) i0), <- (map_nth fst BL (0, 0) j0). exact (NDN i0 j0 Hi Hj Hne). }
pose proof (SBAP 1%nat 0%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AP10. pose proof (SBAP 2%nat 0%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AP20.
pose proof (SBAP 3%nat 0%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AP30. pose proof (SBAP 4%nat 0%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AP40.
pose proof (SBAP 5%nat 0%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AP50. pose proof (SBAP 6%nat 0%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AP60.
pose proof (SBAP 7%nat 0%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AP70. pose proof (SBAP 8%nat 0%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AP80.
cbn [nth BL fst snd] in AP10, AP20, AP30, AP40, AP50, AP60, AP70, AP80.

destruct (live_below_lo RT AF Σ8 m29 _ _ lo ART29 (LIVBL (a_g0 a, 256) ltac:(unfold BL; cbn [In]; do 1 right; left; reflexivity)) LOWX) as (_ & LOG0 & _).
destruct (live_below_lo RT AF Σ8 m29 _ _ lo ART29 (LIVBL (a_g1 a, 256) ltac:(unfold BL; cbn [In]; do 2 right; left; reflexivity)) LOWX) as (_ & LOG1 & _).
destruct (live_below_lo RT AF Σ8 m29 _ _ lo ART29 (LIVBL (a_exc a, 4 * sbd_subframeSize s) ltac:(unfold BL; cbn [In]; do 3 right; left; reflexivity)) LOWX) as (_ & LOEX & _).
destruct (live_below_lo RT AF Σ8 m29 _ _ lo ART29 (LIVBL (a_oq a, 32) ltac:(unfold BL; cbn [In]; do 4 right; left; reflexivity)) LOWX) as (_ & LOOQ & _).
destruct (live_below_lo RT AF Σ8 m29 _ _ lo ART29 (LIVBL (a_iq a, 32) ltac:(unfold BL; cbn [In]; do 5 right; left; reflexivity)) LOWX) as (_ & LOIQ & _).
destruct (live_below_lo RT AF Σ8 m29 _ _ lo ART29 (LIVBL (a_pg a, 16) ltac:(unfold BL; cbn [In]; do 6 right; left; reflexivity)) LOWX) as (_ & LOPG & _).
destruct (live_below_lo RT AF Σ8 m29 _ _ lo ART29 (LIVBL (a_er a, 16) ltac:(unfold BL; cbn [In]; do 7 right; left; reflexivity)) LOWX) as (_ & LOER & _).
destruct (live_below_lo RT AF Σ8 m29 _ _ lo ART29 (LIVBL (a_msp a, 64) ltac:(unfold BL; cbn [In]; do 8 right; left; reflexivity)) LOWX) as (_ & LOMS & _).

assert (ART30 : X0ec.ART RT Σ8 m30).
{ apply (af_frame RT AF Σ8 m29 m30 lo ART29 LOWX); [| exact WM30]. intros a0 Ha. apply MU30. cbn [outside].
split; [| split; [| exact I]]; intros Hin; apply Ha.
- right; right; left. exists S, 160. split; [exact INLX| clear - Hin; lia].
- left. clear - Hin LOV SPT. unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK, USTACK_TOP in *. lia. }
assert (PF30 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m30).
{ apply (pres_fp_trans _ _ _ _ m m29 m30 PF). apply (pres_fp_of_munch _ _ _ _ _ m29 m30 MU30). intros x Hx Ho. cbn [outside] in Ho |- *.
destruct Ho as (_ & _ & _ & Ho). apply sb_outside_app_inv in Ho. destruct Ho as [Hb _]. rewrite outside_blocks_ivs in Hb.
pose proof (Hb (sbd_blk s, S, SBSTATE_SIZEOF) ltac:(rewrite ELBD; apply in_app_iff; left; cbn [sb_blocks In]; left; reflexivity)) as N0.
unfold blk_addr, blk_size, SBSTATE_SIZEOF in N0. cbn [fst snd] in N0.
split; [clear - N0; lia|]. split; [| exact I]. intros Hin. destruct (SPL x Hx) as [H1 | H1]; clear - H1 Hin LOW LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia. }
clear PF. rename PF30 into PF.
pk_munch_all MU30 WM30 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LOV; cbn [outside]; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in LOV;
split; [lia| split; [lia| exact I]])
ltac:(fun x Hx => clear - Hx LOV LOS SIMG; cbn [outside]; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in LOV; split; [lia| split; [lia| exact I]]).
trm MU30 WM30 SV ltac:(clear - BS1 LO608; lia).
trm MU30 WM30 SL29 ltac:(clear - BS1 LO608; lia).
trm MU30 WM30 LPI29 ltac:(rewrite Llpi29; clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 LER29 ltac:(rewrite Ller29; clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 LQ29 ltac:(rewrite Llq29; clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 LIQ29 ltac:(rewrite Lliq29; clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 LAK29 ltac:(rewrite Llak29; clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 RZ1a ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 RZ1b ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 RZ2a ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 RZ2b ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 RZ3a ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 RZ3b ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 RZ4a ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 RZ4b ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 RZ5a ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 RZ5b ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 FRB ltac:(clear - SFA BF LOV; unfold hid, RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 FRS ltac:(clear - SFS SHF BF0 LOV; unfold hid, RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; subst sf; lia).
trm MU30 WM30 STB ltac:(clear - SFH FS1 FS2 BF1 LOV; unfold hid, RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 OC29 ltac:(rewrite LOWS29; clear - SFH FO1 FO2 BF1 LOV; unfold hid, RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 BOBJ29 ltac:(clear - SFH FA1 FA2 BF1 LOV; unfold hid, RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 BDAT29 ltac:(clear - SPD PD1 PD2 Lbs29 BD29 LOV; unfold hid, RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 G0C ltac:(rewrite JG0; clear - AP10 LOG0 LOV BS1; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 G1C ltac:(rewrite JG1; clear - AP20 LOG1 LOV BS1; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 EXC29 ltac:(clear - AP30 LOEX Lexc29 LOV BS1; cbn [sI set_sbd_submodeID sbd_subframeSize] in Lexc29; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 OQ29 ltac:(rewrite Loq29; clear - AP40 LOOQ LOV BS1; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 IQ29 ltac:(rewrite Liq29; clear - AP50 LOIQ LOV BS1; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 PG29 ltac:(rewrite Lpg29; clear - AP60 LOPG LOV BS1; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 ER29 ltac:(rewrite Ler29; clear - AP70 LOER LOV BS1; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 MSP29 ltac:(rewrite Lmsp29; clear - AP80 LOMS LOV BS1; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 HD ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 FST ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 PT ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 SEED ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 CFG ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 IDC ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU30 WM30 PAD ltac:(clear - BS1 LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
assert (OF30 : offsh [(S + 128, S + 132); (usp + -1104, usp + -1088)]) by (cbn [offsh]; clear - LOS LOV SOFF; unfold hid, RT_STACK, SB_LOOP_STACK, INNOV_STACK, SH_LO, SH_HI in *; lia).
assert (ACC30 : forall o n, acc asegs m29 o n -> 0 <= o -> o + n <= 140737488355328 -> acc asegs m30 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch asegs _ m29 m30 o n (conj H0 (conj H1 H)) MU30 (shfree_of_offsh _ o n OF30 H0 H1)))). }
assert (ACO30 : acc asegs m30 OUT 8000) by (apply ACC30; [exact ACO29| clear - FO1 FP0; lia| clear - FO2 BF1 LO608 SPT; lia]).
assert (SSP30 : io_ssp m30).
{ apply (sbd_io_ssp_agree m29 m30 SSP29 (AF_DRV Σ8 m30 ART30)). intros a0 Ha. apply MU30. unfold X00a.SSP_GUARD in Ha. cbn [outside].
clear - Ha LOV LOS SIMG. unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *. split; [lia| split; [lia| exact I]]. }
clear ACA29 ACO29 ACC30 SSP29 ART29 MI29 OF30 MU30.

set (fsz := sbd_frame_size sI) in *.
assert (FSN2 : Z.of_nat (Z.to_nat (2 * fsz)) = 2 * fsz) by (unfold fsz; cbn [sI set_sbd_submodeID sbd_frame_size]; clear - FSV; lia).
apply (f32_split asegs m30 OUT ows29 (Z.to_nat (2 * fsz))) in OC29; [| rewrite LOWS29; unfold fsz; cbn [sI set_sbd_submodeID sbd_frame_size]; clear - FSV; lia].
destruct OC29 as (OCq & OCr). rewrite FSN2 in OCr.
assert (LOCq : Z.of_nat (length (firstn (Z.to_nat (2 * fsz)) ows29)) = 2 * fsz)
by (rewrite length_firstn, LOWS29; unfold fsz; cbn [sI set_sbd_submodeID sbd_frame_size]; clear - FSV; lia).
assert (LOCr : length (skipn (Z.to_nat (2 * fsz)) ows29) = (2000 - Z.to_nat (2 * fsz))%nat) by (rewrite length_skipn, LOWS29; reflexivity).
generalize dependent (firstn (Z.to_nat (2 * fsz)) ows29). intros owq OCq LOCq.
generalize dependent (skipn (Z.to_nat (2 * fsz)) ows29). intros owr OCr LOCr.
assert (FSQ : fsz = 160 \/ fsz = 320) by (unfold fsz; cbn [sI set_sbd_submodeID sbd_frame_size]; exact FSV).
assert (QN : 2 * fsz = 320 \/ 2 * fsz = 640) by (clear - FSQ; lia).
assert (EA1 : Z_to_bv 64 (OUT + 4 * fsz) = Z_to_bv 64 (OUT + 2 * (2 * fsz))) by (f_equal; clear; lia).
assert (EA2 : Z_to_bv 64 sb_A_H0 = Z_to_bv 64 0x27000) by reflexivity.
assert (EU1104 : bv_unsigned (Z_to_bv 64 (usp + -1104)) = usp + -1104) by (apply unsigned_lit; clear - SPT LOV LOS; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
assert (ING0 : In (a_g0 a, 256) (rt_live RT Σ8)) by (apply LIVBL; unfold BL; cbn [In]; do 1 right; left; reflexivity).
assert (ING1 : In (a_g1 a, 256) (rt_live RT Σ8)) by (apply LIVBL; unfold BL; cbn [In]; do 2 right; left; reflexivity).
pose proof (SBAP 1%nat 2%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as G01. cbn [nth BL fst snd] in G01.
pose proof AL as (G08 & G18 & _).
assert (POAq : pois_above (rt_pois RT Σ8) (bv_unsigned (Z_to_bv 64 (usp + -1104)))).
{ rewrite EU1104. intros e He. rewrite EP8 in He. cbn [sb_pois x_usp X app] in He.
destruct He as [<- |[<- |[<- |[<- |[<- | He]]]]]; [unfold pz_lo; cbn [fst]; clear; lia ..|].
pose proof (POA e He) as H1. clear - H1. lia. }
cps_rt (QMF16 (2 * fsz) QN Σ8 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m30
OUT (a_g0 a) (a_g1 a) lo fh (a_g0 a) 256 (a_g1 a) 256 kh owq (sj_g0 j) (sj_g1 j)
FDO MST eq_refl EA1 EA2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
OCq LOCq INFHX FO1 ltac:(clear - FO2 FSQ; lia)
(acc_sub asegs m30 OUT 8000 OUT (4 * (2 * fsz)) ACO30 ltac:(clear; lia) ltac:(clear - FSQ; lia)) OAL
G0C JG0 ING0 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - G08; Z.div_mod_to_equations; lia)
G1C JG1 ING1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - G18; Z.div_mod_to_equations; lia)
G01 POAq FRM30 ART30 MI30 ltac:(rewrite EU1104; exact ST30) LOWX
ltac:(rewrite EU1104; clear - LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)
ltac:(rewrite EU1104; clear - SPT; unfold USTACK_TOP in *; lia)
ltac:(rewrite EU1104; clear - SPA; Z.div_mod_to_equations; lia)).
intros cq (Σ9 & Hcq & EL9 & EF9 & ES9 & EC9 & EP9).
cps_unpack_lib Hcq as (v31 & m31 & owq' & g0q & g1q & RS31 & (ART31 & MI31 & WM31 & ST31) & PRES31 & OCq' & LOCq' & G0Q & LG0Q & G1Q & LG1Q & ACQ).
try rewrite EU1104 in PRES31. try rewrite EU1104 in ST31.
clear OCq G0C G1C POAq.

pose proof (SBAP 3%nat 1%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AEX1. pose proof (SBAP 3%nat 2%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AEX2.
pose proof (SBAP 4%nat 1%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AOQ1. pose proof (SBAP 4%nat 2%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AOQ2.
pose proof (SBAP 5%nat 1%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AIQ1. pose proof (SBAP 5%nat 2%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AIQ2.
pose proof (SBAP 6%nat 1%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as APG1. pose proof (SBAP 6%nat 2%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as APG2.
pose proof (SBAP 7%nat 1%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AER1. pose proof (SBAP 7%nat 2%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AER2.
pose proof (SBAP 8%nat 1%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AMS1. pose proof (SBAP 8%nat 2%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AMS2.
cbn [nth BL fst snd] in AEX1, AEX2, AOQ1, AOQ2, AIQ1, AIQ2, APG1, APG2, AER1, AER2, AMS1, AMS2.
destruct (frame_live_apart RT AF Σ8 m30 fh kh PD ND ART30 INFHX INPDX) as (FLPD & _).
assert (G0IN : In (sbd_g0_mem s, a_g0 a, 256) LALL) by (unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; left; reflexivity).
assert (G1IN : In (sbd_g1_mem s, a_g1 a, 256) LALL) by (unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; right; left; reflexivity).

assert (OG : forall x, (lo <= x \/ S <= x < S + 160 \/ fh <= x < fh + fs_size kh \/ PD <= x < PD + ND \/ f <= x < f + 64 \/ sf <= x < sf + 8) ->
~ (a_g0 a <= x < a_g0 a + 256) /\ ~ (a_g1 a <= x < a_g1 a + 256)).
{ intros x Hx. split; intros Hin.
- pose proof (BOUT _ x G0IN ltac:(unfold blk_addr, blk_size; cbn [fst snd]; exact Hin)) as H1. clear - Hx H1. lia.
- pose proof (BOUT _ x G1IN ltac:(unfold blk_addr, blk_size; cbn [fst snd]; exact Hin)) as H1. clear - Hx H1. lia. }
assert (OQF : forall x, ~ (OUT <= x < OUT + 4 * (2 * fsz)) -> ~ (a_g0 a <= x < a_g0 a + 256) -> ~ (a_g1 a <= x < a_g1 a + 256) ->
outside [(OUT, OUT + 4 * (2 * fsz)); (a_g0 a, a_g0 a + 256); (a_g1 a, a_g1 a + 256)] x)
by (intros x H1 H2 H3; cbn [outside]; exact (conj H1 (conj H2 (conj H3 I)))).
tr1 PRES31 WM31 SV ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 SL29 ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 LPI29 ltac:(fun x Hx => apply CLSg; rewrite Llpi29 in Hx; clear - Hx; lia)
ltac:(fun x Hx => rewrite Llpi29 in Hx; destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 LER29 ltac:(fun x Hx => apply CLSg; rewrite Ller29 in Hx; clear - Hx; lia)
ltac:(fun x Hx => rewrite Ller29 in Hx; destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 LQ29 ltac:(fun x Hx => apply CLSg; rewrite Llq29 in Hx; clear - Hx; lia)
ltac:(fun x Hx => rewrite Llq29 in Hx; destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 LIQ29 ltac:(fun x Hx => apply CLSg; rewrite Lliq29 in Hx; clear - Hx; lia)
ltac:(fun x Hx => rewrite Lliq29 in Hx; destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 LAK29 ltac:(fun x Hx => apply CLSg; rewrite Llak29 in Hx; clear - Hx; lia)
ltac:(fun x Hx => rewrite Llak29 in Hx; destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 STK30 ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 RZ1a ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 RZ1b ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 RZ2a ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 RZ2b ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 RZ3a ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 RZ3b ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 RZ4a ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 RZ4b ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 RZ5a ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 RZ5b ltac:(fun x Hx => apply CLSg; clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(left; clear - Hx LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)) as (O1 & O2); apply OQF; [clear - Hx FO2 BF1 LOV FSQ; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 FRB ltac:(fun x Hx => apply (CLF0g _ _ _ x INF); clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(right; right; right; right; left; clear - Hx; lia)) as (O1 & O2); apply OQF; [clear - Hx FFA FO1 FO2 FSQ; unfold hid in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 FRS ltac:(fun x Hx => apply (CLSFg _ _ _ x INF); clear - Hx; lia)
ltac:(fun x Hx => destruct (OG x ltac:(right; right; right; right; right; clear - Hx; lia)) as (O1 & O2); apply OQF; [clear - Hx FPHI' SHF1 SHF2 FO1 FO2 FSQ; unfold hid in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 STB ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FS1 FS2; lia)
ltac:(fun x Hx => destruct (OG x ltac:(right; right; left; clear - Hx FS1 FS2; lia)) as (O1 & O2); apply OQF; [clear - Hx HOS' FSQ; unfold hid in *; lia| exact O1| exact O2]).
assert (LOCr' : length owr = (2000 - Z.to_nat (2 * sbd_frame_size s))%nat) by exact LOCr.
tr1 PRES31 WM31 OCr ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FO1 FO2 FSV LOCr'; lia)
ltac:(fun x Hx => destruct (OG x ltac:(right; right; left; clear - Hx FO1 FO2 FSV LOCr'; lia)) as (O1 & O2); apply OQF;
[unfold fsz; cbn [sI set_sbd_submodeID sbd_frame_size]; clear - Hx FSV; lia| exact O1| exact O2]).
tr1 PRES31 WM31 BOBJ29 ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FA1 FA2; lia)
ltac:(fun x Hx => destruct (OG x ltac:(right; right; left; clear - Hx FA1 FA2; lia)) as (O1 & O2); apply OQF; [clear - Hx HAO' FSQ; unfold hid in *; lia| exact O1| exact O2]).
tr1 PRES31 WM31 BDAT29 ltac:(fun x Hx => apply (CLLg _ _ _ PD ND x INPDX); clear - Hx PD1 PD2 Lbs29; lia)
ltac:(fun x Hx => destruct (OG x ltac:(right; right; right; left; clear - Hx PD1 PD2 Lbs29; lia)) as (O1 & O2); apply OQF; [clear - Hx FLPD PD1 PD2 Lbs29 FO1 FO2 FSQ; lia| exact O1| exact O2]).
tr1 PRES31 WM31 EXC29 ltac:(fun x Hx => apply (CLLg _ _ _ (a_exc a) (4 * sbd_subframeSize s) x (LIVBL (a_exc a, 4 * sbd_subframeSize s) ltac:(unfold BL; cbn [In]; repeat (first [left; reflexivity | right])))); cbn [sI set_sbd_submodeID sbd_subframeSize] in Lexc29; rewrite ?cells_size_f32 in Hx; clear - Hx Lexc29; lia)
ltac:(fun x Hx => cbn [sI set_sbd_submodeID sbd_subframeSize] in Lexc29; rewrite ?cells_size_f32 in Hx; apply OQF; [intro Hin; pose proof (BOUT (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s) x ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; repeat (first [left; reflexivity | right])) ltac:(unfold blk_addr, blk_size; cbn [fst snd]; clear - Hx Lexc29; lia)) as H1; clear - H1 Hin FO1 FO2 FSQ; lia
| clear - Hx Lexc29 AEX1; lia| clear - Hx Lexc29 AEX2; lia]).
tr1 PRES31 WM31 OQ29 ltac:(fun x Hx => apply (CLLg _ _ _ (a_oq a) (32) x (LIVBL (a_oq a, 32) ltac:(unfold BL; cbn [In]; repeat (first [left; reflexivity | right])))); rewrite Loq29 in Hx; clear - Hx Loq29; lia)
ltac:(fun x Hx => rewrite Loq29 in Hx; apply OQF; [intro Hin; pose proof (BOUT (sbd_old_qlsp s, a_oq a, 32) x ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; repeat (first [left; reflexivity | right])) ltac:(unfold blk_addr, blk_size; cbn [fst snd]; clear - Hx Loq29; lia)) as H1; clear - H1 Hin FO1 FO2 FSQ; lia
| clear - Hx Loq29 AOQ1; lia| clear - Hx Loq29 AOQ2; lia]).
tr1 PRES31 WM31 IQ29 ltac:(fun x Hx => apply (CLLg _ _ _ (a_iq a) (32) x (LIVBL (a_iq a, 32) ltac:(unfold BL; cbn [In]; repeat (first [left; reflexivity | right])))); rewrite Liq29 in Hx; clear - Hx Liq29; lia)
ltac:(fun x Hx => rewrite Liq29 in Hx; apply OQF; [intro Hin; pose proof (BOUT (sbd_interp_qlpc s, a_iq a, 32) x ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; repeat (first [left; reflexivity | right])) ltac:(unfold blk_addr, blk_size; cbn [fst snd]; clear - Hx Liq29; lia)) as H1; clear - H1 Hin FO1 FO2 FSQ; lia
| clear - Hx Liq29 AIQ1; lia| clear - Hx Liq29 AIQ2; lia]).
tr1 PRES31 WM31 PG29 ltac:(fun x Hx => apply (CLLg _ _ _ (a_pg a) (16) x (LIVBL (a_pg a, 16) ltac:(unfold BL; cbn [In]; repeat (first [left; reflexivity | right])))); rewrite Lpg29 in Hx; clear - Hx Lpg29; lia)
ltac:(fun x Hx => rewrite Lpg29 in Hx; apply OQF; [intro Hin; pose proof (BOUT (sbd_pi_gain s, a_pg a, 16) x ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; repeat (first [left; reflexivity | right])) ltac:(unfold blk_addr, blk_size; cbn [fst snd]; clear - Hx Lpg29; lia)) as H1; clear - H1 Hin FO1 FO2 FSQ; lia
| clear - Hx Lpg29 APG1; lia| clear - Hx Lpg29 APG2; lia]).
tr1 PRES31 WM31 ER29 ltac:(fun x Hx => apply (CLLg _ _ _ (a_er a) (16) x (LIVBL (a_er a, 16) ltac:(unfold BL; cbn [In]; repeat (first [left; reflexivity | right])))); rewrite Ler29 in Hx; clear - Hx Ler29; lia)
ltac:(fun x Hx => rewrite Ler29 in Hx; apply OQF; [intro Hin; pose proof (BOUT (sbd_exc_rms s, a_er a, 16) x ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; repeat (first [left; reflexivity | right])) ltac:(unfold blk_addr, blk_size; cbn [fst snd]; clear - Hx Ler29; lia)) as H1; clear - H1 Hin FO1 FO2 FSQ; lia
| clear - Hx Ler29 AER1; lia| clear - Hx Ler29 AER2; lia]).
tr1 PRES31 WM31 MSP29 ltac:(fun x Hx => apply (CLLg _ _ _ (a_msp a) (64) x (LIVBL (a_msp a, 64) ltac:(unfold BL; cbn [In]; repeat (first [left; reflexivity | right])))); rewrite Lmsp29 in Hx; clear - Hx Lmsp29; lia)
ltac:(fun x Hx => rewrite Lmsp29 in Hx; apply OQF; [intro Hin; pose proof (BOUT (sbd_mem_sp s, a_msp a, 64) x ltac:(unfold LALL; apply in_app_iff; left; cbn [sb_blocks tl In]; repeat (first [left; reflexivity | right])) ltac:(unfold blk_addr, blk_size; cbn [fst snd]; clear - Hx Lmsp29; lia)) as H1; clear - H1 Hin FO1 FO2 FSQ; lia
| clear - Hx Lmsp29 AMS1; lia| clear - Hx Lmsp29 AMS2; lia]).
tr1 PRES31 WM31 HD ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia)
ltac:(fun x Hx => apply OQF; [clear - Hx SFH FO1 FO2 FSQ; unfold hid in *; lia| clear - Hx AP10; lia| clear - Hx AP20; lia]).
tr1 PRES31 WM31 FST ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia)
ltac:(fun x Hx => apply OQF; [clear - Hx SFH FO1 FO2 FSQ; unfold hid in *; lia| clear - Hx AP10; lia| clear - Hx AP20; lia]).
tr1 PRES31 WM31 PT ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia)
ltac:(fun x Hx => apply OQF; [clear - Hx SFH FO1 FO2 FSQ; unfold hid in *; lia| clear - Hx AP10; lia| clear - Hx AP20; lia]).
tr1 PRES31 WM31 SEED ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia)
ltac:(fun x Hx => apply OQF; [clear - Hx SFH FO1 FO2 FSQ; unfold hid in *; lia| clear - Hx AP10; lia| clear - Hx AP20; lia]).
tr1 PRES31 WM31 CFG ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia)
ltac:(fun x Hx => apply OQF; [clear - Hx SFH FO1 FO2 FSQ; unfold hid in *; lia| clear - Hx AP10; lia| clear - Hx AP20; lia]).
tr1 PRES31 WM31 IDC ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia)
ltac:(fun x Hx => apply OQF; [clear - Hx SFH FO1 FO2 FSQ; unfold hid in *; lia| clear - Hx AP10; lia| clear - Hx AP20; lia]).
tr1 PRES31 WM31 PAD ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia)
ltac:(fun x Hx => apply OQF; [clear - Hx SFH FO1 FO2 FSQ; unfold hid in *; lia| clear - Hx AP10; lia| clear - Hx AP20; lia]).
tr1 PRES31 WM31 LE30 ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia)
ltac:(fun x Hx => apply OQF; [clear - Hx SFH FO1 FO2 FSQ; unfold hid in *; lia| clear - Hx AP10; lia| clear - Hx AP20; lia]).
assert (AGL31 : agree_blocks asegs m30 m31 LBL).
{ apply (agree_blocks_of_pres_fp RT Σ8 _ _ _ m30 m31 LBL PRES31 WM31 LIVEL). intros bk x Hb Hx.
pose proof (BOUT bk x ltac:(unfold LALL; apply in_app_iff; right; exact Hb) Hx) as H1.
apply OQF.
- clear - H1 FO1 FO2 FSQ. lia.
- intros Hin. pose proof (APL (sbd_g0_mem s, a_g0 a, 256) x ltac:(cbn [sb_blocks tl In]; left; reflexivity) ltac:(unfold blk_addr, blk_size; cbn [fst snd]; exact Hin)) as H2.
rewrite outside_blocks_ivs in H2. exact (H2 bk Hb Hx).
- intros Hin. pose proof (APL (sbd_g1_mem s, a_g1 a, 256) x ltac:(cbn [sb_blocks tl In]; right; left; reflexivity) ltac:(unfold blk_addr, blk_size; cbn [fst snd]; exact Hin)) as H2.
rewrite outside_blocks_ivs in H2. exact (H2 bk Hb Hx). }
pk_blocks AGL31. clear AGL31.
assert (OIMG31 : forall y, 65536 <= y < 6627328 -> outside [(OUT, OUT + 4 * (2 * fsz)); (a_g0 a, a_g0 a + 256); (a_g1 a, a_g1 a + 256)] y).
{ intros y Hy. apply OQF; [clear - Hy FO1 FPIMG; lia| |].
- intros Hin. pose proof (BOUT _ y G0IN ltac:(unfold blk_addr, blk_size; cbn [fst snd]; exact Hin)) as H1. clear - H1 Hy. lia.
- intros Hin. pose proof (BOUT _ y G1IN ltac:(unfold blk_addr, blk_size; cbn [fst snd]; exact Hin)) as H1. clear - H1 Hy. lia. }
pk_io_fp PRES31 ERR_rep OUT_rep IO_FP IO_img ltac:(fun y Hy => apply OIMG31; exact Hy).
assert (SSP31 : io_ssp m31).
{ apply (sbd_io_ssp_agree m30 m31 SSP30 (AF_DRV Σ9 m31 ART31)). intros a0 Ha. apply PRES31; [right; left; exact (sbd_ssp_static _ Ha)|].
unfold X00a.SSP_GUARD in Ha. apply OIMG31. clear - Ha. lia. }
assert (PF31 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m31).
{ apply (pres_fp_trans _ _ _ _ m m30 m31 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ8) (rt_frames RT Σ8) (usp + -1104) _ m30 m31 PRES31).
- intros e He. rewrite EL8. exact He.
- intros e He. rewrite EF8. right. exact He.
- clear; lia.
- intros x Hx Ho. cbn [outside] in Ho. destruct Ho as (_ & HO & _ & Ho). apply sb_outside_app_inv in Ho. destruct Ho as [Hb _].
rewrite ELBD in Hb. pose proof (outside_blocks_app_l _ _ x Hb) as Hb1. rewrite outside_blocks_ivs in Hb1.
pose proof (Hb1 (sbd_g0_mem s, a_g0 a, 256) ltac:(cbn [sb_blocks In]; do 1 right; left; reflexivity)) as N1.
pose proof (Hb1 (sbd_g1_mem s, a_g1 a, 256) ltac:(cbn [sb_blocks In]; do 2 right; left; reflexivity)) as N2.
unfold blk_addr, blk_size in N1, N2. cbn [fst snd] in N1, N2.
apply OQF; [clear - HO FSQ; lia| exact N1| exact N2]. }
clear PF. rename PF31 into PF.
clear ART30 MI30 ST30 SSP30 ACO30 PRES31.
assert (EL98 : rt_live RT Σ9 = rt_live RT Σ8) by exact EL9. assert (EF98 : rt_frames RT Σ9 = rt_frames RT Σ8) by exact EF9.
rewrite <- EL98 in LIVEA, LIVEL, LIVED, LIVBL, INLX, INPDX, ING0, ING1. rewrite <- EF98 in INF, INFHX. rewrite <- ES9 in LOWX.

destruct (af_acc_live RT AF Σ9 m31 S 160 ART31 INLX) as (_ & ACS31).
assert (OBS31 : aobj asegs m31 S 160) by (split; [clear - SPOS; lia|]; split; [clear - BS1 LO608 SPT; unfold APP_TOP; lia| exact ACS31]).
assert (INQ9 : In (usp + -864, 32) (rt_pois RT Σ9)) by (rewrite EP9, EP8; cbn [sb_pois x_usp X app]; do 2 right; left; reflexivity).
assert (OBQ31 : aobj asegs m31 (usp + -864) 32)
by (split; [clear - LOV LOS; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia|]; split; [clear - SPT; unfold APP_TOP, USTACK_TOP in *; lia| exact (af_acc_pois RT AF Σ9 m31 _ _ ART31 INQ9)]).
assert (INOQ9 : In (a_oq a, 32) (rt_live RT Σ9)) by (apply LIVBL; unfold BL; cbn [In]; do 4 right; left; reflexivity).
destruct (af_acc_live RT AF Σ9 m31 _ _ ART31 INOQ9) as (_ & ACOQ31).
assert (OBOQ31 : aobj asegs m31 (a_oq a) 32) by (split; [clear - OQP; lia|]; split; [clear - OQLO LO608 SPT; unfold APP_TOP; lia| exact ACOQ31]).
cps_seg (sbd_t2 usp lo S OUT A f sf (sbmode_struct (sbd_mode sI)) (sbd_frame_size sI) (usp + -864) (a_oq a) v29 sI a (Z_to_bv 64 (sbd_first sI)) lq29 voq29 ja30
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
SL29 HD FST PT ILPC eq_refl OBS31 S8 SPOS BS1 SOFF eq_refl LQ29 Llq29 OBQ31 OQ29 Loq29 OBOQ31 OQ8 OQP OQLO
ltac:(clear - OQSH; unfold SH_LO, SH_HI; lia) OQS STK30 ST31 ltac:(clear - LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia)
LOS ltac:(clear - SPH; lia) SPA MI31 RS31).
clear OBS31 ACS31 OBQ31 OBOQ31 ACOQ31.
destruct POST as (m32 & xa232 & xa332 & xa432 & xa532 & F32 & voq2 & -> & MU32 & WM32 & MI32 & ST32 & FST32 & OQW2 & Lvoq2).
clear ST31 FST OQ29 Loq29.

pose proof (SBAP 1%nat 4%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AG04. pose proof (SBAP 2%nat 4%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AG14.
pose proof (SBAP 3%nat 4%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AEX4. pose proof (SBAP 5%nat 4%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AIQ4.
pose proof (SBAP 6%nat 4%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as APG4. pose proof (SBAP 7%nat 4%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AER4.
pose proof (SBAP 8%nat 4%nat ltac:(lia) ltac:(lia) ltac:(discriminate)) as AMS4.
cbn [nth BL fst snd] in AG04, AG14, AEX4, AIQ4, APG4, AER4, AMS4.
assert (ART32 : X0ec.ART RT Σ9 m32).
{ apply (af_frame RT AF Σ9 m31 m32 lo ART31 LOWX); [| exact WM32]. intros a0 Ha. apply MU32. cbn [outside].
split; [| split; [| exact I]]; intros Hin; apply Ha.
- right; right; left. exists S, 160. split; [exact INLX| clear - Hin; lia].
- right; right; left. exists (a_oq a), 32. split; [exact INOQ9| clear - Hin; lia]. }
assert (PF32 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m32).
{ apply (pres_fp_trans _ _ _ _ m m31 m32 PF). apply (pres_fp_of_munch _ _ _ _ _ m31 m32 MU32). intros x Hx Ho. cbn [outside] in Ho |- *.
destruct Ho as (_ & _ & _ & Ho). apply sb_outside_app_inv in Ho. destruct Ho as [Hb _]. rewrite outside_blocks_ivs in Hb.
pose proof (Hb (sbd_blk s, S, SBSTATE_SIZEOF) ltac:(rewrite ELBD; apply in_app_iff; left; cbn [sb_blocks In]; left; reflexivity)) as N0.
pose proof (Hb (sbd_old_qlsp s, a_oq a, 32) ltac:(rewrite ELBD; apply in_app_iff; left; cbn [sb_blocks In]; do 4 right; left; reflexivity)) as N4.
unfold blk_addr, blk_size, SBSTATE_SIZEOF in N0, N4. cbn [fst snd] in N0, N4.
split; [clear - N0; lia| split; [exact N4| exact I]]. }
clear PF. rename PF32 into PF.
assert (AGL32 : agree_blocks asegs m31 m32 LBL).
{ apply (agree_blocks_of_munch asegs _ m31 m32 LBL MU32 WM32). intros bk x Hb Hx.
pose proof (BOUT bk x ltac:(unfold LALL; apply in_app_iff; right; exact Hb) Hx) as H1. cbn [outside].
split; [clear - H1; lia| split; [| exact I]]. intros Hin.
pose proof (APL (sbd_old_qlsp s, a_oq a, 32) x ltac:(cbn [sb_blocks tl In]; do 3 right; left; reflexivity) ltac:(unfold blk_addr, blk_size; cbn [fst snd]; exact Hin)) as H2.
rewrite outside_blocks_ivs in H2. exact (H2 bk Hb Hx). }
pk_blocks AGL32. clear AGL32.
assert (KEEP : forall P, fp_local IO_FP P -> P m31 -> P m32).
{ intros P L Pm. apply (fp_local_munch IO_FP P _ m31 m32 L IO_img MU32); [| exact Pm]. intros x Hx. unfold SEGTOP_A in Hx. cbn [outside].
split; [clear - Hx SIMG; lia| split; [clear - Hx BOQ0 BOQ1; lia| exact I]]. }
pk_io ERR_rep OUT_rep KEEP. clear KEEP.
assert (SSP32 : io_ssp m32).
{ apply (sbd_io_ssp_agree m31 m32 SSP31 (AF_DRV Σ9 m32 ART32)). intros a0 Ha. apply MU32. unfold X00a.SSP_GUARD in Ha. cbn [outside].
clear - Ha BOQ0 BOQ1 SIMG. split; [lia| split; [lia| exact I]]. }
trm MU32 WM32 SV ltac:(clear - OQLO BS1 LOV LO608; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 SL29 ltac:(clear - OQLO BS1 LOV LO608; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 STK30 ltac:(clear - OQLO BS1 LOV LO608; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 LPI29 ltac:(rewrite ?Llpi29; clear - OQLO BS1 LOV LO608; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 LER29 ltac:(rewrite ?Ller29; clear - OQLO BS1 LOV LO608; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 LQ29 ltac:(rewrite ?Llq29; clear - OQLO BS1 LOV LO608; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 LIQ29 ltac:(rewrite ?Lliq29; clear - OQLO BS1 LOV LO608; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 LAK29 ltac:(rewrite ?Llak29; clear - OQLO BS1 LOV LO608; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 RZ1a ltac:(clear - OQLO BS1 LOV LO608; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 RZ1b ltac:(clear - OQLO BS1 LOV LO608; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 RZ2a ltac:(clear - OQLO BS1 LOV LO608; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 RZ2b ltac:(clear - OQLO BS1 LOV LO608; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 RZ3a ltac:(clear - OQLO BS1 LOV LO608; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 RZ3b ltac:(clear - OQLO BS1 LOV LO608; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 RZ4a ltac:(clear - OQLO BS1 LOV LO608; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 RZ4b ltac:(clear - OQLO BS1 LOV LO608; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 RZ5a ltac:(clear - OQLO BS1 LOV LO608; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 RZ5b ltac:(clear - OQLO BS1 LOV LO608; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
trm MU32 WM32 FRB ltac:(clear - SFA BOQ0 BOQ1 BF; unfold hid in *; lia).
trm MU32 WM32 FRS ltac:(clear - SFS SHF OQSH SHF1 SHF2; unfold hid in *; subst sf; lia).
trm MU32 WM32 STB ltac:(clear - SFH FOQ FS1 FS2; unfold hid in *; lia).
assert (LOCq2 : Z.of_nat (length owq') = 2 * sbd_frame_size s) by exact LOCq'.
trm MU32 WM32 OCq' ltac:(clear - SFH FOQ FO1 FO2 LOCq' LOCq2 FSV FSQ; unfold hid in *; lia).
trm MU32 WM32 OCr ltac:(clear - SFH FOQ FO1 FO2 LOCr LOCr' FSV FSQ; unfold hid in *; lia).
trm MU32 WM32 BOBJ29 ltac:(clear - SFH FOQ FA1 FA2; unfold hid in *; lia).
trm MU32 WM32 BDAT29 ltac:(clear - SPD POQ PD1 PD2 Lbs29; unfold hid in *; lia).
trm MU32 WM32 G0Q ltac:(rewrite ?LG0Q; clear - AP10 AG04; lia).
trm MU32 WM32 G1Q ltac:(rewrite ?LG1Q; clear - AP20 AG14; lia).
assert (Lexc29' : Z.of_nat (length vexc29) = sbd_subframeSize s) by exact Lexc29.
trm MU32 WM32 EXC29 ltac:(clear - AP30 AEX4 Lexc29'; lia).
trm MU32 WM32 IQ29 ltac:(rewrite ?Liq29; clear - AP50 AIQ4; lia).
trm MU32 WM32 PG29 ltac:(rewrite ?Lpg29; clear - AP60 APG4; lia).
trm MU32 WM32 ER29 ltac:(rewrite ?Ler29; clear - AP70 AER4; lia).
trm MU32 WM32 MSP29 ltac:(rewrite ?Lmsp29; clear - AP80 AMS4; lia).
trm MU32 WM32 HD ltac:(clear - OQS; lia).
trm MU32 WM32 PT ltac:(clear - OQS; lia).
trm MU32 WM32 SEED ltac:(clear - OQS; lia).
trm MU32 WM32 CFG ltac:(clear - OQS; lia).
trm MU32 WM32 IDC ltac:(clear - OQS; lia).
trm MU32 WM32 PAD ltac:(clear - OQS; lia).
trm MU32 WM32 LE30 ltac:(clear - OQS; lia).
clear ART31 MI31 SSP31 MU32.

assert (TOP8 : sb_top_stale usp (sbd_mode sI) sm mod 8 = 0)
by (unfold sb_top_stale, sb_exc_hull; destruct (sbd_mode sI); destruct (sm_double_codebook sm =? 0); clear - SPA; Z.div_mod_to_equations; lia).
assert (TOPR : lo <= sb_top_stale usp (sbd_mode sI) sm <= usp + -1088)
by (unfold sb_top_stale, sb_exc_hull; destruct (sbd_mode sI); destruct (sm_double_codebook sm =? 0); clear - LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia).
assert (POAU : forall e, In e (rt_pois RT Σ9) ->
(sb_top_stale usp (sbd_mode sI) sm <= pz_lo e /\ pz_hi e <= usp + -608) \/ usp + -608 <= pz_lo e).
{ intros e He. rewrite EP9, EP8 in He. cbn [sb_pois x_usp X app] in He.
destruct He as [<- |[<- |[<- |[<- |[<- | He]]]]];
[left; unfold pz_lo, pz_hi, alloca_rr; cbn [fst snd]; split; [clear - TOPR; lia| clear - SPA; Z.div_mod_to_equations; lia] ..|].
right. pose proof (POA e He) as H1. clear - H1. lia. }
assert (COKU : call_ok RT Σ9 m32 (Z_to_bv 64 (usp + -1088)) lo).
{ unfold call_ok. rewrite EU1088. split; [exact ST32|]. split; [exact LOWX|]. split; [clear - LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia|].
split; [clear - SPT; unfold USTACK_TOP in *; lia| clear - SPA; Z.div_mod_to_equations; lia]. }
cps_rt (AUN_lo Σ9 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m32 (sb_top_stale usp (sbd_mode sI) sm) (usp + -608) lo FDO MST V416 eq_refl
ltac:(clear - TOPR LOS; lia) TOP8 ltac:(clear - SPA; Z.div_mod_to_equations; lia) ltac:(clear - TOPR; lia)
ltac:(clear - SPT; unfold USTACK_TOP in *; lia) POAU ART32 MI32 COKU).
intros cu (Σ10 & Hcu & EP10 & EL10 & EF10 & ES10 & EC10).
destruct (ASTA_unpack RT Σ10 (PMfd F0 fs0) _ cu Hcu) as (msu & POU & Hcu'); clear Hcu; cbv beta in POU.
destruct POU as (m33 & v33 & RS33 & (ART33 & MI33 & WM33 & ST33) & PRES33 & ACK33).
cps_ret RS33.
rewrite EU1088 in PRES33, ST33.
clear POAU COKU.
assert (EP10' : rt_pois RT Σ10 = rt_pois RT Σ).
{ rewrite EP10, EP9, EP8. cbn [sb_pois x_usp X app]. unfold pois_drop. cbn [List.filter].
rewrite !(proj2 (Z.leb_gt _ _)) by (unfold pz_lo; cbn [fst]; clear; lia).
fold (pois_drop (usp + -608) (rt_pois RT Σ)). apply pois_drop_above. apply (pois_above_le _ usp); [exact POA| clear; lia]. }
clear STK30.
pose proof (pres_fp_of_pres _ _ _ [] _ _ PRES33) as PF33.
tr1 PF33 WM33 SV ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 SL29 ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 RZ1a ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 RZ1b ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 RZ2a ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 RZ2b ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 RZ3a ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 RZ3b ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 RZ4a ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 RZ4b ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 RZ5a ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 RZ5b ltac:(fun x Hx => apply CLSg; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 LPI29 ltac:(fun x Hx => apply CLSg; rewrite ?Llpi29 in Hx; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 LER29 ltac:(fun x Hx => apply CLSg; rewrite ?Ller29 in Hx; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 LQ29 ltac:(fun x Hx => apply CLSg; rewrite ?Llq29 in Hx; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 LIQ29 ltac:(fun x Hx => apply CLSg; rewrite ?Lliq29 in Hx; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 LAK29 ltac:(fun x Hx => apply CLSg; rewrite ?Llak29 in Hx; clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 FRB ltac:(fun x Hx => apply (CLF0g _ _ _ x INF); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 FRS ltac:(fun x Hx => apply (CLSFg _ _ _ x INF); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 STB ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FS1 FS2; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 OCq' ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FO1 FO2 LOCq' LOCq2 FSV FSQ; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 OCr ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FO1 FO2 LOCr LOCr' FSV FSQ; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 BOBJ29 ltac:(fun x Hx => apply (CLFg _ _ _ x INFHX); clear - Hx FA1 FA2; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 BDAT29 ltac:(fun x Hx => apply (CLLg _ _ _ PD ND x INPDX); clear - Hx PD1 PD2 Lbs29; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 G0Q ltac:(fun x Hx => apply (CLLg _ _ _ (a_g0 a) (256) x (LIVBL (a_g0 a, 256) ltac:(unfold BL; cbn [In]; repeat (first [left; reflexivity | right])))); clear - Hx LG0Q; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 G1Q ltac:(fun x Hx => apply (CLLg _ _ _ (a_g1 a) (256) x (LIVBL (a_g1 a, 256) ltac:(unfold BL; cbn [In]; repeat (first [left; reflexivity | right])))); clear - Hx LG1Q; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 EXC29 ltac:(fun x Hx => apply (CLLg _ _ _ (a_exc a) (4 * sbd_subframeSize s) x (LIVBL (a_exc a, 4 * sbd_subframeSize s) ltac:(unfold BL; cbn [In]; repeat (first [left; reflexivity | right])))); clear - Hx Lexc29'; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 OQW2 ltac:(fun x Hx => apply (CLLg _ _ _ (a_oq a) (32) x (LIVBL (a_oq a, 32) ltac:(unfold BL; cbn [In]; repeat (first [left; reflexivity | right])))); clear - Hx Lvoq2; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 IQ29 ltac:(fun x Hx => apply (CLLg _ _ _ (a_iq a) (32) x (LIVBL (a_iq a, 32) ltac:(unfold BL; cbn [In]; repeat (first [left; reflexivity | right])))); clear - Hx Liq29; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 PG29 ltac:(fun x Hx => apply (CLLg _ _ _ (a_pg a) (16) x (LIVBL (a_pg a, 16) ltac:(unfold BL; cbn [In]; repeat (first [left; reflexivity | right])))); clear - Hx Lpg29; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 ER29 ltac:(fun x Hx => apply (CLLg _ _ _ (a_er a) (16) x (LIVBL (a_er a, 16) ltac:(unfold BL; cbn [In]; repeat (first [left; reflexivity | right])))); clear - Hx Ler29; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 MSP29 ltac:(fun x Hx => apply (CLLg _ _ _ (a_msp a) (64) x (LIVBL (a_msp a, 64) ltac:(unfold BL; cbn [In]; repeat (first [left; reflexivity | right])))); clear - Hx Lmsp29; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 HD ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 FST32 ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 PT ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 SEED ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 CFG ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 IDC ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 PAD ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => exact I).
tr1 PF33 WM33 LE30 ltac:(fun x Hx => apply (CLLg _ _ _ S 160 x INLX); clear - Hx; lia) ltac:(fun x Hx => exact I).
assert (AGL33 : agree_blocks asegs m32 m33 LBL) by (exact (agree_blocks_of_pres RT Σ9 _ _ m32 m33 LBL PRES33 WM33 LIVEL)).
pk_blocks AGL33. clear AGL33.
assert (KEEP : forall P, fp_local IO_FP P -> P m32 -> P m33)
by (intros P L Pm; exact (fp_local_pres IO_FP P (rt_live RT Σ9) _ _ m32 m33 L IO_img PRES33 Pm)).
pk_io ERR_rep OUT_rep KEEP. clear KEEP.
assert (PF33' : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((A, A + 48) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP) m m33).
{ apply (pres_fp_trans _ _ _ _ m m32 m33 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ9) (rt_frames RT Σ9) (usp + -1088) [] m32 m33 PF33).
- intros e He. rewrite EL9, EL8. exact He.
- intros e He. rewrite EF9, EF8. right. exact He.
- clear; lia.
- intros x _ _. exact I. }
clear PF. rename PF33' into PF.
clear ART32 MI32 ST32 SSP32 PF33 PRES33 ACK33.

assert (WJ : forall a0 n1 n2, 0 <= n1 -> 0 <= n2 -> wr_at asegs m33 a0 n1 -> wr_at asegs m33 (a0 + n1) n2 -> wr_at asegs m33 a0 (n1 + n2))
by (intros a0 n1 n2 H1 H2 W1 W2; exact (proj2 (wr_at_app asegs m33 a0 n1 n2 H1 H2) (conj W1 W2))).
assert (WAT : forall a0 n cs, rw_cells asegs m33 a0 cs -> Z.of_nat (cells_size cs) = n -> wr_at asegs m33 a0 n)
by (intros a0 n cs H E; rewrite <- E; exact (proj2 H)).
pose proof (WAT _ 32 _ RZ5a eq_refl) as WP0.
pose proof (WAT _ 32 _ LAK29 ltac:(rewrite cells_size_f32, Llak29; reflexivity)) as WP1.
pose proof (WAT _ 32 _ RZ5b eq_refl) as WP2.
pose proof (WAT _ 32 _ RZ4a eq_refl) as WP3.
pose proof (WAT _ 32 _ LIQ29 ltac:(rewrite cells_size_f32, Lliq29; reflexivity)) as WP4.
pose proof (WAT _ 32 _ RZ4b eq_refl) as WP5.
pose proof (WAT _ 32 _ RZ3a eq_refl) as WP6.
pose proof (WAT _ 32 _ LQ29 ltac:(rewrite cells_size_f32, Llq29; reflexivity)) as WP7.
pose proof (WAT _ 32 _ RZ3b eq_refl) as WP8.
pose proof (WAT _ 32 _ RZ2a eq_refl) as WP9.
pose proof (WAT _ 16 _ LER29 ltac:(rewrite cells_size_f32, Ller29; reflexivity)) as WP10.
pose proof (WAT _ 48 _ RZ2b eq_refl) as WP11.
pose proof (WAT _ 32 _ RZ1a eq_refl) as WP12.
pose proof (WAT _ 16 _ LPI29 ltac:(rewrite cells_size_f32, Llpi29; reflexivity)) as WP13.
pose proof (WAT _ 48 _ RZ1b eq_refl) as WP14.
assert (WA1 : wr_at asegs m33 (usp + -1088) 64) by (exact (WJ _ 32 32 ltac:(lia) ltac:(lia) WP0 ltac:(replace (usp + -1088 + 32) with (usp + -1056) by lia; exact WP1))).
assert (WA2 : wr_at asegs m33 (usp + -1088) 96) by (exact (WJ _ 64 32 ltac:(lia) ltac:(lia) WA1 ltac:(replace (usp + -1088 + 64) with (usp + -1024) by lia; exact WP2))).
assert (WA3 : wr_at asegs m33 (usp + -1088) 128) by (exact (WJ _ 96 32 ltac:(lia) ltac:(lia) WA2 ltac:(replace (usp + -1088 + 96) with (usp + -992) by lia; exact WP3))).
assert (WA4 : wr_at asegs m33 (usp + -1088) 160) by (exact (WJ _ 128 32 ltac:(lia) ltac:(lia) WA3 ltac:(replace (usp + -1088 + 128) with (usp + -960) by lia; exact WP4))).
assert (WA5 : wr_at asegs m33 (usp + -1088) 192) by (exact (WJ _ 160 32 ltac:(lia) ltac:(lia) WA4 ltac:(replace (usp + -1088 + 160) with (usp + -928) by lia; exact WP5))).
assert (WA6 : wr_at asegs m33 (usp + -1088) 224) by (exact (WJ _ 192 32 ltac:(lia) ltac:(lia) WA5 ltac:(replace (usp + -1088 + 192) with (usp + -896) by lia; exact WP6))).
assert (WA7 : wr_at asegs m33 (usp + -1088) 256) by (exact (WJ _ 224 32 ltac:(lia) ltac:(lia) WA6 ltac:(replace (usp + -1088 + 224) with (usp + -864) by lia; exact WP7))).
assert (WA8 : wr_at asegs m33 (usp + -1088) 288) by (exact (WJ _ 256 32 ltac:(lia) ltac:(lia) WA7 ltac:(replace (usp + -1088 + 256) with (usp + -832) by lia; exact WP8))).
assert (WA9 : wr_at asegs m33 (usp + -1088) 320) by (exact (WJ _ 288 32 ltac:(lia) ltac:(lia) WA8 ltac:(replace (usp + -1088 + 288) with (usp + -800) by lia; exact WP9))).
assert (WA10 : wr_at asegs m33 (usp + -1088) 336) by (exact (WJ _ 320 16 ltac:(lia) ltac:(lia) WA9 ltac:(replace (usp + -1088 + 320) with (usp + -768) by lia; exact WP10))).
assert (WA11 : wr_at asegs m33 (usp + -1088) 384) by (exact (WJ _ 336 48 ltac:(lia) ltac:(lia) WA10 ltac:(replace (usp + -1088 + 336) with (usp + -752) by lia; exact WP11))).
assert (WA12 : wr_at asegs m33 (usp + -1088) 416) by (exact (WJ _ 384 32 ltac:(lia) ltac:(lia) WA11 ltac:(replace (usp + -1088 + 384) with (usp + -704) by lia; exact WP12))).
assert (WA13 : wr_at asegs m33 (usp + -1088) 432) by (exact (WJ _ 416 16 ltac:(lia) ltac:(lia) WA12 ltac:(replace (usp + -1088 + 416) with (usp + -672) by lia; exact WP13))).
assert (WA14 : wr_at asegs m33 (usp + -1088) 480) by (exact (WJ _ 432 48 ltac:(lia) ltac:(lia) WA13 ltac:(replace (usp + -1088 + 432) with (usp + -656) by lia; exact WP14))).
clear WJ WAT WP0 WP1 WP2 WP3 WP4 WP5 WP6 WP7 WP8 WP9 WP10 WP11 WP12 WP13 WP14 WA1 WA2 WA3 WA4 WA5 WA6 WA7 WA8 WA9 WA10 WA11 WA12 WA13.
clear RZ5a LAK29 RZ5b RZ4a LIQ29 RZ4b RZ3a LQ29 RZ3b RZ2a LER29 RZ2b RZ1a LPI29 RZ1b.
destruct (wr_at_rw_CB m33 (usp + -1088) 480 WA14 ltac:(lia)) as (jh480 & HH480). change (Z.to_nat 480) with 480%nat in HH480. clear WA14.
cps_seg (sbd_t3 usp lo f jh480 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
HH480 ST33 ltac:(clear - LOV; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia) ltac:(clear - SPH; lia) MI33).
destruct POST as (-> & ST34).
clear ST33 HH480.

assert (EFq : rt_frames RT Σ10 = (f, 0%nat) :: rt_frames RT Σ) by (rewrite EF10, EF9, EF8; reflexivity).
assert (ELq : rt_live RT Σ10 = rt_live RT Σ) by (rewrite EL10, EL9, EL8; reflexivity).
assert (ESq : rt_sp0 RT Σ10 = rt_sp0 RT Σ) by (rewrite ES10, ES9, ES8; reflexivity).
set (sF := set_sbd_first sI 0).
set (dF := (speex_decoder_ctl (speex_decoder_ctl low3 CtlGetPiGain).2 CtlGetExc).2).
assert (INVF : sb_inv sF).
{ destruct INV1 as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12). unfold sb_inv, sF. cbn [set_sbd_first sbd_mode sbd_frame_size sbd_full_frame_size
sbd_subframeSize sbd_nbSubframes sbd_lpcSize sbd_first sbd_sampling_rate sbd_lpc_enh_enabled sbd_encode_submode sbd_submodeID sbd_innov_save].
refine (conj I1 (conj I2 (conj I3 (conj I4 (conj I5 (conj I6 (conj (or_introl eq_refl) (conj I8 (conj I9 (conj I10 (conj I11 I12))))))))))). }
set (jF := SBJ le30 seed29 pad129 pad229 g0q g1q vexc29 voq2 viq29 vmsp29 vpg29 ver29).
assert (JOKF : sb_junk_ok sF jF) by (exact (conj Lp129 (conj Lp229 (conj LG0Q (conj LG1Q (conj Lexc29 (conj Lvoq2 (conj Liq29 (conj Lmsp29 (conj Lpg29 Ler29)))))))))).
assert (XF : rw_cells asegs m33 S (SBCELLS sF a OUT jF))
by (apply sb_pieces_iff; exact (conj HD (conj FST32 (conj PT (conj LE30 (conj SEED (conj CFG (conj IDC PAD)))))))).
assert (BUFSF : sb_bufs asegs m33 a jF) by (exact (conj G0Q (conj G1Q (conj EXC29 (conj OQW2 (conj IQ29 (conj MSP29 (conj PG29 ER29)))))))).
assert (REPX : DREP OUT STEREO m33 S (DecSB sF dF) LBD).
{ cbn [decst_rep]. exists a, jF, LBL. split; [exact ELBD1|]. split; [exact S8|]. split; [exact SPOS|]. split; [exact INVF|]. split; [exact JOKF|].
split; [exact XF|]. split; [exact BUFSF|]. exists OUT. exact RLOW. }
set (bF := sbsub_bits sm (sbsub_bits sm (sbsub_bits sm (sbsub_bits sm (lsp_bits LspUnquantHigh (sbw_bits b1)))))).
assert (BREPX : bits_rep asegs m33 A D bF).
{ split; [exists rj29; split; [exact Lrj29| unfold bits_cells; exact BOBJ29]|].
split; [exists bs29; split; [apply (proj2 (u8arr_rw_CB m33 D bs29)); exact BDAT29| exact Hbs29]| exact BSIDE29]. }
assert (PD2X : D + sb_buf_size bF <= PD + ND) by (unfold bF; rewrite BSZ29; exact PD2).
assert (OCF : rw_cells asegs m33 OUT (f32 (owq' ++ owr))).
{ apply (f32_join asegs m33 OUT _ _ OCq'). replace (OUT + 4 * Z.of_nat (length owq')) with (OUT + 4 * (2 * fsz)) by (rewrite LOCq'; reflexivity). exact OCr. }
assert (LOCF : length (owq' ++ owr) = 2000%nat) by (rewrite length_app, LOCr; clear - LOCq' FSQ; lia).
assert (WMX : wmono asegs m m33) by (eapply wmono_trans; [exact WM0|]; eapply wmono_trans; [exact WM8|]; eapply wmono_trans; [exact WM9|]; eapply wmono_trans; [exact WM11|]; eapply wmono_trans; [exact WM12|]; eapply wmono_trans; [exact WM13|]; eapply wmono_trans; [exact WM14|]; eapply wmono_trans; [exact WM15|]; eapply wmono_trans; [exact WM16|]; eapply wmono_trans; [exact WM17|]; eapply wmono_trans; [exact WM18|]; eapply wmono_trans; [exact WM19|]; eapply wmono_trans; [exact WM20|]; eapply wmono_trans; [exact WM21|]; eapply wmono_trans; [exact WM22|]; eapply wmono_trans; [exact WM23|]; eapply wmono_trans; [exact WM24|]; eapply wmono_trans; [exact WM25|]; eapply wmono_trans; [exact WM26|]; eapply wmono_trans; [exact WM27|]; eapply wmono_trans; [exact WM28|]; eapply wmono_trans; [exact WM29|]; eapply wmono_trans; [exact WM30|]; eapply wmono_trans; [exact WM31|]; eapply wmono_trans; [exact WM32|]; exact WM33).
assert (FRX : rw_cells asegs m33 (usp + -608) (sb_fr (fun i => nth i [(Z_to_bv 64 0); (v_8 v29); (Z_to_bv 64 7); (Z_to_bv 64 3); (Z_to_bv 64 (sha (S + 36))); (Z_to_bv 64 (S + 36)); (Z_to_bv 64 (usp + -608)); (Z_to_bv 64 f); (Z_to_bv 64 f); (Z_to_bv 64 (OUT + 4 * (sbd_frame_size sI) + 4)); (Z_to_bv 64 (OUT + 4 * (sbd_frame_size sI))); (Z_to_bv 64 (sha (usp + -1052))); (Z_to_bv 64 (usp + -1052)); (Z_to_bv 64 sf); (Z_to_bv 64 (usp + -768)); (v_120 v29); (Z_to_bv 64 ((sbmode_struct (sbd_mode sI)) + 32)); (Z_to_bv 64 (S + 112)); (Z_to_bv 64 (S + 96)); (Z_to_bv 64 (S + 104)); (Z_to_bv 64 (usp + -960)); (Z_to_bv 64 S); (Z_to_bv 64 OUT); (Z_to_bv 64 (S + 132)); (Z_to_bv 64 (usp + -672)); (Z_to_bv 64 (usp + -864)); (Z_to_bv 64 (S + 20)); (Z_to_bv 64 (sha (S + 20))); (Z_to_bv 64 (2^36 - 16)); (Z_to_bv 64 (S + 88)); (Z_to_bv 64 (S + 80)); (v_248 v29); (v_256 v29); (v_264 v29); (Z_to_bv 64 (S + 120)); (Z_to_bv 64 (S + 28)); (Z_to_bv 64 (sha (S + 28))); (v_296 v29); (Z_to_bv 64 A); (Z_to_bv 64 (usp + -1056)); (Z_to_bv 64 (S + 32)); (Z_to_bv 64 (sha (S + 152))); (Z_to_bv 64 (sha (S + 144))); (Z_to_bv 64 (S + 152)); (Z_to_bv 64 (S + 144)); (Z_to_bv 64 0); (Z_to_bv 64 (S + 72)); (Z_to_bv 64 (sha (S + 32))); (v_384 v29); (v_392 v29); (v_400 v29); (Z_to_bv 64 f); (v_416 v29); (v_424 v29); (v_432 v29); (v_440 v29)] (Z_to_bv 64 0)))).
{ rewrite <- sb_fr_of_list by reflexivity. exact SL29. }
assert (TOPX : sb_top_stale usp (sbd_mode sI) sm = 0 \/ (lo <= sb_top_stale usp (sbd_mode sI) sm /\ 0 < sb_top_stale usp (sbd_mode sI) sm <= usp + -192
/\ sb_top_stale usp (sbd_mode sI) sm mod 8 = 0)) by (right; clear - TOPR TOP8 LOS; lia).
cps_rt (sbd_exit_cps RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AUN_lo AUN_nop Σ Σ10 F0 fs0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m m33 lo S OUT STEREO A D f fh PD ND kh LBD
(fun i => nth i [(Z_to_bv 64 0); (v_8 v29); (Z_to_bv 64 7); (Z_to_bv 64 3); (Z_to_bv 64 (sha (S + 36))); (Z_to_bv 64 (S + 36)); (Z_to_bv 64 (usp + -608)); (Z_to_bv 64 f); (Z_to_bv 64 f); (Z_to_bv 64 (OUT + 4 * (sbd_frame_size sI) + 4)); (Z_to_bv 64 (OUT + 4 * (sbd_frame_size sI))); (Z_to_bv 64 (sha (usp + -1052))); (Z_to_bv 64 (usp + -1052)); (Z_to_bv 64 sf); (Z_to_bv 64 (usp + -768)); (v_120 v29); (Z_to_bv 64 ((sbmode_struct (sbd_mode sI)) + 32)); (Z_to_bv 64 (S + 112)); (Z_to_bv 64 (S + 96)); (Z_to_bv 64 (S + 104)); (Z_to_bv 64 (usp + -960)); (Z_to_bv 64 S); (Z_to_bv 64 OUT); (Z_to_bv 64 (S + 132)); (Z_to_bv 64 (usp + -672)); (Z_to_bv 64 (usp + -864)); (Z_to_bv 64 (S + 20)); (Z_to_bv 64 (sha (S + 20))); (Z_to_bv 64 (2^36 - 16)); (Z_to_bv 64 (S + 88)); (Z_to_bv 64 (S + 80)); (v_248 v29); (v_256 v29); (v_264 v29); (Z_to_bv 64 (S + 120)); (Z_to_bv 64 (S + 28)); (Z_to_bv 64 (sha (S + 28))); (v_296 v29); (Z_to_bv 64 A); (Z_to_bv 64 (usp + -1056)); (Z_to_bv 64 (S + 32)); (Z_to_bv 64 (sha (S + 152))); (Z_to_bv 64 (sha (S + 144))); (Z_to_bv 64 (S + 152)); (Z_to_bv 64 (S + 144)); (Z_to_bv 64 0); (Z_to_bv 64 (S + 72)); (Z_to_bv 64 (sha (S + 32))); (v_384 v29); (v_392 v29); (v_400 v29); (Z_to_bv 64 f); (v_416 v29); (v_424 v29); (v_432 v29); (v_440 v29)] (Z_to_bv 64 0))
(sb_top_stale usp (sbd_mode sI) sm) 0 (DecSB sF dF) bF (owq' ++ owr) stb j24 j36 (Z_to_bv 64 dtx)
EFq ELq ESq EP10' ART0 POA NAF LIVE INPD PD1 PD2X INFH FA1 FA2 ACA FO1 FO2 ACO FS1 FS2 ACST ART33 MI33 RS31 ST34 LOW
ltac:(clear - LOR DSP; unfold RT_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia) SPT SPA PF WMX FRX
eq_refl V416 TOPX SV FRB FRS REPX (fun _ => I) BREPX BOK29 OCF LOCF STB ERRX OUTK0).
intros c' (Σ' & Hc' & E1 & E2 & E3 & E4 & E5).
apply Hk. rewrite INS. change (Z.to_nat 4) with 4%nat. cbn [sbsubs_bits]. exists Σ'. split; [exact Hc'|].
pose proof (bkeep_sbsubs 4 sm (lsp_bits LspUnquantHigh (sbw_bits b1))) as BK1. pose proof (bkeep_lsp LspUnquantHigh (sbw_bits b1)) as BK2. pose proof (bkeep_sbw b1) as BK3.
pose proof (bkeep_trans _ _ _ BK3 (bkeep_trans _ _ _ BK2 BK1)) as (K1 & K2 & K3).
cbn [sbsubs_bits] in K1, K2, K3.
destruct (ctl_keeps_mode_nest low3 CtlGetPiGain) as (M1 & N1). destruct (ctl_keeps_mode_nest (speex_decoder_ctl low3 CtlGetPiGain).2 CtlGetExc) as (M2 & N2).
cbn [dec_depth dec_mode dec_nestedR dec_credit sF sI set_sbd_submodeID set_sbd_first sbd_mode].
split; [clear; lia|]. split; [unfold dF; rewrite ctl_keeps_depth, ctl_keeps_depth, DL3; reflexivity|]. split; [reflexivity|].
split; [split; [unfold dF; rewrite M2, M1; exact NM3| exact (N2 (N1 NEST3))]|].
split; [rewrite K2; exact OWN1|]. split; [rewrite K1; exact CHR1|]. split; [rewrite K3; exact BSZ1|].
split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [| exact E5].
rewrite E4, EC10, EC9, EC8, EC7, EC6, EC5. rewrite DL4 in EC4. rewrite DL3 in EC3. rewrite EC2, EC1 in EC3.
pose proof (dec_depth_pos low) as DP. clear - CBX DP EC3 EC4. lia.
Qed.
End SbDecodeWph.
