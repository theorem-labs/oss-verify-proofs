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
X0ay X0bf X07y X0b3 X0az X0b2 X0ar X07l X08b
X0b5 X0bg.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0r9 X0qz.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0yr X0wl X0wn X0wm X0ys X0x2 X0wp X0yt X0zq X11l X11k X0x1 X0w7 X11i X122 X0yq X11n X11o X11j X11m X11c X0yd X0z2 X11q X123.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X0j9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X09f OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X06d.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wp OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w7 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11i OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X122 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yd OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0z2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X123.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac simpl_sizes ::=
rewrite ?X06d.sb_cells_size, ?cells_size_sb_fhdr, ?cells_size_sb_fshadow, ?cells_size_sb_fr, ?cells_size_sb_saves, ?cells_size_sb_slots,
?cells_size_sbp_hdr, ?cells_size_sbp_ptrs, ?cells_size_sbp_cfg, ?app_length, ?cells_size_app, ?cells_size_f32, ?length_f32;
cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length, ?cells_size_f32, ?length_f32; cbn [length].

Section SbDecodeCPS.
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
Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis APO : alloca_poison_contract RT.
Hypothesis AUN_lo : allocas_unpoison_lo_contract RT.
Hypothesis AUN_nop : allocas_unpoison_nop_contract RT.
Hypothesis MEMS : memset_icontract RT e_asan_memset.
Hypothesis QMF16 : forall N, N = 320 \/ N = 640 -> qmf_synth_cps16 RT N.
Hypothesis LOST : sb_decode_lost_cps RT.
Hypothesis LOOP : sb_subframe_cps RT.

Theorem sb_decode_cps : forall k : nat,
(forall d, (dec_depth d <= k)%nat -> dec_appends d) ->
(forall d, (dec_depth d <= k)%nat -> dec_cps_at RT OUT_rep ERR_rep IO_FP A_speex_decode_native d) ->
(forall d, (dec_depth d <= k)%nat -> ctl2_cps_at RT d) ->
forall s low, (dec_depth low <= k)%nat -> dec_cps_at RT OUT_rep ERR_rep IO_FP A_sb_decode (DecSB s low).
Proof using AF ERR_loc OUT_loc IO_img IO_ssp AF_DRV AF_ERRV AF_LIB FPL SM0 APO AUN_lo AUN_nop MEMS QMF16 LOST LOOP.
intros k IHA IHD IHC s low DK Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
OUT STEREO S A D LBD b lo fh PD NDs kh ows stb q q' ret d' b' PRUN -> -> -> -> REP DEP ISV NEST NDUP LAL8 LIVE BREP BOK INPD PD1 PD2 PDB OC LOWS STB INFH FA FO FS
HAO HAS HOS FD2 ERR0 SSP0 FRM CRD POA ART0 MI0 FRM0 ST0 LOW LOR SPT SPA.
pose proof REP as REP0. cbn [decst_rep] in REP0. destruct REP0 as (a & j & LBL & ELBD & S8 & SPOS & INV & JOK & X & BUFS & OUTL & RLOW).
pose proof INV as (IMODE & IFS & IFFS & ISFS & INS & ILPC & IFST & _ & _ & IES & IID & IISV).
destruct (sb_decode_prun s low b q ret d' b' q' IES PRUN) as (retl & low2 & b1 & q1 & PRL & PNZ & PZ).
pose proof (ctl_keeps_depth low (CtlSetInnovationSave (0 + sbd_frame_size s))) as DL1.
set (low1 := snd (speex_decoder_ctl low (CtlSetInnovationSave (0 + sbd_frame_size s)))) in *.
destruct (IHA low1 ltac:(rewrite DL1; exact DK) b q _ q1 PRL) as (bsl & EBSL).

set (inval := match Z.eq_dec retl 0 with
| left _ => match submode_at (sbm_submodes (sbd_mode s)) (sbw_id b1) with None => negb (sbw_id b1 =? 0) | Some _ => false end
| right _ => false end).
exists (bsl ++ if inval then notify_bytes MSG_INVALID_MODE else []).
split.
{ subst inval. destruct (Z.eq_dec retl 0) as [E|NE].
- specialize (PZ E). unfold sb_outcome in PZ. cbv zeta in PZ.
destruct (submode_at (sbm_submodes (sbd_mode s)) (sbw_id b1)) as [sm|].
+ destruct PZ as (_ & _ & _ & ->). rewrite app_nil_r. exact EBSL.
+ destruct (sbw_id b1 =? 0); cbn [negb].
* destruct PZ as (_ & _ & _ & ->). rewrite app_nil_r. exact EBSL.
* destruct PZ as (_ & _ & _ & ->). unfold p_app. cbn [p_err]. rewrite EBSL, app_assoc. reflexivity.
- destruct (PNZ NE) as (_ & _ & _ & ->). rewrite app_nil_r. exact EBSL. }
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
cbn [dec_stack dec_frames dec_credit dec_depth] in LOR, FRM, CRD, DEP. unfold SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in LOR.
assert (DSP : 0 <= dec_stack low) by (clear; induction low; cbn [dec_stack]; unfold NBDEC_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK; lia).

assert (INL : In (S, 160) (rt_live RT Σ)).
{ specialize (LIVE (sbd_blk s, S, SBSTATE_SIZEOF)). rewrite ELBD in LIVE. exact (LIVE ltac:(left; reflexivity)). }
destruct (live_below_lo RT AF Σ m S 160 lo ART0 INL LOW) as (_ & BS1 & LOS).
destruct (af_acc_live RT AF Σ m S 160 ART0 INL) as (_ & ACS).
pose proof (live_facts RT AF Σ m S 160 ART0 INL) as (_ & _ & SIMG & SHI).
destruct (frame_below_lo RT AF Σ m fh kh lo ART0 INFH LOW) as (BF1 & BF2 & _).
pose proof (frame_facts RT AF Σ m fh kh ART0 INFH) as (FP0 & FP64 & FPIMG & _ & FPHI & _ & _ & _ & _ & _).
assert (FSZ : 0 <= fs_size kh) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
pose proof (AF_LIB Σ m ART0) as LC0. pose proof (af_client_consts RT AF Σ m ART0) as CC0.
pose proof (PMfd_mat_stable F0 fs0) as MST. pose proof (PMfd_fdfs_only F0 fs0) as FDO.
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp (dec_W IO_FP A OUT STEREO LBD) m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
destruct FA as (FA1 & FA2 & ACA & AAL). destruct FO as (FO1 & FO2 & ACO & OAL). destruct FS as (FS1 & FS2 & ACST & SAL).
assert (LOWZ : Z.of_nat (length ows) = 2000) by (rewrite LOWS; reflexivity).

assert (LIVB : forall x, In x (sb_blocks s S a) -> In (blk_addr x, blk_size x) (rt_live RT Σ)) by (intros x Hx; apply LIVE; rewrite ELBD; apply in_app_iff; left; exact Hx).
destruct (live_below_lo RT AF Σ m _ _ lo ART0 INPD LOW) as (_ & BLPD & _).
destruct BREP as ((rjb & Lrjb & BOBJ) & (bsb & BDAT & Hbsb) & BSIDE). unfold bits_cells in BOBJ. apply (proj1 (u8arr_rw_CB m D bsb)) in BDAT.
unfold BITS_SIZEOF in *.
assert (Lbsb : Z.of_nat (length bsb) = sb_buf_size b) by (pose proof BOK as OK'; unfold bits_ok in OK'; rewrite Hbsb, zlength_map_unsigned in OK'; clear - OK'; lia).
assert (BDLO : D + Z.of_nat (length bsb) <= lo) by (clear - Lbsb PD2 BLPD; lia).
pose proof JOK as (JP1 & JP2 & JG0 & JG1 & JEXC & JOQ & JIQ & JMSP & JPG & JER).
pose proof (conj INFH I) as INFHK.
pose proof (conj ART0 I) as ARTEK.

set (LALL := tl (sb_blocks s S a) ++ LBL).
assert (LALLD : forall x, In x LALL -> In x LBD) by (intros x Hx; rewrite ELBD; cbn [sb_blocks tl app] in Hx |- *; right; exact Hx).
assert (LIVEA : forall x, In x LALL -> In (blk_addr x, blk_size x) (rt_live RT Σ)) by (intros x Hx; exact (LIVE x (LALLD x Hx))).
assert (LIVEL : forall x, In x LBL -> In (blk_addr x, blk_size x) (rt_live RT Σ)) by (intros x Hx; apply LIVE; rewrite ELBD; apply in_app_iff; right; exact Hx).
assert (BOUT : forall bk x, In bk LALL -> blk_addr bk <= x < blk_addr bk + blk_size bk ->
x < lo /\ (x < S \/ S + 160 <= x) /\ (x < fh \/ fh + fs_size kh <= x) /\ (x < PD \/ PD + NDs <= x)).
{ intros bk x Hb Hx. pose proof (LIVEA bk Hb) as LB.
destruct (live_below_lo RT AF Σ m _ _ lo ART0 LB LOW) as (_ & B1 & _).
destruct (frame_live_apart RT AF Σ m fh kh _ _ ART0 INFH LB) as (B2 & _).
assert (NE : blk_addr bk <> S).
{ pose proof NDUP as ND'. rewrite ELBD in ND'. cbn [sb_blocks app map blk_id blk_addr fst snd] in ND'. apply List.NoDup_cons_iff in ND'. destruct ND' as [NI _].
intros E. apply NI. rewrite <- E. unfold LALL in Hb. cbn [sb_blocks tl app] in Hb. exact (in_map blk_id _ _ Hb). }
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 LB INL NE) as B3.
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 LB INPD (PDB bk (LALLD bk Hb))) as B4. clear - B1 B2 B3 B4 Hx. lia. }
assert (LO736 : lo <= usp - 736) by (clear - LOR DSP; unfold RT_STACK in LOR; lia).
pose proof (fun so (H : OUT_rep so m) => H) as OUTK.
cps_norm. cps_hide.
cps_seg (sbd_w1 usp lo S A OUT).
destruct POST as (m1 & g1 & xa1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & G1_0 & G1_38 & G1_52 & SV1).
pk_munch_all MU1 WM1 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LO736; cbn [outside]; split; [lia| exact I])
ltac:(fun x Hx => clear - Hx LO736 LOS; cbn [outside]; split; [lia| exact I]).
cps_seg_post.

cps_rt_sized SM0 0. { cbn; tauto. } { pose proof (dec_credit_pos low) as DP; pose proof (dec_depth_pos low) as DP2; clear - CRD DP DP2; lia. } { cps_callok. }
intros cc2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR1 & FPOS & F64 & FTOP & PO1).
Time cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRF & WRS).
pk_pres_all RT PRES2 WM2 LALL LIVEA ERR_rep OUT_rep IO_FP IO_img.
Time cps_new_frame ART2 FRS1 LV1 SP1 WRF WRS sf. cps_hide.
pose proof (AF_LIB Σ1 m2 ART2) as LC2.
set (MP := sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode (sbd_mode s)).
set (MODE := sbmode_struct (sbd_mode s)) in *.
assert (MPF : exists c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12,
ro_cells bsegs m2 MP [C8 (Z_to_bv 64 MODE); C8 c1; C8 c2; C4 c3; C4 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12]
/\ aobj bsegs m2 MP 96 /\ MP mod 8 = 0 /\ 0x10000 <= MP /\ MP + 104 <= 0x65b000).
{ subst MP MODE. destruct IMODE as [E|E]; rewrite E; cbn [sb_mode_ptr sbmode_struct].
- do 12 eexists. split; [exact (lib_const m2 A_speex_wb_mode LC_speex_wb_mode LC2 ltac:(lc_in))|].
split; [apply (aobj_lit RT AF Σ1 m2 A_speex_wb_mode 96 ART2); [unfold ACC_LITS, A_speex_wb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_speex_wb_mode; lia | unfold A_speex_wb_mode, APP_TOP; lia]|].
unfold A_speex_wb_mode. repeat split; lia.
- do 12 eexists. split; [exact (lib_const m2 A_speex_uwb_mode LC_speex_uwb_mode LC2 ltac:(lc_in))|].
split; [apply (aobj_lit RT AF Σ1 m2 A_speex_uwb_mode 96 ART2); [unfold ACC_LITS, A_speex_uwb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_speex_uwb_mode; lia | unfold A_speex_uwb_mode, APP_TOP; lia]|].
unfold A_speex_uwb_mode. repeat split; lia. }
destruct MPF as (c1 & c2 & c3 & c4 & c5 & c6 & c7 & c8 & c9 & c10 & c11 & c12 & DESC & OBM & MP8 & MPLO & MPHI).
pose proof (eq_refl : MP = sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode (sbd_mode s)) as EMP. clearbody MP.
pose proof INL as INL1.
destruct (af_acc_live RT AF Σ1 m2 S 160 ART2 INL1) as (_ & ACS2).
assert (OBS2 : aobj bsegs m2 S 160) by (split; [lia|]; split; [ulc| exact ACS2]).
assert (SOFF : S + 160 <= SH_LO \/ SH_HI <= S) by (clear - SHI; unfold hid, SH_LO, SH_HI in *; lia).
assert (SFA : S + 160 <= f \/ f + 64 <= S) by (match goal with H : hid (f + 64 <= S \/ S + 160 <= f) |- _ => clear - H; unfold hid in H; lia end).
assert (OR0 : 0 < OUT /\ OUT + 8000 < 2^63) by (split; ulc).
assert (FSZR : 0 <= sbd_frame_size s <= 320) by (rewrite IFS; destruct IMODE as [E|E]; rewrite E; cbn; lia).

assert (FS64 : fs_size kh mod 64 = 0 /\ 64 <= fs_size kh).
{ unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat kh) ltac:(lia) ltac:(lia)). split; [rewrite Z.mul_comm; apply Z_mod_mult | lia]. }
assert (CLH : forall x, fh <= x < fh + fs_size kh - 8 -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x)
by (intros x Hx; right; right; right; left; exists fh, kh; split; [exact (proj1 INFHK) | exact Hx]).
assert (FFA : fh + fs_size kh <= f \/ f + 64 <= fh).
{ destruct FS64 as (M64 & G64). destruct (Z_le_gt_dec (f + 64) fh) as [C1|C1]; [right; exact C1|]. left.
destruct (Z_lt_le_dec f fh) as [C2|C2]; [exfalso; destruct (NAF fh (CLH fh ltac:(clear - G64; lia))) as (N1 & _); apply N1; clear - C1 C2; lia|].
destruct (Z_lt_le_dec f (fh + fs_size kh - 8)) as [C3|C3]; [exfalso; destruct (NAF f (CLH f ltac:(clear - C2 C3; lia))) as (N1 & _); apply N1; clear; lia|].
clear - C3 M64 FP64 F2. Z.div_mod_to_equations. lia. }
assert (AFA : A + 48 <= f \/ f + 64 <= A) by (clear - FFA FA1 FA2; lia).
assert (OFA : OUT + 8000 <= f \/ f + 64 <= OUT) by (clear - FFA FO1 FO2; lia).
assert (TFA : STEREO + 24 <= f \/ f + 64 <= STEREO) by (clear - FFA FS1 FS2; lia).
assert (ASA : A + 48 <= sf \/ sf + 8 <= A) by (clear - FPHI SHF1 SHF2 FA1 FA2; unfold hid in *; lia).
assert (OSA : OUT + 8000 <= sf \/ sf + 8 <= OUT) by (clear - FPHI SHF1 SHF2 FO1 FO2; unfold hid in *; lia).
assert (TSA : STEREO + 24 <= sf \/ sf + 8 <= STEREO) by (clear - FPHI SHF1 SHF2 FS1 FS2; unfold hid in *; lia).
assert (BDF : D + Z.of_nat (length bsb) <= f \/ f + 64 <= D) by (clear - Lbsb PD1 PD2 FLA1; unfold hid in FLA1; lia).
assert (BDS : D + Z.of_nat (length bsb) <= sf \/ sf + 8 <= D) by (clear - Lbsb PD1 PD2 FLA2; unfold hid in FLA2; lia).
assert (LIVEA1 : forall x, In x LALL -> In (blk_addr x, blk_size x) (rt_live RT Σ1)) by (intros x Hx; rewrite LV1; exact (LIVEA x Hx)).
assert (BOUT2 : forall bk x, In bk LALL -> blk_addr bk <= x < blk_addr bk + blk_size bk -> (x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)).
{ intros bk x Hb Hx.
destruct (frame_live_apart RT AF Σ1 m2 f 0%nat _ _ ART2 INF (LIVEA1 bk Hb)) as (B2 & B3).
change (fs_size 0) with 64 in B2, B3. rewrite SHF0, <- SHF in B3. clear - B2 B3 Hx. lia. }
clear FLA1 FLA2.
cps_hide.
sb_unpack X as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_w2 usp lo S OUT A f sf MP MODE g1 s a).
destruct POST as (m3 & xt0 & xt1 & xt2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & j24 & j36 & dtx0 & -> & MU3 & WM3 & MI3 & ST3 & FR3 & FRB3 & FRS3).
clear FR1 FRB FRS HD FST PT LE SEED CFG IDC PAD.
pk_munch_all MU3 WM3 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; pose proof (BOUT2 b x Hb Hx) as H2; clear - H1 H2 LO736; cbn [outside]; repeat split; lia)
ltac:(fun x Hx => clear - Hx LO736 LOS SHF1 FIMG; cbn [outside]; repeat split; lia).
Time cps_seg_post.

assert (NDL : List.NoDup (map blk_id LBL)) by (pose proof NDUP as ND'; rewrite ELBD, map_app in ND'; exact (List.NoDup_app_remove_l _ _ ND')).
assert (LAL8L : blocks_al8 LBL) by (intros x Hx; apply LAL8; rewrite ELBD; apply in_app_iff; right; exact Hx).
assert (LIVEL1 : forall x, In x LBL -> In (blk_addr x, blk_size x) (rt_live RT Σ1)) by (intros x Hx; rewrite LV1; exact (LIVEL x Hx)).
assert (FRM1 : (length (rt_frames RT Σ1) + dec_depth low <= FRAMES_MAX)%nat) by (rewrite FRS1; cbn [length]; pose proof (dec_depth_le_frames low) as DF; clear - FRM DF; lia).
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -736)) = usp + -736) by (apply unsigned_lit; ulc).
assert (SPA608 : (usp + -736) mod 32 = 0) by (clear - SPA; Z.div_mod_to_equations; lia).
assert (POA1 : pois_above (rt_pois RT Σ1) (usp + -736)) by (eapply pois_above_le; [exact POA| clear; lia]).
cps_rt (IHC low DK Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 OUTL OUT STEREO (a_low a) LBL (CtlSetInnovationSave (0 + sbd_frame_size s)) (OUT + 4 * sbd_frame_size s) lo).
{ cbn [creq_ok]. split; [clear; lia|]. rewrite IFS. clear - IMODE. unfold hid in IMODE. destruct IMODE as [E|E]; rewrite E; cbn; lia. }
{ rewrite CR1. pose proof (dec_credit_pos low) as DP. pose proof (dec_depth_pos low) as DP2. clear - CRD DP DP2. lia. }
{ rewrite EU. exact POA1. }
{ rewrite EU. exact ST3. }
{ rewrite EU. pose proof (ctl_stack_le_dec low) as CL. clear - LOR CL. unfold RT_STACK in *. lia. }
intros cc4 (Σ2 & Hc4 & LV2 & FRS2 & SP2 & CR2 & PO2).
cps_unpack_lib Hc4 as (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & RLOW4 & CP4 & EXK4 & DST4).
cbn [creq_ivs app] in PRES4. clear DST4 CP4 RLOW.

assert (OUTB : forall x, (lo <= x \/ S <= x < S + 160 \/ fh <= x < fh + fs_size kh \/ PD <= x < PD + NDs \/ f <= x < f + 64 \/ sf <= x < sf + 8) -> outside (blocks_ivs LBL) x).
{ intros x Hx. apply outside_blocks_ivs. intros bk Hb Hin.
pose proof (BOUT bk x ltac:(unfold LALL; apply in_app_iff; right; exact Hb) Hin) as H1. pose proof (BOUT2 bk x ltac:(unfold LALL; apply in_app_iff; right; exact Hb) Hin) as H2.
clear - Hx H1 H2. lia. }
assert (APL : forall bk x, In bk (tl (sb_blocks s S a)) -> blk_addr bk <= x < blk_addr bk + blk_size bk -> outside (blocks_ivs LBL) x).
{ intros bk x Hb Hx. apply outside_blocks_ivs. intros b2 Hb2 Hin.
assert (NE : blk_addr bk <> blk_addr b2).
{ pose proof NDUP as ND'. rewrite ELBD, map_app in ND'. apply (NoDup_app_in_neq _ _ (blk_id bk) (blk_id b2) ND'); [apply in_map; cbn [sb_blocks tl] in Hb |- *; right; exact Hb| apply in_map; exact Hb2]. }
pose proof (live_apart RT AF Σ1 m3 _ _ _ _ ART (LIVEA1 bk ltac:(unfold LALL; apply in_app_iff; left; exact Hb)) (LIVEL1 b2 Hb2) NE) as AP.
clear - AP Hx Hin. lia. }
assert (OUTIMG : forall y, 65536 <= y < 6664192 -> outside (blocks_ivs LBL) y).
{ intros y Hy. apply outside_blocks_ivs. intros bk Hb Hin.
pose proof (live_facts RT AF Σ1 m3 _ _ ART (LIVEL1 bk Hb)) as (_ & _ & IM & _). clear - IM Hy Hin. unfold SEGTOP_A in IM. lia. }
assert (AGB4 : agree_blocks bsegs m3 m4 (tl (sb_blocks s S a))).
{ apply (agree_blocks_of_pres_fp RT Σ1 _ _ _ m3 m4 _ PRES4 WM4); [intros bk Hb; apply LIVEA1; unfold LALL; apply in_app_iff; left; exact Hb| exact APL]. }
apply (sb_bufs_agree s S a j m3 m4) in BUFS; [| exact JOK | exact AGB4]. clear AGB4.
pk_io_fp PRES4 ERR_rep OUT_rep IO_FP IO_img ltac:(fun y Hy => apply OUTIMG; exact Hy).
Time tr_fp PRES4 WM4 ltac:(fun x Hx => apply OUTB; first [ left; ulq0 | right; left; ulq0 | right; right; left; ulq0 | right; right; right; left; ulq0
| right; right; right; right; left; ulq0 | right; right; right; right; right; ulq0 ]).
clear DESC.
assert (PF4 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp (dec_W IO_FP A OUT STEREO LBD) m m4).
{ apply (pres_fp_trans _ _ _ _ m m3 m4 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -736) _ m3 m4 PRES4).
- intros e He. rewrite LV1. exact He.
- intros e He. rewrite FRS1. right. exact He.
- clear; lia.
- intros x Hx Ho. unfold dec_W in Ho. cbn [outside] in Ho. destruct Ho as (_ & _ & _ & Ho). apply sb_outside_app_inv in Ho. destruct Ho as [Ho _].
rewrite ELBD in Ho. exact (outside_blocks_app_r _ _ x Ho). }
clear PF. rename PF4 into PF.
clear Hc0 Hc1 ART MI3 ST3.
cps_sigma LV2 FRS2 SP2.

assert (EL2 : rt_live RT Σ2 = rt_live RT Σ) by congruence.
assert (EF2 : rt_frames RT Σ2 = (f, 0%nat) :: rt_frames RT Σ) by congruence.
assert (ES2 : rt_sp0 RT Σ2 = rt_sp0 RT Σ) by congruence.
assert (EP2 : rt_pois RT Σ2 = rt_pois RT Σ) by congruence.
assert (CB2 : rt_credit RT Σ - 1 - (Z.of_nat (dec_depth low) - 1) <= rt_credit RT Σ2 <= rt_credit RT Σ - 1) by (clear - CR1 CR2; lia).
assert (LIVEA2 : forall x, In x LALL -> In (blk_addr x, blk_size x) (rt_live RT Σ2)) by (intros x Hx; rewrite EL2; exact (LIVEA x Hx)).
clear LV1 FRS1 SP1 PO1 CR1 LV2 FRS2 SP2 PO2 CR2 LIVEA1 LIVEL1 PRES4 PRES2.

destruct (af_acc_live RT AF Σ2 m4 S 160 ART4 INL) as (_ & ACS4).
assert (OBS4 : aobj bsegs m4 S 160) by (split; [lia|]; split; [ulc| exact ACS4]).
sb_unpack X as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_w3 usp S OUT A f sf MODE).
1-2: reflexivity.

subst ms.
clear OBS4 ACS4 HD FST PT LE SEED CFG IDC PAD.
set (m5 := m4) in *. clearbody m5. clear m4.
pose proof (wmono_refl bsegs m5) as WM5.
rename FR3 into FR5. rename ART4 into ART. rename MI4 into MI5.
rename EXK4 into EXR. rename OUTK into OUTK0.

destruct (sbd_low1_facts s low OUT STEREO m5 (a_low a) LBL INV NEST RLOW4) as (ISV1 & NEST1).
assert (DKL1 : (dec_depth low1 <= k)%nat) by (rewrite DL1; exact DK).
assert (DEP1 : (dec_depth low1 <= 3)%nat) by (rewrite DL1; clear - DEP; lia).
assert (PDBL : forall x, In x LBL -> blk_addr x <> PD) by (intros x Hx; apply PDB; rewrite ELBD; apply in_app_iff; right; exact Hx).
assert (LIVEL2 : forall x, In x LBL -> In (blk_addr x, blk_size x) (rt_live RT Σ2)) by (intros x Hx; rewrite EL2; exact (LIVEL x Hx)).
assert (LIVED2 : forall x, In x LBD -> In (blk_addr x, blk_size x) (rt_live RT Σ2)) by (intros x Hx; rewrite EL2; exact (LIVE x Hx)).
assert (BREP5 : bits_rep bsegs m5 A D b).
{ split; [exists rjb; split; [exact Lrjb| unfold bits_cells; exact BOBJ]|].
split; [exists bsb; split; [apply (proj2 (u8arr_rw_CB m5 D bsb)); exact BDAT| exact Hbsb]| exact BSIDE]. }

assert (OFFW : forall x, SH_LO <= x < SH_HI -> outside (dec_W IO_FP A OUT STEREO LBD) x).
{ intros x Hx. unfold dec_W. cbn [outside].
assert (FPHI' : fh + fs_size kh <= SH_LO \/ SH_HI <= fh) by (clear - FPHI; unfold hid, SH_LO, SH_HI in *; lia).
split; [clear - FPHI' Hx FA1 FA2; unfold BITS_SIZEOF; lia|]. split; [clear - FPHI' Hx FO1 FO2; lia|]. split; [clear - FPHI' Hx FS1 FS2; lia|].
apply sb_outside_app; [exact (outside_blocks_shadow RT AF Σ2 m5 LBD x ART LIVED2 Hx)|].
apply (outside_img IO_FP x IO_img). right. clear - Hx. unfold SH_LO, SEGTOP_A in *. lia. }
assert (SHW : forall o n, fh <= o -> o + n <= fh + fs_size kh -> forall i, 0 <= i < n -> outside (dec_W IO_FP A OUT STEREO LBD) (shad (o + i))).
{ intros o n H1 H2 i Hi. apply OFFW. pose proof (frame_facts RT AF Σ2 m5 fh kh ART INFH) as (_ & _ & _ & _ & _ & _ & SA & SL & SH & _).
split.
- unfold shad, SH_LO, SHB in *. assert (0 <= (o + i) / 8) by (apply Z.div_pos; lia). lia.
- assert (shad (o + i) < shad (fh + fs_size kh)); [| lia].
unfold shad. apply Z.add_lt_mono_r. apply Z.div_lt_upper_bound; [lia|].
assert (E : fh + fs_size kh = 8 * ((fh + fs_size kh) / 8)).
{ destruct FS64 as (M64 & _). pose proof (Z.div_mod (fh + fs_size kh) 8 ltac:(lia)) as XD. rewrite Zplus_mod in XD.
replace (fh mod 8) with 0 in XD by (clear - FP64; Z.div_mod_to_equations; lia).
replace (fs_size kh mod 8) with 0 in XD by (clear - M64; Z.div_mod_to_equations; lia). cbn in XD. lia. }
lia. }
assert (FH8 : fh mod 8 = 0) by (clear - FP64; Z.div_mod_to_equations; lia).
assert (FK8 : fs_size kh mod 8 = 0) by (destruct FS64 as (M64 & _); clear - M64; Z.div_mod_to_equations; lia).
assert (ACA5 : acc bsegs m5 A 48)
by (apply (acc_pres_fp_frame _ _ _ _ m m5 fh kh A 48 PF (proj1 INFHK) FH8 FK8 ltac:(lia) FA1 ltac:(lia) (SHW A 48 FA1 ltac:(lia)) ACA)).
assert (ACO5 : acc bsegs m5 OUT 8000)
by (apply (acc_pres_fp_frame _ _ _ _ m m5 fh kh OUT 8000 PF (proj1 INFHK) FH8 FK8 ltac:(lia) FO1 ltac:(lia) (SHW OUT 8000 FO1 ltac:(lia)) ACO)).
assert (ACT5 : acc bsegs m5 STEREO 24)
by (apply (acc_pres_fp_frame _ _ _ _ m m5 fh kh STEREO 24 PF (proj1 INFHK) FH8 FK8 ltac:(lia) FS1 ltac:(lia) (SHW STEREO 24 FS1 ltac:(lia)) ACST)).

assert (OUTIMGD : forall y, 65536 <= y < 6664192 -> outside (blocks_ivs LBD) y).
{ intros y Hy. apply outside_blocks_ivs. intros bk Hb Hin.
pose proof (live_facts RT AF Σ2 m5 _ _ ART (LIVED2 bk Hb)) as (_ & _ & IM & _). clear - IM Hy Hin. unfold SEGTOP_A in IM. lia. }
assert (SSP5 : io_ssp m5).
{ apply (sbd_io_ssp_agree m m5 SSP0 (AF_DRV Σ2 m5 ART)). intros a0 Ha. apply PF; [right; left; exact (sbd_ssp_static _ Ha)|].
unfold dec_W. cbn [outside]. unfold X0r9.SSP_GUARD in Ha.
split; [clear - Ha FA1 FPIMG; unfold BITS_SIZEOF; lia|]. split; [clear - Ha FO1 FPIMG; lia|]. split; [clear - Ha FS1 FPIMG; lia|].
apply sb_outside_app; [apply OUTIMGD; lia|].
apply X0qz.outside_of_not_in_ranges'. intros Hin. apply (IO_ssp _ Hin). unfold X0r9.SSP_GUARD. exact Ha. }
assert (IFA5 : in_frame_obj RT Σ2 m5 fh kh A BITS_SIZEOF) by (unfold BITS_SIZEOF; exact (conj FA1 (conj FA2 (conj ACA5 AAL)))).
assert (IFO5 : in_frame_obj RT Σ2 m5 fh kh OUT 8000) by (exact (conj FO1 (conj FO2 (conj ACO5 OAL)))).
assert (IFS5 : in_frame_obj RT Σ2 m5 fh kh STEREO 24) by (exact (conj FS1 (conj FS2 (conj ACT5 SAL)))).
pose proof (ctl_keeps_res low (CtlSetInnovationSave (0 + sbd_frame_size s))) as (RF1 & RC1 & RS1).
change (snd (speex_decoder_ctl low (CtlSetInnovationSave (0 + sbd_frame_size s)))) with low1 in RF1, RC1, RS1.
assert (FRM5 : (length (rt_frames RT Σ2) + dec_frames low1 <= FRAMES_MAX)%nat) by (rewrite EF2, RF1; cbn [length]; clear - FRM; lia).
assert (CRD5 : dec_credit low1 <= rt_credit RT Σ2) by (rewrite RC1; pose proof (dec_depth_pos low) as DP; clear - CRD CB2 DP; lia).
assert (LOR5 : lo + RT_STACK + dec_stack low1 <= usp + -736) by (rewrite RS1; clear - LOR; unfold RT_STACK; lia).

rewrite Spec.X1nu.evw_app.
eapply rz_conseq; [| apply t_eq_sym, t_emit_app].
refine (sbd_rz_dec RT Σ2 (PMfd F0 fs0) _ (p_err q) (p_err q1) bsl _ _ _ Hc0 EBSL _ _).
{ eapply (IHD low1 DKL1 Σ2 F0 fs0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 OUT STEREO (a_low a) A D LBL b lo fh PD NDs kh ows stb q q1 retl low2 b1 PRL);
cps_auto.
{ rewrite EU. exact POA1. } { rewrite EU. exact ST4. } }
intros cc6 (Σ3 & Hc6 & RNG6 & DEP6 & MOD6 & NEST6 & OWN6 & CHR6 & BSZ6 & LV6 & FRS6 & SP6 & CR6 & PO6).
cps_unpack_lib Hc6 as (m6 & ows6 & stb6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & RLOW6 & EXR6 & BREP6 & BOK6 & OC6 & LOWS6 & STB6 & ACA6 & ACO6 & ACT6 & ERR6 & OUTK6).
clear OC STB BOBJ BDAT BREP5 RLOW4 EXR ERR0 IFA5 IFO5 IFS5.
assert (OUTK7 : forall so, OUT_rep so m -> OUT_rep so m6) by (intros so H; exact (OUTK6 so (OUTK0 so H))). clear OUTK0 OUTK6.
clear Hc0.

assert (FPHI' : fh + fs_size kh <= SH_LO \/ SH_HI <= fh) by (clear - FPHI; unfold hid, SH_LO, SH_HI in *; lia).
assert (FFA' : fh + fs_size kh <= f \/ f + 64 <= fh) by (clear - FFA; unfold hid in FFA; exact FFA).
destruct (frame_live_apart RT AF Σ2 m5 fh kh S 160 ART INFH INL1) as (SFH & _).
assert (SIMG' : S + 160 <= 65536 \/ 6664192 <= S) by (clear - SIMG; unfold hid in SIMG; exact SIMG).
assert (OUTN : forall x, (x < fh \/ fh + fs_size kh <= x) -> outside (blocks_ivs LBL) x -> (x < 65536 \/ 6664192 <= x) ->
outside (dec_W IO_FP A OUT STEREO LBL) x).
{ intros x H1 H2 H3. unfold dec_W. cbn [outside]. split; [clear - H1 FA1 FA2; unfold BITS_SIZEOF; lia|]. split; [clear - H1 FO1 FO2; lia|].
split; [clear - H1 FS1 FS2; lia|]. apply sb_outside_app; [exact H2|]. apply (outside_img IO_FP x IO_img). clear - H3; unfold SEGTOP_A; lia. }
assert (AGB6 : agree_blocks bsegs m5 m6 (tl (sb_blocks s S a))).
{ apply (agree_blocks_of_pres_fp RT Σ2 _ _ _ m5 m6 _ PRES6 WM6).
- intros bk Hb. apply LIVEA2. unfold LALL. apply in_app_iff. left. exact Hb.
- intros bk x Hb Hx. pose proof (LIVEA2 bk ltac:(unfold LALL; apply in_app_iff; left; exact Hb)) as LB.
destruct (frame_live_apart RT AF Σ2 m5 fh kh _ _ ART INFH LB) as (FA0 & _).
pose proof (live_facts RT AF Σ2 m5 _ _ ART LB) as (_ & _ & IM & _).
apply OUTN; [clear - FA0 Hx; lia | exact (APL bk x Hb Hx) | clear - IM Hx; unfold SEGTOP_A in IM; lia]. }
apply (sb_bufs_agree s S a j m5 m6) in BUFS; [| exact JOK | exact AGB6]. clear AGB6.
Time tr_fp PRES6 WM6 ltac:(fun x Hx => apply OUTN;
[ first [ clear - Hx BF1 LO736; lia | clear - Hx FFA'; lia | clear - Hx SFH; lia
| clear - Hx FPHI' SHF1 SHF2; unfold SH_LO, SH_HI in *; lia ]
| apply OUTB; first [ left; ulq0 | right; left; ulq0 | right; right; left; ulq0 | right; right; right; left; ulq0
| right; right; right; right; left; ulq0 | right; right; right; right; right; ulq0 ]
| first [ clear - Hx LO736 LOS; lia | clear - Hx FIMG; lia | clear - Hx SIMG'; lia | clear - Hx SHF1; lia ] ]).
assert (PF6 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp (dec_W IO_FP A OUT STEREO LBD) m m6).
{ apply (pres_fp_trans _ _ _ _ m m5 m6 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ2) (rt_frames RT Σ2) (usp + -736) _ m5 m6 PRES6).
- intros e He. rewrite EL2. exact He.
- intros e He. rewrite EF2. right. exact He.
- clear; lia.
- intros x Hx Ho. unfold dec_W in Ho |- *. cbn [outside] in Ho |- *. destruct Ho as (H1 & H2 & H3 & Ho).
apply sb_outside_app_inv in Ho. destruct Ho as [Hb Hio]. rewrite ELBD in Hb.
exact (conj H1 (conj H2 (conj H3 (sb_outside_app _ _ _ (outside_blocks_app_r _ _ x Hb) Hio)))). }
clear PF. rename PF6 into PF.
assert (SSP6 : io_ssp m6).
{ apply (sbd_io_ssp_agree m5 m6 SSP5 (AF_DRV Σ3 m6 ART6)). intros a0 Ha. apply PRES6; [right; left; exact (sbd_ssp_static _ Ha)|].
unfold dec_W. cbn [outside]. unfold X0r9.SSP_GUARD in Ha.
split; [clear - Ha FA1 FPIMG; unfold BITS_SIZEOF; lia|]. split; [clear - Ha FO1 FPIMG; lia|]. split; [clear - Ha FS1 FPIMG; lia|].
apply sb_outside_app; [apply OUTIMG; lia|].
apply X0qz.outside_of_not_in_ranges'. intros Hin. apply (IO_ssp _ Hin). unfold X0r9.SSP_GUARD. exact Ha. }
clear SSP5 PRES6 ART MI5 ST4.
cps_sigma LV6 FRS6 SP6.

destruct (af_acc_live RT AF Σ3 m6 S 160 ART6 INL1) as (_ & ACS6).
assert (OBS6 : aobj bsegs m6 S 160) by (split; [lia|]; split; [ulc| exact ACS6]).
sb_unpack X as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_w4 usp S OUT A f MODE s a).
{ clear - BS1 LO736 SPT. lia. }
destruct POST as (xa3' & ->).
clear HD FST PT LE SEED CFG IDC PAD OBS6 ACS6.

assert (EL3 : rt_live RT Σ3 = rt_live RT Σ) by congruence.
assert (EF3 : rt_frames RT Σ3 = (f, 0%nat) :: rt_frames RT Σ) by congruence.
assert (ES3 : rt_sp0 RT Σ3 = rt_sp0 RT Σ) by congruence.
assert (EP3 : rt_pois RT Σ3 = rt_pois RT Σ) by congruence.
assert (CB3 : rt_credit RT Σ - 1 - (Z.of_nat (dec_depth low) - 1) - dec_credit low <= rt_credit RT Σ3 <= rt_credit RT Σ - 1)
by (rewrite RC1 in CR6; clear - CB2 CR6; lia).
assert (LIVEL3 : forall x, In x LBL -> In (blk_addr x, blk_size x) (rt_live RT Σ3)) by (intros x Hx; rewrite EL3; exact (LIVEL x Hx)).
assert (LIVEA3 : forall x, In x LALL -> In (blk_addr x, blk_size x) (rt_live RT Σ3)) by (intros x Hx; rewrite EL3; exact (LIVEA x Hx)).
assert (LIVED3 : forall x, In x LBD -> In (blk_addr x, blk_size x) (rt_live RT Σ3)) by (intros x Hx; rewrite EL3; exact (LIVE x Hx)).
clear LV6 FRS6 SP6 CR6 PO6 EL2 EF2 ES2 EP2 CB2 LIVEA2 LIVEL2 LIVED2 FRM1 FRM5 CRD5.

assert (DL2 : dec_depth low2 = dec_depth low) by (rewrite DEP6; exact DL1).
destruct (dec_res_depth low2 low DL2) as (RS2' & RF2' & RC2' & RT2').
assert (DK2 : (dec_depth low2 <= k)%nat) by (rewrite DL2; exact DK).

unfold sb_fhdr in FRB3.
change [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x10d9a); C8 (Z_to_bv 64 0xbe6c0); CB 8 j24; C4 dtx0; CB 20 j36]
with ([C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x10d9a); C8 (Z_to_bv 64 0xbe6c0); CB 8 j24] ++ [C4 dtx0] ++ [CB 20 j36]) in FRB3.
apply rw_cells_app in FRB3. destruct FRB3 as (FH1 & FRB3). apply rw_cells_app in FRB3. destruct FRB3 as (FDT & FH3).
cbn [cells_size csize Nat.add app] in FDT, FH3. change (Z.of_nat 32) with 32 in FDT, FH3. change (Z.of_nat 4) with 4 in FH3.
pose proof (sbd_dtx_acc m6 f sf FRS3 Esf F64 ltac:(lia)) as ADT.
assert (DSTO : dst_obj RT Σ3 m6 (f + 32) 4) by (left; exists f, 0%nat; split; [exact INF|]; split; [lia|]; split; [change (fs_size 0) with 64; lia|];
split; [exact ADT| clear - F64; Z.div_mod_to_equations; lia]).
assert (FRM3 : (length (rt_frames RT Σ3) + dec_depth low2 <= FRAMES_MAX)%nat)
by (rewrite EF3, DL2; cbn [length]; pose proof (dec_depth_le_frames low) as DF; clear - FRM DF; lia).
assert (CRL3 : Z.of_nat (dec_depth low2) <= rt_credit RT Σ3 + 1)
by (rewrite DL2; pose proof (dec_credit_pos low) as DP; pose proof (dec_depth_pos low) as DP2; clear - CB3 CRD DP DP2; lia).
assert (LORC : lo + RT_STACK + ctl_stack low2 <= usp + -736)
by (rewrite RT2'; pose proof (ctl_stack_le_dec low) as CL; clear - LOR CL; unfold RT_STACK in *; lia).
cps_rt (IHC low2 DK2 Σ3 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 OUT OUT STEREO (a_low a) LBL CtlGetDtxStatus (f + 32) lo).
{ exists dtx0. exact FDT. } { rewrite EU. exact POA1. } { rewrite EU. exact ST6. }
intros cc7 (Σ4 & Hc7 & LV7 & FRS7 & SP7 & CR7 & PO7).
cps_unpack_lib Hc7 as (m7 & RS7 & (ART7 & MI7 & WM7 & ST7) & PRES7 & RLOW7 & CP7 & EXK7 & DST7).
cbn [creq_ivs creq_size app] in PRES7. cbn [creq_post] in CP7. destruct CP7 as (FDT7 & DTXV).
clear DST7 FDT DSTO ADT RLOW6 Hc0.
set (low3 := snd (speex_decoder_ctl low2 CtlGetDtxStatus)) in *.
set (dtx := fst (speex_decoder_ctl low2 CtlGetDtxStatus)) in *.
assert (EXR7 : retl = 0 -> EXCREADY m7 (a_low a) low3) by (intros E; exact (EXK7 (EXR6 E))). clear EXR6 EXK7.

assert (SFA' : S + 160 <= f \/ f + 64 <= S) by (clear - SFA; unfold hid in SFA; exact SFA).
assert (OFA' : OUT + 8000 <= f \/ f + 64 <= OUT) by (clear - OFA; unfold hid in OFA; exact OFA).
assert (AFA' : A + 48 <= f \/ f + 64 <= A) by (clear - AFA; unfold hid in AFA; exact AFA).
assert (TFA' : STEREO + 24 <= f \/ f + 64 <= STEREO) by (clear - TFA; unfold hid in TFA; exact TFA).
assert (BDF' : D + Z.of_nat (length bsb) <= f \/ f + 64 <= D) by (clear - BDF; unfold hid in BDF; exact BDF).
assert (SHF3' : f + 64 <= sf \/ sf + 8 <= f) by (clear - SHF3; unfold hid in SHF3; exact SHF3).
assert (FHI' : f + 64 <= SH_LO \/ SH_HI <= f) by (clear - FHI; unfold hid, SH_LO, SH_HI in *; lia).
assert (OUTB7 : forall x, (x < f + 32 \/ f + 36 <= x) -> outside (blocks_ivs LBL) x -> outside ((f + 32, f + 32 + 4) :: blocks_ivs LBL) x)
by (intros x H1 H2; cbn [outside]; split; [lia| exact H2]).
assert (AGB7 : agree_blocks bsegs m6 m7 (tl (sb_blocks s S a))).
{ apply (agree_blocks_of_pres_fp RT Σ3 _ _ _ m6 m7 _ PRES7 WM7); [intros bk Hb; apply LIVEA3; unfold LALL; apply in_app_iff; left; exact Hb|].
intros bk x Hb Hx. apply OUTB7; [| exact (APL bk x Hb Hx)].
pose proof (BOUT2 bk x ltac:(unfold LALL; apply in_app_iff; left; exact Hb) Hx) as (H2 & _). clear - H2. lia. }
apply (sb_bufs_agree s S a j m6 m7) in BUFS; [| exact JOK | exact AGB7]. clear AGB7.
destruct BREP6 as ((rj6 & Lrj6 & BOBJ6) & (bs6 & BDAT6 & Hbs6) & BSIDE6). unfold bits_cells in BOBJ6. apply (proj1 (u8arr_rw_CB m6 D bs6)) in BDAT6.
assert (Lbs6 : Z.of_nat (length bs6) = sb_buf_size b1) by (pose proof BOK6 as OK'; unfold bits_ok in OK'; rewrite Hbs6, zlength_map_unsigned in OK'; clear - OK'; lia).
assert (BD6 : D + Z.of_nat (length bs6) <= PD + NDs) by (rewrite Lbs6, BSZ6; exact PD2).
assert (BDF6 : D + Z.of_nat (length bs6) <= f \/ f + 64 <= D) by (rewrite Lbs6, BSZ6, <- Lbsb; exact BDF').
pk_io_fp PRES7 ERR_rep OUT_rep IO_FP IO_img ltac:(fun y Hy => apply OUTB7; [clear - Hy FIMG; lia | apply OUTIMG; exact Hy]).
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
assert (LOWZ6 : Z.of_nat (length ows6) = 2000) by (rewrite LOWS6; reflexivity).
assert (CLF : forall x, fh <= x < fh + fs_size kh - 8 -> aclient (rt_live RT Σ3) (rt_frames RT Σ3) (usp + -736) x)
by (intros x Hx; right; right; right; left; exists fh, kh; split; [exact INFH| exact Hx]).
assert (CLS : forall x, usp + -736 <= x < usp -> aclient (rt_live RT Σ3) (rt_frames RT Σ3) (usp + -736) x)
by (intros x Hx; left; clear - Hx SPT; unfold USTACK_TOP in *; lia).
assert (CLL : forall p n x, In (p, n) (rt_live RT Σ3) -> p <= x < p + n -> aclient (rt_live RT Σ3) (rt_frames RT Σ3) (usp + -736) x)
by (intros p n x Hp Hx; right; right; left; exists p, n; split; [exact Hp| exact Hx]).
assert (CLF0 : forall x, f <= x < f + 56 -> aclient (rt_live RT Σ3) (rt_frames RT Σ3) (usp + -736) x)
by (intros x Hx; right; right; right; left; exists f, 0%nat; split; [exact INF| change (fs_size 0) with 64; lia]).
assert (CLSF : forall x, sf <= x < sf + 8 -> aclient (rt_live RT Σ3) (rt_frames RT Σ3) (usp + -736) x)
by (intros x Hx; right; right; right; right; exists f, 0%nat; split; [exact INF| change (fs_size 0) with 64; rewrite <- SHF, SHF0; lia]).
tr1 PRES7 WM7 OC6 ltac:(fun x Hx => apply CLF; clear - Hx FO1 FO2 LOWZ6; lia)
ltac:(fun x Hx => apply OUTB7; [clear - Hx OFA' LOWZ6; lia | apply OUTB; right; right; left; clear - Hx FO1 FO2 LOWZ6; lia]).
tr1 PRES7 WM7 STB6 ltac:(fun x Hx => apply CLF; clear - Hx FS1 FS2; lia)
ltac:(fun x Hx => apply OUTB7; [clear - Hx TFA'; lia | apply OUTB; right; right; left; clear - Hx FS1 FS2; lia]).
tr1 PRES7 WM7 BOBJ6 ltac:(fun x Hx => apply CLF; clear - Hx FA1 FA2; lia)
ltac:(fun x Hx => apply OUTB7; [clear - Hx AFA'; lia | apply OUTB; right; right; left; clear - Hx FA1 FA2; lia]).
tr1 PRES7 WM7 BDAT6 ltac:(fun x Hx => apply (CLL PD NDs x INPD); clear - Hx PD1 BD6; lia)
ltac:(fun x Hx => apply OUTB7; [clear - Hx BDF6; lia | apply OUTB; right; right; right; left; clear - Hx PD1 BD6; lia]).
tr1 PRES7 WM7 FR5 ltac:(fun x Hx => apply CLS; clear - Hx; lia)
ltac:(fun x Hx => apply OUTB7; [clear - Hx BF LO736; lia | apply OUTB; left; clear - Hx LO736; lia]).
tr1 PRES7 WM7 SV1 ltac:(fun x Hx => apply CLS; clear - Hx; lia)
ltac:(fun x Hx => apply OUTB7; [clear - Hx BF LO736; lia | apply OUTB; left; clear - Hx LO736; lia]).
tr1 PRES7 WM7 X ltac:(fun x Hx => apply (CLL S 160 x INL1); clear - Hx; lia)
ltac:(fun x Hx => apply OUTB7; [clear - Hx SFA'; lia | apply OUTB; right; left; clear - Hx; lia]).
tr1 PRES7 WM7 FH1 ltac:(fun x Hx => apply CLF0; clear - Hx; lia)
ltac:(fun x Hx => apply OUTB7; [clear - Hx; lia | apply OUTB; right; right; right; right; left; clear - Hx; lia]).
tr1 PRES7 WM7 FH3 ltac:(fun x Hx => apply CLF0; clear - Hx; lia)
ltac:(fun x Hx => apply OUTB7; [clear - Hx; lia | apply OUTB; right; right; right; right; left; clear - Hx; lia]).
tr1 PRES7 WM7 FRS3 ltac:(fun x Hx => apply CLSF; clear - Hx; lia)
ltac:(fun x Hx => apply OUTB7; [clear - Hx SHF3'; lia | apply OUTB; right; right; right; right; right; clear - Hx; lia]).

assert (PF7 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp (dec_W IO_FP A OUT STEREO LBD) m m7).
{ apply (pres_fp_trans _ _ _ _ m m6 m7 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ3) (rt_frames RT Σ3) (usp + -736) _ m6 m7 PRES7).
- intros e He. rewrite EL3. exact He.
- intros e He. rewrite EF3. right. exact He.
- clear; lia.
- intros x Hx Ho. cbn [outside]. split; [destruct (NAF x Hx) as (N1 & _); clear - N1; lia|].
unfold dec_W in Ho. cbn [outside] in Ho. destruct Ho as (_ & _ & _ & Ho). apply sb_outside_app_inv in Ho. destruct Ho as [Ho _].
rewrite ELBD in Ho. exact (outside_blocks_app_r _ _ x Ho). }
clear PF. rename PF7 into PF.
assert (SHW7 : forall o n, fh <= o -> o + n <= fh + fs_size kh -> forall i, 0 <= i < n -> outside ((f + 32, f + 32 + 4) :: blocks_ivs LBL) (shad (o + i))).
{ intros o n H1 H2 i Hi.
assert (SR : SH_LO <= shad (o + i) < SH_HI).
{ pose proof (frame_facts RT AF Σ3 m6 fh kh ART6 INFH) as (_ & _ & _ & _ & _ & _ & SA & SL & SH & _). split.
- unfold shad, SH_LO, SHB in *. assert (0 <= (o + i) / 8) by (apply Z.div_pos; lia). lia.
- assert (shad (o + i) < shad (fh + fs_size kh)); [| lia].
unfold shad. apply Z.add_lt_mono_r. apply Z.div_lt_upper_bound; [lia|].
assert (E : fh + fs_size kh = 8 * ((fh + fs_size kh) / 8)).
{ pose proof (Z.div_mod (fh + fs_size kh) 8 ltac:(lia)) as XD. rewrite Zplus_mod, FH8, FK8 in XD. cbn in XD. lia. }
lia. }
cbn [outside]. split; [clear - SR FHI'; unfold SH_LO, SH_HI in *; lia|].
exact (outside_blocks_shadow RT AF Σ3 m6 LBL _ ART6 LIVEL3 SR). }
assert (ACA7 : acc bsegs m7 A 48)
by (apply (acc_pres_fp_frame _ _ _ _ m6 m7 fh kh A 48 PRES7 INFH FH8 FK8 ltac:(lia) FA1 ltac:(lia) (SHW7 A 48 FA1 ltac:(lia)) ACA6)).
assert (ACO7 : acc bsegs m7 OUT 8000)
by (apply (acc_pres_fp_frame _ _ _ _ m6 m7 fh kh OUT 8000 PRES7 INFH FH8 FK8 ltac:(lia) FO1 ltac:(lia) (SHW7 OUT 8000 FO1 ltac:(lia)) ACO6)).
assert (ACT7 : acc bsegs m7 STEREO 24)
by (apply (acc_pres_fp_frame _ _ _ _ m6 m7 fh kh STEREO 24 PRES7 INFH FH8 FK8 ltac:(lia) FS1 ltac:(lia) (SHW7 STEREO 24 FS1 ltac:(lia)) ACT6)).
assert (SSP7 : io_ssp m7).
{ apply (sbd_io_ssp_agree m6 m7 SSP6 (AF_DRV Σ4 m7 ART7)). intros a0 Ha. apply PRES7; [right; left; exact (sbd_ssp_static _ Ha)|].
unfold X0r9.SSP_GUARD in Ha. apply OUTB7; [clear - Ha FIMG; lia | apply OUTIMG; lia]. }

assert (FRB7 : rw_cells bsegs m7 f (sb_fhdr j24 (Z_to_bv 64 dtx) j36)).
{ unfold sb_fhdr.
change [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x10d9a); C8 (Z_to_bv 64 0xbe6c0); CB 8 j24; C4 (Z_to_bv 64 dtx); CB 20 j36]
with ([C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x10d9a); C8 (Z_to_bv 64 0xbe6c0); CB 8 j24] ++ [C4 (Z_to_bv 64 dtx)] ++ [CB 20 j36]).
apply rw_cells_app. split; [exact FH1|]. apply rw_cells_app. cbn [cells_size csize Nat.add]. change (Z.of_nat 32) with 32. change (Z.of_nat 4) with 4.
split; [exact FDT7| exact FH3]. }
clear FH1 FDT7 FH3 PRES7 ART6 MI6 ST6 ACA6 ACO6 ACT6 SSP6 SHW SHW7 OFFW.
cps_sigma LV7 FRS7 SP7.

assert (EL4 : rt_live RT Σ4 = rt_live RT Σ) by congruence.
assert (EF4 : rt_frames RT Σ4 = (f, 0%nat) :: rt_frames RT Σ) by congruence.
assert (ES4 : rt_sp0 RT Σ4 = rt_sp0 RT Σ) by congruence.
assert (EP4 : rt_pois RT Σ4 = rt_pois RT Σ) by congruence.
assert (CB4 : rt_credit RT Σ - 1 - 2 * (Z.of_nat (dec_depth low) - 1) - dec_credit low <= rt_credit RT Σ4 <= rt_credit RT Σ - 1)
by (rewrite DL2 in CR7; clear - CB3 CR7; lia).
assert (WMX : wmono bsegs m m7) by (eapply wmono_trans; [exact WM1|]; eapply wmono_trans; [exact WM2|]; eapply wmono_trans; [exact WM3|];
eapply wmono_trans; [exact WM4|]; eapply wmono_trans; [exact WM5|]; eapply wmono_trans; [exact WM6| exact WM7]).
pose proof (proj1 ARTEK) as ARTE. pose proof (proj1 INFHK) as INFHE.
assert (POAE : pois_above (rt_pois RT Σ) usp) by (rewrite <- EP4; exact POA).
assert (INPDE : In (PD, NDs) (rt_live RT Σ)) by (rewrite <- EL4; exact INPD).
assert (LOWE : rt_sp0 RT Σ - STACK_WIN <= lo) by (rewrite <- ES4; exact LOW).
clear LV7 FRS7 SP7 CR7 PO7 EL3 EF3 ES3 EP3 CB3.
pose proof (ctl_keeps_mode_nest low2 CtlGetDtxStatus) as (MOD3 & NEST3'). change (snd (speex_decoder_ctl low2 CtlGetDtxStatus)) with low3 in MOD3, NEST3'.
assert (DL3 : dec_depth low3 = dec_depth low) by (unfold low3; rewrite ctl_keeps_depth; exact DL2).

destruct (Z.eq_dec retl 0) as [RZ | RNZ].
2: {
destruct (PNZ RNZ) as (-> & -> & -> & ->).
assert (EIV : inval = false) by (unfold inval; destruct (Z.eq_dec retl 0); [contradiction | reflexivity]).
rewrite EIV. apply rz_emit_nil.
cps_seg (sbd_w5x usp S OUT A f MODE retl).
subst ms.
assert (REPX : DREP OUT STEREO m7 S (DecSB s low3) LBD).
{ cbn [decst_rep]. exists a, j, LBL. split; [exact ELBD|]. split; [exact S8|]. split; [exact SPOS|]. split; [exact INV|]. split; [exact JOK|].
split; [exact X|]. split; [exact BUFS|]. exists OUT. exact RLOW7. }
assert (BREPX : bits_rep bsegs m7 A D b1).
{ split; [exists rj6; split; [exact Lrj6| unfold bits_cells; exact BOBJ6]|].
split; [exists bs6; split; [apply (proj2 (u8arr_rw_CB m7 D bs6)); exact BDAT6| exact Hbs6]| exact BSIDE6]. }
assert (PD2X : D + sb_buf_size b1 <= PD + NDs) by (rewrite BSZ6; exact PD2).
set (gx := fupds g1 [(46%nat, Z_to_bv 64 A); (14%nat, Z_to_bv 64 f); (67%nat, Z_to_bv 64 f); (19%nat, Z_to_bv 64 f); (13%nat, Z_to_bv 64 sf); (40%nat, Z_to_bv 64 S);
(54%nat, Z_to_bv 64 0); (33%nat, Z_to_bv 64 ((S + 20) ≫ 3 + SHB)); (34%nat, Z_to_bv 64 (S + 20)); (61%nat, Z_to_bv 64 1);
(16%nat, Z_to_bv 64 (OUT + 4 * sbd_frame_size s))]) in *.
cps_rt (sbd_exit_cps RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AUN_lo AUN_nop Σ Σ4 F0 fs0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m m7 lo S OUT STEREO A D f fh PD NDs kh LBD gx 0 retl (DecSB s low3) b1 ows6 stb6 j24 j36 (Z_to_bv 64 dtx)
EF4 EL4 ES4 EP4 ARTE POAE NAF LIVE INPDE PD1 PD2X INFHE FA1 FA2 ACA FO1 FO2 ACO FS1 FS2 ACST ART7 MI7 RS7 ST7 LOWE
ltac:(clear - LOR DSP; unfold RT_STACK; lia) SPT SPA PF WMX FR5 ltac:(unfold gx; gslot) ltac:(unfold gx; cbn [fupds Nat.eqb]; exact G1_52) ltac:(unfold gx; gslot)
(or_introl eq_refl) SV1 FRB7 FRS3 REPX (fun E => False_ind _ (RNZ E)) BREPX BOK6 OC6 LOWS6 STB6 ERR6 OUTK).
intros c' (Σ' & Hc' & E1 & E2 & E3 & E4 & E5).
apply Hk. exists Σ'. split; [exact Hc'|].
cbn [dec_depth dec_mode dec_nestedR dec_credit].
split; [clear - RNG6; lia|]. split; [rewrite DL3; reflexivity|]. split; [reflexivity|].
split; [cbn [dec_nestedR] in NEST; destruct NEST as (NM & _); split; [rewrite MOD3, MOD6; unfold low1; rewrite (proj1 (ctl_keeps_mode_nest low _)); exact NM | exact (NEST3' NEST6)]|].
split; [exact OWN6|]. split; [exact CHR6|]. split; [exact BSZ6|].
split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [| exact E5].
rewrite E4. pose proof (dec_depth_pos low) as DP. clear - CB4 DP. lia. }

rewrite RZ in Hc.
assert (EIB : (if inval then notify_bytes MSG_INVALID_MODE else []) = sbd_inv_bytes s b1)
by (unfold inval, sbd_inv_bytes; destruct (submode_at _ _); [reflexivity| destruct (sbw_id b1 =? 0); reflexivity]).
rewrite EIB.
assert (NMW : dec_mode low3 = sbm_nb_mode (sbd_mode s)).
{ cbn [dec_nestedR] in NEST. destruct NEST as (NM & _). rewrite MOD3, MOD6. unfold low1. rewrite (proj1 (ctl_keeps_mode_nest low _)). exact NM. }
assert (BREPW : bits_rep bsegs m7 A D b1).
{ split; [exists rj6; split; [exact Lrj6| unfold bits_cells; exact BOBJ6]|].
split; [exists bs6; split; [apply (proj2 (u8arr_rw_CB m7 D bs6)); exact BDAT6| exact Hbs6]| exact BSIDE6]. }
refine (rz_cpsE RT Σ4 (PMfd F0 fs0) _ _ _ T cc7 Hc
(sbd_wph_cps RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img IO_ssp AF_DRV AF_ERRV AF_LIB FPL APO AUN_lo AUN_nop MEMS QMF16 LOST LOOP
Σ Σ4 F0 fs0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
m m7 lo S OUT STEREO A D f fh PD NDs kh LBD LBL
(fupds g1 [(46%nat, Z_to_bv 64 A); (14%nat, Z_to_bv 64 f); (67%nat, Z_to_bv 64 f); (19%nat, Z_to_bv 64 f); (13%nat, Z_to_bv 64 sf); (40%nat, Z_to_bv 64 S);
(54%nat, Z_to_bv 64 0); (33%nat, Z_to_bv 64 ((S + 20) ≫ 3 + SHB)); (34%nat, Z_to_bv 64 (S + 20)); (61%nat, Z_to_bv 64 1);
(16%nat, Z_to_bv 64 (OUT + 4 * sbd_frame_size s))])
s a j low low3 b b1 ows6 stb6 j24 j36 dtx q1 q' ret d' b'
(PZ RZ) DL3 NMW (NEST3' NEST6) ltac:(clear - DEP; lia) OWN6 CHR6 BSZ6
(fun d E => IHC d ltac:(rewrite E; exact DK)) ELBD NDUP LAL8 S8 SPOS INV JOK ISV
EF4 EL4 ES4 EP4 CB4 CRD FRM ARTE POAE NAF LIVE INPDE PD1 ltac:(rewrite BSZ6; exact PD2) PDB INFHE
FA1 FA2 ACA AAL FO1 FO2 ACO OAL FS1 FS2 ACST SAL HAO HAS HOS FD2
LOWE ltac:(clear - LOR; unfold RT_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK; lia) SPT SPA
ART7 MI7 RS7 ST7 PF WMX FR5
ltac:(cbn [fupds Nat.eqb]; exact G1_0) ltac:(cbn [fupds Nat.eqb]; reflexivity) ltac:(cbn [fupds Nat.eqb]; reflexivity) ltac:(cbn [fupds Nat.eqb]; reflexivity)
ltac:(cbn [fupds Nat.eqb]; reflexivity) ltac:(cbn [fupds Nat.eqb]; reflexivity) ltac:(cbn [fupds Nat.eqb]; reflexivity) ltac:(cbn [fupds Nat.eqb]; reflexivity)
ltac:(cbn [fupds Nat.eqb]; exact G1_52) ltac:(cbn [fupds Nat.eqb]; reflexivity) ltac:(cbn [fupds Nat.eqb]; reflexivity) ltac:(cbn [fupds Nat.eqb]; reflexivity)
ltac:(cbn [fupds Nat.eqb]; reflexivity) ltac:(cbn [fupds Nat.eqb]; exact G1_38)
SV1 FRB7 DTXV FRS3 X BUFS RLOW7 (EXR7 RZ) BREPW BOK6 OC6 LOWS6 STB6 ACA7 ACO7 ACT7 ERR6 OUTK SSP7) _).
intros c' Hc'. apply Hk. exact Hc'.
Qed.
End SbDecodeCPS.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac simpl_sizes ::=
rewrite ?X06d.sb_cells_size, ?cells_size_sb_fhdr, ?cells_size_sb_fshadow, ?cells_size_sb_fr, ?cells_size_sb_saves, ?cells_size_sb_slots,
?cells_size_sbp_hdr, ?cells_size_sbp_ptrs, ?cells_size_sbp_cfg, ?app_length, ?cells_size_app, ?cells_size_f32, ?length_f32;
cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length, ?cells_size_f32, ?length_f32; cbn [length].

Section SbDecodeCPS.
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
Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis APO : alloca_poison_contract RT.
Hypothesis AUN_lo : allocas_unpoison_lo_contract RT.
Hypothesis AUN_nop : allocas_unpoison_nop_contract RT.
Hypothesis MEMS : memset_icontract RT e_asan_memset.
Hypothesis QMF16 : forall N, N = 320 \/ N = 640 -> qmf_synth_cps16 RT N.
Hypothesis LOST : sb_decode_lost_cps RT.
Hypothesis LOOP : sb_subframe_cps RT.

Theorem sb_decode_cps : forall k : nat,
(forall d, (dec_depth d <= k)%nat -> dec_appends d) ->
(forall d, (dec_depth d <= k)%nat -> dec_cps_at RT OUT_rep ERR_rep IO_FP A_speex_decode_native d) ->
(forall d, (dec_depth d <= k)%nat -> ctl2_cps_at RT d) ->
forall s low, (dec_depth low <= k)%nat -> dec_cps_at RT OUT_rep ERR_rep IO_FP A_sb_decode (DecSB s low).
Proof using AF ERR_loc OUT_loc IO_img IO_ssp AF_DRV AF_ERRV AF_LIB FPL SM0 APO AUN_lo AUN_nop MEMS QMF16 LOST LOOP.
intros k IHA IHD IHC s low DK Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
OUT STEREO S A D LBD b lo fh PD NDs kh ows stb q q' ret d' b' PRUN -> -> -> -> REP DEP ISV NEST NDUP LAL8 LIVE BREP BOK INPD PD1 PD2 PDB OC LOWS STB INFH FA FO FS
HAO HAS HOS FD2 ERR0 SSP0 FRM CRD POA ART0 MI0 FRM0 ST0 LOW LOR SPT SPA.
pose proof REP as REP0. cbn [decst_rep] in REP0. destruct REP0 as (a & j & LBL & ELBD & S8 & SPOS & INV & JOK & X & BUFS & OUTL & RLOW).
pose proof INV as (IMODE & IFS & IFFS & ISFS & INS & ILPC & IFST & _ & _ & IES & IID & IISV).
destruct (sb_decode_prun s low b q ret d' b' q' IES PRUN) as (retl & low2 & b1 & q1 & PRL & PNZ & PZ).
pose proof (ctl_keeps_depth low (CtlSetInnovationSave (0 + sbd_frame_size s))) as DL1.
set (low1 := snd (speex_decoder_ctl low (CtlSetInnovationSave (0 + sbd_frame_size s)))) in *.
destruct (IHA low1 ltac:(rewrite DL1; exact DK) b q _ q1 PRL) as (bsl & EBSL).

set (inval := match Z.eq_dec retl 0 with
| left _ => match submode_at (sbm_submodes (sbd_mode s)) (sbw_id b1) with None => negb (sbw_id b1 =? 0) | Some _ => false end
| right _ => false end).
exists (bsl ++ if inval then notify_bytes MSG_INVALID_MODE else []).
split.
{ subst inval. destruct (Z.eq_dec retl 0) as [E|NE].
- specialize (PZ E). unfold sb_outcome in PZ. cbv zeta in PZ.
destruct (submode_at (sbm_submodes (sbd_mode s)) (sbw_id b1)) as [sm|].
+ destruct PZ as (_ & _ & _ & ->). rewrite app_nil_r. exact EBSL.
+ destruct (sbw_id b1 =? 0); cbn [negb].
* destruct PZ as (_ & _ & _ & ->). rewrite app_nil_r. exact EBSL.
* destruct PZ as (_ & _ & _ & ->). unfold p_app. cbn [p_err]. rewrite EBSL, app_assoc. reflexivity.
- destruct (PNZ NE) as (_ & _ & _ & ->). rewrite app_nil_r. exact EBSL. }
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
cbn [dec_stack dec_frames dec_credit dec_depth] in LOR, FRM, CRD, DEP. unfold SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK in LOR.
assert (DSP : 0 <= dec_stack low) by (clear; induction low; cbn [dec_stack]; unfold NBDEC_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK; lia).

assert (INL : In (S, 160) (rt_live RT Σ)).
{ specialize (LIVE (sbd_blk s, S, SBSTATE_SIZEOF)). rewrite ELBD in LIVE. exact (LIVE ltac:(left; reflexivity)). }
destruct (live_below_lo RT AF Σ m S 160 lo ART0 INL LOW) as (_ & BS1 & LOS).
destruct (af_acc_live RT AF Σ m S 160 ART0 INL) as (_ & ACS).
pose proof (live_facts RT AF Σ m S 160 ART0 INL) as (_ & _ & SIMG & SHI).
destruct (frame_below_lo RT AF Σ m fh kh lo ART0 INFH LOW) as (BF1 & BF2 & _).
pose proof (frame_facts RT AF Σ m fh kh ART0 INFH) as (FP0 & FP64 & FPIMG & _ & FPHI & _ & _ & _ & _ & _).
assert (FSZ : 0 <= fs_size kh) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
pose proof (AF_LIB Σ m ART0) as LC0. pose proof (af_client_consts RT AF Σ m ART0) as CC0.
pose proof (PMfd_mat_stable F0 fs0) as MST. pose proof (PMfd_fdfs_only F0 fs0) as FDO.
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp (dec_W IO_FP A OUT STEREO LBD) m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
destruct FA as (FA1 & FA2 & ACA & AAL). destruct FO as (FO1 & FO2 & ACO & OAL). destruct FS as (FS1 & FS2 & ACST & SAL).
assert (LOWZ : Z.of_nat (length ows) = 2000) by (rewrite LOWS; reflexivity).

assert (LIVB : forall x, In x (sb_blocks s S a) -> In (blk_addr x, blk_size x) (rt_live RT Σ)) by (intros x Hx; apply LIVE; rewrite ELBD; apply in_app_iff; left; exact Hx).
destruct (live_below_lo RT AF Σ m _ _ lo ART0 INPD LOW) as (_ & BLPD & _).
destruct BREP as ((rjb & Lrjb & BOBJ) & (bsb & BDAT & Hbsb) & BSIDE). unfold bits_cells in BOBJ. apply (proj1 (u8arr_rw_CB m D bsb)) in BDAT.
unfold BITS_SIZEOF in *.
assert (Lbsb : Z.of_nat (length bsb) = sb_buf_size b) by (pose proof BOK as OK'; unfold bits_ok in OK'; rewrite Hbsb, zlength_map_unsigned in OK'; clear - OK'; lia).
assert (BDLO : D + Z.of_nat (length bsb) <= lo) by (clear - Lbsb PD2 BLPD; lia).
pose proof JOK as (JP1 & JP2 & JG0 & JG1 & JEXC & JOQ & JIQ & JMSP & JPG & JER).
pose proof (conj INFH I) as INFHK.
pose proof (conj ART0 I) as ARTEK.

set (LALL := tl (sb_blocks s S a) ++ LBL).
assert (LALLD : forall x, In x LALL -> In x LBD) by (intros x Hx; rewrite ELBD; cbn [sb_blocks tl app] in Hx |- *; right; exact Hx).
assert (LIVEA : forall x, In x LALL -> In (blk_addr x, blk_size x) (rt_live RT Σ)) by (intros x Hx; exact (LIVE x (LALLD x Hx))).
assert (LIVEL : forall x, In x LBL -> In (blk_addr x, blk_size x) (rt_live RT Σ)) by (intros x Hx; apply LIVE; rewrite ELBD; apply in_app_iff; right; exact Hx).
assert (BOUT : forall bk x, In bk LALL -> blk_addr bk <= x < blk_addr bk + blk_size bk ->
x < lo /\ (x < S \/ S + 160 <= x) /\ (x < fh \/ fh + fs_size kh <= x) /\ (x < PD \/ PD + NDs <= x)).
{ intros bk x Hb Hx. pose proof (LIVEA bk Hb) as LB.
destruct (live_below_lo RT AF Σ m _ _ lo ART0 LB LOW) as (_ & B1 & _).
destruct (frame_live_apart RT AF Σ m fh kh _ _ ART0 INFH LB) as (B2 & _).
assert (NE : blk_addr bk <> S).
{ pose proof NDUP as ND'. rewrite ELBD in ND'. cbn [sb_blocks app map blk_id blk_addr fst snd] in ND'. apply List.NoDup_cons_iff in ND'. destruct ND' as [NI _].
intros E. apply NI. rewrite <- E. unfold LALL in Hb. cbn [sb_blocks tl app] in Hb. exact (in_map blk_id _ _ Hb). }
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 LB INL NE) as B3.
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 LB INPD (PDB bk (LALLD bk Hb))) as B4. clear - B1 B2 B3 B4 Hx. lia. }
assert (LO608 : lo <= usp - 608) by (clear - LOR DSP; unfold RT_STACK in LOR; lia).
pose proof (fun so (H : OUT_rep so m) => H) as OUTK.
cps_norm. cps_hide.
cps_seg (sbd_w1 usp lo S A OUT).
destruct POST as (m1 & g1 & xa1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & G1_0 & G1_38 & G1_52 & SV1).
pk_munch_all MU1 WM1 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LO608; cbn [outside]; split; [lia| exact I])
ltac:(fun x Hx => clear - Hx LO608 LOS; cbn [outside]; split; [lia| exact I]).
cps_seg_post.

cps_rt_sized SM0 0. { cbn; tauto. } { pose proof (dec_credit_pos low) as DP; pose proof (dec_depth_pos low) as DP2; clear - CRD DP DP2; lia. } { cps_callok. }
intros cc2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR1 & FPOS & F64 & FTOP & PO1).
Time cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRF & WRS).
pk_pres_all RT PRES2 WM2 LALL LIVEA ERR_rep OUT_rep IO_FP IO_img.
Time cps_new_frame ART2 FRS1 LV1 SP1 WRF WRS sf. cps_hide.
pose proof (AF_LIB Σ1 m2 ART2) as LC2.
set (MP := sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode (sbd_mode s)).
set (MODE := sbmode_struct (sbd_mode s)) in *.
assert (MPF : exists c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12,
ro_cells asegs m2 MP [C8 (Z_to_bv 64 MODE); C8 c1; C8 c2; C4 c3; C4 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12]
/\ aobj asegs m2 MP 96 /\ MP mod 8 = 0 /\ 0x10000 <= MP /\ MP + 104 <= 0x652000).
{ subst MP MODE. destruct IMODE as [E|E]; rewrite E; cbn [sb_mode_ptr sbmode_struct].
- do 12 eexists. split; [exact (lib_const m2 A_speex_wb_mode LC_speex_wb_mode LC2 ltac:(lc_in))|].
split; [apply (aobj_lit RT AF Σ1 m2 A_speex_wb_mode 96 ART2); [unfold ACC_LITS, A_speex_wb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_speex_wb_mode; lia | unfold A_speex_wb_mode, APP_TOP; lia]|].
unfold A_speex_wb_mode. repeat split; lia.
- do 12 eexists. split; [exact (lib_const m2 A_speex_uwb_mode LC_speex_uwb_mode LC2 ltac:(lc_in))|].
split; [apply (aobj_lit RT AF Σ1 m2 A_speex_uwb_mode 96 ART2); [unfold ACC_LITS, A_speex_uwb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_speex_uwb_mode; lia | unfold A_speex_uwb_mode, APP_TOP; lia]|].
unfold A_speex_uwb_mode. repeat split; lia. }
destruct MPF as (c1 & c2 & c3 & c4 & c5 & c6 & c7 & c8 & c9 & c10 & c11 & c12 & DESC & OBM & MP8 & MPLO & MPHI).
pose proof (eq_refl : MP = sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode (sbd_mode s)) as EMP. clearbody MP.
pose proof INL as INL1.
destruct (af_acc_live RT AF Σ1 m2 S 160 ART2 INL1) as (_ & ACS2).
assert (OBS2 : aobj asegs m2 S 160) by (split; [lia|]; split; [ulc| exact ACS2]).
assert (SOFF : S + 160 <= SH_LO \/ SH_HI <= S) by (clear - SHI; unfold hid, SH_LO, SH_HI in *; lia).
assert (SFA : S + 160 <= f \/ f + 64 <= S) by (match goal with H : hid (f + 64 <= S \/ S + 160 <= f) |- _ => clear - H; unfold hid in H; lia end).
assert (OR0 : 0 <= OUT /\ OUT + 8000 < 2^63) by (split; ulc).
assert (FSZR : 0 <= sbd_frame_size s <= 320) by (rewrite IFS; destruct IMODE as [E|E]; rewrite E; cbn; lia).

assert (FS64 : fs_size kh mod 64 = 0 /\ 64 <= fs_size kh).
{ unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat kh) ltac:(lia) ltac:(lia)). split; [rewrite Z.mul_comm; apply Z_mod_mult | lia]. }
assert (CLH : forall x, fh <= x < fh + fs_size kh - 8 -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x)
by (intros x Hx; right; right; right; left; exists fh, kh; split; [exact (proj1 INFHK) | exact Hx]).
assert (FFA : fh + fs_size kh <= f \/ f + 64 <= fh).
{ destruct FS64 as (M64 & G64). destruct (Z_le_gt_dec (f + 64) fh) as [C1|C1]; [right; exact C1|]. left.
destruct (Z_lt_le_dec f fh) as [C2|C2]; [exfalso; destruct (NAF fh (CLH fh ltac:(clear - G64; lia))) as (N1 & _); apply N1; clear - C1 C2; lia|].
destruct (Z_lt_le_dec f (fh + fs_size kh - 8)) as [C3|C3]; [exfalso; destruct (NAF f (CLH f ltac:(clear - C2 C3; lia))) as (N1 & _); apply N1; clear; lia|].
clear - C3 M64 FP64 F2. Z.div_mod_to_equations. lia. }
assert (AFA : A + 48 <= f \/ f + 64 <= A) by (clear - FFA FA1 FA2; lia).
assert (OFA : OUT + 8000 <= f \/ f + 64 <= OUT) by (clear - FFA FO1 FO2; lia).
assert (TFA : STEREO + 24 <= f \/ f + 64 <= STEREO) by (clear - FFA FS1 FS2; lia).
assert (ASA : A + 48 <= sf \/ sf + 8 <= A) by (clear - FPHI SHF1 SHF2 FA1 FA2; unfold hid in *; lia).
assert (OSA : OUT + 8000 <= sf \/ sf + 8 <= OUT) by (clear - FPHI SHF1 SHF2 FO1 FO2; unfold hid in *; lia).
assert (TSA : STEREO + 24 <= sf \/ sf + 8 <= STEREO) by (clear - FPHI SHF1 SHF2 FS1 FS2; unfold hid in *; lia).
assert (BDF : D + Z.of_nat (length bsb) <= f \/ f + 64 <= D) by (clear - Lbsb PD1 PD2 FLA1; unfold hid in FLA1; lia).
assert (BDS : D + Z.of_nat (length bsb) <= sf \/ sf + 8 <= D) by (clear - Lbsb PD1 PD2 FLA2; unfold hid in FLA2; lia).
assert (LIVEA1 : forall x, In x LALL -> In (blk_addr x, blk_size x) (rt_live RT Σ1)) by (intros x Hx; rewrite LV1; exact (LIVEA x Hx)).
assert (BOUT2 : forall bk x, In bk LALL -> blk_addr bk <= x < blk_addr bk + blk_size bk -> (x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)).
{ intros bk x Hb Hx.
destruct (frame_live_apart RT AF Σ1 m2 f 0%nat _ _ ART2 INF (LIVEA1 bk Hb)) as (B2 & B3).
change (fs_size 0) with 64 in B2, B3. rewrite SHF0, <- SHF in B3. clear - B2 B3 Hx. lia. }
clear FLA1 FLA2.
cps_hide.
sb_unpack X as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_w2 usp lo S OUT f sf MP MODE g1 s a).
destruct POST as (m3 & xt0 & xt1 & xt2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & j24 & j36 & dtx0 & -> & MU3 & WM3 & MI3 & ST3 & FR3 & FRB3 & FRS3).
clear FR1 FRB FRS HD FST PT LE SEED CFG IDC PAD.
pk_munch_all MU3 WM3 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; pose proof (BOUT2 b x Hb Hx) as H2; clear - H1 H2 LO608; cbn [outside]; repeat split; lia)
ltac:(fun x Hx => clear - Hx LO608 LOS SHF1 FIMG; cbn [outside]; repeat split; lia).
Time cps_seg_post.

assert (NDL : List.NoDup (map blk_id LBL)) by (pose proof NDUP as ND'; rewrite ELBD, map_app in ND'; exact (List.NoDup_app_remove_l _ _ ND')).
assert (LAL8L : blocks_al8 LBL) by (intros x Hx; apply LAL8; rewrite ELBD; apply in_app_iff; right; exact Hx).
assert (LIVEL1 : forall x, In x LBL -> In (blk_addr x, blk_size x) (rt_live RT Σ1)) by (intros x Hx; rewrite LV1; exact (LIVEL x Hx)).
assert (FRM1 : (length (rt_frames RT Σ1) + dec_depth low <= FRAMES_MAX)%nat) by (rewrite FRS1; cbn [length]; pose proof (dec_depth_le_frames low) as DF; clear - FRM DF; lia).
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -608)) = usp + -608) by (apply unsigned_lit; ulc).
assert (SPA608 : (usp + -608) mod 32 = 0) by (clear - SPA; Z.div_mod_to_equations; lia).
assert (POA1 : pois_above (rt_pois RT Σ1) (usp + -608)) by (eapply pois_above_le; [exact POA| clear; lia]).
cps_rt (IHC low DK Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 OUTL OUT STEREO (a_low a) LBL (CtlSetInnovationSave (0 + sbd_frame_size s)) (OUT + 4 * sbd_frame_size s) lo).
{ cbn [creq_ok]. split; [clear; lia|]. rewrite IFS. clear - IMODE. unfold hid in IMODE. destruct IMODE as [E|E]; rewrite E; cbn; lia. }
{ rewrite CR1. pose proof (dec_credit_pos low) as DP. pose proof (dec_depth_pos low) as DP2. clear - CRD DP DP2. lia. }
{ rewrite EU. exact POA1. }
{ rewrite EU. exact ST3. }
{ rewrite EU. pose proof (ctl_stack_le_dec low) as CL. clear - LOR CL. unfold RT_STACK in *. lia. }
intros cc4 (Σ2 & Hc4 & LV2 & FRS2 & SP2 & CR2 & PO2).
cps_unpack_lib Hc4 as (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & RLOW4 & CP4 & EXK4 & DST4).
cbn [creq_ivs app] in PRES4. clear DST4 CP4 RLOW.

assert (OUTB : forall x, (lo <= x \/ S <= x < S + 160 \/ fh <= x < fh + fs_size kh \/ PD <= x < PD + NDs \/ f <= x < f + 64 \/ sf <= x < sf + 8) -> outside (blocks_ivs LBL) x).
{ intros x Hx. apply outside_blocks_ivs. intros bk Hb Hin.
pose proof (BOUT bk x ltac:(unfold LALL; apply in_app_iff; right; exact Hb) Hin) as H1. pose proof (BOUT2 bk x ltac:(unfold LALL; apply in_app_iff; right; exact Hb) Hin) as H2.
clear - Hx H1 H2. lia. }
assert (APL : forall bk x, In bk (tl (sb_blocks s S a)) -> blk_addr bk <= x < blk_addr bk + blk_size bk -> outside (blocks_ivs LBL) x).
{ intros bk x Hb Hx. apply outside_blocks_ivs. intros b2 Hb2 Hin.
assert (NE : blk_addr bk <> blk_addr b2).
{ pose proof NDUP as ND'. rewrite ELBD, map_app in ND'. apply (NoDup_app_in_neq _ _ (blk_id bk) (blk_id b2) ND'); [apply in_map; cbn [sb_blocks tl] in Hb |- *; right; exact Hb| apply in_map; exact Hb2]. }
pose proof (live_apart RT AF Σ1 m3 _ _ _ _ ART (LIVEA1 bk ltac:(unfold LALL; apply in_app_iff; left; exact Hb)) (LIVEL1 b2 Hb2) NE) as AP.
clear - AP Hx Hin. lia. }
assert (OUTIMG : forall y, 65536 <= y < 6627328 -> outside (blocks_ivs LBL) y).
{ intros y Hy. apply outside_blocks_ivs. intros bk Hb Hin.
pose proof (live_facts RT AF Σ1 m3 _ _ ART (LIVEL1 bk Hb)) as (_ & _ & IM & _). clear - IM Hy Hin. unfold SEGTOP_A in IM. lia. }
assert (AGB4 : agree_blocks asegs m3 m4 (tl (sb_blocks s S a))).
{ apply (agree_blocks_of_pres_fp RT Σ1 _ _ _ m3 m4 _ PRES4 WM4); [intros bk Hb; apply LIVEA1; unfold LALL; apply in_app_iff; left; exact Hb| exact APL]. }
apply (sb_bufs_agree s S a j m3 m4) in BUFS; [| exact JOK | exact AGB4]. clear AGB4.
pk_io_fp PRES4 ERR_rep OUT_rep IO_FP IO_img ltac:(fun y Hy => apply OUTIMG; exact Hy).
Time tr_fp PRES4 WM4 ltac:(fun x Hx => apply OUTB; first [ left; ulq0 | right; left; ulq0 | right; right; left; ulq0 | right; right; right; left; ulq0
| right; right; right; right; left; ulq0 | right; right; right; right; right; ulq0 ]).
clear DESC.
assert (PF4 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp (dec_W IO_FP A OUT STEREO LBD) m m4).
{ apply (pres_fp_trans _ _ _ _ m m3 m4 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -608) _ m3 m4 PRES4).
- intros e He. rewrite LV1. exact He.
- intros e He. rewrite FRS1. right. exact He.
- clear; lia.
- intros x Hx Ho. unfold dec_W in Ho. cbn [outside] in Ho. destruct Ho as (_ & _ & _ & Ho). apply sb_outside_app_inv in Ho. destruct Ho as [Ho _].
rewrite ELBD in Ho. exact (outside_blocks_app_r _ _ x Ho). }
clear PF. rename PF4 into PF.
clear Hc0 Hc1 ART MI3 ST3.
cps_sigma LV2 FRS2 SP2.

assert (EL2 : rt_live RT Σ2 = rt_live RT Σ) by congruence.
assert (EF2 : rt_frames RT Σ2 = (f, 0%nat) :: rt_frames RT Σ) by congruence.
assert (ES2 : rt_sp0 RT Σ2 = rt_sp0 RT Σ) by congruence.
assert (EP2 : rt_pois RT Σ2 = rt_pois RT Σ) by congruence.
assert (CB2 : rt_credit RT Σ - 1 - (Z.of_nat (dec_depth low) - 1) <= rt_credit RT Σ2 <= rt_credit RT Σ - 1) by (clear - CR1 CR2; lia).
assert (LIVEA2 : forall x, In x LALL -> In (blk_addr x, blk_size x) (rt_live RT Σ2)) by (intros x Hx; rewrite EL2; exact (LIVEA x Hx)).
clear LV1 FRS1 SP1 PO1 CR1 LV2 FRS2 SP2 PO2 CR2 LIVEA1 LIVEL1 PRES4 PRES2.

destruct (af_acc_live RT AF Σ2 m4 S 160 ART4 INL) as (_ & ACS4).
assert (OBS4 : aobj asegs m4 S 160) by (split; [lia|]; split; [ulc| exact ACS4]).
sb_unpack X as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_w3 usp S OUT A f sf MODE).
destruct POST as (m5 & -> & MU5 & WM5 & MI5 & FR5).
clear FR3 OBS4 ACS4 HD FST PT LE SEED CFG IDC PAD.
pk_munch_all MU5 WM5 LALL ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => pose proof (BOUT b x Hb Hx) as H1; clear - H1 LO608; cbn [outside]; repeat split; lia)
ltac:(fun x Hx => clear - Hx LO608 LOS; cbn [outside]; repeat split; lia).
Time cps_seg_post.

destruct (sbd_low1_facts s low OUT STEREO m5 (a_low a) LBL INV NEST RLOW4) as (ISV1 & NEST1).
assert (DKL1 : (dec_depth low1 <= k)%nat) by (rewrite DL1; exact DK).
assert (DEP1 : (dec_depth low1 <= 3)%nat) by (rewrite DL1; clear - DEP; lia).
assert (PDBL : forall x, In x LBL -> blk_addr x <> PD) by (intros x Hx; apply PDB; rewrite ELBD; apply in_app_iff; right; exact Hx).
assert (LIVEL2 : forall x, In x LBL -> In (blk_addr x, blk_size x) (rt_live RT Σ2)) by (intros x Hx; rewrite EL2; exact (LIVEL x Hx)).
assert (LIVED2 : forall x, In x LBD -> In (blk_addr x, blk_size x) (rt_live RT Σ2)) by (intros x Hx; rewrite EL2; exact (LIVE x Hx)).
assert (BREP5 : bits_rep asegs m5 A D b).
{ split; [exists rjb; split; [exact Lrjb| unfold bits_cells; exact BOBJ]|].
split; [exists bsb; split; [apply (proj2 (u8arr_rw_CB m5 D bsb)); exact BDAT| exact Hbsb]| exact BSIDE]. }

assert (OFFW : forall x, SH_LO <= x < SH_HI -> outside (dec_W IO_FP A OUT STEREO LBD) x).
{ intros x Hx. unfold dec_W. cbn [outside].
assert (FPHI' : fh + fs_size kh <= SH_LO \/ SH_HI <= fh) by (clear - FPHI; unfold hid, SH_LO, SH_HI in *; lia).
split; [clear - FPHI' Hx FA1 FA2; unfold BITS_SIZEOF; lia|]. split; [clear - FPHI' Hx FO1 FO2; lia|]. split; [clear - FPHI' Hx FS1 FS2; lia|].
apply sb_outside_app; [exact (outside_blocks_shadow RT AF Σ2 m5 LBD x ART LIVED2 Hx)|].
apply (outside_img IO_FP x IO_img). right. clear - Hx. unfold SH_LO, SEGTOP_A in *. lia. }
assert (SHW : forall o n, fh <= o -> o + n <= fh + fs_size kh -> forall i, 0 <= i < n -> outside (dec_W IO_FP A OUT STEREO LBD) (shad (o + i))).
{ intros o n H1 H2 i Hi. apply OFFW. pose proof (frame_facts RT AF Σ2 m5 fh kh ART INFH) as (_ & _ & _ & _ & _ & _ & SA & SL & SH & _).
split.
- unfold shad, SH_LO, SHB in *. assert (0 <= (o + i) / 8) by (apply Z.div_pos; lia). lia.
- assert (shad (o + i) < shad (fh + fs_size kh)); [| lia].
unfold shad. apply Z.add_lt_mono_r. apply Z.div_lt_upper_bound; [lia|].
assert (E : fh + fs_size kh = 8 * ((fh + fs_size kh) / 8)).
{ destruct FS64 as (M64 & _). pose proof (Z.div_mod (fh + fs_size kh) 8 ltac:(lia)) as XD. rewrite Zplus_mod in XD.
replace (fh mod 8) with 0 in XD by (clear - FP64; Z.div_mod_to_equations; lia).
replace (fs_size kh mod 8) with 0 in XD by (clear - M64; Z.div_mod_to_equations; lia). cbn in XD. lia. }
lia. }
assert (FH8 : fh mod 8 = 0) by (clear - FP64; Z.div_mod_to_equations; lia).
assert (FK8 : fs_size kh mod 8 = 0) by (destruct FS64 as (M64 & _); clear - M64; Z.div_mod_to_equations; lia).
assert (ACA5 : acc asegs m5 A 48)
by (apply (acc_pres_fp_frame _ _ _ _ m m5 fh kh A 48 PF (proj1 INFHK) FH8 FK8 ltac:(lia) FA1 ltac:(lia) (SHW A 48 FA1 ltac:(lia)) ACA)).
assert (ACO5 : acc asegs m5 OUT 8000)
by (apply (acc_pres_fp_frame _ _ _ _ m m5 fh kh OUT 8000 PF (proj1 INFHK) FH8 FK8 ltac:(lia) FO1 ltac:(lia) (SHW OUT 8000 FO1 ltac:(lia)) ACO)).
assert (ACT5 : acc asegs m5 STEREO 24)
by (apply (acc_pres_fp_frame _ _ _ _ m m5 fh kh STEREO 24 PF (proj1 INFHK) FH8 FK8 ltac:(lia) FS1 ltac:(lia) (SHW STEREO 24 FS1 ltac:(lia)) ACST)).

assert (OUTIMGD : forall y, 65536 <= y < 6627328 -> outside (blocks_ivs LBD) y).
{ intros y Hy. apply outside_blocks_ivs. intros bk Hb Hin.
pose proof (live_facts RT AF Σ2 m5 _ _ ART (LIVED2 bk Hb)) as (_ & _ & IM & _). clear - IM Hy Hin. unfold SEGTOP_A in IM. lia. }
assert (SSP5 : io_ssp m5).
{ apply (sbd_io_ssp_agree m m5 SSP0 (AF_DRV Σ2 m5 ART)). intros a0 Ha. apply PF; [right; left; exact (sbd_ssp_static _ Ha)|].
unfold dec_W. cbn [outside]. unfold X00a.SSP_GUARD in Ha.
split; [clear - Ha FA1 FPIMG; unfold BITS_SIZEOF; lia|]. split; [clear - Ha FO1 FPIMG; lia|]. split; [clear - Ha FS1 FPIMG; lia|].
apply sb_outside_app; [apply OUTIMGD; lia|].
apply X000.outside_of_not_in_ranges'. intros Hin. apply (IO_ssp _ Hin). unfold X00a.SSP_GUARD. exact Ha. }
assert (IFA5 : in_frame_obj RT Σ2 m5 fh kh A BITS_SIZEOF) by (unfold BITS_SIZEOF; exact (conj FA1 (conj FA2 (conj ACA5 AAL)))).
assert (IFO5 : in_frame_obj RT Σ2 m5 fh kh OUT 8000) by (exact (conj FO1 (conj FO2 (conj ACO5 OAL)))).
assert (IFS5 : in_frame_obj RT Σ2 m5 fh kh STEREO 24) by (exact (conj FS1 (conj FS2 (conj ACT5 SAL)))).
pose proof (ctl_keeps_res low (CtlSetInnovationSave (0 + sbd_frame_size s))) as (RF1 & RC1 & RS1).
change (snd (speex_decoder_ctl low (CtlSetInnovationSave (0 + sbd_frame_size s)))) with low1 in RF1, RC1, RS1.
assert (FRM5 : (length (rt_frames RT Σ2) + dec_frames low1 <= FRAMES_MAX)%nat) by (rewrite EF2, RF1; cbn [length]; clear - FRM; lia).
assert (CRD5 : dec_credit low1 <= rt_credit RT Σ2) by (rewrite RC1; pose proof (dec_depth_pos low) as DP; clear - CRD CB2 DP; lia).
assert (LOR5 : lo + RT_STACK + dec_stack low1 <= usp + -608) by (rewrite RS1; clear - LOR; unfold RT_STACK; lia).

rewrite Spec.X1nu.evw_app.
eapply rz_conseq; [| apply t_eq_sym, t_emit_app].
refine (sbd_rz_dec RT Σ2 (PMfd F0 fs0) _ (p_err q) (p_err q1) bsl _ _ _ Hc0 EBSL _ _).
{ eapply (IHD low1 DKL1 Σ2 F0 fs0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 OUT STEREO (a_low a) A D LBL b lo fh PD NDs kh ows stb q q1 retl low2 b1 PRL);
cps_auto.
{ rewrite EU. exact POA1. } { rewrite EU. exact ST4. } }
intros cc6 (Σ3 & Hc6 & RNG6 & DEP6 & MOD6 & NEST6 & OWN6 & CHR6 & BSZ6 & LV6 & FRS6 & SP6 & CR6 & PO6).
cps_unpack_lib Hc6 as (m6 & ows6 & stb6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & RLOW6 & EXR6 & BREP6 & BOK6 & OC6 & LOWS6 & STB6 & ACA6 & ACO6 & ACT6 & ERR6 & OUTK6).
clear OC STB BOBJ BDAT BREP5 RLOW4 EXR ERR0 IFA5 IFO5 IFS5.
assert (OUTK7 : forall so, OUT_rep so m -> OUT_rep so m6) by (intros so H; exact (OUTK6 so (OUTK0 so H))). clear OUTK0 OUTK6.
clear Hc0.

assert (FPHI' : fh + fs_size kh <= SH_LO \/ SH_HI <= fh) by (clear - FPHI; unfold hid, SH_LO, SH_HI in *; lia).
assert (FFA' : fh + fs_size kh <= f \/ f + 64 <= fh) by (clear - FFA; unfold hid in FFA; exact FFA).
destruct (frame_live_apart RT AF Σ2 m5 fh kh S 160 ART INFH INL1) as (SFH & _).
assert (SIMG' : S + 160 <= 65536 \/ 6627328 <= S) by (clear - SIMG; unfold hid in SIMG; exact SIMG).
assert (OUTN : forall x, (x < fh \/ fh + fs_size kh <= x) -> outside (blocks_ivs LBL) x -> (x < 65536 \/ 6627328 <= x) ->
outside (dec_W IO_FP A OUT STEREO LBL) x).
{ intros x H1 H2 H3. unfold dec_W. cbn [outside]. split; [clear - H1 FA1 FA2; unfold BITS_SIZEOF; lia|]. split; [clear - H1 FO1 FO2; lia|].
split; [clear - H1 FS1 FS2; lia|]. apply sb_outside_app; [exact H2|]. apply (outside_img IO_FP x IO_img). clear - H3; unfold SEGTOP_A; lia. }
assert (AGB6 : agree_blocks asegs m5 m6 (tl (sb_blocks s S a))).
{ apply (agree_blocks_of_pres_fp RT Σ2 _ _ _ m5 m6 _ PRES6 WM6).
- intros bk Hb. apply LIVEA2. unfold LALL. apply in_app_iff. left. exact Hb.
- intros bk x Hb Hx. pose proof (LIVEA2 bk ltac:(unfold LALL; apply in_app_iff; left; exact Hb)) as LB.
destruct (frame_live_apart RT AF Σ2 m5 fh kh _ _ ART INFH LB) as (FA0 & _).
pose proof (live_facts RT AF Σ2 m5 _ _ ART LB) as (_ & _ & IM & _).
apply OUTN; [clear - FA0 Hx; lia | exact (APL bk x Hb Hx) | clear - IM Hx; unfold SEGTOP_A in IM; lia]. }
apply (sb_bufs_agree s S a j m5 m6) in BUFS; [| exact JOK | exact AGB6]. clear AGB6.
Time tr_fp PRES6 WM6 ltac:(fun x Hx => apply OUTN;
[ first [ clear - Hx BF1 LO608; lia | clear - Hx FFA'; lia | clear - Hx SFH; lia
| clear - Hx FPHI' SHF1 SHF2; unfold SH_LO, SH_HI in *; lia ]
| apply OUTB; first [ left; ulq0 | right; left; ulq0 | right; right; left; ulq0 | right; right; right; left; ulq0
| right; right; right; right; left; ulq0 | right; right; right; right; right; ulq0 ]
| first [ clear - Hx LO608 LOS; lia | clear - Hx FIMG; lia | clear - Hx SIMG'; lia | clear - Hx SHF1; lia ] ]).
assert (PF6 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp (dec_W IO_FP A OUT STEREO LBD) m m6).
{ apply (pres_fp_trans _ _ _ _ m m5 m6 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ2) (rt_frames RT Σ2) (usp + -608) _ m5 m6 PRES6).
- intros e He. rewrite EL2. exact He.
- intros e He. rewrite EF2. right. exact He.
- clear; lia.
- intros x Hx Ho. unfold dec_W in Ho |- *. cbn [outside] in Ho |- *. destruct Ho as (H1 & H2 & H3 & Ho).
apply sb_outside_app_inv in Ho. destruct Ho as [Hb Hio]. rewrite ELBD in Hb.
exact (conj H1 (conj H2 (conj H3 (sb_outside_app _ _ _ (outside_blocks_app_r _ _ x Hb) Hio)))). }
clear PF. rename PF6 into PF.
assert (SSP6 : io_ssp m6).
{ apply (sbd_io_ssp_agree m5 m6 SSP5 (AF_DRV Σ3 m6 ART6)). intros a0 Ha. apply PRES6; [right; left; exact (sbd_ssp_static _ Ha)|].
unfold dec_W. cbn [outside]. unfold X00a.SSP_GUARD in Ha.
split; [clear - Ha FA1 FPIMG; unfold BITS_SIZEOF; lia|]. split; [clear - Ha FO1 FPIMG; lia|]. split; [clear - Ha FS1 FPIMG; lia|].
apply sb_outside_app; [apply OUTIMG; lia|].
apply X000.outside_of_not_in_ranges'. intros Hin. apply (IO_ssp _ Hin). unfold X00a.SSP_GUARD. exact Ha. }
clear SSP5 PRES6 ART MI5 ST4.
cps_sigma LV6 FRS6 SP6.

destruct (af_acc_live RT AF Σ3 m6 S 160 ART6 INL1) as (_ & ACS6).
assert (OBS6 : aobj asegs m6 S 160) by (split; [lia|]; split; [ulc| exact ACS6]).
sb_unpack X as (HD & FST & PT & LE & SEED & CFG & IDC & PAD).
cps_seg (sbd_w4 usp S OUT f MODE s a).
{ clear - BS1 LO608 SPT. lia. }
destruct POST as (xa3' & ->).
clear HD FST PT LE SEED CFG IDC PAD OBS6 ACS6.

assert (EL3 : rt_live RT Σ3 = rt_live RT Σ) by congruence.
assert (EF3 : rt_frames RT Σ3 = (f, 0%nat) :: rt_frames RT Σ) by congruence.
assert (ES3 : rt_sp0 RT Σ3 = rt_sp0 RT Σ) by congruence.
assert (EP3 : rt_pois RT Σ3 = rt_pois RT Σ) by congruence.
assert (CB3 : rt_credit RT Σ - 1 - (Z.of_nat (dec_depth low) - 1) - dec_credit low <= rt_credit RT Σ3 <= rt_credit RT Σ - 1)
by (rewrite RC1 in CR6; clear - CB2 CR6; lia).
assert (LIVEL3 : forall x, In x LBL -> In (blk_addr x, blk_size x) (rt_live RT Σ3)) by (intros x Hx; rewrite EL3; exact (LIVEL x Hx)).
assert (LIVEA3 : forall x, In x LALL -> In (blk_addr x, blk_size x) (rt_live RT Σ3)) by (intros x Hx; rewrite EL3; exact (LIVEA x Hx)).
assert (LIVED3 : forall x, In x LBD -> In (blk_addr x, blk_size x) (rt_live RT Σ3)) by (intros x Hx; rewrite EL3; exact (LIVE x Hx)).
clear LV6 FRS6 SP6 CR6 PO6 EL2 EF2 ES2 EP2 CB2 LIVEA2 LIVEL2 LIVED2 FRM1 FRM5 CRD5.

assert (DL2 : dec_depth low2 = dec_depth low) by (rewrite DEP6; exact DL1).
destruct (dec_res_depth low2 low DL2) as (RS2' & RF2' & RC2' & RT2').
assert (DK2 : (dec_depth low2 <= k)%nat) by (rewrite DL2; exact DK).

unfold sb_fhdr in FRB3.
change [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x10d82); C8 (Z_to_bv 64 0xb67bc); CB 8 j24; C4 dtx0; CB 20 j36]
with ([C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x10d82); C8 (Z_to_bv 64 0xb67bc); CB 8 j24] ++ [C4 dtx0] ++ [CB 20 j36]) in FRB3.
apply rw_cells_app in FRB3. destruct FRB3 as (FH1 & FRB3). apply rw_cells_app in FRB3. destruct FRB3 as (FDT & FH3).
cbn [cells_size csize Nat.add app] in FDT, FH3. change (Z.of_nat 32) with 32 in FDT, FH3. change (Z.of_nat 4) with 4 in FH3.
pose proof (sbd_dtx_acc m6 f sf FRS3 Esf F64 ltac:(lia)) as ADT.
assert (DSTO : dst_obj RT Σ3 m6 (f + 32) 4) by (left; exists f, 0%nat; split; [exact INF|]; split; [lia|]; split; [change (fs_size 0) with 64; lia|];
split; [exact ADT| clear - F64; Z.div_mod_to_equations; lia]).
assert (FRM3 : (length (rt_frames RT Σ3) + dec_depth low2 <= FRAMES_MAX)%nat)
by (rewrite EF3, DL2; cbn [length]; pose proof (dec_depth_le_frames low) as DF; clear - FRM DF; lia).
assert (CRL3 : Z.of_nat (dec_depth low2) <= rt_credit RT Σ3 + 1)
by (rewrite DL2; pose proof (dec_credit_pos low) as DP; pose proof (dec_depth_pos low) as DP2; clear - CB3 CRD DP DP2; lia).
assert (LORC : lo + RT_STACK + ctl_stack low2 <= usp + -608)
by (rewrite RT2'; pose proof (ctl_stack_le_dec low) as CL; clear - LOR CL; unfold RT_STACK in *; lia).
cps_rt (IHC low2 DK2 Σ3 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 OUT OUT STEREO (a_low a) LBL CtlGetDtxStatus (f + 32) lo).
{ exists dtx0. exact FDT. } { rewrite EU. exact POA1. } { rewrite EU. exact ST6. }
intros cc7 (Σ4 & Hc7 & LV7 & FRS7 & SP7 & CR7 & PO7).
cps_unpack_lib Hc7 as (m7 & RS7 & (ART7 & MI7 & WM7 & ST7) & PRES7 & RLOW7 & CP7 & EXK7 & DST7).
cbn [creq_ivs creq_size app] in PRES7. cbn [creq_post] in CP7. destruct CP7 as (FDT7 & DTXV).
clear DST7 FDT DSTO ADT RLOW6 Hc0.
set (low3 := snd (speex_decoder_ctl low2 CtlGetDtxStatus)) in *.
set (dtx := fst (speex_decoder_ctl low2 CtlGetDtxStatus)) in *.
assert (EXR7 : retl = 0 -> EXCREADY m7 (a_low a) low3) by (intros E; exact (EXK7 (EXR6 E))). clear EXR6 EXK7.

assert (SFA' : S + 160 <= f \/ f + 64 <= S) by (clear - SFA; unfold hid in SFA; exact SFA).
assert (OFA' : OUT + 8000 <= f \/ f + 64 <= OUT) by (clear - OFA; unfold hid in OFA; exact OFA).
assert (AFA' : A + 48 <= f \/ f + 64 <= A) by (clear - AFA; unfold hid in AFA; exact AFA).
assert (TFA' : STEREO + 24 <= f \/ f + 64 <= STEREO) by (clear - TFA; unfold hid in TFA; exact TFA).
assert (BDF' : D + Z.of_nat (length bsb) <= f \/ f + 64 <= D) by (clear - BDF; unfold hid in BDF; exact BDF).
assert (SHF3' : f + 64 <= sf \/ sf + 8 <= f) by (clear - SHF3; unfold hid in SHF3; exact SHF3).
assert (FHI' : f + 64 <= SH_LO \/ SH_HI <= f) by (clear - FHI; unfold hid, SH_LO, SH_HI in *; lia).
assert (OUTB7 : forall x, (x < f + 32 \/ f + 36 <= x) -> outside (blocks_ivs LBL) x -> outside ((f + 32, f + 32 + 4) :: blocks_ivs LBL) x)
by (intros x H1 H2; cbn [outside]; split; [lia| exact H2]).
assert (AGB7 : agree_blocks asegs m6 m7 (tl (sb_blocks s S a))).
{ apply (agree_blocks_of_pres_fp RT Σ3 _ _ _ m6 m7 _ PRES7 WM7); [intros bk Hb; apply LIVEA3; unfold LALL; apply in_app_iff; left; exact Hb|].
intros bk x Hb Hx. apply OUTB7; [| exact (APL bk x Hb Hx)].
pose proof (BOUT2 bk x ltac:(unfold LALL; apply in_app_iff; left; exact Hb) Hx) as (H2 & _). clear - H2. lia. }
apply (sb_bufs_agree s S a j m6 m7) in BUFS; [| exact JOK | exact AGB7]. clear AGB7.
destruct BREP6 as ((rj6 & Lrj6 & BOBJ6) & (bs6 & BDAT6 & Hbs6) & BSIDE6). unfold bits_cells in BOBJ6. apply (proj1 (u8arr_rw_CB m6 D bs6)) in BDAT6.
assert (Lbs6 : Z.of_nat (length bs6) = sb_buf_size b1) by (pose proof BOK6 as OK'; unfold bits_ok in OK'; rewrite Hbs6, zlength_map_unsigned in OK'; clear - OK'; lia).
assert (BD6 : D + Z.of_nat (length bs6) <= PD + NDs) by (rewrite Lbs6, BSZ6; exact PD2).
assert (BDF6 : D + Z.of_nat (length bs6) <= f \/ f + 64 <= D) by (rewrite Lbs6, BSZ6, <- Lbsb; exact BDF').
pk_io_fp PRES7 ERR_rep OUT_rep IO_FP IO_img ltac:(fun y Hy => apply OUTB7; [clear - Hy FIMG; lia | apply OUTIMG; exact Hy]).
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
assert (LOWZ6 : Z.of_nat (length ows6) = 2000) by (rewrite LOWS6; reflexivity).
assert (CLF : forall x, fh <= x < fh + fs_size kh - 8 -> aclient (rt_live RT Σ3) (rt_frames RT Σ3) (usp + -608) x)
by (intros x Hx; right; right; right; left; exists fh, kh; split; [exact INFH| exact Hx]).
assert (CLS : forall x, usp + -608 <= x < usp -> aclient (rt_live RT Σ3) (rt_frames RT Σ3) (usp + -608) x)
by (intros x Hx; left; clear - Hx SPT; unfold USTACK_TOP in *; lia).
assert (CLL : forall p n x, In (p, n) (rt_live RT Σ3) -> p <= x < p + n -> aclient (rt_live RT Σ3) (rt_frames RT Σ3) (usp + -608) x)
by (intros p n x Hp Hx; right; right; left; exists p, n; split; [exact Hp| exact Hx]).
assert (CLF0 : forall x, f <= x < f + 56 -> aclient (rt_live RT Σ3) (rt_frames RT Σ3) (usp + -608) x)
by (intros x Hx; right; right; right; left; exists f, 0%nat; split; [exact INF| change (fs_size 0) with 64; lia]).
assert (CLSF : forall x, sf <= x < sf + 8 -> aclient (rt_live RT Σ3) (rt_frames RT Σ3) (usp + -608) x)
by (intros x Hx; right; right; right; right; exists f, 0%nat; split; [exact INF| change (fs_size 0) with 64; rewrite <- SHF, SHF0; lia]).
tr1 PRES7 WM7 OC6 ltac:(fun x Hx => apply CLF; clear - Hx FO1 FO2 LOWZ6; lia)
ltac:(fun x Hx => apply OUTB7; [clear - Hx OFA' LOWZ6; lia | apply OUTB; right; right; left; clear - Hx FO1 FO2 LOWZ6; lia]).
tr1 PRES7 WM7 STB6 ltac:(fun x Hx => apply CLF; clear - Hx FS1 FS2; lia)
ltac:(fun x Hx => apply OUTB7; [clear - Hx TFA'; lia | apply OUTB; right; right; left; clear - Hx FS1 FS2; lia]).
tr1 PRES7 WM7 BOBJ6 ltac:(fun x Hx => apply CLF; clear - Hx FA1 FA2; lia)
ltac:(fun x Hx => apply OUTB7; [clear - Hx AFA'; lia | apply OUTB; right; right; left; clear - Hx FA1 FA2; lia]).
tr1 PRES7 WM7 BDAT6 ltac:(fun x Hx => apply (CLL PD NDs x INPD); clear - Hx PD1 BD6; lia)
ltac:(fun x Hx => apply OUTB7; [clear - Hx BDF6; lia | apply OUTB; right; right; right; left; clear - Hx PD1 BD6; lia]).
tr1 PRES7 WM7 FR5 ltac:(fun x Hx => apply CLS; clear - Hx; lia)
ltac:(fun x Hx => apply OUTB7; [clear - Hx BF LO608; lia | apply OUTB; left; clear - Hx LO608; lia]).
tr1 PRES7 WM7 SV1 ltac:(fun x Hx => apply CLS; clear - Hx; lia)
ltac:(fun x Hx => apply OUTB7; [clear - Hx BF LO608; lia | apply OUTB; left; clear - Hx LO608; lia]).
tr1 PRES7 WM7 X ltac:(fun x Hx => apply (CLL S 160 x INL1); clear - Hx; lia)
ltac:(fun x Hx => apply OUTB7; [clear - Hx SFA'; lia | apply OUTB; right; left; clear - Hx; lia]).
tr1 PRES7 WM7 FH1 ltac:(fun x Hx => apply CLF0; clear - Hx; lia)
ltac:(fun x Hx => apply OUTB7; [clear - Hx; lia | apply OUTB; right; right; right; right; left; clear - Hx; lia]).
tr1 PRES7 WM7 FH3 ltac:(fun x Hx => apply CLF0; clear - Hx; lia)
ltac:(fun x Hx => apply OUTB7; [clear - Hx; lia | apply OUTB; right; right; right; right; left; clear - Hx; lia]).
tr1 PRES7 WM7 FRS3 ltac:(fun x Hx => apply CLSF; clear - Hx; lia)
ltac:(fun x Hx => apply OUTB7; [clear - Hx SHF3'; lia | apply OUTB; right; right; right; right; right; clear - Hx; lia]).

assert (PF7 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp (dec_W IO_FP A OUT STEREO LBD) m m7).
{ apply (pres_fp_trans _ _ _ _ m m6 m7 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ3) (rt_frames RT Σ3) (usp + -608) _ m6 m7 PRES7).
- intros e He. rewrite EL3. exact He.
- intros e He. rewrite EF3. right. exact He.
- clear; lia.
- intros x Hx Ho. cbn [outside]. split; [destruct (NAF x Hx) as (N1 & _); clear - N1; lia|].
unfold dec_W in Ho. cbn [outside] in Ho. destruct Ho as (_ & _ & _ & Ho). apply sb_outside_app_inv in Ho. destruct Ho as [Ho _].
rewrite ELBD in Ho. exact (outside_blocks_app_r _ _ x Ho). }
clear PF. rename PF7 into PF.
assert (SHW7 : forall o n, fh <= o -> o + n <= fh + fs_size kh -> forall i, 0 <= i < n -> outside ((f + 32, f + 32 + 4) :: blocks_ivs LBL) (shad (o + i))).
{ intros o n H1 H2 i Hi.
assert (SR : SH_LO <= shad (o + i) < SH_HI).
{ pose proof (frame_facts RT AF Σ3 m6 fh kh ART6 INFH) as (_ & _ & _ & _ & _ & _ & SA & SL & SH & _). split.
- unfold shad, SH_LO, SHB in *. assert (0 <= (o + i) / 8) by (apply Z.div_pos; lia). lia.
- assert (shad (o + i) < shad (fh + fs_size kh)); [| lia].
unfold shad. apply Z.add_lt_mono_r. apply Z.div_lt_upper_bound; [lia|].
assert (E : fh + fs_size kh = 8 * ((fh + fs_size kh) / 8)).
{ pose proof (Z.div_mod (fh + fs_size kh) 8 ltac:(lia)) as XD. rewrite Zplus_mod, FH8, FK8 in XD. cbn in XD. lia. }
lia. }
cbn [outside]. split; [clear - SR FHI'; unfold SH_LO, SH_HI in *; lia|].
exact (outside_blocks_shadow RT AF Σ3 m6 LBL _ ART6 LIVEL3 SR). }
assert (ACA7 : acc asegs m7 A 48)
by (apply (acc_pres_fp_frame _ _ _ _ m6 m7 fh kh A 48 PRES7 INFH FH8 FK8 ltac:(lia) FA1 ltac:(lia) (SHW7 A 48 FA1 ltac:(lia)) ACA6)).
assert (ACO7 : acc asegs m7 OUT 8000)
by (apply (acc_pres_fp_frame _ _ _ _ m6 m7 fh kh OUT 8000 PRES7 INFH FH8 FK8 ltac:(lia) FO1 ltac:(lia) (SHW7 OUT 8000 FO1 ltac:(lia)) ACO6)).
assert (ACT7 : acc asegs m7 STEREO 24)
by (apply (acc_pres_fp_frame _ _ _ _ m6 m7 fh kh STEREO 24 PRES7 INFH FH8 FK8 ltac:(lia) FS1 ltac:(lia) (SHW7 STEREO 24 FS1 ltac:(lia)) ACT6)).
assert (SSP7 : io_ssp m7).
{ apply (sbd_io_ssp_agree m6 m7 SSP6 (AF_DRV Σ4 m7 ART7)). intros a0 Ha. apply PRES7; [right; left; exact (sbd_ssp_static _ Ha)|].
unfold X00a.SSP_GUARD in Ha. apply OUTB7; [clear - Ha FIMG; lia | apply OUTIMG; lia]. }

assert (FRB7 : rw_cells asegs m7 f (sb_fhdr j24 (Z_to_bv 64 dtx) j36)).
{ unfold sb_fhdr.
change [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x10d82); C8 (Z_to_bv 64 0xb67bc); CB 8 j24; C4 (Z_to_bv 64 dtx); CB 20 j36]
with ([C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x10d82); C8 (Z_to_bv 64 0xb67bc); CB 8 j24] ++ [C4 (Z_to_bv 64 dtx)] ++ [CB 20 j36]).
apply rw_cells_app. split; [exact FH1|]. apply rw_cells_app. cbn [cells_size csize Nat.add]. change (Z.of_nat 32) with 32. change (Z.of_nat 4) with 4.
split; [exact FDT7| exact FH3]. }
clear FH1 FDT7 FH3 PRES7 ART6 MI6 ST6 ACA6 ACO6 ACT6 SSP6 SHW SHW7 OFFW.
cps_sigma LV7 FRS7 SP7.

assert (EL4 : rt_live RT Σ4 = rt_live RT Σ) by congruence.
assert (EF4 : rt_frames RT Σ4 = (f, 0%nat) :: rt_frames RT Σ) by congruence.
assert (ES4 : rt_sp0 RT Σ4 = rt_sp0 RT Σ) by congruence.
assert (EP4 : rt_pois RT Σ4 = rt_pois RT Σ) by congruence.
assert (CB4 : rt_credit RT Σ - 1 - 2 * (Z.of_nat (dec_depth low) - 1) - dec_credit low <= rt_credit RT Σ4 <= rt_credit RT Σ - 1)
by (rewrite DL2 in CR7; clear - CB3 CR7; lia).
assert (WMX : wmono asegs m m7) by (eapply wmono_trans; [exact WM1|]; eapply wmono_trans; [exact WM2|]; eapply wmono_trans; [exact WM3|];
eapply wmono_trans; [exact WM4|]; eapply wmono_trans; [exact WM5|]; eapply wmono_trans; [exact WM6| exact WM7]).
pose proof (proj1 ARTEK) as ARTE. pose proof (proj1 INFHK) as INFHE.
assert (POAE : pois_above (rt_pois RT Σ) usp) by (rewrite <- EP4; exact POA).
assert (INPDE : In (PD, NDs) (rt_live RT Σ)) by (rewrite <- EL4; exact INPD).
assert (LOWE : rt_sp0 RT Σ - STACK_WIN <= lo) by (rewrite <- ES4; exact LOW).
clear LV7 FRS7 SP7 CR7 PO7 EL3 EF3 ES3 EP3 CB3.
pose proof (ctl_keeps_mode_nest low2 CtlGetDtxStatus) as (MOD3 & NEST3'). change (snd (speex_decoder_ctl low2 CtlGetDtxStatus)) with low3 in MOD3, NEST3'.
assert (DL3 : dec_depth low3 = dec_depth low) by (unfold low3; rewrite ctl_keeps_depth; exact DL2).

destruct (Z.eq_dec retl 0) as [RZ | RNZ].
2: {
destruct (PNZ RNZ) as (-> & -> & -> & ->).
assert (EIV : inval = false) by (unfold inval; destruct (Z.eq_dec retl 0); [contradiction | reflexivity]).
rewrite EIV. apply rz_emit_nil.
cps_seg (sbd_w5x usp S OUT f MODE retl).
subst ms.
assert (REPX : DREP OUT STEREO m7 S (DecSB s low3) LBD).
{ cbn [decst_rep]. exists a, j, LBL. split; [exact ELBD|]. split; [exact S8|]. split; [exact SPOS|]. split; [exact INV|]. split; [exact JOK|].
split; [exact X|]. split; [exact BUFS|]. exists OUT. exact RLOW7. }
assert (BREPX : bits_rep asegs m7 A D b1).
{ split; [exists rj6; split; [exact Lrj6| unfold bits_cells; exact BOBJ6]|].
split; [exists bs6; split; [apply (proj2 (u8arr_rw_CB m7 D bs6)); exact BDAT6| exact Hbs6]| exact BSIDE6]. }
assert (PD2X : D + sb_buf_size b1 <= PD + NDs) by (rewrite BSZ6; exact PD2).
set (gx := fupds (fupds g1 [(51%nat, Z_to_bv 64 f); (45%nat, Z_to_bv 64 0); (26%nat, Z_to_bv 64 (S + 20)); (27%nat, Z_to_bv 64 ((S + 20) ≫ 3 + SHB));
(10%nat, Z_to_bv 64 (OUT + 4 * sbd_frame_size s))]) [(13%nat, Z_to_bv 64 sf)]) in *.
cps_rt (sbd_exit_cps RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AUN_lo AUN_nop Σ Σ4 F0 fs0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m m7 lo S OUT STEREO A D f fh PD NDs kh LBD gx 0 retl (DecSB s low3) b1 ows6 stb6 j24 j36 (Z_to_bv 64 dtx)
EF4 EL4 ES4 EP4 ARTE POAE NAF LIVE INPDE PD1 PD2X INFHE FA1 FA2 ACA FO1 FO2 ACO FS1 FS2 ACST ART7 MI7 RS7 ST7 LOWE
ltac:(clear - LOR DSP; unfold RT_STACK; lia) SPT SPA PF WMX FR5 ltac:(unfold gx; gslot) ltac:(unfold gx; cbn [fupds Nat.eqb]; exact G1_52)
(or_introl eq_refl) SV1 FRB7 FRS3 REPX (fun E => False_ind _ (RNZ E)) BREPX BOK6 OC6 LOWS6 STB6 ERR6 OUTK).
intros c' (Σ' & Hc' & E1 & E2 & E3 & E4 & E5).
apply Hk. exists Σ'. split; [exact Hc'|].
cbn [dec_depth dec_mode dec_nestedR dec_credit].
split; [clear - RNG6; lia|]. split; [rewrite DL3; reflexivity|]. split; [reflexivity|].
split; [cbn [dec_nestedR] in NEST; destruct NEST as (NM & _); split; [rewrite MOD3, MOD6; unfold low1; rewrite (proj1 (ctl_keeps_mode_nest low _)); exact NM | exact (NEST3' NEST6)]|].
split; [exact OWN6|]. split; [exact CHR6|]. split; [exact BSZ6|].
split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [| exact E5].
rewrite E4. pose proof (dec_depth_pos low) as DP. clear - CB4 DP. lia. }

rewrite RZ in Hc.
assert (EIB : (if inval then notify_bytes MSG_INVALID_MODE else []) = sbd_inv_bytes s b1)
by (unfold inval, sbd_inv_bytes; destruct (submode_at _ _); [reflexivity| destruct (sbw_id b1 =? 0); reflexivity]).
rewrite EIB.
assert (NMW : dec_mode low3 = sbm_nb_mode (sbd_mode s)).
{ cbn [dec_nestedR] in NEST. destruct NEST as (NM & _). rewrite MOD3, MOD6. unfold low1. rewrite (proj1 (ctl_keeps_mode_nest low _)). exact NM. }
assert (BREPW : bits_rep asegs m7 A D b1).
{ split; [exists rj6; split; [exact Lrj6| unfold bits_cells; exact BOBJ6]|].
split; [exists bs6; split; [apply (proj2 (u8arr_rw_CB m7 D bs6)); exact BDAT6| exact Hbs6]| exact BSIDE6]. }
refine (rz_cpsE RT Σ4 (PMfd F0 fs0) _ _ _ T cc7 Hc
(sbd_wph_cps RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img IO_ssp AF_DRV AF_ERRV AF_LIB FPL APO AUN_lo AUN_nop MEMS QMF16 LOST LOOP
Σ Σ4 F0 fs0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
m m7 lo S OUT STEREO A D f fh PD NDs kh LBD LBL
(fupds (fupds g1 [(51%nat, Z_to_bv 64 f); (45%nat, Z_to_bv 64 0); (26%nat, Z_to_bv 64 (S + 20)); (27%nat, Z_to_bv 64 ((S + 20) ≫ 3 + SHB));
(10%nat, Z_to_bv 64 (OUT + 4 * sbd_frame_size s))]) [(13%nat, Z_to_bv 64 sf)])
s a j low low3 b b1 ows6 stb6 j24 j36 dtx q1 q' ret d' b'
(PZ RZ) DL3 NMW (NEST3' NEST6) ltac:(clear - DEP; lia) OWN6 CHR6 BSZ6
(fun d E => IHC d ltac:(rewrite E; exact DK)) ELBD NDUP LAL8 S8 SPOS INV JOK ISV
EF4 EL4 ES4 EP4 CB4 CRD FRM ARTE POAE NAF LIVE INPDE PD1 ltac:(rewrite BSZ6; exact PD2) PDB INFHE
FA1 FA2 ACA AAL FO1 FO2 ACO OAL FS1 FS2 ACST SAL HAO HAS HOS FD2
LOWE ltac:(clear - LOR; unfold RT_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK; lia) SPT SPA
ART7 MI7 RS7 ST7 PF WMX FR5
ltac:(cbn [fupds Nat.eqb]; exact G1_0) ltac:(cbn [fupds Nat.eqb]; reflexivity) ltac:(cbn [fupds Nat.eqb]; reflexivity)
ltac:(cbn [fupds Nat.eqb]; reflexivity) ltac:(cbn [fupds Nat.eqb]; reflexivity) ltac:(cbn [fupds Nat.eqb]; exact G1_38)
ltac:(cbn [fupds Nat.eqb]; reflexivity) ltac:(cbn [fupds Nat.eqb]; reflexivity) ltac:(cbn [fupds Nat.eqb]; exact G1_52)
SV1 FRB7 DTXV FRS3 X BUFS RLOW7 (EXR7 RZ) BREPW BOK6 OC6 LOWS6 STB6 ACA7 ACO7 ACT7 ERR6 OUTK SSP7) _).
intros c' Hc'. apply Hk. exact Hc'.
Qed.
End SbDecodeCPS.
