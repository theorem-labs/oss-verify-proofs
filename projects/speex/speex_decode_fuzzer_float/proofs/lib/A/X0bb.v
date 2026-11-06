(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1df X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05q X05s X05u X05t
X081 X05l X05m X09f X06d X069 X082 X08y X0b1 X0b0 X05a X088.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0ba X0b8 X0b7 X0b9.

From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0yr X12b X0z5 X0wl X0wn X0wm X0ys X0x2 X0yt X0zq X11l X11k X0w7 X0yz.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0w7 X0yz.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X11w X11u X11t X11v.
Module B_TWIN.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X0j9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X09f OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X06d.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0z5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w7 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yz.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w7 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yz.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11u OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11v.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac simpl_sizes ::=
rewrite ?cells_size_sbp_hdr, ?cells_size_sbp_ptrs, ?cells_size_sbp_cfg, ?cells_size_sb_slots, ?app_length, ?cells_size_app, ?cells_size_f32, ?length_f32;
cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length, ?cells_size_f32, ?length_f32; cbn [length].

Section SBL.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.
Hypothesis APO : alloca_poison_contract RT.
Hypothesis AUN : allocas_unpoison_contract RT.
Hypothesis AUNlo : allocas_unpoison_lo_contract RT.
Hypothesis MEMS : memset_icontract RT e_asan_memset.
Hypothesis L2L8 : lsp_to_lpc_cps8 RT.
Hypothesis INNV : forall p, scb_params_ok p -> innov_unquant_cps RT (ptr := bptr) (InnovSplitCbShapeSignUnquant p).
Hypothesis DA : sblB_dA_stmt RT.

Lemma sblB_tr_live : forall (Σ : rts RT) frames sp W (m m' : mem) A cs p n,
rt_pres_fp (rt_live RT Σ) frames sp W m m' -> wmono bsegs m m' -> In (p, n) (rt_live RT Σ) ->
rw_cells bsegs m A cs -> p <= A -> A + Z.of_nat (cells_size cs) <= p + n ->
(forall x, p <= x < p + n -> outside W x) -> rw_cells bsegs m' A cs.
Proof.
intros Σ frames sp W m m' A cs p n PR WM IN H1 H2 H3 HO. apply (rw_cells_agree bsegs m m' A cs H1); [| exact WM].
intros a Ha. apply PR; [| apply HO; lia]. right; right; left. exists p, n. split; [exact IN| lia].
Qed.
Lemma sblB_tr_frame : forall (Σ : rts RT) live sp W (m m' : mem) A cs f k,
rt_pres_fp live (rt_frames RT Σ) sp W m m' -> wmono bsegs m m' -> In (f, k) (rt_frames RT Σ) ->
rw_cells bsegs m A cs -> f <= A -> A + Z.of_nat (cells_size cs) <= f + fs_size k - 8 ->
(forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells bsegs m' A cs.
Proof.
intros Σ live sp W m m' A cs f k PR WM IN H1 H2 H3 HO. apply (rw_cells_agree bsegs m m' A cs H1); [| exact WM].
intros a Ha. apply PR; [| apply HO; lia]. right; right; right; left. exists f, k. split; [exact IN| lia].
Qed.

Local Ltac sblB_trm H MU WM tac := let H' := fresh "T" in pose proof (rw_cells_transport bsegs _ _ _ _ _ H MU WM ltac:(cbn [disjoint_from]; simpl_sizes; tac)) as H'; clear H; rename H' into H.
Local Ltac sblB_trn H MU WM tac := let H' := fresh "T" in pose proof (rw_cells_transport bsegs _ _ _ _ _ H MU WM ltac:(cbn [disjoint_from]; tac)) as H'; clear H; rename H' into H.

Lemma sblB_subframe_uwb : forall (X : sbinv) (PMc : Model -> Prop) (mR : mem) (sub : Z) (b : bits_st bptr) (sm : submode),
fdfs_only PMc -> mat_stable PMc -> sb_ihyps X -> 0 <= sub < 4 ->
submode_at (sbm_submodes (sbd_mode (x_s X))) (sbd_submodeID (x_s X)) = Some sm ->
sbd_mode (x_s X) = ModeUWB ->
cps bsegs (at_LA RT X PMc mR sub b)
(fun c => (sub < 3 /\ at_LA RT X PMc mR (sub + 1) (sbsub_bits sm b) c) \/ (sub = 3 /\ at_TA RT X PMc mR sm (sbsub_bits sm b) c)).
Proof.
intros X PMc mR sub b sm FDO MST IH SUB SM EM T c Hc Hk.
destruct X as [usp lo gp S OUT A D s a bsz f sf fh kh PD ND live frames sp0 cr pois].
unfold at_LA, sb_loopmem, sb_sigma, sb_WL, sb_pois in Hc.
cbn [x_usp x_lo x_gp x_S x_OUT x_A x_D x_s x_a x_bsz x_f x_sf x_fh x_kh x_PD x_ND x_live x_frames x_sp0 x_cr x_pois] in Hc, IH, SM, Hk, EM.
destruct Hc as (Σ1 & Fx & fc & m & k & v & Hc & FRM & SIG & LM & V480).
destruct LM as (le & seed & pad1 & pad2 & lpi & ler & lq & liq & lak & vexc & voq & viq & vmsp & vpg & ver & ows & ART0 & MI0 & ST0 & PF & WM & SL
& LPIC & LLPI & LERC & LLER & LQC & LLQ & LIQC & LLIQ & LAKC & LLAK & PCS & LPAD1 & LPAD2 & EXBC & LEXB & OQC & LOQ & IQC & LIQ & MSPC & LMSP
& PGC & LPG & ERC & LER & OUTC & LOUT & BREP & BOK & BSZ & ACA & ACO).
destruct SIG as (SLIVE & SFRM & SSP0 & SCR & SPOIS).
destruct IH as [IU32 ITOP ILOW IROOM ISPOS ISAL IINV IISV IBLK INODUP IFH IA IOUT IAOUT ID IDBLK IPOIS ISF IAL].
cbn [x_usp x_lo x_gp x_S x_OUT x_A x_D x_s x_a x_bsz x_f x_sf x_fh x_kh x_PD x_ND x_live x_frames x_sp0 x_cr x_pois] in IU32, ITOP, ILOW, IROOM, ISPOS, ISAL, IINV, IISV, IBLK, INODUP, IFH, IA, IOUT, IAOUT, ID, IDBLK, IPOIS, ISF, IAL.
destruct IINV as (HMO & EFSZ & EFFS & EFS & ENSF & ELPC & HFIRST & HSR & HLE & HENC & HSID & HISV2).
destruct PCS as (HD & FST & PT & LEC & SEEDC & CFG & IDC & PAD2C).

assert (LIVB : forall x, In x (sb_blocks s S a) -> In (blk_addr x, blk_size x) (rt_live RT Σ1)) by (intros x Hx; rewrite SLIVE; exact (IBLK x Hx)).
assert (INL : In (S, 160) (rt_live RT Σ1)) by exact (LIVB (sbd_blk s, S, SBSTATE_SIZEOF) ltac:(cbn [sb_blocks In]; tauto)).
assert (INXB : In (a_exc a, 4 * sbd_subframeSize s) (rt_live RT Σ1)) by exact (LIVB (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s) ltac:(cbn [sb_blocks In]; tauto)).
assert (INOQ : In (a_oq a, 32) (rt_live RT Σ1)) by exact (LIVB (sbd_old_qlsp s, a_oq a, 32) ltac:(cbn [sb_blocks In]; tauto)).
assert (INIQ : In (a_iq a, 32) (rt_live RT Σ1)) by exact (LIVB (sbd_interp_qlpc s, a_iq a, 32) ltac:(cbn [sb_blocks In]; tauto)).
assert (INPG : In (a_pg a, 16) (rt_live RT Σ1)) by exact (LIVB (sbd_pi_gain s, a_pg a, 16) ltac:(cbn [sb_blocks In]; tauto)).
assert (INER : In (a_er a, 16) (rt_live RT Σ1)) by exact (LIVB (sbd_exc_rms s, a_er a, 16) ltac:(cbn [sb_blocks In]; tauto)).
assert (INMSP : In (a_msp a, 64) (rt_live RT Σ1)) by exact (LIVB (sbd_mem_sp s, a_msp a, 64) ltac:(cbn [sb_blocks In]; tauto)).
pose proof (af_sp0_win RT AF Σ1 m ART0) as SPW. rewrite SSP0 in SPW.
assert (LOWS : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SSP0; exact ILOW).
destruct (live_below_lo RT AF Σ1 m S 160 lo ART0 INL LOWS) as (_ & SBLO & LOSH).
pose proof (live_facts RT AF Σ1 m S 160 ART0 INL) as (_ & _ & SIMG & SSHD).
destruct (af_acc_live RT AF Σ1 m S 160 ART0 INL) as (_ & ACS).
assert (OBS : aobj bsegs m S 160) by (split; [lia|]; split; [clear - SBLO IROOM ITOP; unfold APP_TOP, USTACK_TOP, RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact ACS]).
pose proof (AF_LIB Σ1 m ART0) as LC0. pose proof (af_client_consts RT AF Σ1 m ART0) as CC0.
pose proof (fun a0 => aclient_split RT AF Σ1 m (usp + -1216) a0 ART0) as SPL.

destruct (live_below_lo RT AF Σ1 m _ _ lo ART0 INXB LOWS) as (XB0 & XBLO & _).
destruct (live_below_lo RT AF Σ1 m _ _ lo ART0 INOQ LOWS) as (OQ0 & OQLO & _).
destruct (live_below_lo RT AF Σ1 m _ _ lo ART0 INIQ LOWS) as (IQ0 & IQLO & _).
destruct (live_below_lo RT AF Σ1 m _ _ lo ART0 INPG LOWS) as (PG0 & PGLO & _).
destruct (live_below_lo RT AF Σ1 m _ _ lo ART0 INER LOWS) as (ER0 & ERLO & _).
destruct (live_below_lo RT AF Σ1 m _ _ lo ART0 INMSP LOWS) as (MS0 & MSLO & _).
assert (LOR2 : lo + 74848 <= usp + -1216) by (clear - IROOM; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in IROOM; lia).
assert (USPT : usp + 16 <= 140737488355328) by (clear - ITOP; unfold USTACK_TOP in ITOP; lia).
rewrite <- SLIVE, <- SFRM in PF.

destruct BREP as ((rjb & Lrjb & BOBJ) & (bsb & BDAT & Hbsb) & BSIDE). unfold bits_cells in BOBJ. apply (proj1 (sblB_u8arr_rw_CB m D bsb)) in BDAT.
assert (Lbsb : Z.of_nat (length bsb) = sb_buf_size b) by (pose proof BOK as OK'; unfold bits_ok in OK'; rewrite Hbsb, zlength_map_unsigned in OK'; clear - OK'; lia).
destruct ID as (IND & PD1 & PD2).
assert (INPD : In (PD, ND) (rt_live RT Σ1)) by (rewrite SLIVE; exact IND).
destruct (live_below_lo RT AF Σ1 m _ _ lo ART0 INPD LOWS) as (_ & PDLO & _).

assert (INFH0 : In (fh, kh) (rt_frames RT Σ1)) by (rewrite SFRM; right; exact IFH).
destruct (frame_below_lo RT AF Σ1 m fh kh lo ART0 INFH0 LOWS) as (FHLO & _ & _).
assert (ALO : A + 48 <= lo) by (clear - IA FHLO; unfold BITS_SIZEOF in IA; lia).
assert (OUTLO : OUT + 8000 <= lo) by (clear - IOUT FHLO; lia).
assert (DLO : D + Z.of_nat (length bsb) <= lo) by (clear - Lbsb BSZ PD2 PDLO; lia).
assert (IA' : fh <= A /\ A + 48 <= fh + fs_size kh - 8) by (clear - IA; unfold BITS_SIZEOF in IA; lia).

destruct (frame_live_apart RT AF Σ1 m fh kh S 160 ART0 INFH0 INL) as (SFA & _).
destruct (frame_live_apart RT AF Σ1 m fh kh _ _ ART0 INFH0 INXB) as (XBFA & _).
destruct (frame_live_apart RT AF Σ1 m fh kh _ _ ART0 INFH0 INOQ) as (OQFA & _).
destruct (frame_live_apart RT AF Σ1 m fh kh _ _ ART0 INFH0 INIQ) as (IQFA & _).
destruct (frame_live_apart RT AF Σ1 m fh kh _ _ ART0 INFH0 INPG) as (PGFA & _).
destruct (frame_live_apart RT AF Σ1 m fh kh _ _ ART0 INFH0 INER) as (ERFA & _).
destruct (frame_live_apart RT AF Σ1 m fh kh _ _ ART0 INFH0 INMSP) as (MSFA & _).
destruct (frame_live_apart RT AF Σ1 m fh kh _ _ ART0 INFH0 INPD) as (PDFA & _).

destruct HMO as [EMO | EMO]; [rewrite EM in EMO; discriminate EMO |]; pose proof EFS as EFS0; pose proof EFSZ as EFSZ0; rewrite EMO in EFS, EFSZ; cbn [sbm_subframeSize sbm_frameSize] in EFS, EFSZ.

-
assert (INFH : In (fh, kh) (rt_frames RT Σ1)) by (rewrite SFRM; right; exact IFH).
pose proof (frame_facts RT AF Σ1 m fh kh ART0 INFH) as (FH0 & FH64 & FHIMG & FHTOP & _).
assert (FSZK : 0 <= fs_size kh) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (OUTB : OUT + 8000 < 2 ^ 63) by (rewrite SSP0 in FHTOP; clear - IOUT FHTOP FSZK ILOW IROOM ITOP; unfold STACK_WIN, RT_STACK, SB_LOOP_STACK, INNOV_STACK, USTACK_TOP in *; lia).
cps_norm. cps_hide.

cps_seg (sblB_e1 usp lo S OUT A f sf (sbmode_struct (sbd_mode s)) (sbd_frame_size s) 80 384 sub v s a k gp (Z_to_bv 64 6524056) Fx fc m).
destruct POST as (m1 & jh & -> & MU1 & WM1 & MI1 & ST1 & SL1 & HULL1). clear SL.
change (Z.to_nat 384) with 384%nat in HULL1. replace (usp + -1216 - 384) with (usp + -1600) in * by lia.
cps_seg_post.

assert (RR1 : alloca_rr (usp + -1568) 320 = usp + -1216) by (unfold alloca_rr; clear - IU32; Z.div_mod_to_equations; lia).
assert (POA1 : pois_above (rt_pois RT Σ1) (usp + -1216)).
{ rewrite SPOIS. intros e He. apply in_app_iff in He. destruct He as [He|He].
- cbn [In] in He. unfold pz_lo. destruct He as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst]; lia.
- specialize (IPOIS e He). lia. }
cps_rt (APO Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (usp + -1568) 320 lo).
{ f_equal; lia. }
{ rewrite unsigned_lit by (clear - LOR2 USPT ILOW SPW; unfold STACK_WIN in *; lia). lia. }
{ rewrite RR1. exact POA1. }
{ rewrite SFRM; discriminate. }
{ cps_callok. }
intros c2 (Σ2 & Hc2 & PO2 & LV2 & FRS2 & SP2 & CR2).
cps_unpack Hc2 as (m2 & v2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ACX & ACT2).
pose proof LV2 as LVE2. pose proof FRS2 as FRE2. cps_sigma LV2 FRS2 SP2.
clear Hc0.

assert (HIS : sb_isave_ptr OUT s = 0 \/ sb_isave_ptr OUT s = OUT + 8 * sbd_frame_size s).
{ unfold sb_isave_ptr. destruct (sbd_innov_save s) as [kk|]; [right; rewrite IISV; lia| left; reflexivity]. }
assert (OUT0 : 0 < OUT) by (clear - IOUT FH0; lia).
cps_rt (sblB_dB RT AF MEMS Σ2 PMc usp lo (usp + -1600) S OUT A f sf (sbmode_struct (sbd_mode s)) (sbd_frame_size s) 80 sub fh kh _ s a ows).
{ destruct (af_acc_live RT AF Σ2 m2 S 160 ART2 INL) as (_ & ACS2). split; [lia|]. split; [clear - SBLO LOR2 USPT; unfold APP_TOP; lia| exact ACS2]. }
{ assert (OBO : aobj bsegs m OUT 8000) by (split; [lia|]; split; [clear - OUTLO LOR2 USPT; unfold APP_TOP; lia| exact ACO]).
assert (OFE1 : offsh [(usp + -5312, usp + -5304); (usp + -736, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; clear - LOR2 LOSH USPT; lia).
pose proof (aobj_munch bsegs _ m m1 OUT 8000 OBO MU1 (shfree_of_aobj bsegs _ m OUT 8000 OFE1 OBO)) as (_ & _ & ACO1).
apply (ACT2 OUT 8000 ACO1); [unfold USTACK_TOP; clear - OUTLO LOR2 USPT; lia| left; clear - OUTLO LOR2; lia]. }
{ cps_callok. }

intros c3 (Σ3 & Hc3 & LV3 & FRS3 & SP3 & CR3 & PO3).

destruct (ASTA_unpack RT Σ3 PMc _ c3 Hc3) as (ms3 & PO & Hc'); clear Hc3 Hc; cbv beta in PO.
destruct PO as (m3 & xra3 & xt03 & xt13 & xt23 & xa03 & xa13 & xa23 & xa33 & xa43 & xa53 & xa63 & xa73 & xs53 & xt33 & xt43 & xt53 & xt63 & F3 & fc3 & ows3 & -> & FRM3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & SL3 & OUTC3 & LOUT3).
clear SL1 OUTC.
pose proof (SFA : _ \/ _) as SFA'. pose proof (XBFA : _ \/ _) as XBFA'. pose proof (OQFA : _ \/ _) as OQFA'. pose proof (IQFA : _ \/ _) as IQFA'.
pose proof (PGFA : _ \/ _) as PGFA'. pose proof (ERFA : _ \/ _) as ERFA'. pose proof (MSFA : _ \/ _) as MSFA'. pose proof (PDFA : _ \/ _) as PDFA'. pose proof (IAOUT : _ \/ _) as IAOUT'.
let go H IN FA := apply (sblB_tr_live Σ2 _ _ _ m2 m3 _ _ _ _ PRES3 WM3 IN) in H;
[| lia | rewrite ?cells_size_sbp_hdr, ?cells_size_sbp_ptrs, ?cells_size_sbp_cfg, ?cells_size_f32; cbn [cells_size csize Nat.add]; lia
| intros x Hx; cbn [outside]; clear - FA Hx IOUT LOR2 SBLO XBLO OQLO IQLO PGLO ERLO MSLO PDLO; lia] in
go HD INL SFA'; go FST INL SFA'; go PT INL SFA'; go LEC INL SFA'; go SEEDC INL SFA'; go CFG INL SFA'; go IDC INL SFA'; go PAD2C INL SFA';
go EXBC INXB XBFA'; go OQC INOQ OQFA'; go IQC INIQ IQFA'; go MSPC INMSP MSFA'; go PGC INPG PGFA'; go ERC INER ERFA'.

assert (TRS : forall W Asp A0 cs, rt_pres_fp (rt_live RT Σ2) (rt_frames RT Σ2) Asp W m2 m3 ->
rw_cells bsegs m2 A0 cs -> Asp <= A0 -> A0 + Z.of_nat (cells_size cs) <= USTACK_TOP ->
(forall x, A0 <= x < A0 + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells bsegs m3 A0 cs).
{ intros W Asp A0 cs PR H1 H2 H3 HO. apply (rw_cells_agree bsegs m2 m3 A0 cs H1); [| exact WM3].
intros a0 Ha. apply PR; [left; lia | apply HO; lia]. }
let go H L := apply (TRS _ _ _ _ PRES3) in H;
[| lia | rewrite cells_size_f32; clear - L USPT; unfold USTACK_TOP; lia
| intros x Hx; rewrite cells_size_f32 in Hx; cbn [outside]; split; [|split; [|exact I]]; clear - Hx L OUTLO LOR2; lia] in
go LPIC LLPI; go LERC LLER; go LQC LLQ; go LIQC LLIQ; go LAKC LLAK.
apply (TRS _ _ _ _ PRES3) in HULL1;
[| lia | cbn [cells_size csize Nat.add]; clear - USPT; unfold USTACK_TOP; lia
| intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; split; [|split; [|exact I]]; clear - Hx OUTLO LOR2; lia].
apply (sblB_tr_live Σ2 _ _ _ m2 m3 _ _ _ _ PRES3 WM3 INPD) in BDAT;
[| exact PD1 | cbn [cells_size csize]; clear - PD2 BSZ Lbsb; lia
| intros x Hx; cbn [outside]; split; [|split; [|exact I]]; clear - Hx PDLO LOR2 PDFA' IOUT; lia].
apply (sblB_tr_frame Σ2 _ _ _ m2 m3 _ _ fh kh PRES3 WM3 INFH0) in BOBJ;
[| exact (proj1 IA') | cbn [cells_size csize Nat.add]; clear - IA'; lia
| intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; split; [|split; [|exact I]]; clear - Hx ALO LOR2 IAOUT'; unfold BITS_SIZEOF in *; lia].

assert (OFE1 : offsh [(usp + -5312, usp + -5304); (usp + -736, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; clear - LOR2 LOSH USPT; lia).
assert (ACO2 : acc bsegs m2 OUT 8000).
{ assert (OBO : aobj bsegs m OUT 8000) by (split; [lia|]; split; [clear - OUTLO LOR2 USPT; unfold APP_TOP; lia| exact ACO]).
pose proof (aobj_munch bsegs _ m m1 OUT 8000 OBO MU1 (shfree_of_aobj bsegs _ m OUT 8000 OFE1 OBO)) as (_ & _ & ACO1).
apply (ACT2 OUT 8000 ACO1); [unfold USTACK_TOP; clear - OUTLO LOR2 USPT; lia| left; clear - OUTLO LOR2; lia]. }
assert (ACA2 : acc bsegs m2 A 48).
{ assert (OBA : aobj bsegs m A 48) by (split; [lia|]; split; [clear - ALO LOR2 USPT; unfold APP_TOP; lia| exact ACA]).
pose proof (aobj_munch bsegs _ m m1 A 48 OBA MU1 (shfree_of_aobj bsegs _ m A 48 OFE1 OBA)) as (_ & _ & ACA1).
apply (ACT2 A 48 ACA1); [unfold USTACK_TOP; clear - ALO LOR2 USPT; lia| left; clear - ALO LOR2; lia]. }
assert (FH8 : fh mod 8 = 0) by (clear - FH64; Z.div_mod_to_equations; lia).
pose proof (fs_size_mod8 kh) as FK8.
pose proof (frame_facts RT AF Σ2 m2 fh kh ART2 INFH) as (_ & _ & _ & _ & _ & _ & FSA & FSL & FSU & FSS).

assert (SHF : forall o n, fh <= o -> o + n <= fh + fs_size kh -> forall i, 0 <= i < n -> SH_LO <= shad (o + i) < SH_HI
/\ (OUT + 8000 <= shad (o + i) \/ shad (o + i) < OUT)).
{ intros o n H1 H2 i Hi.
assert (B1 : shad fh <= shad (o + i)) by (unfold shad; apply Z.add_le_mono_r; apply Z.div_le_mono; lia).
assert (B2 : shad (o + i) < shad fh + fs_size kh / 8).
{ rewrite <- FSA. unfold shad. apply Z.add_lt_mono_r. apply Z.div_lt_upper_bound; [lia|].
assert (E : fh + fs_size kh = 8 * ((fh + fs_size kh) / 8))
by (pose proof (Z.div_mod (fh + fs_size kh) 8 ltac:(lia)) as XD; rewrite Zplus_mod, FH8, FK8 in XD; cbn in XD; lia).
lia. }
clear - B1 B2 FSL FSU FSS IOUT H1 H2 Hi. lia. }
assert (ACO3 : acc bsegs m3 OUT 8000).
{ apply (acc_pres_fp_frame _ _ _ _ m2 m3 fh kh OUT 8000 PRES3 INFH FH8 FK8 ltac:(lia) (proj1 IOUT) ltac:(lia)); [| exact ACO2].
intros i Hi. destruct (SHF OUT 8000 (proj1 IOUT) ltac:(lia) i Hi) as (S1 & S2). cbn [outside]. split; [|split; [|exact I]]; clear - S1 S2 LOR2 LOSH; unfold SH_LO, SH_HI in *; lia. }
assert (ACA3 : acc bsegs m3 A 48).
{ apply (acc_pres_fp_frame _ _ _ _ m2 m3 fh kh A 48 PRES3 INFH FH8 FK8 ltac:(lia) (proj1 IA') ltac:(lia)); [| exact ACA2].
intros i Hi. destruct (SHF A 48 (proj1 IA') ltac:(lia) i Hi) as (S1 & S2). cbn [outside]. split; [|split; [|exact I]]; clear - S1 S2 LOR2 LOSH; unfold SH_LO, SH_HI in *; lia. }

lazymatch type of PF with rt_pres_fp ?L ?Fr ?U ?W0 ?m0 m2 =>
assert (PF3 : rt_pres_fp L Fr U W0 m0 m3)
by (apply (pres_fp_trans _ _ _ _ m0 m2 m3 PF);
apply (pres_fp_of_pres_fp _ _ _ _ _ _ _ _ m2 m3 PRES3); [intros e He; rewrite LVE2; exact He | intros e He; rewrite FRE2; exact He | lia |];
intros x _ Ho; cbn [outside] in Ho |- *; decompose [and] Ho; split; [assumption | split; [assumption | exact I]]) end.
clear PF. rename PF3 into PF.
pose proof (wmono_trans bsegs _ _ _ (wmono_trans bsegs _ _ _ (wmono_trans bsegs _ _ _ WM WM1) WM2) WM3) as WMR. clear WM WM1 WM2 WM3.
clear ST2 ART2 MI2 PRES2 ACX ACT2 MU1 PRES3 ACO2 ACA2 ACA ACO TRS OBS ACS.
pose proof LV3 as LVE3. pose proof FRS3 as FRE3. cps_sigma LV3 FRS3 SP3.

assert (ACCM : forall W (mA mB : mem) o n, acc bsegs mA o n -> munch W mA mB -> offsh W -> 0 <= o -> o + n <= APP_TOP -> acc bsegs mB o n).
{ intros W mA mB o n H MU OF H0 H1. assert (OB : aobj bsegs mA o n) by (split; [exact H0| split; [exact H1| exact H]]).
exact (proj2 (proj2 (aobj_munch bsegs W mA mB o n OB MU (shfree_of_aobj bsegs W mA o n OF OB)))). }
assert (ACCF : forall live frames sp W (mA mB : mem) o n, rt_pres_fp live frames sp W mA mB -> In (fh, kh) frames ->
(forall x, SH_LO <= x < SH_HI -> outside W x) -> fh <= o -> o + n <= fh + fs_size kh -> acc bsegs mA o n -> acc bsegs mB o n).
{ intros live0 frames0 sp W mA mB o n PR IN HW H1 H2 H. apply (acc_pres_fp_frame _ _ _ _ mA mB fh kh o n PR IN FH8 FK8 ltac:(lia) H1 H2); [| exact H].
intros i Hi. apply HW. exact (proj1 (SHF o n H1 H2 i Hi)). }
assert (ACCX : forall live frames sp d nd (mA mB : mem) o n, rt_pres_ex live frames sp d nd mA mB -> In (fh, kh) frames ->
(d + nd <= SH_LO \/ SH_HI <= d) -> fh <= o -> o + n <= fh + fs_size kh -> o + n <= APP_TOP -> acc bsegs mA o n -> acc bsegs mB o n).
{ intros live0 frames0 sp d nd mA mB o n PR IN HDX H1 H2 H3 H. exact (acc_pres_ex_frame _ _ _ _ _ mA mB fh kh o n PR IN FH8 FK8 ltac:(lia) H1 H2 H3 HDX H). }

assert (TRSK : forall live frames sp W (mA mB : mem) A0 cs, rt_pres_fp live frames sp W mA mB -> wmono bsegs mA mB ->
rw_cells bsegs mA A0 cs -> sp <= A0 -> A0 + Z.of_nat (cells_size cs) <= USTACK_TOP ->
(forall x, A0 <= x < A0 + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells bsegs mB A0 cs).
{ intros live0 frames0 sp W mA mB A0 cs PR WMx H1 H2 H3 HO. apply (rw_cells_agree bsegs mA mB A0 cs H1); [| exact WMx].
intros a0 Ha. apply PR; [left; lia | apply HO; lia]. }

destruct IAL as (AG0 & AG1 & AXB & AOQ & AIQ & AMSP & APG & AER).
assert (OQ4 : a_oq a mod 4 = 0) by (clear - AOQ; Z.div_mod_to_equations; lia).
assert (SOFF : S + 160 <= SH_LO \/ SH_HI <= S) by (clear - SSHD; unfold hid, SH_LO, SH_HI in *; lia).
assert (OBS3 : aobj bsegs m3 S 160)
by (destruct (af_acc_live RT AF Σ3 m3 S 160 ART3 INL) as (_ & AC); split; [lia|]; split; [clear - SBLO LOR2 USPT; unfold APP_TOP; lia| exact AC]).
assert (OBOQ3 : aobj bsegs m3 (a_oq a) 32)
by (destruct (af_acc_live RT AF Σ3 m3 _ _ ART3 INOQ) as (_ & AC); split; [lia|]; split; [clear - OQLO LOR2 USPT; unfold APP_TOP; lia| exact AC]).
assert (INPQ : In (usp + -992, 32) (rt_pois RT Σ3)) by (rewrite PO3, PO2, SPOIS; right; right; right; left; reflexivity).
assert (INPIQ : In (usp + -1088, 32) (rt_pois RT Σ3)) by (rewrite PO3, PO2, SPOIS; right; right; left; reflexivity).
assert (INPAK : In (usp + -1184, 32) (rt_pois RT Σ3)) by (rewrite PO3, PO2, SPOIS; right; left; reflexivity).
assert (OBQ3 : aobj bsegs m3 (usp + -992) 32)
by (split; [lia|]; split; [clear - USPT; unfold APP_TOP; lia| exact (af_acc_pois RT AF Σ3 m3 _ _ ART3 INPQ)]).
assert (OBIQ3 : aobj bsegs m3 (usp + -1088) 32)
by (split; [lia|]; split; [clear - USPT; unfold APP_TOP; lia| exact (af_acc_pois RT AF Σ3 m3 _ _ ART3 INPIQ)]).
pose proof (af_client_consts RT AF Σ3 m3 ART3) as CC3.
cps_seg (sblB_e3 usp lo (usp + -1600) S OUT A f sf (sbmode_struct (sbd_mode s)) (sbd_frame_size s) 80 sub (a_oq a) _ s a voq lq liq).
destruct POST as (m4 & xt04 & xt14 & xt24 & xa44 & xa54 & xa64 & xa74 & xt34 & xt44 & xt54 & xt64 & F4 & fc4 & liq4 & -> & MU4 & WM4 & MI4 & ST4 & FRM4 & SL4 & LIQC4 & LLIQ4).
clear SL3 LIQC LLIQ FRM3 CC3 OBS3 OBOQ3 OBQ3 OBIQ3.
lazymatch type of MU4 with munch ?W _ _ => assert (OF4 : offsh W) by (cbn; unfold SH_LO, SH_HI; clear - LOR2 LOSH USPT; lia) end.
pose proof (ACCM _ m3 m4 A 48 ACA3 MU4 OF4 ltac:(lia) ltac:(clear - ALO LOR2 USPT; unfold APP_TOP; lia)) as ACA4.
pose proof (ACCM _ m3 m4 OUT 8000 ACO3 MU4 OF4 ltac:(lia) ltac:(clear - OUTLO LOR2 USPT; unfold APP_TOP; lia)) as ACO4.
clear ACA3 ACO3 OF4.
pose proof (wmono_trans bsegs _ _ _ WMR WM4) as WMR4.
clear WMR. rename WMR4 into WMR.

clear SFA' XBFA' OQFA' IQFA' PGFA' ERFA' MSFA' PDFA' IAOUT'.
cps_hide.
clear ST3 OFE1 CC0 LC0.
cps_seg_post.

rename ART into ART4. clear MU4 WM4.

assert (POA3 : pois_above (rt_pois RT Σ3) (usp + -1600)).
{ rewrite PO3, PO2. intros e [<-|He]; [unfold pz_lo; cbn [fst]; lia| specialize (POA1 e He); lia]. }
cps_rt (L2L8 Σ3 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F4 fc4 m4 (usp + -1088) (usp + -1184) lo liq4 lak).
{ rewrite FRE3, FRE2, SFRM; discriminate. }
{ rewrite unsigned_lit by (clear - LOR2 USPT ILOW SPW; unfold STACK_WIN in *; lia). exact POA3. }
{ rewrite unsigned_lit by (clear - LOR2 USPT ILOW SPW; unfold STACK_WIN in *; lia). exact ST4. }
{ rewrite unsigned_lit by (clear - LOR2 USPT ILOW SPW; unfold STACK_WIN in *; lia). clear - LOR2; unfold RT_STACK; lia. }
{ rewrite unsigned_lit by (clear - LOR2 USPT ILOW SPW; unfold STACK_WIN in *; lia). clear - USPT; unfold USTACK_TOP; lia. }
{ rewrite unsigned_lit by (clear - LOR2 USPT ILOW SPW; unfold STACK_WIN in *; lia). clear - IU32; Z.div_mod_to_equations; lia. }
intros c5 (Σ5 & Hc5 & LV5 & FRS5 & SP5 & CR5 & PO5).
cps_unpack_lib Hc5 as (v5 & m5 & aks5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5 & LAKC5 & LLAK5).
clear LAKC LLAK.
cps_tr_lib PRES5.

clear Hc.
lazymatch type of PF with rt_pres_fp ?L ?Fr ?U ?W0 ?m0 m4 =>
assert (PF5 : rt_pres_fp L Fr U W0 m0 m5)
by (apply (pres_fp_trans _ _ _ _ m0 m4 m5 PF);
apply (pres_fp_of_pres_fp _ _ _ _ _ _ _ _ m4 m5 PRES5); [intros e He; rewrite LVE3, LVE2; exact He | intros e He; rewrite FRE3, FRE2; exact He | lia |];
intros x _ Ho; cbn [outside] in Ho |- *; decompose [and] Ho; split; [intros Hin; match goal with H : ~ (usp + -1184 <= x < usp + -1152) |- _ => apply H; clear - Hin; lia end | exact I]) end.
clear PF. rename PF5 into PF.
assert (OFW5 : forall x, SH_LO <= x < SH_HI -> outside [(usp + -1184, usp + -1184 + 32)] x)
by (intros x Hx; cbn [outside]; split; [clear - Hx LOR2 LOSH USPT; unfold SH_LO, SH_HI in *; lia | exact I]).
pose proof (ACCF _ _ _ _ m4 m5 A 48 PRES5 INFH OFW5 (proj1 IA') ltac:(lia) ACA4) as ACA5.
pose proof (ACCF _ _ _ _ m4 m5 OUT 8000 PRES5 INFH OFW5 (proj1 IOUT) ltac:(lia) ACO4) as ACO5.
clear ACA4 ACO4 OFW5 PRES5.
pose proof (wmono_trans bsegs _ _ _ WMR WM5) as WMR5. clear WMR WM5. rename WMR5 into WMR.
pose proof LV5 as LVE5. pose proof FRS5 as FRE5. cps_sigma LV5 FRS5 SP5.

assert (LAP : forall p1 n1 p2 n2, In (p1, n1) (rt_live RT Σ5) -> In (p2, n2) (rt_live RT Σ5) -> p1 <> p2 -> p1 + n1 <= p2 \/ p2 + n2 <= p1).
{ intros p1 n1 p2 n2 H1 H2 NE. destruct (in_split _ _ H1) as (l1 & l2 & E).
apply (af_live_disj RT AF Σ5 m5 p1 n1 p2 n2 l1 l2 ART5 E). rewrite E in H2. apply in_app_iff in H2. apply in_app_iff.
destruct H2 as [H2|[H2|H2]]; [left; exact H2| exfalso; apply NE; congruence| right; exact H2]. }
assert (ND9 : List.NoDup [S; a_g0 a; a_g1 a; a_exc a; a_oq a; a_iq a; a_pg a; a_er a; a_msp a]) by exact INODUP.
apply List.NoDup_cons_iff in ND9 as [N0 ND9]. apply List.NoDup_cons_iff in ND9 as [_ ND9]. apply List.NoDup_cons_iff in ND9 as [_ ND9].
apply List.NoDup_cons_iff in ND9 as [N3 ND9]. apply List.NoDup_cons_iff in ND9 as [N4 ND9]. apply List.NoDup_cons_iff in ND9 as [N5 ND9].
apply List.NoDup_cons_iff in ND9 as [N6 ND9]. apply List.NoDup_cons_iff in ND9 as [N7 _].
assert (D_S_XB : S <> a_exc a) by (intros E; apply N0; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INL INXB D_S_XB) as AP_S_XB. clear D_S_XB.
assert (D_S_OQ : S <> a_oq a) by (intros E; apply N0; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INL INOQ D_S_OQ) as AP_S_OQ. clear D_S_OQ.
assert (D_S_IQ : S <> a_iq a) by (intros E; apply N0; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INL INIQ D_S_IQ) as AP_S_IQ. clear D_S_IQ.
assert (D_S_PG : S <> a_pg a) by (intros E; apply N0; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INL INPG D_S_PG) as AP_S_PG. clear D_S_PG.
assert (D_S_ER : S <> a_er a) by (intros E; apply N0; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INL INER D_S_ER) as AP_S_ER. clear D_S_ER.
assert (D_S_MS : S <> a_msp a) by (intros E; apply N0; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INL INMSP D_S_MS) as AP_S_MS. clear D_S_MS.
assert (D_XB_OQ : a_exc a <> a_oq a) by (intros E; apply N3; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INXB INOQ D_XB_OQ) as AP_XB_OQ. clear D_XB_OQ.
assert (D_XB_IQ : a_exc a <> a_iq a) by (intros E; apply N3; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INXB INIQ D_XB_IQ) as AP_XB_IQ. clear D_XB_IQ.
assert (D_XB_PG : a_exc a <> a_pg a) by (intros E; apply N3; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INXB INPG D_XB_PG) as AP_XB_PG. clear D_XB_PG.
assert (D_XB_ER : a_exc a <> a_er a) by (intros E; apply N3; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INXB INER D_XB_ER) as AP_XB_ER. clear D_XB_ER.
assert (D_XB_MS : a_exc a <> a_msp a) by (intros E; apply N3; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INXB INMSP D_XB_MS) as AP_XB_MS. clear D_XB_MS.
assert (D_OQ_IQ : a_oq a <> a_iq a) by (intros E; apply N4; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INOQ INIQ D_OQ_IQ) as AP_OQ_IQ. clear D_OQ_IQ.
assert (D_OQ_PG : a_oq a <> a_pg a) by (intros E; apply N4; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INOQ INPG D_OQ_PG) as AP_OQ_PG. clear D_OQ_PG.
assert (D_OQ_ER : a_oq a <> a_er a) by (intros E; apply N4; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INOQ INER D_OQ_ER) as AP_OQ_ER. clear D_OQ_ER.
assert (D_OQ_MS : a_oq a <> a_msp a) by (intros E; apply N4; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INOQ INMSP D_OQ_MS) as AP_OQ_MS. clear D_OQ_MS.
assert (D_IQ_PG : a_iq a <> a_pg a) by (intros E; apply N5; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INIQ INPG D_IQ_PG) as AP_IQ_PG. clear D_IQ_PG.
assert (D_IQ_ER : a_iq a <> a_er a) by (intros E; apply N5; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INIQ INER D_IQ_ER) as AP_IQ_ER. clear D_IQ_ER.
assert (D_IQ_MS : a_iq a <> a_msp a) by (intros E; apply N5; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INIQ INMSP D_IQ_MS) as AP_IQ_MS. clear D_IQ_MS.
assert (D_PG_ER : a_pg a <> a_er a) by (intros E; apply N6; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INPG INER D_PG_ER) as AP_PG_ER. clear D_PG_ER.
assert (D_PG_MS : a_pg a <> a_msp a) by (intros E; apply N6; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INPG INMSP D_PG_MS) as AP_PG_MS. clear D_PG_MS.
assert (D_ER_MS : a_er a <> a_msp a) by (intros E; apply N7; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INER INMSP D_ER_MS) as AP_ER_MS. clear D_ER_MS.
clear N0 N3 N4 N5 N6 N7.

destruct (live_facts RT AF Σ5 m5 _ _ ART5 INPG) as (_ & _ & PGIMG & PGSH).
destruct (live_facts RT AF Σ5 m5 _ _ ART5 INER) as (_ & _ & ERIMG & ERSH).
destruct (live_facts RT AF Σ5 m5 _ _ ART5 INXB) as (_ & _ & XBIMG & XBSH).
destruct (live_facts RT AF Σ5 m5 _ _ ART5 INIQ) as (_ & _ & IQIMG & IQSH).
destruct (live_facts RT AF Σ5 m5 _ _ ART5 INMSP) as (_ & _ & MSIMG & MSSH).
cps_hide.

rewrite <- PO5 in INPAK, INPQ, INPIQ.
assert (INPLP : In (usp + -800, 16) (rt_pois RT Σ5)) by (rewrite PO5, PO3, PO2, SPOIS; right; right; right; right; right; left; reflexivity).
destruct (af_acc_live RT AF Σ5 m5 S 160 ART5 INL) as (_ & ACS5).
assert (OBS5 : aobj bsegs m5 S 160) by (split; [lia|]; split; [clear - SBLO LOR2 USPT; unfold APP_TOP; lia| exact ACS5]).
destruct (af_acc_live RT AF Σ5 m5 _ _ ART5 INPG) as (_ & ACPG5).
assert (OBPG5 : aobj bsegs m5 (a_pg a) 16) by (split; [lia|]; split; [clear - PGLO LOR2 USPT; unfold APP_TOP; lia| exact ACPG5]).
assert (PG4 : a_pg a mod 4 = 0) by (clear - APG; Z.div_mod_to_equations; lia).
assert (PGOFF : a_pg a + 16 <= SH_LO \/ SH_HI <= a_pg a) by (clear - PGSH; unfold hid, SH_LO, SH_HI in *; lia).
pose proof (af_live_small RT AF Σ5 m5 _ _ ART5 INPG ltac:(lia)) as PGIMG5.
assert (PGIMG' : IMG_TOP_B <= a_pg a) by (clear - PGIMG5; unfold IMG_TOP_B, SEGTOP_A in *; lia).
pose proof (AP_S_PG : _ \/ _) as SPG.
assert (OBAK5 : aobj bsegs m5 (usp + -1184) 32)
by (split; [lia|]; split; [clear - USPT; unfold APP_TOP; lia| exact (af_acc_pois RT AF Σ5 m5 _ _ ART5 INPAK)]).
assert (OBLP5 : aobj bsegs m5 (usp + -800) 16)
by (split; [lia|]; split; [clear - USPT; unfold APP_TOP; lia| exact (af_acc_pois RT AF Σ5 m5 _ _ ART5 INPLP)]).
cps_seg (sblB_e4 usp lo (usp + -1600) S OUT A f sf (sbmode_struct (sbd_mode s)) (sbd_frame_size s) 80 sub (a_pg a) (usp + -1184) (usp + -800) _ s a vpg aks5 lpi).
destruct POST as (m6 & xt06 & xt16 & xt26 & xa36 & xa46 & xa56 & xa66 & xa76 & F6 & fc6 & vpg6 & -> & MU6 & WM6 & MI6 & FRM6 & SL6 & PGC6 & LPG6). clear SL4. rename SL6 into SL4.
clear PGC LPG SPG RS5 OBS5 OBPG5 OBAK5 OBLP5 ACS5 ACPG5 PGOFF PGIMG5 PG4.
lazymatch type of MU6 with munch ?W _ _ => assert (OF6 : offsh W) by (cbn; clear - PGSH LOR2 LOSH USPT; unfold hid, SH_LO, SH_HI in *; lia) end.
pose proof (ACCM _ m5 m6 A 48 ACA5 MU6 OF6 ltac:(lia) ltac:(clear - ALO LOR2 USPT; unfold APP_TOP; lia)) as ACA6.
pose proof (ACCM _ m5 m6 OUT 8000 ACO5 MU6 OF6 ltac:(lia) ltac:(clear - OUTLO LOR2 USPT; unfold APP_TOP; lia)) as ACO6.
clear ACA5 ACO5 OF6.
pose proof (wmono_trans bsegs _ _ _ WMR WM6) as WMR6. clear WMR. rename WMR6 into WMR.

pose proof (LAP _ _ _ _ INPD INPG ltac:(intros E; apply (IDBLK (sbd_pi_gain s, a_pg a, 16) ltac:(cbn [sb_blocks In]; tauto)); cbn [blk_addr fst snd]; congruence)) as AP_PD_PG.
assert (DPG : hid (D + Z.of_nat (length bsb) <= a_pg a \/ a_pg a + 16 <= D)) by (unfold hid in *; rewrite Lbsb, BSZ; clear - AP_PD_PG PD1 PD2; lia).
clear AP_PD_PG.
cps_seg_post.
rename ART into ART6. clear MU6 WM6.

apply (rw_cells_split_CB bsegs _ _ [] 384 _ [] [32; 320; 32]%nat) in HULL1; [| reflexivity]. cbn [mk_CB_cells app] in HULL1.
destruct (rw_cells_uncons bsegs _ _ _ _ HULL1) as (HLZ & HULL1'). destruct (rw_cells_uncons bsegs _ _ _ _ HULL1') as (HBODY & HRZ). clear HULL1 HULL1'.
cbn [csize] in HBODY, HRZ.
replace (usp + -1600 + Z.of_nat 32) with (usp + -1568) in HBODY, HRZ by lia.
replace (usp + -1568 + Z.of_nat 320) with (usp + -1248) in HRZ by lia.
destruct HBODY as [_ WRB]. cbn [cells_size csize Nat.add] in WRB. replace (Z.of_nat (320 + 0)) with 320 in WRB by lia.
assert (INPX : In (usp + -1568, 320) (rt_pois RT Σ5)) by (rewrite PO5, PO3, PO2; left; reflexivity).
cps_rt (MEMS Σ5 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 (usp + -1568) 320 z8 lo).
{ f_equal; lia. }
{ unfold checked_dst. rewrite unsigned_lit by (clear - LOR2 USPT ILOW SPW; unfold STACK_WIN in *; lia). split; [intros _; split|split].
- exact (af_acc_pois RT AF Σ5 m6 _ _ ART6 INPX).
- right; right; left. clear - LOWS LOR2 USPT; unfold STACK_WIN, USTACK_TOP in *; lia.
- intros i Hi. left. clear - Hi LOR2 USPT; unfold USTACK_TOP; lia.
- exact WRB. }
{ cps_callok. }
intros c7 Hc7.
cps_unpack Hc7 as (m7 & RS7 & (ART7 & MI7 & WM7 & ST7) & PRES7 & BYZ).
clear Hc.
pres_transport_g PRES7 ltac:(ulc).
lazymatch type of PF with rt_pres_fp ?L ?Fr ?U ?W0 ?m0 m6 =>
assert (PF7 : rt_pres_fp L Fr U W0 m0 m7)
by (apply (pres_fp_trans _ _ _ _ m0 m6 m7 PF);
apply (pres_fp_of_pres_ex_gen _ _ _ _ _ _ _ _ _ m6 m7 PRES7); [intros e He; rewrite LVE5, LVE3, LVE2; exact He | intros e He; rewrite FRE5, FRE3, FRE2; exact He | lia |];
intros x Hx _ Hd; pose proof (SPL x Hx) as SX; clear - SX Hd SSP0 ILOW LOR2; lia) end.
clear PF. rename PF7 into PF.
assert (DOFF : usp + -1568 + 320 <= SH_LO \/ SH_HI <= usp + -1568) by (right; clear - LOR2 LOSH; unfold SH_HI in *; lia).
pose proof (ACCX _ _ _ _ _ m6 m7 A 48 PRES7 INFH DOFF (proj1 IA') ltac:(lia) ltac:(clear - ALO LOR2 USPT; unfold APP_TOP; lia) ACA6) as ACA7.
pose proof (ACCX _ _ _ _ _ m6 m7 OUT 8000 PRES7 INFH DOFF (proj1 IOUT) ltac:(lia) ltac:(clear - OUTLO LOR2 USPT; unfold APP_TOP; lia) ACO6) as ACO7.
assert (EXV : exists ws, length ws = 80%nat /\ rw_cells bsegs m7 (usp + -1568) (f32 ws)).
{ apply (rw_cells_CB_f32 bsegs m7 _ 80 (repeat z8 (Z.to_nat 320))).
split; [split; [split; [cbn [cell_wf]; rewrite repeat_length; reflexivity| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BYZ]|].
cbn [cells_size csize Nat.add]. exact (wr_at_transport bsegs m6 m7 _ _ WRB WM7). }
destruct EXV as (ex7 & LEX7 & EXC7).
pose proof (wmono_trans bsegs _ _ _ WMR WM7) as WMR7. clear WMR. rename WMR7 into WMR.
clear DOFF ACA6 ACO6 PRES7 WM7 WRB BYZ ST5 ART6 MI6.

assert (BREP7 : bits_rep bsegs m7 A D b).
{ split; [exists rjb; split; [exact Lrjb| unfold bits_cells; exact BOBJ]|].
split; [exists bsb; split; [apply (proj2 (sblB_u8arr_rw_CB m7 D bsb)); exact BDAT| exact Hbsb]| exact BSIDE]. }
clear BOBJ BDAT.
assert (A4 : A mod 4 = 0) by (destruct BSIDE as (A8 & _); clear - A8; Z.div_mod_to_equations; lia).
assert (PDS : PD <> S) by (intros E; apply (IDBLK (sbd_blk s, S, SBSTATE_SIZEOF) ltac:(cbn [sb_blocks In]; tauto)); cbn [blk_addr fst snd]; congruence).
assert (INPER : In (usp + -896, 16) (rt_pois RT Σ5)) by (rewrite PO5, PO3, PO2, SPOIS; right; right; right; right; left; reflexivity).
assert (INPX5 : In (usp + -1600 + 32, 4 * 80) (rt_pois RT Σ5)) by (rewrite PO5, PO3, PO2; left; f_equal; lia).
assert (FRN5 : rt_frames RT Σ5 <> []) by (rewrite FRE5, FRE3, FRE2, SFRM; discriminate).
replace (usp + -1568) with (usp + -1600 + 32) in EXC7 by lia.
assert (FA1 : fh <= A) by (clear - IA; tauto). assert (FA2 : A + BITS_SIZEOF <= fh + fs_size kh - 8) by (clear - IA; tauto).
cps_rt (DA Σ5 PMc usp lo (usp + -1600) S OUT A D f sf (sbmode_struct (sbd_mode s)) (sbd_frame_size s) 80 sub fh PD ND kh
_ s a b sm pad1 seed ex7 ows3 ler _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m7
FDO MST FRM6 SL4 V480 eq_refl eq_refl HD SEEDC CFG IDC EFS eq_refl HSID (or_intror (conj EMO (conj eq_refl (conj EFSZ eq_refl)))) eq_refl SM SUB INL ISAL
BREP7 BOK INFH FA1 FA2 A4 ACA7 INPD PD1 ltac:(rewrite BSZ; exact PD2) PDS LERC LLER INPER
OUTC3 LOUT3 (proj1 IOUT) (proj1 (proj2 IOUT)) (proj2 (proj2 IOUT)) ACO7 IAOUT EXC7 ltac:(clear - LEX7; lia) INPX5 POA3 FRN5
ART7 MI7 ST7 LOWS IROOM IU32 USPT eq_refl).
intros c10 (Σ10 & Hc10 & LV10 & FRS10 & SP10 & CR10 & PO10).
destruct (ASTA_unpack RT Σ10 PMc _ c10 Hc10) as (ms10 & PO & Hc'); clear Hc10; cbv beta in PO.
destruct PO as (m10 & xra10 & xt010 & xt110 & xt210 & xa010 & xa110 & xa210 & xa310 & xa410 & xa510 & xa610 & xa710 & xs210 & xs510 & xs910 & xs1010 & xt310 & xt510
& F10 & fc10 & v10 & seed10 & ex10 & -> & FRM10 & (ART10 & MI10 & WM10 & ST10) & PRES10 & SL10 & V480b & V544b & V288b & V392b & V456b
& SEEDC10 & EXC10 & LEX10 & REP10 & OK10 & ACA10).
clear SL4 SEEDC EXC7 LEX7 BREP7 ACA7 FRM6 Hc0.
assert (IAOUTh : hid (A + BITS_SIZEOF <= OUT \/ OUT + 8000 <= A)) by (unfold hid; unfold hidp in IAOUT; exact IAOUT).
pres_transport_g PRES10 ltac:(ulc).
lazymatch type of PF with rt_pres_fp ?L ?Fr ?U ?W0 ?m0 m7 =>
assert (PF10 : rt_pres_fp L Fr U W0 m0 m10)
by (apply (pres_fp_trans _ _ _ _ m0 m7 m10 PF);
apply (pres_fp_of_pres_fp _ _ _ _ _ _ _ _ m7 m10 PRES10); [intros e He; rewrite LVE5, LVE3, LVE2; exact He | intros e He; rewrite FRE5, FRE3, FRE2; exact He | lia |];
intros x Hx Ho; cbn [outside] in Ho |- *; decompose [and] Ho; pose proof (SPL x Hx) as SX;
split; [assumption|]; split; [assumption|]; split; [assumption|];
split; [intros Hin; clear - SX Hin SSP0 ILOW LOR2; lia | exact I]) end.
clear PF. rename PF10 into PF.
pose proof (frame_facts RT AF Σ5 m7 fh kh ART7 INFH) as (_ & _ & _ & _ & FHSH5 & _).
assert (AOFF : A + 48 <= SH_LO \/ SH_HI <= A) by (clear - FHSH5 FA1 FA2; unfold SH_LO, SH_HI, BITS_SIZEOF in *; lia).
assert (OOFF : OUT + 8000 <= SH_LO \/ SH_HI <= OUT) by (clear - FHSH5 IOUT; unfold SH_LO, SH_HI in *; lia).
assert (OFW10 : forall x, SH_LO <= x < SH_HI -> outside [(usp + -736, usp + -160); (S + 132, S + 136); (A, A + BITS_SIZEOF); (usp + -1600 + 32, usp + -1600 + 32 + 4 * 80)] x).
{ intros x Hx. cbn [outside]. unfold hid in SSHD.
split; [clear - Hx LOR2 LOSH USPT; unfold SH_LO, SH_HI in *; lia|]. split; [clear - Hx SSHD; unfold SH_LO, SH_HI in *; lia|].
split; [clear - Hx AOFF; unfold BITS_SIZEOF; lia|]. split; [clear - Hx LOR2 LOSH USPT; unfold SH_LO, SH_HI in *; lia| exact I]. }
pose proof (ACCF _ _ _ _ m7 m10 OUT 8000 PRES10 INFH OFW10 (proj1 IOUT) ltac:(lia) ACO7) as ACO10.
clear OFW10 ACO7 PRES10 FHSH5.
pose proof (wmono_trans bsegs _ _ _ WMR WM10) as WMR10. clear WMR WM10. rename WMR10 into WMR.
clear ST7 ART7 MI7.
pose proof LV10 as LVE10. pose proof FRS10 as FRE10. cps_sigma LV10 FRS10 SP10.
cps_hide.

assert (BRT : forall W (mA mB : mem) (bb : bits_st bptr), bits_rep bsegs mA A D bb -> munch W mA mB -> wmono bsegs mA mB -> bits_ok bb -> sb_buf_size bb = bsz ->
disjoint_from W A 48 -> disjoint_from W D bsz -> bits_rep bsegs mB A D bb).
{ intros W mA mB bb ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE) MU WMx OKb SZb DAx DD.
assert (LB : Z.of_nat (length bs) = bsz) by (pose proof OKb as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; clear - OK' SZb; lia).
split; [exists rj; split; [exact Lrj|]|]; [| split; [exists bs; split; [|exact Hbs]| exact SIDE]].
- apply (rw_cells_transport bsegs W mA mB A _ OBJ MU WMx). unfold bits_cells. cbn [cells_size csize Nat.add]. exact DAx.
- apply (proj1 (sblB_u8arr_rw_CB mA D bs)) in DAT. apply (proj2 (sblB_u8arr_rw_CB mB D bs)).
apply (rw_cells_transport bsegs W mA mB D _ DAT MU WMx). cbn [cells_size csize]. rewrite Nat.add_0_r, LB. exact DD. }
assert (BRTP : forall live frames sp (mA mB : mem) (bb : bits_st bptr), rt_pres live frames sp mA mB -> wmono bsegs mA mB -> In (fh, kh) frames -> In (PD, ND) live ->
bits_rep bsegs mA A D bb -> bits_ok bb -> sb_buf_size bb = bsz -> bits_rep bsegs mB A D bb).
{ intros live0 frames0 sp mA mB bb PR WMx INF INP ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE) OKb SZb.
assert (LB : Z.of_nat (length bs) = bsz) by (pose proof OKb as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; clear - OK' SZb; lia).
split; [exists rj; split; [exact Lrj|]|]; [| split; [exists bs; split; [|exact Hbs]| exact SIDE]].
- apply (rw_cells_agree bsegs mA mB A _ OBJ); [| exact WMx]. intros x Hx. apply PR. unfold bits_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
right; right; right; left. exists fh, kh. split; [exact INF|]. clear - Hx IA. unfold BITS_SIZEOF in *. lia.
- apply (proj1 (sblB_u8arr_rw_CB mA D bs)) in DAT. apply (proj2 (sblB_u8arr_rw_CB mB D bs)).
apply (rw_cells_agree bsegs mA mB D _ DAT); [| exact WMx]. intros x Hx. apply PR. cbn [cells_size csize] in Hx. rewrite Nat.add_0_r, LB in Hx.
right; right; left. exists PD, ND. split; [exact INP|]. clear - Hx PD1 PD2. lia. }

destruct (af_acc_live RT AF Σ10 m10 S 160 ART10 INL) as (_ & ACS10).
assert (OBS10 : aobj bsegs m10 S 160) by (split; [lia|]; split; [clear - SBLO LOR2 USPT; unfold APP_TOP in *; lia| exact ACS10]).
assert (INPX10 : In (usp + -1600 + 32, 4 * 80) (rt_pois RT Σ10)) by (rewrite PO10; exact INPX5).
assert (OBEX10 : aobj bsegs m10 (usp + -1600 + 32) (4 * 80))
by (split; [clear - LOR2 LOSH; lia|]; split; [clear - USPT; unfold APP_TOP in *; lia| exact (af_acc_pois RT AF Σ10 m10 _ _ ART10 INPX10)]).
assert (OIMG : IMG_TOP_B <= OUT) by (clear - FHIMG IOUT; unfold IMG_TOP_B, SEGTOP_A in *; lia).
assert (SEPSO : S + 160 <= OUT \/ OUT + 8000 <= S) by (unfold hid in SFA; clear - SFA IOUT; lia).
cps_seg (sblB_e12a usp lo (usp + -1600) S OUT A f sf (sbmode_struct (sbd_mode s)) (sbd_frame_size s) 80 sub (usp + -1600 + 32) v10 s a ex10 ows3 xs210 xs510 xs910 xs1010 xra10
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F10 fc10 m10
SL10 HD EFS (or_intror (conj eq_refl EFSZ)) SUB PT HIS
OBS10 ISAL ISPOS SOFF SBLO EXC10 LEX10 OBEX10 ltac:(clear - IU32; Z.div_mod_to_equations; lia) ltac:(clear; lia)
OUTC3 LOUT3 ACO10 OUT0 (proj2 (proj2 IOUT)) OIMG OUTLO ltac:(clear - OUTLO LOR2 USPT; unfold APP_TOP in *; lia) OOFF SEPSO
ltac:(clear - LOR2; lia) ltac:(clear; lia) LOSH ltac:(clear - USPT; lia) MI10).
destruct POST as (m11 & xt011 & xt111 & xa011 & xa111 & xa211 & xa311 & xa411 & xa511 & xa611 & xa711 & F11 & ows11 & -> & MU11 & WM11 & MI11 & OUTC11 & LOUT11).
clear OUTC3 LOUT3 OBS10 ACS10 OBEX10.
destruct (sblB_sbsub_ok b sm (sbd_mode s) (sbd_submodeID s) BOK (or_intror EMO) HSID SM) as (_ & SZSB0).
assert (SZSB : sb_buf_size (sbsub_bits sm b) = bsz) by (rewrite SZSB0; exact BSZ).
assert (REP11 : bits_rep bsegs m11 A D (sbsub_bits sm b)).
{ apply (BRT _ m10 m11 _ REP10 MU11 WM11 OK10).
- exact SZSB.
- cbn [disjoint_from]. split; [| exact I]. unfold hidp, BITS_SIZEOF in IAOUT. clear - IAOUT. lia.
- cbn [disjoint_from]. split; [| exact I]. unfold hid in PDFA. clear - PDFA IOUT PD1 PD2. lia. }
clear REP10.
lazymatch type of MU11 with munch ?W _ _ => assert (OF11 : offsh W) by (cbn; unfold hid in OOFF; clear - OOFF; unfold SH_LO, SH_HI in *; lia) end.
pose proof (ACCM _ m10 m11 A 48 ACA10 MU11 OF11 ltac:(lia) ltac:(clear - ALO LOR2 USPT; unfold APP_TOP in *; lia)) as ACA11.
pose proof (ACCM _ m10 m11 OUT 8000 ACO10 MU11 OF11 ltac:(lia) ltac:(clear - OUTLO LOR2 USPT; unfold APP_TOP in *; lia)) as ACO11.
clear ACA10 ACO10 OF11.
pose proof (wmono_trans bsegs _ _ _ WMR WM11) as WMR11. clear WMR. rename WMR11 into WMR.
cps_seg_post.
rename ART into ART11. clear MU11 WM11.

assert (WINY : (Z.to_nat (320 + 80 * sub) + Z.to_nat 80 <= length ows11)%nat) by (rewrite LOUT11; clear - SUB; lia).
destruct (sblB_f32_win _ OUT ows11 _ _ OUTC11 WINY) as (OY1 & OY2 & OY3). clear OUTC11 WINY.
replace (OUT + 4 * Z.of_nat (Z.to_nat (320 + 80 * sub))) with (OUT + 4 * sbd_frame_size s + 4 * (80 * sub)) in OY2, OY3 by (rewrite EFSZ; clear - SUB; lia).
replace (OUT + 4 * sbd_frame_size s + 4 * (80 * sub) + 4 * Z.of_nat (Z.to_nat 80)) with (OUT + 4 * sbd_frame_size s + 4 * (80 * sub) + 4 * 80) in OY3 by lia.
assert (LY1 : Z.of_nat (length (firstn (Z.to_nat (320 + 80 * sub)) ows11)) = 320 + 80 * sub) by (rewrite length_firstn, LOUT11; clear - SUB; lia).
assert (LY2 : Z.of_nat (length (firstn (Z.to_nat 80) (skipn (Z.to_nat (320 + 80 * sub)) ows11))) = 80) by (rewrite length_firstn, length_skipn, LOUT11; clear - SUB; lia).
assert (LY3 : Z.of_nat (length (skipn (Z.to_nat (320 + 80 * sub) + Z.to_nat 80) ows11)) = 2000 - 320 - 80 * sub - 80)
by (rewrite length_skipn, LOUT11; clear - SUB; lia).
remember (firstn (Z.to_nat (320 + 80 * sub)) ows11) as y1 eqn:EY1.
remember (firstn (Z.to_nat 80) (skipn (Z.to_nat (320 + 80 * sub)) ows11)) as y2 eqn:EY2.
remember (skipn (Z.to_nat (320 + 80 * sub) + Z.to_nat 80) ows11) as y3 eqn:EY3.
clear EY1 EY2 EY3.
destruct (sblB_f32_win _ (a_msp a) vmsp 0 8 MSPC ltac:(rewrite LMSP; lia)) as (_ & MS2 & MS3). clear MSPC.
replace (a_msp a + 4 * Z.of_nat 0) with (a_msp a) in MS2, MS3 by lia. replace (a_msp a + 4 * Z.of_nat 8) with (a_msp a + 32) in MS3 by lia.
change (skipn 0 vmsp) with vmsp in MS2.
assert (LMS2 : length (firstn 8 vmsp) = 8%nat) by (rewrite length_firstn, LMSP; reflexivity).
assert (LMS3 : length (skipn (0 + 8) vmsp) = 8%nat) by (rewrite length_skipn, LMSP; reflexivity).
remember (firstn 8 vmsp) as vm8 eqn:EVM8. remember (skipn (0 + 8) vmsp) as vm8b eqn:EVM8B. clear EVM8 EVM8B.

assert (INPD5 : In (PD, ND) (rt_live RT Σ5)) by (rewrite <- LVE10; exact INPD).
assert (INXB5 : In (a_exc a, 4 * sbd_subframeSize s) (rt_live RT Σ5)) by (rewrite <- LVE10; exact INXB).
assert (INMS5 : In (a_msp a, 64) (rt_live RT Σ5)) by (rewrite <- LVE10; exact INMSP).
assert (INIQ5 : In (a_iq a, 32) (rt_live RT Σ5)) by (rewrite <- LVE10; exact INIQ).
assert (INER5 : In (a_er a, 16) (rt_live RT Σ5)) by (rewrite <- LVE10; exact INER).
pose proof (LAP _ _ _ _ INPD5 INXB5 ltac:(intros E; apply (IDBLK (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s) ltac:(cbn [sb_blocks In]; tauto)); cbn [blk_addr fst snd]; congruence)) as AP_PD_XB.
pose proof (LAP _ _ _ _ INPD5 INMS5 ltac:(intros E; apply (IDBLK (sbd_mem_sp s, a_msp a, 64) ltac:(cbn [sb_blocks In]; tauto)); cbn [blk_addr fst snd]; congruence)) as AP_PD_MS.
pose proof (LAP _ _ _ _ INPD5 INIQ5 ltac:(intros E; apply (IDBLK (sbd_interp_qlpc s, a_iq a, 32) ltac:(cbn [sb_blocks In]; tauto)); cbn [blk_addr fst snd]; congruence)) as AP_PD_IQ.
pose proof (LAP _ _ _ _ INPD5 INER5 ltac:(intros E; apply (IDBLK (sbd_exc_rms s, a_er a, 16) ltac:(cbn [sb_blocks In]; tauto)); cbn [blk_addr fst snd]; congruence)) as AP_PD_ER.
clear INPD5 INXB5 INMS5 INIQ5 INER5.

assert (YP4 : (OUT + 4 * sbd_frame_size s + 4 * (80 * sub)) mod 4 = 0)
by (replace (OUT + 4 * sbd_frame_size s + 4 * (80 * sub)) with (OUT + (sbd_frame_size s + 80 * sub) * 4) by ring; rewrite Z_mod_plus_full; exact (proj2 (proj2 IOUT))).
assert (OBY : aobj bsegs m11 (OUT + 4 * sbd_frame_size s + 4 * (80 * sub)) (4 * 80)).
{ split; [rewrite EFSZ; clear - OUT0 SUB; lia|]. split; [rewrite EFSZ; clear - OUTLO LOR2 USPT SUB; unfold APP_TOP in *; lia|].
apply (acc_sub bsegs m11 OUT 8000); [exact ACO11| rewrite EFSZ; clear - SUB; lia | rewrite EFSZ; clear - SUB; lia]. }
destruct (af_acc_live RT AF Σ10 m11 _ _ ART11 INXB) as (_ & ACXB). rewrite EFS in ACXB.
destruct (af_acc_live RT AF Σ10 m11 _ _ ART11 INIQ) as (_ & ACIQ).
destruct (af_acc_live RT AF Σ10 m11 _ _ ART11 INMSP) as (_ & ACMS).
destruct (af_acc_live RT AF Σ10 m11 S 160 ART11 INL) as (_ & ACS11).
assert (OBS11 : aobj bsegs m11 S 160) by (split; [lia|]; split; [clear - SBLO LOR2 USPT; unfold APP_TOP in *; lia| exact ACS11]).
assert (OBXB : aobj bsegs m11 (a_exc a) (4 * 80)) by (split; [lia|]; split; [rewrite EFS in XBLO; clear - XBLO LOR2 USPT; unfold APP_TOP in *; lia| exact ACXB]).
assert (OBIQ : aobj bsegs m11 (a_iq a) 32) by (split; [lia|]; split; [clear - IQLO LOR2 USPT; unfold APP_TOP in *; lia| exact ACIQ]).
assert (OBMS : aobj bsegs m11 (a_msp a) 32)
by (split; [lia|]; split; [clear - MSLO LOR2 USPT; unfold APP_TOP in *; lia| apply (acc_sub bsegs m11 (a_msp a) 64); [exact ACMS| lia| lia]]).
assert (INPX11 : In (usp + -1600 + 32, 4 * 80) (rt_pois RT Σ10)) by (rewrite PO10; exact INPX5).
assert (OBEX11 : aobj bsegs m11 (usp + -1600 + 32) (4 * 80))
by (split; [clear - LOR2 LOSH; lia|]; split; [clear - USPT; unfold APP_TOP in *; lia| exact (af_acc_pois RT AF Σ10 m11 _ _ ART11 INPX11)]).
pose proof (af_client_consts RT AF Σ10 m11 ART11) as CC11.
pose proof (af_live_small RT AF Σ10 m11 _ _ ART11 INXB ltac:(rewrite EFS; lia)) as XBSEG.
pose proof (af_live_small RT AF Σ10 m11 _ _ ART11 INMSP ltac:(lia)) as MSSEG.
unfold hid in XBSH, MSSH, SFA, XBFA, MSFA, IQFA, AP_XB_IQ, AP_XB_MS, AP_IQ_MS, AP_S_XB, AP_S_MS, OOFF.
rewrite EFS in XBLO, XBSH, XBFA, AP_XB_IQ, AP_XB_MS, AP_S_XB, LEXB.
cps_seg (sblB_e12b usp lo (usp + -1600) S OUT A f sf (sbmode_struct (sbd_mode s)) (sbd_frame_size s) 80 (usp + -1600 + 32) (a_exc a) (a_iq a) (a_msp a)
(OUT + 4 * sbd_frame_size s + 4 * (80 * sub)) v10 s a ex10 vexc viq vm8 y2 xs210 _ xs510 xs910 xs1010 xra10 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F11 fc10 m11
SL10 ltac:(rewrite V392b; reflexivity) HD EFS ELPC (or_intror eq_refl) PT eq_refl eq_refl eq_refl OBS11 ISAL ISPOS SOFF SBLO
EXC10 LEX10 OBEX11 ltac:(clear - IU32; Z.div_mod_to_equations; lia) ltac:(clear; lia) ltac:(clear - USPT; lia)
EXBC LEXB OBXB ltac:(clear - AXB; Z.div_mod_to_equations; lia) ltac:(clear - XBSEG; unfold IMG_TOP_B, SEGTOP_A in *; lia) XBLO
ltac:(clear - XBSH; unfold SH_LO, SH_HI in *; lia)
IQC LIQ OBIQ ltac:(clear - AIQ; Z.div_mod_to_equations; lia) IQLO ltac:(lia)
MS2 LMS2 OBMS ltac:(clear - AMSP; Z.div_mod_to_equations; lia) ltac:(clear - MSSEG; unfold IMG_TOP_B, SEGTOP_A in *; lia) ltac:(clear - MSLO; lia)
ltac:(clear - MSSH; unfold SH_LO, SH_HI in *; lia)
OY2 LY2 OBY YP4 ltac:(rewrite EFSZ; clear - OIMG SUB; lia) ltac:(rewrite EFSZ; clear - OUTLO SUB; lia) ltac:(rewrite EFSZ; clear - OOFF SUB; lia)
ltac:(clear - AP_IQ_MS; lia) ltac:(clear - AP_XB_MS; lia) ltac:(clear - AP_XB_IQ; lia)
ltac:(rewrite EFSZ; clear - XBFA IOUT SUB; lia) ltac:(rewrite EFSZ; clear - MSFA IOUT SUB; lia) ltac:(rewrite EFSZ; clear - IQFA IOUT SUB; lia)
ltac:(clear - AP_S_XB; lia) ltac:(clear - AP_S_MS; lia) ltac:(rewrite EFSZ; clear - SFA IOUT SUB; lia)
CC11 ST10 ltac:(clear - LOR2; lia) ltac:(clear; lia) LOSH ltac:(clear - USPT; lia) MI11 FRM10).
destruct POST as (m12 & xra12 & xt012 & xa012 & xa212 & xa612 & xa712 & xt412 & xt512 & xt612 & F12 & fc12
& vexc12 & vm812 & y212 & -> & MU12 & WM12 & MI12 & ST12 & FRM12 & EXBC12 & LEXB12 & MS212 & LMS212 & OY212 & LY212).
clear EXBC MS2 OY2 LEXB LMS2 LY2 OBY OBS11 OBXB OBIQ OBMS OBEX11 CC11 ACXB ACIQ ACMS ACS11 XBSEG MSSEG FRM10.

assert (REP12 : bits_rep bsegs m12 A D (sbsub_bits sm b)).
{ apply (BRT _ m11 m12 _ REP11 MU12 WM12 OK10 SZSB).
- cbn [disjoint_from]. unfold hidp, BITS_SIZEOF in IAOUT. rewrite EFSZ. clear - IAOUT MSFA XBFA IA ALO LOR2 SUB. unfold BITS_SIZEOF in *. repeat split; lia.
- cbn [disjoint_from]. unfold hid in PDFA, AP_PD_MS, AP_PD_XB. rewrite EFSZ. clear - PDFA AP_PD_MS AP_PD_XB IOUT PD1 PD2 PDLO LOR2 SUB EFS. repeat split; lia. }
clear REP11.
lazymatch type of MU12 with munch ?W _ _ => assert (OF12 : offsh W)
by (cbn; rewrite EFSZ; clear - OOFF MSSH XBSH LOR2 LOSH USPT SUB; unfold SH_LO, SH_HI in *; repeat split; lia) end.
pose proof (ACCM _ m11 m12 A 48 ACA11 MU12 OF12 ltac:(lia) ltac:(clear - ALO LOR2 USPT; unfold APP_TOP in *; lia)) as ACA12.
pose proof (ACCM _ m11 m12 OUT 8000 ACO11 MU12 OF12 ltac:(lia) ltac:(clear - OUTLO LOR2 USPT; unfold APP_TOP in *; lia)) as ACO12.
clear ACA11 ACO11 OF12.
pose proof (wmono_trans bsegs _ _ _ WMR WM12) as WMR12. clear WMR. rename WMR12 into WMR.

assert (ART12 : ART RT Σ10 m12).
{ apply (af_frame RT AF Σ10 m11 m12 lo ART11 LOWS); [| exact WM12].
intros a0 Ha. apply MU12. cbn [outside].
split; [intros Hin; apply Ha; right; right; right; left; exists fh, kh; split; [exact INFH| rewrite EFSZ in Hin; clear - Hin IOUT SUB; lia]|].
split; [intros Hin; apply Ha; right; right; left; exists (a_msp a), 64; split; [exact INMSP| clear - Hin; lia]|].
split; [intros Hin; apply Ha; left; clear - Hin LOR2 USPT; unfold USTACK_TOP in *; lia|].
split; [intros Hin; apply Ha; right; right; left; exists (a_exc a), (4 * sbd_subframeSize s); split; [exact INXB| rewrite EFS; clear - Hin; lia]| exact I]. }
lazymatch type of PF with rt_pres_fp ?L ?Fr ?U ?W0 ?m0 m11 =>
assert (PF12 : rt_pres_fp L Fr U W0 m0 m12)
by (apply (pres_fp_trans _ _ _ _ m0 m11 m12 PF); apply (pres_fp_of_munch _ _ _ _ _ m11 m12 MU12);
intros x Hx Ho; cbn [outside] in Ho |- *; decompose [and] Ho; pose proof (SPL x Hx) as SX;
split; [intros Hin; match goal with H : ~ (OUT <= x < OUT + 8000) |- _ => apply H; rewrite EFSZ in Hin; clear - Hin SUB; lia end|];
split; [intros Hin; match goal with H : ~ (a_msp a <= x < a_msp a + 64) |- _ => apply H; clear - Hin; lia end|];
split; [intros Hin; clear - SX Hin SSP0 ILOW LOR2; lia|];
split; [intros Hin; match goal with H : ~ (a_exc a <= x < a_exc a + 4 * sbd_subframeSize s) |- _ => apply H; rewrite EFS; clear - Hin; lia end| exact I]) end.
clear PF. rename PF12 into PF.
sblB_trm SL10 MU12 WM12 ltac:(unfold hid in *; rewrite ?EFSZ; clear - OUTLO MSLO XBLO LOR2 SUB EFS; repeat split; lia).
sblB_trm EXC10 MU12 WM12 ltac:(unfold hid in *; rewrite ?EFSZ; clear - OUTLO MSLO XBLO LOR2 SUB EFS; repeat split; lia).
sblB_trm LAKC5 MU12 WM12 ltac:(rewrite LLAK5; unfold hid in *; rewrite ?EFSZ; clear - OUTLO MSLO XBLO LOR2 SUB EFS; repeat split; lia).
sblB_trm LIQC4 MU12 WM12 ltac:(rewrite LLIQ4; unfold hid in *; rewrite ?EFSZ; clear - OUTLO MSLO XBLO LOR2 SUB EFS; repeat split; lia).
sblB_trm LPIC MU12 WM12 ltac:(rewrite LLPI; unfold hid in *; rewrite ?EFSZ; clear - OUTLO MSLO XBLO LOR2 SUB EFS; repeat split; lia).
sblB_trm LERC MU12 WM12 ltac:(rewrite LLER; unfold hid in *; rewrite ?EFSZ; clear - OUTLO MSLO XBLO LOR2 SUB EFS; repeat split; lia).
sblB_trm LQC MU12 WM12 ltac:(rewrite LLQ; unfold hid in *; rewrite ?EFSZ; clear - OUTLO MSLO XBLO LOR2 SUB EFS; repeat split; lia).
sblB_trm HLZ MU12 WM12 ltac:(unfold hid in *; rewrite ?EFSZ; clear - OUTLO MSLO XBLO LOR2 SUB EFS; repeat split; lia).
sblB_trm HRZ MU12 WM12 ltac:(unfold hid in *; rewrite ?EFSZ; clear - OUTLO MSLO XBLO LOR2 SUB EFS; repeat split; lia).
sblB_trm HD MU12 WM12 ltac:(unfold hid in *; rewrite ?EFSZ; clear - SFA IOUT AP_S_MS AP_S_XB SBLO LOR2 SUB EFS; repeat split; lia).
sblB_trm FST MU12 WM12 ltac:(unfold hid in *; rewrite ?EFSZ; clear - SFA IOUT AP_S_MS AP_S_XB SBLO LOR2 SUB EFS; repeat split; lia).
sblB_trm PT MU12 WM12 ltac:(unfold hid in *; rewrite ?EFSZ; clear - SFA IOUT AP_S_MS AP_S_XB SBLO LOR2 SUB EFS; repeat split; lia).
sblB_trm LEC MU12 WM12 ltac:(unfold hid in *; rewrite ?EFSZ; clear - SFA IOUT AP_S_MS AP_S_XB SBLO LOR2 SUB EFS; repeat split; lia).
sblB_trm SEEDC10 MU12 WM12 ltac:(unfold hid in *; rewrite ?EFSZ; clear - SFA IOUT AP_S_MS AP_S_XB SBLO LOR2 SUB EFS; repeat split; lia).
sblB_trm CFG MU12 WM12 ltac:(rewrite ?LPAD1; unfold hid in *; rewrite ?EFSZ; clear - SFA IOUT AP_S_MS AP_S_XB SBLO LOR2 SUB EFS; repeat split; lia).
sblB_trm IDC MU12 WM12 ltac:(unfold hid in *; rewrite ?EFSZ; clear - SFA IOUT AP_S_MS AP_S_XB SBLO LOR2 SUB EFS; repeat split; lia).
sblB_trm PAD2C MU12 WM12 ltac:(rewrite ?LPAD2; unfold hid in *; rewrite ?EFSZ; clear - SFA IOUT AP_S_MS AP_S_XB SBLO LOR2 SUB EFS; repeat split; lia).
sblB_trm OQC MU12 WM12 ltac:(rewrite LOQ; unfold hid in *; rewrite ?EFSZ; clear - OQFA IOUT AP_OQ_MS AP_XB_OQ OQLO LOR2 SUB EFS; repeat split; lia).
sblB_trm IQC MU12 WM12 ltac:(rewrite LIQ; unfold hid in *; rewrite ?EFSZ; clear - IQFA IOUT AP_IQ_MS AP_XB_IQ IQLO LOR2 SUB EFS; repeat split; lia).
sblB_trm ERC MU12 WM12 ltac:(rewrite LER; unfold hid in *; rewrite ?EFSZ; clear - ERFA IOUT AP_ER_MS AP_XB_ER ERLO LOR2 SUB EFS; repeat split; lia).
sblB_trm PGC6 MU12 WM12 ltac:(rewrite LPG6; unfold hid in *; rewrite ?EFSZ; clear - PGFA IOUT AP_PG_MS AP_XB_PG PGLO LOR2 SUB EFS; repeat split; lia).
sblB_trm MS3 MU12 WM12 ltac:(rewrite LMS3; unfold hid in *; rewrite ?EFSZ; clear - MSFA IOUT AP_XB_MS MSLO LOR2 SUB EFS; repeat split; lia).
sblB_trm OY1 MU12 WM12 ltac:(rewrite ?LY1; unfold hid in *; rewrite ?EFSZ; clear - MSFA XBFA IOUT LY1 OUTLO LOR2 SUB EFS; repeat split; lia).
sblB_trm OY3 MU12 WM12 ltac:(rewrite ?LY3; unfold hid in *; rewrite ?EFSZ; clear - MSFA XBFA IOUT LY3 OUTLO LOR2 SUB EFS; repeat split; lia).
clear MU12 WM12 ST10 ART11 MI11.
cps_hide.

assert (OUTC12 : rw_cells bsegs m12 OUT (f32 (y1 ++ y212 ++ y3))).
{ apply sblB_f32_join_win; [exact OY1| rewrite LY1; replace (OUT + 4 * (320 + 80 * sub)) with (OUT + 4 * sbd_frame_size s + 4 * (80 * sub)) by (rewrite EFSZ; lia); exact OY212|].
rewrite LY1, LY212. replace (OUT + 4 * (320 + 80 * sub) + 4 * 80) with (OUT + 4 * sbd_frame_size s + 4 * (80 * sub) + 4 * 80) by (rewrite EFSZ; lia). exact OY3. }
assert (LOUT12 : length (y1 ++ y212 ++ y3) = 2000%nat) by (rewrite !length_app; clear - LY1 LY3 LY212 SUB; lia).
assert (MSPC12 : rw_cells bsegs m12 (a_msp a) (f32 (vm812 ++ vm8b))).
{ rewrite f32_app. apply rw_cells_join; [exact MS212|]. rewrite cells_size_f32, LMS212. replace (a_msp a + Z.of_nat (4 * 8)) with (a_msp a + 32) by lia. exact MS3. }
assert (LMSP12 : length (vm812 ++ vm8b) = 16%nat) by (rewrite length_app, LMS212, LMS3; reflexivity).
clear OY1 OY3 OY212 MS212 MS3 LY1 LY3 LY212 LMS212 LMS3.

destruct (af_acc_live RT AF Σ10 m12 _ _ ART12 INXB) as (_ & ACXB). rewrite EFS in ACXB.
destruct (af_acc_live RT AF Σ10 m12 _ _ ART12 INIQ) as (_ & ACIQ).
destruct (af_acc_live RT AF Σ10 m12 _ _ ART12 INER) as (_ & ACER).
destruct (af_acc_live RT AF Σ10 m12 S 160 ART12 INL) as (_ & ACS12).
assert (OBS12 : aobj bsegs m12 S 160) by (split; [lia|]; split; [clear - SBLO LOR2 USPT; unfold APP_TOP in *; lia| exact ACS12]).
assert (OBXB : aobj bsegs m12 (a_exc a) (4 * 80)) by (split; [lia|]; split; [clear - XBLO LOR2 USPT; unfold APP_TOP in *; lia| exact ACXB]).
assert (OBIQ : aobj bsegs m12 (a_iq a) 32) by (split; [lia|]; split; [clear - IQLO LOR2 USPT; unfold APP_TOP in *; lia| exact ACIQ]).
assert (OBER : aobj bsegs m12 (a_er a) 16) by (split; [lia|]; split; [clear - ERLO LOR2 USPT; unfold APP_TOP in *; lia| exact ACER]).
assert (INPAK12 : In (usp + -1184, 32) (rt_pois RT Σ10)) by (rewrite PO10; exact INPAK).
assert (OBAK12 : aobj bsegs m12 (usp + -1184) 32)
by (split; [lia|]; split; [clear - USPT; unfold APP_TOP in *; lia| exact (af_acc_pois RT AF Σ10 m12 _ _ ART12 INPAK12)]).
pose proof (af_client_consts RT AF Σ10 m12 ART12) as CC12.
pose proof (af_live_small RT AF Σ10 m12 _ _ ART12 INIQ ltac:(lia)) as IQSEG.
pose proof (af_live_small RT AF Σ10 m12 _ _ ART12 INER ltac:(lia)) as ERSEG.
unfold hid in IQSH, ERSH, AP_IQ_ER, AP_S_IQ, AP_S_ER, AP_XB_ER, AP_XB_IQ.
rewrite EFS in AP_XB_ER.
cps_seg (sblB_e12c usp lo (usp + -1600) S OUT A f sf (sbmode_struct (sbd_mode s)) (sbd_frame_size s) 80 sub (a_exc a) (a_iq a) (a_er a) (usp + -1184) v10 s a
vexc12 viq ver aks5 xra12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F12 fc12 m12
SL10 ltac:(rewrite V456b; reflexivity) HD EFS ELPC ENSF (or_intror eq_refl) SUB PT eq_refl eq_refl eq_refl OBS12 ISAL ISPOS SOFF SBLO
EXBC12 LEXB12 OBXB ltac:(clear - AXB; Z.div_mod_to_equations; lia) XBLO ltac:(lia)
IQC LIQ OBIQ ltac:(clear - AIQ; Z.div_mod_to_equations; lia) ltac:(clear - IQSEG; unfold IMG_TOP_B, SEGTOP_A in *; lia) IQLO
ltac:(clear - IQSH; unfold SH_LO, SH_HI in *; lia)
ERC LER OBER ltac:(clear - AER; Z.div_mod_to_equations; lia) ltac:(clear - ERSEG; unfold IMG_TOP_B, SEGTOP_A in *; lia) ERLO
ltac:(clear - ERSH; unfold SH_LO, SH_HI in *; lia)
ltac:(clear - AP_IQ_ER; lia) ltac:(clear - AP_S_IQ; lia) ltac:(clear - AP_S_ER; lia) ltac:(clear - AP_XB_IQ; lia) ltac:(clear - AP_XB_ER; lia)
eq_refl LAKC5 LLAK5 OBAK12 CC12 ST12 ltac:(clear - LOR2; lia) ltac:(clear; lia) LOSH ltac:(clear - USPT; lia) IU32 MI12 FRM12).
destruct POST as (m13 & xt013 & xt113 & xt213 & xa213 & xa313 & xa413 & xa513 & xa613 & xa713 & xt313 & xt413 & xt513 & xt613 & F13 & fc13 & viq13 & ver13
& -> & MU13 & WM13 & MI13 & ST13 & FRM13 & IQC13 & LIQ13 & ERC13 & LER13).
clear IQC LIQ ERC LER OBS12 OBXB OBIQ OBER OBAK12 CC12 ACXB ACIQ ACER ACS12 IQSEG ERSEG INPAK12 FRM12.
assert (REP13 : bits_rep bsegs m13 A D (sbsub_bits sm b)).
{ apply (BRT _ m12 m13 _ REP12 MU13 WM13 OK10 SZSB).
- cbn [disjoint_from]. unfold hid in IQFA, ERFA. clear - IQFA ERFA IA ALO LOR2. unfold BITS_SIZEOF in *. repeat split; lia.
- cbn [disjoint_from]. unfold hid in AP_PD_IQ, AP_PD_ER. clear - AP_PD_IQ AP_PD_ER PD1 PD2 PDLO LOR2. repeat split; lia. }
clear REP12.
lazymatch type of MU13 with munch ?W _ _ => assert (OF13 : offsh W)
by (cbn; clear - IQSH ERSH LOR2 LOSH USPT; unfold SH_LO, SH_HI in *; repeat split; lia) end.
pose proof (ACCM _ m12 m13 A 48 ACA12 MU13 OF13 ltac:(lia) ltac:(clear - ALO LOR2 USPT; unfold APP_TOP in *; lia)) as ACA13.
pose proof (ACCM _ m12 m13 OUT 8000 ACO12 MU13 OF13 ltac:(lia) ltac:(clear - OUTLO LOR2 USPT; unfold APP_TOP in *; lia)) as ACO13.
clear ACA12 ACO12 OF13.
pose proof (wmono_trans bsegs _ _ _ WMR WM13) as WMR13. clear WMR. rename WMR13 into WMR.

assert (ART13 : ART RT Σ10 m13).
{ apply (af_frame RT AF Σ10 m12 m13 lo ART12 LOWS); [| exact WM13].
intros a0 Ha. apply MU13. cbn [outside].
split; [intros Hin; apply Ha; right; right; left; exists (a_iq a), 32; split; [exact INIQ| clear - Hin; lia]|].
split; [intros Hin; apply Ha; right; right; left; exists (a_er a), 16; split; [exact INER| clear - Hin; lia]|].
split; [intros Hin; apply Ha; left; clear - Hin LOR2 USPT; unfold USTACK_TOP in *; lia| exact I]. }
lazymatch type of PF with rt_pres_fp ?L ?Fr ?U ?W0 ?m0 m12 =>
assert (PF13 : rt_pres_fp L Fr U W0 m0 m13)
by (apply (pres_fp_trans _ _ _ _ m0 m12 m13 PF); apply (pres_fp_of_munch _ _ _ _ _ m12 m13 MU13);
intros x Hx Ho; cbn [outside] in Ho |- *; decompose [and] Ho; pose proof (SPL x Hx) as SX;
split; [intros Hin; match goal with H : ~ (a_iq a <= x < a_iq a + 32) |- _ => apply H; exact Hin end|];
split; [intros Hin; match goal with H : ~ (a_er a <= x < a_er a + 16) |- _ => apply H; exact Hin end|];
split; [intros Hin; clear - SX Hin SSP0 ILOW LOR2; lia| exact I]) end.
clear PF. rename PF13 into PF.
sblB_trm SL10 MU13 WM13 ltac:(clear - IQLO ERLO LOR2; repeat split; lia).
sblB_trm EXC10 MU13 WM13 ltac:(clear - IQLO ERLO LOR2; repeat split; lia).
sblB_trm LAKC5 MU13 WM13 ltac:(rewrite LLAK5; clear - IQLO ERLO LOR2; repeat split; lia).
sblB_trm LIQC4 MU13 WM13 ltac:(rewrite LLIQ4; clear - IQLO ERLO LOR2; repeat split; lia).
sblB_trm LPIC MU13 WM13 ltac:(rewrite LLPI; clear - IQLO ERLO LOR2; repeat split; lia).
sblB_trm LERC MU13 WM13 ltac:(rewrite LLER; clear - IQLO ERLO LOR2; repeat split; lia).
sblB_trm LQC MU13 WM13 ltac:(rewrite LLQ; clear - IQLO ERLO LOR2; repeat split; lia).
sblB_trm HLZ MU13 WM13 ltac:(clear - IQLO ERLO LOR2; repeat split; lia).
sblB_trm HRZ MU13 WM13 ltac:(clear - IQLO ERLO LOR2; repeat split; lia).
sblB_trm HD MU13 WM13 ltac:(unfold hid in *; clear - AP_S_IQ AP_S_ER SBLO LOR2; repeat split; lia).
sblB_trm FST MU13 WM13 ltac:(unfold hid in *; clear - AP_S_IQ AP_S_ER SBLO LOR2; repeat split; lia).
sblB_trm PT MU13 WM13 ltac:(unfold hid in *; clear - AP_S_IQ AP_S_ER SBLO LOR2; repeat split; lia).
sblB_trm LEC MU13 WM13 ltac:(unfold hid in *; clear - AP_S_IQ AP_S_ER SBLO LOR2; repeat split; lia).
sblB_trm SEEDC10 MU13 WM13 ltac:(unfold hid in *; clear - AP_S_IQ AP_S_ER SBLO LOR2; repeat split; lia).
sblB_trm CFG MU13 WM13 ltac:(rewrite ?LPAD1; unfold hid in *; clear - AP_S_IQ AP_S_ER SBLO LOR2; repeat split; lia).
sblB_trm IDC MU13 WM13 ltac:(unfold hid in *; clear - AP_S_IQ AP_S_ER SBLO LOR2; repeat split; lia).
sblB_trm PAD2C MU13 WM13 ltac:(rewrite ?LPAD2; unfold hid in *; clear - AP_S_IQ AP_S_ER SBLO LOR2; repeat split; lia).
sblB_trm EXBC12 MU13 WM13 ltac:(unfold hid in *; clear - AP_XB_IQ AP_XB_ER XBLO LOR2 EFS LEXB12; repeat split; lia).
sblB_trm OQC MU13 WM13 ltac:(rewrite LOQ; unfold hid in *; clear - AP_OQ_IQ AP_OQ_ER OQLO LOR2; repeat split; lia).
sblB_trm PGC6 MU13 WM13 ltac:(rewrite LPG6; unfold hid in *; clear - AP_IQ_PG AP_PG_ER PGLO LOR2; repeat split; lia).
sblB_trn MSPC12 MU13 WM13 ltac:(rewrite cells_size_f32, LMSP12; unfold hid in *; clear - AP_IQ_MS AP_ER_MS MSLO LOR2; repeat split; lia).
sblB_trn OUTC12 MU13 WM13 ltac:(rewrite cells_size_f32, LOUT12; unfold hid in *; clear - IQFA ERFA IOUT OUTLO LOR2; repeat split; lia).
clear MU13 WM13 ST12 ART12 MI12.
cps_hide.

assert (TOPV : v_544 v10 = Z_to_bv 64 (sblB_v544A (usp + -1600) sm)) by exact V544b.
assert (BOTV : v_288 v10 = Z_to_bv 64 (usp + -1216)) by (rewrite V288b; reflexivity).
assert (DCB0 : sm_double_codebook sm = 0).
{ destruct (sb_submode_cases (sbd_mode s) (sbd_submodeID s) sm (or_intror EMO) HSID SM) as [(E & _) | (_ & _ & ->)]; [rewrite EMO in E; discriminate E| reflexivity]. }
assert (TOPB : usp + -1600 <= sblB_v544A (usp + -1600) sm <= usp + -1600 /\ sblB_v544A (usp + -1600) sm mod 8 = 0).
{ unfold sblB_v544A. rewrite DCB0. cbn [Z.eqb]. split; [lia | clear - IU32; Z.div_mod_to_equations; lia]. }
cps_rt (AUNlo Σ10 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m13 (sblB_v544A (usp + -1600) sm) (usp + -1216) lo).
{ intros e He. rewrite PO10, PO5, PO3, PO2 in He. destruct He as [<-|He].
- left. unfold pz_lo, pz_hi. cbn [fst snd]. rewrite RR1. clear - TOPB. lia.
- right. exact (POA1 e He). }
{ unfold call_ok. rewrite unsigned_lit by (clear - LOR2 LOSH USPT; unfold USTACK_TOP in *; lia).
split; [exact ST13|]. split; [exact LOWS|]. split; [clear - LOR2; unfold RT_STACK; lia|]. split; [clear - USPT; unfold USTACK_TOP in *; lia|].
clear - IU32; Z.div_mod_to_equations; lia. }
intros c14 (Σ14 & Hc14 & PO14 & LV14 & FRS14 & SP14 & CR14).
destruct (ASTA_unpack RT Σ14 PMc _ c14 Hc14) as (ms14 & PO & Hc'); clear Hc14; cbv beta in PO.
destruct PO as (m14 & v014 & RS14 & (ART14 & MI14 & WM14 & ST14) & PRES14 & ACT14).
cps_ret RS14.
rewrite unsigned_lit in ST14, PRES14 by (clear - LOR2 LOSH USPT; unfold USTACK_TOP in *; lia).
clear Hc.
pres_transport_g PRES14 ltac:(ulc).
lazymatch type of PF with rt_pres_fp ?L ?Fr ?U ?W0 ?m0 m13 =>
assert (PF14 : rt_pres_fp L Fr U W0 m0 m14)
by (apply (pres_fp_trans _ _ _ _ m0 m13 m14 PF);
apply (pres_fp_mono _ _ _ _ _ _ _ m13 m14 (pres_fp_of_pres _ _ _ W0 m13 m14 PRES14));
[intros e He; rewrite LVE10, LVE5, LVE3, LVE2; exact He | intros e He; rewrite FRE10, FRE5, FRE3, FRE2; exact He | lia]) end.
clear PF. rename PF14 into PF.
pose proof (ACT14 A 48 ACA13 ltac:(clear - ALO LOR2 USPT; unfold USTACK_TOP in *; lia) ltac:(left; clear - ALO LOR2 TOPB; lia)) as ACA14.
pose proof (ACT14 OUT 8000 ACO13 ltac:(clear - OUTLO LOR2 USPT; unfold USTACK_TOP in *; lia) ltac:(left; clear - OUTLO LOR2 TOPB; lia)) as ACO14.
assert (REP14 : bits_rep bsegs m14 A D (sbsub_bits sm b)) by exact (BRTP _ _ _ m13 m14 _ PRES14 WM14 INFH INPD REP13 OK10 SZSB).
clear ACA13 ACO13 ACT14 REP13 PRES14.
pose proof (wmono_trans bsegs _ _ _ WMR WM14) as WMR14. clear WMR WM14. rename WMR14 into WMR.
clear ST13 ART13 MI13.
pose proof LV14 as LVE14. pose proof FRS14 as FRE14. cps_sigma LV14 FRS14 SP14.

remember (y1 ++ y212 ++ y3) as ows12 eqn:EOWS12. remember (vm812 ++ vm8b) as vms12 eqn:EVMS12. clear EOWS12 EVMS12.

pose proof (stk_release bsegs m14 lo (usp + -1600) _ ST14 HLZ ltac:(clear - LOR2; lia)) as STa. cbn [cells_size csize Nat.add] in STa.
replace (usp + -1600 + Z.of_nat 32) with (usp + -1600 + 32) in STa by lia.
pose proof (stk_release bsegs m14 lo (usp + -1600 + 32) _ STa EXC10 ltac:(clear - LOR2; lia)) as STb. rewrite cells_size_f32 in STb.
replace (usp + -1600 + 32 + Z.of_nat (4 * length ex10)) with (usp + -1248) in STb by (clear - LEX10; lia).
pose proof (stk_release bsegs m14 lo (usp + -1248) _ STb HRZ ltac:(clear - LOR2; lia)) as STc. cbn [cells_size csize Nat.add] in STc.
replace (usp + -1248 + Z.of_nat 32) with (usp + -1216) in STc by lia.
clear STa STb ST14 HLZ HRZ EXC10 LEX10.
destruct (af_acc_live RT AF Σ14 m14 S 160 ART14 INL) as (_ & ACS14).
assert (OBS14 : aobj bsegs m14 S 160) by (split; [lia|]; split; [clear - SBLO LOR2 USPT; unfold APP_TOP in *; lia| exact ACS14]).
cps_seg (sblB_e13 usp (usp + -1600) lo S OUT A f sf (sbmode_struct (sbd_mode s)) (sbd_frame_size s) sub v10 s a gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m14
SL10 BOTV V480b HD ENSF SUB OBS14 ISAL ISPOS SOFF SBLO ltac:(clear - LOR2; lia) LOSH ltac:(clear - USPT; lia) MI14 FRM13).
destruct POST as (m15 & k15 & F15 & fc15 & HOUT & MU15 & WM15 & MI15 & FRM15 & SL15).
clear OBS14 ACS14 SL10.
lazymatch type of MU15 with munch ?W _ _ => assert (OF15 : offsh W) by (cbn; clear - LOR2 LOSH USPT; unfold SH_LO, SH_HI in *; lia) end.
assert (REP15 : bits_rep bsegs m15 A D (sbsub_bits sm b)).
{ apply (BRT _ m14 m15 _ REP14 MU15 WM15 OK10 SZSB); cbn [disjoint_from]; (split; [| exact I]); clear - ALO PD1 PD2 PDLO LOR2; unfold BITS_SIZEOF in *; lia. }
clear REP14.
pose proof (ACCM _ m14 m15 A 48 ACA14 MU15 OF15 ltac:(lia) ltac:(clear - ALO LOR2 USPT; unfold APP_TOP in *; lia)) as ACA15.
pose proof (ACCM _ m14 m15 OUT 8000 ACO14 MU15 OF15 ltac:(lia) ltac:(clear - OUTLO LOR2 USPT; unfold APP_TOP in *; lia)) as ACO15.
clear ACA14 ACO14 OF15.
pose proof (wmono_trans bsegs _ _ _ WMR WM15) as WMR15. clear WMR. rename WMR15 into WMR.
cps_hide.
cps_seg_post.
rename ART into ART15. clear MU15 WM15.

assert (SIG14 : rt_live RT Σ14 = live /\ rt_frames RT Σ14 = (f, 0%nat) :: frames /\ rt_sp0 RT Σ14 = sp0 /\ rt_credit RT Σ14 = cr
/\ rt_pois RT Σ14 = [(usp + -1184, 32); (usp + -1088, 32); (usp + -992, 32); (usp + -896, 16); (usp + -800, 16)] ++ pois).
{ rewrite LVE14, LVE10, LVE5, LVE3, LVE2, SLIVE. rewrite FRE14, FRE10, FRE5, FRE3, FRE2, SFRM. rewrite SP14, SP10, SP5, SP3, SP2, SSP0.
rewrite CR14, CR10, CR5, CR3, CR2, SCR. rewrite PO14, PO10, PO5, PO3, PO2.
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
rewrite pois_drop_cons_below by (unfold pz_lo; cbn [fst]; lia). rewrite (pois_drop_above _ _ POA1). exact SPOIS. }
assert (PFX : rt_pres_fp live ((f, 0%nat) :: frames) (usp + -1216)
[(usp + -736, usp + -160); (usp + -1088, usp + -1056); (usp + -1184, usp + -1152); (S + 132, S + 136); (a_exc a, a_exc a + 4 * sbd_subframeSize s);
(a_iq a, a_iq a + 32); (a_msp a, a_msp a + 64); (a_pg a, a_pg a + 16); (a_er a, a_er a + 16); (OUT, OUT + 8000); (A, A + BITS_SIZEOF)] mR m15)
by (rewrite <- SLIVE, <- SFRM; exact PF).
assert (LMEM : sb_loopmem RT {| x_usp := usp; x_lo := lo; x_gp := gp; x_S := S; x_OUT := OUT; x_A := A; x_D := D; x_s := s; x_a := a; x_bsz := bsz; x_f := f; x_sf := sf;
x_fh := fh; x_kh := kh; x_PD := PD; x_ND := ND; x_live := live; x_frames := frames; x_sp0 := sp0; x_cr := cr; x_pois := pois |}
mR Σ14 m15 (sbsub_bits sm b) (sbvB_480 v10 (Z_to_bv 64 (sub + 1)))).
{ exists le, seed10, pad1, pad2, lpi, ler, lq, liq4, aks5, vexc12, voq, viq13, vms12, vpg6, ver13, ows12.
split; [exact ART15|]. split; [exact MI15|]. split; [exact STc|]. split; [exact PFX|]. split; [exact WMR|]. split; [exact SL15|].
split; [exact LPIC|]. split; [exact LLPI|]. split; [exact LERC|]. split; [exact LLER|]. split; [exact LQC|]. split; [exact LLQ|].
split; [exact LIQC4|]. split; [exact LLIQ4|]. split; [exact LAKC5|]. split; [exact LLAK5|].
split; [exact (conj HD (conj FST (conj PT (conj LEC (conj SEEDC10 (conj CFG (conj IDC PAD2C)))))))|]. split; [exact LPAD1|]. split; [exact LPAD2|].
split; [exact EXBC12|]. split; [exact (eq_trans LEXB12 (eq_sym EFS))|]. split; [exact OQC|]. split; [exact LOQ|]. split; [exact IQC13|]. split; [exact LIQ13|].
split; [exact MSPC12|]. split; [exact LMSP12|]. split; [exact PGC6|]. split; [exact LPG6|]. split; [exact ERC13|]. split; [exact LER13|].
split; [exact OUTC12|]. split; [exact LOUT12|]. split; [exact REP15|]. split; [exact OK10|]. split; [exact SZSB|]. split; [exact ACA15| exact ACO15]. }
unfold hid in HOUT. destruct HOUT as [(SUB3 & ->) | (SUB3 & ->)].
+ apply Hk. left. split; [exact SUB3|].
exists Σ14, F15, fc15, m15, k15, (sbvB_480 v10 (Z_to_bv 64 (sub + 1))).
split; [exact Hc|]. split; [exact FRM15|]. split; [exact SIG14|]. split; [exact LMEM| reflexivity].
+ apply Hk. right. split; [exact SUB3|].
exists Σ14, F15, fc15, m15, k15, (sbvB_480 v10 (Z_to_bv 64 (sub + 1))).
split; [exact Hc|]. split; [exact FRM15|]. split; [exact SIG14|]. split; [exact LMEM|].
cbn [v_544 sbvB_480 x_s x_usp]. rewrite V544b. f_equal. unfold sblB_v544A, sb_top_stale. rewrite EMO. cbn [sb_exc_hull]. lia.

Unshelve. all: exact (Z_to_bv 64 0).
Qed.
End SBL.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac simpl_sizes ::=
rewrite ?cells_size_sbp_hdr, ?cells_size_sbp_ptrs, ?cells_size_sbp_cfg, ?cells_size_sb_slots, ?app_length, ?cells_size_app, ?cells_size_f32, ?length_f32;
cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length, ?cells_size_f32, ?length_f32; cbn [length].

Section SBL.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.
Hypothesis APO : alloca_poison_contract RT.
Hypothesis AUN : allocas_unpoison_contract RT.
Hypothesis AUNlo : allocas_unpoison_lo_contract RT.
Hypothesis MEMS : memset_icontract RT e_asan_memset.
Hypothesis L2L8 : lsp_to_lpc_cps8 RT.
Hypothesis INNV : forall p, scb_params_ok p -> innov_unquant_cps RT (ptr := bptr) (InnovSplitCbShapeSignUnquant p).

Lemma sbl_tr_live : forall (Σ : rts RT) frames sp W (m m' : mem) A cs p n,
rt_pres_fp (rt_live RT Σ) frames sp W m m' -> wmono asegs m m' -> In (p, n) (rt_live RT Σ) ->
rw_cells asegs m A cs -> p <= A -> A + Z.of_nat (cells_size cs) <= p + n ->
(forall x, p <= x < p + n -> outside W x) -> rw_cells asegs m' A cs.
Proof.
intros Σ frames sp W m m' A cs p n PR WM IN H1 H2 H3 HO. apply (rw_cells_agree asegs m m' A cs H1); [| exact WM].
intros a Ha. apply PR; [| apply HO; lia]. right; right; left. exists p, n. split; [exact IN| lia].
Qed.
Lemma sbl_tr_frame : forall (Σ : rts RT) live sp W (m m' : mem) A cs f k,
rt_pres_fp live (rt_frames RT Σ) sp W m m' -> wmono asegs m m' -> In (f, k) (rt_frames RT Σ) ->
rw_cells asegs m A cs -> f <= A -> A + Z.of_nat (cells_size cs) <= f + fs_size k - 8 ->
(forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells asegs m' A cs.
Proof.
intros Σ live sp W m m' A cs f k PR WM IN H1 H2 H3 HO. apply (rw_cells_agree asegs m m' A cs H1); [| exact WM].
intros a Ha. apply PR; [| apply HO; lia]. right; right; right; left. exists f, k. split; [exact IN| lia].
Qed.

Local Ltac sbl_trm H MU WM tac := let H' := fresh "T" in pose proof (rw_cells_transport asegs _ _ _ _ _ H MU WM ltac:(cbn [disjoint_from]; simpl_sizes; tac)) as H'; clear H; rename H' into H.
Local Ltac sbl_trn H MU WM tac := let H' := fresh "T" in pose proof (rw_cells_transport asegs _ _ _ _ _ H MU WM ltac:(cbn [disjoint_from]; tac)) as H'; clear H; rename H' into H.

Lemma sbl_subframe_uwb : forall (X : sbinv) (PMc : Model -> Prop) (mR : mem) (sub : Z) (b : bits_st bptr) (sm : submode),
fdfs_only PMc -> mat_stable PMc -> sb_ihyps X -> 0 <= sub < 4 ->
submode_at (sbm_submodes (sbd_mode (x_s X))) (sbd_submodeID (x_s X)) = Some sm ->
sbd_mode (x_s X) = ModeUWB ->
cps asegs (at_LA RT X PMc mR sub b)
(fun c => (sub < 3 /\ at_LA RT X PMc mR (sub + 1) (sbsub_bits sm b) c) \/ (sub = 3 /\ at_TA RT X PMc mR sm (sbsub_bits sm b) c)).
Proof.
intros X PMc mR sub b sm FDO MST IH SUB SM EM T c Hc Hk.
destruct X as [usp lo gp S OUT A D s a bsz f sf fh kh PD ND live frames sp0 cr pois].
unfold at_LA, sb_loopmem, sb_sigma, sb_WL, sb_pois in Hc.
cbn [x_usp x_lo x_gp x_S x_OUT x_A x_D x_s x_a x_bsz x_f x_sf x_fh x_kh x_PD x_ND x_live x_frames x_sp0 x_cr x_pois] in Hc, IH, SM, Hk, EM.
destruct Hc as (Σ1 & Fx & fc & m & k & v & Hc & FRM & SIG & LM & V296).
destruct LM as (le & seed & pad1 & pad2 & lpi & ler & lq & liq & lak & vexc & voq & viq & vmsp & vpg & ver & ows & ART0 & MI0 & ST0 & PF & WM & SL
& LPIC & LLPI & LERC & LLER & LQC & LLQ & LIQC & LLIQ & LAKC & LLAK & PCS & LPAD1 & LPAD2 & EXBC & LEXB & OQC & LOQ & IQC & LIQ & MSPC & LMSP
& PGC & LPG & ERC & LER & OUTC & LOUT & BREP & BOK & BSZ & ACA & ACO).
destruct SIG as (SLIVE & SFRM & SSP0 & SCR & SPOIS).
destruct IH as [IU32 ITOP ILOW IROOM ISPOS ISAL IINV IISV IBLK INODUP IFH IA IOUT IAOUT ID IDBLK IPOIS ISF IAL].
cbn [x_usp x_lo x_gp x_S x_OUT x_A x_D x_s x_a x_bsz x_f x_sf x_fh x_kh x_PD x_ND x_live x_frames x_sp0 x_cr x_pois] in IU32, ITOP, ILOW, IROOM, ISPOS, ISAL, IINV, IISV, IBLK, INODUP, IFH, IA, IOUT, IAOUT, ID, IDBLK, IPOIS, ISF, IAL.

destruct IINV as (HMO & EFSZ & EFFS & EFS & ENSF & ELPC & HFIRST & HSR & HLE & HENC & HSID & HISV2).
destruct PCS as (HD & FST & PT & LEC & SEEDC & CFG & IDC & PAD2C).

assert (LIVB : forall x, In x (sb_blocks s S a) -> In (blk_addr x, blk_size x) (rt_live RT Σ1)) by (intros x Hx; rewrite SLIVE; exact (IBLK x Hx)).
assert (INL : In (S, 160) (rt_live RT Σ1)) by exact (LIVB (sbd_blk s, S, SBSTATE_SIZEOF) ltac:(cbn [sb_blocks In]; tauto)).
assert (INXB : In (a_exc a, 4 * sbd_subframeSize s) (rt_live RT Σ1)) by exact (LIVB (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s) ltac:(cbn [sb_blocks In]; tauto)).
assert (INOQ : In (a_oq a, 32) (rt_live RT Σ1)) by exact (LIVB (sbd_old_qlsp s, a_oq a, 32) ltac:(cbn [sb_blocks In]; tauto)).
assert (INIQ : In (a_iq a, 32) (rt_live RT Σ1)) by exact (LIVB (sbd_interp_qlpc s, a_iq a, 32) ltac:(cbn [sb_blocks In]; tauto)).
assert (INPG : In (a_pg a, 16) (rt_live RT Σ1)) by exact (LIVB (sbd_pi_gain s, a_pg a, 16) ltac:(cbn [sb_blocks In]; tauto)).
assert (INER : In (a_er a, 16) (rt_live RT Σ1)) by exact (LIVB (sbd_exc_rms s, a_er a, 16) ltac:(cbn [sb_blocks In]; tauto)).
assert (INMSP : In (a_msp a, 64) (rt_live RT Σ1)) by exact (LIVB (sbd_mem_sp s, a_msp a, 64) ltac:(cbn [sb_blocks In]; tauto)).
pose proof (af_sp0_win RT AF Σ1 m ART0) as SPW. rewrite SSP0 in SPW.
assert (LOWS : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SSP0; exact ILOW).
destruct (live_below_lo RT AF Σ1 m S 160 lo ART0 INL LOWS) as (_ & SBLO & LOSH).
pose proof (live_facts RT AF Σ1 m S 160 ART0 INL) as (_ & _ & SIMG & SSHD).
destruct (af_acc_live RT AF Σ1 m S 160 ART0 INL) as (_ & ACS).
assert (OBS : aobj asegs m S 160) by (split; [lia|]; split; [clear - SBLO IROOM ITOP; unfold APP_TOP, USTACK_TOP, RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia| exact ACS]).
pose proof (AF_LIB Σ1 m ART0) as LC0. pose proof (af_client_consts RT AF Σ1 m ART0) as CC0.
pose proof (fun a0 => aclient_split RT AF Σ1 m (usp + -1088) a0 ART0) as SPL.

destruct (live_below_lo RT AF Σ1 m _ _ lo ART0 INXB LOWS) as (XB0 & XBLO & _).
destruct (live_below_lo RT AF Σ1 m _ _ lo ART0 INOQ LOWS) as (OQ0 & OQLO & _).
destruct (live_below_lo RT AF Σ1 m _ _ lo ART0 INIQ LOWS) as (IQ0 & IQLO & _).
destruct (live_below_lo RT AF Σ1 m _ _ lo ART0 INPG LOWS) as (PG0 & PGLO & _).
destruct (live_below_lo RT AF Σ1 m _ _ lo ART0 INER LOWS) as (ER0 & ERLO & _).
destruct (live_below_lo RT AF Σ1 m _ _ lo ART0 INMSP LOWS) as (MS0 & MSLO & _).
assert (LOR2 : lo + 74848 <= usp + -1088) by (clear - IROOM; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in IROOM; lia).
assert (USPT : usp + 16 <= 140737488355328) by (clear - ITOP; unfold USTACK_TOP in ITOP; lia).
rewrite <- SLIVE, <- SFRM in PF.

destruct BREP as ((rjb & Lrjb & BOBJ) & (bsb & BDAT & Hbsb) & BSIDE). unfold bits_cells in BOBJ. apply (proj1 (u8arr_rw_CB m D bsb)) in BDAT.
assert (Lbsb : Z.of_nat (length bsb) = sb_buf_size b) by (pose proof BOK as OK'; unfold bits_ok in OK'; rewrite Hbsb, zlength_map_unsigned in OK'; clear - OK'; lia).
destruct ID as (IND & PD1 & PD2).
assert (INPD : In (PD, ND) (rt_live RT Σ1)) by (rewrite SLIVE; exact IND).
destruct (live_below_lo RT AF Σ1 m _ _ lo ART0 INPD LOWS) as (_ & PDLO & _).

assert (INFH0 : In (fh, kh) (rt_frames RT Σ1)) by (rewrite SFRM; right; exact IFH).
destruct (frame_below_lo RT AF Σ1 m fh kh lo ART0 INFH0 LOWS) as (FHLO & _ & _).
assert (ALO : A + 48 <= lo) by (clear - IA FHLO; unfold BITS_SIZEOF in IA; lia).
assert (OUTLO : OUT + 8000 <= lo) by (clear - IOUT FHLO; lia).
assert (DLO : D + Z.of_nat (length bsb) <= lo) by (clear - Lbsb BSZ PD2 PDLO; lia).
assert (IA' : fh <= A /\ A + 48 <= fh + fs_size kh - 8) by (clear - IA; unfold BITS_SIZEOF in IA; lia).

destruct (frame_live_apart RT AF Σ1 m fh kh S 160 ART0 INFH0 INL) as (SFA & _).
destruct (frame_live_apart RT AF Σ1 m fh kh _ _ ART0 INFH0 INXB) as (XBFA & _).
destruct (frame_live_apart RT AF Σ1 m fh kh _ _ ART0 INFH0 INOQ) as (OQFA & _).
destruct (frame_live_apart RT AF Σ1 m fh kh _ _ ART0 INFH0 INIQ) as (IQFA & _).
destruct (frame_live_apart RT AF Σ1 m fh kh _ _ ART0 INFH0 INPG) as (PGFA & _).
destruct (frame_live_apart RT AF Σ1 m fh kh _ _ ART0 INFH0 INER) as (ERFA & _).
destruct (frame_live_apart RT AF Σ1 m fh kh _ _ ART0 INFH0 INMSP) as (MSFA & _).
destruct (frame_live_apart RT AF Σ1 m fh kh _ _ ART0 INFH0 INPD) as (PDFA & _).

destruct HMO as [EMO | EMO]; [rewrite EM in EMO; discriminate EMO |]; pose proof EFS as EFS0; pose proof EFSZ as EFSZ0; rewrite EMO in EFS, EFSZ; cbn [sbm_subframeSize sbm_frameSize] in EFS, EFSZ.

-
assert (INFH : In (fh, kh) (rt_frames RT Σ1)) by (rewrite SFRM; right; exact IFH).
pose proof (frame_facts RT AF Σ1 m fh kh ART0 INFH) as (FH0 & FH64 & FHIMG & FHTOP & _).
assert (FSZK : 0 <= fs_size kh) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (OUTB : OUT + 8000 < 2 ^ 63) by (rewrite SSP0 in FHTOP; clear - IOUT FHTOP FSZK ILOW IROOM ITOP; unfold STACK_WIN, RT_STACK, SB_LOOP_STACK, INNOV_STACK, USTACK_TOP in *; lia).
cps_norm. cps_hide.

cps_seg (sbl_e1 usp lo S OUT A f sf (sbmode_struct (sbd_mode s)) (sbd_frame_size s) 80 384 sub v s a k gp (Z_to_bv 64 6489176) Fx fc m).
destruct POST as (m1 & jh & -> & MU1 & WM1 & MI1 & ST1 & SL1 & HULL1). clear SL.
change (Z.to_nat 384) with 384%nat in HULL1. replace (usp + -1088 - 384) with (usp + -1472) in * by lia.
cps_seg_post.

assert (RR1 : alloca_rr (usp + -1440) 320 = usp + -1088) by (unfold alloca_rr; clear - IU32; Z.div_mod_to_equations; lia).
assert (POA1 : pois_above (rt_pois RT Σ1) (usp + -1088)).
{ rewrite SPOIS. intros e He. apply in_app_iff in He. destruct He as [He|He].
- cbn [In] in He. unfold pz_lo. destruct He as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst]; lia.
- specialize (IPOIS e He). lia. }
cps_rt (APO Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (usp + -1440) 320 lo).
{ f_equal; lia. }
{ rewrite unsigned_lit by (clear - LOR2 USPT ILOW SPW; unfold STACK_WIN in *; lia). lia. }
{ rewrite RR1. exact POA1. }
{ rewrite SFRM; discriminate. }
{ cps_callok. }
intros c2 (Σ2 & Hc2 & PO2 & LV2 & FRS2 & SP2 & CR2).
cps_unpack Hc2 as (m2 & v2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ACX & ACT2).
pose proof LV2 as LVE2. pose proof FRS2 as FRE2. cps_sigma LV2 FRS2 SP2.
clear Hc0.

assert (HIS : sb_isave_ptr OUT s = 0 \/ sb_isave_ptr OUT s = OUT + 8 * sbd_frame_size s).
{ unfold sb_isave_ptr. destruct (sbd_innov_save s) as [kk|]; [right; rewrite IISV; lia| left; reflexivity]. }
assert (OUT0 : 0 < OUT) by (clear - IOUT FH0; lia).
cps_rt (sbl_dB RT AF MEMS Σ2 PMc usp lo (usp + -1472) S OUT A f sf (sbmode_struct (sbd_mode s)) (sbd_frame_size s) 80 sub fh kh _ s a ows).
{ destruct (af_acc_live RT AF Σ2 m2 S 160 ART2 INL) as (_ & ACS2). split; [lia|]. split; [clear - SBLO LOR2 USPT; unfold APP_TOP; lia| exact ACS2]. }
{ assert (OBO : aobj asegs m OUT 8000) by (split; [lia|]; split; [clear - OUTLO LOR2 USPT; unfold APP_TOP; lia| exact ACO]).
assert (OFE1 : offsh [(usp + -5184, usp + -5176); (usp + -608, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; clear - LOR2 LOSH USPT; lia).
pose proof (aobj_munch asegs _ m m1 OUT 8000 OBO MU1 (shfree_of_aobj asegs _ m OUT 8000 OFE1 OBO)) as (_ & _ & ACO1).
apply (ACT2 OUT 8000 ACO1); [unfold USTACK_TOP; clear - OUTLO LOR2 USPT; lia| left; clear - OUTLO LOR2; lia]. }
{ cps_callok. }

intros c3 (Σ3 & Hc3 & LV3 & FRS3 & SP3 & CR3 & PO3).

destruct (ASTA_unpack RT Σ3 PMc _ c3 Hc3) as (ms3 & PO & Hc'); clear Hc3 Hc; cbv beta in PO.
destruct PO as (m3 & xra3 & xt03 & xt13 & xt23 & xa03 & xa13 & xa33 & xa43 & xa53 & xa63 & xa73 & xt33 & xt43 & xt53 & xt63 & F3 & fc3 & ows3 & -> & FRM3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & SL3 & OUTC3 & LOUT3).
clear SL1 OUTC.
pose proof (SFA : _ \/ _) as SFA'. pose proof (XBFA : _ \/ _) as XBFA'. pose proof (OQFA : _ \/ _) as OQFA'. pose proof (IQFA : _ \/ _) as IQFA'.
pose proof (PGFA : _ \/ _) as PGFA'. pose proof (ERFA : _ \/ _) as ERFA'. pose proof (MSFA : _ \/ _) as MSFA'. pose proof (PDFA : _ \/ _) as PDFA'. pose proof (IAOUT : _ \/ _) as IAOUT'.
let go H IN FA := apply (sbl_tr_live Σ2 _ _ _ m2 m3 _ _ _ _ PRES3 WM3 IN) in H;
[| lia | rewrite ?cells_size_sbp_hdr, ?cells_size_sbp_ptrs, ?cells_size_sbp_cfg, ?cells_size_f32; cbn [cells_size csize Nat.add]; lia
| intros x Hx; cbn [outside]; clear - FA Hx IOUT LOR2 SBLO XBLO OQLO IQLO PGLO ERLO MSLO PDLO; lia] in
go HD INL SFA'; go FST INL SFA'; go PT INL SFA'; go LEC INL SFA'; go SEEDC INL SFA'; go CFG INL SFA'; go IDC INL SFA'; go PAD2C INL SFA';
go EXBC INXB XBFA'; go OQC INOQ OQFA'; go IQC INIQ IQFA'; go MSPC INMSP MSFA'; go PGC INPG PGFA'; go ERC INER ERFA'.

assert (TRS : forall W Asp A0 cs, rt_pres_fp (rt_live RT Σ2) (rt_frames RT Σ2) Asp W m2 m3 ->
rw_cells asegs m2 A0 cs -> Asp <= A0 -> A0 + Z.of_nat (cells_size cs) <= USTACK_TOP ->
(forall x, A0 <= x < A0 + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells asegs m3 A0 cs).
{ intros W Asp A0 cs PR H1 H2 H3 HO. apply (rw_cells_agree asegs m2 m3 A0 cs H1); [| exact WM3].
intros a0 Ha. apply PR; [left; lia | apply HO; lia]. }
let go H L := apply (TRS _ _ _ _ PRES3) in H;
[| lia | rewrite cells_size_f32; clear - L USPT; unfold USTACK_TOP; lia
| intros x Hx; rewrite cells_size_f32 in Hx; cbn [outside]; split; [|split; [|exact I]]; clear - Hx L OUTLO LOR2; lia] in
go LPIC LLPI; go LERC LLER; go LQC LLQ; go LIQC LLIQ; go LAKC LLAK.
apply (TRS _ _ _ _ PRES3) in HULL1;
[| lia | cbn [cells_size csize Nat.add]; clear - USPT; unfold USTACK_TOP; lia
| intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; split; [|split; [|exact I]]; clear - Hx OUTLO LOR2; lia].
apply (sbl_tr_live Σ2 _ _ _ m2 m3 _ _ _ _ PRES3 WM3 INPD) in BDAT;
[| exact PD1 | cbn [cells_size csize]; clear - PD2 BSZ Lbsb; lia
| intros x Hx; cbn [outside]; split; [|split; [|exact I]]; clear - Hx PDLO LOR2 PDFA' IOUT; lia].
apply (sbl_tr_frame Σ2 _ _ _ m2 m3 _ _ fh kh PRES3 WM3 INFH0) in BOBJ;
[| exact (proj1 IA') | cbn [cells_size csize Nat.add]; clear - IA'; lia
| intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; split; [|split; [|exact I]]; clear - Hx ALO LOR2 IAOUT'; unfold BITS_SIZEOF in *; lia].

assert (OFE1 : offsh [(usp + -5184, usp + -5176); (usp + -608, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; clear - LOR2 LOSH USPT; lia).
assert (ACO2 : acc asegs m2 OUT 8000).
{ assert (OBO : aobj asegs m OUT 8000) by (split; [lia|]; split; [clear - OUTLO LOR2 USPT; unfold APP_TOP; lia| exact ACO]).
pose proof (aobj_munch asegs _ m m1 OUT 8000 OBO MU1 (shfree_of_aobj asegs _ m OUT 8000 OFE1 OBO)) as (_ & _ & ACO1).
apply (ACT2 OUT 8000 ACO1); [unfold USTACK_TOP; clear - OUTLO LOR2 USPT; lia| left; clear - OUTLO LOR2; lia]. }
assert (ACA2 : acc asegs m2 A 48).
{ assert (OBA : aobj asegs m A 48) by (split; [lia|]; split; [clear - ALO LOR2 USPT; unfold APP_TOP; lia| exact ACA]).
pose proof (aobj_munch asegs _ m m1 A 48 OBA MU1 (shfree_of_aobj asegs _ m A 48 OFE1 OBA)) as (_ & _ & ACA1).
apply (ACT2 A 48 ACA1); [unfold USTACK_TOP; clear - ALO LOR2 USPT; lia| left; clear - ALO LOR2; lia]. }
assert (FH8 : fh mod 8 = 0) by (clear - FH64; Z.div_mod_to_equations; lia).
pose proof (fs_size_mod8 kh) as FK8.
pose proof (frame_facts RT AF Σ2 m2 fh kh ART2 INFH) as (_ & _ & _ & _ & _ & _ & FSA & FSL & FSU & FSS).

assert (SHF : forall o n, fh <= o -> o + n <= fh + fs_size kh -> forall i, 0 <= i < n -> SH_LO <= shad (o + i) < SH_HI
/\ (OUT + 8000 <= shad (o + i) \/ shad (o + i) < OUT)).
{ intros o n H1 H2 i Hi.
assert (B1 : shad fh <= shad (o + i)) by (unfold shad; apply Z.add_le_mono_r; apply Z.div_le_mono; lia).
assert (B2 : shad (o + i) < shad fh + fs_size kh / 8).
{ rewrite <- FSA. unfold shad. apply Z.add_lt_mono_r. apply Z.div_lt_upper_bound; [lia|].
assert (E : fh + fs_size kh = 8 * ((fh + fs_size kh) / 8))
by (pose proof (Z.div_mod (fh + fs_size kh) 8 ltac:(lia)) as XD; rewrite Zplus_mod, FH8, FK8 in XD; cbn in XD; lia).
lia. }
clear - B1 B2 FSL FSU FSS IOUT H1 H2 Hi. lia. }
assert (ACO3 : acc asegs m3 OUT 8000).
{ apply (acc_pres_fp_frame _ _ _ _ m2 m3 fh kh OUT 8000 PRES3 INFH FH8 FK8 ltac:(lia) (proj1 IOUT) ltac:(lia)); [| exact ACO2].
intros i Hi. destruct (SHF OUT 8000 (proj1 IOUT) ltac:(lia) i Hi) as (S1 & S2). cbn [outside]. split; [|split; [|exact I]]; clear - S1 S2 LOR2 LOSH; unfold SH_LO, SH_HI in *; lia. }
assert (ACA3 : acc asegs m3 A 48).
{ apply (acc_pres_fp_frame _ _ _ _ m2 m3 fh kh A 48 PRES3 INFH FH8 FK8 ltac:(lia) (proj1 IA') ltac:(lia)); [| exact ACA2].
intros i Hi. destruct (SHF A 48 (proj1 IA') ltac:(lia) i Hi) as (S1 & S2). cbn [outside]. split; [|split; [|exact I]]; clear - S1 S2 LOR2 LOSH; unfold SH_LO, SH_HI in *; lia. }

lazymatch type of PF with rt_pres_fp ?L ?Fr ?U ?W0 ?m0 m2 =>
assert (PF3 : rt_pres_fp L Fr U W0 m0 m3)
by (apply (pres_fp_trans _ _ _ _ m0 m2 m3 PF);
apply (pres_fp_of_pres_fp _ _ _ _ _ _ _ _ m2 m3 PRES3); [intros e He; rewrite LVE2; exact He | intros e He; rewrite FRE2; exact He | lia |];
intros x _ Ho; cbn [outside] in Ho |- *; decompose [and] Ho; split; [assumption | split; [assumption | exact I]]) end.
clear PF. rename PF3 into PF.
pose proof (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _ WM WM1) WM2) WM3) as WMR. clear WM WM1 WM2 WM3.
clear ST2 ART2 MI2 PRES2 ACX ACT2 MU1 PRES3 ACO2 ACA2 ACA ACO TRS OBS ACS.
pose proof LV3 as LVE3. pose proof FRS3 as FRE3. cps_sigma LV3 FRS3 SP3.

assert (ACCM : forall W (mA mB : mem) o n, acc asegs mA o n -> munch W mA mB -> offsh W -> 0 <= o -> o + n <= APP_TOP -> acc asegs mB o n).
{ intros W mA mB o n H MU OF H0 H1. assert (OB : aobj asegs mA o n) by (split; [exact H0| split; [exact H1| exact H]]).
exact (proj2 (proj2 (aobj_munch asegs W mA mB o n OB MU (shfree_of_aobj asegs W mA o n OF OB)))). }
assert (ACCF : forall live frames sp W (mA mB : mem) o n, rt_pres_fp live frames sp W mA mB -> In (fh, kh) frames ->
(forall x, SH_LO <= x < SH_HI -> outside W x) -> fh <= o -> o + n <= fh + fs_size kh -> acc asegs mA o n -> acc asegs mB o n).
{ intros live0 frames0 sp W mA mB o n PR IN HW H1 H2 H. apply (acc_pres_fp_frame _ _ _ _ mA mB fh kh o n PR IN FH8 FK8 ltac:(lia) H1 H2); [| exact H].
intros i Hi. apply HW. exact (proj1 (SHF o n H1 H2 i Hi)). }
assert (ACCX : forall live frames sp d nd (mA mB : mem) o n, rt_pres_ex live frames sp d nd mA mB -> In (fh, kh) frames ->
(d + nd <= SH_LO \/ SH_HI <= d) -> fh <= o -> o + n <= fh + fs_size kh -> o + n <= APP_TOP -> acc asegs mA o n -> acc asegs mB o n).
{ intros live0 frames0 sp d nd mA mB o n PR IN HDX H1 H2 H3 H. exact (acc_pres_ex_frame _ _ _ _ _ mA mB fh kh o n PR IN FH8 FK8 ltac:(lia) H1 H2 H3 HDX H). }

assert (TRSK : forall live frames sp W (mA mB : mem) A0 cs, rt_pres_fp live frames sp W mA mB -> wmono asegs mA mB ->
rw_cells asegs mA A0 cs -> sp <= A0 -> A0 + Z.of_nat (cells_size cs) <= USTACK_TOP ->
(forall x, A0 <= x < A0 + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells asegs mB A0 cs).
{ intros live0 frames0 sp W mA mB A0 cs PR WMx H1 H2 H3 HO. apply (rw_cells_agree asegs mA mB A0 cs H1); [| exact WMx].
intros a0 Ha. apply PR; [left; lia | apply HO; lia]. }

destruct IAL as (AG0 & AG1 & AXB & AOQ & AIQ & AMSP & APG & AER).
assert (OQ4 : a_oq a mod 4 = 0) by (clear - AOQ; Z.div_mod_to_equations; lia).
assert (SOFF : S + 160 <= SH_LO \/ SH_HI <= S) by (clear - SSHD; unfold hid, SH_LO, SH_HI in *; lia).
assert (OBS3 : aobj asegs m3 S 160)
by (destruct (af_acc_live RT AF Σ3 m3 S 160 ART3 INL) as (_ & AC); split; [lia|]; split; [clear - SBLO LOR2 USPT; unfold APP_TOP; lia| exact AC]).
assert (OBOQ3 : aobj asegs m3 (a_oq a) 32)
by (destruct (af_acc_live RT AF Σ3 m3 _ _ ART3 INOQ) as (_ & AC); split; [lia|]; split; [clear - OQLO LOR2 USPT; unfold APP_TOP; lia| exact AC]).
assert (INPQ : In (usp + -864, 32) (rt_pois RT Σ3)) by (rewrite PO3, PO2, SPOIS; right; right; right; left; reflexivity).
assert (INPIQ : In (usp + -960, 32) (rt_pois RT Σ3)) by (rewrite PO3, PO2, SPOIS; right; right; left; reflexivity).
assert (INPAK : In (usp + -1056, 32) (rt_pois RT Σ3)) by (rewrite PO3, PO2, SPOIS; right; left; reflexivity).
assert (OBQ3 : aobj asegs m3 (usp + -864) 32)
by (split; [lia|]; split; [clear - USPT; unfold APP_TOP; lia| exact (af_acc_pois RT AF Σ3 m3 _ _ ART3 INPQ)]).
assert (OBIQ3 : aobj asegs m3 (usp + -960) 32)
by (split; [lia|]; split; [clear - USPT; unfold APP_TOP; lia| exact (af_acc_pois RT AF Σ3 m3 _ _ ART3 INPIQ)]).
pose proof (af_client_consts RT AF Σ3 m3 ART3) as CC3.
cps_seg (sbl_e3 usp lo (usp + -1472) S OUT A f sf (sbmode_struct (sbd_mode s)) (sbd_frame_size s) 80 sub (a_oq a) _ s a voq lq liq).
destruct POST as (m4 & xt04 & xt14 & xt24 & xa44 & xa54 & xa64 & xa74 & xt34 & xt44 & xt54 & xt64 & F4 & fc4 & liq4 & -> & MU4 & WM4 & MI4 & ST4 & FRM4 & SL4 & LIQC4 & LLIQ4).
clear SL3 LIQC LLIQ FRM3 CC3 OBS3 OBOQ3 OBQ3 OBIQ3.
lazymatch type of MU4 with munch ?W _ _ => assert (OF4 : offsh W) by (cbn; unfold SH_LO, SH_HI; clear - LOR2 LOSH USPT; lia) end.
pose proof (ACCM _ m3 m4 A 48 ACA3 MU4 OF4 ltac:(lia) ltac:(clear - ALO LOR2 USPT; unfold APP_TOP; lia)) as ACA4.
pose proof (ACCM _ m3 m4 OUT 8000 ACO3 MU4 OF4 ltac:(lia) ltac:(clear - OUTLO LOR2 USPT; unfold APP_TOP; lia)) as ACO4.
clear ACA3 ACO3 OF4.
pose proof (wmono_trans asegs _ _ _ WMR WM4) as WMR4.
clear WMR. rename WMR4 into WMR.

clear SFA' XBFA' OQFA' IQFA' PGFA' ERFA' MSFA' PDFA' IAOUT'.
cps_hide.
clear ST3 OFE1 CC0 LC0.
cps_seg_post.

rename ART into ART4. clear MU4 WM4.

assert (POA3 : pois_above (rt_pois RT Σ3) (usp + -1472)).
{ rewrite PO3, PO2. intros e [<-|He]; [unfold pz_lo; cbn [fst]; lia| specialize (POA1 e He); lia]. }
cps_rt (L2L8 Σ3 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F4 fc4 m4 (usp + -960) (usp + -1056) lo liq4 lak).
{ rewrite FRE3, FRE2, SFRM; discriminate. }
{ rewrite unsigned_lit by (clear - LOR2 USPT ILOW SPW; unfold STACK_WIN in *; lia). exact POA3. }
{ rewrite unsigned_lit by (clear - LOR2 USPT ILOW SPW; unfold STACK_WIN in *; lia). exact ST4. }
{ rewrite unsigned_lit by (clear - LOR2 USPT ILOW SPW; unfold STACK_WIN in *; lia). clear - LOR2; unfold RT_STACK; lia. }
{ rewrite unsigned_lit by (clear - LOR2 USPT ILOW SPW; unfold STACK_WIN in *; lia). clear - USPT; unfold USTACK_TOP; lia. }
{ rewrite unsigned_lit by (clear - LOR2 USPT ILOW SPW; unfold STACK_WIN in *; lia). clear - IU32; Z.div_mod_to_equations; lia. }
intros c5 (Σ5 & Hc5 & LV5 & FRS5 & SP5 & CR5 & PO5).
cps_unpack_lib Hc5 as (v5 & m5 & aks5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5 & LAKC5 & LLAK5).
clear LAKC LLAK.
cps_tr_lib PRES5.

clear Hc.
lazymatch type of PF with rt_pres_fp ?L ?Fr ?U ?W0 ?m0 m4 =>
assert (PF5 : rt_pres_fp L Fr U W0 m0 m5)
by (apply (pres_fp_trans _ _ _ _ m0 m4 m5 PF);
apply (pres_fp_of_pres_fp _ _ _ _ _ _ _ _ m4 m5 PRES5); [intros e He; rewrite LVE3, LVE2; exact He | intros e He; rewrite FRE3, FRE2; exact He | lia |];
intros x _ Ho; cbn [outside] in Ho |- *; decompose [and] Ho; split; [intros Hin; match goal with H : ~ (usp + -1056 <= x < usp + -1024) |- _ => apply H; clear - Hin; lia end | exact I]) end.
clear PF. rename PF5 into PF.
assert (OFW5 : forall x, SH_LO <= x < SH_HI -> outside [(usp + -1056, usp + -1056 + 32)] x)
by (intros x Hx; cbn [outside]; split; [clear - Hx LOR2 LOSH USPT; unfold SH_LO, SH_HI in *; lia | exact I]).
pose proof (ACCF _ _ _ _ m4 m5 A 48 PRES5 INFH OFW5 (proj1 IA') ltac:(lia) ACA4) as ACA5.
pose proof (ACCF _ _ _ _ m4 m5 OUT 8000 PRES5 INFH OFW5 (proj1 IOUT) ltac:(lia) ACO4) as ACO5.
clear ACA4 ACO4 OFW5 PRES5.
pose proof (wmono_trans asegs _ _ _ WMR WM5) as WMR5. clear WMR WM5. rename WMR5 into WMR.
pose proof LV5 as LVE5. pose proof FRS5 as FRE5. cps_sigma LV5 FRS5 SP5.

assert (LAP : forall p1 n1 p2 n2, In (p1, n1) (rt_live RT Σ5) -> In (p2, n2) (rt_live RT Σ5) -> p1 <> p2 -> p1 + n1 <= p2 \/ p2 + n2 <= p1).
{ intros p1 n1 p2 n2 H1 H2 NE. destruct (in_split _ _ H1) as (l1 & l2 & E).
apply (af_live_disj RT AF Σ5 m5 p1 n1 p2 n2 l1 l2 ART5 E). rewrite E in H2. apply in_app_iff in H2. apply in_app_iff.
destruct H2 as [H2|[H2|H2]]; [left; exact H2| exfalso; apply NE; congruence| right; exact H2]. }
assert (ND9 : List.NoDup [S; a_g0 a; a_g1 a; a_exc a; a_oq a; a_iq a; a_pg a; a_er a; a_msp a]) by exact INODUP.
apply List.NoDup_cons_iff in ND9 as [N0 ND9]. apply List.NoDup_cons_iff in ND9 as [_ ND9]. apply List.NoDup_cons_iff in ND9 as [_ ND9].
apply List.NoDup_cons_iff in ND9 as [N3 ND9]. apply List.NoDup_cons_iff in ND9 as [N4 ND9]. apply List.NoDup_cons_iff in ND9 as [N5 ND9].
apply List.NoDup_cons_iff in ND9 as [N6 ND9]. apply List.NoDup_cons_iff in ND9 as [N7 _].
assert (D_S_XB : S <> a_exc a) by (intros E; apply N0; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INL INXB D_S_XB) as AP_S_XB. clear D_S_XB.
assert (D_S_OQ : S <> a_oq a) by (intros E; apply N0; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INL INOQ D_S_OQ) as AP_S_OQ. clear D_S_OQ.
assert (D_S_IQ : S <> a_iq a) by (intros E; apply N0; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INL INIQ D_S_IQ) as AP_S_IQ. clear D_S_IQ.
assert (D_S_PG : S <> a_pg a) by (intros E; apply N0; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INL INPG D_S_PG) as AP_S_PG. clear D_S_PG.
assert (D_S_ER : S <> a_er a) by (intros E; apply N0; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INL INER D_S_ER) as AP_S_ER. clear D_S_ER.
assert (D_S_MS : S <> a_msp a) by (intros E; apply N0; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INL INMSP D_S_MS) as AP_S_MS. clear D_S_MS.
assert (D_XB_OQ : a_exc a <> a_oq a) by (intros E; apply N3; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INXB INOQ D_XB_OQ) as AP_XB_OQ. clear D_XB_OQ.
assert (D_XB_IQ : a_exc a <> a_iq a) by (intros E; apply N3; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INXB INIQ D_XB_IQ) as AP_XB_IQ. clear D_XB_IQ.
assert (D_XB_PG : a_exc a <> a_pg a) by (intros E; apply N3; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INXB INPG D_XB_PG) as AP_XB_PG. clear D_XB_PG.
assert (D_XB_ER : a_exc a <> a_er a) by (intros E; apply N3; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INXB INER D_XB_ER) as AP_XB_ER. clear D_XB_ER.
assert (D_XB_MS : a_exc a <> a_msp a) by (intros E; apply N3; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INXB INMSP D_XB_MS) as AP_XB_MS. clear D_XB_MS.
assert (D_OQ_IQ : a_oq a <> a_iq a) by (intros E; apply N4; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INOQ INIQ D_OQ_IQ) as AP_OQ_IQ. clear D_OQ_IQ.
assert (D_OQ_PG : a_oq a <> a_pg a) by (intros E; apply N4; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INOQ INPG D_OQ_PG) as AP_OQ_PG. clear D_OQ_PG.
assert (D_OQ_ER : a_oq a <> a_er a) by (intros E; apply N4; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INOQ INER D_OQ_ER) as AP_OQ_ER. clear D_OQ_ER.
assert (D_OQ_MS : a_oq a <> a_msp a) by (intros E; apply N4; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INOQ INMSP D_OQ_MS) as AP_OQ_MS. clear D_OQ_MS.
assert (D_IQ_PG : a_iq a <> a_pg a) by (intros E; apply N5; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INIQ INPG D_IQ_PG) as AP_IQ_PG. clear D_IQ_PG.
assert (D_IQ_ER : a_iq a <> a_er a) by (intros E; apply N5; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INIQ INER D_IQ_ER) as AP_IQ_ER. clear D_IQ_ER.
assert (D_IQ_MS : a_iq a <> a_msp a) by (intros E; apply N5; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INIQ INMSP D_IQ_MS) as AP_IQ_MS. clear D_IQ_MS.
assert (D_PG_ER : a_pg a <> a_er a) by (intros E; apply N6; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INPG INER D_PG_ER) as AP_PG_ER. clear D_PG_ER.
assert (D_PG_MS : a_pg a <> a_msp a) by (intros E; apply N6; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INPG INMSP D_PG_MS) as AP_PG_MS. clear D_PG_MS.
assert (D_ER_MS : a_er a <> a_msp a) by (intros E; apply N7; rewrite E; repeat (first [left; reflexivity | right])).
pose proof (LAP _ _ _ _ INER INMSP D_ER_MS) as AP_ER_MS. clear D_ER_MS.
clear N0 N3 N4 N5 N6 N7.

destruct (live_facts RT AF Σ5 m5 _ _ ART5 INPG) as (_ & _ & PGIMG & PGSH).
destruct (live_facts RT AF Σ5 m5 _ _ ART5 INER) as (_ & _ & ERIMG & ERSH).
destruct (live_facts RT AF Σ5 m5 _ _ ART5 INXB) as (_ & _ & XBIMG & XBSH).
destruct (live_facts RT AF Σ5 m5 _ _ ART5 INIQ) as (_ & _ & IQIMG & IQSH).
destruct (live_facts RT AF Σ5 m5 _ _ ART5 INMSP) as (_ & _ & MSIMG & MSSH).
cps_hide.

rewrite <- PO5 in INPAK, INPQ, INPIQ.
assert (INPLP : In (usp + -672, 16) (rt_pois RT Σ5)) by (rewrite PO5, PO3, PO2, SPOIS; right; right; right; right; right; left; reflexivity).
destruct (af_acc_live RT AF Σ5 m5 S 160 ART5 INL) as (_ & ACS5).
assert (OBS5 : aobj asegs m5 S 160) by (split; [lia|]; split; [clear - SBLO LOR2 USPT; unfold APP_TOP; lia| exact ACS5]).
destruct (af_acc_live RT AF Σ5 m5 _ _ ART5 INPG) as (_ & ACPG5).
assert (OBPG5 : aobj asegs m5 (a_pg a) 16) by (split; [lia|]; split; [clear - PGLO LOR2 USPT; unfold APP_TOP; lia| exact ACPG5]).
assert (PG4 : a_pg a mod 4 = 0) by (clear - APG; Z.div_mod_to_equations; lia).
assert (PGOFF : a_pg a + 16 <= SH_LO \/ SH_HI <= a_pg a) by (clear - PGSH; unfold hid, SH_LO, SH_HI in *; lia).
pose proof (af_live_small RT AF Σ5 m5 _ _ ART5 INPG ltac:(lia)) as PGIMG5.
assert (PGIMG' : IMG_TOP <= a_pg a) by (clear - PGIMG5; unfold IMG_TOP, SEGTOP_A in *; lia).
pose proof (AP_S_PG : _ \/ _) as SPG.
assert (OBAK5 : aobj asegs m5 (usp + -1056) 32)
by (split; [lia|]; split; [clear - USPT; unfold APP_TOP; lia| exact (af_acc_pois RT AF Σ5 m5 _ _ ART5 INPAK)]).
assert (OBLP5 : aobj asegs m5 (usp + -672) 16)
by (split; [lia|]; split; [clear - USPT; unfold APP_TOP; lia| exact (af_acc_pois RT AF Σ5 m5 _ _ ART5 INPLP)]).
cps_seg (sbl_e4 usp lo (usp + -1472) S OUT A f sf (sbmode_struct (sbd_mode s)) (sbd_frame_size s) 80 sub (a_pg a) (usp + -1056) (usp + -672) _ s a vpg aks5 lpi).
destruct POST as (m6 & xt06 & xa36 & xa46 & xa56 & xa66 & xa76 & F6 & fc6 & vpg6 & -> & MU6 & WM6 & MI6 & FRM6 & PGC6 & LPG6).
clear PGC LPG SPG RS5 OBS5 OBPG5 OBAK5 OBLP5 ACS5 ACPG5 PGOFF PGIMG5 PG4.
lazymatch type of MU6 with munch ?W _ _ => assert (OF6 : offsh W) by (cbn; clear - PGSH; unfold hid, SH_LO, SH_HI in *; lia) end.
pose proof (ACCM _ m5 m6 A 48 ACA5 MU6 OF6 ltac:(lia) ltac:(clear - ALO LOR2 USPT; unfold APP_TOP; lia)) as ACA6.
pose proof (ACCM _ m5 m6 OUT 8000 ACO5 MU6 OF6 ltac:(lia) ltac:(clear - OUTLO LOR2 USPT; unfold APP_TOP; lia)) as ACO6.
clear ACA5 ACO5 OF6.
pose proof (wmono_trans asegs _ _ _ WMR WM6) as WMR6. clear WMR. rename WMR6 into WMR.

pose proof (LAP _ _ _ _ INPD INPG ltac:(intros E; apply (IDBLK (sbd_pi_gain s, a_pg a, 16) ltac:(cbn [sb_blocks In]; tauto)); cbn [blk_addr fst snd]; congruence)) as AP_PD_PG.
assert (DPG : hid (D + Z.of_nat (length bsb) <= a_pg a \/ a_pg a + 16 <= D)) by (unfold hid in *; rewrite Lbsb, BSZ; clear - AP_PD_PG PD1 PD2; lia).
clear AP_PD_PG.
cps_seg_post.
rename ART into ART6. clear MU6 WM6.

apply (rw_cells_split_CB asegs _ _ [] 384 _ [] [32; 320; 32]%nat) in HULL1; [| reflexivity]. cbn [mk_CB_cells app] in HULL1.
destruct (rw_cells_uncons asegs _ _ _ _ HULL1) as (HLZ & HULL1'). destruct (rw_cells_uncons asegs _ _ _ _ HULL1') as (HBODY & HRZ). clear HULL1 HULL1'.
cbn [csize] in HBODY, HRZ.
replace (usp + -1472 + Z.of_nat 32) with (usp + -1440) in HBODY, HRZ by lia.
replace (usp + -1440 + Z.of_nat 320) with (usp + -1120) in HRZ by lia.
destruct HBODY as [_ WRB]. cbn [cells_size csize Nat.add] in WRB. replace (Z.of_nat (320 + 0)) with 320 in WRB by lia.
assert (INPX : In (usp + -1440, 320) (rt_pois RT Σ5)) by (rewrite PO5, PO3, PO2; left; reflexivity).
cps_rt (MEMS Σ5 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 (usp + -1440) 320 z8 lo).
{ f_equal; lia. }
{ unfold checked_dst. rewrite unsigned_lit by (clear - LOR2 USPT ILOW SPW; unfold STACK_WIN in *; lia). split; [intros _; split|split].
- exact (af_acc_pois RT AF Σ5 m6 _ _ ART6 INPX).
- right; right; left. clear - LOWS LOR2 USPT; unfold STACK_WIN, USTACK_TOP in *; lia.
- intros i Hi. left. clear - Hi LOR2 USPT; unfold USTACK_TOP; lia.
- exact WRB. }
{ cps_callok. }
intros c7 Hc7.
cps_unpack Hc7 as (m7 & RS7 & (ART7 & MI7 & WM7 & ST7) & PRES7 & BYZ).
clear Hc.
pres_transport_g PRES7 ltac:(ulc).
lazymatch type of PF with rt_pres_fp ?L ?Fr ?U ?W0 ?m0 m6 =>
assert (PF7 : rt_pres_fp L Fr U W0 m0 m7)
by (apply (pres_fp_trans _ _ _ _ m0 m6 m7 PF);
apply (pres_fp_of_pres_ex_gen _ _ _ _ _ _ _ _ _ m6 m7 PRES7); [intros e He; rewrite LVE5, LVE3, LVE2; exact He | intros e He; rewrite FRE5, FRE3, FRE2; exact He | lia |];
intros x Hx _ Hd; pose proof (SPL x Hx) as SX; clear - SX Hd SSP0 ILOW LOR2; lia) end.
clear PF. rename PF7 into PF.
assert (DOFF : usp + -1440 + 320 <= SH_LO \/ SH_HI <= usp + -1440) by (right; clear - LOR2 LOSH; unfold SH_HI in *; lia).
pose proof (ACCX _ _ _ _ _ m6 m7 A 48 PRES7 INFH DOFF (proj1 IA') ltac:(lia) ltac:(clear - ALO LOR2 USPT; unfold APP_TOP; lia) ACA6) as ACA7.
pose proof (ACCX _ _ _ _ _ m6 m7 OUT 8000 PRES7 INFH DOFF (proj1 IOUT) ltac:(lia) ltac:(clear - OUTLO LOR2 USPT; unfold APP_TOP; lia) ACO6) as ACO7.
assert (EXV : exists ws, length ws = 80%nat /\ rw_cells asegs m7 (usp + -1440) (f32 ws)).
{ apply (rw_cells_CB_f32 asegs m7 _ 80 (repeat z8 (Z.to_nat 320))).
split; [split; [split; [cbn [cell_wf]; rewrite repeat_length; reflexivity| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BYZ]|].
cbn [cells_size csize Nat.add]. exact (wr_at_transport asegs m6 m7 _ _ WRB WM7). }
destruct EXV as (ex7 & LEX7 & EXC7).
pose proof (wmono_trans asegs _ _ _ WMR WM7) as WMR7. clear WMR. rename WMR7 into WMR.
clear DOFF ACA6 ACO6 PRES7 WM7 WRB BYZ ST5 ART6 MI6.

assert (BREP7 : bits_rep asegs m7 A D b).
{ split; [exists rjb; split; [exact Lrjb| unfold bits_cells; exact BOBJ]|].
split; [exists bsb; split; [apply (proj2 (u8arr_rw_CB m7 D bsb)); exact BDAT| exact Hbsb]| exact BSIDE]. }
clear BOBJ BDAT.
assert (A4 : A mod 4 = 0) by (destruct BSIDE as (A8 & _); clear - A8; Z.div_mod_to_equations; lia).
assert (PDS : PD <> S) by (intros E; apply (IDBLK (sbd_blk s, S, SBSTATE_SIZEOF) ltac:(cbn [sb_blocks In]; tauto)); cbn [blk_addr fst snd]; congruence).
assert (INPER : In (usp + -768, 16) (rt_pois RT Σ5)) by (rewrite PO5, PO3, PO2, SPOIS; right; right; right; right; left; reflexivity).
assert (INPX5 : In (usp + -1472 + 32, 4 * 80) (rt_pois RT Σ5)) by (rewrite PO5, PO3, PO2; left; f_equal; lia).
assert (FRN5 : rt_frames RT Σ5 <> []) by (rewrite FRE5, FRE3, FRE2, SFRM; discriminate).
replace (usp + -1440) with (usp + -1472 + 32) in EXC7 by lia.
assert (FA1 : fh <= A) by (clear - IA; tauto). assert (FA2 : A + BITS_SIZEOF <= fh + fs_size kh - 8) by (clear - IA; tauto).
cps_rt (sbl_dA RT AF AF_LIB APO AUN MEMS INNV Σ5 PMc usp lo (usp + -1472) S OUT A D f sf (sbmode_struct (sbd_mode s)) (sbd_frame_size s) 80 sub fh PD ND kh
_ s a b sm pad1 seed ex7 ows3 ler _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m7
FDO MST FRM6 SL4 V296 eq_refl HD SEEDC CFG IDC EFS eq_refl HSID (or_intror (conj EMO (conj eq_refl (conj EFSZ eq_refl)))) eq_refl SM SUB INL ISAL
BREP7 BOK INFH FA1 FA2 A4 ACA7 INPD PD1 ltac:(rewrite BSZ; exact PD2) PDS LERC LLER INPER
OUTC3 LOUT3 (proj1 IOUT) (proj1 (proj2 IOUT)) (proj2 (proj2 IOUT)) ACO7 IAOUT EXC7 ltac:(clear - LEX7; lia) INPX5 POA3 FRN5
ART7 MI7 ST7 LOWS IROOM IU32 USPT eq_refl).
intros c10 (Σ10 & Hc10 & LV10 & FRS10 & SP10 & CR10 & PO10).
destruct (ASTA_unpack RT Σ10 PMc _ c10 Hc10) as (ms10 & PO & Hc'); clear Hc10; cbv beta in PO.
destruct PO as (m10 & xra10 & xt010 & xt110 & xt210 & xa010 & xa110 & xa210 & xa310 & xa410 & xa510 & xa610 & xa710 & xs410 & xt310 & xt410 & xt510 & xt610
& F10 & fc10 & v10 & seed10 & ex10 & -> & FRM10 & (ART10 & MI10 & WM10 & ST10) & PRES10 & SL10 & V296b & V416b & V248b & V256b & V264b
& SEEDC10 & EXC10 & LEX10 & REP10 & OK10 & ACA10).
clear SL4 SEEDC EXC7 LEX7 BREP7 ACA7 FRM6 Hc0.
assert (IAOUTh : hid (A + BITS_SIZEOF <= OUT \/ OUT + 8000 <= A)) by (unfold hid; unfold hidp in IAOUT; exact IAOUT).
pres_transport_g PRES10 ltac:(ulc).
lazymatch type of PF with rt_pres_fp ?L ?Fr ?U ?W0 ?m0 m7 =>
assert (PF10 : rt_pres_fp L Fr U W0 m0 m10)
by (apply (pres_fp_trans _ _ _ _ m0 m7 m10 PF);
apply (pres_fp_of_pres_fp _ _ _ _ _ _ _ _ m7 m10 PRES10); [intros e He; rewrite LVE5, LVE3, LVE2; exact He | intros e He; rewrite FRE5, FRE3, FRE2; exact He | lia |];
intros x Hx Ho; cbn [outside] in Ho |- *; decompose [and] Ho; pose proof (SPL x Hx) as SX;
split; [assumption|]; split; [assumption|]; split; [assumption|];
split; [intros Hin; clear - SX Hin SSP0 ILOW LOR2; lia | exact I]) end.
clear PF. rename PF10 into PF.
pose proof (frame_facts RT AF Σ5 m7 fh kh ART7 INFH) as (_ & _ & _ & _ & FHSH5 & _).
assert (AOFF : A + 48 <= SH_LO \/ SH_HI <= A) by (clear - FHSH5 FA1 FA2; unfold SH_LO, SH_HI, BITS_SIZEOF in *; lia).
assert (OOFF : OUT + 8000 <= SH_LO \/ SH_HI <= OUT) by (clear - FHSH5 IOUT; unfold SH_LO, SH_HI in *; lia).
assert (OFW10 : forall x, SH_LO <= x < SH_HI -> outside [(usp + -608, usp + -160); (S + 132, S + 136); (A, A + BITS_SIZEOF); (usp + -1472 + 32, usp + -1472 + 32 + 4 * 80)] x).
{ intros x Hx. cbn [outside]. unfold hid in SSHD.
split; [clear - Hx LOR2 LOSH USPT; unfold SH_LO, SH_HI in *; lia|]. split; [clear - Hx SSHD; unfold SH_LO, SH_HI in *; lia|].
split; [clear - Hx AOFF; unfold BITS_SIZEOF; lia|]. split; [clear - Hx LOR2 LOSH USPT; unfold SH_LO, SH_HI in *; lia| exact I]. }
pose proof (ACCF _ _ _ _ m7 m10 OUT 8000 PRES10 INFH OFW10 (proj1 IOUT) ltac:(lia) ACO7) as ACO10.
clear OFW10 ACO7 PRES10 FHSH5.
pose proof (wmono_trans asegs _ _ _ WMR WM10) as WMR10. clear WMR WM10. rename WMR10 into WMR.
clear ST7 ART7 MI7.
pose proof LV10 as LVE10. pose proof FRS10 as FRE10. cps_sigma LV10 FRS10 SP10.
cps_hide.

assert (BRT : forall W (mA mB : mem) (bb : bits_st bptr), bits_rep asegs mA A D bb -> munch W mA mB -> wmono asegs mA mB -> bits_ok bb -> sb_buf_size bb = bsz ->
disjoint_from W A 48 -> disjoint_from W D bsz -> bits_rep asegs mB A D bb).
{ intros W mA mB bb ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE) MU WMx OKb SZb DA DD.
assert (LB : Z.of_nat (length bs) = bsz) by (pose proof OKb as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; clear - OK' SZb; lia).
split; [exists rj; split; [exact Lrj|]|]; [| split; [exists bs; split; [|exact Hbs]| exact SIDE]].
- apply (rw_cells_transport asegs W mA mB A _ OBJ MU WMx). unfold bits_cells. cbn [cells_size csize Nat.add]. exact DA.
- apply (proj1 (u8arr_rw_CB mA D bs)) in DAT. apply (proj2 (u8arr_rw_CB mB D bs)).
apply (rw_cells_transport asegs W mA mB D _ DAT MU WMx). cbn [cells_size csize]. rewrite Nat.add_0_r, LB. exact DD. }
assert (BRTP : forall live frames sp (mA mB : mem) (bb : bits_st bptr), rt_pres live frames sp mA mB -> wmono asegs mA mB -> In (fh, kh) frames -> In (PD, ND) live ->
bits_rep asegs mA A D bb -> bits_ok bb -> sb_buf_size bb = bsz -> bits_rep asegs mB A D bb).
{ intros live0 frames0 sp mA mB bb PR WMx INF INP ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE) OKb SZb.
assert (LB : Z.of_nat (length bs) = bsz) by (pose proof OKb as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; clear - OK' SZb; lia).
split; [exists rj; split; [exact Lrj|]|]; [| split; [exists bs; split; [|exact Hbs]| exact SIDE]].
- apply (rw_cells_agree asegs mA mB A _ OBJ); [| exact WMx]. intros x Hx. apply PR. unfold bits_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
right; right; right; left. exists fh, kh. split; [exact INF|]. clear - Hx IA. unfold BITS_SIZEOF in *. lia.
- apply (proj1 (u8arr_rw_CB mA D bs)) in DAT. apply (proj2 (u8arr_rw_CB mB D bs)).
apply (rw_cells_agree asegs mA mB D _ DAT); [| exact WMx]. intros x Hx. apply PR. cbn [cells_size csize] in Hx. rewrite Nat.add_0_r, LB in Hx.
right; right; left. exists PD, ND. split; [exact INP|]. clear - Hx PD1 PD2. lia. }

destruct (af_acc_live RT AF Σ10 m10 S 160 ART10 INL) as (_ & ACS10).
assert (OBS10 : aobj asegs m10 S 160) by (split; [lia|]; split; [clear - SBLO LOR2 USPT; unfold APP_TOP in *; lia| exact ACS10]).
assert (INPX10 : In (usp + -1472 + 32, 4 * 80) (rt_pois RT Σ10)) by (rewrite PO10; exact INPX5).
assert (OBEX10 : aobj asegs m10 (usp + -1472 + 32) (4 * 80))
by (split; [clear - LOR2 LOSH; lia|]; split; [clear - USPT; unfold APP_TOP in *; lia| exact (af_acc_pois RT AF Σ10 m10 _ _ ART10 INPX10)]).
assert (OIMG : IMG_TOP <= OUT) by (clear - FHIMG IOUT; unfold IMG_TOP in *; lia).
assert (SEPSO : S + 160 <= OUT \/ OUT + 8000 <= S) by (unfold hid in SFA; clear - SFA IOUT; lia).
cps_seg (sbl_e12a usp lo (usp + -1472) S OUT A f sf (sbmode_struct (sbd_mode s)) (sbd_frame_size s) 80 sub (usp + -1472 + 32) v10 s a ex10 ows3 xs410 xra10
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F10 fc10 m10
SL10 ltac:(rewrite V248b; reflexivity) HD EFS (or_intror (conj eq_refl EFSZ)) SUB PT HIS
OBS10 ISAL ISPOS SOFF SBLO EXC10 LEX10 OBEX10 ltac:(clear - IU32; Z.div_mod_to_equations; lia) ltac:(clear; lia)
OUTC3 LOUT3 ACO10 OUT0 (proj2 (proj2 IOUT)) OIMG OUTLO ltac:(clear - OUTLO LOR2 USPT; unfold APP_TOP in *; lia) OOFF SEPSO
ltac:(clear - LOR2; lia) ltac:(clear; lia) LOSH ltac:(clear - USPT; lia) MI10).
destruct POST as (m11 & xa011 & xa111 & xa211 & xa311 & xa411 & xa511 & xs311 & F11 & ows11 & -> & MU11 & WM11 & MI11 & OUTC11 & LOUT11).
clear OUTC3 LOUT3 OBS10 ACS10 OBEX10.
destruct (sbl_sbsub_ok b sm (sbd_mode s) (sbd_submodeID s) BOK (or_intror EMO) HSID SM) as (_ & SZSB0).
assert (SZSB : sb_buf_size (sbsub_bits sm b) = bsz) by (rewrite SZSB0; exact BSZ).
assert (REP11 : bits_rep asegs m11 A D (sbsub_bits sm b)).
{ apply (BRT _ m10 m11 _ REP10 MU11 WM11 OK10).
- exact SZSB.
- cbn [disjoint_from]. split; [| exact I]. unfold hidp, BITS_SIZEOF in IAOUT. clear - IAOUT. lia.
- cbn [disjoint_from]. split; [| exact I]. unfold hid in PDFA. clear - PDFA IOUT PD1 PD2. lia. }
clear REP10.
lazymatch type of MU11 with munch ?W _ _ => assert (OF11 : offsh W) by (cbn; unfold hid in OOFF; clear - OOFF; unfold SH_LO, SH_HI in *; lia) end.
pose proof (ACCM _ m10 m11 A 48 ACA10 MU11 OF11 ltac:(lia) ltac:(clear - ALO LOR2 USPT; unfold APP_TOP in *; lia)) as ACA11.
pose proof (ACCM _ m10 m11 OUT 8000 ACO10 MU11 OF11 ltac:(lia) ltac:(clear - OUTLO LOR2 USPT; unfold APP_TOP in *; lia)) as ACO11.
clear ACA10 ACO10 OF11.
pose proof (wmono_trans asegs _ _ _ WMR WM11) as WMR11. clear WMR. rename WMR11 into WMR.
cps_seg_post.
rename ART into ART11. clear MU11 WM11.

assert (WINY : (Z.to_nat (320 + 80 * sub) + Z.to_nat 80 <= length ows11)%nat) by (rewrite LOUT11; clear - SUB; lia).
destruct (sbl_f32_win _ OUT ows11 _ _ OUTC11 WINY) as (OY1 & OY2 & OY3). clear OUTC11 WINY.
replace (OUT + 4 * Z.of_nat (Z.to_nat (320 + 80 * sub))) with (OUT + 4 * sbd_frame_size s + 4 * (80 * sub)) in OY2, OY3 by (rewrite EFSZ; clear - SUB; lia).
replace (OUT + 4 * sbd_frame_size s + 4 * (80 * sub) + 4 * Z.of_nat (Z.to_nat 80)) with (OUT + 4 * sbd_frame_size s + 4 * (80 * sub) + 4 * 80) in OY3 by lia.
assert (LY1 : Z.of_nat (length (firstn (Z.to_nat (320 + 80 * sub)) ows11)) = 320 + 80 * sub) by (rewrite length_firstn, LOUT11; clear - SUB; lia).
assert (LY2 : Z.of_nat (length (firstn (Z.to_nat 80) (skipn (Z.to_nat (320 + 80 * sub)) ows11))) = 80) by (rewrite length_firstn, length_skipn, LOUT11; clear - SUB; lia).
assert (LY3 : Z.of_nat (length (skipn (Z.to_nat (320 + 80 * sub) + Z.to_nat 80) ows11)) = 2000 - 320 - 80 * sub - 80)
by (rewrite length_skipn, LOUT11; clear - SUB; lia).
remember (firstn (Z.to_nat (320 + 80 * sub)) ows11) as y1 eqn:EY1.
remember (firstn (Z.to_nat 80) (skipn (Z.to_nat (320 + 80 * sub)) ows11)) as y2 eqn:EY2.
remember (skipn (Z.to_nat (320 + 80 * sub) + Z.to_nat 80) ows11) as y3 eqn:EY3.
clear EY1 EY2 EY3.
destruct (sbl_f32_win _ (a_msp a) vmsp 0 8 MSPC ltac:(rewrite LMSP; lia)) as (_ & MS2 & MS3). clear MSPC.
replace (a_msp a + 4 * Z.of_nat 0) with (a_msp a) in MS2, MS3 by lia. replace (a_msp a + 4 * Z.of_nat 8) with (a_msp a + 32) in MS3 by lia.
change (skipn 0 vmsp) with vmsp in MS2.
assert (LMS2 : length (firstn 8 vmsp) = 8%nat) by (rewrite length_firstn, LMSP; reflexivity).
assert (LMS3 : length (skipn (0 + 8) vmsp) = 8%nat) by (rewrite length_skipn, LMSP; reflexivity).
remember (firstn 8 vmsp) as vm8 eqn:EVM8. remember (skipn (0 + 8) vmsp) as vm8b eqn:EVM8B. clear EVM8 EVM8B.

assert (INPD5 : In (PD, ND) (rt_live RT Σ5)) by (rewrite <- LVE10; exact INPD).
assert (INXB5 : In (a_exc a, 4 * sbd_subframeSize s) (rt_live RT Σ5)) by (rewrite <- LVE10; exact INXB).
assert (INMS5 : In (a_msp a, 64) (rt_live RT Σ5)) by (rewrite <- LVE10; exact INMSP).
assert (INIQ5 : In (a_iq a, 32) (rt_live RT Σ5)) by (rewrite <- LVE10; exact INIQ).
assert (INER5 : In (a_er a, 16) (rt_live RT Σ5)) by (rewrite <- LVE10; exact INER).
pose proof (LAP _ _ _ _ INPD5 INXB5 ltac:(intros E; apply (IDBLK (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s) ltac:(cbn [sb_blocks In]; tauto)); cbn [blk_addr fst snd]; congruence)) as AP_PD_XB.
pose proof (LAP _ _ _ _ INPD5 INMS5 ltac:(intros E; apply (IDBLK (sbd_mem_sp s, a_msp a, 64) ltac:(cbn [sb_blocks In]; tauto)); cbn [blk_addr fst snd]; congruence)) as AP_PD_MS.
pose proof (LAP _ _ _ _ INPD5 INIQ5 ltac:(intros E; apply (IDBLK (sbd_interp_qlpc s, a_iq a, 32) ltac:(cbn [sb_blocks In]; tauto)); cbn [blk_addr fst snd]; congruence)) as AP_PD_IQ.
pose proof (LAP _ _ _ _ INPD5 INER5 ltac:(intros E; apply (IDBLK (sbd_exc_rms s, a_er a, 16) ltac:(cbn [sb_blocks In]; tauto)); cbn [blk_addr fst snd]; congruence)) as AP_PD_ER.
clear INPD5 INXB5 INMS5 INIQ5 INER5.

assert (YP4 : (OUT + 4 * sbd_frame_size s + 4 * (80 * sub)) mod 4 = 0)
by (replace (OUT + 4 * sbd_frame_size s + 4 * (80 * sub)) with (OUT + (sbd_frame_size s + 80 * sub) * 4) by ring; rewrite Z_mod_plus_full; exact (proj2 (proj2 IOUT))).
assert (OBY : aobj asegs m11 (OUT + 4 * sbd_frame_size s + 4 * (80 * sub)) (4 * 80)).
{ split; [rewrite EFSZ; clear - OUT0 SUB; lia|]. split; [rewrite EFSZ; clear - OUTLO LOR2 USPT SUB; unfold APP_TOP in *; lia|].
apply (acc_sub asegs m11 OUT 8000); [exact ACO11| rewrite EFSZ; clear - SUB; lia | rewrite EFSZ; clear - SUB; lia]. }
destruct (af_acc_live RT AF Σ10 m11 _ _ ART11 INXB) as (_ & ACXB). rewrite EFS in ACXB.
destruct (af_acc_live RT AF Σ10 m11 _ _ ART11 INIQ) as (_ & ACIQ).
destruct (af_acc_live RT AF Σ10 m11 _ _ ART11 INMSP) as (_ & ACMS).
destruct (af_acc_live RT AF Σ10 m11 S 160 ART11 INL) as (_ & ACS11).
assert (OBS11 : aobj asegs m11 S 160) by (split; [lia|]; split; [clear - SBLO LOR2 USPT; unfold APP_TOP in *; lia| exact ACS11]).
assert (OBXB : aobj asegs m11 (a_exc a) (4 * 80)) by (split; [lia|]; split; [rewrite EFS in XBLO; clear - XBLO LOR2 USPT; unfold APP_TOP in *; lia| exact ACXB]).
assert (OBIQ : aobj asegs m11 (a_iq a) 32) by (split; [lia|]; split; [clear - IQLO LOR2 USPT; unfold APP_TOP in *; lia| exact ACIQ]).
assert (OBMS : aobj asegs m11 (a_msp a) 32)
by (split; [lia|]; split; [clear - MSLO LOR2 USPT; unfold APP_TOP in *; lia| apply (acc_sub asegs m11 (a_msp a) 64); [exact ACMS| lia| lia]]).
assert (INPX11 : In (usp + -1472 + 32, 4 * 80) (rt_pois RT Σ10)) by (rewrite PO10; exact INPX5).
assert (OBEX11 : aobj asegs m11 (usp + -1472 + 32) (4 * 80))
by (split; [clear - LOR2 LOSH; lia|]; split; [clear - USPT; unfold APP_TOP in *; lia| exact (af_acc_pois RT AF Σ10 m11 _ _ ART11 INPX11)]).
pose proof (af_client_consts RT AF Σ10 m11 ART11) as CC11.
pose proof (af_live_small RT AF Σ10 m11 _ _ ART11 INXB ltac:(rewrite EFS; lia)) as XBSEG.
pose proof (af_live_small RT AF Σ10 m11 _ _ ART11 INMSP ltac:(lia)) as MSSEG.
unfold hid in XBSH, MSSH, SFA, XBFA, MSFA, IQFA, AP_XB_IQ, AP_XB_MS, AP_IQ_MS, AP_S_XB, AP_S_MS, OOFF.
rewrite EFS in XBLO, XBSH, XBFA, AP_XB_IQ, AP_XB_MS, AP_S_XB, LEXB.
cps_seg (sbl_e12b usp lo (usp + -1472) S OUT A f sf (sbmode_struct (sbd_mode s)) (sbd_frame_size s) 80 sub (usp + -1472 + 32) (a_exc a) (a_iq a) (a_msp a)
(OUT + 4 * sbd_frame_size s + 4 * (80 * sub)) v10 s a ex10 vexc viq vm8 y2 xs311 xs410 xra10 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F11 fc10 m11
SL10 ltac:(rewrite V256b; reflexivity) HD EFS ELPC (or_intror eq_refl) PT eq_refl eq_refl eq_refl OBS11 ISAL ISPOS SOFF SBLO
EXC10 LEX10 OBEX11 ltac:(clear - IU32; Z.div_mod_to_equations; lia) ltac:(clear; lia) ltac:(clear - USPT; lia)
EXBC LEXB OBXB ltac:(clear - AXB; Z.div_mod_to_equations; lia) ltac:(clear - XBSEG; unfold IMG_TOP, SEGTOP_A in *; lia) XBLO
ltac:(clear - XBSH; unfold SH_LO, SH_HI in *; lia)
IQC LIQ OBIQ ltac:(clear - AIQ; Z.div_mod_to_equations; lia) IQLO
MS2 LMS2 OBMS ltac:(clear - AMSP; Z.div_mod_to_equations; lia) ltac:(clear - MSSEG; unfold IMG_TOP, SEGTOP_A in *; lia) ltac:(clear - MSLO; lia)
ltac:(clear - MSSH; unfold SH_LO, SH_HI in *; lia)
OY2 LY2 OBY YP4 ltac:(rewrite EFSZ; clear - OIMG SUB; lia) ltac:(rewrite EFSZ; clear - OUTLO SUB; lia) ltac:(rewrite EFSZ; clear - OOFF SUB; lia)
ltac:(clear - AP_IQ_MS; lia) ltac:(clear - AP_XB_MS; lia) ltac:(clear - AP_XB_IQ; lia)
ltac:(rewrite EFSZ; clear - XBFA IOUT SUB; lia) ltac:(rewrite EFSZ; clear - MSFA IOUT SUB; lia) ltac:(rewrite EFSZ; clear - IQFA IOUT SUB; lia)
ltac:(clear - AP_S_XB; lia) ltac:(clear - AP_S_MS; lia) ltac:(rewrite EFSZ; clear - SFA IOUT SUB; lia)
CC11 ST10 ltac:(clear - LOR2; lia) ltac:(clear; lia) LOSH ltac:(clear - USPT; lia) MI11 FRM10).
destruct POST as (m12 & xra12 & xt012 & xt112 & xt212 & xa012 & xa212 & xa312 & xa412 & xa512 & xa612 & xa712 & xt312 & xt412 & xt512 & xt612 & F12 & fc12
& vexc12 & vm812 & y212 & -> & MU12 & WM12 & MI12 & ST12 & FRM12 & EXBC12 & LEXB12 & MS212 & LMS212 & OY212 & LY212).
clear EXBC MS2 OY2 LEXB LMS2 LY2 OBY OBS11 OBXB OBIQ OBMS OBEX11 CC11 ACXB ACIQ ACMS ACS11 XBSEG MSSEG FRM10.

assert (REP12 : bits_rep asegs m12 A D (sbsub_bits sm b)).
{ apply (BRT _ m11 m12 _ REP11 MU12 WM12 OK10 SZSB).
- cbn [disjoint_from]. unfold hidp, BITS_SIZEOF in IAOUT. rewrite EFSZ. clear - IAOUT MSFA XBFA IA ALO LOR2 SUB. unfold BITS_SIZEOF in *. repeat split; lia.
- cbn [disjoint_from]. unfold hid in PDFA, AP_PD_MS, AP_PD_XB. rewrite EFSZ. clear - PDFA AP_PD_MS AP_PD_XB IOUT PD1 PD2 PDLO LOR2 SUB EFS. repeat split; lia. }
clear REP11.
lazymatch type of MU12 with munch ?W _ _ => assert (OF12 : offsh W)
by (cbn; rewrite EFSZ; clear - OOFF MSSH XBSH LOR2 LOSH USPT SUB; unfold SH_LO, SH_HI in *; repeat split; lia) end.
pose proof (ACCM _ m11 m12 A 48 ACA11 MU12 OF12 ltac:(lia) ltac:(clear - ALO LOR2 USPT; unfold APP_TOP in *; lia)) as ACA12.
pose proof (ACCM _ m11 m12 OUT 8000 ACO11 MU12 OF12 ltac:(lia) ltac:(clear - OUTLO LOR2 USPT; unfold APP_TOP in *; lia)) as ACO12.
clear ACA11 ACO11 OF12.
pose proof (wmono_trans asegs _ _ _ WMR WM12) as WMR12. clear WMR. rename WMR12 into WMR.

assert (ART12 : ART RT Σ10 m12).
{ apply (af_frame RT AF Σ10 m11 m12 lo ART11 LOWS); [| exact WM12].
intros a0 Ha. apply MU12. cbn [outside].
split; [intros Hin; apply Ha; right; right; right; left; exists fh, kh; split; [exact INFH| rewrite EFSZ in Hin; clear - Hin IOUT SUB; lia]|].
split; [intros Hin; apply Ha; right; right; left; exists (a_msp a), 64; split; [exact INMSP| clear - Hin; lia]|].
split; [intros Hin; apply Ha; left; clear - Hin LOR2 USPT; unfold USTACK_TOP in *; lia|].
split; [intros Hin; apply Ha; right; right; left; exists (a_exc a), (4 * sbd_subframeSize s); split; [exact INXB| rewrite EFS; clear - Hin; lia]| exact I]. }
lazymatch type of PF with rt_pres_fp ?L ?Fr ?U ?W0 ?m0 m11 =>
assert (PF12 : rt_pres_fp L Fr U W0 m0 m12)
by (apply (pres_fp_trans _ _ _ _ m0 m11 m12 PF); apply (pres_fp_of_munch _ _ _ _ _ m11 m12 MU12);
intros x Hx Ho; cbn [outside] in Ho |- *; decompose [and] Ho; pose proof (SPL x Hx) as SX;
split; [intros Hin; match goal with H : ~ (OUT <= x < OUT + 8000) |- _ => apply H; rewrite EFSZ in Hin; clear - Hin SUB; lia end|];
split; [intros Hin; match goal with H : ~ (a_msp a <= x < a_msp a + 64) |- _ => apply H; clear - Hin; lia end|];
split; [intros Hin; clear - SX Hin SSP0 ILOW LOR2; lia|];
split; [intros Hin; match goal with H : ~ (a_exc a <= x < a_exc a + 4 * sbd_subframeSize s) |- _ => apply H; rewrite EFS; clear - Hin; lia end| exact I]) end.
clear PF. rename PF12 into PF.

sbl_trm SL10 MU12 WM12 ltac:(unfold hid in *; rewrite ?EFSZ; clear - OUTLO MSLO XBLO LOR2 SUB EFS; repeat split; lia).
sbl_trm EXC10 MU12 WM12 ltac:(unfold hid in *; rewrite ?EFSZ; clear - OUTLO MSLO XBLO LOR2 SUB EFS; repeat split; lia).
sbl_trm LAKC5 MU12 WM12 ltac:(rewrite LLAK5; unfold hid in *; rewrite ?EFSZ; clear - OUTLO MSLO XBLO LOR2 SUB EFS; repeat split; lia).
sbl_trm LIQC4 MU12 WM12 ltac:(rewrite LLIQ4; unfold hid in *; rewrite ?EFSZ; clear - OUTLO MSLO XBLO LOR2 SUB EFS; repeat split; lia).
sbl_trm LPIC MU12 WM12 ltac:(rewrite LLPI; unfold hid in *; rewrite ?EFSZ; clear - OUTLO MSLO XBLO LOR2 SUB EFS; repeat split; lia).
sbl_trm LERC MU12 WM12 ltac:(rewrite LLER; unfold hid in *; rewrite ?EFSZ; clear - OUTLO MSLO XBLO LOR2 SUB EFS; repeat split; lia).
sbl_trm LQC MU12 WM12 ltac:(rewrite LLQ; unfold hid in *; rewrite ?EFSZ; clear - OUTLO MSLO XBLO LOR2 SUB EFS; repeat split; lia).
sbl_trm HLZ MU12 WM12 ltac:(unfold hid in *; rewrite ?EFSZ; clear - OUTLO MSLO XBLO LOR2 SUB EFS; repeat split; lia).
sbl_trm HRZ MU12 WM12 ltac:(unfold hid in *; rewrite ?EFSZ; clear - OUTLO MSLO XBLO LOR2 SUB EFS; repeat split; lia).
sbl_trm HD MU12 WM12 ltac:(unfold hid in *; rewrite ?EFSZ; clear - SFA IOUT AP_S_MS AP_S_XB SBLO LOR2 SUB EFS; repeat split; lia).
sbl_trm FST MU12 WM12 ltac:(unfold hid in *; rewrite ?EFSZ; clear - SFA IOUT AP_S_MS AP_S_XB SBLO LOR2 SUB EFS; repeat split; lia).
sbl_trm PT MU12 WM12 ltac:(unfold hid in *; rewrite ?EFSZ; clear - SFA IOUT AP_S_MS AP_S_XB SBLO LOR2 SUB EFS; repeat split; lia).
sbl_trm LEC MU12 WM12 ltac:(unfold hid in *; rewrite ?EFSZ; clear - SFA IOUT AP_S_MS AP_S_XB SBLO LOR2 SUB EFS; repeat split; lia).
sbl_trm SEEDC10 MU12 WM12 ltac:(unfold hid in *; rewrite ?EFSZ; clear - SFA IOUT AP_S_MS AP_S_XB SBLO LOR2 SUB EFS; repeat split; lia).
sbl_trm CFG MU12 WM12 ltac:(rewrite ?LPAD1; unfold hid in *; rewrite ?EFSZ; clear - SFA IOUT AP_S_MS AP_S_XB SBLO LOR2 SUB EFS; repeat split; lia).
sbl_trm IDC MU12 WM12 ltac:(unfold hid in *; rewrite ?EFSZ; clear - SFA IOUT AP_S_MS AP_S_XB SBLO LOR2 SUB EFS; repeat split; lia).
sbl_trm PAD2C MU12 WM12 ltac:(rewrite ?LPAD2; unfold hid in *; rewrite ?EFSZ; clear - SFA IOUT AP_S_MS AP_S_XB SBLO LOR2 SUB EFS; repeat split; lia).
sbl_trm OQC MU12 WM12 ltac:(rewrite LOQ; unfold hid in *; rewrite ?EFSZ; clear - OQFA IOUT AP_OQ_MS AP_XB_OQ OQLO LOR2 SUB EFS; repeat split; lia).
sbl_trm IQC MU12 WM12 ltac:(rewrite LIQ; unfold hid in *; rewrite ?EFSZ; clear - IQFA IOUT AP_IQ_MS AP_XB_IQ IQLO LOR2 SUB EFS; repeat split; lia).
sbl_trm ERC MU12 WM12 ltac:(rewrite LER; unfold hid in *; rewrite ?EFSZ; clear - ERFA IOUT AP_ER_MS AP_XB_ER ERLO LOR2 SUB EFS; repeat split; lia).
sbl_trm PGC6 MU12 WM12 ltac:(rewrite LPG6; unfold hid in *; rewrite ?EFSZ; clear - PGFA IOUT AP_PG_MS AP_XB_PG PGLO LOR2 SUB EFS; repeat split; lia).
sbl_trm MS3 MU12 WM12 ltac:(rewrite LMS3; unfold hid in *; rewrite ?EFSZ; clear - MSFA IOUT AP_XB_MS MSLO LOR2 SUB EFS; repeat split; lia).
sbl_trm OY1 MU12 WM12 ltac:(rewrite ?LY1; unfold hid in *; rewrite ?EFSZ; clear - MSFA XBFA IOUT LY1 OUTLO LOR2 SUB EFS; repeat split; lia).
sbl_trm OY3 MU12 WM12 ltac:(rewrite ?LY3; unfold hid in *; rewrite ?EFSZ; clear - MSFA XBFA IOUT LY3 OUTLO LOR2 SUB EFS; repeat split; lia).
clear MU12 WM12 ST10 ART11 MI11.
cps_hide.

assert (OUTC12 : rw_cells asegs m12 OUT (f32 (y1 ++ y212 ++ y3))).
{ apply sbl_f32_join_win; [exact OY1| rewrite LY1; replace (OUT + 4 * (320 + 80 * sub)) with (OUT + 4 * sbd_frame_size s + 4 * (80 * sub)) by (rewrite EFSZ; lia); exact OY212|].
rewrite LY1, LY212. replace (OUT + 4 * (320 + 80 * sub) + 4 * 80) with (OUT + 4 * sbd_frame_size s + 4 * (80 * sub) + 4 * 80) by (rewrite EFSZ; lia). exact OY3. }
assert (LOUT12 : length (y1 ++ y212 ++ y3) = 2000%nat) by (rewrite !length_app; clear - LY1 LY3 LY212 SUB; lia).
assert (MSPC12 : rw_cells asegs m12 (a_msp a) (f32 (vm812 ++ vm8b))).
{ rewrite f32_app. apply rw_cells_join; [exact MS212|]. rewrite cells_size_f32, LMS212. replace (a_msp a + Z.of_nat (4 * 8)) with (a_msp a + 32) by lia. exact MS3. }
assert (LMSP12 : length (vm812 ++ vm8b) = 16%nat) by (rewrite length_app, LMS212, LMS3; reflexivity).
clear OY1 OY3 OY212 MS212 MS3 LY1 LY3 LY212 LMS212 LMS3.

destruct (af_acc_live RT AF Σ10 m12 _ _ ART12 INXB) as (_ & ACXB). rewrite EFS in ACXB.
destruct (af_acc_live RT AF Σ10 m12 _ _ ART12 INIQ) as (_ & ACIQ).
destruct (af_acc_live RT AF Σ10 m12 _ _ ART12 INER) as (_ & ACER).
destruct (af_acc_live RT AF Σ10 m12 S 160 ART12 INL) as (_ & ACS12).
assert (OBS12 : aobj asegs m12 S 160) by (split; [lia|]; split; [clear - SBLO LOR2 USPT; unfold APP_TOP in *; lia| exact ACS12]).
assert (OBXB : aobj asegs m12 (a_exc a) (4 * 80)) by (split; [lia|]; split; [clear - XBLO LOR2 USPT; unfold APP_TOP in *; lia| exact ACXB]).
assert (OBIQ : aobj asegs m12 (a_iq a) 32) by (split; [lia|]; split; [clear - IQLO LOR2 USPT; unfold APP_TOP in *; lia| exact ACIQ]).
assert (OBER : aobj asegs m12 (a_er a) 16) by (split; [lia|]; split; [clear - ERLO LOR2 USPT; unfold APP_TOP in *; lia| exact ACER]).
assert (INPAK12 : In (usp + -1056, 32) (rt_pois RT Σ10)) by (rewrite PO10; exact INPAK).
assert (OBAK12 : aobj asegs m12 (usp + -1056) 32)
by (split; [lia|]; split; [clear - USPT; unfold APP_TOP in *; lia| exact (af_acc_pois RT AF Σ10 m12 _ _ ART12 INPAK12)]).
pose proof (af_client_consts RT AF Σ10 m12 ART12) as CC12.
pose proof (af_live_small RT AF Σ10 m12 _ _ ART12 INIQ ltac:(lia)) as IQSEG.
pose proof (af_live_small RT AF Σ10 m12 _ _ ART12 INER ltac:(lia)) as ERSEG.
unfold hid in IQSH, ERSH, AP_IQ_ER, AP_S_IQ, AP_S_ER, AP_XB_ER, AP_XB_IQ.
rewrite EFS in AP_XB_ER.
cps_seg (sbl_e12c usp lo (usp + -1472) S OUT A f sf (sbmode_struct (sbd_mode s)) (sbd_frame_size s) 80 sub (a_exc a) (a_iq a) (a_er a) (usp + -1056) v10 s a
vexc12 viq ver aks5 xra12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F12 fc12 m12
SL10 HD EFS ELPC ENSF (or_intror eq_refl) SUB PT eq_refl eq_refl eq_refl OBS12 ISAL ISPOS SOFF SBLO
EXBC12 LEXB12 OBXB ltac:(clear - AXB; Z.div_mod_to_equations; lia) XBLO
IQC LIQ OBIQ ltac:(clear - AIQ; Z.div_mod_to_equations; lia) ltac:(clear - IQSEG; unfold IMG_TOP, SEGTOP_A in *; lia) IQLO
ltac:(clear - IQSH; unfold SH_LO, SH_HI in *; lia)
ERC LER OBER ltac:(clear - AER; Z.div_mod_to_equations; lia) ltac:(clear - ERSEG; unfold IMG_TOP, SEGTOP_A in *; lia) ERLO
ltac:(clear - ERSH; unfold SH_LO, SH_HI in *; lia)
ltac:(clear - AP_IQ_ER; lia) ltac:(clear - AP_S_IQ; lia) ltac:(clear - AP_S_ER; lia) ltac:(clear - AP_XB_IQ; lia) ltac:(clear - AP_XB_ER; lia)
eq_refl LAKC5 LLAK5 OBAK12 CC12 ST12 ltac:(clear - LOR2; lia) ltac:(clear; lia) LOSH ltac:(clear - USPT; lia) IU32 MI12 FRM12).
destruct POST as (m13 & xt013 & xt113 & xt213 & xa213 & xa313 & xa413 & xa513 & xa613 & xa713 & xt313 & xt413 & xt513 & xt613 & F13 & fc13 & viq13 & ver13
& -> & MU13 & WM13 & MI13 & ST13 & FRM13 & IQC13 & LIQ13 & ERC13 & LER13).
clear IQC LIQ ERC LER OBS12 OBXB OBIQ OBER OBAK12 CC12 ACXB ACIQ ACER ACS12 IQSEG ERSEG INPAK12 FRM12.
assert (REP13 : bits_rep asegs m13 A D (sbsub_bits sm b)).
{ apply (BRT _ m12 m13 _ REP12 MU13 WM13 OK10 SZSB).
- cbn [disjoint_from]. unfold hid in IQFA, ERFA. clear - IQFA ERFA IA ALO LOR2. unfold BITS_SIZEOF in *. repeat split; lia.
- cbn [disjoint_from]. unfold hid in AP_PD_IQ, AP_PD_ER. clear - AP_PD_IQ AP_PD_ER PD1 PD2 PDLO LOR2. repeat split; lia. }
clear REP12.
lazymatch type of MU13 with munch ?W _ _ => assert (OF13 : offsh W)
by (cbn; clear - IQSH ERSH LOR2 LOSH USPT; unfold SH_LO, SH_HI in *; repeat split; lia) end.
pose proof (ACCM _ m12 m13 A 48 ACA12 MU13 OF13 ltac:(lia) ltac:(clear - ALO LOR2 USPT; unfold APP_TOP in *; lia)) as ACA13.
pose proof (ACCM _ m12 m13 OUT 8000 ACO12 MU13 OF13 ltac:(lia) ltac:(clear - OUTLO LOR2 USPT; unfold APP_TOP in *; lia)) as ACO13.
clear ACA12 ACO12 OF13.
pose proof (wmono_trans asegs _ _ _ WMR WM13) as WMR13. clear WMR. rename WMR13 into WMR.

assert (ART13 : ART RT Σ10 m13).
{ apply (af_frame RT AF Σ10 m12 m13 lo ART12 LOWS); [| exact WM13].
intros a0 Ha. apply MU13. cbn [outside].
split; [intros Hin; apply Ha; right; right; left; exists (a_iq a), 32; split; [exact INIQ| clear - Hin; lia]|].
split; [intros Hin; apply Ha; right; right; left; exists (a_er a), 16; split; [exact INER| clear - Hin; lia]|].
split; [intros Hin; apply Ha; left; clear - Hin LOR2 USPT; unfold USTACK_TOP in *; lia| exact I]. }
lazymatch type of PF with rt_pres_fp ?L ?Fr ?U ?W0 ?m0 m12 =>
assert (PF13 : rt_pres_fp L Fr U W0 m0 m13)
by (apply (pres_fp_trans _ _ _ _ m0 m12 m13 PF); apply (pres_fp_of_munch _ _ _ _ _ m12 m13 MU13);
intros x Hx Ho; cbn [outside] in Ho |- *; decompose [and] Ho; pose proof (SPL x Hx) as SX;
split; [intros Hin; match goal with H : ~ (a_iq a <= x < a_iq a + 32) |- _ => apply H; exact Hin end|];
split; [intros Hin; match goal with H : ~ (a_er a <= x < a_er a + 16) |- _ => apply H; exact Hin end|];
split; [intros Hin; clear - SX Hin SSP0 ILOW LOR2; lia| exact I]) end.
clear PF. rename PF13 into PF.
sbl_trm SL10 MU13 WM13 ltac:(clear - IQLO ERLO LOR2; repeat split; lia).
sbl_trm EXC10 MU13 WM13 ltac:(clear - IQLO ERLO LOR2; repeat split; lia).
sbl_trm LAKC5 MU13 WM13 ltac:(rewrite LLAK5; clear - IQLO ERLO LOR2; repeat split; lia).
sbl_trm LIQC4 MU13 WM13 ltac:(rewrite LLIQ4; clear - IQLO ERLO LOR2; repeat split; lia).
sbl_trm LPIC MU13 WM13 ltac:(rewrite LLPI; clear - IQLO ERLO LOR2; repeat split; lia).
sbl_trm LERC MU13 WM13 ltac:(rewrite LLER; clear - IQLO ERLO LOR2; repeat split; lia).
sbl_trm LQC MU13 WM13 ltac:(rewrite LLQ; clear - IQLO ERLO LOR2; repeat split; lia).
sbl_trm HLZ MU13 WM13 ltac:(clear - IQLO ERLO LOR2; repeat split; lia).
sbl_trm HRZ MU13 WM13 ltac:(clear - IQLO ERLO LOR2; repeat split; lia).
sbl_trm HD MU13 WM13 ltac:(unfold hid in *; clear - AP_S_IQ AP_S_ER SBLO LOR2; repeat split; lia).
sbl_trm FST MU13 WM13 ltac:(unfold hid in *; clear - AP_S_IQ AP_S_ER SBLO LOR2; repeat split; lia).
sbl_trm PT MU13 WM13 ltac:(unfold hid in *; clear - AP_S_IQ AP_S_ER SBLO LOR2; repeat split; lia).
sbl_trm LEC MU13 WM13 ltac:(unfold hid in *; clear - AP_S_IQ AP_S_ER SBLO LOR2; repeat split; lia).
sbl_trm SEEDC10 MU13 WM13 ltac:(unfold hid in *; clear - AP_S_IQ AP_S_ER SBLO LOR2; repeat split; lia).
sbl_trm CFG MU13 WM13 ltac:(rewrite ?LPAD1; unfold hid in *; clear - AP_S_IQ AP_S_ER SBLO LOR2; repeat split; lia).
sbl_trm IDC MU13 WM13 ltac:(unfold hid in *; clear - AP_S_IQ AP_S_ER SBLO LOR2; repeat split; lia).
sbl_trm PAD2C MU13 WM13 ltac:(rewrite ?LPAD2; unfold hid in *; clear - AP_S_IQ AP_S_ER SBLO LOR2; repeat split; lia).
sbl_trm EXBC12 MU13 WM13 ltac:(unfold hid in *; clear - AP_XB_IQ AP_XB_ER XBLO LOR2 EFS LEXB12; repeat split; lia).
sbl_trm OQC MU13 WM13 ltac:(rewrite LOQ; unfold hid in *; clear - AP_OQ_IQ AP_OQ_ER OQLO LOR2; repeat split; lia).
sbl_trm PGC6 MU13 WM13 ltac:(rewrite LPG6; unfold hid in *; clear - AP_IQ_PG AP_PG_ER PGLO LOR2; repeat split; lia).

sbl_trn MSPC12 MU13 WM13 ltac:(rewrite cells_size_f32, LMSP12; unfold hid in *; clear - AP_IQ_MS AP_ER_MS MSLO LOR2; repeat split; lia).
sbl_trn OUTC12 MU13 WM13 ltac:(rewrite cells_size_f32, LOUT12; unfold hid in *; clear - IQFA ERFA IOUT OUTLO LOR2; repeat split; lia).
clear MU13 WM13 ST12 ART12 MI12.
cps_hide.

assert (TOPV : v_416 v10 = Z_to_bv 64 (sbl_v416A (usp + -1472) sm)) by exact V416b.
assert (BOTV : v_264 v10 = Z_to_bv 64 (usp + -1088)) by (rewrite V264b; reflexivity).
assert (DCB0 : sm_double_codebook sm = 0).
{ destruct (sb_submode_cases (sbd_mode s) (sbd_submodeID s) sm (or_intror EMO) HSID SM) as [(E & _) | (_ & _ & ->)]; [rewrite EMO in E; discriminate E| reflexivity]. }
assert (TOPB : usp + -1472 <= sbl_v416A (usp + -1472) sm <= usp + -1472 /\ sbl_v416A (usp + -1472) sm mod 8 = 0).
{ unfold sbl_v416A. rewrite DCB0. cbn [Z.eqb]. split; [lia | clear - IU32; Z.div_mod_to_equations; lia]. }
cps_rt (AUNlo Σ10 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m13 (sbl_v416A (usp + -1472) sm) (usp + -1088) lo).
{ intros e He. rewrite PO10, PO5, PO3, PO2 in He. destruct He as [<-|He].
- left. unfold pz_lo, pz_hi. cbn [fst snd]. rewrite RR1. clear - TOPB. lia.
- right. exact (POA1 e He). }
{ unfold call_ok. rewrite unsigned_lit by (clear - LOR2 LOSH USPT; unfold USTACK_TOP in *; lia).
split; [exact ST13|]. split; [exact LOWS|]. split; [clear - LOR2; unfold RT_STACK; lia|]. split; [clear - USPT; unfold USTACK_TOP in *; lia|].
clear - IU32; Z.div_mod_to_equations; lia. }
intros c14 (Σ14 & Hc14 & PO14 & LV14 & FRS14 & SP14 & CR14).
destruct (ASTA_unpack RT Σ14 PMc _ c14 Hc14) as (ms14 & PO & Hc'); clear Hc14; cbv beta in PO.
destruct PO as (m14 & v014 & RS14 & (ART14 & MI14 & WM14 & ST14) & PRES14 & ACT14).
cps_ret RS14.
rewrite unsigned_lit in ST14, PRES14 by (clear - LOR2 LOSH USPT; unfold USTACK_TOP in *; lia).
clear Hc.
pres_transport_g PRES14 ltac:(ulc).
lazymatch type of PF with rt_pres_fp ?L ?Fr ?U ?W0 ?m0 m13 =>
assert (PF14 : rt_pres_fp L Fr U W0 m0 m14)
by (apply (pres_fp_trans _ _ _ _ m0 m13 m14 PF);
apply (pres_fp_mono _ _ _ _ _ _ _ m13 m14 (pres_fp_of_pres _ _ _ W0 m13 m14 PRES14));
[intros e He; rewrite LVE10, LVE5, LVE3, LVE2; exact He | intros e He; rewrite FRE10, FRE5, FRE3, FRE2; exact He | lia]) end.
clear PF. rename PF14 into PF.
pose proof (ACT14 A 48 ACA13 ltac:(clear - ALO LOR2 USPT; unfold USTACK_TOP in *; lia) ltac:(left; clear - ALO LOR2 TOPB; lia)) as ACA14.
pose proof (ACT14 OUT 8000 ACO13 ltac:(clear - OUTLO LOR2 USPT; unfold USTACK_TOP in *; lia) ltac:(left; clear - OUTLO LOR2 TOPB; lia)) as ACO14.
assert (REP14 : bits_rep asegs m14 A D (sbsub_bits sm b)) by exact (BRTP _ _ _ m13 m14 _ PRES14 WM14 INFH INPD REP13 OK10 SZSB).
clear ACA13 ACO13 ACT14 REP13 PRES14.
pose proof (wmono_trans asegs _ _ _ WMR WM14) as WMR14. clear WMR WM14. rename WMR14 into WMR.
clear ST13 ART13 MI13.
pose proof LV14 as LVE14. pose proof FRS14 as FRE14. cps_sigma LV14 FRS14 SP14.

remember (y1 ++ y212 ++ y3) as ows12 eqn:EOWS12. remember (vm812 ++ vm8b) as vms12 eqn:EVMS12. clear EOWS12 EVMS12.

pose proof (stk_release asegs m14 lo (usp + -1472) _ ST14 HLZ ltac:(clear - LOR2; lia)) as STa. cbn [cells_size csize Nat.add] in STa.
replace (usp + -1472 + Z.of_nat 32) with (usp + -1472 + 32) in STa by lia.
pose proof (stk_release asegs m14 lo (usp + -1472 + 32) _ STa EXC10 ltac:(clear - LOR2; lia)) as STb. rewrite cells_size_f32 in STb.
replace (usp + -1472 + 32 + Z.of_nat (4 * length ex10)) with (usp + -1120) in STb by (clear - LEX10; lia).
pose proof (stk_release asegs m14 lo (usp + -1120) _ STb HRZ ltac:(clear - LOR2; lia)) as STc. cbn [cells_size csize Nat.add] in STc.
replace (usp + -1120 + Z.of_nat 32) with (usp + -1088) in STc by lia.
clear STa STb ST14 HLZ HRZ EXC10 LEX10.
destruct (af_acc_live RT AF Σ14 m14 S 160 ART14 INL) as (_ & ACS14).
assert (OBS14 : aobj asegs m14 S 160) by (split; [lia|]; split; [clear - SBLO LOR2 USPT; unfold APP_TOP in *; lia| exact ACS14]).
cps_seg (sbl_e13 usp (usp + -1472) lo S OUT A f sf (sbmode_struct (sbd_mode s)) (sbd_frame_size s) sub v10 s a gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m14
SL10 BOTV V296b HD ENSF SUB OBS14 ISAL ISPOS SOFF SBLO ltac:(clear - LOR2; lia) LOSH ltac:(clear - USPT; lia) MI14 FRM13).
destruct POST as (m15 & k15 & F15 & fc15 & HOUT & MU15 & WM15 & MI15 & FRM15 & SL15).
clear OBS14 ACS14 SL10.
lazymatch type of MU15 with munch ?W _ _ => assert (OF15 : offsh W) by (cbn; clear - LOR2 LOSH USPT; unfold SH_LO, SH_HI in *; lia) end.
assert (REP15 : bits_rep asegs m15 A D (sbsub_bits sm b)).
{ apply (BRT _ m14 m15 _ REP14 MU15 WM15 OK10 SZSB); cbn [disjoint_from]; (split; [| exact I]); clear - ALO PD1 PD2 PDLO LOR2; unfold BITS_SIZEOF in *; lia. }
clear REP14.
pose proof (ACCM _ m14 m15 A 48 ACA14 MU15 OF15 ltac:(lia) ltac:(clear - ALO LOR2 USPT; unfold APP_TOP in *; lia)) as ACA15.
pose proof (ACCM _ m14 m15 OUT 8000 ACO14 MU15 OF15 ltac:(lia) ltac:(clear - OUTLO LOR2 USPT; unfold APP_TOP in *; lia)) as ACO15.
clear ACA14 ACO14 OF15.
pose proof (wmono_trans asegs _ _ _ WMR WM15) as WMR15. clear WMR. rename WMR15 into WMR.
cps_hide.
cps_seg_post.
rename ART into ART15. clear MU15 WM15.

assert (SIG14 : rt_live RT Σ14 = live /\ rt_frames RT Σ14 = (f, 0%nat) :: frames /\ rt_sp0 RT Σ14 = sp0 /\ rt_credit RT Σ14 = cr
/\ rt_pois RT Σ14 = [(usp + -1056, 32); (usp + -960, 32); (usp + -864, 32); (usp + -768, 16); (usp + -672, 16)] ++ pois).
{ rewrite LVE14, LVE10, LVE5, LVE3, LVE2, SLIVE. rewrite FRE14, FRE10, FRE5, FRE3, FRE2, SFRM. rewrite SP14, SP10, SP5, SP3, SP2, SSP0.
rewrite CR14, CR10, CR5, CR3, CR2, SCR. rewrite PO14, PO10, PO5, PO3, PO2.
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
rewrite pois_drop_cons_below by (unfold pz_lo; cbn [fst]; lia). rewrite (pois_drop_above _ _ POA1). exact SPOIS. }
assert (PFX : rt_pres_fp live ((f, 0%nat) :: frames) (usp + -1088)
[(usp + -608, usp + -160); (usp + -960, usp + -928); (usp + -1056, usp + -1024); (S + 132, S + 136); (a_exc a, a_exc a + 4 * sbd_subframeSize s);
(a_iq a, a_iq a + 32); (a_msp a, a_msp a + 64); (a_pg a, a_pg a + 16); (a_er a, a_er a + 16); (OUT, OUT + 8000); (A, A + BITS_SIZEOF)] mR m15)
by (rewrite <- SLIVE, <- SFRM; exact PF).
assert (LMEM : sb_loopmem RT {| x_usp := usp; x_lo := lo; x_gp := gp; x_S := S; x_OUT := OUT; x_A := A; x_D := D; x_s := s; x_a := a; x_bsz := bsz; x_f := f; x_sf := sf;
x_fh := fh; x_kh := kh; x_PD := PD; x_ND := ND; x_live := live; x_frames := frames; x_sp0 := sp0; x_cr := cr; x_pois := pois |}
mR Σ14 m15 (sbsub_bits sm b) (sbv_296 v10 (Z_to_bv 64 (sub + 1)))).
{ exists le, seed10, pad1, pad2, lpi, ler, lq, liq4, aks5, vexc12, voq, viq13, vms12, vpg6, ver13, ows12.
split; [exact ART15|]. split; [exact MI15|]. split; [exact STc|]. split; [exact PFX|]. split; [exact WMR|]. split; [exact SL15|].
split; [exact LPIC|]. split; [exact LLPI|]. split; [exact LERC|]. split; [exact LLER|]. split; [exact LQC|]. split; [exact LLQ|].
split; [exact LIQC4|]. split; [exact LLIQ4|]. split; [exact LAKC5|]. split; [exact LLAK5|].
split; [exact (conj HD (conj FST (conj PT (conj LEC (conj SEEDC10 (conj CFG (conj IDC PAD2C)))))))|]. split; [exact LPAD1|]. split; [exact LPAD2|].
split; [exact EXBC12|]. split; [exact (eq_trans LEXB12 (eq_sym EFS))|]. split; [exact OQC|]. split; [exact LOQ|]. split; [exact IQC13|]. split; [exact LIQ13|].
split; [exact MSPC12|]. split; [exact LMSP12|]. split; [exact PGC6|]. split; [exact LPG6|]. split; [exact ERC13|]. split; [exact LER13|].
split; [exact OUTC12|]. split; [exact LOUT12|]. split; [exact REP15|]. split; [exact OK10|]. split; [exact SZSB|]. split; [exact ACA15| exact ACO15]. }
unfold hid in HOUT. destruct HOUT as [(SUB3 & ->) | (SUB3 & ->)].
+ apply Hk. left. split; [exact SUB3|].
exists Σ14, F15, fc15, m15, k15, (sbv_296 v10 (Z_to_bv 64 (sub + 1))).
split; [exact Hc|]. split; [exact FRM15|]. split; [exact SIG14|]. split; [exact LMEM| reflexivity].
+ apply Hk. right. split; [exact SUB3|].
exists Σ14, F15, fc15, m15, k15, (sbv_296 v10 (Z_to_bv 64 (sub + 1))).
split; [exact Hc|]. split; [exact FRM15|]. split; [exact SIG14|]. split; [exact LMEM|].
cbn [v_416 sbv_296 x_s x_usp]. rewrite V416b. f_equal. unfold sbl_v416A, sb_top_stale. rewrite EMO. cbn [sb_exc_hull]. lia.

Qed.
End SBL.
