(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s X05u X05t
X081 X05l X05m X09f X06d X069 X05w X063 X082 X08y X0b1 X0b0 X068
X0ay X0az X0ar X07l X0be.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0yr X0wl X0wn X0wm X0ys X0x2 X0wp X0yt X0zq X11l X11k X0x1 X11i X11c X0yd X121.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wp OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11i OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yd OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X121.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac simpl_sizes ::=
rewrite ?X06d.sb_cells_size, ?cells_size_sbp_hdr, ?cells_size_sbp_ptrs, ?cells_size_sbp_cfg, ?cells_size_lost_frame, ?app_length, ?cells_size_app, ?cells_size_f32, ?length_f32;
cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length, ?cells_size_f32, ?length_f32; cbn [length].

Tactic Notation "sb_unpack" hyp(X) "as" simple_intropattern(P) := let Xc := fresh "Xc" in pose proof X as Xc; apply sb_pieces_iff in Xc; destruct Xc as P.

Lemma lsl_live_apart : forall (RT : rt_sig), art_facts RT -> forall (Σ : rts RT) (m : mem) p1 n1 p2 n2, ART RT Σ m -> In (p1, n1) (rt_live RT Σ) -> In (p2, n2) (rt_live RT Σ) -> p1 <> p2 ->
p1 + n1 <= p2 \/ p2 + n2 <= p1.
Proof.
intros RT AF Σ m p1 n1 p2 n2 ART0 H1 H2 NE. destruct (in_split _ _ H1) as (l1 & l2 & E).
apply (af_live_disj RT AF Σ m p1 n1 p2 n2 l1 l2 ART0 E). rewrite E in H2. apply in_app_iff in H2. apply in_app_iff.
destruct H2 as [H2|[H2|H2]]; [left; exact H2| exfalso; apply NE; congruence| right; exact H2].
Qed.

Section SbLost.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis QMF16 : forall N, N = 320 \/ N = 640 -> qmf_synth_cps16 RT N.

Local Ltac trm MU WM H tacD :=
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
Local Ltac tr1 PRES WM H tacA tacO :=
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

Theorem sb_decode_lost_ok : sb_decode_lost_cps RT.
Proof using AF QMF16.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S OUT lo fh kh s a j ows
FDO MST EA0 EA1 EA2 ETP X JOK INV BUFS S8 SPOS AL NDB LIVEB OC LOWS INF IFO POA ART0 MI0 FRM ST0 LOW LOR SPT SPA.
subst a0 a1 a2 tp.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.

pose proof INV as (IM & IFS & IFFS & ISF & INS & ILPC & IFST & ISR & ILE & IES & IID & IIS).
assert (FSV : sbd_frame_size s = 160 \/ sbd_frame_size s = 320) by (rewrite IFS; destruct IM as [-> | ->]; cbn; auto).
pose proof JOK as (JP1 & JP2 & JG0 & JG1 & JEXC & JOQ & JIQ & JMSP & JPG & JER).
destruct BUFS as (G0C & G1C & EXC & OQC & IQC & MSPC & PGC & ERC).
pose proof AL as (G08 & G18 & EX8 & OQ8 & IQ8 & MSP8 & PG8 & ER8).
pose proof IFO as (FO1 & FO2 & ACO & OAL).

assert (INS0 : In (S, 160) (rt_live RT Σ)) by exact (LIVEB (sbd_blk s, S, SBSTATE_SIZEOF) ltac:(cbn [sb_blocks In]; left; reflexivity)).
assert (ING0 : In (a_g0 a, 256) (rt_live RT Σ)) by exact (LIVEB (sbd_g0_mem s, a_g0 a, 256) ltac:(cbn [sb_blocks In]; do 1 right; left; reflexivity)).
assert (ING1 : In (a_g1 a, 256) (rt_live RT Σ)) by exact (LIVEB (sbd_g1_mem s, a_g1 a, 256) ltac:(cbn [sb_blocks In]; do 2 right; left; reflexivity)).
assert (INEX : In (a_exc a, 4 * sbd_subframeSize s) (rt_live RT Σ))
by exact (LIVEB (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s) ltac:(cbn [sb_blocks In]; do 3 right; left; reflexivity)).
assert (INOQ : In (a_oq a, 32) (rt_live RT Σ)) by exact (LIVEB (sbd_old_qlsp s, a_oq a, 32) ltac:(cbn [sb_blocks In]; do 4 right; left; reflexivity)).
assert (INIQ : In (a_iq a, 32) (rt_live RT Σ)) by exact (LIVEB (sbd_interp_qlpc s, a_iq a, 32) ltac:(cbn [sb_blocks In]; do 5 right; left; reflexivity)).
assert (INPG : In (a_pg a, 16) (rt_live RT Σ)) by exact (LIVEB (sbd_pi_gain s, a_pg a, 16) ltac:(cbn [sb_blocks In]; do 6 right; left; reflexivity)).
assert (INER : In (a_er a, 16) (rt_live RT Σ)) by exact (LIVEB (sbd_exc_rms s, a_er a, 16) ltac:(cbn [sb_blocks In]; do 7 right; left; reflexivity)).
assert (INMS : In (a_msp a, 64) (rt_live RT Σ)) by exact (LIVEB (sbd_mem_sp s, a_msp a, 64) ltac:(cbn [sb_blocks In]; do 8 right; left; reflexivity)).
assert (NDA0 : List.NoDup [S; a_g0 a; a_g1 a; a_exc a; a_oq a; a_iq a; a_pg a; a_er a; a_msp a]) by exact NDB.
assert (NDN : forall i0 j0 : nat, (i0 < 9)%nat -> (j0 < 9)%nat -> i0 <> j0 ->
nth i0 [S; a_g0 a; a_g1 a; a_exc a; a_oq a; a_iq a; a_pg a; a_er a; a_msp a] 0 <> nth j0 [S; a_g0 a; a_g1 a; a_exc a; a_oq a; a_iq a; a_pg a; a_er a; a_msp a] 0)
by (intros i0 j0 Hi Hj Hne E; apply Hne; exact (proj1 (NoDup_nth _ 0) NDA0 i0 j0 Hi Hj E)).

destruct (live_below_lo RT AF Σ m S 160 lo ART0 INS0 LOW) as (SP0 & SLO & LOS).
destruct (live_below_lo RT AF Σ m _ _ lo ART0 ING0 LOW) as (G0P & G0LO & _).
destruct (live_below_lo RT AF Σ m _ _ lo ART0 ING1 LOW) as (G1P & G1LO & _).
destruct (live_below_lo RT AF Σ m _ _ lo ART0 INIQ LOW) as (IQP & IQLO & _).
destruct (live_below_lo RT AF Σ m _ _ lo ART0 INMS LOW) as (MSP & MSLO & _).
destruct (frame_below_lo RT AF Σ m fh kh lo ART0 INF LOW) as (FHLO & _ & _).
pose proof (frame_facts RT AF Σ m fh kh ART0 INF) as (FH0 & FH64 & FHIMG & _ & FHSH & _).
pose proof (live_facts RT AF Σ m S 160 ART0 INS0) as (_ & _ & _ & SSH0).
pose proof (live_facts RT AF Σ m _ _ ART0 INMS) as (_ & _ & _ & MSH0).
pose proof (af_live_small RT AF Σ m S 160 ART0 INS0 ltac:(clear; lia)) as SIMG.
pose proof (af_live_small RT AF Σ m _ _ ART0 INMS ltac:(clear; lia)) as MIMG.
destruct (frame_live_apart RT AF Σ m fh kh S 160 ART0 INF INS0) as (FS0 & _).
destruct (frame_live_apart RT AF Σ m fh kh _ _ ART0 INF INIQ) as (FIQ & _).
destruct (frame_live_apart RT AF Σ m fh kh _ _ ART0 INF INMS) as (FMS & _).
pose proof (lsl_live_apart RT AF Σ m _ _ _ _ ART0 INS0 INIQ (NDN 0%nat 5%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as SIQ.
pose proof (lsl_live_apart RT AF Σ m _ _ _ _ ART0 INS0 INMS (NDN 0%nat 8%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as SMS.
pose proof (lsl_live_apart RT AF Σ m _ _ _ _ ART0 INIQ INMS (NDN 5%nat 8%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as IQMS.
pose proof (fun a0 => aclient_split RT AF Σ m usp a0 ART0) as SPL.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
destruct (af_acc_live RT AF Σ m S 160 ART0 INS0) as (_ & ACS).
destruct (af_acc_live RT AF Σ m _ _ ART0 INIQ) as (_ & ACIQ).
destruct (af_acc_live RT AF Σ m _ _ ART0 INMS) as (_ & ACMS).
cps_hide.
set (fsz := sbd_frame_size s) in *.
set (Y := OUT + 4 * fsz).
assert (FSN : Z.of_nat (Z.to_nat fsz) = fsz) by (clear - FSV; unfold hid in *; lia).

apply (f32_split bsegs m OUT ows (Z.to_nat fsz)) in OC; [| rewrite LOWS; clear - FSV; unfold hid in *; lia].
destruct OC as (OCa & OCb). rewrite FSN in OCb.
apply (f32_split bsegs m (OUT + 4 * fsz) (skipn (Z.to_nat fsz) ows) (Z.to_nat fsz)) in OCb; [| rewrite length_skipn, LOWS; clear - FSV; unfold hid in *; lia].
destruct OCb as (OCy & OCc). rewrite FSN in OCc. fold Y in OCy.
replace (OUT + 4 * fsz + 4 * fsz) with (OUT + 8 * fsz) in OCc by (clear; unfold hid in *; lia).
assert (LYW : length (firstn (Z.to_nat fsz) (skipn (Z.to_nat fsz) ows)) = Z.to_nat fsz)
by (rewrite length_firstn, length_skipn, LOWS; clear - FSV; unfold hid in *; lia).
destruct (firstn (Z.to_nat fsz) (skipn (Z.to_nat fsz) ows)) as [|cw rest] eqn:EYW; [cbn [length] in LYW; clear - LYW FSV; unfold hid in *; lia|].
assert (LREST : Z.of_nat (length rest) + 1 = fsz) by (cbn [length] in LYW; clear - LYW FSV; unfold hid in *; lia).
set (wa := firstn (Z.to_nat fsz) ows) in OCa. set (wc := skipn (Z.to_nat fsz) (skipn (Z.to_nat fsz) ows)) in OCc.
assert (LWA : Z.of_nat (length wa) = fsz) by (unfold wa; rewrite length_firstn, LOWS; clear - FSV; unfold hid in *; lia).
assert (LWC : Z.of_nat (length wc) = 2000 - 2 * fsz) by (unfold wc; rewrite !length_skipn, LOWS; clear - FSV; unfold hid in *; lia).

apply (f32_split bsegs m (a_msp a) (sj_msp j) 8) in MSPC; [| rewrite JMSP; clear; unfold hid in *; lia]. destruct MSPC as (MSP1 & MSP2).

sb_unpack X as (HD & FST & PT & LE & SEED & CFG & IDC & PAD). clear X.

assert (OBS : aobj bsegs m S 160) by (split; [clear - SP0; unfold hid in *; lia|]; split; [clear - SLO LOR SPT; unfold hid in *; unfold APP_TOP, USTACK_TOP, RT_STACK, SBLOST_STACK in *; lia| exact ACS]).
assert (OBY : aobj bsegs m Y (4 * fsz))
by (split; [unfold Y; clear - FO1 FH0 FSV; unfold hid in *; lia|]; split; [unfold Y; clear - FO2 FHLO LOR SPT FSV; unfold hid in *; unfold APP_TOP, USTACK_TOP, RT_STACK, SBLOST_STACK in *; lia|
apply (acc_sub bsegs m OUT 8000 Y (4 * fsz) ACO); unfold Y; clear - FSV; unfold hid in *; lia]).
assert (OBQ : aobj bsegs m (a_iq a) 32) by (split; [clear - IQP; unfold hid in *; lia|]; split; [clear - IQLO LOR SPT; unfold hid in *; unfold APP_TOP, USTACK_TOP, RT_STACK, SBLOST_STACK in *; lia| exact ACIQ]).
assert (OBM : aobj bsegs m (a_msp a) 32)
by (split; [clear - MSP; unfold hid in *; lia|]; split; [clear - MSLO LOR SPT; unfold hid in *; unfold APP_TOP, USTACK_TOP, RT_STACK, SBLOST_STACK in *; lia| exact (acc_sub bsegs m (a_msp a) 64 (a_msp a) 32 ACMS ltac:(clear; unfold hid in *; lia) ltac:(clear; unfold hid in *; lia))]).

cps_seg (lost_w1 usp lo S OUT Y fsz s a (Z_to_bv 64 (sbd_first s)) (sj_last_ener j) (sj_seed j) cw rest (sj_iq j) (firstn 8 (sj_msp j))
ra gp (Z_to_bv 64 0x638c98) t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m
HD FST PT LE SEED IDC eq_refl IFFS ILPC ltac:(clear - FSV; unfold hid in *; lia) IID OBS S8 SPOS ltac:(unfold IMG_TOP_B; unfold SEGTOP_A in SIMG; clear - SIMG; unfold hid in *; lia) SLO
eq_refl OCy LREST OBY ltac:(clear - OAL; unfold hid in *; Z.div_mod_to_equations; lia) ltac:(clear - FO1 FH0; unfold hid in *; lia) ltac:(unfold IMG_TOP_B, Y; unfold SEGTOP_A in FHIMG; clear - FHIMG FO1 FSV; unfold hid in *; lia)
ltac:(unfold Y; clear - FO2 FHLO FSV; unfold hid in *; lia)
IQC ltac:(exact JIQ) OBQ ltac:(clear - IQ8; unfold hid in *; Z.div_mod_to_equations; lia) ltac:(clear - IQP; unfold hid in *; lia) ltac:(clear - IQLO; unfold hid in *; lia)
MSP1 ltac:(rewrite length_firstn, JMSP; reflexivity) OBM ltac:(clear - MSP8; unfold hid in *; Z.div_mod_to_equations; lia) ltac:(clear - MSP; unfold hid in *; lia) ltac:(unfold IMG_TOP_B; unfold SEGTOP_A in MIMG; clear - MIMG; unfold hid in *; lia) ltac:(clear - MSLO; unfold hid in *; lia)
ltac:(unfold hidp; clear - SSH0; unfold hid in *; unfold SH_LO, SH_HI; lia)
ltac:(unfold hidp, Y; clear - FHSH FO1 FO2 FSV; unfold hid in *; unfold SH_LO, SH_HI; lia)
ltac:(unfold hidp; clear - MSH0; unfold hid in *; unfold SH_LO, SH_HI; lia)
ltac:(unfold hidp, Y; clear - FS0 FO1 FO2 FSV; unfold hid in *; lia)
ltac:(unfold hidp; clear - SIQ; unfold hid in *; lia)
ltac:(unfold hidp; clear - SMS; unfold hid in *; lia)
ltac:(unfold hidp, Y; clear - FIQ FO1 FO2 FSV; unfold hid in *; lia)
ltac:(unfold hidp, Y; clear - FMS FO1 FO2 FSV; unfold hid in *; lia)
ltac:(unfold hidp; clear - IQMS; unfold hid in *; lia)
ST0 ltac:(clear - LOR; unfold hid in *; unfold RT_STACK, SBLOST_STACK in *; lia) LOS ltac:(clear - SPT; unfold hid in *; unfold USTACK_TOP in *; lia) CC0 MI0 FRM).
destruct POST as (m1 & xt0 & xt1 & xt2 & xt3 & xt4 & xt5 & xt6 & F1 & fc1 & ys1 & mv1 & seed1 & -> & MU1 & WM1 & MI1 & FRM1 & ST1 & FR1
& HD1 & FST1 & PT1 & LE1 & SEED1 & IDC1 & YS1 & LYS1 & IQ1 & MSV1 & LMV1).

assert (ART1 : X14x.ART RT Σ m1).
{ apply (af_frame RT AF Σ m m1 lo ART0 LOW); [| exact WM1]. intros a0 Ha. apply MU1. cbn [outside].
split; [| split; [| split; [| split; [| split; [| split; [| exact I]]]]]]; intros Hin; apply Ha.
- left. clear - Hin LOR SPT. unfold RT_STACK, SBLOST_STACK, USTACK_TOP in *. lia.
- right; right; left. exists S, 160. split; [exact INS0 | clear - Hin; unfold hid in *; lia].
- right; right; left. exists S, 160. split; [exact INS0 | clear - Hin; unfold hid in *; lia].
- right; right; left. exists S, 160. split; [exact INS0 | clear - Hin; unfold hid in *; lia].
- right; right; right; left. exists fh, kh. split; [exact INF | unfold Y in Hin; clear - Hin FO1 FO2 FSV; unfold hid in *; lia].
- right; right; left. exists (a_msp a), 64. split; [exact INMS | clear - Hin; unfold hid in *; lia]. }
set (WF := (OUT, OUT + 8000) :: blocks_ivs (sb_blocks s S a)).
assert (PF1 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp WF m m1).
{ apply (pres_fp_of_munch _ _ _ _ _ m m1 MU1). intros x Hx Ho. unfold WF in Ho. cbn [blocks_ivs map sb_blocks outside blk_addr blk_size fst snd] in Ho |- *.
unfold SBSTATE_SIZEOF in Ho. destruct Ho as (HO & HS & _ & _ & _ & _ & _ & _ & _ & HM & _).
pose proof (SPL x Hx) as SPX.
split; [intros Hin; destruct SPX as [SX|SX]; clear - Hin SX LOR LOW; unfold hid in *; unfold RT_STACK, SBLOST_STACK in *; lia|].
split; [intros Hin; apply HS; clear - Hin; unfold hid in *; lia|]. split; [intros Hin; apply HS; clear - Hin; unfold hid in *; lia|]. split; [intros Hin; apply HS; clear - Hin; unfold hid in *; lia|].
split; [intros Hin; apply HO; unfold Y in Hin; clear - Hin FSV; unfold hid in *; lia|]. split; [intros Hin; apply HM; clear - Hin; unfold hid in *; lia| exact I]. }

destruct (live_below_lo RT AF Σ m _ _ lo ART0 INEX LOW) as (EXP & EXLO & _).
destruct (live_below_lo RT AF Σ m _ _ lo ART0 INOQ LOW) as (OQP & OQLO & _).
destruct (live_below_lo RT AF Σ m _ _ lo ART0 INPG LOW) as (PGP & PGLO & _).
destruct (live_below_lo RT AF Σ m _ _ lo ART0 INER LOW) as (ERP & ERLO & _).
pose proof (lsl_live_apart RT AF Σ m _ _ _ _ ART0 INS0 ING0 (NDN 0%nat 1%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as SG0.
pose proof (lsl_live_apart RT AF Σ m _ _ _ _ ART0 INS0 ING1 (NDN 0%nat 2%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as SG1.
pose proof (lsl_live_apart RT AF Σ m _ _ _ _ ART0 INS0 INEX (NDN 0%nat 3%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as SEX.
pose proof (lsl_live_apart RT AF Σ m _ _ _ _ ART0 INS0 INOQ (NDN 0%nat 4%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as SOQ.
pose proof (lsl_live_apart RT AF Σ m _ _ _ _ ART0 INS0 INPG (NDN 0%nat 6%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as SPG.
pose proof (lsl_live_apart RT AF Σ m _ _ _ _ ART0 INS0 INER (NDN 0%nat 7%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as SER.
pose proof (lsl_live_apart RT AF Σ m _ _ _ _ ART0 ING0 INMS (NDN 1%nat 8%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as G0MS.
pose proof (lsl_live_apart RT AF Σ m _ _ _ _ ART0 ING1 INMS (NDN 2%nat 8%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as G1MS.
pose proof (lsl_live_apart RT AF Σ m _ _ _ _ ART0 INEX INMS (NDN 3%nat 8%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as EXMS.
pose proof (lsl_live_apart RT AF Σ m _ _ _ _ ART0 INOQ INMS (NDN 4%nat 8%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as OQMS.
pose proof (lsl_live_apart RT AF Σ m _ _ _ _ ART0 INPG INMS (NDN 6%nat 8%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as PGMS.
pose proof (lsl_live_apart RT AF Σ m _ _ _ _ ART0 INER INMS (NDN 7%nat 8%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as ERMS.
destruct (frame_live_apart RT AF Σ m fh kh _ _ ART0 INF ING0) as (FG0 & _).
destruct (frame_live_apart RT AF Σ m fh kh _ _ ART0 INF ING1) as (FG1 & _).
destruct (frame_live_apart RT AF Σ m fh kh _ _ ART0 INF INEX) as (FEX & _).
destruct (frame_live_apart RT AF Σ m fh kh _ _ ART0 INF INOQ) as (FOQ & _).
destruct (frame_live_apart RT AF Σ m fh kh _ _ ART0 INF INPG) as (FPG & _).
destruct (frame_live_apart RT AF Σ m fh kh _ _ ART0 INF INER) as (FER & _).
assert (LEX : Z.of_nat (length (sj_exc j)) = sbd_subframeSize s) by exact JEXC.
cps_hide.
trm MU1 WM1 CFG ltac:(clear - SMS FS0 FO1 FO2 FSV SLO LOR; unfold hid in *; unfold Y, RT_STACK, SBLOST_STACK in *; lia).
trm MU1 WM1 PAD ltac:(clear - SMS FS0 FO1 FO2 FSV SLO LOR; unfold hid in *; unfold Y, RT_STACK, SBLOST_STACK in *; lia).
trm MU1 WM1 OCa ltac:(clear - LWA FS0 FMS FO1 FO2 FSV FHLO LOR; unfold hid in *; unfold Y, RT_STACK, SBLOST_STACK in *; lia).
trm MU1 WM1 OCc ltac:(clear - LWC FS0 FMS FO1 FO2 FSV FHLO LOR; unfold hid in *; unfold Y, RT_STACK, SBLOST_STACK in *; lia).
trm MU1 WM1 MSP2 ltac:(rewrite length_skipn, JMSP; cbn; clear - SMS FMS FO1 FO2 FSV MSLO LOR; unfold hid in *; unfold Y, RT_STACK, SBLOST_STACK in *; lia).
trm MU1 WM1 G0C ltac:(rewrite JG0; cbn; clear - SG0 FG0 G0MS FO1 FO2 FSV G0LO LOR; unfold hid in *; unfold Y, RT_STACK, SBLOST_STACK in *; lia).
trm MU1 WM1 G1C ltac:(rewrite JG1; cbn; clear - SG1 FG1 G1MS FO1 FO2 FSV G1LO LOR; unfold hid in *; unfold Y, RT_STACK, SBLOST_STACK in *; lia).
trm MU1 WM1 EXC ltac:(clear - LEX SEX FEX EXMS FO1 FO2 FSV EXLO LOR; unfold hid in *; unfold Y, RT_STACK, SBLOST_STACK in *; lia).
trm MU1 WM1 OQC ltac:(rewrite JOQ; cbn; clear - SOQ FOQ OQMS FO1 FO2 FSV OQLO LOR; unfold hid in *; unfold Y, RT_STACK, SBLOST_STACK in *; lia).
trm MU1 WM1 PGC ltac:(rewrite JPG; cbn; clear - SPG FPG PGMS FO1 FO2 FSV PGLO LOR; unfold hid in *; unfold Y, RT_STACK, SBLOST_STACK in *; lia).
trm MU1 WM1 ERC ltac:(rewrite JER; cbn; clear - SER FER ERMS FO1 FO2 FSV ERLO LOR; unfold hid in *; unfold Y, RT_STACK, SBLOST_STACK in *; lia).

assert (OFW1 : offsh [(usp + -240, usp); (S + 36, S + 40); (S + 132, S + 136); (S + 152, S + 156); (Y, Y + 4 * fsz); (a_msp a, a_msp a + 32)])
by (cbn [offsh]; unfold Y; clear - SSH0 FHSH MSH0 LOS LOR FO1 FO2 FSV; unfold hid in *; unfold SH_LO, SH_HI, RT_STACK, SBLOST_STACK in *; lia).
assert (ACO1 : acc bsegs m1 OUT 8000).
{ refine (proj2 (proj2 (aobj_munch bsegs _ m m1 OUT 8000 _ MU1 _))).
- split; [clear - FO1 FH0; unfold hid in *; lia|]. split; [clear - FO2 FHLO LOR SPT; unfold hid in *; unfold APP_TOP, USTACK_TOP, RT_STACK, SBLOST_STACK in *; lia| exact ACO].
- apply shfree_of_offsh; [exact OFW1 | clear - FO1 FH0; unfold hid in *; lia | clear - FO2 FHLO LOR SPT; unfold hid in *; unfold APP_TOP, USTACK_TOP, RT_STACK, SBLOST_STACK in *; lia]. }

assert (YJ : rw_cells bsegs m1 OUT (f32 (wa ++ ys1))).
{ apply f32_join; [exact OCa|]. replace (OUT + 4 * Z.of_nat (length wa)) with Y by (unfold Y; rewrite LWA; reflexivity). exact YS1. }
assert (LYJ : Z.of_nat (length (wa ++ ys1)) = 2 * fsz) by (rewrite length_app; clear - LWA LYS1; unfold hid in *; lia).
clear OCa YS1.
pose proof (lsl_live_apart RT AF Σ m _ _ _ _ ART0 ING0 ING1 (NDN 1%nat 2%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as G01.
assert (EU112 : bv_unsigned (Z_to_bv 64 (usp + -112)) = usp + -112) by (apply unsigned_lit; clear - LOR SPT LOS; unfold hid in *; unfold SH_HI, RT_STACK, SBLOST_STACK, USTACK_TOP in *; lia).
assert (QN : 2 * fsz = 320 \/ 2 * fsz = 640) by (clear - FSV; unfold hid in *; lia).
assert (EA1 : Z_to_bv 64 Y = Z_to_bv 64 (OUT + 2 * (2 * fsz))) by (f_equal; unfold Y; clear; unfold hid in *; lia).
cps_rt (QMF16 (2 * fsz) QN Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1
OUT (a_g0 a) (a_g1 a) lo fh (a_g0 a) 256 (a_g1 a) 256 kh (wa ++ ys1) (sj_g0 j) (sj_g1 j)
FDO MST eq_refl EA1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
YJ LYJ INF FO1 ltac:(clear - FO2 FSV; unfold hid in *; lia)
(acc_sub bsegs m1 OUT 8000 OUT (4 * (2 * fsz)) ACO1 ltac:(clear; unfold hid in *; lia) ltac:(clear - FSV; unfold hid in *; lia)) OAL
G0C JG0 ING0 ltac:(clear; unfold hid in *; lia) ltac:(clear; unfold hid in *; lia) ltac:(clear - G08; unfold hid in *; Z.div_mod_to_equations; lia)
G1C JG1 ING1 ltac:(clear; unfold hid in *; lia) ltac:(clear; unfold hid in *; lia) ltac:(clear - G18; unfold hid in *; Z.div_mod_to_equations; lia)
ltac:(clear - G01; unfold hid in *; lia)
ltac:(rewrite EU112; apply (pois_above_le _ usp); [exact POA| clear; unfold hid in *; lia]) FRM1 ART1 MI1
ltac:(rewrite EU112; exact ST1) LOW
ltac:(rewrite EU112; clear - LOR; unfold hid in *; unfold RT_STACK, SBLOST_STACK in *; lia)
ltac:(rewrite EU112; clear - SPT; unfold hid in *; unfold USTACK_TOP in *; lia)
ltac:(rewrite EU112; clear - SPA; unfold hid in *; Z.div_mod_to_equations; lia)).
intros cq (Σq & Hcq & LVq & FRq & SPq & CRq & POq).
cps_unpack_lib Hcq as (vq & m2 & ysq & g0q & g1q & RSq & (ART2 & MI2 & WM2 & ST2) & PRES2 & YSQ & LYSQ & G0Q & LG0Q & G1Q & LG1Q & ACQ).
try rewrite EU112 in PRES2. try rewrite EU112 in ST2.
clear YJ G0C G1C. match goal with H : ASTA RT Σ _ _ _ |- _ => clear H end.

assert (CLS : forall x, usp + -112 <= x < usp -> aclient (rt_live RT Σ) (rt_frames RT Σ) (usp + -112) x)
by (intros x Hx; left; clear - Hx SPT; unfold hid in *; unfold USTACK_TOP in *; lia).
assert (CLL : forall p n x, In (p, n) (rt_live RT Σ) -> p <= x < p + n -> aclient (rt_live RT Σ) (rt_frames RT Σ) (usp + -112) x)
by (intros p n x Hp Hx; right; right; left; exists p, n; split; [exact Hp| exact Hx]).
assert (CLF : forall x, fh <= x < fh + fs_size kh - 8 -> aclient (rt_live RT Σ) (rt_frames RT Σ) (usp + -112) x)
by (intros x Hx; right; right; right; left; exists fh, kh; split; [exact INF| exact Hx]).
assert (OUTQ : forall x, (x < OUT \/ OUT + 8 * fsz <= x) -> (x < a_g0 a \/ a_g0 a + 256 <= x) -> (x < a_g1 a \/ a_g1 a + 256 <= x) ->
outside [(OUT, OUT + 4 * (2 * fsz)); (a_g0 a, a_g0 a + 256); (a_g1 a, a_g1 a + 256)] x)
by (intros x H1 H2 H3; cbn [outside]; split; [clear - H1; lia| split; [clear - H2; lia| split; [clear - H3; lia| exact I]]]).
pose proof (lsl_live_apart RT AF Σ m _ _ _ _ ART0 ING0 INIQ (NDN 1%nat 5%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as G0IQ.
pose proof (lsl_live_apart RT AF Σ m _ _ _ _ ART0 ING1 INIQ (NDN 2%nat 5%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as G1IQ.
pose proof (lsl_live_apart RT AF Σ m _ _ _ _ ART0 ING0 INEX (NDN 1%nat 3%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as G0EX.
pose proof (lsl_live_apart RT AF Σ m _ _ _ _ ART0 ING1 INEX (NDN 2%nat 3%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as G1EX.
pose proof (lsl_live_apart RT AF Σ m _ _ _ _ ART0 ING0 INOQ (NDN 1%nat 4%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as G0OQ.
pose proof (lsl_live_apart RT AF Σ m _ _ _ _ ART0 ING1 INOQ (NDN 2%nat 4%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as G1OQ.
pose proof (lsl_live_apart RT AF Σ m _ _ _ _ ART0 ING0 INPG (NDN 1%nat 6%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as G0PG.
pose proof (lsl_live_apart RT AF Σ m _ _ _ _ ART0 ING1 INPG (NDN 2%nat 6%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as G1PG.
pose proof (lsl_live_apart RT AF Σ m _ _ _ _ ART0 ING0 INER (NDN 1%nat 7%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as G0ER.
pose proof (lsl_live_apart RT AF Σ m _ _ _ _ ART0 ING1 INER (NDN 2%nat 7%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as G1ER.
cps_hide.
assert (LMS2 : Z.of_nat (length (skipn 8 (sj_msp j))) = 8) by (rewrite length_skipn, JMSP; reflexivity).
assert (LMV1z : Z.of_nat (length mv1) = 8) by (rewrite LMV1; reflexivity).
tr1 PRES2 WM2 FR1 ltac:(fun x Hx => apply CLS; clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx FO2 FHLO G0LO G1LO LOR FSV; unfold hid in *; unfold RT_STACK, SBLOST_STACK in *; lia).
tr1 PRES2 WM2 HD1 ltac:(fun x Hx => apply (CLL S 160 x INS0); clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx FS0 SG0 SG1 FO1 FO2 FSV; unfold hid in *; lia).
tr1 PRES2 WM2 FST1 ltac:(fun x Hx => apply (CLL S 160 x INS0); clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx FS0 SG0 SG1 FO1 FO2 FSV; unfold hid in *; lia).
tr1 PRES2 WM2 PT1 ltac:(fun x Hx => apply (CLL S 160 x INS0); clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx FS0 SG0 SG1 FO1 FO2 FSV; unfold hid in *; lia).
tr1 PRES2 WM2 LE1 ltac:(fun x Hx => apply (CLL S 160 x INS0); clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx FS0 SG0 SG1 FO1 FO2 FSV; unfold hid in *; lia).
tr1 PRES2 WM2 SEED1 ltac:(fun x Hx => apply (CLL S 160 x INS0); clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx FS0 SG0 SG1 FO1 FO2 FSV; unfold hid in *; lia).
tr1 PRES2 WM2 CFG ltac:(fun x Hx => apply (CLL S 160 x INS0); clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx FS0 SG0 SG1 FO1 FO2 FSV; unfold hid in *; lia).
tr1 PRES2 WM2 IDC1 ltac:(fun x Hx => apply (CLL S 160 x INS0); clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx FS0 SG0 SG1 FO1 FO2 FSV; unfold hid in *; lia).
tr1 PRES2 WM2 PAD ltac:(fun x Hx => apply (CLL S 160 x INS0); clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx FS0 SG0 SG1 FO1 FO2 FSV; unfold hid in *; lia).
tr1 PRES2 WM2 OCc ltac:(fun x Hx => apply CLF; clear - Hx LWC FO1 FO2 FSV; unfold hid in *; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx LWC FG0 FG1 FO1 FO2 FSV; unfold hid in *; lia).
tr1 PRES2 WM2 IQ1 ltac:(fun x Hx => apply (CLL (a_iq a) 32 x INIQ); clear - Hx JIQ; rewrite JIQ in Hx; cbn in Hx; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx JIQ FIQ G0IQ G1IQ FO1 FO2 FSV; rewrite JIQ in Hx; cbn in Hx; unfold hid in *; lia).
tr1 PRES2 WM2 MSV1 ltac:(fun x Hx => apply (CLL (a_msp a) 64 x INMS); clear - Hx LMV1z; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx LMV1z FMS G0MS G1MS FO1 FO2 FSV; unfold hid in *; lia).
tr1 PRES2 WM2 MSP2 ltac:(fun x Hx => apply (CLL (a_msp a) 64 x INMS); clear - Hx LMS2; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx LMS2 FMS G0MS G1MS FO1 FO2 FSV; unfold hid in *; lia).
tr1 PRES2 WM2 EXC ltac:(fun x Hx => apply (CLL (a_exc a) (4 * sbd_subframeSize s) x INEX); clear - Hx LEX; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx LEX FEX G0EX G1EX FO1 FO2 FSV; unfold hid in *; lia).
tr1 PRES2 WM2 OQC ltac:(fun x Hx => apply (CLL (a_oq a) 32 x INOQ); clear - Hx JOQ; rewrite JOQ in Hx; cbn in Hx; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx JOQ FOQ G0OQ G1OQ FO1 FO2 FSV; rewrite JOQ in Hx; cbn in Hx; unfold hid in *; lia).
tr1 PRES2 WM2 PGC ltac:(fun x Hx => apply (CLL (a_pg a) 16 x INPG); clear - Hx JPG; rewrite JPG in Hx; cbn in Hx; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx JPG FPG G0PG G1PG FO1 FO2 FSV; rewrite JPG in Hx; cbn in Hx; unfold hid in *; lia).
tr1 PRES2 WM2 ERC ltac:(fun x Hx => apply (CLL (a_er a) 16 x INER); clear - Hx JER; rewrite JER in Hx; cbn in Hx; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx JER FER G0ER G1ER FO1 FO2 FSV; rewrite JER in Hx; cbn in Hx; unfold hid in *; lia).

assert (PF2 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp WF m m2).
{ apply (pres_fp_trans _ _ _ _ m m1 m2 PF1).
apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ) (rt_frames RT Σ) (usp + -112) _ m1 m2 PRES2); [intros e He; exact He| intros e He; exact He| clear; lia|].
intros x Hx Ho. unfold WF in Ho. cbn [blocks_ivs map sb_blocks outside blk_addr blk_size fst snd] in Ho |- *.
destruct Ho as (HO & _ & H0 & H1 & _).
split; [intros Hin; apply HO; clear - Hin FSV; unfold hid in *; lia|]. split; [exact H0|]. split; [exact H1| exact I]. }
clear PF1.

pose proof (live_facts RT AF Σ m _ _ ART0 ING0) as (_ & _ & _ & G0SH).
pose proof (live_facts RT AF Σ m _ _ ART0 ING1) as (_ & _ & _ & G1SH).
assert (ACO2 : acc bsegs m2 OUT 8000).
{ apply (acc_pres_fp_frame _ _ _ _ m1 m2 fh kh OUT 8000 PRES2 INF ltac:(clear - FH64; Z.div_mod_to_equations; lia) (fs_size_mod8 kh) ltac:(clear - FH0; lia) FO1
ltac:(clear - FO2; lia)); [| exact ACO1].
intros i Hi. pose proof (shad_in_window (OUT + i) ltac:(clear - Hi FO1 FO2 FH0 FHLO LOR SPT; unfold RT_STACK, SBLOST_STACK, USTACK_TOP in *; lia)) as SW.
apply OUTQ; clear - SW FHSH FO1 FO2 G0SH G1SH FSV; unfold hid in *; unfold SH_LO, SH_HI in *; lia. }
clear ACO1 ACQ.

assert (INS0q : In (S, 160) (rt_live RT Σq)) by (rewrite LVq; exact INS0).
destruct (af_acc_live RT AF Σq m2 S 160 ART2 INS0q) as (_ & ACS2).
assert (OBS2 : aobj bsegs m2 S 160) by (split; [clear - SP0; lia|]; split; [clear - SLO LOR SPT; unfold APP_TOP, USTACK_TOP, RT_STACK, SBLOST_STACK in *; lia| exact ACS2]).

cps_seg (lost_w2 usp lo S (sbd_submodeID s) a3 ra gp (Z_to_bv 64 0x638c98) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 FR1 IDC1 OBS2 S8 ltac:(clear - SSH0; unfold hid in *; unfold SH_LO, SH_HI; lia) SLO IID ST2
ltac:(clear - LOR; unfold RT_STACK, SBLOST_STACK in *; lia) LOS ltac:(clear - SPT; unfold USTACK_TOP in *; lia) MI2).
destruct POST as (m3 & v3 & -> & MU3 & WM3 & MI3 & ST3 & IDC3).

assert (LOWq : rt_sp0 RT Σq - STACK_WIN <= lo) by (rewrite SPq; exact LOW).
assert (ART3 : X14x.ART RT Σq m3).
{ apply (af_frame RT AF Σq m2 m3 lo ART2 LOWq); [| exact WM3]. intros a0 Ha. apply MU3. cbn [outside].
split; [| exact I]. intros Hin; apply Ha. right; right; left. exists S, 160. split; [exact INS0q | clear - Hin; lia]. }
assert (PF3 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp WF m m3).
{ apply (pres_fp_trans _ _ _ _ m m2 m3 PF2). apply (pres_fp_of_munch _ _ _ _ _ m2 m3 MU3). intros x Hx Ho. unfold WF in Ho.
cbn [blocks_ivs map sb_blocks outside blk_addr blk_size fst snd] in Ho |- *. unfold SBSTATE_SIZEOF in Ho. destruct Ho as (_ & HS & _).
split; [intros Hin; apply HS; clear - Hin; lia| exact I]. }
clear PF2.
trm MU3 WM3 HD1 ltac:(clear; lia). trm MU3 WM3 FST1 ltac:(clear; lia). trm MU3 WM3 PT1 ltac:(clear; lia). trm MU3 WM3 LE1 ltac:(clear; lia).
trm MU3 WM3 SEED1 ltac:(clear; lia). trm MU3 WM3 CFG ltac:(clear; lia). trm MU3 WM3 PAD ltac:(clear; lia).
trm MU3 WM3 YSQ ltac:(clear - LYSQ FS0 FO1 FO2 FSV; unfold hid in *; lia).
trm MU3 WM3 OCc ltac:(clear - LWC FS0 FO1 FO2 FSV; unfold hid in *; lia).
trm MU3 WM3 G0Q ltac:(rewrite LG0Q; cbn; clear - SG0; unfold hid in *; lia).
trm MU3 WM3 G1Q ltac:(rewrite LG1Q; cbn; clear - SG1; unfold hid in *; lia).
trm MU3 WM3 EXC ltac:(clear - LEX SEX; unfold hid in *; lia).
trm MU3 WM3 OQC ltac:(rewrite JOQ; cbn; clear - SOQ; unfold hid in *; lia).
trm MU3 WM3 IQ1 ltac:(rewrite JIQ; cbn; clear - SIQ; unfold hid in *; lia).
trm MU3 WM3 MSV1 ltac:(clear - LMV1z SMS; unfold hid in *; lia).
trm MU3 WM3 MSP2 ltac:(clear - LMS2 SMS; unfold hid in *; lia).
trm MU3 WM3 PGC ltac:(rewrite JPG; cbn; clear - SPG; unfold hid in *; lia).
trm MU3 WM3 ERC ltac:(rewrite JER; cbn; clear - SER; unfold hid in *; lia).

assert (ACO3 : acc bsegs m3 OUT 8000).
{ refine (proj2 (proj2 (aobj_munch bsegs _ m2 m3 OUT 8000 _ MU3 _))).
- split; [clear - FO1 FH0; lia|]. split; [clear - FO2 FHLO LOR SPT; unfold APP_TOP, USTACK_TOP, RT_STACK, SBLOST_STACK in *; lia| exact ACO2].
- apply shfree_of_offsh; [cbn [offsh]; clear - SSH0; unfold hid in *; unfold SH_LO, SH_HI; lia | clear - FO1 FH0; lia |
clear - FO2 FHLO LOR SPT; unfold APP_TOP, USTACK_TOP, RT_STACK, SBLOST_STACK in *; lia]. }

set (j' := SBJ (sj_last_ener j) seed1 (sj_pad1 j) (sj_pad2 j) g0q g1q (sj_exc j) (sj_oq j) (sj_iq j) (mv1 ++ skipn 8 (sj_msp j)) (sj_pg j) (sj_er j)).
assert (X3 : rw_cells bsegs m3 S (SBCELLS (set_sbd_first s 1) a OUT j')).
{ apply sb_pieces_iff. exact (conj HD1 (conj FST1 (conj PT1 (conj LE1 (conj SEED1 (conj CFG (conj IDC3 PAD))))))). }
assert (JOK3 : sb_junk_ok (set_sbd_first s 1) j').
{ unfold sb_junk_ok. cbn [j' sj_pad1 sj_pad2 sj_g0 sj_g1 sj_exc sj_oq sj_iq sj_msp sj_pg sj_er].
refine (conj JP1 (conj JP2 (conj LG0Q (conj LG1Q (conj JEXC (conj JOQ (conj JIQ (conj _ (conj JPG JER))))))))).
rewrite length_app, length_skipn, LMV1, JMSP. reflexivity. }
assert (MSX : rw_cells bsegs m3 (a_msp a) (f32 (mv1 ++ skipn 8 (sj_msp j)))).
{ apply f32_join; [exact MSV1|]. rewrite LMV1. exact MSP2. }
assert (BUFS3 : sb_bufs bsegs m3 a j') by (exact (conj G0Q (conj G1Q (conj EXC (conj OQC (conj IQ1 (conj MSX (conj PGC ERC)))))))).
assert (OC3 : rw_cells bsegs m3 OUT (f32 (ysq ++ wc))).
{ apply f32_join; [exact YSQ|]. replace (OUT + 4 * Z.of_nat (length ysq)) with (OUT + 8 * fsz) by (rewrite LYSQ; clear; lia). exact OCc. }
assert (LOC3 : length (ysq ++ wc) = 2000%nat) by (rewrite length_app; clear - LYSQ LWC FSV; unfold hid in *; lia).

apply Hk. exists Σq. split; [| split; [exact LVq|]; split; [exact FRq|]; split; [exact SPq|]; split; [exact CRq| exact POq]].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists v3, m3, j', (ysq ++ wc).
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact RSq]|].
split. { split; [exact ART3|]. split; [exact MI3|]. split; [cps_wmono| exact ST3]. }
split; [exact PF3|]. split; [exact X3|]. split; [exact JOK3|]. split; [exact BUFS3|]. split; [exact OC3|]. split; [exact LOC3| exact ACO3].
Qed.
End SbLost.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac simpl_sizes ::=
rewrite ?X06d.sb_cells_size, ?cells_size_sbp_hdr, ?cells_size_sbp_ptrs, ?cells_size_sbp_cfg, ?cells_size_lost_frame, ?app_length, ?cells_size_app, ?cells_size_f32, ?length_f32;
cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length, ?cells_size_f32, ?length_f32; cbn [length].

Section SbLost.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis QMF16 : forall N, N = 320 \/ N = 640 -> qmf_synth_cps16 RT N.

Local Ltac trm MU WM H tacD :=
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
Local Ltac tr1 PRES WM H tacA tacO :=
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

Theorem sb_decode_lost_ok : sb_decode_lost_cps RT.
Proof using AF QMF16.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S OUT lo fh kh s a j ows
FDO MST EA0 EA1 EA2 ETP X JOK INV BUFS S8 SPOS AL NDB LIVEB OC LOWS INF IFO POA ART0 MI0 FRM ST0 LOW LOR SPT SPA.
subst a0 a1 a2 tp.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.

pose proof INV as (IM & IFS & IFFS & ISF & INS & ILPC & IFST & ISR & ILE & IES & IID & IIS).
assert (FSV : sbd_frame_size s = 160 \/ sbd_frame_size s = 320) by (rewrite IFS; destruct IM as [-> | ->]; cbn; auto).
pose proof JOK as (JP1 & JP2 & JG0 & JG1 & JEXC & JOQ & JIQ & JMSP & JPG & JER).
destruct BUFS as (G0C & G1C & EXC & OQC & IQC & MSPC & PGC & ERC).
pose proof AL as (G08 & G18 & EX8 & OQ8 & IQ8 & MSP8 & PG8 & ER8).
pose proof IFO as (FO1 & FO2 & ACO & OAL).

assert (INS0 : In (S, 160) (rt_live RT Σ)) by exact (LIVEB (sbd_blk s, S, SBSTATE_SIZEOF) ltac:(cbn [sb_blocks In]; left; reflexivity)).
assert (ING0 : In (a_g0 a, 256) (rt_live RT Σ)) by exact (LIVEB (sbd_g0_mem s, a_g0 a, 256) ltac:(cbn [sb_blocks In]; do 1 right; left; reflexivity)).
assert (ING1 : In (a_g1 a, 256) (rt_live RT Σ)) by exact (LIVEB (sbd_g1_mem s, a_g1 a, 256) ltac:(cbn [sb_blocks In]; do 2 right; left; reflexivity)).
assert (INEX : In (a_exc a, 4 * sbd_subframeSize s) (rt_live RT Σ))
by exact (LIVEB (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s) ltac:(cbn [sb_blocks In]; do 3 right; left; reflexivity)).
assert (INOQ : In (a_oq a, 32) (rt_live RT Σ)) by exact (LIVEB (sbd_old_qlsp s, a_oq a, 32) ltac:(cbn [sb_blocks In]; do 4 right; left; reflexivity)).
assert (INIQ : In (a_iq a, 32) (rt_live RT Σ)) by exact (LIVEB (sbd_interp_qlpc s, a_iq a, 32) ltac:(cbn [sb_blocks In]; do 5 right; left; reflexivity)).
assert (INPG : In (a_pg a, 16) (rt_live RT Σ)) by exact (LIVEB (sbd_pi_gain s, a_pg a, 16) ltac:(cbn [sb_blocks In]; do 6 right; left; reflexivity)).
assert (INER : In (a_er a, 16) (rt_live RT Σ)) by exact (LIVEB (sbd_exc_rms s, a_er a, 16) ltac:(cbn [sb_blocks In]; do 7 right; left; reflexivity)).
assert (INMS : In (a_msp a, 64) (rt_live RT Σ)) by exact (LIVEB (sbd_mem_sp s, a_msp a, 64) ltac:(cbn [sb_blocks In]; do 8 right; left; reflexivity)).
assert (NDA0 : List.NoDup [S; a_g0 a; a_g1 a; a_exc a; a_oq a; a_iq a; a_pg a; a_er a; a_msp a]) by exact NDB.
assert (NDN : forall i0 j0 : nat, (i0 < 9)%nat -> (j0 < 9)%nat -> i0 <> j0 ->
nth i0 [S; a_g0 a; a_g1 a; a_exc a; a_oq a; a_iq a; a_pg a; a_er a; a_msp a] 0 <> nth j0 [S; a_g0 a; a_g1 a; a_exc a; a_oq a; a_iq a; a_pg a; a_er a; a_msp a] 0)
by (intros i0 j0 Hi Hj Hne E; apply Hne; exact (proj1 (NoDup_nth _ 0) NDA0 i0 j0 Hi Hj E)).

destruct (live_below_lo RT AF Σ m S 160 lo ART0 INS0 LOW) as (SP0 & SLO & LOS).
destruct (live_below_lo RT AF Σ m _ _ lo ART0 ING0 LOW) as (G0P & G0LO & _).
destruct (live_below_lo RT AF Σ m _ _ lo ART0 ING1 LOW) as (G1P & G1LO & _).
destruct (live_below_lo RT AF Σ m _ _ lo ART0 INIQ LOW) as (IQP & IQLO & _).
destruct (live_below_lo RT AF Σ m _ _ lo ART0 INMS LOW) as (MSP & MSLO & _).
destruct (frame_below_lo RT AF Σ m fh kh lo ART0 INF LOW) as (FHLO & _ & _).
pose proof (frame_facts RT AF Σ m fh kh ART0 INF) as (FH0 & FH64 & FHIMG & _ & FHSH & _).
pose proof (live_facts RT AF Σ m S 160 ART0 INS0) as (_ & _ & _ & SSH0).
pose proof (live_facts RT AF Σ m _ _ ART0 INMS) as (_ & _ & _ & MSH0).
pose proof (af_live_small RT AF Σ m S 160 ART0 INS0 ltac:(clear; lia)) as SIMG.
pose proof (af_live_small RT AF Σ m _ _ ART0 INMS ltac:(clear; lia)) as MIMG.
destruct (frame_live_apart RT AF Σ m fh kh S 160 ART0 INF INS0) as (FS0 & _).
destruct (frame_live_apart RT AF Σ m fh kh _ _ ART0 INF INIQ) as (FIQ & _).
destruct (frame_live_apart RT AF Σ m fh kh _ _ ART0 INF INMS) as (FMS & _).
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 INS0 INIQ (NDN 0%nat 5%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as SIQ.
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 INS0 INMS (NDN 0%nat 8%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as SMS.
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 INIQ INMS (NDN 5%nat 8%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as IQMS.
pose proof (fun a0 => aclient_split RT AF Σ m usp a0 ART0) as SPL.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
destruct (af_acc_live RT AF Σ m S 160 ART0 INS0) as (_ & ACS).
destruct (af_acc_live RT AF Σ m _ _ ART0 INIQ) as (_ & ACIQ).
destruct (af_acc_live RT AF Σ m _ _ ART0 INMS) as (_ & ACMS).
cps_hide.
set (fsz := sbd_frame_size s) in *.
set (Y := OUT + 4 * fsz).
assert (FSN : Z.of_nat (Z.to_nat fsz) = fsz) by (clear - FSV; unfold hid in *; lia).

apply (f32_split asegs m OUT ows (Z.to_nat fsz)) in OC; [| rewrite LOWS; clear - FSV; unfold hid in *; lia].
destruct OC as (OCa & OCb). rewrite FSN in OCb.
apply (f32_split asegs m (OUT + 4 * fsz) (skipn (Z.to_nat fsz) ows) (Z.to_nat fsz)) in OCb; [| rewrite length_skipn, LOWS; clear - FSV; unfold hid in *; lia].
destruct OCb as (OCy & OCc). rewrite FSN in OCc. fold Y in OCy.
replace (OUT + 4 * fsz + 4 * fsz) with (OUT + 8 * fsz) in OCc by (clear; unfold hid in *; lia).
assert (LYW : length (firstn (Z.to_nat fsz) (skipn (Z.to_nat fsz) ows)) = Z.to_nat fsz)
by (rewrite length_firstn, length_skipn, LOWS; clear - FSV; unfold hid in *; lia).
destruct (firstn (Z.to_nat fsz) (skipn (Z.to_nat fsz) ows)) as [|cw rest] eqn:EYW; [cbn [length] in LYW; clear - LYW FSV; unfold hid in *; lia|].
assert (LREST : Z.of_nat (length rest) + 1 = fsz) by (cbn [length] in LYW; clear - LYW FSV; unfold hid in *; lia).
set (wa := firstn (Z.to_nat fsz) ows) in OCa. set (wc := skipn (Z.to_nat fsz) (skipn (Z.to_nat fsz) ows)) in OCc.
assert (LWA : Z.of_nat (length wa) = fsz) by (unfold wa; rewrite length_firstn, LOWS; clear - FSV; unfold hid in *; lia).
assert (LWC : Z.of_nat (length wc) = 2000 - 2 * fsz) by (unfold wc; rewrite !length_skipn, LOWS; clear - FSV; unfold hid in *; lia).

apply (f32_split asegs m (a_msp a) (sj_msp j) 8) in MSPC; [| rewrite JMSP; clear; unfold hid in *; lia]. destruct MSPC as (MSP1 & MSP2).

sb_unpack X as (HD & FST & PT & LE & SEED & CFG & IDC & PAD). clear X.

assert (OBS : aobj asegs m S 160) by (split; [clear - SP0; unfold hid in *; lia|]; split; [clear - SLO LOR SPT; unfold hid in *; unfold APP_TOP, USTACK_TOP, RT_STACK, SBLOST_STACK in *; lia| exact ACS]).
assert (OBY : aobj asegs m Y (4 * fsz))
by (split; [unfold Y; clear - FO1 FH0 FSV; unfold hid in *; lia|]; split; [unfold Y; clear - FO2 FHLO LOR SPT FSV; unfold hid in *; unfold APP_TOP, USTACK_TOP, RT_STACK, SBLOST_STACK in *; lia|
apply (acc_sub asegs m OUT 8000 Y (4 * fsz) ACO); unfold Y; clear - FSV; unfold hid in *; lia]).
assert (OBQ : aobj asegs m (a_iq a) 32) by (split; [clear - IQP; unfold hid in *; lia|]; split; [clear - IQLO LOR SPT; unfold hid in *; unfold APP_TOP, USTACK_TOP, RT_STACK, SBLOST_STACK in *; lia| exact ACIQ]).
assert (OBM : aobj asegs m (a_msp a) 32)
by (split; [clear - MSP; unfold hid in *; lia|]; split; [clear - MSLO LOR SPT; unfold hid in *; unfold APP_TOP, USTACK_TOP, RT_STACK, SBLOST_STACK in *; lia| exact (acc_sub asegs m (a_msp a) 64 (a_msp a) 32 ACMS ltac:(clear; unfold hid in *; lia) ltac:(clear; unfold hid in *; lia))]).

cps_seg (lost_w1 usp lo S OUT Y fsz s a (Z_to_bv 64 (sbd_first s)) (sj_last_ener j) (sj_seed j) cw rest (sj_iq j) (firstn 8 (sj_msp j))
ra gp (Z_to_bv 64 0x630458) t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m
HD FST PT LE SEED IDC eq_refl IFFS ILPC ltac:(clear - FSV; unfold hid in *; lia) IID OBS S8 SPOS ltac:(unfold IMG_TOP; unfold SEGTOP_A in SIMG; clear - SIMG; unfold hid in *; lia) SLO
eq_refl OCy LREST OBY ltac:(unfold Y; clear - OAL; unfold hid in *; Z.div_mod_to_equations; lia) ltac:(unfold IMG_TOP, Y; unfold SEGTOP_A in FHIMG; clear - FHIMG FO1 FSV; unfold hid in *; lia)
ltac:(unfold Y; clear - FO2 FHLO FSV; unfold hid in *; lia)
IQC ltac:(exact JIQ) OBQ ltac:(clear - IQ8; unfold hid in *; Z.div_mod_to_equations; lia) ltac:(clear - IQLO; unfold hid in *; lia)
MSP1 ltac:(rewrite length_firstn, JMSP; reflexivity) OBM ltac:(clear - MSP8; unfold hid in *; Z.div_mod_to_equations; lia) ltac:(unfold IMG_TOP; unfold SEGTOP_A in MIMG; clear - MIMG; unfold hid in *; lia) ltac:(clear - MSLO; unfold hid in *; lia)
ltac:(unfold hidp; clear - SSH0; unfold hid in *; unfold SH_LO, SH_HI; lia)
ltac:(unfold hidp, Y; clear - FHSH FO1 FO2 FSV; unfold hid in *; unfold SH_LO, SH_HI; lia)
ltac:(unfold hidp; clear - MSH0; unfold hid in *; unfold SH_LO, SH_HI; lia)
ltac:(unfold hidp, Y; clear - FS0 FO1 FO2 FSV; unfold hid in *; lia)
ltac:(unfold hidp; clear - SIQ; unfold hid in *; lia)
ltac:(unfold hidp; clear - SMS; unfold hid in *; lia)
ltac:(unfold hidp, Y; clear - FIQ FO1 FO2 FSV; unfold hid in *; lia)
ltac:(unfold hidp, Y; clear - FMS FO1 FO2 FSV; unfold hid in *; lia)
ltac:(unfold hidp; clear - IQMS; unfold hid in *; lia)
ST0 ltac:(clear - LOR; unfold hid in *; unfold RT_STACK, SBLOST_STACK in *; lia) LOS ltac:(clear - SPT; unfold hid in *; unfold USTACK_TOP in *; lia) CC0 MI0 FRM).
destruct POST as (m1 & xt0 & xt1 & xt2 & xt3 & xt4 & xt5 & xt6 & F1 & fc1 & ys1 & mv1 & seed1 & j8 & -> & MU1 & WM1 & MI1 & FRM1 & ST1 & FR1
& HD1 & FST1 & PT1 & LE1 & SEED1 & IDC1 & YS1 & LYS1 & IQ1 & MSV1 & LMV1).

assert (ART1 : X0ec.ART RT Σ m1).
{ apply (af_frame RT AF Σ m m1 lo ART0 LOW); [| exact WM1]. intros a0 Ha. apply MU1. cbn [outside].
split; [| split; [| split; [| split; [| split; [| split; [| exact I]]]]]]; intros Hin; apply Ha.
- left. clear - Hin LOR SPT. unfold RT_STACK, SBLOST_STACK, USTACK_TOP in *. lia.
- right; right; left. exists S, 160. split; [exact INS0 | clear - Hin; unfold hid in *; lia].
- right; right; left. exists S, 160. split; [exact INS0 | clear - Hin; unfold hid in *; lia].
- right; right; left. exists S, 160. split; [exact INS0 | clear - Hin; unfold hid in *; lia].
- right; right; right; left. exists fh, kh. split; [exact INF | unfold Y in Hin; clear - Hin FO1 FO2 FSV; unfold hid in *; lia].
- right; right; left. exists (a_msp a), 64. split; [exact INMS | clear - Hin; unfold hid in *; lia]. }
set (WF := (OUT, OUT + 8000) :: blocks_ivs (sb_blocks s S a)).
assert (PF1 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp WF m m1).
{ apply (pres_fp_of_munch _ _ _ _ _ m m1 MU1). intros x Hx Ho. unfold WF in Ho. cbn [blocks_ivs map sb_blocks outside blk_addr blk_size fst snd] in Ho |- *.
unfold SBSTATE_SIZEOF in Ho. destruct Ho as (HO & HS & _ & _ & _ & _ & _ & _ & _ & HM & _).
pose proof (SPL x Hx) as SPX.
split; [intros Hin; destruct SPX as [SX|SX]; clear - Hin SX LOR LOW; unfold hid in *; unfold RT_STACK, SBLOST_STACK in *; lia|].
split; [intros Hin; apply HS; clear - Hin; unfold hid in *; lia|]. split; [intros Hin; apply HS; clear - Hin; unfold hid in *; lia|]. split; [intros Hin; apply HS; clear - Hin; unfold hid in *; lia|].
split; [intros Hin; apply HO; unfold Y in Hin; clear - Hin FSV; unfold hid in *; lia|]. split; [intros Hin; apply HM; clear - Hin; unfold hid in *; lia| exact I]. }

destruct (live_below_lo RT AF Σ m _ _ lo ART0 INEX LOW) as (EXP & EXLO & _).
destruct (live_below_lo RT AF Σ m _ _ lo ART0 INOQ LOW) as (OQP & OQLO & _).
destruct (live_below_lo RT AF Σ m _ _ lo ART0 INPG LOW) as (PGP & PGLO & _).
destruct (live_below_lo RT AF Σ m _ _ lo ART0 INER LOW) as (ERP & ERLO & _).
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 INS0 ING0 (NDN 0%nat 1%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as SG0.
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 INS0 ING1 (NDN 0%nat 2%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as SG1.
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 INS0 INEX (NDN 0%nat 3%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as SEX.
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 INS0 INOQ (NDN 0%nat 4%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as SOQ.
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 INS0 INPG (NDN 0%nat 6%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as SPG.
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 INS0 INER (NDN 0%nat 7%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as SER.
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 ING0 INMS (NDN 1%nat 8%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as G0MS.
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 ING1 INMS (NDN 2%nat 8%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as G1MS.
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 INEX INMS (NDN 3%nat 8%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as EXMS.
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 INOQ INMS (NDN 4%nat 8%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as OQMS.
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 INPG INMS (NDN 6%nat 8%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as PGMS.
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 INER INMS (NDN 7%nat 8%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as ERMS.
destruct (frame_live_apart RT AF Σ m fh kh _ _ ART0 INF ING0) as (FG0 & _).
destruct (frame_live_apart RT AF Σ m fh kh _ _ ART0 INF ING1) as (FG1 & _).
destruct (frame_live_apart RT AF Σ m fh kh _ _ ART0 INF INEX) as (FEX & _).
destruct (frame_live_apart RT AF Σ m fh kh _ _ ART0 INF INOQ) as (FOQ & _).
destruct (frame_live_apart RT AF Σ m fh kh _ _ ART0 INF INPG) as (FPG & _).
destruct (frame_live_apart RT AF Σ m fh kh _ _ ART0 INF INER) as (FER & _).
assert (LEX : Z.of_nat (length (sj_exc j)) = sbd_subframeSize s) by exact JEXC.
cps_hide.
trm MU1 WM1 CFG ltac:(clear - SMS FS0 FO1 FO2 FSV SLO LOR; unfold hid in *; unfold Y, RT_STACK, SBLOST_STACK in *; lia).
trm MU1 WM1 PAD ltac:(clear - SMS FS0 FO1 FO2 FSV SLO LOR; unfold hid in *; unfold Y, RT_STACK, SBLOST_STACK in *; lia).
trm MU1 WM1 OCa ltac:(clear - LWA FS0 FMS FO1 FO2 FSV FHLO LOR; unfold hid in *; unfold Y, RT_STACK, SBLOST_STACK in *; lia).
trm MU1 WM1 OCc ltac:(clear - LWC FS0 FMS FO1 FO2 FSV FHLO LOR; unfold hid in *; unfold Y, RT_STACK, SBLOST_STACK in *; lia).
trm MU1 WM1 MSP2 ltac:(rewrite length_skipn, JMSP; cbn; clear - SMS FMS FO1 FO2 FSV MSLO LOR; unfold hid in *; unfold Y, RT_STACK, SBLOST_STACK in *; lia).
trm MU1 WM1 G0C ltac:(rewrite JG0; cbn; clear - SG0 FG0 G0MS FO1 FO2 FSV G0LO LOR; unfold hid in *; unfold Y, RT_STACK, SBLOST_STACK in *; lia).
trm MU1 WM1 G1C ltac:(rewrite JG1; cbn; clear - SG1 FG1 G1MS FO1 FO2 FSV G1LO LOR; unfold hid in *; unfold Y, RT_STACK, SBLOST_STACK in *; lia).
trm MU1 WM1 EXC ltac:(clear - LEX SEX FEX EXMS FO1 FO2 FSV EXLO LOR; unfold hid in *; unfold Y, RT_STACK, SBLOST_STACK in *; lia).
trm MU1 WM1 OQC ltac:(rewrite JOQ; cbn; clear - SOQ FOQ OQMS FO1 FO2 FSV OQLO LOR; unfold hid in *; unfold Y, RT_STACK, SBLOST_STACK in *; lia).
trm MU1 WM1 PGC ltac:(rewrite JPG; cbn; clear - SPG FPG PGMS FO1 FO2 FSV PGLO LOR; unfold hid in *; unfold Y, RT_STACK, SBLOST_STACK in *; lia).
trm MU1 WM1 ERC ltac:(rewrite JER; cbn; clear - SER FER ERMS FO1 FO2 FSV ERLO LOR; unfold hid in *; unfold Y, RT_STACK, SBLOST_STACK in *; lia).

assert (OFW1 : offsh [(usp + -192, usp); (S + 36, S + 40); (S + 132, S + 136); (S + 152, S + 156); (Y, Y + 4 * fsz); (a_msp a, a_msp a + 32)])
by (cbn [offsh]; unfold Y; clear - SSH0 FHSH MSH0 LOS LOR FO1 FO2 FSV; unfold hid in *; unfold SH_LO, SH_HI, RT_STACK, SBLOST_STACK in *; lia).
assert (ACO1 : acc asegs m1 OUT 8000).
{ refine (proj2 (proj2 (aobj_munch asegs _ m m1 OUT 8000 _ MU1 _))).
- split; [clear - FO1 FH0; unfold hid in *; lia|]. split; [clear - FO2 FHLO LOR SPT; unfold hid in *; unfold APP_TOP, USTACK_TOP, RT_STACK, SBLOST_STACK in *; lia| exact ACO].
- apply shfree_of_offsh; [exact OFW1 | clear - FO1 FH0; unfold hid in *; lia | clear - FO2 FHLO LOR SPT; unfold hid in *; unfold APP_TOP, USTACK_TOP, RT_STACK, SBLOST_STACK in *; lia]. }

assert (YJ : rw_cells asegs m1 OUT (f32 (wa ++ ys1))).
{ apply f32_join; [exact OCa|]. replace (OUT + 4 * Z.of_nat (length wa)) with Y by (unfold Y; rewrite LWA; reflexivity). exact YS1. }
assert (LYJ : Z.of_nat (length (wa ++ ys1)) = 2 * fsz) by (rewrite length_app; clear - LWA LYS1; unfold hid in *; lia).
clear OCa YS1.
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 ING0 ING1 (NDN 1%nat 2%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as G01.
assert (EU112 : bv_unsigned (Z_to_bv 64 (usp + -112)) = usp + -112) by (apply unsigned_lit; clear - LOR SPT LOS; unfold hid in *; unfold SH_HI, RT_STACK, SBLOST_STACK, USTACK_TOP in *; lia).
assert (QN : 2 * fsz = 320 \/ 2 * fsz = 640) by (clear - FSV; unfold hid in *; lia).
assert (EA1 : Z_to_bv 64 Y = Z_to_bv 64 (OUT + 2 * (2 * fsz))) by (f_equal; unfold Y; clear; unfold hid in *; lia).
cps_rt (QMF16 (2 * fsz) QN Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1
OUT (a_g0 a) (a_g1 a) lo fh (a_g0 a) 256 (a_g1 a) 256 kh (wa ++ ys1) (sj_g0 j) (sj_g1 j)
FDO MST eq_refl EA1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
YJ LYJ INF FO1 ltac:(clear - FO2 FSV; unfold hid in *; lia)
(acc_sub asegs m1 OUT 8000 OUT (4 * (2 * fsz)) ACO1 ltac:(clear; unfold hid in *; lia) ltac:(clear - FSV; unfold hid in *; lia)) OAL
G0C JG0 ING0 ltac:(clear; unfold hid in *; lia) ltac:(clear; unfold hid in *; lia) ltac:(clear - G08; unfold hid in *; Z.div_mod_to_equations; lia)
G1C JG1 ING1 ltac:(clear; unfold hid in *; lia) ltac:(clear; unfold hid in *; lia) ltac:(clear - G18; unfold hid in *; Z.div_mod_to_equations; lia)
ltac:(clear - G01; unfold hid in *; lia)
ltac:(rewrite EU112; apply (pois_above_le _ usp); [exact POA| clear; unfold hid in *; lia]) FRM1 ART1 MI1
ltac:(rewrite EU112; exact ST1) LOW
ltac:(rewrite EU112; clear - LOR; unfold hid in *; unfold RT_STACK, SBLOST_STACK in *; lia)
ltac:(rewrite EU112; clear - SPT; unfold hid in *; unfold USTACK_TOP in *; lia)
ltac:(rewrite EU112; clear - SPA; unfold hid in *; Z.div_mod_to_equations; lia)).
intros cq (Σq & Hcq & LVq & FRq & SPq & CRq & POq).
cps_unpack_lib Hcq as (vq & m2 & ysq & g0q & g1q & RSq & (ART2 & MI2 & WM2 & ST2) & PRES2 & YSQ & LYSQ & G0Q & LG0Q & G1Q & LG1Q & ACQ).
try rewrite EU112 in PRES2. try rewrite EU112 in ST2.
clear YJ G0C G1C. match goal with H : ASTA RT Σ _ _ _ |- _ => clear H end.

assert (CLS : forall x, usp + -112 <= x < usp -> aclient (rt_live RT Σ) (rt_frames RT Σ) (usp + -112) x)
by (intros x Hx; left; clear - Hx SPT; unfold hid in *; unfold USTACK_TOP in *; lia).
assert (CLL : forall p n x, In (p, n) (rt_live RT Σ) -> p <= x < p + n -> aclient (rt_live RT Σ) (rt_frames RT Σ) (usp + -112) x)
by (intros p n x Hp Hx; right; right; left; exists p, n; split; [exact Hp| exact Hx]).
assert (CLF : forall x, fh <= x < fh + fs_size kh - 8 -> aclient (rt_live RT Σ) (rt_frames RT Σ) (usp + -112) x)
by (intros x Hx; right; right; right; left; exists fh, kh; split; [exact INF| exact Hx]).
assert (OUTQ : forall x, (x < OUT \/ OUT + 8 * fsz <= x) -> (x < a_g0 a \/ a_g0 a + 256 <= x) -> (x < a_g1 a \/ a_g1 a + 256 <= x) ->
outside [(OUT, OUT + 4 * (2 * fsz)); (a_g0 a, a_g0 a + 256); (a_g1 a, a_g1 a + 256)] x)
by (intros x H1 H2 H3; cbn [outside]; split; [clear - H1; lia| split; [clear - H2; lia| split; [clear - H3; lia| exact I]]]).
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 ING0 INIQ (NDN 1%nat 5%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as G0IQ.
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 ING1 INIQ (NDN 2%nat 5%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as G1IQ.
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 ING0 INEX (NDN 1%nat 3%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as G0EX.
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 ING1 INEX (NDN 2%nat 3%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as G1EX.
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 ING0 INOQ (NDN 1%nat 4%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as G0OQ.
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 ING1 INOQ (NDN 2%nat 4%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as G1OQ.
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 ING0 INPG (NDN 1%nat 6%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as G0PG.
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 ING1 INPG (NDN 2%nat 6%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as G1PG.
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 ING0 INER (NDN 1%nat 7%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as G0ER.
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 ING1 INER (NDN 2%nat 7%nat ltac:(lia) ltac:(lia) ltac:(discriminate))) as G1ER.
cps_hide.
assert (LMS2 : Z.of_nat (length (skipn 8 (sj_msp j))) = 8) by (rewrite length_skipn, JMSP; reflexivity).
assert (LMV1z : Z.of_nat (length mv1) = 8) by (rewrite LMV1; reflexivity).
tr1 PRES2 WM2 FR1 ltac:(fun x Hx => apply CLS; clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx FO2 FHLO G0LO G1LO LOR FSV; unfold hid in *; unfold RT_STACK, SBLOST_STACK in *; lia).
tr1 PRES2 WM2 HD1 ltac:(fun x Hx => apply (CLL S 160 x INS0); clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx FS0 SG0 SG1 FO1 FO2 FSV; unfold hid in *; lia).
tr1 PRES2 WM2 FST1 ltac:(fun x Hx => apply (CLL S 160 x INS0); clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx FS0 SG0 SG1 FO1 FO2 FSV; unfold hid in *; lia).
tr1 PRES2 WM2 PT1 ltac:(fun x Hx => apply (CLL S 160 x INS0); clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx FS0 SG0 SG1 FO1 FO2 FSV; unfold hid in *; lia).
tr1 PRES2 WM2 LE1 ltac:(fun x Hx => apply (CLL S 160 x INS0); clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx FS0 SG0 SG1 FO1 FO2 FSV; unfold hid in *; lia).
tr1 PRES2 WM2 SEED1 ltac:(fun x Hx => apply (CLL S 160 x INS0); clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx FS0 SG0 SG1 FO1 FO2 FSV; unfold hid in *; lia).
tr1 PRES2 WM2 CFG ltac:(fun x Hx => apply (CLL S 160 x INS0); clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx FS0 SG0 SG1 FO1 FO2 FSV; unfold hid in *; lia).
tr1 PRES2 WM2 IDC1 ltac:(fun x Hx => apply (CLL S 160 x INS0); clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx FS0 SG0 SG1 FO1 FO2 FSV; unfold hid in *; lia).
tr1 PRES2 WM2 PAD ltac:(fun x Hx => apply (CLL S 160 x INS0); clear - Hx; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx FS0 SG0 SG1 FO1 FO2 FSV; unfold hid in *; lia).
tr1 PRES2 WM2 OCc ltac:(fun x Hx => apply CLF; clear - Hx LWC FO1 FO2 FSV; unfold hid in *; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx LWC FG0 FG1 FO1 FO2 FSV; unfold hid in *; lia).
tr1 PRES2 WM2 IQ1 ltac:(fun x Hx => apply (CLL (a_iq a) 32 x INIQ); clear - Hx JIQ; rewrite JIQ in Hx; cbn in Hx; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx JIQ FIQ G0IQ G1IQ FO1 FO2 FSV; rewrite JIQ in Hx; cbn in Hx; unfold hid in *; lia).
tr1 PRES2 WM2 MSV1 ltac:(fun x Hx => apply (CLL (a_msp a) 64 x INMS); clear - Hx LMV1z; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx LMV1z FMS G0MS G1MS FO1 FO2 FSV; unfold hid in *; lia).
tr1 PRES2 WM2 MSP2 ltac:(fun x Hx => apply (CLL (a_msp a) 64 x INMS); clear - Hx LMS2; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx LMS2 FMS G0MS G1MS FO1 FO2 FSV; unfold hid in *; lia).
tr1 PRES2 WM2 EXC ltac:(fun x Hx => apply (CLL (a_exc a) (4 * sbd_subframeSize s) x INEX); clear - Hx LEX; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx LEX FEX G0EX G1EX FO1 FO2 FSV; unfold hid in *; lia).
tr1 PRES2 WM2 OQC ltac:(fun x Hx => apply (CLL (a_oq a) 32 x INOQ); clear - Hx JOQ; rewrite JOQ in Hx; cbn in Hx; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx JOQ FOQ G0OQ G1OQ FO1 FO2 FSV; rewrite JOQ in Hx; cbn in Hx; unfold hid in *; lia).
tr1 PRES2 WM2 PGC ltac:(fun x Hx => apply (CLL (a_pg a) 16 x INPG); clear - Hx JPG; rewrite JPG in Hx; cbn in Hx; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx JPG FPG G0PG G1PG FO1 FO2 FSV; rewrite JPG in Hx; cbn in Hx; unfold hid in *; lia).
tr1 PRES2 WM2 ERC ltac:(fun x Hx => apply (CLL (a_er a) 16 x INER); clear - Hx JER; rewrite JER in Hx; cbn in Hx; lia)
ltac:(fun x Hx => apply OUTQ; clear - Hx JER FER G0ER G1ER FO1 FO2 FSV; rewrite JER in Hx; cbn in Hx; unfold hid in *; lia).

assert (PF2 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp WF m m2).
{ apply (pres_fp_trans _ _ _ _ m m1 m2 PF1).
apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ) (rt_frames RT Σ) (usp + -112) _ m1 m2 PRES2); [intros e He; exact He| intros e He; exact He| clear; lia|].
intros x Hx Ho. unfold WF in Ho. cbn [blocks_ivs map sb_blocks outside blk_addr blk_size fst snd] in Ho |- *.
destruct Ho as (HO & _ & H0 & H1 & _).
split; [intros Hin; apply HO; clear - Hin FSV; unfold hid in *; lia|]. split; [exact H0|]. split; [exact H1| exact I]. }
clear PF1.

pose proof (live_facts RT AF Σ m _ _ ART0 ING0) as (_ & _ & _ & G0SH).
pose proof (live_facts RT AF Σ m _ _ ART0 ING1) as (_ & _ & _ & G1SH).
assert (ACO2 : acc asegs m2 OUT 8000).
{ apply (acc_pres_fp_frame _ _ _ _ m1 m2 fh kh OUT 8000 PRES2 INF ltac:(clear - FH64; Z.div_mod_to_equations; lia) (fs_size_mod8 kh) ltac:(clear - FH0; lia) FO1
ltac:(clear - FO2; lia)); [| exact ACO1].
intros i Hi. pose proof (shad_in_window (OUT + i) ltac:(clear - Hi FO1 FO2 FH0 FHLO LOR SPT; unfold RT_STACK, SBLOST_STACK, USTACK_TOP in *; lia)) as SW.
apply OUTQ; clear - SW FHSH FO1 FO2 G0SH G1SH FSV; unfold hid in *; unfold SH_LO, SH_HI in *; lia. }
clear ACO1 ACQ.

assert (INS0q : In (S, 160) (rt_live RT Σq)) by (rewrite LVq; exact INS0).
destruct (af_acc_live RT AF Σq m2 S 160 ART2 INS0q) as (_ & ACS2).
assert (OBS2 : aobj asegs m2 S 160) by (split; [clear - SP0; lia|]; split; [clear - SLO LOR SPT; unfold APP_TOP, USTACK_TOP, RT_STACK, SBLOST_STACK in *; lia| exact ACS2]).

cps_seg (lost_w2 usp lo S (sbd_submodeID s) a3 j8 ra gp (Z_to_bv 64 0x630458) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 FR1 IDC1 OBS2 S8 ltac:(clear - SSH0; unfold hid in *; unfold SH_LO, SH_HI; lia) SLO IID ST2
ltac:(clear - LOR; unfold RT_STACK, SBLOST_STACK in *; lia) LOS ltac:(clear - SPT; unfold USTACK_TOP in *; lia) MI2).
destruct POST as (m3 & v3 & -> & MU3 & WM3 & MI3 & ST3 & IDC3).

assert (LOWq : rt_sp0 RT Σq - STACK_WIN <= lo) by (rewrite SPq; exact LOW).
assert (ART3 : X0ec.ART RT Σq m3).
{ apply (af_frame RT AF Σq m2 m3 lo ART2 LOWq); [| exact WM3]. intros a0 Ha. apply MU3. cbn [outside].
split; [| exact I]. intros Hin; apply Ha. right; right; left. exists S, 160. split; [exact INS0q | clear - Hin; lia]. }
assert (PF3 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp WF m m3).
{ apply (pres_fp_trans _ _ _ _ m m2 m3 PF2). apply (pres_fp_of_munch _ _ _ _ _ m2 m3 MU3). intros x Hx Ho. unfold WF in Ho.
cbn [blocks_ivs map sb_blocks outside blk_addr blk_size fst snd] in Ho |- *. unfold SBSTATE_SIZEOF in Ho. destruct Ho as (_ & HS & _).
split; [intros Hin; apply HS; clear - Hin; lia| exact I]. }
clear PF2.
trm MU3 WM3 HD1 ltac:(clear; lia). trm MU3 WM3 FST1 ltac:(clear; lia). trm MU3 WM3 PT1 ltac:(clear; lia). trm MU3 WM3 LE1 ltac:(clear; lia).
trm MU3 WM3 SEED1 ltac:(clear; lia). trm MU3 WM3 CFG ltac:(clear; lia). trm MU3 WM3 PAD ltac:(clear; lia).
trm MU3 WM3 YSQ ltac:(clear - LYSQ FS0 FO1 FO2 FSV; unfold hid in *; lia).
trm MU3 WM3 OCc ltac:(clear - LWC FS0 FO1 FO2 FSV; unfold hid in *; lia).
trm MU3 WM3 G0Q ltac:(rewrite LG0Q; cbn; clear - SG0; unfold hid in *; lia).
trm MU3 WM3 G1Q ltac:(rewrite LG1Q; cbn; clear - SG1; unfold hid in *; lia).
trm MU3 WM3 EXC ltac:(clear - LEX SEX; unfold hid in *; lia).
trm MU3 WM3 OQC ltac:(rewrite JOQ; cbn; clear - SOQ; unfold hid in *; lia).
trm MU3 WM3 IQ1 ltac:(rewrite JIQ; cbn; clear - SIQ; unfold hid in *; lia).
trm MU3 WM3 MSV1 ltac:(clear - LMV1z SMS; unfold hid in *; lia).
trm MU3 WM3 MSP2 ltac:(clear - LMS2 SMS; unfold hid in *; lia).
trm MU3 WM3 PGC ltac:(rewrite JPG; cbn; clear - SPG; unfold hid in *; lia).
trm MU3 WM3 ERC ltac:(rewrite JER; cbn; clear - SER; unfold hid in *; lia).

assert (ACO3 : acc asegs m3 OUT 8000).
{ refine (proj2 (proj2 (aobj_munch asegs _ m2 m3 OUT 8000 _ MU3 _))).
- split; [clear - FO1 FH0; lia|]. split; [clear - FO2 FHLO LOR SPT; unfold APP_TOP, USTACK_TOP, RT_STACK, SBLOST_STACK in *; lia| exact ACO2].
- apply shfree_of_offsh; [cbn [offsh]; clear - SSH0; unfold hid in *; unfold SH_LO, SH_HI; lia | clear - FO1 FH0; lia |
clear - FO2 FHLO LOR SPT; unfold APP_TOP, USTACK_TOP, RT_STACK, SBLOST_STACK in *; lia]. }

set (j' := SBJ (sj_last_ener j) seed1 (sj_pad1 j) (sj_pad2 j) g0q g1q (sj_exc j) (sj_oq j) (sj_iq j) (mv1 ++ skipn 8 (sj_msp j)) (sj_pg j) (sj_er j)).
assert (X3 : rw_cells asegs m3 S (SBCELLS (set_sbd_first s 1) a OUT j')).
{ apply sb_pieces_iff. exact (conj HD1 (conj FST1 (conj PT1 (conj LE1 (conj SEED1 (conj CFG (conj IDC3 PAD))))))). }
assert (JOK3 : sb_junk_ok (set_sbd_first s 1) j').
{ unfold sb_junk_ok. cbn [j' sj_pad1 sj_pad2 sj_g0 sj_g1 sj_exc sj_oq sj_iq sj_msp sj_pg sj_er].
refine (conj JP1 (conj JP2 (conj LG0Q (conj LG1Q (conj JEXC (conj JOQ (conj JIQ (conj _ (conj JPG JER))))))))).
rewrite length_app, length_skipn, LMV1, JMSP. reflexivity. }
assert (MSX : rw_cells asegs m3 (a_msp a) (f32 (mv1 ++ skipn 8 (sj_msp j)))).
{ apply f32_join; [exact MSV1|]. rewrite LMV1. exact MSP2. }
assert (BUFS3 : sb_bufs asegs m3 a j') by (exact (conj G0Q (conj G1Q (conj EXC (conj OQC (conj IQ1 (conj MSX (conj PGC ERC)))))))).
assert (OC3 : rw_cells asegs m3 OUT (f32 (ysq ++ wc))).
{ apply f32_join; [exact YSQ|]. replace (OUT + 4 * Z.of_nat (length ysq)) with (OUT + 8 * fsz) by (rewrite LYSQ; clear; lia). exact OCc. }
assert (LOC3 : length (ysq ++ wc) = 2000%nat) by (rewrite length_app; clear - LYSQ LWC FSV; unfold hid in *; lia).

apply Hk. exists Σq. split; [| split; [exact LVq|]; split; [exact FRq|]; split; [exact SPq|]; split; [exact CRq| exact POq]].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists v3, m3, j', (ysq ++ wc).
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact RSq]|].
split. { split; [exact ART3|]. split; [exact MI3|]. split; [cps_wmono| exact ST3]. }
split; [exact PF3|]. split; [exact X3|]. split; [exact JOK3|]. split; [exact BUFS3|]. split; [exact OC3|]. split; [exact LOC3| exact ACO3].
Qed.
End SbLost.
