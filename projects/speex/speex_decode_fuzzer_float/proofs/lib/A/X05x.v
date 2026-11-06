(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s X05u
X081 X05l X07y X05m X09f X06d X069 X05y X05z X060 X05w X064 X062 X063.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0yr X0wl X0wn X0ys X0yq X0x2 X0zo X0wr X0ws X0wt X0wp X0wx X0wv X0ww.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zo OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ws OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wp OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wx OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wv OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ww.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CtlGsrLive.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.

Definition ctl_gsr_live_at (d : dec_state bptr) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (OUT STEREO S : Z) (LBD : list block) (P lo pb nb : Z),
fdfs_only PMc -> mat_stable PMc ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 25 -> a2 = Z_to_bv 64 P -> tp = Z_to_bv 64 0x638c98 ->
DREP OUT STEREO m S d LBD -> (dec_depth d <= 3)%nat -> List.NoDup (map blk_id LBD) ->
(exists w : word, rw_cells bsegs m P [C4 w]) ->
(forall b, In b LBD -> In (blk_addr b, blk_size b) (rt_live RT Σ)) ->
In (pb, nb) (rt_live RT Σ) -> pb <= P -> P + 4 <= pb + nb -> P mod 4 = 0 -> ~ In pb (map blk_id LBD) ->
(length (rt_frames RT Σ) + dec_depth d <= FRAMES_MAX)%nat -> Z.of_nat (dec_depth d) <= rt_credit RT Σ + 1 ->
ART RT Σ m -> mem_inv bsegs m -> frm0 fc ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + ctl_stack d <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 32 = 0 ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_speex_decoder_ctl m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists m',
ret_stL (fun _ fc' => frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) ((P, P + 4) :: blocks_ivs LBD) m m'
/\ DREP OUT STEREO m' S d LBD
/\ rw_cells bsegs m' P [C4 (Z_to_bv 64 (fst (speex_decoder_ctl d CtlGetSamplingRate)))]
/\ - 2^31 <= fst (speex_decoder_ctl d CtlGetSamplingRate) < 2^31) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ - (Z.of_nat (dec_depth d) - 1) <= rt_credit RT Σ' <= rt_credit RT Σ
/\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem ctl_gsr_live_nb : forall st, ctl_gsr_live_at (DecNB st).
Proof using AF AF_LIB.
intros st Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
OUT STEREO S LBD P lo pb nb FDO MST -> -> -> -> REP DEP ND PRE LIVE INP FP1 FP2 PAL NINB FRM CRD ART0 MI0 FRM0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
cbn [ctl_stack] in LOR. unfold NBCTL_STACK in LOR.
pose proof REP as REP0. cbn [decst_rep] in REP0. destruct REP0 as [ELBD NB]. subst LBD.
pose proof (LIVE _ ltac:(left; reflexivity)) as INL. unfold blk_addr, blk_size in INL. cbn [fst snd] in INL. unfold NBSTATE_SIZEOF in INL.
destruct (live_below_lo RT AF Σ m S 2968 lo ART0 INL LOW) as (BD0 & BD1 & LOS).
destruct (af_acc_live RT AF Σ m S 2968 ART0 INL) as (_ & ACS).
pose proof (live_facts RT AF Σ m S 2968 ART0 INL) as (_ & _ & SIMG & SHI).
destruct (live_below_lo RT AF Σ m pb nb lo ART0 INP LOW) as (PB0 & PBL & _).
destruct (af_acc_live RT AF Σ m pb nb ART0 INP) as (_ & ACPB).
pose proof (live_facts RT AF Σ m pb nb ART0 INP) as (_ & _ & _ & PHI).
assert (NES : pb <> S) by (intros E; apply NINB; rewrite E; cbn [map blk_id blk_addr fst snd]; left; reflexivity).
pose proof (live_apart RT AF Σ m pb nb S 2968 ART0 INP INL NES) as PAP.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
pose proof (AF_LIB Σ m ART0) as LC0.
assert (OBM : aobj bsegs m A_speex_nb_mode 96)
by (apply (aobj_lit RT AF Σ m A_speex_nb_mode 96 ART0); [unfold ACC_LITS, A_speex_nb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_speex_nb_mode; lia | unfold A_speex_nb_mode, APP_TOP; lia]).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(P, P + 4); (S, S + 2968)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
cps_norm.
refine (rz_evt RT AF Σ PMc _ _ T c MST Hc (rctl_nbA st OUT STEREO S _ CtlGetSamplingRate P lo usp ra gp (Z_to_bv 64 6524056) t0 t1 t2 s0 s1 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m eq_refl REP I PRE _ _ PAL ltac:(clear - PB0 FP1; lia) OBM _ _ ST0 _ _ _ CC0 LC0 MI0 FRM0) _).
- intros b [<-|[]]. unfold ablk, blk_addr, blk_size. cbn [fst snd]. unfold NBSTATE_SIZEOF.
split; [split; [lia|]; split; [ulc| exact ACS]|]. split; [exact (proj1 NB)|]. split; [unfold SH_LO, SH_HI; lia|]. split; [unfold IMG_TOP_B, IMG_TOP; ulc| exact BD1].
- cbn [creq_size]. split; [lia|]. split; [ulc| apply (acc_sub bsegs m pb nb P 4 ACPB); lia].
- cbn [creq_size]. left. lia.
- intros b [<-|[]]. unfold blk_addr, blk_size. cbn [fst snd creq_size]. unfold NBSTATE_SIZEOF. clear - PAP FP1 FP2. lia.
- exact LOS.
- unfold NBCTL_STACK. ulc.
- ulc.
- intros ms' c' POST Hc'. clear Hc.
destruct POST as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & F' & fc' & m' & -> & MU & WM & MI' & FRM' & ST' & REP' & CP' & _).
rewrite (ctlW_grp1 _ _ _ _ _ (eq_refl : creq_grp1 CtlGetSamplingRate = true)) in MU. cbn [blocks_ivs map blk_addr blk_size fst snd creq_size] in MU. unfold NBSTATE_SIZEOF in MU.
cps_seg_post.
apply Hk. exists Σ. split; [| cbn [dec_depth]; repeat split; lia].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m'.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM']|].
split. { split; [assumption|]. split; [exact MI'|]. split; [exact WM| exact ST']. }
split; [exact PF|]. split; [exact REP'|]. exact CP'.
Qed.

Theorem ctl_gsr_live_sb : forall s low, ctl_gsr_live_at (DecSB s low).
Proof using AF SM0 AF_LIB.
intros s low Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
OUT STEREO S LBD P lo pb nb FDO MST -> -> -> -> REP DEP ND PRE LIVE INP FP1 FP2 PAL NINB FRM CRD ART0 MI0 FRM0 ST0 LOW LOR SPT SPA.
set (r := CtlGetSamplingRate) in *. assert (GRP : creq_grp1 r = true) by reflexivity.
assert (PRE' : creq_pre STEREO m S (DecSB s low) P r) by exact PRE. clear PRE. rename PRE' into PRE.
change 4 with (creq_size r) in FP2.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
cbn [ctl_stack dec_depth] in LOR, DEP, FRM, CRD.
assert (CSP : 0 <= ctl_stack low) by (clear; induction low; cbn [ctl_stack]; unfold NBCTL_STACK; lia).
pose proof REP as REP0. cbn [decst_rep] in REP0. destruct REP0 as (a & j & LBL & ELBD & S8 & SPOS & INV & JOK & X & BUFS & OUTL & RLOW).
pose proof INV as (IMODE & _).
rewrite sb_cells_split in X.

assert (INL : In (S, 160) (rt_live RT Σ)).
{ specialize (LIVE (sbd_blk s, S, SBSTATE_SIZEOF)). rewrite ELBD in LIVE. specialize (LIVE ltac:(left; reflexivity)). exact LIVE. }
destruct (live_below_lo RT AF Σ m S 160 lo ART0 INL LOW) as (_ & BS1 & LOS).
destruct (af_acc_live RT AF Σ m S 160 ART0 INL) as (_ & ACS).
pose proof (live_facts RT AF Σ m S 160 ART0 INL) as (_ & _ & _ & SHI).

destruct (live_below_lo RT AF Σ m pb nb lo ART0 INP LOW) as (FP0 & BF1 & _).
pose proof (live_facts RT AF Σ m pb nb ART0 INP) as (_ & _ & _ & FPHI).
assert (NES : pb <> S) by (intros E; apply NINB; rewrite ELBD, E; cbn [sb_blocks app map blk_id blk_addr fst snd]; left; reflexivity).
pose proof (live_apart RT AF Σ m pb nb S 160 ART0 INP INL NES) as FLA1.
assert (SZ : 0 <= creq_size r <= 24) by (destruct r; cbn; lia).

pose proof (AF_LIB Σ m ART0) as LC0.
set (MP := sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode (sbd_mode s)) in *.
assert (MPF : exists c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11, ro_cells bsegs m MP (sb_desc_cells c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11)
/\ aobj bsegs m MP 96 /\ MP mod 8 = 0 /\ 0x10000 <= MP /\ MP + 104 <= 0x65a180).
{ subst MP. destruct IMODE as [E|E]; rewrite E; cbn [sb_mode_ptr].
- do 12 eexists. split; [exact (lib_const m A_speex_wb_mode LC_speex_wb_mode LC0 ltac:(lc_in))|].
split; [apply (aobj_lit RT AF Σ m A_speex_wb_mode 96 ART0); [unfold ACC_LITS, A_speex_wb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_speex_wb_mode; lia | unfold A_speex_wb_mode, APP_TOP; lia]|].
unfold A_speex_wb_mode. repeat split; lia.
- do 12 eexists. split; [exact (lib_const m A_speex_uwb_mode LC_speex_uwb_mode LC0 ltac:(lc_in))|].
split; [apply (aobj_lit RT AF Σ m A_speex_uwb_mode 96 ART0); [unfold ACC_LITS, A_speex_uwb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_speex_uwb_mode; lia | unfold A_speex_uwb_mode, APP_TOP; lia]|].
unfold A_speex_uwb_mode. repeat split; lia. }
destruct MPF as (c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & c8 & c9 & c10 & c11 & ND0 & OBM & MP8 & MPLO & MPHI).
pose proof (eq_refl : MP = sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode (sbd_mode s)) as EMP. clearbody MP.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
assert (OBS : aobj bsegs m S 160) by (split; [lia|]; split; [unfold APP_TOP, STACK_WIN, USTACK_TOP, RT_STACK in *; lia| exact ACS]).
assert (EW : creq_ivs P r = [(P, P + creq_size r)]) by (destruct r; try discriminate GRP; reflexivity).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp (blocks_ivs LBD) m) as PF.
pose proof (fun E : rt_frames RT Σ = [] => af_pois_nil RT AF Σ m ART0 E) as PNIL.
assert (LIVE0 : blocks_in_live RT Σ LBD) by exact LIVE.
assert (POUT : forall x, P <= x < P + creq_size r -> outside (blocks_ivs LBD) x).
{ intros x Hx. apply outside_blocks_ivs. intros b Hb Hin.
assert (NEB : pb <> blk_addr b) by (intros E; apply NINB; rewrite E; exact (in_map blk_id _ _ Hb)).
pose proof (live_apart RT AF Σ m pb nb _ _ ART0 INP (LIVE b Hb) NEB) as B2. clear - B2 Hx Hin FP1 FP2. lia. }

assert (OFFW : forall x, SH_LO <= x < SH_HI -> outside ((P, P + creq_size r) :: blocks_ivs LBD) x).
{ intros x Hx. split; [clear - Hx FPHI FP2 FP1; unfold SH_LO, SH_HI in Hx; cbn [fst snd]; lia| exact (outside_blocks_shadow RT AF Σ m LBD x ART0 LIVE0 Hx)]. }
assert (PR0 : 0 <= P) by lia.
assert (PR1 : P + creq_size r <= 2^64) by (clear - FP2 BF1 LOR SPT CSP; unfold RT_STACK, USTACK_TOP in *; lia).
assert (PCL : forall x, P <= x < P + creq_size r -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x)
by (intros x Hx; right; right; left; exists pb, nb; split; [exact INP| lia]).
pose proof (fun m' S' d' (PR : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp (blocks_ivs LBD) m m') (WM : wmono bsegs m m') =>
creq_pre_agree STEREO m m' S S' (DecSB s low) d' P r GRP PRE
(agree_at_of_pres_fp _ _ usp _ m m' P (creq_size r) PR WM PR0 PR1 (fun x Hx => conj (PCL x Hx) (POUT x Hx)))) as PREK.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
assert (CODE : sbctl_code_ok (ctl_req_code r)) by (unfold sbctl_code_ok; destruct r; cbn [ctl_req_code]; tauto).
assert (CRNG : 0 <= ctl_req_code r < 2^31) by (destruct r; cbn; lia).
assert (LO96 : lo <= usp + -96) by (clear - LOR CSP; unfold RT_STACK in LOR; lia).
cps_norm. cps_hide.

piece X HD. rename X into TL. unfold sbhd in HD. unfold sbtl in TL.
Time cps_seg (sbctl_w1 usp lo S MP P (ctl_req_code r)). { reflexivity. } { ulc. } { ulc. }
destruct POST as (m1 & j8 & xt1 & xa3 & xa4 & xa5 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
assert (BOUT : forall b x, In b (tl (sb_blocks s S a) ++ LBL) -> blk_addr b <= x < blk_addr b + blk_size b ->
x < lo /\ (x < S \/ S + 160 <= x) /\ (x < pb \/ pb + nb <= x)).
{ intros b x Hb Hx.
assert (Hb' : In b LBD) by (rewrite ELBD; cbn [sb_blocks tl app] in Hb |- *; right; exact Hb).
pose proof (LIVE b Hb') as LB.
destruct (live_below_lo RT AF Σ m _ _ lo ART0 LB LOW) as (_ & B1 & _).
assert (NEB : pb <> blk_addr b) by (intros E; apply NINB; rewrite E; exact (in_map blk_id _ _ Hb')).
pose proof (live_apart RT AF Σ m pb nb _ _ ART0 INP LB NEB) as B2.
assert (NE : blk_addr b <> S).
{ rewrite ELBD in ND. cbn [sb_blocks app map blk_id blk_addr fst snd] in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI _].
intros E. apply NI. rewrite <- E. cbn [sb_blocks tl app] in Hb. exact (in_map blk_id _ _ Hb). }
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 LB INL NE) as B3. clear - B1 B2 B3 Hx. lia. }
pose proof (agree_blocks_of_munch bsegs _ m m1 (tl (sb_blocks s S a) ++ LBL) MU1 WM1
ltac:(intros b x Hb Hx; pose proof (BOUT b x Hb Hx) as H1; clear - H1 LO96; cbn [outside]; split; [lia| exact I])) as AG1.
Time cps_seg_post.
apply (sb_bufs_agree s S a j m m1) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG1| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG1| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG1.

cps_rt_sized SM0 0. { cbn; tauto. } { pose proof (dec_depth_pos low) as DP; clear - CRD DP; lia. } { cps_callok. }
intros cc2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR1 & FPOS & F64 & FTOP & PO1).
Time cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRF & WRS).
assert (LIVE1 : blocks_in_live RT Σ1 LBD) by (intros b Hb; rewrite LV1; exact (LIVE b Hb)).
pose proof (agree_blocks_of_pres RT Σ (rt_frames RT Σ) (usp + -96) m1 m2 (tl (sb_blocks s S a) ++ LBL) PRES2 WM2
ltac:(intros b Hb; apply LIVE; rewrite ELBD; cbn [sb_blocks tl app] in Hb |- *; right; exact Hb)) as AG2.
apply (sb_bufs_agree s S a j m1 m2) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG2| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG2| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG2.
Time cps_new_frame ART2 FRS1 LV1 SP1 WRF WRS sf. cps_hide.
assert (BOUT2 : forall b x, In b (tl (sb_blocks s S a) ++ LBL) -> blk_addr b <= x < blk_addr b + blk_size b ->
(x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)).
{ intros b x Hb Hx.
assert (Hb' : In b LBD) by (rewrite ELBD; cbn [sb_blocks tl app] in Hb |- *; right; exact Hb).
destruct (frame_live_apart RT AF Σ1 m2 f 0%nat _ _ ART2 INF (LIVE1 b Hb')) as (B2 & B3).
change (fs_size 0) with 64 in B2, B3. rewrite SHF0, <- SHF in B3. clear - B2 B3 Hx. lia. }

cps_seg (sbctl_w2 usp lo S P (ctl_req_code r) f sf).
destruct POST as (m3 & a0' & a1' & a2' & j24 & l32 & j36 & j40 & l48 & j52 & -> & MU3 & WM3 & MI3 & ST3 & FR3 & FRB3 & FRS3).
Time pose proof (agree_blocks_of_munch bsegs _ m2 m3 (tl (sb_blocks s S a) ++ LBL) MU3 WM3
ltac:(intros b x Hb Hx; pose proof (BOUT b x Hb Hx) as H1; pose proof (BOUT2 b x Hb Hx) as H2; clear - H1 H2 LO96; cbn [outside]; repeat split; lia)) as AG3.
apply (sb_bufs_agree s S a j m2 m3) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG3| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG3| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG3 FR1 FRB FRS.
unfold sbctl_frame in FR3. unfold sbctl_fhdr in FRB3. unfold sbctl_shadow, bF1, bF3, bF8 in FRS3.
Time cps_seg_post.
destruct (af_acc_live RT AF Σ1 m3 S 160 ART INL) as (_ & ACS3).
assert (OBS3 : aobj bsegs m3 S 160) by (split; [lia|]; split; [ulc| exact ACS3]).
assert (SOFF : S + 160 <= SH_LO \/ SH_HI <= S) by (clear - SHI; unfold hid, SH_LO, SH_HI in *; lia).
assert (HD3 : rw_cells bsegs m3 S (sbhd MP (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s))
(Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s))
(Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 (sbd_lpc_enh_enabled s)))) by exact HD.
assert (SBF : 0 < S /\ S + 160 < 2^63) by (split; ulc).
assert (PBF : 0 < P /\ P + 24 < 2^63) by (split; [clear - FP0 FP1; lia| ulc]).
clear HD. cps_hide.

assert (WM03 : wmono bsegs m m3) by cps_wmono.
pose proof (PREK m3 (a_low a) low PF WM03) as PREL3. pose proof (PREK m3 S (DecSB s low) PF WM03) as PRE3. clear PREK PRE.
apply (pres_fp_weaken _ _ _ _ ((P, P + creq_size r) :: blocks_ivs LBD)) in PF; [| intros x Hx; exact (proj2 Hx)].
lazymatch goal with A : X14x.ART RT Σ1 m3 |- _ => destruct (af_acc_live RT AF Σ1 m3 pb nb A INP) as (_ & ACPB3) end.
assert (ACP3 : acc bsegs m3 P (creq_size r)) by (apply (acc_sub bsegs m3 pb nb P _ ACPB3); lia).
assert (OUTB : forall x, (lo <= x \/ (S <= x < S + 160) \/ (pb <= x < pb + nb) \/ (f <= x < f + 64) \/ (sf <= x < sf + 8)) -> outside (blocks_ivs LBL) x).
{ intros x Hx. apply outside_blocks_ivs. intros b Hb Hin.
pose proof (BOUT b x ltac:(apply in_app_iff; right; exact Hb) Hin) as H1. pose proof (BOUT2 b x ltac:(apply in_app_iff; right; exact Hb) Hin) as H2.
clear - Hx H1 H2. lia. }
assert (APL : forall b x, In b (tl (sb_blocks s S a)) -> blk_addr b <= x < blk_addr b + blk_size b -> outside (blocks_ivs LBL) x).
{ intros b x Hb Hx. apply outside_blocks_ivs. intros b2 Hb2 Hin.
assert (NE : blk_addr b <> blk_addr b2).
{ rewrite ELBD, map_app in ND. apply (NoDup_app_in_neq _ _ (blk_id b) (blk_id b2) ND); [apply in_map; cbn [sb_blocks tl] in Hb |- *; right; exact Hb| apply in_map; exact Hb2]. }
pose proof (live_apart RT AF Σ1 m3 _ _ _ _ ART (LIVE1 b ltac:(rewrite ELBD; apply in_app_iff; left; cbn [sb_blocks tl] in Hb |- *; right; exact Hb))
(LIVE1 b2 ltac:(rewrite ELBD; apply in_app_iff; right; exact Hb2)) NE) as AP.
clear - AP Hx Hin. lia. }
assert (PFA : P + creq_size r <= f \/ f + 64 <= P).
{ assert (SZ1 : 1 <= creq_size r) by (clear - GRP; destruct r; try discriminate GRP; cbn; lia).
assert (I1 : P <= P < P + creq_size r) by (clear - SZ1; lia).
assert (I2 : P <= P + creq_size r - 1 < P + creq_size r) by (clear - SZ1; lia).
pose proof (NAF P (PCL P I1)) as (N1 & _).
pose proof (NAF (P + creq_size r - 1) (PCL _ I2)) as (N2 & _).
change (fs_size 0) with 64 in N1, N2. clear - N1 N2 SZ SZ1. lia. }
assert (NDL : List.NoDup (map blk_id LBL)) by (rewrite ELBD, map_app in ND; exact (List.NoDup_app_remove_l _ _ ND)).
assert (LIVEL : forall b, In b LBL -> In (blk_addr b, blk_size b) (rt_live RT Σ1)) by (intros b Hb; apply LIVE1; rewrite ELBD; apply in_app_iff; right; exact Hb).
assert (FRM1 : (length (rt_frames RT Σ1) + dec_depth low <= FRAMES_MAX)%nat) by (rewrite FRS1; cbn [length]; clear - FRM; lia).
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -96)) = usp + -96) by (apply unsigned_lit; ulc).
assert (SPA96 : (usp + -96) mod 32 = 0) by (clear - SPA; Z.div_mod_to_equations; lia).
subst LBD. cbn [sb_blocks app blocks_ivs map blk_addr blk_size fst snd] in PF. unfold SBSTATE_SIZEOF in PF.
subst r. cbn [ctl_req_code creq_size creq_align] in *.
{
destruct PRE3 as (w3 & ARG3).
assert (OBP3 : aobj bsegs m3 P 4) by (split; [lia|]; split; [ulc| exact ACP3]).
assert (APS : P + 4 <= S \/ S + 160 <= P) by (clear - FLA1 FP1 FP2; unfold hid in FLA1; lia).
assert (RV : - 2^31 <= sbd_sampling_rate s < 2^31) by (clear - INV; unfold sb_inv in INV; tauto).
assert (DP0 : (1 <= dec_depth low)%nat) by apply dec_depth_pos.
cps_seg (sbarm_gsr usp S P f sf).
destruct POST as (m4 & yb1 & yb2 & -> & HD4 & ARG4 & MU4 & WM4 & MI4).
pose proof (agree_blocks_of_munch bsegs _ m3 m4 (tl (sb_blocks s S a) ++ LBL) MU4 WM4
ltac:(intros b x Hb Hx; pose proof (BOUT b x Hb Hx) as H1; clear - H1 FP1 FP2; cbn [outside]; split; [lia| exact I])) as AG4.
apply (sb_bufs_agree s S a j m3 m4) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG4| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG4| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG4 HD3 ARG3 OBP3 APS. unfold sbhd in HD4.
cps_seg_post.

assert (FRSE : rw_cells bsegs m4 sf (sbctl_shadow bF8 bF8)) by exact FRS3. clear FRS3.
chunk_uncons FRB3 as HDF.
cps_seg (sbctl_epi_a usp f sf).
destruct POST as (m6 & -> & MU6 & WM6 & MI6 & FRS6).
pose proof (agree_blocks_of_munch bsegs _ m4 m6 (tl (sb_blocks s S a) ++ LBL) MU6 WM6
ltac:(intros b x Hb Hx; pose proof (BOUT2 b x Hb Hx) as H2; clear - H2; cbn [outside]; repeat split; lia)) as AG6.
apply (sb_bufs_agree s S a j m4 m6) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG6 HDF FRSE FRB3 . unfold sbctl_shadow_dead, bF5 in FRS6. cbn [map repeat] in FRS6.
cps_seg_post.

assert (EF2 : rt_frames RT Σ1 = (f, 0%nat) :: rt_frames RT Σ) by (exact FRS1).
assert (EL2 : rt_live RT Σ1 = rt_live RT Σ) by (exact LV1).
lazymatch goal with A : X14x.ART RT Σ1 _ |- _ => rename A into ARTX end.
cps_release_intro ARTX EF2 EL2 (fun E : rt_frames RT Σ = [] => eq_trans PO1 (PNIL E)) Σ3 fl.
assert (FLS : fl < S \/ S + 160 <= fl).
{ destruct (Z_lt_dec fl S) as [L|L]; [left; exact L|]. destruct (Z_le_dec (S + 160) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; left. exists S, 160. split; [exact INL| clear - L G; lia]. }
assert (FLP : fl < pb \/ pb + nb <= fl).
{ destruct (Z_lt_dec fl pb) as [L|L]; [left; exact L|]. destruct (Z_le_dec (pb + nb) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; left. exists pb, nb. split; [exact INP| clear - L G; lia]. }
assert (FR6 : rw_cells bsegs m6 (usp + -96) (sbctl_frame (C8 (Z_to_bv 64 f)) s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) by exact FR3. clear FR3.
cps_seg (sbctl_epi_b usp lo f fl).
destruct POST as (m7 & -> & MU7 & WM7 & MI7 & ST7 & FLG7).
assert (AG7 : agree_blocks bsegs m6 m7 (tl (sb_blocks s S a) ++ LBL)).
{ apply (agree_blocks_of_munch bsegs _ m6 m7 _ MU7 WM7). intros b x Hb Hx. cbn [outside]. split; [| exact I]. intros Hfl.
apply NAC. right; right; left. exists (blk_addr b), (blk_size b). split; [| clear - Hx Hfl; lia].
apply LIVE1. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; cbn [sb_blocks tl] in Hb |- *; right; exact Hb| right; exact Hb]. }
apply (sb_bufs_agree s S a j m6 m7) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG7 FR6 FRS6.
cps_release_done REL MU7 WM7 FLG7.
apply Hk. exists Σ3. split; [| cbn [dec_depth]; split; [congruence|]; split; [congruence|]; split; [congruence|]; split; [clear - EC CR1 DP0; cbn [dec_depth] in *; lia| congruence]].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m7.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM0]|].
split. { split; [assumption|]. split; [exact MI7|]. split; [cps_wmono| exact ST7]. }
split; [exact PF|].
cbn [speex_decoder_ctl fst snd] in *.
split; [| split; [exact ARG4| exact RV]].
cbn [decst_rep]. exists a, j, LBL. split; [reflexivity|]. split; [exact S8|]. split; [exact SPOS|]. split; [exact INV|]. split; [exact JOK|].
split; [rewrite sb_cells_split, <- EMP; apply (proj2 (rw_cells_app bsegs m7 S _ _)); split; [exact HD4| exact TL]|].
split; [exact BUFS|]. exists OUTL. exact RLOW. }
Qed.

Theorem ctl_gsr_live_all : forall d, ctl_gsr_live_at d.
Proof using AF SM0 AF_LIB.
destruct d as [st|s low]; [exact (ctl_gsr_live_nb st)| exact (ctl_gsr_live_sb s low)].
Qed.
End CtlGsrLive.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CtlGsrLive.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.

Definition ctl_gsr_live_at (d : dec_state bptr) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (OUT STEREO S : Z) (LBD : list block) (P lo pb nb : Z),
fdfs_only PMc -> mat_stable PMc ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 25 -> a2 = Z_to_bv 64 P -> tp = Z_to_bv 64 0x630458 ->
DREP OUT STEREO m S d LBD -> (dec_depth d <= 3)%nat -> List.NoDup (map blk_id LBD) ->
(exists w : word, rw_cells asegs m P [C4 w]) ->
(forall b, In b LBD -> In (blk_addr b, blk_size b) (rt_live RT Σ)) ->
In (pb, nb) (rt_live RT Σ) -> pb <= P -> P + 4 <= pb + nb -> P mod 4 = 0 -> ~ In pb (map blk_id LBD) ->
(length (rt_frames RT Σ) + dec_depth d <= FRAMES_MAX)%nat -> Z.of_nat (dec_depth d) <= rt_credit RT Σ + 1 ->
ART RT Σ m -> mem_inv asegs m -> frm0 fc ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + ctl_stack d <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 32 = 0 ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_speex_decoder_ctl m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists m',
ret_stL (fun _ fc' => frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) ((P, P + 4) :: blocks_ivs LBD) m m'
/\ DREP OUT STEREO m' S d LBD
/\ rw_cells asegs m' P [C4 (Z_to_bv 64 (fst (speex_decoder_ctl d CtlGetSamplingRate)))]
/\ - 2^31 <= fst (speex_decoder_ctl d CtlGetSamplingRate) < 2^31) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ - (Z.of_nat (dec_depth d) - 1) <= rt_credit RT Σ' <= rt_credit RT Σ
/\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem ctl_gsr_live_nb : forall st, ctl_gsr_live_at (DecNB st).
Proof using AF AF_LIB.
intros st Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
OUT STEREO S LBD P lo pb nb FDO MST -> -> -> -> REP DEP ND PRE LIVE INP FP1 FP2 PAL NINB FRM CRD ART0 MI0 FRM0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
cbn [ctl_stack] in LOR. unfold NBCTL_STACK in LOR.
pose proof REP as REP0. cbn [decst_rep] in REP0. destruct REP0 as [ELBD NB]. subst LBD.
pose proof (LIVE _ ltac:(left; reflexivity)) as INL. unfold blk_addr, blk_size in INL. cbn [fst snd] in INL. unfold NBSTATE_SIZEOF in INL.
destruct (live_below_lo RT AF Σ m S 2968 lo ART0 INL LOW) as (BD0 & BD1 & LOS).
destruct (af_acc_live RT AF Σ m S 2968 ART0 INL) as (_ & ACS).
pose proof (live_facts RT AF Σ m S 2968 ART0 INL) as (_ & _ & SIMG & SHI).
destruct (live_below_lo RT AF Σ m pb nb lo ART0 INP LOW) as (PB0 & PBL & _).
destruct (af_acc_live RT AF Σ m pb nb ART0 INP) as (_ & ACPB).
pose proof (live_facts RT AF Σ m pb nb ART0 INP) as (_ & _ & _ & PHI).
assert (NES : pb <> S) by (intros E; apply NINB; rewrite E; cbn [map blk_id blk_addr fst snd]; left; reflexivity).
pose proof (live_apart RT AF Σ m pb nb S 2968 ART0 INP INL NES) as PAP.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
pose proof (AF_LIB Σ m ART0) as LC0.
assert (OBM : aobj asegs m A_speex_nb_mode 96)
by (apply (aobj_lit RT AF Σ m A_speex_nb_mode 96 ART0); [unfold ACC_LITS, A_speex_nb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_speex_nb_mode; lia | unfold A_speex_nb_mode, APP_TOP; lia]).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(P, P + 4); (S, S + 2968)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
cps_norm.
refine (rz_evt RT AF Σ PMc _ _ T c MST Hc (rctl_nbA st OUT STEREO S _ CtlGetSamplingRate P lo usp ra gp (Z_to_bv 64 6489176) t0 t1 t2 s0 s1 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m eq_refl REP I PRE _ _ PAL OBM _ _ ST0 _ _ _ CC0 LC0 MI0 FRM0) _).
- intros b [<-|[]]. unfold ablk, blk_addr, blk_size. cbn [fst snd]. unfold NBSTATE_SIZEOF.
split; [split; [lia|]; split; [ulc| exact ACS]|]. split; [exact (proj1 NB)|]. split; [unfold SH_LO, SH_HI; lia|]. split; [unfold IMG_TOP; ulc| exact BD1].
- cbn [creq_size]. split; [lia|]. split; [ulc| apply (acc_sub asegs m pb nb P 4 ACPB); lia].
- cbn [creq_size]. left. lia.
- intros b [<-|[]]. unfold blk_addr, blk_size. cbn [fst snd creq_size]. unfold NBSTATE_SIZEOF. clear - PAP FP1 FP2. lia.
- exact LOS.
- unfold NBCTL_STACK. ulc.
- ulc.
- intros ms' c' POST Hc'. clear Hc.
destruct POST as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & F' & fc' & m' & -> & MU & WM & MI' & FRM' & ST' & REP' & CP' & _).
rewrite (ctlW_grp1 _ _ _ _ _ (eq_refl : creq_grp1 CtlGetSamplingRate = true)) in MU. cbn [blocks_ivs map blk_addr blk_size fst snd creq_size] in MU. unfold NBSTATE_SIZEOF in MU.
cps_seg_post.
apply Hk. exists Σ. split; [| cbn [dec_depth]; repeat split; lia].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m'.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM']|].
split. { split; [assumption|]. split; [exact MI'|]. split; [exact WM| exact ST']. }
split; [exact PF|]. split; [exact REP'|]. exact CP'.
Qed.

Theorem ctl_gsr_live_sb : forall s low, ctl_gsr_live_at (DecSB s low).
Proof using AF SM0 AF_LIB.
intros s low Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
OUT STEREO S LBD P lo pb nb FDO MST -> -> -> -> REP DEP ND PRE LIVE INP FP1 FP2 PAL NINB FRM CRD ART0 MI0 FRM0 ST0 LOW LOR SPT SPA.
set (r := CtlGetSamplingRate) in *. assert (GRP : creq_grp1 r = true) by reflexivity.
assert (PRE' : creq_pre STEREO m S (DecSB s low) P r) by exact PRE. clear PRE. rename PRE' into PRE.
change 4 with (creq_size r) in FP2.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
cbn [ctl_stack dec_depth] in LOR, DEP, FRM, CRD.
assert (CSP : 0 <= ctl_stack low) by (clear; induction low; cbn [ctl_stack]; unfold NBCTL_STACK; lia).
pose proof REP as REP0. cbn [decst_rep] in REP0. destruct REP0 as (a & j & LBL & ELBD & S8 & SPOS & INV & JOK & X & BUFS & OUTL & RLOW).
pose proof INV as (IMODE & _).
rewrite sb_cells_split in X.

assert (INL : In (S, 160) (rt_live RT Σ)).
{ specialize (LIVE (sbd_blk s, S, SBSTATE_SIZEOF)). rewrite ELBD in LIVE. specialize (LIVE ltac:(left; reflexivity)). exact LIVE. }
destruct (live_below_lo RT AF Σ m S 160 lo ART0 INL LOW) as (_ & BS1 & LOS).
destruct (af_acc_live RT AF Σ m S 160 ART0 INL) as (_ & ACS).
pose proof (live_facts RT AF Σ m S 160 ART0 INL) as (_ & _ & _ & SHI).

destruct (live_below_lo RT AF Σ m pb nb lo ART0 INP LOW) as (FP0 & BF1 & _).
pose proof (live_facts RT AF Σ m pb nb ART0 INP) as (_ & _ & _ & FPHI).
assert (NES : pb <> S) by (intros E; apply NINB; rewrite ELBD, E; cbn [sb_blocks app map blk_id blk_addr fst snd]; left; reflexivity).
pose proof (live_apart RT AF Σ m pb nb S 160 ART0 INP INL NES) as FLA1.
assert (SZ : 0 <= creq_size r <= 24) by (destruct r; cbn; lia).

pose proof (AF_LIB Σ m ART0) as LC0.
set (MP := sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode (sbd_mode s)) in *.
assert (MPF : exists c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11, ro_cells asegs m MP (sb_desc_cells c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11)
/\ aobj asegs m MP 96 /\ MP mod 8 = 0 /\ 0x10000 <= MP /\ MP + 104 <= 0x652000).
{ subst MP. destruct IMODE as [E|E]; rewrite E; cbn [sb_mode_ptr].
- do 12 eexists. split; [exact (lib_const m A_speex_wb_mode LC_speex_wb_mode LC0 ltac:(lc_in))|].
split; [apply (aobj_lit RT AF Σ m A_speex_wb_mode 96 ART0); [unfold ACC_LITS, A_speex_wb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_speex_wb_mode; lia | unfold A_speex_wb_mode, APP_TOP; lia]|].
unfold A_speex_wb_mode. repeat split; lia.
- do 12 eexists. split; [exact (lib_const m A_speex_uwb_mode LC_speex_uwb_mode LC0 ltac:(lc_in))|].
split; [apply (aobj_lit RT AF Σ m A_speex_uwb_mode 96 ART0); [unfold ACC_LITS, A_speex_uwb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_speex_uwb_mode; lia | unfold A_speex_uwb_mode, APP_TOP; lia]|].
unfold A_speex_uwb_mode. repeat split; lia. }
destruct MPF as (c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & c8 & c9 & c10 & c11 & ND0 & OBM & MP8 & MPLO & MPHI).
pose proof (eq_refl : MP = sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode (sbd_mode s)) as EMP. clearbody MP.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
assert (OBS : aobj asegs m S 160) by (split; [lia|]; split; [unfold APP_TOP, STACK_WIN, USTACK_TOP, RT_STACK in *; lia| exact ACS]).
assert (EW : creq_ivs P r = [(P, P + creq_size r)]) by (destruct r; try discriminate GRP; reflexivity).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp (blocks_ivs LBD) m) as PF.
pose proof (fun E : rt_frames RT Σ = [] => af_pois_nil RT AF Σ m ART0 E) as PNIL.
assert (LIVE0 : blocks_in_live RT Σ LBD) by exact LIVE.
assert (POUT : forall x, P <= x < P + creq_size r -> outside (blocks_ivs LBD) x).
{ intros x Hx. apply outside_blocks_ivs. intros b Hb Hin.
assert (NEB : pb <> blk_addr b) by (intros E; apply NINB; rewrite E; exact (in_map blk_id _ _ Hb)).
pose proof (live_apart RT AF Σ m pb nb _ _ ART0 INP (LIVE b Hb) NEB) as B2. clear - B2 Hx Hin FP1 FP2. lia. }

assert (OFFW : forall x, SH_LO <= x < SH_HI -> outside ((P, P + creq_size r) :: blocks_ivs LBD) x).
{ intros x Hx. split; [clear - Hx FPHI FP2 FP1; unfold SH_LO, SH_HI in Hx; cbn [fst snd]; lia| exact (outside_blocks_shadow RT AF Σ m LBD x ART0 LIVE0 Hx)]. }
assert (PR0 : 0 <= P) by lia.
assert (PR1 : P + creq_size r <= 2^64) by (clear - FP2 BF1 LOR SPT CSP; unfold RT_STACK, USTACK_TOP in *; lia).
assert (PCL : forall x, P <= x < P + creq_size r -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x)
by (intros x Hx; right; right; left; exists pb, nb; split; [exact INP| lia]).
pose proof (fun m' S' d' (PR : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp (blocks_ivs LBD) m m') (WM : wmono asegs m m') =>
creq_pre_agree STEREO m m' S S' (DecSB s low) d' P r GRP PRE
(agree_at_of_pres_fp _ _ usp _ m m' P (creq_size r) PR WM PR0 PR1 (fun x Hx => conj (PCL x Hx) (POUT x Hx)))) as PREK.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
assert (CODE : sbctl_code_ok (ctl_req_code r)) by (unfold sbctl_code_ok; destruct r; cbn [ctl_req_code]; tauto).
assert (CRNG : 0 <= ctl_req_code r < 2^31) by (destruct r; cbn; lia).
assert (LO96 : lo <= usp + -96) by (clear - LOR CSP; unfold RT_STACK in LOR; lia).
cps_norm. cps_hide.

piece X HD. rename X into TL. unfold sbhd in HD. unfold sbtl in TL.
Time cps_seg (sbctl_w1 usp lo S MP P (ctl_req_code r)). { reflexivity. } { ulc. } { ulc. }
destruct POST as (m1 & j8 & xt1 & xa3 & xa4 & xa5 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
assert (BOUT : forall b x, In b (tl (sb_blocks s S a) ++ LBL) -> blk_addr b <= x < blk_addr b + blk_size b ->
x < lo /\ (x < S \/ S + 160 <= x) /\ (x < pb \/ pb + nb <= x)).
{ intros b x Hb Hx.
assert (Hb' : In b LBD) by (rewrite ELBD; cbn [sb_blocks tl app] in Hb |- *; right; exact Hb).
pose proof (LIVE b Hb') as LB.
destruct (live_below_lo RT AF Σ m _ _ lo ART0 LB LOW) as (_ & B1 & _).
assert (NEB : pb <> blk_addr b) by (intros E; apply NINB; rewrite E; exact (in_map blk_id _ _ Hb')).
pose proof (live_apart RT AF Σ m pb nb _ _ ART0 INP LB NEB) as B2.
assert (NE : blk_addr b <> S).
{ rewrite ELBD in ND. cbn [sb_blocks app map blk_id blk_addr fst snd] in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI _].
intros E. apply NI. rewrite <- E. cbn [sb_blocks tl app] in Hb. exact (in_map blk_id _ _ Hb). }
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 LB INL NE) as B3. clear - B1 B2 B3 Hx. lia. }
pose proof (agree_blocks_of_munch asegs _ m m1 (tl (sb_blocks s S a) ++ LBL) MU1 WM1
ltac:(intros b x Hb Hx; pose proof (BOUT b x Hb Hx) as H1; clear - H1 LO96; cbn [outside]; split; [lia| exact I])) as AG1.
Time cps_seg_post.
apply (sb_bufs_agree s S a j m m1) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG1| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG1| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG1.

cps_rt_sized SM0 0. { cbn; tauto. } { pose proof (dec_depth_pos low) as DP; clear - CRD DP; lia. } { cps_callok. }
intros cc2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR1 & FPOS & F64 & FTOP & PO1).
Time cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRF & WRS).
assert (LIVE1 : blocks_in_live RT Σ1 LBD) by (intros b Hb; rewrite LV1; exact (LIVE b Hb)).
pose proof (agree_blocks_of_pres RT Σ (rt_frames RT Σ) (usp + -96) m1 m2 (tl (sb_blocks s S a) ++ LBL) PRES2 WM2
ltac:(intros b Hb; apply LIVE; rewrite ELBD; cbn [sb_blocks tl app] in Hb |- *; right; exact Hb)) as AG2.
apply (sb_bufs_agree s S a j m1 m2) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG2| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG2| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG2.
Time cps_new_frame ART2 FRS1 LV1 SP1 WRF WRS sf. cps_hide.
assert (BOUT2 : forall b x, In b (tl (sb_blocks s S a) ++ LBL) -> blk_addr b <= x < blk_addr b + blk_size b ->
(x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)).
{ intros b x Hb Hx.
assert (Hb' : In b LBD) by (rewrite ELBD; cbn [sb_blocks tl app] in Hb |- *; right; exact Hb).
destruct (frame_live_apart RT AF Σ1 m2 f 0%nat _ _ ART2 INF (LIVE1 b Hb')) as (B2 & B3).
change (fs_size 0) with 64 in B2, B3. rewrite SHF0, <- SHF in B3. clear - B2 B3 Hx. lia. }

cps_seg (sbctl_w2 usp lo S P (ctl_req_code r) f sf).
destruct POST as (m3 & a0' & a1' & a2' & j24 & l32 & j36 & j40 & l48 & j52 & -> & MU3 & WM3 & MI3 & ST3 & FR3 & FRB3 & FRS3).
Time pose proof (agree_blocks_of_munch asegs _ m2 m3 (tl (sb_blocks s S a) ++ LBL) MU3 WM3
ltac:(intros b x Hb Hx; pose proof (BOUT b x Hb Hx) as H1; pose proof (BOUT2 b x Hb Hx) as H2; clear - H1 H2 LO96; cbn [outside]; repeat split; lia)) as AG3.
apply (sb_bufs_agree s S a j m2 m3) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG3| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG3| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG3 FR1 FRB FRS.
unfold sbctl_frame in FR3. unfold sbctl_fhdr in FRB3. unfold sbctl_shadow, bF1, bF3, bF8 in FRS3.
Time cps_seg_post.
destruct (af_acc_live RT AF Σ1 m3 S 160 ART INL) as (_ & ACS3).
assert (OBS3 : aobj asegs m3 S 160) by (split; [lia|]; split; [ulc| exact ACS3]).
assert (SOFF : S + 160 <= SH_LO \/ SH_HI <= S) by (clear - SHI; unfold hid, SH_LO, SH_HI in *; lia).
assert (HD3 : rw_cells asegs m3 S (sbhd MP (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s))
(Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s))
(Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 (sbd_lpc_enh_enabled s)))) by exact HD.
assert (SBF : 0 < S /\ S + 160 < 2^63) by (split; ulc).
assert (PBF : 0 <= P /\ P + 24 < 2^63) by (split; ulc).
clear HD. cps_hide.

assert (WM03 : wmono asegs m m3) by cps_wmono.
pose proof (PREK m3 (a_low a) low PF WM03) as PREL3. pose proof (PREK m3 S (DecSB s low) PF WM03) as PRE3. clear PREK PRE.
apply (pres_fp_weaken _ _ _ _ ((P, P + creq_size r) :: blocks_ivs LBD)) in PF; [| intros x Hx; exact (proj2 Hx)].
lazymatch goal with A : X0ec.ART RT Σ1 m3 |- _ => destruct (af_acc_live RT AF Σ1 m3 pb nb A INP) as (_ & ACPB3) end.
assert (ACP3 : acc asegs m3 P (creq_size r)) by (apply (acc_sub asegs m3 pb nb P _ ACPB3); lia).
assert (OUTB : forall x, (lo <= x \/ (S <= x < S + 160) \/ (pb <= x < pb + nb) \/ (f <= x < f + 64) \/ (sf <= x < sf + 8)) -> outside (blocks_ivs LBL) x).
{ intros x Hx. apply outside_blocks_ivs. intros b Hb Hin.
pose proof (BOUT b x ltac:(apply in_app_iff; right; exact Hb) Hin) as H1. pose proof (BOUT2 b x ltac:(apply in_app_iff; right; exact Hb) Hin) as H2.
clear - Hx H1 H2. lia. }
assert (APL : forall b x, In b (tl (sb_blocks s S a)) -> blk_addr b <= x < blk_addr b + blk_size b -> outside (blocks_ivs LBL) x).
{ intros b x Hb Hx. apply outside_blocks_ivs. intros b2 Hb2 Hin.
assert (NE : blk_addr b <> blk_addr b2).
{ rewrite ELBD, map_app in ND. apply (NoDup_app_in_neq _ _ (blk_id b) (blk_id b2) ND); [apply in_map; cbn [sb_blocks tl] in Hb |- *; right; exact Hb| apply in_map; exact Hb2]. }
pose proof (live_apart RT AF Σ1 m3 _ _ _ _ ART (LIVE1 b ltac:(rewrite ELBD; apply in_app_iff; left; cbn [sb_blocks tl] in Hb |- *; right; exact Hb))
(LIVE1 b2 ltac:(rewrite ELBD; apply in_app_iff; right; exact Hb2)) NE) as AP.
clear - AP Hx Hin. lia. }
assert (PFA : P + creq_size r <= f \/ f + 64 <= P).
{ assert (SZ1 : 1 <= creq_size r) by (clear - GRP; destruct r; try discriminate GRP; cbn; lia).
assert (I1 : P <= P < P + creq_size r) by (clear - SZ1; lia).
assert (I2 : P <= P + creq_size r - 1 < P + creq_size r) by (clear - SZ1; lia).
pose proof (NAF P (PCL P I1)) as (N1 & _).
pose proof (NAF (P + creq_size r - 1) (PCL _ I2)) as (N2 & _).
change (fs_size 0) with 64 in N1, N2. clear - N1 N2 SZ SZ1. lia. }
assert (NDL : List.NoDup (map blk_id LBL)) by (rewrite ELBD, map_app in ND; exact (List.NoDup_app_remove_l _ _ ND)).
assert (LIVEL : forall b, In b LBL -> In (blk_addr b, blk_size b) (rt_live RT Σ1)) by (intros b Hb; apply LIVE1; rewrite ELBD; apply in_app_iff; right; exact Hb).
assert (FRM1 : (length (rt_frames RT Σ1) + dec_depth low <= FRAMES_MAX)%nat) by (rewrite FRS1; cbn [length]; clear - FRM; lia).
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -96)) = usp + -96) by (apply unsigned_lit; ulc).
assert (SPA96 : (usp + -96) mod 32 = 0) by (clear - SPA; Z.div_mod_to_equations; lia).
subst LBD. cbn [sb_blocks app blocks_ivs map blk_addr blk_size fst snd] in PF. unfold SBSTATE_SIZEOF in PF.
subst r. cbn [ctl_req_code creq_size creq_align] in *.
{
destruct PRE3 as (w3 & ARG3).
assert (OBP3 : aobj asegs m3 P 4) by (split; [lia|]; split; [ulc| exact ACP3]).
assert (APS : P + 4 <= S \/ S + 160 <= P) by (clear - FLA1 FP1 FP2; unfold hid in FLA1; lia).
assert (RV : - 2^31 <= sbd_sampling_rate s < 2^31) by (clear - INV; unfold sb_inv in INV; tauto).
assert (DP0 : (1 <= dec_depth low)%nat) by apply dec_depth_pos.
cps_seg (sbarm_gsr usp S P f sf).
destruct POST as (m4 & yb1 & yb2 & -> & HD4 & ARG4 & MU4 & WM4 & MI4).
pose proof (agree_blocks_of_munch asegs _ m3 m4 (tl (sb_blocks s S a) ++ LBL) MU4 WM4
ltac:(intros b x Hb Hx; pose proof (BOUT b x Hb Hx) as H1; clear - H1 FP1 FP2; cbn [outside]; split; [lia| exact I])) as AG4.
apply (sb_bufs_agree s S a j m3 m4) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG4| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG4| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG4 HD3 ARG3 OBP3 APS. unfold sbhd in HD4.
cps_seg_post.

assert (FRSE : rw_cells asegs m4 sf (sbctl_shadow bF8 bF8)) by exact FRS3. clear FRS3.
chunk_uncons FRB3 as HDF.
cps_seg (sbctl_epi_a usp f sf).
destruct POST as (m6 & -> & MU6 & WM6 & MI6 & FRS6).
pose proof (agree_blocks_of_munch asegs _ m4 m6 (tl (sb_blocks s S a) ++ LBL) MU6 WM6
ltac:(intros b x Hb Hx; pose proof (BOUT2 b x Hb Hx) as H2; clear - H2; cbn [outside]; repeat split; lia)) as AG6.
apply (sb_bufs_agree s S a j m4 m6) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG6 HDF FRSE FRB3 . unfold sbctl_shadow_dead, bF5 in FRS6. cbn [map repeat] in FRS6.
cps_seg_post.

assert (EF2 : rt_frames RT Σ1 = (f, 0%nat) :: rt_frames RT Σ) by (exact FRS1).
assert (EL2 : rt_live RT Σ1 = rt_live RT Σ) by (exact LV1).
lazymatch goal with A : X0ec.ART RT Σ1 _ |- _ => rename A into ARTX end.
cps_release_intro ARTX EF2 EL2 (fun E : rt_frames RT Σ = [] => eq_trans PO1 (PNIL E)) Σ3 fl.
assert (FLS : fl < S \/ S + 160 <= fl).
{ destruct (Z_lt_dec fl S) as [L|L]; [left; exact L|]. destruct (Z_le_dec (S + 160) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; left. exists S, 160. split; [exact INL| clear - L G; lia]. }
assert (FLP : fl < pb \/ pb + nb <= fl).
{ destruct (Z_lt_dec fl pb) as [L|L]; [left; exact L|]. destruct (Z_le_dec (pb + nb) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; left. exists pb, nb. split; [exact INP| clear - L G; lia]. }
assert (FR6 : rw_cells asegs m6 (usp + -96) (sbctl_frame (C8 (Z_to_bv 64 f)) s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) by exact FR3. clear FR3.
cps_seg (sbctl_epi_b usp lo f fl).
destruct POST as (m7 & -> & MU7 & WM7 & MI7 & ST7 & FLG7).
assert (AG7 : agree_blocks asegs m6 m7 (tl (sb_blocks s S a) ++ LBL)).
{ apply (agree_blocks_of_munch asegs _ m6 m7 _ MU7 WM7). intros b x Hb Hx. cbn [outside]. split; [| exact I]. intros Hfl.
apply NAC. right; right; left. exists (blk_addr b), (blk_size b). split; [| clear - Hx Hfl; lia].
apply LIVE1. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; cbn [sb_blocks tl] in Hb |- *; right; exact Hb| right; exact Hb]. }
apply (sb_bufs_agree s S a j m6 m7) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG7 FR6 FRS6.
cps_release_done REL MU7 WM7 FLG7.
apply Hk. exists Σ3. split; [| cbn [dec_depth]; split; [congruence|]; split; [congruence|]; split; [congruence|]; split; [clear - EC CR1 DP0; cbn [dec_depth] in *; lia| congruence]].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m7.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM0]|].
split. { split; [assumption|]. split; [exact MI7|]. split; [cps_wmono| exact ST7]. }
split; [exact PF|].
cbn [speex_decoder_ctl fst snd] in *.
split; [| split; [exact ARG4| exact RV]].
cbn [decst_rep]. exists a, j, LBL. split; [reflexivity|]. split; [exact S8|]. split; [exact SPOS|]. split; [exact INV|]. split; [exact JOK|].
split; [rewrite sb_cells_split, <- EMP; apply (proj2 (rw_cells_app asegs m7 S _ _)); split; [exact HD4| exact TL]|].
split; [exact BUFS|]. exists OUTL. exact RLOW. }
Qed.

Theorem ctl_gsr_live_all : forall d, ctl_gsr_live_at d.
Proof using AF SM0 AF_LIB.
destruct d as [st|s low]; [exact (ctl_gsr_live_nb st)| exact (ctl_gsr_live_sb s low)].
Qed.
End CtlGsrLive.
