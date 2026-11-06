(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1nt X1rg X1rh X1re X1od X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X000 X04b X00c X07z X05o X05p X05s
X071 X06v X06y X06u X073.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X12c X14x X0r0 X0ra X0qz X0v9 X0rb X0wl X0xn X0xq X0xm X0xu.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xu.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).
Local Notation Z64 := (Z_to_bv 64).

Section Exit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Variable LIB : mem -> Prop.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis SS8 : set_shadow_contract RT 0xf8.
Hypothesis SF8 : stack_free_contract RT 8.
Variable X : hinv.
Variable F0 : list (word * FdEntry).
Variable fs0 : Fs.Fs.

Definition hep_ok : Prop :=
x_usp X mod 16 = 0 /\ 368 <= x_usp X /\ x_usp X + 16 <= USTACK_TOP
/\ x_S1 X mod 32 = 0 /\ x_usp X - 368 <= x_S1 X <= x_usp X - 352
/\ x_sp0 X - STACK_WIN <= x_lo X /\ x_lo X + RT_STACK <= x_S1 X /\ SH_HI <= x_lo X
/\ 0 < x_F X /\ x_F X mod 64 = 0 /\ x_F X + fs_size 8 <= x_lo X /\ (x_F X + fs_size 8 <= SH_LO \/ SH_HI <= x_F X).

Theorem h_ep_ok : forall (Σ : rts RT) (fc0 : bv 32),
hep_ok -> rt_live RT Σ = x_live X -> rt_frames RT Σ = [] -> rt_sp0 RT Σ = x_sp0 X -> rt_credit RT Σ = x_cr0 X -> LIB (x_m0 X) ->
cps bsegs (at_EP RT OUT_rep ERR_rep IO_FP X F0 fs0) (h_final RT OUT_rep ERR_rep IO_FP X F0 fs0 Σ LIB fc0).
Proof using AF ERR_loc OUT_loc IO_img LIB_loc SS8 SF8.
intros Σ fc0 HE LV0 FR0 SP0 CR0 LIB0 T c Hc Hk.
destruct Hc as (Σ1 & Fx & fc & m & ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6
& w0 & w8 & w16 & w24 & w32 & w40 & w48 & w56 & w64 & w72 & w80 & w88 & w96 & w104 & w112 & w120 & w128 & w136 & w144 & w152 & w160 & w168 & w176 & w184 & w192 & w200 & w208 & w216 & w224 & w232 & w240 & h0
& c0 & c1 & jg & Hc & FRMF & LV1 & FR1 & SP1 & PO1 & CR1 & ART0 & MI0 & ST0 & SHT & SHM & HD & SPL & GAP & SV & PF & NAF & ERR0 & OUT0).
destruct HE as (U16 & U336 & UT & S32 & SR & LOW & LOR & SHL & F0p & F64 & FLO & FSH).
set (usp := x_usp X) in *. set (S1 := x_S1 X) in *. set (lo := x_lo X) in *. set (F := x_F X) in *.
assert (Esf : x_sf X = Z.shiftr F 3 + SHB) by reflexivity. set (sf := x_sf X) in *.
pose proof (PMfd_mat_stable F0 fs0) as MST. pose proof (PMfd_fdfs_only F0 fs0) as FDO.
change (fs_size 8) with 16384 in *.
assert (INF : In (F, 8%nat) (rt_frames RT Σ1)) by (rewrite FR1; left; reflexivity).
assert (F8 : F mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
assert (SHR : SH_LO <= sf /\ sf + 2048 <= SH_HI).
{ rewrite Esf. rewrite shad_shiftr. destruct (shad_range_al F 16384 ltac:(lia) F8 ltac:(reflexivity) ltac:(lia) ltac:(clear - FLO LOR SR UT; unfold RT_STACK, APP_TOP, USTACK_TOP in *; lia)) as (A1 & A2).
split; [exact A1|]. change (16384 / 8) with 2048 in A2. exact A2. }

destruct SHR as (SH1 & SH2).
pose proof (frame_facts RT AF Σ1 m F 8%nat ART0 INF) as (FF1 & FF64 & FIMG & FSP0 & FHI & FSH0 & FSH1 & FSH2 & FSH3 & FSELF).
change (fs_size 8) with 16384 in *. change (16384 / 8) with 2048 in *.
assert (ESH : shad F = sf) by (rewrite <- FSH0; reflexivity). rewrite ESH in *. clear FSH0.
assert (FSA : F + 16384 <= sf \/ sf + 2048 <= F) by exact FSELF.
assert (SFS : sf + 2048 <= S1) by (clear - SH2 SHL LOR; unfold SH_HI, RT_STACK in *; lia).
assert (FS1 : F + 16384 <= S1) by (clear - FLO LOR; unfold RT_STACK in *; lia).
assert (LOS : lo <= S1) by (clear - LOR; unfold RT_STACK in *; lia).
assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
cps_norm. cps_hide.

Time cps_seg (hx_r sf).
destruct POST as (m1 & -> & MU1 & WM1 & MI1 & SHT1).
clear SHT.
Time cps_seg_post.
apply (fp_local_munch IO_FP ERR_rep _ m m1 ERR_loc IO_img MU1) in ERR0; [| intros x Hx; cbn [outside]; split; [| exact I]; clear - Hx SH1; unfold SH_LO, SEGTOP_A in *; lia].
assert (OUT1 : forall so, OUT_rep so (x_m0 X) -> OUT_rep so m1).
{ intros so Hso. apply (fp_local_munch IO_FP (OUT_rep so) _ m m1 (OUT_loc so) IO_img MU1); [intros x Hx; cbn [outside]; split; [| exact I]; clear - Hx SH1; unfold SH_LO, SEGTOP_A in *; lia| exact (OUT0 so Hso)]. }
clear OUT0 MU1 WM1.

Time cps_seg (hx_1 sf).
destruct POST as (m2 & -> & MU2 & WM2 & MI2).
Time cps_seg_post.
apply (fp_local_munch IO_FP ERR_rep _ m1 m2 ERR_loc IO_img MU2) in ERR0; [| intros x Hx; exact I].
assert (OUT2 : forall so, OUT_rep so (x_m0 X) -> OUT_rep so m2).
{ intros so Hso. apply (fp_local_munch IO_FP (OUT_rep so) _ m1 m2 (OUT_loc so) IO_img MU2); [intros x Hx; exact I| exact (OUT1 so Hso)]. }
clear OUT1 MU2 WM2.
Time cps_rt (SS8 Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 (sf + 16) 1000 lo).
{ cbn. tauto. }
{ intros i Hi. exists F, 8%nat. split; [exact INF|]. rewrite ESH. change (fs_size 8) with 16384. rewrite FSH1. lia. }
{ exact (proj2 SHM). }
{ cps_callok. }
intros cc3 (v0 & Hc3).
Time cps_unpack Hc3 as (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & BY3).
assert (ERR3 : ERR_rep m3).
{ apply (ERR_loc m2 m3 ERR0). intros a Ha. apply PRES3; [right; left; exact (IO_img _ Ha)|].
pose proof (client_static_range _ (IO_img _ Ha)) as R. intros Hin. clear - R Hin SH1. unfold SH_LO, SEGTOP_A in *. lia. }
assert (OUT3 : forall so, OUT_rep so (x_m0 X) -> OUT_rep so m3).
{ intros so Hso. apply (OUT_loc so m2 m3 (OUT2 so Hso)). intros a Ha. apply PRES3; [right; left; exact (IO_img _ Ha)|].
pose proof (client_static_range _ (IO_img _ Ha)) as R. intros Hin. clear - R Hin SH1. unfold SH_LO, SEGTOP_A in *. lia. }
clear ERR0 OUT2 PRES3 BY3.

Time cps_seg (hx_2 F).
{ clear - FF1 FS1 SR UT; unfold USTACK_TOP in *; lia. }
destruct POST as (m4 & -> & MU4 & WM4 & MI4 & HD4).
clear HD.
Time cps_seg_post.
apply (fp_local_munch IO_FP ERR_rep _ m3 m4 ERR_loc IO_img MU4) in ERR3; [| intros x Hx; cbn [outside]; split; [| exact I]; clear - Hx FIMG; unfold SEGTOP_A in *; lia].
assert (OUT4 : forall so, OUT_rep so (x_m0 X) -> OUT_rep so m4).
{ intros so Hso. apply (fp_local_munch IO_FP (OUT_rep so) _ m3 m4 (OUT_loc so) IO_img MU4); [intros x Hx; cbn [outside]; split; [| exact I]; clear - Hx FIMG; unfold SEGTOP_A in *; lia| exact (OUT3 so Hso)]. }
clear OUT3 MU4 WM4.
Time cps_rt (SF8 Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 F [] lo 9280).
{ intros _. unfold HF_SIZE. split; [reflexivity|]. split; [reflexivity| change (fs_size 8) with 16384; lia]. }
{ intros _. exact PO1. }
{ cps_callok. }
intros cc5 (Σ2 & v5 & Hc5 & FRS2 & LV2 & SPS2 & CR2 & PO2).
Time cps_unpack Hc5 as (m5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5).
pose proof (fp_local_pres IO_FP ERR_rep _ _ _ m4 m5 ERR_loc IO_img PRES5 ERR3) as ERR5.
assert (OUT5 : forall so, OUT_rep so (x_m0 X) -> OUT_rep so m5) by (intros so Hso; exact (fp_local_pres IO_FP (OUT_rep so) _ _ _ m4 m5 (OUT_loc so) IO_img PRES5 (OUT4 so Hso))).
clear ERR3 OUT4 PRES5.
assert (LOW2 : rt_sp0 RT Σ2 - 8388608 <= lo) by (rewrite SPS2; exact LOW1).

Time cps_seg (hx_3 usp S1 lo).
destruct POST as (m6 & -> & MU6 & WM6 & MI6 & ST6).
clear SPL GAP SV ST5.
Time cps_seg_post.
apply (fp_local_munch IO_FP ERR_rep _ m5 m6 ERR_loc IO_img MU6) in ERR5; [| intros x Hx; exact I].
assert (OUT6 : forall so, OUT_rep so (x_m0 X) -> OUT_rep so m6).
{ intros so Hso. apply (fp_local_munch IO_FP (OUT_rep so) _ m5 m6 (OUT_loc so) IO_img MU6); [intros x Hx; exact I| exact (OUT5 so Hso)]. }
apply Hk. exists Σ2.
split; [| split; [congruence|]; split; [exact FRS2|]; split; [congruence|]; rewrite CR2, CR0; exact CR1].
eapply ASTA_conseq; [exact Hc2|]. intros ms <-. exists m6.
split; [unfold ret_stR; do 16 eexists; split; [reflexivity| intros _; exact FRMF]|].
split; [split; [exact ART| split; [exact MI6| exact ST6]]|].
split; [rewrite LV0, FR0; unfold LIB_FP; cbn [app]; exact PF|].
split; [exact (LIB_loc (x_m0 X) m6 LIB0 ltac:(intros a Ha; destruct Ha as (x & y & Hin & _); destruct Hin))|].
split; [exact ERR5| exact OUT6].
Qed.
End Exit.

Section ExitXT.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Variable LIB : mem -> Prop.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis SS8 : set_shadow_contract RT 0xf8.
Hypothesis SF8 : stack_free_contract RT 8.
Variable X : hinv.
Variable F0 : list (word * FdEntry).
Variable fs0 : Fs.Fs.

Theorem h_xt_ok : forall (Σ : rts RT) (fc0 : bv 32),
hinv_ok OUT_rep IO_FP X -> rt_live RT Σ = x_live X -> rt_frames RT Σ = [] -> rt_sp0 RT Σ = x_sp0 X -> rt_credit RT Σ = x_cr0 X -> LIB (x_m0 X) ->
cps bsegs (at_XT RT OUT_rep ERR_rep IO_FP X F0 fs0) (h_final RT OUT_rep ERR_rep IO_FP X F0 fs0 Σ LIB fc0).
Proof using AF ERR_loc OUT_loc IO_img LIB_loc SS8 SF8.
intros Σ fc0 HX LV0 FR0 SP0 CR0 LIB0 T c Hc Hk.
destruct Hc as (Σ1 & Fx & fc & m & ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s4 & s5 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6
& w24 & w32 & w40 & w48 & w56 & w64 & w72 & w80 & w88 & w96 & w104 & w112 & w120 & w128 & w136 & w144 & w152 & w160 & w168 & w176 & w184 & w192 & w200
& w208 & w216 & w224 & w232
& Hc & FRM & LV1 & FR1 & SP1 & PO1 & CR1 & ART1 & MI1 & ST1 & PF & ERR1 & OUT1 & SPC & SHL).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).

pose proof (h_shr_at OUT_rep IO_FP IO_img X HX m PF) as SHR.
pose proof (h_saves_at OUT_rep IO_FP IO_img X HX m PF) as SV.
destruct (h_gap_at OUT_rep IO_FP IO_img X HX m PF) as (jg & GAP).
pose proof (h_hdr_at OUT_rep IO_FP IO_img X HX m PF) as HDR.
pose proof (h_pf_entry OUT_rep IO_FP IO_img X HX m PF) as PFE.
pose proof (hi_naf _ _ _ HX) as NAF. pose proof (hi_out _ _ _ HX) as OUT0.
clear PF.

refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply hx_0; [reflexivity| exact SPC| exact MI1| unfold USTACK_TOP in *; lia]. }
intros ms' c' (m1 & -> & MU0 & WM0 & MI0 & SPC0) Hc'.
assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= x_lo X) by (rewrite SP1; exact LW).
assert (INF : In (x_F X, 8%nat) (rt_frames RT Σ1)) by (rewrite FR1; left; reflexivity).
cps_norm. cps_hide.
Time cps_seg_post.
apply (fp_local_munch IO_FP ERR_rep _ m m1 ERR_loc IO_img MU0) in ERR1; [| intros x Hx; exact I].
assert (OUTE : forall so, OUT_rep so (x_m0 X) -> OUT_rep so m1).
{ intros so Hso. apply (fp_local_munch IO_FP (OUT_rep so) _ m m1 (OUT_loc so) IO_img MU0); [intros x Hx; exact I| exact (OUT1 so (OUT0 so Hso))]. }
cb_cut SHR 1000%nat SHM. chunk_uncons HDR as HDR0.
refine (h_ep_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img LIB LIB_loc SS8 SF8 X F0 fs0 Σ fc0 _ LV0 FR0 SP0 CR0 LIB0 T c' _ Hk).
{ pose proof (hi_F _ _ _ HX) as (_ & _ & _ & FH & _). unfold hep_ok. change (fs_size 8) with 16384 in *. unfold H_STACK in *. cps_unf.
split; [exact U16|]. split; [exact U336|]. split; [exact UT|]. split; [exact S32|]. split; [exact SR|]. split; [exact LW|].
split; [lia|]. split; [exact SHLO|]. split; [exact FP0|]. split; [exact F64|]. split; [exact FL| exact FH]. }

unfold at_EP.
exists Σ1, Fx, fc, m1, ra, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, s2, s8, s9, s10, s11, t3, t4, t5, t6.
exists (Z_to_bv 64 (x_sf X + 16)), (Z_to_bv 64 (x_F X)), (Z_to_bv 64 (x_F X)), w24, w32, w40, w48, w56, w64, w72, w80, w88, w96,
w104, w112, w120, w128, w136, w144, w152, w160, w168, w176, w184, w192, w200, w208, w216, w224, w232, (Z_to_bv 64 (x_F X)), (Z_to_bv 64 0x41b58ab3).
do 3 eexists.
split; [exact Hc'|]. split; [exact FRM|]. split; [exact LV1|]. split; [exact FR1|]. split; [exact SP1|]. split; [exact PO1|]. split; [lia|].
split; [exact ART|]. split; [exact MI0|]. split; [eassumption|].
split; [exact SHR|]. split; [exact SHM|]. split; [exact HDR0|].
split; [exact SPC0|]. split; [exact GAP|]. split; [exact SV|]. split; [exact PFE|]. split; [exact NAF|]. split; [exact ERR1| exact OUTE].
Qed.
End ExitXT.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).
Local Notation Z64 := (Z_to_bv 64).

Section Exit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Variable LIB : mem -> Prop.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis SS8 : set_shadow_contract RT 0xf8.
Hypothesis SF8 : stack_free_contract RT 8.
Variable X : hinv.
Variable F0 : list (word * FdEntry).
Variable fs0 : Fs.Fs.

Definition hep_ok : Prop :=
x_usp X mod 16 = 0 /\ 336 <= x_usp X /\ x_usp X + 16 <= USTACK_TOP
/\ x_S1 X mod 32 = 0 /\ x_usp X - 336 <= x_S1 X <= x_usp X - 320
/\ x_sp0 X - STACK_WIN <= x_lo X /\ x_lo X + RT_STACK <= x_S1 X /\ SH_HI <= x_lo X
/\ 0 < x_F X /\ x_F X mod 64 = 0 /\ x_F X + fs_size 8 <= x_lo X /\ (x_F X + fs_size 8 <= SH_LO \/ SH_HI <= x_F X).

Theorem h_ep_ok : forall (Σ : rts RT) (fc0 : bv 32),
hep_ok -> rt_live RT Σ = x_live X -> rt_frames RT Σ = [] -> rt_sp0 RT Σ = x_sp0 X -> rt_credit RT Σ = x_cr0 X -> LIB (x_m0 X) ->
cps asegs (at_EP RT OUT_rep ERR_rep IO_FP X F0 fs0) (h_final RT OUT_rep ERR_rep IO_FP X F0 fs0 Σ LIB fc0).
Proof using AF ERR_loc OUT_loc IO_img LIB_loc SS8 SF8.
intros Σ fc0 HE LV0 FR0 SP0 CR0 LIB0 T c Hc Hk.
destruct Hc as (Σ1 & Fx & fc & m & ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6
& w0 & w8 & w16 & w24 & w32 & w40 & w48 & w56 & w64 & w72 & w80 & w88 & w96 & w104 & w112 & w120 & w128 & w136 & w144 & w152 & w160 & w168 & w176 & w184 & w192 & w200 & w208 & h0
& c0 & c1 & jg & Hc & FRMF & LV1 & FR1 & SP1 & PO1 & CR1 & ART0 & MI0 & ST0 & SHT & SHM & HD & SPL & GAP & SV & PF & NAF & ERR0 & OUT0).
destruct HE as (U16 & U336 & UT & S32 & SR & LOW & LOR & SHL & F0p & F64 & FLO & FSH).
set (usp := x_usp X) in *. set (S1 := x_S1 X) in *. set (lo := x_lo X) in *. set (F := x_F X) in *.
assert (Esf : x_sf X = Z.shiftr F 3 + SHB) by reflexivity. set (sf := x_sf X) in *.
pose proof (PMfd_mat_stable F0 fs0) as MST. pose proof (PMfd_fdfs_only F0 fs0) as FDO.
change (fs_size 8) with 16384 in *.
assert (INF : In (F, 8%nat) (rt_frames RT Σ1)) by (rewrite FR1; left; reflexivity).
assert (F8 : F mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
assert (SHR : SH_LO <= sf /\ sf + 2048 <= SH_HI).
{ rewrite Esf. rewrite shad_shiftr. destruct (shad_range_al F 16384 ltac:(lia) F8 ltac:(reflexivity) ltac:(lia) ltac:(clear - FLO LOR SR UT; unfold RT_STACK, APP_TOP, USTACK_TOP in *; lia)) as (A1 & A2).
split; [exact A1|]. change (16384 / 8) with 2048 in A2. exact A2. }

destruct SHR as (SH1 & SH2).
pose proof (frame_facts RT AF Σ1 m F 8%nat ART0 INF) as (FF1 & FF64 & FIMG & FSP0 & FHI & FSH0 & FSH1 & FSH2 & FSH3 & FSELF).
change (fs_size 8) with 16384 in *. change (16384 / 8) with 2048 in *.
assert (ESH : shad F = sf) by (rewrite <- FSH0; reflexivity). rewrite ESH in *. clear FSH0.
assert (FSA : F + 16384 <= sf \/ sf + 2048 <= F) by exact FSELF.
assert (SFS : sf + 2048 <= S1) by (clear - SH2 SHL LOR; unfold SH_HI, RT_STACK in *; lia).
assert (FS1 : F + 16384 <= S1) by (clear - FLO LOR; unfold RT_STACK in *; lia).
assert (LOS : lo <= S1) by (clear - LOR; unfold RT_STACK in *; lia).
assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
cps_norm. cps_hide.

Time cps_seg (hx_r sf).
destruct POST as (m1 & -> & MU1 & WM1 & MI1 & SHT1).
clear SHT.
Time cps_seg_post.
apply (fp_local_munch IO_FP ERR_rep _ m m1 ERR_loc IO_img MU1) in ERR0; [| intros x Hx; cbn [outside]; split; [| exact I]; clear - Hx SH1; unfold SH_LO, SEGTOP_A in *; lia].
assert (OUT1 : forall so, OUT_rep so (x_m0 X) -> OUT_rep so m1).
{ intros so Hso. apply (fp_local_munch IO_FP (OUT_rep so) _ m m1 (OUT_loc so) IO_img MU1); [intros x Hx; cbn [outside]; split; [| exact I]; clear - Hx SH1; unfold SH_LO, SEGTOP_A in *; lia| exact (OUT0 so Hso)]. }
clear OUT0 MU1 WM1.

Time cps_seg (hx_1 sf).
destruct POST as (m2 & -> & MU2 & WM2 & MI2).
Time cps_seg_post.
apply (fp_local_munch IO_FP ERR_rep _ m1 m2 ERR_loc IO_img MU2) in ERR0; [| intros x Hx; exact I].
assert (OUT2 : forall so, OUT_rep so (x_m0 X) -> OUT_rep so m2).
{ intros so Hso. apply (fp_local_munch IO_FP (OUT_rep so) _ m1 m2 (OUT_loc so) IO_img MU2); [intros x Hx; exact I| exact (OUT1 so Hso)]. }
clear OUT1 MU2 WM2.
Time cps_rt (SS8 Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 (sf + 16) 1000 lo).
{ cbn. tauto. }
{ intros i Hi. exists F, 8%nat. split; [exact INF|]. rewrite ESH. change (fs_size 8) with 16384. rewrite FSH1. lia. }
{ exact (proj2 SHM). }
{ cps_callok. }
intros cc3 (v0 & Hc3).
Time cps_unpack Hc3 as (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & BY3).
assert (ERR3 : ERR_rep m3).
{ apply (ERR_loc m2 m3 ERR0). intros a Ha. apply PRES3; [right; left; exact (IO_img _ Ha)|].
pose proof (client_static_range _ (IO_img _ Ha)) as R. intros Hin. clear - R Hin SH1. unfold SH_LO, SEGTOP_A in *. lia. }
assert (OUT3 : forall so, OUT_rep so (x_m0 X) -> OUT_rep so m3).
{ intros so Hso. apply (OUT_loc so m2 m3 (OUT2 so Hso)). intros a Ha. apply PRES3; [right; left; exact (IO_img _ Ha)|].
pose proof (client_static_range _ (IO_img _ Ha)) as R. intros Hin. clear - R Hin SH1. unfold SH_LO, SEGTOP_A in *. lia. }
clear ERR0 OUT2 PRES3 BY3.

Time cps_seg (hx_2 F).
{ clear - FF1 FS1 SR UT; unfold USTACK_TOP in *; lia. }
destruct POST as (m4 & -> & MU4 & WM4 & MI4 & HD4).
clear HD.
Time cps_seg_post.
apply (fp_local_munch IO_FP ERR_rep _ m3 m4 ERR_loc IO_img MU4) in ERR3; [| intros x Hx; cbn [outside]; split; [| exact I]; clear - Hx FIMG; unfold SEGTOP_A in *; lia].
assert (OUT4 : forall so, OUT_rep so (x_m0 X) -> OUT_rep so m4).
{ intros so Hso. apply (fp_local_munch IO_FP (OUT_rep so) _ m3 m4 (OUT_loc so) IO_img MU4); [intros x Hx; cbn [outside]; split; [| exact I]; clear - Hx FIMG; unfold SEGTOP_A in *; lia| exact (OUT3 so Hso)]. }
clear OUT3 MU4 WM4.
Time cps_rt (SF8 Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 F [] lo 9280).
{ intros _. unfold HF_SIZE. split; [reflexivity|]. split; [reflexivity| change (fs_size 8) with 16384; lia]. }
{ intros _. exact PO1. }
{ cps_callok. }
intros cc5 (Σ2 & v5 & Hc5 & FRS2 & LV2 & SPS2 & CR2 & PO2).
Time cps_unpack Hc5 as (m5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5).
pose proof (fp_local_pres IO_FP ERR_rep _ _ _ m4 m5 ERR_loc IO_img PRES5 ERR3) as ERR5.
assert (OUT5 : forall so, OUT_rep so (x_m0 X) -> OUT_rep so m5) by (intros so Hso; exact (fp_local_pres IO_FP (OUT_rep so) _ _ _ m4 m5 (OUT_loc so) IO_img PRES5 (OUT4 so Hso))).
clear ERR3 OUT4 PRES5.
assert (LOW2 : rt_sp0 RT Σ2 - 8388608 <= lo) by (rewrite SPS2; exact LOW1).

Time cps_seg (hx_3 usp S1 lo).
destruct POST as (m6 & -> & MU6 & WM6 & MI6 & ST6).
clear SPL GAP SV ST5.
Time cps_seg_post.
apply (fp_local_munch IO_FP ERR_rep _ m5 m6 ERR_loc IO_img MU6) in ERR5; [| intros x Hx; exact I].
assert (OUT6 : forall so, OUT_rep so (x_m0 X) -> OUT_rep so m6).
{ intros so Hso. apply (fp_local_munch IO_FP (OUT_rep so) _ m5 m6 (OUT_loc so) IO_img MU6); [intros x Hx; exact I| exact (OUT5 so Hso)]. }
apply Hk. exists Σ2.
split; [| split; [congruence|]; split; [exact FRS2|]; split; [congruence|]; rewrite CR2, CR0; exact CR1].
eapply ASTA_conseq; [exact Hc2|]. intros ms <-. exists m6.
split; [unfold ret_stR; do 16 eexists; split; [reflexivity| intros _; exact FRMF]|].
split; [split; [exact ART| split; [exact MI6| exact ST6]]|].
split; [rewrite LV0, FR0; unfold LIB_FP; cbn [app]; exact PF|].
split; [exact (LIB_loc (x_m0 X) m6 LIB0 ltac:(intros a Ha; destruct Ha as (x & y & Hin & _); destruct Hin))|].
split; [exact ERR5| exact OUT6].
Qed.
End Exit.

Section ExitXT.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Variable LIB : mem -> Prop.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis SS8 : set_shadow_contract RT 0xf8.
Hypothesis SF8 : stack_free_contract RT 8.
Variable X : hinv.
Variable F0 : list (word * FdEntry).
Variable fs0 : Fs.Fs.

Theorem h_xt_ok : forall (Σ : rts RT) (fc0 : bv 32),
hinv_ok OUT_rep IO_FP X -> rt_live RT Σ = x_live X -> rt_frames RT Σ = [] -> rt_sp0 RT Σ = x_sp0 X -> rt_credit RT Σ = x_cr0 X -> LIB (x_m0 X) ->
cps asegs (at_XT RT OUT_rep ERR_rep IO_FP X F0 fs0) (h_final RT OUT_rep ERR_rep IO_FP X F0 fs0 Σ LIB fc0).
Proof using AF ERR_loc OUT_loc IO_img LIB_loc SS8 SF8.
intros Σ fc0 HX LV0 FR0 SP0 CR0 LIB0 T c Hc Hk.
destruct Hc as (Σ1 & Fx & fc & m & ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6
& w0 & w8 & w16 & w48 & w56 & w64 & w80 & w88 & w104 & w112 & w120 & w128 & w136 & w144 & w152 & w160 & w168 & w176 & w184 & w192 & w200
& Hc & FRM & LV1 & FR1 & SP1 & PO1 & CR1 & ART1 & MI1 & ST1 & PF & ERR1 & OUT1 & SPC & SHL).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).

pose proof (h_shr_at OUT_rep IO_FP IO_img X HX m PF) as SHR.
pose proof (h_saves_at OUT_rep IO_FP IO_img X HX m PF) as SV.
destruct (h_gap_at OUT_rep IO_FP IO_img X HX m PF) as (jg & GAP).
pose proof (h_hdr_at OUT_rep IO_FP IO_img X HX m PF) as HDR.
pose proof (h_pf_entry OUT_rep IO_FP IO_img X HX m PF) as PFE.
pose proof (hi_naf _ _ _ HX) as NAF. pose proof (hi_out _ _ _ HX) as OUT0.
clear PF.

refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply hx_0; [reflexivity| exact SPC| exact MI1| unfold USTACK_TOP in *; lia]. }
intros ms' c' (m1 & -> & MU0 & WM0 & MI0 & SPC0) Hc'.
assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= x_lo X) by (rewrite SP1; exact LW).
assert (INF : In (x_F X, 8%nat) (rt_frames RT Σ1)) by (rewrite FR1; left; reflexivity).
cps_norm. cps_hide.
Time cps_seg_post.
apply (fp_local_munch IO_FP ERR_rep _ m m1 ERR_loc IO_img MU0) in ERR1; [| intros x Hx; exact I].
assert (OUTE : forall so, OUT_rep so (x_m0 X) -> OUT_rep so m1).
{ intros so Hso. apply (fp_local_munch IO_FP (OUT_rep so) _ m m1 (OUT_loc so) IO_img MU0); [intros x Hx; exact I| exact (OUT1 so (OUT0 so Hso))]. }
cb_cut SHR 1000%nat SHM. chunk_uncons HDR as HDR0.
refine (h_ep_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img LIB LIB_loc SS8 SF8 X F0 fs0 Σ fc0 _ LV0 FR0 SP0 CR0 LIB0 T c' _ Hk).
{ pose proof (hi_F _ _ _ HX) as (_ & _ & _ & FH & _). unfold hep_ok. change (fs_size 8) with 16384 in *. unfold H_STACK in *. cps_unf.
split; [exact U16|]. split; [exact U336|]. split; [exact UT|]. split; [exact S32|]. split; [exact SR|]. split; [exact LW|].
split; [lia|]. split; [exact SHLO|]. split; [exact FP0|]. split; [exact F64|]. split; [exact FL| exact FH]. }

unfold at_EP.
exists Σ1, Fx, fc, m1, ra, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, s2, s8, s9, s10, s11, t3, t4, t5, t6.
exists w0, w8, w16, (Z_to_bv 64 (x_sf X + 16)), (Z_to_bv 64 (x_F X)), (Z_to_bv 64 (x_F X)), w48, w56, w64, (Z_to_bv 64 (x_d X)), w80, w88, (Z_to_bv 64 SHB),
w104, w112, w120, w128, w136, w144, w152, w160, w168, w176, w184, w192, w200, (Z_to_bv 64 (x_F X)), (Z_to_bv 64 0x41b58ab3).
do 3 eexists.
split; [exact Hc'|]. split; [exact FRM|]. split; [exact LV1|]. split; [exact FR1|]. split; [exact SP1|]. split; [exact PO1|]. split; [lia|].
split; [exact ART|]. split; [exact MI0|]. split; [eassumption|].
split; [exact SHR|]. split; [exact SHM|]. split; [exact HDR0|].
split; [exact SPC0|]. split; [exact GAP|]. split; [exact SV|]. split; [exact PFE|]. split; [exact NAF|]. split; [exact ERR1| exact OUTE].
Qed.
End ExitXT.
