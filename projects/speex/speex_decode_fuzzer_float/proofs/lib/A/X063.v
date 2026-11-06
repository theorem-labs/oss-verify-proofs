(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s X05u
X081 X05l X07y X05m X09f X06d X069 X05w X064 X062.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0yr X0wl X0wn X0ys X0yq X0x2 X0zo X0wp X0wx X0wv.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zo OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wp OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wx OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wv.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma sb_bufs_agree : forall (s : sbd_state bptr) S a j (m m' : mem),
sb_bufs bsegs m a j -> sb_junk_ok s j -> agree_blocks bsegs m m' (tl (sb_blocks s S a)) -> sb_bufs bsegs m' a j.
Proof.
intros s S a j m m' (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7) (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10) AG.
unfold sb_bufs. repeat match goal with |- _ /\ _ => split end;
(eapply rw_cells_agree_at; [eassumption|]);
[ eapply (agree_blocks_at bsegs m m' _ (sbd_g0_mem s, a_g0 a, 256)) | eapply (agree_blocks_at bsegs m m' _ (sbd_g1_mem s, a_g1 a, 256))
| eapply (agree_blocks_at bsegs m m' _ (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s))
| eapply (agree_blocks_at bsegs m m' _ (sbd_old_qlsp s, a_oq a, 32)) | eapply (agree_blocks_at bsegs m m' _ (sbd_interp_qlpc s, a_iq a, 32))
| eapply (agree_blocks_at bsegs m m' _ (sbd_mem_sp s, a_msp a, 64))
| eapply (agree_blocks_at bsegs m m' _ (sbd_pi_gain s, a_pg a, 16)) | eapply (agree_blocks_at bsegs m m' _ (sbd_exc_rms s, a_er a, 16)) ];
try exact AG; try eassumption;
try (cbn; tauto); unfold blk_addr, blk_size; cbn [fst snd]; rewrite ?cells_size_f32; lia.
Qed.

Lemma agree_blocks_app : forall (m m' : mem) L1 L2, agree_blocks bsegs m m' L1 -> agree_blocks bsegs m m' L2 -> agree_blocks bsegs m m' (L1 ++ L2).
Proof.
intros m m' L1 L2 A1 A2 x Hx (b & Hb & Hab). apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [apply A1| apply A2]; try exact Hx; exists b; split; assumption.
Qed.

Definition sbtl (s : sbd_state bptr) (a : sb_addrs) (OUT : Z) (j : sb_junk) : list cell :=
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (a_g0 a)); C8 (Z_to_bv 64 (a_g1 a)); C8 (Z_to_bv 64 (a_exc a));
C8 (Z_to_bv 64 (a_oq a)); C8 (Z_to_bv 64 (a_iq a)); C8 (Z_to_bv 64 (a_msp a)); C8 (Z_to_bv 64 (a_pg a)); C8 (Z_to_bv 64 (a_er a));
C8 (Z_to_bv 64 (sb_isave_ptr OUT s)); C4 (sj_last_ener j); C4 (sj_seed j); C4 (Z_to_bv 64 (sbd_encode_submode s)); CB 4 (sj_pad1 j);
C8 (Z_to_bv 64 (sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR (sbd_mode s))); C4 (Z_to_bv 64 (sbd_submodeID s)); CB 4 (sj_pad2 j)].

Lemma sb_cells_split : forall s a OUT j,
SBCELLS s a OUT j = sbhd (sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode (sbd_mode s)) (a_low a)
(Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s))
(Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s))
(Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 (sbd_lpc_enh_enabled s)) ++ sbtl s a OUT j.
Proof. reflexivity. Qed.

Ltac piece X P :=
lazymatch type of X with
| rw_cells ?segs ?m ?A (?cs1 ++ ?cs2) =>
let n := eval vm_compute in (Z.of_nat (cells_size cs1)) in
apply (proj1 (rw_cells_app segs m A cs1 cs2)) in X; destruct X as [P X];
change (Z.of_nat (cells_size cs1)) with n in X;
repeat match type of X with rw_cells _ _ (?B + ?a + ?b) _ => let v := eval vm_compute in (a + b) in replace (B + a + b) with (B + v) in X by lia end
end.

Lemma NoDup_app_in_neq {A} (l1 l2 : list A) x y : List.NoDup (l1 ++ l2) -> In x l1 -> In y l2 -> x <> y.
Proof.
intros ND H1 H2 ->. induction l1 as [|z l1 IH]; [destruct H1|].
cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND]. destruct H1 as [->|H1].
- apply NI. apply in_app_iff. right. exact H2.
- exact (IH ND H1).
Qed.

Ltac xfp PRES WM OUTB H :=
lazymatch type of PRES with
| rt_pres_fp ?live ?frames ?sp ?W ?m ?m' =>
lazymatch type of H with
| rw_cells bsegs m ?A ?cs =>
let H' := fresh "T" in
assert (H' : rw_cells bsegs m' A cs)
by (apply (rw_cells_agree bsegs m m' A cs H);
[ apply (agree_of_pres_fp live frames sp W m m' _ PRES); intros ? ?Hx; cps_sizes Hx;
split; [ aclient_tac ltac:(ulc) | cbn [outside]; split; [ ulc | apply OUTB; ulc ] ]
| exact WM ]);
clear H; rename H' into H
end
end.

Lemma lookahead_val : forall d : dec_state bptr, (dec_depth d <= 3)%nat ->
fst (speex_decoder_ctl d CtlGetLookahead) = 40 \/ fst (speex_decoder_ctl d CtlGetLookahead) = 80 \/ fst (speex_decoder_ctl d CtlGetLookahead) = 160.
Proof.
intros d Hd. destruct d as [st|s1 [st|s2 [st|s3 low]]].
1-3: cbn -[Z.mul]; unfold NB_SUBFRAME_SIZE; lia.
exfalso. cbn [dec_depth] in Hd. pose proof (dec_depth_pos low). lia.
Qed.

Lemma creq_pre_agree : forall STEREO (m m' : mem) S S' d d' P r, creq_grp1 r = true ->
creq_pre STEREO m S d P r -> agree_at bsegs m m' P (creq_size r) -> creq_pre STEREO m' S' d' P r.
Proof.
intros STEREO m m' S S' d d' P r G PRE AG. destruct r; try discriminate G; cbn [creq_pre creq_size] in *.
- destruct PRE as (w & X & E). exists w. split; [| exact E]. exact (rw_cells_agree_at bsegs m m' P _ X AG).
- destruct PRE as (w & X). exists w. exact (rw_cells_agree_at bsegs m m' P _ X AG).
- destruct PRE as (w & X). exists w. exact (rw_cells_agree_at bsegs m m' P _ X AG).
- destruct PRE as (w & X & E). exists w. split; [| exact E]. exact (rw_cells_agree_at bsegs m m' P _ X AG).
- destruct PRE as (w & X). exists w. exact (rw_cells_agree_at bsegs m m' P _ X AG).
- destruct PRE as (w & X). exists w. exact (rw_cells_agree_at bsegs m m' P _ X AG).
- destruct PRE as (w & X & E). exists w. split; [| exact E]. exact (rw_cells_agree_at bsegs m m' P _ X AG).
Qed.

Lemma agree_at_of_pres_fp : forall live frames sp W (m m' : mem) A n,
rt_pres_fp live frames sp W m m' -> wmono bsegs m m' -> 0 <= A -> A + n <= 2^64 ->
(forall x, A <= x < A + n -> aclient live frames sp x /\ outside W x) -> agree_at bsegs m m' A n.
Proof.
intros live frames sp W m m' A n PRES WM A0 AN H a Ha. split; [| apply WM]. destruct (H a Ha) as [H1 H2].
apply PRES; rewrite wa_unsigned by lia; assumption.
Qed.

Section CtlSB.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.

Theorem ctl_cps_sb : forall s low, ctl_cps_at RT low -> ctl_cps_at RT (DecSB s low).
Proof using AF SM0 AF_LIB.
intros s low IH Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
OUT STEREO S LBD r P lo fp kp FDO MST -> -> -> -> GRP REP DEP ND OK PRE LIVE INF FP1 FP2 ACP PAL FRM CRD ART0 MI0 FRM0 ST0 LOW LOR SPT SPA.
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

destruct (frame_below_lo RT AF Σ m fp kp lo ART0 INF LOW) as (BF1 & BF2 & _).
pose proof (frame_facts RT AF Σ m fp kp ART0 INF) as (FP0 & FP64 & FPIMG & _ & FPHI & _ & _ & _ & _ & _).
destruct (frame_live_apart RT AF Σ m fp kp S 160 ART0 INF INL) as (FLA1 & _).
assert (FSZ : 0 <= fs_size kp) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
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
destruct (frame_live_apart RT AF Σ m fp kp _ _ ART0 INF (LIVE b Hb)) as (B2 & _). clear - B2 Hx Hin FP1 FP2. lia. }

assert (OFFW : forall x, SH_LO <= x < SH_HI -> outside ((P, P + creq_size r) :: blocks_ivs LBD) x).
{ intros x Hx. split; [clear - Hx FPHI FP2 FSZ FP1; unfold SH_LO, SH_HI in Hx; cbn [fst snd]; lia| exact (outside_blocks_shadow RT AF Σ m LBD x ART0 LIVE0 Hx)]. }
pose proof (fun m' (PR : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((P, P + creq_size r) :: blocks_ivs LBD) m m') =>
acc_of_pres_fp RT AF Σ m m m' usp _ fp kp P (creq_size r) ART0 INF FP1 FP2 PR OFFW ACP) as ACCK.
assert (PR0 : 0 <= P) by lia.
assert (PR1 : P + creq_size r <= 2^64) by (clear - FP2 BF1 LOR SPT CSP; unfold RT_STACK, USTACK_TOP in *; lia).
assert (PCL : forall x, P <= x < P + creq_size r -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x)
by (intros x Hx; right; right; right; left; exists fp, kp; split; [exact INF| lia]).
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
x < lo /\ (x < S \/ S + 160 <= x) /\ (x < fp \/ fp + fs_size kp <= x)).
{ intros b x Hb Hx.
assert (Hb' : In b LBD) by (rewrite ELBD; cbn [sb_blocks tl app] in Hb |- *; right; exact Hb).
pose proof (LIVE b Hb') as LB.
destruct (live_below_lo RT AF Σ m _ _ lo ART0 LB LOW) as (_ & B1 & _).
destruct (frame_live_apart RT AF Σ m fp kp _ _ ART0 INF LB) as (B2 & _).
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
destruct (frame_live_apart RT AF Σ1 m2 f 0%nat _ _ ART2 INF0 (LIVE1 b Hb')) as (B2 & B3).
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
pose proof (ACCK m3 PF) as ACP3.
assert (OUTB : forall x, (lo <= x \/ (S <= x < S + 160) \/ (fp <= x < fp + fs_size kp) \/ (f <= x < f + 64) \/ (sf <= x < sf + 8)) -> outside (blocks_ivs LBL) x).
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
destruct r; try discriminate GRP; cbn [ctl_req_code creq_size creq_align] in *.
4: {
destruct PRE3 as (w3 & ARG3 & EQW & RV).
assert (OBP3 : aobj bsegs m3 P 4) by (split; [lia|]; split; [ulc| exact ACP3]).
assert (APS : P + 4 <= S \/ S + 160 <= P) by (clear - FLA1 FP1 FP2 FSZ; unfold hid in FLA1; lia).
assert (SFA : S + 160 <= f \/ f + 64 <= S) by (clear - FLA; unfold hid in FLA; lia).
assert (PFA4 : P + 4 <= f \/ f + 64 <= P) by (clear - PFA; unfold hid in PFA; lia).
assert (POFF : P + 4 <= SH_LO \/ SH_HI <= P) by (clear - FPHI FP1 FP2 FSZ; unfold hid in FPHI; unfold SH_LO, SH_HI; lia).
assert (FSH : f + 64 <= SH_LO \/ SH_HI <= f) by (clear - FHI; unfold hid in FHI; unfold SH_LO, SH_HI; lia).
assert (FTOP' : f + 64 <= APP_TOP) by (clear - FTOP; unfold APP_TOP; lia).
assert (FRSa : rw_cells bsegs m3 sf (sbctl_shadow bF8 bF8)) by exact FRS3. clear FRS3. cps_hide.
apply (proj1 (rw_cells_app bsegs m3 f [_; _; _; _; _; _; _] [_; _])) in FRB3. destruct FRB3 as [FB0 FB1].
change (Z.of_nat (cells_size _)) with 48 in FB1. chunk_uncons FB1 as TMP3. replace (f + 48 + 4) with (f + 52) in FB1 by lia.
cps_seg (sbarm_ssr_a usp S P f sf).
destruct POST as (m4 & yc3 & yc4 & yc5 & tw & -> & HD4 & ARG4 & TMP4 & ETW & FRS4 & MU4 & WM4 & MI4).
pose proof (agree_blocks_of_munch bsegs _ m3 m4 (tl (sb_blocks s S a) ++ LBL) MU4 WM4
ltac:(intros b x Hb Hx; pose proof (BOUT b x Hb Hx) as H1; pose proof (BOUT2 b x Hb Hx) as H2; clear - H1 H2; cbn [outside]; repeat split; lia)) as AG4.
apply (sb_bufs_agree s S a j m3 m4) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG4| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG4| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG4 HD3 ARG3 TMP3 FRSa OBP3. unfold sbhd in HD4. unfold sbctl_shadow, bF1, bF3, bF8 in FRS4.
cps_seg_post.

assert (ACT : acc bsegs m4 (f + 48) 4).
{ apply (acc_ushadow bsegs m4 (f + 48) 4); [clear - F1; Z.div_mod_to_equations; lia| lia| lia|].
replace (shad (f + 48)) with (sf + 6) by (rewrite SHF; unfold shad; clear - F1; Z.div_mod_to_equations; lia).
destruct FRS4 as [[_ BY] _]. cbn [cells_bytes cbytes app] in BY.
change [Z_to_bv 8 (-15); Z_to_bv 8 (-15); Z_to_bv 8 (-15); Z_to_bv 8 (-15); Z_to_bv 8 (-8); Z_to_bv 8 (-14); Z_to_bv 8 4; Z_to_bv 8 (-13)]
with ([Z_to_bv 8 (-15); Z_to_bv 8 (-15); Z_to_bv 8 (-15); Z_to_bv 8 (-15); Z_to_bv 8 (-8); Z_to_bv 8 (-14)] ++ [Z_to_bv 8 4] ++ [Z_to_bv 8 (-13)]) in BY.
apply bytes_at_app in BY. destruct BY as [_ BY]. apply bytes_at_app in BY. destruct BY as [BY _]. exact BY. }
assert (PREL4 : creq_pre STEREO m4 (a_low a) low (f + 48) (CtlSetSamplingRate (c_shr1 v))).
{ cbn [creq_pre]. exists tw. split; [exact TMP4|]. subst tw. exact (shr1w_low32 w3 v EQW RV). }
assert (M4f : (f + 48) mod 4 = 0) by (clear - F1; Z.div_mod_to_equations; lia).
lazymatch goal with A : X14x.ART RT Σ1 m4 |- _ => rename A into ART4 end.
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes bsegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end;
[ eapply (IH Σ1 PMc) with (OUT := OUTL) (STEREO := STEREO) (LBD := LBL) (r := (CtlSetSamplingRate (c_shr1 v))) (P := (f + 48)) (lo := lo) (fp := f) (kp := 0%nat); cps_auto | ].
{ cbn [creq_size]. change (fs_size 0) with 64. lia. }
{ rewrite EU. eassumption. }
intros cc5 (Σ2 & Hc5 & LV2 & FRS2 & SP2 & CR2 & PO2).
destruct (ASTA_unpack RT Σ2 PMc _ cc5 Hc5) as (ms5 & PO5 & Hc5'). clear Hc5. cbv beta in PO5.
destruct PO5 as (m5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5 & REP5 & CP5 & ACP5).
destruct RS5 as (zt0 & zt1 & zt2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & F5 & fc5 & -> & FRM5).
rewrite EU in *. cbn [creq_ivs creq_size app] in PRES5.

xfp PRES5 WM5 OUTB FR3. xfp PRES5 WM5 OUTB FB0. xfp PRES5 WM5 OUTB FB1. xfp PRES5 WM5 OUTB FRS4. xfp PRES5 WM5 OUTB HD4. xfp PRES5 WM5 OUTB TL. xfp PRES5 WM5 OUTB ARG4.
assert (AG5 : agree_blocks bsegs m4 m5 (tl (sb_blocks s S a))).
{ apply (agree_blocks_of_pres_fp RT Σ1 _ _ _ m4 m5 _ PRES5 WM5).
- intros b Hb. apply LIVE1. apply in_app_iff. left. cbn [sb_blocks tl] in Hb |- *. right. exact Hb.
- intros b x Hb Hx. split; [| exact (APL b x Hb Hx)].
pose proof (BOUT b x ltac:(apply in_app_iff; left; exact Hb) Hx) as H1. pose proof (BOUT2 b x ltac:(apply in_app_iff; left; exact Hb) Hx) as H2.
clear - H1 H2 FP1 FP2. cbn [fst snd]. lia. }
apply (sb_bufs_agree s S a j m4 m5) in BUFS; [| exact JOK | exact AG5]. clear AG5 RLOW.
assert (PF5 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((P, P + 4) :: (S, S + 160) :: blocks_ivs (tl (sb_blocks s S a) ++ LBL)) m m5).
{ apply (pres_fp_trans _ _ _ _ m m4 m5 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -96) _ m4 m5 PRES5).
- intros e He. rewrite LV1. exact He.
- intros e He. rewrite FRS1. right. exact He.
- lia.
- intros x Hx (O1 & O2 & O3). split; [pose proof (NAF x Hx) as (N1 & _); change (fs_size 0) with 64 in N1; clear - N1; cbn [fst snd]; lia| exact (outside_blocks_app_r (tl (sb_blocks s S a)) LBL x O3)]. }
clear PF PRES5. rename PF5 into PF.
cps_sigma LV2 FRS2 SP2.
destruct CP5 as (w5 & TMP5 & _).
assert (FRSb : rw_cells bsegs m5 sf (sbctl_shadow bF8 (Z_to_bv 8 4))) by exact FRS4. clear FRS4.
destruct (af_acc_live RT AF Σ2 m5 S 160 ART5 INL) as (_ & ACS5).
assert (OBS5 : aobj bsegs m5 S 160) by (split; [lia|]; split; [ulc| exact ACS5]).
cps_seg (sbarm_ssr_b usp S P f sf).
destruct POST as (m5b & yb1 & -> & FRS5b & MU5b & WM5b & MI5b).
pose proof (agree_blocks_of_munch bsegs _ m5 m5b (tl (sb_blocks s S a) ++ LBL) MU5b WM5b
ltac:(intros b x Hb Hx; pose proof (BOUT2 b x Hb Hx) as H2; clear - H2; cbn [outside]; split; [lia| exact I])) as AG5b.
apply (sb_bufs_agree s S a j m5 m5b) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG5b| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG5b| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG5b FRSb OBS5 ACS5. unfold sbctl_shadow, bF1, bF3, bF8 in FRS5b.
cps_seg_post.

assert (FRSE : rw_cells bsegs m5b sf (sbctl_shadow bF8 bF8)) by exact FRS5b. clear FRS5b.
chunk_uncons FB0 as HDF.
cps_seg (sbctl_epi_a usp f sf).
destruct POST as (m6 & -> & MU6 & WM6 & MI6 & FRS6).
pose proof (agree_blocks_of_munch bsegs _ m5b m6 (tl (sb_blocks s S a) ++ LBL) MU6 WM6
ltac:(intros b x Hb Hx; pose proof (BOUT2 b x Hb Hx) as H2; clear - H2; cbn [outside]; repeat split; lia)) as AG6.
apply (sb_bufs_agree s S a j m5b m6) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG6 HDF FRSE FB0 FB1 TMP5. unfold sbctl_shadow_dead, bF5 in FRS6. cbn [map repeat] in FRS6.
cps_seg_post.

assert (EF2 : rt_frames RT Σ2 = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRS2; exact FRS1).
assert (EL2 : rt_live RT Σ2 = rt_live RT Σ) by (rewrite LV2; exact LV1).
lazymatch goal with A : X14x.ART RT Σ2 _ |- _ => rename A into ARTX end.
cps_release_intro ARTX EF2 EL2 (fun E : rt_frames RT Σ = [] => eq_trans PO2 (eq_trans PO1 (PNIL E))) Σ3 fl.
assert (FLS : fl < S \/ S + 160 <= fl).
{ destruct (Z_lt_dec fl S) as [L|L]; [left; exact L|]. destruct (Z_le_dec (S + 160) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; left. exists S, 160. split; [exact INL| clear - L G; lia]. }
assert (FLP : fl < fp \/ fp + fs_size kp - 8 <= fl).
{ destruct (Z_lt_dec fl fp) as [L|L]; [left; exact L|]. destruct (Z_le_dec (fp + fs_size kp - 8) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; right; left. exists fp, kp. split; [exact INF| clear - L G; lia]. }
assert (FR6 : rw_cells bsegs m6 (usp + -96) (sbctl_frame (C8 (Z_to_bv 64 f)) s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) by exact FR3. clear FR3.
cps_seg (sbctl_epi_b usp lo f fl).
destruct POST as (m7 & -> & MU7 & WM7 & MI7 & ST7 & FLG7).
assert (AG7 : agree_blocks bsegs m6 m7 (tl (sb_blocks s S a) ++ LBL)).
{ apply (agree_blocks_of_munch bsegs _ m6 m7 _ MU7 WM7). intros b x Hb Hx. cbn [outside]. split; [| exact I]. intros Hfl.
apply NAC. right; right; left. exists (blk_addr b), (blk_size b). split; [| clear - Hx Hfl; lia].
rewrite LV2. apply LIVE1. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; cbn [sb_blocks tl] in Hb |- *; right; exact Hb| right; exact Hb]. }
apply (sb_bufs_agree s S a j m6 m7) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG7 FR6 FRS6.
cps_release_done REL MU7 WM7 FLG7.
apply Hk. exists Σ3. split; [| cbn [dec_depth]; split; [congruence|]; split; [congruence|]; split; [congruence|]; split; [clear - EC CR2 CR1; cbn [dec_depth] in *; lia| congruence]].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m7.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM5]|].
split. { split; [assumption|]. split; [exact MI7|]. split; [cps_wmono| exact ST7]. }
split; [exact PF|].
pose proof (ACCK m7 PF) as ACP7.
cbn [speex_decoder_ctl] in *. destruct (speex_decoder_ctl low (CtlSetSamplingRate (c_shr1 v))) as [v' low'] eqn:EC5. cbn [fst snd] in *.
split; [| split; [exists w3; split; [exact ARG4| exact EQW]| exact ACP7]].
assert (HDN : rw_cells bsegs m7 S (sbhd MP (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s))
(Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s))
(Z_to_bv 64 v) (Z_to_bv 64 (sbd_lpc_enh_enabled s)))).
{ unfold sbhd. eapply rw_cells_samebytes; [exact HD4| clear; cbn; tauto| cbn [cells_bytes cbytes app]; rewrite (sx32_cell_eqm w3 v EQW); reflexivity| reflexivity]. }
cbn [decst_rep]. exists a, j, LBL. split; [reflexivity|]. split; [exact S8|]. split; [exact SPOS|]. split; [destruct INV as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12); unfold sb_inv; cbn; repeat split; first [assumption | clear - RV I8 I9 I11; lia]|]. split; [exact JOK|].
split; [change (SBCELLS (set_sbd_sampling_rate s v) a OUT j) with (sbhd (sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode (sbd_mode s)) (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s)) (Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s)) (Z_to_bv 64 v) (Z_to_bv 64 (sbd_lpc_enh_enabled s)) ++ sbtl s a OUT j); rewrite <- EMP; apply (proj2 (rw_cells_app bsegs m7 S _ _)); split; [exact HDN| exact TL]|].
split; [exact BUFS|]. exists OUTL. exact REP5. }
1: {
destruct PRE3 as (w3 & _ & _ & RV).
cps_seg (sbarm_pass_a usp S P f sf).
destruct POST as (ya3 & ya4 & ya5 & ->).
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes bsegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end;
[ eapply (IH Σ1 PMc) with (OUT := OUTL) (STEREO := STEREO) (LBD := LBL) (r := (CtlSetEnh v)) (P := P) (lo := lo) (fp := fp) (kp := kp); cps_auto | ].
{ rewrite EU. exact ST3. }
intros cc5 (Σ2 & Hc5 & LV2 & FRS2 & SP2 & CR2 & PO2).
destruct (ASTA_unpack RT Σ2 PMc _ cc5 Hc5) as (ms5 & PO5 & Hc5'). clear Hc5. cbv beta in PO5.
destruct PO5 as (m5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5 & REP5 & CP5 & ACP5).
destruct RS5 as (zt0 & zt1 & zt2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & F5 & fc5 & -> & FRM5).
rewrite EU in *. cbn [creq_ivs creq_size app] in PRES5.

xfp PRES5 WM5 OUTB FR3. xfp PRES5 WM5 OUTB FRB3. xfp PRES5 WM5 OUTB FRS3. xfp PRES5 WM5 OUTB HD3. xfp PRES5 WM5 OUTB TL.
assert (AG5 : agree_blocks bsegs m3 m5 (tl (sb_blocks s S a))).
{ apply (agree_blocks_of_pres_fp RT Σ1 _ _ _ m3 m5 _ PRES5 WM5).
- intros b Hb. apply LIVE1. apply in_app_iff. left. cbn [sb_blocks tl] in Hb |- *. right. exact Hb.
- intros b x Hb Hx. split; [| exact (APL b x Hb Hx)].
pose proof (BOUT b x ltac:(apply in_app_iff; left; exact Hb) Hx) as H1. pose proof (BOUT2 b x ltac:(apply in_app_iff; left; exact Hb) Hx) as H2.
clear - H1 H2 FP1 FP2. cbn [fst snd]. lia. }
apply (sb_bufs_agree s S a j m3 m5) in BUFS; [| exact JOK | exact AG5]. clear AG5 RLOW.
assert (PF5 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((P, P + 4) :: (S, S + 160) :: blocks_ivs (tl (sb_blocks s S a) ++ LBL)) m m5).
{ apply (pres_fp_trans _ _ _ _ m m3 m5 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -96) _ m3 m5 PRES5).
- intros e He. rewrite LV1. exact He.
- intros e He. rewrite FRS1. right. exact He.
- lia.
- intros x Hx (O1 & O2 & O3). split; [exact O1| exact (outside_blocks_app_r (tl (sb_blocks s S a)) LBL x O3)]. }
clear PF PRES5. rename PF5 into PF.
cps_sigma LV2 FRS2 SP2.
destruct CP5 as (w5 & ARG5 & EQW5).
destruct (af_acc_live RT AF Σ2 m5 S 160 ART5 INL) as (_ & ACS5).
assert (OBS5 : aobj bsegs m5 S 160) by (split; [lia|]; split; [ulc| exact ACS5]).
assert (OBP5 : aobj bsegs m5 P 4) by (split; [lia|]; split; [ulc| exact ACP5]).
assert (APS : P + 4 <= S \/ S + 160 <= P) by (clear - FLA1 FP1 FP2 FSZ; unfold hid in FLA1; lia).
cps_seg (sbarm_enh_b usp S P f sf).
destruct POST as (m5b & yb1 & yb2 & -> & HD5 & ARG5b & MU5b & WM5b & MI5b).
pose proof (agree_blocks_of_munch bsegs _ m5 m5b (tl (sb_blocks s S a) ++ LBL) MU5b WM5b
ltac:(intros b x Hb Hx; pose proof (BOUT b x Hb Hx) as H1; clear - H1; cbn [outside]; split; [lia| exact I])) as AG5b.
apply (sb_bufs_agree s S a j m5 m5b) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG5b| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG5b| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG5b HD3 ARG5 OBS5 ACS5 OBP5 APS. unfold sbhd in HD5.
cps_seg_post.

assert (FRSE : rw_cells bsegs m5b sf (sbctl_shadow bF8 bF8)) by exact FRS3. clear FRS3.
chunk_uncons FRB3 as HDF.
cps_seg (sbctl_epi_a usp f sf).
destruct POST as (m6 & -> & MU6 & WM6 & MI6 & FRS6).
pose proof (agree_blocks_of_munch bsegs _ m5b m6 (tl (sb_blocks s S a) ++ LBL) MU6 WM6
ltac:(intros b x Hb Hx; pose proof (BOUT2 b x Hb Hx) as H2; clear - H2; cbn [outside]; repeat split; lia)) as AG6.
apply (sb_bufs_agree s S a j m5b m6) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG6 HDF FRSE FRB3 . unfold sbctl_shadow_dead, bF5 in FRS6. cbn [map repeat] in FRS6.
cps_seg_post.

assert (EF2 : rt_frames RT Σ2 = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRS2; exact FRS1).
assert (EL2 : rt_live RT Σ2 = rt_live RT Σ) by (rewrite LV2; exact LV1).
lazymatch goal with A : X14x.ART RT Σ2 _ |- _ => rename A into ARTX end.
cps_release_intro ARTX EF2 EL2 (fun E : rt_frames RT Σ = [] => eq_trans PO2 (eq_trans PO1 (PNIL E))) Σ3 fl.
assert (FLS : fl < S \/ S + 160 <= fl).
{ destruct (Z_lt_dec fl S) as [L|L]; [left; exact L|]. destruct (Z_le_dec (S + 160) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; left. exists S, 160. split; [exact INL| clear - L G; lia]. }
assert (FLP : fl < fp \/ fp + fs_size kp - 8 <= fl).
{ destruct (Z_lt_dec fl fp) as [L|L]; [left; exact L|]. destruct (Z_le_dec (fp + fs_size kp - 8) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; right; left. exists fp, kp. split; [exact INF| clear - L G; lia]. }
assert (FR6 : rw_cells bsegs m6 (usp + -96) (sbctl_frame (C8 (Z_to_bv 64 f)) s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) by exact FR3. clear FR3.
cps_seg (sbctl_epi_b usp lo f fl).
destruct POST as (m7 & -> & MU7 & WM7 & MI7 & ST7 & FLG7).
assert (AG7 : agree_blocks bsegs m6 m7 (tl (sb_blocks s S a) ++ LBL)).
{ apply (agree_blocks_of_munch bsegs _ m6 m7 _ MU7 WM7). intros b x Hb Hx. cbn [outside]. split; [| exact I]. intros Hfl.
apply NAC. right; right; left. exists (blk_addr b), (blk_size b). split; [| clear - Hx Hfl; lia].
rewrite LV2. apply LIVE1. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; cbn [sb_blocks tl] in Hb |- *; right; exact Hb| right; exact Hb]. }
apply (sb_bufs_agree s S a j m6 m7) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG7 FR6 FRS6.
cps_release_done REL MU7 WM7 FLG7.
apply Hk. exists Σ3. split; [| cbn [dec_depth]; split; [congruence|]; split; [congruence|]; split; [congruence|]; split; [clear - EC CR2 CR1; cbn [dec_depth] in *; lia| congruence]].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m7.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM5]|].
split. { split; [assumption|]. split; [exact MI7|]. split; [cps_wmono| exact ST7]. }
split; [exact PF|].
pose proof (ACCK m7 PF) as ACP7.
cbn [speex_decoder_ctl] in *. destruct (speex_decoder_ctl low (CtlSetEnh v)) as [v' low'] eqn:EC5. cbn [fst snd] in *.
split; [| split; [exists w5; split; [exact ARG5b| exact EQW5]| exact ACP7]].
assert (HDN : rw_cells bsegs m7 S (sbhd MP (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s))
(Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s))
(Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 v))).
{ unfold sbhd. eapply rw_cells_samebytes; [exact HD5| clear; cbn; tauto| cbn [cells_bytes cbytes app]; rewrite (sx32_cell_eqm w5 v EQW5); reflexivity| reflexivity]. }
cbn [decst_rep]. exists a, j, LBL. split; [reflexivity|]. split; [exact S8|]. split; [exact SPOS|]. split; [destruct INV as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12); unfold sb_inv; cbn; repeat split; first [assumption | clear - RV I8 I9 I11; lia]|]. split; [exact JOK|].
split; [change (SBCELLS (set_sbd_lpc_enh_enabled s v) a OUT j) with (sbhd (sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode (sbd_mode s)) (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s)) (Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s)) (Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 v) ++ sbtl s a OUT j); rewrite <- EMP; apply (proj2 (rw_cells_app bsegs m7 S _ _)); split; [exact HDN| exact TL]|].
split; [exact BUFS|]. exists OUTL. exact REP5. }
1: {
destruct PRE3 as (w3 & ARG3).
assert (OBP3 : aobj bsegs m3 P 4) by (split; [lia|]; split; [ulc| exact ACP3]).
assert (APS : P + 4 <= S \/ S + 160 <= P) by (clear - FLA1 FP1 FP2 FSZ; unfold hid in FLA1; lia).
assert (RV : - 2^31 <= sbd_full_frame_size s < 2^31) by (clear - INV; unfold sb_inv in INV; destruct INV as (IM & I1 & I2 & _); destruct IM as [E|E]; rewrite E in *; cbn in I1; lia).
assert (DP0 : (1 <= dec_depth low)%nat) by apply dec_depth_pos.
cps_seg (sbarm_gfs usp S P f sf).
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
assert (FLP : fl < fp \/ fp + fs_size kp - 8 <= fl).
{ destruct (Z_lt_dec fl fp) as [L|L]; [left; exact L|]. destruct (Z_le_dec (fp + fs_size kp - 8) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; right; left. exists fp, kp. split; [exact INF| clear - L G; lia]. }
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
pose proof (ACCK m7 PF) as ACP7.
cbn [speex_decoder_ctl fst snd] in *.
split; [| split; [split; [exact ARG4| exact RV]| exact ACP7]].
cbn [decst_rep]. exists a, j, LBL. split; [reflexivity|]. split; [exact S8|]. split; [exact SPOS|]. split; [exact INV|]. split; [exact JOK|].
split; [rewrite sb_cells_split, <- EMP; apply (proj2 (rw_cells_app bsegs m7 S _ _)); split; [exact HD4| exact TL]|].
split; [exact BUFS|]. exists OUTL. exact RLOW. }
1: {
cps_seg (sbarm_pass_a usp S P f sf).
destruct POST as (ya3 & ya4 & ya5 & ->).
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes bsegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end;
[ eapply (IH Σ1 PMc) with (OUT := OUTL) (STEREO := STEREO) (LBD := LBL) (r := CtlSetHandlerStereo) (P := P) (lo := lo) (fp := fp) (kp := kp); cps_auto | ].
{ rewrite EU. exact ST3. }
intros cc5 (Σ2 & Hc5 & LV2 & FRS2 & SP2 & CR2 & PO2).
destruct (ASTA_unpack RT Σ2 PMc _ cc5 Hc5) as (ms5 & PO5 & Hc5'). clear Hc5. cbv beta in PO5.
destruct PO5 as (m5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5 & REP5 & CP5 & ACP5).
destruct RS5 as (zt0 & zt1 & zt2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & F5 & fc5 & -> & FRM5).
rewrite EU in *. cbn [creq_ivs creq_size app] in PRES5.

xfp PRES5 WM5 OUTB FR3. xfp PRES5 WM5 OUTB FRB3. xfp PRES5 WM5 OUTB FRS3. xfp PRES5 WM5 OUTB HD3. xfp PRES5 WM5 OUTB TL.
assert (AG5 : agree_blocks bsegs m3 m5 (tl (sb_blocks s S a))).
{ apply (agree_blocks_of_pres_fp RT Σ1 _ _ _ m3 m5 _ PRES5 WM5).
- intros b Hb. apply LIVE1. apply in_app_iff. left. cbn [sb_blocks tl] in Hb |- *. right. exact Hb.
- intros b x Hb Hx. split; [| exact (APL b x Hb Hx)].
pose proof (BOUT b x ltac:(apply in_app_iff; left; exact Hb) Hx) as H1. pose proof (BOUT2 b x ltac:(apply in_app_iff; left; exact Hb) Hx) as H2.
clear - H1 H2 FP1 FP2. cbn [fst snd]. lia. }
apply (sb_bufs_agree s S a j m3 m5) in BUFS; [| exact JOK | exact AG5]. clear AG5 RLOW.
assert (PF5 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((P, P + 24) :: (S, S + 160) :: blocks_ivs (tl (sb_blocks s S a) ++ LBL)) m m5).
{ apply (pres_fp_trans _ _ _ _ m m3 m5 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -96) _ m3 m5 PRES5).
- intros e He. rewrite LV1. exact He.
- intros e He. rewrite FRS1. right. exact He.
- lia.
- intros x Hx (O1 & O2 & O3). split; [exact O1| exact (outside_blocks_app_r (tl (sb_blocks s S a)) LBL x O3)]. }
clear PF PRES5. rename PF5 into PF.
cps_sigma LV2 FRS2 SP2.
destruct CP5 as (pad5 & ARG5).
destruct (af_acc_live RT AF Σ2 m5 S 160 ART5 INL) as (_ & ACS5).
assert (OBS5 : aobj bsegs m5 S 160) by (split; [lia|]; split; [ulc| exact ACS5]).
cps_seg (sbarm_pass_b usp S P f sf).
subst ms.
clear OBS5 ACS5. unfold sbhd in HD3.

assert (FRSE : rw_cells bsegs m5 sf (sbctl_shadow bF8 bF8)) by exact FRS3. clear FRS3.
chunk_uncons FRB3 as HDF.
cps_seg (sbctl_epi_a usp f sf).
destruct POST as (m6 & -> & MU6 & WM6 & MI6 & FRS6).
pose proof (agree_blocks_of_munch bsegs _ m5 m6 (tl (sb_blocks s S a) ++ LBL) MU6 WM6
ltac:(intros b x Hb Hx; pose proof (BOUT2 b x Hb Hx) as H2; clear - H2; cbn [outside]; repeat split; lia)) as AG6.
apply (sb_bufs_agree s S a j m5 m6) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG6 HDF FRSE FRB3 . unfold sbctl_shadow_dead, bF5 in FRS6. cbn [map repeat] in FRS6.
cps_seg_post.

assert (EF2 : rt_frames RT Σ2 = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRS2; exact FRS1).
assert (EL2 : rt_live RT Σ2 = rt_live RT Σ) by (rewrite LV2; exact LV1).
lazymatch goal with A : X14x.ART RT Σ2 _ |- _ => rename A into ARTX end.
cps_release_intro ARTX EF2 EL2 (fun E : rt_frames RT Σ = [] => eq_trans PO2 (eq_trans PO1 (PNIL E))) Σ3 fl.
assert (FLS : fl < S \/ S + 160 <= fl).
{ destruct (Z_lt_dec fl S) as [L|L]; [left; exact L|]. destruct (Z_le_dec (S + 160) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; left. exists S, 160. split; [exact INL| clear - L G; lia]. }
assert (FLP : fl < fp \/ fp + fs_size kp - 8 <= fl).
{ destruct (Z_lt_dec fl fp) as [L|L]; [left; exact L|]. destruct (Z_le_dec (fp + fs_size kp - 8) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; right; left. exists fp, kp. split; [exact INF| clear - L G; lia]. }
assert (FR6 : rw_cells bsegs m6 (usp + -96) (sbctl_frame (C8 (Z_to_bv 64 f)) s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) by exact FR3. clear FR3.
cps_seg (sbctl_epi_b usp lo f fl).
destruct POST as (m7 & -> & MU7 & WM7 & MI7 & ST7 & FLG7).
assert (AG7 : agree_blocks bsegs m6 m7 (tl (sb_blocks s S a) ++ LBL)).
{ apply (agree_blocks_of_munch bsegs _ m6 m7 _ MU7 WM7). intros b x Hb Hx. cbn [outside]. split; [| exact I]. intros Hfl.
apply NAC. right; right; left. exists (blk_addr b), (blk_size b). split; [| clear - Hx Hfl; lia].
rewrite LV2. apply LIVE1. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; cbn [sb_blocks tl] in Hb |- *; right; exact Hb| right; exact Hb]. }
apply (sb_bufs_agree s S a j m6 m7) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG7 FR6 FRS6.
cps_release_done REL MU7 WM7 FLG7.
apply Hk. exists Σ3. split; [| cbn [dec_depth]; split; [congruence|]; split; [congruence|]; split; [congruence|]; split; [clear - EC CR2 CR1; cbn [dec_depth] in *; lia| congruence]].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m7.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM5]|].
split. { split; [assumption|]. split; [exact MI7|]. split; [cps_wmono| exact ST7]. }
split; [exact PF|].
pose proof (ACCK m7 PF) as ACP7.
cbn [speex_decoder_ctl] in *. destruct (speex_decoder_ctl low CtlSetHandlerStereo) as [v' low'] eqn:EC5. cbn [fst snd] in *.
split; [| split; [exists pad5; exact ARG5| exact ACP7]].
cbn [decst_rep]. exists a, j, LBL. split; [reflexivity|]. split; [exact S8|]. split; [exact SPOS|]. split; [exact INV|]. split; [exact JOK|].
split; [rewrite sb_cells_split, <- EMP; apply (proj2 (rw_cells_app bsegs m7 S _ _)); split; [exact HD3| exact TL]|].
split; [exact BUFS|]. exists OUTL. exact REP5. }
1: {
destruct PRE3 as (w3 & ARG3).
assert (OBP3 : aobj bsegs m3 P 4) by (split; [lia|]; split; [ulc| exact ACP3]).
assert (APS : P + 4 <= S \/ S + 160 <= P) by (clear - FLA1 FP1 FP2 FSZ; unfold hid in FLA1; lia).
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
assert (FLP : fl < fp \/ fp + fs_size kp - 8 <= fl).
{ destruct (Z_lt_dec fl fp) as [L|L]; [left; exact L|]. destruct (Z_le_dec (fp + fs_size kp - 8) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; right; left. exists fp, kp. split; [exact INF| clear - L G; lia]. }
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
pose proof (ACCK m7 PF) as ACP7.
cbn [speex_decoder_ctl fst snd] in *.
split; [| split; [split; [exact ARG4| exact RV]| exact ACP7]].
cbn [decst_rep]. exists a, j, LBL. split; [reflexivity|]. split; [exact S8|]. split; [exact SPOS|]. split; [exact INV|]. split; [exact JOK|].
split; [rewrite sb_cells_split, <- EMP; apply (proj2 (rw_cells_app bsegs m7 S _ _)); split; [exact HD4| exact TL]|].
split; [exact BUFS|]. exists OUTL. exact RLOW. }
1: {
cps_seg (sbarm_pass_a usp S P f sf).
destruct POST as (ya3 & ya4 & ya5 & ->).
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes bsegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end;
[ eapply (IH Σ1 PMc) with (OUT := OUTL) (STEREO := STEREO) (LBD := LBL) (r := CtlGetLookahead) (P := P) (lo := lo) (fp := fp) (kp := kp); cps_auto | ].
{ rewrite EU. exact ST3. }
intros cc5 (Σ2 & Hc5 & LV2 & FRS2 & SP2 & CR2 & PO2).
destruct (ASTA_unpack RT Σ2 PMc _ cc5 Hc5) as (ms5 & PO5 & Hc5'). clear Hc5. cbv beta in PO5.
destruct PO5 as (m5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5 & REP5 & CP5 & ACP5).
destruct RS5 as (zt0 & zt1 & zt2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & F5 & fc5 & -> & FRM5).
rewrite EU in *. cbn [creq_ivs creq_size app] in PRES5.

xfp PRES5 WM5 OUTB FR3. xfp PRES5 WM5 OUTB FRB3. xfp PRES5 WM5 OUTB FRS3. xfp PRES5 WM5 OUTB HD3. xfp PRES5 WM5 OUTB TL.
assert (AG5 : agree_blocks bsegs m3 m5 (tl (sb_blocks s S a))).
{ apply (agree_blocks_of_pres_fp RT Σ1 _ _ _ m3 m5 _ PRES5 WM5).
- intros b Hb. apply LIVE1. apply in_app_iff. left. cbn [sb_blocks tl] in Hb |- *. right. exact Hb.
- intros b x Hb Hx. split; [| exact (APL b x Hb Hx)].
pose proof (BOUT b x ltac:(apply in_app_iff; left; exact Hb) Hx) as H1. pose proof (BOUT2 b x ltac:(apply in_app_iff; left; exact Hb) Hx) as H2.
clear - H1 H2 FP1 FP2. cbn [fst snd]. lia. }
apply (sb_bufs_agree s S a j m3 m5) in BUFS; [| exact JOK | exact AG5]. clear AG5 RLOW.
assert (PF5 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((P, P + 4) :: (S, S + 160) :: blocks_ivs (tl (sb_blocks s S a) ++ LBL)) m m5).
{ apply (pres_fp_trans _ _ _ _ m m3 m5 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -96) _ m3 m5 PRES5).
- intros e He. rewrite LV1. exact He.
- intros e He. rewrite FRS1. right. exact He.
- lia.
- intros x Hx (O1 & O2 & O3). split; [exact O1| exact (outside_blocks_app_r (tl (sb_blocks s S a)) LBL x O3)]. }
clear PF PRES5. rename PF5 into PF.
cps_sigma LV2 FRS2 SP2.
destruct CP5 as (ARG5 & RV5).
destruct (af_acc_live RT AF Σ2 m5 S 160 ART5 INL) as (_ & ACS5).
assert (OBS5 : aobj bsegs m5 S 160) by (split; [lia|]; split; [ulc| exact ACS5]).
assert (OBP5 : aobj bsegs m5 P 4) by (split; [lia|]; split; [ulc| exact ACP5]).
assert (RV30 : - 2^30 <= fst (speex_decoder_ctl low CtlGetLookahead) < 2^30)
by (pose proof (lookahead_val low ltac:(clear - DEP; lia)) as LV; clear - LV; lia).
cps_seg (sbarm_gla_b usp S P f sf).
destruct POST as (m5b & yb1 & yb2 & ys8 & -> & ARG5b & MU5b & WM5b & MI5b).
pose proof (agree_blocks_of_munch bsegs _ m5 m5b (tl (sb_blocks s S a) ++ LBL) MU5b WM5b
ltac:(intros b x Hb Hx; pose proof (BOUT b x Hb Hx) as H1; clear - H1 FP1 FP2; cbn [outside]; split; [lia| exact I])) as AG5b.
apply (sb_bufs_agree s S a j m5 m5b) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG5b| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG5b| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG5b ARG5 OBS5 ACS5 OBP5. unfold sbhd in HD3.
cps_seg_post.

assert (FRSE : rw_cells bsegs m5b sf (sbctl_shadow bF8 bF8)) by exact FRS3. clear FRS3.
chunk_uncons FRB3 as HDF.
cps_seg (sbctl_epi_a usp f sf).
destruct POST as (m6 & -> & MU6 & WM6 & MI6 & FRS6).
pose proof (agree_blocks_of_munch bsegs _ m5b m6 (tl (sb_blocks s S a) ++ LBL) MU6 WM6
ltac:(intros b x Hb Hx; pose proof (BOUT2 b x Hb Hx) as H2; clear - H2; cbn [outside]; repeat split; lia)) as AG6.
apply (sb_bufs_agree s S a j m5b m6) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG6 HDF FRSE FRB3 . unfold sbctl_shadow_dead, bF5 in FRS6. cbn [map repeat] in FRS6.
cps_seg_post.

assert (EF2 : rt_frames RT Σ2 = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRS2; exact FRS1).
assert (EL2 : rt_live RT Σ2 = rt_live RT Σ) by (rewrite LV2; exact LV1).
lazymatch goal with A : X14x.ART RT Σ2 _ |- _ => rename A into ARTX end.
cps_release_intro ARTX EF2 EL2 (fun E : rt_frames RT Σ = [] => eq_trans PO2 (eq_trans PO1 (PNIL E))) Σ3 fl.
assert (FLS : fl < S \/ S + 160 <= fl).
{ destruct (Z_lt_dec fl S) as [L|L]; [left; exact L|]. destruct (Z_le_dec (S + 160) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; left. exists S, 160. split; [exact INL| clear - L G; lia]. }
assert (FLP : fl < fp \/ fp + fs_size kp - 8 <= fl).
{ destruct (Z_lt_dec fl fp) as [L|L]; [left; exact L|]. destruct (Z_le_dec (fp + fs_size kp - 8) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; right; left. exists fp, kp. split; [exact INF| clear - L G; lia]. }
assert (FR6 : rw_cells bsegs m6 (usp + -96) (sbctl_frame (C8 (Z_to_bv 64 f)) s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) by exact FR3. clear FR3.
cps_seg (sbctl_epi_b usp lo f fl).
destruct POST as (m7 & -> & MU7 & WM7 & MI7 & ST7 & FLG7).
assert (AG7 : agree_blocks bsegs m6 m7 (tl (sb_blocks s S a) ++ LBL)).
{ apply (agree_blocks_of_munch bsegs _ m6 m7 _ MU7 WM7). intros b x Hb Hx. cbn [outside]. split; [| exact I]. intros Hfl.
apply NAC. right; right; left. exists (blk_addr b), (blk_size b). split; [| clear - Hx Hfl; lia].
rewrite LV2. apply LIVE1. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; cbn [sb_blocks tl] in Hb |- *; right; exact Hb| right; exact Hb]. }
apply (sb_bufs_agree s S a j m6 m7) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG7 FR6 FRS6.
cps_release_done REL MU7 WM7 FLG7.
apply Hk. exists Σ3. split; [| cbn [dec_depth]; split; [congruence|]; split; [congruence|]; split; [congruence|]; split; [clear - EC CR2 CR1; cbn [dec_depth] in *; lia| congruence]].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m7.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM5]|].
split. { split; [assumption|]. split; [exact MI7|]. split; [cps_wmono| exact ST7]. }
split; [exact PF|].
pose proof (ACCK m7 PF) as ACP7.
cbn [speex_decoder_ctl] in *. destruct (speex_decoder_ctl low CtlGetLookahead) as [vl low'] eqn:EC5. cbn [fst snd] in *.
split; [| split; [split; [exact ARG5b| clear - RV30; lia]| exact ACP7]].
cbn [decst_rep]. exists a, j, LBL. split; [reflexivity|]. split; [exact S8|]. split; [exact SPOS|]. split; [exact INV|]. split; [exact JOK|].
split; [rewrite sb_cells_split, <- EMP; apply (proj2 (rw_cells_app bsegs m7 S _ _)); split; [exact HD3| exact TL]|].
split; [exact BUFS|]. exists OUTL. exact REP5. }
1: {
cps_seg (sbarm_pass_a usp S P f sf).
destruct POST as (ya3 & ya4 & ya5 & ->).
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes bsegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end;
[ eapply (IH Σ1 PMc) with (OUT := OUTL) (STEREO := STEREO) (LBD := LBL) (r := (CtlSetWideband v)) (P := P) (lo := lo) (fp := fp) (kp := kp); cps_auto | ].
{ rewrite EU. exact ST3. }
intros cc5 (Σ2 & Hc5 & LV2 & FRS2 & SP2 & CR2 & PO2).
destruct (ASTA_unpack RT Σ2 PMc _ cc5 Hc5) as (ms5 & PO5 & Hc5'). clear Hc5. cbv beta in PO5.
destruct PO5 as (m5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5 & REP5 & CP5 & ACP5).
destruct RS5 as (zt0 & zt1 & zt2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & F5 & fc5 & -> & FRM5).
rewrite EU in *. cbn [creq_ivs creq_size app] in PRES5.

xfp PRES5 WM5 OUTB FR3. xfp PRES5 WM5 OUTB FRB3. xfp PRES5 WM5 OUTB FRS3. xfp PRES5 WM5 OUTB HD3. xfp PRES5 WM5 OUTB TL.
assert (AG5 : agree_blocks bsegs m3 m5 (tl (sb_blocks s S a))).
{ apply (agree_blocks_of_pres_fp RT Σ1 _ _ _ m3 m5 _ PRES5 WM5).
- intros b Hb. apply LIVE1. apply in_app_iff. left. cbn [sb_blocks tl] in Hb |- *. right. exact Hb.
- intros b x Hb Hx. split; [| exact (APL b x Hb Hx)].
pose proof (BOUT b x ltac:(apply in_app_iff; left; exact Hb) Hx) as H1. pose proof (BOUT2 b x ltac:(apply in_app_iff; left; exact Hb) Hx) as H2.
clear - H1 H2 FP1 FP2. cbn [fst snd]. lia. }
apply (sb_bufs_agree s S a j m3 m5) in BUFS; [| exact JOK | exact AG5]. clear AG5 RLOW.
assert (PF5 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((P, P + 4) :: (S, S + 160) :: blocks_ivs (tl (sb_blocks s S a) ++ LBL)) m m5).
{ apply (pres_fp_trans _ _ _ _ m m3 m5 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -96) _ m3 m5 PRES5).
- intros e He. rewrite LV1. exact He.
- intros e He. rewrite FRS1. right. exact He.
- lia.
- intros x Hx (O1 & O2 & O3). split; [exact O1| exact (outside_blocks_app_r (tl (sb_blocks s S a)) LBL x O3)]. }
clear PF PRES5. rename PF5 into PF.
cps_sigma LV2 FRS2 SP2.
destruct CP5 as (w5 & ARG5 & EQW5).
destruct (af_acc_live RT AF Σ2 m5 S 160 ART5 INL) as (_ & ACS5).
assert (OBS5 : aobj bsegs m5 S 160) by (split; [lia|]; split; [ulc| exact ACS5]).
cps_seg (sbarm_pass_b usp S P f sf).
subst ms.
clear OBS5 ACS5. unfold sbhd in HD3.

assert (FRSE : rw_cells bsegs m5 sf (sbctl_shadow bF8 bF8)) by exact FRS3. clear FRS3.
chunk_uncons FRB3 as HDF.
cps_seg (sbctl_epi_a usp f sf).
destruct POST as (m6 & -> & MU6 & WM6 & MI6 & FRS6).
pose proof (agree_blocks_of_munch bsegs _ m5 m6 (tl (sb_blocks s S a) ++ LBL) MU6 WM6
ltac:(intros b x Hb Hx; pose proof (BOUT2 b x Hb Hx) as H2; clear - H2; cbn [outside]; repeat split; lia)) as AG6.
apply (sb_bufs_agree s S a j m5 m6) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG6 HDF FRSE FRB3 . unfold sbctl_shadow_dead, bF5 in FRS6. cbn [map repeat] in FRS6.
cps_seg_post.

assert (EF2 : rt_frames RT Σ2 = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRS2; exact FRS1).
assert (EL2 : rt_live RT Σ2 = rt_live RT Σ) by (rewrite LV2; exact LV1).
lazymatch goal with A : X14x.ART RT Σ2 _ |- _ => rename A into ARTX end.
cps_release_intro ARTX EF2 EL2 (fun E : rt_frames RT Σ = [] => eq_trans PO2 (eq_trans PO1 (PNIL E))) Σ3 fl.
assert (FLS : fl < S \/ S + 160 <= fl).
{ destruct (Z_lt_dec fl S) as [L|L]; [left; exact L|]. destruct (Z_le_dec (S + 160) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; left. exists S, 160. split; [exact INL| clear - L G; lia]. }
assert (FLP : fl < fp \/ fp + fs_size kp - 8 <= fl).
{ destruct (Z_lt_dec fl fp) as [L|L]; [left; exact L|]. destruct (Z_le_dec (fp + fs_size kp - 8) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; right; left. exists fp, kp. split; [exact INF| clear - L G; lia]. }
assert (FR6 : rw_cells bsegs m6 (usp + -96) (sbctl_frame (C8 (Z_to_bv 64 f)) s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) by exact FR3. clear FR3.
cps_seg (sbctl_epi_b usp lo f fl).
destruct POST as (m7 & -> & MU7 & WM7 & MI7 & ST7 & FLG7).
assert (AG7 : agree_blocks bsegs m6 m7 (tl (sb_blocks s S a) ++ LBL)).
{ apply (agree_blocks_of_munch bsegs _ m6 m7 _ MU7 WM7). intros b x Hb Hx. cbn [outside]. split; [| exact I]. intros Hfl.
apply NAC. right; right; left. exists (blk_addr b), (blk_size b). split; [| clear - Hx Hfl; lia].
rewrite LV2. apply LIVE1. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; cbn [sb_blocks tl] in Hb |- *; right; exact Hb| right; exact Hb]. }
apply (sb_bufs_agree s S a j m6 m7) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG7 FR6 FRS6.
cps_release_done REL MU7 WM7 FLG7.
apply Hk. exists Σ3. split; [| cbn [dec_depth]; split; [congruence|]; split; [congruence|]; split; [congruence|]; split; [clear - EC CR2 CR1; cbn [dec_depth] in *; lia| congruence]].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m7.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM5]|].
split. { split; [assumption|]. split; [exact MI7|]. split; [cps_wmono| exact ST7]. }
split; [exact PF|].
pose proof (ACCK m7 PF) as ACP7.
cbn [speex_decoder_ctl] in *. destruct (speex_decoder_ctl low (CtlSetWideband v)) as [v' low'] eqn:EC5. cbn [fst snd] in *.
split; [| split; [exists w5; split; [exact ARG5| exact EQW5]| exact ACP7]].
cbn [decst_rep]. exists a, j, LBL. split; [reflexivity|]. split; [exact S8|]. split; [exact SPOS|]. split; [exact INV|]. split; [exact JOK|].
split; [rewrite sb_cells_split, <- EMP; apply (proj2 (rw_cells_app bsegs m7 S _ _)); split; [exact HD3| exact TL]|].
split; [exact BUFS|]. exists OUTL. exact REP5. }
Qed.

Theorem ctl_cps_all : forall d, ctl_cps_at RT d.
Proof using AF SM0 AF_LIB.
induction d as [st|s low IH]; [exact (ctl_cps_nb RT AF AF_LIB st)| exact (ctl_cps_sb s low IH)].
Qed.
End CtlSB.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma sb_bufs_agree : forall (s : sbd_state bptr) S a j (m m' : mem),
sb_bufs asegs m a j -> sb_junk_ok s j -> agree_blocks asegs m m' (tl (sb_blocks s S a)) -> sb_bufs asegs m' a j.
Proof.
intros s S a j m m' (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7) (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10) AG.
unfold sb_bufs. repeat match goal with |- _ /\ _ => split end;
(eapply rw_cells_agree_at; [eassumption|]);
[ eapply (agree_blocks_at asegs m m' _ (sbd_g0_mem s, a_g0 a, 256)) | eapply (agree_blocks_at asegs m m' _ (sbd_g1_mem s, a_g1 a, 256))
| eapply (agree_blocks_at asegs m m' _ (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s))
| eapply (agree_blocks_at asegs m m' _ (sbd_old_qlsp s, a_oq a, 32)) | eapply (agree_blocks_at asegs m m' _ (sbd_interp_qlpc s, a_iq a, 32))
| eapply (agree_blocks_at asegs m m' _ (sbd_mem_sp s, a_msp a, 64))
| eapply (agree_blocks_at asegs m m' _ (sbd_pi_gain s, a_pg a, 16)) | eapply (agree_blocks_at asegs m m' _ (sbd_exc_rms s, a_er a, 16)) ];
try exact AG; try eassumption;
try (cbn; tauto); unfold blk_addr, blk_size; cbn [fst snd]; rewrite ?cells_size_f32; lia.
Qed.

Lemma agree_blocks_app : forall (m m' : mem) L1 L2, agree_blocks asegs m m' L1 -> agree_blocks asegs m m' L2 -> agree_blocks asegs m m' (L1 ++ L2).
Proof.
intros m m' L1 L2 A1 A2 x Hx (b & Hb & Hab). apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [apply A1| apply A2]; try exact Hx; exists b; split; assumption.
Qed.

Section Blocks.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Lemma live_apart : forall (Σ : rts RT) (m : mem) p1 n1 p2 n2, ART RT Σ m -> In (p1, n1) (rt_live RT Σ) -> In (p2, n2) (rt_live RT Σ) -> p1 <> p2 ->
p1 + n1 <= p2 \/ p2 + n2 <= p1.
Proof using AF.
intros Σ m p1 n1 p2 n2 ART0 H1 H2 NE. destruct (in_split _ _ H1) as (l1 & l2 & E).
apply (af_live_disj RT AF Σ m p1 n1 p2 n2 l1 l2 ART0 E). rewrite E in H2. apply in_app_iff in H2. apply in_app_iff.
destruct H2 as [H2|[H2|H2]]; [left; exact H2| exfalso; apply NE; congruence| right; exact H2].
Qed.

Definition blocks_in_live (Σ : rts RT) (L : list block) : Prop := forall b, In b L -> In (blk_addr b, blk_size b) (rt_live RT Σ).

Lemma agree_blocks_of_pres : forall (Σ : rts RT) frames sp (m m' : mem) L,
rt_pres (rt_live RT Σ) frames sp m m' -> wmono asegs m m' -> blocks_in_live Σ L -> agree_blocks asegs m m' L.
Proof.
intros Σ frames sp m m' L PRES WM BL x Hx (b & Hb & Hab). split; [| apply WM].
apply PRES. rewrite wa_unsigned by lia. right; right; left. exists (blk_addr b), (blk_size b). split; [exact (BL b Hb)| exact Hab].
Qed.

Lemma agree_blocks_of_pres_fp : forall (Σ : rts RT) frames sp W (m m' : mem) L,
rt_pres_fp (rt_live RT Σ) frames sp W m m' -> wmono asegs m m' -> blocks_in_live Σ L ->
(forall b x, In b L -> blk_addr b <= x < blk_addr b + blk_size b -> outside W x) -> agree_blocks asegs m m' L.
Proof.
intros Σ frames sp W m m' L PRES WM BL OUT x Hx (b & Hb & Hab). split; [| apply WM].
apply PRES; rewrite wa_unsigned by lia; [| exact (OUT b x Hb Hab)].
right; right; left. exists (blk_addr b), (blk_size b). split; [exact (BL b Hb)| exact Hab].
Qed.

Lemma outside_blocks_shadow : forall (Σ : rts RT) (m : mem) L x, ART RT Σ m -> blocks_in_live Σ L -> SH_LO <= x < SH_HI -> outside (blocks_ivs L) x.
Proof using AF.
intros Σ m L x ART0 BL Hx. apply outside_blocks_ivs. intros b Hb Hin.
pose proof (af_live_offshadow RT AF Σ m _ _ ART0 (BL b Hb)) as O. unfold SH_LO, SH_HI in Hx. lia.
Qed.

Lemma outside_blocks_app_r : forall L1 L2 x, outside (blocks_ivs (L1 ++ L2)) x -> outside (blocks_ivs L2) x.
Proof. intros L1 L2 x H. apply outside_blocks_ivs. intros b Hb. apply (proj1 (outside_blocks_ivs _ _) H). apply in_app_iff. right. exact Hb. Qed.
Lemma outside_blocks_app_l : forall L1 L2 x, outside (blocks_ivs (L1 ++ L2)) x -> outside (blocks_ivs L1) x.
Proof. intros L1 L2 x H. apply outside_blocks_ivs. intros b Hb. apply (proj1 (outside_blocks_ivs _ _) H). apply in_app_iff. left. exact Hb. Qed.

Lemma acc_of_pres_fp : forall (Σ : rts RT) (m0 m m' : mem) sp W fp kp P n,
ART RT Σ m0 -> In (fp, kp) (rt_frames RT Σ) -> fp <= P -> P + n <= fp + fs_size kp - 8 ->
rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) sp W m m' -> (forall x, SH_LO <= x < SH_HI -> outside W x) ->
acc asegs m P n -> acc asegs m' P n.
Proof using AF.
intros Σ m0 m m' sp W fp kp P n ART0 INF F1 F2 PRES OFF ACC i Hi. destruct (ACC i Hi) as (b & B & OK). exists b. split; [| exact OK].
pose proof (frame_facts RT AF Σ m0 fp kp ART0 INF) as (FP0 & FP64 & _ & _ & _ & _ & SA & S1 & S2 & _).
assert (FSZ : 0 <= fs_size kp) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (R : shad fp <= shad (P + i) < shad (fp + fs_size kp)).
{ unfold shad. split; [assert (fp / 8 <= (P + i) / 8) by (apply Z.div_le_mono; lia); lia|].
assert ((P + i) / 8 < (fp + fs_size kp) / 8); [| lia].
assert (E8 : (fp + fs_size kp) mod 8 = 0).
{ unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. clear - FP64. set (q := 2 ^ Z.of_nat kp). assert (fp mod 8 = 0) by (Z.div_mod_to_equations; lia).
rewrite Z.add_mod, H by lia. change 64 with (8 * 8). rewrite <- Z.mul_assoc, Z.mul_comm, Z.mod_mul by lia. reflexivity. }
clear - E8 F2 Hi. Z.div_mod_to_equations. lia. }
apply (bytes_at_agree asegs m m' _ _ B). intros a Ha. cbn [length] in Ha.
apply PRES; [right; right; right; right; exists fp, kp; split; [exact INF| lia]|].
apply OFF. rewrite SA in R. lia.
Qed.

Lemma lbd_apart_live : forall (Σ : rts RT) (m : mem) L, ART RT Σ m -> blocks_in_live Σ L -> lbd_apart L.
Proof using AF.
intros Σ m L ART0 BL b1 b2 H1 H2 NE. apply (live_apart Σ m _ _ _ _ ART0 (BL b1 H1) (BL b2 H2)). exact NE.
Qed.
End Blocks.

Definition sbtl (s : sbd_state bptr) (a : sb_addrs) (OUT : Z) (j : sb_junk) : list cell :=
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (a_g0 a)); C8 (Z_to_bv 64 (a_g1 a)); C8 (Z_to_bv 64 (a_exc a));
C8 (Z_to_bv 64 (a_oq a)); C8 (Z_to_bv 64 (a_iq a)); C8 (Z_to_bv 64 (a_msp a)); C8 (Z_to_bv 64 (a_pg a)); C8 (Z_to_bv 64 (a_er a));
C8 (Z_to_bv 64 (sb_isave_ptr OUT s)); C4 (sj_last_ener j); C4 (sj_seed j); C4 (Z_to_bv 64 (sbd_encode_submode s)); CB 4 (sj_pad1 j);
C8 (Z_to_bv 64 (sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR (sbd_mode s))); C4 (Z_to_bv 64 (sbd_submodeID s)); CB 4 (sj_pad2 j)].

Lemma sb_cells_split : forall s a OUT j,
SBCELLS s a OUT j = sbhd (sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode (sbd_mode s)) (a_low a)
(Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s))
(Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s))
(Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 (sbd_lpc_enh_enabled s)) ++ sbtl s a OUT j.
Proof. reflexivity. Qed.

Ltac piece X P :=
lazymatch type of X with
| rw_cells ?segs ?m ?A (?cs1 ++ ?cs2) =>
let n := eval vm_compute in (Z.of_nat (cells_size cs1)) in
apply (proj1 (rw_cells_app segs m A cs1 cs2)) in X; destruct X as [P X];
change (Z.of_nat (cells_size cs1)) with n in X;
repeat match type of X with rw_cells _ _ (?B + ?a + ?b) _ => let v := eval vm_compute in (a + b) in replace (B + a + b) with (B + v) in X by lia end
end.

Lemma NoDup_app_in_neq {A} (l1 l2 : list A) x y : List.NoDup (l1 ++ l2) -> In x l1 -> In y l2 -> x <> y.
Proof.
intros ND H1 H2 ->. induction l1 as [|z l1 IH]; [destruct H1|].
cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND]. destruct H1 as [->|H1].
- apply NI. apply in_app_iff. right. exact H2.
- exact (IH ND H1).
Qed.

Ltac xfp PRES WM OUTB H :=
lazymatch type of PRES with
| rt_pres_fp ?live ?frames ?sp ?W ?m ?m' =>
lazymatch type of H with
| rw_cells asegs m ?A ?cs =>
let H' := fresh "T" in
assert (H' : rw_cells asegs m' A cs)
by (apply (rw_cells_agree asegs m m' A cs H);
[ apply (agree_of_pres_fp live frames sp W m m' _ PRES); intros ? ?Hx; cps_sizes Hx;
split; [ aclient_tac ltac:(ulc) | cbn [outside]; split; [ ulc | apply OUTB; ulc ] ]
| exact WM ]);
clear H; rename H' into H
end
end.

Lemma lookahead_val : forall d : dec_state bptr, (dec_depth d <= 3)%nat ->
fst (speex_decoder_ctl d CtlGetLookahead) = 40 \/ fst (speex_decoder_ctl d CtlGetLookahead) = 80 \/ fst (speex_decoder_ctl d CtlGetLookahead) = 160.
Proof.
intros d Hd. destruct d as [st|s1 [st|s2 [st|s3 low]]].
1-3: cbn -[Z.mul]; unfold NB_SUBFRAME_SIZE; lia.
exfalso. cbn [dec_depth] in Hd. pose proof (dec_depth_pos low). lia.
Qed.

Lemma creq_pre_agree : forall STEREO (m m' : mem) S S' d d' P r, creq_grp1 r = true ->
creq_pre STEREO m S d P r -> agree_at asegs m m' P (creq_size r) -> creq_pre STEREO m' S' d' P r.
Proof.
intros STEREO m m' S S' d d' P r G PRE AG. destruct r; try discriminate G; cbn [creq_pre creq_size] in *.
- destruct PRE as (w & X & E). exists w. split; [| exact E]. exact (rw_cells_agree_at asegs m m' P _ X AG).
- destruct PRE as (w & X). exists w. exact (rw_cells_agree_at asegs m m' P _ X AG).
- destruct PRE as (w & X). exists w. exact (rw_cells_agree_at asegs m m' P _ X AG).
- destruct PRE as (w & X & E). exists w. split; [| exact E]. exact (rw_cells_agree_at asegs m m' P _ X AG).
- destruct PRE as (w & X). exists w. exact (rw_cells_agree_at asegs m m' P _ X AG).
- destruct PRE as (w & X). exists w. exact (rw_cells_agree_at asegs m m' P _ X AG).
- destruct PRE as (w & X & E). exists w. split; [| exact E]. exact (rw_cells_agree_at asegs m m' P _ X AG).
Qed.

Lemma agree_at_of_pres_fp : forall live frames sp W (m m' : mem) A n,
rt_pres_fp live frames sp W m m' -> wmono asegs m m' -> 0 <= A -> A + n <= 2^64 ->
(forall x, A <= x < A + n -> aclient live frames sp x /\ outside W x) -> agree_at asegs m m' A n.
Proof.
intros live frames sp W m m' A n PRES WM A0 AN H a Ha. split; [| apply WM]. destruct (H a Ha) as [H1 H2].
apply PRES; rewrite wa_unsigned by lia; assumption.
Qed.

Section CtlSB.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.

Theorem ctl_cps_sb : forall s low, ctl_cps_at RT low -> ctl_cps_at RT (DecSB s low).
Proof using AF SM0 AF_LIB.
intros s low IH Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
OUT STEREO S LBD r P lo fp kp FDO MST -> -> -> -> GRP REP DEP ND OK PRE LIVE INF FP1 FP2 ACP PAL FRM CRD ART0 MI0 FRM0 ST0 LOW LOR SPT SPA.
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

destruct (frame_below_lo RT AF Σ m fp kp lo ART0 INF LOW) as (BF1 & BF2 & _).
pose proof (frame_facts RT AF Σ m fp kp ART0 INF) as (FP0 & FP64 & FPIMG & _ & FPHI & _ & _ & _ & _ & _).
destruct (frame_live_apart RT AF Σ m fp kp S 160 ART0 INF INL) as (FLA1 & _).
assert (FSZ : 0 <= fs_size kp) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
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
destruct (frame_live_apart RT AF Σ m fp kp _ _ ART0 INF (LIVE b Hb)) as (B2 & _). clear - B2 Hx Hin FP1 FP2. lia. }

assert (OFFW : forall x, SH_LO <= x < SH_HI -> outside ((P, P + creq_size r) :: blocks_ivs LBD) x).
{ intros x Hx. split; [clear - Hx FPHI FP2 FSZ FP1; unfold SH_LO, SH_HI in Hx; cbn [fst snd]; lia| exact (outside_blocks_shadow RT AF Σ m LBD x ART0 LIVE0 Hx)]. }
pose proof (fun m' (PR : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((P, P + creq_size r) :: blocks_ivs LBD) m m') =>
acc_of_pres_fp RT AF Σ m m m' usp _ fp kp P (creq_size r) ART0 INF FP1 FP2 PR OFFW ACP) as ACCK.
assert (PR0 : 0 <= P) by lia.
assert (PR1 : P + creq_size r <= 2^64) by (clear - FP2 BF1 LOR SPT CSP; unfold RT_STACK, USTACK_TOP in *; lia).
assert (PCL : forall x, P <= x < P + creq_size r -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x)
by (intros x Hx; right; right; right; left; exists fp, kp; split; [exact INF| lia]).
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
x < lo /\ (x < S \/ S + 160 <= x) /\ (x < fp \/ fp + fs_size kp <= x)).
{ intros b x Hb Hx.
assert (Hb' : In b LBD) by (rewrite ELBD; cbn [sb_blocks tl app] in Hb |- *; right; exact Hb).
pose proof (LIVE b Hb') as LB.
destruct (live_below_lo RT AF Σ m _ _ lo ART0 LB LOW) as (_ & B1 & _).
destruct (frame_live_apart RT AF Σ m fp kp _ _ ART0 INF LB) as (B2 & _).
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
destruct (frame_live_apart RT AF Σ1 m2 f 0%nat _ _ ART2 INF0 (LIVE1 b Hb')) as (B2 & B3).
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
pose proof (ACCK m3 PF) as ACP3.
assert (OUTB : forall x, (lo <= x \/ (S <= x < S + 160) \/ (fp <= x < fp + fs_size kp) \/ (f <= x < f + 64) \/ (sf <= x < sf + 8)) -> outside (blocks_ivs LBL) x).
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
destruct r; try discriminate GRP; cbn [ctl_req_code creq_size creq_align] in *.
4: {
destruct PRE3 as (w3 & ARG3 & EQW & RV).
assert (OBP3 : aobj asegs m3 P 4) by (split; [lia|]; split; [ulc| exact ACP3]).
assert (APS : P + 4 <= S \/ S + 160 <= P) by (clear - FLA1 FP1 FP2 FSZ; unfold hid in FLA1; lia).
assert (SFA : S + 160 <= f \/ f + 64 <= S) by (clear - FLA; unfold hid in FLA; lia).
assert (PFA4 : P + 4 <= f \/ f + 64 <= P) by (clear - PFA; unfold hid in PFA; lia).
assert (POFF : P + 4 <= SH_LO \/ SH_HI <= P) by (clear - FPHI FP1 FP2 FSZ; unfold hid in FPHI; unfold SH_LO, SH_HI; lia).
assert (FSH : f + 64 <= SH_LO \/ SH_HI <= f) by (clear - FHI; unfold hid in FHI; unfold SH_LO, SH_HI; lia).
assert (FTOP' : f + 64 <= APP_TOP) by (clear - FTOP; unfold APP_TOP; lia).
assert (FRSa : rw_cells asegs m3 sf (sbctl_shadow bF8 bF8)) by exact FRS3. clear FRS3. cps_hide.
apply (proj1 (rw_cells_app asegs m3 f [_; _; _; _; _; _; _] [_; _])) in FRB3. destruct FRB3 as [FB0 FB1].
change (Z.of_nat (cells_size _)) with 48 in FB1. chunk_uncons FB1 as TMP3. replace (f + 48 + 4) with (f + 52) in FB1 by lia.
cps_seg (sbarm_ssr_a usp S P f sf).
destruct POST as (m4 & yc3 & yc4 & yc5 & tw & -> & HD4 & ARG4 & TMP4 & ETW & FRS4 & MU4 & WM4 & MI4).
pose proof (agree_blocks_of_munch asegs _ m3 m4 (tl (sb_blocks s S a) ++ LBL) MU4 WM4
ltac:(intros b x Hb Hx; pose proof (BOUT b x Hb Hx) as H1; pose proof (BOUT2 b x Hb Hx) as H2; clear - H1 H2; cbn [outside]; repeat split; lia)) as AG4.
apply (sb_bufs_agree s S a j m3 m4) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG4| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG4| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG4 HD3 ARG3 TMP3 FRSa OBP3. unfold sbhd in HD4. unfold sbctl_shadow, bF1, bF3, bF8 in FRS4.
cps_seg_post.

assert (ACT : acc asegs m4 (f + 48) 4).
{ apply (acc_ushadow asegs m4 (f + 48) 4); [clear - F1; Z.div_mod_to_equations; lia| lia| lia|].
replace (shad (f + 48)) with (sf + 6) by (rewrite SHF; unfold shad; clear - F1; Z.div_mod_to_equations; lia).
destruct FRS4 as [[_ BY] _]. cbn [cells_bytes cbytes app] in BY.
change [Z_to_bv 8 (-15); Z_to_bv 8 (-15); Z_to_bv 8 (-15); Z_to_bv 8 (-15); Z_to_bv 8 (-8); Z_to_bv 8 (-14); Z_to_bv 8 4; Z_to_bv 8 (-13)]
with ([Z_to_bv 8 (-15); Z_to_bv 8 (-15); Z_to_bv 8 (-15); Z_to_bv 8 (-15); Z_to_bv 8 (-8); Z_to_bv 8 (-14)] ++ [Z_to_bv 8 4] ++ [Z_to_bv 8 (-13)]) in BY.
apply bytes_at_app in BY. destruct BY as [_ BY]. apply bytes_at_app in BY. destruct BY as [BY _]. exact BY. }
assert (PREL4 : creq_pre STEREO m4 (a_low a) low (f + 48) (CtlSetSamplingRate (c_shr1 v))).
{ cbn [creq_pre]. exists tw. split; [exact TMP4|]. subst tw. exact (shr1w_low32 w3 v EQW RV). }
assert (M4f : (f + 48) mod 4 = 0) by (clear - F1; Z.div_mod_to_equations; lia).
lazymatch goal with A : X0ec.ART RT Σ1 m4 |- _ => rename A into ART4 end.
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes asegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end;
[ eapply (IH Σ1 PMc) with (OUT := OUTL) (STEREO := STEREO) (LBD := LBL) (r := (CtlSetSamplingRate (c_shr1 v))) (P := (f + 48)) (lo := lo) (fp := f) (kp := 0%nat); cps_auto | ].
{ cbn [creq_size]. change (fs_size 0) with 64. lia. }
{ rewrite EU. eassumption. }
intros cc5 (Σ2 & Hc5 & LV2 & FRS2 & SP2 & CR2 & PO2).
destruct (ASTA_unpack RT Σ2 PMc _ cc5 Hc5) as (ms5 & PO5 & Hc5'). clear Hc5. cbv beta in PO5.
destruct PO5 as (m5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5 & REP5 & CP5 & ACP5).
destruct RS5 as (zt0 & zt1 & zt2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & F5 & fc5 & -> & FRM5).
rewrite EU in *. cbn [creq_ivs creq_size app] in PRES5.

xfp PRES5 WM5 OUTB FR3. xfp PRES5 WM5 OUTB FB0. xfp PRES5 WM5 OUTB FB1. xfp PRES5 WM5 OUTB FRS4. xfp PRES5 WM5 OUTB HD4. xfp PRES5 WM5 OUTB TL. xfp PRES5 WM5 OUTB ARG4.
assert (AG5 : agree_blocks asegs m4 m5 (tl (sb_blocks s S a))).
{ apply (agree_blocks_of_pres_fp RT Σ1 _ _ _ m4 m5 _ PRES5 WM5).
- intros b Hb. apply LIVE1. apply in_app_iff. left. cbn [sb_blocks tl] in Hb |- *. right. exact Hb.
- intros b x Hb Hx. split; [| exact (APL b x Hb Hx)].
pose proof (BOUT b x ltac:(apply in_app_iff; left; exact Hb) Hx) as H1. pose proof (BOUT2 b x ltac:(apply in_app_iff; left; exact Hb) Hx) as H2.
clear - H1 H2 FP1 FP2. cbn [fst snd]. lia. }
apply (sb_bufs_agree s S a j m4 m5) in BUFS; [| exact JOK | exact AG5]. clear AG5 RLOW.
assert (PF5 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((P, P + 4) :: (S, S + 160) :: blocks_ivs (tl (sb_blocks s S a) ++ LBL)) m m5).
{ apply (pres_fp_trans _ _ _ _ m m4 m5 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -96) _ m4 m5 PRES5).
- intros e He. rewrite LV1. exact He.
- intros e He. rewrite FRS1. right. exact He.
- lia.
- intros x Hx (O1 & O2 & O3). split; [pose proof (NAF x Hx) as (N1 & _); change (fs_size 0) with 64 in N1; clear - N1; cbn [fst snd]; lia| exact (outside_blocks_app_r (tl (sb_blocks s S a)) LBL x O3)]. }
clear PF PRES5. rename PF5 into PF.
cps_sigma LV2 FRS2 SP2.
destruct CP5 as (w5 & TMP5 & _).
assert (FRSb : rw_cells asegs m5 sf (sbctl_shadow bF8 (Z_to_bv 8 4))) by exact FRS4. clear FRS4.
destruct (af_acc_live RT AF Σ2 m5 S 160 ART5 INL) as (_ & ACS5).
assert (OBS5 : aobj asegs m5 S 160) by (split; [lia|]; split; [ulc| exact ACS5]).
cps_seg (sbarm_ssr_b usp S P f sf).
destruct POST as (m5b & yb1 & -> & FRS5b & MU5b & WM5b & MI5b).
pose proof (agree_blocks_of_munch asegs _ m5 m5b (tl (sb_blocks s S a) ++ LBL) MU5b WM5b
ltac:(intros b x Hb Hx; pose proof (BOUT2 b x Hb Hx) as H2; clear - H2; cbn [outside]; split; [lia| exact I])) as AG5b.
apply (sb_bufs_agree s S a j m5 m5b) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG5b| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG5b| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG5b FRSb OBS5 ACS5. unfold sbctl_shadow, bF1, bF3, bF8 in FRS5b.
cps_seg_post.

assert (FRSE : rw_cells asegs m5b sf (sbctl_shadow bF8 bF8)) by exact FRS5b. clear FRS5b.
chunk_uncons FB0 as HDF.
cps_seg (sbctl_epi_a usp f sf).
destruct POST as (m6 & -> & MU6 & WM6 & MI6 & FRS6).
pose proof (agree_blocks_of_munch asegs _ m5b m6 (tl (sb_blocks s S a) ++ LBL) MU6 WM6
ltac:(intros b x Hb Hx; pose proof (BOUT2 b x Hb Hx) as H2; clear - H2; cbn [outside]; repeat split; lia)) as AG6.
apply (sb_bufs_agree s S a j m5b m6) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG6 HDF FRSE FB0 FB1 TMP5. unfold sbctl_shadow_dead, bF5 in FRS6. cbn [map repeat] in FRS6.
cps_seg_post.

assert (EF2 : rt_frames RT Σ2 = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRS2; exact FRS1).
assert (EL2 : rt_live RT Σ2 = rt_live RT Σ) by (rewrite LV2; exact LV1).
lazymatch goal with A : X0ec.ART RT Σ2 _ |- _ => rename A into ARTX end.
cps_release_intro ARTX EF2 EL2 (fun E : rt_frames RT Σ = [] => eq_trans PO2 (eq_trans PO1 (PNIL E))) Σ3 fl.
assert (FLS : fl < S \/ S + 160 <= fl).
{ destruct (Z_lt_dec fl S) as [L|L]; [left; exact L|]. destruct (Z_le_dec (S + 160) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; left. exists S, 160. split; [exact INL| clear - L G; lia]. }
assert (FLP : fl < fp \/ fp + fs_size kp - 8 <= fl).
{ destruct (Z_lt_dec fl fp) as [L|L]; [left; exact L|]. destruct (Z_le_dec (fp + fs_size kp - 8) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; right; left. exists fp, kp. split; [exact INF| clear - L G; lia]. }
assert (FR6 : rw_cells asegs m6 (usp + -96) (sbctl_frame (C8 (Z_to_bv 64 f)) s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) by exact FR3. clear FR3.
cps_seg (sbctl_epi_b usp lo f fl).
destruct POST as (m7 & -> & MU7 & WM7 & MI7 & ST7 & FLG7).
assert (AG7 : agree_blocks asegs m6 m7 (tl (sb_blocks s S a) ++ LBL)).
{ apply (agree_blocks_of_munch asegs _ m6 m7 _ MU7 WM7). intros b x Hb Hx. cbn [outside]. split; [| exact I]. intros Hfl.
apply NAC. right; right; left. exists (blk_addr b), (blk_size b). split; [| clear - Hx Hfl; lia].
rewrite LV2. apply LIVE1. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; cbn [sb_blocks tl] in Hb |- *; right; exact Hb| right; exact Hb]. }
apply (sb_bufs_agree s S a j m6 m7) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG7 FR6 FRS6.
cps_release_done REL MU7 WM7 FLG7.
apply Hk. exists Σ3. split; [| cbn [dec_depth]; split; [congruence|]; split; [congruence|]; split; [congruence|]; split; [clear - EC CR2 CR1; cbn [dec_depth] in *; lia| congruence]].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m7.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM5]|].
split. { split; [assumption|]. split; [exact MI7|]. split; [cps_wmono| exact ST7]. }
split; [exact PF|].
pose proof (ACCK m7 PF) as ACP7.
cbn [speex_decoder_ctl] in *. destruct (speex_decoder_ctl low (CtlSetSamplingRate (c_shr1 v))) as [v' low'] eqn:EC5. cbn [fst snd] in *.
split; [| split; [exists w3; split; [exact ARG4| exact EQW]| exact ACP7]].
assert (HDN : rw_cells asegs m7 S (sbhd MP (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s))
(Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s))
(Z_to_bv 64 v) (Z_to_bv 64 (sbd_lpc_enh_enabled s)))).
{ unfold sbhd. eapply rw_cells_samebytes; [exact HD4| clear; cbn; tauto| cbn [cells_bytes cbytes app]; rewrite (sx32_cell_eqm w3 v EQW); reflexivity| reflexivity]. }
cbn [decst_rep]. exists a, j, LBL. split; [reflexivity|]. split; [exact S8|]. split; [exact SPOS|]. split; [destruct INV as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12); unfold sb_inv; cbn; repeat split; first [assumption | clear - RV I8 I9 I11; lia]|]. split; [exact JOK|].
split; [change (SBCELLS (set_sbd_sampling_rate s v) a OUT j) with (sbhd (sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode (sbd_mode s)) (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s)) (Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s)) (Z_to_bv 64 v) (Z_to_bv 64 (sbd_lpc_enh_enabled s)) ++ sbtl s a OUT j); rewrite <- EMP; apply (proj2 (rw_cells_app asegs m7 S _ _)); split; [exact HDN| exact TL]|].
split; [exact BUFS|]. exists OUTL. exact REP5. }
1: {
destruct PRE3 as (w3 & _ & _ & RV).
cps_seg (sbarm_pass_a usp S P f sf).
destruct POST as (ya3 & ya4 & ya5 & ->).
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes asegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end;
[ eapply (IH Σ1 PMc) with (OUT := OUTL) (STEREO := STEREO) (LBD := LBL) (r := (CtlSetEnh v)) (P := P) (lo := lo) (fp := fp) (kp := kp); cps_auto | ].
{ rewrite EU. exact ST3. }
intros cc5 (Σ2 & Hc5 & LV2 & FRS2 & SP2 & CR2 & PO2).
destruct (ASTA_unpack RT Σ2 PMc _ cc5 Hc5) as (ms5 & PO5 & Hc5'). clear Hc5. cbv beta in PO5.
destruct PO5 as (m5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5 & REP5 & CP5 & ACP5).
destruct RS5 as (zt0 & zt1 & zt2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & F5 & fc5 & -> & FRM5).
rewrite EU in *. cbn [creq_ivs creq_size app] in PRES5.

xfp PRES5 WM5 OUTB FR3. xfp PRES5 WM5 OUTB FRB3. xfp PRES5 WM5 OUTB FRS3. xfp PRES5 WM5 OUTB HD3. xfp PRES5 WM5 OUTB TL.
assert (AG5 : agree_blocks asegs m3 m5 (tl (sb_blocks s S a))).
{ apply (agree_blocks_of_pres_fp RT Σ1 _ _ _ m3 m5 _ PRES5 WM5).
- intros b Hb. apply LIVE1. apply in_app_iff. left. cbn [sb_blocks tl] in Hb |- *. right. exact Hb.
- intros b x Hb Hx. split; [| exact (APL b x Hb Hx)].
pose proof (BOUT b x ltac:(apply in_app_iff; left; exact Hb) Hx) as H1. pose proof (BOUT2 b x ltac:(apply in_app_iff; left; exact Hb) Hx) as H2.
clear - H1 H2 FP1 FP2. cbn [fst snd]. lia. }
apply (sb_bufs_agree s S a j m3 m5) in BUFS; [| exact JOK | exact AG5]. clear AG5 RLOW.
assert (PF5 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((P, P + 4) :: (S, S + 160) :: blocks_ivs (tl (sb_blocks s S a) ++ LBL)) m m5).
{ apply (pres_fp_trans _ _ _ _ m m3 m5 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -96) _ m3 m5 PRES5).
- intros e He. rewrite LV1. exact He.
- intros e He. rewrite FRS1. right. exact He.
- lia.
- intros x Hx (O1 & O2 & O3). split; [exact O1| exact (outside_blocks_app_r (tl (sb_blocks s S a)) LBL x O3)]. }
clear PF PRES5. rename PF5 into PF.
cps_sigma LV2 FRS2 SP2.
destruct CP5 as (w5 & ARG5 & EQW5).
destruct (af_acc_live RT AF Σ2 m5 S 160 ART5 INL) as (_ & ACS5).
assert (OBS5 : aobj asegs m5 S 160) by (split; [lia|]; split; [ulc| exact ACS5]).
assert (OBP5 : aobj asegs m5 P 4) by (split; [lia|]; split; [ulc| exact ACP5]).
assert (APS : P + 4 <= S \/ S + 160 <= P) by (clear - FLA1 FP1 FP2 FSZ; unfold hid in FLA1; lia).
cps_seg (sbarm_enh_b usp S P f sf).
destruct POST as (m5b & yb1 & yb2 & -> & HD5 & ARG5b & MU5b & WM5b & MI5b).
pose proof (agree_blocks_of_munch asegs _ m5 m5b (tl (sb_blocks s S a) ++ LBL) MU5b WM5b
ltac:(intros b x Hb Hx; pose proof (BOUT b x Hb Hx) as H1; clear - H1; cbn [outside]; split; [lia| exact I])) as AG5b.
apply (sb_bufs_agree s S a j m5 m5b) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG5b| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG5b| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG5b HD3 ARG5 OBS5 ACS5 OBP5 APS. unfold sbhd in HD5.
cps_seg_post.

assert (FRSE : rw_cells asegs m5b sf (sbctl_shadow bF8 bF8)) by exact FRS3. clear FRS3.
chunk_uncons FRB3 as HDF.
cps_seg (sbctl_epi_a usp f sf).
destruct POST as (m6 & -> & MU6 & WM6 & MI6 & FRS6).
pose proof (agree_blocks_of_munch asegs _ m5b m6 (tl (sb_blocks s S a) ++ LBL) MU6 WM6
ltac:(intros b x Hb Hx; pose proof (BOUT2 b x Hb Hx) as H2; clear - H2; cbn [outside]; repeat split; lia)) as AG6.
apply (sb_bufs_agree s S a j m5b m6) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG6 HDF FRSE FRB3 . unfold sbctl_shadow_dead, bF5 in FRS6. cbn [map repeat] in FRS6.
cps_seg_post.

assert (EF2 : rt_frames RT Σ2 = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRS2; exact FRS1).
assert (EL2 : rt_live RT Σ2 = rt_live RT Σ) by (rewrite LV2; exact LV1).
lazymatch goal with A : X0ec.ART RT Σ2 _ |- _ => rename A into ARTX end.
cps_release_intro ARTX EF2 EL2 (fun E : rt_frames RT Σ = [] => eq_trans PO2 (eq_trans PO1 (PNIL E))) Σ3 fl.
assert (FLS : fl < S \/ S + 160 <= fl).
{ destruct (Z_lt_dec fl S) as [L|L]; [left; exact L|]. destruct (Z_le_dec (S + 160) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; left. exists S, 160. split; [exact INL| clear - L G; lia]. }
assert (FLP : fl < fp \/ fp + fs_size kp - 8 <= fl).
{ destruct (Z_lt_dec fl fp) as [L|L]; [left; exact L|]. destruct (Z_le_dec (fp + fs_size kp - 8) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; right; left. exists fp, kp. split; [exact INF| clear - L G; lia]. }
assert (FR6 : rw_cells asegs m6 (usp + -96) (sbctl_frame (C8 (Z_to_bv 64 f)) s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) by exact FR3. clear FR3.
cps_seg (sbctl_epi_b usp lo f fl).
destruct POST as (m7 & -> & MU7 & WM7 & MI7 & ST7 & FLG7).
assert (AG7 : agree_blocks asegs m6 m7 (tl (sb_blocks s S a) ++ LBL)).
{ apply (agree_blocks_of_munch asegs _ m6 m7 _ MU7 WM7). intros b x Hb Hx. cbn [outside]. split; [| exact I]. intros Hfl.
apply NAC. right; right; left. exists (blk_addr b), (blk_size b). split; [| clear - Hx Hfl; lia].
rewrite LV2. apply LIVE1. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; cbn [sb_blocks tl] in Hb |- *; right; exact Hb| right; exact Hb]. }
apply (sb_bufs_agree s S a j m6 m7) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG7 FR6 FRS6.
cps_release_done REL MU7 WM7 FLG7.
apply Hk. exists Σ3. split; [| cbn [dec_depth]; split; [congruence|]; split; [congruence|]; split; [congruence|]; split; [clear - EC CR2 CR1; cbn [dec_depth] in *; lia| congruence]].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m7.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM5]|].
split. { split; [assumption|]. split; [exact MI7|]. split; [cps_wmono| exact ST7]. }
split; [exact PF|].
pose proof (ACCK m7 PF) as ACP7.
cbn [speex_decoder_ctl] in *. destruct (speex_decoder_ctl low (CtlSetEnh v)) as [v' low'] eqn:EC5. cbn [fst snd] in *.
split; [| split; [exists w5; split; [exact ARG5b| exact EQW5]| exact ACP7]].
assert (HDN : rw_cells asegs m7 S (sbhd MP (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s))
(Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s))
(Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 v))).
{ unfold sbhd. eapply rw_cells_samebytes; [exact HD5| clear; cbn; tauto| cbn [cells_bytes cbytes app]; rewrite (sx32_cell_eqm w5 v EQW5); reflexivity| reflexivity]. }
cbn [decst_rep]. exists a, j, LBL. split; [reflexivity|]. split; [exact S8|]. split; [exact SPOS|]. split; [destruct INV as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12); unfold sb_inv; cbn; repeat split; first [assumption | clear - RV I8 I9 I11; lia]|]. split; [exact JOK|].
split; [change (SBCELLS (set_sbd_lpc_enh_enabled s v) a OUT j) with (sbhd (sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode (sbd_mode s)) (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s)) (Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s)) (Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 v) ++ sbtl s a OUT j); rewrite <- EMP; apply (proj2 (rw_cells_app asegs m7 S _ _)); split; [exact HDN| exact TL]|].
split; [exact BUFS|]. exists OUTL. exact REP5. }
1: {
destruct PRE3 as (w3 & ARG3).
assert (OBP3 : aobj asegs m3 P 4) by (split; [lia|]; split; [ulc| exact ACP3]).
assert (APS : P + 4 <= S \/ S + 160 <= P) by (clear - FLA1 FP1 FP2 FSZ; unfold hid in FLA1; lia).
assert (RV : - 2^31 <= sbd_full_frame_size s < 2^31) by (clear - INV; unfold sb_inv in INV; destruct INV as (IM & I1 & I2 & _); destruct IM as [E|E]; rewrite E in *; cbn in I1; lia).
assert (DP0 : (1 <= dec_depth low)%nat) by apply dec_depth_pos.
cps_seg (sbarm_gfs usp S P f sf).
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
assert (FLP : fl < fp \/ fp + fs_size kp - 8 <= fl).
{ destruct (Z_lt_dec fl fp) as [L|L]; [left; exact L|]. destruct (Z_le_dec (fp + fs_size kp - 8) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; right; left. exists fp, kp. split; [exact INF| clear - L G; lia]. }
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
pose proof (ACCK m7 PF) as ACP7.
cbn [speex_decoder_ctl fst snd] in *.
split; [| split; [split; [exact ARG4| exact RV]| exact ACP7]].
cbn [decst_rep]. exists a, j, LBL. split; [reflexivity|]. split; [exact S8|]. split; [exact SPOS|]. split; [exact INV|]. split; [exact JOK|].
split; [rewrite sb_cells_split, <- EMP; apply (proj2 (rw_cells_app asegs m7 S _ _)); split; [exact HD4| exact TL]|].
split; [exact BUFS|]. exists OUTL. exact RLOW. }
1: {
cps_seg (sbarm_pass_a usp S P f sf).
destruct POST as (ya3 & ya4 & ya5 & ->).
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes asegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end;
[ eapply (IH Σ1 PMc) with (OUT := OUTL) (STEREO := STEREO) (LBD := LBL) (r := CtlSetHandlerStereo) (P := P) (lo := lo) (fp := fp) (kp := kp); cps_auto | ].
{ rewrite EU. exact ST3. }
intros cc5 (Σ2 & Hc5 & LV2 & FRS2 & SP2 & CR2 & PO2).
destruct (ASTA_unpack RT Σ2 PMc _ cc5 Hc5) as (ms5 & PO5 & Hc5'). clear Hc5. cbv beta in PO5.
destruct PO5 as (m5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5 & REP5 & CP5 & ACP5).
destruct RS5 as (zt0 & zt1 & zt2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & F5 & fc5 & -> & FRM5).
rewrite EU in *. cbn [creq_ivs creq_size app] in PRES5.

xfp PRES5 WM5 OUTB FR3. xfp PRES5 WM5 OUTB FRB3. xfp PRES5 WM5 OUTB FRS3. xfp PRES5 WM5 OUTB HD3. xfp PRES5 WM5 OUTB TL.
assert (AG5 : agree_blocks asegs m3 m5 (tl (sb_blocks s S a))).
{ apply (agree_blocks_of_pres_fp RT Σ1 _ _ _ m3 m5 _ PRES5 WM5).
- intros b Hb. apply LIVE1. apply in_app_iff. left. cbn [sb_blocks tl] in Hb |- *. right. exact Hb.
- intros b x Hb Hx. split; [| exact (APL b x Hb Hx)].
pose proof (BOUT b x ltac:(apply in_app_iff; left; exact Hb) Hx) as H1. pose proof (BOUT2 b x ltac:(apply in_app_iff; left; exact Hb) Hx) as H2.
clear - H1 H2 FP1 FP2. cbn [fst snd]. lia. }
apply (sb_bufs_agree s S a j m3 m5) in BUFS; [| exact JOK | exact AG5]. clear AG5 RLOW.
assert (PF5 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((P, P + 24) :: (S, S + 160) :: blocks_ivs (tl (sb_blocks s S a) ++ LBL)) m m5).
{ apply (pres_fp_trans _ _ _ _ m m3 m5 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -96) _ m3 m5 PRES5).
- intros e He. rewrite LV1. exact He.
- intros e He. rewrite FRS1. right. exact He.
- lia.
- intros x Hx (O1 & O2 & O3). split; [exact O1| exact (outside_blocks_app_r (tl (sb_blocks s S a)) LBL x O3)]. }
clear PF PRES5. rename PF5 into PF.
cps_sigma LV2 FRS2 SP2.
destruct CP5 as (pad5 & ARG5).
destruct (af_acc_live RT AF Σ2 m5 S 160 ART5 INL) as (_ & ACS5).
assert (OBS5 : aobj asegs m5 S 160) by (split; [lia|]; split; [ulc| exact ACS5]).
cps_seg (sbarm_pass_b usp S P f sf).
subst ms.
clear OBS5 ACS5. unfold sbhd in HD3.

assert (FRSE : rw_cells asegs m5 sf (sbctl_shadow bF8 bF8)) by exact FRS3. clear FRS3.
chunk_uncons FRB3 as HDF.
cps_seg (sbctl_epi_a usp f sf).
destruct POST as (m6 & -> & MU6 & WM6 & MI6 & FRS6).
pose proof (agree_blocks_of_munch asegs _ m5 m6 (tl (sb_blocks s S a) ++ LBL) MU6 WM6
ltac:(intros b x Hb Hx; pose proof (BOUT2 b x Hb Hx) as H2; clear - H2; cbn [outside]; repeat split; lia)) as AG6.
apply (sb_bufs_agree s S a j m5 m6) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG6 HDF FRSE FRB3 . unfold sbctl_shadow_dead, bF5 in FRS6. cbn [map repeat] in FRS6.
cps_seg_post.

assert (EF2 : rt_frames RT Σ2 = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRS2; exact FRS1).
assert (EL2 : rt_live RT Σ2 = rt_live RT Σ) by (rewrite LV2; exact LV1).
lazymatch goal with A : X0ec.ART RT Σ2 _ |- _ => rename A into ARTX end.
cps_release_intro ARTX EF2 EL2 (fun E : rt_frames RT Σ = [] => eq_trans PO2 (eq_trans PO1 (PNIL E))) Σ3 fl.
assert (FLS : fl < S \/ S + 160 <= fl).
{ destruct (Z_lt_dec fl S) as [L|L]; [left; exact L|]. destruct (Z_le_dec (S + 160) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; left. exists S, 160. split; [exact INL| clear - L G; lia]. }
assert (FLP : fl < fp \/ fp + fs_size kp - 8 <= fl).
{ destruct (Z_lt_dec fl fp) as [L|L]; [left; exact L|]. destruct (Z_le_dec (fp + fs_size kp - 8) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; right; left. exists fp, kp. split; [exact INF| clear - L G; lia]. }
assert (FR6 : rw_cells asegs m6 (usp + -96) (sbctl_frame (C8 (Z_to_bv 64 f)) s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) by exact FR3. clear FR3.
cps_seg (sbctl_epi_b usp lo f fl).
destruct POST as (m7 & -> & MU7 & WM7 & MI7 & ST7 & FLG7).
assert (AG7 : agree_blocks asegs m6 m7 (tl (sb_blocks s S a) ++ LBL)).
{ apply (agree_blocks_of_munch asegs _ m6 m7 _ MU7 WM7). intros b x Hb Hx. cbn [outside]. split; [| exact I]. intros Hfl.
apply NAC. right; right; left. exists (blk_addr b), (blk_size b). split; [| clear - Hx Hfl; lia].
rewrite LV2. apply LIVE1. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; cbn [sb_blocks tl] in Hb |- *; right; exact Hb| right; exact Hb]. }
apply (sb_bufs_agree s S a j m6 m7) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG7 FR6 FRS6.
cps_release_done REL MU7 WM7 FLG7.
apply Hk. exists Σ3. split; [| cbn [dec_depth]; split; [congruence|]; split; [congruence|]; split; [congruence|]; split; [clear - EC CR2 CR1; cbn [dec_depth] in *; lia| congruence]].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m7.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM5]|].
split. { split; [assumption|]. split; [exact MI7|]. split; [cps_wmono| exact ST7]. }
split; [exact PF|].
pose proof (ACCK m7 PF) as ACP7.
cbn [speex_decoder_ctl] in *. destruct (speex_decoder_ctl low CtlSetHandlerStereo) as [v' low'] eqn:EC5. cbn [fst snd] in *.
split; [| split; [exists pad5; exact ARG5| exact ACP7]].
cbn [decst_rep]. exists a, j, LBL. split; [reflexivity|]. split; [exact S8|]. split; [exact SPOS|]. split; [exact INV|]. split; [exact JOK|].
split; [rewrite sb_cells_split, <- EMP; apply (proj2 (rw_cells_app asegs m7 S _ _)); split; [exact HD3| exact TL]|].
split; [exact BUFS|]. exists OUTL. exact REP5. }
1: {
destruct PRE3 as (w3 & ARG3).
assert (OBP3 : aobj asegs m3 P 4) by (split; [lia|]; split; [ulc| exact ACP3]).
assert (APS : P + 4 <= S \/ S + 160 <= P) by (clear - FLA1 FP1 FP2 FSZ; unfold hid in FLA1; lia).
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
assert (FLP : fl < fp \/ fp + fs_size kp - 8 <= fl).
{ destruct (Z_lt_dec fl fp) as [L|L]; [left; exact L|]. destruct (Z_le_dec (fp + fs_size kp - 8) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; right; left. exists fp, kp. split; [exact INF| clear - L G; lia]. }
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
pose proof (ACCK m7 PF) as ACP7.
cbn [speex_decoder_ctl fst snd] in *.
split; [| split; [split; [exact ARG4| exact RV]| exact ACP7]].
cbn [decst_rep]. exists a, j, LBL. split; [reflexivity|]. split; [exact S8|]. split; [exact SPOS|]. split; [exact INV|]. split; [exact JOK|].
split; [rewrite sb_cells_split, <- EMP; apply (proj2 (rw_cells_app asegs m7 S _ _)); split; [exact HD4| exact TL]|].
split; [exact BUFS|]. exists OUTL. exact RLOW. }
1: {
cps_seg (sbarm_pass_a usp S P f sf).
destruct POST as (ya3 & ya4 & ya5 & ->).
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes asegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end;
[ eapply (IH Σ1 PMc) with (OUT := OUTL) (STEREO := STEREO) (LBD := LBL) (r := CtlGetLookahead) (P := P) (lo := lo) (fp := fp) (kp := kp); cps_auto | ].
{ rewrite EU. exact ST3. }
intros cc5 (Σ2 & Hc5 & LV2 & FRS2 & SP2 & CR2 & PO2).
destruct (ASTA_unpack RT Σ2 PMc _ cc5 Hc5) as (ms5 & PO5 & Hc5'). clear Hc5. cbv beta in PO5.
destruct PO5 as (m5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5 & REP5 & CP5 & ACP5).
destruct RS5 as (zt0 & zt1 & zt2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & F5 & fc5 & -> & FRM5).
rewrite EU in *. cbn [creq_ivs creq_size app] in PRES5.

xfp PRES5 WM5 OUTB FR3. xfp PRES5 WM5 OUTB FRB3. xfp PRES5 WM5 OUTB FRS3. xfp PRES5 WM5 OUTB HD3. xfp PRES5 WM5 OUTB TL.
assert (AG5 : agree_blocks asegs m3 m5 (tl (sb_blocks s S a))).
{ apply (agree_blocks_of_pres_fp RT Σ1 _ _ _ m3 m5 _ PRES5 WM5).
- intros b Hb. apply LIVE1. apply in_app_iff. left. cbn [sb_blocks tl] in Hb |- *. right. exact Hb.
- intros b x Hb Hx. split; [| exact (APL b x Hb Hx)].
pose proof (BOUT b x ltac:(apply in_app_iff; left; exact Hb) Hx) as H1. pose proof (BOUT2 b x ltac:(apply in_app_iff; left; exact Hb) Hx) as H2.
clear - H1 H2 FP1 FP2. cbn [fst snd]. lia. }
apply (sb_bufs_agree s S a j m3 m5) in BUFS; [| exact JOK | exact AG5]. clear AG5 RLOW.
assert (PF5 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((P, P + 4) :: (S, S + 160) :: blocks_ivs (tl (sb_blocks s S a) ++ LBL)) m m5).
{ apply (pres_fp_trans _ _ _ _ m m3 m5 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -96) _ m3 m5 PRES5).
- intros e He. rewrite LV1. exact He.
- intros e He. rewrite FRS1. right. exact He.
- lia.
- intros x Hx (O1 & O2 & O3). split; [exact O1| exact (outside_blocks_app_r (tl (sb_blocks s S a)) LBL x O3)]. }
clear PF PRES5. rename PF5 into PF.
cps_sigma LV2 FRS2 SP2.
destruct CP5 as (ARG5 & RV5).
destruct (af_acc_live RT AF Σ2 m5 S 160 ART5 INL) as (_ & ACS5).
assert (OBS5 : aobj asegs m5 S 160) by (split; [lia|]; split; [ulc| exact ACS5]).
assert (OBP5 : aobj asegs m5 P 4) by (split; [lia|]; split; [ulc| exact ACP5]).
assert (RV30 : - 2^30 <= fst (speex_decoder_ctl low CtlGetLookahead) < 2^30)
by (pose proof (lookahead_val low ltac:(clear - DEP; lia)) as LV; clear - LV; lia).
cps_seg (sbarm_gla_b usp S P f sf).
destruct POST as (m5b & yb1 & yb2 & -> & ARG5b & MU5b & WM5b & MI5b).
pose proof (agree_blocks_of_munch asegs _ m5 m5b (tl (sb_blocks s S a) ++ LBL) MU5b WM5b
ltac:(intros b x Hb Hx; pose proof (BOUT b x Hb Hx) as H1; clear - H1 FP1 FP2; cbn [outside]; split; [lia| exact I])) as AG5b.
apply (sb_bufs_agree s S a j m5 m5b) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG5b| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG5b| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG5b ARG5 OBS5 ACS5 OBP5. unfold sbhd in HD3.
cps_seg_post.

assert (FRSE : rw_cells asegs m5b sf (sbctl_shadow bF8 bF8)) by exact FRS3. clear FRS3.
chunk_uncons FRB3 as HDF.
cps_seg (sbctl_epi_a usp f sf).
destruct POST as (m6 & -> & MU6 & WM6 & MI6 & FRS6).
pose proof (agree_blocks_of_munch asegs _ m5b m6 (tl (sb_blocks s S a) ++ LBL) MU6 WM6
ltac:(intros b x Hb Hx; pose proof (BOUT2 b x Hb Hx) as H2; clear - H2; cbn [outside]; repeat split; lia)) as AG6.
apply (sb_bufs_agree s S a j m5b m6) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG6 HDF FRSE FRB3 . unfold sbctl_shadow_dead, bF5 in FRS6. cbn [map repeat] in FRS6.
cps_seg_post.

assert (EF2 : rt_frames RT Σ2 = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRS2; exact FRS1).
assert (EL2 : rt_live RT Σ2 = rt_live RT Σ) by (rewrite LV2; exact LV1).
lazymatch goal with A : X0ec.ART RT Σ2 _ |- _ => rename A into ARTX end.
cps_release_intro ARTX EF2 EL2 (fun E : rt_frames RT Σ = [] => eq_trans PO2 (eq_trans PO1 (PNIL E))) Σ3 fl.
assert (FLS : fl < S \/ S + 160 <= fl).
{ destruct (Z_lt_dec fl S) as [L|L]; [left; exact L|]. destruct (Z_le_dec (S + 160) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; left. exists S, 160. split; [exact INL| clear - L G; lia]. }
assert (FLP : fl < fp \/ fp + fs_size kp - 8 <= fl).
{ destruct (Z_lt_dec fl fp) as [L|L]; [left; exact L|]. destruct (Z_le_dec (fp + fs_size kp - 8) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; right; left. exists fp, kp. split; [exact INF| clear - L G; lia]. }
assert (FR6 : rw_cells asegs m6 (usp + -96) (sbctl_frame (C8 (Z_to_bv 64 f)) s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) by exact FR3. clear FR3.
cps_seg (sbctl_epi_b usp lo f fl).
destruct POST as (m7 & -> & MU7 & WM7 & MI7 & ST7 & FLG7).
assert (AG7 : agree_blocks asegs m6 m7 (tl (sb_blocks s S a) ++ LBL)).
{ apply (agree_blocks_of_munch asegs _ m6 m7 _ MU7 WM7). intros b x Hb Hx. cbn [outside]. split; [| exact I]. intros Hfl.
apply NAC. right; right; left. exists (blk_addr b), (blk_size b). split; [| clear - Hx Hfl; lia].
rewrite LV2. apply LIVE1. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; cbn [sb_blocks tl] in Hb |- *; right; exact Hb| right; exact Hb]. }
apply (sb_bufs_agree s S a j m6 m7) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG7 FR6 FRS6.
cps_release_done REL MU7 WM7 FLG7.
apply Hk. exists Σ3. split; [| cbn [dec_depth]; split; [congruence|]; split; [congruence|]; split; [congruence|]; split; [clear - EC CR2 CR1; cbn [dec_depth] in *; lia| congruence]].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m7.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM5]|].
split. { split; [assumption|]. split; [exact MI7|]. split; [cps_wmono| exact ST7]. }
split; [exact PF|].
pose proof (ACCK m7 PF) as ACP7.
cbn [speex_decoder_ctl] in *. destruct (speex_decoder_ctl low CtlGetLookahead) as [vl low'] eqn:EC5. cbn [fst snd] in *.
split; [| split; [split; [exact ARG5b| clear - RV30; lia]| exact ACP7]].
cbn [decst_rep]. exists a, j, LBL. split; [reflexivity|]. split; [exact S8|]. split; [exact SPOS|]. split; [exact INV|]. split; [exact JOK|].
split; [rewrite sb_cells_split, <- EMP; apply (proj2 (rw_cells_app asegs m7 S _ _)); split; [exact HD3| exact TL]|].
split; [exact BUFS|]. exists OUTL. exact REP5. }
1: {
cps_seg (sbarm_pass_a usp S P f sf).
destruct POST as (ya3 & ya4 & ya5 & ->).
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes asegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end;
[ eapply (IH Σ1 PMc) with (OUT := OUTL) (STEREO := STEREO) (LBD := LBL) (r := (CtlSetWideband v)) (P := P) (lo := lo) (fp := fp) (kp := kp); cps_auto | ].
{ rewrite EU. exact ST3. }
intros cc5 (Σ2 & Hc5 & LV2 & FRS2 & SP2 & CR2 & PO2).
destruct (ASTA_unpack RT Σ2 PMc _ cc5 Hc5) as (ms5 & PO5 & Hc5'). clear Hc5. cbv beta in PO5.
destruct PO5 as (m5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5 & REP5 & CP5 & ACP5).
destruct RS5 as (zt0 & zt1 & zt2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & F5 & fc5 & -> & FRM5).
rewrite EU in *. cbn [creq_ivs creq_size app] in PRES5.

xfp PRES5 WM5 OUTB FR3. xfp PRES5 WM5 OUTB FRB3. xfp PRES5 WM5 OUTB FRS3. xfp PRES5 WM5 OUTB HD3. xfp PRES5 WM5 OUTB TL.
assert (AG5 : agree_blocks asegs m3 m5 (tl (sb_blocks s S a))).
{ apply (agree_blocks_of_pres_fp RT Σ1 _ _ _ m3 m5 _ PRES5 WM5).
- intros b Hb. apply LIVE1. apply in_app_iff. left. cbn [sb_blocks tl] in Hb |- *. right. exact Hb.
- intros b x Hb Hx. split; [| exact (APL b x Hb Hx)].
pose proof (BOUT b x ltac:(apply in_app_iff; left; exact Hb) Hx) as H1. pose proof (BOUT2 b x ltac:(apply in_app_iff; left; exact Hb) Hx) as H2.
clear - H1 H2 FP1 FP2. cbn [fst snd]. lia. }
apply (sb_bufs_agree s S a j m3 m5) in BUFS; [| exact JOK | exact AG5]. clear AG5 RLOW.
assert (PF5 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((P, P + 4) :: (S, S + 160) :: blocks_ivs (tl (sb_blocks s S a) ++ LBL)) m m5).
{ apply (pres_fp_trans _ _ _ _ m m3 m5 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -96) _ m3 m5 PRES5).
- intros e He. rewrite LV1. exact He.
- intros e He. rewrite FRS1. right. exact He.
- lia.
- intros x Hx (O1 & O2 & O3). split; [exact O1| exact (outside_blocks_app_r (tl (sb_blocks s S a)) LBL x O3)]. }
clear PF PRES5. rename PF5 into PF.
cps_sigma LV2 FRS2 SP2.
destruct CP5 as (w5 & ARG5 & EQW5).
destruct (af_acc_live RT AF Σ2 m5 S 160 ART5 INL) as (_ & ACS5).
assert (OBS5 : aobj asegs m5 S 160) by (split; [lia|]; split; [ulc| exact ACS5]).
cps_seg (sbarm_pass_b usp S P f sf).
subst ms.
clear OBS5 ACS5. unfold sbhd in HD3.

assert (FRSE : rw_cells asegs m5 sf (sbctl_shadow bF8 bF8)) by exact FRS3. clear FRS3.
chunk_uncons FRB3 as HDF.
cps_seg (sbctl_epi_a usp f sf).
destruct POST as (m6 & -> & MU6 & WM6 & MI6 & FRS6).
pose proof (agree_blocks_of_munch asegs _ m5 m6 (tl (sb_blocks s S a) ++ LBL) MU6 WM6
ltac:(intros b x Hb Hx; pose proof (BOUT2 b x Hb Hx) as H2; clear - H2; cbn [outside]; repeat split; lia)) as AG6.
apply (sb_bufs_agree s S a j m5 m6) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG6 HDF FRSE FRB3 . unfold sbctl_shadow_dead, bF5 in FRS6. cbn [map repeat] in FRS6.
cps_seg_post.

assert (EF2 : rt_frames RT Σ2 = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRS2; exact FRS1).
assert (EL2 : rt_live RT Σ2 = rt_live RT Σ) by (rewrite LV2; exact LV1).
lazymatch goal with A : X0ec.ART RT Σ2 _ |- _ => rename A into ARTX end.
cps_release_intro ARTX EF2 EL2 (fun E : rt_frames RT Σ = [] => eq_trans PO2 (eq_trans PO1 (PNIL E))) Σ3 fl.
assert (FLS : fl < S \/ S + 160 <= fl).
{ destruct (Z_lt_dec fl S) as [L|L]; [left; exact L|]. destruct (Z_le_dec (S + 160) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; left. exists S, 160. split; [exact INL| clear - L G; lia]. }
assert (FLP : fl < fp \/ fp + fs_size kp - 8 <= fl).
{ destruct (Z_lt_dec fl fp) as [L|L]; [left; exact L|]. destruct (Z_le_dec (fp + fs_size kp - 8) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; right; left. exists fp, kp. split; [exact INF| clear - L G; lia]. }
assert (FR6 : rw_cells asegs m6 (usp + -96) (sbctl_frame (C8 (Z_to_bv 64 f)) s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) by exact FR3. clear FR3.
cps_seg (sbctl_epi_b usp lo f fl).
destruct POST as (m7 & -> & MU7 & WM7 & MI7 & ST7 & FLG7).
assert (AG7 : agree_blocks asegs m6 m7 (tl (sb_blocks s S a) ++ LBL)).
{ apply (agree_blocks_of_munch asegs _ m6 m7 _ MU7 WM7). intros b x Hb Hx. cbn [outside]. split; [| exact I]. intros Hfl.
apply NAC. right; right; left. exists (blk_addr b), (blk_size b). split; [| clear - Hx Hfl; lia].
rewrite LV2. apply LIVE1. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; cbn [sb_blocks tl] in Hb |- *; right; exact Hb| right; exact Hb]. }
apply (sb_bufs_agree s S a j m6 m7) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG7 FR6 FRS6.
cps_release_done REL MU7 WM7 FLG7.
apply Hk. exists Σ3. split; [| cbn [dec_depth]; split; [congruence|]; split; [congruence|]; split; [congruence|]; split; [clear - EC CR2 CR1; cbn [dec_depth] in *; lia| congruence]].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m7.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM5]|].
split. { split; [assumption|]. split; [exact MI7|]. split; [cps_wmono| exact ST7]. }
split; [exact PF|].
pose proof (ACCK m7 PF) as ACP7.
cbn [speex_decoder_ctl] in *. destruct (speex_decoder_ctl low (CtlSetWideband v)) as [v' low'] eqn:EC5. cbn [fst snd] in *.
split; [| split; [exists w5; split; [exact ARG5| exact EQW5]| exact ACP7]].
cbn [decst_rep]. exists a, j, LBL. split; [reflexivity|]. split; [exact S8|]. split; [exact SPOS|]. split; [exact INV|]. split; [exact JOK|].
split; [rewrite sb_cells_split, <- EMP; apply (proj2 (rw_cells_app asegs m7 S _ _)); split; [exact HD3| exact TL]|].
split; [exact BUFS|]. exists OUTL. exact REP5. }
Qed.

Theorem ctl_cps_all : forall d, ctl_cps_at RT d.
Proof using AF SM0 AF_LIB.
induction d as [st|s low IH]; [exact (ctl_cps_nb RT AF AF_LIB st)| exact (ctl_cps_sb s low IH)].
Qed.
End CtlSB.
