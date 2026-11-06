(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1df X1ck X1cg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1nt X1rg X1rh X1re X1od X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require X1qy X1nu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j5 X0ec X001 X00b X000 X04b X00c X07z X05o X05p
X05s X05t X08k X05u
X0ae X09j X09u X0af X09x X09p X09o
X05l X05c X05m X09f X06d X069 X068 X081 X06l X0ak X0aj X07m X05w X06e
X071 X06v X06y X06u X073 X07j X072 X077 X07f X07e
X07b X07c X06o X070.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X12c X19o X14x X0r0 X0ra X0qz X0v9 X0rb X0wl X0wm X0zb X0wn X110 X106 X10j X10c X10b X0w9 X0x2 X0x1 X0ys X0xd X115 X114 X0wp X0x6 X0xn X0xq X0xm X0xu X0ya X0xt X0y6 X0y5 X0xg X0ye X0xs.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X106 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xd OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X115 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X114 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wp OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x6 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xu OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ya OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y6 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xg OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ye OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).
Local Notation Z64 := (Z_to_bv 64).

Definition hdr_tail (h : hstate unit) (hd : spx_header) : option (hstate unit) :=
if 1 <? hd_speex_version_id hd then None else
if negb (hd_mode_bitstream_version hd =? 4) then None else
let d1 := snd (speex_decoder_ctl (init_dec (mode_of_id (hd_mode hd))) (CtlSetEnh 1)) in
let fs := fst (speex_decoder_ctl d1 CtlGetFrameSize) in
let d2 := snd (speex_decoder_ctl d1 CtlGetFrameSize) in
if (fs <? 0) || (640 <? fs) then None else
let rate := if h_rate h =? 0 then hd_rate hd else h_rate h in
let d3 := snd (speex_decoder_ctl d2 (CtlSetSamplingRate rate)) in
if (hd_frames_per_packet hd <? 1) || (10 <? hd_frames_per_packet hd) then None else
let ch0 := if h_channels h =? -1 then hd_nb_channels hd else h_channels h in
let d4 := if ch0 =? 1 then d3 else snd (speex_decoder_ctl d3 CtlSetHandlerStereo) in
if 2147483646 <? hd_extra_headers hd then None else
let d5 := snd (speex_decoder_ctl d4 CtlGetLookahead) in
Some (set_header h d5 (hd_frames_per_packet hd) (if ch0 =? 1 then 1 else 2) rate (hd_extra_headers hd) fs).

Lemma lib_get_mode_id : forall i, 0 <= i < 3 -> speex_lib_get_mode i = Some (mode_of_id i).
Proof.
intros i Hi. unfold speex_lib_get_mode, mode_of_id, SPEEX_NB_MODES.
replace ((i <? 0) || (3 <=? i)) with false by (symmetry; apply orb_false_intro; [apply Z.ltb_ge| apply Z.leb_gt]; lia).
destruct (i =? 0); [reflexivity|]. destruct (i =? 1); reflexivity.
Qed.

Lemma hdr_prun : forall (h : hstate unit) pdata bytes q r q',
prun (hP_process_header h pdata bytes) q = Some (r, q') ->
exists r1, prun (speex_packet_to_header (St := pst) p_calloc p_free p_notify pdata bytes) q = Some (r1, q') /\
match r1 with
| None => r = None
| Some (_, hd) => 0 <= hd_mode hd < 3 -> r = hdr_tail h hd
end.
Proof.
intros h pdata bytes q r q' H. unfold hP_process_header, process_header in H.
rewrite prun_bind in H.
destruct (prun (speex_packet_to_header (St := pst) p_calloc p_free p_notify pdata bytes) q) as [[r1 q1]|] eqn:E1; [| discriminate H].
cbv beta iota in H. exists r1.
destruct r1 as [[[] hd]|].
2: { rewrite prun_ret in H. injection H as <- <-. split; reflexivity. }
assert (KEY : 0 <= hd_mode hd < 3 -> r = hdr_tail h hd /\ q' = q1).
{ intros HM. unfold SPEEX_NB_MODES in H.
replace ((3 <=? hd_mode hd) || (hd_mode hd <? 0)) with false in H by (symmetry; apply orb_false_intro; [apply Z.leb_gt| apply Z.ltb_ge]; lia).
rewrite (lib_get_mode_id _ HM) in H. unfold hdr_tail, mode_bitstream_version in *. unfold bptr in *.
destruct (1 <? hd_speex_version_id hd).
{ rewrite prun_bind, prun_free in H. cbv beta iota in H. rewrite prun_ret in H. injection H as <- <-. split; reflexivity. }
destruct (Z.eqb_spec (hd_mode_bitstream_version hd) 4) as [EV|NV].
2: { destruct (Z.ltb_spec 4 (hd_mode_bitstream_version hd)) as [L1|L1].
- rewrite prun_bind, prun_free in H. cbv beta iota in H. rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
- replace (hd_mode_bitstream_version hd <? 4) with true in H by (symmetry; apply Z.ltb_lt; lia).
rewrite prun_bind, prun_free in H. cbv beta iota in H. rewrite prun_ret in H. injection H as <- <-. split; reflexivity. }
rewrite EV, !Z.ltb_irrefl in H. cbv iota in H. cbn [negb].
unfold h_decoder_init, h_decoder_destroy in H. rewrite prun_bind in H.
destruct (prun (speex_decoder_init (St := pst) p_calloc p_free (mode_of_id (hd_mode hd))) q1) as [[ost q2]|] eqn:E2; [| discriminate H].
destruct (init_prun _ _ _ _ E2) as [-> ->]. cbv beta iota in H.
destruct (@speex_decoder_ctl unit (init_dec (mode_of_id (hd_mode hd))) (CtlSetEnh 1)) as [x1 d1] eqn:C1. cbn [fst snd]. cbv beta iota in H.
destruct (speex_decoder_ctl d1 CtlGetFrameSize) as [fs d2] eqn:C2. cbn [fst snd]. cbv beta iota in H.
destruct ((fs <? 0) || (640 <? fs)) eqn:FSB.
{ change (2 * 320) with 640 in H. rewrite FSB in H.
rewrite prun_bind, prun_destroy in H. cbv beta iota in H. rewrite prun_bind, prun_free in H. cbv beta iota in H. rewrite prun_ret in H.
injection H as <- <-. split; reflexivity. }
change (2 * 320) with 640 in H. rewrite FSB in H.
destruct (speex_decoder_ctl d2 (CtlSetSamplingRate (if h_rate h =? 0 then hd_rate hd else h_rate h))) as [x3 d3] eqn:C3. cbn [fst snd]. cbv beta iota in H.
destruct ((hd_frames_per_packet hd <? 1) || (10 <? hd_frames_per_packet hd)).
{ rewrite prun_bind, prun_destroy in H. cbv beta iota in H. rewrite prun_bind, prun_free in H. cbv beta iota in H. rewrite prun_ret in H.
injection H as <- <-. split; reflexivity. }
destruct ((if h_channels h =? -1 then hd_nb_channels hd else h_channels h) =? 1) eqn:CH; cbn [negb] in H.
- unfold INT_MAX in H. change (2147483647 - 1) with 2147483646 in H.
destruct (2147483646 <? hd_extra_headers hd).
{ rewrite prun_bind, prun_destroy in H. cbv beta iota in H. rewrite prun_bind, prun_free in H. cbv beta iota in H. rewrite prun_ret in H.
injection H as <- <-. split; reflexivity. }
rewrite prun_bind, prun_free in H. cbv beta iota in H.
destruct (speex_decoder_ctl d3 CtlGetLookahead) as [x5 d5] eqn:C5. cbn [fst snd]. cbv beta iota in H. rewrite prun_ret in H. injection H as <- <-.
apply Z.eqb_eq in CH. rewrite CH. split; reflexivity.
- destruct (speex_decoder_ctl d3 CtlSetHandlerStereo) as [x4 d4] eqn:C4. cbn [fst snd]. cbv beta iota in H.
unfold INT_MAX in H. change (2147483647 - 1) with 2147483646 in H.
destruct (2147483646 <? hd_extra_headers hd).
{ rewrite prun_bind, prun_destroy in H. cbv beta iota in H. rewrite prun_bind, prun_free in H. cbv beta iota in H. rewrite prun_ret in H.
injection H as <- <-. split; reflexivity. }
rewrite prun_bind, prun_free in H. cbv beta iota in H.
destruct (speex_decoder_ctl d4 CtlGetLookahead) as [x5 d5] eqn:C5. cbn [fst snd]. cbv beta iota in H. rewrite prun_ret in H. injection H as <- <-.
split; reflexivity. }
assert (Q1 : q' = q1).
{ destruct (andb (0 <=? hd_mode hd) (hd_mode hd <? 3)) eqn:MR.
- apply andb_true_iff in MR as [M1 M2]. apply Z.leb_le in M1. apply Z.ltb_lt in M2. exact (proj2 (KEY (conj M1 M2))).
- unfold SPEEX_NB_MODES in H. replace ((3 <=? hd_mode hd) || (hd_mode hd <? 0)) with true in H.
+ rewrite prun_bind, prun_free in H. cbv beta iota in H. rewrite prun_ret in H. injection H as _ <-. reflexivity.
+ symmetry. apply andb_false_iff in MR as [M|M].
* apply Z.leb_gt in M. apply orb_true_intro. right. apply Z.ltb_lt. lia.
* apply Z.ltb_ge in M. apply orb_true_intro. left. apply Z.leb_le. lia. }
subst q'. split; [reflexivity|]. intros HM. exact (proj1 (KEY HM)).
Qed.

Lemma isave_init : forall mo, isave_ok (init_dec mo).
Proof. destruct mo; cbn; exact I. Qed.
Lemma isave_ctl : forall (d : dec_state bptr) r, (forall off, r <> CtlSetInnovationSave off) -> isave_ok d -> isave_ok (snd (speex_decoder_ctl d r)).
Proof.
intros d r NR H. destruct d as [st|s low]; destruct r; cbn in *; try exact H;
try (match goal with |- context [speex_decoder_ctl low ?rr] => destruct (speex_decoder_ctl low rr) as [v' low'] end; cbn; exact H);
try (exfalso; eapply NR; reflexivity).
Qed.
Lemma nested_init : forall mo, dec_nestedR (init_dec mo).
Proof. destruct mo; cbn; repeat split. Qed.
Lemma depth_init : forall mo, (dec_depth (init_dec mo) <= 3)%nat.
Proof. destruct mo; cbn; lia. Qed.
Lemma depth_ctl : forall (d : dec_state bptr) r, dec_depth (snd (speex_decoder_ctl d r)) = dec_depth d.
Proof. intros d r. apply speex_decoder_ctl_depth. Qed.

Lemma hpure_hdr : forall (X : hinv) (h : hstate unit) (d : dec_state unit) nf ch rate extra fs,
hpure X h -> h_packet_count h = 0 ->
0 <= fs <= 640 -> 1 <= nf <= 10 -> -2^31 <= ch < 2^31 -> -2^31 <= rate < 2^31 -> -2^31 <= extra < 2^31 - 1 ->
1 + (os_lacing_fill (h_os h) - os_lacing_returned (h_os h)) <= 162 * h_consumed X h -> os_lacing_returned (h_os h) <= os_lacing_fill (h_os h) ->
hpure X (incr_packet_count (set_header h d nf ch rate extra fs)).
Proof.
intros X h d nf ch rate extra fs HP PC0 FS NF CH RT EX BUD RF.
destruct HP as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22
& A23 & A24 & A25 & A26 & A27 & A28).
unfold hpure, h_consumed, h_pend in *. cbn [incr_packet_count set_header h_oy h_os h_bits h_st h_stream_init h_packet_count h_last_granule
h_skip_samples h_nframes h_eos h_channels h_rate h_extra_headers h_speex_serialno h_frame_size h_granule_frame_size h_bytes_remaining].
assert (NF' : (if nf =? 0 then 1 else nf) = nf) by (destruct (Z.eqb_spec nf 0); lia). rewrite NF'.
rewrite PC0 in *.
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7|].
split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact A14|]. split; [lia|].
split; [exact A16|]. split; [exact A17|]. split; [exact A18|]. split; [exact A19|]. split; [lia|].
split; [exact A21|]. split; [exact A22|]. split; [exact A23|]. split; [exact A24|]. split; [exact A25|]. split; [exact A26|]. split; lia.
Qed.

Definition init_cps_at8 (RT : rt_sig) (mo : spx_mode) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (lo : Z) (ras : list Z) (OUT STEREO : Z),
fdfs_only PMc -> mat_stable PMc ->
a0 = Z_to_bv 64 (sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode mo) -> tp = Z_to_bv 64 0x638c98 ->
Z.of_nat (length (rt_live RT Σ)) + init_nblocks mo <= LIVE_MAX -> init_credit mo <= rt_credit RT Σ ->
(length (rt_frames RT Σ) + mode_depth mo <= FRAMES_MAX)%nat ->
init_traces mo (bv_unsigned ra) ras -> uw_entry m s0 (bv_unsigned sp) lo ras ->
ART RT Σ m -> mem_inv bsegs m -> frm0 fc ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + init_stack mo <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 32 = 0 ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_speex_decoder_init m)))
(fun c => exists (Σ' : rts RT) (D : Z) (LBD : list block) (NEW : list (Z * Z)),
ASTA RT Σ' PMc (fun ms => exists m',
ret_stL (fun _ fc' => frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 D) m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [] m m'
/\ DREP OUT STEREO m' D (init_dec mo) LBD) c
/\ rt_live RT Σ' = NEW ++ rt_live RT Σ /\ Permutation NEW (blocks_live LBD) /\ List.NoDup (map blk_id LBD) /\ Z.of_nat (length NEW) = init_nblocks mo
/\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ - init_credit mo <= rt_credit RT Σ' <= rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ
/\ blocks_al8 LBD).

Section PkStepB.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis IO_drv : forall y, in_ranges IO_FP y -> ~ drv_cell y.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Variable X : hinv.
Hypothesis HX : hinv_ok OUT_rep IO_FP X.
Local Notation usp := (x_usp X). Local Notation S1 := (x_S1 X). Local Notation lo := (x_lo X). Local Notation F := (x_F X).
Local Notation sf := (x_sf X). Local Notation mR := (x_mR X).

Lemma outside_IO_of_WL : forall x, outside (h_WL IO_FP X) x -> outside IO_FP x.
Proof. intros x H. unfold h_WL in H. cbn [outside] in H. destruct H as (_ & _ & _ & H). exact H. Qed.

Lemma hsep_of_k : forall (Σ1 : rts RT) (m : mem) a (h : hstate unit) k, ART RT Σ1 m -> hsig_k RT X Σ1 a h k -> hsep X a h.
Proof using AF HX.
intros Σ1 m a h k ART1 HS. destruct HS as (EL & ND & PERM & EF & ES & _).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
assert (INF : In (F, 8%nat) (rt_frames RT Σ1)) by (rewrite EF; left; reflexivity).
destruct (af_frames_range RT AF Σ1 m F 8 ART1 INF) as (_ & _ & _ & FR).
destruct (af_fshadow_apart RT AF Σ1 m F 8 ART1 INF) as (FSH & _).
change (fs_size 8) with 16384 in FR, FSH. rewrite <- ESF, ESF2 in FSH.
pose proof (hi_lo _ _ _ HX) as (LW0 & _). rewrite <- ES in LW0.
split; [| split; [| exact (Permutation_NoDup (Permutation_map fst PERM) ND)]].
- intros p q Hin. pose proof (INL _ Hin) as Hl.
destruct (af_live_range RT AF Σ1 m p q ART1 Hl) as (P0 & P1 & P2).
split; [exact P0|]. split; [lia|]. split; [exact (FR p q Hl)|]. split; [exact (FSH p q Hl)|]. split; [exact P2|].
intros p' q' Hc. pose proof (Permutation_in _ (Permutation_sym PERM) Hin) as HinP. destruct (in_split _ _ HinP) as (l1 & l2 & E).
apply (af_live_disj RT AF Σ1 m p q p' q' l1 (l2 ++ x_live X) ART1). { rewrite EL, E, <- app_assoc. reflexivity. }
apply in_or_app. right. apply in_or_app. right. exact Hc.
- intros p1 q1 p2 q2 H1 H2 NE. exact (live_sep_gen RT AF Σ1 m p1 q1 p2 q2 ART1 (INL _ H1) (INL _ H2) NE).
Qed.

Lemma h_bits_shadow_at : forall m', rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) (x_mR X) m' -> ro_cells bsegs m' (shad (F + 8400)) bits_shadow.
Proof using HX IO_img.
intros m' PF'. pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
pose proof (h_shr_at OUT_rep IO_FP IO_img X HX m' PF') as B. destruct B as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
pose proof (bytes_at_sub m' (x_sf X + 16) HSH_R 1034 6 B ltac:(vm_compute; lia)) as B6.
assert (E6 : firstn 6 (skipn 1034 HSH_R) = repeat (Z_to_bv 8 0) 6) by (vm_compute; reflexivity).
rewrite E6 in B6. replace (x_sf X + 16 + Z.of_nat 1034) with (x_sf X + 1050) in B6 by (change (Z.of_nat 1034) with 1034; lia).
assert (ESB : shad (x_F X + 8400) = x_sf X + 1050)
by (rewrite (shad_aligned_add (x_F X) 8400 ltac:(clear - F64; Z.div_mod_to_equations; lia) ltac:(lia)), <- ESF; change (8400 / 8) with 1050; reflexivity).
rewrite ESB. unfold bits_shadow. split; [cbn; tauto|]. cbn [cells_bytes cbytes map repeat app]. exact B6.
Qed.

Lemma h_io_step_io : forall (m m' : mem) a (h : hstate unit) (Lv : list (Z * Z)) W,
hsep X a h -> rt_pres_fp Lv [(F, 8%nat)] S1 (W ++ IO_FP) m m' -> (forall e, In e (x_live X) -> In e Lv) -> fp_h X a h W -> drv_consts m' ->
rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) (x_mR X) m -> io_ssp m ->
rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) (x_mR X) m' /\ io_ssp m'.
Proof using HX IO_img IO_drv.
intros m m' a h Lv W HSP PR INC FPH DC PF SSP.
split.
- apply (pres_fp_trans _ _ _ _ (x_mR X) m m' PF). intros b Hb Ho. apply PR.
+ exact (aclient_mono _ _ _ Lv [(F, 8%nat)] S1 _ Hb INC (fun e He => He) ltac:(lia)).
+ apply outside_app_iff. split; [exact (fp_h_view OUT_rep IO_FP X HX a h W HSP FPH _ Hb Ho)| exact (outside_IO_of_WL _ Ho)].
- apply (io_ssp_pres_fp (W ++ IO_FP) Lv [(F, 8%nat)] S1 m m'); [| exact SSP| exact DC| exact PR].
intros x Hx. apply outside_app_iff. split.
+ apply (fp_h_static OUT_rep IO_FP X HX a h W HSP FPH). unfold B.X0r9.SSP_GUARD, SEGTOP_A in *. lia.
+ apply outside_of_not_in_ranges'. intros Hin. apply (IO_drv x Hin). unfold drv_cell. right; left; exact Hx.
Qed.

Lemma rng_out_blocks : forall (LBD : list block) A n, (forall b, In b LBD -> blk_addr b + blk_size b <= A \/ A + n <= blk_addr b) ->
rng_out (blocks_ivs LBD) A n.
Proof.
induction LBD as [|b LBD IH]; intros A n H; [apply rng_out_nil|]. cbn [blocks_ivs map].
apply rng_out_cons; [destruct (H b (or_introl eq_refl)); lia|]. apply IH. intros b' Hb'. exact (H b' (or_intror Hb')).
Qed.
End PkStepB.

Lemma pk_window : forall (m : mem) (Bd : Z) (body : list byte) (os : stream_st unit) (op : packet),
u8arr bsegs m Bd body -> B.X10q.body_pre (os_body os) body -> zlength (os_body os) = os_body_fill os ->
0 <= pk_off op -> 0 <= pk_bytes op -> pk_off op + pk_bytes op <= os_body_fill os ->
u8ro bsegs m (Bd + pk_off op) (firstn (Z.to_nat (pk_bytes op)) (skipn (Z.to_nat (pk_off op)) body))
/\ map bv_unsigned (firstn (Z.to_nat (pk_bytes op)) (skipn (Z.to_nat (pk_off op)) body)) = packet_data os op
/\ Z.of_nat (length (firstn (Z.to_nat (pk_bytes op)) (skipn (Z.to_nat (pk_off op)) body))) = pk_bytes op.
Proof.
intros m Bd body os op [UB _] [BP BL] ZL P0 P1 P2. unfold zlength in ZL.
assert (ON : (Z.to_nat (pk_off op) + Z.to_nat (pk_bytes op) <= length (os_body os))%nat) by lia.
split; [| split].
- unfold u8ro. rewrite <- (firstn_skipn (Z.to_nat (pk_off op)) body) in UB. apply bytes_at_app in UB as [_ UB].
rewrite <- (firstn_skipn (Z.to_nat (pk_bytes op)) (skipn (Z.to_nat (pk_off op)) body)) in UB. apply bytes_at_app in UB as [UB _].
rewrite length_firstn in UB. replace (Bd + Z.of_nat (Nat.min (Z.to_nat (pk_off op)) (length body))) with (Bd + pk_off op) in UB by lia. exact UB.
- unfold packet_data, zslice, ztake, zdrop. rewrite <- BP. unfold ubytes.
rewrite skipn_firstn_comm, firstn_firstn. replace (Nat.min (Z.to_nat (pk_bytes op)) (length (os_body os) - Z.to_nat (pk_off op))) with (Z.to_nat (pk_bytes op)) by lia.
rewrite skipn_map, firstn_map. reflexivity.
- rewrite length_firstn, length_skipn. lia.
Qed.

Section Hdr.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis IO_drv : forall y, in_ranges IO_FP y -> ~ drv_cell y.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.
Variable X : hinv.
Hypothesis HX : hinv_ok OUT_rep IO_FP X.
Variable F0 : list (word * FdEntry).
Variable fs0 : Fs.Fs.
Local Notation usp := (x_usp X). Local Notation S1 := (x_S1 X). Local Notation lo := (x_lo X). Local Notation F := (x_F X).
Local Notation sf := (x_sf X). Local Notation mR := (x_mR X).
Local Notation PMh := (PMfd F0 fs0).

Definition W_h : list (Z * Z) :=
[(S1, S1 + 248); (sf, sf + 16); (F + 32, F + 88); (F + 8384, F + 8388); (F + 9232, F + 9236); (F + 9248, F + 9252)].

Lemma fp_h_Wh : forall a h, fp_h X a h W_h.
Proof.
intros a h. unfold W_h.
repeat (apply fp_h_cons; [unfold iv_h; first [left; lia | right; left; lia | right; right; left; lia] |]). apply fp_h_nil.
Qed.

Lemma h_uw_chain : forall m, rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) mR m -> uw_chain USTACK_TOP m S1 usp [0x96650].
Proof using HX IO_img.
intros m PF. pose proof (h_saves_at OUT_rep IO_FP IO_img X HX m PF) as SV. unfold h_saves in SV.
change [C8 (x_s11 X); C8 (x_s10 X); C8 (x_s9 X); C8 (x_s8 X); C8 (x_s7 X); C8 (x_s6 X); C8 (x_s5 X); C8 (x_s4 X); C8 (x_s3 X); C8 (x_s2 X);
C8 (x_s1 X); C8 (x_s0 X); C8 (x_ra X)]
with ([C8 (x_s11 X); C8 (x_s10 X); C8 (x_s9 X); C8 (x_s8 X); C8 (x_s7 X); C8 (x_s6 X); C8 (x_s5 X); C8 (x_s4 X); C8 (x_s3 X); C8 (x_s2 X);
C8 (x_s1 X)] ++ [C8 (x_s0 X); C8 (x_ra X)]) in SV.
apply rw_cells_app in SV as [_ SV]. cbn [cells_size csize Nat.add] in SV.
replace (usp + -104 + Z.of_nat 88) with (usp + -16) in SV by lia.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & _).
apply (uw_chain_push USTACK_TOP m S1 usp (bv_unsigned (x_s0 X)) 0x96650 []); [lia| clear - U16; Z.div_mod_to_equations; lia| unfold USTACK_TOP in *; lia| apply bv_unsigned_in_range| |].
- rewrite Z_to_bv_bv_unsigned. rewrite (hi_ra _ _ _ HX) in SV. exact SV.
- apply uw_chain_base. destruct (hi_s0 _ _ _ HX) as [H|[H|H]]; [left; lia| right; left; exact H| right; right; exact H].
Qed.

Lemma h_unwind : forall m site, rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) mR m -> In [site; 0x96650] SITE_TRACES -> 0 <= site < 2^64 ->
unwind_ch m (Z64 site) (Z64 usp) (Z64 S1).
Proof using HX IO_img.
intros m site PF IN SR. pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SRR & _).
exists [0x96650]. rewrite !unsigned_lit by (unfold USTACK_TOP in *; lia). split; [exact IN| exact (h_uw_chain m PF)].
Qed.

Lemma new_not_client : forall (Σ : rts RT) (m : mem) L Lold p n x,
ART RT Σ m -> rt_live RT Σ = L ++ Lold -> rt_frames RT Σ = [(F, 8%nat)] -> rt_sp0 RT Σ = x_sp0 X ->
In (p, n) L -> p <= x < p + n -> ~ aclient Lold [(F, 8%nat)] S1 x.
Proof using AF HX.
intros Σ m L Lold p n x ART0 EL EF ES Hin Hx Hc.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
assert (INL : In (p, n) (rt_live RT Σ)) by (rewrite EL; apply in_or_app; left; exact Hin).
assert (INF : In (F, 8%nat) (rt_frames RT Σ)) by (rewrite EF; left; reflexivity).
destruct (af_live_range RT AF Σ m p n ART0 INL) as (P0 & P1 & P2).
destruct (af_frames_range RT AF Σ m F 8 ART0 INF) as (_ & _ & _ & FR).
destruct (af_fshadow_apart RT AF Σ m F 8 ART0 INF) as (FSH & _).
change (fs_size 8) with 16384 in FR, FSH. rewrite <- ESF, ESF2 in FSH.
rewrite ES in P1. unfold RT_STACK, H_STACK in LR.
destruct Hc as [H|[H|[H|[H|H]]]].
- lia.
- pose proof (client_static_range _ H). unfold SEGTOP_A in *. lia.
- destruct H as (p' & q' & Hin' & H'). destruct (in_split _ _ Hin) as (l1 & l2 & E).
destruct (af_live_disj RT AF Σ m p n p' q' l1 (l2 ++ Lold) ART0) as [D|D]; [rewrite EL, E, <- app_assoc; reflexivity| |lia|lia].
apply in_or_app. right. apply in_or_app. right. exact Hin'.
- destruct H as (f & k & [E|[]] & H'). injection E as <- <-. change (fs_size 8) with 16384 in H'. destruct (FR p n INL); lia.
- destruct H as (f & k & [E|[]] & H'). injection E as <- <-. change (fs_size 8) with 16384 in H'. rewrite <- ESF, ESF2 in H'.
destruct (FSH p n INL); lia.
Qed.

Lemma art_munch_h : forall (Σ : rts RT) (m m1 : mem) W,
ART RT Σ m -> rt_frames RT Σ = [(F, 8%nat)] -> rt_sp0 RT Σ = x_sp0 X ->
munch W m m1 -> wmono bsegs m m1 ->
(forall lo' hi', In (lo', hi') W -> (S1 <= lo' /\ hi' <= USTACK_TOP) \/ (sf <= lo' /\ hi' <= sf + 2048) \/ (F <= lo' /\ hi' <= F + 16376)) ->
ART RT Σ m1.
Proof using AF HX.
intros Σ m m1 W ART0 EF ES MU WM HW.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
apply (af_frame RT AF Σ m m1 S1 ART0); [rewrite ES; unfold RT_STACK, H_STACK in LR; lia| | exact WM].
intros b Hb. apply MU. apply outside_intro. intros l hh Hin Hx. apply Hb. rewrite EF.
destruct (HW l hh Hin) as [H|[H|H]].
- left. lia.
- right; right; right; right. exists F, 8%nat. split; [left; reflexivity|]. change (fs_size 8) with 16384. rewrite <- ESF, ESF2. lia.
- right; right; right; left. exists F, 8%nat. split; [left; reflexivity|]. change (fs_size 8) with 16384. lia.
Qed.

Lemma pf_munch_h : forall (L : list (Z * Z)) (m m1 : mem) W W',
munch W m m1 -> (forall x, outside W' x -> outside W x) -> rt_pres_fp L [(F, 8%nat)] S1 W' m m1.
Proof. intros L m m1 W W' MU HW. apply (pres_fp_of_munch _ _ _ _ _ m m1 MU). intros x _ Ho. exact (HW x Ho). Qed.

Lemma own_pos_h : forall (m : mem) a (h : hstate unit), h_os_rep X m a h -> h_dec_rep X m a h -> hpure X h ->
forall p q, In (p, q) (h_own a h) -> 0 < q.
Proof.
intros m a h OSR DEC HP p q Hin.
unfold h_own in Hin. apply in_app_or in Hin as [Hin|Hin].
- unfold h_dec_rep in DEC. destruct (h_st h) as [d|]; [| destruct Hin].
destruct DEC as (R & _). unfold blocks_live in Hin. apply in_map_iff in Hin as (b & E & Hb). injection E as <- <-.
exact (h_drep_sizes_pos d _ _ m _ _ R b Hb).
- apply in_app_or in Hin as [[E|[]]|Hin].
{ injection E as <- <-. destruct HP as (_ & _ & _ & _ & _ & _ & B & _). lia. }
apply in_app_or in Hin as [Hin|Hin].
+ unfold h_os_rep in OSR. destruct (h_stream_init h =? 0); [destruct Hin|].
destruct OSR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L0 & B0 & _).
destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
+ destruct (sy_data (h_oy h)) eqn:ED; [| destruct Hin]. destruct Hin as [E|[]]. injection E as <- <-.
destruct HP as (_ & _ & (S0 & _) & (DN & ND) & _). destruct (Z.eq_dec (sy_storage (h_oy h)) 0) as [Z0|NZ]; [| lia].
specialize (ND Z0). congruence.
Qed.

Lemma own_xlive_ne : forall a (h : hstate unit), hsep X a h -> (forall p q, In (p, q) (h_own a h) -> 0 < q) ->
forall p q, In (p, q) (h_own a h) -> forall e, In e (x_live X) -> fst e <> p.
Proof using HX.
intros a h HSP OPOS p q Hin [q' k'] Hq E. cbn [fst] in E. subst q'.
destruct (proj1 HSP _ _ Hin) as (_ & _ & _ & _ & _ & SEP). pose proof (OPOS _ _ Hin) as P1.
pose proof (proj1 (hi_live _ _ _ HX) _ _ Hq) as P2. destruct (SEP _ _ Hq); lia.
Qed.

Lemma h_lrl_app : forall ps l1 l2, live_remove_list ps (l1 ++ l2) = live_remove_list ps l1 ++ live_remove_list ps l2.
Proof. induction ps as [|p ps IH]; intros l1 l2; [reflexivity|]. cbn [live_remove_list fold_right]. unfold live_remove_list in IH. rewrite IH. apply live_remove_app. Qed.
Lemma h_lrl_all : forall ps l, (forall e, In e l -> In (fst e) ps) -> live_remove_list ps l = [].
Proof.
intros ps l H. destruct (live_remove_list ps l) as [|e l'] eqn:E; [reflexivity|]. exfalso.
assert (He : In e (live_remove_list ps l)) by (rewrite E; left; reflexivity).
pose proof (live_remove_list_sub _ _ _ He) as He1. pose proof (H e He1) as Hin.
clear E H He1. revert l He. induction ps as [|p ps IH]; intros l He; [destruct Hin|]. cbn [live_remove_list fold_right] in He.
apply live_remove_in in He as (He & NE). destruct Hin as [E|Hin]; [exact (NE (eq_sym E))| exact (IH Hin l He)].
Qed.
Lemma h_lrl_none : forall ps l, (forall e, In e l -> ~ In (fst e) ps) -> live_remove_list ps l = l.
Proof.
induction ps as [|p ps IH]; intros l H; [reflexivity|]. cbn [live_remove_list fold_right]. unfold live_remove_list in IH.
rewrite IH by (intros e He Hin; apply (H e He); right; exact Hin). apply live_remove_none. intros e He E. apply (H e He). left. symmetry. exact E.
Qed.
Lemma h_lrl_perm : forall ps l l', Permutation l l' -> Permutation (live_remove_list ps l) (live_remove_list ps l').
Proof. induction ps as [|p ps IH]; intros l l' P; [exact P|]. cbn [live_remove_list fold_right]. apply perm_live_remove. apply IH. exact P. Qed.

Hypothesis BDES : speex_bits_destroy_cps RT.
Hypothesis SCLR : ogg_stream_clear_cps RT.
Hypothesis YCLR : ogg_sync_clear_cps RT.

Lemma hp_tail_ok : forall (h : hstate unit) (a : haux) (k : Z) (Σ : rts RT) (m : mem) (cc : config) T
(ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 : word) Fr fc
(w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w120 w128 w136 w144 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 : word),
ASTA RT Σ PMh (eq (MS (mkR ra (Z64 S1) (x_gp X) (Z64 0x638c98) t0 t1 t2 (Z64 usp) (Z64 S1) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z64 sf) s4 s5 (Z64 (-8)) s7 s8 s9 (Z64 (F + HO_BITS)) s11 t3 t4 t5 t6)
Fr (Z64 0x9744c) fc None m (seg_rom bsegs))) cc ->
X1cn.frm0 fc -> hsig_k RT X Σ a h k -> h_cost h + k <= FUZZ_COST - 1 -> h_st h = None -> h_stream_init h = 1 -> hpure X h ->
ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo S1 ->
rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) mR m -> ERR_rep m -> (forall so, OUT_rep so mR -> OUT_rep so m) -> io_ssp m ->
rw_cells bsegs m S1 (hsp (Z64 (sf + 16)) (Z64 F) (Z64 F) w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 (Z64 (F + HO_OY)) w120 w128 w136 w144
(Z64 (F + HO_OS)) w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 (Z64 F)) ->
rw_cells bsegs m sf [CB 16 HSH_L_HDR] ->
bits_rep bsegs m (F + HO_BITS) (a_Dc a) (h_bits h) -> h_os_rep X m a h -> sync_rep m (F + HO_OY) (a_Dsy a) (h_oy h) (a_sybytes a) ->
h_dec_rep X m a h ->
(forall c', at_XT RT OUT_rep ERR_rep IO_FP X F0 fs0 c' -> realizes bsegs c' T) ->
realizes bsegs cc T.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV BDES SCLR YCLR.
intros h a k Σ m cc T ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc
w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w120 w128 w136 w144 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232
Hc FRM HS KC STN SI1 HP ART0 MI ST PF ERR OUTR SSP SP LSH BITS OSR SY DEC Hk.
pose proof (hsep_of_k RT AF OUT_rep IO_FP X HX Σ m a h k ART0 HS) as HSP.
assert (DN : a_S a = 0 /\ a_LBD a = []) by (unfold h_dec_rep in DEC; rewrite STN in DEC; exact DEC). clear DEC.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
pose proof hsp_size as HSPS.

refine (rz_evt RT AF Σ PMh _ _ T cc (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply hp_f4; [unfold SH_LO, SH_HI in *; lia | exact LSH | exact MI]. }
intros ms1 cc1 (m1 & -> & MU1 & WM1 & MI1 & LSH1) Hc1. clear Hc.
assert (PR1 : rt_pres_fp (rt_live RT Σ) [(F, 8%nat)] S1 [(sf, sf + 16)] m m1) by (apply (pf_munch_h _ m m1 _ _ MU1); intros x Hx; exact Hx).
pose proof (art_munch_h Σ m m1 _ ART0 EF ESP MU1 WM1 ltac:(intros l hh [E|[]]; injection E as <- <-; right; left; lia)) as ART1.
assert (FPH1 : fp_h X a h [(sf, sf + 16)]) by (apply fp_h_cons; [right; left; lia| apply fp_h_nil]).
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ m m1 a h _ _ HSP PR1
ltac:(intros e He; rewrite EL; apply in_or_app; right; exact He) FPH1 (AF_DRV _ _ ART1) PF ERR OUTR SSP) as (PF1 & ERR1 & OUTR1 & SSP1).
eapply (htr_rw _ _ _ _ m m1 PR1) in SP; rewrite ?HSPS; [| apply acl_stack; unfold USTACK_TOP in *; lia| apply rng_out_cons; [unfold SH_LO, SH_HI in *; lia| apply rng_out_nil]].
assert (OWNTR : forall p q, In (p, q) (h_own a h) -> acl_rng (rt_live RT Σ) [(F, 8%nat)] S1 p q /\ rng_out [(sf, sf + 16)] p q).
{ intros p q Hin. split; [apply (acl_live _ _ _ _ _ _ _ (INL _ Hin)); lia|].
apply rng_out_cons; [apply (iv_own_fshadow X a h HSP _ _ _ _ _ _ Hin); lia|]. apply rng_out_nil. }
assert (BOK : bits_ok (h_bits h)) by (destruct HP as (_ & _ & _ & _ & B & _); exact B).
assert (BITS1 : bits_rep bsegs m1 (F + HO_BITS) (a_Dc a) (h_bits h)).
{ destruct (OWNTR _ _ (own_in_Dc a h)) as (D1 & D2). unfold HO_BITS in *.
apply (bits_rep_tr _ _ _ _ m m1 PR1 _ _ _ BITS BOK); [| | exact D1| exact D2].
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [unfold SH_LO, SH_HI in *; lia|]. apply rng_out_nil. }
assert (SY1 : sync_rep m1 (F + HO_OY) (a_Dsy a) (h_oy h) (a_sybytes a)).
{ unfold HO_OY in *. apply (sync_rep_tr _ _ _ _ m m1 PR1 _ _ _ _ SY).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [unfold SH_LO, SH_HI in *; lia|]. apply rng_out_nil.
- intros NS. exact (OWNTR _ _ (own_in_Dsy a h NS)). }
assert (OSR1 : h_os_rep X m1 a h).
{ apply (h_os_rep_tr _ _ _ _ m m1 PR1 X a h OSR).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- unfold HO_OS. apply rng_out_cons; [unfold SH_LO, SH_HI in *; lia|]. apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
destruct (OWNTR _ _ IB) as (B1 & B2). destruct (OWNTR _ _ IL) as (L1 & L2). destruct (OWNTR _ _ IG) as (G1 & G2).
exact (conj B1 (conj B2 (conj L1 (conj L2 (conj G1 G2))))). }
clear BITS SY OSR PR1 OWNTR.
assert (ST1 : stk bsegs m1 lo S1).
{ apply (stk_agree bsegs m m1 lo S1 ST); [| exact WM1]. apply (agree_of_munch _ m m1 _ MU1). intros x Hx. cbn [outside].
split; [unfold SH_LO, SH_HI in *; lia| exact I]. }
clear MU1 WM1 ST PF ERR OUTR SSP LSH MI ART0.

assert (BSH1 : ro_cells bsegs m1 (shad (F + 8400)) bits_shadow) by exact (h_bits_shadow_at OUT_rep IO_FP IO_img X HX m1 PF1).
assert (INF1 : In (F, 8%nat) (rt_frames RT Σ)) by (rewrite EF; left; reflexivity).
pose proof (INL _ (own_in_Dc a h)) as INDc.
pose proof (h_unwind m1 0x97470 PF1 ltac:(clear; vm_compute; tauto) ltac:(lia)) as UW1.
unfold HO_BITS in BITS1. unfold A_bdes_hp in Hc1.
cps_rt (BDES Σ PMh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (F + 8400) (a_Dc a) F lo 8%nat (h_bits h)).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ destruct HP as (_ & _ & _ & _ & _ & B & _). exact B. }
{ change (fs_size 8) with 16384. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). exact ST1. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold RT_STACK. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). clear - S32. Z.div_mod_to_equations. lia. }
intros cc2 (Σ2 & Hc2 & EL2 & EF2 & ES2 & EC2 & EP2). clear Hc1.
cps_unpack_lib Hc2 as (v2 & m2 & RS & RA2 & PR2).
destruct RS as (-> & ->).
destruct RA2 as (ART2 & MI2 & ST2).
rewrite EF in PR2.

assert (DEC1 : h_dec_rep X m1 a h) by (unfold h_dec_rep; rewrite STN; exact DN).
pose proof (own_pos_h m1 a h OSR1 DEC1 HP) as OPOS. clear DEC1.
pose proof (own_xlive_ne a h HSP OPOS) as XNE.
assert (NDc : forall p q, In (p, q) (h_own a h) -> p <> a_Dc a -> In (p, q) (rt_live RT Σ2)).
{ intros p q Hin NE. rewrite EL2. apply live_remove_keep; [exact (INL _ Hin)| exact NE]. }
assert (XL2 : forall e, In e (x_live X) -> In e (rt_live RT Σ2)).
{ intros e He. rewrite EL2. apply live_remove_keep; [rewrite EL; apply in_or_app; right; exact He| exact (XNE _ _ (own_in_Dc a h) e He)]. }
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ m1 m2 a h _ _ HSP PR2 XL2 (fp_h_nil X a h) (AF_DRV _ _ ART2) PF1 ERR1 OUTR1 SSP1)
as (PF2 & ERR2 & OUTR2 & SSP2).
eapply (htr_rw _ _ _ _ m1 m2 PR2) in SP; rewrite ?HSPS; [| apply acl_stack; unfold USTACK_TOP in *; lia| apply rng_out_nil].
eapply (htr_rw _ _ _ _ m1 m2 PR2) in LSH1; cbn [cells_size csize Nat.add];
[| apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia| apply rng_out_nil].
pose proof (own_ne_Dsy a h (proj2 (proj2 HSP))) as ONE.
assert (OSN : forall p, In p [a_Bd a; a_L a; a_G a] -> p <> a_Dc a).
{ intros p Hp. pose proof (proj2 (proj2 HSP)) as ND1. unfold h_own in ND1. rewrite STN in ND1. cbn [app] in ND1.
replace (h_stream_init h =? 0) with false in ND1 by (rewrite SI1; reflexivity). cbn [map fst app] in ND1.
apply NoDup_cons_iff in ND1 as (N1 & _). intros E. subst p. apply N1. destruct Hp as [E|[E|[E|[]]]]; rewrite <- E; cbn [In]; repeat (first [left; reflexivity | right]). }
assert (OSR2 : h_os_rep X m2 a h).
{ apply (h_os_rep_tr _ _ _ _ m1 m2 PR2 X a h OSR1).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
split; [apply (acl_live _ _ _ _ _ _ _ (NDc _ _ IB (OSN _ (or_introl eq_refl)))); lia|]. split; [apply rng_out_nil|].
split; [apply (acl_live _ _ _ _ _ _ _ (NDc _ _ IL (OSN _ (or_intror (or_introl eq_refl))))); lia|]. split; [apply rng_out_nil|].
split; [apply (acl_live _ _ _ _ _ _ _ (NDc _ _ IG (OSN _ (or_intror (or_intror (or_introl eq_refl)))))); lia| apply rng_out_nil]. }
assert (SY2 : sync_rep m2 (F + HO_OY) (a_Dsy a) (h_oy h) (a_sybytes a)).
{ apply (sync_rep_tr _ _ _ _ m1 m2 PR2 _ _ _ _ SY1).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OY; lia.
- apply rng_out_nil.
- intros NS. destruct (ONE NS) as (N1 & _). split; [| apply rng_out_nil].
apply (acl_live _ _ _ _ _ _ _ (NDc _ _ (own_in_Dsy a h NS) (not_eq_sym N1))); unfold bptr in *; lia. }
clear OSR1 SY1 PR2.

refine (rz_evt RT AF Σ2 PMh _ _ T cc2 (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply hp_f5; [reflexivity | unfold USTACK_TOP in *; lia | exact SP | exact MI2]. }
intros ms3 cc3 -> Hc3. clear Hc.
pose proof OSR2 as OSR2'. unfold h_os_rep in OSR2'. replace (h_stream_init h =? 0) with false in OSR2' by (rewrite SI1; reflexivity).
destruct OSR2' as (OSC & LSH0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & LS0 & BS0 & BL & BG & LG & _).
assert (SIN : h_stream_init h <> 0) by (rewrite SI1; discriminate).
destruct (own_in_os a h SIN) as (IB & IL & IG).
assert (SLV : stream_live RT Σ2 (h_os h) (a_Bd a) (a_L a) (a_G a)).
{ split; [exact (NDc _ _ IB (OSN _ (or_introl eq_refl)))|]. split; [exact (NDc _ _ IL (OSN _ (or_intror (or_introl eq_refl))))|].
split; [exact (NDc _ _ IG (OSN _ (or_intror (or_intror (or_introl eq_refl)))))|]. split; [exact BL|]. split; [exact BG| exact LG]. }
pose proof (h_acc_at OUT_rep IO_FP IO_img X HX m2 PF2) as (_ & _ & _ & _ & _ & _ & ACOS & _).
assert (INF2 : In (F, 8%nat) (rt_frames RT Σ2)) by (rewrite EF2, EF; left; reflexivity).
unfold HO_OS in OSC, ACOS. unfold A_sclr_hp in Hc3.
cps_rt (SCLR Σ2 PMh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 (F + 8688) (a_Bd a) (a_L a) (a_G a) F lo 8%nat
(h_os h) (a_shdr a)).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ unfold bptr in *. lia. }
{ unfold bptr in *. lia. }
{ change (fs_size 8) with 16384. lia. }
{ first [exact ST2 | rewrite unsigned_lit by (unfold USTACK_TOP in *; lia); exact ST2]. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold RT_STACK. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). clear - S32. Z.div_mod_to_equations. lia. }
intros cc4 (Σ3 & Hc4 & EL3 & EF3 & ES3 & EC3 & EP3). clear Hc3.
cps_unpack_lib Hc4 as (m3 & RS & RA3 & PR3 & OSC3).
destruct RS as (-> & ->).
destruct RA3 as (ART3 & MI3 & ST3).
rewrite EF2, EF in PR3.
assert (XL3 : forall e, In e (x_live X) -> In e (rt_live RT Σ3)).
{ intros e He. rewrite EL3. apply live_remove_keep; [apply live_remove_keep; [apply live_remove_keep; [exact (XL2 e He)|]|]|].
- exact (XNE _ _ IB e He). - exact (XNE _ _ IL e He). - exact (XNE _ _ IG e He). }
assert (PR3S : rt_pres_fp (rt_live RT Σ3) [(F, 8%nat)] S1 [(F + 8688, F + 8688 + 408)] m2 m3) by (rewrite EL3; exact PR3).
assert (FPH3 : fp_h X a h [(F + 8688, F + 8688 + 408)]) by (apply fp_h_cons; [right; right; left; lia| apply fp_h_nil]).
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ2 m2 m3 a h _ _ HSP PR3S XL3 FPH3 (AF_DRV _ _ ART3) PF2 ERR2 OUTR2 SSP2)
as (PF3 & ERR3 & OUTR3 & SSP3).
eapply (htr_rw _ _ _ _ m2 m3 PR3S) in SP; rewrite ?HSPS; [| apply acl_stack; unfold USTACK_TOP in *; lia| apply rng_out_cons; [lia| apply rng_out_nil]].
eapply (htr_rw _ _ _ _ m2 m3 PR3S) in LSH1; cbn [cells_size csize Nat.add];
[| apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia| apply rng_out_cons; [lia| apply rng_out_nil]].
assert (NDsy : sy_data (h_oy h) <> None -> forall p, In p [a_Bd a; a_L a; a_G a; a_Dc a] -> p <> a_Dsy a).
{ intros NS p Hp. destruct (ONE NS) as (N1 & N2 & _). destruct (N2 SIN) as (B & L & G).
destruct Hp as [<-|[<-|[<-|[<-|[]]]]]; congruence. }
assert (SYL3 : sy_data (h_oy h) <> None -> In (a_Dsy a, sy_storage (h_oy h)) (rt_live RT Σ3)).
{ intros NS. pose proof (own_in_Dsy a h NS) as INS. rewrite EL3.
apply live_remove_keep; [apply live_remove_keep; [apply live_remove_keep; [apply (NDc _ _ INS); exact (not_eq_sym (NDsy NS _ (or_intror (or_intror (or_intror (or_introl eq_refl))))))|]|]|];
cbn [fst]; intros E; symmetry in E; revert E; apply (NDsy NS); cbn [In]; repeat (first [left; reflexivity | right]). }
assert (SY3 : sync_rep m3 (F + HO_OY) (a_Dsy a) (h_oy h) (a_sybytes a)).
{ apply (sync_rep_tr _ _ _ _ m2 m3 PR3S _ _ _ _ SY2).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OY; lia.
- unfold HO_OY. apply rng_out_cons; [lia| apply rng_out_nil].
- intros NS. pose proof (own_in_Dsy a h NS) as INS. split.
+ apply (acl_live _ _ _ _ _ _ _ (SYL3 NS)); unfold bptr in *; lia.
+ unfold bptr in *. apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ INS); lia| apply rng_out_nil]. }
clear SY2 PR3 PR3S.

refine (rz_evt RT AF Σ3 PMh _ _ T cc4 (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply hp_f6; [reflexivity | unfold USTACK_TOP in *; lia | exact SP | exact MI3]. }
intros ms5 cc5 -> Hc5. clear Hc.
assert (INF3 : In (F, 8%nat) (rt_frames RT Σ3)) by (rewrite EF3, EF2, EF; left; reflexivity).
unfold A_yclr_hp in Hc5. unfold HO_OY in SY3.
cps_rt (YCLR Σ3 PMh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 (F + 8480) (a_Dsy a) F lo 8%nat (h_oy h) (a_sybytes a)).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ change (fs_size 8) with 16384. lia. }
{ first [exact ST3 | rewrite unsigned_lit by (unfold USTACK_TOP in *; lia); exact ST3]. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold RT_STACK. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). clear - S32. Z.div_mod_to_equations. lia. }
intros cc6 (Σ4 & Hc6 & EL4 & EF4 & ES4 & EC4 & EP4). clear Hc5.
cps_unpack_lib Hc6 as (m4 & RS & RA4 & PR4 & SY4).
destruct RS as (-> & ->).
destruct RA4 as (ART4 & MI4 & ST4).

assert (OWNL : forall e, In e (a_P a) -> fst e = a_Dc a \/ fst e = a_Bd a \/ fst e = a_L a \/ fst e = a_G a \/ (sy_data (h_oy h) <> None /\ fst e = a_Dsy a)).
{ intros e He. pose proof (Permutation_in _ PERM He) as Ho. unfold h_own in Ho. rewrite STN in Ho. cbn [app] in Ho.
replace (h_stream_init h =? 0) with false in Ho by (rewrite SI1; reflexivity).
destruct Ho as [E|[E|[E|[E|Ho]]]]; [left| right; left| right; right; left| right; right; right; left| ]; try (rewrite <- E; reflexivity).
right; right; right; right. destruct (sy_data (h_oy h)) eqn:ED; [| destruct Ho]. destruct Ho as [E|[]]. split; [discriminate| rewrite <- E; reflexivity]. }
assert (ELX : rt_live RT Σ4 = x_live X).
{ rewrite EL4, EL3, EL2, EL. unfold sync_clear_live, bptr.
change (live_remove (a_G a) (live_remove (a_L a) (live_remove (a_Bd a) (live_remove (a_Dc a) (a_P a ++ x_live X)))))
with (live_remove_list [a_G a; a_L a; a_Bd a; a_Dc a] (a_P a ++ x_live X)).
destruct (sy_data (h_oy h)) eqn:ED.
- change (live_remove (a_Dsy a) (live_remove_list [a_G a; a_L a; a_Bd a; a_Dc a] (a_P a ++ x_live X)))
with (live_remove_list [a_Dsy a; a_G a; a_L a; a_Bd a; a_Dc a] (a_P a ++ x_live X)).
rewrite h_lrl_app, h_lrl_all, h_lrl_none; [reflexivity| |].
+ intros e He Hin. cbn [In] in Hin.
destruct Hin as [E|[E|[E|[E|[E|[]]]]]];
[ exact (XNE _ _ (own_in_Dsy a h ltac:(rewrite ED; discriminate)) e He (eq_sym E))
| exact (XNE _ _ IG e He (eq_sym E)) | exact (XNE _ _ IL e He (eq_sym E)) | exact (XNE _ _ IB e He (eq_sym E))
| exact (XNE _ _ (own_in_Dc a h) e He (eq_sym E)) ].
+ intros e He. destruct (OWNL e He) as [E|[E|[E|[E|(_ & E)]]]]; rewrite E;
[ exact (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))
| exact (or_intror (or_intror (or_intror (or_introl eq_refl))))
| exact (or_intror (or_intror (or_introl eq_refl)))
| exact (or_intror (or_introl eq_refl))
| exact (or_introl eq_refl) ].
- rewrite h_lrl_app, h_lrl_all, h_lrl_none; [reflexivity| |].
+ intros e He Hin. cbn [In] in Hin.
destruct Hin as [E|[E|[E|[E|[]]]]];
[ exact (XNE _ _ IG e He (eq_sym E)) | exact (XNE _ _ IL e He (eq_sym E)) | exact (XNE _ _ IB e He (eq_sym E))
| exact (XNE _ _ (own_in_Dc a h) e He (eq_sym E)) ].
+ intros e He. destruct (OWNL e He) as [E|[E|[E|[E|(NS & E)]]]]; [rewrite E .. | exfalso; exact (NS eq_refl)].
* exact (or_intror (or_intror (or_intror (or_introl eq_refl)))).
* exact (or_intror (or_intror (or_introl eq_refl))).
* exact (or_intror (or_introl eq_refl)).
* exact (or_introl eq_refl). }
rewrite EF3, EF2, EF in PR4. rewrite <- EL4, ELX in PR4.
assert (FPH4 : fp_h X a h [(F + 8480, F + 8480 + 32)]) by (apply fp_h_cons; [right; right; left; lia| apply fp_h_nil]).
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ3 m3 m4 a h _ _ HSP PR4 (fun e He => He) FPH4 (AF_DRV _ _ ART4) PF3 ERR3 OUTR3 SSP3)
as (PF4 & ERR4 & OUTR4 & _).
eapply (htr_rw _ _ _ _ m3 m4 PR4) in SP; rewrite ?HSPS; [| apply acl_stack; unfold USTACK_TOP in *; lia| apply rng_out_cons; [lia| apply rng_out_nil]].
eapply (htr_rw _ _ _ _ m3 m4 PR4) in LSH1; cbn [cells_size csize Nat.add];
[| apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia| apply rng_out_cons; [lia| apply rng_out_nil]].

refine (rz_evt RT AF Σ4 PMh _ _ T cc6 (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply hp_f7; [reflexivity | exact MI4]. }
intros ms7 cc7 -> Hc7. clear Hc.
apply Hk. unfold at_XT.
do 55 eexists.
split; [exact Hc7|]. split; [exact FRM|]. split; [exact ELX|]. split; [rewrite EF4, EF3, EF2; exact EF|]. split; [rewrite ES4, ES3, ES2; exact ESP|].
split; [rewrite EP4, EP3, EP2; exact EPO0|]. split; [rewrite EC4, EC3, EC2; lia|].
split; [exact ART4|]. split; [exact MI4|]. split; [first [exact ST4 | rewrite unsigned_lit in ST4 by (unfold USTACK_TOP in *; lia); exact ST4]|].
split; [exact PF4|]. split; [exact ERR4|]. split; [exact OUTR4|]. split; [exact SP| exact LSH1].
Qed.

Definition hsig_x (Σ : rts RT) (a : haux) (h : hstate unit) (k : Z) (L : list (Z * Z)) : Prop :=
rt_live RT Σ = L ++ a_P a ++ x_live X /\ List.NoDup (map fst (a_P a)) /\ Permutation (a_P a) (h_own a h)
/\ rt_frames RT Σ = [(F, 8%nat)] /\ rt_sp0 RT Σ = x_sp0 X /\ rt_pois RT Σ = [] /\ x_cr0 X - h_cost h - k <= rt_credit RT Σ.
Lemma hsig_x_nil : forall Σ a h k, hsig_x Σ a h k [] -> hsig_k RT X Σ a h k.
Proof. intros Σ a h k (A1 & A2 & A3 & A4 & A5 & A6 & A7). unfold hsig_k. repeat split; assumption. Qed.

Lemma live_remove_top : forall (Σ : rts RT) (m : mem) p n R, ART RT Σ m -> rt_live RT Σ = (p, n) :: R -> 0 < n ->
(forall e, In e R -> 0 < snd e) -> live_remove p ((p, n) :: R) = R.
Proof using AF.
intros Σ m p n R ART0 EL N0 RP. rewrite live_remove_cons. cbn [fst]. rewrite Z.eqb_refl. apply live_remove_none.
intros [p' n'] He E. cbn [fst] in E. subst p'. pose proof (RP _ He) as P1. cbn [snd] in P1.
destruct (af_live_disj RT AF Σ m p n p n' [] R ART0 ltac:(rewrite EL; reflexivity) ltac:(exact He)); lia.
Qed.

Lemma hp_tr0 : forall (Σ' : rts RT) (m m' : mem) a (h : hstate unit) (L : list (Z * Z)) (spill : list cell),
hsep X a h -> rt_live RT Σ' = L ++ a_P a ++ x_live X -> Permutation (a_P a) (h_own a h) -> drv_consts m' ->
rt_pres_fp (rt_live RT Σ') [(F, 8%nat)] S1 [] m m' ->
rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) mR m -> ERR_rep m -> (forall so, OUT_rep so mR -> OUT_rep so m) -> io_ssp m ->
rw_cells bsegs m S1 spill -> cells_size spill = 248%nat -> rw_cells bsegs m sf [CB 16 HSH_L_HDR] ->
bits_rep bsegs m (F + HO_BITS) (a_Dc a) (h_bits h) -> bits_ok (h_bits h) -> h_os_rep X m a h -> sync_rep m (F + HO_OY) (a_Dsy a) (h_oy h) (a_sybytes a) ->
rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) mR m' /\ ERR_rep m' /\ (forall so, OUT_rep so mR -> OUT_rep so m') /\ io_ssp m'
/\ rw_cells bsegs m' S1 spill /\ rw_cells bsegs m' sf [CB 16 HSH_L_HDR]
/\ bits_rep bsegs m' (F + HO_BITS) (a_Dc a) (h_bits h) /\ h_os_rep X m' a h /\ sync_rep m' (F + HO_OY) (a_Dsy a) (h_oy h) (a_sybytes a).
Proof using HX ERR_loc OUT_loc IO_img.
intros Σ' m m' a h L spill HSP EL PERM DC PR PF ERR OUTR SSP SP SPS LSH BITS BOK OSR SY.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ')).
{ intros e He. rewrite EL. apply in_or_app. right. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ' m m' a h _ _ HSP PR
ltac:(intros e He; rewrite EL; apply in_or_app; right; apply in_or_app; right; exact He) (fp_h_nil X a h) DC PF ERR OUTR SSP)
as (PF' & ERR' & OUTR' & SSP').
split; [exact PF'|]. split; [exact ERR'|]. split; [exact OUTR'|]. split; [exact SSP'|].
split; [apply (htr_rw _ _ _ _ m m' PR _ _ SP); rewrite SPS; [apply acl_stack; unfold USTACK_TOP in *; lia| apply rng_out_nil]|].
split; [apply (htr_rw _ _ _ _ m m' PR _ _ LSH); cbn [cells_size csize Nat.add];
[apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia| apply rng_out_nil]|].
split.
{ unfold HO_BITS in *. apply (bits_rep_tr _ _ _ _ m m' PR _ _ _ BITS BOK); [| apply rng_out_nil| | apply rng_out_nil].
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply (acl_live _ _ _ _ _ _ _ (INL _ (own_in_Dc a h))); lia. }
split.
{ apply (h_os_rep_tr _ _ _ _ m m' PR X a h OSR).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IB)); lia|]. split; [apply rng_out_nil|].
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IL)); lia|]. split; [apply rng_out_nil|].
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IG)); lia| apply rng_out_nil]. }
{ unfold HO_OY in *. apply (sync_rep_tr _ _ _ _ m m' PR _ _ _ _ SY).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_nil.
- intros NS. split; [| apply rng_out_nil]. apply (acl_live _ _ _ _ _ _ _ (INL _ (own_in_Dsy a h NS))); unfold bptr in *; lia. }
Qed.

Hypothesis FRE : free_contract RT.
Lemma hp_f54_ok : forall (h : hstate unit) (a : haux) (k v : Z) (Σ : rts RT) (m : mem) (cc : config) T
(ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s7 s8 s9 s11 t3 t4 t5 t6 : word) Fr fc
(w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w120 w128 w136 w144 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 : word),
ASTA RT Σ PMh (eq (MS (mkR ra (Z64 S1) (x_gp X) (Z64 0x638c98) t0 t1 t2 (Z64 usp) (Z64 S1) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z64 sf) s4 (Z64 v) (Z64 (-8)) s7 s8 s9 (Z64 (F + HO_BITS)) s11 t3 t4 t5 t6)
Fr (Z64 0x97444) fc None m (seg_rom bsegs))) cc ->
X1cn.frm0 fc -> hsig_x Σ a h k [(v, 80)] -> h_cost h + k <= FUZZ_COST - 1 -> h_st h = None -> h_stream_init h = 1 -> hpure X h ->
ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo S1 ->
rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) mR m -> ERR_rep m -> (forall so, OUT_rep so mR -> OUT_rep so m) -> io_ssp m ->
rw_cells bsegs m S1 (hsp (Z64 (sf + 16)) (Z64 F) (Z64 F) w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 (Z64 (F + HO_OY)) w120 w128 w136 w144
(Z64 (F + HO_OS)) w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 (Z64 F)) ->
rw_cells bsegs m sf [CB 16 HSH_L_HDR] ->
bits_rep bsegs m (F + HO_BITS) (a_Dc a) (h_bits h) -> h_os_rep X m a h -> sync_rep m (F + HO_OY) (a_Dsy a) (h_oy h) (a_sybytes a) ->
h_dec_rep X m a h ->
(forall c', at_XT RT OUT_rep ERR_rep IO_FP X F0 fs0 c' -> realizes bsegs c' T) ->
realizes bsegs cc T.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV BDES SCLR YCLR FRE.
intros h a k v Σ m cc T ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc
w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w120 w128 w136 w144 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232
Hc FRM HSX KC STN SI1 HP ART0 MI ST PF ERR OUTR SSP SP LSH BITS OSR SY DEC Hk.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HSX as (EL & ND & PERM & EF & ESP & EPO0 & ECR).

refine (rz_evt RT AF Σ PMh _ _ T cc (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply hp_f3. exact MI. }
intros ms1 cc1 -> Hc1. clear Hc.
pose proof (h_unwind m 0x9744c PF ltac:(clear; vm_compute; tauto) ltac:(lia)) as UW1.
assert (INV : In (v, 80) (rt_live RT Σ)) by (rewrite EL; left; reflexivity).
unfold A_free_hp in Hc1. change 0x67f80 with e_free in Hc1.
cps_rt (FRE Σ PMh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m v 80 lo).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ unfold call_ok. rewrite unsigned_lit by (unfold USTACK_TOP in *; lia).
split; [exact ST|]. split; [rewrite ESP; exact LW|]. split; [unfold RT_STACK; lia|]. split; [unfold USTACK_TOP in *; lia|].
clear - S32. Z.div_mod_to_equations. lia. }
intros cc2 (Σ2 & v2 & Hc2 & EL2 & EF2 & ES2 & EC2 & EP2). clear Hc1.
cps_unpack Hc2 as (m2 & RS & RA2 & PR2).
destruct RA2 as (ART2 & MI2 & ST2).
pose proof (own_pos_h m a h OSR DEC HP) as OPOS.
assert (ELR : rt_live RT Σ2 = a_P a ++ x_live X).
{ rewrite EL2, EL. cbn [app]. apply (live_remove_top Σ m v 80 (a_P a ++ x_live X) ART0 EL ltac:(lia)).
intros [p q] He. apply in_app_or in He as [He|He].
- exact (OPOS p q (Permutation_in _ PERM He)).
- exact (proj1 (hi_live _ _ _ HX) p q He). }
assert (HS2 : hsig_k RT X Σ2 a h k).
{ unfold hsig_k. split; [exact ELR|]. split; [exact ND|]. split; [exact PERM|]. split; [rewrite EF2; exact EF|]. split; [rewrite ES2; exact ESP|].
split; [rewrite EP2; exact EPO0| rewrite EC2; exact ECR]. }
pose proof (hsep_of_k RT AF OUT_rep IO_FP X HX Σ2 m2 a h k ART2 HS2) as HSP2.
rewrite EF in PR2. apply (pres_fp_of_pres _ _ _ []) in PR2.
assert (BOK : bits_ok (h_bits h)) by (destruct HP as (_ & _ & _ & _ & B & _); exact B).
destruct (hp_tr0 Σ2 m m2 a h [] _ HSP2 ELR PERM (AF_DRV _ _ ART2) PR2 PF ERR OUTR SSP SP ltac:(reflexivity) LSH BITS BOK OSR SY)
as (PF2 & ERR2 & OUTR2 & SSP2 & SP2 & LSH2 & BITS2 & OSR2 & SY2).
replace (ret_pc (Z64 0x9744c)) with (Z64 0x9744c) in Hc by (symmetry; apply ret_pc_even; [lia| reflexivity]).
assert (DEC2 : h_dec_rep X m2 a h) by (unfold h_dec_rep in *; rewrite STN in *; exact DEC).
exact (hp_tail_ok h a k Σ2 m2 _ T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
Hc FRM HS2 KC STN SI1 HP ART2 MI2 ltac:(first [exact ST2 | rewrite unsigned_lit in ST2 by (unfold USTACK_TOP in *; lia); exact ST2])
PF2 ERR2 OUTR2 SSP2 SP2 LSH2 BITS2 OSR2 SY2 DEC2 Hk).
Qed.

Lemma h_destroy_stack_le : forall d, destroy_stack d <= 32 * Z.of_nat (dec_depth d) - 16.
Proof. induction d as [st|s low IH]; cbn [destroy_stack dec_depth]; [lia|]. rewrite Nat2Z.inj_succ. lia. Qed.

Lemma hsep_of_x : forall (Σ : rts RT) (m : mem) a h k L, ART RT Σ m -> hsig_x Σ a h k L -> hsep X a h.
Proof using AF HX.
intros Σ m a h k L ART1 HS. destruct HS as (EL & ND & PERM & EF & ES & _).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ)).
{ intros e He. rewrite EL. apply in_or_app. right. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
assert (INF : In (F, 8%nat) (rt_frames RT Σ)) by (rewrite EF; left; reflexivity).
destruct (af_frames_range RT AF Σ m F 8 ART1 INF) as (_ & _ & _ & FR).
destruct (af_fshadow_apart RT AF Σ m F 8 ART1 INF) as (FSH & _).
change (fs_size 8) with 16384 in FR, FSH. rewrite <- ESF, ESF2 in FSH.
pose proof (hi_lo _ _ _ HX) as (LW0 & _). rewrite <- ES in LW0.
split; [| split; [| exact (Permutation_NoDup (Permutation_map fst PERM) ND)]].
- intros p q Hin. pose proof (INL _ Hin) as Hl.
destruct (af_live_range RT AF Σ m p q ART1 Hl) as (P0 & P1 & P2).
split; [exact P0|]. split; [lia|]. split; [exact (FR p q Hl)|]. split; [exact (FSH p q Hl)|]. split; [exact P2|].
intros p' q' Hc. pose proof (Permutation_in _ (Permutation_sym PERM) Hin) as HinP. destruct (in_split _ _ HinP) as (l1 & l2 & E).
apply (af_live_disj RT AF Σ m p q p' q' (L ++ l1) (l2 ++ x_live X) ART1). { rewrite EL, E, <- !app_assoc. reflexivity. }
apply in_or_app. right. apply in_or_app. right. exact Hc.
- intros p1 q1 p2 q2 H1 H2 NE. exact (live_sep_gen RT AF Σ m p1 q1 p2 q2 ART1 (INL _ H1) (INL _ H2) NE).
Qed.

Lemma live_apart_app : forall (Σ : rts RT) (m : mem) L R e1 e2, ART RT Σ m -> rt_live RT Σ = L ++ R -> In e1 L -> In e2 R ->
fst e1 + snd e1 <= fst e2 \/ fst e2 + snd e2 <= fst e1.
Proof using AF.
intros Σ m L R [p1 n1] [p2 n2] ART0 EL H1 H2. cbn [fst snd]. destruct (in_split _ _ H1) as (l1 & l2 & E).
apply (af_live_disj RT AF Σ m p1 n1 p2 n2 l1 (l2 ++ R) ART0). { rewrite EL, E, <- app_assoc. reflexivity. }
apply in_or_app. right. apply in_or_app. right. exact H2.
Qed.

Hypothesis DESTROY : forall d, destroy_cps_at RT d.
Lemma hp_f48_ok : forall (h : hstate unit) (a : haux) (k v D : Z) (d : dec_state bptr) (LBD : list block) (NEW : list (Z * Z))
(Σ : rts RT) (m : mem) (cc : config) T
(ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc
(w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w120 w128 w136 w144 w160 w168 w176 w184 w200 w208 w224 w232 : word),
ASTA RT Σ PMh (eq (MS (mkR ra (Z64 S1) (x_gp X) (Z64 0x638c98) t0 t1 t2 (Z64 usp) (Z64 S1) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z64 sf) s4 (Z64 v) (Z64 (-8)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z64 0x97438) fc None m (seg_rom bsegs))) cc ->
X1cn.frm0 fc -> hsig_x Σ a h k (NEW ++ [(v, 80)]) -> h_cost h + k <= FUZZ_COST - 1 -> h_st h = None -> h_stream_init h = 1 -> hpure X h ->
Permutation NEW (blocks_live LBD) -> List.NoDup (map blk_id LBD) -> DREP (F + HO_OUT) (F + HO_STEREO) m D d LBD -> (dec_depth d <= 3)%nat ->
ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo S1 ->
rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) mR m -> ERR_rep m -> (forall so, OUT_rep so mR -> OUT_rep so m) -> io_ssp m ->
rw_cells bsegs m S1 (hsp (Z64 (sf + 16)) (Z64 F) (Z64 F) w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 (Z64 (F + HO_OY)) w120 w128 w136 w144
(Z64 (F + HO_OS)) w160 w168 w176 w184 (Z64 (F + HO_BITS)) w200 w208 (Z64 D) w224 w232 (Z64 F)) ->
rw_cells bsegs m sf [CB 16 HSH_L_HDR] ->
bits_rep bsegs m (F + HO_BITS) (a_Dc a) (h_bits h) -> h_os_rep X m a h -> sync_rep m (F + HO_OY) (a_Dsy a) (h_oy h) (a_sybytes a) ->
h_dec_rep X m a h ->
(forall c', at_XT RT OUT_rep ERR_rep IO_FP X F0 fs0 c' -> realizes bsegs c' T) ->
realizes bsegs cc T.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV BDES SCLR YCLR FRE DESTROY.
intros h a k v D d LBD NEW Σ m cc T ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc
w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w120 w128 w136 w144 w160 w168 w176 w184 w200 w208 w224 w232
Hc FRM HSX KC STN SI1 HP PNEW NDB DR DD ART0 MI ST PF ERR OUTR SSP SP LSH BITS OSR SY DEC Hk.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HSX as (EL & ND & PERM & EF & ESP & EPO0 & ECR).

refine (rz_evt RT AF Σ PMh _ _ T cc (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply hp_f1; [unfold USTACK_TOP in *; lia | exact SP | exact MI]. }
intros ms1 cc1 -> Hc1. clear Hc.
pose proof (h_unwind m 0x97440 PF ltac:(clear; vm_compute; tauto) ltac:(lia)) as UW1.
assert (INB : forall b, In b LBD -> In (blk_addr b, blk_size b) (rt_live RT Σ)).
{ intros b Hb. rewrite EL. apply in_or_app. left. apply in_or_app. left. apply (Permutation_in _ (Permutation_sym PNEW)).
unfold blocks_live. apply (in_map (fun b => (blk_addr b, blk_size b))). exact Hb. }
pose proof (h_destroy_stack_le d) as DSL.
unfold A_destroy_hp in Hc1. change 0x98a30 with A_speex_decoder_destroy in Hc1.
cps_rt (DESTROY d Σ PMh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m (F + HO_OUT) (F + HO_STEREO) D lo LBD).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). exact ST. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold RT_STACK. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). clear - S32. Z.div_mod_to_equations. lia. }
intros cc2 (Σ2 & Hc2 & EL2 & EF2 & ES2 & EC2 & EP2). clear Hc1.
cps_unpack_lib Hc2 as (v2 & m2 & RS & RA2 & PR2).
destruct RS as (-> & ->).
destruct RA2 as (ART2 & MI2 & ST2).
pose proof (hsep_of_x Σ m a h k _ ART0 HSX) as HSP.
pose proof (own_pos_h m a h OSR DEC HP) as OPOS.
assert (RPOS : forall e, In e ([(v, 80)] ++ a_P a ++ x_live X) -> 0 < snd e).
{ intros [p q] He. apply in_app_or in He as [[E|[]]|He]; [injection E as <- <-; cbn; lia|]. apply in_app_or in He as [He|He].
- exact (OPOS p q (Permutation_in _ PERM He)).
- exact (proj1 (hi_live _ _ _ HX) p q He). }
assert (ELR : rt_live RT Σ2 = [(v, 80)] ++ a_P a ++ x_live X).
{ rewrite EL2, EL, <- app_assoc, h_lrl_app, h_lrl_all, h_lrl_none; [reflexivity| |].
- intros [p q] He Hin. apply in_map_iff in Hin as (b & Eb & Hb). cbn [fst] in Eb. subst p.
assert (INN : In (blk_addr b, blk_size b) NEW) by (apply (Permutation_in _ (Permutation_sym PNEW)); unfold blocks_live; exact (in_map _ _ _ Hb)).
pose proof (h_drep_sizes_pos d _ _ m _ _ DR b Hb) as BP. pose proof (RPOS _ He) as RP. cbn [snd] in RP.
destruct (live_apart_app Σ m NEW ([(v, 80)] ++ a_P a ++ x_live X) _ _ ART0 ltac:(rewrite EL, <- app_assoc; reflexivity) INN He)
as [A|A]; cbn [fst snd] in A; lia.
- intros e He. apply (Permutation_in _ PNEW) in He. unfold blocks_live in He. apply in_map_iff in He as (b & <- & Hb). cbn [fst].
exact (in_map blk_addr _ _ Hb). }
rewrite EF in PR2.
assert (BOK : bits_ok (h_bits h)) by (destruct HP as (_ & _ & _ & _ & B & _); exact B).
destruct (hp_tr0 Σ2 m m2 a h [(v, 80)] _ HSP ELR PERM (AF_DRV _ _ ART2) PR2 PF ERR OUTR SSP SP ltac:(reflexivity) LSH BITS BOK OSR SY)
as (PF2 & ERR2 & OUTR2 & SSP2 & SP2 & LSH2 & BITS2 & OSR2 & SY2).

refine (rz_evt RT AF Σ2 PMh _ _ T cc2 (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply hp_f2; [reflexivity | unfold USTACK_TOP in *; lia | exact SP2 | exact MI2]. }
intros ms3 cc3 -> Hc3. clear Hc.
assert (HSX2 : hsig_x Σ2 a h k [(v, 80)]).
{ split; [exact ELR|]. split; [exact ND|]. split; [exact PERM|]. split; [rewrite EF2; exact EF|]. split; [rewrite ES2; exact ESP|].
split; [rewrite EP2; exact EPO0| rewrite EC2; exact ECR]. }
assert (DEC2 : h_dec_rep X m2 a h) by (unfold h_dec_rep in *; rewrite STN in *; exact DEC).
eapply (hp_f54_ok h a k v Σ2 m2 cc3 T); [exact Hc3 | exact FRM | exact HSX2 | exact KC | exact STN | exact SI1 | exact HP | exact ART2 | exact MI2
| first [exact ST2 | rewrite unsigned_lit in ST2 by (unfold USTACK_TOP in *; lia); exact ST2]
| exact PF2 | exact ERR2 | exact OUTR2 | exact SSP2 | exact SP2 | exact LSH2 | exact BITS2 | exact OSR2 | exact SY2 | exact DEC2 | exact Hk].
Qed.

Lemma h_CB4_C4 : forall segs m A pre bs post, rw_cells segs m A (pre ++ CB 4 bs :: post) ->
exists w : word, rw_cells segs m A (pre ++ C4 w :: post).
Proof.
intros segs m A pre bs post H.
assert (WF : cells_wf (pre ++ CB 4 bs :: post)) by (destruct H as [[Hwf _] _]; exact Hwf).
assert (L : length bs = 4%nat).
{ clear - WF. induction pre as [|c pre IH]; cbn in WF; [exact (proj1 WF)| exact (IH (proj2 WF))]. }
destruct (bytes_are_f32 1 bs L) as (ws & Lw & E). destruct ws as [|w [|? ?]]; try discriminate Lw. exists w.
eapply rw_cells_recast; [exact H | |].
- clear - WF. induction pre as [|c pre IH]; cbn in WF |- *; [split; [exact I| exact (proj2 WF)]| split; [exact (proj1 WF)| exact (IH (proj2 WF))]].
- rewrite !cells_bytes_app. f_equal. cbn [cells_bytes cbytes]. f_equal. rewrite f32_cons, f32_nil in E. cbn [cells_bytes cbytes] in E. rewrite app_nil_r in E. exact E.
Qed.

Lemma h_op_junk_cells : forall (m : mem) A Bd (o : packet) g kc', rw_cells bsegs m A (op_cells Bd (Some o) g kc') -> exists opc, op_junk opc /\ rw_cells bsegs m A opc.
Proof using.
intros m A Bd o g kc' H. cbn [op_cells] in H.
exists [CB 8 (le8 (wz (Bd + pk_off o))); CB 8 (le8 (wz (pk_bytes o))); CB 8 (le8 (wz (pk_b_o_s o))); CB 8 (le8 (wz (pk_e_o_s o)));
CB 8 (le8 g); CB 8 (le8 (wz (pk_packetno o)))].
split; [do 6 eexists; reflexivity|].
eapply rw_cells_recast; [exact H| cbn [cells_wf cell_wf]; repeat split; apply length_le8| reflexivity].
Qed.

Lemma nodup_of_disj : forall L : list (Z * Z),
(forall l1 p n l2, L = l1 ++ (p, n) :: l2 -> forall e, In e (l1 ++ l2) -> p + n <= fst e \/ fst e + snd e <= p) ->
(forall e, In e L -> 0 < snd e) -> List.NoDup (map fst L).
Proof using.
induction L as [|[p n] L IH]; intros HD HP; [constructor|]. cbn [map]. constructor.
- intros Hin. apply in_map_iff in Hin as ([p' n'] & Ee & He). cbn [fst] in Ee. subst p'.
pose proof (HP (p, n) (or_introl eq_refl)) as P1. pose proof (HP (p, n') (or_intror He)) as P2. cbn [snd] in P1, P2.
destruct (HD [] p n L eq_refl (p, n') He) as [D|D]; cbn [fst snd] in D; lia.
- apply IH; [| intros e He; exact (HP e (or_intror He))].
intros l1 p1 n1 l2 E e He. apply (HD ((p, n) :: l1) p1 n1 l2); [rewrite E; reflexivity|]. right. exact He.
Qed.
Lemma live_nodup_pos : forall (Σ : rts RT) (m : mem), ART RT Σ m -> (forall e, In e (rt_live RT Σ) -> 0 < snd e) -> List.NoDup (map fst (rt_live RT Σ)).
Proof using AF.
intros Σ m ART0 HP. apply nodup_of_disj; [| exact HP].
intros l1 p n l2 E [p' n'] He. cbn [fst snd]. exact (af_live_disj RT AF Σ m p n p' n' l1 l2 ART0 E He).
Qed.

Section HP.
Variables (h : hstate unit) (op : packet) (pno nbr brem0 : Z) (a : haux) (Σ1 : rts RT) (m0 : mem) (v48 v56 v88 j224 j232 gw : word) (ogc kc : list cell).
Hypothesis HS1 : hsig RT X Σ1 a h.
Hypothesis HIT : h_iter X h nbr brem0.
Hypothesis SI1 : h_stream_init h = 1.
Hypothesis EOS0 : h_eos h = 0.
Hypothesis PC0 : h_packet_count h = 0.
Hypothesis PN0 : 0 <= pno.
Hypothesis SKW : h_skip_word v48 h.
Hypothesis HR0 : hrep RT OUT_rep ERR_rep IO_FP X Σ1 m0 a h
(h_spill X (Z64 (h_bytes_remaining h)) v48 v56 v88 j224 j232 a h) ogc (op_cells (a_Bd a) (Some op) gw kc).
Hypothesis OGJ : og_junk ogc.
Hypothesis KCS : cells_size kc = 48%nat.
Hypothesis PK0 : pk_off op = 0.
Hypothesis PKB : 0 <= pk_off op /\ 0 <= pk_bytes op /\ pk_off op + pk_bytes op <= os_body_fill (h_os h).
Hypothesis BUD : h_packet_count h + 1 + (os_lacing_fill (h_os h) - os_lacing_returned (h_os h)) <= 162 * h_consumed X h.

Variable m2 : mem.
Hypothesis PF02 : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 (W_h ++ IO_FP) m0 m2.
Hypothesis PFR2 : rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) mR m2.
Hypothesis ERR2 : ERR_rep m2.
Hypothesis OUT2 : forall so, OUT_rep so mR -> OUT_rep so m2.
Hypothesis SSP2 : io_ssp m2.

Lemma hp_hsep : hsep X a h.
Proof using AF HX HS1 HR0. destruct HR0 as (ART0 & _). exact (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m0 a h ART0 HS1). Qed.

Lemma hp_fz : forall (m : mem), drv_consts m -> rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 W_h m2 m ->
rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) mR m /\ ERR_rep m /\ (forall so, OUT_rep so mR -> OUT_rep so m) /\ io_ssp m
/\ (exists ows, rw_cells bsegs m (F + HO_OUT) (f32 ows) /\ length ows = 2000%nat)
/\ bits_rep bsegs m (F + HO_BITS) (a_Dc a) (h_bits h) /\ sync_rep m (F + HO_OY) (a_Dsy a) (h_oy h) (a_sybytes a)
/\ rw_cells bsegs m (F + HO_OG) ogc /\ rw_cells bsegs m (F + HO_OP) (op_cells (a_Bd a) (Some op) gw kc)
/\ h_os_rep X m a h /\ (exists stb, rw_cells bsegs m (F + HO_STEREO) [CB 24 stb]).
Proof using AF HX ERR_loc OUT_loc IO_img HS1 HR0 KCS OGJ PF02 PFR2 ERR2 OUT2 SSP2.
intros m DC PFA.
pose proof hp_hsep as HSP.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS1 as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ1 m2 m a h _ _ HSP PFA
ltac:(intros e He; rewrite EL; apply in_or_app; right; exact He) (fp_h_Wh a h) DC PFR2 ERR2 OUT2 SSP2) as (PF' & ERR' & OUTR' & SSP').
split; [exact PF'|]. split; [exact ERR'|]. split; [exact OUTR'|]. split; [exact SSP'|].
assert (PR : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 (W_h ++ IO_FP) m0 m).
{ apply (pres_fp_trans _ _ _ _ m0 m2 m PF02). apply (pres_fp_weaken _ _ _ W_h _ m2 m PFA). intros x Hx. apply outside_app_iff in Hx. exact (proj1 Hx). }
destruct HR0 as (ART0 & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC & OSR & (stb & STB)
& RATE & (wl & LOOK & LKR) & DEC & HP).
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
assert (ROF : forall A n, F <= A -> A + n <= F + 9168 + 24 -> (A + n <= F + 32 \/ F + 88 <= A) -> (A + n <= F + 8384 \/ F + 8388 <= A) ->
rng_out (W_h ++ IO_FP) A n).
{ intros A n H1 H2 H3 H4. apply rng_out_app; [| apply (rng_out_img IO_FP A n IO_img); right; lia].
unfold W_h. rng_out_tac ltac:(unfold RT_STACK, H_STACK, SH_LO, SH_HI in *; lia). }
assert (ROH : forall p q, In (p, q) (h_own a h) -> rng_out (W_h ++ IO_FP) p q).
{ intros p q Hin. destruct (proj1 HSP p q Hin) as (P0 & PL & PF8 & PS & PI & _). apply rng_out_app.
- unfold W_h. rng_out_tac ltac:(unfold RT_STACK, H_STACK, SH_LO, SH_HI in *; lia).
- apply (rng_out_img IO_FP p q IO_img). destruct PI as [PI|PI]; [left; exact PI| right; exact PI]. }
unfold HO_OUT, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO in *.
change (fs_size 8) with 16384 in *.
split; [exists ows; split; [| exact LOWS]; apply (htr_rw _ _ _ _ m0 m PR _ _ OUTB); rewrite ?cells_size_f32, ?LOWS;
[apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia| apply ROF; lia]|].
assert (BOK : bits_ok (h_bits h)) by (destruct HP as (_ & _ & _ & _ & B & _); exact B).
split; [apply (bits_rep_tr _ _ _ _ m0 m PR _ _ _ BITS BOK);
[apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia| apply ROF; lia|
apply (acl_live _ _ _ _ _ _ _ (INL _ (own_in_Dc a h))); lia| exact (ROH _ _ (own_in_Dc a h))]|].
split; [apply (sync_rep_tr _ _ _ _ m0 m PR _ _ _ _ SY);
[apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia| apply ROF; lia|
intros NS; split; [apply (acl_live _ _ _ _ _ _ _ (INL _ (own_in_Dsy a h NS))); unfold bptr in *; lia| exact (ROH _ _ (own_in_Dsy a h NS))]]|].
assert (OGS : cells_size ogc = 32%nat) by (destruct OGJ as (x1 & x2 & x3 & x4 & ->); reflexivity).
split; [apply (htr_rw _ _ _ _ m0 m PR _ _ OGC); rewrite ?OGS; [apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia| apply ROF; lia]|].
assert (OPS : cells_size (op_cells (a_Bd a) (Some op) gw kc) = 48%nat) by (unfold op_cells; cbn [cells_size csize app]; rewrite ?cells_size_app, ?KCS; reflexivity).
split; [apply (htr_rw _ _ _ _ m0 m PR _ _ OPC); rewrite ?OPS; [apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia| apply ROF; lia]|].
split; [apply (h_os_rep_tr _ _ _ _ m0 m PR X a h OSR);
[apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia| unfold HO_OS; apply ROF; lia|
intros NE; destruct (own_in_os a h NE) as (IB & IL & IG);
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IB)); lia|]; split; [exact (ROH _ _ IB)|];
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IL)); lia|]; split; [exact (ROH _ _ IL)|];
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IG)); lia| exact (ROH _ _ IG)]]|].
exists stb. apply (htr_rw _ _ _ _ m0 m PR _ _ STB); cbn [cells_size csize Nat.add]; [apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia| apply ROF; lia].
Qed.

Lemma hp_st_none : h_st h = None.
Proof using HR0 PC0.
destruct HR0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP).
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M & _).
destruct (h_st h); [exfalso; exact (M PC0)| reflexivity].
Qed.

Hypothesis PN1 : pno <= h_packet_count h.

Lemma hp_kh_ok : forall (Σ : rts RT) (m : mem) (c : config) (D : Z) (d5 : dec_state bptr) (LBD : list block) (NEW : list (Z * Z))
(nf ch rate ex fs : Z) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s10 t3 t4 t5 t6 : word) Fr fc,
ASTA RT Σ PMh (eq (MS (mkR ra (Z64 S1) (x_gp X) (Z64 0x638c98) t0 t1 t2 (Z64 usp) (Z64 S1) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z64 sf) (Z64 1) s5 (Z64 (-8)) (Z64 (F + HO_OS)) (Z64 pno) (Z64 (F + HO_OG)) s10 (Z64 ch)
t3 t4 t5 t6) Fr (Z64 A_KH) fc None m (seg_rom bsegs))) c ->
X1cn.frm0 fc ->
rt_live RT Σ = NEW ++ a_P a ++ x_live X -> rt_frames RT Σ = [(F, 8%nat)] -> rt_sp0 RT Σ = x_sp0 X -> rt_pois RT Σ = [] ->
x_cr0 X - h_cost h - 160 <= rt_credit RT Σ ->
Permutation NEW (blocks_live LBD) -> List.NoDup (map blk_id LBD) -> blocks_al8 LBD -> (length LBD <= 19)%nat ->
ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo S1 ->
rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 W_h m2 m ->
rw_cells bsegs m S1 (h_spill X (Z64 (h_bytes_remaining h)) v48 v56 v88 j224 j232
(HA (a_Dsy a) (a_sybytes a) (a_Bd a) (a_L a) (a_G a) (a_shdr a) (a_body a) (a_lws a) (a_gws a) (a_Dc a) D LBD (NEW ++ a_P a))
(incr_packet_count (set_header h d5 nf ch rate ex fs))) ->
rw_cells bsegs m sf [CB 16 HSH_P1] ->
(exists je, rw_cells bsegs m (F + HO_ENH) [CB 56 je]) ->
rw_cells bsegs m (F + HO_FSZ) [C4 (Z64 fs)] -> rw_cells bsegs m (F + HO_RATE) [C4 (Z64 rate)] -> (exists L, rw_cells bsegs m (F + HO_LOOK) [C4 (Z64 L)] /\ 0 <= L <= H_LOOK_MAX) ->
DREP (F + HO_OUT) (F + HO_STEREO) m D d5 LBD -> 0 < D ->
(dec_depth d5 <= 3)%nat -> isave_ok d5 -> dec_nestedR d5 ->
0 <= fs <= 640 -> 1 <= nf <= 10 -> -2^31 <= ch < 2^31 -> -2^31 <= rate < 2^31 -> -2^31 <= ex < 2^31 - 1 ->
at_KH RT OUT_rep ERR_rep IO_FP X F0 fs0 (incr_packet_count (set_header h d5 nf ch rate ex fs)) pno nbr brem0 c.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV HS1 HIT SI1 EOS0 PC0 PN0 PN1 SKW HR0 OGJ KCS PKB BUD PF02 PFR2 ERR2 OUT2 SSP2.
intros Σ m c D d5 LBD NEW nf ch rate ex fs ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s10 t3 t4 t5 t6 Fr fc
Hc FRM EL EF ESP EPO ECR PNEW NDB AL8 LB19 ART0 MI ST PFA SP LSH ENH FSZ RATE LOOK DR D0 DD ISV NST FSR NFR CHR RTR EXR.
destruct (hp_fz m (AF_DRV _ _ ART0) PFA) as (PF & ERR & OUTR & SSP & OUTB & BITS & SY & OGC & OPC & OSR & STB).
destruct (h_op_junk_cells m _ _ _ _ _ OPC) as (opc & OPJ & OPC').
pose proof HS1 as (EL1 & ND1 & PERM1 & EF1 & ESP1 & EPO1 & ECR1).
pose proof HR0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OSR0 & _ & _ & _ & DEC0 & HP0).
pose proof hp_st_none as STN.
pose proof (own_pos_h m0 a h OSR0 DEC0 HP0) as OPOS.
set (a' := HA (a_Dsy a) (a_sybytes a) (a_Bd a) (a_L a) (a_G a) (a_shdr a) (a_body a) (a_lws a) (a_gws a) (a_Dc a) D LBD (NEW ++ a_P a)).
set (h' := incr_packet_count (set_header h d5 nf ch rate ex fs)).
assert (EOWN : h_own a' h' = blocks_live LBD ++ h_own a h).
{ unfold h_own at 2. rewrite STN. cbn [app]. reflexivity. }
assert (BPOS : forall e, In e NEW -> 0 < snd e).
{ intros e He. apply (Permutation_in _ PNEW) in He. unfold blocks_live in He. apply in_map_iff in He as (b & <- & Hb). cbn [snd].
exact (h_drep_sizes_pos d5 _ _ m _ _ DR b Hb). }
assert (NDL : List.NoDup (map fst (rt_live RT Σ))).
{ apply (live_nodup_pos Σ m ART0). rewrite EL. intros e He. apply in_app_or in He as [He|He]; [exact (BPOS e He)|].
apply in_app_or in He as [He|He]; [destruct e as [p q]; exact (OPOS p q (Permutation_in _ PERM1 He))| destruct e as [p q]; exact (proj1 (hi_live _ _ _ HX) p q He)]. }
assert (ND' : List.NoDup (map fst (NEW ++ a_P a))).
{ rewrite EL, app_assoc, map_app in NDL. exact (NoDup_app_remove_r _ _ NDL). }
unfold at_KH.
exists Σ, a', Fr, fc, m, ra, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, s2, s5, s10, t3, t4, t5, t6, v48, v56, v88, j224, j232, ogc, opc.
split.
{ unfold h_regs. replace (h_packet_count h') with 1 by (unfold h'; cbn [incr_packet_count set_header h_packet_count]; lia).
replace (h_channels h') with ch by (unfold h'; reflexivity). exact Hc. }
split; [exact FRM|].
split.
{ unfold hsig. split; [cbn [a_P a']; rewrite EL, app_assoc; reflexivity|]. split; [exact ND'|].
split; [rewrite EOWN; cbn [a_P a']; apply Permutation_app; [exact PNEW| exact PERM1]|].
split; [exact EF|]. split; [exact ESP|]. split; [exact EPO|].
unfold h_cost, H_HDR_CREDIT, H_DEC_CREDIT in *. unfold h'. cbn [incr_packet_count set_header h_packet_count]. rewrite PC0 in *. lia. }
split; [unfold h_iter in *; exact HIT|].
split; [exact SI1|]. split; [exact EOS0|]. split; [unfold h'; cbn [incr_packet_count set_header h_packet_count]; lia|]. split; [exact SKW|].
split; [unfold h'; cbn [incr_packet_count set_header h_packet_count]; intros E; exfalso; rewrite PC0 in E; lia|].
split.
2: { split; [exact OGJ| exact OPJ]. }
unfold hrep.
split; [exact ART0|]. split; [exact MI|]. split; [exact ST|]. split; [exact PF|]. split; [exact ERR|]. split; [exact OUTR|]. split; [exact SSP|].
split; [exact SP|]. split; [exact LSH|]. split; [exact ENH|]. split; [exact OUTB|]. split; [exact FSZ|]. split; [exact BITS|]. split; [exact SY|].
split; [exact OGC|]. split; [exact OPC'|]. split; [exact OSR|]. split; [exact STB|]. split; [exact RATE|]. split; [destruct LOOK as (L & LK & LR); exists L; split; [exact LK| intros _; exact LR]|].
split.
{ unfold h_dec_rep. cbn [h' incr_packet_count set_header h_st a' a_S a_LBD a_Dc].
split; [exact DR|]. split; [exact D0|]. split; [exact DD|]. split; [exact ISV|]. split; [exact NST|]. split; [exact NDB|]. split; [exact AL8|].
split; [| exact LB19].
intros b Hb E.
assert (INN : In (blk_addr b, blk_size b) NEW) by (apply (Permutation_in _ (Permutation_sym PNEW)); unfold blocks_live; exact (in_map _ _ _ Hb)).
assert (INDc : In (a_Dc a, sb_buf_size (h_bits h)) (a_P a)) by exact (Permutation_in _ (Permutation_sym PERM1) (own_in_Dc a h)).
rewrite map_app in ND'. apply (nodup_app_disj _ _ (blk_addr b) ND'); [exact (in_map fst _ _ INN)| rewrite E; exact (in_map fst _ _ INDc)]. }
pose proof OSR0 as OSR0'. unfold h_os_rep in OSR0'. rewrite SI1 in OSR0'. cbn [Z.eqb] in OSR0'.
destruct OSR0' as (_ & _ & _ & _ & (SI_a & SI_b & _) & _).
apply hpure_hdr; [exact HP0| exact PC0| exact FSR| exact NFR| exact CHR| exact RTR| exact EXR| rewrite PC0 in BUD; lia| lia].
Qed.

Hypothesis CTL : forall d, ctl_cps_at RT d.

Lemma hp_ctl : forall (Σ : rts RT) (m : mem) (cc : config) T (d : dec_state bptr) (D : Z) (LBD : list block) (r : ctl_req) (P : Z)
(ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc,
ASTA RT Σ PMh (eq (MS (mkR ra (Z64 S1) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z64 A_ctl_h) fc None m (seg_rom bsegs))) cc ->
a0 = Z64 D -> a1 = Z64 (ctl_req_code r) -> a2 = Z64 P -> tp = Z64 0x638c98 ->
X1cn.frm0 fc -> rt_frames RT Σ = [(F, 8%nat)] -> rt_sp0 RT Σ = x_sp0 X -> 3 <= rt_credit RT Σ ->
creq_grp1 r = true -> DREP (F + HO_OUT) (F + HO_STEREO) m D d LBD -> (dec_depth d <= 3)%nat -> List.NoDup (map blk_id LBD) ->
(forall b, In b LBD -> In (blk_addr b, blk_size b) (rt_live RT Σ)) ->
creq_ok (F + HO_OUT) P r -> creq_pre (F + HO_STEREO) m D d P r ->
F <= P -> P + creq_size r <= F + 16376 -> acc bsegs m P (creq_size r) -> P mod creq_align r = 0 ->
ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo S1 ->
(forall (Σ' : rts RT) (m' : mem) (c' : config) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) Fr' fc',
ASTA RT Σ' PMh (eq (MS (mkR ra (Z64 S1) gp tp t0' t1' t2' s0 s1 (Z64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
Fr' (ret_pc ra) fc' None m' (seg_rom bsegs))) c' ->
X1cn.frm0 fc' ->
rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_pois RT Σ' = rt_pois RT Σ ->
rt_credit RT Σ - 2 <= rt_credit RT Σ' <= rt_credit RT Σ ->
ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo S1 ->
rt_pres_fp (rt_live RT Σ) [(F, 8%nat)] S1 ((P, P + creq_size r) :: blocks_ivs LBD) m m' ->
DREP (F + HO_OUT) (F + HO_STEREO) m' D (snd (speex_decoder_ctl d r)) LBD -> creq_post (F + HO_STEREO) m' P r (fst (speex_decoder_ctl d r)) ->
acc bsegs m' P (creq_size r) ->
realizes bsegs c' T) ->
realizes bsegs cc T.
Proof.
intros Σ m cc T d D LBD r P ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc
Hc E0 E1 E2 ETP FRM EF ESP CR G1 DR DD NDB INB OK PRE P0 P1 ACC PAL ART0 MI ST K.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
assert (INF : In (F, 8%nat) (rt_frames RT Σ)) by (rewrite EF; left; reflexivity).
assert (CST : ctl_stack d <= 96 * 2 + NBCTL_STACK).
{ destruct d as [st|s low]; cbn [ctl_stack dec_depth] in *; [lia|]. destruct low as [st|s' low']; cbn [ctl_stack dec_depth] in *; [lia|].
destruct low' as [st|s'' low'']; cbn [ctl_stack dec_depth] in *; [lia|]. destruct low''; cbn [dec_depth] in DD; lia. }
unfold A_ctl_h in Hc. change 0x98c74 with A_speex_decoder_ctl in Hc.
cps_rt (CTL d Σ PMh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m (F + HO_OUT) (F + HO_STEREO) D LBD r P lo F 8%nat).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ change (fs_size 8) with 16384. lia. }
{ rewrite EF. cbn [length]. unfold FRAMES_MAX. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). exact ST. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold NBCTL_STACK, RT_STACK in *. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). exact S32. }
intros c' (Σ' & Hc' & EL' & EF' & ES' & EC' & EP'). clear Hc.
cps_unpack_lib Hc' as (m' & RS & RA & PR & DR' & POST & ACC').
destruct RA as (ART' & MI' & WM' & ST').
assert (IV : creq_ivs P r = [(P, P + creq_size r)]) by (destruct r; try discriminate G1; reflexivity).
rewrite IV, EF in PR. cbn [app] in PR.
eapply K; [exact Hc | exact RS | exact EL' | exact EF' | exact ES' | exact EP' | | exact ART' | exact MI'
| first [exact ST' | rewrite unsigned_lit in ST' by (unfold USTACK_TOP in *; lia); exact ST'] | exact PR | exact DR' | exact POST | exact ACC'].
destruct (dec_depth d) as [|[|[|[|?]]]]; cbn [Z.of_nat] in EC'; lia.
Qed.

Definition iv_hp (L : list (Z * Z)) (lo' hi' : Z) : Prop :=
hi' <= lo' \/ (exists l h', In (l, h') W_h /\ l <= lo' /\ hi' <= h') \/ (exists p n, In (p, n) L /\ p <= lo' /\ hi' <= p + n).
Lemma hp_acc : forall (Σ : rts RT) (m m' : mem) (L W : list (Z * Z)),
ART RT Σ m -> rt_live RT Σ = L ++ rt_live RT Σ1 -> rt_frames RT Σ = [(F, 8%nat)] -> rt_sp0 RT Σ = x_sp0 X ->
rt_pres_fp (rt_live RT Σ) [(F, 8%nat)] S1 W m m' -> (forall lo' hi', In (lo', hi') W -> iv_hp L lo' hi') ->
rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 W_h m m'.
Proof.
intros Σ m m' L W ART0 EL EF ES PR HW b Hb Ho. apply PR.
- apply (aclient_mono _ _ _ (rt_live RT Σ) [(F, 8%nat)] S1 _ Hb); [intros e He; rewrite EL; apply in_or_app; right; exact He| intros e He; exact He| lia].
- apply outside_intro. intros l hh Hin Hx. destruct (HW l hh Hin) as [E|[(l' & h'' & Hw & L1 & L2)|(p & n & Hp & P1 & P2)]].
+ lia.
+ revert Ho. generalize W_h Hw. intros W' Hw'. clear - Hw' L1 L2 Hx. induction W' as [|[x y] W' IH]; [destruct Hw'|].
cbn [outside]. intros (O1 & O2). destruct Hw' as [E|Hw']; [injection E as <- <-; lia| exact (IH Hw' O2)].
+ exact (new_not_client Σ m L (rt_live RT Σ1) p n (bv_unsigned b) ART0 EL EF ES Hp ltac:(lia) Hb).
Qed.
Lemma iv_hp_wh : forall L l h', In (l, h') W_h -> iv_hp L l h'.
Proof. intros L l h' H. right; left. exists l, h'. split; [exact H| lia]. Qed.
Lemma iv_hp_blocks : forall (L : list (Z * Z)) (LBD : list block) lo' hi', (forall b, In b LBD -> In (blk_addr b, blk_size b) L) ->
In (lo', hi') (blocks_ivs LBD) -> iv_hp L lo' hi'.
Proof.
intros L LBD lo' hi' HB Hin. unfold blocks_ivs in Hin. apply in_map_iff in Hin as (b & E & Hb). injection E as <- <-.
right; right. exists (blk_addr b), (blk_size b). split; [exact (HB b Hb)| lia].
Qed.

Lemma drep_tr : forall (L : list (Z * Z)) fr sp W (m m' : mem) OUT STEREO S (d : dec_state bptr) LBD,
rt_pres_fp L fr sp W m m' -> DREP OUT STEREO m S d LBD ->
(forall b, In b LBD -> acl_rng L fr sp (blk_addr b) (blk_size b) /\ rng_out W (blk_addr b) (blk_size b)) -> DREP OUT STEREO m' S d LBD.
Proof.
intros L fr sp W m m' OUT STEREO S d LBD PR R HB.
eapply decst_rep_agree; [exact R|].
intros x Hx (b & Hb & Hab). destruct (HB b Hb) as (HA & HO).
assert (E : m' (wa x) = m (wa x)) by (apply PR; rewrite wa_unsigned by lia; [apply HA; lia| apply HO; lia]).
split; [exact E|]. rewrite (wview_agree bsegs m m' _ E). tauto.
Qed.

Lemma c4_mod32 : forall v, bv_unsigned (Z64 v) mod 2^32 = v mod 2^32.
Proof. intros v. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). apply Z.mod_mod_divide. exists (2^32). reflexivity. Qed.

Lemma c4_eqm : forall (m : mem) A (w : word) v, rw_cells bsegs m A [C4 w] -> bv_unsigned w mod 2^32 = v mod 2^32 -> rw_cells bsegs m A [C4 (Z64 v)].
Proof.
intros m A w v H E. eapply rw_cells_recast; [exact H| cbn; tauto|]. cbn [cells_bytes cbytes].
replace (le4 w) with (le4 (Z64 (bv_unsigned w))) by (rewrite Z_to_bv_bv_unsigned; reflexivity).
f_equal. first [apply le4_lit_eqm; rewrite E; reflexivity | apply le4_lit_eqm; symmetry; exact E].
Qed.

Definition blk_sep (v : Z) (LBD : list block) : Prop :=
forall b, In b LBD -> 0 < blk_size b /\ blk_addr b + blk_size b <= lo /\ (blk_addr b + blk_size b <= F \/ F + 16384 <= blk_addr b)
/\ (blk_addr b + blk_size b <= sf \/ sf + 2048 <= blk_addr b) /\ (blk_addr b + blk_size b <= v \/ v + 80 <= blk_addr b).

Lemma rng_out_bsep : forall v LBD A n, blk_sep v LBD ->
((F <= A /\ A + n <= F + 16384) \/ (sf <= A /\ A + n <= sf + 2048) \/ lo <= A \/ (v <= A /\ A + n <= v + 80)) -> rng_out (blocks_ivs LBD) A n.
Proof.
intros v LBD A n HB HA. apply rng_out_blocks. intros b Hb. destruct (HB b Hb) as (B0 & B1 & B2 & B3 & B4). lia.
Qed.

Ltac hp_acl := first
[ apply acl_stack; unfold USTACK_TOP in *; lia
| apply (acl_frame _ [(x_F X, 8%nat)] _ (x_F X) 8 _ _ (or_introl eq_refl)); change (fs_size 8) with 16384; lia
| apply (acl_fshadow _ [(x_F X, 8%nat)] _ (x_F X) 8 _ _ (or_introl eq_refl)); change (fs_size 8) with 16384; lia
| match goal with H : In (?p, ?q) ?L |- acl_rng ?L _ _ _ _ => apply (acl_live _ _ _ p q _ _ H); lia end ].
Ltac hp_rng := repeat (first [ apply rng_out_nil | apply rng_out_cons; [unfold SH_LO, SH_HI in *; lia|]
| eapply rng_out_bsep; [eassumption| unfold SH_LO, SH_HI in *; lia] ]).
Ltac hp_tr PR H := eapply (htr_rw _ _ _ _ _ _ PR) in H; cbn [cells_size csize Nat.add] in H |- *; [| hp_acl | hp_rng].

Lemma hp_ai : forall (Σ : rts RT) (m : mem) (cc : config) T (hd : spx_header) (v D : Z) (junk28 : list byte) (w1 w2 w3 r1 r2 : word)
(LBD : list block) (NEW : list (Z * Z)) (j12 j16 : list byte) (c48 c52 c56 c64 : word) (wl : Z)
(t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) Fr fc,
ASTA RT Σ PMh (eq (MS (mkR (Z64 0x971d0) (Z64 S1) (x_gp X) (Z64 0x638c98) t0 t1 t2 (Z64 usp) (Z64 S1) (Z64 D) a1 a2 a3 a4 a5 a6 a7
(Z64 SHB) (Z64 sf) (Z64 (h_packet_count h)) (Z64 v) (Z64 (-8)) (Z64 0x7fffffff) (Z64 pno) (Z64 (F + 8384)) (Z64 (F + HO_BITS))
(Z64 (h_channels h)) t3 t4 t5 t6) Fr (ret_pc (Z64 0x971d0)) fc None m (seg_rom bsegs))) cc ->
X1cn.frm0 fc ->
rt_live RT Σ = NEW ++ (v, 80) :: rt_live RT Σ1 -> rt_frames RT Σ = [(F, 8%nat)] -> rt_sp0 RT Σ = x_sp0 X -> rt_pois RT Σ = [] ->
rt_credit RT Σ1 - 4 <= rt_credit RT Σ ->
Permutation NEW (blocks_live LBD) -> List.NoDup (map blk_id LBD) -> blocks_al8 LBD -> Z.of_nat (length NEW) = init_nblocks (mode_of_id (hd_mode hd)) ->
DREP (F + HO_OUT) (F + HO_STEREO) m D (init_dec (mode_of_id (hd_mode hd))) LBD ->
0 < v -> v mod 16 = 0 -> rw_cells bsegs m v (spx_header_cells junk28 hd w1 w2 w3 r1 r2) ->
-2^31 <= hd_rate hd < 2^31 -> 1 <= hd_nb_channels hd <= 2 -> -2^31 <= hd_frames_per_packet hd < 2^31 -> -2^31 <= hd_extra_headers hd < 2^31 ->
hd_speex_version_id hd <= 1 -> hd_mode_bitstream_version hd = 4 -> 0 <= hd_mode hd < 3 ->
ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo S1 ->
rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 W_h m2 m ->
rw_cells bsegs m S1 (h_spill X (Z64 (h_bytes_remaining h)) v48 v56 v88 j224 j232 a h) ->
rw_cells bsegs m sf [CB 16 HSH_L_HDR] ->
rw_cells bsegs m (F + 32) [C4 (Z64 1)] -> rw_cells bsegs m (F + 36) [CB 12 j12] -> rw_cells bsegs m (F + 48) [C4 c48; C4 c52; C8 c56; C8 c64] ->
rw_cells bsegs m (F + 72) [CB 16 j16] ->
rw_cells bsegs m (F + HO_FSZ) [C4 (Z64 (h_frame_size h))] -> rw_cells bsegs m (F + HO_RATE) [C4 (Z64 (h_rate h))] -> rw_cells bsegs m (F + HO_LOOK) [C4 (Z_to_bv 64 wl)] ->
(forall c', match hdr_tail h hd with
| None => at_XT RT OUT_rep ERR_rep IO_FP X F0 fs0 c'
| Some h3 => at_KH RT OUT_rep ERR_rep IO_FP X F0 fs0 (incr_packet_count h3) pno nbr brem0 c'
end -> realizes bsegs c' T) ->
realizes bsegs cc T.
Proof.
intros Σ m cc T hd v D junk28 w1 w2 w3 r1 r2 LBD NEW j12 j16 c48 c52 c56 c64 wl t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Fr fc
Hc FRM EL EF ESP EPO ECR PNEW NDB AL8 LNEW DR V0 V16 HC HRR HNC HFP HEX HVV HBV HM ART0 MI ST PFA SP LSH ENH J12 CBK J16 FSZ RATE LOOK Hk.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS1 as (EL1 & ND1 & PERM1 & EF1 & ESP1 & EPO1 & ECR1).
pose proof HR0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OSR0 & _ & _ & _ & DEC0 & HP0).
pose proof hp_st_none as STN.
pose proof hp_hsep as HSP.

unfold hdr_tail in Hk. replace (1 <? hd_speex_version_id hd) with false in Hk by (symmetry; apply Z.ltb_ge; lia).
rewrite HBV in Hk. cbn [Z.eqb negb] in Hk. cbv zeta in Hk.
set (mo := mode_of_id (hd_mode hd)) in *.

assert (INB : forall b, In b LBD -> In (blk_addr b, blk_size b) NEW).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym PNEW)). unfold blocks_live. exact (in_map (fun b => (blk_addr b, blk_size b)) _ _ Hb). }
assert (INBL : forall b, In b LBD -> In (blk_addr b, blk_size b) (rt_live RT Σ)) by (intros b Hb; rewrite EL; apply in_or_app; left; exact (INB b Hb)).
assert (INV : In (v, 80) (rt_live RT Σ)) by (rewrite EL; apply in_or_app; right; left; reflexivity).
assert (BSEP : blk_sep v LBD).
{ intros b Hb. pose proof (h_drep_sizes_pos _ _ _ m _ _ DR b Hb) as BP. pose proof (INBL b Hb) as Hl.
destruct (af_live_range RT AF Σ m _ _ ART0 Hl) as (P0 & P1 & P2). rewrite ESP in P1.
assert (INF : In (F, 8%nat) (rt_frames RT Σ)) by (rewrite EF; left; reflexivity).
destruct (af_frames_range RT AF Σ m F 8 ART0 INF) as (_ & _ & _ & FR).
destruct (af_fshadow_apart RT AF Σ m F 8 ART0 INF) as (FSH & _).
change (fs_size 8) with 16384 in FR, FSH. rewrite <- ESF, ESF2 in FSH.
pose proof (hi_lo _ _ _ HX) as (LW0 & _).
split; [exact BP|]. split; [lia|]. split; [destruct (FR _ _ Hl); lia|]. split; [destruct (FSH _ _ Hl); lia|].
destruct (live_apart_app Σ m NEW ((v, 80) :: rt_live RT Σ1) _ _ ART0 EL (INB b Hb) (or_introl eq_refl)) as [A|A]; cbn [fst snd] in A; lia. }

assert (CRS : 100 <= rt_credit RT Σ).
{ pose proof (hi_cr _ _ _ HX) as FC. unfold h_cost, H_HDR_CREDIT, H_DEC_CREDIT, FUZZ_COST in *. rewrite PC0 in ECR1. lia. }
destruct (drep_head _ _ _ _ _ _ DR) as (nD & IND & ND0 & D8).
pose proof (INBL _ IND) as INDL. cbn [blk_addr blk_size] in INDL.
destruct (af_live_range RT AF Σ m _ _ ART0 INDL) as (DP0 & DL & _). cbn [blk_addr blk_size fst snd] in DP0, DL.
pose proof (af_sp0_range RT AF Σ m ART0) as (SPA & SPB). rewrite ESP in DL, SPA, SPB.
assert (LB : bytes_at bsegs m (shad F) HSH_L_HDR) by (destruct LSH as [[_ B] _]; cbn [cells_bytes cbytes] in B; rewrite app_nil_r in B; rewrite <- ESF; exact B).
destruct (hsh_L_hdr_acc m F ltac:(clear - F64; Z.div_mod_to_equations; lia) ltac:(lia) LB) as (ACE & ACB). clear LB.
unfold HO_ENH, HO_CBK in ACE, ACB.

refine (rz_evt RT AF Σ PMh _ _ T cc (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply hp_w4; [reflexivity | unfold USTACK_TOP in *; lia | unfold STACK_WIN, USTACK_TOP in *; lia | exact SP | exact MI]. }
intros ms1 cc1 -> Hc1. clear Hc.
eapply (hp_ctl Σ m cc1 T (init_dec mo) D LBD (CtlSetEnh 1) (F + 32));
[exact Hc1 | reflexivity | reflexivity | reflexivity | reflexivity | exact FRM | exact EF | exact ESP | lia | reflexivity | exact DR
| pose proof (depth_init mo); exact H | exact NDB | exact INBL | right; reflexivity
| exists (Z64 1); split; [exact ENH| rewrite unsigned_lit by lia; split; [reflexivity| lia]]
| lia | cbn [creq_size]; lia | exact ACE | cbn [creq_align]; clear - F64; Z.div_mod_to_equations; lia | exact ART0 | exact MI | exact ST | ].
intros Σ2 m3 cc2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Fr2 fc2 Hc2 FRM2 EL2 EF2 ES2 EP2 EC2 ART2 MI2 ST2 PR DR2 POST ACC2.
clear Hc1.
cbn [creq_size] in PR.
assert (ELn : rt_live RT Σ = (NEW ++ [(v, 80)]) ++ rt_live RT Σ1) by (rewrite EL, <- app_assoc; reflexivity).
assert (INB' : forall b, In b LBD -> In (blk_addr b, blk_size b) (NEW ++ [(v, 80)])) by (intros b Hb; apply in_or_app; left; exact (INB b Hb)).
pose proof (pres_fp_trans _ _ _ _ m2 m m3 PFA (hp_acc Σ m m3 _ _ ART0 ELn EF ESP PR
ltac:(intros l hh [E|Hin]; [injection E as <- <-; right; left; exists (F + 32), (F + 88); split; [right; right; left; reflexivity| lia]
| exact (iv_hp_blocks _ LBD l hh INB' Hin)]))) as PFA3.
clear PFA.
unfold HO_FSZ, HO_RATE, HO_LOOK in FSZ, RATE, LOOK.
hp_tr PR LSH. hp_tr PR J12. hp_tr PR CBK. hp_tr PR J16. hp_tr PR FSZ. hp_tr PR RATE. hp_tr PR LOOK.
assert (HCS : cells_size (spx_header_cells junk28 hd w1 w2 w3 r1 r2) = 80%nat) by reflexivity.
assert (VSEP : v + 80 <= lo /\ (v + 80 <= F \/ F + 16384 <= v) /\ (v + 80 <= sf \/ sf + 2048 <= v)).
{ assert (INF : In (F, 8%nat) (rt_frames RT Σ)) by (rewrite EF; left; reflexivity).
destruct (af_live_range RT AF Σ m _ _ ART0 INV) as (_ & VL & _). rewrite ESP in VL.
destruct (af_frames_range RT AF Σ m F 8 ART0 INF) as (_ & _ & _ & FR).
destruct (af_fshadow_apart RT AF Σ m F 8 ART0 INF) as (FSH & _).
change (fs_size 8) with 16384 in FR, FSH. rewrite <- ESF, ESF2 in FSH.
pose proof (hi_lo _ _ _ HX) as (LW0 & _).
split; [lia|]. split; [destruct (FR _ _ INV); lia| destruct (FSH _ _ INV); lia]. }
eapply (htr_rw _ _ _ _ _ _ PR) in HC; rewrite ?HCS; [| hp_acl | hp_rng].
eapply (htr_rw _ _ _ _ _ _ PR) in SP; [| unfold h_spill; rewrite hsp_size; hp_acl | unfold h_spill; rewrite hsp_size; hp_rng].
clear PR.
destruct POST as (wenh & ENH2 & _). clear ENH.
rewrite <- EL2 in INBL, INV.

refine (rz_evt RT AF Σ2 PMh _ _ T cc2 (PMfd_mat_stable F0 fs0) Hc2 _ _).
{ eapply hp_w5; [reflexivity | unfold USTACK_TOP in *; lia | unfold SH_LO, SH_HI in *; lia | exact SP | exact MI2]. }
intros ms3 cc3 (m3b & MU3 & WM3 & MI3b & SP3 & ->) Hc3. clear Hc2.
assert (ELn3 : rt_live RT Σ2 = (NEW ++ [(v, 80)]) ++ rt_live RT Σ1) by (rewrite EL2; exact ELn).
assert (EF2' : rt_frames RT Σ2 = [(F, 8%nat)]) by (rewrite EF2; exact EF).
assert (ES2' : rt_sp0 RT Σ2 = x_sp0 X) by (rewrite ES2; exact ESP).
pose proof (art_munch_h Σ2 m3 m3b _ ART2 EF2' ES2' MU3 WM3 ltac:(intros l hh [E|[]]; injection E as <- <-; left; unfold USTACK_TOP in *; lia)) as ART2b.
assert (PR3 : rt_pres_fp (rt_live RT Σ2) [(F, 8%nat)] S1 [(S1, S1 + 248)] m3 m3b) by (apply (pf_munch_h _ m3 m3b _ _ MU3); intros x Hx; exact Hx).
pose proof (pres_fp_trans _ _ _ _ m2 m3 m3b PFA3 (hp_acc Σ2 m3 m3b _ _ ART2 ELn3 EF2' ES2' PR3
ltac:(intros l hh [E|[]]; injection E as <- <-; apply iv_hp_wh; left; reflexivity))) as PFA3b.
assert (ST2b : stk bsegs m3b lo S1).
{ apply (stk_agree bsegs m3 m3b lo S1 ST2); [| exact WM3]. apply (agree_of_munch _ m3 m3b _ MU3). intros x Hx. cbn [outside]. split; [lia| exact I]. }
hp_tr PR3 LSH. hp_tr PR3 ENH2. hp_tr PR3 J12. hp_tr PR3 CBK. hp_tr PR3 J16. hp_tr PR3 FSZ. hp_tr PR3 RATE. hp_tr PR3 LOOK.
eapply (htr_rw _ _ _ _ _ _ PR3) in HC; rewrite ?HCS; [| hp_acl | hp_rng].
assert (DR2b : DREP (F + HO_OUT) (F + HO_STEREO) m3b D (snd (speex_decoder_ctl (init_dec mo) (CtlSetEnh 1))) LBD).
{ apply (drep_tr _ _ _ _ m3 m3b _ _ _ _ _ PR3 DR2). intros b Hb. destruct (BSEP b Hb) as (B0 & B1 & B2 & B3 & B4).
split; [apply (acl_live _ _ _ _ _ _ _ (INBL b Hb)); lia| apply rng_out_cons; [lia| apply rng_out_nil]]. }
clear PR3 PFA3 DR2 ST2 ART2 MI2 SP MU3 WM3 ACC2.
clear m3. rename m3b into m3. rename ART2b into ART2. rename MI3b into MI2. rename ST2b into ST2. rename DR2b into DR2. rename PFA3b into PFA3. rename SP3 into SP.
destruct (hp_fz m3 (AF_DRV _ _ ART2) PFA3) as (PFR3 & _).
pose proof (h_acc_at OUT_rep IO_FP IO_img X HX m3 PFR3) as (_ & ACF & _). unfold HO_FSZ in ACF. clear PFR3.
eapply (hp_ctl Σ2 m3 cc3 T _ D LBD CtlGetFrameSize (F + 8384));
[exact Hc3 | reflexivity | reflexivity | reflexivity | reflexivity | exact FRM2 | rewrite EF2; exact EF | rewrite ES2; exact ESP | lia | reflexivity | exact DR2
| rewrite depth_ctl; exact (depth_init mo) | exact NDB | exact INBL | exact I
| exists (Z64 (h_frame_size h)); exact FSZ
| lia | cbn [creq_size]; lia | exact ACF | cbn [creq_align]; clear - F64; Z.div_mod_to_equations; lia | exact ART2 | exact MI2 | exact ST2 | ].
intros Σ3 m4 cc4 t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' Fr3 fc3 Hc4 FRM3 EL3 EF3 ES3 EP3 EC3 ART3 MI3 ST3 PR DR3 POST ACC3.
clear Hc3.
cbn [creq_size] in PR. destruct POST as (FSZ3 & FSR3).
set (fs := fst (speex_decoder_ctl (snd (speex_decoder_ctl (init_dec mo) (CtlSetEnh 1))) CtlGetFrameSize)) in *.
pose proof (pres_fp_trans _ _ _ _ m2 m3 m4 PFA3 (hp_acc Σ2 m3 m4 _ _ ART2 ELn3 ltac:(rewrite EF2; exact EF) ltac:(rewrite ES2; exact ESP) PR
ltac:(intros l hh [E|Hin]; [injection E as <- <-; right; left; exists (F + 8384), (F + 8388); split; [right; right; right; left; reflexivity| lia]
| exact (iv_hp_blocks _ LBD l hh INB' Hin)]))) as PFA4.
clear PFA3.
hp_tr PR LSH. hp_tr PR ENH2. hp_tr PR J12. hp_tr PR CBK. hp_tr PR J16. hp_tr PR RATE. hp_tr PR LOOK.
eapply (htr_rw _ _ _ _ _ _ PR) in HC; rewrite ?HCS; [| hp_acl | hp_rng].
eapply (htr_rw _ _ _ _ _ _ PR) in SP; [| unfold h_spill; rewrite hsp_size; hp_acl | unfold h_spill; rewrite hsp_size; hp_rng].
clear PR FSZ.
rewrite <- EL3 in INBL, INV.

pose proof (hi_F _ _ _ HX) as (_ & _ & _ & FSHX & _). change (fs_size 8) with 16384 in FSHX.
assert (AOV : aobj bsegs m4 v 80).
{ split; [lia|]. split; [unfold APP_TOP; unfold USTACK_TOP in *; lia|]. exact (proj2 (af_acc_live RT AF Σ3 m4 _ _ ART3 INV)). }
assert (HPR : -2^31 <= h_rate h < 2^31) by (destruct HP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R & _); exact R).
refine (rz_evt RT AF Σ3 PMh _ _ T cc4 (PMfd_mat_stable F0 fs0) Hc4 _ _).
{ eapply hp_w6; [reflexivity | unfold USTACK_TOP in *; lia | lia | lia | exact FSHX | unfold SH_LO, SH_HI in *; lia | lia | clear - V16; Z.div_mod_to_equations; lia | lia
| exact FSR3 | exact HPR | exact HRR | exact FSZ3 | exact RATE | exact AOV | exact HC | exact SP | exact MI3]. }
intros ms5 cc5 (m5 & xa0 & xa1 & xa2 & MU5 & WM5 & MI5 & SP5 & POST5) Hc5. clear Hc4.
assert (ELn4 : rt_live RT Σ3 = (NEW ++ [(v, 80)]) ++ rt_live RT Σ1) by (rewrite EL3, EL2; exact ELn).
assert (EF4 : rt_frames RT Σ3 = [(F, 8%nat)]) by (rewrite EF3, EF2; exact EF).
assert (ES4 : rt_sp0 RT Σ3 = x_sp0 X) by (rewrite ES3, ES2; exact ESP).
pose proof (art_munch_h Σ3 m4 m5 _ ART3 EF4 ES4 MU5 WM5
ltac:(intros l hh [E|[E|[]]]; injection E as <- <-; [left; unfold USTACK_TOP in *; lia| right; right; lia])) as ART5.
assert (PR5 : rt_pres_fp (rt_live RT Σ3) [(F, 8%nat)] S1 [(S1, S1 + 248); (F + 9232, F + 9236)] m4 m5)
by (apply (pf_munch_h _ m4 m5 _ _ MU5); intros x Hx; exact Hx).
pose proof (pres_fp_trans _ _ _ _ m2 m4 m5 PFA4 (hp_acc Σ3 m4 m5 _ _ ART3 ELn4 EF4 ES4 PR5
ltac:(intros l hh [E|[E|[]]]; injection E as <- <-; apply iv_hp_wh;
[left; reflexivity| right; right; right; right; left; reflexivity]))) as PFA5.
clear PFA4.
assert (ST5 : stk bsegs m5 lo S1).
{ apply (stk_agree bsegs m4 m5 lo S1 ST3); [| exact WM5]. apply (agree_of_munch _ m4 m5 _ MU5). intros x Hx. cbn [outside].
split; [lia| split; [lia| exact I]]. }
hp_tr PR5 LSH. hp_tr PR5 ENH2. hp_tr PR5 J12. hp_tr PR5 CBK. hp_tr PR5 J16. hp_tr PR5 FSZ3. hp_tr PR5 LOOK.
eapply (htr_rw _ _ _ _ _ _ PR5) in HC; rewrite ?HCS; [| hp_acl | hp_rng].
assert (DR5 : DREP (F + HO_OUT) (F + HO_STEREO) m5 D (snd (speex_decoder_ctl (snd (speex_decoder_ctl (init_dec mo) (CtlSetEnh 1))) CtlGetFrameSize)) LBD).
{ apply (drep_tr _ _ _ _ m4 m5 _ _ _ _ _ PR5 DR3). intros b Hb. destruct (BSEP b Hb) as (B0 & B1 & B2 & B3 & B4).
split; [apply (acl_live _ _ _ _ _ _ _ (INBL b Hb)); lia| apply rng_out_cons; [lia| apply rng_out_cons; [lia| apply rng_out_nil]]]. }
clear PR5 DR3 ST3 MI3 MU5 WM5.
assert (CR3 : x_cr0 X - h_cost h - 8 <= rt_credit RT Σ3) by lia.
assert (KC64 : h_cost h + 64 <= FUZZ_COST - 1) by (unfold h_cost, H_HDR_CREDIT, H_DEC_CREDIT, FUZZ_COST; rewrite PC0; lia).
assert (HSX3 : hsig_x Σ3 a h 64 (NEW ++ [(v, 80)])).
{ split; [rewrite ELn4, EL1; reflexivity|]. split; [exact ND1|]. split; [exact PERM1|]. split; [exact EF4|]. split; [exact ES4|].
split; [rewrite EP3, EP2; exact EPO| lia]. }
assert (DEC5 : h_dec_rep X m5 a h) by (unfold h_dec_rep in *; rewrite STN in *; exact DEC0).
destruct POST5 as [(FB & ->) | (FG & RATE5 & ->)].
{
replace ((fs <? 0) || (640 <? fs)) with true in Hk
by (symmetry; destruct (Z.ltb_spec fs 0); [reflexivity|]; cbn [orb]; apply Z.ltb_lt; lia).
cbv iota in Hk.
destruct (hp_fz m5 (AF_DRV _ _ ART5) PFA5) as (PF5 & ERR5 & OUTR5 & SSP5 & _ & BITS5 & SY5 & _ & _ & OSR5 & _).
eapply (hp_f48_ok h a 64 v D _ LBD NEW Σ3 m5 cc5 T);
[exact Hc5 | exact FRM3 | exact HSX3 | exact KC64 | exact STN | exact SI1 | exact HP0 | exact PNEW | exact NDB | exact DR5
| rewrite !depth_ctl; exact (depth_init mo) | exact ART5 | exact MI5 | exact ST5 | exact PF5 | exact ERR5 | exact OUTR5 | exact SSP5
| exact SP5 | exact LSH | exact BITS5 | exact OSR5 | exact SY5 | exact DEC5 | exact Hk]. }

replace ((fs <? 0) || (640 <? fs)) with false in Hk by (symmetry; apply orb_false_intro; [apply Z.ltb_ge| apply Z.ltb_ge]; lia).
cbv iota in Hk.
set (rate := if h_rate h =? 0 then hd_rate hd else h_rate h) in *.
assert (RTR : -2^31 <= rate < 2^31) by (unfold rate; destruct (h_rate h =? 0); lia).
destruct (hp_fz m5 (AF_DRV _ _ ART5) PFA5) as (PFR5 & _).
pose proof (h_acc_at OUT_rep IO_FP IO_img X HX m5 PFR5) as (_ & _ & _ & _ & _ & _ & _ & _ & ACR & _). unfold HO_RATE in ACR. clear PFR5.
eapply (hp_ctl Σ3 m5 cc5 T _ D LBD (CtlSetSamplingRate rate) (F + 9232));
[exact Hc5 | reflexivity | reflexivity | reflexivity | reflexivity | exact FRM3 | exact EF4 | exact ES4 | lia | reflexivity | exact DR5
| rewrite !depth_ctl; exact (depth_init mo) | exact NDB | exact INBL | exact I
| exists (Z64 rate); split; [exact RATE5| split; [apply c4_mod32| exact RTR]]
| lia | cbn [creq_size]; lia | exact ACR | cbn [creq_align]; clear - F64; Z.div_mod_to_equations; lia | exact ART5 | exact MI5 | exact ST5 | ].
intros Σ4 m6 cc6 u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 Fr4 fc4 Hc6 FRM4 EL6 EF6 ES6 EP6 EC6 ART6 MI6 ST6 PR DR6 POST ACC6.
clear Hc5.
cbn [creq_size] in PR. destruct POST as (wr & RATE6 & WRM). apply (c4_eqm m6 _ wr rate) in RATE6; [| exact WRM]. clear RATE5.
assert (ELn5 : rt_live RT Σ3 = (NEW ++ [(v, 80)]) ++ rt_live RT Σ1) by exact ELn4.
pose proof (pres_fp_trans _ _ _ _ m2 m5 m6 PFA5 (hp_acc Σ3 m5 m6 _ _ ART5 ELn5 EF4 ES4 PR
ltac:(intros l hh [E|Hin]; [injection E as <- <-; right; left; exists (F + 9232), (F + 9236); split; [right; right; right; right; left; reflexivity| lia]
| exact (iv_hp_blocks _ LBD l hh INB' Hin)]))) as PFA6.
clear PFA5.
hp_tr PR LSH. hp_tr PR ENH2. hp_tr PR J12. hp_tr PR CBK. hp_tr PR J16. hp_tr PR FSZ3. hp_tr PR LOOK.
eapply (htr_rw _ _ _ _ _ _ PR) in HC; rewrite ?HCS; [| hp_acl | hp_rng].
eapply (htr_rw _ _ _ _ _ _ PR) in SP5; [| rewrite hsp_size; hp_acl | rewrite hsp_size; hp_rng].
clear PR.
rewrite <- EL6 in INBL, INV.

assert (lookahead_range : forall d : dec_state bptr, (dec_depth d <= 3)%nat -> 0 <= fst (speex_decoder_ctl d CtlGetLookahead) <= 160).
{ intros d0 H0. destruct d0 as [st|s0 [st|s0' [st|s0'' [st|s3 low]]]]; cbn [dec_depth] in H0; try lia; cbn [speex_decoder_ctl nb_decoder_ctl fst]; unfold NB_SUBFRAME_SIZE; lia. }

assert (HCR : -2^31 <= h_channels h < 2^31) by (destruct HP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R & _); exact R).
assert (AOV6 : aobj bsegs m6 v 80).
{ split; [lia|]. split; [unfold APP_TOP; unfold USTACK_TOP in *; lia|]. exact (proj2 (af_acc_live RT AF Σ4 m6 _ _ ART6 INV)). }
refine (rz_evt RT AF Σ4 PMh _ _ T cc6 (PMfd_mat_stable F0 fs0) Hc6 _ _).
{ eapply hp_w7; [reflexivity | unfold USTACK_TOP in *; lia | exact FI | lia | exact FSHX | unfold SH_LO, SH_HI in *; lia | exact ESF
| unfold SH_LO, SH_HI in *; lia | exact F64 | lia | lia | lia | clear - V16; Z.div_mod_to_equations; lia | lia
| exact HFP | exact HCR | exact HNC | exact AOV6 | exact HC | exact SP5 | exact CBK | exact LSH | exact (AF_LIB _ _ ART6) | exact MI6]. }
intros ms7 cc7 (m7 & xb0 & xb1 & xb2 & MU7 & WM7 & MI7 & SP7 & LSH7 & POST7) Hc7. clear Hc6.
assert (EF7 : rt_frames RT Σ4 = [(F, 8%nat)]) by (rewrite EF6; exact EF4).
assert (ES7 : rt_sp0 RT Σ4 = x_sp0 X) by (rewrite ES6; exact ES4).
assert (ELn7 : rt_live RT Σ4 = (NEW ++ [(v, 80)]) ++ rt_live RT Σ1) by (rewrite EL6; exact ELn5).
pose proof (art_munch_h Σ4 m6 m7 _ ART6 EF7 ES7 MU7 WM7
ltac:(intros l hh [E|[E|[]]]; injection E as <- <-; [left; unfold USTACK_TOP in *; lia| right; right; lia])) as ART7.
assert (PR7 : rt_pres_fp (rt_live RT Σ4) [(F, 8%nat)] S1 [(S1, S1 + 248); (F + 48, F + 72)] m6 m7)
by (apply (pf_munch_h _ m6 m7 _ _ MU7); intros x Hx; exact Hx).
pose proof (pres_fp_trans _ _ _ _ m2 m6 m7 PFA6 (hp_acc Σ4 m6 m7 _ _ ART6 ELn7 EF7 ES7 PR7
ltac:(intros l hh [E|[E|[]]]; injection E as <- <-;
[apply iv_hp_wh; left; reflexivity| right; left; exists (F + 32), (F + 88); split; [right; right; left; reflexivity| lia]]))) as PFA7.
clear PFA6.
assert (ST7 : stk bsegs m7 lo S1).
{ apply (stk_agree bsegs m6 m7 lo S1 ST6); [| exact WM7]. apply (agree_of_munch _ m6 m7 _ MU7). intros x Hx. cbn [outside].
split; [lia| split; [lia| exact I]]. }
hp_tr PR7 ENH2. hp_tr PR7 J12. hp_tr PR7 J16. hp_tr PR7 FSZ3. hp_tr PR7 RATE6. hp_tr PR7 LOOK.
eapply (htr_rw _ _ _ _ _ _ PR7) in HC; rewrite ?HCS; [| hp_acl | hp_rng].
assert (DR7 : DREP (F + HO_OUT) (F + HO_STEREO) m7 D
(snd (speex_decoder_ctl (snd (speex_decoder_ctl (snd (speex_decoder_ctl (init_dec mo) (CtlSetEnh 1))) CtlGetFrameSize)) (CtlSetSamplingRate rate))) LBD).
{ apply (drep_tr _ _ _ _ m6 m7 _ _ _ _ _ PR7 DR6). intros b Hb. destruct (BSEP b Hb) as (B0 & B1 & B2 & B3 & B4).
split; [apply (acl_live _ _ _ _ _ _ _ (INBL b Hb)); lia| apply rng_out_cons; [lia| apply rng_out_cons; [lia| apply rng_out_nil]]]. }
clear PR7 DR6 ST6 MI6 MU7 WM7 SP5 LSH CBK.

assert (K8 : forall (Σ5 : rts RT) (m8 : mem) (cc8 : config) (ch : Z) (d4 : dec_state bptr)
(ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) Fr' fc' (w104 : word) (cb : list cell),
ASTA RT Σ5 PMh (eq (MS (mkR ra' (Z64 S1) (x_gp X) (Z64 0x638c98) t0' t1' t2' (Z64 usp) (Z64 S1) a0' a1' a2' a3' a4' a5' a6' a7'
(Z64 SHB) (Z64 sf) (Z64 (h_packet_count h)) (Z64 v) (Z64 (-8)) (Z64 0x7fffffff) (Z64 pno) (Z64 (F + 48)) (Z64 (F + HO_BITS)) (Z64 ch)
t3' t4' t5' t6') Fr' (Z64 0x972e4) fc' None m8 (seg_rom bsegs))) cc8 ->
X1cn.frm0 fc' ->
rt_live RT Σ5 = (NEW ++ [(v, 80)]) ++ rt_live RT Σ1 -> rt_frames RT Σ5 = [(F, 8%nat)] -> rt_sp0 RT Σ5 = x_sp0 X -> rt_pois RT Σ5 = [] ->
x_cr0 X - h_cost h - 12 <= rt_credit RT Σ5 ->
ART RT Σ5 m8 -> mem_inv bsegs m8 -> stk bsegs m8 lo S1 ->
rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 W_h m2 m8 ->
rw_cells bsegs m8 S1 (hsp (Z64 (sf + 16)) (Z64 F) (Z64 F) (Z64 (x_d X)) (Z64 (F + 64)) (Z64 (h_bytes_remaining h)) v48 v56 (Z64 (F + HO_RATE))
(Z64 (F + HO_CBK)) (Z64 fs) v88 (Z64 (F + HO_ENH)) w104 (Z64 (F + HO_OY)) (Z64 SHB) (Z64 (F + HO_STEREO))
(Z64 (h_last_granule h)) (Z64 (F + HO_OG)) (Z64 (F + HO_OS)) (Z64 (F + HO_OP)) (Z64 (h_speex_serialno h)) (Z64 (F + HO_LOOK))
(Z64 (F + HO_FSZ)) (Z64 (F + HO_BITS)) (Z64 (hd_frames_per_packet hd)) (Z64 (F + HO_OUT)) (Z64 D) j224 j232 (Z64 F)) ->
rw_cells bsegs m8 sf [CB 16 HSH_L_HDR] ->
rw_cells bsegs m8 (F + 32) [C4 wenh] -> rw_cells bsegs m8 (F + 36) [CB 12 j12] -> rw_cells bsegs m8 (F + 48) cb -> cells_size cb = 24%nat ->
rw_cells bsegs m8 (F + 72) [CB 16 j16] ->
rw_cells bsegs m8 (F + 8384) [C4 (Z64 fs)] -> rw_cells bsegs m8 (F + 9232) [C4 (Z64 rate)] -> rw_cells bsegs m8 (F + 9248) [C4 (Z_to_bv 64 wl)] ->
rw_cells bsegs m8 v (spx_header_cells junk28 hd w1 w2 w3 r1 r2) ->
DREP (F + HO_OUT) (F + HO_STEREO) m8 D d4 LBD -> (dec_depth d4 <= 3)%nat -> isave_ok d4 -> dec_nestedR d4 ->
(ch = 1 \/ ch = 2) -> 1 <= hd_frames_per_packet hd <= 10 ->
(forall c', (if 2147483646 <? hd_extra_headers hd then at_XT RT OUT_rep ERR_rep IO_FP X F0 fs0 c'
else at_KH RT OUT_rep ERR_rep IO_FP X F0 fs0
(incr_packet_count (set_header h (snd (speex_decoder_ctl d4 CtlGetLookahead)) (hd_frames_per_packet hd) ch rate (hd_extra_headers hd) fs))
pno nbr brem0 c') -> realizes bsegs c' T) ->
realizes bsegs cc8 T).
{ intros Σ5 m8 cc8 ch d4 kra kt0 kt1 kt2 ka0 ka1 ka2 ka3 ka4 ka5 ka6 ka7 kt3 kt4 kt5 kt6 kFr kfc w104 cb
Hc8 FRM8 EL8 EF8 ES8 EP8 EC8 ART8 MI8 ST8 PFA8 SP8 LSH8 ENH8 J12' CB8 CBS8 J16' FSZ8 RATE8 LOOK8 HC8 DR8 DD8 ISV8 NST8 CH8 NF8 Hk8.
clear Hc7 Hk.
clear SP J12 J16 RATE LOOK HC ART0 MI ST DR Fr2 fc2 FRM2 EL2 EF2 ES2 EP2 EC2 ART2 MI2 ST2 DR2 ENH2 ACF Fr3 fc3 FRM3 EL3 EF3 ES3 EP3 EC3 ART3 FSZ3
ACC3 ELn3 AOV MI5 ELn4 EF4 ES4 ART5 ST5 DR5 CR3 HSX3 DEC5 ACR Fr4 fc4 FRM4 EL6 EF6 ES6 EP6 EC6 ART6 RATE6 WRM ACC6 ELn5 AOV6 MI7 SP7 LSH7 POST7
EF7 ES7 ELn7 ART7 PFA7 ST7 DR7 INBL INV INDL DL DP0 FRM EL EF ESP EPO ECR ACE ACB CRS.
assert (INV8 : In (v, 80) (rt_live RT Σ5)) by (rewrite EL8; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
assert (INBL8 : forall b, In b LBD -> In (blk_addr b, blk_size b) (rt_live RT Σ5)) by (intros b Hb; rewrite EL8; apply in_or_app; left; exact (INB' b Hb)).
assert (AOV8 : aobj bsegs m8 v 80).
{ split; [lia|]. split; [unfold APP_TOP; unfold USTACK_TOP in *; lia|]. exact (proj2 (af_acc_live RT AF Σ5 m8 _ _ ART8 INV8)). }

refine (rz_evt RT AF Σ5 PMh _ _ T cc8 (PMfd_mat_stable F0 fs0) Hc8 _ _).
{ eapply hp_w8; [unfold USTACK_TOP in *; lia | unfold SH_LO, SH_HI in *; lia | lia | clear - V16; Z.div_mod_to_equations; lia | lia
| exact HEX | exact AOV8 | exact HC8 | exact SP8 | exact MI8]. }
intros ms9 cc9 (m9 & xc0 & xc1 & xc2 & MU9 & WM9 & MI9 & SP9 & POST9) Hc9. clear Hc8.
pose proof (art_munch_h Σ5 m8 m9 _ ART8 EF8 ES8 MU9 WM9 ltac:(intros l hh [E|[]]; injection E as <- <-; left; unfold USTACK_TOP in *; lia)) as ART9.
assert (PR9 : rt_pres_fp (rt_live RT Σ5) [(F, 8%nat)] S1 [(S1, S1 + 248)] m8 m9) by (apply (pf_munch_h _ m8 m9 _ _ MU9); intros x Hx; exact Hx).
pose proof (pres_fp_trans _ _ _ _ m2 m8 m9 PFA8 (hp_acc Σ5 m8 m9 _ _ ART8 EL8 EF8 ES8 PR9
ltac:(intros l hh [E|[]]; injection E as <- <-; apply iv_hp_wh; left; reflexivity))) as PFA9.
clear PFA8.
assert (ST9 : stk bsegs m9 lo S1).
{ apply (stk_agree bsegs m8 m9 lo S1 ST8); [| exact WM9]. apply (agree_of_munch _ m8 m9 _ MU9). intros x Hx. cbn [outside]. split; [lia| exact I]. }
hp_tr PR9 LSH8. hp_tr PR9 ENH8. hp_tr PR9 J12'. hp_tr PR9 J16'. hp_tr PR9 FSZ8. hp_tr PR9 RATE8. hp_tr PR9 LOOK8.
eapply (htr_rw _ _ _ _ _ _ PR9) in CB8; rewrite ?CBS8; [| hp_acl | hp_rng].
eapply (htr_rw _ _ _ _ _ _ PR9) in HC8; rewrite ?HCS; [| hp_acl | hp_rng].
assert (DR9 : DREP (F + HO_OUT) (F + HO_STEREO) m9 D d4 LBD).
{ apply (drep_tr _ _ _ _ m8 m9 _ _ _ _ _ PR9 DR8). intros b Hb. destruct (BSEP b Hb) as (B0 & B1 & B2 & B3 & B4).
split; [apply (acl_live _ _ _ _ _ _ _ (INBL8 b Hb)); lia| apply rng_out_cons; [lia| apply rng_out_nil]]. }
clear PR9 DR8 ST8 MI8 MU9 WM9 SP8.
assert (HSX8 : hsig_x Σ5 a h 64 (NEW ++ [(v, 80)])).
{ split; [rewrite EL8, EL1; reflexivity|]. split; [exact ND1|]. split; [exact PERM1|]. split; [exact EF8|]. split; [exact ES8|].
split; [exact EP8| lia]. }
assert (DEC9 : h_dec_rep X m9 a h) by (unfold h_dec_rep in *; rewrite STN in *; exact DEC0).
destruct POST9 as [(XE & ->) | (XN & ->)].
{
replace (2147483646 <? hd_extra_headers hd) with true in Hk8 by (symmetry; apply Z.ltb_lt; lia).
destruct (hp_fz m9 (AF_DRV _ _ ART9) PFA9) as (PF9 & ERR9 & OUTR9 & SSP9 & _ & BITS9 & SY9 & _ & _ & OSR9 & _).
eapply (hp_f48_ok h a 64 v D d4 LBD NEW Σ5 m9 cc9 T);
[exact Hc9 | exact FRM8 | exact HSX8 | exact KC64 | exact STN | exact SI1 | exact HP0 | exact PNEW | exact NDB | exact DR9
| exact DD8 | exact ART9 | exact MI9 | exact ST9 | exact PF9 | exact ERR9 | exact OUTR9 | exact SSP9
| exact SP9 | exact LSH8 | exact BITS9 | exact OSR9 | exact SY9 | exact DEC9 | exact Hk8]. }
replace (2147483646 <? hd_extra_headers hd) with false in Hk8 by (symmetry; apply Z.ltb_ge; lia).

destruct (hp_fz m9 (AF_DRV _ _ ART9) PFA9) as (PFR9 & _).
pose proof (h_unwind m9 0x97310 PFR9 ltac:(clear; vm_compute; tauto) ltac:(lia)) as UW9. clear PFR9.
unfold A_free_hp in Hc9. change 0x67f80 with e_free in Hc9.
cps_rt (FRE Σ5 PMh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m9 v 80 lo).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ unfold call_ok. rewrite unsigned_lit by (unfold USTACK_TOP in *; lia).
split; [exact ST9|]. split; [rewrite ES8; exact LW|]. split; [unfold RT_STACK; lia|]. split; [unfold USTACK_TOP in *; lia|].
clear - S32. Z.div_mod_to_equations. lia. }
intros cc10 (Σ6 & v10 & Hc10 & EL10 & EF10 & ES10 & EC10 & EP10). clear Hc9.
cps_unpack Hc10 as (m10 & RS & RA10 & PR10).
destruct RA10 as (ART10 & MI10 & ST10).

pose proof (own_pos_h m0 a h OSR0 DEC0 HP0) as OPOS.
assert (BPOS : forall e, In e NEW -> 0 < snd e).
{ intros e He. apply (Permutation_in _ PNEW) in He. unfold blocks_live in He. apply in_map_iff in He as (b & <- & Hb). cbn [snd].
exact (h_drep_sizes_pos _ _ _ m9 _ _ DR9 b Hb). }
assert (RPOS : forall e, In e (rt_live RT Σ1) -> 0 < snd e).
{ intros [p q] He. rewrite EL1 in He. apply in_app_or in He as [He|He]; [exact (OPOS p q (Permutation_in _ PERM1 He))| exact (proj1 (hi_live _ _ _ HX) p q He)]. }
assert (ND5 : List.NoDup (map fst (rt_live RT Σ5))).
{ apply (live_nodup_pos Σ5 m9 ART9). rewrite EL8. intros e He. apply in_app_or in He as [He|He]; [| exact (RPOS e He)].
apply in_app_or in He as [He|[E|[]]]; [exact (BPOS e He)| subst e; cbn; lia]. }
assert (EL6' : rt_live RT Σ6 = NEW ++ rt_live RT Σ1).
{ rewrite EL8, !map_app, <- app_assoc in ND5. cbn [map app fst] in ND5.
rewrite EL10, EL8, <- app_assoc. cbn [app].
rewrite live_remove_app, live_remove_cons. cbn [fst]. rewrite Z.eqb_refl. cbv iota.
rewrite (live_remove_none v NEW), (live_remove_none v (rt_live RT Σ1)); [reflexivity| |].
- intros e He E. apply (NoDup_remove_2 _ _ _ ND5). rewrite <- E. apply in_or_app. right. exact (in_map fst _ _ He).
- intros e He E. apply (NoDup_remove_2 _ _ _ ND5). rewrite <- E. apply in_or_app. left. exact (in_map fst _ _ He). }
rewrite EF8 in PR10. apply (pres_fp_of_pres _ _ _ []) in PR10.
assert (EF11 : rt_frames RT Σ6 = [(F, 8%nat)]) by (rewrite EF10; exact EF8).
assert (ES11 : rt_sp0 RT Σ6 = x_sp0 X) by (rewrite ES10; exact ES8).
assert (PR10h : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 W_h m9 m10).
{ apply (pres_fp_weaken _ _ _ [] _ m9 m10); [| intros x _; exact I].
apply (pres_fp_mono _ _ _ (rt_live RT Σ6) [(F, 8%nat)] S1 [] m9 m10 PR10); [intros e He; rewrite EL6'; apply in_or_app; right; exact He| intros e He; exact He| lia]. }
pose proof (pres_fp_trans _ _ _ _ m2 m9 m10 PFA9 PR10h) as PFA10. clear PFA9 PR10h.
assert (INBL10 : forall b, In b LBD -> In (blk_addr b, blk_size b) (rt_live RT Σ6)) by (intros b Hb; rewrite EL6'; apply in_or_app; left; exact (INB b Hb)).
hp_tr PR10 LSH8. hp_tr PR10 ENH8. hp_tr PR10 J12'. hp_tr PR10 J16'. hp_tr PR10 FSZ8. hp_tr PR10 RATE8. hp_tr PR10 LOOK8.
eapply (htr_rw _ _ _ _ _ _ PR10) in CB8; rewrite ?CBS8; [| hp_acl | hp_rng].
eapply (htr_rw _ _ _ _ _ _ PR10) in SP9; [| rewrite hsp_size; hp_acl | rewrite hsp_size; hp_rng].
assert (DR10 : DREP (F + HO_OUT) (F + HO_STEREO) m10 D d4 LBD).
{ apply (drep_tr _ _ _ _ m9 m10 _ _ _ _ _ PR10 DR9). intros b Hb. destruct (BSEP b Hb) as (B0 & B1 & B2 & B3 & B4).
split; [apply (acl_live _ _ _ _ _ _ _ (INBL10 b Hb)); lia| apply rng_out_nil]. }
clear PR10 DR9 ST9 MI9 ART9 HC8 AOV8 INV8 INBL8 ND5.

refine (rz_evt RT AF Σ6 PMh _ _ T cc10 (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply hp_w9; [reflexivity | unfold USTACK_TOP in *; lia | unfold SH_LO, SH_HI in *; lia | lia | exact LSH8 | exact SP9 | exact MI10]. }
intros ms11 cc11 (m11 & -> & MU11 & WM11 & MI11 & LSH11) Hc11. clear Hc.
pose proof (art_munch_h Σ6 m10 m11 _ ART10 EF11 ES11 MU11 WM11 ltac:(intros l hh [E|[]]; injection E as <- <-; right; left; lia)) as ART11.
assert (PR11 : rt_pres_fp (rt_live RT Σ6) [(F, 8%nat)] S1 [(sf, sf + 16)] m10 m11) by (apply (pf_munch_h _ m10 m11 _ _ MU11); intros x Hx; exact Hx).
pose proof (pres_fp_trans _ _ _ _ m2 m10 m11 PFA10 (hp_acc Σ6 m10 m11 NEW _ ART10 EL6' EF11 ES11 PR11
ltac:(intros l hh [E|[]]; injection E as <- <-; apply iv_hp_wh; right; left; reflexivity))) as PFA11.
clear PFA10.
assert (ST11 : stk bsegs m11 lo S1).
{ apply (stk_agree bsegs m10 m11 lo S1 ST10); [| exact WM11]. apply (agree_of_munch _ m10 m11 _ MU11). intros x Hx. cbn [outside].
split; [unfold SH_LO, SH_HI in *; lia| exact I]. }
hp_tr PR11 ENH8. hp_tr PR11 J12'. hp_tr PR11 J16'. hp_tr PR11 FSZ8. hp_tr PR11 RATE8. hp_tr PR11 LOOK8.
eapply (htr_rw _ _ _ _ _ _ PR11) in CB8; rewrite ?CBS8; [| hp_acl | hp_rng].
eapply (htr_rw _ _ _ _ _ _ PR11) in SP9; [| rewrite hsp_size; hp_acl | rewrite hsp_size; hp_rng].
assert (DR11 : DREP (F + HO_OUT) (F + HO_STEREO) m11 D d4 LBD).
{ apply (drep_tr _ _ _ _ m10 m11 _ _ _ _ _ PR11 DR10). intros b Hb. destruct (BSEP b Hb) as (B0 & B1 & B2 & B3 & B4).
split; [apply (acl_live _ _ _ _ _ _ _ (INBL10 b Hb)); lia| apply rng_out_cons; [lia| apply rng_out_nil]]. }
clear PR11 DR10 ST10 MI10 MU11 WM11 LSH8.

assert (CRB : 1000 <= x_cr0 X - h_cost h - 12) by (pose proof (hi_cr _ _ _ HX) as FC; unfold h_cost, H_HDR_CREDIT, H_DEC_CREDIT, FUZZ_COST in *; rewrite PC0; lia).
destruct (hp_fz m11 (AF_DRV _ _ ART11) PFA11) as (PFR11 & _).
pose proof (h_acc_at OUT_rep IO_FP IO_img X HX m11 PFR11) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ACL). unfold HO_LOOK in ACL. clear PFR11.
eapply (hp_ctl Σ6 m11 cc11 T d4 D LBD CtlGetLookahead (F + 9248));
[exact Hc11 | reflexivity | reflexivity | reflexivity | reflexivity | exact FRM8 | exact EF11 | exact ES11 | rewrite EC10; lia | reflexivity | exact DR11
| exact DD8 | exact NDB | exact INBL10 | exact I | exists (Z64 wl); exact LOOK8
| lia | cbn [creq_size]; lia | exact ACL | cbn [creq_align]; clear - F64; Z.div_mod_to_equations; lia | exact ART11 | exact MI11 | exact ST11 | ].
intros Σ7 m12 cc12 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10' v11 v12 v13 Fr7 fc7 Hc12 FRM12 EL12 EF12 ES12 EP12 EC12 ART12 MI12 ST12 PR DR12 POST ACC12.
clear Hc11.
cbn [creq_size] in PR. destruct POST as (LOOK12 & LKR).
assert (INBL12 : forall b, In b LBD -> In (blk_addr b, blk_size b) (NEW)) by exact INB.
pose proof (pres_fp_trans _ _ _ _ m2 m11 m12 PFA11 (hp_acc Σ6 m11 m12 NEW _ ART11 EL6' EF11 ES11 PR
ltac:(intros l hh [E|Hin]; [injection E as <- <-; right; left; exists (F + 9248), (F + 9252); split; [right; right; right; right; right; left; reflexivity| lia]
| exact (iv_hp_blocks _ LBD l hh INBL12 Hin)]))) as PFA12.
clear PFA11.
hp_tr PR LSH11. hp_tr PR ENH8. hp_tr PR J12'. hp_tr PR J16'. hp_tr PR FSZ8. hp_tr PR RATE8.
eapply (htr_rw _ _ _ _ _ _ PR) in CB8; rewrite ?CBS8; [| hp_acl | hp_rng].
eapply (htr_rw _ _ _ _ _ _ PR) in SP9; [| rewrite hsp_size; hp_acl | rewrite hsp_size; hp_rng].
clear PR LOOK8.

refine (rz_evt RT AF Σ7 PMh _ _ T cc12 (PMfd_mat_stable F0 fs0) Hc12 _ _).
{ eapply (hp_w10 _ (h_packet_count h)); [reflexivity | unfold USTACK_TOP in *; lia | rewrite PC0; lia | exact SP9 | exact MI12]. }
intros ms13 cc13 -> Hc13. clear Hc12. rewrite PC0 in Hc13. change (0 + 1) with 1 in Hc13.
apply Hk8. cbv iota.
set (d5 := snd (speex_decoder_ctl d4 CtlGetLookahead)).
assert (LB19 : (length LBD <= 19)%nat).
{ pose proof (Permutation_length PNEW) as PL. unfold blocks_live in PL. rewrite length_map in PL.
assert (I19 : init_nblocks mo <= 19) by (destruct mo; cbn; lia). lia. }
assert (ENH56 : exists je, rw_cells bsegs m12 (F + HO_ENH) [CB 56 je]).
{ assert (R : rw_cells bsegs m12 (F + 32) (([C4 wenh] ++ [CB 12 j12]) ++ cb ++ [CB 16 j16])).
{ apply rw_cells_app. split.
- apply rw_cells_app. split; [exact ENH8|]. cbn [cells_size csize Nat.add]. replace (F + 32 + Z.of_nat 4) with (F + 36) by lia. exact J12'.
- cbn [cells_size csize Nat.add app]. apply rw_cells_app. split; [replace (F + 32 + Z.of_nat 16) with (F + 48) by lia; exact CB8|].
rewrite CBS8. replace (F + 32 + Z.of_nat 16 + Z.of_nat 24) with (F + 72) by lia. exact J16'. }
destruct (rw_cells_forget bsegs m12 _ _ R) as (je & R').
rewrite !cells_size_app, CBS8 in R'. cbn [cells_size csize Nat.add] in R'. exists je. unfold HO_ENH. exact R'. }
assert (SPh : rw_cells bsegs m12 S1 (h_spill X (Z64 (h_bytes_remaining h)) v48 v56 v88 j224 j232
(HA (a_Dsy a) (a_sybytes a) (a_Bd a) (a_L a) (a_G a) (a_shdr a) (a_body a) (a_lws a) (a_gws a) (a_Dc a) D LBD (NEW ++ a_P a))
(incr_packet_count (set_header h d5 (hd_frames_per_packet hd) ch rate (hd_extra_headers hd) fs)))).
{ unfold h_spill. cbn [incr_packet_count set_header h_granule_frame_size h_extra_headers h_eos h_nframes h_channels].
replace (if hd_frames_per_packet hd =? 0 then 1 else hd_frames_per_packet hd) with (hd_frames_per_packet hd)
by (destruct (Z.eqb_spec (hd_frames_per_packet hd) 0); lia).
exact SP9. }
assert (DP0 : 0 < D) by exact (proj1 (decst_rep_pos _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DR12)).
eapply (hp_kh_ok Σ7 m12 cc13 D d5 LBD NEW (hd_frames_per_packet hd) ch rate (hd_extra_headers hd) fs);
[exact Hc13 | exact FRM12 | rewrite EL12, EL6', EL1; reflexivity | rewrite EF12; exact EF11 | rewrite ES12; exact ES11
| rewrite EP12, EP10; exact EP8 | lia | exact PNEW | exact NDB | exact AL8 | exact LB19 | exact ART12 | exact MI12 | exact ST12 | exact PFA12
| exact SPh | exact LSH11 | exact ENH56 | exact FSZ8 | exact RATE8 | exists (fst (speex_decoder_ctl d4 CtlGetLookahead)); split; [exact LOOK12| unfold H_LOOK_MAX; exact (lookahead_range d4 DD8)]
| exact DR12 | exact DP0 | unfold d5; rewrite depth_ctl; exact DD8 | unfold d5; apply isave_ctl; [intros off E; discriminate E| exact ISV8]
| unfold d5; apply ctl_nested_same; exact NST8 | lia | exact NF8 | lia | exact RTR | lia]. }
assert (CR4 : x_cr0 X - h_cost h - 12 <= rt_credit RT Σ4) by lia.
assert (HSX4 : hsig_x Σ4 a h 64 (NEW ++ [(v, 80)])).
{ split; [rewrite ELn7, EL1; reflexivity|]. split; [exact ND1|]. split; [exact PERM1|]. split; [exact EF7|]. split; [exact ES7|].
split; [rewrite EP6, EP3, EP2; exact EPO| lia]. }
assert (DEC7 : h_dec_rep X m7 a h) by (unfold h_dec_rep in *; rewrite STN in *; exact DEC0).
assert (DD7 : (dec_depth (snd (speex_decoder_ctl (snd (speex_decoder_ctl (snd (speex_decoder_ctl (init_dec mo) (CtlSetEnh 1))) CtlGetFrameSize))
(CtlSetSamplingRate rate))) <= 3)%nat) by (rewrite !depth_ctl; exact (depth_init mo)).
destruct POST7 as [(NFB & CB7 & ->) | [(NFG & CH1 & CB7 & ->) | (NFG & CH2 & CB7 & ->)]].
{
replace ((hd_frames_per_packet hd <? 1) || (10 <? hd_frames_per_packet hd)) with true in Hk
by (symmetry; destruct (Z.ltb_spec (hd_frames_per_packet hd) 1); [reflexivity|]; cbn [orb]; apply Z.ltb_lt; lia).
cbv iota in Hk.
destruct (hp_fz m7 (AF_DRV _ _ ART7) PFA7) as (PF7 & ERR7 & OUTR7 & SSP7 & _ & BITS7 & SY7 & _ & _ & OSR7 & _).
eapply (hp_f48_ok h a 64 v D _ LBD NEW Σ4 m7 cc7 T);
[exact Hc7 | exact FRM4 | exact HSX4 | exact KC64 | exact STN | exact SI1 | exact HP0 | exact PNEW | exact NDB | exact DR7
| exact DD7 | exact ART7 | exact MI7 | exact ST7 | exact PF7 | exact ERR7 | exact OUTR7 | exact SSP7
| exact SP7 | exact LSH7 | exact BITS7 | exact OSR7 | exact SY7 | exact DEC7 | exact Hk]. }
replace ((hd_frames_per_packet hd <? 1) || (10 <? hd_frames_per_packet hd)) with false in Hk
by (symmetry; apply orb_false_intro; [apply Z.ltb_ge| apply Z.ltb_ge]; lia).
cbv iota in Hk.
assert (ISV3 : isave_ok (snd (speex_decoder_ctl (snd (speex_decoder_ctl (snd (speex_decoder_ctl (init_dec mo) (CtlSetEnh 1))) CtlGetFrameSize))
(CtlSetSamplingRate rate)))).
{ repeat (apply isave_ctl; [intros off E; discriminate E|]). exact (isave_init mo). }
assert (NST3 : dec_nestedR (snd (speex_decoder_ctl (snd (speex_decoder_ctl (snd (speex_decoder_ctl (init_dec mo) (CtlSetEnh 1))) CtlGetFrameSize))
(CtlSetSamplingRate rate)))).
{ repeat apply ctl_nested_same. exact (nested_init mo). }
{
apply Z.eqb_eq in CH1. rewrite CH1 in Hk. cbv iota in Hk.
eapply (K8 Σ4 m7 cc7 1 _); [exact Hc7 | exact FRM4 | exact ELn7 | exact EF7 | exact ES7 | rewrite EP6, EP3, EP2; exact EPO | exact CR4
| exact ART7 | exact MI7 | exact ST7 | exact PFA7 | exact SP7 | exact LSH7 | exact ENH2 | exact J12 | exact CB7 | reflexivity | exact J16
| exact FSZ3 | exact RATE6 | exact LOOK | exact HC | exact DR7 | exact DD7 | exact ISV3 | exact NST3 | left; reflexivity | lia | ].
intros c' Hc'. apply Hk. destruct (2147483646 <? hd_extra_headers hd); exact Hc'. }

replace ((hd_frames_per_packet hd <? 1) || (10 <? hd_frames_per_packet hd)) with false in Hk
by (symmetry; apply orb_false_intro; [apply Z.ltb_ge| apply Z.ltb_ge]; lia).
cbv iota in Hk.
assert (ISV3 : isave_ok (snd (speex_decoder_ctl (snd (speex_decoder_ctl (snd (speex_decoder_ctl (init_dec mo) (CtlSetEnh 1))) CtlGetFrameSize))
(CtlSetSamplingRate rate)))).
{ repeat (apply isave_ctl; [intros off E; discriminate E|]). exact (isave_init mo). }
assert (NST3 : dec_nestedR (snd (speex_decoder_ctl (snd (speex_decoder_ctl (snd (speex_decoder_ctl (init_dec mo) (CtlSetEnh 1))) CtlGetFrameSize))
(CtlSetSamplingRate rate)))).
{ repeat apply ctl_nested_same. exact (nested_init mo). }
apply Z.eqb_neq in CH2. rewrite CH2 in Hk. cbv iota in Hk.
assert (LB7 : bytes_at bsegs m7 (shad F) HSH_L_HDR) by (destruct LSH7 as [[_ B] _]; cbn [cells_bytes cbytes] in B; rewrite app_nil_r in B; rewrite <- ESF; exact B).
destruct (hsh_L_hdr_acc m7 F ltac:(clear - F64; Z.div_mod_to_equations; lia) ltac:(lia) LB7) as (_ & ACB7). clear LB7.
unfold HO_CBK in ACB7. pose proof (acc_sub bsegs m7 (F + 48) 40 (F + 48) 24 ACB7 ltac:(lia) ltac:(lia)) as ACB24.
eapply (hp_ctl Σ4 m7 cc7 T _ D LBD CtlSetHandlerStereo (F + 48));
[exact Hc7 | reflexivity | reflexivity | reflexivity | reflexivity | exact FRM4 | exact EF7 | exact ES7 | lia | reflexivity | exact DR7
| exact DD7 | exact NDB | exact INBL | exact I | exists c52; exact CB7
| lia | cbn [creq_size]; lia | exact ACB24 | cbn [creq_align]; clear - F64; Z.div_mod_to_equations; lia | exact ART7 | exact MI7 | exact ST7 | ].
intros Σ8 m13 cc13 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 Fr8 fc8 Hc13 FRM13 EL13 EF13 ES13 EP13 EC13 ART13 MI13 ST13 PR DR13 POST ACC13.
clear Hc7.
cbn [creq_size] in PR. destruct POST as (pad & CB13).
pose proof (pres_fp_trans _ _ _ _ m2 m7 m13 PFA7 (hp_acc Σ4 m7 m13 _ _ ART7 ELn7 EF7 ES7 PR
ltac:(intros l hh [E|Hin]; [injection E as <- <-; right; left; exists (F + 32), (F + 88); split; [right; right; left; reflexivity| lia]
| exact (iv_hp_blocks _ LBD l hh INB' Hin)]))) as PFA13.
hp_tr PR LSH7. hp_tr PR ENH2. hp_tr PR J12. hp_tr PR J16. hp_tr PR FSZ3. hp_tr PR RATE6. hp_tr PR LOOK.
eapply (htr_rw _ _ _ _ _ _ PR) in HC; rewrite ?HCS; [| hp_acl | hp_rng].
eapply (htr_rw _ _ _ _ _ _ PR) in SP7; [| rewrite hsp_size; hp_acl | rewrite hsp_size; hp_rng].
clear PR.

refine (rz_evt RT AF Σ8 PMh _ _ T cc13 (PMfd_mat_stable F0 fs0) Hc13 _ _).
{ eapply hp_w8r; [reflexivity | exact MI13]. }
intros ms14 cc14 -> Hc14. clear Hc13.
eapply (K8 Σ8 m13 cc14 2 _); [exact Hc14 | exact FRM13 | rewrite EL13; exact ELn7 | rewrite EF13; exact EF7 | rewrite ES13; exact ES7
| rewrite EP13, EP6, EP3, EP2; exact EPO | lia
| exact ART13 | exact MI13 | exact ST13 | exact PFA13 | exact SP7 | exact LSH7 | exact ENH2 | exact J12 | exact CB13 | reflexivity | exact J16
| exact FSZ3 | exact RATE6 | exact LOOK | exact HC | exact DR13 | rewrite depth_ctl; exact DD7 | apply isave_ctl; [intros off E; discriminate E| exact ISV3]
| apply ctl_nested_same; exact NST3 | right; reflexivity | lia | ].
intros c' Hc'. apply Hk. destruct (2147483646 <? hd_extra_headers hd); exact Hc'.
Qed.

Lemma lit_mode : forall mo, In (mode_addr mo, 96) ACC_LITS.
Proof. intros mo. destruct mo; unfold mode_addr, A_speex_nb_mode, A_speex_wb_mode, A_speex_uwb_mode, ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]). Qed.
Lemma lit_mode_list : In (A_speex_mode_list, 24) ACC_LITS.
Proof. unfold A_speex_mode_list, ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]). Qed.
Lemma mode_addr_range : forall mo, 0 <= mode_addr mo /\ mode_addr mo + 96 <= 0x100000.
Proof. intros mo. destruct mo; unfold mode_addr, A_speex_nb_mode, A_speex_wb_mode, A_speex_uwb_mode; lia. Qed.
Lemma sb_mode_ptr_addr : forall mo, sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode mo = mode_addr mo.
Proof. destruct mo; reflexivity. Qed.
Lemma own_len_none : forall (a' : haux) (h' : hstate unit), h_st h' = None -> (length (h_own a' h') <= 5)%nat.
Proof.
intros a' h' STN'. unfold h_own. rewrite STN'. cbn [app length].
destruct (h_stream_init h' =? 0); destruct (sy_data (h_oy h')); cbn [length app]; lia.
Qed.
Lemma st_traces_96fa4 : In [0x97310; 0x96650] SITE_TRACES. Proof. vm_compute. tauto. Qed.
Lemma st_traces_99bbc : In [0x99f28; 0x96650] SITE_TRACES. Proof. vm_compute. tauto. Qed.

Lemma art_munch_below : forall (Σ : rts RT) (m m1 : mem),
ART RT Σ m -> rt_sp0 RT Σ = x_sp0 X -> munch [(S1 + -16, S1)] m m1 -> wmono bsegs m m1 -> ART RT Σ m1.
Proof.
intros Σ m m1 ART0 ES MU WM.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & _).
apply (af_frame RT AF Σ m m1 (S1 + -16) ART0); [rewrite ES; unfold RT_STACK, H_STACK in LR; lia| | exact WM].
intros b Hb. apply MU. cbn [outside]. split; [intros Hin; apply Hb; left; unfold USTACK_TOP in *; lia| exact I].
Qed.

Hypothesis INIT8 : forall mo, init_cps_at8 RT mo.

Lemma hp_ap : forall (Σ2 : rts RT) (cc : config) T (v : Z) (r1 : option (unit * spx_header))
(t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s9 s10 t3 t4 t5 t6 : word) Fr fc (j12 j16 : list byte) (c48 c52 c56 c64 : word) (wl : Z),
ASTA RT Σ2 PMh (eq (MS (mkR (Z64 0x97114) (Z64 S1) (x_gp X) (Z64 0x638c98) t0 t1 t2 (Z64 usp) (Z64 S1) (Z64 v) a1 a2 a3 a4 a5 a6 a7
(Z64 (F + HO_OP)) (Z64 sf) (Z64 (h_packet_count h)) s5 (Z64 (-8)) (Z64 0x7fffffff) (Z64 pno) s9 s10 (Z64 (h_channels h))
t3 t4 t5 t6) Fr (ret_pc (Z64 0x97114)) fc None m2 (seg_rom bsegs))) cc ->
X1cn.frm0 fc -> rt_frames RT Σ2 = [(F, 8%nat)] -> rt_sp0 RT Σ2 = x_sp0 X -> rt_pois RT Σ2 = [] -> rt_credit RT Σ2 = rt_credit RT Σ1 ->
ART RT Σ2 m2 -> mem_inv bsegs m2 -> stk bsegs m2 lo S1 ->
p2h_result m2 v r1 (rt_live RT Σ1) (rt_live RT Σ2) ->
rw_cells bsegs m2 S1 (h_spill X (Z64 (h_bytes_remaining h)) v48 v56 v88 j224 j232 a h) ->
rw_cells bsegs m2 sf [CB 16 HSH_L_HDR] ->
rw_cells bsegs m2 (F + 32) [C4 (Z64 1)] -> rw_cells bsegs m2 (F + 36) [CB 12 j12] -> rw_cells bsegs m2 (F + 48) [C4 c48; C4 c52; C8 c56; C8 c64] ->
rw_cells bsegs m2 (F + 72) [CB 16 j16] ->
rw_cells bsegs m2 (F + HO_FSZ) [C4 (Z64 (h_frame_size h))] -> rw_cells bsegs m2 (F + HO_RATE) [C4 (Z64 (h_rate h))] -> rw_cells bsegs m2 (F + HO_LOOK) [C4 (Z_to_bv 64 wl)] ->
(forall c', match (match r1 with None => None | Some (_, hd) => hdr_tail h hd end) with
| None => at_XT RT OUT_rep ERR_rep IO_FP X F0 fs0 c'
| Some h3 => at_KH RT OUT_rep ERR_rep IO_FP X F0 fs0 (incr_packet_count h3) pno nbr brem0 c'
end -> realizes bsegs c' T) ->
realizes bsegs cc T.
Proof.
intros Σ2 cc T v r1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s9 s10 t3 t4 t5 t6 Fr fc j12 j16 c48 c52 c56 c64 wl
Hc FRM EF ESP EPO ECR ART2 MI ST PR SP LSH ENH J12 CBK J16 FSZ RATE LOOK Hk.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS1 as (EL1 & ND1 & PERM1 & EF1 & ESP1 & EPO1 & ECR1).
pose proof HR0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OSR0 & _ & _ & _ & DEC0 & HP0).
pose proof hp_st_none as STN.
pose proof hp_hsep as HSP.
pose proof (own_pos_h m0 a h OSR0 DEC0 HP0) as OPOS.
assert (RPOS : forall e, In e (rt_live RT Σ1) -> 0 < snd e).
{ intros [p q] He. rewrite EL1 in He. apply in_app_or in He as [He|He]; [exact (OPOS p q (Permutation_in _ PERM1 He))| exact (proj1 (hi_live _ _ _ HX) p q He)]. }
assert (KC0 : h_cost h + 64 <= FUZZ_COST - 1) by (unfold h_cost, H_HDR_CREDIT, H_DEC_CREDIT, FUZZ_COST; rewrite PC0; lia).
destruct (hp_fz m2 (AF_DRV _ _ ART2) (pres_fp_refl _ _ _ _ _)) as (PFR & ERR & OUTR & SSP & _ & BITS & SY & _ & _ & OSR & _).
assert (DEC2 : h_dec_rep X m2 a h) by (unfold h_dec_rep in *; rewrite STN in *; exact DEC0).
destruct r1 as [[[] hd]|].
2: {
destruct PR as (-> & _ & _ & EQL). specialize (EQL RPOS).
refine (rz_evt RT AF Σ2 PMh _ _ T cc (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply hp_w2n; [reflexivity | unfold USTACK_TOP in *; lia | exact SP | exact MI]. }
intros ms1 cc1 -> Hc1. clear Hc.
assert (HS2 : hsig_k RT X Σ2 a h 0).
{ split; [rewrite EQL; exact EL1|]. split; [exact ND1|]. split; [exact PERM1|]. split; [exact EF|]. split; [exact ESP|]. split; [exact EPO| rewrite ECR; lia]. }
exact (hp_tail_ok h a 0 Σ2 m2 cc1 T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
Hc1 FRM HS2 ltac:(lia) STN SI1 HP0 ART2 MI ST PFR ERR OUTR SSP SP LSH BITS OSR SY DEC2 Hk). }

destruct PR as (junk28 & w1 & w2 & w3 & r1' & r2' & V0 & V16 & EL2 & HC & RV & RR & RM & RB & RN & RF & RE).
cbv iota in Hk. cbv [X1rg.SPEEX_NB_MODES X1rh.SPEEX_NB_MODES] in RM.
assert (INV : In (v, 80) (rt_live RT Σ2)) by (rewrite EL2; left; reflexivity).
assert (VSEP : v + 80 <= lo).
{ destruct (af_live_range RT AF Σ2 m2 _ _ ART2 INV) as (_ & VL & _). rewrite ESP in VL. pose proof (hi_lo _ _ _ HX) as (LW0 & _). lia. }
assert (AOV : aobj bsegs m2 v 80).
{ split; [lia|]. split; [unfold APP_TOP; unfold USTACK_TOP in *; lia|]. exact (proj2 (af_acc_live RT AF Σ2 m2 _ _ ART2 INV)). }

refine (rz_evt RT AF Σ2 PMh _ _ T cc (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply (hp_w2 _ _ v junk28 hd); [reflexivity | unfold USTACK_TOP in *; lia | lia | clear - V16; Z.div_mod_to_equations; lia | lia | lia | exact AOV | exact HC | exact SP
| exact (AF_LIB _ _ ART2) | exact MI]. }
intros ms1 cc1 POST1 Hc1. clear Hc.
set (mo := mode_of_id (hd_mode hd)) in *.

assert (K68 : forall (m3 : mem) (cc3 : config) (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
ASTA RT Σ2 PMh (eq (MS (mkR ra' (Z64 S1) (x_gp X) (Z64 0x638c98) t0' t1' t2' (Z64 usp) (Z64 S1) (Z64 (mode_addr mo)) a1' a2' a3' a4' a5' a6' a7'
(Z64 SHB) (Z64 sf) (Z64 (h_packet_count h)) (Z64 v) (Z64 (-8)) (Z64 0x7fffffff) (Z64 pno) (Z64 (F + 8384)) (Z64 (F + HO_BITS))
(Z64 (h_channels h)) t3' t4' t5' t6') Fr (Z64 0x9716c) fc None m3 (seg_rom bsegs))) cc3 ->
ART RT Σ2 m3 -> mem_inv bsegs m3 -> stk bsegs m3 lo S1 -> rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 W_h m2 m3 ->
rw_cells bsegs m3 S1 (h_spill X (Z64 (h_bytes_remaining h)) v48 v56 v88 j224 j232 a h) ->
rw_cells bsegs m3 sf [CB 16 HSH_L_HDR] ->
rw_cells bsegs m3 (F + 32) [C4 (Z64 1)] -> rw_cells bsegs m3 (F + 36) [CB 12 j12] -> rw_cells bsegs m3 (F + 48) [C4 c48; C4 c52; C8 c56; C8 c64] ->
rw_cells bsegs m3 (F + 72) [CB 16 j16] ->
rw_cells bsegs m3 (F + HO_FSZ) [C4 (Z64 (h_frame_size h))] -> rw_cells bsegs m3 (F + HO_RATE) [C4 (Z64 (h_rate h))] -> rw_cells bsegs m3 (F + HO_LOOK) [C4 (Z_to_bv 64 wl)] ->
rw_cells bsegs m3 v (spx_header_cells junk28 hd w1 w2 w3 r1' r2') ->
realizes bsegs cc3 T).
{ intros m3 cc3 ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Hc3 ART3 MI3 ST3 PFA3 SP3 LSH3 ENH3 J123 CBK3 J163 FSZ3 RATE3 LOOK3 HC3.
clear Hc1 POST1 SP LSH ENH J12 CBK J16 FSZ RATE LOOK HC ART2 MI ST.
assert (AOV3 : aobj bsegs m3 v 80).
{ split; [lia|]. split; [unfold APP_TOP; unfold USTACK_TOP in *; lia|]. exact (proj2 (af_acc_live RT AF Σ2 m3 _ _ ART3 INV)). }
assert (AOM : aobj bsegs m3 (mode_addr mo) 32).
{ pose proof (mode_addr_range mo) as (MA0 & MA1).
apply (aobj_sub bsegs m3 (mode_addr mo) 96); [| lia | lia]. apply (aobj_lit RT AF Σ2 m3 _ _ ART3 (lit_mode mo)); [lia| unfold APP_TOP; lia]. }

refine (rz_evt RT AF Σ2 PMh _ _ T cc3 (PMfd_mat_stable F0 fs0) Hc3 _ _).
{ eapply (hp_w3 v mo junk28 hd); [lia | clear - V16; Z.div_mod_to_equations; lia | unfold USTACK_TOP in *; lia | reflexivity | exact RV | exact RB
| exact AOV3 | exact HC3 | exact AOM | exact (AF_LIB _ _ ART3) | exact MI3]. }
intros ms4 cc4 (xa1 & xa2 & xa3 & POST4) Hc4. clear Hc3.
destruct (hp_fz m3 (AF_DRV _ _ ART3) PFA3) as (PF3 & ERR3 & OUTR3 & SSP3 & _ & BITS3 & SY3 & _ & _ & OSR3 & _).
assert (DEC3 : h_dec_rep X m3 a h) by (unfold h_dec_rep in *; rewrite STN in *; exact DEC0).
assert (HSX2 : hsig_x Σ2 a h 0 [(v, 80)]).
{ split; [rewrite EL2, EL1; reflexivity|]. split; [exact ND1|]. split; [exact PERM1|]. split; [exact EF|]. split; [exact ESP|].
split; [exact EPO| rewrite ECR; lia]. }
destruct POST4 as [(VB & ->) | (VG & BG & ->)].
{
assert (HT : hdr_tail h hd = None).
{ unfold hdr_tail. destruct (Z.ltb_spec 1 (hd_speex_version_id hd)); [reflexivity|].
replace (hd_mode_bitstream_version hd =? 4) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
rewrite HT in Hk.
eapply (hp_f54_ok h a 0 v Σ2 m3 cc4 T);
[exact Hc4 | exact FRM | exact HSX2 | lia | exact STN | exact SI1 | exact HP0 | exact ART3 | exact MI3 | exact ST3 | exact PF3 | exact ERR3
| exact OUTR3 | exact SSP3 | exact SP3 | exact LSH3 | exact BITS3 | exact OSR3 | exact SY3 | exact DEC3 | exact Hk]. }

assert (LVB : Z.of_nat (length (rt_live RT Σ2)) + init_nblocks mo <= LIVE_MAX).
{ rewrite EL2, EL1. cbn [length]. rewrite length_app, (Permutation_length PERM1).
pose proof (own_len_none a h STN) as OL. pose proof (hi_live _ _ _ HX) as (_ & LL). unfold H_LIVE, LIVE_MAX in *.
assert (I19 : init_nblocks mo <= 19) by (destruct mo; cbn; lia). lia. }
assert (CRI : init_credit mo <= rt_credit RT Σ2).
{ rewrite ECR. pose proof (hi_cr _ _ _ HX) as FC. unfold h_cost, H_HDR_CREDIT, H_DEC_CREDIT, FUZZ_COST in *. rewrite PC0 in ECR1.
assert (I4 : init_credit mo <= 4) by (destruct mo; cbn; lia). lia. }
assert (UE : uw_entry m3 (Z64 usp) (bv_unsigned (Z64 S1)) lo [0x96650]).
{ cbn [uw_entry]. rewrite !unsigned_lit by (unfold USTACK_TOP in *; lia). exact (h_uw_chain m3 PF3). }
assert (ITR : init_traces mo (bv_unsigned (Z64 0x971d0)) [0x96650]) by (rewrite unsigned_lit by lia; exact (init_traces_harness mo)).
assert (IST : init_stack mo <= 512) by (destruct mo; cbn; lia).
unfold A_decoder_init_h in Hc4. change 0x9896c with A_speex_decoder_init in Hc4.
cps_rt (INIT8 mo Σ2 PMh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 lo [0x96650] (F + HO_OUT) (F + HO_STEREO)).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ rewrite EF. cbn [length]. unfold FRAMES_MAX. destruct mo; cbn; lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). exact ST3. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold RT_STACK. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). exact S32. }
intros cc5 (Σ3 & D & LBD & NEW & Hc5 & EL3 & PNEW & NDB & LNEW & EF3 & ES3 & EC3 & EP3 & AL8). clear Hc4.
cps_unpack_lib Hc5 as (m4 & RS & RA & PR & DR).
destruct RA as (ART4 & MI4 & WM4 & ST4).
rewrite EF in PR.
assert (PRh : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 W_h m3 m4).
{ apply (pres_fp_weaken _ _ _ [] _ m3 m4); [| intros x _; exact I].
apply (pres_fp_mono _ _ _ (rt_live RT Σ2) [(F, 8%nat)] S1 [] m3 m4 PR); [intros e He; rewrite EL2; right; exact He| intros e He; exact He| lia]. }
pose proof (pres_fp_trans _ _ _ _ m2 m3 m4 PFA3 PRh) as PFA4. clear PFA3 PRh.
unfold HO_FSZ, HO_RATE, HO_LOOK in FSZ3, RATE3, LOOK3.
hp_tr PR LSH3. hp_tr PR ENH3. hp_tr PR J123. hp_tr PR CBK3. hp_tr PR J163. hp_tr PR FSZ3. hp_tr PR RATE3. hp_tr PR LOOK3.
assert (HCS : cells_size (spx_header_cells junk28 hd w1 w2 w3 r1' r2') = 80%nat) by reflexivity.
eapply (htr_rw _ _ _ _ _ _ PR) in HC3; rewrite ?HCS; [| hp_acl | hp_rng].
eapply (htr_rw _ _ _ _ _ _ PR) in SP3; [| unfold h_spill; rewrite hsp_size; hp_acl | unfold h_spill; rewrite hsp_size; hp_rng].
clear PR.
eapply (hp_ai Σ3 m4 cc5 T hd v D junk28 w1 w2 w3 r1' r2' LBD NEW j12 j16 c48 c52 c56 c64 wl);
[exact Hc | exact RS | rewrite EL3, EL2; reflexivity | rewrite EF3; exact EF | rewrite ES3; exact ESP | rewrite EP3; exact EPO
| assert (I4 : init_credit mo <= 4) by (destruct mo; cbn; lia); lia
| exact PNEW | exact NDB | exact AL8 | exact LNEW | exact DR | exact V0 | exact V16 | exact HC3 | exact RR | exact RN | exact RF | exact RE
| exact VG | exact BG | exact RM | exact ART4 | exact MI4 | first [exact ST4 | rewrite unsigned_lit in ST4 by (unfold USTACK_TOP in *; lia); exact ST4]
| exact PFA4 | exact SP3 | exact LSH3 | exact ENH3 | exact J123 | exact CBK3 | exact J163 | exact FSZ3 | exact RATE3 | exact LOOK3 | exact Hk]. }
destruct POST1 as [(M0 & ->) | (MN & ->)].
{
assert (EMO : mode_addr mo = A_speex_nb_mode) by (unfold mo, mode_of_id; rewrite M0; reflexivity).
rewrite <- EMO in Hc1.
exact (K68 m2 cc1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc1 ART2 MI ST (pres_fp_refl _ _ _ _ _) SP LSH ENH J12 CBK J16 FSZ RATE LOOK HC). }

unfold A_lib_get_mode_h in Hc1. change 0xb5708 with A_speex_lib_get_mode in Hc1.
refine (rz_evt RT AF Σ2 PMh _ _ T cc1 (PMfd_mat_stable F0 fs0) Hc1 _ _).
{ eapply (speex_lib_get_mode_walk (hd_mode hd) S1 lo);
[lia | apply (aobj_lit RT AF Σ2 m2 _ _ ART2 lit_mode_list); unfold A_speex_mode_list, APP_TOP; lia
| exact ST | lia | lia | unfold USTACK_TOP in *; lia | exact (af_client_consts RT AF Σ2 m2 ART2) | exact (AF_LIB _ _ ART2) | exact MI]. }
intros ms2 cc2 (g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & g8 & g9 & g10 & g11 & g12 & g13 & m3 & -> & MU3 & WM3 & MI3 & ST3) Hc2. clear Hc1.
pose proof (art_munch_below Σ2 m2 m3 ART2 ESP MU3 WM3) as ART3.
assert (PR3 : rt_pres_fp (rt_live RT Σ2) [(F, 8%nat)] S1 [] m2 m3).
{ apply (pres_fp_of_munch _ _ _ _ _ m2 m3 MU3). intros x Hx _. cbn [outside]. split; [| exact I].
intros Hin. destruct Hx as [H|[H|[H|[H|H]]]]; [lia| pose proof (client_static_range _ H); unfold SEGTOP_A in *; unfold RT_STACK, H_STACK in LR; lia| | |].
- destruct H as (p & q & Hpq & Hx). destruct (af_live_range RT AF Σ2 m2 p q ART2 Hpq) as (_ & PL & _). rewrite ESP in PL.
pose proof (hi_lo _ _ _ HX) as (LW0 & _). lia.
- destruct H as (f & k & [E|[]] & Hx). injection E as <- <-. change (fs_size 8) with 16384 in Hx. lia.
- destruct H as (f & k & [E|[]] & Hx). injection E as <- <-. change (fs_size 8) with 16384 in Hx. unfold SH_LO, SH_HI in *. lia. }
assert (PRh : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 W_h m2 m3).
{ apply (pres_fp_weaken _ _ _ [] _ m2 m3); [| intros x _; exact I].
apply (pres_fp_mono _ _ _ (rt_live RT Σ2) [(F, 8%nat)] S1 [] m2 m3 PR3); [intros e He; rewrite EL2; right; exact He| intros e He; exact He| lia]. }
unfold HO_FSZ, HO_RATE, HO_LOOK in FSZ, RATE, LOOK.
hp_tr PR3 LSH. hp_tr PR3 ENH. hp_tr PR3 J12. hp_tr PR3 CBK. hp_tr PR3 J16. hp_tr PR3 FSZ. hp_tr PR3 RATE. hp_tr PR3 LOOK.
assert (HCS : cells_size (spx_header_cells junk28 hd w1 w2 w3 r1' r2') = 80%nat) by reflexivity.
eapply (htr_rw _ _ _ _ _ _ PR3) in HC; rewrite ?HCS; [| hp_acl | hp_rng].
eapply (htr_rw _ _ _ _ _ _ PR3) in SP; [| unfold h_spill; rewrite hsp_size; hp_acl | unfold h_spill; rewrite hsp_size; hp_rng].

refine (rz_evt RT AF Σ2 PMh _ _ T cc2 (PMfd_mat_stable F0 fs0) Hc2 _ _).
{ eapply hp_w2g; [reflexivity | exact MI3]. }
intros ms4 cc4 -> Hc4. clear Hc2.
exact (K68 m3 cc4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc4 ART3 MI3 ST3 PRh SP LSH ENH J12 CBK J16 FSZ RATE LOOK HC).
Qed.

End HP.

Lemma h_CB8_C8 : forall (m : mem) A j, rw_cells bsegs m A [CB 8 j] -> exists w : word, rw_cells bsegs m A [C8 w].
Proof.
intros m A j H. assert (L : length j = (8 * 1)%nat) by (destruct H as [[[Hwf _] _] _]; exact Hwf).
destruct (CB_C8s_h 1 j L) as (ws & Lws & E). destruct ws as [|w [|? ?]]; try discriminate Lws. exists w.
eapply rw_cells_recast; [exact H| cbn; tauto|]. cbn [map cells_bytes cbytes] in *. rewrite ?app_nil_r in *. exact E.
Qed.

Ltac hp_acl := first
[ apply acl_stack; unfold USTACK_TOP in *; lia
| apply (acl_frame _ [(x_F X, 8%nat)] _ (x_F X) 8 _ _ (or_introl eq_refl)); change (fs_size 8) with 16384; lia
| apply (acl_fshadow _ [(x_F X, 8%nat)] _ (x_F X) 8 _ _ (or_introl eq_refl)); change (fs_size 8) with 16384; lia
| match goal with H : In (?p, ?q) ?L |- acl_rng ?L _ _ _ _ => apply (acl_live _ _ _ p q _ _ H); lia end ].
Ltac hp_rng := repeat (first [ apply rng_out_nil | apply rng_out_cons; [unfold SH_LO, SH_HI in *; lia|] ]).
Ltac hp_tr PR H := eapply (htr_rw _ _ _ _ _ _ PR) in H; cbn [cells_size csize Nat.add] in H |- *; [| hp_acl | hp_rng].

Hypothesis FD2 : fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Hypothesis P2H2 : speex_packet_to_header_cps RT OUT_rep ERR_rep IO_FP.
Hypothesis CTL : forall d, ctl_cps_at RT d.
Hypothesis INIT8 : forall mo, init_cps_at8 RT mo.

Theorem h_hdr_ok : h_hdr_cps RT OUT_rep ERR_rep IO_FP X F0 fs0.
Proof.
intros _ h op pno nbr brem0 q q' r bs PRUN EB T c Hc Hk.
destruct Hc as (Σ1 & a & Fx & fc & m0 & ra & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r10 & t3 & t4 & t5 & t6 & v48 & v56 & v88 & j224 & j232 & gw
& ogc & kc & Hc & FRM & HS1 & HIT & SI1 & EOS0 & PC0 & (PN0 & PN1) & SKW & HR0 & OGJ & KCS & PK0 & PK1 & PK2 & BUD).
destruct (hdr_prun h _ _ q r q' PRUN) as (r1 & P1 & RM). clear PRUN.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS1 as (EL1 & ND1 & PERM1 & EF1 & ESP1 & EPO1 & ECR1).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m0 a h (proj1 HR0) HS1) as HSP.
pose proof HR0 as (ART0 & MI0 & ST0 & PF0 & ERR0 & OUTR0 & SSP0 & SP0 & LSH0 & (je & ENH0) & _ & FSZ0 & _ & _ & _ & OPC0 & OSR0 & _ & RATE0 & (wl & LOOK0 & _)
& DEC0 & HP0).
assert (INF : In (F, 8%nat) (rt_frames RT Σ1)) by (rewrite EF1; left; reflexivity).

unfold HO_ENH in ENH0.
cb_cut ENH0 4%nat ENHa. cb_cut ENH0 12%nat J12. cb_cut ENH0 4%nat C48. cb_cut ENH0 4%nat C52. cb_cut ENH0 8%nat C56. cb_cut ENH0 8%nat C64.
destruct (h_CB4_C4 bsegs m0 (F + 32) [] _ [] ENHa) as (we & ENH1). cbn [app] in ENH1. clear ENHa.
destruct (h_CB4_C4 bsegs m0 (F + 48) [] _ [] C48) as (c48 & C48'). cbn [app] in C48'. clear C48.
destruct (h_CB4_C4 bsegs m0 (F + 52) [] _ [] C52) as (c52 & C52'). cbn [app] in C52'. clear C52.
destruct (h_CB8_C8 m0 (F + 56) _ C56) as (c56 & C56'). clear C56.
destruct (h_CB8_C8 m0 (F + 64) _ C64) as (c64 & C64'). clear C64.
assert (CBK : rw_cells bsegs m0 (F + 48) [C4 c48; C4 c52; C8 c56; C8 c64]).
{ change [C4 c48; C4 c52; C8 c56; C8 c64] with ([C4 c48] ++ [C4 c52] ++ [C8 c56] ++ [C8 c64]).
apply rw_cells_app; split; [exact C48'|]. cbn [cells_size csize Nat.add]. replace (F + 48 + Z.of_nat 4) with (F + 52) by lia.
apply rw_cells_app; split; [exact C52'|]. cbn [cells_size csize Nat.add]. replace (F + 52 + Z.of_nat 4) with (F + 56) by lia.
apply rw_cells_app; split; [exact C56'|]. cbn [cells_size csize Nat.add]. replace (F + 56 + Z.of_nat 8) with (F + 64) by lia. exact C64'. }
clear C48' C52' C56' C64'. rename ENH0 into J16.
assert (OWH : forall x, outside W_h x -> outside [(sf, sf + 16); (F + 32, F + 36)] x).
{ intros x Hx. unfold W_h in Hx. cbn [outside] in Hx |- *. destruct Hx as (_ & O2 & O3 & _). split; [exact O2| split; [lia| exact I]]. }

refine (rz_evt RT AF Σ1 PMh _ _ _ c (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply hp_w1a; [unfold SH_LO, SH_HI in *; lia | exact LSH0 | exact MI0]. }
intros ms1 c1 (m1 & -> & MU1 & WM1 & MI1 & LSH1) Hc1. clear Hc.
pose proof (art_munch_h Σ1 m0 m1 _ ART0 EF1 ESP1 MU1 WM1 ltac:(intros l hh [E|[]]; injection E as <- <-; right; left; lia)) as ART1.
assert (PR1 : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 [(sf, sf + 16)] m0 m1) by (apply (pf_munch_h _ m0 m1 _ _ MU1); intros x Hx; exact Hx).
assert (PW1 : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 [(sf, sf + 16); (F + 32, F + 36)] m0 m1)
by (apply (pf_munch_h _ m0 m1 _ _ MU1); intros x Hx; cbn [outside] in Hx |- *; destruct Hx as (O1 & _ & _); split; [exact O1| exact I]).
assert (ST1 : stk bsegs m1 lo S1).
{ apply (stk_agree bsegs m0 m1 lo S1 ST0); [| exact WM1]. apply (agree_of_munch _ m0 m1 _ MU1). intros x Hx. cbn [outside].
split; [unfold SH_LO, SH_HI in *; lia| exact I]. }
hp_tr PR1 ENH1. eapply (htr_rw _ _ _ _ _ _ PR1) in SP0; [| unfold h_spill; rewrite hsp_size; hp_acl | unfold h_spill; rewrite hsp_size; hp_rng].
clear PR1 MU1 WM1 MI0 ST0.

refine (rz_evt RT AF Σ1 PMh _ _ _ c1 (PMfd_mat_stable F0 fs0) Hc1 _ _).
{ eapply (hp_w1b (x_S1 X) (x_F X)); [unfold USTACK_TOP in *; lia | unfold USTACK_TOP in *; lia | lia | exact SP0 | exact ENH1 | exact MI1]. }
intros ms2 c2 (m2' & -> & MU2 & WM2 & MI2 & ENH2 & SP2) Hc2. clear Hc1.
pose proof (art_munch_h Σ1 m1 m2' _ ART1 EF1 ESP1 MU2 WM2 ltac:(intros l hh [E|[]]; injection E as <- <-; right; right; lia)) as ART2.
assert (PR2 : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 [(F + 32, F + 36)] m1 m2') by (apply (pf_munch_h _ m1 m2' _ _ MU2); intros x Hx; exact Hx).
assert (PW2 : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 [(sf, sf + 16); (F + 32, F + 36)] m0 m2').
{ apply (pres_fp_trans _ _ _ _ m0 m1 m2' PW1). apply (pf_munch_h _ m1 m2' _ _ MU2). intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (_ & O2 & _). split; [exact O2| exact I]. }
assert (ST2 : stk bsegs m2' lo S1).
{ apply (stk_agree bsegs m1 m2' lo S1 ST1); [| exact WM2]. apply (agree_of_munch _ m1 m2' _ MU2). intros x Hx. cbn [outside]. split; [lia| exact I]. }
hp_tr PR2 LSH1.
clear PR2 MU2 WM2 MI1 ST1 PW1 SP0 ENH1.

refine (rz_evt RT AF Σ1 PMh _ _ _ c2 (PMfd_mat_stable F0 fs0) Hc2 _ _).
{ eapply hp_w1c; [unfold SH_LO, SH_HI in *; lia | exact LSH1 | exact MI2]. }
intros ms3 c3 (m3 & -> & MU3 & WM3 & MI3 & LSH3) Hc3. clear Hc2.
pose proof (art_munch_h Σ1 m2' m3 _ ART2 EF1 ESP1 MU3 WM3 ltac:(intros l hh [E|[]]; injection E as <- <-; right; left; lia)) as ART3.
assert (PR3 : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 [(sf, sf + 16)] m2' m3) by (apply (pf_munch_h _ m2' m3 _ _ MU3); intros x Hx; exact Hx).
assert (PW3 : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 [(sf, sf + 16); (F + 32, F + 36)] m0 m3).
{ apply (pres_fp_trans _ _ _ _ m0 m2' m3 PW2). apply (pf_munch_h _ m2' m3 _ _ MU3). intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (O1 & _ & _). split; [exact O1| exact I]. }
assert (ST3 : stk bsegs m3 lo S1).
{ apply (stk_agree bsegs m2' m3 lo S1 ST2); [| exact WM3]. apply (agree_of_munch _ m2' m3 _ MU3). intros x Hx. cbn [outside].
split; [unfold SH_LO, SH_HI in *; lia| exact I]. }
hp_tr PR3 ENH2. eapply (htr_rw _ _ _ _ _ _ PR3) in SP2; [| unfold h_spill; rewrite hsp_size; hp_acl | unfold h_spill; rewrite hsp_size; hp_rng].
clear PR3 MU3 WM3 MI2 ST2 PW2 LSH1.

unfold HO_OP, HO_FSZ, HO_RATE, HO_LOOK in OPC0, FSZ0, RATE0, LOOK0.
assert (OPS : cells_size (op_cells (a_Bd a) (Some op) gw kc) = 48%nat) by reflexivity.
eapply (htr_rw _ _ _ _ _ _ PW3) in OPC0; rewrite ?OPS; [| hp_acl | hp_rng].
hp_tr PW3 J12. hp_tr PW3 CBK. hp_tr PW3 J16. hp_tr PW3 FSZ0. hp_tr PW3 RATE0. hp_tr PW3 LOOK0.
assert (LEN : pk_bytes op <= 4096).
{ pose proof (hi_pay _ _ _ HX) as (_ & SZ & _). unfold MAX_FUZZ_SIZE in SZ.
pose proof HP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BR & _ & Q1 & Q2 & _ & BF & _).
unfold h_consumed, h_pend in *. lia. }

refine (rz_evt RT AF Σ1 PMh _ _ _ c3 (PMfd_mat_stable F0 fs0) Hc3 _ _).
{ eapply (hp_w1d (x_S1 X) (x_F X) (a_Bd a) (pk_bytes op) op gw kc); [unfold USTACK_TOP in *; lia | reflexivity | lia | exact OPC0 | exact MI3]. }
intros ms4 c4 -> Hc4. clear Hc3.

pose proof OSR0 as OSR0'. unfold h_os_rep in OSR0'. destruct (Z.eqb_spec (h_stream_init h) 0) as [E0'|_]; [rewrite SI1 in E0'; discriminate E0'|].
destruct OSR0' as (OS & LH & (UB & LB & BP & UL & WP & LL & UG & LG) & FOK & SINV & BINV & LOK & GL & BD & LV & GV & LS & BS & NBL & NBG & NLG).
destruct (pk_window m0 (a_Bd a) (a_body a) (h_os h) op UB BP (proj1 BINV) ltac:(lia) PK1 PK2) as (U8 & EPD & LPB).
set (pb := firstn (Z.to_nat (pk_bytes op)) (skipn (Z.to_nat (pk_off op)) (a_body a))) in *.
rewrite <- EPD in P1.
assert (SIN : h_stream_init h <> 0) by (rewrite SI1; discriminate).
pose proof (own_in_os a h SIN) as (IBD & _ & _).
assert (INBD : In (a_Bd a, os_body_storage (h_os h)) (rt_live RT Σ1)).
{ rewrite EL1. apply in_or_app. left. exact (Permutation_in _ (Permutation_sym PERM1) IBD). }
assert (BFS : pk_off op + pk_bytes op <= os_body_storage (h_os h)).
{ destruct BP as (_ & BPL). pose proof (proj1 BINV) as ZL. unfold zlength in ZL. unfold bptr in *. lia. }
destruct (proj1 HSP _ _ IBD) as (BD0 & BDL & BDF & BDS & _).
unfold u8ro in U8. eapply (htr_bytes _ _ _ _ _ _ PW3) in U8; [| apply (acl_live _ _ _ _ _ _ _ INBD); rewrite ?LPB; unfold bptr in *; lia
| rewrite ?LPB; hp_rng].
assert (FPHW : fp_h X a h [(sf, sf + 16); (F + 32, F + 36)]) by (apply fp_h_cons; [right; left; lia| apply fp_h_cons; [right; right; left; lia| apply fp_h_nil]]).
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ1 m0 m3 a h _ _ HSP PW3
ltac:(intros e He; rewrite EL1; apply in_or_app; right; exact He) FPHW (AF_DRV _ _ ART3) PF0 ERR0 OUTR0 SSP0) as (PF3 & ERR3 & OUTR3 & SSP3).
assert (STN : h_st h = None).
{ pose proof HP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MM & _). destruct (h_st h); [exfalso; exact (MM PC0)| reflexivity]. }
assert (LVR : Z.of_nat (length (rt_live RT Σ1)) < LIVE_MAX).
{ rewrite EL1, length_app, (Permutation_length PERM1). assert (OL : (length (h_own a h) <= 5)%nat) by (unfold h_own; rewrite STN; cbn [app length]; destruct (h_stream_init h =? 0); destruct (sy_data (h_oy h)); cbn [length app]; lia).
pose proof (hi_live _ _ _ HX) as (_ & LL0). unfold H_LIVE, LIVE_MAX in *. lia. }

edestruct (P2H2 Σ1 F0 fs0 (Z64 0x97114) (Z64 S1) (x_gp X) (Z64 0x638c98) t0 t1 t2 (Z64 usp) (Z64 S1) (Z64 (a_Bd a + pk_off op)) (Z64 (pk_bytes op))
a2 a3 a4 a5 a6 a7 (Z64 (F + 8608)) (Z64 sf) (Z64 (h_packet_count h)) (Z64 (h_speex_serialno h)) (Z64 (-8)) (Z64 0x7fffffff) (Z64 pno)
(Z64 (pk_bytes op)) r10 (Z64 (h_channels h)) t3 t4 t5 t6 Fx fc m3 (a_Bd a + pk_off op) (a_Bd a) (os_body_storage (h_os h)) lo
pb (pk_bytes op) q q' r1 P1) as (bs0 & EB0 & CP).
{ reflexivity. } { reflexivity. } { reflexivity. }
{ exact U8. } { rewrite LPB. lia. } { lia. } { unfold bptr in *. lia. }
{ rewrite PK0, Z.add_0_r. destruct NLG as (_ & B16 & _). clear - B16. Z.div_mod_to_equations. lia. }
{ exact INBD. } { lia. } { rewrite LPB. unfold bptr in *. lia. }
{ exact FD2. } { exact ERR3. } { exact SSP3. } { exact LVR. }
{ exact (af_credit_nonneg RT AF Σ1 m3 ART3). }
{ rewrite EPO1. apply pois_above_nil. }
{ exists [0x96650]. split; [clear; vm_compute; tauto|]. rewrite !unsigned_lit by (unfold USTACK_TOP in *; lia). exact (h_uw_chain m3 PF3). }
{ exact ART3. } { exact MI3. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). exact ST3. }
{ rewrite ESP1. exact LW. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold RT_STACK. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). clear - S32. Z.div_mod_to_equations. lia. }
assert (EBS : bs = bs0) by (rewrite EB in EB0; exact (app_inv_head _ _ _ EB0)). subst bs0.
unfold A_p2h_h in Hc4. change 0x99e60 with A_speex_packet_to_header in Hc4.
apply (CP T c4 Hc4). clear CP.
intros c5 (Σ2 & v & Hc5 & LEN2 & EF2 & ES2 & EC2 & EP2). clear Hc4.
cps_unpack_lib Hc5 as (m2 & RS & RA2 & PR2 & ERR2 & OUT12 & P2R).
destruct RA2 as (ART4 & MI4 & ST4).
pose proof (RS FRM) as FRM2. clear RS.
rewrite EF1 in PR2.
assert (PF02 : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 (W_h ++ IO_FP) m0 m2).
{ apply (pres_fp_trans _ _ _ _ m0 m3 m2).
- apply (pres_fp_weaken _ _ _ _ _ m0 m3 PW3). intros x Hx. apply outside_app_iff in Hx. exact (OWH x (proj1 Hx)).
- apply (pres_fp_weaken _ _ _ _ _ m3 m2 PR2). intros x Hx. apply outside_app_iff in Hx. exact (proj2 Hx). }
destruct (h_io_step_io OUT_rep IO_FP IO_img IO_drv X HX m0 m2 a h (rt_live RT Σ1) W_h HSP PF02
ltac:(intros e He; rewrite EL1; apply in_or_app; right; exact He) (fp_h_Wh a h) (AF_DRV _ _ ART4) PF0 SSP0) as (PFR2 & SSP2).
assert (OUT2 : forall so, OUT_rep so mR -> OUT_rep so m2) by (intros so Hso; exact (OUT12 so (OUTR3 so Hso))).

Ltac hp_rng_io := first [ apply (rng_out_img IO_FP _ _ IO_img); right; unfold SEGTOP_A, SH_LO, SH_HI in *; lia ].
eapply (htr_rw _ _ _ _ _ _ PR2) in SP2; [| unfold h_spill; rewrite hsp_size; hp_acl | unfold h_spill; rewrite hsp_size; hp_rng_io].
Ltac hp_tr_io PR H := eapply (htr_rw _ _ _ _ _ _ PR) in H; cbn [cells_size csize Nat.add] in H |- *; [| hp_acl | hp_rng_io].
hp_tr_io PR2 LSH3. hp_tr_io PR2 ENH2. hp_tr_io PR2 J12. hp_tr_io PR2 CBK. hp_tr_io PR2 J16. hp_tr_io PR2 FSZ0. hp_tr_io PR2 RATE0. hp_tr_io PR2 LOOK0.
clear PR2.

assert (Hk' : forall c', match (match r1 with None => None | Some (_, hd) => hdr_tail h hd end) with
| None => at_XT RT OUT_rep ERR_rep IO_FP X F0 fs0 c'
| Some h3 => at_KH RT OUT_rep ERR_rep IO_FP X F0 fs0 (incr_packet_count h3) pno nbr brem0 c'
end -> realizes bsegs c' T).
{ intros c' Hc'. apply Hk. destruct r1 as [[[] hd]|].
- destruct P2R as (junk28 & w1 & w2 & w3 & r1' & r2' & _ & _ & _ & _ & _ & _ & RM' & _). cbv [X1rg.SPEEX_NB_MODES X1rh.SPEEX_NB_MODES] in RM'.
rewrite (RM RM'). exact Hc'.
- rewrite RM. exact Hc'. }
clear Hk RM.
eapply (hp_ap h op pno nbr brem0 a Σ1 m0 v48 v56 v88 j224 j232 gw ogc kc HS1 HIT SI1 EOS0 PC0 PN0 SKW HR0 OGJ KCS (conj (Z.eq_le_incl _ _ (eq_sym PK0)) (conj PK1 PK2)) BUD m2 PF02 PFR2 ERR2 OUT2 SSP2
PN1 CTL INIT8 Σ2 c5 T v r1);
[exact Hc | exact FRM2 | rewrite EF2; exact EF1 | rewrite ES2; exact ESP1 | rewrite EP2; exact EPO1 | exact EC2 | exact ART4 | exact MI4
| first [exact ST4 | rewrite unsigned_lit in ST4 by (unfold USTACK_TOP in *; lia); exact ST4]
| exact P2R | exact SP2 | exact LSH3 | exact ENH2 | exact J12 | exact CBK | exact J16 | exact FSZ0 | exact RATE0 | exact LOOK0 | exact Hk'].
Qed.

End Hdr.

Lemma init_cps_at8_of : forall RT : rt_sig, (forall mo, init_cps_at RT mo) -> forall mo, init_cps_at8 RT mo.
Proof. intros RT H mo. exact (H mo). Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).
Local Notation Z64 := (Z_to_bv 64).

Definition hdr_tail (h : hstate unit) (hd : spx_header) : option (hstate unit) :=
if 1 <? hd_speex_version_id hd then None else
if negb (hd_mode_bitstream_version hd =? 4) then None else
let d1 := snd (speex_decoder_ctl (init_dec (mode_of_id (hd_mode hd))) (CtlSetEnh 1)) in
let fs := fst (speex_decoder_ctl d1 CtlGetFrameSize) in
let d2 := snd (speex_decoder_ctl d1 CtlGetFrameSize) in
if (fs <? 0) || (640 <? fs) then None else
let rate := if h_rate h =? 0 then hd_rate hd else h_rate h in
let d3 := snd (speex_decoder_ctl d2 (CtlSetSamplingRate rate)) in
if (hd_frames_per_packet hd <? 1) || (10 <? hd_frames_per_packet hd) then None else
let ch0 := if h_channels h =? -1 then hd_nb_channels hd else h_channels h in
let d4 := if ch0 =? 1 then d3 else snd (speex_decoder_ctl d3 CtlSetHandlerStereo) in
if 2147483646 <? hd_extra_headers hd then None else
let d5 := snd (speex_decoder_ctl d4 CtlGetLookahead) in
Some (set_header h d5 (hd_frames_per_packet hd) (if ch0 =? 1 then 1 else 2) rate (hd_extra_headers hd) fs).

Lemma lib_get_mode_id : forall i, 0 <= i < 3 -> speex_lib_get_mode i = Some (mode_of_id i).
Proof.
intros i Hi. unfold speex_lib_get_mode, mode_of_id, SPEEX_NB_MODES.
replace ((i <? 0) || (3 <=? i)) with false by (symmetry; apply orb_false_intro; [apply Z.ltb_ge| apply Z.leb_gt]; lia).
destruct (i =? 0); [reflexivity|]. destruct (i =? 1); reflexivity.
Qed.

Lemma hdr_prun : forall (h : hstate unit) pdata bytes q r q',
prun (hP_process_header h pdata bytes) q = Some (r, q') ->
exists r1, prun (speex_packet_to_header (St := pst) p_calloc p_free p_notify pdata bytes) q = Some (r1, q') /\
match r1 with
| None => r = None
| Some (_, hd) => 0 <= hd_mode hd < 3 -> r = hdr_tail h hd
end.
Proof.
intros h pdata bytes q r q' H. unfold hP_process_header, process_header in H.
rewrite prun_bind in H.
destruct (prun (speex_packet_to_header (St := pst) p_calloc p_free p_notify pdata bytes) q) as [[r1 q1]|] eqn:E1; [| discriminate H].
cbv beta iota in H. exists r1.
destruct r1 as [[[] hd]|].
2: { rewrite prun_ret in H. injection H as <- <-. split; reflexivity. }
assert (KEY : 0 <= hd_mode hd < 3 -> r = hdr_tail h hd /\ q' = q1).
{ intros HM. unfold SPEEX_NB_MODES in H.
replace ((3 <=? hd_mode hd) || (hd_mode hd <? 0)) with false in H by (symmetry; apply orb_false_intro; [apply Z.leb_gt| apply Z.ltb_ge]; lia).
rewrite (lib_get_mode_id _ HM) in H. unfold hdr_tail, mode_bitstream_version in *. unfold bptr in *.
destruct (1 <? hd_speex_version_id hd).
{ rewrite prun_bind, prun_free in H. cbv beta iota in H. rewrite prun_ret in H. injection H as <- <-. split; reflexivity. }
destruct (Z.eqb_spec (hd_mode_bitstream_version hd) 4) as [EV|NV].
2: { destruct (Z.ltb_spec 4 (hd_mode_bitstream_version hd)) as [L1|L1].
- rewrite prun_bind, prun_free in H. cbv beta iota in H. rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
- replace (hd_mode_bitstream_version hd <? 4) with true in H by (symmetry; apply Z.ltb_lt; lia).
rewrite prun_bind, prun_free in H. cbv beta iota in H. rewrite prun_ret in H. injection H as <- <-. split; reflexivity. }
rewrite EV, !Z.ltb_irrefl in H. cbv iota in H. cbn [negb].
unfold h_decoder_init, h_decoder_destroy in H. rewrite prun_bind in H.
destruct (prun (speex_decoder_init (St := pst) p_calloc p_free (mode_of_id (hd_mode hd))) q1) as [[ost q2]|] eqn:E2; [| discriminate H].
destruct (init_prun _ _ _ _ E2) as [-> ->]. cbv beta iota in H.
destruct (@speex_decoder_ctl unit (init_dec (mode_of_id (hd_mode hd))) (CtlSetEnh 1)) as [x1 d1] eqn:C1. cbn [fst snd]. cbv beta iota in H.
destruct (speex_decoder_ctl d1 CtlGetFrameSize) as [fs d2] eqn:C2. cbn [fst snd]. cbv beta iota in H.
destruct ((fs <? 0) || (640 <? fs)) eqn:FSB.
{ change (2 * 320) with 640 in H. rewrite FSB in H.
rewrite prun_bind, prun_destroy in H. cbv beta iota in H. rewrite prun_bind, prun_free in H. cbv beta iota in H. rewrite prun_ret in H.
injection H as <- <-. split; reflexivity. }
change (2 * 320) with 640 in H. rewrite FSB in H.
destruct (speex_decoder_ctl d2 (CtlSetSamplingRate (if h_rate h =? 0 then hd_rate hd else h_rate h))) as [x3 d3] eqn:C3. cbn [fst snd]. cbv beta iota in H.
destruct ((hd_frames_per_packet hd <? 1) || (10 <? hd_frames_per_packet hd)).
{ rewrite prun_bind, prun_destroy in H. cbv beta iota in H. rewrite prun_bind, prun_free in H. cbv beta iota in H. rewrite prun_ret in H.
injection H as <- <-. split; reflexivity. }
destruct ((if h_channels h =? -1 then hd_nb_channels hd else h_channels h) =? 1) eqn:CH; cbn [negb] in H.
- unfold INT_MAX in H. change (2147483647 - 1) with 2147483646 in H.
destruct (2147483646 <? hd_extra_headers hd).
{ rewrite prun_bind, prun_destroy in H. cbv beta iota in H. rewrite prun_bind, prun_free in H. cbv beta iota in H. rewrite prun_ret in H.
injection H as <- <-. split; reflexivity. }
rewrite prun_bind, prun_free in H. cbv beta iota in H.
destruct (speex_decoder_ctl d3 CtlGetLookahead) as [x5 d5] eqn:C5. cbn [fst snd]. cbv beta iota in H. rewrite prun_ret in H. injection H as <- <-.
apply Z.eqb_eq in CH. rewrite CH. split; reflexivity.
- destruct (speex_decoder_ctl d3 CtlSetHandlerStereo) as [x4 d4] eqn:C4. cbn [fst snd]. cbv beta iota in H.
unfold INT_MAX in H. change (2147483647 - 1) with 2147483646 in H.
destruct (2147483646 <? hd_extra_headers hd).
{ rewrite prun_bind, prun_destroy in H. cbv beta iota in H. rewrite prun_bind, prun_free in H. cbv beta iota in H. rewrite prun_ret in H.
injection H as <- <-. split; reflexivity. }
rewrite prun_bind, prun_free in H. cbv beta iota in H.
destruct (speex_decoder_ctl d4 CtlGetLookahead) as [x5 d5] eqn:C5. cbn [fst snd]. cbv beta iota in H. rewrite prun_ret in H. injection H as <- <-.
split; reflexivity. }
assert (Q1 : q' = q1).
{ destruct (andb (0 <=? hd_mode hd) (hd_mode hd <? 3)) eqn:MR.
- apply andb_true_iff in MR as [M1 M2]. apply Z.leb_le in M1. apply Z.ltb_lt in M2. exact (proj2 (KEY (conj M1 M2))).
- unfold SPEEX_NB_MODES in H. replace ((3 <=? hd_mode hd) || (hd_mode hd <? 0)) with true in H.
+ rewrite prun_bind, prun_free in H. cbv beta iota in H. rewrite prun_ret in H. injection H as _ <-. reflexivity.
+ symmetry. apply andb_false_iff in MR as [M|M].
* apply Z.leb_gt in M. apply orb_true_intro. right. apply Z.ltb_lt. lia.
* apply Z.ltb_ge in M. apply orb_true_intro. left. apply Z.leb_le. lia. }
subst q'. split; [reflexivity|]. intros HM. exact (proj1 (KEY HM)).
Qed.

Lemma isave_init : forall mo, isave_ok (init_dec mo).
Proof. destruct mo; cbn; exact I. Qed.
Lemma isave_ctl : forall (d : dec_state bptr) r, (forall off, r <> CtlSetInnovationSave off) -> isave_ok d -> isave_ok (snd (speex_decoder_ctl d r)).
Proof.
intros d r NR H. destruct d as [st|s low]; destruct r; cbn in *; try exact H;
try (match goal with |- context [speex_decoder_ctl low ?rr] => destruct (speex_decoder_ctl low rr) as [v' low'] end; cbn; exact H);
try (exfalso; eapply NR; reflexivity).
Qed.
Lemma nested_init : forall mo, dec_nestedR (init_dec mo).
Proof. destruct mo; cbn; repeat split. Qed.
Lemma depth_init : forall mo, (dec_depth (init_dec mo) <= 3)%nat.
Proof. destruct mo; cbn; lia. Qed.
Lemma depth_ctl : forall (d : dec_state bptr) r, dec_depth (snd (speex_decoder_ctl d r)) = dec_depth d.
Proof. intros d r. apply speex_decoder_ctl_depth. Qed.

Lemma hpure_hdr : forall (X : hinv) (h : hstate unit) (d : dec_state unit) nf ch rate extra fs,
hpure X h -> h_packet_count h = 0 ->
0 <= fs <= 640 -> 1 <= nf <= 10 -> -2^31 <= ch < 2^31 -> -2^31 <= rate < 2^31 -> -2^31 <= extra < 2^31 - 1 ->
1 + (os_lacing_fill (h_os h) - os_lacing_returned (h_os h)) <= 162 * h_consumed X h -> os_lacing_returned (h_os h) <= os_lacing_fill (h_os h) ->
hpure X (incr_packet_count (set_header h d nf ch rate extra fs)).
Proof.
intros X h d nf ch rate extra fs HP PC0 FS NF CH RT EX BUD RF.
destruct HP as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22
& A23 & A24 & A25 & A26 & A27 & A28).
unfold hpure, h_consumed, h_pend in *. cbn [incr_packet_count set_header h_oy h_os h_bits h_st h_stream_init h_packet_count h_last_granule
h_skip_samples h_nframes h_eos h_channels h_rate h_extra_headers h_speex_serialno h_frame_size h_granule_frame_size h_bytes_remaining].
assert (NF' : (if nf =? 0 then 1 else nf) = nf) by (destruct (Z.eqb_spec nf 0); lia). rewrite NF'.
rewrite PC0 in *.
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7|].
split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact A14|]. split; [lia|].
split; [exact A16|]. split; [exact A17|]. split; [exact A18|]. split; [exact A19|]. split; [lia|].
split; [exact A21|]. split; [exact A22|]. split; [exact A23|]. split; [exact A24|]. split; [exact A25|]. split; [exact A26|]. split; lia.
Qed.

Definition init_cps_at8 (RT : rt_sig) (mo : spx_mode) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (lo : Z) (ras : list Z) (OUT STEREO : Z),
fdfs_only PMc -> mat_stable PMc ->
a0 = Z_to_bv 64 (sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode mo) -> tp = Z_to_bv 64 0x630458 ->
Z.of_nat (length (rt_live RT Σ)) + init_nblocks mo <= LIVE_MAX -> init_credit mo <= rt_credit RT Σ ->
(length (rt_frames RT Σ) + mode_depth mo <= FRAMES_MAX)%nat ->
init_traces mo (bv_unsigned ra) ras -> uw_entry m s0 (bv_unsigned sp) lo ras ->
ART RT Σ m -> mem_inv asegs m -> frm0 fc ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + init_stack mo <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 32 = 0 ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_speex_decoder_init m)))
(fun c => exists (Σ' : rts RT) (D : Z) (LBD : list block) (NEW : list (Z * Z)),
ASTA RT Σ' PMc (fun ms => exists m',
ret_stL (fun _ fc' => frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 D) m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [] m m'
/\ DREP OUT STEREO m' D (init_dec mo) LBD) c
/\ rt_live RT Σ' = NEW ++ rt_live RT Σ /\ Permutation NEW (blocks_live LBD) /\ List.NoDup (map blk_id LBD) /\ Z.of_nat (length NEW) = init_nblocks mo
/\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ - init_credit mo <= rt_credit RT Σ' <= rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ
/\ blocks_al8 LBD).

Section Hdr.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis IO_drv : forall y, in_ranges IO_FP y -> ~ drv_cell y.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.
Variable X : hinv.
Hypothesis HX : hinv_ok OUT_rep IO_FP X.
Variable F0 : list (word * FdEntry).
Variable fs0 : Fs.Fs.
Local Notation usp := (x_usp X). Local Notation S1 := (x_S1 X). Local Notation lo := (x_lo X). Local Notation F := (x_F X).
Local Notation sf := (x_sf X). Local Notation mR := (x_mR X).
Local Notation PMh := (PMfd F0 fs0).

Definition W_h : list (Z * Z) :=
[(S1, S1 + 216); (sf, sf + 16); (F + 32, F + 88); (F + 8384, F + 8388); (F + 9232, F + 9236); (F + 9248, F + 9252)].

Lemma fp_h_Wh : forall a h, fp_h X a h W_h.
Proof.
intros a h. unfold W_h.
repeat (apply fp_h_cons; [unfold iv_h; first [left; lia | right; left; lia | right; right; left; lia] |]). apply fp_h_nil.
Qed.

Lemma h_uw_chain : forall m, rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) mR m -> uw_chain USTACK_TOP m S1 usp [0x96564].
Proof using HX IO_img.
intros m PF. pose proof (h_saves_at OUT_rep IO_FP IO_img X HX m PF) as SV. unfold h_saves in SV.
change [C8 (x_s11 X); C8 (x_s10 X); C8 (x_s9 X); C8 (x_s8 X); C8 (x_s7 X); C8 (x_s6 X); C8 (x_s5 X); C8 (x_s4 X); C8 (x_s3 X); C8 (x_s2 X);
C8 (x_s1 X); C8 (x_s0 X); C8 (x_ra X)]
with ([C8 (x_s11 X); C8 (x_s10 X); C8 (x_s9 X); C8 (x_s8 X); C8 (x_s7 X); C8 (x_s6 X); C8 (x_s5 X); C8 (x_s4 X); C8 (x_s3 X); C8 (x_s2 X);
C8 (x_s1 X)] ++ [C8 (x_s0 X); C8 (x_ra X)]) in SV.
apply rw_cells_app in SV as [_ SV]. cbn [cells_size csize Nat.add] in SV.
replace (usp + -104 + Z.of_nat 88) with (usp + -16) in SV by lia.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & _).
apply (uw_chain_push USTACK_TOP m S1 usp (bv_unsigned (x_s0 X)) 0x96564 []); [lia| clear - U16; Z.div_mod_to_equations; lia| unfold USTACK_TOP in *; lia| apply bv_unsigned_in_range| |].
- rewrite Z_to_bv_bv_unsigned. rewrite (hi_ra _ _ _ HX) in SV. exact SV.
- apply uw_chain_base. destruct (hi_s0 _ _ _ HX) as [H|[H|H]]; [left; lia| right; left; exact H| right; right; exact H].
Qed.

Lemma h_unwind : forall m site, rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) mR m -> In [site; 0x96564] SITE_TRACES -> 0 <= site < 2^64 ->
unwind_ch m (Z64 site) (Z64 usp) (Z64 S1).
Proof using HX IO_img.
intros m site PF IN SR. pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SRR & _).
exists [0x96564]. rewrite !unsigned_lit by (unfold USTACK_TOP in *; lia). split; [exact IN| exact (h_uw_chain m PF)].
Qed.

Lemma new_not_client : forall (Σ : rts RT) (m : mem) L Lold p n x,
ART RT Σ m -> rt_live RT Σ = L ++ Lold -> rt_frames RT Σ = [(F, 8%nat)] -> rt_sp0 RT Σ = x_sp0 X ->
In (p, n) L -> p <= x < p + n -> ~ aclient Lold [(F, 8%nat)] S1 x.
Proof using AF HX.
intros Σ m L Lold p n x ART0 EL EF ES Hin Hx Hc.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
assert (INL : In (p, n) (rt_live RT Σ)) by (rewrite EL; apply in_or_app; left; exact Hin).
assert (INF : In (F, 8%nat) (rt_frames RT Σ)) by (rewrite EF; left; reflexivity).
destruct (af_live_range RT AF Σ m p n ART0 INL) as (P0 & P1 & P2).
destruct (af_frames_range RT AF Σ m F 8 ART0 INF) as (_ & _ & _ & FR).
destruct (af_fshadow_apart RT AF Σ m F 8 ART0 INF) as (FSH & _).
change (fs_size 8) with 16384 in FR, FSH. rewrite <- ESF, ESF2 in FSH.
rewrite ES in P1. unfold RT_STACK, H_STACK in LR.
destruct Hc as [H|[H|[H|[H|H]]]].
- lia.
- pose proof (client_static_range _ H). unfold SEGTOP_A in *. lia.
- destruct H as (p' & q' & Hin' & H'). destruct (in_split _ _ Hin) as (l1 & l2 & E).
destruct (af_live_disj RT AF Σ m p n p' q' l1 (l2 ++ Lold) ART0) as [D|D]; [rewrite EL, E, <- app_assoc; reflexivity| |lia|lia].
apply in_or_app. right. apply in_or_app. right. exact Hin'.
- destruct H as (f & k & [E|[]] & H'). injection E as <- <-. change (fs_size 8) with 16384 in H'. destruct (FR p n INL); lia.
- destruct H as (f & k & [E|[]] & H'). injection E as <- <-. change (fs_size 8) with 16384 in H'. rewrite <- ESF, ESF2 in H'.
destruct (FSH p n INL); lia.
Qed.

Lemma art_munch_h : forall (Σ : rts RT) (m m1 : mem) W,
ART RT Σ m -> rt_frames RT Σ = [(F, 8%nat)] -> rt_sp0 RT Σ = x_sp0 X ->
munch W m m1 -> wmono asegs m m1 ->
(forall lo' hi', In (lo', hi') W -> (S1 <= lo' /\ hi' <= USTACK_TOP) \/ (sf <= lo' /\ hi' <= sf + 2048) \/ (F <= lo' /\ hi' <= F + 16376)) ->
ART RT Σ m1.
Proof using AF HX.
intros Σ m m1 W ART0 EF ES MU WM HW.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
apply (af_frame RT AF Σ m m1 S1 ART0); [rewrite ES; unfold RT_STACK, H_STACK in LR; lia| | exact WM].
intros b Hb. apply MU. apply outside_intro. intros l hh Hin Hx. apply Hb. rewrite EF.
destruct (HW l hh Hin) as [H|[H|H]].
- left. lia.
- right; right; right; right. exists F, 8%nat. split; [left; reflexivity|]. change (fs_size 8) with 16384. rewrite <- ESF, ESF2. lia.
- right; right; right; left. exists F, 8%nat. split; [left; reflexivity|]. change (fs_size 8) with 16384. lia.
Qed.

Lemma pf_munch_h : forall (L : list (Z * Z)) (m m1 : mem) W W',
munch W m m1 -> (forall x, outside W' x -> outside W x) -> rt_pres_fp L [(F, 8%nat)] S1 W' m m1.
Proof. intros L m m1 W W' MU HW. apply (pres_fp_of_munch _ _ _ _ _ m m1 MU). intros x _ Ho. exact (HW x Ho). Qed.

Lemma own_pos_h : forall (m : mem) a (h : hstate unit), h_os_rep X m a h -> h_dec_rep X m a h -> hpure X h ->
forall p q, In (p, q) (h_own a h) -> 0 < q.
Proof.
intros m a h OSR DEC HP p q Hin.
unfold h_own in Hin. apply in_app_or in Hin as [Hin|Hin].
- unfold h_dec_rep in DEC. destruct (h_st h) as [d|]; [| destruct Hin].
destruct DEC as (R & _). unfold blocks_live in Hin. apply in_map_iff in Hin as (b & E & Hb). injection E as <- <-.
exact (h_drep_sizes_pos d _ _ m _ _ R b Hb).
- apply in_app_or in Hin as [[E|[]]|Hin].
{ injection E as <- <-. destruct HP as (_ & _ & _ & _ & _ & _ & B & _). lia. }
apply in_app_or in Hin as [Hin|Hin].
+ unfold h_os_rep in OSR. destruct (h_stream_init h =? 0); [destruct Hin|].
destruct OSR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L0 & B0 & _).
destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
+ destruct (sy_data (h_oy h)) eqn:ED; [| destruct Hin]. destruct Hin as [E|[]]. injection E as <- <-.
destruct HP as (_ & _ & (S0 & _) & (DN & ND) & _). destruct (Z.eq_dec (sy_storage (h_oy h)) 0) as [Z0|NZ]; [| lia].
specialize (ND Z0). congruence.
Qed.

Lemma own_xlive_ne : forall a (h : hstate unit), hsep X a h -> (forall p q, In (p, q) (h_own a h) -> 0 < q) ->
forall p q, In (p, q) (h_own a h) -> forall e, In e (x_live X) -> fst e <> p.
Proof using HX.
intros a h HSP OPOS p q Hin [q' k'] Hq E. cbn [fst] in E. subst q'.
destruct (proj1 HSP _ _ Hin) as (_ & _ & _ & _ & _ & SEP). pose proof (OPOS _ _ Hin) as P1.
pose proof (proj1 (hi_live _ _ _ HX) _ _ Hq) as P2. destruct (SEP _ _ Hq); lia.
Qed.

Lemma h_lrl_app : forall ps l1 l2, live_remove_list ps (l1 ++ l2) = live_remove_list ps l1 ++ live_remove_list ps l2.
Proof. induction ps as [|p ps IH]; intros l1 l2; [reflexivity|]. cbn [live_remove_list fold_right]. unfold live_remove_list in IH. rewrite IH. apply live_remove_app. Qed.
Lemma h_lrl_all : forall ps l, (forall e, In e l -> In (fst e) ps) -> live_remove_list ps l = [].
Proof.
intros ps l H. destruct (live_remove_list ps l) as [|e l'] eqn:E; [reflexivity|]. exfalso.
assert (He : In e (live_remove_list ps l)) by (rewrite E; left; reflexivity).
pose proof (live_remove_list_sub _ _ _ He) as He1. pose proof (H e He1) as Hin.
clear E H He1. revert l He. induction ps as [|p ps IH]; intros l He; [destruct Hin|]. cbn [live_remove_list fold_right] in He.
apply live_remove_in in He as (He & NE). destruct Hin as [E|Hin]; [exact (NE (eq_sym E))| exact (IH Hin l He)].
Qed.
Lemma h_lrl_none : forall ps l, (forall e, In e l -> ~ In (fst e) ps) -> live_remove_list ps l = l.
Proof.
induction ps as [|p ps IH]; intros l H; [reflexivity|]. cbn [live_remove_list fold_right]. unfold live_remove_list in IH.
rewrite IH by (intros e He Hin; apply (H e He); right; exact Hin). apply live_remove_none. intros e He E. apply (H e He). left. symmetry. exact E.
Qed.
Lemma h_lrl_perm : forall ps l l', Permutation l l' -> Permutation (live_remove_list ps l) (live_remove_list ps l').
Proof. induction ps as [|p ps IH]; intros l l' P; [exact P|]. cbn [live_remove_list fold_right]. apply perm_live_remove. apply IH. exact P. Qed.

Hypothesis BDES : speex_bits_destroy_cps RT.
Hypothesis SCLR : ogg_stream_clear_cps RT.
Hypothesis YCLR : ogg_sync_clear_cps RT.

Lemma hp_tail_ok : forall (h : hstate unit) (a : haux) (k : Z) (Σ : rts RT) (m : mem) (cc : config) T
(ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 s9 s10 t3 t4 t5 t6 : word) Fr fc
(w0 w8 w16 w48 w56 w64 w80 w88 w104 w112 w128 w136 w144 w160 w168 w176 w184 w192 w200 : word),
ASTA RT Σ PMh (eq (MS (mkR ra (Z64 S1) (x_gp X) (Z64 0x630458) t0 t1 t2 (Z64 usp) (Z64 S1) a0 a1 a2 a3 a4 a5 a6 a7
(Z64 (F + HO_OP)) (Z64 sf) (Z64 (F + HO_OUT)) s5 s6 (Z64 (F + HO_OS)) s8 s9 s10 (Z64 (F + HO_BITS)) t3 t4 t5 t6)
Fr (Z64 0x971c8) fc None m (seg_rom asegs))) cc ->
X1cn.frm0 fc -> hsig_k RT X Σ a h k -> h_cost h + k <= FUZZ_COST - 1 -> h_st h = None -> h_stream_init h = 1 -> hpure X h ->
ART RT Σ m -> mem_inv asegs m -> stk asegs m lo S1 ->
rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) mR m -> ERR_rep m -> (forall so, OUT_rep so mR -> OUT_rep so m) -> io_ssp m ->
rw_cells asegs m S1 (hsp w0 w8 w16 (Z64 (sf + 16)) (Z64 F) (Z64 F) w48 w56 w64 (Z64 (x_d X)) w80 w88 (Z64 SHB) w104 w112 (Z64 (F + HO_OY))
w128 w136 w144 (Z64 (F + HO_OS)) w160 w168 w176 w184 w192 w200 (Z64 F)) ->
rw_cells asegs m sf [CB 16 HSH_L_HDR] ->
bits_rep asegs m (F + HO_BITS) (a_Dc a) (h_bits h) -> h_os_rep X m a h -> sync_rep m (F + HO_OY) (a_Dsy a) (h_oy h) (a_sybytes a) ->
h_dec_rep X m a h ->
(forall c', at_XT RT OUT_rep ERR_rep IO_FP X F0 fs0 c' -> realizes asegs c' T) ->
realizes asegs cc T.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV BDES SCLR YCLR.
intros h a k Σ m cc T ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 s9 s10 t3 t4 t5 t6 Fr fc
w0 w8 w16 w48 w56 w64 w80 w88 w104 w112 w128 w136 w144 w160 w168 w176 w184 w192 w200
Hc FRM HS KC STN SI1 HP ART0 MI ST PF ERR OUTR SSP SP LSH BITS OSR SY DEC Hk.
pose proof (hsep_of_k RT AF OUT_rep IO_FP X HX Σ m a h k ART0 HS) as HSP.
assert (DN : a_S a = 0 /\ a_LBD a = []) by (unfold h_dec_rep in DEC; rewrite STN in DEC; exact DEC). clear DEC.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
assert (HSPS : forall w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208,
cells_size (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208) = 216%nat)
by reflexivity.

refine (rz_evt RT AF Σ PMh _ _ T cc (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply hp_f4; [unfold SH_LO, SH_HI in *; lia | exact LSH | exact MI]. }
intros ms1 cc1 (m1 & -> & MU1 & WM1 & MI1 & LSH1) Hc1. clear Hc.
assert (PR1 : rt_pres_fp (rt_live RT Σ) [(F, 8%nat)] S1 [(sf, sf + 16)] m m1) by (apply (pf_munch_h _ m m1 _ _ MU1); intros x Hx; exact Hx).
pose proof (art_munch_h Σ m m1 _ ART0 EF ESP MU1 WM1 ltac:(intros l hh [E|[]]; injection E as <- <-; right; left; lia)) as ART1.
assert (FPH1 : fp_h X a h [(sf, sf + 16)]) by (apply fp_h_cons; [right; left; lia| apply fp_h_nil]).
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ m m1 a h _ _ HSP PR1
ltac:(intros e He; rewrite EL; apply in_or_app; right; exact He) FPH1 (AF_DRV _ _ ART1) PF ERR OUTR SSP) as (PF1 & ERR1 & OUTR1 & SSP1).
eapply (htr_rw _ _ _ _ m m1 PR1) in SP; rewrite ?HSPS; [| apply acl_stack; unfold USTACK_TOP in *; lia| apply rng_out_cons; [unfold SH_LO, SH_HI in *; lia| apply rng_out_nil]].
assert (OWNTR : forall p q, In (p, q) (h_own a h) -> acl_rng (rt_live RT Σ) [(F, 8%nat)] S1 p q /\ rng_out [(sf, sf + 16)] p q).
{ intros p q Hin. split; [apply (acl_live _ _ _ _ _ _ _ (INL _ Hin)); lia|].
apply rng_out_cons; [apply (iv_own_fshadow X a h HSP _ _ _ _ _ _ Hin); lia|]. apply rng_out_nil. }
assert (BOK : bits_ok (h_bits h)) by (destruct HP as (_ & _ & _ & _ & B & _); exact B).
assert (BITS1 : bits_rep asegs m1 (F + HO_BITS) (a_Dc a) (h_bits h)).
{ destruct (OWNTR _ _ (own_in_Dc a h)) as (D1 & D2). unfold HO_BITS in *.
apply (bits_rep_tr _ _ _ _ m m1 PR1 _ _ _ BITS BOK); [| | exact D1| exact D2].
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [unfold SH_LO, SH_HI in *; lia|]. apply rng_out_nil. }
assert (SY1 : sync_rep m1 (F + HO_OY) (a_Dsy a) (h_oy h) (a_sybytes a)).
{ unfold HO_OY in *. apply (sync_rep_tr _ _ _ _ m m1 PR1 _ _ _ _ SY).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [unfold SH_LO, SH_HI in *; lia|]. apply rng_out_nil.
- intros NS. exact (OWNTR _ _ (own_in_Dsy a h NS)). }
assert (OSR1 : h_os_rep X m1 a h).
{ apply (h_os_rep_tr _ _ _ _ m m1 PR1 X a h OSR).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- unfold HO_OS. apply rng_out_cons; [unfold SH_LO, SH_HI in *; lia|]. apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
destruct (OWNTR _ _ IB) as (B1 & B2). destruct (OWNTR _ _ IL) as (L1 & L2). destruct (OWNTR _ _ IG) as (G1 & G2).
exact (conj B1 (conj B2 (conj L1 (conj L2 (conj G1 G2))))). }
clear BITS SY OSR PR1 OWNTR.
assert (ST1 : stk asegs m1 lo S1).
{ apply (stk_agree asegs m m1 lo S1 ST); [| exact WM1]. apply (agree_of_munch _ m m1 _ MU1). intros x Hx. cbn [outside].
split; [unfold SH_LO, SH_HI in *; lia| exact I]. }
clear MU1 WM1 ST PF ERR OUTR SSP LSH MI ART0.

assert (BSH1 : ro_cells asegs m1 (shad (F + 8400)) bits_shadow) by exact (h_bits_shadow_at OUT_rep IO_FP IO_img X HX m1 PF1).
assert (INF1 : In (F, 8%nat) (rt_frames RT Σ)) by (rewrite EF; left; reflexivity).
pose proof (INL _ (own_in_Dc a h)) as INDc.
pose proof (h_unwind m1 0x971ec PF1 ltac:(clear; vm_compute; tauto) ltac:(lia)) as UW1.
unfold HO_BITS in BITS1. unfold A_bdes_hp in Hc1.
Time cps_rt (BDES Σ PMh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (F + 8400) (a_Dc a) F lo 8%nat (h_bits h)).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ destruct HP as (_ & _ & _ & _ & _ & B & _). exact B. }
{ change (fs_size 8) with 16384. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). exact ST1. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold RT_STACK. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). clear - S32. Z.div_mod_to_equations. lia. }
intros cc2 (Σ2 & Hc2 & EL2 & EF2 & ES2 & EC2 & EP2). clear Hc1.
Time cps_unpack_lib Hc2 as (v2 & m2 & RS & RA2 & PR2).
destruct RS as (-> & ->).
destruct RA2 as (ART2 & MI2 & ST2).
rewrite EF in PR2.

assert (DEC1 : h_dec_rep X m1 a h) by (unfold h_dec_rep; rewrite STN; exact DN).
pose proof (own_pos_h m1 a h OSR1 DEC1 HP) as OPOS. clear DEC1.
pose proof (own_xlive_ne a h HSP OPOS) as XNE.
assert (NDc : forall p q, In (p, q) (h_own a h) -> p <> a_Dc a -> In (p, q) (rt_live RT Σ2)).
{ intros p q Hin NE. rewrite EL2. apply live_remove_keep; [exact (INL _ Hin)| exact NE]. }
assert (XL2 : forall e, In e (x_live X) -> In e (rt_live RT Σ2)).
{ intros e He. rewrite EL2. apply live_remove_keep; [rewrite EL; apply in_or_app; right; exact He| exact (XNE _ _ (own_in_Dc a h) e He)]. }
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ m1 m2 a h _ _ HSP PR2 XL2 (fp_h_nil X a h) (AF_DRV _ _ ART2) PF1 ERR1 OUTR1 SSP1)
as (PF2 & ERR2 & OUTR2 & SSP2).
eapply (htr_rw _ _ _ _ m1 m2 PR2) in SP; rewrite ?HSPS; [| apply acl_stack; unfold USTACK_TOP in *; lia| apply rng_out_nil].
eapply (htr_rw _ _ _ _ m1 m2 PR2) in LSH1; cbn [cells_size csize Nat.add];
[| apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia| apply rng_out_nil].
pose proof (own_ne_Dsy a h (proj2 (proj2 HSP))) as ONE.
assert (OSN : forall p, In p [a_Bd a; a_L a; a_G a] -> p <> a_Dc a).
{ intros p Hp. pose proof (proj2 (proj2 HSP)) as ND1. unfold h_own in ND1. rewrite STN in ND1. cbn [app] in ND1.
replace (h_stream_init h =? 0) with false in ND1 by (rewrite SI1; reflexivity). cbn [map fst app] in ND1.
apply NoDup_cons_iff in ND1 as (N1 & _). intros E. subst p. apply N1. destruct Hp as [E|[E|[E|[]]]]; rewrite <- E; cbn [In]; repeat (first [left; reflexivity | right]). }
assert (OSR2 : h_os_rep X m2 a h).
{ apply (h_os_rep_tr _ _ _ _ m1 m2 PR2 X a h OSR1).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
split; [apply (acl_live _ _ _ _ _ _ _ (NDc _ _ IB (OSN _ (or_introl eq_refl)))); lia|]. split; [apply rng_out_nil|].
split; [apply (acl_live _ _ _ _ _ _ _ (NDc _ _ IL (OSN _ (or_intror (or_introl eq_refl))))); lia|]. split; [apply rng_out_nil|].
split; [apply (acl_live _ _ _ _ _ _ _ (NDc _ _ IG (OSN _ (or_intror (or_intror (or_introl eq_refl)))))); lia| apply rng_out_nil]. }
assert (SY2 : sync_rep m2 (F + HO_OY) (a_Dsy a) (h_oy h) (a_sybytes a)).
{ apply (sync_rep_tr _ _ _ _ m1 m2 PR2 _ _ _ _ SY1).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OY; lia.
- apply rng_out_nil.
- intros NS. destruct (ONE NS) as (N1 & _). split; [| apply rng_out_nil].
apply (acl_live _ _ _ _ _ _ _ (NDc _ _ (own_in_Dsy a h NS) (not_eq_sym N1))); unfold bptr in *; lia. }
clear OSR1 SY1 PR2.

refine (rz_evt RT AF Σ2 PMh _ _ T cc2 (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply hp_f5; [reflexivity | exact MI2]. }
intros ms3 cc3 -> Hc3. clear Hc.
pose proof OSR2 as OSR2'. unfold h_os_rep in OSR2'. replace (h_stream_init h =? 0) with false in OSR2' by (rewrite SI1; reflexivity).
destruct OSR2' as (OSC & LSH0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & LS0 & BS0 & BL & BG & LG).
assert (SIN : h_stream_init h <> 0) by (rewrite SI1; discriminate).
destruct (own_in_os a h SIN) as (IB & IL & IG).
assert (SLV : stream_live RT Σ2 (h_os h) (a_Bd a) (a_L a) (a_G a)).
{ split; [exact (NDc _ _ IB (OSN _ (or_introl eq_refl)))|]. split; [exact (NDc _ _ IL (OSN _ (or_intror (or_introl eq_refl))))|].
split; [exact (NDc _ _ IG (OSN _ (or_intror (or_intror (or_introl eq_refl)))))|]. split; [exact BL|]. split; [exact BG| exact LG]. }
pose proof (h_acc_at OUT_rep IO_FP IO_img X HX m2 PF2) as (_ & _ & _ & _ & _ & _ & ACOS & _).
assert (INF2 : In (F, 8%nat) (rt_frames RT Σ2)) by (rewrite EF2, EF; left; reflexivity).
unfold HO_OS in OSC, ACOS. unfold A_sclr_hp in Hc3.
Time cps_rt (SCLR Σ2 PMh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 (F + 8688) (a_Bd a) (a_L a) (a_G a) F lo 8%nat
(h_os h) (a_shdr a)).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ unfold bptr in *. lia. }
{ unfold bptr in *. lia. }
{ change (fs_size 8) with 16384. lia. }
{ first [exact ST2 | rewrite unsigned_lit by (unfold USTACK_TOP in *; lia); exact ST2]. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold RT_STACK. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). clear - S32. Z.div_mod_to_equations. lia. }
intros cc4 (Σ3 & Hc4 & EL3 & EF3 & ES3 & EC3 & EP3). clear Hc3.
Time cps_unpack_lib Hc4 as (m3 & RS & RA3 & PR3 & OSC3).
destruct RS as (-> & ->).
destruct RA3 as (ART3 & MI3 & ST3).
rewrite EF2, EF in PR3.
assert (XL3 : forall e, In e (x_live X) -> In e (rt_live RT Σ3)).
{ intros e He. rewrite EL3. apply live_remove_keep; [apply live_remove_keep; [apply live_remove_keep; [exact (XL2 e He)|]|]|].
- exact (XNE _ _ IB e He). - exact (XNE _ _ IL e He). - exact (XNE _ _ IG e He). }
assert (PR3S : rt_pres_fp (rt_live RT Σ3) [(F, 8%nat)] S1 [(F + 8688, F + 8688 + 408)] m2 m3) by (rewrite EL3; exact PR3).
assert (FPH3 : fp_h X a h [(F + 8688, F + 8688 + 408)]) by (apply fp_h_cons; [right; right; left; lia| apply fp_h_nil]).
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ2 m2 m3 a h _ _ HSP PR3S XL3 FPH3 (AF_DRV _ _ ART3) PF2 ERR2 OUTR2 SSP2)
as (PF3 & ERR3 & OUTR3 & SSP3).
eapply (htr_rw _ _ _ _ m2 m3 PR3S) in SP; rewrite ?HSPS; [| apply acl_stack; unfold USTACK_TOP in *; lia| apply rng_out_cons; [lia| apply rng_out_nil]].
eapply (htr_rw _ _ _ _ m2 m3 PR3S) in LSH1; cbn [cells_size csize Nat.add];
[| apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia| apply rng_out_cons; [lia| apply rng_out_nil]].
assert (NDsy : sy_data (h_oy h) <> None -> forall p, In p [a_Bd a; a_L a; a_G a; a_Dc a] -> p <> a_Dsy a).
{ intros NS p Hp. destruct (ONE NS) as (N1 & N2 & _). destruct (N2 SIN) as (B & L & G).
destruct Hp as [<-|[<-|[<-|[<-|[]]]]]; congruence. }
assert (SYL3 : sy_data (h_oy h) <> None -> In (a_Dsy a, sy_storage (h_oy h)) (rt_live RT Σ3)).
{ intros NS. pose proof (own_in_Dsy a h NS) as INS. rewrite EL3.
apply live_remove_keep; [apply live_remove_keep; [apply live_remove_keep; [apply (NDc _ _ INS); exact (not_eq_sym (NDsy NS _ (or_intror (or_intror (or_intror (or_introl eq_refl))))))|]|]|];
cbn [fst]; intros E; symmetry in E; revert E; apply (NDsy NS); cbn [In]; repeat (first [left; reflexivity | right]). }
assert (SY3 : sync_rep m3 (F + HO_OY) (a_Dsy a) (h_oy h) (a_sybytes a)).
{ apply (sync_rep_tr _ _ _ _ m2 m3 PR3S _ _ _ _ SY2).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OY; lia.
- unfold HO_OY. apply rng_out_cons; [lia| apply rng_out_nil].
- intros NS. pose proof (own_in_Dsy a h NS) as INS. split.
+ apply (acl_live _ _ _ _ _ _ _ (SYL3 NS)); unfold bptr in *; lia.
+ unfold bptr in *. apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ INS); lia| apply rng_out_nil]. }
clear SY2 PR3 PR3S.

refine (rz_evt RT AF Σ3 PMh _ _ T cc4 (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply hp_f6; [reflexivity | unfold USTACK_TOP in *; lia | exact SP | exact MI3]. }
intros ms5 cc5 -> Hc5. clear Hc.
assert (INF3 : In (F, 8%nat) (rt_frames RT Σ3)) by (rewrite EF3, EF2, EF; left; reflexivity).
unfold A_yclr_hp in Hc5. unfold HO_OY in SY3.
Time cps_rt (YCLR Σ3 PMh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 (F + 8480) (a_Dsy a) F lo 8%nat (h_oy h) (a_sybytes a)).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ change (fs_size 8) with 16384. lia. }
{ first [exact ST3 | rewrite unsigned_lit by (unfold USTACK_TOP in *; lia); exact ST3]. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold RT_STACK. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). clear - S32. Z.div_mod_to_equations. lia. }
intros cc6 (Σ4 & Hc6 & EL4 & EF4 & ES4 & EC4 & EP4). clear Hc5.
Time cps_unpack_lib Hc6 as (m4 & RS & RA4 & PR4 & SY4).
destruct RS as (-> & ->).
destruct RA4 as (ART4 & MI4 & ST4).

assert (OWNL : forall e, In e (a_P a) -> fst e = a_Dc a \/ fst e = a_Bd a \/ fst e = a_L a \/ fst e = a_G a \/ (sy_data (h_oy h) <> None /\ fst e = a_Dsy a)).
{ intros e He. pose proof (Permutation_in _ PERM He) as Ho. unfold h_own in Ho. rewrite STN in Ho. cbn [app] in Ho.
replace (h_stream_init h =? 0) with false in Ho by (rewrite SI1; reflexivity).
destruct Ho as [E|[E|[E|[E|Ho]]]]; [left| right; left| right; right; left| right; right; right; left| ]; try (rewrite <- E; reflexivity).
right; right; right; right. destruct (sy_data (h_oy h)) eqn:ED; [| destruct Ho]. destruct Ho as [E|[]]. split; [discriminate| rewrite <- E; reflexivity]. }
assert (ELX : rt_live RT Σ4 = x_live X).
{ rewrite EL4, EL3, EL2, EL. unfold sync_clear_live, bptr.
change (live_remove (a_G a) (live_remove (a_L a) (live_remove (a_Bd a) (live_remove (a_Dc a) (a_P a ++ x_live X)))))
with (live_remove_list [a_G a; a_L a; a_Bd a; a_Dc a] (a_P a ++ x_live X)).
destruct (sy_data (h_oy h)) eqn:ED.
- change (live_remove (a_Dsy a) (live_remove_list [a_G a; a_L a; a_Bd a; a_Dc a] (a_P a ++ x_live X)))
with (live_remove_list [a_Dsy a; a_G a; a_L a; a_Bd a; a_Dc a] (a_P a ++ x_live X)).
rewrite h_lrl_app, h_lrl_all, h_lrl_none; [reflexivity| |].
+ intros e He Hin. cbn [In] in Hin.
destruct Hin as [E|[E|[E|[E|[E|[]]]]]];
[ exact (XNE _ _ (own_in_Dsy a h ltac:(rewrite ED; discriminate)) e He (eq_sym E))
| exact (XNE _ _ IG e He (eq_sym E)) | exact (XNE _ _ IL e He (eq_sym E)) | exact (XNE _ _ IB e He (eq_sym E))
| exact (XNE _ _ (own_in_Dc a h) e He (eq_sym E)) ].
+ intros e He. destruct (OWNL e He) as [E|[E|[E|[E|(_ & E)]]]]; rewrite E;
[ exact (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))
| exact (or_intror (or_intror (or_intror (or_introl eq_refl))))
| exact (or_intror (or_intror (or_introl eq_refl)))
| exact (or_intror (or_introl eq_refl))
| exact (or_introl eq_refl) ].
- rewrite h_lrl_app, h_lrl_all, h_lrl_none; [reflexivity| |].
+ intros e He Hin. cbn [In] in Hin.
destruct Hin as [E|[E|[E|[E|[]]]]];
[ exact (XNE _ _ IG e He (eq_sym E)) | exact (XNE _ _ IL e He (eq_sym E)) | exact (XNE _ _ IB e He (eq_sym E))
| exact (XNE _ _ (own_in_Dc a h) e He (eq_sym E)) ].
+ intros e He. destruct (OWNL e He) as [E|[E|[E|[E|(NS & E)]]]]; [rewrite E .. | exfalso; exact (NS eq_refl)].
* exact (or_intror (or_intror (or_intror (or_introl eq_refl)))).
* exact (or_intror (or_intror (or_introl eq_refl))).
* exact (or_intror (or_introl eq_refl)).
* exact (or_introl eq_refl). }
rewrite EF3, EF2, EF in PR4. rewrite <- EL4, ELX in PR4.
assert (FPH4 : fp_h X a h [(F + 8480, F + 8480 + 32)]) by (apply fp_h_cons; [right; right; left; lia| apply fp_h_nil]).
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ3 m3 m4 a h _ _ HSP PR4 (fun e He => He) FPH4 (AF_DRV _ _ ART4) PF3 ERR3 OUTR3 SSP3)
as (PF4 & ERR4 & OUTR4 & _).
eapply (htr_rw _ _ _ _ m3 m4 PR4) in SP; rewrite ?HSPS; [| apply acl_stack; unfold USTACK_TOP in *; lia| apply rng_out_cons; [lia| apply rng_out_nil]].
eapply (htr_rw _ _ _ _ m3 m4 PR4) in LSH1; cbn [cells_size csize Nat.add];
[| apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia| apply rng_out_cons; [lia| apply rng_out_nil]].
replace (ret_pc (Z64 0x971fc)) with (Z64 0x971fc) in Hc by (symmetry; apply ret_pc_even; [lia| reflexivity]).
apply Hk. unfold at_XT, A_XT.
do 50 eexists.
split; [exact Hc|]. split; [exact FRM|]. split; [exact ELX|]. split; [rewrite EF4, EF3, EF2; exact EF|]. split; [rewrite ES4, ES3, ES2; exact ESP|].
split; [rewrite EP4, EP3, EP2; exact EPO0|]. split; [rewrite EC4, EC3, EC2; lia|].
split; [exact ART4|]. split; [exact MI4|]. split; [first [exact ST4 | rewrite unsigned_lit in ST4 by (unfold USTACK_TOP in *; lia); exact ST4]|].
split; [exact PF4|]. split; [exact ERR4|]. split; [exact OUTR4|]. split; [exact SP| exact LSH1].
Qed.

Definition hsig_x (Σ : rts RT) (a : haux) (h : hstate unit) (k : Z) (L : list (Z * Z)) : Prop :=
rt_live RT Σ = L ++ a_P a ++ x_live X /\ List.NoDup (map fst (a_P a)) /\ Permutation (a_P a) (h_own a h)
/\ rt_frames RT Σ = [(F, 8%nat)] /\ rt_sp0 RT Σ = x_sp0 X /\ rt_pois RT Σ = [] /\ x_cr0 X - h_cost h - k <= rt_credit RT Σ.
Lemma hsig_x_nil : forall Σ a h k, hsig_x Σ a h k [] -> hsig_k RT X Σ a h k.
Proof. intros Σ a h k (A1 & A2 & A3 & A4 & A5 & A6 & A7). unfold hsig_k. repeat split; assumption. Qed.

Lemma live_remove_top : forall (Σ : rts RT) (m : mem) p n R, ART RT Σ m -> rt_live RT Σ = (p, n) :: R -> 0 < n ->
(forall e, In e R -> 0 < snd e) -> live_remove p ((p, n) :: R) = R.
Proof using AF.
intros Σ m p n R ART0 EL N0 RP. rewrite live_remove_cons. cbn [fst]. rewrite Z.eqb_refl. apply live_remove_none.
intros [p' n'] He E. cbn [fst] in E. subst p'. pose proof (RP _ He) as P1. cbn [snd] in P1.
destruct (af_live_disj RT AF Σ m p n p n' [] R ART0 ltac:(rewrite EL; reflexivity) ltac:(exact He)); lia.
Qed.

Lemma hp_tr0 : forall (Σ' : rts RT) (m m' : mem) a (h : hstate unit) (L : list (Z * Z)) (spill : list cell),
hsep X a h -> rt_live RT Σ' = L ++ a_P a ++ x_live X -> Permutation (a_P a) (h_own a h) -> drv_consts m' ->
rt_pres_fp (rt_live RT Σ') [(F, 8%nat)] S1 [] m m' ->
rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) mR m -> ERR_rep m -> (forall so, OUT_rep so mR -> OUT_rep so m) -> io_ssp m ->
rw_cells asegs m S1 spill -> cells_size spill = 216%nat -> rw_cells asegs m sf [CB 16 HSH_L_HDR] ->
bits_rep asegs m (F + HO_BITS) (a_Dc a) (h_bits h) -> bits_ok (h_bits h) -> h_os_rep X m a h -> sync_rep m (F + HO_OY) (a_Dsy a) (h_oy h) (a_sybytes a) ->
rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) mR m' /\ ERR_rep m' /\ (forall so, OUT_rep so mR -> OUT_rep so m') /\ io_ssp m'
/\ rw_cells asegs m' S1 spill /\ rw_cells asegs m' sf [CB 16 HSH_L_HDR]
/\ bits_rep asegs m' (F + HO_BITS) (a_Dc a) (h_bits h) /\ h_os_rep X m' a h /\ sync_rep m' (F + HO_OY) (a_Dsy a) (h_oy h) (a_sybytes a).
Proof using HX ERR_loc OUT_loc IO_img.
intros Σ' m m' a h L spill HSP EL PERM DC PR PF ERR OUTR SSP SP SPS LSH BITS BOK OSR SY.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ')).
{ intros e He. rewrite EL. apply in_or_app. right. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ' m m' a h _ _ HSP PR
ltac:(intros e He; rewrite EL; apply in_or_app; right; apply in_or_app; right; exact He) (fp_h_nil X a h) DC PF ERR OUTR SSP)
as (PF' & ERR' & OUTR' & SSP').
split; [exact PF'|]. split; [exact ERR'|]. split; [exact OUTR'|]. split; [exact SSP'|].
split; [apply (htr_rw _ _ _ _ m m' PR _ _ SP); rewrite SPS; [apply acl_stack; unfold USTACK_TOP in *; lia| apply rng_out_nil]|].
split; [apply (htr_rw _ _ _ _ m m' PR _ _ LSH); cbn [cells_size csize Nat.add];
[apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia| apply rng_out_nil]|].
split.
{ unfold HO_BITS in *. apply (bits_rep_tr _ _ _ _ m m' PR _ _ _ BITS BOK); [| apply rng_out_nil| | apply rng_out_nil].
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply (acl_live _ _ _ _ _ _ _ (INL _ (own_in_Dc a h))); lia. }
split.
{ apply (h_os_rep_tr _ _ _ _ m m' PR X a h OSR).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IB)); lia|]. split; [apply rng_out_nil|].
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IL)); lia|]. split; [apply rng_out_nil|].
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IG)); lia| apply rng_out_nil]. }
{ unfold HO_OY in *. apply (sync_rep_tr _ _ _ _ m m' PR _ _ _ _ SY).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_nil.
- intros NS. split; [| apply rng_out_nil]. apply (acl_live _ _ _ _ _ _ _ (INL _ (own_in_Dsy a h NS))); unfold bptr in *; lia. }
Qed.

Hypothesis FRE : free_contract RT.
Lemma hp_f54_ok : forall (h : hstate unit) (a : haux) (k v : Z) (Σ : rts RT) (m : mem) (cc : config) T
(ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s10 t3 t4 t5 t6 : word) Fr fc
(w0 w8 w16 w48 w56 w64 w80 w88 w104 w112 w128 w136 w144 w160 w168 w176 w184 w192 w200 : word),
ASTA RT Σ PMh (eq (MS (mkR ra (Z64 S1) (x_gp X) (Z64 0x630458) t0 t1 t2 (Z64 usp) (Z64 S1) a0 a1 a2 a3 a4 a5 a6 a7
(Z64 (F + HO_OP)) (Z64 sf) (Z64 (F + HO_OUT)) (Z64 v) s6 (Z64 (F + HO_OS)) s8 s9 s10 (Z64 (F + HO_BITS)) t3 t4 t5 t6)
Fr (Z64 0x971c0) fc None m (seg_rom asegs))) cc ->
X1cn.frm0 fc -> hsig_x Σ a h k [(v, 80)] -> h_cost h + k <= FUZZ_COST - 1 -> h_st h = None -> h_stream_init h = 1 -> hpure X h ->
ART RT Σ m -> mem_inv asegs m -> stk asegs m lo S1 ->
rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) mR m -> ERR_rep m -> (forall so, OUT_rep so mR -> OUT_rep so m) -> io_ssp m ->
rw_cells asegs m S1 (hsp w0 w8 w16 (Z64 (sf + 16)) (Z64 F) (Z64 F) w48 w56 w64 (Z64 (x_d X)) w80 w88 (Z64 SHB) w104 w112 (Z64 (F + HO_OY))
w128 w136 w144 (Z64 (F + HO_OS)) w160 w168 w176 w184 w192 w200 (Z64 F)) ->
rw_cells asegs m sf [CB 16 HSH_L_HDR] ->
bits_rep asegs m (F + HO_BITS) (a_Dc a) (h_bits h) -> h_os_rep X m a h -> sync_rep m (F + HO_OY) (a_Dsy a) (h_oy h) (a_sybytes a) ->
h_dec_rep X m a h ->
(forall c', at_XT RT OUT_rep ERR_rep IO_FP X F0 fs0 c' -> realizes asegs c' T) ->
realizes asegs cc T.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV BDES SCLR YCLR FRE.
intros h a k v Σ m cc T ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s10 t3 t4 t5 t6 Fr fc
w0 w8 w16 w48 w56 w64 w80 w88 w104 w112 w128 w136 w144 w160 w168 w176 w184 w192 w200
Hc FRM HSX KC STN SI1 HP ART0 MI ST PF ERR OUTR SSP SP LSH BITS OSR SY DEC Hk.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HSX as (EL & ND & PERM & EF & ESP & EPO0 & ECR).

refine (rz_evt RT AF Σ PMh _ _ T cc (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply hp_f3. exact MI. }
intros ms1 cc1 -> Hc1. clear Hc.
pose proof (h_unwind m 0x971c8 PF ltac:(clear; vm_compute; tauto) ltac:(lia)) as UW1.
assert (INV : In (v, 80) (rt_live RT Σ)) by (rewrite EL; left; reflexivity).
unfold A_free_hp in Hc1. change 0x67e94 with e_free in Hc1.
Time cps_rt (FRE Σ PMh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m v 80 lo).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ unfold call_ok. rewrite unsigned_lit by (unfold USTACK_TOP in *; lia).
split; [exact ST|]. split; [rewrite ESP; exact LW|]. split; [unfold RT_STACK; lia|]. split; [unfold USTACK_TOP in *; lia|].
clear - S32. Z.div_mod_to_equations. lia. }
intros cc2 (Σ2 & v2 & Hc2 & EL2 & EF2 & ES2 & EC2 & EP2). clear Hc1.
Time cps_unpack Hc2 as (m2 & RS & RA2 & PR2).
destruct RA2 as (ART2 & MI2 & ST2).
pose proof (own_pos_h m a h OSR DEC HP) as OPOS.
assert (ELR : rt_live RT Σ2 = a_P a ++ x_live X).
{ rewrite EL2, EL. cbn [app]. apply (live_remove_top Σ m v 80 (a_P a ++ x_live X) ART0 EL ltac:(lia)).
intros [p q] He. apply in_app_or in He as [He|He].
- exact (OPOS p q (Permutation_in _ PERM He)).
- exact (proj1 (hi_live _ _ _ HX) p q He). }
assert (HS2 : hsig_k RT X Σ2 a h k).
{ unfold hsig_k. split; [exact ELR|]. split; [exact ND|]. split; [exact PERM|]. split; [rewrite EF2; exact EF|]. split; [rewrite ES2; exact ESP|].
split; [rewrite EP2; exact EPO0| rewrite EC2; exact ECR]. }
pose proof (hsep_of_k RT AF OUT_rep IO_FP X HX Σ2 m2 a h k ART2 HS2) as HSP2.
rewrite EF in PR2. apply (pres_fp_of_pres _ _ _ []) in PR2.
assert (BOK : bits_ok (h_bits h)) by (destruct HP as (_ & _ & _ & _ & B & _); exact B).
destruct (hp_tr0 Σ2 m m2 a h [] _ HSP2 ELR PERM (AF_DRV _ _ ART2) PR2 PF ERR OUTR SSP SP ltac:(reflexivity) LSH BITS BOK OSR SY)
as (PF2 & ERR2 & OUTR2 & SSP2 & SP2 & LSH2 & BITS2 & OSR2 & SY2).
replace (ret_pc (Z64 0x971c8)) with (Z64 0x971c8) in Hc by (symmetry; apply ret_pc_even; [lia| reflexivity]).
assert (DEC2 : h_dec_rep X m2 a h) by (unfold h_dec_rep in *; rewrite STN in *; exact DEC).
exact (hp_tail_ok h a k Σ2 m2 _ T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
Hc FRM HS2 KC STN SI1 HP ART2 MI2 ltac:(first [exact ST2 | rewrite unsigned_lit in ST2 by (unfold USTACK_TOP in *; lia); exact ST2])
PF2 ERR2 OUTR2 SSP2 SP2 LSH2 BITS2 OSR2 SY2 DEC2 Hk).
Qed.

Lemma h_destroy_stack_le : forall d, destroy_stack d <= 32 * Z.of_nat (dec_depth d) - 16.
Proof. induction d as [st|s low IH]; cbn [destroy_stack dec_depth]; [lia|]. rewrite Nat2Z.inj_succ. lia. Qed.

Lemma hsep_of_x : forall (Σ : rts RT) (m : mem) a h k L, ART RT Σ m -> hsig_x Σ a h k L -> hsep X a h.
Proof using AF HX.
intros Σ m a h k L ART1 HS. destruct HS as (EL & ND & PERM & EF & ES & _).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ)).
{ intros e He. rewrite EL. apply in_or_app. right. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
assert (INF : In (F, 8%nat) (rt_frames RT Σ)) by (rewrite EF; left; reflexivity).
destruct (af_frames_range RT AF Σ m F 8 ART1 INF) as (_ & _ & _ & FR).
destruct (af_fshadow_apart RT AF Σ m F 8 ART1 INF) as (FSH & _).
change (fs_size 8) with 16384 in FR, FSH. rewrite <- ESF, ESF2 in FSH.
pose proof (hi_lo _ _ _ HX) as (LW0 & _). rewrite <- ES in LW0.
split; [| split; [| exact (Permutation_NoDup (Permutation_map fst PERM) ND)]].
- intros p q Hin. pose proof (INL _ Hin) as Hl.
destruct (af_live_range RT AF Σ m p q ART1 Hl) as (P0 & P1 & P2).
split; [exact P0|]. split; [lia|]. split; [exact (FR p q Hl)|]. split; [exact (FSH p q Hl)|]. split; [exact P2|].
intros p' q' Hc. pose proof (Permutation_in _ (Permutation_sym PERM) Hin) as HinP. destruct (in_split _ _ HinP) as (l1 & l2 & E).
apply (af_live_disj RT AF Σ m p q p' q' (L ++ l1) (l2 ++ x_live X) ART1). { rewrite EL, E, <- !app_assoc. reflexivity. }
apply in_or_app. right. apply in_or_app. right. exact Hc.
- intros p1 q1 p2 q2 H1 H2 NE. exact (live_sep_gen RT AF Σ m p1 q1 p2 q2 ART1 (INL _ H1) (INL _ H2) NE).
Qed.

Lemma live_apart_app : forall (Σ : rts RT) (m : mem) L R e1 e2, ART RT Σ m -> rt_live RT Σ = L ++ R -> In e1 L -> In e2 R ->
fst e1 + snd e1 <= fst e2 \/ fst e2 + snd e2 <= fst e1.
Proof using AF.
intros Σ m L R [p1 n1] [p2 n2] ART0 EL H1 H2. cbn [fst snd]. destruct (in_split _ _ H1) as (l1 & l2 & E).
apply (af_live_disj RT AF Σ m p1 n1 p2 n2 l1 (l2 ++ R) ART0). { rewrite EL, E, <- app_assoc. reflexivity. }
apply in_or_app. right. apply in_or_app. right. exact H2.
Qed.

Hypothesis DESTROY : forall d, destroy_cps_at RT d.
Lemma hp_f48_ok : forall (h : hstate unit) (a : haux) (k v D : Z) (d : dec_state bptr) (LBD : list block) (NEW : list (Z * Z))
(Σ : rts RT) (m : mem) (cc : config) T
(ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s10 t3 t4 t5 t6 : word) Fr fc
(w0 w8 w16 w48 w56 w64 w80 w88 w104 w112 w128 w136 w144 w160 w168 w176 w184 w192 w200 : word),
ASTA RT Σ PMh (eq (MS (mkR ra (Z64 S1) (x_gp X) (Z64 0x630458) t0 t1 t2 (Z64 usp) (Z64 S1) a0 a1 a2 a3 a4 a5 a6 a7
(Z64 (F + HO_OP)) (Z64 sf) (Z64 (F + HO_OUT)) (Z64 v) s6 s7 s8 (Z64 D) s10 (Z64 (F + HO_BITS)) t3 t4 t5 t6)
Fr (Z64 0x971b4) fc None m (seg_rom asegs))) cc ->
X1cn.frm0 fc -> hsig_x Σ a h k (NEW ++ [(v, 80)]) -> h_cost h + k <= FUZZ_COST - 1 -> h_st h = None -> h_stream_init h = 1 -> hpure X h ->
Permutation NEW (blocks_live LBD) -> List.NoDup (map blk_id LBD) -> DREP (F + HO_OUT) (F + HO_STEREO) m D d LBD -> (dec_depth d <= 3)%nat ->
ART RT Σ m -> mem_inv asegs m -> stk asegs m lo S1 ->
rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) mR m -> ERR_rep m -> (forall so, OUT_rep so mR -> OUT_rep so m) -> io_ssp m ->
rw_cells asegs m S1 (hsp w0 w8 w16 (Z64 (sf + 16)) (Z64 F) (Z64 F) w48 w56 w64 (Z64 (x_d X)) w80 w88 (Z64 SHB) w104 w112 (Z64 (F + HO_OY))
w128 w136 w144 (Z64 (F + HO_OS)) w160 w168 w176 w184 w192 w200 (Z64 F)) ->
rw_cells asegs m sf [CB 16 HSH_L_HDR] ->
bits_rep asegs m (F + HO_BITS) (a_Dc a) (h_bits h) -> h_os_rep X m a h -> sync_rep m (F + HO_OY) (a_Dsy a) (h_oy h) (a_sybytes a) ->
h_dec_rep X m a h ->
(forall c', at_XT RT OUT_rep ERR_rep IO_FP X F0 fs0 c' -> realizes asegs c' T) ->
realizes asegs cc T.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV BDES SCLR YCLR FRE DESTROY.
intros h a k v D d LBD NEW Σ m cc T ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s10 t3 t4 t5 t6 Fr fc
w0 w8 w16 w48 w56 w64 w80 w88 w104 w112 w128 w136 w144 w160 w168 w176 w184 w192 w200
Hc FRM HSX KC STN SI1 HP PNEW NDB DR DD ART0 MI ST PF ERR OUTR SSP SP LSH BITS OSR SY DEC Hk.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HSX as (EL & ND & PERM & EF & ESP & EPO0 & ECR).

refine (rz_evt RT AF Σ PMh _ _ T cc (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply hp_f1. exact MI. }
intros ms1 cc1 -> Hc1. clear Hc.
pose proof (h_unwind m 0x971bc PF ltac:(clear; vm_compute; tauto) ltac:(lia)) as UW1.
assert (INB : forall b, In b LBD -> In (blk_addr b, blk_size b) (rt_live RT Σ)).
{ intros b Hb. rewrite EL. apply in_or_app. left. apply in_or_app. left. apply (Permutation_in _ (Permutation_sym PNEW)).
unfold blocks_live. apply (in_map (fun b => (blk_addr b, blk_size b))). exact Hb. }
pose proof (h_destroy_stack_le d) as DSL.
unfold A_destroy_hp in Hc1. change 0x98480 with A_speex_decoder_destroy in Hc1.
Time cps_rt (DESTROY d Σ PMh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m (F + HO_OUT) (F + HO_STEREO) D lo LBD).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). exact ST. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold RT_STACK. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). clear - S32. Z.div_mod_to_equations. lia. }
intros cc2 (Σ2 & Hc2 & EL2 & EF2 & ES2 & EC2 & EP2). clear Hc1.
Time cps_unpack_lib Hc2 as (v2 & m2 & RS & RA2 & PR2).
destruct RS as (-> & ->).
destruct RA2 as (ART2 & MI2 & ST2).
pose proof (hsep_of_x Σ m a h k _ ART0 HSX) as HSP.
pose proof (own_pos_h m a h OSR DEC HP) as OPOS.
assert (RPOS : forall e, In e ([(v, 80)] ++ a_P a ++ x_live X) -> 0 < snd e).
{ intros [p q] He. apply in_app_or in He as [[E|[]]|He]; [injection E as <- <-; cbn; lia|]. apply in_app_or in He as [He|He].
- exact (OPOS p q (Permutation_in _ PERM He)).
- exact (proj1 (hi_live _ _ _ HX) p q He). }
assert (ELR : rt_live RT Σ2 = [(v, 80)] ++ a_P a ++ x_live X).
{ rewrite EL2, EL, <- app_assoc, h_lrl_app, h_lrl_all, h_lrl_none; [reflexivity| |].
- intros [p q] He Hin. apply in_map_iff in Hin as (b & Eb & Hb). cbn [fst] in Eb. subst p.
assert (INN : In (blk_addr b, blk_size b) NEW) by (apply (Permutation_in _ (Permutation_sym PNEW)); unfold blocks_live; exact (in_map _ _ _ Hb)).
pose proof (h_drep_sizes_pos d _ _ m _ _ DR b Hb) as BP. pose proof (RPOS _ He) as RP. cbn [snd] in RP.
destruct (live_apart_app Σ m NEW ([(v, 80)] ++ a_P a ++ x_live X) _ _ ART0 ltac:(rewrite EL, <- app_assoc; reflexivity) INN He)
as [A|A]; cbn [fst snd] in A; lia.
- intros e He. apply (Permutation_in _ PNEW) in He. unfold blocks_live in He. apply in_map_iff in He as (b & <- & Hb). cbn [fst].
exact (in_map blk_addr _ _ Hb). }
rewrite EF in PR2.
assert (BOK : bits_ok (h_bits h)) by (destruct HP as (_ & _ & _ & _ & B & _); exact B).
destruct (hp_tr0 Σ2 m m2 a h [(v, 80)] _ HSP ELR PERM (AF_DRV _ _ ART2) PR2 PF ERR OUTR SSP SP ltac:(reflexivity) LSH BITS BOK OSR SY)
as (PF2 & ERR2 & OUTR2 & SSP2 & SP2 & LSH2 & BITS2 & OSR2 & SY2).

refine (rz_evt RT AF Σ2 PMh _ _ T cc2 (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply hp_f2; [reflexivity | unfold USTACK_TOP in *; lia | exact SP2 | exact MI2]. }
intros ms3 cc3 -> Hc3. clear Hc.
assert (HSX2 : hsig_x Σ2 a h k [(v, 80)]).
{ split; [exact ELR|]. split; [exact ND|]. split; [exact PERM|]. split; [rewrite EF2; exact EF|]. split; [rewrite ES2; exact ESP|].
split; [rewrite EP2; exact EPO0| rewrite EC2; exact ECR]. }
assert (DEC2 : h_dec_rep X m2 a h) by (unfold h_dec_rep in *; rewrite STN in *; exact DEC).
eapply (hp_f54_ok h a k v Σ2 m2 cc3 T); [exact Hc3 | exact FRM | exact HSX2 | exact KC | exact STN | exact SI1 | exact HP | exact ART2 | exact MI2
| first [exact ST2 | rewrite unsigned_lit in ST2 by (unfold USTACK_TOP in *; lia); exact ST2]
| exact PF2 | exact ERR2 | exact OUTR2 | exact SSP2 | exact SP2 | exact LSH2 | exact BITS2 | exact OSR2 | exact SY2 | exact DEC2 | exact Hk].
Qed.

Lemma h_CB4_C4 : forall segs m A pre bs post, rw_cells segs m A (pre ++ CB 4 bs :: post) ->
exists w : word, rw_cells segs m A (pre ++ C4 w :: post).
Proof.
intros segs m A pre bs post H.
assert (WF : cells_wf (pre ++ CB 4 bs :: post)) by (destruct H as [[Hwf _] _]; exact Hwf).
assert (L : length bs = 4%nat).
{ clear - WF. induction pre as [|c pre IH]; cbn in WF; [exact (proj1 WF)| exact (IH (proj2 WF))]. }
destruct (bytes_are_f32 1 bs L) as (ws & Lw & E). destruct ws as [|w [|? ?]]; try discriminate Lw. exists w.
eapply rw_cells_recast; [exact H | |].
- clear - WF. induction pre as [|c pre IH]; cbn in WF |- *; [split; [exact I| exact (proj2 WF)]| split; [exact (proj1 WF)| exact (IH (proj2 WF))]].
- rewrite !cells_bytes_app. f_equal. cbn [cells_bytes cbytes]. f_equal. rewrite f32_cons, f32_nil in E. cbn [cells_bytes cbytes] in E. rewrite app_nil_r in E. exact E.
Qed.

Lemma h_op_junk_cells : forall (m : mem) A Bd (o : packet) g kc', rw_cells asegs m A (op_cells Bd (Some o) g kc') -> exists opc, op_junk opc /\ rw_cells asegs m A opc.
Proof using.
intros m A Bd o g kc' H. cbn [op_cells] in H.
exists [CB 8 (le8 (wz (Bd + pk_off o))); CB 8 (le8 (wz (pk_bytes o))); CB 8 (le8 (wz (pk_b_o_s o))); CB 8 (le8 (wz (pk_e_o_s o)));
CB 8 (le8 g); CB 8 (le8 (wz (pk_packetno o)))].
split; [do 6 eexists; reflexivity|].
eapply rw_cells_recast; [exact H| cbn [cells_wf cell_wf]; repeat split; apply length_le8| reflexivity].
Qed.

Lemma nodup_of_disj : forall L : list (Z * Z),
(forall l1 p n l2, L = l1 ++ (p, n) :: l2 -> forall e, In e (l1 ++ l2) -> p + n <= fst e \/ fst e + snd e <= p) ->
(forall e, In e L -> 0 < snd e) -> List.NoDup (map fst L).
Proof using.
induction L as [|[p n] L IH]; intros HD HP; [constructor|]. cbn [map]. constructor.
- intros Hin. apply in_map_iff in Hin as ([p' n'] & Ee & He). cbn [fst] in Ee. subst p'.
pose proof (HP (p, n) (or_introl eq_refl)) as P1. pose proof (HP (p, n') (or_intror He)) as P2. cbn [snd] in P1, P2.
destruct (HD [] p n L eq_refl (p, n') He) as [D|D]; cbn [fst snd] in D; lia.
- apply IH; [| intros e He; exact (HP e (or_intror He))].
intros l1 p1 n1 l2 E e He. apply (HD ((p, n) :: l1) p1 n1 l2); [rewrite E; reflexivity|]. right. exact He.
Qed.
Lemma live_nodup_pos : forall (Σ : rts RT) (m : mem), ART RT Σ m -> (forall e, In e (rt_live RT Σ) -> 0 < snd e) -> List.NoDup (map fst (rt_live RT Σ)).
Proof using AF.
intros Σ m ART0 HP. apply nodup_of_disj; [| exact HP].
intros l1 p n l2 E [p' n'] He. cbn [fst snd]. exact (af_live_disj RT AF Σ m p n p' n' l1 l2 ART0 E He).
Qed.

Section HP.
Variables (h : hstate unit) (op : packet) (pno nbr brem0 : Z) (a : haux) (Σ1 : rts RT) (m0 : mem) (j0 j192 j200 gw : word) (ogc kc : list cell).
Hypothesis HS1 : hsig RT X Σ1 a h.
Hypothesis HIT : h_iter X h nbr brem0.
Hypothesis SI1 : h_stream_init h = 1.
Hypothesis EOS0 : h_eos h = 0.
Hypothesis PC0 : h_packet_count h = 0.
Hypothesis PN0 : 0 <= pno.
Hypothesis HR0 : hrep RT OUT_rep ERR_rep IO_FP X Σ1 m0 a h
(h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h)) (Z64 (h_speex_serialno h)) j0 j192 j200 h) ogc (op_cells (a_Bd a) (Some op) gw kc).
Hypothesis OGJ : og_junk ogc.
Hypothesis KCS : cells_size kc = 48%nat.
Hypothesis PKB : 0 <= pk_off op /\ 0 <= pk_bytes op /\ pk_off op + pk_bytes op <= os_body_fill (h_os h).
Hypothesis BUD : h_packet_count h + 1 + (os_lacing_fill (h_os h) - os_lacing_returned (h_os h)) <= 162 * h_consumed X h.

Variable m2 : mem.
Hypothesis PF02 : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 (W_h ++ IO_FP) m0 m2.
Hypothesis PFR2 : rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) mR m2.
Hypothesis ERR2 : ERR_rep m2.
Hypothesis OUT2 : forall so, OUT_rep so mR -> OUT_rep so m2.
Hypothesis SSP2 : io_ssp m2.

Lemma hp_hsep : hsep X a h.
Proof using AF HX HS1 HR0. destruct HR0 as (ART0 & _). exact (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m0 a h ART0 HS1). Qed.

Lemma hp_fz : forall (m : mem), drv_consts m -> rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 W_h m2 m ->
rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) mR m /\ ERR_rep m /\ (forall so, OUT_rep so mR -> OUT_rep so m) /\ io_ssp m
/\ (exists ows, rw_cells asegs m (F + HO_OUT) (f32 ows) /\ length ows = 2000%nat)
/\ bits_rep asegs m (F + HO_BITS) (a_Dc a) (h_bits h) /\ sync_rep m (F + HO_OY) (a_Dsy a) (h_oy h) (a_sybytes a)
/\ rw_cells asegs m (F + HO_OG) ogc /\ rw_cells asegs m (F + HO_OP) (op_cells (a_Bd a) (Some op) gw kc)
/\ h_os_rep X m a h /\ (exists stb, rw_cells asegs m (F + HO_STEREO) [CB 24 stb]).
Proof using AF HX ERR_loc OUT_loc IO_img HS1 HR0 KCS OGJ PF02 PFR2 ERR2 OUT2 SSP2.
intros m DC PFA.
pose proof hp_hsep as HSP.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS1 as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ1 m2 m a h _ _ HSP PFA
ltac:(intros e He; rewrite EL; apply in_or_app; right; exact He) (fp_h_Wh a h) DC PFR2 ERR2 OUT2 SSP2) as (PF' & ERR' & OUTR' & SSP').
split; [exact PF'|]. split; [exact ERR'|]. split; [exact OUTR'|]. split; [exact SSP'|].
assert (PR : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 (W_h ++ IO_FP) m0 m).
{ apply (pres_fp_trans _ _ _ _ m0 m2 m PF02). apply (pres_fp_weaken _ _ _ W_h _ m2 m PFA). intros x Hx. apply outside_app_iff in Hx. exact (proj1 Hx). }
destruct HR0 as (ART0 & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC & OSR & (stb & STB)
& RATE & (wl & LOOK) & DEC & HP).
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
assert (ROF : forall A n, F <= A -> A + n <= F + 9168 + 24 -> (A + n <= F + 32 \/ F + 88 <= A) -> (A + n <= F + 8384 \/ F + 8388 <= A) ->
rng_out (W_h ++ IO_FP) A n).
{ intros A n H1 H2 H3 H4. apply rng_out_app; [| apply (rng_out_img IO_FP A n IO_img); right; lia].
unfold W_h. rng_out_tac ltac:(unfold RT_STACK, H_STACK, SH_LO, SH_HI in *; lia). }
assert (ROH : forall p q, In (p, q) (h_own a h) -> rng_out (W_h ++ IO_FP) p q).
{ intros p q Hin. destruct (proj1 HSP p q Hin) as (P0 & PL & PF8 & PS & PI & _). apply rng_out_app.
- unfold W_h. rng_out_tac ltac:(unfold RT_STACK, H_STACK, SH_LO, SH_HI in *; lia).
- apply (rng_out_img IO_FP p q IO_img). destruct PI as [PI|PI]; [left; exact PI| right; exact PI]. }
unfold HO_OUT, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO in *.
change (fs_size 8) with 16384 in *.
split; [exists ows; split; [| exact LOWS]; apply (htr_rw _ _ _ _ m0 m PR _ _ OUTB); rewrite ?cells_size_f32, ?LOWS;
[apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia| apply ROF; lia]|].
assert (BOK : bits_ok (h_bits h)) by (destruct HP as (_ & _ & _ & _ & B & _); exact B).
split; [apply (bits_rep_tr _ _ _ _ m0 m PR _ _ _ BITS BOK);
[apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia| apply ROF; lia|
apply (acl_live _ _ _ _ _ _ _ (INL _ (own_in_Dc a h))); lia| exact (ROH _ _ (own_in_Dc a h))]|].
split; [apply (sync_rep_tr _ _ _ _ m0 m PR _ _ _ _ SY);
[apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia| apply ROF; lia|
intros NS; split; [apply (acl_live _ _ _ _ _ _ _ (INL _ (own_in_Dsy a h NS))); unfold bptr in *; lia| exact (ROH _ _ (own_in_Dsy a h NS))]]|].
assert (OGS : cells_size ogc = 32%nat) by (destruct OGJ as (x1 & x2 & x3 & x4 & ->); reflexivity).
split; [apply (htr_rw _ _ _ _ m0 m PR _ _ OGC); rewrite ?OGS; [apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia| apply ROF; lia]|].
assert (OPS : cells_size (op_cells (a_Bd a) (Some op) gw kc) = 48%nat) by (unfold op_cells; cbn [cells_size csize app]; rewrite ?cells_size_app, ?KCS; reflexivity).
split; [apply (htr_rw _ _ _ _ m0 m PR _ _ OPC); rewrite ?OPS; [apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia| apply ROF; lia]|].
split; [apply (h_os_rep_tr _ _ _ _ m0 m PR X a h OSR);
[apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia| unfold HO_OS; apply ROF; lia|
intros NE; destruct (own_in_os a h NE) as (IB & IL & IG);
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IB)); lia|]; split; [exact (ROH _ _ IB)|];
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IL)); lia|]; split; [exact (ROH _ _ IL)|];
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IG)); lia| exact (ROH _ _ IG)]]|].
exists stb. apply (htr_rw _ _ _ _ m0 m PR _ _ STB); cbn [cells_size csize Nat.add]; [apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia| apply ROF; lia].
Qed.

Lemma hp_st_none : h_st h = None.
Proof using HR0 PC0.
destruct HR0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP).
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M & _).
destruct (h_st h); [exfalso; exact (M PC0)| reflexivity].
Qed.

Lemma hp_kh_ok : forall (Σ : rts RT) (m : mem) (c : config) (D : Z) (d5 : dec_state bptr) (LBD : list block) (NEW : list (Z * Z))
(nf ch rate ex fs : Z) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 t3 t4 t5 t6 : word) Fr fc,
ASTA RT Σ PMh (eq (MS (mkR ra (Z64 S1) (x_gp X) (Z64 0x630458) t0 t1 t2 (Z64 usp) (Z64 S1) a0 a1 a2 a3 a4 a5 a6 a7
(Z64 (F + HO_OP)) (Z64 sf) (Z64 (F + HO_OUT)) s5 (Z64 1) s7 (Z64 (1 + ex)) (Z64 D) (Z64 (F + HO_OG)) (Z64 (F + HO_BITS))
t3 t4 t5 t6) Fr (Z64 A_KH) fc None m (seg_rom asegs))) c ->
X1cn.frm0 fc ->
rt_live RT Σ = NEW ++ a_P a ++ x_live X -> rt_frames RT Σ = [(F, 8%nat)] -> rt_sp0 RT Σ = x_sp0 X -> rt_pois RT Σ = [] ->
x_cr0 X - h_cost h - 160 <= rt_credit RT Σ ->
Permutation NEW (blocks_live LBD) -> List.NoDup (map blk_id LBD) -> blocks_al8 LBD -> (length LBD <= 19)%nat ->
ART RT Σ m -> mem_inv asegs m -> stk asegs m lo S1 ->
rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 W_h m2 m ->
rw_cells asegs m S1 (h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h)) (Z64 (h_speex_serialno h)) j0 j192 j200
(incr_packet_count (set_header h d5 nf ch rate ex fs))) ->
rw_cells asegs m sf [CB 16 HSH_P1] ->
(exists je, rw_cells asegs m (F + HO_ENH) [CB 56 je]) ->
rw_cells asegs m (F + HO_FSZ) [C4 (Z64 fs)] -> rw_cells asegs m (F + HO_RATE) [C4 (Z64 rate)] -> (exists wl, rw_cells asegs m (F + HO_LOOK) [C4 wl]) ->
DREP (F + HO_OUT) (F + HO_STEREO) m D d5 LBD -> 0 < D ->
(dec_depth d5 <= 3)%nat -> isave_ok d5 -> dec_nestedR d5 ->
0 <= fs <= 640 -> 1 <= nf <= 10 -> -2^31 <= ch < 2^31 -> -2^31 <= rate < 2^31 -> -2^31 <= ex < 2^31 - 1 ->
at_KH RT OUT_rep ERR_rep IO_FP X F0 fs0 (incr_packet_count (set_header h d5 nf ch rate ex fs)) pno nbr brem0 c.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV HS1 HIT SI1 EOS0 PC0 PN0 HR0 OGJ KCS PKB BUD PF02 PFR2 ERR2 OUT2 SSP2.
intros Σ m c D d5 LBD NEW nf ch rate ex fs ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 t3 t4 t5 t6 Fr fc
Hc FRM EL EF ESP EPO ECR PNEW NDB AL8 LB19 ART0 MI ST PFA SP LSH ENH FSZ RATE LOOK DR D0 DD ISV NST FSR NFR CHR RTR EXR.
destruct (hp_fz m (AF_DRV _ _ ART0) PFA) as (PF & ERR & OUTR & SSP & OUTB & BITS & SY & OGC & OPC & OSR & STB).
destruct (h_op_junk_cells m _ _ _ _ _ OPC) as (opc & OPJ & OPC').
pose proof HS1 as (EL1 & ND1 & PERM1 & EF1 & ESP1 & EPO1 & ECR1).
pose proof HR0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OSR0 & _ & _ & _ & DEC0 & HP0).
pose proof hp_st_none as STN.
pose proof (own_pos_h m0 a h OSR0 DEC0 HP0) as OPOS.
set (a' := HA (a_Dsy a) (a_sybytes a) (a_Bd a) (a_L a) (a_G a) (a_shdr a) (a_body a) (a_lws a) (a_gws a) (a_Dc a) D LBD (NEW ++ a_P a)).
set (h' := incr_packet_count (set_header h d5 nf ch rate ex fs)).
assert (EOWN : h_own a' h' = blocks_live LBD ++ h_own a h).
{ unfold h_own at 2. rewrite STN. cbn [app]. reflexivity. }
assert (BPOS : forall e, In e NEW -> 0 < snd e).
{ intros e He. apply (Permutation_in _ PNEW) in He. unfold blocks_live in He. apply in_map_iff in He as (b & <- & Hb). cbn [snd].
exact (h_drep_sizes_pos d5 _ _ m _ _ DR b Hb). }
assert (NDL : List.NoDup (map fst (rt_live RT Σ))).
{ apply (live_nodup_pos Σ m ART0). rewrite EL. intros e He. apply in_app_or in He as [He|He]; [exact (BPOS e He)|].
apply in_app_or in He as [He|He]; [destruct e as [p q]; exact (OPOS p q (Permutation_in _ PERM1 He))| destruct e as [p q]; exact (proj1 (hi_live _ _ _ HX) p q He)]. }
assert (ND' : List.NoDup (map fst (NEW ++ a_P a))).
{ rewrite EL, app_assoc, map_app in NDL. exact (NoDup_app_remove_r _ _ NDL). }
unfold at_KH.
exists Σ, a', Fr, fc, m, ra, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, s5, s7, t3, t4, t5, t6, j0, j192, j200, ogc, opc.
split.
{ unfold h_regs. replace (h_packet_count h') with 1 by (unfold h'; cbn [incr_packet_count set_header h_packet_count]; lia). exact Hc. }
split; [exact FRM|].
split.
{ unfold hsig. split; [cbn [a_P a']; rewrite EL, app_assoc; reflexivity|]. split; [exact ND'|].
split; [rewrite EOWN; cbn [a_P a']; apply Permutation_app; [exact PNEW| exact PERM1]|].
split; [exact EF|]. split; [exact ESP|]. split; [exact EPO|].
unfold h_cost, H_HDR_CREDIT, H_DEC_CREDIT in *. unfold h'. cbn [incr_packet_count set_header h_packet_count]. rewrite PC0 in *. lia. }
split; [unfold h_iter in *; exact HIT|].
split; [exact SI1|]. split; [exact EOS0|]. split; [exact PN0|].
split.
2: { split; [exact OGJ| exact OPJ]. }
unfold hrep.
split; [exact ART0|]. split; [exact MI|]. split; [exact ST|]. split; [exact PF|]. split; [exact ERR|]. split; [exact OUTR|]. split; [exact SSP|].
split; [exact SP|]. split; [exact LSH|]. split; [exact ENH|]. split; [exact OUTB|]. split; [exact FSZ|]. split; [exact BITS|]. split; [exact SY|].
split; [exact OGC|]. split; [exact OPC'|]. split; [exact OSR|]. split; [exact STB|]. split; [exact RATE|]. split; [exact LOOK|].
split.
{ unfold h_dec_rep. cbn [h' incr_packet_count set_header h_st a' a_S a_LBD a_Dc].
split; [exact DR|]. split; [exact D0|]. split; [exact DD|]. split; [exact ISV|]. split; [exact NST|]. split; [exact NDB|]. split; [exact AL8|].
split; [| exact LB19].
intros b Hb E.
assert (INN : In (blk_addr b, blk_size b) NEW) by (apply (Permutation_in _ (Permutation_sym PNEW)); unfold blocks_live; exact (in_map _ _ _ Hb)).
assert (INDc : In (a_Dc a, sb_buf_size (h_bits h)) (a_P a)) by exact (Permutation_in _ (Permutation_sym PERM1) (own_in_Dc a h)).
rewrite map_app in ND'. apply (nodup_app_disj _ _ (blk_addr b) ND'); [exact (in_map fst _ _ INN)| rewrite E; exact (in_map fst _ _ INDc)]. }
pose proof OSR0 as OSR0'. unfold h_os_rep in OSR0'. rewrite SI1 in OSR0'. cbn [Z.eqb] in OSR0'.
destruct OSR0' as (_ & _ & _ & _ & (SI_a & SI_b & _) & _).
apply hpure_hdr; [exact HP0| exact PC0| exact FSR| exact NFR| exact CHR| exact RTR| exact EXR| rewrite PC0 in BUD; lia| lia].
Qed.

Hypothesis CTL : forall d, ctl_cps_at RT d.

Lemma hp_ctl : forall (Σ : rts RT) (m : mem) (cc : config) T (d : dec_state bptr) (D : Z) (LBD : list block) (r : ctl_req) (P : Z)
(ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc,
ASTA RT Σ PMh (eq (MS (mkR ra (Z64 S1) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z64 A_ctl_h) fc None m (seg_rom asegs))) cc ->
a0 = Z64 D -> a1 = Z64 (ctl_req_code r) -> a2 = Z64 P -> tp = Z64 0x630458 ->
X1cn.frm0 fc -> rt_frames RT Σ = [(F, 8%nat)] -> rt_sp0 RT Σ = x_sp0 X -> 3 <= rt_credit RT Σ ->
creq_grp1 r = true -> DREP (F + HO_OUT) (F + HO_STEREO) m D d LBD -> (dec_depth d <= 3)%nat -> List.NoDup (map blk_id LBD) ->
(forall b, In b LBD -> In (blk_addr b, blk_size b) (rt_live RT Σ)) ->
creq_ok (F + HO_OUT) P r -> creq_pre (F + HO_STEREO) m D d P r ->
F <= P -> P + creq_size r <= F + 16376 -> acc asegs m P (creq_size r) -> P mod creq_align r = 0 ->
ART RT Σ m -> mem_inv asegs m -> stk asegs m lo S1 ->
(forall (Σ' : rts RT) (m' : mem) (c' : config) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) Fr' fc',
ASTA RT Σ' PMh (eq (MS (mkR ra (Z64 S1) gp tp t0' t1' t2' s0 s1 (Z64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
Fr' (ret_pc ra) fc' None m' (seg_rom asegs))) c' ->
X1cn.frm0 fc' ->
rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_pois RT Σ' = rt_pois RT Σ ->
rt_credit RT Σ - 2 <= rt_credit RT Σ' <= rt_credit RT Σ ->
ART RT Σ' m' -> mem_inv asegs m' -> stk asegs m' lo S1 ->
rt_pres_fp (rt_live RT Σ) [(F, 8%nat)] S1 ((P, P + creq_size r) :: blocks_ivs LBD) m m' ->
DREP (F + HO_OUT) (F + HO_STEREO) m' D (snd (speex_decoder_ctl d r)) LBD -> creq_post (F + HO_STEREO) m' P r (fst (speex_decoder_ctl d r)) ->
acc asegs m' P (creq_size r) ->
realizes asegs c' T) ->
realizes asegs cc T.
Proof.
intros Σ m cc T d D LBD r P ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc
Hc E0 E1 E2 ETP FRM EF ESP CR G1 DR DD NDB INB OK PRE P0 P1 ACC PAL ART0 MI ST K.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
assert (INF : In (F, 8%nat) (rt_frames RT Σ)) by (rewrite EF; left; reflexivity).
assert (CST : ctl_stack d <= 96 * 2 + NBCTL_STACK).
{ destruct d as [st|s low]; cbn [ctl_stack dec_depth] in *; [lia|]. destruct low as [st|s' low']; cbn [ctl_stack dec_depth] in *; [lia|].
destruct low' as [st|s'' low'']; cbn [ctl_stack dec_depth] in *; [lia|]. destruct low''; cbn [dec_depth] in DD; lia. }
unfold A_ctl_h in Hc. change 0x98638 with A_speex_decoder_ctl in Hc.
Time cps_rt (CTL d Σ PMh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m (F + HO_OUT) (F + HO_STEREO) D LBD r P lo F 8%nat).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ change (fs_size 8) with 16384. lia. }
{ rewrite EF. cbn [length]. unfold FRAMES_MAX. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). exact ST. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold NBCTL_STACK, RT_STACK in *. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). exact S32. }
intros c' (Σ' & Hc' & EL' & EF' & ES' & EC' & EP'). clear Hc.
Time cps_unpack_lib Hc' as (m' & RS & RA & PR & DR' & POST & ACC').
destruct RA as (ART' & MI' & WM' & ST').
assert (IV : creq_ivs P r = [(P, P + creq_size r)]) by (destruct r; try discriminate G1; reflexivity).
rewrite IV, EF in PR. cbn [app] in PR.
eapply K; [exact Hc | exact RS | exact EL' | exact EF' | exact ES' | exact EP' | | exact ART' | exact MI'
| first [exact ST' | rewrite unsigned_lit in ST' by (unfold USTACK_TOP in *; lia); exact ST'] | exact PR | exact DR' | exact POST | exact ACC'].
destruct (dec_depth d) as [|[|[|[|?]]]]; cbn [Z.of_nat] in EC'; lia.
Qed.

Definition iv_hp (L : list (Z * Z)) (lo' hi' : Z) : Prop :=
hi' <= lo' \/ (exists l h', In (l, h') W_h /\ l <= lo' /\ hi' <= h') \/ (exists p n, In (p, n) L /\ p <= lo' /\ hi' <= p + n).
Lemma hp_acc : forall (Σ : rts RT) (m m' : mem) (L W : list (Z * Z)),
ART RT Σ m -> rt_live RT Σ = L ++ rt_live RT Σ1 -> rt_frames RT Σ = [(F, 8%nat)] -> rt_sp0 RT Σ = x_sp0 X ->
rt_pres_fp (rt_live RT Σ) [(F, 8%nat)] S1 W m m' -> (forall lo' hi', In (lo', hi') W -> iv_hp L lo' hi') ->
rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 W_h m m'.
Proof.
intros Σ m m' L W ART0 EL EF ES PR HW b Hb Ho. apply PR.
- apply (aclient_mono _ _ _ (rt_live RT Σ) [(F, 8%nat)] S1 _ Hb); [intros e He; rewrite EL; apply in_or_app; right; exact He| intros e He; exact He| lia].
- apply outside_intro. intros l hh Hin Hx. destruct (HW l hh Hin) as [E|[(l' & h'' & Hw & L1 & L2)|(p & n & Hp & P1 & P2)]].
+ lia.
+ revert Ho. generalize W_h Hw. intros W' Hw'. clear - Hw' L1 L2 Hx. induction W' as [|[x y] W' IH]; [destruct Hw'|].
cbn [outside]. intros (O1 & O2). destruct Hw' as [E|Hw']; [injection E as <- <-; lia| exact (IH Hw' O2)].
+ exact (new_not_client Σ m L (rt_live RT Σ1) p n (bv_unsigned b) ART0 EL EF ES Hp ltac:(lia) Hb).
Qed.
Lemma iv_hp_wh : forall L l h', In (l, h') W_h -> iv_hp L l h'.
Proof. intros L l h' H. right; left. exists l, h'. split; [exact H| lia]. Qed.
Lemma iv_hp_blocks : forall (L : list (Z * Z)) (LBD : list block) lo' hi', (forall b, In b LBD -> In (blk_addr b, blk_size b) L) ->
In (lo', hi') (blocks_ivs LBD) -> iv_hp L lo' hi'.
Proof.
intros L LBD lo' hi' HB Hin. unfold blocks_ivs in Hin. apply in_map_iff in Hin as (b & E & Hb). injection E as <- <-.
right; right. exists (blk_addr b), (blk_size b). split; [exact (HB b Hb)| lia].
Qed.

Lemma drep_tr : forall (L : list (Z * Z)) fr sp W (m m' : mem) OUT STEREO S (d : dec_state bptr) LBD,
rt_pres_fp L fr sp W m m' -> DREP OUT STEREO m S d LBD ->
(forall b, In b LBD -> acl_rng L fr sp (blk_addr b) (blk_size b) /\ rng_out W (blk_addr b) (blk_size b)) -> DREP OUT STEREO m' S d LBD.
Proof.
intros L fr sp W m m' OUT STEREO S d LBD PR R HB.
eapply decst_rep_agree; [exact R|].
intros x Hx (b & Hb & Hab). destruct (HB b Hb) as (HA & HO).
assert (E : m' (wa x) = m (wa x)) by (apply PR; rewrite wa_unsigned by lia; [apply HA; lia| apply HO; lia]).
split; [exact E|]. rewrite (wview_agree asegs m m' _ E). tauto.
Qed.

Lemma c4_mod32 : forall v, bv_unsigned (Z64 v) mod 2^32 = v mod 2^32.
Proof. intros v. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). apply Z.mod_mod_divide. exists (2^32). reflexivity. Qed.

Lemma c4_eqm : forall (m : mem) A (w : word) v, rw_cells asegs m A [C4 w] -> bv_unsigned w mod 2^32 = v mod 2^32 -> rw_cells asegs m A [C4 (Z64 v)].
Proof.
intros m A w v H E. eapply rw_cells_recast; [exact H| cbn; tauto|]. cbn [cells_bytes cbytes].
replace (le4 w) with (le4 (Z64 (bv_unsigned w))) by (rewrite Z_to_bv_bv_unsigned; reflexivity).
f_equal. first [apply le4_lit_eqm; rewrite E; reflexivity | apply le4_lit_eqm; symmetry; exact E].
Qed.

Definition blk_sep (v : Z) (LBD : list block) : Prop :=
forall b, In b LBD -> 0 < blk_size b /\ blk_addr b + blk_size b <= lo /\ (blk_addr b + blk_size b <= F \/ F + 16384 <= blk_addr b)
/\ (blk_addr b + blk_size b <= sf \/ sf + 2048 <= blk_addr b) /\ (blk_addr b + blk_size b <= v \/ v + 80 <= blk_addr b).

Lemma rng_out_bsep : forall v LBD A n, blk_sep v LBD ->
((F <= A /\ A + n <= F + 16384) \/ (sf <= A /\ A + n <= sf + 2048) \/ lo <= A \/ (v <= A /\ A + n <= v + 80)) -> rng_out (blocks_ivs LBD) A n.
Proof.
intros v LBD A n HB HA. apply rng_out_blocks. intros b Hb. destruct (HB b Hb) as (B0 & B1 & B2 & B3 & B4). lia.
Qed.

Ltac hp_acl := first
[ apply acl_stack; unfold USTACK_TOP in *; lia
| apply (acl_frame _ [(x_F X, 8%nat)] _ (x_F X) 8 _ _ (or_introl eq_refl)); change (fs_size 8) with 16384; lia
| apply (acl_fshadow _ [(x_F X, 8%nat)] _ (x_F X) 8 _ _ (or_introl eq_refl)); change (fs_size 8) with 16384; lia
| match goal with H : In (?p, ?q) ?L |- acl_rng ?L _ _ _ _ => apply (acl_live _ _ _ p q _ _ H); lia end ].
Ltac hp_rng := repeat (first [ apply rng_out_nil | apply rng_out_cons; [unfold SH_LO, SH_HI in *; lia|]
| eapply rng_out_bsep; [eassumption| unfold SH_LO, SH_HI in *; lia] ]).
Ltac hp_tr PR H := eapply (htr_rw _ _ _ _ _ _ PR) in H; cbn [cells_size csize Nat.add] in H |- *; [| hp_acl | hp_rng].

Lemma hp_ai : forall (Σ : rts RT) (m : mem) (cc : config) T (hd : spx_header) (v D : Z) (junk28 : list byte) (w1 w2 w3 r1 r2 : word)
(LBD : list block) (NEW : list (Z * Z)) (j12 j16 : list byte) (c48 c52 c56 c64 wl : word)
(t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 t5 t6 : word) Fr fc,
ASTA RT Σ PMh (eq (MS (mkR (Z64 0x96f2c) (Z64 S1) (x_gp X) (Z64 0x630458) t0 t1 t2 (Z64 usp) (Z64 S1) (Z64 D) a1 a2 a3 a4 a5 a6 a7
(Z64 (F + HO_OP)) (Z64 sf) (Z64 (F + HO_OUT)) (Z64 v) (Z64 SHB) (Z64 (F + HO_OS)) (Z64 (F + 32)) s9 (Z64 (F + HO_OG))
(Z64 (F + HO_BITS)) t3 t4 t5 t6) Fr (ret_pc (Z64 0x96f2c)) fc None m (seg_rom asegs))) cc ->
X1cn.frm0 fc ->
rt_live RT Σ = NEW ++ (v, 80) :: rt_live RT Σ1 -> rt_frames RT Σ = [(F, 8%nat)] -> rt_sp0 RT Σ = x_sp0 X -> rt_pois RT Σ = [] ->
rt_credit RT Σ1 - 4 <= rt_credit RT Σ ->
Permutation NEW (blocks_live LBD) -> List.NoDup (map blk_id LBD) -> blocks_al8 LBD -> Z.of_nat (length NEW) = init_nblocks (mode_of_id (hd_mode hd)) ->
DREP (F + HO_OUT) (F + HO_STEREO) m D (init_dec (mode_of_id (hd_mode hd))) LBD ->
0 < v -> v mod 16 = 0 -> rw_cells asegs m v (spx_header_cells junk28 hd w1 w2 w3 r1 r2) ->
-2^31 <= hd_rate hd < 2^31 -> 1 <= hd_nb_channels hd <= 2 -> -2^31 <= hd_frames_per_packet hd < 2^31 -> -2^31 <= hd_extra_headers hd < 2^31 ->
hd_speex_version_id hd <= 1 -> hd_mode_bitstream_version hd = 4 -> 0 <= hd_mode hd < 3 ->
ART RT Σ m -> mem_inv asegs m -> stk asegs m lo S1 ->
rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 W_h m2 m ->
rw_cells asegs m S1 (h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h)) (Z64 (h_speex_serialno h)) j0 j192 j200 h) ->
rw_cells asegs m sf [CB 16 HSH_L_HDR] ->
rw_cells asegs m (F + 32) [C4 (Z64 1)] -> rw_cells asegs m (F + 36) [CB 12 j12] -> rw_cells asegs m (F + 48) [C4 c48; C4 c52; C8 c56; C8 c64] ->
rw_cells asegs m (F + 72) [CB 16 j16] ->
rw_cells asegs m (F + HO_FSZ) [C4 (Z64 (h_frame_size h))] -> rw_cells asegs m (F + HO_RATE) [C4 (Z64 (h_rate h))] -> rw_cells asegs m (F + HO_LOOK) [C4 wl] ->
(forall c', match hdr_tail h hd with
| None => at_XT RT OUT_rep ERR_rep IO_FP X F0 fs0 c'
| Some h3 => at_KH RT OUT_rep ERR_rep IO_FP X F0 fs0 (incr_packet_count h3) pno nbr brem0 c'
end -> realizes asegs c' T) ->
realizes asegs cc T.
Proof.
intros Σ m cc T hd v D junk28 w1 w2 w3 r1 r2 LBD NEW j12 j16 c48 c52 c56 c64 wl t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 t5 t6 Fr fc
Hc FRM EL EF ESP EPO ECR PNEW NDB AL8 LNEW DR V0 V16 HC HRR HNC HFP HEX HVV HBV HM ART0 MI ST PFA SP LSH ENH J12 CBK J16 FSZ RATE LOOK Hk.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS1 as (EL1 & ND1 & PERM1 & EF1 & ESP1 & EPO1 & ECR1).
pose proof HR0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OSR0 & _ & _ & _ & DEC0 & HP0).
pose proof hp_st_none as STN.
pose proof hp_hsep as HSP.

unfold hdr_tail in Hk. replace (1 <? hd_speex_version_id hd) with false in Hk by (symmetry; apply Z.ltb_ge; lia).
rewrite HBV in Hk. cbn [Z.eqb negb] in Hk. cbv zeta in Hk.
set (mo := mode_of_id (hd_mode hd)) in *.

assert (INB : forall b, In b LBD -> In (blk_addr b, blk_size b) NEW).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym PNEW)). unfold blocks_live. exact (in_map (fun b => (blk_addr b, blk_size b)) _ _ Hb). }
assert (INBL : forall b, In b LBD -> In (blk_addr b, blk_size b) (rt_live RT Σ)) by (intros b Hb; rewrite EL; apply in_or_app; left; exact (INB b Hb)).
assert (INV : In (v, 80) (rt_live RT Σ)) by (rewrite EL; apply in_or_app; right; left; reflexivity).
assert (BSEP : blk_sep v LBD).
{ intros b Hb. pose proof (h_drep_sizes_pos _ _ _ m _ _ DR b Hb) as BP. pose proof (INBL b Hb) as Hl.
destruct (af_live_range RT AF Σ m _ _ ART0 Hl) as (P0 & P1 & P2). rewrite ESP in P1.
assert (INF : In (F, 8%nat) (rt_frames RT Σ)) by (rewrite EF; left; reflexivity).
destruct (af_frames_range RT AF Σ m F 8 ART0 INF) as (_ & _ & _ & FR).
destruct (af_fshadow_apart RT AF Σ m F 8 ART0 INF) as (FSH & _).
change (fs_size 8) with 16384 in FR, FSH. rewrite <- ESF, ESF2 in FSH.
pose proof (hi_lo _ _ _ HX) as (LW0 & _).
split; [exact BP|]. split; [lia|]. split; [destruct (FR _ _ Hl); lia|]. split; [destruct (FSH _ _ Hl); lia|].
destruct (live_apart_app Σ m NEW ((v, 80) :: rt_live RT Σ1) _ _ ART0 EL (INB b Hb) (or_introl eq_refl)) as [A|A]; cbn [fst snd] in A; lia. }

assert (CRS : 100 <= rt_credit RT Σ).
{ pose proof (hi_cr _ _ _ HX) as FC. unfold h_cost, H_HDR_CREDIT, H_DEC_CREDIT, FUZZ_COST in *. rewrite PC0 in ECR1. lia. }
destruct (drep_head _ _ _ _ _ _ DR) as (nD & IND & ND0 & D8).
pose proof (INBL _ IND) as INDL. cbn [blk_addr blk_size] in INDL.
destruct (af_live_range RT AF Σ m _ _ ART0 INDL) as (DP0 & DL & _). cbn [blk_addr blk_size fst snd] in DP0, DL.
pose proof (af_sp0_range RT AF Σ m ART0) as (SPA & SPB). rewrite ESP in DL, SPA, SPB.
assert (LB : bytes_at asegs m (shad F) HSH_L_HDR) by (destruct LSH as [[_ B] _]; cbn [cells_bytes cbytes] in B; rewrite app_nil_r in B; rewrite <- ESF; exact B).
destruct (hsh_L_hdr_acc m F ltac:(clear - F64; Z.div_mod_to_equations; lia) ltac:(lia) LB) as (ACE & ACB). clear LB.
unfold HO_ENH, HO_CBK in ACE, ACB.

refine (rz_evt RT AF Σ PMh _ _ T cc (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply hp_w4; [reflexivity | unfold STACK_WIN, USTACK_TOP in *; lia | exact MI]. }
intros ms1 cc1 -> Hc1. clear Hc.
eapply (hp_ctl Σ m cc1 T (init_dec mo) D LBD (CtlSetEnh 1) (F + 32));
[exact Hc1 | reflexivity | reflexivity | reflexivity | reflexivity | exact FRM | exact EF | exact ESP | lia | reflexivity | exact DR
| pose proof (depth_init mo); exact H | exact NDB | exact INBL | right; reflexivity
| exists (Z64 1); split; [exact ENH| rewrite unsigned_lit by lia; split; [reflexivity| lia]]
| lia | cbn [creq_size]; lia | exact ACE | cbn [creq_align]; clear - F64; Z.div_mod_to_equations; lia | exact ART0 | exact MI | exact ST | ].
intros Σ2 m3 cc2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Fr2 fc2 Hc2 FRM2 EL2 EF2 ES2 EP2 EC2 ART2 MI2 ST2 PR DR2 POST ACC2.
clear Hc1.
cbn [creq_size] in PR.
assert (ELn : rt_live RT Σ = (NEW ++ [(v, 80)]) ++ rt_live RT Σ1) by (rewrite EL, <- app_assoc; reflexivity).
assert (INB' : forall b, In b LBD -> In (blk_addr b, blk_size b) (NEW ++ [(v, 80)])) by (intros b Hb; apply in_or_app; left; exact (INB b Hb)).
pose proof (pres_fp_trans _ _ _ _ m2 m m3 PFA (hp_acc Σ m m3 _ _ ART0 ELn EF ESP PR
ltac:(intros l hh [E|Hin]; [injection E as <- <-; right; left; exists (F + 32), (F + 88); split; [right; right; left; reflexivity| lia]
| exact (iv_hp_blocks _ LBD l hh INB' Hin)]))) as PFA3.
clear PFA.
unfold HO_FSZ, HO_RATE, HO_LOOK in FSZ, RATE, LOOK.
hp_tr PR LSH. hp_tr PR J12. hp_tr PR CBK. hp_tr PR J16. hp_tr PR FSZ. hp_tr PR RATE. hp_tr PR LOOK.
assert (HCS : cells_size (spx_header_cells junk28 hd w1 w2 w3 r1 r2) = 80%nat) by reflexivity.
assert (VSEP : v + 80 <= lo /\ (v + 80 <= F \/ F + 16384 <= v) /\ (v + 80 <= sf \/ sf + 2048 <= v)).
{ assert (INF : In (F, 8%nat) (rt_frames RT Σ)) by (rewrite EF; left; reflexivity).
destruct (af_live_range RT AF Σ m _ _ ART0 INV) as (_ & VL & _). rewrite ESP in VL.
destruct (af_frames_range RT AF Σ m F 8 ART0 INF) as (_ & _ & _ & FR).
destruct (af_fshadow_apart RT AF Σ m F 8 ART0 INF) as (FSH & _).
change (fs_size 8) with 16384 in FR, FSH. rewrite <- ESF, ESF2 in FSH.
pose proof (hi_lo _ _ _ HX) as (LW0 & _).
split; [lia|]. split; [destruct (FR _ _ INV); lia| destruct (FSH _ _ INV); lia]. }
eapply (htr_rw _ _ _ _ _ _ PR) in HC; rewrite ?HCS; [| hp_acl | hp_rng].
eapply (htr_rw _ _ _ _ _ _ PR) in SP; [| unfold h_spill; rewrite hsp_size; hp_acl | unfold h_spill; rewrite hsp_size; hp_rng].
clear PR.
destruct POST as (wenh & ENH2 & _). clear ENH.
rewrite <- EL2 in INBL, INV.

refine (rz_evt RT AF Σ2 PMh _ _ T cc2 (PMfd_mat_stable F0 fs0) Hc2 _ _).
{ eapply hp_w5; [reflexivity | unfold USTACK_TOP in *; lia | exact SP | exact MI2]. }
intros ms3 cc3 -> Hc3. clear Hc2.
destruct (hp_fz m3 (AF_DRV _ _ ART2) PFA3) as (PFR3 & _).
pose proof (h_acc_at OUT_rep IO_FP IO_img X HX m3 PFR3) as (_ & ACF & _). unfold HO_FSZ in ACF. clear PFR3.
eapply (hp_ctl Σ2 m3 cc3 T _ D LBD CtlGetFrameSize (F + 8384));
[exact Hc3 | reflexivity | reflexivity | reflexivity | reflexivity | exact FRM2 | rewrite EF2; exact EF | rewrite ES2; exact ESP | lia | reflexivity | exact DR2
| rewrite depth_ctl; exact (depth_init mo) | exact NDB | exact INBL | exact I
| exists (Z64 (h_frame_size h)); exact FSZ
| lia | cbn [creq_size]; lia | exact ACF | cbn [creq_align]; clear - F64; Z.div_mod_to_equations; lia | exact ART2 | exact MI2 | exact ST2 | ].
intros Σ3 m4 cc4 t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' Fr3 fc3 Hc4 FRM3 EL3 EF3 ES3 EP3 EC3 ART3 MI3 ST3 PR DR3 POST ACC3.
clear Hc3.
cbn [creq_size] in PR. destruct POST as (FSZ3 & FSR3).
set (fs := fst (speex_decoder_ctl (snd (speex_decoder_ctl (init_dec mo) (CtlSetEnh 1))) CtlGetFrameSize)) in *.
assert (ELn3 : rt_live RT Σ2 = (NEW ++ [(v, 80)]) ++ rt_live RT Σ1) by (rewrite EL2; exact ELn).
pose proof (pres_fp_trans _ _ _ _ m2 m3 m4 PFA3 (hp_acc Σ2 m3 m4 _ _ ART2 ELn3 ltac:(rewrite EF2; exact EF) ltac:(rewrite ES2; exact ESP) PR
ltac:(intros l hh [E|Hin]; [injection E as <- <-; right; left; exists (F + 8384), (F + 8388); split; [right; right; right; left; reflexivity| lia]
| exact (iv_hp_blocks _ LBD l hh INB' Hin)]))) as PFA4.
clear PFA3.
hp_tr PR LSH. hp_tr PR ENH2. hp_tr PR J12. hp_tr PR CBK. hp_tr PR J16. hp_tr PR RATE. hp_tr PR LOOK.
eapply (htr_rw _ _ _ _ _ _ PR) in HC; rewrite ?HCS; [| hp_acl | hp_rng].
eapply (htr_rw _ _ _ _ _ _ PR) in SP; [| unfold h_spill; rewrite hsp_size; hp_acl | unfold h_spill; rewrite hsp_size; hp_rng].
clear PR FSZ.
rewrite <- EL3 in INBL, INV.

pose proof (hi_F _ _ _ HX) as (_ & _ & _ & FSHX & _). change (fs_size 8) with 16384 in FSHX.
assert (AOV : aobj asegs m4 v 80).
{ split; [lia|]. split; [unfold APP_TOP; unfold USTACK_TOP in *; lia|]. exact (proj2 (af_acc_live RT AF Σ3 m4 _ _ ART3 INV)). }
assert (HPR : -2^31 <= h_rate h < 2^31) by (destruct HP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R & _); exact R).
refine (rz_evt RT AF Σ3 PMh _ _ T cc4 (PMfd_mat_stable F0 fs0) Hc4 _ _).
{ eapply hp_w6; [reflexivity | unfold USTACK_TOP in *; lia | lia | lia | exact FSHX | unfold SH_LO, SH_HI in *; lia | lia | clear - V16; Z.div_mod_to_equations; lia | lia
| reflexivity | exact FSR3 | exact HPR | exact HRR | exact FSZ3 | exact RATE | exact AOV | exact HC | exact SP | exact MI3]. }
intros ms5 cc5 (m5 & xa0 & xa1 & xa2 & MU5 & WM5 & MI5 & SP5 & POST5) Hc5. clear Hc4.
assert (ELn4 : rt_live RT Σ3 = (NEW ++ [(v, 80)]) ++ rt_live RT Σ1) by (rewrite EL3, EL2; exact ELn).
assert (EF4 : rt_frames RT Σ3 = [(F, 8%nat)]) by (rewrite EF3, EF2; exact EF).
assert (ES4 : rt_sp0 RT Σ3 = x_sp0 X) by (rewrite ES3, ES2; exact ESP).
pose proof (art_munch_h Σ3 m4 m5 _ ART3 EF4 ES4 MU5 WM5
ltac:(intros l hh [E|[E|[]]]; injection E as <- <-; [left; unfold USTACK_TOP in *; lia| right; right; lia])) as ART5.
assert (PR5 : rt_pres_fp (rt_live RT Σ3) [(F, 8%nat)] S1 [(S1, S1 + 216); (F + 9232, F + 9236)] m4 m5)
by (apply (pf_munch_h _ m4 m5 _ _ MU5); intros x Hx; exact Hx).
pose proof (pres_fp_trans _ _ _ _ m2 m4 m5 PFA4 (hp_acc Σ3 m4 m5 _ _ ART3 ELn4 EF4 ES4 PR5
ltac:(intros l hh [E|[E|[]]]; injection E as <- <-; apply iv_hp_wh;
[left; reflexivity| right; right; right; right; left; reflexivity]))) as PFA5.
clear PFA4.
assert (ST5 : stk asegs m5 lo S1).
{ apply (stk_agree asegs m4 m5 lo S1 ST3); [| exact WM5]. apply (agree_of_munch _ m4 m5 _ MU5). intros x Hx. cbn [outside].
split; [lia| split; [lia| exact I]]. }
hp_tr PR5 LSH. hp_tr PR5 ENH2. hp_tr PR5 J12. hp_tr PR5 CBK. hp_tr PR5 J16. hp_tr PR5 FSZ3. hp_tr PR5 LOOK.
eapply (htr_rw _ _ _ _ _ _ PR5) in HC; rewrite ?HCS; [| hp_acl | hp_rng].
assert (DR5 : DREP (F + HO_OUT) (F + HO_STEREO) m5 D (snd (speex_decoder_ctl (snd (speex_decoder_ctl (init_dec mo) (CtlSetEnh 1))) CtlGetFrameSize)) LBD).
{ apply (drep_tr _ _ _ _ m4 m5 _ _ _ _ _ PR5 DR3). intros b Hb. destruct (BSEP b Hb) as (B0 & B1 & B2 & B3 & B4).
split; [apply (acl_live _ _ _ _ _ _ _ (INBL b Hb)); lia| apply rng_out_cons; [lia| apply rng_out_cons; [lia| apply rng_out_nil]]]. }
clear PR5 DR3 ST3 MI3 MU5 WM5.
assert (CR3 : x_cr0 X - h_cost h - 8 <= rt_credit RT Σ3) by lia.
assert (KC64 : h_cost h + 64 <= FUZZ_COST - 1) by (unfold h_cost, H_HDR_CREDIT, H_DEC_CREDIT, FUZZ_COST; rewrite PC0; lia).
assert (HSX3 : hsig_x Σ3 a h 64 (NEW ++ [(v, 80)])).
{ split; [rewrite ELn4, EL1; reflexivity|]. split; [exact ND1|]. split; [exact PERM1|]. split; [exact EF4|]. split; [exact ES4|].
split; [rewrite EP3, EP2; exact EPO| lia]. }
assert (DEC5 : h_dec_rep X m5 a h) by (unfold h_dec_rep in *; rewrite STN in *; exact DEC0).
destruct POST5 as [(FB & ->) | (FG & RATE5 & ->)].
{
replace ((fs <? 0) || (640 <? fs)) with true in Hk
by (symmetry; destruct (Z.ltb_spec fs 0); [reflexivity|]; cbn [orb]; apply Z.ltb_lt; lia).
cbv iota in Hk.
destruct (hp_fz m5 (AF_DRV _ _ ART5) PFA5) as (PF5 & ERR5 & OUTR5 & SSP5 & _ & BITS5 & SY5 & _ & _ & OSR5 & _).
eapply (hp_f48_ok h a 64 v D _ LBD NEW Σ3 m5 cc5 T);
[exact Hc5 | exact FRM3 | exact HSX3 | exact KC64 | exact STN | exact SI1 | exact HP0 | exact PNEW | exact NDB | exact DR5
| rewrite !depth_ctl; exact (depth_init mo) | exact ART5 | exact MI5 | exact ST5 | exact PF5 | exact ERR5 | exact OUTR5 | exact SSP5
| exact SP5 | exact LSH | exact BITS5 | exact OSR5 | exact SY5 | exact DEC5 | exact Hk]. }

replace ((fs <? 0) || (640 <? fs)) with false in Hk by (symmetry; apply orb_false_intro; [apply Z.ltb_ge| apply Z.ltb_ge]; lia).
cbv iota in Hk.
set (rate := if h_rate h =? 0 then hd_rate hd else h_rate h) in *.
assert (RTR : -2^31 <= rate < 2^31) by (unfold rate; destruct (h_rate h =? 0); lia).
destruct (hp_fz m5 (AF_DRV _ _ ART5) PFA5) as (PFR5 & _).
pose proof (h_acc_at OUT_rep IO_FP IO_img X HX m5 PFR5) as (_ & _ & _ & _ & _ & _ & _ & _ & ACR & _). unfold HO_RATE in ACR. clear PFR5.
eapply (hp_ctl Σ3 m5 cc5 T _ D LBD (CtlSetSamplingRate rate) (F + 9232));
[exact Hc5 | reflexivity | reflexivity | reflexivity | reflexivity | exact FRM3 | exact EF4 | exact ES4 | lia | reflexivity | exact DR5
| rewrite !depth_ctl; exact (depth_init mo) | exact NDB | exact INBL | exact I
| exists (Z64 rate); split; [exact RATE5| split; [apply c4_mod32| exact RTR]]
| lia | cbn [creq_size]; lia | exact ACR | cbn [creq_align]; clear - F64; Z.div_mod_to_equations; lia | exact ART5 | exact MI5 | exact ST5 | ].
intros Σ4 m6 cc6 u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 Fr4 fc4 Hc6 FRM4 EL6 EF6 ES6 EP6 EC6 ART6 MI6 ST6 PR DR6 POST ACC6.
clear Hc5.
cbn [creq_size] in PR. destruct POST as (wr & RATE6 & WRM). apply (c4_eqm m6 _ wr rate) in RATE6; [| exact WRM]. clear RATE5.
assert (ELn5 : rt_live RT Σ3 = (NEW ++ [(v, 80)]) ++ rt_live RT Σ1) by exact ELn4.
pose proof (pres_fp_trans _ _ _ _ m2 m5 m6 PFA5 (hp_acc Σ3 m5 m6 _ _ ART5 ELn5 EF4 ES4 PR
ltac:(intros l hh [E|Hin]; [injection E as <- <-; right; left; exists (F + 9232), (F + 9236); split; [right; right; right; right; left; reflexivity| lia]
| exact (iv_hp_blocks _ LBD l hh INB' Hin)]))) as PFA6.
clear PFA5.
hp_tr PR LSH. hp_tr PR ENH2. hp_tr PR J12. hp_tr PR CBK. hp_tr PR J16. hp_tr PR FSZ3. hp_tr PR LOOK.
eapply (htr_rw _ _ _ _ _ _ PR) in HC; rewrite ?HCS; [| hp_acl | hp_rng].
eapply (htr_rw _ _ _ _ _ _ PR) in SP5; [| rewrite hsp_size; hp_acl | rewrite hsp_size; hp_rng].
clear PR.
rewrite <- EL6 in INBL, INV.

assert (HCR : -2^31 <= h_channels h < 2^31) by (destruct HP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R & _); exact R).
assert (AOV6 : aobj asegs m6 v 80).
{ split; [lia|]. split; [unfold APP_TOP; unfold USTACK_TOP in *; lia|]. exact (proj2 (af_acc_live RT AF Σ4 m6 _ _ ART6 INV)). }
refine (rz_evt RT AF Σ4 PMh _ _ T cc6 (PMfd_mat_stable F0 fs0) Hc6 _ _).
{ eapply hp_w7; [reflexivity | unfold USTACK_TOP in *; lia | exact FI | lia | exact FSHX | unfold SH_LO, SH_HI in *; lia | exact ESF
| unfold SH_LO, SH_HI in *; lia | exact F64 | lia | lia | lia | clear - V16; Z.div_mod_to_equations; lia | lia | reflexivity
| exact HFP | exact HCR | exact HNC | exact AOV6 | exact HC | exact SP5 | exact CBK | exact LSH | exact (AF_LIB _ _ ART6) | exact MI6]. }
intros ms7 cc7 (m7 & xb0 & xb1 & xb2 & MU7 & WM7 & MI7 & SP7 & LSH7 & POST7) Hc7. clear Hc6.
assert (EF7 : rt_frames RT Σ4 = [(F, 8%nat)]) by (rewrite EF6; exact EF4).
assert (ES7 : rt_sp0 RT Σ4 = x_sp0 X) by (rewrite ES6; exact ES4).
assert (ELn7 : rt_live RT Σ4 = (NEW ++ [(v, 80)]) ++ rt_live RT Σ1) by (rewrite EL6; exact ELn5).
pose proof (art_munch_h Σ4 m6 m7 _ ART6 EF7 ES7 MU7 WM7
ltac:(intros l hh [E|[E|[]]]; injection E as <- <-; [left; unfold USTACK_TOP in *; lia| right; right; lia])) as ART7.
assert (PR7 : rt_pres_fp (rt_live RT Σ4) [(F, 8%nat)] S1 [(S1, S1 + 216); (F + 48, F + 72)] m6 m7)
by (apply (pf_munch_h _ m6 m7 _ _ MU7); intros x Hx; exact Hx).
pose proof (pres_fp_trans _ _ _ _ m2 m6 m7 PFA6 (hp_acc Σ4 m6 m7 _ _ ART6 ELn7 EF7 ES7 PR7
ltac:(intros l hh [E|[E|[]]]; injection E as <- <-;
[apply iv_hp_wh; left; reflexivity| right; left; exists (F + 32), (F + 88); split; [right; right; left; reflexivity| lia]]))) as PFA7.
clear PFA6.
assert (ST7 : stk asegs m7 lo S1).
{ apply (stk_agree asegs m6 m7 lo S1 ST6); [| exact WM7]. apply (agree_of_munch _ m6 m7 _ MU7). intros x Hx. cbn [outside].
split; [lia| split; [lia| exact I]]. }
hp_tr PR7 ENH2. hp_tr PR7 J12. hp_tr PR7 J16. hp_tr PR7 FSZ3. hp_tr PR7 RATE6. hp_tr PR7 LOOK.
eapply (htr_rw _ _ _ _ _ _ PR7) in HC; rewrite ?HCS; [| hp_acl | hp_rng].
assert (DR7 : DREP (F + HO_OUT) (F + HO_STEREO) m7 D
(snd (speex_decoder_ctl (snd (speex_decoder_ctl (snd (speex_decoder_ctl (init_dec mo) (CtlSetEnh 1))) CtlGetFrameSize)) (CtlSetSamplingRate rate))) LBD).
{ apply (drep_tr _ _ _ _ m6 m7 _ _ _ _ _ PR7 DR6). intros b Hb. destruct (BSEP b Hb) as (B0 & B1 & B2 & B3 & B4).
split; [apply (acl_live _ _ _ _ _ _ _ (INBL b Hb)); lia| apply rng_out_cons; [lia| apply rng_out_cons; [lia| apply rng_out_nil]]]. }
clear PR7 DR6 ST6 MI6 MU7 WM7 SP5 LSH CBK.

assert (K8 : forall (Σ5 : rts RT) (m8 : mem) (cc8 : config) (ch : Z) (d4 : dec_state bptr)
(ra' t0' t1' t2' a0' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word) Fr' fc' (w112 w184 : word) (cb : list cell),
ASTA RT Σ5 PMh (eq (MS (mkR ra' (Z64 S1) (x_gp X) (Z64 0x630458) t0' t1' t2' (Z64 usp) (Z64 S1) a0' (Z64 ch) a2' a3' a4' a5' a6' a7'
(Z64 (F + HO_OP)) (Z64 sf) (Z64 (F + HO_OUT)) (Z64 v) (Z64 SHB) s7' (Z64 (F + 32)) (Z64 D) (Z64 (F + HO_OG)) (Z64 (F + HO_BITS))
t3' t4' t5' t6') Fr' (Z64 0x97034) fc' None m8 (seg_rom asegs))) cc8 ->
X1cn.frm0 fc' ->
rt_live RT Σ5 = (NEW ++ [(v, 80)]) ++ rt_live RT Σ1 -> rt_frames RT Σ5 = [(F, 8%nat)] -> rt_sp0 RT Σ5 = x_sp0 X -> rt_pois RT Σ5 = [] ->
x_cr0 X - h_cost h - 12 <= rt_credit RT Σ5 ->
ART RT Σ5 m8 -> mem_inv asegs m8 -> stk asegs m8 lo S1 ->
rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 W_h m2 m8 ->
rw_cells asegs m8 S1 (hsp j0 (Z64 (F + 64)) (Z64 (F + 48)) (Z64 (sf + 16)) (Z64 F) (Z64 F) (Z64 (F + HO_LOOK)) (Z64 (F + HO_RATE))
(Z64 (F + HO_ENH)) (Z64 (x_d X)) (Z64 nbr) (Z64 brem0) (Z64 SHB) (Z64 fs) w112 (Z64 (F + HO_OY)) (Z64 (h_eos h))
(Z64 (hd_frames_per_packet hd)) (Z64 (h_last_granule h)) (Z64 (F + HO_OS)) (Z64 (F + HO_STEREO)) (Z64 (F + HO_FSZ))
(Z64 (h_speex_serialno h)) w184 j192 j200 (Z64 F)) ->
rw_cells asegs m8 sf [CB 16 HSH_L_HDR] ->
rw_cells asegs m8 (F + 32) [C4 wenh] -> rw_cells asegs m8 (F + 36) [CB 12 j12] -> rw_cells asegs m8 (F + 48) cb -> cells_size cb = 24%nat ->
rw_cells asegs m8 (F + 72) [CB 16 j16] ->
rw_cells asegs m8 (F + 8384) [C4 (Z64 fs)] -> rw_cells asegs m8 (F + 9232) [C4 (Z64 rate)] -> rw_cells asegs m8 (F + 9248) [C4 wl] ->
rw_cells asegs m8 v (spx_header_cells junk28 hd w1 w2 w3 r1 r2) ->
DREP (F + HO_OUT) (F + HO_STEREO) m8 D d4 LBD -> (dec_depth d4 <= 3)%nat -> isave_ok d4 -> dec_nestedR d4 ->
(ch = 1 \/ ch = 2) -> 1 <= hd_frames_per_packet hd <= 10 ->
(forall c', (if 2147483646 <? hd_extra_headers hd then at_XT RT OUT_rep ERR_rep IO_FP X F0 fs0 c'
else at_KH RT OUT_rep ERR_rep IO_FP X F0 fs0
(incr_packet_count (set_header h (snd (speex_decoder_ctl d4 CtlGetLookahead)) (hd_frames_per_packet hd) ch rate (hd_extra_headers hd) fs))
pno nbr brem0 c') -> realizes asegs c' T) ->
realizes asegs cc8 T).
{ intros Σ5 m8 cc8 ch d4 kra kt0 kt1 kt2 ka0 ka2 ka3 ka4 ka5 ka6 ka7 ks7 kt3 kt4 kt5 kt6 kFr kfc w112 w184 cb
Hc8 FRM8 EL8 EF8 ES8 EP8 EC8 ART8 MI8 ST8 PFA8 SP8 LSH8 ENH8 J12' CB8 CBS8 J16' FSZ8 RATE8 LOOK8 HC8 DR8 DD8 ISV8 NST8 CH8 NF8 Hk8.
clear Hc7 Hk.
clear SP J12 J16 RATE LOOK HC ART0 MI ST DR Fr2 fc2 FRM2 EL2 EF2 ES2 EP2 EC2 ART2 MI2 ST2 DR2 ENH2 ACC2 ACF Fr3 fc3 FRM3 EL3 EF3 ES3 EP3 EC3 ART3 FSZ3
ACC3 ELn3 AOV MI5 ELn4 EF4 ES4 ART5 ST5 DR5 CR3 HSX3 DEC5 ACR Fr4 fc4 FRM4 EL6 EF6 ES6 EP6 EC6 ART6 RATE6 WRM ACC6 ELn5 AOV6 MI7 SP7 LSH7 POST7
EF7 ES7 ELn7 ART7 PFA7 ST7 DR7 INBL INV INDL DL DP0 FRM EL EF ESP EPO ECR ACE ACB CRS.
assert (INV8 : In (v, 80) (rt_live RT Σ5)) by (rewrite EL8; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
assert (INBL8 : forall b, In b LBD -> In (blk_addr b, blk_size b) (rt_live RT Σ5)) by (intros b Hb; rewrite EL8; apply in_or_app; left; exact (INB' b Hb)).
assert (AOV8 : aobj asegs m8 v 80).
{ split; [lia|]. split; [unfold APP_TOP; unfold USTACK_TOP in *; lia|]. exact (proj2 (af_acc_live RT AF Σ5 m8 _ _ ART8 INV8)). }

refine (rz_evt RT AF Σ5 PMh _ _ T cc8 (PMfd_mat_stable F0 fs0) Hc8 _ _).
{ eapply hp_w8; [unfold USTACK_TOP in *; lia | unfold SH_LO, SH_HI in *; lia | lia | clear - V16; Z.div_mod_to_equations; lia | lia | reflexivity
| exact HEX | exact AOV8 | exact HC8 | exact SP8 | exact MI8]. }
intros ms9 cc9 (m9 & xc0 & xc1 & MU9 & WM9 & MI9 & SP9 & POST9) Hc9. clear Hc8.
pose proof (art_munch_h Σ5 m8 m9 _ ART8 EF8 ES8 MU9 WM9 ltac:(intros l hh [E|[]]; injection E as <- <-; left; unfold USTACK_TOP in *; lia)) as ART9.
assert (PR9 : rt_pres_fp (rt_live RT Σ5) [(F, 8%nat)] S1 [(S1, S1 + 216)] m8 m9) by (apply (pf_munch_h _ m8 m9 _ _ MU9); intros x Hx; exact Hx).
pose proof (pres_fp_trans _ _ _ _ m2 m8 m9 PFA8 (hp_acc Σ5 m8 m9 _ _ ART8 EL8 EF8 ES8 PR9
ltac:(intros l hh [E|[]]; injection E as <- <-; apply iv_hp_wh; left; reflexivity))) as PFA9.
clear PFA8.
assert (ST9 : stk asegs m9 lo S1).
{ apply (stk_agree asegs m8 m9 lo S1 ST8); [| exact WM9]. apply (agree_of_munch _ m8 m9 _ MU9). intros x Hx. cbn [outside]. split; [lia| exact I]. }
hp_tr PR9 LSH8. hp_tr PR9 ENH8. hp_tr PR9 J12'. hp_tr PR9 J16'. hp_tr PR9 FSZ8. hp_tr PR9 RATE8. hp_tr PR9 LOOK8.
eapply (htr_rw _ _ _ _ _ _ PR9) in CB8; rewrite ?CBS8; [| hp_acl | hp_rng].
eapply (htr_rw _ _ _ _ _ _ PR9) in HC8; rewrite ?HCS; [| hp_acl | hp_rng].
assert (DR9 : DREP (F + HO_OUT) (F + HO_STEREO) m9 D d4 LBD).
{ apply (drep_tr _ _ _ _ m8 m9 _ _ _ _ _ PR9 DR8). intros b Hb. destruct (BSEP b Hb) as (B0 & B1 & B2 & B3 & B4).
split; [apply (acl_live _ _ _ _ _ _ _ (INBL8 b Hb)); lia| apply rng_out_cons; [lia| apply rng_out_nil]]. }
clear PR9 DR8 ST8 MI8 MU9 WM9 SP8.
assert (HSX8 : hsig_x Σ5 a h 64 (NEW ++ [(v, 80)])).
{ split; [rewrite EL8, EL1; reflexivity|]. split; [exact ND1|]. split; [exact PERM1|]. split; [exact EF8|]. split; [exact ES8|].
split; [exact EP8| lia]. }
assert (DEC9 : h_dec_rep X m9 a h) by (unfold h_dec_rep in *; rewrite STN in *; exact DEC0).
destruct POST9 as [(XE & ->) | (XN & ->)].
{
replace (2147483646 <? hd_extra_headers hd) with true in Hk8 by (symmetry; apply Z.ltb_lt; lia).
destruct (hp_fz m9 (AF_DRV _ _ ART9) PFA9) as (PF9 & ERR9 & OUTR9 & SSP9 & _ & BITS9 & SY9 & _ & _ & OSR9 & _).
eapply (hp_f48_ok h a 64 v D d4 LBD NEW Σ5 m9 cc9 T);
[exact Hc9 | exact FRM8 | exact HSX8 | exact KC64 | exact STN | exact SI1 | exact HP0 | exact PNEW | exact NDB | exact DR9
| exact DD8 | exact ART9 | exact MI9 | exact ST9 | exact PF9 | exact ERR9 | exact OUTR9 | exact SSP9
| exact SP9 | exact LSH8 | exact BITS9 | exact OSR9 | exact SY9 | exact DEC9 | exact Hk8]. }
replace (2147483646 <? hd_extra_headers hd) with false in Hk8 by (symmetry; apply Z.ltb_ge; lia).

destruct (hp_fz m9 (AF_DRV _ _ ART9) PFA9) as (PFR9 & _).
pose proof (h_unwind m9 0x97068 PFR9 ltac:(clear; vm_compute; tauto) ltac:(lia)) as UW9. clear PFR9.
unfold A_free_hp in Hc9. change 0x67e94 with e_free in Hc9.
Time cps_rt (FRE Σ5 PMh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m9 v 80 lo).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ unfold call_ok. rewrite unsigned_lit by (unfold USTACK_TOP in *; lia).
split; [exact ST9|]. split; [rewrite ES8; exact LW|]. split; [unfold RT_STACK; lia|]. split; [unfold USTACK_TOP in *; lia|].
clear - S32. Z.div_mod_to_equations. lia. }
intros cc10 (Σ6 & v10 & Hc10 & EL10 & EF10 & ES10 & EC10 & EP10). clear Hc9.
Time cps_unpack Hc10 as (m10 & RS & RA10 & PR10).
destruct RA10 as (ART10 & MI10 & ST10).

pose proof (own_pos_h m0 a h OSR0 DEC0 HP0) as OPOS.
assert (BPOS : forall e, In e NEW -> 0 < snd e).
{ intros e He. apply (Permutation_in _ PNEW) in He. unfold blocks_live in He. apply in_map_iff in He as (b & <- & Hb). cbn [snd].
exact (h_drep_sizes_pos _ _ _ m9 _ _ DR9 b Hb). }
assert (RPOS : forall e, In e (rt_live RT Σ1) -> 0 < snd e).
{ intros [p q] He. rewrite EL1 in He. apply in_app_or in He as [He|He]; [exact (OPOS p q (Permutation_in _ PERM1 He))| exact (proj1 (hi_live _ _ _ HX) p q He)]. }
assert (ND5 : List.NoDup (map fst (rt_live RT Σ5))).
{ apply (live_nodup_pos Σ5 m9 ART9). rewrite EL8. intros e He. apply in_app_or in He as [He|He]; [| exact (RPOS e He)].
apply in_app_or in He as [He|[E|[]]]; [exact (BPOS e He)| subst e; cbn; lia]. }
assert (EL6' : rt_live RT Σ6 = NEW ++ rt_live RT Σ1).
{ rewrite EL8, !map_app, <- app_assoc in ND5. cbn [map app fst] in ND5.
rewrite EL10, EL8, <- app_assoc. cbn [app].
rewrite live_remove_app, live_remove_cons. cbn [fst]. rewrite Z.eqb_refl. cbv iota.
rewrite (live_remove_none v NEW), (live_remove_none v (rt_live RT Σ1)); [reflexivity| |].
- intros e He E. apply (NoDup_remove_2 _ _ _ ND5). rewrite <- E. apply in_or_app. right. exact (in_map fst _ _ He).
- intros e He E. apply (NoDup_remove_2 _ _ _ ND5). rewrite <- E. apply in_or_app. left. exact (in_map fst _ _ He). }
rewrite EF8 in PR10. apply (pres_fp_of_pres _ _ _ []) in PR10.
assert (EF11 : rt_frames RT Σ6 = [(F, 8%nat)]) by (rewrite EF10; exact EF8).
assert (ES11 : rt_sp0 RT Σ6 = x_sp0 X) by (rewrite ES10; exact ES8).
assert (PR10h : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 W_h m9 m10).
{ apply (pres_fp_weaken _ _ _ [] _ m9 m10); [| intros x _; exact I].
apply (pres_fp_mono _ _ _ (rt_live RT Σ6) [(F, 8%nat)] S1 [] m9 m10 PR10); [intros e He; rewrite EL6'; apply in_or_app; right; exact He| intros e He; exact He| lia]. }
pose proof (pres_fp_trans _ _ _ _ m2 m9 m10 PFA9 PR10h) as PFA10. clear PFA9 PR10h.
assert (INBL10 : forall b, In b LBD -> In (blk_addr b, blk_size b) (rt_live RT Σ6)) by (intros b Hb; rewrite EL6'; apply in_or_app; left; exact (INB b Hb)).
hp_tr PR10 LSH8. hp_tr PR10 ENH8. hp_tr PR10 J12'. hp_tr PR10 J16'. hp_tr PR10 FSZ8. hp_tr PR10 RATE8. hp_tr PR10 LOOK8.
eapply (htr_rw _ _ _ _ _ _ PR10) in CB8; rewrite ?CBS8; [| hp_acl | hp_rng].
eapply (htr_rw _ _ _ _ _ _ PR10) in SP9; [| rewrite hsp_size; hp_acl | rewrite hsp_size; hp_rng].
assert (DR10 : DREP (F + HO_OUT) (F + HO_STEREO) m10 D d4 LBD).
{ apply (drep_tr _ _ _ _ m9 m10 _ _ _ _ _ PR10 DR9). intros b Hb. destruct (BSEP b Hb) as (B0 & B1 & B2 & B3 & B4).
split; [apply (acl_live _ _ _ _ _ _ _ (INBL10 b Hb)); lia| apply rng_out_nil]. }
clear PR10 DR9 ST9 MI9 ART9 HC8 AOV8 INV8 INBL8 ND5.

refine (rz_evt RT AF Σ6 PMh _ _ T cc10 (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply hp_w9; [reflexivity | unfold USTACK_TOP in *; lia | unfold SH_LO, SH_HI in *; lia | lia | exact LSH8 | exact SP9 | exact MI10]. }
intros ms11 cc11 (m11 & -> & MU11 & WM11 & MI11 & LSH11) Hc11. clear Hc.
pose proof (art_munch_h Σ6 m10 m11 _ ART10 EF11 ES11 MU11 WM11 ltac:(intros l hh [E|[]]; injection E as <- <-; right; left; lia)) as ART11.
assert (PR11 : rt_pres_fp (rt_live RT Σ6) [(F, 8%nat)] S1 [(sf, sf + 16)] m10 m11) by (apply (pf_munch_h _ m10 m11 _ _ MU11); intros x Hx; exact Hx).
pose proof (pres_fp_trans _ _ _ _ m2 m10 m11 PFA10 (hp_acc Σ6 m10 m11 NEW _ ART10 EL6' EF11 ES11 PR11
ltac:(intros l hh [E|[]]; injection E as <- <-; apply iv_hp_wh; right; left; reflexivity))) as PFA11.
clear PFA10.
assert (ST11 : stk asegs m11 lo S1).
{ apply (stk_agree asegs m10 m11 lo S1 ST10); [| exact WM11]. apply (agree_of_munch _ m10 m11 _ MU11). intros x Hx. cbn [outside].
split; [unfold SH_LO, SH_HI in *; lia| exact I]. }
hp_tr PR11 ENH8. hp_tr PR11 J12'. hp_tr PR11 J16'. hp_tr PR11 FSZ8. hp_tr PR11 RATE8. hp_tr PR11 LOOK8.
eapply (htr_rw _ _ _ _ _ _ PR11) in CB8; rewrite ?CBS8; [| hp_acl | hp_rng].
eapply (htr_rw _ _ _ _ _ _ PR11) in SP9; [| rewrite hsp_size; hp_acl | rewrite hsp_size; hp_rng].
assert (DR11 : DREP (F + HO_OUT) (F + HO_STEREO) m11 D d4 LBD).
{ apply (drep_tr _ _ _ _ m10 m11 _ _ _ _ _ PR11 DR10). intros b Hb. destruct (BSEP b Hb) as (B0 & B1 & B2 & B3 & B4).
split; [apply (acl_live _ _ _ _ _ _ _ (INBL10 b Hb)); lia| apply rng_out_cons; [lia| apply rng_out_nil]]. }
clear PR11 DR10 ST10 MI10 MU11 WM11 LSH8.

assert (CRB : 1000 <= x_cr0 X - h_cost h - 12) by (pose proof (hi_cr _ _ _ HX) as FC; unfold h_cost, H_HDR_CREDIT, H_DEC_CREDIT, FUZZ_COST in *; rewrite PC0; lia).
destruct (hp_fz m11 (AF_DRV _ _ ART11) PFA11) as (PFR11 & _).
pose proof (h_acc_at OUT_rep IO_FP IO_img X HX m11 PFR11) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ACL). unfold HO_LOOK in ACL. clear PFR11.
eapply (hp_ctl Σ6 m11 cc11 T d4 D LBD CtlGetLookahead (F + 9248));
[exact Hc11 | reflexivity | reflexivity | reflexivity | reflexivity | exact FRM8 | exact EF11 | exact ES11 | rewrite EC10; lia | reflexivity | exact DR11
| exact DD8 | exact NDB | exact INBL10 | exact I | exists wl; exact LOOK8
| lia | cbn [creq_size]; lia | exact ACL | cbn [creq_align]; clear - F64; Z.div_mod_to_equations; lia | exact ART11 | exact MI11 | exact ST11 | ].
intros Σ7 m12 cc12 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10' v11 v12 v13 Fr7 fc7 Hc12 FRM12 EL12 EF12 ES12 EP12 EC12 ART12 MI12 ST12 PR DR12 POST ACC12.
clear Hc11.
cbn [creq_size] in PR. destruct POST as (LOOK12 & LKR).
assert (INBL12 : forall b, In b LBD -> In (blk_addr b, blk_size b) (NEW)) by exact INB.
pose proof (pres_fp_trans _ _ _ _ m2 m11 m12 PFA11 (hp_acc Σ6 m11 m12 NEW _ ART11 EL6' EF11 ES11 PR
ltac:(intros l hh [E|Hin]; [injection E as <- <-; right; left; exists (F + 9248), (F + 9252); split; [right; right; right; right; right; left; reflexivity| lia]
| exact (iv_hp_blocks _ LBD l hh INBL12 Hin)]))) as PFA12.
clear PFA11.
hp_tr PR LSH11. hp_tr PR ENH8. hp_tr PR J12'. hp_tr PR J16'. hp_tr PR FSZ8. hp_tr PR RATE8.
eapply (htr_rw _ _ _ _ _ _ PR) in CB8; rewrite ?CBS8; [| hp_acl | hp_rng].
eapply (htr_rw _ _ _ _ _ _ PR) in SP9; [| rewrite hsp_size; hp_acl | rewrite hsp_size; hp_rng].
clear PR LOOK8.

refine (rz_evt RT AF Σ7 PMh _ _ T cc12 (PMfd_mat_stable F0 fs0) Hc12 _ _).
{ eapply (hp_w10 _ (hd_extra_headers hd)); [reflexivity | unfold USTACK_TOP in *; lia | lia | exact SP9 | exact MI12]. }
intros ms13 cc13 -> Hc13. clear Hc12.
apply Hk8. cbv iota.
set (d5 := snd (speex_decoder_ctl d4 CtlGetLookahead)).
assert (LB19 : (length LBD <= 19)%nat).
{ pose proof (Permutation_length PNEW) as PL. unfold blocks_live in PL. rewrite length_map in PL.
assert (I19 : init_nblocks mo <= 19) by (destruct mo; cbn; lia). lia. }
assert (ENH56 : exists je, rw_cells asegs m12 (F + HO_ENH) [CB 56 je]).
{ assert (R : rw_cells asegs m12 (F + 32) (([C4 wenh] ++ [CB 12 j12]) ++ cb ++ [CB 16 j16])).
{ apply rw_cells_app. split.
- apply rw_cells_app. split; [exact ENH8|]. cbn [cells_size csize Nat.add]. replace (F + 32 + Z.of_nat 4) with (F + 36) by lia. exact J12'.
- cbn [cells_size csize Nat.add app]. apply rw_cells_app. split; [replace (F + 32 + Z.of_nat 16) with (F + 48) by lia; exact CB8|].
rewrite CBS8. replace (F + 32 + Z.of_nat 16 + Z.of_nat 24) with (F + 72) by lia. exact J16'. }
destruct (rw_cells_forget asegs m12 _ _ R) as (je & R').
rewrite !cells_size_app, CBS8 in R'. cbn [cells_size csize Nat.add] in R'. exists je. unfold HO_ENH. exact R'. }
assert (SPh : rw_cells asegs m12 S1 (h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h)) (Z64 (h_speex_serialno h)) j0 j192 j200
(incr_packet_count (set_header h d5 (hd_frames_per_packet hd) ch rate (hd_extra_headers hd) fs)))).
{ unfold h_spill. cbn [incr_packet_count set_header h_granule_frame_size h_extra_headers h_eos h_nframes h_channels].
replace (if hd_frames_per_packet hd =? 0 then 1 else hd_frames_per_packet hd) with (hd_frames_per_packet hd)
by (destruct (Z.eqb_spec (hd_frames_per_packet hd) 0); lia).
exact SP9. }
assert (DP0 : 0 < D) by exact (proj1 (decst_rep_pos _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DR12)).
eapply (hp_kh_ok Σ7 m12 cc13 D d5 LBD NEW (hd_frames_per_packet hd) ch rate (hd_extra_headers hd) fs);
[exact Hc13 | exact FRM12 | rewrite EL12, EL6', EL1; reflexivity | rewrite EF12; exact EF11 | rewrite ES12; exact ES11
| rewrite EP12, EP10; exact EP8 | lia | exact PNEW | exact NDB | exact AL8 | exact LB19 | exact ART12 | exact MI12 | exact ST12 | exact PFA12
| exact SPh | exact LSH11 | exact ENH56 | exact FSZ8 | exact RATE8 | exists (Z64 (fst (speex_decoder_ctl d4 CtlGetLookahead))); exact LOOK12
| exact DR12 | exact DP0 | unfold d5; rewrite depth_ctl; exact DD8 | unfold d5; apply isave_ctl; [intros off E; discriminate E| exact ISV8]
| unfold d5; apply ctl_nested_same; exact NST8 | lia | exact NF8 | lia | exact RTR | lia]. }
assert (CR4 : x_cr0 X - h_cost h - 12 <= rt_credit RT Σ4) by lia.
assert (HSX4 : hsig_x Σ4 a h 64 (NEW ++ [(v, 80)])).
{ split; [rewrite ELn7, EL1; reflexivity|]. split; [exact ND1|]. split; [exact PERM1|]. split; [exact EF7|]. split; [exact ES7|].
split; [rewrite EP6, EP3, EP2; exact EPO| lia]. }
assert (DEC7 : h_dec_rep X m7 a h) by (unfold h_dec_rep in *; rewrite STN in *; exact DEC0).
assert (DD7 : (dec_depth (snd (speex_decoder_ctl (snd (speex_decoder_ctl (snd (speex_decoder_ctl (init_dec mo) (CtlSetEnh 1))) CtlGetFrameSize))
(CtlSetSamplingRate rate))) <= 3)%nat) by (rewrite !depth_ctl; exact (depth_init mo)).
destruct POST7 as [(NFB & CB7 & ->) | [(NFG & CH1 & CB7 & ->) | (NFG & CH2 & CB7 & ->)]].
{
replace ((hd_frames_per_packet hd <? 1) || (10 <? hd_frames_per_packet hd)) with true in Hk
by (symmetry; destruct (Z.ltb_spec (hd_frames_per_packet hd) 1); [reflexivity|]; cbn [orb]; apply Z.ltb_lt; lia).
cbv iota in Hk.
destruct (hp_fz m7 (AF_DRV _ _ ART7) PFA7) as (PF7 & ERR7 & OUTR7 & SSP7 & _ & BITS7 & SY7 & _ & _ & OSR7 & _).
eapply (hp_f48_ok h a 64 v D _ LBD NEW Σ4 m7 cc7 T);
[exact Hc7 | exact FRM4 | exact HSX4 | exact KC64 | exact STN | exact SI1 | exact HP0 | exact PNEW | exact NDB | exact DR7
| exact DD7 | exact ART7 | exact MI7 | exact ST7 | exact PF7 | exact ERR7 | exact OUTR7 | exact SSP7
| exact SP7 | exact LSH7 | exact BITS7 | exact OSR7 | exact SY7 | exact DEC7 | exact Hk]. }
replace ((hd_frames_per_packet hd <? 1) || (10 <? hd_frames_per_packet hd)) with false in Hk
by (symmetry; apply orb_false_intro; [apply Z.ltb_ge| apply Z.ltb_ge]; lia).
cbv iota in Hk.
assert (ISV3 : isave_ok (snd (speex_decoder_ctl (snd (speex_decoder_ctl (snd (speex_decoder_ctl (init_dec mo) (CtlSetEnh 1))) CtlGetFrameSize))
(CtlSetSamplingRate rate)))).
{ repeat (apply isave_ctl; [intros off E; discriminate E|]). exact (isave_init mo). }
assert (NST3 : dec_nestedR (snd (speex_decoder_ctl (snd (speex_decoder_ctl (snd (speex_decoder_ctl (init_dec mo) (CtlSetEnh 1))) CtlGetFrameSize))
(CtlSetSamplingRate rate)))).
{ repeat apply ctl_nested_same. exact (nested_init mo). }
{
apply Z.eqb_eq in CH1. rewrite CH1 in Hk. cbv iota in Hk.
eapply (K8 Σ4 m7 cc7 1 _); [exact Hc7 | exact FRM4 | exact ELn7 | exact EF7 | exact ES7 | rewrite EP6, EP3, EP2; exact EPO | exact CR4
| exact ART7 | exact MI7 | exact ST7 | exact PFA7 | exact SP7 | exact LSH7 | exact ENH2 | exact J12 | exact CB7 | reflexivity | exact J16
| exact FSZ3 | exact RATE6 | exact LOOK | exact HC | exact DR7 | exact DD7 | exact ISV3 | exact NST3 | left; reflexivity | lia | ].
intros c' Hc'. apply Hk. destruct (2147483646 <? hd_extra_headers hd); exact Hc'. }

replace ((hd_frames_per_packet hd <? 1) || (10 <? hd_frames_per_packet hd)) with false in Hk
by (symmetry; apply orb_false_intro; [apply Z.ltb_ge| apply Z.ltb_ge]; lia).
cbv iota in Hk.
assert (ISV3 : isave_ok (snd (speex_decoder_ctl (snd (speex_decoder_ctl (snd (speex_decoder_ctl (init_dec mo) (CtlSetEnh 1))) CtlGetFrameSize))
(CtlSetSamplingRate rate)))).
{ repeat (apply isave_ctl; [intros off E; discriminate E|]). exact (isave_init mo). }
assert (NST3 : dec_nestedR (snd (speex_decoder_ctl (snd (speex_decoder_ctl (snd (speex_decoder_ctl (init_dec mo) (CtlSetEnh 1))) CtlGetFrameSize))
(CtlSetSamplingRate rate)))).
{ repeat apply ctl_nested_same. exact (nested_init mo). }
apply Z.eqb_neq in CH2. rewrite CH2 in Hk. cbv iota in Hk.
assert (LB7 : bytes_at asegs m7 (shad F) HSH_L_HDR) by (destruct LSH7 as [[_ B] _]; cbn [cells_bytes cbytes] in B; rewrite app_nil_r in B; rewrite <- ESF; exact B).
destruct (hsh_L_hdr_acc m7 F ltac:(clear - F64; Z.div_mod_to_equations; lia) ltac:(lia) LB7) as (_ & ACB7). clear LB7.
unfold HO_CBK in ACB7. pose proof (acc_sub asegs m7 (F + 48) 40 (F + 48) 24 ACB7 ltac:(lia) ltac:(lia)) as ACB24.
eapply (hp_ctl Σ4 m7 cc7 T _ D LBD CtlSetHandlerStereo (F + 48));
[exact Hc7 | reflexivity | reflexivity | reflexivity | reflexivity | exact FRM4 | exact EF7 | exact ES7 | lia | reflexivity | exact DR7
| exact DD7 | exact NDB | exact INBL | exact I | exists c52; exact CB7
| lia | cbn [creq_size]; lia | exact ACB24 | cbn [creq_align]; clear - F64; Z.div_mod_to_equations; lia | exact ART7 | exact MI7 | exact ST7 | ].
intros Σ8 m13 cc13 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 Fr8 fc8 Hc13 FRM13 EL13 EF13 ES13 EP13 EC13 ART13 MI13 ST13 PR DR13 POST ACC13.
clear Hc7.
cbn [creq_size] in PR. destruct POST as (pad & CB13).
pose proof (pres_fp_trans _ _ _ _ m2 m7 m13 PFA7 (hp_acc Σ4 m7 m13 _ _ ART7 ELn7 EF7 ES7 PR
ltac:(intros l hh [E|Hin]; [injection E as <- <-; right; left; exists (F + 32), (F + 88); split; [right; right; left; reflexivity| lia]
| exact (iv_hp_blocks _ LBD l hh INB' Hin)]))) as PFA13.
hp_tr PR LSH7. hp_tr PR ENH2. hp_tr PR J12. hp_tr PR J16. hp_tr PR FSZ3. hp_tr PR RATE6. hp_tr PR LOOK.
eapply (htr_rw _ _ _ _ _ _ PR) in HC; rewrite ?HCS; [| hp_acl | hp_rng].
eapply (htr_rw _ _ _ _ _ _ PR) in SP7; [| rewrite hsp_size; hp_acl | rewrite hsp_size; hp_rng].
clear PR.

refine (rz_evt RT AF Σ8 PMh _ _ T cc13 (PMfd_mat_stable F0 fs0) Hc13 _ _).
{ eapply hp_w8r; [reflexivity | exact MI13]. }
intros ms14 cc14 -> Hc14. clear Hc13.
eapply (K8 Σ8 m13 cc14 2 _); [exact Hc14 | exact FRM13 | rewrite EL13; exact ELn7 | rewrite EF13; exact EF7 | rewrite ES13; exact ES7
| rewrite EP13, EP6, EP3, EP2; exact EPO | lia
| exact ART13 | exact MI13 | exact ST13 | exact PFA13 | exact SP7 | exact LSH7 | exact ENH2 | exact J12 | exact CB13 | reflexivity | exact J16
| exact FSZ3 | exact RATE6 | exact LOOK | exact HC | exact DR13 | rewrite depth_ctl; exact DD7 | apply isave_ctl; [intros off E; discriminate E| exact ISV3]
| apply ctl_nested_same; exact NST3 | right; reflexivity | lia | ].
intros c' Hc'. apply Hk. destruct (2147483646 <? hd_extra_headers hd); exact Hc'.
Qed.

Lemma lit_mode : forall mo, In (mode_addr mo, 96) ACC_LITS.
Proof. intros mo. destruct mo; unfold mode_addr, A_speex_nb_mode, A_speex_wb_mode, A_speex_uwb_mode, ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]). Qed.
Lemma lit_mode_list : In (A_speex_mode_list, 24) ACC_LITS.
Proof. unfold A_speex_mode_list, ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]). Qed.
Lemma mode_addr_range : forall mo, 0 <= mode_addr mo /\ mode_addr mo + 96 <= 0x100000.
Proof. intros mo. destruct mo; unfold mode_addr, A_speex_nb_mode, A_speex_wb_mode, A_speex_uwb_mode; lia. Qed.
Lemma sb_mode_ptr_addr : forall mo, sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode mo = mode_addr mo.
Proof. destruct mo; reflexivity. Qed.
Lemma own_len_none : forall (a' : haux) (h' : hstate unit), h_st h' = None -> (length (h_own a' h') <= 5)%nat.
Proof.
intros a' h' STN'. unfold h_own. rewrite STN'. cbn [app length].
destruct (h_stream_init h' =? 0); destruct (sy_data (h_oy h')); cbn [length app]; lia.
Qed.
Lemma st_traces_96cfc : In [0x97068; 0x96564] SITE_TRACES. Proof. vm_compute. tauto. Qed.
Lemma st_traces_99158 : In [0x994c4; 0x96564] SITE_TRACES. Proof. vm_compute. tauto. Qed.

Lemma art_munch_below : forall (Σ : rts RT) (m m1 : mem),
ART RT Σ m -> rt_sp0 RT Σ = x_sp0 X -> munch [(S1 + -16, S1)] m m1 -> wmono asegs m m1 -> ART RT Σ m1.
Proof.
intros Σ m m1 ART0 ES MU WM.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & _).
apply (af_frame RT AF Σ m m1 (S1 + -16) ART0); [rewrite ES; unfold RT_STACK, H_STACK in LR; lia| | exact WM].
intros b Hb. apply MU. cbn [outside]. split; [intros Hin; apply Hb; left; unfold USTACK_TOP in *; lia| exact I].
Qed.

Hypothesis INIT8 : forall mo, init_cps_at8 RT mo.

Lemma hp_ap : forall (Σ2 : rts RT) (cc : config) T (v : Z) (r1 : option (unit * spx_header))
(t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s9 s10 t3 t4 t5 t6 : word) Fr fc (j12 j16 : list byte) (c48 c52 c56 c64 wl : word),
ASTA RT Σ2 PMh (eq (MS (mkR (Z64 0x96e8c) (Z64 S1) (x_gp X) (Z64 0x630458) t0 t1 t2 (Z64 usp) (Z64 S1) (Z64 v) a1 a2 a3 a4 a5 a6 a7
(Z64 (F + HO_OP)) (Z64 sf) (Z64 (F + HO_OUT)) (Z64 (F + HO_OG)) s6 (Z64 (F + HO_OS)) (Z64 (F + 32)) s9 s10 (Z64 (F + HO_BITS))
t3 t4 t5 t6) Fr (ret_pc (Z64 0x96e8c)) fc None m2 (seg_rom asegs))) cc ->
X1cn.frm0 fc -> rt_frames RT Σ2 = [(F, 8%nat)] -> rt_sp0 RT Σ2 = x_sp0 X -> rt_pois RT Σ2 = [] -> rt_credit RT Σ2 = rt_credit RT Σ1 ->
ART RT Σ2 m2 -> mem_inv asegs m2 -> stk asegs m2 lo S1 ->
p2h_result m2 v r1 (rt_live RT Σ1) (rt_live RT Σ2) ->
rw_cells asegs m2 S1 (h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h)) (Z64 (h_speex_serialno h)) j0 j192 j200 h) ->
rw_cells asegs m2 sf [CB 16 HSH_L_HDR] ->
rw_cells asegs m2 (F + 32) [C4 (Z64 1)] -> rw_cells asegs m2 (F + 36) [CB 12 j12] -> rw_cells asegs m2 (F + 48) [C4 c48; C4 c52; C8 c56; C8 c64] ->
rw_cells asegs m2 (F + 72) [CB 16 j16] ->
rw_cells asegs m2 (F + HO_FSZ) [C4 (Z64 (h_frame_size h))] -> rw_cells asegs m2 (F + HO_RATE) [C4 (Z64 (h_rate h))] -> rw_cells asegs m2 (F + HO_LOOK) [C4 wl] ->
(forall c', match (match r1 with None => None | Some (_, hd) => hdr_tail h hd end) with
| None => at_XT RT OUT_rep ERR_rep IO_FP X F0 fs0 c'
| Some h3 => at_KH RT OUT_rep ERR_rep IO_FP X F0 fs0 (incr_packet_count h3) pno nbr brem0 c'
end -> realizes asegs c' T) ->
realizes asegs cc T.
Proof.
intros Σ2 cc T v r1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s9 s10 t3 t4 t5 t6 Fr fc j12 j16 c48 c52 c56 c64 wl
Hc FRM EF ESP EPO ECR ART2 MI ST PR SP LSH ENH J12 CBK J16 FSZ RATE LOOK Hk.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS1 as (EL1 & ND1 & PERM1 & EF1 & ESP1 & EPO1 & ECR1).
pose proof HR0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OSR0 & _ & _ & _ & DEC0 & HP0).
pose proof hp_st_none as STN.
pose proof hp_hsep as HSP.
pose proof (own_pos_h m0 a h OSR0 DEC0 HP0) as OPOS.
assert (RPOS : forall e, In e (rt_live RT Σ1) -> 0 < snd e).
{ intros [p q] He. rewrite EL1 in He. apply in_app_or in He as [He|He]; [exact (OPOS p q (Permutation_in _ PERM1 He))| exact (proj1 (hi_live _ _ _ HX) p q He)]. }
assert (KC0 : h_cost h + 64 <= FUZZ_COST - 1) by (unfold h_cost, H_HDR_CREDIT, H_DEC_CREDIT, FUZZ_COST; rewrite PC0; lia).
destruct (hp_fz m2 (AF_DRV _ _ ART2) (pres_fp_refl _ _ _ _ _)) as (PFR & ERR & OUTR & SSP & _ & BITS & SY & _ & _ & OSR & _).
assert (DEC2 : h_dec_rep X m2 a h) by (unfold h_dec_rep in *; rewrite STN in *; exact DEC0).
destruct r1 as [[[] hd]|].
2: {
destruct PR as (-> & _ & _ & EQL). specialize (EQL RPOS).
refine (rz_evt RT AF Σ2 PMh _ _ T cc (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply hp_w2n; [reflexivity | exact MI]. }
intros ms1 cc1 -> Hc1. clear Hc.
assert (HS2 : hsig_k RT X Σ2 a h 0).
{ split; [rewrite EQL; exact EL1|]. split; [exact ND1|]. split; [exact PERM1|]. split; [exact EF|]. split; [exact ESP|]. split; [exact EPO| rewrite ECR; lia]. }
exact (hp_tail_ok h a 0 Σ2 m2 cc1 T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
Hc1 FRM HS2 ltac:(lia) STN SI1 HP0 ART2 MI ST PFR ERR OUTR SSP SP LSH BITS OSR SY DEC2 Hk). }

destruct PR as (junk28 & w1 & w2 & w3 & r1' & r2' & V0 & V16 & EL2 & HC & RV & RR & RM & RB & RN & RF & RE).
cbv iota in Hk. cbv [X1rg.SPEEX_NB_MODES X1rh.SPEEX_NB_MODES] in RM.
assert (INV : In (v, 80) (rt_live RT Σ2)) by (rewrite EL2; left; reflexivity).
assert (VSEP : v + 80 <= lo).
{ destruct (af_live_range RT AF Σ2 m2 _ _ ART2 INV) as (_ & VL & _). rewrite ESP in VL. pose proof (hi_lo _ _ _ HX) as (LW0 & _). lia. }
assert (AOV : aobj asegs m2 v 80).
{ split; [lia|]. split; [unfold APP_TOP; unfold USTACK_TOP in *; lia|]. exact (proj2 (af_acc_live RT AF Σ2 m2 _ _ ART2 INV)). }

refine (rz_evt RT AF Σ2 PMh _ _ T cc (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply (hp_w2 _ v junk28 hd); [reflexivity | unfold USTACK_TOP in *; lia | lia | clear - V16; Z.div_mod_to_equations; lia | lia | lia | exact AOV | exact HC | exact SP
| exact (AF_LIB _ _ ART2) | exact MI]. }
intros ms1 cc1 POST1 Hc1. clear Hc.
set (mo := mode_of_id (hd_mode hd)) in *.

assert (K68 : forall (m3 : mem) (cc3 : config) (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
ASTA RT Σ2 PMh (eq (MS (mkR ra' (Z64 S1) (x_gp X) (Z64 0x630458) t0' t1' t2' (Z64 usp) (Z64 S1) (Z64 (mode_addr mo)) a1' a2' a3' a4' a5' a6' a7'
(Z64 (F + HO_OP)) (Z64 sf) (Z64 (F + HO_OUT)) (Z64 v) (Z64 SHB) (Z64 (F + HO_OS)) (Z64 (F + 32)) s9 (Z64 (F + HO_OG))
(Z64 (F + HO_BITS)) t3' t4' t5' t6') Fr (Z64 0x96ed4) fc None m3 (seg_rom asegs))) cc3 ->
ART RT Σ2 m3 -> mem_inv asegs m3 -> stk asegs m3 lo S1 -> rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 W_h m2 m3 ->
rw_cells asegs m3 S1 (h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h)) (Z64 (h_speex_serialno h)) j0 j192 j200 h) ->
rw_cells asegs m3 sf [CB 16 HSH_L_HDR] ->
rw_cells asegs m3 (F + 32) [C4 (Z64 1)] -> rw_cells asegs m3 (F + 36) [CB 12 j12] -> rw_cells asegs m3 (F + 48) [C4 c48; C4 c52; C8 c56; C8 c64] ->
rw_cells asegs m3 (F + 72) [CB 16 j16] ->
rw_cells asegs m3 (F + HO_FSZ) [C4 (Z64 (h_frame_size h))] -> rw_cells asegs m3 (F + HO_RATE) [C4 (Z64 (h_rate h))] -> rw_cells asegs m3 (F + HO_LOOK) [C4 wl] ->
rw_cells asegs m3 v (spx_header_cells junk28 hd w1 w2 w3 r1' r2') ->
realizes asegs cc3 T).
{ intros m3 cc3 ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Hc3 ART3 MI3 ST3 PFA3 SP3 LSH3 ENH3 J123 CBK3 J163 FSZ3 RATE3 LOOK3 HC3.
clear Hc1 POST1 SP LSH ENH J12 CBK J16 FSZ RATE LOOK HC ART2 MI ST.
assert (AOV3 : aobj asegs m3 v 80).
{ split; [lia|]. split; [unfold APP_TOP; unfold USTACK_TOP in *; lia|]. exact (proj2 (af_acc_live RT AF Σ2 m3 _ _ ART3 INV)). }
assert (AOM : aobj asegs m3 (mode_addr mo) 32).
{ pose proof (mode_addr_range mo) as (MA0 & MA1).
apply (aobj_sub asegs m3 (mode_addr mo) 96); [| lia | lia]. apply (aobj_lit RT AF Σ2 m3 _ _ ART3 (lit_mode mo)); [lia| unfold APP_TOP; lia]. }

refine (rz_evt RT AF Σ2 PMh _ _ T cc3 (PMfd_mat_stable F0 fs0) Hc3 _ _).
{ eapply (hp_w3 v mo junk28 hd); [lia | clear - V16; Z.div_mod_to_equations; lia | unfold USTACK_TOP in *; lia | reflexivity | exact RV | exact RB
| exact AOV3 | exact HC3 | exact AOM | exact (AF_LIB _ _ ART3) | exact MI3]. }
intros ms4 cc4 (xa1 & xa2 & xa3 & POST4) Hc4. clear Hc3.
destruct (hp_fz m3 (AF_DRV _ _ ART3) PFA3) as (PF3 & ERR3 & OUTR3 & SSP3 & _ & BITS3 & SY3 & _ & _ & OSR3 & _).
assert (DEC3 : h_dec_rep X m3 a h) by (unfold h_dec_rep in *; rewrite STN in *; exact DEC0).
assert (HSX2 : hsig_x Σ2 a h 0 [(v, 80)]).
{ split; [rewrite EL2, EL1; reflexivity|]. split; [exact ND1|]. split; [exact PERM1|]. split; [exact EF|]. split; [exact ESP|].
split; [exact EPO| rewrite ECR; lia]. }
destruct POST4 as [(VB & ->) | (VG & BG & ->)].
{
assert (HT : hdr_tail h hd = None).
{ unfold hdr_tail. destruct (Z.ltb_spec 1 (hd_speex_version_id hd)); [reflexivity|].
replace (hd_mode_bitstream_version hd =? 4) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
rewrite HT in Hk.
eapply (hp_f54_ok h a 0 v Σ2 m3 cc4 T);
[exact Hc4 | exact FRM | exact HSX2 | lia | exact STN | exact SI1 | exact HP0 | exact ART3 | exact MI3 | exact ST3 | exact PF3 | exact ERR3
| exact OUTR3 | exact SSP3 | exact SP3 | exact LSH3 | exact BITS3 | exact OSR3 | exact SY3 | exact DEC3 | exact Hk]. }

assert (LVB : Z.of_nat (length (rt_live RT Σ2)) + init_nblocks mo <= LIVE_MAX).
{ rewrite EL2, EL1. cbn [length]. rewrite length_app, (Permutation_length PERM1).
pose proof (own_len_none a h STN) as OL. pose proof (hi_live _ _ _ HX) as (_ & LL). unfold H_LIVE, LIVE_MAX in *.
assert (I19 : init_nblocks mo <= 19) by (destruct mo; cbn; lia). lia. }
assert (CRI : init_credit mo <= rt_credit RT Σ2).
{ rewrite ECR. pose proof (hi_cr _ _ _ HX) as FC. unfold h_cost, H_HDR_CREDIT, H_DEC_CREDIT, FUZZ_COST in *. rewrite PC0 in ECR1.
assert (I4 : init_credit mo <= 4) by (destruct mo; cbn; lia). lia. }
assert (UE : uw_entry m3 (Z64 usp) (bv_unsigned (Z64 S1)) lo [0x96564]).
{ cbn [uw_entry]. rewrite !unsigned_lit by (unfold USTACK_TOP in *; lia). exact (h_uw_chain m3 PF3). }
assert (ITR : init_traces mo (bv_unsigned (Z64 0x96f2c)) [0x96564]) by (rewrite unsigned_lit by lia; exact (init_traces_harness mo)).
assert (IST : init_stack mo <= 480) by (destruct mo; cbn; lia).
unfold A_decoder_init_h in Hc4. change 0x983e8 with A_speex_decoder_init in Hc4.
Time cps_rt (INIT8 mo Σ2 PMh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 lo [0x96564] (F + HO_OUT) (F + HO_STEREO)).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ rewrite EF. cbn [length]. unfold FRAMES_MAX. destruct mo; cbn; lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). exact ST3. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold RT_STACK. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). exact S32. }
intros cc5 (Σ3 & D & LBD & NEW & Hc5 & EL3 & PNEW & NDB & LNEW & EF3 & ES3 & EC3 & EP3 & AL8). clear Hc4.
Time cps_unpack_lib Hc5 as (m4 & RS & RA & PR & DR).
destruct RA as (ART4 & MI4 & WM4 & ST4).
rewrite EF in PR.
assert (PRh : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 W_h m3 m4).
{ apply (pres_fp_weaken _ _ _ [] _ m3 m4); [| intros x _; exact I].
apply (pres_fp_mono _ _ _ (rt_live RT Σ2) [(F, 8%nat)] S1 [] m3 m4 PR); [intros e He; rewrite EL2; right; exact He| intros e He; exact He| lia]. }
pose proof (pres_fp_trans _ _ _ _ m2 m3 m4 PFA3 PRh) as PFA4. clear PFA3 PRh.
unfold HO_FSZ, HO_RATE, HO_LOOK in FSZ3, RATE3, LOOK3.
hp_tr PR LSH3. hp_tr PR ENH3. hp_tr PR J123. hp_tr PR CBK3. hp_tr PR J163. hp_tr PR FSZ3. hp_tr PR RATE3. hp_tr PR LOOK3.
assert (HCS : cells_size (spx_header_cells junk28 hd w1 w2 w3 r1' r2') = 80%nat) by reflexivity.
eapply (htr_rw _ _ _ _ _ _ PR) in HC3; rewrite ?HCS; [| hp_acl | hp_rng].
eapply (htr_rw _ _ _ _ _ _ PR) in SP3; [| unfold h_spill; rewrite hsp_size; hp_acl | unfold h_spill; rewrite hsp_size; hp_rng].
clear PR.
eapply (hp_ai Σ3 m4 cc5 T hd v D junk28 w1 w2 w3 r1' r2' LBD NEW j12 j16 c48 c52 c56 c64 wl);
[exact Hc | exact RS | rewrite EL3, EL2; reflexivity | rewrite EF3; exact EF | rewrite ES3; exact ESP | rewrite EP3; exact EPO
| assert (I4 : init_credit mo <= 4) by (destruct mo; cbn; lia); lia
| exact PNEW | exact NDB | exact AL8 | exact LNEW | exact DR | exact V0 | exact V16 | exact HC3 | exact RR | exact RN | exact RF | exact RE
| exact VG | exact BG | exact RM | exact ART4 | exact MI4 | first [exact ST4 | rewrite unsigned_lit in ST4 by (unfold USTACK_TOP in *; lia); exact ST4]
| exact PFA4 | exact SP3 | exact LSH3 | exact ENH3 | exact J123 | exact CBK3 | exact J163 | exact FSZ3 | exact RATE3 | exact LOOK3 | exact Hk]. }
destruct POST1 as [(M0 & ->) | (MN & ->)].
{
assert (EMO : mode_addr mo = A_speex_nb_mode) by (unfold mo, mode_of_id; rewrite M0; reflexivity).
rewrite <- EMO in Hc1.
exact (K68 m2 cc1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc1 ART2 MI ST (pres_fp_refl _ _ _ _ _) SP LSH ENH J12 CBK J16 FSZ RATE LOOK HC). }

unfold A_lib_get_mode_h in Hc1. change 0xaf2c0 with A_speex_lib_get_mode in Hc1.
refine (rz_evt RT AF Σ2 PMh _ _ T cc1 (PMfd_mat_stable F0 fs0) Hc1 _ _).
{ eapply (speex_lib_get_mode_walk (hd_mode hd) S1 lo);
[lia | apply (aobj_lit RT AF Σ2 m2 _ _ ART2 lit_mode_list); unfold A_speex_mode_list, APP_TOP; lia
| exact ST | lia | lia | unfold USTACK_TOP in *; lia | exact (af_client_consts RT AF Σ2 m2 ART2) | exact (AF_LIB _ _ ART2) | exact MI]. }
intros ms2 cc2 (g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & g8 & g9 & g10 & g11 & g12 & g13 & m3 & -> & MU3 & WM3 & MI3 & ST3) Hc2. clear Hc1.
pose proof (art_munch_below Σ2 m2 m3 ART2 ESP MU3 WM3) as ART3.
assert (PR3 : rt_pres_fp (rt_live RT Σ2) [(F, 8%nat)] S1 [] m2 m3).
{ apply (pres_fp_of_munch _ _ _ _ _ m2 m3 MU3). intros x Hx _. cbn [outside]. split; [| exact I].
intros Hin. destruct Hx as [H|[H|[H|[H|H]]]]; [lia| pose proof (client_static_range _ H); unfold SEGTOP_A in *; unfold RT_STACK, H_STACK in LR; lia| | |].
- destruct H as (p & q & Hpq & Hx). destruct (af_live_range RT AF Σ2 m2 p q ART2 Hpq) as (_ & PL & _). rewrite ESP in PL.
pose proof (hi_lo _ _ _ HX) as (LW0 & _). lia.
- destruct H as (f & k & [E|[]] & Hx). injection E as <- <-. change (fs_size 8) with 16384 in Hx. lia.
- destruct H as (f & k & [E|[]] & Hx). injection E as <- <-. change (fs_size 8) with 16384 in Hx. unfold SH_LO, SH_HI in *. lia. }
assert (PRh : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 W_h m2 m3).
{ apply (pres_fp_weaken _ _ _ [] _ m2 m3); [| intros x _; exact I].
apply (pres_fp_mono _ _ _ (rt_live RT Σ2) [(F, 8%nat)] S1 [] m2 m3 PR3); [intros e He; rewrite EL2; right; exact He| intros e He; exact He| lia]. }
unfold HO_FSZ, HO_RATE, HO_LOOK in FSZ, RATE, LOOK.
hp_tr PR3 LSH. hp_tr PR3 ENH. hp_tr PR3 J12. hp_tr PR3 CBK. hp_tr PR3 J16. hp_tr PR3 FSZ. hp_tr PR3 RATE. hp_tr PR3 LOOK.
assert (HCS : cells_size (spx_header_cells junk28 hd w1 w2 w3 r1' r2') = 80%nat) by reflexivity.
eapply (htr_rw _ _ _ _ _ _ PR3) in HC; rewrite ?HCS; [| hp_acl | hp_rng].
eapply (htr_rw _ _ _ _ _ _ PR3) in SP; [| unfold h_spill; rewrite hsp_size; hp_acl | unfold h_spill; rewrite hsp_size; hp_rng].

refine (rz_evt RT AF Σ2 PMh _ _ T cc2 (PMfd_mat_stable F0 fs0) Hc2 _ _).
{ eapply hp_w2g; [reflexivity | exact MI3]. }
intros ms4 cc4 -> Hc4. clear Hc2.
exact (K68 m3 cc4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc4 ART3 MI3 ST3 PRh SP LSH ENH J12 CBK J16 FSZ RATE LOOK HC).
Qed.

End HP.

Lemma h_CB8_C8 : forall (m : mem) A j, rw_cells asegs m A [CB 8 j] -> exists w : word, rw_cells asegs m A [C8 w].
Proof.
intros m A j H. assert (L : length j = (8 * 1)%nat) by (destruct H as [[[Hwf _] _] _]; exact Hwf).
destruct (CB_C8s_h 1 j L) as (ws & Lws & E). destruct ws as [|w [|? ?]]; try discriminate Lws. exists w.
eapply rw_cells_recast; [exact H| cbn; tauto|]. cbn [map cells_bytes cbytes] in *. rewrite ?app_nil_r in *. exact E.
Qed.

Ltac hp_acl := first
[ apply acl_stack; unfold USTACK_TOP in *; lia
| apply (acl_frame _ [(x_F X, 8%nat)] _ (x_F X) 8 _ _ (or_introl eq_refl)); change (fs_size 8) with 16384; lia
| apply (acl_fshadow _ [(x_F X, 8%nat)] _ (x_F X) 8 _ _ (or_introl eq_refl)); change (fs_size 8) with 16384; lia
| match goal with H : In (?p, ?q) ?L |- acl_rng ?L _ _ _ _ => apply (acl_live _ _ _ p q _ _ H); lia end ].
Ltac hp_rng := repeat (first [ apply rng_out_nil | apply rng_out_cons; [unfold SH_LO, SH_HI in *; lia|] ]).
Ltac hp_tr PR H := eapply (htr_rw _ _ _ _ _ _ PR) in H; cbn [cells_size csize Nat.add] in H |- *; [| hp_acl | hp_rng].

Hypothesis FD2 : fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Hypothesis P2H2 : speex_packet_to_header_cps RT OUT_rep ERR_rep IO_FP.
Hypothesis CTL : forall d, ctl_cps_at RT d.
Hypothesis INIT8 : forall mo, init_cps_at8 RT mo.

Theorem h_hdr_ok : h_hdr_cps RT OUT_rep ERR_rep IO_FP X F0 fs0.
Proof.
intros _ h op pno nbr brem0 q q' r bs PRUN EB T c Hc Hk.
destruct Hc as (Σ1 & a & Fx & fc & m0 & ra & t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & j0 & j192 & j200 & gw & ogc & kc
& Hc & FRM & HS1 & HIT & SI1 & EOS0 & PC0 & PN0 & HR0 & OGJ & KCS & PK0 & PK1 & PK2 & BUD).
destruct (hdr_prun h _ _ q r q' PRUN) as (r1 & P1 & RM). clear PRUN.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS1 as (EL1 & ND1 & PERM1 & EF1 & ESP1 & EPO1 & ECR1).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m0 a h (proj1 HR0) HS1) as HSP.
pose proof HR0 as (ART0 & MI0 & ST0 & PF0 & ERR0 & OUTR0 & SSP0 & SP0 & LSH0 & (je & ENH0) & _ & FSZ0 & _ & _ & _ & OPC0 & OSR0 & _ & RATE0 & (wl & LOOK0)
& DEC0 & HP0).
assert (INF : In (F, 8%nat) (rt_frames RT Σ1)) by (rewrite EF1; left; reflexivity).

unfold HO_ENH in ENH0.
cb_cut ENH0 4%nat ENHa. cb_cut ENH0 12%nat J12. cb_cut ENH0 4%nat C48. cb_cut ENH0 4%nat C52. cb_cut ENH0 8%nat C56. cb_cut ENH0 8%nat C64.
destruct (h_CB4_C4 asegs m0 (F + 32) [] j [] ENHa) as (we & ENH1). cbn [app] in ENH1. clear ENHa.
destruct (h_CB4_C4 asegs m0 (F + 48) [] j4 [] C48) as (c48 & C48'). cbn [app] in C48'. clear C48.
destruct (h_CB4_C4 asegs m0 (F + 52) [] j6 [] C52) as (c52 & C52'). cbn [app] in C52'. clear C52.
destruct (h_CB8_C8 m0 (F + 56) j8 C56) as (c56 & C56'). clear C56.
destruct (h_CB8_C8 m0 (F + 64) j10 C64) as (c64 & C64'). clear C64.
assert (CBK : rw_cells asegs m0 (F + 48) [C4 c48; C4 c52; C8 c56; C8 c64]).
{ change [C4 c48; C4 c52; C8 c56; C8 c64] with ([C4 c48] ++ [C4 c52] ++ [C8 c56] ++ [C8 c64]).
apply rw_cells_app; split; [exact C48'|]. cbn [cells_size csize Nat.add]. replace (F + 48 + Z.of_nat 4) with (F + 52) by lia.
apply rw_cells_app; split; [exact C52'|]. cbn [cells_size csize Nat.add]. replace (F + 52 + Z.of_nat 4) with (F + 56) by lia.
apply rw_cells_app; split; [exact C56'|]. cbn [cells_size csize Nat.add]. replace (F + 56 + Z.of_nat 8) with (F + 64) by lia. exact C64'. }
clear C48' C52' C56' C64'. rename ENH0 into J16.
assert (OWH : forall x, outside W_h x -> outside [(sf, sf + 16); (F + 32, F + 36)] x).
{ intros x Hx. unfold W_h in Hx. cbn [outside] in Hx |- *. destruct Hx as (_ & O2 & O3 & _). split; [exact O2| split; [lia| exact I]]. }

refine (rz_evt RT AF Σ1 PMh _ _ _ c (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply hp_w1a; [unfold SH_LO, SH_HI in *; lia | exact LSH0 | exact MI0]. }
intros ms1 c1 (m1 & -> & MU1 & WM1 & MI1 & LSH1) Hc1. clear Hc.
pose proof (art_munch_h Σ1 m0 m1 _ ART0 EF1 ESP1 MU1 WM1 ltac:(intros l hh [E|[]]; injection E as <- <-; right; left; lia)) as ART1.
assert (PR1 : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 [(sf, sf + 16)] m0 m1) by (apply (pf_munch_h _ m0 m1 _ _ MU1); intros x Hx; exact Hx).
assert (PW1 : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 [(sf, sf + 16); (F + 32, F + 36)] m0 m1)
by (apply (pf_munch_h _ m0 m1 _ _ MU1); intros x Hx; cbn [outside] in Hx |- *; destruct Hx as (O1 & _ & _); split; [exact O1| exact I]).
assert (ST1 : stk asegs m1 lo S1).
{ apply (stk_agree asegs m0 m1 lo S1 ST0); [| exact WM1]. apply (agree_of_munch _ m0 m1 _ MU1). intros x Hx. cbn [outside].
split; [unfold SH_LO, SH_HI in *; lia| exact I]. }
hp_tr PR1 ENH1. eapply (htr_rw _ _ _ _ _ _ PR1) in SP0; [| unfold h_spill; rewrite hsp_size; hp_acl | unfold h_spill; rewrite hsp_size; hp_rng].
clear PR1 MU1 WM1 MI0 ST0.

refine (rz_evt RT AF Σ1 PMh _ _ _ c1 (PMfd_mat_stable F0 fs0) Hc1 _ _).
{ eapply (hp_w1b (x_S1 X) (x_F X)); [unfold USTACK_TOP in *; lia | unfold USTACK_TOP in *; lia | lia | exact SP0 | exact ENH1 | exact MI1]. }
intros ms2 c2 (m2' & -> & MU2 & WM2 & MI2 & ENH2 & SP2) Hc2. clear Hc1.
pose proof (art_munch_h Σ1 m1 m2' _ ART1 EF1 ESP1 MU2 WM2 ltac:(intros l hh [E|[]]; injection E as <- <-; right; right; lia)) as ART2.
assert (PR2 : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 [(F + 32, F + 36)] m1 m2') by (apply (pf_munch_h _ m1 m2' _ _ MU2); intros x Hx; exact Hx).
assert (PW2 : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 [(sf, sf + 16); (F + 32, F + 36)] m0 m2').
{ apply (pres_fp_trans _ _ _ _ m0 m1 m2' PW1). apply (pf_munch_h _ m1 m2' _ _ MU2). intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (_ & O2 & _). split; [exact O2| exact I]. }
assert (ST2 : stk asegs m2' lo S1).
{ apply (stk_agree asegs m1 m2' lo S1 ST1); [| exact WM2]. apply (agree_of_munch _ m1 m2' _ MU2). intros x Hx. cbn [outside]. split; [lia| exact I]. }
hp_tr PR2 LSH1.
clear PR2 MU2 WM2 MI1 ST1 PW1 SP0 ENH1.

refine (rz_evt RT AF Σ1 PMh _ _ _ c2 (PMfd_mat_stable F0 fs0) Hc2 _ _).
{ eapply hp_w1c; [unfold SH_LO, SH_HI in *; lia | exact LSH1 | exact MI2]. }
intros ms3 c3 (m3 & -> & MU3 & WM3 & MI3 & LSH3) Hc3. clear Hc2.
pose proof (art_munch_h Σ1 m2' m3 _ ART2 EF1 ESP1 MU3 WM3 ltac:(intros l hh [E|[]]; injection E as <- <-; right; left; lia)) as ART3.
assert (PR3 : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 [(sf, sf + 16)] m2' m3) by (apply (pf_munch_h _ m2' m3 _ _ MU3); intros x Hx; exact Hx).
assert (PW3 : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 [(sf, sf + 16); (F + 32, F + 36)] m0 m3).
{ apply (pres_fp_trans _ _ _ _ m0 m2' m3 PW2). apply (pf_munch_h _ m2' m3 _ _ MU3). intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (O1 & _ & _). split; [exact O1| exact I]. }
assert (ST3 : stk asegs m3 lo S1).
{ apply (stk_agree asegs m2' m3 lo S1 ST2); [| exact WM3]. apply (agree_of_munch _ m2' m3 _ MU3). intros x Hx. cbn [outside].
split; [unfold SH_LO, SH_HI in *; lia| exact I]. }
hp_tr PR3 ENH2. eapply (htr_rw _ _ _ _ _ _ PR3) in SP2; [| unfold h_spill; rewrite hsp_size; hp_acl | unfold h_spill; rewrite hsp_size; hp_rng].
clear PR3 MU3 WM3 MI2 ST2 PW2 LSH1.

unfold HO_OP, HO_FSZ, HO_RATE, HO_LOOK in OPC0, FSZ0, RATE0, LOOK0.
assert (OPS : cells_size (op_cells (a_Bd a) (Some op) gw kc) = 48%nat) by reflexivity.
eapply (htr_rw _ _ _ _ _ _ PW3) in OPC0; rewrite ?OPS; [| hp_acl | hp_rng].
hp_tr PW3 J12. hp_tr PW3 CBK. hp_tr PW3 J16. hp_tr PW3 FSZ0. hp_tr PW3 RATE0. hp_tr PW3 LOOK0.
assert (LEN : pk_bytes op <= 4096).
{ pose proof (hi_pay _ _ _ HX) as (_ & SZ & _). unfold MAX_FUZZ_SIZE in SZ.
pose proof HP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BR & _ & Q1 & Q2 & _ & BF & _).
unfold h_consumed, h_pend in *. lia. }

refine (rz_evt RT AF Σ1 PMh _ _ _ c3 (PMfd_mat_stable F0 fs0) Hc3 _ _).
{ eapply (hp_w1d (x_S1 X) (x_F X) (a_Bd a) (pk_bytes op) op gw kc); [unfold USTACK_TOP in *; lia | reflexivity | lia | exact OPC0 | exact MI3]. }
intros ms4 c4 -> Hc4. clear Hc3.

pose proof OSR0 as OSR0'. unfold h_os_rep in OSR0'. destruct (Z.eqb_spec (h_stream_init h) 0) as [E0'|_]; [rewrite SI1 in E0'; discriminate E0'|].
destruct OSR0' as (OS & LH & (UB & LB & BP & UL & WP & LL & UG & LG) & FOK & SINV & BINV & LOK & GL & BD & LV & GV & LS & BS & NBL & NBG & NLG).
destruct (pk_window m0 (a_Bd a) (a_body a) (h_os h) op UB BP (proj1 BINV) PK0 PK1 PK2) as (U8 & EPD & LPB).
set (pb := firstn (Z.to_nat (pk_bytes op)) (skipn (Z.to_nat (pk_off op)) (a_body a))) in *.
rewrite <- EPD in P1.
assert (SIN : h_stream_init h <> 0) by (rewrite SI1; discriminate).
pose proof (own_in_os a h SIN) as (IBD & _ & _).
assert (INBD : In (a_Bd a, os_body_storage (h_os h)) (rt_live RT Σ1)).
{ rewrite EL1. apply in_or_app. left. exact (Permutation_in _ (Permutation_sym PERM1) IBD). }
assert (BFS : pk_off op + pk_bytes op <= os_body_storage (h_os h)).
{ destruct BP as (_ & BPL). pose proof (proj1 BINV) as ZL. unfold zlength in ZL. unfold bptr in *. lia. }
destruct (proj1 HSP _ _ IBD) as (BD0 & BDL & BDF & BDS & _).
unfold u8ro in U8. eapply (htr_bytes _ _ _ _ _ _ PW3) in U8; [| apply (acl_live _ _ _ _ _ _ _ INBD); rewrite ?LPB; unfold bptr in *; lia
| rewrite ?LPB; hp_rng].
assert (FPHW : fp_h X a h [(sf, sf + 16); (F + 32, F + 36)]) by (apply fp_h_cons; [right; left; lia| apply fp_h_cons; [right; right; left; lia| apply fp_h_nil]]).
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ1 m0 m3 a h _ _ HSP PW3
ltac:(intros e He; rewrite EL1; apply in_or_app; right; exact He) FPHW (AF_DRV _ _ ART3) PF0 ERR0 OUTR0 SSP0) as (PF3 & ERR3 & OUTR3 & SSP3).
assert (STN : h_st h = None).
{ pose proof HP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MM & _). destruct (h_st h); [exfalso; exact (MM PC0)| reflexivity]. }
assert (LVR : Z.of_nat (length (rt_live RT Σ1)) < LIVE_MAX).
{ rewrite EL1, length_app, (Permutation_length PERM1). assert (OL : (length (h_own a h) <= 5)%nat) by (unfold h_own; rewrite STN; cbn [app length]; destruct (h_stream_init h =? 0); destruct (sy_data (h_oy h)); cbn [length app]; lia).
pose proof (hi_live _ _ _ HX) as (_ & LL0). unfold H_LIVE, LIVE_MAX in *. lia. }

edestruct (P2H2 Σ1 F0 fs0 (Z64 0x96e8c) (Z64 S1) (x_gp X) (Z64 0x630458) t0 t1 t2 (Z64 usp) (Z64 S1) (Z64 (a_Bd a + pk_off op)) (Z64 (pk_bytes op))
a2 a3 a4 a5 a6 a7 (Z64 (F + 8608)) (Z64 sf) (Z64 (F + HO_OUT)) (Z64 (F + HO_OG)) (Z64 (h_packet_count h)) (Z64 (F + HO_OS)) (Z64 (F + 32))
(Z64 (a_S a)) (Z64 (pk_bytes op)) (Z64 (F + HO_BITS)) t3 t4 t5 t6 Fx fc m3 (a_Bd a + pk_off op) (a_Bd a) (os_body_storage (h_os h)) lo
pb (pk_bytes op) q q' r1 P1) as (bs0 & EB0 & CP).
{ reflexivity. } { reflexivity. } { reflexivity. }
{ exact U8. } { rewrite LPB. lia. } { lia. } { unfold bptr in *. lia. }
{ exact INBD. } { lia. } { rewrite LPB. unfold bptr in *. lia. }
{ exact FD2. } { exact ERR3. } { exact SSP3. } { exact LVR. }
{ exact (af_credit_nonneg RT AF Σ1 m3 ART3). }
{ rewrite EPO1. apply pois_above_nil. }
{ exists [0x96564]. split; [clear; vm_compute; tauto|]. rewrite !unsigned_lit by (unfold USTACK_TOP in *; lia). exact (h_uw_chain m3 PF3). }
{ exact ART3. } { exact MI3. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). exact ST3. }
{ rewrite ESP1. exact LW. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold RT_STACK. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). clear - S32. Z.div_mod_to_equations. lia. }
assert (EBS : bs = bs0) by (rewrite EB in EB0; exact (app_inv_head _ _ _ EB0)). subst bs0.
unfold A_p2h_h in Hc4. change 0x9941c with A_speex_packet_to_header in Hc4.
apply (CP T c4 Hc4). clear CP.
intros c5 (Σ2 & v & Hc5 & LEN2 & EF2 & ES2 & EC2 & EP2). clear Hc4.
Time cps_unpack_lib Hc5 as (m2 & RS & RA2 & PR2 & ERR2 & OUT12 & P2R).
destruct RA2 as (ART4 & MI4 & ST4).
pose proof (RS FRM) as FRM2. clear RS.
rewrite EF1 in PR2.
assert (PF02 : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 (W_h ++ IO_FP) m0 m2).
{ apply (pres_fp_trans _ _ _ _ m0 m3 m2).
- apply (pres_fp_weaken _ _ _ _ _ m0 m3 PW3). intros x Hx. apply outside_app_iff in Hx. exact (OWH x (proj1 Hx)).
- apply (pres_fp_weaken _ _ _ _ _ m3 m2 PR2). intros x Hx. apply outside_app_iff in Hx. exact (proj2 Hx). }
destruct (h_io_step_io OUT_rep IO_FP IO_img IO_drv X HX m0 m2 a h (rt_live RT Σ1) W_h HSP PF02
ltac:(intros e He; rewrite EL1; apply in_or_app; right; exact He) (fp_h_Wh a h) (AF_DRV _ _ ART4) PF0 SSP0) as (PFR2 & SSP2).
assert (OUT2 : forall so, OUT_rep so mR -> OUT_rep so m2) by (intros so Hso; exact (OUT12 so (OUTR3 so Hso))).

Ltac hp_rng_io := first [ apply (rng_out_img IO_FP _ _ IO_img); right; unfold SEGTOP_A, SH_LO, SH_HI in *; lia ].
eapply (htr_rw _ _ _ _ _ _ PR2) in SP2; [| unfold h_spill; rewrite hsp_size; hp_acl | unfold h_spill; rewrite hsp_size; hp_rng_io].
Ltac hp_tr_io PR H := eapply (htr_rw _ _ _ _ _ _ PR) in H; cbn [cells_size csize Nat.add] in H |- *; [| hp_acl | hp_rng_io].
hp_tr_io PR2 LSH3. hp_tr_io PR2 ENH2. hp_tr_io PR2 J12. hp_tr_io PR2 CBK. hp_tr_io PR2 J16. hp_tr_io PR2 FSZ0. hp_tr_io PR2 RATE0. hp_tr_io PR2 LOOK0.
clear PR2.

assert (Hk' : forall c', match (match r1 with None => None | Some (_, hd) => hdr_tail h hd end) with
| None => at_XT RT OUT_rep ERR_rep IO_FP X F0 fs0 c'
| Some h3 => at_KH RT OUT_rep ERR_rep IO_FP X F0 fs0 (incr_packet_count h3) pno nbr brem0 c'
end -> realizes asegs c' T).
{ intros c' Hc'. apply Hk. destruct r1 as [[[] hd]|].
- destruct P2R as (junk28 & w1 & w2 & w3 & r1' & r2' & _ & _ & _ & _ & _ & _ & RM' & _). cbv [X1rg.SPEEX_NB_MODES X1rh.SPEEX_NB_MODES] in RM'.
rewrite (RM RM'). exact Hc'.
- rewrite RM. exact Hc'. }
clear Hk RM.
eapply (hp_ap h op pno nbr brem0 a Σ1 m0 j0 j192 j200 gw ogc kc HS1 HIT SI1 EOS0 PC0 PN0 HR0 OGJ KCS (conj PK0 (conj PK1 PK2)) BUD m2 PF02 PFR2 ERR2 OUT2 SSP2
CTL INIT8 Σ2 c5 T v r1);
[exact Hc | exact FRM2 | rewrite EF2; exact EF1 | rewrite ES2; exact ESP1 | rewrite EP2; exact EPO1 | exact EC2 | exact ART4 | exact MI4
| first [exact ST4 | rewrite unsigned_lit in ST4 by (unfold USTACK_TOP in *; lia); exact ST4]
| exact P2R | exact SP2 | exact LSH3 | exact ENH2 | exact J12 | exact CBK | exact J16 | exact FSZ0 | exact RATE0 | exact LOOK0 | exact Hk'].
Qed.

End Hdr.
