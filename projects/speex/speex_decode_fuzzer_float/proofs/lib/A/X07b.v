(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1nt X1rg X1rh X1re X1od X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00a X00b X000 X04b X00c X07z X05o X05s X05t
X0ae X09u X09x X0af X09p X0a4 X0a5 X05l X05e X05c
X05m X09f X06d X069 X068 X07m
X09j X071 X06v X06y X06u X073 X07j X072 X079 X07h X07e.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X12c X14x X0r0 X0r9 X0ra X0qz X0v9 X0rb X0wl X0wm X110 X10j X10c X10q X10r X0wb X0w9 X0x2 X0x1 X106 X0xn X0xq X0xm X0xu X0ya X0xt X0y0 X0y8 X0y5.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10r OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X106 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xu OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ya OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y8 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y5.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).

Lemma packetout_same : forall (os os' : stream_st bptr) r opo, ogg_stream_packetout os = Some ((r, opo), os') ->
os_lacing os' = os_lacing os /\ os_granules os' = os_granules os /\ os_body os' = os_body os
/\ os_body_data os' = os_body_data os /\ os_lacing_vals os' = os_lacing_vals os /\ os_granule_vals os' = os_granule_vals os
/\ os_body_storage os' = os_body_storage os /\ os_lacing_storage os' = os_lacing_storage os
/\ os_body_fill os' = os_body_fill os /\ os_lacing_fill os' = os_lacing_fill os /\ os_serialno os' = os_serialno os.
Proof.
intros os os' r opo H. unfold ogg_stream_packetout, packetout in H.
destruct (ogg_stream_check os); [injection H as _ _ <-; repeat split; reflexivity|].
destruct (_ <=? _); [injection H as _ _ <-; repeat split; reflexivity|].
destruct (negb _); [injection H as _ _ <-; cbn; repeat split; reflexivity|].
destruct (gather255 _ _ _ _ _) as [[[n eos] bytes]|]; [injection H as _ _ <-; cbn; repeat split; reflexivity| discriminate H].
Qed.

Lemma packetout_os_pure : forall (os os' : stream_st bptr) r opo, os_pure os -> ogg_stream_packetout os = Some ((r, opo), os') -> stream_fields_ok os' ->
os_pure os' /\ os_lacing_returned os <= os_lacing_returned os' <= os_lacing_fill os
/\ (r = 1 -> opo <> None /\ os_lacing_returned os < os_lacing_returned os')
/\ match opo with Some p => 0 <= pk_off p /\ 0 <= pk_bytes p /\ pk_off p + pk_bytes p <= os_body_fill os /\ zlength (packet_data os' p) = pk_bytes p
| None => True end.
Proof.
intros os os' r opo (FOK & SINV & BINV & LOK & GL & BD & LV & GV & LS & BS) E FOK'.
destruct (packetout_same os os' r opo E) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
destruct (ogg_stream_packetout_frame os r opo os' SINV E) as (SINV' & _ & _ & _ & _ & _ & _ & _ & _ & RR & R1 & _).
destruct (ogg_stream_packetout_body_inv os r opo os' SINV BINV E) as (BINV' & _ & _ & PK).
split.
{ unfold os_pure. rewrite E1, E2, E4, E5, E6, E7, E8. split; [exact FOK'|]. split; [exact SINV'|]. split; [exact BINV'|].
repeat split; assumption. }
split; [exact RR|]. split; [exact R1| exact PK].
Qed.

Section PkStep.
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
Local Notation S1 := (x_S1 X). Local Notation lo := (x_lo X). Local Notation F := (x_F X). Local Notation sf := (x_sf X).

Lemma outside_IO_of_WL : forall x, outside (h_WL IO_FP X) x -> outside IO_FP x.
Proof. intros x H. unfold h_WL in H. cbn [outside] in H. destruct H as (_ & _ & _ & H). exact H. Qed.

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
+ apply (fp_h_static OUT_rep IO_FP X HX a h W HSP FPH). unfold SSP_GUARD, SEGTOP_A in *. lia.
+ apply outside_of_not_in_ranges'. intros Hin. apply (IO_drv x Hin). unfold drv_cell. right; left; exact Hx.
Qed.

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

Lemma hrep_packetout : forall (Σ1 : rts RT) (m m1 : mem) a (h : hstate unit) spill ogc opc r opo (os' : stream_st unit) gw,
hsig RT X Σ1 a h -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 248%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat ->
h_stream_init h <> 0 -> ogg_stream_packetout (h_os h) = Some ((r, opo), os') ->
munch [(F + 8688, F + 8688 + 408); (F + 8608, F + 8608 + 48)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
rw_cells bsegs m1 (F + 8688) (stream_cells (a_Bd a) (a_L a) (a_G a) (a_shdr a) os') -> stream_fields_ok os' ->
rw_cells bsegs m1 (F + 8608) (op_cells (a_Bd a) opo gw opc) ->
hsig RT X Σ1 a (set_ogg h (h_oy h) os')
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ1 m1 a (set_ogg h (h_oy h) os') spill ogc (op_cells (a_Bd a) opo gw opc)
/\ os_lacing_returned (h_os h) <= os_lacing_returned os'
/\ (r = 1 -> opo <> None /\ os_lacing_returned (h_os h) < os_lacing_returned os')
/\ match opo with Some p => 0 <= pk_off p /\ 0 <= pk_bytes p /\ pk_off p + pk_bytes p <= os_body_fill (h_os h) /\ zlength (packet_data os' p) = pk_bytes p
| None => True end.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV.
intros Σ1 m m1 a h spill ogc opc r opo os' gw HS HR SPS OGS OPS SI E MU WM MI1 OS1 FOK1 OP1.
destruct HR as (ART0 & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC & OSR & (stb & STB)
& RATE & (wl & LOOK & LKR) & DEC & HP).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART0 HS) as HSP.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }

unfold h_os_rep in OSR. destruct (Z.eqb_spec (h_stream_init h) 0) as [E0|_]; [exfalso; exact (SI E0)|].
destruct OSR as (_ & LH & (UB & LB & BP & UL & WP & LL & UG & LG) & FOK & SINV & BINV & LOK & GL & BD & LV & GV & LS & BS & NBL & NBG & NLG).
destruct (packetout_same (h_os h) os' r opo E) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
destruct (packetout_os_pure (h_os h) os' r opo (conj FOK (conj SINV (conj BINV (conj LOK (conj GL (conj BD (conj LV (conj GV (conj LS BS))))))))) E FOK1)
as (POS' & RR & R1 & PK).
unfold bptr in *.

assert (PR : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 [(F + 8688, F + 8688 + 408); (F + 8608, F + 8608 + 48)] m m1).
{ apply (pres_fp_of_munch _ _ _ _ _ m m1 MU). intros x _ Ho. exact Ho. }
assert (ART1 : ART RT Σ1 m1).
{ apply (af_frame RT AF Σ1 m m1 S1 ART0); [rewrite ESP; pose proof (hi_lo _ _ _ HX) as (LW0 & _); unfold STACK_WIN in *; lia| | exact WM].
intros b Hb. apply MU. cbn [outside]. rewrite EF in Hb.
split; [intros Hin; apply Hb; exact (acl_frame (rt_live RT Σ1) [(F, 8%nat)] S1 F 8 (F + 8688) 408 INF ltac:(lia) ltac:(change (fs_size 8) with 16384; lia) _ Hin)|].
split; [intros Hin; apply Hb; exact (acl_frame (rt_live RT Σ1) [(F, 8%nat)] S1 F 8 (F + 8608) 48 INF ltac:(lia) ltac:(change (fs_size 8) with 16384; lia) _ Hin)|].
exact I. }
assert (ST1 : stk bsegs m1 lo S1).
{ apply (stk_agree bsegs m m1 lo S1 ST); [| exact WM]. apply (agree_of_munch _ m m1 _ MU). intros x Hx. cbn [outside].
change (fs_size 8) with 16384 in FL. split; [lia|]. split; [lia| exact I]. }
unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK in *.
change (fs_size 8) with 16384 in *.
assert (FRT : forall A cs, rw_cells bsegs m A cs -> F + 32 <= A -> A + Z.of_nat (cells_size cs) <= F + 9252 ->
(A + Z.of_nat (cells_size cs) <= F + 8688 \/ F + 9096 <= A) -> (A + Z.of_nat (cells_size cs) <= F + 8608 \/ F + 8656 <= A) ->
rw_cells bsegs m1 A cs).
{ intros A cs C H1 H2 H3 H4. apply (htr_rw _ _ _ _ m m1 PR _ _ C); [apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (ENH' : rw_cells bsegs m1 (F + 32) [CB 56 je]) by (apply (FRT _ _ ENH); cbn [cells_size csize Nat.add]; lia).
assert (OUTB' : rw_cells bsegs m1 (F + 128) (f32 ows)) by (apply (FRT _ _ OUTB); rewrite ?cells_size_f32, ?LOWS; lia).
assert (FSZ' : rw_cells bsegs m1 (F + 8384) [C4 (Z_to_bv 64 (h_frame_size h))]) by (apply (FRT _ _ FSZ); cbn [cells_size csize Nat.add]; lia).
assert (OGC' : rw_cells bsegs m1 (F + 8544) ogc) by (apply (FRT _ _ OGC); rewrite ?OGS; lia).
assert (STB' : rw_cells bsegs m1 (F + 9168) [CB 24 stb]) by (apply (FRT _ _ STB); cbn [cells_size csize Nat.add]; lia).
assert (RATE' : rw_cells bsegs m1 (F + 9232) [C4 (Z_to_bv 64 (h_rate h))]) by (apply (FRT _ _ RATE); cbn [cells_size csize Nat.add]; lia).
assert (LOOK' : rw_cells bsegs m1 (F + 9248) [C4 (Z_to_bv 64 wl)]) by (apply (FRT _ _ LOOK); cbn [cells_size csize Nat.add]; lia).
clear FRT ENH OUTB FSZ OGC STB RATE LOOK.
assert (SP' : rw_cells bsegs m1 S1 spill).
{ apply (htr_rw _ _ _ _ m m1 PR _ _ SP); rewrite SPS; [apply acl_stack; lia|]. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (LSH' : rw_cells bsegs m1 sf [CB 16 HSH_P1]).
{ apply (htr_rw _ _ _ _ m m1 PR _ _ LSH); cbn [cells_size csize Nat.add]; [apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
unfold SH_HI in *. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (OWNTR : forall p q, In (p, q) (h_own a h) -> acl_rng (rt_live RT Σ1) [(F, 8%nat)] S1 p q /\ rng_out [(F + 8688, F + 8688 + 408); (F + 8608, F + 8608 + 48)] p q).
{ intros p q Hin. split; [apply (acl_live _ _ _ _ _ _ _ (INL _ Hin)); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); lia|]. apply rng_out_nil. }
assert (BOK : bits_ok (h_bits h)) by (destruct HP as (_ & _ & _ & _ & B & _); exact B).
assert (BITS' : bits_rep bsegs m1 (F + 8400) (a_Dc a) (h_bits h)).
{ destruct (OWNTR _ _ (own_in_Dc a h)) as (D1 & D2).
apply (bits_rep_tr _ _ _ _ m m1 PR _ _ _ BITS BOK); [| | exact D1| exact D2].
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (SY' : sync_rep m1 (F + 8480) (a_Dsy a) (h_oy h) (a_sybytes a)).
{ apply (sync_rep_tr _ _ _ _ m m1 PR _ _ _ _ SY).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil.
- intros NS. exact (OWNTR _ _ (own_in_Dsy a h NS)). }
assert (DEC' : h_dec_rep X m1 a h).
{ apply (h_dec_rep_tr _ _ _ _ m m1 PR X a h DEC). intros b Hb.
assert (NS0 : h_st h <> None) by (unfold h_dec_rep in DEC; destruct (h_st h); [discriminate| destruct DEC as (_ & E'); rewrite E' in Hb; destruct Hb]).
apply (OWNTR _ _ (own_in_blk a h NS0 b Hb)). }
destruct (own_in_os a h SI) as (IB & IL & IG).
destruct (OWNTR _ _ IB) as (B1 & B2). destruct (OWNTR _ _ IL) as (L1 & L2). destruct (OWNTR _ _ IG) as (G1 & G2).
assert (OSR' : h_os_rep X m1 a (set_ogg h (h_oy h) os')).
{ apply h_os_rep_intro; cbn [set_ogg h_os h_stream_init].
- exact SI.
- unfold HO_OS. exact OS1.
- exact LH.
- unfold stream_arrays, bptr. rewrite E1, E3, E7, E8.
split; [apply (htr_u8 _ _ _ _ m m1 PR _ _ UB); rewrite LB; assumption|]. split; [exact LB|]. split; [exact BP|].
split; [apply (htr_u32 _ _ _ _ m m1 PR _ _ UL); rewrite LL; assumption|]. split; [exact WP|]. split; [exact LL|].
split; [apply (htr_u64 _ _ _ _ m m1 PR _ _ UG); rewrite LG; assumption| exact LG].
- exact POS'.
- exact NBL. - exact NBG. - exact (proj1 NLG). - exact (proj1 (proj2 NLG)). - rewrite E7. exact (proj2 (proj2 NLG)). }
clear DEC BITS OWNTR SY.
assert (FPH : fp_h X a h [(F + 8688, F + 8688 + 408); (F + 8608, F + 8608 + 48)])
by (apply fp_h_cons; [right; right; left; lia| apply fp_h_cons; [right; right; left; lia| apply fp_h_nil]]).
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ1 m m1 a h _ _ HSP PR
ltac:(intros e He; rewrite EL; apply in_or_app; right; exact He) FPH (AF_DRV _ _ ART1) PF ERR OUTR SSP) as (PF' & ERR' & OUTR' & SSP').
assert (HP' : hpure X (set_ogg h (h_oy h) os')).
{ rewrite set_ogg_with.
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P17 & _ & _ & _ & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
apply hpure_with_os; [exact HP| exact P17| ..]; unfold h_consumed, h_pend in *; rewrite ?E7, ?E8, ?E9, ?E10; lia. }
split.
{ unfold hsig. assert (EOWN : h_own a (set_ogg h (h_oy h) os') = h_own a h).
{ unfold h_own. cbn [set_ogg h_oy h_os h_bits h_st h_stream_init]. rewrite E7, E8. reflexivity. }
rewrite EOWN. unfold h_cost in *. cbn [set_ogg h_packet_count]. exact HS. }
split.
{ unfold hrep. unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK.
cbn [set_ogg h_oy h_os h_bits h_st h_frame_size h_rate].
split; [exact ART1|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact PF'|]. split; [exact ERR'|]. split; [exact OUTR'|]. split; [exact SSP'|].
split; [exact SP'|]. split; [exact LSH'|]. split; [exists je; exact ENH'|]. split; [exists ows; split; [exact OUTB'| exact LOWS]|].
split; [exact FSZ'|]. split; [exact BITS'|]. split; [exact SY'|]. split; [exact OGC'|]. split; [exact OP1|].
split; [unfold HO_OS in OSR'; exact OSR'|]. split; [exists stb; exact STB'|]. split; [exact RATE'|]. split; [exists wl; split; [exact LOOK'| first [exact LKR | (let HH := fresh in intros HH; apply LKR; congruence)]]|].
split; [| exact HP']. unfold h_dec_rep in DEC' |- *. cbn [set_ogg h_st]. exact DEC'. }
split; [exact (proj1 RR)|]. split; [exact R1| exact PK].
Qed.

Lemma hrep_out_step : forall (Σ1 : rts RT) (m m1 : mem) a (h : hstate unit) spill ogc opc (ws' : list word) (stb' : list byte) k,
hsig_k RT X Σ1 a h k -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 248%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat ->
munch [(F + 128, F + 8128); (F + 9168, F + 9192); (S1 + -64, S1)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> stk bsegs m1 lo S1 ->
rw_cells bsegs m1 (F + 128) (f32 ws') -> length ws' = 2000%nat -> rw_cells bsegs m1 (F + 9168) [CB 24 stb'] ->
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m1 a h spill ogc opc.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV.
intros Σ1 m m1 a h spill ogc opc ws' stb' k HS HR SPS OGS OPS MU WM MI1 ST1 OUT1 LOW1 STB1.
destruct HR as (ART0 & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC & OSR & (stb & STB)
& RATE & (wl & LOOK & LKR) & DEC & HP).
pose proof (hsep_of_k Σ1 m a h k ART0 HS) as HSP.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
pose proof (hi_lo _ _ _ HX) as (LW0 & _).

assert (PR : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 [(F + 128, F + 8128); (F + 9168, F + 9192)] m m1).
{ apply (pres_fp_of_munch _ _ _ _ _ m m1 MU). intros x Hx Ho. cbn [outside] in Ho |- *. destruct Ho as (O1 & O2 & _).
split; [exact O1|]. split; [exact O2|]. split; [| exact I].
rewrite <- EF in Hx. destruct (aclient_split RT AF Σ1 m S1 x ART0 Hx) as [XH|XL]; [lia| rewrite ESP in XL; unfold STACK_WIN in *; lia]. }
assert (ART1 : ART RT Σ1 m1).
{ apply (af_frame RT AF Σ1 m m1 (S1 + -64) ART0); [rewrite ESP; unfold STACK_WIN in *; lia| | exact WM].
intros b Hb. apply MU. cbn [outside]. rewrite EF in Hb.
split; [intros Hin; apply Hb; exact (acl_frame (rt_live RT Σ1) [(F, 8%nat)] (S1 + -64) F 8 (F + 128) 8000 INF ltac:(lia) ltac:(change (fs_size 8) with 16384; lia) (bv_unsigned b) ltac:(lia))|].
split; [intros Hin; apply Hb; exact (acl_frame (rt_live RT Σ1) [(F, 8%nat)] (S1 + -64) F 8 (F + 9168) 24 INF ltac:(lia) ltac:(change (fs_size 8) with 16384; lia) (bv_unsigned b) ltac:(lia))|].
split; [intros Hin; apply Hb; apply (acl_stack (rt_live RT Σ1) [(F, 8%nat)] (S1 + -64) (S1 + -64) 64 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) (bv_unsigned b)); lia| exact I]. }
unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK in *.
change (fs_size 8) with 16384 in *.
assert (FRT : forall A cs, rw_cells bsegs m A cs -> F + 32 <= A -> A + Z.of_nat (cells_size cs) <= F + 9252 ->
(A + Z.of_nat (cells_size cs) <= F + 128 \/ F + 8128 <= A) -> (A + Z.of_nat (cells_size cs) <= F + 9168 \/ F + 9192 <= A) ->
rw_cells bsegs m1 A cs).
{ intros A cs C H1 H2 H3 H4. apply (htr_rw _ _ _ _ m m1 PR _ _ C); [apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (ENH' : rw_cells bsegs m1 (F + 32) [CB 56 je]) by (apply (FRT _ _ ENH); cbn [cells_size csize Nat.add]; lia).
assert (FSZ' : rw_cells bsegs m1 (F + 8384) [C4 (Z_to_bv 64 (h_frame_size h))]) by (apply (FRT _ _ FSZ); cbn [cells_size csize Nat.add]; lia).
assert (OGC' : rw_cells bsegs m1 (F + 8544) ogc) by (apply (FRT _ _ OGC); rewrite ?OGS; lia).
assert (OPC' : rw_cells bsegs m1 (F + 8608) opc) by (apply (FRT _ _ OPC); rewrite ?OPS; lia).
assert (RATE' : rw_cells bsegs m1 (F + 9232) [C4 (Z_to_bv 64 (h_rate h))]) by (apply (FRT _ _ RATE); cbn [cells_size csize Nat.add]; lia).
assert (LOOK' : rw_cells bsegs m1 (F + 9248) [C4 (Z_to_bv 64 wl)]) by (apply (FRT _ _ LOOK); cbn [cells_size csize Nat.add]; lia).
clear FRT ENH OUTB FSZ OGC OPC STB RATE LOOK.
assert (SP' : rw_cells bsegs m1 S1 spill).
{ apply (htr_rw _ _ _ _ m m1 PR _ _ SP); rewrite SPS; [apply acl_stack; lia|]. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (LSH' : rw_cells bsegs m1 sf [CB 16 HSH_P1]).
{ apply (htr_rw _ _ _ _ m m1 PR _ _ LSH); cbn [cells_size csize Nat.add]; [apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
unfold SH_HI in *. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (OWNTR : forall p q, In (p, q) (h_own a h) -> acl_rng (rt_live RT Σ1) [(F, 8%nat)] S1 p q /\ rng_out [(F + 128, F + 8128); (F + 9168, F + 9192)] p q).
{ intros p q Hin. split; [apply (acl_live _ _ _ _ _ _ _ (INL _ Hin)); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); lia|]. apply rng_out_nil. }
assert (BOK : bits_ok (h_bits h)) by (destruct HP as (_ & _ & _ & _ & B & _); exact B).
assert (BITS' : bits_rep bsegs m1 (F + 8400) (a_Dc a) (h_bits h)).
{ destruct (OWNTR _ _ (own_in_Dc a h)) as (D1 & D2).
apply (bits_rep_tr _ _ _ _ m m1 PR _ _ _ BITS BOK); [| | exact D1| exact D2].
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (SY' : sync_rep m1 (F + 8480) (a_Dsy a) (h_oy h) (a_sybytes a)).
{ apply (sync_rep_tr _ _ _ _ m m1 PR _ _ _ _ SY).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil.
- intros NS. exact (OWNTR _ _ (own_in_Dsy a h NS)). }
assert (OSR' : h_os_rep X m1 a h).
{ apply (h_os_rep_tr _ _ _ _ m m1 PR X a h OSR).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- unfold HO_OS. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
destruct (OWNTR _ _ IB) as (B1 & B2). destruct (OWNTR _ _ IL) as (L1 & L2). destruct (OWNTR _ _ IG) as (G1 & G2).
exact (conj B1 (conj B2 (conj L1 (conj L2 (conj G1 G2))))). }
assert (DEC' : h_dec_rep X m1 a h).
{ apply (h_dec_rep_tr _ _ _ _ m m1 PR X a h DEC). intros b Hb.
assert (NS0 : h_st h <> None) by (unfold h_dec_rep in DEC; destruct (h_st h); [discriminate| destruct DEC as (_ & E'); rewrite E' in Hb; destruct Hb]).
apply (OWNTR _ _ (own_in_blk a h NS0 b Hb)). }
clear OSR DEC BITS OWNTR SY.
assert (FPH : fp_h X a h [(F + 128, F + 8128); (F + 9168, F + 9192)])
by (apply fp_h_cons; [right; right; left; lia| apply fp_h_cons; [right; right; left; lia| apply fp_h_nil]]).
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ1 m m1 a h _ _ HSP PR
ltac:(intros e He; rewrite EL; apply in_or_app; right; exact He) FPH (AF_DRV _ _ ART1) PF ERR OUTR SSP) as (PF' & ERR' & OUTR' & SSP').
unfold hrep. unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK.
split; [exact ART1|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact PF'|]. split; [exact ERR'|]. split; [exact OUTR'|]. split; [exact SSP'|].
split; [exact SP'|]. split; [exact LSH'|]. split; [exists je; exact ENH'|]. split; [exists ws'; split; [exact OUT1| exact LOW1]|].
split; [exact FSZ'|]. split; [exact BITS'|]. split; [exact SY'|]. split; [exact OGC'|]. split; [exact OPC'|].
split; [unfold HO_OS in OSR'; exact OSR'|]. split; [exists stb'; exact STB1|]. split; [exact RATE'|]. split; [exists wl; split; [exact LOOK'| first [exact LKR | (let HH := fresh in intros HH; apply LKR; congruence)]]|].
split; [exact DEC'| exact HP].
Qed.

Definition a_set_dc (a : haux) (D : Z) (P : list (Z * Z)) : haux :=
HA (a_Dsy a) (a_sybytes a) (a_Bd a) (a_L a) (a_G a) (a_shdr a) (a_body a) (a_lws a) (a_gws a) D (a_S a) (a_LBD a) P.

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

Lemma hrep_rf : forall (Σ1 Σ2 : rts RT) (m m' : mem) a (h : hstate unit) spill ogc opc k len D' (b' : bits_st unit),
hsig_k RT X Σ1 a h k -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 248%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat ->
rt_after_f RT Σ2 S1 lo m m' ->
rt_pres_fp (live_remove (a_Dc a) (rt_live RT Σ1)) (rt_frames RT Σ1) S1 ((F + 8400, F + 8400 + 48) :: IO_FP) m m' ->
bits_rep bsegs m' (F + 8400) D' b' -> bits_ok b' -> sb_owner b' = 1 -> 2000 <= sb_buf_size b' <= 64512 ->
ERR_rep m' -> (forall so, OUT_rep so m -> OUT_rep so m') ->
((len <= sb_buf_size (h_bits h) /\ D' = a_Dc a /\ rt_live RT Σ2 = rt_live RT Σ1 /\ sb_buf_size b' = sb_buf_size (h_bits h))
\/ (sb_buf_size (h_bits h) < len /\ rt_live RT Σ2 = (D', len) :: live_remove (a_Dc a) (rt_live RT Σ1) /\ sb_buf_size b' = len)) ->
rt_frames RT Σ2 = rt_frames RT Σ1 -> rt_sp0 RT Σ2 = rt_sp0 RT Σ1 -> rt_credit RT Σ2 = rt_credit RT Σ1 -> rt_pois RT Σ2 = rt_pois RT Σ1 ->
exists P', hsig_k RT X Σ2 (a_set_dc a D' P') (set_bits_st h b' (h_st h) (h_eos h)) k
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ2 m' (a_set_dc a D' P') (set_bits_st h b' (h_st h) (h_eos h)) spill ogc opc.
Proof using AF HX ERR_loc OUT_loc IO_img IO_drv AF_DRV.
intros Σ1 Σ2 m m' a h spill ogc opc k len D' b' HS HR SPS OGS OPS (ART' & MI' & ST') PR BITS' BOK' OWN' BSZ' ERR' OUTR' CASE EF2 ES2 EC2 EP2.
pose proof (own_pos RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc HR) as OPOS.
destruct HR as (ART0 & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC & OSR & (stb & STB)
& RATE & (wl & LOOK & LKR) & DEC & HP).
pose proof (hsep_of_k Σ1 m a h k ART0 HS) as HSP.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
rewrite EF in PR.
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
pose proof (proj2 (proj2 HSP)) as NDO.

assert (NDc : forall p q, In (p, q) (h_own a h) -> p <> a_Dc a -> In (p, q) (live_remove (a_Dc a) (rt_live RT Σ1))).
{ intros p q Hin NE. apply live_remove_keep; [exact (INL _ Hin)| exact NE]. }
assert (XNE : forall e, In e (x_live X) -> fst e <> a_Dc a).
{ intros [p' q'] He E. cbn [fst] in E. subst p'.
pose proof (OPOS _ _ (own_in_Dc a h)) as P1. pose proof (proj1 (hi_live _ _ _ HX) _ _ He) as P2.
destruct (proj1 HSP _ _ (own_in_Dc a h)) as (_ & _ & _ & _ & _ & SEP). destruct (SEP _ _ He); lia. }
assert (XL : forall e, In e (x_live X) -> In e (live_remove (a_Dc a) (rt_live RT Σ1))).
{ intros e He. apply live_remove_keep; [rewrite EL; apply in_or_app; right; exact He| exact (XNE e He)]. }

assert (NSY : sy_data (h_oy h) <> None -> a_Dsy a <> a_Dc a) by (intros NS; exact (not_eq_sym (proj1 (own_ne_Dsy a h NDO NS)))).
assert (NOS : h_stream_init h <> 0 -> a_Bd a <> a_Dc a /\ a_L a <> a_Dc a /\ a_G a <> a_Dc a).
{ intros NI. split; [exact (not_eq_sym (proj1 (own_ne_os a h NDO NI _ (or_introl eq_refl))))|].
split; [exact (not_eq_sym (proj1 (own_ne_os a h NDO NI _ (or_intror (or_introl eq_refl)))))|].
exact (not_eq_sym (proj1 (own_ne_os a h NDO NI _ (or_intror (or_intror eq_refl))))). }
assert (NBL : h_st h <> None -> forall b, In b (a_LBD a) -> blk_addr b <> a_Dc a).
{ intros NS b Hb. unfold h_dec_rep in DEC. destruct (h_st h); [| exfalso; exact (NS eq_refl)].
destruct DEC as (_ & _ & _ & _ & _ & _ & _ & NB & _). exact (NB b Hb). }
unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK in *.
change (fs_size 8) with 16384 in *.

assert (FRT : forall A cs, rw_cells bsegs m A cs -> F + 32 <= A -> A + Z.of_nat (cells_size cs) <= F + 9252 ->
(A + Z.of_nat (cells_size cs) <= F + 8400 \/ F + 8448 <= A) -> rw_cells bsegs m' A cs).
{ intros A cs C H1 H2 H3. apply (htr_rw _ _ _ _ m m' PR _ _ C); [apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [lia|]. apply rng_out_img; [exact IO_img| right; unfold SEGTOP_A in *; lia]. }
assert (ENH' : rw_cells bsegs m' (F + 32) [CB 56 je]) by (apply (FRT _ _ ENH); cbn [cells_size csize Nat.add]; lia).
assert (OUTB' : rw_cells bsegs m' (F + 128) (f32 ows)) by (apply (FRT _ _ OUTB); rewrite ?cells_size_f32, ?LOWS; lia).
assert (FSZ' : rw_cells bsegs m' (F + 8384) [C4 (Z_to_bv 64 (h_frame_size h))]) by (apply (FRT _ _ FSZ); cbn [cells_size csize Nat.add]; lia).
assert (OGC' : rw_cells bsegs m' (F + 8544) ogc) by (apply (FRT _ _ OGC); rewrite ?OGS; lia).
assert (OPC' : rw_cells bsegs m' (F + 8608) opc) by (apply (FRT _ _ OPC); rewrite ?OPS; lia).
assert (STB' : rw_cells bsegs m' (F + 9168) [CB 24 stb]) by (apply (FRT _ _ STB); cbn [cells_size csize Nat.add]; lia).
assert (RATE' : rw_cells bsegs m' (F + 9232) [C4 (Z_to_bv 64 (h_rate h))]) by (apply (FRT _ _ RATE); cbn [cells_size csize Nat.add]; lia).
assert (LOOK' : rw_cells bsegs m' (F + 9248) [C4 (Z_to_bv 64 wl)]) by (apply (FRT _ _ LOOK); cbn [cells_size csize Nat.add]; lia).
clear FRT ENH OUTB FSZ OGC OPC STB RATE LOOK.
assert (SP' : rw_cells bsegs m' S1 spill).
{ apply (htr_rw _ _ _ _ m m' PR _ _ SP); rewrite SPS; [apply acl_stack; lia|]. apply rng_out_cons; [lia|].
apply rng_out_img; [exact IO_img| right; unfold SEGTOP_A in *; lia]. }
assert (LSH' : rw_cells bsegs m' sf [CB 16 HSH_P1]).
{ apply (htr_rw _ _ _ _ m m' PR _ _ LSH); cbn [cells_size csize Nat.add]; [apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
unfold SH_HI in *. apply rng_out_cons; [lia|]. apply rng_out_img; [exact IO_img| right; unfold SEGTOP_A, SH_LO in *; lia]. }

assert (OWNTR : forall p q, In (p, q) (h_own a h) -> p <> a_Dc a ->
acl_rng (live_remove (a_Dc a) (rt_live RT Σ1)) [(F, 8%nat)] S1 p q /\ rng_out ((F + 8400, F + 8400 + 48) :: IO_FP) p q).
{ intros p q Hin NE. split; [apply (acl_live _ _ _ _ _ _ _ (NDc _ _ Hin NE)); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); lia|].
destruct (proj1 HSP p q Hin) as (_ & _ & _ & _ & PI & _). apply rng_out_img; [exact IO_img| lia]. }
assert (SY' : sync_rep m' (F + 8480) (a_Dsy a) (h_oy h) (a_sybytes a)).
{ apply (sync_rep_tr _ _ _ _ m m' PR _ _ _ _ SY).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia|]. apply rng_out_img; [exact IO_img| right; unfold SEGTOP_A in *; lia].
- intros NS. exact (OWNTR _ _ (own_in_Dsy a h NS) (NSY NS)). }
assert (OSR' : h_os_rep X m' a h).
{ apply (h_os_rep_tr _ _ _ _ m m' PR X a h OSR).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- unfold HO_OS. apply rng_out_cons; [lia|]. apply rng_out_img; [exact IO_img| right; unfold SEGTOP_A in *; lia].
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG). destruct (NOS NE) as (N1 & N2 & N3).
destruct (OWNTR _ _ IB N1) as (B1 & B2). destruct (OWNTR _ _ IL N2) as (L1 & L2). destruct (OWNTR _ _ IG N3) as (G1 & G2).
exact (conj B1 (conj B2 (conj L1 (conj L2 (conj G1 G2))))). }
assert (DEC' : h_dec_rep X m' a h).
{ apply (h_dec_rep_tr _ _ _ _ m m' PR X a h DEC). intros b Hb.
assert (NS0 : h_st h <> None) by (unfold h_dec_rep in DEC; destruct (h_st h); [discriminate| destruct DEC as (_ & E'); rewrite E' in Hb; destruct Hb]).
exact (OWNTR _ _ (own_in_blk a h NS0 b Hb) (NBL NS0 b Hb)). }
clear OSR DEC BITS OWNTR SY.

assert (FPH : fp_h X a h [(F + 8400, F + 8400 + 48)]) by (apply fp_h_cons; [right; right; left; lia| apply fp_h_nil]).
destruct (h_io_step_io m m' a h _ [(F + 8400, F + 8400 + 48)] HSP PR XL FPH (AF_DRV _ _ ART') PF SSP) as (PF' & SSP').
assert (OUTR'' : forall so, OUT_rep so (x_mR X) -> OUT_rep so m') by (intros so Hso; exact (OUTR' so (OUTR so Hso))).

assert (HP' : hpure X (set_bits_st h b' (h_st h) (h_eos h))).
{ unfold hpure, h_consumed, h_pend in *.
cbn [set_bits_st h_oy h_os h_bits h_st h_stream_init h_packet_count h_last_granule h_nframes h_eos h_channels h_rate h_extra_headers
h_speex_serialno h_frame_size h_granule_frame_size h_bytes_remaining].
destruct HP as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & REST).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact BOK'|]. split; [exact OWN'|]. split; [exact BSZ'| exact REST]. }
assert (LENP : 0 < len \/ D' = a_Dc a).
{ destruct CASE as [(_ & E' & _) | (LT & _)]; [right; exact E'| left; pose proof (OPOS _ _ (own_in_Dc a h)); lia]. }
assert (BLKD : h_st h <> None -> forall b, In b (a_LBD a) -> blk_addr b <> D').
{ intros NS b Hb. destruct CASE as [(_ & -> & _) | (LT & EL2 & _)]; [exact (NBL NS b Hb)|].
intros E'. pose proof (own_in_blk a h NS b Hb) as IBk. pose proof (OPOS _ _ IBk) as PBk.
assert (IB2 : In (blk_addr b, blk_size b) ([] ++ live_remove (a_Dc a) (rt_live RT Σ1))) by (exact (NDc _ _ IBk (NBL NS b Hb))).
destruct (af_live_disj RT AF Σ2 m' D' len (blk_addr b) (blk_size b) [] (live_remove (a_Dc a) (rt_live RT Σ1)) ART' EL2 IB2) as [D1|D1];
pose proof (OPOS _ _ (own_in_Dc a h)); lia. }
assert (HR' : forall P', hrep RT OUT_rep ERR_rep IO_FP X Σ2 m' (a_set_dc a D' P') (set_bits_st h b' (h_st h) (h_eos h)) spill ogc opc).
{ intros P'. unfold hrep. unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK.
cbn [a_set_dc a_Dc a_Dsy a_sybytes set_bits_st h_oy h_os h_bits h_st h_frame_size h_rate].
split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact PF'|]. split; [exact ERR'|]. split; [exact OUTR''|]. split; [exact SSP'|].
split; [exact SP'|]. split; [exact LSH'|]. split; [exists je; exact ENH'|]. split; [exists ows; split; [exact OUTB'| exact LOWS]|].
split; [exact FSZ'|]. split; [exact BITS'|]. split; [exact SY'|]. split; [exact OGC'|]. split; [exact OPC'|].
split; [unfold h_os_rep in OSR' |- *; cbn [a_set_dc a_Bd a_L a_G a_shdr a_body a_lws a_gws set_bits_st h_stream_init h_os]; exact OSR'|].
split; [exists stb; exact STB'|]. split; [exact RATE'|]. split; [exists wl; split; [exact LOOK'| first [exact LKR | (let HH := fresh in intros HH; apply LKR; congruence)]]|].
split; [| exact HP'].
unfold h_dec_rep in DEC' |- *. cbn [a_set_dc a_S a_LBD a_Dc set_bits_st h_st].
destruct (h_st h) as [d|]; [| exact DEC'].
destruct DEC' as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9). split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
split; [exact R5|]. split; [exact R6|]. split; [exact R7|]. split; [| exact R9].
intros b Hb. exact (BLKD ltac:(discriminate) b Hb). }

assert (EOWN0 : h_own a h = (match h_st h with Some _ => blocks_live (a_LBD a) | None => [] end) ++ (a_Dc a, sb_buf_size (h_bits h))
:: ((if h_stream_init h =? 0 then [] else [(a_Bd a, os_body_storage (h_os h)); (a_L a, 4 * os_lacing_storage (h_os h));
(a_G a, 8 * os_lacing_storage (h_os h))])
++ (match sy_data (h_oy h) with Some _ => [(a_Dsy a, sy_storage (h_oy h))] | None => [] end))) by reflexivity.
destruct CASE as [(LE & -> & EL2 & EB') | (LT & EL2 & EB')].
-
exists (a_P a). split; [| apply HR'].
assert (EOWN : h_own (a_set_dc a (a_Dc a) (a_P a)) (set_bits_st h b' (h_st h) (h_eos h)) = h_own a h).
{ unfold h_own. cbn [a_set_dc a_Dsy a_Dc a_Bd a_L a_G a_LBD set_bits_st h_oy h_os h_bits h_st h_stream_init]. rewrite EB'. reflexivity. }
unfold hsig_k. rewrite EOWN. cbn [a_set_dc a_P]. rewrite EL2, EF2, ES2, EP2, EC2. unfold h_cost in *. cbn [set_bits_st h_packet_count].
split; [exact EL|]. split; [exact ND|]. split; [exact PERM|]. split; [exact EF|]. split; [exact ESP|]. split; [exact EPO0| exact ECR].
-
set (core := match h_st h with Some _ => blocks_live (a_LBD a) | None => [] end) in *.
set (rest := (if h_stream_init h =? 0 then [] else [(a_Bd a, os_body_storage (h_os h)); (a_L a, 4 * os_lacing_storage (h_os h));
(a_G a, 8 * os_lacing_storage (h_os h))])
++ (match sy_data (h_oy h) with Some _ => [(a_Dsy a, sy_storage (h_oy h))] | None => [] end)) in *.
rewrite EOWN0 in PERM, NDO.
pose proof (perm_live_remove_mid (a_Dc a) _ (a_P a) core rest PERM NDO) as PR1.
exists ((D', len) :: live_remove (a_Dc a) (a_P a)). split; [| apply HR'].
assert (EOWN : h_own (a_set_dc a D' ((D', len) :: live_remove (a_Dc a) (a_P a))) (set_bits_st h b' (h_st h) (h_eos h)) = core ++ (D', len) :: rest).
{ unfold h_own. cbn [a_set_dc a_Dsy a_Dc a_Bd a_L a_G a_LBD set_bits_st h_oy h_os h_bits h_st h_stream_init]. rewrite EB'. reflexivity. }
assert (ELP : rt_live RT Σ2 = ((D', len) :: live_remove (a_Dc a) (a_P a)) ++ x_live X).
{ rewrite EL2, EL, live_remove_app, (live_remove_none (a_Dc a) (x_live X) XNE). reflexivity. }
unfold hsig_k. rewrite EOWN. cbn [a_set_dc a_P]. rewrite EF2, ES2, EP2, EC2. unfold h_cost in *. cbn [set_bits_st h_packet_count].
split; [exact ELP|].
split.
{ apply (h_live_nodup RT AF Σ2 m' ((D', len) :: live_remove (a_Dc a) (a_P a)) [] (x_live X) ART'); [exact ELP|].
intros [p q] Hin. destruct Hin as [E'|Hin]; [injection E' as <- <-; cbn [snd]; pose proof (OPOS _ _ (own_in_Dc a h)); lia|].
apply live_remove_sub in Hin. cbn [snd]. apply (OPOS p q). rewrite EOWN0. exact (Permutation_in _ PERM Hin). }
split; [eapply perm_trans; [apply perm_skip; exact PR1| apply Permutation_middle]|].
split; [exact EF|]. split; [exact ESP|]. split; [exact EPO0| exact ECR].
Qed.

Lemma rng_out_blocks : forall (LBD : list block) A n, (forall b, In b LBD -> blk_addr b + blk_size b <= A \/ A + n <= blk_addr b) ->
rng_out (blocks_ivs LBD) A n.
Proof.
induction LBD as [|b LBD IH]; intros A n H; [apply rng_out_nil|]. cbn [blocks_ivs map].
apply rng_out_cons; [destruct (H b (or_introl eq_refl)); lia|]. apply IH. intros b' Hb'. exact (H b' (or_intror Hb')).
Qed.
Lemma fp_h_app : forall a (h : hstate unit) W1 W2, fp_h X a h W1 -> fp_h X a h W2 -> fp_h X a h (W1 ++ W2).
Proof. intros a h W1 W2 H1 H2 l hh Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (H1 l hh Hin)| exact (H2 l hh Hin)]. Qed.
Lemma fp_h_blocks : forall a (h : hstate unit) (LBD : list block), (forall b, In b LBD -> In (blk_addr b, blk_size b) (h_own a h)) ->
fp_h X a h (blocks_ivs LBD).
Proof.
intros a h LBD H l hh Hin. unfold blocks_ivs in Hin. apply in_map_iff in Hin as (b & E & Hb). injection E as <- <-.
right; right; right. right. exists (blk_addr b), (blk_size b). split; [exact (H b Hb)| lia].
Qed.

Lemma hrep_dec : forall (Σ1 Σ2 : rts RT) (m m' : mem) a (h : hstate unit) spill ogc opc k d d' (b' : bits_st unit) (ows' : list word) (stb' : list byte),
hsig_k RT X Σ1 a h k -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 248%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat ->
h_st h = Some d ->
rt_after RT Σ2 S1 lo m m' ->
rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) S1 (dec_W IO_FP (F + HO_BITS) (F + HO_OUT) (F + HO_STEREO) (a_LBD a)) m m' ->
DREP (F + HO_OUT) (F + HO_STEREO) m' (a_S a) d' (a_LBD a) ->
bits_rep bsegs m' (F + HO_BITS) (a_Dc a) b' -> bits_ok b' ->
rw_cells bsegs m' (F + HO_OUT) (f32 ows') -> length ows' = 2000%nat -> rw_cells bsegs m' (F + HO_STEREO) [CB 24 stb'] ->
ERR_rep m' -> (forall so, OUT_rep so m -> OUT_rep so m') ->
dec_depth d' = dec_depth d -> dec_nestedR d' -> isave_ok d' ->
sb_owner b' = sb_owner (h_bits h) -> sb_buf_size b' = sb_buf_size (h_bits h) ->
rt_live RT Σ2 = rt_live RT Σ1 -> rt_frames RT Σ2 = rt_frames RT Σ1 -> rt_sp0 RT Σ2 = rt_sp0 RT Σ1 ->
rt_credit RT Σ1 - dec_credit d <= rt_credit RT Σ2 -> rt_pois RT Σ2 = rt_pois RT Σ1 ->
hsig_k RT X Σ2 a (set_bits_st h b' (Some d') (h_eos h)) (k + dec_credit d)
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ2 m' a (set_bits_st h b' (Some d') (h_eos h)) spill ogc opc.
Proof using AF HX ERR_loc OUT_loc IO_img IO_drv AF_DRV.
intros Σ1 Σ2 m m' a h spill ogc opc k d d' b' ows' stb' HS HR SPS OGS OPS ESt (ART' & MI' & WM' & ST') PR DR' BITS' BOK' OUT' LOW' STB'
ERR' OUTR' EDD NR' IS' EOW EBS EL2 EF2 ES2 EC2 EP2.
pose proof (own_pos RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc HR) as OPOS.
destruct HR as (ART0 & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC & OSR & (stb & STB)
& RATE & (wl & LOOK & LKR) & DEC & HP).
pose proof (hsep_of_k Σ1 m a h k ART0 HS) as HSP.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
rewrite EF in PR.
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
pose proof (proj2 (proj2 HSP)) as NDO.
unfold h_dec_rep in DEC. rewrite ESt in DEC.
destruct DEC as (DR & SP0 & DD & IS & NR & NDB & AL8 & NBD & LLB).
assert (INB : forall b, In b (a_LBD a) -> In (blk_addr b, blk_size b) (h_own a h)) by (intros b Hb; apply (own_in_blk a h ltac:(rewrite ESt; discriminate) b Hb)).

assert (SEPB : forall p q, In (p, q) (h_own a h) -> (forall b, In b (a_LBD a) -> blk_addr b <> p) ->
forall b, In b (a_LBD a) -> blk_addr b + blk_size b <= p \/ p + q <= blk_addr b).
{ intros p q Hin NE b Hb. destruct (proj1 (proj2 HSP) _ _ _ _ (INB b Hb) Hin (NE b Hb)); lia. }
unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK in *.
unfold dec_W, BITS_SIZEOF in PR.
change (fs_size 8) with 16384 in *.

assert (FRT : forall A cs, rw_cells bsegs m A cs -> F + 32 <= A -> A + Z.of_nat (cells_size cs) <= F + 9252 ->
(A + Z.of_nat (cells_size cs) <= F + 8400 \/ F + 8448 <= A) -> (A + Z.of_nat (cells_size cs) <= F + 128 \/ F + 8128 <= A) ->
(A + Z.of_nat (cells_size cs) <= F + 9168 \/ F + 9192 <= A) -> rw_cells bsegs m' A cs).
{ intros A cs C H1 H2 H3 H4 H5. apply (htr_rw _ _ _ _ m m' PR _ _ C); [apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|].
apply rng_out_app; [| apply rng_out_img; [exact IO_img| right; unfold SEGTOP_A in *; lia]].
apply rng_out_blocks. intros b Hb. destruct (proj1 HSP _ _ (INB b Hb)) as (_ & _ & FR & _). lia. }
assert (ENH' : rw_cells bsegs m' (F + 32) [CB 56 je]) by (apply (FRT _ _ ENH); cbn [cells_size csize Nat.add]; lia).
assert (FSZ' : rw_cells bsegs m' (F + 8384) [C4 (Z_to_bv 64 (h_frame_size h))]) by (apply (FRT _ _ FSZ); cbn [cells_size csize Nat.add]; lia).
assert (OGC' : rw_cells bsegs m' (F + 8544) ogc) by (apply (FRT _ _ OGC); rewrite ?OGS; lia).
assert (OPC' : rw_cells bsegs m' (F + 8608) opc) by (apply (FRT _ _ OPC); rewrite ?OPS; lia).
assert (RATE' : rw_cells bsegs m' (F + 9232) [C4 (Z_to_bv 64 (h_rate h))]) by (apply (FRT _ _ RATE); cbn [cells_size csize Nat.add]; lia).
assert (LOOK' : rw_cells bsegs m' (F + 9248) [C4 (Z_to_bv 64 wl)]) by (apply (FRT _ _ LOOK); cbn [cells_size csize Nat.add]; lia).
clear FRT ENH OUTB FSZ OGC OPC STB RATE LOOK.
assert (SP' : rw_cells bsegs m' S1 spill).
{ apply (htr_rw _ _ _ _ m m' PR _ _ SP); rewrite SPS; [apply acl_stack; lia|]. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|].
apply rng_out_app; [| apply rng_out_img; [exact IO_img| right; unfold SEGTOP_A in *; lia]].
apply rng_out_blocks. intros b Hb. destruct (proj1 HSP _ _ (INB b Hb)) as (_ & BL & _). lia. }
assert (LSH' : rw_cells bsegs m' sf [CB 16 HSH_P1]).
{ apply (htr_rw _ _ _ _ m m' PR _ _ LSH); cbn [cells_size csize Nat.add]; [apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
unfold SH_HI in *. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|].
apply rng_out_app; [| apply rng_out_img; [exact IO_img| right; unfold SEGTOP_A, SH_LO in *; lia]].
apply rng_out_blocks. intros b Hb. destruct (proj1 HSP _ _ (INB b Hb)) as (_ & _ & _ & FSh & _). lia. }

assert (OWNTR : forall p q, In (p, q) (h_own a h) -> (forall b, In b (a_LBD a) -> blk_addr b <> p) ->
acl_rng (rt_live RT Σ1) [(F, 8%nat)] S1 p q
/\ rng_out ((F + 8400, F + 8400 + 48) :: (F + 128, F + 128 + 8000) :: (F + 9168, F + 9168 + 24) :: blocks_ivs (a_LBD a) ++ IO_FP) p q).
{ intros p q Hin NE. split; [apply (acl_live _ _ _ _ _ _ _ (INL _ Hin)); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); lia|].
destruct (proj1 HSP p q Hin) as (_ & _ & _ & _ & PI & _).
apply rng_out_app; [| apply rng_out_img; [exact IO_img| lia]].
apply rng_out_blocks. exact (SEPB p q Hin NE). }
assert (SY' : sync_rep m' (F + 8480) (a_Dsy a) (h_oy h) (a_sybytes a)).
{ apply (sync_rep_tr _ _ _ _ m m' PR _ _ _ _ SY).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|].
apply rng_out_app; [| apply rng_out_img; [exact IO_img| right; unfold SEGTOP_A in *; lia]].
apply rng_out_blocks. intros b Hb. destruct (proj1 HSP _ _ (INB b Hb)) as (_ & _ & FR & _). lia.
- intros NS. apply (OWNTR _ _ (own_in_Dsy a h NS)). intros b Hb. exact (proj2 (proj2 (own_ne_Dsy a h NDO NS)) ltac:(rewrite ESt; discriminate) b Hb). }
assert (OSR' : h_os_rep X m' a h).
{ apply (h_os_rep_tr _ _ _ _ m m' PR X a h OSR).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- unfold HO_OS. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|].
apply rng_out_app; [| apply rng_out_img; [exact IO_img| right; unfold SEGTOP_A in *; lia]].
apply rng_out_blocks. intros b Hb. destruct (proj1 HSP _ _ (INB b Hb)) as (_ & _ & FR & _). lia.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
destruct (OWNTR _ _ IB (fun b Hb => proj2 (proj2 (own_ne_os a h NDO NE _ (or_introl eq_refl))) ltac:(rewrite ESt; discriminate) b Hb)) as (B1 & B2).
destruct (OWNTR _ _ IL (fun b Hb => proj2 (proj2 (own_ne_os a h NDO NE _ (or_intror (or_introl eq_refl)))) ltac:(rewrite ESt; discriminate) b Hb)) as (L1 & L2).
destruct (OWNTR _ _ IG (fun b Hb => proj2 (proj2 (own_ne_os a h NDO NE _ (or_intror (or_intror eq_refl)))) ltac:(rewrite ESt; discriminate) b Hb)) as (G1 & G2).
exact (conj B1 (conj B2 (conj L1 (conj L2 (conj G1 G2))))). }
clear OSR SY OWNTR.

assert (FPH : fp_h X a h ((F + 8400, F + 8400 + 48) :: (F + 128, F + 128 + 8000) :: (F + 9168, F + 9168 + 24) :: blocks_ivs (a_LBD a))).
{ apply fp_h_cons; [right; right; left; lia|]. apply fp_h_cons; [right; right; left; lia|]. apply fp_h_cons; [right; right; left; lia|].
exact (fp_h_blocks a h (a_LBD a) INB). }
rewrite app_comm_cons, app_comm_cons, app_comm_cons in PR.
destruct (h_io_step_io m m' a h _ _ HSP PR ltac:(intros e He; rewrite EL; apply in_or_app; right; exact He) FPH (AF_DRV _ _ ART') PF SSP) as (PF' & SSP').
assert (OUTR'' : forall so, OUT_rep so (x_mR X) -> OUT_rep so m') by (intros so Hso; exact (OUTR' so (OUTR so Hso))).
assert (HP' : hpure X (set_bits_st h b' (Some d') (h_eos h))).
{ unfold hpure, h_consumed, h_pend in *.
cbn [set_bits_st h_oy h_os h_bits h_st h_stream_init h_packet_count h_last_granule h_nframes h_eos h_channels h_rate h_extra_headers
h_speex_serialno h_frame_size h_granule_frame_size h_bytes_remaining].
rewrite ESt in HP.
destruct HP as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & REST).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact BOK'|]. split; [rewrite EOW; exact A6|].
split; [rewrite EBS; exact A7| exact REST]. }
split.
- assert (EOWN : h_own a (set_bits_st h b' (Some d') (h_eos h)) = h_own a h).
{ unfold h_own. cbn [set_bits_st h_oy h_os h_bits h_st h_stream_init]. rewrite ESt, EBS. reflexivity. }
unfold hsig_k. rewrite EOWN, EL2, EF2, ES2, EP2. unfold h_cost in *. cbn [set_bits_st h_packet_count].
split; [exact EL|]. split; [exact ND|]. split; [exact PERM|]. split; [exact EF|]. split; [exact ESP|]. split; [exact EPO0| lia].
- unfold hrep. unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK.
cbn [set_bits_st h_oy h_os h_bits h_st h_frame_size h_rate].
split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact PF'|]. split; [exact ERR'|]. split; [exact OUTR''|]. split; [exact SSP'|].
split; [exact SP'|]. split; [exact LSH'|]. split; [exists je; exact ENH'|]. split; [exists ows'; split; [exact OUT'| exact LOW']|].
split; [exact FSZ'|]. split; [exact BITS'|]. split; [exact SY'|]. split; [exact OGC'|]. split; [exact OPC'|].
split; [unfold h_os_rep in OSR' |- *; cbn [set_bits_st h_stream_init h_os]; exact OSR'|].
split; [exists stb'; exact STB'|]. split; [exact RATE'|]. split; [exists wl; split; [exact LOOK'| first [exact LKR | (let HH := fresh in intros HH; apply LKR; congruence)]]|].
split; [| exact HP'].
unfold h_dec_rep. cbn [set_bits_st h_st].
split; [exact DR'|]. split; [exact SP0|]. split; [unfold bptr in *; lia|]. split; [exact IS'|]. split; [exact NR'|].
split; [exact NDB|]. split; [exact AL8|]. split; [exact NBD| exact LLB].
Qed.

End PkStep.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).

Lemma packetout_same : forall (os os' : stream_st bptr) r opo, ogg_stream_packetout os = Some ((r, opo), os') ->
os_lacing os' = os_lacing os /\ os_granules os' = os_granules os /\ os_body os' = os_body os
/\ os_body_data os' = os_body_data os /\ os_lacing_vals os' = os_lacing_vals os /\ os_granule_vals os' = os_granule_vals os
/\ os_body_storage os' = os_body_storage os /\ os_lacing_storage os' = os_lacing_storage os
/\ os_body_fill os' = os_body_fill os /\ os_lacing_fill os' = os_lacing_fill os /\ os_serialno os' = os_serialno os.
Proof.
intros os os' r opo H. unfold ogg_stream_packetout, packetout in H.
destruct (ogg_stream_check os); [injection H as _ _ <-; repeat split; reflexivity|].
destruct (_ <=? _); [injection H as _ _ <-; repeat split; reflexivity|].
destruct (negb _); [injection H as _ _ <-; cbn; repeat split; reflexivity|].
destruct (gather255 _ _ _ _ _) as [[[n eos] bytes]|]; [injection H as _ _ <-; cbn; repeat split; reflexivity| discriminate H].
Qed.

Lemma packetout_os_pure : forall (os os' : stream_st bptr) r opo, os_pure os -> ogg_stream_packetout os = Some ((r, opo), os') -> stream_fields_ok os' ->
os_pure os' /\ os_lacing_returned os <= os_lacing_returned os' <= os_lacing_fill os
/\ (r = 1 -> opo <> None /\ os_lacing_returned os < os_lacing_returned os')
/\ match opo with Some p => 0 <= pk_off p /\ 0 <= pk_bytes p /\ pk_off p + pk_bytes p <= os_body_fill os /\ zlength (packet_data os' p) = pk_bytes p
| None => True end.
Proof.
intros os os' r opo (FOK & SINV & BINV & LOK & GL & BD & LV & GV & LS & BS) E FOK'.
destruct (packetout_same os os' r opo E) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
destruct (ogg_stream_packetout_frame os r opo os' SINV E) as (SINV' & _ & _ & _ & _ & _ & _ & _ & _ & RR & R1 & _).
destruct (ogg_stream_packetout_body_inv os r opo os' SINV BINV E) as (BINV' & _ & _ & PK).
split.
{ unfold os_pure. rewrite E1, E2, E4, E5, E6, E7, E8. split; [exact FOK'|]. split; [exact SINV'|]. split; [exact BINV'|].
repeat split; assumption. }
split; [exact RR|]. split; [exact R1| exact PK].
Qed.

Section PkStep.
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
Local Notation S1 := (x_S1 X). Local Notation lo := (x_lo X). Local Notation F := (x_F X). Local Notation sf := (x_sf X).

Lemma outside_IO_of_WL : forall x, outside (h_WL IO_FP X) x -> outside IO_FP x.
Proof. intros x H. unfold h_WL in H. cbn [outside] in H. destruct H as (_ & _ & _ & H). exact H. Qed.

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
+ apply (fp_h_static OUT_rep IO_FP X HX a h W HSP FPH). unfold SSP_GUARD, SEGTOP_A in *. lia.
+ apply outside_of_not_in_ranges'. intros Hin. apply (IO_drv x Hin). unfold drv_cell. right; left; exact Hx.
Qed.

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

Lemma hrep_packetout : forall (Σ1 : rts RT) (m m1 : mem) a (h : hstate unit) spill ogc opc r opo (os' : stream_st unit) gw,
hsig RT X Σ1 a h -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 216%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat ->
h_stream_init h <> 0 -> ogg_stream_packetout (h_os h) = Some ((r, opo), os') ->
munch [(F + 8688, F + 8688 + 408); (F + 8608, F + 8608 + 48)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
rw_cells asegs m1 (F + 8688) (stream_cells (a_Bd a) (a_L a) (a_G a) (a_shdr a) os') -> stream_fields_ok os' ->
rw_cells asegs m1 (F + 8608) (op_cells (a_Bd a) opo gw opc) ->
hsig RT X Σ1 a (set_ogg h (h_oy h) os')
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ1 m1 a (set_ogg h (h_oy h) os') spill ogc (op_cells (a_Bd a) opo gw opc)
/\ os_lacing_returned (h_os h) <= os_lacing_returned os'
/\ (r = 1 -> opo <> None /\ os_lacing_returned (h_os h) < os_lacing_returned os')
/\ match opo with Some p => 0 <= pk_off p /\ 0 <= pk_bytes p /\ pk_off p + pk_bytes p <= os_body_fill (h_os h) /\ zlength (packet_data os' p) = pk_bytes p
| None => True end.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV.
intros Σ1 m m1 a h spill ogc opc r opo os' gw HS HR SPS OGS OPS SI E MU WM MI1 OS1 FOK1 OP1.
destruct HR as (ART0 & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC & OSR & (stb & STB)
& RATE & (wl & LOOK) & DEC & HP).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART0 HS) as HSP.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }

unfold h_os_rep in OSR. destruct (Z.eqb_spec (h_stream_init h) 0) as [E0|_]; [exfalso; exact (SI E0)|].
destruct OSR as (_ & LH & (UB & LB & BP & UL & WP & LL & UG & LG) & FOK & SINV & BINV & LOK & GL & BD & LV & GV & LS & BS & NBL & NBG & NLG).
destruct (packetout_same (h_os h) os' r opo E) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
destruct (packetout_os_pure (h_os h) os' r opo (conj FOK (conj SINV (conj BINV (conj LOK (conj GL (conj BD (conj LV (conj GV (conj LS BS))))))))) E FOK1)
as (POS' & RR & R1 & PK).
unfold bptr in *.

assert (PR : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 [(F + 8688, F + 8688 + 408); (F + 8608, F + 8608 + 48)] m m1).
{ apply (pres_fp_of_munch _ _ _ _ _ m m1 MU). intros x _ Ho. exact Ho. }
assert (ART1 : ART RT Σ1 m1).
{ apply (af_frame RT AF Σ1 m m1 S1 ART0); [rewrite ESP; pose proof (hi_lo _ _ _ HX) as (LW0 & _); unfold STACK_WIN in *; lia| | exact WM].
intros b Hb. apply MU. cbn [outside]. rewrite EF in Hb.
split; [intros Hin; apply Hb; exact (acl_frame (rt_live RT Σ1) [(F, 8%nat)] S1 F 8 (F + 8688) 408 INF ltac:(lia) ltac:(change (fs_size 8) with 16384; lia) _ Hin)|].
split; [intros Hin; apply Hb; exact (acl_frame (rt_live RT Σ1) [(F, 8%nat)] S1 F 8 (F + 8608) 48 INF ltac:(lia) ltac:(change (fs_size 8) with 16384; lia) _ Hin)|].
exact I. }
assert (ST1 : stk asegs m1 lo S1).
{ apply (stk_agree asegs m m1 lo S1 ST); [| exact WM]. apply (agree_of_munch _ m m1 _ MU). intros x Hx. cbn [outside].
change (fs_size 8) with 16384 in FL. split; [lia|]. split; [lia| exact I]. }
unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK in *.
change (fs_size 8) with 16384 in *.
assert (FRT : forall A cs, rw_cells asegs m A cs -> F + 32 <= A -> A + Z.of_nat (cells_size cs) <= F + 9252 ->
(A + Z.of_nat (cells_size cs) <= F + 8688 \/ F + 9096 <= A) -> (A + Z.of_nat (cells_size cs) <= F + 8608 \/ F + 8656 <= A) ->
rw_cells asegs m1 A cs).
{ intros A cs C H1 H2 H3 H4. apply (htr_rw _ _ _ _ m m1 PR _ _ C); [apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (ENH' : rw_cells asegs m1 (F + 32) [CB 56 je]) by (apply (FRT _ _ ENH); cbn [cells_size csize Nat.add]; lia).
assert (OUTB' : rw_cells asegs m1 (F + 128) (f32 ows)) by (apply (FRT _ _ OUTB); rewrite ?cells_size_f32, ?LOWS; lia).
assert (FSZ' : rw_cells asegs m1 (F + 8384) [C4 (Z_to_bv 64 (h_frame_size h))]) by (apply (FRT _ _ FSZ); cbn [cells_size csize Nat.add]; lia).
assert (OGC' : rw_cells asegs m1 (F + 8544) ogc) by (apply (FRT _ _ OGC); rewrite ?OGS; lia).
assert (STB' : rw_cells asegs m1 (F + 9168) [CB 24 stb]) by (apply (FRT _ _ STB); cbn [cells_size csize Nat.add]; lia).
assert (RATE' : rw_cells asegs m1 (F + 9232) [C4 (Z_to_bv 64 (h_rate h))]) by (apply (FRT _ _ RATE); cbn [cells_size csize Nat.add]; lia).
assert (LOOK' : rw_cells asegs m1 (F + 9248) [C4 wl]) by (apply (FRT _ _ LOOK); cbn [cells_size csize Nat.add]; lia).
clear FRT ENH OUTB FSZ OGC STB RATE LOOK.
assert (SP' : rw_cells asegs m1 S1 spill).
{ apply (htr_rw _ _ _ _ m m1 PR _ _ SP); rewrite SPS; [apply acl_stack; lia|]. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (LSH' : rw_cells asegs m1 sf [CB 16 HSH_P1]).
{ apply (htr_rw _ _ _ _ m m1 PR _ _ LSH); cbn [cells_size csize Nat.add]; [apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
unfold SH_HI in *. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (OWNTR : forall p q, In (p, q) (h_own a h) -> acl_rng (rt_live RT Σ1) [(F, 8%nat)] S1 p q /\ rng_out [(F + 8688, F + 8688 + 408); (F + 8608, F + 8608 + 48)] p q).
{ intros p q Hin. split; [apply (acl_live _ _ _ _ _ _ _ (INL _ Hin)); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); lia|]. apply rng_out_nil. }
assert (BOK : bits_ok (h_bits h)) by (destruct HP as (_ & _ & _ & _ & B & _); exact B).
assert (BITS' : bits_rep asegs m1 (F + 8400) (a_Dc a) (h_bits h)).
{ destruct (OWNTR _ _ (own_in_Dc a h)) as (D1 & D2).
apply (bits_rep_tr _ _ _ _ m m1 PR _ _ _ BITS BOK); [| | exact D1| exact D2].
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (SY' : sync_rep m1 (F + 8480) (a_Dsy a) (h_oy h) (a_sybytes a)).
{ apply (sync_rep_tr _ _ _ _ m m1 PR _ _ _ _ SY).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil.
- intros NS. exact (OWNTR _ _ (own_in_Dsy a h NS)). }
assert (DEC' : h_dec_rep X m1 a h).
{ apply (h_dec_rep_tr _ _ _ _ m m1 PR X a h DEC). intros b Hb.
assert (NS0 : h_st h <> None) by (unfold h_dec_rep in DEC; destruct (h_st h); [discriminate| destruct DEC as (_ & E'); rewrite E' in Hb; destruct Hb]).
apply (OWNTR _ _ (own_in_blk a h NS0 b Hb)). }
destruct (own_in_os a h SI) as (IB & IL & IG).
destruct (OWNTR _ _ IB) as (B1 & B2). destruct (OWNTR _ _ IL) as (L1 & L2). destruct (OWNTR _ _ IG) as (G1 & G2).
assert (OSR' : h_os_rep X m1 a (set_ogg h (h_oy h) os')).
{ apply h_os_rep_intro; cbn [set_ogg h_os h_stream_init].
- exact SI.
- unfold HO_OS. exact OS1.
- exact LH.
- unfold stream_arrays, bptr. rewrite E1, E3, E7, E8.
split; [apply (htr_u8 _ _ _ _ m m1 PR _ _ UB); rewrite LB; assumption|]. split; [exact LB|]. split; [exact BP|].
split; [apply (htr_u32 _ _ _ _ m m1 PR _ _ UL); rewrite LL; assumption|]. split; [exact WP|]. split; [exact LL|].
split; [apply (htr_u64 _ _ _ _ m m1 PR _ _ UG); rewrite LG; assumption| exact LG].
- exact POS'.
- exact NBL. - exact NBG. - exact NLG. }
clear DEC BITS OWNTR SY.
assert (FPH : fp_h X a h [(F + 8688, F + 8688 + 408); (F + 8608, F + 8608 + 48)])
by (apply fp_h_cons; [right; right; left; lia| apply fp_h_cons; [right; right; left; lia| apply fp_h_nil]]).
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ1 m m1 a h _ _ HSP PR
ltac:(intros e He; rewrite EL; apply in_or_app; right; exact He) FPH (AF_DRV _ _ ART1) PF ERR OUTR SSP) as (PF' & ERR' & OUTR' & SSP').
assert (HP' : hpure X (set_ogg h (h_oy h) os')).
{ rewrite set_ogg_with.
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P17 & _ & _ & _ & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
apply hpure_with_os; [exact HP| exact P17| ..]; unfold h_consumed, h_pend in *; rewrite ?E7, ?E8, ?E9, ?E10; lia. }
split.
{ unfold hsig. assert (EOWN : h_own a (set_ogg h (h_oy h) os') = h_own a h).
{ unfold h_own. cbn [set_ogg h_oy h_os h_bits h_st h_stream_init]. rewrite E7, E8. reflexivity. }
rewrite EOWN. unfold h_cost in *. cbn [set_ogg h_packet_count]. exact HS. }
split.
{ unfold hrep. unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK.
cbn [set_ogg h_oy h_os h_bits h_st h_frame_size h_rate].
split; [exact ART1|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact PF'|]. split; [exact ERR'|]. split; [exact OUTR'|]. split; [exact SSP'|].
split; [exact SP'|]. split; [exact LSH'|]. split; [exists je; exact ENH'|]. split; [exists ows; split; [exact OUTB'| exact LOWS]|].
split; [exact FSZ'|]. split; [exact BITS'|]. split; [exact SY'|]. split; [exact OGC'|]. split; [exact OP1|].
split; [unfold HO_OS in OSR'; exact OSR'|]. split; [exists stb; exact STB'|]. split; [exact RATE'|]. split; [exists wl; exact LOOK'|].
split; [| exact HP']. unfold h_dec_rep in DEC' |- *. cbn [set_ogg h_st]. exact DEC'. }
split; [exact (proj1 RR)|]. split; [exact R1| exact PK].
Qed.

Lemma hrep_out_step : forall (Σ1 : rts RT) (m m1 : mem) a (h : hstate unit) spill ogc opc (ws' : list word) (stb' : list byte) k,
hsig_k RT X Σ1 a h k -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 216%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat ->
munch [(F + 128, F + 8128); (F + 9168, F + 9192); (S1 + -16, S1)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo S1 ->
rw_cells asegs m1 (F + 128) (f32 ws') -> length ws' = 2000%nat -> rw_cells asegs m1 (F + 9168) [CB 24 stb'] ->
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m1 a h spill ogc opc.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV.
intros Σ1 m m1 a h spill ogc opc ws' stb' k HS HR SPS OGS OPS MU WM MI1 ST1 OUT1 LOW1 STB1.
destruct HR as (ART0 & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC & OSR & (stb & STB)
& RATE & (wl & LOOK) & DEC & HP).
pose proof (hsep_of_k Σ1 m a h k ART0 HS) as HSP.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
pose proof (hi_lo _ _ _ HX) as (LW0 & _).

assert (PR : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 [(F + 128, F + 8128); (F + 9168, F + 9192)] m m1).
{ apply (pres_fp_of_munch _ _ _ _ _ m m1 MU). intros x Hx Ho. cbn [outside] in Ho |- *. destruct Ho as (O1 & O2 & _).
split; [exact O1|]. split; [exact O2|]. split; [| exact I].
rewrite <- EF in Hx. destruct (aclient_split RT AF Σ1 m S1 x ART0 Hx) as [XH|XL]; [lia| rewrite ESP in XL; unfold STACK_WIN in *; lia]. }
assert (ART1 : ART RT Σ1 m1).
{ apply (af_frame RT AF Σ1 m m1 (S1 + -16) ART0); [rewrite ESP; unfold STACK_WIN in *; lia| | exact WM].
intros b Hb. apply MU. cbn [outside]. rewrite EF in Hb.
split; [intros Hin; apply Hb; exact (acl_frame (rt_live RT Σ1) [(F, 8%nat)] (S1 + -16) F 8 (F + 128) 8000 INF ltac:(lia) ltac:(change (fs_size 8) with 16384; lia) (bv_unsigned b) ltac:(lia))|].
split; [intros Hin; apply Hb; exact (acl_frame (rt_live RT Σ1) [(F, 8%nat)] (S1 + -16) F 8 (F + 9168) 24 INF ltac:(lia) ltac:(change (fs_size 8) with 16384; lia) (bv_unsigned b) ltac:(lia))|].
split; [intros Hin; apply Hb; apply (acl_stack (rt_live RT Σ1) [(F, 8%nat)] (S1 + -16) (S1 + -16) 16 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) (bv_unsigned b)); lia| exact I]. }
unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK in *.
change (fs_size 8) with 16384 in *.
assert (FRT : forall A cs, rw_cells asegs m A cs -> F + 32 <= A -> A + Z.of_nat (cells_size cs) <= F + 9252 ->
(A + Z.of_nat (cells_size cs) <= F + 128 \/ F + 8128 <= A) -> (A + Z.of_nat (cells_size cs) <= F + 9168 \/ F + 9192 <= A) ->
rw_cells asegs m1 A cs).
{ intros A cs C H1 H2 H3 H4. apply (htr_rw _ _ _ _ m m1 PR _ _ C); [apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (ENH' : rw_cells asegs m1 (F + 32) [CB 56 je]) by (apply (FRT _ _ ENH); cbn [cells_size csize Nat.add]; lia).
assert (FSZ' : rw_cells asegs m1 (F + 8384) [C4 (Z_to_bv 64 (h_frame_size h))]) by (apply (FRT _ _ FSZ); cbn [cells_size csize Nat.add]; lia).
assert (OGC' : rw_cells asegs m1 (F + 8544) ogc) by (apply (FRT _ _ OGC); rewrite ?OGS; lia).
assert (OPC' : rw_cells asegs m1 (F + 8608) opc) by (apply (FRT _ _ OPC); rewrite ?OPS; lia).
assert (RATE' : rw_cells asegs m1 (F + 9232) [C4 (Z_to_bv 64 (h_rate h))]) by (apply (FRT _ _ RATE); cbn [cells_size csize Nat.add]; lia).
assert (LOOK' : rw_cells asegs m1 (F + 9248) [C4 wl]) by (apply (FRT _ _ LOOK); cbn [cells_size csize Nat.add]; lia).
clear FRT ENH OUTB FSZ OGC OPC STB RATE LOOK.
assert (SP' : rw_cells asegs m1 S1 spill).
{ apply (htr_rw _ _ _ _ m m1 PR _ _ SP); rewrite SPS; [apply acl_stack; lia|]. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (LSH' : rw_cells asegs m1 sf [CB 16 HSH_P1]).
{ apply (htr_rw _ _ _ _ m m1 PR _ _ LSH); cbn [cells_size csize Nat.add]; [apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
unfold SH_HI in *. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (OWNTR : forall p q, In (p, q) (h_own a h) -> acl_rng (rt_live RT Σ1) [(F, 8%nat)] S1 p q /\ rng_out [(F + 128, F + 8128); (F + 9168, F + 9192)] p q).
{ intros p q Hin. split; [apply (acl_live _ _ _ _ _ _ _ (INL _ Hin)); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); lia|]. apply rng_out_nil. }
assert (BOK : bits_ok (h_bits h)) by (destruct HP as (_ & _ & _ & _ & B & _); exact B).
assert (BITS' : bits_rep asegs m1 (F + 8400) (a_Dc a) (h_bits h)).
{ destruct (OWNTR _ _ (own_in_Dc a h)) as (D1 & D2).
apply (bits_rep_tr _ _ _ _ m m1 PR _ _ _ BITS BOK); [| | exact D1| exact D2].
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (SY' : sync_rep m1 (F + 8480) (a_Dsy a) (h_oy h) (a_sybytes a)).
{ apply (sync_rep_tr _ _ _ _ m m1 PR _ _ _ _ SY).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil.
- intros NS. exact (OWNTR _ _ (own_in_Dsy a h NS)). }
assert (OSR' : h_os_rep X m1 a h).
{ apply (h_os_rep_tr _ _ _ _ m m1 PR X a h OSR).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- unfold HO_OS. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
destruct (OWNTR _ _ IB) as (B1 & B2). destruct (OWNTR _ _ IL) as (L1 & L2). destruct (OWNTR _ _ IG) as (G1 & G2).
exact (conj B1 (conj B2 (conj L1 (conj L2 (conj G1 G2))))). }
assert (DEC' : h_dec_rep X m1 a h).
{ apply (h_dec_rep_tr _ _ _ _ m m1 PR X a h DEC). intros b Hb.
assert (NS0 : h_st h <> None) by (unfold h_dec_rep in DEC; destruct (h_st h); [discriminate| destruct DEC as (_ & E'); rewrite E' in Hb; destruct Hb]).
apply (OWNTR _ _ (own_in_blk a h NS0 b Hb)). }
clear OSR DEC BITS OWNTR SY.
assert (FPH : fp_h X a h [(F + 128, F + 8128); (F + 9168, F + 9192)])
by (apply fp_h_cons; [right; right; left; lia| apply fp_h_cons; [right; right; left; lia| apply fp_h_nil]]).
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ1 m m1 a h _ _ HSP PR
ltac:(intros e He; rewrite EL; apply in_or_app; right; exact He) FPH (AF_DRV _ _ ART1) PF ERR OUTR SSP) as (PF' & ERR' & OUTR' & SSP').
unfold hrep. unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK.
split; [exact ART1|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact PF'|]. split; [exact ERR'|]. split; [exact OUTR'|]. split; [exact SSP'|].
split; [exact SP'|]. split; [exact LSH'|]. split; [exists je; exact ENH'|]. split; [exists ws'; split; [exact OUT1| exact LOW1]|].
split; [exact FSZ'|]. split; [exact BITS'|]. split; [exact SY'|]. split; [exact OGC'|]. split; [exact OPC'|].
split; [unfold HO_OS in OSR'; exact OSR'|]. split; [exists stb'; exact STB1|]. split; [exact RATE'|]. split; [exists wl; exact LOOK'|].
split; [exact DEC'| exact HP].
Qed.

Definition a_set_dc (a : haux) (D : Z) (P : list (Z * Z)) : haux :=
HA (a_Dsy a) (a_sybytes a) (a_Bd a) (a_L a) (a_G a) (a_shdr a) (a_body a) (a_lws a) (a_gws a) D (a_S a) (a_LBD a) P.

Lemma h_bits_shadow_at : forall m', rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) (x_mR X) m' -> ro_cells asegs m' (shad (F + 8400)) bits_shadow.
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

Lemma hrep_rf : forall (Σ1 Σ2 : rts RT) (m m' : mem) a (h : hstate unit) spill ogc opc k len D' (b' : bits_st unit),
hsig_k RT X Σ1 a h k -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 216%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat ->
rt_after_f RT Σ2 S1 lo m m' ->
rt_pres_fp (live_remove (a_Dc a) (rt_live RT Σ1)) (rt_frames RT Σ1) S1 ((F + 8400, F + 8400 + 48) :: IO_FP) m m' ->
bits_rep asegs m' (F + 8400) D' b' -> bits_ok b' -> sb_owner b' = 1 -> 2000 <= sb_buf_size b' <= 64512 ->
ERR_rep m' -> (forall so, OUT_rep so m -> OUT_rep so m') ->
((len <= sb_buf_size (h_bits h) /\ D' = a_Dc a /\ rt_live RT Σ2 = rt_live RT Σ1 /\ sb_buf_size b' = sb_buf_size (h_bits h))
\/ (sb_buf_size (h_bits h) < len /\ rt_live RT Σ2 = (D', len) :: live_remove (a_Dc a) (rt_live RT Σ1) /\ sb_buf_size b' = len)) ->
rt_frames RT Σ2 = rt_frames RT Σ1 -> rt_sp0 RT Σ2 = rt_sp0 RT Σ1 -> rt_credit RT Σ2 = rt_credit RT Σ1 -> rt_pois RT Σ2 = rt_pois RT Σ1 ->
exists P', hsig_k RT X Σ2 (a_set_dc a D' P') (set_bits_st h b' (h_st h) (h_eos h)) k
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ2 m' (a_set_dc a D' P') (set_bits_st h b' (h_st h) (h_eos h)) spill ogc opc.
Proof using AF HX ERR_loc OUT_loc IO_img IO_drv AF_DRV.
intros Σ1 Σ2 m m' a h spill ogc opc k len D' b' HS HR SPS OGS OPS (ART' & MI' & ST') PR BITS' BOK' OWN' BSZ' ERR' OUTR' CASE EF2 ES2 EC2 EP2.
pose proof (own_pos RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc HR) as OPOS.
destruct HR as (ART0 & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC & OSR & (stb & STB)
& RATE & (wl & LOOK) & DEC & HP).
pose proof (hsep_of_k Σ1 m a h k ART0 HS) as HSP.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
rewrite EF in PR.
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
pose proof (proj2 (proj2 HSP)) as NDO.

assert (NDc : forall p q, In (p, q) (h_own a h) -> p <> a_Dc a -> In (p, q) (live_remove (a_Dc a) (rt_live RT Σ1))).
{ intros p q Hin NE. apply live_remove_keep; [exact (INL _ Hin)| exact NE]. }
assert (XNE : forall e, In e (x_live X) -> fst e <> a_Dc a).
{ intros [p' q'] He E. cbn [fst] in E. subst p'.
pose proof (OPOS _ _ (own_in_Dc a h)) as P1. pose proof (proj1 (hi_live _ _ _ HX) _ _ He) as P2.
destruct (proj1 HSP _ _ (own_in_Dc a h)) as (_ & _ & _ & _ & _ & SEP). destruct (SEP _ _ He); lia. }
assert (XL : forall e, In e (x_live X) -> In e (live_remove (a_Dc a) (rt_live RT Σ1))).
{ intros e He. apply live_remove_keep; [rewrite EL; apply in_or_app; right; exact He| exact (XNE e He)]. }

assert (NSY : sy_data (h_oy h) <> None -> a_Dsy a <> a_Dc a) by (intros NS; exact (not_eq_sym (proj1 (own_ne_Dsy a h NDO NS)))).
assert (NOS : h_stream_init h <> 0 -> a_Bd a <> a_Dc a /\ a_L a <> a_Dc a /\ a_G a <> a_Dc a).
{ intros NI. split; [exact (not_eq_sym (proj1 (own_ne_os a h NDO NI _ (or_introl eq_refl))))|].
split; [exact (not_eq_sym (proj1 (own_ne_os a h NDO NI _ (or_intror (or_introl eq_refl)))))|].
exact (not_eq_sym (proj1 (own_ne_os a h NDO NI _ (or_intror (or_intror eq_refl))))). }
assert (NBL : h_st h <> None -> forall b, In b (a_LBD a) -> blk_addr b <> a_Dc a).
{ intros NS b Hb. unfold h_dec_rep in DEC. destruct (h_st h); [| exfalso; exact (NS eq_refl)].
destruct DEC as (_ & _ & _ & _ & _ & _ & _ & NB & _). exact (NB b Hb). }
unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK in *.
change (fs_size 8) with 16384 in *.

assert (FRT : forall A cs, rw_cells asegs m A cs -> F + 32 <= A -> A + Z.of_nat (cells_size cs) <= F + 9252 ->
(A + Z.of_nat (cells_size cs) <= F + 8400 \/ F + 8448 <= A) -> rw_cells asegs m' A cs).
{ intros A cs C H1 H2 H3. apply (htr_rw _ _ _ _ m m' PR _ _ C); [apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [lia|]. apply rng_out_img; [exact IO_img| right; unfold SEGTOP_A in *; lia]. }
assert (ENH' : rw_cells asegs m' (F + 32) [CB 56 je]) by (apply (FRT _ _ ENH); cbn [cells_size csize Nat.add]; lia).
assert (OUTB' : rw_cells asegs m' (F + 128) (f32 ows)) by (apply (FRT _ _ OUTB); rewrite ?cells_size_f32, ?LOWS; lia).
assert (FSZ' : rw_cells asegs m' (F + 8384) [C4 (Z_to_bv 64 (h_frame_size h))]) by (apply (FRT _ _ FSZ); cbn [cells_size csize Nat.add]; lia).
assert (OGC' : rw_cells asegs m' (F + 8544) ogc) by (apply (FRT _ _ OGC); rewrite ?OGS; lia).
assert (OPC' : rw_cells asegs m' (F + 8608) opc) by (apply (FRT _ _ OPC); rewrite ?OPS; lia).
assert (STB' : rw_cells asegs m' (F + 9168) [CB 24 stb]) by (apply (FRT _ _ STB); cbn [cells_size csize Nat.add]; lia).
assert (RATE' : rw_cells asegs m' (F + 9232) [C4 (Z_to_bv 64 (h_rate h))]) by (apply (FRT _ _ RATE); cbn [cells_size csize Nat.add]; lia).
assert (LOOK' : rw_cells asegs m' (F + 9248) [C4 wl]) by (apply (FRT _ _ LOOK); cbn [cells_size csize Nat.add]; lia).
clear FRT ENH OUTB FSZ OGC OPC STB RATE LOOK.
assert (SP' : rw_cells asegs m' S1 spill).
{ apply (htr_rw _ _ _ _ m m' PR _ _ SP); rewrite SPS; [apply acl_stack; lia|]. apply rng_out_cons; [lia|].
apply rng_out_img; [exact IO_img| right; unfold SEGTOP_A in *; lia]. }
assert (LSH' : rw_cells asegs m' sf [CB 16 HSH_P1]).
{ apply (htr_rw _ _ _ _ m m' PR _ _ LSH); cbn [cells_size csize Nat.add]; [apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
unfold SH_HI in *. apply rng_out_cons; [lia|]. apply rng_out_img; [exact IO_img| right; unfold SEGTOP_A, SH_LO in *; lia]. }

assert (OWNTR : forall p q, In (p, q) (h_own a h) -> p <> a_Dc a ->
acl_rng (live_remove (a_Dc a) (rt_live RT Σ1)) [(F, 8%nat)] S1 p q /\ rng_out ((F + 8400, F + 8400 + 48) :: IO_FP) p q).
{ intros p q Hin NE. split; [apply (acl_live _ _ _ _ _ _ _ (NDc _ _ Hin NE)); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); lia|].
destruct (proj1 HSP p q Hin) as (_ & _ & _ & _ & PI & _). apply rng_out_img; [exact IO_img| lia]. }
assert (SY' : sync_rep m' (F + 8480) (a_Dsy a) (h_oy h) (a_sybytes a)).
{ apply (sync_rep_tr _ _ _ _ m m' PR _ _ _ _ SY).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia|]. apply rng_out_img; [exact IO_img| right; unfold SEGTOP_A in *; lia].
- intros NS. exact (OWNTR _ _ (own_in_Dsy a h NS) (NSY NS)). }
assert (OSR' : h_os_rep X m' a h).
{ apply (h_os_rep_tr _ _ _ _ m m' PR X a h OSR).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- unfold HO_OS. apply rng_out_cons; [lia|]. apply rng_out_img; [exact IO_img| right; unfold SEGTOP_A in *; lia].
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG). destruct (NOS NE) as (N1 & N2 & N3).
destruct (OWNTR _ _ IB N1) as (B1 & B2). destruct (OWNTR _ _ IL N2) as (L1 & L2). destruct (OWNTR _ _ IG N3) as (G1 & G2).
exact (conj B1 (conj B2 (conj L1 (conj L2 (conj G1 G2))))). }
assert (DEC' : h_dec_rep X m' a h).
{ apply (h_dec_rep_tr _ _ _ _ m m' PR X a h DEC). intros b Hb.
assert (NS0 : h_st h <> None) by (unfold h_dec_rep in DEC; destruct (h_st h); [discriminate| destruct DEC as (_ & E'); rewrite E' in Hb; destruct Hb]).
exact (OWNTR _ _ (own_in_blk a h NS0 b Hb) (NBL NS0 b Hb)). }
clear OSR DEC BITS OWNTR SY.

assert (FPH : fp_h X a h [(F + 8400, F + 8400 + 48)]) by (apply fp_h_cons; [right; right; left; lia| apply fp_h_nil]).
destruct (h_io_step_io m m' a h _ [(F + 8400, F + 8400 + 48)] HSP PR XL FPH (AF_DRV _ _ ART') PF SSP) as (PF' & SSP').
assert (OUTR'' : forall so, OUT_rep so (x_mR X) -> OUT_rep so m') by (intros so Hso; exact (OUTR' so (OUTR so Hso))).

assert (HP' : hpure X (set_bits_st h b' (h_st h) (h_eos h))).
{ unfold hpure, h_consumed, h_pend in *.
cbn [set_bits_st h_oy h_os h_bits h_st h_stream_init h_packet_count h_last_granule h_nframes h_eos h_channels h_rate h_extra_headers
h_speex_serialno h_frame_size h_granule_frame_size h_bytes_remaining].
destruct HP as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & REST).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact BOK'|]. split; [exact OWN'|]. split; [exact BSZ'| exact REST]. }
assert (LENP : 0 < len \/ D' = a_Dc a).
{ destruct CASE as [(_ & E' & _) | (LT & _)]; [right; exact E'| left; pose proof (OPOS _ _ (own_in_Dc a h)); lia]. }
assert (BLKD : h_st h <> None -> forall b, In b (a_LBD a) -> blk_addr b <> D').
{ intros NS b Hb. destruct CASE as [(_ & -> & _) | (LT & EL2 & _)]; [exact (NBL NS b Hb)|].
intros E'. pose proof (own_in_blk a h NS b Hb) as IBk. pose proof (OPOS _ _ IBk) as PBk.
assert (IB2 : In (blk_addr b, blk_size b) ([] ++ live_remove (a_Dc a) (rt_live RT Σ1))) by (exact (NDc _ _ IBk (NBL NS b Hb))).
destruct (af_live_disj RT AF Σ2 m' D' len (blk_addr b) (blk_size b) [] (live_remove (a_Dc a) (rt_live RT Σ1)) ART' EL2 IB2) as [D1|D1];
pose proof (OPOS _ _ (own_in_Dc a h)); lia. }
assert (HR' : forall P', hrep RT OUT_rep ERR_rep IO_FP X Σ2 m' (a_set_dc a D' P') (set_bits_st h b' (h_st h) (h_eos h)) spill ogc opc).
{ intros P'. unfold hrep. unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK.
cbn [a_set_dc a_Dc a_Dsy a_sybytes set_bits_st h_oy h_os h_bits h_st h_frame_size h_rate].
split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact PF'|]. split; [exact ERR'|]. split; [exact OUTR''|]. split; [exact SSP'|].
split; [exact SP'|]. split; [exact LSH'|]. split; [exists je; exact ENH'|]. split; [exists ows; split; [exact OUTB'| exact LOWS]|].
split; [exact FSZ'|]. split; [exact BITS'|]. split; [exact SY'|]. split; [exact OGC'|]. split; [exact OPC'|].
split; [unfold h_os_rep in OSR' |- *; cbn [a_set_dc a_Bd a_L a_G a_shdr a_body a_lws a_gws set_bits_st h_stream_init h_os]; exact OSR'|].
split; [exists stb; exact STB'|]. split; [exact RATE'|]. split; [exists wl; exact LOOK'|].
split; [| exact HP'].
unfold h_dec_rep in DEC' |- *. cbn [a_set_dc a_S a_LBD a_Dc set_bits_st h_st].
destruct (h_st h) as [d|]; [| exact DEC'].
destruct DEC' as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9). split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
split; [exact R5|]. split; [exact R6|]. split; [exact R7|]. split; [| exact R9].
intros b Hb. exact (BLKD ltac:(discriminate) b Hb). }

assert (EOWN0 : h_own a h = (match h_st h with Some _ => blocks_live (a_LBD a) | None => [] end) ++ (a_Dc a, sb_buf_size (h_bits h))
:: ((if h_stream_init h =? 0 then [] else [(a_Bd a, os_body_storage (h_os h)); (a_L a, 4 * os_lacing_storage (h_os h));
(a_G a, 8 * os_lacing_storage (h_os h))])
++ (match sy_data (h_oy h) with Some _ => [(a_Dsy a, sy_storage (h_oy h))] | None => [] end))) by reflexivity.
destruct CASE as [(LE & -> & EL2 & EB') | (LT & EL2 & EB')].
-
exists (a_P a). split; [| apply HR'].
assert (EOWN : h_own (a_set_dc a (a_Dc a) (a_P a)) (set_bits_st h b' (h_st h) (h_eos h)) = h_own a h).
{ unfold h_own. cbn [a_set_dc a_Dsy a_Dc a_Bd a_L a_G a_LBD set_bits_st h_oy h_os h_bits h_st h_stream_init]. rewrite EB'. reflexivity. }
unfold hsig_k. rewrite EOWN. cbn [a_set_dc a_P]. rewrite EL2, EF2, ES2, EP2, EC2. unfold h_cost in *. cbn [set_bits_st h_packet_count].
split; [exact EL|]. split; [exact ND|]. split; [exact PERM|]. split; [exact EF|]. split; [exact ESP|]. split; [exact EPO0| exact ECR].
-
set (core := match h_st h with Some _ => blocks_live (a_LBD a) | None => [] end) in *.
set (rest := (if h_stream_init h =? 0 then [] else [(a_Bd a, os_body_storage (h_os h)); (a_L a, 4 * os_lacing_storage (h_os h));
(a_G a, 8 * os_lacing_storage (h_os h))])
++ (match sy_data (h_oy h) with Some _ => [(a_Dsy a, sy_storage (h_oy h))] | None => [] end)) in *.
rewrite EOWN0 in PERM, NDO.
pose proof (perm_live_remove_mid (a_Dc a) _ (a_P a) core rest PERM NDO) as PR1.
exists ((D', len) :: live_remove (a_Dc a) (a_P a)). split; [| apply HR'].
assert (EOWN : h_own (a_set_dc a D' ((D', len) :: live_remove (a_Dc a) (a_P a))) (set_bits_st h b' (h_st h) (h_eos h)) = core ++ (D', len) :: rest).
{ unfold h_own. cbn [a_set_dc a_Dsy a_Dc a_Bd a_L a_G a_LBD set_bits_st h_oy h_os h_bits h_st h_stream_init]. rewrite EB'. reflexivity. }
assert (ELP : rt_live RT Σ2 = ((D', len) :: live_remove (a_Dc a) (a_P a)) ++ x_live X).
{ rewrite EL2, EL, live_remove_app, (live_remove_none (a_Dc a) (x_live X) XNE). reflexivity. }
unfold hsig_k. rewrite EOWN. cbn [a_set_dc a_P]. rewrite EF2, ES2, EP2, EC2. unfold h_cost in *. cbn [set_bits_st h_packet_count].
split; [exact ELP|].
split.
{ apply (live_nodup RT AF Σ2 m' ((D', len) :: live_remove (a_Dc a) (a_P a)) [] (x_live X) ART'); [exact ELP|].
intros [p q] Hin. destruct Hin as [E'|Hin]; [injection E' as <- <-; cbn [snd]; pose proof (OPOS _ _ (own_in_Dc a h)); lia|].
apply live_remove_sub in Hin. cbn [snd]. apply (OPOS p q). rewrite EOWN0. exact (Permutation_in _ PERM Hin). }
split; [eapply perm_trans; [apply perm_skip; exact PR1| apply Permutation_middle]|].
split; [exact EF|]. split; [exact ESP|]. split; [exact EPO0| exact ECR].
Qed.

Lemma rng_out_blocks : forall (LBD : list block) A n, (forall b, In b LBD -> blk_addr b + blk_size b <= A \/ A + n <= blk_addr b) ->
rng_out (blocks_ivs LBD) A n.
Proof.
induction LBD as [|b LBD IH]; intros A n H; [apply rng_out_nil|]. cbn [blocks_ivs map].
apply rng_out_cons; [destruct (H b (or_introl eq_refl)); lia|]. apply IH. intros b' Hb'. exact (H b' (or_intror Hb')).
Qed.
Lemma fp_h_app : forall a (h : hstate unit) W1 W2, fp_h X a h W1 -> fp_h X a h W2 -> fp_h X a h (W1 ++ W2).
Proof. intros a h W1 W2 H1 H2 l hh Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (H1 l hh Hin)| exact (H2 l hh Hin)]. Qed.
Lemma fp_h_blocks : forall a (h : hstate unit) (LBD : list block), (forall b, In b LBD -> In (blk_addr b, blk_size b) (h_own a h)) ->
fp_h X a h (blocks_ivs LBD).
Proof.
intros a h LBD H l hh Hin. unfold blocks_ivs in Hin. apply in_map_iff in Hin as (b & E & Hb). injection E as <- <-.
right; right; right. right. exists (blk_addr b), (blk_size b). split; [exact (H b Hb)| lia].
Qed.

Lemma hrep_dec : forall (Σ1 Σ2 : rts RT) (m m' : mem) a (h : hstate unit) spill ogc opc k d d' (b' : bits_st unit) (ows' : list word) (stb' : list byte),
hsig_k RT X Σ1 a h k -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 216%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat ->
h_st h = Some d ->
rt_after RT Σ2 S1 lo m m' ->
rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) S1 (dec_W IO_FP (F + HO_BITS) (F + HO_OUT) (F + HO_STEREO) (a_LBD a)) m m' ->
DREP (F + HO_OUT) (F + HO_STEREO) m' (a_S a) d' (a_LBD a) ->
bits_rep asegs m' (F + HO_BITS) (a_Dc a) b' -> bits_ok b' ->
rw_cells asegs m' (F + HO_OUT) (f32 ows') -> length ows' = 2000%nat -> rw_cells asegs m' (F + HO_STEREO) [CB 24 stb'] ->
ERR_rep m' -> (forall so, OUT_rep so m -> OUT_rep so m') ->
dec_depth d' = dec_depth d -> dec_nestedR d' -> isave_ok d' ->
sb_owner b' = sb_owner (h_bits h) -> sb_buf_size b' = sb_buf_size (h_bits h) ->
rt_live RT Σ2 = rt_live RT Σ1 -> rt_frames RT Σ2 = rt_frames RT Σ1 -> rt_sp0 RT Σ2 = rt_sp0 RT Σ1 ->
rt_credit RT Σ1 - dec_credit d <= rt_credit RT Σ2 -> rt_pois RT Σ2 = rt_pois RT Σ1 ->
hsig_k RT X Σ2 a (set_bits_st h b' (Some d') (h_eos h)) (k + dec_credit d)
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ2 m' a (set_bits_st h b' (Some d') (h_eos h)) spill ogc opc.
Proof using AF HX ERR_loc OUT_loc IO_img IO_drv AF_DRV.
intros Σ1 Σ2 m m' a h spill ogc opc k d d' b' ows' stb' HS HR SPS OGS OPS ESt (ART' & MI' & WM' & ST') PR DR' BITS' BOK' OUT' LOW' STB'
ERR' OUTR' EDD NR' IS' EOW EBS EL2 EF2 ES2 EC2 EP2.
pose proof (own_pos RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc HR) as OPOS.
destruct HR as (ART0 & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC & OSR & (stb & STB)
& RATE & (wl & LOOK) & DEC & HP).
pose proof (hsep_of_k Σ1 m a h k ART0 HS) as HSP.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
rewrite EF in PR.
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
pose proof (proj2 (proj2 HSP)) as NDO.
unfold h_dec_rep in DEC. rewrite ESt in DEC.
destruct DEC as (DR & SP0 & DD & IS & NR & NDB & AL8 & NBD & LLB).
assert (INB : forall b, In b (a_LBD a) -> In (blk_addr b, blk_size b) (h_own a h)) by (intros b Hb; apply (own_in_blk a h ltac:(rewrite ESt; discriminate) b Hb)).

assert (SEPB : forall p q, In (p, q) (h_own a h) -> (forall b, In b (a_LBD a) -> blk_addr b <> p) ->
forall b, In b (a_LBD a) -> blk_addr b + blk_size b <= p \/ p + q <= blk_addr b).
{ intros p q Hin NE b Hb. destruct (proj1 (proj2 HSP) _ _ _ _ (INB b Hb) Hin (NE b Hb)); lia. }
unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK in *.
unfold dec_W, BITS_SIZEOF in PR.
change (fs_size 8) with 16384 in *.

assert (FRT : forall A cs, rw_cells asegs m A cs -> F + 32 <= A -> A + Z.of_nat (cells_size cs) <= F + 9252 ->
(A + Z.of_nat (cells_size cs) <= F + 8400 \/ F + 8448 <= A) -> (A + Z.of_nat (cells_size cs) <= F + 128 \/ F + 8128 <= A) ->
(A + Z.of_nat (cells_size cs) <= F + 9168 \/ F + 9192 <= A) -> rw_cells asegs m' A cs).
{ intros A cs C H1 H2 H3 H4 H5. apply (htr_rw _ _ _ _ m m' PR _ _ C); [apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|].
apply rng_out_app; [| apply rng_out_img; [exact IO_img| right; unfold SEGTOP_A in *; lia]].
apply rng_out_blocks. intros b Hb. destruct (proj1 HSP _ _ (INB b Hb)) as (_ & _ & FR & _). lia. }
assert (ENH' : rw_cells asegs m' (F + 32) [CB 56 je]) by (apply (FRT _ _ ENH); cbn [cells_size csize Nat.add]; lia).
assert (FSZ' : rw_cells asegs m' (F + 8384) [C4 (Z_to_bv 64 (h_frame_size h))]) by (apply (FRT _ _ FSZ); cbn [cells_size csize Nat.add]; lia).
assert (OGC' : rw_cells asegs m' (F + 8544) ogc) by (apply (FRT _ _ OGC); rewrite ?OGS; lia).
assert (OPC' : rw_cells asegs m' (F + 8608) opc) by (apply (FRT _ _ OPC); rewrite ?OPS; lia).
assert (RATE' : rw_cells asegs m' (F + 9232) [C4 (Z_to_bv 64 (h_rate h))]) by (apply (FRT _ _ RATE); cbn [cells_size csize Nat.add]; lia).
assert (LOOK' : rw_cells asegs m' (F + 9248) [C4 wl]) by (apply (FRT _ _ LOOK); cbn [cells_size csize Nat.add]; lia).
clear FRT ENH OUTB FSZ OGC OPC STB RATE LOOK.
assert (SP' : rw_cells asegs m' S1 spill).
{ apply (htr_rw _ _ _ _ m m' PR _ _ SP); rewrite SPS; [apply acl_stack; lia|]. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|].
apply rng_out_app; [| apply rng_out_img; [exact IO_img| right; unfold SEGTOP_A in *; lia]].
apply rng_out_blocks. intros b Hb. destruct (proj1 HSP _ _ (INB b Hb)) as (_ & BL & _). lia. }
assert (LSH' : rw_cells asegs m' sf [CB 16 HSH_P1]).
{ apply (htr_rw _ _ _ _ m m' PR _ _ LSH); cbn [cells_size csize Nat.add]; [apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
unfold SH_HI in *. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|].
apply rng_out_app; [| apply rng_out_img; [exact IO_img| right; unfold SEGTOP_A, SH_LO in *; lia]].
apply rng_out_blocks. intros b Hb. destruct (proj1 HSP _ _ (INB b Hb)) as (_ & _ & _ & FSh & _). lia. }

assert (OWNTR : forall p q, In (p, q) (h_own a h) -> (forall b, In b (a_LBD a) -> blk_addr b <> p) ->
acl_rng (rt_live RT Σ1) [(F, 8%nat)] S1 p q
/\ rng_out ((F + 8400, F + 8400 + 48) :: (F + 128, F + 128 + 8000) :: (F + 9168, F + 9168 + 24) :: blocks_ivs (a_LBD a) ++ IO_FP) p q).
{ intros p q Hin NE. split; [apply (acl_live _ _ _ _ _ _ _ (INL _ Hin)); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); lia|].
destruct (proj1 HSP p q Hin) as (_ & _ & _ & _ & PI & _).
apply rng_out_app; [| apply rng_out_img; [exact IO_img| lia]].
apply rng_out_blocks. exact (SEPB p q Hin NE). }
assert (SY' : sync_rep m' (F + 8480) (a_Dsy a) (h_oy h) (a_sybytes a)).
{ apply (sync_rep_tr _ _ _ _ m m' PR _ _ _ _ SY).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|].
apply rng_out_app; [| apply rng_out_img; [exact IO_img| right; unfold SEGTOP_A in *; lia]].
apply rng_out_blocks. intros b Hb. destruct (proj1 HSP _ _ (INB b Hb)) as (_ & _ & FR & _). lia.
- intros NS. apply (OWNTR _ _ (own_in_Dsy a h NS)). intros b Hb. exact (proj2 (proj2 (own_ne_Dsy a h NDO NS)) ltac:(rewrite ESt; discriminate) b Hb). }
assert (OSR' : h_os_rep X m' a h).
{ apply (h_os_rep_tr _ _ _ _ m m' PR X a h OSR).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- unfold HO_OS. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|].
apply rng_out_app; [| apply rng_out_img; [exact IO_img| right; unfold SEGTOP_A in *; lia]].
apply rng_out_blocks. intros b Hb. destruct (proj1 HSP _ _ (INB b Hb)) as (_ & _ & FR & _). lia.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
destruct (OWNTR _ _ IB (fun b Hb => proj2 (proj2 (own_ne_os a h NDO NE _ (or_introl eq_refl))) ltac:(rewrite ESt; discriminate) b Hb)) as (B1 & B2).
destruct (OWNTR _ _ IL (fun b Hb => proj2 (proj2 (own_ne_os a h NDO NE _ (or_intror (or_introl eq_refl)))) ltac:(rewrite ESt; discriminate) b Hb)) as (L1 & L2).
destruct (OWNTR _ _ IG (fun b Hb => proj2 (proj2 (own_ne_os a h NDO NE _ (or_intror (or_intror eq_refl)))) ltac:(rewrite ESt; discriminate) b Hb)) as (G1 & G2).
exact (conj B1 (conj B2 (conj L1 (conj L2 (conj G1 G2))))). }
clear OSR SY OWNTR.

assert (FPH : fp_h X a h ((F + 8400, F + 8400 + 48) :: (F + 128, F + 128 + 8000) :: (F + 9168, F + 9168 + 24) :: blocks_ivs (a_LBD a))).
{ apply fp_h_cons; [right; right; left; lia|]. apply fp_h_cons; [right; right; left; lia|]. apply fp_h_cons; [right; right; left; lia|].
exact (fp_h_blocks a h (a_LBD a) INB). }
rewrite app_comm_cons, app_comm_cons, app_comm_cons in PR.
destruct (h_io_step_io m m' a h _ _ HSP PR ltac:(intros e He; rewrite EL; apply in_or_app; right; exact He) FPH (AF_DRV _ _ ART') PF SSP) as (PF' & SSP').
assert (OUTR'' : forall so, OUT_rep so (x_mR X) -> OUT_rep so m') by (intros so Hso; exact (OUTR' so (OUTR so Hso))).
assert (HP' : hpure X (set_bits_st h b' (Some d') (h_eos h))).
{ unfold hpure, h_consumed, h_pend in *.
cbn [set_bits_st h_oy h_os h_bits h_st h_stream_init h_packet_count h_last_granule h_nframes h_eos h_channels h_rate h_extra_headers
h_speex_serialno h_frame_size h_granule_frame_size h_bytes_remaining].
rewrite ESt in HP.
destruct HP as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & REST).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact BOK'|]. split; [rewrite EOW; exact A6|].
split; [rewrite EBS; exact A7| exact REST]. }
split.
- assert (EOWN : h_own a (set_bits_st h b' (Some d') (h_eos h)) = h_own a h).
{ unfold h_own. cbn [set_bits_st h_oy h_os h_bits h_st h_stream_init]. rewrite ESt, EBS. reflexivity. }
unfold hsig_k. rewrite EOWN, EL2, EF2, ES2, EP2. unfold h_cost in *. cbn [set_bits_st h_packet_count].
split; [exact EL|]. split; [exact ND|]. split; [exact PERM|]. split; [exact EF|]. split; [exact ESP|]. split; [exact EPO0| lia].
- unfold hrep. unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK.
cbn [set_bits_st h_oy h_os h_bits h_st h_frame_size h_rate].
split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact PF'|]. split; [exact ERR'|]. split; [exact OUTR''|]. split; [exact SSP'|].
split; [exact SP'|]. split; [exact LSH'|]. split; [exists je; exact ENH'|]. split; [exists ows'; split; [exact OUT'| exact LOW']|].
split; [exact FSZ'|]. split; [exact BITS'|]. split; [exact SY'|]. split; [exact OGC'|]. split; [exact OPC'|].
split; [unfold h_os_rep in OSR' |- *; cbn [set_bits_st h_stream_init h_os]; exact OSR'|].
split; [exists stb'; exact STB'|]. split; [exact RATE'|]. split; [exists wl; exact LOOK'|].
split; [| exact HP'].
unfold h_dec_rep. cbn [set_bits_st h_st].
split; [exact DR'|]. split; [exact SP0|]. split; [unfold bptr in *; lia|]. split; [exact IS'|]. split; [exact NR'|].
split; [exact NDB|]. split; [exact AL8|]. split; [exact NBD| exact LLB].
Qed.

End PkStep.
