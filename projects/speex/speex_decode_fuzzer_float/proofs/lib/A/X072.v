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
X0ae X09u X09x X0af X09p X09l X0a4 X0a5 X0ab X05l X05e X05c
X05m X09f X06d X069 X068 X071 X06v X06y X06u X073 X07j.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X12c X14x X0r0 X0r9 X0ra X0qz X0v9 X0rb X0wl X0wm X110 X10j X10c X108 X10q X10r X10x X0wb X0w9 X0x2 X0x1 X0xn X0xq X0xm X0xu X0ya.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X108 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10r OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xu OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ya.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).

Lemma pageout_ret : forall (sy sy' : sync_st unit) r og, ogg_sync_pageout sy = Some ((r, og), sy') -> r = 1 \/ r = 0 \/ r = -1.
Proof.
intros sy sy' r og E. unfold ogg_sync_pageout in E. destruct (ogg_sync_check sy). { inversion E. lia. }
revert E. generalize (pageout_fuel sy) as fuel. intros fuel. revert sy.
induction fuel as [|fuel IH]; intros sy E; [discriminate|]. cbn [pageout_loop] in E.
destruct (ogg_sync_pageseek sy) as [[r1 og1] sy1].
destruct (0 <? r1); [inversion E; lia|]. destruct (r1 =? 0); [inversion E; lia|].
destruct (sy_unsynced sy1 =? 0); [inversion E; lia|]. eapply IH. exact E.
Qed.

Lemma h_drep_sizes_pos : forall (d : dec_state bptr) OUT STEREO (m : mem) S LBD, DREP OUT STEREO m S d LBD -> forall b, In b LBD -> 0 < blk_size b.
Proof.
induction d as [st|s low IHd]; intros OUT STEREO m S LBD H b Hb; cbn [decst_rep] in H.
- destruct H as [-> _]. destruct Hb as [<-|[]]. unfold blk_size, NBSTATE_SIZEOF. cbn. lia.
- destruct H as (a & j & LBL & -> & _ & _ & INV & _ & _ & _ & OUTL & RL). apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [| exact (IHd _ _ _ _ _ RL b Hb)].
destruct INV as (IM & _ & _ & ISF & _). assert (0 < sbd_subframeSize s) by (rewrite ISF; destruct IM as [E|E]; rewrite E; cbn; lia).
cbn [sb_blocks In] in Hb. unfold SBSTATE_SIZEOF in Hb.
repeat (destruct Hb as [<-|Hb]; [unfold blk_size; cbn [snd]; lia|]). destruct Hb.
Qed.

Lemma nodup_app_disj : forall {A : Type} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros A l1. induction l1 as [|y l1 IH]; intros l2 x ND H1 H2; [destruct H1|].
cbn [app] in ND. apply NoDup_cons_iff in ND as (NI & ND). destruct H1 as [<-|H1].
- apply NI. apply in_or_app. right. exact H2.
- exact (IH l2 x ND H1 H2).
Qed.

Section Own.
Variables (a : haux) (h : hstate unit).
Lemma own_in_Dc : In (a_Dc a, sb_buf_size (h_bits h)) (h_own a h).
Proof. unfold h_own. apply in_or_app. right. apply in_or_app. left. left. reflexivity. Qed.
Lemma own_in_Dsy : sy_data (h_oy h) <> None -> In (a_Dsy a, sy_storage (h_oy h)) (h_own a h).
Proof.
intros ND. unfold h_own. destruct (sy_data (h_oy h)) as [p|]; [| congruence].
apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. left. reflexivity.
Qed.
Lemma own_in_os : h_stream_init h <> 0 ->
In (a_Bd a, os_body_storage (h_os h)) (h_own a h) /\ In (a_L a, 4 * os_lacing_storage (h_os h)) (h_own a h)
/\ In (a_G a, 8 * os_lacing_storage (h_os h)) (h_own a h).
Proof.
intros NE. unfold h_own. replace (h_stream_init h =? 0) with false by (symmetry; apply Z.eqb_neq; exact NE).
split; [| split]; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; cbn; tauto.
Qed.
Lemma own_in_blk : h_st h <> None -> forall b, In b (a_LBD a) -> In (blk_addr b, blk_size b) (h_own a h).
Proof.
intros NE b Hb. unfold h_own. apply in_or_app. left. destruct (h_st h); [| congruence].
unfold blocks_live. apply in_map_iff. exists b. split; [reflexivity| exact Hb].
Qed.

Lemma own_ne_Dsy : List.NoDup (map fst (h_own a h)) -> sy_data (h_oy h) <> None ->
a_Dc a <> a_Dsy a /\ (h_stream_init h <> 0 -> a_Bd a <> a_Dsy a /\ a_L a <> a_Dsy a /\ a_G a <> a_Dsy a)
/\ (h_st h <> None -> forall b, In b (a_LBD a) -> blk_addr b <> a_Dsy a).
Proof.
intros ND NS. unfold h_own in ND. destruct (sy_data (h_oy h)) as [p|]; [| congruence].
rewrite !map_app in ND.
apply NoDup_app_remove_l in ND as ND1.
split; [| split].
- cbn [map fst app] in ND1. apply NoDup_cons_iff in ND1 as (N1 & _). intros E. apply N1. rewrite E. apply in_or_app. right. left. reflexivity.
- intros NE. replace (h_stream_init h =? 0) with false in ND1 by (symmetry; apply Z.eqb_neq; exact NE). cbn [map fst app] in ND1.
apply NoDup_cons_iff in ND1 as (_ & ND2). apply NoDup_cons_iff in ND2 as (B1 & ND3). apply NoDup_cons_iff in ND3 as (B2 & ND4).
apply NoDup_cons_iff in ND4 as (B3 & _). cbn in B1, B2, B3.
split; [| split]; intros E; [apply B1| apply B2| apply B3]; rewrite E; tauto.
- intros NE b Hb E. destruct (h_st h) as [d|]; [| congruence].
apply (nodup_app_disj _ _ (blk_addr b) ND); [unfold blocks_live; rewrite map_map; apply in_map_iff; exists b; split; [reflexivity| exact Hb]|].
rewrite E. apply in_or_app. right. apply in_or_app. right. left. reflexivity.
Qed.
End Own.

Section Steps.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Variable X : hinv.
Hypothesis HX : hinv_ok OUT_rep IO_FP X.
Local Notation S1 := (x_S1 X). Local Notation lo := (x_lo X). Local Notation F := (x_F X). Local Notation sf := (x_sf X).

Lemma hpure_pageout : forall h r ogo oy2, hpure X h -> ogg_sync_pageout (h_oy h) = Some ((r, ogo), oy2) -> hpure X (set_ogg h oy2 (h_os h)).
Proof.
intros h r ogo oy2 HP EPO. unfold hpure, h_consumed, h_pend in *.
cbn [set_ogg h_oy h_os h_bits h_st h_stream_init h_packet_count h_last_granule h_nframes h_eos h_channels h_rate h_extra_headers
h_speex_serialno h_frame_size h_granule_frame_size h_bytes_remaining].
destruct HP as (SI2 & SI & STB & SDN & REST).
destruct (ogg_sync_pageout_frame _ _ _ _ SI EPO) as (SI' & EFL & EBF & EDT & EST & RMO & _).
destruct (ogg_sync_pageout_inv2 _ _ _ _ SI2 EPO) as (SI2' & _).
rewrite EST, EDT. split; [exact SI2'|]. split; [exact SI'|]. split; [exact STB|]. split; [exact SDN|].
destruct SI' as (R0 & _).
destruct REST as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
do 16 (split; [assumption|]). rewrite EFL in *. repeat split; lia.
Qed.

Lemma hrep_pageout : forall (Σ1 : rts RT) (m m' : mem) a h spill opc j0 j1 j2 j3 r ogo oy2,
hsig RT X Σ1 a h ->
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3] opc ->
cells_size spill = 248%nat -> cells_size opc = 48%nat ->
ogg_sync_pageout (h_oy h) = Some ((r, ogo), oy2) ->
rt_after RT Σ1 S1 lo m m' ->
rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) S1
[(F + 8480, F + 8480 + 32); (F + 8544, F + 8544 + 32); (a_Dsy a, a_Dsy a + Z.of_nat (length (a_sybytes a)))] m m' ->
sync_rep m' (F + 8480) (a_Dsy a) oy2 (a_sybytes a) ->
rw_cells bsegs m' (F + 8544) (og_cells (a_Dsy a) ogo [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3]) ->
hsig RT X Σ1 a (set_ogg h oy2 (h_os h))
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ1 m' a (set_ogg h oy2 (h_os h)) spill (og_cells (a_Dsy a) ogo [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3]) opc
/\ match ogo with Some og => r = 1 /\ page_ok oy2 og /\ h_page_budget X (set_ogg h oy2 (h_os h)) og | None => r <> 1 end.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV.
intros Σ1 m m' a h spill opc j0 j1 j2 j3 r ogo oy2 HS HR SPS OPS EPO (ART' & MI' & WM' & ST') PR SY' OG'.
destruct HR as (ART & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC & OSR & (stb & STB)
& RATE & (wl & LOOK & LKR) & DEC & HP).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART HS) as HSP.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
rewrite EF in PR.
pose proof HP as (SI2 & SI & STB0 & SDN & _).
destruct (ogg_sync_pageout_frame _ _ _ _ SI EPO) as (SI' & EFL & EBF & EDT & EST & RMO & PGF).
assert (EOWN : h_own a (set_ogg h oy2 (h_os h)) = h_own a h).
{ unfold h_own. cbn [set_ogg h_oy h_os h_bits h_st h_stream_init]. unfold bptr in EDT, EST. rewrite EDT, EST. reflexivity. }

assert (IVD : iv_own a h (a_Dsy a) (a_Dsy a + Z.of_nat (length (a_sybytes a)))).
{ destruct SY as (_ & _ & DAT & _). unfold sync_data, bptr in DAT. destruct (sy_data (h_oy h)) as [p|] eqn:ED.
- destruct DAT as (_ & _ & LB & _). right. exists (a_Dsy a), (sy_storage (h_oy h)). split; [apply own_in_Dsy; rewrite ED; discriminate|]. lia.
- destruct DAT as (_ & -> & _). left. cbn. lia. }
assert (FPH : fp_h X a h [(F + 8480, F + 8480 + 32); (F + 8544, F + 8544 + 32); (a_Dsy a, a_Dsy a + Z.of_nat (length (a_sybytes a)))]).
{ apply fp_h_cons; [right; right; left; lia|]. apply fp_h_cons; [right; right; left; lia|]. apply fp_h_cons; [right; right; right; exact IVD|]. apply fp_h_nil. }
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ1 m m' a h (rt_live RT Σ1) _ HSP PR
ltac:(intros e He; rewrite EL; apply in_or_app; right; exact He) FPH (AF_DRV _ _ ART') PF ERR OUTR SSP) as (PF' & ERR' & OUTR' & SSP').
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
unfold RT_STACK, H_STACK in LR.
unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK in *.
change (fs_size 8) with 16384 in *.

assert (IVNE : forall p0, (sy_data (h_oy h) <> None -> p0 <> a_Dsy a) -> iv_own_ne a h p0 (a_Dsy a) (a_Dsy a + Z.of_nat (length (a_sybytes a)))).
{ intros p0 NE. destruct SY as (_ & _ & DAT & _). unfold sync_data, bptr in DAT. destruct (sy_data (h_oy h)) as [p|] eqn:ED.
- destruct DAT as (_ & _ & LB & _). right. exists (a_Dsy a), (sy_storage (h_oy h)).
split; [apply own_in_Dsy; rewrite ED; discriminate|]. split; [apply not_eq_sym; apply NE; discriminate| lia].
- destruct DAT as (_ & -> & _). left. cbn. lia. }
pose proof (own_ne_Dsy a h (proj2 (proj2 HSP))) as ONE.

assert (SP' : rw_cells bsegs m' S1 spill).
{ apply (htr_rw _ _ _ _ m m' PR _ _ SP); rewrite SPS; [apply acl_stack; lia|].
apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|].
apply rng_out_cons; [exact (iv_stack_own OUT_rep IO_FP X HX a h HSP _ _ S1 248 IVD ltac:(lia) ltac:(lia))|]. apply rng_out_nil. }
assert (LSH' : rw_cells bsegs m' sf [CB 16 HSH_P1]).
{ apply (htr_rw _ _ _ _ m m' PR _ _ LSH); cbn [cells_size csize Nat.add]; [apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|].
apply rng_out_cons; [exact (iv_fshadow_own X a h HSP _ _ sf 16 IVD ltac:(lia) ltac:(lia))|]. apply rng_out_nil. }

assert (FRT : forall A cs, rw_cells bsegs m A cs -> F + 32 <= A -> A + Z.of_nat (cells_size cs) <= F + 9252 ->
(A + Z.of_nat (cells_size cs) <= F + 8480 \/ F + 8512 <= A) -> (A + Z.of_nat (cells_size cs) <= F + 8544 \/ F + 8576 <= A) ->
rw_cells bsegs m' A cs).
{ intros A cs C H1 H2 H3 H4. apply (htr_rw _ _ _ _ m m' PR _ _ C); [apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|].
apply rng_out_cons; [exact (iv_frame_own X a h HSP _ _ A (Z.of_nat (cells_size cs)) IVD ltac:(lia) ltac:(lia))|]. apply rng_out_nil. }
assert (ENH' : rw_cells bsegs m' (F + 32) [CB 56 je]) by (apply (FRT _ _ ENH); cbn [cells_size csize Nat.add]; lia).
assert (OUTB' : rw_cells bsegs m' (F + 128) (f32 ows)) by (apply (FRT _ _ OUTB); rewrite ?cells_size_f32, ?LOWS; lia).
assert (FSZ' : rw_cells bsegs m' (F + 8384) [C4 (Z_to_bv 64 (h_frame_size h))]) by (apply (FRT _ _ FSZ); cbn [cells_size csize Nat.add]; lia).
assert (OPC' : rw_cells bsegs m' (F + 8608) opc) by (apply (FRT _ _ OPC); rewrite ?OPS; lia).
assert (STB' : rw_cells bsegs m' (F + 9168) [CB 24 stb]) by (apply (FRT _ _ STB); cbn [cells_size csize Nat.add]; lia).
assert (RATE' : rw_cells bsegs m' (F + 9232) [C4 (Z_to_bv 64 (h_rate h))]) by (apply (FRT _ _ RATE); cbn [cells_size csize Nat.add]; lia).
assert (LOOK' : rw_cells bsegs m' (F + 9248) [C4 (Z_to_bv 64 wl)]) by (apply (FRT _ _ LOOK); cbn [cells_size csize Nat.add]; lia).
clear FRT ENH OUTB FSZ OPC STB RATE LOOK.

assert (BOK : bits_ok (h_bits h)) by (destruct HP as (_ & _ & _ & _ & B & _); exact B).
assert (BITS' : bits_rep bsegs m' (F + 8400) (a_Dc a) (h_bits h)).
{ apply (bits_rep_tr _ _ _ _ m m' PR _ _ _ BITS BOK).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|].
apply rng_out_cons; [apply (iv_frame_own X a h HSP _ _ _ _ IVD); lia|]. apply rng_out_nil.
- apply (acl_live _ _ _ _ _ _ _ (INL _ (own_in_Dc a h))); lia.
- apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ (own_in_Dc a h)); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ (own_in_Dc a h)); lia|].
apply rng_out_cons; [apply (iv_own_own X a h HSP _ _ _ _ _ _ (own_in_Dc a h)); [lia| lia| apply IVNE; intros NS; exact (proj1 (ONE NS))]|].
apply rng_out_nil. }
clear BITS.

assert (OWNTR : forall p q, In (p, q) (h_own a h) -> (sy_data (h_oy h) <> None -> p <> a_Dsy a) ->
acl_rng (rt_live RT Σ1) [(F, 8%nat)] S1 p q
/\ rng_out [(F + 8480, F + 8480 + 32); (F + 8544, F + 8544 + 32); (a_Dsy a, a_Dsy a + Z.of_nat (length (a_sybytes a)))] p q).
{ intros p q Hin NE. split; [apply (acl_live _ _ _ _ _ _ _ (INL _ Hin)); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); lia|].
apply rng_out_cons; [apply (iv_own_own X a h HSP _ _ _ _ _ _ Hin); [lia| lia| apply IVNE; exact NE]|]. apply rng_out_nil. }
assert (OSR' : h_os_rep X m' a h).
{ apply (h_os_rep_tr _ _ _ _ m m' PR X a h OSR).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- unfold HO_OS. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|].
apply rng_out_cons; [apply (iv_frame_own X a h HSP _ _ _ _ IVD); lia|]. apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
destruct (OWNTR _ _ IB (fun NS => proj1 ((proj1 (proj2 (ONE NS))) NE))) as (B1 & B2).
destruct (OWNTR _ _ IL (fun NS => proj1 (proj2 ((proj1 (proj2 (ONE NS))) NE)))) as (L1 & L2).
destruct (OWNTR _ _ IG (fun NS => proj2 (proj2 ((proj1 (proj2 (ONE NS))) NE)))) as (G1 & G2).
exact (conj B1 (conj B2 (conj L1 (conj L2 (conj G1 G2))))). }
assert (DEC' : h_dec_rep X m' a h).
{ apply (h_dec_rep_tr _ _ _ _ m m' PR X a h DEC). intros b Hb.
assert (NS0 : h_st h <> None) by (unfold h_dec_rep in DEC; destruct (h_st h); [discriminate| destruct DEC as (_ & E); rewrite E in Hb; destruct Hb]).
apply (OWNTR _ _ (own_in_blk a h NS0 b Hb)). intros NS. exact (proj2 (proj2 (ONE NS)) NS0 b Hb). }
clear OSR DEC OWNTR.

pose proof (hpure_pageout h r ogo oy2 HP EPO) as HP'.
destruct (ogg_sync_pageout_inv2 _ _ _ _ SI2 EPO) as (_ & PGI).
split.
{ destruct HS as (A1 & A2 & A3 & A4 & A5 & A6 & A7). unfold hsig. rewrite EOWN.
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6| exact A7]. }
split.
2:{ destruct ogo as [og|]; [| exact PGI]. destruct PGI as (E1 & POK). split; [exact E1|]. split; [exact POK|].
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
exists (h_consumed X h). unfold h_consumed, h_pend in *. cbn [set_ogg h_oy h_os h_bytes_remaining h_packet_count].
destruct PGF as (G1 & G2). unfold bptr in *. rewrite EFL. repeat split; lia. }
unfold hrep. unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK.
cbn [set_ogg h_oy h_os h_bits h_st h_frame_size h_rate].
split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact PF'|]. split; [exact ERR'|]. split; [exact OUTR'|]. split; [exact SSP'|].
split; [exact SP'|]. split; [exact LSH'|]. split; [exists je; exact ENH'|]. split; [exists ows; split; [exact OUTB'| exact LOWS]|].
split; [exact FSZ'|]. split; [exact BITS'|]. split; [exact SY'|]. split; [exact OG'|]. split; [exact OPC'|].
split; [exact OSR'|]. split; [exists stb; exact STB'|]. split; [exact RATE'|]. split; [exists wl; split; [exact LOOK'| first [exact LKR | (let HH := fresh in intros HH; apply LKR; congruence)]]|].
split; [exact DEC'| exact HP'].
Qed.

Lemma sbuf_inv2 : forall (sy : sync_st bptr) n, sync_inv2 sy -> sync_inv2 (snd (sync_buffer_res sy n)).
Proof.
intros sy n I2. unfold sync_buffer_res.
assert (C2 : sync_inv2 (sy_compact sy)).
{ unfold sy_compact. destruct (negb (sy_returned sy =? 0)); [apply sync_compact_inv2; exact I2| exact I2]. }
destruct (_ <? n); cbn [snd]; [| exact C2].
destruct C2 as (C1 & H). split; [unfold sync_inv in *; cbn; exact C1| unfold sync_hdr in *; cbn; exact H].
Qed.
Lemma sbuf_facts : forall (sy : sync_st bptr) n, sync_inv sy -> sync_fields_ok sy -> 0 < n -> (sy_data sy = None <-> sy_storage sy = 0) -> 0 <= sy_storage sy ->
fst (sync_buffer_res sy n) = Some (tt, sy_fill sy - sy_returned sy)
/\ sy_fill (snd (sync_buffer_res sy n)) = sy_fill sy - sy_returned sy /\ sy_returned (snd (sync_buffer_res sy n)) = 0
/\ sy_data (snd (sync_buffer_res sy n)) = Some tt /\ sy_buf (snd (sync_buffer_res sy n)) = sy_buf (sy_compact sy)
/\ (sy_storage sy - (sy_fill sy - sy_returned sy) >= n -> sy_storage (snd (sync_buffer_res sy n)) = sy_storage sy)
/\ (sy_storage sy - (sy_fill sy - sy_returned sy) < n -> sy_storage (snd (sync_buffer_res sy n)) = n + (sy_fill sy - sy_returned sy) + 4096).
Proof.
intros sy n SI FOK N0 DN S0. destruct (sy_compact_facts sy SI FOK) as (CS & CD & CR & CF & _).
unfold sync_buffer_res. rewrite CS, CF.
destruct (Z.ltb_spec (sy_storage sy - (sy_fill sy - sy_returned sy)) n) as [LT|GE]; cbn [fst snd sy_fill sy_returned sy_data sy_buf sy_storage].
- rewrite CR. repeat split; try reflexivity; lia.
- rewrite CD. destruct (sy_data sy) as [[]|] eqn:ED.
+ rewrite ?CR, ?CF, ?CD. repeat split; try reflexivity; lia.
+ destruct DN as (DN & _). specialize (DN eq_refl). pose proof SI as (R0 & _). lia.
Qed.

Lemma live_remove_cons : forall p e l, live_remove p (e :: l) = if fst e =? p then live_remove p l else e :: live_remove p l.
Proof.
intros p e l. unfold live_remove. rewrite stdpp.list_basics.list.filter_cons.
destruct (fst e =? p); reflexivity.
Qed.
Lemma perm_live_remove : forall p l l', Permutation l l' -> Permutation (live_remove p l) (live_remove p l').
Proof. intros p l l' P. induction P as [|x l l' P IH|x y l|l l' l'' P1 IH1 P2 IH2]; rewrite ?live_remove_cons.
- apply perm_nil.
- destruct (fst x =? p); [exact IH| apply perm_skip; exact IH].
- destruct (fst x =? p), (fst y =? p); try apply perm_swap; apply Permutation_refl.
- exact (perm_trans IH1 IH2).
Qed.
Lemma nodup_fst_live_remove : forall p l, List.NoDup (map fst l) -> List.NoDup (map fst (live_remove p l)).
Proof.
intros p l. induction l as [|x l IH]; intros ND; [exact ND|]. rewrite live_remove_cons.
cbn [map] in ND. apply NoDup_cons_iff in ND as (NI & ND). destruct (fst x =? p); [exact (IH ND)|].
cbn [map]. constructor; [| exact (IH ND)]. intros Hin. apply NI. apply in_map_iff in Hin as (e & E & He).
rewrite <- E. apply in_map. exact (live_remove_sub _ _ _ He).
Qed.
Lemma live_remove_app : forall p l1 l2, live_remove p (l1 ++ l2) = live_remove p l1 ++ live_remove p l2.
Proof. intros p l1 l2. induction l1 as [|x l1 IH]; [reflexivity|]. cbn [app]. rewrite !live_remove_cons, IH. destruct (fst x =? p); reflexivity. Qed.
Lemma live_remove_none : forall p l, (forall e, In e l -> fst e <> p) -> live_remove p l = l.
Proof.
intros p l H. induction l as [|x l IH]; [reflexivity|]. rewrite live_remove_cons.
replace (fst x =? p) with false by (symmetry; apply Z.eqb_neq; apply H; left; reflexivity).
f_equal. apply IH. intros e He. apply H. right. exact He.
Qed.
Lemma live_remove_last : forall p n R, (forall e, In e R -> fst e <> p) -> live_remove p (R ++ [(p, n)]) = R.
Proof.
intros p n R H. rewrite live_remove_app, (live_remove_none p R H), live_remove_cons. cbn [fst]. rewrite Z.eqb_refl. apply app_nil_r.
Qed.

Lemma own_pos : forall (Σ1 : rts RT) (m : mem) a h spill ogc opc, hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
forall p q, In (p, q) (h_own a h) -> 0 < q.
Proof.
intros Σ1 m a h spill ogc opc HR p q Hin.
destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OSR & _ & _ & _ & DEC & HP).
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
Definition a_set_sync (a : haux) (D : Z) (bs : list byte) (P : list (Z * Z)) : haux :=
HA D bs (a_Bd a) (a_L a) (a_G a) (a_shdr a) (a_body a) (a_lws a) (a_gws a) (a_Dc a) (a_S a) (a_LBD a) P.

Lemma hrep_sbuf : forall (Σ1 Σ2 : rts RT) (m m' : mem) a h spill ogc opc nbr D' bytes',
hsig RT X Σ1 a h -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 248%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat -> 0 < nbr <= 200 ->
rt_after_f RT Σ2 S1 lo m m' ->
rt_pres_fp (sync_rest_live (h_oy h) (a_Dsy a) (rt_live RT Σ1)) (rt_frames RT Σ1) S1 [(F + 8480, F + 8480 + 32)] m m' ->
sync_rep m' (F + 8480) D' (snd (sync_buffer_res (h_oy h) nbr)) bytes' ->
((sy_storage (h_oy h) - (sy_fill (h_oy h) - sy_returned (h_oy h)) >= nbr /\ D' = a_Dsy a /\ rt_live RT Σ2 = rt_live RT Σ1)
\/ (sy_storage (h_oy h) - (sy_fill (h_oy h) - sy_returned (h_oy h)) < nbr
/\ rt_live RT Σ2 = (D', nbr + (sy_fill (h_oy h) - sy_returned (h_oy h)) + 4096) :: sync_rest_live (h_oy h) (a_Dsy a) (rt_live RT Σ1))) ->
rt_frames RT Σ2 = rt_frames RT Σ1 -> rt_sp0 RT Σ2 = rt_sp0 RT Σ1 -> rt_credit RT Σ2 = rt_credit RT Σ1 -> rt_pois RT Σ2 = rt_pois RT Σ1 ->
exists P', hsig RT X Σ2 (a_set_sync a D' bytes' P') (set_ogg h (snd (sync_buffer_res (h_oy h) nbr)) (h_os h))
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ2 m' (a_set_sync a D' bytes' P') (set_ogg h (snd (sync_buffer_res (h_oy h) nbr)) (h_os h)) spill ogc opc.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV.
intros Σ1 Σ2 m m' a h spill ogc opc nbr D' bytes' HS HR SPS OGS OPS NB (ART' & MI' & ST') PR SY' CASE EF2 ES2 EC2 EP2.
pose proof (own_pos Σ1 m a h spill ogc opc HR) as OPOS.
destruct HR as (ART & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC & OSR & (stb & STB)
& RATE & (wl & LOOK & LKR) & DEC & HP).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART HS) as HSP.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
rewrite EF in PR.
pose proof HP as (SI2 & SI & STB0 & SDN & _).
pose proof SY as (_ & FOK & _).
destruct (sbuf_facts (h_oy h) nbr SI FOK ltac:(lia) SDN (proj1 STB0)) as (EFST & EFILL & ERET & EDATA & EBUF & SNOG & SGRO).
set (oy1 := snd (sync_buffer_res (h_oy h) nbr)) in *. unfold bptr in *.

assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
assert (INL' : forall p q, In (p, q) (h_own a h) -> (sy_data (h_oy h) <> None -> p <> a_Dsy a) ->
In (p, q) (sync_rest_live (h_oy h) (a_Dsy a) (rt_live RT Σ1))).
{ intros p q Hin NE. unfold sync_rest_live, bptr. destruct (sy_data (h_oy h)) eqn:ED; [| exact (INL _ Hin)].
apply live_remove_keep; [exact (INL _ Hin)|]. cbn [fst]. apply NE. discriminate. }
assert (XL : forall e, In e (x_live X) -> In e (sync_rest_live (h_oy h) (a_Dsy a) (rt_live RT Σ1))).
{ intros [q k] Hq. unfold sync_rest_live, bptr. assert (IX : In (q, k) (rt_live RT Σ1)) by (rewrite EL; apply in_or_app; right; exact Hq).
destruct (sy_data (h_oy h)) eqn:ED; [| exact IX].
apply live_remove_keep; [exact IX|]. cbn [fst]. intros ->.
assert (INS : In (a_Dsy a, sy_storage (h_oy h)) (h_own a h)) by (apply own_in_Dsy; rewrite ED; discriminate).
destruct (proj1 HSP _ _ INS) as (_ & _ & _ & _ & _ & SEP). pose proof (OPOS _ _ INS) as P1.
pose proof (proj1 (hi_live _ _ _ HX) _ _ Hq) as P2. destruct (SEP _ _ Hq); lia. }
pose proof (own_ne_Dsy a h (proj2 (proj2 HSP))) as ONE.
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK in *.
change (fs_size 8) with 16384 in *.

assert (FRT : forall A cs, rw_cells bsegs m A cs -> F + 32 <= A -> A + Z.of_nat (cells_size cs) <= F + 9252 ->
(A + Z.of_nat (cells_size cs) <= F + 8480 \/ F + 8512 <= A) -> rw_cells bsegs m' A cs).
{ intros A cs C H1 H2 H3. apply (htr_rw _ _ _ _ m m' PR _ _ C); [apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [lia|]. apply rng_out_nil. }
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
{ apply (htr_rw _ _ _ _ m m' PR _ _ SP); rewrite SPS; [apply acl_stack; lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (LSH' : rw_cells bsegs m' sf [CB 16 HSH_P1]).
{ apply (htr_rw _ _ _ _ m m' PR _ _ LSH); cbn [cells_size csize Nat.add]; [apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [lia|]. apply rng_out_nil. }

assert (OWNTR : forall p q, In (p, q) (h_own a h) -> (sy_data (h_oy h) <> None -> p <> a_Dsy a) ->
acl_rng (sync_rest_live (h_oy h) (a_Dsy a) (rt_live RT Σ1)) [(F, 8%nat)] S1 p q /\ rng_out [(F + 8480, F + 8480 + 32)] p q).
{ intros p q Hin NE. split; [apply (acl_live _ _ _ _ _ _ _ (INL' _ _ Hin NE)); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); lia|]. apply rng_out_nil. }
assert (BOK : bits_ok (h_bits h)) by (destruct HP as (_ & _ & _ & _ & B & _); exact B).
assert (BITS' : bits_rep bsegs m' (F + 8400) (a_Dc a) (h_bits h)).
{ destruct (OWNTR _ _ (own_in_Dc a h) (fun NS => proj1 (ONE NS))) as (D1 & D2).
apply (bits_rep_tr _ _ _ _ m m' PR _ _ _ BITS BOK); [| | exact D1| exact D2].
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (OSR' : h_os_rep X m' a h).
{ apply (h_os_rep_tr _ _ _ _ m m' PR X a h OSR).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- unfold HO_OS. apply rng_out_cons; [lia|]. apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
destruct (OWNTR _ _ IB (fun NS => proj1 ((proj1 (proj2 (ONE NS))) NE))) as (B1 & B2).
destruct (OWNTR _ _ IL (fun NS => proj1 (proj2 ((proj1 (proj2 (ONE NS))) NE)))) as (L1 & L2).
destruct (OWNTR _ _ IG (fun NS => proj2 (proj2 ((proj1 (proj2 (ONE NS))) NE)))) as (G1 & G2).
exact (conj B1 (conj B2 (conj L1 (conj L2 (conj G1 G2))))). }
assert (DEC' : h_dec_rep X m' a h).
{ apply (h_dec_rep_tr _ _ _ _ m m' PR X a h DEC). intros b Hb.
assert (NS0 : h_st h <> None) by (unfold h_dec_rep in DEC; destruct (h_st h); [discriminate| destruct DEC as (_ & E); rewrite E in Hb; destruct Hb]).
apply (OWNTR _ _ (own_in_blk a h NS0 b Hb)). intros NS. exact (proj2 (proj2 (ONE NS)) NS0 b Hb). }
clear OSR DEC BITS OWNTR.

assert (FPH : fp_h X a h [(F + 8480, F + 8480 + 32)]) by (apply fp_h_cons; [right; right; left; lia| apply fp_h_nil]).
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ1 m m' a h _ _ HSP PR XL FPH (AF_DRV _ _ ART') PF ERR OUTR SSP)
as (PF' & ERR' & OUTR' & SSP').

assert (PEND : 0 <= sy_fill (h_oy h) - sy_returned (h_oy h) <= 4096).
{ destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BR & _ & P1 & P2 & _). unfold h_consumed, h_pend in *.
pose proof (hi_pay _ _ _ HX) as (_ & SZ & _). unfold MAX_FUZZ_SIZE in SZ. lia. }
assert (SPOS : 0 < sy_storage oy1 <= 64512).
{ destruct (Z_lt_ge_dec (sy_storage (h_oy h) - (sy_fill (h_oy h) - sy_returned (h_oy h))) nbr) as [LT|GE]; [rewrite (SGRO LT); lia| rewrite (SNOG GE); lia]. }
assert (HP' : hpure X (set_ogg h oy1 (h_os h))).
{ unfold hpure, h_consumed, h_pend in *.
cbn [set_ogg h_oy h_os h_bits h_st h_stream_init h_packet_count h_last_granule h_nframes h_eos h_channels h_rate h_extra_headers
h_speex_serialno h_frame_size h_granule_frame_size h_bytes_remaining].
destruct HP as (_ & _ & _ & _ & REST).
pose proof (sbuf_inv2 (h_oy h) nbr SI2) as SI2'. fold oy1 in SI2'.
split; [exact SI2'|]. split; [exact (proj1 SI2')|]. split; [lia|]. split; [rewrite EDATA; split; [intros E; discriminate E| intros E; lia]|].
destruct REST as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
do 16 (split; [assumption|]). rewrite EFILL, ERET. repeat split; lia. }

assert (HR' : forall P', hrep RT OUT_rep ERR_rep IO_FP X Σ2 m' (a_set_sync a D' bytes' P') (set_ogg h oy1 (h_os h)) spill ogc opc).
{ intros P'. unfold hrep. unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK.
cbn [a_set_sync a_Dc a_Dsy a_sybytes set_ogg h_oy h_os h_bits h_st h_frame_size h_rate].
split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact PF'|]. split; [exact ERR'|]. split; [exact OUTR'|]. split; [exact SSP'|].
split; [exact SP'|]. split; [exact LSH'|]. split; [exists je; exact ENH'|]. split; [exists ows; split; [exact OUTB'| exact LOWS]|].
split; [exact FSZ'|]. split; [exact BITS'|]. split; [exact SY'|]. split; [exact OGC'|]. split; [exact OPC'|].
split; [exact OSR'|]. split; [exists stb; exact STB'|]. split; [exact RATE'|]. split; [exists wl; split; [exact LOOK'| first [exact LKR | (let HH := fresh in intros HH; apply LKR; congruence)]]|].
split; [exact DEC'| exact HP']. }
destruct CASE as [(GE & -> & E2) | (LT & E2)].
-
exists (a_P a). split; [| apply HR'].
assert (ED0 : sy_data (h_oy h) = Some tt).
{ destruct (sy_data (h_oy h)) as [[]|] eqn:ED; [reflexivity|]. exfalso. destruct SDN as (DN & _). specialize (DN eq_refl). lia. }
assert (EOWN : h_own (a_set_sync a (a_Dsy a) bytes' (a_P a)) (set_ogg h oy1 (h_os h)) = h_own a h).
{ unfold h_own. cbn [a_set_sync a_Dsy a_Dc a_Bd a_L a_G a_LBD set_ogg h_oy h_os h_bits h_st h_stream_init]. rewrite EDATA, ED0, (SNOG GE). reflexivity. }
unfold hsig. rewrite EOWN. cbn [a_set_sync a_P]. rewrite E2, EF2, ES2, EP2, EC2.
split; [exact EL|]. split; [exact ND|]. split; [exact PERM|]. split; [exact EF|]. split; [exact ESP|]. split; [exact EPO0| exact ECR].
-
set (n' := nbr + (sy_fill (h_oy h) - sy_returned (h_oy h)) + 4096) in *.
assert (XNE : sy_data (h_oy h) <> None -> forall e, In e (x_live X) -> fst e <> a_Dsy a).
{ intros NS [q k] Hq E. cbn [fst] in E. subst q.
assert (INS : In (a_Dsy a, sy_storage (h_oy h)) (h_own a h)) by (apply own_in_Dsy; exact NS).
destruct (proj1 HSP _ _ INS) as (_ & _ & _ & _ & _ & SEP). pose proof (OPOS _ _ INS) as P1.
pose proof (proj1 (hi_live _ _ _ HX) _ _ Hq) as P2. destruct (SEP _ _ Hq); lia. }
assert (ESR : sync_rest_live (h_oy h) (a_Dsy a) (rt_live RT Σ1) = sync_rest_live (h_oy h) (a_Dsy a) (a_P a) ++ x_live X).
{ rewrite EL. unfold sync_rest_live, bptr. destruct (sy_data (h_oy h)) eqn:ED; [| reflexivity].
rewrite live_remove_app, (live_remove_none _ (x_live X)); [reflexivity|]. apply XNE. first [discriminate | rewrite ED; discriminate]. }

assert (PCORE : Permutation (sync_rest_live (h_oy h) (a_Dsy a) (a_P a))
((match h_st h with Some _ => blocks_live (a_LBD a) | None => [] end ++ [(a_Dc a, sb_buf_size (h_bits h))])
++ (if h_stream_init h =? 0 then [] else [(a_Bd a, os_body_storage (h_os h)); (a_L a, 4 * os_lacing_storage (h_os h));
(a_G a, 8 * os_lacing_storage (h_os h))]))).
{ pose proof PERM as PERM1. pose proof (proj2 (proj2 HSP)) as NDO. unfold h_own in PERM1, NDO. unfold sync_rest_live, bptr.
destruct (sy_data (h_oy h)) eqn:ED.
- rewrite !app_assoc in PERM1, NDO.
lazymatch type of PERM1 with Permutation _ (?core ++ [_]) =>
transitivity (live_remove (a_Dsy a) (core ++ [(a_Dsy a, sy_storage (h_oy h))])); [apply perm_live_remove; exact PERM1|];
rewrite live_remove_last; [apply Permutation_refl|] end.
intros e He E. rewrite map_app in NDO. apply (nodup_app_disj _ _ (a_Dsy a) NDO); [rewrite <- E; apply in_map; exact He| left; reflexivity].
- rewrite app_nil_r, !app_assoc in PERM1. exact PERM1. }
exists ((D', n') :: sync_rest_live (h_oy h) (a_Dsy a) (a_P a)). split; [| apply HR'].
assert (EOWN : h_own (a_set_sync a D' bytes' ((D', n') :: sync_rest_live (h_oy h) (a_Dsy a) (a_P a))) (set_ogg h oy1 (h_os h))
= ((match h_st h with Some _ => blocks_live (a_LBD a) | None => [] end ++ [(a_Dc a, sb_buf_size (h_bits h))])
++ (if h_stream_init h =? 0 then [] else [(a_Bd a, os_body_storage (h_os h)); (a_L a, 4 * os_lacing_storage (h_os h));
(a_G a, 8 * os_lacing_storage (h_os h))])) ++ [(D', n')]).
{ unfold h_own. cbn [a_set_sync a_Dsy a_Dc a_Bd a_L a_G a_LBD set_ogg h_oy h_os h_bits h_st h_stream_init]. rewrite EDATA, (SGRO LT).
rewrite !app_assoc. reflexivity. }
unfold hsig. rewrite EOWN. cbn [a_set_sync a_P]. rewrite EF2, ES2, EP2, EC2.
split; [rewrite E2, ESR; reflexivity|].
assert (CORE_OWN : forall e, In e ((match h_st h with Some _ => blocks_live (a_LBD a) | None => [] end ++ [(a_Dc a, sb_buf_size (h_bits h))])
++ (if h_stream_init h =? 0 then [] else [(a_Bd a, os_body_storage (h_os h)); (a_L a, 4 * os_lacing_storage (h_os h));
(a_G a, 8 * os_lacing_storage (h_os h))])) -> In e (h_own a h)).
{ intros e He. unfold h_own. rewrite !app_assoc. apply in_or_app. left. exact He. }
split.
{ cbn [map]. constructor.
- intros Hin. apply in_map_iff in Hin as ((p & q) & Ep & Hq). cbn [fst] in Ep. subst p.
pose proof (OPOS _ _ (CORE_OWN _ (Permutation_in _ PCORE Hq))) as QP.
assert (HT : In (D', q) (sync_rest_live (h_oy h) (a_Dsy a) (rt_live RT Σ1))) by (rewrite ESR; apply in_or_app; left; exact Hq).
destruct (af_live_disj RT AF Σ2 m' D' n' D' q [] _ ART' E2 HT); unfold n' in *; lia.
- unfold sync_rest_live, bptr. destruct (sy_data (h_oy h)); [apply nodup_fst_live_remove; exact ND| exact ND]. }
split; [exact (perm_trans (perm_skip _ PCORE) (Permutation_cons_append _ _))|].
split; [exact EF|]. split; [exact ESP|]. split; [exact EPO0| exact ECR].
Qed.

Lemma h_bytes_at_app3 : forall (m : mem) A (a b d : list byte) B D,
bytes_at bsegs m A a -> bytes_at bsegs m B b -> bytes_at bsegs m D d ->
B = A + Z.of_nat (length a) -> D = B + Z.of_nat (length b) ->
bytes_at bsegs m A (a ++ b ++ d).
Proof.
intros m A a b d B D Ha Hb Hd -> ->. apply bytes_at_app. split; [exact Ha|]. apply bytes_at_app. split; [exact Hb|].
rewrite <- Z.add_assoc, <- Nat2Z.inj_add. rewrite Nat2Z.inj_add, Z.add_assoc. exact Hd.
Qed.
Lemma h_wr_at_app3 : forall (m : mem) A na nb nd, 0 <= na -> 0 <= nb -> 0 <= nd ->
wr_at bsegs m A na -> wr_at bsegs m (A + na) nb -> wr_at bsegs m (A + na + nb) nd -> wr_at bsegs m A (na + nb + nd).
Proof.
intros m A na nb nd Ha Hb Hd Wa Wb Wd. replace (na + nb + nd) with (na + (nb + nd)) by lia.
apply (proj2 (wr_at_app bsegs m A na (nb + nd) Ha ltac:(lia))). split; [exact Wa|].
apply (proj2 (wr_at_app bsegs m (A + na) nb nd Hb Hd)). split; assumption.
Qed.
Lemma h_u8arr_window : forall (m : mem) D bs i n,
u8arr bsegs m D bs -> 0 <= i -> 0 <= n -> i + n <= Z.of_nat (length bs) ->
u8arr bsegs m D (firstn (Z.to_nat i) bs)
/\ rw_cells bsegs m (D + i) [CB (Z.to_nat n) (firstn (Z.to_nat n) (skipn (Z.to_nat i) bs))]
/\ u8arr bsegs m (D + i + n) (skipn (Z.to_nat (i + n)) bs).
Proof.
intros m D bs i n [B W] Hi Hn Hin.
rewrite <- (firstn_skipn (Z.to_nat i) bs) in B. apply bytes_at_app in B. destruct B as [B1 B23].
rewrite firstn_length_le in B23 by lia. rewrite Z2Nat.id in B23 by lia.
rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat i) bs)) in B23. apply bytes_at_app in B23. destruct B23 as [B2 B3].
rewrite firstn_length_le in B3 by (rewrite length_skipn; lia). rewrite Z2Nat.id in B3 by lia.
rewrite skipn_skipn in B3. replace (Z.to_nat n + Z.to_nat i)%nat with (Z.to_nat (i + n)) in B3 by lia.
pose proof W as (W0 & W1 & Wi).
split; [| split].
- split; [exact B1|]. rewrite firstn_length_le by lia. rewrite Z2Nat.id by lia. split; [lia|]. split; [lia|]. intros k Hk. apply Wi. lia.
- split; [split|].
+ cbn. rewrite firstn_length_le by (rewrite length_skipn; lia). split; [reflexivity| exact I].
+ cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact B2.
+ cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. split; [lia|]. split; [lia|]. intros k Hk.
replace (D + i + k) with (D + (i + k)) by lia. apply Wi. lia.
- split; [exact B3|]. rewrite length_skipn. split; [lia|]. split; [lia|]. intros k Hk.
replace (D + i + n + k) with (D + (i + n + k)) by lia. apply Wi. lia.
Qed.
Lemma h_u8arr_unwindow : forall (m : mem) D (a : list byte) n (mid : list byte) (b : list byte) i,
u8arr bsegs m D a -> Z.of_nat (length a) = i ->
rw_cells bsegs m (D + i) [CB (Z.to_nat n) mid] -> 0 <= n ->
u8arr bsegs m (D + i + n) b ->
u8arr bsegs m D (a ++ mid ++ b) /\ Z.of_nat (length (a ++ mid ++ b)) = i + n + Z.of_nat (length b).
Proof.
intros m D a n mid b i [Ba Wa] La [[Hwf Bm] Wm] Hn [Bb Wb].
cbn in Hwf. destruct Hwf as [Lm _]. cbn [cells_bytes cbytes app] in Bm. rewrite app_nil_r in Bm.
cbn [cells_size csize Nat.add] in Wm. rewrite Nat.add_0_r, Z2Nat.id in Wm by lia.
assert (L : Z.of_nat (length (a ++ mid ++ b)) = i + n + Z.of_nat (length b)) by (rewrite !length_app; lia).
split; [| exact L]. split.
- eapply h_bytes_at_app3; [exact Ba| exact Bm| exact Bb| lia| lia].
- rewrite L. apply h_wr_at_app3; try lia; [rewrite <- La; exact Wa| exact Wm| exact Wb].
Qed.
Lemma h_firstn_firstn_le : forall {A : Type} (l : list A) n k, (n <= k)%nat -> firstn n (firstn k l) = firstn n l.
Proof. intros A l n k H. rewrite firstn_firstn. f_equal. lia. Qed.

Lemma h_sync_rep_write : forall (m m' : mem) A D (sy : sync_st bptr) (bytes : list byte) (q : bptr) (nb : Z) (src : list byte),
sync_rep m A D sy bytes -> sync_inv sy -> sy_data sy = Some q -> 0 <= nb -> sy_fill sy + nb <= sy_storage sy ->
Z.of_nat (length src) = nb ->
rw_cells bsegs m' A (sync_cells D sy) ->
u8arr bsegs m' D (firstn (Z.to_nat (sy_fill sy)) bytes ++ src ++ skipn (Z.to_nat (sy_fill sy + nb)) bytes) ->
sync_rep m' A D (sync_write sy (sy_fill sy) (ubytes src))
(firstn (Z.to_nat (sy_fill sy)) bytes ++ src ++ skipn (Z.to_nat (sy_fill sy + nb)) bytes).
Proof.
intros m m' A D sy bytes q nb src (OBJ & FOK & DAT & SEP) INV ED Hnb Hroom Lsrc OBJ' ARR'.
unfold sync_data in DAT. rewrite ED in DAT. destruct DAT as (Dpos & ARR & LEN & PRE & LE).
pose proof INV as (I1 & I2 & _). pose proof FOK as (Fs & Ff & Fr & _). unfold int31 in Fs, Ff, Fr. unfold zlength in I2.
assert (LB : Z.of_nat (length (firstn (Z.to_nat (sy_fill sy)) bytes ++ src ++ skipn (Z.to_nat (sy_fill sy + nb)) bytes)) = sy_storage sy).
{ rewrite !length_app, firstn_length_le, length_skipn by lia. lia. }
split; [| split; [| split]].
- unfold sync_write. cbn. exact OBJ'.
- unfold sync_fields_ok, sync_write in *. cbn. exact FOK.
- unfold sync_data, sync_write. cbn. rewrite ED. split; [exact Dpos|]. split; [exact ARR'|]. split; [exact LB|].
assert (L1 : length (ztake (sy_fill sy) (sy_buf sy) ++ ubytes src) = (Z.to_nat (sy_fill sy) + length src)%nat).
{ rewrite length_app. unfold ztake, ubytes. rewrite firstn_length_le, length_map by lia. reflexivity. }
split.
+ rewrite L1. unfold ubytes. rewrite !map_app. rewrite firstn_app. rewrite length_map, firstn_length_le by lia.
replace (Z.to_nat (sy_fill sy) + length src - Z.to_nat (sy_fill sy))%nat with (length src) by lia.
rewrite (@firstn_all2 _ _ (map bv_unsigned (firstn (Z.to_nat (sy_fill sy)) bytes))) by (rewrite length_map, firstn_length_le by lia; lia).
rewrite firstn_app, length_map, Nat.sub_diag, firstn_O, app_nil_r.
rewrite (@firstn_all2 _ _ (map bv_unsigned src)) by (rewrite length_map; lia).
f_equal. unfold ztake. rewrite <- PRE. rewrite h_firstn_firstn_le by lia. unfold ubytes. rewrite firstn_map. reflexivity.
+ rewrite L1, !length_app, firstn_length_le, length_skipn by lia. lia.
- destruct SEP as [S1|S2]; [left| right; exact S2]. lia.
Qed.

Lemma hrep_memcpy : forall (Σ1 : rts RT) (m m' : mem) a h spill ogc opc nbr,
hsig RT X Σ1 a h -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 248%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat ->
sy_data (h_oy h) = Some tt -> 0 <= nbr -> sy_fill (h_oy h) + nbr <= sy_storage (h_oy h) -> nbr <= x_size X ->
rt_after RT Σ1 S1 lo m m' ->
rt_pres_ex (rt_live RT Σ1) (rt_frames RT Σ1) S1 (a_Dsy a + sy_fill (h_oy h)) nbr m m' ->
bytes_at bsegs m' (a_Dsy a + sy_fill (h_oy h)) (firstn (Z.to_nat nbr) (x_bs X)) ->
hsig RT X Σ1 (a_set_sync a (a_Dsy a) (firstn (Z.to_nat (sy_fill (h_oy h))) (a_sybytes a) ++ firstn (Z.to_nat nbr) (x_bs X)
++ skipn (Z.to_nat (sy_fill (h_oy h) + nbr)) (a_sybytes a)) (a_P a))
(set_ogg h (sync_write (h_oy h) (sy_fill (h_oy h)) (ztake nbr (x_payload X))) (h_os h))
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ1 m'
(a_set_sync a (a_Dsy a) (firstn (Z.to_nat (sy_fill (h_oy h))) (a_sybytes a) ++ firstn (Z.to_nat nbr) (x_bs X)
++ skipn (Z.to_nat (sy_fill (h_oy h) + nbr)) (a_sybytes a)) (a_P a))
(set_ogg h (sync_write (h_oy h) (sy_fill (h_oy h)) (ztake nbr (x_payload X))) (h_os h)) spill ogc opc.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV.
intros Σ1 m m' a h spill ogc opc nbr HS HR SPS OGS OPS ED NB ROOM NBS (ART' & MI' & WM' & ST') PRX SRC.
pose proof (own_pos Σ1 m a h spill ogc opc HR) as OPOS.
destruct HR as (ART & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC & OSR & (stb & STB)
& RATE & (wl & LOOK & LKR) & DEC & HP).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART HS) as HSP.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
rewrite EF in PRX.
set (d := a_Dsy a + sy_fill (h_oy h)) in *.
assert (PR : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 [(d, d + nbr)] m m').
{ apply (pres_fp_of_ex _ _ _ d nbr _ m m' PRX). intros x Hx Ho. cbn [outside] in Ho. lia. }
pose proof HP as (SI2 & SI & STB0 & SDN & _).
unfold bptr in *.

assert (INS : In (a_Dsy a, sy_storage (h_oy h)) (h_own a h)) by (apply own_in_Dsy; rewrite ED; discriminate).
assert (IVD : iv_own a h d (d + nbr)).
{ right. exists (a_Dsy a), (sy_storage (h_oy h)). split; [exact INS|]. pose proof SI as (R0 & _). unfold d. lia. }
assert (IVNE : forall p0, p0 <> a_Dsy a -> iv_own_ne a h p0 d (d + nbr)).
{ intros p0 NE. right. exists (a_Dsy a), (sy_storage (h_oy h)). split; [exact INS|]. split; [congruence|]. pose proof SI as (R0 & _). unfold d. lia. }
pose proof (own_ne_Dsy a h (proj2 (proj2 HSP)) ltac:(rewrite ED; discriminate)) as (NDc & NOS & NBLK).
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK in *.
change (fs_size 8) with 16384 in *.
assert (FRT : forall A cs, rw_cells bsegs m A cs -> F + 32 <= A -> A + Z.of_nat (cells_size cs) <= F + 9252 -> rw_cells bsegs m' A cs).
{ intros A cs C H1 H2. apply (htr_rw _ _ _ _ m m' PR _ _ C); [apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [apply (iv_frame_own X a h HSP _ _ _ _ IVD); lia|]. apply rng_out_nil. }
assert (ENH' : rw_cells bsegs m' (F + 32) [CB 56 je]) by (apply (FRT _ _ ENH); cbn [cells_size csize Nat.add]; lia).
assert (OUTB' : rw_cells bsegs m' (F + 128) (f32 ows)) by (apply (FRT _ _ OUTB); rewrite ?cells_size_f32, ?LOWS; lia).
assert (FSZ' : rw_cells bsegs m' (F + 8384) [C4 (Z_to_bv 64 (h_frame_size h))]) by (apply (FRT _ _ FSZ); cbn [cells_size csize Nat.add]; lia).
assert (OGC' : rw_cells bsegs m' (F + 8544) ogc) by (apply (FRT _ _ OGC); rewrite ?OGS; lia).
assert (OPC' : rw_cells bsegs m' (F + 8608) opc) by (apply (FRT _ _ OPC); rewrite ?OPS; lia).
assert (STB' : rw_cells bsegs m' (F + 9168) [CB 24 stb]) by (apply (FRT _ _ STB); cbn [cells_size csize Nat.add]; lia).
assert (RATE' : rw_cells bsegs m' (F + 9232) [C4 (Z_to_bv 64 (h_rate h))]) by (apply (FRT _ _ RATE); cbn [cells_size csize Nat.add]; lia).
assert (LOOK' : rw_cells bsegs m' (F + 9248) [C4 (Z_to_bv 64 wl)]) by (apply (FRT _ _ LOOK); cbn [cells_size csize Nat.add]; lia).
destruct SY as (SYC & FOK & DAT & SYSEP).
assert (SYC' : rw_cells bsegs m' (F + 8480) (sync_cells (a_Dsy a) (h_oy h))) by (apply (FRT _ _ SYC); rewrite ?(eq_refl : Z.of_nat (cells_size (sync_cells (a_Dsy a) (h_oy h))) = 32); cbn; lia).
clear FRT ENH OUTB FSZ OGC OPC STB RATE LOOK.
assert (SP' : rw_cells bsegs m' S1 spill).
{ apply (htr_rw _ _ _ _ m m' PR _ _ SP); rewrite SPS; [apply acl_stack; lia|].
apply rng_out_cons; [exact (iv_stack_own OUT_rep IO_FP X HX a h HSP _ _ S1 248 IVD ltac:(lia) ltac:(lia))|]. apply rng_out_nil. }
assert (LSH' : rw_cells bsegs m' sf [CB 16 HSH_P1]).
{ apply (htr_rw _ _ _ _ m m' PR _ _ LSH); cbn [cells_size csize Nat.add]; [apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [exact (iv_fshadow_own X a h HSP _ _ sf 16 IVD ltac:(lia) ltac:(lia))|]. apply rng_out_nil. }

assert (OWNTR : forall p q, In (p, q) (h_own a h) -> p <> a_Dsy a ->
acl_rng (rt_live RT Σ1) [(F, 8%nat)] S1 p q /\ rng_out [(d, d + nbr)] p q).
{ intros p q Hin NE. split; [apply (acl_live _ _ _ _ _ _ _ (INL _ Hin)); lia|].
apply rng_out_cons; [apply (iv_own_own X a h HSP _ _ _ _ _ _ Hin); [lia| lia| apply IVNE; exact NE]|]. apply rng_out_nil. }
assert (BOK : bits_ok (h_bits h)) by (destruct HP as (_ & _ & _ & _ & B & _); exact B).
assert (BITS' : bits_rep bsegs m' (F + 8400) (a_Dc a) (h_bits h)).
{ destruct (OWNTR _ _ (own_in_Dc a h) NDc) as (D1 & D2).
apply (bits_rep_tr _ _ _ _ m m' PR _ _ _ BITS BOK); [| | exact D1| exact D2].
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [apply (iv_frame_own X a h HSP _ _ _ _ IVD); lia|]. apply rng_out_nil. }
assert (OSR' : h_os_rep X m' a h).
{ apply (h_os_rep_tr _ _ _ _ m m' PR X a h OSR).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- unfold HO_OS. apply rng_out_cons; [apply (iv_frame_own X a h HSP _ _ _ _ IVD); lia|]. apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG). destruct (NOS NE) as (NB1 & NL1 & NG1).
destruct (OWNTR _ _ IB NB1) as (B1 & B2). destruct (OWNTR _ _ IL NL1) as (L1 & L2). destruct (OWNTR _ _ IG NG1) as (G1 & G2).
exact (conj B1 (conj B2 (conj L1 (conj L2 (conj G1 G2))))). }
assert (DEC' : h_dec_rep X m' a h).
{ apply (h_dec_rep_tr _ _ _ _ m m' PR X a h DEC). intros b Hb.
assert (NS0 : h_st h <> None) by (unfold h_dec_rep in DEC; destruct (h_st h); [discriminate| destruct DEC as (_ & E); rewrite E in Hb; destruct Hb]).
apply (OWNTR _ _ (own_in_blk a h NS0 b Hb)). exact (NBLK NS0 b Hb). }
clear OSR DEC BITS OWNTR.

pose proof DAT as DAT0. unfold sync_data, bptr in DAT0. rewrite ED in DAT0. destruct DAT0 as (Dpos & ARR & LEN & PRE & LE).
pose proof SI as (R0 & FB & _). pose proof FOK as (Fs & Ff & _). unfold int31 in Fs, Ff.
destruct (h_u8arr_window m (a_Dsy a) (a_sybytes a) (sy_fill (h_oy h)) nbr ARR ltac:(lia) ltac:(lia) ltac:(lia)) as (W1 & WIN & W3).
assert (W1' : u8arr bsegs m' (a_Dsy a) (firstn (Z.to_nat (sy_fill (h_oy h))) (a_sybytes a))).
{ apply (htr_u8 _ _ _ _ m m' PR _ _ W1); rewrite firstn_length_le by lia; rewrite Z2Nat.id by lia.
- apply (acl_live _ _ _ _ _ _ _ (INL _ INS)); lia.
- apply rng_out_cons; [unfold d; lia|]. apply rng_out_nil. }
assert (W3' : u8arr bsegs m' (a_Dsy a + sy_fill (h_oy h) + nbr) (skipn (Z.to_nat (sy_fill (h_oy h) + nbr)) (a_sybytes a))).
{ apply (htr_u8 _ _ _ _ m m' PR _ _ W3); rewrite length_skipn.
- apply (acl_live _ _ _ _ _ _ _ (INL _ INS)); lia.
- apply rng_out_cons; [unfold d; lia|]. apply rng_out_nil. }
assert (LSRC : Z.of_nat (length (firstn (Z.to_nat nbr) (x_bs X))) = nbr) by (rewrite firstn_length_le; unfold x_size in NBS; lia).
assert (WIN' : rw_cells bsegs m' (a_Dsy a + sy_fill (h_oy h)) [CB (Z.to_nat nbr) (firstn (Z.to_nat nbr) (x_bs X))]).
{ destruct WIN as (_ & (W0 & W1w & Ww)). cbn [cells_size csize Nat.add] in W1w, Ww. rewrite Nat.add_0_r, Z2Nat.id in W1w by lia. rewrite Nat.add_0_r, Z2Nat.id in Ww by lia.
split; [split|].
- cbn. split; [lia| exact I].
- cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact SRC.
- cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. split; [exact W0|]. split; [exact W1w|]. intros i Hi. exact (WM' _ (Ww i Hi)). }
destruct (h_u8arr_unwindow m' (a_Dsy a) _ nbr _ _ (sy_fill (h_oy h)) W1' ltac:(rewrite firstn_length_le by lia; lia) WIN' NB W3') as (ARR' & LEN').
pose proof (h_sync_rep_write m m' (F + 8480) (a_Dsy a) (h_oy h) (a_sybytes a) tt nbr _ (conj SYC (conj FOK (conj DAT SYSEP))) SI ED NB ROOM LSRC SYC' ARR') as SY'.
assert (EUB : ubytes (firstn (Z.to_nat nbr) (x_bs X)) = ztake nbr (x_payload X)) by (unfold ubytes, ztake, x_payload; rewrite firstn_map; reflexivity).
rewrite EUB in SY'.

assert (FPH : fp_h X a h [(d, d + nbr)]) by (apply fp_h_cons; [right; right; right; exact IVD| apply fp_h_nil]).
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ1 m m' a h _ _ HSP PR
ltac:(intros e He; rewrite EL; apply in_or_app; right; exact He) FPH (AF_DRV _ _ ART') PF ERR OUTR SSP) as (PF' & ERR' & OUTR' & SSP').

assert (BOKP : bytes_ok (ztake nbr (x_payload X))).
{ apply bytes_ok_ztake. unfold bytes_ok, x_payload. apply Forall_map. apply Forall_forall. intros b _.
pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. }
destruct (sync_write_inv (h_oy h) (ztake nbr (x_payload X)) SI BOKP) as (SWI & SWL & SWF & SWR & SWS).
pose proof (sync_write_inv2 (h_oy h) (ztake nbr (x_payload X)) SI2 BOKP) as SWI2.
assert (SWD : sy_data (sync_write (h_oy h) (sy_fill (h_oy h)) (ztake nbr (x_payload X))) = sy_data (h_oy h)) by reflexivity.
set (oyw := sync_write (h_oy h) (sy_fill (h_oy h)) (ztake nbr (x_payload X))) in *.
assert (HP' : hpure X (set_ogg h oyw (h_os h))).
{ unfold hpure, h_consumed, h_pend in *.
cbn [set_ogg h_oy h_os h_bits h_st h_stream_init h_packet_count h_last_granule h_nframes h_eos h_channels h_rate h_extra_headers
h_speex_serialno h_frame_size h_granule_frame_size h_bytes_remaining].
destruct HP as (_ & _ & S3 & S4 & REST). rewrite SWS, SWD, SWF, SWR.
split; [exact SWI2|]. split; [exact SWI|]. split; [exact S3|]. split; [exact S4| exact REST]. }
assert (EOWN : h_own (a_set_sync a (a_Dsy a) (firstn (Z.to_nat (sy_fill (h_oy h))) (a_sybytes a) ++ firstn (Z.to_nat nbr) (x_bs X)
++ skipn (Z.to_nat (sy_fill (h_oy h) + nbr)) (a_sybytes a)) (a_P a)) (set_ogg h oyw (h_os h)) = h_own a h).
{ unfold h_own. cbn [a_set_sync a_Dsy a_Dc a_Bd a_L a_G a_LBD set_ogg h_oy h_os h_bits h_st h_stream_init]. rewrite SWD, SWS. reflexivity. }
split.
{ unfold hsig. rewrite EOWN. cbn [a_set_sync a_P].
split; [exact EL|]. split; [exact ND|]. split; [exact PERM|]. split; [exact EF|]. split; [exact ESP|]. split; [exact EPO0| exact ECR]. }
unfold hrep. unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK.
cbn [a_set_sync a_Dc a_Dsy a_sybytes set_ogg h_oy h_os h_bits h_st h_frame_size h_rate].
split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact PF'|]. split; [exact ERR'|]. split; [exact OUTR'|]. split; [exact SSP'|].
split; [exact SP'|]. split; [exact LSH'|]. split; [exists je; exact ENH'|]. split; [exists ows; split; [exact OUTB'| exact LOWS]|].
split; [exact FSZ'|]. split; [exact BITS'|]. split; [exact SY'|]. split; [exact OGC'|]. split; [exact OPC'|].
split; [exact OSR'|]. split; [exists stb; exact STB'|]. split; [exact RATE'|]. split; [exists wl; split; [exact LOOK'| first [exact LKR | (let HH := fresh in intros HH; apply LKR; congruence)]]|].
split; [exact DEC'| exact HP'].
Qed.

Lemma wrote_ok : forall (sy : sync_st unit) n, 0 <= sy_storage sy -> sy_fill sy + n <= sy_storage sy ->
ogg_sync_wrote sy n = (0, mkSync (sy_data sy) (sy_buf sy) (sy_storage sy) (sy_fill sy + n) (sy_returned sy) (sy_unsynced sy) (sy_headerbytes sy) (sy_bodybytes sy)).
Proof.
intros sy n S0 R. unfold ogg_sync_wrote, ogg_sync_check.
replace (sy_storage sy <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
replace (sy_storage sy <? sy_fill sy + n) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma hrep_wrote : forall (Σ1 : rts RT) (m m1 : mem) a h spill spill' ogc opc nbr,
hsig RT X Σ1 a h -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 248%nat -> cells_size spill' = 248%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat ->
0 <= nbr <= h_bytes_remaining h -> sy_fill (h_oy h) + nbr <= sy_storage (h_oy h) -> sy_fill (h_oy h) + nbr <= zlength (sy_buf (h_oy h)) ->
munch [(S1, S1 + 248); (F + 8480, F + 8480 + 32)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
sync_rep m1 (F + 8480) (a_Dsy a) (snd (ogg_sync_wrote (h_oy h) nbr)) (a_sybytes a) -> rw_cells bsegs m1 S1 spill' ->
hsig RT X Σ1 a (set_bytes_remaining h (snd (ogg_sync_wrote (h_oy h) nbr)) (h_bytes_remaining h - nbr))
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ1 m1 a (set_bytes_remaining h (snd (ogg_sync_wrote (h_oy h) nbr)) (h_bytes_remaining h - nbr)) spill' ogc opc.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV.
intros Σ1 m m1 a h spill spill' ogc opc nbr HS HR SPS SPS' OGS OPS NB ROOM RB MU WM MI1 SY1 SP1.
pose proof (own_pos Σ1 m a h spill ogc opc HR) as OPOS.
destruct HR as (ART0 & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC & OSR & (stb & STB)
& RATE & (wl & LOOK & LKR) & DEC & HP).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART0 HS) as HSP.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
assert (PR : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 [(S1, S1 + 248); (F + 8480, F + 8480 + 32)] m m1).
{ apply (pres_fp_of_munch _ _ _ _ _ m m1 MU). intros x _ Ho. exact Ho. }

assert (ART1 : ART RT Σ1 m1).
{ apply (af_frame RT AF Σ1 m m1 S1 ART0); [rewrite ESP; pose proof (hi_lo _ _ _ HX) as (LW0 & _); unfold STACK_WIN in *; lia| | exact WM].
intros b Hb. apply MU. cbn [outside]. rewrite EF in Hb. split; [intros Hin; apply Hb; left; unfold USTACK_TOP in *; lia|].
split; [intros Hin; apply Hb; right; right; right; left; exists F, 8%nat; split; [left; reflexivity| change (fs_size 8) with 16384; lia]| exact I]. }
assert (ST1 : stk bsegs m1 lo S1).
{ apply (stk_agree bsegs m m1 lo S1 ST); [| exact WM]. apply (agree_of_munch _ m m1 _ MU). intros x Hx. cbn [outside]. split; [lia|]. split; [lia| exact I]. }
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK in *.
change (fs_size 8) with 16384 in *.
assert (FRT : forall A cs, rw_cells bsegs m A cs -> F + 32 <= A -> A + Z.of_nat (cells_size cs) <= F + 9252 ->
(A + Z.of_nat (cells_size cs) <= F + 8480 \/ F + 8512 <= A) -> rw_cells bsegs m1 A cs).
{ intros A cs C H1 H2 H3. apply (htr_rw _ _ _ _ m m1 PR _ _ C); [apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (ENH' : rw_cells bsegs m1 (F + 32) [CB 56 je]) by (apply (FRT _ _ ENH); cbn [cells_size csize Nat.add]; lia).
assert (OUTB' : rw_cells bsegs m1 (F + 128) (f32 ows)) by (apply (FRT _ _ OUTB); rewrite ?cells_size_f32, ?LOWS; lia).
assert (FSZ' : rw_cells bsegs m1 (F + 8384) [C4 (Z_to_bv 64 (h_frame_size h))]) by (apply (FRT _ _ FSZ); cbn [cells_size csize Nat.add]; lia).
assert (OGC' : rw_cells bsegs m1 (F + 8544) ogc) by (apply (FRT _ _ OGC); rewrite ?OGS; lia).
assert (OPC' : rw_cells bsegs m1 (F + 8608) opc) by (apply (FRT _ _ OPC); rewrite ?OPS; lia).
assert (STB' : rw_cells bsegs m1 (F + 9168) [CB 24 stb]) by (apply (FRT _ _ STB); cbn [cells_size csize Nat.add]; lia).
assert (RATE' : rw_cells bsegs m1 (F + 9232) [C4 (Z_to_bv 64 (h_rate h))]) by (apply (FRT _ _ RATE); cbn [cells_size csize Nat.add]; lia).
assert (LOOK' : rw_cells bsegs m1 (F + 9248) [C4 (Z_to_bv 64 wl)]) by (apply (FRT _ _ LOOK); cbn [cells_size csize Nat.add]; lia).
clear FRT ENH OUTB FSZ OGC OPC STB RATE LOOK.
assert (LSH' : rw_cells bsegs m1 sf [CB 16 HSH_P1]).
{ apply (htr_rw _ _ _ _ m m1 PR _ _ LSH); cbn [cells_size csize Nat.add]; [apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
unfold SH_HI in *. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (OWNTR : forall p q, In (p, q) (h_own a h) ->
acl_rng (rt_live RT Σ1) [(F, 8%nat)] S1 p q /\ rng_out [(S1, S1 + 248); (F + 8480, F + 8480 + 32)] p q).
{ intros p q Hin. split; [apply (acl_live _ _ _ _ _ _ _ (INL _ Hin)); lia|].
apply rng_out_cons; [apply (iv_own_stack OUT_rep IO_FP X HX a h HSP _ _ _ _ _ _ Hin); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); lia|]. apply rng_out_nil. }
assert (BOK : bits_ok (h_bits h)) by (destruct HP as (_ & _ & _ & _ & B & _); exact B).
assert (BITS' : bits_rep bsegs m1 (F + 8400) (a_Dc a) (h_bits h)).
{ destruct (OWNTR _ _ (own_in_Dc a h)) as (D1 & D2).
apply (bits_rep_tr _ _ _ _ m m1 PR _ _ _ BITS BOK); [| | exact D1| exact D2].
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (OSR' : h_os_rep X m1 a h).
{ apply (h_os_rep_tr _ _ _ _ m m1 PR X a h OSR).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- unfold HO_OS. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
destruct (OWNTR _ _ IB) as (B1 & B2). destruct (OWNTR _ _ IL) as (L1 & L2). destruct (OWNTR _ _ IG) as (G1 & G2).
exact (conj B1 (conj B2 (conj L1 (conj L2 (conj G1 G2))))). }
assert (DEC' : h_dec_rep X m1 a h).
{ apply (h_dec_rep_tr _ _ _ _ m m1 PR X a h DEC). intros b Hb.
assert (NS0 : h_st h <> None) by (unfold h_dec_rep in DEC; destruct (h_st h); [discriminate| destruct DEC as (_ & E); rewrite E in Hb; destruct Hb]).
apply (OWNTR _ _ (own_in_blk a h NS0 b Hb)). }
clear OSR DEC BITS OWNTR.
assert (FPH : fp_h X a h [(S1, S1 + 248); (F + 8480, F + 8480 + 32)]).
{ apply fp_h_cons; [left; lia|]. apply fp_h_cons; [right; right; left; lia|]. apply fp_h_nil. }
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ1 m m1 a h _ _ HSP PR
ltac:(intros e He; rewrite EL; apply in_or_app; right; exact He) FPH (AF_DRV _ _ ART1) PF ERR OUTR SSP) as (PF' & ERR' & OUTR' & SSP').

pose proof HP as (SI2 & SI & (S0 & _) & _).
pose proof (wrote_ok (h_oy h) nbr S0 ROOM) as EW.
pose proof (ogg_sync_wrote_inv2 (h_oy h) nbr 0 _ SI2 ltac:(lia) RB EW) as SWI2.
rewrite EW in SY1 |- *. cbn [snd] in SY1 |- *.
set (oyr := mkSync (sy_data (h_oy h)) (sy_buf (h_oy h)) (sy_storage (h_oy h)) (sy_fill (h_oy h) + nbr) (sy_returned (h_oy h))
(sy_unsynced (h_oy h)) (sy_headerbytes (h_oy h)) (sy_bodybytes (h_oy h))) in *.
assert (HP' : hpure X (set_bytes_remaining h oyr (h_bytes_remaining h - nbr))).
{ unfold hpure, h_consumed, h_pend in *.
cbn [set_bytes_remaining h_oy h_os h_bits h_st h_stream_init h_packet_count h_last_granule h_nframes h_eos h_channels h_rate h_extra_headers
h_speex_serialno h_frame_size h_granule_frame_size h_bytes_remaining].
unfold oyr. cbn [sy_data sy_storage sy_fill sy_returned].
destruct HP as (_ & _ & S3 & S4 & REST).
split; [exact SWI2|]. split; [exact (proj1 SWI2)|]. split; [exact S3|]. split; [exact S4|].
destruct REST as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
do 14 (split; [assumption|]). split; [lia|]. split; [assumption|]. repeat split; lia. }
assert (EOWN : h_own a (set_bytes_remaining h oyr (h_bytes_remaining h - nbr)) = h_own a h) by reflexivity.
split.
{ unfold hsig. rewrite EOWN.
split; [exact EL|]. split; [exact ND|]. split; [exact PERM|]. split; [exact EF|]. split; [exact ESP|]. split; [exact EPO0| exact ECR]. }
unfold hrep. unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK.
cbn [set_bytes_remaining h_oy h_os h_bits h_st h_frame_size h_rate].
split; [exact ART1|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact PF'|]. split; [exact ERR'|]. split; [exact OUTR'|]. split; [exact SSP'|].
split; [exact SP1|]. split; [exact LSH'|]. split; [exists je; exact ENH'|]. split; [exists ows; split; [exact OUTB'| exact LOWS]|].
split; [exact FSZ'|]. split; [exact BITS'|]. split; [exact SY1|]. split; [exact OGC'|]. split; [exact OPC'|].
split; [exact OSR'|]. split; [exists stb; exact STB'|]. split; [exact RATE'|]. split; [exists wl; split; [exact LOOK'| first [exact LKR | (let HH := fresh in intros HH; apply LKR; congruence)]]|].
split; [exact DEC'| exact HP'].
Qed.

Lemma hrep_spill : forall (Σ1 : rts RT) (m m1 : mem) a h spill spill' ogc opc,
hsig RT X Σ1 a h -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 248%nat -> cells_size spill' = 248%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat ->
munch [(S1, S1 + 248)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> rw_cells bsegs m1 S1 spill' ->
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m1 a h spill' ogc opc.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV.
intros Σ1 m m1 a h spill spill' ogc opc HS HR SPS SPS' OGS OPS MU WM MI1 SP1.
destruct HR as (ART0 & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC & OSR & (stb & STB)
& RATE & (wl & LOOK & LKR) & DEC & HP).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART0 HS) as HSP.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
assert (PR : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 [(S1, S1 + 248)] m m1).
{ apply (pres_fp_of_munch _ _ _ _ _ m m1 MU). intros x _ Ho. exact Ho. }
assert (ART1 : ART RT Σ1 m1).
{ apply (af_frame RT AF Σ1 m m1 S1 ART0); [rewrite ESP; pose proof (hi_lo _ _ _ HX) as (LW0 & _); unfold STACK_WIN in *; lia| | exact WM].
intros b Hb. apply MU. cbn [outside]. rewrite EF in Hb. split; [intros Hin; apply Hb; left; unfold USTACK_TOP in *; lia| exact I]. }
assert (ST1 : stk bsegs m1 lo S1).
{ apply (stk_agree bsegs m m1 lo S1 ST); [| exact WM]. apply (agree_of_munch _ m m1 _ MU). intros x Hx. cbn [outside]. split; [lia| exact I]. }
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK in *.
change (fs_size 8) with 16384 in *.
assert (FRT : forall A cs, rw_cells bsegs m A cs -> F + 32 <= A -> A + Z.of_nat (cells_size cs) <= F + 9252 -> rw_cells bsegs m1 A cs).
{ intros A cs C H1 H2. apply (htr_rw _ _ _ _ m m1 PR _ _ C); [apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (ENH' : rw_cells bsegs m1 (F + 32) [CB 56 je]) by (apply (FRT _ _ ENH); cbn [cells_size csize Nat.add]; lia).
assert (OUTB' : rw_cells bsegs m1 (F + 128) (f32 ows)) by (apply (FRT _ _ OUTB); rewrite ?cells_size_f32, ?LOWS; lia).
assert (FSZ' : rw_cells bsegs m1 (F + 8384) [C4 (Z_to_bv 64 (h_frame_size h))]) by (apply (FRT _ _ FSZ); cbn [cells_size csize Nat.add]; lia).
assert (OGC' : rw_cells bsegs m1 (F + 8544) ogc) by (apply (FRT _ _ OGC); rewrite ?OGS; lia).
assert (OPC' : rw_cells bsegs m1 (F + 8608) opc) by (apply (FRT _ _ OPC); rewrite ?OPS; lia).
assert (STB' : rw_cells bsegs m1 (F + 9168) [CB 24 stb]) by (apply (FRT _ _ STB); cbn [cells_size csize Nat.add]; lia).
assert (RATE' : rw_cells bsegs m1 (F + 9232) [C4 (Z_to_bv 64 (h_rate h))]) by (apply (FRT _ _ RATE); cbn [cells_size csize Nat.add]; lia).
assert (LOOK' : rw_cells bsegs m1 (F + 9248) [C4 (Z_to_bv 64 wl)]) by (apply (FRT _ _ LOOK); cbn [cells_size csize Nat.add]; lia).
clear FRT ENH OUTB FSZ OGC OPC STB RATE LOOK.
assert (LSH' : rw_cells bsegs m1 sf [CB 16 HSH_P1]).
{ apply (htr_rw _ _ _ _ m m1 PR _ _ LSH); cbn [cells_size csize Nat.add]; [apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
unfold SH_HI in *. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (OWNTR : forall p q, In (p, q) (h_own a h) -> acl_rng (rt_live RT Σ1) [(F, 8%nat)] S1 p q /\ rng_out [(S1, S1 + 248)] p q).
{ intros p q Hin. split; [apply (acl_live _ _ _ _ _ _ _ (INL _ Hin)); lia|].
apply rng_out_cons; [apply (iv_own_stack OUT_rep IO_FP X HX a h HSP _ _ _ _ _ _ Hin); lia|]. apply rng_out_nil. }
assert (BOK : bits_ok (h_bits h)) by (destruct HP as (_ & _ & _ & _ & B & _); exact B).
assert (BITS' : bits_rep bsegs m1 (F + 8400) (a_Dc a) (h_bits h)).
{ destruct (OWNTR _ _ (own_in_Dc a h)) as (D1 & D2).
apply (bits_rep_tr _ _ _ _ m m1 PR _ _ _ BITS BOK); [| | exact D1| exact D2].
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (SY' : sync_rep m1 (F + 8480) (a_Dsy a) (h_oy h) (a_sybytes a)).
{ apply (sync_rep_tr _ _ _ _ m m1 PR _ _ _ _ SY).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia|]. apply rng_out_nil.
- intros NS. exact (OWNTR _ _ (own_in_Dsy a h NS)). }
assert (OSR' : h_os_rep X m1 a h).
{ apply (h_os_rep_tr _ _ _ _ m m1 PR X a h OSR).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- unfold HO_OS. apply rng_out_cons; [lia|]. apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
destruct (OWNTR _ _ IB) as (B1 & B2). destruct (OWNTR _ _ IL) as (L1 & L2). destruct (OWNTR _ _ IG) as (G1 & G2).
exact (conj B1 (conj B2 (conj L1 (conj L2 (conj G1 G2))))). }
assert (DEC' : h_dec_rep X m1 a h).
{ apply (h_dec_rep_tr _ _ _ _ m m1 PR X a h DEC). intros b Hb.
assert (NS0 : h_st h <> None) by (unfold h_dec_rep in DEC; destruct (h_st h); [discriminate| destruct DEC as (_ & E); rewrite E in Hb; destruct Hb]).
apply (OWNTR _ _ (own_in_blk a h NS0 b Hb)). }
clear OSR DEC BITS OWNTR SY.
assert (FPH : fp_h X a h [(S1, S1 + 248)]) by (apply fp_h_cons; [left; lia| apply fp_h_nil]).
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ1 m m1 a h _ _ HSP PR
ltac:(intros e He; rewrite EL; apply in_or_app; right; exact He) FPH (AF_DRV _ _ ART1) PF ERR OUTR SSP) as (PF' & ERR' & OUTR' & SSP').
unfold hrep. unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK.
split; [exact ART1|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact PF'|]. split; [exact ERR'|]. split; [exact OUTR'|]. split; [exact SSP'|].
split; [exact SP1|]. split; [exact LSH'|]. split; [exists je; exact ENH'|]. split; [exists ows; split; [exact OUTB'| exact LOWS]|].
split; [exact FSZ'|]. split; [exact BITS'|]. split; [exact SY'|]. split; [exact OGC'|]. split; [exact OPC'|].
split; [exact OSR'|]. split; [exists stb; exact STB'|]. split; [exact RATE'|]. split; [exists wl; split; [exact LOOK'| first [exact LKR | (let HH := fresh in intros HH; apply LKR; congruence)]]|].
split; [exact DEC'| exact HP].
Qed.

Lemma h_live_len : forall (Σ1 : rts RT) a h, hsig RT X Σ1 a h ->
Z.of_nat (length (rt_live RT Σ1)) = Z.of_nat (length (h_own a h)) + Z.of_nat (length (x_live X)).
Proof. intros Σ1 a h (EL & _ & PERM & _). rewrite EL, length_app, (Permutation_length PERM). lia. Qed.
Lemma h_own_len : forall (Σ1 : rts RT) (m : mem) a h spill ogc opc, hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
(length (h_own a h) <= 24)%nat.
Proof.
intros Σ1 m a h spill ogc opc HR. destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DEC & _).
unfold h_own. rewrite !length_app. unfold h_dec_rep in DEC.
destruct (h_st h) as [d|]; [destruct DEC as (_ & _ & _ & _ & _ & _ & _ & _ & LL)|];
destruct (h_stream_init h =? 0); destruct (sy_data (h_oy h)); cbn [length]; unfold blocks_live; rewrite ?length_map; lia.
Qed.

End Steps.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).

Lemma pageout_ret : forall (sy sy' : sync_st unit) r og, ogg_sync_pageout sy = Some ((r, og), sy') -> r = 1 \/ r = 0 \/ r = -1.
Proof.
intros sy sy' r og E. unfold ogg_sync_pageout in E. destruct (ogg_sync_check sy). { inversion E. lia. }
revert E. generalize (pageout_fuel sy) as fuel. intros fuel. revert sy.
induction fuel as [|fuel IH]; intros sy E; [discriminate|]. cbn [pageout_loop] in E.
destruct (ogg_sync_pageseek sy) as [[r1 og1] sy1].
destruct (0 <? r1); [inversion E; lia|]. destruct (r1 =? 0); [inversion E; lia|].
destruct (sy_unsynced sy1 =? 0); [inversion E; lia|]. eapply IH. exact E.
Qed.

Lemma h_drep_sizes_pos : forall (d : dec_state bptr) OUT STEREO (m : mem) S LBD, DREP OUT STEREO m S d LBD -> forall b, In b LBD -> 0 < blk_size b.
Proof.
induction d as [st|s low IHd]; intros OUT STEREO m S LBD H b Hb; cbn [decst_rep] in H.
- destruct H as [-> _]. destruct Hb as [<-|[]]. unfold blk_size, NBSTATE_SIZEOF. cbn. lia.
- destruct H as (a & j & LBL & -> & _ & _ & INV & _ & _ & _ & OUTL & RL). apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [| exact (IHd _ _ _ _ _ RL b Hb)].
destruct INV as (IM & _ & _ & ISF & _). assert (0 < sbd_subframeSize s) by (rewrite ISF; destruct IM as [E|E]; rewrite E; cbn; lia).
cbn [sb_blocks In] in Hb. unfold SBSTATE_SIZEOF in Hb.
repeat (destruct Hb as [<-|Hb]; [unfold blk_size; cbn [snd]; lia|]). destruct Hb.
Qed.

Lemma nodup_app_disj : forall {A : Type} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros A l1. induction l1 as [|y l1 IH]; intros l2 x ND H1 H2; [destruct H1|].
cbn [app] in ND. apply NoDup_cons_iff in ND as (NI & ND). destruct H1 as [<-|H1].
- apply NI. apply in_or_app. right. exact H2.
- exact (IH l2 x ND H1 H2).
Qed.

Section Own.
Variables (a : haux) (h : hstate unit).
Lemma own_in_Dc : In (a_Dc a, sb_buf_size (h_bits h)) (h_own a h).
Proof. unfold h_own. apply in_or_app. right. apply in_or_app. left. left. reflexivity. Qed.
Lemma own_in_Dsy : sy_data (h_oy h) <> None -> In (a_Dsy a, sy_storage (h_oy h)) (h_own a h).
Proof.
intros ND. unfold h_own. destruct (sy_data (h_oy h)) as [p|]; [| congruence].
apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. left. reflexivity.
Qed.
Lemma own_in_os : h_stream_init h <> 0 ->
In (a_Bd a, os_body_storage (h_os h)) (h_own a h) /\ In (a_L a, 4 * os_lacing_storage (h_os h)) (h_own a h)
/\ In (a_G a, 8 * os_lacing_storage (h_os h)) (h_own a h).
Proof.
intros NE. unfold h_own. replace (h_stream_init h =? 0) with false by (symmetry; apply Z.eqb_neq; exact NE).
split; [| split]; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; cbn; tauto.
Qed.
Lemma own_in_blk : h_st h <> None -> forall b, In b (a_LBD a) -> In (blk_addr b, blk_size b) (h_own a h).
Proof.
intros NE b Hb. unfold h_own. apply in_or_app. left. destruct (h_st h); [| congruence].
unfold blocks_live. apply in_map_iff. exists b. split; [reflexivity| exact Hb].
Qed.

Lemma own_ne_Dsy : List.NoDup (map fst (h_own a h)) -> sy_data (h_oy h) <> None ->
a_Dc a <> a_Dsy a /\ (h_stream_init h <> 0 -> a_Bd a <> a_Dsy a /\ a_L a <> a_Dsy a /\ a_G a <> a_Dsy a)
/\ (h_st h <> None -> forall b, In b (a_LBD a) -> blk_addr b <> a_Dsy a).
Proof.
intros ND NS. unfold h_own in ND. destruct (sy_data (h_oy h)) as [p|]; [| congruence].
rewrite !map_app in ND.
apply NoDup_app_remove_l in ND as ND1.
split; [| split].
- cbn [map fst app] in ND1. apply NoDup_cons_iff in ND1 as (N1 & _). intros E. apply N1. rewrite E. apply in_or_app. right. left. reflexivity.
- intros NE. replace (h_stream_init h =? 0) with false in ND1 by (symmetry; apply Z.eqb_neq; exact NE). cbn [map fst app] in ND1.
apply NoDup_cons_iff in ND1 as (_ & ND2). apply NoDup_cons_iff in ND2 as (B1 & ND3). apply NoDup_cons_iff in ND3 as (B2 & ND4).
apply NoDup_cons_iff in ND4 as (B3 & _). cbn in B1, B2, B3.
split; [| split]; intros E; [apply B1| apply B2| apply B3]; rewrite E; tauto.
- intros NE b Hb E. destruct (h_st h) as [d|]; [| congruence].
apply (nodup_app_disj _ _ (blk_addr b) ND); [unfold blocks_live; rewrite map_map; apply in_map_iff; exists b; split; [reflexivity| exact Hb]|].
rewrite E. apply in_or_app. right. apply in_or_app. right. left. reflexivity.
Qed.
End Own.

Section Steps.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Variable X : hinv.
Hypothesis HX : hinv_ok OUT_rep IO_FP X.
Local Notation S1 := (x_S1 X). Local Notation lo := (x_lo X). Local Notation F := (x_F X). Local Notation sf := (x_sf X).

Lemma hpure_pageout : forall h r ogo oy2, hpure X h -> ogg_sync_pageout (h_oy h) = Some ((r, ogo), oy2) -> hpure X (set_ogg h oy2 (h_os h)).
Proof.
intros h r ogo oy2 HP EPO. unfold hpure, h_consumed, h_pend in *.
cbn [set_ogg h_oy h_os h_bits h_st h_stream_init h_packet_count h_last_granule h_nframes h_eos h_channels h_rate h_extra_headers
h_speex_serialno h_frame_size h_granule_frame_size h_bytes_remaining].
destruct HP as (SI2 & SI & STB & SDN & REST).
destruct (ogg_sync_pageout_frame _ _ _ _ SI EPO) as (SI' & EFL & EBF & EDT & EST & RMO & _).
destruct (ogg_sync_pageout_inv2 _ _ _ _ SI2 EPO) as (SI2' & _).
rewrite EST, EDT. split; [exact SI2'|]. split; [exact SI'|]. split; [exact STB|]. split; [exact SDN|].
destruct SI' as (R0 & _).
destruct REST as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
do 16 (split; [assumption|]). rewrite EFL in *. repeat split; lia.
Qed.

Lemma hrep_pageout : forall (Σ1 : rts RT) (m m' : mem) a h spill opc j0 j1 j2 j3 r ogo oy2,
hsig RT X Σ1 a h ->
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3] opc ->
cells_size spill = 216%nat -> cells_size opc = 48%nat ->
ogg_sync_pageout (h_oy h) = Some ((r, ogo), oy2) ->
rt_after RT Σ1 S1 lo m m' ->
rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) S1
[(F + 8480, F + 8480 + 32); (F + 8544, F + 8544 + 32); (a_Dsy a, a_Dsy a + Z.of_nat (length (a_sybytes a)))] m m' ->
sync_rep m' (F + 8480) (a_Dsy a) oy2 (a_sybytes a) ->
rw_cells asegs m' (F + 8544) (og_cells (a_Dsy a) ogo [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3]) ->
hsig RT X Σ1 a (set_ogg h oy2 (h_os h))
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ1 m' a (set_ogg h oy2 (h_os h)) spill (og_cells (a_Dsy a) ogo [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3]) opc
/\ match ogo with Some og => r = 1 /\ page_ok oy2 og /\ h_page_budget X (set_ogg h oy2 (h_os h)) og | None => r <> 1 end.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV.
intros Σ1 m m' a h spill opc j0 j1 j2 j3 r ogo oy2 HS HR SPS OPS EPO (ART' & MI' & WM' & ST') PR SY' OG'.
destruct HR as (ART & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC & OSR & (stb & STB)
& RATE & (wl & LOOK) & DEC & HP).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART HS) as HSP.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
rewrite EF in PR.
pose proof HP as (SI2 & SI & STB0 & SDN & _).
destruct (ogg_sync_pageout_frame _ _ _ _ SI EPO) as (SI' & EFL & EBF & EDT & EST & RMO & PGF).
assert (EOWN : h_own a (set_ogg h oy2 (h_os h)) = h_own a h).
{ unfold h_own. cbn [set_ogg h_oy h_os h_bits h_st h_stream_init]. unfold bptr in EDT, EST. rewrite EDT, EST. reflexivity. }

assert (IVD : iv_own a h (a_Dsy a) (a_Dsy a + Z.of_nat (length (a_sybytes a)))).
{ destruct SY as (_ & _ & DAT & _). unfold sync_data, bptr in DAT. destruct (sy_data (h_oy h)) as [p|] eqn:ED.
- destruct DAT as (_ & _ & LB & _). right. exists (a_Dsy a), (sy_storage (h_oy h)). split; [apply own_in_Dsy; rewrite ED; discriminate|]. lia.
- destruct DAT as (_ & -> & _). left. cbn. lia. }
assert (FPH : fp_h X a h [(F + 8480, F + 8480 + 32); (F + 8544, F + 8544 + 32); (a_Dsy a, a_Dsy a + Z.of_nat (length (a_sybytes a)))]).
{ apply fp_h_cons; [right; right; left; lia|]. apply fp_h_cons; [right; right; left; lia|]. apply fp_h_cons; [right; right; right; exact IVD|]. apply fp_h_nil. }
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ1 m m' a h (rt_live RT Σ1) _ HSP PR
ltac:(intros e He; rewrite EL; apply in_or_app; right; exact He) FPH (AF_DRV _ _ ART') PF ERR OUTR SSP) as (PF' & ERR' & OUTR' & SSP').
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
unfold RT_STACK, H_STACK in LR.
unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK in *.
change (fs_size 8) with 16384 in *.

assert (IVNE : forall p0, (sy_data (h_oy h) <> None -> p0 <> a_Dsy a) -> iv_own_ne a h p0 (a_Dsy a) (a_Dsy a + Z.of_nat (length (a_sybytes a)))).
{ intros p0 NE. destruct SY as (_ & _ & DAT & _). unfold sync_data, bptr in DAT. destruct (sy_data (h_oy h)) as [p|] eqn:ED.
- destruct DAT as (_ & _ & LB & _). right. exists (a_Dsy a), (sy_storage (h_oy h)).
split; [apply own_in_Dsy; rewrite ED; discriminate|]. split; [apply not_eq_sym; apply NE; discriminate| lia].
- destruct DAT as (_ & -> & _). left. cbn. lia. }
pose proof (own_ne_Dsy a h (proj2 (proj2 HSP))) as ONE.

assert (SP' : rw_cells asegs m' S1 spill).
{ apply (htr_rw _ _ _ _ m m' PR _ _ SP); rewrite SPS; [apply acl_stack; lia|].
apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|].
apply rng_out_cons; [exact (iv_stack_own OUT_rep IO_FP X HX a h HSP _ _ S1 216 IVD ltac:(lia) ltac:(lia))|]. apply rng_out_nil. }
assert (LSH' : rw_cells asegs m' sf [CB 16 HSH_P1]).
{ apply (htr_rw _ _ _ _ m m' PR _ _ LSH); cbn [cells_size csize Nat.add]; [apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|].
apply rng_out_cons; [exact (iv_fshadow_own X a h HSP _ _ sf 16 IVD ltac:(lia) ltac:(lia))|]. apply rng_out_nil. }

assert (FRT : forall A cs, rw_cells asegs m A cs -> F + 32 <= A -> A + Z.of_nat (cells_size cs) <= F + 9252 ->
(A + Z.of_nat (cells_size cs) <= F + 8480 \/ F + 8512 <= A) -> (A + Z.of_nat (cells_size cs) <= F + 8544 \/ F + 8576 <= A) ->
rw_cells asegs m' A cs).
{ intros A cs C H1 H2 H3 H4. apply (htr_rw _ _ _ _ m m' PR _ _ C); [apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|].
apply rng_out_cons; [exact (iv_frame_own X a h HSP _ _ A (Z.of_nat (cells_size cs)) IVD ltac:(lia) ltac:(lia))|]. apply rng_out_nil. }
assert (ENH' : rw_cells asegs m' (F + 32) [CB 56 je]) by (apply (FRT _ _ ENH); cbn [cells_size csize Nat.add]; lia).
assert (OUTB' : rw_cells asegs m' (F + 128) (f32 ows)) by (apply (FRT _ _ OUTB); rewrite ?cells_size_f32, ?LOWS; lia).
assert (FSZ' : rw_cells asegs m' (F + 8384) [C4 (Z_to_bv 64 (h_frame_size h))]) by (apply (FRT _ _ FSZ); cbn [cells_size csize Nat.add]; lia).
assert (OPC' : rw_cells asegs m' (F + 8608) opc) by (apply (FRT _ _ OPC); rewrite ?OPS; lia).
assert (STB' : rw_cells asegs m' (F + 9168) [CB 24 stb]) by (apply (FRT _ _ STB); cbn [cells_size csize Nat.add]; lia).
assert (RATE' : rw_cells asegs m' (F + 9232) [C4 (Z_to_bv 64 (h_rate h))]) by (apply (FRT _ _ RATE); cbn [cells_size csize Nat.add]; lia).
assert (LOOK' : rw_cells asegs m' (F + 9248) [C4 wl]) by (apply (FRT _ _ LOOK); cbn [cells_size csize Nat.add]; lia).
clear FRT ENH OUTB FSZ OPC STB RATE LOOK.

assert (BOK : bits_ok (h_bits h)) by (destruct HP as (_ & _ & _ & _ & B & _); exact B).
assert (BITS' : bits_rep asegs m' (F + 8400) (a_Dc a) (h_bits h)).
{ apply (bits_rep_tr _ _ _ _ m m' PR _ _ _ BITS BOK).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|].
apply rng_out_cons; [apply (iv_frame_own X a h HSP _ _ _ _ IVD); lia|]. apply rng_out_nil.
- apply (acl_live _ _ _ _ _ _ _ (INL _ (own_in_Dc a h))); lia.
- apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ (own_in_Dc a h)); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ (own_in_Dc a h)); lia|].
apply rng_out_cons; [apply (iv_own_own X a h HSP _ _ _ _ _ _ (own_in_Dc a h)); [lia| lia| apply IVNE; intros NS; exact (proj1 (ONE NS))]|].
apply rng_out_nil. }
clear BITS.

assert (OWNTR : forall p q, In (p, q) (h_own a h) -> (sy_data (h_oy h) <> None -> p <> a_Dsy a) ->
acl_rng (rt_live RT Σ1) [(F, 8%nat)] S1 p q
/\ rng_out [(F + 8480, F + 8480 + 32); (F + 8544, F + 8544 + 32); (a_Dsy a, a_Dsy a + Z.of_nat (length (a_sybytes a)))] p q).
{ intros p q Hin NE. split; [apply (acl_live _ _ _ _ _ _ _ (INL _ Hin)); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); lia|].
apply rng_out_cons; [apply (iv_own_own X a h HSP _ _ _ _ _ _ Hin); [lia| lia| apply IVNE; exact NE]|]. apply rng_out_nil. }
assert (OSR' : h_os_rep X m' a h).
{ apply (h_os_rep_tr _ _ _ _ m m' PR X a h OSR).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- unfold HO_OS. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|].
apply rng_out_cons; [apply (iv_frame_own X a h HSP _ _ _ _ IVD); lia|]. apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
destruct (OWNTR _ _ IB (fun NS => proj1 ((proj1 (proj2 (ONE NS))) NE))) as (B1 & B2).
destruct (OWNTR _ _ IL (fun NS => proj1 (proj2 ((proj1 (proj2 (ONE NS))) NE)))) as (L1 & L2).
destruct (OWNTR _ _ IG (fun NS => proj2 (proj2 ((proj1 (proj2 (ONE NS))) NE)))) as (G1 & G2).
exact (conj B1 (conj B2 (conj L1 (conj L2 (conj G1 G2))))). }
assert (DEC' : h_dec_rep X m' a h).
{ apply (h_dec_rep_tr _ _ _ _ m m' PR X a h DEC). intros b Hb.
assert (NS0 : h_st h <> None) by (unfold h_dec_rep in DEC; destruct (h_st h); [discriminate| destruct DEC as (_ & E); rewrite E in Hb; destruct Hb]).
apply (OWNTR _ _ (own_in_blk a h NS0 b Hb)). intros NS. exact (proj2 (proj2 (ONE NS)) NS0 b Hb). }
clear OSR DEC OWNTR.

pose proof (hpure_pageout h r ogo oy2 HP EPO) as HP'.
destruct (ogg_sync_pageout_inv2 _ _ _ _ SI2 EPO) as (_ & PGI).
split.
{ destruct HS as (A1 & A2 & A3 & A4 & A5 & A6 & A7). unfold hsig. rewrite EOWN.
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6| exact A7]. }
split.
2:{ destruct ogo as [og|]; [| exact PGI]. destruct PGI as (E1 & POK). split; [exact E1|]. split; [exact POK|].
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
exists (h_consumed X h). unfold h_consumed, h_pend in *. cbn [set_ogg h_oy h_os h_bytes_remaining h_packet_count].
destruct PGF as (G1 & G2). unfold bptr in *. rewrite EFL. repeat split; lia. }
unfold hrep. unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK.
cbn [set_ogg h_oy h_os h_bits h_st h_frame_size h_rate].
split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact PF'|]. split; [exact ERR'|]. split; [exact OUTR'|]. split; [exact SSP'|].
split; [exact SP'|]. split; [exact LSH'|]. split; [exists je; exact ENH'|]. split; [exists ows; split; [exact OUTB'| exact LOWS]|].
split; [exact FSZ'|]. split; [exact BITS'|]. split; [exact SY'|]. split; [exact OG'|]. split; [exact OPC'|].
split; [exact OSR'|]. split; [exists stb; exact STB'|]. split; [exact RATE'|]. split; [exists wl; exact LOOK'|].
split; [exact DEC'| exact HP'].
Qed.

Lemma sbuf_inv2 : forall (sy : sync_st bptr) n, sync_inv2 sy -> sync_inv2 (snd (sync_buffer_res sy n)).
Proof.
intros sy n I2. unfold sync_buffer_res.
assert (C2 : sync_inv2 (sy_compact sy)).
{ unfold sy_compact. destruct (negb (sy_returned sy =? 0)); [apply sync_compact_inv2; exact I2| exact I2]. }
destruct (_ <? n); cbn [snd]; [| exact C2].
destruct C2 as (C1 & H). split; [unfold sync_inv in *; cbn; exact C1| unfold sync_hdr in *; cbn; exact H].
Qed.
Lemma sbuf_facts : forall (sy : sync_st bptr) n, sync_inv sy -> sync_fields_ok sy -> 0 < n -> (sy_data sy = None <-> sy_storage sy = 0) -> 0 <= sy_storage sy ->
fst (sync_buffer_res sy n) = Some (tt, sy_fill sy - sy_returned sy)
/\ sy_fill (snd (sync_buffer_res sy n)) = sy_fill sy - sy_returned sy /\ sy_returned (snd (sync_buffer_res sy n)) = 0
/\ sy_data (snd (sync_buffer_res sy n)) = Some tt /\ sy_buf (snd (sync_buffer_res sy n)) = sy_buf (sy_compact sy)
/\ (sy_storage sy - (sy_fill sy - sy_returned sy) >= n -> sy_storage (snd (sync_buffer_res sy n)) = sy_storage sy)
/\ (sy_storage sy - (sy_fill sy - sy_returned sy) < n -> sy_storage (snd (sync_buffer_res sy n)) = n + (sy_fill sy - sy_returned sy) + 4096).
Proof.
intros sy n SI FOK N0 DN S0. destruct (sy_compact_facts sy SI FOK) as (CS & CD & CR & CF & _).
unfold sync_buffer_res. rewrite CS, CF.
destruct (Z.ltb_spec (sy_storage sy - (sy_fill sy - sy_returned sy)) n) as [LT|GE]; cbn [fst snd sy_fill sy_returned sy_data sy_buf sy_storage].
- rewrite CR. repeat split; try reflexivity; lia.
- rewrite CD. destruct (sy_data sy) as [[]|] eqn:ED.
+ rewrite ?CR, ?CF, ?CD. repeat split; try reflexivity; lia.
+ destruct DN as (DN & _). specialize (DN eq_refl). pose proof SI as (R0 & _). lia.
Qed.

Lemma live_remove_cons : forall p e l, live_remove p (e :: l) = if fst e =? p then live_remove p l else e :: live_remove p l.
Proof.
intros p e l. unfold live_remove. rewrite stdpp.list_basics.list.filter_cons.
destruct (fst e =? p); reflexivity.
Qed.
Lemma perm_live_remove : forall p l l', Permutation l l' -> Permutation (live_remove p l) (live_remove p l').
Proof. intros p l l' P. induction P as [|x l l' P IH|x y l|l l' l'' P1 IH1 P2 IH2]; rewrite ?live_remove_cons.
- apply perm_nil.
- destruct (fst x =? p); [exact IH| apply perm_skip; exact IH].
- destruct (fst x =? p), (fst y =? p); try apply perm_swap; apply Permutation_refl.
- exact (perm_trans IH1 IH2).
Qed.
Lemma nodup_fst_live_remove : forall p l, List.NoDup (map fst l) -> List.NoDup (map fst (live_remove p l)).
Proof.
intros p l. induction l as [|x l IH]; intros ND; [exact ND|]. rewrite live_remove_cons.
cbn [map] in ND. apply NoDup_cons_iff in ND as (NI & ND). destruct (fst x =? p); [exact (IH ND)|].
cbn [map]. constructor; [| exact (IH ND)]. intros Hin. apply NI. apply in_map_iff in Hin as (e & E & He).
rewrite <- E. apply in_map. exact (live_remove_sub _ _ _ He).
Qed.
Lemma live_remove_app : forall p l1 l2, live_remove p (l1 ++ l2) = live_remove p l1 ++ live_remove p l2.
Proof. intros p l1 l2. induction l1 as [|x l1 IH]; [reflexivity|]. cbn [app]. rewrite !live_remove_cons, IH. destruct (fst x =? p); reflexivity. Qed.
Lemma live_remove_none : forall p l, (forall e, In e l -> fst e <> p) -> live_remove p l = l.
Proof.
intros p l H. induction l as [|x l IH]; [reflexivity|]. rewrite live_remove_cons.
replace (fst x =? p) with false by (symmetry; apply Z.eqb_neq; apply H; left; reflexivity).
f_equal. apply IH. intros e He. apply H. right. exact He.
Qed.
Lemma live_remove_last : forall p n R, (forall e, In e R -> fst e <> p) -> live_remove p (R ++ [(p, n)]) = R.
Proof.
intros p n R H. rewrite live_remove_app, (live_remove_none p R H), live_remove_cons. cbn [fst]. rewrite Z.eqb_refl. apply app_nil_r.
Qed.

Lemma own_pos : forall (Σ1 : rts RT) (m : mem) a h spill ogc opc, hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
forall p q, In (p, q) (h_own a h) -> 0 < q.
Proof.
intros Σ1 m a h spill ogc opc HR p q Hin.
destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OSR & _ & _ & _ & DEC & HP).
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
Definition a_set_sync (a : haux) (D : Z) (bs : list byte) (P : list (Z * Z)) : haux :=
HA D bs (a_Bd a) (a_L a) (a_G a) (a_shdr a) (a_body a) (a_lws a) (a_gws a) (a_Dc a) (a_S a) (a_LBD a) P.

Lemma hrep_sbuf : forall (Σ1 Σ2 : rts RT) (m m' : mem) a h spill ogc opc nbr D' bytes',
hsig RT X Σ1 a h -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 216%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat -> 0 < nbr <= 200 ->
rt_after_f RT Σ2 S1 lo m m' ->
rt_pres_fp (sync_rest_live (h_oy h) (a_Dsy a) (rt_live RT Σ1)) (rt_frames RT Σ1) S1 [(F + 8480, F + 8480 + 32)] m m' ->
sync_rep m' (F + 8480) D' (snd (sync_buffer_res (h_oy h) nbr)) bytes' ->
((sy_storage (h_oy h) - (sy_fill (h_oy h) - sy_returned (h_oy h)) >= nbr /\ D' = a_Dsy a /\ rt_live RT Σ2 = rt_live RT Σ1)
\/ (sy_storage (h_oy h) - (sy_fill (h_oy h) - sy_returned (h_oy h)) < nbr
/\ rt_live RT Σ2 = (D', nbr + (sy_fill (h_oy h) - sy_returned (h_oy h)) + 4096) :: sync_rest_live (h_oy h) (a_Dsy a) (rt_live RT Σ1))) ->
rt_frames RT Σ2 = rt_frames RT Σ1 -> rt_sp0 RT Σ2 = rt_sp0 RT Σ1 -> rt_credit RT Σ2 = rt_credit RT Σ1 -> rt_pois RT Σ2 = rt_pois RT Σ1 ->
exists P', hsig RT X Σ2 (a_set_sync a D' bytes' P') (set_ogg h (snd (sync_buffer_res (h_oy h) nbr)) (h_os h))
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ2 m' (a_set_sync a D' bytes' P') (set_ogg h (snd (sync_buffer_res (h_oy h) nbr)) (h_os h)) spill ogc opc.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV.
intros Σ1 Σ2 m m' a h spill ogc opc nbr D' bytes' HS HR SPS OGS OPS NB (ART' & MI' & ST') PR SY' CASE EF2 ES2 EC2 EP2.
pose proof (own_pos Σ1 m a h spill ogc opc HR) as OPOS.
destruct HR as (ART & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC & OSR & (stb & STB)
& RATE & (wl & LOOK) & DEC & HP).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART HS) as HSP.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
rewrite EF in PR.
pose proof HP as (SI2 & SI & STB0 & SDN & _).
pose proof SY as (_ & FOK & _).
destruct (sbuf_facts (h_oy h) nbr SI FOK ltac:(lia) SDN (proj1 STB0)) as (EFST & EFILL & ERET & EDATA & EBUF & SNOG & SGRO).
set (oy1 := snd (sync_buffer_res (h_oy h) nbr)) in *. unfold bptr in *.

assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
assert (INL' : forall p q, In (p, q) (h_own a h) -> (sy_data (h_oy h) <> None -> p <> a_Dsy a) ->
In (p, q) (sync_rest_live (h_oy h) (a_Dsy a) (rt_live RT Σ1))).
{ intros p q Hin NE. unfold sync_rest_live, bptr. destruct (sy_data (h_oy h)) eqn:ED; [| exact (INL _ Hin)].
apply live_remove_keep; [exact (INL _ Hin)|]. cbn [fst]. apply NE. discriminate. }
assert (XL : forall e, In e (x_live X) -> In e (sync_rest_live (h_oy h) (a_Dsy a) (rt_live RT Σ1))).
{ intros [q k] Hq. unfold sync_rest_live, bptr. assert (IX : In (q, k) (rt_live RT Σ1)) by (rewrite EL; apply in_or_app; right; exact Hq).
destruct (sy_data (h_oy h)) eqn:ED; [| exact IX].
apply live_remove_keep; [exact IX|]. cbn [fst]. intros ->.
assert (INS : In (a_Dsy a, sy_storage (h_oy h)) (h_own a h)) by (apply own_in_Dsy; rewrite ED; discriminate).
destruct (proj1 HSP _ _ INS) as (_ & _ & _ & _ & _ & SEP). pose proof (OPOS _ _ INS) as P1.
pose proof (proj1 (hi_live _ _ _ HX) _ _ Hq) as P2. destruct (SEP _ _ Hq); lia. }
pose proof (own_ne_Dsy a h (proj2 (proj2 HSP))) as ONE.
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK in *.
change (fs_size 8) with 16384 in *.

assert (FRT : forall A cs, rw_cells asegs m A cs -> F + 32 <= A -> A + Z.of_nat (cells_size cs) <= F + 9252 ->
(A + Z.of_nat (cells_size cs) <= F + 8480 \/ F + 8512 <= A) -> rw_cells asegs m' A cs).
{ intros A cs C H1 H2 H3. apply (htr_rw _ _ _ _ m m' PR _ _ C); [apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [lia|]. apply rng_out_nil. }
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
{ apply (htr_rw _ _ _ _ m m' PR _ _ SP); rewrite SPS; [apply acl_stack; lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (LSH' : rw_cells asegs m' sf [CB 16 HSH_P1]).
{ apply (htr_rw _ _ _ _ m m' PR _ _ LSH); cbn [cells_size csize Nat.add]; [apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [lia|]. apply rng_out_nil. }

assert (OWNTR : forall p q, In (p, q) (h_own a h) -> (sy_data (h_oy h) <> None -> p <> a_Dsy a) ->
acl_rng (sync_rest_live (h_oy h) (a_Dsy a) (rt_live RT Σ1)) [(F, 8%nat)] S1 p q /\ rng_out [(F + 8480, F + 8480 + 32)] p q).
{ intros p q Hin NE. split; [apply (acl_live _ _ _ _ _ _ _ (INL' _ _ Hin NE)); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); lia|]. apply rng_out_nil. }
assert (BOK : bits_ok (h_bits h)) by (destruct HP as (_ & _ & _ & _ & B & _); exact B).
assert (BITS' : bits_rep asegs m' (F + 8400) (a_Dc a) (h_bits h)).
{ destruct (OWNTR _ _ (own_in_Dc a h) (fun NS => proj1 (ONE NS))) as (D1 & D2).
apply (bits_rep_tr _ _ _ _ m m' PR _ _ _ BITS BOK); [| | exact D1| exact D2].
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (OSR' : h_os_rep X m' a h).
{ apply (h_os_rep_tr _ _ _ _ m m' PR X a h OSR).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- unfold HO_OS. apply rng_out_cons; [lia|]. apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
destruct (OWNTR _ _ IB (fun NS => proj1 ((proj1 (proj2 (ONE NS))) NE))) as (B1 & B2).
destruct (OWNTR _ _ IL (fun NS => proj1 (proj2 ((proj1 (proj2 (ONE NS))) NE)))) as (L1 & L2).
destruct (OWNTR _ _ IG (fun NS => proj2 (proj2 ((proj1 (proj2 (ONE NS))) NE)))) as (G1 & G2).
exact (conj B1 (conj B2 (conj L1 (conj L2 (conj G1 G2))))). }
assert (DEC' : h_dec_rep X m' a h).
{ apply (h_dec_rep_tr _ _ _ _ m m' PR X a h DEC). intros b Hb.
assert (NS0 : h_st h <> None) by (unfold h_dec_rep in DEC; destruct (h_st h); [discriminate| destruct DEC as (_ & E); rewrite E in Hb; destruct Hb]).
apply (OWNTR _ _ (own_in_blk a h NS0 b Hb)). intros NS. exact (proj2 (proj2 (ONE NS)) NS0 b Hb). }
clear OSR DEC BITS OWNTR.

assert (FPH : fp_h X a h [(F + 8480, F + 8480 + 32)]) by (apply fp_h_cons; [right; right; left; lia| apply fp_h_nil]).
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ1 m m' a h _ _ HSP PR XL FPH (AF_DRV _ _ ART') PF ERR OUTR SSP)
as (PF' & ERR' & OUTR' & SSP').

assert (PEND : 0 <= sy_fill (h_oy h) - sy_returned (h_oy h) <= 4096).
{ destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BR & _ & P1 & P2 & _). unfold h_consumed, h_pend in *.
pose proof (hi_pay _ _ _ HX) as (_ & SZ & _). unfold MAX_FUZZ_SIZE in SZ. lia. }
assert (SPOS : 0 < sy_storage oy1 <= 64512).
{ destruct (Z_lt_ge_dec (sy_storage (h_oy h) - (sy_fill (h_oy h) - sy_returned (h_oy h))) nbr) as [LT|GE]; [rewrite (SGRO LT); lia| rewrite (SNOG GE); lia]. }
assert (HP' : hpure X (set_ogg h oy1 (h_os h))).
{ unfold hpure, h_consumed, h_pend in *.
cbn [set_ogg h_oy h_os h_bits h_st h_stream_init h_packet_count h_last_granule h_nframes h_eos h_channels h_rate h_extra_headers
h_speex_serialno h_frame_size h_granule_frame_size h_bytes_remaining].
destruct HP as (_ & _ & _ & _ & REST).
pose proof (sbuf_inv2 (h_oy h) nbr SI2) as SI2'. fold oy1 in SI2'.
split; [exact SI2'|]. split; [exact (proj1 SI2')|]. split; [lia|]. split; [rewrite EDATA; split; [intros E; discriminate E| intros E; lia]|].
destruct REST as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
do 16 (split; [assumption|]). rewrite EFILL, ERET. repeat split; lia. }

assert (HR' : forall P', hrep RT OUT_rep ERR_rep IO_FP X Σ2 m' (a_set_sync a D' bytes' P') (set_ogg h oy1 (h_os h)) spill ogc opc).
{ intros P'. unfold hrep. unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK.
cbn [a_set_sync a_Dc a_Dsy a_sybytes set_ogg h_oy h_os h_bits h_st h_frame_size h_rate].
split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact PF'|]. split; [exact ERR'|]. split; [exact OUTR'|]. split; [exact SSP'|].
split; [exact SP'|]. split; [exact LSH'|]. split; [exists je; exact ENH'|]. split; [exists ows; split; [exact OUTB'| exact LOWS]|].
split; [exact FSZ'|]. split; [exact BITS'|]. split; [exact SY'|]. split; [exact OGC'|]. split; [exact OPC'|].
split; [exact OSR'|]. split; [exists stb; exact STB'|]. split; [exact RATE'|]. split; [exists wl; exact LOOK'|].
split; [exact DEC'| exact HP']. }
destruct CASE as [(GE & -> & E2) | (LT & E2)].
-
exists (a_P a). split; [| apply HR'].
assert (ED0 : sy_data (h_oy h) = Some tt).
{ destruct (sy_data (h_oy h)) as [[]|] eqn:ED; [reflexivity|]. exfalso. destruct SDN as (DN & _). specialize (DN eq_refl). lia. }
assert (EOWN : h_own (a_set_sync a (a_Dsy a) bytes' (a_P a)) (set_ogg h oy1 (h_os h)) = h_own a h).
{ unfold h_own. cbn [a_set_sync a_Dsy a_Dc a_Bd a_L a_G a_LBD set_ogg h_oy h_os h_bits h_st h_stream_init]. rewrite EDATA, ED0, (SNOG GE). reflexivity. }
unfold hsig. rewrite EOWN. cbn [a_set_sync a_P]. rewrite E2, EF2, ES2, EP2, EC2.
split; [exact EL|]. split; [exact ND|]. split; [exact PERM|]. split; [exact EF|]. split; [exact ESP|]. split; [exact EPO0| exact ECR].
-
set (n' := nbr + (sy_fill (h_oy h) - sy_returned (h_oy h)) + 4096) in *.
assert (XNE : sy_data (h_oy h) <> None -> forall e, In e (x_live X) -> fst e <> a_Dsy a).
{ intros NS [q k] Hq E. cbn [fst] in E. subst q.
assert (INS : In (a_Dsy a, sy_storage (h_oy h)) (h_own a h)) by (apply own_in_Dsy; exact NS).
destruct (proj1 HSP _ _ INS) as (_ & _ & _ & _ & _ & SEP). pose proof (OPOS _ _ INS) as P1.
pose proof (proj1 (hi_live _ _ _ HX) _ _ Hq) as P2. destruct (SEP _ _ Hq); lia. }
assert (ESR : sync_rest_live (h_oy h) (a_Dsy a) (rt_live RT Σ1) = sync_rest_live (h_oy h) (a_Dsy a) (a_P a) ++ x_live X).
{ rewrite EL. unfold sync_rest_live, bptr. destruct (sy_data (h_oy h)) eqn:ED; [| reflexivity].
rewrite live_remove_app, (live_remove_none _ (x_live X)); [reflexivity|]. apply XNE. first [discriminate | rewrite ED; discriminate]. }

assert (PCORE : Permutation (sync_rest_live (h_oy h) (a_Dsy a) (a_P a))
((match h_st h with Some _ => blocks_live (a_LBD a) | None => [] end ++ [(a_Dc a, sb_buf_size (h_bits h))])
++ (if h_stream_init h =? 0 then [] else [(a_Bd a, os_body_storage (h_os h)); (a_L a, 4 * os_lacing_storage (h_os h));
(a_G a, 8 * os_lacing_storage (h_os h))]))).
{ pose proof PERM as PERM1. pose proof (proj2 (proj2 HSP)) as NDO. unfold h_own in PERM1, NDO. unfold sync_rest_live, bptr.
destruct (sy_data (h_oy h)) eqn:ED.
- rewrite !app_assoc in PERM1, NDO.
lazymatch type of PERM1 with Permutation _ (?core ++ [_]) =>
transitivity (live_remove (a_Dsy a) (core ++ [(a_Dsy a, sy_storage (h_oy h))])); [apply perm_live_remove; exact PERM1|];
rewrite live_remove_last; [apply Permutation_refl|] end.
intros e He E. rewrite map_app in NDO. apply (nodup_app_disj _ _ (a_Dsy a) NDO); [rewrite <- E; apply in_map; exact He| left; reflexivity].
- rewrite app_nil_r, !app_assoc in PERM1. exact PERM1. }
exists ((D', n') :: sync_rest_live (h_oy h) (a_Dsy a) (a_P a)). split; [| apply HR'].
assert (EOWN : h_own (a_set_sync a D' bytes' ((D', n') :: sync_rest_live (h_oy h) (a_Dsy a) (a_P a))) (set_ogg h oy1 (h_os h))
= ((match h_st h with Some _ => blocks_live (a_LBD a) | None => [] end ++ [(a_Dc a, sb_buf_size (h_bits h))])
++ (if h_stream_init h =? 0 then [] else [(a_Bd a, os_body_storage (h_os h)); (a_L a, 4 * os_lacing_storage (h_os h));
(a_G a, 8 * os_lacing_storage (h_os h))])) ++ [(D', n')]).
{ unfold h_own. cbn [a_set_sync a_Dsy a_Dc a_Bd a_L a_G a_LBD set_ogg h_oy h_os h_bits h_st h_stream_init]. rewrite EDATA, (SGRO LT).
rewrite !app_assoc. reflexivity. }
unfold hsig. rewrite EOWN. cbn [a_set_sync a_P]. rewrite EF2, ES2, EP2, EC2.
split; [rewrite E2, ESR; reflexivity|].
assert (CORE_OWN : forall e, In e ((match h_st h with Some _ => blocks_live (a_LBD a) | None => [] end ++ [(a_Dc a, sb_buf_size (h_bits h))])
++ (if h_stream_init h =? 0 then [] else [(a_Bd a, os_body_storage (h_os h)); (a_L a, 4 * os_lacing_storage (h_os h));
(a_G a, 8 * os_lacing_storage (h_os h))])) -> In e (h_own a h)).
{ intros e He. unfold h_own. rewrite !app_assoc. apply in_or_app. left. exact He. }
split.
{ cbn [map]. constructor.
- intros Hin. apply in_map_iff in Hin as ((p & q) & Ep & Hq). cbn [fst] in Ep. subst p.
pose proof (OPOS _ _ (CORE_OWN _ (Permutation_in _ PCORE Hq))) as QP.
assert (HT : In (D', q) (sync_rest_live (h_oy h) (a_Dsy a) (rt_live RT Σ1))) by (rewrite ESR; apply in_or_app; left; exact Hq).
destruct (af_live_disj RT AF Σ2 m' D' n' D' q [] _ ART' E2 HT); unfold n' in *; lia.
- unfold sync_rest_live, bptr. destruct (sy_data (h_oy h)); [apply nodup_fst_live_remove; exact ND| exact ND]. }
split; [exact (perm_trans (perm_skip _ PCORE) (Permutation_cons_append _ _))|].
split; [exact EF|]. split; [exact ESP|]. split; [exact EPO0| exact ECR].
Qed.

Lemma h_bytes_at_app3 : forall (m : mem) A (a b d : list byte) B D,
bytes_at asegs m A a -> bytes_at asegs m B b -> bytes_at asegs m D d ->
B = A + Z.of_nat (length a) -> D = B + Z.of_nat (length b) ->
bytes_at asegs m A (a ++ b ++ d).
Proof.
intros m A a b d B D Ha Hb Hd -> ->. apply bytes_at_app. split; [exact Ha|]. apply bytes_at_app. split; [exact Hb|].
rewrite <- Z.add_assoc, <- Nat2Z.inj_add. rewrite Nat2Z.inj_add, Z.add_assoc. exact Hd.
Qed.
Lemma h_wr_at_app3 : forall (m : mem) A na nb nd, 0 <= na -> 0 <= nb -> 0 <= nd ->
wr_at asegs m A na -> wr_at asegs m (A + na) nb -> wr_at asegs m (A + na + nb) nd -> wr_at asegs m A (na + nb + nd).
Proof.
intros m A na nb nd Ha Hb Hd Wa Wb Wd. replace (na + nb + nd) with (na + (nb + nd)) by lia.
apply (proj2 (wr_at_app asegs m A na (nb + nd) Ha ltac:(lia))). split; [exact Wa|].
apply (proj2 (wr_at_app asegs m (A + na) nb nd Hb Hd)). split; assumption.
Qed.
Lemma h_u8arr_window : forall (m : mem) D bs i n,
u8arr asegs m D bs -> 0 <= i -> 0 <= n -> i + n <= Z.of_nat (length bs) ->
u8arr asegs m D (firstn (Z.to_nat i) bs)
/\ rw_cells asegs m (D + i) [CB (Z.to_nat n) (firstn (Z.to_nat n) (skipn (Z.to_nat i) bs))]
/\ u8arr asegs m (D + i + n) (skipn (Z.to_nat (i + n)) bs).
Proof.
intros m D bs i n [B W] Hi Hn Hin.
rewrite <- (firstn_skipn (Z.to_nat i) bs) in B. apply bytes_at_app in B. destruct B as [B1 B23].
rewrite firstn_length_le in B23 by lia. rewrite Z2Nat.id in B23 by lia.
rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat i) bs)) in B23. apply bytes_at_app in B23. destruct B23 as [B2 B3].
rewrite firstn_length_le in B3 by (rewrite length_skipn; lia). rewrite Z2Nat.id in B3 by lia.
rewrite skipn_skipn in B3. replace (Z.to_nat n + Z.to_nat i)%nat with (Z.to_nat (i + n)) in B3 by lia.
pose proof W as (W0 & W1 & Wi).
split; [| split].
- split; [exact B1|]. rewrite firstn_length_le by lia. rewrite Z2Nat.id by lia. split; [lia|]. split; [lia|]. intros k Hk. apply Wi. lia.
- split; [split|].
+ cbn. rewrite firstn_length_le by (rewrite length_skipn; lia). split; [reflexivity| exact I].
+ cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact B2.
+ cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. split; [lia|]. split; [lia|]. intros k Hk.
replace (D + i + k) with (D + (i + k)) by lia. apply Wi. lia.
- split; [exact B3|]. rewrite length_skipn. split; [lia|]. split; [lia|]. intros k Hk.
replace (D + i + n + k) with (D + (i + n + k)) by lia. apply Wi. lia.
Qed.
Lemma h_u8arr_unwindow : forall (m : mem) D (a : list byte) n (mid : list byte) (b : list byte) i,
u8arr asegs m D a -> Z.of_nat (length a) = i ->
rw_cells asegs m (D + i) [CB (Z.to_nat n) mid] -> 0 <= n ->
u8arr asegs m (D + i + n) b ->
u8arr asegs m D (a ++ mid ++ b) /\ Z.of_nat (length (a ++ mid ++ b)) = i + n + Z.of_nat (length b).
Proof.
intros m D a n mid b i [Ba Wa] La [[Hwf Bm] Wm] Hn [Bb Wb].
cbn in Hwf. destruct Hwf as [Lm _]. cbn [cells_bytes cbytes app] in Bm. rewrite app_nil_r in Bm.
cbn [cells_size csize Nat.add] in Wm. rewrite Nat.add_0_r, Z2Nat.id in Wm by lia.
assert (L : Z.of_nat (length (a ++ mid ++ b)) = i + n + Z.of_nat (length b)) by (rewrite !length_app; lia).
split; [| exact L]. split.
- eapply h_bytes_at_app3; [exact Ba| exact Bm| exact Bb| lia| lia].
- rewrite L. apply h_wr_at_app3; try lia; [rewrite <- La; exact Wa| exact Wm| exact Wb].
Qed.
Lemma h_firstn_firstn_le : forall {A : Type} (l : list A) n k, (n <= k)%nat -> firstn n (firstn k l) = firstn n l.
Proof. intros A l n k H. rewrite firstn_firstn. f_equal. lia. Qed.

Lemma h_sync_rep_write : forall (m m' : mem) A D (sy : sync_st bptr) (bytes : list byte) (q : bptr) (nb : Z) (src : list byte),
sync_rep m A D sy bytes -> sync_inv sy -> sy_data sy = Some q -> 0 <= nb -> sy_fill sy + nb <= sy_storage sy ->
Z.of_nat (length src) = nb ->
rw_cells asegs m' A (sync_cells D sy) ->
u8arr asegs m' D (firstn (Z.to_nat (sy_fill sy)) bytes ++ src ++ skipn (Z.to_nat (sy_fill sy + nb)) bytes) ->
sync_rep m' A D (sync_write sy (sy_fill sy) (ubytes src))
(firstn (Z.to_nat (sy_fill sy)) bytes ++ src ++ skipn (Z.to_nat (sy_fill sy + nb)) bytes).
Proof.
intros m m' A D sy bytes q nb src (OBJ & FOK & DAT & SEP) INV ED Hnb Hroom Lsrc OBJ' ARR'.
unfold sync_data in DAT. rewrite ED in DAT. destruct DAT as (Dpos & ARR & LEN & PRE & LE).
pose proof INV as (I1 & I2 & _). pose proof FOK as (Fs & Ff & Fr & _). unfold int31 in Fs, Ff, Fr. unfold zlength in I2.
assert (LB : Z.of_nat (length (firstn (Z.to_nat (sy_fill sy)) bytes ++ src ++ skipn (Z.to_nat (sy_fill sy + nb)) bytes)) = sy_storage sy).
{ rewrite !length_app, firstn_length_le, length_skipn by lia. lia. }
split; [| split; [| split]].
- unfold sync_write. cbn. exact OBJ'.
- unfold sync_fields_ok, sync_write in *. cbn. exact FOK.
- unfold sync_data, sync_write. cbn. rewrite ED. split; [exact Dpos|]. split; [exact ARR'|]. split; [exact LB|].
assert (L1 : length (ztake (sy_fill sy) (sy_buf sy) ++ ubytes src) = (Z.to_nat (sy_fill sy) + length src)%nat).
{ rewrite length_app. unfold ztake, ubytes. rewrite firstn_length_le, length_map by lia. reflexivity. }
split.
+ rewrite L1. unfold ubytes. rewrite !map_app. rewrite firstn_app. rewrite length_map, firstn_length_le by lia.
replace (Z.to_nat (sy_fill sy) + length src - Z.to_nat (sy_fill sy))%nat with (length src) by lia.
rewrite (@firstn_all2 _ _ (map bv_unsigned (firstn (Z.to_nat (sy_fill sy)) bytes))) by (rewrite length_map, firstn_length_le by lia; lia).
rewrite firstn_app, length_map, Nat.sub_diag, firstn_O, app_nil_r.
rewrite (@firstn_all2 _ _ (map bv_unsigned src)) by (rewrite length_map; lia).
f_equal. unfold ztake. rewrite <- PRE. rewrite h_firstn_firstn_le by lia. unfold ubytes. rewrite firstn_map. reflexivity.
+ rewrite L1, !length_app, firstn_length_le, length_skipn by lia. lia.
- destruct SEP as [S1|S2]; [left| right; exact S2]. lia.
Qed.

Lemma hrep_memcpy : forall (Σ1 : rts RT) (m m' : mem) a h spill ogc opc nbr,
hsig RT X Σ1 a h -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 216%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat ->
sy_data (h_oy h) = Some tt -> 0 <= nbr -> sy_fill (h_oy h) + nbr <= sy_storage (h_oy h) -> nbr <= x_size X ->
rt_after RT Σ1 S1 lo m m' ->
rt_pres_ex (rt_live RT Σ1) (rt_frames RT Σ1) S1 (a_Dsy a + sy_fill (h_oy h)) nbr m m' ->
bytes_at asegs m' (a_Dsy a + sy_fill (h_oy h)) (firstn (Z.to_nat nbr) (x_bs X)) ->
hsig RT X Σ1 (a_set_sync a (a_Dsy a) (firstn (Z.to_nat (sy_fill (h_oy h))) (a_sybytes a) ++ firstn (Z.to_nat nbr) (x_bs X)
++ skipn (Z.to_nat (sy_fill (h_oy h) + nbr)) (a_sybytes a)) (a_P a))
(set_ogg h (sync_write (h_oy h) (sy_fill (h_oy h)) (ztake nbr (x_payload X))) (h_os h))
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ1 m'
(a_set_sync a (a_Dsy a) (firstn (Z.to_nat (sy_fill (h_oy h))) (a_sybytes a) ++ firstn (Z.to_nat nbr) (x_bs X)
++ skipn (Z.to_nat (sy_fill (h_oy h) + nbr)) (a_sybytes a)) (a_P a))
(set_ogg h (sync_write (h_oy h) (sy_fill (h_oy h)) (ztake nbr (x_payload X))) (h_os h)) spill ogc opc.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV.
intros Σ1 m m' a h spill ogc opc nbr HS HR SPS OGS OPS ED NB ROOM NBS (ART' & MI' & WM' & ST') PRX SRC.
pose proof (own_pos Σ1 m a h spill ogc opc HR) as OPOS.
destruct HR as (ART & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC & OSR & (stb & STB)
& RATE & (wl & LOOK) & DEC & HP).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART HS) as HSP.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
rewrite EF in PRX.
set (d := a_Dsy a + sy_fill (h_oy h)) in *.
assert (PR : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 [(d, d + nbr)] m m').
{ apply (pres_fp_of_ex _ _ _ d nbr _ m m' PRX). intros x Hx Ho. cbn [outside] in Ho. lia. }
pose proof HP as (SI2 & SI & STB0 & SDN & _).
unfold bptr in *.

assert (INS : In (a_Dsy a, sy_storage (h_oy h)) (h_own a h)) by (apply own_in_Dsy; rewrite ED; discriminate).
assert (IVD : iv_own a h d (d + nbr)).
{ right. exists (a_Dsy a), (sy_storage (h_oy h)). split; [exact INS|]. pose proof SI as (R0 & _). unfold d. lia. }
assert (IVNE : forall p0, p0 <> a_Dsy a -> iv_own_ne a h p0 d (d + nbr)).
{ intros p0 NE. right. exists (a_Dsy a), (sy_storage (h_oy h)). split; [exact INS|]. split; [congruence|]. pose proof SI as (R0 & _). unfold d. lia. }
pose proof (own_ne_Dsy a h (proj2 (proj2 HSP)) ltac:(rewrite ED; discriminate)) as (NDc & NOS & NBLK).
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK in *.
change (fs_size 8) with 16384 in *.
assert (FRT : forall A cs, rw_cells asegs m A cs -> F + 32 <= A -> A + Z.of_nat (cells_size cs) <= F + 9252 -> rw_cells asegs m' A cs).
{ intros A cs C H1 H2. apply (htr_rw _ _ _ _ m m' PR _ _ C); [apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [apply (iv_frame_own X a h HSP _ _ _ _ IVD); lia|]. apply rng_out_nil. }
assert (ENH' : rw_cells asegs m' (F + 32) [CB 56 je]) by (apply (FRT _ _ ENH); cbn [cells_size csize Nat.add]; lia).
assert (OUTB' : rw_cells asegs m' (F + 128) (f32 ows)) by (apply (FRT _ _ OUTB); rewrite ?cells_size_f32, ?LOWS; lia).
assert (FSZ' : rw_cells asegs m' (F + 8384) [C4 (Z_to_bv 64 (h_frame_size h))]) by (apply (FRT _ _ FSZ); cbn [cells_size csize Nat.add]; lia).
assert (OGC' : rw_cells asegs m' (F + 8544) ogc) by (apply (FRT _ _ OGC); rewrite ?OGS; lia).
assert (OPC' : rw_cells asegs m' (F + 8608) opc) by (apply (FRT _ _ OPC); rewrite ?OPS; lia).
assert (STB' : rw_cells asegs m' (F + 9168) [CB 24 stb]) by (apply (FRT _ _ STB); cbn [cells_size csize Nat.add]; lia).
assert (RATE' : rw_cells asegs m' (F + 9232) [C4 (Z_to_bv 64 (h_rate h))]) by (apply (FRT _ _ RATE); cbn [cells_size csize Nat.add]; lia).
assert (LOOK' : rw_cells asegs m' (F + 9248) [C4 wl]) by (apply (FRT _ _ LOOK); cbn [cells_size csize Nat.add]; lia).
destruct SY as (SYC & FOK & DAT & SYSEP).
assert (SYC' : rw_cells asegs m' (F + 8480) (sync_cells (a_Dsy a) (h_oy h))) by (apply (FRT _ _ SYC); rewrite ?(eq_refl : Z.of_nat (cells_size (sync_cells (a_Dsy a) (h_oy h))) = 32); cbn; lia).
clear FRT ENH OUTB FSZ OGC OPC STB RATE LOOK.
assert (SP' : rw_cells asegs m' S1 spill).
{ apply (htr_rw _ _ _ _ m m' PR _ _ SP); rewrite SPS; [apply acl_stack; lia|].
apply rng_out_cons; [exact (iv_stack_own OUT_rep IO_FP X HX a h HSP _ _ S1 216 IVD ltac:(lia) ltac:(lia))|]. apply rng_out_nil. }
assert (LSH' : rw_cells asegs m' sf [CB 16 HSH_P1]).
{ apply (htr_rw _ _ _ _ m m' PR _ _ LSH); cbn [cells_size csize Nat.add]; [apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [exact (iv_fshadow_own X a h HSP _ _ sf 16 IVD ltac:(lia) ltac:(lia))|]. apply rng_out_nil. }

assert (OWNTR : forall p q, In (p, q) (h_own a h) -> p <> a_Dsy a ->
acl_rng (rt_live RT Σ1) [(F, 8%nat)] S1 p q /\ rng_out [(d, d + nbr)] p q).
{ intros p q Hin NE. split; [apply (acl_live _ _ _ _ _ _ _ (INL _ Hin)); lia|].
apply rng_out_cons; [apply (iv_own_own X a h HSP _ _ _ _ _ _ Hin); [lia| lia| apply IVNE; exact NE]|]. apply rng_out_nil. }
assert (BOK : bits_ok (h_bits h)) by (destruct HP as (_ & _ & _ & _ & B & _); exact B).
assert (BITS' : bits_rep asegs m' (F + 8400) (a_Dc a) (h_bits h)).
{ destruct (OWNTR _ _ (own_in_Dc a h) NDc) as (D1 & D2).
apply (bits_rep_tr _ _ _ _ m m' PR _ _ _ BITS BOK); [| | exact D1| exact D2].
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [apply (iv_frame_own X a h HSP _ _ _ _ IVD); lia|]. apply rng_out_nil. }
assert (OSR' : h_os_rep X m' a h).
{ apply (h_os_rep_tr _ _ _ _ m m' PR X a h OSR).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- unfold HO_OS. apply rng_out_cons; [apply (iv_frame_own X a h HSP _ _ _ _ IVD); lia|]. apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG). destruct (NOS NE) as (NB1 & NL1 & NG1).
destruct (OWNTR _ _ IB NB1) as (B1 & B2). destruct (OWNTR _ _ IL NL1) as (L1 & L2). destruct (OWNTR _ _ IG NG1) as (G1 & G2).
exact (conj B1 (conj B2 (conj L1 (conj L2 (conj G1 G2))))). }
assert (DEC' : h_dec_rep X m' a h).
{ apply (h_dec_rep_tr _ _ _ _ m m' PR X a h DEC). intros b Hb.
assert (NS0 : h_st h <> None) by (unfold h_dec_rep in DEC; destruct (h_st h); [discriminate| destruct DEC as (_ & E); rewrite E in Hb; destruct Hb]).
apply (OWNTR _ _ (own_in_blk a h NS0 b Hb)). exact (NBLK NS0 b Hb). }
clear OSR DEC BITS OWNTR.

pose proof DAT as DAT0. unfold sync_data, bptr in DAT0. rewrite ED in DAT0. destruct DAT0 as (Dpos & ARR & LEN & PRE & LE).
pose proof SI as (R0 & FB & _). pose proof FOK as (Fs & Ff & _). unfold int31 in Fs, Ff.
destruct (h_u8arr_window m (a_Dsy a) (a_sybytes a) (sy_fill (h_oy h)) nbr ARR ltac:(lia) ltac:(lia) ltac:(lia)) as (W1 & WIN & W3).
assert (W1' : u8arr asegs m' (a_Dsy a) (firstn (Z.to_nat (sy_fill (h_oy h))) (a_sybytes a))).
{ apply (htr_u8 _ _ _ _ m m' PR _ _ W1); rewrite firstn_length_le by lia; rewrite Z2Nat.id by lia.
- apply (acl_live _ _ _ _ _ _ _ (INL _ INS)); lia.
- apply rng_out_cons; [unfold d; lia|]. apply rng_out_nil. }
assert (W3' : u8arr asegs m' (a_Dsy a + sy_fill (h_oy h) + nbr) (skipn (Z.to_nat (sy_fill (h_oy h) + nbr)) (a_sybytes a))).
{ apply (htr_u8 _ _ _ _ m m' PR _ _ W3); rewrite length_skipn.
- apply (acl_live _ _ _ _ _ _ _ (INL _ INS)); lia.
- apply rng_out_cons; [unfold d; lia|]. apply rng_out_nil. }
assert (LSRC : Z.of_nat (length (firstn (Z.to_nat nbr) (x_bs X))) = nbr) by (rewrite firstn_length_le; unfold x_size in NBS; lia).
assert (WIN' : rw_cells asegs m' (a_Dsy a + sy_fill (h_oy h)) [CB (Z.to_nat nbr) (firstn (Z.to_nat nbr) (x_bs X))]).
{ destruct WIN as (_ & (W0 & W1w & Ww)). cbn [cells_size csize Nat.add] in W1w, Ww. rewrite Nat.add_0_r, Z2Nat.id in W1w by lia. rewrite Nat.add_0_r, Z2Nat.id in Ww by lia.
split; [split|].
- cbn. split; [lia| exact I].
- cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact SRC.
- cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. split; [exact W0|]. split; [exact W1w|]. intros i Hi. exact (WM' _ (Ww i Hi)). }
destruct (h_u8arr_unwindow m' (a_Dsy a) _ nbr _ _ (sy_fill (h_oy h)) W1' ltac:(rewrite firstn_length_le by lia; lia) WIN' NB W3') as (ARR' & LEN').
pose proof (h_sync_rep_write m m' (F + 8480) (a_Dsy a) (h_oy h) (a_sybytes a) tt nbr _ (conj SYC (conj FOK (conj DAT SYSEP))) SI ED NB ROOM LSRC SYC' ARR') as SY'.
assert (EUB : ubytes (firstn (Z.to_nat nbr) (x_bs X)) = ztake nbr (x_payload X)) by (unfold ubytes, ztake, x_payload; rewrite firstn_map; reflexivity).
rewrite EUB in SY'.

assert (FPH : fp_h X a h [(d, d + nbr)]) by (apply fp_h_cons; [right; right; right; exact IVD| apply fp_h_nil]).
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ1 m m' a h _ _ HSP PR
ltac:(intros e He; rewrite EL; apply in_or_app; right; exact He) FPH (AF_DRV _ _ ART') PF ERR OUTR SSP) as (PF' & ERR' & OUTR' & SSP').

assert (BOKP : bytes_ok (ztake nbr (x_payload X))).
{ apply bytes_ok_ztake. unfold bytes_ok, x_payload. apply Forall_map. apply Forall_forall. intros b _.
pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. }
destruct (sync_write_inv (h_oy h) (ztake nbr (x_payload X)) SI BOKP) as (SWI & SWL & SWF & SWR & SWS).
pose proof (sync_write_inv2 (h_oy h) (ztake nbr (x_payload X)) SI2 BOKP) as SWI2.
assert (SWD : sy_data (sync_write (h_oy h) (sy_fill (h_oy h)) (ztake nbr (x_payload X))) = sy_data (h_oy h)) by reflexivity.
set (oyw := sync_write (h_oy h) (sy_fill (h_oy h)) (ztake nbr (x_payload X))) in *.
assert (HP' : hpure X (set_ogg h oyw (h_os h))).
{ unfold hpure, h_consumed, h_pend in *.
cbn [set_ogg h_oy h_os h_bits h_st h_stream_init h_packet_count h_last_granule h_nframes h_eos h_channels h_rate h_extra_headers
h_speex_serialno h_frame_size h_granule_frame_size h_bytes_remaining].
destruct HP as (_ & _ & S3 & S4 & REST). rewrite SWS, SWD, SWF, SWR.
split; [exact SWI2|]. split; [exact SWI|]. split; [exact S3|]. split; [exact S4| exact REST]. }
assert (EOWN : h_own (a_set_sync a (a_Dsy a) (firstn (Z.to_nat (sy_fill (h_oy h))) (a_sybytes a) ++ firstn (Z.to_nat nbr) (x_bs X)
++ skipn (Z.to_nat (sy_fill (h_oy h) + nbr)) (a_sybytes a)) (a_P a)) (set_ogg h oyw (h_os h)) = h_own a h).
{ unfold h_own. cbn [a_set_sync a_Dsy a_Dc a_Bd a_L a_G a_LBD set_ogg h_oy h_os h_bits h_st h_stream_init]. rewrite SWD, SWS. reflexivity. }
split.
{ unfold hsig. rewrite EOWN. cbn [a_set_sync a_P].
split; [exact EL|]. split; [exact ND|]. split; [exact PERM|]. split; [exact EF|]. split; [exact ESP|]. split; [exact EPO0| exact ECR]. }
unfold hrep. unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK.
cbn [a_set_sync a_Dc a_Dsy a_sybytes set_ogg h_oy h_os h_bits h_st h_frame_size h_rate].
split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact PF'|]. split; [exact ERR'|]. split; [exact OUTR'|]. split; [exact SSP'|].
split; [exact SP'|]. split; [exact LSH'|]. split; [exists je; exact ENH'|]. split; [exists ows; split; [exact OUTB'| exact LOWS]|].
split; [exact FSZ'|]. split; [exact BITS'|]. split; [exact SY'|]. split; [exact OGC'|]. split; [exact OPC'|].
split; [exact OSR'|]. split; [exists stb; exact STB'|]. split; [exact RATE'|]. split; [exists wl; exact LOOK'|].
split; [exact DEC'| exact HP'].
Qed.

Lemma wrote_ok : forall (sy : sync_st unit) n, 0 <= sy_storage sy -> sy_fill sy + n <= sy_storage sy ->
ogg_sync_wrote sy n = (0, mkSync (sy_data sy) (sy_buf sy) (sy_storage sy) (sy_fill sy + n) (sy_returned sy) (sy_unsynced sy) (sy_headerbytes sy) (sy_bodybytes sy)).
Proof.
intros sy n S0 R. unfold ogg_sync_wrote, ogg_sync_check.
replace (sy_storage sy <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
replace (sy_storage sy <? sy_fill sy + n) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma hrep_wrote : forall (Σ1 : rts RT) (m m1 : mem) a h spill spill' ogc opc nbr,
hsig RT X Σ1 a h -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 216%nat -> cells_size spill' = 216%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat ->
0 <= nbr <= h_bytes_remaining h -> sy_fill (h_oy h) + nbr <= sy_storage (h_oy h) -> sy_fill (h_oy h) + nbr <= zlength (sy_buf (h_oy h)) ->
munch [(S1, S1 + 216); (F + 8480, F + 8480 + 32)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
sync_rep m1 (F + 8480) (a_Dsy a) (snd (ogg_sync_wrote (h_oy h) nbr)) (a_sybytes a) -> rw_cells asegs m1 S1 spill' ->
hsig RT X Σ1 a (set_bytes_remaining h (snd (ogg_sync_wrote (h_oy h) nbr)) (h_bytes_remaining h - nbr))
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ1 m1 a (set_bytes_remaining h (snd (ogg_sync_wrote (h_oy h) nbr)) (h_bytes_remaining h - nbr)) spill' ogc opc.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV.
intros Σ1 m m1 a h spill spill' ogc opc nbr HS HR SPS SPS' OGS OPS NB ROOM RB MU WM MI1 SY1 SP1.
pose proof (own_pos Σ1 m a h spill ogc opc HR) as OPOS.
destruct HR as (ART0 & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC & OSR & (stb & STB)
& RATE & (wl & LOOK) & DEC & HP).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART0 HS) as HSP.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
assert (PR : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 [(S1, S1 + 216); (F + 8480, F + 8480 + 32)] m m1).
{ apply (pres_fp_of_munch _ _ _ _ _ m m1 MU). intros x _ Ho. exact Ho. }

assert (ART1 : ART RT Σ1 m1).
{ apply (af_frame RT AF Σ1 m m1 S1 ART0); [rewrite ESP; pose proof (hi_lo _ _ _ HX) as (LW0 & _); unfold STACK_WIN in *; lia| | exact WM].
intros b Hb. apply MU. cbn [outside]. rewrite EF in Hb. split; [intros Hin; apply Hb; left; unfold USTACK_TOP in *; lia|].
split; [intros Hin; apply Hb; right; right; right; left; exists F, 8%nat; split; [left; reflexivity| change (fs_size 8) with 16384; lia]| exact I]. }
assert (ST1 : stk asegs m1 lo S1).
{ apply (stk_agree asegs m m1 lo S1 ST); [| exact WM]. apply (agree_of_munch _ m m1 _ MU). intros x Hx. cbn [outside]. split; [lia|]. split; [lia| exact I]. }
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK in *.
change (fs_size 8) with 16384 in *.
assert (FRT : forall A cs, rw_cells asegs m A cs -> F + 32 <= A -> A + Z.of_nat (cells_size cs) <= F + 9252 ->
(A + Z.of_nat (cells_size cs) <= F + 8480 \/ F + 8512 <= A) -> rw_cells asegs m1 A cs).
{ intros A cs C H1 H2 H3. apply (htr_rw _ _ _ _ m m1 PR _ _ C); [apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (ENH' : rw_cells asegs m1 (F + 32) [CB 56 je]) by (apply (FRT _ _ ENH); cbn [cells_size csize Nat.add]; lia).
assert (OUTB' : rw_cells asegs m1 (F + 128) (f32 ows)) by (apply (FRT _ _ OUTB); rewrite ?cells_size_f32, ?LOWS; lia).
assert (FSZ' : rw_cells asegs m1 (F + 8384) [C4 (Z_to_bv 64 (h_frame_size h))]) by (apply (FRT _ _ FSZ); cbn [cells_size csize Nat.add]; lia).
assert (OGC' : rw_cells asegs m1 (F + 8544) ogc) by (apply (FRT _ _ OGC); rewrite ?OGS; lia).
assert (OPC' : rw_cells asegs m1 (F + 8608) opc) by (apply (FRT _ _ OPC); rewrite ?OPS; lia).
assert (STB' : rw_cells asegs m1 (F + 9168) [CB 24 stb]) by (apply (FRT _ _ STB); cbn [cells_size csize Nat.add]; lia).
assert (RATE' : rw_cells asegs m1 (F + 9232) [C4 (Z_to_bv 64 (h_rate h))]) by (apply (FRT _ _ RATE); cbn [cells_size csize Nat.add]; lia).
assert (LOOK' : rw_cells asegs m1 (F + 9248) [C4 wl]) by (apply (FRT _ _ LOOK); cbn [cells_size csize Nat.add]; lia).
clear FRT ENH OUTB FSZ OGC OPC STB RATE LOOK.
assert (LSH' : rw_cells asegs m1 sf [CB 16 HSH_P1]).
{ apply (htr_rw _ _ _ _ m m1 PR _ _ LSH); cbn [cells_size csize Nat.add]; [apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
unfold SH_HI in *. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (OWNTR : forall p q, In (p, q) (h_own a h) ->
acl_rng (rt_live RT Σ1) [(F, 8%nat)] S1 p q /\ rng_out [(S1, S1 + 216); (F + 8480, F + 8480 + 32)] p q).
{ intros p q Hin. split; [apply (acl_live _ _ _ _ _ _ _ (INL _ Hin)); lia|].
apply rng_out_cons; [apply (iv_own_stack OUT_rep IO_FP X HX a h HSP _ _ _ _ _ _ Hin); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); lia|]. apply rng_out_nil. }
assert (BOK : bits_ok (h_bits h)) by (destruct HP as (_ & _ & _ & _ & B & _); exact B).
assert (BITS' : bits_rep asegs m1 (F + 8400) (a_Dc a) (h_bits h)).
{ destruct (OWNTR _ _ (own_in_Dc a h)) as (D1 & D2).
apply (bits_rep_tr _ _ _ _ m m1 PR _ _ _ BITS BOK); [| | exact D1| exact D2].
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (OSR' : h_os_rep X m1 a h).
{ apply (h_os_rep_tr _ _ _ _ m m1 PR X a h OSR).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- unfold HO_OS. apply rng_out_cons; [lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
destruct (OWNTR _ _ IB) as (B1 & B2). destruct (OWNTR _ _ IL) as (L1 & L2). destruct (OWNTR _ _ IG) as (G1 & G2).
exact (conj B1 (conj B2 (conj L1 (conj L2 (conj G1 G2))))). }
assert (DEC' : h_dec_rep X m1 a h).
{ apply (h_dec_rep_tr _ _ _ _ m m1 PR X a h DEC). intros b Hb.
assert (NS0 : h_st h <> None) by (unfold h_dec_rep in DEC; destruct (h_st h); [discriminate| destruct DEC as (_ & E); rewrite E in Hb; destruct Hb]).
apply (OWNTR _ _ (own_in_blk a h NS0 b Hb)). }
clear OSR DEC BITS OWNTR.
assert (FPH : fp_h X a h [(S1, S1 + 216); (F + 8480, F + 8480 + 32)]).
{ apply fp_h_cons; [left; lia|]. apply fp_h_cons; [right; right; left; lia|]. apply fp_h_nil. }
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ1 m m1 a h _ _ HSP PR
ltac:(intros e He; rewrite EL; apply in_or_app; right; exact He) FPH (AF_DRV _ _ ART1) PF ERR OUTR SSP) as (PF' & ERR' & OUTR' & SSP').

pose proof HP as (SI2 & SI & (S0 & _) & _).
pose proof (wrote_ok (h_oy h) nbr S0 ROOM) as EW.
pose proof (ogg_sync_wrote_inv2 (h_oy h) nbr 0 _ SI2 ltac:(lia) RB EW) as SWI2.
rewrite EW in SY1 |- *. cbn [snd] in SY1 |- *.
set (oyr := mkSync (sy_data (h_oy h)) (sy_buf (h_oy h)) (sy_storage (h_oy h)) (sy_fill (h_oy h) + nbr) (sy_returned (h_oy h))
(sy_unsynced (h_oy h)) (sy_headerbytes (h_oy h)) (sy_bodybytes (h_oy h))) in *.
assert (HP' : hpure X (set_bytes_remaining h oyr (h_bytes_remaining h - nbr))).
{ unfold hpure, h_consumed, h_pend in *.
cbn [set_bytes_remaining h_oy h_os h_bits h_st h_stream_init h_packet_count h_last_granule h_nframes h_eos h_channels h_rate h_extra_headers
h_speex_serialno h_frame_size h_granule_frame_size h_bytes_remaining].
unfold oyr. cbn [sy_data sy_storage sy_fill sy_returned].
destruct HP as (_ & _ & S3 & S4 & REST).
split; [exact SWI2|]. split; [exact (proj1 SWI2)|]. split; [exact S3|]. split; [exact S4|].
destruct REST as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
do 14 (split; [assumption|]). split; [lia|]. split; [assumption|]. repeat split; lia. }
assert (EOWN : h_own a (set_bytes_remaining h oyr (h_bytes_remaining h - nbr)) = h_own a h) by reflexivity.
split.
{ unfold hsig. rewrite EOWN.
split; [exact EL|]. split; [exact ND|]. split; [exact PERM|]. split; [exact EF|]. split; [exact ESP|]. split; [exact EPO0| exact ECR]. }
unfold hrep. unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK.
cbn [set_bytes_remaining h_oy h_os h_bits h_st h_frame_size h_rate].
split; [exact ART1|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact PF'|]. split; [exact ERR'|]. split; [exact OUTR'|]. split; [exact SSP'|].
split; [exact SP1|]. split; [exact LSH'|]. split; [exists je; exact ENH'|]. split; [exists ows; split; [exact OUTB'| exact LOWS]|].
split; [exact FSZ'|]. split; [exact BITS'|]. split; [exact SY1|]. split; [exact OGC'|]. split; [exact OPC'|].
split; [exact OSR'|]. split; [exists stb; exact STB'|]. split; [exact RATE'|]. split; [exists wl; exact LOOK'|].
split; [exact DEC'| exact HP'].
Qed.

Lemma hrep_spill : forall (Σ1 : rts RT) (m m1 : mem) a h spill spill' ogc opc,
hsig RT X Σ1 a h -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 216%nat -> cells_size spill' = 216%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat ->
munch [(S1, S1 + 216)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> rw_cells asegs m1 S1 spill' ->
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m1 a h spill' ogc opc.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV.
intros Σ1 m m1 a h spill spill' ogc opc HS HR SPS SPS' OGS OPS MU WM MI1 SP1.
destruct HR as (ART0 & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC & OSR & (stb & STB)
& RATE & (wl & LOOK) & DEC & HP).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART0 HS) as HSP.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
assert (PR : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 [(S1, S1 + 216)] m m1).
{ apply (pres_fp_of_munch _ _ _ _ _ m m1 MU). intros x _ Ho. exact Ho. }
assert (ART1 : ART RT Σ1 m1).
{ apply (af_frame RT AF Σ1 m m1 S1 ART0); [rewrite ESP; pose proof (hi_lo _ _ _ HX) as (LW0 & _); unfold STACK_WIN in *; lia| | exact WM].
intros b Hb. apply MU. cbn [outside]. rewrite EF in Hb. split; [intros Hin; apply Hb; left; unfold USTACK_TOP in *; lia| exact I]. }
assert (ST1 : stk asegs m1 lo S1).
{ apply (stk_agree asegs m m1 lo S1 ST); [| exact WM]. apply (agree_of_munch _ m m1 _ MU). intros x Hx. cbn [outside]. split; [lia| exact I]. }
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK in *.
change (fs_size 8) with 16384 in *.
assert (FRT : forall A cs, rw_cells asegs m A cs -> F + 32 <= A -> A + Z.of_nat (cells_size cs) <= F + 9252 -> rw_cells asegs m1 A cs).
{ intros A cs C H1 H2. apply (htr_rw _ _ _ _ m m1 PR _ _ C); [apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (ENH' : rw_cells asegs m1 (F + 32) [CB 56 je]) by (apply (FRT _ _ ENH); cbn [cells_size csize Nat.add]; lia).
assert (OUTB' : rw_cells asegs m1 (F + 128) (f32 ows)) by (apply (FRT _ _ OUTB); rewrite ?cells_size_f32, ?LOWS; lia).
assert (FSZ' : rw_cells asegs m1 (F + 8384) [C4 (Z_to_bv 64 (h_frame_size h))]) by (apply (FRT _ _ FSZ); cbn [cells_size csize Nat.add]; lia).
assert (OGC' : rw_cells asegs m1 (F + 8544) ogc) by (apply (FRT _ _ OGC); rewrite ?OGS; lia).
assert (OPC' : rw_cells asegs m1 (F + 8608) opc) by (apply (FRT _ _ OPC); rewrite ?OPS; lia).
assert (STB' : rw_cells asegs m1 (F + 9168) [CB 24 stb]) by (apply (FRT _ _ STB); cbn [cells_size csize Nat.add]; lia).
assert (RATE' : rw_cells asegs m1 (F + 9232) [C4 (Z_to_bv 64 (h_rate h))]) by (apply (FRT _ _ RATE); cbn [cells_size csize Nat.add]; lia).
assert (LOOK' : rw_cells asegs m1 (F + 9248) [C4 wl]) by (apply (FRT _ _ LOOK); cbn [cells_size csize Nat.add]; lia).
clear FRT ENH OUTB FSZ OGC OPC STB RATE LOOK.
assert (LSH' : rw_cells asegs m1 sf [CB 16 HSH_P1]).
{ apply (htr_rw _ _ _ _ m m1 PR _ _ LSH); cbn [cells_size csize Nat.add]; [apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
unfold SH_HI in *. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (OWNTR : forall p q, In (p, q) (h_own a h) -> acl_rng (rt_live RT Σ1) [(F, 8%nat)] S1 p q /\ rng_out [(S1, S1 + 216)] p q).
{ intros p q Hin. split; [apply (acl_live _ _ _ _ _ _ _ (INL _ Hin)); lia|].
apply rng_out_cons; [apply (iv_own_stack OUT_rep IO_FP X HX a h HSP _ _ _ _ _ _ Hin); lia|]. apply rng_out_nil. }
assert (BOK : bits_ok (h_bits h)) by (destruct HP as (_ & _ & _ & _ & B & _); exact B).
assert (BITS' : bits_rep asegs m1 (F + 8400) (a_Dc a) (h_bits h)).
{ destruct (OWNTR _ _ (own_in_Dc a h)) as (D1 & D2).
apply (bits_rep_tr _ _ _ _ m m1 PR _ _ _ BITS BOK); [| | exact D1| exact D2].
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (SY' : sync_rep m1 (F + 8480) (a_Dsy a) (h_oy h) (a_sybytes a)).
{ apply (sync_rep_tr _ _ _ _ m m1 PR _ _ _ _ SY).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia|]. apply rng_out_nil.
- intros NS. exact (OWNTR _ _ (own_in_Dsy a h NS)). }
assert (OSR' : h_os_rep X m1 a h).
{ apply (h_os_rep_tr _ _ _ _ m m1 PR X a h OSR).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- unfold HO_OS. apply rng_out_cons; [lia|]. apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
destruct (OWNTR _ _ IB) as (B1 & B2). destruct (OWNTR _ _ IL) as (L1 & L2). destruct (OWNTR _ _ IG) as (G1 & G2).
exact (conj B1 (conj B2 (conj L1 (conj L2 (conj G1 G2))))). }
assert (DEC' : h_dec_rep X m1 a h).
{ apply (h_dec_rep_tr _ _ _ _ m m1 PR X a h DEC). intros b Hb.
assert (NS0 : h_st h <> None) by (unfold h_dec_rep in DEC; destruct (h_st h); [discriminate| destruct DEC as (_ & E); rewrite E in Hb; destruct Hb]).
apply (OWNTR _ _ (own_in_blk a h NS0 b Hb)). }
clear OSR DEC BITS OWNTR SY.
assert (FPH : fp_h X a h [(S1, S1 + 216)]) by (apply fp_h_cons; [left; lia| apply fp_h_nil]).
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ1 m m1 a h _ _ HSP PR
ltac:(intros e He; rewrite EL; apply in_or_app; right; exact He) FPH (AF_DRV _ _ ART1) PF ERR OUTR SSP) as (PF' & ERR' & OUTR' & SSP').
unfold hrep. unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK.
split; [exact ART1|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact PF'|]. split; [exact ERR'|]. split; [exact OUTR'|]. split; [exact SSP'|].
split; [exact SP1|]. split; [exact LSH'|]. split; [exists je; exact ENH'|]. split; [exists ows; split; [exact OUTB'| exact LOWS]|].
split; [exact FSZ'|]. split; [exact BITS'|]. split; [exact SY'|]. split; [exact OGC'|]. split; [exact OPC'|].
split; [exact OSR'|]. split; [exists stb; exact STB'|]. split; [exact RATE'|]. split; [exists wl; exact LOOK'|].
split; [exact DEC'| exact HP].
Qed.

Lemma h_live_len : forall (Σ1 : rts RT) a h, hsig RT X Σ1 a h ->
Z.of_nat (length (rt_live RT Σ1)) = Z.of_nat (length (h_own a h)) + Z.of_nat (length (x_live X)).
Proof. intros Σ1 a h (EL & _ & PERM & _). rewrite EL, length_app, (Permutation_length PERM). lia. Qed.
Lemma h_own_len : forall (Σ1 : rts RT) (m : mem) a h spill ogc opc, hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
(length (h_own a h) <= 24)%nat.
Proof.
intros Σ1 m a h spill ogc opc HR. destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DEC & _).
unfold h_own. rewrite !length_app. unfold h_dec_rep in DEC.
destruct (h_st h) as [d|]; [destruct DEC as (_ & _ & _ & _ & _ & _ & _ & _ & LL)|];
destruct (h_stream_init h =? 0); destruct (sy_data (h_oy h)); cbn [length]; unfold blocks_live; rewrite ?length_map; lia.
Qed.

End Steps.
