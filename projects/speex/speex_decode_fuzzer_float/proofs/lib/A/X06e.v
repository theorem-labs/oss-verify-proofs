(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j5 X0ec X001 X00b X04b X07z X05o X05p X05s X08k X05u
X081 X05l X05m X09f X06d X069 X06f X06g.
From stdpp Require list_basics.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19o X14x X0r0 X0ra X0v9 X0yr X0wl X0zb X0wn X0ys X0x2 X0x7 X0x8.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x7 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x8.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition live_remove_list (ps : list Z) (l : list (Z * Z)) : list (Z * Z) := fold_right live_remove l ps.

Lemma live_remove_list_app : forall ps qs l, live_remove_list (ps ++ qs) l = live_remove_list ps (live_remove_list qs l).
Proof. intros. unfold live_remove_list. apply fold_right_app. Qed.

Lemma live_remove_in : forall p l e, In e (live_remove p l) <-> In e l /\ fst e <> p.
Proof.
intros p l e. split.
- intros H. split; [exact (live_remove_sub l p e H)|]. unfold live_remove in H.
apply stdpp.base.list_elem_of_In in H. apply stdpp.list_basics.list.list_elem_of_filter in H. destruct H as [H _].
intros E. rewrite E, Z.eqb_refl in H. exact H.
- intros [H1 H2]. exact (live_remove_keep l p e H1 H2).
Qed.

Lemma live_remove_comm : forall p q l, live_remove p (live_remove q l) = live_remove q (live_remove p l).
Proof.
intros p q l. unfold live_remove.
rewrite !stdpp.list_basics.list.list_filter_filter. apply stdpp.list_basics.list.list_filter_iff. intros x. tauto.
Qed.

Lemma live_remove_list_keep : forall ps l e, In e l -> ~ In (fst e) ps -> In e (live_remove_list ps l).
Proof.
induction ps as [|p ps IH]; intros l e H N; [exact H|]. cbn. apply live_remove_keep; [apply IH; [exact H| intros X; apply N; right; exact X]|].
intros E. apply N. left. symmetry. exact E.
Qed.
Lemma live_remove_list_sub : forall ps l e, In e (live_remove_list ps l) -> In e l.
Proof. induction ps as [|p ps IH]; intros l e H; [exact H|]. cbn in H. apply IH. exact (live_remove_sub _ _ _ H). Qed.

Lemma live_remove_list_snoc : forall ps p l, live_remove_list (ps ++ [p]) l = live_remove p (live_remove_list ps l).
Proof.
unfold live_remove_list. induction ps as [|q ps IH]; intros p l; [reflexivity|]. cbn [app fold_right]. rewrite IH. apply live_remove_comm.
Qed.

Fixpoint destroy_stack (d : dec_state bptr) : Z := match d with DecNB _ => 16 | DecSB _ low => 32 + destroy_stack low end.

Section DestroyCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis FRE : free_contract RT.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.

Definition destroy_cps_at (d : dec_state bptr) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (OUT STEREO S lo : Z) (LBD : list block),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 S -> tp = Z_to_bv 64 0x638c98 ->
DREP OUT STEREO m S d LBD -> List.NoDup (map blk_id LBD) ->
(forall b, In b LBD -> In (blk_addr b, blk_size b) (rt_live RT Σ)) ->
ART RT Σ m -> mem_inv bsegs m ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + destroy_stack d <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
unwind_ch m ra s0 sp ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_speex_decoder_destroy m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists v m',
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) [] m m') c
/\ rt_live RT Σ' = live_remove_list (map blk_addr LBD) (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem destroy_cps_nb : forall st, destroy_cps_at (DecNB st).
Proof using AF FRE AF_LIB.
intros st Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m OUT STEREO S lo LBD
FDO MST E0 ETP REP ND LIVE ART0 MI0 ST0 LOW LOR SPT SPA UNW.
cbn [decst_rep] in REP. destruct REP as [-> NB]. cbn [destroy_stack] in LOR.
pose proof (LIVE _ ltac:(left; reflexivity)) as INL. unfold blk_addr, blk_size in INL. cbn [fst snd] in INL.
exact (nb_decoder_destroy_ok RT AF FRE AF_LIB Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S OUT STEREO lo st
FDO MST E0 ETP NB INL ART0 MI0 ST0 LOW LOR SPT SPA UNW).
Qed.

Lemma live_remove_list_perm : forall ps qs l, Permutation ps qs -> live_remove_list ps l = live_remove_list qs l.
Proof.
intros ps qs l H. unfold live_remove_list. induction H as [|x ps qs H IH|x y ps|ps qs rs H1 IH1 H2 IH2]; [reflexivity| cbn [fold_right]; rewrite IH; reflexivity| cbn [fold_right]; apply live_remove_comm| congruence].
Qed.

Lemma uw_chain_pres : forall live frames sp (m m' : mem) ras f fp,
rt_pres live frames sp m m' -> sp <= f -> uw_chain USTACK_TOP m f fp ras -> uw_chain USTACK_TOP m' f fp ras.
Proof.
intros live frames sp m m'. induction ras as [|r ras IHr]; intros f fp PR Hf H; cbn [uw_chain] in *; [exact H|].
destruct H as (H1 & H2 & H3 & fp' & H4 & H5 & H6).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. exists fp'. split; [exact H4|]. split.
- apply (rw_cells_agree_nw bsegs m m' _ _ H5). apply (agree_of_pres live frames sp m m' _ PR). intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. lia.
- apply (IHr fp fp' PR); [lia| exact H6].
Qed.
Lemma unwind_ch_pres : forall live frames sp' (m m' : mem) ra s0 sp,
rt_pres live frames sp' m m' -> sp' <= bv_unsigned sp -> unwind_ch m ra s0 sp -> unwind_ch m' ra s0 sp.
Proof. intros live frames sp' m m' ra s0 sp PR Hs (ras & H1 & H2). exists ras. split; [exact H1| exact (uw_chain_pres live frames sp' m m' ras _ _ PR Hs H2)]. Qed.
Lemma unwind_ch_pres_fp : forall live frames sp' (m m' : mem) ra s0 sp,
rt_pres_fp live frames sp' [] m m' -> sp' <= bv_unsigned sp -> unwind_ch m ra s0 sp -> unwind_ch m' ra s0 sp.
Proof. intros live frames sp' m m' ra s0 sp PR. apply (unwind_ch_pres live frames). intros a Ha. exact (PR a Ha I). Qed.

Definition sbtl2 (s : sbd_state bptr) (a : sb_addrs) (OUT : Z) (j : sb_junk) : list cell :=
[C8 (Z_to_bv 64 (sb_isave_ptr OUT s)); C4 (sj_last_ener j); C4 (sj_seed j); C4 (Z_to_bv 64 (sbd_encode_submode s)); CB 4 (sj_pad1 j);
C8 (Z_to_bv 64 (sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR (sbd_mode s))); C4 (Z_to_bv 64 (sbd_submodeID s)); CB 4 (sj_pad2 j)].
Lemma sb_cells_ptrs : forall s a OUT j,
SBCELLS s a OUT j = sbptrs (sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode (sbd_mode s)) (a_low a)
(Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s)) (Z_to_bv 64 (sbd_nbSubframes s))
(Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s)) (Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 (sbd_lpc_enh_enabled s))
(Z_to_bv 64 0) (a_g0 a) (a_g1 a) (a_exc a) (a_oq a) (a_iq a) (a_msp a) (a_pg a) (a_er a) ++ sbtl2 s a OUT j.
Proof. reflexivity. Qed.

Theorem destroy_cps_sb : forall s low, destroy_cps_at low -> destroy_cps_at (DecSB s low).
Proof using AF FRE AF_LIB.
intros s low IH Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m OUT STEREO S lo LBD
FDO MST -> -> REP ND LIVE ART0 MI0 ST0 LOW LOR SPT SPA UNW.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
cbn [destroy_stack] in LOR.
assert (DSP : 0 <= destroy_stack low) by (clear; induction low; cbn [destroy_stack]; lia).
cbn [decst_rep] in REP. destruct REP as (a & j & LBL & ELBD & S8 & SPOS & INV & JOK & X & _ & OUTL & RLOW).
pose proof INV as (IMODE & _). subst LBD.

assert (INS : In (S, 160) (rt_live RT Σ)) by (exact (LIVE (sbd_blk s, S, SBSTATE_SIZEOF) ltac:(left; reflexivity))).
assert (IN_g0 : In (a_g0 a, 256) (rt_live RT Σ)) by (refine (LIVE (_, a_g0 a, 256) _); cbn [sb_blocks app In]; tauto).
assert (IN_g1 : In (a_g1 a, 256) (rt_live RT Σ)) by (refine (LIVE (_, a_g1 a, 256) _); cbn [sb_blocks app In]; tauto).
assert (IN_ex : In (a_exc a, (4 * sbd_subframeSize s)) (rt_live RT Σ)) by (refine (LIVE (_, a_exc a, (4 * sbd_subframeSize s)) _); cbn [sb_blocks app In]; tauto).
assert (IN_oq : In (a_oq a, 32) (rt_live RT Σ)) by (refine (LIVE (_, a_oq a, 32) _); cbn [sb_blocks app In]; tauto).
assert (IN_iq : In (a_iq a, 32) (rt_live RT Σ)) by (refine (LIVE (_, a_iq a, 32) _); cbn [sb_blocks app In]; tauto).
assert (IN_pg : In (a_pg a, 16) (rt_live RT Σ)) by (refine (LIVE (_, a_pg a, 16) _); cbn [sb_blocks app In]; tauto).
assert (IN_er : In (a_er a, 16) (rt_live RT Σ)) by (refine (LIVE (_, a_er a, 16) _); cbn [sb_blocks app In]; tauto).
assert (IN_msp : In (a_msp a, 64) (rt_live RT Σ)) by (refine (LIVE (_, a_msp a, 64) _); cbn [sb_blocks app In]; tauto).
assert (LIVEL : forall b, In b LBL -> In (blk_addr b, blk_size b) (rt_live RT Σ)) by (intros b Hb; apply LIVE; apply in_app_iff; right; exact Hb).
cbn [sb_blocks app map blk_id blk_addr fst snd] in ND.
apply List.NoDup_cons_iff in ND. destruct ND as [N_S ND].
apply List.NoDup_cons_iff in ND. destruct ND as [N_g0 ND].
apply List.NoDup_cons_iff in ND. destruct ND as [N_g1 ND].
apply List.NoDup_cons_iff in ND. destruct ND as [N_ex ND].
apply List.NoDup_cons_iff in ND. destruct ND as [N_oq ND].
apply List.NoDup_cons_iff in ND. destruct ND as [N_iq ND].
apply List.NoDup_cons_iff in ND. destruct ND as [N_pg ND].
apply List.NoDup_cons_iff in ND. destruct ND as [N_er ND].
apply List.NoDup_cons_iff in ND. destruct ND as [N_msp ND].
rename ND into NDL. fold (map blk_id LBL) in *.
clear LIVE.
destruct (live_below_lo RT AF Σ m S 160 lo ART0 INS LOW) as (_ & BS1 & LOS).
destruct (af_acc_live RT AF Σ m S 160 ART0 INS) as (_ & ACS).

pose proof (AF_LIB Σ m ART0) as LC0.
rewrite sb_cells_ptrs in X.
set (MP := sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode (sbd_mode s)) in *.
assert (MPF : exists c0 c1 c2 c3 c4 c5 c6 c7 c8 c10 c11 c12, ro_cells bsegs m MP (sbd_desc_cells c0 c1 c2 c3 c4 c5 c6 c7 c8 c10 c11 c12)
/\ aobj bsegs m MP 96 /\ MP mod 8 = 0 /\ 0x10000 <= MP /\ MP + 104 <= 0x65b000).
{ subst MP. destruct IMODE as [E|E]; rewrite E; cbn [sb_mode_ptr].
- do 12 eexists. split; [exact (lib_const m A_speex_wb_mode LC_speex_wb_mode LC0 ltac:(lc_in))|].
split; [apply (aobj_lit RT AF Σ m A_speex_wb_mode 96 ART0); [unfold ACC_LITS, A_speex_wb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_speex_wb_mode; lia | unfold A_speex_wb_mode, APP_TOP; lia]|].
unfold A_speex_wb_mode. repeat split; lia.
- do 12 eexists. split; [exact (lib_const m A_speex_uwb_mode LC_speex_uwb_mode LC0 ltac:(lc_in))|].
split; [apply (aobj_lit RT AF Σ m A_speex_uwb_mode 96 ART0); [unfold ACC_LITS, A_speex_uwb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_speex_uwb_mode; lia | unfold A_speex_uwb_mode, APP_TOP; lia]|].
unfold A_speex_uwb_mode. repeat split; lia. }
destruct MPF as (c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & c8 & c10 & c11 & c12 & ND0 & OBM & MP8 & MPLO & MPHI). clearbody MP.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
assert (OBS : aobj bsegs m S 160) by (split; [lia|]; split; [unfold APP_TOP, STACK_WIN, USTACK_TOP, RT_STACK in *; lia| exact ACS]).
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
assert (LO32 : lo <= usp + -32) by (clear - LOR DSP; unfold RT_STACK in LOR; lia).
assert (SBF : 0 < S /\ S + 160 < 2^63) by (split; [lia| unfold USTACK_TOP, RT_STACK in *; lia]).
apply (proj1 (rw_cells_app bsegs m S _ _)) in X. destruct X as [XP XT]. clear XT.
cps_norm.

cps_seg (sbd_w1 usp lo S MP (a_low a)).
destruct POST as (m1 & j0 & xt1 & xa1 & xa2 & xa3 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
assert (RLOW1 : DREP OUTL STEREO m1 (a_low a) low LBL).
{ eapply decst_rep_agree; [exact RLOW|]. apply (agree_blocks_of_munch bsegs _ m m1 LBL MU1 WM1). intros b x Hb Hx. cbn [outside]. split; [| exact I].
destruct (live_below_lo RT AF Σ m _ _ lo ART0 (LIVEL b Hb) LOW) as (_ & B1 & _). clear - B1 Hx LO32. lia. }
assert (UNW1 : unwind_ch m1 ra s0 sp).
{ apply (unwind_ch_transport [(usp + -32, usp)] m m1 ra s0 sp); [| exact MU1| exact WM1| exact UNW].
intros x Hx. cbn [disjoint_from]. fold usp in Hx. split; [lia| exact I]. }
clear RLOW UNW. unfold sbd_frame in FR1.
cps_seg_post.
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; ulc).
assert (UNWL : unwind_ch m1 (Z_to_bv 64 RA_sbd_low) (Z_to_bv 64 S) (Z_to_bv 64 (usp + -32))).
{ apply (unwind_ch_nf m1 _ _ _ lo); [rewrite unsigned_lit by (unfold RA_sbd_low; lia); unfold ALLOC_RAS, RA_sbd_low; cbn [In]; repeat (first [left; reflexivity | right])
| left; rewrite unsigned_lit by lia; lia | rewrite EU; lia]. }
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes bsegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end;
[ eapply (IH Σ PMc) with (OUT := OUTL) (STEREO := STEREO) (LBD := LBL) (lo := lo); cps_auto | ].
{ rewrite EU. eassumption. }
intros cca (Σa & Hca & LVa & FRSa & SPa & CRa & POa).
destruct (ASTA_unpack RT Σa PMc _ cca Hca) as (msa & POSTa & Hca'). clear Hca. cbv beta in POSTa.
destruct POSTa as (va & ma & RSa & (ARTa & MIa & STa) & PRESa).
destruct RSa as (zt0 & zt1 & zt2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & Fa & fca & -> & -> & ->).
rewrite EU in *.

assert (KEEP : forall e, In e (rt_live RT Σ) -> ~ In (fst e) (map blk_id LBL) -> In e (rt_live RT Σa))
by (intros e He Hn; rewrite LVa; exact (live_remove_list_keep _ _ e He Hn)).
assert (INS_a : In (S, 160) (rt_live RT Σa)) by (apply KEEP; [exact INS| cbn [fst]; clear - N_S; intros X; apply N_S; do 8 right; exact X]).
assert (IN_g0_a : In (a_g0 a, 256) (rt_live RT Σa)) by (apply KEEP; [exact IN_g0| cbn [fst]; clear - N_g0; intros X; apply N_g0; do 7 right; exact X]).
assert (IN_g1_a : In (a_g1 a, 256) (rt_live RT Σa)) by (apply KEEP; [exact IN_g1| cbn [fst]; clear - N_g1; intros X; apply N_g1; do 6 right; exact X]).
assert (IN_ex_a : In (a_exc a, (4 * sbd_subframeSize s)) (rt_live RT Σa)) by (apply KEEP; [exact IN_ex| cbn [fst]; clear - N_ex; intros X; apply N_ex; do 5 right; exact X]).
assert (IN_oq_a : In (a_oq a, 32) (rt_live RT Σa)) by (apply KEEP; [exact IN_oq| cbn [fst]; clear - N_oq; intros X; apply N_oq; do 4 right; exact X]).
assert (IN_iq_a : In (a_iq a, 32) (rt_live RT Σa)) by (apply KEEP; [exact IN_iq| cbn [fst]; clear - N_iq; intros X; apply N_iq; do 3 right; exact X]).
assert (IN_pg_a : In (a_pg a, 16) (rt_live RT Σa)) by (apply KEEP; [exact IN_pg| cbn [fst]; clear - N_pg; intros X; apply N_pg; do 2 right; exact X]).
assert (IN_er_a : In (a_er a, 16) (rt_live RT Σa)) by (apply KEEP; [exact IN_er| cbn [fst]; clear - N_er; intros X; apply N_er; do 1 right; exact X]).
assert (IN_msp_a : In (a_msp a, 64) (rt_live RT Σa)) by (apply KEEP; [exact IN_msp| cbn [fst]; clear - N_msp; intros X; apply N_msp; exact X]).
clear KEEP.
assert (SUBa : forall e, In e (rt_live RT Σa) -> In e (rt_live RT Σ)) by (intros e He; rewrite LVa in He; exact (live_remove_list_sub _ _ e He)).
assert (UNWa : unwind_ch ma ra s0 sp) by (apply (unwind_ch_pres_fp _ _ (usp + -32) m1 ma ra s0 sp PRESa); [fold usp; lia| exact UNW1]).

assert (XP_a : rw_cells bsegs ma S (sbptrs MP (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s)) (Z_to_bv 64 (sbd_nbSubframes s))
(Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s)) (Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 (sbd_lpc_enh_enabled s))
(Z_to_bv 64 0) (a_g0 a) (a_g1 a) (a_exc a) (a_oq a) (a_iq a) (a_msp a) (a_pg a) (a_er a))).
{ apply (rw_cells_agree_nw bsegs m1 ma S _ XP). apply (agree_of_pres_fp _ _ _ _ m1 ma _ PRESa). intros x Hx. split; [| exact I].
right; right; left. exists S, 160. split; [exact INS_a|]. clear - Hx. cbn in Hx. lia. }
assert (FR_a : rw_cells bsegs ma (usp + -32) [CB 8 j0; C8 s1; C8 s0; C8 ra]).
{ apply (rw_cells_agree_nw bsegs m1 ma _ _ FR1). apply (agree_of_pres_fp _ _ _ _ m1 ma _ PRESa). intros x Hx. split; [| exact I].
left. clear - Hx SPT. cbn in Hx. unfold USTACK_TOP in *. lia. }
clear XP FR1 UNW1 UNWL.
assert (LOWa : rt_sp0 RT Σa - 8388608 <= lo) by (rewrite SPa; exact LOW).
assert (EF_a : rt_frames RT Σa = rt_frames RT Σ) by exact FRSa.

destruct (af_acc_live RT AF Σa ma S 160 ltac:(eassumption) INS_a) as (_ & ACS_f0).
assert (OBS_f0 : aobj bsegs ma S 160) by (split; [lia|]; split; [ulc| exact ACS_f0]).
cps_seg (sbd_free_seg 0%nat usp S MP (a_low a)).
destruct POST as (xb0 & ->). cbn [sbd_ra sbd_arg] in *.
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes bsegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end; [ eapply FRE with (p := a_g0 a) (n := 256); cps_auto | ].
{ cps_callok. }
{ apply (unwind_ch_nf ma _ _ _ lo); [rewrite unsigned_lit by lia; unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right]) | left; rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by ulc; lia]. }
intros cf0 (Σf0 & vf0 & Hcf0 & LV_f0 & FRS_f0 & SP_f0 & CR_f0 & PO_f0).
assert (INS_f0 : In (S, 160) (rt_live RT Σf0)) by (rewrite LV_f0; apply live_remove_keep; [exact INS_a| cbn [fst]; clear - N_S; intros E; apply N_S; rewrite E; left; reflexivity]).
assert (IN_g1_f0 : In (a_g1 a, 256) (rt_live RT Σf0)) by (rewrite LV_f0; apply live_remove_keep; [exact IN_g1_a| cbn [fst]; clear - N_g0; intros E; apply N_g0; rewrite <- E; left; reflexivity]).
assert (IN_ex_f0 : In (a_exc a, (4 * sbd_subframeSize s)) (rt_live RT Σf0)) by (rewrite LV_f0; apply live_remove_keep; [exact IN_ex_a| cbn [fst]; clear - N_g0; intros E; apply N_g0; rewrite <- E; do 1 right; left; reflexivity]).
assert (IN_oq_f0 : In (a_oq a, 32) (rt_live RT Σf0)) by (rewrite LV_f0; apply live_remove_keep; [exact IN_oq_a| cbn [fst]; clear - N_g0; intros E; apply N_g0; rewrite <- E; do 2 right; left; reflexivity]).
assert (IN_iq_f0 : In (a_iq a, 32) (rt_live RT Σf0)) by (rewrite LV_f0; apply live_remove_keep; [exact IN_iq_a| cbn [fst]; clear - N_g0; intros E; apply N_g0; rewrite <- E; do 3 right; left; reflexivity]).
assert (IN_pg_f0 : In (a_pg a, 16) (rt_live RT Σf0)) by (rewrite LV_f0; apply live_remove_keep; [exact IN_pg_a| cbn [fst]; clear - N_g0; intros E; apply N_g0; rewrite <- E; do 4 right; left; reflexivity]).
assert (IN_er_f0 : In (a_er a, 16) (rt_live RT Σf0)) by (rewrite LV_f0; apply live_remove_keep; [exact IN_er_a| cbn [fst]; clear - N_g0; intros E; apply N_g0; rewrite <- E; do 5 right; left; reflexivity]).
assert (IN_msp_f0 : In (a_msp a, 64) (rt_live RT Σf0)) by (rewrite LV_f0; apply live_remove_keep; [exact IN_msp_a| cbn [fst]; clear - N_g0; intros E; apply N_g0; rewrite <- E; do 6 right; left; reflexivity]).
assert (SUB_f0 : forall e, In e (rt_live RT Σf0) -> In e (rt_live RT Σa)) by (intros e He; rewrite LV_f0 in He; exact (live_remove_sub _ _ e He)).
assert (LOW_f0 : rt_sp0 RT Σf0 - 8388608 <= lo) by (rewrite SP_f0; assumption).
assert (EF_f0 : rt_frames RT Σf0 = rt_frames RT Σ) by (rewrite FRS_f0; exact EF_a).
cps_unpack Hcf0 as (mf0 & RS_f0 & (ART_f0 & MI_f0 & ST_f0) & PRES_f0).
assert (UNW_f0 : unwind_ch mf0 ra s0 sp) by (apply (unwind_ch_pres _ _ (usp + -32) ma mf0 ra s0 sp PRES_f0); [fold usp; lia| assumption]).
assert (XP_f0 : rw_cells bsegs mf0 S (sbptrs MP (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s)) (Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s)) (Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 (sbd_lpc_enh_enabled s)) (Z_to_bv 64 0) (a_g0 a) (a_g1 a) (a_exc a) (a_oq a) (a_iq a) (a_msp a) (a_pg a) (a_er a))).
{ first [exact XP_a| apply (rw_cells_agree_nw bsegs ma mf0 S _ XP_a); apply (agree_of_pres _ _ _ ma mf0 _ PRES_f0); intros x Hx; right; right; left; exists S, 160; split; [exact INS_f0|]; clear - Hx; cbn in Hx; lia]. }
assert (FR_f0 : rw_cells bsegs mf0 (usp + -32) [CB 8 j0; C8 s1; C8 s0; C8 ra]).
{ first [exact FR_a| apply (rw_cells_agree_nw bsegs ma mf0 _ _ FR_a); apply (agree_of_pres _ _ _ ma mf0 _ PRES_f0); intros x Hx; left; clear - Hx SPT; cbn in Hx; unfold USTACK_TOP in *; lia]. }
clear XP_a FR_a.

destruct (af_acc_live RT AF Σf0 mf0 S 160 ltac:(eassumption) INS_f0) as (_ & ACS_f1).
assert (OBS_f1 : aobj bsegs mf0 S 160) by (split; [lia|]; split; [ulc| exact ACS_f1]).
cps_seg (sbd_free_seg 1%nat usp S MP (a_low a)).
destruct POST as (xb1 & ->). cbn [sbd_ra sbd_arg] in *.
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes bsegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end; [ eapply FRE with (p := a_g1 a) (n := 256); cps_auto | ].
{ cps_callok. }
{ apply (unwind_ch_nf mf0 _ _ _ lo); [rewrite unsigned_lit by lia; unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right]) | left; rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by ulc; lia]. }
intros cf1 (Σf1 & vf1 & Hcf1 & LV_f1 & FRS_f1 & SP_f1 & CR_f1 & PO_f1).
assert (INS_f1 : In (S, 160) (rt_live RT Σf1)) by (rewrite LV_f1; apply live_remove_keep; [exact INS_f0| cbn [fst]; clear - N_S; intros E; apply N_S; rewrite E; do 1 right; left; reflexivity]).
assert (IN_ex_f1 : In (a_exc a, (4 * sbd_subframeSize s)) (rt_live RT Σf1)) by (rewrite LV_f1; apply live_remove_keep; [exact IN_ex_f0| cbn [fst]; clear - N_g1; intros E; apply N_g1; rewrite <- E; left; reflexivity]).
assert (IN_oq_f1 : In (a_oq a, 32) (rt_live RT Σf1)) by (rewrite LV_f1; apply live_remove_keep; [exact IN_oq_f0| cbn [fst]; clear - N_g1; intros E; apply N_g1; rewrite <- E; do 1 right; left; reflexivity]).
assert (IN_iq_f1 : In (a_iq a, 32) (rt_live RT Σf1)) by (rewrite LV_f1; apply live_remove_keep; [exact IN_iq_f0| cbn [fst]; clear - N_g1; intros E; apply N_g1; rewrite <- E; do 2 right; left; reflexivity]).
assert (IN_pg_f1 : In (a_pg a, 16) (rt_live RT Σf1)) by (rewrite LV_f1; apply live_remove_keep; [exact IN_pg_f0| cbn [fst]; clear - N_g1; intros E; apply N_g1; rewrite <- E; do 3 right; left; reflexivity]).
assert (IN_er_f1 : In (a_er a, 16) (rt_live RT Σf1)) by (rewrite LV_f1; apply live_remove_keep; [exact IN_er_f0| cbn [fst]; clear - N_g1; intros E; apply N_g1; rewrite <- E; do 4 right; left; reflexivity]).
assert (IN_msp_f1 : In (a_msp a, 64) (rt_live RT Σf1)) by (rewrite LV_f1; apply live_remove_keep; [exact IN_msp_f0| cbn [fst]; clear - N_g1; intros E; apply N_g1; rewrite <- E; do 5 right; left; reflexivity]).
assert (SUB_f1 : forall e, In e (rt_live RT Σf1) -> In e (rt_live RT Σf0)) by (intros e He; rewrite LV_f1 in He; exact (live_remove_sub _ _ e He)).
assert (LOW_f1 : rt_sp0 RT Σf1 - 8388608 <= lo) by (rewrite SP_f1; assumption).
assert (EF_f1 : rt_frames RT Σf1 = rt_frames RT Σ) by (rewrite FRS_f1; exact EF_f0).
cps_unpack Hcf1 as (mf1 & RS_f1 & (ART_f1 & MI_f1 & ST_f1) & PRES_f1).
assert (UNW_f1 : unwind_ch mf1 ra s0 sp) by (apply (unwind_ch_pres _ _ (usp + -32) mf0 mf1 ra s0 sp PRES_f1); [fold usp; lia| assumption]).
assert (XP_f1 : rw_cells bsegs mf1 S (sbptrs MP (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s)) (Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s)) (Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 (sbd_lpc_enh_enabled s)) (Z_to_bv 64 0) (a_g0 a) (a_g1 a) (a_exc a) (a_oq a) (a_iq a) (a_msp a) (a_pg a) (a_er a))).
{ first [exact XP_f0| apply (rw_cells_agree_nw bsegs mf0 mf1 S _ XP_f0); apply (agree_of_pres _ _ _ mf0 mf1 _ PRES_f1); intros x Hx; right; right; left; exists S, 160; split; [exact INS_f1|]; clear - Hx; cbn in Hx; lia]. }
assert (FR_f1 : rw_cells bsegs mf1 (usp + -32) [CB 8 j0; C8 s1; C8 s0; C8 ra]).
{ first [exact FR_f0| apply (rw_cells_agree_nw bsegs mf0 mf1 _ _ FR_f0); apply (agree_of_pres _ _ _ mf0 mf1 _ PRES_f1); intros x Hx; left; clear - Hx SPT; cbn in Hx; unfold USTACK_TOP in *; lia]. }
clear XP_f0 FR_f0.

destruct (af_acc_live RT AF Σf1 mf1 S 160 ltac:(eassumption) INS_f1) as (_ & ACS_f2).
assert (OBS_f2 : aobj bsegs mf1 S 160) by (split; [lia|]; split; [ulc| exact ACS_f2]).
cps_seg (sbd_free_seg 2%nat usp S MP (a_low a)).
destruct POST as (xb2 & ->). cbn [sbd_ra sbd_arg] in *.
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes bsegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end; [ eapply FRE with (p := a_exc a) (n := (4 * sbd_subframeSize s)); cps_auto | ].
{ cps_callok. }
{ apply (unwind_ch_nf mf1 _ _ _ lo); [rewrite unsigned_lit by lia; unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right]) | left; rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by ulc; lia]. }
intros cf2 (Σf2 & vf2 & Hcf2 & LV_f2 & FRS_f2 & SP_f2 & CR_f2 & PO_f2).
assert (INS_f2 : In (S, 160) (rt_live RT Σf2)) by (rewrite LV_f2; apply live_remove_keep; [exact INS_f1| cbn [fst]; clear - N_S; intros E; apply N_S; rewrite E; do 2 right; left; reflexivity]).
assert (IN_oq_f2 : In (a_oq a, 32) (rt_live RT Σf2)) by (rewrite LV_f2; apply live_remove_keep; [exact IN_oq_f1| cbn [fst]; clear - N_ex; intros E; apply N_ex; rewrite <- E; left; reflexivity]).
assert (IN_iq_f2 : In (a_iq a, 32) (rt_live RT Σf2)) by (rewrite LV_f2; apply live_remove_keep; [exact IN_iq_f1| cbn [fst]; clear - N_ex; intros E; apply N_ex; rewrite <- E; do 1 right; left; reflexivity]).
assert (IN_pg_f2 : In (a_pg a, 16) (rt_live RT Σf2)) by (rewrite LV_f2; apply live_remove_keep; [exact IN_pg_f1| cbn [fst]; clear - N_ex; intros E; apply N_ex; rewrite <- E; do 2 right; left; reflexivity]).
assert (IN_er_f2 : In (a_er a, 16) (rt_live RT Σf2)) by (rewrite LV_f2; apply live_remove_keep; [exact IN_er_f1| cbn [fst]; clear - N_ex; intros E; apply N_ex; rewrite <- E; do 3 right; left; reflexivity]).
assert (IN_msp_f2 : In (a_msp a, 64) (rt_live RT Σf2)) by (rewrite LV_f2; apply live_remove_keep; [exact IN_msp_f1| cbn [fst]; clear - N_ex; intros E; apply N_ex; rewrite <- E; do 4 right; left; reflexivity]).
assert (SUB_f2 : forall e, In e (rt_live RT Σf2) -> In e (rt_live RT Σf1)) by (intros e He; rewrite LV_f2 in He; exact (live_remove_sub _ _ e He)).
assert (LOW_f2 : rt_sp0 RT Σf2 - 8388608 <= lo) by (rewrite SP_f2; assumption).
assert (EF_f2 : rt_frames RT Σf2 = rt_frames RT Σ) by (rewrite FRS_f2; exact EF_f1).
cps_unpack Hcf2 as (mf2 & RS_f2 & (ART_f2 & MI_f2 & ST_f2) & PRES_f2).
assert (UNW_f2 : unwind_ch mf2 ra s0 sp) by (apply (unwind_ch_pres _ _ (usp + -32) mf1 mf2 ra s0 sp PRES_f2); [fold usp; lia| assumption]).
assert (XP_f2 : rw_cells bsegs mf2 S (sbptrs MP (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s)) (Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s)) (Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 (sbd_lpc_enh_enabled s)) (Z_to_bv 64 0) (a_g0 a) (a_g1 a) (a_exc a) (a_oq a) (a_iq a) (a_msp a) (a_pg a) (a_er a))).
{ first [exact XP_f1| apply (rw_cells_agree_nw bsegs mf1 mf2 S _ XP_f1); apply (agree_of_pres _ _ _ mf1 mf2 _ PRES_f2); intros x Hx; right; right; left; exists S, 160; split; [exact INS_f2|]; clear - Hx; cbn in Hx; lia]. }
assert (FR_f2 : rw_cells bsegs mf2 (usp + -32) [CB 8 j0; C8 s1; C8 s0; C8 ra]).
{ first [exact FR_f1| apply (rw_cells_agree_nw bsegs mf1 mf2 _ _ FR_f1); apply (agree_of_pres _ _ _ mf1 mf2 _ PRES_f2); intros x Hx; left; clear - Hx SPT; cbn in Hx; unfold USTACK_TOP in *; lia]. }
clear XP_f1 FR_f1.

destruct (af_acc_live RT AF Σf2 mf2 S 160 ltac:(eassumption) INS_f2) as (_ & ACS_f3).
assert (OBS_f3 : aobj bsegs mf2 S 160) by (split; [lia|]; split; [ulc| exact ACS_f3]).
cps_seg (sbd_free_seg 3%nat usp S MP (a_low a)).
destruct POST as (xb3 & ->). cbn [sbd_ra sbd_arg] in *.
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes bsegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end; [ eapply FRE with (p := a_oq a) (n := 32); cps_auto | ].
{ cps_callok. }
{ apply (unwind_ch_nf mf2 _ _ _ lo); [rewrite unsigned_lit by lia; unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right]) | left; rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by ulc; lia]. }
intros cf3 (Σf3 & vf3 & Hcf3 & LV_f3 & FRS_f3 & SP_f3 & CR_f3 & PO_f3).
assert (INS_f3 : In (S, 160) (rt_live RT Σf3)) by (rewrite LV_f3; apply live_remove_keep; [exact INS_f2| cbn [fst]; clear - N_S; intros E; apply N_S; rewrite E; do 3 right; left; reflexivity]).
assert (IN_iq_f3 : In (a_iq a, 32) (rt_live RT Σf3)) by (rewrite LV_f3; apply live_remove_keep; [exact IN_iq_f2| cbn [fst]; clear - N_oq; intros E; apply N_oq; rewrite <- E; left; reflexivity]).
assert (IN_pg_f3 : In (a_pg a, 16) (rt_live RT Σf3)) by (rewrite LV_f3; apply live_remove_keep; [exact IN_pg_f2| cbn [fst]; clear - N_oq; intros E; apply N_oq; rewrite <- E; do 1 right; left; reflexivity]).
assert (IN_er_f3 : In (a_er a, 16) (rt_live RT Σf3)) by (rewrite LV_f3; apply live_remove_keep; [exact IN_er_f2| cbn [fst]; clear - N_oq; intros E; apply N_oq; rewrite <- E; do 2 right; left; reflexivity]).
assert (IN_msp_f3 : In (a_msp a, 64) (rt_live RT Σf3)) by (rewrite LV_f3; apply live_remove_keep; [exact IN_msp_f2| cbn [fst]; clear - N_oq; intros E; apply N_oq; rewrite <- E; do 3 right; left; reflexivity]).
assert (SUB_f3 : forall e, In e (rt_live RT Σf3) -> In e (rt_live RT Σf2)) by (intros e He; rewrite LV_f3 in He; exact (live_remove_sub _ _ e He)).
assert (LOW_f3 : rt_sp0 RT Σf3 - 8388608 <= lo) by (rewrite SP_f3; assumption).
assert (EF_f3 : rt_frames RT Σf3 = rt_frames RT Σ) by (rewrite FRS_f3; exact EF_f2).
cps_unpack Hcf3 as (mf3 & RS_f3 & (ART_f3 & MI_f3 & ST_f3) & PRES_f3).
assert (UNW_f3 : unwind_ch mf3 ra s0 sp) by (apply (unwind_ch_pres _ _ (usp + -32) mf2 mf3 ra s0 sp PRES_f3); [fold usp; lia| assumption]).
assert (XP_f3 : rw_cells bsegs mf3 S (sbptrs MP (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s)) (Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s)) (Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 (sbd_lpc_enh_enabled s)) (Z_to_bv 64 0) (a_g0 a) (a_g1 a) (a_exc a) (a_oq a) (a_iq a) (a_msp a) (a_pg a) (a_er a))).
{ first [exact XP_f2| apply (rw_cells_agree_nw bsegs mf2 mf3 S _ XP_f2); apply (agree_of_pres _ _ _ mf2 mf3 _ PRES_f3); intros x Hx; right; right; left; exists S, 160; split; [exact INS_f3|]; clear - Hx; cbn in Hx; lia]. }
assert (FR_f3 : rw_cells bsegs mf3 (usp + -32) [CB 8 j0; C8 s1; C8 s0; C8 ra]).
{ first [exact FR_f2| apply (rw_cells_agree_nw bsegs mf2 mf3 _ _ FR_f2); apply (agree_of_pres _ _ _ mf2 mf3 _ PRES_f3); intros x Hx; left; clear - Hx SPT; cbn in Hx; unfold USTACK_TOP in *; lia]. }
clear XP_f2 FR_f2.

destruct (af_acc_live RT AF Σf3 mf3 S 160 ltac:(eassumption) INS_f3) as (_ & ACS_f4).
assert (OBS_f4 : aobj bsegs mf3 S 160) by (split; [lia|]; split; [ulc| exact ACS_f4]).
cps_seg (sbd_free_seg 4%nat usp S MP (a_low a)).
destruct POST as (xb4 & ->). cbn [sbd_ra sbd_arg] in *.
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes bsegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end; [ eapply FRE with (p := a_iq a) (n := 32); cps_auto | ].
{ cps_callok. }
{ apply (unwind_ch_nf mf3 _ _ _ lo); [rewrite unsigned_lit by lia; unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right]) | left; rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by ulc; lia]. }
intros cf4 (Σf4 & vf4 & Hcf4 & LV_f4 & FRS_f4 & SP_f4 & CR_f4 & PO_f4).
assert (INS_f4 : In (S, 160) (rt_live RT Σf4)) by (rewrite LV_f4; apply live_remove_keep; [exact INS_f3| cbn [fst]; clear - N_S; intros E; apply N_S; rewrite E; do 4 right; left; reflexivity]).
assert (IN_pg_f4 : In (a_pg a, 16) (rt_live RT Σf4)) by (rewrite LV_f4; apply live_remove_keep; [exact IN_pg_f3| cbn [fst]; clear - N_iq; intros E; apply N_iq; rewrite <- E; left; reflexivity]).
assert (IN_er_f4 : In (a_er a, 16) (rt_live RT Σf4)) by (rewrite LV_f4; apply live_remove_keep; [exact IN_er_f3| cbn [fst]; clear - N_iq; intros E; apply N_iq; rewrite <- E; do 1 right; left; reflexivity]).
assert (IN_msp_f4 : In (a_msp a, 64) (rt_live RT Σf4)) by (rewrite LV_f4; apply live_remove_keep; [exact IN_msp_f3| cbn [fst]; clear - N_iq; intros E; apply N_iq; rewrite <- E; do 2 right; left; reflexivity]).
assert (SUB_f4 : forall e, In e (rt_live RT Σf4) -> In e (rt_live RT Σf3)) by (intros e He; rewrite LV_f4 in He; exact (live_remove_sub _ _ e He)).
assert (LOW_f4 : rt_sp0 RT Σf4 - 8388608 <= lo) by (rewrite SP_f4; assumption).
assert (EF_f4 : rt_frames RT Σf4 = rt_frames RT Σ) by (rewrite FRS_f4; exact EF_f3).
cps_unpack Hcf4 as (mf4 & RS_f4 & (ART_f4 & MI_f4 & ST_f4) & PRES_f4).
assert (UNW_f4 : unwind_ch mf4 ra s0 sp) by (apply (unwind_ch_pres _ _ (usp + -32) mf3 mf4 ra s0 sp PRES_f4); [fold usp; lia| assumption]).
assert (XP_f4 : rw_cells bsegs mf4 S (sbptrs MP (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s)) (Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s)) (Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 (sbd_lpc_enh_enabled s)) (Z_to_bv 64 0) (a_g0 a) (a_g1 a) (a_exc a) (a_oq a) (a_iq a) (a_msp a) (a_pg a) (a_er a))).
{ first [exact XP_f3| apply (rw_cells_agree_nw bsegs mf3 mf4 S _ XP_f3); apply (agree_of_pres _ _ _ mf3 mf4 _ PRES_f4); intros x Hx; right; right; left; exists S, 160; split; [exact INS_f4|]; clear - Hx; cbn in Hx; lia]. }
assert (FR_f4 : rw_cells bsegs mf4 (usp + -32) [CB 8 j0; C8 s1; C8 s0; C8 ra]).
{ first [exact FR_f3| apply (rw_cells_agree_nw bsegs mf3 mf4 _ _ FR_f3); apply (agree_of_pres _ _ _ mf3 mf4 _ PRES_f4); intros x Hx; left; clear - Hx SPT; cbn in Hx; unfold USTACK_TOP in *; lia]. }
clear XP_f3 FR_f3.

destruct (af_acc_live RT AF Σf4 mf4 S 160 ltac:(eassumption) INS_f4) as (_ & ACS_f5).
assert (OBS_f5 : aobj bsegs mf4 S 160) by (split; [lia|]; split; [ulc| exact ACS_f5]).
cps_seg (sbd_free_seg 5%nat usp S MP (a_low a)).
destruct POST as (xb5 & ->). cbn [sbd_ra sbd_arg] in *.
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes bsegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end; [ eapply FRE with (p := a_pg a) (n := 16); cps_auto | ].
{ cps_callok. }
{ apply (unwind_ch_nf mf4 _ _ _ lo); [rewrite unsigned_lit by lia; unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right]) | left; rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by ulc; lia]. }
intros cf5 (Σf5 & vf5 & Hcf5 & LV_f5 & FRS_f5 & SP_f5 & CR_f5 & PO_f5).
assert (INS_f5 : In (S, 160) (rt_live RT Σf5)) by (rewrite LV_f5; apply live_remove_keep; [exact INS_f4| cbn [fst]; clear - N_S; intros E; apply N_S; rewrite E; do 5 right; left; reflexivity]).
assert (IN_er_f5 : In (a_er a, 16) (rt_live RT Σf5)) by (rewrite LV_f5; apply live_remove_keep; [exact IN_er_f4| cbn [fst]; clear - N_pg; intros E; apply N_pg; rewrite <- E; left; reflexivity]).
assert (IN_msp_f5 : In (a_msp a, 64) (rt_live RT Σf5)) by (rewrite LV_f5; apply live_remove_keep; [exact IN_msp_f4| cbn [fst]; clear - N_pg; intros E; apply N_pg; rewrite <- E; do 1 right; left; reflexivity]).
assert (SUB_f5 : forall e, In e (rt_live RT Σf5) -> In e (rt_live RT Σf4)) by (intros e He; rewrite LV_f5 in He; exact (live_remove_sub _ _ e He)).
assert (LOW_f5 : rt_sp0 RT Σf5 - 8388608 <= lo) by (rewrite SP_f5; assumption).
assert (EF_f5 : rt_frames RT Σf5 = rt_frames RT Σ) by (rewrite FRS_f5; exact EF_f4).
cps_unpack Hcf5 as (mf5 & RS_f5 & (ART_f5 & MI_f5 & ST_f5) & PRES_f5).
assert (UNW_f5 : unwind_ch mf5 ra s0 sp) by (apply (unwind_ch_pres _ _ (usp + -32) mf4 mf5 ra s0 sp PRES_f5); [fold usp; lia| assumption]).
assert (XP_f5 : rw_cells bsegs mf5 S (sbptrs MP (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s)) (Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s)) (Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 (sbd_lpc_enh_enabled s)) (Z_to_bv 64 0) (a_g0 a) (a_g1 a) (a_exc a) (a_oq a) (a_iq a) (a_msp a) (a_pg a) (a_er a))).
{ first [exact XP_f4| apply (rw_cells_agree_nw bsegs mf4 mf5 S _ XP_f4); apply (agree_of_pres _ _ _ mf4 mf5 _ PRES_f5); intros x Hx; right; right; left; exists S, 160; split; [exact INS_f5|]; clear - Hx; cbn in Hx; lia]. }
assert (FR_f5 : rw_cells bsegs mf5 (usp + -32) [CB 8 j0; C8 s1; C8 s0; C8 ra]).
{ first [exact FR_f4| apply (rw_cells_agree_nw bsegs mf4 mf5 _ _ FR_f4); apply (agree_of_pres _ _ _ mf4 mf5 _ PRES_f5); intros x Hx; left; clear - Hx SPT; cbn in Hx; unfold USTACK_TOP in *; lia]. }
clear XP_f4 FR_f4.

destruct (af_acc_live RT AF Σf5 mf5 S 160 ltac:(eassumption) INS_f5) as (_ & ACS_f6).
assert (OBS_f6 : aobj bsegs mf5 S 160) by (split; [lia|]; split; [ulc| exact ACS_f6]).
cps_seg (sbd_free_seg 6%nat usp S MP (a_low a)).
destruct POST as (xb6 & ->). cbn [sbd_ra sbd_arg] in *.
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes bsegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end; [ eapply FRE with (p := a_er a) (n := 16); cps_auto | ].
{ cps_callok. }
{ apply (unwind_ch_nf mf5 _ _ _ lo); [rewrite unsigned_lit by lia; unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right]) | left; rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by ulc; lia]. }
intros cf6 (Σf6 & vf6 & Hcf6 & LV_f6 & FRS_f6 & SP_f6 & CR_f6 & PO_f6).
assert (INS_f6 : In (S, 160) (rt_live RT Σf6)) by (rewrite LV_f6; apply live_remove_keep; [exact INS_f5| cbn [fst]; clear - N_S; intros E; apply N_S; rewrite E; do 6 right; left; reflexivity]).
assert (IN_msp_f6 : In (a_msp a, 64) (rt_live RT Σf6)) by (rewrite LV_f6; apply live_remove_keep; [exact IN_msp_f5| cbn [fst]; clear - N_er; intros E; apply N_er; rewrite <- E; left; reflexivity]).
assert (SUB_f6 : forall e, In e (rt_live RT Σf6) -> In e (rt_live RT Σf5)) by (intros e He; rewrite LV_f6 in He; exact (live_remove_sub _ _ e He)).
assert (LOW_f6 : rt_sp0 RT Σf6 - 8388608 <= lo) by (rewrite SP_f6; assumption).
assert (EF_f6 : rt_frames RT Σf6 = rt_frames RT Σ) by (rewrite FRS_f6; exact EF_f5).
cps_unpack Hcf6 as (mf6 & RS_f6 & (ART_f6 & MI_f6 & ST_f6) & PRES_f6).
assert (UNW_f6 : unwind_ch mf6 ra s0 sp) by (apply (unwind_ch_pres _ _ (usp + -32) mf5 mf6 ra s0 sp PRES_f6); [fold usp; lia| assumption]).
assert (XP_f6 : rw_cells bsegs mf6 S (sbptrs MP (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s)) (Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s)) (Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 (sbd_lpc_enh_enabled s)) (Z_to_bv 64 0) (a_g0 a) (a_g1 a) (a_exc a) (a_oq a) (a_iq a) (a_msp a) (a_pg a) (a_er a))).
{ first [exact XP_f5| apply (rw_cells_agree_nw bsegs mf5 mf6 S _ XP_f5); apply (agree_of_pres _ _ _ mf5 mf6 _ PRES_f6); intros x Hx; right; right; left; exists S, 160; split; [exact INS_f6|]; clear - Hx; cbn in Hx; lia]. }
assert (FR_f6 : rw_cells bsegs mf6 (usp + -32) [CB 8 j0; C8 s1; C8 s0; C8 ra]).
{ first [exact FR_f5| apply (rw_cells_agree_nw bsegs mf5 mf6 _ _ FR_f5); apply (agree_of_pres _ _ _ mf5 mf6 _ PRES_f6); intros x Hx; left; clear - Hx SPT; cbn in Hx; unfold USTACK_TOP in *; lia]. }
clear XP_f5 FR_f5.

destruct (af_acc_live RT AF Σf6 mf6 S 160 ltac:(eassumption) INS_f6) as (_ & ACS_f7).
assert (OBS_f7 : aobj bsegs mf6 S 160) by (split; [lia|]; split; [ulc| exact ACS_f7]).
cps_seg (sbd_free_seg 7%nat usp S MP (a_low a)).
destruct POST as (xb7 & ->). cbn [sbd_ra sbd_arg] in *.
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes bsegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end; [ eapply FRE with (p := a_msp a) (n := 64); cps_auto | ].
{ cps_callok. }
{ apply (unwind_ch_nf mf6 _ _ _ lo); [rewrite unsigned_lit by lia; unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right]) | left; rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by ulc; lia]. }
intros cf7 (Σf7 & vf7 & Hcf7 & LV_f7 & FRS_f7 & SP_f7 & CR_f7 & PO_f7).
assert (INS_f7 : In (S, 160) (rt_live RT Σf7)) by (rewrite LV_f7; apply live_remove_keep; [exact INS_f6| cbn [fst]; clear - N_S; intros E; apply N_S; rewrite E; do 7 right; left; reflexivity]).
assert (SUB_f7 : forall e, In e (rt_live RT Σf7) -> In e (rt_live RT Σf6)) by (intros e He; rewrite LV_f7 in He; exact (live_remove_sub _ _ e He)).
assert (LOW_f7 : rt_sp0 RT Σf7 - 8388608 <= lo) by (rewrite SP_f7; assumption).
assert (EF_f7 : rt_frames RT Σf7 = rt_frames RT Σ) by (rewrite FRS_f7; exact EF_f6).
cps_unpack Hcf7 as (mf7 & RS_f7 & (ART_f7 & MI_f7 & ST_f7) & PRES_f7).
assert (UNW_f7 : unwind_ch mf7 ra s0 sp) by (apply (unwind_ch_pres _ _ (usp + -32) mf6 mf7 ra s0 sp PRES_f7); [fold usp; lia| assumption]).
assert (XP_f7 : rw_cells bsegs mf7 S (sbptrs MP (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s)) (Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s)) (Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 (sbd_lpc_enh_enabled s)) (Z_to_bv 64 0) (a_g0 a) (a_g1 a) (a_exc a) (a_oq a) (a_iq a) (a_msp a) (a_pg a) (a_er a))).
{ first [exact XP_f6| apply (rw_cells_agree_nw bsegs mf6 mf7 S _ XP_f6); apply (agree_of_pres _ _ _ mf6 mf7 _ PRES_f7); intros x Hx; right; right; left; exists S, 160; split; [exact INS_f7|]; clear - Hx; cbn in Hx; lia]. }
assert (FR_f7 : rw_cells bsegs mf7 (usp + -32) [CB 8 j0; C8 s1; C8 s0; C8 ra]).
{ first [exact FR_f6| apply (rw_cells_agree_nw bsegs mf6 mf7 _ _ FR_f6); apply (agree_of_pres _ _ _ mf6 mf7 _ PRES_f7); intros x Hx; left; clear - Hx SPT; cbn in Hx; unfold USTACK_TOP in *; lia]. }
clear XP_f6 FR_f6.

cps_seg (sbd_last usp lo S).
destruct POST as (-> & STL).
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes bsegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end; [ eapply FRE with (p := S) (n := 160); cps_auto | ].
{ cps_callok. } { rewrite <- ESP. exact UNW_f7. }
intros cfl (Σl & vl & Hcl & LVl & FRSl & SPl & CRl & POl).
cps_unpack Hcl as (ml & RSl & (ARTl & MIl & STl) & PRESl).
apply Hk. exists Σl. split.
- eapply ASTA_conseq; [eassumption|]. intros ms <-. exists vl, ml.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split; [exact (conj ARTl (conj MIl STl))|].
intros x Hx _.
assert (C7 : aclient (rt_live RT Σf7) (rt_frames RT Σ) (usp + -32) (bv_unsigned x)).
{ apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; rewrite LVl in He; exact (live_remove_sub _ _ e He)| auto| lia]. }
assert (C6 : aclient (rt_live RT Σf6) (rt_frames RT Σ) (usp + -32) (bv_unsigned x)) by (apply (aclient_mono _ _ _ _ _ _ _ C7); [exact SUB_f7| auto| lia]).
assert (C5 : aclient (rt_live RT Σf5) (rt_frames RT Σ) (usp + -32) (bv_unsigned x)) by (apply (aclient_mono _ _ _ _ _ _ _ C6); [exact SUB_f6| auto| lia]).
assert (C4 : aclient (rt_live RT Σf4) (rt_frames RT Σ) (usp + -32) (bv_unsigned x)) by (apply (aclient_mono _ _ _ _ _ _ _ C5); [exact SUB_f5| auto| lia]).
assert (C3 : aclient (rt_live RT Σf3) (rt_frames RT Σ) (usp + -32) (bv_unsigned x)) by (apply (aclient_mono _ _ _ _ _ _ _ C4); [exact SUB_f4| auto| lia]).
assert (C2 : aclient (rt_live RT Σf2) (rt_frames RT Σ) (usp + -32) (bv_unsigned x)) by (apply (aclient_mono _ _ _ _ _ _ _ C3); [exact SUB_f3| auto| lia]).
assert (C1 : aclient (rt_live RT Σf1) (rt_frames RT Σ) (usp + -32) (bv_unsigned x)) by (apply (aclient_mono _ _ _ _ _ _ _ C2); [exact SUB_f2| auto| lia]).
assert (C0 : aclient (rt_live RT Σf0) (rt_frames RT Σ) (usp + -32) (bv_unsigned x)) by (apply (aclient_mono _ _ _ _ _ _ _ C1); [exact SUB_f1| auto| lia]).
assert (Ca : aclient (rt_live RT Σa) (rt_frames RT Σ) (usp + -32) (bv_unsigned x)) by (apply (aclient_mono _ _ _ _ _ _ _ C0); [exact SUB_f0| auto| lia]).
assert (C00 : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x)).
{ apply (aclient_mono _ _ _ _ _ _ _ Hx); [| auto| lia]. intros e He. apply SUBa. apply SUB_f0. apply SUB_f1. apply SUB_f2. apply SUB_f3. apply SUB_f4. apply SUB_f5. apply SUB_f6. apply SUB_f7.
rewrite LVl in He. exact (live_remove_sub _ _ e He). }
rewrite (PRESl x); [| rewrite EF_f7; exact Hx].
rewrite (PRES_f7 x); [| rewrite EF_f6; exact C7].
rewrite (PRES_f6 x); [| rewrite EF_f5; exact C6].
rewrite (PRES_f5 x); [| rewrite EF_f4; exact C5].
rewrite (PRES_f4 x); [| rewrite EF_f3; exact C4].
rewrite (PRES_f3 x); [| rewrite EF_f2; exact C3].
rewrite (PRES_f2 x); [| rewrite EF_f1; exact C2].
rewrite (PRES_f1 x); [| rewrite EF_f0; exact C1].
rewrite (PRES_f0 x); [| rewrite EF_a; exact C0].
rewrite (PRESa x); [| exact Ca | exact I].
apply MU1. cbn [outside]. split; [| exact I]. clear - SPL C00 LOW LOR DSP. specialize (SPL _ C00). lia.
- split; [| split; [rewrite FRSl; exact EF_f7|]; repeat split; congruence].
rewrite LVl, LV_f7, LV_f6, LV_f5, LV_f4, LV_f3, LV_f2, LV_f1, LV_f0, LVa.
rewrite <- !live_remove_list_snoc.
apply live_remove_list_perm. rewrite map_app. cbn [sb_blocks map blk_addr fst snd].
repeat rewrite <- app_assoc. cbn [app].
eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app].
apply Permutation_sym. exact (Permutation_middle [a_g0 a; a_g1 a; a_exc a; a_oq a; a_iq a; a_pg a; a_er a; a_msp a] (map blk_addr LBL) S).
Qed.

Theorem destroy_cps_all : forall d, destroy_cps_at d.
Proof using AF FRE AF_LIB.
induction d as [st|s low IH]; [exact (destroy_cps_nb st)| exact (destroy_cps_sb s low IH)].
Qed.

End DestroyCPS.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition live_remove_list (ps : list Z) (l : list (Z * Z)) : list (Z * Z) := fold_right live_remove l ps.

Lemma live_remove_list_app : forall ps qs l, live_remove_list (ps ++ qs) l = live_remove_list ps (live_remove_list qs l).
Proof. intros. unfold live_remove_list. apply fold_right_app. Qed.

Lemma live_remove_in : forall p l e, In e (live_remove p l) <-> In e l /\ fst e <> p.
Proof.
intros p l e. split.
- intros H. split; [exact (live_remove_sub l p e H)|]. unfold live_remove in H.
apply stdpp.base.list_elem_of_In in H. apply stdpp.list_basics.list.list_elem_of_filter in H. destruct H as [H _].
intros E. rewrite E, Z.eqb_refl in H. exact H.
- intros [H1 H2]. exact (live_remove_keep l p e H1 H2).
Qed.

Lemma live_remove_comm : forall p q l, live_remove p (live_remove q l) = live_remove q (live_remove p l).
Proof.
intros p q l. unfold live_remove.
rewrite !stdpp.list_basics.list.list_filter_filter. apply stdpp.list_basics.list.list_filter_iff. intros x. tauto.
Qed.

Lemma live_remove_list_keep : forall ps l e, In e l -> ~ In (fst e) ps -> In e (live_remove_list ps l).
Proof.
induction ps as [|p ps IH]; intros l e H N; [exact H|]. cbn. apply live_remove_keep; [apply IH; [exact H| intros X; apply N; right; exact X]|].
intros E. apply N. left. symmetry. exact E.
Qed.
Lemma live_remove_list_sub : forall ps l e, In e (live_remove_list ps l) -> In e l.
Proof. induction ps as [|p ps IH]; intros l e H; [exact H|]. cbn in H. apply IH. exact (live_remove_sub _ _ _ H). Qed.

Lemma live_remove_list_snoc : forall ps p l, live_remove_list (ps ++ [p]) l = live_remove p (live_remove_list ps l).
Proof.
unfold live_remove_list. induction ps as [|q ps IH]; intros p l; [reflexivity|]. cbn [app fold_right]. rewrite IH. apply live_remove_comm.
Qed.

Fixpoint destroy_stack (d : dec_state bptr) : Z := match d with DecNB _ => 16 | DecSB _ low => 32 + destroy_stack low end.

Section DestroyCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis FRE : free_contract RT.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.

Definition destroy_cps_at (d : dec_state bptr) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (OUT STEREO S lo : Z) (LBD : list block),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 S -> tp = Z_to_bv 64 0x630458 ->
DREP OUT STEREO m S d LBD -> List.NoDup (map blk_id LBD) ->
(forall b, In b LBD -> In (blk_addr b, blk_size b) (rt_live RT Σ)) ->
ART RT Σ m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + destroy_stack d <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
unwind_ch m ra s0 sp ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_speex_decoder_destroy m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists v m',
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) [] m m') c
/\ rt_live RT Σ' = live_remove_list (map blk_addr LBD) (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem destroy_cps_nb : forall st, destroy_cps_at (DecNB st).
Proof using AF FRE AF_LIB.
intros st Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m OUT STEREO S lo LBD
FDO MST E0 ETP REP ND LIVE ART0 MI0 ST0 LOW LOR SPT SPA UNW.
cbn [decst_rep] in REP. destruct REP as [-> NB]. cbn [destroy_stack] in LOR.
pose proof (LIVE _ ltac:(left; reflexivity)) as INL. unfold blk_addr, blk_size in INL. cbn [fst snd] in INL.
exact (nb_decoder_destroy_ok RT AF FRE AF_LIB Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S OUT STEREO lo st
FDO MST E0 ETP NB INL ART0 MI0 ST0 LOW LOR SPT SPA UNW).
Qed.

Lemma live_remove_list_perm : forall ps qs l, Permutation ps qs -> live_remove_list ps l = live_remove_list qs l.
Proof.
intros ps qs l H. unfold live_remove_list. induction H as [|x ps qs H IH|x y ps|ps qs rs H1 IH1 H2 IH2]; [reflexivity| cbn [fold_right]; rewrite IH; reflexivity| cbn [fold_right]; apply live_remove_comm| congruence].
Qed.

Lemma uw_chain_pres : forall live frames sp (m m' : mem) ras f fp,
rt_pres live frames sp m m' -> sp <= f -> uw_chain USTACK_TOP m f fp ras -> uw_chain USTACK_TOP m' f fp ras.
Proof.
intros live frames sp m m'. induction ras as [|r ras IHr]; intros f fp PR Hf H; cbn [uw_chain] in *; [exact H|].
destruct H as (H1 & H2 & H3 & fp' & H4 & H5 & H6).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. exists fp'. split; [exact H4|]. split.
- apply (rw_cells_agree_nw asegs m m' _ _ H5). apply (agree_of_pres live frames sp m m' _ PR). intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. lia.
- apply (IHr fp fp' PR); [lia| exact H6].
Qed.
Lemma unwind_ch_pres : forall live frames sp' (m m' : mem) ra s0 sp,
rt_pres live frames sp' m m' -> sp' <= bv_unsigned sp -> unwind_ch m ra s0 sp -> unwind_ch m' ra s0 sp.
Proof. intros live frames sp' m m' ra s0 sp PR Hs (ras & H1 & H2). exists ras. split; [exact H1| exact (uw_chain_pres live frames sp' m m' ras _ _ PR Hs H2)]. Qed.
Lemma unwind_ch_pres_fp : forall live frames sp' (m m' : mem) ra s0 sp,
rt_pres_fp live frames sp' [] m m' -> sp' <= bv_unsigned sp -> unwind_ch m ra s0 sp -> unwind_ch m' ra s0 sp.
Proof. intros live frames sp' m m' ra s0 sp PR. apply (unwind_ch_pres live frames). intros a Ha. exact (PR a Ha I). Qed.

Definition sbtl2 (s : sbd_state bptr) (a : sb_addrs) (OUT : Z) (j : sb_junk) : list cell :=
[C8 (Z_to_bv 64 (sb_isave_ptr OUT s)); C4 (sj_last_ener j); C4 (sj_seed j); C4 (Z_to_bv 64 (sbd_encode_submode s)); CB 4 (sj_pad1 j);
C8 (Z_to_bv 64 (sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR (sbd_mode s))); C4 (Z_to_bv 64 (sbd_submodeID s)); CB 4 (sj_pad2 j)].
Lemma sb_cells_ptrs : forall s a OUT j,
SBCELLS s a OUT j = sbptrs (sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode (sbd_mode s)) (a_low a)
(Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s)) (Z_to_bv 64 (sbd_nbSubframes s))
(Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s)) (Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 (sbd_lpc_enh_enabled s))
(Z_to_bv 64 0) (a_g0 a) (a_g1 a) (a_exc a) (a_oq a) (a_iq a) (a_msp a) (a_pg a) (a_er a) ++ sbtl2 s a OUT j.
Proof. reflexivity. Qed.

Theorem destroy_cps_sb : forall s low, destroy_cps_at low -> destroy_cps_at (DecSB s low).
Proof using AF FRE AF_LIB.
intros s low IH Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m OUT STEREO S lo LBD
FDO MST -> -> REP ND LIVE ART0 MI0 ST0 LOW LOR SPT SPA UNW.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
cbn [destroy_stack] in LOR.
assert (DSP : 0 <= destroy_stack low) by (clear; induction low; cbn [destroy_stack]; lia).
cbn [decst_rep] in REP. destruct REP as (a & j & LBL & ELBD & S8 & SPOS & INV & JOK & X & _ & OUTL & RLOW).
pose proof INV as (IMODE & _). subst LBD.

assert (INS : In (S, 160) (rt_live RT Σ)) by (exact (LIVE (sbd_blk s, S, SBSTATE_SIZEOF) ltac:(left; reflexivity))).
assert (IN_g0 : In (a_g0 a, 256) (rt_live RT Σ)) by (refine (LIVE (_, a_g0 a, 256) _); cbn [sb_blocks app In]; tauto).
assert (IN_g1 : In (a_g1 a, 256) (rt_live RT Σ)) by (refine (LIVE (_, a_g1 a, 256) _); cbn [sb_blocks app In]; tauto).
assert (IN_ex : In (a_exc a, (4 * sbd_subframeSize s)) (rt_live RT Σ)) by (refine (LIVE (_, a_exc a, (4 * sbd_subframeSize s)) _); cbn [sb_blocks app In]; tauto).
assert (IN_oq : In (a_oq a, 32) (rt_live RT Σ)) by (refine (LIVE (_, a_oq a, 32) _); cbn [sb_blocks app In]; tauto).
assert (IN_iq : In (a_iq a, 32) (rt_live RT Σ)) by (refine (LIVE (_, a_iq a, 32) _); cbn [sb_blocks app In]; tauto).
assert (IN_pg : In (a_pg a, 16) (rt_live RT Σ)) by (refine (LIVE (_, a_pg a, 16) _); cbn [sb_blocks app In]; tauto).
assert (IN_er : In (a_er a, 16) (rt_live RT Σ)) by (refine (LIVE (_, a_er a, 16) _); cbn [sb_blocks app In]; tauto).
assert (IN_msp : In (a_msp a, 64) (rt_live RT Σ)) by (refine (LIVE (_, a_msp a, 64) _); cbn [sb_blocks app In]; tauto).
assert (LIVEL : forall b, In b LBL -> In (blk_addr b, blk_size b) (rt_live RT Σ)) by (intros b Hb; apply LIVE; apply in_app_iff; right; exact Hb).
cbn [sb_blocks app map blk_id blk_addr fst snd] in ND.
apply List.NoDup_cons_iff in ND. destruct ND as [N_S ND].
apply List.NoDup_cons_iff in ND. destruct ND as [N_g0 ND].
apply List.NoDup_cons_iff in ND. destruct ND as [N_g1 ND].
apply List.NoDup_cons_iff in ND. destruct ND as [N_ex ND].
apply List.NoDup_cons_iff in ND. destruct ND as [N_oq ND].
apply List.NoDup_cons_iff in ND. destruct ND as [N_iq ND].
apply List.NoDup_cons_iff in ND. destruct ND as [N_pg ND].
apply List.NoDup_cons_iff in ND. destruct ND as [N_er ND].
apply List.NoDup_cons_iff in ND. destruct ND as [N_msp ND].
rename ND into NDL. fold (map blk_id LBL) in *.
clear LIVE.
destruct (live_below_lo RT AF Σ m S 160 lo ART0 INS LOW) as (_ & BS1 & LOS).
destruct (af_acc_live RT AF Σ m S 160 ART0 INS) as (_ & ACS).

pose proof (AF_LIB Σ m ART0) as LC0.
rewrite sb_cells_ptrs in X.
set (MP := sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode (sbd_mode s)) in *.
assert (MPF : exists c0 c1 c2 c3 c4 c5 c6 c7 c8 c10 c11 c12, ro_cells asegs m MP (sbd_desc_cells c0 c1 c2 c3 c4 c5 c6 c7 c8 c10 c11 c12)
/\ aobj asegs m MP 96 /\ MP mod 8 = 0 /\ 0x10000 <= MP /\ MP + 104 <= 0x652000).
{ subst MP. destruct IMODE as [E|E]; rewrite E; cbn [sb_mode_ptr].
- do 12 eexists. split; [exact (lib_const m A_speex_wb_mode LC_speex_wb_mode LC0 ltac:(lc_in))|].
split; [apply (aobj_lit RT AF Σ m A_speex_wb_mode 96 ART0); [unfold ACC_LITS, A_speex_wb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_speex_wb_mode; lia | unfold A_speex_wb_mode, APP_TOP; lia]|].
unfold A_speex_wb_mode. repeat split; lia.
- do 12 eexists. split; [exact (lib_const m A_speex_uwb_mode LC_speex_uwb_mode LC0 ltac:(lc_in))|].
split; [apply (aobj_lit RT AF Σ m A_speex_uwb_mode 96 ART0); [unfold ACC_LITS, A_speex_uwb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_speex_uwb_mode; lia | unfold A_speex_uwb_mode, APP_TOP; lia]|].
unfold A_speex_uwb_mode. repeat split; lia. }
destruct MPF as (c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & c8 & c10 & c11 & c12 & ND0 & OBM & MP8 & MPLO & MPHI). clearbody MP.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
assert (OBS : aobj asegs m S 160) by (split; [lia|]; split; [unfold APP_TOP, STACK_WIN, USTACK_TOP, RT_STACK in *; lia| exact ACS]).
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
assert (LO32 : lo <= usp + -32) by (clear - LOR DSP; unfold RT_STACK in LOR; lia).
assert (SBF : 0 < S /\ S + 160 < 2^63) by (split; [lia| unfold USTACK_TOP, RT_STACK in *; lia]).
apply (proj1 (rw_cells_app asegs m S _ _)) in X. destruct X as [XP XT]. clear XT.
cps_norm.

cps_seg (sbd_w1 usp lo S MP (a_low a)).
destruct POST as (m1 & j0 & xt1 & xa1 & xa2 & xa3 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
assert (RLOW1 : DREP OUTL STEREO m1 (a_low a) low LBL).
{ eapply decst_rep_agree; [exact RLOW|]. apply (agree_blocks_of_munch asegs _ m m1 LBL MU1 WM1). intros b x Hb Hx. cbn [outside]. split; [| exact I].
destruct (live_below_lo RT AF Σ m _ _ lo ART0 (LIVEL b Hb) LOW) as (_ & B1 & _). clear - B1 Hx LO32. lia. }
assert (UNW1 : unwind_ch m1 ra s0 sp).
{ apply (unwind_ch_transport [(usp + -32, usp)] m m1 ra s0 sp); [| exact MU1| exact WM1| exact UNW].
intros x Hx. cbn [disjoint_from]. fold usp in Hx. split; [lia| exact I]. }
clear RLOW UNW. unfold sbd_frame in FR1.
cps_seg_post.
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; ulc).
assert (UNWL : unwind_ch m1 (Z_to_bv 64 RA_sbd_low) (Z_to_bv 64 S) (Z_to_bv 64 (usp + -32))).
{ apply (unwind_ch_nf m1 _ _ _ lo); [rewrite unsigned_lit by (unfold RA_sbd_low; lia); unfold ALLOC_RAS, RA_sbd_low; cbn [In]; repeat (first [left; reflexivity | right])
| left; rewrite unsigned_lit by lia; lia | rewrite EU; lia]. }
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes asegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end;
[ eapply (IH Σ PMc) with (OUT := OUTL) (STEREO := STEREO) (LBD := LBL) (lo := lo); cps_auto | ].
{ rewrite EU. eassumption. }
intros cca (Σa & Hca & LVa & FRSa & SPa & CRa & POa).
destruct (ASTA_unpack RT Σa PMc _ cca Hca) as (msa & POSTa & Hca'). clear Hca. cbv beta in POSTa.
destruct POSTa as (va & ma & RSa & (ARTa & MIa & STa) & PRESa).
destruct RSa as (zt0 & zt1 & zt2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & Fa & fca & -> & -> & ->).
rewrite EU in *.

assert (KEEP : forall e, In e (rt_live RT Σ) -> ~ In (fst e) (map blk_id LBL) -> In e (rt_live RT Σa))
by (intros e He Hn; rewrite LVa; exact (live_remove_list_keep _ _ e He Hn)).
assert (INS_a : In (S, 160) (rt_live RT Σa)) by (apply KEEP; [exact INS| cbn [fst]; clear - N_S; intros X; apply N_S; do 8 right; exact X]).
assert (IN_g0_a : In (a_g0 a, 256) (rt_live RT Σa)) by (apply KEEP; [exact IN_g0| cbn [fst]; clear - N_g0; intros X; apply N_g0; do 7 right; exact X]).
assert (IN_g1_a : In (a_g1 a, 256) (rt_live RT Σa)) by (apply KEEP; [exact IN_g1| cbn [fst]; clear - N_g1; intros X; apply N_g1; do 6 right; exact X]).
assert (IN_ex_a : In (a_exc a, (4 * sbd_subframeSize s)) (rt_live RT Σa)) by (apply KEEP; [exact IN_ex| cbn [fst]; clear - N_ex; intros X; apply N_ex; do 5 right; exact X]).
assert (IN_oq_a : In (a_oq a, 32) (rt_live RT Σa)) by (apply KEEP; [exact IN_oq| cbn [fst]; clear - N_oq; intros X; apply N_oq; do 4 right; exact X]).
assert (IN_iq_a : In (a_iq a, 32) (rt_live RT Σa)) by (apply KEEP; [exact IN_iq| cbn [fst]; clear - N_iq; intros X; apply N_iq; do 3 right; exact X]).
assert (IN_pg_a : In (a_pg a, 16) (rt_live RT Σa)) by (apply KEEP; [exact IN_pg| cbn [fst]; clear - N_pg; intros X; apply N_pg; do 2 right; exact X]).
assert (IN_er_a : In (a_er a, 16) (rt_live RT Σa)) by (apply KEEP; [exact IN_er| cbn [fst]; clear - N_er; intros X; apply N_er; do 1 right; exact X]).
assert (IN_msp_a : In (a_msp a, 64) (rt_live RT Σa)) by (apply KEEP; [exact IN_msp| cbn [fst]; clear - N_msp; intros X; apply N_msp; exact X]).
clear KEEP.
assert (SUBa : forall e, In e (rt_live RT Σa) -> In e (rt_live RT Σ)) by (intros e He; rewrite LVa in He; exact (live_remove_list_sub _ _ e He)).
assert (UNWa : unwind_ch ma ra s0 sp) by (apply (unwind_ch_pres_fp _ _ (usp + -32) m1 ma ra s0 sp PRESa); [fold usp; lia| exact UNW1]).

assert (XP_a : rw_cells asegs ma S (sbptrs MP (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s)) (Z_to_bv 64 (sbd_nbSubframes s))
(Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s)) (Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 (sbd_lpc_enh_enabled s))
(Z_to_bv 64 0) (a_g0 a) (a_g1 a) (a_exc a) (a_oq a) (a_iq a) (a_msp a) (a_pg a) (a_er a))).
{ apply (rw_cells_agree_nw asegs m1 ma S _ XP). apply (agree_of_pres_fp _ _ _ _ m1 ma _ PRESa). intros x Hx. split; [| exact I].
right; right; left. exists S, 160. split; [exact INS_a|]. clear - Hx. cbn in Hx. lia. }
assert (FR_a : rw_cells asegs ma (usp + -32) [CB 8 j0; C8 s1; C8 s0; C8 ra]).
{ apply (rw_cells_agree_nw asegs m1 ma _ _ FR1). apply (agree_of_pres_fp _ _ _ _ m1 ma _ PRESa). intros x Hx. split; [| exact I].
left. clear - Hx SPT. cbn in Hx. unfold USTACK_TOP in *. lia. }
clear XP FR1 UNW1 UNWL.
assert (LOWa : rt_sp0 RT Σa - 8388608 <= lo) by (rewrite SPa; exact LOW).
assert (EF_a : rt_frames RT Σa = rt_frames RT Σ) by exact FRSa.

destruct (af_acc_live RT AF Σa ma S 160 ltac:(eassumption) INS_a) as (_ & ACS_f0).
assert (OBS_f0 : aobj asegs ma S 160) by (split; [lia|]; split; [ulc| exact ACS_f0]).
cps_seg (sbd_free_seg 0%nat usp S MP (a_low a)).
destruct POST as (xb0 & ->). cbn [sbd_ra sbd_arg] in *.
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes asegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end; [ eapply FRE with (p := a_g0 a) (n := 256); cps_auto | ].
{ cps_callok. }
{ apply (unwind_ch_nf ma _ _ _ lo); [rewrite unsigned_lit by lia; unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right]) | left; rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by ulc; lia]. }
intros cf0 (Σf0 & vf0 & Hcf0 & LV_f0 & FRS_f0 & SP_f0 & CR_f0 & PO_f0).
assert (INS_f0 : In (S, 160) (rt_live RT Σf0)) by (rewrite LV_f0; apply live_remove_keep; [exact INS_a| cbn [fst]; clear - N_S; intros E; apply N_S; rewrite E; left; reflexivity]).
assert (IN_g1_f0 : In (a_g1 a, 256) (rt_live RT Σf0)) by (rewrite LV_f0; apply live_remove_keep; [exact IN_g1_a| cbn [fst]; clear - N_g0; intros E; apply N_g0; rewrite <- E; left; reflexivity]).
assert (IN_ex_f0 : In (a_exc a, (4 * sbd_subframeSize s)) (rt_live RT Σf0)) by (rewrite LV_f0; apply live_remove_keep; [exact IN_ex_a| cbn [fst]; clear - N_g0; intros E; apply N_g0; rewrite <- E; do 1 right; left; reflexivity]).
assert (IN_oq_f0 : In (a_oq a, 32) (rt_live RT Σf0)) by (rewrite LV_f0; apply live_remove_keep; [exact IN_oq_a| cbn [fst]; clear - N_g0; intros E; apply N_g0; rewrite <- E; do 2 right; left; reflexivity]).
assert (IN_iq_f0 : In (a_iq a, 32) (rt_live RT Σf0)) by (rewrite LV_f0; apply live_remove_keep; [exact IN_iq_a| cbn [fst]; clear - N_g0; intros E; apply N_g0; rewrite <- E; do 3 right; left; reflexivity]).
assert (IN_pg_f0 : In (a_pg a, 16) (rt_live RT Σf0)) by (rewrite LV_f0; apply live_remove_keep; [exact IN_pg_a| cbn [fst]; clear - N_g0; intros E; apply N_g0; rewrite <- E; do 4 right; left; reflexivity]).
assert (IN_er_f0 : In (a_er a, 16) (rt_live RT Σf0)) by (rewrite LV_f0; apply live_remove_keep; [exact IN_er_a| cbn [fst]; clear - N_g0; intros E; apply N_g0; rewrite <- E; do 5 right; left; reflexivity]).
assert (IN_msp_f0 : In (a_msp a, 64) (rt_live RT Σf0)) by (rewrite LV_f0; apply live_remove_keep; [exact IN_msp_a| cbn [fst]; clear - N_g0; intros E; apply N_g0; rewrite <- E; do 6 right; left; reflexivity]).
assert (SUB_f0 : forall e, In e (rt_live RT Σf0) -> In e (rt_live RT Σa)) by (intros e He; rewrite LV_f0 in He; exact (live_remove_sub _ _ e He)).
assert (LOW_f0 : rt_sp0 RT Σf0 - 8388608 <= lo) by (rewrite SP_f0; assumption).
assert (EF_f0 : rt_frames RT Σf0 = rt_frames RT Σ) by (rewrite FRS_f0; exact EF_a).
cps_unpack Hcf0 as (mf0 & RS_f0 & (ART_f0 & MI_f0 & ST_f0) & PRES_f0).
assert (UNW_f0 : unwind_ch mf0 ra s0 sp) by (apply (unwind_ch_pres _ _ (usp + -32) ma mf0 ra s0 sp PRES_f0); [fold usp; lia| assumption]).
assert (XP_f0 : rw_cells asegs mf0 S (sbptrs MP (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s)) (Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s)) (Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 (sbd_lpc_enh_enabled s)) (Z_to_bv 64 0) (a_g0 a) (a_g1 a) (a_exc a) (a_oq a) (a_iq a) (a_msp a) (a_pg a) (a_er a))).
{ first [exact XP_a| apply (rw_cells_agree_nw asegs ma mf0 S _ XP_a); apply (agree_of_pres _ _ _ ma mf0 _ PRES_f0); intros x Hx; right; right; left; exists S, 160; split; [exact INS_f0|]; clear - Hx; cbn in Hx; lia]. }
assert (FR_f0 : rw_cells asegs mf0 (usp + -32) [CB 8 j0; C8 s1; C8 s0; C8 ra]).
{ first [exact FR_a| apply (rw_cells_agree_nw asegs ma mf0 _ _ FR_a); apply (agree_of_pres _ _ _ ma mf0 _ PRES_f0); intros x Hx; left; clear - Hx SPT; cbn in Hx; unfold USTACK_TOP in *; lia]. }
clear XP_a FR_a.

destruct (af_acc_live RT AF Σf0 mf0 S 160 ltac:(eassumption) INS_f0) as (_ & ACS_f1).
assert (OBS_f1 : aobj asegs mf0 S 160) by (split; [lia|]; split; [ulc| exact ACS_f1]).
cps_seg (sbd_free_seg 1%nat usp S MP (a_low a)).
destruct POST as (xb1 & ->). cbn [sbd_ra sbd_arg] in *.
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes asegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end; [ eapply FRE with (p := a_g1 a) (n := 256); cps_auto | ].
{ cps_callok. }
{ apply (unwind_ch_nf mf0 _ _ _ lo); [rewrite unsigned_lit by lia; unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right]) | left; rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by ulc; lia]. }
intros cf1 (Σf1 & vf1 & Hcf1 & LV_f1 & FRS_f1 & SP_f1 & CR_f1 & PO_f1).
assert (INS_f1 : In (S, 160) (rt_live RT Σf1)) by (rewrite LV_f1; apply live_remove_keep; [exact INS_f0| cbn [fst]; clear - N_S; intros E; apply N_S; rewrite E; do 1 right; left; reflexivity]).
assert (IN_ex_f1 : In (a_exc a, (4 * sbd_subframeSize s)) (rt_live RT Σf1)) by (rewrite LV_f1; apply live_remove_keep; [exact IN_ex_f0| cbn [fst]; clear - N_g1; intros E; apply N_g1; rewrite <- E; left; reflexivity]).
assert (IN_oq_f1 : In (a_oq a, 32) (rt_live RT Σf1)) by (rewrite LV_f1; apply live_remove_keep; [exact IN_oq_f0| cbn [fst]; clear - N_g1; intros E; apply N_g1; rewrite <- E; do 1 right; left; reflexivity]).
assert (IN_iq_f1 : In (a_iq a, 32) (rt_live RT Σf1)) by (rewrite LV_f1; apply live_remove_keep; [exact IN_iq_f0| cbn [fst]; clear - N_g1; intros E; apply N_g1; rewrite <- E; do 2 right; left; reflexivity]).
assert (IN_pg_f1 : In (a_pg a, 16) (rt_live RT Σf1)) by (rewrite LV_f1; apply live_remove_keep; [exact IN_pg_f0| cbn [fst]; clear - N_g1; intros E; apply N_g1; rewrite <- E; do 3 right; left; reflexivity]).
assert (IN_er_f1 : In (a_er a, 16) (rt_live RT Σf1)) by (rewrite LV_f1; apply live_remove_keep; [exact IN_er_f0| cbn [fst]; clear - N_g1; intros E; apply N_g1; rewrite <- E; do 4 right; left; reflexivity]).
assert (IN_msp_f1 : In (a_msp a, 64) (rt_live RT Σf1)) by (rewrite LV_f1; apply live_remove_keep; [exact IN_msp_f0| cbn [fst]; clear - N_g1; intros E; apply N_g1; rewrite <- E; do 5 right; left; reflexivity]).
assert (SUB_f1 : forall e, In e (rt_live RT Σf1) -> In e (rt_live RT Σf0)) by (intros e He; rewrite LV_f1 in He; exact (live_remove_sub _ _ e He)).
assert (LOW_f1 : rt_sp0 RT Σf1 - 8388608 <= lo) by (rewrite SP_f1; assumption).
assert (EF_f1 : rt_frames RT Σf1 = rt_frames RT Σ) by (rewrite FRS_f1; exact EF_f0).
cps_unpack Hcf1 as (mf1 & RS_f1 & (ART_f1 & MI_f1 & ST_f1) & PRES_f1).
assert (UNW_f1 : unwind_ch mf1 ra s0 sp) by (apply (unwind_ch_pres _ _ (usp + -32) mf0 mf1 ra s0 sp PRES_f1); [fold usp; lia| assumption]).
assert (XP_f1 : rw_cells asegs mf1 S (sbptrs MP (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s)) (Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s)) (Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 (sbd_lpc_enh_enabled s)) (Z_to_bv 64 0) (a_g0 a) (a_g1 a) (a_exc a) (a_oq a) (a_iq a) (a_msp a) (a_pg a) (a_er a))).
{ first [exact XP_f0| apply (rw_cells_agree_nw asegs mf0 mf1 S _ XP_f0); apply (agree_of_pres _ _ _ mf0 mf1 _ PRES_f1); intros x Hx; right; right; left; exists S, 160; split; [exact INS_f1|]; clear - Hx; cbn in Hx; lia]. }
assert (FR_f1 : rw_cells asegs mf1 (usp + -32) [CB 8 j0; C8 s1; C8 s0; C8 ra]).
{ first [exact FR_f0| apply (rw_cells_agree_nw asegs mf0 mf1 _ _ FR_f0); apply (agree_of_pres _ _ _ mf0 mf1 _ PRES_f1); intros x Hx; left; clear - Hx SPT; cbn in Hx; unfold USTACK_TOP in *; lia]. }
clear XP_f0 FR_f0.

destruct (af_acc_live RT AF Σf1 mf1 S 160 ltac:(eassumption) INS_f1) as (_ & ACS_f2).
assert (OBS_f2 : aobj asegs mf1 S 160) by (split; [lia|]; split; [ulc| exact ACS_f2]).
cps_seg (sbd_free_seg 2%nat usp S MP (a_low a)).
destruct POST as (xb2 & ->). cbn [sbd_ra sbd_arg] in *.
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes asegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end; [ eapply FRE with (p := a_exc a) (n := (4 * sbd_subframeSize s)); cps_auto | ].
{ cps_callok. }
{ apply (unwind_ch_nf mf1 _ _ _ lo); [rewrite unsigned_lit by lia; unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right]) | left; rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by ulc; lia]. }
intros cf2 (Σf2 & vf2 & Hcf2 & LV_f2 & FRS_f2 & SP_f2 & CR_f2 & PO_f2).
assert (INS_f2 : In (S, 160) (rt_live RT Σf2)) by (rewrite LV_f2; apply live_remove_keep; [exact INS_f1| cbn [fst]; clear - N_S; intros E; apply N_S; rewrite E; do 2 right; left; reflexivity]).
assert (IN_oq_f2 : In (a_oq a, 32) (rt_live RT Σf2)) by (rewrite LV_f2; apply live_remove_keep; [exact IN_oq_f1| cbn [fst]; clear - N_ex; intros E; apply N_ex; rewrite <- E; left; reflexivity]).
assert (IN_iq_f2 : In (a_iq a, 32) (rt_live RT Σf2)) by (rewrite LV_f2; apply live_remove_keep; [exact IN_iq_f1| cbn [fst]; clear - N_ex; intros E; apply N_ex; rewrite <- E; do 1 right; left; reflexivity]).
assert (IN_pg_f2 : In (a_pg a, 16) (rt_live RT Σf2)) by (rewrite LV_f2; apply live_remove_keep; [exact IN_pg_f1| cbn [fst]; clear - N_ex; intros E; apply N_ex; rewrite <- E; do 2 right; left; reflexivity]).
assert (IN_er_f2 : In (a_er a, 16) (rt_live RT Σf2)) by (rewrite LV_f2; apply live_remove_keep; [exact IN_er_f1| cbn [fst]; clear - N_ex; intros E; apply N_ex; rewrite <- E; do 3 right; left; reflexivity]).
assert (IN_msp_f2 : In (a_msp a, 64) (rt_live RT Σf2)) by (rewrite LV_f2; apply live_remove_keep; [exact IN_msp_f1| cbn [fst]; clear - N_ex; intros E; apply N_ex; rewrite <- E; do 4 right; left; reflexivity]).
assert (SUB_f2 : forall e, In e (rt_live RT Σf2) -> In e (rt_live RT Σf1)) by (intros e He; rewrite LV_f2 in He; exact (live_remove_sub _ _ e He)).
assert (LOW_f2 : rt_sp0 RT Σf2 - 8388608 <= lo) by (rewrite SP_f2; assumption).
assert (EF_f2 : rt_frames RT Σf2 = rt_frames RT Σ) by (rewrite FRS_f2; exact EF_f1).
cps_unpack Hcf2 as (mf2 & RS_f2 & (ART_f2 & MI_f2 & ST_f2) & PRES_f2).
assert (UNW_f2 : unwind_ch mf2 ra s0 sp) by (apply (unwind_ch_pres _ _ (usp + -32) mf1 mf2 ra s0 sp PRES_f2); [fold usp; lia| assumption]).
assert (XP_f2 : rw_cells asegs mf2 S (sbptrs MP (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s)) (Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s)) (Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 (sbd_lpc_enh_enabled s)) (Z_to_bv 64 0) (a_g0 a) (a_g1 a) (a_exc a) (a_oq a) (a_iq a) (a_msp a) (a_pg a) (a_er a))).
{ first [exact XP_f1| apply (rw_cells_agree_nw asegs mf1 mf2 S _ XP_f1); apply (agree_of_pres _ _ _ mf1 mf2 _ PRES_f2); intros x Hx; right; right; left; exists S, 160; split; [exact INS_f2|]; clear - Hx; cbn in Hx; lia]. }
assert (FR_f2 : rw_cells asegs mf2 (usp + -32) [CB 8 j0; C8 s1; C8 s0; C8 ra]).
{ first [exact FR_f1| apply (rw_cells_agree_nw asegs mf1 mf2 _ _ FR_f1); apply (agree_of_pres _ _ _ mf1 mf2 _ PRES_f2); intros x Hx; left; clear - Hx SPT; cbn in Hx; unfold USTACK_TOP in *; lia]. }
clear XP_f1 FR_f1.

destruct (af_acc_live RT AF Σf2 mf2 S 160 ltac:(eassumption) INS_f2) as (_ & ACS_f3).
assert (OBS_f3 : aobj asegs mf2 S 160) by (split; [lia|]; split; [ulc| exact ACS_f3]).
cps_seg (sbd_free_seg 3%nat usp S MP (a_low a)).
destruct POST as (xb3 & ->). cbn [sbd_ra sbd_arg] in *.
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes asegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end; [ eapply FRE with (p := a_oq a) (n := 32); cps_auto | ].
{ cps_callok. }
{ apply (unwind_ch_nf mf2 _ _ _ lo); [rewrite unsigned_lit by lia; unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right]) | left; rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by ulc; lia]. }
intros cf3 (Σf3 & vf3 & Hcf3 & LV_f3 & FRS_f3 & SP_f3 & CR_f3 & PO_f3).
assert (INS_f3 : In (S, 160) (rt_live RT Σf3)) by (rewrite LV_f3; apply live_remove_keep; [exact INS_f2| cbn [fst]; clear - N_S; intros E; apply N_S; rewrite E; do 3 right; left; reflexivity]).
assert (IN_iq_f3 : In (a_iq a, 32) (rt_live RT Σf3)) by (rewrite LV_f3; apply live_remove_keep; [exact IN_iq_f2| cbn [fst]; clear - N_oq; intros E; apply N_oq; rewrite <- E; left; reflexivity]).
assert (IN_pg_f3 : In (a_pg a, 16) (rt_live RT Σf3)) by (rewrite LV_f3; apply live_remove_keep; [exact IN_pg_f2| cbn [fst]; clear - N_oq; intros E; apply N_oq; rewrite <- E; do 1 right; left; reflexivity]).
assert (IN_er_f3 : In (a_er a, 16) (rt_live RT Σf3)) by (rewrite LV_f3; apply live_remove_keep; [exact IN_er_f2| cbn [fst]; clear - N_oq; intros E; apply N_oq; rewrite <- E; do 2 right; left; reflexivity]).
assert (IN_msp_f3 : In (a_msp a, 64) (rt_live RT Σf3)) by (rewrite LV_f3; apply live_remove_keep; [exact IN_msp_f2| cbn [fst]; clear - N_oq; intros E; apply N_oq; rewrite <- E; do 3 right; left; reflexivity]).
assert (SUB_f3 : forall e, In e (rt_live RT Σf3) -> In e (rt_live RT Σf2)) by (intros e He; rewrite LV_f3 in He; exact (live_remove_sub _ _ e He)).
assert (LOW_f3 : rt_sp0 RT Σf3 - 8388608 <= lo) by (rewrite SP_f3; assumption).
assert (EF_f3 : rt_frames RT Σf3 = rt_frames RT Σ) by (rewrite FRS_f3; exact EF_f2).
cps_unpack Hcf3 as (mf3 & RS_f3 & (ART_f3 & MI_f3 & ST_f3) & PRES_f3).
assert (UNW_f3 : unwind_ch mf3 ra s0 sp) by (apply (unwind_ch_pres _ _ (usp + -32) mf2 mf3 ra s0 sp PRES_f3); [fold usp; lia| assumption]).
assert (XP_f3 : rw_cells asegs mf3 S (sbptrs MP (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s)) (Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s)) (Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 (sbd_lpc_enh_enabled s)) (Z_to_bv 64 0) (a_g0 a) (a_g1 a) (a_exc a) (a_oq a) (a_iq a) (a_msp a) (a_pg a) (a_er a))).
{ first [exact XP_f2| apply (rw_cells_agree_nw asegs mf2 mf3 S _ XP_f2); apply (agree_of_pres _ _ _ mf2 mf3 _ PRES_f3); intros x Hx; right; right; left; exists S, 160; split; [exact INS_f3|]; clear - Hx; cbn in Hx; lia]. }
assert (FR_f3 : rw_cells asegs mf3 (usp + -32) [CB 8 j0; C8 s1; C8 s0; C8 ra]).
{ first [exact FR_f2| apply (rw_cells_agree_nw asegs mf2 mf3 _ _ FR_f2); apply (agree_of_pres _ _ _ mf2 mf3 _ PRES_f3); intros x Hx; left; clear - Hx SPT; cbn in Hx; unfold USTACK_TOP in *; lia]. }
clear XP_f2 FR_f2.

destruct (af_acc_live RT AF Σf3 mf3 S 160 ltac:(eassumption) INS_f3) as (_ & ACS_f4).
assert (OBS_f4 : aobj asegs mf3 S 160) by (split; [lia|]; split; [ulc| exact ACS_f4]).
cps_seg (sbd_free_seg 4%nat usp S MP (a_low a)).
destruct POST as (xb4 & ->). cbn [sbd_ra sbd_arg] in *.
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes asegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end; [ eapply FRE with (p := a_iq a) (n := 32); cps_auto | ].
{ cps_callok. }
{ apply (unwind_ch_nf mf3 _ _ _ lo); [rewrite unsigned_lit by lia; unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right]) | left; rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by ulc; lia]. }
intros cf4 (Σf4 & vf4 & Hcf4 & LV_f4 & FRS_f4 & SP_f4 & CR_f4 & PO_f4).
assert (INS_f4 : In (S, 160) (rt_live RT Σf4)) by (rewrite LV_f4; apply live_remove_keep; [exact INS_f3| cbn [fst]; clear - N_S; intros E; apply N_S; rewrite E; do 4 right; left; reflexivity]).
assert (IN_pg_f4 : In (a_pg a, 16) (rt_live RT Σf4)) by (rewrite LV_f4; apply live_remove_keep; [exact IN_pg_f3| cbn [fst]; clear - N_iq; intros E; apply N_iq; rewrite <- E; left; reflexivity]).
assert (IN_er_f4 : In (a_er a, 16) (rt_live RT Σf4)) by (rewrite LV_f4; apply live_remove_keep; [exact IN_er_f3| cbn [fst]; clear - N_iq; intros E; apply N_iq; rewrite <- E; do 1 right; left; reflexivity]).
assert (IN_msp_f4 : In (a_msp a, 64) (rt_live RT Σf4)) by (rewrite LV_f4; apply live_remove_keep; [exact IN_msp_f3| cbn [fst]; clear - N_iq; intros E; apply N_iq; rewrite <- E; do 2 right; left; reflexivity]).
assert (SUB_f4 : forall e, In e (rt_live RT Σf4) -> In e (rt_live RT Σf3)) by (intros e He; rewrite LV_f4 in He; exact (live_remove_sub _ _ e He)).
assert (LOW_f4 : rt_sp0 RT Σf4 - 8388608 <= lo) by (rewrite SP_f4; assumption).
assert (EF_f4 : rt_frames RT Σf4 = rt_frames RT Σ) by (rewrite FRS_f4; exact EF_f3).
cps_unpack Hcf4 as (mf4 & RS_f4 & (ART_f4 & MI_f4 & ST_f4) & PRES_f4).
assert (UNW_f4 : unwind_ch mf4 ra s0 sp) by (apply (unwind_ch_pres _ _ (usp + -32) mf3 mf4 ra s0 sp PRES_f4); [fold usp; lia| assumption]).
assert (XP_f4 : rw_cells asegs mf4 S (sbptrs MP (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s)) (Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s)) (Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 (sbd_lpc_enh_enabled s)) (Z_to_bv 64 0) (a_g0 a) (a_g1 a) (a_exc a) (a_oq a) (a_iq a) (a_msp a) (a_pg a) (a_er a))).
{ first [exact XP_f3| apply (rw_cells_agree_nw asegs mf3 mf4 S _ XP_f3); apply (agree_of_pres _ _ _ mf3 mf4 _ PRES_f4); intros x Hx; right; right; left; exists S, 160; split; [exact INS_f4|]; clear - Hx; cbn in Hx; lia]. }
assert (FR_f4 : rw_cells asegs mf4 (usp + -32) [CB 8 j0; C8 s1; C8 s0; C8 ra]).
{ first [exact FR_f3| apply (rw_cells_agree_nw asegs mf3 mf4 _ _ FR_f3); apply (agree_of_pres _ _ _ mf3 mf4 _ PRES_f4); intros x Hx; left; clear - Hx SPT; cbn in Hx; unfold USTACK_TOP in *; lia]. }
clear XP_f3 FR_f3.

destruct (af_acc_live RT AF Σf4 mf4 S 160 ltac:(eassumption) INS_f4) as (_ & ACS_f5).
assert (OBS_f5 : aobj asegs mf4 S 160) by (split; [lia|]; split; [ulc| exact ACS_f5]).
cps_seg (sbd_free_seg 5%nat usp S MP (a_low a)).
destruct POST as (xb5 & ->). cbn [sbd_ra sbd_arg] in *.
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes asegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end; [ eapply FRE with (p := a_pg a) (n := 16); cps_auto | ].
{ cps_callok. }
{ apply (unwind_ch_nf mf4 _ _ _ lo); [rewrite unsigned_lit by lia; unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right]) | left; rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by ulc; lia]. }
intros cf5 (Σf5 & vf5 & Hcf5 & LV_f5 & FRS_f5 & SP_f5 & CR_f5 & PO_f5).
assert (INS_f5 : In (S, 160) (rt_live RT Σf5)) by (rewrite LV_f5; apply live_remove_keep; [exact INS_f4| cbn [fst]; clear - N_S; intros E; apply N_S; rewrite E; do 5 right; left; reflexivity]).
assert (IN_er_f5 : In (a_er a, 16) (rt_live RT Σf5)) by (rewrite LV_f5; apply live_remove_keep; [exact IN_er_f4| cbn [fst]; clear - N_pg; intros E; apply N_pg; rewrite <- E; left; reflexivity]).
assert (IN_msp_f5 : In (a_msp a, 64) (rt_live RT Σf5)) by (rewrite LV_f5; apply live_remove_keep; [exact IN_msp_f4| cbn [fst]; clear - N_pg; intros E; apply N_pg; rewrite <- E; do 1 right; left; reflexivity]).
assert (SUB_f5 : forall e, In e (rt_live RT Σf5) -> In e (rt_live RT Σf4)) by (intros e He; rewrite LV_f5 in He; exact (live_remove_sub _ _ e He)).
assert (LOW_f5 : rt_sp0 RT Σf5 - 8388608 <= lo) by (rewrite SP_f5; assumption).
assert (EF_f5 : rt_frames RT Σf5 = rt_frames RT Σ) by (rewrite FRS_f5; exact EF_f4).
cps_unpack Hcf5 as (mf5 & RS_f5 & (ART_f5 & MI_f5 & ST_f5) & PRES_f5).
assert (UNW_f5 : unwind_ch mf5 ra s0 sp) by (apply (unwind_ch_pres _ _ (usp + -32) mf4 mf5 ra s0 sp PRES_f5); [fold usp; lia| assumption]).
assert (XP_f5 : rw_cells asegs mf5 S (sbptrs MP (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s)) (Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s)) (Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 (sbd_lpc_enh_enabled s)) (Z_to_bv 64 0) (a_g0 a) (a_g1 a) (a_exc a) (a_oq a) (a_iq a) (a_msp a) (a_pg a) (a_er a))).
{ first [exact XP_f4| apply (rw_cells_agree_nw asegs mf4 mf5 S _ XP_f4); apply (agree_of_pres _ _ _ mf4 mf5 _ PRES_f5); intros x Hx; right; right; left; exists S, 160; split; [exact INS_f5|]; clear - Hx; cbn in Hx; lia]. }
assert (FR_f5 : rw_cells asegs mf5 (usp + -32) [CB 8 j0; C8 s1; C8 s0; C8 ra]).
{ first [exact FR_f4| apply (rw_cells_agree_nw asegs mf4 mf5 _ _ FR_f4); apply (agree_of_pres _ _ _ mf4 mf5 _ PRES_f5); intros x Hx; left; clear - Hx SPT; cbn in Hx; unfold USTACK_TOP in *; lia]. }
clear XP_f4 FR_f4.

destruct (af_acc_live RT AF Σf5 mf5 S 160 ltac:(eassumption) INS_f5) as (_ & ACS_f6).
assert (OBS_f6 : aobj asegs mf5 S 160) by (split; [lia|]; split; [ulc| exact ACS_f6]).
cps_seg (sbd_free_seg 6%nat usp S MP (a_low a)).
destruct POST as (xb6 & ->). cbn [sbd_ra sbd_arg] in *.
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes asegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end; [ eapply FRE with (p := a_er a) (n := 16); cps_auto | ].
{ cps_callok. }
{ apply (unwind_ch_nf mf5 _ _ _ lo); [rewrite unsigned_lit by lia; unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right]) | left; rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by ulc; lia]. }
intros cf6 (Σf6 & vf6 & Hcf6 & LV_f6 & FRS_f6 & SP_f6 & CR_f6 & PO_f6).
assert (INS_f6 : In (S, 160) (rt_live RT Σf6)) by (rewrite LV_f6; apply live_remove_keep; [exact INS_f5| cbn [fst]; clear - N_S; intros E; apply N_S; rewrite E; do 6 right; left; reflexivity]).
assert (IN_msp_f6 : In (a_msp a, 64) (rt_live RT Σf6)) by (rewrite LV_f6; apply live_remove_keep; [exact IN_msp_f5| cbn [fst]; clear - N_er; intros E; apply N_er; rewrite <- E; left; reflexivity]).
assert (SUB_f6 : forall e, In e (rt_live RT Σf6) -> In e (rt_live RT Σf5)) by (intros e He; rewrite LV_f6 in He; exact (live_remove_sub _ _ e He)).
assert (LOW_f6 : rt_sp0 RT Σf6 - 8388608 <= lo) by (rewrite SP_f6; assumption).
assert (EF_f6 : rt_frames RT Σf6 = rt_frames RT Σ) by (rewrite FRS_f6; exact EF_f5).
cps_unpack Hcf6 as (mf6 & RS_f6 & (ART_f6 & MI_f6 & ST_f6) & PRES_f6).
assert (UNW_f6 : unwind_ch mf6 ra s0 sp) by (apply (unwind_ch_pres _ _ (usp + -32) mf5 mf6 ra s0 sp PRES_f6); [fold usp; lia| assumption]).
assert (XP_f6 : rw_cells asegs mf6 S (sbptrs MP (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s)) (Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s)) (Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 (sbd_lpc_enh_enabled s)) (Z_to_bv 64 0) (a_g0 a) (a_g1 a) (a_exc a) (a_oq a) (a_iq a) (a_msp a) (a_pg a) (a_er a))).
{ first [exact XP_f5| apply (rw_cells_agree_nw asegs mf5 mf6 S _ XP_f5); apply (agree_of_pres _ _ _ mf5 mf6 _ PRES_f6); intros x Hx; right; right; left; exists S, 160; split; [exact INS_f6|]; clear - Hx; cbn in Hx; lia]. }
assert (FR_f6 : rw_cells asegs mf6 (usp + -32) [CB 8 j0; C8 s1; C8 s0; C8 ra]).
{ first [exact FR_f5| apply (rw_cells_agree_nw asegs mf5 mf6 _ _ FR_f5); apply (agree_of_pres _ _ _ mf5 mf6 _ PRES_f6); intros x Hx; left; clear - Hx SPT; cbn in Hx; unfold USTACK_TOP in *; lia]. }
clear XP_f5 FR_f5.

destruct (af_acc_live RT AF Σf6 mf6 S 160 ltac:(eassumption) INS_f6) as (_ & ACS_f7).
assert (OBS_f7 : aobj asegs mf6 S 160) by (split; [lia|]; split; [ulc| exact ACS_f7]).
cps_seg (sbd_free_seg 7%nat usp S MP (a_low a)).
destruct POST as (xb7 & ->). cbn [sbd_ra sbd_arg] in *.
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes asegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end; [ eapply FRE with (p := a_msp a) (n := 64); cps_auto | ].
{ cps_callok. }
{ apply (unwind_ch_nf mf6 _ _ _ lo); [rewrite unsigned_lit by lia; unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right]) | left; rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by ulc; lia]. }
intros cf7 (Σf7 & vf7 & Hcf7 & LV_f7 & FRS_f7 & SP_f7 & CR_f7 & PO_f7).
assert (INS_f7 : In (S, 160) (rt_live RT Σf7)) by (rewrite LV_f7; apply live_remove_keep; [exact INS_f6| cbn [fst]; clear - N_S; intros E; apply N_S; rewrite E; do 7 right; left; reflexivity]).
assert (SUB_f7 : forall e, In e (rt_live RT Σf7) -> In e (rt_live RT Σf6)) by (intros e He; rewrite LV_f7 in He; exact (live_remove_sub _ _ e He)).
assert (LOW_f7 : rt_sp0 RT Σf7 - 8388608 <= lo) by (rewrite SP_f7; assumption).
assert (EF_f7 : rt_frames RT Σf7 = rt_frames RT Σ) by (rewrite FRS_f7; exact EF_f6).
cps_unpack Hcf7 as (mf7 & RS_f7 & (ART_f7 & MI_f7 & ST_f7) & PRES_f7).
assert (UNW_f7 : unwind_ch mf7 ra s0 sp) by (apply (unwind_ch_pres _ _ (usp + -32) mf6 mf7 ra s0 sp PRES_f7); [fold usp; lia| assumption]).
assert (XP_f7 : rw_cells asegs mf7 S (sbptrs MP (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s)) (Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s)) (Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 (sbd_lpc_enh_enabled s)) (Z_to_bv 64 0) (a_g0 a) (a_g1 a) (a_exc a) (a_oq a) (a_iq a) (a_msp a) (a_pg a) (a_er a))).
{ first [exact XP_f6| apply (rw_cells_agree_nw asegs mf6 mf7 S _ XP_f6); apply (agree_of_pres _ _ _ mf6 mf7 _ PRES_f7); intros x Hx; right; right; left; exists S, 160; split; [exact INS_f7|]; clear - Hx; cbn in Hx; lia]. }
assert (FR_f7 : rw_cells asegs mf7 (usp + -32) [CB 8 j0; C8 s1; C8 s0; C8 ra]).
{ first [exact FR_f6| apply (rw_cells_agree_nw asegs mf6 mf7 _ _ FR_f6); apply (agree_of_pres _ _ _ mf6 mf7 _ PRES_f7); intros x Hx; left; clear - Hx SPT; cbn in Hx; unfold USTACK_TOP in *; lia]. }
clear XP_f6 FR_f6.

cps_seg (sbd_last usp lo S).
destruct POST as (-> & STL).
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes asegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end; [ eapply FRE with (p := S) (n := 160); cps_auto | ].
{ cps_callok. } { rewrite <- ESP. exact UNW_f7. }
intros cfl (Σl & vl & Hcl & LVl & FRSl & SPl & CRl & POl).
cps_unpack Hcl as (ml & RSl & (ARTl & MIl & STl) & PRESl).
apply Hk. exists Σl. split.
- eapply ASTA_conseq; [eassumption|]. intros ms <-. exists vl, ml.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split; [exact (conj ARTl (conj MIl STl))|].
intros x Hx _.
assert (C7 : aclient (rt_live RT Σf7) (rt_frames RT Σ) (usp + -32) (bv_unsigned x)).
{ apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; rewrite LVl in He; exact (live_remove_sub _ _ e He)| auto| lia]. }
assert (C6 : aclient (rt_live RT Σf6) (rt_frames RT Σ) (usp + -32) (bv_unsigned x)) by (apply (aclient_mono _ _ _ _ _ _ _ C7); [exact SUB_f7| auto| lia]).
assert (C5 : aclient (rt_live RT Σf5) (rt_frames RT Σ) (usp + -32) (bv_unsigned x)) by (apply (aclient_mono _ _ _ _ _ _ _ C6); [exact SUB_f6| auto| lia]).
assert (C4 : aclient (rt_live RT Σf4) (rt_frames RT Σ) (usp + -32) (bv_unsigned x)) by (apply (aclient_mono _ _ _ _ _ _ _ C5); [exact SUB_f5| auto| lia]).
assert (C3 : aclient (rt_live RT Σf3) (rt_frames RT Σ) (usp + -32) (bv_unsigned x)) by (apply (aclient_mono _ _ _ _ _ _ _ C4); [exact SUB_f4| auto| lia]).
assert (C2 : aclient (rt_live RT Σf2) (rt_frames RT Σ) (usp + -32) (bv_unsigned x)) by (apply (aclient_mono _ _ _ _ _ _ _ C3); [exact SUB_f3| auto| lia]).
assert (C1 : aclient (rt_live RT Σf1) (rt_frames RT Σ) (usp + -32) (bv_unsigned x)) by (apply (aclient_mono _ _ _ _ _ _ _ C2); [exact SUB_f2| auto| lia]).
assert (C0 : aclient (rt_live RT Σf0) (rt_frames RT Σ) (usp + -32) (bv_unsigned x)) by (apply (aclient_mono _ _ _ _ _ _ _ C1); [exact SUB_f1| auto| lia]).
assert (Ca : aclient (rt_live RT Σa) (rt_frames RT Σ) (usp + -32) (bv_unsigned x)) by (apply (aclient_mono _ _ _ _ _ _ _ C0); [exact SUB_f0| auto| lia]).
assert (C00 : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x)).
{ apply (aclient_mono _ _ _ _ _ _ _ Hx); [| auto| lia]. intros e He. apply SUBa. apply SUB_f0. apply SUB_f1. apply SUB_f2. apply SUB_f3. apply SUB_f4. apply SUB_f5. apply SUB_f6. apply SUB_f7.
rewrite LVl in He. exact (live_remove_sub _ _ e He). }
rewrite (PRESl x); [| rewrite EF_f7; exact Hx].
rewrite (PRES_f7 x); [| rewrite EF_f6; exact C7].
rewrite (PRES_f6 x); [| rewrite EF_f5; exact C6].
rewrite (PRES_f5 x); [| rewrite EF_f4; exact C5].
rewrite (PRES_f4 x); [| rewrite EF_f3; exact C4].
rewrite (PRES_f3 x); [| rewrite EF_f2; exact C3].
rewrite (PRES_f2 x); [| rewrite EF_f1; exact C2].
rewrite (PRES_f1 x); [| rewrite EF_f0; exact C1].
rewrite (PRES_f0 x); [| rewrite EF_a; exact C0].
rewrite (PRESa x); [| exact Ca | exact I].
apply MU1. cbn [outside]. split; [| exact I]. clear - SPL C00 LOW LOR DSP. specialize (SPL _ C00). lia.
- split; [| split; [rewrite FRSl; exact EF_f7|]; repeat split; congruence].
rewrite LVl, LV_f7, LV_f6, LV_f5, LV_f4, LV_f3, LV_f2, LV_f1, LV_f0, LVa.
rewrite <- !live_remove_list_snoc.
apply live_remove_list_perm. rewrite map_app. cbn [sb_blocks map blk_addr fst snd].
repeat rewrite <- app_assoc. cbn [app].
eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app].
apply Permutation_sym. exact (Permutation_middle [a_g0 a; a_g1 a; a_exc a; a_oq a; a_iq a; a_pg a; a_er a; a_msp a] (map blk_addr LBL) S).
Qed.

Theorem destroy_cps_all : forall d, destroy_cps_at d.
Proof using AF FRE AF_LIB.
induction d as [st|s low IH]; [exact (destroy_cps_nb st)| exact (destroy_cps_sb s low IH)].
Qed.

End DestroyCPS.
