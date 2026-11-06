(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1ck X1cv.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j5 X0ec X001 X00b X000 X04b X07z X05o.
From stdpp Require list_basics.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19o X14x X0r0 X0ra X0qz X0v9.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Rz.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Lemma PMc_mat_stable' : forall Σ PMc, mat_stable PMc -> mat_stable (fun mo => ARTM RT Σ mo /\ PMc mo).
Proof using AF. intros Σ PMc H. apply mat_stable_and; [exact (af_mat_stable RT AF Σ)| exact H]. Qed.

Lemma rz_evt : forall Σ PMc (ms : machine_state) (Q : machine_state -> Prop) T c,
mat_stable PMc -> ASTA RT Σ PMc (eq ms) c -> evt bsegs Q ms ->
(forall ms' c', Q ms' -> ASTA RT Σ PMc (eq ms') c' -> realizes bsegs c' T) -> realizes bsegs c T.
Proof using AF.
intros Σ PMc ms Q T c MST Hc W K.
assert (CP : cps bsegs (ASTA RT Σ PMc (eq ms)) (ASTA RT Σ PMc Q)).
{ unfold ASTA. apply (ast_evt bsegs SEGTOP_A asegs_wx asegs_below); [apply PMc_mat_stable'; exact MST|]. intros ms0 <-. exact W. }
apply (cps_realizes bsegs _ _ T c CP Hc). intros c1 Hc1.
destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & Q1 & Hc1'). exact (K ms1 c1 Q1 Hc1').
Qed.

Lemma rz_cps : forall Σ PMc (ms : machine_state) (Q : config -> Prop) T c,
ASTA RT Σ PMc (eq ms) c -> cps bsegs (ASTA RT Σ PMc (eq ms)) Q ->
(forall c', Q c' -> realizes bsegs c' T) -> realizes bsegs c T.
Proof. intros Σ PMc ms Q T c Hc CP K. exact (cps_realizes bsegs _ _ T c CP Hc K). Qed.

Lemma rz_cpsE : forall Σ PMc (ms : machine_state) evs (Q : config -> Prop) T c,
ASTA RT Σ PMc (eq ms) c -> cpsE bsegs (ASTA RT Σ PMc (eq ms)) evs Q ->
(forall c', Q c' -> realizes bsegs c' T) -> realizes bsegs c (t_emit evs T).
Proof. intros Σ PMc ms evs Q T c Hc CP K. exact (CP T c Hc K). Qed.

End Rz.

Lemma shad_inside : forall f fsz a n, f mod 8 = 0 -> a mod 8 = 0 -> fsz mod 8 = 0 -> n mod 8 = 0 -> 0 <= f -> f <= a -> a + n <= f + fsz -> 0 <= n ->
shad f <= shad a /\ shad a + n / 8 <= shad f + fsz / 8.
Proof. intros f fsz a n F8 A8 S8 N8 F0 H1 H2 N0. unfold shad. Z.div_mod_to_equations. lia. Qed.

Lemma uw_chain_transport : forall TOPB W (m m' : mem) ras f fp,
(forall a, f <= a -> disjoint_from W a 16) -> munch W m m' -> wmono bsegs m m' ->
uw_chain TOPB m f fp ras -> uw_chain TOPB m' f fp ras.
Proof.
intros TOPB W m m'. induction ras as [|r ras IH]; intros f fp DJ MU WM H; cbn [uw_chain] in *; [exact H|].
destruct H as (H1 & H2 & H3 & fp' & H4 & H5 & H6).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. exists fp'. split; [exact H4|]. split.
- apply (rw_cells_transport bsegs W m m' _ _ H5 MU WM). cbn [cells_size csize Nat.add]. apply DJ. lia.
- apply (IH fp fp'); [intros a Ha; apply DJ; lia| exact MU| exact WM| exact H6].
Qed.
Lemma unwind_ch_transport : forall W (m m' : mem) ra s0 sp,
(forall a, bv_unsigned sp <= a -> disjoint_from W a 16) -> munch W m m' -> wmono bsegs m m' ->
unwind_ch m ra s0 sp -> unwind_ch m' ra s0 sp.
Proof.
intros W m m' ra s0 sp DJ MU WM (ras & H1 & H2). exists ras. split; [exact H1|].
exact (uw_chain_transport USTACK_TOP W m m' ras _ _ DJ MU WM H2).
Qed.

Section PresFp.
Variable RT : rt_sig.

Lemma aclient_mono : forall live frames sp live' frames' sp' a,
aclient live frames sp a -> (forall e, In e live -> In e live') -> (forall e, In e frames -> In e frames') -> sp' <= sp ->
aclient live' frames' sp' a.
Proof.
intros live frames sp live' frames' sp' a H HL HF Hsp. destruct H as [H|[H|[H|[H|H]]]].
- left. lia.
- right; left. exact H.
- right; right; left. destruct H as (p & n & Hin & Hp). exists p, n. split; [apply HL; exact Hin| exact Hp].
- right; right; right; left. destruct H as (f & k & Hin & Hf). exists f, k. split; [apply HF; exact Hin| exact Hf].
- right; right; right; right. destruct H as (f & k & Hin & Hf). exists f, k. split; [apply HF; exact Hin| exact Hf].
Qed.

Lemma pres_fp_refl : forall live frames sp W m, rt_pres_fp live frames sp W m m.
Proof. intros live frames sp W m a _ _. reflexivity. Qed.
Lemma pres_fp_trans : forall live frames sp W m1 m2 m3,
rt_pres_fp live frames sp W m1 m2 -> rt_pres_fp live frames sp W m2 m3 -> rt_pres_fp live frames sp W m1 m3.
Proof. intros live frames sp W m1 m2 m3 H1 H2 a Ha Ho. rewrite (H2 a Ha Ho). exact (H1 a Ha Ho). Qed.
Lemma pres_fp_of_pres : forall live frames sp W m m', rt_pres live frames sp m m' -> rt_pres_fp live frames sp W m m'.
Proof. intros live frames sp W m m' H a Ha _. exact (H a Ha). Qed.
Lemma pres_fp_weaken : forall live frames sp W W' m m', rt_pres_fp live frames sp W m m' -> (forall x, outside W' x -> outside W x) ->
rt_pres_fp live frames sp W' m m'.
Proof. intros live frames sp W W' m m' H HW a Ha Ho. exact (H a Ha (HW _ Ho)). Qed.
Lemma pres_fp_mono : forall live frames sp live' frames' sp' W m m',
rt_pres_fp live' frames' sp' W m m' -> (forall e, In e live -> In e live') -> (forall e, In e frames -> In e frames') -> sp' <= sp ->
rt_pres_fp live frames sp W m m'.
Proof.
intros live frames sp live' frames' sp' W m m' H HL HF Hsp a Ha Ho. apply H; [| exact Ho].
exact (aclient_mono live frames sp live' frames' sp' _ Ha HL HF Hsp).
Qed.
Lemma pres_fp_of_munch : forall live frames sp W W' m m', munch W' m m' ->
(forall x, aclient live frames sp x -> outside W x -> outside W' x) -> rt_pres_fp live frames sp W m m'.
Proof. intros live frames sp W W' m m' MU H a Ha Ho. apply MU. exact (H _ Ha Ho). Qed.
Lemma pres_fp_of_ex : forall live frames sp d n W m m', rt_pres_ex live frames sp d n m m' ->
(forall x, d <= x < d + n -> ~ outside W x) -> rt_pres_fp live frames sp W m m'.
Proof. intros live frames sp d n W m m' H HW a Ha Ho. apply H; [exact Ha|]. intros Hd. exact (HW _ Hd Ho). Qed.

Lemma pres_fp_of_pres_ex_gen : forall live frames sp W live' frames' sp' d n m m',
rt_pres_ex live' frames' sp' d n m m' -> (forall e, In e live -> In e live') -> (forall e, In e frames -> In e frames') -> sp' <= sp ->
(forall x, aclient live frames sp x -> outside W x -> ~ (d <= x < d + n)) -> rt_pres_fp live frames sp W m m'.
Proof.
intros live frames sp W live' frames' sp' d n m m' H HL HF Hsp HW a Ha Ho. apply H; [| exact (HW _ Ha Ho)].
exact (aclient_mono live frames sp live' frames' sp' _ Ha HL HF Hsp).
Qed.

Lemma pres_fp_of_pres_fp : forall live frames sp W live' frames' sp' W' m m',
rt_pres_fp live' frames' sp' W' m m' -> (forall e, In e live -> In e live') -> (forall e, In e frames -> In e frames') -> sp' <= sp ->
(forall x, aclient live frames sp x -> outside W x -> outside W' x) -> rt_pres_fp live frames sp W m m'.
Proof.
intros live frames sp W live' frames' sp' W' m m' H HL HF Hsp HW a Ha Ho. apply H; [| exact (HW _ Ha Ho)].
exact (aclient_mono live frames sp live' frames' sp' _ Ha HL HF Hsp).
Qed.

Lemma live_remove_sub : forall (l : list (Z * Z)) p e, In e (live_remove p l) -> In e l.
Proof.
intros l p e He. unfold live_remove in He. apply stdpp.base.list_elem_of_In in He.
apply stdpp.list_basics.list.list_elem_of_filter in He. apply stdpp.base.list_elem_of_In. exact (proj2 He).
Qed.
Lemma live_remove_keep : forall (l : list (Z * Z)) p e, In e l -> fst e <> p -> In e (live_remove p l).
Proof.
intros l p e He Hp. unfold live_remove. apply stdpp.base.list_elem_of_In. apply stdpp.list_basics.list.list_elem_of_filter.
split; [| apply stdpp.base.list_elem_of_In; exact He]. apply Z.eqb_neq in Hp. rewrite Hp. exact I.
Qed.
End PresFp.

Section Frames.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma ASTA_switch : forall (Σ Σ' : rts RT) PMc Pm c, ASTA RT Σ PMc Pm c -> rt_allow RT Σ' = rt_allow RT Σ ->
(forall mo, ARTM RT Σ mo -> ARTM RT Σ' mo) -> ASTA RT Σ' PMc Pm c.
Proof.
intros Σ Σ' PMc Pm c H HA HM. unfold ASTA in *. rewrite HA.
eapply AST_conseq; [exact H| auto|]. intros mo [H1 H2]. split; [apply HM; exact H1| exact H2].
Qed.

Lemma newframe_apart : forall (Σ Σ1 : rts RT) (m1 : mem) Fr k usp a,
ART RT Σ1 m1 -> rt_frames RT Σ1 = (Fr, k) :: rt_frames RT Σ -> rt_live RT Σ1 = rt_live RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ ->
rt_sp0 RT Σ - STACK_WIN <= usp -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp a ->
~ (Fr <= a < Fr + fs_size k) /\ ~ (shad Fr <= a < shad (Fr + fs_size k)).
Proof using AF.
intros Σ Σ1 m1 Fr k usp a ART1 FRS LV SP0 LU Ha.
assert (INF : In (Fr, k) (rt_frames RT Σ1)) by (rewrite FRS; left; reflexivity).
pose proof (af_frames_range RT AF Σ1 m1 Fr k ART1 INF) as (R0 & R1 & R2 & R3).
pose proof (af_fshadow_apart RT AF Σ1 m1 Fr k ART1 INF) as (SL & SF).
pose proof (af_sp0_range RT AF Σ1 m1 ART1) as SPR. pose proof (af_sp0_win RT AF Σ1 m1 ART1) as SPW.
rewrite SP0 in R1, SPR, SPW.
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (SH1 : shad (Fr + fs_size k) <= 2^44 + SHB).
{ unfold shad. assert ((Fr + fs_size k) / 8 <= 2^44) by (apply Z.div_le_upper_bound; ul). lia. }
assert (SH0 : SHB <= shad Fr) by (unfold shad; assert (0 <= Fr / 8) by (apply Z.div_pos; lia); lia).
assert (SHM : shad Fr <= shad (Fr + fs_size k)) by (unfold shad; pose proof (Z.div_le_mono Fr (Fr + fs_size k) 8 ltac:(lia) ltac:(lia)); lia).
destruct Ha as [H|[H|[H|[H|H]]]].
- split; unfold SHB in *; ul.
- pose proof (client_static_range a H). split; [destruct R2; unfold SEGTOP_A in *; lia|]. unfold SHB, SEGTOP_A in *. lia.
- destruct H as (p & n & Hin & Hp). rewrite <- LV in Hin. destruct (R3 p n Hin); destruct (SL p n Hin); split; lia.
- destruct H as (f & k' & Hin & Hf).
destruct (af_frames_disj RT AF Σ1 m1 Fr k f k' [] (rt_frames RT Σ) ART1 FRS Hin) as [D|D];
(destruct (SF f k' ltac:(rewrite FRS; right; exact Hin)) as [E|E]); split; lia.
- destruct H as (f & k' & Hin & Hf).
assert (INf : In (f, k') (rt_frames RT Σ1)) by (rewrite FRS; right; exact Hin).
pose proof (af_fshadow_apart RT AF Σ1 m1 f k' ART1 INf) as (_ & SF').
destruct (af_frames_disj RT AF Σ1 m1 Fr k f k' [] (rt_frames RT Σ) ART1 FRS Hin) as [D|D].
+ pose proof (Z.div_le_mono (Fr + fs_size k) f 8 ltac:(lia) D). destruct (SF' Fr k INF) as [E|E]; split; unfold shad in *; lia.
+ assert (FSZ' : 0 <= fs_size k') by (unfold fs_size; apply Z.shiftl_nonneg; lia).
pose proof (Z.div_le_mono (f + fs_size k') Fr 8 ltac:(lia) D). destruct (SF' Fr k INF) as [E|E]; split; unfold shad in *; lia.
Qed.

Lemma frame_facts : forall (Σ : rts RT) (m : mem) f k, ART RT Σ m -> In (f, k) (rt_frames RT Σ) ->
0 < f /\ f mod 64 = 0 /\ SEGTOP_A <= f /\ f + fs_size k <= rt_sp0 RT Σ - STACK_WIN
/\ (f + fs_size k <= 0x7fff7000 \/ 0x10007fff8000 <= f)
/\ Z.shiftr f 3 + SHB = shad f /\ shad (f + fs_size k) = shad f + fs_size k / 8
/\ SH_LO <= shad f /\ shad f + fs_size k / 8 <= SH_HI
/\ (f + fs_size k <= shad f \/ shad f + fs_size k / 8 <= f).
Proof using AF.
intros Σ m f k ART0 INF.
pose proof (af_fshadow_apart RT AF Σ m f k ART0 INF) as (_ & SELF). specialize (SELF f k INF).
pose proof (af_frames_range RT AF Σ m f k ART0 INF) as (R0 & R1 & _).
pose proof (af_frames_align RT AF Σ m f k ART0 INF) as (A64 & AIMG).
pose proof (af_frames_hi RT AF Σ m f k ART0 INF) as HI.
pose proof (af_sp0_range RT AF Σ m ART0) as SPR.
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (SA : shad (f + fs_size k) = shad f + fs_size k / 8) by (apply shad_aligned_add; [clear - A64; Z.div_mod_to_equations; lia| exact FSZ]).
split; [exact R0|]. split; [exact A64|]. split; [exact AIMG|]. split; [exact R1|]. split; [exact HI|].
split; [apply shad_shiftr|]. split; [exact SA|].
rewrite <- SA. split; [| split; [| exact SELF]]; unfold shad, SHB, SH_LO, SH_HI.
- assert (0 <= f / 8) by (apply Z.div_pos; lia). lia.
- assert ((f + fs_size k) / 8 <= 2^44) by (apply Z.div_le_upper_bound; ul). lia.
Qed.

Lemma frame_live_apart : forall (Σ : rts RT) (m : mem) f k p n, ART RT Σ m -> In (f, k) (rt_frames RT Σ) -> In (p, n) (rt_live RT Σ) ->
(f + fs_size k <= p \/ p + n <= f) /\ (p + n <= shad f \/ shad (f + fs_size k) <= p).
Proof using AF.
intros Σ m f k p n ART0 INF INL.
pose proof (af_frames_range RT AF Σ m f k ART0 INF) as (_ & _ & _ & R3).
pose proof (af_fshadow_apart RT AF Σ m f k ART0 INF) as (SL & _).
split; [exact (R3 p n INL)| exact (SL p n INL)].
Qed.

Lemma live_facts : forall (Σ : rts RT) (m : mem) p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) ->
0 < p /\ p + n <= rt_sp0 RT Σ - STACK_WIN /\ (p + n <= 0x10000 \/ SEGTOP_A <= p) /\ (p + n <= 0x7fff7000 \/ 0x10007fff8000 <= p).
Proof using AF.
intros Σ m p n ART0 INL. pose proof (af_live_range RT AF Σ m p n ART0 INL) as (L0 & L1 & L2).
pose proof (af_live_offshadow RT AF Σ m p n ART0 INL) as L3. tauto.
Qed.

Lemma aclient_split : forall (Σ : rts RT) (m : mem) usp a, ART RT Σ m -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp a ->
usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN.
Proof using AF.
intros Σ m usp a ART0 [H|[H|[H|[H|H]]]].
- left; lia.
- right. pose proof (client_static_range a H). pose proof (af_sp0_range RT AF Σ m ART0). ul.
- right. destruct H as (p & n & Hin & Hp). pose proof (af_live_range RT AF Σ m p n ART0 Hin). lia.
- right. destruct H as (f & k & Hin & Hf). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & H2 & _).
unfold fs_size in *. pose proof (Z.shiftl_nonneg 64 (Z.of_nat k)) as E. lia.
- right. destruct H as (f & k & Hin & Hf). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & H2 & _).
pose proof (af_sp0_range RT AF Σ m ART0). pose proof (af_sp0_win RT AF Σ m ART0).
unfold shad, SHB in Hf. unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *. Z.div_mod_to_equations. lia.
Qed.

Lemma flag_not_client : forall (Σ Σ1 : rts RT) f k usp fl a,
rt_frames RT Σ1 = (f, k) :: rt_frames RT Σ -> rt_live RT Σ1 = rt_live RT Σ ->
~ aclient (rt_live RT Σ1) (rt_frames RT Σ1) USTACK_TOP fl -> fl < usp ->
aclient (rt_live RT Σ) (rt_frames RT Σ) usp a -> a <> fl.
Proof.
intros Σ Σ1 f k usp fl a FRS LV NAC FLU Ha E. subst a. apply NAC. rewrite LV, FRS.
destruct Ha as [H|[H|[H|[H|H]]]]; [lia| right; left; exact H| right; right; left; exact H|
right; right; right; left; destruct H as (f' & k' & Hin & Hf); exists f', k'; split; [right; exact Hin| exact Hf]|
right; right; right; right; destruct H as (f' & k' & Hin & Hf); exists f', k'; split; [right; exact Hin| exact Hf]].
Qed.

Lemma frame_below_lo : forall (Σ : rts RT) (m : mem) f k lo, ART RT Σ m -> In (f, k) (rt_frames RT Σ) -> rt_sp0 RT Σ - STACK_WIN <= lo ->
f + fs_size k <= lo /\ shad f + fs_size k / 8 <= lo /\ SH_HI <= lo.
Proof using AF.
intros Σ m f k lo ART0 INF LOW. pose proof (frame_facts Σ m f k ART0 INF) as (_ & _ & _ & R1 & _ & _ & _ & _ & S1 & _).
pose proof (af_sp0_win RT AF Σ m ART0) as SPW. unfold SH_HI, STACK_WIN in *. lia.
Qed.
Lemma live_below_lo : forall (Σ : rts RT) (m : mem) p n lo, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> rt_sp0 RT Σ - STACK_WIN <= lo ->
0 < p /\ p + n <= lo /\ SH_HI <= lo.
Proof using AF.
intros Σ m p n lo ART0 INL LOW. pose proof (af_live_range RT AF Σ m p n ART0 INL) as (L0 & L1 & _).
pose proof (af_sp0_win RT AF Σ m ART0) as SPW. unfold SH_HI, STACK_WIN in *. lia.
Qed.

Lemma aobj_lit : forall (Σ : rts RT) (m : mem) a n, ART RT Σ m -> In (a, n) ACC_LITS -> 0 <= a -> a + n <= APP_TOP -> aobj bsegs m a n.
Proof using AF.
intros Σ m a n ART0 IN A0 A1. split; [exact A0|]. split; [exact A1|].
pose proof (af_acc_lits RT AF Σ m ART0) as AL. rewrite Forall_forall in AL. exact (AL (a, n) IN).
Qed.

Lemma newchunk_apart_gen : forall (Σ Σ1 : rts RT) (m1 : mem) p n L usp a,
ART RT Σ1 m1 -> rt_live RT Σ1 = (p, n) :: L -> rt_frames RT Σ1 = rt_frames RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ ->
rt_sp0 RT Σ - STACK_WIN <= usp -> 0 <= n -> aclient L (rt_frames RT Σ) usp a -> ~ (p <= a < p + n).
Proof using AF.
intros Σ Σ1 m1 p n L usp a ART1 LV FRS SP0 LU N0 Ha Hin.
assert (INL : In (p, n) (rt_live RT Σ1)) by (rewrite LV; left; reflexivity).
pose proof (af_live_range RT AF Σ1 m1 p n ART1 INL) as (L0 & L1 & L2). rewrite SP0 in L1.
destruct Ha as [H|[H|[H|[H|H]]]].
- lia.
- pose proof (client_static_range a H). unfold SEGTOP_A in *. lia.
- destruct H as (p' & n' & Hin' & Hp').
destruct (af_live_disj RT AF Σ1 m1 p n p' n' [] L ART1 LV Hin'); lia.
- destruct H as (f & k & Hinf & Hf). rewrite <- FRS in Hinf.
pose proof (af_frames_range RT AF Σ1 m1 f k ART1 Hinf) as (_ & _ & _ & R3). destruct (R3 p n INL); lia.
- destruct H as (f & k & Hinf & Hf). rewrite <- FRS in Hinf.
pose proof (af_fshadow_apart RT AF Σ1 m1 f k ART1 Hinf) as (SL & _). destruct (SL p n INL); lia.
Qed.
Lemma newchunk_apart : forall (Σ Σ1 : rts RT) (m1 : mem) p n usp a,
ART RT Σ1 m1 -> rt_live RT Σ1 = (p, n) :: rt_live RT Σ -> rt_frames RT Σ1 = rt_frames RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ ->
rt_sp0 RT Σ - STACK_WIN <= usp -> 0 <= n -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp a -> ~ (p <= a < p + n).
Proof using AF. intros Σ Σ1 m1 p n usp a. exact (newchunk_apart_gen Σ Σ1 m1 p n (rt_live RT Σ) usp a). Qed.

Lemma live_remove_apart : forall (Σ : rts RT) (m : mem) D n p2 n2, ART RT Σ m -> In (D, n) (rt_live RT Σ) ->
In (p2, n2) (live_remove D (rt_live RT Σ)) -> D + n <= p2 \/ p2 + n2 <= D.
Proof using AF.
intros Σ m D n p2 n2 ART0 IN INR.
assert (NE : p2 <> D).
{ unfold live_remove in INR. apply stdpp.base.list_elem_of_In in INR. apply stdpp.list_basics.list.list_elem_of_filter in INR.
destruct INR as [PR _]. cbn [fst] in PR. destruct (Z.eqb_spec p2 D) as [E|NE]; [destruct PR| exact NE]. }
pose proof (live_remove_sub _ _ _ INR) as IN2.
destruct (in_split _ _ IN) as (l1 & l2 & E). rewrite E in IN2.
apply (af_live_disj RT AF Σ m D n p2 n2 l1 l2 ART0 E).
apply in_app_or in IN2. apply in_or_app. destruct IN2 as [H|[H|H]]; [left; exact H| injection H as H1 _; congruence| right; exact H].
Qed.
Lemma aclient_remove_apart : forall (Σ : rts RT) (m : mem) D n usp a, ART RT Σ m -> In (D, n) (rt_live RT Σ) ->
rt_sp0 RT Σ - STACK_WIN <= usp -> aclient (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) usp a -> ~ (D <= a < D + n).
Proof using AF.
intros Σ m D n usp a ART0 IN LU Ha Hin.
pose proof (af_live_range RT AF Σ m D n ART0 IN) as (L0 & L1 & L2).
destruct Ha as [H|[H|[H|[H|H]]]].
- lia.
- pose proof (client_static_range a H). unfold SEGTOP_A in *. lia.
- destruct H as (p' & n' & Hin' & Hp'). destruct (live_remove_apart Σ m D n p' n' ART0 IN Hin'); lia.
- destruct H as (f & k & Hinf & Hf). pose proof (af_frames_range RT AF Σ m f k ART0 Hinf) as (_ & _ & _ & R3). destruct (R3 D n IN); lia.
- destruct H as (f & k & Hinf & Hf). pose proof (af_fshadow_apart RT AF Σ m f k ART0 Hinf) as (SL & _). destruct (SL D n IN); lia.
Qed.
End Frames.

Lemma outside_img : forall (W : list (Z * Z)) x, (forall y, in_ranges W y -> client_static y) -> (x < 0x10000 \/ SEGTOP_A <= x) -> outside W x.
Proof.
intros W x HW Hx. apply outside_of_not_in_ranges'. intros Hin. pose proof (client_static_range x (HW x Hin)). lia.
Qed.

Lemma u8arr_rw_CB : forall (m : mem) A bs, u8arr bsegs m A bs <-> rw_cells bsegs m A [CB (length bs) bs].
Proof.
intros m A bs. unfold u8arr, rw_cells, cells_at. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize]. rewrite app_nil_r, Nat.add_0_r. tauto.
Qed.

Lemma rw_cells_to_CB : forall segs (m : mem) A cs, rw_cells segs m A cs -> rw_cells segs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
intros segs m A cs H. apply (rw_cells_recast segs m A cs); [exact H| | cbn [cells_bytes cbytes]; apply app_nil_r].
split; [| exact I]. destruct H as [[Hwf _] _]. exact (cells_bytes_length cs Hwf).
Qed.

Lemma fp_local_munch : forall (W : list (Z * Z)) (P : mem -> Prop) Wm (m m' : mem),
fp_local W P -> (forall y, in_ranges W y -> client_static y) -> munch Wm m m' ->
(forall x, 0x10000 <= x < SEGTOP_A -> outside Wm x) -> P m -> P m'.
Proof. intros W P Wm m m' L IMG MU OUT Pm. apply (L m m' Pm). intros a Ha. apply MU. apply OUT. exact (client_static_range _ (IMG _ Ha)). Qed.
Lemma fp_local_pres : forall (W : list (Z * Z)) (P : mem -> Prop) live frames sp (m m' : mem),
fp_local W P -> (forall y, in_ranges W y -> client_static y) -> rt_pres live frames sp m m' -> P m -> P m'.
Proof. intros W P live frames sp m m' L IMG PRES Pm. apply (L m m' Pm). intros a Ha. apply PRES. right; left. exact (IMG _ Ha). Qed.

Definition ret_stL (P : bvmap 5 word -> bv 32 -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (m' : mem)
(ms : machine_state) : Prop :=
exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32),
ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom bsegs) /\ P F' fc'.

Ltac cps_unf := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SH_HI, SH_LO, APP_TOP, IMG_TOP in *.
Ltac cps_norm := cps_unf.

Ltac cps_hide := hide_disj.
Ltac cps_unhide := unhide_disj.
Ltac arith_goal :=
lazymatch goal with
| |- (_ <= _)%Z => idtac | |- (_ < _)%Z => idtac | |- (_ <= _ < _)%Z => idtac | |- (_ <= _ <= _)%Z => idtac | |- (_ < _ <= _)%Z => idtac | |- (_ < _ < _)%Z => idtac
| |- @eq Z _ _ => idtac | |- _ \/ _ => idtac | |- ~ _ => idtac | |- False => idtac | |- _ /\ _ => idtac | |- (_ >= _)%Z => idtac | |- (_ > _)%Z => idtac
| |- _ <> _ => idtac
end.
Ltac with_hid tac := arith_goal; match goal with H : hid ?P |- _ => let U := fresh "U" in pose proof (H : P) as U; tac end.
Ltac ulq0 := idtac; first [ llia | cps_unf; llia ].
Ltac ulc0 := idtac; first [ llia | cps_unf; first [ llia | cllia ] ].
Ltac ulq := idtac; first [ llia | cps_unf; first [ llia | with_hid ltac:(llia) ] ].
Ltac ulc := idtac; first [ llia | cps_unf; first [ llia | cllia | with_hid ltac:(llia) | with_hid ltac:(cllia) ] ].

Ltac cps_sizes Hx :=
rewrite ?cells_size_app, ?cells_size_f32 in Hx;
cbn in Hx.

Ltac fs_lit := repeat match goal with |- context [fs_size ?k] =>
let v := eval vm_compute in (fs_size k) in
lazymatch v with Zpos _ => change (fs_size k) with v end
end.
Ltac aclient_cls tac :=
lazymatch goal with
| |- aclient ?L ?Fr _ _ =>
first
[ left; tac
| right; right; left; match goal with H : In (?p, ?n) L |- _ => exists p, n; split; [exact H | tac] end
| right; right; right; left; match goal with H : In (?f, ?k) Fr |- _ => exists f, k; split; [exact H | fs_lit; tac] end
| right; right; right; right; match goal with H : In (?f, ?k) Fr |- _ => exists f, k; split; [exact H | fs_lit; tac] end ]
end.

Ltac aclient_tac tac := first [ aclient_cls ltac:(ulq0) | aclient_cls ltac:(ulc0) ].

Ltac pres_outside tac :=
cbn [outside];
repeat lazymatch goal with |- _ /\ _ => split end;
first [ exact I
| lazymatch goal with
| |- outside ?W _ => match goal with IMG : forall y, in_ranges W y -> client_static y |- _ => apply (outside_img W _ IMG); tac end
end
| tac ].
Ltac pres_agree PRES tac :=
lazymatch type of PRES with
| rt_pres ?live ?frames ?sp ?m ?m' =>
apply (agree_of_pres live frames sp m m' _ PRES); intros ? ?Hx; cps_sizes Hx; aclient_tac tac
| rt_pres_fp ?live ?frames ?sp ?W ?m ?m' =>
apply (agree_of_pres_fp live frames sp W m m' _ PRES); intros ? ?Hx; cps_sizes Hx; split; [ aclient_tac tac | pres_outside tac ]
| rt_pres_ex ?live ?frames ?sp ?d ?n ?m ?m' =>
apply (agree_of_pres_ex live frames sp d n m m' _ PRES); intros ? ?Hx; cps_sizes Hx; split; [ aclient_tac tac | tac ]
end.
Ltac pres_mems PRES k :=
lazymatch type of PRES with
| rt_pres _ _ _ ?m ?m' => k m m'
| rt_pres_fp _ _ _ _ ?m ?m' => k m m'
| rt_pres_ex _ _ _ _ _ ?m ?m' => k m m'
end.
Ltac pres_transport_g PRES tac :=
pres_mems PRES ltac:(fun m m' =>
repeat match goal with
| H : rw_cells bsegs m ?A ?cs |- _ =>
first [ let H' := fresh "T" in
assert (H' : rw_cells bsegs m' A cs)
by (first [ match goal with WM : wmono bsegs m m' |- _ => apply (rw_cells_agree bsegs m m' A cs H); [ pres_agree PRES tac | exact WM ] end
| apply (rw_cells_agree_nw bsegs m m' A cs H); pres_agree PRES tac ]);
clear H; rename H' into H
| idtac "note: dropping hypothesis (not client memory for this call):" H; clear H ]
| H : ro_cells bsegs m ?A ?cs |- _ =>
first [ let H' := fresh "T" in
assert (H' : ro_cells bsegs m' A cs) by (apply (ro_cells_agree bsegs m m' A cs H); pres_agree PRES tac);
clear H; rename H' into H
| idtac "note: dropping hypothesis (not client memory for this call):" H; clear H ]
| H : bytes_at bsegs m ?A ?bs |- _ =>
first [ let H' := fresh "T" in
assert (H' : bytes_at bsegs m' A bs) by (apply (bytes_at_agree bsegs m m' A bs H); pres_agree PRES tac);
clear H; rename H' into H
| idtac "note: dropping hypothesis (not client memory for this call):" H; clear H ]
end).
Ltac pres_transport PRES WM tac := pres_transport_g PRES tac.

Ltac seg_lia := first [ exact I | repeat (split; [ulq|]); first [exact I | ulq] ].
Ltac seg_transport m m' MU WM :=
let W := lazymatch type of MU with munch ?W _ _ => W end in
repeat match goal with
| H : bytes_at bsegs m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_transport bsegs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; seg_lia ]
| idtac "note: dropping hypothesis (not provably disjoint from the segment's footprint):" H; clear H ]
| H : rw_cells bsegs m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_transport bsegs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; seg_lia ]
| idtac "note: dropping hypothesis (not provably disjoint from the segment's footprint):" H; clear H ]
| H : ro_cells bsegs m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_transport bsegs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; seg_lia ]
| idtac "note: dropping hypothesis (not provably disjoint from the segment's footprint):" H; clear H ]
| H : stk bsegs m ?loq ?hiq |- _ =>
first [ apply (stk_transport_disjoint bsegs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; seg_lia ]
| clear H ]
end.

Ltac cps_auto := try reflexivity; try eassumption; try ulq.

Tactic Notation "cps_seg" uconstr(LEM) :=
lazymatch goal with
| Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes bsegs ?c ?T =>
refine (rz_evt RT ltac:(eassumption) Σ PMc ms _ T c ltac:(eassumption) Hc _ _);
[ eapply LEM; cps_auto
| let ms' := fresh "ms" in let c' := fresh "c" in let Hc' := fresh "Hc" in
intros ms' c' POST Hc'; cbv beta in POST; clear Hc ]
end.

Tactic Notation "cps_rt" uconstr(CON) :=
lazymatch goal with
| Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes bsegs ?c ?T =>
refine (rz_cps RT Σ PMc ms _ T c Hc _ _); [ eapply CON; cps_auto | ]
end.

Tactic Notation "cps_rtE" uconstr(CON) :=
lazymatch goal with
| Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes bsegs ?c (t_emit ?evs ?T) =>
refine (rz_cpsE RT Σ PMc ms evs _ T c Hc _ _); [ eapply CON; cps_auto | ]
end.

Tactic Notation "cps_rt_sized" uconstr(CON) constr(n) :=
lazymatch goal with
| Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes bsegs ?c ?T =>
refine (rz_cps RT Σ PMc ms _ T c Hc _ _); [ eapply CON with (size := n); cps_auto | ]
end.

Ltac cps_callok :=
unfold call_ok; rewrite unsigned_lit by ulc;
split; [eassumption|]; split; [ulc|]; split; [ulc|]; split; [ulc|];
first [ ulq | match goal with H : _ mod 32 = 0 |- _ => clear - H; Z.div_mod_to_equations; lia end ].

Ltac cps_ret_exs RS :=
let T := type of RS in let T' := eval hnf in T in
lazymatch T' with
| ex _ => let x := fresh "r" in destruct RS as [x RS]; cps_ret_exs RS
| _ => idtac
end.
Ltac cps_ret RS :=
cps_ret_exs RS;
lazymatch type of RS with
| ?v = _ => subst v
| ?v = _ /\ _ => let E := fresh "E" in destruct RS as [E RS]; subst v
end.

Ltac cps_pf_seg m m' MU :=
lazymatch goal with
| PF : rt_pres_fp ?L0 ?F0 ?U0 ?W0 ?m0 m |- _ =>
let PF' := fresh "PF" in
assert (PF' : rt_pres_fp L0 F0 U0 W0 m0 m')
by (apply (pres_fp_trans L0 F0 U0 W0 m0 m m' PF); apply (pres_fp_of_munch L0 F0 U0 W0 _ m m' MU);
let x := fresh "x" in let Hx := fresh "Hx" in let Ho := fresh "Ho" in
intros x Hx Ho; cbn [outside] in Ho |- *;
repeat match goal with NA : forall a, aclient L0 F0 U0 a -> _ |- _ => pose proof (NA x Hx); clear NA end;
decompose [and] Ho;
repeat split; ulc);
clear PF; rename PF' into PF
| _ => idtac
end.

Ltac cps_seg_post_with MU WM A LO :=
lazymatch type of MU with
| munch ?W ?m ?m' =>
lazymatch type of A with
| ART ?RT ?Σ m =>
lazymatch type of LO with
| _ <= ?lo =>
let A' := fresh "ART" in
assert (A' : ART RT Σ m')
by (apply (af_frame RT ltac:(eassumption) Σ m m' lo A LO); [| exact WM];
let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; apply MU; cbn [outside]; repeat split; intros ?Hin; apply Ha; aclient_tac ltac:(ulc));
cps_pf_seg m m' MU;
clear A; seg_transport m m' MU WM;
try match goal with MI : mem_inv bsegs m |- _ => clear MI end
end
end
end.

Ltac cps_seg_post :=
match goal with
| MU : munch ?W ?m ?m', WM : wmono bsegs ?m ?m', A : ART ?RT ?Σ ?m |- _ =>
first
[ match goal with ST : stk bsegs m' ?lo _, LO : rt_sp0 RT Σ - _ <= ?lo |- _ => cps_seg_post_with MU WM A LO end
| match goal with ST : stk bsegs m ?lo _, LO : rt_sp0 RT Σ - _ <= ?lo |- _ => cps_seg_post_with MU WM A LO end
| match goal with LO : rt_sp0 RT Σ - _ <= _ |- _ => cps_seg_post_with MU WM A LO end ]
end.

Ltac cps_incl :=
first [ now auto
| apply live_remove_sub
| intros ? ?Hi; first [ exact (live_remove_sub _ _ _ Hi)
| repeat match goal with E : _ = _ |- _ => rewrite E end; auto with datatypes ] ].
Ltac cps_pf_pres PRES :=
let m := lazymatch type of PRES with rt_pres _ _ _ ?m _ => m | rt_pres_fp _ _ _ _ ?m _ => m | rt_pres_ex _ _ _ _ _ ?m _ => m end in
lazymatch goal with
| PF : rt_pres_fp ?L0 ?F0 ?U0 ?W0 ?m0 m |- _ =>
lazymatch type of PRES with
| rt_pres ?live ?frames ?sp m ?m' =>
let PF' := fresh "PF" in
assert (PF' : rt_pres_fp L0 F0 U0 W0 m0 m')
by (apply (pres_fp_trans L0 F0 U0 W0 m0 m m' PF);
apply (pres_fp_mono L0 F0 U0 live frames sp W0 m m' (pres_fp_of_pres live frames sp W0 m m' PRES));
[ cps_incl
| cps_incl
| ulc ]);
clear PF; rename PF' into PF
| rt_pres_fp ?live ?frames ?sp ?W m ?m' =>

let PF' := fresh "PF" in
assert (PF' : rt_pres_fp L0 F0 U0 W0 m0 m')
by (apply (pres_fp_trans L0 F0 U0 W0 m0 m m' PF);
apply (pres_fp_of_pres_fp L0 F0 U0 W0 live frames sp W m m' PRES);
[ cps_incl
| cps_incl
| ulc
| let x := fresh "x" in let Hx := fresh "Hx" in let Ho := fresh "Ho" in
intros x Hx Ho; cbn [outside] in Ho; first [ exact Ho | tauto ] ]);
clear PF; rename PF' into PF
| rt_pres_ex ?live ?frames ?sp ?d ?n m ?m' =>

let PF' := fresh "PF" in
assert (PF' : rt_pres_fp L0 F0 U0 W0 m0 m')
by (apply (pres_fp_trans L0 F0 U0 W0 m0 m m' PF);
apply (pres_fp_of_pres_ex_gen L0 F0 U0 W0 live frames sp d n m m' PRES);
[ cps_incl | cps_incl | ulc
| let x := fresh "x" in let Hx := fresh "Hx" in let Ho := fresh "Ho" in
intros x Hx Ho; cbn [outside] in Ho;
repeat match goal with NA : forall a, aclient L0 F0 U0 a -> _ |- _ => pose proof (NA x Hx); clear NA end;
decompose [and] Ho; ulc ]);
clear PF; rename PF' into PF
| _ => idtac
end
| _ => idtac
end.

Ltac cps_unpack_tr PRES m :=
pres_transport_g PRES ltac:(ulc); cps_pf_pres PRES;
try match goal with A : ART _ _ m |- _ => clear A end;
try match goal with MI : mem_inv bsegs m |- _ => clear MI end;
try match goal with ST : stk bsegs m _ _ |- _ => clear ST end.

Tactic Notation "cps_unpack" hyp(Hc) "as" simple_intropattern(P) :=
try unfold icpt_postF in Hc;
lazymatch type of Hc with
| ASTA ?RT ?Σ' ?PMc ?Pm ?c =>
let ms := fresh "ms" in let Hc' := fresh "Hc" in let PO := fresh "PO" in
destruct (ASTA_unpack RT Σ' PMc Pm c Hc) as (ms & PO & Hc'); clear Hc; cbv beta in PO;
destruct PO as P;
repeat match goal with
| RS : ret_stF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => cps_ret RS
| RS : ret_stR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => cps_ret RS
| RS : ret_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => cps_ret RS
end;
repeat match goal with
| H : context [bv_unsigned (Z_to_bv 64 ?z)] |- _ =>
lazymatch type of H with bv_unsigned (Z_to_bv 64 _) = _ => fail | _ => idtac end;
rewrite (unsigned_lit z) in H by ulc
end;
first
[
let m' := lazymatch type of Hc' with ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _)) _ => mm end in
match goal with
| PRES : rt_pres _ _ _ ?m m' |- _ => cps_unpack_tr PRES m
| PRES : rt_pres_fp _ _ _ _ ?m m' |- _ => cps_unpack_tr PRES m
| PRES : rt_pres_ex _ _ _ _ _ ?m m' |- _ => cps_unpack_tr PRES m
end
| match goal with
| PRES : rt_pres _ _ _ ?m ?m', WM : wmono bsegs ?m ?m' |- _ => cps_unpack_tr PRES m
end
| idtac "note: cps_unpack: no preservation fact found in this post: transport the chunks you still need by hand (D_kit.*_agree*)" ]
end.

Ltac cps_sigma EL EF ES :=
lazymatch type of ES with
| rt_sp0 ?RT ?Σ' = rt_sp0 ?RT ?Σ =>
lazymatch type of EL with
| rt_live RT Σ' = ?e :: rt_live RT Σ =>
repeat match goal with
| H : In ?e0 (rt_live RT Σ) |- _ =>
let H' := fresh H in assert (H' : In e0 (rt_live RT Σ')) by (rewrite EL; right; exact H); clear H; rename H' into H
end;
let INL := fresh "INL" in assert (INL : In e (rt_live RT Σ')) by (rewrite EL; left; reflexivity)
| rt_live RT Σ' = ?e :: live_remove ?p (rt_live RT Σ) =>

repeat match goal with
| H : In ?e0 (rt_live RT Σ) |- _ =>
first [ let H' := fresh H in
assert (H' : In e0 (rt_live RT Σ'))
by (rewrite EL; right; apply (live_remove_keep _ p e0 H); cbn [fst]; first [ assumption | congruence | ulq ]);
clear H; rename H' into H
| clear H ]
end;
let INL := fresh "INL" in assert (INL : In e (rt_live RT Σ')) by (rewrite EL; left; reflexivity)
| rt_live RT Σ' = rt_live RT Σ =>
repeat match goal with H : In ?e0 (rt_live RT Σ) |- _ => rewrite <- EL in H end
end;
repeat match goal with
| H : rt_sp0 RT Σ - _ <= _ |- _ => rewrite <- ES in H
end;
try (match goal with EP : rt_pois RT Σ' = rt_pois RT Σ |- _ =>
repeat match goal with
| H : pois_above (rt_pois RT Σ) _ |- _ => rewrite <- EP in H
| H : pois_apart (rt_pois RT Σ) _ _ |- _ => rewrite <- EP in H
end end);
lazymatch type of EF with
| rt_frames RT Σ' = ?e :: rt_frames RT Σ =>
repeat match goal with
| H : In ?e0 (rt_frames RT Σ) |- _ =>
let H' := fresh H in assert (H' : In e0 (rt_frames RT Σ')) by (rewrite EF; right; exact H); clear H; rename H' into H
end;
let INF := fresh "INF" in assert (INF : In e (rt_frames RT Σ')) by (rewrite EF; left; reflexivity)
| rt_frames RT Σ' = rt_frames RT Σ =>
repeat match goal with H : In ?e0 (rt_frames RT Σ) |- _ => rewrite <- EF in H end
end
end.

Ltac cps_wmono :=
lazymatch goal with
| |- wmono bsegs ?m ?m => apply wmono_refl
| |- wmono bsegs ?m0 ?m =>
first [ eassumption
| match goal with W : wmono bsegs ?m1 m |- _ => apply (wmono_trans bsegs m0 m1 m); [ cps_wmono | exact W ] end ]
end.

Ltac cps_new_frame ART2 EF EL ES WRF WRS sf :=
lazymatch type of EF with
| rt_frames ?RT ?Σ1 = (?f, ?k) :: rt_frames ?RT ?Σ =>
lazymatch type of ART2 with
| ART RT Σ1 ?m2 =>
let fsz := eval vm_compute in (fs_size k) in
let fsz8 := eval vm_compute in (fs_size k / 8) in
let fszb := eval vm_compute in (fs_size k - 8) in
let NAF := fresh "NAF" in
lazymatch goal with
| PF : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) ?U0 _ _ _ |- _ =>
pose proof (fun a (Ha : aclient (rt_live RT Σ) (rt_frames RT Σ) U0 a) =>
newframe_apart RT ltac:(eassumption) Σ Σ1 m2 f k U0 a ART2 EF EL ES ltac:(ulc) Ha) as NAF
| _ => idtac
end;
cps_sigma EL EF ES;
match goal with
| INF : In (f, k) (rt_frames RT Σ1), LO : rt_sp0 RT Σ1 - _ <= ?lo |- _ =>
let BF1 := fresh "BF" in let BF2 := fresh "BF" in
destruct (frame_below_lo RT ltac:(eassumption) Σ1 m2 f k lo ART2 INF LO) as (BF1 & BF2 & _);
let F0 := fresh "F0" in let F64 := fresh "F64" in let FIMG := fresh "FIMG" in let FHI := fresh "FHI" in
let S0 := fresh "SHF" in let S1 := fresh "SHF" in let S2 := fresh "SHF" in let S3 := fresh "SHF" in let S4 := fresh "SHF" in
pose proof (frame_facts RT ltac:(eassumption) Σ1 m2 f k ART2 INF) as (F0 & F64 & FIMG & _ & FHI & S0 & S1 & S2 & S3 & S4);
repeat match goal with
| INL : In (?p, ?n) (rt_live RT Σ1) |- _ =>
lazymatch goal with
| _ : (f + fs_size k <= p \/ p + n <= f) |- _ => fail
| _ : (f + fsz <= p \/ p + n <= f) |- _ => fail
| _ => let A1 := fresh "FLA" in let A2 := fresh "FLA" in
destruct (frame_live_apart RT ltac:(eassumption) Σ1 m2 f k p n ART2 INF INL) as (A1 & A2)
end
end;
set (sf := Z.shiftr f 3 + SHB) in *;
let Esf := fresh "Esf" in assert (Esf : sf = Z.shiftr f 3 + SHB) by reflexivity;
change (fs_size k) with fsz in *; change (fsz - 8) with fszb in *; change (fsz / 8) with fsz8 in *;
rewrite S1 in *; rewrite <- S0 in *;
let jF := fresh "jF" in let jS := fresh "jS" in let FRB := fresh "FRB" in let FRS := fresh "FRS" in
destruct (wr_at_rw_CB m2 f fszb WRF ltac:(lia)) as (jF & FRB);
destruct (wr_at_rw_CB m2 sf fsz8 WRS ltac:(lia)) as (jS & FRS);
let nb := eval vm_compute in (Z.to_nat fszb) in change (Z.to_nat fszb) with nb in FRB;
let n8 := eval vm_compute in (Z.to_nat fsz8) in change (Z.to_nat fsz8) with n8 in FRS;
clear WRF WRS; cps_norm
end
end
end.

Ltac cps_release_intro ARTc EF EL PREL Σ2 fl :=
lazymatch type of EF with
| rt_frames ?RT ?Σ1 = (?f, ?k) :: ?fr =>
lazymatch type of ARTc with
| ART RT Σ1 ?m =>
let fszb := eval vm_compute in (fs_size k - 8) in
let FLC := fresh "FLC" in let NAC := fresh "NAC" in let FL0 := fresh "FL0" in let FLW := fresh "FLW" in let FW := fresh "FW" in
let REL := fresh "REL" in
destruct (af_frame_release RT ltac:(eassumption) Σ1 m f k fr ARTc EF PREL) as (Σ2 & fl & FLC & NAC & FL0 & FLW & FW & REL);
change (fs_size k - 8) with fszb in FW; replace (f + fs_size k - 8) with (f + fszb) in FW by (change (fs_size k) with (fszb + 8); lia);
match goal with LO : rt_sp0 RT Σ1 - _ <= ?lo |- _ => let B := fresh "BFL" in assert (B : fl + 1 <= lo) by ulc end;
cps_norm;
lazymatch goal with
| PF : rt_pres_fp (rt_live RT ?Σ) (rt_frames RT ?Σ) ?U0 _ _ _ |- _ =>
let NFL := fresh "NFL" in
pose proof (fun a (Ha : aclient (rt_live RT Σ) (rt_frames RT Σ) U0 a) =>
flag_not_client RT Σ Σ1 f k U0 fl a EF EL NAC ltac:(ulc) Ha) as NFL
| _ => idtac
end
end
end.

Ltac cps_release_done REL MU WM FLG :=
lazymatch type of MU with
| munch _ ?m ?m' =>
let A := fresh "ART" in let EF := fresh "EF" in let EL := fresh "EL" in let ES := fresh "ES" in let EC := fresh "EC" in
let AL := fresh "AL" in let AM := fresh "AM" in let EP := fresh "EP" in
destruct (REL m' MU WM FLG) as (A & EF & EL & ES & EC & AL & AM & EP);
cps_pf_seg m m' MU;
try match goal with A0 : ART _ _ m |- _ => clear A0 end;
lazymatch type of MU with munch [(?fl, _)] _ _ =>
repeat match goal with
| H : rw_cells bsegs m fl _ |- _ => clear H
| H : ro_cells bsegs m _ [C8 (Z_to_bv 64 fl)] |- _ => clear H
end
end;
seg_transport m m' MU WM;
lazymatch goal with
| Hc : ASTA ?RT ?Σ1 ?PMc ?Pm ?c |- _ =>
let Hc' := fresh "Hc" in
lazymatch type of A with ART RT ?Σ2 _ => pose proof (ASTA_switch RT Σ1 Σ2 PMc Pm c Hc AL AM) as Hc' end; clear Hc
end
end.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Rz.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Lemma PMc_mat_stable' : forall Σ PMc, mat_stable PMc -> mat_stable (fun mo => ARTM RT Σ mo /\ PMc mo).
Proof using AF. intros Σ PMc H. apply mat_stable_and; [exact (af_mat_stable RT AF Σ)| exact H]. Qed.

Lemma rz_evt : forall Σ PMc (ms : machine_state) (Q : machine_state -> Prop) T c,
mat_stable PMc -> ASTA RT Σ PMc (eq ms) c -> evt asegs Q ms ->
(forall ms' c', Q ms' -> ASTA RT Σ PMc (eq ms') c' -> realizes asegs c' T) -> realizes asegs c T.
Proof using AF.
intros Σ PMc ms Q T c MST Hc W K.
assert (CP : cps asegs (ASTA RT Σ PMc (eq ms)) (ASTA RT Σ PMc Q)).
{ unfold ASTA. apply (ast_evt asegs SEGTOP_A asegs_wx asegs_below); [apply PMc_mat_stable'; exact MST|]. intros ms0 <-. exact W. }
apply (cps_realizes asegs _ _ T c CP Hc). intros c1 Hc1.
destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & Q1 & Hc1'). exact (K ms1 c1 Q1 Hc1').
Qed.

Lemma rz_cps : forall Σ PMc (ms : machine_state) (Q : config -> Prop) T c,
ASTA RT Σ PMc (eq ms) c -> cps asegs (ASTA RT Σ PMc (eq ms)) Q ->
(forall c', Q c' -> realizes asegs c' T) -> realizes asegs c T.
Proof. intros Σ PMc ms Q T c Hc CP K. exact (cps_realizes asegs _ _ T c CP Hc K). Qed.

Lemma rz_cpsE : forall Σ PMc (ms : machine_state) evs (Q : config -> Prop) T c,
ASTA RT Σ PMc (eq ms) c -> cpsE asegs (ASTA RT Σ PMc (eq ms)) evs Q ->
(forall c', Q c' -> realizes asegs c' T) -> realizes asegs c (t_emit evs T).
Proof. intros Σ PMc ms evs Q T c Hc CP K. exact (CP T c Hc K). Qed.

End Rz.

Lemma shad_inside : forall f fsz a n, f mod 8 = 0 -> a mod 8 = 0 -> fsz mod 8 = 0 -> n mod 8 = 0 -> 0 <= f -> f <= a -> a + n <= f + fsz -> 0 <= n ->
shad f <= shad a /\ shad a + n / 8 <= shad f + fsz / 8.
Proof. intros f fsz a n F8 A8 S8 N8 F0 H1 H2 N0. unfold shad. Z.div_mod_to_equations. lia. Qed.

Lemma uw_chain_transport : forall TOPB W (m m' : mem) ras f fp,
(forall a, f <= a -> disjoint_from W a 16) -> munch W m m' -> wmono asegs m m' ->
uw_chain TOPB m f fp ras -> uw_chain TOPB m' f fp ras.
Proof.
intros TOPB W m m'. induction ras as [|r ras IH]; intros f fp DJ MU WM H; cbn [uw_chain] in *; [exact H|].
destruct H as (H1 & H2 & H3 & fp' & H4 & H5 & H6).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. exists fp'. split; [exact H4|]. split.
- apply (rw_cells_transport asegs W m m' _ _ H5 MU WM). cbn [cells_size csize Nat.add]. apply DJ. lia.
- apply (IH fp fp'); [intros a Ha; apply DJ; lia| exact MU| exact WM| exact H6].
Qed.
Lemma unwind_ch_transport : forall W (m m' : mem) ra s0 sp,
(forall a, bv_unsigned sp <= a -> disjoint_from W a 16) -> munch W m m' -> wmono asegs m m' ->
unwind_ch m ra s0 sp -> unwind_ch m' ra s0 sp.
Proof.
intros W m m' ra s0 sp DJ MU WM (ras & H1 & H2). exists ras. split; [exact H1|].
exact (uw_chain_transport USTACK_TOP W m m' ras _ _ DJ MU WM H2).
Qed.

Section PresFp.
Variable RT : rt_sig.

Lemma aclient_mono : forall live frames sp live' frames' sp' a,
aclient live frames sp a -> (forall e, In e live -> In e live') -> (forall e, In e frames -> In e frames') -> sp' <= sp ->
aclient live' frames' sp' a.
Proof.
intros live frames sp live' frames' sp' a H HL HF Hsp. destruct H as [H|[H|[H|[H|H]]]].
- left. lia.
- right; left. exact H.
- right; right; left. destruct H as (p & n & Hin & Hp). exists p, n. split; [apply HL; exact Hin| exact Hp].
- right; right; right; left. destruct H as (f & k & Hin & Hf). exists f, k. split; [apply HF; exact Hin| exact Hf].
- right; right; right; right. destruct H as (f & k & Hin & Hf). exists f, k. split; [apply HF; exact Hin| exact Hf].
Qed.

Lemma pres_fp_refl : forall live frames sp W m, rt_pres_fp live frames sp W m m.
Proof. intros live frames sp W m a _ _. reflexivity. Qed.
Lemma pres_fp_trans : forall live frames sp W m1 m2 m3,
rt_pres_fp live frames sp W m1 m2 -> rt_pres_fp live frames sp W m2 m3 -> rt_pres_fp live frames sp W m1 m3.
Proof. intros live frames sp W m1 m2 m3 H1 H2 a Ha Ho. rewrite (H2 a Ha Ho). exact (H1 a Ha Ho). Qed.
Lemma pres_fp_of_pres : forall live frames sp W m m', rt_pres live frames sp m m' -> rt_pres_fp live frames sp W m m'.
Proof. intros live frames sp W m m' H a Ha _. exact (H a Ha). Qed.
Lemma pres_fp_weaken : forall live frames sp W W' m m', rt_pres_fp live frames sp W m m' -> (forall x, outside W' x -> outside W x) ->
rt_pres_fp live frames sp W' m m'.
Proof. intros live frames sp W W' m m' H HW a Ha Ho. exact (H a Ha (HW _ Ho)). Qed.
Lemma pres_fp_mono : forall live frames sp live' frames' sp' W m m',
rt_pres_fp live' frames' sp' W m m' -> (forall e, In e live -> In e live') -> (forall e, In e frames -> In e frames') -> sp' <= sp ->
rt_pres_fp live frames sp W m m'.
Proof.
intros live frames sp live' frames' sp' W m m' H HL HF Hsp a Ha Ho. apply H; [| exact Ho].
exact (aclient_mono live frames sp live' frames' sp' _ Ha HL HF Hsp).
Qed.
Lemma pres_fp_of_munch : forall live frames sp W W' m m', munch W' m m' ->
(forall x, aclient live frames sp x -> outside W x -> outside W' x) -> rt_pres_fp live frames sp W m m'.
Proof. intros live frames sp W W' m m' MU H a Ha Ho. apply MU. exact (H _ Ha Ho). Qed.
Lemma pres_fp_of_ex : forall live frames sp d n W m m', rt_pres_ex live frames sp d n m m' ->
(forall x, d <= x < d + n -> ~ outside W x) -> rt_pres_fp live frames sp W m m'.
Proof. intros live frames sp d n W m m' H HW a Ha Ho. apply H; [exact Ha|]. intros Hd. exact (HW _ Hd Ho). Qed.

Lemma pres_fp_of_pres_ex_gen : forall live frames sp W live' frames' sp' d n m m',
rt_pres_ex live' frames' sp' d n m m' -> (forall e, In e live -> In e live') -> (forall e, In e frames -> In e frames') -> sp' <= sp ->
(forall x, aclient live frames sp x -> outside W x -> ~ (d <= x < d + n)) -> rt_pres_fp live frames sp W m m'.
Proof.
intros live frames sp W live' frames' sp' d n m m' H HL HF Hsp HW a Ha Ho. apply H; [| exact (HW _ Ha Ho)].
exact (aclient_mono live frames sp live' frames' sp' _ Ha HL HF Hsp).
Qed.

Lemma pres_fp_of_pres_fp : forall live frames sp W live' frames' sp' W' m m',
rt_pres_fp live' frames' sp' W' m m' -> (forall e, In e live -> In e live') -> (forall e, In e frames -> In e frames') -> sp' <= sp ->
(forall x, aclient live frames sp x -> outside W x -> outside W' x) -> rt_pres_fp live frames sp W m m'.
Proof.
intros live frames sp W live' frames' sp' W' m m' H HL HF Hsp HW a Ha Ho. apply H; [| exact (HW _ Ha Ho)].
exact (aclient_mono live frames sp live' frames' sp' _ Ha HL HF Hsp).
Qed.

Lemma live_remove_sub : forall (l : list (Z * Z)) p e, In e (live_remove p l) -> In e l.
Proof.
intros l p e He. unfold live_remove in He. apply stdpp.base.list_elem_of_In in He.
apply stdpp.list_basics.list.list_elem_of_filter in He. apply stdpp.base.list_elem_of_In. exact (proj2 He).
Qed.
Lemma live_remove_keep : forall (l : list (Z * Z)) p e, In e l -> fst e <> p -> In e (live_remove p l).
Proof.
intros l p e He Hp. unfold live_remove. apply stdpp.base.list_elem_of_In. apply stdpp.list_basics.list.list_elem_of_filter.
split; [| apply stdpp.base.list_elem_of_In; exact He]. apply Z.eqb_neq in Hp. rewrite Hp. exact I.
Qed.
End PresFp.

Section Frames.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma ASTA_switch : forall (Σ Σ' : rts RT) PMc Pm c, ASTA RT Σ PMc Pm c -> rt_allow RT Σ' = rt_allow RT Σ ->
(forall mo, ARTM RT Σ mo -> ARTM RT Σ' mo) -> ASTA RT Σ' PMc Pm c.
Proof.
intros Σ Σ' PMc Pm c H HA HM. unfold ASTA in *. rewrite HA.
eapply AST_conseq; [exact H| auto|]. intros mo [H1 H2]. split; [apply HM; exact H1| exact H2].
Qed.

Lemma newframe_apart : forall (Σ Σ1 : rts RT) (m1 : mem) Fr k usp a,
ART RT Σ1 m1 -> rt_frames RT Σ1 = (Fr, k) :: rt_frames RT Σ -> rt_live RT Σ1 = rt_live RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ ->
rt_sp0 RT Σ - STACK_WIN <= usp -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp a ->
~ (Fr <= a < Fr + fs_size k) /\ ~ (shad Fr <= a < shad (Fr + fs_size k)).
Proof using AF.
intros Σ Σ1 m1 Fr k usp a ART1 FRS LV SP0 LU Ha.
assert (INF : In (Fr, k) (rt_frames RT Σ1)) by (rewrite FRS; left; reflexivity).
pose proof (af_frames_range RT AF Σ1 m1 Fr k ART1 INF) as (R0 & R1 & R2 & R3).
pose proof (af_fshadow_apart RT AF Σ1 m1 Fr k ART1 INF) as (SL & SF).
pose proof (af_sp0_range RT AF Σ1 m1 ART1) as SPR. pose proof (af_sp0_win RT AF Σ1 m1 ART1) as SPW.
rewrite SP0 in R1, SPR, SPW.
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (SH1 : shad (Fr + fs_size k) <= 2^44 + SHB).
{ unfold shad. assert ((Fr + fs_size k) / 8 <= 2^44) by (apply Z.div_le_upper_bound; ul). lia. }
assert (SH0 : SHB <= shad Fr) by (unfold shad; assert (0 <= Fr / 8) by (apply Z.div_pos; lia); lia).
assert (SHM : shad Fr <= shad (Fr + fs_size k)) by (unfold shad; pose proof (Z.div_le_mono Fr (Fr + fs_size k) 8 ltac:(lia) ltac:(lia)); lia).
destruct Ha as [H|[H|[H|[H|H]]]].
- split; unfold SHB in *; ul.
- pose proof (client_static_range a H). split; [destruct R2; unfold SEGTOP_A in *; lia|]. unfold SHB, SEGTOP_A in *. lia.
- destruct H as (p & n & Hin & Hp). rewrite <- LV in Hin. destruct (R3 p n Hin); destruct (SL p n Hin); split; lia.
- destruct H as (f & k' & Hin & Hf).
destruct (af_frames_disj RT AF Σ1 m1 Fr k f k' [] (rt_frames RT Σ) ART1 FRS Hin) as [D|D];
(destruct (SF f k' ltac:(rewrite FRS; right; exact Hin)) as [E|E]); split; lia.
- destruct H as (f & k' & Hin & Hf).
assert (INf : In (f, k') (rt_frames RT Σ1)) by (rewrite FRS; right; exact Hin).
pose proof (af_fshadow_apart RT AF Σ1 m1 f k' ART1 INf) as (_ & SF').
destruct (af_frames_disj RT AF Σ1 m1 Fr k f k' [] (rt_frames RT Σ) ART1 FRS Hin) as [D|D].
+ pose proof (Z.div_le_mono (Fr + fs_size k) f 8 ltac:(lia) D). destruct (SF' Fr k INF) as [E|E]; split; unfold shad in *; lia.
+ assert (FSZ' : 0 <= fs_size k') by (unfold fs_size; apply Z.shiftl_nonneg; lia).
pose proof (Z.div_le_mono (f + fs_size k') Fr 8 ltac:(lia) D). destruct (SF' Fr k INF) as [E|E]; split; unfold shad in *; lia.
Qed.

Lemma frame_facts : forall (Σ : rts RT) (m : mem) f k, ART RT Σ m -> In (f, k) (rt_frames RT Σ) ->
0 < f /\ f mod 64 = 0 /\ SEGTOP_A <= f /\ f + fs_size k <= rt_sp0 RT Σ - STACK_WIN
/\ (f + fs_size k <= 0x7fff7000 \/ 0x10007fff8000 <= f)
/\ Z.shiftr f 3 + SHB = shad f /\ shad (f + fs_size k) = shad f + fs_size k / 8
/\ SH_LO <= shad f /\ shad f + fs_size k / 8 <= SH_HI
/\ (f + fs_size k <= shad f \/ shad f + fs_size k / 8 <= f).
Proof using AF.
intros Σ m f k ART0 INF.
pose proof (af_fshadow_apart RT AF Σ m f k ART0 INF) as (_ & SELF). specialize (SELF f k INF).
pose proof (af_frames_range RT AF Σ m f k ART0 INF) as (R0 & R1 & _).
pose proof (af_frames_align RT AF Σ m f k ART0 INF) as (A64 & AIMG).
pose proof (af_frames_hi RT AF Σ m f k ART0 INF) as HI.
pose proof (af_sp0_range RT AF Σ m ART0) as SPR.
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (SA : shad (f + fs_size k) = shad f + fs_size k / 8) by (apply shad_aligned_add; [clear - A64; Z.div_mod_to_equations; lia| exact FSZ]).
split; [exact R0|]. split; [exact A64|]. split; [exact AIMG|]. split; [exact R1|]. split; [exact HI|].
split; [apply shad_shiftr|]. split; [exact SA|].
rewrite <- SA. split; [| split; [| exact SELF]]; unfold shad, SHB, SH_LO, SH_HI.
- assert (0 <= f / 8) by (apply Z.div_pos; lia). lia.
- assert ((f + fs_size k) / 8 <= 2^44) by (apply Z.div_le_upper_bound; ul). lia.
Qed.

Lemma frame_live_apart : forall (Σ : rts RT) (m : mem) f k p n, ART RT Σ m -> In (f, k) (rt_frames RT Σ) -> In (p, n) (rt_live RT Σ) ->
(f + fs_size k <= p \/ p + n <= f) /\ (p + n <= shad f \/ shad (f + fs_size k) <= p).
Proof using AF.
intros Σ m f k p n ART0 INF INL.
pose proof (af_frames_range RT AF Σ m f k ART0 INF) as (_ & _ & _ & R3).
pose proof (af_fshadow_apart RT AF Σ m f k ART0 INF) as (SL & _).
split; [exact (R3 p n INL)| exact (SL p n INL)].
Qed.

Lemma live_facts : forall (Σ : rts RT) (m : mem) p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) ->
0 < p /\ p + n <= rt_sp0 RT Σ - STACK_WIN /\ (p + n <= 0x10000 \/ SEGTOP_A <= p) /\ (p + n <= 0x7fff7000 \/ 0x10007fff8000 <= p).
Proof using AF.
intros Σ m p n ART0 INL. pose proof (af_live_range RT AF Σ m p n ART0 INL) as (L0 & L1 & L2).
pose proof (af_live_offshadow RT AF Σ m p n ART0 INL) as L3. tauto.
Qed.

Lemma aclient_split : forall (Σ : rts RT) (m : mem) usp a, ART RT Σ m -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp a ->
usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN.
Proof using AF.
intros Σ m usp a ART0 [H|[H|[H|[H|H]]]].
- left; lia.
- right. pose proof (client_static_range a H). pose proof (af_sp0_range RT AF Σ m ART0). ul.
- right. destruct H as (p & n & Hin & Hp). pose proof (af_live_range RT AF Σ m p n ART0 Hin). lia.
- right. destruct H as (f & k & Hin & Hf). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & H2 & _).
unfold fs_size in *. pose proof (Z.shiftl_nonneg 64 (Z.of_nat k)) as E. lia.
- right. destruct H as (f & k & Hin & Hf). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & H2 & _).
pose proof (af_sp0_range RT AF Σ m ART0). pose proof (af_sp0_win RT AF Σ m ART0).
unfold shad, SHB in Hf. unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *. Z.div_mod_to_equations. lia.
Qed.

Lemma flag_not_client : forall (Σ Σ1 : rts RT) f k usp fl a,
rt_frames RT Σ1 = (f, k) :: rt_frames RT Σ -> rt_live RT Σ1 = rt_live RT Σ ->
~ aclient (rt_live RT Σ1) (rt_frames RT Σ1) USTACK_TOP fl -> fl < usp ->
aclient (rt_live RT Σ) (rt_frames RT Σ) usp a -> a <> fl.
Proof.
intros Σ Σ1 f k usp fl a FRS LV NAC FLU Ha E. subst a. apply NAC. rewrite LV, FRS.
destruct Ha as [H|[H|[H|[H|H]]]]; [lia| right; left; exact H| right; right; left; exact H|
right; right; right; left; destruct H as (f' & k' & Hin & Hf); exists f', k'; split; [right; exact Hin| exact Hf]|
right; right; right; right; destruct H as (f' & k' & Hin & Hf); exists f', k'; split; [right; exact Hin| exact Hf]].
Qed.

Lemma frame_below_lo : forall (Σ : rts RT) (m : mem) f k lo, ART RT Σ m -> In (f, k) (rt_frames RT Σ) -> rt_sp0 RT Σ - STACK_WIN <= lo ->
f + fs_size k <= lo /\ shad f + fs_size k / 8 <= lo /\ SH_HI <= lo.
Proof using AF.
intros Σ m f k lo ART0 INF LOW. pose proof (frame_facts Σ m f k ART0 INF) as (_ & _ & _ & R1 & _ & _ & _ & _ & S1 & _).
pose proof (af_sp0_win RT AF Σ m ART0) as SPW. unfold SH_HI, STACK_WIN in *. lia.
Qed.
Lemma live_below_lo : forall (Σ : rts RT) (m : mem) p n lo, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> rt_sp0 RT Σ - STACK_WIN <= lo ->
0 < p /\ p + n <= lo /\ SH_HI <= lo.
Proof using AF.
intros Σ m p n lo ART0 INL LOW. pose proof (af_live_range RT AF Σ m p n ART0 INL) as (L0 & L1 & _).
pose proof (af_sp0_win RT AF Σ m ART0) as SPW. unfold SH_HI, STACK_WIN in *. lia.
Qed.

Lemma aobj_lit : forall (Σ : rts RT) (m : mem) a n, ART RT Σ m -> In (a, n) ACC_LITS -> 0 <= a -> a + n <= APP_TOP -> aobj asegs m a n.
Proof using AF.
intros Σ m a n ART0 IN A0 A1. split; [exact A0|]. split; [exact A1|].
pose proof (af_acc_lits RT AF Σ m ART0) as AL. rewrite Forall_forall in AL. exact (AL (a, n) IN).
Qed.

Lemma newchunk_apart_gen : forall (Σ Σ1 : rts RT) (m1 : mem) p n L usp a,
ART RT Σ1 m1 -> rt_live RT Σ1 = (p, n) :: L -> rt_frames RT Σ1 = rt_frames RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ ->
rt_sp0 RT Σ - STACK_WIN <= usp -> 0 <= n -> aclient L (rt_frames RT Σ) usp a -> ~ (p <= a < p + n).
Proof using AF.
intros Σ Σ1 m1 p n L usp a ART1 LV FRS SP0 LU N0 Ha Hin.
assert (INL : In (p, n) (rt_live RT Σ1)) by (rewrite LV; left; reflexivity).
pose proof (af_live_range RT AF Σ1 m1 p n ART1 INL) as (L0 & L1 & L2). rewrite SP0 in L1.
destruct Ha as [H|[H|[H|[H|H]]]].
- lia.
- pose proof (client_static_range a H). unfold SEGTOP_A in *. lia.
- destruct H as (p' & n' & Hin' & Hp').
destruct (af_live_disj RT AF Σ1 m1 p n p' n' [] L ART1 LV Hin'); lia.
- destruct H as (f & k & Hinf & Hf). rewrite <- FRS in Hinf.
pose proof (af_frames_range RT AF Σ1 m1 f k ART1 Hinf) as (_ & _ & _ & R3). destruct (R3 p n INL); lia.
- destruct H as (f & k & Hinf & Hf). rewrite <- FRS in Hinf.
pose proof (af_fshadow_apart RT AF Σ1 m1 f k ART1 Hinf) as (SL & _). destruct (SL p n INL); lia.
Qed.
Lemma newchunk_apart : forall (Σ Σ1 : rts RT) (m1 : mem) p n usp a,
ART RT Σ1 m1 -> rt_live RT Σ1 = (p, n) :: rt_live RT Σ -> rt_frames RT Σ1 = rt_frames RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ ->
rt_sp0 RT Σ - STACK_WIN <= usp -> 0 <= n -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp a -> ~ (p <= a < p + n).
Proof using AF. intros Σ Σ1 m1 p n usp a. exact (newchunk_apart_gen Σ Σ1 m1 p n (rt_live RT Σ) usp a). Qed.

Lemma live_remove_apart : forall (Σ : rts RT) (m : mem) D n p2 n2, ART RT Σ m -> In (D, n) (rt_live RT Σ) ->
In (p2, n2) (live_remove D (rt_live RT Σ)) -> D + n <= p2 \/ p2 + n2 <= D.
Proof using AF.
intros Σ m D n p2 n2 ART0 IN INR.
assert (NE : p2 <> D).
{ unfold live_remove in INR. apply stdpp.base.list_elem_of_In in INR. apply stdpp.list_basics.list.list_elem_of_filter in INR.
destruct INR as [PR _]. cbn [fst] in PR. destruct (Z.eqb_spec p2 D) as [E|NE]; [destruct PR| exact NE]. }
pose proof (live_remove_sub _ _ _ INR) as IN2.
destruct (in_split _ _ IN) as (l1 & l2 & E). rewrite E in IN2.
apply (af_live_disj RT AF Σ m D n p2 n2 l1 l2 ART0 E).
apply in_app_or in IN2. apply in_or_app. destruct IN2 as [H|[H|H]]; [left; exact H| injection H as H1 _; congruence| right; exact H].
Qed.
Lemma aclient_remove_apart : forall (Σ : rts RT) (m : mem) D n usp a, ART RT Σ m -> In (D, n) (rt_live RT Σ) ->
rt_sp0 RT Σ - STACK_WIN <= usp -> aclient (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) usp a -> ~ (D <= a < D + n).
Proof using AF.
intros Σ m D n usp a ART0 IN LU Ha Hin.
pose proof (af_live_range RT AF Σ m D n ART0 IN) as (L0 & L1 & L2).
destruct Ha as [H|[H|[H|[H|H]]]].
- lia.
- pose proof (client_static_range a H). unfold SEGTOP_A in *. lia.
- destruct H as (p' & n' & Hin' & Hp'). destruct (live_remove_apart Σ m D n p' n' ART0 IN Hin'); lia.
- destruct H as (f & k & Hinf & Hf). pose proof (af_frames_range RT AF Σ m f k ART0 Hinf) as (_ & _ & _ & R3). destruct (R3 D n IN); lia.
- destruct H as (f & k & Hinf & Hf). pose proof (af_fshadow_apart RT AF Σ m f k ART0 Hinf) as (SL & _). destruct (SL D n IN); lia.
Qed.
End Frames.

Lemma outside_img : forall (W : list (Z * Z)) x, (forall y, in_ranges W y -> client_static y) -> (x < 0x10000 \/ SEGTOP_A <= x) -> outside W x.
Proof.
intros W x HW Hx. apply outside_of_not_in_ranges'. intros Hin. pose proof (client_static_range x (HW x Hin)). lia.
Qed.

Lemma u8arr_rw_CB : forall (m : mem) A bs, u8arr asegs m A bs <-> rw_cells asegs m A [CB (length bs) bs].
Proof.
intros m A bs. unfold u8arr, rw_cells, cells_at. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize]. rewrite app_nil_r, Nat.add_0_r. tauto.
Qed.

Lemma rw_cells_to_CB : forall segs (m : mem) A cs, rw_cells segs m A cs -> rw_cells segs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
intros segs m A cs H. apply (rw_cells_recast segs m A cs); [exact H| | cbn [cells_bytes cbytes]; apply app_nil_r].
split; [| exact I]. destruct H as [[Hwf _] _]. exact (cells_bytes_length cs Hwf).
Qed.

Lemma fp_local_munch : forall (W : list (Z * Z)) (P : mem -> Prop) Wm (m m' : mem),
fp_local W P -> (forall y, in_ranges W y -> client_static y) -> munch Wm m m' ->
(forall x, 0x10000 <= x < SEGTOP_A -> outside Wm x) -> P m -> P m'.
Proof. intros W P Wm m m' L IMG MU OUT Pm. apply (L m m' Pm). intros a Ha. apply MU. apply OUT. exact (client_static_range _ (IMG _ Ha)). Qed.
Lemma fp_local_pres : forall (W : list (Z * Z)) (P : mem -> Prop) live frames sp (m m' : mem),
fp_local W P -> (forall y, in_ranges W y -> client_static y) -> rt_pres live frames sp m m' -> P m -> P m'.
Proof. intros W P live frames sp m m' L IMG PRES Pm. apply (L m m' Pm). intros a Ha. apply PRES. right; left. exact (IMG _ Ha). Qed.

Definition ret_stL (P : bvmap 5 word -> bv 32 -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (m' : mem)
(ms : machine_state) : Prop :=
exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32),
ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom asegs) /\ P F' fc'.

Ltac cps_unf := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SH_HI, SH_LO, APP_TOP, IMG_TOP in *.
Ltac cps_norm := cps_unf.

Ltac cps_hide := hide_disj.
Ltac cps_unhide := unhide_disj.
Ltac arith_goal :=
lazymatch goal with
| |- (_ <= _)%Z => idtac | |- (_ < _)%Z => idtac | |- (_ <= _ < _)%Z => idtac | |- (_ <= _ <= _)%Z => idtac | |- (_ < _ <= _)%Z => idtac | |- (_ < _ < _)%Z => idtac
| |- @eq Z _ _ => idtac | |- _ \/ _ => idtac | |- ~ _ => idtac | |- False => idtac | |- _ /\ _ => idtac | |- (_ >= _)%Z => idtac | |- (_ > _)%Z => idtac
| |- _ <> _ => idtac
end.
Ltac with_hid tac := arith_goal; match goal with H : hid ?P |- _ => let U := fresh "U" in pose proof (H : P) as U; tac end.
Ltac ulq0 := idtac; first [ llia | cps_unf; llia ].
Ltac ulc0 := idtac; first [ llia | cps_unf; first [ llia | cllia ] ].
Ltac ulq := idtac; first [ llia | cps_unf; first [ llia | with_hid ltac:(llia) ] ].
Ltac ulc := idtac; first [ llia | cps_unf; first [ llia | cllia | with_hid ltac:(llia) | with_hid ltac:(cllia) ] ].

Ltac cps_sizes Hx :=
rewrite ?cells_size_app, ?cells_size_f32 in Hx;
cbn in Hx.

Ltac fs_lit := repeat match goal with |- context [fs_size ?k] =>
let v := eval vm_compute in (fs_size k) in
lazymatch v with Zpos _ => change (fs_size k) with v end
end.
Ltac aclient_cls tac :=
lazymatch goal with
| |- aclient ?L ?Fr _ _ =>
first
[ left; tac
| right; right; left; match goal with H : In (?p, ?n) L |- _ => exists p, n; split; [exact H | tac] end
| right; right; right; left; match goal with H : In (?f, ?k) Fr |- _ => exists f, k; split; [exact H | fs_lit; tac] end
| right; right; right; right; match goal with H : In (?f, ?k) Fr |- _ => exists f, k; split; [exact H | fs_lit; tac] end ]
end.

Ltac aclient_tac tac := first [ aclient_cls ltac:(ulq0) | aclient_cls ltac:(ulc0) ].

Ltac pres_outside tac :=
cbn [outside];
repeat lazymatch goal with |- _ /\ _ => split end;
first [ exact I
| lazymatch goal with
| |- outside ?W _ => match goal with IMG : forall y, in_ranges W y -> client_static y |- _ => apply (outside_img W _ IMG); tac end
end
| tac ].
Ltac pres_agree PRES tac :=
lazymatch type of PRES with
| rt_pres ?live ?frames ?sp ?m ?m' =>
apply (agree_of_pres live frames sp m m' _ PRES); intros ? ?Hx; cps_sizes Hx; aclient_tac tac
| rt_pres_fp ?live ?frames ?sp ?W ?m ?m' =>
apply (agree_of_pres_fp live frames sp W m m' _ PRES); intros ? ?Hx; cps_sizes Hx; split; [ aclient_tac tac | pres_outside tac ]
| rt_pres_ex ?live ?frames ?sp ?d ?n ?m ?m' =>
apply (agree_of_pres_ex live frames sp d n m m' _ PRES); intros ? ?Hx; cps_sizes Hx; split; [ aclient_tac tac | tac ]
end.
Ltac pres_mems PRES k :=
lazymatch type of PRES with
| rt_pres _ _ _ ?m ?m' => k m m'
| rt_pres_fp _ _ _ _ ?m ?m' => k m m'
| rt_pres_ex _ _ _ _ _ ?m ?m' => k m m'
end.
Ltac pres_transport_g PRES tac :=
pres_mems PRES ltac:(fun m m' =>
repeat match goal with
| H : rw_cells asegs m ?A ?cs |- _ =>
first [ let H' := fresh "T" in
assert (H' : rw_cells asegs m' A cs)
by (first [ match goal with WM : wmono asegs m m' |- _ => apply (rw_cells_agree asegs m m' A cs H); [ pres_agree PRES tac | exact WM ] end
| apply (rw_cells_agree_nw asegs m m' A cs H); pres_agree PRES tac ]);
clear H; rename H' into H
| idtac "note: dropping hypothesis (not client memory for this call):" H; clear H ]
| H : ro_cells asegs m ?A ?cs |- _ =>
first [ let H' := fresh "T" in
assert (H' : ro_cells asegs m' A cs) by (apply (ro_cells_agree asegs m m' A cs H); pres_agree PRES tac);
clear H; rename H' into H
| idtac "note: dropping hypothesis (not client memory for this call):" H; clear H ]
| H : bytes_at asegs m ?A ?bs |- _ =>
first [ let H' := fresh "T" in
assert (H' : bytes_at asegs m' A bs) by (apply (bytes_at_agree asegs m m' A bs H); pres_agree PRES tac);
clear H; rename H' into H
| idtac "note: dropping hypothesis (not client memory for this call):" H; clear H ]
end).
Ltac pres_transport PRES WM tac := pres_transport_g PRES tac.

Ltac seg_lia := first [ exact I | repeat (split; [ulq|]); first [exact I | ulq] ].
Ltac seg_transport m m' MU WM :=
let W := lazymatch type of MU with munch ?W _ _ => W end in
repeat match goal with
| H : bytes_at asegs m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_transport asegs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; seg_lia ]
| idtac "note: dropping hypothesis (not provably disjoint from the segment's footprint):" H; clear H ]
| H : rw_cells asegs m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_transport asegs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; seg_lia ]
| idtac "note: dropping hypothesis (not provably disjoint from the segment's footprint):" H; clear H ]
| H : ro_cells asegs m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_transport asegs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; seg_lia ]
| idtac "note: dropping hypothesis (not provably disjoint from the segment's footprint):" H; clear H ]
| H : stk asegs m ?loq ?hiq |- _ =>
first [ apply (stk_transport_disjoint asegs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; seg_lia ]
| clear H ]
end.

Ltac cps_auto := try reflexivity; try eassumption; try ulq.

Tactic Notation "cps_seg" uconstr(LEM) :=
lazymatch goal with
| Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes asegs ?c ?T =>
refine (rz_evt RT ltac:(eassumption) Σ PMc ms _ T c ltac:(eassumption) Hc _ _);
[ eapply LEM; cps_auto
| let ms' := fresh "ms" in let c' := fresh "c" in let Hc' := fresh "Hc" in
intros ms' c' POST Hc'; cbv beta in POST; clear Hc ]
end.

Tactic Notation "cps_rt" uconstr(CON) :=
lazymatch goal with
| Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes asegs ?c ?T =>
refine (rz_cps RT Σ PMc ms _ T c Hc _ _); [ eapply CON; cps_auto | ]
end.

Tactic Notation "cps_rtE" uconstr(CON) :=
lazymatch goal with
| Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes asegs ?c (t_emit ?evs ?T) =>
refine (rz_cpsE RT Σ PMc ms evs _ T c Hc _ _); [ eapply CON; cps_auto | ]
end.

Tactic Notation "cps_rt_sized" uconstr(CON) constr(n) :=
lazymatch goal with
| Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes asegs ?c ?T =>
refine (rz_cps RT Σ PMc ms _ T c Hc _ _); [ eapply CON with (size := n); cps_auto | ]
end.

Ltac cps_callok :=
unfold call_ok; rewrite unsigned_lit by ulc;
split; [eassumption|]; split; [ulc|]; split; [ulc|]; split; [ulc|];
first [ ulq | match goal with H : _ mod 32 = 0 |- _ => clear - H; Z.div_mod_to_equations; lia end ].

Ltac cps_ret_exs RS :=
let T := type of RS in let T' := eval hnf in T in
lazymatch T' with
| ex _ => let x := fresh "r" in destruct RS as [x RS]; cps_ret_exs RS
| _ => idtac
end.
Ltac cps_ret RS :=
cps_ret_exs RS;
lazymatch type of RS with
| ?v = _ => subst v
| ?v = _ /\ _ => let E := fresh "E" in destruct RS as [E RS]; subst v
end.

Ltac cps_pf_seg m m' MU :=
lazymatch goal with
| PF : rt_pres_fp ?L0 ?F0 ?U0 ?W0 ?m0 m |- _ =>
let PF' := fresh "PF" in
assert (PF' : rt_pres_fp L0 F0 U0 W0 m0 m')
by (apply (pres_fp_trans L0 F0 U0 W0 m0 m m' PF); apply (pres_fp_of_munch L0 F0 U0 W0 _ m m' MU);
let x := fresh "x" in let Hx := fresh "Hx" in let Ho := fresh "Ho" in
intros x Hx Ho; cbn [outside] in Ho |- *;
repeat match goal with NA : forall a, aclient L0 F0 U0 a -> _ |- _ => pose proof (NA x Hx); clear NA end;
decompose [and] Ho;
repeat split; ulc);
clear PF; rename PF' into PF
| _ => idtac
end.

Ltac cps_seg_post_with MU WM A LO :=
lazymatch type of MU with
| munch ?W ?m ?m' =>
lazymatch type of A with
| ART ?RT ?Σ m =>
lazymatch type of LO with
| _ <= ?lo =>
let A' := fresh "ART" in
assert (A' : ART RT Σ m')
by (apply (af_frame RT ltac:(eassumption) Σ m m' lo A LO); [| exact WM];
let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; apply MU; cbn [outside]; repeat split; intros ?Hin; apply Ha; aclient_tac ltac:(ulc));
cps_pf_seg m m' MU;
clear A; seg_transport m m' MU WM;
try match goal with MI : mem_inv asegs m |- _ => clear MI end
end
end
end.

Ltac cps_seg_post :=
match goal with
| MU : munch ?W ?m ?m', WM : wmono asegs ?m ?m', A : ART ?RT ?Σ ?m |- _ =>
first
[ match goal with ST : stk asegs m' ?lo _, LO : rt_sp0 RT Σ - _ <= ?lo |- _ => cps_seg_post_with MU WM A LO end
| match goal with ST : stk asegs m ?lo _, LO : rt_sp0 RT Σ - _ <= ?lo |- _ => cps_seg_post_with MU WM A LO end
| match goal with LO : rt_sp0 RT Σ - _ <= _ |- _ => cps_seg_post_with MU WM A LO end ]
end.

Ltac cps_incl :=
first [ now auto
| apply live_remove_sub
| intros ? ?Hi; first [ exact (live_remove_sub _ _ _ Hi)
| repeat match goal with E : _ = _ |- _ => rewrite E end; auto with datatypes ] ].
Ltac cps_pf_pres PRES :=
let m := lazymatch type of PRES with rt_pres _ _ _ ?m _ => m | rt_pres_fp _ _ _ _ ?m _ => m | rt_pres_ex _ _ _ _ _ ?m _ => m end in
lazymatch goal with
| PF : rt_pres_fp ?L0 ?F0 ?U0 ?W0 ?m0 m |- _ =>
lazymatch type of PRES with
| rt_pres ?live ?frames ?sp m ?m' =>
let PF' := fresh "PF" in
assert (PF' : rt_pres_fp L0 F0 U0 W0 m0 m')
by (apply (pres_fp_trans L0 F0 U0 W0 m0 m m' PF);
apply (pres_fp_mono L0 F0 U0 live frames sp W0 m m' (pres_fp_of_pres live frames sp W0 m m' PRES));
[ cps_incl
| cps_incl
| ulc ]);
clear PF; rename PF' into PF
| rt_pres_fp ?live ?frames ?sp ?W m ?m' =>

let PF' := fresh "PF" in
assert (PF' : rt_pres_fp L0 F0 U0 W0 m0 m')
by (apply (pres_fp_trans L0 F0 U0 W0 m0 m m' PF);
apply (pres_fp_of_pres_fp L0 F0 U0 W0 live frames sp W m m' PRES);
[ cps_incl
| cps_incl
| ulc
| let x := fresh "x" in let Hx := fresh "Hx" in let Ho := fresh "Ho" in
intros x Hx Ho; cbn [outside] in Ho; first [ exact Ho | tauto ] ]);
clear PF; rename PF' into PF
| rt_pres_ex ?live ?frames ?sp ?d ?n m ?m' =>

let PF' := fresh "PF" in
assert (PF' : rt_pres_fp L0 F0 U0 W0 m0 m')
by (apply (pres_fp_trans L0 F0 U0 W0 m0 m m' PF);
apply (pres_fp_of_pres_ex_gen L0 F0 U0 W0 live frames sp d n m m' PRES);
[ cps_incl | cps_incl | ulc
| let x := fresh "x" in let Hx := fresh "Hx" in let Ho := fresh "Ho" in
intros x Hx Ho; cbn [outside] in Ho;
repeat match goal with NA : forall a, aclient L0 F0 U0 a -> _ |- _ => pose proof (NA x Hx); clear NA end;
decompose [and] Ho; ulc ]);
clear PF; rename PF' into PF
| _ => idtac
end
| _ => idtac
end.

Ltac cps_unpack_tr PRES m :=
pres_transport_g PRES ltac:(ulc); cps_pf_pres PRES;
try match goal with A : ART _ _ m |- _ => clear A end;
try match goal with MI : mem_inv asegs m |- _ => clear MI end;
try match goal with ST : stk asegs m _ _ |- _ => clear ST end.

Tactic Notation "cps_unpack" hyp(Hc) "as" simple_intropattern(P) :=
try unfold icpt_postF in Hc;
lazymatch type of Hc with
| ASTA ?RT ?Σ' ?PMc ?Pm ?c =>
let ms := fresh "ms" in let Hc' := fresh "Hc" in let PO := fresh "PO" in
destruct (ASTA_unpack RT Σ' PMc Pm c Hc) as (ms & PO & Hc'); clear Hc; cbv beta in PO;
destruct PO as P;
repeat match goal with
| RS : ret_stF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => cps_ret RS
| RS : ret_stR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => cps_ret RS
| RS : ret_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => cps_ret RS
end;
repeat match goal with
| H : context [bv_unsigned (Z_to_bv 64 ?z)] |- _ =>
lazymatch type of H with bv_unsigned (Z_to_bv 64 _) = _ => fail | _ => idtac end;
rewrite (unsigned_lit z) in H by ulc
end;
first
[
let m' := lazymatch type of Hc' with ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _)) _ => mm end in
match goal with
| PRES : rt_pres _ _ _ ?m m' |- _ => cps_unpack_tr PRES m
| PRES : rt_pres_fp _ _ _ _ ?m m' |- _ => cps_unpack_tr PRES m
| PRES : rt_pres_ex _ _ _ _ _ ?m m' |- _ => cps_unpack_tr PRES m
end
| match goal with
| PRES : rt_pres _ _ _ ?m ?m', WM : wmono asegs ?m ?m' |- _ => cps_unpack_tr PRES m
end
| idtac "note: cps_unpack: no preservation fact found in this post: transport the chunks you still need by hand (D_kit.*_agree*)" ]
end.

Ltac cps_sigma EL EF ES :=
lazymatch type of ES with
| rt_sp0 ?RT ?Σ' = rt_sp0 ?RT ?Σ =>
lazymatch type of EL with
| rt_live RT Σ' = ?e :: rt_live RT Σ =>
repeat match goal with
| H : In ?e0 (rt_live RT Σ) |- _ =>
let H' := fresh H in assert (H' : In e0 (rt_live RT Σ')) by (rewrite EL; right; exact H); clear H; rename H' into H
end;
let INL := fresh "INL" in assert (INL : In e (rt_live RT Σ')) by (rewrite EL; left; reflexivity)
| rt_live RT Σ' = ?e :: live_remove ?p (rt_live RT Σ) =>

repeat match goal with
| H : In ?e0 (rt_live RT Σ) |- _ =>
first [ let H' := fresh H in
assert (H' : In e0 (rt_live RT Σ'))
by (rewrite EL; right; apply (live_remove_keep _ p e0 H); cbn [fst]; first [ assumption | congruence | ulq ]);
clear H; rename H' into H
| clear H ]
end;
let INL := fresh "INL" in assert (INL : In e (rt_live RT Σ')) by (rewrite EL; left; reflexivity)
| rt_live RT Σ' = rt_live RT Σ =>
repeat match goal with H : In ?e0 (rt_live RT Σ) |- _ => rewrite <- EL in H end
end;
repeat match goal with
| H : rt_sp0 RT Σ - _ <= _ |- _ => rewrite <- ES in H
end;
try (match goal with EP : rt_pois RT Σ' = rt_pois RT Σ |- _ =>
repeat match goal with
| H : pois_above (rt_pois RT Σ) _ |- _ => rewrite <- EP in H
| H : pois_apart (rt_pois RT Σ) _ _ |- _ => rewrite <- EP in H
end end);
lazymatch type of EF with
| rt_frames RT Σ' = ?e :: rt_frames RT Σ =>
repeat match goal with
| H : In ?e0 (rt_frames RT Σ) |- _ =>
let H' := fresh H in assert (H' : In e0 (rt_frames RT Σ')) by (rewrite EF; right; exact H); clear H; rename H' into H
end;
let INF := fresh "INF" in assert (INF : In e (rt_frames RT Σ')) by (rewrite EF; left; reflexivity)
| rt_frames RT Σ' = rt_frames RT Σ =>
repeat match goal with H : In ?e0 (rt_frames RT Σ) |- _ => rewrite <- EF in H end
end
end.

Ltac cps_wmono :=
lazymatch goal with
| |- wmono asegs ?m ?m => apply wmono_refl
| |- wmono asegs ?m0 ?m =>
first [ eassumption
| match goal with W : wmono asegs ?m1 m |- _ => apply (wmono_trans asegs m0 m1 m); [ cps_wmono | exact W ] end ]
end.

Ltac cps_new_frame ART2 EF EL ES WRF WRS sf :=
lazymatch type of EF with
| rt_frames ?RT ?Σ1 = (?f, ?k) :: rt_frames ?RT ?Σ =>
lazymatch type of ART2 with
| ART RT Σ1 ?m2 =>
let fsz := eval vm_compute in (fs_size k) in
let fsz8 := eval vm_compute in (fs_size k / 8) in
let fszb := eval vm_compute in (fs_size k - 8) in
let NAF := fresh "NAF" in
lazymatch goal with
| PF : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) ?U0 _ _ _ |- _ =>
pose proof (fun a (Ha : aclient (rt_live RT Σ) (rt_frames RT Σ) U0 a) =>
newframe_apart RT ltac:(eassumption) Σ Σ1 m2 f k U0 a ART2 EF EL ES ltac:(ulc) Ha) as NAF
| _ => idtac
end;
cps_sigma EL EF ES;
match goal with
| INF : In (f, k) (rt_frames RT Σ1), LO : rt_sp0 RT Σ1 - _ <= ?lo |- _ =>
let BF1 := fresh "BF" in let BF2 := fresh "BF" in
destruct (frame_below_lo RT ltac:(eassumption) Σ1 m2 f k lo ART2 INF LO) as (BF1 & BF2 & _);
let F0 := fresh "F0" in let F64 := fresh "F64" in let FIMG := fresh "FIMG" in let FHI := fresh "FHI" in
let S0 := fresh "SHF" in let S1 := fresh "SHF" in let S2 := fresh "SHF" in let S3 := fresh "SHF" in let S4 := fresh "SHF" in
pose proof (frame_facts RT ltac:(eassumption) Σ1 m2 f k ART2 INF) as (F0 & F64 & FIMG & _ & FHI & S0 & S1 & S2 & S3 & S4);
repeat match goal with
| INL : In (?p, ?n) (rt_live RT Σ1) |- _ =>
lazymatch goal with
| _ : (f + fs_size k <= p \/ p + n <= f) |- _ => fail
| _ : (f + fsz <= p \/ p + n <= f) |- _ => fail
| _ => let A1 := fresh "FLA" in let A2 := fresh "FLA" in
destruct (frame_live_apart RT ltac:(eassumption) Σ1 m2 f k p n ART2 INF INL) as (A1 & A2)
end
end;
set (sf := Z.shiftr f 3 + SHB) in *;
let Esf := fresh "Esf" in assert (Esf : sf = Z.shiftr f 3 + SHB) by reflexivity;
change (fs_size k) with fsz in *; change (fsz - 8) with fszb in *; change (fsz / 8) with fsz8 in *;
rewrite S1 in *; rewrite <- S0 in *;
let jF := fresh "jF" in let jS := fresh "jS" in let FRB := fresh "FRB" in let FRS := fresh "FRS" in
destruct (wr_at_rw_CB m2 f fszb WRF ltac:(lia)) as (jF & FRB);
destruct (wr_at_rw_CB m2 sf fsz8 WRS ltac:(lia)) as (jS & FRS);
let nb := eval vm_compute in (Z.to_nat fszb) in change (Z.to_nat fszb) with nb in FRB;
let n8 := eval vm_compute in (Z.to_nat fsz8) in change (Z.to_nat fsz8) with n8 in FRS;
clear WRF WRS; cps_norm
end
end
end.

Ltac cps_release_intro ARTc EF EL PREL Σ2 fl :=
lazymatch type of EF with
| rt_frames ?RT ?Σ1 = (?f, ?k) :: ?fr =>
lazymatch type of ARTc with
| ART RT Σ1 ?m =>
let fszb := eval vm_compute in (fs_size k - 8) in
let FLC := fresh "FLC" in let NAC := fresh "NAC" in let FL0 := fresh "FL0" in let FLW := fresh "FLW" in let FW := fresh "FW" in
let REL := fresh "REL" in
destruct (af_frame_release RT ltac:(eassumption) Σ1 m f k fr ARTc EF PREL) as (Σ2 & fl & FLC & NAC & FL0 & FLW & FW & REL);
change (fs_size k - 8) with fszb in FW; replace (f + fs_size k - 8) with (f + fszb) in FW by (change (fs_size k) with (fszb + 8); lia);
match goal with LO : rt_sp0 RT Σ1 - _ <= ?lo |- _ => let B := fresh "BFL" in assert (B : fl + 1 <= lo) by ulc end;
cps_norm;
lazymatch goal with
| PF : rt_pres_fp (rt_live RT ?Σ) (rt_frames RT ?Σ) ?U0 _ _ _ |- _ =>
let NFL := fresh "NFL" in
pose proof (fun a (Ha : aclient (rt_live RT Σ) (rt_frames RT Σ) U0 a) =>
flag_not_client RT Σ Σ1 f k U0 fl a EF EL NAC ltac:(ulc) Ha) as NFL
| _ => idtac
end
end
end.

Ltac cps_release_done REL MU WM FLG :=
lazymatch type of MU with
| munch _ ?m ?m' =>
let A := fresh "ART" in let EF := fresh "EF" in let EL := fresh "EL" in let ES := fresh "ES" in let EC := fresh "EC" in
let AL := fresh "AL" in let AM := fresh "AM" in let EP := fresh "EP" in
destruct (REL m' MU WM FLG) as (A & EF & EL & ES & EC & AL & AM & EP);
cps_pf_seg m m' MU;
try match goal with A0 : ART _ _ m |- _ => clear A0 end;
lazymatch type of MU with munch [(?fl, _)] _ _ =>
repeat match goal with
| H : rw_cells asegs m fl _ |- _ => clear H
| H : ro_cells asegs m _ [C8 (Z_to_bv 64 fl)] |- _ => clear H
end
end;
seg_transport m m' MU WM;
lazymatch goal with
| Hc : ASTA ?RT ?Σ1 ?PMc ?Pm ?c |- _ =>
let Hc' := fresh "Hc" in
lazymatch type of A with ART RT ?Σ2 _ => pose proof (ASTA_switch RT Σ1 Σ2 PMc Pm c Hc AL AM) as Hc' end; clear Hc
end
end.
