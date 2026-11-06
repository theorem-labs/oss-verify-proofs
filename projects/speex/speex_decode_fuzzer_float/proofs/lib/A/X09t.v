(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s
X0ae X09j X09m X09p X09l X09s.
From stdpp Require list_basics.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0wl X110 X106 X109 X10c X108 X10f.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X106 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X109 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X108 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10f.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments skipn {A} n l : simpl nomatch.
#[local] Arguments firstn {A} n l : simpl nomatch.

Definition body_expand_res (os : stream_st bptr) (needed : Z) : stream_st bptr :=
if os_body_fill os <? os_body_storage os - needed then os
else set_blocks os (Some tt) (os_body_storage os + needed + 1024) (os_lacing_vals os) (os_granule_vals os) (os_lacing_storage os).

Lemma body_expand_prun : forall (os : stream_st unit) needed q r q',
prun (os_body_expand (St := pst) p_realloc p_free os needed) q = Some (r, q') ->
os_body_data os <> None -> 0 <= needed -> 0 <= os_body_storage os -> os_body_storage os + needed + 1024 < 2^62 ->
r = (0, body_expand_res os needed) /\ q' = q.
Proof.
intros os needed q r q' H BD N0 S0 NB. unfold os_body_expand in H. unfold body_expand_res, bptr in *.
destruct (os_body_fill os <? os_body_storage os - needed).
- rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
- replace (LONG_MAX - needed <? os_body_storage os) with false in H by (symmetry; apply Z.ltb_ge; unfold LONG_MAX; lia).
replace (os_body_storage os + needed <? LONG_MAX - 1024) with true in H by (symmetry; apply Z.ltb_lt; unfold LONG_MAX; lia).
destruct (os_body_data os) as [[]|]; [| exfalso; apply BD; reflexivity].
rewrite prun_bind, (prun_realloc_ok tt) in H by (unfold p_overflows; apply Z.leb_gt; lia).
cbn beta iota in H. rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
Qed.

Definition lacing_expand_res (os : stream_st bptr) (needed : Z) : stream_st bptr :=
if os_lacing_fill os <? os_lacing_storage os - needed then os
else set_blocks os (os_body_data os) (os_body_storage os) (Some tt) (Some tt) (os_lacing_storage os + needed + 32).

Lemma lacing_expand_prun : forall (os : stream_st unit) needed q r q',
prun (os_lacing_expand (St := pst) p_realloc p_free os needed) q = Some (r, q') ->
os_lacing_vals os <> None -> os_granule_vals os <> None -> 0 <= needed -> 0 <= os_lacing_storage os -> os_lacing_storage os + needed + 32 < 2^58 ->
r = (0, lacing_expand_res os needed) /\ q' = q.
Proof.
intros os needed q r q' H LD GD N0 S0 NB. unfold os_lacing_expand in H. unfold lacing_expand_res, bptr in *.
destruct (os_lacing_fill os <? os_lacing_storage os - needed).
- rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
- replace (LONG_MAX - needed <? os_lacing_storage os) with false in H by (symmetry; apply Z.ltb_ge; unfold LONG_MAX; lia).
replace (os_lacing_storage os + needed <? LONG_MAX - 32) with true in H by (symmetry; apply Z.ltb_lt; unfold LONG_MAX; lia).
destruct (os_lacing_vals os) as [[]|]; [| exfalso; apply LD; reflexivity].
destruct (os_granule_vals os) as [[]|]; [| exfalso; apply GD; reflexivity].
rewrite prun_bind, (prun_realloc_ok tt) in H by (unfold p_overflows, SIZEOF_INT; apply Z.leb_gt; lia).
cbn beta iota in H.
rewrite prun_bind, (prun_realloc_ok tt) in H by (unfold p_overflows, SIZEOF_INT64; apply Z.leb_gt; lia).
cbn beta iota in H. rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
Qed.

Section OggExpandCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis REA : realloc_contract RT.

Lemma stream_cells_x_eq : forall Bd L G hdr (os : stream_st bptr),
stream_cells Bd L G hdr os = stream_cells_x Bd (os_body_storage os) L G (os_lacing_storage os) hdr os.
Proof. reflexivity. Qed.

Definition os_body_expand_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A Bd L G needed f lo : Z) (k : nat) (os : stream_st bptr) (hdr bodybytes : list byte),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 needed -> tp = Z_to_bv 64 0x638c98 ->
rw_cells bsegs m A (stream_cells Bd L G hdr os) -> length hdr = 284%nat -> 0 < A ->
u8arr bsegs m Bd bodybytes -> Z.of_nat (length bodybytes) = os_body_storage os ->
In (Bd, os_body_storage os) (rt_live RT Σ) ->
0 <= os_body_fill os <= os_body_storage os -> 0 <= needed -> os_body_storage os + needed + 1024 <= 64512 ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 408 <= f + fs_size k - 8 ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ ->
ART RT Σ m -> mem_inv bsegs m ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 112 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_os_body_expand m)))
(fun c => exists (Σ' : rts RT) (Bd' : Z),
ASTA RT Σ' PMc (fun ms => exists m' (bodybytes' : list byte),
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (live_remove Bd (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 408)] m m'
/\ rw_cells bsegs m' A (stream_cells Bd' L G hdr (body_expand_res os needed))
/\ u8arr bsegs m' Bd' bodybytes' /\ Z.of_nat (length bodybytes') = os_body_storage (body_expand_res os needed)
/\ firstn (length bodybytes) bodybytes' = bodybytes) c
/\ In (Bd', os_body_storage (body_expand_res os needed)) (rt_live RT Σ')
/\ ((os_body_fill os < os_body_storage os - needed /\ Bd' = Bd /\ rt_live RT Σ' = rt_live RT Σ)
\/ (os_body_storage os - needed <= os_body_fill os
/\ rt_live RT Σ' = (Bd', os_body_storage os + needed + 1024) :: live_remove Bd (rt_live RT Σ)))
/\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem os_body_expand_ok : os_body_expand_cps.
Proof using AF REA.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A Bd L G needed f lo k os hdr bodybytes
FDO MST -> -> -> OS LH A0 ARR LEN INL FLS ND NB INF FA1 FA2 LVM CR0 ART0 MI0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
pose proof (frame_facts RT AF Σ m f k ART0 INF) as (F0 & F64 & FIMG & _ & _ & _ & _ & _ & _ & _).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (LOU : rt_sp0 RT Σ - STACK_WIN <= usp) by (clear - LOW LOR; unfold RT_STACK in *; lia).
assert (AR : 0 < A < 2^64) by (clear - A0 FA2 BF1 LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; clear - LOR SPT BF3; unfold RT_STACK, USTACK_TOP, SH_HI in *; lia).
set (bst := os_body_storage os) in *.
destruct (live_below_lo RT AF Σ m Bd bst lo ART0 INL LOW) as (BD0 & BD1 & _).
destruct (frame_live_apart RT AF Σ m f k Bd bst ART0 INF INL) as (FLB & _).
assert (SEPB : Bd + bst <= A \/ A + 408 <= Bd) by (clear - FLB FA1 FA2; lia).
assert (BR : 0 < Bd < 2^64) by (clear - BD0 BD1 FLS LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
pose proof (pres_fp_refl (live_remove Bd (rt_live RT Σ)) (rt_frames RT Σ) usp [(A, A + 408)] m) as PF.
assert (SUBLV : forall e, In e (live_remove Bd (rt_live RT Σ)) -> In e (rt_live RT Σ)) by (intros e He; exact (live_remove_sub _ _ _ He)).
assert (SPL : forall a, aclient (live_remove Bd (rt_live RT Σ)) (rt_frames RT Σ) usp a -> usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN).
{ intros a Ha. apply (aclient_split RT AF Σ m usp a ART0). apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact SUBLV| auto| apply Z.le_refl]. }
rewrite stream_cells_x_eq in OS. fold bst in OS. unfold stream_cells_x in OS.
apply u8arr_rw_CB in ARR.
unfold body_expand_res in Hk. fold bst in Hk.
assert (R1 : 0 <= bst < 2^61) by (clear - NB ND FLS; lia).
assert (R2 : 0 <= os_body_fill os < 2^61) by (clear - NB ND FLS; lia).
assert (R3 : 0 <= needed < 2^61) by (clear - NB ND FLS; lia).
destruct (Z_lt_ge_dec (os_body_fill os) (bst - needed)) as [ROOM|GROW].
-
replace (os_body_fill os <? bst - needed) with true in Hk by (symmetry; apply Z.ltb_lt; exact ROOM).
cps_norm. cps_hide.
cps_seg (be_w0 A Bd bst L G (os_lacing_storage os) needed usp lo hdr os).
destruct POST as (m1 & a1' & a2' & a3' & -> & MU1 & WM1 & MI1 & ST1).
cps_seg_post.
apply Hk. exists Σ, Bd. split.
2:{ split; [exact INL|]. split; [left; split; [exact ROOM| split; reflexivity]|]. repeat split; reflexivity. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m1, bodybytes.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split; [exact (conj ART (conj MI1 ST1))|]. split; [exact PF|].
split; [rewrite stream_cells_x_eq; exact OS|]. apply u8arr_rw_CB in ARR.
split; [exact ARR|]. split; [exact LEN|]. apply firstn_all.
-
replace (os_body_fill os <? bst - needed) with false in Hk by (symmetry; apply Z.ltb_ge; lia).
cbn [set_blocks os_body_storage] in Hk.
set (ns := bst + needed + 1024) in *.
assert (NS : 1 <= ns <= 64512) by (unfold ns; clear - NB ND FLS; lia).
assert (BY0 : bytes_at bsegs m Bd bodybytes) by (destruct ARR as [[_ B] _]; cbn [cells_bytes cbytes] in B; rewrite app_nil_r in B; exact B).
cps_norm. cps_hide.
cps_seg (be_w1 A Bd bst L G (os_lacing_storage os) needed usp lo hdr os).
destruct POST as (m1 & s1' & a2' & a3' & -> & MU1 & WM1 & MI1 & ST1 & FR1). unfold exp_frame in FR1.
cps_seg_post.
cps_rt (REA Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 Bd bst ns lo bodybytes).
all: [> lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- unwind_ch _ _ _ _ => apply unwind_ok_ch; unfold unwind_ok, RA_be_realloc; rewrite EU, !unsigned_lit by (clear - AR; lia);
split; [unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right])| left; ulc]
| |- mcost _ <= _ => unfold mcost; replace (ns <=? 64512) with true by (symmetry; apply Z.leb_le; lia); exact CR0
| |- _ + _ + 80 <= _ => rewrite EU; ulc
| |- _ => first [ exact BY0 | exact LEN | exact LVM | lia ]
end .. | ].
intros kc3 (Σ1 & q & Hc3 & LV1 & FRS1 & SP1 & CR1 & Q0 & Q16 & QND & QTOP & PO1).
cps_unpack Hc3 as (m3 & RS3 & (ART3 & MI3 & ST3) & PRES3 & WRQ & ACQ & BYQ).
rewrite Z.min_l, <- LEN, Nat2Z.id, firstn_all in BYQ by lia.
destruct (fresh_block_u8arr m3 q ns bodybytes WRQ ltac:(lia) BYQ ltac:(lia)) as (junk & ARQ & LQ).
apply u8arr_rw_CB in ARQ.
pose proof LQ as LQ'. rewrite length_app, Nat2Z.inj_add in LQ'.
cps_sigma LV1 FRS1 SP1.
destruct (live_below_lo RT AF Σ1 m3 q ns lo ART3 INL LOW) as (_ & BQ1 & _).
destruct (frame_live_apart RT AF Σ1 m3 f k q ns ART3 INF INL) as (FLQ & _).
assert (SEPQ : q + ns <= A \/ A + 408 <= q) by (clear - FLQ FA1 FA2; lia).
assert (QR : 0 < q < 2^64) by (clear - Q0 BQ1 NS LOR SPT; lia).
cps_hide.
cps_seg (be_w2 A Bd bst L G (os_lacing_storage os) q ns usp lo hdr os).
destruct POST as (m4 & -> & MU4 & WM4 & MI4 & ST4 & OS4). unfold stream_cells_x in OS4.
clear FR1 OS. cps_seg_post.
apply Hk. exists Σ1, q. split.
2:{ split; [exact INL|]. split; [right; split; [lia| exact LV1]|].
split; [exact FRS1|]. split; [exact SP1|]. split; [| exact PO1].
rewrite CR1. unfold mcost. replace (ns <=? 64512) with true by (symmetry; apply Z.leb_le; lia). apply Z.sub_0_r. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m4, (bodybytes ++ junk).
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split; [exact (conj ART (conj MI4 ST4))|]. split; [exact PF|].
split; [exact OS4|]. apply u8arr_rw_CB in ARQ.
split; [exact ARQ|]. split; [exact LQ|].
rewrite firstn_app, Nat.sub_diag, firstn_all. cbn [firstn]. apply app_nil_r.
Qed.

Lemma live_remove_cons_ne : forall p e (l : list (Z * Z)), fst e <> p -> live_remove p (e :: l) = e :: live_remove p l.
Proof.
intros p e l H. unfold live_remove. apply stdpp.list_basics.list.filter_cons_True.
replace (fst e =? p) with false by (symmetry; apply Z.eqb_neq; exact H). exact I.
Qed.

Lemma live_remove_length_lt : forall p n (l : list (Z * Z)), In (p, n) l -> (length (live_remove p l) < length l)%nat.
Proof.
intros p n l H. unfold live_remove. apply (stdpp.list_basics.list.length_filter_lt _ l (p, n)).
- apply stdpp.base.list_elem_of_In. exact H.
- cbn [fst]. rewrite Z.eqb_refl. exact id.
Qed.

Definition os_lacing_expand_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A Bd L G needed f lo : Z) (k : nat) (os : stream_st bptr) (hdr : list byte) (lws gws : list word),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 needed -> tp = Z_to_bv 64 0x638c98 ->
rw_cells bsegs m A (stream_cells Bd L G hdr os) -> length hdr = 284%nat -> 0 < A ->
u32arr bsegs m L lws -> Z.of_nat (length lws) = os_lacing_storage os ->
u64arr bsegs m G gws -> Z.of_nat (length gws) = os_lacing_storage os ->
In (L, 4 * os_lacing_storage os) (rt_live RT Σ) -> In (G, 8 * os_lacing_storage os) (rt_live RT Σ) -> L <> G ->
0 <= os_lacing_fill os <= os_lacing_storage os -> 0 < os_lacing_storage os -> 0 <= needed -> 8 * (os_lacing_storage os + needed + 32) <= 64512 ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 408 <= f + fs_size k - 8 ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ ->
ART RT Σ m -> mem_inv bsegs m ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 112 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_os_lacing_expand m)))
(fun c => exists (Σ' : rts RT) (L' G' : Z),
ASTA RT Σ' PMc (fun ms => exists m' (lws' gws' : list word),
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (live_remove G (live_remove L (rt_live RT Σ))) (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 408)] m m'
/\ rw_cells bsegs m' A (stream_cells Bd L' G' hdr (lacing_expand_res os needed))
/\ u32arr bsegs m' L' lws' /\ Z.of_nat (length lws') = os_lacing_storage (lacing_expand_res os needed) /\ firstn (length lws) lws' = lws
/\ u64arr bsegs m' G' gws' /\ Z.of_nat (length gws') = os_lacing_storage (lacing_expand_res os needed) /\ firstn (length gws) gws' = gws) c
/\ In (L', 4 * os_lacing_storage (lacing_expand_res os needed)) (rt_live RT Σ')
/\ In (G', 8 * os_lacing_storage (lacing_expand_res os needed)) (rt_live RT Σ') /\ L' <> G'
/\ ((os_lacing_fill os < os_lacing_storage os - needed /\ L' = L /\ G' = G /\ rt_live RT Σ' = rt_live RT Σ)
\/ (os_lacing_storage os - needed <= os_lacing_fill os
/\ rt_live RT Σ' = (G', 8 * (os_lacing_storage os + needed + 32)) :: (L', 4 * (os_lacing_storage os + needed + 32))
:: live_remove G (live_remove L (rt_live RT Σ))))
/\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem os_lacing_expand_ok : os_lacing_expand_cps.
Proof using AF REA.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A Bd L G needed f lo k os hdr lws gws
FDO MST -> -> -> OS LH A0 ARL LENL ARG LENG INLL INLG NLG FLS LS0 ND NB INF FA1 FA2 LVM CR0 ART0 MI0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
pose proof (frame_facts RT AF Σ m f k ART0 INF) as (F0 & F64 & FIMG & _ & _ & _ & _ & _ & _ & _).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (LOU : rt_sp0 RT Σ - STACK_WIN <= usp) by (clear - LOW LOR; unfold RT_STACK in *; lia).
assert (AR : 0 < A < 2^64) by (clear - A0 FA2 BF1 LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; clear - LOR SPT BF3; unfold RT_STACK, USTACK_TOP, SH_HI in *; lia).
set (lst := os_lacing_storage os) in *.
destruct (live_below_lo RT AF Σ m L (4 * lst) lo ART0 INLL LOW) as (BL0 & BL1 & _).
destruct (live_below_lo RT AF Σ m G (8 * lst) lo ART0 INLG LOW) as (BG0 & BG1 & _).
destruct (frame_live_apart RT AF Σ m f k L (4 * lst) ART0 INF INLL) as (FLL & _).
destruct (frame_live_apart RT AF Σ m f k G (8 * lst) ART0 INF INLG) as (FLG & _).
assert (SEPL : L + 4 * lst <= A \/ A + 408 <= L) by (clear - FLL FA1 FA2; lia).
assert (SEPG : G + 8 * lst <= A \/ A + 408 <= G) by (clear - FLG FA1 FA2; lia).
assert (LR : 0 < L < 2^64) by (clear - BL0 BL1 FLS LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
assert (GR : 0 < G < 2^64) by (clear - BG0 BG1 FLS LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
set (LV2 := live_remove G (live_remove L (rt_live RT Σ))) in *.
pose proof (pres_fp_refl LV2 (rt_frames RT Σ) usp [(A, A + 408)] m) as PF.
assert (SUBLV : forall e, In e LV2 -> In e (rt_live RT Σ)) by (intros e He; unfold LV2 in He; do 2 apply live_remove_sub in He; exact He).
assert (SPL : forall a, aclient LV2 (rt_frames RT Σ) usp a -> usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN).
{ intros a Ha. apply (aclient_split RT AF Σ m usp a ART0). apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact SUBLV| auto| apply Z.le_refl]. }
rewrite stream_cells_x_eq in OS. fold lst in OS. unfold stream_cells_x in OS.
unfold lacing_expand_res in Hk. fold lst in Hk.
assert (R1 : 0 <= lst < 2^58) by (clear - NB ND FLS; lia).
assert (R2 : 0 <= os_lacing_fill os < 2^58) by (clear - NB ND FLS; lia).
assert (R3 : 0 <= needed < 2^58) by (clear - NB ND FLS; lia).
assert (LBL : Z.of_nat (length (u32s lws)) = 4 * lst) by (rewrite u32s_length; lia).
assert (LBG : Z.of_nat (length (u64s gws)) = 8 * lst) by (rewrite u64s_length; lia).
apply u32arr_u8, u8arr_rw_CB in ARL. apply u64arr_u8, u8arr_rw_CB in ARG.
destruct (Z_lt_ge_dec (os_lacing_fill os) (lst - needed)) as [ROOM|GROW].
-
replace (os_lacing_fill os <? lst - needed) with true in Hk by (symmetry; apply Z.ltb_lt; exact ROOM).
assert (R1' : 0 <= lst < 2^61) by lia. assert (R2' : 0 <= os_lacing_fill os < 2^61) by lia. assert (R3' : 0 <= needed < 2^61) by lia.
cps_norm. cps_hide.
cps_seg (le_w0 A Bd (os_body_storage os) L G lst needed usp lo hdr os).
destruct POST as (m1 & a1' & a2' & a3' & -> & MU1 & WM1 & MI1 & ST1).
cps_seg_post.
apply Hk. exists Σ, L, G. split.
2:{ split; [exact INLL|]. split; [exact INLG|]. split; [exact NLG|]. split; [left; split; [exact ROOM| repeat split; reflexivity]|]. repeat split; reflexivity. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m1, lws, gws.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split; [exact (conj ART (conj MI1 ST1))|]. split; [exact PF|].
split; [rewrite stream_cells_x_eq; exact OS|].
apply u8arr_rw_CB, u8_u32arr in ARL. apply u8arr_rw_CB, u8_u64arr in ARG.
split; [exact ARL|]. split; [exact LENL|]. split; [apply firstn_all|]. split; [exact ARG|]. split; [exact LENG| apply firstn_all].
-
replace (os_lacing_fill os <? lst - needed) with false in Hk by (symmetry; apply Z.ltb_ge; lia).
cbn [set_blocks os_lacing_storage] in Hk.
set (ns := lst + needed + 32) in *.
assert (NS : 1 <= ns /\ 8 * ns <= 64512) by (unfold ns; clear - NB ND FLS; lia).
assert (BYL : bytes_at bsegs m L (u32s lws)) by (destruct ARL as [[_ B] _]; cbn [cells_bytes cbytes] in B; rewrite app_nil_r in B; exact B).
assert (INLG' : In (G, 8 * lst) (live_remove L (rt_live RT Σ))) by (apply live_remove_keep; [exact INLG| cbn [fst]; congruence]).
assert (SUB1 : forall e, In e LV2 -> In e (live_remove L (rt_live RT Σ))) by (intros e He; unfold LV2 in He; apply live_remove_sub in He; exact He).
cps_norm. cps_hide.
cps_seg (le_w1 A Bd (os_body_storage os) L G lst needed usp lo hdr os).
destruct POST as (m1 & s1' & a2' & a3' & -> & MU1 & WM1 & MI1 & ST1 & FR1). unfold exp_frame in FR1.
cps_seg_post.
cps_rt (REA Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 L (4 * lst) (4 * ns) lo (u32s lws)).
all: [> lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- unwind_ch _ _ _ _ => apply unwind_ok_ch; unfold unwind_ok, RA_le_realloc1; rewrite EU, !unsigned_lit by (clear - AR; lia);
split; [unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right])| left; ulc]
| |- mcost _ <= _ => unfold mcost; replace (4 * ns <=? 64512) with true by (symmetry; apply Z.leb_le; lia); exact CR0
| |- _ + _ + 80 <= _ => rewrite EU; ulc
| |- _ => first [ exact BYL | exact LBL | exact LVM | lia ]
end .. | ].
intros kc3 (Σ1 & q1 & Hc3 & LV1 & FRS1 & SP1 & CR1 & Q0 & Q16 & QND & QTOP & PO1).
cps_unpack Hc3 as (m3 & RS3 & (ART3 & MI3 & ST3) & PRES3 & WRQ & ACQ & BYQ).
rewrite Z.min_l, <- LBL, Nat2Z.id, firstn_all in BYQ by lia.
destruct (fresh_block_u8arr m3 q1 (4 * ns) (u32s lws) WRQ ltac:(lia) BYQ ltac:(lia)) as (junk1 & ARQ1 & LQ1).
apply u8arr_rw_CB in ARQ1.
pose proof LQ1 as LQ1'. rewrite length_app, Nat2Z.inj_add in LQ1'.
assert (INQ1 : In (q1, 4 * ns) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
assert (ING1 : In (G, 8 * lst) (rt_live RT Σ1)) by (rewrite LV1; right; exact INLG').
pose proof (af_live_disj RT AF Σ1 m3 q1 (4 * ns) G (8 * lst) [] _ ART3 LV1 INLG') as DQG.
assert (NQG : q1 <> G) by (clear - DQG NS LS0; lia).
assert (EL1 : live_remove G (rt_live RT Σ1) = (q1, 4 * ns) :: LV2) by (rewrite LV1; apply live_remove_cons_ne; cbn [fst]; exact NQG).
assert (INQ1' : In (q1, 4 * ns) (live_remove G (rt_live RT Σ1))) by (rewrite EL1; left; reflexivity).
assert (SUB2 : forall e, In e LV2 -> In e (live_remove G (rt_live RT Σ1))) by (intros e He; rewrite EL1; right; exact He).
assert (INLL0 : id (In (L, 4 * lst) (rt_live RT Σ))) by exact INLL.
clear INLL INLG INLG'.
ogg_sigma_free FRS1 SP1.
destruct (live_below_lo RT AF Σ1 m3 q1 (4 * ns) lo ART3 INQ1 LOW) as (_ & BQ1 & _).
destruct (frame_live_apart RT AF Σ1 m3 f k q1 (4 * ns) ART3 INF INQ1) as (FLQ1 & _).
assert (SEPQ1 : q1 + 4 * ns <= A \/ A + 408 <= q1) by (clear - FLQ1 FA1 FA2; lia).
assert (QR1 : 0 < q1 < 2^64) by (clear - Q0 BQ1 NS LOR SPT; lia).
assert (NS' : 0 <= ns < 2^58) by (clear - NS; lia).
cps_hide.

cps_seg (le_w2 A Bd (os_body_storage os) L G lst q1 ns hdr os).
destruct POST as (m4 & a2x & -> & MU4 & WM4 & MI4 & OS4). unfold stream_cells_x in OS4.
clear OS. cps_seg_post.
assert (BYG : bytes_at bsegs m4 G (u64s gws)) by (destruct ARG as [[_ B] _]; cbn [cells_bytes cbytes] in B; rewrite app_nil_r in B; exact B).
cps_rt (REA Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 G (8 * lst) (8 * ns) lo (u64s gws)).
all: [> lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- unwind_ch _ _ _ _ => apply unwind_ok_ch; unfold unwind_ok, RA_le_realloc2; rewrite EU, !unsigned_lit by (clear - AR; lia);
split; [unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right])| left; ulc]
| |- mcost _ <= _ => unfold mcost; replace (8 * ns <=? 64512) with true by (symmetry; apply Z.leb_le; lia);
rewrite CR1; unfold mcost; replace (4 * ns <=? 64512) with true by (symmetry; apply Z.leb_le; lia); clear - CR0; lia
| |- Z.of_nat (length _) < _ => rewrite LV1; cbn [length]; pose proof (live_remove_length_lt L _ _ INLL0) as LL; clear - LL LVM; lia
| |- _ + _ + 80 <= _ => rewrite EU; ulc
| |- _ => first [ exact BYG | exact LBG | exact ING1 | lia ]
end .. | ].
intros kc5 (Σ2 & q2 & Hc5 & LV2' & FRS2 & SP2 & CR2 & Q20 & Q216 & Q2ND & Q2TOP & PO2).
cps_unpack Hc5 as (m5 & RS5 & (ART5 & MI5 & ST5) & PRES5 & WRQ2 & ACQ2 & BYQ2).
rewrite Z.min_l, <- LBG, Nat2Z.id, firstn_all in BYQ2 by lia.
destruct (fresh_block_u8arr m5 q2 (8 * ns) (u64s gws) WRQ2 ltac:(lia) BYQ2 ltac:(lia)) as (junk2 & ARQ2 & LQ2).
apply u8arr_rw_CB in ARQ2.
pose proof LQ2 as LQ2'. rewrite length_app, Nat2Z.inj_add in LQ2'.
rewrite EL1 in LV2'.
assert (INQ2 : In (q2, 8 * ns) (rt_live RT Σ2)) by (rewrite LV2'; left; reflexivity).
assert (INQ12 : In (q1, 4 * ns) (rt_live RT Σ2)) by (rewrite LV2'; right; left; reflexivity).
pose proof (af_live_disj RT AF Σ2 m5 q2 (8 * ns) q1 (4 * ns) [] _ ART5 LV2' ltac:(left; reflexivity)) as DQ12.
assert (NQ12 : q1 <> q2) by (clear - DQ12 NS; lia).
clear INQ1 ING1 INQ1'.
ogg_sigma_free FRS2 SP2.
destruct (live_below_lo RT AF Σ2 m5 q2 (8 * ns) lo ART5 INQ2 LOW) as (_ & BQ2 & _).
destruct (frame_live_apart RT AF Σ2 m5 f k q2 (8 * ns) ART5 INF INQ2) as (FLQ2 & _).
assert (SEPQ2 : q2 + 8 * ns <= A \/ A + 408 <= q2) by (clear - FLQ2 FA1 FA2; lia).
assert (QR2 : 0 < q2 < 2^64) by (clear - Q20 BQ2 NS LOR SPT; lia).
cps_hide.

cps_seg (le_w3 A Bd (os_body_storage os) q1 G lst q2 ns usp lo hdr os).
destruct POST as (m6 & -> & MU6 & WM6 & MI6 & ST6 & OS6). unfold stream_cells_x in OS6.
clear FR1 OS4. cps_seg_post.
apply Hk. exists Σ2, q1, q2. split.
2:{ split; [exact INQ12|]. split; [exact INQ2|]. split; [exact NQ12|]. split; [right; split; [lia| exact LV2']|].
split; [congruence|]. split; [congruence|]. split; [| congruence].
rewrite CR2, CR1. unfold mcost. replace (8 * ns <=? 64512) with true by (symmetry; apply Z.leb_le; lia).
replace (4 * ns <=? 64512) with true by (symmetry; apply Z.leb_le; lia). lia. }
eapply ASTA_conseq; [eassumption|]. intros ms <-.
destruct (chunk_u32arr m6 q1 lws junk1 ns _ ARQ1 ltac:(apply Nat2Z.inj; rewrite LQ1, Z2Nat.id by lia; lia) ltac:(lia) ltac:(lia)) as (lwx & ARL' & LLW).
destruct (chunk_u64arr m6 q2 gws junk2 ns _ ARQ2 ltac:(apply Nat2Z.inj; rewrite LQ2, Z2Nat.id by lia; lia) ltac:(lia) ltac:(lia)) as (gwx & ARG' & LGW).
exists m6, (lws ++ lwx), (gws ++ gwx).
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split; [exact (conj ART (conj MI6 ST6))|]. split; [exact PF|].
split; [exact OS6|].
split; [exact ARL'|]. split; [exact LLW|]. split; [rewrite firstn_app, Nat.sub_diag, firstn_all; cbn [firstn]; apply app_nil_r|].
split; [exact ARG'|]. split; [exact LGW|]. rewrite firstn_app, Nat.sub_diag, firstn_all. cbn [firstn]. apply app_nil_r.
Qed.
End OggExpandCPS.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments skipn {A} n l : simpl nomatch.
#[local] Arguments firstn {A} n l : simpl nomatch.

Definition body_expand_res (os : stream_st bptr) (needed : Z) : stream_st bptr :=
if os_body_fill os <? os_body_storage os - needed then os
else set_blocks os (Some tt) (os_body_storage os + needed + 1024) (os_lacing_vals os) (os_granule_vals os) (os_lacing_storage os).

Lemma body_expand_prun : forall (os : stream_st unit) needed q r q',
prun (os_body_expand (St := pst) p_realloc p_free os needed) q = Some (r, q') ->
os_body_data os <> None -> 0 <= needed -> 0 <= os_body_storage os -> os_body_storage os + needed + 1024 < 2^62 ->
r = (0, body_expand_res os needed) /\ q' = q.
Proof.
intros os needed q r q' H BD N0 S0 NB. unfold os_body_expand in H. unfold body_expand_res, bptr in *.
destruct (os_body_fill os <? os_body_storage os - needed).
- rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
- replace (LONG_MAX - needed <? os_body_storage os) with false in H by (symmetry; apply Z.ltb_ge; unfold LONG_MAX; lia).
replace (os_body_storage os + needed <? LONG_MAX - 1024) with true in H by (symmetry; apply Z.ltb_lt; unfold LONG_MAX; lia).
destruct (os_body_data os) as [[]|]; [| exfalso; apply BD; reflexivity].
rewrite prun_bind, (prun_realloc_ok tt) in H by (unfold p_overflows; apply Z.leb_gt; lia).
cbn beta iota in H. rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
Qed.

Definition lacing_expand_res (os : stream_st bptr) (needed : Z) : stream_st bptr :=
if os_lacing_fill os <? os_lacing_storage os - needed then os
else set_blocks os (os_body_data os) (os_body_storage os) (Some tt) (Some tt) (os_lacing_storage os + needed + 32).

Lemma lacing_expand_prun : forall (os : stream_st unit) needed q r q',
prun (os_lacing_expand (St := pst) p_realloc p_free os needed) q = Some (r, q') ->
os_lacing_vals os <> None -> os_granule_vals os <> None -> 0 <= needed -> 0 <= os_lacing_storage os -> os_lacing_storage os + needed + 32 < 2^58 ->
r = (0, lacing_expand_res os needed) /\ q' = q.
Proof.
intros os needed q r q' H LD GD N0 S0 NB. unfold os_lacing_expand in H. unfold lacing_expand_res, bptr in *.
destruct (os_lacing_fill os <? os_lacing_storage os - needed).
- rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
- replace (LONG_MAX - needed <? os_lacing_storage os) with false in H by (symmetry; apply Z.ltb_ge; unfold LONG_MAX; lia).
replace (os_lacing_storage os + needed <? LONG_MAX - 32) with true in H by (symmetry; apply Z.ltb_lt; unfold LONG_MAX; lia).
destruct (os_lacing_vals os) as [[]|]; [| exfalso; apply LD; reflexivity].
destruct (os_granule_vals os) as [[]|]; [| exfalso; apply GD; reflexivity].
rewrite prun_bind, (prun_realloc_ok tt) in H by (unfold p_overflows, SIZEOF_INT; apply Z.leb_gt; lia).
cbn beta iota in H.
rewrite prun_bind, (prun_realloc_ok tt) in H by (unfold p_overflows, SIZEOF_INT64; apply Z.leb_gt; lia).
cbn beta iota in H. rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
Qed.

Section OggExpandCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis REA : realloc_contract RT.

Lemma stream_cells_x_eq : forall Bd L G hdr (os : stream_st bptr),
stream_cells Bd L G hdr os = stream_cells_x Bd (os_body_storage os) L G (os_lacing_storage os) hdr os.
Proof. reflexivity. Qed.

Definition os_body_expand_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A Bd L G needed f lo : Z) (k : nat) (os : stream_st bptr) (hdr bodybytes : list byte),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 needed -> tp = Z_to_bv 64 0x630458 ->
rw_cells asegs m A (stream_cells Bd L G hdr os) -> length hdr = 284%nat -> 0 < A ->
u8arr asegs m Bd bodybytes -> Z.of_nat (length bodybytes) = os_body_storage os ->
In (Bd, os_body_storage os) (rt_live RT Σ) ->
0 <= os_body_fill os <= os_body_storage os -> 0 <= needed -> os_body_storage os + needed + 1024 <= 64512 ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 408 <= f + fs_size k - 8 ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ ->
ART RT Σ m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 112 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_os_body_expand m)))
(fun c => exists (Σ' : rts RT) (Bd' : Z),
ASTA RT Σ' PMc (fun ms => exists m' (bodybytes' : list byte),
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (live_remove Bd (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 408)] m m'
/\ rw_cells asegs m' A (stream_cells Bd' L G hdr (body_expand_res os needed))
/\ u8arr asegs m' Bd' bodybytes' /\ Z.of_nat (length bodybytes') = os_body_storage (body_expand_res os needed)
/\ firstn (length bodybytes) bodybytes' = bodybytes) c
/\ In (Bd', os_body_storage (body_expand_res os needed)) (rt_live RT Σ')
/\ ((os_body_fill os < os_body_storage os - needed /\ Bd' = Bd /\ rt_live RT Σ' = rt_live RT Σ)
\/ (os_body_storage os - needed <= os_body_fill os
/\ rt_live RT Σ' = (Bd', os_body_storage os + needed + 1024) :: live_remove Bd (rt_live RT Σ)))
/\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem os_body_expand_ok : os_body_expand_cps.
Proof using AF REA.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A Bd L G needed f lo k os hdr bodybytes
FDO MST -> -> -> OS LH A0 ARR LEN INL FLS ND NB INF FA1 FA2 LVM CR0 ART0 MI0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
pose proof (frame_facts RT AF Σ m f k ART0 INF) as (F0 & F64 & FIMG & _ & _ & _ & _ & _ & _ & _).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (LOU : rt_sp0 RT Σ - STACK_WIN <= usp) by (clear - LOW LOR; unfold RT_STACK in *; lia).
assert (AR : 0 < A < 2^64) by (clear - A0 FA2 BF1 LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; clear - LOR SPT BF3; unfold RT_STACK, USTACK_TOP, SH_HI in *; lia).
set (bst := os_body_storage os) in *.
destruct (live_below_lo RT AF Σ m Bd bst lo ART0 INL LOW) as (BD0 & BD1 & _).
destruct (frame_live_apart RT AF Σ m f k Bd bst ART0 INF INL) as (FLB & _).
assert (SEPB : Bd + bst <= A \/ A + 408 <= Bd) by (clear - FLB FA1 FA2; lia).
assert (BR : 0 < Bd < 2^64) by (clear - BD0 BD1 FLS LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
pose proof (pres_fp_refl (live_remove Bd (rt_live RT Σ)) (rt_frames RT Σ) usp [(A, A + 408)] m) as PF.
assert (SUBLV : forall e, In e (live_remove Bd (rt_live RT Σ)) -> In e (rt_live RT Σ)) by (intros e He; exact (live_remove_sub _ _ _ He)).
assert (SPL : forall a, aclient (live_remove Bd (rt_live RT Σ)) (rt_frames RT Σ) usp a -> usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN).
{ intros a Ha. apply (aclient_split RT AF Σ m usp a ART0). apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact SUBLV| auto| apply Z.le_refl]. }
rewrite stream_cells_x_eq in OS. fold bst in OS. unfold stream_cells_x in OS.
apply u8arr_rw_CB in ARR.
unfold body_expand_res in Hk. fold bst in Hk.
assert (R1 : 0 <= bst < 2^61) by (clear - NB ND FLS; lia).
assert (R2 : 0 <= os_body_fill os < 2^61) by (clear - NB ND FLS; lia).
assert (R3 : 0 <= needed < 2^61) by (clear - NB ND FLS; lia).
destruct (Z_lt_ge_dec (os_body_fill os) (bst - needed)) as [ROOM|GROW].
-
replace (os_body_fill os <? bst - needed) with true in Hk by (symmetry; apply Z.ltb_lt; exact ROOM).
cps_norm. cps_hide.
cps_seg (be_w0 A Bd bst L G (os_lacing_storage os) needed usp lo hdr os).
destruct POST as (m1 & a1' & a2' & a3' & -> & MU1 & WM1 & MI1 & ST1).
cps_seg_post.
apply Hk. exists Σ, Bd. split.
2:{ split; [exact INL|]. split; [left; split; [exact ROOM| split; reflexivity]|]. repeat split; reflexivity. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m1, bodybytes.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split; [exact (conj ART (conj MI1 ST1))|]. split; [exact PF|].
split; [rewrite stream_cells_x_eq; exact OS|]. apply u8arr_rw_CB in ARR.
split; [exact ARR|]. split; [exact LEN|]. apply firstn_all.
-
replace (os_body_fill os <? bst - needed) with false in Hk by (symmetry; apply Z.ltb_ge; lia).
cbn [set_blocks os_body_storage] in Hk.
set (ns := bst + needed + 1024) in *.
assert (NS : 1 <= ns <= 64512) by (unfold ns; clear - NB ND FLS; lia).
assert (BY0 : bytes_at asegs m Bd bodybytes) by (destruct ARR as [[_ B] _]; cbn [cells_bytes cbytes] in B; rewrite app_nil_r in B; exact B).
cps_norm. cps_hide.
cps_seg (be_w1 A Bd bst L G (os_lacing_storage os) needed usp lo hdr os).
destruct POST as (m1 & s1' & a2' & a3' & -> & MU1 & WM1 & MI1 & ST1 & FR1). unfold exp_frame in FR1.
cps_seg_post.
cps_rt (REA Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 Bd bst ns lo bodybytes).
all: [> lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- unwind_ch _ _ _ _ => apply unwind_ok_ch; unfold unwind_ok, RA_be_realloc; rewrite EU, !unsigned_lit by (clear - AR; lia);
split; [unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right])| left; ulc]
| |- mcost _ <= _ => unfold mcost; replace (ns <=? 64512) with true by (symmetry; apply Z.leb_le; lia); exact CR0
| |- _ + _ + 80 <= _ => rewrite EU; ulc
| |- _ => first [ exact BY0 | exact LEN | exact LVM | lia ]
end .. | ].
intros kc3 (Σ1 & q & Hc3 & LV1 & FRS1 & SP1 & CR1 & Q0 & Q16 & QND & QTOP & PO1).
cps_unpack Hc3 as (m3 & RS3 & (ART3 & MI3 & ST3) & PRES3 & WRQ & ACQ & BYQ).
rewrite Z.min_l, <- LEN, Nat2Z.id, firstn_all in BYQ by lia.
destruct (fresh_block_u8arr m3 q ns bodybytes WRQ ltac:(lia) BYQ ltac:(lia)) as (junk & ARQ & LQ).
apply u8arr_rw_CB in ARQ.
pose proof LQ as LQ'. rewrite length_app, Nat2Z.inj_add in LQ'.
cps_sigma LV1 FRS1 SP1.
destruct (live_below_lo RT AF Σ1 m3 q ns lo ART3 INL LOW) as (_ & BQ1 & _).
destruct (frame_live_apart RT AF Σ1 m3 f k q ns ART3 INF INL) as (FLQ & _).
assert (SEPQ : q + ns <= A \/ A + 408 <= q) by (clear - FLQ FA1 FA2; lia).
assert (QR : 0 < q < 2^64) by (clear - Q0 BQ1 NS LOR SPT; lia).
cps_hide.
cps_seg (be_w2 A Bd bst L G (os_lacing_storage os) q ns usp lo hdr os).
destruct POST as (m4 & -> & MU4 & WM4 & MI4 & ST4 & OS4). unfold stream_cells_x in OS4.
clear FR1 OS. cps_seg_post.
apply Hk. exists Σ1, q. split.
2:{ split; [exact INL|]. split; [right; split; [lia| exact LV1]|].
split; [exact FRS1|]. split; [exact SP1|]. split; [| exact PO1].
rewrite CR1. unfold mcost. replace (ns <=? 64512) with true by (symmetry; apply Z.leb_le; lia). apply Z.sub_0_r. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m4, (bodybytes ++ junk).
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split; [exact (conj ART (conj MI4 ST4))|]. split; [exact PF|].
split; [exact OS4|]. apply u8arr_rw_CB in ARQ.
split; [exact ARQ|]. split; [exact LQ|].
rewrite firstn_app, Nat.sub_diag, firstn_all. cbn [firstn]. apply app_nil_r.
Qed.

Lemma live_remove_cons_ne : forall p e (l : list (Z * Z)), fst e <> p -> live_remove p (e :: l) = e :: live_remove p l.
Proof.
intros p e l H. unfold live_remove. apply stdpp.list_basics.list.filter_cons_True.
replace (fst e =? p) with false by (symmetry; apply Z.eqb_neq; exact H). exact I.
Qed.

Lemma live_remove_length_lt : forall p n (l : list (Z * Z)), In (p, n) l -> (length (live_remove p l) < length l)%nat.
Proof.
intros p n l H. unfold live_remove. apply (stdpp.list_basics.list.length_filter_lt _ l (p, n)).
- apply stdpp.base.list_elem_of_In. exact H.
- cbn [fst]. rewrite Z.eqb_refl. exact id.
Qed.

Definition os_lacing_expand_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A Bd L G needed f lo : Z) (k : nat) (os : stream_st bptr) (hdr : list byte) (lws gws : list word),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 needed -> tp = Z_to_bv 64 0x630458 ->
rw_cells asegs m A (stream_cells Bd L G hdr os) -> length hdr = 284%nat -> 0 < A ->
u32arr asegs m L lws -> Z.of_nat (length lws) = os_lacing_storage os ->
u64arr asegs m G gws -> Z.of_nat (length gws) = os_lacing_storage os ->
In (L, 4 * os_lacing_storage os) (rt_live RT Σ) -> In (G, 8 * os_lacing_storage os) (rt_live RT Σ) -> L <> G ->
0 <= os_lacing_fill os <= os_lacing_storage os -> 0 < os_lacing_storage os -> 0 <= needed -> 8 * (os_lacing_storage os + needed + 32) <= 64512 ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 408 <= f + fs_size k - 8 ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ ->
ART RT Σ m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 112 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_os_lacing_expand m)))
(fun c => exists (Σ' : rts RT) (L' G' : Z),
ASTA RT Σ' PMc (fun ms => exists m' (lws' gws' : list word),
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (live_remove G (live_remove L (rt_live RT Σ))) (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 408)] m m'
/\ rw_cells asegs m' A (stream_cells Bd L' G' hdr (lacing_expand_res os needed))
/\ u32arr asegs m' L' lws' /\ Z.of_nat (length lws') = os_lacing_storage (lacing_expand_res os needed) /\ firstn (length lws) lws' = lws
/\ u64arr asegs m' G' gws' /\ Z.of_nat (length gws') = os_lacing_storage (lacing_expand_res os needed) /\ firstn (length gws) gws' = gws) c
/\ In (L', 4 * os_lacing_storage (lacing_expand_res os needed)) (rt_live RT Σ')
/\ In (G', 8 * os_lacing_storage (lacing_expand_res os needed)) (rt_live RT Σ') /\ L' <> G'
/\ ((os_lacing_fill os < os_lacing_storage os - needed /\ L' = L /\ G' = G /\ rt_live RT Σ' = rt_live RT Σ)
\/ (os_lacing_storage os - needed <= os_lacing_fill os
/\ rt_live RT Σ' = (G', 8 * (os_lacing_storage os + needed + 32)) :: (L', 4 * (os_lacing_storage os + needed + 32))
:: live_remove G (live_remove L (rt_live RT Σ))))
/\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem os_lacing_expand_ok : os_lacing_expand_cps.
Proof using AF REA.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A Bd L G needed f lo k os hdr lws gws
FDO MST -> -> -> OS LH A0 ARL LENL ARG LENG INLL INLG NLG FLS LS0 ND NB INF FA1 FA2 LVM CR0 ART0 MI0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
pose proof (frame_facts RT AF Σ m f k ART0 INF) as (F0 & F64 & FIMG & _ & _ & _ & _ & _ & _ & _).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (LOU : rt_sp0 RT Σ - STACK_WIN <= usp) by (clear - LOW LOR; unfold RT_STACK in *; lia).
assert (AR : 0 < A < 2^64) by (clear - A0 FA2 BF1 LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; clear - LOR SPT BF3; unfold RT_STACK, USTACK_TOP, SH_HI in *; lia).
set (lst := os_lacing_storage os) in *.
destruct (live_below_lo RT AF Σ m L (4 * lst) lo ART0 INLL LOW) as (BL0 & BL1 & _).
destruct (live_below_lo RT AF Σ m G (8 * lst) lo ART0 INLG LOW) as (BG0 & BG1 & _).
destruct (frame_live_apart RT AF Σ m f k L (4 * lst) ART0 INF INLL) as (FLL & _).
destruct (frame_live_apart RT AF Σ m f k G (8 * lst) ART0 INF INLG) as (FLG & _).
assert (SEPL : L + 4 * lst <= A \/ A + 408 <= L) by (clear - FLL FA1 FA2; lia).
assert (SEPG : G + 8 * lst <= A \/ A + 408 <= G) by (clear - FLG FA1 FA2; lia).
assert (LR : 0 < L < 2^64) by (clear - BL0 BL1 FLS LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
assert (GR : 0 < G < 2^64) by (clear - BG0 BG1 FLS LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
set (LV2 := live_remove G (live_remove L (rt_live RT Σ))) in *.
pose proof (pres_fp_refl LV2 (rt_frames RT Σ) usp [(A, A + 408)] m) as PF.
assert (SUBLV : forall e, In e LV2 -> In e (rt_live RT Σ)) by (intros e He; unfold LV2 in He; do 2 apply live_remove_sub in He; exact He).
assert (SPL : forall a, aclient LV2 (rt_frames RT Σ) usp a -> usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN).
{ intros a Ha. apply (aclient_split RT AF Σ m usp a ART0). apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact SUBLV| auto| apply Z.le_refl]. }
rewrite stream_cells_x_eq in OS. fold lst in OS. unfold stream_cells_x in OS.
unfold lacing_expand_res in Hk. fold lst in Hk.
assert (R1 : 0 <= lst < 2^58) by (clear - NB ND FLS; lia).
assert (R2 : 0 <= os_lacing_fill os < 2^58) by (clear - NB ND FLS; lia).
assert (R3 : 0 <= needed < 2^58) by (clear - NB ND FLS; lia).
assert (LBL : Z.of_nat (length (u32s lws)) = 4 * lst) by (rewrite u32s_length; lia).
assert (LBG : Z.of_nat (length (u64s gws)) = 8 * lst) by (rewrite u64s_length; lia).
apply u32arr_u8, u8arr_rw_CB in ARL. apply u64arr_u8, u8arr_rw_CB in ARG.
destruct (Z_lt_ge_dec (os_lacing_fill os) (lst - needed)) as [ROOM|GROW].
-
replace (os_lacing_fill os <? lst - needed) with true in Hk by (symmetry; apply Z.ltb_lt; exact ROOM).
assert (R1' : 0 <= lst < 2^61) by lia. assert (R2' : 0 <= os_lacing_fill os < 2^61) by lia. assert (R3' : 0 <= needed < 2^61) by lia.
cps_norm. cps_hide.
cps_seg (le_w0 A Bd (os_body_storage os) L G lst needed usp lo hdr os).
destruct POST as (m1 & a1' & a2' & a3' & -> & MU1 & WM1 & MI1 & ST1).
cps_seg_post.
apply Hk. exists Σ, L, G. split.
2:{ split; [exact INLL|]. split; [exact INLG|]. split; [exact NLG|]. split; [left; split; [exact ROOM| repeat split; reflexivity]|]. repeat split; reflexivity. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m1, lws, gws.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split; [exact (conj ART (conj MI1 ST1))|]. split; [exact PF|].
split; [rewrite stream_cells_x_eq; exact OS|].
apply u8arr_rw_CB, u8_u32arr in ARL. apply u8arr_rw_CB, u8_u64arr in ARG.
split; [exact ARL|]. split; [exact LENL|]. split; [apply firstn_all|]. split; [exact ARG|]. split; [exact LENG| apply firstn_all].
-
replace (os_lacing_fill os <? lst - needed) with false in Hk by (symmetry; apply Z.ltb_ge; lia).
cbn [set_blocks os_lacing_storage] in Hk.
set (ns := lst + needed + 32) in *.
assert (NS : 1 <= ns /\ 8 * ns <= 64512) by (unfold ns; clear - NB ND FLS; lia).
assert (BYL : bytes_at asegs m L (u32s lws)) by (destruct ARL as [[_ B] _]; cbn [cells_bytes cbytes] in B; rewrite app_nil_r in B; exact B).
assert (INLG' : In (G, 8 * lst) (live_remove L (rt_live RT Σ))) by (apply live_remove_keep; [exact INLG| cbn [fst]; congruence]).
assert (SUB1 : forall e, In e LV2 -> In e (live_remove L (rt_live RT Σ))) by (intros e He; unfold LV2 in He; apply live_remove_sub in He; exact He).
cps_norm. cps_hide.
cps_seg (le_w1 A Bd (os_body_storage os) L G lst needed usp lo hdr os).
destruct POST as (m1 & s1' & a2' & a3' & -> & MU1 & WM1 & MI1 & ST1 & FR1). unfold exp_frame in FR1.
cps_seg_post.
cps_rt (REA Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 L (4 * lst) (4 * ns) lo (u32s lws)).
all: [> lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- unwind_ch _ _ _ _ => apply unwind_ok_ch; unfold unwind_ok, RA_le_realloc1; rewrite EU, !unsigned_lit by (clear - AR; lia);
split; [unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right])| left; ulc]
| |- mcost _ <= _ => unfold mcost; replace (4 * ns <=? 64512) with true by (symmetry; apply Z.leb_le; lia); exact CR0
| |- _ + _ + 80 <= _ => rewrite EU; ulc
| |- _ => first [ exact BYL | exact LBL | exact LVM | lia ]
end .. | ].
intros kc3 (Σ1 & q1 & Hc3 & LV1 & FRS1 & SP1 & CR1 & Q0 & Q16 & QND & QTOP & PO1).
cps_unpack Hc3 as (m3 & RS3 & (ART3 & MI3 & ST3) & PRES3 & WRQ & ACQ & BYQ).
rewrite Z.min_l, <- LBL, Nat2Z.id, firstn_all in BYQ by lia.
destruct (fresh_block_u8arr m3 q1 (4 * ns) (u32s lws) WRQ ltac:(lia) BYQ ltac:(lia)) as (junk1 & ARQ1 & LQ1).
apply u8arr_rw_CB in ARQ1.
pose proof LQ1 as LQ1'. rewrite length_app, Nat2Z.inj_add in LQ1'.
assert (INQ1 : In (q1, 4 * ns) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
assert (ING1 : In (G, 8 * lst) (rt_live RT Σ1)) by (rewrite LV1; right; exact INLG').
pose proof (af_live_disj RT AF Σ1 m3 q1 (4 * ns) G (8 * lst) [] _ ART3 LV1 INLG') as DQG.
assert (NQG : q1 <> G) by (clear - DQG NS LS0; lia).
assert (EL1 : live_remove G (rt_live RT Σ1) = (q1, 4 * ns) :: LV2) by (rewrite LV1; apply live_remove_cons_ne; cbn [fst]; exact NQG).
assert (INQ1' : In (q1, 4 * ns) (live_remove G (rt_live RT Σ1))) by (rewrite EL1; left; reflexivity).
assert (SUB2 : forall e, In e LV2 -> In e (live_remove G (rt_live RT Σ1))) by (intros e He; rewrite EL1; right; exact He).
assert (INLL0 : id (In (L, 4 * lst) (rt_live RT Σ))) by exact INLL.
clear INLL INLG INLG'.
ogg_sigma_free FRS1 SP1.
destruct (live_below_lo RT AF Σ1 m3 q1 (4 * ns) lo ART3 INQ1 LOW) as (_ & BQ1 & _).
destruct (frame_live_apart RT AF Σ1 m3 f k q1 (4 * ns) ART3 INF INQ1) as (FLQ1 & _).
assert (SEPQ1 : q1 + 4 * ns <= A \/ A + 408 <= q1) by (clear - FLQ1 FA1 FA2; lia).
assert (QR1 : 0 < q1 < 2^64) by (clear - Q0 BQ1 NS LOR SPT; lia).
assert (NS' : 0 <= ns < 2^58) by (clear - NS; lia).
cps_hide.

cps_seg (le_w2 A Bd (os_body_storage os) L G lst q1 ns hdr os).
destruct POST as (m4 & a2x & -> & MU4 & WM4 & MI4 & OS4). unfold stream_cells_x in OS4.
clear OS. cps_seg_post.
assert (BYG : bytes_at asegs m4 G (u64s gws)) by (destruct ARG as [[_ B] _]; cbn [cells_bytes cbytes] in B; rewrite app_nil_r in B; exact B).
cps_rt (REA Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 G (8 * lst) (8 * ns) lo (u64s gws)).
all: [> lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- unwind_ch _ _ _ _ => apply unwind_ok_ch; unfold unwind_ok, RA_le_realloc2; rewrite EU, !unsigned_lit by (clear - AR; lia);
split; [unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right])| left; ulc]
| |- mcost _ <= _ => unfold mcost; replace (8 * ns <=? 64512) with true by (symmetry; apply Z.leb_le; lia);
rewrite CR1; unfold mcost; replace (4 * ns <=? 64512) with true by (symmetry; apply Z.leb_le; lia); clear - CR0; lia
| |- Z.of_nat (length _) < _ => rewrite LV1; cbn [length]; pose proof (live_remove_length_lt L _ _ INLL0) as LL; clear - LL LVM; lia
| |- _ + _ + 80 <= _ => rewrite EU; ulc
| |- _ => first [ exact BYG | exact LBG | exact ING1 | lia ]
end .. | ].
intros kc5 (Σ2 & q2 & Hc5 & LV2' & FRS2 & SP2 & CR2 & Q20 & Q216 & Q2ND & Q2TOP & PO2).
cps_unpack Hc5 as (m5 & RS5 & (ART5 & MI5 & ST5) & PRES5 & WRQ2 & ACQ2 & BYQ2).
rewrite Z.min_l, <- LBG, Nat2Z.id, firstn_all in BYQ2 by lia.
destruct (fresh_block_u8arr m5 q2 (8 * ns) (u64s gws) WRQ2 ltac:(lia) BYQ2 ltac:(lia)) as (junk2 & ARQ2 & LQ2).
apply u8arr_rw_CB in ARQ2.
pose proof LQ2 as LQ2'. rewrite length_app, Nat2Z.inj_add in LQ2'.
rewrite EL1 in LV2'.
assert (INQ2 : In (q2, 8 * ns) (rt_live RT Σ2)) by (rewrite LV2'; left; reflexivity).
assert (INQ12 : In (q1, 4 * ns) (rt_live RT Σ2)) by (rewrite LV2'; right; left; reflexivity).
pose proof (af_live_disj RT AF Σ2 m5 q2 (8 * ns) q1 (4 * ns) [] _ ART5 LV2' ltac:(left; reflexivity)) as DQ12.
assert (NQ12 : q1 <> q2) by (clear - DQ12 NS; lia).
clear INQ1 ING1 INQ1'.
ogg_sigma_free FRS2 SP2.
destruct (live_below_lo RT AF Σ2 m5 q2 (8 * ns) lo ART5 INQ2 LOW) as (_ & BQ2 & _).
destruct (frame_live_apart RT AF Σ2 m5 f k q2 (8 * ns) ART5 INF INQ2) as (FLQ2 & _).
assert (SEPQ2 : q2 + 8 * ns <= A \/ A + 408 <= q2) by (clear - FLQ2 FA1 FA2; lia).
assert (QR2 : 0 < q2 < 2^64) by (clear - Q20 BQ2 NS LOR SPT; lia).
cps_hide.

cps_seg (le_w3 A Bd (os_body_storage os) q1 G lst q2 ns usp lo hdr os).
destruct POST as (m6 & -> & MU6 & WM6 & MI6 & ST6 & OS6). unfold stream_cells_x in OS6.
clear FR1 OS4. cps_seg_post.
apply Hk. exists Σ2, q1, q2. split.
2:{ split; [exact INQ12|]. split; [exact INQ2|]. split; [exact NQ12|]. split; [right; split; [lia| exact LV2']|].
split; [congruence|]. split; [congruence|]. split; [| congruence].
rewrite CR2, CR1. unfold mcost. replace (8 * ns <=? 64512) with true by (symmetry; apply Z.leb_le; lia).
replace (4 * ns <=? 64512) with true by (symmetry; apply Z.leb_le; lia). lia. }
eapply ASTA_conseq; [eassumption|]. intros ms <-.
destruct (chunk_u32arr m6 q1 lws junk1 ns _ ARQ1 ltac:(apply Nat2Z.inj; rewrite LQ1, Z2Nat.id by lia; lia) ltac:(lia) ltac:(lia)) as (lwx & ARL' & LLW).
destruct (chunk_u64arr m6 q2 gws junk2 ns _ ARQ2 ltac:(apply Nat2Z.inj; rewrite LQ2, Z2Nat.id by lia; lia) ltac:(lia) ltac:(lia)) as (gwx & ARG' & LGW).
exists m6, (lws ++ lwx), (gws ++ gwx).
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split; [exact (conj ART (conj MI6 ST6))|]. split; [exact PF|].
split; [exact OS6|].
split; [exact ARL'|]. split; [exact LLW|]. split; [rewrite firstn_app, Nat.sub_diag, firstn_all; cbn [firstn]; apply app_nil_r|].
split; [exact ARG'|]. split; [exact LGW|]. rewrite firstn_app, Nat.sub_diag, firstn_all. cbn [firstn]. apply app_nil_r.
Qed.
End OggExpandCPS.
