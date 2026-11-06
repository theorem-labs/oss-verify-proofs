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
X0ae X09u X09x X0af X09p X09l X0a4 X0a5 X05l X05e X05c
X05m X06d X069 X068 X071 X06v X06y X06u X073.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X12c X14x X0r0 X0r9 X0ra X0qz X0v9 X0rb X0wl X0wm X110 X10j X10c X108 X10q X10r X0wb X0w9 X0x2 X0x1 X0xn X0xq X0xm X0xu.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X108 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10r OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xu.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).

Definition rng_out (W : list (Z * Z)) (A n : Z) : Prop := forall x, A <= x < A + n -> outside W x.
Lemma rng_out_nil : forall A n, rng_out [] A n.
Proof. intros A n x _. exact I. Qed.
Lemma rng_out_cons : forall lo hi W A n, (A + n <= lo \/ hi <= A \/ hi <= lo) -> rng_out W A n -> rng_out ((lo, hi) :: W) A n.
Proof. intros lo hi W A n H HW x Hx. cbn [outside]. split; [lia| exact (HW x Hx)]. Qed.
Lemma outside_app_iff : forall W1 W2 x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 x; cbn [app outside]; [tauto|]. rewrite IH. tauto. Qed.
Lemma rng_out_app : forall W1 W2 A n, rng_out W1 A n -> rng_out W2 A n -> rng_out (W1 ++ W2) A n.
Proof. intros W1 W2 A n H1 H2 x Hx. apply outside_app_iff. split; [exact (H1 x Hx)| exact (H2 x Hx)]. Qed.
Lemma rng_out_img : forall W A n, (forall y, in_ranges W y -> client_static y) -> (A + n <= 0x10000 \/ SEGTOP_A <= A) -> rng_out W A n.
Proof. intros W A n HW H x Hx. apply (outside_img W x HW). lia. Qed.
Lemma rng_out_sub : forall W A n A' n', rng_out W A n -> A <= A' -> A' + n' <= A + n -> rng_out W A' n'.
Proof. intros W A n A' n' H H1 H2 x Hx. apply H. lia. Qed.

Ltac rng_out_tac tac := repeat (apply rng_out_cons; [tac|]); apply rng_out_nil.

Definition acl_rng (L : list (Z * Z)) (fr : list (Z * nat)) (sp A n : Z) : Prop := forall x, A <= x < A + n -> aclient L fr sp x.
Lemma acl_stack : forall L fr sp A n, sp <= A -> A + n <= USTACK_TOP -> acl_rng L fr sp A n.
Proof. intros L fr sp A n H1 H2 x Hx. left. lia. Qed.
Lemma acl_frame : forall L fr sp f k A n, In (f, k) fr -> f <= A -> A + n <= f + fs_size k - 8 -> acl_rng L fr sp A n.
Proof. intros L fr sp f k A n Hin H1 H2 x Hx. right; right; right; left. exists f, k. split; [exact Hin| lia]. Qed.
Lemma acl_fshadow : forall L fr sp f k A n, In (f, k) fr -> shad f <= A -> A + n <= shad (f + fs_size k) -> acl_rng L fr sp A n.
Proof. intros L fr sp f k A n Hin H1 H2 x Hx. right; right; right; right. exists f, k. split; [exact Hin| lia]. Qed.
Lemma acl_live : forall L fr sp p q A n, In (p, q) L -> p <= A -> A + n <= p + q -> acl_rng L fr sp A n.
Proof. intros L fr sp p q A n Hin H1 H2 x Hx. right; right; left. exists p, q. split; [exact Hin| lia]. Qed.
Lemma acl_static : forall L fr sp A n, (forall x, A <= x < A + n -> client_static x) -> acl_rng L fr sp A n.
Proof. intros L fr sp A n H x Hx. right; left. exact (H x Hx). Qed.

Section Tr.
Variables (L : list (Z * Z)) (fr : list (Z * nat)) (sp : Z) (W : list (Z * Z)) (m m' : mem).
Hypothesis PR : rt_pres_fp L fr sp W m m'.
Lemma agree_rng : forall A n, acl_rng L fr sp A n -> rng_out W A n -> agree_on (fun x => A <= x < A + n) m m'.
Proof using PR. intros A n HA HO. apply (agree_of_pres_fp L fr sp W m m' _ PR). intros x Hx. split; [exact (HA x Hx)| exact (HO x Hx)]. Qed.
Lemma htr_rw : forall A cs, rw_cells bsegs m A cs -> acl_rng L fr sp A (Z.of_nat (cells_size cs)) -> rng_out W A (Z.of_nat (cells_size cs)) ->
rw_cells bsegs m' A cs.
Proof using PR. intros A cs H HA HO. exact (rw_cells_agree_nw bsegs m m' A cs H (agree_rng _ _ HA HO)). Qed.
Lemma htr_ro : forall A cs, ro_cells bsegs m A cs -> acl_rng L fr sp A (Z.of_nat (cells_size cs)) -> rng_out W A (Z.of_nat (cells_size cs)) ->
ro_cells bsegs m' A cs.
Proof using PR. intros A cs H HA HO. exact (ro_cells_agree bsegs m m' A cs H (agree_rng _ _ HA HO)). Qed.
Lemma htr_bytes : forall A bs, bytes_at bsegs m A bs -> acl_rng L fr sp A (Z.of_nat (length bs)) -> rng_out W A (Z.of_nat (length bs)) ->
bytes_at bsegs m' A bs.
Proof using PR. intros A bs H HA HO. exact (bytes_at_agree bsegs m m' A bs H (agree_rng _ _ HA HO)). Qed.
Lemma htr_u8 : forall A bs, u8arr bsegs m A bs -> acl_rng L fr sp A (Z.of_nat (length bs)) -> rng_out W A (Z.of_nat (length bs)) ->
u8arr bsegs m' A bs.
Proof using PR.
intros A bs H HA HO. apply u8arr_rw_CB. apply u8arr_rw_CB in H. apply (htr_rw A _ H); cbn [cells_size csize]; rewrite Nat.add_0_r; assumption.
Qed.
Lemma htr_u64 : forall A ws, u64arr bsegs m A ws -> acl_rng L fr sp A (8 * Z.of_nat (length ws)) -> rng_out W A (8 * Z.of_nat (length ws)) ->
u64arr bsegs m' A ws.
Proof using PR. intros A ws H HA HO. exact (u64arr_agree_nw bsegs m m' A ws H (agree_rng _ _ HA HO)). Qed.
Lemma htr_u32 : forall A ws, u32arr bsegs m A ws -> acl_rng L fr sp A (4 * Z.of_nat (length ws)) -> rng_out W A (4 * Z.of_nat (length ws)) ->
u32arr bsegs m' A ws.
Proof using PR.
intros A ws [Hb Hw] HA HO. pose proof (agree_rng _ _ HA HO) as AG. split.
- apply (bytes_at_agree bsegs m m' A _ Hb). rewrite u32s_length. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. lia.
- exact (wr_at_agree_nw bsegs m m' A _ Hw AG).
Qed.
End Tr.

Section Sep.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable X : hinv.
Hypothesis HX : hinv_ok OUT_rep IO_FP X.
Local Notation S1 := (x_S1 X). Local Notation lo := (x_lo X). Local Notation F := (x_F X). Local Notation sf := (x_sf X).

Definition hsep (a : haux) (h : hstate unit) : Prop :=
(forall p q, In (p, q) (h_own a h) -> 0 < p /\ p + q <= lo /\ (F + 16384 <= p \/ p + q <= F) /\ (p + q <= sf \/ sf + 2048 <= p)
/\ (p + q <= 0x10000 \/ SEGTOP_A <= p) /\ (forall p' q', In (p', q') (x_live X) -> p + q <= p' \/ p' + q' <= p))
/\ (forall p1 q1 p2 q2, In (p1, q1) (h_own a h) -> In (p2, q2) (h_own a h) -> p1 <> p2 -> p1 + q1 <= p2 \/ p2 + q2 <= p1)
/\ List.NoDup (map fst (h_own a h)).

Lemma live_sep_gen : forall (Σ1 : rts RT) (m : mem) p1 n1 p2 n2, ART RT Σ1 m ->
In (p1, n1) (rt_live RT Σ1) -> In (p2, n2) (rt_live RT Σ1) -> p1 <> p2 -> p1 + n1 <= p2 \/ p2 + n2 <= p1.
Proof using AF.
intros Σ1 m p1 n1 p2 n2 ART1 H1 H2 NE. destruct (in_split _ _ H1) as (l1 & l2 & E).
apply (af_live_disj RT AF Σ1 m p1 n1 p2 n2 l1 l2 ART1 E).
rewrite E in H2. apply in_app_or in H2. apply in_or_app. destruct H2 as [H|[H|H]]; [left; exact H| | right; exact H].
exfalso. injection H as E1 E2. exact (NE E1).
Qed.

Lemma hsep_of : forall (Σ1 : rts RT) (m : mem) a h, ART RT Σ1 m -> hsig RT X Σ1 a h -> hsep a h.
Proof using AF HX.
intros Σ1 m a h ART1 HS. destruct HS as (EL & ND & PERM & EF & ES & _).
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
- intros p1 q1 p2 q2 H1 H2 NE. exact (live_sep_gen Σ1 m p1 q1 p2 q2 ART1 (INL _ H1) (INL _ H2) NE).
Qed.

Definition iv_own (a : haux) (h : hstate unit) (lo' hi' : Z) : Prop := hi' <= lo' \/ exists p q, In (p, q) (h_own a h) /\ p <= lo' /\ hi' <= p + q.
Definition iv_own_ne (a : haux) (h : hstate unit) (p0 lo' hi' : Z) : Prop :=
hi' <= lo' \/ exists p q, In (p, q) (h_own a h) /\ p <> p0 /\ p <= lo' /\ hi' <= p + q.

Section Iv.
Variables (a : haux) (h : hstate unit).
Hypothesis HSP : hsep a h.
Lemma iv_frame_own : forall lo' hi' A n, iv_own a h lo' hi' -> F <= A -> A + n <= F + 16384 -> A + n <= lo' \/ hi' <= A \/ hi' <= lo'.
Proof using HSP. intros lo' hi' A n [E|(p & q & Hin & P1 & P2)] H1 H2; [right; right; exact E|]. destruct (proj1 HSP p q Hin) as (_ & _ & S & _). lia. Qed.
Lemma iv_stack_own : forall lo' hi' A n, iv_own a h lo' hi' -> S1 <= A -> A + n <= USTACK_TOP -> A + n <= lo' \/ hi' <= A \/ hi' <= lo'.
Proof using HSP HX.
intros lo' hi' A n [E|(p & q & Hin & P1 & P2)] H1 H2; [right; right; exact E|]. destruct (proj1 HSP p q Hin) as (_ & S & _).
pose proof (hi_lo _ _ _ HX) as (_ & LR & _). unfold RT_STACK, H_STACK in LR. lia.
Qed.
Lemma iv_fshadow_own : forall lo' hi' A n, iv_own a h lo' hi' -> sf <= A -> A + n <= sf + 2048 -> A + n <= lo' \/ hi' <= A \/ hi' <= lo'.
Proof using HSP. intros lo' hi' A n [E|(p & q & Hin & P1 & P2)] H1 H2; [right; right; exact E|]. destruct (proj1 HSP p q Hin) as (_ & _ & _ & S & _). lia. Qed.
Lemma iv_own_own : forall p0 q0 lo' hi' A n, In (p0, q0) (h_own a h) -> p0 <= A -> A + n <= p0 + q0 -> iv_own_ne a h p0 lo' hi' ->
A + n <= lo' \/ hi' <= A \/ hi' <= lo'.
Proof using HSP.
intros p0 q0 lo' hi' A n H0 A1 A2 [E|(p & q & Hin & NE & P1 & P2)]; [right; right; exact E|].
destruct (proj1 (proj2 HSP) p0 q0 p q H0 Hin ltac:(congruence)) as [S|S]; lia.
Qed.
Lemma iv_own_frame : forall p0 q0 lo' hi' A n, In (p0, q0) (h_own a h) -> p0 <= A -> A + n <= p0 + q0 -> F <= lo' -> hi' <= F + 16384 ->
A + n <= lo' \/ hi' <= A \/ hi' <= lo'.
Proof using HSP. intros p0 q0 lo' hi' A n H0 A1 A2 L1 L2. destruct (proj1 HSP p0 q0 H0) as (_ & _ & S & _). lia. Qed.
Lemma iv_own_fshadow : forall p0 q0 lo' hi' A n, In (p0, q0) (h_own a h) -> p0 <= A -> A + n <= p0 + q0 -> sf <= lo' -> hi' <= sf + 2048 ->
A + n <= lo' \/ hi' <= A \/ hi' <= lo'.
Proof using HSP. intros p0 q0 lo' hi' A n H0 A1 A2 L1 L2. destruct (proj1 HSP p0 q0 H0) as (_ & _ & _ & S & _). lia. Qed.
Lemma iv_own_stack : forall p0 q0 lo' hi' A n, In (p0, q0) (h_own a h) -> p0 <= A -> A + n <= p0 + q0 -> S1 <= lo' ->
A + n <= lo' \/ hi' <= A \/ hi' <= lo'.
Proof using HSP HX.
intros p0 q0 lo' hi' A n H0 A1 A2 L1. destruct (proj1 HSP p0 q0 H0) as (_ & S & _).
pose proof (hi_lo _ _ _ HX) as (_ & LR & _). unfold RT_STACK, H_STACK in LR. lia.
Qed.

Lemma own_not_client : forall p q x, In (p, q) (h_own a h) -> p <= x < p + q -> ~ aclient (x_live X) [(F, 8%nat)] S1 x.
Proof using HSP HX.
intros p q x Hin Hx Hc. destruct (proj1 HSP p q Hin) as (P0 & PL & PF & PS & PI & PC).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
destruct Hc as [H|[H|[H|[H|H]]]].
- unfold RT_STACK, H_STACK in LR. lia.
- pose proof (client_static_range _ H). unfold SEGTOP_A in *. lia.
- destruct H as (p' & q' & Hin' & H'). destruct (PC p' q' Hin'); lia.
- destruct H as (f & k & [E|[]] & H'). injection E as <- <-. change (fs_size 8) with 16384 in H'. lia.
- destruct H as (f & k & [E|[]] & H'). injection E as <- <-. change (fs_size 8) with 16384 in H'. rewrite <- ESF, ESF2 in H'. lia.
Qed.
End Iv.
End Sep.

Lemma outside_intro : forall W x, (forall lo hi, In (lo, hi) W -> ~ (lo <= x < hi)) -> outside W x.
Proof.
induction W as [|[lo hi] W IH]; intros x H; cbn [outside]; [exact I|]. split; [apply H; left; reflexivity|].
apply IH. intros lo' hi' Hin. apply H. right. exact Hin.
Qed.

Section Step.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Variable X : hinv.
Hypothesis HX : hinv_ok OUT_rep IO_FP X.
Local Notation S1 := (x_S1 X). Local Notation lo := (x_lo X). Local Notation F := (x_F X). Local Notation sf := (x_sf X).

Definition iv_h (a : haux) (h : hstate unit) (lo' hi' : Z) : Prop :=
(S1 <= lo' /\ hi' <= S1 + 248) \/ (sf <= lo' /\ hi' <= sf + 16) \/ (F + 32 <= lo' /\ hi' <= F + 9252) \/ iv_own a h lo' hi'.
Definition fp_h (a : haux) (h : hstate unit) (W : list (Z * Z)) : Prop := forall lo' hi', In (lo', hi') W -> iv_h a h lo' hi'.
Lemma fp_h_nil : forall a h, fp_h a h [].
Proof. intros a h lo' hi' []. Qed.
Lemma fp_h_cons : forall a h lo' hi' W, iv_h a h lo' hi' -> fp_h a h W -> fp_h a h ((lo', hi') :: W).
Proof. intros a h lo' hi' W H HW l hh [E|Hin]; [injection E as <- <-; exact H| exact (HW l hh Hin)]. Qed.

Section S.
Variables (a : haux) (h : hstate unit) (W : list (Z * Z)).
Hypothesis HSP : hsep X a h.
Hypothesis FPH : fp_h a h W.
Lemma fp_h_static : forall y, 0x10000 <= y < SEGTOP_A -> outside W y.
Proof using HSP FPH HX.
intros y Hy. pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
apply outside_intro. intros l hh Hin Hx. destruct (FPH l hh Hin) as [H|[H|[H|[H|(p & q & Hq & H1 & H2)]]]].
- unfold RT_STACK, H_STACK, SH_HI in *. lia.
- unfold SH_LO, SEGTOP_A in *. lia.
- unfold SEGTOP_A in *. lia.
- lia.
- destruct (proj1 HSP p q Hq) as (_ & _ & _ & _ & PI & _). unfold SEGTOP_A in *. lia.
Qed.
Lemma fp_h_view : forall x, aclient (x_live X) [(F, 8%nat)] S1 x -> outside (h_WL IO_FP X) x -> outside W x.
Proof using HSP FPH HX.
intros x Hc Ho. apply outside_intro. intros l hh Hin Hx. unfold h_WL in Ho. cbn [outside] in Ho.
destruct Ho as (O1 & O2 & O3 & _).
destruct (FPH l hh Hin) as [H|[H|[H|[H|(p & q & Hq & H1 & H2)]]]]; [lia| lia| lia| lia|].
exact (own_not_client OUT_rep IO_FP X HX a h HSP p q x Hq ltac:(lia) Hc).
Qed.
End S.

Lemma h_io_step : forall (Σ1 : rts RT) (m m' : mem) a h (Lv : list (Z * Z)) W,
hsep X a h -> rt_pres_fp Lv [(F, 8%nat)] S1 W m m' -> (forall e, In e (x_live X) -> In e Lv) -> fp_h a h W -> drv_consts m' ->
rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) (x_mR X) m -> ERR_rep m -> (forall so, OUT_rep so (x_mR X) -> OUT_rep so m) -> io_ssp m ->
rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) (x_mR X) m' /\ ERR_rep m' /\ (forall so, OUT_rep so (x_mR X) -> OUT_rep so m') /\ io_ssp m'.
Proof using HX ERR_loc OUT_loc IO_img.
intros Σ1 m m' a h Lv W HSP PR INC FPH DC PF ERR OUTR SSP.
assert (AIO : forall b : word, in_ranges IO_FP (bv_unsigned b) -> m' b = m b).
{ intros b Hb. apply PR.
- right; left. exact (IO_img _ Hb).
- apply (fp_h_static a h W HSP FPH). exact (client_static_range _ (IO_img _ Hb)). }
split; [| split; [| split]].
- apply (pres_fp_trans _ _ _ _ (x_mR X) m m' PF). intros b Hb Ho. apply PR.
+ exact (aclient_mono _ _ _ Lv [(F, 8%nat)] S1 _ Hb INC (fun e He => He) ltac:(lia)).
+ exact (fp_h_view a h W HSP FPH _ Hb Ho).
- exact (ERR_loc m m' ERR AIO).
- intros so Hso. exact (OUT_loc so m m' (OUTR so Hso) AIO).
- apply (io_ssp_pres_fp W Lv [(F, 8%nat)] S1 m m'); [| exact SSP| exact DC| exact PR].
intros x Hx. apply (fp_h_static a h W HSP FPH). unfold SSP_GUARD, SEGTOP_A in *. lia.
Qed.
End Step.

Section Parts.
Variables (L : list (Z * Z)) (fr : list (Z * nat)) (sp : Z) (W : list (Z * Z)) (m m' : mem).
Hypothesis PR : rt_pres_fp L fr sp W m m'.

Lemma bits_rep_tr : forall A D (b : bits_st unit), bits_rep bsegs m A D b -> bits_ok b ->
acl_rng L fr sp A 48 -> rng_out W A 48 -> acl_rng L fr sp D (sb_buf_size b) -> rng_out W D (sb_buf_size b) -> bits_rep bsegs m' A D b.
Proof using PR.
intros A D b ((rj & Lrj & C) & (bs & U & E) & SIDE) OK HA1 HO1 HA2 HO2.
assert (LB : Z.of_nat (length bs) = sb_buf_size b).
{ destruct OK as (ZL & _). rewrite E in ZL. unfold zlength in ZL. rewrite length_map in ZL. exact ZL. }
split; [exists rj; split; [exact Lrj|]; apply (htr_rw L fr sp W m m' PR A _ C); rewrite (bits_cells_size D b rj Lrj); assumption|].
split; [exists bs; split; [apply (htr_u8 L fr sp W m m' PR D bs U); rewrite LB; assumption| exact E]| exact SIDE].
Qed.

Lemma sync_rep_tr : forall A D (sy : sync_st bptr) bytes, sync_rep m A D sy bytes ->
acl_rng L fr sp A 32 -> rng_out W A 32 ->
(sy_data sy <> None -> acl_rng L fr sp D (sy_storage sy) /\ rng_out W D (sy_storage sy)) -> sync_rep m' A D sy bytes.
Proof using PR.
intros A D sy bytes (C & FOK & DAT & SEP) HA1 HO1 HD.
assert (CS : Z.of_nat (cells_size (sync_cells D sy)) = 32) by reflexivity.
split; [apply (htr_rw L fr sp W m m' PR A _ C); rewrite CS; assumption|].
split; [exact FOK|]. split; [| exact SEP].
unfold sync_data in DAT |- *. destruct (sy_data sy) as [p|] eqn:ED; [| exact DAT].
destruct DAT as (D0 & U & LB & PRE & LEN). destruct (HD ltac:(discriminate)) as (HA2 & HO2).
split; [exact D0|]. split; [apply (htr_u8 L fr sp W m m' PR D bytes U); rewrite LB; assumption|]. split; [exact LB|]. split; assumption.
Qed.

Variable X : hinv.
Local Notation F := (x_F X).

Lemma h_os_rep_tr : forall a h, h_os_rep X m a h -> acl_rng L fr sp (F + HO_OS) 408 -> rng_out W (F + HO_OS) 408 ->
(h_stream_init h <> 0 -> acl_rng L fr sp (a_Bd a) (os_body_storage (h_os h)) /\ rng_out W (a_Bd a) (os_body_storage (h_os h))
/\ acl_rng L fr sp (a_L a) (4 * os_lacing_storage (h_os h)) /\ rng_out W (a_L a) (4 * os_lacing_storage (h_os h))
/\ acl_rng L fr sp (a_G a) (8 * os_lacing_storage (h_os h)) /\ rng_out W (a_G a) (8 * os_lacing_storage (h_os h))) ->
h_os_rep X m' a h.
Proof using PR.
intros a h OSR HA HO HARR. unfold h_os_rep in OSR |- *. destruct (Z.eqb_spec (h_stream_init h) 0) as [E|NE].
- destruct OSR as ((jos & C) & EZ). split; [| exact EZ]. exists jos. apply (htr_rw L fr sp W m m' PR _ _ C); exact HA || exact HO.
- destruct OSR as (C & LH & (U8 & LB & BP & U32 & WP & LL & U64 & LG) & REST).
destruct (HARR NE) as (HB1 & HB2 & HL1 & HL2 & HG1 & HG2).
split; [apply (htr_rw L fr sp W m m' PR _ _ C); rewrite (stream_cells_size _ _ _ _ _ LH); assumption|].
split; [exact LH|]. split; [| exact REST].
split; [apply (htr_u8 L fr sp W m m' PR _ _ U8); rewrite LB; assumption|]. split; [exact LB|]. split; [exact BP|].
split; [apply (htr_u32 L fr sp W m m' PR _ _ U32); rewrite LL; assumption|]. split; [exact WP|]. split; [exact LL|].
split; [apply (htr_u64 L fr sp W m m' PR _ _ U64); rewrite LG; assumption| exact LG].
Qed.

Lemma h_dec_rep_tr : forall a h, h_dec_rep X m a h ->
(forall b, In b (a_LBD a) -> acl_rng L fr sp (blk_addr b) (blk_size b) /\ rng_out W (blk_addr b) (blk_size b)) -> h_dec_rep X m' a h.
Proof using PR.
intros a h D HB. unfold h_dec_rep in D |- *. destruct (h_st h) as [d|]; [| exact D].
destruct D as (R & REST). split; [| exact REST].
eapply decst_rep_agree; [exact R|].
intros x Hx (b & Hb & Hab). destruct (HB b Hb) as (HA & HO).
assert (E : m' (wa x) = m (wa x)) by (apply PR; rewrite wa_unsigned by lia; [apply HA; lia| apply HO; lia]).
split; [exact E|]. rewrite (wview_agree bsegs m m' _ E). tauto.
Qed.
End Parts.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).

Definition rng_out (W : list (Z * Z)) (A n : Z) : Prop := forall x, A <= x < A + n -> outside W x.
Lemma rng_out_nil : forall A n, rng_out [] A n.
Proof. intros A n x _. exact I. Qed.
Lemma rng_out_cons : forall lo hi W A n, (A + n <= lo \/ hi <= A \/ hi <= lo) -> rng_out W A n -> rng_out ((lo, hi) :: W) A n.
Proof. intros lo hi W A n H HW x Hx. cbn [outside]. split; [lia| exact (HW x Hx)]. Qed.
Lemma outside_app_iff : forall W1 W2 x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 x; cbn [app outside]; [tauto|]. rewrite IH. tauto. Qed.
Lemma rng_out_app : forall W1 W2 A n, rng_out W1 A n -> rng_out W2 A n -> rng_out (W1 ++ W2) A n.
Proof. intros W1 W2 A n H1 H2 x Hx. apply outside_app_iff. split; [exact (H1 x Hx)| exact (H2 x Hx)]. Qed.
Lemma rng_out_img : forall W A n, (forall y, in_ranges W y -> client_static y) -> (A + n <= 0x10000 \/ SEGTOP_A <= A) -> rng_out W A n.
Proof. intros W A n HW H x Hx. apply (outside_img W x HW). lia. Qed.
Lemma rng_out_sub : forall W A n A' n', rng_out W A n -> A <= A' -> A' + n' <= A + n -> rng_out W A' n'.
Proof. intros W A n A' n' H H1 H2 x Hx. apply H. lia. Qed.

Ltac rng_out_tac tac := repeat (apply rng_out_cons; [tac|]); apply rng_out_nil.

Definition acl_rng (L : list (Z * Z)) (fr : list (Z * nat)) (sp A n : Z) : Prop := forall x, A <= x < A + n -> aclient L fr sp x.
Lemma acl_stack : forall L fr sp A n, sp <= A -> A + n <= USTACK_TOP -> acl_rng L fr sp A n.
Proof. intros L fr sp A n H1 H2 x Hx. left. lia. Qed.
Lemma acl_frame : forall L fr sp f k A n, In (f, k) fr -> f <= A -> A + n <= f + fs_size k - 8 -> acl_rng L fr sp A n.
Proof. intros L fr sp f k A n Hin H1 H2 x Hx. right; right; right; left. exists f, k. split; [exact Hin| lia]. Qed.
Lemma acl_fshadow : forall L fr sp f k A n, In (f, k) fr -> shad f <= A -> A + n <= shad (f + fs_size k) -> acl_rng L fr sp A n.
Proof. intros L fr sp f k A n Hin H1 H2 x Hx. right; right; right; right. exists f, k. split; [exact Hin| lia]. Qed.
Lemma acl_live : forall L fr sp p q A n, In (p, q) L -> p <= A -> A + n <= p + q -> acl_rng L fr sp A n.
Proof. intros L fr sp p q A n Hin H1 H2 x Hx. right; right; left. exists p, q. split; [exact Hin| lia]. Qed.
Lemma acl_static : forall L fr sp A n, (forall x, A <= x < A + n -> client_static x) -> acl_rng L fr sp A n.
Proof. intros L fr sp A n H x Hx. right; left. exact (H x Hx). Qed.

Section Tr.
Variables (L : list (Z * Z)) (fr : list (Z * nat)) (sp : Z) (W : list (Z * Z)) (m m' : mem).
Hypothesis PR : rt_pres_fp L fr sp W m m'.
Lemma agree_rng : forall A n, acl_rng L fr sp A n -> rng_out W A n -> agree_on (fun x => A <= x < A + n) m m'.
Proof using PR. intros A n HA HO. apply (agree_of_pres_fp L fr sp W m m' _ PR). intros x Hx. split; [exact (HA x Hx)| exact (HO x Hx)]. Qed.
Lemma htr_rw : forall A cs, rw_cells asegs m A cs -> acl_rng L fr sp A (Z.of_nat (cells_size cs)) -> rng_out W A (Z.of_nat (cells_size cs)) ->
rw_cells asegs m' A cs.
Proof using PR. intros A cs H HA HO. exact (rw_cells_agree_nw asegs m m' A cs H (agree_rng _ _ HA HO)). Qed.
Lemma htr_ro : forall A cs, ro_cells asegs m A cs -> acl_rng L fr sp A (Z.of_nat (cells_size cs)) -> rng_out W A (Z.of_nat (cells_size cs)) ->
ro_cells asegs m' A cs.
Proof using PR. intros A cs H HA HO. exact (ro_cells_agree asegs m m' A cs H (agree_rng _ _ HA HO)). Qed.
Lemma htr_bytes : forall A bs, bytes_at asegs m A bs -> acl_rng L fr sp A (Z.of_nat (length bs)) -> rng_out W A (Z.of_nat (length bs)) ->
bytes_at asegs m' A bs.
Proof using PR. intros A bs H HA HO. exact (bytes_at_agree asegs m m' A bs H (agree_rng _ _ HA HO)). Qed.
Lemma htr_u8 : forall A bs, u8arr asegs m A bs -> acl_rng L fr sp A (Z.of_nat (length bs)) -> rng_out W A (Z.of_nat (length bs)) ->
u8arr asegs m' A bs.
Proof using PR.
intros A bs H HA HO. apply u8arr_rw_CB. apply u8arr_rw_CB in H. apply (htr_rw A _ H); cbn [cells_size csize]; rewrite Nat.add_0_r; assumption.
Qed.
Lemma htr_u64 : forall A ws, u64arr asegs m A ws -> acl_rng L fr sp A (8 * Z.of_nat (length ws)) -> rng_out W A (8 * Z.of_nat (length ws)) ->
u64arr asegs m' A ws.
Proof using PR. intros A ws H HA HO. exact (u64arr_agree_nw asegs m m' A ws H (agree_rng _ _ HA HO)). Qed.
Lemma htr_u32 : forall A ws, u32arr asegs m A ws -> acl_rng L fr sp A (4 * Z.of_nat (length ws)) -> rng_out W A (4 * Z.of_nat (length ws)) ->
u32arr asegs m' A ws.
Proof using PR.
intros A ws [Hb Hw] HA HO. pose proof (agree_rng _ _ HA HO) as AG. split.
- apply (bytes_at_agree asegs m m' A _ Hb). rewrite u32s_length. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. lia.
- exact (wr_at_agree_nw asegs m m' A _ Hw AG).
Qed.
End Tr.

Section Sep.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable X : hinv.
Hypothesis HX : hinv_ok OUT_rep IO_FP X.
Local Notation S1 := (x_S1 X). Local Notation lo := (x_lo X). Local Notation F := (x_F X). Local Notation sf := (x_sf X).

Definition hsep (a : haux) (h : hstate unit) : Prop :=
(forall p q, In (p, q) (h_own a h) -> 0 < p /\ p + q <= lo /\ (F + 16384 <= p \/ p + q <= F) /\ (p + q <= sf \/ sf + 2048 <= p)
/\ (p + q <= 0x10000 \/ SEGTOP_A <= p) /\ (forall p' q', In (p', q') (x_live X) -> p + q <= p' \/ p' + q' <= p))
/\ (forall p1 q1 p2 q2, In (p1, q1) (h_own a h) -> In (p2, q2) (h_own a h) -> p1 <> p2 -> p1 + q1 <= p2 \/ p2 + q2 <= p1)
/\ List.NoDup (map fst (h_own a h)).

Lemma live_sep_gen : forall (Σ1 : rts RT) (m : mem) p1 n1 p2 n2, ART RT Σ1 m ->
In (p1, n1) (rt_live RT Σ1) -> In (p2, n2) (rt_live RT Σ1) -> p1 <> p2 -> p1 + n1 <= p2 \/ p2 + n2 <= p1.
Proof using AF.
intros Σ1 m p1 n1 p2 n2 ART1 H1 H2 NE. destruct (in_split _ _ H1) as (l1 & l2 & E).
apply (af_live_disj RT AF Σ1 m p1 n1 p2 n2 l1 l2 ART1 E).
rewrite E in H2. apply in_app_or in H2. apply in_or_app. destruct H2 as [H|[H|H]]; [left; exact H| | right; exact H].
exfalso. injection H as E1 E2. exact (NE E1).
Qed.

Lemma hsep_of : forall (Σ1 : rts RT) (m : mem) a h, ART RT Σ1 m -> hsig RT X Σ1 a h -> hsep a h.
Proof using AF HX.
intros Σ1 m a h ART1 HS. destruct HS as (EL & ND & PERM & EF & ES & _).
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
- intros p1 q1 p2 q2 H1 H2 NE. exact (live_sep_gen Σ1 m p1 q1 p2 q2 ART1 (INL _ H1) (INL _ H2) NE).
Qed.

Definition iv_own (a : haux) (h : hstate unit) (lo' hi' : Z) : Prop := hi' <= lo' \/ exists p q, In (p, q) (h_own a h) /\ p <= lo' /\ hi' <= p + q.
Definition iv_own_ne (a : haux) (h : hstate unit) (p0 lo' hi' : Z) : Prop :=
hi' <= lo' \/ exists p q, In (p, q) (h_own a h) /\ p <> p0 /\ p <= lo' /\ hi' <= p + q.

Section Iv.
Variables (a : haux) (h : hstate unit).
Hypothesis HSP : hsep a h.
Lemma iv_frame_own : forall lo' hi' A n, iv_own a h lo' hi' -> F <= A -> A + n <= F + 16384 -> A + n <= lo' \/ hi' <= A \/ hi' <= lo'.
Proof using HSP. intros lo' hi' A n [E|(p & q & Hin & P1 & P2)] H1 H2; [right; right; exact E|]. destruct (proj1 HSP p q Hin) as (_ & _ & S & _). lia. Qed.
Lemma iv_stack_own : forall lo' hi' A n, iv_own a h lo' hi' -> S1 <= A -> A + n <= USTACK_TOP -> A + n <= lo' \/ hi' <= A \/ hi' <= lo'.
Proof using HSP HX.
intros lo' hi' A n [E|(p & q & Hin & P1 & P2)] H1 H2; [right; right; exact E|]. destruct (proj1 HSP p q Hin) as (_ & S & _).
pose proof (hi_lo _ _ _ HX) as (_ & LR & _). unfold RT_STACK, H_STACK in LR. lia.
Qed.
Lemma iv_fshadow_own : forall lo' hi' A n, iv_own a h lo' hi' -> sf <= A -> A + n <= sf + 2048 -> A + n <= lo' \/ hi' <= A \/ hi' <= lo'.
Proof using HSP. intros lo' hi' A n [E|(p & q & Hin & P1 & P2)] H1 H2; [right; right; exact E|]. destruct (proj1 HSP p q Hin) as (_ & _ & _ & S & _). lia. Qed.
Lemma iv_own_own : forall p0 q0 lo' hi' A n, In (p0, q0) (h_own a h) -> p0 <= A -> A + n <= p0 + q0 -> iv_own_ne a h p0 lo' hi' ->
A + n <= lo' \/ hi' <= A \/ hi' <= lo'.
Proof using HSP.
intros p0 q0 lo' hi' A n H0 A1 A2 [E|(p & q & Hin & NE & P1 & P2)]; [right; right; exact E|].
destruct (proj1 (proj2 HSP) p0 q0 p q H0 Hin ltac:(congruence)) as [S|S]; lia.
Qed.
Lemma iv_own_frame : forall p0 q0 lo' hi' A n, In (p0, q0) (h_own a h) -> p0 <= A -> A + n <= p0 + q0 -> F <= lo' -> hi' <= F + 16384 ->
A + n <= lo' \/ hi' <= A \/ hi' <= lo'.
Proof using HSP. intros p0 q0 lo' hi' A n H0 A1 A2 L1 L2. destruct (proj1 HSP p0 q0 H0) as (_ & _ & S & _). lia. Qed.
Lemma iv_own_fshadow : forall p0 q0 lo' hi' A n, In (p0, q0) (h_own a h) -> p0 <= A -> A + n <= p0 + q0 -> sf <= lo' -> hi' <= sf + 2048 ->
A + n <= lo' \/ hi' <= A \/ hi' <= lo'.
Proof using HSP. intros p0 q0 lo' hi' A n H0 A1 A2 L1 L2. destruct (proj1 HSP p0 q0 H0) as (_ & _ & _ & S & _). lia. Qed.
Lemma iv_own_stack : forall p0 q0 lo' hi' A n, In (p0, q0) (h_own a h) -> p0 <= A -> A + n <= p0 + q0 -> S1 <= lo' ->
A + n <= lo' \/ hi' <= A \/ hi' <= lo'.
Proof using HSP HX.
intros p0 q0 lo' hi' A n H0 A1 A2 L1. destruct (proj1 HSP p0 q0 H0) as (_ & S & _).
pose proof (hi_lo _ _ _ HX) as (_ & LR & _). unfold RT_STACK, H_STACK in LR. lia.
Qed.

Lemma own_not_client : forall p q x, In (p, q) (h_own a h) -> p <= x < p + q -> ~ aclient (x_live X) [(F, 8%nat)] S1 x.
Proof using HSP HX.
intros p q x Hin Hx Hc. destruct (proj1 HSP p q Hin) as (P0 & PL & PF & PS & PI & PC).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
destruct Hc as [H|[H|[H|[H|H]]]].
- unfold RT_STACK, H_STACK in LR. lia.
- pose proof (client_static_range _ H). unfold SEGTOP_A in *. lia.
- destruct H as (p' & q' & Hin' & H'). destruct (PC p' q' Hin'); lia.
- destruct H as (f & k & [E|[]] & H'). injection E as <- <-. change (fs_size 8) with 16384 in H'. lia.
- destruct H as (f & k & [E|[]] & H'). injection E as <- <-. change (fs_size 8) with 16384 in H'. rewrite <- ESF, ESF2 in H'. lia.
Qed.
End Iv.
End Sep.

Lemma outside_intro : forall W x, (forall lo hi, In (lo, hi) W -> ~ (lo <= x < hi)) -> outside W x.
Proof.
induction W as [|[lo hi] W IH]; intros x H; cbn [outside]; [exact I|]. split; [apply H; left; reflexivity|].
apply IH. intros lo' hi' Hin. apply H. right. exact Hin.
Qed.

Section Step.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Variable X : hinv.
Hypothesis HX : hinv_ok OUT_rep IO_FP X.
Local Notation S1 := (x_S1 X). Local Notation lo := (x_lo X). Local Notation F := (x_F X). Local Notation sf := (x_sf X).

Definition iv_h (a : haux) (h : hstate unit) (lo' hi' : Z) : Prop :=
(S1 <= lo' /\ hi' <= S1 + 216) \/ (sf <= lo' /\ hi' <= sf + 16) \/ (F + 32 <= lo' /\ hi' <= F + 9252) \/ iv_own a h lo' hi'.
Definition fp_h (a : haux) (h : hstate unit) (W : list (Z * Z)) : Prop := forall lo' hi', In (lo', hi') W -> iv_h a h lo' hi'.
Lemma fp_h_nil : forall a h, fp_h a h [].
Proof. intros a h lo' hi' []. Qed.
Lemma fp_h_cons : forall a h lo' hi' W, iv_h a h lo' hi' -> fp_h a h W -> fp_h a h ((lo', hi') :: W).
Proof. intros a h lo' hi' W H HW l hh [E|Hin]; [injection E as <- <-; exact H| exact (HW l hh Hin)]. Qed.

Section S.
Variables (a : haux) (h : hstate unit) (W : list (Z * Z)).
Hypothesis HSP : hsep X a h.
Hypothesis FPH : fp_h a h W.
Lemma fp_h_static : forall y, 0x10000 <= y < SEGTOP_A -> outside W y.
Proof using HSP FPH HX.
intros y Hy. pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
apply outside_intro. intros l hh Hin Hx. destruct (FPH l hh Hin) as [H|[H|[H|[H|(p & q & Hq & H1 & H2)]]]].
- unfold RT_STACK, H_STACK, SH_HI in *. lia.
- unfold SH_LO, SEGTOP_A in *. lia.
- unfold SEGTOP_A in *. lia.
- lia.
- destruct (proj1 HSP p q Hq) as (_ & _ & _ & _ & PI & _). unfold SEGTOP_A in *. lia.
Qed.
Lemma fp_h_view : forall x, aclient (x_live X) [(F, 8%nat)] S1 x -> outside (h_WL IO_FP X) x -> outside W x.
Proof using HSP FPH HX.
intros x Hc Ho. apply outside_intro. intros l hh Hin Hx. unfold h_WL in Ho. cbn [outside] in Ho.
destruct Ho as (O1 & O2 & O3 & _).
destruct (FPH l hh Hin) as [H|[H|[H|[H|(p & q & Hq & H1 & H2)]]]]; [lia| lia| lia| lia|].
exact (own_not_client OUT_rep IO_FP X HX a h HSP p q x Hq ltac:(lia) Hc).
Qed.
End S.

Lemma h_io_step : forall (Σ1 : rts RT) (m m' : mem) a h (Lv : list (Z * Z)) W,
hsep X a h -> rt_pres_fp Lv [(F, 8%nat)] S1 W m m' -> (forall e, In e (x_live X) -> In e Lv) -> fp_h a h W -> drv_consts m' ->
rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) (x_mR X) m -> ERR_rep m -> (forall so, OUT_rep so (x_mR X) -> OUT_rep so m) -> io_ssp m ->
rt_pres_fp (x_live X) [(F, 8%nat)] S1 (h_WL IO_FP X) (x_mR X) m' /\ ERR_rep m' /\ (forall so, OUT_rep so (x_mR X) -> OUT_rep so m') /\ io_ssp m'.
Proof using HX ERR_loc OUT_loc IO_img.
intros Σ1 m m' a h Lv W HSP PR INC FPH DC PF ERR OUTR SSP.
assert (AIO : forall b : word, in_ranges IO_FP (bv_unsigned b) -> m' b = m b).
{ intros b Hb. apply PR.
- right; left. exact (IO_img _ Hb).
- apply (fp_h_static a h W HSP FPH). exact (client_static_range _ (IO_img _ Hb)). }
split; [| split; [| split]].
- apply (pres_fp_trans _ _ _ _ (x_mR X) m m' PF). intros b Hb Ho. apply PR.
+ exact (aclient_mono _ _ _ Lv [(F, 8%nat)] S1 _ Hb INC (fun e He => He) ltac:(lia)).
+ exact (fp_h_view a h W HSP FPH _ Hb Ho).
- exact (ERR_loc m m' ERR AIO).
- intros so Hso. exact (OUT_loc so m m' (OUTR so Hso) AIO).
- apply (io_ssp_pres_fp W Lv [(F, 8%nat)] S1 m m'); [| exact SSP| exact DC| exact PR].
intros x Hx. apply (fp_h_static a h W HSP FPH). unfold SSP_GUARD, SEGTOP_A in *. lia.
Qed.
End Step.

Section Parts.
Variables (L : list (Z * Z)) (fr : list (Z * nat)) (sp : Z) (W : list (Z * Z)) (m m' : mem).
Hypothesis PR : rt_pres_fp L fr sp W m m'.

Lemma bits_rep_tr : forall A D (b : bits_st unit), bits_rep asegs m A D b -> bits_ok b ->
acl_rng L fr sp A 48 -> rng_out W A 48 -> acl_rng L fr sp D (sb_buf_size b) -> rng_out W D (sb_buf_size b) -> bits_rep asegs m' A D b.
Proof using PR.
intros A D b ((rj & Lrj & C) & (bs & U & E) & SIDE) OK HA1 HO1 HA2 HO2.
assert (LB : Z.of_nat (length bs) = sb_buf_size b).
{ destruct OK as (ZL & _). rewrite E in ZL. unfold zlength in ZL. rewrite length_map in ZL. exact ZL. }
split; [exists rj; split; [exact Lrj|]; apply (htr_rw L fr sp W m m' PR A _ C); rewrite (bits_cells_size D b rj Lrj); assumption|].
split; [exists bs; split; [apply (htr_u8 L fr sp W m m' PR D bs U); rewrite LB; assumption| exact E]| exact SIDE].
Qed.

Lemma sync_rep_tr : forall A D (sy : sync_st bptr) bytes, sync_rep m A D sy bytes ->
acl_rng L fr sp A 32 -> rng_out W A 32 ->
(sy_data sy <> None -> acl_rng L fr sp D (sy_storage sy) /\ rng_out W D (sy_storage sy)) -> sync_rep m' A D sy bytes.
Proof using PR.
intros A D sy bytes (C & FOK & DAT & SEP) HA1 HO1 HD.
assert (CS : Z.of_nat (cells_size (sync_cells D sy)) = 32) by reflexivity.
split; [apply (htr_rw L fr sp W m m' PR A _ C); rewrite CS; assumption|].
split; [exact FOK|]. split; [| exact SEP].
unfold sync_data in DAT |- *. destruct (sy_data sy) as [p|] eqn:ED; [| exact DAT].
destruct DAT as (D0 & U & LB & PRE & LEN). destruct (HD ltac:(discriminate)) as (HA2 & HO2).
split; [exact D0|]. split; [apply (htr_u8 L fr sp W m m' PR D bytes U); rewrite LB; assumption|]. split; [exact LB|]. split; assumption.
Qed.

Variable X : hinv.
Local Notation F := (x_F X).

Lemma h_os_rep_tr : forall a h, h_os_rep X m a h -> acl_rng L fr sp (F + HO_OS) 408 -> rng_out W (F + HO_OS) 408 ->
(h_stream_init h <> 0 -> acl_rng L fr sp (a_Bd a) (os_body_storage (h_os h)) /\ rng_out W (a_Bd a) (os_body_storage (h_os h))
/\ acl_rng L fr sp (a_L a) (4 * os_lacing_storage (h_os h)) /\ rng_out W (a_L a) (4 * os_lacing_storage (h_os h))
/\ acl_rng L fr sp (a_G a) (8 * os_lacing_storage (h_os h)) /\ rng_out W (a_G a) (8 * os_lacing_storage (h_os h))) ->
h_os_rep X m' a h.
Proof using PR.
intros a h OSR HA HO HARR. unfold h_os_rep in OSR |- *. destruct (Z.eqb_spec (h_stream_init h) 0) as [E|NE].
- destruct OSR as ((jos & C) & EZ). split; [| exact EZ]. exists jos. apply (htr_rw L fr sp W m m' PR _ _ C); exact HA || exact HO.
- destruct OSR as (C & LH & (U8 & LB & BP & U32 & WP & LL & U64 & LG) & REST).
destruct (HARR NE) as (HB1 & HB2 & HL1 & HL2 & HG1 & HG2).
split; [apply (htr_rw L fr sp W m m' PR _ _ C); rewrite (stream_cells_size _ _ _ _ _ LH); assumption|].
split; [exact LH|]. split; [| exact REST].
split; [apply (htr_u8 L fr sp W m m' PR _ _ U8); rewrite LB; assumption|]. split; [exact LB|]. split; [exact BP|].
split; [apply (htr_u32 L fr sp W m m' PR _ _ U32); rewrite LL; assumption|]. split; [exact WP|]. split; [exact LL|].
split; [apply (htr_u64 L fr sp W m m' PR _ _ U64); rewrite LG; assumption| exact LG].
Qed.

Lemma h_dec_rep_tr : forall a h, h_dec_rep X m a h ->
(forall b, In b (a_LBD a) -> acl_rng L fr sp (blk_addr b) (blk_size b) /\ rng_out W (blk_addr b) (blk_size b)) -> h_dec_rep X m' a h.
Proof using PR.
intros a h D HB. unfold h_dec_rep in D |- *. destruct (h_st h) as [d|]; [| exact D].
destruct D as (R & REST). split; [| exact REST].
eapply decst_rep_agree; [exact R|].
intros x Hx (b & Hb & Hab). destruct (HB b Hb) as (HA & HO).
assert (E : m' (wa x) = m (wa x)) by (apply PR; rewrite wa_unsigned by lia; [apply HA; lia| apply HO; lia]).
split; [exact E|]. rewrite (wview_agree asegs m m' _ E). tauto.
Qed.
End Parts.
