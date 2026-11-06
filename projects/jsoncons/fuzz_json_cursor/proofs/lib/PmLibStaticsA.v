(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA LibIface FPSteps L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibDefsA PmLibSpecsA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMTA.
Definition mem := (word -> option byte).
Lemma u64_of_Z : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hz. Qed.

Definition cell_in_foot (IC : PMLA.consts) (a n : Z) : Prop := 0 <= a /\ a + n <= 2 ^ 47 /\ forall x, a <= x < a + n -> PMLA.in_foot IC x.
Record consts_wf (IC : PMLA.consts) : Prop := CWF {
  cw_tab : cell_in_foot IC (PMLA.ATEXIT_TAB IC) ATEXIT_TAB_BYTES;
  cw_nl : cell_in_foot IC (PMLA.NEED_LOCKS IC) 1;
  cw_ll : cell_in_foot IC (PMLA.LOCALE_LOCK IC) 4;
  cw_ll_off : ~ PMLA.in_tab IC (PMLA.LOCALE_LOCK IC) /\ ~ PMLA.in_tab IC (PMLA.LOCALE_LOCK IC + 3) /\ (PMLA.NEED_LOCKS IC < PMLA.LOCALE_LOCK IC \/ PMLA.LOCALE_LOCK IC + 4 <= PMLA.NEED_LOCKS IC);
  cw_gg : cell_in_foot IC (PMLA.GLOC_GUARD IC) 1;
  cw_gp : cell_in_foot IC (PMLA.GLOC_PTR IC) 8;
  cw_sg : cell_in_foot IC (PMLA.SYSCAT_GUARD IC) 1;
  cw_eg : cell_in_foot IC (PMLA.ERRCAT_GUARD IC) 2;
  cw_ro : 0 <= PMLA.IMG_RO_LO IC /\ PMLA.IMG_RO_HI IC <= 2 ^ 47;
  cw_foot : forall a, PMLA.in_foot IC a -> 0 <= a < 2 ^ 47;
  cw_cg : cell_in_foot IC (PMLA.CONVCAT_GUARD IC) 2
}.
Ltac foot_tac iv := intros x Hx; unfold PMLA.in_foot; exists iv; split; [cbn [PMLA.FOOT PMLA.C_casan PMLA.C_cboth In]; auto 10 | cbn [fst snd]; lia].
Lemma C_casan_wf : consts_wf PMLA.C_casan.
Proof.
  constructor; unfold cell_in_foot, ATEXIT_TAB_BYTES; cbn [PMLA.ATEXIT_TAB PMLA.NEED_LOCKS PMLA.GLOC_GUARD PMLA.GLOC_PTR PMLA.SYSCAT_GUARD PMLA.ERRCAT_GUARD PMLA.CONVCAT_GUARD PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.LOCALE_LOCK PMLA.C_casan];
    try (split; [lia | split; [lia |]]).
  - foot_tac (0x6b0aa0, 0x6b0cc0). - foot_tac (0x6b0ce3, 0x6b0ce4). - foot_tac (0x6b0dc0, 0x6b0dc4). - unfold PMLA.in_tab, ATEXIT_TAB_BYTES; cbn [PMLA.ATEXIT_TAB PMLA.C_casan]; lia.
  - foot_tac (0x68f290, 0x68f488). - foot_tac (0x68f290, 0x68f488). - foot_tac (0x68f280, 0x68f282). - foot_tac (0x68f048, 0x68f04a). - lia.
  - intros a (iv & Hin & Hr). cbn [PMLA.FOOT PMLA.C_casan In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [fst snd] in Hr; lia |]). contradiction.
  - foot_tac (0x68f040, 0x68f042).
Qed.

Lemma C_cboth_wf : consts_wf PMLA.C_cboth.
Proof.
  constructor; unfold cell_in_foot, ATEXIT_TAB_BYTES; cbn [PMLA.ATEXIT_TAB PMLA.NEED_LOCKS PMLA.GLOC_GUARD PMLA.GLOC_PTR PMLA.SYSCAT_GUARD PMLA.ERRCAT_GUARD PMLA.CONVCAT_GUARD PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.LOCALE_LOCK PMLA.C_cboth];
    try (split; [lia | split; [lia |]]).
  - foot_tac (0x6b1de0, 0x6b2000). - foot_tac (0x6b2023, 0x6b2024). - foot_tac (0x6b2100, 0x6b2104). - unfold PMLA.in_tab, ATEXIT_TAB_BYTES; cbn [PMLA.ATEXIT_TAB PMLA.C_cboth]; lia.
  - foot_tac (0x6905d0, 0x6907c8). - foot_tac (0x6905d0, 0x6907c8). - foot_tac (0x6905c0, 0x6905c2). - foot_tac (0x690388, 0x69038a). - lia.
  - intros a (iv & Hin & Hr). cbn [PMLA.FOOT PMLA.C_cboth In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [fst snd] in Hr; lia |]). contradiction.
  - foot_tac (0x690380, 0x690382).
Qed.

Lemma ls_atexit_cases : forall IC g, PMLA.ls_atexit IC g = [] \/ PMLA.ls_atexit IC g = PMLA.jregs IC \/ PMLA.ls_atexit IC g = PMLA.cregs IC \/
  PMLA.ls_atexit IC g = PMLA.jregs IC ++ PMLA.cregs IC \/ PMLA.ls_atexit IC g = PMLA.cregs IC ++ PMLA.jregs IC.
Proof. intros IC [| | | | |]; cbn; auto 6. Qed.

Section Frame.
Variable segs : list Segment.
Variable IC : PMLA.consts.
Hypothesis WF : consts_wf IC.
Variables M M' : mem.
Hypothesis FOOT_EQ : forall a, 0 <= a < 2 ^ 64 -> PMLA.in_foot IC a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).

Lemma cell_tr : forall a (n : nat) v, cell_in_foot IC a (Z.of_nat n) -> cell_is segs M a n v -> cell_is segs M' a n v.
Proof.
  intros a n v (H0 & H1 & HF) Hc. unfold cell_is in *. rewrite (L5C.rdn_agree segs M M' n a H0 ltac:(lia)); [exact Hc|].
  intros i Hi. apply FOOT_EQ; [lia | apply HF; exact Hi].
Qed.
Lemma sub_cell : forall a n b m, cell_in_foot IC a n -> a <= b -> b + m <= a + n -> cell_in_foot IC b m.
Proof. intros a n b m (H0 & H1 & HF) Hb Hm. split; [lia | split; [lia |]]. intros x Hx. apply HF. lia. Qed.
Lemma u8_tr : forall a v, cell_in_foot IC a 1 -> PMLA.u8 segs M a v -> PMLA.u8 segs M' a v.
Proof. intros a v (H0 & H1 & HF) Hc. unfold PMLA.u8, L5.u8_at in *. rewrite (L5C.rdn_agree segs M M' 1%nat a H0 ltac:(cbn; lia)); [exact Hc|]. intros i Hi. apply FOOT_EQ; [cbn in Hi; lia | apply HF; cbn in Hi; lia]. Qed.
Lemma u64_tr : forall a v, cell_in_foot IC a 8 -> PMLA.u64 segs M a v -> PMLA.u64 segs M' a v.
Proof. intros a v (H0 & H1 & HF) Hc. unfold PMLA.u64, L5.u64_at in *. rewrite (L5C.rdn_agree segs M M' 8%nat a H0 ltac:(cbn; lia)); [exact Hc|]. intros i Hi. apply FOOT_EQ; [cbn in Hi; lia | apply HF; cbn in Hi; lia]. Qed.

Lemma atexit_tr : forall hs, atexit_state_at segs (PMLA.ATEXIT_TAB IC) M hs -> atexit_state_at segs (PMLA.ATEXIT_TAB IC) M' hs.
Proof.
  pose proof (cw_tab IC WF) as T. unfold ATEXIT_TAB_BYTES in T.
  assert (C : forall d (n : nat) v, 0 <= d -> d + Z.of_nat n <= 544 -> cell_is segs M (PMLA.ATEXIT_TAB IC + d) n v -> cell_is segs M' (PMLA.ATEXIT_TAB IC + d) n v).
  { intros d n v Hd Hn. apply cell_tr. apply (sub_cell _ _ _ _ T); lia. }
  assert (C0 : forall (n : nat) v, Z.of_nat n <= 544 -> cell_is segs M (PMLA.ATEXIT_TAB IC) n v -> cell_is segs M' (PMLA.ATEXIT_TAB IC) n v).
  { intros n v Hn Hc. pose proof (C 0 n v ltac:(lia) ltac:(lia)) as X. rewrite Z.add_0_r in X. exact (X Hc). }
  intros hs (A1 & A2 & A3). split; [apply C0; [cbn; lia | exact A1] | split; [apply C; [lia | cbn; lia | exact A2] |]].
  destruct hs as [|h hs'].
  - destruct A3 as (B1 & B2). split; [apply C; [lia | cbn; lia | exact B1] |].
    destruct B2 as [B2 | (B2 & B3)]; [left; apply C; [lia | cbn; lia | exact B2] | right; split; apply C; try (cbn; lia); assumption].
  - destruct A3 as (L32 & B1 & B2 & B3 & B4). split; [exact L32 |]. split; [apply C; [lia | cbn; lia | exact B1] |]. split; [apply C; [lia | cbn; lia | exact B2] |].
    split; [apply C; [lia | cbn; lia | exact B3] |].
    intros i f a Hn. destruct (B4 i f a Hn) as (D1 & D2).
    assert (Hi : (i < length (h :: hs'))%nat) by (apply nth_error_Some; rewrite Hn; discriminate).
    split.
    + rewrite <- Z.add_assoc in D1 |- *. apply C; [lia | change (Z.of_nat 8) with 8; lia | exact D1].
    + rewrite <- Z.add_assoc in D2 |- *. apply C; [lia | change (Z.of_nat 8) with 8; lia | exact D2].
Qed.

Lemma ls_ok_frame : forall g, (forall i, PMLA.IMG_RO_LO IC <= i < PMLA.IMG_RO_HI IC -> M (Z_to_bv 64 i) = None -> M' (Z_to_bv 64 i) = None) ->
  PMLA.ls_ok segs IC g M -> PMLA.ls_ok segs IC g M'.
Proof.
  intros g RO (H1 & (H2 & H3 & H3') & H4). split; [| split; [split; [| split] |]].
  - intros i Hi. apply RO; [exact Hi | exact (H1 i Hi)].
  - apply atexit_tr. exact H2.
  - apply (cell_tr _ 1%nat). exact (cw_nl IC WF). exact H3.
  - apply (cell_tr _ 4%nat). exact (cw_ll IC WF). exact H3'.
  - pose proof (cw_gg IC WF) as G1. pose proof (cw_gp IC WF) as G2. pose proof (cw_sg IC WF) as G3. pose proof (cw_eg IC WF) as G4.
    assert (LD : PMLA.loc_done segs IC M -> PMLA.loc_done segs IC M').
    { intros (X1 & X2 & X3). split; [apply u8_tr; assumption | split; [apply u64_tr; assumption | apply u8_tr; assumption]]. }
    assert (EG : forall b, PMLA.errcat_guard segs IC M b -> PMLA.errcat_guard segs IC M' b).
    { intros b (X1 & X2). split; apply u8_tr; try assumption; apply (sub_cell _ _ _ _ G4); lia. }
    assert (CG : forall b, PMLA.convcat_guard segs IC M b -> PMLA.convcat_guard segs IC M' b).
    { intros b (X1 & X2). pose proof (cw_cg IC WF) as G5. split; apply u8_tr; try assumption; apply (sub_cell _ _ _ _ G5); lia. }
    destruct g; [| destruct H4 as (X & Y & Z); split; [apply LD; exact X | split; [apply EG; exact Y | apply CG; exact Z]] ..].
    intros a Ha Ht Hn. destruct Ha as (iv & Hin & Hr).
    pose proof (cw_foot IC WF a (ex_intro _ iv (conj Hin Hr))) as R.
    rewrite (FOOT_EQ a ltac:(lia) (ex_intro _ iv (conj Hin Hr))). apply H4; [exists iv; auto | exact Ht | exact Hn].
Qed.
End Frame.

Section Top.
Variable L : asan_layout.
Variable ar : asan_run.
Variable IC : PMLA.consts.
Variable Lay : lib_layoutA.
Hypothesis WF : consts_wf IC.
Hypothesis LAY : PMSA.pm_layout_okA L IC Lay.

Theorem lib_frame_okA : PmLibIfaceA.lib_statics_frameA Lay ar (PMSA.pm_staticsA L IC).
Proof.
  destruct LAY as (HL & _ & _ & HF & _ & _ & _ & HRW & _).
  unfold lib_statics_frameA, lib_statics_frame. intros g M M' Hok Hfoot Hro _.
  cbn [LibIface.ls_ok PMSA.pm_staticsA] in *. unfold PMSA.ls_ok in *.
  apply (ls_ok_frame (hl_segs L) IC WF M M').
  - intros a Ha Hin. apply Hfoot; [exact Ha |]. unfold LibIface.in_foot. cbn [ll_foot lib_view]. rewrite HF. exact Hin.
  - intros i Hi Hn. apply Hro; [| exact Hn]. pose proof (cw_ro IC WF) as (R0 & R1). rewrite u64_of_Z by lia. cbn [ll_rw_lo lib_view]. lia.
  - exact Hok.
Qed.

Theorem lib_init_okA : PmLibIfaceA.lib_statics_initA Lay ar (PMSA.pm_staticsA L IC).
Proof.
  destruct LAY as (HL & _ & _ & _ & _ & _ & _ & _ & HA & HH & HN & COV & LLZ).
  unfold lib_statics_initA. intros av uid rnd tid canary hw M F TAB NL.
  destruct F as (IMG & _). cbn [ll_init_img lib_view] in IMG.
  cbn [LibIface.ls_ok LibIface.ls_g0 PMSA.pm_staticsA]. unfold PMSA.ls_ok, PMLA.ls_ok. rewrite HL, HA, HH in TAB. rewrite HL, HN in NL.
  split; [| split; [split; [| split] |]].
  - intros i Hi. destruct (COV i (or_introl Hi)) as (iv & Hin & Hr). exact (IMG iv i Hin Hr).
  - cbn [PMLA.ls_atexit]. rewrite app_nil_r. exact TAB.
  - exact NL.
  -
    apply LLZ. intros a Ha. pose proof (cw_ll IC WF) as (L0 & L1 & LF). pose proof (cw_ll_off IC WF) as (T1 & T2 & NLo).
    assert (NT : ~ PMLA.in_tab IC a) by (unfold PMLA.in_tab, ATEXIT_TAB_BYTES in *; lia).
    assert (NN : a <> PMLA.NEED_LOCKS IC) by (clear - Ha NLo; lia).
    destruct (COV a (or_intror (conj (LF a Ha) (conj NT NN)))) as (iv & Hin & Hr). exact (IMG iv a Hin Hr).
  - intros a Hf Ht Hn. destruct (COV a (or_intror (conj Hf (conj Ht Hn)))) as (iv & Hin & Hr). exact (IMG iv a Hin Hr).
Qed.
End Top.
End PMTA.
