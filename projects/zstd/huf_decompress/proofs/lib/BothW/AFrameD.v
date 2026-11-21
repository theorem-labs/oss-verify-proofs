(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (22 recorded proofs replaced by written proofs (wview_agree, wr_at_agree, wr_at_transportD and 19 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase ARep.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AFrameD () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atK47Corelib4Init9Datatypes6option02K47Corelib4Init5Logic2eq01C47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewK47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib4Init9Datatypes4bool00C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init5Logic3notI47Corelib4Init5Logic3and00c59OSSVerify5KrLib5BothW7AFrameD;wview_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib3Lib5Frame@disjoint_outsideC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib3Lib3Mem;wa_unsignedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7AFrameD;wr_at_agreeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib3Lib5CellsBcells_bytes_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBbytes_at_transportC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7AFrameD@wr_at_transportDC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib3Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u32arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr4u32sC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC47Corelib4Init3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC59OSSVerify5KrLib3Lib3Arr;u32s_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr4u64sC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr;u64s_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7junk_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natK59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells7cell_wfC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z;lt_ge_casesI47Corelib4Init5Logic2or00C47Corelib4Init3Nat3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init9Datatypes3appC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rc59OSSVerify5KrLib5BothW7AFrameDCrw_cells_transportDC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula01C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib5Lists4List9nth_errorC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00C59OSSVerify5KrLib5BothW4ARep7fill_atC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef6repeatC47Corelib4Init5Logic6eq_indc59OSSVerify5KrLib5BothW7AFrameDAu64arr_transportDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7AFrameDAu32arr_transportDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5azeroC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7AFrameDAmunch_agree_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBro_cells_transportC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7AFrameD9wmono_butC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem@wview_write_monoC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_mem".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section WithSegs.
Variable segs : list Segment.

Lemma wview_agree : forall m m' (x : word), m' x = m x -> wview segs m' x = wview segs m x.
Proof. intros m m' x E. unfold wview. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
Lemma wr_at_agree : forall m m' A n,
  wr_at segs m A n -> (forall i, 0 <= i < n -> m' (wa (A + i)) = m (wa (A + i))) -> wr_at segs m' A n.
Proof.
  intros m m' A n (H0 & H1 & H) E. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (wview_agree m m' _ (E i Hi)). apply H. exact Hi.
Qed.

Lemma wr_at_transportD : forall W m m' A n,
  wr_at segs m A n -> munch W m m' -> disjoint_from W A n -> wr_at segs m' A n.
Proof.
  intros W m m' A n WR MU D. pose proof WR as (H0 & H1 & _).
  eapply wr_at_agree; [exact WR|]. intros i Hi. apply MU.
  rewrite wa_unsigned by lia. eapply disjoint_outside; [exact D | lia].
Qed.

Lemma rw_cells_transportD : forall W m m' A cs,
  rw_cells segs m A cs -> munch W m m' ->
  disjoint_from W A (Z.of_nat (cells_size cs)) ->
  rw_cells segs m' A cs.
Proof.
  intros W m m' A cs [[Hwf Hb] Hw] MU D. split; [split; [exact Hwf|]|].
  - eapply bytes_at_transport; eauto. rewrite cells_bytes_length by assumption. exact D.
  - eapply wr_at_transportD; eauto.
Qed.

Lemma u8arr_transportD : forall W m m' A bs,
  u8arr segs m A bs -> munch W m m' ->
  disjoint_from W A (Z.of_nat (length bs)) -> u8arr segs m' A bs.
Proof.
  intros W m m' A bs [Hb Hw] MU D. split.
  - eapply bytes_at_transport; eauto.
  - eapply wr_at_transportD; eauto.
Qed.

Lemma u32arr_transportD : forall W m m' A ws,
  u32arr segs m A ws -> munch W m m' ->
  disjoint_from W A (4 * Z.of_nat (length ws)) -> u32arr segs m' A ws.
Proof.
  intros W m m' A ws [Hb Hw] MU D. split.
  - eapply bytes_at_transport; eauto. rewrite u32s_length, Nat2Z.inj_mul. exact D.
  - eapply wr_at_transportD; eauto.
Qed.

Lemma u64arr_transportD : forall W m m' A ws,
  u64arr segs m A ws -> munch W m m' ->
  disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr segs m' A ws.
Proof.
  intros W m m' A ws [Hb Hw] MU D. split.
  - eapply bytes_at_transport; eauto. rewrite u64s_length, Nat2Z.inj_mul. exact D.
  - eapply wr_at_transportD; eauto.
Qed.

(* [comment removed for export] *)
Lemma stk_transportD : forall W m m' lo hi,
  stk segs m lo hi -> munch W m m' -> disjoint_from W lo (hi - lo) -> stk segs m' lo hi.
Proof.
  intros W m m' lo hi (H0 & H1 & H) MU D. split; [exact H0|]. split; [exact H1|].
  intros a Ha.
  assert (E : m' (wa a) = m (wa a)).
  { apply MU. rewrite wa_unsigned by lia. eapply disjoint_outside; [exact D | lia]. }
  destruct (H a Ha) as [WV [b RD]]. split.
  - rewrite (wview_agree m m' _ E). exact WV.
  - exists b. unfold mrd in *. rewrite E. exact RD.
Qed.

(* [comment removed for export] *)
Lemma munch_agree_range : forall W m m' A n i,
  munch W m m' -> disjoint_from W A n -> 0 <= A -> A + n <= 2^64 -> 0 <= i < n ->
  m' (wa (A + i)) = m (wa (A + i)).
Proof.
  intros W m m' A n i MU D H0 H1 Hi. apply MU. rewrite wa_unsigned by lia.
  eapply disjoint_outside; [exact D | lia].
Qed.
End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma junk_frameD : forall W m m' A n, junk_at m A n -> munch W m m' ->
  (0 < n -> disjoint_from W A n) -> junk_at m' A n.
Proof.
  intros W m m' A n [bs H] MU D. exists bs.
  pose proof H as H0. destruct H0 as [[[L _] [B0 [B1 B]]] [W0 [W1 WR]]]. cbn in L, B1, W1.
  destruct (Z.lt_ge_cases 0 n).
  - eapply rw_cells_transportD; [exact H | exact MU |]. cbn [cells_size csize]. rewrite Nat.add_0_r.
    rewrite Z2Nat.id by lia. exact (D ltac:(lia)).
  - assert (bs = []) as -> by (destruct bs; [reflexivity| cbn in L; lia]).
    split; [split; [cbn; lia|]|]; unfold bytes_at, wr_at; cbn.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Lemma fill_frameD : forall W m m' A n v, fill_at m A n v -> munch W m m' ->
  (0 < n -> disjoint_from W A n) -> fill_at m' A n v.
Proof.
  intros W m m' A n v H MU D. unfold fill_at in *.
  destruct (Z.lt_ge_cases 0 n).
  - eapply rw_cells_transportD; [exact H | exact MU |]. cbn [cells_size csize]. rewrite Nat.add_0_r.
    rewrite Z2Nat.id by lia. exact (D ltac:(lia)).
  - pose proof H as HH. destruct HH as [[[L _] [B0 [B1 B]]] [W0 [W1 WR]]]. cbn in L, B1, W1.
    replace (Z.to_nat n) with 0%nat in * by lia. cbn [repeat] in *.
    split; [split; [cbn; lia|]|]; unfold bytes_at, wr_at; cbn.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Lemma cells_frameD : forall W m m' A cs, rw_cells bsegs m A cs -> munch W m m' ->
  disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells bsegs m' A cs.
Proof. intros. eapply rw_cells_transportD; eauto. Qed.

Lemma u64arr_frameD : forall W m m' A ws, u64arr bsegs m A ws -> munch W m m' ->
  disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr bsegs m' A ws.
Proof. intros. eapply u64arr_transportD; eauto. Qed.
Lemma u32arr_frameD : forall W m m' A ws, u32arr bsegs m A ws -> munch W m m' ->
  disjoint_from W A (4 * Z.of_nat (length ws)) -> u32arr bsegs m' A ws.
Proof. intros. eapply u32arr_transportD; eauto. Qed.

Lemma azero_frameD : forall W m m' A n, azero m A n -> munch W m m' ->
  (0 < n -> disjoint_from W A n) -> azero m' A n.
Proof.
  intros W m m' A n [Z0 WR] MU D. pose proof WR as (W0 & W1 & _).
  assert (E : forall i, 0 <= i < n -> m' (wa (A + i)) = m (wa (A + i))).
  { intros i Hi. eapply munch_agree_range; [exact MU | apply D; lia | lia | lia | lia]. }
  split.
  - intros i Hi. rewrite (E i Hi). apply Z0. exact Hi.
  - eapply wr_at_agree; [exact WR | exact E].
Qed.

(* [comment removed for export] *)
Lemma ro_cells_frameD : forall W m m' A cs, ro_cells bsegs m A cs -> munch W m m' ->
  disjoint_from W A (Z.of_nat (cells_size cs)) -> ro_cells bsegs m' A cs.
Proof. intros. eapply ro_cells_transport; eauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wmono_but (W : list ivl) (m m' : amem) : Prop :=
  forall x : word, outside W (bv_unsigned x) -> wview bsegs m x <> None -> wview bsegs m' x <> None.

Lemma munch_wmono_but : forall W m m', munch W m m' -> wmono_but W m m'.
Proof. intros W m m' MU x Hx. rewrite (wview_agree bsegs m m' x (MU x Hx)). exact (fun H => H). Qed.
Lemma wmono_wmono_but : forall W m m', wmono bsegs m m' -> wmono_but W m m'.
Proof. intros W m m' WM x _. apply WM. Qed.
Lemma wmono_but_refl : forall W m, wmono_but W m m.
Proof. intros W m x _ H; exact H. Qed.
Lemma wmono_but_trans : forall W m1 m2 m3, wmono_but W m1 m2 -> wmono_but W m2 m3 -> wmono_but W m1 m3.
Proof. intros W m1 m2 m3 A B x Hx H. apply B; [exact Hx|]. apply A; assumption. Qed.
Lemma wmono_but_weaken : forall W W' m m', sub_fp W W' -> wmono_but W m m' -> wmono_but W' m m'.
Proof. intros W W' m m' S H x Hx. apply H. apply S. exact Hx. Qed.
Lemma wmono_but_write : forall W m0 m a bs, wmono_but W m0 m -> wmono_but W m0 (write_to_mem m a bs).
Proof. intros W m0 m a bs H x Hx Hw. apply wview_write_mono. apply H; assumption. Qed.
End CANSEC1.
