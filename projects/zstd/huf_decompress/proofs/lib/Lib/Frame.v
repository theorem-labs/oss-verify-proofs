(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (22 recorded proofs replaced by written proofs (mkR_spec, inside_not_outside, disjoint_outside and 19 more)). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Frame () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List6nth_okK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I4ELinuxProcessSemantics5Riscv7Prelude4tree00K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapc59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyI47Corelib4Init5Logic2eq00K4ELinuxProcessSemantics5Riscv7Prelude4tree02K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4list00c59OSSVerify5KrLib3Lib5Frame6insideC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltc59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7and_indK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2or00I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes8list_indK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01c59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes4prod00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01c59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init5Logic3and01K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions;bv_unsignedc59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewc59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib5Lists4List9nth_errorC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z9leb_spec0I47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z9ltb_spec0C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegc59OSSVerify5KrLib3Lib5FrameBinside_not_outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib3Lib3MemAwrite_to_mem_specC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib3Lib3Mem@wview_write_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC59OSSVerify5KrLib3Lib3Mem;wa_unsignedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib5Frame@disjoint_outsideC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5CellsBcells_bytes_lengthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib5FrameBbytes_at_transportC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib5Frame?wr_at_transportC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareI47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Peano2le00C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK47Corelib4Init5Logic2ex01C46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega7EnvRing5PExpr04C47Corelib4Init9Datatypes3appC47Corelib4Init3Nat3addK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib5Lists4List:length_appC56Stdlib5Arith8PeanoNat3Nat8eqb_specC56Stdlib5Arith8PeanoNat3Nat3eqbC47Corelib4Init3Nat3subC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagC46Stdlib5Lists4List>nth_error_app2C46Stdlib9micromega;ZifyClasses9not_morphC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses:impl_morphC46Stdlib5Lists4List>nth_error_app1C47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega=RingMicromega3Op201C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addc59OSSVerify5KrLib3Lib5Frame9stk_splitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib5Frame9stk_bytesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC56Stdlib5Arith8PeanoNat3Nat7add_0_rK59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib9micromega;ZifyClasses3injC46Stdlib5Lists4List>nth_error_NoneC46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib3Lib4Step>rw_cells_boundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib5Frame?stk_of_rw_cellsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib5Frame9stk_mergeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01c59OSSVerify5KrLib3Lib5Frame=stk_transportC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mkR (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) : bvmap 5 word :=
  TNode
    (TNode (TNode (TNode (TNode (TNode TEmpty (Some x31) TEmpty) (Some x15) TEmpty) (Some x7) (TNode TEmpty (Some x23) TEmpty)) (Some x3) (TNode (TNode TEmpty (Some x19) TEmpty) (Some x11) (TNode TEmpty (Some x27) TEmpty)))
       (Some x1) (TNode (TNode (TNode TEmpty (Some x17) TEmpty) (Some x9) (TNode TEmpty (Some x25) TEmpty)) (Some x5) (TNode (TNode TEmpty (Some x21) TEmpty) (Some x13) (TNode TEmpty (Some x29) TEmpty))))
    None
    (TNode (TNode (TNode (TNode TEmpty (Some x16) TEmpty) (Some x8) (TNode TEmpty (Some x24) TEmpty)) (Some x4) (TNode (TNode TEmpty (Some x20) TEmpty) (Some x12) (TNode TEmpty (Some x28) TEmpty))) (Some x2)
       (TNode (TNode (TNode TEmpty (Some x18) TEmpty) (Some x10) (TNode TEmpty (Some x26) TEmpty)) (Some x6) (TNode (TNode TEmpty (Some x22) TEmpty) (Some x14) (TNode TEmpty (Some x30) TEmpty)))).

(* [comment removed for export] *)
Lemma mkR_spec : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 =
  bvmap_set (Z_to_bv 5 31) x31 (bvmap_set (Z_to_bv 5 30) x30 (bvmap_set (Z_to_bv 5 29) x29 (bvmap_set (Z_to_bv 5 28) x28 (
  bvmap_set (Z_to_bv 5 27) x27 (bvmap_set (Z_to_bv 5 26) x26 (bvmap_set (Z_to_bv 5 25) x25 (bvmap_set (Z_to_bv 5 24) x24 (
  bvmap_set (Z_to_bv 5 23) x23 (bvmap_set (Z_to_bv 5 22) x22 (bvmap_set (Z_to_bv 5 21) x21 (bvmap_set (Z_to_bv 5 20) x20 (
  bvmap_set (Z_to_bv 5 19) x19 (bvmap_set (Z_to_bv 5 18) x18 (bvmap_set (Z_to_bv 5 17) x17 (bvmap_set (Z_to_bv 5 16) x16 (
  bvmap_set (Z_to_bv 5 15) x15 (bvmap_set (Z_to_bv 5 14) x14 (bvmap_set (Z_to_bv 5 13) x13 (bvmap_set (Z_to_bv 5 12) x12 (
  bvmap_set (Z_to_bv 5 11) x11 (bvmap_set (Z_to_bv 5 10) x10 (bvmap_set (Z_to_bv 5 9) x9 (bvmap_set (Z_to_bv 5 8) x8 (
  bvmap_set (Z_to_bv 5 7) x7 (bvmap_set (Z_to_bv 5 6) x6 (bvmap_set (Z_to_bv 5 5) x5 (bvmap_set (Z_to_bv 5 4) x4 (
  bvmap_set (Z_to_bv 5 3) x3 (bvmap_set (Z_to_bv 5 2) x2 (bvmap_set (Z_to_bv 5 1) x1 bvmap_empty)))))))))))))))))))))))))))))).
Proof. intros. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ivl := (Z * Z)%type.   (* [comment removed for export] *)

Fixpoint outside (W : list ivl) (x : Z) : Prop :=
  match W with
  | [] => True
  | (lo, hi) :: W' => ~ (lo <= x < hi)%Z /\ outside W' x
  end.

Fixpoint inside (W : list ivl) (a : Z) (n : Z) : Prop :=
  match W with
  | [] => False
  | (lo, hi) :: W' => (lo <= a /\ a + n <= hi)%Z \/ inside W' a n
  end.

Fixpoint disjoint_from (W : list ivl) (a : Z) (n : Z) : Prop :=
  match W with
  | [] => True
  | (lo, hi) :: W' => (a + n <= lo \/ hi <= a)%Z /\ disjoint_from W' a n
  end.

Lemma inside_not_outside : forall W a n x, inside W a n -> (a <= x < a + n)%Z -> ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros a n x Hin Hx; [tauto|].
  intros [H1 H2]. destruct Hin as [Hin|Hin]; [lia|]. exact (IH _ _ _ Hin Hx H2).
Qed.

Lemma disjoint_outside : forall W a n x, disjoint_from W a n -> (a <= x < a + n)%Z -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros a n x Hd Hx; [exact I|].
  destruct Hd as [H1 H2]. split; [lia|]. eauto.
Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition munch (W : list ivl) (m m' : word -> option byte) : Prop :=
  forall x : word, outside W (bv_unsigned x) -> m' x = m x.
Definition wmono (m m' : word -> option byte) : Prop :=
  forall x : word, wview segs m x <> None -> wview segs m' x <> None.

Lemma munch_refl : forall W m, munch W m m.
Proof.
ltac2:(KReplay.run1 (kr_t_Frame ()) ["WithSegs"] "h01Wh12_Hh21mh31xp;1p;2p;3g00<9j18Tg001Fj10Tg001kj12Tg002Ij11Tg00[Kj17Tg00[mj26Tg00>Gj24Tg005Jj23Tg00\Wj35Tg00Rm#8g00;T#0#0#0R0#0#0#0#2R1#1R2%20#1#7R0[f2R3f0R4,61'4P3f1R3O1,30W1X32A5344eW2W0o"). Qed.
Lemma wmono_refl : forall m, wmono m m.
Proof.
ltac2:(KReplay.run1 (kr_t_Frame ()) ["WithSegs"] "h01Hh11mh21xp;1p;3p;2g001Fj10Tg001kj12Tg002Ij11Tg00[Kj13Tg00]Kj38Tg004hj17Tg008Yj36Tg00?=j14Tg00^Hj25Tg00;T#0#0#0R0#0#0#0#2#1R1%20#1R0#3R2[p,4segsf1f0R338%70562#4P3W0X211533eW1o"). Qed.
Lemma wmono_trans : forall m1 m2 m3, wmono m1 m2 -> wmono m2 m3 -> wmono m1 m3.
Proof. intros m1 m2 m3 H1 H2 x Hx. apply H2, H1, Hx. Qed.
Lemma munch_trans : forall W m1 m2 m3, munch W m1 m2 -> munch W m2 m3 -> munch W m1 m3.
Proof. intros W m1 m2 m3 H1 H2 x Hx. rewrite (H2 x Hx). apply H1, Hx. Qed.

(* [comment removed for export] *)
Definition sub_fp (W W' : list ivl) : Prop := forall x, outside W' x -> outside W x.
Lemma munch_weaken : forall W W' m m', sub_fp W W' -> munch W m m' -> munch W' m m'.
Proof. intros W W' m m' Hs H x Hx. apply H, Hs, Hx. Qed.

(* [comment removed for export] *)
Lemma munch_write : forall W m0 m a bs,
  munch W m0 m -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
  inside W a (Z.of_nat (length bs)) ->
  munch W m0 (write_to_mem m (wa a) bs).
Proof.
  intros W m0 m a bs H Ha Hl Hin x Hx. rewrite write_to_mem_spec by lia.
  pose proof (bv_unsigned_in_range 64 x).
  destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length bs))); cbn [andb];
    try (apply H; exact Hx).
  exfalso. eapply (inside_not_outside W a _ (bv_unsigned x) Hin); [lia| exact Hx].
Qed.

Lemma wmono_write : forall m0 m a bs, wmono m0 m -> wmono m0 (write_to_mem m a bs).
Proof. intros m0 m a bs H x Hx. apply wview_write_mono. apply H, Hx. Qed.

(* [comment removed for export] *)
Lemma bytes_at_transport : forall W m m' A bs,
  bytes_at segs m A bs -> munch W m m' -> disjoint_from W A (Z.of_nat (length bs)) ->
  bytes_at segs m' A bs.
Proof.
  intros W m m' A bs (Ha & Hl & H) Hm Hd. split; [lia|]. split; [lia|].
  intros i Hi. unfold mrd. rewrite Hm.
  - apply H. exact Hi.
  - eapply disjoint_outside; [exact Hd|]. rewrite wa_unsigned by lia. lia.
Qed.

Lemma wr_at_transport : forall m m' A n, wr_at segs m A n -> wmono m m' -> wr_at segs m' A n.
Proof. intros m m' A n (Ha & Hn & H) Hw. split; [lia|]. split; [lia|]. intros i Hi. apply Hw, H, Hi. Qed.

Lemma rw_cells_transport : forall W m m' A cs,
  rw_cells segs m A cs -> munch W m m' -> wmono m m' ->
  disjoint_from W A (Z.of_nat (cells_size cs)) ->
  rw_cells segs m' A cs.
Proof.
  intros W m m' A cs [[Hwf Hb] Hw] Hm Hmono Hd. split; [split; [exact Hwf|]|].
  - eapply bytes_at_transport; eauto. rewrite cells_bytes_length by assumption. exact Hd.
  - eapply wr_at_transport; eauto.
Qed.

Lemma ro_cells_transport : forall W m m' A cs,
  ro_cells segs m A cs -> munch W m m' ->
  disjoint_from W A (Z.of_nat (cells_size cs)) ->
  ro_cells segs m' A cs.
Proof.
  intros W m m' A cs [Hwf Hb] Hm Hd. split; [exact Hwf|].
  eapply bytes_at_transport; eauto. rewrite cells_bytes_length by assumption. exact Hd.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stk (m : word -> option byte) (lo hi : Z) : Prop :=
  (0 <= lo)%Z /\ (hi <= 2^64)%Z /\
  forall a, (lo <= a < hi)%Z -> wview segs m (wa a) <> None /\ exists b, mrd segs m (wa a) = Some b.

Lemma stk_split : forall m lo mid hi, stk m lo hi -> (lo <= mid <= hi)%Z -> stk m lo mid /\ stk m mid hi.
Proof. intros m lo mid hi (H1 & H2 & H) Hm. split; (split; [lia|]; split; [lia|]); intros a Ha; apply H; lia. Qed.

Lemma stk_merge : forall m lo mid hi, stk m lo mid -> stk m mid hi -> (lo <= mid <= hi)%Z -> stk m lo hi.
Proof.
  intros m lo mid hi (A1 & A2 & A) (B1 & B2 & B) Hm. split; [lia|]. split; [lia|].
  intros a Ha. destruct (Z.ltb_spec0 a mid); [apply A | apply B]; lia.
Qed.

Lemma stk_empty : forall m lo, (0 <= lo <= 2^64)%Z -> stk m lo lo.
Proof. intros. split; [lia|]. split; [lia|]. intros a Ha. lia. Qed.

(* [comment removed for export] *)
Lemma stk_bytes : forall m lo hi, stk m lo hi -> (lo <= hi)%Z ->
  exists bs, length bs = Z.to_nat (hi - lo) /\ bytes_at segs m lo bs.
Proof.
  intros m lo hi (H1 & H2 & H) Hle.
  set (n := Z.to_nat (hi - lo)).
  assert (G : forall k, (k <= n)%nat -> exists bs, length bs = k /\ forall i, (i < k)%nat -> mrd segs m (wa (lo + Z.of_nat i)) = nth_error bs i).
  { induction k as [|k IH]; intros Hk.
    - exists []. split; [reflexivity|]. intros i Hi; lia.
    - destruct (IH ltac:(lia)) as (bs & Hlen & Hbs).
      destruct (H (lo + Z.of_nat k)%Z ltac:(lia)) as [_ (b & Hb)].
      exists (bs ++ [b]). split. { rewrite app_length; cbn; lia. }
      intros i Hi. destruct (Nat.eqb_spec i k).
      + subst i. rewrite nth_error_app2 by lia. rewrite Hlen, Nat.sub_diag. exact Hb.
      + rewrite nth_error_app1 by lia. apply Hbs. lia. }
  destruct (G n ltac:(lia)) as (bs & Hlen & Hbs). exists bs. split; [exact Hlen|].
  split; [lia|]. split; [lia|]. intros i Hi. apply Hbs. lia.
Qed.

Lemma stk_carve : forall m lo hi (n : nat),
  stk m lo hi -> (lo <= hi - Z.of_nat n)%Z ->
  stk m lo (hi - Z.of_nat n) /\ exists junk, rw_cells segs m (hi - Z.of_nat n) [CB n junk].
Proof.
  intros m lo hi n Hs Hle. pose proof Hs as (H1 & H2 & H).
  destruct (stk_split m lo (hi - Z.of_nat n) hi Hs ltac:(lia)) as [Hlo Hhi].
  split; [exact Hlo|].
  destruct (stk_bytes m (hi - Z.of_nat n) hi Hhi ltac:(lia)) as (bs & Hlen & Hb).
  exists bs. split.
  - split. { cbn. split; [lia|exact I]. }
    cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
    intros i Hi. apply H. lia.
Qed.

(* [comment removed for export] *)
Lemma stk_of_rw_cells : forall m A cs,
  rw_cells segs m A cs -> stk m A (A + Z.of_nat (cells_size cs)).
Proof.
  intros m A cs [[Hwf (Ha & Hl & Hb)] (_ & _ & Hw)].
  rewrite cells_bytes_length in Hl, Hb by assumption.
  split; [lia|]. split; [lia|]. intros a Hr. split.
  - replace a with (A + (a - A))%Z by lia. apply Hw. lia.
  - replace a with (A + Z.of_nat (Z.to_nat (a - A)))%Z by lia. rewrite Hb by lia.
    destruct (nth_error (cells_bytes cs) (Z.to_nat (a - A))) eqn:E; [eexists; reflexivity|].
    apply nth_error_None in E. rewrite cells_bytes_length in E by assumption. lia.
Qed.

Lemma stk_release : forall m lo A cs,
  stk m lo A -> rw_cells segs m A cs -> (lo <= A)%Z ->
  stk m lo (A + Z.of_nat (cells_size cs)).
Proof.
  intros m lo A cs Hs Hc Hle. pose proof (rw_cells_bound segs m A cs Hc).
  eapply stk_merge; [exact Hs | apply stk_of_rw_cells; exact Hc | lia].
Qed.

(* [comment removed for export] *)
Lemma stk_write : forall m lo hi a bs,
  stk m lo hi -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z -> stk (write_to_mem m (wa a) bs) lo hi.
Proof.
  intros m lo hi a bs (H1 & H2 & H) Ha Hl. split; [lia|]. split; [lia|]. intros x Hx.
  destruct (H x Hx) as [Hw (b & Hb)]. split.
  - apply wview_write_mono. exact Hw.
  - unfold mrd. rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
    destruct (Z.leb_spec0 a x); destruct (Z.ltb_spec0 x (a + Z.of_nat (length bs))); cbn [andb]; try (eexists; exact Hb).
    destruct (nth_error bs (Z.to_nat (x - a))) eqn:E; [eexists; reflexivity|]. apply nth_error_None in E. lia.
Qed.

Lemma stk_transport : forall W m m' lo hi,
  stk m lo hi -> munch W m m' -> wmono m m' ->
  (forall x, (lo <= x < hi)%Z -> outside W x \/ exists b, m' (wa x) = Some b) ->
  stk m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) Hm Hw Hcase. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hwa (b & Hb)]. split; [apply Hw; exact Hwa|].
  destruct (Hcase a Ha) as [Ho | (b' & Hb')].
  - exists b. unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
  - exists b'. unfold mrd. rewrite Hb'. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma stk_transport_disjoint : forall W m m' lo hi,
  stk m lo hi -> munch W m m' -> wmono m m' -> disjoint_from W lo (hi - lo) -> stk m' lo hi.
Proof.
  intros. eapply stk_transport; eauto. intros x Hx. left. eapply disjoint_outside; eauto. lia.
Qed.

End WithSegs.
