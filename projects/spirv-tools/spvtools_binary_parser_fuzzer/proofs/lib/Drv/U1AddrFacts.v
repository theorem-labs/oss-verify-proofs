(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb PropExec CatExec CatSim SeqExec StoreOk MemSplit Frame MmapSim AllocCeil LibIface LibBudget LibEff U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import RunsLib U1CxxTable StaticsGen U1Statics U1Cells.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition in_ivs (ivs : list (Z * Z)) (a : Z) : Prop := exists lo hi, In (lo, hi) ivs /\ lo <= a < hi.
Fixpoint in_ivsb (ivs : list (Z * Z)) (a : Z) : bool :=
  match ivs with [] => false | (lo, hi) :: r => ((lo <=? a) && (a <? hi)) || in_ivsb r a end.
Lemma in_ivsb_spec : forall ivs a, in_ivsb ivs a = true <-> in_ivs ivs a.
Proof.
  intros ivs a. induction ivs as [|[lo hi] r IH]; cbn [in_ivsb].
  - split; [discriminate | intros (lo & hi & [] & _)].
  - rewrite Bool.orb_true_iff, Bool.andb_true_iff, Z.leb_le, Z.ltb_lt, IH. split.
    + intros [[H1 H2] | (lo' & hi' & Hin & Hr)]; [exists lo, hi; split; [left; reflexivity | lia]|].
      exists lo', hi'. split; [right; exact Hin | exact Hr].
    + intros (lo' & hi' & [E | Hin] & Hr); [injection E as <- <-; left; lia | right].
      exists lo', hi'. split; assumption.
Qed.

Lemma in_ivs_app : forall l1 l2 a, in_ivs (l1 ++ l2) a <-> in_ivs l1 a \/ in_ivs l2 a.
Proof.
  intros l1 l2 a. unfold in_ivs. split.
  - intros (lo & hi & Hin & Hr). apply in_app_or in Hin as [Hin|Hin]; [left|right]; exists lo, hi; tauto.
  - intros [(lo & hi & Hin & Hr)|(lo & hi & Hin & Hr)]; exists lo, hi; (split; [apply in_or_app; tauto | exact Hr]).
Qed.

Lemma u64_of : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hz. Qed.

Lemma fseg_skip : forall seg rest a n,
  (0 < n)%Z ->
  (a < Z.of_N (seg_base seg) \/ Z.of_N (seg_base seg) + Z.of_N (seg_size seg) < a + n)%Z ->
  find_segment (seg :: rest) a n = find_segment rest a n.
Proof.
  intros seg rest a n Hn H. cbn [find_segment].
  destruct (Z.leb_spec (Z.of_N (seg_base seg)) a); destruct (Z.leb_spec (a + n) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)));
    cbn [andb]; try reflexivity. lia.
Qed.
Lemma fseg_off : forall a n, (0 < n)%Z -> (a + n <= 0x10000 \/ 0x124000 <= a)%Z ->
  find_segment RSEGS a n = None.
Proof.
  intros a n Hn H. unfold Ubsan.M.loaded_segments, Ubsan_loaded_segments.
  rewrite 4 fseg_skip; [reflexivity | exact Hn | | exact Hn | | exact Hn | | exact Hn |];
    cbn [seg_base seg_size Ubsan_segment_000 Ubsan_segment_001 Ubsan_segment_002 Ubsan_segment_003]; lia.
Qed.
Lemma wview_offimg : forall M (x : word), (bv_unsigned x + 1 <= 0x10000 \/ 0x124000 <= bv_unsigned x)%Z -> wview RSEGS M x = M x.
Proof.
  intros M x Hx. unfold wview. destruct (M x); [reflexivity|].
  rewrite fseg_off; [reflexivity | lia | lia].
Qed.

Section Stack.
  Variable sp0 : Z.
  Hypothesis Hsp : 0x7fff80000000 <= sp0 <= 0x800000000000 /\ sp0 mod 16 = 0.

  Lemma stack_def_xfer : forall M M',
    stack_writableZ M sp0 ->
    (forall a, sp0 - 8388608 <= a < sp0 -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None) ->
    stack_writableZ M' sp0.
  Proof.
    intros M M' T8 Hdef d m Hd Hm. apply store_ok_of_all; [rewrite u64_of by lia; lia|].
    intros x Hx. rewrite u64_of in Hx by lia. pose proof (u64_range x) as Ux.
    pose proof (store_ok_all RSEGS M m (Z_to_bv 64 (sp0 - 8388608 + d)) ltac:(rewrite u64_of by lia; lia)
                  (T8 d m Hd Hm) x ltac:(rewrite u64_of by lia; lia)) as W.
    rewrite wview_offimg in W |- * by lia.
    replace x with (Z_to_bv 64 (bv_unsigned x)) in W |- * by (apply bv_eq; rewrite u64_of by lia; reflexivity).
    apply Hdef; [lia | exact W].
  Qed.

  Lemma stack_defined : forall M a, stack_writableZ M sp0 -> sp0 - 8388608 <= a < sp0 -> M (Z_to_bv 64 a) <> None.
  Proof.
    intros M a T8 Ha.
    pose proof (store_ok_all RSEGS M 1 (Z_to_bv 64 (sp0 - 8388608 + (a - (sp0 - 8388608)))) ltac:(rewrite u64_of by lia; cbn; lia)
                  (T8 (a - (sp0 - 8388608)) 1%nat ltac:(lia) ltac:(cbn; lia)) (Z_to_bv 64 a) ltac:(rewrite !u64_of by lia; cbn; lia)) as W.
    rewrite wview_offimg in W by (rewrite u64_of by lia; lia). exact W.
  Qed.
End Stack.

Lemma img_iff : forall a, in_ranges (ly_img L) a <-> 0x10000 <= a < 0x124000.
Proof.
  intros a. unfold in_ranges. cbn [ly_img L]. split.
  - intros (lo & hi & [E|[]] & H). injection E as <- <-. exact H.
  - intros H. exists 0x10000, 0x124000. split; [left; reflexivity | exact H].
Qed.

Lemma high_not_sx : forall a, 0x124000 <= a -> ~ sx_region U1ST a.
Proof.
  intros a Ha Hs. pose proof (sx_region_rw U1ST a Hs) as (lo & hi & Hin & Hr).
  cbn in Hin. destruct Hin as [E|[]]. injection E as <- <-. lia.
Qed.

Lemma high_not_errno : forall a, 0x124000 <= a -> ~ errno_win L a.
Proof. intros a Ha He. unfold errno_win, zwin in He. cbn in He. lia. Qed.

Section High.
  Context {AC : AllocCeiling} {AMB : Amb}.
  Variable MI : MallocIface SEGS L.

  Lemma high_not_owned : forall A M model a, ainv MI A M model -> alloc_ceiling <= a -> ~ owned MI A a.
  Proof.
    intros A M model a AI Ha Ho. pose proof ac_bounds_lit as Hcv.
    assert (Hni : ~ in_ranges (ly_img L) a) by (rewrite img_iff; lia).
    pose proof (ai_owned_below_ceiling MI A M model a AI Ho Hni). lia.
  Qed.
End High.
