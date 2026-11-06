(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State OSSVerify.glaze.binary_reflection.images.Plain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhMallocH2 OSSVerify.Proofs.glaze.binary_reflection.lib.MhASlotW5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module MhASlotKMF.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.glaze.binary_reflection.images.Plain.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhMallocH2.MhSzc OSSVerify.Proofs.glaze.binary_reflection.lib.MhASlotW5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma rup_le : forall x y, 0 < x <= y -> y <= 2 ^ 62 -> y mod 4096 = 0 -> rup x <= y.
Proof.
  intros x y Hxy Hy Hm. destruct (rup_spec x ltac:(lia)) as [R1 R2].
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). nia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma rup_pru : forall x, 0 < x <= 2 ^ 62 -> rup x = page_round_up_Z x.
Proof.
  intros x Hx. destruct (rup_spec x Hx) as [R1 R2]. unfold page_round_up_Z, page_size.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). nia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma rup_mono : forall x y, 0 < x <= y -> y <= 2 ^ 61 -> rup x <= rup y.
Proof.
  intros x y Hxy Hy. destruct (rup_spec y ltac:(lia)) as [R1 R2]. apply rup_le; [lia | lia | exact R1].
Qed.

(* [comment removed for export] *)
Definition pow2_class_ok (sc : Z) : bool :=
  negb (4096 mod (16 * size_class sc) =? 0) || (sc =? 0) || (sc =? 1) || (sc =? 3) || (sc =? 7).
Lemma pow2_class_all : forallb pow2_class_ok (zrange 0 48%nat) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pow2_classes : forall sc, 0 <= sc < 48 -> 4096 mod (16 * size_class sc) = 0 -> sc = 0 \/ sc = 1 \/ sc = 3 \/ sc = 7.
Proof.
  intros sc Hsc Hm. pose proof (forallb_zrange pow2_class_ok 0 48%nat pow2_class_all sc ltac:(cbn; lia)) as H.
  unfold pow2_class_ok in H. rewrite Hm in H. cbn [Z.eqb negb orb] in H.
  repeat (apply Bool.orb_true_iff in H; destruct H as [H|H]); try (apply Z.eqb_eq in H); lia.
Qed.
Lemma size_class_0137 : size_class 0 = 1 /\ size_class 1 = 2 /\ size_class 3 = 4 /\ size_class 7 = 8.
Proof. repeat split; reflexivity. Qed.

Theorem mmap_arm_facts : forall sc cnt0 u' nosm req,
  0 <= sc < 48 -> 1 <= cnt0 <= 32 -> 16 * size_class sc * cnt0 < 2 ^ 20 -> (sc = 7 -> cnt0 <= 31) ->
  (cnt0 = 1 -> 2048 < 16 * size_class sc + 16) -> 0 <= req /\ req + 4 <= 16 * size_class sc -> 0 <= nosm <= 1 ->
  let size := 16 * size_class sc in
  let cnt2 := mred sc size cnt0 u' nosm in
  let cnt3 := fst (m3 size cnt2 req u' nosm) in
  let needed3 := snd (m3 size cnt2 req u' nosm) in
  let ml := needed3 / 4096 in
  let stride := slot_stride ml (cnt3 - 1) sc in
  1 <= cnt2 <= 32 /\ 1 <= cnt3 <= 32 /\ needed3 = 4096 * ml /\ 0 < ml /\ needed3 <= 2 ^ 20 /\
  UNIT + cnt3 * stride <= needed3 /\ stride * cnt3 <= 2 ^ 20 /\ 16 <= stride /\
  (cnt3 = 1 -> stride < UNIT * size_class sc \/ (4096 * ml = page_round_up_Z (UNIT * size_class sc + UNIT) /\ 2048 < UNIT * size_class sc + UNIT)) /\
  (aidx_of size cnt3 < cnt3 - 1 -> 4096 mod stride <> 0) /\
  req + 4 <= stride /\ (16 * size_class sc <= stride \/ 4080 <= stride).
Proof.
  intros sc cnt0 u' nosm req Hsc Hc0 Hq0 H7 H1 Hreq Hnosm size cnt2 cnt3 needed3 ml stride.
  pose proof (size_class_pos sc Hsc) as [SC1 SC2].
  assert (Ssz : 16 <= size <= 131056) by (subst size; lia).
  (* [comment removed for export] *)
  assert (C2 : (cnt2 = cnt0 \/ cnt2 = 2 \/ cnt2 = 3 \/ cnt2 = 5) /\ 1 <= cnt2 <= 32 /\ size * cnt2 < 2 ^ 20 /\ (sc = 7 -> cnt2 <= 31)).
  { subst cnt2. unfold mred.
    repeat match goal with |- context [if ?b then _ else _] => destruct b end; subst size; (split; [lia|]); split; lia. }
  destruct C2 as (C2v & C2r & C2q & C27).
  (* [comment removed for export] *)
  assert (RQ : 0 < req + 20 <= 2 ^ 62) by lia.
  destruct (rup_spec (req + 20) RQ) as [RQ1 RQ2].
  assert (SN : 0 < size * cnt2 + 16 <= 2 ^ 62) by nia.
  destruct (rup_spec (size * cnt2 + 16) SN) as [RN1 RN2].
  assert (RN3 : rup (size * cnt2 + 16) <= 2 ^ 20).
  { apply rup_le; [| lia | reflexivity]. assert (size * cnt2 + 16 <= 2 ^ 20) by (subst size; lia). lia. }
  assert (RQ3 : rup (req + 20) <= 2 ^ 20).
  { apply (Z.le_trans _ (4096 * 33)); [|lia]. apply rup_le; [lia | lia | reflexivity]. }
  assert (C3 : (cnt3 = cnt2 /\ needed3 = rup (size * cnt2 + 16)) \/
               (cnt3 = 1 /\ needed3 = rup (req + 20) /\ (rup (req + 20) < size + 16 \/ 16384 <= rup (req + 20)))).
  { subst cnt3 needed3. unfold m3.
    repeat match goal with |- context [if ?b then _ else _] => destruct b eqn:? end; cbn [fst snd];
      first [left; split; reflexivity | right; split; [reflexivity|]; split; [reflexivity|]].
    - left. apply Z.ltb_lt in Heqb0. exact Heqb0.
    - right. apply Z.ltb_ge in Heqb1. exact Heqb1. }
  assert (N3 : needed3 mod 4096 = 0 /\ 0 < needed3 <= 2 ^ 20) by (destruct C3 as [[_ ->]|(_ & -> & _)]; split; lia).
  destruct N3 as [N3m N3r].
  assert (Eml : needed3 = 4096 * ml /\ 0 < ml).
  { subst ml. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). split; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct Eml as [Eml Mpos].
  assert (C3r : 1 <= cnt3 <= 32) by (destruct C3 as [[-> _]|(-> & _)]; lia).
  (* [comment removed for export] *)
  assert (ST : (cnt3 = 1 -> stride = needed3 - 16) /\ (cnt3 <> 1 -> stride = size)).
  { subst stride size. unfold slot_stride, UNIT.
    replace (negb (ml =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia). cbn [andb].
    destruct (Z.eqb_spec (cnt3 - 1) 0); split; intros; lia. }
  destruct ST as [ST1 ST2].
  assert (S16 : 16 <= stride) by (destruct (Z.eq_dec cnt3 1) as [E|NE]; [rewrite (ST1 E); lia | rewrite (ST2 NE); lia]).
  split; [exact C2r|]. split; [exact C3r|]. split; [exact Eml|]. split; [exact Mpos|]. split; [lia|].
  split.
  { (* [comment removed for export] *) unfold UNIT. destruct (Z.eq_dec cnt3 1) as [E|NE].
    - rewrite (ST1 E), E. lia.
    - rewrite (ST2 NE). destruct C3 as [[-> ->]|(E1 & _)]; [lia | exfalso; exact (NE E1)]. }
  split.
  { destruct (Z.eq_dec cnt3 1) as [E|NE]; [rewrite (ST1 E), E; lia | rewrite (ST2 NE)].
    destruct C3 as [[-> _]|(E1 & _)]; [lia | exfalso; exact (NE E1)]. }
  split; [exact S16|].
  split.
  { (* [comment removed for export] *) intros E. rewrite (ST1 E). unfold UNIT. fold size.
    destruct C3 as [[E3 EN]|(_ & EN & [LT|GE])].
    - (* [comment removed for export] *)
      assert (E2 : cnt2 = 1) by lia. rewrite E2 in EN. replace (size * 1 + 16) with (size + 16) in EN by lia.
      right. rewrite <- Eml, EN. split; [apply rup_pru; lia|].
      destruct C2v as [Ec|[Ec|[Ec|Ec]]]; lia.
    - left. lia.
    - (* [comment removed for export] *)
      destruct (Z.lt_ge_cases (rup (req + 20)) (size + 16)) as [A|A]; [left; lia | right].
      assert (E1 : rup (req + 20) = rup (size + 16)).
      { apply Z.le_antisymm.
        - apply rup_mono; lia.
        - apply rup_le; [| lia | rewrite <- EN; exact N3m]. destruct (rup_spec (size + 16) ltac:(lia)); lia. }
      rewrite <- Eml, EN, E1. split; [apply rup_pru; lia|].
      destruct (rup_spec (size + 16) ltac:(lia)). lia. }
  split.
  { (* [comment removed for export] *)
    intros Hai. destruct (Z.eq_dec cnt3 1) as [E|NE].
    { exfalso. pose proof (aidx_of_rng size cnt3 ltac:(lia) ltac:(lia)). lia. }
    rewrite (ST2 NE). intros Hm0. subst size.
    destruct (pow2_classes sc Hsc Hm0) as [-> |[-> |[-> | ->]]]; pose proof size_class_0137 as (E0 & E1 & E3 & E7').
    all: unfold aidx_of in Hai.
    - rewrite E0 in *. replace (4080 / (16 * 1)) with 255 in Hai by reflexivity. destruct (Z.ltb_spec cnt3 255); lia.
    - rewrite E1 in *. replace (4080 / (16 * 2)) with 127 in Hai by reflexivity. destruct (Z.ltb_spec cnt3 127); lia.
    - rewrite E3 in *. replace (4080 / (16 * 4)) with 63 in Hai by reflexivity. destruct (Z.ltb_spec cnt3 63); lia.
    - rewrite E7' in *. replace (4080 / (16 * 8)) with 31 in Hai by reflexivity.
      assert (cnt3 <= 31) by (destruct C3 as [[-> _]|(-> & _)]; [apply C27; reflexivity | lia]).
      destruct (Z.ltb_spec cnt3 31); [lia|]. cbn in Hai. lia. }
  split.
  { destruct (Z.eq_dec cnt3 1) as [E|NE]; [rewrite (ST1 E) | rewrite (ST2 NE); subst size; lia].
    destruct C3 as [[E3 EN]|(_ & EN & _)]; rewrite EN; [|lia].
    assert (E2 : cnt2 = 1) by lia. rewrite E2 in *. subst size. lia. }
  destruct (Z.eq_dec cnt3 1) as [E|NE]; [rewrite (ST1 E) | rewrite (ST2 NE); left; subst size; lia].
  destruct C3 as [[E3 EN]|(_ & EN & _)]; rewrite EN.
  - left. assert (E2 : cnt2 = 1) by lia. rewrite E2 in *. subst size. lia.
  - right. lia.
Qed.
End MhASlotKMF.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.glaze.binary_reflection.images Require Import Plain.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesMmLib.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.MhMmapK OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaM OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaN OSSVerify.Proofs.glaze.binary_reflection.lib.MhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.MhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.MhNtf OSSVerify.Proofs.glaze.binary_reflection.lib.MhNtf2 OSSVerify.Proofs.glaze.binary_reflection.lib.MhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhCount OSSVerify.Proofs.glaze.binary_reflection.lib.MhBudget OSSVerify.Proofs.glaze.binary_reflection.lib.MhPolicy OSSVerify.Proofs.glaze.binary_reflection.lib.MhASlotKTop OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaR OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaS OSSVerify.Proofs.glaze.binary_reflection.lib.MhASlotKA OSSVerify.Proofs.glaze.binary_reflection.lib.MhMallocH2 OSSVerify.Proofs.glaze.binary_reflection.lib.MhASlotW5 OSSVerify.Proofs.glaze.binary_reflection.lib.MhASlotKF OSSVerify.Proofs.glaze.binary_reflection.lib.MhASlotKN. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.RefCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhKX OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhGap OSSVerify.Proofs.glaze.binary_reflection.lib.MhMmapK OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaM.MhRsegs OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhExt OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhList OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaN.MhNtfLib OSSVerify.Proofs.glaze.binary_reflection.lib.MhNest2.MhNest OSSVerify.Proofs.glaze.binary_reflection.lib.MhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhCover OSSVerify.Proofs.glaze.binary_reflection.lib.MhMmapK.MhAcct OSSVerify.Proofs.glaze.binary_reflection.lib.MhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.MhNtf OSSVerify.Proofs.glaze.binary_reflection.lib.MhNtf2 OSSVerify.Proofs.glaze.binary_reflection.lib.MhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhCount.MhCountSpec OSSVerify.Proofs.glaze.binary_reflection.lib.MhBudget OSSVerify.Proofs.glaze.binary_reflection.lib.MhPolicy OSSVerify.Proofs.glaze.binary_reflection.lib.MhASlotKTop OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaR OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaS.MhMSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhASlotKA.MhASpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaM.MhMmapW OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaM.MhMmapWF OSSVerify.Proofs.glaze.binary_reflection.lib.MhMallocH2.MhASlotW1 OSSVerify.Proofs.glaze.binary_reflection.lib.MhASlotW5.MhASlotW4b OSSVerify.Proofs.glaze.binary_reflection.lib.MhASlotW5 MhASlotKMF OSSVerify.Proofs.glaze.binary_reflection.lib.MhASlotKF.MhASlotT1 OSSVerify.Proofs.glaze.binary_reflection.lib.MhASlotKA OSSVerify.Proofs.glaze.binary_reflection.lib.MhASlotKF OSSVerify.Proofs.glaze.binary_reflection.lib.MhASlotKN.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import PuAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac tr_clear_heavy := repeat match goal with
  | H : context [Z.max _ _] |- _ => clear H | H : context [Z.min _ _] |- _ => clear H
  | H : context [Z.div _ _] |- _ => clear H | H : context [Z.modulo _ _] |- _ => clear H end.
#[local] Ltac lia_fast ::= first [ solve [ clear_disj; tr_clear_heavy; lia ] | solve [ clear_disj; lia ] | lia ].
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac bpeel := apply byte_peel; [ | wd_lenlit; rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | lia | wd_lenlit; rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

(* [comment removed for export] *)
#[local] Ltac mh_lia_nx := rnfix; first [ solve [hclr; lean zlia] | pa_arith_concl; lia_goal_ok; lia_hsep; first [ with_img1f_ zlia | with_img1_ zlia | lia_pairs; with_img2 zlia ] ].
#[local] Ltac lia ::= first [ solve [ rnfix; pa_tiers ltac:(zlia) ] | solve [ rnfix; pa_big; lia_goal_ok; lia_hsep; pa_tierB ltac:(zlia) ] | mh_lia_nx ].
#[local] Ltac lia_fast ::= first [ solve [ rnfix; pa_tiers ltac:(zlia) ] | solve [ rnfix; pa_big; lia_goal_ok; lia_hsep; pa_tierB ltac:(zlia) ] | first [ solve [ clear_disj; tr_clear_heavy; lia ] | solve [ clear_disj; lia ] | lia ] ].
Section FactsM.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Lemma pru_aligned : forall x, 0 <= x -> x mod 4096 = 0 -> page_round_up_Z x = x.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end.
    intros x Hx Hm. unfold page_round_up_Z, page_size.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). nia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Lemma zbv_m1 : Z_to_bv 64 (2 ^ 64 - 1) = Z_to_bv 64 (-1).
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. apply bv_eq. reflexivity. Qed.
End FactsM.

Section ASM.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M : mem) (mdl : Model)
            (regs : bvmap 5 word) (rom : word -> option byte) (sp sc req : Z) (d : nat)
            (F : kfam) (bi bo : bool).
  Hypothesis HL : kfam_laws RSEGS F.
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Hypothesis HLG : LEDGER st (m_vmmaps mdl).
  Hypothesis NJ : nojunk st.
  Hypothesis Hh : m_halted mdl = None.
  Hypothesis Hlz : m_vm_lazy mdl = [].
  Hypothesis Hmat : m_vm_materialized mdl = [].
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hd : dle (dbound (16 * size_class sc)) d.
  Hypothesis Hlimbo : zlen (s_limbo st) + Z.of_nat d + 1 <= 8.
  Hypothesis Hreq : 0 <= req /\ req + 4 <= 16 * size_class sc.
  Hypothesis HBUD : PHI L + MBASE <= vm_limit (m_vmmaps mdl).
  Hypothesis R10 : getr regs 10 = Z_to_bv 64 sc.
  Hypothesis R11 : getr regs 11 = Z_to_bv 64 req.
  Hypothesis R2 : getr regs 2 = Z_to_bv 64 sp.
  Hypothesis Rra : ret_ok (getr regs 1).
  Hypothesis R4 : getr regs 4 = Z_to_bv 64 TPV.
  Hypothesis Hsp : CEIL + ASSTK d <= sp /\ sp < 2 ^ 64.
  Hypothesis DEF : defined M (sp - ASSTK d) sp.
  Hypothesis HQ : forall c', as_ok st L sc req d sp regs M mdl rom c' -> kfx F bi c'.
  Hypothesis HQF : forall c', as_fail st L sc d sp regs M mdl rom c' -> Kf F c'.
  Hypothesis IHd : forall d', (d' < d)%nat -> AS_SPEC3 d'.

  #[local] Notation PT := (pt st L M mdl regs sp sc d).
  #[local] Notation PTE := (ptE st L M mdl regs sp sc d).
  #[local] Notation GBR := (gbr st L M mdl regs sp sc req d).
  #[local] Notation WOKa := (WOK L sp d).

  (* [comment removed for export] *)
  Definition nosm_of (s2g : mst) : Z :=
    if ((7 <=? sc) && (sc <=? 38))%bool then nosmall_of (c_bounces (s_ctx s2g) (sc - 7)) else 0.
  Definition cn_of (s2g : mst) (cntg : Z) : Z * Z :=
    let size := 16 * size_class sc in
    let u' := ucoarse sc (c_usage (s_ctx s2g) sc) (c_usage (s_ctx s2g) (sc + 1)) in
    m3 size (mred sc size cntg u' (nosm_of s2g)) req u' (nosm_of s2g).
  Definition xnew (s2g : mst) (cntg : Z) (s1 : mst) (g : Z) : Prop :=
    s_kind s1 g = GTop /\ g_sc s1 g = sc /\
    g_lastidx s1 g = fst (cn_of s2g cntg) - 1 /\ 4096 * g_maplen s1 g = snd (cn_of s2g cntg) /\
    (forall x, is_group s1 x <-> x = g \/ is_group s2g x).

  Section WithE.
  Variables (s2g : mst) (cntg : Z).
  Hypothesis HL_E : forall s1 Mc mdl1 r g idx,
    PTE s1 Mc mdl1 r -> xnew s2g cntg s1 g -> s_limbo s1 = s_limbo st ->
    head_of (s_alist s1 sc) = g -> is_group s1 g -> g_sc s1 g = sc -> 0 <= idx <= g_lastidx s1 g ->
    s_slot s1 g idx = SJunk 0 -> only_junk s1 g idx -> req + 4 <= g_stride s1 g -> (16 * size_class sc <= g_stride s1 g \/ 4080 <= g_stride s1 g) ->
    getr r 10 = Z_to_bv 64 idx ->
    kat RSEGS (mkCfg (mkst r (0x634a0%bv : word) Mc rom) mdl1) (kfx F bi).

  Lemma scl_rng : 1 <= size_class sc <= 8191. Proof using Hsc d. clear - Hsc d. pose proof (size_class_pos sc Hsc). lia. Qed.
  Lemma stk272 : 288 <= ASSTK d. Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. apply ASSTK_ge. Qed.

  (* [comment removed for export] *)
  Lemma mtail : forall s3 M3 mdl3 r4 m cnt3 needed,
    PT s3 M3 mdl3 r4 -> nojunk s3 -> s_limbo s3 = m :: s_limbo st -> s_alist s3 sc = [] ->
    metaU s3 m -> s_meta s3 m = meta_zero -> ~ In m (s_limbo st) ->
    getr r4 10 = Z_to_bv 64 0 -> getr r4 11 = Z_to_bv 64 needed -> getr r4 12 = Z_to_bv 64 3 -> getr r4 13 = Z_to_bv 64 34 ->
    getr r4 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r4 15 = Z_to_bv 64 0 -> getr r4 18 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r4 1 = Z_to_bv 64 406256 ->
    getr r4 9 = Z_to_bv 64 m -> getr r4 19 = Z_to_bv 64 needed -> getr r4 24 = Z_to_bv 64 (16 * size_class sc) -> getr r4 25 = Z_to_bv 64 cnt3 ->
    let ml := needed / 4096 in let stride := slot_stride ml (cnt3 - 1) sc in
    1 <= cnt3 <= 32 -> needed = 4096 * ml -> 0 < ml -> needed <= 2 ^ 20 ->
    UNIT + cnt3 * stride <= needed -> stride * cnt3 <= 2 ^ 20 -> 16 <= stride ->
    (cnt3 = 1 -> stride < UNIT * size_class sc \/ (4096 * ml = page_round_up_Z (UNIT * size_class sc + UNIT) /\ 2048 < UNIT * size_class sc + UNIT)) ->
    (aidx_of (16 * size_class sc) cnt3 < cnt3 - 1 -> 4096 mod stride <> 0) ->
    req + 4 <= stride -> (16 * size_class sc <= stride \/ 4080 <= stride) ->
    (forall s1, s_kind s1 m = GTop -> g_sc s1 m = sc -> g_lastidx s1 m = cnt3 - 1 -> 4096 * g_maplen s1 m = needed ->
                (forall x, is_group s1 x <-> x = m \/ is_group s3 x) -> xnew s2g cntg s1 m) ->
    kat RSEGS (mkCfg (mkst r4 (0x63c78%bv : word) M3 rom) mdl3) (kfx F bo).
  Proof using HL_E HQF Hsp R4 Rra R2 HBUD Hreq Hlimbo Hsc HL bi. clear - HL_E HQF Hsp R4 Rra R2 HBUD Hreq Hlimbo Hsc HL bi.
    intros s3 M3 mdl3 r4 m cnt3 needed P3 NJ3 EL3 Hnil3 Um3 Zm3 NLm A10 A11 A12 A13 A14 A15 A18 A1 A9 A19 A24 A25
           ml stride Hc3 Eml Mpos N20 Hfit Hq S16 Hsingle Hpnd Rq4 Rbig XG.
    pose proof P3 as [W3 RP3 LG3 Hh3 Hlz3 Hmat3 Hfs3 Hfds3 Hlim3 Hcan3 Herr3 BL3 LM3 MU3 FR3 DF3 SK3 Q2 Q8 Q20 Q21 Q22 Q23 KB3].
    pose proof scl_rng as SCL. pose proof stk272 as S272. ceil.
    assert (Nmod : needed mod 4096 = 0) by (rewrite Eml, Z.mul_comm; apply Z.mod_mul; lia).
    pose proof (pru_aligned needed ltac:(lia) Nmod) as PRU.
    assert (LIM3 : In m (s_limbo s3)) by (rewrite EL3; left; reflexivity).
    destruct (wG_limbo s3 L (WF_groups s3 L W3) m LIM3) as (_ & NG3 & NL3 & NF3).
    destruct (metaU_rng s3 L W3 m Um3) as (MR1 & MR2 & MR8).
    (* [comment removed for export] *)
    assert (SOK64 : store_ok RSEGS M3 (Z_to_bv 64 (sp - 144 - 64)) 64%nat = true).
    { eapply (store_ok_defined M3 (sp - ASSTK d) sp); [exact DF3 | lia | cbn; lia | lia | lia]. }
    rewrite zbv_m1 in A14.
    destruct (mmW1_34 M3 (sp - 144) 0 needed 3 34 ltac:((first [ (clear MR8 Nmod H0 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ])) SOK64 ltac:((first [ (clear MR8 H0 FR3 Herr3 Rbig Hpnd Hsingle HL_E; lia) | lia ])) r4 rom eq_refl Q2 A10 A11 A12 A13 A14 A15)
      as (r5 & RUN5 & C2 & C17 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & K5).
    eapply kat_msteps; [exact Hh3 | exact Hlz3 | exact RUN5 |].
    set (M4 := mm_frame M3 (sp - 144) (getr r4 1) (getr r4 8) (getr r4 9) (getr r4 18) (getr r4 19) (getr r4 20) (getr r4 21)).
    (* [comment removed for export] *)
    pose proof (proj1 (LEDGERX_nil s3 _) LG3) as HLX.
    destruct (budget L mdl d HBUD s3 mdl3 W3 NJ3 ltac:(rewrite EL3, zlen_cons; unfold zlen in *; lia) Hlim3) as (_ & HCR & HRS).
    destruct (ledgerx_grant_rw s3 L [] mdl3 W3 HLX xok_nil Hlz3 Hmat3 (getr r5 10) needed ltac:((first [ (clear MR8 H0 FR3 Herr3 Rbig Hpnd Hsingle HL_E; lia) | lia ])) ltac:(cbn [length Z.of_nat]; (first [ (clear MR8 Nmod H0 FR3 Rbig Hpnd Hsingle HL_E; lia) | lia ]))
                ltac:(rewrite XSUM_nil; (first [ (clear MR8 H0 FR3 Rbig Hpnd Hsingle HL_E; lia) | lia ]))) as (a0 & GR0 & _).
    assert (M4W : forall y, 0 <= y < 2 ^ 64 -> M4 (Z_to_bv 64 y) <> M3 (Z_to_bv 64 y) -> sp - 208 <= y < sp - 144).
    { intros y Hy NE. unfold M4, mm_frame in NE. wdiff NE M3 y. }
    assert (G34 : mem_grows M3 M4) by (intros z Hz; unfold M4, mm_frame; repeat apply (wbytes_grows _ _ _ z); exact Hz).
    apply (kat_of_kfx F bo).
    apply (as_kfx_mmap_rw F r5 (0x63d3c%bv : word) M4 rom mdl3 W_63ce8 needed HL Hh3 Hlz3 F_63ce8 E_63ce8 C17 C11 ltac:(lia) C12 C13 C14 C15 bi bo).
    { rewrite PRU. exists a0. exact GR0. }
    { (* [comment removed for export] *)
      unfold mmrw_fail. replace (errno_ret ENOMEM) with (Z_to_bv 64 (2 ^ 64 - 12)) by (apply bv_eq; reflexivity).
      replace (v_addi (0x63d3c%bv : word) 4) with (0x63d40%bv : word) by (apply bv_eq; reflexivity).
      pose proof (rc_errno s3 M3 (rp_statics s3 M3 RP3)) as Cerr.
      assert (SOKe : store_ok RSEGS M4 (Z_to_bv 64 A_ERRNO) 4%nat = true).
      { eapply store_ok_mono; [exact G34|]. apply store_ok_wseg. vm_compute. reflexivity. }
      assert (SOK16 : store_ok RSEGS M4 (Z_to_bv 64 (sp - 144 - 80)) 16%nat = true).
      { eapply store_ok_mono; [exact G34|]. eapply (store_ok_defined M3 (sp - ASSTK d) sp); [exact DF3 | lia | cbn; lia | lia | lia]. }
      assert (STK4 : forall dd v, 8 <= dd <= 56 -> rdn RSEGS M4 (Z_to_bv 64 (sp - 144 - dd)) 8%nat = Some (word_to_le_bytes 8 v) ->
                     rdn RSEGS M4 (Z_to_bv 64 (sp - 144 - dd)) 8%nat = Some (word_to_le_bytes 8 v)) by (intros; assumption).
      destruct (mmW2f M4 (sp - 144) 0 ltac:(unfold A_ERRNO, TPV; (first [ (clear MR8 Nmod H0 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ])) SOK16 SOKe ltac:((first [ (clear MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ]))
                  (regupd r5 10 (Z_to_bv 64 (2 ^ 64 - 12))) rom (getr r4 1) (getr r4 8) (getr r4 9) (getr r4 18) (getr r4 19) (getr r4 20) (getr r4 21)
                  ltac:(rewrite A1; apply ret_ok_even; reflexivity)
                  ltac:(gres; exact C2) ltac:(gres; reflexivity) ltac:(gres; exact C16) ltac:(gres; kept_rw K5; kept_rw KB3; exact R4)
                  ltac:(unfold M4, mm_frame; rdn_solve) ltac:(unfold M4, mm_frame; rdn_solve) ltac:(unfold M4, mm_frame; rdn_solve)
                  ltac:(unfold M4, mm_frame; rdn_solve) ltac:(unfold M4, mm_frame; rdn_solve) ltac:(unfold M4, mm_frame; rdn_solve)
                  ltac:(unfold M4, mm_frame; rdn_solve))
        as (rf & RUNf & Z2 & Z10 & Z1 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Kf').
      eapply (kf_msteps RSEGS F HL); [exact Hh3 | exact Hlz3 | exact RUNf |].
      rewrite A1. replace (Z_to_bv 64 406256) with (0x632f0%bv : word) by (apply bv_eq; reflexivity).
      set (Mf := mm_ffail M4 (sp - 144) (getr (regupd r5 10 (Z_to_bv 64 (2 ^ 64 - 12))) 8)) in *.
      set (Ms := wbytes (wbytes M4 (Z_to_bv 64 (sp - 144 - 72)) (word_to_le_bytes 8 (Z_to_bv 64 0x63d60)))
                        (Z_to_bv 64 (sp - 144 - 80)) (word_to_le_bytes 8 (getr (regupd r5 10 (Z_to_bv 64 (2 ^ 64 - 12))) 8))).
      assert (EMf : Mf = wbytes Ms (Z_to_bv 64 A_ERRNO) errno12) by reflexivity.
      assert (MsW : forall y, 0 <= y < 2 ^ 64 -> Ms (Z_to_bv 64 y) <> M3 (Z_to_bv 64 y) -> sp - 224 <= y < sp - 144).
      { intros y Hy NE. destruct (decide (Ms (Z_to_bv 64 y) = M4 (Z_to_bv 64 y))) as [E0|NE0].
        - rewrite E0 in NE. pose proof (M4W y Hy NE). lia.
        - unfold Ms in NE0. revert NE0. generalize M4. intros Mb NE0. wdiff NE0 Mb y. }
      assert (MfW : forall y, 0 <= y < 2 ^ 64 -> Mf (Z_to_bv 64 y) <> M3 (Z_to_bv 64 y) ->
                    (sp - 224 <= y < sp - 144) \/ (A_ERRNO <= y < A_ERRNO + 4)).
      { intros y Hy NE. rewrite EMf in NE. destruct (decide (wbytes Ms (Z_to_bv 64 A_ERRNO) errno12 (Z_to_bv 64 y) = Ms (Z_to_bv 64 y))) as [E0|NE0].
        - rewrite E0 in NE. left. exact (MsW y Hy NE).
        - right. unfold errno12, A_ERRNO, TPV in NE0 |- *. revert NE0. generalize Ms. intros Mb NE0. wdiff NE0 Mb y. }
      assert (G3s : mem_grows M3 Ms).
      { eapply mem_grows_trans; [exact G34|]. unfold Ms. do 2 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. }
      assert (G3f : mem_grows M3 Mf).
      { eapply mem_grows_trans; [exact G3s|]. rewrite EMf. apply wbytes_grows. }
      assert (REPs : REP s3 Ms).
      { apply (REP_frame s3 L M3 W3 RP3 Ms G3s). intros y Hy NE. left. pose proof (MsW y Hy NE). ceil. lia. }
      apply (kf_of_kat F HL).
      apply (L_FM st L M mdl regs rom sp sc req (Kf F) d Hsc Hreq Hlimbo R2 Rra Hsp HQF (set_errno s3 12) Mf mdl3 rf m (0x632f0%bv : word)).
      - constructor.
        + apply WF_set_errno; [exact W3 | lia].
        + apply (REP_set_errno s3 L Ms Mf 12 W3 REPs). split.
          * unfold cell. rewrite EMf. unfold errno12, A_ERRNO, TPV. pose proof (rdn_wbytes_hit RSEGS (word_to_le_bytes 4 (Z_to_bv 64 12))) as RH.
            rewrite length_N_to_le_bytes in RH. apply RH. zsimp; lia.
          * intros a NE. pose proof (u64_range a) as AR.
            assert (Eaa : a = Z_to_bv 64 (bv_unsigned a)) by (apply bv_eq; rewrite u_Z2bv by lia; reflexivity).
            rewrite Eaa, EMf in NE |- *. unfold errno12, A_ERRNO, TPV in NE |- *.
            pose proof (wbytes_diff_g Ms (550176 - 164) (word_to_le_bytes 4 (Z_to_bv 64 12)) (bv_unsigned a) ltac:(lia) ltac:(rewrite length_N_to_le_bytes; cbn; lia) AR NE) as IN.
            rewrite length_N_to_le_bytes in IN. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in IN. split; [rewrite u_Z2bv by lia; lia|].
            apply wbytes_inside_some; wd_lenlit; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
        + apply (LEDGER_set_errno s3). exact LG3.
        + exact Hh3. + exact Hlz3. + exact Hmat3. + exact Hfs3. + exact Hfds3. + exact Hlim3.
        + exact Hcan3.
        + exact LM3.
        + exact MU3.
        + intros a Ha NE. destruct (decide (Mf (Z_to_bv 64 a) = M3 (Z_to_bv 64 a))) as [E|NE2].
          * apply FR3; [exact Ha | congruence].
          * destruct (MfW a Ha NE2) as [A|A]; [left; lia | right; right; right; exact A].
        + eapply defined_grows; [exact G3f | exact DF3].
        + apply (stk_transfer st regs sp sc req d Hsc Hreq Hsp M3 Mf); [|exact SK3]. intros y Hy.
          destruct (decide (Mf (Z_to_bv 64 y) = M3 (Z_to_bv 64 y))) as [E|NE]; [exact E|]. exfalso.
          destruct (MfW y ltac:(ceil; (first [ (clear MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ])) NE) as [A|A]; ceil; unfold A_ERRNO, TPV in *; (first [ (clear MR8 Nmod H0 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ]).
        + rewrite Z2. reflexivity.
        + rewrite Z20. exact Q20.
        + eapply keeps_big; [| exact Kf' | reflexivity]. apply keeps_but_upd; [|apply in_regs_dec; reflexivity].
          eapply keeps_big; [exact KB3 | exact K5 | reflexivity].
      - exact NJ3.
      - exact EL3.
      - exact NLm.
      - rewrite Z9. exact A9.
      - kept_rw Kf'. gres. kept_rw K5. exact Q22.
      - exact Z10.
      - right. split; [reflexivity|]. rewrite Z18. exact A18. }
    (* [comment removed for export] *)
    intros aw GR. apply (kfx_of_kat F HL bi). unfold mmrw_grant. rewrite PRU in GR |- *.
    replace (v_addi (0x63d3c%bv : word) 4) with (0x63d40%bv : word) by (apply bv_eq; reflexivity).
    pose proof GR as GR'. unfold grant_ok in GR'. rewrite !Bool.andb_true_iff in GR'. destruct GR' as [[[[GA1 GA2] GA3] GA4] GA5].
    apply Z.eqb_eq in GA1. apply Z.ltb_lt in GA2. apply Z.leb_le in GA3. unfold page_size in GA1.
    set (p0 := bv_unsigned aw) in *.
    assert (Ea : aw = Z_to_bv 64 p0) by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
    pose proof GA4 as GA4'. rewrite (lx_res s3 [] _ HLX) in GA4'.
    destruct (grant_range_hz (m_vmmaps mdl3) (vm_maps (m_vmmaps mdl3)) aw (Z_to_bv 64 needed) (lx_top s3 [] _ HLX) GA4'
                ltac:(rewrite u_Z2bv by (first [ (clear GA1 MR8 H0 FR3 Herr3 Rbig Hpnd Hsingle HL_E; lia) | lia ]); (first [ (clear GA1 MR8 H0 FR3 Herr3 Rbig Hpnd Hsingle HL_E; lia) | lia ])) ltac:(fold p0; (first [ (clear MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ])) ltac:(rewrite u_Z2bv by (first [ (clear GA1 MR8 H0 FR3 Herr3 Rbig Hpnd Hsingle HL_E; lia) | lia ]); exact Nmod) ltac:(rewrite u_Z2bv by (first [ (clear GA1 MR8 H0 FR3 Herr3 Rbig Hpnd Hsingle HL_E; lia) | lia ]); fold p0; (first [ (clear MR8 H0 FR3 Herr3 Rbig Hpnd Hsingle HL_E; lia) | lia ]))) as [HCE IMGF].
    rewrite u_Z2bv in HCE by lia. rewrite u_Z2bv in IMGF by lia. fold p0 in HCE, IMGF.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (HP0 : p0 mod 4096 = 0 /\ HEAPLO <= p0 /\ p0 + needed <= CEIL) by (unfold HEAPLO; (first [ (clear MR8 Herr3 Rbig Hpnd Hsingle HL_E; lia) | lia ])).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (HRF : region_free (vm_reserved (m_vmmaps mdl3) ++ vm_maps (m_vmmaps mdl3)) (Z_to_bv 64 p0) (Z_to_bv 64 needed) = true) by (rewrite <- Ea; exact GA4).
    pose proof (proj1 (rf_apart s3 L [] _ W3 HLX xok_nil p0 needed ltac:(lia) ltac:(lia) (proj2 (proj2 HP0)) HRF)) as AP.
    rewrite Ea. set (M5 := zfill (Z_to_bv 64 p0) (Z_to_bv 64 needed) M4).
    set (mdl5 := mmap_model (Z_to_bv 64 p0) (Z_to_bv 64 needed) mdl3).
    pose (h1 := mkVmMapsFull (vm_reserved (m_vmmaps mdl3)) ((Z_to_bv 64 p0, Z_to_bv 64 needed) :: vm_maps (m_vmmaps mdl3)) (vm_noaccess (m_vmmaps mdl3))
               (vm_start_brk (m_vmmaps mdl3)) (vm_brk (m_vmmaps mdl3)) (vm_limit (m_vmmaps mdl3)) (vm_mmap_base (m_vmmaps mdl3)) (vm_init_sp (m_vmmaps mdl3))).
    pose proof (with_vmmaps_facts h1 mdl3) as MF. change (with_vmmaps h1 mdl3) with mdl5 in MF. destruct MF as (MF1 & MF2 & MF3 & MF4 & MF5 & MF6).
    assert (HLX5 : LEDGERX s3 [(Z_to_bv 64 p0, Z_to_bv 64 needed)] (m_vmmaps mdl5)).
    { rewrite MF1. destruct LG3 as [G1 G2 G3 G4 G5]. constructor; cbn [h1 vm_maps vm_noaccess vm_brk vm_start_brk vm_reserved vm_mmap_base vm_init_sp app].
      - apply perm_skip. exact G1.
      - exact G2.
      - exact G3.
      - exact G4.
      - exact G5. }
    (* [comment removed for export] *)
    ceil; unfold HEAPLO in HP0.
    assert (M5W : forall y, 0 <= y < 2 ^ 64 -> M5 (Z_to_bv 64 y) <> M3 (Z_to_bv 64 y) -> (sp - 208 <= y < sp - 144) \/ (p0 <= y < p0 + needed)).
    { intros y Hy NE. unfold M5 in NE.
      destruct (decide (zfill (Z_to_bv 64 p0) (Z_to_bv 64 needed) M4 (Z_to_bv 64 y) = M4 (Z_to_bv 64 y))) as [E0|NE0].
      - rewrite E0 in NE. left. exact (M4W y Hy NE).
      - right. exact (zfill_diffZ _ p0 needed y ltac:((first [ (clear MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ])) ltac:((first [ (clear GA1 MR8 H0 FR3 Herr3 Rbig Hpnd Hsingle HL_E; lia) | lia ])) ltac:((first [ (clear MR8 H0 FR3 Herr3 Rbig Hpnd Hsingle HL_E; lia) | lia ])) Hy NE0). }
    assert (G35 : mem_grows M3 M5).
    { intros z Hz. unfold M5. apply zfill_grows. unfold M4, mm_frame. repeat apply (wbytes_grows _ _ _ z). exact Hz. }
    assert (REP5 : REP s3 M5).
    { assert (REP4 : REP s3 M4).
      { apply (REP_frame s3 L M3 W3 RP3 M4).
        - intros z Hz. unfold M4, mm_frame. repeat apply (wbytes_grows _ _ _ z). exact Hz.
        - intros y Hy NE. left. pose proof (M4W y Hy NE). ceil. lia. }
      apply (REP_agree_but s3 L M4 M5 p0 (p0 + needed) W3 REP4).
      - intros y Hy NE. exact (zfill_diffZ _ p0 needed y ltac:((first [ (clear MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ])) ltac:((first [ (clear GA1 MR8 H0 FR3 Herr3 Rbig Hpnd Hsingle HL_E; lia) | lia ])) ltac:((first [ (clear MR8 H0 FR3 Herr3 Rbig Hpnd Hsingle HL_E; lia) | lia ])) Hy NE).
      - unfold HEAPLO. lia.
      - intros y Hy. split.
        + intros [D|[D|[D|(x & Hx & Kx & D)]]]; [unfold A_ERRNO, TPV in *; (first [ (clear AP HP0 IMGF GA1 MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ]) | unfold CTX_END, CTX in *; (first [ (clear AP HP0 IMGF GA1 MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ]) | |].
          * destruct D as (ar & Har & R). destruct (area_in_region s3 L W3 ar Har) as (r & Hr & _ & W1 & W2). destruct (AP r Hr); (first [ (clear MR8 H0 FR3 Herr3 Rbig Hpnd Hsingle; lia) | lia ]).
          * pose proof (wg_kind s3 L x (wG_each s3 L (WF_groups s3 L W3) x Hx)) as KD. rewrite Kx in KD. destruct KD as (Y1 & Y2 & _).
            destruct (AP _ Y2); cbn [rg_base rg_len] in *; (first [ (clear MR8 H0 FR3 Rbig Hpnd Hsingle HL_E; lia) | lia ]).
        + intros (x & Hx & G). pose proof (gcell_in_span s3 L W3 x y Hx G).
          destruct (ge_inreg s3 (WF_geom s3 L W3) x Hx) as (r & Hr & W1 & W2). destruct (AP r Hr); (first [ (clear MR8 H0 FR3 Herr3 Rbig Hpnd Hsingle; lia) | lia ]). }
    (* [comment removed for export] *)
    assert (STK5 : forall dd v, 8 <= dd <= 56 -> rdn RSEGS M4 (Z_to_bv 64 (sp - 144 - dd)) 8%nat = Some (word_to_le_bytes 8 v) ->
                   rdn RSEGS M5 (Z_to_bv 64 (sp - 144 - dd)) 8%nat = Some (word_to_le_bytes 8 v)).
    { intros dd v Hd' R. unfold M5. rewrite rdn_zfill_outZ by (cbn; (first [ (clear MR8 H0 Herr3 Rbig Hpnd Hsingle HL_E; lia) | lia ])). exact R. }
    destruct (mmW2 (sp - 144) 0 ltac:((first [ (clear AP HP0 IMGF GA1 MR8 Nmod H0 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ])) ltac:((first [ (clear M5W AP HP0 IMGF GA1 MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ])) (regupd r5 10 (Z_to_bv 64 p0)) rom M5 p0
                (getr r4 1) (getr r4 8) (getr r4 9) (getr r4 18) (getr r4 19) (getr r4 20) (getr r4 21)
                ltac:((first [ (clear MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ])) ltac:(right; (first [ (clear MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ])) ltac:(rewrite A1; apply ret_ok_even; reflexivity)
                ltac:(gres; exact C2) ltac:(gres; reflexivity) ltac:(gres; exact C16)
                (STK5 8 _ ltac:((first [ (clear M5W AP HP0 IMGF GA1 MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ])) ltac:(unfold M4, mm_frame; rdn_solve)) (STK5 16 _ ltac:((first [ (clear M5W AP HP0 IMGF GA1 MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ])) ltac:(unfold M4, mm_frame; rdn_solve))
                (STK5 24 _ ltac:((first [ (clear M5W AP HP0 IMGF GA1 MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ])) ltac:(unfold M4, mm_frame; rdn_solve)) (STK5 32 _ ltac:((first [ (clear M5W AP HP0 IMGF GA1 MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ])) ltac:(unfold M4, mm_frame; rdn_solve))
                (STK5 40 _ ltac:((first [ (clear M5W AP HP0 IMGF GA1 MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ])) ltac:(unfold M4, mm_frame; rdn_solve)) (STK5 48 _ ltac:((first [ (clear M5W AP HP0 IMGF GA1 MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ])) ltac:(unfold M4, mm_frame; rdn_solve))
                (STK5 56 _ ltac:((first [ (clear M5W AP HP0 IMGF GA1 MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ])) ltac:(unfold M4, mm_frame; rdn_solve)))
      as (r6 & RUN6 & D2 & D10 & D1 & D8 & D9 & D18 & D19 & D20 & D21 & K6).
    eapply kat_msteps; [rewrite MF2; exact Hh3 | rewrite MF3; exact Hlz3 | exact RUN6 |].
    rewrite A1. replace (Z_to_bv 64 406256) with (0x632f0%bv : word) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    set (ctr := c_mmap_ctr (s_ctx s3)). pose proof (wc_ctr s3 (WF_ctx s3 L W3)) as CTR. fold ctr in CTR.
    destruct (meta_cells s3 L M5 W3 REP5 m Um3) as (arm & km & Harm & _ & _ & _ & _ & _ & RMm & DEFar & Alo & Ahi).
    rewrite Zm3 in RMm. destruct RMm as [Cm0 Cm8 Cm16 Cm24 Cm28 Cm32]. cbn [mr_prev mr_next mr_mem mr_avail mr_freed mr_W meta_zero] in Cm0, Cm8, Cm16, Cm24, Cm28, Cm32.
    pose proof (meta_store_ok s3 L M5 W3 REP5 m Um3) as SOKm5.
    pose proof (ctx_store_ok s3 M5 REP5) as SOKc5.
    pose proof (rc_ctr s3 M5 (rp_ctx s3 M5 REP5)) as Cctr. fold ctr in Cctr.
    assert (F24 : getr r6 24 = Z_to_bv 64 (16 * size_class sc)) by (kept_rw K6; gres; kept_rw K5; exact A24).
    assert (F25 : getr r6 25 = Z_to_bv 64 cnt3) by (kept_rw K6; gres; kept_rw K5; exact A25).
    assert (F22 : getr r6 22 = Z_to_bv 64 MLOCK) by (kept_rw K6; gres; kept_rw K5; exact Q22).
    destruct (aM5 M5 m p0 0 ctr needed cnt3 (size_class sc) SCL Hc3 ltac:(ceil; unfold HEAPLO in *; (first [ (clear M5W AP IMGF GA1 Nmod Herr3 Rbig Hpnd Hsingle HL_E; lia) | lia ])) ltac:((first [ (clear MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ])) ltac:((first [ (clear M5W AP HP0 IMGF GA1 MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ])) CTR ltac:(split; [(first [ (clear GA1 MR8 H0 FR3 Herr3 Rbig Hpnd Hsingle HL_E; lia) | lia ]) | exact Nmod])
                Cm32 Cctr SOKm5 SOKc5 r6 rom D10 ltac:(rewrite D18; exact A18) ltac:(rewrite D19; exact A19) ltac:(rewrite D9; exact A9) F24 F22 F25)
      as (r7 & RUN7 & H10 & H11 & H12 & H25 & K7).
    eapply kat_msteps; [rewrite MF2; exact Hh3 | rewrite MF3; exact Hlz3 | exact RUN7 |].
    set (M7 := m_m5 M5 m 0 ctr needed) in *.
    set (aidx := aidx_of (16 * size_class sc) cnt3) in *.
    pose proof (aidx_of_rng (16 * size_class sc) cnt3 ltac:(lia) ltac:(lia)) as AIR. fold aidx in AIR.
    set (ctr' := (ctr + 1) mod 2 ^ 32) in *. pose proof (Z.mod_pos_bound (ctr + 1) (2 ^ 32) ltac:(lia)) as CTR'. fold ctr' in CTR'.
    (* [comment removed for export] *)
    assert (APm : m + 40 <= p0 \/ p0 + needed <= m).
    { destruct (area_in_region s3 L W3 arm Harm) as (rr & Hrr & _ & W1 & W2). destruct (AP rr Hrr); (first [ (clear H0 FR3 Herr3 Rbig Hpnd Hsingle HL_E; lia) | lia ]). }
    assert (Z5 : forall y, p0 <= y < p0 + needed -> M5 (Z_to_bv 64 y) = Some (Z_to_bv 8 0)).
    { intros y Hy. unfold M5. apply zfill_inZ; (first [ (clear MR8 H0 FR3 Herr3 Rbig Hpnd Hsingle HL_E; lia) | lia ]). }
    assert (M7W : forall y, 0 <= y < 2 ^ 64 -> M7 (Z_to_bv 64 y) <> M5 (Z_to_bv 64 y) -> (m + 32 <= y < m + 40) \/ (ctx_mmap_counter <= y < ctx_mmap_counter + 4)).
    { intros y Hy NE. unfold M7, m_m5, ctx_mmap_counter, CTX in *. ceil; unfold HEAPLO in *. wdiff NE M5 y. }
    assert (G57 : mem_grows M5 M7) by (unfold M7, m_m5, ctx_mmap_counter, CTX; eapply mem_grows_trans; apply wbytes_grows).
    ceil; unfold ctx_usage, ctx_active, ctx_mmap_counter, CTX, HEAPLO in *.
    assert (C7u : cell M7 (682024 + 464 + 8 * sc) 8 (c_usage (s_ctx s3) sc)).
    { unfold M7, m_m5, ctx_mmap_counter, CTX. peel. peel. exact (rc_usage s3 M5 (rp_ctx s3 M5 REP5) sc Hsc). }
    assert (C7a : cell M7 (682024 + 80 + 8 * sc) 8 0).
    { unfold M7, m_m5, ctx_mmap_counter, CTX. peel. peel. pose proof (rc_active s3 M5 (rp_ctx s3 M5 REP5) sc Hsc) as C. rewrite (wc_active s3 (WF_ctx s3 L W3) sc Hsc), Hnil3 in C. exact C. }
    assert (C7W : cell M7 (m + 32) 8 needed).
    { unfold M7, m_m5, ctx_mmap_counter, CTX. peel. change (0 mod 4096 + needed) with needed. hit. }
    assert (C7m8 : cell M7 (m + 8) 8 0) by (unfold M7, m_m5, ctx_mmap_counter, CTX; peel; peel; exact Cm8).
    assert (C7m0 : cell M7 m 8 0) by (unfold M7, m_m5, ctx_mmap_counter, CTX; peel; peel; exact Cm0).
    assert (B8 : M7 (Z_to_bv 64 (p0 + 8)) = Some (Z_to_bv 8 0)).
    { destruct (decide (M7 (Z_to_bv 64 (p0 + 8)) = M5 (Z_to_bv 64 (p0 + 8)))) as [E|NE]; [rewrite E; apply Z5; lia|].
      exfalso. destruct (M7W (p0 + 8) ltac:((first [ (clear M7W MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ])) NE); (first [ (clear Nmod H0 FR3 Herr3 Rbig Hpnd Hsingle HL_E; lia) | lia ]). }
    assert (SOKc7 : store_ok RSEGS M7 (Z_to_bv 64 682024) 928%nat = true) by (apply store_ok_wseg; vm_compute; reflexivity).
    assert (SOKm7 : store_ok RSEGS M7 (Z_to_bv 64 m) 40%nat = true).
    { eapply (store_ok_defined M7 arm (arm + 4096)); [eapply defined_grows; [exact G57 | exact DEFar] | (first [ (clear M5W AP HP0 IMGF GA1 Nmod H0 FR3 Herr3 Rbig Hpnd Hsingle HL_E; lia) | lia ]) | cbn; (first [ (clear M5W AP HP0 IMGF GA1 Nmod H0 FR3 Herr3 Rbig Hpnd Hsingle HL_E; lia) | lia ]) | (first [ (clear M7W APm M5W AP HP0 IMGF GA1 MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ]) | (first [ (clear M7W APm M5W AP HP0 IMGF GA1 MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ])]. }
    assert (SOKp7 : store_ok RSEGS M7 (Z_to_bv 64 p0) 9%nat = true).
    { eapply (store_ok_defined M7 p0 (p0 + needed)); [| (first [ (clear M7W MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ]) | cbn; (first [ (clear M7W MR8 H0 FR3 Herr3 Rbig Hpnd Hsingle HL_E; lia) | lia ]) | (first [ (clear M7W MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ]) | (first [ (clear M7W MR8 H0 FR3 Herr3 Rbig Hpnd Hsingle HL_E; lia) | lia ])]. intros y Hy. apply G57. rewrite (Z5 y Hy). discriminate. }
    pose proof (wc_usage s3 (WF_ctx s3 L W3) sc) as UR.
    (* [comment removed for export] *)
    destruct (aCommon M7 m p0 sc cnt3 aidx (c_usage (s_ctx s3) sc) needed 0 Hsc Hc3 AIR UR ltac:(ceil; unfold HEAPLO in *; (first [ (clear M5W AP IMGF GA1 Nmod Herr3 Rbig Hpnd Hsingle HL_E; lia) | lia ])) ltac:(ceil; unfold HEAPLO in *; (first [ (clear M7W MR8 Nmod Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ])) ltac:((first [ (clear Nmod H0 FR3 Herr3 Rbig Hpnd Hsingle HL_E; lia) | lia ])) ltac:((first [ (clear M7W GA1 MR8 H0 FR3 Herr3 Rbig Hpnd Hsingle HL_E; lia) | lia ])) ltac:((first [ (clear M7W APm M5W AP HP0 IMGF GA1 MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ]))
                C7u C7a C7W C7m8 C7m0 (rdn1_of_byte _ _ _ B8) SOKc7 SOKm7 SOKp7 r7 rom
                ltac:(kept_rw K7; kept_rw K6; gres; kept_rw K5; exact Q23)
                ltac:(kept_rw K7; rewrite D21; unfold ctx_active, CTX; exact Q21)
                ltac:(kept_rw K7; rewrite D8; exact Q8)
                H25 ltac:(kept_rw K7; rewrite D9; exact A9) H10 H11 H12) as (r8 & RUN8 & O10 & O9 & K8).
    eapply kat_msteps; [rewrite MF2; exact Hh3 | rewrite MF3; exact Hlz3 | exact RUN8 |].
    set (MF := m_com M7 m p0 sc cnt3 aidx (c_usage (s_ctx s3) sc) needed 0) in *.
    assert (G7F : mem_grows M7 MF) by (unfold MF, m_com; do 11 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    assert (G5F : mem_grows M5 MF) by (eapply mem_grows_trans; [exact G57 | exact G7F]).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof ceil_rng as CRN. pose proof (metaU_img s3 L W3 m Um3) as IMm.
    assert (BWR : forall y, 0 <= y < 2 ^ 64 -> MF (Z_to_bv 64 y) <> M5 (Z_to_bv 64 y) ->
                  (m <= y < m + 40) \/ (p0 <= y < p0 + needed) \/ (682024 + 12 <= y < 682024 + 12 + 4) \/
                  (682024 + 464 + 8 * sc <= y < 682024 + 464 + 8 * sc + 8) \/ (682024 + 80 + 8 * sc <= y < 682024 + 80 + 8 * sc + 8)).
    { intros y Hy NE.
      destruct (decide (MF (Z_to_bv 64 y) = M7 (Z_to_bv 64 y))) as [EF|NEF].
      - rewrite EF in NE. destruct (M7W y Hy NE); (first [ (clear H0 FR3 Herr3 Hpnd; lia) | lia ]).
      - unfold MF, m_com, AVc, FRc, AVc', Wn, AIb, ctx_usage, ctx_active, CTX in NEF.
        rewrite <- (w2le1 (Z.lor (Z.land 0 224) aidx)) in NEF by (rewrite Z.land_0_l, Z.lor_0_l; lia). clear - NEF Hy Hsc Hc3 AIR MR1 MR2 HP0 HCE IMGF APm Eml Mpos N20 CTR CTR' UR CRN IMm. wdiff2 NEF M7 y. }
    assert (HMmeta : rep_meta MF m (MR m m p0 (av_of aidx) (fr_of cnt3 aidx) (MhASlotKTop.W ml sc cnt3))).
    { replace (av_of aidx) with (AVc' aidx) by (unfold av_of, brange, AVc'; change (2 ^ 1) with 2; reflexivity).
      replace (fr_of cnt3 aidx) with (FRc cnt3 aidx) by (unfold fr_of, brange, FRc; reflexivity).
      replace (MhASlotKTop.W ml sc cnt3) with (Wn sc cnt3 needed) by (unfold MhASlotKTop.W, mkW, Wn; rewrite Nmod; lia).
      clear - Hsc Hc3 AIR MR1 MR2 HP0 HCE IMGF APm Eml Mpos N20 CTR CTR' UR CRN IMm.
      unfold MF, m_com, ctx_usage, ctx_active, CTX. constructor; cbn [mr_prev mr_next mr_mem mr_avail mr_freed mr_W]; cellw. }
    assert (HMa : cell MF p0 8 m) by (clear - Hsc Hc3 AIR MR1 MR2 HP0 HCE IMGF APm Eml Mpos N20 CTR CTR' UR CRN IMm; unfold MF, m_com, ctx_usage, ctx_active, CTX; cellw).
    assert (HMai : byte_at MF (p0 + 8) aidx).
    { clear - Hsc Hc3 AIR MR1 MR2 HP0 HCE IMGF APm Eml Mpos N20 CTR CTR' UR CRN IMm. unfold MF, m_com, AIb, ctx_usage, ctx_active, CTX. do 5 bpeel. unfold byte_at. rewrite Z.land_0_l, Z.lor_0_l. apply byte_hit. }
    assert (HMz : forall y, p0 + 9 <= y < p0 + 4096 * ml -> MF (Z_to_bv 64 y) = Some (Z_to_bv 8 0)).
    { intros y Hy. rewrite <- Eml in Hy. destruct (decide (MF (Z_to_bv 64 y) = M5 (Z_to_bv 64 y))) as [E|NE]; [rewrite E; apply Z5; lia|]. exfalso.
      assert (Hy64 : 0 <= y < 2 ^ 64) by (clear - Hy Hsc Hc3 AIR MR1 MR2 HP0 HCE IMGF APm Eml Mpos N20 CTR CTR' UR CRN IMm; zlia).
      destruct (BWR y Hy64 NE) as [A|[A|[A|[A|A]]]]; [clear - A Hy Hsc Hc3 AIR MR1 MR2 HP0 HCE IMGF APm Eml Mpos N20 CTR CTR' UR CRN IMm; zlia | | clear - A Hy Hsc Hc3 AIR MR1 MR2 HP0 HCE IMGF APm Eml Mpos N20 CTR CTR' UR CRN IMm; zlia | clear - A Hy Hsc Hc3 AIR MR1 MR2 HP0 HCE IMGF APm Eml Mpos N20 CTR CTR' UR CRN IMm; zlia | clear - A Hy Hsc Hc3 AIR MR1 MR2 HP0 HCE IMGF APm Eml Mpos N20 CTR CTR' UR CRN IMm; zlia].
      (* [comment removed for export] *)
      destruct (decide (MF (Z_to_bv 64 y) = M7 (Z_to_bv 64 y))) as [EF|NEF].
      - rewrite EF in NE. destruct (M7W y Hy64 NE) as [A'|A']; clear - A' Hy Hsc Hc3 AIR MR1 MR2 HP0 HCE IMGF APm Eml Mpos N20 CTR CTR' UR CRN IMm; zlia.
      - unfold MF, m_com, AVc, FRc, AVc', Wn, AIb, ctx_usage, ctx_active, CTX in NEF.
        rewrite <- (w2le1 (Z.lor (Z.land 0 224) aidx)) in NEF by (rewrite Z.land_0_l, Z.lor_0_l; lia).
        clear - NEF Hy A Hsc Hc3 AIR MR1 MR2 HP0 HCE IMGF APm Eml Mpos N20 CTR CTR' UR CRN IMm.
        rewrite !wbytes_outZ in NEF by (wd_lenlit; rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact (NEF eq_refl). }
    assert (HMdef : defined MF p0 (p0 + 4096 * ml)) by (intros y Hy; apply G5F; rewrite <- Eml in Hy; rewrite (Z5 y Hy); discriminate).
    assert (HMctr : cell MF (682024 + 12) 4 ctr').
    { clear - Hsc Hc3 AIR MR1 MR2 HP0 HCE IMGF APm Eml Mpos N20 CTR CTR' UR CRN IMm. unfold MF, m_com, ctx_usage, ctx_active, CTX. do 11 peel. unfold M7, m_m5, ctx_mmap_counter, CTX. peel || idtac. hit. }
    assert (HMusage : cell MF (682024 + 464 + 8 * sc) 8 ((c_usage (s_ctx s3) sc + cnt3) mod 2 ^ 64)).
    { clear - Hsc Hc3 AIR MR1 MR2 HP0 HCE IMGF APm Eml Mpos N20 CTR CTR' UR CRN IMm. unfold MF, m_com, ctx_usage, ctx_active, CTX. do 10 peel. unfold cell. rewrite zbv_mod64. apply cell_hit; cbn; lia. }
    assert (HMact : cell MF (682024 + 80 + 8 * sc) 8 m) by (clear - Hsc Hc3 AIR MR1 MR2 HP0 HCE IMGF APm Eml Mpos N20 CTR CTR' UR CRN IMm; unfold MF, m_com, ctx_usage, ctx_active, CTX; cellw).
    clear CRN IMm.
    pose proof (Z.mod_pos_bound (c_usage (s_ctx s3) sc + cnt3) (2 ^ 64) ltac:(lia)) as UR'.
    assert (AP' : forall r, In r (s_regions s3) -> rg_base r + rg_len r <= p0 \/ p0 + 4096 * ml <= rg_base r).
    { intros r Hr. rewrite <- Eml. destruct (AP r Hr); lia. }
    destruct (newtop_close s3 L M5 MF m p0 ml ctr' sc cnt3 aidx ((c_usage (s_ctx s3) sc + cnt3) mod 2 ^ 64)
                W3 REP5 Um3 NG3 NL3 NF3 ltac:(rewrite <- Eml; ceil; unfold HEAPLO; (first [ (clear UR' HMusage M7W MR8 Herr3 Rbig Hpnd Hsingle HL_E; lia) | lia ])) ltac:(rewrite <- Eml; exact IMGF) ltac:((first [ (clear UR' HMusage BWR M7W APm M5W AP HP0 IMGF GA1 MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd HL_E; lia) | lia ])) AP' CTR' Hsc Hnil3 Hc3 AIR UR'
                ltac:(rewrite <- Eml; exact Hfit) ltac:(exact Hq) ltac:(unfold GRPMAX; (first [ (clear UR' HMusage BWR M7W APm M5W AP HP0 IMGF GA1 MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd HL_E; lia) | lia ])) Hsingle Hpnd sp sp ltac:(ceil; pose proof stk272; (first [ (clear AP' UR' HMusage BWR M7W APm AP IMGF GA1 MR8 Nmod Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ]))
                ltac:(intros y Hy NE; unfold b_wr; rewrite <- Eml; unfold ctx_mmap_counter, ctx_usage, ctx_active, CTX;
                      destruct (BWR y Hy NE) as [A|[A|[A|[A|A]]]]; [left | right; left | right; right; left | right; right; right; left | right; right; right; right; left]; exact A)
                G5F HMmeta HMa HMai HMz HMdef HMctr HMusage HMact) as [W4 RP4].
    set (s4 := MhASlotKTop.st' s3 m p0 ml ctr' sc cnt3 aidx ((c_usage (s_ctx s3) sc + cnt3) mod 2 ^ 64)) in *.
    pose proof (newtop_facts s3 L m p0 ml ctr' sc cnt3 aidx ((c_usage (s_ctx s3) sc + cnt3) mod 2 ^ 64) W3 NG3 ltac:((first [ (clear UR' HMusage BWR M7W APm M5W AP HP0 IMGF GA1 MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd HL_E; lia) | lia ])) Hsc Hc3)
      as (Gm4 & Sm4 & Lm4 & STm4 & _ & SCm4 & Km4 & _ & ML4 & AL4 & _ & _ & LB4 & RG4 & SO4 & IG4).
    fold s4 in Gm4, Sm4, Lm4, STm4, SCm4, Km4, ML4, AL4, LB4, RG4, SO4, IG4.
    pose proof (MhASlotKTop.t_ledger s3 m p0 ml ctr' sc cnt3 aidx ((c_usage (s_ctx s3) sc + cnt3) mod 2 ^ 64) _ ltac:(rewrite <- Eml; exact HLX5)) as LG4. fold s4 in LG4.
    (* [comment removed for export] *)
    assert (STKEQ : forall y, sp - 96 <= y < sp -> MF (Z_to_bv 64 y) = M3 (Z_to_bv 64 y)).
    { intros y Hy. destruct (decide (MF (Z_to_bv 64 y) = M5 (Z_to_bv 64 y))) as [E|NE].
      - rewrite E. destruct (decide (M5 (Z_to_bv 64 y) = M3 (Z_to_bv 64 y))) as [E2'|NE2']; [exact E2'|]. exfalso. destruct (M5W y ltac:((first [ (clear IG4 AP' UR' HMusage APm AP HP0 IMGF GA1 MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ])) NE2'); (first [ (clear IG4 UR' HMusage MR8 H0 Herr3 Rbig Hpnd Hsingle HL_E; lia) | lia ]).
      - exfalso. destruct (BWR y ltac:((first [ (clear IG4 AP' UR' HMusage APm AP HP0 IMGF GA1 MR8 Nmod H0 FR3 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ])) NE) as [A|[A|[A|[A|A]]]]; (first [ (clear H0 FR3 Herr3 Hpnd; lia) | lia ]). }
    assert (P4 : PTE s4 MF mdl5 r8).
    { constructor.
      - exact W4.
      - exact RP4.
      - exact LG4.
      - rewrite MF2. exact Hh3.
      - rewrite MF3. exact Hlz3.
      - rewrite MF4. exact Hmat3.
      - rewrite MF5. exact Hfs3.
      - rewrite MF6. exact Hfds3.
      - rewrite MF1. cbn [h1 vm_limit]. exact Hlim3.
      - exact Hcan3.
      - exact Herr3.
      - intros k Hk. change (s_alist s4 k) with (fupd (s_alist s3) sc [m] k). unfold fupd. destruct (Z.eqb_spec k sc); [(first [ (clear AP' UR' HMusage M5W AP HP0 IMGF GA1 Nmod H0 FR3 Rbig Hpnd Hsingle; lia) | lia ]) | exact (BL3 k Hk)].
      - intros x Hx. change (s_meta s4 x) with (MhASlotKTop.b_meta s3 m p0 ml sc cnt3 aidx x). unfold MhASlotKTop.b_meta.
        destruct (Z.eqb_spec x m) as [->|NEx]; [exfalso; exact (NLm Hx) | exact (LM3 x Hx)].
      - intros x Ux. exact (MU3 x Ux).
      - intros a Ha NE. destruct (decide (MF (Z_to_bv 64 a) = M5 (Z_to_bv 64 a))) as [E|NEa].
        + rewrite E in NE. destruct (decide (M5 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a))) as [E3|NE3].
          * rewrite E3 in NE. exact (FR3 a Ha NE).
          * destruct (M5W a Ha NE3) as [A|A]; [left; (first [ (clear IG4 AP' UR' HMusage BWR M7W APm AP HP0 IMGF GA1 MR8 Nmod H0 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ]) | right; left]. split; [ceil; unfold HEAPLO; (first [ (clear IG4 AP' UR' HMusage BWR M7W APm M5W AP IMGF GA1 MR8 Nmod Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ])|]. split; [clear -A IMGF; lia|]. apply (fresh_nonapp L d s3 p0 needed a W3); [|exact A].
            intros r Hr. destruct (AP r Hr); lia.
        + destruct (BWR a Ha NEa) as [A|[A|[A|[A|A]]]].
          * destruct (meta_WOK L sp d s3 m a W3 Um3 A) as [B|[B|[B|B]]]; [left; lia | right; left; exact B | right; right; left; exact B | right; right; right; exact B].
          * right; left. split; [ceil; unfold HEAPLO; (first [ (clear IG4 AP' UR' HMusage BWR M7W APm M5W AP IMGF GA1 MR8 Nmod Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ])|]. split; [clear -A IMGF; lia|]. apply (fresh_nonapp L d s3 p0 needed a W3); [|exact A]. intros r Hr. destruct (AP r Hr); lia.
          * right; right; left. unfold CTX_END, CTX. lia.
          * right; right; left. unfold CTX_END, CTX. (first [ (clear IG4 AP' UR' HMusage BWR M7W APm M5W AP HP0 IMGF GA1 MR8 Nmod H0 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ]).
          * right; right; left. unfold CTX_END, CTX. (first [ (clear IG4 AP' UR' HMusage BWR M7W APm M5W AP HP0 IMGF GA1 MR8 Nmod H0 Herr3 XG Rbig Hpnd Hsingle HL_E; lia) | lia ]).
      - eapply defined_grows; [exact G5F|]. eapply defined_grows; [exact G35 | exact DF3].
      - ceil. exact (stk_transfer st regs sp sc req d Hsc Hreq Hsp M3 MF STKEQ SK3).
      - kept_rw K8. kept_rw K7. exact D2.
      - kept_rw K8. kept_rw K7. rewrite D20. exact Q20.
      - eapply keeps_big; [|exact K8|reflexivity]. eapply keeps_big; [|exact K7|reflexivity]. eapply keeps_big; [|exact K6|reflexivity].
        apply keeps_but_upd; [|apply in_regs_dec; reflexivity]. eapply keeps_big; [exact KB3 | exact K5 | reflexivity]. }
    (* [comment removed for export] *)
    apply (HL_E s4 MF mdl5 r8 m 0 P4 (XG s4 Km4 SCm4 Lm4 ltac:(rewrite ML4; exact (eq_sym Eml)) IG4)).
    - rewrite LB4, EL3. unfold zremove. cbn [List.filter]. rewrite Z.eqb_refl. cbn [negb]. apply zremove_notin. exact NLm.
    - rewrite AL4. reflexivity.
    - exact Gm4.
    - exact SCm4.
    - rewrite Lm4. (first [ (clear IG4 AP' BWR M7W APm M5W AP HP0 IMGF GA1 MR8 Nmod H0 FR3 Herr3 Rbig HL_E; lia) | lia ]).
    - exact Sm4.
    - intros x k o Hx Hk E. destruct (proj1 (IG4 x) Hx) as [->|Hx3].
      + split; [reflexivity|]. change (s_slot s4 m k) with (MhASlotKTop.b_slot s3 m aidx m k) in E. unfold MhASlotKTop.b_slot in E. rewrite Z.eqb_refl in E.
        unfold nslot_of in E. destruct (Z.eqb_spec k 0); [lia|]. destruct (k <=? aidx); discriminate E.
      + exfalso. assert (Hxm : x <> m) by (intros ->; exact (NG3 Hx3)).
        rewrite (SO4 x k Hx Hxm) in E.
        assert (GLx : g_lastidx s4 x = g_lastidx s3 x).
        { unfold g_lastidx, g_W. change (s_meta s4 x) with (MhASlotKTop.b_meta s3 m p0 ml sc cnt3 aidx x). unfold MhASlotKTop.b_meta.
          destruct (Z.eqb_spec x m) as [Ex|_]; [exfalso; exact (Hxm Ex) | reflexivity]. }
        rewrite GLx in Hk. exact (NJ3 x k o Hx3 Hk E).
    - rewrite STm4. exact Rq4.
    - rewrite STm4. exact Rbig.
    - exact O10.
  Qed.

  Lemma w8_zero_nth : forall j, nth j (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 8 0) = Z_to_bv 8 0.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. intros j. change (word_to_le_bytes 8 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0) 8). apply nth_repeat. Qed.

  (* [comment removed for export] *)
  Lemma pt_pol : forall s1 Mc mdl1 r Mc' r' q' b' sq' (WS : Z -> Prop),
    PT s1 Mc mdl1 r ->
    (forall i, 0 <= q' i < 256) -> (forall i, 0 <= b' i < 256) -> 0 <= sq' < 256 ->
    (forall a, 0 <= a < 2 ^ 64 -> Mc' (Z_to_bv 64 a) <> Mc (Z_to_bv 64 a) -> CTX + 464 <= a < CTX + 913 /\ WS a) ->
    mem_grows Mc Mc' ->
    (forall j, 0 <= j < 48 -> forall a, ctx_usage j <= a < ctx_usage j + 8 -> ~ WS a) ->
    (forall i, 0 <= i < 32 -> cell Mc' (ctx_unmap_seq i) 1 (q' i) \/ (q' i = c_unmap_seq (s_ctx s1) i /\ ~ WS (ctx_unmap_seq i))) ->
    (forall i, 0 <= i < 32 -> cell Mc' (ctx_bounces i) 1 (b' i) \/ (b' i = c_bounces (s_ctx s1) i /\ ~ WS (ctx_bounces i))) ->
    (cell Mc' ctx_seq 1 sq' \/ (sq' = c_seq (s_ctx s1) /\ ~ WS ctx_seq)) ->
    getr r' 2 = getr r 2 -> getr r' 8 = getr r 8 -> getr r' 20 = getr r 20 -> getr r' 21 = getr r 21 ->
    getr r' 22 = getr r 22 -> getr r' 23 = getr r 23 -> keeps_but BIG regs r' ->
    PT (MhPolicy.st' s1 (c_usage (s_ctx s1)) q' b' sq') Mc' mdl1 r'.
  Proof using Hsp Hreq Hsc req. clear - Hsp Hreq Hsc req.
    intros s1 Mc mdl1 r Mc' r' q' b' sq' WS P Hq Hb Hsq WR G NU HMq HMb HMs E2 E8 E20 E21 E22 E23 K'.
    pose proof P as [W1 RP1 LG1 Hh1 Hlz1 Hmat1 Hfs1 Hfds1 Hlim1 Hcan1 Herr1 BL1 LM1 MU1 FR1 DF1 SK1 Q2 Q8 Q20 Q21 Q22 Q23 KB].
    destruct (policy_close s1 L Mc Mc' (spc sp d) (c_usage (s_ctx s1)) q' b' sq' WS W1 RP1 (wc_usage s1 (WF_ctx s1 L W1)) Hq Hb Hsq
                (spc_ok sp d Hsp) ltac:(intros a Ha NE; right; exact (WR a Ha NE)) G
                ltac:(intros j Hj; right; split; [reflexivity | exact (NU j Hj)]) HMq HMb HMs) as [W2 RP2].
    apply (pt_step st L M mdl regs sp sc req d Hsc Hreq Hsp s1 Mc mdl1 r _ Mc' r' P W2 RP2 eq_refl eq_refl eq_refl eq_refl
             ltac:(intros; reflexivity) ltac:(intros; reflexivity) ltac:(intros x Ux; exact Ux) G); try assumption.
    intros a Ha NE. destruct (WR a Ha NE) as [A _]. apply ctx_WOK. unfold CTX_END. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma L_M : forall M2 mdl2 r m,
    GBR s2g M2 mdl2 r m cntg -> 2048 < 16 * size_class sc * cntg + 16 ->
    kat RSEGS (mkCfg (mkst r (0x62f0c%bv : word) M2 rom) mdl2) (kfx F bo).
  Proof using HL_E HQF Hsp R4 Rra R2 HBUD Hreq Hlimbo Hsc HL bi. clear - HL_E HQF Hsp R4 Rra R2 HBUD Hreq Hlimbo Hsc HL bi.
    intros M2 mdl2 r m GB Hbig.
    destruct GB as (P2 & NJ2 & EL2 & Hnil & Um & Zm & NLm & G9 & G10 & G11 & G18 & G19 & G24 & G25 & G14 & G12 & C1 & C2 & C3 & C4).
    pose proof P2 as [W2 RP2 LG2 Hh2 Hlz2 Hmat2 Hfs2 Hfds2 Hlim2 Hcan2 Herr2 BL2 LM2 MU2 FR2 DF2 SK2 Q2 Q8 Q20 Q21 Q22 Q23 KB].
    pose proof scl_rng as SCL.
    (* [comment removed for export] *)
    assert (CONT2 : forall s3 M3 r3 nosm,
      PT s3 M3 mdl2 r3 -> nojunk s3 -> s_limbo s3 = m :: s_limbo st -> s_alist s3 sc = [] -> metaU s3 m -> s_meta s3 m = meta_zero ->
      c_usage (s_ctx s3) = c_usage (s_ctx s2g) -> s_groups s3 = s_groups s2g -> nosm_of s2g = nosm ->
      0 <= nosm <= 1 -> getr r3 13 = Z_to_bv 64 nosm -> getr r3 15 = Z_to_bv 64 31 ->
      getr r3 9 = Z_to_bv 64 m -> getr r3 10 = Z_to_bv 64 (c_usage (s_ctx s2g) sc) -> getr r3 11 = Z_to_bv 64 4096 -> getr r3 18 = Z_to_bv 64 req ->
      getr r3 19 = Z_to_bv 64 cntg -> getr r3 24 = Z_to_bv 64 (16 * size_class sc) -> getr r3 14 = Z_to_bv 64 (16 * size_class sc * cntg) ->
      getr r3 12 = Z_to_bv 64 (16 * size_class sc + 16) ->
      kat RSEGS (mkCfg (mkst r3 (0x631ec%bv : word) M3 rom) mdl2) (kfx F bo)).
    { intros s3 M3 r3 nosm P3 NJ3 EL3 Hnil3 Um3 Zm3 EU GEQ HNS Hns T13 T15 T9 T10 T11 T18 T19 T24 T14 T12.
      pose proof P3 as [W3 RP3 LG3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ U2 U8 U20 U21 U22 U23 KB3].
      pose proof (wc_usage s2g (WF_ctx s2g L W2)) as UR2. pose proof (wc_usage s3 (WF_ctx s3 L W3)) as UR3.
      (* [comment removed for export] *)
      destruct (aM2 M3 sc (size_class sc) cntg (c_usage (s_ctx s2g) sc) (c_usage (s_ctx s3) (sc + 1)) nosm Hsc SCL C1 (UR2 sc) (UR3 (sc + 1)) Hns
                  ltac:(intros A B; exact (rc_usage s3 M3 (rp_ctx s3 M3 RP3) (sc + 1) ltac:(lia))) r3 rom T15 U8 U23 T10 T19 T13 T11 T14)
        as (r4 & RUN4 & V25 & V10 & K4).
      eapply kat_msteps; [exact (p_h _ _ _ _ _ _ _ _ _ _ _ _ P3) | exact (p_lz _ _ _ _ _ _ _ _ _ _ _ _ P3) | exact RUN4 |].
      set (u' := ucoarse sc (c_usage (s_ctx s2g) sc) (c_usage (s_ctx s3) (sc + 1))) in *.
      pose proof (ucoarse_rng sc (c_usage (s_ctx s2g) sc) (c_usage (s_ctx s3) (sc + 1)) (UR2 sc)) as UR'. fold u' in UR'.
      set (cnt2 := mred sc (16 * size_class sc) cntg u' nosm) in *.
      pose proof (MhASlotKMF.mmap_arm_facts sc cntg u' nosm req Hsc C1 C2 C3 C4 Hreq Hns) as MAF.
      cbv zeta in MAF. fold cnt2 in MAF.
      destruct MAF as (C2r & C3r & Eml & Mpos & N20 & Hfit & Hq & S16 & Hsingle & Hpnd & Rq4 & Rbig').
      destruct (aM3 M3 (size_class sc) cnt2 req u' nosm SCL C2r ltac:(lia) UR' Hns r4 rom ltac:(kept_rw K4; exact T24) V25 ltac:(kept_rw K4; exact T11)
                  ltac:(kept_rw K4; exact T13) ltac:(kept_rw K4; exact T18) ltac:(kept_rw K4; exact T12) V10) as (r5 & RUN5 & X25 & X19 & K5).
      eapply kat_msteps; [exact (p_h _ _ _ _ _ _ _ _ _ _ _ _ P3) | exact (p_lz _ _ _ _ _ _ _ _ _ _ _ _ P3) | exact RUN5 |].
      set (cnt3 := fst (m3 (16 * size_class sc) cnt2 req u' nosm)) in *. set (needed := snd (m3 (16 * size_class sc) cnt2 req u' nosm)) in *.
      destruct (aM4 M3 needed r5 rom X19) as (r6 & RUN6 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y18 & Y1 & K6).
      eapply kat_msteps; [exact (p_h _ _ _ _ _ _ _ _ _ _ _ _ P3) | exact (p_lz _ _ _ _ _ _ _ _ _ _ _ _ P3) | exact RUN6 |].
      apply (mtail s3 M3 mdl2 r6 m cnt3 needed); try assumption.
      - apply (pt_regs st L M mdl regs sp sc d s3 M3 mdl2 r3 r6 P3); try (kept_rw K6; kept_rw K5; kept_rw K4; reflexivity).
        eapply keeps_big; [eapply keeps_big; [eapply keeps_big; [exact KB3 | exact K4 | reflexivity] | exact K5 | reflexivity] | exact K6 | reflexivity].
      - kept_rw K6. kept_rw K5. kept_rw K4. exact T9.
      - kept_rw K6. exact X19.
      - kept_rw K6. kept_rw K5. kept_rw K4. exact T24.
      - kept_rw K6. exact X25.
      - (* [comment removed for export] *)
        intros s1 K1 S1 L1 ML1 IG1. split; [exact K1|]. split; [exact S1|].
        assert (ECN : cn_of s2g cntg = (cnt3, needed)).
        { subst cnt3 needed cnt2 u'. unfold cn_of. rewrite EU, HNS. apply surjective_pairing. }
        rewrite ECN. cbn [fst snd]. split; [exact L1|]. split; [exact ML1|].
        intros x. rewrite (IG1 x). unfold is_group. rewrite GEQ. tauto. }
    (* [comment removed for export] *)
    assert (CONT1 : forall s3 M3 r3 nosm,
      PT s3 M3 mdl2 r3 -> nojunk s3 -> s_limbo s3 = m :: s_limbo st -> s_alist s3 sc = [] -> metaU s3 m -> s_meta s3 m = meta_zero ->
      c_usage (s_ctx s3) = c_usage (s_ctx s2g) -> s_groups s3 = s_groups s2g -> nosm_of s2g = nosm ->
      0 <= nosm <= 1 -> getr r3 13 = Z_to_bv 64 nosm -> getr r3 16 = Z_to_bv 64 (c_seq (s_ctx s3)) ->
      getr r3 9 = Z_to_bv 64 m -> getr r3 10 = Z_to_bv 64 (c_usage (s_ctx s2g) sc) -> getr r3 11 = Z_to_bv 64 4096 -> getr r3 18 = Z_to_bv 64 req ->
      getr r3 19 = Z_to_bv 64 cntg -> getr r3 24 = Z_to_bv 64 (16 * size_class sc) -> getr r3 14 = Z_to_bv 64 (16 * size_class sc * cntg) ->
      getr r3 12 = Z_to_bv 64 (16 * size_class sc + 16) ->
      kat RSEGS (mkCfg (mkst r3 (0x631c0%bv : word) M3 rom) mdl2) (kfx F bo)).
    { intros s3 M3 r3 nosm P3 NJ3 EL3 Hnil3 Um3 Zm3 EU GEQ HNS Hns T13 T16 T9 T10 T11 T18 T19 T24 T14 T12.
      pose proof P3 as [W3 RP3 LG3 Hh3 Hlz3 _ _ _ _ _ _ _ _ _ _ _ _ U2 U8 U20 U21 U22 U23 KB3].
      pose proof (wc_seq s3 (WF_ctx s3 L W3)) as Rseq. pose proof (ctx_store_ok s3 M3 RP3) as SOKc3.
      destruct (Z.eq_dec (c_seq (s_ctx s3)) 255) as [E255|N255].
      - destruct (aSeqW M3 (c_seq (s_ctx s3)) SOKc3 r3 rom T16 U22 E255) as (r4 & RUN4 & V15 & V16 & K4).
        eapply kat_msteps; [exact Hh3 | exact Hlz3 | exact RUN4 |].
        assert (WR : forall y, 0 <= y < 2 ^ 64 -> m_seqW M3 (Z_to_bv 64 y) <> M3 (Z_to_bv 64 y) -> CTX + 848 <= y < CTX + 880 \/ y = CTX + 912).
        { intros y Hy NE. unfold m_seqW, ctx_unmap_seq, ctx_seq, CTX in NE. unfold CTX. rewrite <- (w2le1 1) in NE by lia. wdiff2 NE M3 y. }
        assert (GR : mem_grows M3 (m_seqW M3)) by (intros z Hz; unfold m_seqW; repeat apply (wbytes_grows _ _ _ z); exact Hz).
        assert (P4 : PT (MhPolicy.st' s3 (c_usage (s_ctx s3)) (fun _ => 0) (c_bounces (s_ctx s3)) 1) (m_seqW M3) mdl2 r4).
        { apply (pt_pol s3 M3 mdl2 r3 (m_seqW M3) r4 (fun _ => 0) (c_bounces (s_ctx s3)) 1 (fun y => CTX + 848 <= y < CTX + 880 \/ y = CTX + 912) P3
                   ltac:(intros; lia) (wc_bnc s3 (WF_ctx s3 L W3)) ltac:(lia)); try (kept_rw K4; reflexivity).
          + intros y Hy NE. pose proof (WR y Hy NE). unfold CTX in *. lia.
          + exact GR.
          + intros j Hj y Hy [W|W]; unfold ctx_usage, CTX in *; lia.
          + intros i Hi. left. unfold cell. apply byte_at_rdn1. unfold byte_at, m_seqW. unfold ctx_unmap_seq, ctx_seq, CTX.
            rewrite wbytes_outZ by (cbn; lia).
            assert (IN : forall (Mb : mem) b, b <= 682024 + 848 + i < b + 8 -> 0 <= b -> b + 8 < 2 ^ 64 ->
                      wbytes Mb (Z_to_bv 64 b) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 (682024 + 848 + i)) = Some (Z_to_bv 8 0)).
            { intros Mb b Hb Hb0 Hb8. rewrite wbytes_inside; [rewrite w8_zero_nth; reflexivity | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia |].
              rewrite length_N_to_le_bytes, !u_Z2bv by lia. cbn. lia. }
            destruct (Z.lt_ge_cases i 24); [|apply IN; lia].
            rewrite wbytes_outZ by (wd_lenlit; rewrite ?length_N_to_le_bytes; cbn; lia).
            destruct (Z.lt_ge_cases i 16); [|apply IN; lia].
            rewrite wbytes_outZ by (wd_lenlit; rewrite ?length_N_to_le_bytes; cbn; lia).
            destruct (Z.lt_ge_cases i 8); [|apply IN; lia].
            rewrite wbytes_outZ by (wd_lenlit; rewrite ?length_N_to_le_bytes; cbn; lia).
            apply IN; lia.
          + intros i Hi. right. split; [reflexivity|]. intros [W|W]; unfold ctx_bounces, CTX in *; lia.
          + left. unfold cell, m_seqW. unfold ctx_seq, ctx_unmap_seq, CTX. rewrite <- (w2le1 1) by lia. apply cell_hit; cbn; lia.
          + eapply keeps_big; [exact KB3 | exact K4 | reflexivity]. }
        apply (CONT2 _ (m_seqW M3) r4 nosm P4); try assumption; try (kept_rw K4; assumption); try (cbn; exact EU); try (cbn; exact GEQ).
        all: rewrite ?EU; try reflexivity; kept_rw K4; rewrite ?T10, ?EU; reflexivity.
      - destruct (aSeqN M3 (c_seq (s_ctx s3)) Rseq SOKc3 r3 rom T16 U22 N255) as (r4 & RUN4 & V15 & V16 & K4).
        eapply kat_msteps; [exact Hh3 | exact Hlz3 | exact RUN4 |].
        assert (WR : forall y, 0 <= y < 2 ^ 64 -> m_seqN M3 (c_seq (s_ctx s3)) (Z_to_bv 64 y) <> M3 (Z_to_bv 64 y) -> y = CTX + 912).
        { intros y Hy NE. unfold m_seqN, ctx_seq, CTX in NE. unfold CTX. rewrite <- (w2le1 (c_seq (s_ctx s3) + 1)) in NE by lia. wdiff2 NE M3 y. }
        assert (GR : mem_grows M3 (m_seqN M3 (c_seq (s_ctx s3)))) by (intros z Hz; unfold m_seqN; apply (wbytes_grows _ _ _ z); exact Hz).
        assert (P4 : PT (MhPolicy.st' s3 (c_usage (s_ctx s3)) (c_unmap_seq (s_ctx s3)) (c_bounces (s_ctx s3)) (c_seq (s_ctx s3) + 1)) (m_seqN M3 (c_seq (s_ctx s3))) mdl2 r4).
        { apply (pt_pol s3 M3 mdl2 r3 (m_seqN M3 (c_seq (s_ctx s3))) r4 (c_unmap_seq (s_ctx s3)) (c_bounces (s_ctx s3)) (c_seq (s_ctx s3) + 1) (fun y => y = CTX + 912) P3
                   (wc_useq s3 (WF_ctx s3 L W3)) (wc_bnc s3 (WF_ctx s3 L W3)) ltac:(lia)); try (kept_rw K4; reflexivity).
          + intros y Hy NE. pose proof (WR y Hy NE). unfold CTX in *. lia.
          + exact GR.
          + intros j Hj y Hy W; unfold ctx_usage, CTX in *; lia.
          + intros i Hi. right. split; [reflexivity|]. intros W; unfold ctx_unmap_seq, CTX in *; lia.
          + intros i Hi. right. split; [reflexivity|]. intros W; unfold ctx_bounces, CTX in *; lia.
          + left. unfold cell, m_seqN. unfold ctx_seq, CTX. rewrite <- (w2le1 (c_seq (s_ctx s3) + 1)) by lia. apply cell_hit; cbn; lia.
          + eapply keeps_big; [exact KB3 | exact K4 | reflexivity]. }
        apply (CONT2 _ (m_seqN M3 (c_seq (s_ctx s3))) r4 nosm P4); try assumption; try (kept_rw K4; assumption); try (cbn; exact EU); try (cbn; exact GEQ).
        all: rewrite ?EU; try reflexivity; kept_rw K4; rewrite ?T10, ?EU; reflexivity. }
    (* [comment removed for export] *)
    pose proof (rc_seq s2g M2 (rp_ctx s2g M2 RP2)) as Cseq. pose proof (wc_seq s2g (WF_ctx s2g L W2)) as Rseq.
    pose proof (cell1_rdn M2 ctx_seq _ Rseq Cseq) as Mseq.
    pose proof (ctx_store_ok s2g M2 RP2) as SOKc.
    destruct (decide (7 <= sc <= 38)) as [IN|OUT].
    - set (b := c_bounces (s_ctx s2g) (sc - 7)). set (useq := c_unmap_seq (s_ctx s2g) (sc - 7)).
      pose proof (wc_bnc s2g (WF_ctx s2g L W2) (sc - 7)) as Rb. fold b in Rb. pose proof (wc_useq s2g (WF_ctx s2g L W2) (sc - 7)) as Ru. fold useq in Ru.
      pose proof (cell1_rdn M2 _ _ Rb (rc_bnc s2g M2 (rp_ctx s2g M2 RP2) (sc - 7) ltac:(lia))) as Mb. fold b in Mb.
      pose proof (cell1_rdn M2 _ _ Ru (rc_useq s2g M2 (rp_ctx s2g M2 RP2) (sc - 7) ltac:(lia))) as Mu. fold useq in Mu.
      assert (NS : 0 <= nosmall_of b <= 1) by (unfold nosmall_of; destruct (b <? 100); lia).
      assert (HNS : nosm_of s2g = nosmall_of b).
      { unfold nosm_of. replace ((7 <=? sc) && (sc <=? 38))%bool with true by (symmetry; apply Bool.andb_true_iff; split; apply Z.leb_le; lia). reflexivity. }
      assert (GEQ0 : s_groups s2g = s_groups s2g) by reflexivity.
      destruct (decide (useq = 0 \/ 10 <= c_seq (s_ctx s2g) - useq)) as [NB|BB].
      + destruct (aM1nb M2 sc b useq (c_seq (s_ctx s2g)) Hsc Rb Ru Rseq Mseq IN Mb Mu r rom Q8 Q22 NB) as (r1 & RUN1 & V13 & V16 & K1).
        eapply kat_msteps; [exact Hh2 | exact Hlz2 | exact RUN1 |].
        apply (CONT1 s2g M2 r1 (nosmall_of b)); try assumption; try reflexivity; try (kept_rw K1; assumption).
        apply (pt_regs st L M mdl regs sp sc d s2g M2 mdl2 r r1 P2); try (kept_rw K1; reflexivity). eapply keeps_big; [exact KB | exact K1 | reflexivity].
      + destruct (aM1b M2 sc b useq (c_seq (s_ctx s2g)) Hsc Rb Ru Rseq Mseq SOKc IN Mb Mu r rom Q8 Q22 ltac:(lia) ltac:(lia)) as (r1 & RUN1 & V13 & V16 & K1).
        eapply kat_msteps; [exact Hh2 | exact Hlz2 | exact RUN1 |].
        assert (BU : 0 <= bounce_upd b < 256) by (unfold bounce_upd; destruct (Z.ltb_spec b 99); lia).
        assert (WR : forall y, 0 <= y < 2 ^ 64 -> m_bnc M2 sc b (Z_to_bv 64 y) <> M2 (Z_to_bv 64 y) -> y = CTX + 880 + (sc - 7)).
        { intros y Hy NE. unfold m_bnc, ctx_bounces, CTX in NE. unfold CTX. rewrite <- (w2le1 (bounce_upd b)) in NE by lia. wdiff2 NE M2 y. }
        assert (GR : mem_grows M2 (m_bnc M2 sc b)) by (intros z Hz; unfold m_bnc; apply (wbytes_grows _ _ _ z); exact Hz).
        assert (P3 : PT (MhPolicy.st' s2g (c_usage (s_ctx s2g)) (c_unmap_seq (s_ctx s2g)) (fupd (c_bounces (s_ctx s2g)) (sc - 7) (bounce_upd b)) (c_seq (s_ctx s2g))) (m_bnc M2 sc b) mdl2 r1).
        { apply (pt_pol s2g M2 mdl2 r (m_bnc M2 sc b) r1 (c_unmap_seq (s_ctx s2g)) (fupd (c_bounces (s_ctx s2g)) (sc - 7) (bounce_upd b)) (c_seq (s_ctx s2g)) (fun y => y = CTX + 880 + (sc - 7)) P2
                   (wc_useq s2g (WF_ctx s2g L W2)) ltac:(intros i; unfold fupd; destruct (Z.eqb_spec i (sc - 7)); [lia | apply (wc_bnc s2g (WF_ctx s2g L W2))]) Rseq); try (kept_rw K1; reflexivity).
          * intros y Hy NE. pose proof (WR y Hy NE). unfold CTX in *. lia.
          * exact GR.
          * intros j Hj y Hy W; unfold ctx_usage, CTX in *; lia.
          * intros i Hi. right. split; [reflexivity|]. intros W; unfold ctx_unmap_seq, CTX in *; lia.
          * intros i Hi. unfold fupd. destruct (Z.eqb_spec i (sc - 7)) as [->|NEi].
            -- left. unfold cell, m_bnc. unfold ctx_bounces, CTX. rewrite <- (w2le1 (bounce_upd b)) by lia. apply cell_hit; cbn; lia.
            -- right. split; [reflexivity|]. intros W; unfold ctx_bounces, CTX in *; lia.
          * right. split; [reflexivity|]. intros W; unfold ctx_seq, CTX in *; lia.
          * eapply keeps_big; [exact KB | exact K1 | reflexivity]. }
        apply (CONT1 _ (m_bnc M2 sc b) r1 (nosmall_of b) P3); try assumption; try reflexivity; try (kept_rw K1; assumption).
    - destruct (aM1out M2 sc (c_seq (s_ctx s2g)) Hsc Rseq Mseq r rom Q8 Q22 ltac:(lia)) as (r1 & RUN1 & V13 & V16 & K1).
      eapply kat_msteps; [exact Hh2 | exact Hlz2 | exact RUN1 |].
      assert (HNS : nosm_of s2g = 0).
      { unfold nosm_of. destruct (Z.leb_spec 7 sc); destruct (Z.leb_spec sc 38); cbn [andb]; first [reflexivity | exfalso; lia]. }
      apply (CONT1 s2g M2 r1 0); try assumption; try reflexivity; try lia; try (kept_rw K1; assumption).
      apply (pt_regs st L M mdl regs sp sc d s2g M2 mdl2 r r1 P2); try (kept_rw K1; reflexivity). eapply keeps_big; [exact KB | exact K1 | reflexivity].
  Qed.
  End WithE.
End ASM.
