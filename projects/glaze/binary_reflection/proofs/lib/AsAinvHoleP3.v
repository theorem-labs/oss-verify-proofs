(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAinvLedger2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesMmLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvLedger.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= am_lia.
Import ListNotations.
Import APS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation u := bv_unsigned.
#[local] Notation wseps := APS.seps.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma in_ivz_covered : forall l a, in_ivz l a <-> covered l a = true.
Proof.
  intros l a. (lazymatch goal with |- ?G => let G' := eval unfold in_ivz in G in change_no_check G' end). rewrite <- in_ivs_covered. rewrite in_ivs_true'. split.
  - intros (b & n & Hin & H). exists (b, n). split; [exact Hin | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); exact H].
  - intros ([b n] & Hin & H). exists b, n. split; [exact Hin | exact H].
Qed.

(* [comment removed for export] *)
Definition sep_split (l : list (word * word)) : Prop :=
  forall l1 x l2 y, l = l1 ++ x :: l2 -> In y (l1 ++ l2) -> u (fst x) + u (snd x) <= u (fst y) \/ u (fst y) + u (snd y) <= u (fst x).

Lemma seps_of_split : forall l, sep_split l -> wseps l.
Proof.
  induction l as [|x t IH]; intros H; [apply APS.seps_nil|]. apply APS.seps_cons.
  - rewrite Forall_forall. intros y Hy. exact (H [] x t y eq_refl Hy).
  - apply IH. intros l1 x' l2 y E Hy. apply (H (x :: l1) x' l2 y); [rewrite E; reflexivity | right; exact Hy].
Qed.

Lemma split_of_seps : forall l, wseps l -> sep_split l.
Proof.
  intros l H. induction H as [|p t Hf Hs IH]; intros l1 x l2 y E Hy.
  - destruct l1; discriminate E.
  - destruct l1 as [|w l1'].
    + cbn in E. injection E as <- <-. cbn in Hy. rewrite Forall_forall in Hf. exact (Hf y Hy).
    + cbn in E. injection E as <- E'. destruct Hy as [<-|Hy].
      * rewrite Forall_forall in Hf. subst t.
        pose proof (Hf x ltac:(apply in_app_iff; right; left; reflexivity)) as D. unfold APS.iv_disjoint in D. lia.
      * exact (IH l1' x l2 y E' Hy).
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_ends : forall (a sz : word) lo hi q,
  iv_wf (a, sz) -> 0 <= lo -> lo <= hi -> hi <= 2 ^ 64 -> In q (iv_subtract a sz lo hi) ->
  (u (fst q) = u a /\ u (fst q) + u (snd q) = Z.min (u a + u sz) lo /\ u a < lo)
  \/ (u (fst q) = Z.max (u a) hi /\ u (fst q) + u (snd q) = u a + u sz /\ hi < u a + u sz).
Proof.
  intros a sz lo hi q Hwf Hlo Hlh Hhi Hin. unfold iv_wf, B, S in Hwf. cbn [fst snd] in Hwf.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  unfold iv_subtract in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - destruct (u a <? lo) eqn:El; [|destruct Hin]. apply Z.ltb_lt in El.
    destruct Hin as [<-|[]]. left. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). rewrite u64_lit by lia. lia.
  - destruct (hi <? u a + u sz) eqn:Er; [|destruct Hin]. apply Z.ltb_lt in Er.
    destruct Hin as [<-|[]]. right. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). rewrite !u64_lit by lia. lia.
Qed.

Section Frag.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  #[local] Notation SBEG := (bt_spacebeg bt).
  #[local] Notation R6 := (bt_resv6 bt).
  #[local] Notation E6 := (bt_resv6 bt + bt_resv6_len bt).
  Hypothesis HE6 : E6 <= 2 ^ 64.
  Hypothesis HR6 : 0 <= R6.

  (* [comment removed for export] *)
  Lemma frag_pieces : forall (F6 : list (word * word)) (s : Z),
    Forall (frag_ok bt) F6 -> ivs_wf F6 ->
    (s - SBEG) mod KUSERMAP = 0 -> R6 <= s -> s + KUSERMAP <= E6 ->
    Forall (frag_ok bt) (maps_subtract F6 s (s + KUSERMAP)).
  Proof using HR6 HE6.
    intros F6 s HF HW Hal Hlo Hhi. assert (K0 : 0 < KUSERMAP) by ((lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end); lia).
    rewrite Forall_forall. induction F6 as [|[a sz] t IH]; intros q Hq; [destruct Hq|].
    apply Forall_cons_iff in HF as [Hr Ht]. apply ivs_wf_cons_inv in HW as [Ha Hwt].
    cbn [maps_subtract] in Hq. apply in_app_iff in Hq as [Hq|Hq]; [| exact (IH Ht Hwt q Hq)].
    destruct Hr as (F1 & F2 & F3 & F4 & F5). cbn [fst snd] in F1, F2, F3, F4, F5.
    destruct (iv_subtract_ends a sz s (s + KUSERMAP) q Ha ltac:(lia) ltac:(lia) ltac:(lia) Hq) as [(Q1 & Q2 & Q3)|(Q1 & Q2 & Q3)];
      (lazymatch goal with |- ?G => let G' := eval unfold frag_ok in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end); rewrite Q1 in Q2; rewrite Q1, Q2.
    - split; [lia|]. split; [lia|]. split; [lia|]. split; [exact F4|].
      destruct (Z_le_gt_dec (u a + u sz) s); [rewrite Z.min_l by lia; exact F5 | rewrite Z.min_r by lia; right; left; exact Hal].
    - split; [lia|]. split; [lia|]. split; [lia|]. split; [| exact F5].
      destruct (Z_le_gt_dec (u a) (s + KUSERMAP)); [rewrite Z.max_r by lia | rewrite Z.max_l by lia; exact F4].
      right; left. unfold KUSERMAP in *. replace (s + 2 ^ 18 - SBEG) with (s - SBEG + 1 * 2 ^ 18) by lia.
      rewrite Z.mod_add by lia. exact Hal.
  Qed.

  (* [comment removed for export] *)
  Lemma frag_destroyed : forall (F6 : list (word * word)) (s : Z),
    Forall (frag_ok bt) F6 -> wseps F6 -> ivs_wf F6 ->
    (s - SBEG) mod KUSERMAP = 0 -> R6 <= s -> s + KUSERMAP <= E6 ->
    let F6' := maps_subtract F6 s (s + KUSERMAP) in
    Forall (frag_ok bt) F6' /\ wseps F6' /\ ivs_wf F6'
    /\ (forall a, covered F6' a = true <-> covered F6 a = true /\ ~ (s <= a < s + KUSERMAP)).
  Proof using HR6 HE6.
    intros F6 s HF HS HW Hal Hlo Hhi F6'.
    assert (K0 : 0 < KUSERMAP) by ((lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end); lia).
    destruct (maps_subtract_sem F6 s (s + KUSERMAP) HW ltac:(lia)) as (W' & _ & Cv).
    split; [| split; [| split]].
    - apply frag_pieces; assumption.
    - apply seps_maps_subtract; [exact HS | exact HW | lia].
    - exact W'.
    - intros a. (lazymatch goal with |- ?G => let G' := eval unfold F6' in G in change_no_check G' end). rewrite Cv. rewrite andb_true_iff. (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end). rewrite negb_true_iff, andb_false_iff, Z.leb_gt, Z.ltb_ge. intuition lia.
  Qed.

  (* [comment removed for export] *)
  Lemma frag_remapped : forall (F6 : list (word * word)) (s : Z) (sw nw : word),
    Forall (frag_ok bt) F6 -> wseps F6 -> ivs_wf F6 ->
    (s - SBEG) mod KUSERMAP = 0 -> R6 <= s -> s + KUSERMAP <= E6 ->
    u sw = s -> u nw = KUSERMAP ->
    (forall a, s <= a < s + KUSERMAP -> covered F6 a = false) ->
    let F6' := (sw, nw) :: F6 in
    Forall (frag_ok bt) F6' /\ wseps F6' /\ ivs_wf F6'
    /\ (forall a, covered F6' a = true <-> covered F6 a = true \/ s <= a < s + KUSERMAP).
  Proof using HE6.
    intros F6 s sw nw HF HS HW Hal Hlo Hhi Hs Hn Hfree F6'.
    assert (K0 : 0 < KUSERMAP) by ((lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end); lia).
    split; [| split; [| split]].
    - apply Forall_cons; [| exact HF]. (lazymatch goal with |- ?G => let G' := eval unfold frag_ok in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). rewrite Hs, Hn.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [right; left; exact Hal|].
      right; left. unfold KUSERMAP in *. replace (s + 2 ^ 18 - SBEG) with (s - SBEG + 1 * 2 ^ 18) by lia. rewrite Z.mod_add by lia. exact Hal.
    - apply APS.seps_cons; [| exact HS]. rewrite Forall_forall. intros [b n] Hin. (lazymatch goal with |- ?G => let G' := eval unfold APS.iv_disjoint in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). rewrite Hs, Hn.
      (* [comment removed for export] *)
      destruct (Z_le_gt_dec (s + KUSERMAP) (u b)) as [A|A]; [left; exact A|].
      destruct (Z_le_gt_dec (u b + u n) s) as [B|B]; [right; exact B|]. exfalso.
      rewrite Forall_forall in HF. pose proof (HF (b, n) Hin) as (F1 & F2 & F3 & F4 & F5). cbn [fst snd] in F1, F2, F3, F4, F5.
      (* [comment removed for export] *)
      set (x := Z.max s (u b)).
      assert (Hx : s <= x < s + KUSERMAP /\ u b <= x < u b + u n) by ((lazymatch goal with |- ?G => let G' := eval unfold x in G in change_no_check G' end); lia).
      pose proof (Hfree x (proj1 Hx)) as Hf.
      assert (Hc : covered F6 x = true).
      { apply in_ivz_covered. exists b, n. split; [exact Hin | lia]. }
      congruence.
    - apply ivs_wf_cons; [| exact HW]. (lazymatch goal with |- ?G => let G' := eval unfold iv_wf, B, S in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). rewrite Hs, Hn. lia.
    - intros a. (lazymatch goal with |- ?G => let G' := eval unfold F6' in G in change_no_check G' end). change ((sw, nw) :: F6) with ([(sw, nw)] ++ F6). rewrite covered_app.
      (lazymatch goal with |- ?G => let G' := eval cbn [covered existsb] in G in change_no_check G' end). rewrite orb_false_r, orb_true_iff. (lazymatch goal with |- ?G => let G' := eval unfold in_iv, in_rng, B, S in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end).
      rewrite Hs, Hn, andb_true_iff, Z.leb_le, Z.ltb_lt. am_tauto.
  Qed.
End Frag.
End AsAinvLedger2.
Require LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SymExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AxSymExec3Sound Stdlib.Logic.FunctionalExtensionality.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsanPopFree.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SymExec.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AxSymExec3Sound.
Import Stdlib.Logic.FunctionalExtensionality.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition PW0 : bv 32 := 0x00465713.  (* [comment removed for export] *)
Definition PW1 : bv 32 := 0xfff54793.  (* [comment removed for export] *)
Definition PW2 : bv 32 := 0x00150513.  (* [comment removed for export] *)
Definition PW3 : bv 32 := 0x00279793.  (* [comment removed for export] *)
Definition PW4 : bv 32 := 0x00f587b3.  (* [comment removed for export] *)
Definition PW5 : bv 32 := 0x00e7a023.  (* [comment removed for export] *)
Definition PW6 : bv 32 := 0x01560633.  (* [comment removed for export] *)
Definition PW7 : bv 32 := 0xff3562e3.















Section PopFreeLoop.
Variable segs : list Segment.
Variable p : Z.                       (* [comment removed for export] *)
Hypothesis Hp : (28 <= p)%Z /\ (p + 32 < 2 ^ 64)%Z.
Hypothesis HF0 : fetch_word segs (Z_to_bv 64 p) = Some PW0.
Hypothesis HF1 : fetch_word segs (Z_to_bv 64 (p + 4)) = Some PW1.
Hypothesis HF2 : fetch_word segs (Z_to_bv 64 (p + 8)) = Some PW2.
Hypothesis HF3 : fetch_word segs (Z_to_bv 64 (p + 12)) = Some PW3.
Hypothesis HF4 : fetch_word segs (Z_to_bv 64 (p + 16)) = Some PW4.
Hypothesis HF5 : fetch_word segs (Z_to_bv 64 (p + 20)) = Some PW5.
Hypothesis HF6 : fetch_word segs (Z_to_bv 64 (p + 24)) = Some PW6.
Hypothesis HF7 : fetch_word segs (Z_to_bv 64 (p + 28)) = Some PW7.


Ltac red_if :=
  repeat match goal with
  | |- context [if bv_eqb ?a ?b then ?x else ?y] =>
      let v := eval vm_compute in (bv_eqb a b) in
      lazymatch v with
      | true => change (if bv_eqb a b then x else y) with x
      | false => change (if bv_eqb a b then x else y) with y
      end
  end.


Ltac gr := repeat first [ rewrite getr_same by reg_neq_tac | rewrite getr_other by reg_neq_tac ].













End PopFreeLoop.
End AsanPopFree.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsanPlanSoundSums.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanPlanSound.AxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanPlan.AsanPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanPlan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanPlanSound.
Import AsanPopFree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope Z_scope.

Module APSX.
Import AX2. Import AX2S. Import AP. Import APS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Section Specs.
Variable SEGS : list Segment.






(* [comment removed for export] *)
End Specs.

















(* [comment removed for export] *)
Lemma land_shl_disjoint : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z ->
  Z.land (a * 2 ^ k) b = 0%Z.
Proof.
  intros a b k Ha Hk Hb. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i k) as [Hl|Hh].
  - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - rewrite (Z_testbit_high k b i) by lia. apply Bool.andb_false_r.
Qed.

Lemma lor_shl_disjoint : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z ->
  Z.lor (a * 2 ^ k) b = (a * 2 ^ k + b)%Z.
Proof.
  intros a b k Ha Hk Hb.
  rewrite <- Z.lxor_lor by (apply land_shl_disjoint; lia).
  symmetry. apply Z.add_nocarry_lxor. apply land_shl_disjoint; lia.
Qed.

Lemma Z_to_le_bytes_of_bytes : forall bs,
  Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b rest IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256%Z in Hb.
  pose proof (bytes_le_to_Z_nonneg rest) as Hr.
  assert (Hlor : Z.lor (bv_unsigned b) (Z.shiftl (bytes_le_to_Z rest) 8) = bv_unsigned b + 2 ^ 8 * bytes_le_to_Z rest).
  { rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.lor_comm. rewrite lor_shl_disjoint by lia. lia. }
  rewrite Hlor. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    change (2 ^ 8) with 256 in *. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256 in *.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z rest) / 256) with (bytes_le_to_Z rest) by lia. exact IH.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma word_to_le_bytes_of_bytes : forall bs,
  (length bs <= 8)%nat ->
  word_to_le_bytes (length bs) (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs Hlen. unfold word_to_le_bytes.
  pose proof (AX2S.bytes_le_to_Z_bound bs) as Hb.
  assert (Hlt : bytes_le_to_Z bs < 2 ^ 64).
  { eapply Z.lt_le_trans; [exact (proj2 Hb)|]. apply Z.pow_le_mono_r; lia. }
  rewrite u64_lit by lia. apply Z_to_le_bytes_of_bytes.
Qed.

Lemma word_to_le_bytes_of_bytes_n : forall n bs,
  length bs = n -> (n <= 8)%nat ->
  word_to_le_bytes n (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof. intros n bs <- Hn. apply word_to_le_bytes_of_bytes. exact Hn. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section KnowTests.
Variable segs : list Segment.













End KnowTests.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
(* [comment removed for export] *)
Definition res_len_okP : Prop := length (segments_reserved SEGS) = n_res A.
Definition hull_okP : Prop := 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI.
Hypothesis RES_len : res_len_okP.
Hypothesis HULL_ok : hull_okP.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
(* [comment removed for export] *)
Variable FS0 : Fs.Fs.
(* [comment removed for export] *)
Definition segs_wr_ok : Prop := forall seg, In seg SEGS -> seg_writable seg = true -> seg_readable seg = true.
Hypothesis SEGS_wr : segs_wr_ok.

#[local] Notation cfg := (cfg_of SEGS) (only parsing).
#[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0) (only parsing).
#[local] Notation HID := (hid A argH) (only parsing).
#[local] Notation MR := (Mr A argH) (only parsing).

(* [comment removed for export] *)
#[local] Ltac aps_fill :=
  first [eassumption | exact (fun _ : nat => @None acs) | exact (fun _ _ _ => None) | exact (fun _ _ => None) | exact (fun _ => None)
        | exact 0%nat | exact 0%Z | exact nx0 | exact LIMIT].



















































End Sound.

End APSX.
End AsanPlanSoundSums.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrameE3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvLedger AsAinvLedger2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrameE3.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require AsKSys6.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= am_lia.
#[local] Notation u := bv_unsigned.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma maps_subtract_perm : forall l l' lo hi, Permutation l l' -> Permutation (maps_subtract l lo hi) (maps_subtract l' lo hi).
Proof.
  intros l l' lo hi P. induction P as [| x l l' P IH | x y l | l l' l'' P1 IH1 P2 IH2].
  - constructor.
  - destruct x as [a sz]. (lazymatch goal with |- ?G => let G' := eval cbn [maps_subtract] in G in change_no_check G' end). apply Permutation_app_head. exact IH.
  - destruct x as [a sz]. destruct y as [b sz']. (lazymatch goal with |- ?G => let G' := eval cbn [maps_subtract] in G in change_no_check G' end). rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
  - exact (Permutation_trans IH1 IH2).
Qed.

(* [comment removed for export] *)
Definition off_range (lo hi : Z) (e : word * word) : Prop := 0 < u (snd e) /\ (u (fst e) + u (snd e) <= lo \/ hi <= u (fst e)).
Lemma iv_subtract_id : forall a sz lo hi, lo <= hi -> off_range lo hi (a, sz) -> iv_subtract a sz lo hi = [(a, sz)].
Proof.
  intros a sz lo hi Hlh [P D]. cbn [fst snd] in P, D. (lazymatch goal with |- ?G => let G' := eval unfold iv_subtract in G in change_no_check G' end).
  pose proof (u64_range a) as Ha. pose proof (u64_range sz) as Hs.
  destruct D as [D|D].
  - rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite Z.min_l by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. (lazymatch goal with |- ?G => let G' := eval cbn [app] in G in change_no_check G' end).
    rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. (lazymatch goal with |- ?G => let G' := eval cbn [app] in G in change_no_check G' end). rewrite Z.max_l by lia.
    replace (u a + u sz - u a) with (u sz) by lia. rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma maps_subtract_id : forall l lo hi, lo <= hi -> Forall (off_range lo hi) l -> maps_subtract l lo hi = l.
Proof.
  intros l lo hi Hlh HF. induction l as [|[a sz] t IH]; [reflexivity|]. apply Forall_cons_iff in HF as [H1 H2].
  (lazymatch goal with |- ?G => let G' := eval cbn [maps_subtract] in G in change_no_check G' end). rewrite (iv_subtract_id a sz lo hi Hlh H1), (IH H2). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma in_ivz_iv_subtract : forall a sz lo hi x, 0 <= lo -> lo <= hi -> hi < 2 ^ 64 ->
  in_ivz (iv_subtract a sz lo hi) x <-> (u a <= x < u a + u sz /\ ~ (lo <= x < hi)).
Proof.
  intros a sz lo hi x H0 H1 H2. pose proof (u64_range a) as Ha. pose proof (u64_range sz) as Hs. (lazymatch goal with |- ?G => let G' := eval unfold iv_subtract, in_ivz in G in change_no_check G' end). split.
  - intros (b & n & Hin & R). apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
    + destruct (Z.ltb_spec (u a) lo) as [L|L]; [| destruct Hin]. destruct Hin as [E|[]]. injection E as <- <-.
      rewrite u64_lit in R by lia. lia.
    + destruct (Z.ltb_spec hi (u a + u sz)) as [L|L]; [| destruct Hin]. destruct Hin as [E|[]]. injection E as <- <-.
      rewrite !u64_lit in R by lia. lia.
  - intros [R N].
    destruct (Z.lt_ge_cases x lo) as [X|X].
    + exists a, (Z_to_bv 64 (Z.min (u sz) (lo - u a))). split; [| rewrite u64_lit by lia; lia].
      apply in_app_iff. left. rewrite (proj2 (Z.ltb_lt _ _)) by lia. left. reflexivity.
    + assert (hi <= x) by lia.
      exists (Z_to_bv 64 (Z.max (u a) hi)), (Z_to_bv 64 (u a + u sz - Z.max (u a) hi)). split; [| rewrite !u64_lit by lia; lia].
      apply in_app_iff. right. rewrite (proj2 (Z.ltb_lt _ _)) by lia. left. reflexivity.
Qed.
Lemma in_ivz_maps_subtract : forall l lo hi x, 0 <= lo -> lo <= hi -> hi < 2 ^ 64 ->
  in_ivz (maps_subtract l lo hi) x <-> (in_ivz l x /\ ~ (lo <= x < hi)).
Proof.
  intros l lo hi x H0 H1 H2. induction l as [|[a sz] t IH].
  - (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold in_ivz in G in change_no_check G' end). split; [intros (b & n & [] & _) | intros [(b & n & [] & _) _]].
  - (lazymatch goal with |- ?G => let G' := eval cbn [maps_subtract] in G in change_no_check G' end). unfold in_ivz in *. split.
    + intros (b & n & Hin & R). apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
      * assert (X : in_ivz (iv_subtract a sz lo hi) x) by (exists b, n; split; assumption).
        destruct (proj1 (in_ivz_iv_subtract a sz lo hi x H0 H1 H2) X) as [R' N].
        split; [exists a, sz; split; [left; reflexivity | exact R'] | exact N].
      * assert (X : exists b0 n0 : word, In (b0, n0) (maps_subtract t lo hi) /\ u b0 <= x < u b0 + u n0) by (exists b, n; split; assumption).
        destruct (proj1 IH X) as [(b' & n' & Hin' & R') N].
        split; [exists b', n'; split; [right; exact Hin' | exact R'] | exact N].
    + intros [(b & n & [E|Hin] & R) N].
      * injection E as <- <-. destruct (proj2 (in_ivz_iv_subtract a sz lo hi x H0 H1 H2) (conj R N)) as (b' & n' & Hin' & R').
        exists b', n'. split; [apply in_app_iff; left; exact Hin' | exact R'].
      * assert (X : exists b0 n0 : word, In (b0, n0) t /\ u b0 <= x < u b0 + u n0) by (exists b, n; split; assumption).
        destruct (proj2 IH (conj X N)) as (b' & n' & Hin' & R').
        exists b', n'. split; [apply in_app_iff; right; exact Hin' | exact R'].
Qed.

Lemma sum_classes_ext : forall f g k, (forall c, f c = g c) -> sum_classes f k = sum_classes g k.
Proof. intros f g k E. induction k as [|k IH]; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [sum_classes] in G in change_no_check G' end). rewrite IH, E. reflexivity. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section RegData.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.

  Lemma Rep_regdata_mem : forall st st' Lc FF M mdl mdl',
    st_regdata st st' -> Rep bt st Lc FF M mdl -> rep_ledger bt st' mdl' -> rep_budget bt st' Lc mdl' ->
    Rep bt st' Lc FF M mdl'.
  Proof using.
    intros st st' Lc FF M mdl mdl' EQ R L' B'.
    pose proof EQ as (RD & RO & ECI & EC & ETQ & EGQ & ES & ENR & ED & EH & EIA & EAA & EK & ESH).
    pose proof (quar_regdata st st' EQ) as QR.
    destruct R as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18 & R19).
    (lazymatch goal with |- ?G => let G' := eval unfold Rep in G in change_no_check G' end).
    split; [exact R1|].
    split. { unfold rep_instance in *. rewrite ENR, ES, EGQ. exact R2. }
    split. { unfold rep_thread in *. rewrite ETQ, ECI, EC. exact R3. }
    split. { intros c Hc. destruct (RD c) as (RMU & RAU & RFA & RFR). unfold rep_reginfo, rep_freearray in *. rewrite RMU, RAU, RFA, RFR. exact (R4 c Hc). }
    split. { rewrite ETQ. exact R5. } split. { rewrite EGQ. exact R6. }
    split. { unfold rep_secondary in *. rewrite ES. exact R7. }
    split. { unfold rep_headers in *. rewrite QR. exact R8. }
    split. { unfold rep_depot in *. rewrite ED. exact R9. }
    split. { unfold rep_fake in *. rewrite EH. exact R10. }
    split. { unfold rep_ialloc in *. rewrite EIA. exact R11. }
    split. { destruct R12 as (S1 & S2 & S3 & S4 & S5 & S6). (lazymatch goal with |- ?G => let G' := eval unfold rep_shadow in G in change_no_check G' end). rewrite QR, ES.
             split. { intros c g Hc. destruct (RD c) as (RMU & _). rewrite RMU. exact (S1 c g Hc). }
             split. { intros c g Hc. destruct (RD c) as (_ & _ & RFA & _). rewrite RFA. exact (S2 c g Hc). }
             split; [exact S3|]. split; [exact S4|].
             split. { intros c g Hc. destruct (RD c) as (RMU & _). rewrite RMU. exact (S5 c g Hc). }
             exact S6. }
    split; [exact L'|]. split; [exact B'|]. split; [exact R15|]. split; [exact R16|]. split; [exact R17|]. split; [exact R18|]. rewrite EGQ. exact R19.
  Qed.
End RegData.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Slot.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Variables (st : ast) (Lc FF : list (Z * Z)) (c : Z) (qt qg : Z).
  Hypothesis W : WFq bt st Lc FF qt qg.                                       (* [comment removed for export] *)
  Hypothesis Hc : 1 <= c <= 30.
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, T_PC, PC_SZ, T_QC, T_UNW, NMAX in *; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.

  #[local] Notation RB := (region_beg SBEG c).
  #[local] Notation MU := (r_mapped_user (a_reg st c)).

  (* [comment removed for export] *)
  Lemma uslot_span : forall i, uslot bt st c i ->
    SBEG <= RB /\ RB + MU <= i < RB + MU + KUSERMAP /\ RB + MU + KUSERMAP <= fa_beg SBEG c /\ fa_beg SBEG c + 2 ^ 29 <= SBEG + KSPACE
    /\ 0 <= MU /\ RB + 2 ^ 32 = fa_beg SBEG c + 2 ^ 29.
  Proof using Hc W qg qt FF Lc RUN.
    intros i Hi. unfold uslot in Hi. pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF.
    destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _).
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as (Y1 & Y2 & Y3 & _).
    unfold fa_beg, region_beg, KFAOFF, KREGION, KREGION_EXHAUST, KUSERMAP in *. repeat split; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma uslot_below : forall i, i < RB + MU -> uslot bt st c i -> False.
  Proof using. intros i Hi Hs. unfold uslot in Hs. lia. Qed.
  Lemma uslot_fa : forall i, fa_beg SBEG c <= i -> uslot bt st c i -> False.
  Proof using Hc W qg qt FF Lc RUN. intros i Hi Hs. destruct (uslot_span i Hs) as (_ & A & B & _). lia. Qed.
  Lemma region_stride : forall c0, region_beg SBEG c0 + 2 ^ 32 = region_beg SBEG (c0 + 1).
  Proof using. intros c0. (lazymatch goal with |- ?G => let G' := eval unfold region_beg, KREGION in G in change_no_check G' end). lia. Qed.
  Lemma uslot_other : forall c0 i, 1 <= c0 <= 30 -> c0 <> c -> region_beg SBEG c0 <= i < region_beg SBEG c0 + 2 ^ 32 -> uslot bt st c i -> False.
  Proof using Hc W qg qt FF Lc RUN.
    intros c0 i Hc0 NE Hi Hs. destruct (uslot_span i Hs) as (S1 & S2 & S3 & S4 & S5 & S6).
    unfold fa_beg, region_beg, KFAOFF, KREGION in *.
    destruct (Z.lt_trichotomy c0 c) as [LT|[EQ|GT]]; [| exact (NE EQ) |].
    - assert (HM : c0 * 2 ^ 32 + 2 ^ 32 <= c * 2 ^ 32) by (replace (c0 * 2 ^ 32 + 2 ^ 32) with ((c0 + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia).
      clear -Hi S2 S3 S5 S6 HM. lia.
    - assert (HM : c * 2 ^ 32 + 2 ^ 32 <= c0 * 2 ^ 32) by (replace (c * 2 ^ 32 + 2 ^ 32) with ((c + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia).
      clear -Hi S2 S3 S5 S6 HM. unfold KUSERMAP in *. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma uslot_in_space : forall i, uslot bt st c i -> SBEG <= i < SBEG + KSPACE /\ AS_HEAPLO <= i /\ i < CEIL /\ ~ in_band i /\ ~ (ia_img_lo IA <= i < ia_img_hi IA).
  Proof using Hc W qg qt FF Lc.
    intros i Hs. destruct (uslot_span i Hs) as (S1 & S2 & S3 & S4 & S5 & S6).
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & _ & _) & SP6 & SP7 & SP8 & SPH).
    pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X14 & X15 & X16).
    pose proof (img_lits bt st Lc FF W) as [I1 I2]. (lazymatch goal with |- ?G => let G' := eval unfold in_band in G in change_no_check G' end). ulia.
  Qed.

  (* [comment removed for export] *)
  Lemma uslot_vs_carved : forall c0 a i, 1 <= c0 <= 30 -> carved bt st c0 a -> a <= i < a + csize c0 -> uslot bt st c i -> False.
  Proof using Hc W qg qt FF Lc RUN.
    intros c0 a i Hc0 CV Hi Hs. destruct (carved_range bt st Lc FF W c0 a Hc0 CV) as (C1 & C2 & C3 & C4 & C5).
    pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _).
    destruct (Z.eq_dec c0 c) as [-> | NE].
    - exact (uslot_below i ltac:(lia) Hs).
    - apply (uslot_other c0 i Hc0 NE); [| exact Hs]. pose proof (region_stride c0). unfold fa_beg, region_beg, KFAOFF, KREGION in *. lia.
  Qed.

  Theorem uslot_not_supp : forall i, rep_supp bt st Lc FF i -> uslot bt st c i -> False.
  Proof using Hc W qg qt RUN.
    intros i Hsupp Hs. destruct (uslot_in_space i Hs) as (Z1 & Z2 & Z3 & Z4 & Z5). destruct (uslot_span i Hs) as (S1 & S2 & S3 & S4 & S5 & S6).
    pose proof W as ((WR1 & WR2) & WC & WQ & (SS1 & SS2 & SS3 & _) & WL & WK & WD & WM & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & G).
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    (* [comment removed for export] *)
    assert (FIXoff : forall lo hi, In (lo, hi) (bt_fixed bt) -> hi - lo < KSPACE -> lo <= i < hi -> False).
    { intros lo hi Hin Hlen Hi. destruct (space_vs_fixed bt st Lc FF W lo hi Hin Hlen); clear -H Hi Z1 S1 S2 S3 S4; ulia. }
    assert (DYNoff : forall lo hi, In (lo, hi) (dyn_ranges st) -> lo <= i < hi -> False).
    { intros lo hi Hin Hi. destruct (space_vs_dyn bt st Lc FF W lo hi Hin); clear -H Hi Z1 S1 S2 S3 S4; ulia. }
    assert (IMGoff : img_kind bt i -> False) by (intros [Hh _]; exact (Z5 Hh)).
    assert (BANDoff : forall lo, SB <= lo -> lo <= i -> i < AS_HEAPLO -> False) by (intros lo A B C0; clear -A B C0 Z4; unfold in_band in *; ulia).
    assert (REGINFOoff : SBEG + KSPACE <= i -> False) by (clear -Z1; lia).
    assert (FAoff : forall c0, 1 <= c0 <= 30 -> fa_beg SBEG c0 <= i < fa_beg SBEG c0 + 2 ^ 29 -> False).
    { intros c0 Hc0 Hi. destruct (Z.eq_dec c0 c) as [-> | NE]; [exact (uslot_fa i ltac:(lia) Hs)|].
      pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _).
      apply (uslot_other c0 i Hc0 NE); [| exact Hs]. pose proof (region_stride c0). unfold fa_beg, region_beg, KFAOFF, KREGION in *. lia. }
    assert (USERoff : forall c0, 1 <= c0 <= 30 -> region_beg SBEG c0 <= i < region_beg SBEG c0 + r_mapped_user (a_reg st c0) -> False).
    { intros c0 Hc0 Hi. destruct (Z.eq_dec c0 c) as [-> | NE]; [exact (uslot_below i ltac:(lia) Hs)|].
      pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _).
      apply (uslot_other c0 i Hc0 NE); [| exact Hs]. pose proof (region_stride c0). unfold fa_beg, region_beg, KFAOFF, KREGION in *. lia. }
    (* [comment removed for export] *)
    assert (BLKoff : forall p n, In (p, n) Lc \/ In (p - 16, n) (quar st) -> p - rz n <= i < p + rounded n -> False).
    { intros p n Hown Hi. pose proof (rz_range n) as RZ. pose proof (rounded_ge n) as (RG1 & RG2 & RG3 & RG4).
      assert (N1 : 1 <= n <= NMAX).
      { destruct Hown as [HL|HQ]; [destruct (live_range bt st Lc FF W p n HL); lia | destruct (quar_item_range bt st Lc FF W (p - 16) n HQ); lia]. }
      destruct (is_primary n) eqn:HP.
      - assert (K : carved bt st (blk_class n) (prim_alloc_beg p n) /\ 1 <= blk_class n <= 30 /\ p + n <= prim_alloc_beg p n + csize (blk_class n)).
        { destruct Hown as [HL|HQ].
          - pose proof (live_chunk bt st Lc FF W p n HL HP) as G'. cbn zeta in G'. destruct G' as (G1 & G2 & G3 & G4 & G5 & G6). repeat split; assumption || lia.
          - pose proof (quar_chunk bt st Lc FF W (p - 16) n HQ HP) as G'. cbn zeta in G'. replace (p - 16 + 16) with p in G' by lia.
            destruct G' as (G1 & G2 & G3 & G4 & G5 & G6). repeat split; assumption || lia. }
        destruct K as (K1 & K2 & K3). unfold prim_alloc_beg in *.
        pose proof (csize_class_of (needed n)) as CC. unfold blk_class in *.
        assert (NB : 1 <= needed n <= 65536) by (pose proof HP as HP2; unfold is_primary in HP2; apply Z.leb_le in HP2; unfold needed in *; lia).
        specialize (CC NB). assert (EN : needed n = rounded n + rz n) by reflexivity.
        apply (uslot_vs_carved (class_of (needed n)) (p - rz n) i K2 K1); [clear -Hi CC EN; lia | exact Hs].
      - assert (K : exists sc, In sc (a_sec st) /\ sc_user sc = p /\ sc_n sc = n).
        { destruct Hown as [HL|HQ]; [exact (live_sec bt st Lc FF W p n HL HP)|].
          destruct (quar_sec bt st Lc FF W (p - 16) n HQ HP) as (sc & A & B & C0). exists sc. repeat split; try assumption. lia. }
        destruct K as (sc & Hsc & Eu & En). destruct (sec_facts bt st Lc FF W sc Hsc) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
        apply (DYNoff _ _ (sec_dyn st sc Hsc)). subst p n. unfold sc_mapsz in *.
        pose proof (RoundUp_ge (sec_needed (sc_n sc)) PG ltac:((lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia)) as RU. unfold sec_map_size, sec_needed, sc_user, sec_user_off in *.
        clear -Hi A1 A2 RU RG1 RG2 RZ. ulia. }
    destruct Hsupp as [HC | HW].
    - (* [comment removed for export] *)
      unfold rep_cells in HC.
      destruct HC as [K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|K]]]]]]]]]]]]]].
      + exact (IMGoff (img_kinds bt st Lc FF W i (or_introl K))).
      + destruct (decide (bt_ptrarr bt <= i < bt_ptrarr bt + 8 * Z.of_nat (length (a_sec st)))) as [IN|NI].
        * apply (FIXoff _ _ IN8); [ulia | clear -IN SS1 SS3; lia].
        * exact (IMGoff (img_kinds bt st Lc FF W i ltac:(right; left; split; [exact K | exact NI]))).
      + unfold thread_cells, T_QC, T_PC, PC_SZ, T_UNW in K.
        destruct K as [K|[K|[K|[K|[K|[K|[K|K]]]]]]]; first [apply (FIXoff _ _ INT); [ulia | clear -K; ulia] | apply (FIXoff _ _ INC); [ulia | clear -K; lia]].
      + destruct K as (c0 & Hc0 & K). unfold foot_region in K.
        pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & _).
        destruct K as [[K _]|K]; [apply REGINFOoff; lia | apply (FAoff c0 Hc0); lia].
      + destruct K as (b & Hb & K). unfold foot_batch in K. destruct (batch_facts bt st Lc FF W b Hb) as (CVb & BL & B1 & B2).
        apply (uslot_vs_carved BATCHCLASS (ba_addr b) i ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) CVb); [| exact Hs]. change (csize BATCHCLASS) with 8192. unfold BATCHCAP in *. lia.
      + destruct K as (sc & Hs' & K). unfold foot_sec in K. destruct (sec_facts bt st Lc FF W sc Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
        apply (DYNoff _ _ (sec_dyn st sc Hs')). pose proof (sec_map_size_ge (sc_n sc) ltac:(lia)). unfold sc_mapsz in *. ulia.
      + destruct K as (p & n & Hown & K). unfold foot_hdr in K. pose proof (rz_range n). pose proof (rounded_ge n) as (RG1 & RG2 & _).
        apply (BLKoff p n Hown). lia.
      + exact (IMGoff (img_kinds bt st Lc FF W i ltac:(right; right; left; exact K))).
      + destruct K as (id & Hid & K). unfold foot_node in K. destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & A1 & A2 & A3).
        pose proof (node_addr_block bt st id Hid) as Hbk. set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
        destruct HIn as [Eb | Hnb]; [apply (FIXoff _ _ INN); [ulia | rewrite Eb; lia] | apply (DYNoff _ _ (node_dyn st bb Hnb)); lia].
      + unfold foot_fake_static in K. destruct K as [K|[K|[K|[K|K]]]].
        1-3: apply (FIXoff _ _ INFS); ulia.
        * exact (IMGoff (img_kinds bt st Lc FF W i ltac:(do 3 right; left; exact K))).
        * apply (FIXoff _ _ (dtls_member bt st Lc FF W)); ulia.
      + destruct K as (f & k & Hf & K). unfold foot_fword in K. destruct (fake_frame_facts bt st Lc FF W f k Hf) as (A1 & A2 & A3 & A4 & _).
        apply (FIXoff _ _ INFS); ulia.
      + exact (IMGoff (img_kinds bt st Lc FF W i ltac:(do 4 right; left; exact K))).
      + destruct K as (c0 & Hc0 & K). unfold foot_shreg, sh_lo in K. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF.
        destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _).
        destruct K as [[K _]|K]; (apply (BANDoff SB); [lia | clear -K Q1 Q2 Q8 X14; Zlia | clear -K Q1 Q2 Q5 Q6 Q8 X15; Zlia]).
      + destruct K as (sc & Hs' & K). unfold foot_shsec, sh_lo in K. destruct K as [K _]. destruct (sec_facts bt st Lc FF W sc Hs') as (A1 & A2 & _).
        apply (BANDoff SB); [lia | clear -K A1; Zlia | clear -K A2; Zlia].
      + exact (IMGoff (img_kinds bt st Lc FF W i ltac:(do 5 right; exact K))).
    - (* [comment removed for export] *)
      unfold rep_wr in HW.
      destruct HW as [K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|K]]]]]]]]]]]]].
      + apply (FIXoff _ _ IN8); [ulia | clear -K SS1 SS3; lia].
      + apply (FIXoff _ _ INT); ulia.
      + destruct K as (c0 & Hc0 & K). pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & _).
        destruct K as [K|[K|K]]; [apply REGINFOoff; lia | apply (FAoff c0 Hc0); lia | apply (USERoff c0 Hc0); lia].
      + destruct K as (b & Hb & K). destruct (batch_facts bt st Lc FF W b Hb) as (CVb & BL & B1 & B2).
        apply (uslot_vs_carved BATCHCLASS (ba_addr b) i ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) CVb); [| exact Hs]. change (csize BATCHCLASS) with 8192. unfold BATCHSZ in *. lia.
      + destruct K as (sc & Hs' & K). apply (DYNoff _ _ (sec_dyn st sc Hs')). exact K.
      + destruct K as (p & n & Hin & K). pose proof (rz_range n). pose proof (rounded_ge n) as (RG1 & RG2 & _).
        destruct K as [K|K]; [apply (BLKoff p n (or_introl Hin)); lia|].
        destruct (live_range bt st Lc FF W p n Hin) as (A1 & A2 & A3 & A4). unfold sh_lo, sh_hi in K.
        apply (BANDoff SB); [lia | clear -K A1; Zlia | clear -K A2; Zlia].
      + destruct K as (m & n & Hq & K). pose proof (rz_range n). pose proof (rounded_ge n) as (RG1 & RG2 & _).
        apply (BLKoff (m + 16) n); [right; replace (m + 16 - 16) with m by lia; exact Hq | lia].
      + destruct K as (b & Hb & K). destruct Hb as [Eb | Hnb]; [apply (FIXoff _ _ INN); [ulia | rewrite Eb; lia] | apply (DYNoff _ _ (node_dyn st b Hnb)); lia].
      + destruct K as (b & Hb & K). destruct Hb as [Eb | Hsb]; [apply (FIXoff _ _ INS); [ulia | rewrite Eb; lia] | apply (DYNoff _ _ (store_dyn st b Hsb)); lia].
      + apply (FIXoff _ _ INFS); ulia.
      + destruct K as (f & k & Hf & K). destruct (fake_frame_facts bt st Lc FF W f k Hf) as (A1 & A2 & A3 & A4 & _). unfold sh_lo, sh_hi in K.
        apply (BANDoff SB); [lia | clear -K A1 X5; Zlia | clear -K A2 X6; Zlia].
      + destruct K as (c0 & Hc0 & K). unfold sh_lo in K. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF.
        destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _). apply (BANDoff SB); [lia | clear -K Q1 X14; Zlia | clear -K Q1 Q2 Q5 X15; Zlia].
      + destruct K as (sc & Hs' & K). unfold sh_lo in K. destruct (sec_facts bt st Lc FF W sc Hs') as (A1 & A2 & _).
        apply (BANDoff SB); [lia | clear -K A1; Zlia | clear -K A2; Zlia].
      + unfold shmaps, AS_GAPLO, AS_GAPHI in K. apply (BANDoff AS_LO); ulia.
  Qed.
End Slot.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Uhole.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.

  Lemma committed_regdata : forall st st' a, st_regdata st st' -> committed bt st' a <-> committed bt st a.
  Proof using.
    intros st st' a EQ. destruct EQ as (RD & _ & _ & _ & _ & _ & _ & ENR & _). (lazymatch goal with |- ?G => let G' := eval unfold committed in G in change_no_check G' end). rewrite ENR.
    split.
    - intros [(c0 & Hc0 & X) | X]; [| right; exact X]. left. exists c0. destruct (RD c0) as (RMU & _ & RFA & _). rewrite RMU, RFA in X. exact (conj Hc0 X).
    - intros [(c0 & Hc0 & X) | X]; [| right; exact X]. left. exists c0. destruct (RD c0) as (RMU & _ & RFA & _). rewrite RMU, RFA. exact (conj Hc0 X).
  Qed.

  Lemma holes_uhole : forall st c a, 1 <= c <= 30 ->
    holes bt (op_uhole st c) a <-> holes bt st a \/ uslot bt st c a.
  Proof using.
    intros st c a Hc. (lazymatch goal with |- ?G => let G' := eval unfold holes, uslot in G in change_no_check G' end). split.
    - intros (c0 & Hc0 & X). destruct (uhole_flags st c c0) as [EU EF]. destruct (uhole_data st c c0) as (RMU & RAU & RFA & RFR).
      rewrite EU, EF, RMU, RFA in X. destruct (Z.eqb_spec c0 c) as [E | NE].
      + subst c0. destruct X as [[_ X] | X]; [right; exact X | left; exists c; split; [exact Hc | right; exact X]].
      + left. exists c0. exact (conj Hc0 X).
    - intros [(c0 & Hc0 & X) | X].
      + exists c0. destruct (uhole_flags st c c0) as [EU EF]. destruct (uhole_data st c c0) as (RMU & RAU & RFA & RFR).
        rewrite EU, EF, RMU, RFA. split; [exact Hc0|]. destruct (Z.eqb_spec c0 c) as [E | NE]; [| exact X].
        destruct X as [[_ X] | X]; [left; split; [reflexivity | exact X] | right; exact X].
      + exists c. destruct (uhole_flags st c c) as [EU EF]. destruct (uhole_data st c c) as (RMU & RAU & RFA & RFR).
        rewrite EU, EF, RMU, RFA, Z.eqb_refl. split; [exact Hc|]. left. split; [reflexivity | exact X].
  Qed.

  Theorem OPS_REP_uhole_pf : OPS_REP_uhole bt.
  Proof using.
    intros st Lc FF M M' mdl mdl' c W R Hc NH EX CH LD MI EAG.
    set (lo := region_beg SBEG c + r_mapped_user (a_reg st c)) in *.
    (* [comment removed for export] *)
    pose proof W as ((WR1 & WR2) & WC & WQ & WS & WL & WK & WD & WM & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & LZ0 & LZB & LRI & M06 & M0K & _) & G).
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & SP4 & SP5) & SP6 & SP7 & SP8 & SPH).
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14).
    destruct (WR1 c Hc) as (Y1 & Y2 & Y3 & _).
    assert (SLOT : SBEG <= lo /\ bt_resv6 bt <= lo /\ lo + KUSERMAP <= bt_resv6 bt + bt_resv6_len bt /\ lo + KUSERMAP <= SBEG + KSPACE /\ 0 <= lo /\ lo + KUSERMAP < 2 ^ 64).
    { subst lo. unfold fa_beg, region_beg, KFAOFF, KREGION, KREGION_EXHAUST, KUSERMAP in *. ulia. }
    destruct SLOT as (SL1 & SL2 & SL3 & SL4 & SL5 & SL6). assert (Elo : lo = lo) by reflexivity. unfold lo in Elo at 2. clearbody lo.
    (* [comment removed for export] *)
    assert (R' : Rep bt st Lc FF M' mdl).
    { apply (Rep_local bt st Lc FF M M' mdl W R). apply agree_at. intros a NE Hs.
      destruct (CH a NE) as [HU _]. exact (uslot_not_supp bt st Lc FF c _ _ W Hc (u a) Hs HU). }
    (* [comment removed for export] *)
    pose proof (st_regdata_uhole st c Hc) as EQ.
    apply (Rep_regdata_mem bt st (op_uhole st c) Lc FF M' mdl mdl' EQ R').
    - (* [comment removed for export] *)
      destruct R' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R13 & _).
      destruct R13 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12).
      destruct LD as (DM & DN & DL & DF & E1 & E2 & E3 & E4 & E5 & E6).
      assert (HOL : forall a, holes bt (op_uhole st c) a <-> holes bt st a \/ uslot bt st c a) by (intros a; exact (holes_uhole st c a Hc)).
      assert (COM : forall a, committed bt (op_uhole st c) a <-> committed bt st a) by (intros a; exact (committed_regdata st _ a EQ)).
      assert (USL : forall a, uslot bt st c a <-> lo <= a < lo + KUSERMAP) by (intros a; (lazymatch goal with |- ?G => let G' := eval unfold uslot in G in change_no_check G' end); subst lo; am_tauto).
      (lazymatch goal with |- ?G => let G' := eval unfold rep_ledger in G in change_no_check G' end). change (dyn_maps (op_uhole st c)) with (dyn_maps st). change (a_dep (op_uhole st c)) with (a_dep st).
      split. { destruct L1 as (F6 & PF & FOK & FPW & FH).
               assert (WF6 : ivs_wf F6).
               { intros q Hq. rewrite Forall_forall in FOK. destruct (FOK q Hq) as (A1 & A2 & A3 & _). (lazymatch goal with |- ?G => let G' := eval unfold iv_wf, BackingAlgebra.B, BackingAlgebra.S in G in change_no_check G' end).
                 clear -A1 A2 A3 SP3. ulia. }
               pose proof (frag_destroyed bt ltac:(clear -SP3; ulia) ltac:(clear -SP1; lia) F6 lo FOK (seps_of_split F6 FPW) WF6
                             ltac:(subst lo; apply user_slot_aligned; exact Y2) SL2 SL3) as FD.
               cbn zeta in FD. destruct FD as (FOK' & FSP' & FWF' & FCV').
               exists (maps_subtract F6 lo (lo + KUSERMAP)).
               split. { rewrite DM. eapply Permutation_trans; [apply maps_subtract_perm; exact PF|].
                        rewrite !maps_subtract_app.
                        rewrite (maps_subtract_id (bt_maps0 bt) lo (lo + KUSERMAP) ltac:((lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end); lia)).
                        2:{ pose proof M0K as M0. rewrite Forall_forall in M0 |- *. intros [b n] Hin. specialize (M0 _ Hin). cbn [fst snd] in M0 |- *.
                            (lazymatch goal with |- ?G => let G' := eval unfold off_range in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). split; [exact M0|].
                            (* [comment removed for export] *)
                            pose proof (M06 b n) as M6b. clear -M0 M6b Hin SL2 SL3.
                            destruct (Z.lt_ge_cases (u b) (bt_resv6 bt)) as [B1|B1].
                            - left. destruct (Z.le_gt_cases (u b + u n) (bt_resv6 bt)) as [B2|B2]; [clear M6b Hin; lia|].
                              exfalso. apply (M6b (bt_resv6 bt) Hin); clear M6b Hin; unfold KUSERMAP in *; lia.
                            - right. destruct (Z.lt_ge_cases (u b) (bt_resv6 bt + bt_resv6_len bt)) as [B2|B2]; [| clear M6b Hin; unfold KUSERMAP, KFAMAP in *; lia].
                              exfalso. apply (M6b (u b) Hin); clear M6b Hin; unfold KUSERMAP in *; lia. }
                        rewrite (maps_subtract_id (dyn_maps st) lo (lo + KUSERMAP) ltac:((lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end); lia)); [apply Permutation_refl|].
                        rewrite Forall_forall. intros [b n] Hin. (lazymatch goal with |- ?G => let G' := eval unfold off_range in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end).
                        unfold dyn_maps in Hin. rewrite !in_app_iff, !in_map_iff in Hin.
                        destruct Hin as [(sc & E & Hs) | [(bb & E & Hb) | (bb & E & Hb)]]; injection E as <- <-.
                        + destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _).
                          pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W IN6 (sec_dyn st sc Hs)) as D. hnf in D. cbn in D.
                          pose proof (sec_map_size_ge (sc_n sc) ltac:(lia)) as (MS1 & _). unfold sc_mapsz in *. rewrite !u64_lit by (first [clear - A7 A6 A5 A2 A1 | idtac]; ulia). (first [clear - D A7 A6 A5 SL3 SL1 R6a | idtac]; ulia).
                        + destruct (node_blocks_range bt st Lc FF W bb ltac:(right; exact Hb)) as (A1 & A2 & A3).
                          pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W IN6 (node_dyn st bb Hb)) as D. hnf in D. cbn in D. rewrite !u64_lit by ulia. ulia.
                        + destruct (store_blocks_range bt st Lc FF W bb ltac:(right; exact Hb)) as (A1 & A2 & A3).
                          pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W IN6 (store_dyn st bb Hb)) as D. hnf in D. cbn in D. rewrite !u64_lit by ulia. (first [clear - D SL3 SL1 R6a | idtac]; ulia). }
               split; [exact FOK'|]. split; [exact (split_of_seps _ FSP')|].
               intros a Ha. rewrite !in_ivz_covered, (FCV' a), (HOL a), (USL a). rewrite <- in_ivz_covered. rewrite (FH a Ha). am_tauto. }
      split. { intros a. rewrite DN, (in_ivz_maps_subtract (vm_noaccess (m_vmmaps mdl)) lo (lo + KUSERMAP) a SL5 ltac:((lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end); lia) SL6), (L2 a), (COM a), (HOL a), (USL a). am_tauto. }
      split. { intros a. rewrite (DL a), (L3 a), (COM a), (HOL a), (USL a).
               assert (STORE : forall b, In b (dp_storeblocks (a_dep st)) -> b <= a < b + 2 ^ 23 -> ~ (lo <= a < lo + KUSERMAP)).
               { intros b Hb Hab X. pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W IN6 (store_dyn st b Hb)) as D. hnf in D. cbn in D. clear -D Hab X SL2 SL3. unfold KUSERMAP in *. lia. }
               split.
               - intros [[(A & B & Cn) | (b & Hb & Hab)] N]; [left; am_tauto | right; exists b; exact (conj Hb Hab)].
               - intros [(A & B & Cn) | (b & Hb & Hab)]; [split; [left; am_tauto | am_tauto] | split; [right; exists b; exact (conj Hb Hab) | exact (STORE b Hb Hab)]]. }
      split; [exact DF|]. unfold alloc_top in L10 |- *. rewrite E1, E2, E3, E4, E5, E6. repeat (split; [assumption|]). rewrite DN. apply AsKSys6.ivs_pos_subtract. exact L12.
    - (* [comment removed for export] *)
      destruct R' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R14 & _).
      destruct R14 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). (lazymatch goal with |- ?G => let G' := eval unfold rep_budget in G in change_no_check G' end).
      change (a_aa (op_uhole st c)) with (a_aa st). change (a_sec (op_uhole st c)) with (a_sec st). change (a_dep (op_uhole st c)) with (a_dep st).
      change (a_shsec (op_uhole st c)) with (a_shsec st). change (a_nres (op_uhole st c)) with (a_nres st).
      split; [exact B1|]. split; [exact MI|]. split; [exact B3|]. split; [exact B4|].
      split. { intros c0 Hc0. destruct (uhole_data st c c0) as (RMU & RAU & RFA & RFR). rewrite RMU, RFA. exact (B5 c0 Hc0). }
      split; [exact B6|]. split; [exact B7|].
      assert (PC : prim_charge (op_uhole st c) = prim_charge st).
      { (lazymatch goal with |- ?G => let G' := eval unfold prim_charge in G in change_no_check G' end). apply sum_classes_ext. intros c0. destruct (uhole_data st c c0) as (RMU & RAU & RFA & RFR). rewrite RMU, RFA. reflexivity. }
      rewrite PC. change (sec_charge (op_uhole st c)) with (sec_charge st). change (depot_charge (op_uhole st c)) with (depot_charge st).
      (* [comment removed for export] *)
      destruct B8 as [B8 B9]. split; [clear -B8 EAG; lia | exact B9].
  Qed.
End Uhole.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Fslot.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Variables (st : ast) (Lc FF : list (Z * Z)) (c : Z) (qt qg : Z).
  Hypothesis W : WFq bt st Lc FF qt qg.                                       (* [comment removed for export] *)
  Hypothesis Hc : 1 <= c <= 30.
  Hypothesis FR : r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29.
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, T_PC, PC_SZ, T_QC, T_UNW, NMAX in *; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.

  #[local] Notation FB := (fa_beg SBEG c).
  #[local] Notation MF := (r_mapped_fa (a_reg st c)).

  Lemma fslot_span : forall i, fslot bt st c i ->
    SBEG <= region_beg SBEG c /\ region_beg SBEG c + r_mapped_user (a_reg st c) <= FB /\ FB + MF <= i < FB + MF + KFAMAP
    /\ FB + MF + KFAMAP <= FB + 2 ^ 29 /\ FB + 2 ^ 29 <= SBEG + KSPACE /\ 0 <= MF /\ region_beg SBEG c + 2 ^ 32 = FB + 2 ^ 29.
  Proof using FR Hc W qg qt FF Lc RUN.
    intros i Hi. unfold fslot in Hi. pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF.
    destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _).
    unfold fa_beg, region_beg, KFAOFF, KREGION, KFAMAP in *. repeat split; try lia.
  Qed.
  Lemma fslot_in_space : forall i, fslot bt st c i -> SBEG <= i < SBEG + KSPACE /\ AS_HEAPLO <= i /\ i < CEIL /\ ~ in_band i /\ ~ (ia_img_lo IA <= i < ia_img_hi IA).
  Proof using FR Hc W qg qt FF Lc.
    intros i Hs. destruct (fslot_span i Hs) as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & _ & _) & SP6 & SP7 & SP8 & SPH).
    pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X14 & X15 & X16).
    pose proof (img_lits bt st Lc FF W) as [I1 I2]. (lazymatch goal with |- ?G => let G' := eval unfold in_band in G in change_no_check G' end). ulia.
  Qed.
  (* [comment removed for export] *)
  Lemma fslot_below : forall i, i < FB + MF -> fslot bt st c i -> False.
  Proof using. intros i Hi Hs. unfold fslot in Hs. lia. Qed.
  Lemma fslot_other : forall c0 i, 1 <= c0 <= 30 -> c0 <> c -> region_beg SBEG c0 <= i < region_beg SBEG c0 + 2 ^ 32 -> fslot bt st c i -> False.
  Proof using FR Hc W qg qt FF Lc RUN.
    intros c0 i Hc0 NE Hi Hs. destruct (fslot_span i Hs) as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
    unfold fa_beg, region_beg, KFAOFF, KREGION in *.
    destruct (Z.lt_trichotomy c0 c) as [LT|[EQ|GT]]; [| exact (NE EQ) |].
    - assert (HM : c0 * 2 ^ 32 + 2 ^ 32 <= c * 2 ^ 32) by (replace (c0 * 2 ^ 32 + 2 ^ 32) with ((c0 + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia).
      clear -Hi S3 S6 HM. lia.
    - assert (HM : c * 2 ^ 32 + 2 ^ 32 <= c0 * 2 ^ 32) by (replace (c * 2 ^ 32 + 2 ^ 32) with ((c + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia).
      clear -Hi S3 S4 S6 HM. unfold KFAMAP in *. lia.
  Qed.
  Lemma fslot_vs_carved : forall c0 a i, 1 <= c0 <= 30 -> carved bt st c0 a -> a <= i < a + csize c0 -> fslot bt st c i -> False.
  Proof using FR Hc W qg qt FF Lc RUN.
    intros c0 a i Hc0 CV Hi Hs. destruct (carved_range bt st Lc FF W c0 a Hc0 CV) as (C1 & C2 & C3 & C4 & C5).
    pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _).
    destruct (Z.eq_dec c0 c) as [-> | NE].
    - destruct (fslot_span i Hs) as (S1 & S2 & S3 & _). exact (fslot_below i ltac:(lia) Hs).
    - apply (fslot_other c0 i Hc0 NE); [| exact Hs]. unfold fa_beg, region_beg, KFAOFF, KREGION in *. lia.
  Qed.

  Theorem fslot_not_supp : forall i, rep_supp bt st Lc FF i -> fslot bt st c i -> False.
  Proof using FR Hc W qg qt RUN.
    intros i Hsupp Hs. destruct (fslot_in_space i Hs) as (Z1 & Z2 & Z3 & Z4 & Z5). destruct (fslot_span i Hs) as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
    pose proof W as ((WR1 & WR2) & WC & WQ & (SS1 & SS2 & SS3 & _) & WL & WK & WD & WM & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & G).
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    assert (FIXoff : forall lo hi, In (lo, hi) (bt_fixed bt) -> hi - lo < KSPACE -> lo <= i < hi -> False).
    { intros lo hi Hin Hlen Hi. destruct (space_vs_fixed bt st Lc FF W lo hi Hin Hlen); clear -H Hi Z1 S3 S4 S5; ulia. }
    assert (DYNoff : forall lo hi, In (lo, hi) (dyn_ranges st) -> lo <= i < hi -> False).
    { intros lo hi Hin Hi. destruct (space_vs_dyn bt st Lc FF W lo hi Hin); clear -H Hi Z1 S3 S4 S5; ulia. }
    assert (IMGoff : img_kind bt i -> False) by (intros [Hh _]; exact (Z5 Hh)).
    assert (BANDoff : forall lo, SB <= lo -> lo <= i -> i < AS_HEAPLO -> False) by (intros lo A B C0; clear -A B C0 Z4; unfold in_band in *; ulia).
    assert (REGINFOoff : SBEG + KSPACE <= i -> False) by (clear -Z1; lia).
    assert (FAoff : forall c0, 1 <= c0 <= 30 -> fa_beg SBEG c0 <= i < fa_beg SBEG c0 + r_mapped_fa (a_reg st c0) -> False).
    { intros c0 Hc0 Hi. destruct (Z.eq_dec c0 c) as [-> | NE]; [exact (fslot_below i ltac:(lia) Hs)|].
      pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _).
      apply (fslot_other c0 i Hc0 NE); [| exact Hs]. unfold fa_beg, region_beg, KFAOFF, KREGION in *. lia. }
    assert (USERoff : forall c0, 1 <= c0 <= 30 -> region_beg SBEG c0 <= i < region_beg SBEG c0 + r_mapped_user (a_reg st c0) -> False).
    { intros c0 Hc0 Hi. destruct (Z.eq_dec c0 c) as [-> | NE]; [exact (fslot_below i ltac:(lia) Hs)|].
      pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _).
      apply (fslot_other c0 i Hc0 NE); [| exact Hs]. unfold fa_beg, region_beg, KFAOFF, KREGION in *. lia. }
    assert (BLKoff : forall p n, In (p, n) Lc \/ In (p - 16, n) (quar st) -> p - rz n <= i < p + rounded n -> False).
    { intros p n Hown Hi. pose proof (rz_range n) as RZ. pose proof (rounded_ge n) as (RG1 & RG2 & RG3 & RG4).
      assert (N1 : 1 <= n <= NMAX).
      { destruct Hown as [HL|HQ]; [destruct (live_range bt st Lc FF W p n HL); lia | destruct (quar_item_range bt st Lc FF W (p - 16) n HQ); lia]. }
      destruct (is_primary n) eqn:HP.
      - assert (K : carved bt st (blk_class n) (prim_alloc_beg p n) /\ 1 <= blk_class n <= 30 /\ p + n <= prim_alloc_beg p n + csize (blk_class n)).
        { destruct Hown as [HL|HQ].
          - pose proof (live_chunk bt st Lc FF W p n HL HP) as G'. cbn zeta in G'. destruct G' as (G1 & G2 & G3 & G4 & G5 & G6). repeat split; assumption || lia.
          - pose proof (quar_chunk bt st Lc FF W (p - 16) n HQ HP) as G'. cbn zeta in G'. replace (p - 16 + 16) with p in G' by lia.
            destruct G' as (G1 & G2 & G3 & G4 & G5 & G6). repeat split; assumption || lia. }
        destruct K as (K1 & K2 & K3). unfold prim_alloc_beg in *.
        pose proof (csize_class_of (needed n)) as CC. unfold blk_class in *.
        assert (NB : 1 <= needed n <= 65536) by (pose proof HP as HP2; unfold is_primary in HP2; apply Z.leb_le in HP2; unfold needed in *; lia).
        specialize (CC NB). assert (EN : needed n = rounded n + rz n) by reflexivity.
        apply (fslot_vs_carved (class_of (needed n)) (p - rz n) i K2 K1); [clear -Hi CC EN; lia | exact Hs].
      - assert (K : exists sc, In sc (a_sec st) /\ sc_user sc = p /\ sc_n sc = n).
        { destruct Hown as [HL|HQ]; [exact (live_sec bt st Lc FF W p n HL HP)|].
          destruct (quar_sec bt st Lc FF W (p - 16) n HQ HP) as (sc & A & B & C0). exists sc. repeat split; try assumption. lia. }
        destruct K as (sc & Hsc & Eu & En). destruct (sec_facts bt st Lc FF W sc Hsc) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
        apply (DYNoff _ _ (sec_dyn st sc Hsc)). subst p n. unfold sc_mapsz in *.
        pose proof (RoundUp_ge (sec_needed (sc_n sc)) PG ltac:((lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia)) as RU. unfold sec_map_size, sec_needed, sc_user, sec_user_off in *.
        clear -Hi A1 A2 RU RG1 RG2 RZ. ulia. }
    destruct Hsupp as [HC | HW].
    - unfold rep_cells in HC.
      destruct HC as [K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|K]]]]]]]]]]]]]].
      + exact (IMGoff (img_kinds bt st Lc FF W i (or_introl K))).
      + destruct (decide (bt_ptrarr bt <= i < bt_ptrarr bt + 8 * Z.of_nat (length (a_sec st)))) as [IN|NI].
        * apply (FIXoff _ _ IN8); [ulia | clear -IN SS1 SS3; lia].
        * exact (IMGoff (img_kinds bt st Lc FF W i ltac:(right; left; split; [exact K | exact NI]))).
      + unfold thread_cells, T_QC, T_PC, PC_SZ, T_UNW in K.
        destruct K as [K|[K|[K|[K|[K|[K|[K|K]]]]]]]; first [apply (FIXoff _ _ INT); [ulia | clear -K; ulia] | apply (FIXoff _ _ INC); [ulia | clear -K; lia]].
      + destruct K as (c0 & Hc0 & K). unfold foot_region in K.
        pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & _).
        destruct K as [[K _]|K]; [apply REGINFOoff; lia | apply (FAoff c0 Hc0); lia].
      + destruct K as (b & Hb & K). unfold foot_batch in K. destruct (batch_facts bt st Lc FF W b Hb) as (CVb & BL & B1 & B2).
        apply (fslot_vs_carved BATCHCLASS (ba_addr b) i ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) CVb); [| exact Hs]. change (csize BATCHCLASS) with 8192. unfold BATCHCAP in *. lia.
      + destruct K as (sc & Hs' & K). unfold foot_sec in K. destruct (sec_facts bt st Lc FF W sc Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
        apply (DYNoff _ _ (sec_dyn st sc Hs')). pose proof (sec_map_size_ge (sc_n sc) ltac:(lia)). unfold sc_mapsz in *. ulia.
      + destruct K as (p & n & Hown & K). unfold foot_hdr in K. pose proof (rz_range n). pose proof (rounded_ge n) as (RG1 & RG2 & _).
        apply (BLKoff p n Hown). lia.
      + exact (IMGoff (img_kinds bt st Lc FF W i ltac:(right; right; left; exact K))).
      + destruct K as (id & Hid & K). unfold foot_node in K. destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & A1 & A2 & A3).
        pose proof (node_addr_block bt st id Hid) as Hbk. set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
        destruct HIn as [Eb | Hnb]; [apply (FIXoff _ _ INN); [ulia | rewrite Eb; lia] | apply (DYNoff _ _ (node_dyn st bb Hnb)); lia].
      + unfold foot_fake_static in K. destruct K as [K|[K|[K|[K|K]]]].
        1-3: apply (FIXoff _ _ INFS); ulia.
        * exact (IMGoff (img_kinds bt st Lc FF W i ltac:(do 3 right; left; exact K))).
        * apply (FIXoff _ _ (dtls_member bt st Lc FF W)); ulia.
      + destruct K as (f & k & Hf & K). unfold foot_fword in K. destruct (fake_frame_facts bt st Lc FF W f k Hf) as (A1 & A2 & A3 & A4 & _).
        apply (FIXoff _ _ INFS); ulia.
      + exact (IMGoff (img_kinds bt st Lc FF W i ltac:(do 4 right; left; exact K))).
      + destruct K as (c0 & Hc0 & K). unfold foot_shreg, sh_lo in K. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF.
        destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _).
        destruct K as [[K _]|K]; (apply (BANDoff SB); [lia | clear -K Q1 Q2 Q8 X14; Zlia | clear -K Q1 Q2 Q5 Q6 Q8 X15; Zlia]).
      + destruct K as (sc & Hs' & K). unfold foot_shsec, sh_lo in K. destruct K as [K _]. destruct (sec_facts bt st Lc FF W sc Hs') as (A1 & A2 & _).
        apply (BANDoff SB); [lia | clear -K A1; Zlia | clear -K A2; Zlia].
      + exact (IMGoff (img_kinds bt st Lc FF W i ltac:(do 5 right; exact K))).
    - unfold rep_wr in HW.
      destruct HW as [K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|K]]]]]]]]]]]]].
      + apply (FIXoff _ _ IN8); [ulia | clear -K SS1 SS3; lia].
      + apply (FIXoff _ _ INT); ulia.
      + destruct K as (c0 & Hc0 & K). pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & _).
        destruct K as [K|[K|K]]; [apply REGINFOoff; lia | apply (FAoff c0 Hc0); lia | apply (USERoff c0 Hc0); lia].
      + destruct K as (b & Hb & K). destruct (batch_facts bt st Lc FF W b Hb) as (CVb & BL & B1 & B2).
        apply (fslot_vs_carved BATCHCLASS (ba_addr b) i ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) CVb); [| exact Hs]. change (csize BATCHCLASS) with 8192. unfold BATCHSZ in *. lia.
      + destruct K as (sc & Hs' & K). apply (DYNoff _ _ (sec_dyn st sc Hs')). exact K.
      + destruct K as (p & n & Hin & K). pose proof (rz_range n). pose proof (rounded_ge n) as (RG1 & RG2 & _).
        destruct K as [K|K]; [apply (BLKoff p n (or_introl Hin)); lia|].
        destruct (live_range bt st Lc FF W p n Hin) as (A1 & A2 & A3 & A4). unfold sh_lo, sh_hi in K.
        apply (BANDoff SB); [lia | clear -K A1; Zlia | clear -K A2; Zlia].
      + destruct K as (m & n & Hq & K). pose proof (rz_range n). pose proof (rounded_ge n) as (RG1 & RG2 & _).
        apply (BLKoff (m + 16) n); [right; replace (m + 16 - 16) with m by lia; exact Hq | lia].
      + destruct K as (b & Hb & K). destruct Hb as [Eb | Hnb]; [apply (FIXoff _ _ INN); [ulia | rewrite Eb; lia] | apply (DYNoff _ _ (node_dyn st b Hnb)); lia].
      + destruct K as (b & Hb & K). destruct Hb as [Eb | Hsb]; [apply (FIXoff _ _ INS); [ulia | rewrite Eb; lia] | apply (DYNoff _ _ (store_dyn st b Hsb)); lia].
      + apply (FIXoff _ _ INFS); ulia.
      + destruct K as (f & k & Hf & K). destruct (fake_frame_facts bt st Lc FF W f k Hf) as (A1 & A2 & A3 & A4 & _). unfold sh_lo, sh_hi in K.
        apply (BANDoff SB); [lia | clear -K A1 X5; Zlia | clear -K A2 X6; Zlia].
      + destruct K as (c0 & Hc0 & K). unfold sh_lo in K. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF.
        destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _). apply (BANDoff SB); [lia | clear -K Q1 X14; Zlia | clear -K Q1 Q2 Q5 X15; Zlia].
      + destruct K as (sc & Hs' & K). unfold sh_lo in K. destruct (sec_facts bt st Lc FF W sc Hs') as (A1 & A2 & _).
        apply (BANDoff SB); [lia | clear -K A1; Zlia | clear -K A2; Zlia].
      + unfold shmaps, AS_GAPLO, AS_GAPHI in K. apply (BANDoff AS_LO); ulia.
  Qed.
End Fslot.

Section Fhole.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.

  Lemma holes_fhole : forall st c a, 1 <= c <= 30 ->
    holes bt (op_fhole st c) a <-> holes bt st a \/ fslot bt st c a.
  Proof using.
    intros st c a Hc. (lazymatch goal with |- ?G => let G' := eval unfold holes, fslot in G in change_no_check G' end). split.
    - intros (c0 & Hc0 & X). destruct (fhole_flags st c c0) as [EF EU]. destruct (fhole_data st c c0) as (RMU & RAU & RFA & RFR).
      rewrite EU, EF, RMU, RFA in X. destruct (Z.eqb_spec c0 c) as [E | NE].
      + subst c0. destruct X as [X | [_ X]]; [left; exists c; split; [exact Hc | left; exact X] | right; exact X].
      + left. exists c0. exact (conj Hc0 X).
    - intros [(c0 & Hc0 & X) | X].
      + exists c0. destruct (fhole_flags st c c0) as [EF EU]. destruct (fhole_data st c c0) as (RMU & RAU & RFA & RFR).
        rewrite EU, EF, RMU, RFA. split; [exact Hc0|]. destruct (Z.eqb_spec c0 c) as [E | NE]; [| exact X].
        destruct X as [X | [_ X]]; [left; exact X | right; split; [reflexivity | exact X]].
      + exists c. destruct (fhole_flags st c c) as [EF EU]. destruct (fhole_data st c c) as (RMU & RAU & RFA & RFR).
        rewrite EU, EF, RMU, RFA, Z.eqb_refl. split; [exact Hc|]. right. split; [reflexivity | exact X].
  Qed.

  Theorem OPS_REP_fhole_pf : OPS_REP_fhole bt.
  Proof using.
    intros st Lc FF M M' mdl mdl' c W R Hc NH FR CH LD MI EAG.
    set (lo := fa_beg SBEG c + r_mapped_fa (a_reg st c)) in *.
    pose proof W as ((WR1 & WR2) & WC & WQ & WS & WL & WK & WD & WM & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & LZ0 & LZB & LRI & M06 & M0K & _) & G).
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & SP4 & SP5) & SP6 & SP7 & SP8 & SPH).
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14).
    destruct (WR1 c Hc) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & _).
    assert (SLOT : SBEG <= lo /\ bt_resv6 bt <= lo /\ lo + KFAMAP <= bt_resv6 bt + bt_resv6_len bt /\ lo + KFAMAP <= SBEG + KSPACE /\ 0 <= lo /\ lo + KFAMAP < 2 ^ 64).
    { subst lo. unfold KFAMAP in *. (first [clear - Q6 Q5 Q4 Q3 Q2 Q1 SP3 SP1 R6b R6a FR | idtac]; ulia). }
    destruct SLOT as (SL1 & SL2 & SL3 & SL4 & SL5 & SL6). assert (Elo : lo = lo) by reflexivity. unfold lo in Elo at 2. clearbody lo.
    assert (R' : Rep bt st Lc FF M' mdl).
    { apply (Rep_local bt st Lc FF M M' mdl W R). apply agree_at. intros a NE Hs.
      destruct (CH a NE) as [HU _]. exact (fslot_not_supp bt st Lc FF c _ _ W Hc FR (u a) Hs HU). }
    pose proof (st_regdata_fhole st c Hc) as EQ.
    apply (Rep_regdata_mem bt st (op_fhole st c) Lc FF M' mdl mdl' EQ R').
    - destruct R' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R13 & _).
      destruct R13 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12).
      destruct LD as (DM & DN & DL & DF & E1 & E2 & E3 & E4 & E5 & E6).
      assert (HOL : forall a, holes bt (op_fhole st c) a <-> holes bt st a \/ fslot bt st c a) by (intros a; exact (holes_fhole st c a Hc)).
      assert (COM : forall a, committed bt (op_fhole st c) a <-> committed bt st a) by (intros a; exact (committed_regdata bt st _ a EQ)).
      assert (USL : forall a, fslot bt st c a <-> lo <= a < lo + KFAMAP) by (intros a; (lazymatch goal with |- ?G => let G' := eval unfold fslot in G in change_no_check G' end); subst lo; am_tauto).
      (lazymatch goal with |- ?G => let G' := eval unfold rep_ledger in G in change_no_check G' end). change (dyn_maps (op_fhole st c)) with (dyn_maps st). change (a_dep (op_fhole st c)) with (a_dep st).
      split. { destruct L1 as (F6 & PF & FOK & FPW & FH).
               assert (WF6 : ivs_wf F6).
               { intros q Hq. rewrite Forall_forall in FOK. destruct (FOK q Hq) as (A1 & A2 & A3 & _). (lazymatch goal with |- ?G => let G' := eval unfold iv_wf, BackingAlgebra.B, BackingAlgebra.S in G in change_no_check G' end).
                 clear -A1 A2 A3 SP3. ulia. }
               pose proof (frag_destroyed bt ltac:(clear -SP3; ulia) ltac:(clear -SP1; lia) F6 lo FOK (seps_of_split F6 FPW) WF6
                             ltac:(subst lo; apply fa_slot_aligned; exact Y6) SL2 ltac:((lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end); unfold KFAMAP in SL3; exact SL3)) as FD.
               cbn zeta in FD. destruct FD as (FOK' & FSP' & FWF' & FCV').
               exists (maps_subtract F6 lo (lo + KUSERMAP)).
               assert (EK : KUSERMAP = KFAMAP) by reflexivity.
               split. { rewrite DM, <- EK. eapply Permutation_trans; [apply maps_subtract_perm; exact PF|].
                        rewrite !maps_subtract_app.
                        rewrite (maps_subtract_id (bt_maps0 bt) lo (lo + KUSERMAP) ltac:((lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end); lia)).
                        2:{ pose proof M0K as M0. rewrite Forall_forall in M0 |- *. intros [b n] Hin. specialize (M0 _ Hin). cbn [fst snd] in M0 |- *.
                            (lazymatch goal with |- ?G => let G' := eval unfold off_range in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). split; [exact M0|]. rewrite EK.
                            pose proof (M06 b n) as M6b. clear -M0 M6b Hin SL2 SL3.
                            destruct (Z.lt_ge_cases (u b) (bt_resv6 bt)) as [B1|B1].
                            - left. destruct (Z.le_gt_cases (u b + u n) (bt_resv6 bt)) as [B2|B2]; [clear M6b Hin; lia|].
                              exfalso. apply (M6b (bt_resv6 bt) Hin); clear M6b Hin; unfold KUSERMAP, KFAMAP in *; lia.
                            - right. destruct (Z.lt_ge_cases (u b) (bt_resv6 bt + bt_resv6_len bt)) as [B2|B2]; [| clear M6b Hin; unfold KUSERMAP, KFAMAP in *; lia].
                              exfalso. apply (M6b (u b) Hin); clear M6b Hin; unfold KUSERMAP, KFAMAP in *; lia. }
                        rewrite (maps_subtract_id (dyn_maps st) lo (lo + KUSERMAP) ltac:((lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end); lia)); [apply Permutation_refl|].
                        rewrite Forall_forall. intros [b n] Hin. (lazymatch goal with |- ?G => let G' := eval unfold off_range in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). rewrite EK.
                        unfold dyn_maps in Hin. rewrite !in_app_iff, !in_map_iff in Hin.
                        destruct Hin as [(sc & E & Hs) | [(bb & E & Hb) | (bb & E & Hb)]]; injection E as <- <-.
                        + destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _).
                          pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W IN6 (sec_dyn st sc Hs)) as D. hnf in D. cbn in D.
                          pose proof (sec_map_size_ge (sc_n sc) ltac:(lia)) as (MS1 & _). unfold sc_mapsz in *. rewrite !u64_lit by (first [clear - A7 A6 A5 A2 A1 | idtac]; ulia). unfold KFAMAP in *. (first [clear - D A7 A6 A5 SL3 SL1 R6a | idtac]; ulia).
                        + destruct (node_blocks_range bt st Lc FF W bb ltac:(right; exact Hb)) as (A1 & A2 & A3).
                          pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W IN6 (node_dyn st bb Hb)) as D. hnf in D. cbn in D. rewrite !u64_lit by (first [clear - A2 A1 | idtac]; ulia). unfold KFAMAP in *. (first [clear - D SL3 SL1 R6a | idtac]; ulia).
                        + destruct (store_blocks_range bt st Lc FF W bb ltac:(right; exact Hb)) as (A1 & A2 & A3).
                          pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W IN6 (store_dyn st bb Hb)) as D. hnf in D. cbn in D. rewrite !u64_lit by (first [clear - A2 A1 | idtac]; ulia). unfold KFAMAP in *. (first [clear - D SL3 SL1 R6a | idtac]; ulia). }
               split; [exact FOK'|]. split; [exact (split_of_seps _ FSP')|].
               intros a Ha. rewrite !in_ivz_covered, (FCV' a), (HOL a), (USL a), <- EK. rewrite <- in_ivz_covered. rewrite (FH a Ha). am_tauto. }
      split. { intros a. rewrite DN, (in_ivz_maps_subtract (vm_noaccess (m_vmmaps mdl)) lo (lo + KFAMAP) a SL5 ltac:((lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end); lia) SL6), (L2 a), (COM a), (HOL a), (USL a). am_tauto. }
      split. { intros a. rewrite (DL a), (L3 a), (COM a), (HOL a), (USL a).
               assert (STORE : forall b, In b (dp_storeblocks (a_dep st)) -> b <= a < b + 2 ^ 23 -> ~ (lo <= a < lo + KFAMAP)).
               { intros b Hb Hab X. pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W IN6 (store_dyn st b Hb)) as D. hnf in D. cbn in D. clear -D Hab X SL2 SL3. unfold KFAMAP in *. lia. }
               split.
               - intros [[(A & B & Cn) | (b & Hb & Hab)] N]; [left; am_tauto | right; exists b; exact (conj Hb Hab)].
               - intros [(A & B & Cn) | (b & Hb & Hab)]; [split; [left; am_tauto | am_tauto] | split; [right; exists b; exact (conj Hb Hab) | exact (STORE b Hb Hab)]]. }
      split; [exact DF|]. unfold alloc_top in L10 |- *. rewrite E1, E2, E3, E4, E5, E6. repeat (split; [assumption|]). rewrite DN. apply AsKSys6.ivs_pos_subtract. exact L12.
    - destruct R' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R14 & _).
      destruct R14 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). (lazymatch goal with |- ?G => let G' := eval unfold rep_budget in G in change_no_check G' end).
      change (a_aa (op_fhole st c)) with (a_aa st). change (a_sec (op_fhole st c)) with (a_sec st). change (a_dep (op_fhole st c)) with (a_dep st).
      change (a_shsec (op_fhole st c)) with (a_shsec st). change (a_nres (op_fhole st c)) with (a_nres st).
      split; [exact B1|]. split; [exact MI|]. split; [exact B3|]. split; [exact B4|].
      split. { intros c0 Hc0. destruct (fhole_data st c c0) as (RMU & RAU & RFA & RFR). rewrite RMU, RFA. exact (B5 c0 Hc0). }
      split; [exact B6|]. split; [exact B7|].
      assert (PC : prim_charge (op_fhole st c) = prim_charge st).
      { (lazymatch goal with |- ?G => let G' := eval unfold prim_charge in G in change_no_check G' end). apply sum_classes_ext. intros c0. destruct (fhole_data st c c0) as (RMU & RAU & RFA & RFR). rewrite RMU, RFA. reflexivity. }
      rewrite PC. change (sec_charge (op_fhole st c)) with (sec_charge st). change (depot_charge (op_fhole st c)) with (depot_charge st).
      (* [comment removed for export] *)
      destruct B8 as [B8 B9]. split; [clear -B8 EAG; lia | exact B9].
  Qed.
End Fhole.
