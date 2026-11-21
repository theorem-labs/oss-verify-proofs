(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import OverlayIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeB1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeB2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeB3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeB5.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeO1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeO2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section GTree.
Variable t : tree_id.
Variable FC2 : arr.
Variable DL2 : arr.
Variable L : Z.
Variable mc : Z.
Variable FCf : arr.
Variable DLf : arr.
Variable HPf : arr.
Variable DPf : arr.
Variable Wg : Z -> Z.
Local Notation E := (sd_elems t).
Hypothesis HR : heap_result t FC2 DL2 L mc FCf DLf HPf DPf.
Hypothesis GF : greedy_facts t FC2 L FCf HPf Wg.

(* [comment removed for export] *)
Definition gtree_of : gtree :=
  {| g_lo := HM L; g_hi := 572; g_par := par t L HPf; g_leaf := leafb t HPf; g_code := nd HPf;
     g_wt := fun i => Wg (nd HPf i); g_ext := fun i => 572 - i |}.

Let RHM : 2 <= HM L <= 570 := HM_range t FC2 DL2 L mc FCf DLf HPf DPf HR.
Let RL : 2 <= L <= E := hr_L _ _ _ _ _ _ _ _ _ HR.
Let RE : 19 <= E <= 286 := proj1 (elems_range t).

(* [comment removed for export] *)
Lemma round_of : forall i, HM L < i < 573 ->
  let k := (572 - i) / 2 + 1 in 1 <= k <= L - 1 /\ (i = 574 - 2 * k \/ i = 573 - 2 * k) /\ dadid t i = E + k - 1.
Proof. intros i Hi. unfold dadid, RefDeflSafeB3.HM in *. cbv zeta. Z.to_euclidean_division_equations; lia. Qed.

(* [comment removed for export] *)
Lemma children_of_round : forall k c, 1 <= k <= L - 1 -> HM L < c < 573 ->
  (par t L HPf c = posof L HPf (E + k - 1) <-> (c = 574 - 2 * k \/ c = 573 - 2 * k)).
Proof.
  intros k c Hk Hc.
  destruct (hr_cov _ _ _ _ _ _ _ _ _ HR (E + k - 1) ltac:(unfold Vj; right; lia)) as (p & Hp & Ep).
  assert (Pp : posof L HPf (E + k - 1) = p) by (rewrite <- Ep; apply (posof_nd _ _ _ _ _ _ _ _ _ HR); unfold tail, RefDeflSafeB3.HM in *; lia).
  rewrite Pp. rewrite (children_internal _ _ _ _ _ _ _ _ _ HR p c) by (unfold tail, nd, RefDeflSafeB3.HM in *; try lia; rewrite Ep; lia).
  unfold nd. rewrite Ep. lia.
Qed.

Theorem gtree_of_ok : gtree_ok gtree_of.
Proof.
  pose proof GF as [WL WF WN ND NM MIN].
  assert (TAILV : forall i, HM L <= i < 573 -> (0 <= nd HPf i < E /\ arr_get FC2 (nd HPf i) <> 0) \/ (E <= nd HPf i < E + L - 1)).
  { intros i Hi. exact (nd_cases _ _ _ _ _ _ _ _ _ HR i ltac:(unfold tail; lia)). }
  constructor; cbn [g_lo g_hi g_par g_leaf g_code g_wt g_ext gtree_of]; unfold g_pos; cbn [g_lo g_hi gtree_of].
  - lia.
  - intros i Hi. destruct (par_spec _ _ _ _ _ _ _ _ _ HR i ltac:(lia)) as (A & B & _). unfold tail in A. lia.
  - intros i Hi. destruct (par_spec _ _ _ _ _ _ _ _ _ HR i ltac:(lia)) as (_ & _ & _ & D). unfold leafb. apply Z.ltb_ge. exact D.
  - intros p Hp Hl. unfold leafb in Hl. apply Z.ltb_ge in Hl.
    assert (Rnd : E <= nd HPf p < E + L - 1).
    { destruct (Z.eq_dec p (HM L)) as [->|Np].
      - unfold nd, RefDeflSafeB3.HM. rewrite (hr_root _ _ _ _ _ _ _ _ _ HR). lia.
      - destruct (TAILV p ltac:(lia)) as [[A _]|A]; lia. }
    set (k := nd HPf p - E + 1).
    assert (Pp : posof L HPf (E + k - 1) = p) by (subst k; replace (E + (nd HPf p - E + 1) - 1) with (nd HPf p) by lia; apply (posof_nd _ _ _ _ _ _ _ _ _ HR); unfold tail; lia).
    exists (574 - 2 * k), (573 - 2 * k). unfold RefDeflSafeB3.HM in *.
    split; [lia|]. split; [lia|]. split; [lia|].
    split; [rewrite <- Pp; apply (proj2 (children_of_round k (574 - 2 * k) ltac:(lia) ltac:(unfold RefDeflSafeB3.HM; lia))); left; reflexivity|].
    split; [rewrite <- Pp; apply (proj2 (children_of_round k (573 - 2 * k) ltac:(lia) ltac:(unfold RefDeflSafeB3.HM; lia))); right; reflexivity|].
    intros c Hc Pc. rewrite <- Pp in Pc. exact (proj1 (children_of_round k c ltac:(lia) ltac:(unfold RefDeflSafeB3.HM; lia)) Pc).
  - intros i Hi Hl. unfold leafb in Hl. apply Z.ltb_lt in Hl.
    assert (NZ : arr_get FC2 (nd HPf i) <> 0).
    { destruct (Z.eq_dec i (HM L)) as [->|Ni]; [unfold nd, RefDeflSafeB3.HM in Hl; rewrite (hr_root _ _ _ _ _ _ _ _ _ HR) in Hl; lia|].
      destruct (TAILV i ltac:(lia)) as [[_ A]|A]; [exact A | lia]. }
    pose proof (nd_cases _ _ _ _ _ _ _ _ _ HR i ltac:(unfold tail; lia)).
    rewrite (WL (nd HPf i)) by (unfold nd in *; lia). pose proof (WN (nd HPf i)) as X. rewrite (WL (nd HPf i)) in X by (unfold nd in *; lia). lia.
  - intros p a b Hp Hl Ha Hb Nab Pa Pb. unfold leafb in Hl. apply Z.ltb_ge in Hl.
    assert (Rnd : E <= nd HPf p < E + L - 1).
    { destruct (Z.eq_dec p (HM L)) as [->|Np].
      - unfold nd, RefDeflSafeB3.HM. rewrite (hr_root _ _ _ _ _ _ _ _ _ HR). lia.
      - destruct (TAILV p ltac:(lia)) as [[A _]|A]; lia. }
    set (k := nd HPf p - E + 1) in *.
    assert (Pp : posof L HPf (E + k - 1) = p) by (subst k; replace (E + (nd HPf p - E + 1) - 1) with (nd HPf p) by lia; apply (posof_nd _ _ _ _ _ _ _ _ _ HR); unfold tail; lia).
    rewrite <- Pp in Pa, Pb.
    apply (proj1 (children_of_round k a ltac:(lia) ltac:(lia))) in Pa. apply (proj1 (children_of_round k b ltac:(lia) ltac:(lia))) in Pb.
    replace (nd HPf p) with (E + k - 1) by lia. rewrite (ND k) by lia.
    destruct Pa as [-> | ->]; destruct Pb as [-> | ->]; unfold nd in *; lia.
  - intros i j Hi Hj Li Lj Eq. apply (hr_inj _ _ _ _ _ _ _ _ _ HR i j); unfold RefDeflSafeB3.HM in *; [lia | lia | exact Eq].
  - intros i j Hi Hj Eq. lia.
  - intros i Hi. lia.
  - intros a b Ha Hb Nab Pab.
    destruct (par_spec _ _ _ _ _ _ _ _ _ HR a ltac:(lia)) as (Ta & _ & Nda & Ia).
    pose proof (round_of a ltac:(lia)) as (Ka & Ca & Da). cbv zeta in Ka, Ca, Da. set (k := (572 - a) / 2 + 1) in *.
    assert (Ppar : par t L HPf a = posof L HPf (E + k - 1)).
    { rewrite <- Da, <- Nda. symmetry. apply (posof_nd _ _ _ _ _ _ _ _ _ HR). exact Ta. }
    rewrite Pab in Ppar. pose proof (proj1 (children_of_round k b Ka ltac:(lia)) Ppar) as Cb. lia.
  - intros i Hi Hp. destruct (par_spec _ _ _ _ _ _ _ _ _ HR i ltac:(lia)) as (_ & B & _). lia.
  - (* [comment removed for export] *)
    intros i x Hi Hx Hext ALIVE.
    pose proof (round_of i ltac:(lia)) as (Ki & Ci & Di). cbv zeta in Ki, Ci, Di. set (k := (572 - i) / 2 + 1) in *. clearbody k.
    (* [comment removed for export] *)
    assert (AL : nd HPf x < E + k - 1 \/ (nd HPf x = E + k - 1 /\ i = 573 - 2 * k)).
    { destruct ALIVE as [Lx | (c & Hc & Pc & Ec)].
      - left. unfold leafb in Lx. apply Z.ltb_lt in Lx. lia.
      - destruct (par_spec _ _ _ _ _ _ _ _ _ HR c ltac:(lia)) as (Tc & _ & Ndc & Ic). rewrite Pc in Ndc, Tc.
        pose proof (round_of c ltac:(lia)) as (Kc & Cc & Dc). cbv zeta in Kc, Cc, Dc. rewrite Ndc, Dc.
        unfold RefDeflSafeB3.HM in *. Z.to_euclidean_division_equations; lia. }
    destruct AL as [LT | [EQ ->]].
    + destruct Ci as [-> | ->].
      * destruct (Z.eq_dec x (573 - 2 * k)) as [->|Nx]; [apply NM; exact Ki|].
        exact (proj1 (MIN k x Ki ltac:(unfold RefDeflSafeB3.HM in *; lia) LT)).
      * exact (proj2 (MIN k x Ki ltac:(unfold RefDeflSafeB3.HM in *; lia) LT)).
    + rewrite EQ, (ND k Ki). pose proof (WN (arr_get HPf (574 - 2 * k))). unfold nd in *. lia.
Qed.
End GTree.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section BuildTree.
Variable s : deflate_state.
Variable t : tree_id.
Local Notation E := (sd_elems t).
Hypothesis HP : bt_pre s t.
Hypothesis WB : zsum (fun u => arr_get (tree_fc s t) u) 0 (Z.to_nat E) + 2 < 2 ^ 16.

(* [comment removed for export] *)

End BuildTree.
