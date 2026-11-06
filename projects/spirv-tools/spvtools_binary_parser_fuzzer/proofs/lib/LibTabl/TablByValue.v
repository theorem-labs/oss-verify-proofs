(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec LibIface LibEff.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition VAL (T : list (Z * Z * Z)) (j : Z) : Z :=
  match nth_error T (Z.to_nat j) with Some r => v_value r | None => 2 ^ 32 end.

Fixpoint sorted_adj (l : list Z) : bool :=
  match l with
  | a :: ((b :: _) as l') => (a <? b) && sorted_adj l'
  | _ => true
  end.

Definition byvalue_okb (K T : list (Z * Z * Z)) : bool :=
  forallb (fun k => let f := v_first k in let c := v_count k in
                    (0 <=? f) && (0 <=? c) && (f + c <=? Zlen T) &&
                    sorted_adj (map v_value (zsub f c T))) K
  && forallb (fun r => (0 <=? v_value r) && (v_value r <? 2 ^ 32)) T.

Lemma opnd_cert : byvalue_okb OPND_KIND OPND = true.  Proof. vm_compute. reflexivity. Qed.
Lemma ext_cert : byvalue_okb EXT_KIND EXT = true.     Proof. vm_compute. reflexivity. Qed.

Lemma sorted_adj_nth : forall l i a b, sorted_adj l = true ->
  nth_error l i = Some a -> nth_error l (S i) = Some b -> a < b.
Proof.
  induction l as [|u l IH]; intros i a b Hs Ha Hb; [destruct i; discriminate|].
  destruct l as [|v l']; [destruct i; cbn in Hb; [discriminate|destruct i; discriminate]|].
  cbn [sorted_adj] in Hs. apply andb_prop in Hs as [H1 H2]. apply Z.ltb_lt in H1.
  destruct i as [|i].
  - cbn in Ha, Hb. injection Ha as <-. injection Hb as <-. exact H1.
  - cbn in Ha, Hb. eapply IH; [exact H2 | exact Ha | exact Hb].
Qed.

Section ByValue.
Variables (K T : list (Z * Z * Z)).
Hypothesis CERT : byvalue_okb K T = true.

Lemma VAL_row : forall j, 0 <= j < Zlen T -> exists r, nth_error T (Z.to_nat j) = Some r /\ VAL T j = v_value r /\ 0 <= VAL T j < 2 ^ 32.
Proof using K T CERT.
  intros j Hj. pose proof CERT as C. unfold byvalue_okb in C. apply andb_prop in C as [_ HB]. unfold VAL.
  destruct (nth_error T (Z.to_nat j)) as [r|] eqn:E.
  - exists r. split; [reflexivity|]. split; [reflexivity|].
    rewrite forallb_forall in HB. specialize (HB r (nth_error_In _ _ E)). apply andb_prop in HB as [A B].
    apply Z.leb_le in A. apply Z.ltb_lt in B. lia.
  - exfalso. apply nth_error_None in E. unfold Zlen in Hj. lia.
Qed.

Lemma VAL_succ : forall f c j, 0 <= f -> f + c <= Zlen T -> sorted_adj (map v_value (zsub f c T)) = true ->
  f <= j -> j + 1 < f + c -> VAL T j < VAL T (j + 1).
Proof using K T CERT.
  intros f c j Hf Hfc HS Hj Hj1.
  destruct (VAL_row j ltac:(lia)) as (r & Er & -> & _). destruct (VAL_row (j + 1) ltac:(lia)) as (r' & Er' & -> & _).
  apply (sorted_adj_nth _ (Z.to_nat (j - f)) _ _ HS).
  - rewrite nth_error_map. unfold zsub. rewrite nth_error_firstn.
    replace (Z.to_nat (j - f) <? Z.to_nat c)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    rewrite nth_error_skipn. replace (Z.to_nat f + Z.to_nat (j - f))%nat with (Z.to_nat j) by lia. rewrite Er. reflexivity.
  - rewrite nth_error_map. unfold zsub. rewrite nth_error_firstn.
    replace (S (Z.to_nat (j - f)) <? Z.to_nat c)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    rewrite nth_error_skipn. replace (Z.to_nat f + S (Z.to_nat (j - f)))%nat with (Z.to_nat (j + 1)) by lia. rewrite Er'. reflexivity.
Qed.

Lemma VAL_mono : forall f c j k, 0 <= f -> f + c <= Zlen T -> sorted_adj (map v_value (zsub f c T)) = true ->
  f <= j -> j <= k -> k < f + c -> VAL T j <= VAL T k.
Proof using K T CERT.
  intros f c j k Hf Hfc HS Hj Hjk Hk. replace k with (j + Z.of_nat (Z.to_nat (k - j))) by lia.
  assert (Hm : j + Z.of_nat (Z.to_nat (k - j)) < f + c) by lia. revert Hm.
  induction (Z.to_nat (k - j)) as [|m IH]; intros Hm; [rewrite Z.add_0_r; lia|].
  pose proof (IH ltac:(lia)). pose proof (VAL_succ f c (j + Z.of_nat m) Hf Hfc HS ltac:(lia) ltac:(lia)).
  replace (j + Z.of_nat (S m)) with (j + Z.of_nat m + 1) by lia. lia.
Qed.

Lemma VAL_lt : forall f c j k, 0 <= f -> f + c <= Zlen T -> sorted_adj (map v_value (zsub f c T)) = true ->
  f <= j -> j < k -> k < f + c -> VAL T j < VAL T k.
Proof using K T CERT.
  intros f c j k Hf Hfc HS Hj Hjk Hk. pose proof (VAL_succ f c j Hf Hfc HS Hj ltac:(lia)).
  pose proof (VAL_mono f c (j + 1) k Hf Hfc HS ltac:(lia) ltac:(lia) Hk). lia.
Qed.

Lemma lbv_found : forall t f c y i, kind_range K t = (f, c) -> 0 <= f ->
  f <= i < f + c -> f + c <= Zlen T -> VAL T i = y -> (forall j, f <= j < i -> VAL T j < y) ->
  exists r, find_byvalue K T t y = Some (i, r) /\ nth_error T (Z.to_nat i) = Some r.
Proof using K T CERT.
  intros t f c y i Hk Hf Hi Hfc Hy Hlt. destruct (VAL_row i ltac:(lia)) as (r & Er & EV & _). exists r. split; [|exact Er].
  unfold find_byvalue. rewrite Hk. rewrite Z.max_r by lia.
  rewrite (find_ix_hit _ (zsub f c T) (Z.to_nat (i - f)) r f).
  - f_equal. f_equal. lia.
  - unfold zsub. rewrite nth_error_firstn. replace (Z.to_nat (i - f) <? Z.to_nat c)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    rewrite nth_error_skipn. replace (Z.to_nat f + Z.to_nat (i - f))%nat with (Z.to_nat i) by lia. exact Er.
  - apply Z.eqb_eq. congruence.
  - intros m z Hm Hz. apply Z.eqb_neq. pose proof (Hlt (f + Z.of_nat m) ltac:(lia)) as L1.
    unfold VAL in L1. unfold zsub in Hz. rewrite nth_error_firstn in Hz.
    destruct (m <? Z.to_nat c)%nat; [|discriminate]. rewrite nth_error_skipn in Hz.
    replace (Z.to_nat (f + Z.of_nat m)) with (Z.to_nat f + m)%nat in L1 by lia. rewrite Hz in L1. lia.
Qed.

Lemma lbv_missed : forall t f c y i, kind_range K t = (f, c) -> 0 <= f -> 0 <= c -> f + c <= Zlen T ->
  sorted_adj (map v_value (zsub f c T)) = true ->
  f <= i <= f + c -> (forall j, f <= j < i -> VAL T j < y) -> (forall j, i <= j < f + c -> y <= VAL T j) ->
  ~ (i < f + c /\ VAL T i = y) -> find_byvalue K T t y = None.
Proof using K T CERT.
  intros t f c y i Hk Hf Hc Hfc HS Hi Hlt Hge Hn. unfold find_byvalue. rewrite Hk. apply find_ix_none.
  intros z Hz. apply Z.eqb_neq.
  destruct (In_nth_error _ _ Hz) as [m Hm].
  unfold zsub in Hm. rewrite nth_error_firstn in Hm. destruct (Nat.ltb_spec m (Z.to_nat c)) as [Hmc|]; [|discriminate].
  rewrite nth_error_skipn in Hm.
  assert (EV : VAL T (f + Z.of_nat m) = v_value z).
  { unfold VAL. replace (Z.to_nat (f + Z.of_nat m)) with (Z.to_nat f + m)%nat by lia. rewrite Hm. reflexivity. }
  rewrite <- EV. destruct (Z.lt_ge_cases (f + Z.of_nat m) i) as [Hl|Hg].
  - pose proof (Hlt (f + Z.of_nat m) ltac:(lia)). lia.
  - pose proof (Hge (f + Z.of_nat m) ltac:(lia)).
    destruct (Z.eq_dec (f + Z.of_nat m) i) as [E|NE].
    + intros C. apply Hn. rewrite <- E. lia.
    + pose proof (Hge i ltac:(lia)). pose proof (VAL_lt f c i (f + Z.of_nat m) Hf Hfc HS ltac:(lia) ltac:(lia) ltac:(lia)).
      assert (VAL T i <> y) by (intros C; apply Hn; lia). lia.
Qed.

Lemma kind_empty : forall t y, kind_range K t = (0, 0) -> find_byvalue K T t y = None.
Proof using K T. intros t y Hk. unfold find_byvalue. rewrite Hk. reflexivity. Qed.
End ByValue.

Section Cells.
Variable SEGS : list Segment.
Variable L : Layout.
Variable ti : tabl_img.
Hypothesis RODATA : forall a, ti_ro_lo ti <= a < ti_ro_hi ti -> ro_addr L a.
Hypothesis IFX : img_facts SEGS ti.

Lemma byvalue_cell : forall T base stride (CHK : chk_rows3 SEGS ti base stride 0 T = true) M j,
  ro_clear L M -> 0 <= j < Zlen T -> 12 <= stride ->
  cell4 SEGS M (base + stride * j) (VAL T j) /\ ti_ro_lo ti <= base + stride * j /\ base + stride * j + stride <= ti_ro_hi ti.
Proof using SEGS L ti RODATA IFX.
  intros T base stride CHK M j HRO Hj Hs.
  assert (Er : exists r, nth_error T (Z.to_nat j) = Some r /\ VAL T j = v_value r).
  { unfold VAL. destruct (nth_error T (Z.to_nat j)) as [r|] eqn:E; [exists r; auto|]. exfalso. apply nth_error_None in E. unfold Zlen in Hj. lia. }
  destruct Er as (r & Er & EV).
  pose proof (chk_rows3_nth SEGS ti base stride 0 T CHK (Z.to_nat j) r Er) as C. cbn beta iota zeta in C.
  rewrite Z2Nat.id in C by lia. rewrite Z.add_0_l in C. destruct C as (Cw & C0 & _).
  destruct (in_win_bounds ti _ _ Cw) as [Wlo Whi].
  destruct (fld_of_chk SEGS L ti RODATA M _ _ HRO (if_w0 _ _ IFX) (if_w1 _ _ IFX) Wlo ltac:(lia) C0) as [F B].
  rewrite EV. split; [split; [cbn; lia | exact F] | lia].
Qed.

Lemma opnd_cell : forall M j, ro_clear L M -> 0 <= j < Zlen OPND ->
  cell4 SEGS M (ti_opnd ti + 52 * j) (VAL OPND j) /\ ti_ro_lo ti <= ti_opnd ti + 52 * j /\ ti_opnd ti + 52 * j + 52 <= ti_ro_hi ti.
Proof using SEGS L ti RODATA IFX. intros M j HRO Hj. apply (byvalue_cell OPND (ti_opnd ti) 52 (if_opnd _ _ IFX) M j HRO Hj). lia. Qed.

Lemma ext_cell : forall M j, ro_clear L M -> 0 <= j < Zlen EXT ->
  cell4 SEGS M (ti_ext ti + 28 * j) (VAL EXT j) /\ ti_ro_lo ti <= ti_ext ti + 28 * j /\ ti_ext ti + 28 * j + 28 <= ti_ro_hi ti.
Proof using SEGS L ti RODATA IFX. intros M j HRO Hj. apply (byvalue_cell EXT (ti_ext ti) 28 (if_ext _ _ IFX) M j HRO Hj). lia. Qed.
End Cells.
