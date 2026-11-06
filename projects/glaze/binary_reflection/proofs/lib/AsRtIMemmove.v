(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsDepotSum.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation U := bv_unsigned.

Definition ivl (lo n : Z) : Z -> Prop := fun z => lo <= z < lo + n.
Definition wun (W1 W2 : Z -> Prop) : Z -> Prop := fun z => W1 z \/ W2 z.

Definition msum (W : Z -> Prop) (M M' : word -> option byte) : Prop :=
  (forall x : word, ~ W (U x) -> M' x = M x) /\ mem_grows M M'.

Lemma msum_refl : forall W M, msum W M M.
Proof. intros W M. split; [intros x _; reflexivity | apply mem_grows_refl]. Qed.
Lemma msum_trans : forall W1 W2 M1 M2 M3, msum W1 M1 M2 -> msum W2 M2 M3 -> msum (wun W1 W2) M1 M3.
Proof.
  intros W1 W2 M1 M2 M3 [F1 G1] [F2 G2]. split.
  - intros x Hx. rewrite F2 by (intro H; apply Hx; right; exact H). apply F1. intro H. apply Hx. left. exact H.
  - eapply mem_grows_trans; eassumption.
Qed.
Lemma msum_weaken : forall (W W' : Z -> Prop) M M', (forall z, W z -> W' z) -> msum W M M' -> msum W' M M'.
Proof. intros W W' M M' S [F G]. split; [intros x Hx; apply F; intro H; apply Hx, S, H | exact G]. Qed.
Lemma msum_outside : forall (W : Z -> Prop) (M M' : word -> option byte), (forall x : word, ~ W (U x) -> M' x = M x) -> mem_grows M M' -> msum W M M'.
Proof. intros W M M' F G. split; assumption. Qed.
Lemma msum_wbytes : forall M (a : word) bs, U a + Z.of_nat (length bs) <= 2 ^ 64 -> msum (ivl (U a) (Z.of_nat (length bs))) M (wbytes M a bs).
Proof.
  intros M a bs Hnw. split; [| apply wbytes_grows]. intros x Hx. unfold ivl in Hx.
  destruct (Z_lt_le_dec (U x) (U a)) as [C|C]; [apply wbytes_below; lia|].
  destruct (Z_lt_le_dec (U x) (U a + Z.of_nat (length bs))) as [C'|C']; [exfalso; apply Hx; lia|]. apply wbytes_above. lia.
Qed.

Section Transfer.
  Variable segs : list Segment.
  Lemma msum_rdn : forall (W : Z -> Prop) M M' (a : word) n, msum W M M' -> U a + Z.of_nat n <= 2 ^ 64 ->
    (forall z, U a <= z < U a + Z.of_nat n -> ~ W z) -> rdn segs M' a n = rdn segs M a n.
  Proof using. intros W M M' a n [F _] Hnw Hd. apply rdn_ext; [exact Hnw|]. intros x Hx. apply F. apply Hd. exact Hx. Qed.
  Lemma msum_rdn_eq : forall (W : Z -> Prop) M M' (a : word) n v, msum W M M' -> U a + Z.of_nat n <= 2 ^ 64 ->
    (forall z, U a <= z < U a + Z.of_nat n -> ~ W z) -> rdn segs M a n = Some v -> rdn segs M' a n = Some v.
  Proof using. intros W M M' a n v S Hnw Hd Hr. rewrite (msum_rdn W M M' a n S Hnw Hd). exact Hr. Qed.
  Lemma msum_store_ok : forall (W : Z -> Prop) M M' (a : word) n, msum W M M' -> store_ok segs M a n = true -> store_ok segs M' a n = true.
  Proof using. intros W M M' a n [_ G] H. eapply store_ok_mono; eassumption. Qed.

  (* [comment removed for export] *)
  Lemma msum_unrestrict : forall (Hd : word -> bool) (W : Z -> Prop) M Mr',
    (forall x : word, W (U x) -> Hd x = false) -> msum W (mrestrict Hd M) Mr' -> msum W M (munrestrict Hd M Mr').
  Proof using.
    intros Hd W M Mr' HW [F G]. split.
    - intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold munrestrict in G in change_no_check G' end). destruct (Hd x) eqn:E; [reflexivity|]. rewrite (F x Hx). (lazymatch goal with |- ?G => let G' := eval unfold mrestrict in G in change_no_check G' end). rewrite E. reflexivity.
    - intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold munrestrict in G in change_no_check G' end). destruct (Hd x) eqn:E; [exact Hx|]. apply G. (lazymatch goal with |- ?G => let G' := eval unfold mrestrict in G in change_no_check G' end). rewrite E. exact Hx.
  Qed.
  Lemma rdn_munrestrict : forall (Hd : word -> bool) M Mr' (a : word) n, U a + Z.of_nat n <= 2 ^ 64 -> hid_off Hd (U a) (Z.of_nat n) ->
    rdn segs (munrestrict Hd M Mr') a n = rdn segs Mr' a n.
  Proof using. intros Hd M Mr' a n Hnw Hh. apply rdn_ext; [exact Hnw|]. intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold munrestrict in G in change_no_check G' end). rewrite (Hh x Hx). reflexivity. Qed.
End Transfer.
End AsDepotSum.
Module AsDepotSum2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib AsDepotSum.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
#[local] Abbreviation U := bv_unsigned.
Definition Wdec (W : Z -> Prop) : Type := forall z, {W z} + {~ W z}.
Lemma ivl_dec : forall lo n, Wdec (ivl lo n).
Proof. intros lo n z. (lazymatch goal with |- ?G => let G' := eval unfold ivl in G in change_no_check G' end). destruct (Z_le_dec lo z); [destruct (Z_lt_dec z (lo + n)); [left; lia | right; lia] | right; lia]. Defined.
Lemma wun_dec : forall W1 W2, Wdec W1 -> Wdec W2 -> Wdec (wun W1 W2).
Proof. intros W1 W2 D1 D2 z. (lazymatch goal with |- ?G => let G' := eval unfold wun in G in change_no_check G' end). destruct (D1 z); [left; left; assumption|]. destruct (D2 z); [left; right; assumption | right; tauto]. Defined.
Lemma msum_changed : forall W (M M' : word -> option byte), Wdec W -> msum W M M' -> forall a : word, M' a <> M a -> W (U a) /\ M' a <> None.
Proof.
  intros W M M' D [F G] a NE. split.
  - destruct (D (U a)) as [Y|N]; [exact Y | exfalso; apply NE; apply F; exact N].
  - destruct (M a) eqn:EM; [apply G; rewrite EM; discriminate|]. destruct (M' a) eqn:EM'; [discriminate | exfalso; apply NE; reflexivity].
Qed.
End AsDepotSum2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition imemmove_words : list (bv 32) :=
  [W_7fed8; W_7fedc; W_7fee0; W_7fee4; W_7fee8; W_7feec; W_7fef0; W_7fef4; W_7fef8; W_7fefc; W_7ff00;
   W_7ff04; W_7ff08; W_7ff0c; W_7ff10; W_7ff14; W_7ff18; W_7ff1c; W_7ff20; W_7ff24; W_7ff28; W_7ff2c]%list.

(* [comment removed for export] *)
Definition imemmove_clob : list reg := [11; 12; 13; 14; 15; 16].

Section FPGen1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition inrng (a : Z) (len : Z) (x : Z) : bool := (Z.leb a x && Z.ltb x (a + len))%bool.

Lemma inrng_true : forall a len x, inrng a len x = true <-> (a <= x < a + len)%Z.
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold inrng in G in change_no_check G' end). rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.

Lemma inrng_false : forall a len x, inrng a len x = false <-> ~ (a <= x < a + len)%Z.
Proof using. intros. rewrite <- inrng_true. destruct (inrng a len x); split; intros; congruence. Qed.

Lemma wbytes_get_g : forall bs m (a x : word),
  (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  wbytes m a bs x =
    if inrng (bv_unsigned a) (Z.of_nat (length bs)) (bv_unsigned x)
    then Some (nth (Z.to_nat (bv_unsigned x - bv_unsigned a)) bs (Z_to_bv 8 0))
    else m x.
Proof using.
  induction bs as [|b rest IH]; intros m a x Hnw.
  - (lazymatch goal with |- ?G => let G' := eval cbn [wbytes length Z.of_nat] in G in change_no_check G' end). destruct (inrng _ _ _) eqn:E; [|reflexivity].
    apply inrng_true in E. lia.
  - cbn [wbytes length] in *. pose proof (u64_range a). pose proof (u64_range x).
    destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Ex|Nx].
    + assert (x = a) by (apply bv_eq; exact Ex). subst x.
      match goal with |- wbytes ?m1 _ _ _ = _ =>
        assert (Hb : wbytes m1 (a + 1)%bv rest a = m1 a) end.
      { destruct rest as [|b2 rest2]; [reflexivity|]. cbn [length] in Hnw.
        apply wbytes_below; rewrite word_succ_at, at_u; (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); lia. }
      rewrite Hb, bv_eqb_refl.
      replace (inrng _ _ _) with true by (symmetry; apply inrng_true; lia).
      rewrite Z.sub_diag. reflexivity.
    + destruct rest as [|b2 rest2].
      { (lazymatch goal with |- ?G => let G' := eval cbn [wbytes length Z.of_nat Z.add] in G in change_no_check G' end). rewrite (bv_eqb_neq x a) by (intros ->; apply Nx; reflexivity).
        destruct (inrng _ _ _) eqn:E; [|reflexivity].
        exfalso. apply inrng_true in E. cbn in E. lia. }
      cbn [length] in Hnw.
      rewrite IH by (rewrite word_succ_at, at_u; (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); lia).
      rewrite word_succ_at, at_u by lia.
      rewrite (bv_eqb_neq x a) by (intros ->; apply Nx; reflexivity).
      destruct (inrng (bv_unsigned a + 1) _ _) eqn:E1; destruct (inrng (bv_unsigned a) _ _) eqn:E2.
      * apply inrng_true in E1.
        replace (Z.to_nat (bv_unsigned x - bv_unsigned a)) with (S (Z.to_nat (bv_unsigned x - (bv_unsigned a + 1)))) by lia.
        reflexivity.
      * exfalso. apply inrng_true in E1. apply inrng_false in E2. cbn [length] in E1, E2. lia.
      * exfalso. apply inrng_true in E2. apply inrng_false in E1. cbn [length] in E1, E2. lia.
      * reflexivity.
Qed.

(* [comment removed for export] *)
Lemma wbytes_comm_g : forall m (a1 a2 : word) l1 l2,
  (bv_unsigned a1 + Z.of_nat (length l1) <= 2 ^ 64)%Z ->
  (bv_unsigned a2 + Z.of_nat (length l2) <= 2 ^ 64)%Z ->
  (bv_unsigned a1 + Z.of_nat (length l1) <= bv_unsigned a2 \/ bv_unsigned a2 + Z.of_nat (length l2) <= bv_unsigned a1)%Z ->
  wbytes (wbytes m a1 l1) a2 l2 = wbytes (wbytes m a2 l2) a1 l1.
Proof using.
  intros m a1 a2 l1 l2 H1 H2 Hd. apply functional_extensionality. intros x.
  rewrite !wbytes_get_g by assumption.
  destruct (inrng (bv_unsigned a2) _ _) eqn:E2; destruct (inrng (bv_unsigned a1) _ _) eqn:E1; try reflexivity.
  exfalso. apply inrng_true in E1. apply inrng_true in E2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section OVL.
  Variable segs : list Segment.
  Variable mem0 : word -> option byte.
  Variables d s : word.
  Variable n : Z.
  Variable bs : list byte.
  Hypothesis Hn : (0 <= n < 2 ^ 63)%Z.
  Hypothesis Hlen : length bs = Z.to_nat n.
  Hypothesis Hsrc : rdn segs mem0 s (length bs) = Some bs.
  Hypothesis Hdst : store_ok segs mem0 d (Z.to_nat n) = true.
  Hypothesis Hnws : (bv_unsigned s + n < 2 ^ 64)%Z.
  Hypothesis Hnwd : (bv_unsigned d + n < 2 ^ 64)%Z.

  (* [comment removed for export] *)
  Definition memF (k : Z) : word -> option byte := wbytes mem0 d (firstn (Z.to_nat k) bs).
  (* [comment removed for export] *)
  Definition memB (k : Z) : word -> option byte := wbytes mem0 (at_ d k) (skipn (Z.to_nat k) bs).

  Lemma memF_n : memF n = wbytes mem0 d bs.
  Proof using Hlen. (lazymatch goal with |- ?G => let G' := eval unfold memF in G in change_no_check G' end). rewrite <- Hlen, firstn_all. reflexivity. Qed.
  Lemma memB_n : memB n = mem0.
  Proof using Hlen. (lazymatch goal with |- ?G => let G' := eval unfold memB in G in change_no_check G' end). rewrite <- Hlen, skipn_all. reflexivity. Qed.
  Lemma memB_0 : memB 0 = wbytes mem0 d bs.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold memB in G in change_no_check G' end). rewrite at_0. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma rdF1 : forall k j,
      (bv_unsigned d < bv_unsigned s)%Z ->
      (0 <= k <= j)%Z -> (j + 1 <= n)%Z ->
      rdn segs (memF k) (at_ s j) 1 = Some [b_ bs j].
  Proof using Hnws Hsrc Hlen.
    intros k j Hds Hk Hj. (lazymatch goal with |- ?G => let G' := eval unfold memF, b_ in G in change_no_check G' end). pose proof (u64_range s). pose proof (u64_range d).
    rewrite rdn_wbytes_out.
    - replace (at_ s j) with (at_ s (Z.of_nat (Z.to_nat j))) by (f_equal; lia).
      rewrite (rdn_sub segs mem0 (length bs) s bs (Z.to_nat j) 1 Hsrc) by (rewrite Hlen; lia).
      rewrite sub_nth by (rewrite Hlen; lia). reflexivity.
    - right. rewrite length_firstn, Hlen, at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia.
    - rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia.
    - rewrite length_firstn, Hlen. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rdB1 : forall k j,
      (bv_unsigned s < bv_unsigned d)%Z ->
      (0 <= j)%Z -> (j + 1 <= k)%Z -> (k <= n)%Z ->
      rdn segs (memB k) (at_ s j) 1 = Some [b_ bs j].
  Proof using Hnwd Hsrc Hlen.
    intros k j Hsd Hj Hjk Hk. (lazymatch goal with |- ?G => let G' := eval unfold memB, b_ in G in change_no_check G' end). pose proof (u64_range s). pose proof (u64_range d).
    rewrite rdn_wbytes_out.
    - replace (at_ s j) with (at_ s (Z.of_nat (Z.to_nat j))) by (f_equal; lia).
      rewrite (rdn_sub segs mem0 (length bs) s bs (Z.to_nat j) 1 Hsrc) by (rewrite Hlen; lia).
      rewrite sub_nth by (rewrite Hlen; lia). reflexivity.
    - left. rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia.
    - rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia.
    - rewrite length_skipn, Hlen, at_u; lia.
  Qed.

  Lemma wrF : forall k j m, (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z -> store_ok segs (memF k) (at_ d j) m = true.
  Proof using Hnwd Hdst Hlen Hn.
    intros k j m Hj Hm. (lazymatch goal with |- ?G => let G' := eval unfold memF in G in change_no_check G' end).
    apply (store_ok_at segs mem0 d (Z.to_nat n)); try assumption; lia.
  Qed.

  Lemma wrB : forall k j m, (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z -> (0 <= k)%Z -> store_ok segs (memB k) (at_ d j) m = true.
  Proof using Hnwd Hdst Hlen.
    intros k j m Hj Hm Hk. (lazymatch goal with |- ?G => let G' := eval unfold memB in G in change_no_check G' end). pose proof (u64_range d).
    destruct m as [|m']; [reflexivity|].
    apply (store_ok_mono segs (S m') mem0); [apply wbytes_grows|].
    apply (store_ok_sub segs mem0 d (at_ d j) (Z.to_nat n) (S m')); try assumption; rewrite ?at_u; lia.
  Qed.

  Lemma memF_extend1 : forall k, (0 <= k)%Z -> (k + 1 <= n)%Z ->
      wbytes (memF k) (at_ d k) [b_ bs k] = memF (k + 1).
  Proof using Hlen.
    intros k Hk H1. (lazymatch goal with |- ?G => let G' := eval unfold memF, b_ in G in change_no_check G' end).
    replace (at_ d k) with (at_ d (Z.of_nat (Z.to_nat k))) by (f_equal; lia).
    rewrite <- sub_nth by (rewrite Hlen; lia).
    rewrite wbytes_extend' by (rewrite Hlen; lia). f_equal. f_equal. lia.
  Qed.

  Lemma memB_extend1 : forall k, (1 <= k <= n)%Z ->
      wbytes (memB k) (at_ d (k - 1)) [b_ bs (k - 1)] = memB (k - 1).
  Proof using Hnwd Hlen.
    intros k Hk. (lazymatch goal with |- ?G => let G' := eval unfold memB, b_ in G in change_no_check G' end). pose proof (u64_range d).
    assert (Hs : skipn (Z.to_nat (k - 1)) bs = sub bs (Z.to_nat (k - 1)) 1 ++ skipn (Z.to_nat k) bs).
    { (lazymatch goal with |- ?G => let G' := eval unfold sub in G in change_no_check G' end). rewrite <- (firstn_skipn 1 (skipn (Z.to_nat (k - 1)) bs)) at 1.
      rewrite skipn_skipn. f_equal. f_equal. lia. }
    rewrite Hs, wbytes_app, at_at.
    assert (Hl : length (sub bs (Z.to_nat (k - 1)) 1) = 1%nat) by (apply sub_length; rewrite Hlen; lia).
    rewrite Hl. replace (k - 1 + Z.of_nat 1)%Z with k by lia.
    rewrite sub_nth by (rewrite Hlen; lia). symmetry.
    apply wbytes_comm_g.
    - (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). rewrite at_u; lia.
    - rewrite length_skipn, Hlen, at_u; lia.
    - left. (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). rewrite !at_u; lia.
  Qed.
End OVL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section IMEMMOVE.
  Variable segs : list Segment.
  Variable base : word.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HCODE : code_at segs base 0 imemmove_words.
  Hypothesis Hn : (0 <= n < 2 ^ 63)%Z.
  Hypothesis Hlen : length bs = Z.to_nat n.
  Hypothesis Hsrc : rdn segs mem0 src (length bs) = Some bs.
  Hypothesis Hdst : store_ok segs mem0 dst (Z.to_nat n) = true.
  Hypothesis Hnws : (bv_unsigned src + n < 2 ^ 64)%Z.
  Hypothesis Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z.

  #[local] Abbreviation MF := (memF mem0 dst bs).
  #[local] Abbreviation MB := (memB mem0 dst bs).
  #[local] Abbreviation B := (b_ bs).
  #[local] Abbreviation CL := (fun r => In r imemmove_clob).

  (* [comment removed for export] *)
  Definition imemmove_mem : word -> option byte :=
    if Z.eqb (bv_unsigned dst) (bv_unsigned src) then mem0 else wbytes mem0 dst bs.

  Ltac get_code :=
    let HC := fresh "HC" in
    pose proof HCODE as HC; cbn [code_at imemmove_words Z.add Pos.add Pos.succ] in HC;
    destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24 & C28 & C32 & C36 & C40 & C44 & C48 & C52 & C56 & C60 & C64
                    & C68 & C72 & C76 & C80 & C84 & _).

  (* [comment removed for export] *)
  Ltac side := first [eassumption | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].

  (* [comment removed for export] *)
  Ltac mlbu F D RD :=
    chain_step; [reflexivity
      | eapply step_lbu; [exact F | reflexivity | exact D | gres; rwH; imm_norm; rewrite ?at_addi, ?Z.add_0_r; eapply RD; side]
      | step_simpl]; vn.
  (* [comment removed for export] *)
  Ltac msb F D kk WR EXT :=
    chain_step; [reflexivity
      | eapply MmapSim.step_sb_at with (a := at_ dst kk) (b := B kk);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi, ?Z.add_0_r; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | apply sb_val_b
        | eapply WR; side ]
      | step_simpl];
    rewrite EXT by side; vn.

  (* [comment removed for export] *)
  Lemma fwd_loop : forall (i : nat) regs (ret : word) k,
    (bv_unsigned dst < bv_unsigned src)%Z ->
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = at_ dst n ->
    (0 <= k < n)%Z -> Z.of_nat i = (n - 1 - k)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 16) (MF k) rom) (mkst regs' ret (MF n) rom)
      /\ regs_agree CL regs regs'.
  Proof using Hnwd Hnws Hdst Hsrc Hlen Hn HCODE.
    get_code. pose proof (u64_range src) as Hs. pose proof (u64_range dst) as Hd.
    induction i as [|i IH]; intros regs ret k Hds Hret H1 H11 H13 H12 Hk Hi.
    - wd_eexists. split.
      + mlbu C16 D_7fee8 rdF1.                                          (* [comment removed for export] *)
        msb C20 D_7feec k wrF (memF_extend1 mem0 dst n bs Hlen k).  (* [comment removed for export] *)
        an C24 D_7fef0.                                (* [comment removed for export] *)
        an C28 D_7fef4.                                (* [comment removed for export] *)
        ab_ft C32 D_7fef8 ltac:(condz).                (* [comment removed for export] *)
        an C36 D_7fefc.                                (* [comment removed for export] *)
        aret C84 D_7ff2c ret.
        replace (k + 1)%Z with n by lia. wd_refl.
      + (lazymatch goal with |- ?G => let G' := eval unfold imemmove_clob in G in change_no_check G' end). solve_regs_agree.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 16) (MF (k + 1)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1)
                         /\ getr r 12 = at_ dst n /\ regs_agree CL regs r)).
      + wd_eexists. split.
        * mlbu C16 D_7fee8 rdF1.
          msb C20 D_7feec k wrF (memF_extend1 mem0 dst n bs Hlen k).
          an C24 D_7fef0.
          an C28 D_7fef4.
          ab_tk C32 D_7fef8 ltac:(condz).              (* [comment removed for export] *)
          wd_refl.
        * post. (lazymatch goal with |- ?G => let G' := eval unfold imemmove_clob in G in change_no_check G' end). solve_regs_agree.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
        destruct (IH r1 ret (k + 1)%Z Hds Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
        exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  Lemma bwd_loop : forall (i : nat) regs (ret a2v : word) k,
    (bv_unsigned src < bv_unsigned dst)%Z ->
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 13 = Z_to_bv 64 (k - 1) ->
    getr regs 12 = a2v -> bv_unsigned a2v = 1%Z ->
    (1 <= k <= n)%Z -> Z.of_nat i = (k - 1)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 56) (MB k) rom) (mkst regs' ret (MB 0) rom)
      /\ regs_agree CL regs regs'.
  Proof using Hnwd Hdst Hsrc Hlen Hn HCODE.
    get_code. pose proof (u64_range src) as Hs. pose proof (u64_range dst) as Hd.
    induction i as [|i IH]; intros regs ret a2v k Hsd Hret H1 H10 H11 H13 H12 Ha2 Hk Hi.
    - (* [comment removed for export] *)
      wd_eexists. split.
      + av C56 D_7ff10 (at_ src (k - 1)) ltac:(apply v_add_at; lia).                 (* [comment removed for export] *)
        mlbu C60 D_7ff14 rdB1.                                                         (* [comment removed for export] *)
        av C64 D_7ff18 (at_ dst (k - 1)) ltac:(apply v_add_at; lia).                 (* [comment removed for export] *)
        av C68 D_7ff1c (Z_to_bv 64 k) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).       (* [comment removed for export] *)
        av C72 D_7ff20 (Z_to_bv 64 (k - 2)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia). (* [comment removed for export] *)
        msb C76 D_7ff24 (k - 1)%Z wrB (memB_extend1 mem0 dst n bs Hlen Hnwd k).      (* [comment removed for export] *)
        ab_ft C80 D_7ff28 ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_ltu, bv_ltu in G in change_no_check G' end); unorm; rewrite Ha2; apply Z.ltb_ge; lia).  (* [comment removed for export] *)
        aret C84 D_7ff2c ret.
        replace (k - 1)%Z with 0%Z by lia. wd_refl.
      + (lazymatch goal with |- ?G => let G' := eval unfold imemmove_clob in G in change_no_check G' end). solve_regs_agree.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 56) (MB (k - 1)) rom)
               (fun r => getr r 1 = ret /\ getr r 10 = dst /\ getr r 11 = src /\ getr r 13 = Z_to_bv 64 (k - 1 - 1)
                         /\ getr r 12 = a2v /\ regs_agree CL regs r)).
      + wd_eexists. split.
        * av C56 D_7ff10 (at_ src (k - 1)) ltac:(apply v_add_at; lia).
          mlbu C60 D_7ff14 rdB1.
          av C64 D_7ff18 (at_ dst (k - 1)) ltac:(apply v_add_at; lia).
          av C68 D_7ff1c (Z_to_bv 64 k) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).
          av C72 D_7ff20 (Z_to_bv 64 (k - 1 - 1)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).
          msb C76 D_7ff24 (k - 1)%Z wrB (memB_extend1 mem0 dst n bs Hlen Hnwd k).
          ab_tk C80 D_7ff28 ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_ltu, bv_ltu in G in change_no_check G' end); unorm; rewrite Ha2; apply Z.ltb_lt; lia).  (* [comment removed for export] *)
          wd_refl.
        * post. (lazymatch goal with |- ?G => let G' := eval unfold imemmove_clob in G in change_no_check G' end). solve_regs_agree.
      + cbv beta. intros r1 (R1 & R10 & R11 & R13 & R12 & AG).
        destruct (IH r1 ret a2v (k - 1)%Z Hsd Hret R1 R10 R11 R13 R12 Ha2 ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
        exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.

  Ltac blez_tac :=
    rwH; (lazymatch goal with |- ?G => let G' := eval cbn [getr bv_eqb Z.eqb] in G in change_no_check G' end); rewrite ?c_lts_smallZ by lia;
    first [apply Z.ltb_lt | apply Z.ltb_ge]; lia.

  (* [comment removed for export] *)
  Theorem imemmove_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps segs (mkst regs (at_ base 0) mem0 rom) (mkst regs' ret imemmove_mem rom)
      /\ regs_agree CL regs regs'.
  Proof using Hnwd Hnws Hdst Hsrc Hlen Hn HCODE.
    get_code. intros regs ret Hret H1 H10 H11 H12.
    pose proof (u64_range src) as Hs. pose proof (u64_range dst) as Hd.
    (lazymatch goal with |- ?G => let G' := eval unfold imemmove_mem in G in change_no_check G' end).
    destruct (Z.lt_ge_cases (bv_unsigned dst) (bv_unsigned src)) as [Hlt|Hge].
    - (* [comment removed for export] *)
      replace (bv_unsigned dst =? bv_unsigned src)%Z with false by (symmetry; apply Z.eqb_neq; lia).
      destruct (Z.eq_dec n 0) as [Hz|Hnz].
      + assert (Hbs : bs = []) by (destruct bs; [reflexivity | cbn [length] in Hlen; lia]).
        rewrite Hbs. (lazymatch goal with |- ?G => let G' := eval cbn [wbytes] in G in change_no_check G' end).
        wd_eexists. split.
        * ab_ft C0 D_7fed8 ltac:(condz).                                  (* [comment removed for export] *)
          ab_tk C4 D_7fedc ltac:(blez_tac).                               (* [comment removed for export] *)
          aret C84 D_7ff2c ret. wd_refl.
        * apply regs_agree_refl.
      + rewrite <- (memF_n mem0 dst n bs Hlen). change mem0 with (MF 0).
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 16) (MF 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0
                           /\ getr r 12 = at_ dst n /\ regs_agree CL regs r)).
        * wd_eexists. split.
          -- ab_ft C0 D_7fed8 ltac:(condz).                               (* [comment removed for export] *)
             ab_ft C4 D_7fedc ltac:(blez_tac).                            (* [comment removed for export] *)
             av C8 D_7fee0 (at_ dst n) ltac:(apply v_add_at; lia).          (* [comment removed for export] *)
             an C12 D_7fee4.                                                 (* [comment removed for export] *)
             wd_refl.
          -- post; rewrite ?at_0; try reflexivity. (lazymatch goal with |- ?G => let G' := eval unfold imemmove_clob in G in change_no_check G' end). solve_regs_agree.
        * cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
          destruct (fwd_loop (Z.to_nat (n - 1)) r1 ret 0 Hlt Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
          exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
    - destruct (Z.eq_dec (bv_unsigned dst) (bv_unsigned src)) as [Heq|Hne].
      + (* [comment removed for export] *)
        replace (bv_unsigned dst =? bv_unsigned src)%Z with true by (symmetry; apply Z.eqb_eq; lia).
        wd_eexists. split.
        * ab_tk C0 D_7fed8 ltac:(condz).                                  (* [comment removed for export] *)
          ab_tk C40 D_7ff00 ltac:(condz).                                 (* [comment removed for export] *)
          aret C84 D_7ff2c ret. wd_refl.
        * apply regs_agree_refl.
      + (* [comment removed for export] *)
        replace (bv_unsigned dst =? bv_unsigned src)%Z with false by (symmetry; apply Z.eqb_neq; lia).
        destruct (Z.eq_dec n 0) as [Hz|Hnz].
        * assert (Hbs : bs = []) by (destruct bs; [reflexivity | cbn [length] in Hlen; lia]).
          rewrite Hbs. (lazymatch goal with |- ?G => let G' := eval cbn [wbytes] in G in change_no_check G' end).
          wd_eexists. split.
          -- ab_tk C0 D_7fed8 ltac:(condz).
             ab_ft C40 D_7ff00 ltac:(condz).                               (* [comment removed for export] *)
             ab_tk C44 D_7ff04 ltac:(blez_tac).                            (* [comment removed for export] *)
             aret C84 D_7ff2c ret. wd_refl.
          -- apply regs_agree_refl.
        * rewrite <- (memB_0 mem0 dst bs).
          pattern mem0 at 1. rewrite <- (memB_n mem0 dst n bs Hlen).
          eapply (runs_trans segs _ (fun r => mkst r (at_ base 56) (MB n) rom)
                   (fun r => getr r 1 = ret /\ getr r 10 = dst /\ getr r 11 = src /\ getr r 13 = Z_to_bv 64 (n - 1)
                             /\ (exists a2v, getr r 12 = a2v /\ bv_unsigned a2v = 1%Z) /\ regs_agree CL regs r)).
          -- wd_eexists. split.
             ++ ab_tk C0 D_7fed8 ltac:(condz).
                ab_ft C40 D_7ff00 ltac:(condz).
                ab_ft C44 D_7ff04 ltac:(blez_tac).                         (* [comment removed for export] *)
                av C48 D_7ff08 (Z_to_bv 64 (n - 1)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
                an C52 D_7ff0c.                                             (* [comment removed for export] *)
                wd_refl.
             ++ post. 1: { wd_eexists; split; [reflexivity|]. vm_compute. reflexivity. }
                (lazymatch goal with |- ?G => let G' := eval unfold imemmove_clob in G in change_no_check G' end). solve_regs_agree.
          -- cbv beta. intros r1 (R1 & R10 & R11 & R13 & (a2v & R12 & Ha2) & AG).
             destruct (bwd_loop (Z.to_nat (n - 1)) r1 ret a2v n ltac:(lia) Hret R1 R10 R11 R13 R12 Ha2 ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
             exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.
End IMEMMOVE.

(* [comment removed for export] *)
Record moveH (segs : list Segment) (mem0 : word -> option byte) (dst src : word) (n : Z) (bs : list byte) : Prop := MOVEH {
  mvHn : (0 <= n < 2 ^ 63)%Z;
  mvHlen : length bs = Z.to_nat n;
  mvHsrc : rdn segs mem0 src (length bs) = Some bs;
  mvHdst : store_ok segs mem0 dst (Z.to_nat n) = true;
  mvHnws : (bv_unsigned src + n < 2 ^ 64)%Z;
  mvHnwd : (bv_unsigned dst + n < 2 ^ 64)%Z }.

(* [comment removed for export] *)
Definition imemmove_result (mem0 : word -> option byte) (dst src : word) (bs : list byte) : word -> option byte :=
  if Z.eqb (bv_unsigned dst) (bv_unsigned src) then mem0 else wbytes mem0 dst bs.

Theorem imemmove_summary : forall segs base mem0 (dst src : word) n bs rom regs (ret : word),
  code_at segs base 0 imemmove_words -> moveH segs mem0 dst src n bs ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
  exists regs',
    msteps segs (mkst regs (at_ base 0) mem0 rom) (mkst regs' ret (imemmove_result mem0 dst src bs) rom)
    /\ regs_agree (fun r => In r imemmove_clob) regs regs'.
Proof using.
  intros segs base mem0 dst src n bs rom regs ret HC [Hn Hlen Hsrc Hdst Hnws Hnwd].
  exact (imemmove_run segs base mem0 dst src n bs rom HC Hn Hlen Hsrc Hdst Hnws Hnwd regs ret).
Qed.


End FPGen1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.glaze.binary_reflection.images Require Import Asan.

Section FPGen3.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition asan_imemmove_entry : word := 0x7fee0.

Lemma asan_imemmove_code :
  code_at Asan.M.loaded_segments asan_imemmove_entry 0 imemmove_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold imemmove_words in G in change_no_check G' end). code_at_vm. Qed.


End FPGen3.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
