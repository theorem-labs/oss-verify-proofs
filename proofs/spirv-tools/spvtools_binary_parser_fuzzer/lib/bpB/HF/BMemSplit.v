(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BSeqExec BStepTac BStoreOk BStreamSim.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma wbytes_inside : forall bs m (a x : word),
  bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
  wbytes m a bs x = Some (nth (Z.to_nat (bv_unsigned x - bv_unsigned a)) bs (Z_to_bv 8 0)).
Proof.
  induction bs as [|b rest IH]; intros m a x Hnw Hx; [cbn in Hx; lia|].
  cbn [wbytes length] in *.
  destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
  - assert (x = a) by (apply bv_eq; exact Heq). subst x.
    rewrite Z.sub_diag. cbn [Z.to_nat nth].
    destruct rest as [|b' rest'].
    + cbn [wbytes]. rewrite bv_eqb_refl. reflexivity.
    + cbn [length] in Hnw. rewrite wbytes_below.
      * rewrite bv_eqb_refl. reflexivity.
      * rewrite u_add1 by lia. cbn [length]. lia.
      * rewrite u_add1 by lia. lia.
  - assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1)
      by (apply u_add1; lia).
    rewrite (IH _ (a + 1)%bv) by (rewrite Hu1; lia).
    rewrite Hu1.
    replace (Z.to_nat (bv_unsigned x - bv_unsigned a))
      with (S (Z.to_nat (bv_unsigned x - (bv_unsigned a + 1)))) by lia.
    reflexivity.
Qed.

Lemma wbytes_outside : forall bs m (a x : word),
  bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned x) ->
  wbytes m a bs x = m x.
Proof.
  intros bs m a x Hnw [Hlt|Hge].
  - apply wbytes_below; assumption.
  - apply wbytes_above; assumption.
Qed.

Lemma wbytes_select : forall (P : word -> bool) (f g : word -> option byte) (a : word) bs,
  bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
                    P x = true) ->
  wbytes (fun x => if P x then f x else g x) a bs
  = (fun x => if P x then wbytes f a bs x else g x).
Proof.
  intros P f g a bs Hnw HP. apply functional_extensionality. intro x.
  destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
  - rewrite !wbytes_outside by lia. reflexivity.
  - destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Hin|Hout].
    + rewrite !wbytes_inside by lia. rewrite (HP x) by lia. reflexivity.
    + rewrite !wbytes_outside by lia. reflexivity.
Qed.

Lemma wbytes_select_r : forall (P : word -> bool) (f g : word -> option byte) (a : word) bs,
  bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
                    P x = false) ->
  wbytes (fun x => if P x then f x else g x) a bs
  = (fun x => if P x then f x else wbytes g a bs x).
Proof.
  intros P f g a bs Hnw HP. apply functional_extensionality. intro x.
  destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
  - rewrite !wbytes_outside by lia. reflexivity.
  - destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Hin|Hout].
    + rewrite !wbytes_inside by lia. rewrite (HP x) by lia. reflexivity.
    + rewrite !wbytes_outside by lia. reflexivity.
Qed.

Definition win_lo (sp0 : word) : Z := bv_unsigned sp0 - stack_max_size.

Definition in_win (sp0 : word) (x : word) : Prop :=
  win_lo sp0 <= bv_unsigned x < bv_unsigned sp0.

Definition cmem (sp0 : word) (mem0 J D : word -> option byte) : word -> option byte :=
  fun a => if (bv_unsigned sp0 <=? bv_unsigned a) then mem0 a
           else if (win_lo sp0 <=? bv_unsigned a) then J a else D a.

Definition wfJ (sp0 : word) (J : word -> option byte) : Prop :=
  forall x : word, in_win sp0 x -> J x <> None.

Lemma wfJ_wbytes : forall sp0 J a bs, wfJ sp0 J -> wfJ sp0 (wbytes J a bs).
Proof. intros sp0 J a bs H x Hx. apply wbytes_grows. apply H. exact Hx. Qed.

Definition agree_above (lo : Z) (J J' : word -> option byte) : Prop :=
  forall x : word, lo <= bv_unsigned x -> J' x = J x.

Section CMem.
  Variable sp0 : word.
  Variable mem0 : word -> option byte.

  Let csel := cmem sp0 mem0.

  Lemma stack_max_size_pos : 0 < stack_max_size.
  Proof. rewrite stack_max_size_val. lia. Qed.

  Lemma wbytes_cmem_win : forall J D (a : word) bs,
    win_lo sp0 <= bv_unsigned a ->
    bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned sp0 ->
    wbytes (cmem sp0 mem0 J D) a bs = cmem sp0 mem0 (wbytes J a bs) D.
  Proof.
    intros J D a bs Hlo Hhi. unfold cmem.
    pose proof (u64_range sp0) as Hsp.
    rewrite (wbytes_select_r (fun x => bv_unsigned sp0 <=? bv_unsigned x) mem0
               (fun x => if win_lo sp0 <=? bv_unsigned x then J x else D x) a bs)
      by (first [lia | intros x Hx; apply Z.leb_gt; lia]).
    apply functional_extensionality. intro x.
    destruct (bv_unsigned sp0 <=? bv_unsigned x); [reflexivity|].
    rewrite (wbytes_select (fun x => win_lo sp0 <=? bv_unsigned x) J D a bs)
      by (first [lia | intros y Hy; apply Z.leb_le; lia]).
    reflexivity.
  Qed.

  Lemma wbytes_cmem_data : forall J D (a : word) bs,
    bv_unsigned a + Z.of_nat (length bs) <= win_lo sp0 ->
    wbytes (cmem sp0 mem0 J D) a bs = cmem sp0 mem0 J (wbytes D a bs).
  Proof.
    intros J D a bs Hhi. unfold cmem.
    pose proof (u64_range sp0) as Hsp. pose proof stack_max_size_pos.
    unfold win_lo in *.
    rewrite (wbytes_select_r (fun x => bv_unsigned sp0 <=? bv_unsigned x) mem0
               (fun x => if bv_unsigned sp0 - stack_max_size <=? bv_unsigned x then J x else D x) a bs)
      by (first [lia | intros x Hx; apply Z.leb_gt; lia]).
    apply functional_extensionality. intro x.
    destruct (bv_unsigned sp0 <=? bv_unsigned x); [reflexivity|].
    rewrite (wbytes_select_r (fun x => bv_unsigned sp0 - stack_max_size <=? bv_unsigned x) J D a bs)
      by (first [lia | intros y Hy; apply Z.leb_gt; lia]).
    reflexivity.
  Qed.

  Lemma rdn_cmem_data : forall segs J D (a : word) n,
    bv_unsigned a + Z.of_nat n <= win_lo sp0 ->
    rdn segs (cmem sp0 mem0 J D) a n = rdn segs D a n.
  Proof.
    intros segs J D a n Hhi. pose proof (u64_range sp0). pose proof stack_max_size_pos.
    unfold win_lo in *.
    apply rdn_ext; [lia|].
    intros x Hx. unfold cmem, win_lo.
    rewrite (proj2 (Z.leb_gt _ _)) by lia.
    rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
  Qed.

  Lemma cmem_at_win : forall J D (x : word),
    in_win sp0 x -> cmem sp0 mem0 J D x = J x.
  Proof.
    intros J D x [Hlo Hhi]. unfold cmem.
    rewrite (proj2 (Z.leb_gt _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
  Qed.

  Lemma store_ok_cmem_win : forall segs J D (a : word) n,
    wfJ sp0 J ->
    win_lo sp0 <= bv_unsigned a ->
    bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 ->
    store_ok segs (cmem sp0 mem0 J D) a n = true.
  Proof.
    intros segs J D a n HJ Hlo Hhi. pose proof (u64_range sp0).
    apply store_ok_of_all; [lia|].
    intros x Hx. unfold wview.
    rewrite cmem_at_win by (unfold in_win; lia).
    destruct (J x) as [b|] eqn:E; [discriminate|].
    exfalso. apply (HJ x); [unfold in_win; lia | exact E].
  Qed.

  Lemma store_ok_cmem_data : forall segs J D (a : word) n,
    wseg_ok segs a n = true ->
    store_ok segs (cmem sp0 mem0 J D) a n = true.
  Proof. intros. apply store_ok_wseg. assumption. Qed.

End CMem.

