(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Model.
  Variable V : Type.
  Variable n : Z.
  Variable sent : Z.

  Definition ent : Type := (Z * (Z * V))%type.
  Definition addr (e : ent) : Z := fst e.
  Definition hkey (e : ent) : Z := fst (snd e).
  Definition hh (e : ent) : Z := hmod (hkey e) n.

  Definition bjust (P : list ent) (i b : Z) : Prop :=
    (b = sent /\ exists x P', P = x :: P' /\ hh x = i)
    \/ (exists P1 y z P2, P = P1 ++ y :: z :: P2 /\ b = addr y /\ hh z = i).

  Record binv (P : list ent) (B : Z -> Z) : Prop := BINV {
    bi_just : forall i, 0 <= i < n -> B i <> 0 -> bjust P i (B i);
    bi_full : forall x, In x P -> B (hh x) <> 0
  }.

  Lemma hh_range : 0 < n -> forall x, 0 <= hh x < n.
  Proof using V n. intros Hn x. unfold hh, hmod. apply Z.mod_pos_bound. exact Hn. Qed.

  Lemma bjust_app : forall P Q i b, bjust P i b -> bjust (P ++ Q) i b.
  Proof using V n sent.
    intros P Q i b [[Hb (x & P' & -> & Hx)] | (P1 & y & z & P2 & -> & Hb & Hz)].
    - left. split; [exact Hb|]. exists x, (P' ++ Q). split; [reflexivity | exact Hx].
    - right. exists P1, y, z, (P2 ++ Q). rewrite <- app_assoc. cbn. split; [reflexivity|]. split; assumption.
  Qed.

  Lemma step_same : forall P x B,
    binv P B -> P <> [] -> hh x = hh (last P x) -> binv (P ++ [x]) B.
  Proof using V n sent.
    intros P x B [J F] Hne Hh. constructor.
    - intros i Hi Hb. apply bjust_app. exact (J i Hi Hb).
    - intros x0 Hin. apply in_app_iff in Hin. destruct Hin as [Hin | [<- | []]]; [exact (F x0 Hin)|].
      rewrite Hh. apply F. destruct P as [|p P']; [exfalso; exact (Hne eq_refl)|].
      assert (Hc : (p :: P') <> []) by discriminate. rewrite (app_removelast_last x Hc) at 2. apply in_app_iff. right. left. reflexivity.
  Qed.

  Lemma step_empty : forall P x B,
    binv P B -> P <> [] -> 0 < n -> addr (last P x) <> 0 ->
    binv (P ++ [x]) (fun i => if i =? hh x then addr (last P x) else B i).
  Proof using V n sent.
    intros P x B [J F] Hne Hn Ha. constructor.
    - intros i Hi Hb. destruct (Z.eqb_spec i (hh x)) as [-> | Hne'].
      + right. destruct P as [|p P']; [exfalso; exact (Hne eq_refl)|].
        exists (removelast (p :: P')), (last (p :: P') x), x, (@nil ent). split; [| split; reflexivity].
        assert (Hc : (p :: P') <> []) by discriminate. rewrite (app_removelast_last x Hc) at 1. rewrite <- app_assoc. reflexivity.
      + apply bjust_app. exact (J i Hi Hb).
    - intros x0 Hin. apply in_app_iff in Hin. destruct Hin as [Hin | [<- | []]].
      + destruct (Z.eqb_spec (hh x0) (hh x)) as [E|E]; [exact Ha | exact (F x0 Hin)].
      + rewrite Z.eqb_refl. exact Ha.
  Qed.

  Lemma step_front : forall P x B,
    binv P B -> 0 <= hh x < n -> B (hh x) = sent -> sent <> 0 ->
    (forall P1 y z P2, P = P1 ++ y :: z :: P2 -> addr y <> sent) ->
    binv (x :: P) B.
  Proof using V n sent.
    intros P x B [J F] Hr Hs Hsz Hnoty. constructor.
    - intros i Hi Hb. destruct (J i Hi Hb) as [[Hb' (w & P' & HP & Hw)] | (P1 & y & z & P2 & HP & Hb' & Hz)].
      +
        assert (Hi' : i = hh x).
        { destruct (J (hh x) Hr ltac:(rewrite Hs; exact Hsz)) as [[_ (w' & P'' & HP' & Hw')] | (P1 & y & z & P2 & HP' & Hb'' & Hz)].
          - rewrite HP in HP'. injection HP' as <- <-. congruence.
          - exfalso. rewrite Hs in Hb''. exact (Hnoty P1 y z P2 HP' (eq_sym Hb'')). }
        left. split; [exact Hb'|]. exists x, P. split; [reflexivity | symmetry; exact Hi'].
      + right. exists (x :: P1), y, z, P2. rewrite HP. split; [reflexivity|]. split; assumption.
    - intros x0 [<- | Hin]; [rewrite Hs; exact Hsz | exact (F x0 Hin)].
  Qed.

  Definition adj (P : list ent) (a b : ent) : Prop := exists Q1 Q2, P = Q1 ++ a :: b :: Q2.

  Lemma adj_cons : forall p P a b, adj P a b -> adj (p :: P) a b.
  Proof using V. intros p P a b (Q1 & Q2 & ->). exists (p :: Q1), Q2. reflexivity. Qed.

  Lemma adj_insert : forall P1 y z P2 x a b,
    adj (P1 ++ y :: z :: P2) a b -> a <> y -> adj (P1 ++ y :: x :: z :: P2) a b.
  Proof using V.
    induction P1 as [|p P1 IH]; intros y z P2 x a b (Q1 & Q2 & HP) Hay; cbn in *.
    - destruct Q1 as [|q Q1']; cbn in HP.
      + injection HP as <- <- <-. exfalso. exact (Hay eq_refl).
      + injection HP as <- HP. exists (y :: x :: Q1'), Q2. cbn. rewrite HP. reflexivity.
    - destruct Q1 as [|q Q1']; cbn in HP.
      + injection HP as <- HP. exists [], (tl (P1 ++ y :: x :: z :: P2)). cbn. f_equal.
        destruct P1 as [|p1 P1']; cbn in *; [injection HP as <- <-; reflexivity | injection HP as <- HP; reflexivity].
      + injection HP as <- HP. apply adj_cons. apply IH; [| exact Hay]. exists Q1', Q2. exact HP.
  Qed.

  Lemma adj_succ_unique : forall P a b a' b',
    NoDup (map addr P) -> adj P a b -> adj P a' b' -> addr a = addr a' -> a = a' /\ b = b'.
  Proof using V.
    induction P as [|p P IH]; intros a b a' b' Hnd (Q1 & Q2 & HP) (R1 & R2 & HR) Heq.
    - destruct Q1; discriminate HP.
    - cbn in Hnd. inversion Hnd as [| q l Hni Hnd']. subst.
      destruct Q1 as [|q1 Q1']; destruct R1 as [|r1 R1']; cbn in HP, HR.
      + injection HP as E1 E2. injection HR as E3 E4. subst. split; congruence.
      + injection HP as E1 E2. injection HR as E3 E4. subst. exfalso. apply Hni.
        rewrite Heq. apply in_map. rewrite E4. apply in_app_iff. right. left. reflexivity.
      + injection HP as E1 E2. injection HR as E3 E4. subst. exfalso. apply Hni.
        rewrite <- Heq. apply in_map. apply in_app_iff. right. left. reflexivity.
      + injection HP as E1 E2. injection HR as E3 E4. subst.
        apply (IH a b a' b' Hnd'); [exists Q1', Q2; reflexivity | exists R1', R2; exact E4 | exact Heq].
  Qed.

  Lemma step_splice : forall P1 y z P2 x B,
    binv (P1 ++ y :: z :: P2) B -> B (hh x) = addr y -> hh z = hh x -> addr y <> sent -> addr y <> 0 ->
    NoDup (map addr (P1 ++ y :: z :: P2)) ->
    binv (P1 ++ y :: x :: z :: P2) B.
  Proof using V n sent.
    intros P1 y z P2 x B [J F] Hb Hz Hys Hy0 Hnd. constructor.
    - intros i Hi Hbi. destruct (J i Hi Hbi) as [[Hb' (w & P' & HP & Hw)] | (Q1 & y' & z' & Q2 & HP & Hb' & Hz')].
      + left. split; [exact Hb'|]. destruct P1 as [|p P1'].
        * cbn in HP. injection HP as <- <-. exists y, (x :: z :: P2). split; [reflexivity | exact Hw].
        * cbn in HP. injection HP as <- <-. exists p, (P1' ++ y :: x :: z :: P2). split; [reflexivity | exact Hw].
      + right. destruct (Z.eq_dec (addr y') (addr y)) as [Heq | Hne].
        *
          destruct (adj_succ_unique _ y' z' y z Hnd ltac:(exists Q1, Q2; exact HP) ltac:(exists P1, P2; reflexivity) Heq) as [-> ->].
          exists P1, y, x, (z :: P2). split; [reflexivity|]. split; [exact Hb' | congruence].
        * destruct (adj_insert P1 y z P2 x y' z' ltac:(exists Q1, Q2; exact HP) ltac:(intros ->; exact (Hne eq_refl))) as (R1 & R2 & HR).
          exists R1, y', z', R2. split; [exact HR|]. split; assumption.
    - intros x0 Hin. apply in_app_iff in Hin. destruct Hin as [Hin | [<- | [<- | Hin]]].
      + apply F. apply in_app_iff. left. exact Hin.
      + apply F. apply in_app_iff. right. left. reflexivity.
      + rewrite Hb. exact Hy0.
      + apply F. apply in_app_iff. right. right. exact Hin.
  Qed.

  Lemma binv_start : forall x, sent <> 0 -> 0 < n ->
    binv [x] (fun i => if i =? hh x then sent else 0).
  Proof using V n sent.
    intros x Hs Hn. constructor.
    - intros i Hi Hb. destruct (Z.eqb_spec i (hh x)) as [->|Hne]; [| exfalso; exact (Hb eq_refl)].
      left. split; [reflexivity|]. exists x, (@nil ent). split; reflexivity.
    - intros x0 [<-|[]]. rewrite Z.eqb_refl. exact Hs.
  Qed.

  Lemma binv_weak : forall P B i, binv P B -> 0 <= i < n ->
    (forall P1 y z P2, P = P1 ++ y :: z :: P2 -> addr y <> sent) ->
    B i = 0 \/ In (B i) (map addr P) \/ (B i = sent /\ exists x P', P = x :: P' /\ hh x = i).
  Proof using V n sent.
    intros P B i [J F] Hi Hnoty. destruct (Z.eq_dec (B i) 0) as [Hz | Hnz]; [left; exact Hz | right].
    destruct (J i Hi Hnz) as [[Hb (w & P' & HP & Hw)] | (Q1 & y & z & Q2 & HP & Hb & Hz)].
    - right. split; [exact Hb|]. exists w, P'. split; assumption.
    - left. rewrite Hb, HP. apply in_map. apply in_app_iff. right. left. reflexivity.
  Qed.
End Model.
