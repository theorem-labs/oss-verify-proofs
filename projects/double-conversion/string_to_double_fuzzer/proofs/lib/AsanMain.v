(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgA.   (* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec ShapeAlg SpinAlg AgentLib Spec.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanImages AsanPlanImagesInit AsanInit AsanStartup AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive mtree : Type :=
| MLeaf (L : nat) (p : plan)                                                   (* [comment removed for export] *)
| MPre (L : nat) (p : plan) (HT : list (nat * (nat * acs))) (PT : list (nat * mtree))
                                                 (* [comment removed for export] *)
| MSplit (q : qty) (mid : Z) (le gt : mtree)                                  (* [comment removed for export] *)
| MCase (e : expr) (mid : Z) (le gt : mtree)                                  (* [comment removed for export] *)
| MClass (C' : class) (t : mtree)                                             (* [comment removed for export] *)
| MEmpty (L : nat)                                                            (* [comment removed for export] *)
| MPre0 (L : nat) (p : plan) (HT : list (nat * (nat * acs))) (PT : list (nat * mtree)).
                                                 (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tailsF_ok_of_list : forall KCm BFUELm FUELm ITm TL,
  tailsF_okb KCm BFUELm FUELm ITm TL = true -> tailsF_ok KCm BFUELm FUELm ITm (AP.tt_of_list TL).
Proof.
  intros KCm BFUELm FUELm ITm TL H t T p s Ht Hf. unfold AP.tt_of_list in Ht.
  pose proof (proj1 (forallb_forall _ _) H (T, p, s) (nth_error_In TL t Ht)) as X. cbn beta iota in X. rewrite Hf in X.
  destruct (tailf_check KCm BFUELm FUELm ITm T p) as [s'|]; [|discriminate]. apply andb_prop in X as [X1 X2].
  apply shape_eqb_eq in X1. subst s'. split; [reflexivity | exact X2].
Qed.
Lemma tailsF_ok_none : forall KCm BFUELm FUELm ITm, tailsF_ok KCm BFUELm FUELm ITm AP.TT_none.
Proof. intros KCm BFUELm FUELm ITm t T p s H. discriminate H. Qed.

Section MTreeInd.
  Variable P : mtree -> Prop.
  Hypothesis Hleaf : forall L p, P (MLeaf L p).
  Hypothesis Hpre : forall L p HT PT, (forall j t, In (j, t) PT -> P t) -> P (MPre L p HT PT).
  Hypothesis Hsplit : forall q mid le gt, P le -> P gt -> P (MSplit q mid le gt).
  Hypothesis Hcase : forall e mid le gt, P le -> P gt -> P (MCase e mid le gt).
  Hypothesis Hclass : forall C' t, P t -> P (MClass C' t).
  Hypothesis Hempty : forall L, P (MEmpty L).
  Hypothesis Hpre0 : forall L p HT PT, (forall j t, In (j, t) PT -> P t) -> P (MPre0 L p HT PT).
  Fixpoint mtree_ind2 (t : mtree) : P t :=
    match t with
    | MLeaf L p => Hleaf L p
    | MEmpty L => Hempty L
    | MCase e mid le gt => Hcase e mid le gt (mtree_ind2 le) (mtree_ind2 gt)
    | MClass C' t' => Hclass C' t' (mtree_ind2 t')
    | MPre L p HT PT =>
        Hpre L p HT PT
          ((fix go (PT : list (nat * mtree)) : forall j t, In (j, t) PT -> P t :=
              match PT return (forall j t, In (j, t) PT -> P t) with
              | [] => fun j t H => False_ind _ H
              | (j', t') :: PT' => fun j t H =>
                  match H with
                  | or_introl E => eq_ind (j', t') (fun jt => P (snd jt)) (mtree_ind2 t') (j, t) E
                  | or_intror H' => go PT' j t H'
                  end
              end) PT)
    | MSplit q mid le gt => Hsplit q mid le gt (mtree_ind2 le) (mtree_ind2 gt)
    | MPre0 L p HT PT =>
        Hpre0 L p HT PT
          ((fix go (PT : list (nat * mtree)) : forall j t, In (j, t) PT -> P t :=
              match PT return (forall j t, In (j, t) PT -> P t) with
              | [] => fun j t H => False_ind _ H
              | (j', t') :: PT' => fun j t H =>
                  match H with
                  | or_introl E => eq_ind (j', t') (fun jt => P (snd jt)) (mtree_ind2 t') (j, t) E
                  | or_intror H' => go PT' j t H'
                  end
              end) PT)
    end.
End MTreeInd.

(* [comment removed for export] *)
Inductive lshape : Type := LNode (L : nat) | LSplit (q : qty) (mid : Z) (a b : lshape).
Fixpoint lvl_shape (t : mtree) : lshape :=
  match t with
  | MLeaf L _ => LNode L
  | MPre L _ _ _ => LNode L
  | MSplit q mid a b => LSplit q mid (lvl_shape a) (lvl_shape b)
  | MCase _ _ a _ => lvl_shape a
  | MClass _ a => lvl_shape a
  | MEmpty L => LNode L
  | MPre0 L _ _ _ => LNode L
  end.
Fixpoint lshape_eqb (x y : lshape) : bool :=
  match x, y with
  | LNode a, LNode b => Nat.eqb a b
  | LSplit q m a b, LSplit q' m' a' b' => qty_eqb q q' && Z.eqb m m' && lshape_eqb a a' && lshape_eqb b b'
  | _, _ => false
  end.
Lemma lshape_eqb_eq : forall x y, lshape_eqb x y = true -> x = y.
Proof.
  induction x as [a|q m a IHa b IHb]; intros [a'|q' m' a' b'] H; cbn [lshape_eqb] in H; try discriminate.
  - apply Nat.eqb_eq in H. subst. reflexivity.
  - apply andb_prop in H as [H Hb]. apply andb_prop in H as [H Ha]. apply andb_prop in H as [Hq Hm].
    apply qty_eqb_eq in Hq. apply Z.eqb_eq in Hm. rewrite (IHa _ Ha), (IHb _ Hb). subst. reflexivity.
Qed.

Section MainCheck.
  (* [comment removed for export] *)
  Variable HS_asan : nat -> option acs.
  Variables KCm BFUELm FUELm : nat.
  Variable ITm : itab.
  Variable TTm : nat -> option (acs * plan * shape).   (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[local] Notation CHK C HS HL cs p :=
    (check ASEGS ITm ASAN NX0 AsanInit.LIMIT (XNm ASEGS ASAN NX0 RPN.RP_ASAN (iotab_of C)) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of C)) (XLm ASEGS ASAN NX0)
           HS HL TTm KCm BFUELm FUELm None cs p).

  (* [comment removed for export] *)
  Definition lv_shared (HT : list (nat * (nat * acs))) (j : nat) : bool :=
    match lv_of HT j with
    | Some L => existsb (fun e : nat * (nat * acs) => negb (Nat.eqb (fst e) j) && Nat.eqb (fst (snd e)) L) HT
    | None => false
    end.
  Definition sub_lo (L : nat) (HT : list (nat * (nat * acs))) (j Lj : nat) : nat := if lv_shared HT j then Lj else L.

  (* [comment removed for export] *)
  Definition mcover (HT : list (nat * (nat * acs))) (PT : list (nat * mtree)) : bool :=
    forallb (fun e : nat * (nat * acs) => match lookupT PT (fst e) with Some _ => true | None => false end) HT.

  (* [comment removed for export] *)
  Fixpoint mtree_ok (lo hi : nat) (ch : acs) (C : class) (t : mtree) : bool :=
    match t with
    | MLeaf L p =>
        Nat.leb lo L && Nat.leb L hi &&
        match CHK C HS_none HL_none (pay_start ch C) p with COk s => class_pay_ok L C s | CErr _ _ _ => false end
    | MPre L p HT PT =>
        Nat.leb lo L && Nat.leb L hi &&
        match CHK C (hs_of HT) (lv_of HT) (pay_start ch C) p with
        | COk s =>
            class_seg_ok (lv_of HT) L C s && mcover HT PT &&
            (fix forest (PT : list (nat * mtree)) : bool :=
               match PT with
               | [] => true
               | (j, t') :: PT' =>
                   match ht_of HT j with Some e => Nat.leb L (fst e) && mtree_ok (sub_lo L HT j (fst e)) (fst e) (snd e) C t' | None => true end && forest PT'
               end) PT
        | CErr _ _ _ => false
        end
    | MSplit q mid le gt => mtree_ok lo hi ch (C ++ [(q, QMIN, mid)]) le && mtree_ok lo hi ch (C ++ [(q, mid + 1, QMAX)]) gt
    | MCase e mid le gt =>
        lshape_eqb (lvl_shape le) (lvl_shape gt) &&
        mtree_ok lo hi (mcase_lo ch e mid) C le && mtree_ok lo hi (mcase_hi ch e mid) C gt
    | MClass C' t' => class_le C C' && mtree_ok lo hi ch C' t'
    | MEmpty L => Nat.leb lo L && Nat.leb L hi && class_empty C
    | MPre0 L p HT PT =>                                                     (* [comment removed for export] *)
        Nat.leb lo L && Nat.leb L hi && forallb (fun e : nat * (nat * acs) => Nat.eqb (fst (snd e)) L) HT &&
        match CHK [] (hs_of HT) (lv_of HT) ch p with
        | COk s =>
            all_holes s && mcover HT PT &&
            (fix forest (PT : list (nat * mtree)) : bool :=
               match PT with
               | [] => true
               | (j, t') :: PT' =>
                   match ht_of HT j with Some e => mtree_ok L L (snd e) C t' | None => true end && forest PT'
               end) PT
        | CErr _ _ _ => false
        end
    end.

  (* [comment removed for export] *)
  Fixpoint mforest_ok (L : nat) (HT : list (nat * (nat * acs))) (C : class) (PT : list (nat * mtree)) : bool :=
    match PT with
    | [] => true
    | (j, t') :: PT' => match ht_of HT j with Some e => Nat.leb L (fst e) && mtree_ok (sub_lo L HT j (fst e)) (fst e) (snd e) C t' | None => true end && mforest_ok L HT C PT'
    end.
  Lemma mtree_ok_MPre : forall lo hi ch C L p HT PT,
    mtree_ok lo hi ch C (MPre L p HT PT) =
    (Nat.leb lo L && Nat.leb L hi &&
     match CHK C (hs_of HT) (lv_of HT) (pay_start ch C) p with
     | COk s => class_seg_ok (lv_of HT) L C s && mcover HT PT && mforest_ok L HT C PT
     | CErr _ _ _ => false
     end)%bool.
  Proof.
    intros. cbn [mtree_ok]. destruct (check _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) as [s|]; [|reflexivity].
    f_equal. f_equal. induction PT as [|[j t'] PT IH]; [reflexivity|]. cbn [mforest_ok]. rewrite IH. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Fixpoint mforest0_ok (L : nat) (HT : list (nat * (nat * acs))) (C : class) (PT : list (nat * mtree)) : bool :=
    match PT with
    | [] => true
    | (j, t') :: PT' => match ht_of HT j with Some e => mtree_ok L L (snd e) C t' | None => true end && mforest0_ok L HT C PT'
    end.
  Lemma mtree_ok_MPre0 : forall lo hi ch C L p HT PT,
    mtree_ok lo hi ch C (MPre0 L p HT PT) =
    (Nat.leb lo L && Nat.leb L hi && forallb (fun e : nat * (nat * acs) => Nat.eqb (fst (snd e)) L) HT &&
     match CHK [] (hs_of HT) (lv_of HT) ch p with
     | COk s => all_holes s && mcover HT PT && mforest0_ok L HT C PT
     | CErr _ _ _ => false
     end)%bool.
  Proof.
    intros. cbn [mtree_ok]. destruct (check _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) as [s|]; [|reflexivity].
    f_equal. f_equal. induction PT as [|[j t'] PT IH]; [reflexivity|]. cbn [mforest0_ok]. rewrite IH. reflexivity.
  Qed.
  Lemma mforest0_ok_sound : forall L HT C PT j t e,
    mforest0_ok L HT C PT = true -> In (j, t) PT -> ht_of HT j = Some e -> mtree_ok L L (snd e) C t = true.
  Proof.
    intros L HT C PT j t e. induction PT as [|[j' t'] PT IH]; intros HF Hin He; [destruct Hin|].
    cbn [mforest0_ok] in HF. apply andb_prop in HF as [H1 H2].
    destruct Hin as [Heq|Hin]; [|exact (IH H2 Hin He)].
    injection Heq as -> ->. rewrite He in H1. exact H1.
  Qed.
  (* [comment removed for export] *)
  Lemma mtree_ok_seg0 : forall lo hi ch C L p HT PT s,
    (Nat.leb lo L && Nat.leb L hi)%bool = true ->
    forallb (fun e : nat * (nat * acs) => Nat.eqb (fst (snd e)) L) HT = true ->
    CHK [] (hs_of HT) (lv_of HT) ch p = COk s -> all_holes s = true ->
    mcover HT PT = true -> mforest0_ok L HT C PT = true ->
    mtree_ok lo hi ch C (MPre0 L p HT PT) = true.
  Proof. intros lo hi ch C L p HT PT s HL HLV H1 H2 H3 H4. rewrite mtree_ok_MPre0, H1, H2, H3, H4, HL, HLV. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma mtree_ok_seg00 : forall h C p HT PT s,
    forallb (fun e : nat * (nat * acs) => Nat.eqb (fst (snd e)) 0) HT = true ->
    pre0_check HS_asan KCm BFUELm FUELm ITm TTm h HT p = COk s -> all_holes s = true ->
    mcover HT PT = true -> mforest0_ok 0 HT C PT = true ->
    mtree_ok 0 0 (HSA HS_asan h) C (MPre0 0 p HT PT) = true.
  Proof. intros h C p HT PT s HLV H1 H2 H3 H4. unfold pre0_check in H1. exact (mtree_ok_seg0 0%nat 0%nat (HSA HS_asan h) C 0 p HT PT s eq_refl HLV H1 H2 H3 H4). Qed.

  (* [comment removed for export] *)
  Lemma mtree_ok_split : forall lo hi ch C q mid le gt,
    mtree_ok lo hi ch (C ++ [(q, QMIN, mid)]) le = true -> mtree_ok lo hi ch (C ++ [(q, mid + 1, QMAX)]) gt = true ->
    mtree_ok lo hi ch C (MSplit q mid le gt) = true.
  Proof. intros lo hi ch C q mid le gt H1 H2. cbn [mtree_ok]. rewrite H1, H2. reflexivity. Qed.

  Lemma mtree_ok_leaf : forall lo hi ch C L p s,
    (Nat.leb lo L && Nat.leb L hi)%bool = true ->
    CHK C HS_none HL_none (pay_start ch C) p = COk s -> class_pay_ok L C s = true -> mtree_ok lo hi ch C (MLeaf L p) = true.
  Proof. intros lo hi ch C L p s HL H1 H2. cbn [mtree_ok]. rewrite H1, H2, HL. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma mtree_ok_leaf0 : forall h C p s,
    main_check HS_asan KCm BFUELm FUELm ITm TTm h C p = COk s -> class_shape_ok C s = true -> mtree_ok 0 0 (HSA HS_asan h) C (MLeaf 0 p) = true.
  Proof. intros h C p s H1 H2. cbn [mtree_ok]. unfold main_check, main_start in H1. rewrite H1. exact H2. Qed.
  Lemma mtree_ok_leafP : forall lo hi ch C L p s,
    (Nat.leb lo L && Nat.leb L hi)%bool = true ->
    pay_check KCm BFUELm FUELm ITm TTm ch C p = COk s -> class_pay_ok L C s = true -> mtree_ok lo hi ch C (MLeaf L p) = true.
  Proof. intros lo hi ch C L p s HL H1 H2. eapply mtree_ok_leaf; eassumption. Qed.

  Lemma mtree_ok_seg : forall lo hi ch C L p HT PT s,
    (Nat.leb lo L && Nat.leb L hi)%bool = true ->
    CHK C (hs_of HT) (lv_of HT) (pay_start ch C) p = COk s -> class_seg_ok (lv_of HT) L C s = true ->
    mcover HT PT = true -> mforest_ok L HT C PT = true ->
    mtree_ok lo hi ch C (MPre L p HT PT) = true.
  Proof. intros lo hi ch C L p HT PT s HL H1 H2 H3 H4. rewrite mtree_ok_MPre, H1, H2, H3, H4, HL. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma mtree_ok_pre0 : forall hi h C L p HT PT s,
    Nat.leb L hi = true ->
    pre_check HS_asan KCm BFUELm FUELm ITm TTm h C HT p = COk s -> class_seg_ok (lv_of HT) L C s = true ->
    mcover HT PT = true -> mforest_ok L HT C PT = true ->
    mtree_ok 0 hi (HSA HS_asan h) C (MPre L p HT PT) = true.
  Proof. intros hi h C L p HT PT s HL H1 H2 H3 H4. unfold pre_check, main_start in H1. exact (mtree_ok_seg 0%nat hi (HSA HS_asan h) C L p HT PT s HL H1 H2 H3 H4). Qed.
  (* [comment removed for export] *)
  Lemma mtree_ok_segP : forall lo hi ch C L p HT PT s,
    (Nat.leb lo L && Nat.leb L hi)%bool = true ->
    seg_check KCm BFUELm FUELm ITm TTm ch C HT p = COk s -> class_seg_ok (lv_of HT) L C s = true ->
    mcover HT PT = true -> mforest_ok L HT C PT = true ->
    mtree_ok lo hi ch C (MPre L p HT PT) = true.
  Proof. intros. eapply mtree_ok_seg; eassumption. Qed.

  Lemma mtree_ok_case : forall lo hi ch C e mid le gt,
    lshape_eqb (lvl_shape le) (lvl_shape gt) = true ->
    mtree_ok lo hi (mcase_lo ch e mid) C le = true -> mtree_ok lo hi (mcase_hi ch e mid) C gt = true ->
    mtree_ok lo hi ch C (MCase e mid le gt) = true.
  Proof. intros lo hi ch C e mid le gt H0 H1 H2. cbn [mtree_ok]. rewrite H0, H1, H2. reflexivity. Qed.

  Lemma mtree_ok_class : forall lo hi ch C C' t,
    class_le C C' = true -> mtree_ok lo hi ch C' t = true -> mtree_ok lo hi ch C (MClass C' t) = true.
  Proof. intros lo hi ch C C' t H0 H1. cbn [mtree_ok]. rewrite H0, H1. reflexivity. Qed.

  Lemma mtree_ok_empty : forall lo hi ch C L,
    (Nat.leb lo L && Nat.leb L hi)%bool = true -> class_empty C = true -> mtree_ok lo hi ch C (MEmpty L) = true.
  Proof. intros lo hi ch C L HL H1. cbn [mtree_ok]. rewrite H1, HL. reflexivity. Qed.

  Lemma mforest_ok_nil : forall L HT C, mforest_ok L HT C [] = true.
  Proof. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma mforest_ok_cons : forall L HT C j t PT Lj chj,
    ht_of HT j = Some (Lj, chj) -> Nat.leb L Lj = true -> mtree_ok (sub_lo L HT j Lj) Lj chj C t = true -> mforest_ok L HT C PT = true ->
    mforest_ok L HT C ((j, t) :: PT) = true.
  Proof. intros L HT C j t PT Lj chj H1 HL H2 H3. cbn [mforest_ok]. rewrite H1. cbn [fst snd]. rewrite HL, H2. exact H3. Qed.
  (* [comment removed for export] *)
  Lemma mforest_ok_skip : forall L HT C j t PT,
    ht_of HT j = None -> mforest_ok L HT C PT = true -> mforest_ok L HT C ((j, t) :: PT) = true.
  Proof. intros L HT C j t PT H1 H2. cbn [mforest_ok]. rewrite H1. exact H2. Qed.

  Lemma mforest_ok_sound : forall L HT C PT j t e,
    mforest_ok L HT C PT = true -> In (j, t) PT -> ht_of HT j = Some e ->
    (L <= fst e)%nat /\ mtree_ok (sub_lo L HT j (fst e)) (fst e) (snd e) C t = true.
  Proof.
    intros L HT C PT j t e. induction PT as [|[j' t'] PT IH]; intros HF Hin He; [destruct Hin|].
    cbn [mforest_ok] in HF. apply andb_prop in HF as [H1 H2].
    destruct Hin as [Heq|Hin]; [|exact (IH H2 Hin He)].
    injection Heq as -> ->. rewrite He in H1. apply andb_prop in H1 as [HL H1]. apply Nat.leb_le in HL. split; [exact HL | exact H1].
  Qed.
  Lemma lv_shared_eq : forall HT h1 h2 L,
    lv_of HT h1 = Some L -> lv_of HT h2 = Some L -> h1 <> h2 -> lv_shared HT h1 = true.
  Proof.
    intros HT h1 h2 L H1 H2 Hne. unfold lv_shared. rewrite H1. apply existsb_exists.
    unfold lv_of in H2. destruct (ht_of HT h2) as [[L2 ch2]|] eqn:He; [|discriminate]. cbn [fst] in H2. injection H2 as ->.
    exists (h2, (L, ch2)). split; [exact (ht_of_In _ _ _ He)|]. cbn [fst snd].
    rewrite Nat.eqb_refl. destruct (Nat.eqb_spec h2 h1); [congruence | reflexivity].
  Qed.
  Lemma mcover_sound : forall HT PT j e, mcover HT PT = true -> ht_of HT j = Some e -> exists t, lookupT PT j = Some t.
  Proof.
    intros HT PT j e HC He. unfold mcover in HC. rewrite forallb_forall in HC.
    specialize (HC (j, e) (ht_of_In _ _ _ He)). cbn [fst] in HC. destruct (lookupT PT j) as [t|]; [exists t; reflexivity | discriminate].
  Qed.
End MainCheck.

Lemma pc_set_kn : forall cs k, pc (set_kn cs k) = pc cs.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Main.
  (* [comment removed for export] *)
  Variable LINV : (word -> option byte) -> Prop.
  Hypothesis HLINV : LINV_STMT LINV.
  Hypothesis XALL : XALL_STMT LINV.
  Hypothesis XRP : XRP_STMT LINV.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid : word.
  Variable hw : word.               (* [comment removed for export] *)
  Variables nofile sigmask : word.
  Variable abt : bool.  (* [comment removed for export] *)  (* [comment removed for export] *)
  Variable groups : list word.
  Variable net : NetQueue.
  Variable ur : InputStream.   
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.   (* [comment removed for export] *)

  #[local] Notation c := (content_of argv fs).
  #[local] Notation SINV0' := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation SINV := (SINVm APH sp rdraw brk0 argv envp uid hw (content_of argv fs)).
  #[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).
  #[local] Notation LIM := AsanInit.LIMIT.

  (* [comment removed for export] *)
  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS IT0.
  Variable HS_asan : nat -> option acs.
  Variable startup_plan : plan.
  Variable startup_shape : shape.
  Variables KC0 BFUEL FUEL : nat.
  Variable TT0 : nat -> option (acs * plan * shape).   (* [comment removed for export] *)
  Hypothesis startup_cert :
    check ASEGS IT0 ASAN NX0 LIM (RPN.xn ASEGS ASAN NX0 RPN.RP_ASAN) XE0 XB0 XL0 HS_asan HL0 TT0 KC0 BFUEL FUEL None asan_init startup_plan = COk startup_shape.
  Hypothesis TT0_ok : AP.tails_ok0 ASEGS IT0 ASAN NX0 LIM TT0 KC0.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis startup_all_holes : all_holes startup_shape = true.
  (* [comment removed for export] *)
  Hypothesis HSA_noblob : forall h ch, HS_asan h = Some ch -> acs_noblob ch = true.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variables KCm BFUELm FUELm : nat.
  Variable ITm : itab.
  Variable TTm : nat -> option (acs * plan * shape).   (* [comment removed for export] *)
  Hypothesis ITm_ok : itab_sound ASEGS ITm.
  Hypothesis TTm_ok : tails_all_ok KCm BFUELm FUELm ITm TTm.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis Msys : forall {fx : FPState} y, sys_stmt ASEGS ASAN NX0 LIM SINV argH LINV fs y.
  Hypothesis Mbrk2 : forall {fx : FPState}, brk2_stmt ASEGS ASAN NX0 LIM SINV argH LINV fs.
  Hypothesis Mmmap2 : forall {fx : FPState}, mm2_stmt ASEGS ASAN NX0 LIM SINV argH LINV fs (node_mmap2 ASAN NX0 LIM).
  Hypothesis Mmmapin : forall {fx : FPState} (hole : bool), mm3_stmt ASEGS ASAN NX0 LIM SINV argH LINV fs (node_mmapin ASAN LIM hole).
  Hypothesis Mmprotect2 : forall {fx : FPState}, mm2_stmt ASEGS ASAN NX0 LIM SINV argH LINV fs (node_mprotect2 ASAN LIM).
  Hypothesis Mexit : forall {fx : FPState}, exit_stmt ASEGS ASAN LIM SINV argH LINV fs.
  Hypothesis Mx : forall {fx : FPState} x, x_stmt ASEGS ASAN NX0 LIM SINV argH LINV fs x.
  (* [comment removed for export] *)
  Hypothesis Mxn : forall {fx : FPState} T, H_class_prop T argv fs SINV -> ext_stmt ASEGS ASAN NX0 LIM (XNm ASEGS ASAN NX0 RPN.RP_ASAN T) SINV argH LINV fs.
  Hypothesis Mxe : forall {fx : FPState}, emit_stmt ASEGS ASAN NX0 LIM (XEm ASEGS ASAN NX0) SINV argH LINV fs.
  Hypothesis Mxb : forall {fx : FPState} T, H_class_prop T argv fs SINV -> ext2_stmt ASEGS ASAN NX0 LIM (XBm ASEGS NX0 T) SINV argH LINV fs.
  (* [comment removed for export] *)
  Hypothesis Mlib : lib_stmt ASEGS ASAN NX0 LIM (XLm ASEGS ASAN NX0) SINV argH LINV fs.
  (* [comment removed for export] *)
  Hypothesis VF : forall E M, SINV E M -> know_ok ASEGS E M (vfacts (variant_of c)).

  Lemma SINVm_frame' : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Proof. intros. eapply SINVm_frame; eassumption. Qed.
  Lemma SINVm_agree' : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
  Proof. intros. eapply SINVm_agree; eassumption. Qed.
  Lemma SINVm_blob : forall E M, SINV E M -> forall j, eb E (8 + j)%nat = chunk j (content_of argv fs).
  Proof. intros E M (_ & _ & _ & H) j. apply H. Qed.

  Lemma HOLES0_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES0 h E fs' = HOLES0 h E' fs'.
  Proof. reflexivity. Qed.
  Lemma HOLES0_nil : forall h E fs', HOLES0 h E fs' [].
  Proof. intros. reflexivity. Qed.
  Lemma HS_none_sound : forall (fx : FPState), frm_zero fx -> holes_stmt ASEGS ASAN LIM HS_none SINV argH LINV HOLES0 fs.
  Proof. intros fx _ h ch H. discriminate H. Qed.
  Lemma HOLES0_lv : forall h1 h2 L E fs', HL_none h1 = Some L -> HL_none h2 = Some L -> HOLES0 h1 E fs' = HOLES0 h2 E fs'.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Fixpoint lshape_lvl (x : lshape) : nat :=
    match x with
    | LNode L => L
    | LSplit q mid a b => if qval q argv fs <=? mid then lshape_lvl a else lshape_lvl b
    end.
  Definition mtree_lvl (t : mtree) : nat := lshape_lvl (lvl_shape t).
  Lemma mtree_lvl_split : forall q mid le gt,
    mtree_lvl (MSplit q mid le gt) = if qval q argv fs <=? mid then mtree_lvl le else mtree_lvl gt.
  Proof. reflexivity. Qed.

  #[local] Notation CHK C HS HL cs p :=
    (check ASEGS ITm ASAN NX0 LIM (XNm ASEGS ASAN NX0 RPN.RP_ASAN (iotab_of C)) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of C)) (XLm ASEGS ASAN NX0)
           HS HL TTm KCm BFUELm FUELm None cs p).
  #[local] Notation AH := (argH0_high APH sp rdraw argv envp uid hw Hsp Hva).
  #[local] Notation AA := (argH0_agree APH sp rdraw argv envp uid hw).

  (* [comment removed for export] *)
  Lemma main_check_sound_tt : forall TTx (TTx_ok : AP.tails_ok ASEGS ITm ASAN NX0 LIM TTx KCm)
      (TTx_full : forall (fx : FPState), frm_zero fx -> forall t T p s, TTx t = Some (T, p, s) -> AP.is_full p = true ->
         forall E R FULL model D, cs_ok ASEGS ASAN LIM SINV argH LINV fs E T R FULL model -> D [] ->
           srealizes ASEGS (cfg_of ASEGS R (pc T) FULL model) (sd HOLES0 D E (m_fs model) s) /\ shape_closed s = true) C HS HL HOLES,
    H_class_prop (iotab_of C) argv fs SINV ->
    (forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs') -> (forall h E fs', HOLES h E fs' []) ->
    (forall h1 h2 L E fs', HL h1 = Some L -> HL h2 = Some L -> HOLES h1 E fs' = HOLES h2 E fs') ->
    (forall (fx : FPState), frm_zero fx -> holes_stmt ASEGS ASAN LIM HS SINV argH LINV HOLES fs) ->
    forall p cs s,
      check ASEGS ITm ASAN NX0 LIM (XNm ASEGS ASAN NX0 RPN.RP_ASAN (iotab_of C)) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of C)) (XLm ASEGS ASAN NX0)
            HS HL TTx KCm BFUELm FUELm None cs p = COk s ->
    forall (fx : FPState), frm_zero fx ->
    forall E R FULL model, cs_ok ASEGS ASAN LIM SINV argH LINV fs E cs R FULL model ->
      srealizes ASEGS (cfg_of ASEGS R (pc cs) FULL model) (sd HOLES t_nil E (m_fs model) s).
  Proof.
    intros TTx TTx_ok TTx_full C HS HL HOLES HCL HOa HOn HOlv HOs p cs s Hchk fx FRM E R FULL model HC.
    exact (check_sound ASEGS ITm ITm_ok ASAN NX0 LIM HS HL
                  (XNm ASEGS ASAN NX0 RPN.RP_ASAN (iotab_of C)) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of C)) (XLm ASEGS ASAN NX0)
                  asan_wx asan_in_hull asan_hull_ok asan_shadow_ok SINV argH AH AA (Nat.le_refl NX0) SINVm_frame' SINVm_agree' LINV (proj2 HLINV)
                  HOLES HOa HOn HOlv fs KCm TTx TTx_ok
                  (@Msys) (@Mbrk2) (@Mmmap2) (@Mmmapin) (@Mmprotect2) (@Mexit) (@Mx)
                  (fun fx => node_join_sound (fx:=fx) ASEGS ASAN NX0 LIM SINV argH LINV fs)
                  (AsanNodesMmLib.node_zones_sound ASEGS ASAN LIM SINV argH LINV fs asan_res_len asan_hull_ok asan_res_chain)   (* [comment removed for export] *)
                  (AsanNodesMmLib.node_zonehull_sound ASEGS ASAN LIM SINV argH LINV fs asan_res_len asan_hull_ok asan_res_chain)   (* [comment removed for export] *)
                  (fun fx => @Mxn fx _ HCL) (@Mxe) (fun fx => @Mxb fx _ HCL) Mlib HOs
                  (fun fx1 FRM1 t T p1 s1 Ht Hif E1 R1 FULL1 model1 D1 HC1 HD1 =>
                     eq_ind _ (fun X => srealizes ASEGS (cfg_of ASEGS R1 (pc T) FULL1 model1) X)
                            (proj1 (TTx_full fx1 FRM1 t T p1 s1 Ht Hif E1 R1 FULL1 model1 D1 HC1 HD1)) _
                            (sd_closed HOLES0 HOLES D1 D1 E1 (m_fs model1) s1 (proj2 (TTx_full fx1 FRM1 t T p1 s1 Ht Hif E1 R1 FULL1 model1 D1 HC1 HD1))))   (* [comment removed for export] *)
                  FUELm BFUELm None p cs s Hchk fx FRM E R FULL model t_nil HC I eq_refl).
  Qed.

  (* [comment removed for export] *)
  Lemma TTm_fulls : forall (fx : FPState), frm_zero fx -> forall t T p s, TTm t = Some (T, p, s) -> AP.is_full p = true ->
    forall E R FULL model D, cs_ok ASEGS ASAN LIM SINV argH LINV fs E T R FULL model -> D [] ->
      srealizes ASEGS (cfg_of ASEGS R (pc T) FULL model) (sd HOLES0 D E (m_fs model) s) /\ shape_closed s = true.
  Proof.
    intros fx FRM t T p s Ht Hif E R FULL model D HC HD.
    destruct (proj2 TTm_ok t T p s Ht Hif) as [Hchk Hcl]. split; [|exact Hcl].
    pose proof (in_class_H_class APH sp rdraw argv envp fs uid hw Hva Hfit [] SINV eq_refl SINVm_blob) as HCL.
    unfold tailf_check in Hchk.
    pose proof (main_check_sound_tt AP.TT_none (proj1 (AP.tails_ok_none ASEGS ITm ASAN NX0 LIM KCm))
                  (fun fx1 _ t1 T1 p1 s1 (H1 : AP.TT_none t1 = Some (T1, p1, s1)) => match (eq_ind None (fun o => match o with None => True | Some _ => False end) I _ H1) with end)
                  [] HS_none HL_none HOLES0 HCL HOLES0_agree HOLES0_nil HOLES0_lv HS_none_sound p T s Hchk fx FRM E R FULL model HC) as RZ.
    rewrite (sd_closed HOLES0 HOLES0 D t_nil E (m_fs model) s Hcl). exact RZ.
  Qed.
  Lemma main_check_sound : forall C HS HL HOLES,
    H_class_prop (iotab_of C) argv fs SINV ->
    (forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs') -> (forall h E fs', HOLES h E fs' []) ->
    (forall h1 h2 L E fs', HL h1 = Some L -> HL h2 = Some L -> HOLES h1 E fs' = HOLES h2 E fs') ->
    (forall (fx : FPState), frm_zero fx -> holes_stmt ASEGS ASAN LIM HS SINV argH LINV HOLES fs) ->
    forall p cs s, CHK C HS HL cs p = COk s ->
    forall (fx : FPState), frm_zero fx ->
    forall E R FULL model, cs_ok ASEGS ASAN LIM SINV argH LINV fs E cs R FULL model ->
      srealizes ASEGS (cfg_of ASEGS R (pc cs) FULL model) (sd HOLES t_nil E (m_fs model) s).
  Proof. exact (main_check_sound_tt TTm (proj1 TTm_ok) TTm_fulls). Qed.

  (* [comment removed for export] *)
  Lemma cs_ok_main_facts : forall E cs R FULL model,
    cs_ok ASEGS ASAN LIM SINV argH LINV fs E cs R FULL model ->
    (forall n, (n < 8)%nat -> ev E n = ev (E0 APH sp rdraw brk0 argv envp uid hw) n)
    /\ eb E 1%nat = nth 0 argv [] /\ eb E 2%nat = nth 1 argv [] /\ m_fs model = fs
    /\ know_ok ASEGS E FULL (vfacts (variant_of c)).
  Proof.
    intros E cs R FULL model HC.
    pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC) as HS. pose proof HS as HS'.
    destruct HS as [[Hev _] [HB1 [HB2 _]]].
    refine (conj _ (conj HB1 (conj HB2 (conj (co_fs _ _ _ _ _ _ _ _ _ _ _ _ HC) (VF _ _ HS'))))).
    intros n Hn. apply Hev. unfold NX0. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cs_ok_pay_start : forall C E cs R FULL model,
    in_class C argv fs = true ->
    cs_ok ASEGS ASAN LIM SINV argH LINV fs E cs R FULL model ->
    cs_ok ASEGS ASAN LIM SINV argH LINV fs E (pay_start cs C) R FULL model.
  Proof.
    intros C E cs R FULL model HC HCS. unfold pay_start. apply cs_ok_set_kn; [exact HCS|]. apply Forall_app. split.
    - eapply facts_of_class_sound; [eassumption.. | ]. apply (cs_ok_main_facts E cs R FULL model HCS).
    - exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS).
  Qed.

  Lemma in_class_split : forall C q mid,
    in_class C argv fs = true ->
    if qval q argv fs <=? mid then in_class (C ++ [(q, QMIN, mid)]) argv fs = true
    else in_class (C ++ [(q, mid + 1, QMAX)]) argv fs = true.
  Proof.
    intros C q mid HC. pose proof (qval_bounds APH sp rdraw argv envp fs uid hw Hva Hfit q) as Hq.
    destruct (Z.leb_spec (qval q argv fs) mid); rewrite in_class_app, HC; cbn;
      (apply andb_true_intro; split; [|reflexivity]); apply andb_true_intro; split; apply Z.leb_le; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cbounds_entry : forall C q lo hi acc,
    In (q, lo, hi) C ->
    lo <= fst (fold_left (fun acc (t : qty * Z * Z) => let '(q', lo', hi') := t in
                           if qty_eqb q q' then (Z.max (fst acc) lo', Z.min (snd acc) hi') else acc) C acc)
    /\ snd (fold_left (fun acc (t : qty * Z * Z) => let '(q', lo', hi') := t in
                         if qty_eqb q q' then (Z.max (fst acc) lo', Z.min (snd acc) hi') else acc) C acc) <= hi.
  Proof.
    assert (MONO : forall C q acc,
      fst acc <= fst (fold_left (fun acc (t : qty * Z * Z) => let '(q', lo', hi') := t in
                                  if qty_eqb q q' then (Z.max (fst acc) lo', Z.min (snd acc) hi') else acc) C acc)
      /\ snd (fold_left (fun acc (t : qty * Z * Z) => let '(q', lo', hi') := t in
                           if qty_eqb q q' then (Z.max (fst acc) lo', Z.min (snd acc) hi') else acc) C acc) <= snd acc).
    { intros C q. induction C as [|[[q' lo'] hi'] C IH]; intros acc; cbn [fold_left]; [lia|].
      destruct (qty_eqb q q'); [|apply IH]. specialize (IH (Z.max (fst acc) lo', Z.min (snd acc) hi')). cbn [fst snd] in IH. lia. }
    intros C q lo hi. induction C as [|[[q' lo'] hi'] C IH]; intros acc Hin; [destruct Hin|].
    cbn [fold_left]. destruct Hin as [E|Hin]; [|apply IH; exact Hin].
    injection E as -> -> ->. replace (qty_eqb q q) with true by (symmetry; apply qty_eqb_eq; reflexivity).
    specialize (MONO C q (Z.max (fst acc) lo, Z.min (snd acc) hi)). cbn [fst snd] in MONO. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma qval_qrange : forall q, fst (qrange q) <= qval q argv fs <= snd (qrange q).
  Proof.
    pose proof (argc_range argv Hva). pose proof (L0_range' argv Hva). pose proof (L1_range' APH sp rdraw argv envp uid hw Hva). pose proof (qlook_range sp argv envp fs Hva Hfit).
    pose proof (cfglen_range (content_of argv fs)). pose proof (flen_range (content_of argv fs)).
    pose proof (bz_range 2 (content_of argv fs)). pose proof (bz_range 1 (content_of argv fs)).
    pose proof (Z.mod_pos_bound (bz 2 (content_of argv fs)) 4 ltac:(lia)).
    assert (0 <= bz 1 (content_of argv fs) / 128 <= 1).
    { split; [apply Z.div_pos; lia |]. assert (bz 1 (content_of argv fs) / 128 < 2) by (apply Z.div_lt_upper_bound; lia). lia. }
    pose proof (room_eq (content_of argv fs)). pose proof (cmod_eq (content_of argv fs)).
    intros q; destruct q; cbn [qval qrange fst snd]; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma qbounds_sound : forall C q, in_class C argv fs = true -> fst (qbounds C q) <= qval q argv fs <= snd (qbounds C q).
  Proof.
    intros C q HC. unfold qbounds, clamp. cbn [fst snd].
    pose proof (cbounds_sound C q argv fs HC (qval_bounds APH sp rdraw argv envp fs uid hw Hva Hfit q)). pose proof (qval_qrange q). lia.
  Qed.
  Lemma in_class_nonempty : forall C, in_class C argv fs = true -> class_empty C = false.
  Proof.
    intros C HC. apply Bool.not_true_is_false. unfold class_empty. intros H.
    apply Bool.orb_prop in H as [H|H]; [apply Bool.orb_prop in H as [H|H]|].
    - rewrite existsb_exists in H. destruct H as (q & _ & H). apply Z.ltb_lt in H. pose proof (qbounds_sound C q HC). lia.
    - apply Z.ltb_lt in H. pose proof (qbounds_sound C QFlen HC). pose proof (qbounds_sound C QCfgLen HC). pose proof (qbounds_sound C QRoom HC).
      cbn [qval] in *. pose proof (room_eq (content_of argv fs)). unfold cfglen in *. lia.
    - apply Z.ltb_lt in H. pose proof (qbounds_sound C QFlen HC). pose proof (qbounds_sound C QCfgLen HC). pose proof (qbounds_sound C QRoom HC).
      cbn [qval] in *. pose proof (room_eq (content_of argv fs)). unfold cfglen in *. lia.
  Qed.
  Lemma in_class_weaken : forall C C', class_le C C' = true -> in_class C argv fs = true -> in_class C' argv fs = true.
  Proof.
    intros C C' HLE HC. unfold in_class. apply forallb_forall. intros [[q lo] hi] Hin.
    pose proof (qbounds_sound C q HC) as B.
    unfold class_le in HLE. rewrite forallb_forall in HLE.
    assert (Hq : In q all_qty) by (destruct q; cbn; tauto).
    specialize (HLE q Hq). cbn beta in HLE. apply Bool.orb_prop in HLE as [H0|HLE]; [apply Z.ltb_lt in H0; lia|].
    apply andb_prop in HLE as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof (cbounds_entry C' q lo hi (QMIN, QMAX) Hin) as E. unfold cbounds in H1, H2.
    apply andb_true_intro; split; apply Z.leb_le; lia.
  Qed.

  (* [comment removed for export] *)
  Theorem mtree_sound : forall t lo hi ch C,
    mtree_ok KCm BFUELm FUELm ITm TTm lo hi ch C t = true -> in_class C argv fs = true ->
    (lo <= mtree_lvl t)%nat /\ (mtree_lvl t <= hi)%nat /\
    forall (fx : FPState), frm_zero fx ->
    forall E R FULL model,
      cs_ok ASEGS ASAN LIM SINV argH LINV fs E ch R FULL model ->
      srealizes ASEGS (cfg_of ASEGS R (pc ch) FULL model) (t_res (mtree_lvl t) argv fs).
  Proof.
    induction t as [L p | L p HT PT IH | q mid le gt IHle IHgt | e mid le gt IHle IHgt | C' t IHt | L | L p HT PT IH] using mtree_ind2; intros lo hi ch C HT0 HC.
    - (* [comment removed for export] *)
      cbn [mtree_ok] in HT0. apply andb_prop in HT0 as [HL HT0]. apply andb_prop in HL as [HL1 HL2].
      apply Nat.leb_le in HL1. apply Nat.leb_le in HL2. cbn [mtree_lvl lvl_shape lshape_lvl]. split; [exact HL1|]. split; [exact HL2|].
      intros fx FRM E R FULL model HCS.
      destruct (check _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) as [s| ] eqn:Hchk; [|discriminate].
      pose proof (cs_ok_pay_start C E ch R FULL model HC HCS) as HC2.
      destruct (cs_ok_main_facts E _ R FULL model HC2) as (Hev & HB1 & HB2 & Hfs & HVF).
      pose proof (in_class_H_class APH sp rdraw argv envp fs uid hw Hva Hfit C SINV HC SINVm_blob) as HCL.
      pose proof (main_check_sound C HS_none HL_none HOLES0 HCL HOLES0_agree HOLES0_nil HOLES0_lv HS_none_sound p _ s Hchk fx FRM E R FULL model HC2) as RZ.
      rewrite Hfs in RZ. unfold pay_start in RZ. rewrite pc_set_kn in RZ.
      eapply srz_conseq; [exact RZ|].
      exact (class_pay_sound APH sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit ASEGS L C s E _ HOLES0 t_nil HC HT0 Hev HB1 HB2 HVF).
    - (* [comment removed for export] *)
      rewrite mtree_ok_MPre in HT0. apply andb_prop in HT0 as [HL HT0]. apply andb_prop in HL as [HL1 HL2].
      apply Nat.leb_le in HL1. apply Nat.leb_le in HL2. cbn [mtree_lvl lvl_shape lshape_lvl]. split; [exact HL1|]. split; [exact HL2|].
      intros fx FRM E R FULL model HCS.
      destruct (check _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) as [s| ] eqn:Hchk; [|discriminate].
      apply andb_prop in HT0 as [HT0 HF]. apply andb_prop in HT0 as [Hseg Hcov].
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      set (HOLESL := fun (h : nat) (E' : env) (fs' : Fs.Fs) =>
                       if lv_shared HT h then match lv_of HT h with Some Lj => t_res Lj argv fs' | None => t_nil end
                       else match lookupT PT h with Some t' => t_res (mtree_lvl t') argv fs' | None => t_nil end).
      assert (HLa : forall h E1 E2 fs', env_agree NX0 E1 E2 -> HOLESL h E1 fs' = HOLESL h E2 fs') by reflexivity.
      assert (HLn : forall h E1 fs', HOLESL h E1 fs' []).
      { intros h E1 fs'. unfold HOLESL. destruct (lv_shared HT h); [destruct (lv_of HT h); [apply t_res_nil | reflexivity]|].
        destruct (lookupT PT h); [apply t_res_nil | reflexivity]. }
      assert (HLlv : forall h1 h2 L0 E1 fs', lv_of HT h1 = Some L0 -> lv_of HT h2 = Some L0 -> HOLESL h1 E1 fs' = HOLESL h2 E1 fs').
      { intros h1 h2 L0 E1 fs' Hh1 Hh2. destruct (Nat.eq_dec h1 h2) as [->|Hne]; [reflexivity|].
        unfold HOLESL. rewrite (lv_shared_eq HT h1 h2 L0 Hh1 Hh2 Hne), (lv_shared_eq HT h2 h1 L0 Hh2 Hh1 ltac:(congruence)), Hh1, Hh2. reflexivity. }
      assert (HLs : forall (fx1 : FPState), frm_zero fx1 -> holes_stmt ASEGS ASAN LIM (hs_of HT) SINV argH LINV HOLESL fs).
      { intros fx1 FRM1 j chj Hj E1 R1 FULL1 model1 HC1.
        unfold hs_of in Hj. destruct (ht_of HT j) as [[Lj chj']|] eqn:He; [|discriminate]. cbn [snd] in Hj. injection Hj as ->.
        destruct (mcover_sound HT PT j _ Hcov He) as (t' & Ht').
        pose proof (mforest_ok_sound KCm BFUELm FUELm ITm TTm L HT C PT j t' _ HF (lookupT_In _ _ _ Ht') He) as [HLj Hok]. cbn [fst snd] in HLj, Hok.
        destruct (IH j t' (lookupT_In _ _ _ Ht') _ Lj chj C Hok HC) as (Hlo & Hhi & RZ).
        unfold HOLESL. rewrite (co_fs _ _ _ _ _ _ _ _ _ _ _ _ HC1).
        unfold sub_lo in Hlo. destruct (lv_shared HT j).
        - unfold lv_of. rewrite He. cbn [fst]. replace Lj with (mtree_lvl t') by lia. exact (RZ fx1 FRM1 E1 R1 FULL1 model1 HC1).
        - rewrite Ht'. exact (RZ fx1 FRM1 E1 R1 FULL1 model1 HC1). }
      pose proof (cs_ok_pay_start C E ch R FULL model HC HCS) as HC2.
      destruct (cs_ok_main_facts E _ R FULL model HC2) as (Hev & HB1 & HB2 & Hfs & HVF).
      pose proof (in_class_H_class APH sp rdraw argv envp fs uid hw Hva Hfit C SINV HC SINVm_blob) as HCL.
      pose proof (main_check_sound C (hs_of HT) (lv_of HT) HOLESL HCL HLa HLn HLlv HLs p _ s Hchk fx FRM E R FULL model HC2) as RZ.
      rewrite Hfs in RZ. unfold pay_start in RZ. rewrite pc_set_kn in RZ.
      eapply srz_conseq; [exact RZ|].
      eapply (class_seg_sound APH sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit ASEGS (lv_of HT) L C s E _ HOLESL t_nil HC Hseg Hev HB1 HB2 HVF).
      (* [comment removed for export] *)
      intros j Lj Hlv. pose proof Hlv as Hlv0. unfold lv_of in Hlv. destruct (ht_of HT j) as [[Lj' chj]|] eqn:He; [|discriminate]. cbn [fst] in Hlv. injection Hlv as ->.
      destruct (mcover_sound HT PT j _ Hcov He) as (t' & Ht').
      pose proof (mforest_ok_sound KCm BFUELm FUELm ITm TTm L HT C PT j t' _ HF (lookupT_In _ _ _ Ht') He) as [HLj Hok]. cbn [fst snd] in HLj, Hok.
      destruct (IH j t' (lookupT_In _ _ _ Ht') _ Lj chj C Hok HC) as (H1 & H2 & _).
      unfold HOLESL, sub_lo in *. destruct (lv_shared HT j).
      + exists Lj. split; [exact HLj|]. split; [lia|]. rewrite Hlv0. apply t_eq_refl.
      + exists (mtree_lvl t'). split; [lia|]. split; [exact H2|]. rewrite Ht'. apply t_eq_refl.
    - (* [comment removed for export] *)
      cbn [mtree_ok] in HT0. apply andb_prop in HT0 as [H1 H2]. rewrite mtree_lvl_split.
      pose proof (in_class_split C q mid HC) as HC'.
      destruct (qval q argv fs <=? mid); [exact (IHle lo hi ch _ H1 HC') | exact (IHgt lo hi ch _ H2 HC')].
    - (* [comment removed for export] *)
      cbn [mtree_ok] in HT0. apply andb_prop in HT0 as [HT0 H2]. apply andb_prop in HT0 as [Hsh H1].
      apply lshape_eqb_eq in Hsh.
      assert (Llo : mtree_lvl (MCase e mid le gt) = mtree_lvl le) by reflexivity.
      assert (Lhi : mtree_lvl (MCase e mid le gt) = mtree_lvl gt) by (unfold mtree_lvl; cbn [lvl_shape]; rewrite Hsh; reflexivity).
      destruct (IHle lo hi _ C H1 HC) as (A1 & A2 & RZle). destruct (IHgt lo hi _ C H2 HC) as (_ & _ & RZgt).
      rewrite Llo. split; [exact A1|]. split; [exact A2|].
      intros fx FRM E R FULL model HCS.
      pose proof (u64_range (edenot E e)) as He. pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) as HK.
      assert (HB : fst (ebounds (kn ch) e) <= uE E e <= snd (ebounds (kn ch) e)).
      { unfold ebounds. destruct (erange (kn ch) e) as [[blo bhi]|] eqn:Her; cbn [fst snd].
        - exact (erange_sound ASEGS E _ (kn ch) e blo bhi HK Her).
        - unfold uE, two64. lia. }
      destruct (Z.leb_spec (uE E e) mid) as [Hm|Hm].
      + apply (RZle fx FRM E R FULL model). unfold mcase_lo. apply cs_ok_set_kn; [exact HCS|].
        constructor; [cbn [kentry_ok]; unfold uE in *; lia | exact HK].
      + rewrite <- Llo, Lhi. apply (RZgt fx FRM E R FULL model). unfold mcase_hi. apply cs_ok_set_kn; [exact HCS|].
        constructor; [cbn [kentry_ok]; unfold uE, two64 in *; lia | exact HK].
    - (* [comment removed for export] *)
      cbn [mtree_ok] in HT0. apply andb_prop in HT0 as [HLE H1].
      exact (IHt lo hi ch C' H1 (in_class_weaken C C' HLE HC)).
    - (* [comment removed for export] *)
      cbn [mtree_ok] in HT0. apply andb_prop in HT0 as [_ HE]. rewrite (in_class_nonempty C HC) in HE. discriminate HE.
    - (* [comment removed for export] *)
      rewrite mtree_ok_MPre0 in HT0. apply andb_prop in HT0 as [HL HT0]. apply andb_prop in HL as [HL HLV]. apply andb_prop in HL as [HL1 HL2].
      apply Nat.leb_le in HL1. apply Nat.leb_le in HL2. cbn [mtree_lvl lvl_shape lshape_lvl]. split; [exact HL1|]. split; [exact HL2|].
      intros fx FRM E R FULL model HCS.
      destruct (check _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) as [s| ] eqn:Hchk; [|discriminate].
      apply andb_prop in HT0 as [HT0 HF]. apply andb_prop in HT0 as [Hall Hcov].
      set (HOLESW := fun (_ : nat) (_ : env) (fs' : Fs.Fs) => t_res L argv fs').
      assert (HLa : forall h E1 E2 fs', env_agree NX0 E1 E2 -> HOLESW h E1 fs' = HOLESW h E2 fs') by reflexivity.
      assert (HLn : forall h E1 fs', HOLESW h E1 fs' []) by (intros; unfold HOLESW; apply t_res_nil).
      assert (HLlv : forall h1 h2 L0 E1 fs', lv_of HT h1 = Some L0 -> lv_of HT h2 = Some L0 -> HOLESW h1 E1 fs' = HOLESW h2 E1 fs') by reflexivity.
      assert (HLs : forall (fx1 : FPState), frm_zero fx1 -> holes_stmt ASEGS ASAN LIM (hs_of HT) SINV argH LINV HOLESW fs).
      { intros fx1 FRM1 j chj Hj E1 R1 FULL1 model1 HC1.
        unfold hs_of in Hj. destruct (ht_of HT j) as [[Lj chj']|] eqn:He; [|discriminate]. cbn [snd] in Hj. injection Hj as ->.
        destruct (mcover_sound HT PT j _ Hcov He) as (t' & Ht').
        pose proof (mforest0_ok_sound KCm BFUELm FUELm ITm TTm L HT C PT j t' _ HF (lookupT_In _ _ _ Ht') He) as Hok. cbn [snd] in Hok.
        destruct (IH j t' (lookupT_In _ _ _ Ht') L L chj C Hok HC) as (Hlo & Hhi & RZ).
        unfold HOLESW. rewrite (co_fs _ _ _ _ _ _ _ _ _ _ _ _ HC1).
        replace L with (mtree_lvl t') by lia. exact (RZ fx1 FRM1 E1 R1 FULL1 model1 HC1). }
      pose proof (in_class_H_class APH sp rdraw argv envp fs uid hw Hva Hfit [] SINV eq_refl SINVm_blob) as HCL.
      pose proof (main_check_sound [] (hs_of HT) (lv_of HT) HOLESW HCL HLa HLn HLlv HLs p _ s Hchk fx FRM E R FULL model HCS) as RZ.
      rewrite (co_fs _ _ _ _ _ _ _ _ _ _ _ _ HCS) in RZ.
      eapply srz_conseq; [exact RZ|].
      apply sd_all_holes; [exact Hall | intros h; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Definition HOLESM (h : nat) (E : env) (fs' : Fs.Fs) : TSet := spec argv fs'.
  Lemma HOLESM_agree : forall h E E' fs', env_agree NX0 E E' -> HOLESM h E fs' = HOLESM h E' fs'.
  Proof. reflexivity. Qed.
  Lemma HOLESM_nil : forall h E fs', HOLESM h E fs' [].
  Proof. intros. apply spec_nil. Qed.
  Lemma HOLESM_lv : forall h1 h2 E fs', HOLESM h1 E fs' = HOLESM h2 E fs'.   (* [comment removed for export] *)
  Proof. reflexivity. Qed.

  #[local] Notation TREE_OK h := (mtree_ok KCm BFUELm FUELm ITm TTm 0 0 (HSA HS_asan h)).

  Variable TREE : nat -> nat -> mtree.
  Hypothesis TREES : forall h ch i, HS_asan h = Some ch -> (i < 6)%nat -> TREE_OK h (root_class i) (TREE h i) = true.

  Theorem main_holes : forall (fx : FPState), frm_zero fx -> holes_stmt ASEGS ASAN LIM HS_asan SINV0' argH LINV HOLESM fs.
  Proof.
    intros fx FRM h ch Hh E R FULL model HC.
    assert (Ech : ch = HSA HS_asan h) by (unfold HSA; rewrite Hh; reflexivity).
    rewrite Ech in HC |- *.
    (* [comment removed for export] *)
    pose proof (cs_ok_reblob ASEGS ASAN APH sp rdraw brk0 argv envp uid hw c LIM LINV fs E (HSA HS_asan h) R FULL model ltac:(rewrite <- Ech; exact (HSA_noblob h ch Hh)) HC) as HC1.
    unfold HOLESM. rewrite (co_fs _ _ _ _ _ _ _ _ _ _ _ _ HC).
    destruct (root_cover argv fs Hva) as (i & Hi & HCi).
    destruct (mtree_sound (TREE h i) 0 0 (HSA HS_asan h) (root_class i) (TREES h ch i Hh Hi) HCi) as (H1 & H2 & RZ).
    assert (HL : mtree_lvl (TREE h i) = 0%nat) by lia. rewrite HL in RZ. cbn [t_res] in RZ.
    exact (RZ fx FRM _ R FULL model HC1).
  Qed.

  (* [comment removed for export] *)
  Theorem asan_realizes_spec :
    srealizes ASEGS (init_config ASEGS ImgA.M.init_pc APH sp brk0 mbase rdraw LIM
                                 (AsanInit.inp argv envp fs stdin uid gid hw groups net ur nofile sigmask abt))
              (spec argv fs).
  Proof.
    eapply srz_conseq.
    - exact (asan_startup LINV HLINV XALL XRP sp rdraw brk0 mbase argv envp fs stdin uid gid hw nofile sigmask abt groups net ur Hsp Hbrk Hva Hve Hfit Huid Hhw
               IT0 IT0_ok HS_asan startup_plan startup_shape KC0 BFUEL FUEL TT0 startup_cert TT0_ok HOLESM HOLESM_agree HOLESM_nil HOLESM_lv main_holes).
    - apply sd_all_holes; [exact startup_all_holes | reflexivity].
  Qed.
End Main.
