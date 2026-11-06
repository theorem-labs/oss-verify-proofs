(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  PropExec ShapeAlg AgentLib AsanSpec AxSymExec3 AsanPlanCore AsanPlan AsanPlanFO AsanPlanImages AsanInit
  AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AP.
Unset Lia Cache.
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
| MEmpty (L : nat).                                                           (* [comment removed for export] *)

(* [comment removed for export] *)
Section MTreeInd.
  Variable P : mtree -> Prop.
  Hypothesis Hleaf : forall L p, P (MLeaf L p).
  Hypothesis Hpre : forall L p HT PT, (forall j t, In (j, t) PT -> P t) -> P (MPre L p HT PT).
  Hypothesis Hsplit : forall q mid le gt, P le -> P gt -> P (MSplit q mid le gt).
  Hypothesis Hcase : forall e mid le gt, P le -> P gt -> P (MCase e mid le gt).
  Hypothesis Hclass : forall C' t, P t -> P (MClass C' t).
  Hypothesis Hempty : forall L, P (MEmpty L).
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
    end.
End MTreeInd.

(* [comment removed for export] *)
Definition qbounds2 (C : class) (q : qty) : Z * Z :=
  let b := qbounds C q in
  match q with
  | QL1 => let v := look_of C in clamp b (fst (look_L1 v)) (snd (look_L1 v))
  | QRoom => let f := qbounds C QFlen in let g := qbounds C QCfgLen in clamp b (fst f - 6 - snd g) (snd f - 6 - fst g)
  | _ => b
  end.
Definition class_le2 (C C' : class) : bool :=
  forallb (fun q => let a := qbounds2 C q in let b := cbounds C' q in
                    (snd a <? fst a) || ((fst b <=? fst a) && (snd a <=? snd b)))%bool all_qty.

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

  (* [comment removed for export] *)
  #[local] Notation CHK C HS cs p :=
    (APF.check ASEGS ITm INFO_ASAN NX0 AsanInit.LIMIT (XNm ASEGS INFO_ASAN NX0 RPN.RP_ASAN (iotab_of C)) (XEm ASEGS INFO_ASAN NX0) (XBm ASEGS NX0 (iotab_of C))
           HS KCm BFUELm FUELm None cs p).

  (* [comment removed for export] *)
  Definition mcover (HT : list (nat * (nat * acs))) (PT : list (nat * mtree)) : bool :=
    forallb (fun e : nat * (nat * acs) => match lookupT PT (fst e) with Some _ => true | None => false end) HT.

  (* [comment removed for export] *)
  Fixpoint mtree_ok (lo hi : nat) (ch : acs) (C : class) (t : mtree) : bool :=
    match t with
    | MLeaf L p =>
        Nat.leb lo L && Nat.leb L hi &&
        match CHK C HS_none (pay_start ch C) p with COk s => class_pay_ok L C s | CErr _ _ _ => false end
    | MPre L p HT PT =>
        Nat.leb lo L && Nat.leb L hi &&
        match CHK C (hs_of HT) (pay_start ch C) p with
        | COk s =>
            class_seg_ok (lv_of HT) L C s && mcover HT PT &&
            (fix forest (PT : list (nat * mtree)) : bool :=
               match PT with
               | [] => true
               | (j, t') :: PT' =>
                   match ht_of HT j with Some e => mtree_ok (Nat.max L 1) (fst e) (snd e) C t' | None => true end && forest PT'
               end) PT
        | CErr _ _ _ => false
        end
    | MSplit q mid le gt => mtree_ok lo hi ch (C ++ [(q, QMIN, mid)]) le && mtree_ok lo hi ch (C ++ [(q, mid + 1, QMAX)]) gt
    | MCase e mid le gt =>
        lshape_eqb (lvl_shape le) (lvl_shape gt) &&
        mtree_ok lo hi (mcase_lo ch e mid) C le && mtree_ok lo hi (mcase_hi ch e mid) C gt
    | MClass C' t' => class_le2 C C' && mtree_ok lo hi ch C' t'
    | MEmpty L => Nat.leb lo L && Nat.leb L hi && class_empty C
    end.

  (* [comment removed for export] *)
  Fixpoint mforest_ok (L : nat) (HT : list (nat * (nat * acs))) (C : class) (PT : list (nat * mtree)) : bool :=
    match PT with
    | [] => true
    | (j, t') :: PT' => match ht_of HT j with Some e => mtree_ok (Nat.max L 1) (fst e) (snd e) C t' | None => true end && mforest_ok L HT C PT'
    end.
  Lemma mtree_ok_MPre : forall lo hi ch C L p HT PT,
    mtree_ok lo hi ch C (MPre L p HT PT) =
    (Nat.leb lo L && Nat.leb L hi &&
     match CHK C (hs_of HT) (pay_start ch C) p with
     | COk s => class_seg_ok (lv_of HT) L C s && mcover HT PT && mforest_ok L HT C PT
     | CErr _ _ _ => false
     end)%bool.
  Proof.
    intros. cbn [mtree_ok]. destruct (APF.check _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) as [s|]; [|reflexivity].
    f_equal. f_equal. induction PT as [|[j t'] PT IH]; [reflexivity|]. cbn [mforest_ok]. rewrite IH. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma mtree_ok_split : forall lo hi ch C q mid le gt,
    mtree_ok lo hi ch (C ++ [(q, QMIN, mid)]) le = true -> mtree_ok lo hi ch (C ++ [(q, mid + 1, QMAX)]) gt = true ->
    mtree_ok lo hi ch C (MSplit q mid le gt) = true.
  Proof. intros lo hi ch C q mid le gt H1 H2. cbn [mtree_ok]. rewrite H1, H2. reflexivity. Qed.

  Lemma mtree_ok_leaf : forall lo hi ch C L p s,
    (Nat.leb lo L && Nat.leb L hi)%bool = true ->
    CHK C HS_none (pay_start ch C) p = COk s -> class_pay_ok L C s = true -> mtree_ok lo hi ch C (MLeaf L p) = true.
  Proof. intros lo hi ch C L p s HL H1 H2. cbn [mtree_ok]. rewrite H1, H2, HL. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma mtree_ok_leaf0 : forall h C p s,
    main_check HS_asan KCm BFUELm FUELm ITm h C p = COk s -> class_shape_ok C s = true -> mtree_ok 0 0 (HSA HS_asan h) C (MLeaf 0 p) = true.
  Proof. intros h C p s H1 H2. cbn [mtree_ok]. unfold main_check, main_start in H1. rewrite H1. exact H2. Qed.
  Lemma mtree_ok_leafP : forall lo hi ch C L p s,
    (Nat.leb lo L && Nat.leb L hi)%bool = true ->
    pay_check KCm BFUELm FUELm ITm ch C p = COk s -> class_pay_ok L C s = true -> mtree_ok lo hi ch C (MLeaf L p) = true.
  Proof. intros lo hi ch C L p s HL H1 H2. eapply mtree_ok_leaf; eassumption. Qed.

  Lemma mtree_ok_seg : forall lo hi ch C L p HT PT s,
    (Nat.leb lo L && Nat.leb L hi)%bool = true ->
    CHK C (hs_of HT) (pay_start ch C) p = COk s -> class_seg_ok (lv_of HT) L C s = true ->
    mcover HT PT = true -> mforest_ok L HT C PT = true ->
    mtree_ok lo hi ch C (MPre L p HT PT) = true.
  Proof. intros lo hi ch C L p HT PT s HL H1 H2 H3 H4. rewrite mtree_ok_MPre, H1, H2, H3, H4, HL. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma mtree_ok_pre0 : forall hi h C L p HT PT s,
    Nat.leb L hi = true ->
    pre_check HS_asan KCm BFUELm FUELm ITm h C HT p = COk s -> class_seg_ok (lv_of HT) L C s = true ->
    mcover HT PT = true -> mforest_ok L HT C PT = true ->
    mtree_ok 0 hi (HSA HS_asan h) C (MPre L p HT PT) = true.
  Proof. intros hi h C L p HT PT s HL H1 H2 H3 H4. unfold pre_check, main_start in H1. exact (mtree_ok_seg 0%nat hi (HSA HS_asan h) C L p HT PT s HL H1 H2 H3 H4). Qed.
  (* [comment removed for export] *)
  Lemma mtree_ok_segP : forall lo hi ch C L p HT PT s,
    (Nat.leb lo L && Nat.leb L hi)%bool = true ->
    seg_check KCm BFUELm FUELm ITm ch C HT p = COk s -> class_seg_ok (lv_of HT) L C s = true ->
    mcover HT PT = true -> mforest_ok L HT C PT = true ->
    mtree_ok lo hi ch C (MPre L p HT PT) = true.
  Proof. intros. eapply mtree_ok_seg; eassumption. Qed.

  Lemma mtree_ok_case : forall lo hi ch C e mid le gt,
    lshape_eqb (lvl_shape le) (lvl_shape gt) = true ->
    mtree_ok lo hi (mcase_lo ch e mid) C le = true -> mtree_ok lo hi (mcase_hi ch e mid) C gt = true ->
    mtree_ok lo hi ch C (MCase e mid le gt) = true.
  Proof. intros lo hi ch C e mid le gt H0 H1 H2. cbn [mtree_ok]. rewrite H0, H1, H2. reflexivity. Qed.

  Lemma mtree_ok_class : forall lo hi ch C C' t,
    class_le2 C C' = true -> mtree_ok lo hi ch C' t = true -> mtree_ok lo hi ch C (MClass C' t) = true.
  Proof. intros lo hi ch C C' t H0 H1. cbn [mtree_ok]. rewrite H0, H1. reflexivity. Qed.

  Lemma mtree_ok_empty : forall lo hi ch C L,
    (Nat.leb lo L && Nat.leb L hi)%bool = true -> class_empty C = true -> mtree_ok lo hi ch C (MEmpty L) = true.
  Proof. intros lo hi ch C L HL H1. cbn [mtree_ok]. rewrite H1, HL. reflexivity. Qed.

  Lemma mforest_ok_nil : forall L HT C, mforest_ok L HT C [] = true.
  Proof. reflexivity. Qed.
  Lemma mforest_ok_cons : forall L HT C j t PT Lj chj,
    ht_of HT j = Some (Lj, chj) -> mtree_ok (Nat.max L 1) Lj chj C t = true -> mforest_ok L HT C PT = true ->
    mforest_ok L HT C ((j, t) :: PT) = true.
  Proof. intros L HT C j t PT Lj chj H1 H2 H3. cbn [mforest_ok]. rewrite H1. cbn [fst snd]. rewrite H2. exact H3. Qed.
  (* [comment removed for export] *)
  Lemma mforest_ok_skip : forall L HT C j t PT,
    ht_of HT j = None -> mforest_ok L HT C PT = true -> mforest_ok L HT C ((j, t) :: PT) = true.
  Proof. intros L HT C j t PT H1 H2. cbn [mforest_ok]. rewrite H1. exact H2. Qed.

  Lemma mforest_ok_sound : forall L HT C PT j t e,
    mforest_ok L HT C PT = true -> In (j, t) PT -> ht_of HT j = Some e -> mtree_ok (Nat.max L 1) (fst e) (snd e) C t = true.
  Proof.
    intros L HT C PT j t e. induction PT as [|[j' t'] PT IH]; intros HF Hin He; [destruct Hin|].
    cbn [mforest_ok] in HF. apply andb_prop in HF as [H1 H2].
    destruct Hin as [Heq|Hin]; [|exact (IH H2 Hin He)].
    injection Heq as -> ->. rewrite He in H1. exact H1.
  Qed.
  Lemma mcover_sound : forall HT PT j e, mcover HT PT = true -> ht_of HT j = Some e -> exists t, lookupT PT j = Some t.
  Proof.
    intros HT PT j e HC He. unfold mcover in HC. rewrite forallb_forall in HC.
    specialize (HC (j, e) (ht_of_In _ _ _ He)). cbn [fst] in HC. destruct (lookupT PT j) as [t|]; [exists t; reflexivity | discriminate].
  Qed.
End MainCheck.

Lemma pc_set_kn : forall cs k, pc (set_kn cs k) = pc cs.
Proof. reflexivity. Qed.

