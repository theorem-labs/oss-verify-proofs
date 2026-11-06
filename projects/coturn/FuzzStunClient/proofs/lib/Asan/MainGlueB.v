(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec ShapeAlg SpinAlg AgentLib AsanAcct.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Spec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import
  AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanInit
  AsanNodesArg AsanNodesIO AsanNodesFX AsanNodesDepot AsanMainLib AsanShape FContractAsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import FPA_both.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import MainGlueDefsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Inductive rtree : Type :=
| RLeaf (p : plan)                      (* [comment removed for export] *)
| RClass (C' : class) (t : rtree)       (* [comment removed for export] *)
| RPreS (p : plan) (HR : list (nat * (shape * acs))) (RT : list (nat * rtree)).
                                        (* [comment removed for export] *)

(* [comment removed for export] *)
Section RTreeInd.
  Variable P : rtree -> Prop.
  Hypothesis Hrleaf : forall p, P (RLeaf p).
  Hypothesis Hrclass : forall C' t, P t -> P (RClass C' t).
  Hypothesis Hrpres : forall p HR RT, (forall j t, In (j, t) RT -> P t) -> P (RPreS p HR RT).
  Fixpoint rtree_ind2 (t : rtree) : P t :=
    match t with
    | RLeaf p => Hrleaf p
    | RClass C' t' => Hrclass C' t' (rtree_ind2 t')
    | RPreS p HR RT =>
        Hrpres p HR RT
          ((fix go (RT : list (nat * rtree)) : forall j t, In (j, t) RT -> P t :=
              match RT return (forall j t, In (j, t) RT -> P t) with
              | [] => fun j t H => False_ind _ H
              | (j', t') :: RT' => fun j t H =>
                  match H with
                  | or_introl E => eq_ind (j', t') (fun jt => P (snd jt)) (rtree_ind2 t') (j, t) E
                  | or_intror H' => go RT' j t H'
                  end
              end) RT)
    end.
End RTreeInd.

Fixpoint subst_holes (RS : nat -> option shape) (s : shape) : shape :=
  match s with
  | SHole h => match RS h with Some r => r | None => SHole h end
  | SEmitP fd ps s' => SEmitP fd ps (subst_holes RS s')
  | SAlt2 a b => SAlt2 (subst_holes RS a) (subst_holes RS b)
  | SCase e mid a b => SCase e mid (subst_holes RS a) (subst_holes RS b)
  | other => other
  end.
(* [comment removed for export] *)
Definition rs_of (HR : list (nat * (shape * acs))) (h : nat) : option shape :=
  match lookupT HR h with Some e => Some (fst e) | None => None end.
Definition hs_ofS (HR : list (nat * (shape * acs))) (h : nat) : option acs :=
  match lookupT HR h with Some e => Some (snd e) | None => None end.
Definition mcoverS (HR : list (nat * (shape * acs))) (PT : list (nat * rtree)) : bool :=
  forallb (fun e : nat * (shape * acs) => match lookupT PT (fst e) with Some _ => true | None => false end) HR.

(* [comment removed for export] *)
Definition hs_ofX (HT : list (nat * (nat * acs))) (HR : list (nat * (shape * acs))) (h : nat) : option acs :=
  match ht_of HT h with Some e => Some (snd e) | None => hs_ofS HR h end.
Definition rs_ofX (HT : list (nat * (nat * acs))) (HR : list (nat * (shape * acs))) (h : nat) : option shape :=
  match ht_of HT h with Some _ => None | None => rs_of HR h end.
Fixpoint hole_free (s : shape) : bool :=
  match s with
  | SHole _ => false
  | SEmitP _ _ s' => hole_free s'
  | SAlt2 a b | SCase _ _ a b => hole_free a && hole_free b
  | _ => true
  end.
Lemma sd_hole_free : forall (H1 H2 : nat -> env -> Fs.Fs -> TSet) D E fs s, hole_free s = true -> sd H1 D E fs s = sd H2 D E fs s.
Proof.
  intros H1 H2 D E fs s. induction s as [|c|fd ps s IH|a IHa b IHb|e mid a IHa b IHb|h|]; intros HS; cbn [hole_free] in HS; cbn [sd];
    try reflexivity; try discriminate HS.
  - rewrite (IH HS). reflexivity.
  - apply andb_prop in HS as [Ha Hb]. rewrite (IHa Ha), (IHb Hb). reflexivity.
  - apply andb_prop in HS as [Ha Hb]. rewrite (IHa Ha), (IHb Hb). reflexivity.
Qed.
Definition hr_hole_free (HR : list (nat * (shape * acs))) : bool := forallb (fun e : nat * (shape * acs) => hole_free (fst (snd e))) HR.

(* [comment removed for export] *)
Inductive mtree : Type :=
| MLeaf (L : nat) (p : plan)                                                   (* [comment removed for export] *)
| MPre (L : nat) (p : plan) (HT : list (nat * (nat * acs))) (PT : list (nat * mtree))
                                                 (* [comment removed for export] *)
| MSplit (q : qty) (mid : Z) (le gt : mtree)                                  (* [comment removed for export] *)
| MCase (e : expr) (mid : Z) (le gt : mtree)                                  (* [comment removed for export] *)
| MClass (C' : class) (t : mtree)                                             (* [comment removed for export] *)
| MEmpty (L : nat)                                                            (* [comment removed for export] *)
| MPreS (L : nat) (p : plan) (HR : list (nat * (shape * acs))) (PT : list (nat * rtree))
                                                 (* [comment removed for export] *)
| MPreX (L : nat) (p : plan) (HT : list (nat * (nat * acs))) (PT : list (nat * mtree))
        (HR : list (nat * (shape * acs))) (RT : list (nat * rtree))
                                                 (* [comment removed for export] *)
| MLoop (L : nat) (p : plan) (b v : N) (h : nat) (HT : list (nat * (nat * acs))) (PT : list (nat * mtree)).
                                                 (* [comment removed for export] *)

(* [comment removed for export] *)
Section MTreeInd.
  Variable P : mtree -> Prop.
  Hypothesis Hleaf : forall L p, P (MLeaf L p).
  Hypothesis Hpre : forall L p HT PT, (forall j t, In (j, t) PT -> P t) -> P (MPre L p HT PT).
  Hypothesis Hsplit : forall q mid le gt, P le -> P gt -> P (MSplit q mid le gt).
  Hypothesis Hcase : forall e mid le gt, P le -> P gt -> P (MCase e mid le gt).
  Hypothesis Hclass : forall C' t, P t -> P (MClass C' t).
  Hypothesis Hempty : forall L, P (MEmpty L).
  Hypothesis Hpres : forall L p HR PT, P (MPreS L p HR PT).
  Hypothesis Hprex : forall L p HT PT HR RT, (forall j t, In (j, t) PT -> P t) -> P (MPreX L p HT PT HR RT).
  Hypothesis Hloop : forall L p b v h HT PT, (forall j t, In (j, t) PT -> P t) -> P (MLoop L p b v h HT PT).
  Fixpoint mtree_ind2 (t : mtree) : P t :=
    match t with
    | MPreX L p HT PT HR RT =>
        Hprex L p HT PT HR RT
          ((fix go (PT : list (nat * mtree)) : forall j t, In (j, t) PT -> P t :=
              match PT return (forall j t, In (j, t) PT -> P t) with
              | [] => fun j t H => False_ind _ H
              | (j', t') :: PT' => fun j t H =>
                  match H with
                  | or_introl E => eq_ind (j', t') (fun jt => P (snd jt)) (mtree_ind2 t') (j, t) E
                  | or_intror H' => go PT' j t H'
                  end
              end) PT)
    | MLeaf L p => Hleaf L p
    | MPreS L p HR PT => Hpres L p HR PT
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
    | MLoop L p b v h HT PT =>
        Hloop L p b v h HT PT
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
  | MPreS L _ _ _ => LNode L
  | MPreX L _ _ _ _ _ => LNode L
  | MLoop L _ _ _ _ _ _ => LNode L
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
    (check BSEGS ITm BOTH NX0 AsanInit.LIMIT (XNM (iotab_of C)) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of C))
           HS KCm BFUELm FUELm None cs p).
  (* [comment removed for export] *)
  #[local] Notation CHKL C HS cs p lc :=
    (check BSEGS ITm BOTH NX0 AsanInit.LIMIT (XNM (iotab_of C)) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of C))
           HS KCm BFUELm FUELm lc cs p).

  (* [comment removed for export] *)
  Definition mcover (HT : list (nat * (nat * acs))) (PT : list (nat * mtree)) : bool :=
    forallb (fun e : nat * (nat * acs) => match lookupT PT (fst e) with Some _ => true | None => false end) HT.

  (* [comment removed for export] *)
  Fixpoint rtree_ok (r : shape) (ch : acs) (C : class) (t : rtree) : bool :=
    match t with
    | RLeaf p => match CHK C HS_none (pay_start ch C) p with COk s => shape_eqb s r && shape_vars_lt NX0 r | CErr _ _ _ => false end
    | RClass C' t' => class_le C C' && rtree_ok r ch C' t'
    | RPreS p HR RT =>
        match CHK C (hs_ofS HR) (pay_start ch C) p with
        | COk s =>
            shape_eqb (subst_holes (rs_of HR) s) r && shape_vars_lt NX0 r && mcoverS HR RT &&
            (fix forest (RT : list (nat * rtree)) : bool :=
               match RT with
               | [] => true
               | (j, t') :: RT' =>
                   match lookupT HR j with Some (rj, chj) => rtree_ok rj chj C t' | None => true end && forest RT'
               end) RT
        | CErr _ _ _ => false
        end
    end.
  Definition rforest_ok (HR : list (nat * (shape * acs))) (C : class) (PT : list (nat * rtree)) : bool :=
    forallb (fun e : nat * rtree => match lookupT HR (fst e) with Some (r, chj) => rtree_ok r chj C (snd e) | None => true end) PT.

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
                   match ht_of HT j with Some e => mtree_ok L (fst e) (snd e) C t' | None => true end && forest PT'
               end) PT
        | CErr _ _ _ => false
        end
    | MSplit q mid le gt => mtree_ok lo hi ch (C ++ [(q, QMIN, mid)]) le && mtree_ok lo hi ch (C ++ [(q, mid + 1, QMAX)]) gt
    | MCase e mid le gt =>
        lshape_eqb (lvl_shape le) (lvl_shape gt) &&
        mtree_ok lo hi (mcase_lo ch e mid) C le && mtree_ok lo hi (mcase_hi ch e mid) C gt
    | MClass C' t' => class_le C C' && mtree_ok lo hi ch C' t'
    | MEmpty L => Nat.leb lo L && Nat.leb L hi && class_empty C
    | MPreS L p HR PT =>
        Nat.leb lo L && Nat.leb L hi &&
        match CHK C (hs_ofS HR) (pay_start ch C) p with
        | COk s => class_pay_ok L C (subst_holes (rs_of HR) s) && mcoverS HR PT && rforest_ok HR C PT
        | CErr _ _ _ => false
        end
    | MPreX L p HT PT HR RT =>
        Nat.leb lo L && Nat.leb L hi &&
        match CHK C (hs_ofX HT HR) (pay_start ch C) p with
        | COk s =>
            class_seg_ok (lv_of HT) L C (subst_holes (rs_ofX HT HR) s) && mcover HT PT &&
            (fix forest (PT : list (nat * mtree)) : bool :=
               match PT with
               | [] => true
               | (j, t') :: PT' =>
                   match ht_of HT j with Some e => mtree_ok L (fst e) (snd e) C t' | None => true end && forest PT'
               end) PT
            && mcoverS HR RT && rforest_ok HR C RT && hr_hole_free HR
        | CErr _ _ _ => false
        end
    | MLoop L p b v h HT PT =>
        Nat.leb lo L && Nat.leb L hi && N.leb NX0 b && N.ltb v b &&
        match ht_of HT h with Some _ => false | None => true end &&
        match CHKL C (hs_of HT) (pay_start ch C) p (Some (MC b v h ch)) with
        | COk s =>
            class_seg_ok (lv_of ((h, (L, ch)) :: HT)) L C s && mcover HT PT &&
            (fix forest (PT : list (nat * mtree)) : bool :=
               match PT with
               | [] => true
               | (j, t') :: PT' =>
                   match ht_of HT j with Some e => mtree_ok L (fst e) (snd e) C t' | None => true end && forest PT'
               end) PT
        | CErr _ _ _ => false
        end
    end.

  (* [comment removed for export] *)
  Fixpoint mforest_ok (L : nat) (HT : list (nat * (nat * acs))) (C : class) (PT : list (nat * mtree)) : bool :=
    match PT with
    | [] => true
    | (j, t') :: PT' => match ht_of HT j with Some e => mtree_ok L (fst e) (snd e) C t' | None => true end && mforest_ok L HT C PT'
    end.
  Lemma mtree_ok_MPre : forall lo hi ch C L p HT PT,
    mtree_ok lo hi ch C (MPre L p HT PT) =
    (Nat.leb lo L && Nat.leb L hi &&
     match CHK C (hs_of HT) (pay_start ch C) p with
     | COk s => class_seg_ok (lv_of HT) L C s && mcover HT PT && mforest_ok L HT C PT
     | CErr _ _ _ => false
     end)%bool.
  Proof.
    intros. cbn [mtree_ok]. destruct (check _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) as [s|]; [|reflexivity].
    f_equal. f_equal. induction PT as [|[j t'] PT IH]; [reflexivity|]. cbn [mforest_ok]. rewrite IH. reflexivity.
  Qed.

  Lemma mtree_ok_MPreX : forall lo hi ch C L p HT PT HR RT,
    mtree_ok lo hi ch C (MPreX L p HT PT HR RT) =
    (Nat.leb lo L && Nat.leb L hi &&
     match CHK C (hs_ofX HT HR) (pay_start ch C) p with
     | COk s => class_seg_ok (lv_of HT) L C (subst_holes (rs_ofX HT HR) s) && mcover HT PT && mforest_ok L HT C PT
                && mcoverS HR RT && rforest_ok HR C RT && hr_hole_free HR
     | CErr _ _ _ => false
     end)%bool.
  Proof.
    intros. cbn [mtree_ok]. destruct (check _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) as [s|]; [|reflexivity].
    f_equal. f_equal. f_equal. f_equal. f_equal. induction PT as [|[j t'] PT IH]; [reflexivity|]. cbn [mforest_ok]. rewrite IH. reflexivity.
  Qed.
  Lemma mtree_ok_preX : forall lo hi ch C L p HT PT HR RT s,
    (Nat.leb lo L && Nat.leb L hi)%bool = true ->
    CHK C (hs_ofX HT HR) (pay_start ch C) p = COk s ->
    class_seg_ok (lv_of HT) L C (subst_holes (rs_ofX HT HR) s) = true ->
    mcover HT PT = true -> mforest_ok L HT C PT = true ->
    mcoverS HR RT = true -> rforest_ok HR C RT = true -> hr_hole_free HR = true ->
    mtree_ok lo hi ch C (MPreX L p HT PT HR RT) = true.
  Proof. intros lo hi ch C L p HT PT HR RT s HL H1 H2 H3 H4 H5 H6 H7. rewrite mtree_ok_MPreX, H1, H2, H3, H4, H5, H6, H7, HL. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma mtree_ok_MLoop : forall lo hi ch C L p b v h HT PT,
    mtree_ok lo hi ch C (MLoop L p b v h HT PT) =
    (Nat.leb lo L && Nat.leb L hi && N.leb NX0 b && N.ltb v b &&
     match ht_of HT h with Some _ => false | None => true end &&
     match CHKL C (hs_of HT) (pay_start ch C) p (Some (MC b v h ch)) with
     | COk s => class_seg_ok (lv_of ((h, (L, ch)) :: HT)) L C s && mcover HT PT && mforest_ok L HT C PT
     | CErr _ _ _ => false
     end)%bool.
  Proof.
    intros. cbn [mtree_ok]. destruct (check _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) as [s|]; [|reflexivity].
    f_equal. f_equal. induction PT as [|[j t'] PT IH]; [reflexivity|]. cbn [mforest_ok]. rewrite IH. reflexivity.
  Qed.
  Lemma mtree_ok_loop : forall lo hi ch C L p b v h HT PT s,
    (Nat.leb lo L && Nat.leb L hi && N.leb NX0 b && N.ltb v b)%bool = true ->
    ht_of HT h = None ->
    CHKL C (hs_of HT) (pay_start ch C) p (Some (MC b v h ch)) = COk s ->
    class_seg_ok (lv_of ((h, (L, ch)) :: HT)) L C s = true ->
    mcover HT PT = true -> mforest_ok L HT C PT = true ->
    mtree_ok lo hi ch C (MLoop L p b v h HT PT) = true.
  Proof. intros lo hi ch C L p b v h HT PT s HL Hh H1 H2 H3 H4. rewrite mtree_ok_MLoop, H1, H2, H3, H4, HL, Hh. reflexivity. Qed.

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
    class_le C C' = true -> mtree_ok lo hi ch C' t = true -> mtree_ok lo hi ch C (MClass C' t) = true.
  Proof. intros lo hi ch C C' t H0 H1. cbn [mtree_ok]. rewrite H0, H1. reflexivity. Qed.

  Lemma mtree_ok_empty : forall lo hi ch C L,
    (Nat.leb lo L && Nat.leb L hi)%bool = true -> class_empty C = true -> mtree_ok lo hi ch C (MEmpty L) = true.
  Proof. intros lo hi ch C L HL H1. cbn [mtree_ok]. rewrite H1, HL. reflexivity. Qed.

  Lemma mforest_ok_nil : forall L HT C, mforest_ok L HT C [] = true.
  Proof. reflexivity. Qed.
  Lemma mforest_ok_cons : forall L HT C j t PT Lj chj,
    ht_of HT j = Some (Lj, chj) -> mtree_ok L Lj chj C t = true -> mforest_ok L HT C PT = true ->
    mforest_ok L HT C ((j, t) :: PT) = true.
  Proof. intros L HT C j t PT Lj chj H1 H2 H3. cbn [mforest_ok]. rewrite H1. cbn [fst snd]. rewrite H2. exact H3. Qed.
  (* [comment removed for export] *)
  Lemma mforest_ok_skip : forall L HT C j t PT,
    ht_of HT j = None -> mforest_ok L HT C PT = true -> mforest_ok L HT C ((j, t) :: PT) = true.
  Proof. intros L HT C j t PT H1 H2. cbn [mforest_ok]. rewrite H1. exact H2. Qed.

  Lemma mforest_ok_sound : forall L HT C PT j t e,
    mforest_ok L HT C PT = true -> In (j, t) PT -> ht_of HT j = Some e -> mtree_ok L (fst e) (snd e) C t = true.
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
  (* [comment removed for export] *)
  Lemma mtree_ok_preS : forall lo hi ch C L p HR PT s,
    (Nat.leb lo L && Nat.leb L hi)%bool = true ->
    CHK C (hs_ofS HR) (pay_start ch C) p = COk s ->
    class_pay_ok L C (subst_holes (rs_of HR) s) = true ->
    mcoverS HR PT = true -> rforest_ok HR C PT = true ->
    mtree_ok lo hi ch C (MPreS L p HR PT) = true.
  Proof. intros lo hi ch C L p HR PT s HL H1 H2 H3 H4. cbn [mtree_ok]. rewrite H1, HL, H2, H3, H4. reflexivity. Qed.
  Lemma rtree_ok_leaf : forall r ch C p s,
    CHK C HS_none (pay_start ch C) p = COk s -> shape_eqb s r = true -> shape_vars_lt NX0 r = true ->
    rtree_ok r ch C (RLeaf p) = true.
  Proof. intros r ch C p s H1 H2 H3. cbn [rtree_ok]. rewrite H1, H2, H3. reflexivity. Qed.
  Lemma rtree_ok_class : forall r ch C C' t, class_le C C' = true -> rtree_ok r ch C' t = true -> rtree_ok r ch C (RClass C' t) = true.
  Proof. intros r ch C C' t H1 H2. cbn [rtree_ok]. rewrite H1, H2. reflexivity. Qed.
  Lemma rforest_ok_nil : forall HR C, rforest_ok HR C [] = true.
  Proof. reflexivity. Qed.
  Lemma rforest_ok_cons : forall HR C h t PT r chj,
    lookupT HR h = Some (r, chj) -> rtree_ok r chj C t = true -> rforest_ok HR C PT = true -> rforest_ok HR C ((h, t) :: PT) = true.
  Proof. intros HR C h t PT r chj H1 H2 H3. unfold rforest_ok. cbn [forallb fst snd]. rewrite H1, H2. exact H3. Qed.
  (* [comment removed for export] *)
  Lemma rtree_ok_RPreS : forall r ch C p HR RT,
    rtree_ok r ch C (RPreS p HR RT) =
    match CHK C (hs_ofS HR) (pay_start ch C) p with
    | COk s => shape_eqb (subst_holes (rs_of HR) s) r && shape_vars_lt NX0 r && mcoverS HR RT && rforest_ok HR C RT
    | CErr _ _ _ => false
    end.
  Proof.
    intros. cbn [rtree_ok]. destruct (check _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) as [s|]; [|reflexivity].
    f_equal. unfold rforest_ok. induction RT as [|[j t'] RT IH]; [reflexivity|]. cbn [forallb fst snd]. rewrite IH. reflexivity.
  Qed.
  Lemma rtree_ok_preS : forall r ch C p HR RT s,
    CHK C (hs_ofS HR) (pay_start ch C) p = COk s -> shape_eqb (subst_holes (rs_of HR) s) r = true -> shape_vars_lt NX0 r = true ->
    mcoverS HR RT = true -> rforest_ok HR C RT = true -> rtree_ok r ch C (RPreS p HR RT) = true.
  Proof. intros r ch C p HR RT s H1 H2 H3 H4 H5. rewrite rtree_ok_RPreS, H1, H2, H3, H4, H5. reflexivity. Qed.
  (* [comment removed for export] *)
End MainCheck.

Lemma pc_set_kn : forall cs k, pc (set_kn cs k) = pc cs.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sd_subst_holes : forall (H1 H2 : nat -> env -> Fs.Fs -> TSet) D E fs (RS : nat -> option shape) s,
  (forall h, match RS h with Some r => t_eq (H1 h E fs) (sd H2 D E fs r) | None => t_eq (H1 h E fs) (H2 h E fs) end) ->
  t_eq (sd H1 D E fs s) (sd H2 D E fs (subst_holes RS s)).
Proof.
  intros H1 H2 D E fs RS s HH. induction s as [|c|fd ps s IH|a IHa b IHb|e mid a IHa b IHb|h|]; cbn [subst_holes sd].
  - apply t_eq_refl.
  - apply t_eq_refl.
  - apply t_eq_emit. exact IH.
  - apply t_eq_alt2; assumption.
  - destruct (bv_unsigned (edenot E e) <=? mid); assumption.
  - specialize (HH h). destruct (RS h) as [r|]; [exact HH | cbn [sd]; exact HH].
  - apply t_eq_refl.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Main.
  (* [comment removed for export] *)
  Hypothesis Iwx : AsanAcct.wx_segs_nowrap BSEGS.
  Hypothesis Ihull : forall a : word, APS.in_hull BOTH (bv_unsigned a) = false -> find_segment BSEGS (bv_unsigned a) 1 = None.
  Hypothesis Ihok : APS.hull_ok BOTH.
  Hypothesis Ishok : APS.shadow_ok BOTH.
  Variable APH : PhdrInfo.
  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid : word.
  Variable hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk BSEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.

  #[local] Notation c := (content_of argv fs).
  #[local] Notation SINV0' := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation SINV := (SINVm APH sp rdraw brk0 argv envp uid hw (content_of argv fs)).
  #[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).
  #[local] Notation LIM := AsanInit.LIMIT.

  (* [comment removed for export] *)
  Variable HS_asan : nat -> option acs.
  (* [comment removed for export] *)
  Hypothesis HSA_noblob : forall h ch, HS_asan h = Some ch -> acs_noblob ch = true.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variables KCm BFUELm FUELm : nat.
  Variable ITm : itab.
  Hypothesis ITm_ok : itab_sound BSEGS ITm.

  (* [comment removed for export] *)
  Hypothesis Inx0 : APS.nx0_ok NX0.
  Hypothesis AH : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Hypothesis AT : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a.
  Hypothesis AA : forall E E' (a : word), env_agree NX0 E E' -> argH E a = argH E' a.
  Hypothesis SF : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SA : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
  Hypothesis Msys : forall y, sys_stmt BSEGS BOTH NX0 LIM SINV argH fs y.
  Hypothesis Mbrk2 : brk2_stmt BSEGS BOTH NX0 LIM SINV argH fs.
  Hypothesis Mbrk2s : brk2s_stmt BSEGS BOTH NX0 LIM SINV argH fs.
  Hypothesis Mmmap2 : mm2_stmt BSEGS BOTH NX0 LIM SINV argH fs (node_mmap2 BOTH NX0 LIM).
  Hypothesis Mmmapin : forall hole : bool, mm3_stmt BSEGS BOTH NX0 LIM SINV argH fs (node_mmapin BOTH LIM hole).
  Hypothesis Mmprotect2 : mm2_stmt BSEGS BOTH NX0 LIM SINV argH fs (node_mprotect2 BOTH LIM).
  Hypothesis Mexit : exit_stmt BSEGS BOTH LIM SINV argH fs.
  Hypothesis Mx : forall x, x_stmt BSEGS BOTH NX0 LIM SINV argH fs x.
  Hypothesis Mjoin : join_stmt BSEGS BOTH NX0 LIM SINV argH fs.
  Hypothesis Mjoin_ok : join_ok_stmt BSEGS BOTH LIM SINV argH fs.
  (* [comment removed for export] *)
  Hypothesis Mxn : forall T, H_class_prop T argv fs SINV -> ext_stmt BSEGS BOTH NX0 LIM (XNM T) SINV argH fs.
  Hypothesis Mxe : emit_stmt BSEGS BOTH NX0 LIM (XEm BSEGS BOTH NX0) SINV argH fs.
  Hypothesis Mxb : forall T, H_class_prop T argv fs SINV -> ext2_stmt BSEGS BOTH NX0 LIM (XBm BSEGS NX0 T) SINV argH fs.
  (* [comment removed for export] *)
  Hypothesis VF : forall E M, SINV E M -> know_ok BSEGS E M (vfacts (variant_of c)).

  Lemma SINVm_blob : forall E M, SINV E M -> forall j, eb E (8 + j)%nat = chunk j (content_of argv fs).
  Proof. intros E M (_ & _ & _ & H) j. apply H. Qed.

  Lemma HOLES0_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES0 h E fs' = HOLES0 h E' fs'.
  Proof. reflexivity. Qed.
  Lemma HOLES0_nil : forall h E fs', HOLES0 h E fs' [].
  Proof. intros. reflexivity. Qed.
  Lemma HS_none_sound : holes_stmt BSEGS BOTH LIM HS_none SINV argH HOLES0 fs.
  Proof. intros h ch H. discriminate H. Qed.

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

  #[local] Notation CHK C HS cs p :=
    (check BSEGS ITm BOTH NX0 LIM (XNM (iotab_of C)) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of C))
           HS KCm BFUELm FUELm None cs p).
  #[local] Notation CHKL C HS cs p lc :=
    (check BSEGS ITm BOTH NX0 LIM (XNM (iotab_of C)) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of C))
           HS KCm BFUELm FUELm lc cs p).
  #[local] Notation AH := (argH0_high APH sp argv envp uid Hsp Hva).
  #[local] Notation AA := (argH0_agree APH sp argv envp uid).

  (* [comment removed for export] *)
  Lemma main_check_sound : forall C HS HOLES,
    H_class_prop (iotab_of C) argv fs SINV ->
    (forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs') -> (forall h E fs', HOLES h E fs' []) ->
    holes_stmt BSEGS BOTH LIM HS SINV argH HOLES fs ->
    forall p cs s, CHK C HS cs p = COk s ->
    forall E R FULL model, cs_ok BSEGS BOTH LIM SINV argH fs E cs R FULL model ->
      srealizes BSEGS (cfg_of BSEGS R (pc cs) FULL model) (sd HOLES t_nil E (m_fs model) s).
  Proof.
    intros C HS HOLES HCL HOa HOn HOs p cs s Hchk E R FULL model HC.
    exact (check_sound BSEGS ITm ITm_ok BOTH NX0 LIM HS
                  (XNM (iotab_of C)) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of C))
                  Iwx Ihull Ihok Ishok Inx0 SINV argH AH AT AA SF SA
                  HOLES HOa HOn fs KCm
                  Msys Mbrk2 Mbrk2s Mmmap2 Mmmapin Mmprotect2 Mexit Mx Mjoin Mjoin_ok
                  (Mxn _ HCL) Mxe (Mxb _ HCL) HOs
                  FUELm BFUELm None p cs s Hchk E R FULL model t_nil HC I eq_refl).
  Qed.

  (* [comment removed for export] *)
  Lemma main_check_sound_M : forall C HS HOLES b v h st,
    H_class_prop (iotab_of C) argv fs SINV ->
    (forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs') -> (forall h E fs', HOLES h E fs' []) ->
    holes_stmt BSEGS BOTH LIM HS SINV argH HOLES fs ->
    forall p cs s, CHKL C HS cs p (Some (MC b v h st)) = COk s ->
    forall E R FULL model, cs_ok BSEGS BOTH LIM SINV argH fs E cs R FULL model ->
    (NX0 <= b)%N -> (v < b)%N ->
    (forall E' R' F' m', env_agree NX0 E E' -> cs_ok BSEGS BOTH LIM SINV argH fs E' st R' F' m' ->
       bv_unsigned (ev E v) < bv_unsigned (ev E' v) -> m_fs m' = m_fs model ->
       srealizes BSEGS (cfg_of BSEGS R' (pc st) F' m') (HOLES h E' (m_fs model))) ->
    srealizes BSEGS (cfg_of BSEGS R (pc cs) FULL model) (sd HOLES t_nil E (m_fs model) s).
  Proof.
    intros C HS HOLES b v h st HCL HOa HOn HOs p cs s Hchk E R FULL model HC Hb Hv HM.
    exact (check_sound_M BSEGS ITm ITm_ok BOTH NX0 LIM HS
                  (XNM (iotab_of C)) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of C))
                  Iwx Ihull Ihok Ishok Inx0 SINV argH AH AT AA SF SA
                  HOLES HOa HOn fs KCm
                  Msys Mbrk2 Mbrk2s Mmmap2 Mmmapin Mmprotect2 Mexit Mx Mjoin Mjoin_ok
                  (Mxn _ HCL) Mxe (Mxb _ HCL) HOs
                  FUELm BFUELm p cs b v h st s Hchk E R FULL model t_nil HC eq_refl Hb Hv HM).
  Qed.

  (* [comment removed for export] *)
  Lemma cs_ok_main_facts : forall E cs R FULL model,
    cs_ok BSEGS BOTH LIM SINV argH fs E cs R FULL model ->
    (forall n, (n < 8)%N -> ev E n = ev (E0 APH sp rdraw brk0 argv envp uid hw) n)
    /\ eb E 1%nat = nth 0 argv [] /\ eb E 2%nat = nth 1 argv [] /\ m_fs model = fs
    /\ know_ok BSEGS E FULL (vfacts (variant_of c)).
  Proof.
    intros E cs R FULL model HC.
    pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as HS. pose proof HS as HS'.
    destruct HS as [[Hev _] [HB1 [HB2 _]]].
    refine (conj _ (conj HB1 (conj HB2 (conj (co_fs _ _ _ _ _ _ _ _ _ _ _ HC) (VF _ _ HS'))))).
    intros n Hn. apply Hev. unfold NX0. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cs_ok_pay_start : forall C E cs R FULL model,
    in_class C argv fs = true ->
    cs_ok BSEGS BOTH LIM SINV argH fs E cs R FULL model ->
    cs_ok BSEGS BOTH LIM SINV argH fs E (pay_start cs C) R FULL model.
  Proof.
    intros C E cs R FULL model HC HCS. unfold pay_start. apply cs_ok_set_kn; [exact HCS|]. apply Forall_app. split.
    - eapply facts_of_class_sound; [eassumption.. | ]. apply (cs_ok_main_facts E cs R FULL model HCS).
    - exact (co_know _ _ _ _ _ _ _ _ _ _ _ HCS).
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
    intros C HC. apply Bool.not_true_is_false. unfold class_empty. intros H. apply Bool.orb_prop in H as [H|H].
    - revert H. rewrite existsb_exists. intros (q & _ & H).
      apply Z.ltb_lt in H. pose proof (qbounds_sound C q HC). lia.
    - (* [comment removed for export] *)
      unfold room_infeasible in H.
      pose proof (qbounds_sound C QFlen HC) as BF. pose proof (qbounds_sound C QCfgLen HC) as BC. pose proof (qbounds_sound C QRoom HC) as BR.
      cbn [qval] in BF, BC, BR. rewrite room_eq in BR. unfold cfglen in BC, BR.
      apply Bool.orb_prop in H as [H|H]; apply Z.ltb_lt in H; lia.
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
  Lemma rtree_ok_vars : forall t r ch C, rtree_ok KCm BFUELm FUELm ITm r ch C t = true -> shape_vars_lt NX0 r = true.
  Proof.
    intros t. induction t as [p | C' t IHt | p HR RT IH] using rtree_ind2; intros r ch C HF.
    - cbn [rtree_ok] in HF. destruct (check _ _ _ _ _ _ _ _ _ _ _ _ _ _ p); [|discriminate]. apply andb_prop in HF as [_ H]. exact H.
    - cbn [rtree_ok] in HF. apply andb_prop in HF as [_ H]. exact (IHt r ch C' H).
    - rewrite rtree_ok_RPreS in HF. destruct (check _ _ _ _ _ _ _ _ _ _ _ _ _ _ p); [|discriminate].
      apply andb_prop in HF as [HF _]. apply andb_prop in HF as [HF _]. apply andb_prop in HF as [_ H]. exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma rtree_sound : forall t r ch C,
    rtree_ok KCm BFUELm FUELm ITm r ch C t = true -> in_class C argv fs = true ->
    forall E R FULL model,
      cs_ok BSEGS BOTH LIM SINV argH fs E ch R FULL model ->
      srealizes BSEGS (cfg_of BSEGS R (pc ch) FULL model) (sd HOLES0 t_nil E (m_fs model) r).
  Proof.
    induction t as [p | C' t IHt | p HR RT IH] using rtree_ind2; intros r ch C HT0 HC E R FULL model HCS.
    - cbn [rtree_ok] in HT0.
      destruct (check _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) as [s| ] eqn:Hchk; [|discriminate].
      apply andb_prop in HT0 as [Heq _]. apply shape_eqb_eq in Heq. subst s.
      pose proof (cs_ok_pay_start C E ch R FULL model HC HCS) as HC2.
      pose proof (in_class_H_class APH sp rdraw argv envp fs uid hw Hva Hfit C SINV HC SINVm_blob) as HCL.
      pose proof (main_check_sound C HS_none HOLES0 HCL HOLES0_agree HOLES0_nil HS_none_sound p _ r Hchk E R FULL model HC2) as RZ.
      unfold pay_start in RZ. rewrite pc_set_kn in RZ. exact RZ.
    - cbn [rtree_ok] in HT0.
      apply andb_prop in HT0 as [HLE H1]. exact (IHt r ch C' H1 (in_class_weaken C C' HLE HC) E R FULL model HCS).
    - (* [comment removed for export] *)
      rewrite rtree_ok_RPreS in HT0.
      destruct (check _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) as [s| ] eqn:Hchk; [|discriminate].
      apply andb_prop in HT0 as [HT0 HF]. apply andb_prop in HT0 as [HT0 Hcov]. apply andb_prop in HT0 as [Heq Hvars].
      apply shape_eqb_eq in Heq.
      (* [comment removed for export] *)
      assert (VARS : forall h r', rs_of HR h = Some r' -> shape_vars_lt NX0 r' = true).
      { intros h r' Hr. unfold rs_of in Hr. destruct (lookupT HR h) as [[r0 chj]|] eqn:Hl; [|discriminate].
        cbn [fst] in Hr. injection Hr as <-.
        unfold mcoverS in Hcov. pose proof Hcov as Hcov'. rewrite forallb_forall in Hcov'.
        specialize (Hcov' (h, (r0, chj)) (lookupT_In _ _ _ Hl)). cbn [fst] in Hcov'.
        destruct (lookupT RT h) as [t'|] eqn:Ht'; [|discriminate].
        pose proof HF as HF'. unfold rforest_ok in HF'. rewrite forallb_forall in HF'. specialize (HF' (h, t') (lookupT_In _ _ _ Ht')).
        cbn [fst snd] in HF'. rewrite Hl in HF'. exact (rtree_ok_vars t' r0 chj C HF'). }
      set (HOLESR := fun (h : nat) (E' : env) (fs' : Fs.Fs) =>
                       match rs_of HR h with Some r' => sd HOLES0 t_nil E' fs' r' | None => t_nil end).
      assert (HRa : forall h E1 E2 fs', env_agree NX0 E1 E2 -> HOLESR h E1 fs' = HOLESR h E2 fs').
      { intros h E1 E2 fs' Hag. unfold HOLESR. destruct (rs_of HR h) as [r'|] eqn:Hr; [|reflexivity].
        exact (sd_agree NX0 HOLES0 HOLES0_agree t_nil E1 E2 fs' r' Hag (VARS h r' Hr)). }
      assert (HRn : forall h E1 fs', HOLESR h E1 fs' []).
      { intros h E1 fs'. unfold HOLESR. destruct (rs_of HR h) as [r'|]; [|reflexivity].
        exact (sd_has_nil HOLES0 HOLES0_nil t_nil E1 fs' r' eq_refl). }
      assert (HRs : holes_stmt BSEGS BOTH LIM (hs_ofS HR) SINV argH HOLESR fs).
      { intros j chj Hj E1 R1 FULL1 model1 HC1.
        unfold hs_ofS in Hj. destruct (lookupT HR j) as [[rj chj']|] eqn:He; [|discriminate]. cbn [snd] in Hj. injection Hj as ->.
        unfold mcoverS in Hcov. pose proof Hcov as Hcov'. rewrite forallb_forall in Hcov'.
        specialize (Hcov' (j, (rj, chj)) (lookupT_In _ _ _ He)). cbn [fst] in Hcov'.
        destruct (lookupT RT j) as [t'|] eqn:Ht'; [|discriminate].
        pose proof HF as HF'. unfold rforest_ok in HF'. rewrite forallb_forall in HF'. specialize (HF' (j, t') (lookupT_In _ _ _ Ht')).
        cbn [fst snd] in HF'. rewrite He in HF'.
        unfold HOLESR, rs_of. rewrite He. cbn [fst].
        exact (IH j t' (lookupT_In _ _ _ Ht') rj chj C HF' HC E1 R1 FULL1 model1 HC1). }
      pose proof (cs_ok_pay_start C E ch R FULL model HC HCS) as HC2.
      pose proof (in_class_H_class APH sp rdraw argv envp fs uid hw Hva Hfit C SINV HC SINVm_blob) as HCL.
      pose proof (main_check_sound C (hs_ofS HR) HOLESR HCL HRa HRn HRs p _ s Hchk E R FULL model HC2) as RZ.
      unfold pay_start in RZ. rewrite pc_set_kn in RZ.
      eapply srz_conseq; [exact RZ|]. rewrite <- Heq.
      apply (sd_subst_holes HOLESR HOLES0 t_nil E (m_fs model) (rs_of HR) s).
      intros h. unfold HOLESR. destruct (rs_of HR h); apply t_eq_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma rforest_vars : forall HR C PT h r,
    mcoverS HR PT = true -> rforest_ok KCm BFUELm FUELm ITm HR C PT = true -> rs_of HR h = Some r -> shape_vars_lt NX0 r = true.
  Proof.
    intros HR C PT h r Hcov HF Hr. unfold rs_of in Hr. destruct (lookupT HR h) as [[r' chj]|] eqn:Hl; [|discriminate].
    cbn [fst] in Hr. injection Hr as <-.
    unfold mcoverS in Hcov. rewrite forallb_forall in Hcov. specialize (Hcov (h, (r', chj)) (lookupT_In _ _ _ Hl)). cbn [fst] in Hcov.
    destruct (lookupT PT h) as [t|] eqn:Ht; [|discriminate].
    unfold rforest_ok in HF. rewrite forallb_forall in HF. specialize (HF (h, t) (lookupT_In _ _ _ Ht)). cbn [fst snd] in HF.
    rewrite Hl in HF. exact (rtree_ok_vars t r' chj C HF).
  Qed.

  (* [comment removed for export] *)
  Theorem mtree_sound : forall t lo hi ch C,
    mtree_ok KCm BFUELm FUELm ITm lo hi ch C t = true -> in_class C argv fs = true ->
    (lo <= mtree_lvl t)%nat /\ (mtree_lvl t <= hi)%nat /\
    forall E R FULL model,
      cs_ok BSEGS BOTH LIM SINV argH fs E ch R FULL model ->
      srealizes BSEGS (cfg_of BSEGS R (pc ch) FULL model) (t_res (mtree_lvl t) argv fs).
  Proof.
    induction t as [L p | L p HT PT IH | q mid le gt IHle IHgt | e mid le gt IHle IHgt | C' t IHt | L | L p HR PT | L p HT PT HR RT IH
                    | L p b v h HT PT IH] using mtree_ind2; intros lo hi ch C HT0 HC.
    - (* [comment removed for export] *)
      cbn [mtree_ok] in HT0. apply andb_prop in HT0 as [HL HT0]. apply andb_prop in HL as [HL1 HL2].
      apply Nat.leb_le in HL1. apply Nat.leb_le in HL2. cbn [mtree_lvl lvl_shape lshape_lvl]. split; [exact HL1|]. split; [exact HL2|].
      intros E R FULL model HCS.
      destruct (check _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) as [s| ] eqn:Hchk; [|discriminate].
      pose proof (cs_ok_pay_start C E ch R FULL model HC HCS) as HC2.
      destruct (cs_ok_main_facts E _ R FULL model HC2) as (Hev & HB1 & HB2 & Hfs & HVF).
      pose proof (in_class_H_class APH sp rdraw argv envp fs uid hw Hva Hfit C SINV HC SINVm_blob) as HCL.
      pose proof (main_check_sound C HS_none HOLES0 HCL HOLES0_agree HOLES0_nil HS_none_sound p _ s Hchk E R FULL model HC2) as RZ.
      rewrite Hfs in RZ. unfold pay_start in RZ. rewrite pc_set_kn in RZ.
      eapply srz_conseq; [exact RZ|].
      exact (class_pay_sound APH sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit BSEGS L C s E _ HOLES0 t_nil HC HT0 Hev HB1 HB2 HVF).
    - (* [comment removed for export] *)
      rewrite mtree_ok_MPre in HT0. apply andb_prop in HT0 as [HL HT0]. apply andb_prop in HL as [HL1 HL2].
      apply Nat.leb_le in HL1. apply Nat.leb_le in HL2. cbn [mtree_lvl lvl_shape lshape_lvl]. split; [exact HL1|]. split; [exact HL2|].
      intros E R FULL model HCS.
      destruct (check _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) as [s| ] eqn:Hchk; [|discriminate].
      apply andb_prop in HT0 as [HT0 HF]. apply andb_prop in HT0 as [Hseg Hcov].
      (* [comment removed for export] *)
      set (HOLESL := fun (h : nat) (E' : env) (fs' : Fs.Fs) =>
                       match lookupT PT h with Some t' => t_res (mtree_lvl t') argv fs' | None => t_nil end).
      assert (HLa : forall h E1 E2 fs', env_agree NX0 E1 E2 -> HOLESL h E1 fs' = HOLESL h E2 fs') by reflexivity.
      assert (HLn : forall h E1 fs', HOLESL h E1 fs' []).
      { intros h E1 fs'. unfold HOLESL. destruct (lookupT PT h); [apply t_res_nil | reflexivity]. }
      assert (HLs : holes_stmt BSEGS BOTH LIM (hs_of HT) SINV argH HOLESL fs).
      { intros j chj Hj E1 R1 FULL1 model1 HC1.
        unfold hs_of in Hj. destruct (ht_of HT j) as [[Lj chj']|] eqn:He; [|discriminate]. cbn [snd] in Hj. injection Hj as ->.
        destruct (mcover_sound HT PT j _ Hcov He) as (t' & Ht').
        pose proof (mforest_ok_sound KCm BFUELm FUELm ITm L HT C PT j t' _ HF (lookupT_In _ _ _ Ht') He) as Hok. cbn [fst snd] in Hok.
        destruct (IH j t' (lookupT_In _ _ _ Ht') L Lj chj C Hok HC) as (_ & _ & RZ).
        unfold HOLESL. rewrite Ht', (co_fs _ _ _ _ _ _ _ _ _ _ _ HC1). exact (RZ E1 R1 FULL1 model1 HC1). }
      pose proof (cs_ok_pay_start C E ch R FULL model HC HCS) as HC2.
      destruct (cs_ok_main_facts E _ R FULL model HC2) as (Hev & HB1 & HB2 & Hfs & HVF).
      pose proof (in_class_H_class APH sp rdraw argv envp fs uid hw Hva Hfit C SINV HC SINVm_blob) as HCL.
      pose proof (main_check_sound C (hs_of HT) HOLESL HCL HLa HLn HLs p _ s Hchk E R FULL model HC2) as RZ.
      rewrite Hfs in RZ. unfold pay_start in RZ. rewrite pc_set_kn in RZ.
      eapply srz_conseq; [exact RZ|].
      eapply (class_seg_sound APH sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit BSEGS (lv_of HT) L C s E _ HOLESL t_nil HC Hseg Hev HB1 HB2 HVF).
      (* [comment removed for export] *)
      intros j Lj Hlv. unfold lv_of in Hlv. destruct (ht_of HT j) as [[Lj' chj]|] eqn:He; [|discriminate]. cbn [fst] in Hlv. injection Hlv as ->.
      destruct (mcover_sound HT PT j _ Hcov He) as (t' & Ht').
      pose proof (mforest_ok_sound KCm BFUELm FUELm ITm L HT C PT j t' _ HF (lookupT_In _ _ _ Ht') He) as Hok. cbn [fst snd] in Hok.
      destruct (IH j t' (lookupT_In _ _ _ Ht') L Lj chj C Hok HC) as (H1 & H2 & _).
      exists (mtree_lvl t'). split; [exact H1|]. split; [exact H2|]. unfold HOLESL. rewrite Ht'. apply t_eq_refl.
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
      intros E R FULL model HCS.
      pose proof (u64_range (edenot E e)) as He. pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HCS) as HK.
      assert (HB : fst (ebounds (kn ch) e) <= uE E e <= snd (ebounds (kn ch) e)).
      { unfold ebounds. destruct (erange (kn ch) e) as [[blo bhi]|] eqn:Her; cbn [fst snd].
        - exact (erange_sound BSEGS E _ (kn ch) e blo bhi HK Her).
        - unfold uE, two64. lia. }
      destruct (Z.leb_spec (uE E e) mid) as [Hm|Hm].
      + apply (RZle E R FULL model). unfold mcase_lo. apply cs_ok_set_kn; [exact HCS|].
        constructor; [cbn [kentry_ok]; unfold uE in *; lia | exact HK].
      + rewrite <- Llo, Lhi. apply (RZgt E R FULL model). unfold mcase_hi. apply cs_ok_set_kn; [exact HCS|].
        constructor; [cbn [kentry_ok]; unfold uE, two64 in *; lia | exact HK].
    - (* [comment removed for export] *)
      cbn [mtree_ok] in HT0. apply andb_prop in HT0 as [HLE H1].
      exact (IHt lo hi ch C' H1 (in_class_weaken C C' HLE HC)).
    - (* [comment removed for export] *)
      cbn [mtree_ok] in HT0. apply andb_prop in HT0 as [_ HE]. rewrite (in_class_nonempty C HC) in HE. discriminate HE.
    - (* [comment removed for export] *)
      cbn [mtree_ok] in HT0. apply andb_prop in HT0 as [HL HT0]. apply andb_prop in HL as [HL1 HL2].
      apply Nat.leb_le in HL1. apply Nat.leb_le in HL2. cbn [mtree_lvl lvl_shape lshape_lvl]. split; [exact HL1|]. split; [exact HL2|].
      intros E R FULL model HCS.
      destruct (check _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) as [s| ] eqn:Hchk; [|discriminate].
      apply andb_prop in HT0 as [HT0 HF]. apply andb_prop in HT0 as [Hpay Hcov].
      set (HOLESR := fun (h : nat) (E' : env) (fs' : Fs.Fs) =>
                       match rs_of HR h with Some r => sd HOLES0 t_nil E' fs' r | None => t_nil end).
      assert (HRa : forall h E1 E2 fs', env_agree NX0 E1 E2 -> HOLESR h E1 fs' = HOLESR h E2 fs').
      { intros h E1 E2 fs' Hag. unfold HOLESR. destruct (rs_of HR h) as [r|] eqn:Hr; [|reflexivity].
        exact (sd_agree NX0 HOLES0 HOLES0_agree t_nil E1 E2 fs' r Hag (rforest_vars HR C PT h r Hcov HF Hr)). }
      assert (HRn : forall h E1 fs', HOLESR h E1 fs' []).
      { intros h E1 fs'. unfold HOLESR. destruct (rs_of HR h) as [r|]; [|reflexivity].
        exact (sd_has_nil HOLES0 HOLES0_nil t_nil E1 fs' r eq_refl). }
      assert (HRs : holes_stmt BSEGS BOTH LIM (hs_ofS HR) SINV argH HOLESR fs).
      { intros j chj Hj E1 R1 FULL1 model1 HC1.
        unfold hs_ofS in Hj. destruct (lookupT HR j) as [[rj chj']|] eqn:He; [|discriminate]. cbn [snd] in Hj. injection Hj as ->.
        unfold mcoverS in Hcov. pose proof Hcov as Hcov'. rewrite forallb_forall in Hcov'.
        specialize (Hcov' (j, (rj, chj)) (lookupT_In _ _ _ He)). cbn [fst] in Hcov'.
        destruct (lookupT PT j) as [t'|] eqn:Ht'; [|discriminate].
        pose proof HF as HF'. unfold rforest_ok in HF'. rewrite forallb_forall in HF'. specialize (HF' (j, t') (lookupT_In _ _ _ Ht')).
        cbn [fst snd] in HF'. rewrite He in HF'.
        unfold HOLESR, rs_of. rewrite He. cbn [fst].
        exact (rtree_sound t' rj chj C HF' HC E1 R1 FULL1 model1 HC1). }
      pose proof (cs_ok_pay_start C E ch R FULL model HC HCS) as HC2.
      destruct (cs_ok_main_facts E _ R FULL model HC2) as (Hev & HB1 & HB2 & Hfs & HVF).
      pose proof (in_class_H_class APH sp rdraw argv envp fs uid hw Hva Hfit C SINV HC SINVm_blob) as HCL.
      pose proof (main_check_sound C (hs_ofS HR) HOLESR HCL HRa HRn HRs p _ s Hchk E R FULL model HC2) as RZ.
      rewrite Hfs in RZ. unfold pay_start in RZ. rewrite pc_set_kn in RZ.
      eapply srz_conseq; [exact RZ|].
      eapply t_eq_trans; [apply (sd_subst_holes HOLESR HOLES0 t_nil E fs (rs_of HR) s) |].
      { intros h. unfold HOLESR. destruct (rs_of HR h); apply t_eq_refl. }
      exact (class_pay_sound APH sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit BSEGS L C _ E _ HOLES0 t_nil HC Hpay Hev HB1 HB2 HVF).
    - (* [comment removed for export] *)
      rewrite mtree_ok_MPreX in HT0. apply andb_prop in HT0 as [HL HT0]. apply andb_prop in HL as [HL1 HL2].
      apply Nat.leb_le in HL1. apply Nat.leb_le in HL2. cbn [mtree_lvl lvl_shape lshape_lvl]. split; [exact HL1|]. split; [exact HL2|].
      intros E R FULL model HCS.
      destruct (check _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) as [s| ] eqn:Hchk; [|discriminate].
      apply andb_prop in HT0 as [HT0 HHF]. apply andb_prop in HT0 as [HT0 HRF]. apply andb_prop in HT0 as [HT0 HcovS].
      apply andb_prop in HT0 as [HT0 HF]. apply andb_prop in HT0 as [Hseg Hcov].
      set (HOLESL := fun (h : nat) (E' : env) (fs' : Fs.Fs) =>
                       match ht_of HT h with
                       | Some _ => match lookupT PT h with Some t' => t_res (mtree_lvl t') argv fs' | None => t_nil end
                       | None => t_nil
                       end).
      set (HOLESX := fun (h : nat) (E' : env) (fs' : Fs.Fs) =>
                       match ht_of HT h with
                       | Some _ => HOLESL h E' fs'
                       | None => match rs_of HR h with Some r => sd HOLES0 t_nil E' fs' r | None => t_nil end
                       end).
      assert (HXa : forall h E1 E2 fs', env_agree NX0 E1 E2 -> HOLESX h E1 fs' = HOLESX h E2 fs').
      { intros h E1 E2 fs' Hag. unfold HOLESX. destruct (ht_of HT h); [reflexivity|].
        destruct (rs_of HR h) as [r|] eqn:Hr; [|reflexivity].
        exact (sd_agree NX0 HOLES0 HOLES0_agree t_nil E1 E2 fs' r Hag (rforest_vars HR C RT h r HcovS HRF Hr)). }
      assert (HXn : forall h E1 fs', HOLESX h E1 fs' []).
      { intros h E1 fs'. unfold HOLESX, HOLESL. destruct (ht_of HT h).
        - destruct (lookupT PT h); [apply t_res_nil | reflexivity].
        - destruct (rs_of HR h) as [r|]; [|reflexivity]. exact (sd_has_nil HOLES0 HOLES0_nil t_nil E1 fs' r eq_refl). }
      assert (HXs : holes_stmt BSEGS BOTH LIM (hs_ofX HT HR) SINV argH HOLESX fs).
      { intros j chj Hj E1 R1 FULL1 model1 HC1.
        unfold hs_ofX in Hj. destruct (ht_of HT j) as [[Lj chj']|] eqn:He.
        - cbn [snd] in Hj. injection Hj as ->.
          destruct (mcover_sound HT PT j _ Hcov He) as (t' & Ht').
          pose proof (mforest_ok_sound KCm BFUELm FUELm ITm L HT C PT j t' _ HF (lookupT_In _ _ _ Ht') He) as Hok. cbn [fst snd] in Hok.
          destruct (IH j t' (lookupT_In _ _ _ Ht') L Lj chj C Hok HC) as (_ & _ & RZ).
          unfold HOLESX, HOLESL. rewrite He, Ht', (co_fs _ _ _ _ _ _ _ _ _ _ _ HC1). exact (RZ E1 R1 FULL1 model1 HC1).
        - unfold hs_ofS in Hj. destruct (lookupT HR j) as [[rj chj']|] eqn:Hr; [|discriminate]. cbn [snd] in Hj. injection Hj as ->.
          unfold mcoverS in HcovS. pose proof HcovS as Hcov'. rewrite forallb_forall in Hcov'.
          specialize (Hcov' (j, (rj, chj)) (lookupT_In _ _ _ Hr)). cbn [fst] in Hcov'.
          destruct (lookupT RT j) as [t'|] eqn:Ht'; [|discriminate].
          pose proof HRF as HF'. unfold rforest_ok in HF'. rewrite forallb_forall in HF'. specialize (HF' (j, t') (lookupT_In _ _ _ Ht')).
          cbn [fst snd] in HF'. rewrite Hr in HF'.
          unfold HOLESX, rs_of. rewrite He, Hr. cbn [fst].
          exact (rtree_sound t' rj chj C HF' HC E1 R1 FULL1 model1 HC1). }
      pose proof (cs_ok_pay_start C E ch R FULL model HC HCS) as HC2.
      destruct (cs_ok_main_facts E _ R FULL model HC2) as (Hev & HB1 & HB2 & Hfs & HVF).
      pose proof (in_class_H_class APH sp rdraw argv envp fs uid hw Hva Hfit C SINV HC SINVm_blob) as HCL.
      pose proof (main_check_sound C (hs_ofX HT HR) HOLESX HCL HXa HXn HXs p _ s Hchk E R FULL model HC2) as RZ.
      rewrite Hfs in RZ. unfold pay_start in RZ. rewrite pc_set_kn in RZ.
      eapply srz_conseq; [exact RZ|].
      eapply t_eq_trans; [apply (sd_subst_holes HOLESX HOLESL t_nil E fs (rs_ofX HT HR) s) |].
      { intros h. unfold rs_ofX, HOLESX. destruct (ht_of HT h) as [e|] eqn:Eh; [apply t_eq_refl|].
        destruct (rs_of HR h) as [r|] eqn:Er.
        - unfold rs_of in Er. destruct (lookupT HR h) as [[r' chr]|] eqn:Hl; [|discriminate]. cbn [fst] in Er. injection Er as <-.
          unfold hr_hole_free in HHF. rewrite forallb_forall in HHF. specialize (HHF (h, (r', chr)) (lookupT_In _ _ _ Hl)). cbn [fst snd] in HHF.
          rewrite (sd_hole_free HOLES0 HOLESL t_nil E fs r' HHF). apply t_eq_refl.
        - unfold HOLESL. rewrite Eh. apply t_eq_refl. }
      eapply (class_seg_sound APH sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit BSEGS (lv_of HT) L C _ E _ HOLESL t_nil HC Hseg Hev HB1 HB2 HVF).
      intros j Lj Hlv. unfold lv_of in Hlv. destruct (ht_of HT j) as [[Lj' chj]|] eqn:He; [|discriminate]. cbn [fst] in Hlv. injection Hlv as ->.
      destruct (mcover_sound HT PT j _ Hcov He) as (t' & Ht').
      pose proof (mforest_ok_sound KCm BFUELm FUELm ITm L HT C PT j t' _ HF (lookupT_In _ _ _ Ht') He) as Hok. cbn [fst snd] in Hok.
      destruct (IH j t' (lookupT_In _ _ _ Ht') L Lj chj C Hok HC) as (H1 & H2 & _).
      exists (mtree_lvl t'). split; [exact H1|]. split; [exact H2|]. unfold HOLESL. rewrite He, Ht'. apply t_eq_refl.
    - (* [comment removed for export] *)
      rewrite mtree_ok_MLoop in HT0. apply andb_prop in HT0 as [HL HT0]. apply andb_prop in HL as [HL Hh].
      apply andb_prop in HL as [HL Hv]. apply andb_prop in HL as [HL Hb]. apply andb_prop in HL as [HL1 HL2].
      apply Nat.leb_le in HL1. apply Nat.leb_le in HL2. apply N.leb_le in Hb. apply N.ltb_lt in Hv.
      destruct (ht_of HT h) as [eh|] eqn:Hhn; [discriminate Hh|]. clear Hh.
      cbn [mtree_lvl lvl_shape lshape_lvl]. split; [exact HL1|]. split; [exact HL2|].
      destruct (check _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) as [s| ] eqn:Hchk; [|discriminate].
      apply andb_prop in HT0 as [HT0 HF]. apply andb_prop in HT0 as [Hseg Hcov].
      (* [comment removed for export] *)
      set (HOLESL := fun (h' : nat) (E' : env) (fs' : Fs.Fs) =>
                       if Nat.eqb h' h then t_res L argv fs'
                       else match lookupT PT h' with Some t' => t_res (mtree_lvl t') argv fs' | None => t_nil end).
      assert (HLa : forall h' E1 E2 fs', env_agree NX0 E1 E2 -> HOLESL h' E1 fs' = HOLESL h' E2 fs') by reflexivity.
      assert (HLn : forall h' E1 fs', HOLESL h' E1 fs' []).
      { intros h' E1 fs'. unfold HOLESL. destruct (Nat.eqb h' h); [apply t_res_nil|].
        destruct (lookupT PT h'); [apply t_res_nil | reflexivity]. }
      assert (HLs : holes_stmt BSEGS BOTH LIM (hs_of HT) SINV argH HOLESL fs).
      { intros j chj Hj E1 R1 FULL1 model1 HC1.
        unfold hs_of in Hj. destruct (ht_of HT j) as [[Lj chj']|] eqn:He; [|discriminate]. cbn [snd] in Hj. injection Hj as ->.
        assert (Hjh : Nat.eqb j h = false).
        { apply Nat.eqb_neq. intros ->. rewrite Hhn in He. discriminate He. }
        destruct (mcover_sound HT PT j _ Hcov He) as (t' & Ht').
        pose proof (mforest_ok_sound KCm BFUELm FUELm ITm L HT C PT j t' _ HF (lookupT_In _ _ _ Ht') He) as Hok. cbn [fst snd] in Hok.
        destruct (IH j t' (lookupT_In _ _ _ Ht') L Lj chj C Hok HC) as (_ & _ & RZ).
        unfold HOLESL. rewrite Hjh, Ht', (co_fs _ _ _ _ _ _ _ _ _ _ _ HC1). exact (RZ E1 R1 FULL1 model1 HC1). }
      pose proof (in_class_H_class APH sp rdraw argv envp fs uid hw Hva Hfit C SINV HC SINVm_blob) as HCL.
      (* [comment removed for export] *)
      assert (HHL : forall j Lj, lv_of ((h, (L, ch)) :: HT) j = Some Lj ->
                 exists L'', (L <= L'')%nat /\ (L'' <= Lj)%nat /\ t_eq (HOLESL j (E0 APH sp rdraw brk0 argv envp uid hw) fs) (t_res L'' argv fs)).
      { intros j Lj Hlv. unfold lv_of in Hlv. cbn [ht_of] in Hlv. destruct (Nat.eqb_spec h j) as [<-|Hne].
        - cbn [fst] in Hlv. injection Hlv as <-. exists L. split; [lia|]. split; [lia|]. unfold HOLESL. rewrite Nat.eqb_refl. apply t_eq_refl.
        - destruct (ht_of HT j) as [[Lj' chj]|] eqn:He; [|discriminate]. cbn [fst] in Hlv. injection Hlv as ->.
          destruct (mcover_sound HT PT j _ Hcov He) as (t' & Ht').
          pose proof (mforest_ok_sound KCm BFUELm FUELm ITm L HT C PT j t' _ HF (lookupT_In _ _ _ Ht') He) as Hok. cbn [fst snd] in Hok.
          destruct (IH j t' (lookupT_In _ _ _ Ht') L Lj chj C Hok HC) as (H1 & H2 & _).
          exists (mtree_lvl t'). split; [exact H1|]. split; [exact H2|]. unfold HOLESL.
          assert (Hjh : Nat.eqb j h = false) by (apply Nat.eqb_neq; intros ->; apply Hne; reflexivity).
          rewrite Hjh, Ht'. apply t_eq_refl. }
      (* [comment removed for export] *)
      assert (IND : forall n : nat, forall E R FULL model,
                 cs_ok BSEGS BOTH LIM SINV argH fs E ch R FULL model ->
                 (Z.to_nat (2 ^ 64 - bv_unsigned (ev E v)) <= n)%nat ->
                 srealizes BSEGS (cfg_of BSEGS R (pc ch) FULL model) (t_res L argv fs)).
      { induction n as [|n IHn]; intros E R FULL model HCS Hn.
        - exfalso. pose proof (u64_range (ev E v)) as Hr. lia.
        - pose proof (cs_ok_pay_start C E ch R FULL model HC HCS) as HC2.
          destruct (cs_ok_main_facts E _ R FULL model HC2) as (Hev & HB1 & HB2 & Hfs & HVF).
          pose proof (main_check_sound_M C (hs_of HT) HOLESL b v h ch HCL HLa HLn HLs p _ s Hchk E R FULL model HC2 Hb Hv) as RZ.
          assert (HM : forall E' R' F' m', env_agree NX0 E E' -> cs_ok BSEGS BOTH LIM SINV argH fs E' ch R' F' m' ->
                         bv_unsigned (ev E v) < bv_unsigned (ev E' v) -> m_fs m' = m_fs model ->
                         srealizes BSEGS (cfg_of BSEGS R' (pc ch) F' m') (HOLESL h E' (m_fs model))).
          { intros E' R' F' m' _ HC' Hlt Hfs'. unfold HOLESL. rewrite Nat.eqb_refl. rewrite Hfs.
            apply (IHn E' R' F' m' HC'). pose proof (u64_range (ev E' v)). pose proof (u64_range (ev E v)). lia. }
          specialize (RZ HM). rewrite Hfs in RZ. unfold pay_start in RZ. rewrite pc_set_kn in RZ.
          eapply srz_conseq; [exact RZ|].
          eapply (class_seg_sound APH sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit BSEGS (lv_of ((h, (L, ch)) :: HT)) L C s E _
                    HOLESL t_nil HC Hseg Hev HB1 HB2 HVF).
          intros j Lj Hlv. destruct (HHL j Lj Hlv) as (L'' & H1 & H2 & H3). exists L''. split; [exact H1|]. split; [exact H2|].
          exact H3. }
      intros E R FULL model HCS. exact (IND _ E R FULL model HCS (Nat.le_refl _)).
  Qed.

  (* [comment removed for export] *)
  Definition HOLESM (h : nat) (E : env) (fs' : Fs.Fs) : TSet := spec argv fs'.
  Lemma HOLESM_agree : forall h E E' fs', env_agree NX0 E E' -> HOLESM h E fs' = HOLESM h E' fs'.
  Proof. reflexivity. Qed.
  Lemma HOLESM_nil : forall h E fs', HOLESM h E fs' [].
  Proof. intros. apply spec_nil. Qed.

  #[local] Notation TREE_OK h := (mtree_ok KCm BFUELm FUELm ITm 0 0 (HSA HS_asan h)).

  Variable TREE : nat -> nat -> mtree.
  Hypothesis TREES : forall h ch i, HS_asan h = Some ch -> (i < 6)%nat -> TREE_OK h (root_class i) (TREE h i) = true.

  Theorem main_holes : holes_stmt BSEGS BOTH LIM HS_asan SINV0' argH HOLESM fs.
  Proof.
    intros h ch Hh E R FULL model HC.
    assert (Ech : ch = HSA HS_asan h) by (unfold HSA; rewrite Hh; reflexivity).
    rewrite Ech in HC |- *.
    (* [comment removed for export] *)
    pose proof (cs_ok_reblob BSEGS BOTH APH sp rdraw brk0 argv envp uid hw c LIM fs E (HSA HS_asan h) R FULL model
                  (eq_ind ch (fun x => acs_noblob x = true) (HSA_noblob h ch Hh) _ Ech) HC) as HC1.
    unfold HOLESM. rewrite (co_fs _ _ _ _ _ _ _ _ _ _ _ HC).
    destruct (root_cover argv fs Hva) as (i & Hi & HCi).
    destruct (mtree_sound (TREE h i) 0 0 (HSA HS_asan h) (root_class i) (TREES h ch i Hh Hi) HCi) as (H1 & H2 & RZ).
    assert (HL : mtree_lvl (TREE h i) = 0%nat) by lia. rewrite HL in RZ. cbn [t_res] in RZ.
    exact (RZ _ R FULL model HC1).
  Qed.

End Main.
