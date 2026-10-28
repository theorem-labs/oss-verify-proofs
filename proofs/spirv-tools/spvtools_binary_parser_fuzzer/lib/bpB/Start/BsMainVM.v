(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BxSymExec3 BxSymExec3Sound BothPlanCore BothPlan BothPlanSound.
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition siv : Type := (lin * lin)%type.

Definition siv_den (E : env) (s : siv) : list (word * word) :=
  let lo := lden E (fst s) in let hi := lden E (snd s) in
  if lo <? hi then [(Z_to_bv 64 lo, Z_to_bv 64 (hi - lo))] else [].
Fixpoint sivs_den (E : env) (l : list siv) : list (word * word) :=
  match l with [] => [] | s :: r => siv_den E s ++ sivs_den E r end.

Definition siv_wf (E : env) (s : siv) : Prop := 0 <= lden E (fst s) /\ lden E (snd s) <= 2 ^ 64 /\ lden E (snd s) - lden E (fst s) < 2 ^ 64.

Definition lconst (c : Z) : lin := (c, []).
Definition lcat (x y : lin) : lin := (fst x + fst y, snd x ++ snd y).

Lemma tden_app : forall E a b, tden E (a ++ b) = tden E a + tden E b.
Proof. intros E a b. induction a as [|[k e] a IH]; cbn [tden app]; [lia|]. rewrite IH. lia. Qed.
Lemma lcat_den : forall E x y, lden E (lcat x y) = lden E x + lden E y.
Proof. intros E [c1 t1] [c2 t2]. unfold lcat, lden. cbn [fst snd]. rewrite tden_app. lia. Qed.
Lemma lconst_den : forall E c, lden E (lconst c) = c.
Proof. intros E c. unfold lconst, lden. cbn. lia. Qed.

Definition le_lin (kn : list kentry) (x y : lin) : bool :=
  lin_test kn (fst y - fst x) (lsub_e (snd y) (snd x)) (fun lo _ => 0 <=? lo).
Definition lt_lin (kn : list kentry) (x y : lin) : bool :=
  lin_test kn (fst y - fst x) (lsub_e (snd y) (snd x)) (fun lo _ => 0 <? lo).

Definition lin_ofx (kn : list kentry) (e : expr) : option lin :=
  if lin_nowrapR kn e then Some (lin_of e) else None.

Definition lin_ofa (kn : list kentry) (a : saddr) : option lin :=
  match lin_ofx kn (a_base a) with Some l => Some (lcat l (lconst (a_off a))) | None => None end.

Definition inside (kn : list kentry) (x : siv) (flo fhi : lin) : bool :=
  le_lin kn flo (fst x) && le_lin kn (snd x) fhi.

Definition lin_has (l : lin) (e : expr) : bool :=
  match e with ELit _ => true | _ => existsb (fun t => shares_var e (snd t)) (snd l) end.
Definition kdisj_pre (x r : siv) (b1 b2 : expr) : bool :=
  (lin_has (fst x) b1 && lin_has (fst r) b2) || (lin_has (fst x) b2 && lin_has (fst r) b1).

Definition kdisj1 (kn : list kentry) (x r : siv) (K : kentry) : bool :=
  match K with
  | KDisj a1 n1 a2 n2 =>
      if negb (kdisj_pre x r (a_base a1) (a_base a2)) then false else
      match lin_ofa kn a1, lin_ofx kn n1, lin_ofa kn a2, lin_ofx kn n2 with
      | Some f1, Some m1, Some f2, Some m2 =>
          let g1 := lcat f1 m1 in let g2 := lcat f2 m2 in
          (inside kn x f1 g1 && inside kn r f2 g2) || (inside kn x f2 g2 && inside kn r f1 g1)
      | _, _, _, _ => false
      end
  | _ => false
  end.
Definition kdisj (kn : list kentry) (x r : siv) : bool := existsb (kdisj1 kn x r) kn.

Definition disjoint_dec (kn : list kentry) (x r : siv) : bool :=
  le_lin kn (snd x) (fst r) || le_lin kn (snd r) (fst x) || kdisj kn x r.

Fixpoint drop_empty (kn : list kentry) (l : list siv) : list siv :=
  match l with
  | [] => []
  | s :: r => if le_lin kn (snd s) (fst s) then drop_empty kn r else s :: drop_empty kn r
  end.

Definition sym_sub1 (kn : list kentry) (r : siv) (x : siv) : option (list siv) :=
  if disjoint_dec kn x r then Some [x]
  else
    let a := fst x in let b := snd x in let lo := fst r in let hi := snd r in
    match (if le_lin kn lo b then Some lo else if le_lin kn b lo then Some b else None),
          (if le_lin kn a hi then Some hi else if le_lin kn hi a then Some a else None) with
    | Some mn, Some mx => Some (drop_empty kn [(a, mn); (mx, b)])
    | _, _ => None
    end.

Fixpoint sym_sub (kn : list kentry) (l : list siv) (r : siv) : option (list siv) :=
  match l with
  | [] => Some []
  | x :: l' => match sym_sub1 kn r x, sym_sub kn l' r with
               | Some p, Some q => Some (p ++ q)
               | _, _ => None
               end
  end.

Definition siv_of (kn : list kentry) (a n : expr) : option siv :=
  match lin_ofx kn a, lin_ofx kn n with
  | Some la, Some ln =>
      let r := (la, lcat la ln) in
      if lt_lin kn (fst r) (snd r) && le_lin kn (snd r) (lconst (2 ^ 64)) then Some r else None
  | _, _ => None
  end.

Definition sym_step (kn : list kentry) (op : vmop) (NL : list siv * list siv) : option (list siv * list siv) :=
  let (N, L) := NL in
  match op with
  | VNew k a n =>
      match siv_of kn a n with
      | Some r => Some ((if is_none_kind k then r :: N else N), (if is_lazy_kind k then r :: L else L))
      | None => None
      end
  | VFixIn nr pn a n =>
      match siv_of kn a n with
      | Some r => match sym_sub kn N r, sym_sub kn L r with
                  | Some N', Some L' => Some ((if pn then r :: N' else N'), (if nr then r :: L' else L'))
                  | _, _ => None
                  end
      | None => None
      end
  | VUnmap a n =>
      match siv_of kn a n with
      | Some r => match sym_sub kn N r, sym_sub kn L r with
                  | Some N', Some L' => Some (N', L')
                  | _, _ => None
                  end
      | None => None
      end
  | VProt a n =>
      match siv_of kn a n with
      | Some r => match sym_sub kn N r with Some N' => Some (N', L) | None => None end
      | None => None
      end
  end.

Fixpoint sym_replay (kn : list kentry) (ops : list vmop) : option (list siv * list siv) :=
  match ops with
  | [] => Some ([], [])
  | op :: r => match sym_replay kn r with Some NL => sym_step kn op NL | None => None end
  end.

Section Sound.
  Variable segs : list Segment.
  Variable E : env.
  Variable M : word -> option byte.
  Variable kn : list kentry.
  Hypothesis KN : know_ok segs E M kn.

  Lemma le_lin_sound : forall x y, le_lin kn x y = true -> lden E x <= lden E y.
  Proof.
    intros [cx tx] [cy ty] H. unfold le_lin in H. cbn [fst snd] in H.
    apply (lin_test_sound segs E M kn) in H as (lo & hi & Ht & Hb); [|exact KN].
    apply Z.leb_le in Ht. rewrite lsub_e_sound in Hb. unfold lden. cbn [fst snd]. lia.
  Qed.
  Lemma lt_lin_sound : forall x y, lt_lin kn x y = true -> lden E x < lden E y.
  Proof.
    intros [cx tx] [cy ty] H. unfold lt_lin in H. cbn [fst snd] in H.
    apply (lin_test_sound segs E M kn) in H as (lo & hi & Ht & Hb); [|exact KN].
    apply Z.ltb_lt in Ht. rewrite lsub_e_sound in Hb. unfold lden. cbn [fst snd]. lia.
  Qed.

  Lemma lin_ofx_sound : forall e l, lin_ofx kn e = Some l -> uE E e = lden E l.
  Proof.
    intros e l H. unfold lin_ofx in H. destruct (lin_nowrapR kn e) eqn:Hw; [|discriminate]. injection H as <-.
    unfold uE. rewrite (lin_nowrapR_sound segs E M kn e KN Hw). unfold lden. reflexivity.
  Qed.
  Lemma lin_ofa_sound : forall a l, lin_ofa kn a = Some l -> estart E a = lden E l.
  Proof.
    intros [b k] l H. unfold lin_ofa in H. cbn [a_base a_off] in H.
    destruct (lin_ofx kn b) as [lb|] eqn:Hb; [|discriminate]. injection H as <-.
    rewrite lcat_den, lconst_den. unfold estart. cbn [a_base a_off]. rewrite <- (lin_ofx_sound b lb Hb). reflexivity.
  Qed.

  Lemma inside_sound : forall x f g, inside kn x f g = true -> lden E f <= lden E (fst x) /\ lden E (snd x) <= lden E g.
  Proof.
    intros x f g H. unfold inside in H. apply andb_prop in H as [H1 H2].
    split; [exact (le_lin_sound _ _ H1) | exact (le_lin_sound _ _ H2)].
  Qed.

  Lemma kdisj_sound : forall x r, kdisj kn x r = true ->
    lden E (snd x) <= lden E (fst r) \/ lden E (snd r) <= lden E (fst x).
  Proof.
    intros x r H. unfold kdisj in H. apply existsb_exists in H as [K [HK H]].
    pose proof (proj1 (Forall_forall _ _) KN K HK) as KD.
    destruct K; try discriminate H. cbn [kdisj1] in H. cbn [kentry_ok] in KD.
    destruct (negb (kdisj_pre x r (a_base a1) (a_base a2))); [discriminate|].
    destruct (lin_ofa kn a1) as [f1|] eqn:F1; [|discriminate].
    destruct (lin_ofx kn n1) as [m1|] eqn:M1; [|discriminate].
    destruct (lin_ofa kn a2) as [f2|] eqn:F2; [|discriminate].
    destruct (lin_ofx kn n2) as [m2|] eqn:M2; [|discriminate].
    pose proof (lin_ofa_sound a1 f1 F1) as E1. pose proof (lin_ofa_sound a2 f2 F2) as E2.
    pose proof (lin_ofx_sound n1 m1 M1) as N1. pose proof (lin_ofx_sound n2 m2 M2) as N2.
    unfold elenZ in KD. fold (uE E n1) in KD. fold (uE E n2) in KD. rewrite E1, E2, N1, N2 in KD.
    apply orb_prop in H as [H|H]; apply andb_prop in H as [Hx Hr];
      apply inside_sound in Hx as [Hx1 Hx2]; apply inside_sound in Hr as [Hr1 Hr2];
      rewrite lcat_den in Hx2, Hr2; lia.
  Qed.

  Lemma disjoint_dec_sound : forall x r, disjoint_dec kn x r = true ->
    lden E (snd x) <= lden E (fst r) \/ lden E (snd r) <= lden E (fst x).
  Proof.
    intros x r H. unfold disjoint_dec in H. apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|].
    - left. exact (le_lin_sound _ _ H).
    - right. exact (le_lin_sound _ _ H).
    - exact (kdisj_sound x r H).
  Qed.

  Lemma u_of_Z : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
  Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small. exact Hz. Qed.

  Lemma maps_subtract_app : forall l1 l2 lo hi, maps_subtract (l1 ++ l2) lo hi = maps_subtract l1 lo hi ++ maps_subtract l2 lo hi.
  Proof. intros l1 l2 lo hi. induction l1 as [|[a s] l1 IH]; cbn [maps_subtract app]; [reflexivity|]. rewrite IH, app_assoc. reflexivity. Qed.

  Lemma siv_den_empty : forall s, lden E (snd s) <= lden E (fst s) -> siv_den E s = [].
  Proof. intros s H. unfold siv_den. destruct (lden E (fst s) <? lden E (snd s)) eqn:C; [apply Z.ltb_lt in C; lia | reflexivity]. Qed.
  Lemma siv_den_full : forall s, lden E (fst s) < lden E (snd s) ->
    siv_den E s = [(Z_to_bv 64 (lden E (fst s)), Z_to_bv 64 (lden E (snd s) - lden E (fst s)))].
  Proof. intros s H. unfold siv_den. destruct (lden E (fst s) <? lden E (snd s)) eqn:C; [reflexivity | apply Z.ltb_ge in C; lia]. Qed.

  Lemma drop_empty_den : forall l, sivs_den E (drop_empty kn l) = sivs_den E l.
  Proof.
    induction l as [|s l IH]; [reflexivity|]. cbn [drop_empty].
    destruct (le_lin kn (snd s) (fst s)) eqn:C; cbn [sivs_den]; rewrite IH; [|reflexivity].
    rewrite (siv_den_empty s (le_lin_sound _ _ C)). reflexivity.
  Qed.
  Lemma drop_empty_wf : forall l, Forall (siv_wf E) l -> Forall (siv_wf E) (drop_empty kn l).
  Proof.
    induction l as [|s l IH]; intros H; [constructor|]. cbn [drop_empty]. apply Forall_cons_iff in H as [H1 H2].
    destruct (le_lin kn (snd s) (fst s)); [exact (IH H2) | constructor; [exact H1 | exact (IH H2)]].
  Qed.

  Lemma sym_sub1_sound : forall r x p,
    siv_wf E x -> lden E (fst r) <= lden E (snd r) ->
    sym_sub1 kn r x = Some p ->
    maps_subtract (siv_den E x) (lden E (fst r)) (lden E (snd r)) = sivs_den E p /\ Forall (siv_wf E) p.
  Proof.
    intros r x p WF Hr H. unfold sym_sub1 in H.
    destruct WF as (W1 & W2 & W3).
    destruct (disjoint_dec kn x r) eqn:D.
    - injection H as <-. split; [|constructor; [split; [assumption|split; assumption] | constructor]].
      cbn [sivs_den]. rewrite app_nil_r.
      destruct (Z.lt_ge_cases (lden E (fst x)) (lden E (snd x))) as [NE|EM].
      + rewrite (siv_den_full x NE). cbn [maps_subtract]. rewrite app_nil_r. unfold iv_subtract.
        rewrite !u_of_Z by lia.
        pose proof (disjoint_dec_sound x r D) as DD.
        destruct DD as [DD|DD].
        * destruct (lden E (fst x) <? lden E (fst r)) eqn:C1; [|apply Z.ltb_ge in C1; lia].
          destruct (lden E (snd r) <? lden E (fst x) + (lden E (snd x) - lden E (fst x))) eqn:C2; [apply Z.ltb_lt in C2; lia|].
          cbn [app]. rewrite Z.min_l by lia. reflexivity.
        * destruct (lden E (fst x) <? lden E (fst r)) eqn:C1; [apply Z.ltb_lt in C1; lia|].
          destruct (lden E (snd r) <? lden E (fst x) + (lden E (snd x) - lden E (fst x))) eqn:C2; [|apply Z.ltb_ge in C2; lia].
          cbn [app]. rewrite Z.max_l by lia. do 2 f_equal. f_equal. lia.
      + rewrite (siv_den_empty x EM). reflexivity.
    - cbn [fst snd] in H.
      set (a := fst x) in *. set (b := snd x) in *. set (lo := fst r) in *. set (hi := snd r) in *.
      destruct (if le_lin kn lo b then Some lo else if le_lin kn b lo then Some b else None) as [mn|] eqn:MN; [|discriminate].
      destruct (if le_lin kn a hi then Some hi else if le_lin kn hi a then Some a else None) as [mx|] eqn:MX; [|discriminate].
      assert (HP : drop_empty kn [(a, mn); (mx, b)] = p) by congruence. clear H. rewrite <- HP.
      assert (HMN : lden E mn = Z.min (lden E b) (lden E lo) /\ lden E mn <= lden E b).
      { destruct (le_lin kn lo b) eqn:C1.
        - injection MN as <-. pose proof (le_lin_sound _ _ C1). rewrite Z.min_r by lia. lia.
        - destruct (le_lin kn b lo) eqn:C2; [|discriminate]. injection MN as <-. pose proof (le_lin_sound _ _ C2). rewrite Z.min_l by lia. lia. }
      assert (HMX : lden E mx = Z.max (lden E a) (lden E hi) /\ lden E a <= lden E mx).
      { destruct (le_lin kn a hi) eqn:C1.
        - injection MX as <-. pose proof (le_lin_sound _ _ C1). rewrite Z.max_r by lia. lia.
        - destruct (le_lin kn hi a) eqn:C2; [|discriminate]. injection MX as <-. pose proof (le_lin_sound _ _ C2). rewrite Z.max_l by lia. lia. }
      destruct HMN as [HMN HMN2]. destruct HMX as [HMX HMX2].
      split.
      2: { apply drop_empty_wf. constructor; [unfold siv_wf; cbn [fst snd]; lia|]. constructor; [unfold siv_wf; cbn [fst snd]; lia|]. constructor. }
      rewrite drop_empty_den. cbn [sivs_den]. rewrite app_nil_r.
      destruct (Z.lt_ge_cases (lden E a) (lden E b)) as [NE|EM].
      + rewrite (siv_den_full x NE). cbn [maps_subtract]. rewrite app_nil_r. unfold iv_subtract.
        fold a. fold b. rewrite !u_of_Z by lia.
        replace (lden E a + (lden E b - lden E a)) with (lden E b) by lia.
        f_equal.
        * unfold siv_den. cbn [fst snd]. rewrite HMN.
          destruct (lden E a <? lden E lo) eqn:C1.
          -- apply Z.ltb_lt in C1. destruct (lden E a <? Z.min (lden E b) (lden E lo)) eqn:C2; [|apply Z.ltb_ge in C2; lia].
             do 2 f_equal. f_equal. lia.
          -- apply Z.ltb_ge in C1. destruct (lden E a <? Z.min (lden E b) (lden E lo)) eqn:C2; [apply Z.ltb_lt in C2; lia|]. reflexivity.
        * unfold siv_den. cbn [fst snd]. rewrite HMX.
          destruct (lden E hi <? lden E b) eqn:C1.
          -- apply Z.ltb_lt in C1. destruct (Z.max (lden E a) (lden E hi) <? lden E b) eqn:C2; [|apply Z.ltb_ge in C2; lia]. reflexivity.
          -- apply Z.ltb_ge in C1. destruct (Z.max (lden E a) (lden E hi) <? lden E b) eqn:C2; [apply Z.ltb_lt in C2; lia|]. reflexivity.
      + rewrite (siv_den_empty x EM). cbn [maps_subtract].
        unfold siv_den. cbn [fst snd]. rewrite HMN, HMX.
        destruct (lden E a <? Z.min (lden E b) (lden E lo)) eqn:C1; [apply Z.ltb_lt in C1; lia|].
        destruct (Z.max (lden E a) (lden E hi) <? lden E b) eqn:C2; [apply Z.ltb_lt in C2; lia|]. reflexivity.
  Qed.

  Lemma sym_sub_sound : forall l r p,
    Forall (siv_wf E) l -> lden E (fst r) <= lden E (snd r) ->
    sym_sub kn l r = Some p ->
    maps_subtract (sivs_den E l) (lden E (fst r)) (lden E (snd r)) = sivs_den E p /\ Forall (siv_wf E) p.
  Proof.
    intros l r. induction l as [|x l IH]; intros p WF Hr H; cbn [sym_sub] in H.
    - injection H as <-. split; [reflexivity | constructor].
    - destruct (sym_sub1 kn r x) as [p1|] eqn:H1; [|discriminate].
      destruct (sym_sub kn l r) as [p2|] eqn:H2; [|discriminate]. injection H as <-.
      apply Forall_cons_iff in WF as [WFx WFl].
      destruct (sym_sub1_sound r x p1 WFx Hr H1) as [A1 B1].
      destruct (IH p2 WFl Hr eq_refl) as [A2 B2].
      cbn [sivs_den]. rewrite maps_subtract_app, A1, A2. split; [|apply Forall_app; split; assumption].
      clear. induction p1 as [|s p1 IH]; cbn [sivs_den app]; [reflexivity|]. rewrite <- IH, app_assoc. reflexivity.
  Qed.

  Lemma siv_of_sound : forall a n r, siv_of kn a n = Some r ->
    lden E (fst r) = uE E a /\ lden E (snd r) = uE E a + uE E n /\ 0 < uE E n /\ siv_wf E r
    /\ siv_den E r = [vm_iv E a n].
  Proof.
    intros a n r H. unfold siv_of in H.
    destruct (lin_ofx kn a) as [la|] eqn:La; [|discriminate]. destruct (lin_ofx kn n) as [ln|] eqn:Ln; [|discriminate].
    cbn [fst snd] in H.
    destruct (lt_lin kn la (lcat la ln) && le_lin kn (lcat la ln) (lconst (2 ^ 64))) eqn:C; [|discriminate].
    injection H as <-. apply andb_prop in C as [C1 C2]. cbn [fst snd].
    apply lt_lin_sound in C1. apply le_lin_sound in C2. rewrite lconst_den in C2. rewrite lcat_den in *.
    pose proof (lin_ofx_sound a la La) as Ea. pose proof (lin_ofx_sound n ln Ln) as En.
    pose proof (u64_range (edenot E a)) as Ra. pose proof (u64_range (edenot E n)) as Rn. unfold uE in Ea, En |- *.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold siv_wf; cbn [fst snd]; rewrite lcat_den; lia|].
    unfold siv_den. cbn [fst snd]. rewrite lcat_den.
    destruct (lden E la <? lden E la + lden E ln) eqn:C; [|apply Z.ltb_ge in C; lia].
    unfold vm_iv. rewrite <- Ea.
    replace (bv_unsigned (edenot E a) + lden E ln - bv_unsigned (edenot E a)) with (bv_unsigned (edenot E n)) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
  Qed.

  Lemma sym_step_sound : forall op N L N' L',
    Forall (siv_wf E) N -> Forall (siv_wf E) L ->
    sym_step kn op (N, L) = Some (N', L') ->
    vm_step E op (sivs_den E N) (sivs_den E L) = (sivs_den E N', sivs_den E L') /\ Forall (siv_wf E) N' /\ Forall (siv_wf E) L'.
  Proof.
    intros op N L N' L' WN WL H. destruct op as [k a n|nr pn a n|a n|a n]; cbn [sym_step] in H.
    - destruct (siv_of kn a n) as [r|] eqn:R; [|discriminate]. injection H as <- <-.
      destruct (siv_of_sound a n r R) as (R1 & R2 & R3 & R4 & R5).
      unfold vm_step. split; [|split; [destruct (is_none_kind k) | destruct (is_lazy_kind k)]; try constructor; assumption].
      destruct (is_none_kind k), (is_lazy_kind k); cbn [sivs_den]; rewrite ?R5; reflexivity.
    - destruct (siv_of kn a n) as [r|] eqn:R; [|discriminate].
      destruct (sym_sub kn N r) as [N1|] eqn:S1; [|discriminate]. destruct (sym_sub kn L r) as [L1|] eqn:S2; [|discriminate].
      injection H as <- <-. destruct (siv_of_sound a n r R) as (R1 & R2 & R3 & R4 & R5).
      destruct (sym_sub_sound N r N1 WN ltac:(lia) S1) as [A1 B1]. destruct (sym_sub_sound L r L1 WL ltac:(lia) S2) as [A2 B2].
      unfold vm_step, vm_lo, vm_hi. fold (uE E a). fold (uE E n). rewrite <- R2, <- R1, A1, A2.
      split; [|split; [destruct pn | destruct nr]; try constructor; assumption].
      destruct pn, nr; cbn [sivs_den]; rewrite ?R5; reflexivity.
    - destruct (siv_of kn a n) as [r|] eqn:R; [|discriminate].
      destruct (sym_sub kn N r) as [N1|] eqn:S1; [|discriminate]. destruct (sym_sub kn L r) as [L1|] eqn:S2; [|discriminate].
      injection H as <- <-. destruct (siv_of_sound a n r R) as (R1 & R2 & R3 & R4 & R5).
      destruct (sym_sub_sound N r N1 WN ltac:(lia) S1) as [A1 B1]. destruct (sym_sub_sound L r L1 WL ltac:(lia) S2) as [A2 B2].
      unfold vm_step, vm_lo, vm_hi. fold (uE E a). fold (uE E n). rewrite <- R2, <- R1, A1, A2. split; [reflexivity | split; assumption].
    - destruct (siv_of kn a n) as [r|] eqn:R; [|discriminate].
      destruct (sym_sub kn N r) as [N1|] eqn:S1; [|discriminate].
      injection H as <- <-. destruct (siv_of_sound a n r R) as (R1 & R2 & R3 & R4 & R5).
      destruct (sym_sub_sound N r N1 WN ltac:(lia) S1) as [A1 B1].
      unfold vm_step, vm_lo, vm_hi. fold (uE E a). fold (uE E n). rewrite <- R2, <- R1, A1. split; [reflexivity | split; assumption].
  Qed.

  Theorem sym_replay_sound : forall ops N L,
    sym_replay kn ops = Some (N, L) ->
    vm_replay E ops = (sivs_den E N, sivs_den E L) /\ Forall (siv_wf E) N /\ Forall (siv_wf E) L.
  Proof.
    induction ops as [|op ops IH]; intros N L H; cbn [sym_replay] in H.
    - injection H as <- <-. split; [reflexivity | split; constructor].
    - destruct (sym_replay kn ops) as [[N0 L0]|] eqn:H0; [|discriminate].
      destruct (IH N0 L0 eq_refl) as (A & WN & WL).
      cbn [vm_replay]. rewrite A. exact (sym_step_sound op N0 L0 N L WN WL H).
  Qed.
End Sound.

Definition is_arith (K : kentry) : bool :=
  match K with KRange _ _ _ | KAlign _ _ | KDisj _ _ _ _ => true | _ => false end.
Definition kn_arith (k : list kentry) : list kentry := List.filter is_arith k.

Lemma kn_arith_ok : forall segs E M k, know_ok segs E M k -> know_ok segs E M (kn_arith k).
Proof. intros segs E M k H. unfold kn_arith. apply incl_Forall with (l1 := k); [apply incl_filter | exact H]. Qed.

Lemma cs_ok_vm_closed :
  forall SEGS A LIMIT SINV argH FS0 E cs R FULL model N L,
    cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model ->
    sym_replay (kn_arith (kn cs)) (a_vmops cs) = Some (N, L) ->
    vm_noaccess (m_vmmaps model) = sivs_den E N /\ m_vm_lazy model = sivs_den E L
    /\ Forall (siv_wf E) N /\ Forall (siv_wf E) L.
Proof.
  intros SEGS A LIMIT SINV argH FS0 E cs R FULL model N L HC HR.
  pose proof (kn_arith_ok _ _ _ _ (co_know _ _ _ _ _ _ _ _ _ _ _ HC)) as KN.
  destruct (sym_replay_sound SEGS E _ _ KN (a_vmops cs) N L HR) as (HV & WN & WL).
  destruct (co_vmx _ _ _ _ _ _ _ _ _ _ _ HC) as [H1 H2]. rewrite HV in H1, H2. cbn [fst snd] in H1, H2.
  repeat split; assumption.
Qed.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BxSymExec3B.
Import AX2B.

Definition le_linB (bc : bctx) (x y : lin) : bool :=
  lin_testB bc (fst y - fst x) (lsub_e (snd y) (snd x)) (fun lo _ => 0 <=? lo).
Definition lt_linB (bc : bctx) (x y : lin) : bool :=
  lin_testB bc (fst y - fst x) (lsub_e (snd y) (snd x)) (fun lo _ => 0 <? lo).
Definition lin_ofxB (bc : bctx) (e : expr) : option lin :=
  if lin_nowrapRB bc e then Some (lin_of e) else None.
Definition lin_ofaB (bc : bctx) (a : saddr) : option lin :=
  match lin_ofxB bc (a_base a) with Some l => Some (lcat l (lconst (a_off a))) | None => None end.
Definition insideB (bc : bctx) (x : siv) (flo fhi : lin) : bool :=
  le_linB bc flo (fst x) && le_linB bc (snd x) fhi.
Definition kdisj1B (bc : bctx) (x r : siv) (K : kentry) : bool :=
  match K with
  | KDisj a1 n1 a2 n2 =>
      if negb (kdisj_pre x r (a_base a1) (a_base a2)) then false else
      match lin_ofaB bc a1, lin_ofxB bc n1, lin_ofaB bc a2, lin_ofxB bc n2 with
      | Some f1, Some m1, Some f2, Some m2 =>
          let g1 := lcat f1 m1 in let g2 := lcat f2 m2 in
          (insideB bc x f1 g1 && insideB bc r f2 g2) || (insideB bc x f2 g2 && insideB bc r f1 g1)
      | _, _, _, _ => false
      end
  | _ => false
  end.
Definition kdisjB (bc : bctx) (x r : siv) : bool := existsb (kdisj1B bc x r) (bc_fk bc).
Definition disjoint_decB (bc : bctx) (x r : siv) : bool :=
  le_linB bc (snd x) (fst r) || le_linB bc (snd r) (fst x) || kdisjB bc x r.
Fixpoint drop_emptyB (bc : bctx) (l : list siv) : list siv :=
  match l with
  | [] => []
  | s :: r => if le_linB bc (snd s) (fst s) then drop_emptyB bc r else s :: drop_emptyB bc r
  end.
Definition sym_sub1B (bc : bctx) (r : siv) (x : siv) : option (list siv) :=
  if disjoint_decB bc x r then Some [x]
  else
    let a := fst x in let b := snd x in let lo := fst r in let hi := snd r in
    match (if le_linB bc lo b then Some lo else if le_linB bc b lo then Some b else None),
          (if le_linB bc a hi then Some hi else if le_linB bc hi a then Some a else None) with
    | Some mn, Some mx => Some (drop_emptyB bc [(a, mn); (mx, b)])
    | _, _ => None
    end.
Fixpoint sym_subB (bc : bctx) (l : list siv) (r : siv) : option (list siv) :=
  match l with
  | [] => Some []
  | x :: l' => match sym_sub1B bc r x, sym_subB bc l' r with
               | Some p, Some q => Some (p ++ q)
               | _, _ => None
               end
  end.
Definition siv_ofB (bc : bctx) (a n : expr) : option siv :=
  match lin_ofxB bc a, lin_ofxB bc n with
  | Some la, Some ln =>
      let r := (la, lcat la ln) in
      if lt_linB bc (fst r) (snd r) && le_linB bc (snd r) (lconst (2 ^ 64)) then Some r else None
  | _, _ => None
  end.
Definition sym_stepB (bc : bctx) (op : vmop) (NL : list siv * list siv) : option (list siv * list siv) :=
  let (N, L) := NL in
  match op with
  | VNew k a n =>
      match siv_ofB bc a n with
      | Some r => Some ((if is_none_kind k then r :: N else N), (if is_lazy_kind k then r :: L else L))
      | None => None
      end
  | VFixIn nr pn a n =>
      match siv_ofB bc a n with
      | Some r => match sym_subB bc N r, sym_subB bc L r with
                  | Some N', Some L' => Some ((if pn then r :: N' else N'), (if nr then r :: L' else L'))
                  | _, _ => None
                  end
      | None => None
      end
  | VUnmap a n =>
      match siv_ofB bc a n with
      | Some r => match sym_subB bc N r, sym_subB bc L r with
                  | Some N', Some L' => Some (N', L')
                  | _, _ => None
                  end
      | None => None
      end
  | VProt a n =>
      match siv_ofB bc a n with
      | Some r => match sym_subB bc N r with Some N' => Some (N', L) | None => None end
      | None => None
      end
  end.
Fixpoint sym_replayB (bc : bctx) (ops : list vmop) : option (list siv * list siv) :=
  match ops with
  | [] => Some ([], [])
  | op :: r => match sym_replayB bc r with Some NL => sym_stepB bc op NL | None => None end
  end.

Definition cs_ledgers (cs : acs) : option (list siv * list siv) :=
  sym_replayB (mkbc (kn_arith (kn cs))) (a_vmops cs).

Section BEq.
  Variable fk : list kentry.
  #[local] Notation bc := (mkbc fk).
  Lemma le_linB_eqf : forall x y, le_linB bc x y = le_lin fk x y.
  Proof. intros. unfold le_linB, le_lin. rewrite lin_testB_eqf. reflexivity. Qed.
  Lemma lt_linB_eqf : forall x y, lt_linB bc x y = lt_lin fk x y.
  Proof. intros. unfold lt_linB, lt_lin. rewrite lin_testB_eqf. reflexivity. Qed.
  Lemma lin_ofxB_eqf : forall e, lin_ofxB bc e = lin_ofx fk e.
  Proof. intros. unfold lin_ofxB, lin_ofx. rewrite lin_nowrapRB_eqf. reflexivity. Qed.
  Lemma lin_ofaB_eqf : forall a, lin_ofaB bc a = lin_ofa fk a.
  Proof. intros. unfold lin_ofaB, lin_ofa. rewrite lin_ofxB_eqf. reflexivity. Qed.
  Lemma insideB_eqf : forall x f g, insideB bc x f g = inside fk x f g.
  Proof. intros. unfold insideB, inside. rewrite !le_linB_eqf. reflexivity. Qed.
  Lemma kdisj1B_eqf : forall x r K, kdisj1B bc x r K = kdisj1 fk x r K.
  Proof. intros x r K. destruct K; try reflexivity. cbn [kdisj1B kdisj1]. destruct (negb _); [reflexivity|]. rewrite !lin_ofaB_eqf, !lin_ofxB_eqf.
         repeat (destruct (lin_ofa fk _) || destruct (lin_ofx fk _)); try reflexivity. rewrite !insideB_eqf. reflexivity. Qed.
  Lemma kdisjB_eqf : forall x r, kdisjB bc x r = kdisj fk x r.
  Proof.
    intros. unfold kdisjB, kdisj. rewrite bc_fk_mkbc.
    assert (H : forall l, existsb (kdisj1B bc x r) l = existsb (kdisj1 fk x r) l).
    { induction l as [|K l IH]; [reflexivity|]. cbn [existsb]. rewrite kdisj1B_eqf, IH. reflexivity. }
    apply H.
  Qed.
  Lemma disjoint_decB_eqf : forall x r, disjoint_decB bc x r = disjoint_dec fk x r.
  Proof. intros. unfold disjoint_decB, disjoint_dec. rewrite !le_linB_eqf, kdisjB_eqf. reflexivity. Qed.
  Lemma drop_emptyB_eqf : forall l, drop_emptyB bc l = drop_empty fk l.
  Proof. induction l as [|s l IH]; [reflexivity|]. cbn [drop_emptyB drop_empty]. rewrite le_linB_eqf, IH. reflexivity. Qed.
  Lemma sym_sub1B_eqf : forall r x, sym_sub1B bc r x = sym_sub1 fk r x.
  Proof.
    intros. unfold sym_sub1B, sym_sub1. rewrite disjoint_decB_eqf, !le_linB_eqf.
    destruct (disjoint_dec fk x r); [reflexivity|].
    destruct (le_lin fk (fst r) (snd x)), (le_lin fk (snd x) (fst r)), (le_lin fk (fst x) (snd r)), (le_lin fk (snd r) (fst x));
      rewrite ?drop_emptyB_eqf; reflexivity.
  Qed.
  Lemma sym_subB_eqf : forall l r, sym_subB bc l r = sym_sub fk l r.
  Proof. induction l as [|x l IH]; intros r; [reflexivity|]. cbn [sym_subB sym_sub]. rewrite sym_sub1B_eqf, IH. reflexivity. Qed.
  Lemma siv_ofB_eqf : forall a n, siv_ofB bc a n = siv_of fk a n.
  Proof.
    intros. unfold siv_ofB, siv_of. rewrite !lin_ofxB_eqf.
    destruct (lin_ofx fk a), (lin_ofx fk n); try reflexivity. rewrite lt_linB_eqf, le_linB_eqf. reflexivity.
  Qed.
  Lemma sym_stepB_eqf : forall op NL, sym_stepB bc op NL = sym_step fk op NL.
  Proof. intros op [N L]. destruct op; cbn [sym_stepB sym_step]; rewrite siv_ofB_eqf, ?sym_subB_eqf; try reflexivity;
         destruct (siv_of fk _ _); rewrite ?sym_subB_eqf; reflexivity. Qed.
  Lemma sym_replayB_eqf : forall ops, sym_replayB bc ops = sym_replay fk ops.
  Proof. induction ops as [|op ops IH]; [reflexivity|]. cbn [sym_replayB sym_replay]. rewrite IH. destruct (sym_replay fk ops); [apply sym_stepB_eqf | reflexivity]. Qed.
End BEq.

Theorem cs_ledgers_sound :
  forall SEGS A LIMIT SINV argH FS0 E cs R FULL model N L,
    cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model ->
    cs_ledgers cs = Some (N, L) ->
    vm_noaccess (m_vmmaps model) = sivs_den E N /\ m_vm_lazy model = sivs_den E L
    /\ Forall (siv_wf E) N /\ Forall (siv_wf E) L.
Proof.
  intros SEGS A LIMIT SINV argH FS0 E cs R FULL model N L HC HR. unfold cs_ledgers in HR. rewrite sym_replayB_eqf in HR.
  exact (cs_ok_vm_closed SEGS A LIMIT SINV argH FS0 E cs R FULL model N L HC HR).
Qed.
