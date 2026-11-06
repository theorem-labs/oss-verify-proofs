(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AxSymExec3 AxSymExec3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module CXFC.
Import AX2. Import AX2B.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint lp_eqb (a b : list positive) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => if Pos.eqb x y then lp_eqb a' b' else false
  | _, _ => false
  end.
Lemma lp_eqb_eq : forall a b, lp_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  destruct (Pos.eqb_spec x y) as [->|]; [|discriminate]. f_equal. apply IH. exact H.
Qed.
Definition memo1 : Type := list (list positive * bool).
Fixpoint memo_get (m : memo1) (RS : list positive) : option bool :=
  match m with
  | [] => None
  | (RS', b) :: r => if lp_eqb RS RS' then Some b else memo_get r RS
  end.
Lemma memo_get_in : forall m RS b, memo_get m RS = Some b -> In (RS, b) m.
Proof.
  induction m as [|[RS' b'] r IH]; intros RS b H; cbn in H; [discriminate|].
  destruct (lp_eqb RS RS') eqn:E.
  - injection H as <-. apply lp_eqb_eq in E. subst. left. reflexivity.
  - right. apply IH. exact H.
Qed.
(* [comment removed for export] *)
Definition iside : Type := (positive * (saddr * expr))%type.
Fixpoint disj_sidesRI (fs : list dfact) (RS : list positive) : list iside :=
  match fs with
  | [] => []
  | (i, j, (s1, s2)) :: rest =>
      let r := disj_sidesRI rest RS in
      let r1 := if pmem j RS then (i, s1) :: r else r in
      if pmem i RS then (j, s2) :: r1 else r1
  end.
Lemma disj_sidesRI_snd : forall fs RS, map snd (disj_sidesRI fs RS) = disj_sidesR fs RS.
Proof.
  induction fs as [|[[i j] [s1 s2]] rest IH]; intros RS; [reflexivity|]. cbn [disj_sidesRI disj_sidesR].
  destruct (pmem i RS), (pmem j RS); cbn [map snd]; rewrite IH; reflexivity.
Qed.
Lemma disj_sidesRI_in : forall (P : iside -> Prop) fs RS,
  (forall i j s1 s2, In (i, j, (s1, s2)) fs -> P (i, s1) /\ P (j, s2)) -> Forall P (disj_sidesRI fs RS).
Proof.
  intros P fs RS. induction fs as [|[[i j] [s1 s2]] rest IH]; intros H; [constructor|]. cbn [disj_sidesRI].
  assert (IH' : Forall P (disj_sidesRI rest RS)) by (apply IH; intros; apply (H i0 j0); right; assumption).
  destruct (H i j s1 s2 (or_introl eq_refl)) as [P1 P2].
  destruct (pmem i RS), (pmem j RS); repeat constructor; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition linsum : Type := option (Z * list (Z * expr) * option (Z * Z) * bool).
(* [comment removed for export] *)
Definition lsumx : Type := (option (Z * Z) * bool * Z * bool)%type.
Record memo2 : Type := MM { mm_L : memo1; mm_X : memo1; mm_sL : ptree bool; mm_sX : ptree bool; mm_lin : option (expr * linsum); mm_h2 : option (option Z);
                         mm_linx : option (expr * (lsumx * lsumx));
                         mm_blk : list (expr * ptree (lsumx * lsumx)) (* [comment removed for export] *) }.
Definition memo0 : memo2 := MM [] [] PTLeaf PTLeaf None None None [].
Definition memo0b (B : list (expr * ptree (lsumx * lsumx))) : memo2 := MM [] [] PTLeaf PTLeaf None None None B.

Section Entry.
Variable bc : bctx.
(* [comment removed for export] *)
Variables (b2 : expr) (k2 : Z) (n2 : expr).
Definition D_of (RS : list positive) : list (saddr * expr) := disj_sidesR (rt_facts (bc_rt bc)) RS.
Definition iside_ok (t : iside) : Prop := rt_In (bc_rt bc) (fst t) (fst (snd t)) (snd (snd t)).
Definition linsum_of (b1 : expr) : linsum :=
  if shares_var b1 b2 then
    let l1 := lin_of b1 in let l2 := lin_of b2 in
    let dts := lsub_e (snd l2) (snd l1) in
    Some ((fst l2 - fst l1)%Z, dts, lin_range (erangeB bc) 0 dts, (if lin_nowrapRB bc b1 then lin_nowrapRB bc b2 else false))
  else None.
Definition lin_via (LS : linsum) (k1 m1 m2 : Z) : bool :=
  match LS with
  | None => false
  | Some (cd, dts, R0, NW) =>
      let c := (cd + k2 - k1)%Z in
      let test := fun lo hi : Z => (Z.leb m1 lo || Z.leb hi (- m2))%bool in
      if (match R0 with
          | Some (lo0, hi0) => if test (lo0 + c)%Z (hi0 + c)%Z then true else lin_test_relB bc c dts test
          | None => lin_test_relB bc c dts test
          end) then NW else false
  end.
Lemma lin_range_shift : forall rng c ts,
  lin_range rng c ts = match lin_range rng 0 ts with Some (lo, hi) => Some ((lo + c)%Z, (hi + c)%Z) | None => None end.
Proof.
  intros rng c ts. induction ts as [|[k a] r IH]; [reflexivity|]. cbn [lin_range].
  destruct (rng a) as [[al ah]|]; [|reflexivity]. rewrite IH. destruct (lin_range rng 0 r) as [[lo hi]|]; [|reflexivity].
  destruct (Z.leb 0 k); f_equal; f_equal; ring.
Qed.
Lemma lin_via_eq : forall b1 k1 m1 m2,
  lin_via (linsum_of b1) k1 m1 m2 = (if shares_var b1 b2 then lin_apart0BF bc b1 k1 m1 b2 k2 m2 else false).
Proof.
  intros b1 k1 m1 m2. unfold linsum_of. destruct (shares_var b1 b2); [|reflexivity]. cbv zeta. unfold lin_via, lin_apart0BF, lin_testB.
  replace (fst (lin_of b2) + k2 - fst (lin_of b1) - k1)%Z with (fst (lin_of b2) - fst (lin_of b1) + k2 - k1)%Z by ring.
  rewrite (lin_range_shift (erangeB bc) (fst (lin_of b2) - fst (lin_of b1) + k2 - k1)%Z).
  destruct (lin_range (erangeB bc) 0 (lsub_e (snd (lin_of b2)) (snd (lin_of b1)))) as [[lo0 hi0]|]; reflexivity.
Qed.
(* [comment removed for export] *)
Lemma lin_ge0BF_fast : forall pos neg lo0 hi0,
  lin_range (erangeB bc) 0 (lsub_e (xt_lin pos) (xt_lin neg)) = Some (lo0, hi0) ->
  (Z.ltb (hi0 + (xt_const pos - xt_const neg)) 0 = true -> has_round (lsub_e (xt_lin pos) (xt_lin neg)) = false -> lin_ge0BF bc pos neg = false)
  /\ (Z.ltb (hi0 + (xt_const pos - xt_const neg)) 0 = false -> Z.leb 0 (lo0 + (xt_const pos - xt_const neg)) = true ->
      xt_nowrapB bc pos = true -> xt_nowrapB bc neg = true -> lin_ge0BF bc pos neg = true).
Proof.
  intros pos neg lo0 hi0 E. unfold lin_ge0BF, lin_ge0_coreBX. cbv zeta.
  rewrite (lin_range_shift (erangeB bc) (xt_const pos - xt_const neg)%Z), E. cbn [lin_hopeless lin_test_rB]. split.
  - intros H1 H2. rewrite H1, H2. reflexivity.
  - intros H1 H2 H3 H4. rewrite H1, H2, H3, H4. reflexivity.
Qed.
Definition linx_of (b1 : expr) : lsumx * lsumx :=
  let tA := lsub_e (xt_lin [(b2, 0%Z)]) (xt_lin [(b1, 0%Z)]) in
  let tB := lsub_e (xt_lin [(b1, 0%Z)]) (xt_lin [(b2, 0%Z); (n2, 0%Z)]) in
  let w1 := lin_nowrapRB bc b1 in let w2 := lin_nowrapRB bc b2 in
  ((lin_range (erangeB bc) 0 tA, has_round tA, (fst (lin_of b2) - fst (lin_of b1))%Z, if w2 then w1 else false),
   (lin_range (erangeB bc) 0 tB, has_round tB, (fst (lin_of b1) - fst (lin_of b2) - fst (lin_of n2))%Z,
    if w1 then (if w2 then lin_nowrapRB bc n2 else false) else false)).
Definition geA (SA : lsumx) (b1 : expr) (k1 : Z) (n1 : expr) : bool :=
  match n1, SA with
  | ELit z1, (Some (lo0, hi0), hr, c0, nw) =>
      let c := (c0 + k2 - k1 - snorm z1)%Z in
      if Z.ltb (hi0 + c) 0 then (if hr then lin_ge0BF bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] else false)
      else if Z.leb 0 (lo0 + c) then
             (if nw then if lin_nowrapRB bc (ELit z1) then true else lin_ge0BF bc [(b2, k2)] [(b1, k1); (n1, 0%Z)]
              else lin_ge0BF bc [(b2, k2)] [(b1, k1); (n1, 0%Z)])
           else lin_ge0BF bc [(b2, k2)] [(b1, k1); (n1, 0%Z)]
  | _, _ => lin_ge0BF bc [(b2, k2)] [(b1, k1); (n1, 0%Z)]
  end.
Definition geB (SB : lsumx) (b1 : expr) (k1 : Z) : bool :=
  match SB with
  | (Some (lo0, hi0), hr, c0, nw) =>
      let c := (c0 + k1 - k2)%Z in
      if Z.ltb (hi0 + c) 0 then (if hr then lin_ge0BF bc [(b1, k1)] [(b2, k2); (n2, 0%Z)] else false)
      else if Z.leb 0 (lo0 + c) then (if nw then true else lin_ge0BF bc [(b1, k1)] [(b2, k2); (n2, 0%Z)])
           else lin_ge0BF bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  | _ => lin_ge0BF bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.
Lemma geA_eq : forall b1 k1 n1, geA (fst (linx_of b1)) b1 k1 n1 = lin_ge0BF bc [(b2, k2)] [(b1, k1); (n1, 0%Z)].
Proof.
  intros b1 k1 n1. unfold geA, linx_of. cbv zeta. cbn [fst snd]. destruct n1 as [z1| | | | | | |]; try reflexivity.
  destruct (lin_range (erangeB bc) 0 (lsub_e (xt_lin [(b2, 0%Z)]) (xt_lin [(b1, 0%Z)]))) as [[lo0 hi0]|] eqn:E; [|reflexivity].
  assert (ET : lsub_e (xt_lin [(b2, k2)]) (xt_lin [(b1, k1); (ELit z1, 0%Z)]) = lsub_e (xt_lin [(b2, 0%Z)]) (xt_lin [(b1, 0%Z)])) by reflexivity.
  assert (EC : (xt_const [(b2, k2)] - xt_const [(b1, k1); (ELit z1, 0%Z)] = fst (lin_of b2) - fst (lin_of b1) + k2 - k1 - snorm z1)%Z)
    by (cbn [xt_const lin_of fst]; ring).
  destruct (lin_ge0BF_fast [(b2, k2)] [(b1, k1); (ELit z1, 0%Z)] lo0 hi0) as [F1 F2]; [rewrite ET; exact E|].
  rewrite ET in F1. rewrite EC in F1, F2.
  destruct (Z.ltb (hi0 + (fst (lin_of b2) - fst (lin_of b1) + k2 - k1 - snorm z1)) 0) eqn:H1.
  - destruct (has_round (lsub_e (xt_lin [(b2, 0%Z)]) (xt_lin [(b1, 0%Z)]))) eqn:H2; [reflexivity|]. symmetry. apply F1; reflexivity.
  - destruct (Z.leb 0 (lo0 + (fst (lin_of b2) - fst (lin_of b1) + k2 - k1 - snorm z1))) eqn:H2; [|reflexivity].
    destruct (lin_nowrapRB bc b2) eqn:W2; [|reflexivity]. destruct (lin_nowrapRB bc b1) eqn:W1; [|reflexivity].
    destruct (lin_nowrapRB bc (ELit z1)) eqn:W3; [|reflexivity].
    symmetry. apply F2; try reflexivity; cbn [xt_nowrapB]; rewrite ?W1, ?W2, ?W3; reflexivity.
Qed.
Lemma geB_eq : forall b1 k1, geB (snd (linx_of b1)) b1 k1 = lin_ge0BF bc [(b1, k1)] [(b2, k2); (n2, 0%Z)].
Proof.
  intros b1 k1. unfold geB, linx_of. cbv zeta. cbn [fst snd].
  destruct (lin_range (erangeB bc) 0 (lsub_e (xt_lin [(b1, 0%Z)]) (xt_lin [(b2, 0%Z); (n2, 0%Z)]))) as [[lo0 hi0]|] eqn:E; [|reflexivity].
  assert (ET : lsub_e (xt_lin [(b1, k1)]) (xt_lin [(b2, k2); (n2, 0%Z)]) = lsub_e (xt_lin [(b1, 0%Z)]) (xt_lin [(b2, 0%Z); (n2, 0%Z)])) by reflexivity.
  assert (EC : (xt_const [(b1, k1)] - xt_const [(b2, k2); (n2, 0%Z)] = fst (lin_of b1) - fst (lin_of b2) - fst (lin_of n2) + k1 - k2)%Z)
    by (cbn [xt_const]; ring).
  destruct (lin_ge0BF_fast [(b1, k1)] [(b2, k2); (n2, 0%Z)] lo0 hi0) as [F1 F2]; [rewrite ET; exact E|].
  rewrite ET in F1. rewrite EC in F1, F2.
  destruct (Z.ltb (hi0 + (fst (lin_of b1) - fst (lin_of b2) - fst (lin_of n2) + k1 - k2)) 0) eqn:H1.
  - destruct (has_round (lsub_e (xt_lin [(b1, 0%Z)]) (xt_lin [(b2, 0%Z); (n2, 0%Z)]))) eqn:H2; [reflexivity|]. symmetry. apply F1; reflexivity.
  - destruct (Z.leb 0 (lo0 + (fst (lin_of b1) - fst (lin_of b2) - fst (lin_of n2) + k1 - k2))) eqn:H2; [|reflexivity].
    destruct (lin_nowrapRB bc b1) eqn:W1; [|reflexivity]. destruct (lin_nowrapRB bc b2) eqn:W2; [|reflexivity].
    destruct (lin_nowrapRB bc n2) eqn:W3; [|reflexivity].
    symmetry. apply F2; try reflexivity; cbn [xt_nowrapB]; rewrite ?W1, ?W2, ?W3; reflexivity.
Qed.
(* [comment removed for export] *)
Definition sidesumG (b : expr) (cb : expr) (ml : expr) : lsumx * lsumx :=
  let tA := lsub_e (xt_lin [(b, 0%Z)]) (xt_lin [(cb, 0%Z)]) in
  let tB := lsub_e (xt_lin [(cb, 0%Z); (ml, 0%Z)]) (xt_lin [(b, 0%Z)]) in
  let w1 := lin_nowrapRB bc b in let w2 := lin_nowrapRB bc cb in
  ((lin_range (erangeB bc) 0 tA, has_round tA, (fst (lin_of b) - fst (lin_of cb))%Z, if w1 then w2 else false),
   (lin_range (erangeB bc) 0 tB, has_round tB, (fst (lin_of cb) + fst (lin_of ml) - fst (lin_of b))%Z,
    if w2 then (if lin_nowrapRB bc ml then w1 else false) else false)).
Definition sidesum (cb : expr) (ml : expr) : lsumx * lsumx := sidesumG b2 cb ml.
Definition sgeA (SA : lsumx) (cb : expr) (ck : Z) : bool :=
  match SA with
  | (Some (lo0, hi0), hr, c0, nw) =>
      let c := (c0 + k2 - ck)%Z in
      if Z.ltb (hi0 + c) 0 then (if hr then lin_ge0BF bc [(b2, k2)] [(cb, ck)] else false)
      else if Z.leb 0 (lo0 + c) then (if nw then true else lin_ge0BF bc [(b2, k2)] [(cb, ck)])
           else lin_ge0BF bc [(b2, k2)] [(cb, ck)]
  | _ => lin_ge0BF bc [(b2, k2)] [(cb, ck)]
  end.
Definition sgeB (SB : lsumx) (cb : expr) (ck : Z) (ml : expr) (z1 : Z) : bool :=
  match SB with
  | (Some (lo0, hi0), hr, c0, nw) =>
      let c := (c0 + ck - k2 - snorm z1)%Z in
      if Z.ltb (hi0 + c) 0 then (if hr then lin_ge0BF bc [(cb, ck); (ml, 0%Z)] [(b2, k2); (ELit z1, 0%Z)] else false)
      else if Z.leb 0 (lo0 + c) then
             (if nw then if lin_nowrapRB bc (ELit z1) then true else lin_ge0BF bc [(cb, ck); (ml, 0%Z)] [(b2, k2); (ELit z1, 0%Z)]
              else lin_ge0BF bc [(cb, ck); (ml, 0%Z)] [(b2, k2); (ELit z1, 0%Z)])
           else lin_ge0BF bc [(cb, ck); (ml, 0%Z)] [(b2, k2); (ELit z1, 0%Z)]
  | _ => lin_ge0BF bc [(cb, ck); (ml, 0%Z)] [(b2, k2); (ELit z1, 0%Z)]
  end.
Lemma sgeA_eq : forall cb ck ml, sgeA (fst (sidesum cb ml)) cb ck = lin_ge0BF bc [(b2, k2)] [(cb, ck)].
Proof.
  intros cb ck ml. unfold sgeA, sidesum, sidesumG. cbv zeta. cbn [fst snd].
  destruct (lin_range (erangeB bc) 0 (lsub_e (xt_lin [(b2, 0%Z)]) (xt_lin [(cb, 0%Z)]))) as [[lo0 hi0]|] eqn:E; [|reflexivity].
  assert (ET : lsub_e (xt_lin [(b2, k2)]) (xt_lin [(cb, ck)]) = lsub_e (xt_lin [(b2, 0%Z)]) (xt_lin [(cb, 0%Z)])) by reflexivity.
  assert (EC : (xt_const [(b2, k2)] - xt_const [(cb, ck)] = fst (lin_of b2) - fst (lin_of cb) + k2 - ck)%Z) by (cbn [xt_const]; ring).
  destruct (lin_ge0BF_fast [(b2, k2)] [(cb, ck)] lo0 hi0) as [F1 F2]; [rewrite ET; exact E|].
  rewrite ET in F1. rewrite EC in F1, F2.
  destruct (Z.ltb (hi0 + (fst (lin_of b2) - fst (lin_of cb) + k2 - ck)) 0) eqn:H1.
  - destruct (has_round (lsub_e (xt_lin [(b2, 0%Z)]) (xt_lin [(cb, 0%Z)]))) eqn:H2; [reflexivity|]. symmetry. apply F1; reflexivity.
  - destruct (Z.leb 0 (lo0 + (fst (lin_of b2) - fst (lin_of cb) + k2 - ck))) eqn:H2; [|reflexivity].
    destruct (lin_nowrapRB bc b2) eqn:W1; [|reflexivity]. destruct (lin_nowrapRB bc cb) eqn:W2; [|reflexivity].
    symmetry. apply F2; try reflexivity; cbn [xt_nowrapB]; rewrite ?W1, ?W2; reflexivity.
Qed.
Lemma sgeB_eq : forall cb ck ml z1, sgeB (snd (sidesum cb ml)) cb ck ml z1 = lin_ge0BF bc [(cb, ck); (ml, 0%Z)] [(b2, k2); (ELit z1, 0%Z)].
Proof.
  intros cb ck ml z1. unfold sgeB, sidesum, sidesumG. cbv zeta. cbn [fst snd].
  destruct (lin_range (erangeB bc) 0 (lsub_e (xt_lin [(cb, 0%Z); (ml, 0%Z)]) (xt_lin [(b2, 0%Z)]))) as [[lo0 hi0]|] eqn:E; [|reflexivity].
  assert (ET : lsub_e (xt_lin [(cb, ck); (ml, 0%Z)]) (xt_lin [(b2, k2); (ELit z1, 0%Z)]) = lsub_e (xt_lin [(cb, 0%Z); (ml, 0%Z)]) (xt_lin [(b2, 0%Z)])) by reflexivity.
  assert (EC : (xt_const [(cb, ck); (ml, 0%Z)] - xt_const [(b2, k2); (ELit z1, 0%Z)] = fst (lin_of cb) + fst (lin_of ml) - fst (lin_of b2) + ck - k2 - snorm z1)%Z)
    by (cbn [xt_const lin_of fst]; ring).
  destruct (lin_ge0BF_fast [(cb, ck); (ml, 0%Z)] [(b2, k2); (ELit z1, 0%Z)] lo0 hi0) as [F1 F2]; [rewrite ET; exact E|].
  rewrite ET in F1. rewrite EC in F1, F2.
  destruct (Z.ltb (hi0 + (fst (lin_of cb) + fst (lin_of ml) - fst (lin_of b2) + ck - k2 - snorm z1)) 0) eqn:H1.
  - destruct (has_round (lsub_e (xt_lin [(cb, 0%Z); (ml, 0%Z)]) (xt_lin [(b2, 0%Z)]))) eqn:H2; [reflexivity|]. symmetry. apply F1; reflexivity.
  - destruct (Z.leb 0 (lo0 + (fst (lin_of cb) + fst (lin_of ml) - fst (lin_of b2) + ck - k2 - snorm z1))) eqn:H2; [|reflexivity].
    destruct (lin_nowrapRB bc cb) eqn:W2; [|reflexivity]. destruct (lin_nowrapRB bc ml) eqn:W3; [|reflexivity]. destruct (lin_nowrapRB bc b2) eqn:W1; [|reflexivity].
    destruct (lin_nowrapRB bc (ELit z1)) eqn:W4; [|reflexivity].
    symmetry. apply F2; try reflexivity; cbn [xt_nowrapB]; rewrite ?W1, ?W2, ?W3, ?W4; reflexivity.
Qed.
Definition blk_ok (B : list (expr * ptree (lsumx * lsumx))) : Prop :=
  Forall (fun bt => forall i SM, pt_get (snd bt) i = Some SM -> forall c ml, rt_In (bc_rt bc) i c ml -> SM = sidesumG (fst bt) (a_base c) ml) B.
Definition memo_ok (m : memo2) : Prop :=
  (forall RS b, In (RS, b) (mm_L m) -> forall z2, n2 = ELit z2 -> b = in_sidesB bc (D_of RS) b2 k2 (zlit64 z2))
  /\ (forall RS b, In (RS, b) (mm_X m) -> b = in_sides_xB bc (D_of RS) b2 k2 n2)
  /\ (forall i b, pt_get (mm_sL m) i = Some b -> forall c ml z2, rt_In (bc_rt bc) i c ml -> n2 = ELit z2 -> b = sub_itvB bc b2 k2 (zlit64 z2) c ml)
  /\ (forall i b, pt_get (mm_sX m) i = Some b -> forall c ml, rt_In (bc_rt bc) i c ml -> b = sub_itv_xB bc b2 k2 n2 c ml)
  /\ (forall b1c LS, mm_lin m = Some (b1c, LS) -> LS = linsum_of b1c)
  /\ (forall v, mm_h2 m = Some v -> v = xhiB bc n2)
  /\ (forall b1c SX, mm_linx m = Some (b1c, SX) -> SX = linx_of b1c)
  /\ blk_ok (mm_blk m).
Lemma memo_ok0 : memo_ok memo0.
Proof. repeat split; cbn; intros; try contradiction; try discriminate; try (destruct i; discriminate). constructor. Qed.
Lemma memo_ok0b : forall B, blk_ok B -> memo_ok (memo0b B).
Proof. intros B HB. repeat split; cbn; intros; try contradiction; try discriminate; try (destruct i; discriminate). exact HB. Qed.
Lemma memo_ok_blk : forall m, memo_ok m -> blk_ok (mm_blk m).
Proof. intros m (_ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.
Definition lin_get (b1 : expr) (m : memo2) : linsum * memo2 :=
  match mm_lin m with
  | Some (b1c, LS) =>
      if expr_eqb b1 b1c then (LS, m)
      else let LS' := linsum_of b1 in (LS', MM (mm_L m) (mm_X m) (mm_sL m) (mm_sX m) (Some (b1, LS')) (mm_h2 m) (mm_linx m) (mm_blk m))
  | None => let LS' := linsum_of b1 in (LS', MM (mm_L m) (mm_X m) (mm_sL m) (mm_sX m) (Some (b1, LS')) (mm_h2 m) (mm_linx m) (mm_blk m))
  end.
Lemma lin_get_spec : forall b1 m, memo_ok m -> fst (lin_get b1 m) = linsum_of b1 /\ memo_ok (snd (lin_get b1 m)).
Proof.
  intros b1 m Hm. pose proof Hm as (HL & HX & HsL & HsX & HLin & Hh2 & HLx & HBlk). unfold lin_get.
  assert (NEW : memo_ok (MM (mm_L m) (mm_X m) (mm_sL m) (mm_sX m) (Some (b1, linsum_of b1)) (mm_h2 m) (mm_linx m) (mm_blk m))).
  { repeat split; cbn [mm_L mm_X mm_sL mm_sX mm_lin mm_h2 mm_linx mm_blk]; try assumption. intros b1c LS E. injection E as <- <-. reflexivity. }
  destruct (mm_lin m) as [[b1c LS]|] eqn:E; [|split; [reflexivity|exact NEW]].
  destruct (expr_eqb b1 b1c) eqn:Eb; [|split; [reflexivity|exact NEW]].
  apply p_expr_eqb_eq in Eb. subst b1c. cbn [fst snd]. split; [exact (HLin _ _ eq_refl) | exact Hm].
Qed.

Definition h2_get (m : memo2) : option Z * memo2 :=
  match mm_h2 m with
  | Some v => (v, m)
  | None => let v := xhiB bc n2 in (v, MM (mm_L m) (mm_X m) (mm_sL m) (mm_sX m) (mm_lin m) (Some v) (mm_linx m) (mm_blk m))
  end.
Lemma h2_get_spec : forall m, memo_ok m -> fst (h2_get m) = xhiB bc n2 /\ memo_ok (snd (h2_get m)).
Proof.
  intros m Hm. pose proof Hm as (HL & HX & HsL & HsX & HLin & Hh2 & HLx & HBlk). unfold h2_get.
  destruct (mm_h2 m) as [v|] eqn:E; cbn [fst snd]; [split; [exact (Hh2 _ eq_refl) | exact Hm]|].
  split; [reflexivity|]. repeat split; cbn [mm_L mm_X mm_sL mm_sX mm_lin mm_h2 mm_linx mm_blk]; try assumption. intros v E'. injection E' as <-. reflexivity.
Qed.
Definition linx_get (b1 : expr) (m : memo2) : (lsumx * lsumx) * memo2 :=
  match mm_linx m with
  | Some (b1c, SX) =>
      if expr_eqb b1 b1c then (SX, m)
      else let SX' := linx_of b1 in (SX', MM (mm_L m) (mm_X m) (mm_sL m) (mm_sX m) (mm_lin m) (mm_h2 m) (Some (b1, SX')) (mm_blk m))
  | None => let SX' := linx_of b1 in (SX', MM (mm_L m) (mm_X m) (mm_sL m) (mm_sX m) (mm_lin m) (mm_h2 m) (Some (b1, SX')) (mm_blk m))
  end.
Lemma linx_get_spec : forall b1 m, memo_ok m -> fst (linx_get b1 m) = linx_of b1 /\ memo_ok (snd (linx_get b1 m)).
Proof.
  intros b1 m Hm. pose proof Hm as (HL & HX & HsL & HsX & HLin & Hh2 & HLx & HBlk). unfold linx_get.
  assert (NEW : memo_ok (MM (mm_L m) (mm_X m) (mm_sL m) (mm_sX m) (mm_lin m) (mm_h2 m) (Some (b1, linx_of b1)) (mm_blk m))).
  { repeat split; cbn [mm_L mm_X mm_sL mm_sX mm_lin mm_h2 mm_linx mm_blk]; try assumption. intros b1c SX E. injection E as <- <-. reflexivity. }
  destruct (mm_linx m) as [[b1c SX]|] eqn:E; [|split; [reflexivity|exact NEW]].
  destruct (expr_eqb b1 b1c) eqn:Eb; [|split; [reflexivity|exact NEW]].
  apply p_expr_eqb_eq in Eb. subst b1c. cbn [fst snd]. split; [exact (HLx _ _ eq_refl) | exact Hm].
Qed.
(* [comment removed for export] *)
Fixpoint scanL (DI : list iside) (m2 : Z) (t : ptree bool) : bool * ptree bool :=
  match DI with
  | [] => (false, t)
  | (i, (c, ml)) :: r =>
      match pt_get t i with
      | Some b => if b then (true, t) else scanL r m2 t
      | None => let b := sub_itvB bc b2 k2 m2 c ml in
                if b then (true, pt_set i b t) else scanL r m2 (pt_set i b t)
      end
  end.
Fixpoint scanX (DI : list iside) (t : ptree bool) : bool * ptree bool :=
  match DI with
  | [] => (false, t)
  | (i, (c, ml)) :: r =>
      match pt_get t i with
      | Some b => if b then (true, t) else scanX r t
      | None => let b := sub_itv_xB bc b2 k2 n2 c ml in
                if b then (true, pt_set i b t) else scanX r (pt_set i b t)
      end
  end.
Definition sL_ok (m2 : Z) (t : ptree bool) : Prop :=
  forall i b, pt_get t i = Some b -> forall c ml, rt_In (bc_rt bc) i c ml -> b = sub_itvB bc b2 k2 m2 c ml.
Definition sX_ok (t : ptree bool) : Prop :=
  forall i b, pt_get t i = Some b -> forall c ml, rt_In (bc_rt bc) i c ml -> b = sub_itv_xB bc b2 k2 n2 c ml.
Hypothesis RTF : forall i c m c' m', rt_In (bc_rt bc) i c m -> rt_In (bc_rt bc) i c' m' -> c = c' /\ m = m'.
Lemma sL_ok_set : forall m2 t i c ml, sL_ok m2 t -> rt_In (bc_rt bc) i c ml -> sL_ok m2 (pt_set i (sub_itvB bc b2 k2 m2 c ml) t).
Proof.
  intros m2 t i c ml H R i' b' G c' ml' R'. destruct (Pos.eq_dec i' i) as [->|NE].
  - rewrite pt_gss in G. injection G as <-. destruct (RTF _ _ _ _ _ R R') as [-> ->]. reflexivity.
  - rewrite pt_gso in G by exact NE. exact (H _ _ G _ _ R').
Qed.
Lemma sX_ok_set : forall t i c ml, sX_ok t -> rt_In (bc_rt bc) i c ml -> sX_ok (pt_set i (sub_itv_xB bc b2 k2 n2 c ml) t).
Proof.
  intros t i c ml H R i' b' G c' ml' R'. destruct (Pos.eq_dec i' i) as [->|NE].
  - rewrite pt_gss in G. injection G as <-. destruct (RTF _ _ _ _ _ R R') as [-> ->]. reflexivity.
  - rewrite pt_gso in G by exact NE. exact (H _ _ G _ _ R').
Qed.
Lemma scanL_spec : forall DI m2 t, Forall iside_ok DI -> sL_ok m2 t ->
  fst (scanL DI m2 t) = in_sidesB bc (map snd DI) b2 k2 m2 /\ sL_ok m2 (snd (scanL DI m2 t)).
Proof.
  induction DI as [|[i [c ml]] r IH]; intros m2 t HF Ht; [split; [reflexivity|exact Ht]|].
  apply Forall_cons_iff in HF as [R HF]. unfold iside_ok in R. cbn [fst snd] in R. cbn [scanL map snd in_sidesB].
  destruct (pt_get t i) as [b|] eqn:G.
  - rewrite <- (Ht _ _ G _ _ R). destruct b; [split; [reflexivity|exact Ht] | apply IH; assumption].
  - cbv zeta. pose proof (sL_ok_set m2 t i c ml Ht R) as Ht'.
    destruct (sub_itvB bc b2 k2 m2 c ml); [split; [reflexivity|exact Ht'] | apply IH; assumption].
Qed.
Lemma scanX_spec : forall DI t, Forall iside_ok DI -> sX_ok t ->
  fst (scanX DI t) = in_sides_xB bc (map snd DI) b2 k2 n2 /\ sX_ok (snd (scanX DI t)).
Proof.
  induction DI as [|[i [c ml]] r IH]; intros t HF Ht; [split; [reflexivity|exact Ht]|].
  apply Forall_cons_iff in HF as [R HF]. unfold iside_ok in R. cbn [fst snd] in R. cbn [scanX map snd in_sides_xB].
  destruct (pt_get t i) as [b|] eqn:G.
  - rewrite <- (Ht _ _ G _ _ R). destruct b; [split; [reflexivity|exact Ht] | apply IH; assumption].
  - cbv zeta. pose proof (sX_ok_set t i c ml Ht R) as Ht'.
    destruct (sub_itv_xB bc b2 k2 n2 c ml); [split; [reflexivity|exact Ht'] | apply IH; assumption].
Qed.

(* [comment removed for export] *)
Definition sub_itvBQ (qp : qprep) (b : expr) (k n : Z) (c : saddr) (ml : expr) : bool :=
  if (if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
        match xloB bc ml with Some l => Z.leb (k + n) (a_off c + l) | None => false end
      else false)
  then true
  else if (Z.leb 0 n && Z.ltb n two64)%bool then xinsideBQ bc qp b k (ELit n) (a_base c) (a_off c) ml else false.
Lemma sub_itvBQ_eq : forall b k n c ml, sub_itvBQ (mkqp bc b (ELit n)) b k n c ml = sub_itvB bc b k n c ml.
Proof. intros. unfold sub_itvBQ, sub_itvB. rewrite xinsideBQ_eq. reflexivity. Qed.
Fixpoint scanLQ (qp : qprep) (DI : list iside) (m2 : Z) (t : ptree bool) : bool * ptree bool :=
  match DI with
  | [] => (false, t)
  | (i, (c, ml)) :: r =>
      match pt_get t i with
      | Some b => if b then (true, t) else scanLQ qp r m2 t
      | None => let b := sub_itvBQ qp b2 k2 m2 c ml in
                if b then (true, pt_set i b t) else scanLQ qp r m2 (pt_set i b t)
      end
  end.
Lemma scanLQ_eq : forall DI m2 t, scanLQ (mkqp bc b2 (ELit m2)) DI m2 t = scanL DI m2 t.
Proof.
  induction DI as [|[i [c ml]] r IH]; intros m2 t; [reflexivity|]. cbn [scanLQ scanL].
  destruct (pt_get t i) as [b|]; [destruct b; [reflexivity|apply IH]|]. rewrite sub_itvBQ_eq. cbv zeta.
  destruct (sub_itvB bc b2 k2 m2 c ml); [reflexivity|apply IH].
Qed.
(* [comment removed for export] *)
Definition btree : Type := ptree (lsumx * lsumx).
Definition bt_ok (bt : btree) : Prop :=
  forall i SM, pt_get bt i = Some SM -> forall c ml, rt_In (bc_rt bc) i c ml -> SM = sidesumG b2 (a_base c) ml.
Definition xinside0S (SM : lsumx * lsumx) (cb : expr) (ck : Z) (ml : expr) (z1 : Z) : bool :=
  if sgeA (fst SM) cb ck then sgeB (snd SM) cb ck ml z1 else false.
Lemma xinside0S_eq : forall cb ck ml z1, xinside0S (sidesumG b2 cb ml) cb ck ml z1 = xinside0B bc b2 k2 (ELit z1) cb ck ml.
Proof.
  intros. unfold xinside0S, xinside0B. change (sidesumG b2 cb ml) with (sidesum cb ml). rewrite sgeA_eq, sgeB_eq. reflexivity.
Qed.
Definition side_test (qp : qprep) (i : positive) (c : saddr) (ml : expr) (m2 : Z) (bt : btree) : bool * btree :=
  if (if (expr_eqb b2 (a_base c) && Z.leb (a_off c) k2)%bool then
        match xloB bc ml with Some l => Z.leb (k2 + m2) (a_off c + l) | None => false end
      else false)
  then (true, bt)
  else if (Z.leb 0 m2 && Z.ltb m2 two64)%bool then
         if shares_var b2 (a_base c) then
           match pt_get bt i with
           | Some SM => (xinside0S SM (a_base c) (a_off c) ml m2, bt)
           | None => let SM := sidesumG b2 (a_base c) ml in (xinside0S SM (a_base c) (a_off c) ml m2, pt_set i SM bt)
           end
         else if novars (a_base c) then
                ((if xinside_numBQ bc qp b2 k2 (ELit m2) (a_base c) (a_off c) ml then true else xinside_jtBQ bc qp b2 k2 (ELit m2) (a_base c) (a_off c) ml), bt)
              else (false, bt)
       else (false, bt).
Lemma side_test_spec : forall qp i c ml m2 bt, bt_ok bt -> rt_In (bc_rt bc) i c ml ->
  fst (side_test qp i c ml m2 bt) = sub_itvBQ qp b2 k2 m2 c ml /\ bt_ok (snd (side_test qp i c ml m2 bt)).
Proof.
  intros qp i c ml m2 bt Hb R. unfold side_test, sub_itvBQ, xinsideBQ.
  destruct (if (expr_eqb b2 (a_base c) && Z.leb (a_off c) k2)%bool then match xloB bc ml with Some l => Z.leb (k2 + m2) (a_off c + l) | None => false end else false);
    [split; [reflexivity|exact Hb]|].
  destruct (Z.leb 0 m2 && Z.ltb m2 two64)%bool; [|split; [reflexivity|exact Hb]].
  destruct (shares_var b2 (a_base c)).
  - destruct (pt_get bt i) as [SM|] eqn:G; cbn [fst snd].
    + rewrite (Hb _ _ G _ _ R). split; [apply xinside0S_eq | exact Hb].
    + split; [apply xinside0S_eq|]. intros i' SM' G' c' ml' R'. destruct (Pos.eq_dec i' i) as [->|NE].
      * rewrite pt_gss in G'. injection G' as <-. destruct (RTF _ _ _ _ _ R R') as [-> ->]. reflexivity.
      * rewrite pt_gso in G' by exact NE. exact (Hb _ _ G' _ _ R').
  - destruct (novars (a_base c)); split; try reflexivity; exact Hb.
Qed.
Fixpoint scanLB (qp : qprep) (DI : list iside) (m2 : Z) (t : ptree bool) (bt : btree) : (bool * ptree bool) * btree :=
  match DI with
  | [] => ((false, t), bt)
  | (i, (c, ml)) :: r =>
      match pt_get t i with
      | Some b => if b then ((true, t), bt) else scanLB qp r m2 t bt
      | None => let sb := side_test qp i c ml m2 bt in
                if fst sb then ((true, pt_set i (fst sb) t), snd sb) else scanLB qp r m2 (pt_set i (fst sb) t) (snd sb)
      end
  end.
Lemma scanLB_spec : forall qp DI m2 t bt, Forall iside_ok DI -> bt_ok bt ->
  fst (scanLB qp DI m2 t bt) = scanLQ qp DI m2 t /\ bt_ok (snd (scanLB qp DI m2 t bt)).
Proof.
  intros qp DI. induction DI as [|[i [c ml]] r IH]; intros m2 t bt HF Hb; [split; [reflexivity|exact Hb]|].
  apply Forall_cons_iff in HF as [R HF]. unfold iside_ok in R. cbn [fst snd] in R. cbn [scanLB scanLQ].
  destruct (pt_get t i) as [b|]; [destruct b; [split; [reflexivity|exact Hb] | apply IH; assumption]|].
  destruct (side_test_spec qp i c ml m2 bt Hb R) as [E1 E2]. cbv zeta. rewrite E1.
  destruct (sub_itvBQ qp b2 k2 m2 c ml); [split; [reflexivity|exact E2] | apply IH; assumption].
Qed.
Definition blk_tree (B : list (expr * btree)) : btree :=
  match List.find (fun bt => expr_eqb b2 (fst bt)) B with Some bt => snd bt | None => PTLeaf end.
Lemma blk_tree_ok : forall B, blk_ok B -> bt_ok (blk_tree B).
Proof.
  intros B H. unfold blk_tree. match goal with |- context [List.find ?f B] => destruct (List.find f B) as [bt|] eqn:E end.
  - apply List.find_some in E as [IN Eb]. apply p_expr_eqb_eq in Eb.
    intros i SM G c ml R. rewrite Eb. exact (proj1 (Forall_forall _ _) H _ IN i SM G c ml R).
  - intros i SM G. rewrite pt_get_leaf in G. discriminate.
Qed.
Lemma firstn_In' : forall (X : Type) n (l : list X) x, In x (List.firstn n l) -> In x l.
Proof. intros X n. induction n as [|n IH]; intros [|y l] x H; cbn in H; try contradiction. destruct H as [->|H]; [left; reflexivity | right; apply IH; exact H]. Qed.
Definition blk_put (B : list (expr * btree)) (bt : btree) : list (expr * btree) :=
  (b2, bt) :: List.firstn 5 (List.filter (fun x => negb (expr_eqb b2 (fst x))) B).
Lemma blk_put_ok : forall B bt, blk_ok B -> bt_ok bt -> blk_ok (blk_put B bt).
Proof.
  intros B bt HB Hbt. unfold blk_put, blk_ok. constructor; [exact Hbt|].
  apply Forall_forall. intros x IN. apply (proj1 (Forall_forall _ _) HB). apply firstn_In' in IN. apply List.filter_In in IN. exact (proj1 IN).
Qed.
Definition sidesL (RS : list positive) (DI : list iside) (m2 : Z) (m : memo2) : bool * memo2 :=
  match memo_get (mm_L m) RS with
  | Some b => (b, m)
  | None => let sr := scanLB (mkqp bc b2 (ELit m2)) DI m2 (mm_sL m) (blk_tree (mm_blk m)) in
            (fst (fst sr), MM ((RS, fst (fst sr)) :: mm_L m) (mm_X m) (snd (fst sr)) (mm_sX m) (mm_lin m) (mm_h2 m) (mm_linx m) (blk_put (mm_blk m) (snd sr)))
  end.
Definition sidesX (RS : list positive) (DI : list iside) (m : memo2) : bool * memo2 :=
  match memo_get (mm_X m) RS with
  | Some b => (b, m)
  | None => let '(b, t) := scanX DI (mm_sX m) in (b, MM (mm_L m) ((RS, b) :: mm_X m) (mm_sL m) t (mm_lin m) (mm_h2 m) (mm_linx m) (mm_blk m))
  end.
Definition di_ok (RS : list positive) (DI : list iside) : Prop := map snd DI = D_of RS /\ Forall iside_ok DI.
Lemma sidesL_spec : forall RS DI z2 m, memo_ok m -> di_ok RS DI -> n2 = ELit z2 ->
  fst (sidesL RS DI (zlit64 z2) m) = in_sidesB bc (D_of RS) b2 k2 (zlit64 z2) /\ memo_ok (snd (sidesL RS DI (zlit64 z2) m)).
Proof.
  intros RS DI z2 m (HL & HX & HsL & HsX & HLin & Hh2 & HLx & HBlk) [HD HF] En. unfold sidesL. destruct (memo_get (mm_L m) RS) as [b|] eqn:G; cbn [fst snd].
  - split; [|repeat split; assumption]. apply memo_get_in in G. exact (HL _ _ G _ En).
  - assert (Ht : sL_ok (zlit64 z2) (mm_sL m)).
    { intros i b G' c ml R. exact (HsL _ _ G' _ _ _ R En). }
    destruct (scanL_spec DI (zlit64 z2) (mm_sL m) HF Ht) as [E1 E2]. rewrite HD in E1.
    destruct (scanLB_spec (mkqp bc b2 (ELit (zlit64 z2))) DI (zlit64 z2) (mm_sL m) (blk_tree (mm_blk m)) HF (blk_tree_ok _ HBlk)) as [B1 B2].
    rewrite B1, scanLQ_eq.
    destruct (scanL DI (zlit64 z2) (mm_sL m)) as [b t]. cbn [fst snd] in *. split; [exact E1|].
    repeat split; cbn [mm_L mm_X mm_sL mm_sX mm_lin mm_h2 mm_linx mm_blk]; try assumption.
    + intros RS' b' [E|IN] z En'.
      * injection E as <- <-. rewrite En in En'. injection En' as <-. exact E1.
      * exact (HL _ _ IN _ En').
    + intros i b' G' c ml z R En'. rewrite En in En'. injection En' as <-. exact (E2 _ _ G' _ _ R).
    + apply blk_put_ok; assumption.
Qed.
Lemma sidesX_spec : forall RS DI m, memo_ok m -> di_ok RS DI ->
  fst (sidesX RS DI m) = in_sides_xB bc (D_of RS) b2 k2 n2 /\ memo_ok (snd (sidesX RS DI m)).
Proof.
  intros RS DI m (HL & HX & HsL & HsX & HLin & Hh2 & HLx & HBlk) [HD HF]. unfold sidesX. destruct (memo_get (mm_X m) RS) as [b|] eqn:G; cbn [fst snd].
  - split; [|repeat split; assumption]. apply memo_get_in in G. exact (HX _ _ G).
  - destruct (scanX_spec DI (mm_sX m) HF HsX) as [E1 E2]. rewrite HD in E1.
    destruct (scanX DI (mm_sX m)) as [b t]. cbn [fst snd] in *. split; [exact E1|].
    repeat split; cbn [mm_L mm_X mm_sL mm_sX mm_lin mm_h2 mm_linx mm_blk]; try assumption.
    intros RS' b' [E|IN]; [injection E as <- <-; exact E1 | exact (HX _ _ IN)].
Qed.

Definition xtail (RS : list positive) (DI : list iside) (b1 : expr) (k1 : Z) (n1 : expr) (m : memo2) : bool * memo2 :=
  let '(r, m') := sidesX RS DI m in
  if r then (true, m')
  else if negb (shares_var b1 b2) then (false, m')
  else let sm := linx_get b1 m' in
       if geA (fst (fst sm)) b1 k1 n1 then (true, snd sm)
       else (geB (snd (fst sm)) b1 k1, snd sm).
Lemma xtail_spec : forall RS DI b1 k1 n1, di_ok RS DI -> forall m0, memo_ok m0 ->
  fst (xtail RS DI b1 k1 n1 m0)
  = (if in_sides_xB bc (D_of RS) b2 k2 n2 then true else if negb (shares_var b1 b2) then false
     else if lin_ge0BF bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true else lin_ge0BF bc [(b1, k1)] [(b2, k2); (n2, 0%Z)])
  /\ memo_ok (snd (xtail RS DI b1 k1 n1 m0)).
Proof.
  intros RS DI b1 k1 n1 HDI m0 Hm0. unfold xtail. destruct (sidesX_spec RS DI m0 Hm0 HDI) as [E1 E2].
  destruct (sidesX RS DI m0) as [r m']. cbn [fst snd] in E1, E2. rewrite <- E1.
  destruct r; [split; [reflexivity|exact E2]|].
  destruct (negb (shares_var b1 b2)); [split; [reflexivity|exact E2]|].
  destruct (linx_get_spec b1 m' E2) as [L1 L2]. cbv zeta.
  destruct (linx_get b1 m') as [SX m'']. cbn [fst snd] in L1, L2 |- *. subst SX. rewrite geA_eq, geB_eq.
  destruct (lin_ge0BF bc [(b2, k2)] [(b1, k1); (n1, 0%Z)]); split; try reflexivity; exact L2.
Qed.
(* [comment removed for export] *)
Definition ranges_apart_pcBFM (sp : sprep) (RS : list positive) (DI : list iside) (b1 : expr) (k1 : Z) (n1 : expr)
           (br2 : option (Z * Z)) (m : memo2) : bool * memo2 :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      if (match sp_rng sp, br2 with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
          | _, _ => false
          end) then (true, m)
      else let '(r, m') := sidesL RS DI m2 m in
           if r then (true, m')
           else let '(LS, m'') := lin_get b1 m' in (lin_via LS k1 m1 m2, m'')
  | _, _ =>
    let hm := h2_get m in
    if (match sp_rng sp, br2, sp_h1 sp, fst hm with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else
            if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then (true, snd hm)
    else xtail RS DI b1 k1 n1 (snd hm)
  end.
Definition sp_ok (sp : sprep) (RS : list positive) (DI : list iside) : Prop := sp_D sp = D_of RS /\ sp_Dx sp = D_of RS /\ di_ok RS DI.
End Entry.

Lemma ranges_apart_pcBFM_spec : forall bc b2 k2 n2, 
  (forall i c m c' m', rt_In (bc_rt bc) i c m -> rt_In (bc_rt bc) i c' m' -> c = c' /\ m = m') ->
  forall sp RS DI b1 k1 n1 br2 m, memo_ok bc b2 k2 n2 m -> sp_ok bc sp RS DI ->
  fst (ranges_apart_pcBFM bc b2 k2 n2 sp RS DI b1 k1 n1 br2 m) = ranges_apart_pcBF bc sp b1 k1 n1 br2 b2 k2 n2
  /\ memo_ok bc b2 k2 n2 (snd (ranges_apart_pcBFM bc b2 k2 n2 sp RS DI b1 k1 n1 br2 m)).
Proof.
  intros bc b2 k2 n2 RTF sp RS DI b1 k1 n1 br2 m Hm (HD & HDx & HDI). unfold ranges_apart_pcBFM, ranges_apart_pcBF.
  pose proof (xtail_spec bc b2 k2 n2 RTF RS DI b1 k1 n1 HDI) as XC. rewrite HDx.
  destruct (h2_get_spec bc b2 k2 n2 m Hm) as [EH1 EH2].
  assert (GEN : forall c : bool,
     fst (if c then (true, snd (h2_get bc n2 m)) else xtail bc b2 k2 n2 RS DI b1 k1 n1 (snd (h2_get bc n2 m)))
     = (if c then true else if in_sides_xB bc (D_of bc RS) b2 k2 n2 then true else if negb (shares_var b1 b2) then false
        else if lin_ge0BF bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true else lin_ge0BF bc [(b1, k1)] [(b2, k2); (n2, 0%Z)])
     /\ memo_ok bc b2 k2 n2 (snd (if c then (true, snd (h2_get bc n2 m)) else xtail bc b2 k2 n2 RS DI b1 k1 n1 (snd (h2_get bc n2 m))))).
  { intros [|]; [split; [reflexivity|exact EH2] | exact (XC _ EH2)]. }
  destruct n1 as [z1| | | | | | |]; try (cbv zeta; rewrite EH1; apply GEN).
  destruct n2 as [z2| | | | | | |]; try (cbv zeta; rewrite EH1; apply GEN).
  cbv zeta.
  match goal with |- context [if ?c then (true, m) else _] => destruct c end; [split; [reflexivity|exact Hm]|].
  destruct (sidesL_spec bc b2 k2 (ELit z2) RTF RS DI z2 m Hm HDI eq_refl) as [E1 E2]. rewrite HD.
  destruct (sidesL bc b2 k2 RS DI (zlit64 z2) m) as [r m']. cbn [fst snd] in E1, E2. rewrite <- E1.
  destruct r; [destruct (shares_var b1 b2); [destruct (lin_apart0BF bc b1 k1 (zlit64 z1) b2 k2 (zlit64 z2))|]; split; try reflexivity; exact E2|].
  destruct (lin_get_spec bc b2 k2 (ELit z2) b1 m' E2) as [L1 L2].
  destruct (lin_get bc b2 b1 m') as [LS m'']. cbn [fst snd] in L1, L2 |- *. subst LS. rewrite lin_via_eq.
  destruct (shares_var b1 b2); [destruct (lin_apart0BF bc b1 k1 (zlit64 z1) b2 k2 (zlit64 z2))|]; split; try reflexivity; exact L2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition prune1pcKM (bc : bctx) (sp : sprep) (RS : list positive) (DI : list iside) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (same : bool)
  (br2 : option (Z * Z)) (m : memo2) : pk_res * memo2 :=
  let k := a_off wa in
  let wb := a_base wa in
  let zfK (mk : saddr -> expr -> kentry) (kb : expr) (kk : Z) (len : expr) :=
    if same then
      (match len with
       | ELit l0 => PRepl (ktrim mk kb kk l0 k w)
       | _ => if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl (kcutB bc mk wb k (elen w) kb kk len)
       end, m)
    else let '(r, m') := ranges_apart_pcBFM bc kb kk len sp RS DI wb k (elen w) br2 m in
         if r then (PKeep, m')
         else (match kcutB bc mk wb k (elen w) kb kk len with
               | [] => PRepl []
               | cut => PRepl cut
               end, m') in
  match K with
  | KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ => (PKeep, m)
  | KImg lo hi =>
      (match wb with
       | ELit 0 =>
           let r1 := if Z.ltb lo (Z.min k hi) then [KImg lo (Z.min k hi)] else [] in
           let lo2 := Z.max lo (k + Z.of_nat w) in
           let r2 := if Z.ltb lo2 hi then [KImg lo2 hi] else [] in
           PRepl (r1 ++ r2)
       | _ => if Z.ltb (hi - lo) (2 ^ 64) then
                (if ranges_apart_pBF bc sp wb k (elen w) (ELit 0) lo (ELit (hi - lo)) then PKeep else PRepl [])
              else PRepl []
       end, m)
  | KZero (SA kb kk) len => zfK KZero kb kk len
  | KFill (SA kb kk) len c => zfK (fun a n => KFill a n c) kb kk len
  | KUnk (SA kb kk) len => zfK KUnk kb kk len
  | KWord (SA kb kk) w' v =>
      if same then ((if (Z.leb (kk + Z.of_nat w') k || Z.leb (k + Z.of_nat w) kk)%bool then PKeep else PRepl (kword_cut kb kk w' v k w)), m)
      else let '(r, m') := ranges_apart_pcBFM bc kb kk (elen w') sp RS DI wb k (elen w) br2 m in
           if r then (PKeep, m')
           else if (if Nat.eqb w 1 then if Nat.eqb w' 1 then expr_eqb wv v else false else false) then (PKeep, m')
           else (PRepl [], m')
  | KBlob (SA kb kk) len bk =>
      if same then
        (match len with
         | ELit l0 => let l := (l0 mod 2 ^ 64)%Z in
                      if (Z.leb (kk + l) k || Z.leb (k + Z.of_nat w) kk)%bool then PKeep else PRepl []
         | _ => if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl []
         end, m)
      else let '(r, m') := ranges_apart_pcBFM bc kb kk len sp RS DI wb k (elen w) br2 m in
           ((if r then PKeep else PRepl []), m')
  end.

(* [comment removed for export] *)
Definition ksubj (K : kentry) : expr * Z * expr :=
  match K with
  | KWord (SA kb kk) w' _ => (kb, kk, elen w')
  | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KUnk (SA kb kk) len | KBlob (SA kb kk) len _ => (kb, kk, len)
  | _ => (ELit 0, 0, ELit 0)
  end.
Definition kmemo_ok (bc : bctx) (K : kentry) (m : memo2) : Prop :=
  memo_ok bc (fst (fst (ksubj K))) (snd (fst (ksubj K))) (snd (ksubj K)) m.
Lemma kmemo_ok0 : forall bc K, kmemo_ok bc K memo0.
Proof. intros. apply memo_ok0. Qed.
Lemma kmemo_ok0b : forall bc K B, blk_ok bc B -> kmemo_ok bc K (memo0b B).
Proof. intros. apply memo_ok0b. assumption. Qed.
Lemma kmemo_ok_blk : forall bc K m, kmemo_ok bc K m -> blk_ok bc (mm_blk m).
Proof. intros bc K m H. exact (memo_ok_blk _ _ _ _ m H). Qed.
Definition rt_fun (bc : bctx) : Prop := forall i c m c' m', rt_In (bc_rt bc) i c m -> rt_In (bc_rt bc) i c' m' -> c = c' /\ m = m'.

Lemma prune1pcKM_spec : forall bc, rt_fun bc -> forall sp RS DI wa w wv K same br2 m, kmemo_ok bc K m -> sp_ok bc sp RS DI ->
  fst (prune1pcKM bc sp RS DI wa w wv K same br2 m) = prune1pcK bc sp wa w wv K same br2
  /\ kmemo_ok bc K (snd (prune1pcKM bc sp RS DI wa w wv K same br2 m)).
Proof.
  intros bc RTF sp RS DI wa w wv K same br2 m Hm Hsp. unfold prune1pcKM, prune1pcK, kmemo_ok in *.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    cbn [ksubj fst snd] in *; try (split; [reflexivity|exact Hm]).
  - (* [comment removed for export] *) destruct same; [split; [reflexivity|exact Hm]|].
    destruct (ranges_apart_pcBFM_spec bc kb kk (elen w') RTF sp RS DI (a_base wa) (a_off wa) (elen w) br2 m Hm Hsp) as [E1 E2].
    destruct (ranges_apart_pcBFM bc kb kk (elen w') sp RS DI (a_base wa) (a_off wa) (elen w) br2 m) as [r mm]. cbn [fst snd] in E1, E2.
    rewrite <- E1. destruct r; [split; [reflexivity|exact E2]|].
    replace (if Nat.eqb w 1 then if Nat.eqb w' 1 then expr_eqb wv v else false else false) with (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool
      by (destruct (Nat.eqb w 1), (Nat.eqb w' 1); reflexivity).
    destruct (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool; split; try reflexivity; exact E2.
  - (* [comment removed for export] *) destruct same; [split; [reflexivity|exact Hm]|].
    destruct (ranges_apart_pcBFM_spec bc kb kk len RTF sp RS DI (a_base wa) (a_off wa) (elen w) br2 m Hm Hsp) as [E1 E2].
    destruct (ranges_apart_pcBFM bc kb kk len sp RS DI (a_base wa) (a_off wa) (elen w) br2 m) as [r mm]. cbn [fst snd] in E1, E2.
    rewrite <- E1. destruct r; [split; [reflexivity|exact E2]|]. split; [|exact E2]. cbn [fst].
    destruct (kcutB bc KZero (a_base wa) (a_off wa) (elen w) kb kk len); reflexivity.
  - (* [comment removed for export] *) destruct same.
    + split; [|exact Hm]. cbn [fst]. destruct len; reflexivity.
    + destruct (ranges_apart_pcBFM_spec bc kb kk len RTF sp RS DI (a_base wa) (a_off wa) (elen w) br2 m Hm Hsp) as [E1 E2].
      destruct (ranges_apart_pcBFM bc kb kk len sp RS DI (a_base wa) (a_off wa) (elen w) br2 m) as [r mm]. cbn [fst snd] in E1, E2.
      rewrite <- E1. split; [reflexivity|exact E2].
  - (* [comment removed for export] *) destruct same; [split; [reflexivity|exact Hm]|].
    destruct (ranges_apart_pcBFM_spec bc kb kk len RTF sp RS DI (a_base wa) (a_off wa) (elen w) br2 m Hm Hsp) as [E1 E2].
    destruct (ranges_apart_pcBFM bc kb kk len sp RS DI (a_base wa) (a_off wa) (elen w) br2 m) as [r mm]. cbn [fst snd] in E1, E2.
    rewrite <- E1. destruct r; [split; [reflexivity|exact E2]|]. split; [|exact E2]. cbn [fst].
    destruct (kcutB bc (fun a n => KFill a n fc) (a_base wa) (a_off wa) (elen w) kb kk len); reflexivity.
  - (* [comment removed for export] *) destruct same; [split; [reflexivity|exact Hm]|].
    destruct (ranges_apart_pcBFM_spec bc kb kk len RTF sp RS DI (a_base wa) (a_off wa) (elen w) br2 m Hm Hsp) as [E1 E2].
    destruct (ranges_apart_pcBFM bc kb kk len sp RS DI (a_base wa) (a_off wa) (elen w) br2 m) as [r mm]. cbn [fst snd] in E1, E2.
    rewrite <- E1. destruct r; [split; [reflexivity|exact E2]|]. split; [|exact E2]. cbn [fst].
    destruct (kcutB bc KUnk (a_base wa) (a_off wa) (elen w) kb kk len); reflexivity.
Qed.


(* [comment removed for export] *)
Definition subj_tail_eqb (K K' : kentry) : bool :=
  if Z.eqb (snd (fst (ksubj K))) (snd (fst (ksubj K'))) then expr_eqb (snd (ksubj K)) (snd (ksubj K')) else false.
Lemma ksubj_base : forall K kb, kbase K = Some kb -> fst (fst (ksubj K)) = kb.
Proof. intros K kb H. destruct K as [[b k] w v|[b k] l|[b k] l bk| | | | | |[b k] l c|[b k] l]; cbn in *; congruence. Qed.
Lemma subj_tail_eqb_eq : forall K K' kb, kbase K = Some kb -> kbase K' = Some kb -> subj_tail_eqb K K' = true -> ksubj K' = ksubj K.
Proof.
  intros K K' kb H1 H2 E. unfold subj_tail_eqb in E.
  pose proof (ksubj_base _ _ H1) as B1. pose proof (ksubj_base _ _ H2) as B2.
  destruct (ksubj K) as [[b1 k1] n1]. destruct (ksubj K') as [[b2 k2] n2]. cbn [fst snd] in *.
  destruct (Z.eqb_spec k1 k2) as [->|]; [|discriminate]. apply p_expr_eqb_eq in E. subst. reflexivity.
Qed.
Lemma kmemo_ok_subj : forall bc K K' m, ksubj K' = ksubj K -> kmemo_ok bc K m -> kmemo_ok bc K' m.
Proof. intros bc K K' m E H. unfold kmemo_ok in *. rewrite E. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition stxr : Type := (stx * (list positive * list iside))%type.
Definition sx_ok (bc : bctx) (p : stxr) : Prop := sp_ok bc (sx_sp (fst p)) (fst (snd p)) (snd (snd p)).

Fixpoint mk_stxsF (bc : bctx) (log : list sentry) (t : ntab) : list stxr * ntab :=   (* [comment removed for export] *)
  match log with
  | [] => ([], t)
  | SE a w v :: older =>
      let '(sxs, t1) := mk_stxsF bc older t in
      let '(r, t2) := intern bc t1 (a_base a) in
      let '(bid, bi) := r in
      let RS := regs_w bc a w in
      (sxs ++ [(STX a w v (mk_sprepR bc RS (a_base a) w) bid (bi_br bi) (partners_of (bc_rt bc) RS), (RS, disj_sidesRI (rt_facts (bc_rt bc)) RS))], t2)
  end.
Lemma mk_stxsF_eq : forall bc log t,
  mk_stxs bc log t = (map fst (fst (mk_stxsF bc log t)), snd (mk_stxsF bc log t)).
Proof.
  intros bc log. induction log as [|[a w v] older IH]; intros t; [reflexivity|].
  cbn [mk_stxs mk_stxsF]. rewrite (IH t). destruct (mk_stxsF bc older t) as [sxs t1]. cbn [fst snd].
  destruct (intern bc t1 (a_base a)) as [[bid bi] t2]. cbn [fst snd]. rewrite map_app. reflexivity.
Qed.
Lemma rt_fun_mk : forall bc, bc_rt bc = mk_rt (bc_fk bc) -> rt_fun bc.
Proof. intros bc E. pose proof (mk_rt_wf (bc_fk bc)) as W. rewrite <- E in W. exact (rtw_fun _ _ W). Qed.
Lemma mk_stxsF_ok : forall bc log t, bc_rt bc = mk_rt (bc_fk bc) -> Forall (sx_ok bc) (fst (mk_stxsF bc log t)).
Proof.
  intros bc log t E. pose proof (mk_rt_wf (bc_fk bc)) as W. rewrite <- E in W. revert t.
  induction log as [|[a w v] older IH]; intros t; [constructor|].
  cbn [mk_stxsF]. specialize (IH t). destruct (mk_stxsF bc older t) as [sxs t1]. cbn [fst] in IH.
  destruct (intern bc t1 (a_base a)) as [[bid bi] t2]. cbn [fst].
  apply Forall_app. split; [exact IH|]. constructor; [|constructor].
  unfold sx_ok, sp_ok, mk_sprepR, D_of, di_ok. cbn [fst snd sx_sp sp_D sp_Dx]. repeat split.
  - apply disj_sidesRI_snd.
  - apply disj_sidesRI_in. intros i j s1 s2 IN. unfold iside_ok. cbn [fst snd]. exact (rtw_fids _ _ W i j s1 s2 IN).
Qed.

Fixpoint chainK2M (bc : bctx) (sxs : list stxr) (K : kentry) (okb : option expr) (same_of : positive -> bool) (br2 : option (Z * Z))
         (m : memo2) : list kentry :=
  match sxs with
  | [] => [K]
  | sxr :: rest =>
      let sx := fst sxr in
      match prune1pcKM bc (sx_sp sx) (fst (snd sxr)) (snd (snd sxr)) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 m with
      | (PKeep, m') => chainK2M bc rest K okb same_of br2 m'
      | (PRepl l, m') =>
          match okb with
          | Some kb =>
              flat_map (fun K' => match kbase K' with
                                  | Some kb' => if expr_eqb kb' kb then chainK2M bc rest K' okb same_of br2 (if subj_tail_eqb K K' then m' else memo0)
                                                else chain_slow bc (map fst rest) [K']
                                  | None => chain_slow bc (map fst rest) [K']
                                  end) l
          | None => chain_slow bc (map fst rest) l
          end
      end
  end.
Lemma flat_map_ext' : forall (X Y : Type) (f g : X -> list Y) l, (forall x, f x = g x) -> flat_map f l = flat_map g l.
Proof. intros X Y f g l H. induction l as [|x r IH]; [reflexivity|]. cbn. rewrite H, IH. reflexivity. Qed.
Lemma chainK2M_eq : forall bc, rt_fun bc -> forall sxs K okb same_of br2 m, Forall (sx_ok bc) sxs -> kmemo_ok bc K m ->
  (forall kb, okb = Some kb -> kbase K = Some kb) ->
  chainK2M bc sxs K okb same_of br2 m = chainK2 bc (map fst sxs) K okb same_of br2.
Proof.
  intros bc RTF sxs. induction sxs as [|[sx [RS DI]] rest IH]; intros K okb same_of br2 m HS Hm HB; [reflexivity|].
  apply Forall_cons_iff in HS as [H1 HS]. cbn [chainK2M chainK2 map fst snd].
  destruct (prune1pcKM_spec bc RTF (sx_sp sx) RS DI (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 m Hm H1) as [E1 E2].
  destruct (prune1pcKM bc (sx_sp sx) RS DI (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 m) as [r m']. cbn [fst snd] in E1, E2.
  rewrite <- E1. destruct r as [|l]; [apply IH; assumption|].
  destruct okb as [kb|]; [|reflexivity].
  apply flat_map_ext'. intros K'. destruct (kbase K') as [kb'|] eqn:HK'; [|reflexivity].
  destruct (expr_eqb kb' kb) eqn:Eb; [|reflexivity]. apply p_expr_eqb_eq in Eb. subst kb'.
  apply IH; [exact HS | | intros kb0 H0; injection H0 as <-; exact HK'].
  destruct (subj_tail_eqb K K') eqn:Es; [|apply kmemo_ok0].
  apply (kmemo_ok_subj bc K K' m'); [|exact E2]. exact (subj_tail_eqb_eq K K' kb (HB kb eq_refl) HK' Es).
Qed.

(* [comment removed for export] *)
Definition blkc : Type := list (expr * ptree (lsumx * lsumx)).
Fixpoint chainK2MB (bc : bctx) (sxs : list stxr) (K : kentry) (okb : option expr) (same_of : positive -> bool) (br2 : option (Z * Z))
         (m : memo2) : list kentry * blkc :=
  match sxs with
  | [] => ([K], mm_blk m)
  | sxr :: rest =>
      let sx := fst sxr in
      match prune1pcKM bc (sx_sp sx) (fst (snd sxr)) (snd (snd sxr)) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 m with
      | (PKeep, m') => chainK2MB bc rest K okb same_of br2 m'
      | (PRepl l, m') =>
          (match okb with
           | Some kb =>
               flat_map (fun K' => match kbase K' with
                                   | Some kb' => if expr_eqb kb' kb then chainK2M bc rest K' okb same_of br2 (if subj_tail_eqb K K' then m' else memo0)
                                                 else chain_slow bc (map fst rest) [K']
                                   | None => chain_slow bc (map fst rest) [K']
                                   end) l
           | None => chain_slow bc (map fst rest) l
           end, mm_blk m')
      end
  end.
Lemma chainK2MB_spec : forall bc, rt_fun bc -> forall sxs K okb same_of br2 m, Forall (sx_ok bc) sxs -> kmemo_ok bc K m ->
  fst (chainK2MB bc sxs K okb same_of br2 m) = chainK2M bc sxs K okb same_of br2 m /\ blk_ok bc (snd (chainK2MB bc sxs K okb same_of br2 m)).
Proof.
  intros bc RTF sxs. induction sxs as [|[sx [RS DI]] rest IH]; intros K okb same_of br2 m HS Hm; [split; [reflexivity|exact (kmemo_ok_blk bc K m Hm)]|].
  apply Forall_cons_iff in HS as [H1 HS]. cbn [chainK2MB chainK2M fst snd].
  destruct (prune1pcKM_spec bc RTF (sx_sp sx) RS DI (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 m Hm H1) as [_ E2].
  destruct (prune1pcKM bc (sx_sp sx) RS DI (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 m) as [r m']. cbn [fst snd] in E2 |- *.
  destruct r as [|l]; [apply IH; assumption|]. cbn [fst snd]. split; [reflexivity|exact (kmemo_ok_blk bc K m' E2)].
Qed.
Definition flF : Type := list (stxr * list stxr).
Definition fl_proj (fl : flF) : list (stx * list stx) := map (fun p => (fst (fst p), map fst (snd p))) fl.
Fixpoint mk_flF (cg : list positive) (g : gval) (sxs : list stxr) : flF :=
  match sxs with
  | [] => []
  | sx :: rest => if verdict2R cg (fst sx) g then mk_flF cg g rest else (sx, rest) :: mk_flF cg g rest
  end.
Lemma mk_flF_proj : forall cg g sxs, fl_proj (mk_flF cg g sxs) = mk_fl cg g (map fst sxs).
Proof.
  intros cg g sxs. induction sxs as [|sx rest IH]; [reflexivity|]. cbn [mk_flF mk_fl map].
  destruct (verdict2R cg (fst sx) g); [exact IH|]. cbn [fl_proj map fst snd]. f_equal. exact IH.
Qed.
(* [comment removed for export] *)
Definition vpre (sx : stxr) : option (Z * Z) :=
  match sp_rng (sx_sp (fst sx)) with
  | Some (lo1, hi1) => Some ((hi1 + a_off (sx_a (fst sx)) + sx_m1 (fst sx))%Z, (lo1 + a_off (sx_a (fst sx)))%Z)
  | None => None
  end.
Definition gpre (g : gval) : option (Z * Z) :=
  match g with
  | (_, _, Some (lo2, hi2), (glo, ghi)) => Some ((glo + lo2)%Z, (ghi + hi2)%Z)
  | _ => None
  end.
Definition verdictV (sx : stx) (v : option (Z * Z)) (g : gval) (gp : option (Z * Z)) : bool :=
  match g with
  | (b, _, _, _) =>
      if Pos.eqb b (sx_bid sx) then false else
      match v, gp with
      | Some (a1, b1), Some (c2, d2) => if Z.leb a1 c2 then true else Z.leb d2 b1
      | _, _ => false
      end
  end.
Lemma verdictV_eq : forall sx g, verdictV (fst sx) (vpre sx) g (gpre g) = verdict (fst sx) g.
Proof.
  intros [sx x] [[[b gkb] obr] [glo ghi]]. unfold verdictV, verdict, vpre, gpre. cbn [fst].
  destruct (Pos.eqb b (sx_bid sx)); [reflexivity|].
  destruct (sp_rng (sx_sp sx)) as [[lo1 hi1]|]; [|reflexivity]. destruct obr as [[lo2 hi2]|]; [|reflexivity].
  replace (Z.leb (hi1 + a_off (sx_a sx) + sx_m1 sx - lo2) glo) with (Z.leb (hi1 + a_off (sx_a sx) + sx_m1 sx) (glo + lo2))
    by (destruct (Z.leb_spec (hi1 + a_off (sx_a sx) + sx_m1 sx) (glo + lo2)); destruct (Z.leb_spec (hi1 + a_off (sx_a sx) + sx_m1 sx - lo2) glo); try reflexivity; lia).
  replace (Z.leb ghi (lo1 + a_off (sx_a sx) - hi2)) with (Z.leb (ghi + hi2) (lo1 + a_off (sx_a sx)))
    by (destruct (Z.leb_spec (ghi + hi2) (lo1 + a_off (sx_a sx))); destruct (Z.leb_spec ghi (lo1 + a_off (sx_a sx) - hi2)); try reflexivity; lia).
  destruct (Z.leb (hi1 + a_off (sx_a sx) + sx_m1 sx) (glo + lo2)); reflexivity.
Qed.
Fixpoint mk_flV (cg : list positive) (g : gval) (gp : option (Z * Z)) (sxs : list stxr) (vs : list (option (Z * Z))) : flF :=
  match sxs, vs with
  | sx :: rest, v :: vrest =>
      if (if verdictV (fst sx) v g gp then true else verdict_disjR cg (fst sx) g) then mk_flV cg g gp rest vrest
      else (sx, rest) :: mk_flV cg g gp rest vrest
  | _, _ => mk_flF cg g sxs
  end.
Lemma mk_flV_eq : forall cg g sxs, mk_flV cg g (gpre g) sxs (map vpre sxs) = mk_flF cg g sxs.
Proof.
  intros cg g sxs. induction sxs as [|sx rest IH]; [reflexivity|]. cbn [mk_flV mk_flF map]. rewrite verdictV_eq, IH. reflexivity.
Qed.
Lemma pt_map_ext : forall (A B : Type) (f h : A -> B) t, (forall a, f a = h a) -> pt_map f t = pt_map h t.
Proof. intros A B f h t H. induction t as [|l IHl o r IHr]; [reflexivity|]. cbn [pt_map]. rewrite IHl, IHr. destruct o; [rewrite H|]; reflexivity. Qed.
Definition fl_ok (bc : bctx) (fl : flF) : Prop := Forall (fun p => sx_ok bc (fst p) /\ Forall (sx_ok bc) (snd p)) fl.
Lemma mk_flF_ok : forall bc cg g sxs, Forall (sx_ok bc) sxs -> fl_ok bc (mk_flF cg g sxs).
Proof.
  intros bc cg g sxs. induction sxs as [|sx rest IH]; intros HS; [constructor|].
  apply Forall_cons_iff in HS as [H1 HS]. cbn [mk_flF]. destruct (verdict2R cg (fst sx) g); [exact (IH HS)|].
  constructor; [split; assumption | exact (IH HS)].
Qed.

Fixpoint chainKFM (bc : bctx) (fl : flF) (K : kentry) (okb : option expr) (same_of : positive -> bool)
         (br2 : option (Z * Z)) (m : memo2) : list kentry :=
  match fl with
  | [] => [K]
  | (sxr, rest) :: fl' =>
      let sx := fst sxr in
      match prune1pcKM bc (sx_sp sx) (fst (snd sxr)) (snd (snd sxr)) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 m with
      | (PKeep, m') => chainKFM bc fl' K okb same_of br2 m'
      | (PRepl l, m') =>
          match okb with
          | Some kb =>
              flat_map (fun K' => match kbase K' with
                                  | Some kb' => if expr_eqb kb' kb then chainK2M bc rest K' okb same_of br2 (if subj_tail_eqb K K' then m' else memo0)
                                                else chain_slow bc (map fst rest) [K']
                                  | None => chain_slow bc (map fst rest) [K']
                                  end) l
          | None => chain_slow bc (map fst rest) l
          end
      end
  end.
Lemma chainKFM_eq : forall bc, rt_fun bc -> forall fl K okb same_of br2 m, fl_ok bc fl -> kmemo_ok bc K m ->
  (forall kb, okb = Some kb -> kbase K = Some kb) ->
  chainKFM bc fl K okb same_of br2 m = chainKF bc (fl_proj fl) K okb same_of br2.
Proof.
  intros bc RTF fl. induction fl as [|[[sx [RS DI]] rest] fl' IH]; intros K okb same_of br2 m HS Hm HB; [reflexivity|].
  apply Forall_cons_iff in HS as [[H1 HR] HS]. cbn [chainKFM chainKF fl_proj map fst snd].
  destruct (prune1pcKM_spec bc RTF (sx_sp sx) RS DI (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 m Hm H1) as [E1 E2].
  destruct (prune1pcKM bc (sx_sp sx) RS DI (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 m) as [r m']. cbn [fst snd] in E1, E2.
  rewrite <- E1. destruct r as [|l]; [apply IH; assumption|].
  destruct okb as [kb|]; [|reflexivity].
  apply flat_map_ext'. intros K'. destruct (kbase K') as [kb'|] eqn:HK'; [|reflexivity].
  destruct (expr_eqb kb' kb) eqn:Eb; [|reflexivity]. apply p_expr_eqb_eq in Eb. subst kb'.
  apply (chainK2M_eq bc RTF); [exact HR | | intros kb0 H0; injection H0 as <-; exact HK'].
  destruct (subj_tail_eqb K K') eqn:Es; [|apply kmemo_ok0].
  apply (kmemo_ok_subj bc K K' m'); [|exact E2]. exact (subj_tail_eqb_eq K K' kb (HB kb eq_refl) HK' Es).
Qed.

Definition gflF : Type := (gval * flF)%type.
Definition mk_glF (bc : bctx) (bnds : gtab) (sxs : list stxr) : ptree gflF := pt_map (fun g => (g, mk_flF (cg_of bc g) g sxs)) bnds.
Definition mk_glV (bc : bctx) (bnds : gtab) (sxs : list stxr) : ptree gflF :=
  let vs := map vpre sxs in pt_map (fun g => (g, mk_flV (cg_of bc g) g (gpre g) sxs vs)) bnds.
Lemma mk_glV_eq : forall bc bnds sxs, mk_glV bc bnds sxs = mk_glF bc bnds sxs.
Proof. intros. unfold mk_glV, mk_glF. apply pt_map_ext. intros g. rewrite mk_flV_eq. reflexivity. Qed.

(* [comment removed for export] *)
Definition is_pure (K : kentry) : bool := match K with KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ => true | _ => false end.
Lemma chainK2M_pure : forall bc sxs K okb same_of br2 m, is_pure K = true -> chainK2M bc sxs K okb same_of br2 m = [K].
Proof.
  intros bc sxs K okb same_of br2. induction sxs as [|sxr rest IH]; intros m HP; [reflexivity|].
  cbn [chainK2M]. destruct K; try discriminate; cbn [prune1pcKM]; apply IH; exact HP.
Qed.
Fixpoint entriesGM (bc : bctx) (sxs : list stxr) (gl : ptree gflF) (kn : list kentry) (infos : list (option einfo)) : list kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      (match oi with
       | Some ei =>
           let okb := kbase K in
           let same_of := match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end in
           let br2 := match okb with Some _ => ei_br ei | None => None end in
           match pt_get gl (ei_gid ei) with
           | Some (g, fl) => if inb g ei then chainKFM bc fl K okb same_of br2 memo0 else chainK2M bc sxs K okb same_of br2 memo0
           | None => chainK2M bc sxs K okb same_of br2 memo0
           end
       | None => if is_pure K then [K] else chainK2M bc sxs K None (fun _ => false) None memo0
       end) ++ entriesGM bc sxs gl rest irest
  | _, _ => []
  end.
Lemma entriesGM_eq : forall bc, rt_fun bc -> forall sxs bnds kn infos, Forall (sx_ok bc) sxs ->
  entriesGM bc sxs (mk_glF bc bnds sxs) kn infos = entriesG bc (map fst sxs) (mk_gl bc bnds (map fst sxs)) kn infos.
Proof.
  intros bc RTF sxs bnds kn. induction kn as [|K rest IH]; intros infos HS; [reflexivity|].
  destruct infos as [|oi irest]; [reflexivity|]. cbn [entriesGM entriesG]. rewrite (IH irest HS). f_equal.
  destruct oi as [ei|].
  2:{ destruct (is_pure K) eqn:HP; [rewrite <- (chainK2M_pure bc sxs K None (fun _ => false) None memo0 HP)|]; apply (chainK2M_eq bc RTF); [exact HS | apply kmemo_ok0 | discriminate | exact HS | apply kmemo_ok0 | discriminate]. }
  unfold mk_glF, mk_gl. rewrite !pt_get_map.
  destruct (pt_get bnds (ei_gid ei)) as [g|]; [|apply (chainK2M_eq bc RTF); [exact HS | apply kmemo_ok0 | intros kb H; exact H]].
  destruct (inb g ei); [|apply (chainK2M_eq bc RTF); [exact HS | apply kmemo_ok0 | intros kb H; exact H]].
  rewrite <- mk_flF_proj. apply (chainKFM_eq bc RTF); [apply mk_flF_ok; exact HS | apply kmemo_ok0 | intros kb H; exact H].
Qed.

Fixpoint stores_partM (bc : bctx) (sxs : list stxr) : list kentry :=   (* [comment removed for export] *)
  match sxs with
  | [] => []
  | sxr :: newer => let sx := fst sxr in
      stores_partM bc newer ++ chainK2M bc newer (KWord (sx_a sx) (sx_w sx) (sx_v sx)) (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx) memo0
  end.
Lemma stores_partM_eq : forall bc, rt_fun bc -> forall sxs, Forall (sx_ok bc) sxs -> stores_partM bc sxs = stores_part bc (map fst sxs).
Proof.
  intros bc RTF sxs. induction sxs as [|[sx x] newer IH]; intros HS; [reflexivity|].
  apply Forall_cons_iff in HS as [_ HS]. cbn [stores_partM stores_part map fst]. rewrite (IH HS). f_equal.
  apply (chainK2M_eq bc RTF); [exact HS | apply kmemo_ok0|]. intros kb H. destruct (sx_a sx) as [b k]. exact H.
Qed.

Definition carryGF (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := mk_stxsF bc log nt_empty in
  let '(r, gs) := scan_entries bc kn t0 gst_empty in
  let '(infos, _) := r in
  stores_partM bc sxs ++ entriesGM bc sxs (mk_glF bc (gs_bnds gs) sxs) kn infos.
Lemma carryGF_eq : forall bc log kn, bc_rt bc = mk_rt (bc_fk bc) -> carryGF bc log kn = carryG bc log kn.
Proof.
  intros bc log kn E. unfold carryGF, carryG. rewrite (mk_stxsF_eq bc log nt_empty).
  pose proof (mk_stxsF_ok bc log nt_empty E) as HS. destruct (mk_stxsF bc log nt_empty) as [sxs t0]. cbn [fst snd] in *.
  destruct (scan_entries bc kn t0 gst_empty) as [[infos t1] gs]. rewrite (entriesGM_eq bc (rt_fun_mk bc E) sxs (gs_bnds gs) kn infos HS), (stores_partM_eq bc (rt_fun_mk bc E) sxs HS). reflexivity.
Qed.

Definition carryKF (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryGF bc log kn, [], [])
  | _, _ => carryB bc log kn hints
  end.
Theorem carryKF_eq : forall bc log kn hints, bc_rt bc = mk_rt (bc_fk bc) -> carryKF bc log kn hints = carryK bc log kn hints.
Proof. intros bc log kn hints E. unfold carryKF, carryK. destruct log; [reflexivity|]. destruct hints; [rewrite (carryGF_eq _ _ _ E)|]; reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint mk_stxsFL (bc : bctx) (log : list sentry) (lrs : list (list positive)) (t : ntab) : list stxr * ntab :=
  match log with
  | [] => ([], t)
  | SE a w v :: older =>
      let '(sxs, t1) := mk_stxsFL bc older (match lrs with _ :: r => r | [] => [] end) t in
      let '(r, t2) := intern bc t1 (a_base a) in
      let '(bid, bi) := r in
      let RS := match lrs with RS0 :: _ => if Nat.leb w 8 then RS0 else regs_w bc a w | [] => regs_w bc a w end in
      (sxs ++ [(STX a w v (mk_sprepR bc RS (a_base a) w) bid (bi_br bi) (partners_of (bc_rt bc) RS), (RS, disj_sidesRI (rt_facts (bc_rt bc)) RS))], t2)
  end.
Lemma zlit64_small : forall w, (w <= 8)%nat -> zlit64 (Z.of_nat w) = Z.of_nat w.
Proof.
  intros w H. unfold zlit64, two64.
  replace (Z.leb 0 (Z.of_nat w)) with true by (symmetry; apply Z.leb_le; lia).
  replace (Z.ltb (Z.of_nat w) (2 ^ 64)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma mk_stxsFL_eq : forall bc log lrs t, lrs = map (regsE bc) log -> mk_stxsFL bc log lrs t = mk_stxsF bc log t.
Proof.
  intros bc log. induction log as [|[[kb kk] w v] older IH]; intros lrs t ->; [reflexivity|].
  cbn [mk_stxsFL mk_stxsF map]. rewrite (IH _ t eq_refl).
  destruct (mk_stxsF bc older t) as [sxs t1]. destruct (intern bc t1 (a_base (SA kb kk))) as [[bid bi] t2].
  assert (E : (if Nat.leb w 8 then regsE bc (SE (SA kb kk) w v) else regs_w bc (SA kb kk) w) = regs_w bc (SA kb kk) w).
  { destruct (Nat.leb w 8) eqn:L; [|reflexivity]. apply Nat.leb_le in L. unfold regsE, regs_w. cbn [a_base a_off]. rewrite (zlit64_small w L). reflexivity. }
  rewrite E. reflexivity.
Qed.
(* [comment removed for export] *)
Definition rsc : Type := option (list positive * (list (saddr * expr) * list iside)).
Definition rsc_ok (bc : bctx) (c : rsc) : Prop :=
  match c with Some (RS, v) => v = (disj_sidesR (rt_facts (bc_rt bc)) RS, disj_sidesRI (rt_facts (bc_rt bc)) RS) | None => True end.
Definition rs_get (bc : bctx) (RS : list positive) (c : rsc) : (list (saddr * expr) * list iside) * rsc :=
  match c with
  | Some (RS', v) =>
      if lp_eqb RS RS' then (v, c)
      else let v' := (disj_sidesR (rt_facts (bc_rt bc)) RS, disj_sidesRI (rt_facts (bc_rt bc)) RS) in (v', Some (RS, v'))
  | None => let v' := (disj_sidesR (rt_facts (bc_rt bc)) RS, disj_sidesRI (rt_facts (bc_rt bc)) RS) in (v', Some (RS, v'))
  end.
Lemma rs_get_spec : forall bc RS c, rsc_ok bc c ->
  fst (rs_get bc RS c) = (disj_sidesR (rt_facts (bc_rt bc)) RS, disj_sidesRI (rt_facts (bc_rt bc)) RS) /\ rsc_ok bc (snd (rs_get bc RS c)).
Proof.
  intros bc RS c H. unfold rs_get. destruct c as [[RS' v]|]; [|split; reflexivity].
  destruct (lp_eqb RS RS') eqn:E; [|split; reflexivity]. apply lp_eqb_eq in E. subst RS'. cbn [fst snd]. split; [exact H|exact H].
Qed.
Fixpoint mk_stxsFC (bc : bctx) (log : list sentry) (lrs : list (list positive)) (t : ntab) : list stxr * ntab * rsc :=
  match log with
  | [] => ([], t, None)
  | SE a w v :: older =>
      let '(sxs, t1, c1) := mk_stxsFC bc older (match lrs with _ :: r => r | [] => [] end) t in
      let '(r, t2) := intern bc t1 (a_base a) in
      let '(bid, bi) := r in
      let RS := match lrs with RS0 :: _ => if Nat.leb w 8 then RS0 else regs_w bc a w | [] => regs_w bc a w end in
      let '(DD, c2) := rs_get bc RS c1 in
      (sxs ++ [(STX a w v (SPrep (base_rangeB bc (a_base a)) (xhiB bc (elen w)) (fst DD) (fst DD)) bid (bi_br bi) (partners_of (bc_rt bc) RS), (RS, snd DD))], t2, c2)
  end.
Lemma mk_stxsFC_eq : forall bc log lrs t,
  fst (mk_stxsFC bc log lrs t) = mk_stxsFL bc log lrs t /\ rsc_ok bc (snd (mk_stxsFC bc log lrs t)).
Proof.
  intros bc log. induction log as [|[a w v] older IH]; intros lrs t; [split; reflexivity|].
  cbn [mk_stxsFC mk_stxsFL]. destruct (IH (match lrs with _ :: r => r | [] => [] end) t) as [E1 E2].
  destruct (mk_stxsFC bc older (match lrs with _ :: r => r | [] => [] end) t) as [[sxs t1] c1]. cbn [fst snd] in E1, E2. rewrite <- E1.
  destruct (intern bc t1 (a_base a)) as [[bid bi] t2].
  destruct (rs_get_spec bc (match lrs with RS0 :: _ => if Nat.leb w 8 then RS0 else regs_w bc a w | [] => regs_w bc a w end) c1 E2) as [G1 G2].
  destruct (rs_get bc (match lrs with RS0 :: _ => if Nat.leb w 8 then RS0 else regs_w bc a w | [] => regs_w bc a w end) c1) as [DD c2].
  cbn [fst snd] in G1, G2 |- *. subst DD. cbn [fst snd]. split; [reflexivity|exact G2].
Qed.
Definition carryGFL (bc : bctx) (log : list sentry) (lrs : list (list positive)) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := fst (mk_stxsFC bc log lrs nt_empty) in
  let '(r, gs) := scan_entries bc kn t0 gst_empty in
  let '(infos, _) := r in
  stores_partM bc sxs ++ entriesGM bc sxs (mk_glV bc (gs_bnds gs) sxs) kn infos.
Definition carryKFL (bc : bctx) (log : list sentry) (lrs : list (list positive)) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryGFL bc log lrs kn, [], [])
  | _, _ => carryB bc log kn hints
  end.
Lemma carryKFL_eq : forall bc log lrs kn hints, bc_rt bc = mk_rt (bc_fk bc) -> lrs = map (regsE bc) log ->
  carryKFL bc log lrs kn hints = carryKF bc log kn hints.
Proof.
  intros bc log lrs kn hints _ L. unfold carryKFL, carryKF, carryGFL, carryGF. rewrite (proj1 (mk_stxsFC_eq bc log lrs nt_empty)). rewrite (mk_stxsFL_eq bc log lrs nt_empty L).
  destruct log; [reflexivity|]. destruct hints; [|reflexivity]. destruct (mk_stxsF bc (s :: log) nt_empty) as [sxs t0].
  destruct (scan_entries bc kn t0 gst_empty) as [[infos t1] gs]. rewrite mk_glV_eq. reflexivity.
Qed.

End CXFC.
