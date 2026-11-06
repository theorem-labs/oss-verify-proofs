(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AxSymExec3 AxSymExec3B.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxfCarry CxfL1 CxfL2 CxfLeaf CxfNat.
Import ListNotations.
Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module CXFCL.
Import CXFC.
Notation "x && y" := (if x then y else false) (at level 40, left associativity) : bool_scope.
Notation "x || y" := (if x then true else y) (at level 50, left associativity) : bool_scope.
Import AX2.
Import AX2L.
Import AX2B.
Import AX2BL.
Fixpoint lp_eqb (a b : list positive) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => if Pos.eqb x y then lp_eqb a' b' else false
  | _, _ => false
  end.
Lemma L_CXFCL_lp_eqb : @lp_eqb = @CXFC.lp_eqb.
Proof. unfold lp_eqb. reflexivity. Qed.

Definition memo1 : Type := list (list positive * bool).
Lemma L_CXFCL_memo1 : @memo1 = @CXFC.memo1.
Proof. unfold memo1. reflexivity. Qed.

Fixpoint memo_get (m : memo1) (RS : list positive) : option bool :=
  match m with
  | [] => None
  | (RS', b) :: r => if lp_eqb RS RS' then Some b else memo_get r RS
  end.
Lemma L_CXFCL_memo_get : @memo_get = @CXFC.memo_get.
Proof. unfold memo_get. rewrite ?L_CXFCL_lp_eqb, ?L_CXFCL_memo1. reflexivity. Qed.

Definition iside : Type := (positive * (saddr * expr))%type.
Lemma L_CXFCL_iside : @iside = @CXFC.iside.
Proof. unfold iside. reflexivity. Qed.

Fixpoint disj_sidesRI (fs : list dfact) (RS : list positive) : list iside :=
  match fs with
  | [] => []
  | (i, j, (s1, s2)) :: rest =>
      let r := disj_sidesRI rest RS in
      let r1 := if pmem j RS then (i, s1) :: r else r in
      if pmem i RS then (j, s2) :: r1 else r1
  end.
Lemma L_CXFCL_disj_sidesRI : @disj_sidesRI = @CXFC.disj_sidesRI.
Proof. unfold disj_sidesRI. rewrite ?L_CXFCL_iside, ?AX2BL.L_AX2BL_dfact, ?AX2BL.L_AX2BL_pmem. reflexivity. Qed.

Definition linsum : Type := option (Z * list (Z * expr) * option (Z * Z) * bool).
Lemma L_CXFCL_linsum : @linsum = @CXFC.linsum.
Proof. unfold linsum. reflexivity. Qed.

Definition lsumx : Type := (option (Z * Z) * bool * Z * bool)%type.
Lemma L_CXFCL_lsumx : @lsumx = @CXFC.lsumx.
Proof. unfold lsumx. reflexivity. Qed.

Definition memo0 : memo2 := MM [] [] PTLeaf PTLeaf None None None [].
Lemma L_CXFCL_memo0 : @memo0 = @CXFC.memo0.
Proof. unfold memo0. reflexivity. Qed.

Definition memo0b (B : list (expr * ptree (lsumx * lsumx))) : memo2 := MM [] [] PTLeaf PTLeaf None None None B.
Lemma L_CXFCL_memo0b : @memo0b = @CXFC.memo0b.
Proof. unfold memo0b. rewrite ?L_CXFCL_lsumx. reflexivity. Qed.

Section Entry.
Variable bc : bctx.
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
Definition lin_get (b1 : expr) (m : memo2) : linsum * memo2 :=
  match mm_lin m with
  | Some (b1c, LS) =>
      if expr_eqb b1 b1c then (LS, m)
      else let LS' := linsum_of b1 in (LS', MM (mm_L m) (mm_X m) (mm_sL m) (mm_sX m) (Some (b1, LS')) (mm_h2 m) (mm_linx m) (mm_blk m))
  | None => let LS' := linsum_of b1 in (LS', MM (mm_L m) (mm_X m) (mm_sL m) (mm_sX m) (Some (b1, LS')) (mm_h2 m) (mm_linx m) (mm_blk m))
  end.
Definition h2_get (m : memo2) : option Z * memo2 :=
  match mm_h2 m with
  | Some v => (v, m)
  | None => let v := xhiB bc n2 in (v, MM (mm_L m) (mm_X m) (mm_sL m) (mm_sX m) (mm_lin m) (Some v) (mm_linx m) (mm_blk m))
  end.
Definition linx_get (b1 : expr) (m : memo2) : (lsumx * lsumx) * memo2 :=
  match mm_linx m with
  | Some (b1c, SX) =>
      if expr_eqb b1 b1c then (SX, m)
      else let SX' := linx_of b1 in (SX', MM (mm_L m) (mm_X m) (mm_sL m) (mm_sX m) (mm_lin m) (mm_h2 m) (Some (b1, SX')) (mm_blk m))
  | None => let SX' := linx_of b1 in (SX', MM (mm_L m) (mm_X m) (mm_sL m) (mm_sX m) (mm_lin m) (mm_h2 m) (Some (b1, SX')) (mm_blk m))
  end.
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
Definition sub_itvBQ (qp : qprep) (b : expr) (k n : Z) (c : saddr) (ml : expr) : bool :=
  if (if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
        match xloB bc ml with Some l => Z.leb (k + n) (a_off c + l) | None => false end
      else false)
  then true
  else if (Z.leb 0 n && Z.ltb n two64)%bool then xinsideBQ bc qp b k (ELit n) (a_base c) (a_off c) ml else false.
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
Definition btree : Type := ptree (lsumx * lsumx).
Definition bt_ok (bt : btree) : Prop :=
  forall i SM, pt_get bt i = Some SM -> forall c ml, rt_In (bc_rt bc) i c ml -> SM = sidesumG b2 (a_base c) ml.
Definition xinside0S (SM : lsumx * lsumx) (cb : expr) (ck : Z) (ml : expr) (z1 : Z) : bool :=
  if sgeA (fst SM) cb ck then sgeB (snd SM) cb ck ml z1 else false.
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
Definition blk_tree (B : list (expr * btree)) : btree :=
  match List.find (fun bt => expr_eqb b2 (fst bt)) B with Some bt => snd bt | None => PTLeaf end.
Definition blk_put (B : list (expr * btree)) (bt : btree) : list (expr * btree) :=
  (b2, bt) :: List.firstn 5 (List.filter (fun x => negb (expr_eqb b2 (fst x))) B).
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
Definition xtail (RS : list positive) (DI : list iside) (b1 : expr) (k1 : Z) (n1 : expr) (m : memo2) : bool * memo2 :=
  let '(r, m') := sidesX RS DI m in
  if r then (true, m')
  else if negb (shares_var b1 b2) then (false, m')
  else let sm := linx_get b1 m' in
       if geA (fst (fst sm)) b1 k1 n1 then (true, snd sm)
       else (geB (snd (fst sm)) b1 k1, snd sm).
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
Lemma L_CXFCL_D_of : @D_of = @CXFC.D_of.
Proof. unfold D_of. rewrite ?AX2BL.L_AX2BL_disj_sidesR. reflexivity. Qed.

Lemma L_CXFCL_iside_ok : @iside_ok = @CXFC.iside_ok.
Proof. unfold iside_ok. rewrite ?L_CXFCL_iside, ?AX2BL.L_AX2BL_rt_In. reflexivity. Qed.

Lemma L_CXFCL_linsum_of : @linsum_of = @CXFC.linsum_of.
Proof. unfold linsum_of. rewrite ?L_CXFCL_linsum, ?AX2BL.L_AX2BL_erangeB, ?AX2BL.L_AX2BL_lin_nowrapRB, ?AX2L.L_AX2L_lin_of, ?AX2L.L_AX2L_lin_range, ?AX2L.L_AX2L_lsub_e, ?AX2L.L_AX2L_shares_var. reflexivity. Qed.

Lemma L_CXFCL_lin_via : @lin_via = @CXFC.lin_via.
Proof. unfold lin_via. rewrite ?L_CXFCL_linsum, ?AX2BL.L_AX2BL_lin_test_relB. reflexivity. Qed.

Lemma L_CXFCL_linx_of : @linx_of = @CXFC.linx_of.
Proof. unfold linx_of. rewrite ?L_CXFCL_lsumx, ?AX2BL.L_AX2BL_erangeB, ?AX2L.L_AX2L_has_round, ?AX2BL.L_AX2BL_lin_nowrapRB, ?AX2L.L_AX2L_lin_of, ?AX2L.L_AX2L_lin_range, ?AX2L.L_AX2L_lsub_e, ?AX2L.L_AX2L_xt_lin. reflexivity. Qed.

Lemma L_CXFCL_geA : @geA = @CXFC.geA.
Proof. unfold geA. rewrite ?L_CXFCL_lsumx, ?AX2BL.L_AX2BL_lin_ge0BF, ?AX2BL.L_AX2BL_lin_nowrapRB, ?AX2L.L_AX2L_snorm. reflexivity. Qed.

Lemma L_CXFCL_geB : @geB = @CXFC.geB.
Proof. unfold geB. rewrite ?L_CXFCL_lsumx, ?AX2BL.L_AX2BL_lin_ge0BF. reflexivity. Qed.

Lemma L_CXFCL_sidesumG : @sidesumG = @CXFC.sidesumG.
Proof. unfold sidesumG. rewrite ?L_CXFCL_lsumx, ?AX2BL.L_AX2BL_erangeB, ?AX2L.L_AX2L_has_round, ?AX2BL.L_AX2BL_lin_nowrapRB, ?AX2L.L_AX2L_lin_of, ?AX2L.L_AX2L_lin_range, ?AX2L.L_AX2L_lsub_e, ?AX2L.L_AX2L_xt_lin. reflexivity. Qed.

Lemma L_CXFCL_sidesum : @sidesum = @CXFC.sidesum.
Proof. unfold sidesum. rewrite ?L_CXFCL_lsumx, ?L_CXFCL_sidesumG. reflexivity. Qed.

Lemma L_CXFCL_sgeA : @sgeA = @CXFC.sgeA.
Proof. unfold sgeA. rewrite ?L_CXFCL_lsumx, ?AX2BL.L_AX2BL_lin_ge0BF. reflexivity. Qed.

Lemma L_CXFCL_sgeB : @sgeB = @CXFC.sgeB.
Proof. unfold sgeB. rewrite ?L_CXFCL_lsumx, ?AX2BL.L_AX2BL_lin_ge0BF, ?AX2BL.L_AX2BL_lin_nowrapRB, ?AX2L.L_AX2L_snorm. reflexivity. Qed.

Lemma L_CXFCL_blk_ok : @blk_ok = @CXFC.blk_ok.
Proof. unfold blk_ok. rewrite ?L_CXFCL_lsumx, ?L_CXFCL_sidesumG, ?AX2L.L_AX2L_pt_get, ?AX2BL.L_AX2BL_rt_In. reflexivity. Qed.

Lemma L_CXFCL_memo_ok : @memo_ok = @CXFC.memo_ok.
Proof. unfold memo_ok. rewrite ?L_CXFCL_D_of, ?L_CXFCL_linsum_of, ?L_CXFCL_linx_of, ?L_CXFCL_blk_ok, ?AX2BL.L_AX2BL_in_sidesB, ?AX2BL.L_AX2BL_in_sides_xB, ?AX2L.L_AX2L_pt_get, ?AX2BL.L_AX2BL_rt_In, ?AX2BL.L_AX2BL_sub_itvB, ?AX2BL.L_AX2BL_sub_itv_xB, ?AX2BL.L_AX2BL_xhiB, ?AX2L.L_AX2L_zlit64. reflexivity. Qed.

Lemma L_CXFCL_lin_get : @lin_get = @CXFC.lin_get.
Proof. unfold lin_get. rewrite ?L_CXFCL_linsum, ?L_CXFCL_linsum_of, ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Lemma L_CXFCL_h2_get : @h2_get = @CXFC.h2_get.
Proof. unfold h2_get. rewrite ?AX2BL.L_AX2BL_xhiB. reflexivity. Qed.

Lemma L_CXFCL_linx_get : @linx_get = @CXFC.linx_get.
Proof. unfold linx_get. rewrite ?L_CXFCL_lsumx, ?L_CXFCL_linx_of, ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Lemma L_CXFCL_scanL : @scanL = @CXFC.scanL.
Proof. unfold scanL. rewrite ?L_CXFCL_iside, ?AX2L.L_AX2L_pt_get, ?AX2L.L_AX2L_pt_set, ?AX2BL.L_AX2BL_sub_itvB. reflexivity. Qed.

Lemma L_CXFCL_scanX : @scanX = @CXFC.scanX.
Proof. unfold scanX. rewrite ?L_CXFCL_iside, ?AX2L.L_AX2L_pt_get, ?AX2L.L_AX2L_pt_set, ?AX2BL.L_AX2BL_sub_itv_xB. reflexivity. Qed.

Lemma L_CXFCL_sL_ok : @sL_ok = @CXFC.sL_ok.
Proof. unfold sL_ok. rewrite ?AX2L.L_AX2L_pt_get, ?AX2BL.L_AX2BL_rt_In, ?AX2BL.L_AX2BL_sub_itvB. reflexivity. Qed.

Lemma L_CXFCL_sX_ok : @sX_ok = @CXFC.sX_ok.
Proof. unfold sX_ok. rewrite ?AX2L.L_AX2L_pt_get, ?AX2BL.L_AX2BL_rt_In, ?AX2BL.L_AX2BL_sub_itv_xB. reflexivity. Qed.

Lemma L_CXFCL_sub_itvBQ : @sub_itvBQ = @CXFC.sub_itvBQ.
Proof. unfold sub_itvBQ. rewrite ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_two64, ?AX2BL.L_AX2BL_xinsideBQ, ?AX2BL.L_AX2BL_xloB. reflexivity. Qed.

Lemma L_CXFCL_scanLQ : @scanLQ = @CXFC.scanLQ.
Proof. unfold scanLQ. rewrite ?L_CXFCL_iside, ?L_CXFCL_sub_itvBQ, ?AX2L.L_AX2L_pt_get, ?AX2L.L_AX2L_pt_set. reflexivity. Qed.

Lemma L_CXFCL_btree : @btree = @CXFC.btree.
Proof. unfold btree. rewrite ?L_CXFCL_lsumx. reflexivity. Qed.

Lemma L_CXFCL_bt_ok : @bt_ok = @CXFC.bt_ok.
Proof. unfold bt_ok. rewrite ?L_CXFCL_sidesumG, ?L_CXFCL_btree, ?AX2L.L_AX2L_pt_get, ?AX2BL.L_AX2BL_rt_In. reflexivity. Qed.

Lemma L_CXFCL_xinside0S : @xinside0S = @CXFC.xinside0S.
Proof. unfold xinside0S. rewrite ?L_CXFCL_lsumx, ?L_CXFCL_sgeA, ?L_CXFCL_sgeB. reflexivity. Qed.

Lemma L_CXFCL_side_test : @side_test = @CXFC.side_test.
Proof. unfold side_test. rewrite ?L_CXFCL_sidesumG, ?L_CXFCL_btree, ?L_CXFCL_xinside0S, ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_novars, ?AX2L.L_AX2L_pt_get, ?AX2L.L_AX2L_pt_set, ?AX2L.L_AX2L_shares_var, ?AX2L.L_AX2L_two64, ?AX2BL.L_AX2BL_xinside_jtBQ, ?AX2BL.L_AX2BL_xinside_numBQ, ?AX2BL.L_AX2BL_xloB. reflexivity. Qed.

Lemma L_CXFCL_scanLB : @scanLB = @CXFC.scanLB.
Proof. unfold scanLB. rewrite ?L_CXFCL_iside, ?L_CXFCL_btree, ?L_CXFCL_side_test, ?AX2L.L_AX2L_pt_get, ?AX2L.L_AX2L_pt_set. reflexivity. Qed.

Lemma L_CXFCL_blk_tree : @blk_tree = @CXFC.blk_tree.
Proof. unfold blk_tree. rewrite ?L_CXFCL_btree, ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Lemma L_CXFCL_blk_put : @blk_put = @CXFC.blk_put.
Proof. unfold blk_put. rewrite ?L_CXFCL_btree, ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Lemma L_CXFCL_sidesL : @sidesL = @CXFC.sidesL.
Proof. unfold sidesL. rewrite ?L_CXFCL_memo_get, ?L_CXFCL_iside, ?L_CXFCL_scanLB, ?L_CXFCL_blk_tree, ?L_CXFCL_blk_put, ?AX2BL.L_AX2BL_mkqp. reflexivity. Qed.

Lemma L_CXFCL_sidesX : @sidesX = @CXFC.sidesX.
Proof. unfold sidesX. rewrite ?L_CXFCL_memo_get, ?L_CXFCL_iside, ?L_CXFCL_scanX. reflexivity. Qed.

Lemma L_CXFCL_di_ok : @di_ok = @CXFC.di_ok.
Proof. unfold di_ok. rewrite ?L_CXFCL_iside, ?L_CXFCL_D_of, ?L_CXFCL_iside_ok. reflexivity. Qed.

Lemma L_CXFCL_xtail : @xtail = @CXFC.xtail.
Proof. unfold xtail. rewrite ?L_CXFCL_iside, ?L_CXFCL_geA, ?L_CXFCL_geB, ?L_CXFCL_linx_get, ?L_CXFCL_sidesX, ?AX2L.L_AX2L_shares_var. reflexivity. Qed.

Lemma L_CXFCL_ranges_apart_pcBFM : @ranges_apart_pcBFM = @CXFC.ranges_apart_pcBFM.
Proof. unfold ranges_apart_pcBFM. rewrite ?L_CXFCL_iside, ?L_CXFCL_lin_via, ?L_CXFCL_lin_get, ?L_CXFCL_h2_get, ?L_CXFCL_sidesL, ?L_CXFCL_xtail, ?AX2BL.L_AX2BL_end_hiB, ?AX2L.L_AX2L_zlit64. reflexivity. Qed.

Lemma L_CXFCL_sp_ok : @sp_ok = @CXFC.sp_ok.
Proof. unfold sp_ok. rewrite ?L_CXFCL_iside, ?L_CXFCL_D_of, ?L_CXFCL_di_ok. reflexivity. Qed.

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
       | _ => if Z.ltb (hi - lo) (CXLF.p64) then
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
           else if (if CXNAT.eqbF w 1 then if CXNAT.eqbF w' 1 then expr_eqb wv v else false else false) then (PKeep, m')
           else (PRepl [], m')
  | KBlob (SA kb kk) len bk =>
      if same then
        (match len with
         | ELit l0 => let l := (CXLF.zm64 l0)%Z in
                      if (Z.leb (kk + l) k || Z.leb (k + Z.of_nat w) kk)%bool then PKeep else PRepl []
         | _ => if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl []
         end, m)
      else let '(r, m') := ranges_apart_pcBFM bc kb kk len sp RS DI wb k (elen w) br2 m in
           ((if r then PKeep else PRepl []), m')
  end.
Lemma L_CXFCL_prune1pcKM : @prune1pcKM = @CXFC.prune1pcKM.
Proof. unfold prune1pcKM. rewrite ?L_CXFCL_iside, ?L_CXFCL_ranges_apart_pcBFM, ?AX2L.L_AX2L_elen, ?AX2L.L_AX2L_expr_eqb, ?AX2BL.L_AX2BL_kcutB, ?AX2L.L_AX2L_ktrim, ?AX2L.L_AX2L_kword_cut, ?AX2BL.L_AX2BL_ranges_apart_pBF, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition ksubj (K : kentry) : expr * Z * expr :=
  match K with
  | KWord (SA kb kk) w' _ => (kb, kk, elen w')
  | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KUnk (SA kb kk) len | KBlob (SA kb kk) len _ => (kb, kk, len)
  | _ => (ELit 0, 0, ELit 0)
  end.
Lemma L_CXFCL_ksubj : @ksubj = @CXFC.ksubj.
Proof. unfold ksubj. rewrite ?AX2L.L_AX2L_elen. reflexivity. Qed.

Definition kmemo_ok (bc : bctx) (K : kentry) (m : memo2) : Prop :=
  memo_ok bc (fst (fst (ksubj K))) (snd (fst (ksubj K))) (snd (ksubj K)) m.
Lemma L_CXFCL_kmemo_ok : @kmemo_ok = @CXFC.kmemo_ok.
Proof. unfold kmemo_ok. rewrite ?L_CXFCL_memo_ok, ?L_CXFCL_ksubj. reflexivity. Qed.

Definition rt_fun (bc : bctx) : Prop := forall i c m c' m', rt_In (bc_rt bc) i c m -> rt_In (bc_rt bc) i c' m' -> c = c' /\ m = m'.
Lemma L_CXFCL_rt_fun : @rt_fun = @CXFC.rt_fun.
Proof. unfold rt_fun. rewrite ?AX2BL.L_AX2BL_rt_In. reflexivity. Qed.

Definition subj_tail_eqb (K K' : kentry) : bool :=
  if Z.eqb (snd (fst (ksubj K))) (snd (fst (ksubj K'))) then expr_eqb (snd (ksubj K)) (snd (ksubj K')) else false.
Lemma L_CXFCL_subj_tail_eqb : @subj_tail_eqb = @CXFC.subj_tail_eqb.
Proof. unfold subj_tail_eqb. rewrite ?L_CXFCL_ksubj, ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Definition stxr : Type := (stx * (list positive * list iside))%type.
Lemma L_CXFCL_stxr : @stxr = @CXFC.stxr.
Proof. unfold stxr. rewrite ?L_CXFCL_iside. reflexivity. Qed.

Definition sx_ok (bc : bctx) (p : stxr) : Prop := sp_ok bc (sx_sp (fst p)) (fst (snd p)) (snd (snd p)).
Lemma L_CXFCL_sx_ok : @sx_ok = @CXFC.sx_ok.
Proof. unfold sx_ok. rewrite ?L_CXFCL_sp_ok, ?L_CXFCL_stxr. reflexivity. Qed.

Fixpoint mk_stxsF (bc : bctx) (log : list sentry) (t : ntab) : list stxr * ntab :=   
  match log with
  | [] => ([], t)
  | SE a w v :: older =>
      let '(sxs, t1) := mk_stxsF bc older t in
      let '(r, t2) := intern bc t1 (a_base a) in
      let '(bid, bi) := r in
      let RS := regs_w bc a w in
      (sxs ++ [(STX a w v (mk_sprepR bc RS (a_base a) w) bid (bi_br bi) (partners_of (bc_rt bc) RS), (RS, disj_sidesRI (rt_facts (bc_rt bc)) RS))], t2)
  end.
Lemma L_CXFCL_mk_stxsF : @mk_stxsF = @CXFC.mk_stxsF.
Proof. unfold mk_stxsF. rewrite ?L_CXFCL_disj_sidesRI, ?L_CXFCL_stxr, ?AX2BL.L_AX2BL_intern, ?AX2BL.L_AX2BL_mk_sprepR, ?AX2BL.L_AX2BL_partners_of, ?AX2BL.L_AX2BL_regs_w. reflexivity. Qed.

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
Lemma L_CXFCL_chainK2M : @chainK2M = @CXFC.chainK2M.
Proof. unfold chainK2M. rewrite ?L_CXFCL_memo0, ?L_CXFCL_prune1pcKM, ?L_CXFCL_subj_tail_eqb, ?L_CXFCL_stxr, ?AX2BL.L_AX2BL_chain_slow, ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_kbase. reflexivity. Qed.

Definition blkc : Type := list (expr * ptree (lsumx * lsumx)).
Lemma L_CXFCL_blkc : @blkc = @CXFC.blkc.
Proof. unfold blkc. rewrite ?L_CXFCL_lsumx. reflexivity. Qed.

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
Lemma L_CXFCL_chainK2MB : @chainK2MB = @CXFC.chainK2MB.
Proof. unfold chainK2MB. rewrite ?L_CXFCL_memo0, ?L_CXFCL_prune1pcKM, ?L_CXFCL_subj_tail_eqb, ?L_CXFCL_stxr, ?L_CXFCL_chainK2M, ?L_CXFCL_blkc, ?AX2BL.L_AX2BL_chain_slow, ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_kbase. reflexivity. Qed.

Definition flF : Type := list (stxr * list stxr).
Lemma L_CXFCL_flF : @flF = @CXFC.flF.
Proof. unfold flF. rewrite ?L_CXFCL_stxr. reflexivity. Qed.

Definition fl_proj (fl : flF) : list (stx * list stx) := map (fun p => (fst (fst p), map fst (snd p))) fl.
Lemma L_CXFCL_fl_proj : @fl_proj = @CXFC.fl_proj.
Proof. unfold fl_proj. rewrite ?L_CXFCL_flF. reflexivity. Qed.

Fixpoint mk_flF (cg : list positive) (g : gval) (sxs : list stxr) : flF :=
  match sxs with
  | [] => []
  | sx :: rest => if verdict2R cg (fst sx) g then mk_flF cg g rest else (sx, rest) :: mk_flF cg g rest
  end.
Lemma L_CXFCL_mk_flF : @mk_flF = @CXFC.mk_flF.
Proof. unfold mk_flF. rewrite ?L_CXFCL_stxr, ?L_CXFCL_flF, ?AX2BL.L_AX2BL_gval, ?AX2BL.L_AX2BL_verdict2R. reflexivity. Qed.

Definition vpre (sx : stxr) : option (Z * Z) :=
  match sp_rng (sx_sp (fst sx)) with
  | Some (lo1, hi1) => Some ((hi1 + a_off (sx_a (fst sx)) + sx_m1 (fst sx))%Z, (lo1 + a_off (sx_a (fst sx)))%Z)
  | None => None
  end.
Lemma L_CXFCL_vpre : @vpre = @CXFC.vpre.
Proof. unfold vpre. rewrite ?L_CXFCL_stxr, ?AX2BL.L_AX2BL_sx_m1. reflexivity. Qed.

Definition gpre (g : gval) : option (Z * Z) :=
  match g with
  | (_, _, Some (lo2, hi2), (glo, ghi)) => Some ((glo + lo2)%Z, (ghi + hi2)%Z)
  | _ => None
  end.
Lemma L_CXFCL_gpre : @gpre = @CXFC.gpre.
Proof. unfold gpre. rewrite ?AX2BL.L_AX2BL_gval. reflexivity. Qed.

Definition verdictV (sx : stx) (v : option (Z * Z)) (g : gval) (gp : option (Z * Z)) : bool :=
  match g with
  | (b, _, _, _) =>
      if Pos.eqb b (sx_bid sx) then false else
      match v, gp with
      | Some (a1, b1), Some (c2, d2) => if Z.leb a1 c2 then true else Z.leb d2 b1
      | _, _ => false
      end
  end.
Lemma L_CXFCL_verdictV : @verdictV = @CXFC.verdictV.
Proof. unfold verdictV. rewrite ?AX2BL.L_AX2BL_gval. reflexivity. Qed.

Fixpoint mk_flV (cg : list positive) (g : gval) (gp : option (Z * Z)) (sxs : list stxr) (vs : list (option (Z * Z))) : flF :=
  match sxs, vs with
  | sx :: rest, v :: vrest =>
      if (if verdictV (fst sx) v g gp then true else verdict_disjR cg (fst sx) g) then mk_flV cg g gp rest vrest
      else (sx, rest) :: mk_flV cg g gp rest vrest
  | _, _ => mk_flF cg g sxs
  end.
Lemma L_CXFCL_mk_flV : @mk_flV = @CXFC.mk_flV.
Proof. unfold mk_flV. rewrite ?L_CXFCL_stxr, ?L_CXFCL_flF, ?L_CXFCL_mk_flF, ?L_CXFCL_verdictV, ?AX2BL.L_AX2BL_gval, ?AX2BL.L_AX2BL_verdict_disjR. reflexivity. Qed.

Definition fl_ok (bc : bctx) (fl : flF) : Prop := Forall (fun p => sx_ok bc (fst p) /\ Forall (sx_ok bc) (snd p)) fl.
Lemma L_CXFCL_fl_ok : @fl_ok = @CXFC.fl_ok.
Proof. unfold fl_ok. rewrite ?L_CXFCL_sx_ok, ?L_CXFCL_flF. reflexivity. Qed.

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
Lemma L_CXFCL_chainKFM : @chainKFM = @CXFC.chainKFM.
Proof. unfold chainKFM. rewrite ?L_CXFCL_memo0, ?L_CXFCL_prune1pcKM, ?L_CXFCL_subj_tail_eqb, ?L_CXFCL_chainK2M, ?L_CXFCL_flF, ?AX2BL.L_AX2BL_chain_slow, ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_kbase. reflexivity. Qed.

Definition gflF : Type := (gval * flF)%type.
Lemma L_CXFCL_gflF : @gflF = @CXFC.gflF.
Proof. unfold gflF. rewrite ?L_CXFCL_flF, ?AX2BL.L_AX2BL_gval. reflexivity. Qed.

Definition mk_glF (bc : bctx) (bnds : gtab) (sxs : list stxr) : ptree gflF := pt_map (fun g => (g, mk_flF (cg_of bc g) g sxs)) bnds.
Lemma L_CXFCL_mk_glF : @mk_glF = @CXFC.mk_glF.
Proof. unfold mk_glF. rewrite ?L_CXFCL_stxr, ?L_CXFCL_mk_flF, ?L_CXFCL_gflF, ?AX2BL.L_AX2BL_cg_of, ?AX2BL.L_AX2BL_gtab, ?AX2BL.L_AX2BL_pt_map. reflexivity. Qed.

Definition mk_glV (bc : bctx) (bnds : gtab) (sxs : list stxr) : ptree gflF :=
  let vs := map vpre sxs in pt_map (fun g => (g, mk_flV (cg_of bc g) g (gpre g) sxs vs)) bnds.
Lemma L_CXFCL_mk_glV : @mk_glV = @CXFC.mk_glV.
Proof. unfold mk_glV. rewrite ?L_CXFCL_stxr, ?L_CXFCL_vpre, ?L_CXFCL_gpre, ?L_CXFCL_mk_flV, ?L_CXFCL_gflF, ?AX2BL.L_AX2BL_cg_of, ?AX2BL.L_AX2BL_gtab, ?AX2BL.L_AX2BL_pt_map. reflexivity. Qed.

Definition is_pure (K : kentry) : bool := match K with KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ => true | _ => false end.
Lemma L_CXFCL_is_pure : @is_pure = @CXFC.is_pure.
Proof. unfold is_pure. reflexivity. Qed.

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
Lemma L_CXFCL_entriesGM : @entriesGM = @CXFC.entriesGM.
Proof. unfold entriesGM. rewrite ?L_CXFCL_memo0, ?L_CXFCL_stxr, ?L_CXFCL_chainK2M, ?L_CXFCL_chainKFM, ?L_CXFCL_gflF, ?L_CXFCL_is_pure, ?AX2BL.L_AX2BL_inb, ?AX2L.L_AX2L_kbase, ?AX2L.L_AX2L_pt_get. reflexivity. Qed.

Fixpoint stores_partM (bc : bctx) (sxs : list stxr) : list kentry :=   
  match sxs with
  | [] => []
  | sxr :: newer => let sx := fst sxr in
      stores_partM bc newer ++ chainK2M bc newer (KWord (sx_a sx) (sx_w sx) (sx_v sx)) (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx) memo0
  end.
Lemma L_CXFCL_stores_partM : @stores_partM = @CXFC.stores_partM.
Proof. unfold stores_partM. rewrite ?L_CXFCL_memo0, ?L_CXFCL_stxr, ?L_CXFCL_chainK2M. reflexivity. Qed.

Definition carryGF (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := mk_stxsF bc log nt_empty in
  let '(r, gs) := scan_entries bc kn t0 gst_empty in
  let '(infos, _) := r in
  stores_partM bc sxs ++ entriesGM bc sxs (mk_glF bc (gs_bnds gs) sxs) kn infos.
Lemma L_CXFCL_carryGF : @carryGF = @CXFC.carryGF.
Proof. unfold carryGF. rewrite ?L_CXFCL_mk_stxsF, ?L_CXFCL_mk_glF, ?L_CXFCL_entriesGM, ?L_CXFCL_stores_partM, ?AX2BL.L_AX2BL_gst_empty, ?AX2BL.L_AX2BL_nt_empty, ?AX2BL.L_AX2BL_scan_entries. reflexivity. Qed.

Definition carryKF (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryGF bc log kn, [], [])
  | _, _ => carryB bc log kn hints
  end.
Lemma L_CXFCL_carryKF : @carryKF = @CXFC.carryKF.
Proof. unfold carryKF. rewrite ?L_CXFCL_carryGF, ?AX2BL.L_AX2BL_carryB. reflexivity. Qed.

Fixpoint mk_stxsFL (bc : bctx) (log : list sentry) (lrs : list (list positive)) (t : ntab) : list stxr * ntab :=
  match log with
  | [] => ([], t)
  | SE a w v :: older =>
      let '(sxs, t1) := mk_stxsFL bc older (match lrs with _ :: r => r | [] => [] end) t in
      let '(r, t2) := intern bc t1 (a_base a) in
      let '(bid, bi) := r in
      let RS := match lrs with RS0 :: _ => if CXNAT.lebF w 8 then RS0 else regs_w bc a w | [] => regs_w bc a w end in
      (sxs ++ [(STX a w v (mk_sprepR bc RS (a_base a) w) bid (bi_br bi) (partners_of (bc_rt bc) RS), (RS, disj_sidesRI (rt_facts (bc_rt bc)) RS))], t2)
  end.
Lemma L_CXFCL_mk_stxsFL : @mk_stxsFL = @CXFC.mk_stxsFL.
Proof. unfold mk_stxsFL. rewrite ?L_CXFCL_disj_sidesRI, ?L_CXFCL_stxr, ?AX2BL.L_AX2BL_intern, ?AX2BL.L_AX2BL_mk_sprepR, ?AX2BL.L_AX2BL_partners_of, ?AX2BL.L_AX2BL_regs_w, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition rsc : Type := option (list positive * (list (saddr * expr) * list iside)).
Lemma L_CXFCL_rsc : @rsc = @CXFC.rsc.
Proof. unfold rsc. rewrite ?L_CXFCL_iside. reflexivity. Qed.

Definition rsc_ok (bc : bctx) (c : rsc) : Prop :=
  match c with Some (RS, v) => v = (disj_sidesR (rt_facts (bc_rt bc)) RS, disj_sidesRI (rt_facts (bc_rt bc)) RS) | None => True end.
Lemma L_CXFCL_rsc_ok : @rsc_ok = @CXFC.rsc_ok.
Proof. unfold rsc_ok. rewrite ?L_CXFCL_disj_sidesRI, ?L_CXFCL_rsc, ?AX2BL.L_AX2BL_disj_sidesR. reflexivity. Qed.

Definition rs_get (bc : bctx) (RS : list positive) (c : rsc) : (list (saddr * expr) * list iside) * rsc :=
  match c with
  | Some (RS', v) =>
      if lp_eqb RS RS' then (v, c)
      else let v' := (disj_sidesR (rt_facts (bc_rt bc)) RS, disj_sidesRI (rt_facts (bc_rt bc)) RS) in (v', Some (RS, v'))
  | None => let v' := (disj_sidesR (rt_facts (bc_rt bc)) RS, disj_sidesRI (rt_facts (bc_rt bc)) RS) in (v', Some (RS, v'))
  end.
Lemma L_CXFCL_rs_get : @rs_get = @CXFC.rs_get.
Proof. unfold rs_get. rewrite ?L_CXFCL_lp_eqb, ?L_CXFCL_iside, ?L_CXFCL_disj_sidesRI, ?L_CXFCL_rsc, ?AX2BL.L_AX2BL_disj_sidesR. reflexivity. Qed.

Fixpoint mk_stxsFC (bc : bctx) (log : list sentry) (lrs : list (list positive)) (t : ntab) : list stxr * ntab * rsc :=
  match log with
  | [] => ([], t, None)
  | SE a w v :: older =>
      let '(sxs, t1, c1) := mk_stxsFC bc older (match lrs with _ :: r => r | [] => [] end) t in
      let '(r, t2) := intern bc t1 (a_base a) in
      let '(bid, bi) := r in
      let RS := match lrs with RS0 :: _ => if CXNAT.lebF w 8 then RS0 else regs_w bc a w | [] => regs_w bc a w end in
      let '(DD, c2) := rs_get bc RS c1 in
      (sxs ++ [(STX a w v (SPrep (base_rangeB bc (a_base a)) (xhiB bc (elen w)) (fst DD) (fst DD)) bid (bi_br bi) (partners_of (bc_rt bc) RS), (RS, snd DD))], t2, c2)
  end.
Lemma L_CXFCL_mk_stxsFC : @mk_stxsFC = @CXFC.mk_stxsFC.
Proof. unfold mk_stxsFC. rewrite ?L_CXFCL_stxr, ?L_CXFCL_rsc, ?L_CXFCL_rs_get, ?AX2BL.L_AX2BL_base_rangeB, ?AX2L.L_AX2L_elen, ?AX2BL.L_AX2BL_intern, ?AX2BL.L_AX2BL_partners_of, ?AX2BL.L_AX2BL_regs_w, ?AX2BL.L_AX2BL_xhiB, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition carryGFL (bc : bctx) (log : list sentry) (lrs : list (list positive)) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := fst (mk_stxsFC bc log lrs nt_empty) in
  let '(r, gs) := scan_entries bc kn t0 gst_empty in
  let '(infos, _) := r in
  stores_partM bc sxs ++ entriesGM bc sxs (mk_glV bc (gs_bnds gs) sxs) kn infos.
Lemma L_CXFCL_carryGFL : @carryGFL = @CXFC.carryGFL.
Proof. unfold carryGFL. rewrite ?L_CXFCL_mk_glV, ?L_CXFCL_entriesGM, ?L_CXFCL_stores_partM, ?L_CXFCL_mk_stxsFC, ?AX2BL.L_AX2BL_gst_empty, ?AX2BL.L_AX2BL_nt_empty, ?AX2BL.L_AX2BL_scan_entries. reflexivity. Qed.

Definition carryKFL (bc : bctx) (log : list sentry) (lrs : list (list positive)) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryGFL bc log lrs kn, [], [])
  | _, _ => carryB bc log kn hints
  end.
Lemma L_CXFCL_carryKFL : @carryKFL = @CXFC.carryKFL.
Proof. unfold carryKFL. rewrite ?L_CXFCL_carryGFL, ?AX2BL.L_AX2BL_carryB. reflexivity. Qed.

End CXFCL.
