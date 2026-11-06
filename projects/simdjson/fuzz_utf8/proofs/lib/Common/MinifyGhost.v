(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import SlotProp MallocNodes2.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP.
Open Scope Z_scope.

Module MG.
Definition QS_ID : nat := 70.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fp_qs (args : list expr) : list (expr * expr) :=
  match args with [tbl; b; i; _; _] => [(b, i); (tbl, ELit 768)] | _ => [(ELit 0, ELit 0)] end.

(* [comment removed for export] *)
Definition vals_of (kn : list kentry) (e : expr) : option (list Z) :=
  match e with
  | ELit z => let v := z mod two64 in if (Z.leb 0 v && Z.leb v 255)%bool then Some [v] else None
  | _ => match xlo kn e, xhi kn e with
         | Some lo, Some hi => if (Z.leb 0 lo && Z.leb hi 255 && Z.leb lo hi)%bool then Some (map (fun k => lo + Z.of_nat k) (seq 0 (Z.to_nat (hi - lo + 1)))) else None
         | _, _ => None
         end
  end.
(* [comment removed for export] *)
Definition var_of (e : expr) : option nat := match e with EVar v => Some v | _ => None end.
Definition okvar (vs : list nat) (x : nat) : bool := existsb (Nat.eqb x) vs.
Definition pins (l : list (option nat * Z)) : list nat :=
  flat_map (fun pz : option nat * Z => match fst pz with Some x => [x] | None => [] end) l.

(* [comment removed for export] *)
Fixpoint eclosed (vs : list nat) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar v => okvar vs v
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => eclosed vs a && eclosed vs b
  | EExt _ _ _ a => eclosed vs a
  | EBlob _ _ _ _ => false
  end%bool.
Fixpoint distinctb (l : list nat) : bool :=
  match l with [] => true | x :: r => negb (existsb (Nat.eqb x) r) && distinctb r end%bool.
Definition eupdz (E : env) (v : nat) (z : Z) : env := Env (fun x => if Nat.eqb x v then Z_to_bv 64 z else ev E x) (eb E).
Fixpoint eupds (E : env) (l : list (option nat * Z)) : env :=
  match l with [] => E | (Some v, z) :: r => eupds (eupdz E v z) r | (None, _) :: r => eupds E r end.
Definition E00 : env := Env (fun _ => Z_to_bv 64 0) (fun _ => []).

(* [comment removed for export] *)
Definition qstep_v (w u m0 m1 : Z) : Z * Z := (Z.lxor (Z.land u m0) w, Z.lor (Z.lxor u 255) m1).

(* [comment removed for export] *)
Definition step_case (wv uv : nat) (p0 p1 : option nat) (w' u' : expr) (zw zu z0 z1 : Z) : bool :=
  let E := eupds E00 [(Some wv, zw); (Some uv, zu); (p0, z0); (p1, z1)] in
  let (mw, mu) := qstep_v zw zu z0 z1 in
  (Z.eqb (bv_unsigned (edenot E w')) mw && Z.eqb (bv_unsigned (edenot E u')) mu)%bool.

Definition allz (l : list Z) (f : Z -> bool) : bool := forallb f l.

(* [comment removed for export] *)
Definition addr_is (kn : list kentry) (a : saddr) (e : xterms) : bool :=
  lin_ge0 kn [(a_base a, a_off a)] e && lin_ge0 kn e [(a_base a, a_off a)].
(* [comment removed for export] *)
Fixpoint find_rec (kn allkn : list kentry) (e : xterms) (w : nat) : option expr :=
  match kn with
  | [] => None
  | KWord a w' v :: rest => if (Nat.eqb w' w && addr_is allkn a e)%bool then Some v else find_rec rest allkn e w
  | _ :: rest => find_rec rest allkn e w
  end.
(* [comment removed for export] *)
Definition find_rec1 (kn : list kentry) (e : xterms) : option expr := find_rec kn kn e 1%nat.

(* [comment removed for export] *)
Definition byte_of (v : expr) : expr := EExt false 0 1 v.

(* [comment removed for export] *)
Definition step_with (kn : list kentry) (tbl b i w' u' : expr) (h : gatom) : bool :=
  if negb (Nat.eqb (g_id h) QS_ID) then false else
  match g_args h with
  | [tbl0; b0; i0; w0; u0] =>
      match var_of w0, var_of u0 with
      | Some wv, Some uv =>
      if negb (expr_eqb tbl tbl0 && expr_eqb b b0)%bool then false else
      if negb (lin_ge0 kn [(i, 0)] [(i0, 1)] && lin_ge0 kn [(i0, 1)] [(i, 0)])%bool then false else
      match find_rec1 kn [(b, 0); (i0, 0)] with
      | None => false
      | Some cv =>
          let c := byte_of cv in
          match find_rec1 kn [(c, 0); (c, 0); (c, 0); (tbl, 0)], find_rec1 kn [(c, 0); (c, 0); (c, 0); (tbl, 1)] with
          | Some r0, Some r1 =>
              match vals_of kn (EVar wv), vals_of kn (EVar uv), vals_of kn r0, vals_of kn r1 with
              | Some ws, Some us, Some m0s, Some m1s =>
                  let p0 := var_of r0 in let p1 := var_of r1 in
                  let vs := pins [(Some wv, 0); (Some uv, 0); (p0, 0); (p1, 0)] in
                  if negb (match r0 with ELit _ | EVar _ => true | _ => false end && match r1 with ELit _ | EVar _ => true | _ => false end)%bool then false else
                  if negb (eclosed vs w' && eclosed vs u')%bool then false else
                  (* [comment removed for export] *)
                  if negb (distinctb vs) then false else
                  allz ws (fun zw => allz us (fun zu => allz m0s (fun z0 => allz m1s (fun z1 => step_case wv uv p0 p1 w' u' zw zu z0 z1))))
              | _, _, _, _ => false
              end
          | _, _ => false
          end
      end
      | _, _ => false
      end
  | _ => false
  end.

(* [comment removed for export] *)
Definition is_val (kn : list kentry) (e : expr) (z : Z) : bool :=
  match xlo kn e, xhi kn e with Some lo, Some hi => (Z.eqb lo z && Z.eqb hi z)%bool | _, _ => false end.
Definition init_ok (kn : list kentry) (tbl b i w u : expr) : bool :=
  (match tbl with ELit t => (Z.leb 0 t && Z.ltb (t + 768) two64)%bool | _ => false end
   && is_val kn i 0 && is_val kn w 0 && is_val kn u 1)%bool.

(* [comment removed for export] *)
Fixpoint ereplace (x y e : expr) : expr :=
  if expr_eqb e x then y else
  match e with
  | EAlu op a c => EAlu op (ereplace x y a) (ereplace x y c)
  | EAluw op a c => EAluw op (ereplace x y a) (ereplace x y c)
  | EMd op a c => EMd op (ereplace x y a) (ereplace x y c)
  | EMdw op a c => EMdw op (ereplace x y a) (ereplace x y c)
  | EExt sx lo n a => EExt sx lo n (ereplace x y a)
  | _ => e
  end.
Definition fun_pair (kn : list kentry) (a1 a2 : expr) (h1 h2 : gatom) : bool :=
  if negb (Nat.eqb (g_id h1) QS_ID && Nat.eqb (g_id h2) QS_ID)%bool then false else
  match g_args h1, g_args h2 with
  | [tbl1; b1; i1; w1; u1], [tbl2; b2; i2; w2; u2] =>
      (expr_eqb tbl1 tbl2 && expr_eqb b1 b2 && lin_ge0 kn [(i1, 0)] [(i2, 0)] && lin_ge0 kn [(i2, 0)] [(i1, 0)]
       && expr_eqb (ereplace w1 w2 a1) a2)%bool
  | _, _ => false
  end.
Definition fun_ok (kn : list kentry) (hyps : list gatom) (a1 a2 : expr) : bool :=
  existsb (fun h1 => existsb (fun h2 => fun_pair kn a1 a2 h1 h2) hyps) hyps.

Definition qs_vcok (v : vc) : bool :=
  match vc_concl v with
  | VCAtom g =>
      if negb (Nat.eqb (g_id g) QS_ID) then false else
      match g_args g with
      | [tbl; b; i; w; u] => (init_ok (vc_kn v) tbl b i w u || existsb (step_with (vc_kn v) tbl b i w u) (vc_hyps v))%bool
      | _ => false
      end
  | VCFact (KRange (EAlu ALU_SUB a1 a2) 0 0) => fun_ok (vc_kn v) (vc_hyps v) a1 a2
  | _ => false
  end.

(* [comment removed for export] *)
Definition vals_ofB (bc : AX2B.bctx) (e : expr) : option (list Z) :=
  match e with
  | ELit z => let v := z mod two64 in if (Z.leb 0 v && Z.leb v 255)%bool then Some [v] else None
  | _ => match AX2B.xloB bc e, AX2B.xhiB bc e with
         | Some lo, Some hi => if (Z.leb 0 lo && Z.leb hi 255 && Z.leb lo hi)%bool then Some (map (fun k => lo + Z.of_nat k) (seq 0 (Z.to_nat (hi - lo + 1)))) else None
         | _, _ => None
         end
  end.
Lemma vals_ofB_eqf : forall k, vals_ofB (AX2B.mkbc k) = vals_of k.
Proof. intros. apply functional_extensionality; intros e. unfold vals_ofB, vals_of. rewrite AX2B.xloB_eqf, AX2B.xhiB_eqf. reflexivity. Qed.
Definition addr_isB (bc : AX2B.bctx) (a : saddr) (e : xterms) : bool :=
  if AX2B.lin_ge0B bc [(a_base a, a_off a)] e then AX2B.lin_ge0B bc e [(a_base a, a_off a)] else false.
Lemma addr_isB_eqf : forall k, addr_isB (AX2B.mkbc k) = addr_is k.
Proof.
  intros. apply functional_extensionality; intros a. apply functional_extensionality; intros e.
  unfold addr_isB, addr_is. rewrite AX2B.lin_ge0B_eqf. destruct (lin_ge0 k _ _); reflexivity.
Qed.
Fixpoint find_recB (bc : AX2B.bctx) (kn : list kentry) (e : xterms) (w : nat) : option expr :=
  match kn with
  | [] => None
  | KWord a w' v :: rest => if Nat.eqb w' w then (if addr_isB bc a e then Some v else find_recB bc rest e w) else find_recB bc rest e w
  | _ :: rest => find_recB bc rest e w
  end.
Lemma find_recB_eqf : forall k kn e w, find_recB (AX2B.mkbc k) kn e w = find_rec kn k e w.
Proof.
  intros k kn e w. induction kn as [|K rest IH]; [reflexivity|]. cbn [find_recB find_rec]. rewrite IH, addr_isB_eqf.
  destruct K; try reflexivity. destruct (Nat.eqb _ w); [cbn [andb]|reflexivity]. reflexivity.
Qed.
Definition find_rec1B (bc : AX2B.bctx) (kn : list kentry) (e : xterms) : option expr := find_recB bc kn e 1%nat.
Lemma find_rec1B_eqf : forall k, find_rec1B (AX2B.mkbc k) k = find_rec1 k.
Proof. intros. apply functional_extensionality; intros e. unfold find_rec1B, find_rec1. apply find_recB_eqf. Qed.
Definition step_withB (bc : AX2B.bctx) (kn : list kentry) (tbl b i w' u' : expr) (h : gatom) : bool :=
  if negb (Nat.eqb (g_id h) QS_ID) then false else
  match g_args h with
  | [tbl0; b0; i0; w0; u0] =>
      match var_of w0, var_of u0 with
      | Some wv, Some uv =>
      if negb (expr_eqb tbl tbl0 && expr_eqb b b0)%bool then false else
      if negb (if AX2B.lin_ge0B bc [(i, 0)] [(i0, 1)] then AX2B.lin_ge0B bc [(i0, 1)] [(i, 0)] else false) then false else
      match find_rec1B bc kn [(b, 0); (i0, 0)] with
      | None => false
      | Some cv =>
          let c := byte_of cv in
          match find_rec1B bc kn [(c, 0); (c, 0); (c, 0); (tbl, 0)], find_rec1B bc kn [(c, 0); (c, 0); (c, 0); (tbl, 1)] with
          | Some r0, Some r1 =>
              match vals_ofB bc (EVar wv), vals_ofB bc (EVar uv), vals_ofB bc r0, vals_ofB bc r1 with
              | Some ws, Some us, Some m0s, Some m1s =>
                  let p0 := var_of r0 in let p1 := var_of r1 in
                  let vs := pins [(Some wv, 0); (Some uv, 0); (p0, 0); (p1, 0)] in
                  if negb (match r0 with ELit _ | EVar _ => true | _ => false end && match r1 with ELit _ | EVar _ => true | _ => false end)%bool then false else
                  if negb (eclosed vs w' && eclosed vs u')%bool then false else
                  if negb (distinctb vs) then false else
                  allz ws (fun zw => allz us (fun zu => allz m0s (fun z0 => allz m1s (fun z1 => step_case wv uv p0 p1 w' u' zw zu z0 z1))))
              | _, _, _, _ => false
              end
          | _, _ => false
          end
      end
      | _, _ => false
      end
  | _ => false
  end.
Lemma step_withB_eqf : forall k, step_withB (AX2B.mkbc k) k = step_with k.
Proof.
  intros. repeat (apply functional_extensionality; intros ?). unfold step_withB, step_with.
  rewrite find_rec1B_eqf, vals_ofB_eqf, AX2B.lin_ge0B_eqf. reflexivity.
Qed.
Definition is_valB (bc : AX2B.bctx) (e : expr) (z : Z) : bool :=
  match AX2B.xloB bc e, AX2B.xhiB bc e with Some lo, Some hi => (Z.eqb lo z && Z.eqb hi z)%bool | _, _ => false end.
Definition init_okB (bc : AX2B.bctx) (tbl b i w u : expr) : bool :=
  (match tbl with ELit t => (Z.leb 0 t && Z.ltb (t + 768) two64)%bool | _ => false end
   && is_valB bc i 0 && is_valB bc w 0 && is_valB bc u 1)%bool.
Lemma init_okB_eqf : forall k, init_okB (AX2B.mkbc k) = init_ok k.
Proof.
  intros. repeat (apply functional_extensionality; intros ?). unfold init_okB, init_ok, is_valB, is_val.
  rewrite AX2B.xloB_eqf, AX2B.xhiB_eqf. reflexivity.
Qed.
Definition fun_pairB (bc : AX2B.bctx) (a1 a2 : expr) (h1 h2 : gatom) : bool :=
  if negb (Nat.eqb (g_id h1) QS_ID && Nat.eqb (g_id h2) QS_ID)%bool then false else
  match g_args h1, g_args h2 with
  | [tbl1; b1; i1; w1; u1], [tbl2; b2; i2; w2; u2] =>
      if (expr_eqb tbl1 tbl2 && expr_eqb b1 b2)%bool then
        if AX2B.lin_ge0B bc [(i1, 0)] [(i2, 0)] then
          if AX2B.lin_ge0B bc [(i2, 0)] [(i1, 0)] then expr_eqb (ereplace w1 w2 a1) a2 else false
        else false
      else false
  | _, _ => false
  end.
Lemma fun_pairB_eqf : forall k, fun_pairB (AX2B.mkbc k) = fun_pair k.
Proof.
  intros. repeat (apply functional_extensionality; intros ?). unfold fun_pairB, fun_pair. rewrite AX2B.lin_ge0B_eqf.
  destruct (negb _); [reflexivity|].
  repeat match goal with |- context [match g_args ?h with _ => _ end] => destruct (g_args h) as [|? [|? [|? [|? [|? [|? ?]]]]]]; try reflexivity end.
  destruct (expr_eqb _ _), (expr_eqb _ _), (lin_ge0 k _ _), (lin_ge0 k _ _); reflexivity.
Qed.
Definition fun_okB (bc : AX2B.bctx) (hyps : list gatom) (a1 a2 : expr) : bool :=
  existsb (fun h1 => existsb (fun h2 => fun_pairB bc a1 a2 h1 h2) hyps) hyps.
Lemma fun_okB_eqf : forall k, fun_okB (AX2B.mkbc k) = fun_ok k.
Proof. intros. repeat (apply functional_extensionality; intros ?). unfold fun_okB, fun_ok. rewrite fun_pairB_eqf. reflexivity. Qed.
Definition qs_vcokM (v : vc) : bool :=
  let k := vc_kn v in let bc := AX2B.mkbc k in
  match vc_concl v with
  | VCAtom g =>
      if negb (Nat.eqb (g_id g) QS_ID) then false else
      match g_args g with
      | [tbl; b; i; w; u] => if init_okB bc tbl b i w u then true else existsb (step_withB bc k tbl b i w u) (vc_hyps v)
      | _ => false
      end
  | VCFact (KRange (EAlu ALU_SUB a1 a2) 0 0) => fun_okB bc (vc_hyps v) a1 a2
  | _ => false
  end.
Lemma qs_vcokM_eq : forall v, qs_vcokM v = qs_vcok v.
Proof.
  intros v. unfold qs_vcokM, qs_vcok. cbv zeta. rewrite init_okB_eqf, step_withB_eqf, fun_okB_eqf. reflexivity.
Qed.
Lemma qs_vcokM_eqf : qs_vcokM = qs_vcok.
Proof. apply functional_extensionality. apply qs_vcokM_eq. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithSegs.
Context {fx : FPState}.
Variable SEGS : list Segment.
Definition mem : Type := word -> option byte.

Definition rdZ (M : mem) (a : Z) (n : nat) : option Z :=
  match rdn SEGS M (Z_to_bv 64 a) n with Some bs => Some (bytes_le_to_Z bs) | None => None end.
Definition tb (M : mem) (tbl c k : Z) : Z :=
  match rdZ M (tbl + 3 * c + k) 1 with Some v => v | None => 0 end.
Definition qstep (M : mem) (tbl : Z) (wu : Z * Z) (c : Z) : Z * Z :=
  qstep_v (fst wu) (snd wu) (tb M tbl c 0) (tb M tbl c 1).
Definition qfold (M : mem) (tbl : Z) (cs : list Z) (wu : Z * Z) : Z * Z := fold_left (qstep M tbl) cs wu.

Definition p_qs (vs : list Z) (M : mem) : Prop :=
  match vs with
  | [tbl; b; i; w; u] =>
      0 <= b /\ 0 <= i /\ b + i <= two64 /\ 0 <= tbl /\ tbl + 768 < two64 /\
      exists bs, rdn SEGS M (Z_to_bv 64 b) (Z.to_nat i) = Some bs /\ qfold M tbl (map bv_unsigned bs) (0, 1) = (w, u)
  | _ => False
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition uD (E : env) (e : expr) : Z := bv_unsigned (edenot E e).

Lemma okvar_In : forall vs x, okvar vs x = true -> In x vs.
Proof. intros vs x H. unfold okvar in H. apply existsb_exists in H as [y [Hin Heq]]. apply Nat.eqb_eq in Heq. subst. exact Hin. Qed.

Lemma edenot_eclosed : forall vs E E' e,
  eclosed vs e = true -> (forall v, In v vs -> ev E v = ev E' v) -> edenot E e = edenot E' e.
Proof.
  intros vs E E' e. induction e; cbn [eclosed edenot]; intros H HA.
  - reflexivity.
  - apply HA. apply okvar_In. exact H.
  - apply andb_prop in H as [H1 H2]. rewrite (IHe1 H1 HA), (IHe2 H2 HA). reflexivity.
  - apply andb_prop in H as [H1 H2]. rewrite (IHe1 H1 HA), (IHe2 H2 HA). reflexivity.
  - apply andb_prop in H as [H1 H2]. rewrite (IHe1 H1 HA), (IHe2 H2 HA). reflexivity.
  - apply andb_prop in H as [H1 H2]. rewrite (IHe1 H1 HA), (IHe2 H2 HA). reflexivity.
  - rewrite (IHe H HA). reflexivity.
  - discriminate H.
Qed.

Lemma distinctb_sound : forall l, distinctb l = true -> List.NoDup l.
Proof.
  induction l as [|x r IH]; cbn [distinctb]; intros H; [constructor|].
  apply andb_prop in H as [H1 H2]. constructor; [|exact (IH H2)].
  intros Hin. assert (X : existsb (Nat.eqb x) r = true) by (apply existsb_exists; exists x; split; [exact Hin | apply Nat.eqb_refl]).
  rewrite X in H1. discriminate H1.
Qed.

Lemma ereplace_denot : forall E x y e, edenot E x = edenot E y -> edenot E (ereplace x y e) = edenot E e.
Proof.
  intros E x y e Hxy. induction e; cbn [ereplace];
    (destruct (expr_eqb _ x) eqn:Q; [apply expr_eqb_eq in Q; rewrite Q, <- Hxy; reflexivity|]); cbn [edenot];
    try reflexivity; try (rewrite IHe1, IHe2; reflexivity); try (rewrite IHe; reflexivity).
Qed.


Lemma ev_eupdz : forall E v z x, ev (eupdz E v z) x = if Nat.eqb x v then Z_to_bv 64 z else ev E x.
Proof. reflexivity. Qed.
Lemma eb_eupdz : forall E v z, eb (eupdz E v z) = eb E.
Proof. reflexivity. Qed.
Lemma eb_eupds : forall l E, eb (eupds E l) = eb E.
Proof. induction l as [|[[v|] z] r IH]; intros E; cbn [eupds]; [reflexivity | rewrite IH; reflexivity | apply IH]. Qed.

Lemma allz_true : forall l f z, allz l f = true -> In z l -> f z = true.
Proof. intros l f z H Hin. unfold allz in H. exact (proj1 (forallb_forall _ _) H z Hin). Qed.

Lemma In_range : forall lo n z, lo <= z < lo + Z.of_nat n -> In z (map (fun k => lo + Z.of_nat k) (seq 0 n)).
Proof.
  intros lo n z Hz. apply in_map_iff. exists (Z.to_nat (z - lo)). split; [lia|]. apply in_seq. lia.
Qed.

Lemma vals_of_sound : forall E M kn e l, know_ok SEGS E M kn -> vals_of kn e = Some l -> In (uD E e) l.
Proof.
  intros E M kn e l Hkn H. unfold vals_of in H.
  assert (GEN : match xlo kn e, xhi kn e with
                | Some lo, Some hi => if (Z.leb 0 lo && Z.leb hi 255 && Z.leb lo hi)%bool then Some (map (fun k => lo + Z.of_nat k) (seq 0 (Z.to_nat (hi - lo + 1)))) else None
                | _, _ => None end = Some l -> In (uD E e) l).
  { clear H. intros H. destruct (xlo kn e) as [lo|] eqn:Hl; [|discriminate]. destruct (xhi kn e) as [hi|] eqn:Hh; [|discriminate].
    destruct (Z.leb 0 lo && Z.leb hi 255 && Z.leb lo hi)%bool eqn:Hb; [|discriminate]. injection H as <-.
    pose proof (xlo_sound SEGS E M kn e lo Hkn Hl) as L. pose proof (xhi_sound SEGS E M kn e hi Hkn Hh) as R.
    unfold uD. apply In_range. rewrite Z2Nat.id by lia. lia. }
  destruct e; try exact (GEN H). cbn zeta in H. destruct (Z.leb 0 (z mod two64) && Z.leb (z mod two64) 255)%bool; [|discriminate].
  injection H as <-. unfold uD. cbn [edenot]. rewrite u_lit64. left. reflexivity.
Qed.


Lemma vals_of_bounded : forall kn e l z, vals_of kn e = Some l -> In z l -> 0 <= z <= 255.
Proof.
  intros kn e l z H Hin. unfold vals_of in H.
  assert (GEN : forall lo hi, (Z.leb 0 lo && Z.leb hi 255 && Z.leb lo hi)%bool = true ->
            In z (map (fun k => lo + Z.of_nat k) (seq 0 (Z.to_nat (hi - lo + 1)))) -> 0 <= z <= 255).
  { intros lo hi Hb Hz. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
    apply in_map_iff in Hz as [k [<- Hk]]. apply in_seq in Hk. lia. }
  destruct e;
    try (destruct (xlo kn _) as [lo'|]; [|discriminate]; destruct (xhi kn _) as [hi'|]; [|discriminate];
         destruct (Z.leb 0 lo' && Z.leb hi' 255 && Z.leb lo' hi')%bool eqn:Hb; [|discriminate]; injection H as <-; exact (GEN lo' hi' Hb Hin)).
  cbn zeta in H. destruct (Z.leb 0 (z0 mod two64) && Z.leb (z0 mod two64) 255)%bool eqn:Hb; [|discriminate].
  injection H as <-. destruct Hin as [<-|[]]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* [comment removed for export] *)
Lemma addr_is_sound : forall E M kn a e, know_ok SEGS E M kn -> addr_is kn a e = true -> estart E a = xt_den E e.
Proof.
  intros E M kn a e Hkn H. unfold addr_is in H. apply andb_prop in H as [H1 H2].
  pose proof (lin_ge0_sound SEGS E M kn _ _ Hkn H1) as A. pose proof (lin_ge0_sound SEGS E M kn _ _ Hkn H2) as B.
  cbn [xt_den] in A, B. unfold estart. lia.
Qed.

Lemma find_rec_sound : forall E M allkn kn e w v, know_ok SEGS E M allkn -> know_ok SEGS E M kn ->
  find_rec kn allkn e w = Some v ->
  (w <= 8)%nat /\ 0 <= xt_den E e /\ xt_den E e + Z.of_nat w <= 2 ^ 64 /\
  rdn SEGS M (Z_to_bv 64 (xt_den E e)) w = Some (word_to_le_bytes w (edenot E v)).
Proof.
  intros E M allkn kn e w v Hall Hkn. induction kn as [|K rest IH]; cbn [find_rec]; intros H; [discriminate|].
  apply Forall_cons_iff in Hkn as [HK Hrest].
  destruct K as [a w' v'| | | | | | | | |]; try exact (IH Hrest H).
  destruct (Nat.eqb w' w && addr_is allkn a e)%bool eqn:Hb; [|exact (IH Hrest H)].
  injection H as <-. apply andb_prop in Hb as [Hw Ha]. apply Nat.eqb_eq in Hw. subst w'.
  cbn [kentry_ok] in HK. destruct HK as (Hw8 & Hfl & Hrd).
  pose proof (addr_is_sound E M allkn a e Hall Ha) as He. pose proof (flat_u E a _ Hfl) as Hu.
  destruct Hfl as (F1 & F2 & F3 & F4).
  split; [exact Hw8|]. split; [lia|]. split; [lia|].
  rewrite <- He. replace (Z_to_bv 64 (estart E a)) with (adenot E a); [exact Hrd|].
  apply bv_eq. rewrite Hu, Z_to_bv_unsigned. symmetry. apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. lia.
Qed.

Lemma rdZ_of_rec : forall E M allkn kn e w v, know_ok SEGS E M allkn -> know_ok SEGS E M kn ->
  find_rec kn allkn e w = Some v -> rdZ M (xt_den E e) w = Some (bv_unsigned (edenot E v) mod 2 ^ (8 * Z.of_nat w)).
Proof.
  intros E M allkn kn e w v Hall Hkn H. destruct (find_rec_sound E M allkn kn e w v Hall Hkn H) as (_ & _ & _ & Hr).
  unfold rdZ. rewrite Hr, bytes_le_N. reflexivity.
Qed.

Lemma u_ext1 : forall E v, bv_unsigned (edenot E (EExt false 0 1 v)) = bv_unsigned (edenot E v) mod 2 ^ 8.
Proof.
  intros E v. cbn [edenot]. unfold ext_val, ext_Z. cbn [Z.of_nat Z.mul Z.pow_pos Pos.mul]. rewrite Z.div_1_r, u_lit64a.
  pose proof (u64_range (edenot E v)) as Hr.
  apply Z.mod_small. pose proof (Z.mod_pos_bound (bv_unsigned (edenot E v)) (2 ^ 8) ltac:(lia)). lia.
Qed.

Lemma rdn_app : forall M (a : word) n m bs cs,
  rdn SEGS M a n = Some bs -> rdn SEGS M (a + nat_to_word n) m = Some cs -> rdn SEGS M a (n + m) = Some (bs ++ cs).
Proof.
  intros M a n. revert a. induction n as [|n IH]; intros a m bs cs Hb Hc.
  - cbn [rdn] in Hb. injection Hb as <-. rewrite word_add_0 in Hc. cbn [Nat.add app]. exact Hc.
  - cbn [rdn] in Hb. cbn [Nat.add rdn].
    destruct (match M a with Some b => Some b | None => seg_rom SEGS a end) as [b|]; [|discriminate].
    destruct (rdn SEGS M (a + 1)%bv n) as [rest|] eqn:Hr; [|discriminate]. injection Hb as <-.
    replace (a + nat_to_word (S n))%bv with (a + 1 + nat_to_word n)%bv in Hc
      by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
    rewrite (IH _ m rest cs Hr Hc). reflexivity.
Qed.

Lemma u_byte_of : forall E v, uD E (byte_of v) = uD E v mod 256.
Proof. intros E v. unfold byte_of, uD. rewrite u_ext1. reflexivity. Qed.

Lemma find_rec1_sound : forall E M kn e v, know_ok SEGS E M kn -> find_rec1 kn e = Some v ->
  0 <= xt_den E e /\ xt_den E e + 1 <= 2 ^ 64 /\
  rdn SEGS M (Z_to_bv 64 (xt_den E e)) 1 = Some [Z_to_bv 8 (uD E v)].
Proof.
  intros E M kn e v Hkn H. unfold find_rec1 in H.
  destruct (find_rec_sound E M kn kn e 1 v Hkn Hkn H) as (_ & H1 & H2 & H3).
  split; [exact H1|]. split; [cbn [Z.of_nat] in H2; lia|]. rewrite H3. reflexivity.
Qed.

Lemma tb_of_rec : forall E M kn cb tbl k r, know_ok SEGS E M kn ->
  find_rec1 kn [(cb, 0); (cb, 0); (cb, 0); (tbl, k)] = Some r -> tb M (uD E tbl) (uD E cb) k = uD E r mod 256.
Proof.
  intros E M kn cb tbl k r Hkn H. unfold find_rec1 in H.
  pose proof (rdZ_of_rec E M kn kn _ 1 r Hkn Hkn H) as R. cbn [xt_den fst snd Z.of_nat Z.mul] in R.
  unfold tb. unfold uD. replace (bv_unsigned (edenot E tbl) + 3 * bv_unsigned (edenot E cb) + k)
    with (bv_unsigned (edenot E cb) + 0 + (bv_unsigned (edenot E cb) + 0 + (bv_unsigned (edenot E cb) + 0 + (bv_unsigned (edenot E tbl) + k + 0)))) by lia.
  rewrite R. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma eupds_other : forall l E x, (forall p z, In (p, z) l -> p <> Some x) -> ev (eupds E l) x = ev E x.
Proof.
  induction l as [|[[v|] z] r IH]; intros E x H; cbn [eupds]; [reflexivity| |].
  - rewrite IH; [|intros p z' Hin; exact (H p z' (or_intror Hin))]. rewrite ev_eupdz.
    destruct (Nat.eqb_spec x v) as [->|]; [|reflexivity]. exfalso. exact (H (Some v) z (or_introl eq_refl) eq_refl).
  - apply IH. intros p z' Hin. exact (H p z' (or_intror Hin)).
Qed.

Lemma eupds_pin : forall l E x z, List.NoDup (pins l) -> In (Some x, z) l -> ev (eupds E l) x = Z_to_bv 64 z.
Proof.
  induction l as [|[p z'] r IH]; intros E x z Hnd Hin; [destruct Hin|].
  destruct p as [v|].
  - cbn [pins flat_map fst app] in Hnd. apply List.NoDup_cons_iff in Hnd as [Hv Hnd].
    destruct Hin as [Heq|Hin].
    + injection Heq as -> ->. cbn [eupds]. rewrite eupds_other.
      * rewrite ev_eupdz, Nat.eqb_refl. reflexivity.
      * intros p z2 Hp ->. apply Hv. unfold pins. apply in_flat_map. exists (Some x, z2). split; [exact Hp | left; reflexivity].
    + cbn [eupds]. apply IH; [exact Hnd | exact Hin].
  - cbn [pins flat_map fst app] in Hnd. destruct Hin as [Heq|Hin]; [discriminate|]. cbn [eupds]. apply IH; [exact Hnd | exact Hin].
Qed.

Lemma pins_in : forall l v, In v (pins l) -> exists z, In (Some v, z) l.
Proof.
  intros l v H. unfold pins in H. apply in_flat_map in H as [[p z] [Hin Hv]]. cbn [fst] in Hv.
  destruct p as [x|]; [|destruct Hv]. destruct Hv as [<-|[]]. exists z. exact Hin.
Qed.

(* [comment removed for export] *)
Definition Lenv (E : env) (wv uv : nat) (r0 r1 : expr) : list (option nat * Z) :=
  [(Some wv, uD E (EVar wv)); (Some uv, uD E (EVar uv)); (var_of r0, uD E r0); (var_of r1, uD E r1)].

Lemma Lenv_val : forall E wv uv r0 r1 v z, In (Some v, z) (Lenv E wv uv r0 r1) -> Z_to_bv 64 z = ev E v.
Proof.
  intros E wv uv r0 r1 v z Hin.
  assert (SELF : forall x, Z_to_bv 64 (uD E (EVar x)) = ev E x) by (intros; unfold uD; cbn [edenot]; apply Z_to_bv_bv_unsigned).
  unfold Lenv in Hin. destruct Hin as [H|[H|[H|[H|[]]]]].
  - injection H as -> <-. apply SELF.
  - injection H as -> <-. apply SELF.
  - destruct r0; cbn [var_of] in H; try discriminate. injection H as -> <-. apply SELF.
  - destruct r1; cbn [var_of] in H; try discriminate. injection H as -> <-. apply SELF.
Qed.

Lemma step_env_agree : forall E wv uv r0 r1,
  distinctb (pins (Lenv E wv uv r0 r1)) = true ->
  forall v, In v (pins (Lenv E wv uv r0 r1)) -> ev E v = ev (eupds E00 (Lenv E wv uv r0 r1)) v.
Proof.
  intros E wv uv r0 r1 Hd v Hin. apply distinctb_sound in Hd.
  destruct (pins_in _ _ Hin) as [z Hz]. rewrite (eupds_pin _ E00 v z Hd Hz). symmetry. exact (Lenv_val E wv uv r0 r1 v z Hz).
Qed.



(* [comment removed for export] *)
Definition agree_on (M M' : mem) (a : Z) (n : Z) : Prop :=
  forall x : word, a <= bv_unsigned x < a + n -> M' x = M x.
Lemma rdn_frame : forall M M' a n, 0 <= a -> a + Z.of_nat n <= two64 -> agree_on M M' a (Z.of_nat n) ->
  rdn SEGS M' (Z_to_bv 64 a) n = rdn SEGS M (Z_to_bv 64 a) n.
Proof.
  intros M M' a n Ha Hn Hag. unfold two64 in Hn. destruct n as [|n']; [reflexivity|].
  assert (Hu : bv_unsigned (Z_to_bv 64 a) = a).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. lia. }
  apply rdn_ext; [rewrite Hu; lia|]. intros x Hx. apply Hag. rewrite Hu in Hx. lia.
Qed.
Lemma tb_frame : forall M M' tbl c k, 0 <= tbl -> tbl + 768 < two64 -> 0 <= c <= 255 -> 0 <= k <= 2 ->
  agree_on M M' tbl 768 -> tb M' tbl c k = tb M tbl c k.
Proof.
  intros M M' tbl c k Ht Ht2 Hc Hk Hag. unfold tb, rdZ.
  rewrite (rdn_frame M M' (tbl + 3 * c + k) 1); [reflexivity | lia | cbn; unfold two64 in *; lia |].
  intros x Hx. apply Hag. cbn in Hx. lia.
Qed.
Lemma qfold_frame : forall M M' tbl cs wu, 0 <= tbl -> tbl + 768 < two64 -> agree_on M M' tbl 768 ->
  (forall c, In c cs -> 0 <= c <= 255) -> qfold M' tbl cs wu = qfold M tbl cs wu.
Proof.
  intros M M' tbl cs. induction cs as [|c r IH]; intros wu Ht Ht2 Hag Hcs; [reflexivity|].
  unfold qfold. cbn [fold_left]. fold (qfold M' tbl r (qstep M' tbl wu c)). fold (qfold M tbl r (qstep M tbl wu c)).
  unfold qstep. rewrite !(tb_frame M M' tbl c) by (try lia; try exact Hag; apply Hcs; left; reflexivity).
  apply IH; [exact Ht | exact Ht2 | exact Hag |]. intros c' Hc'. apply Hcs. right. exact Hc'.
Qed.
Theorem p_qs_frame : forall args E M M',
  (forall a, APS.in_fp E (fp_qs args) a = true -> M' a = M a) ->
  p_qs (map (uD E) args) M -> p_qs (map (uD E) args) M'.
Proof.
  intros args E M M' Hfp H. unfold fp_qs in Hfp.
  destruct args as [|tbl [|b [|i [|w [|u [|]]]]]]; cbn [map] in H |- *; try contradiction.
  unfold p_qs in H |- *. destruct H as (Pb & Pi & Pbi & Pt & Pt2 & bs & Hrd & Hq).
  assert (IN1 : forall x : word, uD E b <= bv_unsigned x < uD E b + uD E i -> M' x = M x).
  { intros x Hx. apply Hfp. unfold APS.in_fp. cbn [existsb fst snd]. unfold estart, elenZ. cbn [a_base a_off].
    apply Bool.orb_true_iff. left. unfold uD in Hx. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  assert (IN2 : forall x : word, uD E tbl <= bv_unsigned x < uD E tbl + 768 -> M' x = M x).
  { intros x Hx. apply Hfp. unfold APS.in_fp. cbn [existsb fst snd]. unfold estart, elenZ. cbn [a_base a_off edenot].
    apply Bool.orb_true_iff. right. apply Bool.orb_true_iff. left. unfold uD in Hx. rewrite u_lit64. change (768 mod two64) with 768.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  exists bs. split.
  - rewrite <- Hrd. apply rdn_frame; [lia | rewrite Z2Nat.id by lia; unfold two64 in *; lia |]. intros x Hx. apply IN1. rewrite Z2Nat.id in Hx by lia. lia.
  - rewrite <- Hq. unfold two64 in *. apply qfold_frame; [lia | unfold two64; lia | exact IN2 |].
    intros c Hc. apply in_map_iff in Hc as [bt [<- _]]. pose proof (bv_unsigned_in_range _ bt) as R. change (bv_modulus 8) with 256 in R. lia.
Qed.

(* [comment removed for export] *)
Section Rules.
Variable GP : nat -> list Z -> (word -> option byte) -> Prop.
Hypothesis GP70 : forall vs M, GP QS_ID vs M <-> p_qs vs M.

Lemma gholds_qs : forall E M args, APS.gholds GP E M (GA QS_ID args) <-> p_qs (map (uD E) args) M.
Proof. intros. unfold APS.gholds. cbn [g_id g_args]. rewrite GP70. unfold APS.uE, uD. tauto. Qed.

Lemma qfold_app1 : forall M tbl cs c wu, qfold M tbl (cs ++ [c]) wu = qstep M tbl (qfold M tbl cs wu) c.
Proof. intros. unfold qfold. rewrite fold_left_app. reflexivity. Qed.

Lemma uD_lit : forall E z, uD E (ELit z) = z mod two64.
Proof. intros. unfold uD. cbn [edenot]. apply u_lit64. Qed.

Lemma is_val_sound : forall E M kn e z, know_ok SEGS E M kn -> is_val kn e z = true -> uD E e = z.
Proof.
  intros E M kn e z Hkn H. unfold is_val in H.
  destruct (xlo kn e) as [lo|] eqn:Hl; [|discriminate]. destruct (xhi kn e) as [hi|] eqn:Hh; [|discriminate].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst.
  pose proof (xlo_sound SEGS E M kn e _ Hkn Hl). pose proof (xhi_sound SEGS E M kn e _ Hkn Hh). unfold uD. lia.
Qed.

Lemma init_ok_sound : forall E M kn tbl b i w u,
  know_ok SEGS E M kn -> init_ok kn tbl b i w u = true -> p_qs [uD E tbl; uD E b; uD E i; uD E w; uD E u] M.
Proof.
  intros E M kn tbl b i w u Hkn H. unfold init_ok in H.
  apply andb_prop in H as [H Hu]. apply andb_prop in H as [H Hw]. apply andb_prop in H as [Ht Hi].
  destruct tbl as [t| | | | | | |]; try discriminate. apply andb_prop in Ht as [Ht1 Ht2]. apply Z.leb_le in Ht1. apply Z.ltb_lt in Ht2.
  rewrite (is_val_sound E M kn i 0 Hkn Hi), (is_val_sound E M kn w 0 Hkn Hw), (is_val_sound E M kn u 1 Hkn Hu), uD_lit.
  pose proof (u64_range (edenot E b)) as Rb. unfold p_qs. unfold two64 in *.
  rewrite (Z.mod_small t) by lia. unfold uD.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  exists []. split; [reflexivity|]. reflexivity.
Qed.

Lemma step_case_sound : forall E wv uv r0 r1 w' u',
  distinctb (pins (Lenv E wv uv r0 r1)) = true ->
  eclosed (pins (Lenv E wv uv r0 r1)) w' = true -> eclosed (pins (Lenv E wv uv r0 r1)) u' = true ->
  step_case wv uv (var_of r0) (var_of r1) w' u' (uD E (EVar wv)) (uD E (EVar uv)) (uD E r0) (uD E r1) = true ->
  (uD E w', uD E u') = qstep_v (uD E (EVar wv)) (uD E (EVar uv)) (uD E r0) (uD E r1).
Proof.
  intros E wv uv r0 r1 w' u' Hd Hcw Hcu H. unfold step_case in H.
  set (E' := eupds E00 _) in H.
  assert (AG : forall v, In v (pins (Lenv E wv uv r0 r1)) -> ev E v = ev E' v) by (exact (step_env_agree E wv uv r0 r1 Hd)).
  destruct (qstep_v _ _ _ _) as [mw mu]. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2.
  unfold uD. rewrite (edenot_eclosed _ E E' w' Hcw AG), (edenot_eclosed _ E E' u' Hcu AG). rewrite H1, H2. reflexivity.
Qed.

Lemma pins_Lenv : forall E wv uv r0 r1,
  pins [(Some wv, 0); (Some uv, 0); (var_of r0, 0); (var_of r1, 0)] = pins (Lenv E wv uv r0 r1).
Proof. intros. unfold Lenv, pins. cbn [flat_map fst app]. reflexivity. Qed.

Lemma step_with_sound : forall E M kn hyps tbl b i w' u' h,
  know_ok SEGS E M kn -> Forall (APS.gholds GP E M) hyps -> In h hyps ->
  step_with kn tbl b i w' u' h = true -> p_qs [uD E tbl; uD E b; uD E i; uD E w'; uD E u'] M.
Proof.
  intros E M kn hyps tbl b i w' u' h Hkn Hh Hin H. unfold step_with in H.
  destruct (Nat.eqb_spec (g_id h) QS_ID) as [Hid|]; [|discriminate]. cbn [negb] in H.
  destruct h as [hid hargs]. cbn [g_id g_args] in Hid, H. subst hid.
  destruct hargs as [|tbl0 [|b0 [|i0 [|w0 [|u0 [|]]]]]]; try discriminate.
  destruct (var_of w0) as [wv|] eqn:Hw0; [|discriminate]. destruct (var_of u0) as [uv|] eqn:Hu0; [|discriminate].
  destruct w0 as [?|wv'|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?]; try discriminate. cbn [var_of] in Hw0. injection Hw0 as ->.
  destruct u0 as [?|uv'|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?]; try discriminate. cbn [var_of] in Hu0. injection Hu0 as ->.
  destruct (expr_eqb tbl tbl0 && expr_eqb b b0)%bool eqn:Heq; cbn [negb] in H; [|discriminate].
  apply andb_prop in Heq as [Ht Hb]. apply expr_eqb_eq in Ht. apply expr_eqb_eq in Hb. subst tbl0 b0.
  destruct (lin_ge0 kn [(i, 0)] [(i0, 1)] && lin_ge0 kn [(i0, 1)] [(i, 0)])%bool eqn:Hlin; [|discriminate]. cbn [negb] in H.
  apply andb_prop in Hlin as [L1 L2].
  pose proof (lin_ge0_sound SEGS E M kn _ _ Hkn L1) as G1. pose proof (lin_ge0_sound SEGS E M kn _ _ Hkn L2) as G2.
  cbn [xt_den fst snd] in G1, G2.
  assert (Hi : uD E i = uD E i0 + 1) by (unfold uD; lia). clear G1 G2 L1 L2.
  destruct (find_rec1 kn [(b, 0); (i0, 0)]) as [cv|] eqn:Hc; [|discriminate]. cbn zeta in H.
  destruct (find_rec1 kn [(byte_of cv, 0); (byte_of cv, 0); (byte_of cv, 0); (tbl, 0)]) as [r0|] eqn:Hr0; [|discriminate].
  destruct (find_rec1 kn [(byte_of cv, 0); (byte_of cv, 0); (byte_of cv, 0); (tbl, 1)]) as [r1|] eqn:Hr1; [|discriminate].
  destruct (vals_of kn (EVar wv)) as [ws|] eqn:Hws; [|discriminate].
  destruct (vals_of kn (EVar uv)) as [us|] eqn:Hus; [|discriminate].
  destruct (vals_of kn r0) as [m0s|] eqn:Hm0; [|discriminate].
  destruct (vals_of kn r1) as [m1s|] eqn:Hm1; [|discriminate].
  cbn zeta in H. rewrite (pins_Lenv E) in H.
  destruct (match r0 with ELit _ | EVar _ => true | _ => false end && match r1 with ELit _ | EVar _ => true | _ => false end)%bool; [|discriminate]. cbn [negb] in H.
  destruct (eclosed _ w' && eclosed _ u')%bool eqn:Hcl; [|discriminate]. cbn [negb] in H. apply andb_prop in Hcl as [Hcw Hcu].
  destruct (distinctb _) eqn:Hd; [|discriminate]. cbn [negb] in H.
  (* [comment removed for export] *)
  pose proof (proj1 (Forall_forall _ _) Hh _ Hin) as HQ. apply gholds_qs in HQ. cbn [map] in HQ.
  unfold p_qs in HQ. destruct HQ as (Pb & Pi & Pbi & Pt & Pt2 & bs & Hrd & Hq).
  (* [comment removed for export] *)
  destruct (find_rec1_sound E M kn _ cv Hkn Hc) as (C1 & C2 & C3). cbn [xt_den fst snd] in C1, C2, C3.
  replace (bv_unsigned (edenot E b) + 0 + (bv_unsigned (edenot E i0) + 0 + 0)) with (uD E b + uD E i0) in C2, C3 by (unfold uD; lia).
  (* [comment removed for export] *)
  pose proof (tb_of_rec E M kn (byte_of cv) tbl 0 r0 Hkn Hr0) as T0. pose proof (tb_of_rec E M kn (byte_of cv) tbl 1 r1 Hkn Hr1) as T1.
  rewrite u_byte_of in T0, T1.
  (* [comment removed for export] *)
  pose proof (vals_of_sound E M kn _ _ Hkn Hws) as Iw. pose proof (vals_of_sound E M kn _ _ Hkn Hus) as Iu.
  pose proof (vals_of_sound E M kn _ _ Hkn Hm0) as I0. pose proof (vals_of_sound E M kn _ _ Hkn Hm1) as I1.
  pose proof (allz_true _ _ _ H Iw) as H'. cbn beta in H'. pose proof (allz_true _ _ _ H' Iu) as H''. cbn beta in H''.
  pose proof (allz_true _ _ _ H'' I0) as H3. cbn beta in H3. pose proof (allz_true _ _ _ H3 I1) as H4. cbn beta in H4.
  pose proof (step_case_sound E wv uv r0 r1 w' u' Hd Hcw Hcu H4) as SC.
  (* [comment removed for export] *)
  assert (B0 : uD E r0 mod 256 = uD E r0) by (apply Z.mod_small; pose proof (vals_of_bounded kn r0 m0s _ Hm0 I0); lia).
  assert (B1 : uD E r1 mod 256 = uD E r1) by (apply Z.mod_small; pose proof (vals_of_bounded kn r1 m1s _ Hm1 I1); lia).
  rewrite B0 in T0. rewrite B1 in T1.
  (* [comment removed for export] *)
  unfold p_qs. unfold two64 in *. rewrite Hi. split; [lia|]. split; [unfold uD; pose proof (u64_range (edenot E i0)); lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  exists (bs ++ [Z_to_bv 8 (uD E cv)]). split.
  - replace (Z.to_nat (uD E i0 + 1)) with (Z.to_nat (uD E i0) + 1)%nat by lia.
    apply rdn_app; [exact Hrd|].
    replace (Z_to_bv 64 (uD E b) + nat_to_word (Z.to_nat (uD E i0)))%bv with (Z_to_bv 64 (uD E b + uD E i0)); [exact C3|].
    apply bv_eq. rewrite u_lit64. unfold nat_to_word. rewrite bv_add_unsigned, !u_lit64, Z2Nat.id by lia.
    change two64 with (2 ^ 64). change (bv_modulus 64) with (2 ^ 64).
    rewrite (Z.mod_small (uD E b)) by (unfold uD; pose proof (u64_range (edenot E b)); lia).
    rewrite (Z.mod_small (uD E i0)) by (unfold uD; pose proof (u64_range (edenot E i0)); lia).
    rewrite (Z.mod_small (uD E b + uD E i0)) by lia. rewrite bv_wrap64_mod. symmetry. apply Z.mod_small. lia.
  - rewrite map_app. cbn [map]. rewrite qfold_app1, Hq. unfold qstep. cbn [fst snd].
    rewrite Z_to_bv_unsigned, bv_wrap8_mod. change (2 ^ 8) with 256.
    rewrite T0, T1. symmetry. exact SC.
Qed.


Lemma p_qs_fun : forall tbl b i w1 u1 w2 u2 M,
  p_qs [tbl; b; i; w1; u1] M -> p_qs [tbl; b; i; w2; u2] M -> w1 = w2 /\ u1 = u2.
Proof.
  intros tbl b i w1 u1 w2 u2 M H1 H2. unfold p_qs in H1, H2.
  destruct H1 as (_ & _ & _ & _ & _ & bs1 & R1 & Q1). destruct H2 as (_ & _ & _ & _ & _ & bs2 & R2 & Q2).
  rewrite R1 in R2. injection R2 as <-. rewrite Q1 in Q2. injection Q2 as <- <-. split; reflexivity.
Qed.

Lemma fun_pair_sound : forall E M kn hyps a1 a2 h1 h2,
  know_ok SEGS E M kn -> Forall (APS.gholds GP E M) hyps -> In h1 hyps -> In h2 hyps ->
  fun_pair kn a1 a2 h1 h2 = true -> kentry_ok SEGS E M (KRange (EAlu ALU_SUB a1 a2) 0 0).
Proof.
  intros E M kn hyps a1 a2 h1 h2 Hkn Hh Hin1 Hin2 H. unfold fun_pair in H.
  destruct (Nat.eqb (g_id h1) QS_ID && Nat.eqb (g_id h2) QS_ID)%bool eqn:Hid; [|discriminate]. cbn [negb] in H.
  apply andb_prop in Hid as [Hi1 Hi2]. apply Nat.eqb_eq in Hi1. apply Nat.eqb_eq in Hi2.
  destruct h1 as [id1 args1]. destruct h2 as [id2 args2]. cbn [g_id g_args] in Hi1, Hi2, H. subst id1 id2.
  destruct args1 as [|tbl1 [|b1 [|i1 [|w1 [|u1 [|]]]]]]; try discriminate.
  destruct args2 as [|tbl2 [|b2 [|i2 [|w2 [|u2 [|]]]]]]; try discriminate.
  apply andb_prop in H as [H Hr]. apply andb_prop in H as [H L2]. apply andb_prop in H as [H L1]. apply andb_prop in H as [Ht Hb].
  apply expr_eqb_eq in Ht. apply expr_eqb_eq in Hb. apply expr_eqb_eq in Hr. subst tbl2 b2 a2.
  pose proof (lin_ge0_sound SEGS E M kn _ _ Hkn L1) as G1. pose proof (lin_ge0_sound SEGS E M kn _ _ Hkn L2) as G2.
  cbn [xt_den fst snd] in G1, G2.
  pose proof (proj1 (Forall_forall _ _) Hh _ Hin1) as Q1. pose proof (proj1 (Forall_forall _ _) Hh _ Hin2) as Q2.
  apply gholds_qs in Q1. apply gholds_qs in Q2. cbn [map] in Q1, Q2.
  replace (uD E i2) with (uD E i1) in Q2 by (unfold uD; lia).
  destruct (p_qs_fun _ _ _ _ _ _ _ _ Q1 Q2) as [Hw _].
  assert (Hd : edenot E w1 = edenot E w2) by (apply bv_eq; unfold uD in Hw; exact Hw).
  cbn [kentry_ok edenot]. rewrite (ereplace_denot E w1 w2 a1 Hd). rewrite u_sub64.
  rewrite Z.sub_diag. rewrite Z.mod_0_l by (cbn; lia). lia.
Qed.

Lemma fun_ok_sound : forall E M kn hyps a1 a2,
  know_ok SEGS E M kn -> Forall (APS.gholds GP E M) hyps ->
  fun_ok kn hyps a1 a2 = true -> kentry_ok SEGS E M (KRange (EAlu ALU_SUB a1 a2) 0 0).
Proof.
  intros E M kn hyps a1 a2 Hkn Hh H. unfold fun_ok in H.
  apply existsb_exists in H as [h1 [Hin1 H]]. apply existsb_exists in H as [h2 [Hin2 H]].
  exact (fun_pair_sound E M kn hyps a1 a2 h1 h2 Hkn Hh Hin1 Hin2 H).
Qed.

Theorem qs_vcok_sound : forall v, qs_vcok v = true -> APS.vc_holds SEGS GP v.
Proof.
  intros [k hyps c p] H. unfold qs_vcok in H. cbn [vc_concl vc_kn vc_hyps] in H.
  unfold APS.vc_holds. cbn [vc_kn vc_hyps vc_concl]. intros E M HK HP.
  destruct c as [g|K].
  - destruct (Nat.eqb_spec (g_id g) QS_ID) as [Hid|]; [|discriminate]. cbn [negb] in H.
    destruct g as [id args]. cbn [g_id g_args] in Hid, H. subst id.
    destruct args as [|tbl [|b [|i [|w [|u [|]]]]]]; try discriminate.
    apply gholds_qs. cbn [map].
    apply Bool.orb_true_iff in H. destruct H as [H|H].
    + exact (init_ok_sound E M k tbl b i w u HK H).
    + apply existsb_exists in H as [h [Hin Hs]]. exact (step_with_sound E M k hyps tbl b i w u h HK HP Hin Hs).
  - destruct K as [| | | | |e lo hi| | | |]; try discriminate.
    destruct e as [| |op a1 a2| | | | |]; try discriminate. destruct op; try discriminate.
    destruct lo; try discriminate. destruct hi; try discriminate.
    exact (fun_ok_sound E M k hyps a1 a2 HK HP H).
Qed.

End Rules.
End WithSegs.
End MG.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Module PG.
Section S.
Context {fx : FPState}.
Variable SEGS : list Segment.

Definition fp (id : nat) (args : list expr) : list (expr * expr) :=
  if Nat.eqb id MN2.SLOT_ID then MN2.slot_fp args else if Nat.eqb id MG.QS_ID then MG.fp_qs args else [].
Definition Gpm : gparams := GPAR fp MG.qs_vcokM.   (* [comment removed for export] *)

Definition GPpm (id : nat) (vs : list Z) (M : word -> option byte) : Prop :=
  if Nat.eqb id MN2.SLOT_ID then slot_sem SEGS vs M else if Nat.eqb id MG.QS_ID then MG.p_qs SEGS vs M else False.

Lemma GPpm_slot : forall vs M, GPpm MN2.SLOT_ID vs M <-> slot_sem SEGS vs M.
Proof. intros. unfold GPpm. rewrite Nat.eqb_refl. tauto. Qed.
Lemma GPpm_qs : forall vs M, GPpm MG.QS_ID vs M <-> MG.p_qs SEGS vs M.
Proof. intros. unfold GPpm. cbn [Nat.eqb MG.QS_ID MN2.SLOT_ID]. tauto. Qed.

(* [comment removed for export] *)
Lemma GPpm_frame : forall id args E M M',
  (forall a, APS.in_fp E (g_fp Gpm id args) a = true -> M' a = M a) ->
  GPpm id (map (APS.uE E) args) M -> GPpm id (map (APS.uE E) args) M'.
Proof.
  intros id args E M M' Hfp H. unfold GPpm in *. unfold Gpm in Hfp. cbn [g_fp] in Hfp. unfold fp in Hfp.
  destruct (Nat.eqb_spec id MN2.SLOT_ID) as [->|Hne].
  - apply (SlotProp.GPm_frame SEGS MN2.SLOT_ID args E M M'); unfold SlotProp.GPm; rewrite ?Nat.eqb_refl; [|exact H].
    unfold MN2.Gm. cbn [g_fp]. rewrite Nat.eqb_refl. exact Hfp.
  - destruct (Nat.eqb_spec id MG.QS_ID) as [->|Hne2]; [|exact H].
    change (map (APS.uE E) args) with (map (MG.uD E) args) in H |- *. exact (MG.p_qs_frame SEGS args E M M' Hfp H).
Qed.

Lemma Gpm_ok : forall v, g_vcok Gpm v = true -> APS.vc_holds SEGS GPpm v.
Proof. intros v H. cbn [g_vcok Gpm] in H. rewrite MG.qs_vcokM_eq in H. exact (MG.qs_vcok_sound SEGS GPpm GPpm_qs v H). Qed.

End S.
End PG.
