(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 ImgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Module AX2B.
Import AX2.
Create HintDb bceq discriminated.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma p_aluop_eqb_eq : forall a b, aluop_eqb a b = true -> a = b.
Proof. intros [] []; cbn; intros; try reflexivity; discriminate. Qed.
Lemma p_mulop_eqb_eq : forall a b, mulop_eqb a b = true -> a = b.
Proof. intros [] []; cbn; intros; try reflexivity; discriminate. Qed.
Lemma p_expr_eqb_eq : forall x y, expr_eqb x y = true -> x = y.
Proof.
  induction x; destruct y; cbn; intros H; try discriminate;
    repeat match goal with
      | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
      | H : (if ?c then _ else false) = true |- _ => let E := fresh "E" in destruct c eqn:E; [|discriminate H]
      end;
    repeat match goal with
      | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
      | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
      | H : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in H
      | H : aluop_eqb _ _ = true |- _ => apply p_aluop_eqb_eq in H
      | H : mulop_eqb _ _ = true |- _ => apply p_mulop_eqb_eq in H
      | H : expr_eqb ?a _ = true, IH : forall y, expr_eqb ?a y = true -> _ |- _ => apply IH in H
      end; subst; reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint pos_pow2_log (p : positive) : option Z :=
  match p with
  | xH => Some 0%Z
  | xO q => match pos_pow2_log q with Some k => Some (Z.succ k) | None => None end
  | xI _ => None
  end.
Lemma pos_pow2_log_spec : forall p k, pos_pow2_log p = Some k -> (0 <= k)%Z /\ Zpos p = (2 ^ k)%Z.
Proof.
  induction p as [q IH|q IH|]; intros k H; cbn [pos_pow2_log] in H; [discriminate| |].
  - destruct (pos_pow2_log q) as [k0|]; [|discriminate]. injection H as <-. destruct (IH k0 eq_refl) as [H0 E].
    split; [lia|]. rewrite Z.pow_succ_r by exact H0. rewrite <- E. reflexivity.
  - injection H as <-. split; [lia | reflexivity].
Qed.
Definition zdivf (a b : Z) : Z :=
  match b with
  | Zpos p => match pos_pow2_log p with Some k => Z.shiftr a k | None => Z.div a b end
  | _ => Z.div a b
  end.
Definition zmodf (a b : Z) : Z :=
  match b with
  | Zpos p => match pos_pow2_log p with Some _ => Z.land a (Z.pred b) | None => Z.modulo a b end
  | _ => Z.modulo a b
  end.
Lemma zdivf_eq : forall a b, zdivf a b = (a / b)%Z.
Proof.
  intros a b. unfold zdivf. destruct b as [|p|p]; try reflexivity.
  destruct (pos_pow2_log p) as [k|] eqn:E; [|reflexivity].
  destruct (pos_pow2_log_spec p k E) as [Hk ->]. apply Z.shiftr_div_pow2. exact Hk.
Qed.
Lemma zmodf_eq : forall a b, zmodf a b = (a mod b)%Z.
Proof.
  intros a b. unfold zmodf. destruct b as [|p|p]; try reflexivity.
  destruct (pos_pow2_log p) as [k|] eqn:E; [|reflexivity].
  destruct (pos_pow2_log_spec p k E) as [Hk ->]. rewrite <- Z.ones_equiv. apply Z.land_ones. exact Hk.
Qed.
Lemma zdivf_feq : zdivf = Z.div.
Proof. apply functional_extensionality. intros a. apply functional_extensionality. intros b. apply zdivf_eq. Qed.
Lemma zmodf_feq : zmodf = Z.modulo.
Proof. apply functional_extensionality. intros a. apply functional_extensionality. intros b. apply zmodf_eq. Qed.

(* [comment removed for export] *)
Definition zshr (a s : Z) : Z := if Z.leb 0 s then Z.shiftr a s else (a / 2 ^ s)%Z.
Definition zshl (a s : Z) : Z := if Z.leb 0 s then Z.shiftl a s else (a * 2 ^ s)%Z.
Definition zmodp (a j : Z) : Z := if Z.leb 0 j then Z.land a (Z.ones j) else (a mod 2 ^ j)%Z.
Lemma zshr_feq : zshr = (fun a s => (a / 2 ^ s)%Z).
Proof.
  apply functional_extensionality. intros a. apply functional_extensionality. intros s. unfold zshr.
  destruct (Z.leb_spec 0 s); [apply Z.shiftr_div_pow2; assumption | reflexivity].
Qed.
Lemma zshl_feq : zshl = (fun a s => (a * 2 ^ s)%Z).
Proof.
  apply functional_extensionality. intros a. apply functional_extensionality. intros s. unfold zshl.
  destruct (Z.leb_spec 0 s); [apply Z.shiftl_mul_pow2; assumption | reflexivity].
Qed.
Lemma zmodp_feq : zmodp = (fun a j => (a mod 2 ^ j)%Z).
Proof.
  apply functional_extensionality. intros a. apply functional_extensionality. intros j. unfold zmodp.
  destruct (Z.leb_spec 0 j); [apply Z.land_ones; assumption | reflexivity].
Qed.
(* [comment removed for export] *)
Definition shamt64 (s : Z) : Z := if (if Z.leb 0 s then Z.ltb s 64 else false) then s else (s mod 64)%Z.
Lemma shamt64_feq : shamt64 = (fun s => (s mod 64)%Z).
Proof.
  apply functional_extensionality. intros s. unfold shamt64.
  destruct (Z.leb_spec 0 s); [|reflexivity]. destruct (Z.ltb_spec s 64); [|reflexivity]. symmetry. apply Z.mod_small. lia.
Qed.
Definition lit_shamtF (e : expr) : option Z := match e with ELit s => Some (shamt64 s) | _ => None end.
Lemma lit_shamtF_feq : lit_shamtF = lit_shamt.
Proof. apply functional_extensionality. intros e. unfold lit_shamtF, lit_shamt. rewrite shamt64_feq. reflexivity. Qed.
(* [comment removed for export] *)
Definition two8z : Z := 2 ^ 8.
Definition two16z : Z := 2 ^ 16.
Definition pow8n (n : nat) : Z :=
  match n with
  | 1%nat => two8z | 2%nat => two16z | 4%nat => two32z | 8%nat => two64
  | _ => (2 ^ (8 * Z.of_nat n))%Z
  end.
Lemma pow8n_feq : pow8n = (fun n => (2 ^ (8 * Z.of_nat n))%Z).
Proof.
  apply functional_extensionality. intros n. unfold pow8n.
  do 9 (destruct n as [|n]; [reflexivity|]). reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint pos_ctz (fuel : nat) (p : positive) : Z :=
  match fuel with
  | O => 0%Z
  | S f => match p with xO q => (1 + pos_ctz f q)%Z | _ => 0%Z end
  end.
Definition ctz64F (z : Z) : Z :=
  match z with Z0 => 64%Z | Zpos p => pos_ctz 64 p | Zneg p => pos_ctz 64 p end.
Lemma ctz_fuel_0 : forall f, ctz_fuel f 0 = Z.of_nat f.
Proof. induction f as [|f IH]; [reflexivity|]. cbn [ctz_fuel]. change (0 mod 2)%Z with 0%Z. change (0 / 2)%Z with 0%Z. cbn [Z.eqb]. rewrite IH. lia. Qed.
Lemma ctz_fuel_pos : forall f p, ctz_fuel f (Zpos p) = pos_ctz f p.
Proof.
  induction f as [|f IH]; intros p; [reflexivity|]. cbn [ctz_fuel pos_ctz]. destruct p as [q|q|].
  - replace (Z.pos q~1 mod 2)%Z with 1%Z; [reflexivity|]. rewrite Pos2Z.inj_xI. symmetry. rewrite Z.add_comm, Z.mul_comm. rewrite Z.mod_add by lia. reflexivity.
  - replace (Z.pos q~0 mod 2)%Z with 0%Z; [|rewrite Pos2Z.inj_xO; symmetry; rewrite Z.mul_comm; apply Z.mod_mul; lia].
    replace (Z.pos q~0 / 2)%Z with (Z.pos q); [|rewrite Pos2Z.inj_xO; symmetry; rewrite Z.mul_comm; apply Z.div_mul; lia].
    cbn [Z.eqb]. rewrite IH. reflexivity.
  - reflexivity.
Qed.
Lemma ctz_fuel_neg : forall f p, ctz_fuel f (Zneg p) = pos_ctz f p.
Proof.
  induction f as [|f IH]; intros p; [reflexivity|]. cbn [ctz_fuel pos_ctz]. destruct p as [q|q|].
  - replace (Z.neg q~1 mod 2)%Z with 1%Z; [reflexivity|].
    change (Z.neg q~1) with (- Z.pos q~1)%Z. rewrite Pos2Z.inj_xI.
    replace (- (2 * Z.pos q + 1))%Z with (1 + (- Z.pos q - 1) * 2)%Z by lia. rewrite Z.mod_add by lia. reflexivity.
  - replace (Z.neg q~0 mod 2)%Z with 0%Z; [|change (Z.neg q~0) with (- Z.pos q~0)%Z; rewrite Pos2Z.inj_xO;
      replace (- (2 * Z.pos q))%Z with ((- Z.pos q) * 2)%Z by lia; symmetry; apply Z.mod_mul; lia].
    replace (Z.neg q~0 / 2)%Z with (Z.neg q); [|change (Z.neg q~0) with (- Z.pos q~0)%Z; rewrite Pos2Z.inj_xO;
      replace (- (2 * Z.pos q))%Z with ((- Z.pos q) * 2)%Z by lia; rewrite Z.div_mul by lia; reflexivity].
    cbn [Z.eqb]. rewrite IH. reflexivity.
  - reflexivity.
Qed.
Lemma ctz64F_eq : forall z, ctz64F z = ctz64 z.
Proof.
  intros [|p|p]; unfold ctz64F, ctz64; [rewrite ctz_fuel_0; reflexivity | rewrite ctz_fuel_pos; reflexivity | rewrite ctz_fuel_neg; reflexivity].
Qed.
Lemma ctz64F_feq : ctz64F = ctz64.
Proof. apply functional_extensionality. exact ctz64F_eq. Qed.

(* [comment removed for export] *)
Fixpoint find_rangeF (kn : list kentry) (e : expr) : option (Z * Z) :=
  match kn with
  | [] => None
  | KRange e' lo hi :: rest =>
      if expr_eqb e e' then Some (lo, hi) else
      match e with
      | ELit _ => find_rangeF rest e
      | _ =>
        let '(v, c) := lit_strip e in
        let '(v', c') := lit_strip e' in
        if expr_eqb v v' then
          let d := (c - c')%Z in
          if (if Z.leb 0 lo then if Z.leb lo hi then if Z.ltb hi two64 then if Z.leb 0 (lo + d) then Z.ltb (hi + d) two64 else false else false else false else false)
          then Some ((lo + d)%Z, (hi + d)%Z) else find_rangeF rest e
        else find_rangeF rest e
      end
  | _ :: rest => find_rangeF rest e
  end.
Lemma find_rangeF_eq : forall kn e, find_rangeF kn e = find_range kn e.
Proof.
  intros kn e. induction kn as [|K rest IH]; [reflexivity|].
  destruct K as [a w v|a l|a l bk|lo hi|e1 m|e' lo hi|a n|a1 n1 a2 n2|a l c|a l]; cbn [find_rangeF find_range]; try exact IH.
  destruct (expr_eqb e e'); [reflexivity|]. rewrite IH.
  destruct e; try reflexivity;
    (destruct (lit_strip _) as [v c]; destruct (lit_strip e') as [v' c']; destruct (expr_eqb v v'); [|reflexivity];
     change (2 ^ 64)%Z with two64;
     destruct (Z.leb 0 lo); [|reflexivity]; destruct (Z.leb lo hi); [|reflexivity]; destruct (Z.ltb hi two64); [|reflexivity];
     destruct (Z.leb 0 (lo + (c - c'))); reflexivity).
Qed.

(* [comment removed for export] *)
Definition rel_litD (rb : expr) (rk : Z) (rn : Z) (kb : expr) (kk : Z) (kn : Z) : rangerel :=
  if expr_eqb rb kb then
    if (if Z.ltb 0 rn then Z.ltb 0 kn else false) then
      let d := (rk - kk)%Z in
      if Z.leb (d + rn) 0 then RDisjoint
      else if Z.leb kn d then RDisjoint
      else if (if Z.leb 0 d then Z.leb (d + rn) kn else false) then RInside d else RPartial
    else rel_lit rb rk rn kb kk kn
  else RUnknown.
Lemma rel_litD_eq : forall rb rk rn kb kk kn, rel_litD rb rk rn kb kk kn = rel_lit rb rk rn kb kk kn.
Proof.
  intros. unfold rel_litD. destruct (expr_eqb rb kb) eqn:E; [|unfold rel_lit; rewrite E; reflexivity].
  destruct (Z.ltb_spec 0 rn) as [Hn|]; [|reflexivity]. destruct (Z.ltb_spec 0 kn) as [Hk|]; [|reflexivity].
  unfold rel_lit. rewrite E. cbv zeta.
  destruct (Z.leb_spec (rk - kk + rn) 0); destruct (Z.leb_spec kn (rk - kk)); destruct (Z.leb_spec 0 (rk - kk)); destruct (Z.leb_spec (rk - kk + rn) kn);
    destruct (Z.leb_spec kk rk); destruct (Z.leb_spec (rk + rn) (kk + kn)); destruct (Z.leb_spec (rk + rn) kk); destruct (Z.leb_spec (kk + kn) rk);
    cbn [andb orb]; try reflexivity; lia.
Qed.
Lemma rel_litD_feq : rel_litD = rel_lit.
Proof. do 6 (apply functional_extensionality; intro). apply rel_litD_eq. Qed.
#[export] Hint Rewrite rel_litD_feq : bceq.

(* [comment removed for export] *)
Definition ge0_testF (L : list (Z * expr)) (c : Z) : Z -> Z -> bool :=
  fun lo _ => if Z.leb 0 lo then true
              else let g := ts_gran L 0 in if Z.ltb 1 g then Z.leb 0 (lo + zmodf (c - lo) g)%Z else false.
Lemma ge0_testF_feq : ge0_testF = ge0_test.
Proof. unfold ge0_testF, ge0_test, lin_tight. rewrite zmodf_feq. reflexivity. Qed.
#[export] Hint Rewrite zshr_feq zshl_feq zmodp_feq zmodf_feq zdivf_feq lit_shamtF_feq pow8n_feq shamt64_feq ctz64F_feq ge0_testF_feq : bceq.

(* [comment removed for export] *)
Fixpoint first_var (e : expr) : option nat :=
  match e with
  | ELit _ => None
  | EVar n => Some n
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b =>
      match first_var a with Some n => Some n | None => first_var b end
  | EExt _ _ _ a => first_var a
  | EBlob _ _ _ _ => None
  end.
Definition vkey_of (e : expr) : option nat := first_var (fst (lit_strip e)).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition lget {A : Type} (l : ptree (list A)) (n : nat) : list A :=
  match pt_get l (Pos.of_succ_nat n) with Some b => b | None => [] end.
Definition lset {A : Type} (l : ptree (list A)) (n : nat) (x : A) : ptree (list A) :=
  pt_set (Pos.of_succ_nat n) (x :: lget l n) l.
Lemma lget_lset : forall (A : Type) (l : ptree (list A)) n x m,
  lget (lset l n x) m = if Nat.eqb m n then x :: lget l m else lget l m.
Proof.
  intros A l n x m. unfold lset, lget at 1. unfold lget at 2 3.
  destruct (Nat.eqb_spec m n) as [->|NE].
  - rewrite pt_gss. reflexivity.
  - rewrite pt_gso; [reflexivity|]. intros H. apply NE. apply SuccNat2Pos.inj. exact H.
Qed.
Lemma lget_leaf : forall (A : Type) n, lget (@PTLeaf (list A)) n = [].
Proof. intros A n. unfold lget. rewrite pt_get_leaf. reflexivity. Qed.
Record rindex := RI { ri_vars : ptree (list kentry); ri_other : list kentry }.
Definition ri_bucket (ri : rindex) (k : option nat) : list kentry :=
  match k with Some n => lget (ri_vars ri) n | None => ri_other ri end.
Fixpoint mk_ri (fk : list kentry) : rindex :=
  match fk with
  | [] => RI PTLeaf []
  | K :: rest =>
      let t := mk_ri rest in
      match K with
      | KRange e' _ _ =>
          match vkey_of e' with
          | Some n => RI (lset (ri_vars t) n K) (ri_other t)
          | None => RI (ri_vars t) (K :: ri_other t)
          end
      | _ => t
      end
  end.
Definition find_rangeI_ref (ri : rindex) (e : expr) : option (Z * Z) := find_range (ri_bucket ri (vkey_of e)) e.
Definition find_rangeI0 (ri : rindex) (e : expr) : option (Z * Z) := find_rangeF (ri_bucket ri (vkey_of e)) e.   (* [comment removed for export] *)

Definition okey_eqb (a b : option nat) : bool :=
  match a, b with Some x, Some y => Nat.eqb x y | None, None => true | _, _ => false end.
Lemma okey_eqb_spec : forall a b, reflect (a = b) (okey_eqb a b).
Proof.
  intros [x|] [y|]; cbn; try (constructor; congruence).
  destruct (Nat.eqb_spec x y); constructor; congruence.
Qed.
Lemma ri_bucket_cons : forall t K e' lo hi k,
  K = KRange e' lo hi ->
  ri_bucket (match vkey_of e' with
             | Some n => RI (lset (ri_vars t) n K) (ri_other t)
             | None => RI (ri_vars t) (K :: ri_other t)
             end) k
  = if okey_eqb k (vkey_of e') then K :: ri_bucket t k else ri_bucket t k.
Proof.
  intros t K e' lo hi k ->. destruct (vkey_of e') as [n|] eqn:Ev; destruct k as [m|]; cbn [ri_bucket ri_vars ri_other okey_eqb]; try reflexivity.
  apply lget_lset.
Qed.
Lemma find_rangeI_ref_eq : forall fk e, find_rangeI_ref (mk_ri fk) e = find_range fk e.
Proof.
  intros fk e. unfold find_rangeI_ref. induction fk as [|K rest IH].
  - cbn [mk_ri]. destruct (vkey_of e) as [n|]; cbn [ri_bucket ri_vars ri_other]; [rewrite lget_leaf; reflexivity | reflexivity].
  - cbn [mk_ri]. destruct K as [a w v|a l|a l bk|lo hi|e1 m|e' lo hi|a n|a1 n1 a2 n2|a l c|a l];
      cbn [find_range]; rewrite <- ?IH; try reflexivity.
    rewrite (ri_bucket_cons (mk_ri rest) _ e' lo hi _ eq_refl).
    destruct (okey_eqb_spec (vkey_of e) (vkey_of e')) as [EQ|NE].
    + cbn [find_range]. rewrite IH. reflexivity.
    + rewrite IH. destruct (expr_eqb e e') eqn:Ee.
      * exfalso. apply NE. apply p_expr_eqb_eq in Ee. subst. reflexivity.
      * destruct (lit_strip e) as [v c] eqn:Lx. destruct (lit_strip e') as [v' c'] eqn:Le'.
        destruct (expr_eqb v v') eqn:Ev.
        -- exfalso. apply NE. unfold vkey_of. rewrite Lx, Le'. cbn [fst]. apply p_expr_eqb_eq in Ev. subst. reflexivity.
        -- destruct e; reflexivity.
Qed.
Lemma find_rangeI0_eq : forall fk e, find_rangeI0 (mk_ri fk) e = find_range fk e.
Proof. intros fk e. unfold find_rangeI0. rewrite find_rangeF_eq. apply find_rangeI_ref_eq. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint esize (e : expr) : nat :=
  match e with
  | ELit _ | EVar _ | EBlob _ _ _ _ => 1
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => S (esize a + esize b)
  | EExt _ _ _ a => S (esize a)
  end.
Definition kfp (K : kentry) : nat := match K with KRange e' _ _ => esize (fst (lit_strip e')) | _ => O end.
Definition deco (B : list kentry) : list (nat * kentry) := List.map (fun K => (kfp K, K)) B.
Fixpoint find_rangeD (fp : nat) (l : list (nat * kentry)) (e : expr) : option (Z * Z) :=
  match l with
  | [] => None
  | (fp', K) :: rest =>
      if Nat.eqb fp fp' then
        match K with
        | KRange e' lo hi =>
            if expr_eqb e e' then Some (lo, hi) else
            match e with
            | ELit _ => find_rangeD fp rest e
            | _ =>
              let '(v, c) := lit_strip e in
              let '(v', c') := lit_strip e' in
              if expr_eqb v v' then
                let d := (c - c')%Z in
                if (if Z.leb 0 lo then if Z.leb lo hi then if Z.ltb hi two64 then if Z.leb 0 (lo + d) then Z.ltb (hi + d) two64 else false else false else false else false)
                then Some ((lo + d)%Z, (hi + d)%Z) else find_rangeD fp rest e
              else find_rangeD fp rest e
            end
        | _ => find_rangeD fp rest e
        end
      else find_rangeD fp rest e
  end.
Lemma find_rangeD_eq : forall B e, find_rangeD (esize (fst (lit_strip e))) (deco B) e = find_rangeF B e.
Proof.
  intros B e. induction B as [|K rest IH]; [reflexivity|]. unfold deco in *. cbn [List.map find_rangeD].
  destruct (Nat.eqb (esize (fst (lit_strip e))) (kfp K)) eqn:EQ.
  - destruct K as [a w v|a l|a l bk|lo hi|e1 m|e' lo hi|a n|a1 n1 a2 n2|a l c|a l]; cbn [find_rangeF]; try exact IH.
    rewrite IH. reflexivity.
  - destruct K as [a w v|a l|a l bk|lo hi|e1 m|e' lo hi|a n|a1 n1 a2 n2|a l c|a l]; cbn [find_rangeF]; try exact IH.
    cbn [kfp] in EQ. apply Nat.eqb_neq in EQ.
    destruct (expr_eqb e e') eqn:Ee; [exfalso; apply EQ; apply p_expr_eqb_eq in Ee; subst; reflexivity|].
    rewrite IH. destruct (lit_strip e) as [v c] eqn:Lx. destruct (lit_strip e') as [v' c'] eqn:Le'. cbn [fst] in EQ.
    destruct (expr_eqb v v') eqn:Ev; [exfalso; apply EQ; apply p_expr_eqb_eq in Ev; subst; reflexivity|].
    destruct e; reflexivity.
Qed.
Record rindexL := RIL { ril_ri : rindex; ril_list : list (list (nat * kentry)); ril_other : list (nat * kentry) }.
Fixpoint max_key (fk : list kentry) : nat :=
  match fk with
  | [] => O
  | KRange e' _ _ :: rest => match vkey_of e' with Some n => Nat.max n (max_key rest) | None => max_key rest end
  | _ :: rest => max_key rest
  end.
Fixpoint mk_list (t : ptree (list kentry)) (k : positive) (cnt : nat) : list (list (nat * kentry)) :=
  match cnt with
  | O => []
  | S c => deco (match pt_get t k with Some b => b | None => [] end) :: mk_list t (Pos.succ k) c
  end.
Definition mk_riL (fk : list kentry) : rindexL :=
  let t := mk_ri fk in RIL t (mk_list (ri_vars t) xH (S (max_key fk))) (deco (ri_other t)).
Definition ri_bucketL (r : rindexL) (k : option nat) : list (nat * kentry) :=
  match k with
  | Some n => match nth_error (ril_list r) n with Some b => b | None => deco (lget (ri_vars (ril_ri r)) n) end
  | None => ril_other r
  end.
Definition find_rangeI (r : rindexL) (e : expr) : option (Z * Z) :=
  find_rangeD (esize (fst (lit_strip e))) (ri_bucketL r (vkey_of e)) e.
Lemma mk_list_nth : forall t cnt j i b, nth_error (mk_list t (Pos.of_succ_nat j) cnt) i = Some b -> b = deco (lget t (j + i)).
Proof.
  intros t cnt. induction cnt as [|c IH]; intros j i b H; [destruct i; discriminate|].
  cbn [mk_list] in H. destruct i as [|i].
  - cbn [nth_error] in H. injection H as <-. rewrite Nat.add_0_r. reflexivity.
  - cbn [nth_error] in H. rewrite <- SuccNat2Pos.inj_succ in H. rewrite (IH (S j) i b H). f_equal. f_equal. lia.
Qed.
Lemma ri_bucketL_eq : forall fk k, ri_bucketL (mk_riL fk) k = deco (ri_bucket (mk_ri fk) k).
Proof.
  intros fk [n|]; [|reflexivity]. unfold ri_bucketL, mk_riL. cbn [ril_list ril_ri ri_bucket].
  destruct (nth_error _ n) as [b|] eqn:E; [|reflexivity].
  change xH with (Pos.of_succ_nat 0) in E. apply mk_list_nth in E. exact E.
Qed.
Lemma find_rangeI_eq : forall fk e, find_rangeI (mk_riL fk) e = find_range fk e.
Proof. intros fk e. unfold find_rangeI. rewrite ri_bucketL_eq, find_rangeD_eq. exact (find_rangeI0_eq fk e). Qed.

(* [comment removed for export] *)
Definition skey (c : saddr) (m : expr) (c' : saddr) (m' : expr) : bool :=
  if Z.eqb (a_off c) (a_off c') then if expr_eqb (a_base c) (a_base c') then expr_eqb m m' else false else false.
Fixpoint sd_find (tab : list (saddr * expr * positive)) (c : saddr) (m : expr) : option positive :=
  match tab with
  | [] => None
  | (c', m', i) :: r => if skey c m c' m' then Some i else sd_find r c m
  end.
Definition sd_intern (tab : list (saddr * expr * positive)) (nx : positive) (c : saddr) (m : expr)
  : positive * list (saddr * expr * positive) * positive :=
  match sd_find tab c m with
  | Some i => (i, tab, nx)
  | None => (nx, (c, m, nx) :: tab, Pos.succ nx)
  end.
(* [comment removed for export] *)
Definition zkey (z : Z) : positive := match z with Z0 => xH | Zpos p => xO p | Zneg p => xI p end.
Definition sd_key (c : saddr) : positive :=
  match a_base c with ELit z => xO (zkey z) | _ => xI (zkey (a_off c)) end.   (* [comment removed for export] *)
Definition sd_findT (tab : ptree (list (saddr * expr * positive))) (c : saddr) (m : expr) : option positive :=
  match pt_get tab (sd_key c) with Some b => sd_find b c m | None => None end.
Definition sd_internT (tab : ptree (list (saddr * expr * positive))) (nx : positive) (c : saddr) (m : expr)
  : positive * ptree (list (saddr * expr * positive)) * positive :=
  match sd_findT tab c m with
  | Some i => (i, tab, nx)
  | None => (nx, pt_set (sd_key c) ((c, m, nx) :: match pt_get tab (sd_key c) with Some b => b | None => [] end) tab, Pos.succ nx)
  end.
Fixpoint mk_kdi0 (fk : list kentry) (tab : ptree (list (saddr * expr * positive))) (nx : positive)
  : list (kentry * positive * positive) * ptree (list (saddr * expr * positive)) * positive :=
  match fk with
  | [] => ([], tab, nx)
  | KDisj c1 m1 c2 m2 :: rest =>
      let '(r, tab1, nx1) := mk_kdi0 rest tab nx in
      let '(i2, tab2, nx2) := sd_internT tab1 nx1 c2 m2 in
      let '(i1, tab3, nx3) := sd_internT tab2 nx2 c1 m1 in
      ((KDisj c1 m1 c2 m2, i1, i2) :: r, tab3, nx3)
  | _ :: rest => mk_kdi0 rest tab nx
  end.
Definition mk_kdi (fk : list kentry) : list (kentry * positive * positive) := fst (fst (mk_kdi0 fk PTLeaf xH)).

(* [comment removed for export] *)
Fixpoint sfd_insert (n : nat) (f : sfact) (l : list (nat * sfact)) : list (nat * sfact) :=
  match l with
  | [] => [(n, f)]
  | (m, g) :: r => if Nat.leb m n then (n, f) :: l else (m, g) :: sfd_insert n f r
  end.
Definition sfd_sort (l : list sfact) : list (nat * sfact) := fold_right (fun f acc => sfd_insert (length (fst f)) f acc) [] l.
Definition sf_sortF (l : list sfact) : list sfact := List.map snd (sfd_sort l).
Definition sfd_ok (D : list (nat * sfact)) : Prop := Forall (fun x => fst x = length (fst (snd x))) D.
Lemma sfd_insert_ok : forall f D, sfd_ok D ->
  List.map snd (sfd_insert (length (fst f)) f D) = sf_insert f (List.map snd D) /\ sfd_ok (sfd_insert (length (fst f)) f D).
Proof.
  intros f D. induction D as [|[m g] r IH]; intros H.
  - split; [reflexivity|]. constructor; [reflexivity|constructor].
  - apply Forall_cons_iff in H as [Hm Hr]. cbn [fst snd] in Hm. subst m. cbn [sfd_insert List.map snd sf_insert].
    destruct (Nat.leb (length (fst g)) (length (fst f))).
    + split; [reflexivity|]. constructor; [reflexivity|]. constructor; [reflexivity|exact Hr].
    + destruct (IH Hr) as [E O]. split; [cbn [List.map snd]; rewrite E; reflexivity|]. constructor; [reflexivity|exact O].
Qed.
Lemma sfd_sort_ok : forall l, List.map snd (sfd_sort l) = sf_sort l /\ sfd_ok (sfd_sort l).
Proof.
  induction l as [|f r [E O]]; [split; [reflexivity|constructor]|].
  unfold sfd_sort, sf_sort in *. cbn [fold_right]. destruct (sfd_insert_ok f _ O) as [E' O']. split; [rewrite E', E; reflexivity | exact O'].
Qed.
Lemma sf_sortF_feq : sf_sortF = sf_sort.
Proof. apply functional_extensionality. intros l. exact (proj1 (sfd_sort_ok l)). Qed.

Record bctx : Type := BC {
  bc_fk : list kentry;      (* [comment removed for export] *)
  bc_ffk : list kentry;     (* [comment removed for export] *)
  bc_fs : list sfact;       (* [comment removed for export] *)
  bc_fss : list sfact;      (* [comment removed for export] *)
  bc_ri : rindexL;          (* [comment removed for export] *)
  bc_kdi : list (kentry * positive * positive)   (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Definition mkbc0 (fk : list kentry) (fs : list sfact) : bctx :=
  BC fk (facts_of fk) fs (sf_sortF fs) (mk_riL (facts_of fk)) (mk_kdi fk).   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma zmod64_feq : zmod64 = (fun z => (z mod 2 ^ 64)%Z).
Proof. apply functional_extensionality. exact zmod64_eq. Qed.
Lemma zdiv64_feq : zdiv64 = (fun z => (z / 2 ^ 64)%Z).
Proof. apply functional_extensionality. exact zdiv64_eq. Qed.

Lemma lin_range_ext : forall r1 r2 c ts, (forall a, r1 a = r2 a) -> lin_range r1 c ts = lin_range r2 c ts.
Proof. intros r1 r2 c ts H. induction ts as [|[k a] rest IH]; [reflexivity|]. cbn [lin_range]. rewrite H, IH. reflexivity. Qed.

(* [comment removed for export] *)
Ltac beq_crush rw :=
  repeat (first [ reflexivity
                | progress rw
                | lazymatch goal with
                  | |- ?L = _ =>
                      lazymatch L with
                      | (if ?c then _ else _) => destruct c
                      | (match ?x with _ => _ end) => destruct x
                      end
                  end ]).

Fixpoint erange_fB (fuel : nat) (bc : bctx) (e : expr) {struct fuel} : option (Z * Z) :=
  match fuel with
  | O => None
  | S fuel' =>
  let erange := erange_fB fuel' in
  match find_rangeI (bc_ri bc) e with
  | Some r => Some (clampi r)
  | None =>
  match (let l := lin_of e in
         if lin_trivial l then None
         else match lin_range (erange bc) (fst l) (snd l) with
              | Some (lo, hi) =>
                  (* [comment removed for export] *)
                  let q := zdiv64 lo in   (* [comment removed for export] *)
                  if Z.eqb q (zdiv64 hi) then Some ((lo - q * two64)%Z, (hi - q * two64)%Z) else None
              | None => None
              end) with
  | Some r => Some r
  | None =>
  match e with
  | ELit z => let v := zmod64 z in Some (v, v)   (* [comment removed for export] *)
  | EVar _ => None
  | EAlu op a b =>
      match op with
      | ALU_ADD =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.ltb (ah + bh) two64 then Some ((al + bl)%Z, (ah + bh)%Z)
              else if Z.leb two64 (al + bl) then Some ((al + bl - two64)%Z, (ah + bh - two64)%Z)
              else None
          | _, _ => None
          end
      | ALU_SUB =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.leb bh al then Some ((al - bh)%Z, (ah - bl)%Z)
              else if Z.ltb ah bl then Some ((al - bh + two64)%Z, (ah - bl + two64)%Z)
              else None
          | _, _ => None
          end
      | ALU_AND =>
          (* [comment removed for export] *)
          match (match b, erange bc a with
                 | ELit m, Some (al, ah) =>
                     let m' := zmod64 m in
                     let j := Z.log2 (m' + 1) in
                     if (if (if Z.eqb (m' + 1) (2 ^ j) then Z.leb (zshr al j) (zshr ah j) else false) then Z.eqb (zshr al j) (zshr ah j) else false)
                     then Some (zmodp al j, zmodp ah j)
                     else let jh := Z.log2 (two64 - m') in
                          if (if Z.eqb (two64 - m') (2 ^ jh) then Z.ltb jh 64 else false)
                          then Some ((al - zmodp al jh)%Z, (ah - zmodp ah jh)%Z)
                          else None
                 | _, _ => None
                 end) with
          | Some r => Some r
          | None =>
          match erange bc a, erange bc b with
          | Some (_, ah), Some (_, bh) => Some (0%Z, Z.min ah bh)
          | Some (_, ah), None => Some (0%Z, ah)
          | None, Some (_, bh) => Some (0%Z, bh)
          | None, None => None
          end
          end
      | ALU_OR =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) => Some (Z.max al bl, mask_cover (Z.max ah bh))
          | _, _ => None
          end
      | ALU_XOR =>
          match erange bc a, erange bc b with
          | Some (_, ah), Some (_, bh) => Some (0%Z, mask_cover (Z.max ah bh))
          | _, _ => None
          end
      | ALU_SRL =>
          match erange bc a, lit_shamtF b with
          | Some (al, ah), Some s => Some (zshr al s, zshr ah s)
          | _, _ => None
          end
      | ALU_SRA =>
          match erange bc a, lit_shamtF b with
          | Some (al, ah), Some s =>
              if Z.ltb ah two63z then Some (zshr al s, zshr ah s) else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange bc a, lit_shamtF b with
          | Some (al, ah), Some s =>
              if Z.ltb (zshl ah s) two64 then Some (zshl al s, zshl ah s) else None
          | _, _ => None
          end
      | ALU_SLTU =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.ltb ah bl then Some (1%Z, 1%Z)
              else if Z.leb bh al then Some (0%Z, 0%Z) else Some (0%Z, 1%Z)
          | _, _ => Some (0%Z, 1%Z)
          end
      | ALU_SLT =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.ltb ah two63z && Z.ltb bh two63z)%bool then
                (if Z.ltb ah bl then Some (1%Z, 1%Z)
                 else if Z.leb bh al then Some (0%Z, 0%Z) else Some (0%Z, 1%Z))
              else Some (0%Z, 1%Z)
          | _, _ => Some (0%Z, 1%Z)
          end
      end
  | EAluw op a b =>
      match op with
      | ALU_ADD =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              let bl' := if Z.eqb bl bh then zsigned64 bl else bl in
              let bh' := if Z.eqb bl bh then zsigned64 bh else bh in
              if (Z.leb 0 (al + bl') && Z.ltb (ah + bh') two31z)%bool
              then Some ((al + bl')%Z, (ah + bh')%Z) else None
          | _, _ => None
          end
      | ALU_SUB =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb bh al && Z.ltb (ah - bl) two31z)%bool
              then Some ((al - bh)%Z, (ah - bl)%Z) else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange bc a, lit_shamtF b with
          | Some (al, ah), Some s =>
              let s' := zmodf s 32 in
              if Z.ltb (zshl ah s') two31z then Some (zshl al s', zshl ah s') else None
          | _, _ => None
          end
      | ALU_SRL =>
          match erange bc a, lit_shamtF b with
          | Some (al, ah), Some s =>
              let s' := zmodf s 32 in
              if (Z.ltb ah two32z && (Z.ltb 0 s' || Z.ltb ah two31z))%bool
              then Some (zshr al s', zshr ah s') else None
          | _, _ => None
          end
      | ALU_SRA =>
          match erange bc a, lit_shamtF b with
          | Some (al, ah), Some s =>
              let s' := zmodf s 32 in
              if Z.ltb ah two31z then Some (zshr al s', zshr ah s') else None
          | _, _ => None
          end
      | _ => None
      end
  | EMd op a b =>
      match op with
      | M_MUL =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb 0 al && Z.leb 0 bl && Z.ltb (ah * bh) two64)%bool
              then Some ((al * bl)%Z, (ah * bh)%Z) else None
          | _, _ => None
          end
      | M_MULHU =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb 0 al && Z.leb 0 bl)%bool
              then Some (zdiv64 (al * bl), zdiv64 (ah * bh)) else None
          | _, _ => None
          end
      | M_DIVU =>
          match erange bc a, b with
          | Some (al, ah), ELit d =>
              let d' := zmod64 d in
              if Z.ltb 0 d' then Some ((al / d')%Z, (ah / d')%Z) else None
          | _, _ => None
          end
      | M_REMU =>
          match erange bc a, b with
          | Some (al, ah), ELit d =>
              let d' := zmod64 d in
              if Z.ltb 0 d' then Some (0%Z, Z.min ah (d' - 1)) else None
          | _, _ => None
          end
      | _ => None
      end
  | EMdw _ _ _ => None
  | EExt sx lo n a =>
      let w := pow8n n in
      if sx then
        match lo, erange bc a with
        | O, Some (al, ah) =>
            if (Z.leb 0 al && Z.ltb ah (zdivf w 2))%bool then Some (al, ah)
            else if (Nat.leb 1 n && Nat.leb n 8 && Z.leb (zdivf w 2) al && Z.ltb ah w)%bool
                 then Some ((two64 - w + al)%Z, (two64 - w + ah)%Z) else None
        | _, _ => None
        end
      else
        match lo, erange bc a with
        | O, Some (al, ah) =>
            if (Z.leb 0 al && Z.ltb ah w)%bool then Some (al, ah) else Some (0%Z, Z.min (w - 1) two64m1)
        | _, _ => Some (0%Z, Z.min (w - 1) two64m1)
        end
  | EBlob sx k i n =>
      (* [comment removed for export] *)
      if sx then Some (0%Z, two64m1) else Some (0%Z, Z.min (pow8n n - 1) two64m1)%Z
  end
  end
  end
  end.

Definition erange0B (bc : bctx) (e : expr) : option (Z * Z) := erange_fB erange_fuel bc e.

Definition erangeB (bc : bctx) (e : expr) : option (Z * Z) :=
  let r := erange0B bc e in
  let '(e', s) := deand e in
  if Z.eqb s 0 then r else
  match erange0B bc (unlin (lin_of e')) with     (* [comment removed for export] *)
  | Some (lo', hi') =>
      if Z.leb s lo' then
        match r with
        | Some (lo, hi) => Some (Z.max lo (lo' - s), Z.min hi hi')
        | None => Some ((lo' - s)%Z, hi')
        end
      else r
  | None => r
  end.

Definition base_rangeB (bc : bctx) (e : expr) : option (Z * Z) :=
  match e with ELit z => let v := zmod64 z in Some (v, v) | _ => erangeB bc e end.   (* [comment removed for export] *)

Definition ealignB (bc : bctx) (e : expr) : Z := Z.max (ealign0 (bc_ffk bc) e) (pageup_align e).

Definition lin_nowrapB (bc : bctx) (e : expr) : bool :=
  let l := lin_of e in
  match lin_range (erangeB bc) (fst l) (snd l) with
  | Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi two64)%bool
  | None => false
  end.

Fixpoint srl_expandB (bc : bctx) (ts : list (Z * expr)) : Z * list (Z * expr) :=
  match ts with
  | [] => (0%Z, [])
  | (k, a) :: rest =>
      let '(c, ts') := srl_expandB bc rest in
      let keep := (c, lins_e k a ts') in
      match a with
      | EAlu ALU_SRL e (ELit s) =>
          let sh := shamt64 (zmod64 s) in
          if (if Z.eqb (zmodp k sh) 0%Z then lin_nowrapB bc e else false) then   (* [comment removed for export] *)
            let q := zshr k sh in
            let le := lin_of e in
            if Z.leb sh (ealignB bc e) then   (* [comment removed for export] *)
              ((c + q * fst le)%Z, fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le))
            else
            ((c + q * fst le)%Z,
             lins_e (- q)%Z (srl_rem e (2 ^ sh)%Z) (fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le)))
          else keep
      | EAlu ALU_AND e (ELit mk) =>
          (* [comment removed for export] *)
          match highmask_s mk with
          | Some s =>
              if lin_nowrapB bc e then
                let le := lin_of e in
                ((c + k * fst le)%Z,
                 lins_e (- k)%Z (srl_rem e (2 ^ s)) (fold_right (fun t acc => lins_e (k * fst t)%Z (snd t) acc) ts' (snd le)))
              else keep
          | None => keep
          end
      | _ => keep
      end
  end.

Definition fact_nowrapB (bc : bctx) (e : expr) (hi : Z) : bool :=
  let l := lin_of e in
  match lin_range (erangeB bc) (fst l) (snd l) with
  | Some (a, b) => (Z.ltb b two64 && Z.ltb hi (a + two64))%bool
  | None => false
  end.

Definition sum_fact_x2B (bc : bctx) (c2 : Z) (ts2 : list (Z * expr)) (lo hi : Z) : list sfact :=
  if has_srl ts2 then
    let '(c3, ts3) := srl_expandB bc ts2 in
    match ts3 with
    | _ :: _ => if Z.eqb c3 0 then [] else (ts3, ((lo - c2 - c3)%Z, (hi - c2 - c3)%Z)) :: sum_fact_abs ts3 (lo - c2 - c3)%Z (hi - c2 - c3)%Z
    | [] => []
    end
  else [].
Definition sum_fact_xB (bc : bctx) (ts : list (Z * expr)) (lo hi : Z) : list sfact :=
  let '(c2, ts2) := srl_expandB bc ts in
  match ts2 with
  | _ :: _ => if Z.eqb c2 0 then [] else (ts2, ((lo - c2)%Z, (hi - c2)%Z)) :: sum_fact_abs ts2 (lo - c2)%Z (hi - c2)%Z   (* [comment removed for export] *)
                                             ++ sum_fact_x2B bc c2 ts2 lo hi                                                 (* [comment removed for export] *)
  | [] => []
  end.

(* [comment removed for export] *)
Definition sum_fact_gF (ts : list (Z * expr)) (lo hi : Z) : list sfact :=
  let g := ts_gcd ts 0 in
  if (if Z.ltb 1 g then forallb (fun t => Z.eqb (zmodf (fst t) g) 0) ts else false)
  then [(List.map (fun t => (zdivf (fst t) g, snd t)) ts, ((- zdivf (- lo) g)%Z, zdivf hi g))] else [].
Lemma sum_fact_gF_feq : sum_fact_gF = sum_fact_g.
Proof.
  do 3 (apply functional_extensionality; intro). unfold sum_fact_gF, sum_fact_g, ts_divisible, ts_div, zceil_div.
  rewrite zmodf_feq, zdivf_feq. reflexivity.
Qed.
#[export] Hint Rewrite sum_fact_gF_feq : bceq.
Fixpoint sum_factsB (bc : bctx) (kn : list kentry) : list sfact :=
  match kn with
  | [] => []
  | KRange e lo hi :: rest =>
      match e with
      | EVar _ => sum_factsB bc rest
      | _ =>
        match lin_of e with
        | (c, (_ :: _ :: _) as ts) =>
            if fact_nowrapB bc e hi then (ts, ((lo - c)%Z, (hi - c)%Z)) :: sum_fact_xB bc ts (lo - c)%Z (hi - c)%Z
                                          ++ sum_fact_gF ts (lo - c)%Z (hi - c)%Z ++ sum_factsB bc rest   (* [comment removed for export] *)
            else sum_factsB bc rest
        | _ => sum_factsB bc rest
        end
      end
  | _ :: rest => sum_factsB bc rest
  end.


(* [comment removed for export] *)
Lemma bc_fk_mkbc0 : forall fk fs, bc_fk (mkbc0 fk fs) = fk. Proof. reflexivity. Qed.
Lemma bc_ffk_mkbc0 : forall fk fs, bc_ffk (mkbc0 fk fs) = facts_of fk. Proof. reflexivity. Qed.
Lemma find_rangeI_mkbc0 : forall fk fs, find_rangeI (bc_ri (mkbc0 fk fs)) = find_range (facts_of fk).
Proof. intros. apply functional_extensionality. intros e. apply find_rangeI_eq. Qed.
#[export] Hint Rewrite bc_fk_mkbc0 bc_ffk_mkbc0 find_rangeI_mkbc0 : bceq.
Ltac bcfe := repeat (apply functional_extensionality; intros ?).

Lemma erange_fB_eqf0 : forall fk fs fuel, erange_fB fuel (mkbc0 fk fs) = erange_f fuel (facts_of fk).
Proof.
  intros fk fs fuel. induction fuel as [|f IH]; bcfe; [reflexivity|].
  cbn [erange_fB erange_f]. rewrite IH. autorewrite with bceq.
  rewrite ?zshr_feq, ?zshl_feq, ?zmodp_feq, ?zmodf_feq, ?zdivf_feq, ?lit_shamtF_feq, ?pow8n_feq, ?zmod64_feq, ?zdiv64_feq. reflexivity.
Qed.
#[export] Hint Rewrite erange_fB_eqf0 : bceq.

Lemma erange0B_eqf0 : forall fk fs, erange0B (mkbc0 fk fs) = erange0 fk.
Proof. intros. bcfe. unfold erange0B, erange0. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite erange0B_eqf0 : bceq.
Lemma erangeB_eqf0 : forall fk fs, erangeB (mkbc0 fk fs) = erange fk.
Proof. intros. bcfe. unfold erangeB, erange. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite erangeB_eqf0 : bceq.
Lemma base_rangeB_eqf0 : forall fk fs, base_rangeB (mkbc0 fk fs) = base_range fk.
Proof.
  intros. bcfe. unfold base_rangeB, base_range. autorewrite with bceq.
  match goal with |- context [match ?e with _ => _ end] => destruct e end; try reflexivity.
  cbv zeta. rewrite zmod64_eq2. reflexivity.
Qed.
#[export] Hint Rewrite base_rangeB_eqf0 : bceq.
Lemma ealignB_eqf0 : forall fk fs, ealignB (mkbc0 fk fs) = ealign fk.
Proof. intros. bcfe. unfold ealignB, ealign. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite ealignB_eqf0 : bceq.
Lemma lin_nowrapB_eqf0 : forall fk fs, lin_nowrapB (mkbc0 fk fs) = lin_nowrap fk.
Proof. intros. bcfe. unfold lin_nowrapB, lin_nowrap. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_nowrapB_eqf0 : bceq.
Lemma srl_expandB_eqf0 : forall fk fs, srl_expandB (mkbc0 fk fs) = srl_expand fk.
Proof.
  intros fk fs. apply functional_extensionality; intros ts. 
  induction ts as [|[k a] rest IH]; intros; bcfe; [reflexivity|].
  cbn [srl_expandB srl_expand]. rewrite IH. autorewrite with bceq. rewrite ?zmod64_feq. reflexivity.
Qed.
#[export] Hint Rewrite srl_expandB_eqf0 : bceq.
Lemma fact_nowrapB_eqf0 : forall fk fs, fact_nowrapB (mkbc0 fk fs) = fact_nowrap fk.
Proof. intros. bcfe. unfold fact_nowrapB, fact_nowrap. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite fact_nowrapB_eqf0 : bceq.
Lemma sum_fact_x2B_eqf0 : forall fk fs, sum_fact_x2B (mkbc0 fk fs) = sum_fact_x2 fk.
Proof. intros. bcfe. unfold sum_fact_x2B, sum_fact_x2. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite sum_fact_x2B_eqf0 : bceq.
Lemma sum_fact_xB_eqf0 : forall fk fs, sum_fact_xB (mkbc0 fk fs) = sum_fact_x fk.
Proof. intros. bcfe. unfold sum_fact_xB, sum_fact_x. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite sum_fact_xB_eqf0 : bceq.
Lemma sum_factsB_eqf0 : forall fk fs, sum_factsB (mkbc0 fk fs) = sum_facts fk.
Proof.
  intros fk fs. apply functional_extensionality; intros kn. 
  induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [sum_factsB sum_facts]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite sum_factsB_eqf0 : bceq.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mkbc (fk : list kentry) : bctx :=
  let b0 := mkbc0 fk [] in
  let fs := sum_factsB b0 fk in
  BC fk (bc_ffk b0) fs (sf_sortF fs) (bc_ri b0) (bc_kdi b0).
Lemma mkbc_unfold : forall fk, mkbc fk = mkbc0 fk (sum_factsB (mkbc0 fk []) fk).
Proof. reflexivity. Qed.
Lemma bc_fk_mkbc : forall fk, bc_fk (mkbc fk) = fk. Proof. reflexivity. Qed.
Lemma bc_ffk_mkbc : forall fk, bc_ffk (mkbc fk) = facts_of fk. Proof. reflexivity. Qed.
Lemma bc_fs_mkbc : forall fk, bc_fs (mkbc fk) = sum_facts fk fk.
Proof. intros. rewrite mkbc_unfold. cbn [bc_fs mkbc0]. rewrite sum_factsB_eqf0. reflexivity. Qed.
Lemma bc_fss_mkbc : forall fk, bc_fss (mkbc fk) = sf_sort (sum_facts fk fk).
Proof. intros. rewrite mkbc_unfold. cbn [bc_fss mkbc0]. rewrite sum_factsB_eqf0, sf_sortF_feq. reflexivity. Qed.
Lemma find_rangeI_mkbc : forall fk, find_rangeI (bc_ri (mkbc fk)) = find_range (facts_of fk).
Proof. intros. rewrite mkbc_unfold. apply find_rangeI_mkbc0. Qed.
#[export] Hint Rewrite bc_fk_mkbc bc_ffk_mkbc bc_fs_mkbc bc_fss_mkbc find_rangeI_mkbc : bceq.
Lemma erange_fB_eqf : forall fk fuel, erange_fB fuel (mkbc fk) = erange_f fuel (facts_of fk).
Proof. intros. rewrite mkbc_unfold. apply erange_fB_eqf0. Qed.
#[export] Hint Rewrite erange_fB_eqf : bceq.

Lemma erange0B_eqf : forall fk, erange0B (mkbc fk) = erange0 fk.
Proof. intros. rewrite mkbc_unfold. apply erange0B_eqf0. Qed.
#[export] Hint Rewrite erange0B_eqf : bceq.
Lemma erangeB_eqf : forall fk, erangeB (mkbc fk) = erange fk.
Proof. intros. rewrite mkbc_unfold. apply erangeB_eqf0. Qed.
#[export] Hint Rewrite erangeB_eqf : bceq.
Lemma base_rangeB_eqf : forall fk, base_rangeB (mkbc fk) = base_range fk.
Proof. intros. rewrite mkbc_unfold. apply base_rangeB_eqf0. Qed.
#[export] Hint Rewrite base_rangeB_eqf : bceq.
Lemma ealignB_eqf : forall fk, ealignB (mkbc fk) = ealign fk.
Proof. intros. rewrite mkbc_unfold. apply ealignB_eqf0. Qed.
#[export] Hint Rewrite ealignB_eqf : bceq.
Lemma lin_nowrapB_eqf : forall fk, lin_nowrapB (mkbc fk) = lin_nowrap fk.
Proof. intros. rewrite mkbc_unfold. apply lin_nowrapB_eqf0. Qed.
#[export] Hint Rewrite lin_nowrapB_eqf : bceq.
Lemma srl_expandB_eqf : forall fk, srl_expandB (mkbc fk) = srl_expand fk.
Proof. intros. rewrite mkbc_unfold. apply srl_expandB_eqf0. Qed.
#[export] Hint Rewrite srl_expandB_eqf : bceq.
Lemma fact_nowrapB_eqf : forall fk, fact_nowrapB (mkbc fk) = fact_nowrap fk.
Proof. intros. rewrite mkbc_unfold. apply fact_nowrapB_eqf0. Qed.
#[export] Hint Rewrite fact_nowrapB_eqf : bceq.
Lemma sum_fact_xB_eqf : forall fk, sum_fact_xB (mkbc fk) = sum_fact_x fk.
Proof. intros. rewrite mkbc_unfold. apply sum_fact_xB_eqf0. Qed.
#[export] Hint Rewrite sum_fact_xB_eqf : bceq.
Lemma sum_factsB_eqf : forall fk, sum_factsB (mkbc fk) = sum_facts fk.
Proof. intros. rewrite mkbc_unfold. apply sum_factsB_eqf0. Qed.
#[export] Hint Rewrite sum_factsB_eqf : bceq.

Definition lin_test_relB (bc : bctx) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  match bc_fs bc with
  | [] => false
  | fs => lin_test_rel2 (erangeB bc) fs (bc_fss bc) c ts test   (* [comment removed for export] *)
  end.

Definition lin_testB (bc : bctx) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  match lin_range (erangeB bc) c ts with
  | Some (lo, hi) => if test lo hi then true else lin_test_relB bc c ts test
  | None => lin_test_relB bc c ts test
  end.

Definition lin_srangeB (bc : bctx) (e : expr) : option (Z * Z) :=
  let l := lin_of e in
  let j := srl_scale_need (snd l) in
  if (if Z.leb 0 j then Z.leb j 24 else false) then   (* [comment removed for export] *)
    let sc := (2 ^ j)%Z in
    let ts := List.map (fun t => ((sc * fst t)%Z, snd t)) (snd l) in
    let '(c2, t2) := srl_expandB bc ts in
    let '(c3, t3) := (if has_srl t2 then srl_expandB bc t2 else (0%Z, t2)) in
    match lin_range (erangeB bc) (sc * fst l + c2 + c3)%Z t3 with
    | Some (lo', hi') =>
        let lo := (- zshr (- lo') j)%Z in let hi := zshr hi' j in
        if (if Z.leb 0 lo then (if Z.leb lo hi then Z.ltb hi two64 else false) else false) then Some (lo, hi) else None
    | None => None
    end
  else None.

Definition lin_nowrapRB (bc : bctx) (e : expr) : bool :=
  let l := lin_of e in
  let '(c2, t2) := srl_expandB bc (snd l) in            (* [comment removed for export] *)
  if lin_testB bc (fst l + c2)%Z t2 (fun lo hi => (Z.leb 0 lo && Z.ltb hi two64)%bool) then true
  else (* [comment removed for export] *)
    match lin_srangeB bc e with Some _ => true | None => false end.

Definition lin_apart0B (bc : bctx) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  (lin_nowrapRB bc b1 && lin_nowrapRB bc b2 &&
   let l1 := lin_of b1 in let l2 := lin_of b2 in
   lin_testB bc (fst l2 + k2 - fst l1 - k1)%Z (lsub_e (snd l2) (snd l1))
            (fun lo hi => (Z.leb n1 lo || Z.leb hi (- n2))%bool))%bool.

Definition lin_apartB (bc : bctx) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if shares_var b1 b2 then lin_apart0B bc b1 k1 n1 b2 k2 n2 else false.

Definition lin_brangeB (bc : bctx) (e : expr) : option (Z * Z) :=
  let l := lin_of e in
  match bc_fs bc with
  | [] => None
  | fs => lin_brange2 (erangeB bc) fs (bc_fss bc) l   (* [comment removed for export] *)
  end.

Definition xloB (bc : bctx) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erangeB bc e with
         | Some (lo, _) => Some lo
         | None => match lin_brangeB bc e with
                   | Some (lo, _) => Some lo
                   | None => match lin_srangeB bc e with Some (lo, _) => Some lo | None => None end   (* [comment removed for export] *)
                   end
         end
  end.

Definition xhiB (bc : bctx) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erangeB bc e with
         | Some (_, hi) => Some hi
         | None => match lin_brangeB bc e with
                   | Some (_, hi) => Some hi
                   | None => match lin_srangeB bc e with Some (_, hi) => Some hi | None => None end   (* [comment removed for export] *)
                   end
         end
  end.

Fixpoint xt_nowrapB (bc : bctx) (ts : xterms) : bool :=
  match ts with [] => true | (e, _) :: r => lin_nowrapRB bc e && xt_nowrapB bc r end.

Definition srl_scale_need2B (bc : bctx) (ts : list (Z * expr)) : Z :=
  let j := srl_scale_need ts in
  if Z.ltb 0 j then j else
  let '(_, t2) := srl_expandB bc ts in
  if has_srl t2 then Z.max (srl_scale_need t2) (let '(_, t3) := srl_expandB bc t2 in srl_scale_need t3) else 0%Z.

Definition lin_ge0_scaledB (bc : bctx) (c : Z) (ts : list (Z * expr)) : bool :=
  let j := srl_scale_need2B bc ts in
  if (if Z.ltb 0 j then Z.leb j 24 else false) then
    let sc := (2 ^ j)%Z in
    let ts' := List.map (fun t => ((sc * fst t)%Z, snd t)) ts in
    let '(c2, t2) := srl_expandB bc ts' in
    let '(c3, t3) := (if has_srl t2 then srl_expandB bc t2 else (0%Z, t2)) in
    let '(c4, t4) := (if has_srl t3 then srl_expandB bc t3 else (0%Z, t3)) in
    lin_testB bc (sc * c + c2 + c3 + c4)%Z t4 (fun lo _ => Z.leb 0 lo)
  else false.

(* [comment removed for export] *)
Definition lin_refutedB (bc : bctx) (c : Z) (ts : list (Z * expr)) : bool :=
  match lin_range (erangeB bc) c ts with Some (_, hi) => Z.ltb hi 0 | None => false end.
Definition lin_ge0B_pass (bc : bctx) (c0 : Z) (L : list (Z * expr)) : bool :=
   let ok := ge0_testF L c0 in   (* [comment removed for export] *)
   (* [comment removed for export] *)
   (if lin_testB bc c0 L ok then true
    else let '(c2, t2) := srl_expandB bc L in
         if (if same_form c2 t2 L then false else lin_testB bc (c0 + c2)%Z t2 ok) then true
         else (* [comment removed for export] *)
         if (if has_srl t2 then
               let '(c3, t3) := srl_expandB bc t2 in
               lin_testB bc (c0 + c2 + c3)%Z t3 ok
             else false) then true
         else (* [comment removed for export] *)
           lin_ge0_scaledB bc c0 L).
Definition lin_ge0B_core (bc : bctx) (pos neg : xterms) (c0 : Z) (L : list (Z * expr)) : bool :=
  (if xt_nowrapB bc pos then (if xt_nowrapB bc neg then lin_ge0B_pass bc c0 L else false) else false).   (* [comment removed for export] *)
Definition lin_ge0B (bc : bctx) (pos neg : xterms) : bool :=
  let c0 := (xt_const pos - xt_const neg)%Z in
  let L := lsub_e (xt_lin pos) (xt_lin neg) in
  if lin_refutedB bc c0 L then false else lin_ge0B_core bc pos neg c0 L.

Definition xinside0B (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if lin_ge0B bc [(b1, k1)] [(b2, k2)] then lin_ge0B bc [(b2, k2); (n2, 0%Z)] [(b1, k1); (n1, 0%Z)] else false.

(* [comment removed for export] *)
Definition lin_nowrapRLB (bc : bctx) (e : expr) (l : lin) : bool :=
  let '(c2, t2) := srl_expandB bc (snd l) in
  if lin_testB bc (fst l + c2)%Z t2 (fun lo hi => (Z.leb 0 lo && Z.ltb hi two64)%bool) then true
  else match lin_srangeB bc e with Some _ => true | None => false end.
Lemma lin_nowrapRLB_eq : forall bc e, lin_nowrapRLB bc e (lin_of e) = lin_nowrapRB bc e.
Proof. reflexivity. Qed.
Definition xtl1 (l : lin) : list (Z * expr) := fold_right (fun t acc => lins_e (fst t) (snd t) acc) [] (snd l).
Definition xtl2 (l ln : lin) : list (Z * expr) := fold_right (fun t acc => lins_e (fst t) (snd t) acc) (xtl1 ln) (snd l).
Definition xinside0PB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  let l1 := lin_of b1 in let l2 := lin_of b2 in
  let c01 := (fst l1 + k1 + 0 - (fst l2 + k2 + 0))%Z in
  let L1 := lsub_e (xtl1 l1) (xtl1 l2) in
  if lin_refutedB bc c01 L1 then false else
  if lin_nowrapRLB bc b1 l1 then
    if lin_nowrapRLB bc b2 l2 then
      if lin_ge0B_pass bc c01 L1 then
        let ln1 := lin_of n1 in let ln2 := lin_of n2 in
        let c02 := (fst l2 + k2 + (fst ln2 + 0 + 0) - (fst l1 + k1 + (fst ln1 + 0 + 0)))%Z in
        let L2 := lsub_e (xtl2 l2 ln2) (xtl2 l1 ln1) in
        if lin_refutedB bc c02 L2 then false else
        if lin_nowrapRLB bc n2 ln2 then (if lin_nowrapRLB bc n1 ln1 then lin_ge0B_pass bc c02 L2 else false) else false
      else false
    else false
  else false.
Lemma xinside0PB_eq : forall bc b1 k1 n1 b2 k2 n2, xinside0PB bc b1 k1 n1 b2 k2 n2 = xinside0B bc b1 k1 n1 b2 k2 n2.
Proof.
  intros. unfold xinside0PB, xinside0B, lin_ge0B, lin_ge0B_core, xtl2, xtl1. cbv zeta. cbn [xt_const xt_lin xt_nowrapB].
  rewrite !lin_nowrapRLB_eq.
  destruct (lin_refutedB bc _ _); [reflexivity|].
  destruct (lin_nowrapRB bc b1); [|reflexivity]. destruct (lin_nowrapRB bc b2); [|reflexivity]. cbn [andb].
  destruct (lin_ge0B_pass bc _ _); [|reflexivity].
  destruct (lin_refutedB bc _ _); [reflexivity|].
  destruct (lin_nowrapRB bc n2); [|reflexivity]. destruct (lin_nowrapRB bc n1); reflexivity.
Qed.
Lemma xinside0PB_feq : xinside0PB = xinside0B.
Proof. do 7 (apply functional_extensionality; intro). apply xinside0PB_eq. Qed.
#[export] Hint Rewrite xinside0PB_feq : bceq.

Definition xinside_numB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match xloB bc b2, xhiB bc b2 with
  | Some lo2, Some hi2 =>
      if Z.eqb lo2 hi2 then
        match base_rangeB bc b1, xhiB bc n1, xloB bc n2 with
        | Some (lo1, hi1), Some h1, Some l2 => Z.leb (lo2 + k2) (lo1 + k1) && Z.leb (hi1 + k1 + h1) (lo2 + k2 + l2)
        | _, _, _ => false
        end
      else false
  | _, _ => false
  end.

Definition xin_possibleB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match base_rangeB bc b1, base_rangeB bc b2 with
  | Some (lo1, hi1), Some (lo2, hi2) =>
      if Z.ltb (hi1 + k1) (lo2 + k2) then false
      else match n2 with
           | ELit z2 => negb (Z.ltb (hi2 + k2 + zlit64 z2) (lo1 + k1 + match n1 with ELit z1 => zlit64 z1 | _ => 0 end))
           | _ => true
           end
  | _, _ => true
  end.
Definition xinside_numSB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match base_rangeB bc b1, base_rangeB bc b2, xhiB bc n1, xloB bc n2 with
  | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some l2 => Z.leb (hi2 + k2) (lo1 + k1) && Z.leb (hi1 + k1 + h1) (lo2 + k2 + l2)
  | _, _, _, _ => false
  end.
Definition xinsideB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if shares_var b1 b2 then (if xin_possibleB bc b1 k1 n1 b2 k2 n2 then xinside0PB bc b1 k1 n1 b2 k2 n2 else false)
  else if xinside_numSB bc b1 k1 n1 b2 k2 n2 then true
  else if novars b1 then false
  else if xin_possibleB bc b1 k1 n1 b2 k2 n2 then xinside0PB bc b1 k1 n1 b2 k2 n2 else false.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition xin_possible_r (br1 br2 : option (Z * Z)) (k1 : Z) (n1 : expr) (k2 : Z) (n2 : expr) : bool :=
  match br1, br2 with
  | Some (lo1, hi1), Some (lo2, hi2) =>
      if Z.ltb (hi1 + k1) (lo2 + k2) then false
      else match n2 with
           | ELit z2 => negb (Z.ltb (hi2 + k2 + zlit64 z2) (lo1 + k1 + match n1 with ELit z1 => zlit64 z1 | _ => 0 end))
           | _ => true
           end
  | _, _ => true
  end.
Definition xinside_numS_r (bc : bctx) (br1 br2 : option (Z * Z)) (k1 : Z) (n1 : expr) (k2 : Z) (n2 : expr) : bool :=
  match br1, br2, xhiB bc n1, xloB bc n2 with
  | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some l2 => Z.leb (hi2 + k2) (lo1 + k1) && Z.leb (hi1 + k1 + h1) (lo2 + k2 + l2)
  | _, _, _, _ => false
  end.
Definition xinsideRB (bc : bctx) (br1 : option (Z * Z)) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  let br2 := base_rangeB bc b2 in
  if shares_var b1 b2 then (if xin_possible_r br1 br2 k1 n1 k2 n2 then xinside0PB bc b1 k1 n1 b2 k2 n2 else false)
  else if xinside_numS_r bc br1 br2 k1 n1 k2 n2 then true
  else if novars b1 then false
  else if xin_possible_r br1 br2 k1 n1 k2 n2 then xinside0PB bc b1 k1 n1 b2 k2 n2 else false.
Lemma xinsideRB_eq : forall bc b1 k1 n1 b2 k2 n2,
  xinsideRB bc (base_rangeB bc b1) b1 k1 n1 b2 k2 n2 = xinsideB bc b1 k1 n1 b2 k2 n2.
Proof. intros. reflexivity. Qed.
(* [comment removed for export] *)
Definition xinside_numS_rh (bc : bctx) (br1 br2 : option (Z * Z)) (h1 : option Z) (k1 : Z) (k2 : Z) (n2 : expr) : bool :=
  match br1, br2, h1, xloB bc n2 with
  | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some l2 => Z.leb (hi2 + k2) (lo1 + k1) && Z.leb (hi1 + k1 + h1) (lo2 + k2 + l2)
  | _, _, _, _ => false
  end.
Definition xinsideRHB (bc : bctx) (br1 : option (Z * Z)) (h1 : option Z) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  let br2 := base_rangeB bc b2 in
  if shares_var b1 b2 then (if xin_possible_r br1 br2 k1 n1 k2 n2 then xinside0PB bc b1 k1 n1 b2 k2 n2 else false)
  else if xinside_numS_rh bc br1 br2 h1 k1 k2 n2 then true
  else if novars b1 then false
  else if xin_possible_r br1 br2 k1 n1 k2 n2 then xinside0PB bc b1 k1 n1 b2 k2 n2 else false.
Lemma xinsideRHB_eq : forall bc br1 b1 k1 n1 b2 k2 n2,
  xinsideRHB bc br1 (xhiB bc n1) b1 k1 n1 b2 k2 n2 = xinsideRB bc br1 b1 k1 n1 b2 k2 n2.
Proof. intros. reflexivity. Qed.

Definition sub_itv1B (bc : bctx) (b : expr) (k n : Z) (c : saddr) (m : expr) : bool :=
  if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
    match xloB bc m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end
  else false.
Definition sub_itvB (bc : bctx) (b : expr) (k n : Z) (c : saddr) (m : expr) : bool :=
  if sub_itv1B bc b k n c m then true
  else (* [comment removed for export] *)
    if (Z.leb 0 n && Z.ltb n two64)%bool then
      (if side_cand b (a_base c) then xinsideB bc b k (ELit n) (a_base c) (a_off c) m else false)
    else false.

Fixpoint kdisj_apartB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itvB bc b1 k1 n1 c1 m1 then sub_itvB bc b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itvB bc b1 k1 n1 c2 m2 then sub_itvB bc b2 k2 n2 c1 m1 else false) then true
      else kdisj_apartB bc rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apartB bc rest b1 k1 n1 b2 k2 n2
  end.
Fixpoint kdisj_apart1B (bc : bctx) (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itv1B bc b1 k1 n1 c1 m1 then sub_itv1B bc b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itv1B bc b1 k1 n1 c2 m2 then sub_itv1B bc b2 k2 n2 c1 m1 else false) then true
      else kdisj_apart1B bc rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apart1B bc rest b1 k1 n1 b2 k2 n2
  end.
Definition kdisj_apart12B (bc : bctx) (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if kdisj_apart1B bc kn b1 k1 n1 b2 k2 n2 then true else kdisj_apartB bc kn b1 k1 n1 b2 k2 n2.

Definition ranges_apartB (bc : bctx) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if (match base_rangeB bc b1, base_rangeB bc b2 with
      | Some (lo1, hi1), Some (lo2, hi2) =>
          (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
      | _, _ => false
      end) then true
  else if kdisj_apart12B bc (bc_fk bc) b1 k1 n1 b2 k2 n2 then true
  else lin_apartB bc b1 k1 n1 b2 k2 n2.

Definition sub_itv_x1B (bc : bctx) (b : expr) (k : Z) (n : expr) (c : saddr) (m : expr) : bool :=
  if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
    match xhiB bc n, xloB bc m with
    | Some nh, Some ml => if Z.leb 0 nh then Z.leb (k + nh) (a_off c + ml) else false
    | _, _ => false
    end
  else false.
Definition sub_itv_xB (bc : bctx) (b : expr) (k : Z) (n : expr) (c : saddr) (m : expr) : bool :=
  if sub_itv_x1B bc b k n c m then true
  else if side_cand b (a_base c) then xinsideB bc b k n (a_base c) (a_off c) m else false.

Fixpoint kdisj_apart_xB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itv_xB bc b1 k1 n1 c1 m1 then sub_itv_xB bc b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itv_xB bc b1 k1 n1 c2 m2 then sub_itv_xB bc b2 k2 n2 c1 m1 else false) then true
      else kdisj_apart_xB bc rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apart_xB bc rest b1 k1 n1 b2 k2 n2
  end.
Fixpoint kdisj_apart_x1B (bc : bctx) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itv_x1B bc b1 k1 n1 c1 m1 then sub_itv_x1B bc b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itv_x1B bc b1 k1 n1 c2 m2 then sub_itv_x1B bc b2 k2 n2 c1 m1 else false) then true
      else kdisj_apart_x1B bc rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apart_x1B bc rest b1 k1 n1 b2 k2 n2
  end.
Definition kdisj_apart_x12B (bc : bctx) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if kdisj_apart_x1B bc kn b1 k1 n1 b2 k2 n2 then true else kdisj_apart_xB bc kn b1 k1 n1 b2 k2 n2.

Definition end_hiB (bc : bctx) (b : expr) (k : Z) (n : expr) (lo1 hi1 h1 : Z) : option Z :=
  match n with
  | ELit _ => None
  | _ => if (if Z.leb 0 (lo1 + k) then Z.ltb (hi1 + k + h1) two64 else false)
         then let e := mkAlu ALU_ADD (mkAlu ALU_ADD b (ELit k)) n in
              match find_rangeI (bc_ri bc) e with
              | Some (_, ehi) => Some ehi
              | None => match lin_brangeB bc e with Some (_, ehi) => Some ehi | None => None end   (* [comment removed for export] *)
              end
         else None
  end.

Definition ranges_apart_xB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 => ranges_apartB bc b1 k1 (zlit64 z1) b2 k2 (zlit64 z2)
  | _, _ =>
    if (match base_rangeB bc b1, base_rangeB bc b2, xhiB bc n1, xhiB bc n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else (* [comment removed for export] *)
            if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if kdisj_apart_x12B bc (bc_fk bc) b1 k1 n1 b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.

(* [comment removed for export] *)
Definition memo_key (c : saddr) (m : expr) (c' : saddr) (m' : expr) : bool :=
  if Z.eqb (a_off c) (a_off c') then if expr_eqb (a_base c) (a_base c') then expr_eqb m m' else false else false.
Fixpoint memo_find (c : saddr) (m : expr) (memo : list (saddr * expr * bool)) : option bool :=
  match memo with
  | [] => None
  | (c', m', r) :: rest => if memo_key c m c' m' then Some r else memo_find c m rest
  end.
Definition test_m (f : saddr -> expr -> bool) (c : saddr) (m : expr) (memo : list (saddr * expr * bool))
  : bool * list (saddr * expr * bool) :=
  match memo_find c m memo with
  | Some r => (r, memo)
  | None => let r := f c m in (r, (c, m, r) :: memo)
  end.
Fixpoint disj_sides_m (f : saddr -> expr -> bool) (kn : list kentry) (memo : list (saddr * expr * bool))
  : list (saddr * expr) * list (saddr * expr * bool) :=
  match kn with
  | [] => ([], memo)
  | KDisj c1 m1 c2 m2 :: rest =>
      let '(r, memo1) := disj_sides_m f rest memo in
      let '(t2, memo2) := test_m f c2 m2 memo1 in
      let '(t1, memo3) := test_m f c1 m1 memo2 in
      (if t1 then (c2, m2) :: (if t2 then (c1, m1) :: r else r) else (if t2 then (c1, m1) :: r else r), memo3)
  | _ :: rest => disj_sides_m f rest memo
  end.
Fixpoint disj_sides_ref (f : saddr -> expr -> bool) (kn : list kentry) : list (saddr * expr) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sides_ref f rest in
      let r1 := if f c2 m2 then (c1, m1) :: r else r in
      if f c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sides_ref f rest
  end.
Definition memo_ok (f : saddr -> expr -> bool) (memo : list (saddr * expr * bool)) : Prop :=
  forall c m r, memo_find c m memo = Some r -> r = f c m.
Lemma memo_ok_nil : forall f, memo_ok f [].
Proof. intros f c m r H. discriminate H. Qed.
Lemma memo_key_true : forall c m c' m', memo_key c m c' m' = true -> c = c' /\ m = m'.
Proof.
  intros [b o] m [b' o'] m'. unfold memo_key. cbn [a_base a_off].
  destruct (Z.eqb_spec o o') as [->|]; [|discriminate].
  destruct (expr_eqb b b') eqn:Eb; [|discriminate]. intros Em.
  apply p_expr_eqb_eq in Eb. apply p_expr_eqb_eq in Em. subst. split; reflexivity.
Qed.
Lemma test_m_ok : forall f c m memo r memo', memo_ok f memo -> test_m f c m memo = (r, memo') -> r = f c m /\ memo_ok f memo'.
Proof.
  intros f c m memo r memo' Hm Ht. unfold test_m in Ht.
  destruct (memo_find c m memo) as [r0|] eqn:Hf.
  - injection Ht as <- <-. split; [exact (Hm _ _ _ Hf) | exact Hm].
  - injection Ht as <- <-. split; [reflexivity|].
    intros c' m' r' H. cbn [memo_find] in H.
    destruct (memo_key c' m' c m) eqn:E; [|exact (Hm _ _ _ H)].
    injection H as <-. apply memo_key_true in E as [-> ->]. reflexivity.
Qed.
Lemma disj_sides_m_ok : forall f kn memo, memo_ok f memo ->
  fst (disj_sides_m f kn memo) = disj_sides_ref f kn /\ memo_ok f (snd (disj_sides_m f kn memo)).
Proof.
  intros f kn. induction kn as [|K rest IH]; intros memo Hm; [split; [reflexivity | exact Hm]|].
  destruct K as [| | | | | | |c1 m1 c2 m2| |]; cbn [disj_sides_m disj_sides_ref]; try exact (IH memo Hm).
  destruct (disj_sides_m f rest memo) as [r memo1] eqn:H1. destruct (IH memo Hm) as [A B]. rewrite H1 in A, B. cbn [fst snd] in A, B.
  destruct (test_m f c2 m2 memo1) as [t2 memo2] eqn:H2. destruct (test_m_ok f c2 m2 memo1 t2 memo2 B H2) as [E2 B2].
  destruct (test_m f c1 m1 memo2) as [t1 memo3] eqn:H3. destruct (test_m_ok f c1 m1 memo2 t1 memo3 B2 H3) as [E1 B3].
  cbn [fst snd]. split; [|exact B3]. subst t1 t2 r. reflexivity.
Qed.

(* [comment removed for export] *)
Definition tsides1 (t : kentry * positive * positive) : list (positive * saddr * expr) :=
  match t with (KDisj c1 m1 c2 m2, i1, i2) => [(i1, c1, m1); (i2, c2, m2)] | _ => [] end.
Definition tsides (U : list (kentry * positive * positive)) : list (positive * saddr * expr) := flat_map tsides1 U.
Definition kdi_ok (U : list (kentry * positive * positive)) : Prop :=
  forall i c m c' m', In (i, c, m) (tsides U) -> In (i, c', m') (tsides U) -> c = c' /\ m = m'.
Definition memo_ok_i (f : saddr -> expr -> bool) (U : list (kentry * positive * positive)) (memo : ptree bool) : Prop :=
  forall i r, pt_get memo i = Some r -> forall c m, In (i, c, m) (tsides U) -> r = f c m.
Lemma memo_ok_i_nil : forall f U, memo_ok_i f U PTLeaf.
Proof. intros f U i r H. destruct i; discriminate H. Qed.
Definition test_i (f : saddr -> expr -> bool) (c : saddr) (m : expr) (i : positive) (memo : ptree bool) : bool * ptree bool :=
  match pt_get memo i with
  | Some r => (r, memo)
  | None => let r := f c m in (r, pt_set i r memo)
  end.
Lemma test_i_ok : forall f U c m i memo r memo', kdi_ok U -> In (i, c, m) (tsides U) -> memo_ok_i f U memo ->
  test_i f c m i memo = (r, memo') -> r = f c m /\ memo_ok_i f U memo'.
Proof.
  intros f U c m i memo r memo' HU Hin Hm Ht. unfold test_i in Ht.
  destruct (pt_get memo i) as [r0|] eqn:Hg.
  - injection Ht as <- <-. split; [exact (Hm _ _ Hg _ _ Hin) | exact Hm].
  - injection Ht as <- <-. split; [reflexivity|].
    intros j r' Hj c' m' Hin'. destruct (Pos.eq_dec j i) as [->|NE].
    + rewrite pt_gss in Hj. injection Hj as <-. destruct (HU _ _ _ _ _ Hin Hin') as [<- <-]. reflexivity.
    + rewrite pt_gso in Hj by exact NE. exact (Hm _ _ Hj _ _ Hin').
Qed.
Fixpoint disj_sides_i (f : saddr -> expr -> bool) (l : list (kentry * positive * positive)) (memo : ptree bool)
  : list (saddr * expr) * ptree bool :=
  match l with
  | [] => ([], memo)
  | (KDisj c1 m1 c2 m2, i1, i2) :: rest =>
      let '(r, memo1) := disj_sides_i f rest memo in
      let '(t2, memo2) := test_i f c2 m2 i2 memo1 in
      let '(t1, memo3) := test_i f c1 m1 i1 memo2 in
      (if t1 then (c2, m2) :: (if t2 then (c1, m1) :: r else r) else (if t2 then (c1, m1) :: r else r), memo3)
  | _ :: rest => disj_sides_i f rest memo
  end.
Definition fst3 (t : kentry * positive * positive) : kentry := fst (fst t).
Lemma tsides_incl : forall U l t, incl l U -> In t (tsides l) -> In t (tsides U).
Proof. intros U l t H Hi. unfold tsides in *. apply in_flat_map in Hi as (x & Hx & Ht). apply in_flat_map. exists x. split; [apply H; exact Hx | exact Ht]. Qed.
Lemma tsides_in1 : forall U l c1 m1 c2 m2 i1 i2, incl ((KDisj c1 m1 c2 m2, i1, i2) :: l) U -> In (i1, c1, m1) (tsides U).
Proof. intros U l c1 m1 c2 m2 i1 i2 H. apply (tsides_incl U [(KDisj c1 m1 c2 m2, i1, i2)]); [intros x [<-|[]]; apply H; left; reflexivity | cbn; left; reflexivity]. Qed.
Lemma tsides_in2 : forall U l c1 m1 c2 m2 i1 i2, incl ((KDisj c1 m1 c2 m2, i1, i2) :: l) U -> In (i2, c2, m2) (tsides U).
Proof. intros U l c1 m1 c2 m2 i1 i2 H. apply (tsides_incl U [(KDisj c1 m1 c2 m2, i1, i2)]); [intros x [<-|[]]; apply H; left; reflexivity | cbn; right; left; reflexivity]. Qed.
Lemma disj_sides_i_ok : forall f U l memo, kdi_ok U -> incl l U -> memo_ok_i f U memo ->
  fst (disj_sides_i f l memo) = disj_sides_ref f (map fst3 l) /\ memo_ok_i f U (snd (disj_sides_i f l memo)).
Proof.
  intros f U l. induction l as [|[[K i1] i2] rest IH]; intros memo HU Hl Hm; [split; [reflexivity | exact Hm]|].
  assert (Hr : incl rest U) by (intros x Hx; apply Hl; right; exact Hx).
  destruct K as [| | | | | | |c1 m1 c2 m2| |]; cbn [disj_sides_i disj_sides_ref map fst3 fst]; try exact (IH memo HU Hr Hm).
  destruct (disj_sides_i f rest memo) as [r memo1] eqn:H1. destruct (IH memo HU Hr Hm) as [A B]. rewrite H1 in A, B. cbn [fst snd] in A, B.
  destruct (test_i f c2 m2 i2 memo1) as [t2 memo2] eqn:H2. destruct (test_i_ok f U c2 m2 i2 memo1 t2 memo2 HU (tsides_in2 _ _ _ _ _ _ _ _ Hl) B H2) as [E2 C2].
  destruct (test_i f c1 m1 i1 memo2) as [t1 memo3] eqn:H3. destruct (test_i_ok f U c1 m1 i1 memo2 t1 memo3 HU (tsides_in1 _ _ _ _ _ _ _ _ Hl) C2 H3) as [E1 C3].
  cbn [fst snd]. split; [|exact C3]. subst t1 t2 r. reflexivity.
Qed.


Definition isKD (K : kentry) : bool := match K with KDisj _ _ _ _ => true | _ => false end.
Lemma disj_sides_ref_isKD : forall f kn, disj_sides_ref f (List.filter isKD kn) = disj_sides_ref f kn.
Proof.
  intros f kn. induction kn as [|K rest IH]; [reflexivity|].
  destruct K; cbn [List.filter isKD disj_sides_ref]; rewrite ?IH; reflexivity.
Qed.
Lemma mk_kdi0_map : forall fk tab nx, map fst3 (fst (fst (mk_kdi0 fk tab nx))) = List.filter isKD fk.
Proof.
  intros fk. induction fk as [|K rest IH]; intros tab nx; [reflexivity|].
  destruct K as [| | | | | | |c1 m1 c2 m2| |]; cbn [mk_kdi0 List.filter isKD]; try apply IH.
  destruct (mk_kdi0 rest tab nx) as [[r tab1] nx1] eqn:E. specialize (IH tab nx). rewrite E in IH. cbn [fst] in IH.
  destruct (sd_internT tab1 nx1 c2 m2) as [[i2 tab2] nx2]. destruct (sd_internT tab2 nx2 c1 m1) as [[i1 tab3] nx3].
  cbn [fst map fst3]. rewrite IH. reflexivity.
Qed.
Lemma mk_kdi_map : forall fk, map fst3 (mk_kdi fk) = List.filter isKD fk.
Proof. intros. apply mk_kdi0_map. Qed.
Definition tmem (tab : ptree (list (saddr * expr * positive))) (c : saddr) (m : expr) (i : positive) : Prop :=
  exists k b, pt_get tab k = Some b /\ In (c, m, i) b.
Definition tinv (tab : ptree (list (saddr * expr * positive))) (nx : positive) : Prop :=
  (forall c m i, tmem tab c m i -> (i < nx)%positive) /\
  (forall c m c' m' i, tmem tab c m i -> tmem tab c' m' i -> c = c' /\ m = m').
Lemma sd_find_in : forall tab c m i, sd_find tab c m = Some i -> In (c, m, i) tab.
Proof.
  intros tab c m i. induction tab as [|[[c' m'] j] r IH]; cbn [sd_find]; [discriminate|].
  destruct (skey c m c' m') eqn:E.
  - intros H. injection H as <-. unfold skey in E.
    destruct (Z.eqb (a_off c) (a_off c')) eqn:Eo; [|discriminate].
    destruct (expr_eqb (a_base c) (a_base c')) eqn:Eb; [|discriminate].
    apply p_expr_eqb_eq in E. apply p_expr_eqb_eq in Eb. apply Z.eqb_eq in Eo. subst m'.
    destruct c as [cb co], c' as [cb' co']. cbn in *. subst. left. reflexivity.
  - intros H. right. apply IH. exact H.
Qed.
Lemma sd_internT_ok : forall tab nx c m i tab' nx', tinv tab nx -> sd_internT tab nx c m = (i, tab', nx') ->
  tinv tab' nx' /\ tmem tab' c m i /\ (forall c0 m0 i0, tmem tab c0 m0 i0 -> tmem tab' c0 m0 i0).
Proof.
  intros tab nx c m i tab' nx' [Hlt Hu] H. unfold sd_internT, sd_findT in H.
  destruct (pt_get tab (sd_key c)) as [b|] eqn:Hb.
  - destruct (sd_find b c m) as [j|] eqn:Hf.
    + injection H as <- <- <-. split; [split; assumption|]. split; [|intros; assumption].
      exists (sd_key c), b. split; [exact Hb | apply sd_find_in; exact Hf].
    + injection H as <- <- <-.
      assert (MEM : forall c0 m0 i0, tmem (pt_set (sd_key c) ((c, m, nx) :: b) tab) c0 m0 i0 -> (c0, m0, i0) = (c, m, nx) \/ tmem tab c0 m0 i0).
      { intros c0 m0 i0 (k & b0 & Hk & Hin). destruct (Pos.eq_dec k (sd_key c)) as [->|NE].
        - rewrite pt_gss in Hk. injection Hk as <-. destruct Hin as [Heq|Hin]; [left; symmetry; exact Heq | right; exists (sd_key c), b; split; assumption].
        - rewrite pt_gso in Hk by exact NE. right. exists k, b0. split; assumption. }
      assert (INC : forall c0 m0 i0, tmem tab c0 m0 i0 -> tmem (pt_set (sd_key c) ((c, m, nx) :: b) tab) c0 m0 i0).
      { intros c0 m0 i0 (k & b0 & Hk & Hin). destruct (Pos.eq_dec k (sd_key c)) as [->|NE].
        - rewrite Hb in Hk. injection Hk as <-. exists (sd_key c), ((c, m, nx) :: b). split; [apply pt_gss | right; exact Hin].
        - exists k, b0. split; [rewrite pt_gso by exact NE; exact Hk | exact Hin]. }
      split; [split|split; [exists (sd_key c), ((c, m, nx) :: b); split; [apply pt_gss | left; reflexivity] | exact INC]].
      * intros c0 m0 i0 Hm. destruct (MEM _ _ _ Hm) as [Heq|Hm']; [injection Heq as <- <- <-; lia | specialize (Hlt _ _ _ Hm'); lia].
      * intros c1 m1 c2 m2 i' H1 H2. destruct (MEM _ _ _ H1) as [E1|M1]; destruct (MEM _ _ _ H2) as [E2|M2].
        -- injection E1 as <- <- <-. injection E2 as <- <-. split; reflexivity.
        -- injection E1 as <- <- <-. specialize (Hlt _ _ _ M2). lia.
        -- injection E2 as <- <- <-. specialize (Hlt _ _ _ M1). lia.
        -- exact (Hu _ _ _ _ _ M1 M2).
  - injection H as <- <- <-.
    assert (MEM : forall c0 m0 i0, tmem (pt_set (sd_key c) [(c, m, nx)] tab) c0 m0 i0 -> (c0, m0, i0) = (c, m, nx) \/ tmem tab c0 m0 i0).
    { intros c0 m0 i0 (k & b0 & Hk & Hin). destruct (Pos.eq_dec k (sd_key c)) as [->|NE].
      - rewrite pt_gss in Hk. injection Hk as <-. destruct Hin as [Heq|[]]. left; symmetry; exact Heq.
      - rewrite pt_gso in Hk by exact NE. right. exists k, b0. split; assumption. }
    assert (INC : forall c0 m0 i0, tmem tab c0 m0 i0 -> tmem (pt_set (sd_key c) [(c, m, nx)] tab) c0 m0 i0).
    { intros c0 m0 i0 (k & b0 & Hk & Hin). destruct (Pos.eq_dec k (sd_key c)) as [->|NE].
      - rewrite Hb in Hk. discriminate Hk.
      - exists k, b0. split; [rewrite pt_gso by exact NE; exact Hk | exact Hin]. }
    split; [split|split; [exists (sd_key c), [(c, m, nx)]; split; [apply pt_gss | left; reflexivity] | exact INC]].
    * intros c0 m0 i0 Hm. destruct (MEM _ _ _ Hm) as [Heq|Hm']; [injection Heq as <- <- <-; lia | specialize (Hlt _ _ _ Hm'); lia].
    * intros c1 m1 c2 m2 i' H1 H2. destruct (MEM _ _ _ H1) as [E1|M1]; destruct (MEM _ _ _ H2) as [E2|M2].
      -- injection E1 as <- <- <-. injection E2 as <- <-. split; reflexivity.
      -- injection E1 as <- <- <-. specialize (Hlt _ _ _ M2). lia.
      -- injection E2 as <- <- <-. specialize (Hlt _ _ _ M1). lia.
      -- exact (Hu _ _ _ _ _ M1 M2).
Qed.
Lemma mk_kdi0_ok : forall fk tab nx r tab' nx', tinv tab nx -> mk_kdi0 fk tab nx = (r, tab', nx') ->
  tinv tab' nx' /\ (forall c m i, tmem tab c m i -> tmem tab' c m i) /\ (forall i c m, In (i, c, m) (tsides r) -> tmem tab' c m i).
Proof.
  intros fk. induction fk as [|K rest IH]; intros tab nx r tab' nx' HT H.
  - cbn in H. injection H as <- <- <-. split; [exact HT|]. split; [intros; assumption | intros i c m []].
  - destruct K as [| | | | | | |c1 m1 c2 m2| |]; cbn [mk_kdi0] in H; try exact (IH _ _ _ _ _ HT H).
    destruct (mk_kdi0 rest tab nx) as [[r0 tab1] nx1] eqn:E0.
    destruct (sd_internT tab1 nx1 c2 m2) as [[i2 tab2] nx2] eqn:E2.
    destruct (sd_internT tab2 nx2 c1 m1) as [[i1 tab3] nx3] eqn:E3.
    injection H as <- <- <-.
    destruct (IH _ _ _ _ _ HT E0) as (T1 & I1 & S1).
    destruct (sd_internT_ok _ _ _ _ _ _ _ T1 E2) as (T2 & In2 & I2).
    destruct (sd_internT_ok _ _ _ _ _ _ _ T2 E3) as (T3 & In3 & I3).
    split; [exact T3|]. split; [intros c m i Hx; apply I3, I2, I1; exact Hx|].
    intros i c m Hin. cbn [tsides flat_map tsides1] in Hin. rewrite <- app_comm_cons in Hin.
    destruct Hin as [Heq|[Heq|Hin]].
    + injection Heq as <- <- <-. exact In3.
    + injection Heq as <- <- <-. apply I3. exact In2.
    + apply I3, I2. apply S1. exact Hin.
Qed.
Lemma mk_kdi_ok : forall fk, kdi_ok (mk_kdi fk).
Proof.
  intros fk. unfold mk_kdi. destruct (mk_kdi0 fk PTLeaf xH) as [[r tab] nx] eqn:E. cbn [fst].
  assert (T0 : tinv PTLeaf xH).
  { split; [intros c m i (k & b & Hk & _) | intros c m c' m' i (k & b & Hk & _)]; rewrite pt_get_leaf in Hk; discriminate Hk. }
  destruct (mk_kdi0_ok _ _ _ _ _ _ T0 E) as ([_ Hu] & _ & S).
  intros i c m c' m' H1 H2. exact (Hu _ _ _ _ _ (S _ _ _ H1) (S _ _ _ H2)).
Qed.

Definition disj_sidesIB (bc : bctx) (b1 : expr) (k1 n1 : Z) : list (saddr * expr) :=
  fst (disj_sides_i (fun c m => sub_itvB bc b1 k1 n1 c m) (bc_kdi bc) PTLeaf).
Definition disj_sides_xIB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) : list (saddr * expr) :=
  fst (disj_sides_i (fun c m => sub_itv_xB bc b1 k1 n1 c m) (bc_kdi bc) PTLeaf).

(* [comment removed for export] *)
Definition sub_itvRB (bc : bctx) (br1 : option (Z * Z)) (b : expr) (k n : Z) (c : saddr) (m : expr) : bool :=
  if sub_itv1B bc b k n c m then true
  else
    if (Z.leb 0 n && Z.ltb n two64)%bool then
      (if side_cand b (a_base c) then xinsideRB bc br1 b k (ELit n) (a_base c) (a_off c) m else false)
    else false.
Definition sub_itv_xRB (bc : bctx) (br1 : option (Z * Z)) (b : expr) (k : Z) (n : expr) (c : saddr) (m : expr) : bool :=
  if sub_itv_x1B bc b k n c m then true
  else if side_cand b (a_base c) then xinsideRB bc br1 b k n (a_base c) (a_off c) m else false.
Definition disj_sidesRB (bc : bctx) (br1 : option (Z * Z)) (b1 : expr) (k1 n1 : Z) : list (saddr * expr) :=
  fst (disj_sides_i (fun c m => sub_itvRB bc br1 b1 k1 n1 c m) (bc_kdi bc) PTLeaf).
Definition disj_sides_xRB (bc : bctx) (br1 : option (Z * Z)) (b1 : expr) (k1 : Z) (n1 : expr) : list (saddr * expr) :=
  fst (disj_sides_i (fun c m => sub_itv_xRB bc br1 b1 k1 n1 c m) (bc_kdi bc) PTLeaf).
Lemma disj_sidesRB_eq : forall bc b1 k1 n1, disj_sidesRB bc (base_rangeB bc b1) b1 k1 n1 = disj_sidesIB bc b1 k1 n1.
Proof. reflexivity. Qed.
Lemma disj_sides_xRB_eq : forall bc b1 k1 n1, disj_sides_xRB bc (base_rangeB bc b1) b1 k1 n1 = disj_sides_xIB bc b1 k1 n1.
Proof. reflexivity. Qed.

Definition disj_sidesB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 n1 : Z) : list (saddr * expr) :=
  fst (disj_sides_m (fun c m => sub_itvB bc b1 k1 n1 c m) kn []).
Definition disj_sides_xB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) : list (saddr * expr) :=
  fst (disj_sides_m (fun c m => sub_itv_xB bc b1 k1 n1 c m) kn []).
Lemma disj_sidesB_ref : forall bc kn b1 k1 n1,
  disj_sidesB bc kn b1 k1 n1 = disj_sides_ref (fun c m => sub_itvB bc b1 k1 n1 c m) kn.
Proof. intros. unfold disj_sidesB. exact (proj1 (disj_sides_m_ok _ kn [] (memo_ok_nil _))). Qed.
Lemma disj_sides_xB_ref : forall bc kn b1 k1 n1,
  disj_sides_xB bc kn b1 k1 n1 = disj_sides_ref (fun c m => sub_itv_xB bc b1 k1 n1 c m) kn.
Proof. intros. unfold disj_sides_xB. exact (proj1 (disj_sides_m_ok _ kn [] (memo_ok_nil _))). Qed.
Lemma disj_sidesIB_eq : forall bc b1 k1 n1, bc_kdi bc = mk_kdi (bc_fk bc) ->
  disj_sidesIB bc b1 k1 n1 = disj_sidesB bc (bc_fk bc) b1 k1 n1.
Proof.
  intros bc b1 k1 n1 Hw. unfold disj_sidesIB. rewrite Hw, disj_sidesB_ref.
  rewrite (proj1 (disj_sides_i_ok _ (mk_kdi (bc_fk bc)) _ PTLeaf (mk_kdi_ok _) (incl_refl _) (memo_ok_i_nil _ _))).
  rewrite mk_kdi_map, disj_sides_ref_isKD. reflexivity.
Qed.
Lemma disj_sides_xIB_eq : forall bc b1 k1 n1, bc_kdi bc = mk_kdi (bc_fk bc) ->
  disj_sides_xIB bc b1 k1 n1 = disj_sides_xB bc (bc_fk bc) b1 k1 n1.
Proof.
  intros bc b1 k1 n1 Hw. unfold disj_sides_xIB. rewrite Hw, disj_sides_xB_ref.
  rewrite (proj1 (disj_sides_i_ok _ (mk_kdi (bc_fk bc)) _ PTLeaf (mk_kdi_ok _) (incl_refl _) (memo_ok_i_nil _ _))).
  rewrite mk_kdi_map, disj_sides_ref_isKD. reflexivity.
Qed.

Fixpoint in_sidesB0 (bc : bctx) (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itvB bc b2 k2 n2 c m then true else in_sidesB0 bc r b2 k2 n2
  end.

Fixpoint in_sides_xB0 (bc : bctx) (D : list (saddr * expr)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itv_xB bc b2 k2 n2 c m then true else in_sides_xB0 bc r b2 k2 n2
  end.
(* [comment removed for export] *)
Fixpoint in_sides1B (bc : bctx) (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itv1B bc b2 k2 n2 c m then true else in_sides1B bc r b2 k2 n2
  end.
Fixpoint in_sides_x1B (bc : bctx) (D : list (saddr * expr)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itv_x1B bc b2 k2 n2 c m then true else in_sides_x1B bc r b2 k2 n2
  end.
Definition in_sidesB (bc : bctx) (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool :=
  if in_sides1B bc D b2 k2 n2 then true else in_sidesB0 bc D b2 k2 n2.
Definition in_sides_xB (bc : bctx) (D : list (saddr * expr)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if in_sides_x1B bc D b2 k2 n2 then true else in_sides_xB0 bc D b2 k2 n2.
Lemma in_sidesB_B0 : forall bc D b2 k2 n2, in_sidesB bc D b2 k2 n2 = in_sidesB0 bc D b2 k2 n2.
Proof.
  intros. unfold in_sidesB. destruct (in_sides1B bc D b2 k2 n2) eqn:E; [|reflexivity]. symmetry.
  induction D as [|[c m] r IH]; [discriminate|]. cbn [in_sides1B in_sidesB0] in *.
  unfold sub_itvB. destruct (sub_itv1B bc b2 k2 n2 c m); [reflexivity|].
  rewrite (IH E). destruct (if (Z.leb 0 n2 && Z.ltb n2 two64)%bool then if side_cand b2 (a_base c) then xinsideB bc b2 k2 (ELit n2) (a_base c) (a_off c) m else false else false); reflexivity.
Qed.
Lemma in_sides_xB_B0 : forall bc D b2 k2 n2, in_sides_xB bc D b2 k2 n2 = in_sides_xB0 bc D b2 k2 n2.
Proof.
  intros. unfold in_sides_xB. destruct (in_sides_x1B bc D b2 k2 n2) eqn:E; [|reflexivity]. symmetry.
  induction D as [|[c m] r IH]; [discriminate|]. cbn [in_sides_x1B in_sides_xB0] in *.
  unfold sub_itv_xB. destruct (sub_itv_x1B bc b2 k2 n2 c m); [reflexivity|].
  rewrite (IH E). destruct (if side_cand b2 (a_base c) then xinsideB bc b2 k2 n2 (a_base c) (a_off c) m else false); reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint in_sidesR0 (bc : bctx) (br2 : option (Z * Z)) (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itvRB bc br2 b2 k2 n2 c m then true else in_sidesR0 bc br2 r b2 k2 n2
  end.
Fixpoint in_sides_xR0 (bc : bctx) (br2 : option (Z * Z)) (D : list (saddr * expr)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itv_xRB bc br2 b2 k2 n2 c m then true else in_sides_xR0 bc br2 r b2 k2 n2
  end.
Definition in_sidesHB (bc : bctx) (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool :=
  if in_sides1B bc D b2 k2 n2 then true
  else match D with [] => false | _ :: _ => in_sidesR0 bc (base_rangeB bc b2) D b2 k2 n2 end.
Definition sub_itv_xRHB (bc : bctx) (br1 : option (Z * Z)) (h1 : option Z) (b : expr) (k : Z) (n : expr) (c : saddr) (m : expr) : bool :=
  if sub_itv_x1B bc b k n c m then true
  else if side_cand b (a_base c) then xinsideRHB bc br1 h1 b k n (a_base c) (a_off c) m else false.
Fixpoint in_sides_xRH0 (bc : bctx) (br2 : option (Z * Z)) (h2 : option Z) (D : list (saddr * expr)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itv_xRHB bc br2 h2 b2 k2 n2 c m then true else in_sides_xRH0 bc br2 h2 r b2 k2 n2
  end.
Lemma in_sides_xRH0_eq : forall bc br2 D b2 k2 n2, in_sides_xRH0 bc br2 (xhiB bc n2) D b2 k2 n2 = in_sides_xR0 bc br2 D b2 k2 n2.
Proof. intros bc br2 D b2 k2 n2. induction D as [|[c m] r IH]; [reflexivity|]. cbn [in_sides_xRH0 in_sides_xR0]. rewrite IH. reflexivity. Qed.
Definition in_sides_xHB (bc : bctx) (D : list (saddr * expr)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if in_sides_x1B bc D b2 k2 n2 then true
  else match D with [] => false | _ :: _ => in_sides_xRH0 bc (base_rangeB bc b2) (xhiB bc n2) D b2 k2 n2 end.   (* [comment removed for export] *)
Lemma in_sidesR0_eq : forall bc D b2 k2 n2, in_sidesR0 bc (base_rangeB bc b2) D b2 k2 n2 = in_sidesB0 bc D b2 k2 n2.
Proof. intros bc D b2 k2 n2. induction D as [|[c m] r IH]; [reflexivity|]. cbn [in_sidesR0 in_sidesB0]. rewrite IH. reflexivity. Qed.
Lemma in_sides_xR0_eq : forall bc D b2 k2 n2, in_sides_xR0 bc (base_rangeB bc b2) D b2 k2 n2 = in_sides_xB0 bc D b2 k2 n2.
Proof. intros bc D b2 k2 n2. induction D as [|[c m] r IH]; [reflexivity|]. cbn [in_sides_xR0 in_sides_xB0]. rewrite IH. reflexivity. Qed.
Lemma in_sidesHB_feq : in_sidesHB = in_sidesB.
Proof.
  do 5 (apply functional_extensionality; intro). unfold in_sidesHB, in_sidesB.
  destruct (in_sides1B _ _ _ _ _); [reflexivity|]. rewrite in_sidesR0_eq. destruct x0; reflexivity.
Qed.
Lemma in_sides_xHB_feq : in_sides_xHB = in_sides_xB.
Proof.
  do 5 (apply functional_extensionality; intro). unfold in_sides_xHB, in_sides_xB.
  destruct (in_sides_x1B _ _ _ _ _); [reflexivity|]. rewrite in_sides_xRH0_eq, in_sides_xR0_eq. destruct x0; reflexivity.
Qed.
#[export] Hint Rewrite in_sidesHB_feq in_sides_xHB_feq : bceq.

(* [comment removed for export] *)
Definition sub_itvLB (b : expr) (k n : Z) (c : saddr) (m : expr) : bool :=
  match b, a_base c, m with
  | ELit zb, ELit zc, ELit zm =>
      if Z.leb (zmod64 zc + a_off c) (zmod64 zb + k) then Z.leb (zmod64 zb + k + n) (zmod64 zc + a_off c + zlit64 zm) else false
  | _, _, _ => false
  end.
Fixpoint in_sidesLB (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itvLB b2 k2 n2 c m then true else in_sidesLB r b2 k2 n2
  end.
Lemma zlit64_small : forall z, (0 <= z < two64)%Z -> zlit64 z = z.
Proof.
  intros z [H1 H2]. unfold zlit64. apply Z.leb_le in H1. apply Z.ltb_lt in H2. rewrite H1, H2. reflexivity.
Qed.
Lemma zlit64_range : forall z, (0 <= zlit64 z < two64)%Z.
Proof.
  intros z. unfold zlit64. destruct (Z.leb 0 z && Z.ltb z two64)%bool eqn:E.
  - apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
  - apply Z.mod_pos_bound. unfold two64. lia.
Qed.
Lemma sub_itvLB_full : forall bc b k n c m,
  sub_itvLB b k n c m = true -> (0 <= n < two64)%Z -> sub_itvB bc b k n c m = true.
Proof.
  intros bc b k n [cb co] m H Hn. unfold sub_itvLB in H. cbn [a_base a_off] in H.
  destruct b as [zb| | | | | | |]; try discriminate. destruct cb as [zc| | | | | | |]; try discriminate.
  destruct m as [zm| | | | | | |]; try discriminate.
  unfold sub_itvB. destruct (sub_itv1B bc (ELit zb) k n (SA (ELit zc) co) (ELit zm)); [reflexivity|].
  replace (Z.leb 0 n && Z.ltb n two64)%bool with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
  cbn [side_cand novars a_base a_off orb]. unfold xinsideB. cbn [shares_var].
  unfold xinside_numSB, base_rangeB. cbv zeta. cbn [xhiB xloB]. rewrite (zlit64_small n Hn).
  destruct (Z.leb (zmod64 zc + co) (zmod64 zb + k)); [|discriminate]. rewrite H. reflexivity.
Qed.
Lemma in_sidesLB_B : forall bc D b k n,
  in_sidesLB D b k n = true -> (0 <= n < two64)%Z -> in_sidesB bc D b k n = true.
Proof.
  intros bc D b k n H Hn. rewrite in_sidesB_B0. induction D as [|[c m] r IH]; [discriminate|]. cbn [in_sidesLB in_sidesB0] in *.
  destruct (sub_itvLB b k n c m) eqn:E.
  - rewrite (sub_itvLB_full bc _ _ _ _ _ E Hn). reflexivity.
  - rewrite (IH H). destruct (sub_itvB bc b k n c m); reflexivity.
Qed.
Lemma sub_itvLB_mono : forall b glo glen kk m c mm,
  sub_itvLB b glo glen c mm = true -> (glo <= kk)%Z -> (kk + m <= glo + glen)%Z -> sub_itvLB b kk m c mm = true.
Proof.
  intros b glo glen kk m [cb co] mm H H1 H2. unfold sub_itvLB in *. cbn [a_base a_off] in *.
  destruct b as [zb| | | | | | |]; try discriminate. destruct cb as [zc| | | | | | |]; try discriminate.
  destruct mm as [zm| | | | | | |]; try discriminate.
  destruct (Z.leb_spec (zmod64 zc + co) (zmod64 zb + glo)) as [Ho|]; [|discriminate]. apply Z.leb_le in H.
  replace (Z.leb (zmod64 zc + co) (zmod64 zb + kk)) with true by (symmetry; apply Z.leb_le; lia). apply Z.leb_le. lia.
Qed.
Lemma in_sidesLB_mono : forall D b glo glen kk m,
  in_sidesLB D b glo glen = true -> (glo <= kk)%Z -> (kk + m <= glo + glen)%Z -> in_sidesLB D b kk m = true.
Proof.
  intros D b glo glen kk m H H1 H2. induction D as [|[c mm] r IH]; [discriminate|]. cbn [in_sidesLB] in *.
  destruct (sub_itvLB b glo glen c mm) eqn:E.
  - rewrite (sub_itvLB_mono _ _ _ _ _ _ _ E H1 H2). reflexivity.
  - rewrite (IH H). destruct (sub_itvLB b kk m c mm); reflexivity.
Qed.

(* [comment removed for export] *)
Definition two62z : Z := 4611686018427387904%Z.
(* [comment removed for export] *)
Definition lo_ge0 (o : option (Z * Z)) (lo0 : Z) : bool := match o with Some (lo, _) => Z.leb 0 (lo + lo0) | None => false end.
Definition rel_ge0B (bc : bctx) (c : Z) (ts : list (Z * expr)) : bool :=
  match bc_fs bc with
  | [] => false
  | fs =>
      match sum_subst fs ts 0 0 false with
      | (ts', (lo0, _), true) =>
          if lo_ge0 (lin_range (erangeB bc) c ts') lo0 then true
          else match ts' with
               | [] => false
               | _ :: _ => match sum_subst (bc_fss bc) ts 0 0 false with
                           | (ts2, (lo2, _), true) => lo_ge0 (lin_range (erangeB bc) c ts2) lo2
                           | _ => false
                           end
               end
      | _ => false
      end
  end.
Definition first_ge0B (bc : bctx) (c : Z) (ts : list (Z * expr)) : bool :=
  if lo_ge0 (lin_range (erangeB bc) c ts) 0 then true else rel_ge0B bc c ts.
Definition plain_ge0B (bc : bctx) (pos neg : xterms) : bool :=
  if xt_nowrapB bc pos then (if xt_nowrapB bc neg then
    first_ge0B bc (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)) else false) else false.
(* [comment removed for export] *)
Definition plain_ge0R (bc : bctx) (pos neg : xterms) : bool :=
  if lin_refutedB bc (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)) then false else plain_ge0B bc pos neg.
Definition sub_itvPB (bc : bctx) (b : expr) (k n : Z) (c : saddr) (m : expr) : bool :=
  if (if Z.leb 0 n then Z.ltb n two62z else false) then
    if shares_var b (a_base c) then
      if xin_possibleB bc b k (ELit n) (a_base c) (a_off c) m then
        if plain_ge0R bc [(b, k)] [(a_base c, a_off c)]
        then plain_ge0R bc [(a_base c, a_off c); (m, 0%Z)] [(b, k); (ELit n, 0%Z)] else false
      else false
    else false
  else false.
Fixpoint in_sidesPB (bc : bctx) (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itvPB bc b2 k2 n2 c m then true else in_sidesPB bc r b2 k2 n2
  end.
Lemma first_ge0B_test : forall bc c ts L c', first_ge0B bc c ts = true -> lin_testB bc c ts (ge0_test L c') = true.
Proof.
  intros bc c ts L c' H. unfold first_ge0B in H. unfold lin_testB.
  assert (REL : rel_ge0B bc c ts = true -> lin_test_relB bc c ts (ge0_test L c') = true).
  { clear H. intros H. unfold rel_ge0B in H. unfold lin_test_relB. destruct (bc_fs bc) as [|f fs]; [discriminate|].
    unfold lin_test_rel2. destruct (sum_subst (f :: fs) ts 0 0 false) as [[ts' [lo0 hi0]] [|]]; [|discriminate].
    destruct (lin_range (erangeB bc) c ts') as [[lo hi]|] eqn:E1; cbn [lo_ge0] in H.
    - unfold ge0_test at 1. destruct (Z.leb 0 (lo + lo0)) eqn:E2; [reflexivity|].
      destruct (let g := ts_gran L 0 in if Z.ltb 1 g then Z.leb 0 (lin_tight g c' (lo + lo0)) else false); [reflexivity|].
      destruct ts' as [|t ts']; [discriminate|]. unfold sum_try.
      destruct (sum_subst (bc_fss bc) ts 0 0 false) as [[ts2 [lo2 hi2]] [|]]; [|discriminate].
      destruct (lin_range (erangeB bc) c ts2) as [[l2 h2]|]; [|discriminate]. cbn [lo_ge0] in H. unfold ge0_test. rewrite H. reflexivity.
    - destruct ts' as [|t ts']; [discriminate|]. unfold sum_try.
      destruct (sum_subst (bc_fss bc) ts 0 0 false) as [[ts2 [lo2 hi2]] [|]]; [|discriminate].
      destruct (lin_range (erangeB bc) c ts2) as [[l2 h2]|]; [|discriminate]. cbn [lo_ge0] in H. unfold ge0_test. rewrite H. reflexivity. }
  destruct (lin_range (erangeB bc) c ts) as [[lo hi]|]; cbn [lo_ge0] in H.
  - unfold ge0_test at 1. rewrite Z.add_0_r in H. destruct (Z.leb 0 lo); [reflexivity|].
    destruct (let g := ts_gran L 0 in if Z.ltb 1 g then Z.leb 0 (lin_tight g c' lo) else false); [reflexivity|]. exact (REL H).
  - exact (REL H).
Qed.
Lemma plain_ge0B_full : forall bc pos neg, plain_ge0B bc pos neg = true ->
  lin_ge0B_core bc pos neg (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)) = true.
Proof.
  intros bc pos neg H. unfold plain_ge0B in H. unfold lin_ge0B_core, lin_ge0B_pass. rewrite ge0_testF_feq.
  destruct (xt_nowrapB bc pos); [|discriminate]. destruct (xt_nowrapB bc neg); [|discriminate]. cbv zeta.
  rewrite (first_ge0B_test _ _ _ _ _ H). reflexivity.
Qed.
Lemma plain_ge0R_full : forall bc pos neg, plain_ge0R bc pos neg = true -> lin_ge0B bc pos neg = true.
Proof.
  intros bc pos neg H. unfold plain_ge0R in H. unfold lin_ge0B. cbv zeta.
  destruct (lin_refutedB bc (xt_const pos - xt_const neg) (lsub_e (xt_lin pos) (xt_lin neg))); [discriminate|].
  apply plain_ge0B_full. exact H.
Qed.
Lemma sub_itvPB_full : forall bc b k n c m,
  sub_itvPB bc b k n c m = true -> sub_itvB bc b k n c m = true.
Proof.
  intros bc b k n c m H. unfold sub_itvPB in H.
  destruct (Z.leb_spec 0 n) as [Hn0|]; [|discriminate]. destruct (Z.ltb_spec n two62z) as [Hn1|]; [|discriminate].
  destruct (shares_var b (a_base c)) eqn:Hsh; [|discriminate].
  destruct (xin_possibleB bc b k (ELit n) (a_base c) (a_off c) m) eqn:Hp; [|discriminate].
  destruct (plain_ge0R bc [(b, k)] [(a_base c, a_off c)]) eqn:H1; [|discriminate].
  unfold sub_itvB. destruct (sub_itv1B bc b k n c m); [reflexivity|].
  replace (Z.leb 0 n && Z.ltb n two64)%bool with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; unfold two62z, two64 in *; lia).
  unfold side_cand. rewrite Hsh, Bool.orb_true_r. unfold xinsideB. rewrite Hsh, Hp. rewrite xinside0PB_eq. unfold xinside0B.
  rewrite (plain_ge0R_full _ _ _ H1). exact (plain_ge0R_full _ _ _ H).
Qed.
Lemma in_sidesPB_B : forall bc D b k n, in_sidesPB bc D b k n = true -> in_sidesB bc D b k n = true.
Proof.
  intros bc D b k n H. rewrite in_sidesB_B0. induction D as [|[c m] r IH]; [discriminate|]. cbn [in_sidesPB in_sidesB0] in *.
  destruct (sub_itvPB bc b k n c m) eqn:E.
  - rewrite (sub_itvPB_full _ _ _ _ _ _ E). reflexivity.
  - rewrite (IH H). destruct (sub_itvB bc b k n c m); reflexivity.
Qed.
Lemma lin_range_shift : forall r c d ts,
  lin_range r (c + d)%Z ts = match lin_range r c ts with Some (lo, hi) => Some ((lo + d)%Z, (hi + d)%Z) | None => None end.
Proof.
  intros r c d ts. induction ts as [|[k a] rest IH]; [reflexivity|]. cbn [lin_range]. rewrite IH.
  destruct (r a) as [[al ah]|]; [|reflexivity]. destruct (lin_range r c rest) as [[lo hi]|]; [|reflexivity].
  destruct (Z.leb 0 k); f_equal; f_equal; lia.
Qed.
Lemma lo_ge0_shift : forall r c d ts lo0, (0 <= d)%Z -> lo_ge0 (lin_range r c ts) lo0 = true -> lo_ge0 (lin_range r (c + d)%Z ts) lo0 = true.
Proof.
  intros r c d ts lo0 Hd H. rewrite lin_range_shift. destruct (lin_range r c ts) as [[lo hi]|]; [|discriminate]. cbn [lo_ge0] in *.
  apply Z.leb_le in H. apply Z.leb_le. lia.
Qed.
Lemma lin_refutedB_mono : forall bc c d ts, (0 <= d)%Z -> lin_refutedB bc c ts = false -> lin_refutedB bc (c + d)%Z ts = false.
Proof.
  intros bc c d ts Hd H. unfold lin_refutedB in *. rewrite lin_range_shift. destruct (lin_range (erangeB bc) c ts) as [[lo hi]|]; [|reflexivity].
  apply Z.ltb_ge in H. apply Z.ltb_ge. lia.
Qed.
Lemma first_ge0B_mono : forall bc c d ts, (0 <= d)%Z -> first_ge0B bc c ts = true -> first_ge0B bc (c + d)%Z ts = true.
Proof.
  intros bc c d ts Hd H. unfold first_ge0B in *.
  destruct (lo_ge0 (lin_range (erangeB bc) c ts) 0) eqn:E0.
  - rewrite (lo_ge0_shift _ _ _ _ _ Hd E0). reflexivity.
  - destruct (lo_ge0 (lin_range (erangeB bc) (c + d) ts) 0); [reflexivity|].
    unfold rel_ge0B in *. destruct (bc_fs bc) as [|f fs]; [discriminate|].
    destruct (sum_subst (f :: fs) ts 0 0 false) as [[ts' [lo0 hi0]] [|]]; [|discriminate].
    destruct (lo_ge0 (lin_range (erangeB bc) c ts') lo0) eqn:E1.
    + rewrite (lo_ge0_shift _ _ _ _ _ Hd E1). reflexivity.
    + destruct (lo_ge0 (lin_range (erangeB bc) (c + d) ts') lo0); [reflexivity|].
      destruct ts' as [|t ts']; [discriminate|].
      destruct (sum_subst (bc_fss bc) ts 0 0 false) as [[ts2 [lo2 hi2]] [|]]; [|discriminate].
      exact (lo_ge0_shift _ _ _ _ _ Hd H).
Qed.
Lemma snorm_small62 : forall z, (0 <= z < two62z)%Z -> snorm z = z.
Proof.
  intros z Hz. unfold snorm. replace (Z.leb mtwo63z z) with true by (symmetry; apply Z.leb_le; unfold mtwo63z, two62z in *; lia).
  replace (Z.ltb z two63z) with true by (symmetry; apply Z.ltb_lt; unfold two63z, two62z in *; lia). reflexivity.
Qed.
Lemma lin_nowrapRB_lit62 : forall bc z, (0 <= z < two62z)%Z -> lin_nowrapRB bc (ELit z) = true.
Proof.
  intros bc z Hz. unfold lin_nowrapRB. cbn [lin_of fst snd srl_expandB]. rewrite (snorm_small62 z Hz).
  unfold lin_testB. cbn [lin_range].
  replace (Z.leb 0 (z + 0) && Z.ltb (z + 0) two64)%bool with true; [reflexivity|].
  symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; unfold two62z, two64 in *; lia.
Qed.
Lemma xin_possibleB_mono : forall bc b glo glen kk m cb ck cm,
  (0 <= glen < two62z)%Z -> (0 <= m)%Z -> (glo <= kk)%Z -> (kk + m <= glo + glen)%Z ->
  xin_possibleB bc b glo (ELit glen) cb ck cm = true -> xin_possibleB bc b kk (ELit m) cb ck cm = true.
Proof.
  intros bc b glo glen kk m cb ck cm Hg Hm H1 H2 H. unfold xin_possibleB in *.
  destruct (base_rangeB bc b) as [[lo1 hi1]|]; [|reflexivity]. destruct (base_rangeB bc cb) as [[lo2 hi2]|]; [|reflexivity].
  assert (Zg : zlit64 glen = glen) by (apply zlit64_small; unfold two62z, two64 in *; lia).
  assert (Zm : zlit64 m = m) by (apply zlit64_small; unfold two62z, two64 in *; lia).
  rewrite Zg in H. rewrite Zm.
  destruct (Z.ltb_spec (hi1 + glo) (lo2 + ck)); [discriminate|].
  destruct (Z.ltb_spec (hi1 + kk) (lo2 + ck)); [lia|].
  destruct cm as [z2| | | | | | |]; try reflexivity.
  destruct (Z.ltb_spec (hi2 + ck + zlit64 z2) (lo1 + glo + glen)); [discriminate|].
  destruct (Z.ltb_spec (hi2 + ck + zlit64 z2) (lo1 + kk + m)); [lia|reflexivity].
Qed.
Lemma sub_itvPB_mono : forall bc b glo glen kk m c mm,
  sub_itvPB bc b glo glen c mm = true -> (glo <= kk)%Z -> (kk + m <= glo + glen)%Z -> (0 <= m)%Z -> sub_itvPB bc b kk m c mm = true.
Proof.
  intros bc b glo glen kk m [cb ck] mm H H1 H2 Hm. unfold sub_itvPB in *. cbn [a_base a_off] in *.
  destruct (Z.leb_spec 0 glen) as [Hg0|]; [|discriminate]. destruct (Z.ltb_spec glen two62z) as [Hg1|]; [|discriminate].
  replace (Z.leb 0 m) with true by (symmetry; apply Z.leb_le; lia).
  replace (Z.ltb m two62z) with true by (symmetry; apply Z.ltb_lt; lia).
  destruct (shares_var b cb); [|discriminate].
  destruct (xin_possibleB bc b glo (ELit glen) cb ck mm) eqn:Hp; [|discriminate].
  rewrite (xin_possibleB_mono bc b glo glen kk m cb ck mm (conj Hg0 Hg1) Hm H1 H2 Hp).
  destruct (plain_ge0R bc [(b, glo)] [(cb, ck)]) eqn:P1; [|discriminate].
  assert (P1' : plain_ge0R bc [(b, kk)] [(cb, ck)] = true).
  { unfold plain_ge0R in *. cbn [xt_const xt_lin] in *.
    replace (fst (lin_of b) + kk + 0 - (fst (lin_of cb) + ck + 0))%Z with ((fst (lin_of b) + glo + 0 - (fst (lin_of cb) + ck + 0)) + (kk - glo))%Z by lia.
    destruct (lin_refutedB bc (fst (lin_of b) + glo + 0 - (fst (lin_of cb) + ck + 0)) _) eqn:R1; [discriminate|].
    rewrite (lin_refutedB_mono _ _ (kk - glo) _ ltac:(lia) R1).
    unfold plain_ge0B in *. cbn [xt_nowrapB] in *.
    destruct (lin_nowrapRB bc b && true)%bool; [|discriminate]. destruct (lin_nowrapRB bc cb && true)%bool; [|discriminate].
    cbn [xt_const xt_lin] in *.
    replace (fst (lin_of b) + kk + 0 - (fst (lin_of cb) + ck + 0))%Z with ((fst (lin_of b) + glo + 0 - (fst (lin_of cb) + ck + 0)) + (kk - glo))%Z by lia.
    apply first_ge0B_mono; [lia | exact P1]. }
  rewrite P1'.
  unfold plain_ge0R in *. cbn [xt_const xt_lin lin_of fst snd fold_right] in *.
  rewrite (snorm_small62 glen (conj Hg0 Hg1)) in H. rewrite (snorm_small62 m ltac:(lia)).
  replace (fst (lin_of cb) + ck + (fst (lin_of mm) + 0 + 0) - (fst (lin_of b) + kk + (m + 0 + 0)))%Z
    with ((fst (lin_of cb) + ck + (fst (lin_of mm) + 0 + 0) - (fst (lin_of b) + glo + (glen + 0 + 0))) + (glo + glen - kk - m))%Z by lia.
  destruct (lin_refutedB bc (fst (lin_of cb) + ck + (fst (lin_of mm) + 0 + 0) - (fst (lin_of b) + glo + (glen + 0 + 0))) _) eqn:R2; [discriminate|].
  rewrite (lin_refutedB_mono _ _ (glo + glen - kk - m) _ ltac:(lia) R2).
  unfold plain_ge0B in *. cbn [xt_nowrapB] in *.
  destruct (lin_nowrapRB bc cb && (lin_nowrapRB bc mm && true))%bool; [|discriminate].
  rewrite (lin_nowrapRB_lit62 bc glen (conj Hg0 Hg1)) in H. rewrite (lin_nowrapRB_lit62 bc m ltac:(lia)).
  destruct (lin_nowrapRB bc b && (true && true))%bool; [|discriminate].
  cbn [xt_const xt_lin lin_of fst snd fold_right] in *.
  rewrite (snorm_small62 glen (conj Hg0 Hg1)) in H. rewrite (snorm_small62 m ltac:(lia)).
  replace (fst (lin_of cb) + ck + (fst (lin_of mm) + 0 + 0) - (fst (lin_of b) + kk + (m + 0 + 0)))%Z
    with ((fst (lin_of cb) + ck + (fst (lin_of mm) + 0 + 0) - (fst (lin_of b) + glo + (glen + 0 + 0))) + (glo + glen - kk - m))%Z by lia.
  apply first_ge0B_mono; [lia | exact H].
Qed.
Lemma in_sidesPB_mono : forall bc D b glo glen kk m,
  in_sidesPB bc D b glo glen = true -> (glo <= kk)%Z -> (kk + m <= glo + glen)%Z -> (0 <= m)%Z -> in_sidesPB bc D b kk m = true.
Proof.
  intros bc D b glo glen kk m H H1 H2 Hm. induction D as [|[c mm] r IH]; [discriminate|]. cbn [in_sidesPB] in *.
  destruct (sub_itvPB bc b glo glen c mm) eqn:E.
  - rewrite (sub_itvPB_mono _ _ _ _ _ _ _ _ E H1 H2 Hm). reflexivity.
  - rewrite (IH H). destruct (sub_itvPB bc b kk m c mm); reflexivity.
Qed.



(* [comment removed for export] *)
Lemma sub_itv_x_lit : forall kn b k z c m, (0 <= z < two64)%Z -> sub_itv_x kn b k (ELit z) c m = sub_itv kn b k z c m.
Proof.
  intros kn b k z c m Hz. unfold sub_itv_x, sub_itv, sub_itv_x1, sub_itv1. cbn [xhi]. rewrite (zlit64_small z Hz).
  destruct Hz as [H1 H2]. pose proof H1 as H1'. pose proof H2 as H2'. apply Z.leb_le in H1'. apply Z.ltb_lt in H2'. rewrite H1', H2'. cbn [andb].
  destruct (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool; [|reflexivity].
  destruct (xlo kn m) as [ml|]; reflexivity.
Qed.
Lemma disj_sides_x_lit : forall allkn kn b k z, (0 <= z < two64)%Z -> disj_sides_x allkn kn b k (ELit z) = disj_sides allkn kn b k z.
Proof.
  intros allkn kn b k z Hz. induction kn as [|K rest IH]; [reflexivity|].
  destruct K; cbn [disj_sides_x disj_sides]; try exact IH.
  rewrite !(sub_itv_x_lit allkn b k z) by exact Hz. rewrite IH. reflexivity.
Qed.
Definition mk_sprepB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) : sprep :=
  let br1 := base_rangeB bc b1 in   (* [comment removed for export] *)
  match n1 with
  | ELit z1 =>
      if (if Z.leb 0 z1 then Z.ltb z1 two64 else false)
      then let D := disj_sidesRB bc br1 b1 k1 (zlit64 z1) in SPrep br1 (xhiB bc n1) D D
      else SPrep br1 (xhiB bc n1) (disj_sidesRB bc br1 b1 k1 (zlit64 z1)) (disj_sides_xRB bc br1 b1 k1 n1)
  | _ => SPrep br1 (xhiB bc n1) [] (disj_sides_xRB bc br1 b1 k1 n1)
  end.
Lemma bc_kdi_mkbc : forall fk, bc_kdi (mkbc fk) = mk_kdi (bc_fk (mkbc fk)).
Proof. reflexivity. Qed.

Definition ranges_apart_pB (bc : bctx) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr)
           (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      if (match sp_rng sp, base_rangeB bc b2 with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
          | _, _ => false
          end) then true
      else if in_sidesHB bc (sp_D sp) b2 k2 m2 then true
      else lin_apartB bc b1 k1 m1 b2 k2 m2
  | _, _ =>
    if (match sp_rng sp, base_rangeB bc b2, sp_h1 sp, xhiB bc n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else (* [comment removed for export] *)
            if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if in_sides_xHB bc (sp_Dx sp) b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.

Lemma lin_test_relB_eqf : forall fk, lin_test_relB (mkbc fk) = lin_test_rel fk.
Proof. intros. bcfe. unfold lin_test_relB, lin_test_rel. autorewrite with bceq. destruct (sum_facts fk fk); reflexivity. Qed.
#[export] Hint Rewrite lin_test_relB_eqf : bceq.
Lemma lin_testB_eqf : forall fk, lin_testB (mkbc fk) = lin_test fk.
Proof. intros. bcfe. unfold lin_testB, lin_test. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_testB_eqf : bceq.
Lemma lin_srangeB_eqf : forall fk, lin_srangeB (mkbc fk) = lin_srange fk.
Proof. intros. bcfe. unfold lin_srangeB, lin_srange. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_srangeB_eqf : bceq.
Lemma lin_nowrapRB_eqf : forall fk, lin_nowrapRB (mkbc fk) = lin_nowrapR fk.
Proof. intros. bcfe. unfold lin_nowrapRB, lin_nowrapR. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_nowrapRB_eqf : bceq.
Lemma lin_apart0B_eqf : forall fk, lin_apart0B (mkbc fk) = lin_apart0 fk.
Proof. intros. bcfe. unfold lin_apart0B, lin_apart0. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_apart0B_eqf : bceq.
Lemma lin_apartB_eqf : forall fk, lin_apartB (mkbc fk) = lin_apart fk.
Proof. intros. bcfe. unfold lin_apartB, lin_apart. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_apartB_eqf : bceq.
Lemma lin_brangeB_eqf : forall fk, lin_brangeB (mkbc fk) = lin_brange fk.
Proof. intros. bcfe. unfold lin_brangeB, lin_brange. autorewrite with bceq. destruct (sum_facts fk fk); reflexivity. Qed.
#[export] Hint Rewrite lin_brangeB_eqf : bceq.
Lemma xloB_eqf : forall fk, xloB (mkbc fk) = xlo fk.
Proof. intros. bcfe. unfold xloB, xlo. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite xloB_eqf : bceq.
Lemma xhiB_eqf : forall fk, xhiB (mkbc fk) = xhi fk.
Proof. intros. bcfe. unfold xhiB, xhi. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite xhiB_eqf : bceq.
Lemma xt_nowrapB_eqf : forall fk, xt_nowrapB (mkbc fk) = xt_nowrap fk.
Proof.
  intros fk. apply functional_extensionality; intros ts. 
  induction ts as [|[e k] rest IH]; intros; bcfe; [reflexivity|].
  cbn [xt_nowrapB xt_nowrap]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite xt_nowrapB_eqf : bceq.
Lemma srl_scale_need2B_eqf : forall fk, srl_scale_need2B (mkbc fk) = srl_scale_need2 fk.
Proof. intros. bcfe. unfold srl_scale_need2B, srl_scale_need2. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite srl_scale_need2B_eqf : bceq.
Lemma lin_ge0_scaledB_eqf : forall fk, lin_ge0_scaledB (mkbc fk) = lin_ge0_scaled fk.
Proof. intros. bcfe. unfold lin_ge0_scaledB, lin_ge0_scaled. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_ge0_scaledB_eqf : bceq.
Lemma lin_ge0B_eqf : forall fk, lin_ge0B (mkbc fk) = lin_ge0 fk.
Proof. intros. bcfe. unfold lin_ge0B, lin_ge0B_core, lin_ge0B_pass, lin_refutedB, lin_ge0, lin_refuted. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_ge0B_eqf : bceq.
Lemma xinside0B_eqf : forall fk, xinside0B (mkbc fk) = xinside0 fk.
Proof. intros. bcfe. unfold xinside0B, xinside0. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite xinside0B_eqf : bceq.
Lemma xinside_numB_eqf : forall fk, xinside_numB (mkbc fk) = xinside_num fk.
Proof. intros. bcfe. unfold xinside_numB, xinside_num. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite xinside_numB_eqf : bceq.
Lemma xin_possibleB_eqf : forall fk, xin_possibleB (mkbc fk) = xin_possible fk.
Proof. intros. bcfe. unfold xin_possibleB, xin_possible. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite xin_possibleB_eqf : bceq.
Lemma xinside_numSB_eqf : forall fk, xinside_numSB (mkbc fk) = xinside_numS fk.
Proof. intros. bcfe. unfold xinside_numSB, xinside_numS. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite xinside_numSB_eqf : bceq.
Lemma xinsideB_eqf : forall fk, xinsideB (mkbc fk) = xinside fk.
Proof. intros. bcfe. unfold xinsideB, xinside. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite xinsideB_eqf : bceq.

Lemma sub_itv1B_eqf : forall fk, sub_itv1B (mkbc fk) = sub_itv1 fk.
Proof. intros. bcfe. unfold sub_itv1B, sub_itv1. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite sub_itv1B_eqf : bceq.
Lemma sub_itvB_eqf : forall fk, sub_itvB (mkbc fk) = sub_itv fk.
Proof. intros. bcfe. unfold sub_itvB, sub_itv. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite sub_itvB_eqf : bceq.
Lemma kdisj_apartB_eqf : forall fk, kdisj_apartB (mkbc fk) = kdisj_apart fk.
Proof.
  intros fk. apply functional_extensionality; intros kn. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1. apply functional_extensionality; intros b2. apply functional_extensionality; intros k2. apply functional_extensionality; intros n2. 
  revert b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [kdisj_apartB kdisj_apart]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite kdisj_apartB_eqf : bceq.
Lemma kdisj_apart1B_eqf : forall fk, kdisj_apart1B (mkbc fk) = kdisj_apart1 fk.
Proof.
  intros fk. apply functional_extensionality; intros kn. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1. apply functional_extensionality; intros b2. apply functional_extensionality; intros k2. apply functional_extensionality; intros n2. 
  revert b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [kdisj_apart1B kdisj_apart1]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite kdisj_apart1B_eqf : bceq.
Lemma kdisj_apart12B_eqf : forall fk, kdisj_apart12B (mkbc fk) = kdisj_apart12 fk.
Proof. intros. bcfe. unfold kdisj_apart12B, kdisj_apart12. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite kdisj_apart12B_eqf : bceq.
Lemma ranges_apartB_eqf : forall fk, ranges_apartB (mkbc fk) = ranges_apart fk.
Proof. intros. bcfe. unfold ranges_apartB, ranges_apart. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite ranges_apartB_eqf : bceq.
Lemma sub_itv_x1B_eqf : forall fk, sub_itv_x1B (mkbc fk) = sub_itv_x1 fk.
Proof. intros. bcfe. unfold sub_itv_x1B, sub_itv_x1. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite sub_itv_x1B_eqf : bceq.
Lemma sub_itv_xB_eqf : forall fk, sub_itv_xB (mkbc fk) = sub_itv_x fk.
Proof. intros. bcfe. unfold sub_itv_xB, sub_itv_x. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite sub_itv_xB_eqf : bceq.
Lemma kdisj_apart_xB_eqf : forall fk, kdisj_apart_xB (mkbc fk) = kdisj_apart_x fk.
Proof.
  intros fk. apply functional_extensionality; intros kn. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1. apply functional_extensionality; intros b2. apply functional_extensionality; intros k2. apply functional_extensionality; intros n2. 
  revert b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [kdisj_apart_xB kdisj_apart_x]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite kdisj_apart_xB_eqf : bceq.
Lemma kdisj_apart_x1B_eqf : forall fk, kdisj_apart_x1B (mkbc fk) = kdisj_apart_x1 fk.
Proof.
  intros fk. apply functional_extensionality; intros kn. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1. apply functional_extensionality; intros b2. apply functional_extensionality; intros k2. apply functional_extensionality; intros n2. 
  revert b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [kdisj_apart_x1B kdisj_apart_x1]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite kdisj_apart_x1B_eqf : bceq.
Lemma kdisj_apart_x12B_eqf : forall fk, kdisj_apart_x12B (mkbc fk) = kdisj_apart_x12 fk.
Proof. intros. bcfe. unfold kdisj_apart_x12B, kdisj_apart_x12. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite kdisj_apart_x12B_eqf : bceq.
Lemma end_hiB_eqf : forall fk, end_hiB (mkbc fk) = end_hi fk.
Proof. intros. bcfe. unfold end_hiB, end_hi. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite end_hiB_eqf : bceq.
Lemma ranges_apart_xB_eqf : forall fk, ranges_apart_xB (mkbc fk) = ranges_apart_x fk.
Proof. intros. bcfe. unfold ranges_apart_xB, ranges_apart_x. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite ranges_apart_xB_eqf : bceq.
Lemma disj_sidesB_eqf : forall fk, disj_sidesB (mkbc fk) = disj_sides fk.
Proof.
  intros fk. apply functional_extensionality; intros kn. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1. 
  rewrite disj_sidesB_ref.
  revert b1 k1 n1. induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [disj_sides_ref disj_sides]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite disj_sidesB_eqf : bceq.
Lemma disj_sides_xB_eqf : forall fk, disj_sides_xB (mkbc fk) = disj_sides_x fk.
Proof.
  intros fk. apply functional_extensionality; intros kn. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1. 
  rewrite disj_sides_xB_ref.
  revert b1 k1 n1. induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [disj_sides_ref disj_sides_x]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite disj_sides_xB_eqf : bceq.
Lemma in_sidesB_eqf : forall fk, in_sidesB (mkbc fk) = in_sides fk.
Proof.
  intros fk. apply functional_extensionality; intros D. apply functional_extensionality; intros b2. apply functional_extensionality; intros k2. apply functional_extensionality; intros n2. 
  rewrite in_sidesB_B0.
  revert b2 k2 n2. induction D as [|[c m] rest IH]; intros; bcfe; [reflexivity|].
  cbn [in_sidesB0 in_sides]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite in_sidesB_eqf : bceq.
Lemma in_sides_xB_eqf : forall fk, in_sides_xB (mkbc fk) = in_sides_x fk.
Proof.
  intros fk. apply functional_extensionality; intros D. apply functional_extensionality; intros b2. apply functional_extensionality; intros k2. apply functional_extensionality; intros n2. 
  rewrite in_sides_xB_B0.
  revert b2 k2 n2. induction D as [|[c m] rest IH]; intros; bcfe; [reflexivity|].
  cbn [in_sides_xB0 in_sides_x]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite in_sides_xB_eqf : bceq.
Lemma mk_sprepB_eqf : forall fk, mk_sprepB (mkbc fk) = mk_sprep fk.
Proof.
  intros fk. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1.
  unfold mk_sprepB, mk_sprep. cbv zeta.
  destruct n1 as [z1| | | | | | |]; rewrite ?disj_sidesRB_eq, ?disj_sides_xRB_eq;
    try (rewrite ?(disj_sides_xIB_eq (mkbc fk) _ _ _ (bc_kdi_mkbc fk)); autorewrite with bceq; reflexivity).
  destruct (if Z.leb 0 z1 then Z.ltb z1 two64 else false) eqn:Hc;
    [|rewrite (disj_sidesIB_eq (mkbc fk) _ _ _ (bc_kdi_mkbc fk)), (disj_sides_xIB_eq (mkbc fk) _ _ _ (bc_kdi_mkbc fk)); autorewrite with bceq; reflexivity].
  assert (Hz : (0 <= z1 < two64)%Z).
  { destruct (Z.leb_spec 0 z1); [|discriminate]. apply Z.ltb_lt in Hc. split; assumption. }
  cbv zeta. rewrite (disj_sidesIB_eq (mkbc fk) _ _ _ (bc_kdi_mkbc fk)). autorewrite with bceq. cbn [bc_fk mkbc mkbc0].
  rewrite (disj_sides_x_lit fk fk b1 k1 z1 Hz), (zlit64_small z1 Hz). reflexivity.
Qed.
#[export] Hint Rewrite mk_sprepB_eqf : bceq.
Lemma ranges_apart_pB_eqf : forall fk, ranges_apart_pB (mkbc fk) = ranges_apart_p fk.
Proof. intros. bcfe. unfold ranges_apart_pB, ranges_apart_p. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite ranges_apart_pB_eqf : bceq.

(* [comment removed for export] *)
Fixpoint coeffs_divkB (bc : bctx) (m : Z) (ts : list (Z * expr)) : bool :=
  match ts with
  | [] => true
  | (k, a) :: rest => (if (if Z.eqb (zmodf k m) 0 then true else Z.eqb (zmodf (k * 2 ^ ealignB bc a) m) 0) then coeffs_divkB bc m rest else false)
  end.

Definition lin_lowbits_knB (bc : bctx) (e : expr) (k : Z) : option Z :=
  let l := lin_of e in
  if coeffs_divkB bc (2 ^ k) (snd l) then Some (zmodp (fst l) k)
  else pageup_low e (2 ^ k).

Definition lin_nowrap_lB (bc : bctx) (c : Z) (ts : list (Z * expr)) : bool :=
  match lin_range (erangeB bc) c ts with
  | Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi two64)%bool
  | None => false
  end.

Definition mkSrlB (bc : bctx) (a : expr) (s : Z) : expr :=
  let l := lin_of a in
  let m := (2 ^ s)%Z in
  if (if (if negb (lin_trivial l) then coeffs_div m (snd l) else false) then lin_nowrapB bc a else false)
  then unlin (zshr (fst l) s, ldiv_terms m (snd l))     (* [comment removed for export] *)
  else
    (* [comment removed for export] *)
    match (if (if negb (lin_trivial l) then lin_nowrapB bc a else false) then lsplit_divc m (snd l) else ([], [])) with
    | ((_ :: _) as dts, (_ :: _) as rts) =>
        match (if lin_nowrap_lB bc (fst l) rts then erangeB bc (unlin (fst l, rts)) else None) with
        | Some (lo, hi) =>
            if Z.eqb (zshr lo s) (zshr hi s) then unlin (zshr lo s, ldiv_terms m dts)
            else mkAlu ALU_SRL a (ELit s)
        | None => mkAlu ALU_SRL a (ELit s)
        end
    | _ => mkAlu ALU_SRL a (ELit s)
    end.

Fixpoint lowbitsB (bc : bctx) (e : expr) (j : Z) {struct e} : option Z :=
  match e with
  | ELit z => Some (zmodp (zmod64 z) j)%Z
  | EAlu ALU_AND a (ELit c) =>
      if Z.eqb (zmodp (zmod64 c) j) 0 then Some 0%Z else
      match lowbitsB bc a j with Some v => Some (Z.land v (zmodp (zmod64 c) j)) | None => (if Z.leb j (ealignB bc e) then Some 0%Z else lin_lowbits_knB bc e j) end
  | EAlu ALU_OR a (ELit c) =>
      match lowbitsB bc a j with Some v => Some (Z.lor v (zmodp (zmod64 c) j)) | None => (if Z.leb j (ealignB bc e) then Some 0%Z else lin_lowbits_knB bc e j) end
  | EAlu ALU_XOR a (ELit c) =>
      match lowbitsB bc a j with Some v => Some (Z.lxor v (zmodp (zmod64 c) j)) | None => (if Z.leb j (ealignB bc e) then Some 0%Z else lin_lowbits_knB bc e j) end
  | EAlu ALU_ADD a b =>
      match lowbitsB bc a j, lowbitsB bc b j with Some x, Some y => Some (zmodp (x + y) j) | _, _ => (if Z.leb j (ealignB bc e) then Some 0%Z else lin_lowbits_knB bc e j) end
  | EAlu ALU_SUB a b =>
      match lowbitsB bc a j, lowbitsB bc b j with Some x, Some y => Some (zmodp (x - y) j) | _, _ => (if Z.leb j (ealignB bc e) then Some 0%Z else lin_lowbits_knB bc e j) end
  | EMd M_MUL (ELit c) a =>
      if Z.eqb (zmodp (zmod64 c) j) 0 then Some 0%Z else
      match lowbitsB bc a j with Some v => Some (zmodp (c * v) j) | None => (if Z.leb j (ealignB bc e) then Some 0%Z else lin_lowbits_knB bc e j) end
  | _ => (if Z.leb j (ealignB bc e) then Some 0%Z else lin_lowbits_knB bc e j)
  end.

Fixpoint lsplit_divB (bc : bctx) (m : Z) (ts : list (Z * expr)) : list (Z * expr) * list (Z * expr) :=
  match ts with
  | [] => ([], [])
  | (k, a) :: rest =>
      let (d, r) := lsplit_divB bc m rest in
      if (if Z.eqb (zmodf k m) 0 then true else Z.eqb (zmodf (k * 2 ^ ealignB bc a) m) 0) then ((k, a) :: d, r) else (d, (k, a) :: r)
  end.

Definition and_high_splitB (bc : bctx) (bk : expr) (j c : Z) (dts rts : list (Z * expr)) : expr :=
  let m := (2 ^ j)%Z in
  let cA := (c - c mod m)%Z in
  let r := unlin ((c mod m)%Z, rts) in
  match erangeB bc r with
  | Some (lo, hi) =>
      if Z.eqb (lo / m) (hi / m) then unlin ((cA + (lo / m) * m)%Z, dts)
      else mkAlu ALU_ADD (unlin (cA, dts)) (mkAlu ALU_AND r bk)
  | None => mkAlu ALU_ADD (unlin (cA, dts)) (mkAlu ALU_AND r bk)
  end.

Definition and_low_splitB (bc : bctx) (bk : expr) (j c : Z) (rts : list (Z * expr)) : expr :=
  let m := (2 ^ j)%Z in
  let r := unlin (zmodp c j, rts) in
  match erangeB bc r with
  | Some (lo, hi) =>
      if Z.eqb (zshr lo j) (zshr hi j) then unlin ((zmodp c j - (zshr lo j) * m)%Z, rts)
      else mkAlu ALU_AND r bk
  | None => mkAlu ALU_AND r bk
  end.

Definition narrow_maskB (bc : bctx) (a : expr) (k' : Z) : option Z :=
  let i := ctz64F k' in
  let m := (k' + 2 ^ i)%Z in
  let j := Z.log2 m in
  if (Z.ltb 0 k' && Z.eqb m (2 ^ j) && Z.ltb j 64)%bool then
    match xhiB bc a with
    | Some h => if Z.ltb h (2 ^ j) then Some (two64 - 2 ^ i)%Z else None
    | None => None
    end
  else None.

Definition mkAnd0B (bc : bctx) (a b : expr) : expr :=
  match b with
  | ELit k =>
      let k' := zmod64 k in
      let j := Z.log2 (two64 - k') in
      if (Z.eqb (two64 - k') (2 ^ j) && Z.ltb j 64)%bool then
        (* [comment removed for export] *)
        (if Z.leb j (ealignB bc a) then a
         else let l := lin_of a in
              if (if negb (lin_trivial l) then coeffs_divkB bc (2 ^ j) (snd l) else false)
              then unlin ((fst l - zmodp (fst l) j)%Z, snd l)
              else (* [comment removed for export] *)
                match (if lin_trivial l then ([], snd l) else lsplit_divB bc (2 ^ j) (snd l)) with
                | ((_ :: _) as dts, (_ :: _) as rts) => and_high_splitB bc b j (fst l) dts rts
                | _ => (* [comment removed for export] *)
                       mkMd M_MUL (ELit (2 ^ j)%Z) (mkSrlB bc a j)
                end)
      else
        let j2 := Z.log2 (k' + 1) in
        if (Z.eqb (k' + 1) (2 ^ j2) && Z.ltb j2 64)%bool then
          (* [comment removed for export] *)
          (if Z.leb j2 (ealignB bc a) then ELit 0
           else match lowbitsB bc a j2 with        (* [comment removed for export] *)
           | Some v => ELit v
           | None =>
           if lin_trivial (lin_of a) then mkAlu ALU_AND a b
           else match lin_lowbits_knB bc a j2 with
                | Some v => ELit v
                | None => (* [comment removed for export] *)
                    match lsplit_divB bc (2 ^ j2) (snd (lin_of a)) with
                    | (_ :: _, (_ :: _) as rts) => and_low_splitB bc b j2 (fst (lin_of a)) rts
                    | _ => mkAlu ALU_AND a b
                    end
                end
           end)
        else (* [comment removed for export] *)
          let j3 := (Z.log2 k' + 1)%Z in
          if (Z.ltb 0 k' && Z.leb j3 64 && negb (lin_trivial (lin_of a)))%bool then
            match lin_lowbits_knB bc a j3 with
            | Some v => ELit (Z.land v k')
            | None => mkAlu ALU_AND a b
            end
          else mkAlu ALU_AND a b
  | _ => mkAlu ALU_AND a b
  end.

Definition mkAndB (bc : bctx) (a b : expr) : expr :=
  match b with
  | ELit k =>
      match narrow_maskB bc a (k mod two64)%Z with
      | Some m => mkAnd0B bc a (ELit m)
      | None => mkAnd0B bc a b
      end
  | _ => mkAnd0B bc a b
  end.

Definition mkAndKB (bc : bctx) (a b : expr) : expr :=
  match a, b with
  | EAlu ALU_AND x (ELit m1), ELit k => mkAndB bc x (ELit (Z.land (m1 mod two64) (k mod two64))%Z)
  | EMd M_MUL (ELit m) (EAlu ALU_SRL x (ELit i)), ELit k =>
      (* [comment removed for export] *)
      let i' := ((i mod two64) mod 64)%Z in
      if Z.eqb (m mod two64) (2 ^ i') then mkAndB bc x (ELit (Z.land (two64 - 2 ^ i') (k mod two64))%Z)
      else mkAndB bc a b
  | _, _ => mkAndB bc a b
  end.

Definition or_disjointB (bc : bctx) (a b : expr) : bool :=
  match erangeB bc b with
  | Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi (2 ^ (ealignB bc a)))%bool
  | None => false
  end.

Definition mkOrB (bc : bctx) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | Some x, Some y => ELit (zalu ALU_OR x y)
  | _, _ =>
      if or_disjointB bc a b then mkAlu ALU_ADD a b
      else if or_disjointB bc b a then mkAlu ALU_ADD a b
      else (* [comment removed for export] *)
           match b with
           | ELit c => mkAlu ALU_ADD (mkAndKB bc a (ELit (Z.lnot (c mod two64)))) (ELit c)
           | _ => match a with
                  | ELit c => mkAlu ALU_ADD (mkAndKB bc b (ELit (Z.lnot (c mod two64)))) (ELit c)
                  | _ => EAlu ALU_OR a b
                  end
           end
  end.

Fixpoint conc_tryB (bc : bctx) (e : expr) (cands : list expr) : option Z :=
  match cands with
  | [] => None
  | s :: rest =>
      if closedb s then conc_tryB bc e rest else
      if negb (evalS_def s e) then conc_tryB bc e rest else
      match erangeB bc s with
      | Some (lo, hi) =>
          if Z.leb (hi - lo) conc_limit then
            match evalS s (wrap64 lo) e with
            | Some v =>
                if (if Z.ltb hi lo then true
                     else if probeS s e v hi then probeS s e v (lo + (hi - lo) / 2)%Z else false) then
                  if all_eval_toS s e v lo (Z.to_nat (hi - lo + 1)) then Some v
                  else conc_tryB bc e rest
                else conc_tryB bc e rest
            | None => conc_tryB bc e rest
            end
          else conc_tryB bc e rest
      | None => conc_tryB bc e rest
      end
  end.

Definition concretizeB (bc : bctx) (e : expr) : option Z :=
  if closedb e then eval_closed e else conc_tryB bc e (nubE (subexprs e)).

Definition foldKB (bc : bctx) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => match erangeB bc e with
         | Some (lo, hi) => if Z.eqb lo hi then ELit lo
                            else match concretizeB bc e with Some v => ELit v | None => e end
         | None => match concretizeB bc e with Some v => ELit v | None => e end   (* [comment removed for export] *)
         end
  end.

Definition ltuB (bc : bctx) (a b : expr) : option bool :=
  if lin_ge0B bc [(b, (-1)%Z)] [(a, 0%Z)] then Some true
  else if lin_ge0B bc [(a, 0%Z)] [(b, 0%Z)] then Some false else None.
(* [comment removed for export] *)
Definition lin_branchB (bc : bctx) (c : branch_cond) (a b : expr) : option bool :=
  match c with
  | BC_LTU => ltuB bc a b
  | BC_GEU => option_map negb (ltuB bc a b)
  | BC_LT | BC_GE =>
      match erangeB bc a, erangeB bc b with
      | Some (_, ah), Some (_, bh) =>
          if (if Z.ltb ah two63z then Z.ltb bh two63z else false)
          then match c with BC_LT => ltuB bc a b | _ => option_map negb (ltuB bc a b) end
          else None
      | _, _ => None
      end
  | BC_EQ | BC_NE =>
      (* [comment removed for export] *)
      if (if lin_ge0B bc [(b, (-1)%Z)] [(a, 0%Z)] then true else lin_ge0B bc [(a, (-1)%Z)] [(b, 0%Z)])
      then Some (match c with BC_EQ => false | _ => true end)
      else
      (* [comment removed for export] *)
      if (if lin_ge0B bc [(a, 0%Z)] [(b, 0%Z)] then lin_ge0B bc [(b, 0%Z)] [(a, 0%Z)] else false)
      then Some (match c with BC_EQ => true | _ => false end)
      else None
  end.


Definition disj_branchB (bc : bctx) (c : branch_cond) (a b : expr) : option bool :=
  match c with
  | BC_EQ | BC_NE =>
      if ranges_apart_xB bc a 0%Z (ELit 1%Z) b 0%Z (ELit 1%Z) then Some (match c with BC_EQ => false | _ => true end) else None
  | _ => None
  end.
Definition decide_branchB (bc : bctx) (c : branch_cond) (a b : expr) : option bool :=
  match a, b with
  | ELit x, ELit y => Some (lit_branch c x y)
  | _, _ =>
      if expr_eqb a b then Some (cond_on_eq c)
      else match diff_branch c a b with
           | Some t => Some t
           | None =>
             match (match erangeB bc a, erangeB bc b with
                    | Some (al, ah), Some (bl, bh) => range_branch c al ah bl bh
                    | _, _ => None
                    end) with
             | Some t => Some t
             | None => match lin_branchB bc c a b with      (* [comment removed for export] *)
                       | Some t => Some t
                       | None => match disj_branchB bc c a b with   (* [comment removed for export] *)
                                 | Some t => Some t
                                 | None => congr_branch c a b        (* [comment removed for export] *)
                                 end
                       end
             end
           end
  end.

Definition mkSltB (bc : bctx) (c : branch_cond) (op : aluop) (a b : expr) : expr :=
  match a, b with
  | ELit _, ELit _ => mkAlu op a b
  | _, _ => match decide_branchB bc c a b with
            | Some true => ELit 1
            | Some false => ELit 0
            | None => mkAlu op a b
            end
  end.

Definition mkAluK0B (bc : bctx) (op : aluop) (a b : expr) : expr :=
  match op with
  | ALU_SLTU => mkSltB bc BC_LTU ALU_SLTU a b
  | ALU_SLT => mkSltB bc BC_LT ALU_SLT a b
  | ALU_AND => match a, b with
               | ELit _, ELit _ => mkAndB bc a b
               | ELit _, _ => mkAndKB bc b a      (* [comment removed for export] *)
               | _, _ => mkAndKB bc a b
               end
  | ALU_OR => if expr_eqb a b then a else mkOrB bc a b
  | ALU_XOR => if expr_eqb a b then ELit 0 else match is_lit a, b with
               | None, ELit k => if Z.eqb (k mod two64) (two64 - 1) then mkAlu ALU_SUB (ELit (two64 - 1)) a
                                else mkAlu op a b
               | _, _ => mkAlu op a b
               end
  | ALU_SRL => match is_lit a, shamt_of b 6 with
               | None, Some s => mkSrlB bc a s
               | _, _ => mkAlu op a b
               end
  | _ => mkAlu op a b
  end.

Definition mkAluKB (bc : bctx) (op : aluop) (a b : expr) : expr :=
  foldKB bc (mkAluK0B bc op a b).

Definition mkMdKB (bc : bctx) (op : mulop) (a b : expr) : expr :=
  match is_lit a, op, b with
  | None, M_REMU, ELit m =>
      match pow2_log m with
      | Some k => mkAluKB bc ALU_AND a (ELit (2 ^ k - 1))
      | None => mkMd op a b
      end
  | None, M_DIVU, ELit m =>
      match pow2_log m with
      | Some k => mkAluKB bc ALU_SRL a (ELit k)
      | None => mkMd op a b
      end
  | _, _, _ => mkMd op a b
  end.

Definition zband32B (bc : bctx) (d : expr) : bool :=
  let l := lin_of d in
  match lin_range (erangeB bc) (fst l) (snd l) with
  | Some (lo, hi) => (Z.ltb (- two31z) lo && Z.ltb hi two31z)%bool
  | None => false
  end.

Definition mkAluwK0B (bc : bctx) (op : aluop) (a b : expr) : expr :=
  match op with
  | ALU_ADD | ALU_SUB =>
      let d := mkAlu op a b in
      match is_lit d with
      | Some v => ELit (zsx32 v)
      | None => match erangeB bc d with
                | Some (lo, hi) => if sx32_stable lo hi then d else if zband32B bc d then d else mkAluw op a b
                | None => if zband32B bc d then d else mkAluw op a b
                end
      end
  | _ => mkAluw op a b
  end.

Definition mkAluwKB (bc : bctx) (op : aluop) (a b : expr) : expr :=
  foldKB bc (mkAluwK0B bc op a b).

Definition extK0B (bc : bctx) (v : expr) : expr :=
  match v with
  | EExt sx O n e =>
      if Nat.leb n 7 then
        match erangeB bc e with
        | Some (lo, hi) => if Z.ltb hi (if sx then zdivf (pow8n n) 2 else pow8n n) then e else v
        | None => v
        end
      else v
  | _ => v
  end.

Definition extKB (bc : bctx) (v : expr) : expr := foldKB bc (extK0B bc v).

Definition flat_scB (bc : bctx) (a : saddr) (n : nat) : list sidecond :=
  match base_rangeB bc (a_base a) with
  | Some (lo, hi) =>
      if (Z.leb 0 (lo + a_off a) && Z.leb (hi + a_off a + Z.of_nat n) two64)%bool
      then [] else [SCFlat a (elen n)]
  | None => [SCFlat a (elen n)]
  end.

Fixpoint wr_coveredB0 (bc : bctx) (kn : list kentry) (a : saddr) (n : nat) : bool :=
  match kn with
  | [] => false
  | KWr (SA kb kk) len :: rest =>
      if (if (expr_eqb (a_base a) kb && Z.leb kk (a_off a))%bool
          then match xloB bc len with Some l => Z.leb (a_off a + Z.of_nat n) (kk + l) | None => false end
          else false)
      then true
      else if xinsideB bc (a_base a) (a_off a) (ELit (Z.of_nat n)) kb kk len then true
      else wr_coveredB0 bc rest a n
  | _ :: rest => wr_coveredB0 bc rest a n
  end.
(* [comment removed for export] *)
Fixpoint wr_covered1B (bc : bctx) (kn : list kentry) (a : saddr) (n : nat) : bool :=
  match kn with
  | [] => false
  | KWr (SA kb kk) len :: rest =>
      if (if (expr_eqb (a_base a) kb && Z.leb kk (a_off a))%bool
          then match xloB bc len with Some l => Z.leb (a_off a + Z.of_nat n) (kk + l) | None => false end
          else false)
      then true
      else wr_covered1B bc rest a n
  | _ :: rest => wr_covered1B bc rest a n
  end.
Definition wr_coveredB (bc : bctx) (kn : list kentry) (a : saddr) (n : nat) : bool :=
  if wr_covered1B bc kn a n then true else wr_coveredB0 bc kn a n.
Lemma wr_coveredB_B0 : forall bc kn a n, wr_coveredB bc kn a n = wr_coveredB0 bc kn a n.
Proof.
  intros. unfold wr_coveredB. destruct (wr_covered1B bc kn a n) eqn:E; [|reflexivity]. symmetry.
  induction kn as [|K rest IH]; [discriminate|].
  destruct K as [| | | | | |[kb kk] len| | |]; cbn [wr_covered1B wr_coveredB0] in *; try (apply IH; exact E).
  destruct (if (expr_eqb (a_base a) kb && Z.leb kk (a_off a))%bool
            then match xloB bc len with Some l => Z.leb (a_off a + Z.of_nat n) (kk + l) | None => false end else false); [reflexivity|].
  rewrite (IH E). destruct (xinsideB bc (a_base a) (a_off a) (ELit (Z.of_nat n)) kb kk len); reflexivity.
Qed.

Definition storeok_scB (bc : bctx) (a : saddr) (n : nat) : list sidecond :=
  if wr_coveredB bc (bc_fk bc) a n then [] else [SCStoreOk a n].

Definition conc_exprB (bc : bctx) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => match concretizeB bc e with Some v => ELit v | None => e end
  end.

Definition enum_branchB (bc : bctx) (c : branch_cond) (a b : expr) : option bool :=
  let '(e, pos) := cond_probe c a b in
  match concretizeB bc e with
  | Some v => let z := Z.eqb (v mod two64) 0 in Some (if pos then negb z else z)
  | None => None
  end.

Definition to_saddrKB (bc : bctx) (e : expr) (imm : Z) : saddr :=
  match split_lit e with
  | (ELit _, _) => to_saddr e imm
  | _ => match concretizeB bc (mkAlu ALU_ADD e (ELit imm)) with
         | Some v => SA (ELit 0) v
         | None => to_saddr e imm
         end
  end.

Definition amo_alignedbB (bc : bctx) (e : expr) (wd : awidth) : bool :=
  match lin_lowbits_knB bc e (match wd with AW => 2 | AD => 3 end) with
  | Some r => Z.eqb r 0
  | None => false
  end.

Definition amo_newvalB (bc : bctx) (wd : awidth) (aop : option aluop) (old src : expr) : expr :=
  match aop with
  | None => src
  | Some o => match wd with AW => mkAluwKB bc o old src | AD => mkAluKB bc o old src end
  end.

Fixpoint log_lookupB (bc : bctx) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      match rel_litD rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupB bc rest rb rk n sx hints acc
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          if ranges_apartB bc rb rk (Z.of_nat n) kb kk (Z.of_nat w)
          then log_lookupB bc rest rb rk n sx hints acc
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupB bc rest rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
          end
      end
  end.

(* [comment removed for export] *)
Lemma p_in_sidesB_ref : forall bc kn b1 k1 n1 b2 k2 n2,
  in_sidesB bc (disj_sides_ref (fun c m => sub_itvB bc b1 k1 n1 c m) kn) b2 k2 n2 = kdisj_apartB bc kn b1 k1 n1 b2 k2 n2.
Proof.
  intros bc kn b1 k1 n1 b2 k2 n2. rewrite in_sidesB_B0. induction kn as [|K rest IH]; [reflexivity|].
  destruct K as [| | | | | | |c1 m1 c2 m2| |]; cbn [disj_sides_ref kdisj_apartB]; try exact IH.
  destruct (sub_itvB bc b1 k1 n1 c1 m1), (sub_itvB bc b1 k1 n1 c2 m2); cbn [in_sidesB0];
    destruct (sub_itvB bc b2 k2 n2 c2 m2) eqn:E2, (sub_itvB bc b2 k2 n2 c1 m1) eqn:E1;
    rewrite ?E1, ?E2, ?IH; reflexivity.
Qed.
Lemma p_sub_itv1B_sub : forall bc b k n c m, sub_itv1B bc b k n c m = true -> sub_itvB bc b k n c m = true.
Proof. intros bc b k n c m H. unfold sub_itvB. rewrite H. reflexivity. Qed.
Lemma p_kdisj_apart1B_full : forall bc kn b1 k1 n1 b2 k2 n2,
  kdisj_apart1B bc kn b1 k1 n1 b2 k2 n2 = true -> kdisj_apartB bc kn b1 k1 n1 b2 k2 n2 = true.
Proof.
  intros bc kn b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; [discriminate|].
  destruct K as [| | | | | | |c1 m1 c2 m2| |]; cbn [kdisj_apart1B kdisj_apartB]; try exact IH.
  destruct (sub_itv1B bc b1 k1 n1 c1 m1) eqn:A1.
  - rewrite (p_sub_itv1B_sub _ _ _ _ _ _ A1).
    destruct (sub_itv1B bc b2 k2 n2 c2 m2) eqn:A2; [rewrite (p_sub_itv1B_sub _ _ _ _ _ _ A2); reflexivity|].
    destruct (sub_itv1B bc b1 k1 n1 c2 m2) eqn:A3.
    + rewrite (p_sub_itv1B_sub _ _ _ _ _ _ A3).
      destruct (sub_itv1B bc b2 k2 n2 c1 m1) eqn:A4; [rewrite (p_sub_itv1B_sub _ _ _ _ _ _ A4); intros _; destruct (sub_itvB bc b2 k2 n2 c2 m2); reflexivity|].
      intros H. rewrite (IH H). destruct (sub_itvB bc b2 k2 n2 c2 m2); [reflexivity|]. destruct (sub_itvB bc b2 k2 n2 c1 m1); reflexivity.
    + intros H. rewrite (IH H). destruct (sub_itvB bc b2 k2 n2 c2 m2); [reflexivity|].
      destruct (if sub_itvB bc b1 k1 n1 c2 m2 then sub_itvB bc b2 k2 n2 c1 m1 else false); reflexivity.
  - destruct (sub_itv1B bc b1 k1 n1 c2 m2) eqn:A3.
    + rewrite (p_sub_itv1B_sub _ _ _ _ _ _ A3).
      destruct (sub_itv1B bc b2 k2 n2 c1 m1) eqn:A4.
      * rewrite (p_sub_itv1B_sub _ _ _ _ _ _ A4). intros _.
        destruct (if sub_itvB bc b1 k1 n1 c1 m1 then sub_itvB bc b2 k2 n2 c2 m2 else false); reflexivity.
      * intros H. rewrite (IH H).
        destruct (if sub_itvB bc b1 k1 n1 c1 m1 then sub_itvB bc b2 k2 n2 c2 m2 else false); [reflexivity|].
        destruct (sub_itvB bc b2 k2 n2 c1 m1); reflexivity.
    + intros H. rewrite (IH H).
      destruct (if sub_itvB bc b1 k1 n1 c1 m1 then sub_itvB bc b2 k2 n2 c2 m2 else false); [reflexivity|].
      destruct (if sub_itvB bc b1 k1 n1 c2 m2 then sub_itvB bc b2 k2 n2 c1 m1 else false); reflexivity.
Qed.
Lemma p_kdisj_apart12B_eq : forall bc kn b1 k1 n1 b2 k2 n2,
  kdisj_apart12B bc kn b1 k1 n1 b2 k2 n2 = kdisj_apartB bc kn b1 k1 n1 b2 k2 n2.
Proof.
  intros. unfold kdisj_apart12B. destruct (kdisj_apart1B bc kn b1 k1 n1 b2 k2 n2) eqn:E; [|reflexivity].
  symmetry. apply p_kdisj_apart1B_full. exact E.
Qed.
Lemma p_zlit64_nat8 : forall n, Nat.leb n 8 = true -> zlit64 (Z.of_nat n) = Z.of_nat n.
Proof. intros n H. apply Nat.leb_le in H. apply zlit64_small. unfold two64. lia. Qed.
(* [comment removed for export] *)
Lemma p_ranges_apart_pB_lit : forall bc b1 k1 n b2 k2 w, bc_kdi bc = mk_kdi (bc_fk bc) -> Nat.leb n 8 = true -> Nat.leb w 8 = true ->
  ranges_apart_pB bc (mk_sprepB bc b1 k1 (elen n)) b1 k1 (elen n) b2 k2 (elen w) = ranges_apartB bc b1 k1 (Z.of_nat n) b2 k2 (Z.of_nat w).
Proof.
  intros bc b1 k1 n b2 k2 w Hk Hn Hw. unfold ranges_apart_pB, ranges_apartB, elen. rewrite ?in_sidesHB_feq, ?in_sides_xHB_feq.
  rewrite (p_zlit64_nat8 n Hn), (p_zlit64_nat8 w Hw).
  unfold mk_sprepB.
  assert (Hc : (if Z.leb 0 (Z.of_nat n) then Z.ltb (Z.of_nat n) two64 else false) = true).
  { apply Nat.leb_le in Hn. destruct (Z.leb_spec 0 (Z.of_nat n)); [|lia]. apply Z.ltb_lt. unfold two64. lia. }
  rewrite Hc. cbv zeta. cbn [sp_rng sp_D]. rewrite (p_zlit64_nat8 n Hn). rewrite ?disj_sidesRB_eq.
  rewrite (disj_sidesIB_eq _ _ _ _ Hk), disj_sidesB_ref, p_in_sidesB_ref, p_kdisj_apart12B_eq. reflexivity.
Qed.
(* [comment removed for export] *)
Definition num_apartB (br1 br2 : option (Z * Z)) (k1 n1 k2 n2 : Z) : bool :=
  match br1, br2 with
  | Some (lo1, hi1), Some (lo2, hi2) => (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
  | _, _ => false
  end.
Lemma num_apartB_full : forall bc b1 k1 n1 b2 k2 n2,
  num_apartB (base_rangeB bc b1) (base_rangeB bc b2) k1 n1 k2 n2 = true -> ranges_apartB bc b1 k1 n1 b2 k2 n2 = true.
Proof. intros bc b1 k1 n1 b2 k2 n2 H. unfold ranges_apartB. unfold num_apartB in H. rewrite H. reflexivity. Qed.
Fixpoint log_lookupPB_go (bc : bctx) (br1 : option (Z * Z)) (log : list sentry) (osp : option sprep) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      match rel_litD rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupPB_go bc br1 rest osp rb rk n sx hints acc
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          if Nat.leb w 8 then
            if num_apartB br1 (base_rangeB bc kb) rk (Z.of_nat n) kk (Z.of_nat w) then log_lookupPB_go bc br1 rest osp rb rk n sx hints acc else
            let sp := match osp with Some sp => sp | None => mk_sprepB bc rb rk (elen n) end in
            if ranges_apart_pB bc sp rb rk (elen n) kb kk (elen w)
            then log_lookupPB_go bc br1 rest (Some sp) rb rk n sx hints acc
            else
            match hints with
            | false :: _ => LStuck
            | _ => log_lookupPB_go bc br1 rest (Some sp) rb rk n sx (tl hints)
                     (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
            end
          else
          if ranges_apartB bc rb rk (Z.of_nat n) kb kk (Z.of_nat w)
          then log_lookupPB_go bc br1 rest osp rb rk n sx hints acc
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupPB_go bc br1 rest osp rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
          end
      end
  end.
Definition log_lookupPBr (bc : bctx) (br : option (Z * Z)) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) : lres :=
  if Nat.leb n 8 then log_lookupPB_go bc br log None rb rk n sx hints acc else log_lookupB bc log rb rk n sx hints acc.
Definition log_lookupPB (bc : bctx) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) : lres :=
  log_lookupPBr bc (base_rangeB bc rb) log rb rk n sx hints acc.
Lemma log_lookupPB_go_eq : forall bc rb rk n sx, bc_kdi bc = mk_kdi (bc_fk bc) -> Nat.leb n 8 = true -> forall log osp hints acc,
  (osp = None \/ osp = Some (mk_sprepB bc rb rk (elen n))) ->
  log_lookupPB_go bc (base_rangeB bc rb) log osp rb rk n sx hints acc = log_lookupB bc log rb rk n sx hints acc.
Proof.
  intros bc rb rk n sx Hk Hn log. induction log as [|[[kb kk] w v] rest IH]; intros osp hints acc Ho; [reflexivity|].
  cbn [log_lookupPB_go log_lookupB].
  destruct (rel_litD rb rk (Z.of_nat n) kb kk (Z.of_nat w)); try reflexivity.
  - apply IH. exact Ho.
  - destruct (Nat.leb w 8) eqn:Hw.
    + destruct (num_apartB (base_rangeB bc rb) (base_rangeB bc kb) rk (Z.of_nat n) kk (Z.of_nat w)) eqn:HN.
      { rewrite (num_apartB_full _ _ _ _ _ _ _ HN). apply IH. exact Ho. }
      assert (Hsp : match osp with Some sp => sp | None => mk_sprepB bc rb rk (elen n) end = mk_sprepB bc rb rk (elen n)).
      { destruct Ho as [->| ->]; reflexivity. }
      cbv zeta. rewrite Hsp. rewrite (p_ranges_apart_pB_lit bc rb rk n kb kk w Hk Hn Hw).
      destruct (ranges_apartB bc rb rk (Z.of_nat n) kb kk (Z.of_nat w)).
      * apply IH. right. reflexivity.
      * destruct hints as [|[|] hs]; try reflexivity; apply IH; right; reflexivity.
    + destruct (ranges_apartB bc rb rk (Z.of_nat n) kb kk (Z.of_nat w)).
      * apply IH. exact Ho.
      * destruct hints as [|[|] hs]; try reflexivity; apply IH; exact Ho.
Qed.
Lemma log_lookupPB_eq : forall bc log rb rk n sx hints acc, bc_kdi bc = mk_kdi (bc_fk bc) ->
  log_lookupPB bc log rb rk n sx hints acc = log_lookupB bc log rb rk n sx hints acc.
Proof.
  intros bc log rb rk n sx hints acc Hk. unfold log_lookupPB, log_lookupPBr. destruct (Nat.leb n 8) eqn:Hn; [|reflexivity].
  apply log_lookupPB_go_eq; [exact Hk | exact Hn | left; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma img_bytes_fast_eq' : forall segs a n, IMF.img_bytes_fast segs a n = img_bytes segs a n.
Proof. intros segs a n. rewrite IMF.img_bytes_fast_eq. reflexivity. Qed.
#[export] Hint Rewrite img_bytes_fast_eq' : bceq.

Fixpoint know_lookupA0B (bc : bctx) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  let know_lookup := know_lookupA0B bc in
  match kn with
  | [] => LMiss acc hints
  | K :: rest =>
      match K with
      | KWord (SA kb kk) w v =>
          match rel_litD rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
          | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
          | _ => know_lookup segs rest rb rk n sx hints acc
          end
      | KZero (SA kb kk) len =>
          match len with
          | ELit l0 =>
              match rel_litD rb rk (Z.of_nat n) kb kk (zmod64 l0) with
              | RInside _ => LHit (ELit 0) acc hints
              | RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
              | RUnknown =>
                  (* [comment removed for export] *)
                  if xinsideB bc rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
                  match hints with
                  | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
          | _ =>
              if xinsideB bc rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
              match hints with
              | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
              | false :: hs => know_lookup segs rest rb rk n sx hs acc
              | [] => know_lookup segs rest rb rk n sx [] acc
              end
          end
      | KFill (SA kb kk) len c =>
          (* [comment removed for export] *)
          let hit := fill_lit sx n c in
          match len with
          | ELit l0 =>
              match rel_litD rb rk (Z.of_nat n) kb kk (zmod64 l0) with
              | RInside _ => LHit hit acc hints
              | RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
              | RUnknown =>
                  if xinsideB bc rb rk (elen n) kb kk len then LHit hit acc hints else
                  match hints with
                  | true :: hs => LHit hit (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
          | _ =>
              if xinsideB bc rb rk (elen n) kb kk len then LHit hit acc hints else
              match hints with
              | true :: hs => LHit hit (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
              | false :: hs => know_lookup segs rest rb rk n sx hs acc
              | [] => know_lookup segs rest rb rk n sx [] acc
              end
          end
      | KUnk _ _ => know_lookup segs rest rb rk n sx hints acc   (* [comment removed for export] *)
      | KBlob (SA kb kk) len k =>
          if expr_eqb rb kb then
            (* [comment removed for export] *)
            if Z.leb kk rk then
              match len with
              | ELit l0 =>
                  if Z.leb (rk + Z.of_nat n) (kk + (zmod64 l0))
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else if Z.leb (kk + (zmod64 l0)) rk then know_lookup segs rest rb rk n sx hints acc
                  else LStuck
              | _ =>
                  (* [comment removed for export] *)
                  if match erangeB bc len with   (* [comment removed for export] *)
                     | Some (lo, _) => Z.leb (rk + Z.of_nat n) (kk + lo)
                     | None => false
                     end
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else
                  match hints with
                  | true :: hs => LHit (EBlob sx k (rk - kk) n)
                                    (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
            else know_lookup segs rest rb rk n sx hints acc
          else know_lookup segs rest rb rk n sx hints acc
      | KImg lo hi =>
          match rb with
          | ELit 0 =>
              if (Z.leb lo rk && Z.leb (rk + Z.of_nat n) hi)%bool then
                match IMF.img_bytes_fast segs rk n with   (* [comment removed for export] *)
                | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                | None => LStuck
                end
              else know_lookup segs rest rb rk n sx hints acc
          | _ => know_lookup segs rest rb rk n sx hints acc
          end
      | KAlign _ _ => know_lookup segs rest rb rk n sx hints acc
      | KRange _ _ _ => know_lookup segs rest rb rk n sx hints acc
      | KWr _ _ => know_lookup segs rest rb rk n sx hints acc
      | KDisj _ _ _ _ => know_lookup segs rest rb rk n sx hints acc
      end
  end.

Fixpoint know_lookupA0G (XI : expr -> Z -> expr -> expr -> Z -> expr -> bool) (ER : expr -> option (Z * Z)) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  let know_lookup := know_lookupA0G XI ER in
  match kn with
  | [] => LMiss acc hints
  | K :: rest =>
      match K with
      | KWord (SA kb kk) w v =>
          match rel_litD rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
          | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
          | _ => know_lookup segs rest rb rk n sx hints acc
          end
      | KZero (SA kb kk) len =>
          match len with
          | ELit l0 =>
              match rel_litD rb rk (Z.of_nat n) kb kk (zmod64 l0) with
              | RInside _ => LHit (ELit 0) acc hints
              | RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
              | RUnknown =>
                  (* [comment removed for export] *)
                  if XI rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
                  match hints with
                  | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
          | _ =>
              if XI rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
              match hints with
              | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
              | false :: hs => know_lookup segs rest rb rk n sx hs acc
              | [] => know_lookup segs rest rb rk n sx [] acc
              end
          end
      | KFill (SA kb kk) len c =>
          (* [comment removed for export] *)
          let hit := fill_lit sx n c in
          match len with
          | ELit l0 =>
              match rel_litD rb rk (Z.of_nat n) kb kk (zmod64 l0) with
              | RInside _ => LHit hit acc hints
              | RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
              | RUnknown =>
                  if XI rb rk (elen n) kb kk len then LHit hit acc hints else
                  match hints with
                  | true :: hs => LHit hit (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
          | _ =>
              if XI rb rk (elen n) kb kk len then LHit hit acc hints else
              match hints with
              | true :: hs => LHit hit (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
              | false :: hs => know_lookup segs rest rb rk n sx hs acc
              | [] => know_lookup segs rest rb rk n sx [] acc
              end
          end
      | KUnk _ _ => know_lookup segs rest rb rk n sx hints acc   (* [comment removed for export] *)
      | KBlob (SA kb kk) len k =>
          if expr_eqb rb kb then
            (* [comment removed for export] *)
            if Z.leb kk rk then
              match len with
              | ELit l0 =>
                  if Z.leb (rk + Z.of_nat n) (kk + (zmod64 l0))
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else if Z.leb (kk + (zmod64 l0)) rk then know_lookup segs rest rb rk n sx hints acc
                  else LStuck
              | _ =>
                  (* [comment removed for export] *)
                  if match ER len with   (* [comment removed for export] *)
                     | Some (lo, _) => Z.leb (rk + Z.of_nat n) (kk + lo)
                     | None => false
                     end
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else
                  match hints with
                  | true :: hs => LHit (EBlob sx k (rk - kk) n)
                                    (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
            else know_lookup segs rest rb rk n sx hints acc
          else know_lookup segs rest rb rk n sx hints acc
      | KImg lo hi =>
          match rb with
          | ELit 0 =>
              if (Z.leb lo rk && Z.leb (rk + Z.of_nat n) hi)%bool then
                match IMF.img_bytes_fast segs rk n with   (* [comment removed for export] *)
                | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                | None => LStuck
                end
              else know_lookup segs rest rb rk n sx hints acc
          | _ => know_lookup segs rest rb rk n sx hints acc
          end
      | KAlign _ _ => know_lookup segs rest rb rk n sx hints acc
      | KRange _ _ _ => know_lookup segs rest rb rk n sx hints acc
      | KWr _ _ => know_lookup segs rest rb rk n sx hints acc
      | KDisj _ _ _ _ => know_lookup segs rest rb rk n sx hints acc
      end
  end.

(* [comment removed for export] *)
Lemma know_lookupA0G_B : forall bc segs kn rb rk n sx hints acc,
  know_lookupA0G (xinsideB bc) (erangeB bc) segs kn rb rk n sx hints acc = know_lookupA0B bc segs kn rb rk n sx hints acc.
Proof.
  intros bc segs kn. induction kn as [|K rest IH]; intros; [reflexivity|].
  cbn [know_lookupA0G know_lookupA0B]. cbv zeta. rewrite ?IH.
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a nn|a1 n1 a2 n2|[kb kk] len fc|[kb kk] len]; try reflexivity;
    repeat match goal with
           | |- context [match ?x with _ => _ end] => destruct x; rewrite ?IH; try reflexivity
           end.
Qed.
Lemma know_lookupA0G_ext : forall XI1 XI2 ER segs rb,
  (forall k1 n1 b2 k2 n2, XI1 rb k1 n1 b2 k2 n2 = XI2 rb k1 n1 b2 k2 n2) ->
  forall kn rk n sx hints acc,
  know_lookupA0G XI1 ER segs kn rb rk n sx hints acc = know_lookupA0G XI2 ER segs kn rb rk n sx hints acc.
Proof.
  intros XI1 XI2 ER segs rb HX kn. induction kn as [|K rest IH]; intros; [reflexivity|].
  cbn [know_lookupA0G]. cbv zeta. rewrite ?HX, ?IH.
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a nn|a1 n1 a2 n2|[kb kk] len fc|[kb kk] len]; try reflexivity;
    repeat match goal with
           | |- context [match ?x with _ => _ end] => destruct x; rewrite ?HX, ?IH; try reflexivity
           end.
Qed.

Definition know_lookupAB (bc : bctx) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match know_lookupA0B bc segs kn rb rk n sx hints acc with
  | LMiss acc' hints' =>
      match know_bytes_lit segs kn rb rk n with
      | Some bs => LHit (lit_of_bytes sx n bs) acc' hints'
      | None => LMiss acc' hints'
      end
  | r => r
  end.

Definition sym_readB (segs : list Segment) (ss : sym_state) (bc : bctx) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  match log_lookupB bc (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] with
  | LStuck => None
  | LHit v scs hints =>
      Some (extKB bc v, flat_scB bc a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss)
  | LMiss scs hints =>
      match know_lookupAB bc segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
      | LStuck => None
      | LHit v scs' hints' =>
          Some (extKB bc v, flat_scB bc a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss)
      | LMiss scs' hints' =>
          (* [comment removed for export] *)
          let i := s_next ss in
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          Some (rv, flat_scB bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i)
      end
  end.

Definition sym_stepB (bc : bctx) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | OpImm op rd rs imm => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm op rd rs sh => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op op rd rs1 rs2 => SOk (sset ss rd (mkAluKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | OpImm32 rd rs imm => SOk (sset ss rd (mkAluwKB bc ALU_ADD (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op32 op rd rs1 rs2 => SOk (sset ss rd (mkAluwKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul op rd rs1 rs2 => SOk (sset ss rd (mkMdKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul32 op rd rs1 rs2 => SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
  | Lui rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12)))) (p + 4)) [] scr
  | Auipc rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12 + p)))) (p + 4)) [] scr
  | Jal rd imm => SOk (sset ss rd (ELit (p + 4)) (bv_unsigned (Z_to_bv 64 (p + bv_signed imm)))) [] scr
  | Jalr rd rs1 imm =>
      match conc_exprB bc (g rs1) with
      | ELit z => SOk (sset ss rd (ELit (p + 4)) (Z.land (bv_wrap 64 z + bv_signed imm) (-2) mod 2^64)) [] scr
      | _ => SStop
      end
  | Branch c rs1 rs2 imm =>
      let tk := bv_unsigned (Z_to_bv 64 (p + bv_signed imm)) in
      let a := g rs1 in let b := g rs2 in
      match match decide_branchB bc c a b with
            | Some t => Some t
            | None => match decide_branchB bc c (conc_exprB bc a) (conc_exprB bc b) with
                      | Some t => Some t
                      | None => enum_branchB bc c a b
                      end
            end with
      | Some t => SOk (sjump ss (if t then tk else p + 4)) [] scr
      | None =>
          match sc_dirs scr with
          | [] => SStop
          | t :: dirs' =>
              SOk (sjump ss (if t then tk else p + 4)) [SCBr t c a b]
                  (SCR dirs' (sc_reads scr) (sc_hints scr))
          end
      end
  | Fence _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | FenceI _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Load sz sx rd rs imm =>
      let n := msize_bytes sz in
      (* [comment removed for export] *)
      let sx' := match sz with SZ8 => false | _ => sx end in
      let a := to_saddrKB bc (g rs) (bv_signed imm) in
      match sym_readB segs ss bc scr a n sx' with
      | None => SStop
      | Some (v, scs, scr', nx') =>
          SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                   (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
      end
  | Store sz rs1 rs2 imm =>
      let n := msize_bytes sz in
      let a := to_saddrKB bc (g rs1) (bv_signed imm) in
      match resv_inval (s_resv ss) a with
      | None => SStop
      | Some r' =>
          SOk (SSR (p + 4) (s_regs ss) (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) r')
              (flat_scB bc a n ++ storeok_scB bc a n) scr
      end
  (* [comment removed for export] *)
  | Lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match sym_readB segs ss bc scr a n (amo_sx wd) with
        | None => SStop
        | Some (v, scs, scr', nx') =>
            SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                     (s_log ss) (s_know ss) nx' (Some a)) scs scr'
        end
      else SStop
  | Sc wd _ _ rd rs1 rs2 =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs1 in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match s_resv ss with
        | Some r =>
            if saddr_eqb r a then
              SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) (ELit 0))
                       (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) None)
                  (flat_scB bc a n ++ storeok_scB bc a n) scr
            else SStop   (* [comment removed for export] *)
        | None => SStop
        end
      else SStop
  | Amo op wd _ _ rd rs1 rs2 =>
      match amo_aluop op with
      | None => SStop
      | Some aop =>
          let n := msize_bytes (amo_sz wd) in
          let e := g rs1 in
          if amo_alignedbB bc e wd then
            let a := to_saddrKB bc e 0 in
            match resv_inval (s_resv ss) a with
            | None => SStop
            | Some r' =>
                match sym_readB segs ss bc scr a n (amo_sx wd) with
                | None => SStop
                | Some (vold, scs, scr', nx') =>
                    SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) vold)
                             (SE a n (amo_newvalB bc wd aop vold (g rs2)) :: s_log ss) (s_know ss) nx' r')
                        (scs ++ storeok_scB bc a n) scr'
                end
            end
          else SStop
      end
  | _ => SStop
  end.

Definition know_lookupB (segs : list Segment) (bc : bctx) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  know_lookupAB bc segs (bc_fk bc) rb rk n sx hints acc.


Local Open Scope Z_scope.
(* [comment removed for export] *)
Definition gran (a : Z) : Z := Z.shiftr a 12.
Definition is_lit0 (e : expr) : bool := match e with ELit 0 => true | _ => false end.
(* [comment removed for export] *)
Definition lit0_extent (K : kentry) : option (Z * Z) :=
  match K with
  | KWord (SA (ELit 0) kk) w _ => Some (kk, kk + Z.of_nat w)
  | KZero (SA (ELit 0) kk) (ELit l0) => Some (kk, kk + zmod64 l0)
  | KFill (SA (ELit 0) kk) (ELit l0) _ => Some (kk, kk + zmod64 l0)
  | KBlob (SA (ELit 0) kk) (ELit l0) _ => Some (kk, kk + zmod64 l0)
  | KImg lo hi => Some (lo, hi)
  | _ => None
  end.
(* [comment removed for export] *)
Definition ext_fits (s e : Z) : bool := if Z.ltb s e then Z.leb (gran (e - 1) - gran s) 1 else false.
Definition ext_has (s e g : Z) : bool := if Z.eqb g (gran s) then true else Z.eqb g (gran (e - 1)).
(* [comment removed for export] *)
Definition kx_wide0 (K : kentry) : bool :=
  match lit0_extent K with
  | Some (s, e) => negb (ext_fits s e)
  | None =>
      match K with
      | KZero (SA kb _) _ | KFill (SA kb _) _ _ => true      (* [comment removed for export] *)
      | KBlob (SA kb _) _ _ => is_lit0 kb                    (* [comment removed for export] *)
      | _ => false
      end
  end.
(* [comment removed for export] *)
Definition kx_cand0 (g : Z) (K : kentry) : bool :=
  match lit0_extent K with
  | Some (s, e) => if ext_fits s e then ext_has s e g else true
  | None => kx_wide0 K
  end.
(* [comment removed for export] *)
Definition kx_candf (K : kentry) : bool :=
  match K with
  | KWord (SA kb _) _ _ | KBlob (SA kb _) _ _ => negb (is_lit0 kb)
  | KZero _ _ | KFill _ _ _ => true
  | _ => false
  end.
(* [comment removed for export] *)
Definition kx_gkey (g : Z) : positive := match g with Z0 => xH | Zpos p => xO p | Zneg p => xI p end.
Record kix : Type := KX {
  kx_kn : list kentry;                              (* [comment removed for export] *)
  kx_w0 : list (positive * kentry);                 (* [comment removed for export] *)
  kx_gran : ptree (list (positive * kentry));       (* [comment removed for export] *)
  kx_wf : list kentry                               (* [comment removed for export] *)
}.
Definition kx_bucket (t : ptree (list (positive * kentry))) (g : Z) : list (positive * kentry) :=
  match pt_get t (kx_gkey g) with Some b => b | None => [] end.
Definition kx_add (g : Z) (x : positive * kentry) (t : ptree (list (positive * kentry))) : ptree (list (positive * kentry)) :=
  pt_set (kx_gkey g) (x :: kx_bucket t g) t.
Fixpoint kx_build (kn : list kentry) (i : positive) : list (positive * kentry) * ptree (list (positive * kentry)) * list kentry :=
  match kn with
  | [] => ([], PTLeaf, [])
  | K :: rest =>
      let '(w0, gr, wf) := kx_build rest (Pos.succ i) in
      let wf' := if kx_candf K then K :: wf else wf in
      match lit0_extent K with
      | Some (s, e) =>
          if ext_fits s e then
            let g1 := gran s in let g2 := gran (e - 1) in
            let gr1 := kx_add g1 (i, K) gr in
            (w0, (if Z.eqb g1 g2 then gr1 else kx_add g2 (i, K) gr1), wf')
          else ((i, K) :: w0, gr, wf')
      | None => if kx_wide0 K then ((i, K) :: w0, gr, wf') else (w0, gr, wf')
      end
  end.
Definition mk_kix (kn : list kentry) : kix :=
  let r := kx_build kn xH in KX kn (fst (fst r)) (snd (fst r)) (snd r).
(* [comment removed for export] *)
Fixpoint kx_merge (l1 : list (positive * kentry)) : list (positive * kentry) -> list kentry :=
  match l1 with
  | [] => fun l2 => List.map snd l2
  | (p1, K1) :: r1 =>
      fix go (l2 : list (positive * kentry)) : list kentry :=
        match l2 with
        | [] => K1 :: List.map snd r1
        | (p2, K2) :: r2 => if Pos.ltb p1 p2 then K1 :: kx_merge r1 l2 else K2 :: go r2
        end
  end.
Definition kx_select (kx : kix) (rb : expr) (rk : Z) : list kentry :=
  if is_lit0 rb then kx_merge (kx_bucket (kx_gran kx) (gran rk)) (kx_w0 kx)
  else kx_wf kx.

Definition know_lookupA0I (bc : bctx) (kx : kix) (segs : list Segment) (rb : expr) (rk : Z)
           (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match hints, n with
  | [], S _ => know_lookupA0B bc segs (kx_select kx rb rk) rb rk n sx [] acc
  | _, _ => know_lookupA0B bc segs (kx_kn kx) rb rk n sx hints acc
  end.

(* [comment removed for export] *)
Lemma gran_div : forall a, gran a = a / 4096.
Proof. intros a. unfold gran. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma gran_mono : forall a b, a <= b -> gran a <= gran b.
Proof. intros a b H. rewrite !gran_div. apply Z.div_le_mono; lia. Qed.
Lemma gran_between : forall s e x,
  s <= x -> x < e -> ext_fits s e = true -> ext_has s e (gran x) = true.
Proof.
  intros s e x Hs He Hf. unfold ext_fits, ext_has in *.
  destruct (Z.ltb s e); [|discriminate]. apply Z.leb_le in Hf.
  pose proof (gran_mono s x Hs) as A. pose proof (gran_mono x (e - 1) ltac:(lia)) as B.
  destruct (Z.eqb_spec (gran x) (gran s)); [reflexivity|].
  destruct (Z.eqb_spec (gran x) (gran (e - 1))); [reflexivity|]. exfalso. lia.
Qed.
Lemma kx_aluop_eqb_refl : forall a, aluop_eqb a a = true. Proof. intros []; reflexivity. Qed.
Lemma kx_mulop_eqb_refl : forall a, mulop_eqb a a = true. Proof. intros []; reflexivity. Qed.
Lemma kx_expr_eqb_refl : forall x, expr_eqb x x = true.
Proof.
  induction x; cbn -[Z.eqb Nat.eqb]; rewrite ?kx_aluop_eqb_refl, ?kx_mulop_eqb_refl, ?IHx, ?IHx1, ?IHx2, ?Z.eqb_refl, ?Nat.eqb_refl, ?Bool.eqb_reflx; reflexivity.
Qed.

Lemma rel_lit_same : forall rb rk rn kk kl,
  rel_lit rb rk rn rb kk kl =
    if (Z.leb kk rk && Z.leb (rk + rn) (kk + kl))%bool then RInside (rk - kk)
    else if (Z.leb (rk + rn) kk || Z.leb (kk + kl) rk)%bool then RDisjoint else RPartial.
Proof. intros. unfold rel_lit. rewrite kx_expr_eqb_refl. reflexivity. Qed.

Lemma rel_lit_other : forall rb rk rn kb kk kl,
  expr_eqb rb kb = false -> rel_lit rb rk rn kb kk kl = RUnknown.
Proof. intros rb rk rn kb kk kl H. unfold rel_lit. rewrite H. reflexivity. Qed.

Lemma is_lit0_eqb : forall rb kb, is_lit0 kb = true -> expr_eqb rb kb = is_lit0 rb.
Proof.
  intros rb kb H. destruct kb as [z| | | | | | |]; try discriminate. cbn in H.
  destruct z; try discriminate.
  destruct rb as [z'| | | | | | |]; cbn; try reflexivity; destruct z'; reflexivity.
Qed.
Lemma expr_eqb_lit0_l : forall kb, expr_eqb (ELit 0) kb = is_lit0 kb.
Proof. intros kb. destruct kb as [z| | | | | | |]; cbn; try reflexivity; destruct z; reflexivity. Qed.
Lemma is_lit0_true : forall e, is_lit0 e = true -> e = ELit 0.
Proof. intros e H. destruct e as [z| | | | | | |]; try discriminate. cbn in H. destruct z; try discriminate. reflexivity. Qed.

(* [comment removed for export] *)
Lemma know_lookupA0B_skip0 : forall bc segs K rest rk n sx acc,
  kx_cand0 (gran rk) K = false ->
  know_lookupA0B bc segs (K :: rest) (ELit 0) rk (S n) sx [] acc = know_lookupA0B bc segs rest (ELit 0) rk (S n) sx [] acc.
Proof.
  intros bc segs K rest rk n sx acc HC.
  cbn [know_lookupA0B]. rewrite ?rel_litD_feq. rewrite ?zmod64_eq.
  unfold kx_cand0, kx_wide0 in HC.
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len];
    cbn [lit0_extent] in HC; rewrite ?zmod64_eq in HC; try reflexivity.
  - (* [comment removed for export] *)
    destruct (is_lit0 kb) eqn:L.
    + apply is_lit0_true in L. subst kb. cbn [lit0_extent] in HC.
      rewrite rel_lit_same.
      destruct (Z.leb kk rk && Z.leb (rk + Z.of_nat (S n)) (kk + Z.of_nat w))%bool eqn:E.
      * exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
        destruct (ext_fits kk (kk + Z.of_nat w)) eqn:F; [|discriminate].
        rewrite (gran_between kk (kk + Z.of_nat w) rk) in HC; [discriminate|lia|lia|exact F].
      * destruct (Z.leb (rk + Z.of_nat (S n)) kk || Z.leb (kk + Z.of_nat w) rk)%bool; reflexivity.
    + destruct kb as [z| | | | | | |]; try (rewrite rel_lit_other by reflexivity; reflexivity).
      cbn in L. destruct z; try discriminate; rewrite rel_lit_other by reflexivity; reflexivity.
  - (* [comment removed for export] *)
    destruct (is_lit0 kb) eqn:L.
    + apply is_lit0_true in L. subst kb. destruct len as [l0| | | | | | |]; cbn [lit0_extent] in HC; rewrite ?zmod64_eq in HC; rewrite ?zmod64_eq; try discriminate.
      rewrite rel_lit_same.
      destruct (Z.leb kk rk && Z.leb (rk + Z.of_nat (S n)) (kk + l0 mod 2 ^ 64))%bool eqn:E.
      * exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
        destruct (ext_fits kk (kk + l0 mod 2 ^ 64)) eqn:F; [|discriminate].
        rewrite (gran_between kk (kk + l0 mod 2 ^ 64) rk) in HC; [discriminate|lia|lia|exact F].
      * destruct (Z.leb (rk + Z.of_nat (S n)) kk || Z.leb (kk + l0 mod 2 ^ 64) rk)%bool; reflexivity.
    + destruct kb as [z| | | | | | |]; cbn [lit0_extent] in HC; try (destruct len; discriminate).
      cbn in L. destruct z; try discriminate; destruct len; discriminate.
  - (* [comment removed for export] *)
    destruct (is_lit0 kb) eqn:L.
    + apply is_lit0_true in L. subst kb. destruct len as [l0| | | | | | |]; cbn [lit0_extent is_lit0] in HC; rewrite ?zmod64_eq in HC; rewrite ?zmod64_eq; try discriminate.
      rewrite kx_expr_eqb_refl.
      destruct (ext_fits kk (kk + l0 mod 2 ^ 64)) eqn:F; [|discriminate].
      destruct (Z.leb_spec kk rk) as [H1|H1]; [|reflexivity].
      destruct (Z.leb_spec (rk + Z.of_nat (S n)) (kk + (l0 mod 2 ^ 64))) as [H2|H2].
      * exfalso. rewrite (gran_between kk (kk + l0 mod 2 ^ 64) rk) in HC; [discriminate|lia|lia|exact F].
      * destruct (Z.leb_spec (kk + (l0 mod 2 ^ 64)) rk) as [H3|H3]; [reflexivity|].
        exfalso. rewrite (gran_between kk (kk + l0 mod 2 ^ 64) rk) in HC; [discriminate|lia|lia|exact F].
    + rewrite expr_eqb_lit0_l, L. reflexivity.
  - (* [comment removed for export] *)
    destruct (ext_fits lo hi) eqn:F; [|discriminate].
    destruct (Z.leb lo rk && Z.leb (rk + Z.of_nat (S n)) hi)%bool eqn:E; [|reflexivity].
    exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    rewrite (gran_between lo hi rk) in HC; [discriminate|lia|lia|exact F].
  - (* [comment removed for export] *)
    destruct (is_lit0 kb) eqn:L.
    + apply is_lit0_true in L. subst kb. destruct len as [l0| | | | | | |]; cbn [lit0_extent] in HC; rewrite ?zmod64_eq in HC; rewrite ?zmod64_eq; try discriminate.
      cbv zeta. rewrite rel_lit_same.
      destruct (Z.leb kk rk && Z.leb (rk + Z.of_nat (S n)) (kk + l0 mod 2 ^ 64))%bool eqn:E.
      * exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
        destruct (ext_fits kk (kk + l0 mod 2 ^ 64)) eqn:F; [|discriminate].
        rewrite (gran_between kk (kk + l0 mod 2 ^ 64) rk) in HC; [discriminate|lia|lia|exact F].
      * destruct (Z.leb (rk + Z.of_nat (S n)) kk || Z.leb (kk + l0 mod 2 ^ 64) rk)%bool; reflexivity.
    + destruct kb as [z| | | | | | |]; cbn [lit0_extent] in HC; try (destruct len; discriminate).
      cbn in L. destruct z; try discriminate; destruct len; discriminate.
Qed.

(* [comment removed for export] *)
Lemma know_lookupA0B_skipf : forall bc segs K rest rb rk n sx acc,
  is_lit0 rb = false -> kx_candf K = false ->
  know_lookupA0B bc segs (K :: rest) rb rk n sx [] acc = know_lookupA0B bc segs rest rb rk n sx [] acc.
Proof.
  intros bc segs K rest rb rk n sx acc Hrb HC.
  cbn [know_lookupA0B]. rewrite ?rel_litD_feq. unfold kx_candf in HC.
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len];
    try reflexivity; try discriminate.
  - (* [comment removed for export] *) destruct (is_lit0 kb) eqn:L; [|discriminate].
    rewrite rel_lit_other; [reflexivity|]. rewrite (is_lit0_eqb rb kb L). exact Hrb.
  - (* [comment removed for export] *) destruct (is_lit0 kb) eqn:L; [|discriminate].
    rewrite (is_lit0_eqb rb kb L), Hrb. reflexivity.
  - (* [comment removed for export] *) destruct rb as [z| | | | | | |]; try reflexivity. cbn in Hrb. destruct z; try reflexivity. discriminate.
Qed.

(* [comment removed for export] *)
Lemma know_lookupA0B_filter0 : forall bc segs l rk n sx acc,
  know_lookupA0B bc segs (List.filter (kx_cand0 (gran rk)) l) (ELit 0) rk (S n) sx [] acc
  = know_lookupA0B bc segs l (ELit 0) rk (S n) sx [] acc.
Proof.
  intros bc segs l rk n sx. induction l as [|K rest IH]; intros acc; [reflexivity|].
  cbn [List.filter]. destruct (kx_cand0 (gran rk) K) eqn:HC.
  - (* [comment removed for export] *)
    cbn [know_lookupA0B]. rewrite !IH.
    destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; try reflexivity.
  - rewrite know_lookupA0B_skip0 by exact HC. apply IH.
Qed.
Lemma know_lookupA0B_filterf : forall bc segs l rb rk n sx acc,
  is_lit0 rb = false ->
  know_lookupA0B bc segs (List.filter kx_candf l) rb rk n sx [] acc = know_lookupA0B bc segs l rb rk n sx [] acc.
Proof.
  intros bc segs l rb rk n sx acc Hrb. revert acc. induction l as [|K rest IH]; intros acc; [reflexivity|].
  cbn [List.filter]. destruct (kx_candf K) eqn:HC.
  - cbn [know_lookupA0B]. rewrite !IH.
    destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; try reflexivity.
  - rewrite know_lookupA0B_skipf by assumption. apply IH.
Qed.


(* [comment removed for export] *)
Fixpoint tagged (kn : list kentry) (i : positive) : list (positive * kentry) :=
  match kn with [] => [] | K :: rest => (i, K) :: tagged rest (Pos.succ i) end.
Definition all_gt (i : positive) (l : list (positive * kentry)) : Prop := Forall (fun t => (i < fst t)%positive) l.

Lemma filter_tagged_gt : forall P kn i j, (j < i)%positive -> all_gt j (List.filter P (tagged kn i)).
Proof.
  intros P kn. induction kn as [|K rest IH]; intros i j Hj; cbn [tagged List.filter]; [constructor|].
  destruct (P (i, K)).
  - constructor; [cbn; lia|]. apply IH. lia.
  - apply IH. lia.
Qed.

Lemma kx_merge_nil_l : forall l2, kx_merge [] l2 = List.map snd l2.
Proof. reflexivity. Qed.
Lemma kx_merge_cons_l : forall p K r1 l2,
  all_gt p l2 -> kx_merge ((p, K) :: r1) l2 = K :: kx_merge r1 l2.
Proof.
  intros p K r1 l2 H. destruct l2 as [|[p2 K2] r2]; cbn [kx_merge].
  - destruct r1 as [|[? ?] ?]; reflexivity.
  - apply Forall_inv in H. cbn in H. destruct (Pos.ltb_spec p p2); [reflexivity|lia].
Qed.
Lemma kx_merge_cons_r : forall p K l1 r2,
  all_gt p l1 -> kx_merge l1 ((p, K) :: r2) = K :: kx_merge l1 r2.
Proof.
  intros p K l1 r2 H. destruct l1 as [|[p1 K1] r1]; cbn [kx_merge List.map snd]; [reflexivity|].
  apply Forall_inv in H. cbn in H. destruct (Pos.ltb_spec p1 p); [lia|reflexivity].
Qed.

(* [comment removed for export] *)
Lemma kx_merge_filters : forall (P Q : kentry -> bool) kn i,
  (forall K, P K = true -> Q K = false) ->
  kx_merge (List.filter (fun t => P (snd t)) (tagged kn i)) (List.filter (fun t => Q (snd t)) (tagged kn i))
  = List.filter (fun K => P K || Q K) kn.
Proof.
  intros P Q kn. induction kn as [|K rest IH]; intros i HPQ; [reflexivity|].
  cbn [tagged List.filter snd].
  destruct (P K) eqn:HP.
  - rewrite (HPQ K HP). cbn [orb]. rewrite kx_merge_cons_l; [rewrite IH; [reflexivity|exact HPQ]|].
    apply filter_tagged_gt. lia.
  - destruct (Q K) eqn:HQ; cbn [orb].
    + rewrite kx_merge_cons_r; [rewrite IH; [reflexivity|exact HPQ]|]. apply filter_tagged_gt. lia.
    + apply IH. exact HPQ.
Qed.

(* [comment removed for export] *)
Definition narrow_in (g : Z) (K : kentry) : bool :=
  match lit0_extent K with
  | Some (s, e) => if ext_fits s e then ext_has s e g else false
  | None => false
  end.
Lemma kx_cand0_split : forall g K, kx_cand0 g K = (narrow_in g K || kx_wide0 K).
Proof.
  intros g K. unfold kx_cand0, narrow_in, kx_wide0.
  destruct (lit0_extent K) as [[s e]|]; [|reflexivity].
  destruct (ext_fits s e); cbn [negb orb]; [rewrite Bool.orb_false_r|]; reflexivity.
Qed.
Lemma narrow_not_wide : forall g K, narrow_in g K = true -> kx_wide0 K = false.
Proof.
  intros g K. unfold narrow_in, kx_wide0. destruct (lit0_extent K) as [[s e]|]; [|discriminate].
  destruct (ext_fits s e); [reflexivity|discriminate].
Qed.

Lemma kx_gkey_inj : forall a b, kx_gkey a = kx_gkey b -> a = b.
Proof. intros [|a|a] [|b|b] H; cbn in H; congruence. Qed.
Lemma kx_bucket_add_same : forall g x t, kx_bucket (kx_add g x t) g = x :: kx_bucket t g.
Proof. intros. unfold kx_add, kx_bucket at 1. rewrite pt_gss. reflexivity. Qed.
Lemma kx_bucket_add_other : forall g g' x t, g <> g' -> kx_bucket (kx_add g' x t) g = kx_bucket t g.
Proof.
  intros g g' x t H. unfold kx_add. unfold kx_bucket at 1. rewrite pt_gso; [reflexivity|].
  intros E. apply H. apply kx_gkey_inj. exact E.
Qed.
Lemma kx_bucket_leaf : forall g, kx_bucket PTLeaf g = [].
Proof. intros. unfold kx_bucket. rewrite pt_get_leaf. reflexivity. Qed.

Lemma kx_build_spec : forall kn i w0 gr wf,
  kx_build kn i = (w0, gr, wf) ->
  w0 = List.filter (fun t => kx_wide0 (snd t)) (tagged kn i)
  /\ (forall g, kx_bucket gr g = List.filter (fun t => narrow_in g (snd t)) (tagged kn i))
  /\ wf = List.filter kx_candf kn.
Proof.
  induction kn as [|K rest IH]; intros i w0 gr wf H.
  - cbn in H. injection H as <- <- <-. split; [reflexivity|]. split; [intros g; rewrite kx_bucket_leaf; reflexivity | reflexivity].
  - cbn [kx_build] in H. destruct (kx_build rest (Pos.succ i)) as [[w0' gr'] wf'] eqn:Hb.
    destruct (IH (Pos.succ i) w0' gr' wf' Hb) as (A & B & C). clear IH.
    cbn [tagged List.filter snd].
    assert (NW : forall g, narrow_in g K = match lit0_extent K with Some (s, e) => if ext_fits s e then ext_has s e g else false | None => false end) by reflexivity.
    assert (WD : kx_wide0 K = match lit0_extent K with
                              | Some (s, e) => negb (ext_fits s e)
                              | None => match K with
                                        | KZero (SA kb _) _ | KFill (SA kb _) _ _ => true
                                        | KBlob (SA kb _) _ _ => is_lit0 kb
                                        | _ => false
                                        end
                              end) by reflexivity.
    destruct (lit0_extent K) as [[s e]|] eqn:HE.
    + destruct (ext_fits s e) eqn:HF.
      * (* [comment removed for export] *)
        match type of H with (_, ?G, _) = _ => set (gr1 := G) in H end.
        injection H as <- <- <-. rewrite WD. cbn [negb]. split; [exact A|]. split; [|rewrite C; reflexivity].
        intros g. rewrite NW.
        assert (STEP : kx_bucket gr1 g = if ext_has s e g then (i, K) :: kx_bucket gr' g else kx_bucket gr' g).
        { subst gr1. unfold ext_has. destruct (Z.eqb_spec (gran s) (gran (e - 1))) as [EQ|NE].
          - destruct (Z.eqb_spec g (gran s)) as [->|NE1].
            + rewrite kx_bucket_add_same. reflexivity.
            + rewrite kx_bucket_add_other by exact NE1. destruct (Z.eqb_spec g (gran (e - 1))); [congruence|reflexivity].
          - destruct (Z.eqb_spec g (gran s)) as [->|NE1].
            + rewrite kx_bucket_add_other by exact NE. rewrite kx_bucket_add_same. reflexivity.
            + destruct (Z.eqb_spec g (gran (e - 1))) as [->|NE2].
              * rewrite kx_bucket_add_same. rewrite kx_bucket_add_other by exact NE1. reflexivity.
              * rewrite kx_bucket_add_other by exact NE2. rewrite kx_bucket_add_other by exact NE1. reflexivity. }
        rewrite STEP, B. reflexivity.
      * (* [comment removed for export] *)
        injection H as <- <- <-. rewrite WD. cbn [negb]. split; [rewrite A; reflexivity|]. split; [|rewrite C; reflexivity].
        intros g. rewrite NW, B. reflexivity.
    + clear WD. destruct (kx_wide0 K); injection H as <- <- <-.
      * split; [rewrite A; reflexivity|]. split; [|rewrite C; reflexivity]. intros g. rewrite NW, B. reflexivity.
      * split; [exact A|]. split; [|rewrite C; reflexivity]. intros g. rewrite NW, B. reflexivity.
Qed.

Lemma kx_select_eq : forall kn rb rk,
  kx_select (mk_kix kn) rb rk = if is_lit0 rb then List.filter (kx_cand0 (gran rk)) kn else List.filter kx_candf kn.
Proof.
  intros kn rb rk. unfold kx_select, mk_kix.
  destruct (kx_build kn 1%positive) as [[w0 gr] wf] eqn:Hb. cbn [kx_gran kx_w0 kx_wf fst snd].
  destruct (kx_build_spec kn 1%positive w0 gr wf Hb) as (A & B & C).
  destruct (is_lit0 rb); [|exact C].
  rewrite B, A. rewrite (kx_merge_filters (narrow_in (gran rk)) kx_wide0 kn 1%positive (narrow_not_wide (gran rk))).
  apply filter_ext. intros K. symmetry. apply kx_cand0_split.
Qed.

Theorem know_lookupA0I_eq : forall bc kn segs rb rk n sx hints acc,
  know_lookupA0I bc (mk_kix kn) segs rb rk n sx hints acc = know_lookupA0B bc segs kn rb rk n sx hints acc.
Proof.
  intros bc kn segs rb rk n sx hints acc. unfold know_lookupA0I.
  destruct hints as [|h hs]; [|reflexivity]. destruct n as [|n]; [reflexivity|].
  rewrite kx_select_eq. destruct (is_lit0 rb) eqn:L.
  - apply is_lit0_true in L. subst rb. apply know_lookupA0B_filter0.
  - apply know_lookupA0B_filterf. exact L.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition know_lookupA0Jr (bc : bctx) (br1 : option (Z * Z)) (kx : kix) (segs : list Segment) (rb : expr) (rk : Z)
           (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match hints, n with
  | [], S _ => know_lookupA0G (xinsideRB bc br1) (erangeB bc) segs (kx_select kx rb rk) rb rk n sx [] acc
  | _, _ => know_lookupA0G (xinsideRB bc br1) (erangeB bc) segs (kx_kn kx) rb rk n sx hints acc
  end.
Definition know_lookupA0J (bc : bctx) (kx : kix) (segs : list Segment) (rb : expr) (rk : Z)
           (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  let br1 := base_rangeB bc rb in
  match hints, n with
  | [], S _ => know_lookupA0G (xinsideRB bc br1) (erangeB bc) segs (kx_select kx rb rk) rb rk n sx [] acc
  | _, _ => know_lookupA0G (xinsideRB bc br1) (erangeB bc) segs (kx_kn kx) rb rk n sx hints acc
  end.
Lemma know_lookupA0J_eq : forall bc kx segs rb rk n sx hints acc,
  know_lookupA0J bc kx segs rb rk n sx hints acc = know_lookupA0I bc kx segs rb rk n sx hints acc.
Proof.
  intros. unfold know_lookupA0J, know_lookupA0I. cbv zeta.
  assert (HX : forall k1 n1 b2 k2 n2, xinsideRB bc (base_rangeB bc rb) rb k1 n1 b2 k2 n2 = xinsideB bc rb k1 n1 b2 k2 n2) by (intros; reflexivity).
  destruct hints as [|h hs]; [destruct n as [|n']|];
    rewrite (know_lookupA0G_ext _ _ (erangeB bc) segs rb HX), know_lookupA0G_B; reflexivity.
Qed.

(* [comment removed for export] *)
Definition know_lookupABIr (bc : bctx) (br : option (Z * Z)) (kx : kix) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match know_lookupA0Jr bc br kx segs rb rk n sx hints acc with
  | LMiss acc' hints' =>
      match know_bytes_lit segs kn rb rk n with
      | Some bs => LHit (lit_of_bytes sx n bs) acc' hints'
      | None => LMiss acc' hints'
      end
  | r => r
  end.
Definition flat_scRB (br : option (Z * Z)) (a : saddr) (n : nat) : list sidecond :=
  match br with
  | Some (lo, hi) =>
      if (Z.leb 0 (lo + a_off a) && Z.leb (hi + a_off a + Z.of_nat n) two64)%bool
      then [] else [SCFlat a (elen n)]
  | None => [SCFlat a (elen n)]
  end.
Definition know_lookupABI (bc : bctx) (kx : kix) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match know_lookupA0J bc kx segs rb rk n sx hints acc with
  | LMiss acc' hints' =>
      match know_bytes_lit segs kn rb rk n with
      | Some bs => LHit (lit_of_bytes sx n bs) acc' hints'
      | None => LMiss acc' hints'
      end
  | r => r
  end.
Lemma know_lookupABI_eq : forall bc kn segs,
  know_lookupABI bc (mk_kix kn) segs kn = know_lookupAB bc segs kn.
Proof.
  intros bc kn segs. bcfe. unfold know_lookupABI, know_lookupAB. rewrite know_lookupA0J_eq, know_lookupA0I_eq. reflexivity.
Qed.
Local Close Scope Z_scope.

Definition sym_readBI (segs : list Segment) (ss : sym_state) (bc : bctx) (kx : kix) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  let br := base_rangeB bc (a_base a) in   (* [comment removed for export] *)
  match log_lookupPBr bc br (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] with   (* [comment removed for export] *)
  | LStuck => None
  | LHit v scs hints =>
      Some (extKB bc v, flat_scRB br a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss)
  | LMiss scs hints =>
      match know_lookupABIr bc br kx segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
      | LStuck => None
      | LHit v scs' hints' =>
          Some (extKB bc v, flat_scRB br a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss)
      | LMiss scs' hints' =>
          (* [comment removed for export] *)
          let i := s_next ss in
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          Some (rv, flat_scRB br a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i)
      end
  end.


Definition sym_stepBI (bc : bctx) (kx : kix) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | OpImm op rd rs imm => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm op rd rs sh => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op op rd rs1 rs2 => SOk (sset ss rd (mkAluKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | OpImm32 rd rs imm => SOk (sset ss rd (mkAluwKB bc ALU_ADD (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op32 op rd rs1 rs2 => SOk (sset ss rd (mkAluwKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul op rd rs1 rs2 => SOk (sset ss rd (mkMdKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul32 op rd rs1 rs2 => SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
  | Lui rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12)))) (p + 4)) [] scr
  | Auipc rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12 + p)))) (p + 4)) [] scr
  | Jal rd imm => SOk (sset ss rd (ELit (p + 4)) (bv_unsigned (Z_to_bv 64 (p + bv_signed imm)))) [] scr
  | Jalr rd rs1 imm =>
      match conc_exprB bc (g rs1) with
      | ELit z => SOk (sset ss rd (ELit (p + 4)) (Z.land (bv_wrap 64 z + bv_signed imm) (-2) mod 2^64)) [] scr
      | _ => SStop
      end
  | Branch c rs1 rs2 imm =>
      let tk := bv_unsigned (Z_to_bv 64 (p + bv_signed imm)) in
      let a := g rs1 in let b := g rs2 in
      match match decide_branchB bc c a b with
            | Some t => Some t
            | None => match decide_branchB bc c (conc_exprB bc a) (conc_exprB bc b) with
                      | Some t => Some t
                      | None => enum_branchB bc c a b
                      end
            end with
      | Some t => SOk (sjump ss (if t then tk else p + 4)) [] scr
      | None =>
          match sc_dirs scr with
          | [] => SStop
          | t :: dirs' =>
              SOk (sjump ss (if t then tk else p + 4)) [SCBr t c a b]
                  (SCR dirs' (sc_reads scr) (sc_hints scr))
          end
      end
  | Fence _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | FenceI _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Load sz sx rd rs imm =>
      let n := msize_bytes sz in
      (* [comment removed for export] *)
      let sx' := match sz with SZ8 => false | _ => sx end in
      let a := to_saddrKB bc (g rs) (bv_signed imm) in
      match sym_readBI segs ss bc kx scr a n sx' with
      | None => SStop
      | Some (v, scs, scr', nx') =>
          SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                   (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
      end
  | Store sz rs1 rs2 imm =>
      let n := msize_bytes sz in
      let a := to_saddrKB bc (g rs1) (bv_signed imm) in
      match resv_inval (s_resv ss) a with
      | None => SStop
      | Some r' =>
          SOk (SSR (p + 4) (s_regs ss) (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) r')
              (flat_scB bc a n ++ storeok_scB bc a n) scr
      end
  (* [comment removed for export] *)
  | Lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match sym_readBI segs ss bc kx scr a n (amo_sx wd) with
        | None => SStop
        | Some (v, scs, scr', nx') =>
            SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                     (s_log ss) (s_know ss) nx' (Some a)) scs scr'
        end
      else SStop
  | Sc wd _ _ rd rs1 rs2 =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs1 in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match s_resv ss with
        | Some r =>
            if saddr_eqb r a then
              SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) (ELit 0))
                       (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) None)
                  (flat_scB bc a n ++ storeok_scB bc a n) scr
            else SStop   (* [comment removed for export] *)
        | None => SStop
        end
      else SStop
  | Amo op wd _ _ rd rs1 rs2 =>
      match amo_aluop op with
      | None => SStop
      | Some aop =>
          let n := msize_bytes (amo_sz wd) in
          let e := g rs1 in
          if amo_alignedbB bc e wd then
            let a := to_saddrKB bc e 0 in
            match resv_inval (s_resv ss) a with
            | None => SStop
            | Some r' =>
                match sym_readBI segs ss bc kx scr a n (amo_sx wd) with
                | None => SStop
                | Some (vold, scs, scr', nx') =>
                    SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) vold)
                             (SE a n (amo_newvalB bc wd aop vold (g rs2)) :: s_log ss) (s_know ss) nx' r')
                        (scs ++ storeok_scB bc a n) scr'
                end
            end
          else SStop
      end
  | _ => SStop
  end.


Lemma log_lookupPBr_eq : forall bc log rb rk n sx hints acc,
  log_lookupPBr bc (base_rangeB bc rb) log rb rk n sx hints acc = log_lookupPB bc log rb rk n sx hints acc.
Proof. reflexivity. Qed.
Lemma know_lookupABIr_eq : forall bc kx segs kn rb,
  know_lookupABIr bc (base_rangeB bc rb) kx segs kn rb = know_lookupABI bc kx segs kn rb.
Proof. reflexivity. Qed.
Lemma flat_scRB_eq : forall bc a n, flat_scRB (base_rangeB bc (a_base a)) a n = flat_scB bc a n.
Proof. reflexivity. Qed.
Lemma sym_readBI_eqf : forall segs ss bc, bc_kdi bc = mk_kdi (bc_fk bc) -> sym_readBI segs ss bc (mk_kix (s_know ss)) = sym_readB segs ss bc.
Proof.
  intros segs ss bc Hk. bcfe. unfold sym_readBI, sym_readB. cbv zeta.
  rewrite !log_lookupPBr_eq, ?know_lookupABIr_eq, ?flat_scRB_eq.
  rewrite (log_lookupPB_eq _ _ _ _ _ _ _ _ Hk), know_lookupABI_eq. reflexivity.
Qed.
Lemma sym_stepBI_eq : forall bc segs i ss scr, bc_kdi bc = mk_kdi (bc_fk bc) ->
  sym_stepBI bc (mk_kix (s_know ss)) segs i ss scr = sym_stepB bc segs i ss scr.
Proof. intros bc segs i ss scr Hk. unfold sym_stepBI, sym_stepB. rewrite (sym_readBI_eqf _ _ _ Hk). reflexivity. Qed.

Lemma coeffs_divkB_eqf : forall fk, coeffs_divkB (mkbc fk) = coeffs_divk fk.
Proof.
  intros fk. apply functional_extensionality; intros m. apply functional_extensionality; intros ts. 
  induction ts as [|[k a] rest IH]; intros; bcfe; [reflexivity|].
  cbn [coeffs_divkB coeffs_divk]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite coeffs_divkB_eqf : bceq.
Lemma lin_lowbits_knB_eqf : forall fk, lin_lowbits_knB (mkbc fk) = lin_lowbits_kn fk.
Proof. intros. bcfe. unfold lin_lowbits_knB, lin_lowbits_kn. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_lowbits_knB_eqf : bceq.
Lemma lin_nowrap_lB_eqf : forall fk, lin_nowrap_lB (mkbc fk) = lin_nowrap_l fk.
Proof. intros. bcfe. unfold lin_nowrap_lB, lin_nowrap_l. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_nowrap_lB_eqf : bceq.
Lemma mkSrlB_eqf : forall fk, mkSrlB (mkbc fk) = mkSrl fk.
Proof. intros. bcfe. unfold mkSrlB, mkSrl. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkSrlB_eqf : bceq.
Lemma lowbitsB_eqf : forall fk, lowbitsB (mkbc fk) = lowbits fk.
Proof.
  intros fk. apply functional_extensionality; intros e.
  induction e; bcfe; cbn [lowbitsB lowbits]; rewrite ?IHe1, ?IHe2, ?IHe; autorewrite with bceq; rewrite ?zmod64_feq; reflexivity.
Qed.
#[export] Hint Rewrite lowbitsB_eqf : bceq.
Lemma lsplit_divB_eqf : forall fk, lsplit_divB (mkbc fk) = lsplit_div fk.
Proof.
  intros fk. apply functional_extensionality; intros m. apply functional_extensionality; intros ts. 
  induction ts as [|[k a] rest IH]; intros; bcfe; [reflexivity|].
  cbn [lsplit_divB lsplit_div]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite lsplit_divB_eqf : bceq.
Lemma and_high_splitB_eqf : forall fk, and_high_splitB (mkbc fk) = and_high_split fk.
Proof. intros. bcfe. unfold and_high_splitB, and_high_split. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite and_high_splitB_eqf : bceq.
Lemma and_low_splitB_eqf : forall fk, and_low_splitB (mkbc fk) = and_low_split fk.
Proof. intros. bcfe. unfold and_low_splitB, and_low_split. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite and_low_splitB_eqf : bceq.
Lemma narrow_maskB_eqf : forall fk, narrow_maskB (mkbc fk) = narrow_mask fk.
Proof. intros. bcfe. unfold narrow_maskB, narrow_mask. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite narrow_maskB_eqf : bceq.
Lemma mkAnd0B_eqf : forall fk, mkAnd0B (mkbc fk) = mkAnd0 fk.
Proof. intros. bcfe. unfold mkAnd0B, mkAnd0. autorewrite with bceq. rewrite ?zmod64_feq. reflexivity. Qed.
#[export] Hint Rewrite mkAnd0B_eqf : bceq.
Lemma mkAndB_eqf : forall fk, mkAndB (mkbc fk) = mkAnd fk.
Proof. intros. bcfe. unfold mkAndB, mkAnd. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkAndB_eqf : bceq.
Lemma mkAndKB_eqf : forall fk, mkAndKB (mkbc fk) = mkAndK fk.
Proof. intros. bcfe. unfold mkAndKB, mkAndK. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkAndKB_eqf : bceq.
Lemma or_disjointB_eqf : forall fk, or_disjointB (mkbc fk) = or_disjoint fk.
Proof. intros. bcfe. unfold or_disjointB, or_disjoint. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite or_disjointB_eqf : bceq.
Lemma mkOrB_eqf : forall fk, mkOrB (mkbc fk) = mkOr fk.
Proof. intros. bcfe. unfold mkOrB, mkOr. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkOrB_eqf : bceq.
Lemma conc_tryB_eqf : forall fk, conc_tryB (mkbc fk) = conc_try fk.
Proof.
  intros fk. apply functional_extensionality; intros e. apply functional_extensionality; intros cands. 
  induction cands as [|s rest IH]; intros; bcfe; [reflexivity|].
  cbn [conc_tryB conc_try]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite conc_tryB_eqf : bceq.
Lemma concretizeB_eqf : forall fk, concretizeB (mkbc fk) = concretize fk.
Proof. intros. bcfe. unfold concretizeB, concretize. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite concretizeB_eqf : bceq.
Lemma foldKB_eqf : forall fk, foldKB (mkbc fk) = foldK fk.
Proof. intros. bcfe. unfold foldKB, foldK. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite foldKB_eqf : bceq.
Lemma lin_branchB_eqf : forall fk, lin_branchB (mkbc fk) = lin_branch fk.
Proof. intros. bcfe. unfold lin_branchB, lin_branch, ltuB. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_branchB_eqf : bceq.
Lemma disj_branchB_eqf : forall fk, disj_branchB (mkbc fk) = disj_branch fk.
Proof. intros. bcfe. unfold disj_branchB, disj_branch. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite disj_branchB_eqf : bceq.
Lemma decide_branchB_eqf : forall fk, decide_branchB (mkbc fk) = decide_branch fk.
Proof. intros. bcfe. unfold decide_branchB, decide_branch. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite decide_branchB_eqf : bceq.
Lemma mkSltB_eqf : forall fk, mkSltB (mkbc fk) = mkSlt fk.
Proof. intros. bcfe. unfold mkSltB, mkSlt. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkSltB_eqf : bceq.
Lemma mkAluK0B_eqf : forall fk, mkAluK0B (mkbc fk) = mkAluK0 fk.
Proof. intros. bcfe. unfold mkAluK0B, mkAluK0. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkAluK0B_eqf : bceq.
Lemma mkAluKB_eqf : forall fk, mkAluKB (mkbc fk) = mkAluK fk.
Proof. intros. bcfe. unfold mkAluKB, mkAluK. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkAluKB_eqf : bceq.
Lemma mkMdKB_eqf : forall fk, mkMdKB (mkbc fk) = mkMdK fk.
Proof. intros. bcfe. unfold mkMdKB, mkMdK. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkMdKB_eqf : bceq.
Lemma zband32B_eqf : forall fk, zband32B (mkbc fk) = zband32 fk.
Proof. intros. bcfe. unfold zband32B, zband32. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite zband32B_eqf : bceq.
Lemma mkAluwK0B_eqf : forall fk, mkAluwK0B (mkbc fk) = mkAluwK0 fk.
Proof. intros. bcfe. unfold mkAluwK0B, mkAluwK0. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkAluwK0B_eqf : bceq.
Lemma mkAluwKB_eqf : forall fk, mkAluwKB (mkbc fk) = mkAluwK fk.
Proof. intros. bcfe. unfold mkAluwKB, mkAluwK. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkAluwKB_eqf : bceq.
Lemma extK0B_eqf : forall fk, extK0B (mkbc fk) = extK0 fk.
Proof. intros. bcfe. unfold extK0B, extK0. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite extK0B_eqf : bceq.
Lemma extKB_eqf : forall fk, extKB (mkbc fk) = extK fk.
Proof. intros. bcfe. unfold extKB, extK. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite extKB_eqf : bceq.
Lemma flat_scB_eqf : forall fk, flat_scB (mkbc fk) = flat_sc fk.
Proof. intros. bcfe. unfold flat_scB, flat_sc. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite flat_scB_eqf : bceq.
Lemma wr_coveredB0_eqf : forall fk, wr_coveredB0 (mkbc fk) = wr_covered fk.
Proof.
  intros fk. apply functional_extensionality; intros kn. 
  induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [wr_coveredB0 wr_covered]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
Lemma wr_coveredB_eqf : forall fk, wr_coveredB (mkbc fk) = wr_covered fk.
Proof.
  intros fk. rewrite <- wr_coveredB0_eqf. bcfe. apply wr_coveredB_B0.
Qed.
#[export] Hint Rewrite wr_coveredB_eqf : bceq.
Lemma storeok_scB_eqf : forall fk, storeok_scB (mkbc fk) = storeok_sc fk.
Proof. intros. bcfe. unfold storeok_scB, storeok_sc. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite storeok_scB_eqf : bceq.
Lemma conc_exprB_eqf : forall fk, conc_exprB (mkbc fk) = conc_expr fk.
Proof. intros. bcfe. unfold conc_exprB, conc_expr. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite conc_exprB_eqf : bceq.
Lemma enum_branchB_eqf : forall fk, enum_branchB (mkbc fk) = enum_branch fk.
Proof. intros. bcfe. unfold enum_branchB, enum_branch. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite enum_branchB_eqf : bceq.
Lemma to_saddrKB_eqf : forall fk, to_saddrKB (mkbc fk) = to_saddrK fk.
Proof. intros. bcfe. unfold to_saddrKB, to_saddrK. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite to_saddrKB_eqf : bceq.
Lemma amo_alignedbB_eqf : forall fk, amo_alignedbB (mkbc fk) = amo_alignedb fk.
Proof. intros. bcfe. unfold amo_alignedbB, amo_alignedb. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite amo_alignedbB_eqf : bceq.
Lemma amo_newvalB_eqf : forall fk, amo_newvalB (mkbc fk) = amo_newval fk.
Proof. intros. bcfe. unfold amo_newvalB, amo_newval. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite amo_newvalB_eqf : bceq.
Lemma log_lookupB_eqf : forall fk, log_lookupB (mkbc fk) = log_lookup fk.
Proof.
  intros fk. apply functional_extensionality; intros log. 
  induction log as [|[[kb kk] w v] rest IH]; intros; bcfe; [reflexivity|].
  cbn [log_lookupB log_lookup]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite log_lookupB_eqf : bceq.
Lemma know_lookupA0B_eqf : forall fk, know_lookupA0B (mkbc fk) = know_lookupA0 fk.
Proof.
  intros fk. apply functional_extensionality; intros segs. apply functional_extensionality; intros kn. 
  induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [know_lookupA0B know_lookupA0]. rewrite IH. autorewrite with bceq. rewrite zmod64_feq. cbv beta. reflexivity.
Qed.
#[export] Hint Rewrite know_lookupA0B_eqf : bceq.
Lemma know_lookupAB_eqf : forall fk, know_lookupAB (mkbc fk) = know_lookupA fk.
Proof. intros. bcfe. unfold know_lookupAB, know_lookupA. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite know_lookupAB_eqf : bceq.
Lemma sym_readB_eqf : forall fk segs ss, sym_readB segs ss (mkbc fk) = sym_read segs ss fk.
Proof. intros. bcfe. unfold sym_readB, sym_read. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite sym_readB_eqf : bceq.
Lemma know_lookupB_eqf : forall fk segs, know_lookupB segs (mkbc fk) = know_lookup segs fk.
Proof. intros. bcfe. unfold know_lookupB, know_lookup. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite know_lookupB_eqf : bceq.

Lemma sym_stepB_eq : forall segs i ss scr,
  sym_stepB (mkbc (facts_of (s_know ss))) segs i ss scr = sym_step segs i ss scr.
Proof. intros. unfold sym_stepB, sym_step. autorewrite with bceq. reflexivity. Qed.
(* [comment removed for export] *)
Lemma sym_step_know : forall segs i ss scr ss' scs scr',
  sym_step segs i ss scr = SOk ss' scs scr' -> s_know ss' = s_know ss.
Proof.
  intros segs i ss scr ss' scs scr' H. unfold sym_step, sym_read in H.
  destruct i; try discriminate;
  repeat (lazymatch type of H with
          | SOk _ _ _ = SOk _ _ _ => injection H as <- _ _
          | (match ?x with _ => _ end) = _ => destruct x
          | (let (_, _) := ?x in _) = _ => destruct x
          | (if ?x then _ else _) = _ => destruct x
          end); try discriminate; try reflexivity.
Qed.

(* [comment removed for export] *)
Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Fixpoint existsb_sc {T : Type} (f : T -> bool) (l : list T) : bool :=
  match l with [] => false | x :: r => if f x then true else existsb_sc f r end.
Lemma existsb_sc_eq : forall (T : Type) (f : T -> bool) l, existsb_sc f l = existsb f l.
Proof. intros T f l. induction l as [|x r IH]; [reflexivity|]. cbn [existsb_sc existsb]. rewrite IH. destruct (f x); reflexivity. Qed.
Definition zf_coversB (bc : bctx) (rb : expr) (rk : Z) (n : nat) (kb : expr) (kk : Z) (len : expr) : bool :=
  if (match len with
      | ELit l0 => match rel_lit rb rk (Z.of_nat n) kb kk (zmod64 l0) with RInside _ => true | _ => false end
      | _ => false
      end) then true else xinsideB bc rb rk (elen n) kb kk len.

Definition kentry_overlayB (bc : bctx) (rb : expr) (rk : Z) (n : nat) (K : kentry) : bool :=
  match K with
  | KUnk (SA kb kk) len | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
      zf_coversB bc rb rk n kb kk len
  | _ => false
  end.

Definition kentry_readableB (bc : bctx) (rb : expr) (rk : Z) (n : nat) (K : kentry) : bool :=
  match K with
  | KWord (SA kb kk) w _ =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with RInside _ => true | _ => false end
  | _ => kentry_overlayB bc rb rk n K
  end.

Definition kn_readableB (bc : bctx) (kn : list kentry) (rb : expr) (rk : Z) (n : nat) : bool :=
  if existsb_sc (kentry_readableB bc rb rk n) kn then true else know_bytes_cov segs true kn rb rk n.

Definition kn_overlayB (bc : bctx) (kn : list kentry) (rb : expr) (rk : Z) (n : nat) : bool :=
  if existsb_sc (kentry_overlayB bc rb rk n) kn then true else know_bytes_cov segs false kn rb rk n.

Definition x_dischargeableB (bc : bctx) (ss ss' : sym_state) (rb : option (saddr * nat * bool)) (sc : sidecond) : bool :=
  let kn := s_know ss in
  match sc with
  | SCReadBase a n sx (EVar j) =>
      (match rb with
       | Some (a', n', sx') => saddr_eqb a' a && Nat.eqb n' n && Bool.eqb sx' sx
       | None => false
       end)
      && Nat.eqb j (s_next ss) && Nat.ltb j (s_next ss') && evars_lt (s_next ss) (a_base a)
      && Nat.leb 1 n && Nat.leb n 8 && kn_readableB bc kn (a_base a) (a_off a) n
  | SCFlat a (ELit z) =>
      Z.leb 1 z && Z.leb z 8 && kn_readableB bc kn (a_base a) (a_off a) (Z.to_nat z)
  | SCStoreOk a n => Nat.leb 1 n && Nat.leb n 8 && kn_overlayB bc kn (a_base a) (a_off a) n
  | _ => false
  end%bool.

Definition x_filterB (bc : bctx) (ss ss' : sym_state) (scs : list sidecond) : list sidecond :=
  match scs with
  | [] => []          (* [comment removed for export] *)
  | _ => let rb := find_readbase (s_next ss) scs in
         List.filter (fun sc => negb (x_dischargeableB bc ss ss' rb sc)) scs
  end.

Definition sym_stepXB (bc : bctx) (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  match sym_stepB bc segs i ss scr with
  | SOk ss' scs scr' =>
      if Nat.leb (s_next ss) (s_next ss')            (* [comment removed for export] *)
      then SOk (cap_rd K i ss') (x_filterB bc ss ss' scs) scr'
      else SStop
  | SStop => SStop
  end.


Lemma zf_coversB_eqf : forall fk, zf_coversB (mkbc fk) = zf_covers fk.
Proof. intros. bcfe. unfold zf_coversB, zf_covers. autorewrite with bceq. rewrite zmod64_feq. cbv beta. reflexivity. Qed.
#[local] Hint Rewrite zf_coversB_eqf : bceq.
Lemma kentry_overlayB_eqf : forall fk, kentry_overlayB (mkbc fk) = kentry_overlay fk.
Proof. intros. bcfe. unfold kentry_overlayB, kentry_overlay. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kentry_overlayB_eqf : bceq.
Lemma kentry_readableB_eqf : forall fk, kentry_readableB (mkbc fk) = kentry_readable fk.
Proof. intros. bcfe. unfold kentry_readableB, kentry_readable. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kentry_readableB_eqf : bceq.
Lemma kn_readableB_eqf : forall fk, kn_readableB (mkbc fk) = kn_readable segs fk.
Proof. intros. bcfe. unfold kn_readableB, kn_readable. rewrite existsb_sc_eq. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kn_readableB_eqf : bceq.
Lemma kn_overlayB_eqf : forall fk, kn_overlayB (mkbc fk) = kn_overlay segs fk.
Proof. intros. bcfe. unfold kn_overlayB, kn_overlay. rewrite existsb_sc_eq. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kn_overlayB_eqf : bceq.

Lemma x_dischargeableB_eq : forall ss ss' rb sc,
  x_dischargeableB (mkbc (facts_of (s_know ss))) ss ss' rb sc = x_dischargeable segs ss ss' rb sc.
Proof. intros. unfold x_dischargeableB, x_dischargeable. autorewrite with bceq. reflexivity. Qed.
Lemma x_filterB_eq : forall ss ss' scs,
  x_filterB (mkbc (facts_of (s_know ss))) ss ss' scs = x_filter segs ss ss' scs.
Proof.
  intros. unfold x_filterB, x_filter. destruct scs as [|sc rest]; [reflexivity|].
  erewrite filter_ext; [reflexivity|]. intros x. rewrite x_dischargeableB_eq. reflexivity.
Qed.
Lemma cap_rd_know : forall K i ss, s_know (cap_rd K i ss) = s_know ss.
Proof.
  intros K i ss. unfold cap_rd. destruct K; [reflexivity|]. destruct (rd_of i) as [rd|]; [|reflexivity].
  destruct (bv_eqb rd 0); [reflexivity|]. destruct (esize_le (sr_get (s_regs ss) rd) (S K)); reflexivity.
Qed.
Lemma sym_stepXB_eq : forall K i ss scr,
  sym_stepXB (mkbc (facts_of (s_know ss))) K i ss scr = sym_stepX segs K i ss scr.
Proof.
  intros. unfold sym_stepXB, sym_stepX. rewrite sym_stepB_eq.
  destruct (sym_step segs i ss scr) as [ss' scs scr'|]; [|reflexivity]. rewrite x_filterB_eq. reflexivity.
Qed.
Lemma sym_stepX_know : forall K i ss scr ss' scs scr',
  sym_stepX segs K i ss scr = SOk ss' scs scr' -> s_know ss' = s_know ss.
Proof.
  intros K i ss scr ss' scs scr' H. unfold sym_stepX in H.
  destruct (sym_step segs i ss scr) as [ss1 scs1 scr1|] eqn:E; [|discriminate].
  destruct (Nat.leb (s_next ss) (s_next ss1)); [|discriminate]. injection H as <- _ _.
  rewrite cap_rd_know. exact (sym_step_know _ _ _ _ _ _ _ E).
Qed.

(* [comment removed for export] *)
Fixpoint sym_execTXB_go (bc : bctx) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
  : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then ss else ck
      | Some i =>
          match sym_stepXB bc K i ss scr_nil with
          | SOk ss' [] _ => sym_execTXB_go bc t K f false stops ss' (if s_clean ss' then ss' else ck)
          | _ => if s_clean ss then ss else ck
          end
      end
  end.
Definition sym_execTXB (bc : bctx) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
  sym_execTXB_go bc t K fuel first stops (clr ss) (clr ss).

Lemma sym_execTXB_go_eq : forall t K fuel first stops ss ck,
  sym_execTXB_go (mkbc (facts_of (s_know ss))) t K fuel first stops ss ck = sym_execTX_go segs t K fuel first stops ss ck.
Proof.
  intros t K fuel. induction fuel as [|f IH]; intros first stops ss ck; [reflexivity|].
  cbn [sym_execTXB_go sym_execTX_go].
  destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
  destruct (itab_lookup t (s_pc ss)) as [i|]; [|reflexivity].
  rewrite sym_stepXB_eq. destruct (sym_stepX segs K i ss scr_nil) as [ss' scs scr'|] eqn:E; [|reflexivity].
  destruct scs; [|reflexivity].
  rewrite <- (sym_stepX_know _ _ _ _ _ _ _ E). apply IH.
Qed.
Lemma sym_execTXB_eq : forall kn0 t K fuel first stops ss,
  s_know ss = kn0 ->
  sym_execTXB (mkbc (facts_of kn0)) t K fuel first stops ss = sym_execTX segs t K fuel first stops ss.
Proof.
  intros kn0 t K fuel first stops ss <-. unfold sym_execTXB, sym_execTX.
  replace (s_know ss) with (s_know (clr ss)) by (destruct ss; reflexivity).
  apply sym_execTXB_go_eq.
Qed.
(* [comment removed for export] *)
Lemma sym_execTX_go_know : forall t K fuel first stops ss ck,
  s_know ck = s_know ss ->
  s_know (sym_execTX_go segs t K fuel first stops ss ck) = s_know ss.
Proof.
  intros t K fuel. induction fuel as [|f IH]; intros first stops ss ck Hck.
  - cbn. destruct (s_clean ss); [reflexivity|exact Hck].
  - cbn [sym_execTX_go].
    destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [destruct (s_clean ss); [reflexivity|exact Hck]|].
    destruct (itab_lookup t (s_pc ss)) as [i|]; [|destruct (s_clean ss); [reflexivity|exact Hck]].
    destruct (sym_stepX segs K i ss scr_nil) as [ss' scs scr'|] eqn:E; [|destruct (s_clean ss); [reflexivity|exact Hck]].
    destruct scs; [|destruct (s_clean ss); [reflexivity|exact Hck]].
    pose proof (sym_stepX_know _ _ _ _ _ _ _ E) as HK.
    rewrite IH; [exact HK|]. destruct (s_clean ss'); [reflexivity|]. rewrite Hck, HK. reflexivity.
Qed.
Lemma sym_execTX_know : forall t K fuel first stops ss,
  s_know (sym_execTX segs t K fuel first stops ss) = s_know ss.
Proof.
  intros. unfold sym_execTX. rewrite sym_execTX_go_know; [|reflexivity]. destruct ss; reflexivity.
Qed.
(* [comment removed for export] *)
Definition sym_stepXBI (bc : bctx) (kx : kix) (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  match sym_stepBI bc kx segs i ss scr with
  | SOk ss' scs scr' =>
      if Nat.leb (s_next ss) (s_next ss')
      then SOk (cap_rd K i ss') (x_filterB bc ss ss' scs) scr'
      else SStop
  | SStop => SStop
  end.
Lemma sym_stepXBI_eq : forall K i ss scr,
  sym_stepXBI (mkbc (facts_of (s_know ss))) (mk_kix (s_know ss)) K i ss scr = sym_stepX segs K i ss scr.
Proof.
  intros. unfold sym_stepXBI. rewrite (sym_stepBI_eq _ _ _ _ _ (bc_kdi_mkbc _)). fold (sym_stepXB (mkbc (facts_of (s_know ss))) K i ss scr). apply sym_stepXB_eq.
Qed.
Fixpoint sym_execTXBI_go (bc : bctx) (kx : kix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
  : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then ss else ck
      | Some i =>
          match sym_stepXBI bc kx K i ss scr_nil with
          | SOk ss' [] _ => sym_execTXBI_go bc kx t K f false stops ss' (if s_clean ss' then ss' else ck)
          | _ => if s_clean ss then ss else ck
          end
      end
  end.
Definition sym_execTXBI (bc : bctx) (kx : kix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
  sym_execTXBI_go bc kx t K fuel first stops (clr ss) (clr ss).
Lemma sym_execTXBI_go_eq : forall t K fuel first stops ss ck,
  sym_execTXBI_go (mkbc (facts_of (s_know ss))) (mk_kix (s_know ss)) t K fuel first stops ss ck = sym_execTX_go segs t K fuel first stops ss ck.
Proof.
  intros t K fuel. induction fuel as [|f IH]; intros first stops ss ck; [reflexivity|].
  cbn [sym_execTXBI_go sym_execTX_go].
  destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
  destruct (itab_lookup t (s_pc ss)) as [i|]; [|reflexivity].
  rewrite sym_stepXBI_eq. destruct (sym_stepX segs K i ss scr_nil) as [ss' scs scr'|] eqn:E; [|reflexivity].
  destruct scs; [|reflexivity].
  rewrite <- (sym_stepX_know _ _ _ _ _ _ _ E). apply IH.
Qed.
Lemma sym_execTXBI_eq : forall kn0 t K fuel first stops ss,
  s_know ss = kn0 ->
  sym_execTXBI (mkbc (facts_of kn0)) (mk_kix kn0) t K fuel first stops ss = sym_execTX segs t K fuel first stops ss.
Proof.
  intros kn0 t K fuel first stops ss <-. unfold sym_execTXBI, sym_execTX.
  replace (s_know ss) with (s_know (clr ss)) by (destruct ss; reflexivity).
  apply sym_execTXBI_go_eq.
Qed.

End WithSegs.

(* [comment removed for export] *)
Definition kcutB (bc : bctx) (mk : saddr -> expr -> kentry) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry :=
  let ws := mkAlu ALU_ADD wb (ELit wk) in
  let ks := mkAlu ALU_ADD kb (ELit kk) in
  (* [comment removed for export] *)
  let low :=
    if (if lin_ge0B bc [(kb, kk)] [(wb, wk)] then false   (* [comment removed for export] *)
        else if lin_ge0B bc [(wb, wk)] [(kb, kk)] then lin_ge0B bc [(kb, kk); (len, 0%Z)] [(wb, wk)] else false)
    then [mk (SA kb kk) (mkAlu ALU_SUB ws ks)] else [] in
  let high :=
    if (if lin_ge0B bc [(kb, kk); (len, 0%Z)] [(wb, wk); (wn, 0%Z)]            (* [comment removed for export] *)
        then if lin_ge0B bc [(wb, wk); (wn, 0%Z)] [(kb, kk)]                    (* [comment removed for export] *)
             then lin_ge0B bc [(ELit 0, (two64 - 1)%Z)] [(kb, kk); (len, 0%Z)]  (* [comment removed for export] *)
             else false
        else false)
    then let we := mkAlu ALU_ADD ws wn in
         let '(hb, ho) := split_lit we in
         let ha := if (lin_ge0B bc [(hb, ho)] [(wb, wk); (wn, 0%Z)] && lin_ge0B bc [(wb, wk); (wn, 0%Z)] [(hb, ho)])%bool
                   then SA hb ho else SA we 0%Z in
         [mk ha (mkAlu ALU_SUB (mkAlu ALU_ADD ks len) we)]
    else [] in
  low ++ high.

Definition kzero_cutB (bc : bctx) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry := kcutB bc KZero wb wk wn kb kk len.

Definition kfill_cutB (bc : bctx) (c : Z) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry := kcutB bc (fun a n => KFill a n c) wb wk wn kb kk len.

Definition kunk_cutB (bc : bctx) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry := kcutB bc KUnk wb wk wn kb kk len.

Definition prune_zfB (bc : bctx) (mk : saddr -> expr -> kentry) (wb : expr) (k : Z) (w : nat)
           (K : kentry) (kb : expr) (kk : Z) (len : expr) (apart : unit -> bool) (hints : list bool)
           (diffbase : unit -> list kentry * list sidecond * list bool)
  : list kentry * list sidecond * list bool :=
  (* [comment removed for export] *)
  if expr_eqb kb wb then
    match len with
    | ELit l0 => (ktrim mk kb kk l0 k w, [], hints)
    | _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints)
           else (kcutB bc mk wb k (elen w) kb kk len, [], hints)
    end
  else if apart tt then ([K], [], hints)
  else match kcutB bc mk wb k (elen w) kb kk len with
       | [] => diffbase tt
       | cut => (cut, [], hints)
       end.

Definition prune1pB (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  let k := a_off wa in
  let diffbase (ka : saddr) (kl : expr) :=
    let apart := ranges_apart_pB bc sp (a_base wa) k (elen w) (a_base ka) (a_off ka) kl in
    if apart then ([K], [], hints) else
    match hints with
    | true :: hs => ([K], [SCDisj wa (elen w) ka kl], hs)   (* [comment removed for export] *)
    | false :: hs => ([], [], hs)                          (* [comment removed for export] *)
    | [] => ([], [], [])                                   (* [comment removed for export] *)
    end in
  match K with
  | KAlign _ _ => ([K], [], hints)
  | KRange _ _ _ => ([K], [], hints)
  | KWr _ _ => ([K], [], hints)
  | KDisj _ _ _ _ => ([K], [], hints)
  | KImg lo hi =>
      match a_base wa with
      | ELit 0 =>
          let r1 := if Z.ltb lo (Z.min k hi) then [KImg lo (Z.min k hi)] else [] in
          let lo2 := Z.max lo (k + Z.of_nat w) in
          let r2 := if Z.ltb lo2 hi then [KImg lo2 hi] else [] in
          (r1 ++ r2, [], hints)
      | _ => if Z.ltb (hi - lo) two64 then diffbase (SA (ELit 0) lo) (ELit (hi - lo))
             else ([], [], hints)
      end
  | KZero (SA kb kk) len =>
      prune_zfB bc KZero (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_pB bc sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KFill (SA kb kk) len c =>
      prune_zfB bc (fun a n => KFill a n c) (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_pB bc sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KUnk (SA kb kk) len =>
      prune_zfB bc KUnk (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_pB bc sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KWord (SA kb kk) w' v =>
      if expr_eqb kb (a_base wa) then
        (if (Z.leb (kk + Z.of_nat w') k || Z.leb (k + Z.of_nat w) kk)%bool
         then ([K], [], hints) else (kword_cut kb kk w' v k w, [], hints))   (* [comment removed for export] *)
      else if ranges_apart_pB bc sp (a_base wa) k (elen w) kb kk (elen w') then ([K], [], hints)
      else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool
      then ([K], [], hints)   (* [comment removed for export] *)
      else diffbase (SA kb kk) (elen w')
  | KBlob (SA kb kk) len bk =>
      if expr_eqb kb (a_base wa) then
        match len with
        | ELit l0 =>
            let l := zmod64 l0 in
            (if (Z.leb (kk + l) k || Z.leb (k + Z.of_nat w) kk)%bool
             then ([K], [], hints) else ([], [], hints))
        | _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints) else ([], [], hints)
        end
      else diffbase (SA kb kk) len
  end.

Definition ranges_apart_pcB (bc : bctx) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr)
           (br2 : option (Z * Z)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      if (match sp_rng sp, br2 with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
          | _, _ => false
          end) then true
      else if in_sidesHB bc (sp_D sp) b2 k2 m2 then true
      else lin_apartB bc b1 k1 m1 b2 k2 m2
  | _, _ =>
    if (match sp_rng sp, br2, sp_h1 sp, xhiB bc n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else (* [comment removed for export] *)
            if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if in_sides_xHB bc (sp_Dx sp) b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.

Definition prune1pcB (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (hints : list bool)
  (br2 : option (Z * Z)) : list kentry * list sidecond * list bool :=
  let k := a_off wa in
  let diffbase (ka : saddr) (kl : expr) :=
    let apart := ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 (a_base ka) (a_off ka) kl in
    if apart then ([K], [], hints) else
    match hints with
    | true :: hs => ([K], [SCDisj wa (elen w) ka kl], hs)
    | false :: hs => ([], [], hs)
    | [] => ([], [], [])
    end in
  match K with
  | KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ | KImg _ _ => prune1pB bc sp wa w wv K hints
  | KZero (SA kb kk) len =>
      if expr_eqb kb (a_base wa) then prune1pB bc sp wa w wv K hints
      else if ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
      else match kzero_cutB bc (a_base wa) k (elen w) kb kk len with
           | [] => diffbase (SA kb kk) len
           | cut => (cut, [], hints)
           end
  | KFill (SA kb kk) len c =>
      if expr_eqb kb (a_base wa) then prune1pB bc sp wa w wv K hints
      else if ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
      else match kfill_cutB bc c (a_base wa) k (elen w) kb kk len with
           | [] => diffbase (SA kb kk) len
           | cut => (cut, [], hints)
           end
  | KUnk (SA kb kk) len =>
      if expr_eqb kb (a_base wa) then prune1pB bc sp wa w wv K hints
      else if ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
      else match kunk_cutB bc (a_base wa) k (elen w) kb kk len with
           | [] => diffbase (SA kb kk) len
           | cut => (cut, [], hints)
           end
  | KWord (SA kb kk) w' v =>
      if expr_eqb kb (a_base wa) then prune1pB bc sp wa w wv K hints
      else if ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 kb kk (elen w') then ([K], [], hints)
      else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool
      then ([K], [], hints)
      else diffbase (SA kb kk) (elen w')
  | KBlob (SA kb kk) len bk =>
      if expr_eqb kb (a_base wa) then prune1pB bc sp wa w wv K hints
      else diffbase (SA kb kk) len
  end.

Fixpoint prunepcB (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (kn : list kentry) (hints : list bool)
  (cache : list (expr * option (Z * Z))) : list kentry * list sidecond * list bool :=
  match kn with
  | [] => ([], [], hints)
  | K :: rest =>
      let '(br2, cache') :=
        match kbase K with
        | Some kb => match br_lookup cache kb with
                     | Some r => (r, cache)
                     | None => let r := base_rangeB bc kb in (r, (kb, r) :: cache)
                     end
        | None => (None, cache)
        end in
      let '(kept, scs1, hs1) := prune1pcB bc sp wa w wv K hints br2 in
      let '(r, scs2, hs2) := prunepcB bc sp wa w wv rest hs1 cache' in
      (kept ++ r, scs1 ++ scs2, hs2)
  end.


Lemma kcutB_eqf : forall fk, kcutB (mkbc fk) = (fun mk => kcut mk fk).
Proof. intros. bcfe. unfold kcutB, kcut. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite kcutB_eqf : bceq.
Lemma kzero_cutB_eqf : forall fk, kzero_cutB (mkbc fk) = kzero_cut fk.
Proof. intros. bcfe. unfold kzero_cutB, kzero_cut. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite kzero_cutB_eqf : bceq.
Lemma kfill_cutB_eqf : forall fk, kfill_cutB (mkbc fk) = (fun c => kfill_cut c fk).
Proof. intros. bcfe. unfold kfill_cutB, kfill_cut. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite kfill_cutB_eqf : bceq.
Lemma kunk_cutB_eqf : forall fk, kunk_cutB (mkbc fk) = kunk_cut fk.
Proof. intros. bcfe. unfold kunk_cutB, kunk_cut. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite kunk_cutB_eqf : bceq.
Lemma prune_zfB_eqf : forall fk, prune_zfB (mkbc fk) = (fun mk => prune_zf mk fk).
Proof. intros. bcfe. unfold prune_zfB, prune_zf. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite prune_zfB_eqf : bceq.
Lemma prune1pB_eqf : forall fk, prune1pB (mkbc fk) = prune1p fk.
Proof. intros. bcfe. unfold prune1pB, prune1p. autorewrite with bceq. rewrite zmod64_feq. cbv beta. reflexivity. Qed.
#[export] Hint Rewrite prune1pB_eqf : bceq.
Lemma ranges_apart_pcB_eqf : forall fk, ranges_apart_pcB (mkbc fk) = ranges_apart_pc fk.
Proof. intros. bcfe. unfold ranges_apart_pcB, ranges_apart_pc. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite ranges_apart_pcB_eqf : bceq.
Lemma prune1pcB_eqf : forall fk, prune1pcB (mkbc fk) = prune1pc fk.
Proof. intros. bcfe. unfold prune1pcB, prune1pc. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite prune1pcB_eqf : bceq.
Lemma prunepcB_eqf : forall fk, prunepcB (mkbc fk) = prunepc fk.
Proof.
  intros fk. apply functional_extensionality; intros sp. apply functional_extensionality; intros wa. apply functional_extensionality; intros w. apply functional_extensionality; intros wv. apply functional_extensionality; intros kn. 
  induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [prunepcB prunepc]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite prunepcB_eqf : bceq.

(* [comment removed for export] *)
#[export] Hint Rewrite zf_coversB_eqf kentry_overlayB_eqf kentry_readableB_eqf kn_readableB_eqf kn_overlayB_eqf : bceq.

(* [comment removed for export] *)
Lemma filter_nil_app : forall (l1 l2 : list kentry),
  List.filter is_factb l1 = [] -> List.filter is_factb l2 = [] -> List.filter is_factb (l1 ++ l2) = [].
Proof. intros l1 l2 H1 H2. rewrite List.filter_app, H1, H2. reflexivity. Qed.
Lemma filter_if_single : forall (c : bool) K,
  is_factb K = false -> List.filter is_factb (if c then [K] else []) = [].
Proof. intros c K H. destruct c; cbn; rewrite ?H; reflexivity. Qed.

Lemma kcut_nofacts : forall mk kn wb wk wn kb kk len,
  (forall a n, is_factb (mk a n) = false) ->
  List.filter is_factb (kcut mk kn wb wk wn kb kk len) = [].
Proof.
  intros mk kn wb wk wn kb kk len H. unfold kcut.
  apply filter_nil_app.
  - apply filter_if_single. apply H.
  - match goal with |- List.filter is_factb (if ?c then _ else _) = [] => destruct c; [|reflexivity] end.
    destruct (split_lit (mkAlu ALU_ADD (mkAlu ALU_ADD wb (ELit wk)) wn)) as [hb ho].
    cbn [List.filter]. rewrite H. reflexivity.
Qed.
Lemma ktrim_nofacts : forall mk kb kk l0 k w,
  (forall a n, is_factb (mk a n) = false) ->
  List.filter is_factb (ktrim mk kb kk l0 k w) = [].
Proof. intros. unfold ktrim. apply filter_nil_app; apply filter_if_single; apply H. Qed.
Lemma kword_cut_nofacts : forall kb kk w' v k w, List.filter is_factb (kword_cut kb kk w' v k w) = [].
Proof.
  intros. unfold kword_cut. destruct v; try reflexivity.
  apply filter_nil_app; apply filter_if_single; reflexivity.
Qed.
Lemma prune_zf_nofacts : forall mk allkn wb k w K kb kk len apart hints diffbase,
  (forall a n, is_factb (mk a n) = false) -> is_factb K = false ->
  List.filter is_factb (fst (fst (diffbase tt))) = [] ->
  List.filter is_factb (fst (fst (prune_zf mk allkn wb k w K kb kk len apart hints diffbase))) = [].
Proof.
  intros mk allkn wb k w K kb kk len apart hints diffbase Hm HK Hd. unfold prune_zf.
  destruct (expr_eqb kb wb).
  - destruct len; cbn [fst]; try (apply ktrim_nofacts; exact Hm);
      (destruct (Z.leb (k + Z.of_nat w) kk); cbn [fst List.filter]; [rewrite HK; reflexivity | apply kcut_nofacts; exact Hm]).
  - destruct (apart tt); cbn [fst List.filter]; [rewrite HK; reflexivity|].
    destruct (kcut mk allkn wb k (elen w) kb kk len) as [|c cs] eqn:E; [exact Hd|].
    cbn [fst]. rewrite <- E. apply kcut_nofacts. exact Hm.
Qed.

Ltac nfcrush :=
  cbn [fst List.filter is_factb];
  first [ reflexivity
        | apply kword_cut_nofacts
        | (apply filter_nil_app; apply filter_if_single; reflexivity)
        | match goal with
          | |- context [if ?c then _ else _] => destruct c; nfcrush
          | |- context [match ?h with nil => _ | cons _ _ => _ end] => destruct h; nfcrush
          | |- context [match ?h with ELit _ => _ | _ => _ end] => destruct h; nfcrush
          | |- context [match ?h with Z0 => _ | _ => _ end] => destruct h; nfcrush
          end ].

Lemma prune1p_facts : forall allkn sp wa w wv K hints,
  List.filter is_factb (fst (fst (prune1p allkn sp wa w wv K hints))) = List.filter is_factb [K].
Proof.
  intros allkn sp wa w wv K hints. unfold prune1p.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|[kb kk] n|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; cbn [List.filter is_factb];
    try reflexivity;
    try (apply prune_zf_nofacts; [reflexivity|reflexivity|]); nfcrush.
Qed.

Lemma prune1pc_facts : forall allkn sp wa w wv K hints br2,
  List.filter is_factb (fst (fst (prune1pc allkn sp wa w wv K hints br2))) = List.filter is_factb [K].
Proof.
  intros allkn sp wa w wv K hints br2. unfold prune1pc.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|[kb kk] n|a1 n1 a2 n2|[kb kk] len c|[kb kk] len];
    try apply prune1p_facts.
  - destruct (expr_eqb kb (a_base wa)); [apply prune1p_facts|]. nfcrush.
  - destruct (expr_eqb kb (a_base wa)); [apply prune1p_facts|].
    unfold kzero_cut. destruct (ranges_apart_pc _ _ _ _ _ _ _ _ _); [reflexivity|].
    destruct (kcut KZero allkn (a_base wa) (a_off wa) (elen w) kb kk len) eqn:E; [nfcrush|].
    cbn [fst]. rewrite <- E. apply kcut_nofacts. reflexivity.
  - destruct (expr_eqb kb (a_base wa)); [apply prune1p_facts|]. nfcrush.
  - destruct (expr_eqb kb (a_base wa)); [apply prune1p_facts|].
    unfold kfill_cut. destruct (ranges_apart_pc _ _ _ _ _ _ _ _ _); [reflexivity|].
    destruct (kcut (fun a n => KFill a n c) allkn (a_base wa) (a_off wa) (elen w) kb kk len) eqn:E; [nfcrush|].
    cbn [fst]. rewrite <- E. apply kcut_nofacts. reflexivity.
  - destruct (expr_eqb kb (a_base wa)); [apply prune1p_facts|].
    unfold kunk_cut. destruct (ranges_apart_pc _ _ _ _ _ _ _ _ _); [reflexivity|].
    destruct (kcut KUnk allkn (a_base wa) (a_off wa) (elen w) kb kk len) eqn:E; [nfcrush|].
    cbn [fst]. rewrite <- E. apply kcut_nofacts. reflexivity.
Qed.

Lemma prunepc_facts : forall allkn sp wa w wv kn hints cache,
  List.filter is_factb (fst (fst (prunepc allkn sp wa w wv kn hints cache))) = List.filter is_factb kn.
Proof.
  intros allkn sp wa w wv kn. induction kn as [|K rest IH]; intros hints cache; [reflexivity|].
  cbn [prunepc].
  destruct (match kbase K with Some kb => match br_lookup cache kb with Some r => (r, cache) | None => (base_range allkn kb, (kb, base_range allkn kb) :: cache) end | None => (None, cache) end) as [br2 cache'].
  destruct (prune1pc allkn sp wa w wv K hints br2) as [[kept scs1] hs1] eqn:E1.
  destruct (prunepc allkn sp wa w wv rest hs1 cache') as [[r scs2] hs2] eqn:E2.
  cbn [fst]. rewrite List.filter_app. pose proof (prune1pc_facts allkn sp wa w wv K hints br2) as H1. rewrite E1 in H1. cbn [fst] in H1.
  rewrite H1. specialize (IH hs1 cache'). rewrite E2 in IH. cbn [fst] in IH. rewrite IH. cbn [List.filter]. destruct (is_factb K); reflexivity.
Qed.

Lemma carry_facts : forall log kn hints,
  List.filter is_factb (fst (fst (carry log kn hints))) = List.filter is_factb kn.
Proof.
  intros log kn hints. induction log as [|[a w v] older IH]; [reflexivity|].
  cbn [carry]. destruct (carry older kn hints) as [[kn1 scs1] hs1]. cbn [fst] in IH.
  destruct (prunepc _ _ _ _ _ kn1 hs1 []) as [[kn2 scs2] hs2] eqn:E.
  cbn [fst List.filter is_factb]. pose proof (prunepc_facts (facts_of kn1) (mk_sprep (facts_of kn1) (a_base a) (a_off a) (elen w)) a w v kn1 hs1 []) as H.
  rewrite E in H. cbn [fst] in H. rewrite H. exact IH.
Qed.

Fixpoint carryB (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log with
  | [] => (kn, [], hints)
  | SE a w v :: older =>
      let '(kn1, scs1, hs1) := carryB bc older kn hints in
      let '(kn2, scs2, hs2) := prunepcB bc (mk_sprepB bc (a_base a) (a_off a) (elen w)) a w v kn1 hs1 [] in
      (KWord a w v :: kn2, scs1 ++ scs2, hs2)
  end.
Lemma carryB_eq : forall log kn hints, carryB (mkbc (facts_of kn)) log kn hints = carry log kn hints.
Proof.
  intros log kn hints. induction log as [|[a w v] older IH]; [reflexivity|].
  cbn [carryB carry]. rewrite IH.
  pose proof (carry_facts older kn hints) as HF.
  destruct (carry older kn hints) as [[kn1 scs1] hs1]. cbn [fst] in HF.
  rewrite !facts_of_filter, <- HF, <- !facts_of_filter.
  autorewrite with bceq. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p_aluop_eqb_refl : forall a, aluop_eqb a a = true. Proof. intros []; reflexivity. Qed.
Lemma p_mulop_eqb_refl : forall a, mulop_eqb a a = true. Proof. intros []; reflexivity. Qed.
Lemma p_expr_eqb_refl : forall x, expr_eqb x x = true.
Proof.
  induction x; cbn -[Z.eqb Nat.eqb]; rewrite ?p_aluop_eqb_refl, ?p_mulop_eqb_refl, ?IHx, ?IHx1, ?IHx2, ?Z.eqb_refl, ?Nat.eqb_refl, ?Bool.eqb_reflx; reflexivity.
Qed.
Lemma p_prune1pc_eq : forall allkn sp wa w wv K hints br2,
  match kbase K with Some kb => br2 = base_range allkn kb | None => True end ->
  prune1pc allkn sp wa w wv K hints br2 = prune1p allkn sp wa w wv K hints.
Proof.
  intros allkn sp wa w wv K hints br2 Hb.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    cbn [kbase] in Hb; try reflexivity; subst br2; unfold prune1pc, prune1p, prune_zf, kzero_cut, kfill_cut, kunk_cut;
    destruct (expr_eqb kb (a_base wa)); reflexivity.
Qed.
Definition p_br_cache_ok (allkn : list kentry) (c : list (expr * option (Z * Z))) : Prop :=
  Forall (fun p => snd p = base_range allkn (fst p)) c.
Lemma p_br_lookup_ok : forall allkn c b r, p_br_cache_ok allkn c -> br_lookup c b = Some r -> r = base_range allkn b.
Proof.
  intros allkn c b r Hc. induction c as [|[b' r'] rest IH]; cbn; [discriminate|].
  apply Forall_cons_iff in Hc as [H1 Hc]. cbn in H1.
  destruct (expr_eqb b b') eqn:E.
  - intros H. injection H as <-. apply p_expr_eqb_eq in E. subst b'. exact H1.
  - apply IH. exact Hc.
Qed.
Lemma p_prunepc_eq : forall allkn sp wa w wv kn hints cache,
  p_br_cache_ok allkn cache ->
  prunepc allkn sp wa w wv kn hints cache = prunep allkn sp wa w wv kn hints.
Proof.
  intros allkn sp wa w wv kn. induction kn as [|K rest IH]; intros hints cache Hc; [reflexivity|].
  cbn [prunepc prunep].
  destruct (kbase K) as [kb|] eqn:HK.
  - destruct (br_lookup cache kb) as [r|] eqn:HL.
    + rewrite (p_prune1pc_eq allkn sp wa w wv K hints r) by (rewrite HK; exact (p_br_lookup_ok _ _ _ _ Hc HL)).
      destruct (prune1p allkn sp wa w wv K hints) as [[kept scs1] hs1]. rewrite (IH hs1 cache Hc). reflexivity.
    + rewrite (p_prune1pc_eq allkn sp wa w wv K hints (base_range allkn kb)) by (rewrite HK; reflexivity).
      destruct (prune1p allkn sp wa w wv K hints) as [[kept scs1] hs1].
      rewrite (IH hs1 ((kb, base_range allkn kb) :: cache)) by (constructor; [reflexivity | exact Hc]). reflexivity.
  - rewrite (p_prune1pc_eq allkn sp wa w wv K hints None) by (rewrite HK; exact I).
    destruct (prune1p allkn sp wa w wv K hints) as [[kept scs1] hs1]. rewrite (IH hs1 cache Hc). reflexivity.
Qed.

(* [comment removed for export] *)
Definition g1 (fk : list kentry) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) : list kentry :=
  fst (fst (prune1p fk sp wa w wv K [])).

Ltac pk_crush :=
  cbn [fst snd];
  first [ reflexivity
        | match goal with
          | |- context [if ?c then _ else _] => destruct c; pk_crush
          | |- context [match ?h with ELit _ => _ | _ => _ end] => destruct h; pk_crush
          | |- context [match ?h with Z0 => _ | _ => _ end] => destruct h; pk_crush
          | |- context [match ?h with nil => _ | cons _ _ => _ end] => destruct h; pk_crush
          end ].

Lemma prune1p_nil : forall fk sp wa w wv K,
  prune1p fk sp wa w wv K [] = (g1 fk sp wa w wv K, [], []).
Proof.
  intros. unfold g1, prune1p, prune_zf.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len]; pk_crush.
Qed.
Lemma prunep_nil : forall fk sp wa w wv kn,
  prunep fk sp wa w wv kn [] = (flat_map (g1 fk sp wa w wv) kn, [], []).
Proof.
  intros fk sp wa w wv kn. induction kn as [|K rest IH]; [reflexivity|].
  cbn [prunep flat_map]. rewrite prune1p_nil, IH. reflexivity.
Qed.

(* [comment removed for export] *)
Inductive pk_res := PKeep | PRepl (l : list kentry).
Definition pk_list (K : kentry) (r : pk_res) : list kentry := match r with PKeep => [K] | PRepl l => l end.

(* [comment removed for export] *)
Definition prune1pcK (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (same : bool)
  (br2 : option (Z * Z)) : pk_res :=
  let k := a_off wa in
  let wb := a_base wa in
  let zfK (mk : saddr -> expr -> kentry) (kb : expr) (kk : Z) (len : expr) :=
    if same then
      match len with
      | ELit l0 => PRepl (ktrim mk kb kk l0 k w)
      | _ => if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl (kcutB bc mk wb k (elen w) kb kk len)
      end
    else if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk len then PKeep
    else match kcutB bc mk wb k (elen w) kb kk len with
         | [] => if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk len then PKeep else PRepl []
         | cut => PRepl cut
         end in
  match K with
  | KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ => PKeep
  | KImg lo hi =>
      match wb with
      | ELit 0 =>
          let r1 := if Z.ltb lo (Z.min k hi) then [KImg lo (Z.min k hi)] else [] in
          let lo2 := Z.max lo (k + Z.of_nat w) in
          let r2 := if Z.ltb lo2 hi then [KImg lo2 hi] else [] in
          PRepl (r1 ++ r2)
      | _ => if Z.ltb (hi - lo) two64 then
               (if ranges_apart_pB bc sp wb k (elen w) (ELit 0) lo (ELit (hi - lo)) then PKeep else PRepl [])
             else PRepl []
      end
  | KZero (SA kb kk) len => zfK KZero kb kk len
  | KFill (SA kb kk) len c => zfK (fun a n => KFill a n c) kb kk len
  | KUnk (SA kb kk) len => zfK KUnk kb kk len
  | KWord (SA kb kk) w' v =>
      if same then (if (Z.leb (kk + Z.of_nat w') k || Z.leb (k + Z.of_nat w) kk)%bool then PKeep else PRepl (kword_cut kb kk w' v k w))
      else if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk (elen w') then PKeep
      else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool then PKeep
      else if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk (elen w') then PKeep else PRepl []
  | KBlob (SA kb kk) len bk =>
      if same then
        match len with
        | ELit l0 => let l := zmod64 l0 in
                     if (Z.leb (kk + l) k || Z.leb (k + Z.of_nat w) kk)%bool then PKeep else PRepl []
        | _ => if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl []
        end
      else if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk len then PKeep else PRepl []
  end.

Lemma prune1pcK_eq : forall fk sp wa w wv K br2 same,
  (match kbase K with Some kb => same = expr_eqb kb (a_base wa) | None => True end) ->
  pk_list K (prune1pcK (mkbc fk) sp wa w wv K same br2) = fst (fst (prune1pc fk sp wa w wv K [] br2)).
Proof.
  intros fk sp wa w wv K br2 same H.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    cbn [kbase] in H; try subst same; unfold prune1pcK, prune1pc, prune1p, prune_zf, kzero_cut, kfill_cut, kunk_cut;
    autorewrite with bceq; rewrite ?zmod64_feq; unfold two64; cbn [a_base a_off]; pk_crush.
Qed.

(* [comment removed for export] *)
Definition bkey (e : expr) : option nat := first_var e.
Record binfo := BI { bi_base : expr; bi_br : option (Z * Z) }.
Record ntab := NT { nt_vars : ptree (list (expr * positive)); nt_other : list (expr * positive); nt_next : positive; nt_info : ptree binfo }.
Definition nt_empty : ntab := NT PTLeaf [] xH PTLeaf.
Fixpoint alookupE (l : list (expr * positive)) (b : expr) : option positive :=
  match l with
  | [] => None
  | (b', id) :: rest => if expr_eqb b b' then Some id else alookupE rest b
  end.
Definition nt_bucket (t : ntab) (k : option nat) : list (expr * positive) :=
  match k with Some n => lget (nt_vars t) n | None => nt_other t end.
Definition nt_add (t : ntab) (k : option nat) (p : expr * positive) (bi : binfo) : ntab :=
  match k with
  | Some n => NT (lset (nt_vars t) n p) (nt_other t) (Pos.succ (nt_next t)) (pt_set (nt_next t) bi (nt_info t))
  | None => NT (nt_vars t) (p :: nt_other t) (Pos.succ (nt_next t)) (pt_set (nt_next t) bi (nt_info t))
  end.
Definition intern (bc : bctx) (t : ntab) (b : expr) : positive * binfo * ntab :=
  let k := bkey b in
  match alookupE (nt_bucket t k) b with
  | Some id => (id, match pt_get (nt_info t) id with Some bi => bi | None => BI b (base_rangeB bc b) end, t)
  | None => let id := nt_next t in
            let bi := BI b (base_rangeB bc b) in
            (id, bi, nt_add t k (b, id) bi)
  end.

Definition NTI (bc : bctx) (t : ntab) : Prop :=
  (forall k b id, In (b, id) (nt_bucket t k) ->
     k = bkey b /\ pt_get (nt_info t) id = Some (BI b (base_rangeB bc b)) /\ (id < nt_next t)%positive)
  /\ (forall k b id id', In (b, id) (nt_bucket t k) -> In (b, id') (nt_bucket t k) -> id = id').

Lemma nt_bucket_empty : forall k, nt_bucket nt_empty k = [].
Proof. intros [n|]; cbn [nt_bucket nt_empty nt_vars nt_other]; [apply lget_leaf | reflexivity]. Qed.
Lemma NTI_empty : forall bc, NTI bc nt_empty.
Proof. intros bc. split; intros; rewrite nt_bucket_empty in *; contradiction. Qed.

Lemma alookupE_Some : forall l b id, alookupE l b = Some id -> In (b, id) l.
Proof.
  induction l as [|[b' id'] rest IH]; cbn; intros b id H; [discriminate|].
  destruct (expr_eqb b b') eqn:E.
  - injection H as <-. apply p_expr_eqb_eq in E. subst. left. reflexivity.
  - right. apply IH. exact H.
Qed.
Lemma alookupE_None : forall l b id, alookupE l b = None -> ~ In (b, id) l.
Proof.
  induction l as [|[b' id'] rest IH]; cbn; intros b id H; [tauto|].
  destruct (expr_eqb b b') eqn:E; [discriminate|].
  intros [X|X].
  - injection X as -> ->. rewrite p_expr_eqb_refl in E. discriminate.
  - exact (IH _ _ H X).
Qed.
Lemma nt_add_bucket : forall t k p bi k',
  nt_bucket (nt_add t k p bi) k' = if okey_eqb k' k then p :: nt_bucket t k' else nt_bucket t k'.
Proof.
  intros t [n|] p bi [m|]; cbn [nt_add nt_bucket nt_vars nt_other okey_eqb]; try reflexivity. apply lget_lset.
Qed.
Lemma nt_add_next : forall t k p bi, nt_next (nt_add t k p bi) = Pos.succ (nt_next t).
Proof. intros t [n|] p bi; reflexivity. Qed.
Lemma nt_add_info : forall t k p bi, nt_info (nt_add t k p bi) = pt_set (nt_next t) bi (nt_info t).
Proof. intros t [n|] p bi; reflexivity. Qed.

Lemma intern_ok : forall bc t b id bi t',
  NTI bc t -> intern bc t b = (id, bi, t') ->
  NTI bc t' /\ bi = BI b (base_rangeB bc b) /\ In (b, id) (nt_bucket t' (bkey b))
  /\ (forall k p, In p (nt_bucket t k) -> In p (nt_bucket t' k)).
Proof.
  intros bc t b id bi t' [HA HB] H. unfold intern in H.
  destruct (alookupE (nt_bucket t (bkey b)) b) as [id0|] eqn:HL.
  - injection H as <- <- <-. pose proof (alookupE_Some _ _ _ HL) as HIn.
    destruct (HA _ _ _ HIn) as (_ & Hinfo & _). rewrite Hinfo.
    split; [split; assumption|]. split; [reflexivity|]. split; [exact HIn|]. intros; assumption.
  - injection H as <- <- <-.
    split; [|split; [reflexivity|split]].
    + split.
      * intros k b0 id0 HIn. rewrite nt_add_bucket in HIn. rewrite nt_add_info, nt_add_next.
        destruct (okey_eqb_spec k (bkey b)) as [->|NE].
        -- destruct HIn as [X|X].
           ++ injection X as <- <-. split; [reflexivity|]. rewrite pt_gss. split; [reflexivity|lia].
           ++ destruct (HA _ _ _ X) as (H1 & H2 & H3). split; [exact H1|].
              rewrite pt_gso by lia. split; [exact H2|lia].
        -- destruct (HA _ _ _ HIn) as (H1 & H2 & H3). split; [exact H1|]. rewrite pt_gso by lia. split; [exact H2|lia].
      * intros k b0 id0 id0' H1 H2. rewrite nt_add_bucket in H1, H2.
        destruct (okey_eqb_spec k (bkey b)) as [->|NE]; [|exact (HB _ _ _ _ H1 H2)].
        destruct H1 as [X1|X1]; destruct H2 as [X2|X2].
        -- congruence.
        -- injection X1 as <- <-. exfalso. exact (alookupE_None _ _ _ HL X2).
        -- injection X2 as <- <-. exfalso. exact (alookupE_None _ _ _ HL X1).
        -- exact (HB _ _ _ _ X1 X2).
    + rewrite nt_add_bucket. destruct (okey_eqb_spec (bkey b) (bkey b)); [|congruence]. left. reflexivity.
    + intros k p HIn. rewrite nt_add_bucket. destruct (okey_eqb_spec k (bkey b)); [right|]; exact HIn.
Qed.

Lemma nt_same_eq : forall bc t b1 id1 b2 id2,
  NTI bc t -> In (b1, id1) (nt_bucket t (bkey b1)) -> In (b2, id2) (nt_bucket t (bkey b2)) ->
  Pos.eqb id1 id2 = expr_eqb b1 b2.
Proof.
  intros bc t b1 id1 b2 id2 [HA HB] H1 H2.
  destruct (HA _ _ _ H1) as (_ & I1 & _). destruct (HA _ _ _ H2) as (_ & I2 & _).
  destruct (Pos.eqb_spec id1 id2) as [<-|NE].
  - rewrite I1 in I2. injection I2 as <-. symmetry. apply p_expr_eqb_refl.
  - destruct (expr_eqb b1 b2) eqn:E; [|reflexivity]. exfalso. apply NE.
    apply p_expr_eqb_eq in E. subst b2. exact (HB _ _ _ _ H1 H2).
Qed.

Record stx := STX { sx_a : saddr; sx_w : nat; sx_v : expr; sx_sp : sprep; sx_bid : positive; sx_br : option (Z * Z);
                    sx_cls : positive (* [comment removed for export] *) }.

Fixpoint mk_stxs (bc : bctx) (log : list sentry) (t : ntab) : list stx * ntab :=   (* [comment removed for export] *)
  match log with
  | [] => ([], t)
  | SE a w v :: older =>
      let '(sxs, t1) := mk_stxs bc older t in
      let '(r, t2) := intern bc t1 (a_base a) in
      let '(bid, bi) := r in
      (sxs ++ [STX a w v (mk_sprepB bc (a_base a) (a_off a) (elen w)) bid (bi_br bi) xH], t2)
  end.

Definition obrB (bc : bctx) (K : kentry) : option (Z * Z) :=
  match kbase K with Some kb => base_rangeB bc kb | None => None end.
Definition g1cB (bc : bctx) (sx : stx) (K : kentry) : list kentry :=
  fst (fst (prune1pcB bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K [] (obrB bc K))).
Fixpoint chain_slow (bc : bctx) (sxs : list stx) (l : list kentry) : list kentry :=
  match sxs with
  | [] => l
  | sx :: rest => chain_slow bc rest (flat_map (g1cB bc sx) l)
  end.
Fixpoint chainK (bc : bctx) (sxs : list stx) (K : kentry) (same_of : positive -> bool) (br2 : option (Z * Z)) : list kentry :=
  match sxs with
  | [] => [K]
  | sx :: rest =>
      match prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 with
      | PKeep => chainK bc rest K same_of br2
      | PRepl l => chain_slow bc rest l
      end
  end.
(* [comment removed for export] *)
Fixpoint chainK2 (bc : bctx) (sxs : list stx) (K : kentry) (okb : option expr) (same_of : positive -> bool) (br2 : option (Z * Z)) : list kentry :=
  match sxs with
  | [] => [K]
  | sx :: rest =>
      match prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 with
      | PKeep => chainK2 bc rest K okb same_of br2
      | PRepl l =>
          match okb with
          | Some kb =>
              flat_map (fun K' => match kbase K' with
                                  | Some kb' => if expr_eqb kb' kb then chainK2 bc rest K' okb same_of br2 else chain_slow bc rest [K']
                                  | None => chain_slow bc rest [K']
                                  end) l
          | None => chain_slow bc rest l
          end
      end
  end.


Fixpoint entriesV (bc : bctx) (sxs : list stx) (kn : list kentry) (t : ntab) : list kentry :=
  match kn with
  | [] => []
  | K :: rest =>
      match kbase K with
      | Some kb => let '(r, t') := intern bc t kb in
                   let '(bid, bi) := r in
                   chainK2 bc sxs K (Some kb) (Pos.eqb bid) (bi_br bi) ++ entriesV bc sxs rest t'
      | None => chainK2 bc sxs K None (fun _ => false) None ++ entriesV bc sxs rest t
      end
  end.
Fixpoint stores_part (bc : bctx) (sxs : list stx) : list kentry :=   (* [comment removed for export] *)
  match sxs with
  | [] => []
  | sx :: newer => stores_part bc newer ++ chainK2 bc newer (KWord (sx_a sx) (sx_w sx) (sx_v sx)) (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx)
  end.
Definition carryV (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs, t) := mk_stxs bc log nt_empty in
  stores_part bc sxs ++ entriesV bc sxs kn t.
(* [comment removed for export] *)
Definition carryK0 (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryV bc log kn, [], [])
  | _, _ => carryB bc log kn hints
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FM (fk : list kentry) (s : sentry) (l : list kentry) : list kentry :=
  match s with SE a w v => flat_map (g1 fk (mk_sprep fk (a_base a) (a_off a) (elen w)) a w v) l end.
Fixpoint chainRo (fk : list kentry) (sxo : list sentry) (l : list kentry) : list kentry :=
  match sxo with [] => l | s :: newer => chainRo fk newer (FM fk s l) end.
Definition kw (s : sentry) : kentry := match s with SE a w v => KWord a w v end.
Fixpoint SPRo (fk : list kentry) (sxo : list sentry) : list kentry :=
  match sxo with [] => [] | s :: newer => SPRo fk newer ++ chainRo fk newer [kw s] end.

Lemma flat_map_app' : forall (A B : Type) (f : A -> list B) l1 l2, flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof. intros. rewrite !flat_map_concat_map, map_app, concat_app. reflexivity. Qed.
Lemma FM_app : forall fk s l1 l2, FM fk s (l1 ++ l2) = FM fk s l1 ++ FM fk s l2.
Proof. intros fk [a w v] l1 l2. unfold FM. apply flat_map_app'. Qed.
Lemma chainRo_snoc : forall fk sxo s l, chainRo fk (sxo ++ [s]) l = FM fk s (chainRo fk sxo l).
Proof. intros fk sxo. induction sxo as [|x rest IH]; intros; [reflexivity|]. cbn [chainRo app]. apply IH. Qed.
Lemma chainRo_app : forall fk sxo l1 l2, chainRo fk sxo (l1 ++ l2) = chainRo fk sxo l1 ++ chainRo fk sxo l2.
Proof. intros fk sxo. induction sxo as [|x rest IH]; intros; [reflexivity|]. cbn [chainRo]. rewrite FM_app. apply IH. Qed.
Lemma SPRo_snoc : forall fk sxo s, SPRo fk (sxo ++ [s]) = kw s :: FM fk s (SPRo fk sxo).
Proof.
  intros fk sxo s. induction sxo as [|x rest IH]; [destruct s; reflexivity|].
  cbn [SPRo app]. rewrite IH, chainRo_snoc, FM_app. reflexivity.
Qed.

Lemma carry_vertical : forall log kn,
  carry log kn [] = (SPRo (facts_of kn) (rev log) ++ chainRo (facts_of kn) (rev log) kn, [], []).
Proof.
  intros log kn. induction log as [|[a w v] older IH]; [reflexivity|].
  cbn [carry rev]. pose proof (carry_facts older kn []) as HF. rewrite IH in HF |- *. cbn [fst] in HF.
  cbv beta iota zeta. rewrite !facts_of_filter in *. rewrite HF.
  rewrite p_prunepc_eq by constructor. rewrite prunep_nil.
  match goal with |- context [flat_map ?g ?l] => change (flat_map g l) with (FM (List.filter is_factb kn) (SE a w v) l) end.
  rewrite FM_app, SPRo_snoc, chainRo_snoc. reflexivity.
Qed.

(* [comment removed for export] *)
Definition strip (sx : stx) : sentry := SE (sx_a sx) (sx_w sx) (sx_v sx).
Definition SX_OK (bc : bctx) (t : ntab) (sx : stx) : Prop :=
  In (a_base (sx_a sx), sx_bid sx) (nt_bucket t (bkey (a_base (sx_a sx))))
  /\ sx_br sx = base_rangeB bc (a_base (sx_a sx))
  /\ sx_sp sx = mk_sprepB bc (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx)).

Lemma g1cB_eq : forall fk sx,
  sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx)) ->
  flat_map (g1cB (mkbc fk) sx) = FM fk (strip sx).
Proof.
  intros fk sx Hsp. apply functional_extensionality; intros l. unfold FM, strip. f_equal.
  apply functional_extensionality; intros K. unfold g1cB, obrB. rewrite Hsp. autorewrite with bceq.
  rewrite p_prune1pc_eq by (destruct (kbase K); reflexivity). rewrite prune1p_nil. reflexivity.
Qed.
Lemma chain_slow_eq : forall fk sxs l,
  Forall (fun sx => sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx))) sxs ->
  chain_slow (mkbc fk) sxs l = chainRo fk (map strip sxs) l.
Proof.
  intros fk sxs. induction sxs as [|sx rest IH]; intros l HF; [reflexivity|].
  apply Forall_cons_iff in HF as [H1 HF]. cbn [chain_slow chainRo map]. rewrite (g1cB_eq _ _ H1). apply IH. exact HF.
Qed.
Lemma chainK_eq : forall fk sxs K same_of br2,
  Forall (fun sx => sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx))) sxs ->
  match kbase K with
  | Some kb => br2 = base_rangeB (mkbc fk) kb /\ Forall (fun sx => same_of (sx_bid sx) = expr_eqb kb (a_base (sx_a sx))) sxs
  | None => br2 = None
  end ->
  chainK (mkbc fk) sxs K same_of br2 = chain_slow (mkbc fk) sxs [K].
Proof.
  intros fk sxs. induction sxs as [|sx rest IH]; intros K same_of br2 HS HK; [reflexivity|].
  apply Forall_cons_iff in HS as [H1 HS]. cbn [chainK chain_slow flat_map]. rewrite app_nil_r.
  unfold g1cB at 1.
  assert (E : pk_list K (prune1pcK (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2)
              = fst (fst (prune1pcB (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K [] (obrB (mkbc fk) K)))).
  { autorewrite with bceq. destruct (kbase K) as [kb|] eqn:HB.
    - destruct HK as [-> HK]. apply Forall_cons_iff in HK as [HK1 HK].
      unfold obrB. rewrite HB. apply prune1pcK_eq. rewrite HB. exact HK1.
    - unfold obrB. rewrite HB. subst br2. apply prune1pcK_eq. rewrite HB. exact I. }
  destruct (prune1pcK _ _ _ _ _ K _ br2) as [|l]; cbn [pk_list] in E.
  - rewrite <- E. apply IH; [exact HS|]. destruct (kbase K) as [kb|]; [|exact HK].
    destruct HK as [Hbr HK]. apply Forall_cons_iff in HK as [_ HK]. exact (conj Hbr HK).
  - rewrite <- E. reflexivity.
Qed.

Lemma flat_map_flat_map : forall (A B C : Type) (f : A -> list B) (g : B -> list C) l,
  flat_map g (flat_map f l) = flat_map (fun x => flat_map g (f x)) l.
Proof. intros. induction l as [|x r IH]; [reflexivity|]. cbn. rewrite flat_map_app', IH. reflexivity. Qed.
Lemma chain_slow_flat_map : forall bc sxs l, chain_slow bc sxs l = flat_map (fun K => chain_slow bc sxs [K]) l.
Proof.
  intros bc sxs. induction sxs as [|sx rest IH]; intros l.
  - cbn. induction l as [|x r IHl]; [reflexivity|]. cbn. rewrite <- IHl. reflexivity.
  - cbn [chain_slow]. rewrite IH. rewrite flat_map_flat_map.
    f_equal. apply functional_extensionality. intros K. cbn [flat_map]. rewrite app_nil_r. rewrite <- IH. reflexivity.
Qed.
Lemma chainK2_eq : forall fk sxs K okb same_of br2,
  Forall (fun sx => sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx))) sxs ->
  okb = kbase K ->
  match okb with
  | Some kb => br2 = base_rangeB (mkbc fk) kb /\ Forall (fun sx => same_of (sx_bid sx) = expr_eqb kb (a_base (sx_a sx))) sxs
  | None => br2 = None
  end ->
  chainK2 (mkbc fk) sxs K okb same_of br2 = chain_slow (mkbc fk) sxs [K].
Proof.
  intros fk sxs. induction sxs as [|sx rest IH]; intros K okb same_of br2 HS Hokb HK; [reflexivity|].
  apply Forall_cons_iff in HS as [H1 HS]. cbn [chainK2 chain_slow flat_map]. rewrite app_nil_r.
  unfold g1cB at 1.
  assert (E : pk_list K (prune1pcK (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2)
              = fst (fst (prune1pcB (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K [] (obrB (mkbc fk) K)))).
  { autorewrite with bceq. unfold obrB. rewrite <- Hokb. destruct okb as [kb|].
    - destruct HK as [-> HK]. apply Forall_cons_iff in HK as [HK1 HK]. apply prune1pcK_eq. rewrite <- Hokb. exact HK1.
    - subst br2. apply prune1pcK_eq. rewrite <- Hokb. exact I. }
  destruct (prune1pcK _ _ _ _ _ K _ br2) as [|l]; cbn [pk_list] in E; rewrite <- E.
  - apply IH; [exact HS|exact Hokb|]. destruct okb as [kb|]; [|exact HK].
    destruct HK as [Hbr HK]. apply Forall_cons_iff in HK as [_ HK]. exact (conj Hbr HK).
  - destruct okb as [kb|]; [|reflexivity]. rewrite (chain_slow_flat_map _ rest l).
    f_equal. apply functional_extensionality. intros K'.
    destruct (kbase K') as [kb'|] eqn:HB'; [|reflexivity].
    destruct (expr_eqb kb' kb) eqn:EQ; [|reflexivity].
    apply p_expr_eqb_eq in EQ. subst kb'.
    apply IH; [exact HS|symmetry; exact HB'|].
    destruct HK as [Hbr HK]. apply Forall_cons_iff in HK as [_ HK]. exact (conj Hbr HK).
Qed.



Lemma SX_OK_mono : forall bc t t' sx,
  (forall k p, In p (nt_bucket t k) -> In p (nt_bucket t' k)) -> SX_OK bc t sx -> SX_OK bc t' sx.
Proof. intros bc t t' sx Hm (H1 & H2 & H3). split; [apply Hm; exact H1|]. split; assumption. Qed.

Lemma mk_stxs_ok : forall fk log t sxs t',
  NTI (mkbc fk) t -> mk_stxs (mkbc fk) log t = (sxs, t') ->
  NTI (mkbc fk) t' /\ Forall (SX_OK (mkbc fk) t') sxs /\ map strip sxs = rev log
  /\ (forall k p, In p (nt_bucket t k) -> In p (nt_bucket t' k)).
Proof.
  intros fk log. induction log as [|[a w v] older IH]; intros t sxs t' HT H.
  - cbn in H. injection H as <- <-. split; [exact HT|]. split; [constructor|]. split; [reflexivity|]. intros; assumption.
  - cbn [mk_stxs] in H. destruct (mk_stxs (mkbc fk) older t) as [sxs0 t1] eqn:E0.
    destruct (intern (mkbc fk) t1 (a_base a)) as [[bid bi] t2] eqn:EI.
    injection H as <- <-.
    destruct (IH t sxs0 t1 HT E0) as (HT1 & HS & Hmap & Hm1).
    destruct (intern_ok _ _ _ _ _ _ HT1 EI) as (HT2 & -> & HIn & Hm2).
    split; [exact HT2|]. split.
    + apply Forall_app. split.
      * apply Forall_impl with (P := SX_OK (mkbc fk) t1); [|exact HS]. intros sx. apply SX_OK_mono. exact Hm2.
      * constructor; [|constructor]. split; [exact HIn|]. split; reflexivity.
    + split; [rewrite map_app, Hmap; reflexivity|]. intros k p Hp. apply Hm2. apply Hm1. exact Hp.
Qed.

Lemma Forall_SX_sp : forall fk t sxs, Forall (SX_OK (mkbc fk) t) sxs ->
  Forall (fun sx => sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx))) sxs.
Proof. intros fk t sxs H. apply Forall_impl with (P := SX_OK (mkbc fk) t); [|exact H]. intros sx (_ & _ & X). exact X. Qed.

Lemma Forall_SX_same : forall fk t sxs kb bid,
  NTI (mkbc fk) t -> In (kb, bid) (nt_bucket t (bkey kb)) -> Forall (SX_OK (mkbc fk) t) sxs ->
  Forall (fun sx => Pos.eqb bid (sx_bid sx) = expr_eqb kb (a_base (sx_a sx))) sxs.
Proof.
  intros fk t sxs kb bid HT HIn H. apply Forall_impl with (P := SX_OK (mkbc fk) t); [|exact H].
  intros sx (H1 & _ & _). exact (nt_same_eq _ _ _ _ _ _ HT HIn H1).
Qed.

Lemma entriesV_eq : forall fk sxs kn t,
  NTI (mkbc fk) t -> Forall (SX_OK (mkbc fk) t) sxs ->
  entriesV (mkbc fk) sxs kn t = chainRo fk (map strip sxs) kn.
Proof.
  intros fk sxs kn. induction kn as [|K rest IH]; intros t HT HS.
  - cbn. clear. induction sxs as [|sx r IH]; [reflexivity|]. cbn. destruct (strip sx). exact IH.
  - cbn [entriesV]. change (K :: rest) with ([K] ++ rest). rewrite chainRo_app.
    destruct (kbase K) as [kb|] eqn:HB.
    + destruct (intern (mkbc fk) t kb) as [[bid bi] t'] eqn:EI.
      destruct (intern_ok _ _ _ _ _ _ HT EI) as (HT' & -> & HIn & Hm).
      assert (HS' : Forall (SX_OK (mkbc fk) t') sxs).
      { apply Forall_impl with (P := SX_OK (mkbc fk) t); [|exact HS]. intros sx. apply SX_OK_mono. exact Hm. }
      rewrite (IH t' HT' HS'). f_equal.
      rewrite chainK2_eq; [apply chain_slow_eq; exact (Forall_SX_sp _ _ _ HS) | exact (Forall_SX_sp _ _ _ HS) | symmetry; exact HB |].
      cbn [bi_br]. split; [reflexivity|]. exact (Forall_SX_same _ _ _ _ _ HT' HIn HS').
    + rewrite (IH t HT HS). f_equal.
      rewrite chainK2_eq; [apply chain_slow_eq; exact (Forall_SX_sp _ _ _ HS) | exact (Forall_SX_sp _ _ _ HS) | symmetry; exact HB |].
      reflexivity.
Qed.

Lemma stores_part_eq : forall fk t sxs,
  NTI (mkbc fk) t -> Forall (SX_OK (mkbc fk) t) sxs ->
  stores_part (mkbc fk) sxs = SPRo fk (map strip sxs).
Proof.
  intros fk t sxs HT. induction sxs as [|sx newer IH]; intros HS; [reflexivity|].
  apply Forall_cons_iff in HS as [H1 HS]. cbn [stores_part SPRo map]. rewrite (IH HS). f_equal.
  destruct H1 as (HIn & Hbr & _). destruct (sx_a sx) as [b o] eqn:Ea. cbn [a_base a_off] in HIn, Hbr.
  rewrite chainK2_eq; [unfold kw, strip; rewrite Ea; apply chain_slow_eq; exact (Forall_SX_sp _ _ _ HS) | exact (Forall_SX_sp _ _ _ HS) | reflexivity |].
  cbn [a_base]. split; [exact Hbr|]. exact (Forall_SX_same _ _ _ _ _ HT HIn HS).
Qed.

Lemma carryK0_eq : forall log kn hints,
  carryK0 (mkbc (facts_of kn)) log kn hints = carry log kn hints.
Proof.
  intros log kn hints. unfold carryK0. destruct log as [|s older]; [reflexivity|].
  destruct hints as [|h hs]; [|apply carryB_eq].
  rewrite carry_vertical. unfold carryV.
  destruct (mk_stxs (mkbc (facts_of kn)) (s :: older) nt_empty) as [sxs t] eqn:E.
  destruct (mk_stxs_ok _ _ _ _ _ (NTI_empty _) E) as (HT & HS & Hmap & _).
  rewrite (stores_part_eq _ _ _ HT HS), (entriesV_eq _ _ _ _ HT HS), Hmap. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint pt_map {A B : Type} (f : A -> B) (t : ptree A) : ptree B :=
  match t with
  | PTLeaf => PTLeaf
  | PTNode l o r => PTNode (pt_map f l) (match o with Some a => Some (f a) | None => None end) (pt_map f r)
  end.
Lemma pt_get_map : forall (A B : Type) (f : A -> B) t k,
  pt_get (pt_map f t) k = match pt_get t k with Some a => Some (f a) | None => None end.
Proof. intros A B f t. induction t as [|l IHl o r IHr]; intros k; [destruct k; reflexivity|]. destruct k; cbn; auto. Qed.

(* [comment removed for export] *)
Definition kdescr (K : kentry) : option (expr * Z * option Z) :=
  match K with
  | KWord (SA kb kk) w _ => Some (kb, kk, Some (zlit64 (Z.of_nat w)))
  | KZero (SA kb kk) len | KUnk (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
      Some (kb, kk, match len with ELit z => Some (zlit64 z) | _ => None end)
  | KImg lo hi => Some (ELit 0%Z, lo, if Z.ltb (hi - lo) two64 then Some (zlit64 (hi - lo)) else None)
  | _ => None
  end.
Record einfo := EI { ei_bid : positive; ei_gid : positive; ei_kb : expr; ei_br : option (Z * Z); ei_k : Z; ei_m : option Z }.

(* [comment removed for export] *)
Definition gval : Type := (positive * expr * option (Z * Z) * (Z * Z))%type.   (* [comment removed for export] *)
Definition gtab := ptree gval.
Record gst := GST { gs_gid : ptree (ptree positive); gs_next : positive; gs_bnds : gtab }.
Definition gst_empty : gst := GST PTLeaf xH PTLeaf.
Definition gkey (kk : Z) : positive :=
  let g := Z.shiftr kk 16 in Z.to_pos (if Z.leb 0 g then 2 * g + 1 else - (2 * g))%Z.
Definition ggroup (gs : gst) (bid : positive) (kk : Z) : positive * gst :=
  let gk := gkey kk in
  let inner := match pt_get (gs_gid gs) bid with Some i => i | None => PTLeaf end in
  match pt_get inner gk with
  | Some gid => (gid, gs)
  | None => let gid := gs_next gs in
            (gid, GST (pt_set bid (pt_set gk gid inner) (gs_gid gs)) (Pos.succ gid) (gs_bnds gs))
  end.
Definition bnd_add (gs : gst) (gid bid : positive) (kb : expr) (obr : option (Z * Z)) (lo hi : Z) : gst :=
  GST (gs_gid gs) (gs_next gs)
      (match pt_get (gs_bnds gs) gid with
       | Some (b, gb, o, (l, h)) => pt_set gid (b, gb, o, (Z.min l lo, Z.max h hi)) (gs_bnds gs)
       | None => pt_set gid (bid, kb, obr, (lo, hi)) (gs_bnds gs)
       end).
Fixpoint scan_entries (bc : bctx) (kn : list kentry) (t : ntab) (gs : gst) : list (option einfo) * ntab * gst :=
  match kn with
  | [] => ([], t, gs)
  | K :: rest =>
      match kdescr K with
      | Some (kb, kk, om) =>
          let '(r, t1) := intern bc t kb in
          let '(bid, bi) := r in
          let '(gid, gs1) := match om with
                             | Some m => let '(gid, gs0) := ggroup gs bid kk in (gid, bnd_add gs0 gid bid kb (bi_br bi) kk (kk + m)%Z)
                             | None => (xH, gs)
                             end in
          let '(infos, t2, gs2) := scan_entries bc rest t1 gs1 in
          (Some (EI bid gid kb (bi_br bi) kk om) :: infos, t2, gs2)
      | None =>
          let '(infos, t2, gs2) := scan_entries bc rest t gs in
          (None :: infos, t2, gs2)
      end
  end.

Definition sx_m1 (sx : stx) : Z := zlit64 (Z.of_nat (sx_w sx)).
(* [comment removed for export] *)
Definition verdict (sx : stx) (g : gval) : bool :=
  match g with
  | (b, _, obr, (glo, ghi)) =>
      if Pos.eqb b (sx_bid sx) then false else
      match sp_rng (sx_sp sx), obr with
      | Some (lo1, hi1), Some (lo2, hi2) =>
          (Z.leb (hi1 + a_off (sx_a sx) + sx_m1 sx - lo2) glo || Z.leb ghi (lo1 + a_off (sx_a sx) - hi2))%bool
      | _, _ => false
      end
  end.
(* [comment removed for export] *)
Definition verdict_s (bc : bctx) (sx : stx) (g : gval) : bool :=
  match g with
  | (b, gb, _, (glo, ghi)) =>
      if Pos.eqb b (sx_bid sx) then false else
      if in_sides1B bc (sp_D (sx_sp sx)) gb glo (ghi - glo) then true
      else if in_sidesLB (sp_D (sx_sp sx)) gb glo (ghi - glo) then true   (* [comment removed for export] *)
      else in_sidesPB bc (sp_D (sx_sp sx)) gb glo (ghi - glo)             (* [comment removed for export] *)
  end.
Definition verdict2 (bc : bctx) (sx : stx) (g : gval) : bool := if verdict sx g then true else verdict_s bc sx g.
(* [comment removed for export] *)
Fixpoint mk_fl (bc : bctx) (g : gval) (sxs : list stx) : list (stx * list stx) :=
  match sxs with
  | [] => []
  | sx :: rest => if verdict2 bc sx g then mk_fl bc g rest else (sx, rest) :: mk_fl bc g rest
  end.
Definition gfl : Type := (gval * list (stx * list stx))%type.
Definition mk_gl (bc : bctx) (bnds : gtab) (sxs : list stx) : ptree gfl := pt_map (fun g => (g, mk_fl bc g sxs)) bnds.
(* [comment removed for export] *)
Definition side_eqb (p q : saddr * expr) : bool := if saddr_eqb (fst p) (fst q) then expr_eqb (snd p) (snd q) else false.
Fixpoint dl_eqb (a b : list (saddr * expr)) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => if side_eqb x y then dl_eqb a' b' else false
  | _, _ => false
  end.
Definition ckey_eqb (sx sy : stx) : bool :=
  if Pos.eqb (sx_bid sx) (sx_bid sy) then
    if dl_eqb (sp_D (sx_sp sx)) (sp_D (sx_sp sy)) then dl_eqb (sp_Dx (sx_sp sx)) (sp_Dx (sx_sp sy)) else false
  else false.
Definition set_cls (sx : stx) (c : positive) : stx := STX (sx_a sx) (sx_w sx) (sx_v sx) (sx_sp sx) (sx_bid sx) (sx_br sx) c.
Fixpoint cls_find (tab : list stx) (sx : stx) : option positive :=
  match tab with [] => None | r :: t => if ckey_eqb sx r then Some (sx_cls r) else cls_find t sx end.
Fixpoint assign_cls (sxs : list stx) (tab : list stx) (next : positive) : list stx :=
  match sxs with
  | [] => []
  | sx :: rest =>
      match cls_find tab sx with
      | Some c => set_cls sx c :: assign_cls rest tab next
      | None => let r := set_cls sx next in r :: assign_cls rest (r :: tab) (Pos.succ next)
      end
  end.
Definition smemo : Type := list (positive * bool).
Fixpoint smemo_find (m : smemo) (c : positive) : option bool :=
  match m with [] => None | (c', v) :: t => if Pos.eqb c' c then Some v else smemo_find t c end.
Fixpoint mk_flM (bc : bctx) (g : gval) (sxs : list stx) (memo : smemo) : list (stx * list stx) :=
  match sxs with
  | [] => []
  | sx :: rest =>
      if verdict sx g then mk_flM bc g rest memo else
      match smemo_find memo (sx_cls sx) with
      | Some v => if v then mk_flM bc g rest memo else (sx, rest) :: mk_flM bc g rest memo
      | None => let v := verdict_s bc sx g in
                let memo' := (sx_cls sx, v) :: memo in
                if v then mk_flM bc g rest memo' else (sx, rest) :: mk_flM bc g rest memo'
      end
  end.
Definition mk_glM (bc : bctx) (bnds : gtab) (sxs : list stx) : ptree gfl := pt_map (fun g => (g, mk_flM bc g sxs [])) bnds.

Definition obr_eqb (a b : option (Z * Z)) : bool :=
  match a, b with
  | Some (x1, y1), Some (x2, y2) => Z.eqb x1 x2 && Z.eqb y1 y2
  | None, None => true
  | _, _ => false
  end%bool.
(* [comment removed for export] *)
Definition inb (g : gval) (ei : einfo) : bool :=
  match ei_m ei, g with
  | Some m, (b, gb, obr, (lo, hi)) =>
      Pos.eqb b (ei_bid ei) && obr_eqb obr (ei_br ei) && Z.leb lo (ei_k ei) && Z.leb (ei_k ei + m) hi && expr_eqb gb (ei_kb ei)
  | _, _ => false
  end%bool.

Fixpoint chainKF (bc : bctx) (fl : list (stx * list stx)) (K : kentry) (okb : option expr) (same_of : positive -> bool)
         (br2 : option (Z * Z)) : list kentry :=
  match fl with
  | [] => [K]
  | (sx, rest) :: fl' =>
      match prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 with
      | PKeep => chainKF bc fl' K okb same_of br2
      | PRepl l =>
          match okb with
          | Some kb =>
              flat_map (fun K' => match kbase K' with
                                  | Some kb' => if expr_eqb kb' kb then chainK2 bc rest K' okb same_of br2 else chain_slow bc rest [K']
                                  | None => chain_slow bc rest [K']
                                  end) l
          | None => chain_slow bc rest l
          end
      end
  end.

Fixpoint entriesG (bc : bctx) (sxs : list stx) (gl : ptree gfl) (kn : list kentry) (infos : list (option einfo)) : list kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      (match oi with
       | Some ei =>
           let okb := kbase K in
           let same_of := match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end in
           let br2 := match okb with Some _ => ei_br ei | None => None end in
           match pt_get gl (ei_gid ei) with
           | Some (g, fl) => if inb g ei then chainKF bc fl K okb same_of br2 else chainK2 bc sxs K okb same_of br2
           | None => chainK2 bc sxs K okb same_of br2
           end
       | None => chainK2 bc sxs K None (fun _ => false) None
       end) ++ entriesG bc sxs gl rest irest
  | _, _ => []
  end.

(* [comment removed for export] *)
Definition rapc_num (bc : bctx) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr) (br2 : option (Z * Z)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      match sp_rng sp, br2 with
      | Some (lo1, hi1), Some (lo2, hi2) => (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
      | _, _ => false
      end
  | _, _ =>
      match sp_rng sp, br2, sp_h1 sp, xhiB bc n2 with
      | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
          if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
          else if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
          else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
      | _, _, _, _ => false
      end
  end.
Definition rapc_side (bc : bctx) (sp : sprep) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit _, ELit z2 => in_sidesHB bc (sp_D sp) b2 k2 (zlit64 z2)
  | _, _ => in_sides_xHB bc (sp_Dx sp) b2 k2 n2
  end.
Definition rapc_lin (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 => lin_apartB bc b1 k1 (zlit64 z1) b2 k2 (zlit64 z2)
  | _, _ =>
      if negb (shares_var b1 b2) then false
      else if lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
      else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.
(* [comment removed for export] *)
Definition kspan (K : kentry) : option (expr * Z * expr) :=
  match K with
  | KWord (SA kb kk) w' _ => Some (kb, kk, elen w')
  | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KUnk (SA kb kk) len | KBlob (SA kb kk) len _ => Some (kb, kk, len)
  | _ => None
  end.
(* [comment removed for export] *)
Definition prune1pcK_R (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (r : bool) : pk_res :=
  let k := a_off wa in
  let wb := a_base wa in
  let zfR (mk : saddr -> expr -> kentry) (kb : expr) (kk : Z) (len : expr) :=
    if r then PKeep
    else match kcutB bc mk wb k (elen w) kb kk len with
         | [] => PRepl []
         | cut => PRepl cut
         end in
  match K with
  | KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ => PKeep
  | KImg lo hi =>
      match wb with
      | ELit 0 =>
          let r1 := if Z.ltb lo (Z.min k hi) then [KImg lo (Z.min k hi)] else [] in
          let lo2 := Z.max lo (k + Z.of_nat w) in
          let r2 := if Z.ltb lo2 hi then [KImg lo2 hi] else [] in
          PRepl (r1 ++ r2)
      | _ => if Z.ltb (hi - lo) two64 then
               (if ranges_apart_pB bc sp wb k (elen w) (ELit 0) lo (ELit (hi - lo)) then PKeep else PRepl [])
             else PRepl []
      end
  | KZero (SA kb kk) len => zfR KZero kb kk len
  | KFill (SA kb kk) len c => zfR (fun a n => KFill a n c) kb kk len
  | KUnk (SA kb kk) len => zfR KUnk kb kk len
  | KWord (SA kb kk) w' v =>
      if r then PKeep
      else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool then PKeep
      else PRepl []
  | KBlob (SA kb kk) len bk => if r then PKeep else PRepl []
  end.
(* [comment removed for export] *)
Definition step_r (bc : bctx) (sx : stx) (br2 : option (Z * Z)) (K : kentry) (memo : smemo) : bool * smemo :=
  match kspan K with
  | Some (kb, kk, len) =>
      let wb := a_base (sx_a sx) in let k := a_off (sx_a sx) in let n1 := elen (sx_w sx) in
      if rapc_num bc (sx_sp sx) wb k n1 br2 kb kk len then (true, memo)
      else match smemo_find memo (sx_cls sx) with
           | Some sd => (if sd then true else rapc_lin bc wb k n1 kb kk len, memo)
           | None => let sd := rapc_side bc (sx_sp sx) n1 kb kk len in
                     (if sd then true else rapc_lin bc wb k n1 kb kk len, (sx_cls sx, sd) :: memo)
           end
  | None => (false, memo)
  end.
Definition prune1pcKM (bc : bctx) (sx : stx) (K : kentry) (same : bool) (br2 : option (Z * Z)) (memo : smemo) : pk_res * smemo :=
  if same then (prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K true br2, memo)
  else let '(r, memo') := step_r bc sx br2 K memo in
       (prune1pcK_R bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K r, memo').
Fixpoint chainK2M (bc : bctx) (sxs : list stx) (K : kentry) (okb : option expr) (same_of : positive -> bool) (br2 : option (Z * Z))
         (memo : smemo) : list kentry :=
  match sxs with
  | [] => [K]
  | sx :: rest =>
      let '(pr, memo') := prune1pcKM bc sx K (same_of (sx_bid sx)) br2 memo in
      match pr with
      | PKeep => chainK2M bc rest K okb same_of br2 memo'
      | PRepl l =>
          match okb with
          | Some kb =>
              flat_map (fun K' => match kbase K' with
                                  | Some kb' => if expr_eqb kb' kb then chainK2M bc rest K' okb same_of br2 [] else chain_slow bc rest [K']
                                  | None => chain_slow bc rest [K']
                                  end) l
          | None => chain_slow bc rest l
          end
      end
  end.
Fixpoint chainKFM (bc : bctx) (fl : list (stx * list stx)) (K : kentry) (okb : option expr) (same_of : positive -> bool)
         (br2 : option (Z * Z)) (memo : smemo) : list kentry :=
  match fl with
  | [] => [K]
  | (sx, rest) :: fl' =>
      let '(pr, memo') := prune1pcKM bc sx K (same_of (sx_bid sx)) br2 memo in
      match pr with
      | PKeep => chainKFM bc fl' K okb same_of br2 memo'
      | PRepl l =>
          match okb with
          | Some kb =>
              flat_map (fun K' => match kbase K' with
                                  | Some kb' => if expr_eqb kb' kb then chainK2M bc rest K' okb same_of br2 [] else chain_slow bc rest [K']
                                  | None => chain_slow bc rest [K']
                                  end) l
          | None => chain_slow bc rest l
          end
      end
  end.
Fixpoint stores_partM (bc : bctx) (sxs : list stx) : list kentry :=   (* [comment removed for export] *)
  match sxs with
  | [] => []
  | sx :: newer => stores_partM bc newer ++ chainK2M bc newer (KWord (sx_a sx) (sx_w sx) (sx_v sx)) (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx) []
  end.
Fixpoint entriesGM (bc : bctx) (sxs : list stx) (gl : ptree gfl) (kn : list kentry) (infos : list (option einfo)) : list kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      (match oi with
       | Some ei =>
           let okb := kbase K in
           let same_of := match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end in
           let br2 := match okb with Some _ => ei_br ei | None => None end in
           match pt_get gl (ei_gid ei) with
           | Some (g, fl) => if inb g ei then chainKFM bc fl K okb same_of br2 [] else chainK2M bc sxs K okb same_of br2 []
           | None => chainK2M bc sxs K okb same_of br2 []
           end
       | None => [K]      (* [comment removed for export] *)
       end) ++ entriesGM bc sxs gl rest irest
  | _, _ => []
  end.

Definition carryG (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs0, t0) := mk_stxs bc log nt_empty in
  let sxs := assign_cls sxs0 [] xH in      (* [comment removed for export] *)
  let '(r, gs) := scan_entries bc kn t0 gst_empty in
  let '(infos, _) := r in
  stores_partM bc sxs ++ entriesGM bc sxs (mk_glM bc (gs_bnds gs) sxs) kn infos.

(* [comment removed for export] *)
Lemma zlit64_idem : forall z, zlit64 (zlit64 z) = zlit64 z.
Proof.
  intros z. unfold zlit64. destruct (Z.leb 0 z && Z.ltb z two64)%bool eqn:E; [rewrite E; reflexivity|].
  pose proof (Z.mod_pos_bound z two64 ltac:(unfold two64; lia)) as B.
  replace (Z.leb 0 (z mod two64) && Z.ltb (z mod two64) two64)%bool with true; [reflexivity|].
  symmetry. apply andb_true_intro. split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.

Lemma kdescr_kbase : forall K kb kk om,
  kdescr K = Some (kb, kk, om) -> kbase K = Some kb \/ (exists lo hi, K = KImg lo hi /\ kb = ELit 0%Z /\ kk = lo).
Proof.
  intros K kb kk om H.
  destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
    cbn [kdescr kbase] in *; try discriminate; try (injection H as <- <- Hm); try (left; reflexivity).
  right. exists lo, hi. repeat split; congruence.
Qed.
Lemma kdescr_None_kbase : forall K, kdescr K = None -> kbase K = None.
Proof.
  intros K H. destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
    cbn [kdescr kbase] in *; try discriminate; reflexivity.
Qed.

Lemma prune1pcK_keep_based : forall bc sp wa w wv K kb kk m lo1 hi1 lo2 hi2,
  kbase K = Some kb -> kdescr K = Some (kb, kk, Some m) ->
  sp_rng sp = Some (lo1, hi1) -> base_rangeB bc kb = Some (lo2, hi2) ->
  (hi1 + a_off wa + zlit64 (Z.of_nat w) <= lo2 + kk \/ hi2 + kk + m <= lo1 + a_off wa)%Z ->
  prune1pcK bc sp wa w wv K false (base_rangeB bc kb) = PKeep.
Proof.
  intros bc sp wa w wv K kb kk m lo1 hi1 lo2 hi2 HB HD Hsp Hbr Hnum.
  destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
    cbn [kbase kdescr] in HB, HD; try discriminate; injection HB as ->;
    try (injection HD as <- <-); try (destruct len as [z| | | | | | |]; try discriminate; injection HD as <- <-);
    unfold prune1pcK; cbn [a_base a_off]; unfold ranges_apart_pcB; rewrite ?in_sidesHB_feq, ?in_sides_xHB_feq; cbn [elen]; rewrite Hsp, Hbr;
    match goal with |- context [if ((?a <=? ?b) || (?c <=? ?d))%Z then _ else _] =>
      replace ((a <=? b) || (c <=? d))%Z%bool with true; [reflexivity|];
      symmetry; apply Bool.orb_true_iff; destruct Hnum as [H|H]; [left|right]; apply Z.leb_le; rewrite ?zlit64_idem; lia end.
Qed.

Lemma prune1pcK_keep_img : forall bc sp wa w wv lo hi m lo1 hi1 lo2 hi2 same br2,
  kdescr (KImg lo hi) = Some (ELit 0%Z, lo, Some m) ->
  expr_eqb (ELit 0%Z) (a_base wa) = false ->
  sp_rng sp = Some (lo1, hi1) -> base_rangeB bc (ELit 0%Z) = Some (lo2, hi2) ->
  (hi1 + a_off wa + zlit64 (Z.of_nat w) <= lo2 + lo \/ hi2 + lo + m <= lo1 + a_off wa)%Z ->
  prune1pcK bc sp wa w wv (KImg lo hi) same br2 = PKeep.
Proof.
  intros bc sp wa w wv lo hi m lo1 hi1 lo2 hi2 same br2 HD Hne Hsp Hbr Hnum.
  cbn [kdescr] in HD. destruct (Z.ltb (hi - lo) two64) eqn:Hlt; [|discriminate]. injection HD as <-.
  unfold prune1pcK. destruct wa as [wb k]. cbn [a_base a_off] in *.
  assert (STEP : (if ranges_apart_pB bc sp wb k (elen w) (ELit 0%Z) lo (ELit (hi - lo)) then PKeep else PRepl []) = PKeep).
  { unfold ranges_apart_pB. rewrite ?in_sidesHB_feq, ?in_sides_xHB_feq. cbn [elen]. rewrite Hsp, Hbr.
    match goal with |- context [if ((?a <=? ?b) || (?c <=? ?d))%Z then _ else _] =>
      replace ((a <=? b) || (c <=? d))%Z%bool with true; [reflexivity|];
      symmetry; apply Bool.orb_true_iff; destruct Hnum as [H|H]; [left|right]; apply Z.leb_le; rewrite ?zlit64_idem; lia end. }
  rewrite Hlt. destruct wb as [z| | | | | | |]; try exact STEP.
  destruct z; try exact STEP. cbn in Hne. discriminate.
Qed.

(* [comment removed for export] *)
Definition EINF (bc : bctx) (t : ntab) (K : kentry) (oi : option einfo) : Prop :=
  match oi with
  | None => kdescr K = None
  | Some ei => kdescr K = Some (ei_kb ei, ei_k ei, ei_m ei)
               /\ In (ei_kb ei, ei_bid ei) (nt_bucket t (bkey (ei_kb ei)))
               /\ ei_br ei = base_rangeB bc (ei_kb ei)
  end.
Lemma EINF_mono : forall bc t t' K oi,
  (forall k p, In p (nt_bucket t k) -> In p (nt_bucket t' k)) -> EINF bc t K oi -> EINF bc t' K oi.
Proof. intros bc t t' K [ei|] Hm H; cbn [EINF] in *; [|exact H]. destruct H as (A & B & C). split; [exact A|]. split; [apply Hm; exact B| exact C]. Qed.

Lemma scan_entries_ok : forall fk kn t gs infos t' gs',
  NTI (mkbc fk) t -> scan_entries (mkbc fk) kn t gs = (infos, t', gs') ->
  NTI (mkbc fk) t'
  /\ (forall k p, In p (nt_bucket t k) -> In p (nt_bucket t' k))
  /\ Forall2 (EINF (mkbc fk) t') kn infos.
Proof.
  intros fk kn. induction kn as [|K rest IH]; intros t gs infos t' gs' HT H.
  - cbn in H. injection H as <- <- <-. split; [exact HT|]. split; [intros; assumption|]. constructor.
  - cbn [scan_entries] in H.
    destruct (kdescr K) as [[[kb kk] om]|] eqn:HD.
    + destruct (intern (mkbc fk) t kb) as [[bid bi] t1] eqn:EI.
      destruct (intern_ok _ _ _ _ _ _ HT EI) as (HT1 & Hbi & HIn & Hm1).
      lazymatch type of H with (let '(_, _) := ?X in _) = _ => destruct X as [gid gs1] end.
      destruct (scan_entries (mkbc fk) rest t1 _) as [[infos2 t2] gs2] eqn:ES.
      injection H as <- <- <-.
      destruct (IH _ _ _ _ _ HT1 ES) as (HT2 & Hm2 & HF).
      split; [exact HT2|]. split; [intros k p Hp; apply Hm2; apply Hm1; exact Hp|].
      constructor; [|exact HF]. cbn [EINF ei_kb ei_k ei_m ei_bid ei_br].
      split; [exact HD|]. split; [apply Hm2; exact HIn|]. rewrite Hbi. reflexivity.
    + destruct (scan_entries (mkbc fk) rest t gs) as [[infos2 t2] gs2] eqn:ES.
      injection H as <- <- <-.
      destruct (IH _ _ _ _ _ HT ES) as (HT2 & Hm2 & HF).
      split; [exact HT2|]. split; [exact Hm2|]. constructor; [exact HD | exact HF].
Qed.

(* [comment removed for export] *)
Lemma sub_itv1B_mono : forall bc b glo glen kk m c mm,
  sub_itv1B bc b glo glen c mm = true -> (glo <= kk)%Z -> (kk + m <= glo + glen)%Z -> sub_itv1B bc b kk m c mm = true.
Proof.
  intros bc b glo glen kk m c mm H H1 H2. unfold sub_itv1B in *.
  destruct (expr_eqb b (a_base c)); [|discriminate]. cbn [andb] in *.
  destruct (Z.leb_spec (a_off c) glo) as [Ho|]; [|discriminate].
  destruct (xloB bc mm) as [ml|]; [|discriminate]. apply Z.leb_le in H.
  replace (Z.leb (a_off c) kk) with true by (symmetry; apply Z.leb_le; lia). apply Z.leb_le. lia.
Qed.
Lemma in_sides1B_mono : forall bc D b glo glen kk m,
  in_sides1B bc D b glo glen = true -> (glo <= kk)%Z -> (kk + m <= glo + glen)%Z -> in_sides1B bc D b kk m = true.
Proof.
  intros bc D b glo glen kk m H H1 H2. induction D as [|[c mm] r IH]; [discriminate|]. cbn [in_sides1B] in *.
  destruct (sub_itv1B bc b glo glen c mm) eqn:E.
  - rewrite (sub_itv1B_mono _ _ _ _ _ _ _ _ E H1 H2). reflexivity.
  - rewrite (IH H). destruct (sub_itv1B bc b kk m c mm); reflexivity.
Qed.
Lemma ranges_apart_pcB_side1 : forall bc sp b1 k1 w br2 b2 k2 z2,
  in_sidesB bc (sp_D sp) b2 k2 (zlit64 z2) = true ->
  ranges_apart_pcB bc sp b1 k1 (elen w) br2 b2 k2 (ELit z2) = true.
Proof.
  intros bc sp b1 k1 w br2 b2 k2 z2 H. unfold ranges_apart_pcB. rewrite ?in_sidesHB_feq, ?in_sides_xHB_feq. cbn [elen]. rewrite H.
  destruct (match sp_rng sp with Some (lo1, hi1) => match br2 with Some (lo2, hi2) => _ | None => false end | None => false end); reflexivity.
Qed.
Lemma prune1pcK_keep_side : forall bc sp wa w wv K kb kk m br2,
  kbase K = Some kb -> kdescr K = Some (kb, kk, Some m) ->
  in_sidesB bc (sp_D sp) kb kk m = true ->
  prune1pcK bc sp wa w wv K false br2 = PKeep.
Proof.
  intros bc sp wa w wv K kb kk m br2 HB HD Hs.
  destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
    cbn [kbase kdescr] in HB, HD; try discriminate; injection HB as ->;
    try (injection HD as <- <-); try (destruct len as [z| | | | | | |]; try discriminate; injection HD as <- <-);
    unfold prune1pcK; cbn [a_base a_off];
    try (change (elen w') with (ELit (Z.of_nat w')));
    rewrite ?(ranges_apart_pcB_side1 bc sp (a_base wa) (a_off wa) w br2 _ _ _ Hs); reflexivity.
Qed.
Lemma prune1pcK_keep_img_side : forall bc sp wa w wv lo hi m same br2,
  kdescr (KImg lo hi) = Some (ELit 0%Z, lo, Some m) ->
  expr_eqb (ELit 0%Z) (a_base wa) = false ->
  in_sidesB bc (sp_D sp) (ELit 0%Z) lo m = true ->
  prune1pcK bc sp wa w wv (KImg lo hi) same br2 = PKeep.
Proof.
  intros bc sp wa w wv lo hi m same br2 HD Hne Hs.
  cbn [kdescr] in HD. destruct (Z.ltb (hi - lo) two64) eqn:Hlt; [|discriminate]. injection HD as <-.
  unfold prune1pcK. destruct wa as [wb k]. cbn [a_base a_off] in *.
  assert (STEP : (if ranges_apart_pB bc sp wb k (elen w) (ELit 0%Z) lo (ELit (hi - lo)) then PKeep else PRepl []) = PKeep).
  { unfold ranges_apart_pB. rewrite ?in_sidesHB_feq, ?in_sides_xHB_feq. cbn [elen]. rewrite Hs.
    destruct (match sp_rng sp with Some (lo1, hi1) => match base_rangeB bc (ELit 0%Z) with Some (lo2, hi2) => _ | None => false end | None => false end); reflexivity. }
  rewrite Hlt. destruct wb as [z| | | | | | |]; try exact STEP.
  destruct z; try exact STEP. cbn in Hne. discriminate.
Qed.
(* [comment removed for export] *)
Lemma verdict_s_inb : forall bc sx g ei m,
  verdict_s bc sx g = true -> inb g ei = true -> ei_m ei = Some m -> (0 <= m < two64)%Z ->
  Pos.eqb (ei_bid ei) (sx_bid sx) = false /\ in_sidesB bc (sp_D (sx_sp sx)) (ei_kb ei) (ei_k ei) m = true.
Proof.
  intros bc sx [[[b gb] obr] [glo ghi]] ei m Hv Hi Hm Hmr. unfold verdict_s in Hv. unfold inb in Hi. rewrite Hm in Hi.
  apply andb_prop in Hi as [Hi H5]. apply andb_prop in Hi as [Hi H4]. apply andb_prop in Hi as [Hi H3]. apply andb_prop in Hi as [H1 _].
  apply Pos.eqb_eq in H1. subst b. apply Z.leb_le in H3. apply Z.leb_le in H4. apply p_expr_eqb_eq in H5. subst gb.
  destruct (Pos.eqb (ei_bid ei) (sx_bid sx)); [discriminate|]. split; [reflexivity|].
  destruct (in_sides1B bc (sp_D (sx_sp sx)) (ei_kb ei) glo (ghi - glo)) eqn:H1B.
  - unfold in_sidesB. rewrite (in_sides1B_mono _ _ _ _ _ (ei_k ei) m H1B H3 ltac:(lia)). reflexivity.
  - destruct (in_sidesLB (sp_D (sx_sp sx)) (ei_kb ei) glo (ghi - glo)) eqn:HLB.
    + apply in_sidesLB_B; [|exact Hmr]. eapply in_sidesLB_mono; [exact HLB | exact H3 | lia].
    + apply in_sidesPB_B. eapply in_sidesPB_mono; [exact Hv | exact H3 | lia | lia].
Qed.
Lemma kdescr_m_range : forall K kb kk m, kdescr K = Some (kb, kk, Some m) -> (0 <= m < two64)%Z.
Proof.
  intros K kb kk m H.
  destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
    cbn [kdescr] in H; try discriminate;
    try (destruct len as [z| | | | | | |]; try discriminate); try (destruct (Z.ltb (hi - lo) two64); try discriminate);
    injection H as _ _ <-; apply zlit64_range.
Qed.

Lemma chainKF_eq : forall bc g sxs K okb same_of br2,
  (forall sx, In sx sxs -> verdict2 bc sx g = true ->
     prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 = PKeep) ->
  chainKF bc (mk_fl bc g sxs) K okb same_of br2 = chainK2 bc sxs K okb same_of br2.
Proof.
  intros bc g sxs. induction sxs as [|sx rest IH]; intros K okb same_of br2 Hf; [reflexivity|].
  cbn [mk_fl chainK2].
  assert (IH' : chainKF bc (mk_fl bc g rest) K okb same_of br2 = chainK2 bc rest K okb same_of br2)
    by (apply IH; intros; apply Hf; [right|]; assumption).
  destruct (verdict2 bc sx g) eqn:Hv.
  - rewrite (Hf sx (or_introl eq_refl) Hv). exact IH'.
  - cbn [chainKF]. destruct (prune1pcK _ _ _ _ _ K _ br2); [exact IH'|reflexivity].
Qed.

(* [comment removed for export] *)
Lemma verdict_inb_num : forall sx g ei m,
  verdict sx g = true -> inb g ei = true -> ei_m ei = Some m ->
  Pos.eqb (ei_bid ei) (sx_bid sx) = false
  /\ exists lo1 hi1 lo2 hi2, sp_rng (sx_sp sx) = Some (lo1, hi1) /\ ei_br ei = Some (lo2, hi2)
     /\ (hi1 + a_off (sx_a sx) + zlit64 (Z.of_nat (sx_w sx)) <= lo2 + ei_k ei \/ hi2 + ei_k ei + m <= lo1 + a_off (sx_a sx))%Z.
Proof.
  intros sx [[[b gb] obr] [glo ghi]] ei m Hv Hi Hm. unfold verdict in Hv. unfold inb in Hi. rewrite Hm in Hi.
  apply andb_prop in Hi as [Hi _]. apply andb_prop in Hi as [Hi H4]. apply andb_prop in Hi as [Hi H3]. apply andb_prop in Hi as [H1 H2].
  apply Pos.eqb_eq in H1. subst b. apply Z.leb_le in H3. apply Z.leb_le in H4.
  destruct (Pos.eqb (ei_bid ei) (sx_bid sx)); [discriminate|]. split; [reflexivity|].
  destruct (sp_rng (sx_sp sx)) as [[lo1 hi1]|]; [|discriminate].
  destruct obr as [[lo2 hi2]|]; [|discriminate].
  destruct (ei_br ei) as [[x2 y2]|]; [|discriminate]. cbn [obr_eqb] in H2. apply andb_prop in H2 as [X Y].
  apply Z.eqb_eq in X. apply Z.eqb_eq in Y. subst x2 y2.
  exists lo1, hi1, lo2, hi2. split; [reflexivity|]. split; [reflexivity|].
  unfold sx_m1 in Hv. apply Bool.orb_prop in Hv. destruct Hv as [H|H]; apply Z.leb_le in H; lia.
Qed.

Lemma entriesG_eq : forall fk sxs bnds kn infos t1,
  NTI (mkbc fk) t1 -> Forall (SX_OK (mkbc fk) t1) sxs -> Forall2 (EINF (mkbc fk) t1) kn infos ->
  entriesG (mkbc fk) sxs (mk_gl (mkbc fk) bnds sxs) kn infos = chainRo fk (map strip sxs) kn.
Proof.
  intros fk sxs bnds kn infos t1 HT HS HF. induction HF as [|K oi rest irest HK HF IH].
  - cbn. clear. induction sxs as [|sx r IH]; [reflexivity|]. cbn. destruct (strip sx). exact IH.
  - cbn [entriesG]. change (K :: rest) with ([K] ++ rest). rewrite chainRo_app, IH. f_equal.
    rewrite <- (chain_slow_eq fk sxs [K] (Forall_SX_sp _ _ _ HS)).
    pose proof (Forall_SX_sp _ _ _ HS) as HSP.
    destruct oi as [ei|]; cbn [EINF] in HK.
    + destruct HK as (HD & HIn & Hbr).
      (* [comment removed for export] *)
      assert (FULL : forall okb, okb = kbase K ->
        chainK2 (mkbc fk) sxs K okb
          (match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end)
          (match okb with Some _ => ei_br ei | None => None end) = chain_slow (mkbc fk) sxs [K]).
      { intros okb Hokb. apply chainK2_eq; [exact HSP|exact Hokb|].
        destruct okb as [kb|]; [|reflexivity].
        destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & _ & _)]; [|cbn in Hokb; discriminate].
        rewrite <- Hokb in HB. injection HB as ->.
        split; [exact Hbr|]. exact (Forall_SX_same _ _ _ _ _ HT HIn HS). }
      unfold mk_gl. rewrite pt_get_map.
      destruct (pt_get bnds (ei_gid ei)) as [g|]; [|apply FULL; reflexivity].
      destruct (inb g ei) eqn:Hinb; [|apply FULL; reflexivity].
      rewrite <- (FULL (kbase K) eq_refl). apply chainKF_eq.
      intros sx Hsx Hv.
      assert (Hm : exists m, ei_m ei = Some m).
      { unfold inb in Hinb. destruct (ei_m ei) as [m|]; [exists m; reflexivity|discriminate]. }
      destruct Hm as [m Hm].
      pose proof (proj1 (Forall_forall _ _) HS sx Hsx) as (SXin & SXbr & SXsp).
      rewrite Hm in HD.
      unfold verdict2 in Hv. destruct (verdict sx g) eqn:Hv1.
      { destruct (verdict_inb_num _ _ _ _ Hv1 Hinb Hm) as (Hne & lo1 & hi1 & lo2 & hi2 & Hsp & Hbr2 & Hnum).
        destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & Hk)].
        * rewrite HB. rewrite Hne. rewrite Hbr. eapply prune1pcK_keep_based; [exact HB|exact HD|exact Hsp| | exact Hnum].
          rewrite <- Hbr. exact Hbr2.
        * cbn [kbase]. rewrite Hkb, Hk in *.
          eapply prune1pcK_keep_img; [exact HD| |exact Hsp| rewrite <- Hbr; exact Hbr2 | exact Hnum].
          rewrite <- (nt_same_eq _ _ _ _ _ _ HT HIn SXin). exact Hne. }
      destruct (verdict_s_inb _ _ _ _ _ Hv Hinb Hm (kdescr_m_range _ _ _ _ HD)) as (Hne & Hs1).
      destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & Hk)].
      * rewrite HB. rewrite Hne. eapply prune1pcK_keep_side; [exact HB|exact HD|exact Hs1].
      * cbn [kbase]. rewrite Hkb, Hk in *.
        eapply prune1pcK_keep_img_side; [exact HD| |exact Hs1].
        rewrite <- (nt_same_eq _ _ _ _ _ _ HT HIn SXin). exact Hne.
    + apply chainK2_eq; [exact HSP| symmetry; apply kdescr_None_kbase; exact HK | reflexivity].
Qed.

Lemma side_eqb_eq : forall p q, side_eqb p q = true -> p = q.
Proof.
  intros [[b1 k1] n1] [[b2 k2] n2] H. unfold side_eqb, saddr_eqb in H. cbn [fst snd a_base a_off] in H.
  destruct (Z.eqb_spec k1 k2) as [->|]; [|discriminate].
  destruct (expr_eqb b1 b2) eqn:E1; [|discriminate]. apply p_expr_eqb_eq in E1. apply p_expr_eqb_eq in H. subst. reflexivity.
Qed.
Lemma dl_eqb_eq : forall a b, dl_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn [dl_eqb] in H; try discriminate; [reflexivity|].
  destruct (side_eqb x y) eqn:E; [|discriminate]. apply side_eqb_eq in E. subst y. rewrite (IH b H). reflexivity.
Qed.
Definition CKEY (sx : stx) : positive * list (saddr * expr) * list (saddr * expr) := (sx_bid sx, sp_D (sx_sp sx), sp_Dx (sx_sp sx)).
Lemma ckey_eqb_eq : forall sx sy, ckey_eqb sx sy = true -> CKEY sx = CKEY sy.
Proof.
  intros sx sy H. unfold ckey_eqb in H. destruct (Pos.eqb_spec (sx_bid sx) (sx_bid sy)) as [E|]; [|discriminate].
  destruct (dl_eqb (sp_D (sx_sp sx)) (sp_D (sx_sp sy))) eqn:E1; [|discriminate].
  apply dl_eqb_eq in E1. apply dl_eqb_eq in H. unfold CKEY. rewrite E, E1, H. reflexivity.
Qed.
Definition CLS_OK (sxs : list stx) : Prop :=
  forall s1 s2, In s1 sxs -> In s2 sxs -> sx_cls s1 = sx_cls s2 -> CKEY s1 = CKEY s2.
Definition TOK (tab : list stx) (next : positive) : Prop :=
  (forall r, In r tab -> (sx_cls r < next)%positive) /\ CLS_OK tab.
Lemma cls_find_in : forall tab sx c, cls_find tab sx = Some c -> exists r, In r tab /\ sx_cls r = c /\ CKEY r = CKEY sx.
Proof.
  induction tab as [|a tab IH]; intros sx c H; cbn [cls_find] in H; [discriminate|].
  destruct (ckey_eqb sx a) eqn:E.
  - injection H as <-. exists a. split; [left; reflexivity|]. split; [reflexivity|]. symmetry. apply ckey_eqb_eq. exact E.
  - destruct (IH _ _ H) as (r & Hin & Hc & Hk). exists r. split; [right; exact Hin|]. split; assumption.
Qed.
Lemma assign_cls_ok : forall sxs tab next, TOK tab next ->
  exists tab' next', TOK tab' next' /\ incl tab tab' /\
    forall sx, In sx (assign_cls sxs tab next) -> exists r, In r tab' /\ sx_cls r = sx_cls sx /\ CKEY r = CKEY sx.
Proof.
  induction sxs as [|sx rest IH]; intros tab next HT.
  - exists tab, next. split; [exact HT|]. split; [apply incl_refl|]. intros sx [].
  - cbn [assign_cls]. destruct (cls_find tab sx) as [c|] eqn:EF.
    + destruct (IH tab next HT) as (tab' & next' & HT' & Hinc & Hall).
      exists tab', next'. split; [exact HT'|]. split; [exact Hinc|].
      intros s0 [<-|Hin]; [|apply Hall; exact Hin].
      destruct (cls_find_in _ _ _ EF) as (r & Hr & Hc & Hk). exists r. split; [apply Hinc; exact Hr|]. split; [exact Hc | exact Hk].
    + cbv zeta. set (r0 := set_cls sx next).
      assert (HT1 : TOK (r0 :: tab) (Pos.succ next)).
      { destruct HT as [Hlt Hok]. split.
        - intros r [<-|Hin]; [unfold r0; cbn [set_cls sx_cls]; lia | specialize (Hlt r Hin); lia].
        - intros s1 s2 [<-|H1] [<-|H2] Hc; try reflexivity.
          + specialize (Hlt s2 H2). unfold r0 in Hc. cbn [set_cls sx_cls] in Hc. lia.
          + specialize (Hlt s1 H1). unfold r0 in Hc. cbn [set_cls sx_cls] in Hc. lia.
          + apply Hok; assumption. }
      destruct (IH (r0 :: tab) (Pos.succ next) HT1) as (tab' & next' & HT' & Hinc & Hall).
      exists tab', next'. split; [exact HT'|]. split; [intros x Hx; apply Hinc; right; exact Hx|].
      intros s0 [<-|Hin]; [|apply Hall; exact Hin].
      exists r0. split; [apply Hinc; left; reflexivity|]. split; reflexivity.
Qed.
Lemma assign_cls_CLS_OK : forall sxs, CLS_OK (assign_cls sxs [] xH).
Proof.
  intros sxs. destruct (assign_cls_ok sxs [] xH) as (tab' & next' & [_ Hok] & _ & Hall).
  { split; [intros r []|intros s1 s2 []]. }
  intros s1 s2 H1 H2 Hc. destruct (Hall s1 H1) as (r1 & R1 & C1 & K1). destruct (Hall s2 H2) as (r2 & R2 & C2 & K2).
  rewrite <- K1, <- K2. apply Hok; [exact R1 | exact R2 | congruence].
Qed.
Lemma assign_cls_strip : forall sxs tab next, map strip (assign_cls sxs tab next) = map strip sxs.
Proof.
  induction sxs as [|sx rest IH]; intros tab next; [reflexivity|]. cbn [assign_cls].
  destruct (cls_find tab sx); cbv zeta; cbn [map]; rewrite IH; reflexivity.
Qed.
Lemma assign_cls_SX_OK : forall bc t sxs tab next, Forall (SX_OK bc t) sxs -> Forall (SX_OK bc t) (assign_cls sxs tab next).
Proof.
  intros bc t sxs. induction sxs as [|sx rest IH]; intros tab next H; [constructor|].
  apply Forall_cons_iff in H as [H1 H2]. cbn [assign_cls].
  destruct (cls_find tab sx); cbv zeta; (constructor; [exact H1 | apply IH; exact H2]).
Qed.

Lemma rapc_split : forall bc sp b1 k1 n1 br2 b2 k2 n2,
  ranges_apart_pcB bc sp b1 k1 n1 br2 b2 k2 n2 =
  if rapc_num bc sp b1 k1 n1 br2 b2 k2 n2 then true
  else if rapc_side bc sp n1 b2 k2 n2 then true else rapc_lin bc b1 k1 n1 b2 k2 n2.
Proof. intros. unfold ranges_apart_pcB, rapc_num, rapc_side, rapc_lin. destruct n1, n2; reflexivity. Qed.
Lemma prune1pcK_R_eq : forall bc sp wa w wv K br2,
  prune1pcK bc sp wa w wv K false br2 =
  prune1pcK_R bc sp wa w wv K
    (match kspan K with
     | Some (kb, kk, len) => ranges_apart_pcB bc sp (a_base wa) (a_off wa) (elen w) br2 kb kk len
     | None => false
     end).
Proof.
  intros bc sp wa w wv K br2.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    unfold prune1pcK, prune1pcK_R; cbn [kspan]; try reflexivity;
    destruct (ranges_apart_pcB bc sp (a_base wa) (a_off wa) (elen w) br2 kb kk _); try reflexivity;
    destruct (kcutB bc _ (a_base wa) (a_off wa) (elen w) kb kk len); reflexivity.
Qed.
Definition MOK (bc : bctx) (K : kentry) (all : list stx) (memo : smemo) : Prop :=
  forall c sd, In (c, sd) memo -> forall sx, In sx all -> sx_cls sx = c ->
    match kspan K with
    | Some (kb, kk, len) => rapc_side bc (sx_sp sx) (elen (sx_w sx)) kb kk len = sd
    | None => True
    end.
Lemma rapc_side_key : forall bc s1 s2 b2 k2 n2, CKEY s1 = CKEY s2 ->
  rapc_side bc (sx_sp s1) (elen (sx_w s1)) b2 k2 n2 = rapc_side bc (sx_sp s2) (elen (sx_w s2)) b2 k2 n2.
Proof.
  intros bc s1 s2 b2 k2 n2 H. unfold CKEY in H. injection H as H1 H2 H3. unfold rapc_side, elen. rewrite H2, H3. reflexivity.
Qed.
Lemma smemo_find_in : forall (m : smemo) c v, smemo_find m c = Some v -> In (c, v) m.
Proof.
  induction m as [|[c' v'] t IH]; intros c v H; cbn [smemo_find] in H; [discriminate|].
  destruct (Pos.eqb_spec c' c) as [->|NE]; [injection H as <-; left; reflexivity | right; apply IH; exact H].
Qed.
Lemma step_r_ok : forall bc all sx br2 K memo, CLS_OK all -> In sx all -> MOK bc K all memo ->
  fst (step_r bc sx br2 K memo) =
    (match kspan K with
     | Some (kb, kk, len) => ranges_apart_pcB bc (sx_sp sx) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx)) br2 kb kk len
     | None => false
     end)
  /\ MOK bc K all (snd (step_r bc sx br2 K memo)).
Proof.
  intros bc all sx br2 K memo HC Hin HM. unfold step_r.
  destruct (kspan K) as [[[kb kk] len]|] eqn:EK; [|split; [reflexivity|exact HM]].
  rewrite rapc_split. cbv zeta.
  destruct (rapc_num bc (sx_sp sx) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx)) br2 kb kk len); [split; [reflexivity|exact HM]|].
  destruct (smemo_find memo (sx_cls sx)) as [sd|] eqn:EF.
  - cbn [fst snd]. split; [|exact HM]. apply smemo_find_in in EF. pose proof (HM _ _ EF sx Hin eq_refl) as X. rewrite EK in X.
    rewrite X. reflexivity.
  - cbn [fst snd]. split; [reflexivity|]. intros c sd [E|Hm] s0 H0 Hc.
    + injection E as <- <-. rewrite EK. apply rapc_side_key. apply HC; [exact H0 | exact Hin | exact Hc].
    + exact (HM c sd Hm s0 H0 Hc).
Qed.
Lemma prune1pcKM_ok : forall bc all sx K same br2 memo, CLS_OK all -> In sx all -> MOK bc K all memo ->
  fst (prune1pcKM bc sx K same br2 memo) = prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K same br2
  /\ MOK bc K all (snd (prune1pcKM bc sx K same br2 memo)).
Proof.
  intros bc all sx K same br2 memo HC Hin HM. unfold prune1pcKM. destruct same; [split; [reflexivity|exact HM]|].
  destruct (step_r_ok bc all sx br2 K memo HC Hin HM) as [E M]. destruct (step_r bc sx br2 K memo) as [r memo'].
  cbn [fst snd] in *. split; [|exact M]. rewrite prune1pcK_R_eq. rewrite E. reflexivity.
Qed.
Lemma chainK2M_eq : forall bc all, CLS_OK all -> forall sxs, incl sxs all -> forall K okb same_of br2 memo,
  MOK bc K all memo -> chainK2M bc sxs K okb same_of br2 memo = chainK2 bc sxs K okb same_of br2.
Proof.
  intros bc all HC sxs. induction sxs as [|sx rest IH]; intros Hinc K okb same_of br2 memo HM; [reflexivity|].
  cbn [chainK2M chainK2].
  assert (Hin : In sx all) by (apply Hinc; left; reflexivity).
  assert (Hinc' : incl rest all) by (intros x Hx; apply Hinc; right; exact Hx).
  destruct (prune1pcKM_ok bc all sx K (same_of (sx_bid sx)) br2 memo HC Hin HM) as [E M].
  destruct (prune1pcKM bc sx K (same_of (sx_bid sx)) br2 memo) as [pr memo']. cbn [fst snd] in E, M. rewrite <- E.
  destruct pr as [|l]; [apply IH; assumption|].
  destruct okb as [kb|]; [|reflexivity].
  apply flat_map_ext. intros K'. destruct (kbase K') as [kb'|]; [|reflexivity]. destruct (expr_eqb kb' kb); [|reflexivity].
  apply IH; [exact Hinc'|]. intros c sd [].
Qed.
Lemma chainKFM_eq : forall bc all, CLS_OK all -> forall fl, (forall sx rest, In (sx, rest) fl -> In sx all /\ incl rest all) ->
  forall K okb same_of br2 memo, MOK bc K all memo -> chainKFM bc fl K okb same_of br2 memo = chainKF bc fl K okb same_of br2.
Proof.
  intros bc all HC fl. induction fl as [|[sx rest] fl' IH]; intros Hfl K okb same_of br2 memo HM; [reflexivity|].
  cbn [chainKFM chainKF].
  destruct (Hfl sx rest (or_introl eq_refl)) as [Hin Hinc'].
  destruct (prune1pcKM_ok bc all sx K (same_of (sx_bid sx)) br2 memo HC Hin HM) as [E M].
  destruct (prune1pcKM bc sx K (same_of (sx_bid sx)) br2 memo) as [pr memo']. cbn [fst snd] in E, M. rewrite <- E.
  destruct pr as [|l]; [apply IH; [intros; apply Hfl; right; assumption | exact M]|].
  destruct okb as [kb|]; [|reflexivity].
  apply flat_map_ext. intros K'. destruct (kbase K') as [kb'|]; [|reflexivity]. destruct (expr_eqb kb' kb); [|reflexivity].
  apply (chainK2M_eq bc all HC rest Hinc'). intros c sd [].
Qed.
Lemma mk_fl_incl : forall bc g sxs sx rest, In (sx, rest) (mk_fl bc g sxs) -> In sx sxs /\ incl rest sxs.
Proof.
  intros bc g sxs. induction sxs as [|a sxs IH]; intros sx rest H; cbn [mk_fl] in H; [contradiction|].
  destruct (verdict2 bc a g).
  - destruct (IH _ _ H) as [A B]. split; [right; exact A | intros x Hx; right; apply B; exact Hx].
  - destruct H as [E|H].
    + injection E as <- <-. split; [left; reflexivity | intros x Hx; right; exact Hx].
    + destruct (IH _ _ H) as [A B]. split; [right; exact A | intros x Hx; right; apply B; exact Hx].
Qed.
Lemma verdict_s_key : forall bc s1 s2 g, CKEY s1 = CKEY s2 -> verdict_s bc s1 g = verdict_s bc s2 g.
Proof.
  intros bc s1 s2 [[[b gb] obr] [glo ghi]] H. unfold CKEY in H. injection H as H1 H2 H3. unfold verdict_s. rewrite H1, H2. reflexivity.
Qed.
Lemma mk_flM_eq : forall bc g all, CLS_OK all -> forall sxs, incl sxs all -> forall memo : smemo,
  (forall c v, In (c, v) memo -> forall sx, In sx all -> sx_cls sx = c -> verdict_s bc sx g = v) ->
  mk_flM bc g sxs memo = mk_fl bc g sxs.
Proof.
  intros bc g all HC sxs. induction sxs as [|sx rest IH]; intros Hinc memo HM; [reflexivity|].
  assert (Hin : In sx all) by (apply Hinc; left; reflexivity).
  assert (Hinc' : incl rest all) by (intros x Hx; apply Hinc; right; exact Hx).
  cbn [mk_flM mk_fl]. unfold verdict2. destruct (verdict sx g); [apply IH; assumption|].
  destruct (smemo_find memo (sx_cls sx)) as [v|] eqn:EF.
  - apply smemo_find_in in EF. rewrite (HM _ _ EF sx Hin eq_refl). rewrite (IH Hinc' memo HM). reflexivity.
  - cbv zeta.
    assert (HM' : forall c v, In (c, v) ((sx_cls sx, verdict_s bc sx g) :: memo) -> forall s0, In s0 all -> sx_cls s0 = c -> verdict_s bc s0 g = v).
    { intros c v [E|Hm] s0 H0 Hc; [|exact (HM c v Hm s0 H0 Hc)]. injection E as <- <-. apply verdict_s_key. apply HC; assumption. }
    rewrite (IH Hinc' _ HM'). reflexivity.
Qed.
Lemma pt_map_ext : forall (A B : Type) (f h : A -> B) (t : ptree A), (forall a, f a = h a) -> pt_map f t = pt_map h t.
Proof.
  intros A B f h t H. induction t as [|l IHl o r IHr]; [reflexivity|]. cbn [pt_map]. rewrite IHl, IHr.
  destruct o as [a|]; [rewrite H|]; reflexivity.
Qed.
Lemma mk_glM_eq : forall bc bnds sxs, CLS_OK sxs -> mk_glM bc bnds sxs = mk_gl bc bnds sxs.
Proof.
  intros bc bnds sxs HC. unfold mk_glM, mk_gl. apply pt_map_ext. intros g.
  rewrite (mk_flM_eq bc g sxs HC sxs (incl_refl _) []) by (intros c v []). reflexivity.
Qed.
Lemma stores_partM_eq : forall bc all, CLS_OK all -> forall sxs, incl sxs all -> stores_partM bc sxs = stores_part bc sxs.
Proof.
  intros bc all HC sxs. induction sxs as [|sx newer IH]; intros Hinc; [reflexivity|].
  assert (Hinc' : incl newer all) by (intros x Hx; apply Hinc; right; exact Hx).
  cbn [stores_partM stores_part]. rewrite (IH Hinc'). f_equal.
  apply (chainK2M_eq bc all HC newer Hinc'). intros c sd [].
Qed.
Lemma chainK2_fact : forall bc sxs K okb same_of br2, kdescr K = None -> chainK2 bc sxs K okb same_of br2 = [K].
Proof.
  intros bc sxs K okb same_of br2 HK. induction sxs as [|sx rest IH]; [reflexivity|]. cbn [chainK2].
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    cbn [kdescr] in HK; try discriminate; cbn [prune1pcK]; exact IH.
Qed.
Lemma entriesGM_eq : forall bc t sxs bnds kn infos, CLS_OK sxs -> Forall2 (EINF bc t) kn infos ->
  entriesGM bc sxs (mk_gl bc bnds sxs) kn infos = entriesG bc sxs (mk_gl bc bnds sxs) kn infos.
Proof.
  intros bc t sxs bnds kn infos HC HF. induction HF as [|K oi rest irest HK HF IH]; [reflexivity|].
  cbn [entriesGM entriesG]. rewrite IH. f_equal.
  destruct oi as [ei|]; [|cbn [EINF] in HK; symmetry; apply chainK2_fact; exact HK].
  cbv zeta. unfold mk_gl. rewrite pt_get_map.
  destruct (pt_get bnds (ei_gid ei)) as [g|]; [|apply (chainK2M_eq bc sxs HC sxs (incl_refl _)); intros c sd []].
  destruct (inb g ei); [|apply (chainK2M_eq bc sxs HC sxs (incl_refl _)); intros c sd []].
  apply (chainKFM_eq bc sxs HC); [intros sx r Hin; exact (mk_fl_incl _ _ _ _ _ Hin) | intros c sd []].
Qed.
Lemma carryG_eq : forall log kn,
  carryG (mkbc (facts_of kn)) log kn = SPRo (facts_of kn) (rev log) ++ chainRo (facts_of kn) (rev log) kn.
Proof.
  intros log kn. unfold carryG.
  destruct (mk_stxs (mkbc (facts_of kn)) log nt_empty) as [sxs0 t0] eqn:E.
  destruct (mk_stxs_ok _ _ _ _ _ (NTI_empty _) E) as (HT0 & HS00 & Hmap0 & _).
  cbv zeta. set (sxs := assign_cls sxs0 [] xH).
  assert (HC : CLS_OK sxs) by apply assign_cls_CLS_OK.
  assert (HS0 : Forall (SX_OK (mkbc (facts_of kn)) t0) sxs) by (apply assign_cls_SX_OK; exact HS00).
  assert (Hmap : map strip sxs = rev log) by (unfold sxs; rewrite assign_cls_strip; exact Hmap0).
  destruct (scan_entries (mkbc (facts_of kn)) kn t0 gst_empty) as [[infos t1] gs] eqn:ES.
  destruct (scan_entries_ok _ _ _ _ _ _ _ HT0 ES) as (HT1 & Hm & HF).
  assert (HS1 : Forall (SX_OK (mkbc (facts_of kn)) t1) sxs).
  { apply Forall_impl with (P := SX_OK (mkbc (facts_of kn)) t0); [|exact HS0]. intros sx. apply SX_OK_mono. exact Hm. }
  rewrite (mk_glM_eq _ _ _ HC), (stores_partM_eq _ sxs HC sxs (incl_refl _)), (entriesGM_eq _ _ _ _ _ _ HC HF).
  rewrite (stores_part_eq _ _ _ HT0 HS0), (entriesG_eq _ _ _ _ _ _ HT1 HS1 HF), Hmap. reflexivity.
Qed.

Definition carryK (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryG bc log kn, [], [])
  | _, _ => carryB bc log kn hints
  end.
Lemma carryK_eq : forall log kn hints,
  carryK (mkbc (facts_of kn)) log kn hints = carry log kn hints.
Proof.
  intros log kn hints. unfold carryK. destruct log as [|s older]; [reflexivity|].
  destruct hints as [|h hs]; [|apply carryB_eq].
  rewrite carry_vertical, carryG_eq. reflexivity.
Qed.

End AX2B.
