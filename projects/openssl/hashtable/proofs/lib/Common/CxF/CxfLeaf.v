(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CXLF.

Definition zshr (a s : Z) : Z := if Z.leb 0 s then Z.shiftr a s else a / 2 ^ s.
Lemma zshr_eq : zshr = fun a s => a / 2 ^ s.
Proof.
  apply functional_extensionality; intros a. apply functional_extensionality; intros s. unfold zshr.
  destruct (Z.leb_spec 0 s); [apply Z.shiftr_div_pow2; assumption | reflexivity].
Qed.

Definition zm64 (z : Z) : Z := AX2.zmod64 z.
Lemma zm64_eq : zm64 = fun z => z mod 2 ^ 64.
Proof. apply functional_extensionality; intros z. unfold zm64. apply AX2.zmod64_eq. Qed.

Definition zmodp (a j : Z) : Z := if Z.leb 0 j then Z.land a (Z.ones j) else a mod 2 ^ j.
Lemma zmodp_eq : zmodp = fun a j => a mod 2 ^ j.
Proof.
  apply functional_extensionality; intros a. apply functional_extensionality; intros j. unfold zmodp.
  destruct (Z.leb_spec 0 j); [apply Z.land_ones; assumption | reflexivity].
Qed.
Definition zpow2 (j : Z) : Z := if Z.leb 0 j then Z.shiftl 1 j else 2 ^ j.
Lemma zpow2_eq : zpow2 = fun j => 2 ^ j.
Proof.
  apply functional_extensionality; intros j. unfold zpow2.
  destruct (Z.leb_spec 0 j); [apply Z.shiftl_1_l | reflexivity].
Qed.

Definition zhalf (w : Z) : Z := Z.div2 w.
Lemma zhalf_eq : zhalf = fun w => w / 2.
Proof. apply functional_extensionality; intros w. unfold zhalf. apply Z.div2_div. Qed.

Definition p12 : Z := 2 ^ 12.  Definition p16 : Z := 2 ^ 16.  Definition p24 : Z := 2 ^ 24.  Definition p26 : Z := 2 ^ 26.
Definition p31 : Z := 2 ^ 31.  Definition p32 : Z := 2 ^ 32.  Definition p40 : Z := 2 ^ 40.  Definition p46 : Z := 2 ^ 46.
Definition p47 : Z := 2 ^ 47.  Definition p48 : Z := 2 ^ 48.  Definition p62 : Z := 2 ^ 62.  Definition p63 : Z := 2 ^ 63.
Definition p64 : Z := 2 ^ 64.

(* [comment removed for export] *)
Fixpoint ctzp (fuel : nat) (p : positive) : Z :=
  match fuel with
  | O => 0
  | S f => match p with xO q => Z.succ (ctzp f q) | _ => 0 end
  end.
Definition ctz_fuelF (fuel : nat) (z : Z) : Z :=
  match z with Z0 => Z.of_nat fuel | Zpos p => ctzp fuel p | Zneg p => ctzp fuel p end.
Lemma ctz_fuelF_eq : forall fuel z, ctz_fuelF fuel z = AX2.ctz_fuel fuel z.
Proof.
  induction fuel as [|f IH]; intros z; [destruct z; reflexivity|].
  cbn [AX2.ctz_fuel]. destruct z as [|p|p].
  - change (0 mod 2) with 0. change (0 / 2) with 0. cbn [Z.eqb]. rewrite <- IH. cbn [ctz_fuelF]. lia.
  - destruct p as [q|q|].
    + replace (Z.pos q~1 mod 2) with 1 by (rewrite Pos2Z.inj_xI; rewrite Z.add_comm, Z.mul_comm, Z.mod_add by lia; reflexivity). reflexivity.
    + replace (Z.pos q~0 mod 2) with 0 by (rewrite Pos2Z.inj_xO; rewrite Z.mul_comm, Z.mod_mul by lia; reflexivity).
      replace (Z.pos q~0 / 2) with (Z.pos q) by (rewrite Pos2Z.inj_xO; rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
      cbn [Z.eqb]. rewrite <- IH. cbn [ctz_fuelF ctzp]. lia.
    + reflexivity.
  - destruct p as [q|q|].
    + replace (Z.neg q~1 mod 2) with 1.
      2:{ change (Z.neg q~1) with (- Z.pos q~1). rewrite Pos2Z.inj_xI. replace (- (2 * Z.pos q + 1)) with (1 + (- Z.pos q - 1) * 2) by lia.
          rewrite Z.mod_add by lia. reflexivity. }
      reflexivity.
    + replace (Z.neg q~0 mod 2) with 0.
      2:{ change (Z.neg q~0) with (- Z.pos q~0). rewrite Pos2Z.inj_xO. replace (- (2 * Z.pos q)) with ((- Z.pos q) * 2) by lia. rewrite Z.mod_mul by lia. reflexivity. }
      replace (Z.neg q~0 / 2) with (Z.neg q).
      2:{ change (Z.neg q~0) with (- Z.pos q~0). rewrite Pos2Z.inj_xO. replace (- (2 * Z.pos q)) with ((- Z.pos q) * 2) by lia. rewrite Z.div_mul by lia. reflexivity. }
      cbn [Z.eqb]. rewrite <- IH. cbn [ctz_fuelF ctzp]. lia.
    + reflexivity.
Qed.
Lemma ctz_fuelF_eqf : ctz_fuelF = AX2.ctz_fuel.
Proof. apply functional_extensionality; intros f. apply functional_extensionality; intros z. apply ctz_fuelF_eq. Qed.

(* [comment removed for export] *)
Import ListNotations.
Fixpoint fact_quotF (fts ts : list (Z * AX2.expr)) (acc : option Z) : option Z :=
  match fts with
  | [] => acc
  | (k, a) :: r =>
      if Z.eqb k 0 then None else
      let K := AX2.coef_of a ts in
      if Z.eqb K 0 then None else
      let '(q, m) := Z.div_eucl K k in
      if negb (Z.eqb m 0) then None else
      match acc with
      | None => fact_quotF r ts (Some q)
      | Some q0 => if Z.eqb q0 q then fact_quotF r ts acc else None
      end
  end.
Lemma fact_quotF_eqf : fact_quotF = AX2.fact_quot.
Proof.
  apply functional_extensionality; intros fts. apply functional_extensionality; intros ts. apply functional_extensionality; intros acc.
  revert acc. induction fts as [|[k a] r IH]; intros acc; [reflexivity|]. cbn [fact_quotF AX2.fact_quot].
  destruct (Z.eqb k 0); [reflexivity|]. cbv zeta. destruct (Z.eqb (AX2.coef_of a ts) 0); [reflexivity|].
  unfold Z.modulo, Z.div. destruct (Z.div_eucl (AX2.coef_of a ts) k) as [q m]. cbn [fst snd].
  destruct (negb (Z.eqb m 0)); [reflexivity|]. destruct acc as [q0|]; [|apply IH]. destruct (Z.eqb q0 q); [apply IH|reflexivity].
Qed.

End CXLF.
