(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsWalk.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N8Store.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma ck1_bnez_false : forall v, v = 0 -> negb (bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0)) = false.
Proof. intros v ->. reflexivity. Qed.

Lemma ck1_bnez_true : forall v, 0 <= v < 8 -> v <> 0 -> negb (bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0)) = true.
Proof. intros v Hv Nv. rewrite bv_eqb_Z, !unsigned_lit by lia. destruct (Z.eqb_spec v 0); [lia| reflexivity]. Qed.

Lemma ck1_land7_of_word : forall a, 0 <= a -> Z.land (bv_unsigned (Z_to_bv 64 a)) 7 = a mod 8.
Proof.
  intros a Ha. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  rewrite land7_mod8 by (apply Z.mod_pos_bound; unfold bv_modulus; cbn; lia).
  unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^61 * 8). Z.div_mod_to_equations. nia.
Qed.

Lemma ck1_bge_false : forall a v, 0 <= a -> 0 <= v < 8 -> a mod 8 + 1 <= v ->
  negb (bv_lts (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 a)) 7)) (Z_to_bv 64 v)) = false.
Proof.
  intros a v Ha Hv Hav. rewrite ck1_land7_of_word by exact Ha.
  unfold bv_lts. rewrite !Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64 / 2) with (2^63). change (2 ^ Z.of_N 64) with (2^64).
  rewrite (Z.mod_small (a mod 8 + 2^63)) by (Z.div_mod_to_equations; lia). rewrite (Z.mod_small (v + 2^63)) by lia.
  destruct (Z.ltb_spec (a mod 8 + 2 ^ 63 - 2 ^ 63) (v + 2 ^ 63 - 2 ^ 63)); [reflexivity| exfalso; Z.div_mod_to_equations; lia].
Qed.

Lemma ck1_blt_true : forall a v, 0 <= a -> 0 <= v < 8 -> a mod 8 + 1 <= v ->
  bv_lts (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 a)) 7)) (Z_to_bv 64 v) = true.
Proof. intros a v Ha Hv Hav. pose proof (ck1_bge_false a v Ha Hv Hav) as E. destruct (bv_lts _ _); [reflexivity| discriminate E]. Qed.

End HCW.

(* [comment removed for export] *)
Ltac ck1_load ACC a v V1 V2 Ha :=
  let ACW := fresh "ACW" in let RD := fresh "RD" in let SXV := fresh "SXV" in
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (ACW : accessible mc a 1) by (eapply accessible_sub; [exact ACC| lia| lia| lia]) end;
  assert (Ha : 0 <= a) by lia;
  destruct (accessible_read1 _ _ ACW) as (v & V1 & V2 & RD);
  rewrite <- (sh_shiftr a), ASHADOW_BASE_val in RD by exact Ha;
  replace (wa (Z.shiftr a 3 + 2147450880)) with (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) in RD by (symmetry; apply wa_of_Z_to_bv; lia);
  step; clear RD ACW;
  assert (SXV : sxb (b8 v) = Z_to_bv 64 v) by (unfold sxb; rewrite b8_signed_small by lia; reflexivity); rewrite SXV; clear SXV.

(* [comment removed for export] *)
Ltac ck1_branch_bge a v V1 V2 Ha K :=
  let Ev := fresh "Ev" in let Nv := fresh "Nv" in let VV := fresh "VV" in
  step; destruct (Z.eq_dec v 0) as [Ev|Nv];
  [ if_false_by (ck1_bnez_false v Ev); apply K
  | if_true_by (ck1_bnez_true v V1 Nv); destruct V2 as [VV|VV]; [exfalso; exact (Nv VV)|];
    step; step; if_false_by (ck1_bge_false a v Ha V1 VV); step; apply K ].

(* [comment removed for export] *)
Ltac ck1_branch_blt a v V1 V2 Ha K :=
  let Ev := fresh "Ev" in let Nv := fresh "Nv" in let VV := fresh "VV" in
  step; destruct (Z.eq_dec v 0) as [Ev|Nv];
  [ if_false_by (ck1_bnez_false v Ev); apply K
  | if_true_by (ck1_bnez_true v V1 Nv); destruct V2 as [VV|VV]; [exfalso; exact (Nv VV)|];
    step; step; if_true_by (ck1_blt_true a v Ha V1 VV); apply K ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HCW8.
  Context {HCEIL : HeapCeil}.

Lemma accessible_read8 : forall m a, accessible m a 8 -> ov_read_bytes asegs m (wa (sh a)) 1 = Some [b8 0].
Proof.
  intros m a ACC. pose proof ACC as (A0 & _ & AC).
  set (x := a + (7 - a mod 8)).
  assert (Hx : a <= x < a + 8) by (subst x; Z.div_mod_to_equations; lia).
  assert (SX : sh x = sh a) by (subst x; unfold sh; Z.div_mod_to_equations; nia).
  assert (ACW : accessible m x 1) by (eapply accessible_sub; [exact ACC| lia| lia| lia]).
  destruct (accessible_read1 _ _ ACW) as (v & V1 & V2 & RD).
  assert (X7 : x mod 8 = 7) by (subst x; Z.div_mod_to_equations; lia).
  assert (v = 0) by lia. subst v. rewrite <- SX. exact RD.
Qed.

Lemma ck8_zxb0 : zxb (b8 0) = Z_to_bv 64 0.
Proof. reflexivity. Qed.
Lemma ck8_sxb0 : sxb (b8 0) = Z_to_bv 64 0.
Proof. reflexivity. Qed.

End HCW8.

(* [comment removed for export] *)
Ltac ck8_load ACC a :=
  let ACW := fresh "ACW" in let RD := fresh "RD" in let Ha := fresh "Ha" in
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (ACW : accessible mc a 8) by (eapply accessible_sub; [exact ACC| lia| lia| lia]) end;
  assert (Ha : 0 <= a) by lia;
  pose proof (accessible_read8 _ _ ACW) as RD;
  rewrite <- (sh_shiftr a), ASHADOW_BASE_val in RD by exact Ha;
  replace (wa (Z.shiftr a 3 + 2147450880)) with (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) in RD by (symmetry; apply wa_of_Z_to_bv; lia);
  step; clear RD ACW Ha; rewrite ?ck8_zxb0, ?ck8_sxb0.

(* [comment removed for export] *)
Ltac ck8_check ACC a := ck8_load ACC a; step; if_false_by (ck1_bnez_false 0 eq_refl).

(* [comment removed for export] *)
Ltac ck8_load_lit ACC a :=
  let ACW := fresh "ACW" in let RD := fresh "RD" in
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (ACW : accessible mc a 8) by (eapply accessible_sub; [exact ACC| lia| lia| lia]) end;
  pose proof (accessible_read8 _ _ ACW) as RD;
  let v := eval vm_compute in (sh a) in
  change (sh a) with v in RD;
  replace (wa v) with (Z_to_bv 64 v) in RD by (symmetry; apply wa_of_Z_to_bv; lia);
  step; clear RD ACW; rewrite ?ck8_zxb0, ?ck8_sxb0.
Ltac ck8_check_lit ACC a := ck8_load_lit ACC a; step; if_false_by (ck1_bnez_false 0 eq_refl).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CKK.
  Context {HCEIL : HeapCeil}.

  Lemma accessible_readk : forall m a k, accessible m a k -> 1 <= k -> a mod 8 + k <= 8 ->
    exists v, 0 <= v < 8 /\ (v = 0 \/ a mod 8 + k <= v) /\ ov_read_bytes asegs m (wa (sh a)) 1 = Some [b8 v].
  Proof.
    intros m a k ACC Hk Hg. pose proof ACC as (A0 & A1 & AC).
    destruct (accessible_read1 m (a + k - 1) ltac:(eapply accessible_sub; [exact ACC| lia| lia| lia])) as (v & V0 & OK & RD).
    assert (SX : sh (a + k - 1) = sh a) by (unfold sh; Z.div_mod_to_equations; nia).
    rewrite SX in RD. exists v. split; [exact V0|]. split; [| exact RD].
    destruct OK as [K|K]; [left; exact K| right]. Z.div_mod_to_equations. nia.
  Qed.

  Lemma ckk_bge_false : forall a v i, 0 <= a -> 0 <= v < 8 -> 0 <= i < 8 -> a mod 8 + i + 1 <= v ->
    negb (bv_lts (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 a)) 7 + i)) (Z_to_bv 64 v)) = false.
  Proof.
    intros a v i Ha Hv Hi Hav. rewrite ck1_land7_of_word by exact Ha.
    unfold bv_lts. rewrite !Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 64 / 2) with (2^63). change (2 ^ Z.of_N 64) with (2^64).
    rewrite (Z.mod_small (a mod 8 + i + 2^63)) by (Z.div_mod_to_equations; lia). rewrite (Z.mod_small (v + 2^63)) by lia.
    destruct (Z.ltb_spec (a mod 8 + i + 2 ^ 63 - 2 ^ 63) (v + 2 ^ 63 - 2 ^ 63)); [reflexivity| exfalso; Z.div_mod_to_equations; lia].
  Qed.
  Lemma ckk_blt_true : forall a v i, 0 <= a -> 0 <= v < 8 -> 0 <= i < 8 -> a mod 8 + i + 1 <= v ->
    bv_lts (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 a)) 7 + i)) (Z_to_bv 64 v) = true.
  Proof. intros a v i Ha Hv Hi Hav. pose proof (ckk_bge_false a v i Ha Hv Hi Hav) as E. destruct (bv_lts _ _); [reflexivity| discriminate E]. Qed.
  (* [comment removed for export] *)
  Lemma ckk_bge_false' : forall a v i, 0 <= a < 2^64 -> 0 <= v < 8 -> 0 <= i < 8 -> a mod 8 + i + 1 <= v ->
    negb (bv_lts (Z_to_bv 64 (Z.land a 7 + i)) (Z_to_bv 64 v)) = false.
  Proof. intros a v i Ha Hv Hi Hav. rewrite <- (unsigned_lit a) at 1 by lia. apply ckk_bge_false; lia. Qed.
  Lemma ckk_blt_true' : forall a v i, 0 <= a < 2^64 -> 0 <= v < 8 -> 0 <= i < 8 -> a mod 8 + i + 1 <= v ->
    bv_lts (Z_to_bv 64 (Z.land a 7 + i)) (Z_to_bv 64 v) = true.
  Proof. intros a v i Ha Hv Hi Hav. rewrite <- (unsigned_lit a) at 1 by lia. apply ckk_blt_true; lia. Qed.

  (* [comment removed for export] *)
  Lemma accessible_read2 : forall m a, accessible m a 2 -> a mod 8 + 2 <= 8 ->
    exists v, 0 <= v < 8 /\ (v = 0 \/ a mod 8 + 2 <= v) /\ ov_read_bytes asegs m (wa (sh a)) 1 = Some [b8 v].
  Proof. intros m a ACC Hg. apply (accessible_readk m a 2 ACC ltac:(lia) Hg). Qed.
  Lemma ck2_bge_false : forall a v, 0 <= a -> 0 <= v < 8 -> a mod 8 + 2 <= v ->
    negb (bv_lts (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 a)) 7 + 1)) (Z_to_bv 64 v)) = false.
  Proof. intros. apply ckk_bge_false; lia. Qed.
  Lemma ck2_blt_true : forall a v, 0 <= a -> 0 <= v < 8 -> a mod 8 + 2 <= v ->
    bv_lts (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 a)) 7 + 1)) (Z_to_bv 64 v) = true.
  Proof. intros. apply ckk_blt_true; lia. Qed.
  Lemma ck2_bge_false' : forall a v, 0 <= a < 2^64 -> 0 <= v < 8 -> a mod 8 + 2 <= v ->
    negb (bv_lts (Z_to_bv 64 (Z.land a 7 + 1)) (Z_to_bv 64 v)) = false.
  Proof. intros. apply ckk_bge_false'; lia. Qed.
  Lemma ck2_blt_true' : forall a v, 0 <= a < 2^64 -> 0 <= v < 8 -> a mod 8 + 2 <= v ->
    bv_lts (Z_to_bv 64 (Z.land a 7 + 1)) (Z_to_bv 64 v) = true.
  Proof. intros. apply ckk_blt_true'; lia. Qed.
End CKK.

(* [comment removed for export] *)
Ltac ckk_load ACC a k v V1 V2 Ha :=
  let ACW := fresh "ACW" in let RD := fresh "RD" in let SXV := fresh "SXV" in
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (ACW : accessible mc a k) by (eapply accessible_sub; [exact ACC| lia| lia| lia]) end;
  assert (Ha : 0 <= a) by lia;
  destruct (accessible_readk _ _ _ ACW ltac:(lia) ltac:(first [lia | Z.div_mod_to_equations; lia])) as (v & V1 & V2 & RD);
  rewrite <- (sh_shiftr a), ASHADOW_BASE_val in RD by exact Ha;
  replace (wa (Z.shiftr a 3 + 2147450880)) with (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) in RD by (symmetry; apply wa_of_Z_to_bv; lia);
  step; clear RD ACW;
  assert (SXV : sxb (b8 v) = Z_to_bv 64 v) by (unfold sxb; rewrite b8_signed_small by lia; reflexivity); rewrite ?SXV, ?ck8_zxb0; clear SXV.
(* [comment removed for export] *)
Ltac ckk_branch_bge a k v V1 V2 Ha K :=
  let Ev := fresh "Ev" in let Nv := fresh "Nv" in let VV := fresh "VV" in
  step; destruct (Z.eq_dec v 0) as [Ev|Nv];
  [ if_false_by (ck1_bnez_false v Ev); apply K
  | if_true_by (ck1_bnez_true v V1 Nv); destruct V2 as [VV|VV]; [exfalso; exact (Nv VV)|];
    step; zstep; step;
    first [if_false_by (ckk_bge_false a v (k - 1) Ha V1 ltac:(lia) ltac:(lia))| if_false_by (ckk_bge_false' a v (k - 1) ltac:(lia) V1 ltac:(lia) ltac:(lia))];
    step; apply K ].
(* [comment removed for export] *)
Ltac ckk_branch_blt a k v V1 V2 Ha K :=
  let Ev := fresh "Ev" in let Nv := fresh "Nv" in let VV := fresh "VV" in
  step; destruct (Z.eq_dec v 0) as [Ev|Nv];
  [ if_false_by (ck1_bnez_false v Ev); apply K
  | if_true_by (ck1_bnez_true v V1 Nv); destruct V2 as [VV|VV]; [exfalso; exact (Nv VV)|];
    step; zstep; step;
    first [if_true_by (ckk_blt_true a v (k - 1) Ha V1 ltac:(lia) ltac:(lia))| if_true_by (ckk_blt_true' a v (k - 1) ltac:(lia) V1 ltac:(lia) ltac:(lia))];
    apply K ].
Ltac ck2_load ACC a v V1 V2 Ha := ckk_load ACC a 2 v V1 V2 Ha.
Ltac ck2_branch_bge a v V1 V2 Ha K := ckk_branch_bge a 2 v V1 V2 Ha K.
Ltac ck2_branch_blt a v V1 V2 Ha K := ckk_branch_blt a 2 v V1 V2 Ha K.
Ltac ck4_load ACC a v V1 V2 Ha := ckk_load ACC a 4 v V1 V2 Ha.
Ltac ck4_branch_bge a v V1 V2 Ha K := ckk_branch_bge a 4 v V1 V2 Ha K.
Ltac ck4_branch_blt a v V1 V2 Ha K := ckk_branch_blt a 4 v V1 V2 Ha K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma al8 : forall x, x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x H. rewrite land_7. exact H. Qed.
Lemma al8u : forall x, x mod 8 = 0 -> 0 <= x < 2^64 -> Z.land (bv_unsigned (Z_to_bv 64 x)) 7 = 0.
Proof. intros x H R. rewrite unsigned_lit by lia. apply al8, H. Qed.

(* [comment removed for export] *)
Lemma land_3 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma al4 : forall x, x mod 4 = 0 -> Z.land x 3 = 0.
Proof. intros x H. rewrite land_3. exact H. Qed.
Lemma al4u : forall x, x mod 4 = 0 -> 0 <= x < 2^64 -> Z.land (bv_unsigned (Z_to_bv 64 x)) 3 = 0.
Proof. intros x H R. rewrite unsigned_lit by lia. apply al4, H. Qed.

(* [comment removed for export] *)
Ltac ubal_by H :=
  match goal with
  | |- context [Z.land (bv_unsigned (Z_to_bv 64 ?x)) 7] => rewrite (al8u x) by (first [exact H | revert H; clear; intros H; lia | lia])
  | |- context [Z.land ?x 7] => rewrite (al8 x) by (first [exact H | revert H; clear; intros H; lia | lia])
  | |- context [Z.land (bv_unsigned (Z_to_bv 64 ?x)) 3] => rewrite (al4u x) by (first [exact H | revert H; clear; intros H; lia | lia])
  | |- context [Z.land ?x 3] => rewrite (al4 x) by (first [exact H | revert H; clear; intros H; lia | lia])
  end.
(* [comment removed for export] *)
Ltac if_lit :=
  match goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota
  end.
(* [comment removed for export] *)
Ltac ub_dead :=
  let KU := fresh "KU" in
  if_cases KU; zify_cond KU;
  [ exfalso; revert KU; rewrite ?unsigned_lit by lia; intros KU; lia
  | clear KU ].
Lemma askit_signed_lit : forall z, - 2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed. rewrite unsigned_lit_wrap.
  destruct (Z.ltb_spec (z mod 2^64) (2^63)) as [L|L].
  - destruct (Z.neg_nonneg_cases z) as [N|N]; [| rewrite Z.mod_small in * by lia; lia].
    rewrite <- (Z.mod_add _ 1) in L by lia. rewrite Z.mod_small in L by lia. lia.
  - destruct (Z.neg_nonneg_cases z) as [N|N]; [| rewrite Z.mod_small in * by lia; lia].
    rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Ltac askit_shl_norm :=
  repeat match goal with
  | |- context [Z.shiftl ?x 3] => rewrite (Z.shiftl_mul_pow2 x 3) by lia; change (2 ^ 3) with 8
  | |- context [Z.shiftl ?x 2] => rewrite (Z.shiftl_mul_pow2 x 2) by lia; change (2 ^ 2) with 4
  end.
Ltac has_var c := match c with context [?x] => is_var x end.
Ltac if_lit_strict := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      tryif has_var c then fail else
      let v := eval vm_compute in c in
      lazymatch v with true => idtac | false => idtac end;
      replace c with v by (vm_compute; reflexivity); cbv iota end.
Ltac ubal_any :=
  repeat match goal with
  | |- context [Z.land (bv_unsigned (Z_to_bv 64 ?x)) 7] => rewrite (al8u x) by (first [assumption | lia])
  | |- context [Z.land (bv_unsigned (Z_to_bv 64 ?x)) 3] => rewrite (al4u x) by (first [assumption | lia])
  | |- context [Z.land ?x 7] => rewrite (al8 x) by (first [assumption | lia])
  | |- context [Z.land ?x 3] => rewrite (al4 x) by (first [assumption | lia])
  end.
Ltac ub_A_any :=
  let KU := fresh "KU" in
  if_cases KU; zify_cond KU;
  [ clear KU
  | exfalso; revert KU; rewrite ?unsigned_lit, ?askit_signed_lit by lia; intros KU; lia ].
Ltac ub_al := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      lazymatch c with context [Z.land _ _] => progress ubal_any; if_lit_strict end end.
Ltac ub_norm := rewrite ?sx32_wz by lia; askit_shl_norm.
Ltac trap_at segs x :=
  let b := eval vm_compute in (match fetch_word segs (Z_to_bv 64 x) with Some w => Z.eqb (bv_unsigned w) 3221229683 | None => false end) in
  lazymatch b with true => idtac | false => fail end.
Ltac ub_res := lazymatch goal with
  | |- evt ?segs _ (MS _ _ (if _ then Z_to_bv 64 ?ta else Z_to_bv 64 ?fa) _ _ _ _) =>
      first [ if_lit_strict | ub_al
            | (trap_at segs ta; first [ ub_dead | (progress ub_norm; ub_dead) ])
            | (trap_at segs fa; first [ ub_A_any | (progress ub_norm; ub_A_any) ])
            | (progress ub_norm; if_lit_strict) ]
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      first [ if_lit_strict | ub_al | (progress ub_norm; if_lit_strict) ] end.
Ltac at_ctl := lazymatch goal with |- evt ?segs _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with Some ?w => let d := eval vm_compute in (decode_any w) in
    lazymatch d with
    | Some (Jalr _ _ _, _) => idtac
    | Some (Jal ?rd _, _) => let z := eval vm_compute in (bv_unsigned rd) in lazymatch z with 0%Z => fail | _ => idtac end
    | _ => fail end end end.
Ltac bst := first [ ub_res | (tryif at_ctl then fail else st1) ].
Ltac go_n n := lazymatch n with O => idtac "PK-FUEL" | S ?k => tryif (progress bst) then go_n k else idtac end.
Ltac go := go_n 80%nat.
Ltac at_pc P := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => let b := eval vm_compute in (Z.eqb pc P) in lazymatch b with true => idtac | false => fail end end.
Ltac go_to_n P n := lazymatch n with O => idtac "PK-FUEL" | S ?k => tryif at_pc P then idtac else (tryif (progress bst) then go_to_n P k else idtac) end.
Ltac go_to P := go_to_n P 200%nat.
Ltac pk := match goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => idtac "PK-IF"
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => tryif at_ctl then idtac "PK-CTL" pc else idtac "PK-PC" pc
  | |- _ => idtac "PK-OTHER" end.
Ltac pg := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PK-GOAL-PC" pc; idtac "PK-GOAL-R" R end.
Ltac bst_dbg := match goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => idtac "PK-TRY-IF" c
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "PK-TRY-PC" pc
  | |- _ => idtac "PK-TRY-OTHER" end; bst.
Ltac godbg_n n := lazymatch n with O => idtac "PK-FUEL" | S ?k => tryif (progress bst_dbg) then godbg_n k else idtac "PK-STOP" end.
Ltac godbg := godbg_n 80%nat.
