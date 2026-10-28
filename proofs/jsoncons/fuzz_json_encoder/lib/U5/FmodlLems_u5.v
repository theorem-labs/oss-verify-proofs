(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import DecLemTac.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import CutCert CutOps CutOpsD CutHeap CutAutoD CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FCutCert Require Import Pm6CutKitD_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FCutGen Require Import Cut_fmodl_xsrc_u5.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Module FML.
Definition U (E : env) (e : expr) : Z := bv_unsigned (edenot E e).
Definition sg (z : Z) : Z := if z <? 2 ^ 63 then z else z - 2 ^ 64.
Lemma U_range : forall E e, 0 <= U E e < 2 ^ 64. Proof. intros. apply DLT.u_range. Qed.
Lemma U_var : forall E n, U E (EVar n) = bv_unsigned (ev E n). Proof. reflexivity. Qed.
Lemma U_lit : forall E z, U E (ELit z) = z mod 2 ^ 64. Proof. intros. unfold U. cbn [edenot]. apply u_lit64. Qed.
Lemma U_sltu : forall E a b, U E (EAlu ALU_SLTU a b) = if U E a <? U E b then 1 else 0. Proof. intros. unfold U. cbn [edenot]. apply u_sltu64. Qed.
Lemma U_slt : forall E a b, U E (EAlu ALU_SLT a b) = if sg (U E a) <? sg (U E b) then 1 else 0.
Proof. intros. unfold U, sg. cbn [edenot]. rewrite u_slt64, !DLT.s_of_u. reflexivity. Qed.
Lemma U_or : forall E a b, U E (EAlu ALU_OR a b) = Z.lor (U E a) (U E b). Proof. intros. unfold U. cbn [edenot]. apply u_or64. Qed.
Lemma U_and : forall E a b, U E (EAlu ALU_AND a b) = Z.land (U E a) (U E b). Proof. intros. unfold U. cbn [edenot]. apply u_and64. Qed.
Lemma U_srl : forall E a b, U E (EAlu ALU_SRL a b) = U E a / 2 ^ (U E b mod 64). Proof. intros. unfold U. cbn [edenot]. apply u_srl64. Qed.
Lemma U_lin : forall E e, U E e = (lden E (lin_of e)) mod 2 ^ 64.
Proof.
  intros E e. pose proof (lin_of_sound E e) as [q Hq]. unfold AX2S.uE in Hq. pose proof (U_range E e) as Hu. unfold U in *.
  rewrite Hq. rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. exact Hu.
Qed.
(* [comment removed for export] *)
Ltac ustep E e :=
  lazymatch e with
  | EVar _ => rewrite (U_var E) in *
  | ELit _ => rewrite (U_lit E e) in * || (let z := match e with ELit ?z => z end in rewrite (U_lit E z) in * )
  | EAlu ALU_SLTU ?a ?b => rewrite (U_sltu E a b) in *
  | EAlu ALU_SLT ?a ?b => rewrite (U_slt E a b) in *
  | EAlu ALU_OR ?a ?b => rewrite (U_or E a b) in *
  | EAlu ALU_AND ?a ?b => rewrite (U_and E a b) in *
  | EAlu ALU_SRL ?a ?b => rewrite (U_srl E a b) in *
  | _ => rewrite (U_lin E e) in *; unfold lden in *;
         repeat (match goal with |- context [lin_of ?x] => let l := fresh "l" in set (l := lin_of x) in *; vm_compute in l; subst l
                            | H : context [lin_of ?x] |- _ => let l := fresh "l" in set (l := lin_of x) in *; vm_compute in l; subst l end);
         cbn [fst snd tden] in *; change (AX2S.uE E) with (U E) in *
  end.
Ltac usteps E := repeat match goal with
                        | |- context [U E ?e] => ustep E e
                        | H : context [U E ?e] |- _ => ustep E e
                        end.
Ltac start := let E := fresh "E" in let M := fresh "M" in let HP := fresh "HP" in
  unfold CXD.lemma_ok; intros E M HP; DLT.prem_split HP; clear HP; cbn [kentry_ok] in *;
  repeat match goal with |- context [bv_unsigned (edenot E ?e)] => change (bv_unsigned (edenot E e)) with (U E e)
                       | H : context [bv_unsigned (edenot E ?e)] |- _ => change (bv_unsigned (edenot E e)) with (U E e) in H end;
  usteps E; DLT.gen_u.

Lemma lor_pos_iff : forall a b, 0 <= a -> 0 <= b -> (0 < Z.lor a b <-> (0 < a \/ 0 < b)).
Proof.
  intros a b Ha Hb. pose proof (Z.lor_eq_0_iff a b) as H0. pose proof (proj2 (Z.lor_nonneg a b) (conj Ha Hb)) as Hn. split.
  - intros H. destruct (Z.eq_dec a 0) as [->|]; [|lia]. destruct (Z.eq_dec b 0) as [->|]; [|lia]. rewrite Z.lor_0_l in H. lia.
  - intros H. assert (Z.lor a b <> 0) by (intros X; apply H0 in X; lia). lia.
Qed.
Lemma land_ones48 : forall a, 0 <= a -> Z.land a 281474976710655 = a mod 2 ^ 48.
Proof. intros a Ha. change 281474976710655 with (Z.ones 48). apply Z.land_ones. lia. Qed.
Ltac nn := repeat first [lia | (apply Z.lor_nonneg; split) | (apply Z.mod_pos_bound; lia) | (apply Z.div_pos; [|apply Z.pow_pos_nonneg; lia]) | (apply Z.land_nonneg; left)].
(* [comment removed for export] *)
Ltac lits := cbv [sg] in *;
  repeat match goal with
         | |- context [Z.modulo (Zpos ?p) (2 ^ 64)] => let v := eval vm_compute in (Z.modulo (Zpos p) (2 ^ 64)) in change (Z.modulo (Zpos p) (2 ^ 64)) with v in *
         | H : context [Z.modulo (Zpos ?p) (2 ^ 64)] |- _ => let v := eval vm_compute in (Z.modulo (Zpos p) (2 ^ 64)) in change (Z.modulo (Zpos p) (2 ^ 64)) with v in *
         end;
  change (0 mod 2 ^ 64) with 0 in *;
  repeat match goal with
         | |- context [Z.modulo (Zpos ?p) 64] => let v := eval vm_compute in (Z.modulo (Zpos p) 64) in change (Z.modulo (Zpos p) 64) with v in *
         | H : context [Z.modulo (Zpos ?p) 64] |- _ => let v := eval vm_compute in (Z.modulo (Zpos p) 64) in change (Z.modulo (Zpos p) 64) with v in *
         end.
Lemma lor_range : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= Z.lor a b < 2 ^ 64.
Proof. intros a b Ha Hb. apply Z_lor_range; lia. Qed.
Lemma land_le_r : forall a b, 0 <= a -> 0 <= b -> Z.land a b <= b.
Proof.
  intros a b Ha Hb. assert (D : Z.land (Z.ldiff b a) (Z.land a b) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit b n), (Z.testbit a n); reflexivity. }
  assert (S : Z.lor (Z.ldiff b a) (Z.land a b) = b).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec, Z.ldiff_spec, Z.land_spec. destruct (Z.testbit b n), (Z.testbit a n); reflexivity. }
  pose proof (Z.add_nocarry_lxor _ _ D) as A1. pose proof (Z.lxor_lor _ _ D) as A2. rewrite A2, S in A1.
  assert (0 <= Z.ldiff b a) by (apply Z.ldiff_nonneg; left; exact Hb). lia.
Qed.
Lemma lor_bounds : forall a b, 0 <= a -> 0 <= b -> a <= Z.lor a b /\ b <= Z.lor a b /\ Z.lor a b <= a + b.
Proof.
  intros a b Ha Hb. pose proof (Z.add_lor_land a b) as S. pose proof (land_le_r a b Ha Hb). pose proof (land_le_r b a Hb Ha) as L2. rewrite Z.land_comm in L2.
  assert (0 <= Z.land a b) by (apply Z.land_nonneg; left; exact Ha). lia.
Qed.
Ltac rg := repeat first [lia | (apply lor_range) | (apply Z.mod_pos_bound; lia)
                         | (match goal with |- 0 <= ?a / ?b < _ => assert (0 < b) by (apply Z.pow_pos_nonneg; lia); assert (0 <= a < 2 ^ 64) by rg; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia] end)].
(* [comment removed for export] *)
Ltac lors := repeat match goal with
                    | |- context [Z.lor ?a ?b] => absl a b
                    | H : context [Z.lor ?a ?b] |- _ => absl a b
                    end
with absl a b := let z := fresh "z" in let Hz := fresh "Hz" in let Iz := fresh "Iz" in
  assert (Hz : 0 <= Z.lor a b < 2 ^ 64) by rg;
  assert (Iz : a <= Z.lor a b /\ b <= Z.lor a b /\ Z.lor a b <= a + b) by (apply lor_bounds; rg);
  set (z := Z.lor a b) in *; clearbody z.
Ltac lands := repeat match goal with
                     | |- context [Z.land ?a 281474976710655] => rewrite (land_ones48 a) in * by lia
                     | H : context [Z.land ?a 281474976710655] |- _ => rewrite (land_ones48 a) in * by lia
                     end.
Ltac lits2 := lits; change (0 mod 64) with 0 in *; change (2 ^ 0) with 1 in *; rewrite ?Z.div_1_r in *.
Ltac fin := lits2; lands; lors; DLT.ifs; Z.div_mod_to_equations; lia.
Ltac lem_in := let E := fresh "E" in let M := fresh "M" in let HP := fresh "HP" in
  unfold CXD.lemma_ok; intros E M HP; rewrite Forall_forall in HP; apply HP; cbn [In]; repeat first [left; reflexivity | right].
Ltac lem_any := let E := fresh "E" in let M := fresh "M" in let HP := fresh "HP" in
  unfold CXD.lemma_ok; intros E M HP; cbn [kentry_ok];
  match goal with |- 0 <= bv_unsigned ?t <= 18446744073709551615 => pose proof (DLT.u_range t); lia end.
(* [comment removed for export] *)
Ltac lem_shift := start; lits2;
  match goal with
  | P4 : 1 <= ?x / 2 ^ (((64 + (-1 * ?t + 0)) mod 2 ^ 64) mod 64) <= _, Pt : 1 <= ?t <= 64 |- _ =>
      destruct (Z.eq_dec t 1) as [Et|Et];
      [ subst t; change (((64 + (-1 * 1 + 0)) mod 2 ^ 64) mod 64) with 63 in P4; rewrite Z.div_small in P4 by lia; lia
      | rewrite (Z.mod_small (64 + (-1 * t + 0)) (2 ^ 64)) in P4 by lia; rewrite (Z.mod_small (64 + (-1 * t + 0)) 64) in P4 by lia;
        first [ solve [clear P4; Z.div_mod_to_equations; lia]
              | rewrite (Z.mod_small (65 + (-1 * t + 0)) (2 ^ 64)) by lia; rewrite (Z.mod_small (65 + (-1 * t + 0)) 64) by lia;
                rewrite (Z.mod_small (0 + (2 * x + 0)) (2 ^ 64)) by lia;
                replace (65 + (-1 * t + 0)) with (Z.succ (64 + (-1 * t + 0))) by lia; rewrite Z.pow_succ_r by lia;
                replace (0 + (2 * x + 0)) with (2 * x) by lia; rewrite Z.div_mul_cancel_l by (try lia; apply Z.pow_nonzero; lia); exact P4 ] ]
  end.
End FML.
Lemma lems_ok : LEMS_OK.
Proof.
  unfold LEMS_OK, CXD.LEMS_OK, LEMS.
  repeat (apply Forall_cons; [cbn [fst snd]; first [solve [FML.lem_in] | solve [FML.lem_any] | solve [FML.lem_shift] | solve [FML.start; FML.fin]] |]); apply Forall_nil.
Qed.
(* [comment removed for export] *)
Definition plans_ok := plans lems_ok.
Print Assumptions plans_ok.
