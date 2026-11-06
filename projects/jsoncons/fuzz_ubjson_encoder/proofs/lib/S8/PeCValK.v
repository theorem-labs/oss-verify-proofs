(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec AxSymExec3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import Utf8FactsS8.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECVK.
Import UTF8F.
Section K.
Context {fx : PropExec.FPState}. Context {bmK : BMode}.

Lemma by_table (test : Z -> bool) b : forallb (fun k => test (Z.of_nat k)) (seq 0 256) = true -> 0 <= b < 256 -> test b = true.
Proof.
  intros T Hb. rewrite forallb_forall in T. specialize (T (Z.to_nat b) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in T by lia. exact T.
Qed.

Definition v_ascii (b : Z) : Z := if b <? 128 then 0 else 1.
Definition v_cont (b : Z) : Z := if (128 <=? b) && (b <? 192) then 0 else 1.
Definition v_ltu (b k : Z) : Z := if b <? k then 1 else 0.
Definition v_gtu (k b : Z) : Z := if k <? b then 1 else 0.
Definition v_lead (b : Z) : Z := if (128 <=? b) && (b <? 194) then 1 else 0.

Definition c_ascii (w : word) : Z := bv_unsigned (alu64 Instr.ALU_SLT (ext_val true 0 1 w) (Z_to_bv 64 0)).
Definition c_cont (w : word) : Z := bv_unsigned (alu64 Instr.ALU_SLT (Z_to_bv 64 (-65)) (ext_val true 0 1 w)).
Definition c_ltu (w : word) (k : Z) : Z := bv_unsigned (alu64 Instr.ALU_SLTU (alu64 Instr.ALU_AND (ext_val true 0 1 w) (Z_to_bv 64 255)) (Z_to_bv 64 k)).
Definition c_gtu (k : Z) (w : word) : Z := bv_unsigned (alu64 Instr.ALU_SLTU (Z_to_bv 64 k) (alu64 Instr.ALU_AND (ext_val true 0 1 w) (Z_to_bv 64 255))).
Definition c_gt239 (w : word) : Z := bv_unsigned (alu64 Instr.ALU_SLT (Z_to_bv 64 239) w).
Definition c_lead (w : word) : Z :=
  bv_unsigned (alu64 Instr.ALU_SLT (alu64 Instr.ALU_SRA (mul_div Instr.M_MUL (Z_to_bv 64 72057594037927936) w) (Z_to_bv 64 56)) (Z_to_bv 64 (-62))).
Definition c_sx8 (w : word) : Z := bv_unsigned (ext_val true 0 1 w).

Lemma e_ascii E j : bv_unsigned (edenot E (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar j)) (ELit 0))) = c_ascii (ev E j). Proof. reflexivity. Qed.
Lemma e_cont E j : bv_unsigned (edenot E (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar j)))) = c_cont (ev E j). Proof. reflexivity. Qed.
Lemma e_ltu E j k : bv_unsigned (edenot E (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_AND (EExt true 0 1 (EVar j)) (ELit 255)) (ELit k))) = c_ltu (ev E j) k. Proof. reflexivity. Qed.
Lemma e_gtu E k j : bv_unsigned (edenot E (EAlu Instr.ALU_SLTU (ELit k) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar j)) (ELit 255)))) = c_gtu k (ev E j). Proof. reflexivity. Qed.
Lemma e_gt239 E j : bv_unsigned (edenot E (EAlu Instr.ALU_SLT (ELit 239) (EVar j))) = c_gt239 (ev E j). Proof. reflexivity. Qed.
Lemma e_lead E j : bv_unsigned (edenot E (EAlu Instr.ALU_SLT (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar j)) (ELit 56)) (ELit (-62)))) = c_lead (ev E j). Proof. reflexivity. Qed.
Lemma e_sx8 E j : bv_unsigned (edenot E (EExt true 0 1 (EVar j))) = c_sx8 (ev E j). Proof. reflexivity. Qed.

Lemma t_ascii : forallb (fun k => Z.eqb (c_ascii (Z_to_bv 64 (Z.of_nat k))) (v_ascii (Z.of_nat k))) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma t_cont : forallb (fun k => Z.eqb (c_cont (Z_to_bv 64 (Z.of_nat k))) (v_cont (Z.of_nat k))) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma t_ltu144 : forallb (fun k => Z.eqb (c_ltu (Z_to_bv 64 (Z.of_nat k)) 144) (v_ltu (Z.of_nat k) 144)) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma t_ltu160 : forallb (fun k => Z.eqb (c_ltu (Z_to_bv 64 (Z.of_nat k)) 160) (v_ltu (Z.of_nat k) 160)) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma t_gtu143 : forallb (fun k => Z.eqb (c_gtu 143 (Z_to_bv 64 (Z.of_nat k))) (v_gtu 143 (Z.of_nat k))) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma t_gtu159 : forallb (fun k => Z.eqb (c_gtu 159 (Z_to_bv 64 (Z.of_nat k))) (v_gtu 159 (Z.of_nat k))) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma t_gt239 : forallb (fun k => Z.eqb (c_gt239 (Z_to_bv 64 (Z.of_nat k))) (v_gtu 239 (Z.of_nat k))) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma t_lead : forallb (fun k => Z.eqb (c_lead (Z_to_bv 64 (sx8u (Z.of_nat k)))) (v_lead (Z.of_nat k))) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma t_leadu : forallb (fun k => Z.eqb (c_lead (Z_to_bv 64 (Z.of_nat k))) (v_lead (Z.of_nat k))) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma t_sx8 : forallb (fun k => Z.eqb (c_sx8 (Z_to_bv 64 (Z.of_nat k))) (sx8u (Z.of_nat k))) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r_ascii E j b : ev E j = Z_to_bv 64 b -> 0 <= b < 256 -> bv_unsigned (edenot E (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar j)) (ELit 0))) = v_ascii b.
Proof. intros H Hb. rewrite e_ascii, H. apply Z.eqb_eq. exact (by_table (fun b => Z.eqb (c_ascii (Z_to_bv 64 b)) (v_ascii b)) b t_ascii Hb). Qed.
Lemma r_cont E j b : ev E j = Z_to_bv 64 b -> 0 <= b < 256 -> bv_unsigned (edenot E (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar j)))) = v_cont b.
Proof. intros H Hb. rewrite e_cont, H. apply Z.eqb_eq. exact (by_table (fun b => Z.eqb (c_cont (Z_to_bv 64 b)) (v_cont b)) b t_cont Hb). Qed.
Lemma r_ltu144 E j b : ev E j = Z_to_bv 64 b -> 0 <= b < 256 -> bv_unsigned (edenot E (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_AND (EExt true 0 1 (EVar j)) (ELit 255)) (ELit 144))) = v_ltu b 144.
Proof. intros H Hb. rewrite e_ltu, H. apply Z.eqb_eq. exact (by_table (fun b => Z.eqb (c_ltu (Z_to_bv 64 b) 144) (v_ltu b 144)) b t_ltu144 Hb). Qed.
Lemma r_ltu160 E j b : ev E j = Z_to_bv 64 b -> 0 <= b < 256 -> bv_unsigned (edenot E (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_AND (EExt true 0 1 (EVar j)) (ELit 255)) (ELit 160))) = v_ltu b 160.
Proof. intros H Hb. rewrite e_ltu, H. apply Z.eqb_eq. exact (by_table (fun b => Z.eqb (c_ltu (Z_to_bv 64 b) 160) (v_ltu b 160)) b t_ltu160 Hb). Qed.
Lemma r_gtu143 E j b : ev E j = Z_to_bv 64 b -> 0 <= b < 256 -> bv_unsigned (edenot E (EAlu Instr.ALU_SLTU (ELit 143) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar j)) (ELit 255)))) = v_gtu 143 b.
Proof. intros H Hb. rewrite e_gtu, H. apply Z.eqb_eq. exact (by_table (fun b => Z.eqb (c_gtu 143 (Z_to_bv 64 b)) (v_gtu 143 b)) b t_gtu143 Hb). Qed.
Lemma r_gtu159 E j b : ev E j = Z_to_bv 64 b -> 0 <= b < 256 -> bv_unsigned (edenot E (EAlu Instr.ALU_SLTU (ELit 159) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar j)) (ELit 255)))) = v_gtu 159 b.
Proof. intros H Hb. rewrite e_gtu, H. apply Z.eqb_eq. exact (by_table (fun b => Z.eqb (c_gtu 159 (Z_to_bv 64 b)) (v_gtu 159 b)) b t_gtu159 Hb). Qed.
Lemma r_gt239 E j b : ev E j = Z_to_bv 64 b -> 0 <= b < 256 -> bv_unsigned (edenot E (EAlu Instr.ALU_SLT (ELit 239) (EVar j))) = v_gtu 239 b.
Proof. intros H Hb. rewrite e_gt239, H. apply Z.eqb_eq. exact (by_table (fun b => Z.eqb (c_gt239 (Z_to_bv 64 b)) (v_gtu 239 b)) b t_gt239 Hb). Qed.
Lemma r_lead E j b : ev E j = Z_to_bv 64 (sx8u b) -> 0 <= b < 256 -> bv_unsigned (edenot E (EAlu Instr.ALU_SLT (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar j)) (ELit 56)) (ELit (-62)))) = v_lead b.
Proof. intros H Hb. rewrite e_lead, H. apply Z.eqb_eq. exact (by_table (fun b => Z.eqb (c_lead (Z_to_bv 64 (sx8u b))) (v_lead b)) b t_lead Hb). Qed.
Lemma r_leadu E j b : ev E j = Z_to_bv 64 b -> 0 <= b < 256 ->
  bv_unsigned (edenot E (EAlu Instr.ALU_SLT (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar j)) (ELit 56)) (ELit (-62)))) = v_lead b.
Proof. intros H Hb. rewrite e_lead, H. apply Z.eqb_eq. exact (by_table (fun b => Z.eqb (c_lead (Z_to_bv 64 b)) (v_lead b)) b t_leadu Hb). Qed.
Lemma r_sx8 E j b : ev E j = Z_to_bv 64 b -> 0 <= b < 256 -> edenot E (EExt true 0 1 (EVar j)) = Z_to_bv 64 (sx8u b).
Proof.
  intros H Hb. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (EExt true 0 1 (EVar j)))). f_equal.
  rewrite e_sx8, H. apply Z.eqb_eq. exact (by_table (fun b => Z.eqb (c_sx8 (Z_to_bv 64 b)) (sx8u b)) b t_sx8 Hb).
Qed.

Lemma v_ascii_spec b : (v_ascii b = 0 <-> b < 128) /\ (v_ascii b = 1 <-> 128 <= b).
Proof. unfold v_ascii. destruct (Z.ltb_spec b 128); lia. Qed.
Lemma v_cont_spec b : (v_cont b = 0 <-> 128 <= b < 192) /\ (v_cont b = 1 <-> ~ (128 <= b < 192)).
Proof. unfold v_cont. destruct (Z.leb_spec 128 b); destruct (Z.ltb_spec b 192); cbn [andb]; lia. Qed.
Lemma v_ltu_spec b k : (v_ltu b k = 1 <-> b < k) /\ (v_ltu b k = 0 <-> k <= b).
Proof. unfold v_ltu. destruct (Z.ltb_spec b k); lia. Qed.
Lemma v_gtu_spec k b : (v_gtu k b = 1 <-> k < b) /\ (v_gtu k b = 0 <-> b <= k).
Proof. unfold v_gtu. destruct (Z.ltb_spec k b); lia. Qed.
Lemma v_lead_spec b : (v_lead b = 1 <-> 128 <= b < 194) /\ (v_lead b = 0 <-> ~ (128 <= b < 194)).
Proof. unfold v_lead. destruct (Z.leb_spec 128 b); destruct (Z.ltb_spec b 194); cbn [andb]; lia. Qed.
Lemma v_ascii_range b : 0 <= v_ascii b <= 1. Proof. unfold v_ascii. destruct (b <? 128); lia. Qed.
Lemma v_cont_range b : 0 <= v_cont b <= 1. Proof. unfold v_cont. destruct (_ && _); lia. Qed.
Lemma v_ltu_range b k : 0 <= v_ltu b k <= 1. Proof. unfold v_ltu. destruct (b <? k); lia. Qed.
Lemma v_gtu_range k b : 0 <= v_gtu k b <= 1. Proof. unfold v_gtu. destruct (k <? b); lia. Qed.
Lemma v_lead_range b : 0 <= v_lead b <= 1. Proof. unfold v_lead. destruct (_ && _); lia. Qed.

Lemma eqm64 x k : 0 <= x < 256 -> 0 <= k < 256 ->
  (((x - k) mod 2 ^ 64) < 1 <-> x = k) /\ (1 <= ((x - k) mod 2 ^ 64) <-> x <> k).
Proof.
  intros Hx Hk. destruct (Z_lt_le_dec x k) as [L|G].
  - replace ((x - k) mod 2 ^ 64) with (x - k + 2 ^ 64) by (symmetry; rewrite <- (Z.mod_add _ 1) by lia; apply Z.mod_small; lia). lia.
  - rewrite Z.mod_small by lia. lia.
Qed.

Section Fwd.
  Variables (E : env) (j : nat) (b : Z).
  Hypothesis Hj : ev E j = Z_to_bv 64 b.
  Hypothesis Hb : 0 <= b < 256.
  Let CONT := EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar j)).
  Let ASCII := EAlu Instr.ALU_SLT (EExt true 0 1 (EVar j)) (ELit 0).
  Let LTU k := EAlu Instr.ALU_SLTU (EAlu Instr.ALU_AND (EExt true 0 1 (EVar j)) (ELit 255)) (ELit k).
  Let GTU k := EAlu Instr.ALU_SLTU (ELit k) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar j)) (ELit 255)).
  Let GT239 := EAlu Instr.ALU_SLT (ELit 239) (EVar j).
  Lemma f_cont0 : bv_unsigned (edenot E CONT) <= 0 -> 128 <= b < 192.
  Proof. unfold CONT. rewrite (r_cont E j b Hj Hb). pose proof (v_cont_spec b). pose proof (v_cont_range b). lia. Qed.
  Lemma f_cont1 : 1 <= bv_unsigned (edenot E CONT) -> b < 128 \/ 192 <= b.
  Proof. unfold CONT. rewrite (r_cont E j b Hj Hb). pose proof (v_cont_spec b). pose proof (v_cont_range b). lia. Qed.
  Lemma f_ascii0 : bv_unsigned (edenot E ASCII) <= 0 -> b < 128.
  Proof. unfold ASCII. rewrite (r_ascii E j b Hj Hb). pose proof (v_ascii_spec b). pose proof (v_ascii_range b). lia. Qed.
  Lemma f_ascii1 : 1 <= bv_unsigned (edenot E ASCII) -> 128 <= b.
  Proof. unfold ASCII. rewrite (r_ascii E j b Hj Hb). pose proof (v_ascii_spec b). pose proof (v_ascii_range b). lia. Qed.
  Lemma f_ltu144_0 : bv_unsigned (edenot E (LTU 144)) <= 0 -> 144 <= b.
  Proof. unfold LTU. rewrite (r_ltu144 E j b Hj Hb). pose proof (v_ltu_spec b 144). pose proof (v_ltu_range b 144). lia. Qed.
  Lemma f_ltu144_1 : 1 <= bv_unsigned (edenot E (LTU 144)) -> b < 144.
  Proof. unfold LTU. rewrite (r_ltu144 E j b Hj Hb). pose proof (v_ltu_spec b 144). pose proof (v_ltu_range b 144). lia. Qed.
  Lemma f_ltu160_0 : bv_unsigned (edenot E (LTU 160)) <= 0 -> 160 <= b.
  Proof. unfold LTU. rewrite (r_ltu160 E j b Hj Hb). pose proof (v_ltu_spec b 160). pose proof (v_ltu_range b 160). lia. Qed.
  Lemma f_ltu160_1 : 1 <= bv_unsigned (edenot E (LTU 160)) -> b < 160.
  Proof. unfold LTU. rewrite (r_ltu160 E j b Hj Hb). pose proof (v_ltu_spec b 160). pose proof (v_ltu_range b 160). lia. Qed.
  Lemma f_gtu143_0 : bv_unsigned (edenot E (GTU 143)) <= 0 -> b <= 143.
  Proof. unfold GTU. rewrite (r_gtu143 E j b Hj Hb). pose proof (v_gtu_spec 143 b). pose proof (v_gtu_range 143 b). lia. Qed.
  Lemma f_gtu143_1 : 1 <= bv_unsigned (edenot E (GTU 143)) -> 143 < b.
  Proof. unfold GTU. rewrite (r_gtu143 E j b Hj Hb). pose proof (v_gtu_spec 143 b). pose proof (v_gtu_range 143 b). lia. Qed.
  Lemma f_gtu159_0 : bv_unsigned (edenot E (GTU 159)) <= 0 -> b <= 159.
  Proof. unfold GTU. rewrite (r_gtu159 E j b Hj Hb). pose proof (v_gtu_spec 159 b). pose proof (v_gtu_range 159 b). lia. Qed.
  Lemma f_gtu159_1 : 1 <= bv_unsigned (edenot E (GTU 159)) -> 159 < b.
  Proof. unfold GTU. rewrite (r_gtu159 E j b Hj Hb). pose proof (v_gtu_spec 159 b). pose proof (v_gtu_range 159 b). lia. Qed.
  Lemma f_gt239_0 : bv_unsigned (edenot E GT239) <= 0 -> b <= 239.
  Proof. unfold GT239. rewrite (r_gt239 E j b Hj Hb). pose proof (v_gtu_spec 239 b). pose proof (v_gtu_range 239 b). lia. Qed.
  Lemma f_gt239_1 : 1 <= bv_unsigned (edenot E GT239) -> 239 < b.
  Proof. unfold GT239. rewrite (r_gt239 E j b Hj Hb). pose proof (v_gtu_spec 239 b). pose proof (v_gtu_range 239 b). lia. Qed.
End Fwd.
Section FwdLead.
  Variables (E : env) (j : nat) (b : Z).
  Hypothesis Hj : ev E j = Z_to_bv 64 (sx8u b).
  Hypothesis Hb : 0 <= b < 256.
  Let LEAD := EAlu Instr.ALU_SLT (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar j)) (ELit 56)) (ELit (-62)).
  Lemma f_lead0 : bv_unsigned (edenot E LEAD) <= 0 -> b < 128 \/ 194 <= b.
  Proof. unfold LEAD. rewrite (r_lead E j b Hj Hb). pose proof (v_lead_spec b). pose proof (v_lead_range b). lia. Qed.
  Lemma f_lead1 : 1 <= bv_unsigned (edenot E LEAD) -> 128 <= b < 194.
  Proof. unfold LEAD. rewrite (r_lead E j b Hj Hb). pose proof (v_lead_spec b). pose proof (v_lead_range b). lia. Qed.
End FwdLead.
Section FwdLeadU.
  Variables (E : env) (j : nat) (b : Z).
  Hypothesis Hj : ev E j = Z_to_bv 64 b.
  Hypothesis Hb : 0 <= b < 256.
  Let LEAD := EAlu Instr.ALU_SLT (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar j)) (ELit 56)) (ELit (-62)).
  Lemma f_leadu0 : bv_unsigned (edenot E LEAD) <= 0 -> b < 128 \/ 194 <= b.
  Proof. unfold LEAD. rewrite (r_leadu E j b Hj Hb). pose proof (v_lead_spec b). pose proof (v_lead_range b). lia. Qed.
  Lemma f_leadu1 : 1 <= bv_unsigned (edenot E LEAD) -> 128 <= b < 194.
  Proof. unfold LEAD. rewrite (r_leadu E j b Hj Hb). pose proof (v_lead_spec b). pose proof (v_lead_range b). lia. Qed.
End FwdLeadU.
Lemma eqm_eq x k : 0 <= x < 256 -> 0 <= k < 256 -> ((x - k) mod 2 ^ 64) < 1 -> x = k.
Proof. intros Hx Hk H. pose proof (eqm64 x k Hx Hk). lia. Qed.
Lemma eqm_ne x k : 0 <= x < 256 -> 0 <= k < 256 -> 1 <= ((x - k) mod 2 ^ 64) -> x < k \/ k < x.
Proof. intros Hx Hk H. pose proof (eqm64 x k Hx Hk). lia. Qed.

End K.

Lemma sub_in (A KS : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) A = true -> forall k, In k A -> In k KS.
Proof.
  intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.
Ltac kin := apply sub_in; vm_compute; reflexivity.

Ltac raw1 :=
  match goal with
  | H : _ <= bv_unsigned (edenot _ _) <= _ |- _ => destruct H as [? H]
  | H : 0 <= bv_unsigned (edenot _ _) |- _ => clear H
  | H : bv_unsigned (edenot _ _) <= 1 |- _ => clear H
  | H : bv_unsigned (edenot ?E (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar ?j)))) <= 0 |- _ =>
      apply (f_cont0 E j _ eq_refl ltac:(assumption)) in H
  | H : 1 <= bv_unsigned (edenot ?E (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar ?j)))) |- _ =>
      apply (f_cont1 E j _ eq_refl ltac:(assumption)) in H
  | H : bv_unsigned (edenot ?E (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar ?j)) (ELit 0))) <= 0 |- _ =>
      apply (f_ascii0 E j _ eq_refl ltac:(assumption)) in H
  | H : 1 <= bv_unsigned (edenot ?E (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar ?j)) (ELit 0))) |- _ =>
      apply (f_ascii1 E j _ eq_refl ltac:(assumption)) in H
  | H : bv_unsigned (edenot ?E (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_AND (EExt true 0 1 (EVar ?j)) (ELit 255)) (ELit 144))) <= 0 |- _ =>
      apply (f_ltu144_0 E j _ eq_refl ltac:(assumption)) in H
  | H : 1 <= bv_unsigned (edenot ?E (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_AND (EExt true 0 1 (EVar ?j)) (ELit 255)) (ELit 144))) |- _ =>
      apply (f_ltu144_1 E j _ eq_refl ltac:(assumption)) in H
  | H : bv_unsigned (edenot ?E (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_AND (EExt true 0 1 (EVar ?j)) (ELit 255)) (ELit 160))) <= 0 |- _ =>
      apply (f_ltu160_0 E j _ eq_refl ltac:(assumption)) in H
  | H : 1 <= bv_unsigned (edenot ?E (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_AND (EExt true 0 1 (EVar ?j)) (ELit 255)) (ELit 160))) |- _ =>
      apply (f_ltu160_1 E j _ eq_refl ltac:(assumption)) in H
  | H : bv_unsigned (edenot ?E (EAlu Instr.ALU_SLTU (ELit 143) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar ?j)) (ELit 255)))) <= 0 |- _ =>
      apply (f_gtu143_0 E j _ eq_refl ltac:(assumption)) in H
  | H : 1 <= bv_unsigned (edenot ?E (EAlu Instr.ALU_SLTU (ELit 143) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar ?j)) (ELit 255)))) |- _ =>
      apply (f_gtu143_1 E j _ eq_refl ltac:(assumption)) in H
  | H : bv_unsigned (edenot ?E (EAlu Instr.ALU_SLTU (ELit 159) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar ?j)) (ELit 255)))) <= 0 |- _ =>
      apply (f_gtu159_0 E j _ eq_refl ltac:(assumption)) in H
  | H : 1 <= bv_unsigned (edenot ?E (EAlu Instr.ALU_SLTU (ELit 159) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar ?j)) (ELit 255)))) |- _ =>
      apply (f_gtu159_1 E j _ eq_refl ltac:(assumption)) in H
  | H : bv_unsigned (edenot ?E (EAlu Instr.ALU_SLT (ELit 239) (EVar ?j))) <= 0 |- _ =>
      apply (f_gt239_0 E j _ eq_refl ltac:(assumption)) in H
  | H : 1 <= bv_unsigned (edenot ?E (EAlu Instr.ALU_SLT (ELit 239) (EVar ?j))) |- _ =>
      apply (f_gt239_1 E j _ eq_refl ltac:(assumption)) in H
  | H : bv_unsigned (edenot ?E (EAlu Instr.ALU_SLT (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar ?j)) (ELit 56)) (ELit (-62)))) <= 0 |- _ =>
      first [ apply (f_lead0 E j _ eq_refl ltac:(assumption)) in H | apply (f_leadu0 E j _ eq_refl ltac:(assumption)) in H ]
  | H : 1 <= bv_unsigned (edenot ?E (EAlu Instr.ALU_SLT (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar ?j)) (ELit 56)) (ELit (-62)))) |- _ =>
      first [ apply (f_lead1 E j _ eq_refl ltac:(assumption)) in H | apply (f_leadu1 E j _ eq_refl ltac:(assumption)) in H ]
  | H : getr _ _ = edenot ?E (EExt true 0 1 (EVar ?j)) |- _ =>
      rewrite (r_sx8 E j _ eq_refl ltac:(assumption)) in H
  | H : getr _ _ = edenot _ _ |- _ => clear H
  | H : ((?x - ?k) mod 2 ^ 64) < 1 |- _ => apply (eqm_eq x k ltac:(assumption) ltac:(clear; lia)) in H
  | H : 1 <= ((?x - ?k) mod 2 ^ 64) |- _ => apply (eqm_ne x k ltac:(assumption) ltac:(clear; lia)) in H
  end.
Ltac raws := repeat raw1.

Ltac fold_bytes := repeat match goal with E : ?b = bat ?l ?j |- context [bat ?l ?j] => rewrite <- E end.

Ltac legal_false :=
  first [ apply legal_false_lead1; assumption
        | apply legal_false_lead2; first [assumption | lia]
        | apply legal_false_c1; assumption
        | apply legal_false_c2; assumption
        | apply legal_false_c3; assumption
        | apply legal_false_e0; assumption
        | apply legal_false_ed; assumption
        | apply legal_false_f0; assumption
        | apply legal_false_f4; assumption ].
Ltac legal_true :=
  first [ apply legal1_true | apply legal2_true | apply legal3_true | apply legal4_true ]; first [assumption | lia | intros ->; lia].

Ltac split_exit H MS KS := destruct H as [MS H]; lazymatch type of H with
  | (forall x, _) /\ _ => destruct H as [KS H]; repeat (lazymatch type of H with _ /\ _ => destruct H as [? H] end)
  | _ => rename H into KS
  end.
Ltac get_reg Rx n :=
  match goal with
  | H : getr Rx (Z_to_bv 5 (Z.of_nat n)) = Z_to_bv 64 ?v |- _ => constr:(H)
  end.

Ltac asc_byte :=
  let Hk := fresh in intros Hk;
  first [ match goal with E : ?b = bat _ ?j |- bat _ ?j < 128 => rewrite <- E; assumption end | exfalso; clear - Hk; lia ].

End PECVK.
