(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjLeaves.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_stage2_defs Sj_tables.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition T_JT : Z := 79724.
Definition JT_TAB : list Z :=
  [200292; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 196872; 231080; 231080; 196872; 196872; 196872; 196872; 196872; 196872; 196872; 196872; 196872; 196872; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 201556; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 201060; 231080; 231080; 231080; 231080; 231080; 231080; 231080; 198400; 231080; 231080; 231080; 231080; 231080; 198556; 231080; 231080; 231080; 231080; 231080; 231080; 199004].
Definition jt (i : Z) : Z := nth (Z.to_nat i) JT_TAB 0.
Definition JT_WORDS : list word := map (Z_to_bv 64) JT_TAB.

Lemma jt_image : ro_bytes_b usegs T_JT (u32s JT_WORDS) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma jt_at : forall m, mem_inv usegs m -> bytes_at usegs m T_JT (u32s JT_WORDS).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold T_JT; lia | rewrite u32s_length; unfold T_JT, JT_WORDS; rewrite length_map; cbn; lia |].
  apply ro_bytes_b_sound. exact jt_image.
Qed.
Lemma jt_read : forall (m : word -> option byte) i a, mem_inv usegs m -> 0 <= i < 90 -> a = wa (T_JT + 4 * i) ->
  ov_read_bytes usegs m a 4 = Some (le4 (Z_to_bv 64 (jt i))).
Proof.
  intros m i a MI Hi ->. eapply (u32ro_read m T_JT JT_WORDS i); [apply jt_at; exact MI| | lia | reflexivity].
  unfold JT_WORDS, jt. rewrite nth_error_map. rewrite (nth_error_nth' JT_TAB 0); [reflexivity|].
  change (length JT_TAB) with 90%nat. lia.
Qed.

Definition root_target (b : Z) : Z :=
  if b =? 34 then 280016 else if (b =? 45) || ((48 <=? b) && (b <=? 57)) then 276596 else if b =? 91 then 281280
  else if b =? 102 then 280784 else if b =? 110 then 278124 else if b =? 116 then 278280 else if b =? 123 then 278728 else 310804.

Lemma jt_range : forall i, 0 <= i < 90 -> 0 <= jt i < 2 ^ 31.
Proof.
  intros i Hi. unfold jt.
  assert (F : forallb (fun x => (0 <=? x) && (x <? 2 ^ 31)) JT_TAB = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in F. assert (L : (Z.to_nat i < length JT_TAB)%nat) by (change (length JT_TAB) with 90%nat; lia).
  specialize (F _ (nth_In JT_TAB 0 L)). apply andb_true_iff in F. destruct F as [F1 F2]. apply Z.leb_le in F1. apply Z.ltb_lt in F2. lia.
Qed.

Lemma jt_target : forall b, 34 <= b <= 123 -> T_JT + jt (b - 34) = root_target b.
Proof.
  intros b Hb.
  assert (F : forallb (fun i => T_JT + jt (i - 34) =? root_target i) (map Z.of_nat (seq 34 90)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in F. apply Z.eqb_eq. apply F.
  apply in_map_iff. exists (Z.to_nat b). split; [lia|]. apply in_seq. lia.
Qed.
