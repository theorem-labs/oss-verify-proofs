(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf Zpa.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Zpm Zwd Z107.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition T_JT : Z := 143796.
Definition JT_TAB : list Z :=
  [518208; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 512000; 601868; 601868; 512000; 512000; 512000; 512000; 512000; 512000; 512000; 512000; 512000; 512000; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 519872; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 519568; 601868; 601868; 601868; 601868; 601868; 601868; 601868; 517072; 601868; 601868; 601868; 601868; 601868; 517348; 601868; 601868; 601868; 601868; 601868; 601868; 517624].
Definition jt (i : Z) : Z := nth (Z.to_nat i) JT_TAB 0.
Definition JT_WORDS : list word := map (Z_to_bv 64) JT_TAB.

Lemma jt_image : ro_bytes_b bsegs T_JT (u32s JT_WORDS) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma jt_at : forall m, mem_inv bsegs m -> bytes_at bsegs m T_JT (u32s JT_WORDS).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold T_JT; lia | rewrite u32s_length; unfold T_JT, JT_WORDS; rewrite length_map; cbn; lia |].
  apply ro_bytes_b_sound. exact jt_image.
Qed.
Lemma jt_read : forall (m : word -> option byte) i a, mem_inv bsegs m -> 0 <= i < 90 -> a = wa (T_JT + 4 * i) ->
  ov_read_bytes bsegs m a 4 = Some (le4 (Z_to_bv 64 (jt i))).
Proof.
  intros m i a MI Hi ->. eapply (u32ro_read m T_JT JT_WORDS i); [apply jt_at; exact MI| | lia | reflexivity].
  unfold JT_WORDS, jt. rewrite nth_error_map. rewrite (nth_error_nth' JT_TAB 0); [reflexivity|].
  change (length JT_TAB) with 90%nat. lia.
Qed.

Definition root_target (b : Z) : Z :=
  if b =? 34 then 662004 else if (b =? 45) || ((48 <=? b) && (b <=? 57)) then 655796 else if b =? 91 then 663668
  else if b =? 102 then 663364 else if b =? 110 then 660868 else if b =? 116 then 661144 else if b =? 123 then 661420 else 745664.

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
