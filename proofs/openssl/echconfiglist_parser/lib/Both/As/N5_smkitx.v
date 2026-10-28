(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge TacX SFModel SysStep.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsWalk FakeStackRep N5_smkit.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma land_16383 : forall x, Z.land x 16383 = x mod 16384.
Proof. intros. change 16383 with (Z.ones 14). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_4095 : forall x, Z.land x 4095 = x mod 4096.
Proof. intros. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_255 : forall x, Z.land x 255 = x mod 256.
Proof. intros. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma wrap_mod_16384 : forall e, bv_unsigned (Z_to_bv 64 e) mod 16384 = e mod 16384.
Proof. intros e. exact (unsigned_wrap_mod e 14 ltac:(lia)). Qed.
Lemma wrap_mod_4096 : forall e, bv_unsigned (Z_to_bv 64 e) mod 4096 = e mod 4096.
Proof. intros e. exact (unsigned_wrap_mod e 12 ltac:(lia)). Qed.
Lemma wrap_mod_256 : forall e, bv_unsigned (Z_to_bv 64 e) mod 256 = e mod 256.
Proof. intros e. exact (unsigned_wrap_mod e 8 ltac:(lia)). Qed.


Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Lemma RFSI_free_slot_n : forall fsb LF m k h, RFSI fsb LF m -> 0 <= k <= KMAX -> Z.of_nat (length LF) < NF k ->
  exists j, 0 <= j < NF k /\ flagv LF (flag_addr fsb k ((h + j) mod NF k)) = 0.
Proof.
  intros fsb LF m k h R HK LEN. pose proof R as (_ & _ & _ & SL & _).
  pose proof (class_facts k HK) as (A & _).
  destruct (seqZ_facts (Z.to_nat (NF k))) as (ND & INS & LENS).
  destruct (existsb (fun p => negb (liveb LF (flag_addr fsb k p))) (map Z.of_nat (seq 0 (Z.to_nat (NF k))))) eqn:EX.
  - apply existsb_exists in EX. destruct EX as (p & IN & NL). apply INS in IN.
    exists ((p - h) mod NF k). split; [Z.div_mod_to_equations; lia|].
    replace ((h + (p - h) mod NF k) mod NF k) with p.
    2:{ rewrite Zplus_mod_idemp_r. replace (h + (p - h)) with p by lia. symmetry. apply Z.mod_small. lia. }
    unfold flagv. destruct (liveb LF (flag_addr fsb k p)); [cbn in NL; discriminate| reflexivity].
  - exfalso.
    assert (ALL : forall p, In p (map Z.of_nat (seq 0 (Z.to_nat (NF k)))) -> 0 <= p < NF k /\ liveb LF (flag_addr fsb k p) = true).
    { intros p IN. pose proof (proj1 (INS p) IN) as RP. split; [lia|].
      destruct (liveb LF (flag_addr fsb k p)) eqn:L; [reflexivity|]. exfalso.
      assert (T : existsb (fun p => negb (liveb LF (flag_addr fsb k p))) (map Z.of_nat (seq 0 (Z.to_nat (NF k)))) = true).
      { apply existsb_exists. exists p. split; [exact IN|]. rewrite L. reflexivity. }
      rewrite T in EX. discriminate. }
    assert (SL' : forall f, In f LF -> exists pos, slot_ok (ff_class f) pos /\ ff_flag f = flag_addr fsb (ff_class f) pos).
    { intros f IN. destruct (SL f IN) as (pos & S & _ & E). exists pos. split; assumption. }
    pose proof (live_positions_bound fsb k LF _ HK SL' ND ALL) as B.
    rewrite LENS in B. lia.
Qed.


(* [comment removed for export] *)
Lemma shad8_of_word : forall m A, 0 <= A -> A mod 8 = 0 ->
  rw_cells asegs m (sh A) [C8 (Z_to_bv 64 0)] -> SHAD m A (poison_bytes 8 0).
Proof.
  intros m A H0 H8 RC. split; [exact H0|]. split; [exact H8|].
  apply (u8arr_of_rw_cells asegs m (sh A) 8).
  pose proof (rw_cells_merge asegs m (sh A) [] [C8 (Z_to_bv 64 0)] []) as M.
  rewrite app_nil_r in M. cbn [app cells_size csize cells_bytes cbytes Nat.add] in M.
  exact (M RC).
Qed.

(* [comment removed for export] *)
Lemma shad32_of_words : forall m A, 0 <= A -> A mod 8 = 0 ->
  rw_cells asegs m (sh A) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] -> SHAD m A (poison_bytes 32 0).
Proof.
  intros m A H0 H8 RC. split; [exact H0|]. split; [exact H8|].
  apply (u8arr_of_rw_cells asegs m (sh A) 32).
  pose proof (rw_cells_merge asegs m (sh A) [] [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] []) as M.
  rewrite app_nil_r in M. cbn [app cells_size csize cells_bytes cbytes Nat.add] in M.
  exact (M RC).
Qed.

(* [comment removed for export] *)
Lemma shad512_zero : forall m A, 0 <= A -> A mod 8 = 0 ->
  rw_cells asegs m (sh A) (repeat (C8 (Z_to_bv 64 0)) 64) -> SHAD m A (poison_bytes 512 0).
Proof.
  intros m A H0 H8 RC. split; [exact H0|]. split; [exact H8|].
  apply (u8arr_of_rw_cells asegs m (sh A) 512).
  pose proof (rw_cells_merge asegs m (sh A) [] (repeat (C8 (Z_to_bv 64 0)) 64) []) as M.
  rewrite app_nil_r in M. cbn [app cells_size csize cells_bytes cbytes Nat.add repeat] in M.
  exact (M RC).
Qed.
Lemma le8_f5 : le8 (Z_to_bv 64 0xf5f5f5f5f5f5f5f5) = repeat (b8 0xf5) 8.
Proof. cbn [repeat]. unfold le8. repeat (apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|]). reflexivity. Qed.
Lemma shad512_f5 : forall m A, 0 <= A -> A mod 8 = 0 ->
  rw_cells asegs m (sh A) (repeat (C8 (Z_to_bv 64 0xf5f5f5f5f5f5f5f5)) 64) -> SHAD m A (poison_bytes 512 0xf5).
Proof.
  intros m A H0 H8 RC. split; [exact H0|]. split; [exact H8|].
  apply (u8arr_of_rw_cells asegs m (sh A) 512).
  pose proof (rw_cells_merge asegs m (sh A) [] (repeat (C8 (Z_to_bv 64 0xf5f5f5f5f5f5f5f5)) 64) []) as M.
  rewrite app_nil_r in M. cbn [app cells_size csize cells_bytes cbytes Nat.add repeat] in M. rewrite !le8_f5 in M. cbn [repeat app] in M.
  exact (M RC).
Qed.
End HCW.
