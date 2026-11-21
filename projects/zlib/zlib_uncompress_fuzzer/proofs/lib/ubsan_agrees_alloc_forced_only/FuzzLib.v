(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.


Definition lkeeps (l : list reg) (regs regs' : bvmap 5 word) : Prop :=
  forall r : reg, In r l -> getr regs' r = getr regs r.

Lemma lkeeps_refl : forall l regs, lkeeps l regs regs.
Proof. intros l regs r _. reflexivity. Qed.

Lemma lkeeps_trans : forall l r1 r2 r3, lkeeps l r1 r2 -> lkeeps l r2 r3 -> lkeeps l r1 r3.
Proof. intros l r1 r2 r3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.

Lemma lkeeps_upd : forall l regs regs' (rd : reg) v,
  lkeeps l regs regs' -> ~ In rd l -> lkeeps l regs (regupd regs' rd v).
Proof.
  intros l regs regs' rd v K Hn r Hr.
  rewrite getr_other; [apply K, Hr|]. intros ->. exact (Hn Hr).
Qed.


Lemma lkeeps_incl : forall l l' regs regs', incl l' l -> lkeeps l regs regs' -> lkeeps l' regs regs'.
Proof. intros l l' regs regs' Hi K r Hr. apply K, Hi, Hr. Qed.


Lemma keeps_cs_lkeeps : forall regs regs', keeps_cs regs regs' <-> lkeeps callee_saved regs regs'.
Proof. intros; split; intros K r Hr; apply K, Hr. Qed.

Ltac not_inl := first [ apply RefMemcpyLib.not_in_regs_dec; reflexivity | cbv; intuition discriminate ].
Ltac solve_lkeeps :=
  repeat (apply lkeeps_upd; [| not_inl]); first [apply lkeeps_refl | assumption].

Lemma incl_regs_dec : forall (l' l : list reg),
  forallb (fun x => existsb (fun y => bv_eqb y x) l) l' = true -> incl l' l.
Proof.
  intros l' l H r Hr. apply in_regs_dec.
  exact (proj1 (forallb_forall _ _) H r Hr).
Qed.
Ltac incl_dec := apply incl_regs_dec; reflexivity.

Definition ak1 : list reg := [1; 3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
















Lemma v_add_wrap2 : forall a b, v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. unfold v_add. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite <- Zplus_mod. reflexivity.
Qed.















Definition LIM1 : Z := 18446744073708503040.
Definition LIM2 : Z := 18446744073708503039.


Lemma entry_test_out : forall n, (0 <= n < 2 ^ 64)%Z -> ~ (1 <= n <= 1048576)%Z ->
  c_ltu (v_add (Z_to_bv 64 n) (Z_to_bv 64 LIM2)) (Z_to_bv 64 LIM1) = true.
Proof.
  intros n Hn Hout. unfold LIM1, LIM2. rewrite v_add_wrap2.
  destruct (Z.eq_dec n 0) as [->|Hnz].
  - rewrite c_ltu_lit by lia. apply Z.ltb_lt. lia.
  - rewrite (Z_to_bv_64_mod (n + _)).
    replace ((n + 18446744073708503039) mod 2 ^ 64)%Z with (n - 1048577)%Z.
    + rewrite c_ltu_lit by lia. apply Z.ltb_lt. lia.
    + replace (n + 18446744073708503039)%Z with ((n - 1048577) + 1 * 2 ^ 64)%Z by lia.
      rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia.
Qed.


Definition AM : Z := 106321291491121335.










Lemma rdn1_grows : forall segs m m' (a : word) b,
  mem_grows m m' -> rdn segs m a 1 = Some [b] -> exists b', rdn segs m' a 1 = Some [b'].
Proof.
  intros segs m m' a b Hg H. cbn [rdn] in *.
  destruct (m a) as [b0|] eqn:Hm.
  - assert (Hm' : m' a <> None) by (apply Hg; congruence).
    destruct (m' a) as [b1|]; [exists b1; reflexivity | congruence].
  - destruct (m' a) as [b1|]; [exists b1; reflexivity|].
    destruct (seg_rom segs a) as [b2|]; [exists b2; reflexivity | discriminate].
Qed.

Lemma rdn1_wbytes : forall segs m (a wa : word) bs b,
  rdn segs m a 1 = Some [b] -> exists b', rdn segs (wbytes m wa bs) a 1 = Some [b'].
Proof. intros segs m a wa bs b H. eapply rdn1_grows; [apply wbytes_grows | exact H]. Qed.

Lemma lenW8 : forall v : word, length (word_to_le_bytes 8 v) = 8%nat.
Proof. intros v. apply length_N_to_le_bytes. Qed.
