(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import
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
Definition bk : list reg := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv.


Lemma lxor_lt_256 : forall a b, (0 <= a < 256)%Z -> (0 <= b < 256)%Z -> (0 <= Z.lxor a b < 256)%Z.
Proof.
  intros a b Ha Hb. split; [apply Z.lxor_nonneg; lia|].
  apply (Z_bounded_by_bits 8); [lia | apply Z.lxor_nonneg; lia |].
  intros k Hk. rewrite Z.lxor_spec.
  rewrite (Z_testbit_high 8 a k) by lia. rewrite (Z_testbit_high 8 b k) by lia. reflexivity.
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
