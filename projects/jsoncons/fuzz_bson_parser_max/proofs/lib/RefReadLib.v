(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX Frame RefMemcpyLib.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kfootprint (E : env) (K : kentry) : option (Z * Z) :=
  match K with
  | KWord a w _ => Some (estart E a, Z.of_nat w)
  | KZero a n => Some (estart E a, elenZ E n)
  | KBlob a n _ => Some (estart E a, elenZ E n)
  | KImg lo hi => Some (lo, hi - lo)%Z
  | _ => None
  end.

Definition kfoot_far (E : env) (K : kentry) (wa wn : Z) : Prop :=
  match kfootprint E K with
  | None => True
  | Some (s, n) => (s + n <= wa \/ wa + wn <= s)%Z
  end.

Lemma wbytes_same_far : forall m (a : word) bs (x : word),
  (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  (bv_unsigned x + 1 <= bv_unsigned a \/ bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned x)%Z ->
  wbytes m a bs x = m x.
Proof.
  intros m a bs x Hnw Hfar. apply wbytes_outside; [|exact Hnw]. unfold in_rng. lia.
Qed.

Lemma kentry_ok_wbytes_far : forall segs E M (a : word) bs K,
  (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  kfoot_far E K (bv_unsigned a) (Z.of_nat (length bs)) ->
  kentry_ok segs E M K -> kentry_ok segs E (wbytes M a bs) K.
Proof.
  intros segs E M a bs K Hnw Hfar HK.
  destruct K as [[b k] w v|[b k] n|[b k] n bk|lo hi|e m|e lo hi|[b k] n|a1 n1 a2 n2];
    cbn [kfoot_far kfootprint kentry_ok] in *; try exact HK.
  - destruct HK as (Hw & Hfl & Hr). split; [exact Hw|]. split; [exact Hfl|].
    rewrite <- Hr. pose proof (flat_u E _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
    apply rdn_agree. intros j Hj. rewrite Hu. apply wbytes_same_far; [exact Hnw|].
    rewrite u_small by lia. unfold estart in *. cbn [a_base a_off] in *. lia.
  - destruct HK as (Hfl & Hz). split; [exact Hfl|]. intros i Hi.
    destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite wbytes_same_far; [apply Hz; exact Hi | exact Hnw |]. rewrite u_small by lia. lia.
  - destruct HK as (Hfl & Hlen & Hz). split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi.
    destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite wbytes_same_far; [apply Hz; exact Hi | exact Hnw |]. rewrite u_small by lia. lia.
  - destruct HK as (H0 & H64 & Hnone). split; [exact H0|]. split; [exact H64|]. intros i Hi.
    rewrite wbytes_same_far; [apply Hnone; exact Hi | exact Hnw |]. rewrite u_small by lia. lia.
  - destruct HK as [Hfl Hst]. split; [exact Hfl|]. intros d m Hd Hm.
    eapply store_ok_mono; [apply wbytes_grows|]. apply Hst; assumption.
Qed.

Lemma know_ok_wbytes_far : forall segs E M (a : word) bs kn,
  (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  Forall (fun K => kfoot_far E K (bv_unsigned a) (Z.of_nat (length bs))) kn ->
  know_ok segs E M kn -> know_ok segs E (wbytes M a bs) kn.
Proof.
  intros segs E M a bs kn Hnw Hfar HK. unfold know_ok in *.
  induction kn as [|K rest IH]; [constructor|].
  apply Forall_cons_iff in Hfar as [F1 F2]. apply Forall_cons_iff in HK as [K1 K2].
  constructor; [eapply kentry_ok_wbytes_far; eassumption | apply IH; assumption].
Qed.

(* [comment removed for export] *)
Lemma wbytes_nil' : forall m (a : word), wbytes m a [] = m.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mem_denot_1 : forall E M a w v,
  mem_denot E M [SE a w v] = wbytes M (adenot E a) (word_to_le_bytes w (edenot E v)).
Proof. reflexivity. Qed.

Lemma mem_denot_nil : forall E M, mem_denot E M [] = M.
Proof. reflexivity. Qed.

Lemma rdn_wbytes_self : forall segs m (a : word) bs,
  (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  rdn segs (wbytes m a bs) a (length bs) = Some bs.
Proof. intros. apply rdn_wbytes_hit. assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma word_to_nat_lit : forall z, (0 <= z < 2 ^ 64)%Z -> word_to_nat (Z_to_bv 64 z) = Z.to_nat z.
Proof. intros z Hz. unfold word_to_nat. rewrite u_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma file_read_all : forall data (cnt : Z),
  (Z.of_nat (length data) <= cnt < 2 ^ 64)%Z ->
  file_read data (Z_to_bv 64 0) (Z_to_bv 64 cnt) = data.
Proof.
  intros data cnt Hc. rewrite file_read_unguarded. rewrite !word_to_nat_lit by lia. cbn [Z.to_nat skipn].
  apply firstn_all2. lia.
Qed.

(* [comment removed for export] *)
Lemma file_read_eof : forall data (off cnt : word),
  (Z.of_nat (length data) <= bv_unsigned off)%Z -> file_read data off cnt = [].
Proof.
  intros data off cnt Ho. rewrite file_read_unguarded.
  rewrite skipn_all2 by (unfold word_to_nat; lia). apply firstn_nil.
Qed.

(* [comment removed for export] *)
Lemma file_read_full : forall data (off cnt : Z),
  (0 <= off)%Z -> (0 <= cnt)%Z -> (off + cnt <= Z.of_nat (length data))%Z -> (Z.of_nat (length data) < 2 ^ 64)%Z ->
  file_read data (Z_to_bv 64 off) (Z_to_bv 64 cnt) = firstn (Z.to_nat cnt) (skipn (Z.to_nat off) data)
  /\ length (file_read data (Z_to_bv 64 off) (Z_to_bv 64 cnt)) = Z.to_nat cnt.
Proof.
  intros data off cnt H0 H1 H2 H3. rewrite !file_read_unguarded. rewrite !word_to_nat_lit by lia.
  split; [reflexivity|]. rewrite length_firstn, length_skipn. lia.
Qed.

Lemma len_word_Z : forall bs : list byte, len_word bs = Z_to_bv 64 (Z.of_nat (length bs)).
Proof. intros. reflexivity. Qed.
End FPX_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
