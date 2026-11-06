(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg SymExec Frame RefMemcpyLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import SymExec3 SymExec3Sound SymRun3.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Definition blobs_ev (bl : list (list byte)) : nat -> list byte := fun n => nth n bl [].

Section Drive.
Context {fx : FPState}.
Variable segs : list Segment.

Definition kread (kn : list kentry) (b : expr) (k : Z) (n : nat) : option expr :=
  match know_lookup segs kn b k n false [] [] with
  | LHit v [] _ => Some v
  | _ => None
  end.

Lemma kread_sound : forall E M kn b k n v,
  know_ok segs E M kn -> kread kn b k n = Some v -> (1 <= n)%nat -> (n <= 8)%nat ->
  flat E (SA b k) (Z.of_nat n) ->
  exists bs, rdn segs M (adenot E (SA b k)) n = Some bs /\ length bs = n
             /\ Z_to_bv 64 (bytes_le_to_Z bs) = edenot E v.
Proof.
  intros E M kn b k n v Hkn Hr Hn1 Hn8 Hfl. unfold kread in Hr.
  pose proof (know_lookup_sound segs E M kn b k n false [] [] Hkn Hn1 Hn8) as Hs.
  destruct (know_lookup segs kn b k n false [] []) as [v' scs h|scs h|]; try discriminate.
  destruct scs; [|discriminate]. injection Hr as ->.
  destruct (Hs ltac:(constructor) Hfl) as (bs & A & B & C). exists bs. unfold extz in C. auto.
Qed.

Lemma word_to_le_bytes_of_lez : forall n bs,
  length bs = n -> (n <= 8)%nat -> word_to_le_bytes n (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros n bs Hl Hn. unfold word_to_le_bytes.
  pose proof (bytes_le_to_Z_bound bs) as Hb. rewrite Hl in Hb.
  assert (Hlt : (2 ^ (8 * Z.of_nat n) <= 2 ^ 64)%Z) by (apply Z.pow_le_mono_r; lia).
  rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z.mod_small by lia.
  rewrite <- Hl. apply Z_to_le_bytes_lez.
Qed.

Lemma kread_rdn : forall E M kn b k n v,
  know_ok segs E M kn -> kread kn b k n = Some v -> (1 <= n)%nat -> (n <= 8)%nat ->
  flat E (SA b k) (Z.of_nat n) ->
  rdn segs M (adenot E (SA b k)) n = Some (word_to_le_bytes n (edenot E v)).
Proof.
  intros E M kn b k n v Hkn Hr Hn1 Hn8 Hfl.
  destruct (kread_sound E M kn b k n v Hkn Hr Hn1 Hn8 Hfl) as (bs & A & B & C).
  rewrite A, <- C, word_to_le_bytes_of_lez by assumption. reflexivity.
Qed.

Fixpoint kblob_find (kn : list kentry) (b : expr) (k : Z) : option (expr * nat) :=
  match kn with
  | [] => None
  | KBlob (SA kb kk) len bk :: rest =>
      if (expr_eqb b kb && Z.eqb k kk)%bool then Some (len, bk) else kblob_find rest b k
  | _ :: rest => kblob_find rest b k
  end.

Definition junk_vals (R' : bvmap 5 word) : list word :=
  map (fun i => getr R' (Z_to_bv 5 (Z.of_nat i))) (seq 0 32).

Definition sr_after_call_j (sr : list expr) (kept : list nat) (jbase : N) : list expr :=
  map (fun i => if existsb (Nat.eqb i) kept then nth i sr (ELit 0) else EVar (jbase + N.of_nat i))
      (seq 0 32).

Lemma nth_map_seq_gen : forall {A} (f : nat -> A) len s n d, (n < len)%nat ->
  nth n (map f (seq s len)) d = f (s + n)%nat.
Proof.
  intros A f len. induction len as [|len IH]; intros s n d H; [lia|].
  cbn [seq map]. destruct n as [|n].
  - cbn [nth]. rewrite Nat.add_0_r. reflexivity.
  - cbn [nth]. rewrite IH by lia. f_equal. lia.
Qed.

Lemma nth_map_seq : forall {A} (f : nat -> A) n len d, (n < len)%nat ->
  nth n (map f (seq 0 len)) d = f n.
Proof. intros. rewrite nth_map_seq_gen by assumption. reflexivity. Qed.

Lemma sr_vars_lt_nth : forall b sr n, sr_vars_lt b sr = true -> expr_vars_lt b (nth n sr (ELit 0)) = true.
Proof.
  intros b sr. induction sr as [|e t IH]; intros n H; [destruct n; reflexivity|].
  cbn [sr_vars_lt] in H. apply andb_prop in H as [He Ht]. destruct n; [exact He | apply IH; exact Ht].
Qed.

Lemma regs_after_call : forall vals ebs sr R R' kept,
  sr_vars_lt (N.of_nat (length vals)) sr = true ->
  regs_ok (Env (vals_ev vals) ebs) sr R ->
  (forall i, In i kept -> (i < 32)%nat /\ getr R' (Z_to_bv 5 (Z.of_nat i)) = getr R (Z_to_bv 5 (Z.of_nat i))) ->
  ~ In 0%nat kept ->
  regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sr_after_call_j sr kept (N.of_nat (length vals))) R'.
Proof.
  intros vals ebs sr R R' kept Hlt HR Hkept H0 r.
  pose proof (ridx_range r) as Hr.
  unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. reflexivity.
  - unfold sr_after_call_j. rewrite nth_map_seq by exact Hr.
    destruct (existsb (Nat.eqb (ridx r)) kept) eqn:Hex.
    + apply existsb_exists in Hex as (i & Hin & Heqi). apply Nat.eqb_eq in Heqi. subst i.
      destruct (Hkept _ Hin) as [_ Hg]. rewrite ridx_roundtrip in Hg. rewrite Hg.
      pose proof (HR r) as Hv. unfold sr_get in Hv. rewrite Hr0 in Hv. rewrite Hv.
      eapply edenot_agree; [apply vals_app_agree|]. apply sr_vars_lt_nth. exact Hlt.
    + cbn [edenot ev]. unfold vals_ev. rewrite app_nth2 by lia.
      replace (N.to_nat (N.of_nat (length vals) + N.of_nat (ridx r)) - length vals)%nat with (ridx r) by lia.
      unfold junk_vals. rewrite nth_map_seq by exact Hr. rewrite ridx_roundtrip. reflexivity.
Qed.

End Drive.
