(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase StackLayout State Run Fs.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Cli Require Import CliVerdict.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLin AxSys AxEntryRel AsanWEb.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxEntryS AxEntryFacts AxFd.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma map_nth_seq0 {A : Type} (l : list A) (d : A) : map (fun k => nth k l d) (seq 0 (length l)) = l.
Proof.
  induction l as [|x r IH]; [reflexivity|]. cbn [length seq map nth]. f_equal.
  rewrite <- seq_shift, map_map. exact IH.
Qed.

(* [comment removed for export] *)
Lemma dec_str_enc (inp : ProcInput) (sp brk0 : word) (draw : EntryDraw) (k : Z) :
  valid_input inp -> 0 <= k < 1048576 -> dec_str k (enc_b inp sp draw brk0) = nth (Z.to_nat k) (in_argv inp) [].
Proof.
  intros Hinp Hk. unfold dec_str. rewrite (proj2 (Z.leb_le 0 k)) by lia. rewrite (proj2 (Z.ltb_lt k 1048576)) by lia. cbn [andb].
  unfold enc_b. rewrite (enc_lenvar inp sp draw _ k ltac:(lia)).
  set (a := nth (Z.to_nat k) (in_argv inp) []).
  assert (Hlen : Z.of_nat (length a) <= 131071).
  { destruct Hinp as ((_ & _ & Hl & _) & _). destruct (Nat.lt_ge_cases (Z.to_nat k) (length (in_argv inp))) as [L|L].
    - rewrite Forall_forall in Hl. exact (Hl a (nth_In _ _ L)).
    - unfold a. rewrite nth_overflow by exact L. cbn. lia. }
  rewrite Z.mod_small by lia. rewrite Nat2Z.id.
  rewrite <- (map_nth_seq0 a (Z_to_bv 8 0)) at 2. apply map_ext_in. intros j Hj. apply in_seq in Hj.
  rewrite (enc_strvar inp sp draw _ k (Z.of_nat j) ltac:(lia) ltac:(lia)). rewrite Nat2Z.id. fold a. apply Z_to_bv_bv_unsigned.
Qed.

Lemma dec_argvB_enc (inp : ProcInput) (sp brk0 : word) (draw : EntryDraw) :
  valid_input inp -> dec_argvB (enc_b inp sp draw brk0) = in_argv inp.
Proof.
  intros Hinp. unfold dec_argvB. pose proof Hinp as ((HA & _) & _).
  assert (Ec : enc_b inp sp draw brk0 v_argc = Z.of_nat (length (in_argv inp))) by reflexivity.
  rewrite Ec. rewrite Z.mod_small by lia. rewrite Nat2Z.id.
  rewrite <- (map_nth_seq0 (in_argv inp) []) at 2.
  apply map_ext_in. intros k Hk. apply in_seq in Hk.
  rewrite (dec_str_enc inp sp brk0 draw (Z.of_nat k) Hinp ltac:(lia)). rewrite Nat2Z.id. reflexivity.
Qed.

Lemma V_ne2 (argv : list (list byte)) (fs : Fs) : length argv <> 2%nat -> V argv fs = true.
Proof. intros H. destruct argv as [|a [|b [|c r]]]; try reflexivity. cbn in H. lia. Qed.

(* [comment removed for export] *)
Lemma good_inp_enc (inp : ProcInput) (sp brk0 : word) (draw : EntryDraw) :
  valid_input inp -> good_inp (in_fs inp) (enc_b inp sp draw brk0).
Proof.
  intros Hinp. unfold good_inp. rewrite (dec_argvB_enc inp sp brk0 draw Hinp). exact (proj1 Hinp).
Qed.
