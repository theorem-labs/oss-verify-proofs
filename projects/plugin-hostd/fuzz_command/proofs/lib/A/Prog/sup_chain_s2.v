(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the text model of sup_chain's loop for its ASan walk (plugin-hostd/fuzz_command,
   0x8c2b4), in the style of lib/Prog/RecFacts.v (digits_S, dec_length, dec_no0): the two formats it hands to
   sprintf ("%d" at 0x21f00 and " %d" at 0x21ee0) as lists of lib/Prog/printf_facts_c.v, their pieces and text;
   the bridge from musl's decimal printer pf_dec to the recorder model's dec; and the recursion, lengths and
   no-NUL property of dec_list (lib/Prog/RecModel.v) over the prefixes the loop has printed. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRo.
Import ListNotations.
Open Scope Z_scope.

Module PF := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.printf_facts_c.

(* The formats: sup_chain prints member k with sprintf(list + o, k ? " %d" : "%d", ids[k]). *)
Definition sc_fmt0 : list Z := [37; 100].
Definition sc_fmt1 : list Z := [32; 37; 100].

Lemma sc_fmt0_bytes : PF.pf_bytes sc_fmt0 ++ [Z_to_bv 8 0] = RO_lit_21f00.
Proof. reflexivity. Qed.

Lemma sc_fmt1_bytes : PF.pf_bytes sc_fmt1 ++ [Z_to_bv 8 0] = RO_lit_21ee0.
Proof. reflexivity. Qed.

Lemma sc_fmt0_parse : PF.pf_parse sc_fmt0 = Some [PF.Pd].
Proof. reflexivity. Qed.

Lemma sc_fmt1_parse : PF.pf_parse sc_fmt1 = Some [PF.PLit 32; PF.Pd].
Proof. reflexivity. Qed.

Lemma sc_fmt0_text : forall v, PF.pf_text [PF.Pd] [PF.AInt v] = Some (PF.pf_dec v).
Proof.
  intros v. change (Some (PF.pf_dec v ++ []) = Some (PF.pf_dec v)). rewrite app_nil_r. reflexivity.
Qed.

Lemma sc_fmt1_text : forall v, PF.pf_text [PF.PLit 32; PF.Pd] [PF.AInt v] = Some (32 :: PF.pf_dec v).
Proof.
  intros v. change (Some (32 :: (PF.pf_dec v ++ [])) = Some (32 :: PF.pf_dec v)). rewrite app_nil_r. reflexivity.
Qed.

(* musl's digit loop and the model's digit loop are the same recursion over the same fuel. *)
Lemma sc_pf_digits_bytes : forall f x acc,
  PF.pf_bytes (PF.pf_digits f x acc) = digits f x (PF.pf_bytes acc).
Proof.
  induction f as [|f IH]; intros x acc; cbn [PF.pf_digits digits]; [reflexivity|].
  destruct (x <? 10); [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma sc_pf_digits_bytes0 : forall f x, PF.pf_bytes (PF.pf_digits f x []) = digits f x [].
Proof. intros f x. exact (sc_pf_digits_bytes f x []). Qed.

(* One more unit of fuel changes nothing once the fuel covers every digit. *)
Lemma sc_digits_fuel : forall k n acc, 0 <= n < 10 ^ Z.of_nat (S k) ->
  digits (S (S k)) n acc = digits (S k) n acc.
Proof.
  induction k as [|k IH]; intros n acc Hn.
  - cbn [digits]. destruct (Z.ltb_spec n 10) as [H|H]; [reflexivity|].
    change (10 ^ Z.of_nat 1) with 10 in Hn. lia.
  - rewrite (digits_S (S (S k)) n acc), (digits_S (S k) n acc).
    destruct (Z.ltb_spec n 10) as [H|H]; [reflexivity|].
    apply IH.
    replace (10 ^ Z.of_nat (S (S k))) with (10 * 10 ^ Z.of_nat (S k)) in Hn
      by (rewrite (Nat2Z.inj_succ (S k)), Z.pow_succ_r by lia; ring).
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma sc_dec_bridge : forall v, -2^31 <= v < 2^31 -> PF.pf_bytes (PF.pf_dec v) = dec v.
Proof.
  intros v Hv. unfold PF.pf_dec, dec.
  assert (Ha : 0 <= Z.abs v < 10 ^ Z.of_nat (S 9)) by (change (10 ^ Z.of_nat (S 9)) with 10000000000; lia).
  destruct (Z.ltb_spec v 0) as [H|H].
  - replace (- v) with (Z.abs v) by lia.
    change (PF.pf_bytes (45 :: PF.pf_digits 11 (Z.abs v) []))
      with (Z_to_bv 8 45 :: PF.pf_bytes (PF.pf_digits 11 (Z.abs v) [])).
    rewrite sc_pf_digits_bytes0, (sc_digits_fuel 9 (Z.abs v) [] Ha). reflexivity.
  - rewrite (Z.abs_eq v H) in Ha |- *.
    rewrite sc_pf_digits_bytes0, (sc_digits_fuel 9 v [] Ha). reflexivity.
Qed.

Lemma sc_fmt1_text_bytes : forall v, -2^31 <= v < 2^31 -> PF.pf_bytes (32 :: PF.pf_dec v) = SPACE :: dec v.
Proof.
  intros v Hv. change (PF.pf_bytes (32 :: PF.pf_dec v)) with (Z_to_bv 8 32 :: PF.pf_bytes (PF.pf_dec v)).
  rewrite (sc_dec_bridge v Hv). reflexivity.
Qed.

(* The format, its pieces and the bytes of its text, for the member at index k. *)
Lemma sc_fmt_bytes : forall k : nat,
  PF.pf_bytes (if Nat.eqb k 0 then sc_fmt0 else sc_fmt1) ++ [Z_to_bv 8 0]
  = if Nat.eqb k 0 then RO_lit_21f00 else RO_lit_21ee0.
Proof. intros k. destruct (Nat.eqb k 0); [exact sc_fmt0_bytes | exact sc_fmt1_bytes]. Qed.

Lemma sc_fmt_text : forall (k : nat) v, -2^31 <= v < 2^31 ->
  exists ps t, PF.pf_parse (if Nat.eqb k 0 then sc_fmt0 else sc_fmt1) = Some ps
    /\ PF.pf_text ps [PF.AInt v] = Some t
    /\ PF.pf_bytes t = (if Nat.eqb k 0 then dec v else SPACE :: dec v).
Proof.
  intros k v Hv. destruct (Nat.eqb k 0).
  - exists [PF.Pd], (PF.pf_dec v). split; [exact sc_fmt0_parse|]. split; [apply sc_fmt0_text|].
    exact (sc_dec_bridge v Hv).
  - exists [PF.PLit 32; PF.Pd], (32 :: PF.pf_dec v). split; [exact sc_fmt1_parse|]. split; [apply sc_fmt1_text|].
    exact (sc_fmt1_text_bytes v Hv).
Qed.

(* The loop's text: dec_list over the prefixes of ids. *)
Lemma sc_dec_list_nil : dec_list [] = [].
Proof. reflexivity. Qed.

Lemma sc_dec_list_snoc : forall l v,
  dec_list (l ++ [v]) = dec_list l ++ (match l with [] => dec v | _ :: _ => SPACE :: dec v end).
Proof.
  intros [|i r] v.
  - exact (app_nil_r (dec v)).
  - change (dec i ++ concat (map (fun j => SPACE :: dec j) (r ++ [v])) =
            (dec i ++ concat (map (fun j => SPACE :: dec j) r)) ++ SPACE :: dec v).
    rewrite <- (app_assoc (dec i)). f_equal.
    rewrite map_app, concat_app. f_equal.
    exact (app_nil_r (SPACE :: dec v)).
Qed.

Lemma sc_firstn_snoc : forall (A : Type) (l : list A) k v, nth_error l k = Some v ->
  firstn (S k) l = firstn k l ++ [v].
Proof.
  intros A l. induction l as [|a l IH]; intros k v H.
  - destruct k; cbn [nth_error] in H; discriminate H.
  - destruct k as [|k].
    + cbn [nth_error] in H. injection H as E. subst. reflexivity.
    + change (a :: firstn (S k) l = a :: (firstn k l ++ [v])). rewrite (IH k v H). reflexivity.
Qed.

Lemma sc_firstn_len : forall (A : Type) (l : list A) k, (k <= length l)%nat -> length (firstn k l) = k.
Proof.
  intros A l. induction l as [|a l IH]; intros [|k] H; cbn [firstn length] in *; try reflexivity; try lia.
  rewrite IH by lia. reflexivity.
Qed.

Lemma sc_Forall_firstn : forall (A : Type) (P : A -> Prop) (l : list A) k, Forall P l -> Forall P (firstn k l).
Proof.
  intros A P l. induction l as [|a l IH]; intros [|k] H; cbn [firstn]; try constructor.
  - exact (Forall_inv H).
  - apply IH. exact (Forall_inv_tail H).
Qed.

Lemma sc_dec_list_step : forall ids k v, nth_error ids k = Some v ->
  dec_list (firstn (S k) ids) = dec_list (firstn k ids) ++ (if Nat.eqb k 0 then dec v else SPACE :: dec v).
Proof.
  intros ids k v H. rewrite (sc_firstn_snoc _ ids k v H), sc_dec_list_snoc.
  destruct k as [|k]; [reflexivity|].
  destruct ids as [|a ids']; [cbn [nth_error] in H; discriminate H | reflexivity].
Qed.

(* No NUL byte: the text can be handed to xstrdup whole. *)
Lemma sc_space_dec_no0 : forall j, no0 (SPACE :: dec j).
Proof.
  intros j. change (SPACE :: dec j) with ([SPACE] ++ dec j). apply no0_app; [|apply dec_no0].
  apply no0_forall. apply Forall_cons; [|apply Forall_nil]. unfold SPACE. rewrite byte_unsigned by lia. lia.
Qed.

Lemma sc_concat_no0 : forall r, no0 (concat (map (fun j => SPACE :: dec j) r)).
Proof.
  induction r as [|j r IH]; [intros H; exact H|].
  change (no0 ((SPACE :: dec j) ++ concat (map (fun j => SPACE :: dec j) r))).
  apply no0_app; [apply sc_space_dec_no0 | exact IH].
Qed.

Lemma sc_dec_list_nz : forall ids, ~ In (Z_to_bv 8 0) (dec_list ids).
Proof.
  intros [|i r]; [intros H; exact H|].
  change (no0 (dec i ++ concat (map (fun j => SPACE :: dec j) r))).
  apply no0_app; [apply dec_no0 | apply sc_concat_no0].
Qed.

(* Lengths: each member takes at most 11 bytes plus one separator, so n members fit 12n - 1 bytes. *)
Lemma sc_concat_len : forall r, Forall (fun v => -2^31 <= v < 2^31) r ->
  Z.of_nat (length (concat (map (fun j => SPACE :: dec j) r))) <= 12 * Z.of_nat (length r).
Proof.
  induction r as [|j r IH]; intros HF; [cbn [map concat length]; lia|].
  change (concat (map (fun j => SPACE :: dec j) (j :: r)))
    with ((SPACE :: dec j) ++ concat (map (fun j => SPACE :: dec j) r)).
  rewrite length_app. cbn [length].
  pose proof (dec_length j (Forall_inv HF)). specialize (IH (Forall_inv_tail HF)). lia.
Qed.

Lemma sc_dec_list_len : forall ids, Forall (fun v => -2^31 <= v < 2^31) ids -> (1 <= length ids)%nat ->
  Z.of_nat (length (dec_list ids)) <= 12 * Z.of_nat (length ids) - 1.
Proof.
  intros [|i r] HF Hn; [cbn [length] in Hn; lia|].
  change (dec_list (i :: r)) with (dec i ++ concat (map (fun j => SPACE :: dec j) r)).
  rewrite length_app. cbn [length].
  pose proof (dec_length i (Forall_inv HF)). pose proof (sc_concat_len r (Forall_inv_tail HF)). lia.
Qed.

Lemma sc_dec_list_prefix_len : forall ids k, Forall (fun v => -2^31 <= v < 2^31) ids -> (k <= length ids)%nat ->
  Z.of_nat (length (dec_list (firstn k ids))) <= 12 * Z.of_nat k.
Proof.
  intros ids [|k] HF Hk; [exact (Z.le_refl 0)|].
  pose proof (sc_firstn_len _ ids (S k) Hk) as Hl.
  pose proof (sc_dec_list_len (firstn (S k) ids) (sc_Forall_firstn _ _ ids (S k) HF) ltac:(lia)) as E.
  lia.
Qed.
