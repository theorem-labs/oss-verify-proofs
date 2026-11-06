(* Modified by Theorem Labs, 2026-10: copied from lib/A/Prog/CwcText.v for fuzz_command.asan-ubsan: module paths, the two literals' names. *)
(* The text check_words_chain builds, as lists: the list-level facts its ASan walk reads.

   check_words_chain (fuzz_command.c:356-371) writes, into its 769-byte array list, the "%d" text of the atoi wrapper's
   value of each word k from 2 to read-1, with the format "%d" at k = 2 and " %d" after it, each through one snprintf
   call that starts where the text before it ends. The contract states the result with chain_list_at
   (lib/B/Prog/HarnessPropsA.v:48-55); the snprintf contract (lib/B/Rt/RtFormat.v:72-88) states one call's text with
   the released printf model pf_parse, pf_text, pf_dec and pf_bytes (lib/Prog/printf_facts_c.v:10-91) and leaves
   firstn (Z.to_nat (n - 1)) T ++ [0] in the buffer.

   This file is stated over those released definitions only. It proves the text of the two format literals
   (RO_lit_218e0 "%d" and RO_lit_21b80 " %d", lib/B/Prog/CmdRo.v:71,92), the length and byte range of pf_dec, the
   step and the prefix form of chain_items_at that the loop invariant reads, the length bound that keeps every call
   inside the array and uncut, and the list facts of pf_bytes that read the buffer back. It proves no function's
   contract. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import HarnessPropsA.
Import ListNotations.
Open Scope Z_scope.

(** * The text of one format *)

Lemma pf_parse_d : pf_parse [37; 100] = Some [Pd].
Proof. reflexivity. Qed.

Lemma pf_parse_spd : pf_parse [32; 37; 100] = Some [PLit 32; Pd].
Proof. reflexivity. Qed.

(* "%d" and " %d" with one int argument *)
Lemma pf_text_d : forall v, pf_parse [37; 100] = Some [Pd] /\ pf_text [Pd] [AInt v] = Some (pf_dec v).
Proof. intros v. split; [reflexivity|]. cbn [pf_text option_map]. rewrite app_nil_r. reflexivity. Qed.

Lemma pf_text_spd : forall v,
  pf_parse [32; 37; 100] = Some [PLit 32; Pd] /\ pf_text [PLit 32; Pd] [AInt v] = Some (32 :: pf_dec v).
Proof. intros v. split; [reflexivity|]. cbn [pf_text option_map]. rewrite app_nil_r. reflexivity. Qed.

(** * pf_dec *)

Lemma pf_digits_len : forall f x acc j, 0 <= x < 10 ^ Z.of_nat j -> (1 <= j)%nat ->
  (length (pf_digits f x acc) <= j + length acc)%nat.
Proof.
  induction f as [|f IH]; intros x acc j Hx Hj; cbn [pf_digits]; [lia|].
  destruct (Z.ltb_spec x 10) as [L|L].
  - cbn [length]. lia.
  - destruct j as [|[|j]]; [lia| |].
    + exfalso. assert (E : 10 ^ Z.of_nat 1 = 10) by reflexivity. lia.
    + assert (B : 0 <= x / 10 < 10 ^ Z.of_nat (S j)).
      { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
        replace (Z.of_nat (S (S j))) with (Z.of_nat (S j) + 1) in Hx by lia.
        rewrite Z.pow_add_r, Z.pow_1_r in Hx by lia. lia. }
      specialize (IH (x / 10) ((48 + x mod 10) :: acc) (S j) B ltac:(lia)).
      cbn [length] in IH. lia.
Qed.

Lemma pf_dec_len : forall v, -2^31 <= v < 2^31 -> (length (pf_dec v) <= 11)%nat.
Proof.
  intros v Hv. unfold pf_dec.
  assert (E : 10 ^ Z.of_nat 10 = 10000000000) by reflexivity.
  destruct (Z.ltb_spec v 0).
  - pose proof (pf_digits_len 11 (- v) [] 10 ltac:(lia) ltac:(lia)) as HL. cbn [length] in *. lia.
  - pose proof (pf_digits_len 11 v [] 10 ltac:(lia) ltac:(lia)) as HL. cbn [length] in *. lia.
Qed.

Lemma pf_digits_nonnil : forall f x acc, acc <> [] -> pf_digits f x acc <> [].
Proof.
  induction f as [|f IH]; intros x acc Ha; cbn [pf_digits]; [exact Ha|].
  destruct (x <? 10); [discriminate | apply IH; discriminate].
Qed.

Lemma pf_digits_S_nonnil : forall f x acc, pf_digits (S f) x acc <> [].
Proof.
  intros f x acc. cbn [pf_digits]. destruct (x <? 10); [discriminate | apply pf_digits_nonnil; discriminate].
Qed.

Lemma pf_dec_nonnil : forall v, pf_dec v <> [].
Proof. intros v. unfold pf_dec. destruct (v <? 0); [discriminate | apply pf_digits_S_nonnil]. Qed.

(* every byte of the text is a nonzero byte, so the text holds no terminator *)
Lemma pf_digits_nz : forall f x acc, 0 <= x -> Forall (fun c => 0 < c < 256) acc ->
  Forall (fun c => 0 < c < 256) (pf_digits f x acc).
Proof.
  induction f as [|f IH]; intros x acc Hx Ha; cbn [pf_digits]; [exact Ha|].
  destruct (Z.ltb_spec x 10).
  - constructor; [cbv beta; lia | exact Ha].
  - apply IH; [apply Z.div_pos; lia|]. constructor; [|exact Ha].
    pose proof (Z.mod_pos_bound x 10 ltac:(lia)). cbv beta. lia.
Qed.

Lemma pf_dec_nz : forall v, Forall (fun c => 0 < c < 256) (pf_dec v).
Proof.
  intros v. unfold pf_dec. destruct (Z.ltb_spec v 0).
  - constructor; [cbv beta; lia|]. apply pf_digits_nz; [lia | constructor].
  - apply pf_digits_nz; [lia | constructor].
Qed.

(** * The loop's items *)

(* the text of the call at word k: a space before every item after the first, then the number *)
Definition ci_text (atoi : list byte -> Z) (k : nat) (ws : list (list byte)) : list Z :=
  (if Nat.eqb k 2 then [] else [32]) ++ pf_dec (atoi (nth k ws [])).

(* the format of the call at word k, its pieces, and the text it produces *)
Definition ci_fmt (k : nat) : list Z := if Nat.eqb k 2 then [37; 100] else [32; 37; 100].
Definition ci_ps (k : nat) : list pf_piece := if Nat.eqb k 2 then [Pd] else [PLit 32; Pd].

Lemma pf_text_ci : forall atoi k ws,
  pf_parse (ci_fmt k) = Some (ci_ps k) /\
  pf_text (ci_ps k) [AInt (atoi (nth k ws []))] = Some (ci_text atoi k ws).
Proof.
  intros atoi k ws. unfold ci_fmt, ci_ps, ci_text. destruct (Nat.eqb k 2).
  - apply pf_text_d.
  - apply pf_text_spd.
Qed.

Lemma chain_items_at_step : forall atoi k n ws,
  chain_items_at atoi k (S n) ws = ci_text atoi k ws ++ chain_items_at atoi (S k) n ws.
Proof. intros atoi k n ws. cbn [chain_items_at]. unfold ci_text. rewrite <- app_assoc. reflexivity. Qed.

Lemma chain_items_at_app : forall atoi k n m ws,
  chain_items_at atoi k (n + m) ws = chain_items_at atoi k n ws ++ chain_items_at atoi (k + n) m ws.
Proof.
  intros atoi k n m ws. revert k. induction n as [|n IH]; intros k.
  - rewrite Nat.add_0_r. reflexivity.
  - change (S n + m)%nat with (S (n + m)).
    rewrite !chain_items_at_step, IH, app_assoc.
    replace (S k + n)%nat with (k + S n)%nat by lia. reflexivity.
Qed.

Lemma chain_items_at_snoc : forall atoi k n ws,
  chain_items_at atoi k (S n) ws = chain_items_at atoi k n ws ++ ci_text atoi (k + n) ws.
Proof.
  intros atoi k n ws. rewrite <- Nat.add_1_r, chain_items_at_app, chain_items_at_step.
  cbn [chain_items_at]. rewrite app_nil_r. reflexivity.
Qed.

Lemma ci_text_len : forall atoi k ws, (length (pf_dec (atoi (nth k ws []))) <= 11)%nat ->
  (length (ci_text atoi k ws) <= 12)%nat.
Proof. intros atoi k ws H. unfold ci_text. rewrite length_app. destruct (Nat.eqb k 2); cbn [length]; lia. Qed.

Lemma chain_items_at_len : forall atoi k n ws,
  (forall j, (length (pf_dec (atoi (nth j ws []))) <= 11)%nat) ->
  (length (chain_items_at atoi k n ws) <= 12 * n)%nat.
Proof.
  intros atoi k n ws H. revert k. induction n as [|n IH]; intros k; [cbn; lia|].
  rewrite chain_items_at_step, length_app. pose proof (ci_text_len atoi k ws (H k)). specialize (IH (S k)). lia.
Qed.

Lemma chain_list_at_len : forall atoi r ws,
  (forall j, (length (pf_dec (atoi (nth j ws []))) <= 11)%nat) -> 0 <= r <= 64 ->
  (length (chain_list_at atoi r ws) <= 12 * Z.to_nat (r - 2))%nat.
Proof. intros atoi r ws H _. unfold chain_list_at. apply chain_items_at_len. exact H. Qed.

Lemma ci_text_nz : forall atoi k ws, Forall (fun c => 0 < c < 256) (ci_text atoi k ws).
Proof.
  intros atoi k ws. unfold ci_text. apply Forall_app. split; [|apply pf_dec_nz].
  destruct (Nat.eqb k 2); repeat constructor; lia.
Qed.

Lemma chain_items_at_nz : forall atoi k n ws, Forall (fun c => 0 < c < 256) (chain_items_at atoi k n ws).
Proof.
  intros atoi k n ws. revert k. induction n as [|n IH]; intros k; [constructor|].
  rewrite chain_items_at_step. apply Forall_app. split; [apply ci_text_nz | apply IH].
Qed.

Lemma chain_list_at_nz : forall atoi r ws, Forall (fun c => 0 < c < 256) (chain_list_at atoi r ws).
Proof. intros atoi r ws. apply chain_items_at_nz. Qed.

(** * The text snprintf leaves *)

(* a text shorter than the room is not cut *)
Lemma firstn_all_text : forall (T : list Z) n, (Z.of_nat (length T) < n)%Z -> firstn (Z.to_nat (n - 1)) T = T.
Proof. intros T n H. apply firstn_all2. lia. Qed.

(** * pf_bytes *)

Lemma pf_bytes_app : forall a b, pf_bytes (a ++ b) = pf_bytes a ++ pf_bytes b.
Proof. intros a b. unfold pf_bytes. apply map_app. Qed.

Lemma pf_bytes_len : forall l, length (pf_bytes l) = length l.
Proof. intros l. unfold pf_bytes. apply length_map. Qed.

Lemma pf_bytes_nul : forall l, pf_bytes (l ++ [0]) = pf_bytes l ++ [Z_to_bv 8 0].
Proof. intros l. unfold pf_bytes. rewrite map_app. reflexivity. Qed.

Lemma pf_bytes_unsigned : forall l, Forall (fun c => 0 <= c < 256) l -> map bv_unsigned (pf_bytes l) = l.
Proof.
  intros l H. unfold pf_bytes. rewrite map_map. transitivity (map (fun c => c) l); [|apply map_id].
  apply map_ext_in. intros c Hc. rewrite Forall_forall in H. specialize (H c Hc).
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact H.
Qed.

(* pf_bytes is injective on lists of bytes below 256 *)
Lemma pf_bytes_inj : forall a b, Forall (fun c => 0 <= c < 256) a -> Forall (fun c => 0 <= c < 256) b ->
  pf_bytes a = pf_bytes b -> a = b.
Proof.
  intros a b Ha Hb E.
  rewrite <- (pf_bytes_unsigned a Ha), <- (pf_bytes_unsigned b Hb), E. reflexivity.
Qed.

Lemma nz_bytes : forall l, Forall (fun c => 0 < c < 256) l -> Forall (fun c => 0 <= c < 256) l.
Proof. intros l H. eapply Forall_impl; [|exact H]. intros c Hc. cbv beta in Hc |- *. lia. Qed.
