(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* fr_LS, the concrete live-state invariant LS of the entry walk of fuzz_reply's LLVMFuzzerTestOneInput
   (lib/A/W_LLVMFuzzerTestOneInput_cut.v, the Section variable `LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop`
   that lcut carries at every cut point), and the LS rules that follow from it.

   THE SHAPE IS STRUCTURAL, NOT A METER (a Theorem Labs lane's plan of record, 2026-10-29).  MT stays ameter_triv:
   - at ameter_triv a rule that ties the post-state S' to S only through mo_le cannot be met by any LS that bounds
     live bytes (LS-FINDING.v (sha256 e350965e21c5; internal record), ls_rules_collapse_at_triv);
   - no meter can carry the bound either, because a callee charges the SUM of its grants and fuzz_reply's relay grows
     its held table by one entry per begin (relay.c:106): 17,184,602,328 bytes in one call on a 1.5 MB input
     (METER-FINDING.txt sha256 e56f281c60fb; internal record).
   Instead LS bounds the live blocks through the MODEL:
   - its own split `ablocks B ly S ~ input_blks cx ++ model_blks m ++ rest`, where the entry's bytes pay for the input,
     for rest and for e0 (the bytes of the entry's harness blocks the model holds: g_out's buffer, g_src's table);
     blocks_bytes S = bsum (ablocks B ly S) by definition (Reusable/YCbq.v blocks_bytes_bsum), and every post rule
     keeps rest (its callee post moves the program's blocks only);
   - the entry leaves the call room CALL_ROOM = 2^33 (lib/A/ACfn_cf.v fr_live_pre at its instance);
   - a potential on the model, PHI m = bsum (model_blks m) + W_P * (bytes queued) + W_H * (bytes held) + (vector
     slack), is bounded by MB_K * (input consumed) + APARTIAL * (open sources) + e0 + MB_C.  A write pays for its copy,
     its queued bytes' credit and its record (amortized: a vector at most doubles, the slack 16 * max 0 (2 n - cap)
     pays the doubling) out of the 3 + n input bytes it consumes; op_add pays for its 6,000-byte partial buffer out of
     the source it opens; a drain spends the queued bytes' credit on the lines, records and output it makes, a remove
     / gone spends the held bytes' credit on the ends it writes.  The input is under 2^26 bytes, so the model is under
     65 * 2^26 + 24,000 + 2^26 = 4,429,209,024 bytes above the entry's harness blocks, and every cut point has 2^31
     bytes to spare under LIVE_MAX (fr_LS_room);
   - the pending records number at most a quarter of the input consumed (a write consumes at least 4 bytes), so a
     pending vector is under 2^29 bytes and list_push's growth premise lp_vbytes < WR_MMAX holds.
   t does not appear: every bound is in the input consumed and the open sources, so the rules that run without a
   `t < OPS_MAX` premise (the small arms, the write arm) need none.
   Proved here, each in lib/A/ReplyATop.v's family form at LS := fun fx rc => fr_LS B and checked against its text:
   the seven rules that keep the model's blocks (head_nout, head_skip, close, eintr, sendmax, default, write_skip),
   the three add rules (add_room, add_open, add_none) and write_room; and, at the cf instance (MT := ameter_triv,
   fr_live_pre := ACfn_cf.fr_live_pre), the prologue's LS_pro_oa (fr_LS_pro_oa).  write_push and LS_pro are proved for
   the texts PROPOSED beside them (atop_LS_write_push_prop, fr_LS_pro): as published, write_push leaves the pushed list
   and the post-state free (LS-FINDING.v sha256 e350965e21c5; internal record), and LS_pro gives no entry split for LS's own rest. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_write
W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ACfn_cf.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ------------------------------------------------------------------ the constants *)
Definition MB_K : Z := 65.                       (* per input byte consumed: a write's n + 1 copy and 64 n credit *)
Definition MB_C : Z := 67108864.                 (* 2^26: the first head's g_src table, slack for the constants *)
Definition W_P : Z := 64.                        (* the credit a queued byte carries into the drain *)
Definition W_H : Z := 4.                         (* the credit a held key byte carries into remove / gone *)
Definition ROOM_SPARE : Z := 2147483648.         (* 2^31: what every cut point has to spare under LIVE_MAX *)

(* ------------------------------------------------------------------ the measures of the model *)
Local Notation zsum l := (fold_right Z.add 0 l).
Definition hl_bytes (l : hlist) : Z := zsum (map (fun r : Z * list byte => Z.of_nat (length (snd r))) (hl_recs l)).
Definition vsl (l : hlist) : Z := AREC * Z.max 0 (2 * hl_n l - hl_cap l).
Definition slot_pend (o : option hsrc) : Z :=
  match o with Some h => Z.max 0 (hl_bytes (hs_pending h) - hs_off h) | None => 0 end.
Definition slot_held (o : option hsrc) : Z := match o with Some h => hl_bytes (hs_held h) | None => 0 end.
Definition slot_vsl (o : option hsrc) : Z :=
  match o with Some h => vsl (hs_pending h) + vsl (hs_expected h) + vsl (hs_held h) | None => 0 end.
Definition slot_npend (o : option hsrc) : Z := match o with Some h => hl_n (hs_pending h) | None => 0 end.
Definition slot_open (o : option hsrc) : Z := match o with Some _ => 1 | None => 0 end.
Definition entry_held (e : rentry) : Z :=
  zsum (map (fun k => Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys e)).
Definition pend_bytes (m : lmod) : Z := zsum (map slot_pend (lm_hs m)).
Definition held_bytes (m : lmod) : Z := zsum (map slot_held (lm_hs m)) + zsum (map entry_held (lm_es m)).
Definition vslack (m : lmod) : Z := zsum (map slot_vsl (lm_hs m)).
Definition npend (m : lmod) : Z := zsum (map slot_npend (lm_hs m)).
Section ls.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

Definition PHI (m : lmod) : Z := bsum (model_blks m) + W_P * pend_bytes m + W_H * held_bytes m + vslack m.
Definition kk (cx : lfcx) (m : lmod) : Z := Z.min (lm_k m) (c_n cx).

(* ------------------------------------------------------------------ list and count helpers *)
Lemma zsum_app : forall l1 l2, zsum (l1 ++ l2) = zsum l1 + zsum l2.
Proof. induction l1 as [|a l1 IH]; intros l2; cbn; [lia | rewrite IH; lia]. Qed.
Lemma zsum_map_nonneg : forall {X} (g : X -> Z) l, (forall x, 0 <= g x) -> 0 <= zsum (map g l).
Proof. intros X g l H. induction l as [|a l IH]; cbn; [lia | specialize (H a); lia]. Qed.
Lemma zsum_map_elem : forall {X} (g : X -> Z) l i y, (forall x, 0 <= g x) -> nth_error l i = Some y ->
  g y <= zsum (map g l).
Proof.
  intros X g l. induction l as [|a l IH]; intros i y H Hi; destruct i as [|i]; cbn in Hi; try discriminate.
  - injection Hi as ->. cbn. pose proof (zsum_map_nonneg g l H). lia.
  - cbn. specialize (IH i y H Hi). specialize (H a). lia.
Qed.
Lemma bsum_app : forall l1 l2, bsum (l1 ++ l2) = bsum l1 + bsum l2.
Proof. induction l1 as [|b l1 IH]; intros l2; cbn [app bsum fold_right] in *; unfold bsum in *; cbn; [lia|]. rewrite IH. lia. Qed.
Lemma bsum_perm : forall l l', Permutation l l' -> bsum l = bsum l'.
Proof. intros l l' HP. induction HP; unfold bsum in *; cbn in *; lia. Qed.
Lemma bsum_cons : forall b l, bsum (b :: l) = snd b + bsum l.
Proof. reflexivity. Qed.
Lemma bsum_nil : bsum [] = 0.
Proof. reflexivity. Qed.

Definition zzdec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.
Definition cnt1 (a x : Z * Z) : nat := count_occ zzdec [a] x.
Lemma cnt_cons : forall a l x, count_occ zzdec (a :: l) x = (cnt1 a x + count_occ zzdec l x)%nat.
Proof. intros a l x. unfold cnt1. cbn [count_occ]. destruct (zzdec a x); lia. Qed.
Lemma cnt_nil : forall x, count_occ zzdec [] x = 0%nat.
Proof. reflexivity. Qed.
Ltac cnt_norm := repeat progress (rewrite ?count_occ_app, ?cnt_cons, ?cnt_nil in *).
(* turn every Permutation hypothesis and the goal into counts at one point, then linear arithmetic *)
Ltac perm_lia :=
  repeat match goal with H : Permutation _ _ |- _ =>
    let H' := fresh "Hc" in pose proof (proj1 (Permutation_count_occ zzdec _ _) H) as H'; clear H end;
  apply (proj2 (Permutation_count_occ zzdec _ _)); let x := fresh "x" in intros x;
  repeat match goal with H : forall _ : Z * Z, count_occ _ _ _ = count_occ _ _ _ |- _ => specialize (H x) end;
  cnt_norm; lia.

Lemma set_nth_len : forall {A} i (x : A) l, length (set_nth i x l) = length l.
Proof. intros A i. induction i as [|i IH]; intros x [|y l]; cbn; try reflexivity; rewrite IH; reflexivity. Qed.
Lemma ad_set_nth_eq : forall {A} i (x : A) l, ad_set_nth i x l = set_nth i x l.
Proof. intros A i. induction i as [|i IH]; intros x [|y l]; cbn; try reflexivity; rewrite IH; reflexivity. Qed.
Lemma set_nth_perm : forall {A} (f : A -> list (Z * Z)) i x y l, nth_error l i = Some y ->
  Permutation (concat (map f (set_nth i x l)) ++ f y) (concat (map f l) ++ f x).
Proof.
  intros A f i. induction i as [|i IH]; intros x y [|z l] H; cbn in H; try discriminate.
  - injection H as ->. cbn [set_nth map concat]. perm_lia.
  - cbn [set_nth map concat]. rewrite <- !app_assoc. apply Permutation_app_head. exact (IH x y l H).
Qed.
Lemma set_nth_zsum : forall {A} (g : A -> Z) i x y l, nth_error l i = Some y ->
  zsum (map g (set_nth i x l)) + g y = zsum (map g l) + g x.
Proof.
  intros A g i. induction i as [|i IH]; intros x y [|z l] H; cbn in H; try discriminate.
  - injection H as ->. cbn. lia.
  - cbn. specialize (IH x y l H). lia.
Qed.
Lemma upd_hs_map : forall {X : Type} (g : option hsrc -> X) i f l, (forall h, g (Some (f h)) = g (Some h)) ->
  map g (upd_hs i f l) = map g l.
Proof.
  intros X g. induction i as [|i IH]; intros f l Hf.
  - destruct l as [|[h|] l']; [reflexivity | | reflexivity]. cbn [upd_hs map]. rewrite Hf. reflexivity.
  - destruct l as [|x l']; [reflexivity|]. cbn [upd_hs map]. rewrite (IH f l' Hf). reflexivity.
Qed.
Lemma upd_hs_len : forall i f l, length (upd_hs i f l) = length l.
Proof.
  intros i f l. rewrite <- (length_map (fun _ : option hsrc => tt) (upd_hs i f l)), <- (length_map (fun _ : option hsrc => tt) l).
  f_equal. apply upd_hs_map. reflexivity.
Qed.
Lemma nth_some_error : forall (hs : list (option hsrc)) i h, nth i hs None = Some h -> nth_error hs i = Some (Some h).
Proof.
  intros hs i h H. destruct (Nat.lt_ge_cases i (length hs)) as [Hl|Hl].
  - rewrite (nth_error_nth' hs None Hl). rewrite H. reflexivity.
  - rewrite (nth_overflow hs None Hl) in H. discriminate.
Qed.
Lemma oa_first_free : forall hs i, length hs = 4%nat -> oa_first (ad_os hs) = Some i ->
  (i < 4)%nat /\ nth_error hs i = Some None.
Proof.
  intros hs i Hl H. destruct hs as [|a [|b [|c [|d [|e hs']]]]]; cbn in Hl; try discriminate.
  destruct a, b, c, d; cbn in H; try discriminate; injection H as <-; split; first [lia | reflexivity].
Qed.

(* the measures are nonnegative and nopen is a sum *)
Lemma hl_bytes_nonneg : forall l, 0 <= hl_bytes l.
Proof. intros l. unfold hl_bytes. apply zsum_map_nonneg. intros r. lia. Qed.
Lemma slot_pend_nonneg : forall o, 0 <= slot_pend o.
Proof. intros [h|]; cbn; lia. Qed.
Lemma slot_held_nonneg : forall o, 0 <= slot_held o.
Proof. intros [h|]; cbn; [apply hl_bytes_nonneg | lia]. Qed.
Lemma slot_vsl_nonneg : forall o, 0 <= slot_vsl o.
Proof. intros [h|]; cbn; unfold vsl, AREC; lia. Qed.
Lemma slot_npend_nonneg : forall o, 0 <= slot_npend o.
Proof. intros [h|]; cbn; unfold hl_n; lia. Qed.
Lemma entry_held_nonneg : forall e, 0 <= entry_held e.
Proof. intros e. unfold entry_held. apply zsum_map_nonneg. intros k. lia. Qed.
Lemma nopen_zsum : forall hs, nopen hs = zsum (map slot_open hs).
Proof.
  unfold nopen. induction hs as [|o hs IH]; [reflexivity|].
  destruct o; cbn [List.filter length map fold_right slot_open]; lia.
Qed.
Lemma nopen_le4 : forall hs, length hs = 4%nat -> nopen hs <= 4.
Proof.
  intros hs Hl. rewrite nopen_zsum. destruct hs as [|a [|b [|c [|d [|e hs']]]]]; cbn in Hl; try discriminate.
  destruct a, b, c, d; cbn; lia.
Qed.
Lemma PHI_ge : forall m, bsum (model_blks m) <= PHI m.
Proof.
  intros m. unfold PHI, pend_bytes, held_bytes, vslack, W_P, W_H.
  pose proof (zsum_map_nonneg slot_pend (lm_hs m) slot_pend_nonneg).
  pose proof (zsum_map_nonneg slot_held (lm_hs m) slot_held_nonneg).
  pose proof (zsum_map_nonneg entry_held (lm_es m) entry_held_nonneg).
  pose proof (zsum_map_nonneg slot_vsl (lm_hs m) slot_vsl_nonneg). lia.
Qed.
Lemma npend_nonneg : forall m, 0 <= npend m.
Proof. intros m. apply zsum_map_nonneg. exact slot_npend_nonneg. Qed.


(* ------------------------------------------------------------------ LS *)
Definition fr_LS (cx : lfcx) (t : Z) (m : lmod) (ly : alayout) (S : astate) : Prop :=
  exists rest e0,
    Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) /\
    bsum rest + bsum (input_blks cx) + e0 <= blocks_bytes (c_S cx) /\
    blocks_bytes (c_S cx) + ACfn_cf.CALL_ROOM <= LIVE_MAX /\
    0 <= c_n cx < 2 ^ 26 /\ length (lm_hs m) = 4%nat /\
    4 * npend m <= kk cx m /\
    PHI m <= MB_K * kk cx m + APARTIAL * nopen (lm_hs m) + e0 + MB_C.

(* what LS gives at any cut point: the live bytes, with 2^31 to spare under LIVE_MAX *)
Lemma fr_LS_room : forall cx t m ly S, fr_LS cx t m ly S -> blocks_bytes S + ROOM_SPARE <= LIVE_MAX.
Proof.
  intros cx t m ly S (rest & e0 & HP & HR & HE & Hc & Hl & Hnp & HM).
  rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP), !bsum_app.
  pose proof (PHI_ge m). pose proof (nopen_le4 _ Hl). pose proof (npend_nonneg m).
  assert (Hk : kk cx m <= c_n cx) by (unfold kk; lia).
  assert (HC : ACfn_cf.CALL_ROOM = 8589934592) by reflexivity.
  unfold MB_K, MB_C, ROOM_SPARE, APARTIAL in *. lia.
Qed.
(* the input consumed is never negative under LS (the pending records are) *)
Lemma fr_LS_k : forall cx t m ly S, fr_LS cx t m ly S -> 0 <= kk cx m.
Proof. intros cx t m ly S (rest & e0 & _ & _ & _ & _ & _ & Hnp & _). pose proof (npend_nonneg m). lia. Qed.

(* ------------------------------------------------------------------ the rules that keep the model's blocks *)
(* a model with the same blocks and measures and no less input consumed has the same LS (t is free) *)
Lemma fr_LS_keep : forall cx t t' m m' ly S,
  model_blks m' = model_blks m -> PHI m' = PHI m -> nopen (lm_hs m') = nopen (lm_hs m) ->
  length (lm_hs m') = length (lm_hs m) -> npend m' = npend m -> kk cx m <= kk cx m' ->
  fr_LS cx t m ly S -> fr_LS cx t' m' ly S.
Proof.
  intros cx t t' m m' ly S Hb Hp Ho Hl Hn Hk (rest & e0 & HP & HR & HE & Hc & Hl0 & Hnp & HM).
  exists rest, e0. rewrite Hb, Hp, Ho, Hl, Hn. unfold MB_K in *.
  refine (conj HP (conj HR (conj HE (conj Hc (conj Hl0 (conj _ _)))))); lia.
Qed.
(* the measures read lm_hs, lm_es, lm_G, lm_cap and lm_out only *)
Lemma fr_LS_k_only : forall cx t t' m m' ly S,
  lm_hs m' = lm_hs m -> lm_es m' = lm_es m -> lm_G m' = lm_G m -> lm_cap m' = lm_cap m -> lm_out m' = lm_out m ->
  lm_k m <= lm_k m' \/ kk cx m <= kk cx m' -> fr_LS cx t m ly S -> fr_LS cx t' m' ly S.
Proof.
  intros cx t t' m m' ly S E1 E2 E3 E4 E5 Hk H.
  assert (Hb : model_blks m' = model_blks m) by (unfold model_blks; rewrite E1, E2, E3, E4, E5; reflexivity).
  apply (fr_LS_keep cx t t' m m' ly S Hb); [| rewrite E1; reflexivity | rewrite E1; reflexivity
    | unfold npend; rewrite E1; reflexivity | unfold kk in *; lia | exact H].
  unfold PHI, pend_bytes, held_bytes, vslack. rewrite Hb, E1, E2. reflexivity.
Qed.
(* close / eintr change one source's flags only *)
Lemma fr_LS_upd : forall cx t t' m m' ly S i f,
  lm_hs m' = upd_hs i f (lm_hs m) -> (forall h, asrc_blks (f h) = asrc_blks h) ->
  (forall h, hs_pending (f h) = hs_pending h /\ hs_off (f h) = hs_off h /\ hs_held (f h) = hs_held h /\
     hs_expected (f h) = hs_expected h) ->
  lm_es m' = lm_es m -> lm_G m' = lm_G m -> lm_cap m' = lm_cap m -> lm_out m' = lm_out m ->
  lm_k m <= lm_k m' -> fr_LS cx t m ly S -> fr_LS cx t' m' ly S.
Proof.
  intros cx t t' m m' ly S i f E1 Hfb Hf E2 E3 E4 E5 Hk H.
  assert (Mg : forall (g : option hsrc -> Z), (forall h, g (Some (f h)) = g (Some h)) -> map g (lm_hs m') = map g (lm_hs m))
    by (intros g Hg; rewrite E1; apply upd_hs_map; exact Hg).
  assert (Hb : model_blks m' = model_blks m).
  { unfold model_blks. rewrite E2, E3, E4, E5, E1, (upd_hs_blks i f (lm_hs m) Hfb). reflexivity. }
  apply (fr_LS_keep cx t t' m m' ly S Hb).
  - unfold PHI, pend_bytes, held_bytes, vslack. rewrite Hb, E2.
    rewrite (Mg slot_pend), (Mg slot_held), (Mg slot_vsl); [reflexivity | intros h; destruct (Hf h) as (P1 & P2 & P3 & P4); cbn; rewrite P1, P3, P4; reflexivity
      | intros h; destruct (Hf h) as (P1 & P2 & P3 & P4); cbn; rewrite P3; reflexivity
      | intros h; destruct (Hf h) as (P1 & P2 & P3 & P4); cbn; rewrite P1, P2; reflexivity].
  - rewrite !nopen_zsum, (Mg slot_open); [reflexivity | reflexivity].
  - rewrite E1. apply upd_hs_len.
  - unfold npend. rewrite (Mg slot_npend); [reflexivity | intros h; destruct (Hf h) as (P1 & _); cbn; rewrite P1; reflexivity].
  - unfold kk. lia.
  - exact H.
Qed.

Lemma hd_k'_ge : forall cx m, lm_k m <= hd_k' cx m.
Proof. intros cx m. unfold hd_k'. destruct (lm_k m + 1 <? c_n cx); lia. Qed.
Lemma sm_kn_ge : forall cx m, lm_k m <= sm_kn cx m.
Proof. intros cx m. unfold sm_kn. destruct (lm_k m + 1 <? c_n cx); lia. Qed.
Lemma in_byte_nonneg : forall cx j, 0 <= in_byte cx j.
Proof. intros cx j. unfold in_byte. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat j) (c_pl cx) (Z_to_bv 8 0))). lia. Qed.
Lemma wr_u_nonneg : forall cx m, 0 <= wr_u cx m.
Proof.
  intros cx m. unfold wr_u. pose proof (in_byte_nonneg cx (wr_k1 cx m)). pose proof (in_byte_nonneg cx (wr_k1 cx m + 1)).
  destruct (2 <=? wr_rem cx m); [lia|]. destruct (wr_rem cx m =? 1); lia.
Qed.
Lemma wr_k2_kk : forall cx m, kk cx m <= Z.min (wr_k2 cx m) (c_n cx).
Proof.
  intros cx m. pose proof (wr_u_nonneg cx m). unfold kk, wr_k2, wr_n, wr_c, wr_rem, wr_k1 in *.
  destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia.
Qed.
(* a write that takes bytes: the copy is at most n bytes, the input consumed grows by 3 + n, within the input *)
Lemma wr_facts : forall cx m, 0 < wr_n cx m ->
  lm_k m + 3 + wr_n cx m <= wr_k2 cx m <= c_n cx /\ Z.of_nat (length (wr_x cx m)) <= wr_n cx m.
Proof.
  intros cx m Hn. split.
  - revert Hn. unfold wr_k2, wr_n, wr_c, wr_rem, wr_k1. destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); intros; lia.
  - unfold wr_x. rewrite firstn_length. lia.
Qed.

(* the seven, at one (fx, rc) *)
Lemma fr_LS_head_nout : forall cx t m ly S, fr_LS cx t m ly S -> fr_LS cx t (lm_clear_O m) ly S.
Proof. intros cx t m ly S H. exact H. Qed.
Lemma fr_LS_head_skip : forall cx t m ly S,
  0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (hd_kb cx m) = None -> fr_LS cx t m ly S -> fr_LS cx (t + 1) (lm_set_k m (hd_k' cx m)) ly S.
Proof.
  intros cx t m ly S _ _ _ _ _ _ H. apply (fr_LS_k_only cx t (t + 1) m _ ly S); try reflexivity; [| exact H].
  left. exact (hd_k'_ge cx m).
Qed.
Lemma fr_LS_close : forall cx t m i ly S, fr_LS cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  fr_LS cx (t + 1) (sm_close cx m i) ly S.
Proof.
  intros cx t m i ly S H _. apply (fr_LS_upd cx t (t + 1) m _ ly S i upd_closed);
    [reflexivity | intros h; reflexivity | intros h; repeat split | reflexivity | reflexivity | reflexivity | reflexivity
    | exact (sm_kn_ge cx m) | exact H].
Qed.
Lemma fr_LS_eintr : forall cx t m i ly S, fr_LS cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  fr_LS cx (t + 1) (sm_eintr cx m i) ly S.
Proof.
  intros cx t m i ly S H _. apply (fr_LS_upd cx t (t + 1) m _ ly S i upd_eintr);
    [reflexivity | intros h; reflexivity | intros h; repeat split | reflexivity | reflexivity | reflexivity | reflexivity
    | exact (sm_kn_ge cx m) | exact H].
Qed.
Lemma fr_LS_sendmax : forall cx t m ly S, fr_LS cx t m ly S ->
  fr_LS cx (t + 1) (sm_sendmax cx m (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0)) ly S.
Proof.
  intros cx t m ly S H. apply (fr_LS_k_only cx t (t + 1) m _ ly S); try reflexivity; [| exact H].
  left. exact (sm_kn_ge cx m).
Qed.
Lemma fr_LS_default : forall cx t m ly S, fr_LS cx t m ly S -> fr_LS cx (t + 1) (sm_default cx m (sm_dg cx m)) ly S.
Proof.
  intros cx t m ly S H. apply (fr_LS_k_only cx t (t + 1) m _ ly S); try reflexivity; [| exact H].
  left. exact (sm_kn_ge cx m).
Qed.
Lemma fr_LS_write_skip : forall cx t m ly S, fr_LS cx t m ly S -> fr_LS cx (t + 1) (wr_skip m (wr_k2 cx m)) ly S.
Proof.
  intros cx t m ly S H. apply (fr_LS_k_only cx t (t + 1) m _ ly S); try reflexivity; [| exact H].
  right. unfold kk at 2. cbn [lm_k wr_skip]. exact (wr_k2_kk cx m).
Qed.

(* ------------------------------------------------------------------ op_add *)
Lemma fr_LS_add_room : forall cx t m ly S, fr_LS cx t m ly S ->
  blocks_bytes S + APARTIAL + ATABLE <= LIVE_MAX.
Proof.
  intros cx t m ly S H. pose proof (fr_LS_room cx t m ly S H). unfold ROOM_SPARE, APARTIAL, ATABLE in *. lia.
Qed.
Lemma fr_LS_add_none : forall cx t m ly S, fr_LS cx t m ly S -> fr_LS cx (t + 1) (ad_none m) ly S.
Proof.
  intros cx t m ly S H. apply (fr_LS_k_only cx t (t + 1) m _ ly S); try reflexivity; [| exact H].
  left. cbn [ad_none lm_k]. lia.
Qed.
(* op_add opened slot i (closed before): the model gains exactly the new partial buffer *)
Lemma ad_open_hs : forall m i q pj ev,
  lm_hs (ad_open m i q pj ev) = set_nth i (Some (oa_new_src (100 + lm_nfd m) q pj)) (lm_hs m).
Proof. intros m i q pj ev. cbn [ad_open lm_hs]. rewrite ad_set_nth_eq. reflexivity. Qed.
Lemma ad_open_es : forall m i q pj ev, lm_es (ad_open m i q pj ev) = lm_es m ++ [ra_new (100 + lm_nfd m)].
Proof. reflexivity. Qed.
Lemma model_perm_add : forall m i q pj ev, nth_error (lm_hs m) i = Some None ->
  Permutation (model_blks (ad_open m i q pj ev)) ((q, APARTIAL) :: model_blks m).
Proof.
  intros m i q pj ev Hi. unfold model_blks. rewrite ad_open_hs, ad_open_es, map_app, concat_app.
  assert (EG : lm_G (ad_open m i q pj ev) = lm_G m) by reflexivity.
  assert (EC : lm_cap (ad_open m i q pj ev) = lm_cap m) by reflexivity.
  assert (EO : lm_out (ad_open m i q pj ev) = lm_out m) by reflexivity.
  rewrite EG, EC, EO.
  pose proof (set_nth_perm slot_blks i (Some (oa_new_src (100 + lm_nfd m) q pj)) None (lm_hs m) Hi) as Hs.
  assert (HX : slot_blks (Some (oa_new_src (100 + lm_nfd m) q pj)) = [(q, APARTIAL)]) by reflexivity.
  assert (HN : slot_blks None = []) by reflexivity.
  rewrite HX, HN in Hs.
  assert (He : concat (map aentry_blks [ra_new (100 + lm_nfd m)]) = []) by reflexivity.
  rewrite He. perm_lia.
Qed.
Lemma fr_LS_add_open : forall cx t m i q pj ev ly S (ly' : alayout) (S' : astate),
  fr_LS cx t m ly S -> oa_first (ad_os (lm_hs m)) = Some i ->
  Permutation (ablocks B ly' S') ((q, APARTIAL) :: ablocks B ly S) ->
  fr_LS cx (t + 1) (ad_open m i q pj ev) ly' S'.
Proof.
  intros cx t m i q pj ev ly S ly' S' (rest & e0 & HP & HR & HE & Hc & Hl & Hnp & HM) Hf HP'.
  destruct (oa_first_free (lm_hs m) i Hl Hf) as (Hi4 & Hi).
  pose proof (model_perm_add m i q pj ev Hi) as Hm.
  assert (Zs : forall (g : option hsrc -> Z), zsum (map g (lm_hs (ad_open m i q pj ev))) + g None =
                 zsum (map g (lm_hs m)) + g (Some (oa_new_src (100 + lm_nfd m) q pj)))
    by (intros g; rewrite ad_open_hs; exact (set_nth_zsum g i _ None (lm_hs m) Hi)).
  exists rest, e0. split; [| split; [exact HR | split; [exact HE | split; [exact Hc | split]]]].
  - pose proof (Permutation_sym Hm) as Hm'. clear Hm. perm_lia.
  - rewrite ad_open_hs, set_nth_len. exact Hl.
  - assert (Hk : kk cx m <= kk cx (ad_open m i q pj ev)) by (unfold kk; cbn [ad_open lm_k]; lia).
    pose proof (Zs slot_pend) as Z1. pose proof (Zs slot_held) as Z2. pose proof (Zs slot_vsl) as Z3.
    pose proof (Zs slot_npend) as Z4. pose proof (Zs slot_open) as Z5.
    assert (P1 : slot_pend (Some (oa_new_src (100 + lm_nfd m) q pj)) = 0) by reflexivity.
    assert (P2 : slot_held (Some (oa_new_src (100 + lm_nfd m) q pj)) = 0) by reflexivity.
    assert (P3 : slot_vsl (Some (oa_new_src (100 + lm_nfd m) q pj)) = 0) by reflexivity.
    assert (P4 : slot_npend (Some (oa_new_src (100 + lm_nfd m) q pj)) = 0) by reflexivity.
    assert (P5 : slot_open (Some (oa_new_src (100 + lm_nfd m) q pj)) = 1) by reflexivity.
    assert (N1 : slot_pend None = 0) by reflexivity. assert (N2 : slot_held None = 0) by reflexivity.
    assert (N3 : slot_vsl None = 0) by reflexivity. assert (N4 : slot_npend None = 0) by reflexivity.
    assert (N5 : slot_open None = 0) by reflexivity.
    assert (Eh : zsum (map entry_held (lm_es (ad_open m i q pj ev))) = zsum (map entry_held (lm_es m))).
    { rewrite ad_open_es, map_app, zsum_app. assert (E0 : entry_held (ra_new (100 + lm_nfd m)) = 0) by reflexivity.
      cbn [map fold_right]. lia. }
    assert (Eb : bsum (model_blks (ad_open m i q pj ev)) = APARTIAL + bsum (model_blks m))
      by (rewrite (bsum_perm _ _ Hm), bsum_cons; reflexivity).
    split.
    + unfold npend in *. lia.
    + unfold PHI, pend_bytes, held_bytes, vslack in *. rewrite !nopen_zsum in *. rewrite Eb, Eh.
      unfold MB_K, APARTIAL, W_P, W_H in *. lia.
Qed.

(* ------------------------------------------------------------------ the write arm's room *)
Lemma npend_slot : forall m si h, nth si (lm_hs m) None = Some h -> hl_n (hs_pending h) <= npend m.
Proof.
  intros m si h Hh. unfold npend. exact (zsum_map_elem slot_npend (lm_hs m) si (Some h) slot_npend_nonneg
    (nth_some_error _ _ _ Hh)).
Qed.
Lemma fr_LS_write_room : forall cx t m si h ly S, fr_LS cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  (lp_grow (hs_pending h) = true -> lp_vbytes (hs_pending h) < WR_MMAX) /\
  blocks_bytes S + (if lp_grow (hs_pending h) then lp_vbytes (hs_pending h) else 0) + (wr_n cx m + 1) <= LIVE_MAX.
Proof.
  intros cx t m si h ly S H (_ & _ & Hh) Hn.
  pose proof (fr_LS_room cx t m ly S H) as Hroom. pose proof (fr_LS_k cx t m ly S H) as Hk0.
  destruct H as (rest & e0 & HP & HR & HE & Hc & Hl & Hnp & HM).
  pose proof (npend_slot m si h Hh) as Hs. pose proof (wr_facts cx m Hn) as ((W1 & W2) & _).
  assert (Hkk : kk cx m <= c_n cx) by (unfold kk; lia).
  set (l := hs_pending h) in *.
  assert (Hn0 : 0 <= hl_n l) by (unfold hl_n; lia).
  assert (Hv : lp_grow l = true -> lp_vbytes l <= 32 * hl_n l + 128).
  { unfold lp_grow, lp_vbytes, grow_cap, AREC. intros G. apply Z.eqb_eq in G. rewrite G, Z.eqb_refl.
    destruct (Z.eqb_spec (hl_cap l) 0); lia. }
  assert (HW : WR_MMAX = 1072693248) by reflexivity.
  split.
  - intros G. specialize (Hv G). unfold ROOM_SPARE in *. lia.
  - destruct (lp_grow l) eqn:G; [specialize (Hv eq_refl) |]; unfold ROOM_SPARE, kk in *; lia.
Qed.

(* ------------------------------------------------------------------ the write arm's push, at the proposed text *)
(* a pending list gains the record (d, x): its blocks gain the copy, and the vector moves when it grows *)
Lemma fr_LS_write_push : forall cx t m si h (l' : hlist) d ly S ly' S' ev,
  fr_LS cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, wr_x cx m)] ->
  hl_cap l' = grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  (lp_grow (hs_pending h) = false -> hl_v l' = hl_v (hs_pending h)) ->
  (forall rest, Permutation (ablocks B ly S)
       ((if lp_grow (hs_pending h) && negb (hl_cap (hs_pending h) =? 0)
         then [(hl_v (hs_pending h), AREC * hl_cap (hs_pending h))] else []) ++ rest) ->
     Permutation (ablocks B ly' S')
       ((d, Z.of_nat (length (wr_x cx m)) + 1) ::
        (if lp_grow (hs_pending h) then [(hl_v l', AREC * hl_cap l')] else []) ++ rest)) ->
  fr_LS cx (t + 1) (wr_push m (wr_k2 cx m) si (set_pending h l') ev) ly' S'.
Proof.
  intros cx t m si h l' d ly S ly' S' ev H (_ & _ & Hh) Hn Hrecs Hcap Hv Hlp.
  pose proof (fr_LS_k cx t m ly S H) as Hk0.
  destruct H as (rest & e0 & HP & HR & HE & Hc & Hl & Hnp & HM).
  pose proof (wr_facts cx m Hn) as ((W1 & W2) & Wx).
  pose proof (nth_some_error _ _ _ Hh) as Hi.
  set (l := hs_pending h) in *. set (x := wr_x cx m) in *. set (h' := set_pending h l').
  set (m' := wr_push m (wr_k2 cx m) si h' ev).
  set (dd := (d, Z.of_nat (length x) + 1)).
  set (OV := if lp_grow l && negb (hl_cap l =? 0) then [(hl_v l, AREC * hl_cap l)] else []).
  set (NV := if lp_grow l then [(hl_v l', AREC * hl_cap l')] else []).
  set (VL := if hl_cap l =? 0 then [] else [(hl_v l, AREC * hl_cap l)]).
  set (VL' := if hl_cap l' =? 0 then [] else [(hl_v l', AREC * hl_cap l')]).
  set (CL := map (fun r : Z * list byte => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l)).
  assert (Hn1 : hl_n l' = hl_n l + 1) by (unfold hl_n; rewrite Hrecs, length_app; cbn; lia).
  assert (Hb1 : hl_bytes l' = hl_bytes l + Z.of_nat (length x))
    by (unfold hl_bytes; rewrite Hrecs, map_app, zsum_app; cbn; lia).
  assert (Hn0 : 0 <= hl_n l) by (unfold hl_n; lia).
  (* the vector, case by case: VL' ++ OV ~ VL ++ NV, and what it costs with the slack *)
  assert (HV : Permutation (VL' ++ OV) (VL ++ NV) /\
               bsum NV - bsum OV + vsl l' - vsl l <= 128).
  { unfold VL', OV, VL, NV, vsl. rewrite Hn1. unfold lp_grow in *. unfold grow_cap in Hcap.
    destruct (Z.eqb_spec (hl_n l) (hl_cap l)) as [G|G].
    - try rewrite (proj2 (Z.eqb_eq _ _) G) in Hcap. cbv beta iota in Hcap.
      destruct (Z.eqb_spec (hl_cap l) 0) as [C0|C0].
      + rewrite Hcap. rewrite C0 in *. cbn. unfold AREC. split; [apply Permutation_refl | lia].
      + assert (E2 : (2 * hl_cap l =? 0) = false) by (apply Z.eqb_neq; lia).
        rewrite Hcap, E2. cbn [andb negb app]. split; [first [apply perm_swap | apply Permutation_app_comm] | cbn; unfold AREC; lia].
    - assert (Hv' : hl_v l' = hl_v l) by (apply Hv; first [exact (proj2 (Z.eqb_neq _ _) G) | reflexivity]).
      try rewrite (proj2 (Z.eqb_neq _ _) G) in Hcap. cbv beta iota in Hcap.
      rewrite Hcap, Hv'. cbn [andb negb app]. split.
      + apply Permutation_refl.
      + cbn. unfold AREC. lia. }
  destruct HV as (HVp & HVc).
  (* asrc_blks h' against asrc_blks h *)
  assert (Ha : asrc_blks h = (hs_partial h, APARTIAL) :: (VL ++ CL) ++ alist_blks (hs_expected h) ++ alist_blks (hs_held h))
    by reflexivity.
  assert (Ha' : asrc_blks h' = (hs_partial h, APARTIAL) :: (VL' ++ CL ++ [dd]) ++ alist_blks (hs_expected h) ++
                  alist_blks (hs_held h))
    by (unfold h', asrc_blks, alist_blks; cbn [set_pending hs_partial hs_pending hs_expected hs_held];
        fold VL'; rewrite Hrecs, map_app; reflexivity).
  pose proof (set_nth_perm slot_blks si (Some h') (Some h) (lm_hs m) Hi) as Hsw. cbn [slot_blks] in Hsw.
  rewrite Ha, Ha' in Hsw.
  (* the model: model' ++ OV ~ model ++ NV ++ [dd] *)
  assert (HM2 : Permutation (model_blks m' ++ OV) (model_blks m ++ NV ++ [dd])).
  { unfold model_blks, m'. cbn [wr_push lm_G lm_es lm_hs lm_cap lm_out]. perm_lia. }
  (* the old vector, when it moves, is a block of the model *)
  assert (Hsplit : exists mm, Permutation (model_blks m) (OV ++ mm)).
  { destruct (lp_grow l && negb (hl_cap l =? 0)) eqn:Eg; unfold OV; try rewrite Eg; cbv beta iota.
    - assert (Hin : In (hl_v l, AREC * hl_cap l) (model_blks m)).
      { apply andb_true_iff in Eg as (_ & E). apply negb_true_iff in E. unfold model_blks.
        right. apply in_app_iff. right. apply in_app_iff. left. apply in_concat.
        exists (slot_blks (Some h)). split; [apply in_map; exact (nth_error_In _ _ Hi)|].
        cbn [slot_blks]. rewrite Ha. right. apply in_app_iff. left. apply in_app_iff. left.
        unfold VL. rewrite E. left. reflexivity. }
      destruct (in_split _ _ Hin) as (l1 & l2 & E). exists (l1 ++ l2). rewrite E. perm_lia.
    - exists (model_blks m). apply Permutation_refl. }
  destruct Hsplit as (mm & Hmm).
  assert (HP1 : Permutation (ablocks B ly S) (OV ++ (input_blks cx ++ mm ++ rest))) by perm_lia.
  pose proof (Hlp _ HP1) as HP2. fold x dd NV in HP2.
  (* the measures *)
  assert (Zs : forall (g : option hsrc -> Z), zsum (map g (lm_hs m')) + g (Some h) = zsum (map g (lm_hs m)) + g (Some h'))
    by (intros g; exact (set_nth_zsum g si (Some h') (Some h) (lm_hs m) Hi)).
  pose proof (Zs slot_pend) as Z1. pose proof (Zs slot_held) as Z2. pose proof (Zs slot_vsl) as Z3.
  pose proof (Zs slot_npend) as Z4. pose proof (Zs slot_open) as Z5.
  cbn [slot_pend slot_held slot_vsl slot_npend slot_open h' set_pending hs_pending hs_off hs_held hs_expected] in Z1, Z2, Z3, Z4, Z5.
  fold l in Z1, Z3, Z4.
  assert (Eb : bsum (model_blks m') + bsum OV = bsum (model_blks m) + bsum NV + snd dd)
    by (rewrite <- bsum_app, (bsum_perm _ _ HM2), !bsum_app; cbn; lia).
  assert (Hk' : kk cx m' = wr_k2 cx m) by (unfold kk, m'; cbn [wr_push lm_k]; lia).
  assert (Hkm : kk cx m = lm_k m) by (unfold kk; lia).
  exists rest, e0. split; [| split; [exact HR | split; [exact HE | split; [exact Hc | split]]]].
  - clear - HP2 Hmm HM2. perm_lia.
  - unfold m'. cbn [wr_push lm_hs]. rewrite set_nth_len. exact Hl.
  - split.
    + unfold npend in *. rewrite Hk', Hkm in *. lia.
    + unfold PHI, pend_bytes, held_bytes, vslack in *. rewrite !nopen_zsum in *. rewrite Hk', Hkm in *.
      assert (E1 : lm_es m' = lm_es m) by reflexivity. rewrite E1.
      unfold dd in Eb. cbn [snd] in Eb. rewrite Hb1 in Z1.
      unfold MB_K, W_P, W_H, APARTIAL in *. lia.
Qed.
(* ------------------------------------------------------------------ the prologue: LS_pro_oa, and LS_pro at the proposed text *)
(* op_add's room at the state after the fake frame: the entry's call room (ACfn_cf.v fr_live_pre at its instance) *)
Lemma fr_LS_pro_oa : forall XM_LIB RLO RHI G_fr cx (S2 : astate) (pos : Z),
  lf_base B ameter_triv XM_LIB RLO RHI ACfn_cf.fr_live_pre G_fr cx ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) ->
  blocks_bytes S2 + APARTIAL + ATABLE <= LIVE_MAX /\ mo_ok ameter_triv S2 (oa_cost ameter_triv).
Proof.
  intros XM_LIB RLO RHI G_fr cx S2 pos (_ & Hpre) _ _ _ Hbb.
  destruct Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & Hlive & _). unfold ACfn_cf.fr_live_pre in Hlive.
  assert (HC : ACfn_cf.CALL_ROOM = 8589934592) by reflexivity.
  split; [| exact I]. rewrite Hbb. unfold APARTIAL, ATABLE. lia.
Qed.
(* the model at the first head (pro_m of lib/A/W_LLVMFuzzerTestOneInput_pro.v, a working branch fff279dd36e) *)
Definition ls_pro_m (q T' : Z) (pj : list byte) (c : ctl) (O : list byte) (cap out : Z) : lmod :=
  LM 0 [Some (oa_new_src 100 q pj); None; None; None] T' [ra_new 100] c O 0 cap out 0 1.
(* LS at the first head, AT THE PROPOSED TEXT: the published premise
     Permutation (ablocks B ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks entry) \/
     Permutation (ablocks B ly S) ((q, APARTIAL) :: ablocks entry)
   does not place (T', ATABLE) among the live blocks in its second case, nor the entry's input and g_out buffer among
   the entry's blocks, so LS's own split cannot be built from it.  The proposed premise is HFP_pro's entry split (its
   first conjunct, at the entry's table T0) with ra_post's two cases (T0 = 0: the table is new; T0 <> 0: T' = T0). *)
Lemma fr_LS_pro : forall XM_LIB RLO RHI G_fr cx q T' pj c O cap out ly S,
  lf_base B ameter_triv XM_LIB RLO RHI ACfn_cf.fr_live_pre G_fr cx ->
  (exists T0 rest0, Permutation (ablocks B (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) /\
     ((T0 = 0 /\ Permutation (ablocks B ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks B ly S) ((q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))))) ->
  fr_LS cx 0 (ls_pro_m q T' pj c O cap out) ly S.
Proof.
  intros XM_LIB RLO RHI G_fr cx q T' pj c O cap out ly S (_ & Hpre) (T0 & rest0 & HE0 & Hcase).
  destruct Hpre as (_ & _ & _ & _ & Hd & _ & _ & _ & Hlive & _). unfold ACfn_cf.fr_live_pre in Hlive.
  assert (Hc : 0 <= c_n cx < 2 ^ 26) by (destruct Hd as [(Hd & _) | (Hd & _)]; lia).
  assert (Hmb : model_blks (ls_pro_m q T' pj c O cap out) = (T', ATABLE) :: (q, APARTIAL) :: aout_blks cap out)
    by reflexivity.
  assert (Ep : pend_bytes (ls_pro_m q T' pj c O cap out) = 0) by reflexivity.
  assert (Eh : held_bytes (ls_pro_m q T' pj c O cap out) = 0) by reflexivity.
  assert (Ev : vslack (ls_pro_m q T' pj c O cap out) = 0) by reflexivity.
  assert (En : npend (ls_pro_m q T' pj c O cap out) = 0) by reflexivity.
  assert (Eo : nopen (lm_hs (ls_pro_m q T' pj c O cap out)) = 1) by reflexivity.
  assert (Ek : kk cx (ls_pro_m q T' pj c O cap out) = 0) by (unfold kk; cbn [ls_pro_m lm_k]; lia).
  assert (Eb0 : blocks_bytes (c_S cx) = bsum (ablocks B (c_ly cx) (c_S cx))) by apply blocks_bytes_bsum.
  destruct Hcase as [(HT0 & HP) | (HT0 & HT' & HP)].
  - subst T0. rewrite Z.eqb_refl in HE0. cbv beta iota in HE0.
    exists rest0, (bsum (aout_blks cap out)).
    split; [rewrite Hmb; perm_lia |].
    split; [rewrite Eb0, (bsum_perm _ _ HE0), !bsum_app, ?bsum_nil; lia |].
    split; [exact Hlive | split; [exact Hc | split; [reflexivity | split]]].
    + rewrite En, Ek. lia.
    + unfold PHI. rewrite Hmb, Ep, Eh, Ev, Eo, Ek. rewrite !bsum_cons. cbn [snd].
      unfold MB_K, MB_C, W_P, W_H, APARTIAL, ATABLE. lia.
  - subst T'. rewrite (proj2 (Z.eqb_neq _ _) HT0) in HE0. cbv beta iota in HE0.
    exists rest0, (ATABLE + bsum (aout_blks cap out)).
    split; [rewrite Hmb; perm_lia |].
    split; [rewrite Eb0, (bsum_perm _ _ HE0), !bsum_app, bsum_cons, ?bsum_nil; cbn [snd]; lia |].
    split; [exact Hlive | split; [exact Hc | split; [reflexivity | split]]].
    + rewrite En, Ek. lia.
    + unfold PHI. rewrite Hmb, Ep, Eh, Ev, Eo, Ek. rewrite !bsum_cons. cbn [snd].
      unfold MB_K, MB_C, W_P, W_H, APARTIAL, ATABLE. lia.
Qed.
End ls.

(* ------------------------------------------------------------------ the rules in ReplyATop.v's family form *)
Section fam.
Variable B : asyms.
Variable RIf : forall (fx : YK11.FPState) (rc : YM05.RunCeil), lfcx (rc := rc) -> Z -> lmod -> Prop.
Local Notation LSf := (fun (fx : YK11.FPState) (rc : YM05.RunCeil) => fr_LS (rc := rc) B).
Lemma atop_LS_head_nout : forall (fx : YK11.FPState) (rc : YM05.RunCeil) cx t m ly S,
  LSf fx rc cx t m ly S -> LSf fx rc cx t (lm_clear_O m) ly S.
Proof. intros fx rc. exact (fr_LS_head_nout (rc := rc) B). Qed.
Lemma atop_LS_head_skip : forall (fx : YK11.FPState) (rc : YM05.RunCeil) cx t m ly S,
  0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (hd_kb cx m) = None -> LSf fx rc cx t m ly S -> LSf fx rc cx (t + 1) (lm_set_k m (hd_k' cx m)) ly S.
Proof. intros fx rc. exact (fr_LS_head_skip (rc := rc) B). Qed.
Lemma atop_LS_add_room : forall (fx : YK11.FPState) (rc : YM05.RunCeil) cx t m ly S,
  LSf fx rc cx t m ly S -> RIf fx rc cx t m -> ad_at_op cx m ->
  blocks_bytes S + APARTIAL + ATABLE <= LIVE_MAX /\ mo_ok ameter_triv S (oa_cost ameter_triv).
Proof. intros fx rc cx t m ly S H _ _. split; [exact (fr_LS_add_room (rc := rc) B cx t m ly S H) | exact I]. Qed.
Lemma atop_LS_add_open : forall (fx : YK11.FPState) (rc : YM05.RunCeil) cx t m i q pj ev ly S
  (ly' : alayout) (S' : astate),
  LSf fx rc cx t m ly S -> RIf fx rc cx t m -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = Some i ->
  mo_le ameter_triv S S' (oa_cost ameter_triv) -> Permutation (ablocks B ly' S') ((q, APARTIAL) :: ablocks B ly S) ->
  LSf fx rc cx (t + 1) (ad_open m i q pj ev) ly' S'.
Proof. intros fx rc cx t m i q pj ev ly S ly' S' H _ _ Hf _ HP. exact (fr_LS_add_open (rc := rc) B cx t m i q pj ev ly S ly' S' H Hf HP). Qed.
Lemma atop_LS_add_none : forall (fx : YK11.FPState) (rc : YM05.RunCeil) cx t m ly S,
  LSf fx rc cx t m ly S -> RIf fx rc cx t m -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = None ->
  LSf fx rc cx (t + 1) (ad_none m) ly S.
Proof. intros fx rc cx t m ly S H _ _ _. exact (fr_LS_add_none (rc := rc) B cx t m ly S H). Qed.
Lemma atop_LS_close : forall (fx : YK11.FPState) (rc : YM05.RunCeil) cx t m i ly S, LSf fx rc cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  LSf fx rc cx (t + 1) (sm_close cx m i) ly S.
Proof. intros fx rc. exact (fr_LS_close (rc := rc) B). Qed.
Lemma atop_LS_eintr : forall (fx : YK11.FPState) (rc : YM05.RunCeil) cx t m i ly S, LSf fx rc cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  LSf fx rc cx (t + 1) (sm_eintr cx m i) ly S.
Proof. intros fx rc. exact (fr_LS_eintr (rc := rc) B). Qed.
Lemma atop_LS_sendmax : forall (fx : YK11.FPState) (rc : YM05.RunCeil) cx t m ly S, LSf fx rc cx t m ly S ->
  LSf fx rc cx (t + 1) (sm_sendmax cx m (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0)) ly S.
Proof. intros fx rc. exact (fr_LS_sendmax (rc := rc) B). Qed.
Lemma atop_LS_default : forall (fx : YK11.FPState) (rc : YM05.RunCeil) cx t m ly S,
  LSf fx rc cx t m ly S -> LSf fx rc cx (t + 1) (sm_default cx m (sm_dg cx m)) ly S.
Proof. intros fx rc. exact (fr_LS_default (rc := rc) B). Qed.
Lemma atop_LS_write_skip : forall (fx : YK11.FPState) (rc : YM05.RunCeil) cx t m ly S,
  LSf fx rc cx t m ly S -> LSf fx rc cx (t + 1) (wr_skip m (wr_k2 cx m)) ly S.
Proof. intros fx rc. exact (fr_LS_write_skip (rc := rc) B). Qed.
Lemma atop_LS_write_room : forall (fx : YK11.FPState) (rc : YM05.RunCeil) cx t m si h ly S,
  LSf fx rc cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  (lp_grow (hs_pending h) = true -> lp_vbytes (hs_pending h) < WR_MMAX) /\
  blocks_bytes S + (if lp_grow (hs_pending h) then lp_vbytes (hs_pending h) else 0) + (wr_n cx m + 1) <= LIVE_MAX /\
  mo_ok ameter_triv S (lp_cost ameter_triv (hs_pending h) (wr_n cx m)).
Proof.
  intros fx rc cx t m si h ly S H Hp Hn. destruct (fr_LS_write_room (rc := rc) B cx t m si h ly S H Hp Hn) as (A1 & A2).
  exact (conj A1 (conj A2 I)).
Qed.
(* the write arm's push AT THE PROPOSED TEXT: lp_post's facts about the pushed list (W_contract.v lp_post: the record,
   the vector's size and address, and the blocks' change) in place of the published `mo_le MT S S' cost` alone *)
Lemma atop_LS_write_push_prop : forall (fx : YK11.FPState) (rc : YM05.RunCeil) cx t m si h (l' : hlist) d ev ly S ly' S',
  LSf fx rc cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, wr_x cx m)] ->
  hl_cap l' = grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  (lp_grow (hs_pending h) = false -> hl_v l' = hl_v (hs_pending h)) ->
  (forall rest, Permutation (ablocks B ly S)
       ((if lp_grow (hs_pending h) && negb (hl_cap (hs_pending h) =? 0)
         then [(hl_v (hs_pending h), AREC * hl_cap (hs_pending h))] else []) ++ rest) ->
     Permutation (ablocks B ly' S')
       ((d, Z.of_nat (length (wr_x cx m)) + 1) ::
        (if lp_grow (hs_pending h) then [(hl_v l', AREC * hl_cap l')] else []) ++ rest)) ->
  mo_le ameter_triv S S' (lp_cost ameter_triv (hs_pending h) (wr_n cx m)) ->
  LSf fx rc cx (t + 1) (wr_push m (wr_k2 cx m) si (set_pending h l') ev) ly' S'.
Proof.
  intros fx rc cx t m si h l' d ev ly S ly' S' H Hp Hn Hr Hc Hv HP _.
  exact (fr_LS_write_push (rc := rc) B cx t m si h l' d ly S ly' S' ev H Hp Hn Hr Hc Hv HP).
Qed.
End fam.
