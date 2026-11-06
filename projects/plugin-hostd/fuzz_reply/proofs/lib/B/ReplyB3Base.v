(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyLS.v, with its module paths and module names changed; 33 of its 207 lines of code are new or changed and 420 lines of the source are left out. *)
(* proves no function (kind: model and invariant lemmas): the helpers of A's v2 LS files that image B's v2 port lacks
   and the v3 layer reads *)
(* Theorem Labs, 2026-10: the image-B port of the helpers of lib/A/ReplyLS.v (sha256 9996c0f696df; internal record) and
   lib/A/ReplyLSArms.v (sha256 829a485ef52f; internal record) at 1b1e21bdbd40 that lib/B/ReplyLSB.v,
   ReplyLSBArms.v and ReplyLSBTrPeak.v do not define and A's v3 files (ReplyLS3.v, ReplyLS3c.v, ReplyLS3Arms.v, ...)
   read.  Names and statements are A's; each lemma cites its A line (A = ReplyLS.v, AA = ReplyLSArms.v).
     ROOM_SPARE (A :79); zsum_app, zsum_map_nonneg, zsum_map_elem (A :106-116); set_nth_len, ad_set_nth_eq,
     set_nth_perm, set_nth_zsum, upd_hs_map, upd_hs_len, nth_some_error, oa_first_free (A :142-183); slot_open (A :91);
     hl_bytes_nonneg, slot_pend_nonneg, slot_held_nonneg, slot_vsl_nonneg, slot_npend_nonneg, entry_held_nonneg,
     nopen_zsum, nopen_le4, PHI_ge, npend_nonneg (A :186-217); sm_kn_ge, in_byte_nonneg, wr_u_nonneg, wr_k2_kk
     (A :293-306); wr_facts_B (A :308-314 wr_facts); ad_open_hs, ad_open_es, model_perm_add (A :372-391); npend_slot
     (A :429-433); fr_LS_pro_oa (A :551-561); mo_ok_triv (AA :71-72); ev_len_le (AA :115-118).
   Not ported as names: MT, MMAX (AA :68-69) and LSf (A :615) are Local Notations in A, which do not leave their files;
   each v3 file states its own (lib/A/ReplyLS3.v :514, ReplyLS3Arms.v :74-75).  MMAX is restated here, locally.
   KF-COUNT (the meter pattern of a Theorem Labs lane, A #6): the meter is a Section Context {MT : ameter_ops}, implicit
   (read off lf_base's argument); fr_LS_pro_oa states only its room conjunct (the row's meter conjunct is the B
   instance's, from its count clause); mo_ok_triv is ameter_triv's own fact; AA's rm_cnl_cost / rm_cshe_cost copies
   are gone: the v3 files read lib/B/W_LLVMFuzzerTestOneInput_remove.v's, which take the meter first (A: ReplyLSArms.v
   reads W_LLVMFuzzerTestOneInput_remove.rm_*_cost MT).  zsum_map_elem, ad_set_nth_eq, hl_bytes_nonneg, entry_held_nonneg,
   in_byte_nonneg and wr_u_nonneg are the proofs' own steps (A's lemmas of the same names).
   A -> B SWAPS (as lib/B/ReplyLSB.v's header, which this file follows line for line):
   - lib/A AB1v -> lib/B YB1v; lib/Reusable YE01 -> lib/B YE01; lib/A AE2k -> lib/B YE2k, then `Require ReplyGuardB`;
     lib/A ACfn (Imported) -> lib/B YCfn, Required only; lib/A W_* -> lib/B's files of the same names;
   - lib/A ReplyLS -> lib/B ReplyLSB (MB_K .. W_H, the measures hl_bytes .. npend, PHI, kk, bsum_*, zzdec, cnt_cons,
     cnt_nil); lib/A ReplyLSArms -> this file and lib/B ReplyLSBArms;
   - lib/A W_LLVMFuzzerTestOneInput_small / _write / _add / W_op_add -> lib/B's files of the same names (upd_hs,
     upd_hs_blks, sm_kn; set_nth, wr_*, WR_MMAX; ad_set_nth, ad_open, ad_os; oa_first, oa_new_src, oa_cost).  The wr_*
     names are B's _write.v's, NOT the copies in lib/B/ReplyLSBArms.v :116-128;
   - lib/A W_LLVMFuzzerTestOneInput_event -> lib/B ReplyLSBArms.ev_len (:136, the copy of lib/B/W_LLVMFuzzerTestOneInput_arm_event.v:502-503);
   - ACfn_cf.fr_live_pre (fr_LS_pro_oa) -> lib/B/YCfn_cf.v :61 fr_live_pre_b, whose room CALL_ROOM_B (:59) is A's
     2 ^ 33; ameter_triv is lib/Reusable/YCbp.v's (the instance of lf_base's meter record lib/Reusable/YC5d.v);
   - wr_facts -> wr_facts_B: lib/B/W_LLVMFuzzerTestOneInput_write.v :299 already names a Definition wr_facts.
   No statement here mentions fr_LS, so none takes ReplyLSB.fr_LS's CALL_ROOM_B parameter. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
(* the meter record (YC5d) and its one instance ameter_triv (Reusable/YCbp.v :17-18), as lib/B/ReplyLSBArms.v *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_write
W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyLSBArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB.
Import ListNotations.
(* the event op's length (ReplyLSBArms.v:152, the text-identical copy of arm_event.v:502; cand13 rebase: the event
   walk arm_event does not load beside the B kit until an internal work row re-fits it) *)
Local Notation ev_len := ReplyLSBArms.ev_len.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ------------------------------------------------------------------ the constant (A :79) *)
Definition ROOM_SPARE : Z := 2147483648.         (* 2^31: what every cut point has to spare under LIVE_MAX *)

Local Notation zsum l := (fold_right Z.add 0 l).
(* the write arm's request bound (AA :65-69) *)
Local Notation MMAX := WR_MMAX.

(* ------------------------------------------------------------------ slot_open (A :91) *)
Definition slot_open (o : option hsrc) : Z := match o with Some _ => 1 | None => 0 end.

Section base.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the meter (KF-COUNT): a Variable, implicit, read off lf_base's argument *)
Context {MT : ameter_ops}.

(* counts of a block at a point (ReplyLSB.v's perm_lia, which is local to its Section) *)
Ltac perm_lia :=
  repeat match goal with H : Permutation _ _ |- _ =>
    let H' := fresh "Hc" in pose proof (proj1 (Permutation_count_occ zzdec _ _) H) as H'; clear H end;
  apply (proj2 (Permutation_count_occ zzdec _ _)); let x := fresh "x" in intros x;
  repeat match goal with H : forall _ : Z * Z, count_occ _ _ _ = count_occ _ _ _ |- _ => specialize (H x) end;
  repeat progress (rewrite ?count_occ_app, ?cnt_cons, ?cnt_nil in *); lia.

(* ------------------------------------------------------------------ list and count helpers (A :106-116) *)
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

(* ------------------------------------------------------------------ set_nth, upd_hs, oa_first (A :142-183) *)
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

(* ------------------------------------------------------------------ the measures (A :186-217) *)
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

(* ------------------------------------------------------------------ the cursors (A :293-314) *)
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
(* a write that takes bytes: the copy is at most n bytes, the input consumed grows by 3 + n, within the input
   (A :308-314 wr_facts) *)
Lemma wr_facts_B : forall cx m, 0 < wr_n cx m ->
  lm_k m + 3 + wr_n cx m <= wr_k2 cx m <= c_n cx /\ Z.of_nat (length (wr_x cx m)) <= wr_n cx m.
Proof.
  intros cx m Hn. split.
  - revert Hn. unfold wr_k2, wr_n, wr_c, wr_rem, wr_k1. destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); intros; lia.
  - unfold wr_x. rewrite length_firstn. lia.
Qed.

(* ------------------------------------------------------------------ op_add opened slot i (A :371-391) *)
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

(* ------------------------------------------------------------------ the write arm's slot (A :429-433) *)
Lemma npend_slot : forall m si h, nth si (lm_hs m) None = Some h -> hl_n (hs_pending h) <= npend m.
Proof.
  intros m si h Hh. unfold npend. exact (zsum_map_elem slot_npend (lm_hs m) si (Some h) slot_npend_nonneg
    (nth_some_error _ _ _ Hh)).
Qed.

(* ------------------------------------------------------------------ the prologue's op_add room (A :550-561) *)
(* op_add's room at the state after the fake frame: the entry's call room (YCfn_cf.v :61 fr_live_pre_b, with
   CALL_ROOM_B = 2 ^ 33, A's ACfn_cf.CALL_ROOM); the row's meter conjunct is the B instance's *)
Lemma fr_LS_pro_oa : forall XM_LIB RLO RHI G_fr cx (S2 : astate) (pos : Z),
  lf_base B MT XM_LIB RLO RHI YCfn_cf.fr_live_pre_b G_fr cx ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) ->
  blocks_bytes S2 + APARTIAL + ATABLE <= LIVE_MAX.
Proof.
  intros XM_LIB RLO RHI G_fr cx S2 pos (_ & Hpre) _ _ _ Hbb.
  destruct Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & Hlive & _). unfold YCfn_cf.fr_live_pre_b in Hlive.
  assert (HC : YCfn_cf.CALL_ROOM_B = 8589934592) by reflexivity.
  rewrite Hbb. unfold APARTIAL, ATABLE. lia.
Qed.
End base.

(* ------------------------------------------------------------------ ReplyLSArms.v's (AA :71-72, :115-118) *)
Lemma mo_ok_triv : forall (S : astate) (c : Z), mo_ok ameter_triv S c.
Proof. intros S c. exact I. Qed.

Section arms.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* the event's bytes are input bytes: at most c_n of them *)
Lemma ev_len_le : forall cx m, 0 <= lm_k m -> 0 <= c_n cx -> ev_len cx m <= c_n cx.
Proof.
  intros cx m Hk Hn. unfold ev_len. destruct (Z.leb_spec 2 (c_n cx - lm_k m - 1)); lia.
Qed.
End arms.
