(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyLS.v, with its module paths and module names changed; 219 of its 522 lines of code are new or changed and 291 lines of the source are left out. *)
(* proves no function (kind: model and invariant lemmas): fr_LS3, LS v3 of the entry walk of LLVMFuzzerTestOneInput
   at image B, its room, and the rules of ReplyLSB.v / lib/A/ReplyLS.v at v3 *)
(* Theorem Labs, 2026-10: the image-B (fuzz_reply.asan-ubsan) port of lib/A/ReplyLS3.v (sha256
   f116a5fb48df; internal record) at 1b1e21bdbd40.  What v3 is and why (ECRED, E_ENT, W_U, K0,
   W_OPEN): A's header, A :3-33; every definition is A's text and every lemma keeps A's name and statement but for the
   swaps below.  Each piece cites its A line (A = lib/A/ReplyLS3.v).
   A -> B SWAPS (as lib/B/ReplyLSB.v, the B port of A's v2 file, makes them):
   - the Require header is lib/B/ReplyB3Base.v's (lib/B YB1v, YE01, YE2k, `Require YCfn`, lib/B W_*, ReplyGuardB, the
     B arm files _head / _small / _write / _add, YCfn_cf); lib/A ReplyLS -> lib/B ReplyLSB + ReplyB3Base (A's helpers
     that ReplyLSB lacks; A's wr_facts is ReplyB3Base.wr_facts_B);
   - ACfn_cf.CALL_ROOM -> the Section variable CALL_ROOM_B, declared after B, as ReplyLSB.fr_LS takes it:
     fr_LS3 is `fr_LS3 B CALL_ROOM_B`.  A's room lemmas read CALL_ROOM's value 2 ^ 33 (A :139); at B they take the
     premise `YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B` (YCfn_cf.v :59, the B driver's room, A's value), right after
     CALL_ROOM_B: fr_LS3_room_x, fr_LS3_room, fr_LS3_add_room, fr_LS3_write_room and their family forms
     atop_LS3_add_room, atop_LS3_write_room.  The premise holds at the B instance CALL_ROOM_B := YCfn_cf.CALL_ROOM_B
     (Z.le_refl).  fr_LS3_room_rel (B only, no premise) is the room in lib/B/ReplyLSBArms.v bt_LS_room's form:
     blocks_bytes S + CALL_ROOM_B <= LIVE_MAX + LS3_OVER, LS3_OVER = 66 * 2 ^ 26 + 90495 (v2's LS_OVER plus
     4 * (E_ENT + K0));
   - fr_LS3_pro_oa: ACfn_cf.fr_live_pre -> YCfn_cf.fr_live_pre_b (ReplyB3Base.fr_LS_pro_oa);
   - KF-COUNT (the meter pattern of a Theorem Labs lane, A #6): A's MT := ameter_triv -> a Section Context
     {MT : ameter_ops}, implicit (read off the rules' lf_base / mo_le arguments); fr_LS3_pro_oa, atop_LS3_add_room and
     atop_LS3_write_room state only their room conjuncts (the rows' meter conjuncts are the B instance's, from its count
     clause), atop_LS3_add_open and atop_LS3_write_push_prop take their unread mo_le premise at MT;
   - fr_LS3_pro: as ReplyLSB.fr_LS_pro_b ports A's v2 fr_LS_pro: the meter MT is quantified (A: ameter_triv; fr_LS3
     reads no meter) and fr_live_pre is A's ACfn_cf.fr_live_pre text at CALL_ROOM_B,
     `fun S0 => blocks_bytes S0 + CALL_ROOM_B <= LIVE_MAX`; ls_pro_m is ReplyLSB's (its ls_new_src is B
     W_op_add.v oa_new_src's text);
   - fr_LS3_sat: at the B instance CALL_ROOM_B := YCfn_cf.CALL_ROOM_B (A: at ACfn_cf.CALL_ROOM, the same 2 ^ 33);
   - the Sections take {SK : YI16.sink_head} in their Context: lib/B/ReplyGuardB.v removes the sink classes' hints,
     so lf_base's sink argument comes from the Context (as ReplyLSB.v :144).
   The model names (lfcx, lmod, model_blks, nopen, upd_hs, sm_*, wr_*, set_nth, set_pending, wr_push, ad_open,
   ad_none, oa_first, oa_new_src, oa_cost, lp_grow, lp_vbytes, grow_cap, asrc_blks, alist_blks, ra_new, AREC,
   APARTIAL, ATABLE) are lib/B's (_cut.v, _small.v, _write.v, _add.v, W_op_add.v, W_contract.v, W_rep.v) with A's
   texts and A's values. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB ReplyB3Base.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ------------------------------------------------------------------ v3's constants (A :72-76) *)
Definition E_ENT : Z := 16384.                   (* the relay entry's line buffer at its largest (aentry_ok :124) *)
Definition W_U : Z := 14.                        (* the credit a byte of the relay's unfinished line carries *)
Definition K0 : Z := 256.                        (* per open source: the first vector of its expected and held lists *)
Definition W_OPEN : Z := APARTIAL + E_ENT + K0.  (* the bound's term per open source (v2: APARTIAL) *)

(* the bytes LS v3 may hold above its call room (B only): the potential's bound MB_K * kk + W_OPEN * 4 + MB_C at
   kk < 2 ^ 26, the room fr_LS3_room_rel gives *)
Definition LS3_OVER : Z := 4429275519.
Lemma LS3_OVER_val : LS3_OVER = 66 * 2 ^ 26 + 90495.
Proof. reflexivity. Qed.

Section ls3.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* B's twin of A's ACfn_cf.CALL_ROOM, as ReplyLSB.fr_LS takes it (see the header) *)
Variable CALL_ROOM_B : Z.
(* the meter (KF-COUNT): a Variable, implicit, read off lf_base's argument *)
Context {MT : ameter_ops}.
(* ------------------------------------------------------------------ the extra credit (A :81-119) *)
Local Notation zsum l := (fold_right Z.add 0 l).
(* counts of a block at a point: every Permutation hypothesis and the goal, then linear arithmetic (ReplyLS.v's
   perm_lia, which is local to its Section) *)
Ltac perm_lia :=
  repeat match goal with H : Permutation _ _ |- _ =>
    let H' := fresh "Hc" in pose proof (proj1 (Permutation_count_occ zzdec _ _) H) as H'; clear H end;
  apply (proj2 (Permutation_count_occ zzdec _ _)); let x := fresh "x" in intros x;
  repeat match goal with H : forall _ : Z * Z, count_occ _ _ _ = count_occ _ _ _ |- _ => specialize (H x) end;
  repeat progress (rewrite ?count_occ_app, ?cnt_cons, ?cnt_nil in *); lia.
Definition ent_cred (e : rentry) : Z := Z.max 0 (E_ENT - re_cap e) + W_U * Z.of_nat (length (re_U e)).
Definition lst_cred (l : hlist) : Z := AREC * Z.max 0 (8 - hl_cap l).
Definition slot_cred (o : option hsrc) : Z :=
  match o with Some h => lst_cred (hs_expected h) + lst_cred (hs_held h) | None => 0 end.
Definition ECRED (m : lmod) : Z := zsum (map ent_cred (lm_es m)) + zsum (map slot_cred (lm_hs m)).
Definition PHI3 (m : lmod) : Z := PHI m + ECRED m.

Lemma ent_cred_nonneg : forall e, 0 <= ent_cred e.
Proof. intros e. unfold ent_cred, W_U. lia. Qed.
Lemma lst_cred_nonneg : forall l, 0 <= lst_cred l.
Proof. intros l. unfold lst_cred, AREC. lia. Qed.
Lemma slot_cred_nonneg : forall o, 0 <= slot_cred o.
Proof. intros [h|]; cbn [slot_cred]; [pose proof (lst_cred_nonneg (hs_expected h)); pose proof (lst_cred_nonneg (hs_held h)) |]; lia. Qed.
Lemma ECRED_nonneg : forall m, 0 <= ECRED m.
Proof.
  intros m. unfold ECRED.
  pose proof (zsum_map_nonneg ent_cred (lm_es m) ent_cred_nonneg).
  pose proof (zsum_map_nonneg slot_cred (lm_hs m) slot_cred_nonneg). lia.
Qed.
Lemma PHI3_ge : forall m, bsum (model_blks m) <= PHI3 m.
Proof. intros m. unfold PHI3. pose proof (PHI_ge m). pose proof (ECRED_nonneg m). lia. Qed.
(* the line buffer with its credit is at least E_ENT whatever re_cap is, and exactly E_ENT while 0 <= re_cap <= E_ENT *)
Lemma ent_buf_ge : forall c, E_ENT <= (if c =? 0 then 0 else c) + Z.max 0 (E_ENT - c).
Proof. intros c. unfold E_ENT. destruct (Z.eqb_spec c 0); lia. Qed.
Lemma ent_buf_le : forall c, c <= E_ENT -> (if c =? 0 then 0 else c) + Z.max 0 (E_ENT - c) <= E_ENT.
Proof. intros c Hc. unfold E_ENT in *. destruct (Z.eqb_spec c 0); lia. Qed.
(* a list's vector with its credit is at least AREC * 8 whatever its cap is *)
Lemma lst_vec_ge : forall cap, AREC * 8 <= (if cap =? 0 then 0 else AREC * cap) + AREC * Z.max 0 (8 - cap).
Proof. intros cap. unfold AREC. destruct (Z.eqb_spec cap 0); lia. Qed.


(* ------------------------------------------------------------------ LS v3 (A :122-130) *)
Definition fr_LS3 (cx : lfcx) (t : Z) (m : lmod) (ly : alayout) (S : astate) : Prop :=
  exists rest e0,
    Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) /\
    bsum rest + bsum (input_blks cx) + e0 <= blocks_bytes (c_S cx) /\
    blocks_bytes (c_S cx) + CALL_ROOM_B <= LIVE_MAX /\
    0 <= c_n cx < 2 ^ 26 /\ length (lm_hs m) = 4%nat /\
    4 * npend m <= kk cx m /\
    PHI3 m <= MB_K * kk cx m + W_OPEN * nopen (lm_hs m) + e0 + MB_C.

(* what LS v3 gives at any cut point, for every call room (B only; the form of ReplyLSBArms.v bt_LS_room) *)
Lemma fr_LS3_room_rel : forall cx t m ly S, fr_LS3 cx t m ly S -> blocks_bytes S + CALL_ROOM_B <= LIVE_MAX + LS3_OVER.
Proof.
  intros cx t m ly S (rest & e0 & HP & HR & HE & Hc & Hl & Hnp & HM).
  rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP), !bsum_app.
  pose proof (PHI3_ge m). pose proof (nopen_le4 _ Hl). pose proof (npend_nonneg m).
  assert (Hk : kk cx m <= c_n cx) by (unfold kk; lia).
  assert (E26 : 2 ^ 26 = 67108864) by reflexivity.
  unfold LS3_OVER, MB_K, MB_C, W_OPEN, E_ENT, K0, APARTIAL in *. lia.
Qed.
(* what LS v3 gives at any cut point, to the byte (A :132-141): v2's 4,160,725,633 less 4 * (E_ENT + K0), at a call
   room of at least the B driver's 2 ^ 33 *)
Lemma fr_LS3_room_x : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B ->
  forall cx t m ly S, fr_LS3 cx t m ly S -> blocks_bytes S + 4160659073 <= LIVE_MAX.
Proof.
  intros HCR cx t m ly S H. pose proof (fr_LS3_room_rel cx t m ly S H) as Hr.
  assert (HC : YCfn_cf.CALL_ROOM_B = 8589934592) by reflexivity.
  unfold LS3_OVER in Hr. lia.
Qed.
(* fr_LS_room at v3: 2^31 to spare under LIVE_MAX (A :142-144) *)
Lemma fr_LS3_room : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B ->
  forall cx t m ly S, fr_LS3 cx t m ly S -> blocks_bytes S + ROOM_SPARE <= LIVE_MAX.
Proof. intros HCR cx t m ly S H. pose proof (fr_LS3_room_x HCR cx t m ly S H). unfold ROOM_SPARE. lia. Qed.
Lemma fr_LS3_k : forall cx t m ly S, fr_LS3 cx t m ly S -> 0 <= kk cx m.
Proof. intros cx t m ly S (rest & e0 & _ & _ & _ & _ & _ & Hnp & _). pose proof (npend_nonneg m). lia. Qed.

(* ------------------------------------------------------------------ the rules that keep the model's blocks (A :148-193) *)
Lemma fr_LS3_keep : forall cx t t' m m' ly S,
  model_blks m' = model_blks m -> PHI3 m' = PHI3 m -> nopen (lm_hs m') = nopen (lm_hs m) ->
  length (lm_hs m') = length (lm_hs m) -> npend m' = npend m -> kk cx m <= kk cx m' ->
  fr_LS3 cx t m ly S -> fr_LS3 cx t' m' ly S.
Proof.
  intros cx t t' m m' ly S Hb Hp Ho Hl Hn Hk (rest & e0 & HP & HR & HE & Hc & Hl0 & Hnp & HM).
  exists rest, e0. rewrite Hb, Hp, Ho, Hl, Hn. unfold MB_K in *.
  refine (conj HP (conj HR (conj HE (conj Hc (conj Hl0 (conj _ _)))))); lia.
Qed.
Lemma fr_LS3_k_only : forall cx t t' m m' ly S,
  lm_hs m' = lm_hs m -> lm_es m' = lm_es m -> lm_G m' = lm_G m -> lm_cap m' = lm_cap m -> lm_out m' = lm_out m ->
  lm_k m <= lm_k m' \/ kk cx m <= kk cx m' -> fr_LS3 cx t m ly S -> fr_LS3 cx t' m' ly S.
Proof.
  intros cx t t' m m' ly S E1 E2 E3 E4 E5 Hk H.
  assert (Hb : model_blks m' = model_blks m) by (unfold model_blks; rewrite E1, E2, E3, E4, E5; reflexivity).
  apply (fr_LS3_keep cx t t' m m' ly S Hb); [| rewrite E1; reflexivity | rewrite E1; reflexivity
    | unfold npend; rewrite E1; reflexivity | unfold kk in *; lia | exact H].
  unfold PHI3, PHI, ECRED, pend_bytes, held_bytes, vslack. rewrite Hb, E1, E2. reflexivity.
Qed.
Lemma fr_LS3_upd : forall cx t t' m m' ly S i f,
  lm_hs m' = upd_hs i f (lm_hs m) -> (forall h, asrc_blks (f h) = asrc_blks h) ->
  (forall h, hs_pending (f h) = hs_pending h /\ hs_off (f h) = hs_off h /\ hs_held (f h) = hs_held h /\
     hs_expected (f h) = hs_expected h) ->
  lm_es m' = lm_es m -> lm_G m' = lm_G m -> lm_cap m' = lm_cap m -> lm_out m' = lm_out m ->
  lm_k m <= lm_k m' -> fr_LS3 cx t m ly S -> fr_LS3 cx t' m' ly S.
Proof.
  intros cx t t' m m' ly S i f E1 Hfb Hf E2 E3 E4 E5 Hk H.
  assert (Mg : forall (g : option hsrc -> Z), (forall h, g (Some (f h)) = g (Some h)) -> map g (lm_hs m') = map g (lm_hs m))
    by (intros g Hg; rewrite E1; apply upd_hs_map; exact Hg).
  assert (Hb : model_blks m' = model_blks m).
  { unfold model_blks. rewrite E2, E3, E4, E5, E1, (upd_hs_blks i f (lm_hs m) Hfb). reflexivity. }
  apply (fr_LS3_keep cx t t' m m' ly S Hb).
  - unfold PHI3, PHI, ECRED, pend_bytes, held_bytes, vslack. rewrite Hb, E2.
    rewrite (Mg slot_pend), (Mg slot_held), (Mg slot_vsl), (Mg slot_cred);
      [reflexivity
      | intros h; destruct (Hf h) as (P1 & P2 & P3 & P4); cbn; rewrite P3, P4; reflexivity
      | intros h; destruct (Hf h) as (P1 & P2 & P3 & P4); cbn; rewrite P1, P3, P4; reflexivity
      | intros h; destruct (Hf h) as (P1 & P2 & P3 & P4); cbn; rewrite P3; reflexivity
      | intros h; destruct (Hf h) as (P1 & P2 & P3 & P4); cbn; rewrite P1, P2; reflexivity].
  - rewrite !nopen_zsum, (Mg slot_open); [reflexivity | reflexivity].
  - rewrite E1. apply upd_hs_len.
  - unfold npend. rewrite (Mg slot_npend); [reflexivity | intros h; destruct (Hf h) as (P1 & _); cbn; rewrite P1; reflexivity].
  - unfold kk. lia.
  - exact H.
Qed.

(* the seven, at one (fx, rc) (A :195-237) *)
Lemma fr_LS3_head_nout : forall cx t m ly S, fr_LS3 cx t m ly S -> fr_LS3 cx t (lm_clear_O m) ly S.
Proof. intros cx t m ly S H. exact H. Qed.
Lemma fr_LS3_head_skip : forall cx t m ly S,
  0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (hd_kb cx m) = None -> fr_LS3 cx t m ly S -> fr_LS3 cx (t + 1) (lm_set_k m (hd_k' cx m)) ly S.
Proof.
  intros cx t m ly S _ _ _ _ _ _ H. apply (fr_LS3_k_only cx t (t + 1) m _ ly S); try reflexivity; [| exact H].
  left. exact (hd_k'_ge cx m).
Qed.
Lemma fr_LS3_close : forall cx t m i ly S, fr_LS3 cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  fr_LS3 cx (t + 1) (sm_close cx m i) ly S.
Proof.
  intros cx t m i ly S H _. apply (fr_LS3_upd cx t (t + 1) m _ ly S i upd_closed);
    [reflexivity | intros h; reflexivity | intros h; repeat split | reflexivity | reflexivity | reflexivity | reflexivity
    | exact (sm_kn_ge cx m) | exact H].
Qed.
Lemma fr_LS3_eintr : forall cx t m i ly S, fr_LS3 cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  fr_LS3 cx (t + 1) (sm_eintr cx m i) ly S.
Proof.
  intros cx t m i ly S H _. apply (fr_LS3_upd cx t (t + 1) m _ ly S i upd_eintr);
    [reflexivity | intros h; reflexivity | intros h; repeat split | reflexivity | reflexivity | reflexivity | reflexivity
    | exact (sm_kn_ge cx m) | exact H].
Qed.
Lemma fr_LS3_sendmax : forall cx t m ly S, fr_LS3 cx t m ly S ->
  fr_LS3 cx (t + 1) (sm_sendmax cx m (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0)) ly S.
Proof.
  intros cx t m ly S H. apply (fr_LS3_k_only cx t (t + 1) m _ ly S); try reflexivity; [| exact H].
  left. exact (sm_kn_ge cx m).
Qed.
Lemma fr_LS3_default : forall cx t m ly S, fr_LS3 cx t m ly S -> fr_LS3 cx (t + 1) (sm_default cx m (sm_dg cx m)) ly S.
Proof.
  intros cx t m ly S H. apply (fr_LS3_k_only cx t (t + 1) m _ ly S); try reflexivity; [| exact H].
  left. exact (sm_kn_ge cx m).
Qed.
Lemma fr_LS3_write_skip : forall cx t m ly S, fr_LS3 cx t m ly S -> fr_LS3 cx (t + 1) (wr_skip m (wr_k2 cx m)) ly S.
Proof.
  intros cx t m ly S H. apply (fr_LS3_k_only cx t (t + 1) m _ ly S); try reflexivity; [| exact H].
  right. unfold kk at 2. cbn [lm_k wr_skip]. exact (wr_k2_kk cx m).
Qed.

(* ------------------------------------------------------------------ op_add (A :239-291) *)
Lemma fr_LS3_add_room : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B -> forall cx t m ly S, fr_LS3 cx t m ly S ->
  blocks_bytes S + APARTIAL + ATABLE <= LIVE_MAX.
Proof.
  intros HCR cx t m ly S H. pose proof (fr_LS3_room HCR cx t m ly S H). unfold ROOM_SPARE, APARTIAL, ATABLE in *. lia.
Qed.
Lemma fr_LS3_add_none : forall cx t m ly S, fr_LS3 cx t m ly S -> fr_LS3 cx (t + 1) (ad_none m) ly S.
Proof.
  intros cx t m ly S H. apply (fr_LS3_k_only cx t (t + 1) m _ ly S); try reflexivity; [| exact H].
  left. cbn [ad_none lm_k]. lia.
Qed.
(* op_add opened slot i: the model gains the partial buffer, ECRED gains E_ENT (the new entry) and K0 (the new
   source's two empty lists), the bound gains W_OPEN *)
Lemma fr_LS3_add_open : forall cx t m i q pj ev ly S (ly' : alayout) (S' : astate),
  fr_LS3 cx t m ly S -> oa_first (ad_os (lm_hs m)) = Some i ->
  Permutation (ablocks B ly' S') ((q, APARTIAL) :: ablocks B ly S) ->
  fr_LS3 cx (t + 1) (ad_open m i q pj ev) ly' S'.
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
    pose proof (Zs slot_npend) as Z4. pose proof (Zs slot_open) as Z5. pose proof (Zs slot_cred) as Z6.
    assert (P1 : slot_pend (Some (oa_new_src (100 + lm_nfd m) q pj)) = 0) by reflexivity.
    assert (P2 : slot_held (Some (oa_new_src (100 + lm_nfd m) q pj)) = 0) by reflexivity.
    assert (P3 : slot_vsl (Some (oa_new_src (100 + lm_nfd m) q pj)) = 0) by reflexivity.
    assert (P4 : slot_npend (Some (oa_new_src (100 + lm_nfd m) q pj)) = 0) by reflexivity.
    assert (P5 : slot_open (Some (oa_new_src (100 + lm_nfd m) q pj)) = 1) by reflexivity.
    assert (P6 : slot_cred (Some (oa_new_src (100 + lm_nfd m) q pj)) = K0) by reflexivity.
    assert (N1 : slot_pend None = 0) by reflexivity. assert (N2 : slot_held None = 0) by reflexivity.
    assert (N3 : slot_vsl None = 0) by reflexivity. assert (N4 : slot_npend None = 0) by reflexivity.
    assert (N5 : slot_open None = 0) by reflexivity. assert (N6 : slot_cred None = 0) by reflexivity.
    assert (Eh : zsum (map entry_held (lm_es (ad_open m i q pj ev))) = zsum (map entry_held (lm_es m))).
    { rewrite ad_open_es, map_app, zsum_app. assert (E0 : entry_held (ra_new (100 + lm_nfd m)) = 0) by reflexivity.
      cbn [map fold_right]. lia. }
    assert (Ee : zsum (map ent_cred (lm_es (ad_open m i q pj ev))) = zsum (map ent_cred (lm_es m)) + E_ENT).
    { rewrite ad_open_es, map_app, zsum_app. assert (E0 : ent_cred (ra_new (100 + lm_nfd m)) = E_ENT) by reflexivity.
      cbn [map fold_right]. lia. }
    assert (Eb : bsum (model_blks (ad_open m i q pj ev)) = APARTIAL + bsum (model_blks m))
      by (rewrite (bsum_perm _ _ Hm), bsum_cons; reflexivity).
    split.
    + unfold npend in *. lia.
    + unfold PHI3, PHI, ECRED, pend_bytes, held_bytes, vslack in *. rewrite !nopen_zsum in *. rewrite Eb, Eh, Ee.
      clear - HM Hk Z1 Z2 Z3 Z5 Z6 P1 P2 P3 P5 P6 N1 N2 N3 N5 N6.
      unfold W_OPEN, MB_K, APARTIAL, W_P, W_H, E_ENT, K0 in *. lia.
Qed.

(* ------------------------------------------------------------------ the write arm's room (A :293-312) *)
Lemma fr_LS3_write_room : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B ->
  forall cx t m si h ly S, fr_LS3 cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  (lp_grow (hs_pending h) = true -> lp_vbytes (hs_pending h) < WR_MMAX) /\
  blocks_bytes S + (if lp_grow (hs_pending h) then lp_vbytes (hs_pending h) else 0) + (wr_n cx m + 1) <= LIVE_MAX.
Proof.
  intros HCR cx t m si h ly S H (_ & _ & Hh) Hn.
  pose proof (fr_LS3_room HCR cx t m ly S H) as Hroom. pose proof (fr_LS3_k cx t m ly S H) as Hk0.
  destruct H as (rest & e0 & HP & HR & HE & Hc & Hl & Hnp & HM).
  pose proof (npend_slot m si h Hh) as Hs. pose proof (wr_facts_B cx m Hn) as ((W1 & W2) & _).
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

(* ------------------------------------------------------------------ the write arm's push, at the proposed text (A :314-403) *)
Lemma fr_LS3_write_push : forall cx t m si h (l' : hlist) d ly S ly' S' ev,
  fr_LS3 cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, wr_x cx m)] ->
  hl_cap l' = grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  (lp_grow (hs_pending h) = false -> hl_v l' = hl_v (hs_pending h)) ->
  (forall rest, Permutation (ablocks B ly S)
       ((if lp_grow (hs_pending h) && negb (hl_cap (hs_pending h) =? 0)
         then [(hl_v (hs_pending h), AREC * hl_cap (hs_pending h))] else []) ++ rest) ->
     Permutation (ablocks B ly' S')
       ((d, Z.of_nat (length (wr_x cx m)) + 1) ::
        (if lp_grow (hs_pending h) then [(hl_v l', AREC * hl_cap l')] else []) ++ rest)) ->
  fr_LS3 cx (t + 1) (wr_push m (wr_k2 cx m) si (set_pending h l') ev) ly' S'.
Proof.
  intros cx t m si h l' d ly S ly' S' ev H (_ & _ & Hh) Hn Hrecs Hcap Hv Hlp.
  pose proof (fr_LS3_k cx t m ly S H) as Hk0.
  destruct H as (rest & e0 & HP & HR & HE & Hc & Hl & Hnp & HM).
  pose proof (wr_facts_B cx m Hn) as ((W1 & W2) & Wx).
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
  assert (Ha : asrc_blks h = (hs_partial h, APARTIAL) :: (VL ++ CL) ++ alist_blks (hs_expected h) ++ alist_blks (hs_held h))
    by reflexivity.
  assert (Ha' : asrc_blks h' = (hs_partial h, APARTIAL) :: (VL' ++ CL ++ [dd]) ++ alist_blks (hs_expected h) ++
                  alist_blks (hs_held h))
    by (unfold h', asrc_blks, alist_blks; cbn [set_pending hs_partial hs_pending hs_expected hs_held];
        fold VL'; rewrite Hrecs, map_app; reflexivity).
  pose proof (set_nth_perm slot_blks si (Some h') (Some h) (lm_hs m) Hi) as Hsw. cbn [slot_blks] in Hsw.
  rewrite Ha, Ha' in Hsw.
  assert (HM2 : Permutation (model_blks m' ++ OV) (model_blks m ++ NV ++ [dd])).
  { unfold model_blks, m'. cbn [wr_push lm_G lm_es lm_hs lm_cap lm_out]. perm_lia. }
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
  assert (Zs : forall (g : option hsrc -> Z), zsum (map g (lm_hs m')) + g (Some h) = zsum (map g (lm_hs m)) + g (Some h'))
    by (intros g; exact (set_nth_zsum g si (Some h') (Some h) (lm_hs m) Hi)).
  pose proof (Zs slot_pend) as Z1. pose proof (Zs slot_held) as Z2. pose proof (Zs slot_vsl) as Z3.
  pose proof (Zs slot_npend) as Z4. pose proof (Zs slot_open) as Z5. pose proof (Zs slot_cred) as Z6.
  cbn [slot_pend slot_held slot_vsl slot_npend slot_open slot_cred h' set_pending hs_pending hs_off hs_held hs_expected]
    in Z1, Z2, Z3, Z4, Z5, Z6.
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
    + unfold PHI3, PHI, ECRED, pend_bytes, held_bytes, vslack in *. rewrite !nopen_zsum in *. rewrite Hk', Hkm in *.
      assert (E1 : lm_es m' = lm_es m) by reflexivity. rewrite E1.
      unfold dd in Eb. cbn [snd] in Eb. rewrite Hb1 in Z1.
      unfold W_OPEN, MB_K, W_P, W_H, APARTIAL, E_ENT, K0 in *. lia.
Qed.

(* ------------------------------------------------------------------ the prologue (A :405-453) *)
(* LS_pro_oa does not name LS: fr_LS_pro_oa (ReplyB3Base.v, A's ReplyLS.v:551) is the rule at v3 as it is; restated
   for the family *)
Lemma fr_LS3_pro_oa : forall XM_LIB RLO RHI G_fr cx (S2 : astate) (pos : Z),
  lf_base B MT XM_LIB RLO RHI YCfn_cf.fr_live_pre_b G_fr cx ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) ->
  blocks_bytes S2 + APARTIAL + ATABLE <= LIVE_MAX.
Proof. exact (fr_LS_pro_oa B). Qed.
(* LS at the first head, at the proposed text of fr_LS_pro (ReplyLS.v:571, the pro arm's text; B: ReplyLSB.v
   fr_LS_pro_b's form, the meter quantified, fr_live_pre at CALL_ROOM_B): the same premises; ECRED is E_ENT for the
   fresh entry ra_new 100 and K0 for the one open source, the bound's W_OPEN for it *)
Lemma fr_LS3_pro : forall MT XM_LIB RLO RHI G_fr cx q T' pj c O cap out ly S,
  lf_base B MT XM_LIB RLO RHI (fun S0 => blocks_bytes S0 + CALL_ROOM_B <= LIVE_MAX) G_fr cx ->
  (exists T0 rest0, Permutation (ablocks B (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) /\
     ((T0 = 0 /\ Permutation (ablocks B ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks B ly S) ((q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))))) ->
  fr_LS3 cx 0 (ls_pro_m q T' pj c O cap out) ly S.
Proof.
  intros MT0 XM_LIB RLO RHI G_fr cx q T' pj c O cap out ly S (_ & Hpre) (T0 & rest0 & HE0 & Hcase).
  destruct Hpre as (_ & _ & _ & _ & Hd & _ & _ & _ & Hlive & _). cbv beta in Hlive.
  assert (Hc : 0 <= c_n cx < 2 ^ 26) by (destruct Hd as [(Hd & _) | (Hd & _)]; lia).
  assert (Hmb : model_blks (ls_pro_m q T' pj c O cap out) = (T', ATABLE) :: (q, APARTIAL) :: aout_blks cap out)
    by reflexivity.
  assert (Ep : pend_bytes (ls_pro_m q T' pj c O cap out) = 0) by reflexivity.
  assert (Eh : held_bytes (ls_pro_m q T' pj c O cap out) = 0) by reflexivity.
  assert (Ev : vslack (ls_pro_m q T' pj c O cap out) = 0) by reflexivity.
  assert (Ec : ECRED (ls_pro_m q T' pj c O cap out) = E_ENT + K0) by reflexivity.
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
    + unfold PHI3, PHI. rewrite Hmb, Ep, Eh, Ev, Ec, Eo, Ek. rewrite !bsum_cons. cbn [snd].
      unfold W_OPEN, MB_K, MB_C, W_P, W_H, APARTIAL, ATABLE, E_ENT, K0. lia.
  - subst T'. rewrite (proj2 (Z.eqb_neq _ _) HT0) in HE0. cbv beta iota in HE0.
    exists rest0, (ATABLE + bsum (aout_blks cap out)).
    split; [rewrite Hmb; perm_lia |].
    split; [rewrite Eb0, (bsum_perm _ _ HE0), !bsum_app, bsum_cons, ?bsum_nil; cbn [snd]; lia |].
    split; [exact Hlive | split; [exact Hc | split; [reflexivity | split]]].
    + rewrite En, Ek. lia.
    + unfold PHI3, PHI. rewrite Hmb, Ep, Eh, Ev, Ec, Eo, Ek. rewrite !bsum_cons. cbn [snd].
      unfold W_OPEN, MB_K, MB_C, W_P, W_H, APARTIAL, ATABLE, E_ENT, K0. lia.
Qed.
End ls3.

(* ------------------------------------------------------------------ fr_LS3 is satisfiable at a concrete state (A :456-508) *)
(* The first head's shape (ls_pro_m): a real 1-byte input block, the relay's table, one open source holding a fresh
   entry ra_new 100 and its 6000-byte partial buffer, no out buffer (cap 0); the allocator state holds exactly those
   three blocks (c_S cx = S, so the entry's live bytes are the same three), e0 = 0, t = 0.  The witnesses are closed
   terms; the addresses are sptr_addr B ly of the chunks' user pointers (B is the instance's symbol table, LS's own
   parameter).  B: at the B instance's call room CALL_ROOM_B := YCfn_cf.CALL_ROOM_B (2 ^ 33, A's ACfn_cf.CALL_ROOM). *)
Section sat3.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Definition ls3_ly : alayout := ALayout 0 0 0 0 0 0 0 0 0 0 0 0 [] [] 0 [] (0, 0) (fun _ => 0).
(* the three live chunks: the input block (1 byte), the relay's table, the splitter's buffer *)
Definition ls3_k0 : YG00.chunk := YG00.mkChunk (YG00.PPrim 0) 1 YG00.CAllocated.
Definition ls3_k1 : YG00.chunk := YG00.mkChunk (YG00.PPrim 4096) ATABLE YG00.CAllocated.
Definition ls3_k2 : YG00.chunk := YG00.mkChunk (YG00.PPrim 16384) APARTIAL YG00.CAllocated.
Definition ls3_S : astate := YG00.set_chunks [ls3_k0; ls3_k1; ls3_k2] YG00.init_state.
(* the world: nothing hidden, no allowance (w_H8 trivially: w_H is constant); the model: LPS's mkModel over empty maps
   (as YK02.v:156 vm_model) *)
Lemma ls3_Hoff : H_off_segments segs (fun _ => false).
Proof. intros a Ha. discriminate. Qed.
Definition ls3_W : world segs := mkW segs (fun _ => false) [] ls3_Hoff (Forall_nil _) (fun _ _ => eq_refl).
Definition ls3_vm : VmMaps :=
  mkVmMapsFull [] [] [] (Z_to_bv 64 0) (Z_to_bv 64 0) 0 (Z_to_bv 64 0) (Z_to_bv 64 0).
Definition ls3_md : Model := mkModel [] ls3_vm IEof [] None None None.
Definition ls3_p : Z := sptr_addr B ls3_ly (YG00.ck_user ls3_k0).
Definition ls3_G : Z := sptr_addr B ls3_ly (YG00.ck_user ls3_k1).
Definition ls3_q : Z := sptr_addr B ls3_ly (YG00.ck_user ls3_k2).
Definition ls3_cx : lfcx (rc := rc) :=
  LFCX ls3_ly ls3_S ls3_W bvmap_empty (fun _ => None) ls3_md ls3_p 1 [] 0.
(* the model: the first head's (ls_pro_m) with table ls3_G, partial buffer ls3_q, nothing read, no out buffer *)
Definition ls3_m : lmod := ls_pro_m ls3_q ls3_G [] (CTL 3 0 0 0 0) [] 0 0.

Lemma fr_LS3_sat : exists (cx : lfcx (rc := rc)) t m ly S, fr_LS3 B YCfn_cf.CALL_ROOM_B cx t m ly S.
Proof.
  exists ls3_cx, 0, ls3_m, ls3_ly, ls3_S, [], 0.
  assert (EA : ablocks B ls3_ly ls3_S = input_blks ls3_cx ++ model_blks ls3_m ++ []) by reflexivity.
  assert (Hbb : blocks_bytes ls3_S = 1 + ATABLE + APARTIAL) by (vm_compute; reflexivity).
  assert (Hin : bsum (input_blks ls3_cx) = 1) by reflexivity.
  assert (Hrest : bsum (@nil (Z * Z)) = 0) by reflexivity.
  assert (HS : c_S ls3_cx = ls3_S) by reflexivity.
  assert (Hn : c_n ls3_cx = 1) by reflexivity.
  assert (HC : YCfn_cf.CALL_ROOM_B = 8589934592) by reflexivity.
  assert (HL : LIVE_MAX = 17179869184) by reflexivity.
  assert (En : npend ls3_m = 0) by reflexivity.
  assert (Ek : kk ls3_cx ls3_m = 0) by reflexivity.
  assert (Eo : nopen (lm_hs ls3_m) = 1) by reflexivity.
  (* PHI3 at the witness: the table and the partial buffer, E_ENT for the fresh entry, K0 for the open source *)
  assert (Ep : PHI3 ls3_m = ATABLE + APARTIAL + E_ENT + K0) by reflexivity.
  rewrite EA, HS, Hbb, Hn, Hin, Hrest, HC, HL, En, Ek, Eo, Ep.
  split; [apply Permutation_refl|].
  unfold W_OPEN, MB_K, MB_C, ATABLE, APARTIAL, E_ENT, K0.
  refine (conj _ (conj _ (conj _ (conj eq_refl (conj _ _))))); lia.
Qed.
End sat3.

(* ------------------------------------------------------------------ the rules in ReplyATop.v's family form (A :510-580) *)
Section fam3.
Variable B : asyms.
Variable CALL_ROOM_B : Z.
(* the meter (KF-COUNT): a Variable, implicit, read off the rules' mo_le arguments *)
Context {MT : ameter_ops}.
Variable RIf : forall (fx : YK11.FPState) (rc : YM05.RunCeil), lfcx (rc := rc) -> Z -> lmod -> Prop.
Local Notation LSf := (fun (fx : YK11.FPState) (rc : YM05.RunCeil) => fr_LS3 (rc := rc) B CALL_ROOM_B).
Lemma atop_LS3_head_nout : forall (fx : YK11.FPState) (rc : YM05.RunCeil) cx t m ly S,
  LSf fx rc cx t m ly S -> LSf fx rc cx t (lm_clear_O m) ly S.
Proof. intros fx rc. exact (fr_LS3_head_nout (rc := rc) B CALL_ROOM_B). Qed.
Lemma atop_LS3_head_skip : forall (fx : YK11.FPState) (rc : YM05.RunCeil) cx t m ly S,
  0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (hd_kb cx m) = None -> LSf fx rc cx t m ly S -> LSf fx rc cx (t + 1) (lm_set_k m (hd_k' cx m)) ly S.
Proof. intros fx rc. exact (fr_LS3_head_skip (rc := rc) B CALL_ROOM_B). Qed.
Lemma atop_LS3_add_room : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B -> forall (fx : YK11.FPState) (rc : YM05.RunCeil) cx t m ly S,
  LSf fx rc cx t m ly S -> RIf fx rc cx t m -> ad_at_op cx m ->
  blocks_bytes S + APARTIAL + ATABLE <= LIVE_MAX.
Proof.
  intros HCR fx rc cx t m ly S H _ _.
  exact (fr_LS3_add_room (rc := rc) B CALL_ROOM_B HCR cx t m ly S H).
Qed.
Lemma atop_LS3_add_open : forall (fx : YK11.FPState) (rc : YM05.RunCeil) cx t m i q pj ev ly S
  (ly' : alayout) (S' : astate),
  LSf fx rc cx t m ly S -> RIf fx rc cx t m -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = Some i ->
  mo_le MT S S' (oa_cost MT) -> Permutation (ablocks B ly' S') ((q, APARTIAL) :: ablocks B ly S) ->
  LSf fx rc cx (t + 1) (ad_open m i q pj ev) ly' S'.
Proof. intros fx rc cx t m i q pj ev ly S ly' S' H _ _ Hf _ HP. exact (fr_LS3_add_open (rc := rc) B CALL_ROOM_B cx t m i q pj ev ly S ly' S' H Hf HP). Qed.
Lemma atop_LS3_add_none : forall (fx : YK11.FPState) (rc : YM05.RunCeil) cx t m ly S,
  LSf fx rc cx t m ly S -> RIf fx rc cx t m -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = None ->
  LSf fx rc cx (t + 1) (ad_none m) ly S.
Proof. intros fx rc cx t m ly S H _ _ _. exact (fr_LS3_add_none (rc := rc) B CALL_ROOM_B cx t m ly S H). Qed.
Lemma atop_LS3_close : forall (fx : YK11.FPState) (rc : YM05.RunCeil) cx t m i ly S, LSf fx rc cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  LSf fx rc cx (t + 1) (sm_close cx m i) ly S.
Proof. intros fx rc. exact (fr_LS3_close (rc := rc) B CALL_ROOM_B). Qed.
Lemma atop_LS3_eintr : forall (fx : YK11.FPState) (rc : YM05.RunCeil) cx t m i ly S, LSf fx rc cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  LSf fx rc cx (t + 1) (sm_eintr cx m i) ly S.
Proof. intros fx rc. exact (fr_LS3_eintr (rc := rc) B CALL_ROOM_B). Qed.
Lemma atop_LS3_sendmax : forall (fx : YK11.FPState) (rc : YM05.RunCeil) cx t m ly S, LSf fx rc cx t m ly S ->
  LSf fx rc cx (t + 1) (sm_sendmax cx m (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0)) ly S.
Proof. intros fx rc. exact (fr_LS3_sendmax (rc := rc) B CALL_ROOM_B). Qed.
Lemma atop_LS3_default : forall (fx : YK11.FPState) (rc : YM05.RunCeil) cx t m ly S,
  LSf fx rc cx t m ly S -> LSf fx rc cx (t + 1) (sm_default cx m (sm_dg cx m)) ly S.
Proof. intros fx rc. exact (fr_LS3_default (rc := rc) B CALL_ROOM_B). Qed.
Lemma atop_LS3_write_skip : forall (fx : YK11.FPState) (rc : YM05.RunCeil) cx t m ly S,
  LSf fx rc cx t m ly S -> LSf fx rc cx (t + 1) (wr_skip m (wr_k2 cx m)) ly S.
Proof. intros fx rc. exact (fr_LS3_write_skip (rc := rc) B CALL_ROOM_B). Qed.
Lemma atop_LS3_write_room : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B ->
  forall (fx : YK11.FPState) (rc : YM05.RunCeil) cx t m si h ly S,
  LSf fx rc cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  (lp_grow (hs_pending h) = true -> lp_vbytes (hs_pending h) < WR_MMAX) /\
  blocks_bytes S + (if lp_grow (hs_pending h) then lp_vbytes (hs_pending h) else 0) + (wr_n cx m + 1) <= LIVE_MAX.
Proof.
  intros HCR fx rc cx t m si h ly S H Hp Hn.
  exact (fr_LS3_write_room (rc := rc) B CALL_ROOM_B HCR cx t m si h ly S H Hp Hn).
Qed.
Lemma atop_LS3_write_push_prop : forall (fx : YK11.FPState) (rc : YM05.RunCeil) cx t m si h (l' : hlist) d ev ly S ly' S',
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
  mo_le MT S S' (lp_cost MT (hs_pending h) (wr_n cx m)) ->
  LSf fx rc cx (t + 1) (wr_push m (wr_k2 cx m) si (set_pending h l') ev) ly' S'.
Proof.
  intros fx rc cx t m si h l' d ev ly S ly' S' H Hp Hn Hr Hc Hv HP _.
  exact (fr_LS3_write_push (rc := rc) B CALL_ROOM_B cx t m si h l' d ly S ly' S' ev H Hp Hn Hr Hc Hv HP).
Qed.
End fam3.
