(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* B's out-buffer conjunct: ReplyLS3o.v's fr_OUT (A, row B1c) ported to B's fr_LS (lib/B/ReplyLSB.v:182-189), with
   the twin of every B rule that concludes LS, and the instance at CR := YCfn_cf.CALL_ROOM_B.
   proves no function (kind: invariant lemma).

   THE SHAPE, as in A (lib/A/ReplyLS3o.v):
     XB cx m S   := blocks_bytes (c_S cx) - blocks_bytes S + bsum (model_blks m)
     MASS m      := sum over the relay's entries of (|re_U e| + sum over its keys of (|key| + 7)) + pend_bytes m
     fr_OUT OM cx t m ly S := 0 <= lm_cap m /\ 0 <= XB /\ lm_cap m <= XB + OM /\ MASS m <= 65535 * t
   OM is a parameter, as A keeps it; a Theorem Labs lane's ruled value is OUT_MAX4 = 4 * (OPS_MAX - 1) * 65,535 =
   133,953,540 (2026-10-30 01:47Z; a8's 66,976,770 of ACfn_cf.v:57 at a389032ec36 is OUT_MAX3 here, kept for the
   citation).  A key counts at |key| + 7, the cost of the BEGIN line that made it: ou_gesture_begin_key reads
   RelayModel.gesture, which B shares with A (lib/Prog/RelayModel.v), so the key model's fact ports unchanged.

   THE RULES.  B's LS-concluding rules at this tree (k3's 61e610e6176) are the two heads (ReplyLSB.v:291, :293),
   the prologue (ReplyLSB.v:243 fr_LS_pro_b) and the event step (ReplyLSBArms.v:267 LS_event_step_T, instance
   :695 LS_event_step_B).  B has no drain / remove / gone LS step yet, so this file has no twin for those; when
   they land, A's lib/A/ReplyLS3o.v twins (fr_OUT_drain_step_p, fr_OUT_rm_step_p) and lib/A/ReplyLS3oGn.v
   (fr_OUT_gone_end) are the texts to port. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT ListTr RelayRunF send_line_b_c gesture_end_b_c gestures_end_b_c relay_remove_b_c
  relay_instance_gone_b_c drain_b_c RelayCap SlotReads.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
  W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB ReplyLSBArms ReplyLSBTrPeak.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Notation zsum l := (fold_right Z.add 0 l).

(* ================================================================== the constants (A ReplyLS3o.v:95-105) *)
(* a8's value, a working branch a389032ec36 lib/A/ACfn_cf.v:57 *)
Definition OUT_MAX3 : Z := 66976770.
(* a Theorem Labs lane's ruling 2026-10-30 01:47Z, after row B1c found a8's too small for the remove / gone arms *)
Definition OUT_MAX4 : Z := 133953540.
(* the bytes one write operation adds: fuzz_take (fuzz_u16 (&in), ..), fuzz_reply.c:705 *)
Definition WMAX : Z := 65535.
Lemma OUT_MAX3_src : OUT_MAX3 = 2 * (OPS_MAX - 1) * WMAX.
Proof. reflexivity. Qed.
Lemma OUT_MAX4_src : OUT_MAX4 = 4 * (OPS_MAX - 1) * WMAX.
Proof. reflexivity. Qed.

(* ================================================================== the key model (A ReplyLS3o.v:110-150) *)
Definition kw7 (x : list Z) : Z := Z.of_nat (length x) + 7.
Definition kw7s (T : list (list Z)) : Z := zsum (map kw7 T).
Lemma kw7_nonneg : forall x, 0 <= kw7 x.
Proof. intros x. unfold kw7. lia. Qed.
Lemma kw7s_nonneg : forall T, 0 <= kw7s T.
Proof. intros T. apply bt_zsum_map_nonneg. exact kw7_nonneg. Qed.
(* an END line (|key| + 5) is within its key's weight: gesture reads a begin line as `<key> begin`, so the key is
   the line less " begin" and |key| + 7 is that line's own cost with its NUL *)
Lemma ou_gesture_begin_key : forall l x, gesture l = Some (GBegin, x) ->
  Z.of_nat (length x) + 6 = Z.of_nat (length l).
Proof.
  intros l x H. unfold gesture in H.
  destruct (list_eqb (firstn 13 l) K_GESTURE && Z.eqb (nth 13 l 0) SPACE && Nat.ltb 13 (length l)); [|discriminate].
  destruct (last_space_from 0 l) as [j|]; [|discriminate].
  destruct (Nat.ltb 13 j); [|discriminate].
  destruct (list_eqb (skipn (S j) l) W_BEGIN) eqn:Eb.
  - assert (Ex : firstn j l = x) by (injection H as E; exact E).
    rewrite <- Ex.
    unfold list_eqb in Eb. destruct (list_eq_dec Z.eq_dec (skipn (S j) l) W_BEGIN) as [E|_]; [|discriminate].
    assert (L5 : length (skipn (S j) l) = 5%nat) by (rewrite E; reflexivity).
    rewrite length_skipn in L5.
    assert (Hj : (S j + 5 <= length l)%nat) by lia.
    rewrite length_firstn. lia.
  - destruct (list_eqb (skipn (S j) l) W_END); discriminate.
Qed.
Lemma ou_keys_total_kw7 : forall ks, gestures_end_b_c.keys_total ks <= kw7s (drain_b_c.keys_texts ks).
Proof.
  induction ks as [|k ks IH]; [cbn [kw7s map fold_right]; reflexivity|].
  change (gestures_end_b_c.keys_total (k :: ks)) with
    (Z.of_nat (length (gestures_end_b_c.key_text k)) + 5 + gestures_end_b_c.keys_total ks).
  change (drain_b_c.keys_texts (k :: ks)) with
    (bzs (gestures_end_b_c.key_text k) :: drain_b_c.keys_texts ks).
  unfold kw7s, kw7 in *. cbn [map fold_right]. rewrite RelayCap.rc_length_bzs. lia.
Qed.

(* ================================================================== MASS: what one operation may still send *)
Definition ent_mass (e : rentry) : Z :=
  Z.of_nat (length (re_U e)) + kw7s (drain_b_c.keys_texts (re_keys e)).
Lemma ent_mass_nonneg : forall e, 0 <= ent_mass e.
Proof. intros e. unfold ent_mass. pose proof (kw7s_nonneg (drain_b_c.keys_texts (re_keys e))). lia. Qed.
Lemma ou_keys_total_mass : forall e, gestures_end_b_c.keys_total (re_keys e) <= ent_mass e.
Proof. intros e. unfold ent_mass. pose proof (ou_keys_total_kw7 (re_keys e)). lia. Qed.
Definition MASSe (es : list rentry) : Z := zsum (map ent_mass es).
Definition MASS (m : lmod) : Z := MASSe (lm_es m) + pend_bytes m.
Lemma MASSe_nonneg : forall es, 0 <= MASSe es.
Proof. intros es. apply bt_zsum_map_nonneg. exact ent_mass_nonneg. Qed.
Lemma MASS_nonneg : forall m, 0 <= MASS m.
Proof.
  intros m. unfold MASS. pose proof (MASSe_nonneg (lm_es m)).
  assert (0 <= pend_bytes m) by (apply bt_zsum_map_nonneg; exact bt_slot_pend_nonneg). lia.
Qed.

(* ================================================================== fr_OUT *)
Section bo.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable OM : Z.

Definition XB (cx : lfcx) (m : lmod) (S : astate) : Z :=
  blocks_bytes (c_S cx) - blocks_bytes S + bsum (model_blks m).
Definition fr_OUT (cx : lfcx) (t : Z) (m : lmod) (ly : alayout) (S : astate) : Prop :=
  0 <= lm_cap m /\ 0 <= XB cx m S /\ lm_cap m <= XB cx m S + OM /\ MASS m <= WMAX * t.

Lemma bo_xb_perm : forall cx m ly S rest,
  Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
  XB cx m S = blocks_bytes (c_S cx) - bsum (input_blks cx) - bsum rest.
Proof.
  intros cx m ly S rest HP. unfold XB.
  rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP), !bsum_app. lia.
Qed.
Lemma bo_xb_same_rest : forall cx m ly S m' ly' S' rest,
  Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ model_blks m' ++ rest) ->
  XB cx m' S' = XB cx m S.
Proof.
  intros cx m ly S m' ly' S' rest HP HP'.
  rewrite (bo_xb_perm cx m ly S rest HP), (bo_xb_perm cx m' ly' S' rest HP'). reflexivity.
Qed.

(* ---------------------------------------------------------------- the keep rules *)
Lemma fr_OUT_keep : forall cx t t' m m' ly S,
  model_blks m' = model_blks m -> lm_cap m' = lm_cap m -> MASS m' <= MASS m -> t <= t' ->
  fr_OUT cx t m ly S -> fr_OUT cx t' m' ly S.
Proof.
  intros cx t t' m m' ly S Hb Hc Hm Ht (O1 & O2 & O3 & O4).
  unfold fr_OUT, XB in *. rewrite Hb, Hc. unfold WMAX in *. repeat split; try lia.
Qed.
Lemma fr_OUT_k_only : forall cx t t' m m' ly S,
  lm_hs m' = lm_hs m -> lm_es m' = lm_es m -> lm_G m' = lm_G m -> lm_cap m' = lm_cap m -> lm_out m' = lm_out m ->
  t <= t' -> fr_OUT cx t m ly S -> fr_OUT cx t' m' ly S.
Proof.
  intros cx t t' m m' ly S E1 E2 E3 E4 E5 Ht H.
  apply (fr_OUT_keep cx t t' m m' ly S); [| exact E4 | | exact Ht | exact H].
  - unfold model_blks. rewrite E1, E2, E3, E4, E5. reflexivity.
  - unfold MASS, MASSe, pend_bytes. rewrite E1, E2. lia.
Qed.

(* ---------------------------------------------------------------- SEG_HEAD's two (ReplyLSB.v:291, :293) *)
Lemma fr_OUT_head_nout_b : forall cx t m ly S, fr_OUT cx t m ly S -> fr_OUT cx t (lm_clear_O m) ly S.
Proof. intros cx t m ly S H. apply (fr_OUT_k_only cx t t m _ ly S); try reflexivity; try lia; exact H. Qed.
Lemma fr_OUT_head_skip_b : forall cx t m ly S,
  fr_OUT cx t m ly S -> fr_OUT cx (t + 1) (lm_set_k m (hd_k' cx m)) ly S.
Proof. intros cx t m ly S H. apply (fr_OUT_k_only cx t (t + 1) m _ ly S); try reflexivity; try lia; exact H. Qed.

(* ---------------------------------------------------------------- the first head (ReplyLSB.v:243 fr_LS_pro_b) *)
Lemma fr_OUT_pro_b : forall cx q T' pj c O cap out ly S,
  0 <= cap -> 0 <= OM ->
  (exists T0 rest0, Permutation (ablocks B (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) /\
     ((T0 = 0 /\ Permutation (ablocks B ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks B ly S) ((q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))))) ->
  fr_OUT cx 0 (ls_pro_m q T' pj c O cap out) ly S.
Proof.
  intros cx q T' pj c O cap out ly S Hc HOM (T0 & rest0 & HE0 & Hcase).
  set (m := ls_pro_m q T' pj c O cap out).
  assert (EC : lm_cap m = cap) by reflexivity.
  assert (EM : bsum (model_blks m) = ATABLE + APARTIAL + cap).
  { assert (Hmb : model_blks m = (T', ATABLE) :: (q, APARTIAL) :: aout_blks cap out) by reflexivity.
    rewrite Hmb, !bsum_cons, (bt_bsum_aout_eq cap out Hc). cbn [snd]. lia. }
  assert (EB : blocks_bytes S = blocks_bytes (c_S cx) + (if T0 =? 0 then ATABLE else 0) + APARTIAL).
  { destruct Hcase as [(HT0 & HP) | (HT0 & HT' & HP)].
    - subst T0. rewrite Z.eqb_refl.
      rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP), !bsum_cons,
        <- (blocks_bytes_bsum B (c_ly cx) (c_S cx)). cbn [snd]. lia.
    - rewrite (proj2 (Z.eqb_neq _ _) HT0).
      rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP), !bsum_cons,
        <- (blocks_bytes_bsum B (c_ly cx) (c_S cx)). cbn [snd]. lia. }
  assert (EX : XB cx m S = (if T0 =? 0 then 0 else ATABLE) + cap)
    by (unfold XB; rewrite EM, EB; destruct (T0 =? 0); lia).
  assert (EMass : MASS m = 0) by reflexivity.
  unfold fr_OUT. rewrite EC, EX, EMass. unfold ATABLE in *.
  destruct (T0 =? 0); repeat split; lia.
Qed.

(* ---------------------------------------------------------------- the event arm's step (ReplyLSBArms.v:267) *)
(* one event sends one line of at most 65,536 bytes (fuzz_u16), so g_out grows to at most 131,072 *)
Lemma bo_ev_len : forall cx m e, ev_evt cx m e -> re_len e <= 65536.
Proof.
  intros cx m e (He & _). unfold re_len, ev_len, ev_u16 in *.
  pose proof (sm_in_byte_rng cx (lm_k m + 1)). pose proof (sm_in_byte_rng cx (lm_k m + 2)).
  destruct (2 <=? c_n cx - lm_k m - 1), (1 <=? c_n cx - lm_k m - 1); lia.
Qed.
Lemma fr_OUT_event_step_b : forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out' (ly1 ly2 : alayout) q,
  fr_OUT cx t m ly S -> ev_evt cx m e ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> 0 <= lm_cap m ->
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, re_len e)] ->
  (exists rest, Permutation (ablocks B ly1 S1) (aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly2 S2)
       (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) out' ++ rest)) ->
  (exists l1 l2, ablocks B ly2 S2 = l1 ++ (q, re_len e) :: l2 /\ ablocks B ly3 S3 = l1 ++ l2) ->
  131072 <= OM ->
  fr_OUT cx (t + 1) (ev_step cx m e v out') ly3 S3.
Proof.
  intros cx t m ly S S1 S2 S3 ly3 e v out' ly1 ly2 q (U1 & U2 & U3 & U4) HE Hk HO Hc0 Hm HRR Hf HOM.
  destruct HRR as (restR & HR1 & HR2). destruct Hf as (l1 & l2 & Hf2 & Hf3).
  set (cap' := sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) in *.
  set (m' := ev_step cx m e v out') in *.
  assert (ECap : lm_cap m' = cap') by reflexivity.
  (* g_capout: at most twice one line *)
  assert (HO0 : Z.of_nat (length (lm_O m)) = 0) by (rewrite HO; reflexivity).
  assert (Hcge : lm_cap m <= cap').
  { unfold cap', sl_cap.
    exact (proj2 (tp_send_line (sl_live (lm_c m) (re_len e)) (lm_mx m) (Z.of_nat (length (lm_O m)))
                   (lm_cap m) (re_len e) 0 RelayRunF.adr0 Hc0)). }
  assert (Hcle : cap' <= Z.max (lm_cap m) (2 * 65536)).
  { pose proof (bt_cap_le (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) as Hle.
    pose proof (bo_ev_len cx m e HE) as Hlen. unfold cap'. lia. }
  assert (Hc0' : 0 <= cap') by lia.
  (* XB: the event's block is malloc'd and freed, and g_out's bytes move with its capacity *)
  assert (EB1 : blocks_bytes S1 = blocks_bytes S + re_len e) by exact (bt_malloc_bb B ly S ly1 S1 q (re_len e) Hm).
  assert (EB2 : blocks_bytes S2 = blocks_bytes S1 - bsum (aout_blks (lm_cap m) (lm_out m)) +
                                  bsum (aout_blks cap' out')).
  { rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ HR2), (blocks_bytes_bsum B ly1 S1), (bsum_perm _ _ HR1),
      !bsum_app. lia. }
  assert (EB3 : blocks_bytes S3 = blocks_bytes S2 - re_len e).
  { rewrite (blocks_bytes_bsum B ly3 S3), (blocks_bytes_bsum B ly2 S2), Hf2, Hf3, bsum_app, bsum_app, bsum_cons.
    cbn [snd]. lia. }
  assert (EM : bsum (model_blks m') = bsum (model_blks m) - bsum (aout_blks (lm_cap m) (lm_out m)) +
                                      bsum (aout_blks cap' out')).
  { rewrite (bt_model_blks m'), (bt_model_blks m), !bsum_app.
    assert (Ep : bt_pfx m' = bt_pfx m) by reflexivity. rewrite Ep.
    assert (Ec : lm_cap m' = cap') by reflexivity. assert (Eo : lm_out m' = out') by reflexivity.
    rewrite Ec, Eo. lia. }
  assert (EX : XB cx m' S3 = XB cx m S) by (unfold XB; lia).
  assert (EMass : MASS m' = MASS m) by reflexivity.
  unfold fr_OUT in *. rewrite EX, ECap. unfold WMAX in *. repeat split; try lia.
Qed.
End bo.

(* ================================================================== the B instance (CR := CALL_ROOM_B) *)
Section binst.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* a Theorem Labs lane's ruled OUT_MAX covers one event's 131,072 with room to spare *)
Lemma bo_OUT_MAX4_ev : 131072 <= OUT_MAX4.
Proof. unfold OUT_MAX4. lia. Qed.

Lemma LS_head_nout_BO : forall cx t m ly S,
  fr_OUT OUT_MAX4 cx t m ly S -> fr_OUT OUT_MAX4 cx t (lm_clear_O m) ly S.
Proof. exact (fr_OUT_head_nout_b OUT_MAX4). Qed.
Lemma LS_head_skip_BO : forall cx t m ly S,
  fr_OUT OUT_MAX4 cx t m ly S -> fr_OUT OUT_MAX4 cx (t + 1) (lm_set_k m (hd_k' cx m)) ly S.
Proof. exact (fr_OUT_head_skip_b OUT_MAX4). Qed.
Lemma LS_pro_BO : forall cx q T' pj c O cap out ly S,
  0 <= cap ->
  (exists T0 rest0, Permutation (ablocks B (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) /\
     ((T0 = 0 /\ Permutation (ablocks B ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks B ly S) ((q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))))) ->
  fr_OUT OUT_MAX4 cx 0 (ls_pro_m q T' pj c O cap out) ly S.
Proof.
  intros cx q T' pj c O cap out ly S Hc HE.
  exact (fr_OUT_pro_b B OUT_MAX4 cx q T' pj c O cap out ly S Hc ltac:(unfold OUT_MAX4; lia) HE).
Qed.
Lemma LS_event_step_BO : forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out' (ly1 ly2 : alayout) q,
  fr_OUT OUT_MAX4 cx t m ly S -> ev_evt cx m e ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> 0 <= lm_cap m ->
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, re_len e)] ->
  (exists rest, Permutation (ablocks B ly1 S1) (aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly2 S2)
       (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) out' ++ rest)) ->
  (exists l1 l2, ablocks B ly2 S2 = l1 ++ (q, re_len e) :: l2 /\ ablocks B ly3 S3 = l1 ++ l2) ->
  fr_OUT OUT_MAX4 cx (t + 1) (ev_step cx m e v out') ly3 S3.
Proof.
  intros cx t m ly S S1 S2 S3 ly3 e v out' ly1 ly2 q HOU HE Hk HO Hc0 Hm HRR Hf.
  exact (fr_OUT_event_step_b B OUT_MAX4 cx t m ly S S1 S2 S3 ly3 e v out' ly1 ly2 q HOU HE Hk HO Hc0 Hm HRR Hf
           bo_OUT_MAX4_ev).
Qed.
End binst.
