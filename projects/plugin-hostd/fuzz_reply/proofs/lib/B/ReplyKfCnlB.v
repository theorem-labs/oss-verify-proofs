(* The image-B (asan-ubsan) twin of lib/A/ReplyKfCnl.v at a working branch 3d1ff6eaa94 (a Theorem Labs lane, 2026-10-30):
   the same text over lib/B, the same lemma names, all of it: B's W_contract.v gm_cost / gmc / cnl_go / gm_post /
   gm_spec (and W_contract_x.v's _x twins) are token-identical to A's from a Theorem Labs lane's kit 3a33ee94ccc on. *)
(* KF-COUNT, the check_no_loss / check_shape part (CUT-k4.md (sha256 2ee9221a56b3; internal record)): how many SECONDARY requests
   (Psec n, n >= 64,513 bytes: ReplyLSCntL.is_sec_iff) the plain model's request traces of check_shape_ends,
   source_reset, list free / drop, gesture_model and check_no_loss make, at a meter MT that charges 1 for a secondary
   malloc or realloc and 0 for anything else (KF_MAL, KF_FREE; the Section shape of ReplyKfCB.v, whose lemmas take them).
   proves no function (kind: segment lemma: trace-count arithmetic over the plain model's request traces)
   - frees only (cost 0): kf_recs_drop_zero, kf_list_free_zero, kf_cshe_zero, kf_source_reset_zero.
   - gesture_model (kf_gesture_model): one push or one drop.  The push is ReplyKfCB.kf_list_push: its vector growth
     (realloc 16 cap -> 32 cap, malloc 128 at cap 0) is secondary only when cap >= 2,017, and then it raises the
     potential ReplyKfCB.kf_psi_v cap = max 10 (log2 cap) by 1; a primary growth does not lower it.  The key copy is
     |key| + 1 <= |line| bytes (a key is a proper prefix of its line), so a line of at most APARTIAL bytes copies a
     primary key (kf_apartial_primary).
   - check_no_loss (kf_cnl_tr_le, kf_cnl_le): the potentials telescope (kf_cnl_psi); the held capacity either never
     moves or ends at most max 8 (2 (n + the begin records)) < 2^26 (kf_cnl_cap), so the trace costs at most
     ReplyKfCB.kf_vec_range's 15.  No capacity premise.  The text premise is alist_at's (kf_alist_short).
   - the SPEC costs, W8's fixed kit text (e09792169e4: gesture_model's charge is its trace's): gm_cost (W_contract.v:1651)
     is gmc (:1993) at the held list's texts and capacity (kf_gm_cost_gmc); one gmc is at most the potential's rise to
     capstep's capacity (kf_gmc_le, kf_gm_cost_le, and kf_gm_cost_le_post over gm_post's H'), and per call between 0
     and 1 (kf_gm_cost_nonneg, kf_gm_cost_le1: at most one growth, the key copy primary, a free 0); over the expected
     records cnl_go (:2002) telescopes to cnl_cap's capacity (kf_cnl_go_psi), which kf_cnl_cap_range bounds as for
     the trace, so cnl_cost (:2008) is at most 15 (kf_cnl_cost_le) under kf_cnl_le's two premises.  No NoDup and no
     hl_n <= hl_cap premise: the bound is over the spec's own model (texts, capstep), not through the trace. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK04 YP09 YI04 YI00 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YO0i YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep RelayModel CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayRunT RelayRunF drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyCnt ReplyLSCntL.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyKfCB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import ListTr HarnessTr.
(* the list names (map, filter, the length lemmas) are Stdlib's *)
From Stdlib Require Import List.
Import ListNotations.
Open Scope Z_scope.

(* a copy of a line of at most APARTIAL bytes, NUL included, is primary *)
Lemma kf_apartial_primary : forall n, 0 <= n <= APARTIAL -> Psec (n + 1) = false.
Proof. intros n Hn. unfold APARTIAL in Hn. apply ReplyKfCB.kf_psec_small. lia. Qed.

(* a gesture's key is a proper prefix of its line *)
Lemma kf_lsf_lt : forall l i j, RelayModel.last_space_from i l = Some j -> (j < i + length l)%nat.
Proof.
  induction l as [|b l IH]; intros i j H; cbn [RelayModel.last_space_from] in H; [discriminate|].
  destruct (RelayModel.last_space_from (S i) l) as [j'|] eqn:E.
  - injection H as <-. specialize (IH _ _ E). cbn [length]. lia.
  - destruct (b =? RelayModel.SPACE); [injection H as <-; cbn [length]; lia | discriminate].
Qed.
Lemma kf_gesture_len : forall l k x, RelayModel.gesture l = Some (k, x) -> (length x < length l)%nat.
Proof.
  intros l k x G. unfold RelayModel.gesture in G. cbv zeta in G.
  destruct (RelayModel.list_eqb (firstn 13 l) RelayModel.K_GESTURE && Z.eqb (nth 13 l 0) RelayModel.SPACE &&
            Nat.ltb 13 (length l)); [|discriminate].
  destruct (RelayModel.last_space_from 0 l) as [j|] eqn:E; [|discriminate].
  destruct (Nat.ltb 13 j); [|discriminate].
  apply kf_lsf_lt in E.
  assert (Lx : length (firstn j l) = j) by (rewrite length_firstn; lia).
  destruct (RelayModel.list_eqb (skipn (S j) l) RelayModel.W_BEGIN); [injection G as <- <-; lia|].
  destruct (RelayModel.list_eqb (skipn (S j) l) RelayModel.W_END); [injection G as <- <-; lia | discriminate].
Qed.

(* the expected and held lists are lines (alist_at's lines = true, W_rep.v:91-92): every text is at most APARTIAL *)
Section kfal.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PI : PAImg fr_prog_listing}.
Variable B : asyms.
Lemma kf_alist_short : forall ly S (W : world (@pa_segs _ fr_prog_listing PI)) mem LA l,
  alist_at B ly S W mem LA l true -> Forall (fun r => Z.of_nat (length (snd r)) <= APARTIAL) (hl_recs l).
Proof.
  intros ly S W mem LA l (_ & _ & _ & _ & _ & _ & _ & _ & HF).
  eapply Forall_impl; [|exact HF]. intros r (_ & _ & Ht & _). exact (proj2 (Ht eq_refl)).
Qed.
End kfal.

(* ================================================================== the potential's floor, the begin count *)
Lemma kf_psi_v_floor : forall c, 10 <= ReplyKfCB.kf_psi_v c.
Proof. intros c. unfold ReplyKfCB.kf_psi_v. lia. Qed.
Lemma kf_zb_range : forall b, 0 <= zb b <= 1.
Proof. intros [|]; cbn [zb]; lia. Qed.
Lemma kf_cb_cons : forall l ls, Z.of_nat (count_begin (l :: ls)) = zb (is_begin l) + Z.of_nat (count_begin ls).
Proof.
  intros l ls.
  assert (E : count_begin (l :: ls) = (if is_begin l then S (count_begin ls) else count_begin ls)).
  { unfold count_begin. cbn. destruct (is_begin l); reflexivity. }
  rewrite E. destruct (is_begin l); cbn [zb]; lia.
Qed.

(* ================================================================== the held list's shape after one line *)
Lemma kf_gm_sh : forall j s ln,
  ListTr.sh_n (HarnessTr.gesture_model_sh j s ln) <= ListTr.sh_n s + zb (is_begin ln) /\
  (ListTr.sh_cap (HarnessTr.gesture_model_sh j s ln) = ListTr.sh_cap s \/
   ListTr.sh_cap (HarnessTr.gesture_model_sh j s ln) <= Z.max 8 (2 * ListTr.sh_n s)).
Proof.
  intros j s ln. unfold HarnessTr.gesture_model_sh, is_begin.
  destruct (RelayModel.gesture ln) as [[[|] x]|]; cbn [zb].
  - destruct (existsb (RelayModel.list_eqb x) (ListTr.sh_keys s)); [lia|].
    unfold ListTr.list_push_sh, grow_cap, ListTr.sh_n.
    destruct (Z.eqb_spec (Z.of_nat (length (ListTr.sh_recs s))) (ListTr.sh_cap s)) as [En|En];
      [destruct (Z.eqb_spec (ListTr.sh_cap s) 0)|]; cbn [ListTr.sh_cap ListTr.sh_recs];
      rewrite length_app; cbn [length]; lia.
  - destruct (HarnessTr.find_key x (ListTr.sh_keys s)) as [i|]; [|lia].
    unfold ListTr.list_drop_sh, ListTr.sh_n. cbn [ListTr.sh_cap ListTr.sh_recs].
    rewrite length_app, length_firstn, length_skipn. lia.
  - lia.
Qed.

Lemma kf_cnl_cap : forall rs j s,
  ListTr.sh_cap (HarnessTr.check_no_loss_sh j s rs) = ListTr.sh_cap s \/
  ListTr.sh_cap (HarnessTr.check_no_loss_sh j s rs) <=
    Z.max 8 (2 * (ListTr.sh_n s + Z.of_nat (count_begin (map snd rs)))).
Proof.
  induction rs as [|r rs IH]; intros j s; [left; reflexivity|].
  cbn [HarnessTr.check_no_loss_sh List.map]. rewrite kf_cb_cons.
  destruct (kf_gm_sh j s (snd r)) as [N C]. pose proof (kf_zb_range (is_begin (snd r))).
  match goal with |- context [HarnessTr.check_no_loss_sh ?j' ?s' rs] => destruct (IH j' s') as [E|E] end;
    lia.
Qed.

(* list_push's new capacity is drain_b_c.push_cap's (ListRep.grow_cap doubles as 2 * cap, push_cap as cap * 2) *)
Lemma kf_push_sh_cap : forall j s x,
  ListTr.sh_cap (ListTr.list_push_sh j s x) = drain_b_c.push_cap (ListTr.sh_n s) (ListTr.sh_cap s).
Proof.
  intros j s x. unfold ListTr.list_push_sh, drain_b_c.push_cap, grow_cap.
  destruct (ListTr.sh_n s =? ListTr.sh_cap s); cbn [ListTr.sh_cap]; [|reflexivity].
  destruct (ListTr.sh_cap s =? 0); [reflexivity | apply Z.mul_comm].
Qed.

(* a growth never lowers the potential *)
Lemma kf_psi_grow : forall n cap, 0 <= n -> ReplyKfCB.kf_psi_v cap <= ReplyKfCB.kf_psi_v (grow_cap n cap).
Proof.
  intros n cap Hn. unfold grow_cap.
  destruct (Z.eqb_spec n cap) as [En|En]; [|lia].
  destruct (Z.eqb_spec cap 0) as [E0|E0].
  - rewrite E0. pose proof ReplyKfCB.kf_psi_v_08. lia.
  - replace (2 * cap) with (cap * 2) by lia. exact (proj1 (ReplyKfCB.kf_psi_v_double cap ltac:(lia))).
Qed.

(* the spec's model of one line (RelayModel.upd, capstep): at most one more key, the capacity kept or at most
   max 8 (2 n) *)
Lemma kf_upd_step : forall T l cap,
  Z.of_nat (length (RelayModel.upd T l)) <= Z.of_nat (length T) + zb (is_begin l) /\
  (capstep T l cap = cap \/ capstep T l cap <= Z.max 8 (2 * Z.of_nat (length T))).
Proof.
  intros T l cap. split.
  - unfold RelayModel.upd, is_begin. destruct (RelayModel.gesture l) as [[[|] x]|]; cbn [zb].
    + destruct (existsb (RelayModel.list_eqb x) T); [lia|]. rewrite length_app. cbn [length]. lia.
    + pose proof (filter_length_le (fun y => negb (RelayModel.list_eqb x y)) T). lia.
    + lia.
  - unfold capstep. destruct (Nat.ltb (length T) (length (RelayModel.upd T l))); [|left; reflexivity].
    unfold grow_cap. destruct (Z.eqb_spec (Z.of_nat (length T)) cap) as [En|En];
      [destruct (Z.eqb_spec cap 0)|]; lia.
Qed.

Lemma kf_cnl_cap_range : forall rs T cap,
  cnl_cap T cap rs = cap \/
  cnl_cap T cap rs <= Z.max 8 (2 * (Z.of_nat (length T) + Z.of_nat (count_begin (map (fun r => bzs (snd r)) rs)))).
Proof.
  induction rs as [|r rs IH]; intros T cap; [left; reflexivity|].
  cbn [cnl_cap List.map]. rewrite kf_cb_cons.
  destruct (kf_upd_step T (bzs (snd r)) cap) as [N C]. pose proof (kf_zb_range (is_begin (bzs (snd r)))).
  destruct (IH (RelayModel.upd T (bzs (snd r))) (capstep T (bzs (snd r)) cap)) as [E|E]; lia.
Qed.

Section kfcnl.
Variable MT : ameter_ops.
Hypothesis KF_MAL : forall n, mo_malloc MT n = if Psec n then 1 else 0.
Hypothesis KF_FREE : mo_free MT = 0.

(* ================================================================== frees only *)
Lemma kf_rec_drop_zero : forall r, tr_cost MT (ListTr.rec_drop_tr r) = 0.
Proof. intros r. unfold ListTr.rec_drop_tr, tr_cost. cbn [fold_right]. rewrite KF_FREE. reflexivity. Qed.
Lemma kf_recs_drop_zero : forall rs, tr_cost MT (ListTr.recs_drop_tr rs) = 0.
Proof.
  induction rs as [|r rs IH]; [reflexivity|].
  unfold ListTr.recs_drop_tr in *. cbn [List.map List.concat].
  rewrite (ReplyKfCB.kf_cost_app MT), kf_rec_drop_zero, IH. reflexivity.
Qed.
Lemma kf_list_free_zero : forall s, tr_cost MT (ListTr.list_free_tr s) = 0.
Proof.
  intros s. unfold ListTr.list_free_tr. rewrite (ReplyKfCB.kf_cost_app MT), kf_recs_drop_zero.
  destruct (ListTr.sh_cap s =? 0); [reflexivity|]. unfold tr_cost. cbn [fold_right]. rewrite KF_FREE. reflexivity.
Qed.
Lemma kf_cshe_zero : forall nm gone P rs d, tr_cost MT (HarnessTr.check_shape_ends_tr nm gone P rs d) = 0.
Proof.
  intros nm gone P rs d. unfold HarnessTr.check_shape_ends_tr.
  destruct (gone =? 0); [|apply kf_recs_drop_zero].
  destruct (ends_run P rs d (want_of P rs)) as [[[? ds] ?]|]; [apply kf_recs_drop_zero | reflexivity].
Qed.
Lemma kf_source_reset_zero : forall nm h, tr_cost MT (HarnessTr.source_reset_tr nm h) = 0.
Proof.
  intros nm h. unfold HarnessTr.source_reset_tr, HarnessTr.hlist_free_tr.
  rewrite !(ReplyKfCB.kf_cost_app MT), !kf_list_free_zero. unfold tr_cost. cbn [fold_right]. rewrite KF_FREE.
  reflexivity.
Qed.

(* ================================================================== gesture_model: one push or one drop *)
(* one push of a primary key: ReplyKfCB.kf_list_push, and no growth at all when the capacity is negative *)
Lemma kf_push : forall j s x, Psec (Z.of_nat (length x) + 1) = false ->
  tr_cost MT (ListTr.list_push_tr s x)
    <= ReplyKfCB.kf_psi_v (ListTr.sh_cap (ListTr.list_push_sh j s x)) - ReplyKfCB.kf_psi_v (ListTr.sh_cap s).
Proof.
  intros j s x Hx. rewrite ListTr.list_push_tr_tra, kf_push_sh_cap.
  destruct (Z.leb_spec 0 (ListTr.sh_cap s)) as [Hc|Hc].
  - pose proof (ReplyKfCB.kf_list_push MT KF_MAL KF_FREE (ListTr.sh_v s) (ListTr.sh_n s) (ListTr.sh_cap s)
                  (Z.of_nat (length x)) Hc (Nat2Z.is_nonneg _)) as P.
    rewrite Hx in P. cbv beta iota in P. lia.
  - assert (En : (ListTr.sh_n s =? ListTr.sh_cap s) = false) by (apply Z.eqb_neq; unfold ListTr.sh_n; lia).
    unfold ListTr.list_push_tra, drain_b_c.push_cap. rewrite En. cbn [app].
    rewrite (ReplyKfCB.kf_cost_malloc MT KF_MAL KF_FREE), Hx. cbv beta iota. lia.
Qed.

Lemma kf_gesture_model : forall (j : nat) (s : ListTr.shl) (ln : list Z), Z.of_nat (length ln) <= APARTIAL ->
  tr_cost MT (HarnessTr.gesture_model_tr s ln)
    <= ReplyKfCB.kf_psi_v (ListTr.sh_cap (HarnessTr.gesture_model_sh j s ln)) - ReplyKfCB.kf_psi_v (ListTr.sh_cap s).
Proof.
  intros j s ln Hl. unfold HarnessTr.gesture_model_tr, HarnessTr.gesture_model_sh.
  destruct (RelayModel.gesture ln) as [[[|] x]|] eqn:G.
  - destruct (existsb (RelayModel.list_eqb x) (ListTr.sh_keys s)); [rewrite (ReplyKfCB.kf_cost_nil MT); lia|].
    apply kf_push. pose proof (kf_gesture_len _ _ _ G). apply kf_apartial_primary. lia.
  - destruct (HarnessTr.find_key x (ListTr.sh_keys s)) as [i|]; [|rewrite (ReplyKfCB.kf_cost_nil MT); lia].
    unfold ListTr.list_drop_tr. rewrite kf_rec_drop_zero. unfold ListTr.list_drop_sh. cbn [ListTr.sh_cap]. lia.
  - rewrite (ReplyKfCB.kf_cost_nil MT). lia.
Qed.

(* ================================================================== check_no_loss: the potentials telescope *)
Lemma kf_cnl_psi : forall rs j s, Forall (fun r => Z.of_nat (length (snd r)) <= APARTIAL) rs ->
  tr_cost MT (HarnessTr.check_no_loss_tr j s rs)
    <= ReplyKfCB.kf_psi_v (ListTr.sh_cap (HarnessTr.check_no_loss_sh j s rs)) - ReplyKfCB.kf_psi_v (ListTr.sh_cap s).
Proof.
  induction rs as [|r rs IH]; intros j s Hk.
  - cbn [HarnessTr.check_no_loss_tr HarnessTr.check_no_loss_sh]. rewrite (ReplyKfCB.kf_cost_nil MT). lia.
  - pose proof (Forall_inv Hk) as Hr. pose proof (Forall_inv_tail Hk) as Hrs.
    cbn [HarnessTr.check_no_loss_tr HarnessTr.check_no_loss_sh].
    rewrite !(ReplyKfCB.kf_cost_app MT), kf_rec_drop_zero.
    pose proof (kf_gesture_model j s (snd r) Hr) as G1.
    match goal with |- context [HarnessTr.check_no_loss_tr ?j' ?s' rs] => pose proof (IH j' s' Hrs) as G2 end.
    lia.
Qed.

(* the per-call bound, START-count form: X:1328 (hl_n held + count_begin (texts expected) < 2^22) gives the first
   premise, alist_at's lines = true (kf_alist_short) the second *)
Lemma kf_cnl_tr_le : forall (j : nat) (s : ListTr.shl) (rs : list (ListTr.tad * list Z)),
  ListTr.sh_n s + Z.of_nat (count_begin (map snd rs)) < 2 ^ 25 ->
  Forall (fun r => Z.of_nat (length (snd r)) <= APARTIAL) rs ->
  tr_cost MT (HarnessTr.check_no_loss_tr j s rs) <= 15.
Proof.
  intros j s rs Hc Hk. pose proof (kf_cnl_psi rs j s Hk) as P.
  pose proof (kf_psi_v_floor (ListTr.sh_cap s)) as P0.
  destruct (kf_cnl_cap rs j s) as [E|E].
  - rewrite E in P. lia.
  - assert (Hn : 0 <= ListTr.sh_n s) by (unfold ListTr.sh_n; lia).
    assert (Hf : ListTr.sh_cap (HarnessTr.check_no_loss_sh j s rs) < 2 ^ 26).
    { assert (E25 : 2 ^ 25 = 33554432) by reflexivity. assert (E26 : 2 ^ 26 = 67108864) by reflexivity.
      clear -E Hc Hn E25 E26. lia. }
    pose proof (ReplyKfCB.kf_vec_range 0 _ (Z.le_refl 0) Hf) as R.
    assert (R0 : ReplyKfCB.kf_psi_v 0 = 10) by reflexivity. lia.
Qed.

(* the spec-level form, at W_contract_x.v:296-297's cnl_tr *)
Lemma kf_cnl_le : forall E H : hlist,
  hl_n H + Z.of_nat (count_begin (texts E)) < 2 ^ 25 ->
  Forall (fun r => Z.of_nat (length (snd r)) <= APARTIAL) (hl_recs E) ->
  tr_cost MT (cnl_tr E H) <= 15.
Proof.
  intros E H Hc Hk. unfold cnl_tr. apply kf_cnl_tr_le.
  - unfold ListTr.sh_n, ListTr.sh_of. cbn [ListTr.sh_recs]. rewrite length_map, map_map. exact Hc.
  - apply Forall_map. eapply Forall_impl; [|exact Hk]. intros r Hr. cbn [snd ListTr.shr].
    unfold bzs. rewrite length_map. exact Hr.
Qed.

(* ================================================================== the spec costs (W8's fixed kit text) *)

(* gm_cost is gmc at the held list's texts and capacity *)
Lemma kf_gm_cost_gmc : forall (H : hlist) (ln : list byte), gm_cost MT H ln = gmc MT (texts H) (hl_cap H) ln.
Proof.
  intros H ln.
  assert (En : hl_n H = Z.of_nat (length (texts H))) by (unfold hl_n, texts; rewrite length_map; reflexivity).
  unfold gm_cost, gmc, lp_cost, lp_grow, lp_vbytes. rewrite En. reflexivity.
Qed.

(* one line: at most the potential's rise to the capacity capstep gives (the push's growth; the key copy is primary) *)
Lemma kf_gmc_le : forall (T : list (list Z)) (cap : Z) (ln : list byte), Z.of_nat (length ln) <= APARTIAL ->
  gmc MT T cap ln <= ReplyKfCB.kf_psi_v (capstep T (bzs ln) cap) - ReplyKfCB.kf_psi_v cap.
Proof.
  intros T cap ln Hl.
  assert (Hst : ReplyKfCB.kf_psi_v cap <= ReplyKfCB.kf_psi_v (capstep T (bzs ln) cap)).
  { unfold capstep. destruct (Nat.ltb (length T) (length (RelayModel.upd T (bzs ln))));
      [apply kf_psi_grow; lia | lia]. }
  unfold gmc. destruct (RelayModel.gesture (bzs ln)) as [[[|] x]|] eqn:G; cbv beta iota.
  - destruct (existsb (RelayModel.list_eqb x) T) eqn:Ex; cbv beta iota; [lia|].
    assert (Ec : capstep T (bzs ln) cap = grow_cap (Z.of_nat (length T)) cap).
    { unfold capstep, RelayModel.upd. rewrite G. cbv beta iota. rewrite Ex. cbv beta iota.
      rewrite length_app. cbn [length].
      replace (Nat.ltb (length T) (length T + 1)) with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. }
    rewrite Ec. clear Hst Ec.
    pose proof (kf_gesture_len _ _ _ G) as Lx. unfold bzs in Lx. rewrite length_map in Lx.
    rewrite (KF_MAL (Z.of_nat (length x) + 1)), (kf_apartial_primary (Z.of_nat (length x))) by lia.
    cbv beta iota. unfold grow_cap.
    destruct (Z.eqb_spec (Z.of_nat (length T)) cap) as [En|En]; cbv beta iota; [|lia].
    destruct (Z.eqb_spec cap 0) as [E0|E0]; cbv beta iota; rewrite KF_MAL, KF_FREE.
    + rewrite (ReplyKfCB.kf_psec_small (AREC * 8)) by (unfold AREC; lia). cbv beta iota. rewrite E0.
      pose proof ReplyKfCB.kf_psi_v_08. lia.
    + replace (AREC * (2 * cap)) with (32 * cap) by (unfold AREC; lia). replace (2 * cap) with (cap * 2) by lia.
      destruct (ReplyKfCB.kf_psi_v_double cap ltac:(lia)) as [_ D]. lia.
  - rewrite KF_FREE. destruct (existsb (RelayModel.list_eqb x) T); cbv beta iota; lia.
  - lia.
Qed.

Lemma kf_gm_cost_le : forall (H : hlist) (ln : list byte), Z.of_nat (length ln) <= APARTIAL ->
  gm_cost MT H ln <= ReplyKfCB.kf_psi_v (capstep (texts H) (bzs ln) (hl_cap H)) - ReplyKfCB.kf_psi_v (hl_cap H).
Proof. intros H ln Hl. rewrite kf_gm_cost_gmc. exact (kf_gmc_le (texts H) (hl_cap H) ln Hl). Qed.

(* the per-call form: one line costs at most one secondary request (the push's growth; its key copy is primary, a
   free costs 0), and never less than 0 *)
Lemma kf_gmc_nonneg : forall (T : list (list Z)) (cap : Z) (ln : list byte), 0 <= gmc MT T cap ln.
Proof.
  intros T cap ln. unfold gmc.
  destruct (RelayModel.gesture (bzs ln)) as [[[|] x]|]; cbv beta iota.
  - destruct (existsb (RelayModel.list_eqb x) T); cbv beta iota; [lia|].
    rewrite KF_FREE, !KF_MAL.
    pose proof (ReplyKfCB.kf_b01 (Psec (Z.of_nat (length x) + 1))).
    pose proof (ReplyKfCB.kf_b01 (Psec (AREC * grow_cap (Z.of_nat (length T)) cap))).
    destruct (Z.of_nat (length T) =? cap); cbv beta iota; lia.
  - rewrite KF_FREE. destruct (existsb (RelayModel.list_eqb x) T); cbv beta iota; lia.
  - lia.
Qed.
Lemma kf_gmc_le1 : forall (T : list (list Z)) (cap : Z) (ln : list byte), Z.of_nat (length ln) <= APARTIAL ->
  gmc MT T cap ln <= 1.
Proof.
  intros T cap ln Hl. unfold gmc.
  destruct (RelayModel.gesture (bzs ln)) as [[[|] x]|] eqn:G; cbv beta iota.
  - destruct (existsb (RelayModel.list_eqb x) T); cbv beta iota; [lia|].
    pose proof (kf_gesture_len _ _ _ G) as Lx. unfold bzs in Lx. rewrite length_map in Lx.
    rewrite (KF_MAL (Z.of_nat (length x) + 1)), (kf_apartial_primary (Z.of_nat (length x))) by lia.
    cbv beta iota. rewrite KF_FREE.
    destruct (Z.of_nat (length T) =? cap); cbv beta iota; [|lia].
    rewrite KF_MAL. pose proof (ReplyKfCB.kf_b01 (Psec (AREC * grow_cap (Z.of_nat (length T)) cap))). lia.
  - rewrite KF_FREE. destruct (existsb (RelayModel.list_eqb x) T); cbv beta iota; lia.
  - lia.
Qed.
Lemma kf_gm_cost_le1 : forall (H : hlist) (ln : list byte), Z.of_nat (length ln) <= APARTIAL ->
  gm_cost MT H ln <= 1.
Proof. intros H ln Hl. rewrite kf_gm_cost_gmc. exact (kf_gmc_le1 (texts H) (hl_cap H) ln Hl). Qed.
Lemma kf_gm_cost_nonneg : forall (H : hlist) (ln : list byte), 0 <= gm_cost MT H ln.
Proof. intros H ln. rewrite kf_gm_cost_gmc. apply kf_gmc_nonneg. Qed.

(* the same over the H' gm_post leaves (W_contract.v gm_post: texts H' = upd (texts H) (bzs ln) and its capacity law) *)
Lemma kf_gm_cost_le_post : forall (H H' : hlist) (ln : list byte), Z.of_nat (length ln) <= APARTIAL ->
  texts H' = RelayModel.upd (texts H) (bzs ln) ->
  hl_cap H' = (if hl_n H <? hl_n H' then grow_cap (hl_n H) (hl_cap H) else hl_cap H) ->
  gm_cost MT H ln <= ReplyKfCB.kf_psi_v (hl_cap H') - ReplyKfCB.kf_psi_v (hl_cap H).
Proof.
  intros H H' ln Hl Et Ec. pose proof (kf_gm_cost_le H ln Hl) as P.
  assert (Ecs : capstep (texts H) (bzs ln) (hl_cap H) = hl_cap H').
  { rewrite Ec. unfold capstep. rewrite <- Et. unfold hl_n, texts. rewrite !length_map.
    destruct (Nat.ltb_spec (length (hl_recs H)) (length (hl_recs H')));
      destruct (Z.ltb_spec (Z.of_nat (length (hl_recs H))) (Z.of_nat (length (hl_recs H')))); cbv beta iota;
      try lia; reflexivity. }
  rewrite Ecs in P. exact P.
Qed.

(* check_no_loss's spec cost: cnl_go telescopes to cnl_cap's capacity *)
Lemma kf_cnl_go_psi : forall rs T cap, Forall (fun r => Z.of_nat (length (snd r)) <= APARTIAL) rs ->
  cnl_go MT T cap rs <= ReplyKfCB.kf_psi_v (cnl_cap T cap rs) - ReplyKfCB.kf_psi_v cap.
Proof.
  induction rs as [|r rs IH]; intros T cap Hk.
  - cbn [cnl_go cnl_cap]. lia.
  - pose proof (Forall_inv Hk) as Hr. pose proof (Forall_inv_tail Hk) as Hrs.
    cbn [cnl_go cnl_cap]. rewrite KF_FREE.
    pose proof (kf_gmc_le T cap (snd r) Hr) as G1.
    pose proof (IH (RelayModel.upd T (bzs (snd r))) (capstep T (bzs (snd r)) cap) Hrs) as G2. lia.
Qed.

(* the per-call bound, kf_cnl_le's premises: X:1328 gives the first, alist_at (kf_alist_short) the second *)
Lemma kf_cnl_cost_le : forall E H : hlist,
  hl_n H + Z.of_nat (count_begin (texts E)) < 2 ^ 25 ->
  Forall (fun r => Z.of_nat (length (snd r)) <= APARTIAL) (hl_recs E) ->
  cnl_cost MT E H <= 15.
Proof.
  intros E H Hc Hk. unfold cnl_cost.
  pose proof (kf_cnl_go_psi (hl_recs E) (texts H) (hl_cap H) Hk) as P.
  pose proof (kf_psi_v_floor (hl_cap H)) as P0.
  destruct (kf_cnl_cap_range (hl_recs E) (texts H) (hl_cap H)) as [Ec|Ec].
  - rewrite Ec in P. lia.
  - assert (Hn : hl_n H = Z.of_nat (length (texts H))) by (unfold hl_n, texts; rewrite length_map; reflexivity).
    change (count_begin (texts E)) with (count_begin (map (fun r => bzs (snd r)) (hl_recs E))) in Hc.
    assert (Hf : cnl_cap (texts H) (hl_cap H) (hl_recs E) < 2 ^ 26).
    { assert (E25 : 2 ^ 25 = 33554432) by reflexivity. assert (E26 : 2 ^ 26 = 67108864) by reflexivity.
      clear -Ec Hc Hn E25 E26. lia. }
    pose proof (ReplyKfCB.kf_vec_range 0 _ (Z.le_refl 0) Hf) as R.
    assert (R0 : ReplyKfCB.kf_psi_v 0 = 10) by reflexivity. lia.
Qed.

End kfcnl.
