(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment TOP of the ASan walk of fuzz_reply's relay_instance_gone
   (fuzz_reply.asan 0x82d98 .. 0x82e50 / 0x82f44), against the frozen segment interface
   lib/A/W_relay_instance_gone_cx.v (rig_top_stmt).  The Section-hypothesis block is that file's (commit
   92dac370558), verbatim.
   Layout: the tracks' pure trace lemmas, then the generic Section: its hypotheses, the statements of the lemma
   tracks, and their proofs (drain's
   model and budget, drain's live bytes, the relay representation across drain, GLIVE, GIN / GOUT at the key loop's
   start, the snprintf / strlen calls), then the walk itself: top_p1 (0x82d98 -> drain -> 0x82dd0), top_p2
   (0x82dd0 -> snprintf, strlen, the nheld test -> RGI / RGE) and rig_top_proof.
   C3 (475b8a2b569, the peak form): drain's room is the peak of its trace, a prefix of the remaining trace (top_room);
   drain's live bytes are bounded in the NET form, blocks_bytes S' <= blocks_bytes S + tr_net (dr_tr ..) (dr_bytes:
   the potential td_pot now weighs the pending texts too, which drain frees as it reads them), and tb_core carries
   gbud's peak room across the drain step with tr_peak_app.
   ROUTE (b), STEP 3 (CONVERSION.md (sha256 1015972e02a9; internal record); the RIG_x round): over any allocator relation
   ARx with its laws and the room record RP, at W_relay_instance_gone_cx.v's generic Section c (its list copied
   verbatim).  The statements of the lemma tracks now sit inside that Section, after its hypotheses.  Every journal is
   ajournal_gx_x with its head sets; the laws are AR_laws_x's.  THE ROOM at the drain call: gbud's room over the
   remaining trace grest i splits at the drain (tr_cost MT_rk is additive and nonnegative), so drain gets
   rp_RM RP S (Z.to_nat (dr_cost MT_rk ..) + dr_kr ..) with dr_kr the rest's MT_rk count plus gxkr, and its post's
   rp_RM RP S' dr_kr is gbud's room after the drain (top_room / top_budget).  THE COUNTS: drain's count premise dr_pk is
   within gbud's (tr_peakP of a prefix), and after the drain the live counts move by exactly tr_netP of drain's trace
   (stmt_dr_cnt, RR's lib/A/W_rr_m_dcnt.v rmc_dr_cnt), which tr_peakP_app turns into gbud's count bound over the rest
   (tb_core).  The fake frame is only 32-aligned in a generic state (alx_frames): ts_ra, ts_hull and the shadow seat
   tp_seat2 read that alignment (F's shadow address is 4-aligned). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_rig_top.v, with its module paths and module names changed; 516 of its 657 lines of code are new or changed and 5398 lines of the source are left out. *)
(* The count accounting behind ReplyGnCnt.v's gcnt_step, for any count predicate P, moved out of ReplyGnCnt.v verbatim
   (lemma names unchanged), so that the other arms' count rules can use it without ReplyGnCnt.v's LS-side Requires.
   proves no function (kind: invariant lemma).
   - za / tz / ws: the P-count of a block list, of a one-block chain, of one block per text; the model's pieces
     (za_alist, za_aentry, za_asrc, za_model) and the net count of the request pieces (net_nil .. net_realloc).
   - check_no_loss's model change is its trace's net under the exact capacity law (acc_cnl_src), check_shape_ends only
     drops blocks (acc_cshe_src); each callee piece's exact net (acc_sl_run .. acc_lines); the drain's model change
     (acc_drain); the drain's model fields do not depend on its sends (acc_kaf .. acc_fin_state); the keys
     gestures_end_instance ends (acc_geik, acc_gei_perm); acc_ws_len, acc_hpkh, acc_texts_lines, acc_za_out.
   - ReplyGnCnt.v keeps net_le_peak: it reads ReplyLScntRP.lsc_net_le_peak. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT RelayRunF ListTr drain_b_c send_line_b_c gesture_end_b_c gestures_end_b_c relay_remove_b_c RelayCap SlotInv
  SlotReads relay_instance_gone_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require HarnessTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyTrPeakW.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_gone_base.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_instance_gone_b_lem.
From stdpp Require list_basics.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ################################################################## the count accounting, for any predicate P *)
(* za l: the P-count of a block list, in Z; tz n: the P-count of a one-block chain of n bytes (0 while NULL); ws T: the
   P-count of one block per text of T (|t| + 1 bytes each).  net: a trace's net P-count (ReplyTrPeakW.tr_net_w at the
   weight zb (P n), which tr_peakP bounds: ReplyLScntRP.lsc_net_le_peak). *)
Section acc.
Variable P : Z -> bool.
Definition tz (n : Z) : Z := if n =? 0 then 0 else zb (P n).
Definition za (l : list (Z * Z)) : Z := Z.of_nat (acnt P l).
Definition ws (T : list (list Z)) : Z := fold_right Z.add 0 (map (fun x => zb (P (Z.of_nat (length x) + 1))) T).
Local Abbreviation net := (ReplyTrPeakW.tr_net_w (fun n => zb (P n))).

Lemma zb_range : forall b, 0 <= zb b <= 1.
Proof. intros [|]; cbn; lia. Qed.
Lemma tz_range : forall n, 0 <= tz n <= 1.
Proof. intros n. unfold tz. destruct (n =? 0); [lia | apply zb_range]. Qed.
Lemma tz_nz : forall n, n <> 0 -> tz n = zb (P n).
Proof. intros n H. unfold tz. rewrite (proj2 (Z.eqb_neq n 0) H). reflexivity. Qed.
Lemma za_nil : za [] = 0.
Proof. reflexivity. Qed.
Lemma za_app : forall l1 l2, za (l1 ++ l2) = za l1 + za l2.
Proof. intros l1 l2. unfold za. rewrite acnt_app. lia. Qed.
Lemma za_cons : forall b l, za (b :: l) = zb (P (snd b)) + za l.
Proof.
  intros [a n] l. unfold za, acnt. cbn [map List.filter snd]. unfold zb. destruct (P n); cbn [length]; lia.
Qed.
Lemma za_concat : forall {X : Type} (f : X -> list (Z * Z)) (l : list X),
  za (concat (map f l)) = fold_right Z.add 0 (map (fun x => za (f x)) l).
Proof.
  intros X f l. induction l as [|x l IH]; [reflexivity|]. cbn [map concat fold_right]. rewrite za_app, IH. reflexivity.
Qed.
Lemma za_nonneg : forall l, 0 <= za l.
Proof. intros l. unfold za. lia. Qed.
Lemma ws_nil : ws [] = 0.
Proof. reflexivity. Qed.
Lemma ws_cons : forall x T, ws (x :: T) = zb (P (Z.of_nat (length x) + 1)) + ws T.
Proof. reflexivity. Qed.
Lemma ws_app : forall T1 T2, ws (T1 ++ T2) = ws T1 + ws T2.
Proof. intros T1 T2. induction T1 as [|x T1 IH]; [reflexivity|]. cbn [app]. rewrite !ws_cons, IH. lia. Qed.
Lemma ws_nonneg : forall T, 0 <= ws T.
Proof. induction T as [|x T IH]; [cbn; lia|]. rewrite ws_cons. pose proof (zb_range (P (Z.of_nat (length x) + 1))). lia. Qed.
(* a list's blocks: its vector and one block per record *)
Lemma za_recs : forall recs : list (Z * list byte),
  za (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) recs) = ws (map (fun r => bzs (snd r)) recs).
Proof.
  induction recs as [|r recs IH]; [reflexivity|]. cbn [map]. rewrite za_cons, ws_cons, IH. cbn [snd].
  unfold bzs. rewrite length_map. reflexivity.
Qed.
Lemma za_alist : forall l, za (alist_blks l) = tz (AREC * hl_cap l) + ws (texts l).
Proof.
  intros l. unfold alist_blks, texts. rewrite za_app, za_recs. unfold tz, AREC.
  destruct (Z.eqb_spec (hl_cap l) 0) as [E|E]; [rewrite E; reflexivity|].
  rewrite (proj2 (Z.eqb_neq (16 * hl_cap l) 0) ltac:(lia)), za_cons, za_nil. cbn [snd]. lia.
Qed.
Lemma za_aentry : forall e, za (aentry_blks e) =
  tz (re_cap e) + (if re_hp e =? 0 then 0 else zb (P (re_kh e))) + ws (drain_b_c.keys_texts (re_keys e)).
Proof.
  intros e. unfold aentry_blks, drain_b_c.keys_texts. rewrite !za_app. unfold tz.
  assert (K : forall ks, za (map (fun k => (gestures_end_b_c.key_addr k,
                                            Z.of_nat (length (gestures_end_b_c.key_text k)) + 1)) ks) =
                         ws (map (fun k => bzs (gestures_end_b_c.key_text k)) ks)).
  { induction ks as [|k ks IH]; [reflexivity|]. cbn [map]. rewrite za_cons, ws_cons, IH. cbn [snd].
    unfold bzs. rewrite length_map. reflexivity. }
  rewrite K. destruct (re_cap e =? 0), (re_hp e =? 0); rewrite ?za_cons, ?za_nil; cbn [snd]; lia.
Qed.
Lemma za_asrc : forall h, za (asrc_blks h) =
  zb (P APARTIAL) + za (alist_blks (hs_pending h)) + za (alist_blks (hs_expected h)) + za (alist_blks (hs_held h)).
Proof. intros h. unfold asrc_blks. rewrite za_cons, !za_app. cbn [snd]. lia. Qed.
Lemma za_model : forall m, za (model_blks m) =
  zb (P ATABLE) + fold_right Z.add 0 (map (fun e => za (aentry_blks e)) (lm_es m)) +
  fold_right Z.add 0 (map (fun o => za (slot_blks o)) (lm_hs m)) + za (aout_blks (lm_cap m) (lm_out m)).
Proof. intros m. unfold model_blks. rewrite za_cons, !za_app, !za_concat. cbn [snd]. lia. Qed.

(* ---- the net count of the request pieces *)
Lemma net_nil : forall X, @ReplyTrPeakW.tr_net_w (fun n => zb (P n)) X [] = 0.
Proof. reflexivity. Qed.
Lemma net_app : forall X (a b : list (RelayRunT.rev X)), net (a ++ b) = net a + net b.
Proof. intros. apply ReplyTrPeakW.tr_net_w_app. Qed.
Lemma net_malloc : forall X n (r : list (RelayRunT.rev X)), net (RelayRunT.RMalloc n :: r) = zb (P n) + net r.
Proof. reflexivity. Qed.
Lemma net_free : forall X k a (r : list (RelayRunT.rev X)), net (RelayRunT.RFree k a :: r) = - zb (P k) + net r.
Proof. reflexivity. Qed.
Lemma net_realloc : forall X k n a (r : list (RelayRunT.rev X)),
  net (RelayRunT.RRealloc k n a :: r) = zb (P n) - zb (P k) + net r.
Proof. reflexivity. Qed.

(* ================================================================== check_no_loss: its model change is its net *)
(* gesture_model on a held list with distinct keys: the keys become upd's, the capacity capstep's (W_contract.v:1894),
   the keys stay distinct, and the net count is the change of the list's blocks *)
Lemma acc_find_key : forall x ks i, HarnessTr.find_key x ks = Some i -> nth i ks [] = x.
Proof.
  intros x ks. induction ks as [|k ks IH]; intros i H; cbn [HarnessTr.find_key] in H; [discriminate|].
  destruct (RelayModel.list_eqb x k) eqn:Ek; [injection H as <-; symmetry; apply list_eqb_true, Ek|].
  destruct (HarnessTr.find_key x ks) as [i'|] eqn:E; [|discriminate]. cbn in H. injection H as <-.
  exact (IH i' eq_refl).
Qed.
Lemma acc_find_none : forall x ks, HarnessTr.find_key x ks = None -> forall y, In y ks -> RelayModel.list_eqb x y = false.
Proof.
  intros x ks. induction ks as [|k ks IH]; intros H y Hy; [destruct Hy|]. cbn [HarnessTr.find_key] in H.
  destruct (RelayModel.list_eqb x k) eqn:Ek; [discriminate|].
  destruct (HarnessTr.find_key x ks) eqn:E; [discriminate|]. destruct Hy as [<-|Hy]; [exact Ek|exact (IH eq_refl y Hy)].
Qed.
Lemma acc_filter_none : forall x ks, (forall y, In y ks -> RelayModel.list_eqb x y = false) ->
  List.filter (fun y => negb (RelayModel.list_eqb x y)) ks = ks.
Proof.
  intros x ks. induction ks as [|k ks IH]; intros H; [reflexivity|]. cbn [List.filter].
  rewrite (H k (or_introl eq_refl)). cbn [negb]. rewrite IH; [reflexivity|]. intros y Hy. exact (H y (or_intror Hy)).
Qed.
(* removing the i-th key of distinct keys is filtering it out *)
Lemma acc_filter_drop : forall ks i, List.NoDup ks -> (i < length ks)%nat ->
  List.filter (fun y => negb (RelayModel.list_eqb (nth i ks []) y)) ks = firstn i ks ++ skipn (S i) ks.
Proof.
  induction ks as [|k ks IH]; intros i ND Hi; [cbn in Hi; lia|]. inversion ND as [|? ? Hk ND']; subst.
  destruct i as [|i]; cbn [nth firstn skipn app List.filter].
  - rewrite list_eqb_refl. cbn [negb]. apply acc_filter_none. intros y Hy.
    destruct (RelayModel.list_eqb k y) eqn:E; [apply list_eqb_true in E; subst; contradiction | reflexivity].
  - cbn in Hi. destruct (RelayModel.list_eqb (nth i ks []) k) eqn:E.
    + apply list_eqb_true in E. exfalso. apply Hk. rewrite <- E. apply nth_In. lia.
    + cbn [negb]. f_equal. apply IH; [exact ND' | lia].
Qed.
Lemma acc_ws_drop : forall ks i, (i < length ks)%nat ->
  ws (firstn i ks ++ skipn (S i) ks) = ws ks - zb (P (Z.of_nat (length (nth i ks [])) + 1)).
Proof.
  induction ks as [|k ks IH]; intros i Hi; [cbn in Hi; lia|].
  destruct i as [|i].
  - change (firstn 0 (k :: ks) ++ skipn 1 (k :: ks)) with ks. cbn [nth]. rewrite ws_cons. lia.
  - change (firstn (S i) (k :: ks) ++ skipn (S (S i)) (k :: ks)) with (k :: (firstn i ks ++ skipn (S i) ks)).
    cbn [nth]. rewrite !ws_cons, IH by (cbn in Hi; lia). lia.
Qed.
Lemma acc_nodup_drop : forall {A : Type} (ks : list A) i, List.NoDup ks -> List.NoDup (firstn i ks ++ skipn (S i) ks).
Proof.
  intros A ks. induction ks as [|k ks IH]; intros i ND; [destruct i; constructor|].
  inversion ND as [|? ? Hk ND']; subst. destruct i as [|i]; cbn [firstn skipn app]; [exact ND'|].
  constructor; [|exact (IH i ND')]. intros Hin. apply in_app_or in Hin as [H|H].
  - apply Hk. exact (relay_instance_gone_b_lem.rigl_in_firstn _ _ _ H).
  - apply Hk. rewrite <- (firstn_skipn (S i) ks). apply in_or_app. right. exact H.
Qed.
Lemma acc_nodup_snoc : forall {A : Type} (l : list A) x, List.NoDup l -> ~ In x l -> List.NoDup (l ++ [x]).
Proof.
  intros A l x. induction l as [|a l IH]; intros ND Nx; cbn [app]; [constructor; [intros []|constructor]|].
  inversion ND as [|? ? Ha ND']; subst. constructor.
  - intros Hin. apply in_app_or in Hin as [H|[H|[]]]; [exact (Ha H)|]. subst. apply Nx. left. reflexivity.
  - apply IH; [exact ND'|]. intros H. apply Nx. right. exact H.
Qed.
Lemma acc_gm : forall j s l, List.NoDup (ListTr.sh_keys s) ->
  ListTr.sh_keys (HarnessTr.gesture_model_sh j s l) = upd (ListTr.sh_keys s) l /\
  ListTr.sh_cap (HarnessTr.gesture_model_sh j s l) = capstep (ListTr.sh_keys s) l (ListTr.sh_cap s) /\
  List.NoDup (ListTr.sh_keys (HarnessTr.gesture_model_sh j s l)) /\
  net (HarnessTr.gesture_model_tr s l) =
    tz (16 * ListTr.sh_cap (HarnessTr.gesture_model_sh j s l)) + ws (ListTr.sh_keys (HarnessTr.gesture_model_sh j s l))
    - tz (16 * ListTr.sh_cap s) - ws (ListTr.sh_keys s).
Proof.
  intros j s l ND. unfold HarnessTr.gesture_model_sh, HarnessTr.gesture_model_tr, capstep, upd.
  destruct (gesture l) as [[[|] x]|] eqn:G.
  - destruct (existsb (RelayModel.list_eqb x) (ListTr.sh_keys s)) eqn:Ex.
    + rewrite Nat.ltb_irrefl. split; [reflexivity|]. split; [reflexivity|]. split; [exact ND|].
      cbn. lia.
    + assert (Nx : ~ In x (ListTr.sh_keys s)).
      { intros Hin. assert (existsb (RelayModel.list_eqb x) (ListTr.sh_keys s) = true) as T; [|congruence].
        apply existsb_exists. exists x. split; [exact Hin | apply list_eqb_refl]. }
      rewrite length_app. cbn [length].
      match goal with |- context [Nat.ltb ?a ?b] => replace (Nat.ltb a b) with true by (symmetry; apply Nat.ltb_lt; lia) end.
      assert (En : ListTr.sh_n s = Z.of_nat (length (ListTr.sh_keys s))) by (unfold ListTr.sh_n; rewrite HarnessTr.length_sh_keys; reflexivity).
      unfold ListTr.list_push_sh, ListTr.list_push_tr, ListTr.list_grow_tr.
      assert (KA : forall a, ListTr.sh_keys (ListTr.SHL a (grow_cap (ListTr.sh_n s) (ListTr.sh_cap s))
                     (ListTr.sh_recs s ++ [(a, x)])) = ListTr.sh_keys s ++ [x]).
      { intros a. unfold ListTr.sh_keys. cbn. rewrite map_app. reflexivity. }
      destruct (Z.eqb_spec (ListTr.sh_n s) (ListTr.sh_cap s)) as [Ec|Ec].
      * cbn [ListTr.sh_keys ListTr.sh_recs ListTr.sh_cap]. unfold ListTr.sh_keys in *. cbn [ListTr.sh_recs].
        rewrite map_app. cbn [map snd]. rewrite <- En. split; [reflexivity|]. split; [reflexivity|].
        split; [exact (acc_nodup_snoc _ _ ND Nx)|].
        rewrite ws_app, ws_cons, ws_nil. unfold grow_cap. rewrite (proj2 (Z.eqb_eq _ _) Ec).
        destruct (Z.eqb_spec (ListTr.sh_cap s) 0) as [E0|E0].
        -- rewrite E0. cbn [app]. rewrite net_malloc, net_malloc, net_nil. unfold tz.
           change (16 * 8) with 128. change (16 * 0) with 0. cbn. lia.
        -- cbn [app]. rewrite net_realloc, net_malloc, net_nil. rewrite !tz_nz by lia.
           replace (16 * (2 * ListTr.sh_cap s)) with (32 * ListTr.sh_cap s) by lia. lia.
      * cbn [ListTr.sh_keys ListTr.sh_recs ListTr.sh_cap]. unfold ListTr.sh_keys in *. cbn [ListTr.sh_recs].
        rewrite map_app. cbn [map snd]. rewrite <- En. unfold grow_cap.
        rewrite (proj2 (Z.eqb_neq _ _) Ec). split; [reflexivity|]. split; [reflexivity|].
        split; [exact (acc_nodup_snoc _ _ ND Nx)|].
        rewrite ws_app, ws_cons, ws_nil. cbn [app]. rewrite net_malloc, net_nil. lia.
  - destruct (HarnessTr.find_key x (ListTr.sh_keys s)) as [i|] eqn:Ef.
    + pose proof (HarnessTr.find_key_lt _ _ _ Ef) as Hi. pose proof (acc_find_key _ _ _ Ef) as Ex.
      assert (EK : ListTr.sh_keys (ListTr.list_drop_sh s i) = firstn i (ListTr.sh_keys s) ++ skipn (S i) (ListTr.sh_keys s)).
      { unfold ListTr.sh_keys, ListTr.list_drop_sh. cbn [ListTr.sh_recs]. rewrite map_app, <- firstn_map, <- skipn_map.
        reflexivity. }
      rewrite EK. subst x. rewrite (acc_filter_drop _ _ ND Hi).
      rewrite length_app, length_firstn, length_skipn.
      match goal with |- context [Nat.ltb ?a ?b] => replace (Nat.ltb a b) with false by (symmetry; apply Nat.ltb_ge; lia) end.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact (acc_nodup_drop _ _ ND)|].
      rewrite (acc_ws_drop _ _ Hi). unfold ListTr.list_drop_tr, ListTr.rec_drop_tr, ListTr.rec_len.
      rewrite net_free, net_nil. cbn [ListTr.sh_cap ListTr.list_drop_sh].
      assert (EL : snd (nth i (ListTr.sh_recs s) (RelayRunT.Known ListTr.pdefT, [])) = nth i (ListTr.sh_keys s) []).
      { unfold ListTr.sh_keys. exact (eq_sym (map_nth snd (ListTr.sh_recs s) (RelayRunT.Known ListTr.pdefT, []) i)). }
      rewrite EL. lia.
    + rewrite (acc_filter_none _ _ (acc_find_none _ _ Ef)), Nat.ltb_irrefl.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact ND|]. cbn. lia.
  - rewrite Nat.ltb_irrefl. split; [reflexivity|]. split; [reflexivity|]. split; [exact ND|]. cbn. lia.
Qed.
(* check_no_loss over the expected records: its net is the held list's change (to upds / cnl_cap) less the freed
   expected texts *)
Lemma acc_cnl_run : forall (nm : Z -> RelayRunT.addr YO0i.sptr) (recs : list (Z * list byte)) j s,
  List.NoDup (ListTr.sh_keys s) ->
  net (HarnessTr.check_no_loss_tr j s (map (ListTr.shr nm) recs)) =
    tz (16 * cnl_cap (ListTr.sh_keys s) (ListTr.sh_cap s) recs) +
    ws (upds (ListTr.sh_keys s) (map (fun r => bzs (snd r)) recs))
    - tz (16 * ListTr.sh_cap s) - ws (ListTr.sh_keys s) - ws (map (fun r => bzs (snd r)) recs).
Proof.
  intros nm recs. induction recs as [|r recs IH]; intros j s ND.
  - cbn [map HarnessTr.check_no_loss_tr cnl_cap]. unfold upds. cbn [fold_left]. rewrite net_nil, ws_nil. lia.
  - cbn [map HarnessTr.check_no_loss_tr cnl_cap]. unfold upds. cbn [fold_left]. fold (upds (upd (ListTr.sh_keys s) (bzs (snd r)))
      (map (fun r0 => bzs (snd r0)) recs)).
    cbn [snd ListTr.shr]. destruct (acc_gm j s (bzs (snd r)) ND) as (K & C & ND' & N).
    rewrite !net_app, N.
    rewrite (IH _ _ ND'), K, C. unfold ListTr.rec_drop_tr, ListTr.rec_len. rewrite net_free, net_nil.
    rewrite ws_cons. unfold ListTr.shr. cbn [snd]. lia.
Qed.

(* the source after check_no_loss (gn_cnl_ok with the held list's exact capacity): its blocks' count moved by the
   call's own trace's net *)
Lemma acc_cnl_src : forall (h h' : hsrc) (E' H' : hlist),
  gn_cnl_ok h h' E' H' ->
  List.NoDup (texts (hs_held h)) ->
  za (asrc_blks h') = za (asrc_blks h) + net (W_contract_x.cnl_tr (hs_expected h) (hs_held h)).
Proof.
  intros h h' E' H' (-> & ER & _ & EC & _ & ET & _ & _ & HC) ND.
  rewrite !za_asrc. unfold set_exp_held. cbn [hs_pending hs_expected hs_held].
  rewrite !za_alist. unfold W_contract_x.cnl_tr.
  assert (SK : ListTr.sh_keys (ListTr.sh_of (fun _ => RelayRunF.adr0) (hs_held h)) = texts (hs_held h)).
  { unfold ListTr.sh_keys, ListTr.sh_of, texts. cbn [ListTr.sh_recs]. rewrite map_map. reflexivity. }
  rewrite (acc_cnl_run _ _ 0 _ ltac:(rewrite SK; exact ND)). rewrite SK.
  cbn [ListTr.sh_cap ListTr.sh_of]. rewrite HC, ET, EC.
  assert (TE : texts E' = []) by (unfold texts; rewrite ER; reflexivity). rewrite TE, ws_nil.
  change (map (fun r : Z * list byte => bzs (snd r)) (hl_recs (hs_expected h))) with (texts (hs_expected h)).
  unfold AREC. lia.
Qed.
(* check_shape_ends only drops held records *)
Lemma acc_ws_sub_filter : forall (f : Z * list byte -> bool) rs,
  ws (map (fun r => bzs (snd r)) (filter f rs)) <= ws (map (fun r => bzs (snd r)) rs).
Proof.
  intros f rs. induction rs as [|r rs IH]; [cbn; lia|]. rewrite list_basics.list.filter_cons.
  destruct (decide _); cbn [map]; rewrite ?ws_cons; pose proof (zb_range (P (Z.of_nat (length (bzs (snd r))) + 1)));
    lia.
Qed.
Lemma acc_ws_drop_nth : forall i (rs : list (Z * list byte)),
  ws (map (fun r => bzs (snd r)) (drop_nth i rs)) <= ws (map (fun r => bzs (snd r)) rs).
Proof.
  intros i rs. unfold drop_nth. revert i. induction rs as [|r rs IH]; intros i; [destruct i; cbn; lia|].
  destruct i as [|i].
  - change (firstn 0 (r :: rs) ++ skipn 1 (r :: rs)) with rs. cbn [map]. rewrite ws_cons.
    pose proof (zb_range (P (Z.of_nat (length (bzs (snd r))) + 1))). lia.
  - change (firstn (S i) (r :: rs) ++ skipn (S (S i)) (r :: rs)) with (r :: (firstn i rs ++ skipn (S i) rs)).
    cbn [map]. rewrite !ws_cons. specialize (IH i). lia.
Qed.
Lemma acc_ends_run : forall Pf w rs d rs' ds c, ends_run Pf rs d w = Some (rs', ds, c) ->
  ws (map (fun r => bzs (snd r)) rs') <= ws (map (fun r => bzs (snd r)) rs).
Proof.
  intros Pf w. induction w as [|w IH]; intros rs d rs' ds c E; cbn in E; [injection E as <- <- <-; lia|].
  destruct (split_nul d) as [[l d']|]; [|discriminate].
  destruct (_ && _ && _); [|discriminate].
  destruct (find_text _ rs) as [i|]; [|discriminate].
  destruct (ends_run Pf (drop_nth i rs) d' w) as [[[r1 d1] c1]|] eqn:E1; [|discriminate].
  injection E as <- <- <-. pose proof (IH _ _ _ _ _ E1). pose proof (acc_ws_drop_nth i rs). lia.
Qed.
Lemma acc_cshe_src : forall Pf gone A0 ob (h h'' : hsrc) ds c,
  gn_cshe_ok Pf gone A0 ob h h'' ds c -> za (asrc_blks h'') <= za (asrc_blks h).
Proof.
  intros Pf gone A0 ob h h'' ds c (H'' & -> & _ & EC & _ & _ & HR).
  rewrite !za_asrc. unfold set_held. cbn [hs_pending hs_expected hs_held]. rewrite !za_alist, EC.
  unfold texts. destruct HR as [(_ & ER & _)|(_ & ER)].
  - rewrite ER. pose proof (acc_ws_sub_filter (fun r => negb (prefixb Pf (snd r))) (hl_recs (hs_held h))) as HF.
    cbv beta in HF. lia.
  - pose proof (acc_ends_run _ _ _ _ _ _ _ ER). lia.
Qed.

(* ================================================================== the plain model's request pieces: exact nets *)
(* send_line's rounds: the g_out chain, from cap to its final capacity (the capacity does not depend on the names) *)
Lemma acc_sl_run : forall f mx no cap rem j o, 0 <= cap ->
  net (fst (send_line_b_c.sl_run f mx no cap rem j o)) =
    tz (fst (snd (send_line_b_c.sl_run f mx no cap rem j o))) - tz cap /\
  0 <= fst (snd (send_line_b_c.sl_run f mx no cap rem j o)) /\
  fst (snd (send_line_b_c.sl_run f mx no cap rem j o)) = fst (snd (send_line_b_c.sl_run f mx no cap rem 0 RelayRunF.adr0)).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o Hc; cbn [send_line_b_c.sl_run].
  - cbn [fst snd]. rewrite net_nil. split; [lia|]. split; [lia|reflexivity].
  - destruct (rem <=? 0); [cbn [fst snd]; rewrite net_nil; split; [lia|]; split; [lia|reflexivity]|].
    set (n := if negb (mx =? 0) && (mx <? rem) then mx else rem).
    destruct (Z.ltb_spec cap (no + n)) as [L|L].
    + cbn [fst snd]. destruct (IH mx (no + n) ((no + n) * 2) (rem - n) (S j) (RelayRunT.Ret j) ltac:(lia))
        as (N1 & N2 & N3).
      destruct (IH mx (no + n) ((no + n) * 2) (rem - n) 1%nat (RelayRunT.Ret 0%nat) ltac:(lia)) as (_ & _ & N4).
      split; [|split; [exact N2|]]; [|rewrite N3, N4; reflexivity].
      rewrite (tz_nz ((no + n) * 2)) in N1 by lia.
      destruct (Z.eqb_spec cap 0) as [E0|E0].
      * rewrite net_malloc, N1. subst cap. change (tz 0) with 0. lia.
      * rewrite net_realloc, N1, (tz_nz cap E0). lia.
    + destruct (IH mx (no + n) cap (rem - n) j o Hc) as (N1 & N2 & N3).
      destruct (IH mx (no + n) cap (rem - n) 0%nat RelayRunF.adr0 Hc) as (_ & _ & N4).
      split; [exact N1|]. split; [exact N2|]. rewrite N3. reflexivity.
Qed.
Lemma acc_send_line : forall live mx no cap len j o, 0 <= cap ->
  net (send_line_b_c.send_line_tr live mx no cap len j o) = tz (send_line_b_c.send_line_cap live mx no cap len) - tz cap /\
  0 <= send_line_b_c.send_line_cap live mx no cap len.
Proof.
  intros live mx no cap len j o Hc. unfold send_line_b_c.send_line_tr, send_line_b_c.send_line_cap.
  destruct live; [|rewrite net_nil; lia].
  destruct (acc_sl_run (Z.to_nat len) mx no cap len j o Hc) as (A & B & C). rewrite <- C. split; [exact A|exact B].
Qed.
Lemma acc_ge : forall live mx no cap xl j o, 0 <= cap ->
  net (gesture_end_b_c.gesture_end_tr live mx no cap xl j o) = tz (gesture_end_b_c.gesture_end_cap live mx no cap xl) - tz cap /\
  0 <= gesture_end_b_c.gesture_end_cap live mx no cap xl.
Proof.
  intros live mx no cap xl j o Hc. unfold gesture_end_b_c.gesture_end_tr, gesture_end_b_c.gesture_end_cap.
  rewrite net_app. destruct (acc_send_line live mx no cap xl j o Hc) as (A1 & B1).
  match goal with |- context [send_line_b_c.send_line_tr live mx (no + xl) ?c 5 ?jj ?oo] =>
    destruct (acc_send_line live mx (no + xl) c 5 jj oo B1) as (A2 & B2) end.
  split; [lia | exact B2].
Qed.
(* gestures_end's key run: the g_out chain, and each key's free *)
Lemma acc_ker : forall xks live mx no cap j o, 0 <= cap ->
  net (fst (gestures_end_b_c.keys_end_run live mx no cap xks j o)) =
    tz (fst (snd (gestures_end_b_c.keys_end_run live mx no cap xks j o))) - tz cap -
    fold_right Z.add 0 (map (fun xk => zb (P (fst xk + 1))) xks) /\
  0 <= fst (snd (gestures_end_b_c.keys_end_run live mx no cap xks j o)).
Proof.
  induction xks as [|[xl ka] r IH]; intros live mx no cap j o Hc; cbn [gestures_end_b_c.keys_end_run].
  - cbn [fst snd map fold_right]. rewrite net_nil. split; [lia | exact Hc].
  - cbn [fst snd map fold_right]. rewrite net_app, net_free.
    destruct (acc_ge live mx no cap xl j o Hc) as (A1 & B1).
    match goal with |- context [gestures_end_b_c.keys_end_run live mx ?n ?c r ?jj ?oo] =>
      destruct (IH live mx n c jj oo B1) as (A2 & B2) end.
    split; [cbn [fst]; lia | exact B2].
Qed.
(* drain's buffer growth *)
Lemma acc_grow : forall cap used j b,
  net (fst (drain_b_c.grow_tr cap used j b)) = tz (fst (snd (drain_b_c.grow_tr cap used j b))) - tz cap.
Proof.
  intros cap used j b. unfold drain_b_c.grow_tr. destruct (cap - used <? 4096); cbn [fst snd]; [|rewrite net_nil; lia].
  destruct (Z.eqb_spec cap 0) as [E0|E0].
  - rewrite net_malloc, net_nil. subst cap. rewrite (tz_nz 8192) by lia. change (tz 0) with 0. lia.
  - rewrite net_realloc, net_nil, (tz_nz (cap * 2)) by lia. rewrite (tz_nz cap E0). lia.
Qed.
(* list_push of one text, and reference_feed's pushes *)
Lemma acc_push_tra : forall v n cap x,
  net (ListTr.list_push_tra v n cap x) = tz (16 * drain_b_c.push_cap n cap) - tz (16 * cap) + zb (P (x + 1)).
Proof.
  intros v n cap x. unfold ListTr.list_push_tra, drain_b_c.push_cap. rewrite net_app.
  destruct (n =? cap).
  - destruct (Z.eqb_spec cap 0) as [E0|E0].
    + subst cap. change (0 =? 0) with true. cbv iota. rewrite net_malloc, net_nil, net_malloc, net_nil.
      change (16 * 8) with 128. change (16 * 0) with 0. rewrite (tz_nz 128) by lia. change (tz 0) with 0. lia.
    + rewrite net_realloc, net_nil, net_malloc, net_nil.
      rewrite (tz_nz (16 * (cap * 2))) by lia. rewrite (tz_nz (16 * cap)) by lia.
      replace (16 * (cap * 2)) with (32 * cap) by lia. lia.
  - rewrite net_nil, net_malloc, net_nil. lia.
Qed.
Lemma acc_pushes : forall ls n cap j v rs,
  net (fst (fst (drain_b_c.pushes_run n cap ls j v rs))) =
    tz (16 * snd (fst (drain_b_c.pushes_run n cap ls j v rs))) - tz (16 * cap) + ws ls.
Proof.
  induction ls as [|l ls IH]; intros n cap j v rs; cbn [drain_b_c.pushes_run fst snd].
  - rewrite net_nil, ws_nil. lia.
  - rewrite net_app, acc_push_tra, IH, ws_cons. lia.
Qed.
(* gesture_seen: the held array's growth and a key's strndup, or a key's free *)
Lemma acc_ws_perm : forall T1 T2, Permutation T1 T2 -> ws T1 = ws T2.
Proof.
  intros T1 T2 H. induction H as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2]; [reflexivity| | |].
  - rewrite !ws_cons, IH. reflexivity.
  - rewrite !ws_cons. lia.
  - lia.
Qed.
Lemma acc_ws_swap : forall (H : list (list Z)) n, (n < length H)%nat ->
  ws (swap_remove [] n H) = ws H - zb (P (Z.of_nat (length (nth n H [])) + 1)).
Proof.
  intros H n Hn. rewrite (acc_ws_perm _ _ (relay_instance_gone_b_lem.rigl_swap_perm [] n H Hn)), ws_cons. lia.
Qed.
Lemma acc_seen : forall H ka l j ha ks,
  net (fst (fst (drain_b_c.seen_tr H ka l j ha ks))) =
    tz (snd (fst (drain_b_c.seen_tr H ka l j ha ks))) - tz ka + ws (seen_arr H l) - ws H.
Proof.
  intros H ka l j ha ks. unfold drain_b_c.seen_tr, seen_arr.
  destruct (gesture l) as [[[|] x]|]; cbn [fst snd]; [| |rewrite net_nil; lia].
  - destruct (index_of x H) as [n|] eqn:Ei; cbn [fst snd]; [rewrite net_nil; lia|].
    rewrite (tz_nz ((Z.of_nat (length H) + 1) * 8)) by lia. rewrite ws_app, ws_cons, ws_nil.
    destruct (Z.eqb_spec ka 0) as [E0|E0].
    + subst ka. rewrite net_malloc, net_malloc, net_nil. change (tz 0) with 0. lia.
    + rewrite net_realloc, net_malloc, net_nil, (tz_nz ka E0). lia.
  - destruct (index_of x H) as [n|] eqn:Ei; cbn [fst snd]; [|rewrite net_nil; lia].
    destruct (index_of_some x H n Ei) as (a & b & -> & <-).
    assert (EN : nth (length a) (a ++ x :: b) [] = x) by (rewrite app_nth2, Nat.sub_diag by lia; reflexivity).
    rewrite acc_ws_swap by (rewrite length_app; cbn; lia). rewrite EN, net_free, net_nil. lia.
Qed.
(* the relayed lines: each send_line, then gesture_seen *)
Lemma acc_lines : forall ls live mx no cap H ka j o ha ks, 0 <= cap ->
  net (fst (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks))) =
    tz (fst (fst (snd (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks))))) - tz cap +
    tz (snd (snd (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks)))) - tz ka +
    ws (snd (fst (snd (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks))))) - ws H /\
  0 <= fst (fst (snd (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks)))).
Proof.
  induction ls as [|l ls IH]; intros live mx no cap H ka j o ha ks Hc; cbn [drain_b_c.lines_run fst snd].
  - rewrite net_nil. split; [lia | exact Hc].
  - rewrite !net_app, acc_seen.
    destruct (acc_send_line live mx no cap (Z.of_nat (length l) + 1) j o Hc) as (A1 & B1).
    rewrite A1.
    match goal with |- context [drain_b_c.lines_run live mx ?n ?c ?H1 ?k1 ls ?jj ?oo ?hh ?kk] =>
      destruct (IH live mx n c H1 k1 jj oo hh kk B1) as (A2 & B2) end.
    rewrite A2. split; [lia | exact B2].
Qed.

(* ================================================================== drain: the model change is at most the net *)
(* the blocks a drain's state names: the buffer, the held array, the held keys, the expected list's vector and g_out *)
Definition dphi (s : drain_b_c.dstate) : Z :=
  tz (drain_b_c.ds_cap s) + tz (drain_b_c.ds_ka s) + ws (drain_b_c.ds_H s) + tz (16 * drain_b_c.ds_ecap s) +
  tz (drain_b_c.ds_ocap s).
Lemma acc_drain : forall f live mx s j a, relay_instance_gone_b_lem.dr_inv s -> 0 <= drain_b_c.ds_ocap s ->
  (length (relay_instance_gone_b_lem.dr_rest s) + (if drain_b_c.ds_eintr s then 2 else 1) <= f)%nat ->
  dphi (fst (snd (drain_b_c.drain_run f live mx s j a))) - dphi s +
    ws (lines (drain_b_c.ds_ref s) (relay_instance_gone_b_lem.dr_rest s)) - ws (drain_b_c.ds_pend s)
    <= net (fst (drain_b_c.drain_run f live mx s j a)) /\
  0 <= drain_b_c.ds_ocap (fst (snd (drain_b_c.drain_run f live mx s j a))).
Proof.
  induction f as [|f IH]; intros live mx [c u sk H ka ei pd off rf en ec no oc] j a INV HO FU;
    [destruct ei; cbn [drain_b_c.ds_eintr] in FU; lia|].
  unfold relay_instance_gone_b_lem.dr_inv in INV. unfold relay_instance_gone_b_lem.dr_rest in FU |- *.
  cbn [drain_b_c.ds_u drain_b_c.ds_skip drain_b_c.ds_ref drain_b_c.ds_cap drain_b_c.ds_pend drain_b_c.ds_off
       drain_b_c.ds_eintr drain_b_c.ds_ocap] in INV, FU, HO |- *.
  destruct INV as (J & HC & HP).
  pose proof J as (Jk & Jw & Jl & Jz).
  pose proof (relay_instance_gone_b_lem.rig_ll_z _ Jl) as UL'.
  assert (UL'' : 0 <= Z.of_nat (length u) <= 6000) by lia.
  pose proof (relay_instance_gone_b_lem.rig_grow c (Z.of_nat (length u)) j (drain_b_c.da_buf a) HC UL'') as [G1 G2].
  pose proof (acc_grow c (Z.of_nat (length u)) j (drain_b_c.da_buf a)) as GN.
  cbn [drain_b_c.drain_run drain_b_c.ds_cap drain_b_c.ds_u drain_b_c.ds_skip drain_b_c.ds_H drain_b_c.ds_ka
       drain_b_c.ds_eintr drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_en drain_b_c.ds_ecap
       drain_b_c.ds_no drain_b_c.ds_ocap].
  set (cp := fst (snd (drain_b_c.grow_tr c (Z.of_nat (length u)) j (drain_b_c.da_buf a)))) in *.
  destruct ei; cbv beta iota in FU.
  - assert (IV : relay_instance_gone_b_lem.dr_inv (drain_b_c.DS cp u sk H ka false pd off rf en ec no oc)).
    { unfold relay_instance_gone_b_lem.dr_inv. cbn. split; [exact J|]. split; [lia | exact HP]. }
    assert (FU1 : (length (relay_instance_gone_b_lem.dr_rest (drain_b_c.DS cp u sk H ka false pd off rf en ec no oc)) +
                   (if drain_b_c.ds_eintr (drain_b_c.DS cp u sk H ka false pd off rf en ec no oc) then 2 else 1) <= f)%nat).
    { unfold relay_instance_gone_b_lem.dr_rest. cbn. lia. }
    match goal with |- context [drain_b_c.drain_run f live mx (drain_b_c.DS cp u sk H ka false pd off rf en ec no oc) ?jj ?aa] =>
      destruct (IH live mx _ jj aa IV HO FU1) as [E1 E2] end.
    unfold relay_instance_gone_b_lem.dr_rest in E1. cbn [fst snd] in *. rewrite net_app, GN.
    unfold dphi in *. cbn [drain_b_c.ds_cap drain_b_c.ds_ka drain_b_c.ds_H drain_b_c.ds_ecap drain_b_c.ds_ocap
      drain_b_c.ds_ref drain_b_c.ds_pend drain_b_c.ds_off] in E1 |- *. split; [lia | exact E2].
  - destruct pd as [|r0 rs].
    + cbn [relay_instance_gone_b_lem.dr_rest_of fst snd]. rewrite lines_nil, GN. unfold dphi.
      cbn [drain_b_c.ds_cap drain_b_c.ds_ka drain_b_c.ds_H drain_b_c.ds_ecap drain_b_c.ds_ocap drain_b_c.ds_pend].
      rewrite ws_nil. split; [lia | exact HO].
    + destruct HP as [HOF HF].
      match goal with |- context [Z.min ?a ?b <=? 0] => remember (Z.min a b) as nn eqn:Enn end.
      assert (NP : 0 < nn) by (rewrite Enn; lia).
      destruct (Z.leb_spec nn 0) as [X|X]; [lia|]. clear X.
      set (d := firstn (Z.to_nat nn) (skipn (Z.to_nat off) r0)) in *.
      pose proof (chunk_ok u sk rf d J) as CK.
      destruct (chunk u sk d) as [[u' sk'] rl] eqn:ECH.
      destruct CK as [Erl J'].
      set (PEND := if off + nn =? Z.of_nat (length r0) then rs else r0 :: rs) in *.
      set (OFF := if off + nn =? Z.of_nat (length r0) then 0 else off + nn) in *.
      assert (RS : relay_instance_gone_b_lem.dr_rest_of (r0 :: rs) off = d ++ relay_instance_gone_b_lem.dr_rest_of PEND OFF /\
                   relay_instance_gone_b_lem.dr_pend_ok PEND OFF).
      { unfold PEND, OFF, d. cbn [relay_instance_gone_b_lem.dr_rest_of].
        destruct (Z.eqb_spec (off + nn) (Z.of_nat (length r0))) as [W|W].
        - split.
          + rewrite firstn_all2 by (rewrite length_skipn; lia). f_equal.
            destruct rs as [|r1 rs1]; reflexivity.
          + destruct rs as [|r1 rs1]; [exact I|]. inversion HF as [|? ? HF1 HF2]; subst. cbn [relay_instance_gone_b_lem.dr_pend_ok].
            split; [lia | exact HF2].
        - split.
          + cbn [relay_instance_gone_b_lem.dr_rest_of]. replace (Z.to_nat (off + nn)) with (Z.to_nat nn + Z.to_nat off)%nat by lia.
            rewrite <- skipn_skipn, app_assoc, firstn_skipn. reflexivity.
          + cbn [relay_instance_gone_b_lem.dr_pend_ok]. split; [lia | exact HF]. }
      destruct RS as [RS1 RS2].
      assert (PW : ws (r0 :: rs) - ws PEND = if off + nn =? Z.of_nat (length r0) then zb (P (Z.of_nat (length r0) + 1)) else 0).
      { unfold PEND. destruct (off + nn =? Z.of_nat (length r0)); rewrite ws_cons; lia. }
      assert (TD : forall aa, net (if off + nn =? Z.of_nat (length r0) then ListTr.list_drop_tra aa (Z.of_nat (length r0)) else [])
                   = - (if off + nn =? Z.of_nat (length r0) then zb (P (Z.of_nat (length r0) + 1)) else 0)).
      { intros aa. destruct (off + nn =? Z.of_nat (length r0)); [unfold ListTr.list_drop_tra; rewrite net_free, net_nil|
          rewrite net_nil]; lia. }
      fold PEND OFF.
      match goal with |- context [drain_b_c.pushes_run en ec ?ls ?j1 ?ev ?er] =>
        pose proof (acc_pushes ls en ec j1 ev er) as PU;
        destruct (drain_b_c.pushes_run en ec ls j1 ev er) as [[tpu ec'] [v' rs']] eqn:EPU end.
      cbn [fst snd] in PU |- *.
      match goal with |- context [drain_b_c.lines_run live mx no oc H ka rl ?j3 ?o3 ?h3 ?k3] =>
        destruct (acc_lines rl live mx no oc H ka j3 o3 h3 k3 HO) as [SL SLo];
        destruct (drain_b_c.lines_run live mx no oc H ka rl j3 o3 h3 k3) as [[t1 [[oc1 H1] ka1]] [[o1 ha1] ks1]] end.
      cbn [fst snd] in SL, SLo |- *.
      assert (IVG : relay_instance_gone_b_lem.dr_inv (drain_b_c.DS cp u' sk' H1 ka1 false PEND OFF (feed rf d)
                      (en + Z.of_nat (length (lines rf d))) ec' (no + Z.of_nat (length (with_nul rl))) oc1)).
      { unfold relay_instance_gone_b_lem.dr_inv. cbn. split; [exact J'|]. split; [lia | exact RS2]. }
      assert (FUG : (length (relay_instance_gone_b_lem.dr_rest (drain_b_c.DS cp u' sk' H1 ka1 false PEND OFF (feed rf d)
                      (en + Z.of_nat (length (lines rf d))) ec' (no + Z.of_nat (length (with_nul rl))) oc1)) +
                     (if drain_b_c.ds_eintr (drain_b_c.DS cp u' sk' H1 ka1 false PEND OFF (feed rf d)
                      (en + Z.of_nat (length (lines rf d))) ec' (no + Z.of_nat (length (with_nul rl))) oc1) then 2 else 1)
                     <= f)%nat).
      { unfold relay_instance_gone_b_lem.dr_rest. cbn. rewrite RS1, length_app in FU.
        assert (length d = Z.to_nat nn) by (unfold d; rewrite firstn_length_le by (rewrite length_skipn; lia); reflexivity).
        lia. }
      match goal with |- context [drain_b_c.drain_run f live mx (drain_b_c.DS cp u' sk' H1 ka1 false PEND OFF (feed rf d)
                         ?en' ec' ?no' oc1) ?jj ?aa] =>
        assert (EQS : en' = en + Z.of_nat (length (lines rf d)) /\ no' = no + Z.of_nat (length (with_nul rl)))
          by (split; reflexivity);
        destruct (IH live mx _ jj aa IVG SLo FUG) as [E1 E2] end.
      unfold relay_instance_gone_b_lem.dr_rest in E1. cbn [drain_b_c.ds_ref drain_b_c.ds_pend drain_b_c.ds_off] in E1.
      rewrite !net_app, GN, PU, TD, SL.
      rewrite RS1, lines_app, ws_app. unfold dphi in *.
      cbn [drain_b_c.ds_cap drain_b_c.ds_ka drain_b_c.ds_H drain_b_c.ds_ecap drain_b_c.ds_ocap] in E1 |- *.
      split; [lia | exact E2].
Qed.
End acc.

(* ================================================================== the drain's model fields do not depend on its sends *)
(* the held array's size after the relayed lines: lines_run's, with no send and no names *)
Fixpoint acc_kaf (H : list (list Z)) (ka : Z) (ls : list (list Z)) : Z :=
  match ls with
  | [] => ka
  | l :: r => acc_kaf (seen_arr H l) (snd (fst (drain_b_c.seen_tr H ka l 0 RelayRunF.adr0 []))) r
  end.
Lemma acc_lines_hk : forall ls live mx no cap H ka j o ha ks,
  snd (fst (snd (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks)))) = fold_left seen_arr ls H /\
  snd (snd (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks))) = acc_kaf H ka ls.
Proof.
  induction ls as [|l ls IH]; intros live mx no cap H ka j o ha ks; cbn [drain_b_c.lines_run fst snd]; [split; reflexivity|].
  cbn [fold_left acc_kaf].
  match goal with |- context [drain_b_c.lines_run live mx ?n ?c ?H1 ?k1 ls ?jj ?oo ?hh ?kk] =>
    destruct (IH live mx n c H1 k1 jj oo hh kk) as (E1 & E2) end.
  rewrite E1, E2. split; [reflexivity|]. f_equal. apply RelayCap.rc_seen_ka.
Qed.
(* a drain state with g_nout and g_capout forgotten *)
Definition acc_canon (s : drain_b_c.dstate) : drain_b_c.dstate :=
  drain_b_c.DS (drain_b_c.ds_cap s) (drain_b_c.ds_u s) (drain_b_c.ds_skip s) (drain_b_c.ds_H s) (drain_b_c.ds_ka s)
    (drain_b_c.ds_eintr s) (drain_b_c.ds_pend s) (drain_b_c.ds_off s) (drain_b_c.ds_ref s) (drain_b_c.ds_en s)
    (drain_b_c.ds_ecap s) 0 0.
Lemma acc_drain_canon : forall f live mx s j a,
  acc_canon (fst (snd (drain_b_c.drain_run f live mx s j a))) =
  acc_canon (fst (snd (drain_b_c.drain_run f false 0 (acc_canon s) 0 drain_b_c.dadr0))).
Proof.
  induction f as [|f IH]; intros live mx [c u sk H ka ei pd off rf en ec no oc] j a; [reflexivity|].
  unfold acc_canon at 3. cbn [drain_b_c.ds_cap drain_b_c.ds_u drain_b_c.ds_skip drain_b_c.ds_H drain_b_c.ds_ka
    drain_b_c.ds_eintr drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_en drain_b_c.ds_ecap].
  cbn [drain_b_c.drain_run drain_b_c.ds_cap drain_b_c.ds_u drain_b_c.ds_skip drain_b_c.ds_H drain_b_c.ds_ka
       drain_b_c.ds_eintr drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_en drain_b_c.ds_ecap
       drain_b_c.ds_no drain_b_c.ds_ocap].
  rewrite (RelayCap.rc_grow_cap c (Z.of_nat (length u)) j (drain_b_c.da_buf a) 0 (drain_b_c.da_buf drain_b_c.dadr0)).
  set (cp := fst (snd (drain_b_c.grow_tr c (Z.of_nat (length u)) 0 (drain_b_c.da_buf drain_b_c.dadr0)))).
  destruct ei.
  - cbn [fst snd]. rewrite IH. symmetry. rewrite IH. reflexivity.
  - destruct pd as [|r0 rs]; [reflexivity|].
    match goal with |- context [Z.min ?x ?y <=? 0] => destruct (Z.min x y <=? 0) end; [reflexivity|].
    match goal with |- context [chunk u sk ?d] => destruct (chunk u sk d) as [[u' sk'] rl] end.
    match goal with |- context [drain_b_c.lines_run live mx no oc H ka rl ?j3 ?o3 ?h3 ?k3] =>
      destruct (acc_lines_hk rl live mx no oc H ka j3 o3 h3 k3) as (L1 & L2);
      destruct (drain_b_c.lines_run live mx no oc H ka rl j3 o3 h3 k3) as [[t1 [[oc1 H1] ka1]] [[o1 ha1] ks1]] end.
    match goal with |- context [drain_b_c.lines_run false 0 0 0 H ka rl ?j3 ?o3 ?h3 ?k3] =>
      destruct (acc_lines_hk rl false 0 0 0 H ka j3 o3 h3 k3) as (L3 & L4);
      destruct (drain_b_c.lines_run false 0 0 0 H ka rl j3 o3 h3 k3) as [[t2 [[oc2 H2] ka2]] [[o2 ha2] ks2]] end.
    cbn [fst snd] in L1, L2, L3, L4 |- *. subst H1 H2 ka1 ka2.
    match goal with |- context [drain_b_c.pushes_run en ec ?ls ?j1 ?v1 ?r1] =>
      match goal with |- context [drain_b_c.pushes_run en ec ls ?j2 ?v2 ?r2] =>
        tryif constr_eq j1 j2 then fail else
        rewrite (RelayCap.rc_pushes_cap ls en ec j1 v1 r1 j2 v2 r2) end end.
    rewrite IH. symmetry. rewrite IH. reflexivity.
Qed.
Lemma acc_fin_canon : forall live live' mx mx' NO NO' CAP CAP' e h,
  acc_canon (drain_b_c.drain_fin live mx NO CAP e h) = acc_canon (drain_b_c.drain_fin live' mx' NO' CAP' e h).
Proof.
  intros. unfold drain_b_c.drain_fin, drain_b_c.drain_go. rewrite acc_drain_canon. symmetry. rewrite acc_drain_canon.
  reflexivity.
Qed.
Lemma acc_fin_state : forall f live mx s j a j' a',
  fst (snd (drain_b_c.drain_run f live mx s j a)) = fst (snd (drain_b_c.drain_run f live mx s j' a')).
Proof. intros. apply RelayCap.rc_drain_state. Qed.

(* ================================================================== the keys gestures_end_instance ends *)
Lemma acc_geik : forall f pre n (K : list (Z * list byte * list byte)),
  map (fun k => bzs (gestures_end_b_c.key_text k)) (fst (geik_loop f pre n K)) =
    fst (gei_loop f pre n (map (fun k => bzs (gestures_end_b_c.key_text k)) K)) /\
  map (fun k => bzs (gestures_end_b_c.key_text k)) (snd (geik_loop f pre n K)) =
    snd (gei_loop f pre n (map (fun k => bzs (gestures_end_b_c.key_text k)) K)).
Proof.
  induction f as [|f IH]; intros pre n K; cbn [geik_loop gei_loop]; [split; reflexivity|].
  rewrite length_map.
  destruct (Nat.ltb_spec n (length K)) as [Hn|Hn]; [|split; reflexivity].
  assert (EN : nth n (map (fun k => bzs (gestures_end_b_c.key_text k)) K) [] =
               bzs (gestures_end_b_c.key_text (nth n K (0, [], [])))).
  { exact (map_nth (fun k : Z * list byte * list byte => bzs (gestures_end_b_c.key_text k)) K (0, [], []) n). }
  rewrite EN. destruct (has_prefix pre (bzs (gestures_end_b_c.key_text (nth n K (0, [], []))))).
  - assert (SW : swap_remove [] n (map (fun k : Z * list byte * list byte => bzs (gestures_end_b_c.key_text k)) K) =
                 map (fun k : Z * list byte * list byte => bzs (gestures_end_b_c.key_text k)) (swap_remove (0, [], []) n K))
      by (rewrite RelayCap.rc_swap_map; reflexivity).
    rewrite SW.
    destruct (IH pre n (swap_remove (0, [], []) n K)) as (E1 & E2).
    destruct (geik_loop f pre n (swap_remove (0, [], []) n K)) as [Ek Kk].
    destruct (gei_loop f pre n (map (fun k => bzs (gestures_end_b_c.key_text k)) (swap_remove (0, [], []) n K)))
      as [Eg Kg].
    cbn [fst snd map] in *. rewrite E1, E2. split; reflexivity.
  - apply IH.
Qed.
Lemma acc_gei_perm : forall f pre n (H : list (list Z)),
  Permutation H (fst (gei_loop f pre n H) ++ snd (gei_loop f pre n H)).
Proof.
  induction f as [|f IH]; intros pre n H; cbn [gei_loop]; [apply Permutation_refl|].
  destruct (Nat.ltb_spec n (length H)) as [Hn|Hn]; [|apply Permutation_refl].
  destruct (has_prefix pre (nth n H [])); [|apply IH].
  pose proof (IH pre n (swap_remove [] n H)) as P1.
  destruct (gei_loop f pre n (swap_remove [] n H)) as [E K]. cbn [fst snd app] in *.
  eapply perm_trans; [exact (relay_instance_gone_b_lem.rigl_swap_perm [] n H Hn)|].
  apply perm_skip. exact P1.
Qed.

(* ================================================================== relay_instance_gone's helpers (ReplyGnCnt.v's
   Section rig) *)
Section rig.
Variable P : Z -> bool.
Local Abbreviation net := (ReplyTrPeakW.tr_net_w (fun n => zb (P n))).
Local Abbreviation tz := (tz P).
Local Abbreviation za := (za P).
Local Abbreviation ws := (ws P).

Lemma acc_ws_len : forall T1 T2, map (@length Z) T1 = map (@length Z) T2 -> ws T1 = ws T2.
Proof.
  induction T1 as [|x T1 IH]; intros [|y T2] E; cbn in E; try discriminate; [reflexivity|].
  injection E as E1 E2. rewrite !ws_cons, E1, (IH T2 E2). reflexivity.
Qed.
Lemma acc_hpkh : forall e, (re_hp e = 0 /\ re_keys e = []) \/ (re_hp e <> 0 /\ 8 <= re_kh e) ->
  (if re_hp e =? 0 then 0 else zb (P (re_kh e))) = tz (drain_b_c.ent_ka e).
Proof.
  intros e [(E & _)|(E & K)]; unfold drain_b_c.ent_ka; rewrite ?E; [reflexivity|].
  rewrite (proj2 (Z.eqb_neq _ _) E). rewrite tz_nz by lia. reflexivity.
Qed.
(* the source a drain leaves, against the one it read: the pending texts go, the expected list takes the lines *)
Lemma acc_texts_lines : forall (h h' : hsrc),
  hl_recs (hs_expected h) = [] ->
  map snd (hl_recs (hs_expected h')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  ws (texts (hs_expected h')) = ws (dr_lines h).
Proof.
  intros h h' E0 Ex. rewrite E0 in Ex. cbn [map app] in Ex. apply acc_ws_len. unfold texts.
  rewrite <- (map_map snd bzs), Ex, !map_map. apply map_ext. intros l. unfold bzs. rewrite !length_map. reflexivity.
Qed.
End rig.

(* ================================================================== the model relay_instance_gone leaves: g_out *)
Section mrig.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable P : Z -> bool.
Local Abbreviation za := (za P).
Local Abbreviation tz := (tz P).

Lemma acc_za_out : forall cap out, za (aout_blks cap out) = tz cap.
Proof.
  intros cap out. unfold aout_blks, tz. destruct (cap =? 0); [reflexivity|]. rewrite za_cons, za_nil. cbn [snd]. lia.
Qed.
End mrig.
