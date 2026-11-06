From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import send_line_c gesture_end_c relay_event_c
  RelayFrame RelayModel RelayKeys send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c
  RelayRep HarnessRep drain_b_c relay_remove_b_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma rma_firstn_app : forall {X : Type} (l1 l2 : list X), firstn (length l1) (l1 ++ l2) = l1.
Proof. intros X l1 l2. induction l1 as [|a l1 IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma rma_skipn_app_S : forall {X : Type} (l1 l2 : list X) (x : X), skipn (S (length l1)) (l1 ++ x :: l2) = l2.
Proof. intros X l1 l2 x. induction l1 as [|a l1 IH]; cbn; [reflexivity|]. exact IH. Qed.

Lemma rma_remove_at_last : forall {X : Type} (l : list X) (x : X), remove_at (length l) (l ++ [x]) = l.
Proof.
  intros X l x. unfold remove_at. rewrite rev_unit. cbv beta iota zeta.
  rewrite rev_involutive, Nat.eqb_refl. reflexivity.
Qed.

Lemma rma_remove_at_mid : forall {X : Type} (l1 l2 : list X) (x z : X),
  remove_at (length l1) (l1 ++ x :: l2 ++ [z]) = l1 ++ z :: l2.
Proof.
  intros X l1 l2 x z. unfold remove_at.
  replace (l1 ++ x :: l2 ++ [z]) with ((l1 ++ x :: l2) ++ [z]) by (rewrite <- app_assoc; reflexivity).
  rewrite rev_unit. cbv beta iota zeta. rewrite rev_involutive.
  replace (Nat.eqb (length l1) (length (l1 ++ x :: l2))) with false
    by (symmetry; apply Nat.eqb_neq; rewrite app_length; cbn [length]; lia).
  rewrite rma_firstn_app, rma_skipn_app_S. reflexivity.
Qed.

Lemma rma_nodup_std : forall {X : Type} (l : list X), NoDup l -> List.NoDup l.
Proof.
  intros X l H. induction H as [|x l Hn _ IH]; constructor; [|exact IH].
  intros Hi. apply Hn. clear -Hi. induction l as [|y l IHl]; [destruct Hi|].
  destruct Hi as [->|Hi]; hnf; [constructor 1 | constructor 2; exact (IHl Hi)].
Qed.

Lemma rma_nodup_of_std : forall {X : Type} (l : list X), List.NoDup l -> NoDup l.
Proof.
  intros X l H. induction H as [|x l Hn _ IH]; constructor; [|exact IH].
  intros Hm. apply Hn. clear -Hm. induction l as [|y l IHl]; hnf in Hm; inversion Hm; subst.
  - left. reflexivity.
  - right. apply IHl. assumption.
Qed.

Lemma rma_nodup_map_nth : forall {X Y : Type} (f : X -> Y) (l : list X) (d : X) (i i' : nat),
  NoDup (map f l) -> (i < length l)%nat -> (i' < length l)%nat -> f (nth i l d) = f (nth i' l d) -> i = i'.
Proof.
  intros X Y f l d i i' H Hi Hi' E.
  assert (L : length (map f l) = length l) by apply length_map.
  apply (proj1 (NoDup_nth (map f l) (f d)) (rma_nodup_std _ H) i i'); [lia | lia | rewrite !map_nth; exact E].
Qed.

Lemma rma_split_nth : forall {X : Type} (l : list X) (d : X) (i : nat), (i < length l)%nat ->
  l = firstn i l ++ nth i l d :: skipn (S i) l.
Proof.
  intros X l d. induction l as [|a l IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; [reflexivity|]. cbn [firstn nth skipn app]. f_equal. apply IH. lia.
Qed.

Lemma rma_entry_len : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  length (entry_bytes e) = 56%nat.
Proof.
  intros e H1 H2. unfold entry_bytes. rewrite !app_length, !length_le4, !length_le8, H1, H2. reflexivity.
Qed.

Lemma rma_concat_len : forall es, Forall (fun e => length (entry_bytes e) = 56%nat) es ->
  length (concat (map entry_bytes es)) = (56 * length es)%nat.
Proof.
  induction es as [|e es IH]; intros H; [reflexivity|].
  apply Forall_cons_iff in H as [He Hes]. cbn [map concat]. rewrite app_length, He, (IH Hes). cbn [length]. lia.
Qed.

Lemma rma_nodup_mid_std : forall {X : Type} (l1 l2 l3 : list X), List.NoDup (l1 ++ l2 ++ l3) -> List.NoDup (l1 ++ l3).
Proof.
  intros X l1 l2 l3. induction l1 as [|a l1 IH]; cbn [app]; intros H.
  - revert H. induction l2 as [|b l2 IH2]; cbn [app]; intros H; [exact H|].
    apply IH2. apply NoDup_cons_iff in H as [_ Hl]. exact Hl.
  - apply NoDup_cons_iff in H as [Ha Hl]. constructor.
    + intros Hin. apply Ha. apply in_app_iff in Hin. apply in_app_iff.
      destruct Hin as [Hin|Hin]; [left; exact Hin | right; apply in_app_iff; right; exact Hin].
    + apply IH. exact Hl.
Qed.

Lemma rma_nodup_mid : forall {X : Type} (l1 l2 l3 : list X), NoDup (l1 ++ l2 ++ l3) -> NoDup (l1 ++ l3).
Proof. intros X l1 l2 l3 H. apply rma_nodup_of_std. apply rma_nodup_mid_std with l2. apply rma_nodup_std. exact H. Qed.

Lemma rma_nodup_pick : forall (a b : Z) (es : list rentry) (Y : list Z) (i : nat), (i < length es)%nat ->
  NoDup (a :: b :: concat (map entry_blocks es) ++ Y) -> NoDup (a :: b :: entry_blocks (nth i es no_entry) ++ Y).
Proof.
  intros a b es Y i Hi H.
  rewrite (rma_split_nth es no_entry i Hi) in H.
  rewrite map_app, concat_app in H. cbn [map concat] in H. rewrite <- !app_assoc in H.
  pose proof (rma_nodup_mid [a; b] (concat (map entry_blocks (firstn i es)))
    (entry_blocks (nth i es no_entry) ++ concat (map entry_blocks (skipn (S i) es)) ++ Y) H) as H1.
  exact (rma_nodup_mid ([a; b] ++ entry_blocks (nth i es no_entry)) (concat (map entry_blocks (skipn (S i) es))) Y H1).
Qed.

Ltac rma_send T1 T2 :=
  unfold send_live, send_off;
  destruct (Z.eqb_spec T1 0); destruct (Z.eqb_spec T2 0); destruct (Z.eqb_spec (T1 + T2) 0);
  cbn; intros; first [reflexivity | lia | discriminate | congruence].

Lemma rma_off_br : forall cl br dd T1 T2, (cl = 3 \/ cl = -1) -> (br = 0 \/ br = 1) -> (dd = 0 \/ dd = 1) ->
  0 <= T1 -> 0 <= T2 ->
  (if send_off cl (if send_off cl br T1 then br else dd) T2 then (if send_off cl br T1 then br else dd) else dd) =
  (if send_off cl br (T1 + T2) then br else dd).
Proof.
  intros cl br dd T1 T2 Hc Hb Hd H1 H2.
  destruct Hc as [-> | ->]; destruct Hb as [-> | ->]; destruct Hd as [-> | ->]; rma_send T1 T2.
Qed.

Lemma rma_off_ei : forall cl br dd ei T1 T2, (cl = 3 \/ cl = -1) -> (br = 0 \/ br = 1) -> (dd = 0 \/ dd = 1) ->
  0 <= T1 -> 0 <= T2 ->
  (if send_off cl (if send_off cl br T1 then br else dd) T2 then (if send_off cl br T1 then ei else 0) else 0) =
  (if send_off cl br (T1 + T2) then ei else 0).
Proof.
  intros cl br dd ei T1 T2 Hc Hb Hd H1 H2.
  destruct Hc as [-> | ->]; destruct Hb as [-> | ->]; destruct Hd as [-> | ->]; rma_send T1 T2.
Qed.

Lemma rma_live_or : forall cl br dd T1 T2, (cl = 3 \/ cl = -1) -> (br = 0 \/ br = 1) -> (dd = 0 \/ dd = 1) ->
  0 <= T1 -> 0 <= T2 ->
  send_live cl br dd (T1 + T2) = send_live cl br dd T1 || send_live cl (if send_off cl br T1 then br else dd) dd T2.
Proof.
  intros cl br dd T1 T2 Hc Hb Hd H1 H2.
  destruct Hc as [-> | ->]; destruct Hb as [-> | ->]; destruct Hd as [-> | ->]; rma_send T1 T2.
Qed.

Lemma rma_live_first : forall cl br dd T1 T2, (cl = 3 \/ cl = -1) -> (br = 0 \/ br = 1) -> (dd = 0 \/ dd = 1) ->
  0 <= T1 -> 0 <= T2 ->
  send_live cl br dd T1 = false -> send_live cl (if send_off cl br T1 then br else dd) dd T2 = true -> T1 = 0.
Proof.
  intros cl br dd T1 T2 Hc Hb Hd H1 H2.
  destruct Hc as [-> | ->]; destruct Hb as [-> | ->]; destruct Hd as [-> | ->]; rma_send T1 T2.
Qed.

Lemma rma_live_second : forall cl br dd T1 T2, (cl = 3 \/ cl = -1) -> (br = 0 \/ br = 1) -> (dd = 0 \/ dd = 1) ->
  0 <= T1 -> 0 <= T2 ->
  send_live cl br dd T1 = true -> send_live cl (if send_off cl br T1 then br else dd) dd T2 = false -> T2 = 0.
Proof.
  intros cl br dd T1 T2 Hc Hb Hd H1 H2.
  destruct Hc as [-> | ->]; destruct Hb as [-> | ->]; destruct Hd as [-> | ->]; rma_send T1 T2.
Qed.

Lemma rma_keys_total_nonneg : forall ks, 0 <= keys_total ks.
Proof. unfold keys_total. induction ks as [|k ks IH]; cbn [fold_right]; lia. Qed.

Lemma rma_keys_total_zero : forall ks, keys_total ks = 0 -> ks = [].
Proof.
  intros ks H. destruct ks as [|k ks]; [reflexivity|]. exfalso.
  pose proof (rma_keys_total_nonneg ks) as N. unfold keys_total in *. cbn [fold_right] in H. lia.
Qed.

Lemma rma_keys_total_bound : forall ks, Forall (fun k => Z.of_nat (length (key_text k)) <= 6000) ks ->
  keys_total ks <= 6005 * Z.of_nat (length ks).
Proof.
  unfold keys_total. induction ks as [|k ks IH]; intros H; cbn [fold_right length]; [lia|].
  apply Forall_cons_iff in H as [Hk Hks]. specialize (IH Hks). lia.
Qed.

Lemma rma_keys_fst : forall (ks ks' : list (Z * list byte * list byte)), map fst ks = map fst ks' ->
  keys_total ks = keys_total ks' /\ keys_out ks = keys_out ks' /\ keys_texts ks = keys_texts ks' /\
  map key_addr ks = map key_addr ks' /\ length ks = length ks'.
Proof.
  induction ks as [|k ks IH]; intros [|k' ks'] H; cbn [map] in H; try discriminate.
  - repeat split; reflexivity.
  - injection H as H1 H2. destruct (IH ks' H2) as (T & O & X & A & L).
    unfold keys_total, keys_out, keys_texts, key_addr, key_text in *.
    cbn [fold_right map concat length].
    rewrite H1, T, O, X, A, L. repeat split; reflexivity.
Qed.

Lemma rma_lines_len : forall st d, (length (lines st d) <= length d)%nat.
Proof.
  intros st d. revert st. induction d as [|b d IH]; intros st.
  - rewrite RelayModel.lines_nil. cbn. lia.
  - rewrite RelayModel.lines_cons. specialize (IH (fst (RelayModel.step st b))).
    destruct (snd (RelayModel.step st b)); cbn [length]; lia.
Qed.

Lemma rma_with_nul_cons : forall l ls, with_nul (l :: ls) = (l ++ [0]) ++ with_nul ls.
Proof. reflexivity. Qed.

Lemma rma_wn_inv : forall d st,
  (length (with_nul (lines st d)) + length (ls_w (feed st d)) <= length (ls_w st) + length d)%nat.
Proof.
  induction d as [|b d IH]; intros st.
  - rewrite RelayModel.lines_nil, RelayModel.feed_nil. cbn. lia.
  - rewrite RelayModel.lines_cons, RelayModel.feed_cons. cbn [length].
    destruct (Z.eq_dec b 0) as [->|Hb].
    + rewrite RelayModel.step_zero. cbn [fst snd].
      specialize (IH (RelayModel.LS [] false)). cbn [ls_w length] in IH.
      destruct (ls_k st).
      * lia.
      * rewrite rma_with_nul_cons, !app_length. cbn [length]. lia.
    + destruct (ls_k st) eqn:Hk.
      * rewrite (RelayModel.step_nz_k st b Hb Hk). cbn [fst snd]. specialize (IH st). lia.
      * destruct (Nat.eq_dec (length (ls_w st)) RelayModel.LINE_LIMIT) as [He|He].
        -- rewrite (RelayModel.step_nz_full st b Hb Hk He). cbn [fst snd].
           specialize (IH (RelayModel.LS (ls_w st) true)). cbn [ls_w] in IH. lia.
        -- rewrite (RelayModel.step_nz_add st b Hb Hk He). cbn [fst snd].
           specialize (IH (RelayModel.LS (ls_w st ++ [b]) false)). cbn [ls_w] in IH.
           rewrite app_length in IH. cbn [length] in IH. lia.
Qed.

Lemma rma_with_nul_len : forall st d, (length (with_nul (lines st d)) <= length (ls_w st) + length d)%nat.
Proof. intros st d. pose proof (rma_wn_inv d st). lia. Qed.

Lemma rma_filter_len : forall {X : Type} (f : X -> bool) (l : list X), (length (List.filter f l) <= length l)%nat.
Proof.
  intros X f l. induction l as [|a l IH]; [cbn; lia|]. cbn [List.filter]. destruct (f a); cbn [length]; lia.
Qed.

Lemma rma_upd_len : forall G l, (length (RelayModel.upd G l) <= S (length G))%nat.
Proof.
  intros G l. unfold RelayModel.upd. destruct (RelayModel.gesture l) as [[[|] x]|].
  - match goal with |- context [if ?c then _ else _] => destruct c end; [lia|].
    rewrite app_length. cbn [length]. lia.
  - eapply Nat.le_trans; [apply rma_filter_len | lia].
  - lia.
Qed.

Lemma rma_upds_len : forall G ls, (length (upds G ls) <= length G + length ls)%nat.
Proof.
  intros G ls. revert G. unfold upds. induction ls as [|l ls IH]; intros G; cbn [fold_left length].
  - lia.
  - specialize (IH (RelayModel.upd G l)). pose proof (rma_upd_len G l). lia.
Qed.

Lemma rma_same_set_len : forall X G ls, NoDup X -> same_set X (upds G ls) -> (length X <= length G + length ls)%nat.
Proof.
  intros X G ls ND SS. eapply Nat.le_trans; [|apply rma_upds_len].
  apply NoDup_incl_length; [exact (rma_nodup_std _ ND)|]. intros y Hy. exact (proj1 (SS y) Hy).
Qed.

(* drain's rounds read the stream still pending: the head text from ds_off, then the rest. *)
Definition rma_ds (s : dstate) : list Z :=
  match ds_pend s with
  | [] => []
  | r0 :: rs => skipn (Z.to_nat (ds_off s)) r0 ++ concat rs
  end.

Definition rma_pok (s : dstate) : Prop :=
  0 <= ds_off s /\
  match ds_pend s with
  | [] => True
  | r0 :: rs => ds_off s < Z.of_nat (length r0) /\ Forall (fun r => (1 <= length r)%nat) rs
  end.

Definition rma_cok (s : dstate) : Prop := ds_cap s = 0 \/ 8192 <= ds_cap s.

Lemma rma_round_split : forall (r0 : list Z) rs off n,
  0 <= off -> 0 < n -> off + n <= Z.of_nat (length r0) ->
  skipn (Z.to_nat off) r0 ++ concat rs =
  firstn (Z.to_nat n) (skipn (Z.to_nat off) r0) ++
    (if off + n =? Z.of_nat (length r0) then concat rs else skipn (Z.to_nat (off + n)) r0 ++ concat rs).
Proof.
  intros r0 rs off n H0 H1 H2. destruct (Z.eqb_spec (off + n) (Z.of_nat (length r0))) as [E|E].
  - rewrite (firstn_all2 (n := Z.to_nat n)); [reflexivity|]. rewrite length_skipn. lia.
  - rewrite app_assoc. f_equal. replace (Z.to_nat (off + n)) with (Z.to_nat n + Z.to_nat off)%nat by lia.
    rewrite <- skipn_skipn. symmetry. apply firstn_skipn.
Qed.

Lemma rma_ds_whole : forall (rs : list (list Z)),
  match rs with [] => [] | r1 :: rs' => skipn (Z.to_nat 0) r1 ++ concat rs' end = concat rs.
Proof. intros [|r1 rs]; reflexivity. Qed.

Lemma rma_grow : forall cap used j b, (cap = 0 \/ 8192 <= cap) -> 0 <= used <= 6000 ->
  (fst (snd (grow_tr cap used j b)) = 0 \/ 8192 <= fst (snd (grow_tr cap used j b))) /\
  used < fst (snd (grow_tr cap used j b)).
Proof.
  intros cap used j b Hc Hu. unfold grow_tr.
  destruct (Z.ltb_spec (cap - used) 4096); cbn [fst snd]; [|lia].
  destruct (Z.eqb_spec cap 0); lia.
Qed.

Lemma rma_wn_app : forall l1 l2, with_nul (l1 ++ l2) = with_nul l1 ++ with_nul l2.
Proof. intros l1 l2. unfold with_nul. rewrite map_app. apply concat_app. Qed.

Lemma rma_wn_nil : forall ls, length (with_nul ls) = 0%nat -> ls = [].
Proof.
  intros [|l ls] H; [reflexivity|]. exfalso. rewrite rma_with_nul_cons, !length_app in H. cbn [length] in H. lia.
Qed.

Section DrainRun.

(* A drain whose stream holds no complete line asks nothing of send_line: its run is the same live or not. *)
Lemma rma_dr_live : forall f s live live' mx j a,
  J1 (ds_u s) (ds_skip s) (ds_ref s) -> 0 <= ds_off s -> lines (ds_ref s) (rma_ds s) = [] ->
  drain_run f live mx s j a = drain_run f live' mx s j a.
Proof.
  induction f as [|f IH]; intros s live live' mx j a HJ HO HL; [reflexivity|].
  cbn [drain_run]. cbv zeta. destruct (ds_eintr s).
  - rewrite (IH _ live live' mx _ _); [reflexivity | exact HJ | exact HO | exact HL].
  - unfold rma_ds in HL. destruct (ds_pend s) as [|r0 rs] eqn:P; [reflexivity|].
    match goal with |- context [Z.min ?a ?b <=? 0] => set (n := Z.min a b) end.
    destruct (Z.leb_spec n 0) as [NZ|NZ]; [reflexivity|].
    set (d := firstn (Z.to_nat n) (skipn (Z.to_nat (ds_off s)) r0)).
    destruct (chunk (ds_u s) (ds_skip s) d) as [[u' sk'] rl] eqn:CH.
    pose proof (chunk_ok (ds_u s) (ds_skip s) (ds_ref s) d HJ) as CK. rewrite CH in CK. cbv beta iota in CK.
    destruct CK as [RL J'].
    assert (NL : n <= Z.of_nat (length r0) - ds_off s) by (unfold n; lia).
    rewrite (rma_round_split r0 rs (ds_off s) n HO NZ ltac:(lia)) in HL. fold d in HL.
    rewrite lines_app in HL. apply app_eq_nil in HL as [HL1 HL2].
    rewrite <- RL in HL1. subst rl. cbn [lines_run fst snd].
    revert HL2. destruct (ds_off s + n =? Z.of_nat (length r0)); intros HL2.
    + rewrite (IH _ live live' mx _ _); [reflexivity | exact J' | cbn [ds_off]; lia |].
      unfold rma_ds. cbn [ds_ref ds_pend ds_off]. rewrite rma_ds_whole. exact HL2.
    + rewrite (IH _ live live' mx _ _); [reflexivity | exact J' | cbn [ds_off]; lia |].
      unfold rma_ds. cbn [ds_ref ds_pend ds_off]. exact HL2.
Qed.

(* g_nout after a drain that reads its whole stream within the fuel: every complete line, with its NUL, sent. *)
Lemma rma_dr_no : forall f s live mx j a,
  J1 (ds_u s) (ds_skip s) (ds_ref s) -> rma_pok s -> rma_cok s ->
  (length (rma_ds s) + (if ds_eintr s then 2 else 1) <= f)%nat ->
  ds_no (fst (snd (drain_run f live mx s j a))) =
    ds_no s + Z.of_nat (length (with_nul (lines (ds_ref s) (rma_ds s)))).
Proof.
  induction f as [|f IH]; intros s live mx j a HJ HP HC HF; [revert HF; destruct (ds_eintr s); lia|].
  pose proof HJ as (_ & _ & HU & _).
  assert (HU' : 0 <= Z.of_nat (length (ds_u s)) <= 6000).
  { split; [apply Nat2Z.is_nonneg|]. apply Nat2Z.inj_le in HU. exact HU. }
  pose proof (rma_grow (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a) HC HU') as GR.
  cbn [drain_run]. cbv zeta. destruct (ds_eintr s) eqn:EI.
  - cbn [fst snd]. rewrite IH; [reflexivity | exact HJ | exact HP | exact (proj1 GR) |]. cbn [ds_eintr].
    unfold rma_ds in HF |- *. cbn [ds_pend ds_off]. lia.
  - unfold rma_ds in HF |- *. destruct HP as [HO HP]. destruct (ds_pend s) as [|r0 rs] eqn:P.
    { cbn [fst snd ds_no]. rewrite lines_nil. cbn. lia. }
    destruct HP as [HP1 HP2].
    match goal with |- context [Z.min ?a ?b <=? 0] => set (n := Z.min a b) end.
    assert (NZ : 0 < n) by (unfold n; lia).
    destruct (Z.leb_spec n 0) as [NZ'|_]; [lia|].
    set (d := firstn (Z.to_nat n) (skipn (Z.to_nat (ds_off s)) r0)).
    destruct (chunk (ds_u s) (ds_skip s) d) as [[u' sk'] rl] eqn:CH.
    pose proof (chunk_ok (ds_u s) (ds_skip s) (ds_ref s) d HJ) as CK. rewrite CH in CK. cbv beta iota in CK.
    destruct CK as [RL J'].
    assert (NL : n <= Z.of_nat (length r0) - ds_off s) by (unfold n; lia).
    assert (LD : length d = Z.to_nat n) by (unfold d; rewrite length_firstn, length_skipn; lia).
    rewrite (rma_round_split r0 rs (ds_off s) n HO NZ ltac:(lia)) in HF |- *. fold d in HF |- *.
    rewrite length_app in HF. rewrite lines_app, rma_wn_app, length_app, <- RL.
    match goal with |- context [lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl ?j3 ?o ?ha ?ks] =>
      destruct (lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl j3 o ha ks)
        as [[tl [[oc' H'] ka']] [[o' ha'] ks']] end.
    cbn [fst snd].
    revert HF. destruct (Z.eqb_spec (ds_off s + n) (Z.of_nat (length r0))) as [E|E]; intros HF.
    + rewrite IH; [ | exact J' | | exact (proj1 GR) | ].
      * cbn [ds_no ds_ref]. unfold rma_ds. cbn [ds_pend ds_off]. rewrite rma_ds_whole. lia.
      * unfold rma_pok. cbn [ds_off ds_pend]. split; [lia|].
        destruct rs as [|r1 rs]; [exact I|]. apply Forall_cons_iff in HP2 as [H1 H2]. split; [lia | exact H2].
      * cbn [ds_eintr]. unfold rma_ds. cbn [ds_pend ds_off]. rewrite rma_ds_whole. lia.
    + rewrite IH; [ | exact J' | | exact (proj1 GR) | ].
      * cbn [ds_no ds_ref]. unfold rma_ds. cbn [ds_pend ds_off]. lia.
      * unfold rma_pok. cbn [ds_off ds_pend]. split; [lia|]. split; [lia | exact HP2].
      * cbn [ds_eintr]. unfold rma_ds. cbn [ds_pend ds_off]. lia.
Qed.

Lemma rma_lr_cap : forall rl mx no cap H ka j o ha ks,
  fst (fst (snd (fst (lines_run false mx no cap H ka rl j o ha ks)))) = cap.
Proof.
  induction rl as [|l rl IH]; intros mx no cap H ka j o ha ks; [reflexivity|].
  cbn [lines_run]. cbv zeta. cbn [fst snd]. rewrite IH. reflexivity.
Qed.

(* g_capout after a drain whose sends are dead. *)
Lemma rma_dr_cap : forall f s mx j a, ds_ocap (fst (snd (drain_run f false mx s j a))) = ds_ocap s.
Proof.
  induction f as [|f IH]; intros s mx j a; [reflexivity|].
  cbn [drain_run]. cbv zeta. destruct (ds_eintr s).
  - cbn [fst snd]. rewrite IH. reflexivity.
  - destruct (ds_pend s) as [|r0 rs]; [reflexivity|].
    match goal with |- context [Z.min ?a ?b <=? 0] => destruct (Z.min a b <=? 0) end; [reflexivity|].
    match goal with |- context [chunk ?u ?k ?d] => destruct (chunk u k d) as [[u' sk'] rl] end.
    match goal with |- context [lines_run false mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl ?j3 ?o ?ha ?ks] =>
      pose proof (rma_lr_cap rl mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) j3 o ha ks) as LC;
      destruct (lines_run false mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl j3 o ha ks)
        as [[tl [[oc' H'] ka']] [[o' ha'] ks']] end.
    cbn [snd fst] in LC |- *. rewrite IH. cbn [ds_ocap]. exact LC.
Qed.

Lemma rma_skipn_map : forall {X Y : Type} (f : X -> Y) n l, skipn n (map f l) = map f (skipn n l).
Proof. intros X Y f n. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. apply IH. Qed.

Lemma rma_ds_init : forall NO CAP e h, rma_ds (drain_init NO CAP e h) = bzs (pending_stream h).
Proof.
  intros NO CAP e h. unfold rma_ds, drain_init, pending_stream. cbn [ds_pend ds_off].
  destruct (hl_recs (hs_pending h)) as [|r rs]; [reflexivity|]. cbn [map].
  unfold bzs. rewrite map_app, rma_skipn_map, concat_map, map_map. reflexivity.
Qed.

(* drain's run with the liveness of a send of one byte, as drain's own contract states it (with the liveness of
   its total TOT), and g_nout after it. *)
Lemma rma_fin_live : forall live live' mx NO CAP e h j a,
  J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h) -> 0 <= hs_off h ->
  lines (hs_state h) (bzs (pending_stream h)) = [] ->
  drain_tr live mx NO CAP e h j a = drain_tr live' mx NO CAP e h j a /\
  drain_fin live mx NO CAP e h = drain_fin live' mx NO CAP e h.
Proof.
  intros live live' mx NO CAP e h j a HJ HO HL. unfold drain_tr, drain_fin, drain_go.
  assert (HL' : lines (ds_ref (drain_init NO CAP e h)) (rma_ds (drain_init NO CAP e h)) = [])
    by (rewrite rma_ds_init; exact HL).
  rewrite (rma_dr_live _ (drain_init NO CAP e h) live live' mx j a HJ HO HL').
  rewrite (rma_dr_live _ (drain_init NO CAP e h) live live' mx 0%nat dadr0 HJ HO HL').
  split; reflexivity.
Qed.

Lemma rma_fin_no : forall live mx NO CAP e h,
  J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h) -> rma_pok (drain_init NO CAP e h) ->
  (re_cap e = 0 \/ 8192 <= re_cap e) ->
  ds_no (drain_fin live mx NO CAP e h) =
    NO + Z.of_nat (length (with_nul (lines (hs_state h) (bzs (pending_stream h))))).
Proof.
  intros live mx NO CAP e h HJ HP HC. unfold drain_fin, drain_go.
  rewrite rma_dr_no; [| exact HJ | exact HP | exact HC |].
  - rewrite rma_ds_init. reflexivity.
  - rewrite rma_ds_init. unfold bzs. rewrite length_map. cbn [ds_eintr drain_init].
    destruct (hs_eintr h =? 1); lia.
Qed.

Lemma rma_fin_cap : forall mx NO CAP e h, ds_ocap (drain_fin false mx NO CAP e h) = CAP.
Proof. intros mx NO CAP e h. unfold drain_fin, drain_go. rewrite rma_dr_cap. reflexivity. Qed.
End DrainRun.

Lemma rma_live_nz : forall cl br dd T, T <> 0 -> send_live cl br dd T = send_live cl br dd 1.
Proof.
  intros cl br dd T HT. unfold send_live, send_off.
  rewrite (proj2 (Z.eqb_neq T 0) HT). reflexivity.
Qed.

Lemma rma_ge_dead : forall mx no cap no' cap' xks j o j' o',
  fst (keys_end_run false mx no cap xks j o) = fst (keys_end_run false mx no' cap' xks j' o').
Proof.
  intros mx no cap no' cap' xks. revert no cap no' cap'.
  induction xks as [|[xl ka] xks IH]; intros no cap no' cap' j o j' o'; [reflexivity|].
  cbn [keys_end_run fst gesture_end_tr send_line_tr app]. cbv zeta. cbn [fst app].
  f_equal. apply IH.
Qed.
