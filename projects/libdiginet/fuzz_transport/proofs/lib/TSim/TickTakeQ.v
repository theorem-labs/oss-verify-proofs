(* What agree_q (Agree.v, D) says about the two queues, the session's sq B and the harness's hq B (QueueFacts.v),
   read through take's mask (TakeOk.v), and agree_q after the run (TickTakeW.tt_end).
   - tt_queued_le, tt_sq_ok: every session entry is 32 bytes, 1 <= len <= 24, and body_check accepts its bytes
     (tagged: D1's entry and D2's command; raw: D4).
   - tt_hq_ok, tt_bridge, tt_body_tag: tagged mode; ttq_ent is the bridge between entry i of sq B and serial i
     of hq B (D1's entry over D2's command), so the body take builds is the taken commands' bytes, first byte TAG.
   - tt_qmodel_frame: a frame outside R_nq keeps the harness's queue model (hq only while g_nq <= CMDS_MAX:
     g_q[1024] would read g_fail_next, which R_nq holds).
   - tt_agree_q: the entries / serials not taken, with the taken serials SENT, satisfy agree_q again.
   TRAP (SettleOk.v): no world terms compared by the unifier; every rewrite's left side is in the goal. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links QueueFacts SimLib SendOk SettleOk
  TickDefs TakeOk TickTakeW.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------- lists *)

Lemma ttq_Forall_In : forall {A} (P : A -> Prop) l x, Forall P l -> In x l -> P x.
Proof.
  intros A P l x H. induction H as [|y l Hy _ IH]; intros Hx; [destruct Hx|].
  destruct Hx as [<-|Hx]; [exact Hy | exact (IH Hx)].
Qed.

Lemma ttq_Forall_intro : forall {A} (P : A -> Prop) l, (forall x, In x l -> P x) -> Forall P l.
Proof.
  intros A P l. induction l as [|y l IH]; intros H; constructor.
  - apply H. left. reflexivity.
  - apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

Lemma ttq_Forall2_length : forall {X Y} (R : X -> Y -> Prop) l1 l2, Forall2 R l1 l2 -> length l1 = length l2.
Proof. intros X Y R l1 l2 H. induction H as [|x y l1 l2 _ _ IH]; cbn [length]; lia. Qed.

Lemma ttq_Forall2_nth : forall {X Y} (R : X -> Y -> Prop) l1 l2 n d1 d2, Forall2 R l1 l2 ->
  (n < length l1)%nat -> R (nth n l1 d1) (nth n l2 d2).
Proof.
  intros X Y R l1 l2 n d1 d2 H. revert n.
  induction H as [|x y l1 l2 Hxy _ IH]; intros [|n] Hn; cbn [length nth] in *; try lia.
  - exact Hxy.
  - apply IH. lia.
Qed.

Lemma ttq_Forall2_impl_in : forall {X Y} (R R' : X -> Y -> Prop) l1 l2,
  (forall x y, In y l2 -> R x y -> R' x y) -> Forall2 R l1 l2 -> Forall2 R' l1 l2.
Proof.
  intros X Y R R' l1 l2 Himp H. revert Himp.
  induction H as [|x y l1 l2 Hxy _ IH]; intros Himp; constructor.
  - apply Himp; [left; reflexivity | exact Hxy].
  - apply IH. intros a b Hb Hab. apply Himp; [right; exact Hb | exact Hab].
Qed.

Lemma ttq_Forall2_map_eq : forall {X Y W} (f : X -> W) (g : Y -> W) (R : X -> Y -> Prop) l1 l2,
  (forall x y, R x y -> f x = g y) -> Forall2 R l1 l2 -> map f l1 = map g l2.
Proof.
  intros X Y W f g R l1 l2 Hfg H. induction H as [|x y l1 l2 Hxy _ IH]; cbn [map]; [reflexivity|].
  rewrite (Hfg x y Hxy), IH. reflexivity.
Qed.

Lemma ttq_Forall2_map_same : forall {A X Y} (R : X -> Y -> Prop) (f : A -> X) (g : A -> Y) l,
  (forall x, In x l -> R (f x) (g x)) -> Forall2 R (map f l) (map g l).
Proof.
  intros A X Y R f g l. induction l as [|x l IH]; intros H; cbn [map]; constructor.
  - apply H. left. reflexivity.
  - apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma ttq_map_ext_in : forall {A X} (f g : A -> X) l, (forall x, In x l -> f x = g x) -> map f l = map g l.
Proof.
  intros A X f g l. induction l as [|x l IH]; intros H; cbn [map]; [reflexivity|].
  assert (Ex : f x = g x) by (apply H; left; reflexivity).
  assert (El : map f l = map g l) by (apply IH; intros y Hy; apply H; right; exact Hy).
  rewrite Ex, El. reflexivity.
Qed.

Lemma ttq_in_map : forall {A X} (f : A -> X) l z, In z (map f l) -> exists y, In y l /\ f y = z.
Proof.
  intros A X f l z. induction l as [|y l IH]; cbn [map In]; [intros []|].
  intros [E|H].
  - exists y. split; [left; reflexivity | exact E].
  - destruct (IH H) as [w [Hw E]]. exists w. split; [right; exact Hw | exact E].
Qed.

Lemma ttq_nth_In : forall {A} (l : list A) n d, (n < length l)%nat -> In (nth n l d) l.
Proof.
  intros A l. induction l as [|x l IH]; intros [|n] d Hn; cbn [length nth In] in *; try lia.
  - left. reflexivity.
  - right. apply IH. lia.
Qed.

Lemma ttq_NoDup_nth : forall {A} (l : list A) d i j, List.NoDup l -> (i < length l)%nat -> (j < length l)%nat ->
  nth i l d = nth j l d -> i = j.
Proof.
  intros A l d i j Hnd. revert i j.
  induction Hnd as [|y l Hy Hnd IH]; intros [|i] [|j] Hi Hj E; cbn [length nth] in Hi, Hj, E; try lia.
  - exfalso. apply Hy. rewrite E. apply ttq_nth_In. lia.
  - exfalso. apply Hy. rewrite <- E. apply ttq_nth_In. lia.
  - f_equal. apply IH; [lia | lia | exact E].
Qed.

Lemma ttq_NoDup_map_in : forall {A X} (f : A -> X) l, List.NoDup l ->
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> List.NoDup (map f l).
Proof.
  intros A X f l Hnd. induction Hnd as [|x l Hx Hnd IH]; intros Hf; cbn [map]; constructor.
  - intros Hin. destruct (ttq_in_map f l (f x) Hin) as [y [Hy E]].
    assert (Exy : y = x) by (apply Hf; [right; exact Hy | left; reflexivity | exact E]).
    subst y. exact (Hx Hy).
  - apply IH. intros a b Ha Hb Hab. apply Hf; [right; exact Ha | right; exact Hb | exact Hab].
Qed.

Lemma ttq_length_pick : forall {A} (m : list bool) (l : list A), (length (pick m l) <= length l)%nat.
Proof.
  intros A m l. revert m. induction l as [|x l IH]; intros [|[|] m]; cbn [pick length]; try lia.
  - specialize (IH m). lia.
  - specialize (IH m). lia.
Qed.

(* with the mask as long as the list, an element is taken or kept *)
Lemma ttq_in_pick_or_unpick : forall {A} (m : list bool) (l : list A) x, length m = length l -> In x l ->
  In x (pick m l) \/ In x (unpick m l).
Proof.
  intros A m l x. revert m. unfold unpick.
  induction l as [|y l IH]; intros [|b m] Hlen Hx; cbn [length] in Hlen; try discriminate.
  - destruct Hx.
  - assert (Hl : length m = length l) by lia.
    destruct Hx as [<-|Hx]; destruct b; cbn [pick map negb In].
    + left. left. reflexivity.
    + right. left. reflexivity.
    + destruct (IH m Hl Hx) as [H|H]; [left; right; exact H | right; exact H].
    + destruct (IH m Hl Hx) as [H|H]; [left; exact H | right; right; exact H].
Qed.

(* in a list without duplicates, a kept element is not taken *)
Lemma ttq_pick_unpick_disj : forall {A} (m : list bool) (l : list A) x, List.NoDup l ->
  In x (unpick m l) -> ~ In x (pick m l).
Proof.
  intros A m l x Hnd. revert m. unfold unpick.
  induction Hnd as [|y l Hy Hnd IH]; intros [|[|] m] Hx Hp; cbn [pick map negb In] in Hx, Hp.
  - exact Hp.
  - exact Hp.
  - exact Hp.
  - exact Hp.
  - destruct Hp as [<-|Hp]; [apply Hy; eapply in_pick; exact Hx | exact (IH m Hx Hp)].
  - destruct Hx as [<-|Hx]; [apply Hy; eapply in_pick; exact Hp | exact (IH m Hx Hp)].
Qed.

Lemma ttq_NoDup_pick : forall {A} (m : list bool) (l : list A), List.NoDup l -> List.NoDup (pick m l).
Proof.
  intros A m l Hnd. revert m.
  induction Hnd as [|y l Hy Hnd IH]; intros [|[|] m]; cbn [pick].
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor; [|apply IH]. intros Hin. apply Hy. eapply in_pick. exact Hin.
  - apply IH.
Qed.

(* ---------------------------------------------------------------- the session's queue *)

Lemma tt_queued_le : forall ops B, agree_q ops B -> 0 <= S_queued B <= 512.
Proof.
  intros ops B HQ. pose proof (u_at_nonneg B A_S_queued 4) as H0. fold (S_queued B) in H0.
  destruct (Z.eqb_spec (g_raw B) 0) as [Hr|Hr].
  - pose proof (d1_queued _ _ HQ Hr) as E. pose proof (d1_nq _ _ HQ Hr) as N. unfold QUEUE_MAX in N. lia.
  - pose proof (d4_queued _ _ HQ Hr) as N. unfold QUEUE_MAX in N. lia.
Qed.

Lemma ttq_sq_ent_length : forall B i, length B = WN -> 0 <= i < 512 -> length (sq_ent B i) = 32%nat.
Proof.
  intros B i HB Hi. unfold sq_ent. apply w_length_sub. rewrite HB.
  unfold WN, W_LEN, A_S_queue_bytes, OFF_g_s. lia.
Qed.

(* an entry's first n <= 24 bytes are its command bytes' *)
Lemma ttq_firstn_sq_ent : forall B i n, 0 <= i -> (n <= 24)%nat ->
  firstn n (sq_ent B i) = firstn n (S_queue_bytes B i).
Proof.
  intros B i n Hi Hn. rewrite (S_queue_bytes_ent B i Hi), firstn_firstn, Nat.min_l by exact Hn. reflexivity.
Qed.

Definition ttq_ent_ok (e : list byte) : Prop :=
  length e = 32%nat /\ 1 <= e_len e <= 24 /\ body_check (e_bytes e) = 0.

Lemma tt_sq_ok : forall ops B, length B = WN -> agree_q ops B ->
  Forall (fun e => length e = 32%nat /\ 1 <= e_len e <= 24 /\ body_check (e_bytes e) = 0) (sq B).
Proof.
  intros ops B HB HQ. pose proof (tt_queued_le ops B HQ) as Hq.
  apply ttq_Forall_intro. intros e He. cbv beta. apply tk_In_sq in He as [i [Hi ->]].
  split; [apply ttq_sq_ent_length; [exact HB | lia]|].
  rewrite body_check_spec. unfold e_bytes, e_len.
  rewrite <- (S_queue_len_ent B i) by lia.
  destruct (Z.eqb_spec (g_raw B) 0) as [Hr|Hr].
  - assert (Hi' : 0 <= i < g_nq B) by (rewrite <- (d1_queued _ _ HQ Hr); exact Hi).
    destruct (d1_entry _ _ HQ Hr i Hi') as (Hk & Hst & Hby & Hlen & _ & _).
    destruct (d2_cmd _ _ HQ (Q_at B i) Hk ltac:(rewrite Hst; unfold PENDING; lia)) as (_ & _ & _ & Hl & _ & Hsys).
    rewrite Hlen. split; [lia|].
    rewrite (ttq_firstn_sq_ent B i) by lia. rewrite Hby, Hsys. reflexivity.
  - destruct (d4_entry _ _ HQ Hr i Hi) as (Hl & Hsys).
    split; [exact Hl|].
    rewrite (ttq_firstn_sq_ent B i) by lia. rewrite Hsys. reflexivity.
Qed.

(* ---------------------------------------------------------------- tagged: the bridge between the queues *)

(* entry e of the session's queue is serial k of the harness's: D1's entry over D2's command *)
Definition ttq_ent (B : list byte) (e : list byte) (k : Z) : Prop :=
  firstn 24 e = Cmd_bytes B k /\ e_len e = Cmd_len B k /\ cmd_key_of e = Cmd_key B k /\
  e_disp e = Cmd_display B k /\ e_bytes e = cmd_body B k /\ Cmd_st B k = PENDING /\ 0 <= k < g_ncmd B.

Lemma ttq_ent_bytes : forall B e k, ttq_ent B e k -> e_bytes e = cmd_body B k.
Proof. intros B e k (_ & _ & _ & _ & H & _). exact H. Qed.

Lemma ttq_ent_disp : forall B e k, ttq_ent B e k -> e_disp e = Cmd_display B k.
Proof. intros B e k (_ & _ & _ & H & _). exact H. Qed.

Lemma ttq_ent_at : forall ops B i, agree_q ops B -> g_raw B = 0 -> 0 <= i < g_nq B ->
  ttq_ent B (sq_ent B i) (Q_at B i).
Proof.
  intros ops B i HQ Hr Hi.
  destruct (d1_entry _ _ HQ Hr i Hi) as (Hk & Hst & Hby & Hlen & Hkey & Hdisp).
  destruct (d2_cmd _ _ HQ (Q_at B i) Hk ltac:(rewrite Hst; unfold PENDING; lia)) as (_ & _ & _ & Hl & _ & _).
  unfold ttq_ent, e_bytes, e_len, e_disp.
  rewrite <- (S_queue_bytes_ent B i) by lia.
  rewrite <- (S_queue_len_ent B i) by lia.
  rewrite <- (S_queue_key_ent B i) by lia.
  rewrite <- (S_queue_display_ent B i) by lia.
  split; [exact Hby|]. split; [exact Hlen|]. split; [exact Hkey|]. split; [exact Hdisp|].
  split; [|split; [exact Hst | exact Hk]].
  rewrite Hlen. unfold sq_ent. rewrite sub_firstn by lia.
  unfold cmd_body. apply d1_bytes_len; [exact Hby | lia].
Qed.

Lemma ttq_sq_hq : forall ops B, agree_q ops B -> g_raw B = 0 -> Forall2 (ttq_ent B) (sq B) (hq B).
Proof.
  intros ops B HQ Hr. pose proof (u_at_nonneg B OFF_g_nq 4) as H0. fold (g_nq B) in H0.
  unfold sq, hq. rewrite (d1_queued _ _ HQ Hr).
  apply ttq_Forall2_map_same. intros i Hi. apply in_zseq in Hi.
  apply (ttq_ent_at ops B i HQ Hr). lia.
Qed.

Lemma tt_hq_ok : forall ops B, length B = WN -> agree_q ops B -> g_raw B = 0 ->
  0 <= g_nq B <= QUEUE_MAX /\ List.NoDup (hq B) /\ Forall (tagged_ok B) (hq B) /\ length (hq B) = length (sq B).
Proof.
  intros ops B HB HQ Hr. pose proof (u_at_nonneg B OFF_g_nq 4) as H0. fold (g_nq B) in H0.
  pose proof (d1_nq _ _ HQ Hr) as Hnq. pose proof (d3_ncmd _ _ HQ) as Hn1. pose proof (d3_ops _ _ HQ) as Hn2.
  split; [lia|]. split; [|split].
  - unfold hq. apply ttq_NoDup_map_in; [apply NoDup_zseq|].
    intros i j Hi Hj E. apply in_zseq in Hi. apply in_zseq in Hj.
    apply (d1_nodup _ _ HQ Hr i j); [lia | lia | exact E].
  - apply ttq_Forall_intro. intros k Hk. apply tk_In_hq in Hk as [i [Hi ->]].
    destruct (d1_entry _ _ HQ Hr i Hi) as (Hk & Hst & _ & _ & _ & _).
    destruct (d2_cmd _ _ HQ (Q_at B i) Hk ltac:(rewrite Hst; unfold PENDING; lia)) as (H1 & H2 & H3 & H4 & _ & _).
    unfold tagged_ok.
    split; [exact Hk|]. split; [unfold CMDS_MAX, OPS_MAX in *; lia|]. split; [exact Hst|].
    split; [exact H4|]. split; [exact H1|]. split; [exact H2 | exact H3].
  - rewrite tk_hq_length, tk_sq_length, (d1_queued _ _ HQ Hr). reflexivity.
Qed.

Lemma tt_bridge : forall ops B m, length B = WN -> agree_q ops B -> g_raw B = 0 ->
  tt_body B m = concat (map (cmd_body B) (tt_Ts B m)) /\
  tt_hd B m = fold_left Z.lor (map (Cmd_display B) (tt_Ts B m)) 0 /\
  length (tt_Ts B m) = length (tt_T B m).
Proof.
  intros ops B m HB HQ Hr. pose proof (pick_Forall2 _ m _ _ (ttq_sq_hq ops B HQ Hr)) as HF.
  unfold tt_body, tt_hd, tt_Ts, tt_T.
  split; [|split].
  - rewrite (ttq_Forall2_map_eq e_bytes (cmd_body B) (ttq_ent B) _ _ (ttq_ent_bytes B) HF). reflexivity.
  - rewrite (ttq_Forall2_map_eq e_disp (Cmd_display B) (ttq_ent B) _ _ (ttq_ent_disp B) HF). reflexivity.
  - symmetry. exact (ttq_Forall2_length _ _ _ HF).
Qed.

Lemma ttq_cmd_body_firstn : forall X k, Cmd_len X k <= 24 ->
  cmd_body X k = firstn (Z.to_nat (Cmd_len X k)) (Cmd_bytes X k).
Proof.
  intros X k H. pose proof (u_at_nonneg X (A_Cmd_len k) 1) as H0. change (0 <= Cmd_len X k) in H0.
  unfold cmd_body, Cmd_bytes. rewrite sub_firstn by lia. reflexivity.
Qed.

Lemma ttq_cmd_body_length : forall B k, length B = WN -> 0 <= k < Cmd_N ->
  length (cmd_body B k) = Z.to_nat (Cmd_len B k).
Proof.
  intros B k HB Hk. pose proof (u_at_bound B (A_Cmd_len k) 1) as Hb. change (Cmd_len B k < 256) in Hb.
  unfold cmd_body. apply w_length_sub. rewrite HB.
  unfold WN, W_LEN, A_Cmd_bytes, OFF_g_cmd, Cmd_N in *. lia.
Qed.

Lemma ttq_at8_app_l : forall l1 l2, (0 < length l1)%nat -> at8 (l1 ++ l2) 0 = at8 l1 0.
Proof. intros [|x l1] l2 H; cbn [length] in H; [lia | reflexivity]. Qed.

Lemma ttq_at8_firstn : forall l n, (0 < n)%nat -> at8 (firstn n l) 0 = at8 l 0.
Proof. intros [|x l] [|n] H; try lia; reflexivity. Qed.

Lemma tt_body_tag : forall ops B m, length B = WN -> agree_q ops B -> g_raw B = 0 -> tt_T B m <> [] ->
  at8 (tt_body B m) 0 = TAG.
Proof.
  intros ops B m HB HQ Hr Hne.
  destruct (tt_bridge ops B m HB HQ Hr) as (Hb & _ & Hl).
  destruct (tt_hq_ok ops B HB HQ Hr) as (_ & _ & Hok & _).
  assert (Hok' : Forall (tagged_ok B) (tt_Ts B m)) by (apply Forall_pick; exact Hok).
  rewrite Hb. clear Hb. revert Hl Hok'.
  destruct (tt_Ts B m) as [|k Ts]; intros Hl Hok'.
  - exfalso. apply Hne. destruct (tt_T B m) as [|e T]; [reflexivity|]. cbn [length] in Hl. discriminate Hl.
  - apply Forall_cons_iff in Hok' as [Hk _].
    destruct Hk as (Hk1 & Hk2 & _ & Hlen & Htag & _).
    assert (Hlb : length (cmd_body B k) = Z.to_nat (Cmd_len B k))
      by (apply ttq_cmd_body_length; [exact HB | unfold Cmd_N, CMDS_MAX in *; lia]).
    cbn [map concat].
    rewrite ttq_at8_app_l by (rewrite Hlb; lia).
    rewrite (ttq_cmd_body_firstn B k) by lia.
    rewrite ttq_at8_firstn by lia. exact Htag.
Qed.

(* ---------------------------------------------------------------- frames over the queue model *)

Lemma ttq_qframe_cmd : forall B B' k, length B = WN -> wframe R_nq B B' -> 0 <= k < Cmd_N ->
  Cmd_st B' k = Cmd_st B k /\ Cmd_len B' k = Cmd_len B k /\ Cmd_bytes B' k = Cmd_bytes B k /\
  Cmd_display B' k = Cmd_display B k /\ Cmd_key B' k = Cmd_key B k.
Proof.
  intros B B' k HB HF Hk. unfold Cmd_st, Cmd_len, Cmd_bytes, Cmd_display, Cmd_key.
  split; [tk_get HF|]. split; [tk_get HF|]. split; [tk_get HF|]. split; [tk_get HF | tk_get HF].
Qed.

Lemma ttq_qframe_q : forall B B' i, length B = WN -> wframe R_nq B B' -> 0 <= i < 1024 -> Q_at B' i = Q_at B i.
Proof. intros B B' i HB HF Hi. unfold Q_at. tk_get HF. Qed.

Lemma ttq_qframe_body : forall B B' k, length B = WN -> wframe R_nq B B' -> 0 <= k < Cmd_N ->
  cmd_body B' k = cmd_body B k.
Proof.
  intros B B' k HB HF Hk. destruct (ttq_qframe_cmd B B' k HB HF Hk) as (_ & E & _).
  pose proof (u_at_bound B (A_Cmd_len k) 1) as Hb. change (Cmd_len B k < 256) in Hb.
  unfold cmd_body. rewrite E. tk_get HF.
Qed.

Lemma tt_qmodel_frame : forall B B', length B = WN -> wframe R_nq B B' ->
  g_nq B' = g_nq B /\ (g_nq B <= CMDS_MAX -> hq B' = hq B) /\ g_ncmd B' = g_ncmd B /\
  (forall k, 0 <= k < Cmd_N -> Cmd_st B' k = Cmd_st B k /\ Cmd_len B' k = Cmd_len B k /\
     Cmd_bytes B' k = Cmd_bytes B k /\ Cmd_display B' k = Cmd_display B k /\ Cmd_key B' k = Cmd_key B k /\
     cmd_body B' k = cmd_body B k) /\
  (forall k, tagged_ok B k -> tagged_ok B' k).
Proof.
  intros B B' HB HF.
  assert (Hnq : g_nq B' = g_nq B) by (unfold g_nq; tk_get HF).
  assert (Hnc : g_ncmd B' = g_ncmd B) by (unfold g_ncmd; tk_get HF).
  assert (Hc : forall k, 0 <= k < Cmd_N -> Cmd_st B' k = Cmd_st B k /\ Cmd_len B' k = Cmd_len B k /\
     Cmd_bytes B' k = Cmd_bytes B k /\ Cmd_display B' k = Cmd_display B k /\ Cmd_key B' k = Cmd_key B k /\
     cmd_body B' k = cmd_body B k).
  { intros k Hk. destruct (ttq_qframe_cmd B B' k HB HF Hk) as (E1 & E2 & E3 & E4 & E5).
    split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
    exact (ttq_qframe_body B B' k HB HF Hk). }
  split; [exact Hnq|]. split; [|split; [exact Hnc | split; [exact Hc|]]].
  - intros Hle. unfold hq. rewrite Hnq. apply ttq_map_ext_in. intros i Hi. apply in_zseq in Hi.
    apply (ttq_qframe_q B B' i HB HF). unfold CMDS_MAX in Hle. lia.
  - intros k (Hk1 & Hk2 & Hk3 & Hk4 & Hk5 & Hk6 & Hk7).
    destruct (Hc k ltac:(unfold Cmd_N, CMDS_MAX in *; lia)) as (E1 & E2 & E3 & _ & _ & _).
    unfold tagged_ok. rewrite Hnc, E1, E2, E3.
    split; [exact Hk1|]. split; [exact Hk2|]. split; [exact Hk3|]. split; [exact Hk4|].
    split; [exact Hk5|]. split; [exact Hk6 | exact Hk7].
Qed.

(* the statement as first asked, with the queue bound it needs as a hypothesis (agree_q's d1_nq, tagged) *)
Lemma tt_qmodel_frame_nq : forall B B', length B = WN -> g_nq B <= QUEUE_MAX -> wframe R_nq B B' ->
  g_nq B' = g_nq B /\ hq B' = hq B /\ g_ncmd B' = g_ncmd B /\
  (forall k, 0 <= k < Cmd_N -> Cmd_st B' k = Cmd_st B k /\ Cmd_len B' k = Cmd_len B k /\
     Cmd_bytes B' k = Cmd_bytes B k /\ Cmd_display B' k = Cmd_display B k /\ Cmd_key B' k = Cmd_key B k /\
     cmd_body B' k = cmd_body B k) /\
  (forall k, tagged_ok B k -> tagged_ok B' k).
Proof.
  intros B B' HB Hq HF. destruct (tt_qmodel_frame B B' HB HF) as (H1 & H2 & H3 & H4 & H5).
  split; [exact H1|]. split; [apply H2; unfold CMDS_MAX, QUEUE_MAX in *; lia|].
  split; [exact H3|]. split; [exact H4 | exact H5].
Qed.

(* te_frame: g_raw, g_ncmd and every g_cmd field but st are outside R_tt *)
Lemma ttq_fr_raw : forall B Bf, length B = WN -> wframe R_tt B Bf -> g_raw Bf = g_raw B.
Proof. intros B Bf HB HF. unfold g_raw. tk_get HF. Qed.

Lemma ttq_fr_ncmd : forall B Bf, length B = WN -> wframe R_tt B Bf -> g_ncmd Bf = g_ncmd B.
Proof. intros B Bf HB HF. unfold g_ncmd. tk_get HF. Qed.

Lemma ttq_fr_cmd : forall B Bf k, length B = WN -> wframe R_tt B Bf -> 0 <= k < Cmd_N ->
  Cmd_len Bf k = Cmd_len B k /\ Cmd_bytes Bf k = Cmd_bytes B k /\ Cmd_display Bf k = Cmd_display B k /\
  Cmd_key Bf k = Cmd_key B k.
Proof.
  intros B Bf k HB HF Hk. unfold Cmd_len, Cmd_bytes, Cmd_display, Cmd_key.
  split; [tk_get HF|]. split; [tk_get HF|]. split; [tk_get HF | tk_get HF].
Qed.

(* ---------------------------------------------------------------- agree_q after the run *)

(* a bridge pair survives the run when its serial's state does *)
Lemma ttq_ent_transfer : forall ops B Bf e k, length B = WN -> agree_q ops B -> wframe R_tt B Bf ->
  Cmd_st Bf k = Cmd_st B k -> ttq_ent B e k -> ttq_ent Bf e k.
Proof.
  intros ops B Bf e k HB HQ HF Hst (Hby & Hlen & Hkey & Hdisp & Hbody & Hpe & Hk).
  pose proof (d3_ncmd _ _ HQ) as Hn1. pose proof (d3_ops _ _ HQ) as Hn2.
  destruct (d2_cmd _ _ HQ k Hk ltac:(rewrite Hpe; unfold PENDING; lia)) as (_ & _ & _ & Hl & _ & _).
  destruct (ttq_fr_cmd B Bf k HB HF ltac:(unfold Cmd_N, OPS_MAX in *; lia)) as (E1 & E2 & E3 & E4).
  pose proof (ttq_fr_ncmd B Bf HB HF) as En.
  unfold ttq_ent. rewrite (ttq_cmd_body_firstn Bf k) by (rewrite E1; lia).
  rewrite E1, E2, E3, E4, En, Hst.
  split; [exact Hby|]. split; [exact Hlen|]. split; [exact Hkey|]. split; [exact Hdisp|].
  split; [|split; [exact Hpe | exact Hk]].
  rewrite Hbody. apply ttq_cmd_body_firstn. lia.
Qed.

Lemma ttq_d2_transfer : forall ops B Bf k, length B = WN -> agree_q ops B -> wframe R_tt B Bf ->
  0 <= k < g_ncmd B -> Cmd_st B k <> 0 ->
  at8 (Cmd_bytes Bf k) 0 = TAG /\ at8 (Cmd_bytes Bf k) 1 = Z.land k 0x7f /\
  at8 (Cmd_bytes Bf k) 2 = Z.land (Z.shiftr k 7) 0x7f /\ 3 <= Cmd_len Bf k <= 24 /\
  bit01 (Cmd_display Bf k) /\ system_at (firstn (Z.to_nat (Cmd_len Bf k)) (Cmd_bytes Bf k)) = false.
Proof.
  intros ops B Bf k HB HQ HF Hk Hs.
  pose proof (d3_ncmd _ _ HQ) as Hn1. pose proof (d3_ops _ _ HQ) as Hn2.
  destruct (ttq_fr_cmd B Bf k HB HF ltac:(unfold Cmd_N, OPS_MAX in *; lia)) as (E1 & E2 & E3 & _).
  rewrite E1, E2, E3. exact (d2_cmd _ _ HQ k Hk Hs).
Qed.

(* D4 from the entries' facts (tt_sq_ok's), on any world *)
Lemma ttq_sq_d4 : forall X i, Forall ttq_ent_ok (sq X) -> 0 <= i < S_queued X ->
  1 <= S_queue_len X i <= 24 /\ system_at (firstn (Z.to_nat (S_queue_len X i)) (S_queue_bytes X i)) = false.
Proof.
  intros X i HF Hi.
  assert (Hin : In (sq_ent X i) (sq X)) by (apply tk_In_sq; exists i; split; [exact Hi | reflexivity]).
  destruct (ttq_Forall_In _ _ _ HF Hin) as (_ & Hl & Hbc).
  unfold e_bytes, e_len in Hbc. unfold e_len in Hl.
  rewrite (S_queue_len_ent X i) by lia.
  split; [exact Hl|].
  rewrite <- (ttq_firstn_sq_ent X i) by lia.
  rewrite body_check_spec in Hbc.
  destruct (system_at (firstn (Z.to_nat (cmd_len_of (sq_ent X i))) (sq_ent X i))); [discriminate Hbc | reflexivity].
Qed.

(* D1's entry from the bridge, on any world *)
Lemma ttq_ent_entry : forall X i, S_queued X = g_nq X -> Forall2 (ttq_ent X) (sq X) (hq X) -> 0 <= i < g_nq X ->
  0 <= Q_at X i < g_ncmd X /\ Cmd_st X (Q_at X i) = PENDING /\
  S_queue_bytes X i = Cmd_bytes X (Q_at X i) /\ S_queue_len X i = Cmd_len X (Q_at X i) /\
  S_queue_key X i = Cmd_key X (Q_at X i) /\ S_queue_display X i = Cmd_display X (Q_at X i).
Proof.
  intros X i Hq HF Hi.
  assert (Hn : (Z.to_nat i < length (sq X))%nat) by (rewrite tk_sq_length; lia).
  pose proof (ttq_Forall2_nth _ _ _ (Z.to_nat i) [] 0 HF Hn) as H.
  rewrite (tk_sq_nth X i [] ltac:(lia)), (tk_hq_nth X i 0 Hi) in H.
  destruct H as (Hby & Hlen & Hkey & Hdisp & _ & Hst & Hk).
  rewrite (S_queue_bytes_ent X i), (S_queue_len_ent X i), (S_queue_key_ent X i), (S_queue_display_ent X i) by lia.
  split; [exact Hk|]. split; [exact Hst|]. split; [exact Hby|]. split; [exact Hlen|].
  split; [exact Hkey | exact Hdisp].
Qed.

(* D1's no-duplicate clause from NoDup, on any world *)
Lemma ttq_hq_nodup_idx : forall X, List.NoDup (hq X) -> forall i j, 0 <= i < g_nq X -> 0 <= j < g_nq X ->
  Q_at X i = Q_at X j -> i = j.
Proof.
  intros X Hnd i j Hi Hj E.
  assert (Hl : length (hq X) = Z.to_nat (g_nq X)) by apply tk_hq_length.
  assert (Ez : Z.to_nat i = Z.to_nat j).
  { apply (ttq_NoDup_nth (hq X) 0); [exact Hnd | lia | lia |].
    exact (eq_trans (tk_hq_nth X i 0 Hi) (eq_trans E (eq_sym (tk_hq_nth X j 0 Hj)))). }
  lia.
Qed.

Lemma ttq_hq_in_idx : forall X k, In k (hq X) <-> exists i, 0 <= i < g_nq X /\ Q_at X i = k.
Proof.
  intros X k. split.
  - intros H. apply tk_In_hq in H as [i [Hi E]]. exists i. split; [exact Hi | symmetry; exact E].
  - intros [i [Hi E]]. apply tk_In_hq. exists i. split; [exact Hi | symmetry; exact E].
Qed.

(* tagged: the harness's queue after the run, as lists *)
Lemma ttq_after_tagged : forall ops B Bf m, length B = WN -> agree_q ops B -> length m = length (sq B) ->
  tt_end B Bf m -> g_raw B = 0 ->
  S_queued Bf = g_nq Bf /\ g_nq Bf <= QUEUE_MAX /\ List.NoDup (hq Bf) /\ Forall2 (ttq_ent Bf) (sq Bf) (hq Bf) /\
  (forall k, 0 <= k < g_ncmd B -> (Cmd_st Bf k = PENDING <-> In k (hq Bf))) /\
  (forall k, 0 <= k < g_ncmd B -> Cmd_st Bf k <> 0 -> Cmd_st B k <> 0).
Proof.
  intros ops B Bf m HB HQ Hm HE Hr.
  pose proof (te_frame _ _ _ HE) as HF.
  destruct (tt_hq_ok ops B HB HQ Hr) as (Hnq & Hnd & _ & Hlq).
  pose proof (ttq_sq_hq ops B HQ Hr) as H2.
  pose proof (d3_ncmd _ _ HQ) as Hn1. pose proof (d3_ops _ _ HQ) as Hn2.
  assert (HN : g_ncmd B <= Cmd_N) by (unfold Cmd_N, OPS_MAX in *; lia).
  assert (Hmq : length m = length (hq B)) by (rewrite Hlq; exact Hm).
  (* B's PENDING serials are exactly hq B *)
  assert (Hpend : forall k, 0 <= k < g_ncmd B -> (Cmd_st B k = PENDING <-> In k (hq B))).
  { intros k Hk. pose proof (d1_pending _ _ HQ Hr k Hk) as P. split.
    - intros Hs. apply P in Hs as [i [Hi E]]. apply tk_In_hq. exists i. split; [exact Hi | symmetry; exact E].
    - intros Hin. apply tk_In_hq in Hin as [i [Hi E]]. apply P. exists i. split; [exact Hi | symmetry; exact E]. }
  assert (Hkept : forall k, In k (unpick m (hq B)) -> ~ In k (tt_Ts B m))
    by (intros k Hk; exact (ttq_pick_unpick_disj m (hq B) k Hnd Hk)).
  assert (HU : Forall2 (ttq_ent B) (unpick m (sq B)) (unpick m (hq B))) by (apply unpick_Forall2; exact H2).
  assert (HUf : Forall2 (ttq_ent Bf) (unpick m (sq B)) (unpick m (hq B))).
  { apply (ttq_Forall2_impl_in (ttq_ent B)); [|exact HU].
    intros e k Hin He. apply (ttq_ent_transfer ops B Bf e k HB HQ HF); [|exact He].
    destruct He as (_ & _ & _ & _ & _ & _ & Hk).
    exact (te_st_out _ _ _ HE Hr k ltac:(lia) (Hkept k Hin)). }
  split; [|split; [|split; [|split; [|split]]]].
  - rewrite (te_queued _ _ _ HE), (te_nq _ _ _ HE Hr), (ttq_Forall2_length _ _ _ HU). reflexivity.
  - rewrite (te_nq _ _ _ HE Hr). pose proof (ttq_length_pick (map negb m) (hq B)) as L.
    rewrite tk_hq_length in L. unfold unpick. unfold QUEUE_MAX in *. lia.
  - rewrite (te_hq _ _ _ HE Hr). unfold unpick. apply ttq_NoDup_pick. exact Hnd.
  - rewrite (te_sq _ _ _ HE), (te_hq _ _ _ HE Hr). exact HUf.
  - intros k Hk. rewrite (te_hq _ _ _ HE Hr). split.
    + intros Hs. destruct (List.in_dec Z.eq_dec k (tt_Ts B m)) as [Hin|Hout].
      * exfalso. rewrite (te_st_in _ _ _ HE Hr k Hin) in Hs. unfold SENT, PENDING in Hs. lia.
      * rewrite (te_st_out _ _ _ HE Hr k ltac:(lia) Hout) in Hs. apply (Hpend k Hk) in Hs.
        destruct (ttq_in_pick_or_unpick m (hq B) k Hmq Hs) as [Hp|Hu]; [exfalso; exact (Hout Hp) | exact Hu].
    + intros Hu. rewrite (te_st_out _ _ _ HE Hr k ltac:(lia) (Hkept k Hu)).
      apply (Hpend k Hk). exact (in_unpick m (hq B) k Hu).
  - intros k Hk Hs. destruct (List.in_dec Z.eq_dec k (tt_Ts B m)) as [Hin|Hout].
    + assert (Hq : In k (hq B)) by exact (in_pick m (hq B) k Hin).
      apply (Hpend k Hk) in Hq. rewrite Hq. unfold PENDING. lia.
    + rewrite <- (te_st_out _ _ _ HE Hr k ltac:(lia) Hout). exact Hs.
Qed.

Lemma tt_agree_q : forall ops B Bf m, length B = WN -> agree_q ops B -> length m = length (sq B) ->
  tt_end B Bf m -> agree_q ops Bf.
Proof.
  intros ops B Bf m HB HQ Hm HE.
  pose proof (te_frame _ _ _ HE) as HF.
  pose proof (ttq_fr_raw B Bf HB HF) as Er.
  pose proof (ttq_fr_ncmd B Bf HB HF) as En.
  pose proof (d3_ncmd _ _ HQ) as Hn1. pose proof (d3_ops _ _ HQ) as Hn2.
  assert (HN : g_ncmd B <= Cmd_N) by (unfold Cmd_N, OPS_MAX in *; lia).
  (* a command of Bf not refused was not refused in B: tagged, a taken serial was PENDING; raw, st untouched *)
  assert (Hst0 : forall k, 0 <= k < g_ncmd B -> Cmd_st Bf k <> 0 -> Cmd_st B k <> 0).
  { destruct (Z.eqb_spec (g_raw B) 0) as [Hr|Hr].
    - destruct (ttq_after_tagged ops B Bf m HB HQ Hm HE Hr) as (_ & _ & _ & _ & _ & H6). exact H6.
    - intros k Hk Hs. destruct (tt_qmodel_frame B Bf HB (te_raw _ _ _ HE Hr)) as (_ & _ & _ & Hc & _).
      destruct (Hc k ltac:(lia)) as (E & _). rewrite <- E. exact Hs. }
  (* every entry left is one of B's *)
  assert (Hok : Forall ttq_ent_ok (sq Bf)).
  { rewrite (te_sq _ _ _ HE). unfold unpick. apply Forall_pick. exact (tt_sq_ok ops B HB HQ). }
  assert (HqB : 0 <= S_queued B <= 512) by exact (tt_queued_le ops B HQ).
  assert (HqBf : S_queued Bf <= S_queued B).
  { rewrite (te_queued _ _ _ HE). pose proof (ttq_length_pick (map negb m) (sq B)) as L.
    rewrite tk_sq_length in L. unfold unpick. lia. }
  assert (Hd1 : g_raw Bf = 0 -> S_queued Bf = g_nq Bf /\ g_nq Bf <= QUEUE_MAX /\ List.NoDup (hq Bf) /\
     Forall2 (ttq_ent Bf) (sq Bf) (hq Bf) /\ (forall k, 0 <= k < g_ncmd B -> (Cmd_st Bf k = PENDING <-> In k (hq Bf)))).
  { intros Hr'. assert (Hr : g_raw B = 0) by (rewrite <- Er; exact Hr').
    destruct (ttq_after_tagged ops B Bf m HB HQ Hm HE Hr) as (H1 & H2 & H3 & H4 & H5 & _).
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4 | exact H5]. }
  constructor.
  - intros Hr. exact (proj1 (Hd1 Hr)).
  - intros Hr. exact (proj1 (proj2 (Hd1 Hr))).
  - intros Hr i Hi. destruct (Hd1 Hr) as (Hq & _ & _ & H2 & _). exact (ttq_ent_entry Bf i Hq H2 Hi).
  - intros Hr. destruct (Hd1 Hr) as (_ & _ & Hnd & _ & _). exact (ttq_hq_nodup_idx Bf Hnd).
  - intros Hr k Hk. destruct (Hd1 Hr) as (_ & _ & _ & _ & Hp).
    exact (iff_trans (Hp k ltac:(lia)) (ttq_hq_in_idx Bf k)).
  - intros k Hk Hs. exact (ttq_d2_transfer ops B Bf k HB HQ HF ltac:(lia) (Hst0 k ltac:(lia) Hs)).
  - rewrite En. exact Hn1.
  - exact Hn2.
  - intros _. unfold QUEUE_MAX. lia.
  - intros _ i Hi. exact (ttq_sq_d4 Bf i Hok Hi).
Qed.
