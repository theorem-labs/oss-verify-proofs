(* The room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record) for check_no_loss's _x walk (W_check_no_loss.v): the count and budget
   bookkeeping its loop carries.  Pure lemmas over the plain model, no walk.
   - cnl_spec_x's count premise is cnt_ok_pk RP (cnl_pk E H) (W_contract_x.v:308, :1361): the live counts plus the peak
     of the request trace cnl_tr E H (HarnessTr.check_no_loss_tr over the held list's shape and the expected records)
     plus 2.  The loop keeps it for the records still owed (cnl_cnt at the loop head, cnl_cntm after gesture_model):
     a held list's live count is cnl_pot of its capacity and texts (cnl_acnt_blks); one gesture_model call moves it by
     the net count of its trace (cnl_gm_step, at the shape gesture_model_sh), the free of the consumed line by its
     rec_drop_tr's (cnl_cnt_free); a step is allowed because the peak of a ++ b is at least net a + peak b
     (cnl_cnt_step).  gesture_model's own count premise (gm_pk <= 2) and free's (cnt_ok) follow from the invariant
     because a peak is nonnegative (cnl_cnt_gm_pre, cnl_cntm_free_pre).
   - The room budget rp_RM RP S (Z.to_nat (cnl_cost MT_rk E H) + kr) splits per record into gesture_model's charge, one
     free and the rest (cnl_rk_step). *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel RelayRunT ListTr HarnessTr RelayRunF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_journal_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyCnt ReplyTrPeakW.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Open Scope Z_scope.

(* ------------------------------------------------------------------ the live count of a held list *)
(* the count of a held list's text blocks (one per text, its length + 1) and of its vector (AREC * cap, none at cap 0) *)
Definition cnl_tsum (P : Z -> bool) (T : list (list Z)) : Z :=
  fold_right (fun t a => ReplyCnt.zb (P (Z.of_nat (length t) + 1)) + a) 0 T.
Definition cnl_pot (P : Z -> bool) (cap : Z) (T : list (list Z)) : Z :=
  (if cap =? 0 then 0 else ReplyCnt.zb (P (AREC * cap))) + cnl_tsum P T.
(* the net count change of a request trace (ReplyTrPeakW.v's at the weight zb (P n)) *)
Definition cnl_net {X : Type} (P : Z -> bool) (tr : list (RelayRunT.rev X)) : Z :=
  ReplyTrPeakW.tr_net_w (fun n => ReplyCnt.zb (P n)) tr.

Lemma cnl_peak_app : forall (X : Type) (P : Z -> bool) (a b : list (RelayRunT.rev X)),
  ReplyCnt.tr_peakP P (a ++ b) = Z.max (ReplyCnt.tr_peakP P a) (cnl_net P a + ReplyCnt.tr_peakP P b).
Proof. intros X P a b. unfold cnl_net. rewrite !ReplyCnt.tr_peakP_w. apply ReplyTrPeakW.tr_peak_w_app. Qed.

Lemma cn_zb_nat : forall b : bool, Z.of_nat (if b then 1%nat else 0%nat) = ReplyCnt.zb b.
Proof. intros []; reflexivity. Qed.

Lemma cnl_acnt_recs : forall P (rs : list (Z * list byte)),
  Z.of_nat (ReplyCnt.acnt P (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) rs)) =
  cnl_tsum P (map (fun r => bzs (snd r)) rs).
Proof.
intros P rs. unfold cnl_tsum. induction rs as [|r rs IH]; [reflexivity|].
cbn [map fold_right]. rewrite acnt_cons, Nat2Z.inj_add, IH. cbn [snd]. rewrite cn_zb_nat. unfold bzs. rewrite length_map.
reflexivity.
Qed.

Lemma cnl_acnt_blks : forall P (l : hlist), Z.of_nat (ReplyCnt.acnt P (list_blks l)) = cnl_pot P (hl_cap l) (texts l).
Proof.
intros P l. unfold list_blks, cnl_pot, texts. rewrite ReplyCnt.acnt_app, Nat2Z.inj_add, cnl_acnt_recs.
destruct (hl_cap l =? 0); [reflexivity|].
rewrite acnt_cons, acnt_nil, Nat.add_0_r. cbn [snd]. rewrite cn_zb_nat. reflexivity.
Qed.

(* ------------------------------------------------------------------ the model's list facts *)
Lemma cn_leqb : forall a b, RelayModel.list_eqb a b = true <-> a = b.
Proof. intros a b. unfold RelayModel.list_eqb. destruct (list_eq_dec Z.eq_dec a b); split; congruence. Qed.

Lemma cn_find_key_some : forall x T i, HarnessTr.find_key x T = Some i -> (i < length T)%nat /\ nth i T [] = x.
Proof.
intros x T. induction T as [|t T IH]; intros i H; cbn [HarnessTr.find_key] in H; [discriminate|].
destruct (RelayModel.list_eqb x t) eqn:E.
- injection H as <-. apply cn_leqb in E. subst t. split; [cbn [length]; lia | reflexivity].
- destruct (HarnessTr.find_key x T) as [i'|] eqn:E'; cbn [option_map] in H; [|discriminate]. injection H as <-.
  destruct (IH i' eq_refl) as (Hl & Hn). split; [cbn [length]; lia | exact Hn].
Qed.

Lemma cn_find_key_none : forall x T, HarnessTr.find_key x T = None -> ~ In x T.
Proof.
intros x T. induction T as [|t T IH]; intros H Hin; [exact Hin|]. cbn [HarnessTr.find_key] in H.
destruct (RelayModel.list_eqb x t) eqn:E; [discriminate|].
destruct (HarnessTr.find_key x T) eqn:E'; cbn [option_map] in H; [discriminate|].
destruct Hin as [Ht | Hin]; [subst t; rewrite (proj2 (cn_leqb x x) eq_refl) in E; discriminate | exact (IH eq_refl Hin)].
Qed.

Lemma cn_filter_notin : forall x T, ~ In x T -> List.filter (fun y => negb (RelayModel.list_eqb x y)) T = T.
Proof.
intros x T. induction T as [|t T IH]; intros Hn; [reflexivity|]. cbn [List.filter].
destruct (RelayModel.list_eqb x t) eqn:E.
- exfalso. apply cn_leqb in E. apply Hn. left. symmetry. exact E.
- cbn [negb]. rewrite IH; [reflexivity|]. intros Hin. apply Hn. right. exact Hin.
Qed.

Lemma cn_filter_at : forall T i x, List.NoDup T -> (i < length T)%nat -> nth i T [] = x ->
  List.filter (fun y => negb (RelayModel.list_eqb x y)) T = firstn i T ++ skipn (S i) T.
Proof.
intros T. induction T as [|t T IH]; intros i x HND Hi Hx; [cbn [length] in Hi; lia|].
apply List.NoDup_cons_iff in HND as [Ht HND]. cbn [List.filter].
destruct i as [|i]; cbn [nth] in Hx.
- subst t. rewrite (proj2 (cn_leqb x x) eq_refl). cbn [negb firstn skipn app]. apply cn_filter_notin. exact Ht.
- assert (Hxt : RelayModel.list_eqb x t = false).
  { destruct (RelayModel.list_eqb x t) eqn:E; [|reflexivity]. apply cn_leqb in E. subst t. exfalso. apply Ht.
    rewrite <- Hx. apply nth_In. cbn [length] in Hi. lia. }
  rewrite Hxt. cbn [negb firstn skipn app]. f_equal. apply IH; [exact HND | cbn [length] in Hi; lia | exact Hx].
Qed.

Lemma cn_filter_len : forall x T, (length (List.filter (fun y => negb (RelayModel.list_eqb x y)) T) <= length T)%nat.
Proof. intros x T. induction T as [|y T IH]; cbn [List.filter length]; [lia|]. destruct (negb (RelayModel.list_eqb x y)); cbn [length]; lia. Qed.

Lemma cn_tsum_drop : forall P T i, (i < length T)%nat ->
  cnl_tsum P (firstn i T ++ skipn (S i) T) = cnl_tsum P T - ReplyCnt.zb (P (Z.of_nat (length (nth i T [])) + 1)).
Proof.
intros P T. unfold cnl_tsum. induction T as [|t T IH]; intros i Hi; [cbn [length] in Hi; lia|].
destruct i as [|i]; cbn [firstn skipn app nth fold_right]; [change (skipn 0 T) with T; lia|].
rewrite IH by (cbn [length] in Hi; lia). lia.
Qed.

Lemma cn_tsum_app1 : forall P T x, cnl_tsum P (T ++ [x]) = cnl_tsum P T + ReplyCnt.zb (P (Z.of_nat (length x) + 1)).
Proof.
intros P T x. unfold cnl_tsum. induction T as [|t T IH]; cbn [app fold_right]; [lia|]. rewrite IH. lia.
Qed.

Lemma cn_map_firstn : forall {A C : Type} (f : A -> C) n (l : list A), map f (firstn n l) = firstn n (map f l).
Proof. intros A C f n. induction n as [|n IH]; intros [|a l]; cbn [firstn map]; [reflexivity..|]. rewrite IH. reflexivity. Qed.
Lemma cn_map_skipn : forall {A C : Type} (f : A -> C) n (l : list A), map f (skipn n l) = skipn n (map f l).
Proof. intros A C f n. induction n as [|n IH]; intros [|a l]; cbn [skipn map]; [reflexivity..|]. apply IH. Qed.

(* ------------------------------------------------------------------ one gesture_model call on the trace's shape *)
(* gesture_model's trace step: the shape after it has the model's texts upd T ln and the capacity capstep (the post's
   hl_cap), and the live count moves by the trace's net count *)
Lemma cnl_gm_step : forall P (j : nat) (s : ListTr.shl) (ln : list Z), List.NoDup (ListTr.sh_keys s) ->
  ListTr.sh_keys (HarnessTr.gesture_model_sh j s ln) = RelayModel.upd (ListTr.sh_keys s) ln /\
  ListTr.sh_cap (HarnessTr.gesture_model_sh j s ln) = capstep (ListTr.sh_keys s) ln (ListTr.sh_cap s) /\
  cnl_pot P (capstep (ListTr.sh_keys s) ln (ListTr.sh_cap s)) (RelayModel.upd (ListTr.sh_keys s) ln) =
  cnl_pot P (ListTr.sh_cap s) (ListTr.sh_keys s) + cnl_net P (HarnessTr.gesture_model_tr s ln).
Proof.
intros P j s ln HND.
assert (Hn : ListTr.sh_n s = Z.of_nat (length (ListTr.sh_keys s)))
  by (unfold ListTr.sh_n, ListTr.sh_keys; rewrite length_map; reflexivity).
assert (Hnil : forall (X : Type) P0, cnl_net P0 (@nil (RelayRunT.rev X)) = 0) by reflexivity.
unfold capstep. unfold HarnessTr.gesture_model_sh, HarnessTr.gesture_model_tr, RelayModel.upd.
destruct (RelayModel.gesture ln) as [[[|] x]|]; cbv beta iota.
- (* a begin line *)
  destruct (existsb (RelayModel.list_eqb x) (ListTr.sh_keys s)) eqn:Ex; cbv beta iota.
  + rewrite Nat.ltb_irrefl. split; [reflexivity|]. split; [reflexivity|]. rewrite Hnil. lia.
  + assert (Hlt : Nat.ltb (length (ListTr.sh_keys s)) (length (ListTr.sh_keys s ++ [x])) = true)
      by (apply Nat.ltb_lt; rewrite length_app; cbn [length]; lia).
    rewrite Hlt. unfold ListTr.list_push_sh, ListTr.list_push_tr, ListTr.list_grow_tr. rewrite Hn.
    set (c := ListTr.sh_cap s) in *. set (n := Z.of_nat (length (ListTr.sh_keys s))) in *.
    assert (Hk : forall v cap' t, ListTr.sh_keys (ListTr.SHL v cap' (ListTr.sh_recs s ++ [(t, x)])) = ListTr.sh_keys s ++ [x])
      by (intros v cap' t; unfold ListTr.sh_keys; cbn [ListTr.sh_recs]; rewrite map_app; reflexivity).
    destruct (n =? c) eqn:Ec; cbv beta iota.
    * apply Z.eqb_eq in Ec. rewrite Hk. cbn [ListTr.sh_cap]. split; [reflexivity|]. split; [reflexivity|].
      unfold cnl_pot. rewrite cn_tsum_app1. unfold grow_cap. rewrite Ec, Z.eqb_refl.
      destruct (c =? 0) eqn:E0; cbv beta iota.
      -- assert (E8 : (8 =? 0) = false) by reflexivity. rewrite E8.
         replace (AREC * 8) with 128 by (unfold AREC; lia).
         unfold cnl_net, ReplyTrPeakW.tr_net_w. cbn [app fold_right]. lia.
      -- apply Z.eqb_neq in E0. assert (E2 : (2 * c =? 0) = false) by (apply Z.eqb_neq; lia). rewrite E2.
         replace (AREC * (2 * c)) with (32 * c) by (unfold AREC; lia).
         replace (AREC * c) with (16 * c) by (unfold AREC; lia).
         unfold cnl_net, ReplyTrPeakW.tr_net_w. cbn [app fold_right]. lia.
    * apply Z.eqb_neq in Ec. rewrite Hk. cbn [ListTr.sh_cap]. split; [reflexivity|].
      assert (Eg : grow_cap n c = c) by (unfold grow_cap; rewrite (proj2 (Z.eqb_neq n c) Ec); reflexivity).
      rewrite Eg. split; [reflexivity|].
      unfold cnl_pot. rewrite cn_tsum_app1. unfold cnl_net, ReplyTrPeakW.tr_net_w. cbn [app fold_right]. lia.
- (* an end line *)
  assert (Hlt : Nat.ltb (length (ListTr.sh_keys s))
    (length (List.filter (fun y => negb (RelayModel.list_eqb x y)) (ListTr.sh_keys s))) = false)
    by (apply Nat.ltb_ge; apply cn_filter_len).
  rewrite Hlt.
  destruct (HarnessTr.find_key x (ListTr.sh_keys s)) as [i|] eqn:Ef; cbv beta iota.
  + destruct (cn_find_key_some _ _ _ Ef) as (Hi & Hx).
    rewrite (cn_filter_at (ListTr.sh_keys s) i x HND Hi Hx).
    assert (Hk : ListTr.sh_keys (ListTr.list_drop_sh s i) =
      firstn i (ListTr.sh_keys s) ++ skipn (S i) (ListTr.sh_keys s)).
    { unfold ListTr.list_drop_sh, ListTr.sh_keys. cbn [ListTr.sh_recs]. rewrite map_app, cn_map_firstn, cn_map_skipn.
      reflexivity. }
    rewrite Hk. split; [reflexivity|]. split; [reflexivity|].
    unfold cnl_pot. rewrite cn_tsum_drop by exact Hi.
    unfold cnl_net, ReplyTrPeakW.tr_net_w, ListTr.list_drop_tr, ListTr.rec_drop_tr, ListTr.rec_len. cbn [fold_right].
    assert (Esn : forall d, snd (nth i (ListTr.sh_recs s) d) = nth i (ListTr.sh_keys s) (snd d)).
    { intros d. unfold ListTr.sh_keys. rewrite map_nth. reflexivity. }
    rewrite Esn. cbn [snd]. lia.
  + rewrite (cn_filter_notin x (ListTr.sh_keys s) (cn_find_key_none x _ Ef)).
    split; [reflexivity|]. split; [reflexivity|]. rewrite Hnil. lia.
- (* no gesture *)
  rewrite Nat.ltb_irrefl. split; [reflexivity|]. split; [reflexivity|]. rewrite Hnil. lia.
Qed.

(* ------------------------------------------------------------------ the loop's count invariant *)
Section cnt.
Variable RP : roomp.
(* the records rs still owed, with the held list H1 at the loop head: some shape of the trace (its names play no
   part in the sizes) has H1's texts and capacity, and the live counts plus the peak of the trace still owed plus 2
   are under the bounds *)
Definition cnl_cnt (rs : list (Z * list byte)) (H1 : hlist) (l : list (Z * Z)) : Prop :=
  exists (jt : nat) (s : ListTr.shl), ListTr.sh_keys s = texts H1 /\ ListTr.sh_cap s = hl_cap H1 /\
  cnt_ok_pk RP (fun P => (Z.to_nat (ReplyCnt.tr_peakP P
    (HarnessTr.check_no_loss_tr jt s (map (ListTr.shr (fun _ => RelayRunF.adr0)) rs))) + 2)%nat) l.
(* after gesture_model returned on r: the free of r's line is still owed before the rest *)
Definition cnl_cntm (r : Z * list byte) (rs : list (Z * list byte)) (H1 : hlist) (l : list (Z * Z)) : Prop :=
  exists (jt : nat) (s : ListTr.shl), ListTr.sh_keys s = texts H1 /\ ListTr.sh_cap s = hl_cap H1 /\
  cnt_ok_pk RP (fun P => (Z.to_nat (ReplyCnt.tr_peakP P
    (ListTr.rec_drop_tr (ListTr.shr (fun _ => RelayRunF.adr0) r) ++
     HarnessTr.check_no_loss_tr jt s (map (ListTr.shr (fun _ => RelayRunF.adr0)) rs))) + 2)%nat) l.

(* a step of the trace: the counts moved by the step's net count, the peak of the rest is what is left owed *)
Lemma cnl_cnt_step : forall (l l' : list (Z * Z)) {X : Type} (a b : list (RelayRunT.rev X)) (c : nat),
  (forall P, Z.of_nat (ReplyCnt.acnt P l') = Z.of_nat (ReplyCnt.acnt P l) + cnl_net P a) ->
  cnt_ok_pk RP (fun P => (Z.to_nat (ReplyCnt.tr_peakP P (a ++ b)) + c)%nat) l ->
  cnt_ok_pk RP (fun P => (Z.to_nat (ReplyCnt.tr_peakP P b) + c)%nat) l'.
Proof.
intros l l' X a b c Hn Hc. revert Hc. apply cnt_ok_pk_mono. intros P. cbv beta. specialize (Hn P).
rewrite cnl_peak_app. pose proof (ReplyCnt.tr_peakP_nonneg X P a). pose proof (ReplyCnt.tr_peakP_nonneg X P b). lia.
Qed.

(* the entry: cnl_spec_x's count premise is the invariant at the trace's own shape sh_of *)
Lemma cnl_cnt_entry : forall (E H : hlist) l, cnt_ok_pk RP (cnl_pk E H) l -> cnl_cnt (hl_recs E) H l.
Proof.
intros E H l Hc. exists 0%nat, (ListTr.sh_of (fun _ => RelayRunF.adr0) H).
split; [unfold ListTr.sh_keys, ListTr.sh_of, texts; cbn [ListTr.sh_recs]; rewrite map_map; reflexivity|].
split; [reflexivity | exact Hc].
Qed.

(* gesture_model's count premise (its peak gm_pk is at most 2) *)
Lemma cnl_cnt_gm_pre : forall r rs H1 l, cnl_cnt (r :: rs) H1 l -> cnt_ok_pk RP (gm_pk H1) l.
Proof.
intros r rs H1 l (jt & s & _ & _ & Hc). revert Hc. apply cnt_ok_pk_mono.
intros P. cbv beta. unfold gm_pk.
pose proof (ReplyCnt.tr_peakP_nonneg _ P
  (HarnessTr.check_no_loss_tr jt s (map (ListTr.shr (fun _ => RelayRunF.adr0)) (r :: rs)))).
destruct (P (lp_vbytes H1) && lp_grow H1); lia.
Qed.

(* gesture_model's return: its post's texts and capacity, and its blocks in place of the held list's *)
Lemma cnl_cnt_gm_post : forall r rs (H1 H2 : hlist) l l' rest, List.NoDup (texts H1) ->
  texts H2 = RelayModel.upd (texts H1) (bzs (snd r)) -> hl_cap H2 = capstep (texts H1) (bzs (snd r)) (hl_cap H1) ->
  Permutation l (list_blks H1 ++ rest) -> Permutation l' (list_blks H2 ++ rest) ->
  cnl_cnt (r :: rs) H1 l -> cnl_cntm r rs H2 l'.
Proof.
intros r rs H1 H2 l l' rest HND HT HC Hp Hp' (jt & s & Hk & Hcap & Hc).
cbn [map HarnessTr.check_no_loss_tr] in Hc.
change (snd (ListTr.shr (fun _ => RelayRunF.adr0) r)) with (bzs (snd r)) in Hc.
rewrite <- Hk in HND.
destruct (cnl_gm_step (fun _ => false) jt s (bzs (snd r)) HND) as (Hk2 & Hc2 & _).
eexists. exists (HarnessTr.gesture_model_sh jt s (bzs (snd r))).
split; [rewrite Hk2, Hk, HT; reflexivity|].
split; [rewrite Hc2, Hk, Hcap, HC; reflexivity|].
apply (cnl_cnt_step l l' (HarnessTr.gesture_model_tr s (bzs (snd r)))); [|exact Hc].
intros P. destruct (cnl_gm_step P jt s (bzs (snd r)) HND) as (_ & _ & Hpot).
rewrite (ReplyCnt.acnt_perm P _ _ Hp), (ReplyCnt.acnt_perm P _ _ Hp'), !ReplyCnt.acnt_app, !Nat2Z.inj_add,
  !cnl_acnt_blks.
rewrite HT, HC, <- Hk, <- Hcap. lia.
Qed.

(* free's count premise after gesture_model *)
Lemma cnl_cntm_free_pre : forall r rs H1 l, cnl_cntm r rs H1 l -> cnt_ok RP l.
Proof.
intros r rs H1 l (jt & s & _ & _ & Hc). unfold cnt_ok. revert Hc. apply cnt_ok_pk_mono. intros P. cbv beta. lia.
Qed.

(* the free of r's line (its block, length + 1) *)
Lemma cnl_cnt_free : forall r rs H1 (la lb : list (Z * Z)) pa,
  cnl_cntm r rs H1 (la ++ (pa, Z.of_nat (length (snd r)) + 1) :: lb) -> cnl_cnt rs H1 (la ++ lb).
Proof.
intros r rs H1 la lb pa (jt & s & Hk & Hcap & Hc). exists jt, s. split; [exact Hk|]. split; [exact Hcap|].
apply (cnl_cnt_step (la ++ (pa, Z.of_nat (length (snd r)) + 1) :: lb) (la ++ lb)
  (ListTr.rec_drop_tr (ListTr.shr (fun _ => RelayRunF.adr0) r))); [|exact Hc].
intros P. rewrite !ReplyCnt.acnt_app, acnt_cons, !Nat2Z.inj_add. cbn [snd]. rewrite cn_zb_nat.
unfold cnl_net, ReplyTrPeakW.tr_net_w, ListTr.rec_drop_tr, ListTr.rec_len, ListTr.shr. cbn [fold_right snd].
unfold bzs. rewrite length_map. lia.
Qed.
End cnt.

(* ------------------------------------------------------------------ the room budget per record *)
(* gesture_model's MT_rk charge (gmc counts list_push's calls on a begin of a new key, one free on an end of a held
   key, none otherwise) is never negative *)
Lemma cnl_rk_gmc_nonneg : forall T cap ln, 0 <= gmc MT_rk T cap ln.
Proof.
intros T cap ln. unfold gmc. cbn [mo_malloc mo_free MT_rk].
destruct (RelayModel.gesture (bzs ln)) as [[[|] x]|]; cbv beta iota;
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia.
Qed.
Lemma cnl_rk_go_nonneg : forall rs T cap, 0 <= cnl_go MT_rk T cap rs.
Proof.
induction rs as [|r rs IH]; intros T cap; cbn [cnl_go]; [lia|]. change (mo_free MT_rk) with 1.
pose proof (cnl_rk_gmc_nonneg T cap (snd r)).
pose proof (IH (RelayModel.upd T (bzs (snd r))) (capstep T (bzs (snd r)) cap)).
lia.
Qed.
Lemma cnl_rk_gm : forall (H : hlist) ln, gm_cost MT_rk H ln = gmc MT_rk (texts H) (hl_cap H) ln.
Proof.
intros H ln. unfold gm_cost, lp_cost, gmc, lp_grow, lp_vbytes.
replace (Z.of_nat (length (texts H))) with (hl_n H) by (unfold texts, hl_n; rewrite length_map; reflexivity).
reflexivity.
Qed.
(* gesture_model's charge (MT_rk counts its calls), then the line's free, then the rest *)
Lemma cnl_rk_step : forall (H : hlist) r rs kr,
  (Z.to_nat (cnl_go MT_rk (texts H) (hl_cap H) (r :: rs)) + kr)%nat =
  (Z.to_nat (gm_cost MT_rk H (snd r)) +
   S (Z.to_nat (cnl_go MT_rk (RelayModel.upd (texts H) (bzs (snd r))) (capstep (texts H) (bzs (snd r)) (hl_cap H)) rs)
      + kr))%nat.
Proof.
intros H r rs kr. rewrite cnl_rk_gm. cbn [cnl_go]. change (mo_free MT_rk) with 1.
pose proof (cnl_rk_gmc_nonneg (texts H) (hl_cap H) (snd r)).
pose proof (cnl_rk_go_nonneg rs (RelayModel.upd (texts H) (bzs (snd r))) (capstep (texts H) (bzs (snd r)) (hl_cap H))).
lia.
Qed.
Lemma cnl_rm_cast : forall RP0 S0 (m m' : nat), rp_RM RP0 S0 m -> m = m' -> rp_RM RP0 S0 m'.
Proof. intros RP0 S0 m m' H <-. exact H. Qed.

(* ------------------------------------------------------------------ the held list's capacity over the records *)
(* the capacity after the expected records is never below the start one (cnl_post_x's hl_cap H <= hl_cap H'):
   capstep grows a capacity only when it equals the held count, which is nonnegative *)
Lemma cnl_cap_ge : forall rs T cap, cap <= cnl_cap T cap rs.
Proof.
induction rs as [|r rs IH]; intros T cap; cbn [cnl_cap]; [lia|].
assert (Hs : cap <= capstep T (bzs (snd r)) cap).
{ unfold capstep. destruct (Nat.ltb (length T) (length (RelayModel.upd T (bzs (snd r))))); [|lia].
  unfold grow_cap. destruct (Z.of_nat (length T) =? cap) eqn:E; [|lia]. apply Z.eqb_eq in E.
  destruct (cap =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia | lia]. }
pose proof (IH (RelayModel.upd T (bzs (snd r))) (capstep T (bzs (snd r)) cap)). lia.
Qed.
