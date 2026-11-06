From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack
  AllocPackRoom AllocBound AllocGS FrameSlotP AllocPack3 AllocPack3Room ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import StatementKept SlotInv SlotSteps SlotRes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import SlotParse SlotCaps3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotRI3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayRunT RelayRunF ListTr HarnessRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import HarnessTr relay_add_b_c op_add_c send_line_b_c gesture_end_b_c gestures_end_b_c relay_finish_b_c SlotMove SlotNcMove3 SlotRun3 SlotOp7R3 SlotResR3 SlotResReply.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Inductive fch (M : Z) : Z -> adrF -> nat -> trF -> Z -> adrF -> Prop :=
| fch_nil cap a j : fch M cap a j [] cap a
| fch_grow cap a j c tr cap' a' : 0 <= cap < c -> c <= M -> fch M c (Ret j) (S j) tr cap' a' ->
    fch M cap a j ((if cap =? 0 then RMalloc c else RRealloc cap c a) :: tr) cap' a'
| fch_free cap a j n x tr cap' a' : 0 <= n -> fch M cap a j tr cap' a' -> fch M cap a j (RFree n x :: tr) cap' a'.

Lemma fch_app M cap a j t1 c1 a1 t2 c2 a2 : fch M cap a j t1 c1 a1 -> fch M c1 a1 (j + nretF t1) t2 c2 a2 ->
  fch M cap a j (t1 ++ t2) c2 a2.
Proof.
  intros H1. revert t2 c2 a2.
  induction H1 as [cap a j|cap a j c tr cap' a' Hc HM Hch IH|cap a j n x tr cap' a' Hn Hch IH]; intros t2 c2 a2 H2.
  - cbn [app]. cbn [nret fold_right] in H2. rewrite Nat.add_0_r in H2. exact H2.
  - cbn [app]. apply fch_grow; [exact Hc|exact HM|]. apply IH.
    assert (E : Nat.add j (nretF ((if Z.eqb cap 0%Z then RMalloc c else RRealloc cap c a) :: tr)) =
      Nat.add (S j) (nretF tr)) by (destruct (Z.eqb cap 0%Z); change (nretF (_ :: tr)) with (S (nretF tr)); lia).
    rewrite E in H2. exact H2.
  - cbn [app]. apply fch_free; [exact Hn|]. apply IH. cbn in H2. exact H2.
Qed.

Lemma fch_le M cap a j tr cap' a' : fch M cap a j tr cap' a' -> cap <= cap'.
Proof. intros H. induction H as [|cap a j c tr cap' a' Hc _ _ IH|]; lia. Qed.

Lemma fch_nogrow M cap a j tr cap' a' : fch M cap a j tr cap' a' -> cap' = cap -> a' = a.
Proof.
  intros H. induction H as [|cap a j c tr cap' a' Hc _ Hch IH|cap a j n x tr cap' a' _ _ IH]; intros E.
  - reflexivity.
  - pose proof (fch_le _ _ _ _ _ _ _ Hch). lia.
  - exact (IH E).
Qed.

Lemma fch_first M cap a j tr cap' a' : fch M cap a j tr cap' a' -> cap <> 0 -> cap' <> cap ->
  exists c, In (RRealloc cap c a) tr.
Proof.
  intros H. induction H as [cap a j|cap a j c tr cap' a' Hc _ Hch IH|cap a j n x tr cap' a' _ _ IH]; intros H0 Hne.
  - exfalso. exact (Hne eq_refl).
  - exists c. left. rewrite (proj2 (Z.eqb_neq cap 0) H0). reflexivity.
  - destruct (IH H0 Hne) as (c & Hc). exists c. right. exact Hc.
Qed.

Lemma fch_fsz M cap a j tr cap' a' : fch M cap a j tr cap' a' -> Forall (fun n => 0 <= n) (fsz tr).
Proof.
  intros H. induction H as [|cap a j c tr cap' a' _ _ _ IH|cap a j n x tr cap' a' Hn _ IH].
  - constructor.
  - destruct (cap =? 0); exact IH.
  - constructor; [exact Hn|exact IH].
Qed.

Lemma op7_ch_fch M cap a j tr cap' a' : op7_ch M cap a j tr cap' a' -> fch M cap a j tr cap' a'.
Proof.
  intros H. induction H as [cap a j|cap a j c tr cap' a' Hc HM _ IH]; [apply fch_nil|]. apply fch_grow; assumption.
Qed.

Lemma fch_send M live mx NO CAP LEN j o : 0 <= mx -> 0 <= NO -> 0 <= CAP -> 2 * (NO + LEN) <= M ->
  fch M CAP o j (send_line_tr live mx NO CAP LEN j o) (send_line_cap live mx NO CAP LEN)
    (send_line_out live mx NO CAP LEN j o).
Proof.
  intros Hmx HNO HC HM. unfold send_line_tr, send_line_cap, send_line_out. destruct live; [|apply fch_nil].
  rewrite (op7_sl_cap _ mx NO CAP LEN 0 adr0 j o). apply op7_ch_fch. apply (op7_sl_ch M mx); assumption.
Qed.

Lemma fch_gesture M live mx NO CAP XL j o : 0 <= mx -> 0 <= NO -> 0 <= CAP -> 0 <= XL -> 2 * (NO + XL + 5) <= M ->
  fch M CAP o j (gesture_end_tr live mx NO CAP XL j o) (gesture_end_cap live mx NO CAP XL)
    (gesture_end_out live mx NO CAP XL j o).
Proof.
  intros Hmx HNO HC HX HM. unfold gesture_end_tr, gesture_end_cap, gesture_end_out.
  pose proof (fch_send M live mx NO CAP XL j o Hmx HNO HC ltac:(lia)) as F1.
  apply (fch_app _ _ _ _ _ _ _ _ _ _ F1). apply fch_send; [exact Hmx|lia|pose proof (fch_le _ _ _ _ _ _ _ F1); lia|lia].
Qed.

Lemma fsz_sl f mx no cap rem j o : fsz (fst (sl_run f mx no cap rem j o)) = [].
Proof.
  revert no cap rem j o. induction f as [|f IH]; intros no cap rem j o; cbn [sl_run]; [reflexivity|]. cbv zeta.
  destruct (rem <=? 0); [reflexivity|].
  destruct (cap <? no + (if negb (mx =? 0) && (mx <? rem) then mx else rem)); [|apply IH].
  cbn [fst]. destruct (cap =? 0); cbn [fsz]; apply IH.
Qed.

Lemma fsz_send live mx NO CAP LEN j o : fsz (send_line_tr live mx NO CAP LEN j o) = [].
Proof. unfold send_line_tr. destruct live; [apply fsz_sl|reflexivity]. Qed.

Lemma fsz_gesture live mx NO CAP XL j o : fsz (gesture_end_tr live mx NO CAP XL j o) = [].
Proof. unfold gesture_end_tr. rewrite fsz_app, !fsz_send. reflexivity. Qed.

Lemma fsz_keys live mx : forall xks no cap j o,
  fsz (fst (keys_end_run live mx no cap xks j o)) = map (fun x => fst x + 1) xks.
Proof.
  induction xks as [|[xl ka] r IH]; intros no cap j o; [reflexivity|]. cbn [keys_end_run]. cbv zeta. cbn [fst].
  rewrite fsz_app, fsz_gesture. cbn [fsz app map fst]. rewrite IH. reflexivity.
Qed.

Lemma fch_keys M live mx : 0 <= mx -> forall xks no cap j o, Forall (fun x => 0 <= fst x) xks -> 0 <= no -> 0 <= cap ->
  2 * (no + zsum (fun x => fst x + 5) xks) <= M ->
  fch M cap o j (fst (keys_end_run live mx no cap xks j o)) (fst (snd (keys_end_run live mx no cap xks j o)))
    (snd (snd (keys_end_run live mx no cap xks j o))).
Proof.
  intros Hmx. induction xks as [|[xl ka] r IH]; intros no cap j o Hx Hno Hcap HM; [apply fch_nil|].
  apply Forall_cons_iff in Hx as [Hxl Hr]. cbn [fst] in Hxl. rewrite zsum_cons in HM. cbn [fst] in HM.
  assert (Z0 : 0 <= zsum (fun x => fst x + 5) r).
  { apply zsum_nonneg. intros y Hy. rewrite Forall_forall in Hr. pose proof (Hr y Hy). cbv beta in *. lia. }
  cbn [keys_end_run]. cbv zeta. cbn [fst snd].
  pose proof (fch_gesture M live mx no cap xl j o Hmx Hno Hcap Hxl ltac:(lia)) as F1.
  apply (fch_app _ _ _ _ _ _ _ _ _ _ F1). apply fch_free; [lia|].
  apply IH; [exact Hr|lia|pose proof (fch_le _ _ _ _ _ _ _ F1); lia|lia].
Qed.

Lemma keys_cap_ind live mx : forall xks xks' no cap j j' o o', map fst xks = map fst xks' ->
  fst (snd (keys_end_run live mx no cap xks j o)) = fst (snd (keys_end_run live mx no cap xks' j' o')).
Proof.
  induction xks as [|[xl ka] r IH]; intros [|[xl' ka'] r'] no cap j j' o o' H; try discriminate H; [reflexivity|].
  cbn [map fst] in H. injection H as -> H. cbn [keys_end_run]. cbv zeta. cbn [snd]. apply IH. exact H.
Qed.

Lemma key_runs_fst nm ks : map fst (key_runs nm ks) = key_lens ks.
Proof. unfold key_runs, key_lens. rewrite map_map. reflexivity. Qed.

Lemma key_lens_fst ks : map fst (map (fun xl => (xl, adr0)) (key_lens ks)) = key_lens ks.
Proof. rewrite map_map. cbn [fst]. apply map_id. Qed.

Lemma keys_total_runs nm ks : zsum (fun x => fst x + 5) (key_runs nm ks) = keys_total ks.
Proof.
  induction ks as [|kk ks IH]; [reflexivity|]. unfold key_runs, keys_total in *. cbn [map fold_right].
  rewrite zsum_cons. cbn [fst]. rewrite IH. lia.
Qed.

Lemma key_runs_nonneg nm ks : Forall (fun x => 0 <= fst x) (key_runs nm ks).
Proof. apply Forall_forall. intros x Hx. unfold key_runs in Hx. apply in_map_iff in Hx as (kk & <- & _). cbn [fst]. lia. Qed.

Lemma keys_total_nonneg ks : 0 <= keys_total ks.
Proof. rewrite <- (keys_total_runs (fun _ => adr0) ks). apply zsum_nonneg. intros x Hx.
  pose proof (proj1 (Forall_forall _ _) (key_runs_nonneg (fun _ => adr0) ks) x Hx) as H. cbv beta in *. lia. Qed.

Lemma entries_total_nonneg es : 0 <= entries_total es.
Proof.
  induction es as [|e es IH]; [reflexivity|].
  change (entries_total (e :: es)) with (keys_total (re_keys e) + entries_total es).
  pose proof (keys_total_nonneg (re_keys e)). lia.
Qed.

Lemma fch_entries M nm live mx : 0 <= mx -> forall es no cap j o,
  Forall (fun e => 0 <= re_cap e /\ (re_hp e <> 0 -> 0 <= re_kh e)) es -> 0 <= no -> 0 <= cap ->
  2 * (no + entries_total es) <= M ->
  fch M cap o j (fst (entries_end_run nm live mx no cap es j o)) (fst (snd (entries_end_run nm live mx no cap es j o)))
    (snd (snd (entries_end_run nm live mx no cap es j o))).
Proof.
  intros Hmx. induction es as [|e r IH]; intros no cap j o He Hno Hcap HM; [apply fch_nil|].
  apply Forall_cons_iff in He as [(He1 & He2) Hr].
  change (entries_total (e :: r)) with (keys_total (re_keys e) + entries_total r) in HM.
  pose proof (entries_total_nonneg r) as T0. pose proof (keys_total_nonneg (re_keys e)) as K0.
  cbn [entries_end_run]. cbv zeta. cbn [fst snd].
  set (tf := if re_cap e =? 0 then [] else [RFree (re_cap e) (nm (re_buf e))]).
  assert (Ftf : fch M cap o j tf cap o).
  { unfold tf. destruct (re_cap e =? 0); [apply fch_nil|]. apply fch_free; [exact He1|apply fch_nil]. }
  assert (Ntf : nretF tf = 0%nat) by (unfold tf; destruct (re_cap e =? 0); reflexivity).
  apply (fch_app _ _ _ _ _ _ _ _ _ _ Ftf). rewrite Ntf, Nat.add_0_r.
  pose proof (fch_keys M live mx Hmx (key_runs nm (re_keys e)) no cap j o (key_runs_nonneg nm (re_keys e)) Hno Hcap
    ltac:(rewrite keys_total_runs; lia)) as FK.
  rewrite (keys_cap_ind live mx (key_runs nm (re_keys e)) (map (fun xl => (xl, adr0)) (key_lens (re_keys e)))
    no cap j 0 o adr0) in FK by (rewrite key_runs_fst, key_lens_fst; reflexivity).
  assert (FG : fch M cap o j (gestures_end_tr live mx no cap (key_runs nm (re_keys e)) (re_hp e) (re_kh e) j o
      (nm (re_hp e))) (gestures_end_cap live mx no cap (key_lens (re_keys e)))
      (gestures_end_out live mx no cap (key_runs nm (re_keys e)) j o)).
  { unfold gestures_end_tr, gestures_end_out. apply (fch_app _ _ _ _ _ _ _ _ _ _ FK).
    destruct (Z.eqb_spec (re_hp e) 0) as [H0|H0]; [apply fch_nil|]. apply fch_free; [exact (He2 H0)|apply fch_nil]. }
  apply (fch_app _ _ _ _ _ _ _ _ _ _ FG). apply IH; [exact Hr|lia| |lia].
  pose proof (fch_le _ _ _ _ _ _ _ FG). lia.
Qed.

Lemma entries_cap_ind live mx : forall es nm nm' no cap j j' o o',
  fst (snd (entries_end_run nm live mx no cap es j o)) = fst (snd (entries_end_run nm' live mx no cap es j' o')).
Proof.
  induction es as [|e r IH]; intros nm nm' no cap j j' o o'; [reflexivity|]. cbn [entries_end_run]. cbv zeta.
  cbn [snd]. apply IH.
Qed.

Lemma fch_finish nm live mx CAP es o : 0 <= mx -> 0 <= CAP ->
  Forall (fun e => 0 <= re_cap e /\ (re_hp e <> 0 -> 0 <= re_kh e)) es ->
  fch (2 * entries_total es) CAP o 0 (relay_finish_tr nm live mx 0 CAP es 0 o) (relay_finish_cap live mx 0 CAP es)
    (relay_finish_out nm live mx 0 CAP es 0 o).
Proof.
  intros Hmx HC He. unfold relay_finish_tr, relay_finish_cap, relay_finish_out.
  rewrite (entries_cap_ind live mx es (fun _ => adr0) nm 0 CAP 0 0 adr0 o).
  apply fch_entries; [exact Hmx|exact He|lia|exact HC|lia].
Qed.

Lemma keys_off mx : forall xks no cap j o, fst (snd (keys_end_run false mx no cap xks j o)) = cap.
Proof.
  induction xks as [|[xl ka] r IH]; intros no cap j o; [reflexivity|]. cbn [keys_end_run]. cbv zeta. cbn [snd].
  rewrite IH. reflexivity.
Qed.

Lemma entries_off nm mx : forall es no cap j o, fst (snd (entries_end_run nm false mx no cap es j o)) = cap.
Proof.
  induction es as [|e r IH]; intros no cap j o; [reflexivity|].
  cbn [entries_end_run]. cbv zeta. cbn [snd]. rewrite IH. unfold gestures_end_cap. apply keys_off.
Qed.

Lemma fin_cap_off mx es no cap : relay_finish_cap false mx no cap es = cap.
Proof. unfold relay_finish_cap. apply entries_off. Qed.

Lemma ent_dels_cons e r : ent_dels (e :: r) = ((if re_cap e =? 0 then [] else [(re_buf e, re_cap e)]) ++
  (if re_hp e =? 0 then [] else [(re_hp e, re_kh e)])) ++ ent_dels r.
Proof. reflexivity. Qed.

Lemma fin_free_at nm live mx : forall es no cap j o x, In x (map fst (ent_dels es)) ->
  exists m, In (RFree m (nm x)) (fst (entries_end_run nm live mx no cap es j o)).
Proof.
  induction es as [|e r IH]; intros no cap j o x Hx; [destruct Hx|].
  rewrite ent_dels_cons, !map_app, !in_app_iff in Hx. cbn [entries_end_run]. cbv zeta. cbn [fst].
  destruct Hx as [[Hx|Hx]|Hx].
  - revert Hx. destruct (re_cap e =? 0); cbn [map fst]; [intros []|]. intros [<-|[]]. exists (re_cap e).
    apply in_or_app. left. left. reflexivity.
  - revert Hx. destruct (re_hp e =? 0) eqn:Eh; cbn [map fst]; [intros []|]. intros [<-|[]]. exists (re_kh e).
    rewrite !in_app_iff. right. left. unfold gestures_end_tr. rewrite Eh. apply in_or_app. right. left. reflexivity.
  - match goal with |- context [fst (entries_end_run nm live mx ?a ?b r ?c ?d)] =>
      destruct (IH a b c d x Hx) as (m & Hm) end.
    exists m. rewrite !in_app_iff. right. right. exact Hm.
Qed.

Lemma fin_dels (g : Z -> Z) nm live mx : (forall x, 0 <= x -> 0 <= g x) -> forall es no cap j o,
  Forall (fun e => 0 <= re_cap e /\ (re_hp e <> 0 -> 0 <= re_kh e)) es ->
  zsum (fun t => g (snd t)) (ent_dels es) <= zsum g (fsz (fst (entries_end_run nm live mx no cap es j o))).
Proof.
  intros Hg. induction es as [|e r IH]; intros no cap j o He; [cbn; lia|].
  apply Forall_cons_iff in He as [(He1 & He2) Hr].
  rewrite ent_dels_cons. cbn [entries_end_run]. cbv zeta. cbn [fst]. unfold gestures_end_tr.
  rewrite !fsz_app, fsz_keys, !zsum_app.
  match goal with |- context [fsz (fst (entries_end_run nm live mx ?a ?b r ?c ?d))] =>
    pose proof (IH a b c d Hr) as I; revert I; generalize (fsz (fst (entries_end_run nm live mx a b r c d)));
    intros FR I end.
  assert (K : 0 <= zsum g (map (fun x => fst x + 1) (key_runs nm (re_keys e)))).
  { apply zsum_nonneg. intros y Hy. apply in_map_iff in Hy as (x & <- & Hx).
    pose proof (proj1 (Forall_forall _ _) (key_runs_nonneg nm (re_keys e)) x Hx). cbv beta in *. apply Hg. lia. }
  destruct (Z.eqb_spec (re_cap e) 0) as [C0|C0]; destruct (Z.eqb_spec (re_hp e) 0) as [H0|H0];
    cbn [fsz app]; rewrite ?zsum_app, ?zsum_cons, ?zsum_nil; cbn [snd]; rewrite ?zsum_app, ?zsum_cons, ?zsum_nil in *;
    try pose proof (Hg _ He1); try pose proof (Hg _ (He2 H0)); lia.
Qed.

Lemma out_dl3 x out CAP q1 CAP' :
  op7_dz CAP' x - op7_dz CAP x <=
  zsum (fun t => one_if x (band (snd t))) (out_move_adds out CAP q1 CAP') -
  zsum (fun t => one_if x (band (snd t))) (out_move_dels out CAP q1 CAP').
Proof.
  unfold out_move_adds, out_move_dels, op7_dz. destruct (out_same out CAP q1 CAP') eqn:S.
  - unfold out_same in S. apply andb_prop in S as [_ S]. apply Z.eqb_eq in S. subst CAP'. cbn [orb].
    rewrite !zsum_nil. lia.
  - cbn [orb]. pose proof (one_if_b x (band CAP')). pose proof (one_if_b x (band CAP)).
    destruct (Z.eqb_spec CAP' 0); destruct (Z.eqb_spec CAP 0); rewrite ?zsum_cons, ?zsum_nil; cbn [snd]; lia.
Qed.

Lemma out_db3 out CAP q1 CAP' :
  CAP' - CAP <= zsum snd (out_move_adds out CAP q1 CAP') - zsum snd (out_move_dels out CAP q1 CAP').
Proof.
  unfold out_move_adds, out_move_dels. destruct (out_same out CAP q1 CAP') eqn:S.
  - unfold out_same in S. apply andb_prop in S as [_ S]. apply Z.eqb_eq in S. subst CAP'. cbn [orb].
    rewrite !zsum_nil. lia.
  - cbn [orb]. destruct (Z.eqb_spec CAP 0); rewrite ?zsum_cons, ?zsum_nil; cbn [snd]; lia.
Qed.

Definition fI (qs : list sptr) (b1 : pbound3) (CAP : Z) (bc : pbound3) (cap : Z) (a : adrF) (t0 : trF) : Prop :=
  p3_cap bc = p3_cap b1 /\ p3_mcap bc = p3_mcap b1 /\ length (p3_live bc) = 49%nat /\
  (forall c, 0 <= c < 49 -> znth c (p3_live bc) = znth c (p3_live b1) + op7_dz cap c - op7_dz CAP c - bcnt c (fsz t0)) /\
  p3_bytes bc = p3_bytes b1 + cap - CAP - zsum (fun n => n) (fsz t0) /\ 0 <= CAP <= cap /\
  Forall (fun n => 0 <= n) (fsz t0) /\
  (forall c, count_mis (p3_mis bc) c <= count_mis (p3_mis b1) c) /\
  (forall e, In e (p3_mis bc) ->
     (cap <> 0 /\ fst e = resolveF qs a /\ (cap = CAP -> In e (p3_mis b1) /\ ~ touched qs t0 (fst e))) \/
     (In e (p3_mis b1) /\ ~ touched qs t0 (fst e))).

Lemma touched_app qs t1 t2 p : touched qs (t1 ++ t2) p -> touched qs t1 p \/ touched qs t2 p.
Proof.
  intros (a & Ea & [(n & Hn)|(k & n & Hn)]); apply in_app_or in Hn as [Hn|Hn].
  - left. exists a. split; [exact Ea|]. left. exists n. exact Hn.
  - right. exists a. split; [exact Ea|]. left. exists n. exact Hn.
  - left. exists a. split; [exact Ea|]. right. exists k, n. exact Hn.
  - right. exists a. split; [exact Ea|]. right. exists k, n. exact Hn.
Qed.

Lemma touched_one_malloc qs c p : ~ touched qs [RMalloc c] p.
Proof. intros (a & _ & [(m & [H|[]])|(k & m & [H|[]])]); discriminate H. Qed.

Lemma touched_one_free qs n x p : touched qs [RFree n x] p -> resolveF qs x = p.
Proof.
  intros (a & Ea & [(m & [H|[]])|(k & m & [H|[]])]); [|discriminate H]. injection H as -> ->. exact Ea.
Qed.

Lemma touched_one_realloc qs k n x p : touched qs [RRealloc k n x] p -> resolveF qs x = p.
Proof.
  intros (a & Ea & [(m & [H|[]])|(k' & m & [H|[]])]); [discriminate H|]. injection H as -> -> ->. exact Ea.
Qed.

Lemma fI_init qs b1 CAP a : 0 <= CAP -> length (p3_live b1) = 49%nat -> fI qs b1 CAP b1 CAP a [].
Proof.
  intros HC Hl. unfold fI. cbn [fsz]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hl|].
  split; [intros c _; change (bcnt c []) with 0; lia|]. split; [rewrite zsum_nil; lia|]. split; [lia|].
  split; [constructor|]. split; [intros c; lia|].
  intros e He. right. split; [exact He|]. intros (x & _ & [(n & [])|(k & n & [])]).
Qed.

Lemma fI_malloc qs b1 CAP bc a t0 c j : fI qs b1 CAP bc 0 a t0 -> 0 < c ->
  fI qs b1 CAP (pb3_malloc bc c) c (Ret j) (t0 ++ [RMalloc c]).
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hc. pose proof (AllocPackRoom.band_range c ltac:(lia)) as Bc.
  assert (CAP = 0) as -> by lia.
  assert (F : fsz (t0 ++ [RMalloc c]) = fsz t0) by (rewrite fsz_app; cbn [fsz]; apply app_nil_r).
  unfold fI, pb3_malloc. cbn [p3_cap p3_mcap p3_live p3_bytes p3_mis]. rewrite F.
  split; [exact H1|]. split; [exact H2|]. split; [rewrite AllocPackRoom.lv_add_length; exact H3|].
  split.
  { intros x Hx. rewrite znth_lv_add_d by (first [exact H3 | lia]). rewrite H4 by exact Hx.
    rewrite (op7_dz_pos c x) by lia. rewrite !op7_dz_0. lia. }
  split; [lia|]. split; [lia|]. split; [exact H7|]. split; [exact H8|].
  intros e He. destruct (H9 e He) as [(E & _)|(Hm & Hu)]; [exfalso; lia|right; split; [exact Hm|]].
  intros Ht. apply touched_app in Ht as [Ht|Ht]; [exact (Hu Ht)|exact (touched_one_malloc qs c _ Ht)].
Qed.

Lemma fI_realloc qs b1 CAP bc cap a t0 c j : fI qs b1 CAP bc cap a t0 -> 0 < cap < c ->
  fI qs b1 CAP (pb3_realloc bc cap c (resolveF qs a) (nth j qs (SP 0 0))) c (Ret j) (t0 ++ [RRealloc cap c a]).
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hc.
  pose proof (AllocPackRoom.band_range c ltac:(lia)) as Bc. pose proof (AllocPackRoom.band_range cap ltac:(lia)) as Bk.
  assert (F : fsz (t0 ++ [RRealloc cap c a]) = fsz t0) by (rewrite fsz_app; cbn [fsz]; apply app_nil_r).
  unfold fI, pb3_realloc. cbn [p3_cap p3_mcap p3_live p3_bytes p3_mis]. rewrite F.
  split; [exact H1|]. split; [exact H2|]. split; [rewrite !AllocPackRoom.lv_add_length; exact H3|].
  split.
  { intros x Hx. rewrite znth_lv_add_d by (first [rewrite AllocPackRoom.lv_add_length; exact H3 | lia]).
    rewrite znth_lv_add_d by (first [exact H3 | lia]). rewrite H4 by exact Hx.
    rewrite (op7_dz_pos c x), (op7_dz_pos cap x) by lia. lia. }
  split; [lia|]. split; [lia|]. split; [exact H7|].
  split.
  { intros x. pose proof (count_mis_realloc (p3_mis bc) cap c (resolveF qs a) (nth j qs (SP 0 0)) x ltac:(lia)).
    specialize (H8 x). lia. }
  intros e He. apply op7_mis_realloc_in in He as [(Ef & Eq)|(Hm & Hn)].
  - left. split; [lia|]. split; [exact Ef|]. intros E. exfalso. lia.
  - destruct (H9 e Hm) as [(_ & Ef & _)|(Hm1 & Hu)]; [contradiction|]. right. split; [exact Hm1|].
    intros Ht. apply touched_app in Ht as [Ht|Ht]; [exact (Hu Ht)|].
    apply Hn. symmetry. exact (touched_one_realloc qs _ _ _ _ Ht).
Qed.

Lemma fI_free qs b1 CAP bc cap a t0 n x : fI qs b1 CAP bc cap a t0 -> 0 <= n ->
  fI qs b1 CAP (pb3_free bc n (resolveF qs x)) cap a (t0 ++ [RFree n x]).
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hn. pose proof (AllocPackRoom.band_range n Hn) as Bn.
  assert (F : fsz (t0 ++ [RFree n x]) = fsz t0 ++ [n]) by (rewrite fsz_app; reflexivity).
  unfold fI, pb3_free. cbn [p3_cap p3_mcap p3_live p3_bytes p3_mis]. rewrite F.
  split; [exact H1|]. split; [exact H2|]. split; [rewrite AllocPackRoom.lv_add_length; exact H3|].
  split.
  { intros y Hy. rewrite znth_lv_add_d by (first [exact H3 | lia]). rewrite H4 by exact Hy.
    rewrite bcnt_app, bcnt_cons. change (bcnt y []) with 0. lia. }
  split; [rewrite zsum_app, zsum_cons, zsum_nil; lia|]. split; [exact H6|].
  split; [apply Forall_app; split; [exact H7|repeat constructor; exact Hn]|].
  split; [intros y; pose proof (count_mis_filter (p3_mis bc) (fun e => negb (sptr_eqb (fst e) (resolveF qs x))) y);
    specialize (H8 y); unfold mis_del; lia|].
  intros e He. apply op7_mis_del_in in He as [Hm Hne].
  assert (U : forall t0', ~ touched qs t0' (fst e) -> ~ touched qs (t0' ++ [RFree n x]) (fst e)).
  { intros t0' Hu Ht. apply touched_app in Ht as [Ht|Ht]; [exact (Hu Ht)|].
    apply Hne. symmetry. exact (touched_one_free qs _ _ _ Ht). }
  destruct (H9 e Hm) as [(Hc0 & Ef & Hcc)|(Hm1 & Hu)].
  - left. split; [exact Hc0|]. split; [exact Ef|]. intros Ec. destruct (Hcc Ec) as (Hm1 & Hu).
    split; [exact Hm1|exact (U t0 Hu)].
  - right. split; [exact Hm1|exact (U t0 Hu)].
Qed.

Lemma fch_run qs b1 CAP M : forall cap a j tr cap' a', fch M cap a j tr cap' a' ->
  forall bc t0, fI qs b1 CAP bc cap a t0 -> fI qs b1 CAP (run3 qs bc j tr) cap' a' (t0 ++ tr).
Proof.
  intros cap a j tr cap' a' H.
  induction H as [cap a j|cap a j c tr cap' a' Hc HM Hch IH|cap a j n x tr cap' a' Hn Hch IH]; intros bc t0 HI.
  - cbn [run_from]. rewrite app_nil_r. exact HI.
  - destruct (Z.eqb_spec cap 0) as [E|E].
    + subst cap. cbn [run_from].
      replace (t0 ++ RMalloc c :: tr) with ((t0 ++ [RMalloc c]) ++ tr) by (rewrite <- app_assoc; reflexivity).
      apply IH. eapply fI_malloc; [exact HI|lia].
    + cbn [run_from].
      replace (t0 ++ RRealloc cap c a :: tr) with ((t0 ++ [RRealloc cap c a]) ++ tr)
        by (rewrite <- app_assoc; reflexivity).
      apply IH. apply fI_realloc; [exact HI|lia].
  - cbn [run_from]. replace (t0 ++ RFree n x :: tr) with ((t0 ++ [RFree n x]) ++ tr)
      by (rewrite <- app_assoc; reflexivity).
    apply IH. apply fI_free; [exact HI|exact Hn].
Qed.

Lemma fch_room qs b1 CAP M (R : pbound3 -> Z -> Prop)
  (HR : forall bc cap a t0 c, fI qs b1 CAP bc cap a t0 -> 0 <= cap < c -> c <= M -> R bc c) :
  forall cap a j tr cap' a', fch M cap a j tr cap' a' -> forall bc t0, fI qs b1 CAP bc cap a t0 ->
  room_from pbound3 sptr (SP 0 0) pb3_malloc pb3_free pb3_realloc R qs bc j tr.
Proof.
  intros cap a j tr cap' a' H.
  induction H as [cap a j|cap a j c tr cap' a' Hc HM Hch IH|cap a j n x tr cap' a' Hn Hch IH]; intros bc t0 HI.
  - exact I.
  - destruct (Z.eqb_spec cap 0) as [E|E].
    + subst cap. cbn [room_from]. split; [exact (HR bc 0 a t0 c HI Hc HM)|].
      apply (IH _ (t0 ++ [RMalloc c])). eapply fI_malloc; [exact HI|lia].
    + cbn [room_from]. split; [exact (HR bc cap a t0 c HI Hc HM)|].
      apply (IH _ (t0 ++ [RRealloc cap c a])). apply fI_realloc; [exact HI|lia].
  - cbn [room_from]. apply (IH _ (t0 ++ [RFree n x])). apply fI_free; [exact HI|exact Hn].
Qed.

Lemma fI_rIv qs b CAP bc cap a t0 : fI qs b CAP bc cap a t0 -> cap <= 2 * NMAX -> rIv b bc.
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _) Hc. unfold rIv. split; [exact H1|]. split; [exact H2|].
  split.
  { intros c Hcc. rewrite (H4 c Hcc). pose proof (op7_dz_b cap c). pose proof (op7_dz_b CAP c).
    pose proof (bcnt_nonneg c (fsz t0)). lia. }
  split; [rewrite H5; pose proof (zsum_id_nonneg _ H7); lia|exact H8].
Qed.

Theorem fin_res3 E k L A G out es hj live mx CAP :
  RI3_reply E k (view_of G out es hj) L A -> List.NoDup (map fst (blocks L A)) -> 0 <= mx -> 0 <= CAP ->
  Forall (fun e => 0 <= re_cap e /\ (re_hp e <> 0 -> 0 <= re_kh e)) es -> entries_total es < INPUT_MAX ->
  res_tr pack3_form (fin_RV_d RI3_reply E k L A G out es hj live mx CAP) A
    (relay_finish_tr (known_at L A) live mx 0 CAP es 0 (known_at L A out)).
Proof.
  intros (b & al & alb & HR & HL) HND0 Hmx HC He Htot.
  pose proof HL as (_ & _ & _ & HlL & _).
  pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & HU & _) & _).
  pose proof (fch_finish (known_at L A) live mx CAP es (known_at L A out) Hmx HC He) as Hch.
  assert (HMx : 2 * entries_total es <= NMAX) by (unfold INPUT_MAX, NMAX in *; pose proof (entries_total_nonneg es); lia).
  exists b. split; [exact HR|]. split.
  - intros qs _. rewrite roomF3.
    refine (fch_room qs b CAP (2 * entries_total es) room_pack3 _ _ _ _ _ _ _ Hch b [] (fI_init qs b CAP _ HC HlL)).
    intros bc cap0 a0 t0 c HI Hc HcM. apply (room3_rIv _ _ _ _ _ _ b al alb bc c HL); [|lia].
    apply (fI_rIv qs b CAP bc cap0 a0 t0 HI). lia.
  - intros L' A' qs _ HA'. rewrite runF3 in HA'. hnf.
    intros G' out' es' hj' Hcov Hp Hek Hes Hhj q1 Hq1 Hlink HM HND HK HWs HWg.
    pose proof (fch_run qs b CAP _ _ _ _ _ _ _ Hch b [] (fI_init qs b CAP _ HC HlL)) as HI. cbn [app] in HI.
    destruct HI as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9).
    destruct (nc_move_grow3 _ _ _ _ _ _ _ _ HM) as (G1 & G2).
    pose proof (out_db3 out CAP q1 (relay_finish_cap live mx 0 CAP es)) as OB.
    pose proof (fin_dels (fun n => n) (known_at L A) live mx (fun x Hx => Hx) es 0 CAP 0 (known_at L A out) He) as FB.
    cbv beta in FB. change (zsum (fun t => snd t) (ent_dels es)) with (zsum snd (ent_dels es)) in FB.
    apply (step3 E k k _ L A b al alb _ L' A' _ []
      (dl_of (out_move_dels out CAP q1 (relay_finish_cap live mx 0 CAP es) ++ ent_dels es)
        (out_move_adds out CAP q1 (relay_finish_cap live mx 0 CAP es)))
      (db_of (out_move_dels out CAP q1 (relay_finish_cap live mx 0 CAP es) ++ ent_dels es)
        (out_move_adds out CAP q1 (relay_finish_cap live mx 0 CAP es)))
      (out_move_dels out CAP q1 (relay_finish_cap live mx 0 CAP es) ++ ent_dels es)
      (fun p => live = true /\ out_same out CAP q1 (relay_finish_cap live mx 0 CAP es) = false /\
         p = resolveF qs (relay_finish_out (known_at L A) live mx 0 CAP es 0 (known_at L A out)))
      HL HR (Forall_nil _) HA' I1 I2 I3).
    + intros c Hc. rewrite (I4 c Hc). change (bcnt c []) with 0.
      pose proof (out_dl3 c out CAP q1 (relay_finish_cap live mx 0 CAP es)) as OD.
      pose proof (fin_dels (fun n => one_if c (band n)) (known_at L A) live mx (fun x _ => proj1 (one_if_b c (band x)))
        es 0 CAP 0 (known_at L A out) He) as FD.
      unfold dl_of. rewrite zsum_app. unfold bcnt, relay_finish_tr. cbv beta in FD. lia.
    + rewrite I5. unfold db_of. rewrite zsum_app. unfold relay_finish_tr. rewrite zsum_nil. lia.
    + intros e He'.
      assert (UC : In e (p3_mis b) ->
          ~ touched qs (relay_finish_tr (known_at L A) live mx 0 CAP es 0 (known_at L A out)) (fst e) ->
          (In e (p3_mis b) /\ ~ In (ptr_addr L (fst e))
             (map fst (out_move_dels out CAP q1 (relay_finish_cap live mx 0 CAP es) ++ ent_dels es))) \/
          (live = true /\ out_same out CAP q1 (relay_finish_cap live mx 0 CAP es) = false /\
           fst e = resolveF qs (relay_finish_out (known_at L A) live mx 0 CAP es 0 (known_at L A out)))).
      { intros Hm Hu.
        destruct (in_dec Z.eq_dec (ptr_addr L (fst e)) (map fst (out_move_dels out CAP q1
          (relay_finish_cap live mx 0 CAP es) ++ ent_dels es))) as [Hx|Hx]; [|left; split; assumption].
        destruct (HU e Hm) as (_ & n & Hn). pose proof (sptr_of_at L A (fst e) n HND0 Hn) as Es.
        rewrite map_app, in_app_iff in Hx. destruct Hx as [Hx|Hx].
        - unfold out_move_dels in Hx. revert Hx.
          destruct (out_same out CAP q1 (relay_finish_cap live mx 0 CAP es)) eqn:Os; cbn [orb]; [intros []|].
          destruct (Z.eqb_spec CAP 0) as [C0|C0]; cbn [map fst]; [intros []|]. intros [Ex|[]].
          destruct live eqn:Lv; subst live.
          + right. split; [reflexivity|]. split; [reflexivity|].
            destruct (Z.eq_dec (relay_finish_cap true mx 0 CAP es) CAP) as [Ec|Ec].
            * rewrite (fch_nogrow _ _ _ _ _ _ _ Hch Ec). cbn [resolve known_at]. rewrite Ex. symmetry. exact Es.
            * exfalso. destruct (fch_first _ _ _ _ _ _ _ Hch C0 Ec) as (c & Hin). apply Hu.
              rewrite <- Es, <- Ex. exact (touched_realloc qs _ _ _ _ Hin).
          + exfalso. rewrite (Hq1 eq_refl), fin_cap_off in Os. unfold out_same in Os.
            rewrite !Z.eqb_refl in Os. discriminate Os.
        - exfalso. destruct (fin_free_at (known_at L A) live mx es 0 CAP 0 (known_at L A out) _ Hx) as (m & Hin).
          apply Hu. rewrite <- Es. exact (touched_free qs _ _ _ Hin). }
      destruct (I9 e He') as [(Hc0 & Ef & Hcc)|(Hm & Hu)]; [|exact (UC Hm Hu)].
      destruct (Z.eq_dec (relay_finish_cap live mx 0 CAP es) CAP) as [Ec|Ec].
      * destruct (Hcc Ec) as (Hm & Hu). exact (UC Hm Hu).
      * right. destruct live eqn:Lv; subst live; [|exfalso; exact (Ec (fin_cap_off mx es 0 CAP))].
        split; [reflexivity|]. split; [|exact Ef]. unfold out_same. rewrite (proj2 (Z.eqb_neq _ _) Ec).
        apply andb_false_r.
    + intros p (Hlv & Hos & ->). rewrite (proj2 (Hlink Hlv)).
      apply (nc_move_adds_in _ _ _ _ _ _ _ _ (q1, relay_finish_cap live mx 0 CAP es) HM).
      unfold out_move_adds. rewrite Hos. left. reflexivity.
    + exact HND.
    + exact HK.
    + exact (nc_len G' out' es' hj' Hes Hhj).
    + exact G1.
    + exact G2.
    + exact HWs.
    + rewrite !wt_view. change (zlen []) with 0. lia.
    + exact (cred_same E k G out es hj G' out' es' hj' Hp Hek).
    + exact (ek_view_nonneg hj').
Qed.
