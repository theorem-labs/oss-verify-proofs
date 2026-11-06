From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import PackReparse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require SlotSizes.
Import ListNotations.
Local Open Scope Z_scope.

(* U twin of Prog/PackBytes.v (c-frame-gi): the rendered block sizes of a parsed tree, with their 16-byte headers,
   stay under 232 bytes per input byte. ReaderRes and PackReparse are the ubsan build's; SlotSizes is the shared
   plain one, whose lemmas state only Spec terms. *)

Definition bbg_q (L : list nat) : Z := zl (map (fun b => Z.of_nat b + 16) L).

Lemma bbg_q_app : forall a b, bbg_q (a ++ b) = bbg_q a + bbg_q b.
Proof. intros a b. unfold bbg_q. rewrite map_app. apply zl_app. Qed.

Lemma bbg_q_cons : forall a l, bbg_q (a :: l) = Z.of_nat a + 16 + bbg_q l.
Proof. reflexivity. Qed.

Lemma bbg_q_nil : bbg_q [] = 0.
Proof. reflexivity. Qed.

Lemma bbg_q_one : forall a, bbg_q [a] = Z.of_nat a + 16.
Proof. intros a. rewrite bbg_q_cons, bbg_q_nil. lia. Qed.

Lemma bbg_q_eq : forall l, bbg_q l = zl (map Z.of_nat l) + 16 * Z.of_nat (length l).
Proof.
  induction l as [|a l IH]; [reflexivity|]. rewrite bbg_q_cons, IH. cbn [map zl length]. lia.
Qed.

Definition bbg_w (o : bool) : Z := if o then 312 else 232.

Definition bbg_ib (o : bool) (m : list Z * jv) : Z := bbg_q (ib o m) + bbg_w o.

Lemma bbg_rkb : forall o k, (1 <= k)%nat -> bbg_q (rkb o (rfcap k 0 0)) <= 232 + bbg_w o * Z.of_nat k.
Proof.
  intros o k Hk. destruct (rfcap_shape k Hk) as (j & E & _ & H2). rewrite E.
  pose proof (Nat.pow_nonzero 2 j ltac:(discriminate)) as P.
  rewrite rkb_S by lia. destruct H2 as [->|H2].
  - destruct o; cbn [bbg_w Nat.pow]; rewrite ?bbg_q_cons, ?bbg_q_nil; lia.
  - set (p := (2 ^ j)%nat) in *. clearbody p.
    destruct o; cbn [bbg_w]; rewrite ?bbg_q_cons, ?bbg_q_nil; lia.
Qed.

Lemma bbg_flat : forall o nw, bbg_q (flat_map (ib o) nw) + bbg_w o * Z.of_nat (length nw) = zl (map (bbg_ib o) nw).
Proof.
  intros o nw. induction nw as [|m nw IH]; cbn [flat_map map zl length].
  - rewrite bbg_q_nil. lia.
  - rewrite bbg_q_app. unfold bbg_ib at 1. rewrite <- IH. destruct o; cbn [bbg_w]; lia.
Qed.

Section PZ.

Variable sm : list Z -> Z * Z.

Definition bbg_RL (f : nat) : Prop := forall d o n cap acc y ok v r tr ok',
  jrl sm f d o n cap acc y ok = (Some (v, r), tr, ok') ->
  exists nw, nw <> [] /\ v = mk o (rev acc ++ nw) /\
    zl (map (bbg_ib o) nw) + 232 * Z.of_nat (length r) <= 232 * Z.of_nat (length y).

Lemma bbg_cont : forall f d o b y ok v r tr ok', bbg_RL f ->
  jr_cont (jrl sm f) d o (b :: y) ok = (Some (v, r), tr, ok') ->
  bbg_q (rtsz v) + 232 * Z.of_nat (length r) <= 232 * Z.of_nat (length (b :: y)).
Proof.
  intros f d o b y ok v r tr ok' IHl H. unfold jr_cont in H.
  destruct (Nat.ltb MAXD (S d)); cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  cbn [tl] in H. cbv zeta in H. cbn [length].
  assert (LOOP : forall z, (length z <= length y)%nat -> jrl sm f (S d) o 0 0 [] z ok = (Some (v, r), tr, ok') ->
    bbg_q (rtsz v) + 232 * Z.of_nat (length r) <= 232 * Z.of_nat (S (length y))).
  { intros z Hz HL. destruct (IHl _ _ _ _ _ _ _ _ _ _ _ HL) as (nw & Hne & -> & Hc). cbn [rev app].
    rewrite rtsz_mk, bbg_q_app.
    assert (Hk : (1 <= length nw)%nat) by (destruct nw; [contradiction | cbn [length]; lia]).
    pose proof (bbg_rkb o (length nw) Hk) as Hr. pose proof (bbg_flat o nw) as Hs.
    destruct o; cbn [bbg_w] in Hr, Hs; lia. }
  destruct (skip y) as [|c r0] eqn:Ey; cbv beta iota in H.
  { exact (LOOP [] ltac:(cbn [length]; lia) H). }
  destruct (c =? closer o); cbv beta iota in H.
  2: { exact (LOOP (c :: r0) ltac:(rewrite <- Ey; exact (skip_len y)) H). }
  unfold jret in H. injection H as Hv Hr _ _. subst v r.
  pose proof (skip_len y) as Hy. rewrite Ey in Hy. cbn [length] in Hy.
  replace (bbg_q (rtsz (mk o []))) with 0 by (destruct o; reflexivity). lia.
Qed.

Lemma bbg_fuel : forall f,
  (forall d x ok v r tr ok', jrv sm f d x ok = (Some (v, r), tr, ok') ->
     bbg_q (rtsz v) + 232 * Z.of_nat (length r) <= 232 * Z.of_nat (length x)) /\ bbg_RL f.
Proof.
  induction f as [|f [IHv IHl]].
  - split; [|unfold bbg_RL]; intros; cbn [jrv jrl] in *; unfold jrefuse in *; discriminate.
  - split.
    + intros d x ok v r tr ok' H. cbn [jrv] in H.
      destruct (skip x) as [|b y] eqn:Ex; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      pose proof (skip_len x) as Hs'. rewrite Ex in Hs'.
      enough (G : bbg_q (rtsz v) + 232 * Z.of_nat (length r) <= 232 * Z.of_nat (length (b :: y))) by lia.
      destruct (b =? 123); cbv beta iota in H; [exact (bbg_cont f d true b y ok v r tr ok' IHl H)|].
      destruct (b =? 91); cbv beta iota in H; [exact (bbg_cont f d false b y ok v r tr ok' IHl H)|].
      destruct (b =? 34); cbv beta iota in H.
      { apply jbind_some in H as ([s r1] & t1 & ok1 & t2 & Hj & H & _).
        destruct (jr_string_esc y ok s r1 t1 ok1 Hj) as (q & _ & Hl & _ & He).
        cbv beta iota in H. unfold jret in H. injection H as Hv Hr _ _. subst v r1.
        cbn [rtsz]. rewrite bbg_q_one. cbn [length]. lia. }
      destruct (b =? 116); cbv beta iota in H.
      { destruct (SlotSizes.lit_w _ _ _ _ _ _ _ _ H) as [-> Hl]. unfold w_true in Hl. cbn [length] in Hl |- *.
        cbn [rtsz]. rewrite bbg_q_nil. lia. }
      destruct (b =? 102); cbv beta iota in H.
      { destruct (SlotSizes.lit_w _ _ _ _ _ _ _ _ H) as [-> Hl]. unfold w_false in Hl. cbn [length] in Hl |- *.
        cbn [rtsz]. rewrite bbg_q_nil. lia. }
      destruct (b =? 110); cbv beta iota in H.
      { destruct (SlotSizes.lit_w _ _ _ _ _ _ _ _ H) as [-> Hl]. unfold w_null in Hl. cbn [length] in Hl |- *.
        cbn [rtsz]. rewrite bbg_q_nil. lia. }
      destruct (SlotSizes.num_w _ _ _ _ _ _ _ H) as (txt & bits & -> & H1 & Hl).
      cbn [rtsz]. rewrite bbg_q_one. lia.
    + unfold bbg_RL. intros d o n cap acc y ok v r tr ok' H. cbn [jrl] in H.
      apply jbind_some in H as (cap1 & tg & ok1 & t2 & _ & H & _). cbv beta in H.
      apply jbind_some in H as ([nm y1] & tn & ok2 & t3 & En & H & _). cbv beta iota in H.
      apply jbind_some in H as ([v0 r0] & tv & ok3 & t4 & Ev & H & _). cbv beta iota in H.
      pose proof (IHv d y1 ok2 v0 r0 tv ok3 Ev) as Hv0.
      pose proof (SlotSizes.name_w o y ok1 nm y1 tn ok2 En) as Hn.
      assert (Hm : forall z : list Z, (length z + 1 <= length r0)%nat ->
        bbg_ib o (nm, v0) + 232 * Z.of_nat (length z) <= 232 * Z.of_nat (length y)).
      { intros z Hz. unfold bbg_ib, ib. cbn [fst snd]. rewrite bbg_q_app.
        destruct o; cbv beta iota in Hn |- *; cbn [bbg_w].
        - rewrite bbg_q_one. change (length (flat_map ech nm)) with (elen nm) in Hn. lia.
        - subst y1. rewrite bbg_q_nil. lia. }
      pose proof (skip_len r0) as Hsr.
      destruct (skip r0) as [|c r1] eqn:Er; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      cbn [length] in Hsr.
      destruct (c =? 44); cbv beta iota in H.
      { destruct (IHl d o (S n) cap1 ((nm, v0) :: acc) r1 ok3 v r t4 ok' H) as (nw & Hne & Hv & Hc).
        exists ((nm, v0) :: nw). split; [discriminate|].
        split; [rewrite Hv; cbn [rev]; rewrite <- app_assoc; reflexivity|].
        cbn [map zl]. pose proof (Hm r1 ltac:(lia)). lia. }
      destruct (c =? closer o); cbv beta iota in H; [|unfold jrefuse in H; discriminate].
      unfold jret in H. injection H as Hv Hr _ _. subst v r.
      exists [(nm, v0)]. split; [discriminate|]. split; [cbn [rev]; reflexivity|].
      cbn [map zl]. pose proof (Hm r1 ltac:(lia)). lia.
Qed.

Theorem bbg_read : forall x t, json_read sm x = Some t ->
  zl (map Z.of_nat (rtsz t)) + 16 * Z.of_nat (length (rtsz t)) <= 232 * Z.of_nat (length x).
Proof.
  intros x t H. unfold json_read in H. rewrite jr_run_eq in H. cbn [fst] in H.
  destruct (jr_value sm 0 x []) as [[[[t' r]|] tr] ok'] eqn:E; cbn [fst post] in H; [|discriminate].
  destruct (skip r); [injection H as <-|discriminate].
  unfold jr_value in E. pose proof (proj1 (bbg_fuel _) 0%nat x [] t' r tr ok' E) as G.
  rewrite <- bbg_q_eq. lia.
Qed.

End PZ.
