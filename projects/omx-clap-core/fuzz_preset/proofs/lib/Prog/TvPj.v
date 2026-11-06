From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct TvSpec.
Import ListNotations.
Open Scope Z_scope.

Section P.
Variable segs : list Segment.

Lemma pj_items_nth : forall (P : Z -> jv -> list (Z * Z) -> Prop) l a D i,
  pj_items P a l D -> (i < length l)%nat ->
  exists Dx, incl Dx D /\ P (a + 56 * Z.of_nat i) (nth i l JNull) Dx.
Proof.
  intros P l. induction l as [|u r IH]; intros a D i H Hi; cbn [length] in Hi; [lia|].
  cbn [pj_items] in H. destruct H as (D1 & D2 & -> & H1 & H2).
  destruct i as [|i].
  - exists D1. split; [intros b Hb; apply in_or_app; left; exact Hb|]. cbn [nth]. rewrite Z.add_0_r. exact H1.
  - destruct (IH (a + 56) D2 i H2 ltac:(lia)) as (Dx & Hinc & HP).
    exists Dx. split; [intros b Hb; apply in_or_app; right; apply Hinc; exact Hb|].
    cbn [nth]. replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) by lia. exact HP.
Qed.

Lemma pj_mems_nth : forall m lblk (P : Z -> jv -> list (Z * Z) -> Prop) l a ka D i,
  pj_mems segs m lblk P a ka l D -> (i < length l)%nat ->
  exists x k Dx, In (x, k) D /\ incl Dx D /\ pj_u64 segs m (ka + 8 * Z.of_nat i) x /\
    pj_cstr segs m lblk x k (fst (nth i l ([], JNull))) /\ P (a + 56 * Z.of_nat i) (snd (nth i l ([], JNull))) Dx.
Proof.
  intros m lblk P l. induction l as [|[nm u] r IH]; intros a ka D i H Hi; cbn [length] in Hi; [lia|].
  cbn [pj_mems] in H. destruct H as (x & k & D1 & D2 & -> & Hx & Hc & H1 & H2).
  destruct i as [|i].
  - exists x, k, D1. split; [left; reflexivity|].
    split; [intros b Hb; right; apply in_or_app; left; exact Hb|].
    cbn [nth fst snd]. rewrite !Z.add_0_r. split; [exact Hx|]. split; [exact Hc | exact H1].
  - destruct (IH (a + 56) (ka + 8) D2 i H2 ltac:(lia)) as (x' & k' & Dx & Hin & Hinc & Hx' & Hc' & HP).
    exists x', k', Dx. split; [right; apply in_or_app; right; exact Hin|].
    split; [intros b Hb; right; apply in_or_app; right; apply Hinc; exact Hb|].
    cbn [nth]. replace (ka + 8 * Z.of_nat (S i)) with (ka + 8 + 8 * Z.of_nat i) by lia.
    replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) by lia.
    split; [exact Hx'|]. split; [exact Hc' | exact HP].
Qed.

Definition coll_facts (m : word -> option byte) (lblk : Z -> Z -> Prop) (v : Z) (tv : jv) (D : list (Z * Z))
    (kp yp n : Z) : Prop :=
  pj_u32 segs m v (tag tv) /\ pj_u64 segs m (v + 24) kp /\ pj_u64 segs m (v + 32) yp /\ pj_u64 segs m (v + 40) n /\
  n = Z.of_nat (length (kids tv)) /\
  (0 < n -> exists cap, n <= cap /\ lblk kp (56 * cap) /\ In (kp, 56 * cap) D) /\
  (forall i, (i < length (kids tv))%nat ->
     exists Dx, incl Dx D /\ pj_node segs m lblk (kp + 56 * Z.of_nat i) (nth i (kids tv) JNull) Dx) /\
  (forall ms i, tv = JObj ms -> (i < length ms)%nat ->
     exists x k, In (x, k) D /\ pj_u64 segs m (yp + 8 * Z.of_nat i) x /\
       pj_cstr segs m lblk x k (fst (nth i ms ([], JNull))) /\
       (exists cap, Z.of_nat (length ms) <= cap /\ lblk yp (8 * cap) /\ In (yp, 8 * cap) D)).

Lemma pj_coll : forall m lblk v tv D, pj_node segs m lblk v tv D -> tag tv = 5 \/ tag tv = 6 ->
  exists kp yp n, coll_facts m lblk v tv D kp yp n.
Proof.
  intros m lblk v tv D H Ht.
  destruct tv as [| | | txt bits | s | items | ms]; cbn [tag] in Ht; try lia.
  - cbn [pj_node] in H. destruct H as (_ & _ & num & str & kp & yp & n & cap & Hh & Hb).
    destruct Hh as (_ & HT & _ & _ & HK & HY & HN & _).
    destruct Hb as (_ & _ & En & Hnc & Hcap & Di & ED & HI).
    exists kp, yp, n. unfold coll_facts. cbn [tag kids].
    split; [exact HT|]. split; [exact HK|]. split; [exact HY|]. split; [exact HN|]. split; [exact En|].
    split.
    { intros Hn. exists cap. split; [lia|].
      destruct Hcap as [(C0 & _)|(Cp & Hl)]; [lia|]. split; [exact Hl|].
      rewrite ED. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left. reflexivity. }
    split.
    { intros i Hi. destruct (pj_items_nth _ items kp Di i HI Hi) as (Dx & Hinc & HP).
      exists Dx. split; [|exact HP]. intros b Hb. rewrite ED. apply in_or_app. right. apply Hinc. exact Hb. }
    intros ms i E. discriminate E.
  - cbn [pj_node] in H. destruct H as (_ & _ & num & str & kp & yp & n & cap & Hh & Hb).
    destruct Hh as (_ & HT & _ & _ & HK & HY & HN & _).
    destruct Hb as (_ & En & Hnc & Hcap & Di & ED & HM).
    exists kp, yp, n. unfold coll_facts. cbn [tag kids]. rewrite length_map.
    split; [exact HT|]. split; [exact HK|]. split; [exact HY|]. split; [exact HN|]. split; [exact En|].
    split.
    { intros Hn. exists cap. split; [lia|].
      destruct Hcap as [(C0 & _)|(Cp & Hl & _)]; [lia|]. split; [exact Hl|].
      rewrite ED. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left. reflexivity. }
    split.
    { intros i Hi. destruct (pj_mems_nth m lblk _ ms kp yp Di i HM Hi) as (x & k & Dx & _ & Hinc & _ & _ & HP).
      exists Dx. split.
      - intros b Hb. rewrite ED. apply in_or_app. right. apply Hinc. exact Hb.
      - rewrite nth_kids_obj. exact HP. }
    intros ms' i E Hi. injection E as <-.
    destruct (pj_mems_nth m lblk _ ms kp yp Di i HM Hi) as (x & k & Dx & Hin & _ & Hx & Hc & _).
    exists x, k. split; [rewrite ED; apply in_or_app; right; exact Hin|]. split; [exact Hx|]. split; [exact Hc|].
    exists cap. split; [lia|].
    destruct Hcap as [(C0 & _)|(Cp & _ & Hl)]; [lia|]. split; [exact Hl|].
    rewrite ED. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. right. left. reflexivity.
Qed.

End P.
