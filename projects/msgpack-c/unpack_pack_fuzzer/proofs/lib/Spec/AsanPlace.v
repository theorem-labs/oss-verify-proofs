(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import MState.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import AsanInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Fixpoint zsizes (l : list (Z * Z)) : Z := match l with [] => 0 | e :: l' => snd e + zsizes l' end.

Lemma zsizes_app : forall l1 l2, zsizes (l1 ++ l2) = zsizes l1 + zsizes l2.
Proof. induction l1 as [|e l1 IH]; intros; cbn; [reflexivity| rewrite IH; lia]. Qed.

Lemma zargmin : forall (l : list (Z * Z)), l <> [] -> exists e, In e l /\ forall e', In e' l -> fst e <= fst e'.
Proof.
  induction l as [|e l IH]; intros Hne; [congruence|].
  destruct l as [|e2 l2].
  - exists e. split; [left; reflexivity|]. intros e' [<-|[]]. lia.
  - destruct (IH ltac:(discriminate)) as (m & Hm & Hmin).
    destruct (Z_le_gt_dec (fst e) (fst m)).
    + exists e. split; [left; reflexivity|]. intros e' [<-|Hin]; [lia|]. specialize (Hmin e' Hin). lia.
    + exists m. split; [right; exact Hm|]. intros e' [<-|Hin]; [lia|]. apply Hmin. exact Hin.
Qed.

Definition pgup (x : Z) : Z := (x + 4095) / 4096 * 4096.
Lemma pgup_facts : forall x, pgup x mod 4096 = 0 /\ x <= pgup x <= x + 4095.
Proof. intros x. unfold pgup. split; [apply Z_mod_mult|]. Z.div_mod_to_equations. lia. Qed.

Lemma free_gap : forall (n : nat) (l : list (Z * Z)) (lo hi G : Z),
  length l = n -> 0 <= G -> Forall (fun e => 0 <= snd e) l ->
  (hi - lo) - zsizes l >= (Z.of_nat n + 1) * (G + 4095) ->
  exists g, g mod 4096 = 0 /\ lo <= g /\ g + G <= hi /\ Forall (fun e => g + G <= fst e \/ fst e + snd e <= g) l.
Proof.
  induction n as [|n IH]; intros l lo hi G Hlen HG Hpos Hroom.
  - destruct l; [|discriminate]. cbn [zsizes] in Hroom.
    exists (pgup lo). pose proof (pgup_facts lo) as [HM HR].
    split; [exact HM|]. split; [lia|]. split; [lia| constructor].
  - destruct l as [|e0 l0]; [discriminate|].
    destruct (zargmin (e0 :: l0) ltac:(discriminate)) as (m & Hm & Hmin).
    apply in_split in Hm as (l1 & l2 & El). rewrite El in *.
    assert (Hlen' : length (l1 ++ l2) = n) by (rewrite length_app in *; cbn in Hlen; lia).
    assert (Hpos' : Forall (fun e => 0 <= snd e) (l1 ++ l2)).
    { apply Forall_app in Hpos as [P1 P2]. apply Forall_cons_iff in P2 as [_ P2]. apply Forall_app. split; assumption. }
    assert (Hm0 : 0 <= snd m). { apply Forall_app in Hpos as [_ P2]. apply Forall_cons_iff in P2 as [P _]. exact P. }
    rewrite zsizes_app in Hroom. cbn [zsizes] in Hroom.
    destruct (Z_le_gt_dec (lo + G + 4095) (fst m)) as [Hfar|Hnear].
    +
      exists (pgup lo). pose proof (pgup_facts lo) as [HM HR].
      split; [exact HM|]. split; [lia|].
      assert (ZS : 0 <= zsizes l1 /\ 0 <= zsizes l2).
      { apply Forall_app in Hpos' as [P1 P2]. split; [clear -P1; induction l1 as [|x l1 IH1]| clear -P2; induction l2 as [|x l2 IH1]]; cbn; try lia;
          match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H as [Hx H]; specialize (IH1 H); lia end. }
      split; [nia|].
      rewrite Forall_forall. intros e' He'. left. specialize (Hmin e' He'). lia.
    +
      set (lo' := Z.max lo (fst m + snd m)).
      destruct (IH (l1 ++ l2) lo' hi G Hlen' HG Hpos') as (g & G1 & G2 & G3 & G4).
      { subst lo'. rewrite zsizes_app. nia. }
      exists g. split; [exact G1|]. split; [lia|]. split; [exact G3|].
      apply Forall_app in G4 as [G4a G4b]. apply Forall_app. split; [exact G4a|]. constructor; [|exact G4b].
      right. lia.
Qed.

Definition meets (lo hi : Z) (e : Z * Z) : bool := (fst e <? hi) && (lo <? fst e + snd e).

Lemma free_gap_filter : forall (l : list (Z * Z)) (lo hi G N T : Z),
  0 <= G -> Forall (fun e => 0 <= snd e) l ->
  Z.of_nat (length (List.filter (meets lo hi) l)) <= N -> zsizes (List.filter (meets lo hi) l) <= T ->
  0 <= N -> (hi - lo) - T >= (N + 1) * (G + 4095) ->
  exists g, g mod 4096 = 0 /\ lo <= g /\ g + G <= hi /\ Forall (fun e => g + G <= fst e \/ fst e + snd e <= g) l.
Proof.
  intros l lo hi G N T HG Hpos HN HT HN0 Hroom.
  destruct (free_gap (length (List.filter (meets lo hi) l)) (List.filter (meets lo hi) l) lo hi G eq_refl HG) as (g & G1 & G2 & G3 & G4).
  - apply Forall_forall. intros e He. apply filter_In in He as [He _]. exact (proj1 (Forall_forall _ _) Hpos e He).
  - nia.
  - exists g. split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
    apply Forall_forall. intros e He.
    destruct (meets lo hi e) eqn:Em.
    + apply (proj1 (Forall_forall _ _) G4). apply filter_In. split; assumption.
    + unfold meets in Em. apply andb_false_iff in Em as [Em|Em]; [apply Z.ltb_ge in Em; left| apply Z.ltb_ge in Em; right]; lia.
Qed.

Definition zent (e : word * word) : Z * Z := (bv_unsigned (fst e), bv_unsigned (snd e)).

Lemma region_free_of_clear : forall (maps : list (word * word)) (g G : Z),
  0 <= g -> 0 <= G -> g + G < 2^64 ->
  Forall (fun e => g + G <= fst e \/ fst e + snd e <= g) (map zent maps) ->
  region_free maps (Z_to_bv 64 g) (Z_to_bv 64 G) = true.
Proof.
  induction maps as [|[a sz] maps IH]; intros g G Hg HG Hhi HF; [reflexivity|].
  cbn [map zent fst snd] in HF. apply Forall_cons_iff in HF as [H1 HF].
  cbn [region_free]. rewrite (IH g G Hg HG Hhi HF), andb_true_r.
  unfold iv_overlap. rewrite !unsigned_lit by lia. unfold zent in H1. cbn [fst snd] in H1.
  apply negb_true_iff. apply andb_false_iff.
  destruct H1 as [H1|H1]; [right| left]; apply Z.ltb_ge; lia.
Qed.

