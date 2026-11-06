(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec ArtMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Inductive ashape : Set := Sh_bare | Sh_off (o : Z) | Sh_off2 (o1 o2 : Z).
Definition aval (B : Z) (s : ashape) : Z := match s with Sh_bare => B | Sh_off o => B + o | Sh_off2 o1 o2 => B + o1 + o2 end.
Definition aoff (s : ashape) : Z := match s with Sh_bare => 0 | Sh_off o => o | Sh_off2 o1 o2 => o1 + o2 end.
Lemma aval_off : forall B s, aval B s = B + aoff s.
Proof. intros B [|o|o1 o2]; cbn [aval aoff]; lia. Qed.

Record hull : Set := mkhull { hB : Z; hlo : Z; hhi : Z }.
Definition hull0 : hull := mkhull 0 0 0.
Definition hbase (env : list hull) (j : nat) : Z := hB (nth j env hull0).
Inductive wkind : Set := WKn (n : nat) (v : Z) | WKf (k : nat) (b : Z).
Definition wsize (k : wkind) : nat := match k with WKn n _ => n | WKf k _ => k end.
Record wlayer : Set := mkwl { wlj : nat; wls : ashape; wlk : wkind }.

Fixpoint wstk (env : list hull) (M0 : word -> option byte) (l : list wlayer) : word -> option byte :=
  match l with
  | [] => M0
  | ly :: l' =>
      match wlk ly with
      | WKn n v => Wn n (wstk env M0 l') (aval (hbase env (wlj ly)) (wls ly)) v
      | WKf k b => Wf (wstk env M0 l') (aval (hbase env (wlj ly)) (wls ly)) k b
      end
  end.

Definition lay_ok (env : list hull) (ob mz : Z) (ly : wlayer) : bool :=
  let h := nth (wlj ly) env hull0 in let o := aoff (wls ly) in let n := Z.of_nat (wsize (wlk ly)) in
  (wlj ly <? length env)%nat && (hlo h <=? o) && (o + n <=? hhi h)
  && (match wlj ly with O => (o + n <=? ob) || (ob + mz <=? o) | S _ => true end).
Definition stk_chk (env : list hull) (sb : ashape) (m : nat) (mz : Z) (l : list wlayer) : bool :=
  (mz =? Z.of_nat m) && (hlo (nth 0 env hull0) <=? aoff sb) && (aoff sb + mz <=? hhi (nth 0 env hull0)) && forallb (lay_ok env (aoff sb) mz) l.

Definition hull_rng (h : hull) : Prop := 0 <= hB h + hlo h /\ hB h + hhi h < 2 ^ 64.
Fixpoint env_oth (env : list hull) (b mz : Z) : Prop :=
  match env with
  | [] => True
  | h :: env' => (hull_rng h /\ (b + mz <= hB h + hlo h \/ hB h + hhi h <= b)) /\ env_oth env' b mz
  end.
Definition env_ok (env : list hull) (b mz : Z) : Prop :=
  match env with [] => False | h :: env' => hull_rng h /\ env_oth env' b mz end.
Lemma env_ok_intro : forall B lo hi env b mz, 0 <= B + lo -> B + hi < 2 ^ 64 -> env_oth env b mz -> env_ok (mkhull B lo hi :: env) b mz.
Proof. intros. split; [split; assumption | assumption]. Qed.
Lemma env_oth_nil : forall b mz, env_oth [] b mz.
Proof. intros. exact I. Qed.
Lemma env_oth_cons : forall B lo hi env b mz, 0 <= B + lo -> B + hi < 2 ^ 64 -> (b + mz <= B + lo \/ B + hi <= b) -> env_oth env b mz ->
  env_oth (mkhull B lo hi :: env) b mz.
Proof. intros. split; [split; [split; assumption | assumption] | assumption]. Qed.

Lemma env_oth_nth : forall env b mz j, env_oth env b mz -> (j < length env)%nat ->
  hull_rng (nth j env hull0) /\ (b + mz <= hB (nth j env hull0) + hlo (nth j env hull0) \/ hB (nth j env hull0) + hhi (nth j env hull0) <= b).
Proof.
  induction env as [|h env IH]; intros b mz j H Hj; [cbn in Hj; lia|].
  destruct H as [H1 H2]. destruct j as [|j]; [exact H1 | apply IH; [exact H2 | cbn in Hj; lia]].
Qed.

Inductive slayer : Set := SLn (n : nat) (a v : Z) | SLf (a : Z) (k : nat) (b : Z).
Fixpoint sstk (M0 : word -> option byte) (l : list slayer) : word -> option byte :=
  match l with
  | [] => M0
  | SLn n a v :: l' => Wn n (sstk M0 l') a v
  | SLf a k b :: l' => Wf (sstk M0 l') a k b
  end.

Section WithSegs.
Variable segs : list Segment.

Lemma wok_sstk : forall M0 l b m, wok segs M0 b m -> wok segs (sstk M0 l) b m.
Proof.
  intros M0 l b m H. induction l as [|[n a v|a k bb] l IH]; [exact H | |]; cbn [sstk]; [apply wok_Wn | apply wok_Wf]; exact IH.
Qed.
Lemma wr_sstk : forall M0 l b m, wr segs M0 b m -> wr segs (sstk M0 l) b m.
Proof.
  intros M0 l b m H. induction l as [|[n a v|a k bb] l IH]; [exact H | |]; cbn [sstk]; [apply wr_Wn | apply wr_Wf]; exact IH.
Qed.

Lemma cell_wstk_other : forall env M0 l b sb m mz u,
  b = aval (hbase env 0) sb -> env_ok env b mz -> stk_chk env sb m mz l = true ->
  cell segs M0 b m u -> cell segs (wstk env M0 l) b m u.
Proof.
  intros env M0 l b sb m mz u Eb0 HE HC H.
  unfold stk_chk in HC.
  apply andb_prop in HC. destruct HC as [HC HL]. apply andb_prop in HC. destruct HC as [HC Hb2]. apply andb_prop in HC. destruct HC as [Hmz Hb1].
  apply Z.eqb_eq in Hmz. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
  destruct env as [|h0 env']; [destruct HE|]. destruct HE as [[Rb1 Rb2] HO].
  assert (Eb : b = hB h0 + aoff sb) by (rewrite Eb0; unfold hbase; cbn [nth]; apply aval_off).
  cbn [nth] in Hb1, Hb2.
  induction l as [|ly l IH]; [exact H|].
  cbn [forallb] in HL. apply andb_prop in HL. destruct HL as [Hly HL]. specialize (IH HL).
  unfold lay_ok in Hly. cbn zeta in Hly.
  apply andb_prop in Hly. destruct Hly as [Hly Hsb]. apply andb_prop in Hly. destruct Hly as [Hly Ho2]. apply andb_prop in Hly. destruct Hly as [Hj Ho1].
  apply Nat.ltb_lt in Hj. apply Z.leb_le in Ho1. apply Z.leb_le in Ho2.
  assert (Ea : aval (hbase (h0 :: env') (wlj ly)) (wls ly) = hB (nth (wlj ly) (h0 :: env') hull0) + aoff (wls ly)) by (unfold hbase; apply aval_off).
  assert (RA : 0 <= hB (nth (wlj ly) (h0 :: env') hull0) + hlo (nth (wlj ly) (h0 :: env') hull0)
               /\ hB (nth (wlj ly) (h0 :: env') hull0) + hhi (nth (wlj ly) (h0 :: env') hull0) < 2 ^ 64
               /\ apart (aval (hbase (h0 :: env') (wlj ly)) (wls ly)) (Z.of_nat (wsize (wlk ly))) b (Z.of_nat m)).
  { unfold apart. rewrite Ea. destruct (wlj ly) as [|j] eqn:Ej.
    - cbn [nth] in *. split; [exact Rb1|]. split; [exact Rb2|]. rewrite Eb. apply orb_prop in Hsb. destruct Hsb as [Hs|Hs]; apply Z.leb_le in Hs; lia.
    - cbn [nth] in *. cbn [length] in Hj. destruct (env_oth_nth env' b mz j HO ltac:(lia)) as [[R1 R2] R3]. split; [exact R1|]. split; [exact R2|]. lia. }
  destruct RA as (R1 & R2 & AP).
  cbn [wstk]. destruct (wlk ly) as [n v|k bb]; cbn [wsize] in *.
  - apply cell_Wn_other; [lia | lia | lia | lia | exact AP | exact IH].
  - apply cell_Wf_other; [lia | lia | lia | lia | exact AP | exact IH].
Qed.
End WithSegs.
