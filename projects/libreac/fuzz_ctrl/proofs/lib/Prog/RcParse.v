From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind.
Import ListNotations.
Open Scope Z_scope.

Definition cp_z : byte := Z_to_bv 8 0.
Definition cp_b (fr : list byte) (i : nat) : byte := nth i fr cp_z.
Definition cp_v (fr : list byte) (i : nat) : Z := bv_unsigned (cp_b fr i).

Definition cp_hdr (n : Z) (fr : list byte) : bool :=
  (50 <=? n) && (cp_v fr 12 =? 0x88) && (cp_v fr 13 =? 0x19).

Definition cp_type (fr : list byte) (x y : Z) : bool := (cp_v fr 16 =? x) && (cp_v fr 17 =? y).

Definition cp_rec (fr : list byte) : bool :=
  cp_type fr 0xcd 0xea && (cp_v fr 18 =? 4) && (cp_v fr 19 =? 3).

Definition cp_amp (fr : list byte) : bool :=
  (cp_v fr 32 =? 0x12) && (cp_v fr 33 =? 0x12) && (cp_v fr 34 =? 1) && (cp_v fr 35 =? 1).

Definition cp_kind (fr : list byte) : Z :=
  if cp_type fr 0 0 then 1
  else if cp_type fr 0xcf 0xea then 4
  else if cp_type fr 0xce 0xea then 8
  else if negb (cp_type fr 0xcd 0xea) then 13
  else if cp_v fr 18 =? 1 then KL1 (cp_v fr 22)
  else if cp_v fr 18 =? 2 then 12
  else if cp_v fr 18 =? 4 then (if negb (cp_v fr 19 =? 3) then 11 else if cp_amp fr then 6 else 5)
  else 13.

Definition cp_bcast (fr : list byte) : bool :=
  forallb (fun b => bv_unsigned b =? 0xff) [cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3; cp_b fr 4; cp_b fr 5].

Definition cp_struct (fr : list byte) (k : Z) : list byte :=
  [Z_to_bv 8 k; cp_z; cp_z; cp_z;
   cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9; cp_b fr 10; cp_b fr 11;
   cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3; cp_b fr 4; cp_b fr 5;
   (if cp_bcast fr then Z_to_bv 8 1 else cp_z); cp_z; cp_z; cp_z;
   cp_b fr 14; cp_b fr 15; cp_b fr 18; cp_b fr 19; cp_b fr 21; cp_b fr 20; cp_b fr 22; cp_z]
  ++ (if cp_rec fr then [cp_b fr 35; cp_b fr 34] else [cp_z; cp_z])
  ++ (if k =? 6 then [cp_b fr 36; cp_b fr 37; cp_b fr 38] else [cp_z; cp_z; cp_z])
  ++ [cp_z; cp_z; cp_z].

Definition ctrlparse (n : Z) (fr : list byte) : Z * list byte :=
  if cp_hdr n fr then (cp_kind fr, cp_struct fr (cp_kind fr)) else (0, repeat cp_z 36).

Definition cp_rd (n : Z) (fr : list byte) : list nat :=
  if negb (50 <=? n) then []
  else if negb (cp_v fr 12 =? 0x88) then [12%nat]
  else if negb (cp_v fr 13 =? 0x19) then [12%nat; 13%nat]
  else seq 0 23 ++
       (if cp_rec fr then
          [32%nat; 34%nat; 35%nat] ++ (if cp_v fr 32 =? 0x12 then [33%nat] else []) ++
          (if cp_kind fr =? 6 then [36%nat; 37%nat; 38%nat] else [])
        else []).

Lemma KL1_range : forall x, 2 <= KL1 x <= 13 /\ KL1 x <> 4 /\ KL1 x <> 5 /\ KL1 x <> 6 /\ KL1 x <> 8 /\
  KL1 x <> 11 /\ KL1 x <> 12.
Proof.
  intros x. unfold KL1.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia.
Qed.

Lemma cp_kind_range : forall fr, 1 <= cp_kind fr <= 13.
Proof.
  intros fr. unfold cp_kind. pose proof (KL1_range (cp_v fr 22)).
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn [negb]; lia.
Qed.

Lemma ctrlparse_kind_range : forall n fr, 0 <= fst (ctrlparse n fr) <= 13.
Proof.
  intros n fr. unfold ctrlparse. pose proof (cp_kind_range fr).
  destruct (cp_hdr n fr); cbn [fst]; lia.
Qed.

Lemma ctrlparse_length : forall n fr, length (snd (ctrlparse n fr)) = 36%nat.
Proof.
  intros n fr. unfold ctrlparse, cp_struct.
  destruct (cp_hdr n fr); cbn [snd]; [|reflexivity].
  destruct (cp_rec fr), (cp_kind fr =? 6); reflexivity.
Qed.

Lemma cp_hdr_spec : forall n fr,
  cp_hdr n fr = true <-> 50 <= n /\ cp_v fr 12 = 0x88 /\ cp_v fr 13 = 0x19.
Proof.
  intros n fr. unfold cp_hdr. rewrite !andb_true_iff, Z.leb_le, !Z.eqb_eq. tauto.
Qed.

Lemma ctrlparse_none : forall n fr,
  fst (ctrlparse n fr) = 0 <-> ~ (50 <= n /\ cp_v fr 12 = 0x88 /\ cp_v fr 13 = 0x19).
Proof.
  intros n fr. rewrite <- cp_hdr_spec. unfold ctrlparse. pose proof (cp_kind_range fr).
  destruct (cp_hdr n fr); cbn [fst]; split; intros H'; try lia; try congruence.
Qed.

Lemma ctrlparse_bytes_none : forall n fr, cp_hdr n fr = false -> snd (ctrlparse n fr) = repeat cp_z 36.
Proof. intros n fr H. unfold ctrlparse. rewrite H. reflexivity. Qed.

Lemma ctrlparse_filler : forall n fr,
  fst (ctrlparse n fr) = 1 <-> cp_hdr n fr = true /\ cp_v fr 16 = 0 /\ cp_v fr 17 = 0.
Proof.
  intros n fr. unfold ctrlparse. destruct (cp_hdr n fr); cbn [fst].
  - unfold cp_kind, cp_type. pose proof (KL1_range (cp_v fr 22)) as KR.
    destruct (Z.eqb_spec (cp_v fr 16) 0) as [E16|E16], (Z.eqb_spec (cp_v fr 17) 0) as [E17|E17]; cbn [andb negb].
    + split; intros; [repeat split; assumption | reflexivity].
    + split; [|intros (_ & _ & X); congruence].
      repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn [negb]; intros X; exfalso; lia.
    + split; [|intros (_ & X & _); congruence].
      repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn [negb]; intros X; exfalso; lia.
    + split; [|intros (_ & X & _); congruence].
      repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn [negb]; intros X; exfalso; lia.
  - split; [lia|]. intros [H _]. discriminate.
Qed.

Lemma ctrlparse_kind_bytes : forall n fr,
  firstn 4 (snd (ctrlparse n fr)) = [Z_to_bv 8 (fst (ctrlparse n fr)); cp_z; cp_z; cp_z].
Proof.
  intros n fr. unfold ctrlparse. destruct (cp_hdr n fr); reflexivity.
Qed.

Lemma ctrlparse_fields : forall n fr, fst (ctrlparse n fr) <> 0 ->
  let B := snd (ctrlparse n fr) in
  (forall j, (j < 6)%nat -> nth (4 + j) B cp_z = cp_b fr (6 + j)) /\
  (forall j, (j < 6)%nat -> nth (10 + j) B cp_z = cp_b fr j) /\
  firstn 4 (skipn 16 B) = [if cp_bcast fr then Z_to_bv 8 1 else cp_z; cp_z; cp_z; cp_z] /\
  nth 20 B cp_z = cp_b fr 14 /\ nth 21 B cp_z = cp_b fr 15 /\
  nth 22 B cp_z = cp_b fr 18 /\ nth 23 B cp_z = cp_b fr 19 /\
  nth 24 B cp_z = cp_b fr 21 /\ nth 25 B cp_z = cp_b fr 20 /\
  nth 26 B cp_z = cp_b fr 22 /\
  nth 27 B cp_z = cp_z /\ nth 33 B cp_z = cp_z /\ nth 34 B cp_z = cp_z /\ nth 35 B cp_z = cp_z.
Proof.
  intros n fr Hk B. subst B. unfold ctrlparse in *. destruct (cp_hdr n fr); cbn [fst] in Hk; [|lia].
  cbn [snd]. unfold cp_struct.
  split; [intros j Hj; do 6 (destruct j as [|j]; [reflexivity|]); lia|].
  split; [intros j Hj; do 6 (destruct j as [|j]; [reflexivity|]); lia|].
  destruct (cp_rec fr), (cp_kind fr =? 6); repeat split.
Qed.

Lemma ctrlparse_rec : forall n fr, fst (ctrlparse n fr) = 5 \/ fst (ctrlparse n fr) = 6 ->
  cp_hdr n fr = true /\ cp_rec fr = true /\
  nth 28 (snd (ctrlparse n fr)) cp_z = cp_b fr 35 /\ nth 29 (snd (ctrlparse n fr)) cp_z = cp_b fr 34.
Proof.
  intros n fr Hk. unfold ctrlparse in *. destruct (cp_hdr n fr) eqn:Eh; cbn [fst] in Hk; [|lia].
  assert (R : cp_rec fr = true).
  { unfold cp_kind, cp_rec in *. pose proof (KL1_range (cp_v fr 22)).
    destruct (cp_type fr 0 0); [lia|]. destruct (cp_type fr 0xcf 0xea); [lia|].
    destruct (cp_type fr 0xce 0xea); [lia|]. destruct (cp_type fr 0xcd 0xea); cbn [negb] in Hk; [|lia].
    destruct (cp_v fr 18 =? 1); [lia|]. destruct (cp_v fr 18 =? 2); [lia|].
    destruct (cp_v fr 18 =? 4); [|lia]. destruct (cp_v fr 19 =? 3); cbn [negb] in Hk; [|lia].
    reflexivity. }
  cbn [snd]. unfold cp_struct. rewrite R. repeat split; assumption.
Qed.

Lemma ctrlparse_headamp : forall n fr,
  fst (ctrlparse n fr) = 6 <-> cp_hdr n fr = true /\ cp_rec fr = true /\ cp_amp fr = true.
Proof.
  intros n fr. unfold ctrlparse. destruct (cp_hdr n fr); cbn [fst]; [|split; [lia|intros [H _]; discriminate]].
  unfold cp_kind, cp_rec. pose proof (KL1_range (cp_v fr 22)) as KR.
  destruct (cp_type fr 0 0) eqn:T0.
  { split; [lia|]. intros (_ & H & _). unfold cp_type in *. rewrite !andb_true_iff, !Z.eqb_eq in H, T0. lia. }
  destruct (cp_type fr 0xcf 0xea) eqn:T1.
  { split; [lia|]. intros (_ & H & _). unfold cp_type in *. rewrite !andb_true_iff, !Z.eqb_eq in H, T1. lia. }
  destruct (cp_type fr 0xce 0xea) eqn:T2.
  { split; [lia|]. intros (_ & H & _). unfold cp_type in *. rewrite !andb_true_iff, !Z.eqb_eq in H, T2. lia. }
  destruct (cp_type fr 0xcd 0xea); cbn [negb andb]; [|split; [lia|intros (_ & H & _); discriminate]].
  destruct (Z.eqb_spec (cp_v fr 18) 1); [split; [lia|intros (_ & H & _); rewrite !andb_true_iff, !Z.eqb_eq in H; lia]|].
  destruct (Z.eqb_spec (cp_v fr 18) 2); [split; [lia|intros (_ & H & _); rewrite !andb_true_iff, !Z.eqb_eq in H; lia]|].
  destruct (Z.eqb_spec (cp_v fr 18) 4); cbn [andb]; [|split; [lia|intros (_ & H & _); discriminate]].
  destruct (cp_v fr 19 =? 3); cbn [negb]; [|split; [lia|intros (_ & H & _); discriminate]].
  destruct (cp_amp fr); split; intros HH; try (repeat split; reflexivity); try lia;
    destruct HH as (_ & _ & HH); discriminate.
Qed.

Lemma ctrlparse_link1 : forall n fr k, k = 2 \/ k = 7 \/ k = 9 \/ k = 10 \/ k = 3 ->
  fst (ctrlparse n fr) = k <->
  cp_hdr n fr = true /\ cp_type fr 0xcd 0xea = true /\ cp_v fr 18 = 1 /\ KL1 (cp_v fr 22) = k.
Proof.
  intros n fr k Hk. unfold ctrlparse. destruct (cp_hdr n fr); cbn [fst];
    [|split; [lia|intros [H _]; discriminate]].
  unfold cp_kind. pose proof (KL1_range (cp_v fr 22)) as KR.
  assert (TD : forall x y, cp_type fr x y = true -> cp_type fr 0xcd 0xea = true -> x = 0xcd /\ y = 0xea).
  { intros x y A B. unfold cp_type in *. apply andb_true_iff in A as [A1 A2]. apply andb_true_iff in B as [B1 B2].
    apply Z.eqb_eq in A1, A2, B1, B2. lia. }
  destruct (cp_type fr 0 0) eqn:T0; [split; [lia|intros (_ & H & _); destruct (TD _ _ T0 H); lia]|].
  destruct (cp_type fr 0xcf 0xea) eqn:T1; [split; [lia|intros (_ & H & _); destruct (TD _ _ T1 H); lia]|].
  destruct (cp_type fr 0xce 0xea) eqn:T2; [split; [lia|intros (_ & H & _); destruct (TD _ _ T2 H); lia]|].
  destruct (cp_type fr 0xcd 0xea); cbn [negb]; [|split; [lia|intros (_ & H & _); discriminate]].
  destruct (Z.eqb_spec (cp_v fr 18) 1); [split; [intros K; repeat split; assumption|intros (_ & _ & _ & K); exact K]|].
  split; [|intros (_ & _ & H & _); lia].
  destruct (cp_v fr 18 =? 2); [lia|]. destruct (cp_v fr 18 =? 4); [|lia].
  destruct (cp_v fr 19 =? 3); cbn [negb]; [|lia]. destruct (cp_amp fr); lia.
Qed.

Lemma cp_rd_lt39 : forall n fr i, In i (cp_rd n fr) -> (i < 39)%nat.
Proof.
  intros n fr i H. unfold cp_rd in H.
  destruct (50 <=? n); cbn [negb] in H; [|destruct H].
  destruct (cp_v fr 12 =? 0x88); cbn [negb] in H; [|destruct H as [<-|[]]; lia].
  destruct (cp_v fr 13 =? 0x19); cbn [negb] in H; [|destruct H as [<-|[<-|[]]]; lia].
  apply in_app_or in H. destruct H as [H|H]; [apply in_seq in H; lia|].
  destruct (cp_rec fr); [|destruct H].
  apply in_app_or in H. destruct H as [H|H]; [destruct H as [<-|[<-|[<-|[]]]]; lia|].
  apply in_app_or in H. destruct H as [H|H].
  - destruct (cp_v fr 32 =? 0x12); [destruct H as [<-|[]]; lia|destruct H].
  - destruct (cp_kind fr =? 6); [destruct H as [<-|[<-|[<-|[]]]]; lia|destruct H].
Qed.

Lemma cp_rd_12 : forall n fr, 50 <= n -> In 12%nat (cp_rd n fr).
Proof.
  intros n fr Hn. unfold cp_rd. rewrite (proj2 (Z.leb_le 50 n) Hn). cbn [negb].
  destruct (cp_v fr 12 =? 0x88); cbn [negb]; [|left; reflexivity].
  destruct (cp_v fr 13 =? 0x19); cbn [negb]; [|left; reflexivity].
  apply in_or_app. left. apply in_seq. lia.
Qed.

Lemma cp_rd_13 : forall n fr, 50 <= n -> cp_v fr 12 = 0x88 -> In 13%nat (cp_rd n fr).
Proof.
  intros n fr Hn H12. unfold cp_rd. rewrite (proj2 (Z.leb_le 50 n) Hn), H12. cbn [negb Z.eqb Pos.eqb].
  destruct (cp_v fr 13 =? 0x19); cbn [negb]; [|right; left; reflexivity].
  apply in_or_app. left. apply in_seq. lia.
Qed.

Lemma cp_rd_e : forall n fr i, cp_hdr n fr = true -> (i < 23)%nat -> In i (cp_rd n fr).
Proof.
  intros n fr i H Hi. apply cp_hdr_spec in H as (Hn & H12 & H13). unfold cp_rd.
  rewrite (proj2 (Z.leb_le 50 n) Hn), H12, H13. cbn [negb Z.eqb Pos.eqb].
  apply in_or_app. left. apply in_seq. lia.
Qed.

Lemma cp_rd_rec : forall n fr i, cp_hdr n fr = true -> cp_rec fr = true ->
  (i = 32 \/ i = 34 \/ i = 35)%nat -> In i (cp_rd n fr).
Proof.
  intros n fr i H R Hi. apply cp_hdr_spec in H as (Hn & H12 & H13). unfold cp_rd.
  rewrite (proj2 (Z.leb_le 50 n) Hn), H12, H13, R. cbn [negb Z.eqb Pos.eqb].
  apply in_or_app. right. apply in_or_app. left. cbn. lia.
Qed.

Lemma cp_rd_33 : forall n fr, cp_hdr n fr = true -> cp_rec fr = true -> cp_v fr 32 = 0x12 ->
  In 33%nat (cp_rd n fr).
Proof.
  intros n fr H R H32. apply cp_hdr_spec in H as (Hn & H12 & H13). unfold cp_rd.
  rewrite (proj2 (Z.leb_le 50 n) Hn), H12, H13, R, H32. cbn [negb Z.eqb Pos.eqb].
  apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. left. reflexivity.
Qed.

Lemma cp_rd_amp : forall n fr i, cp_hdr n fr = true -> cp_rec fr = true -> cp_kind fr = 6 ->
  (i = 36 \/ i = 37 \/ i = 38)%nat -> In i (cp_rd n fr).
Proof.
  intros n fr i H R K Hi. apply cp_hdr_spec in H as (Hn & H12 & H13). unfold cp_rd.
  rewrite (proj2 (Z.leb_le 50 n) Hn), H12, H13, R, K. cbn [negb Z.eqb Pos.eqb].
  apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. cbn. lia.
Qed.

Lemma ctrlparse_rd_dep : forall n fr fr',
  (forall i, In i (cp_rd n fr) -> cp_b fr i = cp_b fr' i) ->
  ctrlparse n fr = ctrlparse n fr' /\ cp_rd n fr = cp_rd n fr'.
Proof.
  intros n fr fr' H.
  assert (V : forall i, In i (cp_rd n fr) -> cp_v fr i = cp_v fr' i) by (intros i Hi; unfold cp_v; rewrite (H i Hi); reflexivity).
  destruct (Z.leb_spec 50 n) as [Hn|Hn].
  2:{ unfold ctrlparse, cp_rd, cp_hdr. rewrite (proj2 (Z.leb_gt 50 n) Hn). split; reflexivity. }
  pose proof (V 12%nat (cp_rd_12 n fr Hn)) as V12.
  destruct (Z.eqb_spec (cp_v fr 12) 0x88) as [E12|E12].
  2:{ unfold ctrlparse, cp_rd, cp_hdr. rewrite <- V12. rewrite (proj2 (Z.eqb_neq _ _) E12).
      rewrite !andb_false_r. cbn [andb negb]. split; reflexivity. }
  pose proof (V 13%nat (cp_rd_13 n fr Hn E12)) as V13.
  destruct (Z.eqb_spec (cp_v fr 13) 0x19) as [E13|E13].
  2:{ unfold ctrlparse, cp_rd, cp_hdr. rewrite <- V12, <- V13. rewrite (proj2 (Z.eqb_neq _ _) E13).
      rewrite !andb_false_r. cbn [andb negb]. split; reflexivity. }
  assert (HD : cp_hdr n fr = true) by (apply cp_hdr_spec; tauto).
  assert (HD' : cp_hdr n fr' = true) by (apply cp_hdr_spec; rewrite <- V12, <- V13; tauto).
  assert (B : forall i, (i < 23)%nat -> cp_b fr i = cp_b fr' i) by (intros i Hi; apply H, cp_rd_e; assumption).
  assert (RC : cp_rec fr = cp_rec fr').
  { unfold cp_rec, cp_type, cp_v. rewrite !B by lia. reflexivity. }
  assert (BC : cp_bcast fr = cp_bcast fr') by (unfold cp_bcast; rewrite !B by lia; reflexivity).
  assert (KE : cp_kind fr = cp_kind fr' /\ (cp_rec fr = true -> cp_v fr 32 = cp_v fr' 32 /\
            cp_v fr 34 = cp_v fr' 34 /\ cp_v fr 35 = cp_v fr' 35 /\
            (cp_v fr 32 = 0x12 -> cp_v fr 33 = cp_v fr' 33))).
  { assert (RX : cp_rec fr = true -> cp_v fr 32 = cp_v fr' 32 /\ cp_v fr 34 = cp_v fr' 34 /\
              cp_v fr 35 = cp_v fr' 35 /\ (cp_v fr 32 = 0x12 -> cp_v fr 33 = cp_v fr' 33)).
    { intros R. split; [apply V, cp_rd_rec; tauto|]. split; [apply V, cp_rd_rec; tauto|].
      split; [apply V, cp_rd_rec; tauto|]. intros H32. apply V, cp_rd_33; assumption. }
    split; [|exact RX].
    unfold cp_kind. unfold cp_type, cp_v at 1 2 3 4 5 6 7 8. rewrite !B by lia. fold (cp_v fr' 16) (cp_v fr' 17).
    assert (B18 : cp_v fr 18 = cp_v fr' 18) by (unfold cp_v; rewrite B by lia; reflexivity).
    assert (B19 : cp_v fr 19 = cp_v fr' 19) by (unfold cp_v; rewrite B by lia; reflexivity).
    assert (B22 : cp_v fr 22 = cp_v fr' 22) by (unfold cp_v; rewrite B by lia; reflexivity).
    rewrite B18, B19, B22.
    destruct ((cp_v fr' 16 =? 0) && (cp_v fr' 17 =? 0)); [reflexivity|].
    destruct ((cp_v fr' 16 =? 207) && (cp_v fr' 17 =? 234)); [reflexivity|].
    destruct ((cp_v fr' 16 =? 206) && (cp_v fr' 17 =? 234)); [reflexivity|].
    destruct ((cp_v fr' 16 =? 205) && (cp_v fr' 17 =? 234)) eqn:TD; cbn [negb]; [|reflexivity].
    destruct (cp_v fr' 18 =? 1); [reflexivity|]. destruct (cp_v fr' 18 =? 2); [reflexivity|].
    destruct (cp_v fr' 18 =? 4) eqn:L4; [|reflexivity]. destruct (cp_v fr' 19 =? 3) eqn:S3; cbn [negb]; [|reflexivity].
    assert (R : cp_rec fr = true).
    { unfold cp_rec, cp_type. rewrite B18, B19. unfold cp_v at 1 2. rewrite !B by lia. fold (cp_v fr' 16) (cp_v fr' 17).
      rewrite TD, L4, S3. reflexivity. }
    destruct (RX R) as (X32 & X34 & X35 & X33). unfold cp_amp. rewrite <- X34, <- X35, <- X32.
    destruct (Z.eqb_spec (cp_v fr 32) 0x12) as [E32|E32]; cbn [andb]; [|reflexivity].
    rewrite <- (X33 E32). reflexivity. }
  destruct KE as [KE RX].
  unfold ctrlparse, cp_rd. rewrite HD, HD'. rewrite <- V12, <- V13, E12, E13. cbn [negb Z.eqb Pos.eqb].
  rewrite (proj2 (Z.leb_le 50 n) Hn). cbn [negb].
  unfold cp_struct. rewrite <- KE, <- RC, <- BC. rewrite !B by lia.
  destruct (cp_rec fr) eqn:R.
  - destruct (RX eq_refl) as (X32 & X34 & X35 & X33). rewrite <- X32.
    assert (A : cp_kind fr = 6 -> forall i, (i = 36 \/ i = 37 \/ i = 38)%nat -> cp_b fr i = cp_b fr' i)
      by (intros K i Hi; apply H, cp_rd_amp; assumption).
    assert (B34 : cp_b fr 34 = cp_b fr' 34) by (apply H, cp_rd_rec; [exact HD | exact R | lia]).
    assert (B35 : cp_b fr 35 = cp_b fr' 35) by (apply H, cp_rd_rec; [exact HD | exact R | lia]).
    rewrite B34, B35.
    destruct (Z.eqb_spec (cp_kind fr) 6) as [K6|K6].
    + rewrite (A K6 36%nat), (A K6 37%nat), (A K6 38%nat) by lia. split; reflexivity.
    + split; reflexivity.
  - assert (K6 : cp_kind fr <> 6).
    { intros K. assert (fst (ctrlparse n fr) = 6) as K' by (unfold ctrlparse; rewrite HD; exact K).
      apply ctrlparse_headamp in K'. rewrite R in K'. destruct K' as (_ & X & _). discriminate. }
    rewrite (proj2 (Z.eqb_neq _ _) K6). split; reflexivity.
Qed.
