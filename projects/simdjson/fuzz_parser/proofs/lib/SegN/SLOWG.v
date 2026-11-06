(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

Module SNG.
Local Notation u := bv_unsigned.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Fam.
Variable segs : list Segment.
(* [comment removed for export] *)
Definition rb (M : word -> option byte) (x : Z) : option byte :=
  match M (Z_to_bv 64 x) with Some c => Some c | None => seg_rom segs (Z_to_bv 64 x) end.
(* [comment removed for export] *)
Definition bat (M : word -> option byte) (x b : Z) : Prop := exists c, rb M x = Some c /\ u c = b.

Definition isdig (b : Z) : Prop := 48 <= b <= 57.

Definition digs (M : word -> option byte) (a n : Z) : Prop := forall j, 0 <= j < n -> exists b, bat M (a + j) b /\ isdig b.
Definition zdot (M : word -> option byte) (a n : Z) : Prop := forall j, 0 <= j < n -> exists b, bat M (a + j) b /\ (b = 48 \/ b = 46).
Definition zeros (M : word -> option byte) (a n : Z) : Prop := forall j, 0 <= j < n -> bat M (a + j) 48.

(* [comment removed for export] *)
Definition is0 (M : word -> option byte) (x : Z) : Z :=
  match rb M x with Some c => if Z.eqb (u c) 48 then 1 else 0 | None => 0 end.
Fixpoint cnt0 (M : word -> option byte) (a : Z) (n : nat) : Z :=
  match n with O => 0 | S n' => cnt0 M a n' + is0 M (a + Z.of_nat n') end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition g_dig (M : word -> option byte) (a n : word) : Prop := u a + u n <= 2^64 /\ digs M (u a) (u n).
Definition g_dot (M : word -> option byte) (a : word) : Prop := bat M (u a) 46.
Definition g_frac (M : word -> option byte) (ip il fp fl : word) : Prop :=
  u fl = 0 \/ (u ip + u il + 1 < 2^64 /\ u fp = u ip + u il + 1 /\ bat M (u ip + u il) 46).
Definition g_zrun (M : word -> option byte) (a n k : word) : Prop :=
  u a + u n <= 2^64 /\ zdot M (u a) (u n) /\ u k = cnt0 M (u a) (Z.to_nat (u n)).
Definition g_nzd (M : word -> option byte) (ip il fp fl : word) : Prop :=
  u ip + u il <= 2^64 /\ u fp + u fl <= 2^64 /\
  ((exists j, 0 <= j < u il /\ exists b, bat M (u ip + j) b /\ 49 <= b <= 57) \/
   (exists j, 0 <= j < u fl /\ exists b, bat M (u fp + j) b /\ 49 <= b <= 57)).
Definition g_z0 (M : word -> option byte) (a n i : word) : Prop := u a + u n <= 2^64 /\ (u i = 0 -> zeros M (u a) (u n)).

Definition sng_gp (id : nat) (vs : list word) (M : word -> option byte) : Prop :=
  match id, vs with
  | 1%nat, [a; n] => g_dig M a n
  | 2%nat, [a] => g_dot M a
  | 3%nat, [ip; il; fp; fl] => g_frac M ip il fp fl
  | 4%nat, [a; n; k] => g_zrun M a n k
  | 5%nat, [ip; il; fp; fl] => g_nzd M ip il fp fl
  | 6%nat, [a; n; i] => g_z0 M a n i
  | _, _ => False
  end.

End Fam.

Definition sng_gfp (id : nat) (args : list expr) : list SG.gwin :=
  match id, args with
  | 1%nat, [a; n] => [(a, 0, n)]
  | 2%nat, [a] => [(a, 0, ELit 1)]
  | 3%nat, [ip; il; fp; fl] => [(EAlu ALU_ADD ip il, 0, ELit 1)]
  | 4%nat, [a; n; k] => [(a, 0, n)]
  | 5%nat, [ip; il; fp; fl] => [(ip, 0, il); (fp, 0, fl)]
  | 6%nat, [a; n; i] => [(a, 0, n)]
  | _, _ => []
  end.

Section Fam2.
Variable segs : list Segment.
Local Notation bat := (bat segs).
Local Notation rb := (rb segs).
Local Notation digs := (digs segs).
Local Notation zdot := (zdot segs).
Local Notation zeros := (zeros segs).
Local Notation is0 := (is0 segs).
Local Notation cnt0 := (cnt0 segs).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma u_small' : forall x, 0 <= x < 2^64 -> u (Z_to_bv 64 x) = x.
Proof. intros x H. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). apply Z.mod_small. exact H. Qed.

Lemma u_rng' : forall x : word, 0 <= u x < 2^64.
Proof. intros x. pose proof (bv_unsigned_in_range 64 x) as H. unfold bv_modulus in H. exact H. Qed.

Section Frame.
Variables (M M' : word -> option byte).

Lemma bat_frame : forall lo hi x b, (forall y : word, lo <= u y < hi -> M' y = M y) -> lo <= x < hi -> 0 <= x < 2^64 ->
  bat M x b -> bat M' x b.
Proof.
  intros lo hi x b HF Hx Hx64 (c & Hc & Hu). exists c. split; [|exact Hu]. unfold SNG.rb in *. rewrite HF; [exact Hc|]. rewrite u_small'; lia.
Qed.

Lemma digs_frame : forall a n, (forall y : word, a <= u y < a + n -> M' y = M y) -> 0 <= a -> a + n <= 2^64 -> digs M a n -> digs M' a n.
Proof.
  intros a n HF Ha Hn H j Hj. destruct (H j Hj) as (b & Hb & Hd). exists b. split; [|exact Hd].
  apply (bat_frame a (a + n)); [exact HF | lia | lia | exact Hb].
Qed.
Lemma zdot_frame : forall a n, (forall y : word, a <= u y < a + n -> M' y = M y) -> 0 <= a -> a + n <= 2^64 -> zdot M a n -> zdot M' a n.
Proof.
  intros a n HF Ha Hn H j Hj. destruct (H j Hj) as (b & Hb & Hd). exists b. split; [|exact Hd].
  apply (bat_frame a (a + n)); [exact HF | lia | lia | exact Hb].
Qed.
Lemma zeros_frame : forall a n, (forall y : word, a <= u y < a + n -> M' y = M y) -> 0 <= a -> a + n <= 2^64 -> zeros M a n -> zeros M' a n.
Proof. intros a n HF Ha Hn H j Hj. apply (bat_frame a (a + n)); [exact HF | lia | lia | exact (H j Hj)]. Qed.

Lemma is0_frame : forall x, M' (Z_to_bv 64 x) = M (Z_to_bv 64 x) -> is0 M' x = is0 M x.
Proof. intros x H. unfold SNG.is0, SNG.rb. rewrite H. reflexivity. Qed.

Lemma cnt0_frame : forall a n, (forall y : word, a <= u y < a + Z.of_nat n -> M' y = M y) -> 0 <= a -> a + Z.of_nat n <= 2^64 ->
  cnt0 M' a n = cnt0 M a n.
Proof.
  intros a n. induction n as [|n IH]; intros HF Ha Hn; [reflexivity|]. cbn [cnt0].
  rewrite IH; [| intros y Hy; apply HF; lia | lia | lia].
  rewrite is0_frame; [reflexivity|]. apply HF. rewrite u_small'; lia.
Qed.
End Frame.

Lemma win_den_lit : forall E b off n, SG.win_den E (b, off, n) = (u (edenot E b) + off, u (edenot E b) + off + u (edenot E n)).
Proof. reflexivity. Qed.

Lemma u_edenot_lit : forall E z, u (edenot E (ELit z)) = z mod 2^64.
Proof. intros E z. cbn [edenot]. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma u_edenot_add : forall E a b, u (edenot E (EAlu ALU_ADD a b)) = (u (edenot E a) + u (edenot E b)) mod 2^64.
Proof. intros E a b. cbn [edenot]. unfold alu64, alu. rewrite bv_add_unsigned. reflexivity. Qed.

Theorem sng_frame : SG.gp_frameP (sng_gp segs) sng_gfp.
Proof.
  intros id args E M M' HF H.
  (* [comment removed for export] *)
  assert (W1 : forall b off n, In (b, off, n) (sng_gfp id args) ->
            forall y : word, u (edenot E b) + off <= u y < u (edenot E b) + off + u (edenot E n) -> M' y = M y).
  { intros b off n Hin y Hy. apply HF. exists (b, off, n). split; [exact Hin|]. cbn [SG.win_den]. exact Hy. }
  destruct id as [|[|[|[|[|[|[|id]]]]]]]; cbn [sng_gp sng_gfp] in *;
    try (destruct args; cbn [map] in H; exact H).
  - (* [comment removed for export] *)
    destruct args as [|a [|n [|? ?]]]; cbn [map sng_gp] in H |- *; try exact H.
    destruct H as (Hb & Hd). split; [exact Hb|].
    specialize (W1 a 0 n (or_introl eq_refl)). rewrite Z.add_0_r in W1.
    apply (digs_frame M M'); [exact W1 | apply u_rng' | exact Hb | exact Hd].
  - (* [comment removed for export] *)
    destruct args as [|a [|? ?]]; cbn [map sng_gp] in H |- *; try exact H.
    specialize (W1 a 0 (ELit 1) (or_introl eq_refl)). rewrite Z.add_0_r, u_edenot_lit in W1. change (1 mod 2^64) with 1 in W1.
    unfold g_dot in *. apply (bat_frame M M' (u (edenot E a)) (u (edenot E a) + 1)); [exact W1 | lia | apply u_rng' | exact H].
  - (* [comment removed for export] *)
    destruct args as [|ip [|il [|fp [|fl [|? ?]]]]]; cbn [map sng_gp] in H |- *; try exact H.
    unfold g_frac in *. destruct H as [H|(H1 & H2 & H3)]; [left; exact H|right]. split; [exact H1|]. split; [exact H2|].
    specialize (W1 (EAlu ALU_ADD ip il) 0 (ELit 1) (or_introl eq_refl)). rewrite Z.add_0_r, u_edenot_lit, u_edenot_add in W1.
    change (1 mod 2^64) with 1 in W1. pose proof (u_rng' (edenot E ip)). pose proof (u_rng' (edenot E il)).
    rewrite Z.mod_small in W1 by lia.
    apply (bat_frame M M' (u (edenot E ip) + u (edenot E il)) (u (edenot E ip) + u (edenot E il) + 1)); [exact W1 | lia | lia | exact H3].
  - (* [comment removed for export] *)
    destruct args as [|a [|n [|k [|? ?]]]]; cbn [map sng_gp] in H |- *; try exact H.
    destruct H as (Hb & Hz & Hk). specialize (W1 a 0 n (or_introl eq_refl)). rewrite Z.add_0_r in W1.
    pose proof (u_rng' (edenot E a)). pose proof (u_rng' (edenot E n)).
    split; [exact Hb|]. split; [apply (zdot_frame M M'); [exact W1 | lia | exact Hb | exact Hz]|].
    rewrite Hk. symmetry. apply cnt0_frame; [| lia | rewrite Z2Nat.id by lia; exact Hb].
    intros y Hy. apply W1. rewrite Z2Nat.id in Hy by lia. exact Hy.
  - (* [comment removed for export] *)
    destruct args as [|ip [|il [|fp [|fl [|? ?]]]]]; cbn [map sng_gp] in H |- *; try exact H.
    destruct H as (Hb1 & Hb2 & Hx). split; [exact Hb1|]. split; [exact Hb2|].
    pose proof (W1 ip 0 il (or_introl eq_refl)) as W1a. pose proof (W1 fp 0 fl (or_intror (or_introl eq_refl))) as W1b.
    rewrite Z.add_0_r in W1a, W1b.
    pose proof (u_rng' (edenot E ip)). pose proof (u_rng' (edenot E fp)).
    destruct Hx as [(j & Hj & b & Hb & Hd)|(j & Hj & b & Hb & Hd)]; [left|right]; exists j; split; [exact Hj| |exact Hj|];
      exists b; (split; [|exact Hd]).
    + apply (bat_frame M M' (u (edenot E ip)) (u (edenot E ip) + u (edenot E il))); [exact W1a | lia | lia | exact Hb].
    + apply (bat_frame M M' (u (edenot E fp)) (u (edenot E fp) + u (edenot E fl))); [exact W1b | lia | lia | exact Hb].
  - (* [comment removed for export] *)
    destruct args as [|a [|n [|i [|? ?]]]]; cbn [map sng_gp] in H |- *; try exact H.
    destruct H as (Hb & Hz). split; [exact Hb|]. intros Hi. specialize (W1 a 0 n (or_introl eq_refl)). rewrite Z.add_0_r in W1.
    apply (zeros_frame M M'); [exact W1 | apply u_rng' | exact Hb | exact (Hz Hi)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Runs.
Variable M : word -> option byte.

Lemma bat_fun : forall x b1 b2, bat M x b1 -> bat M x b2 -> b1 = b2.
Proof. intros x b1 b2 (c1 & H1 & U1) (c2 & H2 & U2). rewrite H1 in H2. injection H2 as ->. lia. Qed.

Lemma digs_0 : forall a, digs M a 0.
Proof. intros a j Hj. lia. Qed.
Lemma zdot_0 : forall a, zdot M a 0.
Proof. intros a j Hj. lia. Qed.
Lemma zeros_0 : forall a, zeros M a 0.
Proof. intros a j Hj. lia. Qed.

Lemma digs_app : forall a n k, 0 <= n -> digs M a n -> digs M (a + n) k -> digs M a (n + k).
Proof.
  intros a n k Hn H1 H2 j Hj. destruct (Z.lt_ge_cases j n) as [Hl|Hg]; [apply H1; lia|].
  destruct (H2 (j - n) ltac:(lia)) as (b & Hb & Hd). exists b. split; [|exact Hd]. replace (a + j) with (a + n + (j - n)) by lia. exact Hb.
Qed.
Lemma digs_1 : forall x b, bat M x b -> isdig b -> digs M x 1.
Proof. intros x b Hb Hd j Hj. exists b. replace (x + j) with x by lia. split; assumption. Qed.
Lemma digs_sub : forall a n k, 0 <= k <= n -> digs M a n -> digs M a k.
Proof. intros a n k Hk H j Hj. apply H. lia. Qed.
Lemma zdot_app1 : forall a n b, 0 <= n -> zdot M a n -> bat M (a + n) b -> (b = 48 \/ b = 46) -> zdot M a (n + 1).
Proof.
  intros a n b Hn H Hb Hd j Hj. destruct (Z.lt_ge_cases j n) as [Hl|Hg]; [apply H; lia|].
  exists b. replace (a + j) with (a + n) by lia. split; assumption.
Qed.
Lemma zeros_app1 : forall a n, 0 <= n -> zeros M a n -> bat M (a + n) 48 -> zeros M a (n + 1).
Proof.
  intros a n Hn H Hb j Hj. destruct (Z.lt_ge_cases j n) as [Hl|Hg]; [apply H; lia|]. replace (a + j) with (a + n) by lia. exact Hb.
Qed.

Lemma is0_48 : forall x, bat M x 48 -> is0 M x = 1.
Proof. intros x (c & H & U). unfold SNG.is0. rewrite H, U. reflexivity. Qed.
Lemma is0_not48 : forall x b, bat M x b -> b <> 48 -> is0 M x = 0.
Proof. intros x b (c & H & U) Hb. unfold SNG.is0. rewrite H. destruct (Z.eqb_spec (u c) 48); [lia|reflexivity]. Qed.
Lemma is0_rng : forall x, 0 <= is0 M x <= 1.
Proof. intros x. unfold SNG.is0. destruct (SNG.rb _ M x); [destruct (Z.eqb _ _)|]; lia. Qed.

Lemma cnt0_S : forall a n, cnt0 M a (S n) = cnt0 M a n + is0 M (a + Z.of_nat n).
Proof. reflexivity. Qed.
Lemma cnt0_rng : forall a n, 0 <= cnt0 M a n <= Z.of_nat n.
Proof. intros a n. induction n as [|n IH]; cbn [cnt0]; [lia|]. pose proof (is0_rng (a + Z.of_nat n)). lia. Qed.
Lemma cnt0_mono : forall a n k, cnt0 M a n <= cnt0 M a (n + k).
Proof.
  intros a n k. induction k as [|k IH]; [rewrite Nat.add_0_r; lia|]. rewrite Nat.add_succ_r, cnt0_S.
  pose proof (is0_rng (a + Z.of_nat (n + k))). lia.
Qed.
Lemma cnt0_zeros : forall a n, zeros M a (Z.of_nat n) -> cnt0 M a n = Z.of_nat n.
Proof.
  intros a n. induction n as [|n IH]; intros H; [reflexivity|]. rewrite cnt0_S, IH; [|intros j Hj; apply H; lia].
  rewrite is0_48; [lia|]. apply H. lia.
Qed.
(* [comment removed for export] *)
Lemma cnt0_app : forall a n k, cnt0 M a (n + k) = cnt0 M a n + cnt0 M (a + Z.of_nat n) k.
Proof.
  intros a n k. induction k as [|k IH]; [rewrite Nat.add_0_r; cbn; lia|].
  rewrite Nat.add_succ_r, !cnt0_S, IH. replace (a + Z.of_nat (n + k)) with (a + Z.of_nat n + Z.of_nat k) by lia. lia.
Qed.

(* [comment removed for export] *)
Definition nzb (x : Z) : Prop := exists b, bat M x b /\ 49 <= b <= 57.
Lemma nzb_dec : forall x, nzb x \/ ~ nzb x.
Proof.
  intros x. unfold nzb. destruct (rb M x) as [c|] eqn:H.
  - destruct (Z_le_dec 49 (u c)) as [H1|H1]; [destruct (Z_le_dec (u c) 57) as [H2|H2]|].
    + left. exists (u c). split; [exists c; split; [exact H | reflexivity] | lia].
    + right. intros (b & (c' & Hc & U) & Hb). rewrite H in Hc. injection Hc as <-. lia.
    + right. intros (b & (c' & Hc & U) & Hb). rewrite H in Hc. injection Hc as <-. lia.
  - right. intros (b & (c' & Hc & U) & Hb). rewrite H in Hc. discriminate.
Qed.
Lemma run_nz_dec : forall a n, (exists j, 0 <= j < Z.of_nat n /\ nzb (a + j)) \/ (forall j, 0 <= j < Z.of_nat n -> ~ nzb (a + j)).
Proof.
  intros a n. induction n as [|n IH].
  - right. intros j Hj. lia.
  - destruct IH as [(j & Hj & Hz)|Hn]; [left; exists j; split; [lia|exact Hz]|].
    destruct (nzb_dec (a + Z.of_nat n)) as [Hz|Hz]; [left; exists (Z.of_nat n); split; [lia|exact Hz]|].
    right. intros j Hj. destruct (Z.eq_dec j (Z.of_nat n)) as [->|Hne]; [exact Hz|]. apply Hn. lia.
Qed.
Lemma digs_not_nz_zeros : forall a n, 0 <= n -> digs M a n -> (forall j, 0 <= j < n -> ~ nzb (a + j)) -> zeros M a n.
Proof.
  intros a n Hn Hd Hz j Hj. destruct (Hd j Hj) as (b & Hb & Hdg). destruct (Z.eq_dec b 48) as [->|Hne]; [exact Hb|].
  exfalso. apply (Hz j Hj). exists b. split; [exact Hb|]. unfold isdig in Hdg. lia.
Qed.

(* [comment removed for export] *)
Lemma nzd_intro : forall ip il fp fl z k endp,
  0 <= ip -> 0 <= il -> 0 <= fl -> ip + il <= endp -> fp + fl <= endp -> endp < 2^64 ->
  digs M ip il -> digs M fp fl -> (fl = 0 \/ (fp = ip + il + 1 /\ bat M (ip + il) 46)) ->
  ip <= z -> zdot M ip (z - ip) -> cnt0 M ip (Z.to_nat (z - ip)) = k ->
  (z = endp \/ exists b, bat M z b /\ b <> 48 /\ b <> 46) ->
  k + 20 <= il + fl ->
  (exists j, 0 <= j < il /\ nzb (ip + j)) \/ (exists j, 0 <= j < fl /\ nzb (fp + j)).
Proof.
  intros ip il fp fl z k endp Hip Hil Hfl H1 H2 H3 Hd1 Hd2 Hfr Hz Hzd Hk Hstop Hcnt.
  destruct (run_nz_dec ip (Z.to_nat il)) as [(j & Hj & Hn)|A]; [left; exists j; split; [lia|exact Hn]|].
  destruct (run_nz_dec fp (Z.to_nat fl)) as [(j & Hj & Hn)|B]; [right; exists j; split; [lia|exact Hn]|].
  exfalso. rewrite Z2Nat.id in A, B by lia.
  pose proof (digs_not_nz_zeros ip il Hil Hd1 A) as Z1. pose proof (digs_not_nz_zeros fp fl Hfl Hd2 B) as Z2.
  (* [comment removed for export] *)
  set (E' := if Z.eqb fl 0 then ip + il else fp + fl).
  assert (HE : ip + il <= E' <= endp) by (unfold E'; destruct (Z.eqb_spec fl 0); lia).
  (* [comment removed for export] *)
  assert (ZD : forall x, ip <= x < E' -> exists b, bat M x b /\ (b = 48 \/ b = 46)).
  { intros x Hx. destruct (Z.lt_ge_cases x (ip + il)) as [Hl|Hg].
    - exists 48. split; [|left; reflexivity]. replace x with (ip + (x - ip)) by lia. apply Z1. lia.
    - unfold E' in Hx. destruct (Z.eqb_spec fl 0) as [Hf0|Hf0]; [lia|]. destruct Hfr as [Hfr|(Hfp & Hdot)]; [lia|].
      destruct (Z.eq_dec x (ip + il)) as [->|Hne]; [exists 46; split; [exact Hdot | right; reflexivity]|].
      exists 48. split; [|left; reflexivity]. replace x with (fp + (x - fp)) by lia. apply Z2. lia. }
  assert (CNT : cnt0 M ip (Z.to_nat (E' - ip)) = il + fl).
  { unfold E'. destruct (Z.eqb_spec fl 0) as [Hf0|Hf0].
    - subst fl. replace (ip + il - ip) with il by lia. rewrite cnt0_zeros; [lia|]. rewrite Z2Nat.id by lia. exact Z1.
    - destruct Hfr as [Hfr|(Hfp & Hdot)]; [lia|]. subst fp.
      assert (C1 : cnt0 M ip (Z.to_nat il) = il) by (rewrite cnt0_zeros by (rewrite Z2Nat.id by lia; exact Z1); lia).
      assert (C2 : is0 M (ip + il) = 0) by (apply (is0_not48 _ 46); [exact Hdot | lia]).
      assert (C3 : cnt0 M (ip + il + 1) (Z.to_nat fl) = fl) by (rewrite cnt0_zeros by (rewrite Z2Nat.id by lia; exact Z2); lia).
      replace (Z.to_nat (ip + il + 1 + fl - ip)) with (S (Z.to_nat il) + Z.to_nat fl)%nat by lia.
      rewrite cnt0_app, cnt0_S. replace (ip + Z.of_nat (S (Z.to_nat il))) with (ip + il + 1) by lia.
      replace (ip + Z.of_nat (Z.to_nat il)) with (ip + il) by lia. lia. }
  destruct (Z.lt_ge_cases z E') as [Hlt|Hge].
  - (* [comment removed for export] *)
    destruct Hstop as [Hend|(b & Hb & Hb1 & Hb2)]; [lia|].
    destruct (ZD z ltac:(lia)) as (b' & Hb' & Hbb). rewrite (bat_fun z b b' Hb Hb') in Hb1, Hb2. lia.
  - (* [comment removed for export] *)
    replace (Z.to_nat (z - ip)) with (Z.to_nat (E' - ip) + Z.to_nat (z - E'))%nat in Hk by lia.
    rewrite cnt0_app, CNT in Hk. pose proof (cnt0_rng (ip + Z.of_nat (Z.to_nat (E' - ip))) (Z.to_nat (z - E'))). lia.
Qed.

(* [comment removed for export] *)
Lemma nzd_intro' : forall ip il fp fl z k,
  0 <= ip -> 0 <= il -> 0 <= fl ->
  digs M ip il -> digs M fp fl -> (fl = 0 \/ (fp = ip + il + 1 /\ bat M (ip + il) 46)) ->
  ip <= z -> zdot M ip (z - ip) -> cnt0 M ip (Z.to_nat (z - ip)) = k ->
  ((exists b, bat M z b /\ b <> 48 /\ b <> 46) \/ (ip + il <= z /\ fp + fl <= z)) ->
  k + 20 <= il + fl ->
  (exists j, 0 <= j < il /\ nzb (ip + j)) \/ (exists j, 0 <= j < fl /\ nzb (fp + j)).
Proof.
  intros ip il fp fl z k Hip Hil Hfl Hd1 Hd2 Hfr Hz Hzd Hk Hstop Hcnt.
  destruct (run_nz_dec ip (Z.to_nat il)) as [(j & Hj & Hn)|A]; [left; exists j; split; [lia|exact Hn]|].
  destruct (run_nz_dec fp (Z.to_nat fl)) as [(j & Hj & Hn)|B]; [right; exists j; split; [lia|exact Hn]|].
  exfalso. rewrite Z2Nat.id in A, B by lia.
  pose proof (digs_not_nz_zeros ip il Hil Hd1 A) as Z1. pose proof (digs_not_nz_zeros fp fl Hfl Hd2 B) as Z2.
  set (E' := if Z.eqb fl 0 then ip + il else fp + fl).
  assert (HE : ip + il <= E') by (unfold E'; destruct (Z.eqb_spec fl 0); [lia|]; destruct Hfr as [Hfr|(Hfp & _)]; lia).
  assert (ZD : forall x, ip <= x < E' -> exists b, bat M x b /\ (b = 48 \/ b = 46)).
  { intros x Hx. destruct (Z.lt_ge_cases x (ip + il)) as [Hl|Hg].
    - exists 48. split; [|left; reflexivity]. replace x with (ip + (x - ip)) by lia. apply Z1. lia.
    - unfold E' in Hx. destruct (Z.eqb_spec fl 0) as [Hf0|Hf0]; [lia|]. destruct Hfr as [Hfr|(Hfp & Hdot)]; [lia|].
      destruct (Z.eq_dec x (ip + il)) as [->|Hne]; [exists 46; split; [exact Hdot | right; reflexivity]|].
      exists 48. split; [|left; reflexivity]. replace x with (fp + (x - fp)) by lia. apply Z2. lia. }
  assert (CNT : cnt0 M ip (Z.to_nat (E' - ip)) = il + fl).
  { unfold E'. destruct (Z.eqb_spec fl 0) as [Hf0|Hf0].
    - subst fl. replace (ip + il - ip) with il by lia. rewrite cnt0_zeros; [lia|]. rewrite Z2Nat.id by lia. exact Z1.
    - destruct Hfr as [Hfr|(Hfp & Hdot)]; [lia|]. subst fp.
      assert (C1 : cnt0 M ip (Z.to_nat il) = il) by (rewrite cnt0_zeros by (rewrite Z2Nat.id by lia; exact Z1); lia).
      assert (C2 : is0 M (ip + il) = 0) by (apply (is0_not48 _ 46); [exact Hdot | lia]).
      assert (C3 : cnt0 M (ip + il + 1) (Z.to_nat fl) = fl) by (rewrite cnt0_zeros by (rewrite Z2Nat.id by lia; exact Z2); lia).
      replace (Z.to_nat (ip + il + 1 + fl - ip)) with (S (Z.to_nat il) + Z.to_nat fl)%nat by lia.
      rewrite cnt0_app, cnt0_S. replace (ip + Z.of_nat (S (Z.to_nat il))) with (ip + il + 1) by lia.
      replace (ip + Z.of_nat (Z.to_nat il)) with (ip + il) by lia. lia. }
  destruct (Z.lt_ge_cases z E') as [Hlt|Hge].
  - destruct Hstop as [(b & Hb & Hb1 & Hb2)|(S1 & S2)].
    + destruct (ZD z ltac:(lia)) as (b' & Hb' & Hbb). rewrite (bat_fun z b b' Hb Hb') in Hb1, Hb2. lia.
    + unfold E' in Hlt. destruct (Z.eqb_spec fl 0); lia.
  - replace (Z.to_nat (z - ip)) with (Z.to_nat (E' - ip) + Z.to_nat (z - E'))%nat in Hk by lia.
    rewrite cnt0_app, CNT in Hk. pose proof (cnt0_rng (ip + Z.of_nat (Z.to_nat (E' - ip))) (Z.to_nat (z - E'))). lia.
Qed.

(* [comment removed for export] *)
Lemma z0_step : forall a n i d, 0 <= n -> 0 <= i -> 0 <= d <= 9 -> (i = 0 -> zeros M a n) -> bat M (a + n) (48 + d) ->
  (10 * i + d = 0 -> zeros M a (n + 1)).
Proof.
  intros a n i d Hn Hi Hd Hz Hb H0. assert (i = 0) by lia. assert (d = 0) by lia. subst.
  apply zeros_app1; [exact Hn | exact (Hz eq_refl) | exact Hb].
Qed.

(* [comment removed for export] *)
Lemma z0_final : forall ip il fp fl i,
  ((exists j, 0 <= j < il /\ nzb (ip + j)) \/ (exists j, 0 <= j < fl /\ nzb (fp + j))) ->
  (i = 0 -> zeros M ip il) -> (i = 0 -> zeros M fp fl) -> i <> 0.
Proof.
  intros ip il fp fl i Hn Z1 Z2 Hi. destruct Hn as [(j & Hj & b & Hb & Hd)|(j & Hj & b & Hb & Hd)].
  - pose proof (Z1 Hi j Hj) as H. rewrite (bat_fun _ _ _ Hb H) in Hd. lia.
  - pose proof (Z2 Hi j Hj) as H. rewrite (bat_fun _ _ _ Hb H) in Hd. lia.
Qed.
End Runs.

End Fam2.
End SNG.
