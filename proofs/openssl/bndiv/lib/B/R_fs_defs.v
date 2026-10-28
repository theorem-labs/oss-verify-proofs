(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA Arr.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_small R_m2s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope Z_scope.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition kFakeStackSize : Z := 0xb09000.
Definition NF (c : Z) : Z := 2 ^ (14 - c).
Definition flags_off (c : Z) : Z := 32768 - 2 ^ (15 - c).
Definition fsz (c : Z) : Z := 64 * 2 ^ c.
Definition fl_base (FSB c : Z) : Z := FSB + 0x1000 + flags_off c.
Definition frame_addr (FSB c p : Z) : Z := FSB + 0x9000 + c * 2 ^ 20 + p * fsz c.
Definition b8 (z : Z) : byte := Z_to_bv 8 z.

Lemma NF_0 : NF 0 = 16384. Proof. reflexivity. Qed.
Lemma NF_2 : NF 2 = 4096. Proof. reflexivity. Qed.
Lemma NF_4 : NF 4 = 1024. Proof. reflexivity. Qed.
Lemma flags_off_0 : flags_off 0 = 0. Proof. reflexivity. Qed.
Lemma flags_off_2 : flags_off 2 = 0x6000. Proof. reflexivity. Qed.
Lemma flags_off_4 : flags_off 4 = 0x7800. Proof. reflexivity. Qed.
Lemma fsz_0 : fsz 0 = 64. Proof. reflexivity. Qed.
Lemma fsz_2 : fsz 2 = 256. Proof. reflexivity. Qed.
Lemma fsz_4 : fsz 4 = 1024. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition FSB_ok (FSB : Z) : Prop :=
  kHighShadowEnd + 4096 <= FSB /\ FSB + kFakeStackSize <= 2 ^ 47 /\ (FSB mod 4096 = 0).

(* [comment removed for export] *)
Definition fs_hint (FSB c : Z) (m : mem) (h : Z) : Prop := rw_cells bsegs m (FSB + 8 * c) [C8 (Z_to_bv 64 h)].
(* [comment removed for export] *)
Definition fs_const (FSB : Z) (m : mem) : Prop :=
  rw_cells bsegs m (FSB + 0x58) [C8 (Z_to_bv 64 20); C1 (Z_to_bv 8 0)].
Definition fs_flags (FSB c : Z) (m : mem) (fl : list Z) : Prop := u8arr bsegs m (fl_base FSB c) (map b8 fl).
Definition flags_ok (c : Z) (fl : list Z) : Prop :=
  Z.of_nat (length fl) = NF c /\ Forall (fun z => z = 0 \/ z = 1) fl.
Fixpoint nbusy (fl : list Z) : nat :=
  match fl with [] => 0%nat | z :: r => ((if Z.eqb z 0 then 0 else 1) + nbusy r)%nat end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint scan_from (fl : list Z) (n h : Z) (k : nat) : option nat :=
  match k with
  | O => None
  | S k' => if Z.eqb (nth (Z.to_nat (h mod n)) fl 1) 0 then Some O
            else option_map S (scan_from fl n (h + 1) k')
  end.

Lemma scan_from_spec : forall fl n h k j,
  scan_from fl n h k = Some j ->
  (j < k)%nat
  /\ nth (Z.to_nat ((h + Z.of_nat j) mod n)) fl 1 = 0
  /\ (forall i, (i < j)%nat -> nth (Z.to_nat ((h + Z.of_nat i) mod n)) fl 1 <> 0).
Proof.
  intros fl n h k. revert h. induction k as [|k IH]; intros h j E; cbn [scan_from] in E; [discriminate|].
  destruct (Z.eqb_spec (nth (Z.to_nat (h mod n)) fl 1) 0) as [Hz|Hnz].
  - inversion E; subst j. split; [lia|]. split; [rewrite Z.add_0_r; exact Hz|]. intros i Hi. lia.
  - destruct (scan_from fl n (h + 1) k) as [j'|] eqn:E'; cbn in E; [|discriminate].
    inversion E; subst j. destruct (IH (h + 1) j' E') as (Hj & Hf & Hb).
    split; [lia|]. split.
    + replace (h + Z.of_nat (S j')) with (h + 1 + Z.of_nat j') by lia. exact Hf.
    + intros i Hi. destruct i as [|i].
      * rewrite Z.add_0_r. exact Hnz.
      * replace (h + Z.of_nat (S i)) with (h + 1 + Z.of_nat i) by lia. apply Hb. lia.
Qed.

(* [comment removed for export] *)
Lemma nbusy_le_length : forall fl, (nbusy fl <= length fl)%nat.
Proof. induction fl as [|z r IH]; cbn [nbusy length]; [lia|]. destruct (Z.eqb z 0); lia. Qed.

Lemma nbusy_zero_nth : forall fl i, (i < length fl)%nat -> nbusy fl = 0%nat -> nth i fl 1 = 0.
Proof.
  induction fl as [|z r IH]; intros i Hi H; cbn [length] in Hi; [lia|].
  cbn [nbusy] in H. destruct (Z.eqb_spec z 0) as [Hz|Hz]; [|lia].
  destruct i as [|i]; cbn [nth]; [exact Hz|]. apply IH; lia.
Qed.

Lemma scan_from_none : forall fl n h k,
  scan_from fl n h k = None -> forall i, (i < k)%nat -> nth (Z.to_nat ((h + Z.of_nat i) mod n)) fl 1 <> 0.
Proof.
  intros fl n h k. revert h. induction k as [|k IH]; intros h E i Hi; [lia|].
  cbn [scan_from] in E. destruct (Z.eqb_spec (nth (Z.to_nat (h mod n)) fl 1) 0) as [Hz|Hnz]; [discriminate|].
  destruct (scan_from fl n (h + 1) k) eqn:E'; cbn in E; [discriminate|].
  destruct i as [|i].
  - rewrite Z.add_0_r. exact Hnz.
  - replace (h + Z.of_nat (S i)) with (h + 1 + Z.of_nat i) by lia. apply IH; [exact E'| lia].
Qed.

Lemma nbusy_full : forall fl, (forall k, (k < length fl)%nat -> nth k fl 1 <> 0) -> nbusy fl = length fl.
Proof.
  induction fl as [|z r IH]; intros H; cbn [nbusy length]; [reflexivity|].
  pose proof (H O ltac:(cbn [length]; lia)) as H0. cbn [nth] in H0.
  destruct (Z.eqb_spec z 0) as [Hz|Hz]; [contradiction|].
  rewrite IH; [reflexivity|]. intros k Hk. exact (H (S k) ltac:(cbn [length]; lia)).
Qed.

(* [comment removed for export] *)
Lemma scan_target_exists : forall fl n h,
  Z.of_nat (length fl) = n -> (nbusy fl < length fl)%nat ->
  exists j, scan_from fl n h (Z.to_nat n) = Some j.
Proof.
  intros fl n h Hn Hb.
  destruct (scan_from fl n h (Z.to_nat n)) as [j|] eqn:E; [exists j; reflexivity|].
  exfalso. pose proof (scan_from_none _ _ _ _ E) as HN.
  assert (Hall : forall k, (k < length fl)%nat -> nth k fl 1 <> 0).
  { intros k Hk. set (i := Z.to_nat ((Z.of_nat k - h) mod n)).
    assert (Hpos : 0 < n) by lia.
    assert (Hi : (i < Z.to_nat n)%nat).
    { unfold i. pose proof (Z.mod_pos_bound (Z.of_nat k - h) n Hpos). lia. }
    specialize (HN i Hi).
    replace (Z.to_nat ((h + Z.of_nat i) mod n)) with k in HN; [exact HN|].
    unfold i. rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia).
    rewrite Z.add_mod_idemp_r by lia. replace (h + (Z.of_nat k - h)) with (Z.of_nat k) by lia.
    rewrite Z.mod_small by lia. lia. }
  pose proof (nbusy_full fl Hall). lia.
Qed.

(* [comment removed for export] *)
Lemma map_b8_upd : forall fl i z, map b8 (upd fl i z) = upd (map b8 fl) i (b8 z).
Proof.
  induction fl as [|x r IH]; intros i z; [destruct i; reflexivity|].
  destruct i as [|i]; cbn [upd map]; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma nth_upd_same : forall (fl : list Z) i z d, (i < length fl)%nat -> nth i (upd fl i z) d = z.
Proof.
  induction fl as [|x r IH]; intros i z d Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; cbn [upd nth]; [reflexivity|]. apply IH. lia.
Qed.

Lemma nth_upd_other : forall (fl : list Z) i j z d, i <> j -> nth j (upd fl i z) d = nth j fl d.
Proof.
  induction fl as [|x r IH]; intros i j z d Hij; [destruct i; reflexivity|].
  destruct i as [|i], j as [|j]; cbn [upd nth]; try reflexivity; [lia|]. apply IH. lia.
Qed.

Lemma flags_ok_upd : forall c fl i z, flags_ok c fl -> (z = 0 \/ z = 1) -> flags_ok c (upd fl i z).
Proof.
  intros c fl i z [Hl Hf] Hz. split; [rewrite upd_length; exact Hl|].
  clear Hl. revert i. induction Hf as [|x r Hx Hr IH]; intros i.
  - destruct i; cbn [upd]; constructor.
  - destruct i as [|i]; cbn [upd].
    + constructor; [exact Hz| exact Hr].
    + constructor; [exact Hx| apply IH].
Qed.

Lemma nbusy_upd_set : forall fl i, (i < length fl)%nat -> nth i fl 1 = 0 -> nbusy (upd fl i 1) = S (nbusy fl).
Proof.
  induction fl as [|x r IH]; intros i Hi Hz; cbn [length] in Hi; [lia|].
  destruct i as [|i]; cbn [upd nbusy nth] in *.
  - subst x. reflexivity.
  - rewrite IH by (auto; lia). lia.
Qed.

Lemma nbusy_upd_clear : forall fl i, (i < length fl)%nat -> nth i fl 1 = 1 -> S (nbusy (upd fl i 0)) = nbusy fl.
Proof.
  induction fl as [|x r IH]; intros i Hi Hz; cbn [length] in Hi; [lia|].
  destruct i as [|i]; cbn [upd nbusy nth] in *.
  - subst x. reflexivity.
  - rewrite <- (IH i) by (auto; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma frame_addr_range : forall FSB c p, (c = 0 \/ c = 2 \/ c = 4) -> 0 <= p < NF c ->
  FSB + 0x9000 <= frame_addr FSB c p /\ frame_addr FSB c p + fsz c <= FSB + kFakeStackSize.
Proof.
  intros FSB c p Hc Hp. unfold frame_addr, kFakeStackSize.
  destruct Hc as [ -> | [ -> | -> ] ]; rewrite ?NF_0, ?NF_2, ?NF_4 in Hp; rewrite ?fsz_0, ?fsz_2, ?fsz_4; lia.
Qed.

Lemma fl_base_range : forall FSB c p, (c = 0 \/ c = 2 \/ c = 4) -> 0 <= p < NF c ->
  FSB + 0x1000 <= fl_base FSB c + p /\ fl_base FSB c + p + 1 <= FSB + 0x9000.
Proof.
  intros FSB c p Hc Hp. unfold fl_base.
  destruct Hc as [ -> | [ -> | -> ] ]; rewrite ?NF_0, ?NF_2, ?NF_4 in Hp; rewrite ?flags_off_0, ?flags_off_2, ?flags_off_4; lia.
Qed.

(* [comment removed for export] *)
Definition fs_free_frames (FSB c : Z) (m : mem) (fl : list Z) : Prop :=
  forall p, 0 <= p < NF c -> nth (Z.to_nat p) fl 1 = 0 ->
    (exists junk, rw_cells bsegs m (frame_addr FSB c p) [CB (Z.to_nat (fsz c)) junk])
    /\ (exists junk, rw_cells bsegs m (shad (frame_addr FSB c p)) [CB (Z.to_nat (fsz c / 8)) junk]).

Lemma fs_free_frames_transport : forall FSB c m m' fl W,
  fs_free_frames FSB c m fl -> munch W m m' -> wmono bsegs m m' ->
  (forall p, 0 <= p < NF c -> nth (Z.to_nat p) fl 1 = 0 ->
     disjoint_from W (frame_addr FSB c p) (fsz c) /\ disjoint_from W (shad (frame_addr FSB c p)) (fsz c / 8)) ->
  fs_free_frames FSB c m' fl.
Proof.
  intros FSB c m m' fl W H MU WM HD p Hp Hf.
  destruct (H p Hp Hf) as [[j1 H1] [j2 H2]]. destruct (HD p Hp Hf) as [D1 D2].
  assert (E1 : 0 <= fsz c) by (unfold fsz; pose proof (Z.pow_nonneg 2 c); lia).
  split; [exists j1| exists j2]; eapply rw_cells_transport; eauto; cbn [cells_size csize];
    rewrite Nat.add_0_r, Z2Nat.id; auto; apply Z.div_pos; lia.
Qed.

(* [comment removed for export] *)
Lemma shad_frame : forall FSB c p, FSB mod 4096 = 0 -> 0 <= c -> 0 <= p ->
  shad (frame_addr FSB c p) = SHB + FSB / 8 + 0x1200 + c * 2 ^ 17 + p * (fsz c / 8).
Proof.
  intros FSB c p HF Hc Hp. unfold shad, frame_addr, fsz.
  assert (E : FSB = 4096 * (FSB / 4096)) by (apply Z.div_exact; lia).
  set (f := FSB / 4096) in *. rewrite E.
  assert (P : 0 < 2 ^ c) by (apply Z.pow_pos_nonneg; lia).
  replace (64 * 2 ^ c / 8) with (8 * 2 ^ c) by (apply Z.div_unique with 0; lia).
  replace (4096 * f / 8) with (512 * f) by (apply Z.div_unique with 0; lia).
  replace (4096 * f + 0x9000 + c * 2 ^ 20 + p * (64 * 2 ^ c)) with ((512 * f + 0x1200 + c * 2 ^ 17 + p * (8 * 2 ^ c)) * 8)
    by (change (2 ^ 20) with (2 ^ 17 * 8); ring).
  rewrite Z.div_mul by lia. lia.
Qed.

Lemma nth_error_map_b8 : forall fl i, (i < length fl)%nat -> nth_error (map b8 fl) i = Some (b8 (nth i fl 1)).
Proof.
  induction fl as [|x r IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; cbn [map nth_error nth]; [reflexivity|]. apply IH. lia.
Qed.

Lemma flags_ok_nth : forall c fl i, flags_ok c fl -> (i < length fl)%nat -> nth i fl 1 = 0 \/ nth i fl 1 = 1.
Proof.
  intros c fl i [_ Hf] Hi. rewrite Forall_forall in Hf. apply Hf. apply nth_In. exact Hi.
Qed.

(* [comment removed for export] *)
Lemma fs_free_frames_take : forall FSB c m fl i,
  fs_free_frames FSB c m fl -> fs_free_frames FSB c m (upd fl i 1).
Proof.
  intros FSB c m fl i H p Hp Hf. apply H; [exact Hp|].
  destruct (Nat.eq_dec (Z.to_nat p) i) as [E|E].
  - subst i. destruct (Nat.lt_ge_cases (Z.to_nat p) (length fl)) as [L|L].
    + rewrite nth_upd_same in Hf by exact L. discriminate.
    + rewrite nth_overflow in Hf; [discriminate| rewrite upd_length; exact L].
  - rewrite nth_upd_other in Hf by (intro; apply E; symmetry; assumption). exact Hf.
Qed.

Lemma nth_upd_free_other : forall (fl : list Z) i p, nth p (upd fl i 1) 1 = 0 -> p <> i.
Proof.
  intros fl i p H E. subst p. destruct (Nat.lt_ge_cases i (length fl)) as [L|L].
  - rewrite nth_upd_same in H by exact L. discriminate.
  - rewrite nth_overflow in H; [discriminate| rewrite upd_length; exact L].
Qed.

(* [comment removed for export] *)
Definition sm_W (c FSB pos usp : Z) : list (Z * Z) :=
  [(FSB + 8 * c, FSB + 8 * c + 8); (fl_base FSB c + pos, fl_base FSB c + pos + 1);
   (frame_addr FSB c pos, frame_addr FSB c pos + fsz c);
   (shad (frame_addr FSB c pos), shad (frame_addr FSB c pos) + fsz c / 8);
   (usp - 208, usp)].
