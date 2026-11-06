(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import PropExec CatExec StoreOk MemSplit.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CliDriver Require Import SymExec2 SymExec2Sound SymRun SymDrive SymDriveX.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition WIN : Z := 8388608.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma store_ok_mono_local : forall segs (M M' : word -> option byte) (a : word) n,
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  (forall x : word, (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n)%Z -> M x <> None -> M' x <> None) ->
  store_ok segs M a n = true -> store_ok segs M' a n = true.
Proof.
  intros segs M M' a n Hnw Hg Hok.
  apply store_ok_of_all; [exact Hnw|]. intros x Hx.
  pose proof (store_ok_all segs M n a Hnw Hok x Hx) as Hw.
  unfold wview in *. destruct (M x) as [b|] eqn:EM.
  - destruct (M' x) as [b'|] eqn:EM'; [discriminate|]. exfalso. exact (Hg x Hx ltac:(congruence) EM').
  - destruct (M' x) as [b'|]; [discriminate | exact Hw].
Qed.

(* [comment removed for export] *)

Definition avoids_b (U : list (Z * Z)) (k n : Z) : bool :=
  forallb (fun r : Z * Z => (k + n <=? fst r) || (snd r <=? k))%Z U.

(* [comment removed for export] *)
Definition fp_kept (U : list (Z * Z)) (slo shi ihi : Z) (b : expr) (k n : Z) : bool :=
  match b with
  | ELit z => (z =? 0)%Z && (0 <=? k)%Z && (k + n <=? ihi)%Z && (0 <=? n)%Z && avoids_b U k n
  | EVar i => Nat.eqb i 0 && (0 <=? n)%Z &&
              ((0 <=? k)%Z || ((- WIN <=? k)%Z && (k + n <=? slo)%Z) || ((shi <=? k)%Z && (k + n <=? 0)%Z))
  | _ => false
  end.

Definition kn_call1 (U : list (Z * Z)) (slo shi ihi dlo : Z) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => fp_kept U slo shi ihi b k (Z.of_nat w)
  | KZero (SA b k) (ELit l) => (0 <=? l)%Z && (l <? 2 ^ 64)%Z && fp_kept U slo shi ihi b k l
  | KZero _ _ => false
  | KBlob (SA b k) (ELit l) _ => (0 <=? l)%Z && (l <? 2 ^ 64)%Z && fp_kept U slo shi ihi b k l
  | KBlob _ _ _ => false
  | KImg lo hi => (lo <? hi)%Z && fp_kept U slo shi ihi (ELit 0) lo (hi - lo)
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA (EVar i) k) n => Nat.eqb i 0 && (- WIN <=? k)%Z && (k + n <=? 0)%Z && (0 <=? n)%Z
  | KWr (SA (ELit z) k) n => (z =? 0)%Z && (dlo <=? k)%Z && (k + n <=? ihi)%Z && (0 <=? n)%Z
  | KWr _ _ => false
  end.

Definition kn_call (U : list (Z * Z)) (slo shi ihi dlo : Z) (kn : list kentry) : list kentry :=
  List.filter (kn_call1 U slo shi ihi dlo) kn.

Section Sound.
  Variables (segs : list Segment) (E : env) (M M' : word -> option byte).
  Variables (U : list (Z * Z)) (slo shi ihi dlo : Z).
  Let sp0 : Z := bv_unsigned (ev E 0).

  (* [comment removed for export] *)
  Definition touched (x : Z) : Prop :=
    (x < ihi /\ exists r, In r U /\ fst r <= x < snd r)%Z
    \/ (ihi <= x < sp0 - WIN)%Z
    \/ (sp0 + slo <= x < sp0 + shi)%Z.

  Hypothesis Hsp : (2 ^ 40 <= sp0)%Z /\ (sp0 <= 2 ^ 47)%Z.
  Hypothesis Hihi : (0 <= ihi < 2 ^ 40 - WIN)%Z.
  Hypothesis Hscr : (- WIN <= slo <= shi)%Z /\ (shi <= 0)%Z.
  Hypothesis OUT : forall x : word, ~ touched (bv_unsigned x) -> M' x = M x.
  Hypothesis WINNN : forall x : word, (sp0 - WIN <= bv_unsigned x < sp0)%Z -> M x <> None -> M' x <> None.
  Hypothesis SEGWR : forall m (a : word) n, (dlo <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= ihi)%Z ->
                     store_ok segs m a n = true.

  Lemma avoids_sound : forall k n x, avoids_b U k n = true -> (k <= x < k + n)%Z ->
    ~ exists r, In r U /\ (fst r <= x < snd r)%Z.
  Proof.
    intros k n x Hb Hx [r [Hin Hr]]. unfold avoids_b in Hb.
    pose proof (proj1 (forallb_forall _ _) Hb r Hin) as H. cbn in H.
    apply orb_prop in H. destruct H as [H|H]; apply Z.leb_le in H; lia.
  Qed.

  Lemma fp_kept_sound : forall b k n, fp_kept U slo shi ihi b k n = true ->
    (0 <= n)%Z /\
    forall x, (bv_unsigned (edenot E b) + k <= x < bv_unsigned (edenot E b) + k + n)%Z -> ~ touched x.
  Proof.
    intros b k n H. destruct Hsp as [S1 S2]. destruct Hscr as [C1 C2].
    destruct b as [z|i| | | | | |]; cbn [fp_kept] in H; try discriminate.
    - apply andb_prop in H as [H Hav]. apply andb_prop in H as [H Hn]. apply andb_prop in H as [H Hk2].
      apply andb_prop in H as [Hz Hk1].
      apply Z.eqb_eq in Hz. subst z. apply Z.leb_le in Hk1. apply Z.leb_le in Hk2. apply Z.leb_le in Hn.
      split; [exact Hn|]. intros x Hx. cbn [edenot] in Hx. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hx.
      intros [T|[T|T]]; try lia.
      destruct T as [_ T]. apply (avoids_sound k n x Hav); [lia | exact T].
    - apply andb_prop in H as [H Hc]. apply andb_prop in H as [Hi Hn].
      apply Nat.eqb_eq in Hi. subst i. apply Z.leb_le in Hn. split; [exact Hn|].
      intros x Hx. change (edenot E (EVar 0)) with (ev E 0) in Hx. fold sp0 in Hx.
      intros [T|[T|T]].
      + destruct T as [T _].
        apply orb_prop in Hc. destruct Hc as [Hc|Hc]; [apply orb_prop in Hc; destruct Hc as [Hc|Hc]|].
        * apply Z.leb_le in Hc. lia.
        * apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2. unfold WIN in *. lia.
        * apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2. unfold WIN in *. lia.
      + apply orb_prop in Hc. destruct Hc as [Hc|Hc]; [apply orb_prop in Hc; destruct Hc as [Hc|Hc]|].
        * apply Z.leb_le in Hc. unfold WIN in *. lia.
        * apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2. unfold WIN in *. lia.
        * apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2. unfold WIN in *. lia.
      + apply orb_prop in Hc. destruct Hc as [Hc|Hc]; [apply orb_prop in Hc; destruct Hc as [Hc|Hc]|].
        * apply Z.leb_le in Hc. lia.
        * apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2. lia.
        * apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2. lia.
  Qed.

  Lemma OUTr : forall (b : expr) k n, fp_kept U slo shi ihi b k n = true ->
    flat E (SA b k) n ->
    forall j, (0 <= j < n)%Z -> M' (Z_to_bv 64 (estart E (SA b k) + j)) = M (Z_to_bv 64 (estart E (SA b k) + j)).
  Proof.
    intros b k n Hk Hf j Hj. destruct Hf as (F1 & F2 & F3 & F4).
    destruct (fp_kept_sound b k n Hk) as [_ NT].
    apply OUT. rewrite u_small by lia. apply NT. unfold estart. cbn [a_base a_off]. unfold estart in *. cbn [a_base a_off] in *. lia.
  Qed.

  Theorem know_ok_call : forall kn,
    know_ok segs E M kn -> know_ok segs E M' (kn_call U slo shi ihi dlo kn).
  Proof.
    intros kn HK. destruct Hsp as [S1 S2]. destruct Hscr as [C1 C2].
    unfold know_ok, kn_call. apply Forall_forall. intros K HinF.
    apply filter_In in HinF as [Hin Hb].
    pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
    destruct K as [[b k] w v|[b k] len|[b k] len bk|lo hi|e m|e lo hi|[b k] n|a1 n1 a2 n2]; cbn [kn_call1] in Hb.
    - (* [comment removed for export] *)
      cbn [kentry_ok] in HKK |- *. destruct HKK as (Hw & Hf & Hr). split; [exact Hw|]. split; [exact Hf|].
      rewrite <- Hr. apply rdn_agree. intros j Hj. pose proof (flat_u E _ _ Hf) as Hu. rewrite Hu.
      apply (OUTr b k (Z.of_nat w) Hb Hf). lia.
    - (* [comment removed for export] *)
      destruct len as [l| | | | | | |]; try discriminate.
      apply andb_prop in Hb as [Hl Hk]. apply andb_prop in Hl as [Hl0 Hl1].
      apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
      cbn [kentry_ok] in HKK |- *. destruct HKK as (Hf & Hz).
      assert (El : elenZ E (ELit l) = l) by (unfold elenZ; cbn [edenot]; apply u_small; lia).
      rewrite El in *. split; [exact Hf|].
      intros i Hi. rewrite (OUTr b k l Hk Hf i Hi). apply Hz. exact Hi.
    - (* [comment removed for export] *)
      destruct len as [l| | | | | | |]; try discriminate.
      apply andb_prop in Hb as [Hl Hk]. apply andb_prop in Hl as [Hl0 Hl1].
      apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
      cbn [kentry_ok] in HKK |- *. destruct HKK as (Hf & Hlen & Hz).
      assert (El : elenZ E (ELit l) = l) by (unfold elenZ; cbn [edenot]; apply u_small; lia).
      rewrite El in *. split; [exact Hf|]. split; [exact Hlen|].
      intros i Hi. rewrite (OUTr b k l Hk Hf i Hi). apply Hz. exact Hi.
    - (* [comment removed for export] *)
      apply andb_prop in Hb as [Hlh Hk]. apply Z.ltb_lt in Hlh.
      cbn [kentry_ok] in HKK |- *. destruct HKK as (H0 & H1 & Hnone). split; [exact H0|]. split; [exact H1|].
      destruct (fp_kept_sound (ELit 0) lo (hi - lo)%Z Hk) as [_ NT].
      intros i Hi. rewrite OUT; [apply Hnone; exact Hi|].
      rewrite u_small by lia. apply NT. cbn [edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia.
    - (* [comment removed for export] *) exact HKK.
    - (* [comment removed for export] *) exact HKK.
    - (* [comment removed for export] *)
      cbn [kentry_ok] in HKK |- *. destruct HKK as (Hf & Hst). split; [exact Hf|].
      pose proof Hf as Hf0. destruct Hf as (F1 & F2 & F3 & F4). unfold estart in F1, F2, F4 |- *. cbn [a_base a_off] in F1, F2, F4 |- *.
      destruct b as [z|i| | | | | |]; try discriminate.
      + (* [comment removed for export] *)
        apply andb_prop in Hb as [Hb Hn]. apply andb_prop in Hb as [Hb Hk2]. apply andb_prop in Hb as [Hz Hk1].
        apply Z.eqb_eq in Hz. subst z. apply Z.leb_le in Hk1. apply Z.leb_le in Hk2. apply Z.leb_le in Hn.
        cbn [edenot] in *. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in *.
        intros d m Hd Hm. apply SEGWR; rewrite u_small by lia; lia.
      + (* [comment removed for export] *)
        apply andb_prop in Hb as [Hb Hn]. apply andb_prop in Hb as [Hb Hk2]. apply andb_prop in Hb as [Hi Hk1].
        apply Nat.eqb_eq in Hi. subst i. apply Z.leb_le in Hk1. apply Z.leb_le in Hk2. apply Z.leb_le in Hn.
        change (edenot E (EVar 0)) with (ev E 0) in *. fold sp0 in F1, F2, F4 |- *.
        intros d m Hd Hm. pose proof (Hst d m Hd Hm) as Hok.
        eapply store_ok_mono_local; [rewrite u_small by lia; lia | | exact Hok].
        intros x Hx. rewrite u_small in Hx by lia. apply WINNN. unfold WIN in *. lia.
    - (* [comment removed for export] *) exact HKK.
  Qed.
End Sound.

(* [comment removed for export] *)
Definition entry_win_b (spi : nat) (e : sentry) : bool :=
  match e with
  | SE (SA (EVar i) k) w _ => Nat.eqb i spi && (- WIN <=? k)%Z && (k + Z.of_nat w <=? 0)%Z
  | _ => false
  end.
Definition log_win_b (spi : nat) (log : list sentry) : bool := forallb (entry_win_b spi) log.

Lemma mem_denot_out_win : forall E M log spi (x : word),
  log_win_b spi log = true ->
  (2 ^ 40 <= bv_unsigned (ev E spi))%Z ->
  ~ (bv_unsigned (ev E spi) - WIN <= bv_unsigned x < bv_unsigned (ev E spi))%Z ->
  mem_denot E M log x = M x.
Proof.
  intros E M log spi x Hb Hsp Hx. pose proof (u64_range x) as Hxr. pose proof (u64_range (ev E spi)) as Hs.
  induction log as [|[[b k] w v] rest IH]; [reflexivity|].
  cbn [log_win_b forallb] in Hb. apply andb_prop in Hb as [He Hrest].
  destruct b as [z|i| | | | | |]; try discriminate He. cbn [entry_win_b] in He.
  apply andb_prop in He as [He Hk2]. apply andb_prop in He as [Hi Hk1].
  apply Nat.eqb_eq in Hi. subst i. apply Z.leb_le in Hk1. apply Z.leb_le in Hk2. unfold WIN in *.
  cbn [mem_denot]. rewrite wbytes_outside.
  - apply IH. exact Hrest.
  - rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite u_small by lia. lia.
  - rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite u_small by lia. lia.
Qed.

(* [comment removed for export] *)
Definition entry_wd_b (spi : nat) (dlo dhi : Z) (e : sentry) : bool :=
  match e with
  | SE (SA (EVar i) k) w _ => Nat.eqb i spi && (- WIN <=? k)%Z && (k + Z.of_nat w <=? 0)%Z
  | SE (SA (ELit z) k) w _ => (z =? 0)%Z && (dlo <=? k)%Z && (k + Z.of_nat w <=? dhi)%Z
  | _ => false
  end.
Definition log_wd_b (spi : nat) (dlo dhi : Z) (log : list sentry) : bool := forallb (entry_wd_b spi dlo dhi) log.

Lemma mem_denot_out_wd : forall E M log spi dlo dhi (x : word),
  log_wd_b spi dlo dhi log = true ->
  (2 ^ 40 <= bv_unsigned (ev E spi))%Z -> (0 <= dlo)%Z -> (dhi <= 2 ^ 40 - WIN)%Z ->
  ~ (bv_unsigned (ev E spi) - WIN <= bv_unsigned x < bv_unsigned (ev E spi))%Z ->
  ~ (dlo <= bv_unsigned x < dhi)%Z ->
  mem_denot E M log x = M x.
Proof.
  intros E M log spi dlo dhi x Hb Hsp Hd0 Hd1 Hx1 Hx2. pose proof (u64_range x) as Hxr. pose proof (u64_range (ev E spi)) as Hs.
  induction log as [|[[b k] w v] rest IH]; [reflexivity|].
  cbn [log_wd_b forallb] in Hb. apply andb_prop in Hb as [He Hrest].
  cbn [mem_denot]. rewrite wbytes_outside.
  - apply IH. exact Hrest.
  - rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off].
    destruct b as [z|i| | | | | |]; try discriminate He; cbn [entry_wd_b] in He.
    + apply andb_prop in He as [He Hk2]. apply andb_prop in He as [Hz Hk1]. apply Z.eqb_eq in Hz. subst z.
      apply Z.leb_le in Hk1. apply Z.leb_le in Hk2. cbn [edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
      unfold WIN in *. rewrite u_small by lia. lia.
    + apply andb_prop in He as [He Hk2]. apply andb_prop in He as [Hi Hk1]. apply Nat.eqb_eq in Hi. subst i.
      apply Z.leb_le in Hk1. apply Z.leb_le in Hk2. cbn [edenot]. unfold WIN in *. rewrite u_small by lia. lia.
  - rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off].
    destruct b as [z|i| | | | | |]; try discriminate He; cbn [entry_wd_b] in He.
    + apply andb_prop in He as [He Hk2]. apply andb_prop in He as [Hz Hk1]. apply Z.eqb_eq in Hz. subst z.
      apply Z.leb_le in Hk1. apply Z.leb_le in Hk2. cbn [edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
      unfold WIN in *. rewrite u_small by lia. lia.
    + apply andb_prop in He as [He Hk2]. apply andb_prop in He as [Hi Hk1]. apply Nat.eqb_eq in Hi. subst i.
      apply Z.leb_le in Hk1. apply Z.leb_le in Hk2. cbn [edenot]. unfold WIN in *. rewrite u_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma mem_denot_grows : forall E M log, mem_grows M (mem_denot E M log).
Proof.
  intros E M log. induction log as [|[[b k] w v] rest IH]; [apply mem_grows_refl|].
  cbn [mem_denot]. eapply mem_grows_trans; [exact IH | apply wbytes_grows].
Qed.

(* [comment removed for export] *)
Definition entry_wdl_b (spi : nat) (rs : list (Z * Z)) (e : sentry) : bool :=
  match e with
  | SE (SA (EVar i) k) w _ => Nat.eqb i spi && (- WIN <=? k)%Z && (k + Z.of_nat w <=? 0)%Z
  | SE (SA (ELit z) k) w _ => (z =? 0)%Z && existsb (fun r : Z * Z => (fst r <=? k)%Z && (k + Z.of_nat w <=? snd r)%Z) rs
  | _ => false
  end.
Definition log_wdl_b (spi : nat) (rs : list (Z * Z)) (log : list sentry) : bool := forallb (entry_wdl_b spi rs) log.

Lemma mem_denot_out_wdl : forall E M log spi rs (x : word),
  log_wdl_b spi rs log = true ->
  (2 ^ 40 <= bv_unsigned (ev E spi))%Z ->
  Forall (fun r : Z * Z => (0 <= fst r)%Z /\ (snd r <= 2 ^ 40 - WIN)%Z) rs ->
  ~ (bv_unsigned (ev E spi) - WIN <= bv_unsigned x < bv_unsigned (ev E spi))%Z ->
  Forall (fun r : Z * Z => ~ (fst r <= bv_unsigned x < snd r)%Z) rs ->
  mem_denot E M log x = M x.
Proof.
  intros E M log spi rs x Hb Hsp Hrs Hx1 Hx2. pose proof (u64_range x) as Hxr. pose proof (u64_range (ev E spi)) as Hs.
  induction log as [|[[b k] w v] rest IH]; [reflexivity|].
  cbn [log_wdl_b forallb] in Hb. apply andb_prop in Hb as [He Hrest].
  assert (OUTk : forall z, b = ELit z ->
            (z = 0)%Z /\ exists r, In r rs /\ (fst r <= k)%Z /\ (k + Z.of_nat w <= snd r)%Z).
  { intros z ->. cbn [entry_wdl_b] in He. apply andb_prop in He as [Hz Hex]. apply Z.eqb_eq in Hz.
    apply existsb_exists in Hex as (r & Hin & Hr). apply andb_prop in Hr as [Hr1 Hr2]. apply Z.leb_le in Hr1. apply Z.leb_le in Hr2.
    split; [exact Hz|]. exists r. repeat split; assumption. }
  cbn [mem_denot]. rewrite wbytes_outside.
  - apply IH. exact Hrest.
  - rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off].
    destruct b as [z|i| | | | | |]; try discriminate He.
    + destruct (OUTk z eq_refl) as (-> & r & Hin & Hk1 & Hk2). cbn [edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
      pose proof (proj1 (Forall_forall _ _) Hrs r Hin) as [R1 R2]. unfold WIN in *. rewrite u_small by lia. lia.
    + cbn [entry_wdl_b] in He. apply andb_prop in He as [He Hk2]. apply andb_prop in He as [Hi Hk1]. apply Nat.eqb_eq in Hi. subst i.
      apply Z.leb_le in Hk1. apply Z.leb_le in Hk2. cbn [edenot]. unfold WIN in *. rewrite u_small by lia. lia.
  - rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off].
    destruct b as [z|i| | | | | |]; try discriminate He.
    + destruct (OUTk z eq_refl) as (-> & r & Hin & Hk1 & Hk2). cbn [edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
      pose proof (proj1 (Forall_forall _ _) Hrs r Hin) as [R1 R2]. pose proof (proj1 (Forall_forall _ _) Hx2 r Hin) as X2.
      unfold WIN in *. rewrite u_small by lia. lia.
    + cbn [entry_wdl_b] in He. apply andb_prop in He as [He Hk2]. apply andb_prop in He as [Hi Hk1]. apply Nat.eqb_eq in Hi. subst i.
      apply Z.leb_le in Hk1. apply Z.leb_le in Hk2. cbn [edenot]. unfold WIN in *. rewrite u_small by lia. lia.
Qed.
