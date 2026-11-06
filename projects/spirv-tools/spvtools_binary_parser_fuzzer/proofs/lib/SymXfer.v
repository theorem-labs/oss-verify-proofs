(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk AllocSim MmapSim Frame SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Xfer.
  Variable segs : list Segment.

  Definition apart_b (kn : list kentry) (wb : expr) (wk wn : Z) (b : expr) (k n : Z) : bool :=
    (expr_eqb b wb && (Z.leb (k + n) wk || Z.leb (wk + wn) k)) || ranges_apart kn wb wk wn b k n.

  Definition kentry_apart_b (kn : list kentry) (wb : expr) (wk wn : Z) (grows : bool) (K : kentry) : bool :=
    match K with
    | KWord (SA b k) w _ => apart_b kn wb wk wn b k (Z.of_nat w)
    | KZero (SA b k) (ELit n) => apart_b kn wb wk wn b k (n mod 2 ^ 64)%Z
    | KZero _ _ => false
    | KBlob (SA b k) (ELit n) _ => apart_b kn wb wk wn b k (n mod 2 ^ 64)%Z
    | KBlob _ _ _ => false
    | KImg lo hi => apart_b kn wb wk wn (ELit 0) lo (hi - lo)%Z
    | KAlign _ _ => true
    | KRange _ _ _ => true
    | KDisj _ _ _ _ => true
    | KWr (SA b k) n => grows || apart_b kn wb wk wn b k n
    end.

  Definition kn_xfer (kn : list kentry) (wb : expr) (wk wn : Z) (grows : bool) : list kentry :=
    List.filter (kentry_apart_b kn wb wk wn grows) kn.

  Lemma elenZ_lit : forall E n, elenZ E (ELit n) = (n mod 2 ^ 64)%Z.
  Proof. intros. unfold elenZ. cbn [edenot]. rewrite Z_to_bv_unsigned, bv_wrap64_mod. reflexivity. Qed.

  Definition kentry_eqb (a b : kentry) : bool :=
    match a, b with
    | KWord a1 w1 v1, KWord a2 w2 v2 => saddr_eqb a1 a2 && Nat.eqb w1 w2 && expr_eqb v1 v2
    | KZero a1 n1, KZero a2 n2 => saddr_eqb a1 a2 && expr_eqb n1 n2
    | KBlob a1 n1 k1, KBlob a2 n2 k2 => saddr_eqb a1 a2 && expr_eqb n1 n2 && Nat.eqb k1 k2
    | KImg l1 h1, KImg l2 h2 => Z.eqb l1 l2 && Z.eqb h1 h2
    | KAlign e1 m1, KAlign e2 m2 => expr_eqb e1 e2 && Z.eqb m1 m2
    | KRange e1 l1 h1, KRange e2 l2 h2 => expr_eqb e1 e2 && Z.eqb l1 l2 && Z.eqb h1 h2
    | KWr a1 n1, KWr a2 n2 => saddr_eqb a1 a2 && Z.eqb n1 n2
    | KDisj a1 n1 b1 m1, KDisj a2 n2 b2 m2 => saddr_eqb a1 a2 && Z.eqb n1 n2 && saddr_eqb b1 b2 && Z.eqb m1 m2
    | _, _ => false
    end.

  Lemma kentry_eqb_eq : forall a b, kentry_eqb a b = true -> a = b.
  Proof.
    intros a b H. destruct a, b; cbn [kentry_eqb] in H; try discriminate;
      repeat match goal with s : saddr |- _ => destruct s end;
      unfold saddr_eqb in H; cbn [a_base a_off] in H;
      repeat match goal with G : (_ && _)%bool = true |- _ => apply andb_prop in G; destruct G end;
      repeat match goal with
             | H : saddr_eqb _ _ = true |- _ => apply saddr_eqb_eq in H
             | H : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in H
             | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
             | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
             end; subst; reflexivity.
  Qed.

  Definition kn_inclb (kn' kn : list kentry) : bool :=
    forallb (fun K => existsb (kentry_eqb K) kn) kn'.

  Lemma kzero_sub : forall E M b k n d m,
    kentry_ok segs E M (KZero (SA b k) (ELit n)) -> (0 <= n < 2 ^ 64)%Z ->
    (0 <= d)%Z -> (0 < m)%Z -> (d + m <= n)%Z ->
    kentry_ok segs E M (KZero (SA b (k + d)) (ELit m)).
  Proof.
    intros E M b k n d m HK Hn Hd Hm Hdm. cbn [kentry_ok] in *. rewrite !elenZ_lit in *.
    rewrite !Z.mod_small in * by lia. destruct HK as [Hfl Hz].
    unfold flat, estart in *. cbn [a_base a_off] in *. split; [lia|].
    intros i Hi. replace (bv_unsigned (edenot E b) + (k + d) + i)%Z with (bv_unsigned (edenot E b) + k + (d + i))%Z by lia.
    apply Hz. lia.
  Qed.

  Lemma kwr_sub : forall E M b k n d m,
    kentry_ok segs E M (KWr (SA b k) n) -> (0 <= d)%Z -> (0 < m)%Z -> (d + m <= n)%Z ->
    kentry_ok segs E M (KWr (SA b (k + d)) m).
  Proof.
    intros E M b k n d m HK Hd Hm Hdm. cbn [kentry_ok] in *. destruct HK as [Hfl Hs].
    unfold flat, estart in *. cbn [a_base a_off] in *. split; [lia|].
    intros d' m' Hd' Hm'. replace (bv_unsigned (edenot E b) + (k + d) + d')%Z with (bv_unsigned (edenot E b) + k + (d + d'))%Z by lia.
    apply Hs; lia.
  Qed.

  Definition zbytes_eqb (bs : list byte) (w : nat) (v : Z) : bool :=
    Nat.eqb (length bs) w && Z.eqb (bytes_le_to_Z bs) v.

  Definition kderive (kn : list kentry) (K : kentry) : bool :=
    existsb (kentry_eqb K) kn ||
    match K with
    | KWord (SA b k) w (ELit v) =>
        (Nat.leb 1 w && Nat.leb w 8) &&
        (
         (Z.eqb v 0 &&
          existsb (fun K0 => match K0 with
                             | KZero (SA b' k') (ELit n) =>
                                 expr_eqb b b' && Z.leb k' k && Z.leb (k + Z.of_nat w) (k' + n)
                                 && Z.leb 0 n && Z.ltb n (2 ^ 64)
                             | _ => false end) kn)
         ||

         match b with
         | ELit 0 =>
             existsb (fun K0 => match K0 with
                                | KImg lo hi => Z.leb lo k && Z.leb (k + Z.of_nat w) hi
                                | _ => false end) kn
             && match rdn segs (fun _ => None) (Z_to_bv 64 k) w with
                | Some bs => zbytes_eqb bs w v
                | None => false
                end
         | _ => false
         end)
    | KZero (SA b k) (ELit n) =>
        Z.ltb 0 n &&
        existsb (fun K0 => match K0 with
                           | KZero (SA b' k') (ELit n') =>
                               expr_eqb b b' && Z.leb k' k && Z.leb (k + n) (k' + n')
                               && Z.leb 0 n' && Z.ltb n' (2 ^ 64)
                           | _ => false end) kn
    | KImg lo hi =>
        existsb (fun K0 => match K0 with
                           | KImg lo' hi' => Z.leb lo' lo && Z.leb hi hi' && Z.leb lo hi
                           | _ => false end) kn
    | KWr (SA b k) n =>
        Z.ltb 0 n &&
        existsb (fun K0 => match K0 with
                           | KWr (SA b' k') n' => expr_eqb b b' && Z.leb k' k && Z.leb (k + n) (k' + n')
                           | _ => false end) kn
    | _ => false
    end.

  Lemma know_in : forall E M kn K, know_ok segs E M kn -> In K kn -> kentry_ok segs E M K.
  Proof. intros E M kn K HK Hin. unfold know_ok in HK. rewrite Forall_forall in HK. apply HK, Hin. Qed.

  Lemma rdn_zero_bytes : forall M (a : Z) (w : nat),
    (0 <= a)%Z -> (a + Z.of_nat w <= 2 ^ 64)%Z ->
    (forall i, (0 <= i < Z.of_nat w)%Z -> M (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0)) ->
    rdn segs M (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 0)).
  Proof.
    intros M a w. revert a. induction w as [|w IH]; intros a H0 Hb Hz; [reflexivity|].
    cbn [rdn]. pose proof (Hz 0%Z ltac:(lia)) as Hz0. rewrite Z.add_0_r in Hz0. rewrite Hz0.
    replace (Z_to_bv 64 a + 1) with (Z_to_bv 64 (a + 1)).
    2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
        change (1 mod 2 ^ 64)%Z with 1%Z. rewrite Zplus_mod_idemp_l. reflexivity. }
    destruct w as [|w'].
    - reflexivity.
    - rewrite (IH (a + 1)%Z); [reflexivity | lia | lia |].
      intros i Hi. replace (a + 1 + i)%Z with (a + (1 + i))%Z by lia. apply Hz. lia.
  Qed.

  Theorem kderive_sound : forall E M kn K,
    know_ok segs E M kn -> kderive kn K = true -> kentry_ok segs E M K.
  Proof.
    intros E M kn K HK Hd. unfold kderive in Hd.
    apply orb_prop in Hd as [Hd|Hd].
    { apply existsb_exists in Hd as (K' & Hin & Heq). apply kentry_eqb_eq in Heq. subst K'. exact (know_in _ _ _ _ HK Hin). }
    destruct K as [[b k] w v|[b k] n|a n bk|lo hi|e m|e lo hi|[b k] n|a1 n1 a2 n2]; try discriminate.
    -
      destruct v as [v| | | | | | |]; try discriminate.
      apply andb_prop in Hd as [Hw Hd]. apply andb_prop in Hw as [Hw1 Hw8].
      apply Nat.leb_le in Hw1. apply Nat.leb_le in Hw8.
      apply orb_prop in Hd as [Hd|Hd].
      + apply andb_prop in Hd as [Hv Hd]. apply Z.eqb_eq in Hv. subst v.
        apply existsb_exists in Hd as (K0 & Hin & Hc).
        destruct K0 as [|[b' k'] [n| | | | | | |]| | | | | |]; try discriminate.
        repeat match goal with G : (_ && _)%bool = true |- _ => apply andb_prop in G; destruct G end.
        apply expr_eqb_eq in H. subst b'.
        repeat match goal with G : (_ <=? _)%Z = true |- _ => apply Z.leb_le in G | G : (_ <? _)%Z = true |- _ => apply Z.ltb_lt in G end.
        pose proof (know_in _ _ _ _ HK Hin) as HZ. cbn [kentry_ok] in HZ. rewrite elenZ_lit, Z.mod_small in HZ by lia.
        destruct HZ as [Hfl Hz]. unfold flat, estart in Hfl |- *. cbn [kentry_ok a_base a_off] in *.
        split; [exact Hw8|]. split; [unfold flat, estart; cbn [a_base a_off]; lia|].
        unfold adenot, v_addi. cbn [a_base a_off edenot].
        apply rdn_zero_bytes; [lia | lia |]. intros i Hi.
        replace (bv_unsigned (edenot E b) + k + i)%Z with (bv_unsigned (edenot E b) + k' + (k - k' + i))%Z by lia.
        apply Hz. lia.
      + destruct b as [[|p|p]| | | | | | |]; try discriminate.
        apply andb_prop in Hd as [Hc Hr]. apply existsb_exists in Hc as (K0 & Hin & Hc).
        destruct K0 as [| | |lo hi| | | |]; try discriminate.
        apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
        pose proof (know_in _ _ _ _ HK Hin) as HI. cbn [kentry_ok] in HI. destruct HI as (Hlo & Hhi & Hnone).
        destruct (rdn segs (fun _ => None) (Z_to_bv 64 k) w) as [bs|] eqn:Hrd; [|discriminate].
        unfold zbytes_eqb in Hr. apply andb_prop in Hr as [Hl Hbz]. apply Nat.eqb_eq in Hl. apply Z.eqb_eq in Hbz.
        cbn [kentry_ok]. split; [exact Hw8|]. split; [unfold flat, estart; cbn [a_base a_off edenot]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia|].
        rewrite adenot_lit0. cbn [edenot]. rewrite (rdn_untouched segs M k w) by (try lia; intros i Hi; apply Hnone; lia).
        rewrite Hrd, <- Hbz, word_to_le_bytes_of_lez by assumption. reflexivity.
    -
      destruct n as [n| | | | | | |]; try discriminate.
      apply andb_prop in Hd as [Hn Hd]. apply Z.ltb_lt in Hn.
      apply existsb_exists in Hd as (K0 & Hin & Hc).
      destruct K0 as [|[b' k'] [n'| | | | | | |]| | | | | |]; try discriminate.
      repeat match goal with G : (_ && _)%bool = true |- _ => apply andb_prop in G; destruct G end.
      apply expr_eqb_eq in H. subst b'.
      repeat match goal with G : (_ <=? _)%Z = true |- _ => apply Z.leb_le in G | G : (_ <? _)%Z = true |- _ => apply Z.ltb_lt in G end.
      pose proof (know_in _ _ _ _ HK Hin) as HZ.
      replace k with (k' + (k - k'))%Z by lia. eapply kzero_sub; [exact HZ | lia | lia | lia | lia].
    -
      apply existsb_exists in Hd as (K0 & Hin & Hc).
      destruct K0 as [| | |lo' hi'| | | |]; try discriminate.
      repeat match goal with G : (_ && _)%bool = true |- _ => apply andb_prop in G; destruct G end.
      repeat match goal with G : (_ <=? _)%Z = true |- _ => apply Z.leb_le in G end.
      pose proof (know_in _ _ _ _ HK Hin) as HI. cbn [kentry_ok] in HI |- *. destruct HI as (A & B & C).
      split; [lia|]. split; [lia|]. intros i Hi. apply C. lia.
    -
      apply andb_prop in Hd as [Hn Hd]. apply Z.ltb_lt in Hn.
      apply existsb_exists in Hd as (K0 & Hin & Hc).
      destruct K0 as [| | | | | |[b' k'] n'|]; try discriminate.
      repeat match goal with G : (_ && _)%bool = true |- _ => apply andb_prop in G; destruct G end.
      apply expr_eqb_eq in H. subst b'.
      repeat match goal with G : (_ <=? _)%Z = true |- _ => apply Z.leb_le in G end.
      pose proof (know_in _ _ _ _ HK Hin) as HW.
      replace k with (k' + (k - k'))%Z by lia. eapply kwr_sub; [exact HW | lia | lia | lia].
  Qed.

  Definition kderive_all (kn kn' : list kentry) : bool := forallb (kderive kn) kn'.

  Theorem kderive_all_sound : forall E M kn kn',
    know_ok segs E M kn -> kderive_all kn kn' = true -> know_ok segs E M kn'.
  Proof.
    intros E M kn kn' HK H. unfold kderive_all in H. rewrite forallb_forall in H.
    unfold know_ok. apply Forall_forall. intros K HKin. eapply kderive_sound; [exact HK | apply H, HKin].
  Qed.

  Fixpoint eren (f : nat -> nat) (e : expr) : expr :=
    match e with
    | ELit z => ELit z
    | EVar n => EVar (f n)
    | EAlu op a b => EAlu op (eren f a) (eren f b)
    | EAluw op a b => EAluw op (eren f a) (eren f b)
    | EMd op a b => EMd op (eren f a) (eren f b)
    | EMdw op a b => EMdw op (eren f a) (eren f b)
    | EExt sx lo n a => EExt sx lo n (eren f a)
    | EBlob sx k i n => EBlob sx k i n
    end.

  Fixpoint eok (l : list nat) (e : expr) : bool :=
    match e with
    | ELit _ => true
    | EVar n => existsb (Nat.eqb n) l
    | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => eok l a && eok l b
    | EExt _ _ _ a => eok l a
    | EBlob _ _ _ _ => false
    end.

  Definition aren (f : nat -> nat) (a : saddr) : saddr := SA (eren f (a_base a)) (a_off a).

  Definition kren (f : nat -> nat) (K : kentry) : kentry :=
    match K with
    | KWord a w v => KWord (aren f a) w (eren f v)
    | KZero a n => KZero (aren f a) (eren f n)
    | KBlob a n k => KBlob (aren f a) (eren f n) k
    | KImg lo hi => KImg lo hi
    | KAlign e m => KAlign (eren f e) m
    | KRange e lo hi => KRange (eren f e) lo hi
    | KWr a n => KWr (aren f a) n
    | KDisj a1 n1 a2 n2 => KDisj (aren f a1) n1 (aren f a2) n2
    end.

  Definition kok (l : list nat) (K : kentry) : bool :=
    match K with
    | KWord a _ v => eok l (a_base a) && eok l v
    | KZero a n => eok l (a_base a) && eok l n
    | KBlob _ _ _ => false
    | KImg _ _ => true
    | KAlign e _ => eok l e
    | KRange e _ _ => eok l e
    | KWr a _ => eok l (a_base a)
    | KDisj a1 _ a2 _ => eok l (a_base a1) && eok l (a_base a2)
    end.

End Xfer.
