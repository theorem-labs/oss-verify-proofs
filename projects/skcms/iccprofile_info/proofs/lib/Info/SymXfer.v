(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import
  PropExec CatExec CatSim SeqExec StoreOk AllocSim MmapSim Frame SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX.
Unset Nia Cache.  (* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithFP1. Context {FP : PropExec.FPState}.
Section Xfer.
  Variable segs : list Segment.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition apart_b (kn : list kentry) (wb : expr) (wk wn : Z) (b : expr) (k n : Z) : bool :=
    (expr_eqb b wb && (Z.leb (k + n) wk || Z.leb (wk + wn) k)) || ranges_apart kn wb wk wn b k n.

  Lemma apart_b_sound : forall E M kn wb wk wn b k n,
    know_ok segs E M kn -> apart_b kn wb wk wn b k n = true ->
    ((estart E (SA b k) + n <= estart E (SA wb wk))%Z
     \/ (estart E (SA wb wk) + wn <= estart E (SA b k))%Z).
  Proof.
    intros E M kn wb wk wn b k n Hkn H. unfold apart_b in H.
    apply orb_prop in H as [H|H]; [|pose proof (ranges_apart_sound segs E M kn wb wk wn b k n Hkn H); lia].
    apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1. subst b.
    unfold estart. cbn [a_base a_off]. apply orb_prop in H2 as [H2|H2]; apply Z.leb_le in H2; lia.
  Qed.

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

  Lemma estart_lit0 : forall E lo, estart E (SA (ELit 0) lo) = lo.
  Proof. intros. unfold estart. cbn [a_base a_off edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia. Qed.

  Lemma store_ok_agree : forall M M' (a : word) n,
    (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
    (forall x : word, (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n)%Z -> M' x = M x) ->
    store_ok segs M a n = true -> store_ok segs M' a n = true.
  Proof.
    intros M M' a n Hb Hag Hs.
    apply store_ok_of_all; [exact Hb|]. intros x Hx.
    pose proof (store_ok_all segs M n a Hb Hs x Hx) as H1.
    unfold wview in *. rewrite (Hag x Hx). exact H1.
  Qed.

  Theorem kentry_xfer_sound : forall E M M' kn wb wk wn grows K,
    know_ok segs E M kn ->
    (forall x : word,
        (bv_unsigned x < estart E (SA wb wk) \/ estart E (SA wb wk) + wn <= bv_unsigned x)%Z -> M' x = M x) ->
    (grows = true -> mem_grows M M') ->
    kentry_ok segs E M K -> kentry_apart_b kn wb wk wn grows K = true -> kentry_ok segs E M' K.
  Proof.
    intros E M M' kn wb wk wn grows K Hkn Hag Hg HK Hb.
    destruct K as [[b k] w v|[b k] n|[b k] n bk|lo hi|e m|e lo hi|[b k] n|a1 n1 a2 n2];
      cbn [kentry_apart_b] in Hb; cbn [kentry_ok] in HK |- *; try exact HK.
    - (* [comment removed for export] *)
      destruct HK as (Hw8 & Hfl & Hr). split; [exact Hw8|]. split; [exact Hfl|].
      pose proof (apart_b_sound E M kn _ _ _ _ _ _ Hkn Hb) as Hap.
      rewrite <- Hr. pose proof (flat_u E _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
      apply rdn_agree. intros j Hj. apply Hag. rewrite Hu. rewrite u_small by lia. lia.
    - (* [comment removed for export] *)
      destruct n as [n| | | | | | |]; try discriminate.
      destruct HK as (Hfl & Hz). rewrite elenZ_lit in *.
      pose proof (apart_b_sound E M kn _ _ _ _ _ _ Hkn Hb) as Hap.
      split; [exact Hfl|]. intros i Hi. destruct Hfl as (F1 & F2 & F3 & F4).
      rewrite Hag; [apply Hz; exact Hi|]. rewrite u_small by lia. lia.
    - (* [comment removed for export] *)
      destruct n as [n| | | | | | |]; try discriminate.
      destruct HK as (Hfl & Hlen & Hz). rewrite elenZ_lit in *.
      pose proof (apart_b_sound E M kn _ _ _ _ _ _ Hkn Hb) as Hap.
      split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi. destruct Hfl as (F1 & F2 & F3 & F4).
      rewrite Hag; [apply Hz; exact Hi|]. rewrite u_small by lia. lia.
    - (* [comment removed for export] *)
      destruct HK as (H0 & H64 & Hnone).
      pose proof (apart_b_sound E M kn _ _ _ _ _ _ Hkn Hb) as Hap. rewrite estart_lit0 in Hap.
      split; [exact H0|]. split; [exact H64|]. intros i Hi.
      rewrite Hag; [apply Hnone; exact Hi|]. rewrite u_small by lia. lia.
    - (* [comment removed for export] *)
      destruct HK as [Hfl Hst]. split; [exact Hfl|]. intros d m Hd Hm.
      apply orb_prop in Hb as [Hb|Hb].
      + eapply store_ok_mono; [exact (Hg Hb)|]. apply Hst; assumption.
      + pose proof (apart_b_sound E M kn _ _ _ _ _ _ Hkn Hb) as Hap.
        destruct Hfl as (F1 & F2 & F3 & F4).
        destruct m as [|m']; [reflexivity|].
        apply (store_ok_agree M M'); [rewrite u_small by lia; lia | | apply Hst; assumption].
        intros x Hx. apply Hag. rewrite u_small in Hx by lia. lia.
  Qed.

  Theorem kn_xfer_sound : forall E M M' kn wb wk wn grows,
    know_ok segs E M kn ->
    (forall x : word,
        (bv_unsigned x < estart E (SA wb wk) \/ estart E (SA wb wk) + wn <= bv_unsigned x)%Z -> M' x = M x) ->
    (grows = true -> mem_grows M M') ->
    know_ok segs E M' (kn_xfer kn wb wk wn grows).
  Proof.
    intros E M M' kn wb wk wn grows Hkn Hag Hg. unfold kn_xfer, know_ok.
    apply Forall_forall. intros K HK. apply filter_In in HK as [Hin Hb].
    eapply kentry_xfer_sound; try eassumption.
    unfold know_ok in Hkn. rewrite Forall_forall in Hkn. apply Hkn, Hin.
  Qed.

  (* [comment removed for export] *)
  Theorem xfer_zfill : forall E M kn wb wk (a : word) wn,
    know_ok segs E M kn -> estart E (SA wb wk) = bv_unsigned a ->
    (0 < wn < 2 ^ 64)%Z -> (bv_unsigned a + wn <= 2 ^ 64)%Z ->
    know_ok segs E (zfill a (Z_to_bv 64 wn) M)
            (KZero (SA wb wk) (ELit wn) :: KWr (SA wb wk) wn :: kn_xfer kn wb wk wn true).
  Proof.
    intros E M kn wb wk a wn Hkn He Hpos Hb.
    pose proof (u64_range a) as Ha.
    assert (Hn : bv_unsigned (Z_to_bv 64 wn) = wn) by (apply u_small; lia).
    constructor; [|constructor].
    - cbn [kentry_ok]. rewrite elenZ_lit, Z.mod_small by lia. unfold flat. rewrite He.
      split; [lia|]. intros i Hi. unfold zfill, zmem. rewrite (u_small (bv_unsigned a + i)) by lia.
      rewrite Hn.
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
    - cbn [kentry_ok]. unfold flat. rewrite He. split; [lia|]. intros d m Hd Hm.
      destruct m as [|m']; [reflexivity|].
      unfold zfill. apply store_ok_zmem; rewrite ?u_small by lia; lia.
    - eapply kn_xfer_sound; [exact Hkn | | intros _; unfold zfill; apply zmem_grows].
      intros x Hx. unfold zfill. apply zmem_out. rewrite Hn. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem xfer_unfill : forall E M kn wb wk (a : word) wn,
    know_ok segs E M kn -> estart E (SA wb wk) = bv_unsigned a ->
    (0 < wn < 2 ^ 64)%Z -> (bv_unsigned a + wn <= 2 ^ 64)%Z ->
    know_ok segs E (unfill a (Z_to_bv 64 wn) M) (kn_xfer kn wb wk wn false).
  Proof.
    intros E M kn wb wk a wn Hkn He Hpos Hb.
    pose proof (u64_range a) as Ha.
    assert (Hn : bv_unsigned (Z_to_bv 64 wn) = wn) by (apply u_small; lia).
    eapply kn_xfer_sound; [exact Hkn | | intros H; discriminate H].
    intros x Hx. apply unfill_out. rewrite Hn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma know_ok_filter : forall E M kn (f : kentry -> bool),
    know_ok segs E M kn -> know_ok segs E M (List.filter f kn).
  Proof.
    intros E M kn f Hkn. unfold know_ok in *. apply Forall_forall. intros K HK.
    apply filter_In in HK as [Hin _]. rewrite Forall_forall in Hkn. apply Hkn, Hin.
  Qed.

  Lemma know_ok_incl : forall E M kn kn',
    incl kn' kn -> know_ok segs E M kn -> know_ok segs E M kn'.
  Proof.
    intros E M kn kn' Hi Hkn. unfold know_ok in *. apply Forall_forall. intros K HK.
    rewrite Forall_forall in Hkn. apply Hkn, Hi, HK.
  Qed.

  (* [comment removed for export] *)
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

  Lemma kn_inclb_sound : forall kn' kn, kn_inclb kn' kn = true -> incl kn' kn.
  Proof.
    intros kn' kn H K HK. unfold kn_inclb in H. rewrite forallb_forall in H.
    specialize (H K HK). apply existsb_exists in H as (K' & Hin & Heq).
    apply kentry_eqb_eq in Heq. subst. exact Hin.
  Qed.

  Lemma know_ok_sub : forall E M kn kn',
    kn_inclb kn' kn = true -> know_ok segs E M kn -> know_ok segs E M kn'.
  Proof. intros. eapply know_ok_incl; [apply kn_inclb_sound|]; eassumption. Qed.
  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition zbytes_eqb (bs : list byte) (w : nat) (v : Z) : bool :=
    Nat.eqb (length bs) w && Z.eqb (bytes_le_to_Z bs) v.

  Definition kderive (kn : list kentry) (K : kentry) : bool :=
    existsb (kentry_eqb K) kn ||
    match K with
    | KWord (SA b k) w (ELit v) =>
        (Nat.leb 1 w && Nat.leb w 8) &&
        ((* [comment removed for export] *)
         (Z.eqb v 0 &&
          existsb (fun K0 => match K0 with
                             | KZero (SA b' k') (ELit n) =>
                                 expr_eqb b b' && Z.leb k' k && Z.leb (k + Z.of_nat w) (k' + n)
                                 && Z.leb 0 n && Z.ltb n (2 ^ 64)
                             | _ => false end) kn)
         ||
         (* [comment removed for export] *)
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
    - (* [comment removed for export] *)
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
    - (* [comment removed for export] *)
      destruct n as [n| | | | | | |]; try discriminate.
      apply andb_prop in Hd as [Hn Hd]. apply Z.ltb_lt in Hn.
      apply existsb_exists in Hd as (K0 & Hin & Hc).
      destruct K0 as [|[b' k'] [n'| | | | | | |]| | | | | |]; try discriminate.
      repeat match goal with G : (_ && _)%bool = true |- _ => apply andb_prop in G; destruct G end.
      apply expr_eqb_eq in H. subst b'.
      repeat match goal with G : (_ <=? _)%Z = true |- _ => apply Z.leb_le in G | G : (_ <? _)%Z = true |- _ => apply Z.ltb_lt in G end.
      pose proof (know_in _ _ _ _ HK Hin) as HZ.
      replace k with (k' + (k - k'))%Z by lia. eapply kzero_sub; [exact HZ | lia | lia | lia | lia].
    - (* [comment removed for export] *)
      apply existsb_exists in Hd as (K0 & Hin & Hc).
      destruct K0 as [| | |lo' hi'| | | |]; try discriminate.
      repeat match goal with G : (_ && _)%bool = true |- _ => apply andb_prop in G; destruct G end.
      repeat match goal with G : (_ <=? _)%Z = true |- _ => apply Z.leb_le in G end.
      pose proof (know_in _ _ _ _ HK Hin) as HI. cbn [kentry_ok] in HI |- *. destruct HI as (A & B & C).
      split; [lia|]. split; [lia|]. intros i Hi. apply C. lia.
    - (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

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

  (* [comment removed for export] *)
  Fixpoint eok (l : list nat) (e : expr) : bool :=
    match e with
    | ELit _ => true
    | EVar n => existsb (Nat.eqb n) l
    | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => eok l a && eok l b
    | EExt _ _ _ a => eok l a
    | EBlob _ _ _ _ => false
    end.

  Lemma edenot_ren : forall E E' f l e,
    (forall i, In i l -> ev E' i = ev E (f i)) -> eok l e = true -> edenot E' e = edenot E (eren f e).
  Proof.
    intros E E' f l e Hev. induction e; cbn [eren edenot eok]; intros Hb;
      repeat match goal with G : (_ && _)%bool = true |- _ => apply andb_prop in G; destruct G end;
      try reflexivity;
      try (rewrite IHe1, IHe2 by assumption; reflexivity);
      try (rewrite IHe by assumption; reflexivity).
    - apply Hev. apply existsb_exists in Hb as (j & Hin & Hj). apply Nat.eqb_eq in Hj. subst j. exact Hin.
    - discriminate.
  Qed.

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

  Lemma kentry_ok_ren : forall E E' M f l K,
    (forall i, In i l -> ev E' i = ev E (f i)) -> kok l K = true ->
    kentry_ok segs E M (kren f K) -> kentry_ok segs E' M K.
  Proof.
    intros E E' M f l K Hev Hb HK.
    assert (AD : forall a, eok l (a_base a) = true -> adenot E' a = adenot E (aren f a)).
    { intros [b k] H. unfold adenot, aren. cbn [a_base a_off]. rewrite (edenot_ren E E' f l b Hev H). reflexivity. }
    assert (ES : forall a, eok l (a_base a) = true -> estart E' a = estart E (aren f a)).
    { intros [b k] H. unfold estart, aren. cbn [a_base a_off]. rewrite (edenot_ren E E' f l b Hev H). reflexivity. }
    assert (FL : forall a n, eok l (a_base a) = true -> flat E (aren f a) n -> flat E' a n).
    { intros a n H Hf. unfold flat in *. rewrite (ES a H). exact Hf. }
    destruct K as [a w v|a n|a n bk|lo hi|e m|e lo hi|a n|a1 n1 a2 n2]; cbn [kren kok kentry_ok] in *;
      repeat match goal with G : (_ && _)%bool = true |- _ => apply andb_prop in G; destruct G end;
      try discriminate.
    - destruct HK as (A & B & C). split; [exact A|]. split; [apply FL; assumption|].
      rewrite (AD a), (edenot_ren E E' f l v) by assumption. exact C.
    - destruct HK as [A B]. unfold elenZ in *. rewrite (edenot_ren E E' f l n) by assumption.
      split; [apply FL; assumption|]. intros i Hi. rewrite (ES a) by assumption. apply B. exact Hi.
    - exact HK.
    - rewrite (edenot_ren E E' f l e) by assumption. exact HK.
    - rewrite (edenot_ren E E' f l e) by assumption. exact HK.
    - destruct HK as [A B]. split; [apply FL; assumption|]. intros d m Hd Hm. rewrite (ES a) by assumption. apply B; assumption.
    - rewrite (ES a1), (ES a2) by assumption. exact HK.
  Qed.

  Theorem know_ok_ren : forall E E' M f l kn,
    (forall i, In i l -> ev E' i = ev E (f i)) -> forallb (kok l) kn = true ->
    know_ok segs E M (map (kren f) kn) -> know_ok segs E' M kn.
  Proof.
    intros E E' M f l kn Hev Hb HK. unfold know_ok in *. rewrite forallb_forall in Hb.
    apply Forall_forall. intros K HKin. eapply kentry_ok_ren; [exact Hev | apply Hb, HKin |].
    rewrite Forall_forall in HK. apply HK. apply in_map. exact HKin.
  Qed.
End Xfer.
End WithFP1.

