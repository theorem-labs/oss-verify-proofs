(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec StoreOk ShapeAlg SpinAlg AxSymExec3 AxSymExec3Sound AsanPlanCore CxPlan CxPlanSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxRel.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zj_range (wr : bool) (K : kentry) : option (expr * Z * expr) :=
  match K, wr with
  | KZero (SA b k) n, false => Some (b, k, n)
  | KWr (SA b k) n, true => Some (b, k, n)
  | _, _ => None
  end.

(* [comment removed for export] *)
Fixpoint zj_second (allk k : list kentry) (wr : bool) (b1 : expr) (k1 : Z) (n1 : expr) (tb : expr) (tk : Z) (tn : expr) : bool :=
  match k with
  | [] => false
  | K :: r =>
      match zj_range wr K with
      | Some (b2, k2, n2) =>
          if (lin_ge0 allk [(b1, k1); (n1, 0)] [(b2, k2)] && lin_ge0 allk [(b2, k2); (n2, 0)] [(tb, tk); (tn, 0)])%bool then true
          else zj_second allk r wr b1 k1 n1 tb tk tn
      | None => zj_second allk r wr b1 k1 n1 tb tk tn
      end
  end.

(* [comment removed for export] *)
Fixpoint zj_first (allk k : list kentry) (wr : bool) (tb : expr) (tk : Z) (tn : expr) : bool :=
  match k with
  | [] => false
  | K :: r =>
      match zj_range wr K with
      | Some (b1, k1, n1) =>
          if (lin_ge0 allk [(tb, tk)] [(b1, k1)] && lin_ge0 allk [(b1, k1); (n1, -1)] [(tb, tk)] && zj_second allk allk wr b1 k1 n1 tb tk tn)%bool then true
          else zj_first allk r wr tb tk tn
      | None => zj_first allk r wr tb tk tn
      end
  end.

(* [comment removed for export] *)
Definition zj_target (cs : acs) (args : list expr) : option (expr * expr) :=
  match args with
  | [te; tn] => Some (te, tn)
  | [] => Some (reg cs 10, reg cs 12)
  | _ => None
  end.

Definition node_zjoin (cs : acs) (args : list expr) : option acs :=
  match zj_target cs args with
  | Some (te, tn) =>
      let k := kn cs in
      let '(tb, tk) := split_lit te in
      if (expr_vars_lt (nxt cs) te && expr_vars_lt (nxt cs) tn && zj_first k k false tb tk tn && zj_first k k true tb tk tn)%bool
      then Some (set_kn cs (KWr (SA tb tk) tn :: KZero (SA tb tk) tn :: k))
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition zj_xn (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 60 then node_zjoin cs args else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
  Variable SEGS : list Segment.

  Lemma zj_range_sound : forall wr K b k n, zj_range wr K = Some (b, k, n) ->
    K = (if wr then KWr (SA b k) n else KZero (SA b k) n).
  Proof.
    intros wr K b k n H. destruct K as [a ? ?|a ?|a ? ?|? ?|? ?|? ? ?|a ?|a ? ? ?|a ? ?|a ?]; try destruct a as [bb0 kk0]; destruct wr; cbn [zj_range] in H; try discriminate;
      inversion H; subst; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma zj_second_sound : forall E M allk wr b1 k1 n1 tb tk tn k,
    know_ok SEGS E M allk -> (forall K, In K k -> In K allk) ->
    zj_second allk k wr b1 k1 n1 tb tk tn = true ->
    exists b2 k2 n2, In (if wr then KWr (SA b2 k2) n2 else KZero (SA b2 k2) n2) allk
      /\ estart E (SA b2 k2) <= estart E (SA b1 k1) + elenZ E n1
      /\ estart E (SA tb tk) + elenZ E tn <= estart E (SA b2 k2) + elenZ E n2.
  Proof.
    intros E M allk wr b1 k1 n1 tb tk tn k HK. induction k as [|K r IH]; intros Hin H; cbn [zj_second] in H; [discriminate|].
    assert (Hr : forall K0, In K0 r -> In K0 allk) by (intros K0 H0; apply Hin; right; exact H0).
    destruct (zj_range wr K) as [[[b2 k2] n2]|] eqn:Er; [|exact (IH Hr H)].
    destruct (lin_ge0 allk [(b1, k1); (n1, 0)] [(b2, k2)] && lin_ge0 allk [(b2, k2); (n2, 0)] [(tb, tk); (tn, 0)])%bool eqn:Eb; [|exact (IH Hr H)].
    apply andb_prop in Eb as [E1 E2].
    pose proof (lin_ge0_sound SEGS E M allk _ _ HK E1) as A1. pose proof (lin_ge0_sound SEGS E M allk _ _ HK E2) as A2.
    cbn [xt_den] in A1, A2. unfold estart, elenZ. cbn [a_base a_off].
    exists b2, k2, n2. split; [|split; lia].
    rewrite <- (zj_range_sound wr K b2 k2 n2 Er). apply Hin. left. reflexivity.
  Qed.

  Lemma zj_first_sound : forall E M allk wr tb tk tn k,
    know_ok SEGS E M allk -> (forall K, In K k -> In K allk) ->
    zj_first allk k wr tb tk tn = true ->
    exists b1 k1 n1 b2 k2 n2,
      In (if wr then KWr (SA b1 k1) n1 else KZero (SA b1 k1) n1) allk
      /\ In (if wr then KWr (SA b2 k2) n2 else KZero (SA b2 k2) n2) allk
      /\ estart E (SA b1 k1) <= estart E (SA tb tk) < estart E (SA b1 k1) + elenZ E n1
      /\ estart E (SA b2 k2) <= estart E (SA b1 k1) + elenZ E n1
      /\ estart E (SA tb tk) + elenZ E tn <= estart E (SA b2 k2) + elenZ E n2.
  Proof.
    intros E M allk wr tb tk tn k HK. induction k as [|K r IH]; intros Hin H; cbn [zj_first] in H; [discriminate|].
    assert (Hr : forall K0, In K0 r -> In K0 allk) by (intros K0 H0; apply Hin; right; exact H0).
    destruct (zj_range wr K) as [[[b1 k1] n1]|] eqn:Er; [|exact (IH Hr H)].
    destruct (lin_ge0 allk [(tb, tk)] [(b1, k1)] && lin_ge0 allk [(b1, k1); (n1, -1)] [(tb, tk)] && zj_second allk allk wr b1 k1 n1 tb tk tn)%bool eqn:Eb; [|exact (IH Hr H)].
    apply andb_prop in Eb as [E1 E2]. apply andb_prop in E1 as [E1 E1'].
    pose proof (lin_ge0_sound SEGS E M allk _ _ HK E1) as A1. cbn [xt_den] in A1.
    pose proof (lin_ge0_sound SEGS E M allk _ _ HK E1') as A1'. cbn [xt_den] in A1'.
    destruct (zj_second_sound E M allk wr b1 k1 n1 tb tk tn allk HK (fun K0 H0 => H0) E2) as (b2 & k2 & n2 & I2 & B1 & B2).
    exists b1, k1, n1, b2, k2, n2. split; [|split; [exact I2|split; [|split; [exact B1|exact B2]]]].
    - rewrite <- (zj_range_sound wr K b1 k1 n1 Er). apply Hin. left. reflexivity.
    - unfold estart, elenZ. cbn [a_base a_off]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma zjoin_zero_ok : forall E M allk tb tk tn,
    know_ok SEGS E M allk -> zj_first allk allk false tb tk tn = true -> kentry_ok SEGS E M (KZero (SA tb tk) tn).
  Proof.
    intros E M allk tb tk tn HK H.
    destruct (zj_first_sound E M allk false tb tk tn allk HK (fun K0 H0 => H0) H) as (b1 & k1 & n1 & b2 & k2 & n2 & I1 & I2 & B0 & B1 & B2).
    pose proof (proj1 (Forall_forall _ _) HK _ I1) as [F1 Z1]. pose proof (proj1 (Forall_forall _ _) HK _ I2) as [F2 Z2].
    pose proof (u64_range (edenot E tn)) as Rn. unfold elenZ in *.
    destruct F1 as (F1a & F1b & F1c & F1d). destruct F2 as (F2a & F2b & F2c & F2d).
    cbn [kentry_ok]. split.
    - unfold flat, elenZ. repeat split; lia.
    - intros i Hi. unfold elenZ in Hi.
      destruct (Z_lt_le_dec (estart E (SA tb tk) + i) (estart E (SA b1 k1) + bv_unsigned (edenot E n1))) as [Hl|Hl].
      + replace (estart E (SA tb tk) + i) with (estart E (SA b1 k1) + (estart E (SA tb tk) + i - estart E (SA b1 k1))) by lia.
        apply Z1. lia.
      + replace (estart E (SA tb tk) + i) with (estart E (SA b2 k2) + (estart E (SA tb tk) + i - estart E (SA b2 k2))) by lia.
        apply Z2. lia.
  Qed.

  Lemma zjoin_wr_ok : forall E M allk tb tk tn,
    know_ok SEGS E M allk -> zj_first allk allk true tb tk tn = true -> kentry_ok SEGS E M (KWr (SA tb tk) tn).
  Proof.
    intros E M allk tb tk tn HK H.
    destruct (zj_first_sound E M allk true tb tk tn allk HK (fun K0 H0 => H0) H) as (b1 & k1 & n1 & b2 & k2 & n2 & I1 & I2 & B0 & B1 & B2).
    pose proof (proj1 (Forall_forall _ _) HK _ I1) as [F1 W1]. pose proof (proj1 (Forall_forall _ _) HK _ I2) as [F2 W2].
    pose proof (u64_range (edenot E tn)) as Rn. unfold elenZ in *.
    destruct F1 as (F1a & F1b & F1c & F1d). destruct F2 as (F2a & F2b & F2c & F2d).
    cbn [kentry_ok]. split.
    - unfold flat, elenZ. repeat split; lia.
    - intros d m Hd Hm. unfold elenZ in Hm.
      assert (Hu : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z).
      { intros z Hz. rewrite Z_to_bv_unsigned, bv_wrap64_mod. apply Z.mod_small. exact Hz. }
      destruct m as [|m']; [reflexivity|].
      apply store_ok_of_all.
      + rewrite Hu by lia. lia.
      + intros x Hx. rewrite Hu in Hx by lia.
        destruct (Z_lt_le_dec (bv_unsigned x) (estart E (SA b1 k1) + bv_unsigned (edenot E n1))) as [Hl|Hl].
        * pose proof (W1 (bv_unsigned x - estart E (SA b1 k1)) 1%nat ltac:(lia) ltac:(cbn; lia)) as S1.
          replace (estart E (SA b1 k1) + (bv_unsigned x - estart E (SA b1 k1))) with (bv_unsigned x) in S1 by lia.
          rewrite Z_to_bv_bv_unsigned in S1.
          apply (store_ok_all SEGS M 1 x ltac:(pose proof (u64_range x); cbn; lia) S1 x). cbn. lia.
        * pose proof (W2 (bv_unsigned x - estart E (SA b2 k2)) 1%nat ltac:(lia) ltac:(cbn; lia)) as S2.
          replace (estart E (SA b2 k2) + (bv_unsigned x - estart E (SA b2 k2))) with (bv_unsigned x) in S2 by lia.
          rewrite Z_to_bv_bv_unsigned in S2.
          apply (store_ok_all SEGS M 1 x ltac:(pose proof (u64_range x); cbn; lia) S2 x). cbn. lia.
  Qed.

  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable ISP : Z.
  Variable FS0 : Fs.Fs.

  Theorem zj_xn_sound : ext_stmt SEGS A nx0 LIMIT zj_xn SINV argH ISP FS0.
  Proof.
    intros id args cs cs' E R FULL model T HC _ Hn Hk. unfold zj_xn in Hn.
    destruct (Nat.eqb id 60); [|discriminate]. unfold node_zjoin in Hn.
    destruct (zj_target cs args) as [[te tn]|]; [|discriminate].
    destruct (split_lit te) as [tb tk] eqn:Es.
    destruct (expr_vars_lt (nxt cs) te && expr_vars_lt (nxt cs) tn && zj_first (kn cs) (kn cs) false tb tk tn && zj_first (kn cs) (kn cs) true tb tk tn)%bool eqn:Eb; [|discriminate].
    injection Hn as <-.
    apply andb_prop in Eb as [Eb Hw]. apply andb_prop in Eb as [_ Hz].
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    assert (HK' : know_ok SEGS E (Mr A argH E cs model FULL) (KWr (SA tb tk) tn :: KZero (SA tb tk) tn :: kn cs)).
    { unfold know_ok. constructor; [|constructor; [|exact HK]].
      - exact (zjoin_wr_ok E _ (kn cs) tb tk tn HK Hw).
      - exact (zjoin_zero_ok E _ (kn cs) tb tk tn HK Hz). }
    pose proof (cs_ok_set_kn SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model _ HC HK') as HC'.
    apply (Hk E R FULL model); [split; (split; [intros; reflexivity | reflexivity]) | exact HC' | reflexivity].
  Qed.
End Sound.
