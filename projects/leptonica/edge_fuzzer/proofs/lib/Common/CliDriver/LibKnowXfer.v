(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec CatExec StoreOk.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver Require Import SymExec2 SymExec2Sound SymRun SymDrive SymDriveX.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint emap (rv : nat -> expr) (rb : nat -> nat) (e : expr) : expr :=
  match e with
  | ELit z => ELit z
  | EVar n => rv n
  | EAlu op a b => EAlu op (emap rv rb a) (emap rv rb b)
  | EAluw op a b => EAluw op (emap rv rb a) (emap rv rb b)
  | EMd op a b => EMd op (emap rv rb a) (emap rv rb b)
  | EMdw op a b => EMdw op (emap rv rb a) (emap rv rb b)
  | EExt sx lo n a => EExt sx lo n (emap rv rb a)
  | EBlob sx k i n => EBlob sx (rb k) i n
  end.

Section XFER.
Context {fx : FPState}.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (E : env) (rvl : list expr) (rb : nat -> nat) (ebf : nat -> list byte).
  Hypothesis Hb : forall k, ebf k = eb E (rb k).

  Definition rv (i : nat) : expr := nth i rvl (ELit 0).
  (* [comment removed for export] *)
  Definition xenv : env := Env (vals_ev (map (edenot E) rvl)) ebf.

  Lemma xenv_ev : forall i, ev xenv i = edenot E (rv i).
  Proof.
    intros i. cbn [xenv ev]. unfold vals_ev, rv.
    change (Z_to_bv 64 0) with (edenot E (ELit 0)). apply map_nth.
  Qed.

  Lemma emap_sound : forall e, edenot xenv e = edenot E (emap rv rb e).
  Proof.
    induction e; cbn [edenot emap]; try reflexivity;
      try (rewrite IHe1, IHe2; reflexivity); try (rewrite IHe; reflexivity).
    - apply xenv_ev.
    - cbn [xenv eb]. rewrite Hb. reflexivity.
  Qed.

  Definition amap (a : saddr) : saddr := SA (emap rv rb (a_base a)) (a_off a).

  Lemma amap_adenot : forall a, adenot xenv a = adenot E (amap a).
  Proof. intros [b k]. unfold adenot, amap. cbn [a_base a_off]. rewrite emap_sound. reflexivity. Qed.

  Lemma amap_estart : forall a, estart xenv a = estart E (amap a).
  Proof. intros [b k]. unfold estart, amap. cbn [a_base a_off]. rewrite emap_sound. reflexivity. Qed.

  Lemma amap_flat : forall a n, flat xenv a n <-> flat E (amap a) n.
  Proof. intros. unfold flat. rewrite amap_estart. tauto. Qed.

  Definition kmap (K : kentry) : kentry :=
    match K with
    | KWord a w v => KWord (amap a) w (emap rv rb v)
    | KZero a n => KZero (amap a) (emap rv rb n)
    | KBlob a n bk => KBlob (amap a) (emap rv rb n) (rb bk)
    | KImg lo hi => K
    | KAlign e m => KAlign (emap rv rb e) m
    | KRange e lo hi => KRange (emap rv rb e) lo hi
    | KWr a n => KWr (amap a) n
    | KDisj a1 n1 a2 n2 => KDisj (amap a1) n1 (amap a2) n2
    end.

  Lemma kmap_sound : forall segs M K,
    kentry_ok segs E M (kmap K) -> kentry_ok segs xenv M K.
  Proof.
    intros segs M K HK. destruct K; cbn [kmap kentry_ok] in *.
    - rewrite amap_adenot, emap_sound, amap_flat. exact HK.
    - unfold elenZ in *. rewrite emap_sound, amap_estart, amap_flat. exact HK.
    - unfold elenZ in *. rewrite emap_sound, amap_estart, amap_flat. cbn [xenv eb]. rewrite Hb. exact HK.
    - exact HK.
    - rewrite emap_sound. exact HK.
    - rewrite emap_sound. exact HK.
    - rewrite amap_estart, amap_flat. exact HK.
    - rewrite !amap_estart. exact HK.
  Qed.

  Lemma know_ok_xfer : forall segs M kn',
    know_ok segs E M (map kmap kn') -> know_ok segs xenv M kn'.
  Proof.
    intros segs M kn' H. unfold know_ok in *. apply Forall_forall. intros K HK.
    apply kmap_sound. apply (proj1 (Forall_forall _ _) H). apply in_map. exact HK.
  Qed.

  (* [comment removed for export] *)
  Fixpoint sr_mismatch (sr sr' : list expr) (i : nat) : list nat :=
    match sr, sr' with
    | e :: r, e' :: r' => (if expr_eqb (emap rv rb e') e then [] else [i]) ++ sr_mismatch r r' (S i)
    | [], [] => []
    | _, _ => [i]   (* [comment removed for export] *)
    end.

  Lemma sr_mismatch_sound : forall sr sr' i0,
    length sr = length sr' ->
    (forall i, In (i0 + i)%nat (sr_mismatch sr sr' i0) ->
       edenot E (emap rv rb (nth i sr' (ELit 0))) = edenot E (nth i sr (ELit 0))) ->
    forall i, (i < length sr)%nat -> edenot E (emap rv rb (nth i sr' (ELit 0))) = edenot E (nth i sr (ELit 0)).
  Proof.
    induction sr as [|e r IH]; intros sr' i0 Hlen Hman i Hi.
    - cbn in Hi. lia.
    - destruct sr' as [|e' r']; [cbn in Hlen; lia|]. cbn [length] in Hlen.
      destruct i as [|i].
      + cbn [nth]. cbn [sr_mismatch] in Hman.
        destruct (expr_eqb (emap rv rb e') e) eqn:Heq.
        * apply expr_eqb_eq in Heq. rewrite Heq. reflexivity.
        * apply (Hman 0%nat). rewrite Nat.add_0_r. cbn. left. reflexivity.
      + cbn [nth]. apply (IH r' (S i0)); [lia | | cbn in Hi; lia].
        intros j Hj. apply (Hman (S j)). cbn [sr_mismatch].
        apply in_or_app. right. replace (i0 + S j)%nat with (S i0 + j)%nat by lia. exact Hj.
  Qed.

  Lemma regs_ok_xfer : forall sr sr' R,
    regs_ok E sr R -> length sr = 32%nat -> length sr' = 32%nat ->
    (forall i, In i (sr_mismatch sr sr' 0) -> i <> 0%nat ->
       edenot E (emap rv rb (nth i sr' (ELit 0))) = edenot E (nth i sr (ELit 0))) ->
    regs_ok xenv sr' R.
  Proof.
    intros sr sr' R HR Hl Hl' Hman r. rewrite (HR r). unfold sr_get.
    destruct (bv_eqb r 0) eqn:Hr0; [reflexivity|].
    assert (Hnz : ridx r <> 0%nat).
    { intros H0. assert (r = 0%bv) by (apply bv_eq; change (bv_unsigned (0%bv : reg)) with 0%Z; pose proof (bv_unsigned_in_range _ r); unfold ridx in H0; lia).
      subst r. rewrite bv_eqb_refl in Hr0. discriminate. }
    rewrite emap_sound. symmetry.
    destruct sr as [|e0 sr0]; [cbn in Hl; lia|]. destruct sr' as [|e0' sr0']; [cbn in Hl'; lia|].
    destruct (ridx r) as [|i] eqn:Hri; [lia|]. cbn [nth].
    apply (sr_mismatch_sound sr0 sr0' 1%nat); [cbn in Hl, Hl'; lia | | pose proof (ridx_range r); cbn in Hl; lia].
    intros j Hj. change (nth j sr0' (ELit 0)) with (nth (S j) (e0' :: sr0') (ELit 0)).
    change (nth j sr0 (ELit 0)) with (nth (S j) (e0 :: sr0) (ELit 0)).
    apply Hman; [|lia]. cbn [sr_mismatch]. apply in_or_app. right. exact Hj.
  Qed.
End XFER.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lit_of (e : expr) : option Z := match e with ELit z => Some z | _ => None end.

(* [comment removed for export] *)
Definition kimpl (K K' : kentry) : bool :=
  match K, K' with
  | KWord a w v, KWord a' w' v' => saddr_eqb a a' && Nat.eqb w w' && expr_eqb v v'
  | KZero (SA b k) n, KZero (SA b' k') n' =>
      expr_eqb b b' &&
      match lit_of n, lit_of n' with
      | Some l, Some l' => Z.leb 0 l && Z.ltb l (2 ^ 64) && Z.ltb 0 l' && Z.leb k k' && Z.leb (k' + l') (k + l)
      | _, _ => Z.eqb k k' && expr_eqb n n'
      end
  | KBlob a n bk, KBlob a' n' bk' => saddr_eqb a a' && expr_eqb n n' && Nat.eqb bk bk'
  | KImg lo hi, KImg lo' hi' => Z.leb lo lo' && Z.leb hi' hi && Z.leb lo' hi'
  | KAlign e m, KAlign e' m' => expr_eqb e e' && Z.eqb m m'
  | KRange e lo hi, KRange e' lo' hi' => expr_eqb e e' && Z.leb lo' lo && Z.leb hi hi'
  | KWr (SA b k) n, KWr (SA b' k') n' => expr_eqb b b' && Z.leb k k' && Z.leb (k' + n') (k + n) && Z.ltb 0 n'
  | KDisj (SA b1 k1) n1 (SA b2 k2) n2, KDisj (SA c1 j1) m1 (SA c2 j2) m2 =>
      (Z.leb 0 m1 && Z.leb 0 m2) &&
      ((expr_eqb b1 c1 && expr_eqb b2 c2 && Z.leb k1 j1 && Z.leb (j1 + m1) (k1 + n1) && Z.leb k2 j2 && Z.leb (j2 + m2) (k2 + n2))
       || (expr_eqb b1 c2 && expr_eqb b2 c1 && Z.leb k1 j2 && Z.leb (j2 + m2) (k1 + n1) && Z.leb k2 j1 && Z.leb (j1 + m1) (k2 + n2)))
  | _, _ => false
  end.

Section VP1. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma saddr_eqb_eq : forall a b, saddr_eqb a b = true -> a = b.
Proof.
  intros [b k] [b' k'] H. unfold saddr_eqb in H. cbn [a_base a_off] in H.
  apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.
End VP1.

Ltac bprops :=
  repeat match goal with
  | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
  | H : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in H
  | H : saddr_eqb _ _ = true |- _ => apply saddr_eqb_eq in H
  | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
  | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
  | H : Z.leb _ _ = true |- _ => apply Z.leb_le in H
  | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
  end.

Section VP2. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma kimpl_sound : forall segs E M K K',
  kimpl K K' = true -> kentry_ok segs E M K -> kentry_ok segs E M K'.
Proof.
  intros segs E M K K' Hb HK.
  destruct K as [a w v|[b k] n|a n bk|lo hi|e m|e lo hi|[b k] n|[b1 k1] n1 [b2 k2] n2];
  destruct K' as [a' w' v'|[b' k'] n'|a' n' bk'|lo' hi'|e' m'|e' lo' hi'|[b' k'] n'|[c1 j1] m1 [c2 j2] m2];
  cbn [kimpl] in Hb; try discriminate; cbn [kentry_ok] in HK |- *.
  - bprops. subst. exact HK.
  - destruct (lit_of n) as [l|] eqn:Hn; destruct (lit_of n') as [l'|] eqn:Hn'.
    + destruct n as [l0| | | | | | |]; try discriminate. destruct n' as [l0'| | | | | | |]; try discriminate.
      cbn [lit_of] in Hn, Hn'. injection Hn as ->. injection Hn' as ->.
      bprops. subst b'.
      destruct HK as (Hf & Hz).
      assert (El : elenZ E (ELit l) = l) by (unfold elenZ; cbn [edenot]; apply u_small; lia).
      assert (El' : elenZ E (ELit l') = l') by (unfold elenZ; cbn [edenot]; apply u_small; lia).
      rewrite El in *. rewrite El' in *.
      destruct Hf as (G1 & G2 & G3 & G4). unfold estart in *. cbn [a_base a_off] in *.
      split; [unfold flat, estart; cbn [a_base a_off]; repeat split; lia|].
      intros i Hi. replace (bv_unsigned (edenot E b) + k' + i)%Z with (bv_unsigned (edenot E b) + k + (k' - k + i))%Z by lia.
      apply Hz. lia.
    + destruct n as [l0| | | | | | |]; try discriminate; bprops; subst; exact HK.
    + bprops; subst; exact HK.
    + bprops; subst; exact HK.
  - bprops. subst. exact HK.
  - bprops. destruct HK as (Hlo0 & Hhi0 & Hn). split; [lia|]. split; [lia|]. intros i Hi. apply Hn. lia.
  - bprops. subst. exact HK.
  - bprops. subst. lia.
  - bprops. subst b'. destruct HK as (Hf & Hst).
    destruct Hf as (G1 & G2 & G3 & G4). unfold estart in *. cbn [a_base a_off] in *.
    split; [unfold flat, estart; cbn [a_base a_off]; repeat split; lia|].
    intros d m0 Hd Hm. replace (bv_unsigned (edenot E b) + k' + d)%Z with (bv_unsigned (edenot E b) + k + (k' - k + d))%Z by lia.
    apply Hst; lia.
  - apply andb_prop in Hb as [Hm Hb]. apply andb_prop in Hm as [Hm1 Hm2]. apply Z.leb_le in Hm1. apply Z.leb_le in Hm2.
    unfold estart in *. cbn [a_base a_off] in *.
    apply orb_prop in Hb. destruct Hb as [Hb|Hb]; bprops; subst; lia.
Qed.
End VP2.

Definition kentry_implied (kn : list kentry) (K' : kentry) : bool := existsb (fun K => kimpl K K') kn.

Fixpoint kn_missing (kn : list kentry) (goals : list kentry) : list kentry :=
  match goals with
  | [] => []
  | K' :: rest => (if kentry_implied kn K' then [] else [K']) ++ kn_missing kn rest
  end.

(* [comment removed for export] *)
Section VP3. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma know_ok_entails : forall segs E M kn goals,
  know_ok segs E M kn ->
  Forall (kentry_ok segs E M) (kn_missing kn goals) ->
  know_ok segs E M goals.
Proof.
  intros segs E M kn goals HK Hman. unfold know_ok. induction goals as [|K' rest IH]; [constructor|].
  cbn [kn_missing] in Hman. apply Forall_app in Hman as [H1 H2].
  constructor; [|apply IH; exact H2].
  destruct (kentry_implied kn K') eqn:Hi.
  - unfold kentry_implied in Hi. apply existsb_exists in Hi as (K & HinK & Hb).
    eapply kimpl_sound; [exact Hb|]. exact (proj1 (Forall_forall _ _) HK K HinK).
  - inversion H1. assumption.
Qed.
End VP3.

(* [comment removed for export] *)
Section VP4. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma know_ok_xfer_entails : forall segs E rvl rb ebf M kn kn',
  (forall k, ebf k = eb E (rb k)) ->
  know_ok segs E M kn ->
  Forall (kentry_ok segs E M) (kn_missing kn (map (kmap rvl rb) kn')) ->
  know_ok segs (xenv E rvl ebf) M kn'.
Proof.
  intros segs E rvl rb ebf M kn kn' Hb HK Hm. apply (know_ok_xfer E rvl rb ebf Hb). eapply know_ok_entails; [exact HK | exact Hm].
Qed.
End VP4.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint expr_noblob (e : expr) : bool :=
  match e with
  | ELit _ | EVar _ => true
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => expr_noblob a && expr_noblob b
  | EExt _ _ _ a => expr_noblob a
  | EBlob _ _ _ _ => false
  end.

Definition kentry_noblob (K : kentry) : bool :=
  match K with
  | KWord a _ v => expr_noblob (a_base a) && expr_noblob v
  | KZero a n => expr_noblob (a_base a) && expr_noblob n
  | KBlob _ _ _ => false
  | KImg _ _ => true
  | KAlign e _ => expr_noblob e
  | KRange e _ _ => expr_noblob e
  | KWr a _ => expr_noblob (a_base a)
  | KDisj a1 _ a2 _ => expr_noblob (a_base a1) && expr_noblob (a_base a2)
  end.

Section VP5. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma edenot_noblob : forall v eb1 eb2 e,
  expr_noblob e = true -> edenot (Env v eb1) e = edenot (Env v eb2) e.
Proof.
  intros v eb1 eb2 e. induction e; cbn [expr_noblob edenot ev eb]; intros H; try reflexivity; try discriminate;
    try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1), (IHe2 H2); reflexivity);
    try (rewrite (IHe H); reflexivity).
Qed.
End VP5.

Section VP6. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma kentry_noblob_irrel : forall segs v eb1 eb2 M K,
  kentry_noblob K = true -> kentry_ok segs (Env v eb1) M K -> kentry_ok segs (Env v eb2) M K.
Proof.
  intros segs v eb1 eb2 M K Hb HK.
  destruct K as [[b k] w val|[b k] n|a n bk|lo hi|e m|e lo hi|[b k] n|[b1 k1] n1 [b2 k2] n2];
    cbn [kentry_noblob a_base] in Hb; try discriminate; cbn [kentry_ok] in HK |- *;
    unfold flat, estart, adenot, elenZ in *; cbn [a_base a_off] in *.
  - apply andb_prop in Hb as [H1 H2]. rewrite <- !(edenot_noblob v eb1 eb2 b H1), <- !(edenot_noblob v eb1 eb2 val H2). exact HK.
  - apply andb_prop in Hb as [H1 H2]. rewrite <- !(edenot_noblob v eb1 eb2 b H1), <- !(edenot_noblob v eb1 eb2 n H2). exact HK.
  - exact HK.
  - rewrite <- !(edenot_noblob v eb1 eb2 e Hb). exact HK.
  - rewrite <- !(edenot_noblob v eb1 eb2 e Hb). exact HK.
  - rewrite <- !(edenot_noblob v eb1 eb2 b Hb). exact HK.
  - apply andb_prop in Hb as [H1 H2]. rewrite <- !(edenot_noblob v eb1 eb2 b1 H1), <- !(edenot_noblob v eb1 eb2 b2 H2). exact HK.
Qed.
End VP6.

Section VP7. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma know_ok_noblob_irrel : forall segs v eb1 eb2 M kn,
  forallb kentry_noblob kn = true -> know_ok segs (Env v eb1) M kn -> know_ok segs (Env v eb2) M kn.
Proof.
  intros segs v eb1 eb2 M kn Hb HK. unfold know_ok in *. apply Forall_forall. intros K HinK.
  apply (kentry_noblob_irrel segs v eb1 eb2 M K).
  - apply forallb_forall with (x := K) in Hb; assumption.
  - exact (proj1 (Forall_forall _ _) HK K HinK).
Qed.
End VP7.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
