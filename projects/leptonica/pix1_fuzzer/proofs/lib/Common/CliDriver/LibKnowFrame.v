(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import PropExec CatExec StoreOk AllocSim MmapSim MemSplit.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CliDriver Require Import SymExec2 SymExec2Sound SymRun SymDrive SymDriveX.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition apart_b (allkn : list kentry) (ub : expr) (uk un : Z) (b : expr) (k n : Z) : bool :=
  if expr_eqb b ub then (Z.leb (k + n) uk || Z.leb (uk + un) k)%bool
  else ranges_apart allkn ub uk un b k n.

Section VP1. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma apart_b_sound : forall segs E M allkn ub uk un b k n,
  know_ok segs E M allkn -> apart_b allkn ub uk un b k n = true ->
  ((estart E (SA ub uk) + un <= estart E (SA b k))%Z \/ (estart E (SA b k) + n <= estart E (SA ub uk))%Z).
Proof.
  intros segs E M allkn ub uk un b k n HK H. unfold apart_b in H.
  destruct (expr_eqb b ub) eqn:Heq.
  - apply expr_eqb_eq in Heq. subst b. unfold estart. cbn [a_base a_off].
    apply orb_prop in H. destruct H as [H|H]; apply Z.leb_le in H; lia.
  - eapply ranges_apart_sound; [exact HK | exact H].
Qed.
End VP1.

(* [comment removed for export] *)
Definition kn_frame1 (allkn : list kentry) (ub : expr) (uk un : Z) (K : kentry) : list kentry :=
  match K with
  | KWord (SA b k) w _ => if apart_b allkn ub uk un b k (Z.of_nat w) then [K] else []
  | KZero (SA b k) (ELit l) =>
      if (Z.leb 0 l && Z.ltb l (2 ^ 64))%bool then
        if apart_b allkn ub uk un b k l then [K]
        else if expr_eqb b ub then
          (if Z.ltb k uk then [KZero (SA b k) (ELit (Z.min l (uk - k)))] else [])
          ++ (if Z.ltb (uk + un) (k + l) then [KZero (SA b (Z.max k (uk + un))) (ELit (k + l - Z.max k (uk + un)))] else [])
        else []
      else []
  | KZero _ _ => []
  | KBlob (SA b k) (ELit l) _ => if (Z.leb 0 l && Z.ltb l (2 ^ 64) && apart_b allkn ub uk un b k l)%bool then [K] else []
  | KBlob _ _ _ => []
  | KImg lo hi => if (Z.leb 0 lo && Z.ltb lo hi && Z.leb hi (2 ^ 64) && apart_b allkn ub uk un (ELit 0) lo (hi - lo))%bool then [K] else []
  | KAlign _ _ => [K]
  | KRange _ _ _ => [K]
  | KDisj _ _ _ _ => [K]
  | KWr _ _ => [K]
  end.

Definition kn_frame (kn : list kentry) (ub : expr) (uk un : Z) : list kentry :=
  flat_map (kn_frame1 kn ub uk un) kn.

Section VP2. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma edenot_lit0 : forall E, bv_unsigned (edenot E (ELit 0)) = 0%Z.
Proof. intros. reflexivity. Qed.
End VP2.

(* [comment removed for export] *)
Section VP3. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma know_ok_frame : forall segs E M M' kn ub uk un,
  know_ok segs E M kn -> flat E (SA ub uk) un ->
  (forall x : word,
     (bv_unsigned x < estart E (SA ub uk) \/ estart E (SA ub uk) + un <= bv_unsigned x)%Z -> M' x = M x) ->
  mem_grows M M' ->
  know_ok segs E M' (kn_frame kn ub uk un).
Proof.
  intros segs E M M' kn ub uk un HK Hfl OUT GR.
  pose proof (flat_u E _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
  unfold know_ok, kn_frame. apply Forall_forall. intros K' HinF.
  apply in_flat_map in HinF as (K & Hin & Hb).
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  assert (APART : forall b k n, apart_b kn ub uk un b k n = true ->
            ((estart E (SA ub uk) + un <= estart E (SA b k))%Z \/ (estart E (SA b k) + n <= estart E (SA ub uk))%Z)).
  { intros b k n H. eapply apart_b_sound; [exact HK | exact H]. }
  destruct K as [[b k] w v|[b k] len|[b k] len bk|lo hi|e m|e lo hi|[b k] n|a1 n1 a2 n2];
    cbn [kn_frame1] in Hb.
  - (* [comment removed for export] *)
    destruct (apart_b kn ub uk un b k (Z.of_nat w)) eqn:Hap; [|destruct Hb].
    destruct Hb as [<-|[]]. cbn [kentry_ok] in HKK |- *.
    destruct HKK as (Hw & Hf & Hr). split; [exact Hw|]. split; [exact Hf|].
    rewrite <- Hr. apply rdn_agree. intros j Hj.
    pose proof (flat_u E _ _ Hf) as Hub. destruct Hf as (G1 & G2 & G3 & G4).
    apply OUT. rewrite u_small by lia. destruct (APART b k (Z.of_nat w) Hap); lia.
  - (* [comment removed for export] *)
    destruct len as [l| | | | | | |]; try (destruct Hb; fail); [|destruct Hb..].
    destruct (Z.leb 0 l && Z.ltb l (2 ^ 64))%bool eqn:Hl; [|destruct Hb].
    apply andb_prop in Hl as [Hl0 Hl1]. apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
    cbn [kentry_ok] in HKK. destruct HKK as (Hf & Hz).
    assert (El : elenZ E (ELit l) = l) by (unfold elenZ; cbn [edenot]; apply u_small; lia).
    rewrite El in *. pose proof Hf as Hf0. destruct Hf as (G1 & G2 & G3 & G4).
    destruct (apart_b kn ub uk un b k l) eqn:Hap.
    + destruct Hb as [<-|[]]. cbn [kentry_ok]. rewrite El. split; [exact Hf0|].
      intros i Hi. rewrite OUT; [apply Hz; exact Hi|].
      rewrite u_small by lia. destruct (APART b k l Hap); lia.
    + destruct (expr_eqb b ub) eqn:Heq; [|destruct Hb].
      apply expr_eqb_eq in Heq. subst b.
      unfold estart in G1, G2, G4, OUT, Hz |- *. cbn [a_base a_off] in G1, G2, G4, OUT, Hz |- *.
      apply in_app_or in Hb. destruct Hb as [Hb|Hb].
      * destruct (Z.ltb k uk) eqn:Hlt; [|destruct Hb]. apply Z.ltb_lt in Hlt.
        destruct Hb as [<-|[]]. cbn [kentry_ok]. unfold flat, elenZ, estart. cbn [a_base a_off edenot].
        rewrite u_small by lia. split; [split; [exact G1 | split; [exact G2 | split; lia]]|].
        intros i Hi. rewrite OUT; [apply Hz; lia|]. rewrite u_small by lia. lia.
      * destruct (Z.ltb (uk + un) (k + l)) eqn:Hlt; [|destruct Hb]. apply Z.ltb_lt in Hlt.
        destruct Hb as [<-|[]]. cbn [kentry_ok]. unfold flat, elenZ, estart. cbn [a_base a_off edenot].
        rewrite u_small by lia. split; [split; [lia | split; [lia | split; lia]]|].
        intros i Hi. rewrite OUT; [|rewrite u_small by lia; lia].
        replace (bv_unsigned (edenot E ub) + Z.max k (uk + un) + i)%Z
          with (bv_unsigned (edenot E ub) + k + (Z.max k (uk + un) - k + i))%Z by lia.
        apply Hz. lia.
  - (* [comment removed for export] *)
    destruct len as [l| | | | | | |]; try (destruct Hb; fail); [|destruct Hb..].
    destruct (Z.leb 0 l && Z.ltb l (2 ^ 64) && apart_b kn ub uk un b k l)%bool eqn:Hl; [|destruct Hb].
    destruct Hb as [<-|[]].
    apply andb_prop in Hl as [Hl Hap]. apply andb_prop in Hl as [Hl0 Hl1].
    apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
    cbn [kentry_ok] in HKK |- *. destruct HKK as (Hf & Hlen & Hz). split; [exact Hf|]. split; [exact Hlen|].
    assert (El : elenZ E (ELit l) = l) by (unfold elenZ; cbn [edenot]; apply u_small; lia).
    rewrite El in *. destruct Hf as (G1 & G2 & G3 & G4).
    intros i Hi. rewrite OUT; [apply Hz; exact Hi|].
    rewrite u_small by lia. destruct (APART b k l Hap); lia.
  - (* [comment removed for export] *)
    destruct (Z.leb 0 lo && Z.ltb lo hi && Z.leb hi (2 ^ 64) && apart_b kn ub uk un (ELit 0) lo (hi - lo))%bool eqn:Hl; [|destruct Hb].
    destruct Hb as [<-|[]].
    apply andb_prop in Hl as [Hl Hap]. apply andb_prop in Hl as [Hl Hhi]. apply andb_prop in Hl as [Hlo Hlh].
    apply Z.leb_le in Hlo. apply Z.ltb_lt in Hlh. apply Z.leb_le in Hhi.
    cbn [kentry_ok] in HKK |- *. destruct HKK as (H0 & H1 & Hnone). split; [exact H0|]. split; [exact H1|].
    intros i Hi. rewrite OUT; [apply Hnone; exact Hi|].
    pose proof (APART (ELit 0) lo (hi - lo)%Z Hap) as AP. unfold estart in AP |- *. cbn [a_base a_off] in AP |- *.
    rewrite edenot_lit0 in AP. rewrite u_small by lia. lia.
  - (* [comment removed for export] *) destruct Hb as [<-|[]]. exact HKK.
  - (* [comment removed for export] *) destruct Hb as [<-|[]]. exact HKK.
  - (* [comment removed for export] *)
    destruct Hb as [<-|[]]. cbn [kentry_ok] in HKK |- *.
    destruct HKK as (Hf & Hst). split; [exact Hf|].
    intros d m Hd Hm. eapply store_ok_mono; [exact GR | apply Hst; assumption].
  - (* [comment removed for export] *) destruct Hb as [<-|[]]. exact HKK.
Qed.
End VP3.

(* [comment removed for export] *)

Section VP4. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma zfill_inside : forall (a n : word) M (x : word),
  (bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n)%Z ->
  zfill a n M x = Some (Z_to_bv 8 0).
Proof.
  intros a n M x H. unfold zfill, zmem.
  rewrite (proj2 (Z.leb_le _ _) (proj1 H)). rewrite (proj2 (Z.ltb_lt _ _) (proj2 H)). reflexivity.
Qed.
End VP4.

Section VP5. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma zfill_outside : forall (a n : word) M (x : word),
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
  zfill a n M x = M x.
Proof. intros a n M x H. apply zfill_out. exact H. Qed.
End VP5.

(* [comment removed for export] *)
Section VP6. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma know_ok_zfill : forall segs E M kn ub uk un,
  know_ok segs E M kn -> flat E (SA ub uk) un -> (0 < un)%Z -> (un < 2 ^ 64)%Z ->
  know_ok segs E (zfill (adenot E (SA ub uk)) (Z_to_bv 64 un) M)
          (KZero (SA ub uk) (ELit un) :: kn_frame kn ub uk un).
Proof.
  intros segs E M kn ub uk un HK Hfl Hpos Hun.
  pose proof (flat_u E _ _ Hfl) as Hu. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
  unfold estart in F1, F2, F3, F4. cbn [a_base a_off] in F1, F2, F3, F4.
  apply know_ok_cons.
  - eapply (kzero_intro segs E _ ub (edenot E ub) uk (ELit un) un); [reflexivity | | exact F1 | exact Hpos | exact F4 |].
    + cbn [edenot]. apply u_small. clear -Hpos Hun. lia.
    + intros i Hi. apply zfill_inside. rewrite Hu, !u_small by lia. unfold estart. cbn [a_base a_off]. lia.
  - eapply know_ok_frame; [exact HK | exact Hfl | |].
    + intros x Hx. apply zfill_outside. rewrite Hu, u_small by lia. exact Hx.
    + intros x Hx. unfold zfill, zmem. destruct (_ && _)%bool; [discriminate | exact Hx].
Qed.
End VP6.

(* [comment removed for export] *)

Section VP7. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma know_ok_wblob : forall segs E M kn ub uk (k : nat) (bs : list byte),
  know_ok segs E M kn -> flat E (SA ub uk) (Z.of_nat (length bs)) ->
  eb E k = bs -> (0 < length bs)%nat -> (Z.of_nat (length bs) < 2 ^ 64)%Z ->
  know_ok segs E (wbytes M (adenot E (SA ub uk)) bs)
          (KBlob (SA ub uk) (ELit (Z.of_nat (length bs))) k :: kn_frame kn ub uk (Z.of_nat (length bs))).
Proof.
  intros segs E M kn ub uk k bs HK Hfl Hb Hpos Hsmall.
  pose proof (flat_u E _ _ Hfl) as Hu. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
  unfold estart in F1, F2, F3, F4. cbn [a_base a_off] in F1, F2, F3, F4.
  apply know_ok_cons.
  - eapply (kblob_intro segs E _ ub (edenot E ub) uk _ k bs); [reflexivity | exact Hb | | exact F1 | exact F2 | exact F4 |].
    + cbn [edenot]. apply u_small. clear -Hsmall. lia.
    + intros i Hi.
      rewrite MemSplit.wbytes_inside by (rewrite Hu; unfold estart; cbn [a_base a_off]; rewrite ?u_small by lia; lia).
      f_equal. f_equal. rewrite Hu, u_small by lia. unfold estart. cbn [a_base a_off]. lia.
  - eapply know_ok_frame; [exact HK | exact Hfl | |].
    + intros x Hx. apply MemSplit.wbytes_outside; rewrite Hu; [unfold estart; cbn [a_base a_off]; lia | exact Hx].
    + apply wbytes_grows.
Qed.
End VP7.

(* [comment removed for export] *)
Section VP8. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma wbytes_nil_id : forall M (a : word), wbytes M a [] = M.
Proof. intros. reflexivity. Qed.
End VP8.

(* [comment removed for export] *)

Section VP9. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma rdn_1_of_mem : forall segs M (a : word) (b : byte),
  M a = Some b -> rdn segs M a 1 = Some [b].
Proof. intros segs M a b H. cbn [rdn]. rewrite H. reflexivity. Qed.
End VP9.

Section VP10. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma kword1_of_mem : forall segs E M (e : expr) (a : word) off (z : Z),
  edenot E e = a -> (0 <= z < 256)%Z ->
  (0 <= bv_unsigned a + off)%Z -> (bv_unsigned a + off + 1 <= 2 ^ 64)%Z ->
  M (Z_to_bv 64 (bv_unsigned a + off)) = Some (Z_to_bv 8 z) ->
  kentry_ok segs E M (KWord (SA e off) 1 (ELit z)).
Proof.
  intros segs E M e a off z He Hz H1 H2 Hm.
  eapply (kword_intro segs E M e a off 1 (ELit z) (Z_to_bv 64 z)); try assumption; try reflexivity; try lia.
  rewrite (rdn_1_of_mem segs M _ _ Hm). cbn. rewrite u_small by lia. reflexivity.
Qed.
End VP10.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
