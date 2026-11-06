(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCStream.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rcode (c L : Z) : list Z := if L <? 4 then repeat c (Z.to_nat L) else repeat c 4 ++ [L - 4].

Fixpoint rl_enc (runs : list (Z * Z)) : list Z :=
  match runs with [] => [] | (c, L) :: rs => rcode c L ++ rl_enc rs end.
Fixpoint rl_dec (runs : list (Z * Z)) : list Z :=
  match runs with [] => [] | (c, L) :: rs => repeat c (Z.to_nat L) ++ rl_dec rs end.

(* [comment removed for export] *)
Definition hd_char (runs : list (Z * Z)) : Z := match runs with [] => 256 | (c, _) :: _ => c end.

(* [comment removed for export] *)
Definition ADJ (c L : Z) (next : Z) : Prop := L < 4 -> next <> c.

Fixpoint RWF (runs : list (Z * Z)) : Prop :=
  match runs with
  | [] => True
  | (c, L) :: rs => 0 <= c < 256 /\ 1 <= L <= 255 /\ ADJ c L (hd_char rs) /\ RWF rs
  end.

Lemma rl_enc_app : forall r1 r2, rl_enc (r1 ++ r2) = rl_enc r1 ++ rl_enc r2.
Proof. induction r1 as [|[c L] r1 IH]; intros r2; cbn [rl_enc app]; [reflexivity|]. rewrite IH, app_assoc. reflexivity. Qed.
Lemma rl_dec_app : forall r1 r2, rl_dec (r1 ++ r2) = rl_dec r1 ++ rl_dec r2.
Proof. induction r1 as [|[c L] r1 IH]; intros r2; cbn [rl_dec app]; [reflexivity|]. rewrite IH, app_assoc. reflexivity. Qed.

Lemma rcode_length : forall c L, 1 <= L <= 255 -> Z.of_nat (length (rcode c L)) = (if L <? 4 then L else 5).
Proof.
  intros c L HL. unfold rcode. destruct (Z.ltb_spec L 4).
  - rewrite repeat_length. lia.
  - rewrite length_app, repeat_length. cbn [length]. lia.
Qed.
Lemma rcode_length_ge1 : forall c L, 1 <= L <= 255 -> (1 <= length (rcode c L))%nat.
Proof. intros c L HL. pose proof (rcode_length c L HL) as E. destruct (Z.ltb_spec L 4); lia. Qed.
Lemma rcode_hd : forall c L, 1 <= L -> exists tl, rcode c L = c :: tl.
Proof.
  intros c L HL. unfold rcode. destruct (Z.ltb_spec L 4).
  - replace (Z.to_nat L) with (S (Z.to_nat (L - 1))) by lia. cbn [repeat]. eauto.
  - cbn [repeat app]. eauto.
Qed.
Lemma rcode_bytes : forall c L, 0 <= c < 256 -> 1 <= L <= 255 -> Forall (fun b => 0 <= b < 256) (rcode c L).
Proof.
  intros c L Hc HL. unfold rcode. destruct (Z.ltb_spec L 4).
  - apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia.
  - apply Forall_app. split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia|]. constructor; [lia| constructor].
Qed.

Lemma rl_enc_hd : forall runs, RWF runs -> runs <> [] -> exists tl, rl_enc runs = hd_char runs :: tl.
Proof.
  intros [|[c L] rs] W NE; [congruence|]. cbn [rl_enc hd_char]. cps_destruct W as (Hc & HL & _ & _).
  destruct (rcode_hd c L ltac:(lia)) as [tl ->]. cbn [app]. eauto.
Qed.
Lemma rl_enc_bytes : forall runs, RWF runs -> Forall (fun b => 0 <= b < 256) (rl_enc runs).
Proof.
  induction runs as [|[c L] rs IH]; intros W; cbn [rl_enc]; [constructor|]. cps_destruct W as (Hc & HL & _ & W).
  apply Forall_app. split; [apply rcode_bytes; lia| apply IH; exact W].
Qed.
Lemma rl_dec_bytes : forall runs, RWF runs -> Forall (fun b => 0 <= b < 256) (rl_dec runs).
Proof.
  induction runs as [|[c L] rs IH]; intros W; cbn [rl_dec]; [constructor|]. cps_destruct W as (Hc & HL & _ & W).
  apply Forall_app. split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia| apply IH; exact W].
Qed.
Lemma rl_enc_length_ge : forall runs, RWF runs -> (length runs <= length (rl_enc runs))%nat.
Proof.
  induction runs as [|[c L] rs IH]; intros W; cbn [rl_enc length]; [lia|]. cps_destruct W as (Hc & HL & _ & W).
  pose proof (IH W). rewrite length_app. pose proof (rcode_length_ge1 c L HL). lia.
Qed.
Lemma RWF_app : forall r1 r2, RWF (r1 ++ r2) <-> RWF r1 /\ RWF r2 /\ (match last r1 (256, 255) with (c, L) => ADJ c L (hd_char r2) end).
Proof.
  induction r1 as [|[c L] r1 IH]; intros r2.
  - cbn [app RWF last]. unfold ADJ. intuition lia.
  - cbn [app RWF]. rewrite IH.
    destruct r1 as [|[c' L'] r1']; cbn [last hd_char app].
    + destruct r2 as [|[c2 L2] r2']; cbn [hd_char]; unfold ADJ; intuition lia.
    + tauto.
Qed.
Lemma RWF_snoc : forall runs c L, RWF (runs ++ [(c, L)]) <-> RWF runs /\ 0 <= c < 256 /\ 1 <= L <= 255 /\ (match last runs (256, 255) with (c', L') => ADJ c' L' c end).
Proof.
  intros runs c L. rewrite RWF_app. cbn [RWF hd_char]. destruct (last runs (256, 255)) as [c' L']. unfold ADJ. intuition lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint unrle1 (t : list Z) : list Z :=
  match t with
  | [] => []
  | c :: t1 =>
    match t1 with
    | [] => [c]
    | c2 :: t2 =>
      if negb (c2 =? c) then c :: unrle1 t1 else
      match t2 with
      | [] => [c; c]
      | c3 :: t3 =>
        if negb (c3 =? c) then c :: c :: unrle1 t2 else
        match t3 with
        | [] => [c; c; c]
        | c4 :: t4 =>
          if negb (c4 =? c) then c :: c :: c :: unrle1 t3 else
          match t4 with
          | [] => [c; c; c; c]
          | m :: t5 => repeat c (Z.to_nat (m + 4)) ++ unrle1 t5
          end
        end
      end
    end
  end.

Lemma unrle1_eq : forall c t1, unrle1 (c :: t1) =
    match t1 with
    | [] => [c]
    | c2 :: t2 =>
      if negb (c2 =? c) then c :: unrle1 t1 else
      match t2 with
      | [] => [c; c]
      | c3 :: t3 =>
        if negb (c3 =? c) then c :: c :: unrle1 t2 else
        match t3 with
        | [] => [c; c; c]
        | c4 :: t4 =>
          if negb (c4 =? c) then c :: c :: c :: unrle1 t3 else
          match t4 with
          | [] => [c; c; c; c]
          | m :: t5 => repeat c (Z.to_nat (m + 4)) ++ unrle1 t5
          end
        end
      end
    end.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma unrle1_code : forall c L rest, 1 <= L <= 255 -> ADJ c L (hd 256 rest) ->
  unrle1 (rcode c L ++ rest) = repeat c (Z.to_nat L) ++ unrle1 rest.
Proof.
  intros c L rest HL AD. unfold rcode, ADJ in *.
  destruct (Z.ltb_spec L 4) as [LT|GE].
  - assert (NX : forall x tl, rest = x :: tl -> negb (x =? c) = true).
    { intros x tl ->. cbn [hd] in AD. apply Bool.negb_true_iff. apply Z.eqb_neq. apply AD. exact LT. }
    assert (L = 1 \/ L = 2 \/ L = 3) as [-> |[-> | ->]] by lia;
      [change (Z.to_nat 1) with 1%nat| change (Z.to_nat 2) with 2%nat| change (Z.to_nat 3) with 3%nat]; cbn [repeat app];
      rewrite unrle1_eq, ?Z.eqb_refl; cbn [negb]; destruct rest as [|x tl]; try reflexivity; rewrite (NX x tl eq_refl); reflexivity.
  - change (repeat c 4 ++ [L - 4]) with (c :: c :: c :: c :: [L - 4]). cbn [app]. rewrite unrle1_eq, !Z.eqb_refl. cbn [negb]. f_equal. f_equal. lia.
Qed.

Theorem unrle1_enc : forall runs, RWF runs -> unrle1 (rl_enc runs) = rl_dec runs.
Proof.
  induction runs as [|[c L] rs IH]; intros W; [reflexivity|]. cbn [rl_enc rl_dec]. cps_destruct W as (Hc & HL & AD & W).
  rewrite unrle1_code; [| exact HL|].
  - rewrite IH by exact W. reflexivity.
  - destruct rs as [|[c' L'] rs']; [unfold ADJ; cbn; intros; lia|].
    destruct (rl_enc_hd ((c', L') :: rs') W ltac:(discriminate)) as [tl E]. rewrite E. cbn [hd]. exact AD.
Qed.

Definition rlcodes (t data : list Z) : Prop := exists runs, RWF runs /\ t = rl_enc runs /\ data = rl_dec runs.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition crc_list (crc : Z) (l : list Z) : Z := fold_left crc_update l crc.
Lemma crc_list_app : forall crc l1 l2, crc_list crc (l1 ++ l2) = crc_list (crc_list crc l1) l2.
Proof. intros. unfold crc_list. apply fold_left_app. Qed.
Lemma crc_list_cons : forall crc x l, crc_list crc (x :: l) = crc_list (crc_update crc x) l.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma crc_list_repeat : forall k crc c, crc_list crc (repeat c k) = crc_update_n crc c k.
Proof. induction k as [|k IH]; intros; cbn [repeat crc_update_n]; [reflexivity|]. rewrite crc_list_cons. apply IH. Qed.
