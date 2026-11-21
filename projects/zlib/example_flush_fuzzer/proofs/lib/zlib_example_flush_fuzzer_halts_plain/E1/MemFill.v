(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import MemRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.
Definition filled (m : word -> option byte) (lo hi : Z) (bb : byte) : Prop :=
  forall x : word, lo <= bv_unsigned x < hi -> m x = Some bb.

Definition same_outside (mem m : word -> option byte) (lo hi : Z) : Prop :=
  forall x : word, ~ (lo <= bv_unsigned x < hi) -> m x = mem x.

Lemma filled_nil : forall m lo bb, filled m lo lo bb.
Proof. intros m lo bb x Hx. lia. Qed.

Lemma filled_sub : forall m lo hi lo' hi' bb,
  filled m lo hi bb -> lo <= lo' -> hi' <= hi -> filled m lo' hi' bb.
Proof. intros m lo hi lo' hi' bb H H1 H2 x Hx. apply H. lia. Qed.

Lemma filled_join : forall m a b c d bb,
  filled m a b bb -> filled m c d bb -> c <= b -> filled m a d bb.
Proof.
  intros m a b c d bb H1 H2 Hcb x Hx.
  destruct (Z_lt_le_dec (bv_unsigned x) b); [apply H1; lia | apply H2; lia].
Qed.

Lemma zw_succ : forall a, 0 <= a -> a + 1 < 2 ^ 64 -> (zw a + 1)%bv = zw (a + 1).
Proof.
  intros a H0 H1. apply bv_eq. rewrite u_add1 by (rewrite u_zw_small; lia).
  rewrite !u_zw_small by lia. reflexivity.
Qed.

Lemma wbytes_const_lookup : forall k m (a : Z) (bb : byte) (x : word),
  0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  wbytes m (zw a) (repeat bb k) x
  = if (a <=? bv_unsigned x) && (bv_unsigned x <? a + Z.of_nat k) then Some bb else m x.
Proof.
  induction k as [|k IH]; intros m a bb x Ha Hk.
  - cbn [repeat wbytes]. change (Z.of_nat 0) with 0.
    destruct (Z.leb_spec a (bv_unsigned x)), (Z.ltb_spec (bv_unsigned x) (a + 0)); cbn [andb]; try reflexivity; lia.
  - cbn [repeat wbytes].
    destruct (Z.eq_dec (a + 1) (2 ^ 64)) as [E|NE].
    +
      assert (k = 0%nat) by lia. subst k. cbn [repeat wbytes].
      pose proof (u64_range x).
      destruct (bv_eqb x (zw a)) eqn:Hq.
      * assert (x = zw a) by (apply bv_eq; unfold bv_eqb in Hq; lia). subst x. rewrite u_zw_small by lia.
        destruct (Z.leb_spec a a), (Z.ltb_spec a (a + Z.of_nat 1)); cbn [andb]; try reflexivity; lia.
      * assert (bv_unsigned x <> a).
        { intros E2. unfold bv_eqb in Hq. rewrite u_zw_small in Hq by lia. apply Z.eqb_neq in Hq. lia. }
        destruct (Z.leb_spec a (bv_unsigned x)), (Z.ltb_spec (bv_unsigned x) (a + Z.of_nat 1)); cbn [andb]; try reflexivity; lia.
    + rewrite zw_succ by lia. rewrite IH by lia. cbv beta.
      pose proof (u64_range x).
      destruct (bv_eqb x (zw a)) eqn:Hq.
      * assert (x = zw a) by (apply bv_eq; unfold bv_eqb in Hq; lia). subst x. rewrite u_zw_small by lia.
        destruct (Z.leb_spec (a + 1) a); [lia|]. cbn [andb].
        destruct (Z.leb_spec a a), (Z.ltb_spec a (a + Z.of_nat (S k))); cbn [andb]; try reflexivity; lia.
      * assert (bv_unsigned x <> a).
        { intros E2. unfold bv_eqb in Hq. rewrite u_zw_small in Hq by lia. apply Z.eqb_neq in Hq. lia. }
        destruct (Z.leb_spec (a + 1) (bv_unsigned x)), (Z.ltb_spec (bv_unsigned x) (a + 1 + Z.of_nat k)),
                 (Z.leb_spec a (bv_unsigned x)), (Z.ltb_spec (bv_unsigned x) (a + Z.of_nat (S k)));
          cbn [andb]; try reflexivity; lia.
Qed.

Lemma filled_wbytes_new : forall k m a bb,
  0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  filled (wbytes m (zw a) (repeat bb k)) a (a + Z.of_nat k) bb.
Proof.
  intros k m a bb Ha Hk x Hx. rewrite wbytes_const_lookup by lia.
  destruct (Z.leb_spec a (bv_unsigned x)), (Z.ltb_spec (bv_unsigned x) (a + Z.of_nat k)); cbn [andb]; try reflexivity; lia.
Qed.

Lemma filled_wbytes_keep : forall k m a bb lo hi,
  0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  filled m lo hi bb -> filled (wbytes m (zw a) (repeat bb k)) lo hi bb.
Proof.
  intros k m a bb lo hi Ha Hk H x Hx. rewrite wbytes_const_lookup by lia.
  destruct (_ && _); [reflexivity | apply H; exact Hx].
Qed.

Lemma same_outside_refl : forall mem lo hi, same_outside mem mem lo hi.
Proof. intros mem lo hi x _. reflexivity. Qed.

Lemma same_outside_wbytes : forall k mem m a bb lo hi,
  0 <= a -> a + Z.of_nat k <= 2 ^ 64 -> lo <= a -> a + Z.of_nat k <= hi ->
  same_outside mem m lo hi -> same_outside mem (wbytes m (zw a) (repeat bb k)) lo hi.
Proof.
  intros k mem m a bb lo hi Ha Hk H1 H2 H x Hx. rewrite wbytes_const_lookup by lia.
  destruct (Z.leb_spec a (bv_unsigned x)), (Z.ltb_spec (bv_unsigned x) (a + Z.of_nat k)); cbn [andb];
    try (apply H; exact Hx). lia.
Qed.

Lemma grows_wbytes : forall (mem m : word -> option byte) (a : word) bs,
  (forall x, mem x <> None -> m x <> None) -> forall x, mem x <> None -> wbytes m a bs x <> None.
Proof. intros mem m a bs H x Hx. apply wbytes_grows. exact (H x Hx). Qed.


  Definition ms_bb (c : Z) : byte := Z_to_bv 8 (c mod 2 ^ 8).

Lemma Z_to_bv8_mod : forall c, Z_to_bv 8 c = ms_bb c.
Proof.
  intros c. unfold ms_bb. apply bv_eq. rewrite !Z_to_bv_unsigned.
  change (bv_wrap 8 c = bv_wrap 8 (c mod 2 ^ 8)). unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma rep1 : forall c, Z_to_le_bytes 1 c = repeat (ms_bb c) 1.
Proof. intros c. cbn [Z_to_le_bytes repeat]. rewrite Z_to_bv8_mod. reflexivity. Qed.

Fixpoint allb (n : nat) (f : Z -> bool) : bool :=
  match n with O => true | S n' => f (Z.of_nat n') && allb n' f end.

Lemma allb_ok : forall n f, allb n f = true -> forall z, 0 <= z < Z.of_nat n -> f z = true.
Proof.
  induction n as [|n IH]; intros f H z Hz; [lia|].
  cbn [allb] in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec z (Z.of_nat n)) as [->|Hne]; [exact H1|]. apply IH; [exact H2 | lia].
Qed.

Definition bytes_eqb (l1 l2 : list byte) : bool :=
  forallb (fun p => bv_eqb (fst p) (snd p)) (combine l1 l2) && Nat.eqb (length l1) (length l2).

Lemma bytes_eqb_eq : forall l1 l2, bytes_eqb l1 l2 = true -> l1 = l2.
Proof.
  unfold bytes_eqb. induction l1 as [|a l1 IH]; intros [|b l2] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [H0 H1].
  f_equal; [apply bv_eq; unfold bv_eqb in H0; lia | apply IH; rewrite H1, H2; reflexivity].
Qed.







Lemma filled_wbytes_new' : forall k m a bb lo hi,
  0 <= a -> a + Z.of_nat k <= 2 ^ 64 -> lo = a -> hi = a + Z.of_nat k ->
  filled (wbytes m (zw a) (repeat bb k)) lo hi bb.
Proof. intros k m a bb lo hi Ha Hk -> ->. apply filled_wbytes_new; assumption. Qed.

Lemma filled_transport : forall m1 m2 lo hi L R bb,
  filled m1 lo hi bb -> filled m2 L R bb -> (forall x : word, ~ (L <= bv_unsigned x < R) -> m2 x = m1 x) ->
  filled m2 lo hi bb.
Proof.
  intros m1 m2 lo hi L R bb H1 H2 Hs x Hx.
  destruct (Z_le_gt_dec L (bv_unsigned x)); [destruct (Z_lt_le_dec (bv_unsigned x) R)|].
  - apply H2. lia.
  - rewrite Hs by lia. apply H1. exact Hx.
  - rewrite Hs by lia. apply H1. exact Hx.
Qed.

Fixpoint ctower (m : word -> option byte) (bb : byte) (L : list (Z * nat)) : word -> option byte :=
  match L with
  | [] => m
  | (a, k) :: L' => wbytes (ctower m bb L') (zw a) (repeat bb k)
  end.

Definition cst_ok (lo hi : Z) (p : Z * nat) : Prop :=
  0 <= fst p /\ fst p + Z.of_nat (snd p) <= 2 ^ 64 /\ lo <= fst p /\ fst p + Z.of_nat (snd p) <= hi.

Lemma ctower_filled : forall m bb lo hi L a k,
  Forall (cst_ok lo hi) L -> In (a, k) L -> filled (ctower m bb L) a (a + Z.of_nat k) bb.
Proof.
  intros m bb lo hi L. induction L as [|[a0 k0] L IH]; intros a k HF Hin; [destruct Hin|].
  inversion HF as [|x l Hok HF']; subst. unfold cst_ok in Hok. cbn [fst snd] in Hok.
  cbn [ctower]. destruct Hin as [E|Hin].
  - injection E as -> ->. apply filled_wbytes_new; lia.
  - apply filled_wbytes_keep; [lia | lia |]. apply IH; assumption.
Qed.

Lemma ctower_same : forall m bb lo hi L,
  Forall (cst_ok lo hi) L -> same_outside m (ctower m bb L) lo hi.
Proof.
  intros m bb lo hi L. induction L as [|[a0 k0] L IH]; intros HF; cbn [ctower].
  - apply same_outside_refl.
  - inversion HF as [|x l Hok HF']; subst. unfold cst_ok in Hok. cbn [fst snd] in Hok.
    apply same_outside_wbytes; try lia. apply IH. exact HF'.
Qed.

Lemma ctower_grows : forall m bb L x, m x <> None -> ctower m bb L x <> None.
Proof.
  intros m bb L. induction L as [|[a0 k0] L IH]; intros x Hx; cbn [ctower]; [exact Hx|].
  apply wbytes_grows. apply IH. exact Hx.
Qed.

End FXG.
Ltac reify_tower t :=
  lazymatch t with
  | wbytes ?m (zw ?a) (repeat _ ?k) => let L := reify_tower m in constr:((a, k) :: L)
  | _ => constr:(@nil (Z * nat))
  end.
Ltac tower_base t :=
  lazymatch t with
  | wbytes ?m (zw _) (repeat _ _) => tower_base m
  | _ => t
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

End FXG.
Ltac fold_tower t bb :=
  let L := reify_tower t in let b := tower_base t in
  change t with (ctower b bb L).
Ltac prove_In := cbn [In]; repeat (first [ left; reflexivity | right ]).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

End FXG.
Ltac ffind :=
  first [ apply filled_wbytes_new'; [lia | lia | lia | lia]
        | apply filled_wbytes_keep; [lia | lia | ffind] ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

End FXG.
Ltac fsame :=
  first [ apply same_outside_refl
        | apply same_outside_wbytes; [lia | lia | lia | lia | fsame] ].
Ltac fgrows :=
  first [ exact (fun x H => H)
        | apply grows_wbytes; fgrows ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

Lemma land_neg_pow2 : forall x n, 0 <= n -> Z.land x (- 2 ^ n) = x - x mod 2 ^ n.
Proof.
  intros x n Hn.
  replace (- 2 ^ n) with (Z.lnot (Z.ones n)) by (unfold Z.ones; rewrite Z.shiftl_1_l; unfold Z.lnot; lia).
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  pose proof (Z.div_mod x (2 ^ n) ltac:(lia)). lia.
Qed.

Lemma land_m4 : forall x, Z.land x (-4) = x - x mod 4.
Proof. intros x. exact (land_neg_pow2 x 2 ltac:(lia)). Qed.
Lemma land_m32 : forall x, Z.land x (-32) = x - x mod 32.
Proof. intros x. exact (land_neg_pow2 x 5 ltac:(lia)). Qed.

Lemma land_4 : forall y, Z.land y 4 = y mod 8 - y mod 4.
Proof.
  intros y.
  assert (E7 : Z.land y 7 = y mod 8) by (change 7 with (Z.ones 3); apply Z.land_ones; lia).
  assert (E : Z.land y 4 = Z.land (Z.land y 7) 4).
  { rewrite <- Z.land_assoc. reflexivity. }
  rewrite E, E7.
  pose proof (Z.mod_pos_bound y 8 ltac:(lia)) as Hr.
  assert (H8 : forall r, 0 <= r < 8 -> Z.land r 4 = r - r mod 4).
  { intros r Hr8.
    pose proof (allb_ok 8 (fun r => Z.eqb (Z.land r 4) (r - r mod 4)) ltac:(vm_compute; reflexivity) r Hr8) as Hb.
    apply Z.eqb_eq in Hb. exact Hb. }
  rewrite H8 by lia.
  enough (E4 : (y mod 8) mod 4 = y mod 4) by lia.
  apply Z.mod_mod_divide. exists 2. reflexivity.
Qed.

Definition iv (a : Z) (k : nat) : Z * Z := (a, a + Z.of_nat k).

End FXG.
Ltac fentry HF :=
  first [ eapply (ctower_filled _ _ _ _ _ _ _ HF); prove_In | assumption ].
Ltac faccT HF H l :=
  lazymatch l with
  | nil => idtac
  | ?e :: ?rest =>
      let cd := eval cbv beta delta [iv] in e in
      lazymatch type of H with
      | filled ?M ?a ?b ?bb =>
          lazymatch cd with (?c, ?d) =>
            let H2 := fresh "F" in
            assert (H2 : filled M c d bb) by fentry HF;
            let H3 := fresh "F" in
            pose proof (filled_join M a b c d bb H H2 ltac:(lia)) as H3;
            clear H H2; rename H3 into H; faccT HF H rest
          end
      end
  end.
Ltac fcoverT HF l :=
  lazymatch goal with
  | |- filled ?M ?lo ?hi ?bb =>
      lazymatch l with
      | ?e :: ?rest =>
          let cd := eval cbv beta delta [iv] in e in
          lazymatch cd with (?c, ?d) =>
            let H := fresh "F" in
            assert (H : filled M c d bb) by fentry HF;
            faccT HF H rest;
            eapply (filled_sub M _ _ lo hi bb H); lia
          end
      end
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.



Lemma memset_lin_facts : forall s n : Z, exists K N1 B N2 q1 q2 : Z,
  K = (0 - s) mod 4 /\ N1 = Z.land (n - K) (-4) /\ B = Z.land (s + K) 4 /\
  N2 = Z.land (N1 - B + -24) (-32) /\
  0 <= K < 4 /\ N1 = 4 * q1 /\ n - K - 3 <= N1 <= n - K /\ (B = 0 \/ B = 4) /\
  N2 = 32 * q2 /\ N1 - B - 24 - 31 <= N2 <= N1 - B - 24.
Proof.
  intros s n.
  set (K := (0 - s) mod 4). set (N1 := Z.land (n - K) (-4)). set (B := Z.land (s + K) 4).
  set (N2 := Z.land (N1 - B + -24) (-32)).
  exists K, N1, B, N2, ((n - K) / 4), ((N1 - B + -24) / 32).
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  assert (LK : 0 <= K < 4) by (subst K; apply Z.mod_pos_bound; lia).
  assert (LN1 : N1 = 4 * ((n - K) / 4) /\ n - K - 3 <= N1 <= n - K).
  { subst N1. rewrite land_m4. pose proof (Z.div_mod (n - K) 4 ltac:(lia)).
    pose proof (Z.mod_pos_bound (n - K) 4 ltac:(lia)). lia. }
  assert (LB : B = 0 \/ B = 4).
  { subst B. rewrite land_4. pose proof (Z.mod_pos_bound (s + K) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (s + K) 4 ltac:(lia)).
    pose proof (Z.div_mod (s + K) 8 ltac:(lia)). pose proof (Z.div_mod (s + K) 4 ltac:(lia)). lia. }
  assert (LN2 : N2 = 32 * ((N1 - B + -24) / 32) /\ N1 - B - 24 - 31 <= N2 <= N1 - B - 24).
  { subst N2. rewrite land_m32. pose proof (Z.div_mod (N1 - B + -24) 32 ltac:(lia)).
    pose proof (Z.mod_pos_bound (N1 - B + -24) 32 ltac:(lia)). lia. }
  lia.
Qed.
End FXG.
