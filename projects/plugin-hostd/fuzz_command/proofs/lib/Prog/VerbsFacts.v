From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import Verbs StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import strcspn_c.
Import ListNotations.
Open Scope Z_scope.

Lemma sep_set : forall b : byte,
  existsb (fun c => Z.eqb (bv_unsigned c) (bv_unsigned b)) [Z_to_bv 8 32; Z_to_bv 8 9] = is_sep b.
Proof.
  intros b. cbn [existsb]. unfold is_sep.
  change (bv_unsigned (Z_to_bv 8 32)) with 32. change (bv_unsigned (Z_to_bv 8 9)) with 9.
  rewrite (Z.eqb_sym 32), (Z.eqb_sym 9), orb_false_r. reflexivity.
Qed.

Lemma sp_set : forall b : byte,
  existsb (fun c => Z.eqb (bv_unsigned c) (bv_unsigned b)) [Z_to_bv 8 32] = (bv_unsigned b =? 32).
Proof.
  intros b. cbn [existsb]. change (bv_unsigned (Z_to_bv 8 32)) with 32.
  rewrite (Z.eqb_sym 32), orb_false_r. reflexivity.
Qed.

Lemma cspn_tfirst : forall t, cspn_len (map (Z_to_bv 8) [32; 9]) t = length (tfirst t).
Proof.
  intros t. change (map (Z_to_bv 8) [32; 9]) with [Z_to_bv 8 32; Z_to_bv 8 9]. unfold tfirst.
  induction t as [|b t IH]; [reflexivity|].
  cbn [cspn_len upto]. rewrite sep_set.
  destruct (is_sep b); cbn [length]; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma cspn_vfirst : forall f, cspn_len [Z_to_bv 8 32] f = length (vfirst f).
Proof.
  unfold vfirst. induction f as [|b f IH]; [reflexivity|].
  cbn [cspn_len upto]. rewrite sp_set.
  destruct (bv_unsigned b =? 32); cbn [length]; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma verb_is_m_len_ne : forall tb f, length (tfirst tb) <> length (vfirst f) -> verb_is_m tb f = false.
Proof. intros tb f H. unfold verb_is_m. rewrite (proj2 (Nat.eqb_neq _ _) H). reflexivity. Qed.

Lemma upto_split : forall (p : byte -> bool) l, exists r, l = upto p l ++ r.
Proof.
  intros p l. induction l as [|b l [r IH]]; [exists []; reflexivity|].
  cbn [upto]. destruct (p b); [exists (b :: l); reflexivity|].
  exists r. cbn [app]. rewrite <- IH. reflexivity.
Qed.

Lemma upto_length : forall (p : byte -> bool) l, (length (upto p l) <= length l)%nat.
Proof.
  intros p l. induction l as [|b l IH]; [cbn; lia|]. cbn [upto]. destruct (p b); cbn [length]; lia.
Qed.

Lemma strncmp_walk_prefix : forall l1 r1 l2 r2 k,
  length l1 = S k -> length r1 = S k ->
  Forall (fun b => bv_unsigned b <> 0) l1 -> Forall (fun b => bv_unsigned b <> 0) r1 ->
  exists v, strncmp_walk (l1 ++ l2) (r1 ++ r2) k = Some v /\ -256 < v < 256 /\ (v =? 0) = list_eqb l1 r1.
Proof.
  induction l1 as [|a l1 IH]; intros r1 l2 r2 k Hl Hr Nl Nr; [discriminate|].
  destruct r1 as [|b r1]; [discriminate|].
  apply Forall_cons_iff in Nl. destruct Nl as [Na Nl]. apply Forall_cons_iff in Nr. destruct Nr as [Nb Nr].
  pose proof (bv_unsigned_in_range 8 a) as Ra. pose proof (bv_unsigned_in_range 8 b) as Rb.
  change (bv_modulus 8) with 256 in Ra, Rb.
  cbn [app strncmp_walk list_eqb].
  rewrite (proj2 (Z.eqb_neq _ _) Na), (proj2 (Z.eqb_neq _ _) Nb). cbn [orb].
  destruct k as [|k].
  - cbn [length] in Hl, Hr. destruct l1; [|discriminate]. destruct r1; [|discriminate].
    cbn [Nat.eqb orb list_eqb]. exists (bv_unsigned a - bv_unsigned b). split; [reflexivity|]. split; [lia|].
    rewrite andb_true_r. destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b));
      [apply Z.eqb_eq; lia | apply Z.eqb_neq; lia].
  - cbn [Nat.eqb orb]. cbn [length] in Hl, Hr.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|NE]; cbn [negb andb].
    + destruct (IH r1 l2 r2 k ltac:(lia) ltac:(lia) Nl Nr) as (v & Hv & Rv & Qv).
      exists v. split; [exact Hv|]. split; [exact Rv| exact Qv].
    + exists (bv_unsigned a - bv_unsigned b). split; [reflexivity|]. split; [lia|]. apply Z.eqb_neq. lia.
Qed.

Lemma strncmp_verb : forall tb f fs,
  Forall (fun b => bv_unsigned b <> 0) tb -> Forall (fun b => bv_unsigned b <> 0) f ->
  length (tfirst tb) = length (vfirst f) ->
  exists v, strncmp_model (tb ++ [Z_to_bv 8 0]) (f ++ Z_to_bv 8 0 :: fs) (Z.of_nat (length (vfirst f))) = Some v /\
            -256 < v < 256 /\ (v =? 0) = verb_is_m tb f.
Proof.
  intros tb f fs Nt Nf Hlen.
  unfold verb_is_m. rewrite Hlen, Nat.eqb_refl. cbn [andb].
  destruct (upto_split (fun b => bv_unsigned b =? 32) f) as [rf Ef]. fold (vfirst f) in Ef.
  assert (Lt : (length (vfirst f) <= length tb)%nat).
  { rewrite <- Hlen. apply upto_length. }
  unfold strncmp_model.
  destruct (length (vfirst f)) as [|k] eqn:Ek.
  - exists 0. split; [reflexivity|]. split; [lia|].
    apply length_zero_iff_nil in Ek. rewrite Ek. reflexivity.
  - rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbv iota.
    replace (Z.to_nat (Z.of_nat (S k) - 1)) with k by lia.
    assert (E1 : tb ++ [Z_to_bv 8 0] = firstn (S k) tb ++ (skipn (S k) tb ++ [Z_to_bv 8 0]))
      by (rewrite app_assoc, firstn_skipn; reflexivity).
    assert (E2 : f ++ Z_to_bv 8 0 :: fs = vfirst f ++ (rf ++ Z_to_bv 8 0 :: fs))
      by (rewrite app_assoc, <- Ef; reflexivity).
    rewrite E1, E2.
    rewrite Ef in Nf. apply Forall_app in Nf. destruct Nf as [Nf _].
    rewrite <- (firstn_skipn (S k) tb) in Nt. apply Forall_app in Nt. destruct Nt as [Nt _].
    apply strncmp_walk_prefix; [rewrite length_firstn; lia | exact Ek | exact Nt | exact Nf].
Qed.
