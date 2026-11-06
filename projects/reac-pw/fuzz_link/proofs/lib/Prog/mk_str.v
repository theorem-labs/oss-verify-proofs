(* reac-pw/fuzz_link, PLAIN build: facts about C strings in memory that the W2-own-mark walks use.
   Pure list and memory facts; no address of the image. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require Import StrFun.
Local Open Scope Z_scope.

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. exact H. Qed.

Lemma byte_zero : forall b : byte, bv_unsigned b = 0 -> b = zb 0.
Proof. intros b H. apply bv_eq. rewrite H. reflexivity. Qed.

Lemma byte_eq : forall a b : byte, bv_unsigned a = bv_unsigned b -> a = b.
Proof. intros a b H. apply bv_eq. exact H. Qed.

Lemma bz_zb0 : bv_unsigned (zb 0) = 0.
Proof. reflexivity. Qed.

Lemma no_nul_check : forall l, forallb (fun b => negb (bv_unsigned b =? 0)) l = true -> ~ In (zb 0) l.
Proof.
  intros l H Hin. rewrite forallb_forall in H. specialize (H _ Hin). rewrite bz_zb0 in H. discriminate.
Qed.

Lemma bytes_at_hd : forall m a b l, bytes_at rsegs m a (b :: l) -> mrd rsegs m (wa a) = Some b.
Proof.
  intros m a b l (_ & _ & H). specialize (H 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in H. exact H.
Qed.

Lemma bytes_at_tl : forall m a b l, bytes_at rsegs m a (b :: l) -> bytes_at rsegs m (a + 1) l.
Proof.
  intros m a b l H. change (b :: l) with ([b] ++ l) in H. apply bytes_at_app in H. exact (proj2 H).
Qed.

Lemma bytes_at_read1 : forall m (a : word) b l, bytes_at rsegs m (bv_unsigned a) (b :: l) ->
  ov_read_bytes rsegs m a 1 = Some [b].
Proof.
  intros m a b l H. pose proof (bytes_at_ov_read rsegs m (bv_unsigned a) (b :: l) 0 1 H ltac:(cbn; lia)) as R.
  cbn [Z.of_nat firstn skipn] in R. rewrite Z.add_0_r in R. unfold wa in R. rewrite Z_to_bv_bv_unsigned in R.
  exact R.
Qed.

Lemma bv_eqb_lit : forall z w, 0 <= z < 2 ^ 64 -> 0 <= w < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 w) = (z =? w).
Proof. intros z w Hz Hw. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma bv_eqb_true : forall a b : word, bv_eqb a b = true -> a = b.
Proof. intros a b H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

Lemma bv_eqb_false : forall a b : word, bv_eqb a b = false -> bv_unsigned a <> bv_unsigned b.
Proof. intros a b H. unfold bv_eqb in H. apply Z.eqb_neq in H. exact H. Qed.

Lemma bv_eqb_z0 : forall v, -2 ^ 63 <= v < 2 ^ 63 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with 18446744073709551616. change (2 ^ 63) with 9223372036854775808 in Hv.
  rewrite Z.mod_0_l by lia.
  destruct (Z.eqb_spec v 0) as [->|Hn]; [reflexivity|]. apply Z.eqb_neq. intros H.
  apply Z.mod_divide in H; [|lia]. destruct H as [q Hq]. lia.
Qed.

Lemma cstr_at_unique : forall m s1 a s2, cstr_at m a s1 -> cstr_at m a s2 -> s1 = s2.
Proof.
  intros m s1. induction s1 as [|x s1 IH]; intros a s2 [B1 N1] [B2 N2]; destruct s2 as [|y s2].
  - reflexivity.
  - cbn in B1, B2. apply bytes_at_hd in B1, B2. rewrite B1 in B2. injection B2 as E.
    exfalso. apply N2. left. symmetry. exact E.
  - cbn in B1, B2. apply bytes_at_hd in B1, B2. rewrite B1 in B2. injection B2 as E.
    exfalso. apply N1. left. exact E.
  - cbn [app] in B1, B2. pose proof (bytes_at_hd _ _ _ _ B1) as H1. pose proof (bytes_at_hd _ _ _ _ B2) as H2.
    rewrite H1 in H2. injection H2 as <-. f_equal.
    apply (IH (a + 1)).
    + split; [exact (bytes_at_tl _ _ _ _ B1) | intros H; apply N1; right; exact H].
    + split; [exact (bytes_at_tl _ _ _ _ B2) | intros H; apply N2; right; exact H].
Qed.

Lemma str_arg_unique : forall m a o1 o2, str_arg m a o1 -> str_arg m a o2 -> o1 = o2.
Proof.
  intros m a [s1|] [s2|]; cbn; intros H1 H2.
  - f_equal. exact (cstr_at_unique m s1 a s2 (proj2 H1) (proj2 H2)).
  - exfalso. exact (proj1 H1 H2).
  - exfalso. exact (proj1 H2 H1).
  - reflexivity.
Qed.

(* strncmp(s, p, k + 1) over two C strings when p has exactly k + 1 bytes *)
Lemma strncmp_walk_pref : forall p s k, ~ In (zb 0) s -> ~ In (zb 0) p -> length p = S k ->
  exists v, strncmp_walk (s ++ [zb 0]) (p ++ [zb 0]) k = Some v /\ -256 < v < 256 /\
            (v = 0 <-> firstn (S k) s = p).
Proof.
  induction p as [|b p IH]; intros s k Ns Np Lp; [cbn in Lp; discriminate|].
  assert (Hb : bv_unsigned b <> 0) by (intros E; apply Np; left; apply byte_zero; exact E).
  pose proof (byte_range b) as Rb.
  destruct s as [|a s].
  - exists (0 - bv_unsigned b). cbn [app strncmp_walk]. rewrite bz_zb0. cbn [Z.eqb orb].
    split; [reflexivity|]. split; [lia|]. split; [lia | cbn; discriminate].
  - assert (Ha : bv_unsigned a <> 0) by (intros E; apply Ns; left; apply byte_zero; exact E).
    pose proof (byte_range a) as Ra.
    cbn [app strncmp_walk].
    replace (bv_unsigned a =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ha).
    replace (bv_unsigned b =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hb).
    cbn [orb].
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [Eab|Nab].
    + apply byte_eq in Eab. subst b. cbn [negb]. rewrite orb_false_r.
      destruct k as [|k].
      * cbn [Nat.eqb]. exists (bv_unsigned a - bv_unsigned a). split; [reflexivity|]. split; [lia|].
        cbn in Lp. destruct p; [|cbn in Lp; discriminate]. cbn [firstn]. split; [reflexivity | lia].
      * cbn [Nat.eqb]. cbn in Lp. injection Lp as Lp.
        destruct (IH s k (fun H => Ns (or_intror H)) (fun H => Np (or_intror H)) Lp) as (v & Hv & Rv & Iv).
        exists v. split; [exact Hv|]. split; [exact Rv|].
        rewrite Iv. cbn [firstn]. split; [intros ->; reflexivity | intros H; injection H as H; exact H].
    + cbn [negb]. rewrite orb_true_r.
      exists (bv_unsigned a - bv_unsigned b). split; [reflexivity|]. split; [lia|].
      split; [lia|]. cbn [firstn]. intros H; injection H as H _. subst b. contradiction.
Qed.

Lemma S_PREFIX_no_nul : ~ In (zb 0) S_PREFIX.
Proof. apply no_nul_check. vm_compute. reflexivity. Qed.
Lemma S_VLAN_no_nul : ~ In (zb 0) S_VLAN.
Proof. apply no_nul_check. vm_compute. reflexivity. Qed.
Lemma S_SERVED_no_nul : ~ In (zb 0) S_SERVED.
Proof. apply no_nul_check. vm_compute. reflexivity. Qed.

Lemma strncmp_prefix : forall s, ~ In (zb 0) s ->
  exists v, strncmp_model (s ++ [zb 0]) (S_PREFIX ++ [zb 0]) 8 = Some v /\ -256 < v < 256 /\
            (v = 0 <-> has_prefix s = true).
Proof.
  intros s Ns. destruct (strncmp_walk_pref S_PREFIX s 7 Ns S_PREFIX_no_nul eq_refl) as (v & Hv & Rv & Iv).
  exists v. split; [exact Hv|]. split; [exact Rv|].
  unfold has_prefix. rewrite bl_eqb_iff. exact Iv.
Qed.

(* the policy strings, read out of the image *)
Lemma prefix_at : forall m, mem_inv rsegs m -> bytes_at rsegs m A_PREFIX (S_PREFIX ++ [zb 0]).
Proof. intros m MI. apply ro_bytes_at; [exact MI | unfold A_PREFIX; lia | cbn; unfold A_PREFIX; lia |].
  unfold A_PREFIX. vm_compute. repeat split; reflexivity. Qed.
Lemma vlan_at : forall m, mem_inv rsegs m -> bytes_at rsegs m A_VLAN (S_VLAN ++ [zb 0]).
Proof. intros m MI. apply ro_bytes_at; [exact MI | unfold A_VLAN; lia | cbn; unfold A_VLAN; lia |].
  unfold A_VLAN. vm_compute. repeat split; reflexivity. Qed.
Lemma served_at : forall m, mem_inv rsegs m -> bytes_at rsegs m A_SERVED (S_SERVED ++ [zb 0]).
Proof. intros m MI. apply ro_bytes_at; [exact MI | unfold A_SERVED; lia | cbn; unfold A_SERVED; lia |].
  unfold A_SERVED. vm_compute. repeat split; reflexivity. Qed.
Lemma empty_at : forall m, mem_inv rsegs m -> bytes_at rsegs m A_EMPTY [zb 0].
Proof. intros m MI. apply ro_bytes_at; [exact MI | unfold A_EMPTY; lia | cbn; unfold A_EMPTY; lia |].
  unfold A_EMPTY. vm_compute. repeat split; reflexivity. Qed.
