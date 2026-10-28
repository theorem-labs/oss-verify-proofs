(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import StartupTac ArgvEnv RefLayout RefMemcpyLib.
Import ListNotations.
Open Scope bv_scope.

Abbreviation RPH := Ubsan.M.phdrs.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1. Context {fx : PropExec.FPState}.

Fixpoint after_last_slash (s : list byte) (i acc : nat) : nat :=
  match s with
  | [] => acc
  | b :: s' => after_last_slash s' (S i) (if bv_eqb b (Z_to_bv 8 47) then S i else acc)
  end.
Definition progname_off (s : list byte) : nat := after_last_slash s 0 0.

Lemma after_last_slash_le : forall s i acc, (acc <= i)%nat ->
  (after_last_slash s i acc <= i + length s)%nat.
Proof.
  induction s as [|c s IH]; intros i acc H; cbn [after_last_slash length]; [lia|].
  etransitivity; [apply IH; destruct (bv_eqb _ _); lia | lia].
Qed.

Lemma progname_off_le : forall s, (progname_off s <= length s)%nat.
Proof. intro s. unfold progname_off. pose proof (after_last_slash_le s 0 0). lia. Qed.

Definition rnd4 (rnd : bv 128) (j : nat) : list byte := firstn 4 (skipn j (at_random_bytes rnd)).
Definition rnd4w (rnd : bv 128) (j : nat) : word := Z_to_bv 64 (bytes_le_to_Z (rnd4 rnd j)).
Definition rlw (rnd : bv 128) (j : nat) : word := v_lw (rnd4w rnd j).
Definition guard_bytes (rnd : bv 128) : list byte :=
  firstn 1 (word_to_le_bytes 4 (rlw rnd 0)) ++ [Z_to_bv 8 0] ++ sub (word_to_le_bytes 4 (rlw rnd 0)) 2 2
  ++ word_to_le_bytes 4 (rlw rnd 4).
Definition canary_w (rnd : bv 128) : word := Z_to_bv 64 (bytes_le_to_Z (guard_bytes rnd)).

Lemma rnd4_eq : forall rnd j, firstn 4 (skipn j (at_random_bytes rnd)) = rnd4 rnd j.
Proof. reflexivity. Qed.
Lemma length_rnd4 : forall rnd j, (j + 4 <= 16)%nat -> length (rnd4 rnd j) = 4%nat.
Proof. intros rnd j Hj. unfold rnd4. rewrite length_firstn, length_skipn, length_at_random_bytes. lia. Qed.
Lemma rnd4_val : forall rnd j, bytes_le_to_Z (rnd4 rnd j) = bv_unsigned (rnd4w rnd j).
Proof.
  intros rnd j. unfold rnd4w. symmetry.
  pose proof (bytes_le_to_Z_nonneg (rnd4 rnd j)). pose proof (bytes_le_to_Z_bound (rnd4 rnd j)) as Hb.
  assert (Hl : (length (rnd4 rnd j) <= 4)%nat).
  { unfold rnd4. rewrite length_firstn. lia. }
  assert (2 ^ (8 * Z.of_nat (length (rnd4 rnd j))) <= 2 ^ 32)%Z by (apply Z.pow_le_mono_r; lia).
  apply u_Z2bv; lia.
Qed.
Lemma length_word_to_le_bytes : forall n v, length (word_to_le_bytes n v) = n.
Proof. intros. unfold word_to_le_bytes. apply length_Z_to_le_bytes. Qed.
Lemma length_guard_bytes : forall rnd, length (guard_bytes rnd) = 8%nat.
Proof.
  intro rnd. unfold guard_bytes, sub. rewrite !length_app, !length_firstn, length_skipn, !length_word_to_le_bytes. reflexivity.
Qed.
Lemma canary_val : forall rnd, bytes_le_to_Z (guard_bytes rnd) = bv_unsigned (canary_w rnd).
Proof.
  intro rnd. unfold canary_w. symmetry.
  pose proof (bytes_le_to_Z_nonneg (guard_bytes rnd)). pose proof (bytes_le_to_Z_bound (guard_bytes rnd)) as Hb.
  rewrite length_guard_bytes in Hb. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in Hb. apply u_Z2bv; lia.
Qed.
Lemma canary_bytes : forall rnd, word_to_le_bytes 8 (canary_w rnd) = guard_bytes rnd.
Proof.
  intro rnd. unfold canary_w, word_to_le_bytes.
  pose proof (canary_val rnd) as Hv. unfold canary_w in Hv. rewrite <- Hv.
  rewrite <- (length_guard_bytes rnd) at 1. apply Z_to_le_bytes_lez.
Qed.

Lemma rd_guard_gen : forall segs (D : word -> option byte) (w0 w4 : list byte) (g : Z),
  length w0 = 4%nat -> length w4 = 4%nat ->
  (0 <= g)%Z -> (g + 8 < 2^64)%Z ->
  rdn segs (wbytes (wbytes (wbytes D (Z_to_bv 64 g) w0)
                          (Z_to_bv 64 (g + 4)) w4)
                  (Z_to_bv 64 (g + 1)) [Z_to_bv 8 0]) (Z_to_bv 64 g) 8 = Some (firstn 1 w0 ++ [Z_to_bv 8 0] ++ sub w0 2 2 ++ w4).
Proof.
  intros segs D w0 w4 g L0 L4 Hg0 Hg1.
  assert (U : forall k, (0 <= k <= 8)%Z -> bv_unsigned (Z_to_bv 64 (g + k)) = (g + k)%Z) by (intros; apply u_Z2bv; lia).
  assert (U0 : bv_unsigned (Z_to_bv 64 g) = g) by (apply u_Z2bv; lia).
  assert (A : forall k j z, (0 <= k)%Z -> (k + Z.of_nat j <= 8)%Z -> (z = k + Z.of_nat j)%Z ->
             (Z_to_bv 64 (g + k) + nat_to_word j)%bv = Z_to_bv 64 (g + z)).
  { intros k j z Hk Hj ->. rewrite at_nat. unfold at_. rewrite U by lia. f_equal. lia. }
  change 8%nat with (1 + (1 + (2 + 4)))%nat.
  apply rdn_app.
  { rewrite rdn_wbytes_out by (cbn [length]; rewrite ?U, ?U0; lia).
    rewrite rdn_wbytes_out by (rewrite ?U, ?U0, ?L4; lia).
    apply (rdn_firstn segs _ 4); [|lia]. rewrite <- L0. apply rdn_wbytes_hit. rewrite U0, L0. lia. }
  replace (Z_to_bv 64 g + nat_to_word 1)%bv with (Z_to_bv 64 (g + 1))
    by (rewrite at_nat; unfold at_; rewrite U0; reflexivity).
  apply rdn_app.
  { apply (rdn_wbytes_hit segs [Z_to_bv 8 0]). cbn [length]. rewrite U; lia. }
  rewrite (A 1%Z 1%nat 2%Z) by lia.
  apply rdn_app.
  { rewrite rdn_wbytes_out by (cbn [length]; rewrite ?U; lia).
    rewrite rdn_wbytes_out by (rewrite ?U, ?L4; lia).
    replace (Z_to_bv 64 (g + 2)) with (at_ (Z_to_bv 64 g) (Z.of_nat 2)) by (unfold at_; rewrite U0; reflexivity).
    apply (rdn_sub segs _ 4). 2: lia. rewrite <- L0. apply rdn_wbytes_hit. rewrite U0, L0. lia. }
  rewrite (A 2%Z 2%nat 4%Z) by lia.
  rewrite rdn_wbytes_out by (cbn [length]; rewrite ?U; lia).
  rewrite <- L4 at 1. apply rdn_wbytes_hit. rewrite U, L4; lia.
Qed.

Lemma rd_guard_at : forall segs (D : word -> option byte) rnd (g : Z),
  (0 <= g)%Z -> (g + 8 < 2^64)%Z ->
  rdn segs (wbytes (wbytes (wbytes D (Z_to_bv 64 g) (word_to_le_bytes 4 (rlw rnd 0)))
                          (Z_to_bv 64 (g + 4)) (word_to_le_bytes 4 (rlw rnd 4)))
                  (Z_to_bv 64 (g + 1)) [Z_to_bv 8 0]) (Z_to_bv 64 g) 8 = Some (guard_bytes rnd).
Proof.
  intros. unfold guard_bytes. apply rd_guard_gen; try assumption; apply length_word_to_le_bytes.
Qed.

Section Defs.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rnd : bv 128.

  Definition aux_base : word := Z_to_bv 64 (bv_unsigned sp0 - 368).

  Definition argv_w : word := Z_to_bv 64 (bv_unsigned sp0 + 8).
  Definition envp_w : word := Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)).
  Definition auxv_w : word :=
    Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev)).
  Definition argc_w : word := argcN av.

  Definition pn_w : word := cat_argv_ptr sp0 av ev 0.
  Definition progname_w : word :=
    Z_to_bv 64 (bv_unsigned pn_w + Z.of_nat (progname_off (nth 0 av []))).

  Definition rnd_w : word := at_random_ptr sp0 av ev.

  Definition D_libc : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (fun _ => None)
      (Z_to_bv 64 0xd6730) (word_to_le_bytes 8 envp_w))
      (Z_to_bv 64 0xf6a98) (word_to_le_bytes 8 auxv_w))
      (Z_to_bv 64 0xf6af8) (word_to_le_bytes 8 hw))
      (Z_to_bv 64 0xf6ac0) (word_to_le_bytes 8 (Z_to_bv 64 4096)))
      (Z_to_bv 64 0xf6a88) (word_to_le_bytes 8 pn_w))
      (Z_to_bv 64 0xf6a80) (word_to_le_bytes 8 progname_w).

  Definition J_lsm (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0xa6aa4)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x3924c)).

  Definition J_aux (Jf : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
      (wbytes Jf aux_base (zeros 304))
      (Z_to_bv 64 (bv_unsigned sp0 - 344)) (word_to_le_bytes 8 (Z_to_bv 64 0x10040)))
      (Z_to_bv 64 (bv_unsigned sp0 - 336)) (word_to_le_bytes 8 (Z_to_bv 64 56)))
      (Z_to_bv 64 (bv_unsigned sp0 - 328)) (word_to_le_bytes 8 (Z_to_bv 64 10)))
      (Z_to_bv 64 (bv_unsigned sp0 - 240)) (word_to_le_bytes 8 hw))
      (Z_to_bv 64 (bv_unsigned sp0 - 320)) (word_to_le_bytes 8 (Z_to_bv 64 4096)))
      (Z_to_bv 64 (bv_unsigned sp0 - 280)) (word_to_le_bytes 8 uid))
      (Z_to_bv 64 (bv_unsigned sp0 - 272)) (word_to_le_bytes 8 uid))
      (Z_to_bv 64 (bv_unsigned sp0 - 184)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 168)) (word_to_le_bytes 8 rnd_w).

  Definition D_tlsA (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0xf6828) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 0xf6838) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 0xf6830) (word_to_le_bytes 8 (Z_to_bv 64 8)))
      (Z_to_bv 64 0xf6aa8) (word_to_le_bytes 8 (Z_to_bv 64 0xe0)))
      (Z_to_bv 64 0xf6ab0) (word_to_le_bytes 8 (Z_to_bv 64 8)))
      (Z_to_bv 64 0xd6810) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 0xd67f8) (word_to_le_bytes 8 (Z_to_bv 64 0xd6810)))
      (Z_to_bv 64 0xd6738) (word_to_le_bytes 8 (Z_to_bv 64 0xd6738)))
      (Z_to_bv 64 0xf6a90) [Z_to_bv 8 1])
      (Z_to_bv 64 0xd6760) (word_to_le_bytes 4 (Z_to_bv 64 2)).

  Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0xd6758) (word_to_le_bytes 4 tid))
      (Z_to_bv 64 0xd67d0) (word_to_le_bytes 8 (Z_to_bv 64 0xf6ac8)))
      (Z_to_bv 64 0xd67b0) (word_to_le_bytes 8 (Z_to_bv 64 0xd67b0)))
      (Z_to_bv 64 0xd6740) (word_to_le_bytes 8 (Z_to_bv 64 0xd6738)))
      (Z_to_bv 64 0xd6748) (word_to_le_bytes 8 (Z_to_bv 64 0xd6738)))
      (Z_to_bv 64 0xd6750) (word_to_le_bytes 8 (Z_to_bv 64 0)).

  Definition D_tls (tid : word) (D : word -> option byte) : word -> option byte :=
    D_tlsB tid (D_tlsA D).

  Definition J_tls (J : word -> option byte) (ra s0 s1 s2 s3 s4 s5 : word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 s0))
      (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1))
      (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 s2))
      (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 s3))
      (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 s4))
      (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 s5).

  Definition D_ssp (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0xf6a70) (word_to_le_bytes 4 (rlw rnd 0)))
      (Z_to_bv 64 0xf6a74) (word_to_le_bytes 4 (rlw rnd 4)))
      (Z_to_bv 64 0xf6a71) [Z_to_bv 8 0])
      (Z_to_bv 64 0xd67f0) (word_to_le_bytes 8 (canary_w rnd)).

  Definition D_fd (D : word -> option byte) : word -> option byte :=
    wbytes D (Z_to_bv 64 0xc4d70) [Z_to_bv 8 1].

  Definition D_main (tid : word) : word -> option byte := D_fd (D_ssp (D_tls tid D_libc)).

End Defs.

End FPX_1.
