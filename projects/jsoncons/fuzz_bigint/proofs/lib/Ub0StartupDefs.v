(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the start-up memory is laid out from the launch input, mmap base and draw: argc, argv[0]'s pointer at the top of the stack block, AT_RANDOM's pointer by the CONFIG_RSEQ flag, and the auxv words musl's __init_libc stores (rseq_w); launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import StartupTac ArgvEnv RefLayout RefMemcpyLib.
Import ListNotations.
Open Scope bv_scope.

Abbreviation RPH := Ubsan.M.phdrs.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require PropExec.
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
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 : word.
  Variable rdraw : EntryDraw.
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation ev := (in_envp inp) (only parsing).
  Local Notation uid := (in_uid inp) (only parsing).
  Local Notation hw := (in_hwcap inp) (only parsing).
  Variable rnd : bv 128.

  Definition aux_base : word := Z_to_bv 64 (bv_unsigned sp0 - 368).
  Definition argv_w : word := Z_to_bv 64 (bv_unsigned sp0 + 8).
  Definition envp_w : word := Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)).
  Definition auxv_w : word :=
    Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev)).
  Definition argc_w : word := argcN inp.

  Definition pn_w : word := cat_argv_ptr (ed_top rdraw) av ev (in_execfn inp) 0.
  Definition progname_w : word :=
    Z_to_bv 64 (bv_unsigned pn_w + Z.of_nat (progname_off (nth 0 av []))).

  Definition rnd_w : word := at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev.

  Definition D_libc : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (fun _ => None)
      (Z_to_bv 64 0x70e68) (word_to_le_bytes 8 envp_w))
      (Z_to_bv 64 0x911d0) (word_to_le_bytes 8 auxv_w))
      (Z_to_bv 64 0x91230) (word_to_le_bytes 8 hw))
      (Z_to_bv 64 0x911f8) (word_to_le_bytes 8 (Z_to_bv 64 4096)))
      (Z_to_bv 64 0x911c0) (word_to_le_bytes 8 pn_w))
      (Z_to_bv 64 0x911b8) (word_to_le_bytes 8 progname_w).

  Definition J_lsm (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x4b964)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x20348)).

  (* musl's __init_libc stores aux[t] = v for each auxv pair with t < AUX_CNT
     (38), in the kernel's order ([StackLayout.auxv_entries]); the cache
     words (types 40-47) and AT_MINSIGSTKSZ (51) are skipped.  The two
     CONFIG_RSEQ slots (aux[27], aux[28]) hold the kernel's values when the
     build has rseq; without it they keep the memset's zeros, which is what
     [rseq_w] states, so the image has one shape for both builds. *)
  Definition rseq_w (z : Z) : word :=
    if kb_rseq (in_kernel inp) then Z_to_bv 64 z else Z_to_bv 64 0.

  Definition J_aux (Jf : word -> option byte) : word -> option byte :=
    wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
      (wbytes Jf aux_base (zeros 304))
      (Z_to_bv 64 (bv_unsigned sp0 - 104)) (word_to_le_bytes 8 (la_sysinfo_ehdr (launch_auxv inp sp0 mbase))))
      (Z_to_bv 64 (bv_unsigned sp0 - 240)) (word_to_le_bytes 8 hw))
      (Z_to_bv 64 (bv_unsigned sp0 - 320)) (word_to_le_bytes 8 (Z_to_bv 64 4096)))
      (Z_to_bv 64 (bv_unsigned sp0 - 232)) (word_to_le_bytes 8 (Z_to_bv 64 100)))
      (Z_to_bv 64 (bv_unsigned sp0 - 344)) (word_to_le_bytes 8 (Z_to_bv 64 0x10040)))
      (Z_to_bv 64 (bv_unsigned sp0 - 336)) (word_to_le_bytes 8 (Z_to_bv 64 56)))
      (Z_to_bv 64 (bv_unsigned sp0 - 328)) (word_to_le_bytes 8 (Z_to_bv 64 10)))
      (Z_to_bv 64 (bv_unsigned sp0 - 312)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 304)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 296)) (word_to_le_bytes 8 entry))
      (Z_to_bv 64 (bv_unsigned sp0 - 280)) (word_to_le_bytes 8 uid))
      (Z_to_bv 64 (bv_unsigned sp0 - 272)) (word_to_le_bytes 8 uid))
      (Z_to_bv 64 (bv_unsigned sp0 - 264)) (word_to_le_bytes 8 (in_gid inp)))
      (Z_to_bv 64 (bv_unsigned sp0 - 256)) (word_to_le_bytes 8 (in_gid inp)))
      (Z_to_bv 64 (bv_unsigned sp0 - 184)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 168)) (word_to_le_bytes 8 rnd_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 120)) (word_to_le_bytes 8 (at_execfn_ptr (ed_top rdraw) (in_execfn inp))))
      (Z_to_bv 64 (bv_unsigned sp0 - 152)) (word_to_le_bytes 8 (rseq_w 28)))
      (Z_to_bv 64 (bv_unsigned sp0 - 144)) (word_to_le_bytes 8 (rseq_w 32)).

  Definition D_tlsA (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x90f60) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 0x90f70) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 0x90f68) (word_to_le_bytes 8 (Z_to_bv 64 8)))
      (Z_to_bv 64 0x911e0) (word_to_le_bytes 8 (Z_to_bv 64 0xe0)))
      (Z_to_bv 64 0x911e8) (word_to_le_bytes 8 (Z_to_bv 64 8)))
      (Z_to_bv 64 0x70f48) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 0x70f30) (word_to_le_bytes 8 (Z_to_bv 64 0x70f48)))
      (Z_to_bv 64 0x70e70) (word_to_le_bytes 8 (Z_to_bv 64 0x70e70)))
      (Z_to_bv 64 0x911c8) [Z_to_bv 8 1])
      (Z_to_bv 64 0x70e98) (word_to_le_bytes 4 (Z_to_bv 64 2)).

  Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x70e90) (word_to_le_bytes 4 tid))
      (Z_to_bv 64 0x70f08) (word_to_le_bytes 8 (Z_to_bv 64 0x91200)))
      (Z_to_bv 64 0x70ee8) (word_to_le_bytes 8 (Z_to_bv 64 0x70ee8)))
      (Z_to_bv 64 0x70e78) (word_to_le_bytes 8 (Z_to_bv 64 0x70e70)))
      (Z_to_bv 64 0x70e80) (word_to_le_bytes 8 (Z_to_bv 64 0x70e70)))
      (Z_to_bv 64 0x70e88) (word_to_le_bytes 8 (Z_to_bv 64 0)).

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
      (Z_to_bv 64 0x911a8) (word_to_le_bytes 4 (rlw rnd 0)))
      (Z_to_bv 64 0x911ac) (word_to_le_bytes 4 (rlw rnd 4)))
      (Z_to_bv 64 0x911a9) [Z_to_bv 8 0])
      (Z_to_bv 64 0x70f28) (word_to_le_bytes 8 (canary_w rnd)).

  Definition D_fd (D : word -> option byte) : word -> option byte :=
    wbytes D (Z_to_bv 64 0x60370) [Z_to_bv 8 1].

  Definition D_main (tid : word) : word -> option byte := D_fd (D_ssp (D_tls tid D_libc)).

End Defs.

End FPX_1.
