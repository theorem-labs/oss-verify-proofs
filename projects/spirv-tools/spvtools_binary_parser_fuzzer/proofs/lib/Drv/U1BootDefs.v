(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ArgvEnv RefLayout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Cls Require Import ClsTac.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Fixpoint after_last_slash (s : list byte) (i acc : nat) : nat :=
  match s with
  | [] => acc
  | b :: s' => after_last_slash s' (S i) (if bv_eqb b (Z_to_bv 8 47) then S i else acc)
  end.
Definition progname_off (s : list byte) : nat := after_last_slash s 0 0.

Definition RPH : PhdrInfo := {| ph_addr := 0x10040%N; ph_ent := 56%N; ph_num := 10%N |}.

Section Defs.
  Variable sp0 : word.
  Variable rdraw : EntryDraw.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.

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
      (Z_to_bv 64 0x102348) (word_to_le_bytes 8 envp_w))
      (Z_to_bv 64 0x1226b0) (word_to_le_bytes 8 auxv_w))
      (Z_to_bv 64 0x122710) (word_to_le_bytes 8 hw))
      (Z_to_bv 64 0x1226d8) (word_to_le_bytes 8 (Z_to_bv 64 4096)))
      (Z_to_bv 64 0x1226a0) (word_to_le_bytes 8 pn_w))
      (Z_to_bv 64 0x122698) (word_to_le_bytes 8 progname_w).

  Definition J_lsm (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0xd1798)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x6583c)).

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
      (Z_to_bv 64 0x122440) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 0x122450) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 0x122448) (word_to_le_bytes 8 (Z_to_bv 64 8)))
      (Z_to_bv 64 0x1226c0) (word_to_le_bytes 8 (Z_to_bv 64 0xe0)))
      (Z_to_bv 64 0x1226c8) (word_to_le_bytes 8 (Z_to_bv 64 8)))
      (Z_to_bv 64 0x102428) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 0x102410) (word_to_le_bytes 8 (Z_to_bv 64 0x102428)))
      (Z_to_bv 64 0x102350) (word_to_le_bytes 8 (Z_to_bv 64 0x102350)))
      (Z_to_bv 64 0x1226a8) [Z_to_bv 8 1])
      (Z_to_bv 64 0x102378) (word_to_le_bytes 4 (Z_to_bv 64 2)).

  Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x102370) (word_to_le_bytes 4 tid))
      (Z_to_bv 64 0x1023e8) (word_to_le_bytes 8 (Z_to_bv 64 0x1226e0)))
      (Z_to_bv 64 0x1023c8) (word_to_le_bytes 8 (Z_to_bv 64 0x1023c8)))
      (Z_to_bv 64 0x102358) (word_to_le_bytes 8 (Z_to_bv 64 0x102350)))
      (Z_to_bv 64 0x102360) (word_to_le_bytes 8 (Z_to_bv 64 0x102350)))
      (Z_to_bv 64 0x102368) (word_to_le_bytes 8 (Z_to_bv 64 0)).

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

  Definition D_fd (D : word -> option byte) : word -> option byte :=
    wbytes D (Z_to_bv 64 0xf0200) [Z_to_bv 8 1].

  Definition D_pre_ios (tid : word) : word -> option byte := D_tls tid D_libc.

  Definition D_main (tid : word) : word -> option byte := D_fd (D_pre_ios tid).

End Defs.

From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import RefMemcpyLib.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition canary_bytes (rdraw : EntryDraw) : list byte :=
  nth 0 (at_random_bytes (ed_random rdraw)) (Z_to_bv 8 0) :: Z_to_bv 8 0 :: firstn 6 (skipn 2 (at_random_bytes (ed_random rdraw))).
Definition canary (rdraw : EntryDraw) : word := Z_to_bv 64 (lez (canary_bytes rdraw)).

Lemma canary_le : forall r, word_to_le_bytes 8 (canary r) = canary_bytes r.
Proof.
  intros r. unfold canary, word_to_le_bytes.
  assert (Hl : length (canary_bytes r) = 8%nat) by reflexivity.
  pose proof (lez_bound_len (canary_bytes r) 8 Hl) as Hb.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
  change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Hb.
  rewrite Z.mod_small by lia.
  rewrite <- Hl at 1. apply Z_to_le_bytes_lez.
Qed.

Lemma Z_to_bv_u_plus0' : forall a : word, Z_to_bv 64 (bv_unsigned a + 0) = a.
Proof. intros a. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Lemma rdn_pointwise' : forall segs mem n (a : word) bs,
  length bs = n ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  (forall j, (j < n)%nat ->
     mem (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0))) ->
  rdn segs mem a n = Some bs.
Proof.
  intros segs mem n. induction n as [|n IH]; intros a bs Hlen Hnw Hpt.
  - destruct bs; [reflexivity | cbn in Hlen; lia].
  - destruct bs as [|b bs']; [cbn in Hlen; lia|]. cbn in Hlen.
    cbn [rdn].
    pose proof (Hpt 0%nat ltac:(lia)) as H0. cbn [nth Z.of_nat] in H0.
    rewrite Z_to_bv_u_plus0' in H0. rewrite H0.
    destruct n as [|n'].
    + destruct bs'; [reflexivity | cbn in Hlen; lia].
    + assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
      rewrite (IH (a + 1) bs'); [reflexivity | lia | lia |].
      intros j Hj. rewrite Hu1.
      replace (bv_unsigned a + 1 + Z.of_nat j)%Z with (bv_unsigned a + Z.of_nat (S j))%Z by lia.
      rewrite (Hpt (S j)) by lia. reflexivity.
Qed.

Lemma rd_guard_bytes : forall segs D b0 b1 b2 b3 b4 b5 b6 b7,
  rdn segs (wbytes (wbytes (wbytes D (Z_to_bv 64 1189512) [b0; b1; b2; b3]) (Z_to_bv 64 1189516) [b4; b5; b6; b7])
             (Z_to_bv 64 1189513) [Z_to_bv 8 0])
      (Z_to_bv 64 1189512) 8 = Some [b0; Z_to_bv 8 0; b2; b3; b4; b5; b6; b7].
Proof.
  intros. apply rdn_pointwise'; [reflexivity | apply Z.leb_le; vm_compute; reflexivity |].
  intros j Hj. destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; try reflexivity. lia.
Qed.

Lemma rd_guard : forall segs D r,
  rdn segs (wbytes (wbytes (wbytes D (Z_to_bv 64 1189512) (word_to_le_bytes 4 (LWv (firstn 4 (skipn 0 (at_random_bytes (ed_random r)))))))
             (Z_to_bv 64 1189516) (word_to_le_bytes 4 (LWv (firstn 4 (skipn 4 (at_random_bytes (ed_random r)))))))
             (Z_to_bv 64 1189513) [Z_to_bv 8 0])
      (Z_to_bv 64 1189512) 8 = Some (word_to_le_bytes 8 (canary r)).
Proof.
  intros segs D r. rewrite canary_le.
  rewrite !sw_bytes_LWv by (rewrite length_firstn, length_skipn, length_at_random_bytes; reflexivity).
  unfold canary_bytes. generalize (length_at_random_bytes (ed_random r)). generalize (at_random_bytes (ed_random r)) as l. intros l Hl.
  destruct l as [|c0 [|c1 [|c2 [|c3 [|c4 [|c5 [|c6 [|c7 l']]]]]]]]; cbn in Hl; try discriminate.
  cbn [firstn skipn nth]. apply rd_guard_bytes.
Qed.
