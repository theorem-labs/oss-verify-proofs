(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the section takes the launch input, mmap base and entry point in place of argv, envp, uid and AT_HWCAP; CDefT name table removed and D_libc, J_lsm, J_aux, D_tlsA, D_tlsB, J_tls, D_ssp and guard_read decoded to plain text; J_aux writes the revision's auxv, adding AT_SYSINFO_EHDR, AT_CLKTCK, AT_BASE, AT_FLAGS, AT_ENTRY, AT_GID, AT_EGID, AT_EXECFN and the two CONFIG_RSEQ slots; argc_w, pn_w and rnd_w follow the new layout, with new execfn_w and rseq_w); and launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Plain.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import StartupTac ArgvEnv Layout.
Import ListNotations.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.


Abbreviation RPH := Plain.M.phdrs.

(* [comment removed for export] *)
Fixpoint after_last_slash (s : list byte) (i acc : nat) : nat :=
  match s with
  | [] => acc
  | b :: s' => after_last_slash s' (S i) (if bv_eqb b (Z_to_bv 8 47) then S i else acc)
  end.
Definition progname_off (s : list byte) : nat := after_last_slash s 0 0.



Section Defs.
  Variable sp0 : word.
  Variable inp : ProcInput.    (* argv, envp, uid, gid, AT_HWCAP, the kernel build and the exec file name *)
  Variable mbase : word.       (* the mmap base the auxv's AT_SYSINFO_EHDR reads *)
  Variable entry : word.       (* AT_ENTRY *)
  Variable rdraw : EntryDraw.  (* [comment removed for export] *)
  Local Notation av := (in_argv inp).
  Local Notation ev := (in_envp inp).
  Local Notation uid := (in_uid inp).
  Local Notation gid := (in_gid inp).
  Local Notation hw := (in_hwcap inp).
  Local Notation rseq := (kb_rseq (in_kernel inp)).

  (* [comment removed for export] *)
  Definition aux_base : word := Z_to_bv 64 (bv_unsigned sp0 - 368).
  (* [comment removed for export] *)
  Definition argv_w : word := Z_to_bv 64 (bv_unsigned sp0 + 8).
  Definition envp_w : word := Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)).
  Definition auxv_w : word :=
    Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev)).
  Definition argc_w : word := argcN inp.
  (* [comment removed for export] *)
  Definition pn_w : word := cat_argv_ptr (ed_top rdraw) av ev (in_execfn inp) 0.
  Definition progname_w : word :=
    Z_to_bv 64 (bv_unsigned pn_w + Z.of_nat (progname_off (nth 0 av []))).
  (* [comment removed for export] *)
  Definition rnd_w : word := at_random_ptr sp0 rseq av ev.
  Definition execfn_w : word := at_execfn_ptr (ed_top rdraw) (in_execfn inp).
  (* [comment removed for export] *)
  Definition rnd_bytes : list byte := at_random_bytes (ed_random rdraw).
  Definition guard_lo_bytes : list byte := firstn 4 rnd_bytes.
  Definition guard_hi_bytes : list byte := firstn 4 (skipn 4 rnd_bytes).
  (* [comment removed for export] *)
  Definition guard_lo : word := v_lw (Z_to_bv 64 (bytes_le_to_Z guard_lo_bytes)).
  Definition guard_hi : word := v_lw (Z_to_bv 64 (bytes_le_to_Z guard_hi_bytes)).
  (* [comment removed for export] *)
  Definition canary_bytes : list byte :=
    firstn 1 rnd_bytes ++ [Z_to_bv 8 0] ++ firstn 6 (skipn 2 rnd_bytes).
  Definition canary_w : word := Z_to_bv 64 (bytes_le_to_Z canary_bytes).
  (* [comment removed for export] *)
  Definition secret_bytes : list byte := firstn 8 (skipn 8 rnd_bytes).
  Definition secret_w : word := Z_to_bv 64 (bytes_le_to_Z secret_bytes).

  (* [comment removed for export] *)
  Definition D_libc : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (fun _ => None)
      (Z_to_bv 64 0x598f8) (word_to_le_bytes 8 envp_w))
      (Z_to_bv 64 0x79c58) (word_to_le_bytes 8 auxv_w))
      (Z_to_bv 64 0x79cb8) (word_to_le_bytes 8 hw))
      (Z_to_bv 64 0x79c80) (word_to_le_bytes 8 (Z_to_bv 64 4096)))
      (Z_to_bv 64 0x79c48) (word_to_le_bytes 8 pn_w))
      (Z_to_bv 64 0x79c40) (word_to_le_bytes 8 progname_w).

  (* [comment removed for export] *)
  Definition J_lsm (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x3bb40)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x1cdcc)).

  (* [comment removed for export] *)
  (* musl's __init_libc stores aux[t] = v for each auxv pair with t < AUX_CNT (38), in the
     kernel's order ([StackLayout.auxv_entries]); the cache words (types 40-47) and
     AT_MINSIGSTKSZ (51) are skipped, and aux[k] sits at aux_base + 8 k.  The two CONFIG_RSEQ
     slots (aux[27], aux[28]) hold the kernel's values when the build has rseq; without it they
     keep the memset's zeros, which is what [rseq_w] states, so the image has one shape for
     both builds (the wbytes layers are the walk's store sequence, so the order is forced). *)
  Definition rseq_w (z : Z) : word := if rseq then Z_to_bv 64 z else Z_to_bv 64 0.

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
      (Z_to_bv 64 (bv_unsigned sp0 - 264)) (word_to_le_bytes 8 gid))
      (Z_to_bv 64 (bv_unsigned sp0 - 256)) (word_to_le_bytes 8 gid))
      (Z_to_bv 64 (bv_unsigned sp0 - 184)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 168)) (word_to_le_bytes 8 rnd_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 120)) (word_to_le_bytes 8 execfn_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 152)) (word_to_le_bytes 8 (rseq_w 28)))
      (Z_to_bv 64 (bv_unsigned sp0 - 144)) (word_to_le_bytes 8 (rseq_w 32)).

  (* [comment removed for export] *)
  Definition D_tlsA (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x799f0) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 0x79a00) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 0x799f8) (word_to_le_bytes 8 (Z_to_bv 64 8)))
      (Z_to_bv 64 0x79c68) (word_to_le_bytes 8 (Z_to_bv 64 224)))
      (Z_to_bv 64 0x79c70) (word_to_le_bytes 8 (Z_to_bv 64 8)))
      (Z_to_bv 64 0x599d8) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 0x599c0) (word_to_le_bytes 8 (Z_to_bv 64 0x599d8)))
      (Z_to_bv 64 0x59900) (word_to_le_bytes 8 (Z_to_bv 64 0x59900)))
      (Z_to_bv 64 0x79c50) [Z_to_bv 8 1])
      (Z_to_bv 64 0x59928) (word_to_le_bytes 4 (Z_to_bv 64 2)).

  Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x59920) (word_to_le_bytes 4 tid))
      (Z_to_bv 64 0x59998) (word_to_le_bytes 8 (Z_to_bv 64 0x79c88)))
      (Z_to_bv 64 0x59978) (word_to_le_bytes 8 (Z_to_bv 64 0x59978)))
      (Z_to_bv 64 0x59908) (word_to_le_bytes 8 (Z_to_bv 64 0x59900)))
      (Z_to_bv 64 0x59910) (word_to_le_bytes 8 (Z_to_bv 64 0x59900)))
      (Z_to_bv 64 0x59918) (word_to_le_bytes 8 (Z_to_bv 64 0)).

  Definition D_tls (tid : word) (D : word -> option byte) : word -> option byte :=
    D_tlsB tid (D_tlsA D).

  (* [comment removed for export] *)
  Definition J_tls (J : word -> option byte) (ra s0 s1 s2 s3 s4 s5 : word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 s0))
      (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1))
      (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 s2))
      (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 s3))
      (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 s4))
      (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 s5).

  (* [comment removed for export] *)
  Definition D_ssp (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x79c30) (word_to_le_bytes 4 guard_lo))
      (Z_to_bv 64 0x79c34) (word_to_le_bytes 4 guard_hi))
      (Z_to_bv 64 0x79c31) [Z_to_bv 8 0])
      (Z_to_bv 64 0x599b8) (word_to_le_bytes 8 canary_w).

  (* [comment removed for export] *)
  #[using="Type"] Lemma length_rnd_bytes : length rnd_bytes = 16%nat.
  Proof. unfold rnd_bytes. apply length_at_random_bytes. Qed.
  #[using="Type"] Lemma length_guard_lo_bytes : length guard_lo_bytes = 4%nat.
  Proof. unfold guard_lo_bytes. rewrite firstn_length, length_rnd_bytes. reflexivity. Qed.
  #[using="Type"] Lemma length_guard_hi_bytes : length guard_hi_bytes = 4%nat.
  Proof. unfold guard_hi_bytes. rewrite firstn_length, skipn_length, length_rnd_bytes. reflexivity. Qed.
  #[using="Type"] Lemma length_canary_bytes : length canary_bytes = 8%nat.
  Proof. unfold canary_bytes. rewrite !app_length, !firstn_length, skipn_length, length_rnd_bytes. reflexivity. Qed.
  #[using="Type"] Lemma length_secret_bytes : length secret_bytes = 8%nat.
  Proof. unfold secret_bytes. rewrite firstn_length, skipn_length, length_rnd_bytes. reflexivity. Qed.

  #[using="Type"] Lemma bytes_le_to_Z_lt : forall bs k, length bs = k -> (0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat k))%Z.
  Proof.
    intros bs k <-. split; [apply bytes_le_to_Z_nonneg | apply bytes_le_to_Z_bound].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma bytes_val : forall bs, (length bs <= 8)%nat -> bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bs)).
  Proof.
    intros bs Hl. pose proof (bytes_le_to_Z_lt bs (length bs) eq_refl) as B.
    assert (2 ^ (8 * Z.of_nat (length bs)) <= 2 ^ 64)%Z by (apply Z.pow_le_mono_r; lia).
    symmetry. apply u_Z2bv; lia.
  Qed.
  #[using="Type"] Lemma guard_lo_val : bytes_le_to_Z guard_lo_bytes = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z guard_lo_bytes)).
  Proof. apply bytes_val. rewrite length_guard_lo_bytes. lia. Qed.
  #[using="Type"] Lemma guard_hi_val : bytes_le_to_Z guard_hi_bytes = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z guard_hi_bytes)).
  Proof. apply bytes_val. rewrite length_guard_hi_bytes. lia. Qed.
  #[using="Type"] Lemma canary_val : bytes_le_to_Z canary_bytes = bv_unsigned canary_w.
  Proof. unfold canary_w. apply bytes_val. rewrite length_canary_bytes. lia. Qed.
  #[using="Type"] Lemma secret_val : bytes_le_to_Z secret_bytes = bv_unsigned secret_w.
  Proof. unfold secret_w. apply bytes_val. rewrite length_secret_bytes. lia. Qed.


  (* [comment removed for export] *)
  #[using="Type"] Lemma lor_shl8_low' : forall b r, (0 <= b < 256)%Z -> (0 <= r)%Z -> Z_to_bv 8 (Z.lor b (Z.shiftl r 8)) = Z_to_bv 8 b.
  Proof.
    intros b r Hb Hr. apply bv_eq. rewrite !Z_to_bv_unsigned. change (bv_wrap 8 ?x) with (x mod 2^8)%Z. cbv beta.
    change (bv_wrap 8 b) with (b mod 2^8)%Z.
    apply Z.bits_inj'. intros i Hi.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    - rewrite !Z.mod_pow2_bits_low by lia. rewrite Z.lor_spec, Z.shiftl_spec by lia.
      rewrite (Z.testbit_neg_r r (i - 8)) by lia. apply orb_false_r.
    - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
  Qed.
  #[using="Type"] Lemma lor_shl8_high' : forall b r, (0 <= b < 256)%Z -> (0 <= r)%Z -> Z.shiftr (Z.lor b (Z.shiftl r 8)) 8 = r.
  Proof.
    intros b r Hb Hr. rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
    rewrite Z.shiftr_div_pow2, Z.div_small by lia. reflexivity.
  Qed.
  #[using="Type"] Lemma Z_to_le_bytes_to_Z' : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
  Proof.
    induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
    pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. pose proof (bytes_le_to_Z_nonneg bs).
    f_equal.
    - rewrite lor_shl8_low' by (cbn in Hb; lia). apply Z_to_bv_bv_unsigned.
    - rewrite lor_shl8_high' by (cbn in Hb; lia). exact IH.
  Qed.
  #[using="Type"] Lemma bv_wrap_swrap' : forall n z, bv_wrap n (bv_swrap n z) = bv_wrap n z.
  Proof.
    intros n z. unfold bv_swrap. unfold bv_wrap.
    pose proof (bv_modulus_pos n) as P.
    set (M := bv_modulus n) in *. set (h := bv_half_modulus n).
    assert (E : ((z + h) mod M = (z + h) - M * ((z + h) / M))%Z) by (pose proof (Z.div_mod (z+h) M ltac:(lia)); lia).
    rewrite E. replace (z + h - M * ((z + h) / M) - h)%Z with (z + (- ((z + h) / M)) * M)%Z by lia.
    rewrite Z.mod_add by lia. reflexivity.
  Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma lw_sw_bytes : forall bs, length bs = 4%nat ->
    word_to_le_bytes 4 (v_lw (Z_to_bv 64 (bytes_le_to_Z bs))) = bs.
  Proof.
    intros bs Hl. unfold word_to_le_bytes, v_lw.
    rewrite Z_to_bv_unsigned. rewrite (Z_to_le_bytes_wrap 4 64) by (cbn; lia).
    rewrite <- (Z_to_le_bytes_wrap 4 32 (bv_swrap 32 _)) by (cbn; lia).
    rewrite bv_wrap_swrap'. rewrite (Z_to_le_bytes_wrap 4 32) by (cbn; lia).
    rewrite <- (bytes_val bs) by (rewrite Hl; lia). rewrite <- Hl. apply Z_to_le_bytes_to_Z'.
  Qed.
  #[using="Type"] Lemma guard_lo_store : word_to_le_bytes 4 guard_lo = guard_lo_bytes.
  Proof. apply lw_sw_bytes. apply length_guard_lo_bytes. Qed.
  #[using="Type"] Lemma guard_hi_store : word_to_le_bytes 4 guard_hi = guard_hi_bytes.
  Proof. apply lw_sw_bytes. apply length_guard_hi_bytes. Qed.
  #[using="Type"] Lemma canary_store : word_to_le_bytes 8 canary_w = canary_bytes.
  Proof.
    unfold word_to_le_bytes. rewrite <- canary_val. rewrite <- length_canary_bytes. apply Z_to_le_bytes_to_Z'.
  Qed.
  #[using="Type"] Lemma secret_store : word_to_le_bytes 8 secret_w = secret_bytes.
  Proof.
    unfold word_to_le_bytes. rewrite <- secret_val. rewrite <- length_secret_bytes. apply Z_to_le_bytes_to_Z'.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma guard_read : forall segs (DD : word -> option byte),
    rdn segs (wbytes (wbytes (wbytes DD (Z_to_bv 64 0x79c30) (word_to_le_bytes 4 guard_lo))
                                        (Z_to_bv 64 0x79c34) (word_to_le_bytes 4 guard_hi))
                                (Z_to_bv 64 0x79c31) [Z_to_bv 8 0]) (Z_to_bv 64 0x79c30) 8
    = Some canary_bytes.
  Proof.
    intros segs DD. rewrite guard_lo_store, guard_hi_store.
    unfold canary_bytes, guard_lo_bytes, guard_hi_bytes, rnd_bytes, at_random_bytes.
    cbn [firstn skipn app].
    set (b0 := bv_extract 0 8 _). set (b1 := bv_extract 8 8 _). set (b2 := bv_extract 16 8 _). set (b3 := bv_extract 24 8 _).
    set (b4 := bv_extract 32 8 _). set (b5 := bv_extract 40 8 _). set (b6 := bv_extract 48 8 _). set (b7 := bv_extract 56 8 _).
    clearbody b0 b1 b2 b3 b4 b5 b6 b7. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition D_fd (D : word -> option byte) : word -> option byte :=
    wbytes D (Z_to_bv 64 0x49820) [Z_to_bv 8 1].

  (* [comment removed for export] *)
  Definition D_main (tid : word) : word -> option byte := D_fd (D_ssp (D_tls tid D_libc)).

End Defs.
