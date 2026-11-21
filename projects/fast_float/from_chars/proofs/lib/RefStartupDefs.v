(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput; the CONFIG_RSEQ flag of the start-up layer; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StartupTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.StartupTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.ArgvEnv OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.
Import ListNotations.
Open Scope bv_scope.
Local Instance clf_fx : PropExec.FPState := PropExec.fx0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation RPH := Plain.M.phdrs.

(* [comment removed for export] *)
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

Section Defs.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 : word.
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation ev := (in_envp inp) (only parsing).
  Local Notation uid := (in_uid inp) (only parsing).
  Local Notation hw := (in_hwcap inp) (only parsing).
  Variable rdraw : EntryDraw.

  (* [comment removed for export] *)
  Definition aux_base : word := Z_to_bv 64 (bv_unsigned sp0 - 368).
  (* [comment removed for export] *)
  Definition argv_w : word := Z_to_bv 64 (bv_unsigned sp0 + 8).
  Definition envp_w : word := Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)).
  Definition auxv_w : word :=
    Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev)).
  Definition argc_w : word := argcN inp.
  (* [comment removed for export] *)
  Definition pn_w : word := cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0.
  Definition progname_w : word :=
    Z_to_bv 64 (bv_unsigned pn_w + Z.of_nat (progname_off (nth 0 av []))).
  (* [comment removed for export] *)
  Definition rnd_w : word := at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp).

  (* [comment removed for export] *)
  Definition D_libc : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (fun _ => None)
      (Z_to_bv 64 0x75b00) (word_to_le_bytes 8 envp_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0x95e68) (word_to_le_bytes 8 auxv_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0x95ec8) (word_to_le_bytes 8 hw))              (* [comment removed for export] *)
      (Z_to_bv 64 0x95e90) (word_to_le_bytes 8 (Z_to_bv 64 4096))) (* [comment removed for export] *)
      (Z_to_bv 64 0x95e58) (word_to_le_bytes 8 pn_w))            (* [comment removed for export] *)
      (Z_to_bv 64 0x95e50) (word_to_le_bytes 8 progname_w).      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition J_lsm (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x50834)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x22638)).

  (* AT_RSEQ_FEATURE_SIZE / AT_RSEQ_ALIGN (keys 27, 28) are in the auxv
     only with CONFIG_RSEQ; without it musl's aux[27], aux[28] keep the
     memset's zeros. *)
  Definition rs28 : word := if kb_rseq (in_kernel inp) then Z_to_bv 64 28 else Z_to_bv 64 0.
  Definition rs32 : word := if kb_rseq (in_kernel inp) then Z_to_bv 64 32 else Z_to_bv 64 0.

  (* musl's aux[] table after the auxv walk: aux[k] at aux_base + 8k for
     every key k < AUX_CNT = 38, in the order create_elf_tables writes
     them (StackLayout.auxv_entries); keys >= 38 (the cache words and
     AT_MINSIGSTKSZ) are skipped. *)
  Definition J_aux0 (Jf : word -> option byte) : word -> option byte :=
    (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
      (wbytes Jf aux_base (zeros 304))
      (Z_to_bv 64 (bv_unsigned sp0 - 104))                                       (* AT_SYSINFO_EHDR *)
        (word_to_le_bytes 8 (la_sysinfo_ehdr (launch_auxv inp sp0 mbase))))
      (Z_to_bv 64 (bv_unsigned sp0 - 240)) (word_to_le_bytes 8 hw))              (* AT_HWCAP *)
      (Z_to_bv 64 (bv_unsigned sp0 - 320)) (word_to_le_bytes 8 (Z_to_bv 64 4096))) (* AT_PAGESZ *)
      (Z_to_bv 64 (bv_unsigned sp0 - 232)) (word_to_le_bytes 8 (Z_to_bv 64 100))) (* AT_CLKTCK *)
      (Z_to_bv 64 (bv_unsigned sp0 - 344)) (word_to_le_bytes 8 (Z_to_bv 64 0x10040))) (* AT_PHDR *)
      (Z_to_bv 64 (bv_unsigned sp0 - 336)) (word_to_le_bytes 8 (Z_to_bv 64 56)))   (* AT_PHENT *)
      (Z_to_bv 64 (bv_unsigned sp0 - 328)) (word_to_le_bytes 8 (Z_to_bv 64 10)))   (* AT_PHNUM *)
      (Z_to_bv 64 (bv_unsigned sp0 - 312)) (word_to_le_bytes 8 (Z_to_bv 64 0)))    (* AT_BASE *)
      (Z_to_bv 64 (bv_unsigned sp0 - 304)) (word_to_le_bytes 8 (Z_to_bv 64 0)))    (* AT_FLAGS *)
      (Z_to_bv 64 (bv_unsigned sp0 - 296)) (word_to_le_bytes 8 entry))             (* AT_ENTRY *)
      (Z_to_bv 64 (bv_unsigned sp0 - 280)) (word_to_le_bytes 8 uid))               (* AT_UID *)
      (Z_to_bv 64 (bv_unsigned sp0 - 272)) (word_to_le_bytes 8 uid))               (* AT_EUID *)
      (Z_to_bv 64 (bv_unsigned sp0 - 264)) (word_to_le_bytes 8 (in_gid inp)))      (* AT_GID *)
      (Z_to_bv 64 (bv_unsigned sp0 - 256)) (word_to_le_bytes 8 (in_gid inp)))      (* AT_EGID *)
      (Z_to_bv 64 (bv_unsigned sp0 - 184)) (word_to_le_bytes 8 (Z_to_bv 64 0)))    (* AT_SECURE *)
      (Z_to_bv 64 (bv_unsigned sp0 - 168)) (word_to_le_bytes 8 rnd_w))             (* AT_RANDOM *)
      (Z_to_bv 64 (bv_unsigned sp0 - 120))                                         (* AT_EXECFN *)
        (word_to_le_bytes 8 (at_execfn_ptr (ed_top rdraw) (in_execfn inp)))).

  Definition J_aux (Jf : word -> option byte) : word -> option byte :=
    wbytes (wbytes (J_aux0 Jf)
      (Z_to_bv 64 (bv_unsigned sp0 - 152)) (word_to_le_bytes 8 rs28))            (* AT_RSEQ_FEATURE_SIZE *)
      (Z_to_bv 64 (bv_unsigned sp0 - 144)) (word_to_le_bytes 8 rs32).            (* AT_RSEQ_ALIGN *)

  Lemma J_aux_rseq : forall Jf, kb_rseq (in_kernel inp) = true ->
    J_aux Jf = wbytes (wbytes (J_aux0 Jf)
                 (Z_to_bv 64 (bv_unsigned sp0 - 152)) (word_to_le_bytes 8 (Z_to_bv 64 28)))
                 (Z_to_bv 64 (bv_unsigned sp0 - 144)) (word_to_le_bytes 8 (Z_to_bv 64 32)).
  Proof. intros Jf E. unfold J_aux, rs28, rs32. rewrite E. reflexivity. Qed.

  (* Without CONFIG_RSEQ the walk stores nothing at aux[27], aux[28]: the
     two words there are the memset's zeros, so storing zeros over them
     is the identity. *)
  Lemma J_aux_norseq : forall Jf, kb_rseq (in_kernel inp) = false ->
    (0x7fff80000000 <= bv_unsigned sp0)%Z -> (bv_unsigned sp0 <= 0x800000000000)%Z ->
    J_aux Jf = J_aux0 Jf.
  Proof.
    intros Jf E Hlo Hhi. unfold J_aux, rs28, rs32. rewrite E. cbv iota.
    assert (HZ : forall z, (bv_unsigned sp0 - 152 <= z < bv_unsigned sp0 - 136)%Z ->
                   J_aux0 Jf (Z_to_bv 64 z) = Some (Z_to_bv 8 0)).
    { intros z Hz. unfold J_aux0, aux_base.
      repeat (rewrite wbytes_outside by region_side).
      rewrite wbytes_inside by region_side. apply f_equal. apply nth_zeros. }
    assert (HB : forall (o : Z) j, (0 <= o <= 8)%Z -> (j < 8)%nat ->
                   J_aux0 Jf (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp0 - 152 + o))
                                          + Z.of_nat j))
                   = Some (nth j (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 8 0))).
    { intros o j Ho Hj. rewrite u_Z2bv by lia. rewrite HZ by lia.
      do 8 (destruct j as [|j]; [vm_compute; reflexivity|]). lia. }
    rewrite (wbytes_same_m (word_to_le_bytes 8 (Z_to_bv 64 0)) (J_aux0 Jf)
               (Z_to_bv 64 (bv_unsigned sp0 - 152))).
    - apply wbytes_same_m.
      + rewrite length_N_to_le_bytes. rewrite u_Z2bv by lia. lia.
      + intros j Hj. rewrite length_N_to_le_bytes in Hj.
        replace (bv_unsigned sp0 - 144)%Z with (bv_unsigned sp0 - 152 + 8)%Z by lia.
        apply HB; lia.
    - rewrite length_N_to_le_bytes. rewrite u_Z2bv by lia. lia.
    - intros j Hj. rewrite length_N_to_le_bytes in Hj.
      replace (bv_unsigned sp0 - 152)%Z with (bv_unsigned sp0 - 152 + 0)%Z by lia.
      apply HB; lia.
  Qed.

  (* [comment removed for export] *)
  Definition D_tlsA (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x95bf8) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x95c08) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x95c00) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x95e78) (word_to_le_bytes 8 (Z_to_bv 64 0xe0)))     (* [comment removed for export] *)
      (Z_to_bv 64 0x95e80) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x75be0) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x75bc8) (word_to_le_bytes 8 (Z_to_bv 64 0x75be0)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x75b08) (word_to_le_bytes 8 (Z_to_bv 64 0x75b08)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x95e60) [Z_to_bv 8 1])                              (* [comment removed for export] *)
      (Z_to_bv 64 0x75b30) (word_to_le_bytes 4 (Z_to_bv 64 2)).        (* [comment removed for export] *)

  Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x75b28) (word_to_le_bytes 4 tid))                   (* [comment removed for export] *)
      (Z_to_bv 64 0x75ba0) (word_to_le_bytes 8 (Z_to_bv 64 0x95e98)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x75b80) (word_to_le_bytes 8 (Z_to_bv 64 0x75b80)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x75b10) (word_to_le_bytes 8 (Z_to_bv 64 0x75b08)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x75b18) (word_to_le_bytes 8 (Z_to_bv 64 0x75b08)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x75b20) (word_to_le_bytes 8 (Z_to_bv 64 0)).        (* [comment removed for export] *)

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
  Definition rnd_lo : word := Z_to_bv 64 (bytes_le_to_Z (firstn 4 (skipn 0 (at_random_bytes (ed_random rdraw))))).
  Definition rnd_hi : word := Z_to_bv 64 (bytes_le_to_Z (firstn 4 (skipn 4 (at_random_bytes (ed_random rdraw))))).
  Definition canary_bytes : list byte :=
    let w0 := word_to_le_bytes 4 (v_lw rnd_lo) in
    [nth 0 w0 (Z_to_bv 8 0); Z_to_bv 8 0; nth 2 w0 (Z_to_bv 8 0); nth 3 w0 (Z_to_bv 8 0)] ++ word_to_le_bytes 4 (v_lw rnd_hi).
  Definition canary : word := Z_to_bv 64 (bytes_le_to_Z canary_bytes).
  Definition D_ssp (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x95e40) (word_to_le_bytes 4 (v_lw rnd_lo)))      (* [comment removed for export] *)
      (Z_to_bv 64 0x95e44) (word_to_le_bytes 4 (v_lw rnd_hi)))      (* [comment removed for export] *)
      (Z_to_bv 64 0x95e41) [Z_to_bv 8 0])                            (* [comment removed for export] *)
      (Z_to_bv 64 0x75bc0) (word_to_le_bytes 8 canary).              (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Type"] Lemma rd_guard : forall segs (D : word -> option byte),
    rdn segs (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x95e40) (word_to_le_bytes 4 (v_lw rnd_lo)))
      (Z_to_bv 64 0x95e44) (word_to_le_bytes 4 (v_lw rnd_hi)))
      (Z_to_bv 64 0x95e41) [Z_to_bv 8 0]) (Z_to_bv 64 0x95e40) 8%nat = Some canary_bytes.
  Proof. LiaFast.lf_pins LiaFast.u0. intros. reflexivity. Qed.

  #[using="Type"] Lemma canary_val : bytes_le_to_Z canary_bytes = bv_unsigned canary.
  Proof. LiaFast.lf_pins LiaFast.u0.
    unfold canary. rewrite u_Z2bv; [reflexivity | apply bytes_le_to_Z_nonneg |].
    pose proof (bytes_le_to_Z_bound canary_bytes) as H.
    assert (HL : length canary_bytes = 8%nat) by (unfold canary_bytes; rewrite length_app, length_N_to_le_bytes; reflexivity).
    rewrite HL in H. exact H.
  Qed.

  #[using="Type"] Lemma rnd_lo_val : bytes_le_to_Z (firstn 4 (skipn 0 (at_random_bytes (ed_random rdraw)))) = bv_unsigned rnd_lo.
  Proof. LiaFast.lf_pins LiaFast.u0.
    unfold rnd_lo. rewrite u_Z2bv; [reflexivity | apply bytes_le_to_Z_nonneg |].
    pose proof (bytes_le_to_Z_bound (firstn 4 (skipn 0 (at_random_bytes (ed_random rdraw))))) as H.
    assert (HL : length (firstn 4 (skipn 0 (at_random_bytes (ed_random rdraw)))) = 4%nat) by reflexivity.
    rewrite HL in H. change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z in H. lia.
  Qed.
  #[using="Type"] Lemma rnd_hi_val : bytes_le_to_Z (firstn 4 (skipn 4 (at_random_bytes (ed_random rdraw)))) = bv_unsigned rnd_hi.
  Proof. LiaFast.lf_pins LiaFast.u0.
    unfold rnd_hi. rewrite u_Z2bv; [reflexivity | apply bytes_le_to_Z_nonneg |].
    pose proof (bytes_le_to_Z_bound (firstn 4 (skipn 4 (at_random_bytes (ed_random rdraw))))) as H.
    assert (HL : length (firstn 4 (skipn 4 (at_random_bytes (ed_random rdraw)))) = 4%nat) by reflexivity.
    rewrite HL in H. change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z in H. lia.
  Qed.

  (* [comment removed for export] *)
  Definition D_fd (D : word -> option byte) : word -> option byte :=
    wbytes D (Z_to_bv 64 0x65010) [Z_to_bv 8 1].

  (* [comment removed for export] *)
  Definition D_pre_ios (tid : word) : word -> option byte := D_tls tid D_libc.

  (* [comment removed for export] *)
  Definition D_main (tid : word) : word -> option byte := D_fd (D_ssp (D_pre_ios tid)).

End Defs.
