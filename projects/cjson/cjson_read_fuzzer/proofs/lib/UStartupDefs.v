(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the Defs section takes the whole ProcInput and the mmap base, argv pointers are computed from the stack top and exec file name, and musl's auxv frame J_aux gains AT_SYSINFO_EHDR, AT_CLKTCK, AT_BASE, AT_FLAGS, AT_ENTRY, AT_GID/AT_EGID, AT_EXECFN and the two CONFIG_RSEQ slots, with the new lemma J_aux_norseq. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.cjson.cjson_read_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.StartupTac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.ArgvEnv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.RefLayout.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.StartupSsp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
#[local] Existing Instance fx0.
Unset Lia Cache.

Abbreviation RPH := Ubsan.M.phdrs.

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
  (** The launch: the entry stack pointer, the process input (argv, envp,
      credentials, AT_HWCAP, the exec file name and the kernel build are its
      fields), the mmap base and the entry draw ([ed_random] = the AT_RANDOM
      bytes, [ed_top] = the stack VMA's end). *)
  Variable sp0 : word.
  Variable inp : ProcInput.
  Variable mbase : word.
  Variable rdraw : EntryDraw.          (* [comment removed for export] *)
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation ev := (in_envp inp) (only parsing).
  Local Notation uid := (in_uid inp) (only parsing).
  Local Notation gid := (in_gid inp) (only parsing).
  Local Notation hw := (in_hwcap inp) (only parsing).
  Local Notation rseq := (kb_rseq (in_kernel inp)) (only parsing).

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
  (** AT_EXECFN's value, and AT_SYSINFO_EHDR's (the vDSO text base the launch
      computes from the mmap base). *)
  Definition execfn_w : word := at_execfn_ptr (ed_top rdraw) (in_execfn inp).
  Definition ehdr_w : word := la_sysinfo_ehdr (launch_auxv inp sp0 mbase).

  (* [comment removed for export] *)
  Definition D_libc : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (fun _ => None)
      (Z_to_bv 64 0x34900) (word_to_le_bytes 8 envp_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0x54c60) (word_to_le_bytes 8 auxv_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0x54cc0) (word_to_le_bytes 8 hw))              (* [comment removed for export] *)
      (Z_to_bv 64 0x54c88) (word_to_le_bytes 8 (Z_to_bv 64 4096))) (* [comment removed for export] *)
      (Z_to_bv 64 0x54c50) (word_to_le_bytes 8 pn_w))            (* [comment removed for export] *)
      (Z_to_bv 64 0x54c48) (word_to_le_bytes 8 progname_w).      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition J_lsm (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x15bf0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x1316c)).

  (** musl's [__init_libc] frame after its auxv loop: [aux[AUX_CNT]] zeroed at
      [sp0 - 368], then [aux[t] = v] for each pair of [StackLayout.auxv_entries]
      with [t < 38], in the auxv's order.  The pairs with [t >= 38] (the cache
      words, AT_MINSIGSTKSZ) are skipped by the loop.  Under CONFIG_RSEQ the
      auxv carries two more pairs, AT_RSEQ_FEATURE_SIZE (27) and
      AT_RSEQ_ALIGN (28), stored last. *)
  Definition J_aux27 (Jf : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
      (wbytes Jf aux_base (zeros 304))
      (Z_to_bv 64 (bv_unsigned sp0 - 104)) (word_to_le_bytes 8 ehdr_w))              (* AT_SYSINFO_EHDR *)
      (Z_to_bv 64 (bv_unsigned sp0 - 240)) (word_to_le_bytes 8 hw))                  (* AT_HWCAP *)
      (Z_to_bv 64 (bv_unsigned sp0 - 320)) (word_to_le_bytes 8 (Z_to_bv 64 4096)))    (* AT_PAGESZ *)
      (Z_to_bv 64 (bv_unsigned sp0 - 232)) (word_to_le_bytes 8 (Z_to_bv 64 100)))     (* AT_CLKTCK *)
      (Z_to_bv 64 (bv_unsigned sp0 - 344)) (word_to_le_bytes 8 (Z_to_bv 64 0x10040)))  (* AT_PHDR *)
      (Z_to_bv 64 (bv_unsigned sp0 - 336)) (word_to_le_bytes 8 (Z_to_bv 64 56)))      (* AT_PHENT *)
      (Z_to_bv 64 (bv_unsigned sp0 - 328)) (word_to_le_bytes 8 (Z_to_bv 64 10)))      (* AT_PHNUM *)
      (Z_to_bv 64 (bv_unsigned sp0 - 312)) (word_to_le_bytes 8 (Z_to_bv 64 0)))       (* AT_BASE *)
      (Z_to_bv 64 (bv_unsigned sp0 - 304)) (word_to_le_bytes 8 (Z_to_bv 64 0)))       (* AT_FLAGS *)
      (Z_to_bv 64 (bv_unsigned sp0 - 296)) (word_to_le_bytes 8 (Z_to_bv 64 0x13020)))  (* AT_ENTRY *)
      (Z_to_bv 64 (bv_unsigned sp0 - 280)) (word_to_le_bytes 8 uid))                 (* AT_UID *)
      (Z_to_bv 64 (bv_unsigned sp0 - 272)) (word_to_le_bytes 8 uid))                 (* AT_EUID *)
      (Z_to_bv 64 (bv_unsigned sp0 - 264)) (word_to_le_bytes 8 gid))                 (* AT_GID *)
      (Z_to_bv 64 (bv_unsigned sp0 - 256)) (word_to_le_bytes 8 gid))                 (* AT_EGID *)
      (Z_to_bv 64 (bv_unsigned sp0 - 184)) (word_to_le_bytes 8 (Z_to_bv 64 0)))       (* AT_SECURE *)
      (Z_to_bv 64 (bv_unsigned sp0 - 168)) (word_to_le_bytes 8 rnd_w))               (* AT_RANDOM *)
      (Z_to_bv 64 (bv_unsigned sp0 - 120)) (word_to_le_bytes 8 execfn_w).            (* AT_EXECFN *)

  (** The two CONFIG_RSEQ slots are written with the value the loop leaves
      there in either case: 28 and 32 when the auxv carries the pairs, and the
      memset's 0 when it does not ([J_aux_norseq]).  Keeping the stores
      unconditional keeps every other slot readable by peeling. *)
  Definition J_aux (Jf : word -> option byte) : word -> option byte :=
    wbytes (wbytes (J_aux27 Jf)
      (Z_to_bv 64 (bv_unsigned sp0 - 152))
      (word_to_le_bytes 8 (Z_to_bv 64 (if rseq then 28 else 0))))   (* AT_RSEQ_FEATURE_SIZE *)
      (Z_to_bv 64 (bv_unsigned sp0 - 144))
      (word_to_le_bytes 8 (Z_to_bv 64 (if rseq then 32 else 0))).   (* AT_RSEQ_ALIGN *)

  (* [comment removed for export] *)
  Definition D_tlsA (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x549f8) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x54a08) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x54a00) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x54c70) (word_to_le_bytes 8 (Z_to_bv 64 0xe0)))     (* [comment removed for export] *)
      (Z_to_bv 64 0x54c78) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x349e0) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x349c8) (word_to_le_bytes 8 (Z_to_bv 64 0x349e0)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x34908) (word_to_le_bytes 8 (Z_to_bv 64 0x34908)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x54c58) [Z_to_bv 8 1])                              (* [comment removed for export] *)
      (Z_to_bv 64 0x34930) (word_to_le_bytes 4 (Z_to_bv 64 2)).        (* [comment removed for export] *)

  Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x34928) (word_to_le_bytes 4 tid))                   (* [comment removed for export] *)
      (Z_to_bv 64 0x349a0) (word_to_le_bytes 8 (Z_to_bv 64 0x54c90)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x34980) (word_to_le_bytes 8 (Z_to_bv 64 0x34980)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x34910) (word_to_le_bytes 8 (Z_to_bv 64 0x34908)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x34918) (word_to_le_bytes 8 (Z_to_bv 64 0x34908)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x34920) (word_to_le_bytes 8 (Z_to_bv 64 0)).        (* [comment removed for export] *)

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
      (Z_to_bv 64 0x54c38) (word_to_le_bytes 4 (v_lw (rnd_lo (ed_random rdraw)))))  (* [comment removed for export] *)
      (Z_to_bv 64 0x54c3c) (word_to_le_bytes 4 (v_lw (rnd_hi (ed_random rdraw)))))  (* [comment removed for export] *)
      (Z_to_bv 64 0x54c39) [Z_to_bv 8 0])                                (* [comment removed for export] *)
      (Z_to_bv 64 0x349c0) (word_to_le_bytes 8 (canary_w (ed_random rdraw))).                 (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_fd (D : word -> option byte) : word -> option byte :=
    wbytes D (Z_to_bv 64 0x24870) [Z_to_bv 8 1].

  (* [comment removed for export] *)
  Definition D_main (tid : word) : word -> option byte := D_fd (D_ssp (D_tls tid D_libc)).

End Defs.


Lemma nth_le8_zero : forall i, nth i (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof.
  intros i. destruct (Nat.lt_ge_cases i 8) as [H|H].
  - do 8 (destruct i as [|i]; [reflexivity|]). lia.
  - apply nth_overflow. rewrite length_N_to_le_bytes. exact H.
Qed.

(** Without CONFIG_RSEQ the loop never writes [aux[27]] or [aux[28]]: the
    memset's zeros stay, which is what [J_aux]'s two stores write. *)
Lemma J_aux_norseq : forall sp0 inp mbase rdraw Jf,
  (0x7fff80000000 <= bv_unsigned sp0)%Z -> (bv_unsigned sp0 <= 0x800000000000)%Z ->
  kb_rseq (in_kernel inp) = false ->
  J_aux sp0 inp mbase rdraw Jf = J_aux27 sp0 inp mbase rdraw Jf.
Proof.
  intros sp0 inp mbase rdraw Jf Hlo Hhi Hrs. unfold J_aux. rewrite Hrs. cbv iota.
  apply Stdlib.Logic.FunctionalExtensionality.functional_extensionality. intros x.
  pose proof (u64_range x) as Hx.
  destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned sp0 - 152)) as [H1|H1];
    [| destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned sp0 - 136)) as [H2|H2]].
  1, 3: rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes; rewrite ?u_Z2bv by lia; lia);
        reflexivity.
  destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned sp0 - 144)) as [H3|H3].
  - rewrite (wbytes_outside _ _ (Z_to_bv 64 (bv_unsigned sp0 - 144)))
      by (rewrite ?length_N_to_le_bytes; rewrite ?u_Z2bv by lia; lia).
    rewrite wbytes_inside by (rewrite ?length_N_to_le_bytes; rewrite ?u_Z2bv by lia; lia).
    unfold J_aux27, aux_base.
    rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes; rewrite ?u_Z2bv by lia; lia).
    rewrite wbytes_inside
      by (rewrite ?OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.ZStores.length_zeros;
          rewrite ?u_Z2bv by lia; lia).
    rewrite nth_le8_zero, OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.ZStores.nth_zeros.
    reflexivity.
  - rewrite wbytes_inside by (rewrite ?length_N_to_le_bytes; rewrite ?u_Z2bv by lia; lia).
    unfold J_aux27, aux_base.
    rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes; rewrite ?u_Z2bv by lia; lia).
    rewrite wbytes_inside
      by (rewrite ?OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.ZStores.length_zeros;
          rewrite ?u_Z2bv by lia; lia).
    rewrite nth_le8_zero, OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.ZStores.nth_zeros.
    reflexivity.
Qed.
