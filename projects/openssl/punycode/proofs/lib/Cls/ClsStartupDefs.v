(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up definitions take the whole ProcInput, the mmap base and the entry; the string pointers follow the stack top and the exec file name; J_aux also stores AT_ENTRY, AT_GID, AT_EGID, AT_CLKTCK, AT_EXECFN and AT_SYSINFO_EHDR, and the RSEQ pair under CONFIG_RSEQ); and launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.openssl.punycode.lib.Cls Require Import ClsAnchor.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import StartupTac ArgvEnv RefLayout.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

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
  Definition rnd16 : list byte := at_random_bytes (ed_random rdraw).

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
  Definition D_libc : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (fun _ => None)
      (Z_to_bv 64 0x14160) (word_to_le_bytes 8 envp_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0x14318) (word_to_le_bytes 8 auxv_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0x14378) (word_to_le_bytes 8 hw))                (* [comment removed for export] *)
      (Z_to_bv 64 0x14340) (word_to_le_bytes 8 (Z_to_bv 64 4096))) (* [comment removed for export] *)
      (Z_to_bv 64 0x14308) (word_to_le_bytes 8 pn_w))            (* [comment removed for export] *)
      (Z_to_bv 64 0x14300) (word_to_le_bytes 8 progname_w).      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition J_lsm (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x11760)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x1149c)).

  (* [comment removed for export] *)
  (* musl's __init_libc stores aux[type] for every auxv pair with type < AUX_CNT (38): the
     cache-geometry pairs (40..47) and AT_MINSIGSTKSZ (51) are skipped; the RSEQ pair (27, 28)
     is present only under CONFIG_RSEQ. aux[k] sits at aux_base + 8 k. *)
  Definition J_rseq (J : word -> option byte) : word -> option byte :=
    if rseq
    then wbytes (wbytes J
           (Z_to_bv 64 (bv_unsigned sp0 - 152)) (word_to_le_bytes 8 (Z_to_bv 64 28)))
           (Z_to_bv 64 (bv_unsigned sp0 - 144)) (word_to_le_bytes 8 (Z_to_bv 64 32))
    else J.
  Definition J_aux (Jf : word -> option byte) : word -> option byte :=
    J_rseq
    (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
      (wbytes Jf aux_base (zeros 304))
      (Z_to_bv 64 (bv_unsigned sp0 - 344)) (word_to_le_bytes 8 (Z_to_bv 64 0x10040)))  (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 336)) (word_to_le_bytes 8 (Z_to_bv 64 56)))       (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 328)) (word_to_le_bytes 8 (Z_to_bv 64 10)))       (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 240)) (word_to_le_bytes 8 hw))                   (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 320)) (word_to_le_bytes 8 (Z_to_bv 64 4096)))     (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 280)) (word_to_le_bytes 8 uid))        (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 272)) (word_to_le_bytes 8 uid))        (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 184)) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 168)) (word_to_le_bytes 8 rnd_w))                 (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 296)) (word_to_le_bytes 8 entry))                 (* aux[AT_ENTRY] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 264)) (word_to_le_bytes 8 gid))                   (* aux[AT_GID] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 256)) (word_to_le_bytes 8 gid))                   (* aux[AT_EGID] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 232)) (word_to_le_bytes 8 (Z_to_bv 64 100)))      (* aux[AT_CLKTCK] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 120)) (word_to_le_bytes 8 execfn_w))              (* aux[AT_EXECFN] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 104))
        (word_to_le_bytes 8 (la_sysinfo_ehdr (launch_auxv inp sp0 mbase)))).               (* aux[AT_SYSINFO_EHDR] *)

  (* [comment removed for export] *)
  Definition D_tlsA (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x14188) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x14198) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x14190) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x14328) (word_to_le_bytes 8 (Z_to_bv 64 0xe0)))     (* [comment removed for export] *)
      (Z_to_bv 64 0x14330) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x14278) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x14260) (word_to_le_bytes 8 (Z_to_bv 64 0x14278)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x141a0) (word_to_le_bytes 8 (Z_to_bv 64 0x141a0)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x14310) [Z_to_bv 8 1])                              (* [comment removed for export] *)
      (Z_to_bv 64 0x141c8) (word_to_le_bytes 4 (Z_to_bv 64 2)).        (* [comment removed for export] *)

  Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x141c0) (word_to_le_bytes 4 tid))                   (* [comment removed for export] *)
      (Z_to_bv 64 0x14238) (word_to_le_bytes 8 (Z_to_bv 64 0x14348)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x14218) (word_to_le_bytes 8 (Z_to_bv 64 0x14218)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x141a8) (word_to_le_bytes 8 (Z_to_bv 64 0x141a0)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x141b0) (word_to_le_bytes 8 (Z_to_bv 64 0x141a0)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x141b8) (word_to_le_bytes 8 (Z_to_bv 64 0)).        (* [comment removed for export] *)

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
  Definition D_fd (D : word -> option byte) : word -> option byte :=
    wbytes D (Z_to_bv 64 0x14110) [Z_to_bv 8 1].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition D_main (tid : word) : word -> option byte := D_fd (D_tls tid D_libc).

End Defs.
