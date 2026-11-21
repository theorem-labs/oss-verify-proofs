(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.World Require Import Tgt_checksum_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require Import StartupTac ArgvEnv RefLayout DrawDefs.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

Abbreviation RPH := Tgt_checksum_fuzzer_ubsan.M.phdrs.

Fixpoint after_last_slash (s : list byte) (i acc : nat) : nat :=
  match s with
  | [] => acc
  | b :: s' => after_last_slash s' (S i) (if bv_eqb b (Z_to_bv 8 47) then S i else acc)
  end.
Definition progname_off (s : list byte) : nat := after_last_slash s 0 0.



Section Defs.
  Variable sp0 : word.
  (* port727 (): the launch is one ProcInput, as in Common/ArgvEnv's Scaffold: argv / envp / uid /
     gid / AT_HWCAP / the exec name / the kernel build are its fields; the old names stay as notations. *)
  Variable inp : ProcInput.
  Variable mbase : word.        (* the launch's mmap base: AT_SYSINFO_EHDR is the vDSO above it *)
  Variable rdraw : EntryDraw.
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation ev := (in_envp inp) (only parsing).
  Local Notation uid := (in_uid inp) (only parsing).
  Local Notation hw := (in_hwcap inp) (only parsing).
  Local Notation gid := (in_gid inp) (only parsing).
  Local Notation rseq := (kb_rseq (in_kernel inp)) (only parsing).

  Definition aux_base : word := Z_to_bv 64 (bv_unsigned sp0 - 368).
  Definition argv_w : word := Z_to_bv 64 (bv_unsigned sp0 + 8).
  Definition envp_w : word := Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)).
  Definition auxv_w : word :=
    Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev)).
  Definition argc_w : word := len_word av.
  Definition pn_w : word := cat_argv_ptr (ed_top rdraw) av ev (in_execfn inp) 0.
  Definition progname_w : word :=
    Z_to_bv 64 (bv_unsigned pn_w + Z.of_nat (progname_off (nth 0 av []))).
  Definition rnd_w : word := at_random_ptr sp0 rseq av ev.
  (* port727: AT_EXECFN's value, the address of the exec name at the block's top. *)
  Definition xfn_w : word := at_execfn_ptr (ed_top rdraw) (in_execfn inp).

  Definition D_libc : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (fun _ => None)
      (Z_to_bv 64 0x2fcb0) (word_to_le_bytes 8 envp_w))
      (Z_to_bv 64 0x50018) (word_to_le_bytes 8 auxv_w))
      (Z_to_bv 64 0x50078) (word_to_le_bytes 8 hw))
      (Z_to_bv 64 0x50040) (word_to_le_bytes 8 (Z_to_bv 64 4096)))
      (Z_to_bv 64 0x50008) (word_to_le_bytes 8 pn_w))
      (Z_to_bv 64 0x50000) (word_to_le_bytes 8 progname_w).

  Definition J_lsm (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x15820)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x13d70)).

  (* port727 (): __init_libc's aux[AUX_CNT] after its auxv loop. 's vector is
     StackLayout.auxv_entries: 26 pairs (+ AT_RSEQ_FEATURE_SIZE / AT_RSEQ_ALIGN under CONFIG_RSEQ) + AT_NULL. The loop
     stores aux[key] := value for every key below AUX_CNT (38), in the vector's order; AT_SYSINFO_EHDR (33) is below
     38 too. The keys 40-47 (the cache words) and 51 (AT_MINSIGSTKSZ) are skipped. aux[k] is at sp0 - 368 + 8 k. *)
  Definition J_aux0 (Jf : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
      (wbytes Jf aux_base (zeros 304))
      (Z_to_bv 64 (bv_unsigned sp0 - 104)) (word_to_le_bytes 8 (la_sysinfo_ehdr (launch_auxv inp sp0 mbase))))  (* AT_SYSINFO_EHDR 33 *)
      (Z_to_bv 64 (bv_unsigned sp0 - 240)) (word_to_le_bytes 8 hw))                    (* AT_HWCAP 16 *)
      (Z_to_bv 64 (bv_unsigned sp0 - 320)) (word_to_le_bytes 8 (Z_to_bv 64 4096)))     (* AT_PAGESZ 6 *)
      (Z_to_bv 64 (bv_unsigned sp0 - 232)) (word_to_le_bytes 8 (Z_to_bv 64 100)))      (* AT_CLKTCK 17 *)
      (Z_to_bv 64 (bv_unsigned sp0 - 344)) (word_to_le_bytes 8 (Z_to_bv 64 0x10040)))  (* AT_PHDR 3 *)
      (Z_to_bv 64 (bv_unsigned sp0 - 336)) (word_to_le_bytes 8 (Z_to_bv 64 56)))       (* AT_PHENT 4 *)
      (Z_to_bv 64 (bv_unsigned sp0 - 328)) (word_to_le_bytes 8 (Z_to_bv 64 10)))       (* AT_PHNUM 5 *)
      (Z_to_bv 64 (bv_unsigned sp0 - 312)) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* AT_BASE 7 *)
      (Z_to_bv 64 (bv_unsigned sp0 - 304)) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* AT_FLAGS 8 *)
      (Z_to_bv 64 (bv_unsigned sp0 - 296)) (word_to_le_bytes 8 (Z_to_bv 64 0x13c24)))  (* AT_ENTRY 9 *)
      (Z_to_bv 64 (bv_unsigned sp0 - 280)) (word_to_le_bytes 8 uid))                   (* AT_UID 11 *)
      (Z_to_bv 64 (bv_unsigned sp0 - 272)) (word_to_le_bytes 8 uid))                   (* AT_EUID 12 *)
      (Z_to_bv 64 (bv_unsigned sp0 - 264)) (word_to_le_bytes 8 gid))                   (* AT_GID 13 *)
      (Z_to_bv 64 (bv_unsigned sp0 - 256)) (word_to_le_bytes 8 gid))                   (* AT_EGID 14 *)
      (Z_to_bv 64 (bv_unsigned sp0 - 184)) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* AT_SECURE 23 *)
      (Z_to_bv 64 (bv_unsigned sp0 - 168)) (word_to_le_bytes 8 rnd_w))                 (* AT_RANDOM 25 *)
      (Z_to_bv 64 (bv_unsigned sp0 - 120)) (word_to_le_bytes 8 xfn_w).                 (* AT_EXECFN 31 *)
  Definition J_aux (Jf : word -> option byte) : word -> option byte :=
    if rseq
    then wbytes (wbytes (J_aux0 Jf)
           (Z_to_bv 64 (bv_unsigned sp0 - 152)) (word_to_le_bytes 8 (Z_to_bv 64 28)))  (* AT_RSEQ_FEATURE_SIZE 27 *)
           (Z_to_bv 64 (bv_unsigned sp0 - 144)) (word_to_le_bytes 8 (Z_to_bv 64 32))   (* AT_RSEQ_ALIGN 28 *)
    else J_aux0 Jf.

  Definition D_tlsA (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x4fda8) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 0x4fdb8) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 0x4fdb0) (word_to_le_bytes 8 (Z_to_bv 64 8)))
      (Z_to_bv 64 0x50028) (word_to_le_bytes 8 (Z_to_bv 64 0xe0)))
      (Z_to_bv 64 0x50030) (word_to_le_bytes 8 (Z_to_bv 64 8)))
      (Z_to_bv 64 0x2fd90) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 0x2fd78) (word_to_le_bytes 8 (Z_to_bv 64 0x2fd90)))
      (Z_to_bv 64 0x2fcb8) (word_to_le_bytes 8 (Z_to_bv 64 0x2fcb8)))
      (Z_to_bv 64 0x50010) [Z_to_bv 8 1])
      (Z_to_bv 64 0x2fce0) (word_to_le_bytes 4 (Z_to_bv 64 2)).

  Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x2fcd8) (word_to_le_bytes 4 tid))
      (Z_to_bv 64 0x2fd50) (word_to_le_bytes 8 (Z_to_bv 64 0x50048)))
      (Z_to_bv 64 0x2fd30) (word_to_le_bytes 8 (Z_to_bv 64 0x2fd30)))
      (Z_to_bv 64 0x2fcc0) (word_to_le_bytes 8 (Z_to_bv 64 0x2fcb8)))
      (Z_to_bv 64 0x2fcc8) (word_to_le_bytes 8 (Z_to_bv 64 0x2fcb8)))
      (Z_to_bv 64 0x2fcd0) (word_to_le_bytes 8 (Z_to_bv 64 0)).

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
      (Z_to_bv 64 0x4fff0) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0))))
      (Z_to_bv 64 0x4fff4) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4))))
      (Z_to_bv 64 0x4fff1) [Z_to_bv 8 0])
      (Z_to_bv 64 0x2fd70) (word_to_le_bytes 8 (canary_w rdraw)).

  Definition D_fd (D : word -> option byte) : word -> option byte :=
    wbytes D (Z_to_bv 64 0x1fc30) [Z_to_bv 8 1].

  Definition D_main (tid : word) : word -> option byte := D_fd (D_ssp (D_tls tid D_libc)).

End Defs.
