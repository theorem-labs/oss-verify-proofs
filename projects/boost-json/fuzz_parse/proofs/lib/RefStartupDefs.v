(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef); ported to LPS 727298f3: statements written out as text, lemmas added for the revision, the launch input as a ProcInput. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* LPS 75d69e00: the definitions are stated explicitly (they were zQ-encoded).  The section is
   over the ProcInput [inp] (argcN / envp_ptr / wrap_mem now take it, see ArgvEnv.v); the
   binary-specific constants are the ones Rocq decoded from the previous zQ text, unchanged.
   New: the auxv layer gains the 75d69e00 kernel's entries (AT_SYSINFO_EHDR, AT_CLKTCK, AT_BASE,
   AT_FLAGS, AT_ENTRY, AT_GID/EGID, AT_EXECFN) and the CONFIG_RSEQ pair [J_rseq]; the AT_RANDOM
   pointer reads the rseq flag. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import StartupTac ArgvEnv RefLayout.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation RPH := Plain.M.phdrs.

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Fixpoint after_last_slash (s : list byte) (i acc : nat) : nat :=
  match s with
  | [] => acc
  | b :: s' => after_last_slash s' (S i) (if bv_eqb b (Z_to_bv 8 47) then S i else acc)
  end.
Definition progname_off : list byte -> nat := fun s => after_last_slash s 0 0.

End FPX1.

Section Defs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 : word.
  Variable rnd : EntryDraw.    (* [comment removed for export] *)
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation ev := (in_envp inp) (only parsing).
  Local Notation uid := (in_uid inp) (only parsing).
  Local Notation hw := (in_hwcap inp) (only parsing).

  (* [comment removed for export] *)
  Definition rb : list byte := at_random_bytes (ed_random rnd).
  Definition rbn : nat -> byte := fun i => nth i rb (Z_to_bv 8 0).

  (* [comment removed for export] *)
  Definition aux_base : word := Z_to_bv 64 (bv_unsigned sp0 - 368).
  (* [comment removed for export] *)
  Definition argv_w : word := Z_to_bv 64 (bv_unsigned sp0 + 8).
  Definition envp_w : word := Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)).
  Definition auxv_w : word :=
    Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev)).
  Definition argc_w : word := argcN inp.
  (* [comment removed for export] *)
  Definition pn_w : word := cat_argv_ptr (ed_top rnd) av ev (in_execfn inp) 0.
  Definition progname_w : word :=
    Z_to_bv 64 (bv_unsigned pn_w + Z.of_nat (progname_off (nth 0 av []))).
  (* [comment removed for export] *)
  Definition rnd_w : word := at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev.

  (* [comment removed for export] *)
  Definition D_libc : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (fun _ : word => None)
      (Z_to_bv 64 1095144) (word_to_le_bytes 8 envp_w))            (* 0x10b5e8 *)
      (Z_to_bv 64 1227088) (word_to_le_bytes 8 auxv_w))            (* 0x12b950 *)
      (Z_to_bv 64 1227184) (word_to_le_bytes 8 hw))                (* 0x12b9b0 *)
      (Z_to_bv 64 1227128) (word_to_le_bytes 8 (Z_to_bv 64 4096))) (* 0x12b978 *)
      (Z_to_bv 64 1227072) (word_to_le_bytes 8 pn_w))              (* 0x12b940 *)
      (Z_to_bv 64 1227064) (word_to_le_bytes 8 progname_w).        (* 0x12b938 *)

  (* [comment removed for export] *)
  Definition J_lsm : (word -> option byte) -> word -> option byte := fun J =>
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 893020)))  (* 0xda05c *)
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 291792)).  (* 0x473d0 *)

  (* LPS 08b1429: with CONFIG_RSEQ the kernel adds AT_RSEQ_FEATURE_SIZE (27) = 28 and
     AT_RSEQ_ALIGN (28) = 32, which __init_libc copies into aux[27], aux[28]. *)
  Definition J_rseq (J : word -> option byte) : word -> option byte :=
    if kb_rseq (in_kernel inp)
    then wbytes (wbytes J
           (Z_to_bv 64 (bv_unsigned sp0 - 152)) (word_to_le_bytes 8 (Z_to_bv 64 28)))
           (Z_to_bv 64 (bv_unsigned sp0 - 144)) (word_to_le_bytes 8 (Z_to_bv 64 32))
    else J.

  (* [comment removed for export] *)
  Definition J_aux (Jf : word -> option byte) : word -> option byte :=
    J_rseq
    (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
      (wbytes Jf aux_base (zeros 304))
      (Z_to_bv 64 (bv_unsigned sp0 - 104))                                        (* aux[33] AT_SYSINFO_EHDR *)
        (word_to_le_bytes 8 (la_sysinfo_ehdr (launch_auxv inp sp0 mbase))))
      (Z_to_bv 64 (bv_unsigned sp0 - 240)) (word_to_le_bytes 8 hw))              (* aux[16] AT_HWCAP *)
      (Z_to_bv 64 (bv_unsigned sp0 - 320)) (word_to_le_bytes 8 (Z_to_bv 64 4096))) (* aux[6] AT_PAGESZ *)
      (Z_to_bv 64 (bv_unsigned sp0 - 232)) (word_to_le_bytes 8 (Z_to_bv 64 100))) (* aux[17] AT_CLKTCK *)
      (Z_to_bv 64 (bv_unsigned sp0 - 344)) (word_to_le_bytes 8 (Z_to_bv 64 65600))) (* aux[3] AT_PHDR 0x10040 *)
      (Z_to_bv 64 (bv_unsigned sp0 - 336)) (word_to_le_bytes 8 (Z_to_bv 64 56)))   (* aux[4] AT_PHENT *)
      (Z_to_bv 64 (bv_unsigned sp0 - 328)) (word_to_le_bytes 8 (Z_to_bv 64 10)))   (* aux[5] AT_PHNUM *)
      (Z_to_bv 64 (bv_unsigned sp0 - 312)) (word_to_le_bytes 8 (Z_to_bv 64 0)))    (* aux[7] AT_BASE *)
      (Z_to_bv 64 (bv_unsigned sp0 - 304)) (word_to_le_bytes 8 (Z_to_bv 64 0)))    (* aux[8] AT_FLAGS *)
      (Z_to_bv 64 (bv_unsigned sp0 - 296)) (word_to_le_bytes 8 entry))            (* aux[9] AT_ENTRY *)
      (Z_to_bv 64 (bv_unsigned sp0 - 280)) (word_to_le_bytes 8 uid))              (* aux[11] AT_UID *)
      (Z_to_bv 64 (bv_unsigned sp0 - 272)) (word_to_le_bytes 8 uid))              (* aux[12] AT_EUID *)
      (Z_to_bv 64 (bv_unsigned sp0 - 264)) (word_to_le_bytes 8 (in_gid inp)))     (* aux[13] AT_GID *)
      (Z_to_bv 64 (bv_unsigned sp0 - 256)) (word_to_le_bytes 8 (in_gid inp)))     (* aux[14] AT_EGID *)
      (Z_to_bv 64 (bv_unsigned sp0 - 184)) (word_to_le_bytes 8 (Z_to_bv 64 0)))    (* aux[23] AT_SECURE *)
      (Z_to_bv 64 (bv_unsigned sp0 - 168)) (word_to_le_bytes 8 rnd_w))            (* aux[25] AT_RANDOM *)
      (Z_to_bv 64 (bv_unsigned sp0 - 120))                                        (* aux[31] AT_EXECFN *)
        (word_to_le_bytes 8 (at_execfn_ptr (ed_top rnd) (in_execfn inp)))).

  (* [comment removed for export] *)
  Definition D_tlsA : (word -> option byte) -> word -> option byte := fun D =>
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 1226464) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 1226480) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 1226472) (word_to_le_bytes 8 (Z_to_bv 64 8)))
      (Z_to_bv 64 1227104) (word_to_le_bytes 8 (Z_to_bv 64 224)))
      (Z_to_bv 64 1227112) (word_to_le_bytes 8 (Z_to_bv 64 8)))
      (Z_to_bv 64 1095368) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 1095344) (word_to_le_bytes 8 (Z_to_bv 64 1095368)))
      (Z_to_bv 64 1095152) (word_to_le_bytes 8 (Z_to_bv 64 1095152)))
      (Z_to_bv 64 1227080) [Z_to_bv 8 1])
      (Z_to_bv 64 1095192) (word_to_le_bytes 4 (Z_to_bv 64 2)).

  Definition D_tlsB : word -> (word -> option byte) -> word -> option byte := fun tid D =>
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 1095184) (word_to_le_bytes 4 tid))
      (Z_to_bv 64 1095304) (word_to_le_bytes 8 (Z_to_bv 64 1227136)))
      (Z_to_bv 64 1095272) (word_to_le_bytes 8 (Z_to_bv 64 1095272)))
      (Z_to_bv 64 1095160) (word_to_le_bytes 8 (Z_to_bv 64 1095152)))
      (Z_to_bv 64 1095168) (word_to_le_bytes 8 (Z_to_bv 64 1095152)))
      (Z_to_bv 64 1095176) (word_to_le_bytes 8 (Z_to_bv 64 0)).

  Definition D_tls : word -> (word -> option byte) -> word -> option byte := fun tid D =>
    D_tlsB tid (D_tlsA D).

  (* [comment removed for export] *)
  Definition J_tls : (word -> option byte) -> word -> word -> word -> word -> word -> word -> word -> word -> option byte :=
    fun J ra s0 s1 s2 s3 s4 s5 =>
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 s0))
      (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1))
      (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 s2))
      (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 s3))
      (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 s4))
      (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 s5).

  (* [comment removed for export] *)
  Definition canary_bytes : list byte := [rbn 0; Z_to_bv 8 0; rbn 2; rbn 3; rbn 4; rbn 5; rbn 6; rbn 7].
  Definition canary_w : word := Z_to_bv 64 (bytes_le_to_Z canary_bytes).
  Definition D_ssp : (word -> option byte) -> word -> option byte := fun D =>
    wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 1226488) [rbn 0; rbn 1; rbn 2; rbn 3])
      (Z_to_bv 64 1226492) [rbn 4; rbn 5; rbn 6; rbn 7])
      (Z_to_bv 64 1226489) [Z_to_bv 8 0])
      (Z_to_bv 64 1095336) (word_to_le_bytes 8 canary_w).

  (* [comment removed for export] *)
  Definition D_fd : (word -> option byte) -> word -> option byte := fun D =>
    wbytes D (Z_to_bv 64 1022896) [Z_to_bv 8 1].

  (* [comment removed for export] *)
  Definition D_cxx : (word -> option byte) -> word -> option byte := fun D =>
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 1089256) (word_to_le_bytes 4 (Z_to_bv 64 1)))
      (Z_to_bv 64 1088608) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 1089256) (word_to_le_bytes 4 (Z_to_bv 64 2)))
      (Z_to_bv 64 1088612) (word_to_le_bytes 4 (Z_to_bv 64 1)))
      (Z_to_bv 64 1089256) (word_to_le_bytes 4 (Z_to_bv 64 3)))
      (Z_to_bv 64 1088616) (word_to_le_bytes 4 (Z_to_bv 64 2)).

  (* [comment removed for export] *)
  Definition D_main : word -> word -> option byte := fun tid => D_cxx (D_fd (D_ssp (D_tls tid D_libc))).

  Lemma firstn4_rb : firstn 4 rb = [rbn 0; rbn 1; rbn 2; rbn 3].
  Proof. reflexivity. Qed.
  Lemma firstn4_skipn4_rb : firstn 4 (skipn 4 rb) = [rbn 4; rbn 5; rbn 6; rbn 7].
  Proof. reflexivity. Qed.

  (* LPS 08b1429: [J_rseq] is an [if] on [kb_rseq]; the window fact, and a read away from its
     two slots [sp0 - 152, sp0 - 136), hold in both layouts. *)
  Lemma wfJ_J_rseq : forall J, wfJ sp0 J -> wfJ sp0 (J_rseq J).
  Proof.
    intros J HJ. unfold J_rseq.
    destruct (kb_rseq (in_kernel inp)); [repeat apply wfJ_wbytes |]; exact HJ.
  Qed.

  Lemma rdn_J_rseq_out : forall segs J (za : Z) n,
    (152 <= bv_unsigned sp0)%Z -> (0 <= za)%Z -> (za + Z.of_nat n < 2^64)%Z ->
    (za + Z.of_nat n <= bv_unsigned sp0 - 152 \/ bv_unsigned sp0 - 136 <= za)%Z ->
    rdn segs (J_rseq J) (Z_to_bv 64 za) n = rdn segs J (Z_to_bv 64 za) n.
  Proof.
    intros segs J za n H152 H0 Hn Hd. pose proof (u64_range sp0) as Hsp.
    unfold J_rseq. destruct (kb_rseq (in_kernel inp)); [|reflexivity].
    rewrite !rdn_wbytes_out_Z; [reflexivity | ..];
      rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
  Qed.

End Defs.
(* [comment removed for export] *)
