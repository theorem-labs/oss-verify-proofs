(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the section takes the launch, a process input with VA size, mmap base, entry point, break and entry draw, and its launch hypotheses, in place of separate argv, envp, uid, hwcap and random values; argc, the stack-image bound and the argv-pointer lemmas restated over entry_stack_image and the new layout with the strings at the top; encoded statements decoded to plain text; using annotations dropped; comments restored). *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PropExec CatExec SeqExec StepTac.

Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_ArgvEnv () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.le"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.ABoot.PropExec.rdn"; "Scaffold.wmem"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.stack_to_mem"; "LinuxProcessSemantics.LinuxProcessSem.Run.entry_stack_image"; "Corelib.Init.Peano.lt"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.ABoot.CatExec.cat_argv_ptr"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Lists.ListDef.nth"; "Corelib.Init.Datatypes.nil"; "stdpp.bitvector.definitions.bv_add"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.nat_to_word"; "Corelib.Init.Nat.add"; "Corelib.Init.Nat.mul"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.word_le8"].


Section Scaffold.

  (** The loaded segments (source_segs / target_segs at each call site)
      and the launch: the process input, the entry's mmap base, stack
      pointer, program break and draw.  The argv/envp lists, the
      credentials and AT_HWCAP are fields of [inp], and the stack VMA's
      end is [ed_top] of the draw, so one [ProcInput] and one
      [EntryDraw] fix the whole initial stack image. *)
  Variable segs : list Segment.
  Variable v : VaSize.
  Variable inp : ProcInput.
  Variable mbase : word.

  (** The image's program-header record ([MemImageType.PhdrInfo]) and
      its entry point: the auxv carries both. *)
  Variable ph : PhdrInfo.
  Variable entry : word.

  Variable sp brk : word.
  Variable draw : EntryDraw.

  (** The ambient hypotheses every binary shares. *)
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va v (mkEntry sp brk mbase draw) inp.
  Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned sp)%Z.
  Hypothesis Hsp_hi : (bv_unsigned sp <= sp_window_hi)%Z.

  (* =============================================================== *)
  (* sp-window bounds (the [rsp_lo_num]/[rsp_hi_num] / [asp_*] twins) *)
  (* =============================================================== *)

  Lemma sp_lo_num : (0x7fff80000000 <= bv_unsigned sp)%Z.
  Proof. exact Hsp_lo. Qed.

  Lemma sp_hi_num : (bv_unsigned sp <= 0x800000000000)%Z.
  Proof. exact Hsp_hi. Qed.

  (* =============================================================== *)
  (* argc                                                            *)
  (* =============================================================== *)

  Definition argcN : word := len_word (in_argv inp).

  Lemma u_argcN : bv_unsigned argcN = Z.of_nat (length (in_argv inp)).
  Proof.
    pose proof (valid_argv_len (in_argv inp) Hva).
    unfold argcN, len_word. apply u_Z2bv; lia.
  Qed.

  (* =============================================================== *)
  (* No-overflow bound for the initial stack image                   *)
  (* =============================================================== *)

  Lemma bsb_nw :
    (bv_unsigned sp
     + Z.of_nat (length (entry_stack_image inp mbase ph entry sp draw)) < 2^64)%Z.
  Proof.
    pose proof (bsb_bound v inp mbase ph entry sp brk draw Hvl Hlau).
    pose proof sp_hi_num. lia.
  Qed.

  (* =============================================================== *)
  (* envp pointer (the value _start stores into musl's environ slot)  *)
  (* =============================================================== *)

  Definition envp_ptr : word :=
    Z_to_bv 64 (bv_unsigned sp + 8 + 8 * Z.of_nat (length (in_argv inp)) + 8).

  Lemma envp_ptr_eq :
    v_addi (v_add (Z_to_bv 64 (bv_unsigned sp + 8)) (v_slli argcN 3)) 8 = envp_ptr.
  Proof.
    pose proof sp_hi_num. pose proof sp_lo_num.
    pose proof (valid_argv_len (in_argv inp) Hva) as Hlen.
    apply bv_eq. unfold envp_ptr, v_addi.
    rewrite !Z_to_bv_unsigned.
    rewrite v_add_small
      by (rewrite u_Z2bv by lia; rewrite v_slli_3 by (rewrite u_argcN; lia);
          rewrite u_argcN; lia).
    rewrite u_Z2bv by lia.
    rewrite v_slli_3 by (rewrite u_argcN; lia).
    rewrite u_argcN.
    f_equal; lia.
  Qed.

  (* =============================================================== *)
  (* Wrapped initial memory and its read-backs                        *)
  (* =============================================================== *)

  Definition wmem : word -> option byte := wrap_mem inp mbase ph entry sp draw.

  (** At/above [sp] the wrapper equals the raw stack image (peels the
      zero-fill branch); this is the shared, overlay-free member of the
      [rdn_<layer>_above]/[rdn_wmem_stack] peeling triad. *)
  Lemma rdn_wmem_stack : forall (a : word) n,
    (bv_unsigned sp <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
    rdn segs wmem a n
    = rdn segs (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw)) a n.
  Proof. intros a n Ha Hn. unfold wmem. apply rdn_wrap_stack_above; assumption. Qed.

  (** The argc word at [sp]. *)
  Lemma read_argc_w :
    rdn segs wmem sp 8%nat = Some (word_le8 argcN).
  Proof.
    pose proof sp_hi_num.
    rewrite rdn_wmem_stack by lia.
    apply read_argc. exact bsb_nw.
  Qed.

  (* =============================================================== *)
  (* argv-pointer group (pointer bounds + read-back of the pointer    *)
  (* word through [wmem])                                             *)
  (* =============================================================== *)

  (** Address bounds for the [k]-th argv pointer.  Generalizes the
      per-example [psrc_bounds]/[pdst_bounds] over the index [k]; note it
      is [segs]- and overlay-independent.  The strings now sit at the TOP
      of the block, so the bound comes from the launch rather than from
      [valid_argv]/[valid_envp] and needs no slack constant. *)
  Lemma argv_ptr_bounds_at : forall k, (k < length (in_argv inp))%nat ->
    (bv_unsigned sp
     <= bv_unsigned (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
                       (in_execfn inp) k))%Z /\
    (bv_unsigned (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
                    (in_execfn inp) k)
       + Z.of_nat (length (nth k (in_argv inp) [])) + 1 < 2^64)%Z.
  Proof.
    intros k Hk. exact (argv_ptr_bounds v inp mbase sp brk draw k Hlau Hk).
  Qed.

  (** Read-back of the [k]-th argv pointer word out of [wmem] (the
      overlay-free tail the [read_psrc_*]/[read_pdst_*] lemmas reduce to
      after peeling their own overlay). *)
  Lemma read_argv_ptr_w : forall k, (k < length (in_argv inp))%nat ->
    rdn segs wmem (sp + nat_to_word (8 + 8 * k)) 8%nat
    = Some (word_le8 (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
                        (in_execfn inp) k)).
  Proof.
    intros k Hk. pose proof sp_lo_num. pose proof sp_hi_num.
    pose proof (valid_argv_len (in_argv inp) Hva) as Hal.
    rewrite rdn_wmem_stack by (rewrite word_add_nat; u_norm; lia).
    apply read_argv_ptr_k; [ exact Hk | exact bsb_nw ].
  Qed.

End Scaffold.
