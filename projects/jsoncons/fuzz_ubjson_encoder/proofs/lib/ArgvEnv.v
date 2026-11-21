(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs; the new launch (process input, auxv, group id, exec file name); the BMode context. *)
(** * Common/ArgvEnv.v — parametric argv/envp/stack-window startup scaffolding

    Every example's source/target proof rebuilds the same startup
    bookkeeping out of only the initial stack pointer [sp], the argv/envp
    lists [av]/[ev], and the four ambient hypotheses shared by every
    binary ([valid_argv av], [valid_envp ev] and the OS-fixed sp-window
    bounds).  This module proves that bookkeeping ONCE, in a section
    quantified over [(segs, sp, av, ev)] plus those four hypotheses, so a
    per-binary file instantiates it (twice: once at the source [rsp], once
    at the target [asp]) with a one-line [exact]/[apply] per lemma instead
    of re-deriving it.

    What lives here (fully determined by [sp], [av], [ev] and the
    hypotheses, so it generalizes cleanly):

    - [sp_lo_num]/[sp_hi_num] : the OS sp-window restated as raw hex
      bounds (the [rsp_lo_num]/[rsp_hi_num] / [asp_*] twins);
    - [argcN] / [u_argcN]     : the argument count as a [word];
    - [bsb_nw]                : the initial stack image fits under 2^64
      (the [source_bsb_nw] / [target_bsb_nw] no-overflow side condition);
    - [envp_ptr] / [envp_ptr_eq] : musl's [environ] pointer and the fact
      that _start's [addi (add sp<<...) 8] computes it;
    - [wmem] / [rdn_wmem_stack] / [read_argc_w] : the initial wrapped
      memory, its agreement with the raw stack image at/above [sp], and
      the read-back of the [argc] word;
    - [argv_ptr_bounds_at] / [read_argv_ptr_w] : the [k]-th argv pointer's
      address bounds and its read-back through [wmem] (via CatExec's
      [cat_argv_ptr] / [read_argv_ptr_k]).

    What CANNOT live here (depends on the per-binary memory OVERLAY — the
    example's [fmem]/[emem] wbytes stack of callee-save/environ stores —
    or on FileSim, which not every example imports): the
    [rdn_<overlay>_above] peel lemmas and the overlay-level argv read-back
    lemmas ([read_psrc_*], [source_cstr_*]).  Those stay local; their
    generic tail is exactly [rdn_wmem_stack] + [read_argv_ptr_w] /
    FileSim's [read_argv_cstr_k], which they call after peeling their own
    overlay down to [wmem].

    This file imports only Common (up to StepTac) and the specification;
    it never imports an example.

    Reference instantiation: [Examples/modprint_ns/modprint_ns_source.v]
    and [..._target.v] (the [rsp] and [asp] copies).  Some other examples
    hand-roll the same lemmas; new examples should not. *)

From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatExec SeqExec StepTac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section Scaffold.

  (** The loaded segments (source_segs / target_segs at each call site)
      and the launch: the process input, the entry's mmap base, stack
      pointer, program break and draw.  The argv/envp lists, the
      credentials and AT_HWCAP are fields of [inp], and the stack VMA's
      end is [ed_top] of the draw, so one [ProcInput] and one
      [EntryDraw] fix the whole initial stack image. *)
  Variable segs : list Segment. Context {bmK : BMode}.
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
