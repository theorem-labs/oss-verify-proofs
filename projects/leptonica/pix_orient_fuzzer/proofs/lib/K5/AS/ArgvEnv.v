(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch input ProcInput; the recorded proofs of sp_lo_num, sp_hi_num, u_argcN, bsb_nw, envp_ptr_eq, rdn_wmem_stack and 3 more replaced by plain proofs). *)
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import PropExec CatExec SeqExec StepTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

Section Scaffold.

  (* [comment removed for export] *)
  Variable segs : list Segment.
  Variable v : VaSize.
  Variable inp : ProcInput.
  Variable mbase : word.

  (* [comment removed for export] *)
  Variable ph : PhdrInfo.
  Variable entry : word.

  Variable sp brk : word.
  Variable draw : EntryDraw.

  (* [comment removed for export] *)
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va v (mkEntry sp brk mbase draw) inp.
  Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned sp)%Z.
  Hypothesis Hsp_hi : (bv_unsigned sp <= sp_window_hi)%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma sp_lo_num : (0x7fff80000000 <= bv_unsigned sp)%Z.
  Proof. exact Hsp_lo. Qed.

  Lemma sp_hi_num : (bv_unsigned sp <= 0x800000000000)%Z.
  Proof. exact Hsp_hi. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition argcN : word := len_word (in_argv inp).

  Lemma u_argcN : bv_unsigned argcN = Z.of_nat (length (in_argv inp)).
  Proof.
    pose proof (valid_argv_len (in_argv inp) Hva).
    unfold argcN, len_word. apply u_Z2bv; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma bsb_nw :
    (bv_unsigned sp
     + Z.of_nat (length (entry_stack_image inp mbase ph entry sp draw)) < 2^64)%Z.
  Proof.
    pose proof (bsb_bound v inp mbase ph entry sp brk draw Hvl Hlau).
    pose proof sp_hi_num. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition wmem : word -> option byte := wrap_mem inp mbase ph entry sp draw.

  (* [comment removed for export] *)
  Lemma rdn_wmem_stack : forall (a : word) n,
    (bv_unsigned sp <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
    rdn segs wmem a n
    = rdn segs (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw)) a n.
  Proof. intros a n Ha Hn. unfold wmem. apply rdn_wrap_stack_above; assumption. Qed.

  (* [comment removed for export] *)
  Lemma read_argc_w :
    rdn segs wmem sp 8%nat = Some (word_le8 argcN).
  Proof.
    pose proof sp_hi_num.
    rewrite rdn_wmem_stack by lia.
    apply read_argc. exact bsb_nw.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
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
