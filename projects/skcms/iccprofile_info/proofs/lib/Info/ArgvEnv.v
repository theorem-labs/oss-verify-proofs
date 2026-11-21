(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the argument-vector facts read the launch input, mmap base, entry point and draw (valid_launch, entry_launch_ok_va). *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec SeqExec StepTac.
Unset Nia Cache.  (* [comment removed for export] *) Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

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
      is [segs]- and overlay-independent.  The strings sit at the TOP
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

Lemma cat_total_arg_bytes_firstn_S : forall k (l : list (list byte)), (k < length l)%nat ->
  (total_arg_bytes_nat (firstn (S k) l) = total_arg_bytes_nat (firstn k l) + (length (nth k l []) + 1))%nat.
Proof.
  induction k as [|k IH]; intros l Hk.
  - destruct l as [|s r]; [cbn in Hk; lia|]. change (firstn 1 (s :: r)) with [s]. change (firstn 0 (s :: r)) with (@nil (list byte)).
    change (nth 0 (s :: r) []) with s. rewrite total_arg_bytes_cons. change (total_arg_bytes_nat []) with 0%nat. lia.
  - destruct l as [|s r]; [cbn in Hk; lia|]. cbn in Hk.
    change (firstn (S (S k)) (s :: r)) with (s :: firstn (S k) r). change (firstn (S k) (s :: r)) with (s :: firstn k r).
    change (nth (S k) (s :: r) []) with (nth k r []). rewrite !total_arg_bytes_cons. rewrite (IH r) by lia. lia.
Qed.

(* 08b1429: the argv strings end eight bytes below the stack VMA's top ed_top, which the launch keeps
   at or below Sv48's STACK_TOP (valid_stack_top_va), so every argv string ends below TASK_SIZE. *)
Lemma cat_argv_ptr_task : forall inp mbase (sp brk : word) draw (k : nat),
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp ->
  (k < length (in_argv inp))%nat ->
  (bv_unsigned (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) k)
   + Z.of_nat (length (nth k (in_argv inp) [])) + 1 <= 0x800000000000)%Z.
Proof.
  intros inp mbase sp brk draw k Hlau Hk.
  pose proof (u_cat_string_base Sv48 inp mbase sp brk draw Hlau) as Hb.
  pose proof (launch_string_base_arith Sv48 inp mbase sp brk draw Hlau) as HA.
  pose proof Hlau as Hl. cbn [entry_launch_ok_va] in Hl. destruct Hl as ((_ & Htop & _) & _ & _).
  assert (Hvt : va_stack_top Sv48 = 0x800000000000%Z) by reflexivity. rewrite Hvt in Htop.
  pose proof (total_arg_bytes_firstn_le (S k) (in_argv inp)) as Hle.
  rewrite (cat_total_arg_bytes_firstn_S k (in_argv inp) Hk) in Hle.
  assert (HL : (total_arg_bytes_nat (in_argv inp)
                <= launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))%nat)
    by (unfold launch_string_bytes; rewrite length_flatten_strings; lia).
  pose proof (u64_range (ed_top draw)). pose proof (u64_range sp).
  rewrite cat_argv_ptr_offset by exact Hk. rewrite word_add_nat_Z2bv.
  rewrite u_Z2bv_lt by (rewrite Hb; lia).
  rewrite Hb. lia.
Qed.
