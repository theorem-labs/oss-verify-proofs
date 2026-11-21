(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the argument block read from the launch input ProcInput through Run.entry_stack_image under valid_launch and entry_launch_ok_va, with the argv pointers counted from the stack top; adds read_argc_prefix_w and read_argv0_prefix_w, which bound only the argc and first argv reads); and launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StepTac.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StepTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
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

(* The startup slice reads only the argc/argv prefix.  Bound the read itself,
   not the unused tail of entry_stack_image; no extra launch premise is needed.
   These are the PropExec.rdn_stack/read_at_offset proofs with that local bound. *)
Lemma rdn_stack_read_bound : forall segs sp bytes k addr,
  (bv_unsigned sp <= bv_unsigned addr)%Z ->
  (Z.to_nat (bv_unsigned addr - bv_unsigned sp) + k <= length bytes)%nat ->
  (bv_unsigned addr + Z.of_nat k < 2^64)%Z ->
  rdn segs (stack_to_mem sp bytes) addr k =
  Some (firstn k (skipn (Z.to_nat (bv_unsigned addr - bv_unsigned sp)) bytes)).
Proof.
  intros segs sp bytes k. induction k as [|k IH]; intros addr Hsp Hlen Hnw.
  - cbn. reflexivity.
  - cbn [rdn].
    destruct (nth_error_skipn_cons bytes (Z.to_nat (bv_unsigned addr - bv_unsigned sp)) ltac:(lia)) as [b [Hnth Hskip]].
    unfold stack_to_mem.
    assert (Hle : Z.leb (bv_unsigned sp) (bv_unsigned addr) = true) by (apply Z.leb_le; lia).
    rewrite Hle.
    assert (Hlt : Z.ltb (bv_unsigned addr - bv_unsigned sp) (Z.of_nat (length bytes)) = true)
      by (apply Z.ltb_lt; lia).
    rewrite Hlt, Hnth.
    assert (Hu1 : bv_unsigned (addr + 1) = (bv_unsigned addr + 1)%Z) by (apply u_add1; lia).
    rewrite IH by lia.
    rewrite Hskip.
    replace (Z.to_nat (bv_unsigned (addr + 1) - bv_unsigned sp))
      with (S (Z.to_nat (bv_unsigned addr - bv_unsigned sp))) by lia.
    reflexivity.
Qed.

Lemma read_at_offset_read_bound : forall segs (sp : word) bytes pre mid post k,
  bytes = pre ++ mid ++ post -> length mid = k ->
  (bv_unsigned sp + Z.of_nat (length pre) + Z.of_nat k < 2^64)%Z ->
  rdn segs (stack_to_mem sp bytes) (sp + nat_to_word (length pre)) k = Some mid.
Proof.
  intros segs sp bytes pre mid post k Hb Hk Hnw.
  pose proof (u64_range sp) as Hsp64.
  assert (Hu : bv_unsigned (sp + nat_to_word (length pre)) = (bv_unsigned sp + Z.of_nat (length pre))%Z).
  { unfold nat_to_word. rewrite bv_add_unsigned, Z_to_bv_unsigned.
    rewrite bv_wrap_add_idemp_r, bv_wrap64_mod. apply Z.mod_small. lia. }
  assert (Hsp : (bv_unsigned sp <= bv_unsigned (sp + nat_to_word (length pre)))%Z) by lia.
  assert (Hlen : (Z.to_nat (bv_unsigned (sp + nat_to_word (length pre)) - bv_unsigned sp) + k <= length bytes)%nat)
    by (rewrite Hu, Hb, !length_app; lia).
  rewrite (rdn_stack_read_bound segs sp bytes k _ Hsp Hlen ltac:(lia)).
  rewrite Hu.
  replace (Z.to_nat (bv_unsigned sp + Z.of_nat (length pre) - bv_unsigned sp)) with (length pre) by lia.
  rewrite Hb, skipn_app, skipn_all, Nat.sub_diag.
  cbn [app]. rewrite skipn_O.
  rewrite firstn_app, <- Hk, firstn_all, Nat.sub_diag.
  cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

Lemma read_argc_prefix_w : forall segs inp mbase ph entry sp draw,
  (bv_unsigned sp + 8 < 2^64)%Z ->
  rdn segs (wrap_mem inp mbase ph entry sp draw) sp 8%nat =
  Some (word_le8 (argcN inp)).
Proof.
  intros segs inp mbase ph entry sp draw Hnw.
  rewrite rdn_wrap_stack_above by lia.
  destruct (bsb_argc_prefix (launch_auxv inp sp mbase) ph entry sp (ed_top draw)
              (in_argv inp) (in_envp inp) (in_execfn inp)
              (in_uid inp) (in_gid inp) (in_hwcap inp) draw) as [tl E].
  rewrite <- entry_stack_image_block in E.
  pose proof (read_at_offset_read_bound segs sp (entry_stack_image inp mbase ph entry sp draw)
                [] (word_le8 (len_word (in_argv inp))) tl 8%nat) as H.
  cbn [length] in H. rewrite word_add_0 in H.
  apply H; [exact E | reflexivity | lia].
Qed.

Lemma read_argv0_prefix_w : forall segs inp mbase ph entry sp draw,
  (0 < length (in_argv inp))%nat ->
  (bv_unsigned sp + 16 < 2^64)%Z ->
  rdn segs (wrap_mem inp mbase ph entry sp draw) (sp + nat_to_word 8) 8%nat =
  Some (word_le8 (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) 0)).
Proof.
  intros segs inp mbase ph entry sp draw Hk Hnw.
  pose proof (u64_range sp) as Hsp64.
  rewrite rdn_wrap_stack_above by (rewrite word_add_nat; u_norm; lia).
  destruct (bsb_ptr_k inp mbase ph entry sp draw 0 Hk) as [post E].
  cbn [firstn flat_map app] in E.
  change (entry_stack_image inp mbase ph entry sp draw =
    word_le8 (len_word (in_argv inp)) ++
    word_le8 (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) ++ post) in E.
  pose proof (read_at_offset_read_bound segs sp (entry_stack_image inp mbase ph entry sp draw)
    (word_le8 (len_word (in_argv inp)))
    (word_le8 (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) 0))
    post 8%nat E (length_n_to_le_8 _) ltac:(rewrite length_n_to_le_8; lia)) as H.
  rewrite length_n_to_le_8 in H. exact H.
Qed.
