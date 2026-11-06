(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_canonical on the ASan build of
   plugin-hostd/fuzz_command, in the shape of cgif_file_fuzzer's walks (lib/A/AC8b.v: a loop walked by the
   symbolic executor over the position-abstract listing, its inline shadow checks removed by tok_load/tok_branch)
   and of this unit's xstrdup walk (the malloc call through amalloc04_sub of PaCall.v).
   The walk is cut at six points: the malloc return (0x89338: the null check, decided by the executor, and the
   empty-line check), the outer head (0x89354), the word-scan head (0x89364), the word start (0x893a0), the copy
   head (0x893e8) and the tail (0x89474); the model of the output is lib/Prog/RecFacts.v's
   canon T = join_sp (words T), and the word lemmas below are the Words section of fuzz_command's own released
   plain proof lib/Prog/rec_canonical.v, copied so that the walk stands on RecFacts alone. The walk's hypotheses are
   the statement's AMALLOC4 and TL (CmdPaLib.v: the malloc trampoline is the rule's entry, the GOT shadow cell). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_canonical.v, with its module paths and module names changed; 696 of its 835 lines of code are new or changed and 2224 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/rec_canonical.v, with its module paths, module names, addresses and numbers changed; 1240 of its 1322 lines of code are new or changed and 753 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/sup_instance_verb.v, with its module paths and module names changed; 226 of its 313 lines of code are new or changed and 1235 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/RecTail.v, with its module paths and module names changed; 31 of its 63 lines of code are new or changed and 281 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/descriptors_get_c.v; 18 of its 51 lines of code are new or changed and 30 lines of the source are left out. *)
From Stdlib Require Import String ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInvU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Definition DESCRIPTORS_ADD : Z := 0x1721c.
Definition DESCRIPTORS_ADD_K : Z := 8368.

Definition descriptors_add_sizes (uri : option (list byte)) : list Z :=
  [Z.of_nat (length (sarg uri)) + 1].

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition descriptors_add_ret (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (uri : option (list byte)) (R : rstate) (O : list (Z * Z)) (b : sbound) (c' : config) : Prop :=
  exists L' A' regs' mem' md' O',
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    call_post_rec B MR DESCRIPTORS_ADD_K L A regs mem md rec_area (fun a => In a (map fst O)) L' A' regs' mem' md' /\
    g_rec_rep segs L' A' mem' (descriptors_add_m R uri) O' /\ owns_new L A O O' /\
    (forall pn, In pn (blocks L' A') -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn O') /\
    others_kept segs L A mem L' A' mem' O /\
    ro_agree segs mem' /\ f18_words segs mem' /\
    st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    sb_le (sb_shift b A A') (sb_mallocs b (descriptors_add_sizes uri)) /\
    res_ok_slots A' (sb_shift b A A').

Definition descriptors_add_contract : Prop :=
  forall L A regs mem md (pu : Z) (uri : option (list byte)) (R : rstate) (O : list (Z * Z)) b,
    call_pre_k B MR DESCRIPTORS_ADD_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 pu ->
    str_arg B L A O (spZ regs) DESCRIPTORS_ADD_K mem pu uri ->
    g_rec_rep segs L A mem R O ->
    ro_agree segs mem -> f18_words segs mem ->
    res_ok_slots A b ->
    room_ag (sb_mallocs b (descriptors_add_sizes uri)) (LMAX + 1) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 DESCRIPTORS_ADD) mem (seg_rom segs)) md)
      (descriptors_add_ret L A regs mem md uri R O b).

End K.
