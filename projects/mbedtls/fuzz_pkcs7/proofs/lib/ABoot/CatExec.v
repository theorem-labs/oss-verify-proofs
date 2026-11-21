(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the encoded statements written out in plain text, the using attributes dropped and doc comments added; the revision's stack layout, with the argument strings at the top of the stack block: cat_string_base taken from the stack end, cat_string_off and cat_block_head added, and the argv read lemmas restated over the whole input with the entry_launch_ok_va premise; launch arithmetic and word lemmas added; wrap_mem_below bounded by stack_window_lo; the access_okb premise on tw_write_gen and tw_write_rec); and launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import ExitSim PropExec CatSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_CatExec () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Datatypes.nat"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_rom"; "OSSVerify.KrLib.ABoot.PropExec.seg_rom"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_read_bytes_aux"; "OSSVerify.KrLib.ABoot.PropExec.rdn"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_mem"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_read_bytes"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.word_to_nat"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "WithFP.wbytes"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.or"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.is_ecall"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.Riscv.Instr.instr"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.Riscv.DecodeC.decode_any"; "Corelib.Init.Datatypes.pair"; "LinuxProcessSemantics.Riscv.Instr.Store"; "LinuxProcessSemantics.Riscv.Instr.SZ8"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "OSSVerify.KrLib.ABoot.PropExec.v_addi"; "OSSVerify.KrLib.ABoot.PropExec.getr"; "stdpp.bitvector.definitions.bv_signed"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step"; "OSSVerify.KrLib.ABoot.PropExec.mkst"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.PhdrInfo"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.EntryDraw"; "Stdlib.ZArith.BinInt.Z.sub"; "LinuxProcessSemantics.LinuxProcessSem.State.stack_max_size"; "OSSVerify.KrLib.ABoot.PropExec.wrap_mem"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Peano.lt"; "Stdlib.Lists.List.flat_map"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.word_le8"; "Corelib.Init.Datatypes.app"; "Corelib.Lists.ListDef.firstn"; "Corelib.Lists.ListDef.nth"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Lists.ListDef.skipn"; "Corelib.Init.Datatypes.S"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.flatten_strings"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.fst"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.string_addrs"; "stdpp.bitvector.definitions.bv_add"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.nat_to_word"; "OSSVerify.KrLib.ABoot.PropExec.total_arg_bytes_nat"; "WithFP.cat_argv_ptr"; "WithFP.cat_string_base"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.len_word"; "WithFP.cat_env_base"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.auxv_bytes"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.at_random_ptr"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.build_stack_bytes"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.stack_to_mem"; "LinuxProcessSemantics.LinuxProcessSem.Run.entry_stack_image"; "Corelib.Init.Nat.add"; "Corelib.Init.Nat.mul"; "WithFP.cat_struct_prefix"; "WithFP.cat_struct_size"; "Corelib.Init.Peano.le"; "LinuxProcessSemantics.LinuxProcessSem.Run.valid_argv"; "LinuxProcessSemantics.LinuxProcessSem.Fs.path_eqb"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi.dot_path"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open.openat_plain_name"; "Corelib.Lists.ListDef.Forall"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.Build_machine_state"; "OSSVerify.KrLib.ABoot.PropExec.fp_regs"; "OSSVerify.KrLib.ABoot.PropExec.fp_csr"; "LinuxProcessSemantics.LinuxProcessSem.Run.advance_past_svc"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.set_gpr0"; "OSSVerify.KrLib.ABoot.PropExec.regupd"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_gpr"; "WithFP.pend"; "OSSVerify.KrLib.ABoot.CatSim.to_wexit"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "OSSVerify.KrLib.ABoot.ExitSim.is_exit_no"; "LinuxProcessSemantics.Riscv.Sem.reg_get"].


Section WithFP.
Context {fx : FPState}.

(* ================================================================= *)
(* (A) ms_read_bytes -> rdn bridge                                   *)
(* ================================================================= *)

Lemma ms_read_bytes_aux_rdn : forall segs ms n addr,
  ms_rom ms = seg_rom segs ->
  ms_read_bytes_aux ms addr n = rdn segs (ms_mem ms) addr n.
Proof.
  intros segs ms n. induction n as [|n IH]; intros addr Hrom; [reflexivity|].
  cbn [ms_read_bytes_aux rdn]. unfold ms_read_byte. rewrite Hrom.
  destruct (ms_mem ms addr) as [b|].
  - rewrite IH by exact Hrom. reflexivity.
  - unfold seg_rom. destruct (memory_read segs addr 1) as [[|b r]|];
      try reflexivity; rewrite IH by exact Hrom; reflexivity.
Qed.

Lemma ms_read_bytes_rdn : forall segs ms addr len,
  ms_rom ms = seg_rom segs ->
  ms_read_bytes ms addr len = rdn segs (ms_mem ms) addr (word_to_nat len).
Proof. intros. unfold ms_read_bytes. apply ms_read_bytes_aux_rdn; assumption. Qed.

(* ================================================================= *)
(* (B) Store-double memory theory                                    *)
(* ================================================================= *)

(* memory-level mirror of the interpreter's store path (write_to_mem) *)
Fixpoint wbytes (m : word -> option byte) (addr : word) (bs : list byte)
    : word -> option byte :=
  match bs with
  | [] => m
  | b :: rest => wbytes (fun a => if bv_eqb a addr then Some b else m a) (addr+1) rest
  end.

(** Reads at/above the end of the written range are unchanged.  The
    bound [addr + length bs <= x < 2^64] already rules out a wrapping
    write walk, so no extra no-overflow hypothesis is needed. *)
Lemma wbytes_above : forall bs m (addr x : word),
  (bv_unsigned addr + Z.of_nat (length bs) <= bv_unsigned x)%Z ->
  wbytes m addr bs x = m x.
Proof.
  induction bs as [|b rest IH]; intros m addr x Hle; [reflexivity|].
  cbn [wbytes length] in *.
  pose proof (u64_range x) as Hx.
  assert (Hu1 : bv_unsigned (addr + 1) = (bv_unsigned addr + 1)%Z)
    by (apply u_add1; lia).
  rewrite IH by lia.
  cbv beta.
  assert (Hne : bv_eqb x addr = false)
    by (unfold bv_eqb; apply Z.eqb_neq; lia).
  rewrite Hne. reflexivity.
Qed.

Lemma rdn_wbytes_disjoint : forall segs bs m (addr a : word) n,
  (bv_unsigned addr + Z.of_nat (length bs) <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn segs (wbytes m addr bs) a n = rdn segs m a n.
Proof.
  intros segs bs m addr a n Hle Hnw. apply rdn_ext; [exact Hnw|].
  intros x Hx. apply wbytes_above. lia.
Qed.

(** Reads below the written range are unchanged.  A no-overflow
    hypothesis [addr + length bs <= 2^64]: the write walk is a wrapping
    [bv] add, so without it the tail of a huge write could wrap around
    to [x].  Trivially discharged downstream (stack stores sit far
    below 2^64). *)
Lemma wbytes_below : forall bs m (addr x : word),
  (bv_unsigned addr + Z.of_nat (length bs) <= 2^64)%Z ->
  (bv_unsigned x < bv_unsigned addr)%Z ->
  wbytes m addr bs x = m x.
Proof.
  induction bs as [|b rest IH]; intros m addr x Hnw Hlt; [reflexivity|].
  cbn [wbytes length] in *.
  assert (Hne : bv_eqb x addr = false)
    by (unfold bv_eqb; apply Z.eqb_neq; lia).
  destruct rest as [|b' rest'].
  - cbn [wbytes]. rewrite Hne. reflexivity.
  - assert (Hu1 : bv_unsigned (addr + 1) = (bv_unsigned addr + 1)%Z)
      by (apply u_add1; cbn [length] in Hnw; lia).
    rewrite IH by lia.
    cbv beta. rewrite Hne. reflexivity.
Qed.

Lemma rdn_wbytes_below : forall segs bs m (addr a : word) n,
  (bv_unsigned a + Z.of_nat n <= bv_unsigned addr)%Z ->
  (bv_unsigned addr + Z.of_nat (length bs) <= 2^64)%Z ->
  rdn segs (wbytes m addr bs) a n = rdn segs m a n.
Proof.
  intros segs bs m addr a n Hle Hnw.
  pose proof (u64_range addr) as Ha.
  apply rdn_ext; [lia|].
  intros x Hx. apply wbytes_below; [exact Hnw|lia].
Qed.

(** The two-sided form.  [rdn_wbytes_disjoint] and [rdn_wbytes_below]
    each need to know WHICH side of the store the read sits on, and a
    peeling tactic has to commit to one of them before its side
    condition is proved.  That is fine for a store at a known address,
    and wrong for a store into an mmap grant: all a proof has about the
    grant base is that it avoids the image ([MmapSim.zfill]'s own
    [rdn_zfill_out] is already stated over exactly this disjunction, for
    the same reason), so neither one-sided bound holds on its own and
    only their disjunction does. *)
Lemma rdn_wbytes_out : forall segs bs m (addr a : word) n,
  (bv_unsigned a + Z.of_nat n <= bv_unsigned addr
   \/ bv_unsigned addr + Z.of_nat (length bs) <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  (bv_unsigned addr + Z.of_nat (length bs) <= 2^64)%Z ->
  rdn segs (wbytes m addr bs) a n = rdn segs m a n.
Proof.
  intros segs bs m addr a n [Hb|Hd] Hnw Hnw'.
  - apply rdn_wbytes_below; [exact Hb | exact Hnw'].
  - apply rdn_wbytes_disjoint; [exact Hd | exact Hnw].
Qed.

Lemma length_Z_to_le_bytes : forall n z, length (Z_to_le_bytes n z) = n.
Proof.
  induction n as [|n IH]; intro z; [reflexivity|].
  cbn [Z_to_le_bytes length]. rewrite IH. reflexivity.
Qed.

Lemma length_N_to_le_bytes : forall n (v : word), length (word_to_le_bytes n v) = n.
Proof. intros. unfold word_to_le_bytes. apply length_Z_to_le_bytes. Qed.

(** The tree interpreter's byte-writer [write_to_mem] IS [wbytes]
    (same recursion, byte [i] at [addr + i]) — the one bridge the
    store-lemma proofs need, since [interp_eff] threads only the
    memory overlay. *)
Lemma write_to_mem_wbytes : forall bs (m : word -> option byte) (addr : word),
  write_to_mem m addr bs = wbytes m addr bs.
Proof.
  induction bs as [|b rest IH]; intros m addr; [reflexivity|].
  cbn [write_to_mem wbytes]. apply IH.
Qed.

(** Store double: writes 8 bytes to [wbytes] at [rs1+imm]; registers and
    (modulo the store) the rest of memory are unchanged.  The exact stored
    value is irrelevant downstream (only its 8-byte length matters), so it is
    left existential (the witness is [word_to_le_bytes 8 rs2] — the exact
    little-endian byte list the interpreter writes for the tree's
    64-bit [EStore], = [word_le8] of rs2).

    Side-condition: all 8 target bytes must be WRITABLE
    ([RiscvSemantics.store_ok] — present in the overlay, or in a
    segment carrying 'w'), or the store faults.  Note this depends on
    [mem]: a store is bounded by what the process has actually mapped,
    not merely by which segments it misses, so an unmapped-store fault is
    the SIGSEGV it is on Linux and does not silently create a mapping.
    For the stack stores this covers, the target is in the RLIMIT_STACK
    window the initial overlay zero-maps, so the condition closes by
    [Common/StoreOk.solve_store_ok]. *)
Lemma step_sd : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) 8%nat = true ->
  exists bs, length bs = 8%nat /\
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm)) bs) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  exists (word_to_le_bytes 8 (getr regs rs2)). split; [reflexivity|].
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, b_npc4. reflexivity.
Qed.

(** THE ARITHMETIC OF RULE 2, ONCE.  [Run.launch_sp_hi] is
    [align_down16 (top - 8 - L) - C] and [align_down16] never raises its
    argument, so the head, the strings and the eight-byte slot
    [create_init_stack_vma] (mm/vma_exec.c, Linux v6.18.46, commit
    1f99e9ab748f) skipped all fit between [sp] and the stack VMA's end.
    Every address lemma below reads this. *)
Lemma launch_string_base_arith : forall v inp mbase (sp brk : word) draw,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (bv_unsigned sp
   + Z.of_nat (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp)
                 (in_envp inp))
   + Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                 (in_execfn inp))
   + 8 <= bv_unsigned (ed_top draw))%Z.
Proof.
  intros v inp mbase sp brk draw Hlaunch.
  cbn [entry_launch_ok_va] in Hlaunch.
  destruct Hlaunch as (_ & (_ & _ & Hhi) & _).
  unfold launch_sp_hi, align_down16 in Hhi.
  pose proof (Z.mod_pos_bound
    (bv_unsigned (ed_top draw) - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                   (in_execfn inp))) 16 ltac:(lia)).
  lia.
Qed.

(** The entry stack pointer is inside the stack VMA.  Read wherever a
    proof needs the window floor [Run.stack_window_lo], which counts
    RLIMIT_STACK from [ed_top] ([expand_downwards], mm/vma.c, Linux
    v6.18.46, commit 1f99e9ab748f), to lie at or below [sp - 8 MiB]. *)
Lemma launch_sp_le_ed_top : forall v inp mbase (sp brk : word) draw,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (bv_unsigned sp <= bv_unsigned (ed_top draw))%Z.
Proof.
  intros v inp mbase sp brk draw Hlaunch.
  pose proof (launch_string_base_arith v inp mbase sp brk draw Hlaunch).
  pose proof (Nat2Z.is_nonneg
    (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))).
  pose proof (Nat2Z.is_nonneg
    (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))).
  lia.
Qed.

(** Below the live stack region the wrapper memory reads as unmapped. *)
Lemma stack_max_size_val : stack_max_size = 8388608%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma wrap_mem_below :
  forall v inp mbase ph entry (sp brk : word) draw (addr : word),
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (bv_unsigned addr < bv_unsigned sp - stack_max_size)%Z ->
  wrap_mem inp mbase ph entry sp draw addr = None.
Proof.
  intros v inp mbase ph entry sp brk draw addr Hlau Hlt.
  pose proof stack_max_size_val as Hsms.
  pose proof (launch_sp_le_ed_top v inp mbase sp brk draw Hlau) as Htop.
  pose proof (Z.le_max_l (bv_unsigned (ed_top draw) - stack_max_size)
                (bv_unsigned mbase + stack_guard_gap_bytes (in_kernel inp))) as Hmax.
  unfold wrap_mem, stack_to_mem.
  assert (Hsp : Z.leb (bv_unsigned sp) (bv_unsigned addr) = false)
    by (apply Z.leb_gt; lia).
  rewrite Hsp.
  assert (Hgate : Z.leb (stack_window_lo (in_kernel inp) mbase draw)
                        (bv_unsigned addr) = false)
    by (apply Z.leb_gt; unfold stack_window_lo in *; lia).
  rewrite Hgate. reflexivity.
Qed.

(* ================================================================= *)
(* (C) Generic list helpers                                          *)
(* ================================================================= *)

Lemma flat_map_app' : forall {A B : Type} (f : A -> list B) l1 l2,
  flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof.
  intros A B f l1 l2. induction l1 as [|x xs IH]; cbn; [reflexivity|].
  rewrite IH, app_assoc. reflexivity.
Qed.

Lemma skipn_nth : forall {A : Type} (l : list A) k d, (k < length l)%nat ->
  skipn k l = nth k l d :: skipn (S k) l.
Proof.
  induction l as [|x xs IH]; intros k d Hk; [cbn in Hk; lia|].
  destruct k as [|k']; [reflexivity|].
  cbn [skipn nth]. apply IH. cbn in Hk; lia.
Qed.

Lemma flat_map_split : forall {A B : Type} (f : A -> list B) l k d, (k < length l)%nat ->
  flat_map f l = flat_map f (firstn k l) ++ f (nth k l d) ++ flat_map f (skipn (S k) l).
Proof.
  intros A B f l k d Hk.
  rewrite <- (firstn_skipn k l) at 1.
  rewrite flat_map_app'.
  rewrite (skipn_nth l k d Hk). reflexivity.
Qed.

Lemma flat_map_le8_decomp : forall (l : list word) k, (k < length l)%nat ->
  flat_map word_le8 l =
  flat_map word_le8 (firstn k l) ++ word_le8 (nth k l (Z_to_bv 64 0))
    ++ flat_map word_le8 (skipn (S k) l).
Proof. intros l k Hk. apply (flat_map_split word_le8 l k (Z_to_bv 64 0) Hk). Qed.

Lemma flatten_strings_decomp : forall strs k, (k < length strs)%nat ->
  flatten_strings strs =
  flatten_strings (firstn k strs) ++ (nth k strs [] ++ [Z_to_bv 8 0])
    ++ flatten_strings (skipn (S k) strs).
Proof.
  intros strs k Hk.
  apply (flat_map_split (fun s => s ++ [Z_to_bv 8 0]) strs k [] Hk).
Qed.

Lemma total_arg_bytes_cons : forall s l,
  total_arg_bytes_nat (s :: l) = (length s + 1 + total_arg_bytes_nat l)%nat.
Proof. reflexivity. Qed.

Lemma total_arg_bytes_firstn_le : forall k l,
  (total_arg_bytes_nat (firstn k l) <= total_arg_bytes_nat l)%nat.
Proof.
  induction k as [|k IH]; intros l.
  - change (total_arg_bytes_nat (firstn 0 l)) with 0%nat. lia.
  - destruct l as [|s rest]; [cbn; lia|].
    cbn [firstn]. rewrite !total_arg_bytes_cons. specialize (IH rest). lia.
Qed.

(** String [k], its bytes and its NUL all fit inside the blob: what
    bounds an argv pointer now that the strings sit at the TOP of the
    block and the only budget above them is [L]
    ([StackLayout.launch_string_bytes]). *)
Lemma total_arg_bytes_firstn_within : forall (l : list (list byte)) k,
  (k < length l)%nat ->
  (total_arg_bytes_nat (firstn k l) + length (nth k l []) + 1
   <= total_arg_bytes_nat l)%nat.
Proof.
  intros l. induction l as [|s rest IH]; intros k Hk; [cbn in Hk; lia|].
  destruct k as [|k'].
  - cbn [firstn nth]. change (total_arg_bytes_nat []) with 0%nat.
    rewrite total_arg_bytes_cons. lia.
  - cbn [firstn nth]. rewrite !total_arg_bytes_cons.
    specialize (IH k' ltac:(cbn in Hk; lia)). lia.
Qed.

Lemma natN_le : forall n m, (n <= m)%nat -> (N.of_nat n <= N.of_nat m)%N.
Proof. intros n m H. lia. Qed.

(** vm-computed equations for [Z.of_nat] on the two large literals from
    [valid_argv]; sealing them behind a [Qed] keeps the (expensive) lazy
    conversion through a multi-million-cell unary [nat] out of both the
    tactic and the Qed-time kernel check of every user of these bounds. *)
Lemma of_nat_131071 : Z.of_nat 131071 = 131071%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma of_nat_2097152 : Z.of_nat 2097152 = 2097152%Z.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(* (D) Cat-argv stack-layout abbreviations                           *)
(* ================================================================= *)

(** [Z]-level readings of the three word operations the layout performs.
    [StepTac] states the same two facts, but [StepTac] is BELOW this
    file (it imports CatExec), so they are proved here. *)
Lemma u_Z2bv_lt : forall z, (0 <= z)%Z -> (z < 2 ^ 64)%Z ->
  bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z H0 H1. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  apply Z.mod_small. lia.
Qed.

Lemma word_add_nat_Z2bv : forall (a : word) (n : nat),
  a + nat_to_word n = Z_to_bv 64 (bv_unsigned a + Z.of_nat n).
Proof.
  intros a n. apply bv_eq. unfold nat_to_word.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  apply Zplus_mod_idemp_r.
Qed.

(** The companion of [word_add_nat_Z2bv] for the subtraction
    [StackLayout.string_base_addr] performs.  Hypothesis-free: both
    sides wrap identically. *)
Lemma word_sub_nat : forall (a : word) (n : nat),
  a - nat_to_word n = Z_to_bv 64 (bv_unsigned a - Z.of_nat n).
Proof.
  intros a n. apply bv_eq. unfold nat_to_word.
  rewrite bv_sub_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  apply Zminus_mod_idemp_r.
Qed.

(** The pointer vector [create_elf_tables] (fs/binfmt_elf.c, Linux
    v6.18.46, commit 1f99e9ab748f) writes AT the entry stack pointer:
    argc, the argv pointers and their NULL, the envp pointers and their
    NULL -- [8 * items] bytes ([StackLayout.block_items]).  The
    auxiliary vector follows it ([StackLayout.auxv_size] bytes), then
    the alignment gap and the sixteen AT_RANDOM bytes.

    THIS IS NO LONGER THE STRING OFFSET.  The strings sit at the TOP of
    the block, above the AT_RANDOM bytes and the [arch_align_stack]
    pad, so [cat_string_base] below takes the stack VMA's end rather
    than [sp]. *)
Definition cat_struct_size (av ev : list (list byte)) : nat :=
  (8 * block_items av ev)%nat.

(** argv[0]: the lowest string byte, [8 + L] below the stack VMA's end
    [top] ([StackLayout.string_base_addr]).  [do_execveat_common]
    (fs/exec.c) copies the exec file name, the envp strings and the
    argv strings downwards from the eight-byte slot
    [create_init_stack_vma] (mm/vma_exec.c) left at the top. *)
Definition cat_string_base (top : word) (av ev : list (list byte))
    (execfn : list byte) : word :=
  string_base_addr top av ev execfn.

Definition cat_env_base (top : word) (av ev : list (list byte))
    (execfn : list byte) : word :=
  cat_string_base top av ev execfn + nat_to_word (total_arg_bytes_nat av).

(** The k-th argv pointer value: the address of argv string k's bytes. *)
Definition cat_argv_ptr (top : word) (av ev : list (list byte))
    (execfn : list byte) (k : nat) : word :=
  nth k (fst (string_addrs (cat_string_base top av ev execfn) av)) (Z_to_bv 64 0).

(** The distance from [sp] to argv[0]: the head [C]
    ([StackLayout.block_head_size]) and the [arch_align_stack] pad above
    the sixteen AT_RANDOM bytes.  NOTHING BUT [Run.entry_launch_ok_va]
    PINS THE PAD, which is why every lemma below that turns this into an
    address carries that premise. *)
Definition cat_string_off (rseq : bool) (sp top : word)
    (av ev : list (list byte)) (execfn : list byte) : nat :=
  (block_head_size rseq av ev + block_pad_len rseq sp top av ev execfn)%nat.

Lemma nth_string_addrs : forall strs (base : word) k, (k < length strs)%nat ->
  nth k (fst (string_addrs base strs)) (Z_to_bv 64 0)
  = base + nat_to_word (total_arg_bytes_nat (firstn k strs)).
Proof.
  induction strs as [|s rest IH]; intros base k Hk; [cbn in Hk; lia|].
  rewrite string_addrs_fst_structure.
  destruct k as [|k'].
  - cbn [nth firstn]. change (total_arg_bytes_nat []) with 0%nat.
    rewrite word_add_0. reflexivity.
  - cbn [nth]. rewrite (IH (base + len_word s + 1) k' ltac:(cbn in Hk; lia)).
    cbn [firstn]. rewrite total_arg_bytes_cons.
    rewrite len_word_nat, word1_nat, !nat_to_word_add_merge.
    f_equal. f_equal. lia.
Qed.

Lemma cat_argv_ptr_offset : forall top av ev execfn k, (k < length av)%nat ->
  cat_argv_ptr top av ev execfn k
  = cat_string_base top av ev execfn
    + nat_to_word (total_arg_bytes_nat (firstn k av)).
Proof. intros. unfold cat_argv_ptr. apply nth_string_addrs. assumption. Qed.

(** argv[0]'s address in [Z]: [top - 8 - L]. *)
Lemma u_cat_string_base : forall v inp mbase (sp brk : word) draw,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  bv_unsigned (cat_string_base (ed_top draw) (in_argv inp) (in_envp inp)
                 (in_execfn inp))
  = (bv_unsigned (ed_top draw) - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                   (in_execfn inp)))%Z.
Proof.
  intros v inp mbase sp brk draw Hlaunch.
  pose proof (launch_string_base_arith v inp mbase sp brk draw Hlaunch) as HA.
  pose proof (u64_range sp). pose proof (u64_range (ed_top draw)).
  pose proof (Nat2Z.is_nonneg
    (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))).
  unfold cat_string_base, string_base_addr. rewrite word_sub_nat.
  assert (Hz : (0 <= bv_unsigned (ed_top draw)
                     - Z.of_nat (8 + launch_string_bytes (in_argv inp)
                                       (in_envp inp) (in_execfn inp))
                < 2 ^ 64)%Z).
  { rewrite Nat2Z.inj_add. change (Z.of_nat 8) with 8%Z. lia. }
  rewrite (u_Z2bv_lt _ (proj1 Hz) (proj2 Hz)).
  rewrite Nat2Z.inj_add. change (Z.of_nat 8) with 8%Z. lia.
Qed.

(** argv[0] in [sp]-relative form.  Under the launch conjunct the pad is
    exactly what is left of [top - sp] once the head, the strings and the
    eight-byte slot are taken out, so the [Z.to_nat] in
    [StackLayout.block_pad_len] does not clamp. *)
Lemma cat_string_base_offset : forall v inp mbase (sp brk : word) draw,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  cat_string_base (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp)
  = sp + nat_to_word (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top draw)
                        (in_argv inp) (in_envp inp) (in_execfn inp)).
Proof.
  intros v inp mbase sp brk draw Hlaunch.
  pose proof (launch_string_base_arith v inp mbase sp brk draw Hlaunch) as HA.
  pose proof (u_cat_string_base v inp mbase sp brk draw Hlaunch) as Hu.
  pose proof (u64_range sp). pose proof (u64_range (ed_top draw)).
  apply bv_eq. rewrite Hu, word_add_nat_Z2bv.
  unfold cat_string_off, block_pad_len.
  rewrite u_Z2bv_lt
    by (rewrite Nat2Z.inj_add; rewrite Z2Nat.id by lia; lia).
  rewrite Nat2Z.inj_add. rewrite Z2Nat.id by lia. lia.
Qed.

(* ================================================================= *)
(* (E) entry stack image decompositions                              *)
(* ================================================================= *)

(** The pointer vector at [sp], as bytes. *)
Definition cat_struct_prefix (top : word) (av ev : list (list byte))
    (execfn : list byte) : list byte :=
  word_le8 (len_word av)
  ++ flat_map word_le8 (fst (string_addrs (cat_string_base top av ev execfn) av))
  ++ word_le8 (Z_to_bv 64 0)
  ++ flat_map word_le8 (fst (string_addrs (cat_env_base top av ev execfn) ev))
  ++ word_le8 (Z_to_bv 64 0).

Lemma length_cat_struct_prefix : forall top av ev execfn,
  length (cat_struct_prefix top av ev execfn) = cat_struct_size av ev.
Proof.
  intros top av ev execfn.
  unfold cat_struct_prefix, cat_struct_size, block_items.
  rewrite !length_app, !length_flat_map_le8, !length_string_addrs_fst,
    !length_n_to_le_8.
  lia.
Qed.

(** Everything the block holds BELOW the strings: the pointer vector,
    the auxv, the alignment gap, the sixteen AT_RANDOM bytes and the
    [arch_align_stack] pad. *)
Definition cat_block_head (la : LaunchAuxv) (ph : PhdrInfo)
    (entry sp top : word) (av ev : list (list byte)) (execfn : list byte)
    (uid gid hw : word) (draw : EntryDraw) : list byte :=
  block_below_random la ph entry sp top av ev execfn uid gid hw
  ++ at_random_bytes (ed_random draw)
  ++ repeat (Z_to_bv 8 0) (block_pad_len (la_rseq la) sp top av ev execfn).

Lemma length_cat_block_head :
  forall la ph entry sp top av ev execfn uid gid hw draw,
  length (cat_block_head la ph entry sp top av ev execfn uid gid hw draw)
  = cat_string_off (la_rseq la) sp top av ev execfn.
Proof.
  intros la ph entry sp top av ev execfn uid gid hw draw.
  unfold cat_block_head, block_below_random, cat_string_off. cbv zeta.
  rewrite (string_addrs_pair av). cbv beta iota.
  rewrite (string_addrs_pair ev). cbv beta iota.
  rewrite !length_app, !repeat_length, !length_flat_map_le8,
    !length_string_addrs_fst, length_auxv_bytes, length_at_random_bytes,
    !length_n_to_le_8.
  unfold block_head_size, block_items. lia.
Qed.

(** image = argc ++ argv_ptrs ++ <tail>. *)
Lemma bsb_argv_prefix : forall inp mbase ph entry (sp : word) draw, exists tail,
  entry_stack_image inp mbase ph entry sp draw =
    word_le8 (len_word (in_argv inp))
    ++ flat_map word_le8
         (fst (string_addrs
                 (cat_string_base (ed_top draw) (in_argv inp) (in_envp inp)
                    (in_execfn inp))
                 (in_argv inp)))
    ++ tail.
Proof.
  intros inp mbase ph entry sp draw.
  rewrite entry_stack_image_block.
  unfold build_stack_bytes, cat_string_base. cbv zeta.
  rewrite (string_addrs_pair (in_argv inp)). cbv beta iota.
  rewrite (string_addrs_pair (in_envp inp)). cbv beta iota.
  eexists. rewrite <- !app_assoc. reflexivity.
Qed.

(** image = (argc ++ argv_ptrs[<k]) ++ argv_ptrs[k] ++ <post>. *)
Lemma bsb_ptr_k : forall inp mbase ph entry (sp : word) draw k,
  (k < length (in_argv inp))%nat -> exists post,
  entry_stack_image inp mbase ph entry sp draw =
    (word_le8 (len_word (in_argv inp))
      ++ flat_map word_le8
           (firstn k (fst (string_addrs
                             (cat_string_base (ed_top draw) (in_argv inp)
                                (in_envp inp) (in_execfn inp))
                             (in_argv inp)))))
    ++ word_le8 (nth k (fst (string_addrs
                               (cat_string_base (ed_top draw) (in_argv inp)
                                  (in_envp inp) (in_execfn inp))
                               (in_argv inp))) (Z_to_bv 64 0))
    ++ post.
Proof.
  intros inp mbase ph entry sp draw k Hk.
  destruct (bsb_argv_prefix inp mbase ph entry sp draw) as [tail E].
  assert (Hk' : (k < length (fst (string_addrs
                   (cat_string_base (ed_top draw) (in_argv inp) (in_envp inp)
                      (in_execfn inp)) (in_argv inp))))%nat)
    by (rewrite length_string_addrs_fst; exact Hk).
  rewrite (flat_map_le8_decomp _ k Hk') in E.
  eexists. rewrite E. rewrite <- !app_assoc. reflexivity.
Qed.

(** The argv pointer array is still AT [sp]: the k-th pointer is eight
    bytes at [sp + 8 + 8k], which is why this lemma needs no launch
    premise.  Only the VALUE it holds moved to the top of the block. *)
Lemma read_argv_ptr_k : forall segs inp mbase ph entry (sp : word) draw k,
  (k < length (in_argv inp))%nat ->
  (bv_unsigned sp
   + Z.of_nat (length (entry_stack_image inp mbase ph entry sp draw))
     < 2 ^ 64)%Z ->
  rdn segs (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw))
      (sp + nat_to_word (8 + 8 * k)) 8%nat
  = Some (word_le8 (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
                      (in_execfn inp) k)).
Proof.
  intros segs inp mbase ph entry sp draw k Hk Hnw.
  destruct (bsb_ptr_k inp mbase ph entry sp draw k Hk) as [post E].
  pose proof (read_at_offset_image segs inp mbase ph entry sp draw
    (word_le8 (len_word (in_argv inp))
      ++ flat_map word_le8
           (firstn k (fst (string_addrs
                             (cat_string_base (ed_top draw) (in_argv inp)
                                (in_envp inp) (in_execfn inp))
                             (in_argv inp)))))
    (word_le8 (nth k (fst (string_addrs
                             (cat_string_base (ed_top draw) (in_argv inp)
                                (in_envp inp) (in_execfn inp))
                             (in_argv inp))) (Z_to_bv 64 0)))
    post 8%nat E (length_n_to_le_8 _) Hnw) as H'.
  assert (Hlen : length (word_le8 (len_word (in_argv inp))
      ++ flat_map word_le8
           (firstn k (fst (string_addrs
                             (cat_string_base (ed_top draw) (in_argv inp)
                                (in_envp inp) (in_execfn inp))
                             (in_argv inp)))))
    = (8 + 8 * k)%nat).
  { rewrite length_app, length_n_to_le_8, length_flat_map_le8, firstn_length_le;
      [reflexivity | rewrite length_string_addrs_fst; lia]. }
  rewrite Hlen in H'.
  rewrite H'. unfold cat_argv_ptr. reflexivity.
Qed.

(** image = <head and pad> ++ argv strings ++ <tail>. *)
Lemma bsb_strings_split : forall inp mbase ph entry (sp : word) draw, exists tail,
  entry_stack_image inp mbase ph entry sp draw
  = cat_block_head (launch_auxv inp sp mbase) ph entry sp (ed_top draw)
      (in_argv inp) (in_envp inp) (in_execfn inp)
      (in_uid inp) (in_gid inp) (in_hwcap inp) draw
    ++ flatten_strings (in_argv inp) ++ tail.
Proof.
  intros inp mbase ph entry sp draw.
  rewrite entry_stack_image_block, build_stack_bytes_split_random.
  unfold cat_block_head, block_above_random.
  eexists. rewrite <- !app_assoc. reflexivity.
Qed.

(** image = <pre> ++ (argv[k] ++ [0]) ++ <post>, with [length pre]
    known.  [length pre] now carries the pad, so a caller that wants an
    ADDRESS out of it needs the launch conjunct
    ([cat_string_base_offset]). *)
Lemma bsb_byte_k : forall inp mbase ph entry (sp : word) draw k,
  (k < length (in_argv inp))%nat -> exists pre post,
  entry_stack_image inp mbase ph entry sp draw
  = pre ++ (nth k (in_argv inp) [] ++ [Z_to_bv 8 0]) ++ post
  /\ length pre
     = (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top draw)
          (in_argv inp) (in_envp inp) (in_execfn inp)
        + total_arg_bytes_nat (firstn k (in_argv inp)))%nat.
Proof.
  intros inp mbase ph entry sp draw k Hk.
  destruct (bsb_strings_split inp mbase ph entry sp draw) as [tail E].
  rewrite (flatten_strings_decomp (in_argv inp) k Hk) in E.
  exists (cat_block_head (launch_auxv inp sp mbase) ph entry sp (ed_top draw)
            (in_argv inp) (in_envp inp) (in_execfn inp)
            (in_uid inp) (in_gid inp) (in_hwcap inp) draw
          ++ flatten_strings (firstn k (in_argv inp))).
  eexists.
  split.
  - rewrite E. rewrite <- !app_assoc. reflexivity.
  - rewrite length_app, length_cat_block_head, length_flatten_strings.
    reflexivity.
Qed.

Lemma read_argv_byte_k :
  forall v segs inp mbase ph entry (sp brk : word) draw k j,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (k < length (in_argv inp))%nat ->
  (j <= length (nth k (in_argv inp) []))%nat ->
  rdn segs (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw))
      (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) k
       + nat_to_word j) 1%nat
  = Some [nth j (nth k (in_argv inp) [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)].
Proof.
  intros v segs inp mbase ph entry sp brk draw k j Hlaunch Hk Hj.
  pose proof (entry_stack_image_no_wrap v inp mbase ph entry sp brk draw Hlaunch)
    as Hnw.
  destruct (bsb_byte_k inp mbase ph entry sp draw k Hk) as [pre [post [E Hlen]]].
  pose proof (read_byte_at_image segs inp mbase ph entry sp draw
    pre (nth k (in_argv inp) [] ++ [Z_to_bv 8 0]) post j E) as H'.
  rewrite Hlen in H'.
  replace (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
             (in_execfn inp) k + nat_to_word j)
    with (sp + nat_to_word
                 (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top draw)
                    (in_argv inp) (in_envp inp) (in_execfn inp)
                  + total_arg_bytes_nat (firstn k (in_argv inp)) + j)).
  2:{ rewrite (cat_argv_ptr_offset _ _ _ _ k Hk),
        (cat_string_base_offset v inp mbase sp brk draw Hlaunch).
      rewrite !nat_to_word_add_merge. f_equal. f_equal. lia. }
  apply H'; [rewrite length_app; cbn [length]; lia | exact Hnw].
Qed.

Lemma read_argv_str_k :
  forall v segs inp mbase ph entry (sp brk : word) draw k,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (k < length (in_argv inp))%nat ->
  rdn segs (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw))
      (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) k)
      (length (nth k (in_argv inp) []))
  = Some (nth k (in_argv inp) []).
Proof.
  intros v segs inp mbase ph entry sp brk draw k Hlaunch Hk.
  pose proof (entry_stack_image_no_wrap v inp mbase ph entry sp brk draw Hlaunch)
    as Hnw.
  destruct (bsb_byte_k inp mbase ph entry sp draw k Hk) as [pre [post [E Hlen]]].
  pose proof (read_at_offset_image segs inp mbase ph entry sp draw
    pre (nth k (in_argv inp) []) ([Z_to_bv 8 0] ++ post)
    (length (nth k (in_argv inp) []))) as H.
  rewrite Hlen in H.
  replace (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
             (in_execfn inp) k)
    with (sp + nat_to_word
                 (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top draw)
                    (in_argv inp) (in_envp inp) (in_execfn inp)
                  + total_arg_bytes_nat (firstn k (in_argv inp)))).
  2:{ rewrite (cat_argv_ptr_offset _ _ _ _ k Hk),
        (cat_string_base_offset v inp mbase sp brk draw Hlaunch).
      rewrite nat_to_word_add_merge. reflexivity. }
  apply H; [ | reflexivity | exact Hnw].
  rewrite E. rewrite <- !app_assoc. reflexivity.
Qed.

(* ================================================================= *)
(* (E.5) [byte_at] unpacking and [valid_argv] projections             *)
(*                                                                    *)
(* [byte_at s k] is the NUL-padded k-th byte of [s] (the byte an argv  *)
(* string reads back as at offset [k], including the implicit         *)
(* terminating NUL at [k = length s]).  Every example that walks an    *)
(* argv string byte-by-byte defined this identically; centralized     *)
(* here next to the argv layout theory it decomposes.                 *)
(* ================================================================= *)

Definition byte_at (s : list byte) (k : nat) : byte :=
  nth k (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0).

Lemma nth_lt_byte_at : forall s j, (j < length s)%nat ->
  byte_at s j = nth j s (Z_to_bv 8 0).
Proof. intros s j Hj. unfold byte_at. apply app_nth1. exact Hj. Qed.

Lemma byte_at_len : forall s, byte_at s (length s) = Z_to_bv 8 0.
Proof.
  intros s. unfold byte_at. rewrite app_nth2 by lia.
  rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma byte_at_nz : forall s j, ~ In (Z_to_bv 8 0) s -> (j < length s)%nat ->
  byte_at s j <> Z_to_bv 8 0.
Proof.
  intros s j Hnz Hj Hc.
  apply Hnz. rewrite <- Hc. rewrite nth_lt_byte_at by exact Hj.
  apply nth_In. exact Hj.
Qed.

(** Bytes are typed, so the bound holds hypothesis-free. *)
Lemma byte_at_bound : forall s j, (bv_unsigned (byte_at s j) < 256)%Z.
Proof. intros s j. unfold byte_at. apply nth_app0_bound. Qed.

Lemma valid_argv_len : forall av, valid_argv av ->
  (Z.of_nat (length av) <= 1024)%Z.
Proof. intros av [Hlen _]. lia. Qed.

Lemma valid_argv_nonempty : forall av, valid_argv av -> (1 <= length av)%nat.
Proof. intros av [Hlen _]. lia. Qed.

Lemma valid_argv_str_len : forall av k, valid_argv av -> (k < length av)%nat ->
  (Z.of_nat (length (nth k av [])) <= 131071)%Z.
Proof.
  intros av k [_ [_ [Hstr _]]] Hk.
  rewrite Forall_forall in Hstr.
  specialize (Hstr _ (nth_In av [] Hk)). exact Hstr.
Qed.

Lemma valid_argv_str_nz : forall av k, valid_argv av -> (k < length av)%nat ->
  ~ In (Z_to_bv 8 0) (nth k av []).
Proof.
  intros av k [_ [_ [_ [Hnz _]]]] Hk.
  rewrite Forall_forall in Hnz. apply Hnz. apply nth_In. exact Hk.
Qed.

(** The fifth [valid_argv] clause, delivered in the shape
    [Sys.Fs.Open]'s arms ask for.

    THE INDEX IS [S k] BECAUSE THE CLAUSE IS ON THE TAIL: argv[0]
    conventionally holds a path, so [Run.valid_argv] says nothing about
    it and this lemma cannot either.  Both callers open [nth 1] and
    [nth 2], which is why the tail is enough.

    The [dot_path] side is NOT supplied here: "." is a path the model
    resolves, so whether an argument is "." is a case the caller splits
    on rather than a validity question — which is exactly how
    [Examples.cp_ns] and [Examples.headcp_ns] reach this lemma, with the
    false branch of their own split in hand. *)
Lemma valid_argv_str_plain : forall av k, valid_argv av ->
  (S k < length av)%nat ->
  path_eqb (nth (S k) av []) dot_path = false ->
  openat_plain_name (nth (S k) av []) = true.
Proof.
  intros av k [_ [_ [_ [_ Hpl]]]] Hk Hdot.
  assert (Hnth : nth (S k) av [] = nth k (tl av) []).
  { destruct av as [|a av']; [cbn in Hk; lia | reflexivity]. }
  assert (Hk' : (k < length (tl av))%nat).
  { destruct av as [|a av']; cbn in *; lia. }
  rewrite Forall_forall in Hpl.
  destruct (Hpl _ (nth_In (tl av) [] Hk')) as [Hsl Hdd].
  rewrite Hnth in Hdot |- *.
  unfold openat_plain_name, path_is_dirref.
  rewrite Hdot, Hsl, Hdd. reflexivity.
Qed.

(** Trivial since bytes are typed; kept as the restatement so
    downstream call sites survive. *)
Lemma valid_argv_str_bytes : forall av k, valid_argv av -> (k < length av)%nat ->
  Forall (fun b : byte => (bv_unsigned b < 256)%Z) (nth k av []).
Proof.
  intros av k _ _. apply Forall_forall. intros b _. apply u8_range.
Qed.

(* ================================================================= *)
(* (F) Extra value facts used by the target binary                    *)
(* ================================================================= *)

(** Hypothesis-free: the wrap in [Z_to_bv] cancels.  [x + 1] is the
    wrapping [bv] add, convertible with [v_addi x 1]. *)
Lemma v_addi_pred : forall x : word, v_addi (x + 1) (-1) = x.
Proof.
  intro x. apply bv_eq. unfold v_addi.
  rewrite Z_to_bv_unsigned, bv_add_unsigned.
  change (bv_unsigned (1 : word)) with 1%Z.
  rewrite bv_wrap_add_idemp_l.
  replace (bv_unsigned x + 1 + -1)%Z with (bv_unsigned x) by lia.
  apply bv_wrap_bv_unsigned.
Qed.

(* ================================================================= *)
(* (G) Ergonomic [to_wexit] constructors                             *)
(*                                                                   *)
(* A plain run of instructions is an [msteps] (chained from             *)
(* [PropExec.step_*] via [CatSim.msteps_to_wexit]); a write is           *)
(* [tw_write] with its post-svc register file collapsed by [adv_set];   *)
(* a code-0 exit is [tw_exit0].                                        *)
(* ================================================================= *)

(** The pending state a write/exit syscall dispatches from. *)
Definition pend (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte)
    : machine_state :=
  {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := Some (Z_to_bv 64 64);
     ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}.

(** Collapse [advance_past_svc (set_gpr0 <record> v)] to a [mkst]: advance the
    PC past the svc after writing the (dead) syscall return to x10. *)
Lemma adv_set : forall regs pc sv mem rom v,
  advance_past_svc (set_gpr0
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv; ms_resv := None; ms_fcsr := fp_csr;
       ms_mem := mem; ms_rom := rom |} v)
  = mkst (regupd regs 10 v) (v_addi pc 4) mem rom.
Proof.
  intros regs pc sv mem rom v.
  unfold advance_past_svc, set_gpr0, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.

(** A write to fd 1 at a [pend] state, continuing with the post-svc state.
    The environment may deliver any nonempty prefix of [buf], so the
    continuation is the delivered-length family: x10 holds
    [len_word (firstn n buf)] for the chosen [n]. *)
Lemma tw_write_gen : forall segs regs pc mem rom buf bufs code,
  ms_gpr (pend regs pc mem rom) 0 = Z_to_bv 64 1 ->
  ms_read_bytes (pend regs pc mem rom)
    (ms_gpr (pend regs pc mem rom) 1) (ms_gpr (pend regs pc mem rom) 2) = Some buf ->
  (* the range [vfs_write]'s [access_ok] accepts; see [CatSim.write1_check_n] *)
  access_okb (ms_gpr (pend regs pc mem rom) 1)
    (bv_unsigned (ms_gpr (pend regs pc mem rom) 2)) = true ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     to_wexit segs (mkst (regupd regs 10 (len_word (firstn n buf)))
                         (v_addi pc 4) mem rom) bufs code) ->
  to_wexit segs (pend regs pc mem rom) (buf :: bufs) code.
Proof.
  intros segs regs pc mem rom buf bufs code Hg0 Hr Hok Hnb Hcont.
  eapply tw_write;
    [reflexivity | reflexivity | exact Hg0 | exact Hr | exact Hok | exact Hnb | ].
  intros n Hn1 Hn2. unfold pend. rewrite adv_set. apply Hcont; assumption.
Qed.

(** A code-0 exit: the pending state carries an exit syscall number and a0 = 0. *)
Lemma tw_exit0 : forall segs ms x8,
  ms_svc_pending ms = Some x8 -> is_exit_no x8 ->
  ms_gpr ms 0 = Z_to_bv 64 0 ->
  to_wexit segs ms [] (Z_to_bv 64 0).
Proof.
  intros segs ms x8 Hsvc Hex Hg0.
  assert (Hc : bv_and (ms_gpr ms 0) (Z_to_bv 64 255) = Z_to_bv 64 0).
  { rewrite Hg0. apply bv_eq.
    rewrite bv_and_unsigned, !Z_to_bv_unsigned. reflexivity. }
  rewrite <- Hc. eapply tw_exit; eassumption.
Qed.

(** A write at the raw ecall post-state record (svc field is [Some (getr regs
    17)], as [step_ecall] leaves it).  [reg_get regs 10/11/12] are a0/a1/a2.
    The syscall-number test is Z-characterized, mirroring [tw_write]. *)
Lemma tw_write_rec : forall segs regs pc mem rom buf bufs code,
  bv_unsigned (getr regs 17) = 64%Z ->
  reg_get regs 10 = Z_to_bv 64 1 ->
  ms_read_bytes {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                   ms_mem := mem; ms_rom := rom |}
    (reg_get regs 11) (reg_get regs 12) = Some buf ->
  access_okb (reg_get regs 11) (bv_unsigned (reg_get regs 12)) = true ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     to_wexit segs (mkst (regupd regs 10 (len_word (firstn n buf)))
                         (v_addi pc 4) mem rom) bufs code) ->
  to_wexit segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                   ms_mem := mem; ms_rom := rom |}
    (buf :: bufs) code.
Proof.
  intros segs regs pc mem rom buf bufs code H17 H10 Hr Hok Hnb Hcont.
  eapply tw_write.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_0. exact H10.
  - unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_1, arg_reg_2. exact Hr.
  - unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_1, arg_reg_2. exact Hok.
  - exact Hnb.
  - intros n Hn1 Hn2. rewrite adv_set. apply Hcont; assumption.
Qed.

(** A code-0 exit at the raw ecall post-state record ([a7 = 93], a0 = 0). *)
Lemma tw_exit_rec : forall segs regs pc mem rom,
  bv_unsigned (getr regs 17) = 93%Z ->
  reg_get regs 10 = Z_to_bv 64 0 ->
  to_wexit segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                   ms_mem := mem; ms_rom := rom |} [] (Z_to_bv 64 0).
Proof.
  intros segs regs pc mem rom H17 H10.
  eapply tw_exit0.
  - cbn [ms_svc_pending]. reflexivity.
  - left. exact H17.
  - unfold ms_gpr. cbn [ms_regs].
    rewrite arg_reg_0. exact H10.
Qed.
End WithFP.
