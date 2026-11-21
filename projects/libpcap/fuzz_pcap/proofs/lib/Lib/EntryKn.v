(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the entry table rebuilt on the new entry stack image, over the launch input: the auxiliary vector's 27 pairs (29 with CONFIG_RSEQ), AT_RANDOM below the strings with their pad, the 6144512-byte stack window (was 8388608) and the stack_window_lo floor; its using attributes dropped; e_auxnull (the address of the vector's AT_NULL key, free of the CONFIG_RSEQ flag) and its lemma e_auxnull_eq added; split_lit_denot moved out of the section; and launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk StepTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require ArgvEnv__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefLayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.ArgvEnv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* PORT NOTE (LPS f1006fe8 -> 75d69e00).  Three things moved and this file
   is rebuilt on all three.

   1. The entry-image tuple.  [Run.entry_stack_image] takes
      [(inp, mb, ph, entry, sp, rnd)] and [StackLayout.build_stack_bytes]
      takes twelve arguments; argv, envp, the exec file name, uid, gid,
      hwcap and CONFIG_RSEQ are read off [inp].  This section adopts the
      tuple E2/Musl/InitMem.v's [Section Layout] already uses, verbatim.
      [Run.entry_stack_image_top] is DELETED at 75d69e00 -- the image IS
      the block -- so the old [bsb] / [SIMG] pair collapses to one list.

   2. The auxiliary vector.  [StackLayout.auxv_entries] (75d69e00
      StackLayout.v:229-263) is 27 pairs, 29 under CONFIG_RSEQ, in
      [create_elf_tables]' own order.  The AT_ TYPE CONSTANTS DID NOT
      MOVE; the SLOTS did.  AT_PHDR still carries type 3 and now sits at
      slot 13, AT_PHENT type 4 at slot 14, AT_PHNUM type 5 at slot 15,
      AT_HWCAP type 16 at slot 10, AT_PAGESZ type 6 at slot 11, AT_UID
      type 11 at slot 19, AT_EUID type 12 at slot 20, AT_SECURE type 23
      at slot 23, AT_RANDOM type 25 at slot 24, and AT_NULL type 0 at
      slot [26 + 2 * rseq] -- i.e. [auxv_count rseq - 1], which is left
      PARAMETRIC in [kb_rseq (in_kernel inp)].  Nothing below pins that
      flag: [Run.valid_input] leaves it free.

      [kn0] carries ALL 27/29 pairs, key AND value (rule 26i-WALK: a
      subset table leaves keys with no chunk and a model walk that reads
      every key stops one load early).

   3. The block's shape.  AT_RANDOM now sits BELOW the strings at
      [usp + C - 16], where [C = block_head_size rseq argv envp]
      (75d69e00 StackLayout.v:399), and the strings start at
      [usp + C + pad] with [pad = block_pad_len ...].  The old world's
      [W] -- the count of eight-byte words from argv[0]'s string up to
      the random block -- DOES NOT EXIST in the new layout, because the
      order of those two regions is reversed.  [V_W] is therefore
      replaced by [V_RNDOFF] (= C - 16, the model's own
      [at_random_ptr] offset) and a new [V_PAD] carries the
      [arch_align_stack] pad.  The literals 160 (ten auxv pairs), 184
      (= 160 + 24) and 200 are gone with it; every bound below comes
      from [Run.block_head_size_bounds] (75d69e00 Run.v:3889) and
      [StackLayout.length_build_stack_bytes] (75d69e00
      StackLayout.v:533), never from a named byte count.

   [PropExec.build_stack_bytes_within_span] is DELETED at 75d69e00
   (PropExec__Common.v:2443 records it); [usp_fit] is re-derived from
   [length_entry_stack_image_launch] and [valid_stack_top_va] instead.

   The [#[using=...]] attributes are dropped throughout, as
   Common/ArgvEnv__Common.v did at this revision: every one of them
   named section variables that no longer exist.  That changes these
   lemmas' argument lists. *)

Definition V_SP : nat := 0.
Definition V_ARGC : nat := 1.
Definition V_ENVC : nat := 2.
Definition V_L0 : nat := 3.
(* C - 16: [StackLayout.at_random_ptr]'s own offset above sp.  Replaces
   the pre-revision [V_W], which counted eight-byte words from the
   strings UP to the random block -- a direction the revision reverses. *)
Definition V_RNDOFF : nat := 4.
Definition V_UID : nat := 5.
Definition V_HW : nat := 6.
Definition V_PAD : nat := 7.
Definition V_GID : nat := 8.
Definition V_ENTRY : nat := 9.
Definition V_EXECFN : nat := 10.
Definition V_SYSINFO : nat := 11.
Definition V_MINSIG : nat := 12.
Definition V_L1IS : nat := 13.
Definition V_L1IG : nat := 14.
Definition V_L1DS : nat := 15.
Definition V_L1DG : nat := 16.
Definition V_L2S : nat := 17.
Definition V_L2G : nat := 18.
Definition V_L3S : nat := 19.
Definition V_L3G : nat := 20.
(* [Run.stack_window_lo (in_kernel inp) mb rnd] (75d69e00 Run.v:1379) and
   the length [sp - that].  The pre-revision [wrap_mem] floor was the
   literal [sp - stack_max_size]; at 75d69e00 the floor is
   [Z.max (ed_top - stack_max_size) (mbase + stack_guard_gap_bytes kb)],
   which sits AT OR ABOVE it, so the old zero/writable window of a flat
   8388608 bytes below sp is no longer a true claim.  Carried as values
   because neither branch of the [Z.max] is a function of the other
   slots. *)
Definition V_WLO : nat := 21.
Definition V_WLEN : nat := 22.
Definition NX0 : nat := 23.          (* [comment removed for export] *)
Definition K_ARGV0 : nat := 1.      (* [comment removed for export] *)
Definition K_RND : nat := 25.       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition eadd (a b : expr) : expr := mkAlu ALU_ADD a b.
Definition escale (c : Z) (e : expr) : expr := mkMd M_MUL (ELit c) e.
Definition eaddz (a : expr) (z : Z) : expr := mkAlu ALU_ADD a (ELit z).

Definition e_sp : expr := EVar V_SP.
(* the zero/writable window below sp, from [Run.stack_window_lo] *)
Definition e_wlo : expr := EVar V_WLO.
Definition e_envp : expr := eadd e_sp (eadd (escale 8 (EVar V_ARGC)) (ELit 16)).
(* 8 + 8*(argc+1) + 8*(envc+1): the pointer arrays did not move. *)
Definition e_auxv : expr := eadd e_envp (eadd (escale 8 (EVar V_ENVC)) (ELit 8)).
(* sp + (C - 16) -- [StackLayout.at_random_ptr sp rseq argv envp]. *)
Definition e_atrandom : expr := eadd e_sp (EVar V_RNDOFF).
(* the lowest string byte: the top of the random block plus the pad. *)
Definition e_str0 : expr := eaddz (eadd e_atrandom (EVar V_PAD)) 16.
Definition e_str1 : expr := eadd e_str0 (eaddz (EVar V_L0) 1).
(* [comment removed for export] *)
Definition e_argv1w : expr := EMd M_MUL (EAlu ALU_SLTU (ELit 1) (EVar V_ARGC)) e_str1.

Definition e_auxb : expr * Z := split_lit e_auxv.
Definition e_atrb : expr * Z := split_lit e_atrandom.
Definition e_strb : expr * Z := split_lit e_str0.
Definition auxw (i : Z) (ty : Z) (v : expr) : list kentry :=
  [KWord (SA (fst e_auxb) (snd e_auxb + 16 * i)) 8 (ELit ty); KWord (SA (fst e_auxb) (snd e_auxb + 16 * i + 8)) 8 v].

(* The entry table with CONFIG_RSEQ given as a closed flag [rs], so that a
   boot chain run by [vm_compute] can be built once per value of the flag.
   [kn0] below is [kn0_b] at [kb_rseq (in_kernel inp)]. *)
Definition kn_rseq_b (rs : bool) : list kentry :=
  if rs then auxw 26 27 (ELit 28) ++ auxw 27 28 (ELit 32) else [].
Definition kn_null_b (rs : bool) : list kentry :=
  auxw (Z.of_nat (auxv_count rs) - 1) 0 (ELit 0).
Definition kn0_b (rs : bool) (ph : PhdrInfo) (ilo ihi rwlo rwlen : Z) (kn_extra : list kentry) : list kentry :=
  [KRange (EVar V_SP) 0x7fff80000000 0x7fffffffff40; KAlign (EVar V_SP) 16;
   KRange (eaddz e_atrandom 16) 0x7fff800000c0 0x800000000000;
   KRange (EVar V_ARGC) 1 1024; KRange (EVar V_ENVC) 0 256; KRange (EVar V_L0) 0 131071;
   KRange (EVar V_RNDOFF) 464 10736; KRange (EVar V_PAD) 0 2101782;
   KRange (EVar V_UID) 0 0xFFFFFFFE;
   KWr (SA e_sp (-6144512)) (ELit 6144512); KZero (SA e_sp (-6144512)) (ELit 6144512);
   KWord (SA e_sp 0) 8 (EVar V_ARGC); KWord (SA e_sp 8) 8 e_str0; KWord (SA e_sp 16) 8 e_argv1w]
  ++ auxw 0  33 (EVar V_SYSINFO)
  ++ auxw 1  40 (EVar V_L1IS) ++ auxw 2  41 (EVar V_L1IG)
  ++ auxw 3  42 (EVar V_L1DS) ++ auxw 4  43 (EVar V_L1DG)
  ++ auxw 5  44 (EVar V_L2S)  ++ auxw 6  45 (EVar V_L2G)
  ++ auxw 7  46 (EVar V_L3S)  ++ auxw 8  47 (EVar V_L3G)
  ++ auxw 9  51 (EVar V_MINSIG)
  ++ auxw 10 16 (EVar V_HW)
  ++ auxw 11 6  (ELit 4096)
  ++ auxw 12 17 (ELit 100)
  ++ auxw 13 3  (ELit (Z.of_N (ph_addr ph)))
  ++ auxw 14 4  (ELit (Z.of_N (ph_ent ph)))
  ++ auxw 15 5  (ELit (Z.of_N (ph_num ph)))
  ++ auxw 16 7  (ELit 0)
  ++ auxw 17 8  (ELit 0)
  ++ auxw 18 9  (EVar V_ENTRY)
  ++ auxw 19 11 (EVar V_UID) ++ auxw 20 12 (EVar V_UID)
  ++ auxw 21 13 (EVar V_GID) ++ auxw 22 14 (EVar V_GID)
  ++ auxw 23 23 (ELit 0)
  ++ auxw 24 25 e_atrandom
  ++ auxw 25 31 (EVar V_EXECFN)
  ++ kn_rseq_b rs
  ++ kn_null_b rs
  ++ [KBlob (SA (fst e_atrb) (snd e_atrb)) (ELit 16) K_RND;
      KBlob (SA (fst e_strb) (snd e_strb)) (eaddz (EVar V_L0) 1) K_ARGV0;
      KImg ilo ihi; KWr (SA (ELit 0) rwlo) (ELit rwlen)]
  ++ kn_extra.

(* The address of the vector's AT_NULL key, [sp + 8 argc + 8 envc + 24 + 16 (auxv_count rs - 1)],
   written without the CONFIG_RSEQ flag: [V_RNDOFF] = C - 16 already counts the vector's
   [16 * auxv_count rs] bytes, and the zero gap between the vector and the random bytes is
   [8 * ((argc + envc + 3) mod 2)] ([StackLayout.block_head_size]).  A walk over the vector ends
   with its pointer here under either value of the flag, so the two per-flag boot chains can meet
   on this one expression. *)
Definition e_auxnull : expr :=
  EAlu ALU_SUB (EAlu ALU_ADD (EVar V_SP) (EVar V_RNDOFF))
    (EAlu ALU_ADD (ELit 16)
       (EMd M_MUL (ELit 8) (EMd M_REMU (EAlu ALU_ADD (EAlu ALU_ADD (EVar V_ARGC) (EVar V_ENVC)) (ELit 1)) (ELit 2)))).

Lemma e_auxnull_eq : forall (E : env) (inp : ProcInput) (sp : word) (k : Z),
  ev E V_SP = sp ->
  ev E V_ARGC = Z_to_bv 64 (Z.of_nat (length (in_argv inp))) ->
  ev E V_ENVC = Z_to_bv 64 (Z.of_nat (length (in_envp inp))) ->
  ev E V_RNDOFF = Z_to_bv 64 (Z.of_nat (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)) - 16) ->
  bv_unsigned sp <= 2 ^ 47 -> (length (in_argv inp) <= 1024)%nat -> (length (in_envp inp) <= 256)%nat ->
  k = 24 + 16 * (Z.of_nat (auxv_count (kb_rseq (in_kernel inp))) - 1) ->
  edenot E e_auxnull
  = edenot E (EAlu ALU_ADD (EAlu ALU_ADD (EVar V_SP) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar V_ARGC)) (EMd M_MUL (ELit 8) (EVar V_ENVC)))) (ELit k)).
Proof.
  intros E inp sp k H0 H1 H2 H4 Hsp Ha Hv Hk.
  pose proof (bv_unsigned_in_range 64 sp) as HS. change (bv_modulus 64) with (2 ^ 64) in HS.
  set (A := Z.of_nat (length (in_argv inp))) in *. set (V := Z.of_nat (length (in_envp inp))) in *.
  set (N := Z.of_nat (auxv_count (kb_rseq (in_kernel inp)))) in *.
  assert (HA : 0 <= A <= 1024) by (unfold A; lia). assert (HV : 0 <= V <= 256) by (unfold V; lia).
  assert (HN : 27 <= N <= 29) by (unfold N, auxv_count; destruct (kb_rseq (in_kernel inp)); lia).
  assert (HC : Z.of_nat (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))
               = 8 * (A + V + 3) + 16 * N + 8 * ((A + V + 3) mod 2) + 16).
  { unfold block_head_size, block_items, auxv_size. cbv zeta. unfold A, V, N. lia. }
  assert (HR : 0 <= (A + V + 3) mod 2 < 2) by (apply Z.mod_pos_bound; lia).
  apply bv_eq. unfold e_auxnull. cbn [edenot].
  rewrite H0, H1, H2, H4.
  rewrite u_sub64, !u_add64, !u_mul64.
  rewrite u_remu64 by (rewrite u64_lit by lia; lia).
  rewrite !u_add64.
  rewrite !u64_lit by lia.
  rewrite HC. lia.
Qed.

(* Outside the section: inside it, [lia] reifies the section's Let-bound lengths and hypotheses and
   the lemma would take them as arguments. *)
Lemma split_lit_denot : forall E e b k, split_lit e = (b, k) ->
  edenot E e = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
Proof.
  intros E e b k H.
  assert (G : forall e' : expr, edenot E e' = Z_to_bv 64 (bv_unsigned (edenot E e') + 0)).
  { intros e'. rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
  unfold split_lit in H.
  destruct e; try (injection H as <- <-; apply G).
  - injection H as <- <-. cbn [edenot]. rewrite u64_lit by lia. rewrite Z.add_0_l. reflexivity.
  - lazymatch type of H with (match ?o with _ => _ end = _) => destruct o end; try (injection H as <- <-; apply G).
    lazymatch type of H with (match ?y with _ => _ end = _) => destruct y end; try (injection H as <- <-; apply G).
    injection H as <- <-. cbn [edenot]. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Z.add_mod_idemp_r by lia. reflexivity.
Qed.

Section Entry.
  Variable segs : list Segment.
  Variable vsz : VaSize.
  Variable inp : ProcInput.
  Variable mb : word.
  Variable ph : PhdrInfo.
  Variable entry : word.
  Variable sp brk : word.
  Variable rnd : EntryDraw.
  (* [comment removed for export] *)
  Variables ilo ihi rwlo rwlen : Z.
  Hypothesis Hhull : 0 <= ilo <= ihi /\ ihi <= 2 ^ 32.
  Hypothesis Hrw : (0 <= rwlo /\ 0 <= rwlen /\ rwlo + rwlen < 2 ^ 64)
                   /\ forall m (x : word), rwlo <= bv_unsigned x < rwlo + rwlen -> wview segs m x <> None.
  (* [comment removed for export] *)
  Variable kn_extra : list kentry.

  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va vsz (mkEntry sp brk mb rnd) inp.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Huid : valid_id (in_uid inp).
  (* The window floor is at or below [sp - 6144512]: [StoreOk.stack_window_lo_valid] gives
     [wlo <= usp + stack_window_reach - stack_max_size] = [usp - 6144513] from [valid_launch]
     and [entry_launch_ok_va Sv48]; this section is generic in [vsz], so its callers prove
     it from that lemma (A3/Boot1.v [Hwlo_sp]).  The OTHER direction,
     [usp - stack_max_size <= wlo], needs no premise and is [wlo_lo] below. *)
  Hypothesis Hwlo : (stack_window_lo (in_kernel inp) mb rnd <= bv_unsigned sp - 6144512)%Z.

  (* The entry-image tuple, exactly E2/Musl/InitMem.v's [Section Layout]. *)
  Let bsb := entry_stack_image inp mb ph entry sp rnd.
  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length (in_argv inp)).
  Let envc := Z.of_nat (length (in_envp inp)).
  Let s0 := nth 0 (in_argv inp) [].
  Let L0 := Z.of_nat (length s0).
  (* C, PAD and STRL: the three lengths the block is made of. *)
  Let C := Z.of_nat (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)).
  Let RND := (C - 16)%Z.
  Let PAD := Z.of_nat (block_pad_len (kb_rseq (in_kernel inp)) sp (ed_top rnd)
                         (in_argv inp) (in_envp inp) (in_execfn inp)).
  Let STRL := Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp)).

  Definition M0 : word -> option byte := wrap_mem inp mb ph entry sp rnd.
  Definition R0 : bvmap 5 word := regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp.

  Definition vals0 : list word :=
    [sp; Z_to_bv 64 argc; Z_to_bv 64 envc; Z_to_bv 64 L0; Z_to_bv 64 RND;
     in_uid inp; in_hwcap inp; Z_to_bv 64 PAD; in_gid inp; entry;
     at_execfn_ptr (ed_top rnd) (in_execfn inp);
     la_sysinfo_ehdr (launch_auxv inp sp mb);
     la_minsigstksz (launch_auxv inp sp mb);
     cw_l1i_size (la_cache (launch_auxv inp sp mb));
     cw_l1i_geom (la_cache (launch_auxv inp sp mb));
     cw_l1d_size (la_cache (launch_auxv inp sp mb));
     cw_l1d_geom (la_cache (launch_auxv inp sp mb));
     cw_l2_size  (la_cache (launch_auxv inp sp mb));
     cw_l2_geom  (la_cache (launch_auxv inp sp mb));
     cw_l3_size  (la_cache (launch_auxv inp sp mb));
     cw_l3_geom  (la_cache (launch_auxv inp sp mb));
     Z_to_bv 64 (stack_window_lo (in_kernel inp) mb rnd);
     Z_to_bv 64 (bv_unsigned sp - stack_window_lo (in_kernel inp) mb rnd)].
  Definition blobs0 (k : nat) : list byte :=
    if Nat.eqb k K_RND then at_random_bytes (ed_random rnd)
    else if Nat.eqb k K_ARGV0 then s0 ++ [Z_to_bv 8 0]
    else [].
  Definition E0 : env := Env (vals_ev vals0) blobs0.

  (* The CONFIG_RSEQ pair and the terminator.  The terminator's slot is
     [auxv_count rseq - 1] = [26 + 2*rseq], parametric in the flag. *)
  Definition kn_rseq : list kentry := kn_rseq_b (kb_rseq (in_kernel inp)).
  Definition kn_null : list kentry := kn_null_b (kb_rseq (in_kernel inp)).

  Definition kn0 : list kentry := kn0_b (kb_rseq (in_kernel inp)) ph ilo ihi rwlo rwlen kn_extra.

  (* [comment removed for export] *)
  Lemma Hlo' : (sp_window_lo <= bv_unsigned sp)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
  Lemma Hhi' : (bv_unsigned sp <= sp_window_hi)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
  Lemma Hal' : (bv_unsigned sp mod 16 = 0)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
  Lemma Hav0 : (0 < length (in_argv inp))%nat. Proof. destruct Hva as [[? ?] _]; lia. Qed.
  Lemma len_av : 1 <= argc <= 1024. Proof. unfold argc. destruct Hva as [H _]. lia. Qed.
  Lemma len_ev : 0 <= envc <= 256. Proof. unfold envc. destruct Hve as [H _]. lia. Qed.
  Lemma usp_lo : 0x7fff80000000 <= usp. Proof. pose proof Hlo'. unfold sp_window_lo in *. unfold usp. lia. Qed.

  (* ------------------------------------------------------------------ *)
  (* The block's length, from the model's own equation.  The pre-revision
     [stack_image_size] baked in an auxv of 160 bytes, ten pairs; that
     claim is unprovable at 75d69e00 and the definition is deleted rather
     than re-tuned. *)

  Lemma length_bsb_eq : Z.of_nat (length bsb) = C + PAD + STRL + 8.
  Proof.
    unfold bsb, entry_stack_image. rewrite length_build_stack_bytes.
    cbn [launch_auxv la_rseq]. unfold C, PAD, STRL. lia.
  Qed.

  Lemma bsb_ge :
    8 * (argc + envc) + 472 <= C
    /\ C <= 8 * (argc + envc) + 512
    /\ 0 <= PAD /\ 1 <= STRL
    /\ Z.of_nat (length bsb) = C + PAD + STRL + 8.
  Proof.
    pose proof length_bsb_eq as HL.
    pose proof (block_head_size_bounds (kb_rseq (in_kernel inp))
                  (in_argv inp) (in_envp inp)) as HC.
    assert (HS : 1 <= STRL) by (unfold STRL, launch_string_bytes; lia).
    assert (HP : 0 <= PAD) by (unfold PAD; lia).
    unfold C, argc, envc in *. lia.
  Qed.

  (* The pre-revision bound came from [build_stack_bytes_within_span],
     deleted at 75d69e00.  The image's length is now EXACTLY
     [top - sp] and [top] is capped by [valid_stack_top_va]. *)
  Lemma usp_fit : usp + Z.of_nat (length bsb) <= 2 ^ 47.
  Proof.
    unfold bsb.
    rewrite (length_entry_stack_image_launch vsz inp mb ph entry sp brk rnd Hlau).
    destruct Hlau as (Htop & _ & _).
    unfold valid_stack_top_va in Htop. destruct Htop as (_ & Htople & _).
    unfold usp. destruct vsz; cbn [va_stack_top] in Htople;
      unfold sv39_task_size, sp_window_hi in *; lia.
  Qed.

  Lemma bsb_len_hi : Z.of_nat (length bsb) <= 2101782.
  Proof. unfold bsb. exact (bsb_bound vsz inp mb ph entry sp brk rnd Hvl Hlau). Qed.

  Lemma RND_range : 464 <= RND <= 10736.
  Proof.
    pose proof bsb_ge as (B1 & B2 & _ & _ & _). pose proof len_av. pose proof len_ev.
    unfold RND. lia.
  Qed.

  Lemma PAD_range : 0 <= PAD <= 2101782.
  Proof.
    pose proof bsb_ge as (B1 & _ & B3 & B4 & B5). pose proof bsb_len_hi.
    pose proof len_av. pose proof len_ev. lia.
  Qed.

  Lemma L0_range : 0 <= L0 <= 131071.
  Proof. unfold L0, s0. pose proof (valid_argv_str_len (in_argv inp) 0 Hva Hav0). lia. Qed.

  Lemma usp_hi : usp + 192 <= 2 ^ 47.
  Proof.
    pose proof usp_fit. pose proof bsb_ge as (B1 & _ & B3 & B4 & B5).
    pose proof len_av. pose proof len_ev. lia.
  Qed.

  (* [StoreOk.stack_window_lo_ge_sp] re-derived locally and without the
     model's Sv48 pin: [stack_window_lo] is a [Z.max] whose left branch is
     [ed_top - stack_max_size], and [ed_top = usp + length bsb >= usp]. *)
  Lemma wlo_lo : usp - 8388608 <= stack_window_lo (in_kernel inp) mb rnd.
  Proof.
    pose proof (length_entry_stack_image_launch vsz inp mb ph entry sp brk rnd Hlau) as HT.
    pose proof (Nat2Z.is_nonneg (length (entry_stack_image inp mb ph entry sp rnd))).
    pose proof (Z.le_max_l (bv_unsigned (ed_top rnd) - stack_max_size)
                  (bv_unsigned mb + stack_guard_gap_bytes (in_kernel inp))) as HM.
    unfold stack_window_lo, stack_max_size, usp in *. lia.
  Qed.

  Lemma wlo_range : 0 <= stack_window_lo (in_kernel inp) mb rnd <= usp.
  Proof. pose proof usp_lo. pose proof wlo_lo. pose proof Hwlo. unfold usp in *. lia. Qed.

  Lemma wlen_range : 0 <= usp - stack_window_lo (in_kernel inp) mb rnd <= 8388608.
  Proof. pose proof wlo_lo. pose proof Hwlo. unfold usp in *. lia. Qed.

  (* The auxiliary vector sits inside the head, below the random block:
     [auxv_off + auxv_size + 16 <= C <= length bsb]. *)
  Lemma auxv_fits :
    (auxv_off (in_argv inp) (in_envp inp) + auxv_size (kb_rseq (in_kernel inp)) + 16
     <= length bsb)%nat.
  Proof.
    pose proof bsb_ge as (B1 & B2 & B3 & B4 & B5).
    unfold C in *. unfold auxv_off, block_head_size, block_items in *. lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  Definition uE (e : expr) : Z := bv_unsigned (edenot E0 e).

  Lemma uE0 :
    uE (EVar V_SP) = usp /\ uE (EVar V_ARGC) = argc /\ uE (EVar V_ENVC) = envc
    /\ uE (EVar V_L0) = L0 /\ uE (EVar V_RNDOFF) = RND /\ uE (EVar V_PAD) = PAD
    /\ uE (EVar V_UID) = bv_unsigned (in_uid inp)
    /\ uE (EVar V_HW) = bv_unsigned (in_hwcap inp)
    /\ uE (EVar V_WLO) = stack_window_lo (in_kernel inp) mb rnd
    /\ uE (EVar V_WLEN) = usp - stack_window_lo (in_kernel inp) mb rnd.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev.
    pose proof RND_range. pose proof PAD_range. pose proof L0_range.
    pose proof wlo_range. pose proof wlen_range.
    unfold uE. cbn [edenot E0 ev nth vals0 vals_ev
                    V_SP V_ARGC V_ENVC V_L0 V_RNDOFF V_PAD V_UID V_HW V_WLO V_WLEN].
    rewrite !u64_lit by lia. repeat split; reflexivity.
  Qed.

  Lemma edenot_sp : edenot E0 e_sp = sp. Proof. reflexivity. Qed.
  Lemma edenot_uid : edenot E0 (EVar V_UID) = in_uid inp. Proof. reflexivity. Qed.
  Lemma edenot_gid : edenot E0 (EVar V_GID) = in_gid inp. Proof. reflexivity. Qed.
  Lemma edenot_hw : edenot E0 (EVar V_HW) = in_hwcap inp. Proof. reflexivity. Qed.
  Lemma edenot_entry : edenot E0 (EVar V_ENTRY) = entry. Proof. reflexivity. Qed.
  Lemma edenot_execfn :
    edenot E0 (EVar V_EXECFN) = at_execfn_ptr (ed_top rnd) (in_execfn inp).
  Proof. reflexivity. Qed.
  Lemma edenot_sysinfo :
    edenot E0 (EVar V_SYSINFO) = la_sysinfo_ehdr (launch_auxv inp sp mb).
  Proof. reflexivity. Qed.
  Lemma edenot_minsig :
    edenot E0 (EVar V_MINSIG) = la_minsigstksz (launch_auxv inp sp mb).
  Proof. reflexivity. Qed.
  Lemma edenot_l1is :
    edenot E0 (EVar V_L1IS) = cw_l1i_size (la_cache (launch_auxv inp sp mb)).
  Proof. reflexivity. Qed.
  Lemma edenot_l1ig :
    edenot E0 (EVar V_L1IG) = cw_l1i_geom (la_cache (launch_auxv inp sp mb)).
  Proof. reflexivity. Qed.
  Lemma edenot_l1ds :
    edenot E0 (EVar V_L1DS) = cw_l1d_size (la_cache (launch_auxv inp sp mb)).
  Proof. reflexivity. Qed.
  Lemma edenot_l1dg :
    edenot E0 (EVar V_L1DG) = cw_l1d_geom (la_cache (launch_auxv inp sp mb)).
  Proof. reflexivity. Qed.
  Lemma edenot_l2s :
    edenot E0 (EVar V_L2S) = cw_l2_size (la_cache (launch_auxv inp sp mb)).
  Proof. reflexivity. Qed.
  Lemma edenot_l2g :
    edenot E0 (EVar V_L2G) = cw_l2_geom (la_cache (launch_auxv inp sp mb)).
  Proof. reflexivity. Qed.
  Lemma edenot_l3s :
    edenot E0 (EVar V_L3S) = cw_l3_size (la_cache (launch_auxv inp sp mb)).
  Proof. reflexivity. Qed.
  Lemma edenot_l3g :
    edenot E0 (EVar V_L3G) = cw_l3_geom (la_cache (launch_auxv inp sp mb)).
  Proof. reflexivity. Qed.

  Lemma u_e_envp : uE e_envp = usp + 8 * argc + 16.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. destruct uE0 as (U0 & U1 & _).
    unfold e_envp, e_sp, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U0, U1. rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_auxv : uE e_auxv = usp + 8 * argc + 8 * envc + 24.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. destruct uE0 as (_ & _ & U2 & _).
    pose proof u_e_envp as UE. unfold e_auxv, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite UE, U2. rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_atrandom : uE e_atrandom = usp + C - 16.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof RND_range.
    pose proof bsb_ge as (B1 & B2 & B3 & B4 & B5).
    destruct uE0 as (U0 & _ & _ & _ & U4 & _).
    unfold e_atrandom, e_sp, eadd, uE in *. rewrite !mkAlu_denot.
    rewrite !u_add64. rewrite U0, U4. rewrite !Z.mod_small by lia. unfold RND. lia.
  Qed.

  Lemma u_e_str0 : uE e_str0 = usp + C + PAD.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof RND_range. pose proof PAD_range.
    pose proof bsb_ge as (B1 & B2 & B3 & B4 & B5).
    destruct uE0 as (U0 & _ & _ & _ & U4 & U5 & _).
    unfold e_str0, e_atrandom, e_sp, eadd, eaddz, uE in *.
    rewrite !mkAlu_denot, !edenot_lit.
    rewrite !u_add64, !u64_lit by lia. rewrite U0, U4, U5.
    rewrite !Z.mod_small by lia. unfold RND. lia.
  Qed.

  Lemma u_e_str1 : uE e_str1 = usp + C + PAD + L0 + 1.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof PAD_range. pose proof L0_range.
    pose proof bsb_ge as (B1 & B2 & B3 & B4 & B5).
    destruct uE0 as (_ & _ & _ & U3 & _).
    pose proof u_e_str0 as US. unfold e_str1, eadd, eaddz, uE in *. rewrite !mkAlu_denot, !edenot_lit.
    rewrite !u_add64, !u64_lit by lia. rewrite US, U3. rewrite !Z.mod_small by lia. lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The zero window is [[stack_window_lo, sp)], NOT the pre-revision
     [[sp - 8388608, sp)]: at 75d69e00 the floor is at or above the old
     one (75d69e00 Run.v:1379) and the old claim is false on the gap. *)
  Lemma M0_below : forall a : word,
    stack_window_lo (in_kernel inp) mb rnd <= bv_unsigned a < usp ->
    M0 a = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha. unfold M0.
    assert (Hs : stack_to_mem sp (entry_stack_image inp mb ph entry sp rnd) a = None).
    { unfold stack_to_mem. replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; unfold usp in Ha; lia). reflexivity. }
    unfold wrap_mem. rewrite Hs.
    replace (Z.leb (stack_window_lo (in_kernel inp) mb rnd) (bv_unsigned a)) with true
      by (symmetry; apply Z.leb_le; lia).
    replace (Z.ltb (bv_unsigned a) (bv_unsigned sp)) with true by (symmetry; apply Z.ltb_lt; unfold usp in Ha; lia). reflexivity.
  Qed.

  Lemma M0_low : forall a : word, bv_unsigned a < stack_window_lo (in_kernel inp) mb rnd -> M0 a = None.
  Proof.
    intros a Ha. unfold M0. pose proof wlo_range.
    assert (Hs : stack_to_mem sp (entry_stack_image inp mb ph entry sp rnd) a = None).
    { unfold stack_to_mem. replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; unfold usp in *; lia). reflexivity. }
    unfold wrap_mem. rewrite Hs.
    replace (Z.leb (stack_window_lo (in_kernel inp) mb rnd) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  Qed.

  Lemma rdn_M0_stack : forall (a : word) n,
    usp <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
    rdn segs M0 a n = rdn segs (stack_to_mem sp bsb) a n.
  Proof.
    intros a n Ha Hn. unfold M0, bsb. apply rdn_wrap_stack_above; unfold usp in *; lia.
  Qed.

  Lemma firstn1_skipn_nth : forall (l : list byte) (i : nat) (d : byte),
    (i < length l)%nat -> firstn 1 (skipn i l) = [nth i l d].
  Proof.
    induction l as [|x l IH]; intros i d Hi; cbn in Hi; [lia|].
    destruct i as [|i]; cbn; [reflexivity|]. apply IH. lia.
  Qed.

  Lemma split_u : forall e b k, split_lit e = (b, k) -> 0 <= k -> k <= uE e ->
    bv_unsigned (edenot E0 b) + k = uE e.
  Proof.
    intros e b k Hs Hk Hle. unfold uE in *. rewrite (split_lit_denot E0 e b k Hs) in Hle |- *.
    pose proof (u64_range (edenot E0 b)) as Rb.
    rewrite Z_to_bv_unsigned in Hle |- *. unfold bv_wrap, bv_modulus in *. change (2 ^ Z.of_N 64) with (2 ^ 64) in *.
    destruct (Z_lt_le_dec (bv_unsigned (edenot E0 b) + k) (2 ^ 64)).
    - rewrite Z.mod_small by lia. reflexivity.
    - exfalso.
      assert ((bv_unsigned (edenot E0 b) + k) mod 2 ^ 64 = bv_unsigned (edenot E0 b) + k - 2 ^ 64).
      { replace (bv_unsigned (edenot E0 b) + k) with ((bv_unsigned (edenot E0 b) + k - 2 ^ 64) + 1 * 2 ^ 64) at 1 by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
      lia.
  Qed.

  Lemma adenot_SA : forall E b k, adenot E (SA b k) = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
  Proof. intros. unfold adenot, v_addi. cbn [a_base a_off]. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma kword_stack : forall b k ve (w : word),
    bv_unsigned (edenot E0 b) + k = bv_unsigned w ->
    usp <= bv_unsigned w -> bv_unsigned w + 8 <= usp + Z.of_nat (length bsb) ->
    rdn segs (stack_to_mem sp bsb) w 8%nat = Some (word_le8 (edenot E0 ve)) ->
    kentry_ok segs E0 M0 (KWord (SA b k) 8 ve).
  Proof.
    intros b k ve w Hw Hlo Hhi Hrd. pose proof usp_fit. pose proof usp_lo. pose proof (u64_range w).
    cbn [kentry_ok]. split; [lia|].
    assert (Hfl : flat E0 (SA b k) (Z.of_nat 8)) by (unfold flat, estart; cbn [a_base a_off]; change (Z.of_nat 8) with 8; lia).
    split; [exact Hfl|].
    rewrite adenot_SA. rewrite Hw, Z_to_bv_bv_unsigned.
    rewrite rdn_M0_stack; [| lia | change (Z.of_nat 8) with 8; lia].
    rewrite Hrd. rewrite n_to_le_8_spec. reflexivity.
  Qed.

  Lemma auxb_eq : split_lit e_auxv = (fst e_auxb, snd e_auxb).
  Proof. unfold e_auxb; destruct (split_lit e_auxv); reflexivity. Qed.
  Lemma auxk_eq : snd e_auxb = 24. Proof. vm_compute. reflexivity. Qed.

  (* ------------------------------------------------------------------ *)
  (* The walk over the vector.  [RefLayout.read_auxv_word] is the model's
     own read, and its bound is [2 * auxv_count rseq] -- 54 words, 58
     under CONFIG_RSEQ -- not the pre-revision 20.  These wrappers are
     stated with the section's own tuple and closed by [eapply]/
     [eassumption] so that no positional argument list is guessed. *)

  Lemma lay_read_auxv_word : forall j,
    (j < 2 * auxv_count (kb_rseq (in_kernel inp)))%nat ->
    rdn segs (stack_to_mem sp (entry_stack_image inp mb ph entry sp rnd))
      (sp + nat_to_word (auxv_off (in_argv inp) (in_envp inp) + 8 * j)) 8%nat
    = Some (word_le8
              (nth j (auxv_words (launch_auxv inp sp mb) ph entry
                        (in_uid inp) (in_gid inp) (in_hwcap inp)
                        (at_random_ptr sp (kb_rseq (in_kernel inp))
                           (in_argv inp) (in_envp inp))
                        (at_execfn_ptr (ed_top rnd) (in_execfn inp)))
                   (Z_to_bv 64 0))).
  Proof.
    intros j Hj. pose proof Hlo' as HL. pose proof Hhi' as HH.
    eapply read_auxv_word; try exact Hlau; eassumption.
  Qed.

  Lemma lay_read_argv_null :
    rdn segs (stack_to_mem sp (entry_stack_image inp mb ph entry sp rnd))
      (sp + nat_to_word (8 + 8 * length (in_argv inp))) 8%nat
    = Some (word_le8 (Z_to_bv 64 0)).
  Proof.
    pose proof Hlo' as HL. pose proof Hhi' as HH.
    eapply read_argv_null; try exact Hlau; eassumption.
  Qed.

  Lemma lay_at_random_off : exists off : nat,
    at_random_ptr sp (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)
    = (sp + nat_to_word off)%bv
    /\ off = (block_head_size (kb_rseq (in_kernel inp))
                (in_argv inp) (in_envp inp) - 16)%nat
    /\ (Z.of_nat off mod 8 = 0)%Z
    /\ forall j n, (j + n <= 16)%nat ->
         rdn segs (stack_to_mem sp (entry_stack_image inp mb ph entry sp rnd))
           (at_random_ptr sp (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)
            + nat_to_word j) n
         = Some (firstn n (skipn j (at_random_bytes (ed_random rnd)))).
  Proof.
    pose proof Hlo' as HL. pose proof Hhi' as HH.
    eapply at_random_off; try exact Hlau; eassumption.
  Qed.

  Lemma u_at_random_ptr :
    bv_unsigned (at_random_ptr sp (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))
    = usp + C - 16.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof bsb_ge as (B1 & B2 & B3 & B4 & B5).
    pose proof len_av. pose proof len_ev.
    unfold at_random_ptr. rewrite word_add_nat.
    rewrite (Nat2Z.inj_sub _ 16) by lia.
    change (Z.of_nat 16) with 16%Z.
    rewrite Z.add_sub_assoc.
    unfold usp, C in *. apply u64_lit. lia.
  Qed.

  Lemma atr_ptr_eq :
    at_random_ptr sp (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)
    = edenot E0 e_atrandom.
  Proof.
    apply bv_eq. rewrite u_at_random_ptr. pose proof u_e_atrandom as U.
    unfold uE in U. rewrite U. reflexivity.
  Qed.

  (* argv[k]'s string address, derived locally rather than through
     [RefLayout.u_cat_argv_ptr], so no argument list is guessed. *)
  Lemma u_cat_argv_ptr_k : forall k, (k < length (in_argv inp))%nat ->
    bv_unsigned (cat_argv_ptr (ed_top rnd) (in_argv inp) (in_envp inp) (in_execfn inp) k)
    = usp + C + PAD + Z.of_nat (total_arg_bytes_nat (firstn k (in_argv inp))).
  Proof.
    intros k Hk. pose proof usp_lo. pose proof usp_fit.
    pose proof bsb_ge as (B1 & B2 & B3 & B4 & B5).
    pose proof (total_arg_bytes_firstn_le k (in_argv inp)) as HF.
    pose proof (length_flatten_strings (in_argv inp)) as F1.
    pose proof (length_flatten_strings (in_envp inp)) as F2.
    rewrite (cat_argv_ptr_offset (ed_top rnd) (in_argv inp) (in_envp inp) (in_execfn inp) k Hk),
            (cat_string_base_offset vsz inp mb sp brk rnd Hlau).
    rewrite nat_to_word_add_merge, word_add_nat.
    unfold cat_string_off, C, PAD, STRL, usp, launch_string_bytes in *.
    rewrite !Nat2Z.inj_add.
    rewrite !Z.add_assoc.
    apply u64_lit. lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma auxv_word_ok : forall (j : nat) ve,
    (j < 2 * auxv_count (kb_rseq (in_kernel inp)))%nat ->
    nth j (auxv_words (launch_auxv inp sp mb) ph entry
             (in_uid inp) (in_gid inp) (in_hwcap inp)
             (at_random_ptr sp (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))
             (at_execfn_ptr (ed_top rnd) (in_execfn inp)))
        (Z_to_bv 64 0) = edenot E0 ve ->
    kentry_ok segs E0 M0 (KWord (SA (fst e_auxb) (snd e_auxb + 8 * Z.of_nat j)) 8 ve).
  Proof.
    intros j ve Hj Hv. pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof auxv_fits as AF. pose proof bsb_ge as (B1 & B2 & B3 & B4 & B5).
    assert (Hjs : (8 * j + 8 <= auxv_size (kb_rseq (in_kernel inp)))%nat)
      by (unfold auxv_size in *; lia).
    set (ab := fst e_auxb) in *. set (ak := snd e_auxb) in *.
    pose proof (split_u e_auxv ab ak auxb_eq) as Hs. rewrite u_e_auxv in Hs.
    pose proof auxk_eq as Hak. fold ak in Hak.
    specialize (Hs ltac:(lia) ltac:(lia)).
    apply (kword_stack ab (ak + 8 * Z.of_nat j) ve (sp + nat_to_word (auxv_off (in_argv inp) (in_envp inp) + 8 * j))%bv).
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; [|lia]. rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; [|lia]. rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - rewrite <- Hv. unfold bsb. exact (lay_read_auxv_word j Hj).
  Qed.

  Lemma auxw_ok : forall i ty ve,
    (0 <= i < Z.of_nat (auxv_count (kb_rseq (in_kernel inp)))) ->
    nth (Z.to_nat (2 * i))
        (auxv_words (launch_auxv inp sp mb) ph entry
           (in_uid inp) (in_gid inp) (in_hwcap inp)
           (at_random_ptr sp (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))
           (at_execfn_ptr (ed_top rnd) (in_execfn inp))) (Z_to_bv 64 0) = Z_to_bv 64 ty ->
    nth (Z.to_nat (2 * i + 1))
        (auxv_words (launch_auxv inp sp mb) ph entry
           (in_uid inp) (in_gid inp) (in_hwcap inp)
           (at_random_ptr sp (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))
           (at_execfn_ptr (ed_top rnd) (in_execfn inp))) (Z_to_bv 64 0) = edenot E0 ve ->
    know_ok segs E0 M0 (auxw i ty ve).
  Proof.
    intros i ty ve Hi H1 H2. unfold auxw.
    constructor; [|constructor; [|constructor]].
    - replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia.
      apply auxv_word_ok; [lia|]. rewrite H1. reflexivity.
    - replace (snd e_auxb + 16 * i + 8) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i + 1))) by lia.
      apply auxv_word_ok; [lia|]. exact H2.
  Qed.

  (* [auxv_words] is [flat_map] over [auxv_entries]; this is
     [RefLayout.auxv_words_eq] re-derived locally (its proof is
     [reflexivity]). *)
  Lemma aw_eq : forall ar ae,
    auxv_words (launch_auxv inp sp mb) ph entry (in_uid inp) (in_gid inp) (in_hwcap inp) ar ae
    = flat_map (fun e => [fst e; snd e])
        (auxv_entries (launch_auxv inp sp mb) ph entry
           (in_uid inp) (in_gid inp) (in_hwcap inp) ar ae).
  Proof. reflexivity. Qed.

  (* Slots 26..28 live past [auxv_entries]' [if la_rseq la], so they are
     read under a case split on the flag and never with it pinned. *)
  Lemma auxv_tail_true : kb_rseq (in_kernel inp) = true -> forall ar ae,
    nth 52 (auxv_words (launch_auxv inp sp mb) ph entry (in_uid inp) (in_gid inp) (in_hwcap inp) ar ae) (Z_to_bv 64 0) = Z_to_bv 64 27
    /\ nth 53 (auxv_words (launch_auxv inp sp mb) ph entry (in_uid inp) (in_gid inp) (in_hwcap inp) ar ae) (Z_to_bv 64 0) = Z_to_bv 64 28
    /\ nth 54 (auxv_words (launch_auxv inp sp mb) ph entry (in_uid inp) (in_gid inp) (in_hwcap inp) ar ae) (Z_to_bv 64 0) = Z_to_bv 64 28
    /\ nth 55 (auxv_words (launch_auxv inp sp mb) ph entry (in_uid inp) (in_gid inp) (in_hwcap inp) ar ae) (Z_to_bv 64 0) = Z_to_bv 64 32
    /\ nth 56 (auxv_words (launch_auxv inp sp mb) ph entry (in_uid inp) (in_gid inp) (in_hwcap inp) ar ae) (Z_to_bv 64 0) = Z_to_bv 64 0
    /\ nth 57 (auxv_words (launch_auxv inp sp mb) ph entry (in_uid inp) (in_gid inp) (in_hwcap inp) ar ae) (Z_to_bv 64 0) = Z_to_bv 64 0.
  Proof.
    intros Hr ar ae. unfold auxv_words, auxv_entries.
    cbn [launch_auxv la_rseq la_cache]. rewrite Hr.
    cbn [flat_map app fst snd nth
         AT_RSEQ_FEATURE_SIZE AT_RSEQ_ALIGN AT_NULL].
    repeat split; reflexivity.
  Qed.

  Lemma auxv_tail_false : kb_rseq (in_kernel inp) = false -> forall ar ae,
    nth 52 (auxv_words (launch_auxv inp sp mb) ph entry (in_uid inp) (in_gid inp) (in_hwcap inp) ar ae) (Z_to_bv 64 0) = Z_to_bv 64 0
    /\ nth 53 (auxv_words (launch_auxv inp sp mb) ph entry (in_uid inp) (in_gid inp) (in_hwcap inp) ar ae) (Z_to_bv 64 0) = Z_to_bv 64 0.
  Proof.
    intros Hr ar ae. unfold auxv_words, auxv_entries.
    cbn [launch_auxv la_rseq la_cache]. rewrite Hr.
    cbn [flat_map app fst snd nth AT_NULL].
    split; reflexivity.
  Qed.

  Lemma kn_rseq_ok : know_ok segs E0 M0 kn_rseq.
  Proof.
    unfold kn_rseq, kn_rseq_b. case_eq (kb_rseq (in_kernel inp)); intro Hr; [|apply Forall_nil].
    pose proof (auxv_tail_true Hr
                  (at_random_ptr sp (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))
                  (at_execfn_ptr (ed_top rnd) (in_execfn inp)))
      as (T0 & T1 & T2 & T3 & _ & _).
    apply Forall_app; split.
    - apply auxw_ok;
        [ rewrite Hr; cbn [auxv_count]; lia
        | replace (Z.to_nat (2 * 26)) with 52%nat by (vm_compute; reflexivity); exact T0
        | replace (Z.to_nat (2 * 26 + 1)) with 53%nat by (vm_compute; reflexivity);
          rewrite edenot_lit; exact T1 ].
    - apply auxw_ok;
        [ rewrite Hr; cbn [auxv_count]; lia
        | replace (Z.to_nat (2 * 27)) with 54%nat by (vm_compute; reflexivity); exact T2
        | replace (Z.to_nat (2 * 27 + 1)) with 55%nat by (vm_compute; reflexivity);
          rewrite edenot_lit; exact T3 ].
  Qed.

  (* 11c-HOIST-FINAL.  The flag here is [kb_rseq (in_kernel inp)] with
     [inp] an opaque Section VARIABLE, so conversion CANNOT bridge it to
     [true]/[false]: [exact] is no safer than [rewrite], and hoisting
     would not help.  Three consequences, all load-bearing:

     - [auxv_tail_true]/[auxv_tail_false] are instantiated at the
       UNSPECIALISED [at_random_ptr sp (kb_rseq (in_kernel inp)) ...],
       the spelling [auxw_ok]'s subgoals carry, so [exact Tn] matches
       SYNTACTICALLY and needs no conversion.  They are posed AFTER the
       split because they take [Hr]; nothing is rewritten with them.
     - the terminator index is normalised with [rewrite ?Hr] -- a no-op
       if the [destruct] already substituted, the rewrite if it did not
       -- then [cbn [auxv_count]], so the step does not depend on which
       spelling survives the split.
     - the [rewrite Hr] inside the bracket is the OTHER case: that
       subgoal is generated by [apply auxw_ok] after the split and still
       carries the unspecialised flag.

     This section binds no [Let rseq], but it DOES bind three [Let]s whose
     bodies name the flag -- [C], [RND] and [PAD] -- and a plain [destruct]
     must clear and re-introduce every one of them, which fails with
     "C is already used" (in [kn_rseq_ok]).
     So [case_eq] IS needed, in [kn_rseq_ok], in [kn_null_ok] and in the
     [auxv_count] side goal of [auxv_words_ok]: it cases the goal's own
     occurrence and leaves the context untouched, which is also what keeps
     the unspecialised spelling the three [exact Tn] steps match.  Do not
     tidy any of the three, and do not turn [case_eq] back into
     [destruct]. *)
  Lemma kn_null_ok : know_ok segs E0 M0 kn_null.
  Proof.
    unfold kn_null, kn_null_b. case_eq (kb_rseq (in_kernel inp)); intro Hr.
    - rewrite ?Hr. cbn [auxv_count].
      pose proof (auxv_tail_true Hr
                    (at_random_ptr sp (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))
                    (at_execfn_ptr (ed_top rnd) (in_execfn inp)))
        as (_ & _ & _ & _ & T4 & T5).
      apply auxw_ok;
        [ rewrite Hr; cbn [auxv_count]; lia
        | replace (Z.to_nat (2 * (Z.of_nat 29 - 1))) with 56%nat
            by (vm_compute; reflexivity); exact T4
        | replace (Z.to_nat (2 * (Z.of_nat 29 - 1) + 1)) with 57%nat
            by (vm_compute; reflexivity); rewrite edenot_lit; exact T5 ].
    - rewrite ?Hr. cbn [auxv_count].
      pose proof (auxv_tail_false Hr
                    (at_random_ptr sp (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))
                    (at_execfn_ptr (ed_top rnd) (in_execfn inp)))
        as (T0 & T1).
      apply auxw_ok;
        [ rewrite Hr; cbn [auxv_count]; lia
        | replace (Z.to_nat (2 * (Z.of_nat 27 - 1))) with 52%nat
            by (vm_compute; reflexivity); exact T0
        | replace (Z.to_nat (2 * (Z.of_nat 27 - 1) + 1)) with 53%nat
            by (vm_compute; reflexivity); rewrite edenot_lit; exact T1 ].
  Qed.

  (* ------------------------------------------------------------------ *)
  Lemma kr_ok : forall e lo hi, lo <= uE e <= hi -> kentry_ok segs E0 M0 (KRange e lo hi).
  Proof. intros e lo hi H. cbn [kentry_ok]. unfold uE in H. exact H. Qed.

  (* [[sp - 6144512, sp)], inside [[stack_window_lo, sp)], the window [wrap_mem] really
     zero-maps at the revision: the pre-revision entry's flat 8388608 bytes below sp is not a
     true claim of the revision's floor, the launch's 6144512 is ([Hwlo]). *)
  Lemma stack_window_ok :
    kentry_ok segs E0 M0 (KWr (SA e_sp (-6144512)) (ELit 6144512))
    /\ kentry_ok segs E0 M0 (KZero (SA e_sp (-6144512)) (ELit 6144512)).
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof wlo_range. pose proof Hwlo.
    assert (Hst : estart E0 (SA e_sp (-6144512)) = usp - 6144512).
    { unfold estart. cbn [a_base a_off]. rewrite edenot_sp. unfold usp in *. lia. }
    assert (Hl : elenZ E0 (ELit 6144512) = 6144512) by (unfold elenZ; rewrite edenot_lit, u64_lit; lia).
    assert (Hfl : flat E0 (SA e_sp (-6144512)) (elenZ E0 (ELit 6144512))).
    { unfold flat. rewrite Hst, Hl. unfold usp in *. lia. }
    split; cbn [kentry_ok]; (split; [exact Hfl|]); rewrite Hst, ?Hl.
    - intros d m Hd Hdm. apply store_ok_of_all; rewrite u_small by (unfold usp in *; lia); [lia|].
      intros x Hx. unfold wview. rewrite (M0_below x) by (unfold usp in *; lia). discriminate.
    - intros i Hi. apply M0_below. rewrite u_small by (unfold usp in *; lia). unfold usp in *. lia.
  Qed.

  Lemma argc_word_ok : kentry_ok segs E0 M0 (KWord (SA e_sp 0) 8 (EVar V_ARGC)).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof bsb_ge as (B1 & B2 & B3 & B4 & B5).
    apply (kword_stack e_sp 0 (EVar V_ARGC) sp).
    - rewrite edenot_sp. unfold usp. lia.
    - unfold usp. lia.
    - unfold usp in *. lia.
    - pose proof (read_argc inp mb ph entry segs sp rnd) as RW.
      assert (Hv : len_word (in_argv inp) = edenot E0 (EVar V_ARGC)).
      { apply bv_eq. destruct uE0 as (_ & U1 & _). unfold uE in U1. rewrite U1. unfold argc.
        eapply u_argcN; eassumption. }
      rewrite <- Hv. unfold bsb in *. apply RW. unfold usp in *. lia.
  Qed.

  Lemma argv0_word_ok : kentry_ok segs E0 M0 (KWord (SA e_sp 8) 8 e_str0).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof bsb_ge as (B1 & B2 & B3 & B4 & B5). pose proof PAD_range.
    apply (kword_stack e_sp 8 e_str0 (sp + nat_to_word (8 + 8 * 0))%bv).
    - rewrite edenot_sp. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - pose proof (read_argv_ptr_k segs inp mb ph entry sp rnd 0 Hav0) as RW.
      assert (Hv : cat_argv_ptr (ed_top rnd) (in_argv inp) (in_envp inp) (in_execfn inp) 0
                   = edenot E0 e_str0).
      { apply bv_eq. rewrite (u_cat_argv_ptr_k 0 Hav0).
        pose proof u_e_str0 as U. unfold uE in U. rewrite U.
        replace (total_arg_bytes_nat (firstn 0 (in_argv inp))) with 0%nat by reflexivity.
        lia. }
      rewrite <- Hv. unfold bsb in *. apply RW. unfold usp in *. lia.
  Qed.

  Lemma argv1_word_ok : kentry_ok segs E0 M0 (KWord (SA e_sp 16) 8 e_argv1w).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof bsb_ge as (B1 & B2 & B3 & B4 & B5). pose proof PAD_range.
    pose proof L0_range as HL0.
    assert (Hw1 : edenot E0 e_argv1w = if (1 <? argc) then edenot E0 e_str1 else Z_to_bv 64 0).
    { unfold e_argv1w. cbn [edenot]. destruct uE0 as (_ & U1 & _). unfold uE in U1. cbn [edenot] in U1.
      apply bv_eq. rewrite u_mul64, u_sltu64, u64_lit, U1 by lia.
      pose proof (u64_range (edenot E0 e_str1)).
      destruct (1 <? argc); [rewrite Z.mul_1_l, Z.mod_small by lia; reflexivity | rewrite u64_lit by lia; reflexivity]. }
    apply (kword_stack e_sp 16 e_argv1w (sp + nat_to_word (8 + 8 * 1))%bv).
    - rewrite edenot_sp. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite Hw1. destruct (1 <? argc) eqn:Hc.
      + apply Z.ltb_lt in Hc. assert (Hav1 : (1 < length (in_argv inp))%nat) by (unfold argc in Hc; lia).
        pose proof (read_argv_ptr_k segs inp mb ph entry sp rnd 1 Hav1) as RW.
        assert (Hv : cat_argv_ptr (ed_top rnd) (in_argv inp) (in_envp inp) (in_execfn inp) 1
                     = edenot E0 e_str1).
        { apply bv_eq. rewrite (u_cat_argv_ptr_k 1 Hav1).
          pose proof u_e_str1 as U. unfold uE in U. rewrite U.
          assert (TF : forall l : list (list byte), (0 < length l)%nat ->
                        Z.of_nat (total_arg_bytes_nat (firstn 1 l)) = Z.of_nat (length (nth 0 l [])) + 1)
            by (intros [|x t] Hl; [cbn in Hl; lia|]; change (firstn 1 (x :: t)) with [x]; cbn -[Z.of_nat Z.add]; lia).
          rewrite (TF (in_argv inp) Hav0). unfold L0, s0. lia. }
        rewrite <- Hv. unfold bsb in *. apply RW. unfold usp in *. lia.
      + apply Z.ltb_ge in Hc. assert (Hav1 : length (in_argv inp) = 1%nat) by (unfold argc in Hc; pose proof Hav0; lia).
        pose proof lay_read_argv_null as RW. rewrite Hav1 in RW.
        unfold bsb. exact RW.
  Qed.

  (* [comment removed for export] *)
  Lemma atrandom_ok : kentry_ok segs E0 M0 (KBlob (SA (fst e_atrb) (snd e_atrb)) (ELit 16) K_RND).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof bsb_ge as (B1 & B2 & B3 & B4 & B5).
    assert (Hab : split_lit e_atrandom = (fst e_atrb, snd e_atrb)) by (unfold e_atrb; destruct (split_lit e_atrandom); reflexivity).
    set (ab := fst e_atrb) in *. set (ak := snd e_atrb) in *.
    pose proof (split_u e_atrandom ab ak Hab) as Hs. rewrite u_e_atrandom in Hs.
    assert (Hak : ak = 0) by (subst ak; vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)).
    assert (Hst : estart E0 (SA ab ak) = usp + C - 16) by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (ELit 16) = 16) by (unfold elenZ; rewrite edenot_lit, u64_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl.
    assert (HE : eb E0 K_RND = at_random_bytes (ed_random rnd)) by reflexivity.
    rewrite HE.
    split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
    split; [rewrite length_at_random_bytes; reflexivity|].
    intros i Hi.
    destruct lay_at_random_off as [off (Hp & Hoff & Hmod & Hrd)].
    assert (Hu : bv_unsigned (at_random_ptr sp (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))
                 = usp + C - 16) by apply u_at_random_ptr.
    specialize (Hrd (Z.to_nat i) 1%nat ltac:(lia)).
    rewrite (firstn1_skipn_nth _ _ (Z_to_bv 8 0)) in Hrd by (rewrite length_at_random_bytes; lia).
    assert (Ha : (at_random_ptr sp (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)
                  + nat_to_word (Z.to_nat i))%bv = Z_to_bv 64 (usp + C - 16 + i)).
    { apply bv_eq. rewrite word_add_nat, Hu, u64_lit, u64_lit; unfold usp in *; lia. }
    rewrite Ha in Hrd.
    unfold M0. rewrite (wrap_above_sp inp mb ph entry sp rnd _) by (rewrite u64_lit; unfold usp in *; lia).
    cbn [rdn] in Hrd.
    destruct (stack_to_mem sp (entry_stack_image inp mb ph entry sp rnd)
                (Z_to_bv 64 (usp + C - 16 + i))) as [b|] eqn:Hstk.
    - cbn in Hrd. injection Hrd as ->. reflexivity.
    - exfalso. unfold stack_to_mem in Hstk. rewrite u64_lit in Hstk by (unfold usp in *; lia).
      replace (bv_unsigned sp <=? usp + C - 16 + i) with true in Hstk by (symmetry; apply Z.leb_le; unfold usp; lia).
      cbv zeta in Hstk.
      replace (usp + C - 16 + i - bv_unsigned sp
               <? Z.of_nat (length (entry_stack_image inp mb ph entry sp rnd))) with true in Hstk
        by (symmetry; apply Z.ltb_lt; unfold bsb in *; unfold usp in *; lia).
      apply nth_error_None in Hstk. unfold bsb in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma argv0_end_le : usp + C + PAD + L0 + 1 <= usp + Z.of_nat (length bsb).
  Proof.
    destruct (bsb_byte_k inp mb ph entry sp rnd 0 Hav0) as [pre [post [E Hlen]]].
    pose proof (f_equal (@length byte) E) as HL. rewrite !length_app in HL. cbn [length] in HL.
    fold bsb in HL. rewrite Hlen in HL. unfold cat_string_off in HL.
    replace (total_arg_bytes_nat (firstn 0 (in_argv inp))) with 0%nat in HL by reflexivity.
    fold s0 in HL. unfold L0, C, PAD. lia.
  Qed.

  Lemma argv0_str_ok : kentry_ok segs E0 M0 (KBlob (SA (fst e_strb) (snd e_strb)) (eaddz (EVar V_L0) 1) K_ARGV0).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof bsb_ge as (B1 & B2 & B3 & B4 & B5). pose proof PAD_range.
    pose proof L0_range as HL0. pose proof argv0_end_le as HEND.
    assert (Hab : split_lit e_str0 = (fst e_strb, snd e_strb)) by (unfold e_strb; destruct (split_lit e_str0); reflexivity).
    set (ab := fst e_strb) in *. set (ak := snd e_strb) in *.
    pose proof (split_u e_str0 ab ak Hab) as Hs. rewrite u_e_str0 in Hs.
    assert (Hak : ak = 16) by (subst ak; vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)).
    assert (Hst : estart E0 (SA ab ak) = usp + C + PAD) by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (eaddz (EVar V_L0) 1) = L0 + 1).
    { unfold elenZ, eaddz. rewrite mkAlu_denot, edenot_lit, u_add64, u64_lit by lia.
      destruct uE0 as (_ & _ & _ & U3 & _). unfold uE in U3. rewrite U3. apply Z.mod_small. lia. }
    assert (HE : eb E0 K_ARGV0 = s0 ++ [Z_to_bv 8 0]) by reflexivity.
    pose proof (u_cat_argv_ptr_k 0 Hav0) as Hp0.
    replace (total_arg_bytes_nat (firstn 0 (in_argv inp))) with 0%nat in Hp0 by reflexivity.
    assert (Hp0' : bv_unsigned (cat_argv_ptr (ed_top rnd) (in_argv inp) (in_envp inp) (in_execfn inp) 0)
                   = usp + C + PAD) by lia.
    cbn [kentry_ok]. rewrite Hst, Hl, HE.
    split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
    split; [rewrite length_app; cbn [length]; unfold L0; lia|].
    intros i Hi.
    pose proof (read_argv_byte_k vsz segs inp mb ph entry sp brk rnd 0 (Z.to_nat i)
                  Hlau Hav0 ltac:(fold s0; unfold L0 in Hi; lia)) as RB.
    fold s0 in RB.
    rewrite word_add_nat, Hp0' in RB. rewrite Z2Nat.id in RB by lia.
    unfold M0. rewrite (wrap_above_sp inp mb ph entry sp rnd _) by (rewrite u64_lit; unfold usp in *; lia).
    cbn [rdn] in RB.
    destruct (stack_to_mem sp (entry_stack_image inp mb ph entry sp rnd)
                (Z_to_bv 64 (usp + C + PAD + i))) as [b|] eqn:Hstk.
    - cbn in RB. injection RB as ->. reflexivity.
    - exfalso. unfold stack_to_mem in Hstk. rewrite u64_lit in Hstk by (unfold usp in *; lia).
      replace (bv_unsigned sp <=? usp + C + PAD + i) with true in Hstk by (symmetry; apply Z.leb_le; unfold usp; lia).
      cbv zeta in Hstk.
      replace (usp + C + PAD + i - bv_unsigned sp
               <? Z.of_nat (length (entry_stack_image inp mb ph entry sp rnd))) with true in Hstk
        by (symmetry; apply Z.ltb_lt; unfold bsb in *; unfold usp in *; lia).
      apply nth_error_None in Hstk. unfold bsb in *. lia.
  Qed.

  (* The image hull sits below the window floor: [wlo >= usp - 8388608]
     ([wlo_lo]) and [usp >= 0x7fff80000000], while [Hhull] caps [ihi] at
     [2^32].  No premise is needed, as before the revision. *)
  Lemma kimg_ok : kentry_ok segs E0 M0 (KImg ilo ihi).
  Proof.
    pose proof usp_lo. pose proof wlo_lo. destruct Hhull as [H1 H2].
    cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    apply M0_low. rewrite u64_lit; lia.
  Qed.

  Lemma rw_window_ok : kentry_ok segs E0 M0 (KWr (SA (ELit 0) rwlo) (ELit rwlen)).
  Proof.
    destruct Hrw as ((R1 & R0 & R2) & R3).
    assert (Hst : estart E0 (SA (ELit 0) rwlo) = rwlo) by (unfold estart; cbn [a_base a_off]; rewrite edenot_lit, u64_lit; lia).
    assert (Hl : elenZ E0 (ELit rwlen) = rwlen) by (unfold elenZ; rewrite edenot_lit, u64_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl. split; [unfold flat; rewrite Hst; lia|].
    intros d m Hd Hdm. destruct m as [|m']; [reflexivity|].
    assert (Hu : bv_unsigned (Z_to_bv 64 (rwlo + d)) = rwlo + d) by (apply u_small; rewrite Nat2Z.inj_succ in Hdm; lia).
    apply store_ok_of_all; rewrite Hu; [lia|].
    intros x Hx. apply R3. lia.
  Qed.

  Hypothesis Hextra : know_ok segs E0 M0 kn_extra.

  Theorem kn0_ok : know_ok segs E0 M0 kn0.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof RND_range. pose proof PAD_range.
    pose proof bsb_ge as (B1 & B2 & B3 & B4 & B5). destruct Hhull as [I1 I2]. pose proof L0_range.
    destruct uE0 as (U0 & U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9).
    pose proof stack_window_ok as [SW1 SW2].
    pose proof (aw_eq (at_random_ptr sp (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))
                  (at_execfn_ptr (ed_top rnd) (in_execfn inp))) as AW.
    assert (Hcnt : forall i, 0 <= i <= 25 ->
                   0 <= i < Z.of_nat (auxv_count (kb_rseq (in_kernel inp))))
      by (intros i Hi; case_eq (kb_rseq (in_kernel inp)); intros _; cbn [auxv_count]; lia).
    unfold kn0, kn0_b. unfold know_ok.
    repeat (apply Forall_app; split).
    - repeat apply Forall_cons; try apply Forall_nil.
      + apply kr_ok. lia.
      + cbn [kentry_ok]. split; [lia|]. unfold uE in U0. rewrite U0. exact Hal'.
      + apply kr_ok. pose proof u_e_atrandom as UA. unfold uE in UA |- *. unfold eaddz. rewrite mkAlu_denot, edenot_lit, u_add64, u64_lit, UA by lia.
        rewrite Z.mod_small by lia. lia.
      + apply kr_ok. lia.
      + apply kr_ok. lia.
      + apply kr_ok. lia.
      + apply kr_ok. lia.
      + apply kr_ok. lia.
      + apply kr_ok. rewrite U6. unfold valid_id in Huid. pose proof (u64_range (in_uid inp)). lia.
      + exact SW1.
      + exact SW2.
      + apply argc_word_ok.
      + apply argv0_word_ok.
      + apply argv1_word_ok.
    - apply auxw_ok; [apply Hcnt; lia | rewrite AW; reflexivity | rewrite AW, edenot_sysinfo; reflexivity].
    - apply auxw_ok; [apply Hcnt; lia | rewrite AW; reflexivity | rewrite AW, edenot_l1is; reflexivity].
    - apply auxw_ok; [apply Hcnt; lia | rewrite AW; reflexivity | rewrite AW, edenot_l1ig; reflexivity].
    - apply auxw_ok; [apply Hcnt; lia | rewrite AW; reflexivity | rewrite AW, edenot_l1ds; reflexivity].
    - apply auxw_ok; [apply Hcnt; lia | rewrite AW; reflexivity | rewrite AW, edenot_l1dg; reflexivity].
    - apply auxw_ok; [apply Hcnt; lia | rewrite AW; reflexivity | rewrite AW, edenot_l2s; reflexivity].
    - apply auxw_ok; [apply Hcnt; lia | rewrite AW; reflexivity | rewrite AW, edenot_l2g; reflexivity].
    - apply auxw_ok; [apply Hcnt; lia | rewrite AW; reflexivity | rewrite AW, edenot_l3s; reflexivity].
    - apply auxw_ok; [apply Hcnt; lia | rewrite AW; reflexivity | rewrite AW, edenot_l3g; reflexivity].
    - apply auxw_ok; [apply Hcnt; lia | rewrite AW; reflexivity | rewrite AW, edenot_minsig; reflexivity].
    - apply auxw_ok; [apply Hcnt; lia | rewrite AW; reflexivity | rewrite AW, edenot_hw; reflexivity].
    - apply auxw_ok; [apply Hcnt; lia | rewrite AW; reflexivity | rewrite AW, edenot_lit; reflexivity].
    - apply auxw_ok; [apply Hcnt; lia | rewrite AW; reflexivity | rewrite AW, edenot_lit; reflexivity].
    - apply auxw_ok; [apply Hcnt; lia | rewrite AW; reflexivity | rewrite AW, edenot_lit; reflexivity].
    - apply auxw_ok; [apply Hcnt; lia | rewrite AW; reflexivity | rewrite AW, edenot_lit; reflexivity].
    - apply auxw_ok; [apply Hcnt; lia | rewrite AW; reflexivity | rewrite AW, edenot_lit; reflexivity].
    - apply auxw_ok; [apply Hcnt; lia | rewrite AW; reflexivity | rewrite AW, edenot_lit; reflexivity].
    - apply auxw_ok; [apply Hcnt; lia | rewrite AW; reflexivity | rewrite AW, edenot_lit; reflexivity].
    - apply auxw_ok; [apply Hcnt; lia | rewrite AW; reflexivity | rewrite AW, edenot_entry; reflexivity].
    - apply auxw_ok; [apply Hcnt; lia | rewrite AW; reflexivity | rewrite AW, edenot_uid; reflexivity].
    - apply auxw_ok; [apply Hcnt; lia | rewrite AW; reflexivity | rewrite AW, edenot_uid; reflexivity].
    - apply auxw_ok; [apply Hcnt; lia | rewrite AW; reflexivity | rewrite AW, edenot_gid; reflexivity].
    - apply auxw_ok; [apply Hcnt; lia | rewrite AW; reflexivity | rewrite AW, edenot_gid; reflexivity].
    - apply auxw_ok; [apply Hcnt; lia | rewrite AW; reflexivity | rewrite AW, edenot_lit; reflexivity].
    - apply auxw_ok; [apply Hcnt; lia | rewrite AW; reflexivity | rewrite AW; rewrite <- atr_ptr_eq; reflexivity].
    - apply auxw_ok; [apply Hcnt; lia | rewrite AW; reflexivity | rewrite AW, edenot_execfn; reflexivity].
    - exact kn_rseq_ok.
    - exact kn_null_ok.
    - repeat apply Forall_cons; try apply Forall_nil.
      + apply atrandom_ok.
      + apply argv0_str_ok.
      + apply kimg_ok.
      + apply rw_window_ok.
    - exact Hextra.
  Qed.

  (* [kn0_ok] at a closed CONFIG_RSEQ flag: the table a per-flag boot chain
     starts from. *)
  Theorem kn0_ok_b : forall rs, kb_rseq (in_kernel inp) = rs ->
    know_ok segs E0 M0 (kn0_b rs ph ilo ihi rwlo rwlen kn_extra).
  Proof. intros rs <-. exact kn0_ok. Qed.

  Theorem regs0_ok : regs_ok E0 sr_init R0.
  Proof. unfold E0, vals0, R0. apply regs_ok_init. Qed.

End Entry.
