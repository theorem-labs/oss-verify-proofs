(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the main entry over the launch input ProcInput, the CONFIG_RSEQ flag, the new auxv and the init stack window; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require WsegFast PropExec CatExec CatSim SeqExec StoreOk FileSim ArgvEnv SymExec SymExec2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymRun.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymRun SymDrive MemSplit RefLayout StartupTac StartupRnd U.S0StartupDefs U.S0Startup.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require StartupTac ArgvEnv RefLayout StartupRnd U.S0StartupDefs U.S0Startup.
Module S0StartupFacts.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.bzip2.bzip2_compress_target.images.Ubsan.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StartupTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ArgvEnv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.RefLayout OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StartupRnd OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.S0StartupDefs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.S0Startup.
Import ListNotations.
Local Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RPH := Ubsan.M.phdrs.

(* [comment removed for export] *)
Definition D_main_cells : list (Z * nat) :=
  [(0x44110%Z, 8%nat); (0x64478%Z, 8%nat); (0x644d8%Z, 8%nat); (0x644a0%Z, 8%nat); (0x64468%Z, 8%nat); (0x64460%Z, 8%nat); (0x64208%Z, 8%nat); (0x64218%Z, 8%nat); (0x64210%Z, 8%nat); (0x64488%Z, 8%nat); (0x64490%Z, 8%nat); (0x441f0%Z, 8%nat); (0x441d8%Z, 8%nat); (0x44118%Z, 8%nat); (0x64470%Z, 1%nat); (0x44140%Z, 4%nat); (0x44138%Z, 4%nat); (0x441b0%Z, 8%nat); (0x44190%Z, 8%nat); (0x44120%Z, 8%nat); (0x44128%Z, 8%nat); (0x44130%Z, 8%nat); (0x64450%Z, 4%nat); (0x64454%Z, 4%nat); (0x64451%Z, 1%nat); (0x441d0%Z, 8%nat); (0x34090%Z, 1%nat)].

Definition range_disjoint_b (a : Z) (n : nat) (c : Z * nat) : bool :=
  ((a + Z.of_nat n <=? fst c) || (fst c + Z.of_nat (snd c) <=? a))%Z.

Definition D_main_missb (a : Z) (n : nat) : bool :=
  forallb (range_disjoint_b a n) D_main_cells && (0 <=? a)%Z && (a + Z.of_nat n <=? 0x66000)%Z.

(* [comment removed for export] *)
Definition djw (P : Prop) : Prop := P.

Lemma range_disjoint_djw : forall a n c,
  range_disjoint_b a n c = true ->
  djw (a + Z.of_nat n <= fst c \/ fst c + Z.of_nat (snd c) <= a)%Z.
Proof.
  intros a n [c l] H. unfold range_disjoint_b in H. cbn [fst snd] in *.
  apply orb_true_iff in H. unfold djw. destruct H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Section Facts.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 : word.
  Variable rnd : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation hw := (in_hwcap inp) (only parsing).
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.

  Let D := D_main inp sp0 rnd tid.

  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma D_main_tid : forall segs,
    rdn segs D (Z_to_bv 64 0x44138) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 tid)) as Hh.
    rewrite length_N_to_le_bytes in Hh. apply Hh. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_guard : forall segs,
    rdn segs D (Z_to_bv 64 0x64450) 8 = Some (canary_bytes rnd).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply (rdn_canary segs _ 0x64450 rnd); lia.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma D_main_pagesize : forall segs,
    rdn segs D (Z_to_bv 64 0x644a0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 4096)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof len_av. subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma D_main_self : forall segs,
    rdn segs D (Z_to_bv 64 0x44118) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x44118)).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_canary : forall segs,
    rdn segs D (Z_to_bv 64 0x441d0) 8 = Some (word_to_le_bytes 8 (canary_w rnd)).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_hwcap : forall segs,
    rdn segs D (Z_to_bv 64 0x644d8) 8 = Some (word_to_le_bytes 8 hw).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof len_av. subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry inp mbase entry sp0 rnd tid regs mem.

  (* [comment removed for export] *)

  Lemma main_entry_tid : forall segs,
    rdn segs mem (Z_to_bv 64 0x44138) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. rewrite (main_entry_rdn_data inp mbase entry sp0 rnd tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_tid.
  Qed.

  Lemma main_entry_guard : forall segs,
    rdn segs mem (Z_to_bv 64 0x64450) 8 = Some (canary_bytes rnd).
  Proof.
    intros segs. rewrite (main_entry_rdn_data inp mbase entry sp0 rnd tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_guard.
  Qed.
End Facts.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S0StartupFacts.

Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.WsegFast OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.FileSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ArgvEnv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymExec2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymRun.SymExec2Sound OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymRun OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymDrive OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MemSplit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.RefLayout OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StartupTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StartupRnd OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.S0StartupDefs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.S0Startup OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.S0MainEntry.S0StartupFacts.
Import ListNotations.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require NatLitLia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require U.S0WsegData.   (* [comment removed for export] *)
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
Open Scope bv_scope.
Import SX2. Import SX2S.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma D_main_none : forall inp sp0 rnd tid (i : Z),
  valid_argv (in_argv inp) -> (0x7fff80000000 <= bv_unsigned sp0)%Z -> (bv_unsigned sp0 <= 0x800000000000)%Z ->
  D_main_missb i 1 = true ->
  D_main inp sp0 rnd tid (Z_to_bv 64 i) = None.
Proof.
  intros inp sp0 rnd tid i Hva Hlo Hhi Hb. pose proof (u64_range (in_hwcap inp)) as Hhw.
  pose proof (u64_range tid) as Ht.
  unfold D_main_missb, D_main_cells in Hb. cbn [forallb] in Hb.
  repeat match goal with
         | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H as [? ?]
         end.
  repeat match goal with
         | H : range_disjoint_b _ _ _ = true |- _ =>
             apply range_disjoint_djw in H; cbn [fst snd] in H
         | H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
         | H : true = true |- _ => clear H
         end.
  assert (Hui : bv_unsigned (Z_to_bv 64 i) = i) by (apply u_small; lia).
  unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
  repeat (rewrite MemSplit.wbytes_outside;
    [ | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite u_small by (cbn; lia); cbn; lia
      | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite Hui; rewrite u_small by (cbn; lia);
        match goal with H : djw _ |- _ => unfold djw in H; clear -H; lia end ]).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma seg_rom_high : forall (a : word), (0x66000 <= bv_unsigned a)%Z -> seg_rom RSEGS a = None.
Proof.
  intros a Ha. unfold seg_rom. unfold memory_read.
  cbn -[bv_unsigned Z.leb Z.ltb Z.add Z.sub N.leb N.ltb N.add bv_extract Z.of_N Z.to_N].
  cbn [Z.of_N].
  repeat (lazymatch goal with
          | |- context [((?lo <=? bv_unsigned a)%Z && ?c)%bool] =>
              replace c with false by (symmetry; apply Z.leb_gt; lia); rewrite andb_false_r
          end).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_pointwise_inv : forall segs m n (a : word) bs,
  (forall j, (j < n)%nat -> seg_rom segs (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = None) ->
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  rdn segs m a n = Some bs ->
  forall j, (j < n)%nat -> m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0)).
Proof.
  intros segs m n. induction n as [|n IH]; intros a bs Hseg Hnw Hr j Hj; [lia|].
  cbn [rdn] in Hr. pose proof (u64_range a) as Ha.
  pose proof (Hseg 0%nat ltac:(lia)) as H0. rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned in H0.
  destruct (m a) as [b|] eqn:Hm.
  - destruct (rdn segs m (a + 1) n) as [rest|] eqn:Hr'; [|discriminate]. injection Hr as <-.
    destruct j as [|j].
    + rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned. exact Hm.
    + cbn [nth]. assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
      replace (bv_unsigned a + Z.of_nat (S j))%Z with (bv_unsigned (a + 1) + Z.of_nat j)%Z by lia.
      apply (IH (a + 1) rest); [ | lia | exact Hr' | lia].
      intros k Hk. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat k)%Z with (bv_unsigned a + Z.of_nat (S k))%Z by lia.
      apply Hseg. lia.
  - rewrite H0 in Hr. discriminate.
Qed.

(* The blobs the main phase reads: argv[0], argv[1], the AT_RANDOM bytes,
   the canary and AT_HWCAP.  Outside the section so a consumer can name the
   hwcap word it holds. *)
Definition blobs0 (a0s path : list byte) (hw : word) (rnd : EntryDraw) : list (list byte) :=
  [a0s ++ [Z_to_bv 8 0]; path ++ [Z_to_bv 8 0]; at_random_bytes (ed_random rnd); canary_bytes rnd; word_to_le_bytes 8 hw].

Section MainEntry.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 brk : word.
  Variables a0s path : list byte.
  Variable rnd : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Local Notation ev := (in_envp inp) (only parsing).
  Local Notation uid := (in_uid inp) (only parsing).
  Local Notation hw := (in_hwcap inp) (only parsing).
  Let av := [a0s; path].
  Hypothesis Hav : in_argv inp = av.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rnd) inp.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry inp mbase entry sp0 rnd tid regs mem.

  Let Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  Definition p0 : word := cat_argv_ptr (ed_top rnd) (in_argv inp) ev (in_execfn inp) 0.
  Definition p1 : word := cat_argv_ptr (ed_top rnd) (in_argv inp) ev (in_execfn inp) 1.
  Definition auxvp : word := auxv_w inp sp0.
  Definition rndp : word := at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) ev.

  (* [comment removed for export] *)
  Definition vals0 : list word := [sp0; p0; p1; auxvp; rndp; tid] ++ junk_vals regs.
  Definition E0 : env := Env (vals_ev vals0) (blobs_ev (blobs0 a0s path hw rnd)).

  Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

  Definition sr_main : list expr :=
    [ELit 0; ELit 0x28c48; spx (-48); ELit 0x10800; ELit 0x441e0; EVar 11; EVar 12; EVar 13;
     spx 8; ELit 2; ELit 2; spx 8; spx 32; EVar 19; EVar 20; EVar 21;
     EVar 22; EVar 23; ELit 0x13580; spx 32; ELit 0; ELit 0; ELit 0; ELit 0;
     ELit 0; ELit 0; ELit 0; ELit 0; EVar 34; EVar 35; EVar 36; EVar 37].

  Definition kn_stack : list kentry :=
    [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
     (* LPS 75d69e00 (#38): was [KWr (SA (EVar 0) (-8388608)) 8388608].  BYTES.
        8388608 is the allocator ceiling [stack_max_size]; what entry actually
        reserves, and so all [main_entry_store_ok_win] can give, is the span
        [stack_window_depth = 8388608 - 2244095 = 6144513].  Discharged at the
        [kn_stack] KWr case below.  The 4 GiB KDisj entries in [kn_auxv] are a
        different (disjointness) role and stay at their old, stronger extent. *)
     KWr (SA (EVar 0) (-6144513)) 6144513;
     KWord (SA (EVar 0) 0) 8 (ELit 2); KWord (SA (EVar 0) 8) 8 (EVar 1);
     KWord (SA (EVar 0) 16) 8 (EVar 2); KWord (SA (EVar 0) 24) 8 (ELit 0)].

  Definition kn_auxv : list kentry :=
    [KRange (EVar 3) 0x7fff80000000 0x800000400000; KRange (EVar 4) 0x7fff80000000 0x800000400000;
     (* LPS 75d69e00 (#38), rule 12k: was [... (SA (EVar 3) 0) 160], the OLD ten-pair
        vector.  The revision's vector is 27 pairs, 29 under CONFIG_RSEQ: at most
        2 * 29 * 8 = 464 bytes, the figure [auxvp_bounds] below already reserves.
        Maximum over both [kb_rseq] values, so kernel-free and strictly stronger. *)
     KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 3) 0) 464;
     KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 4) 0) 16;
     (* [comment removed for export] *)
     KDisj (SA (EVar 0) (-4294967296)) 4294967296 (SA (EVar 3) 0) 464;
     KDisj (SA (EVar 0) (-4294967296)) 4294967296 (SA (EVar 4) 0) 16;
     KAlign (EVar 3) 8; KAlign (EVar 4) 8;
     (* The auxv's WORDS are not recorded here, and that is the open item behind
        [U/S0W65x.v:425] / [S0W65x.v:426] -- NOT a settled decision.  The claim this
        comment used to make, "the main phase reads none of it", is FALSE: the block at
        pc 0x29c38 walks the vector looking for AT_RANDOM, reading the a_type word at
        [auxvp + 16] first (measured: the run halts there, at
        pc 0x29c48, with sidecond [SCReadBase {a_base := EVar 3; a_off := 16} 8 false
        (EVar 70)], having allocated EVar 70 as a FRESH variable for the word it could
        not resolve -- byte-for-byte the same shape as the Asan twin).  Measured vector
        at this revision: auxv_count 27 / 29, auxv_size
        432 / 464 bytes, a_type of entries 0..25 =
        33 40 41 42 43 44 45 46 47 51 16 6 17 3 4 5 7 8 9 11 12 13 14 23 25 31
        -- so AT_PAGESZ is entry 11 (value word at 11*16+8 = 184) and AT_RANDOM is
        entry 24 (value word at 24*16+8 = 392).  Restoring a [KWord (SA (EVar 3) (16*j))
        8 (ELit t_j)] row for entries 1..24 plus AT_RANDOM's value word, each discharged
        through [rd_auxv_main], makes the walk unroll again; all of those sit strictly
        below the rseq pairs and AT_NULL, so [kb_rseq] stays free. *)
     KBlob (SA (EVar 4) 0) (ELit 16) 2].

  (* LPS 75d69e00 (#38), rule 12k -- THE AUXV a_type WORDS, restored at the revision's
     own slot indices.  [kn_auxv] above records none of them, and that is what halts the
     walk at pc 0x20174: it reads the a_type word at [auxvp + 16] (entry 1; pairs are 16
     bytes), cannot resolve it, and allocates a FRESH valuation variable for it --
     which is the [EVar 70] that [S0W65x.v]'s [b_expr] then names "brk".
     Vector measured at this revision (image
     sha256:2c6b6db8...e590fe, exit 0): auxv_count 27 / 29, and a_type of entries 0..25
       33 40 41 42 43 44 45 46 47 51 16 6 17 3 4 5 7 8 9 11 12 13 14 23 25 31.
     Entry j's a_type word sits at byte offset 16 * j and is element 2 * j of
     [auxv_words], which is what [rd_auxv_main] reads.  Entries 1..24 are recorded here:
     24 is AT_RANDOM, where the walk stops, and every one of these is strictly BELOW the
     AT_RSEQ pairs and AT_NULL -- so this list is the same for both values of
     [kb_rseq] and pins nothing about it.  Entry 0 (AT_SYSINFO_EHDR, type 33) IS read:
     the scan starts with s1 = 0, so its first load is the a_type at [auxvp + 0]
     (measured on the Plain twin: without a row for it block B stops at the
     scan's [beq] on a fresh variable).  Its row sits after AT_EXECFN's below. *)
  Definition kn_auxw : list kentry :=
    [KWord (SA (EVar 3) 16) 8 (ELit 40);   (*  1 AT_L1I_CACHESIZE *)
     KWord (SA (EVar 3) 32) 8 (ELit 41);   (*  2 AT_L1I_CACHEGEOMETRY *)
     KWord (SA (EVar 3) 48) 8 (ELit 42);   (*  3 AT_L1D_CACHESIZE *)
     KWord (SA (EVar 3) 64) 8 (ELit 43);   (*  4 AT_L1D_CACHEGEOMETRY *)
     KWord (SA (EVar 3) 80) 8 (ELit 44);   (*  5 AT_L2_CACHESIZE *)
     KWord (SA (EVar 3) 96) 8 (ELit 45);   (*  6 AT_L2_CACHEGEOMETRY *)
     KWord (SA (EVar 3) 112) 8 (ELit 46);   (*  7 AT_L3_CACHESIZE *)
     KWord (SA (EVar 3) 128) 8 (ELit 47);   (*  8 AT_L3_CACHEGEOMETRY *)
     KWord (SA (EVar 3) 144) 8 (ELit 51);   (*  9 AT_MINSIGSTKSZ *)
     KWord (SA (EVar 3) 160) 8 (ELit 16);   (* 10 AT_HWCAP *)
     KWord (SA (EVar 3) 176) 8 (ELit 6);   (* 11 AT_PAGESZ *)
     KWord (SA (EVar 3) 192) 8 (ELit 17);   (* 12 AT_CLKTCK *)
     KWord (SA (EVar 3) 208) 8 (ELit 3);   (* 13 AT_PHDR *)
     KWord (SA (EVar 3) 224) 8 (ELit 4);   (* 14 AT_PHENT *)
     KWord (SA (EVar 3) 240) 8 (ELit 5);   (* 15 AT_PHNUM *)
     KWord (SA (EVar 3) 256) 8 (ELit 7);   (* 16 AT_BASE *)
     KWord (SA (EVar 3) 272) 8 (ELit 8);   (* 17 AT_FLAGS *)
     KWord (SA (EVar 3) 288) 8 (ELit 9);   (* 18 AT_ENTRY *)
     KWord (SA (EVar 3) 304) 8 (ELit 11);   (* 19 AT_UID *)
     KWord (SA (EVar 3) 320) 8 (ELit 12);   (* 20 AT_EUID *)
     KWord (SA (EVar 3) 336) 8 (ELit 13);   (* 21 AT_GID *)
     KWord (SA (EVar 3) 352) 8 (ELit 14);   (* 22 AT_EGID *)
     KWord (SA (EVar 3) 368) 8 (ELit 23);   (* 23 AT_SECURE *)
     KWord (SA (EVar 3) 384) 8 (ELit 25);   (* 24 AT_RANDOM *)
     (* 25 AT_EXECFN's a_TYPE word, at 25*16 = 400.  The 24 rows above carried the
        FIRST call's walk; the SECOND call's resumed scan reads one pair further.
        A TYPE word is kernel-free, so this does not pin [kb_rseq]: [kauxv_type]'s
        bound [j < auxv_count] holds at 25 for BOTH flag values (27 and 29), so the
        row still stops short of the AT_RSEQ pairs and AT_NULL.  Mirrored from the
        Asan tree; the Ubsan addresses are a MEASUREMENT, not an assumption. *)
     KWord (SA (EVar 3) 400) 8 (ELit 31);   (* 25 AT_EXECFN *)
     (* 0 AT_SYSINFO_EHDR's a_TYPE word, at offset 0: the FIRST word the scan reads.
        [auxv_entries] lists it first unconditionally, and 0 < auxv_count at both
        [kb_rseq] values, so it pins nothing. *)
     KWord (SA (EVar 3) 0) 8 (ELit 33);   (*  0 AT_SYSINFO_EHDR *)
     (* AT_RANDOM's a_VAL word, at 24*16+8 = 392.  One run left
        exactly this read open after the 24 a_type rows carried the walk from 0x20184
        to 0x26BE8; the next added it and the block came back with
        nvals 70 and NO sideconds.  Its value is [rndp inp sp0], bound at index 4.
        NOTE for a span sweep (Main, rule 12k): the 160 above is AT_HWCAP's a_TYPE slot,
        not an old auxv span.  bzip2 has ZERO old-span sites, so a sweep keyed on the
        literal 160 would corrupt a true claim here and find nothing it was looking for. *)
     KWord (SA (EVar 3) 392) 8 (EVar 4)].

  (* The auxv TERMINATOR, which depends on the free kernel field [kb_rseq]: with
     CONFIG_RSEQ, pairs 26 and 27 are AT_RSEQ_FEATURE_SIZE (27) and AT_RSEQ_ALIGN (28) and
     AT_NULL is pair 28.  Without it, AT_NULL is pair 26 ([auxv_entries], LPS 75d69e00).
     The scan after the AT_RANDOM memcpy reads these words, so a walk past them has to
     split on the flag.  These lists are NOT in [kn_main].  [know_auxv_term] proves the
     one that holds, as a disjunction, so the flag stays free. *)
  Definition kn_termT : list kentry :=
    [KWord (SA (EVar 3) 416) 8 (ELit 27); KWord (SA (EVar 3) 432) 8 (ELit 28);
     KWord (SA (EVar 3) 448) 8 (ELit 0)].
  Definition kn_termF : list kentry := [KWord (SA (EVar 3) 416) 8 (ELit 0)].

  (* [comment removed for export] *)
  Definition kn_image : list kentry :=
    [KWr (SA (ELit 0) 0x33000) 0x33000;
     KImg 0x10000 0x34090;
     KImg 0x34091 0x340d9; KImg 0x440d9 0x44110; KImg 0x641e8 0x64208;
     KWord (SA (ELit 0) 0x44118) 8 (ELit 0x44118);
     KWord (SA (ELit 0) 0x44138) 4 (EVar 5);
     KImg 0x44144 0x44190; KImg 0x44198 0x441b0; KImg 0x441b8 0x441d0;
     KBlob (SA (ELit 0) 0x441d0) (ELit 8) 3;                 (* [comment removed for export] *)
     KImg 0x441e0 0x441f0; KImg 0x441f8 0x641e8; KImg 0x64220 0x64450;
     KBlob (SA (ELit 0) 0x64450) (ELit 8) 3;                 (* [comment removed for export] *)
     KImg 0x64458 0x64460;
     KImg 0x64471 0x64478; KWord (SA (ELit 0) 0x64478) 8 (EVar 3);
     KImg 0x64480 0x64488; KImg 0x64498 0x644a0; KWord (SA (ELit 0) 0x644a0) 8 (ELit 4096);
     KImg 0x644a8 0x644d8; KBlob (SA (ELit 0) 0x644d8) (ELit 8) 4 (* [comment removed for export] *); KImg 0x644e0 0x66000;
     KRange (EVar 5) 1 4194303;
     KImg 0 0x1000 (* [comment removed for export] *)].

  (* [comment removed for export] *)
  Definition kn_main : list kentry := kn_stack ++ kn_auxv ++ kn_auxw ++ kn_image.
End MainEntry.

Definition all_regs : list reg := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Lemma nth_all_regs : forall n, (n < 32)%nat -> nth n all_regs 0%bv = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros n Hn.
  destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; apply bv_eq; reflexivity.
Qed.

Lemma regs_ok_by_index : forall E sr R,
  (forall i, (i < 32)%nat -> getr R (nth i all_regs 0%bv) = edenot E (nth i sr (ELit 0))) ->
  regs_ok E sr R.
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot].
    reflexivity.
  - pose proof (H (ridx r) (ridx_range r)) as Hx. rewrite nth_all_regs in Hx by apply ridx_range.
    rewrite ridx_roundtrip in Hx. exact Hx.
Qed.

Section MainEntryProofs.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 brk : word.
  Variables a0s path : list byte.
  Variable rnd : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Local Notation envv := (in_envp inp) (only parsing).
  Local Notation uid := (in_uid inp) (only parsing).
  Local Notation hw := (in_hwcap inp) (only parsing).
  Let av := [a0s; path].
  Hypothesis Hav : in_argv inp = av.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rnd) inp.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry inp mbase entry sp0 rnd tid regs mem.

  Let E := E0 inp sp0 a0s path rnd tid regs.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma ev_vals : forall n, ev E n = nth n ([sp0; p0 inp rnd; p1 inp rnd; auxvp inp sp0; rndp inp sp0; tid] ++ junk_vals regs) (Z_to_bv 64 0).
  Proof. intros n. reflexivity. Qed.

  Lemma ev_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. rewrite ev_vals. change (6 + i)%nat with (length [sp0; p0 inp rnd; p1 inp rnd; auxvp inp sp0; rndp inp sp0; tid] + i)%nat.
    rewrite app_nth2_plus. unfold junk_vals. rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.

  Lemma spx_val : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
  Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev E 0) with sp0.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

End MainEntryProofs.

Section MainRegs.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 brk : word.
  Variables a0s path : list byte.
  Variable rnd : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Local Notation envv := (in_envp inp) (only parsing).
  Local Notation uid := (in_uid inp) (only parsing).
  Local Notation hw := (in_hwcap inp) (only parsing).
  Let av := [a0s; path].
  Hypothesis Hav : in_argv inp = av.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rnd) inp.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry inp mbase entry sp0 rnd tid regs mem.
  Let E := E0 inp sp0 a0s path rnd tid regs.

  Ltac reg_case :=
    cbn [nth sr_main all_regs];
          first [ rewrite (spx_val inp sp0 a0s path rnd tid regs)
                | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                    change (edenot E (EVar n)) with (ev E n);
                    first [ rewrite (ev_junk inp sp0 a0s path rnd tid regs (n - 6)) by lia; reflexivity | idtac ]
                  | |- _ => cbn [edenot] end ];
          first [ reflexivity
                | exact (me_ra _ _ _ _ _ _ _ _ ME) | exact (me_gp _ _ _ _ _ _ _ _ ME) | exact (me_tp _ _ _ _ _ _ _ _ ME)
                | exact (me_s2 _ _ _ _ _ _ _ _ ME)
                | rewrite (me_sp _ _ _ _ _ _ _ _ ME); apply bv_eq; rewrite !u_small by lia; lia
                | rewrite (me_s0 _ _ _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a1 _ _ _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a2 _ _ _ _ _ _ _ _ ME); f_equal; rewrite Hav; subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s3 _ _ _ _ _ _ _ _ ME); f_equal; rewrite Hav; subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s1 _ _ _ _ _ _ _ _ ME); unfold argcN, len_word; rewrite Hav; reflexivity
                | rewrite (me_a0 _ _ _ _ _ _ _ _ ME); unfold argcN, len_word; rewrite Hav; reflexivity
                | apply (me_szero _ _ _ _ _ _ _ _ ME); cbn; tauto
                | idtac ].

  Theorem main_regs_ok : regs_ok E sr_main regs.
  Proof.
    pose proof (proj1 Hvsp) as Hlo. pose proof (proj1 (proj2 Hvsp)) as Hhi. unfold sp_window_lo, sp_window_hi in *.
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_case.
  Qed.
End MainRegs.

Section KnowProofs.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 brk : word.
  Variables a0s path : list byte.
  Variable rnd : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Local Notation envv := (in_envp inp) (only parsing).
  Local Notation uid := (in_uid inp) (only parsing).
  Local Notation hw := (in_hwcap inp) (only parsing).
  Let av := [a0s; path].
  Hypothesis Hav : in_argv inp = av.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rnd) inp.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry inp mbase entry sp0 rnd tid regs mem.
  Let E := E0 inp sp0 a0s path rnd tid regs.

  Lemma kp_lo : (0x7fff80000000 <= bv_unsigned sp0)%Z. Proof. exact (proj1 Hvsp). Qed.
  Lemma kp_hi : (bv_unsigned sp0 <= 0x800000000000)%Z. Proof. exact (proj1 (proj2 Hvsp)). Qed.
  Lemma kp_al : (bv_unsigned sp0 mod 16 = 0)%Z. Proof. exact (proj2 (proj2 Hvsp)). Qed.
  Lemma ke0 : ev E 0 = sp0. Proof. reflexivity. Qed.
  Lemma ke1 : ev E 1 = p0 inp rnd. Proof. reflexivity. Qed.
  Lemma ke2 : ev E 2 = p1 inp rnd. Proof. reflexivity. Qed.
  Lemma ke3 : ev E 3 = auxvp inp sp0. Proof. reflexivity. Qed.
  Lemma ke4 : ev E 4 = rndp inp sp0. Proof. reflexivity. Qed.
  Lemma ke5 : ev E 5 = tid. Proof. reflexivity. Qed.

  Lemma know_stack : know_ok RSEGS E mem kn_stack.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    unfold kn_stack, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot]; rewrite ?ke0, ?ke1, ?ke2;
      unfold flat, estart; cbn [a_base a_off edenot]; rewrite ?ke0.
    - split; [lia | exact Hal].
    - lia.
    - split; [lia|]. intros d m Hd Hm.
      (* LPS 75d69e00 (#38): floor is now the span, so the goal no longer
         mentions [stack_max_size]; was [... ; unfold stack_max_size; lia]. *)
      apply (main_entry_store_ok_win inp mbase entry sp0 rnd tid regs mem ME);
        rewrite u_small by lia; clear - Hd Hm; lia.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite (main_entry_rdn_above inp mbase entry sp0 rnd tid regs mem ME) by lia.
      assert (Hr : rdn RSEGS (wrap_mem inp mbase RPH entry sp0 rnd) sp0 8 = Some (word_le8 (argcN inp)))
        by (eapply (read_argc_w RSEGS Sv48 inp mbase RPH entry sp0 brk rnd); try eassumption; unfold sp_window_hi; lia).
      rewrite Hr. unfold argcN. rewrite Hav.
      rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above inp mbase entry sp0 rnd tid regs mem ME) by (rewrite u_small by lia; lia).
      assert (Hr : rdn RSEGS (wrap_mem inp mbase RPH entry sp0 rnd) (sp0 + nat_to_word (8 + 8 * 0)) 8
                   = Some (word_le8 (cat_argv_ptr (ed_top rnd) (in_argv inp) envv (in_execfn inp) 0)))
        by (eapply (read_argv_ptr_w RSEGS Sv48 inp mbase RPH entry sp0 brk rnd); try eassumption;
            first [unfold sp_window_lo; lia | unfold sp_window_hi; lia | rewrite Hav; subst av; cbn; lia]). rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above inp mbase entry sp0 rnd tid regs mem ME) by (rewrite u_small by lia; lia).
      assert (Hr : rdn RSEGS (wrap_mem inp mbase RPH entry sp0 rnd) (sp0 + nat_to_word (8 + 8 * 1)) 8
                   = Some (word_le8 (cat_argv_ptr (ed_top rnd) (in_argv inp) envv (in_execfn inp) 1)))
        by (eapply (read_argv_ptr_w RSEGS Sv48 inp mbase RPH entry sp0 brk rnd); try eassumption;
            first [unfold sp_window_lo; lia | unfold sp_window_hi; lia | rewrite Hav; subst av; cbn; lia]). rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 1)) with 16%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above inp mbase entry sp0 rnd tid regs mem ME) by (rewrite u_small by lia; lia).
      assert (Hr : rdn RSEGS (stack_to_mem sp0 (entry_stack_image inp mbase RPH entry sp0 rnd))
                     (sp0 + nat_to_word (8 + 8 * length (in_argv inp))) 8 = Some (word_le8 (Z_to_bv 64 0)))
        by (eapply (read_argv_null RSEGS Sv48 inp mbase RPH entry sp0 brk rnd); try eassumption;
            first [unfold sp_window_lo; lia | unfold sp_window_hi; lia]).
      rewrite w_add_nat in Hr. rewrite Hav in Hr. subst av. change (Z.of_nat (8 + 8 * length [a0s; path])) with 24%Z in Hr.
      rewrite <- (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rnd) in Hr by (try rewrite u_small by lia; lia).
      unfold wmem in Hr. rewrite n_to_le_8_spec in Hr. exact Hr.
  Qed.

  Lemma auxvp_eq : auxvp inp sp0 = Z_to_bv 64 (bv_unsigned sp0 + Z.of_nat (auxv_off av envv)).
  Proof. unfold auxvp, auxv_w, auxv_off. rewrite Hav. subst av. cbn [length]. f_equal. lia. Qed.

  Lemma auxvp_u : bv_unsigned (auxvp inp sp0) = (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z
    /\ (Z.of_nat (auxv_off av envv) + 176 <= 2240000)%Z.
  Proof.
    pose proof kp_lo. pose proof kp_hi. destruct Hve as [Hle _].
    rewrite auxvp_eq. unfold auxv_off in *. subst av. cbn [length] in *.
    rewrite u_small by lia. split; lia.
  Qed.

  Lemma rnd_u : (bv_unsigned sp0 <= bv_unsigned (rndp inp sp0))%Z
    /\ (bv_unsigned (rndp inp sp0) + 16 <= bv_unsigned sp0 + 2240000)%Z
    /\ (bv_unsigned (rndp inp sp0) mod 8 = 0)%Z
    /\ (forall j n, (j + n <= 16)%nat ->
          rdn RSEGS (stack_to_mem sp0 (entry_stack_image inp mbase RPH entry sp0 rnd))
              (Z_to_bv 64 (bv_unsigned (rndp inp sp0) + Z.of_nat j)) n = Some (firstn n (skipn j (at_random_bytes (ed_random rnd))))).
  Proof.
    pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    pose proof (lay_bsb_len Sv48 inp mbase RPH entry sp0 brk rnd Hvl Hlau) as Hl.
    assert (RF := rnd_facts RSEGS Sv48 inp mbase RPH entry sp0 brk rnd).
    repeat match type of RF with ?P -> _ =>
      specialize (RF ltac:(first [exact Hva | exact Hve | exact Hvl | exact Hlau | exact kp_al
                                 | (unfold sp_window_lo; lia) | (unfold sp_window_hi; lia)])) end.
    cps_destruct RF as (A & B & C & D & F).
    unfold rndp. repeat split; try assumption; try lia.
  Qed.


  Lemma know_auxv : know_ok RSEGS E mem kn_auxv.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    destruct auxvp_u as [Hau Hab]. cps_destruct rnd_u as (Hr1 & Hr2 & Hr3 & Hr4).
    unfold kn_auxv, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot];
      rewrite ?ke0, ?ke3, ?ke4; unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?ke0, ?ke3, ?ke4;
      try rewrite Hau; try lia.
    - (* [comment removed for export] *) split; [lia|].
      destruct (proj1 (Z.mod_divide (bv_unsigned sp0) 16 ltac:(lia)) Hal) as [q Hq].
      replace (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z with ((2 * q + 5 + Z.of_nat (length envv)) * 8)%Z
        by (unfold auxv_off; subst av; cbn [length]; lia).
      apply Z_mod_mult.
    - (* [comment removed for export] *)
      rewrite u_small by lia. split; [lia|]. change (eb E 2) with (at_random_bytes (ed_random rnd)). split; [rewrite length_at_random_bytes; reflexivity|]. intros i Hi.
      assert (Hr : rdn RSEGS mem (rndp inp sp0) 16 = Some (at_random_bytes (ed_random rnd))).
      { rewrite (main_entry_rdn_above inp mbase entry sp0 rnd tid regs mem ME) by lia.
        pose proof (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rnd) as Hw. unfold wmem in Hw.
        rewrite Hw by lia.
        pose proof (Hr4 0%nat 16%nat ltac:(lia)) as H16. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H16.
        rewrite H16. f_equal. }
      pose proof (rdn_pointwise_inv RSEGS mem 16 (rndp inp sp0) _
                    ltac:(intros j Hj; apply seg_rom_high; rewrite u_small by lia; lia)
                    ltac:(lia) Hr (Z.to_nat i) ltac:(lia)) as Hp.
      rewrite Z2Nat.id in Hp by lia.
      replace (bv_unsigned (rndp inp sp0) + 0 + i)%Z with (bv_unsigned (rndp inp sp0) + i)%Z by lia.
      rewrite Hp. reflexivity.
  Qed.


  (* LPS 08b1429: an auxv word of the main entry's memory, read off the stack image
     ([RefLayout.read_auxv_word]); both CONFIG_RSEQ layouts, [j] ranging over the vector. *)
  Lemma rd_auxv_main : forall j w a,
    (j < 2 * auxv_count (kb_rseq (in_kernel inp)))%nat ->
    nth j (auxv_words (launch_auxv inp sp0 mbase) RPH entry uid (in_gid inp) hw (rndp inp sp0)
             (at_execfn_ptr (ed_top rnd) (in_execfn inp))) (Z_to_bv 64 0) = w ->
    a = (bv_unsigned (auxvp inp sp0) + 8 * Z.of_nat j)%Z ->
    rdn RSEGS mem (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 w).
  Proof.
    intros j w a Hj Hw ->. pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
    destruct auxvp_u as [Hau Hab].
    assert (Hac : (auxv_count (kb_rseq (in_kernel inp)) <= 29)%nat)
      by (unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia).
    (* [u64_lit] lives in AgentLib, which this file never Requires; the
       in-scope name for the identical statement is [u_small]. *)
    rewrite (main_entry_rdn_above inp mbase entry sp0 rnd tid regs mem ME) by (rewrite u_small by lia; lia).
    pose proof (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rnd) as Hwm. unfold wmem in Hwm.
    rewrite Hwm by (rewrite u_small by lia; lia).
    replace (Z_to_bv 64 (bv_unsigned (auxvp inp sp0) + 8 * Z.of_nat j))
      with (sp0 + nat_to_word (auxv_off (in_argv inp) (in_envp inp) + 8 * j))
      by (rewrite word_add_nat; f_equal; rewrite Hav, Hau; lia).
    rewrite <- Hw. unfold rndp.
    eapply read_auxv_word; first [exact Hva | exact Hve | exact Hvl | exact Hlau | exact Hj
                                 | (unfold sp_window_lo; lia) | (unfold sp_window_hi; lia) | eassumption].
  Qed.

  (* The conjunction had lost its backslash ("...)%Z /    (..."), so Coq read
     the [/] as Z division and the left conjunct as a Z.  464 is BYTES: 29
     auxv PAIRS * 2 words * 8, matching [Hac : auxv_count .. <= 29] above. *)
  Lemma auxvp_bounds : (bv_unsigned sp0 <= bv_unsigned (auxvp inp sp0))%Z /\ (bv_unsigned (auxvp inp sp0) + 464 <= 2 ^ 64)%Z.
  Proof. pose proof kp_lo. pose proof kp_hi. destruct auxvp_u as [Hau Hab]. lia. Qed.

  (* One row of [kn_auxw]: entry [j]'s a_type word, which is element [2 * j] of
     [auxv_words] and sits at byte offset [16 * j] from [auxvp].  Proved once and
     applied per entry, so the 24 rows cost one proof rather than 24.  The bound is
     [j < auxv_count], i.e. strictly inside the vector at BOTH [kb_rseq] values, which
     is what keeps the rows free of the AT_RSEQ pairs and AT_NULL. *)
  Lemma kauxv_type : forall (j : nat) (t : Z),
    (j < auxv_count (kb_rseq (in_kernel inp)))%nat ->
    nth (2 * j) (auxv_words (launch_auxv inp sp0 mbase) RPH entry uid (in_gid inp) hw (rndp inp sp0)
                   (at_execfn_ptr (ed_top rnd) (in_execfn inp))) (Z_to_bv 64 0) = Z_to_bv 64 t ->
    kentry_ok RSEGS E mem (KWord (SA (EVar 3) (16 * Z.of_nat j)) 8 (ELit t)).
  Proof.
    intros j t Hj Ht. pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
    destruct auxvp_u as [Hau Hab].
    assert (Hac : (auxv_count (kb_rseq (in_kernel inp)) <= 29)%nat)
      by (unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia).
    cbn [kentry_ok]. split; [lia|].
    unfold flat, estart. cbn [a_base a_off edenot]. rewrite ke3. rewrite Hau.
    split; [repeat split; lia|].
    cbn [adenot a_base a_off edenot]. rewrite ?ke3.
    erewrite <- (rd_auxv_main (2 * j) (Z_to_bv 64 t));
      [ f_equal
      | lia
      | exact Ht
      | (* Rocq printed this goal: the record projections
           [a_base {| ... |}] / [a_off {| ... |}] are still unreduced, so no arithmetic
           tactic applies until they are.  [cbn] them, name [ev E 3], then it is linear. *)
        cbn [a_base a_off edenot]; rewrite ke3; lia ].
  Qed.

  (* AT_RANDOM's a_VAL word: element 49 of [auxv_words], byte offset 392, value
     [rndp inp sp0] -- which [rd_auxv_main] already carries in that argument slot,
     and which the env binds at index 4 ([ke4]). *)
  Lemma kauxv_rnd : kentry_ok RSEGS E mem (KWord (SA (EVar 3) 392) 8 (EVar 4)).
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
    destruct auxvp_u as [Hau Hab].
    assert (Hac : (auxv_count (kb_rseq (in_kernel inp)) <= 29)%nat)
      by (unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia).
    assert (Hge : (25 <= auxv_count (kb_rseq (in_kernel inp)))%nat)
      by (unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia).
    cbn [kentry_ok]. split; [lia|].
    unfold flat, estart. cbn [a_base a_off edenot]. rewrite ke3. rewrite Hau.
    split; [repeat split; lia|].
    cbn [adenot a_base a_off edenot]. rewrite ?ke3, ?ke4.
    erewrite <- (rd_auxv_main 49%nat (rndp inp sp0));
      [ f_equal
      | lia
      | cbn [auxv_words auxv_entries flat_map app nth fst snd]; reflexivity
      | cbn [a_base a_off edenot]; rewrite ke3; lia ].
  Qed.

  Lemma know_auxw : know_ok RSEGS E mem kn_auxw.
  Proof.
    unfold kn_auxw, know_ok.
    repeat apply Forall_cons; try apply Forall_nil;
      [ apply (kauxv_type 1 40)  | apply (kauxv_type 2 41)  | apply (kauxv_type 3 42)
      | apply (kauxv_type 4 43)  | apply (kauxv_type 5 44)  | apply (kauxv_type 6 45)
      | apply (kauxv_type 7 46)  | apply (kauxv_type 8 47)  | apply (kauxv_type 9 51)
      | apply (kauxv_type 10 16) | apply (kauxv_type 11 6)  | apply (kauxv_type 12 17)
      | apply (kauxv_type 13 3)  | apply (kauxv_type 14 4)  | apply (kauxv_type 15 5)
      | apply (kauxv_type 16 7)  | apply (kauxv_type 17 8)  | apply (kauxv_type 18 9)
      | apply (kauxv_type 19 11) | apply (kauxv_type 20 12) | apply (kauxv_type 21 13)
      | apply (kauxv_type 22 14) | apply (kauxv_type 23 23) | apply (kauxv_type 24 25)
      | apply (kauxv_type 25 31)
      | apply (kauxv_type 0 33)
      | exact kauxv_rnd ];
      first [ unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia
            | vm_compute; reflexivity ].
  Qed.

  (* The terminator words ([kn_termT] / [kn_termF]), as the disjunction of the two
     [kb_rseq] cases: the flag is case-split here and never fixed.  Each row is
     [kauxv_type] at an index below that case's [auxv_count] (26, 27, 28 < 29 with
     CONFIG_RSEQ, 26 < 27 without), and the word itself is read off [auxv_entries] once the
     launch record's [la_rseq] is the case's literal. *)
  Lemma know_auxv_term : know_ok RSEGS E mem kn_termT \/ know_ok RSEGS E mem kn_termF.
  Proof.
    destruct (kb_rseq (in_kernel inp)) eqn:Hr; [left | right]; unfold kn_termT, kn_termF, know_ok;
      repeat apply Forall_cons; try apply Forall_nil;
      [ apply (kauxv_type 26 27) | apply (kauxv_type 27 28) | apply (kauxv_type 28 0)
      | apply (kauxv_type 26 0) ];
      first [ unfold auxv_count; rewrite Hr; cbv beta iota; lia
            | generalize (eq_refl : la_rseq (launch_auxv inp sp0 mbase) = kb_rseq (in_kernel inp));
              rewrite Hr; destruct (launch_auxv inp sp0 mbase) as [la_e la_c la_m la_r];
              cbn [la_rseq]; intros ->; vm_compute; reflexivity ].
  Qed.


  (* [comment removed for export] *)
  Lemma D_main_auxvp : forall segs,
    rdn segs (D_main inp sp0 rnd tid) (Z_to_bv 64 0x64478) 8
    = Some (word_to_le_bytes 8 (auxvp inp sp0)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof kp_lo. pose proof kp_hi.
    unfold auxvp, D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  Lemma wseg_data : wseg_ok RSEGS (Z_to_bv 64 0x33000) 208896 = true.
  Proof. exact (wseg_fast_sound _ _ _ S0WsegData.wseg_fast_data). Qed.   (* [comment removed for export] *)

  Lemma range_disjoint_sub : forall lo n c i, range_disjoint_b lo n c = true ->
    (lo <= i)%Z -> (i + 1 <= lo + Z.of_nat n)%Z -> range_disjoint_b i 1 c = true.
  Proof.
    intros lo n [c w] i H Hlo Hhi. unfold range_disjoint_b in *. cbn [fst snd] in *.
    apply orb_true_iff in H. apply orb_true_iff. rewrite !Z.leb_le in *. cbn [Z.of_nat Pos.of_succ_nat]. lia.
  Qed.

  Lemma missb_sub : forall lo n i, D_main_missb lo n = true ->
    (lo <= i)%Z -> (i + 1 <= lo + Z.of_nat n)%Z -> D_main_missb i 1 = true.
  Proof.
    intros lo n i H Hlo Hhi. unfold D_main_missb in *.
    apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
    apply Z.leb_le in H2. apply Z.leb_le in H3.
    apply andb_true_iff; split; [apply andb_true_iff; split|]; [| apply Z.leb_le; lia | apply Z.leb_le; cbn [Z.of_nat Pos.of_succ_nat]; lia].
    apply forallb_forall. intros c Hc. apply (range_disjoint_sub lo n); [|lia|lia].
    apply (proj1 (forallb_forall _ _) H1). exact Hc.
  Qed.

  (* [comment removed for export] *)
  Lemma kimg_ok : forall lo hi, D_main_missb lo (Z.to_nat (hi - lo)) = true -> (lo <= hi)%Z -> (hi <= 0x66000)%Z ->
    kentry_ok RSEGS E mem (KImg lo hi).
  Proof.
    intros lo hi Hb Hle Hhi. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    assert (Hlo0 : (0 <= lo)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb].
      apply Z.leb_le in Hb. exact Hb. }
    cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    rewrite (main_entry_mem_data inp mbase entry sp0 rnd tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
    apply (D_main_none inp sp0 rnd tid i Hva); [lia | lia |].
    apply (missb_sub lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
  Qed.

  Ltac kimg := apply kimg_ok; [vm_compute; reflexivity | lia | lia].

  Ltac kw_pre :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
  Ltac kw_data L :=
    kw_pre;
    rewrite (main_entry_rdn_data inp mbase entry sp0 rnd tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    rewrite (L RSEGS); try reflexivity.
  Ltac kw_mem L := kw_pre; rewrite (L RSEGS); try reflexivity.

  (* [comment removed for export] *)
  Lemma kblob_static8 : forall (a : Z) (k : nat) bs,
    (0x10000 <= a)%Z -> (a + 8 <= 0x66000)%Z -> eb E k = bs -> length bs = 8%nat ->
    rdn [] mem (Z_to_bv 64 a) 8 = Some bs ->
    kentry_ok RSEGS E mem (KBlob (SA (ELit 0) a) (ELit 8) k).
  Proof.
    intros a k bs Ha Hb Hk Hlen Hr.
    apply (kblob_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0) a (ELit 8) k bs); cbn [edenot]; rewrite ?u_small by lia; try lia;
      try reflexivity; try exact Hk; try (rewrite Hlen; reflexivity).
    rewrite Hlen. intros i Hi.
    pose proof (rdn_pointwise_inv [] mem 8 (Z_to_bv 64 a) bs ltac:(intros j Hj; reflexivity)
                  ltac:(rewrite u_small by lia; lia) Hr (Z.to_nat i) ltac:(lia)) as Hp.
    rewrite u_small, Z2Nat.id in Hp by lia. rewrite Z.add_0_l. exact Hp.
  Qed.

  Lemma know_image : know_ok RSEGS E mem kn_image.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof (u64_range tid) as Ht.
    unfold kn_image, know_ok.
    repeat apply Forall_cons; try apply Forall_nil;
      try kimg;
      try (lazymatch goal with
           | |- kentry_ok _ _ _ (KBlob (SA (ELit 0) 0x441d0) _ _) =>
               apply (kblob_static8 0x441d0 3 (canary_bytes rnd)); [lia | lia | reflexivity | apply length_canary_bytes
                 | rewrite (main_entry_rdn_data inp mbase entry sp0 rnd tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
                   rewrite <- word_to_le_bytes_canary; apply (D_main_canary inp sp0 rnd tid)]
           | |- kentry_ok _ _ _ (KBlob (SA (ELit 0) 0x64450) _ _) =>
               apply (kblob_static8 0x64450 3 (canary_bytes rnd)); [lia | lia | reflexivity | apply length_canary_bytes
                 | apply (main_entry_guard inp mbase entry sp0 rnd tid Hlo regs mem ME)]
           | |- kentry_ok _ _ _ (KBlob (SA (ELit 0) 0x644d8) _ _) =>
               apply (kblob_static8 0x644d8 4 (word_to_le_bytes 8 hw)); [lia | lia | reflexivity | apply length_N_to_le_bytes
                 | rewrite (main_entry_rdn_data inp mbase entry sp0 rnd tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
                   apply (D_main_hwcap inp sp0 rnd tid Hva)]
           end);
      cbn [kentry_ok a_base a_off edenot]; rewrite ?ke3, ?ke5; unfold flat, estart, elenZ; cbn [a_base a_off edenot];
      rewrite ?(u_small 0) by lia; cbn [Z.add].
    - (* [comment removed for export] *) split; [lia|]. intros d m Hd Hm.
      eapply (store_ok_window RSEGS mem (Z_to_bv 64 0x33000) (Z_to_bv 64 (0x33000 + d)) 208896 m 0x33000 0x66000);
        [reflexivity | vm_cast_no_check (@eq_refl Z 0x66000%Z) | cbn; lia | apply wseg_data | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
    - kw_data (D_main_self inp sp0 rnd tid).
    - kw_mem (main_entry_tid inp mbase entry sp0 rnd tid Hlo regs mem ME).
    - kw_data D_main_auxvp.
    - kw_data (D_main_pagesize inp sp0 rnd tid Hva).
    - (* [comment removed for export] *) lia.
  Qed.


  Theorem main_know_ok : know_ok RSEGS E mem kn_main.
  Proof.
    unfold kn_main, know_ok.
    apply Forall_app; split; [apply know_stack|].
    apply Forall_app; split; [apply know_auxv|].
    apply Forall_app; split; [apply know_auxw | apply know_image].
  Qed.

  (* [main_know_ok] plus the [kb_rseq]-split terminator rows, and the fact that the auxv
     sits above sp0 (so the rows survive every store below it).  It is proved from
     [main_know_ok], so it takes exactly the same section arguments. *)
  Theorem main_know_term : (bv_unsigned sp0 <= bv_unsigned (auxvp inp sp0))%Z /\
    (know_ok RSEGS E mem (kn_main ++ kn_termT) \/ know_ok RSEGS E mem (kn_main ++ kn_termF)).
  Proof.
    split; [exact (proj1 auxvp_bounds)|].
    pose proof main_know_ok as HK.
    destruct know_auxv_term as [HT|HT]; [left | right];
      unfold know_ok in *; apply Forall_app; split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma main_str : forall k, (k < 2)%nat ->
    rdn RSEGS mem (cat_argv_ptr (ed_top rnd) (in_argv inp) envv (in_execfn inp) k) (length (nth k (in_argv inp) []) + 1) = Some (nth k (in_argv inp) [] ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr (ed_top rnd) (in_argv inp) envv (in_execfn inp) k))%Z
    /\ (bv_unsigned (cat_argv_ptr (ed_top rnd) (in_argv inp) envv (in_execfn inp) k) <= bv_unsigned sp0 + 2107576)%Z   (* [comment removed for export] *)
    /\ (Z.of_nat (length (nth k (in_argv inp) [])) <= 131071)%Z.
  Proof.
    intros k Hk. pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
    assert (Hk' : (k < length (in_argv inp))%nat) by (rewrite Hav; subst av; cbn; lia).
    destruct (argv_ptr_bounds Sv48 inp mbase sp0 brk rnd k Hlau Hk') as [B1 B2].
    assert (Hu : bv_unsigned (cat_argv_ptr (ed_top rnd) (in_argv inp) (in_envp inp) (in_execfn inp) k)
                 = (bv_unsigned sp0
                    + Z.of_nat (cat_string_off (kb_rseq (in_kernel inp)) sp0 (ed_top rnd)
                                  (in_argv inp) (in_envp inp) (in_execfn inp)
                                + total_arg_bytes_nat (firstn k (in_argv inp))))%Z)
      by (eapply (u_cat_argv_ptr Sv48 inp mbase RPH entry sp0 brk rnd); try eassumption;
          first [unfold sp_window_lo; lia | unfold sp_window_hi; lia]).
    (* RefLayout's Section Layout discharges (inp mbase ph entry sp brk rdraw);
       the call was missing [brk], so [rnd] landed on a word slot.  The
       lay_bsb_len call on the next line is the control for the order. *)
    pose proof (struct_av_bound inp mbase RPH entry sp0 brk rnd) as Hsb.
    pose proof (lay_bsb_len Sv48 inp mbase RPH entry sp0 brk rnd Hvl Hlau) as Hl.
    pose proof (total_arg_bytes_firstn_le k (in_argv inp)) as Hf.
    pose proof (valid_argv_str_len (in_argv inp) k Hva Hk') as Hlen.
    repeat split.
    - rewrite (main_entry_rdn_above inp mbase entry sp0 rnd tid regs mem ME) by lia.
      pose proof (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rnd) as Hw. unfold wmem in Hw. rewrite Hw by lia.
      pose proof (read_argv_cstr_k Sv48 RSEGS inp mbase RPH entry sp0 brk rnd k Hlau Hk') as Hc.
      exact Hc.
    - exact B1.
    - lia.
    - exact Hlen.
  Qed.
End KnowProofs.

(* At the revision the argv strings sit at the top of the stack VMA, below
   [ed_top], which [entry_launch_ok_va] bounds by the Sv48 stack top. *)
Lemma argv_ptr_fits : forall inp mbase (sp brk : word) rnd k,
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
  (k < length (in_argv inp))%nat ->
  (bv_unsigned (cat_argv_ptr (ed_top rnd) (in_argv inp) (in_envp inp) (in_execfn inp) k)
   + Z.of_nat (length (nth k (in_argv inp) [])) + 1 <= 0x800000000000)%Z.
Proof.
  intros inp mbase sp brk rnd k Hlaunch Hk.
  pose proof (launch_string_base_arith Sv48 inp mbase sp brk rnd Hlaunch) as HA.
  pose proof (u_cat_string_base Sv48 inp mbase sp brk rnd Hlaunch) as Hu.
  pose proof (u64_range sp). pose proof (u64_range (ed_top rnd)).
  pose proof (Nat2Z.is_nonneg
    (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))).
  pose proof (Nat2Z.is_nonneg (total_arg_bytes_nat (firstn k (in_argv inp)))).
  assert (Hstr : (Z.of_nat (total_arg_bytes_nat (firstn k (in_argv inp)))
                  + Z.of_nat (length (nth k (in_argv inp) [])) + 1
                  <= Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                 (in_execfn inp)))%Z).
  { pose proof (total_arg_bytes_firstn_within (in_argv inp) k Hk) as Hw.
    unfold launch_string_bytes. rewrite length_flatten_strings.
    pose proof (Nat2Z.is_nonneg (length (flatten_strings (in_envp inp)))).
    pose proof (Nat2Z.is_nonneg (length (in_execfn inp))).
    lia. }
  cbn [entry_launch_ok_va] in Hlaunch. destruct Hlaunch as ((_ & Htop & _) & _).
  assert (Hv : (va_stack_top Sv48 <= 0x800000000000)%Z) by (unfold Z.le; vm_compute; discriminate).
  rewrite (cat_argv_ptr_offset _ _ _ _ k Hk), word_add_nat_Z2bv, Hu.
  rewrite u_Z2bv_lt by lia.
  lia.
Qed.

(* What the main phase's consumers hold about the launch, in one hypothesis:
   the hwcap word they name, the launch facts [ref_startup] passes on, and
   the state at [main]'s first instruction.  The entry point is the image's
   own ([ref_startup]). *)
Definition main_launch (inp : ProcInput) (hw mbase sp0 brk : word) (rnd : EntryDraw) (tid : word)
    (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  in_hwcap inp = hw /\ valid_launch inp /\ entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rnd) inp
  /\ main_entry inp mbase (0x13434 : word) sp0 rnd tid regs mem.
