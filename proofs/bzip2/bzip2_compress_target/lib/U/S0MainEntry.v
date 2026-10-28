(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require WsegFast PropExec CatExec CatSim SeqExec StoreOk FileSim ArgvEnv SymExec SymExec2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymRun.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymRun SymDrive MemSplit RefLayout StartupTac StartupRnd U.S0StartupDefs U.S0Startup.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require StartupTac ArgvEnv RefLayout StartupRnd U.S0StartupDefs U.S0Startup.
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
Import OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StartupTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ArgvEnv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefLayout OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StartupRnd OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0StartupDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Startup.
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
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable uid : word.   (* [comment removed for export] *)
  Variable hw : word.    (* [comment removed for export] *)
  Variable rnd : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.

  Let D := D_main sp0 av ev hw rnd tid.

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
  Hypothesis ME : main_entry sp0 av ev uid hw rnd tid regs mem.

  (* [comment removed for export] *)

  Lemma main_entry_tid : forall segs,
    rdn segs mem (Z_to_bv 64 0x44138) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. rewrite (main_entry_rdn_data sp0 av ev uid hw rnd tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_tid.
  Qed.

  Lemma main_entry_guard : forall segs,
    rdn segs mem (Z_to_bv 64 0x64450) 8 = Some (canary_bytes rnd).
  Proof.
    intros segs. rewrite (main_entry_rdn_data sp0 av ev uid hw rnd tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_guard.
  Qed.
End Facts.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S0StartupFacts.

Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.WsegFast OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.FileSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ArgvEnv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymRun.SymExec2Sound OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymRun OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymDrive OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MemSplit OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefLayout OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StartupTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StartupRnd OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0StartupDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Startup OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0MainEntry.S0StartupFacts.
Import ListNotations.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require NatLitLia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0WsegData.   (* [comment removed for export] *)
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
Open Scope bv_scope.
Import SX2. Import SX2S.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma D_main_none : forall sp0 av ev hw rnd tid (i : Z),
  valid_argv av -> (0x7fff80000000 <= bv_unsigned sp0)%Z -> (bv_unsigned sp0 <= 0x800000000000)%Z ->
  D_main_missb i 1 = true ->
  D_main sp0 av ev hw rnd tid (Z_to_bv 64 i) = None.
Proof.
  intros sp0 av ev hw rnd tid i Hva Hlo Hhi Hb. pose proof (u64_range hw) as Hhw.
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

Section MainEntry.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable ev : list (list byte).
  Variable uid : word.   (* [comment removed for export] *)
  Variable hw : word.    (* [comment removed for export] *)
  Variable rnd : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av ev uid hw rnd tid regs mem.

  Let Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  Definition p0 : word := cat_argv_ptr sp0 av ev 0.
  Definition p1 : word := cat_argv_ptr sp0 av ev 1.
  Definition auxvp : word := auxv_w sp0 av ev.
  Definition rndp : word := at_random_ptr sp0 av ev.

  (* [comment removed for export] *)
  Definition vals0 : list word := [sp0; p0; p1; auxvp; rndp; tid] ++ junk_vals regs.
  Definition blobs0 : list (list byte) :=
    [a0s ++ [Z_to_bv 8 0]; path ++ [Z_to_bv 8 0]; at_random_bytes (ed_random rnd); canary_bytes rnd; word_to_le_bytes 8 hw].
  Definition E0 : env := Env (vals_ev vals0) (blobs_ev blobs0).

  Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

  Definition sr_main : list expr :=
    [ELit 0; ELit 0x28c48; spx (-48); ELit 0x10800; ELit 0x441e0; EVar 11; EVar 12; EVar 13;
     spx 8; ELit 2; ELit 2; spx 8; spx 32; EVar 19; EVar 20; EVar 21;
     EVar 22; EVar 23; ELit 0x13580; spx 32; ELit 0; ELit 0; ELit 0; ELit 0;
     ELit 0; ELit 0; ELit 0; ELit 0; EVar 34; EVar 35; EVar 36; EVar 37].

  Definition kn_stack : list kentry :=
    [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
     KWr (SA (EVar 0) (-8388608)) 8388608;
     KWord (SA (EVar 0) 0) 8 (ELit 2); KWord (SA (EVar 0) 8) 8 (EVar 1);
     KWord (SA (EVar 0) 16) 8 (EVar 2); KWord (SA (EVar 0) 24) 8 (ELit 0)].

  Definition kn_auxv : list kentry :=
    [KRange (EVar 3) 0x7fff80000000 0x800000400000; KRange (EVar 4) 0x7fff80000000 0x800000400000;
     KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 3) 0) 160;
     KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 4) 0) 16;
     (* [comment removed for export] *)
     KDisj (SA (EVar 0) (-4294967296)) 4294967296 (SA (EVar 3) 0) 160;
     KDisj (SA (EVar 0) (-4294967296)) 4294967296 (SA (EVar 4) 0) 16;
     KAlign (EVar 3) 8; KAlign (EVar 4) 8;
     (* [comment removed for export] *)
     KWord (SA (EVar 3) 0) 8 (ELit 3); KWord (SA (EVar 3) 8) 8 (ELit 0x10040);
     KWord (SA (EVar 3) 16) 8 (ELit 4); KWord (SA (EVar 3) 24) 8 (ELit 56);
     KWord (SA (EVar 3) 32) 8 (ELit 5); KWord (SA (EVar 3) 40) 8 (ELit 10);
     KWord (SA (EVar 3) 48) 8 (ELit 16); KBlob (SA (EVar 3) 56) (ELit 8) 4;
     KWord (SA (EVar 3) 64) 8 (ELit 6); KWord (SA (EVar 3) 72) 8 (ELit 4096);
     KWord (SA (EVar 3) 80) 8 (ELit 11); (* [comment removed for export] *)
     KWord (SA (EVar 3) 96) 8 (ELit 12);
     KWord (SA (EVar 3) 112) 8 (ELit 23); KWord (SA (EVar 3) 120) 8 (ELit 0);
     KWord (SA (EVar 3) 128) 8 (ELit 25); KWord (SA (EVar 3) 136) 8 (EVar 4);
     KWord (SA (EVar 3) 144) 8 (ELit 0); KWord (SA (EVar 3) 152) 8 (ELit 0);
     KBlob (SA (EVar 4) 0) (ELit 16) 2].

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
  Definition kn_main : list kentry := kn_stack ++ kn_auxv ++ kn_image.
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
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable uid : word.   (* [comment removed for export] *)
  Variable hw : word.    (* [comment removed for export] *)
  Variable rnd : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv uid hw rnd tid regs mem.

  Let E := E0 sp0 a0s path envv hw rnd tid regs.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma ev_vals : forall n, ev E n = nth n ([sp0; p0 sp0 a0s path envv; p1 sp0 a0s path envv; auxvp sp0 a0s path envv; rndp sp0 a0s path envv; tid] ++ junk_vals regs) (Z_to_bv 64 0).
  Proof. intros n. reflexivity. Qed.

  Lemma ev_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. rewrite ev_vals. change (6 + i)%nat with (length [sp0; p0 sp0 a0s path envv; p1 sp0 a0s path envv; auxvp sp0 a0s path envv; rndp sp0 a0s path envv; tid] + i)%nat.
    rewrite app_nth2_plus. unfold junk_vals. rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.

  Lemma spx_val : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
  Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev E 0) with sp0.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

End MainEntryProofs.

Section MainRegs.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable uid : word.   (* [comment removed for export] *)
  Variable hw : word.    (* [comment removed for export] *)
  Variable rnd : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv uid hw rnd tid regs mem.
  Let E := E0 sp0 a0s path envv hw rnd tid regs.

  Ltac reg_case :=
    cbn [nth sr_main all_regs];
          first [ rewrite (spx_val sp0 a0s path envv hw rnd tid regs)
                | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                    change (edenot E (EVar n)) with (ev E n);
                    first [ rewrite (ev_junk sp0 a0s path envv hw rnd tid regs (n - 6)) by lia; reflexivity | idtac ]
                  | |- _ => cbn [edenot] end ];
          first [ reflexivity
                | exact (me_ra _ _ _ _ _ _ _ _ _ ME) | exact (me_gp _ _ _ _ _ _ _ _ _ ME) | exact (me_tp _ _ _ _ _ _ _ _ _ ME)
                | exact (me_s2 _ _ _ _ _ _ _ _ _ ME)
                | rewrite (me_sp _ _ _ _ _ _ _ _ _ ME); apply bv_eq; rewrite !u_small by lia; lia
                | rewrite (me_s0 _ _ _ _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a1 _ _ _ _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a2 _ _ _ _ _ _ _ _ _ ME); f_equal; subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s3 _ _ _ _ _ _ _ _ _ ME); f_equal; subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s1 _ _ _ _ _ _ _ _ _ ME); unfold argcN, len_word; reflexivity
                | rewrite (me_a0 _ _ _ _ _ _ _ _ _ ME); unfold argcN, len_word; reflexivity
                | apply (me_szero _ _ _ _ _ _ _ _ _ ME); cbn; tauto
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
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable uid : word.   (* [comment removed for export] *)
  Variable hw : word.    (* [comment removed for export] *)
  Variable rnd : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv uid hw rnd tid regs mem.
  Let E := E0 sp0 a0s path envv hw rnd tid regs.

  Lemma kp_lo : (0x7fff80000000 <= bv_unsigned sp0)%Z. Proof. exact (proj1 Hvsp). Qed.
  Lemma kp_hi : (bv_unsigned sp0 <= 0x800000000000)%Z. Proof. exact (proj1 (proj2 Hvsp)). Qed.
  Lemma kp_al : (bv_unsigned sp0 mod 16 = 0)%Z. Proof. exact (proj2 (proj2 Hvsp)). Qed.
  Lemma ke0 : ev E 0 = sp0. Proof. reflexivity. Qed.
  Lemma ke1 : ev E 1 = p0 sp0 a0s path envv. Proof. reflexivity. Qed.
  Lemma ke2 : ev E 2 = p1 sp0 a0s path envv. Proof. reflexivity. Qed.
  Lemma ke3 : ev E 3 = auxvp sp0 a0s path envv. Proof. reflexivity. Qed.
  Lemma ke4 : ev E 4 = rndp sp0 a0s path envv. Proof. reflexivity. Qed.
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
      apply (main_entry_store_ok_win sp0 av envv uid hw rnd tid regs mem ME); rewrite u_small by lia; unfold stack_max_size; lia.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite (main_entry_rdn_above sp0 av envv uid hw rnd tid regs mem ME) by lia.
      pose proof (read_argc_w RSEGS RPH sp0 av envv uid hw rnd Hva) as Hr. unfold wmem in Hr.
      rewrite (Hr Hve) by (unfold sp_window_hi; lia).
      rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above sp0 av envv uid hw rnd tid regs mem ME) by (rewrite u_small by lia; lia).
      pose proof (read_argv_ptr_w RSEGS RPH sp0 av envv uid hw rnd Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 0%nat ltac:(subst av; cbn; lia)) as Hr.
      unfold wmem in Hr. rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above sp0 av envv uid hw rnd tid regs mem ME) by (rewrite u_small by lia; lia).
      pose proof (read_argv_ptr_w RSEGS RPH sp0 av envv uid hw rnd Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 1%nat ltac:(subst av; cbn; lia)) as Hr.
      unfold wmem in Hr. rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 1)) with 16%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above sp0 av envv uid hw rnd tid regs mem ME) by (rewrite u_small by lia; lia).
      pose proof (read_argv_null RSEGS RPH sp0 av envv uid hw rnd Hva Hve ltac:(unfold sp_window_hi; lia)) as Hr.
      rewrite w_add_nat in Hr. subst av. change (Z.of_nat (8 + 8 * length [a0s; path])) with 24%Z in Hr.
      rewrite <- (rdn_wmem_stack RSEGS RPH sp0 [a0s; path] envv uid hw rnd) in Hr by (try rewrite u_small by lia; lia).
      unfold wmem in Hr. rewrite n_to_le_8_spec in Hr. exact Hr.
  Qed.

  Lemma auxvp_eq : auxvp sp0 a0s path envv = Z_to_bv 64 (bv_unsigned sp0 + Z.of_nat (auxv_off av envv)).
  Proof. unfold auxvp, auxv_w, auxv_off. subst av. cbn [length]. f_equal. lia. Qed.

  Lemma auxvp_u : bv_unsigned (auxvp sp0 a0s path envv) = (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z
    /\ (Z.of_nat (auxv_off av envv) + 176 <= 2240000)%Z.
  Proof.
    pose proof kp_lo. pose proof kp_hi.
    pose proof (auxv_off_bound RPH sp0 av envv uid hw rnd) as Hb.
    pose proof (lay_bsb_len RPH sp0 av envv uid hw rnd Hva Hve) as Hl.
    rewrite auxvp_eq. rewrite u_small by lia. lia.
  Qed.

  Lemma rnd_u : (bv_unsigned sp0 <= bv_unsigned (rndp sp0 a0s path envv))%Z
    /\ (bv_unsigned (rndp sp0 a0s path envv) + 16 <= bv_unsigned sp0 + 2240000)%Z
    /\ (bv_unsigned (rndp sp0 a0s path envv) mod 8 = 0)%Z
    /\ (forall j n, (j + n <= 16)%nat ->
          rdn RSEGS (stack_to_mem sp0 (entry_stack_image RPH sp0 av envv uid hw rnd))
              (Z_to_bv 64 (bv_unsigned (rndp sp0 a0s path envv) + Z.of_nat j)) n = Some (firstn n (skipn j (at_random_bytes (ed_random rnd))))).
  Proof.
    pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    pose proof (lay_bsb_len RPH sp0 av envv uid hw rnd Hva Hve) as Hl.
    cps_destruct (rnd_facts RSEGS RPH sp0 av envv uid hw rnd Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) kp_al)
      as (A & B & C & D & F).
    unfold rndp. subst av. repeat split; try assumption; try lia.
  Qed.

  Lemma auxv_word_at : forall j, (j < 20)%nat ->
    rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat j)) 8
    = Some (word_to_le_bytes 8 (nth j (auxv_words RPH (rndp sp0 a0s path envv) uid hw) (Z_to_bv 64 0))).
  Proof.
    intros j Hj. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    destruct auxvp_u as [Hu Hb].
    rewrite (main_entry_rdn_above sp0 av envv uid hw rnd tid regs mem ME) by (rewrite u_small by lia; lia).
    pose proof (rdn_wmem_stack RSEGS RPH sp0 av envv uid hw rnd) as Hw. unfold wmem in Hw.
    rewrite Hw by (rewrite u_small by lia; lia).
    replace (Z_to_bv 64 (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat j))
      with (sp0 + nat_to_word (auxv_off av envv + 8 * j)) by (rewrite w_add_nat; f_equal; lia).
    rewrite (read_auxv_word RSEGS RPH sp0 av envv uid hw rnd Hva Hve ltac:(unfold sp_window_hi; lia) j Hj).
    rewrite n_to_le_8_spec. unfold rndp. reflexivity.
  Qed.

  Ltac kw_auxv j :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; rewrite ke3; unfold v_addi;
    lazymatch goal with |- rdn _ _ (Z_to_bv 64 (?u + ?k)) 8 = _ =>
      replace k with (8 * Z.of_nat j)%Z by reflexivity end;
    rewrite (auxv_word_at j) by lia; unfold auxv_words; cbn [nth]; try reflexivity.

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
    - kw_auxv 0%nat. - kw_auxv 1%nat. - kw_auxv 2%nat. - kw_auxv 3%nat. - kw_auxv 4%nat. - kw_auxv 5%nat.
    - kw_auxv 6%nat.
    - (* [comment removed for export] *)
      rewrite u_small by lia. split; [lia|]. change (eb E 4) with (word_to_le_bytes 8 hw). split; [rewrite length_N_to_le_bytes; reflexivity|].
      intros i Hi.
      pose proof (auxv_word_at 7%nat ltac:(lia)) as Hw7. unfold auxv_words in Hw7. cbn [nth flat_map fst snd auxv_entries app] in Hw7.
      pose proof (rdn_pointwise_inv RSEGS mem 8 (Z_to_bv 64 (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat 7)) _
                    ltac:(intros j Hj; rewrite (u_small (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat 7)) by lia;
                          apply seg_rom_high; rewrite u_small by lia; lia)
                    ltac:(rewrite u_small by lia; lia) Hw7 (Z.to_nat i) ltac:(lia)) as Hp.
      rewrite Z2Nat.id, u_small in Hp by lia. rewrite Hau in Hp.
      replace (bv_unsigned sp0 + Z.of_nat (auxv_off av envv) + 56 + i)%Z
        with (bv_unsigned sp0 + Z.of_nat (auxv_off av envv) + 8 * Z.of_nat 7 + i)%Z by lia.
      rewrite Hp. reflexivity.
    - kw_auxv 8%nat. - kw_auxv 9%nat. - kw_auxv 10%nat. - kw_auxv 12%nat.
    - kw_auxv 14%nat. - kw_auxv 15%nat. - kw_auxv 16%nat. - kw_auxv 17%nat. - kw_auxv 18%nat. - kw_auxv 19%nat.
    - (* [comment removed for export] *)
      rewrite u_small by lia. split; [lia|]. change (eb E 2) with (at_random_bytes (ed_random rnd)). split; [rewrite length_at_random_bytes; reflexivity|]. intros i Hi.
      assert (Hr : rdn RSEGS mem (rndp sp0 a0s path envv) 16 = Some (at_random_bytes (ed_random rnd))).
      { rewrite (main_entry_rdn_above sp0 av envv uid hw rnd tid regs mem ME) by lia.
        pose proof (rdn_wmem_stack RSEGS RPH sp0 av envv uid hw rnd) as Hw. unfold wmem in Hw.
        rewrite Hw by lia.
        pose proof (Hr4 0%nat 16%nat ltac:(lia)) as H16. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H16.
        rewrite H16. f_equal. }
      pose proof (rdn_pointwise_inv RSEGS mem 16 (rndp sp0 a0s path envv) _
                    ltac:(intros j Hj; apply seg_rom_high; rewrite u_small by lia; lia)
                    ltac:(lia) Hr (Z.to_nat i) ltac:(lia)) as Hp.
      rewrite Z2Nat.id in Hp by lia.
      replace (bv_unsigned (rndp sp0 a0s path envv) + 0 + i)%Z with (bv_unsigned (rndp sp0 a0s path envv) + i)%Z by lia.
      rewrite Hp. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_auxvp : forall segs,
    rdn segs (D_main sp0 av envv hw rnd tid) (Z_to_bv 64 0x64478) 8
    = Some (word_to_le_bytes 8 (auxvp sp0 a0s path envv)).
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
    rewrite (main_entry_mem_data sp0 av envv uid hw rnd tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
    apply (D_main_none sp0 av envv hw rnd tid i Hva); [lia | lia |].
    apply (missb_sub lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
  Qed.

  Ltac kimg := apply kimg_ok; [vm_compute; reflexivity | lia | lia].

  Ltac kw_pre :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
  Ltac kw_data L :=
    kw_pre;
    rewrite (main_entry_rdn_data sp0 av envv uid hw rnd tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
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
                 | rewrite (main_entry_rdn_data sp0 av envv uid hw rnd tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
                   rewrite <- word_to_le_bytes_canary; apply (D_main_canary sp0 av envv hw rnd tid)]
           | |- kentry_ok _ _ _ (KBlob (SA (ELit 0) 0x64450) _ _) =>
               apply (kblob_static8 0x64450 3 (canary_bytes rnd)); [lia | lia | reflexivity | apply length_canary_bytes
                 | apply (main_entry_guard sp0 av envv uid hw rnd tid Hlo regs mem ME)]
           | |- kentry_ok _ _ _ (KBlob (SA (ELit 0) 0x644d8) _ _) =>
               apply (kblob_static8 0x644d8 4 (word_to_le_bytes 8 hw)); [lia | lia | reflexivity | apply length_N_to_le_bytes
                 | rewrite (main_entry_rdn_data sp0 av envv uid hw rnd tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
                   apply (D_main_hwcap sp0 av envv hw rnd tid Hva)]
           end);
      cbn [kentry_ok a_base a_off edenot]; rewrite ?ke3, ?ke5; unfold flat, estart, elenZ; cbn [a_base a_off edenot];
      rewrite ?(u_small 0) by lia; cbn [Z.add].
    - (* [comment removed for export] *) split; [lia|]. intros d m Hd Hm.
      eapply (store_ok_window RSEGS mem (Z_to_bv 64 0x33000) (Z_to_bv 64 (0x33000 + d)) 208896 m 0x33000 0x66000);
        [reflexivity | vm_cast_no_check (@eq_refl Z 0x66000%Z) | cbn; lia | apply wseg_data | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
    - kw_data (D_main_self sp0 av envv hw rnd tid).
    - kw_mem (main_entry_tid sp0 av envv uid hw rnd tid Hlo regs mem ME).
    - kw_data D_main_auxvp.
    - kw_data (D_main_pagesize sp0 av envv hw rnd tid Hva).
    - (* [comment removed for export] *) lia.
  Qed.


  Theorem main_know_ok : know_ok RSEGS E mem kn_main.
  Proof.
    unfold kn_main, know_ok.
    apply Forall_app; split; [apply know_stack|].
    apply Forall_app; split; [apply know_auxv | apply know_image].
  Qed.

  (* [comment removed for export] *)
  Lemma main_str : forall k, (k < 2)%nat ->
    rdn RSEGS mem (cat_argv_ptr sp0 av envv k) (length (nth k av []) + 1) = Some (nth k av [] ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr sp0 av envv k))%Z
    /\ (bv_unsigned (cat_argv_ptr sp0 av envv k) <= bv_unsigned sp0 + 2107576)%Z   (* [comment removed for export] *)
    /\ (Z.of_nat (length (nth k av [])) <= 131071)%Z.
  Proof.
    intros k Hk. pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
    pose proof (lay_bsb_nw RPH sp0 av envv uid hw rnd Hva Hve ltac:(unfold sp_window_hi; lia)) as Hnw.
    assert (Hk' : (k < length av)%nat) by (subst av; cbn; lia).
    destruct (argv_ptr_bounds_at sp0 av envv Hva Hve ltac:(unfold sp_window_hi; lia) k Hk') as [B1 B2].
    pose proof (u_cat_argv_ptr sp0 av envv Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
    pose proof (struct_av_bound av envv Hva Hve) as Hsb.
    pose proof (total_arg_bytes_firstn_le k av) as Hf.
    pose proof (argv_str_len av Hva k Hk') as Hlen.
    repeat split.
    - rewrite (main_entry_rdn_above sp0 av envv uid hw rnd tid regs mem ME) by lia.
      pose proof (rdn_wmem_stack RSEGS RPH sp0 av envv uid hw rnd) as Hw. unfold wmem in Hw. rewrite Hw by lia.
      apply read_argv_cstr_k; [exact Hk' | exact Hnw].
    - exact B1.
    - lia.
    - exact Hlen.
  Qed.
End KnowProofs.
