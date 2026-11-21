(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the main-entry facts over the launch input ProcInput, its entry draw and the launch facts valid_launch and entry_launch_ok_va; the 27/29-pair auxv type words, the rseq-split terminator and AT_RANDOM's value word recorded at their new offsets; the stack window shrunk to the 6144512 bytes below sp0 the launch zero-fills; adds argv_ptr_fits and main_launch), as bzip2/bzip2_compress_target's main-entry facts were; and launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Exvwg.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Amb PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require ArgvEnv SymExec SymExec2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive MemSplit RefL1zx Star5ef D_St4s2 D_Stmwg.

Module D_Stw4n.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Amb
  Star5ef ArgvEnv RefL1zx D_St4s2 D_Stmwg.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RPH := Plain.M.phdrs.

(* [comment removed for export] *)
Definition D_main_cells : list (Z * nat) :=
  [(0x42088%Z, 8%nat); (0x623f0%Z, 8%nat); (0x62450%Z, 8%nat); (0x62418%Z, 8%nat); (0x623e0%Z, 8%nat); (0x623d8%Z, 8%nat); (0x62180%Z, 8%nat); (0x62190%Z, 8%nat); (0x62188%Z, 8%nat); (0x62400%Z, 8%nat); (0x62408%Z, 8%nat); (0x42168%Z, 8%nat); (0x42150%Z, 8%nat); (0x42090%Z, 8%nat); (0x623e8%Z, 1%nat); (0x420b8%Z, 4%nat); (0x420b0%Z, 4%nat); (0x42128%Z, 8%nat); (0x42108%Z, 8%nat); (0x42098%Z, 8%nat); (0x420a0%Z, 8%nat); (0x420a8%Z, 8%nat); (0x623c8%Z, 4%nat); (0x623cc%Z, 4%nat); (0x623c9%Z, 1%nat); (0x42148%Z, 8%nat); (0x317b0%Z, 1%nat)].

Definition range_disjoint_b (a : Z) (n : nat) (c : Z * nat) : bool :=
  ((a + Z.of_nat n <=? fst c) || (fst c + Z.of_nat (snd c) <=? a))%Z.

Definition D_main_missb (a : Z) (n : nat) : bool :=
  forallb (range_disjoint_b a n) D_main_cells && (0 <=? a)%Z && (a + Z.of_nat n <=? 0x70000)%Z.

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
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Local Notation av := (in_argv inp) (only parsing).
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.

  Local Notation R16 := (at_random_bytes (ed_random rdraw)) (only parsing).
  Let D := D_main inp sp0 rdraw tid.

  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Ltac hitD :=
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc;
    pose proof len_av;
    peel; first [ apply rdn_wbytes_hit8; unorm; lia
                | match goal with |- rdn _ (wbytes _ ?a ?bs) ?a _ = _ =>
                    rewrite <- (length_N_to_le_bytes 4) at 1; apply rdn_wbytes_hit; rewrite length_N_to_le_bytes; unorm; lia end ].

  (* [comment removed for export] *)
  Lemma D_main_tid : forall segs,
    rdn segs D (Z_to_bv 64 0x420b0) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 tid)) as Hh.
    rewrite length_N_to_le_bytes in Hh. apply Hh. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_guard : forall segs,
    rdn segs D (Z_to_bv 64 0x623c8) 8 = Some (guard_bytes R16).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rd_guard3; rewrite length_N_to_le_bytes; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_guard_at : forall i, (0 <= i < 8)%Z ->
    D (Z_to_bv 64 (0x623c8 + i)) = Some (nth (Z.to_nat i) (guard_bytes R16) (Z_to_bv 8 0)).
  Proof.
    intros i Hi. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
    rewrite 2 MemSplit.wbytes_outside by
      (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; imm_norm; unorm; lia).
    apply guard3_at; [rewrite length_N_to_le_bytes; reflexivity | rewrite length_N_to_le_bytes; reflexivity | exact Hi].
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_pagesize : forall segs,
    rdn segs D (Z_to_bv 64 0x62418) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 4096)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof len_av. subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma D_main_self : forall segs,
    rdn segs D (Z_to_bv 64 0x42090) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x42090)).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma D_main_canary_at : forall i, (0 <= i < 8)%Z ->
    D (Z_to_bv 64 (0x42148 + i)) = Some (nth (Z.to_nat i) (word_to_le_bytes 8 (canary_w R16)) (Z_to_bv 8 0)).
  Proof.
    intros i Hi. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp.
    rewrite MemSplit.wbytes_outside by
      (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; imm_norm; unorm; lia).
    rewrite MemSplit.wbytes_inside by
      (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; imm_norm; unorm; lia).
    f_equal. f_equal. imm_norm. unorm. lia.
  Qed.

  (* [comment removed for export] *)
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry inp mbase entry sp0 rdraw tid regs mem.

  (* [comment removed for export] *)

  #[using="ME regs D Hlo"] Lemma main_entry_tid : forall segs,
    rdn segs mem (Z_to_bv 64 0x420b0) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. rewrite (main_entry_rdn_data inp mbase entry sp0 rdraw tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_tid.
  Qed.

  (* [comment removed for export] *)
End Facts.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End D_Stw4n.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Amb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim.FileSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ArgvEnv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MemSplit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefL1zx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Star5ef OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_St4s2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Stmwg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Manqc.D_Stw4n.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma D_main_none : forall inp sp0 rnd tid (i : Z),
  valid_argv (in_argv inp) -> (0x7fff80000000 <= bv_unsigned sp0)%Z -> (bv_unsigned sp0 <= 0x800000000000)%Z ->
  D_main_missb i 1 = true ->
  D_main inp sp0 rnd tid (Z_to_bv 64 i) = None.
Proof.
  intros inp sp0 rnd tid i Hva Hlo Hhi Hb.
  pose proof (u64_range tid) as Ht. pose proof (u64_range (in_hwcap inp)) as Hhw.
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
Lemma seg_rom_high : forall (a : word), (0x63000 <= bv_unsigned a)%Z -> seg_rom RSEGS a = None.
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

(* [comment removed for export] *)
Lemma total_arg_bytes_firstn_S : forall k (l : list (list byte)), (k < length l)%nat ->
  total_arg_bytes_nat (firstn (S k) l) = (total_arg_bytes_nat (firstn k l) + (length (nth k l []) + 1))%nat.
Proof.
  induction k as [|k IH]; intros l Hk.
  - destruct l as [|s rest]; [cbn in Hk; lia|].
    change (firstn 1 (s :: rest)) with [s]. change (firstn 0 (s :: rest)) with (@nil (list byte)). cbn [nth].
    rewrite total_arg_bytes_cons. change (total_arg_bytes_nat []) with 0%nat. lia.
  - destruct l as [|s rest]; [cbn in Hk; lia|]. cbn [length] in Hk.
    change (firstn (S (S k)) (s :: rest)) with (s :: firstn (S k) rest).
    change (firstn (S k) (s :: rest)) with (s :: firstn k rest).
    rewrite !total_arg_bytes_cons. rewrite (IH rest) by lia. cbn [nth]. lia.
Qed.

Section MainEntry.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 brk : word.
  Variables a0s path : list byte.
  Variable rdraw : EntryDraw.
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
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry inp mbase entry sp0 rdraw tid regs mem.
  Local Notation R16 := (at_random_bytes (ed_random rdraw)) (only parsing).

  Let Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  Definition p0 : word := cat_argv_ptr (ed_top rdraw) (in_argv inp) ev (in_execfn inp) 0.
  Definition p1 : word := cat_argv_ptr (ed_top rdraw) (in_argv inp) ev (in_execfn inp) 1.
  Definition auxvp : word := auxv_w inp sp0.
  Definition rnd : word := at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) ev.

  (* [comment removed for export] *)
  Definition vals0 : list word := [sp0; p0; p1; auxvp; rnd; tid] ++ junk_vals regs.
  Definition blobs0 : list (list byte) := [a0s ++ [Z_to_bv 8 0]; path ++ [Z_to_bv 8 0]; guard_bytes R16].
  Definition E0 : env := Env (vals_ev vals0) (blobs_ev blobs0).

  Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

  Definition sr_main : list expr :=
    [ELit 0; ELit 0x223dc; spx (-48); ELit 0x10800; ELit 0x42158; EVar 11; EVar 12; EVar 13;
     spx 8; ELit 2; ELit 2; spx 8; spx 32; EVar 19; EVar 20; EVar 21;
     EVar 22; EVar 23; ELit 0x17b64; spx 32; ELit 0; ELit 0; ELit 0; ELit 0;
     ELit 0; ELit 0; ELit 0; ELit 0; EVar 34; EVar 35; EVar 36; EVar 37].

  Definition kn_stack : list kentry :=
    [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
     (* At 727298f3 the launch zero-fills, and so [main_entry_store_ok_win] certifies, only
        [MemSplit.wok_lo sp0, sp0) = [sp0 - 6144513, sp0) below sp0 (was 8388608 bytes, the
        allocator ceiling); the window is the 16-aligned 6144512 bytes inside it.  BYTES. *)
     KWr (SA (EVar 0) (-6144512)) 6144512;
     KWord (SA (EVar 0) 0) 8 (ELit 2); KWord (SA (EVar 0) 8) 8 (EVar 1);
     KWord (SA (EVar 0) 16) 8 (EVar 2); KWord (SA (EVar 0) 24) 8 (ELit 0)].

  Definition kn_auxv : list kentry :=
    [KRange (EVar 3) 0x7fff80000000 0x800000400000; KRange (EVar 4) 0x7fff80000000 0x800000400000;
     (* The 727298f3 vector is 27 pairs, 29 under CONFIG_RSEQ: at most 2 * 29 * 8 = 464 bytes
        (was 160, the old ten pairs).  A disjointness fact: the 8388608 stays. *)
     KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 3) 0) 464;
     KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 4) 0) 16;
     (* The old ten-pair vector's words are not recorded: at 727298f3 they sit elsewhere.
        The type words of the new vector and AT_RANDOM's value word are [kn_auxw] below. *)
     KAlign (EVar 3) 8; KAlign (EVar 4) 8].

  (* The auxv a_type words at the revision's slot indices (entry j's type at 16 * j), and
     AT_RANDOM's value word (entry 24, at 24 * 16 + 8 = 392), as bzip2/bzip2_compress_target
     records them for its getauxval(AT_RANDOM) walk.  The types of entries 0..25 are
     33 40 41 42 43 44 45 46 47 51 16 6 17 3 4 5 7 8 9 11 12 13 14 23 25 31 ([auxv_entries]);
     every row sits strictly below the AT_RSEQ pairs and AT_NULL, so [kb_rseq] stays free.
     Each row is proved from the launch below, and the main-phase walks are checked against
     exactly these rows. *)
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
     KWord (SA (EVar 3) 400) 8 (ELit 31);   (* 25 AT_EXECFN *)
     KWord (SA (EVar 3) 0) 8 (ELit 33);   (*  0 AT_SYSINFO_EHDR *)
     KWord (SA (EVar 3) 392) 8 (EVar 4)].  (* AT_RANDOM's value word: [rnd], bound at index 4 *)

  (* The auxv terminator, which depends on the free kernel field [kb_rseq]: with CONFIG_RSEQ
     pairs 26 and 27 are AT_RSEQ_FEATURE_SIZE (27) and AT_RSEQ_ALIGN (28) and AT_NULL is pair
     28; without it AT_NULL is pair 26.  Not in [kn_main]: [know_auxv_term] proves the one
     that holds, as a disjunction, so the flag stays free. *)
  Definition kn_termT : list kentry :=
    [KWord (SA (EVar 3) 416) 8 (ELit 27); KWord (SA (EVar 3) 432) 8 (ELit 28);
     KWord (SA (EVar 3) 448) 8 (ELit 0)].
  Definition kn_termF : list kentry := [KWord (SA (EVar 3) 416) 8 (ELit 0)].

  Definition kn_image : list kentry :=
    [KWr (SA (ELit 0) 0x31000) 0x32000;  (* [comment removed for export] *)
     KImg 0x10000 0x317b0;
     KImg 0x317b1 0x317f9; (* [comment removed for export] *)
     KImg 0x417f9 0x42088; KImg 0x62160 0x62180;
     KWord (SA (ELit 0) 0x42090) 8 (ELit 0x42090);
     KWord (SA (ELit 0) 0x420b0) 4 (EVar 5);
     KImg 0x420bc 0x42108; KImg 0x42110 0x42128; KImg 0x42130 0x42148;
     KBlob (SA (ELit 0) 0x42148) (ELit 8) 2;  (* [comment removed for export] *)
     KImg 0x42158 0x42168; KImg 0x42170 0x62160; KImg 0x62198 0x623c8;
     KBlob (SA (ELit 0) 0x623c8) (ELit 8) 2;  (* [comment removed for export] *)
     KImg 0x623d0 0x623d8;
     KImg 0x623e9 0x623f0; KWord (SA (ELit 0) 0x623f0) 8 (EVar 3);
     KImg 0x623f8 0x62400; KImg 0x62410 0x62418; KWord (SA (ELit 0) 0x62418) 8 (ELit 4096);
     KImg 0x62420 0x62450; (* [comment removed for export] *) KImg 0x62458 0x63000;
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
  Variable rdraw : EntryDraw.
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
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry inp mbase entry sp0 rdraw tid regs mem.
  Local Notation R16 := (at_random_bytes (ed_random rdraw)) (only parsing).

  Let E := E0 inp sp0 a0s path rdraw tid regs.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma ev_vals : forall n, ev E n = nth n ([sp0; p0 inp rdraw; p1 inp rdraw; auxvp inp sp0; rnd inp sp0; tid] ++ junk_vals regs) (Z_to_bv 64 0).
  Proof. intros n. reflexivity. Qed.

  (* [comment removed for export] *)

  Lemma ev_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. rewrite ev_vals. change (6 + i)%nat with (length [sp0; p0 inp rdraw; p1 inp rdraw; auxvp inp sp0; rnd inp sp0; tid] + i)%nat.
    rewrite app_nth2_plus.
    unfold junk_vals. rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
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
  Variable rdraw : EntryDraw.
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
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry inp mbase entry sp0 rdraw tid regs mem.
  Local Notation R16 := (at_random_bytes (ed_random rdraw)) (only parsing).
  Let E := E0 inp sp0 a0s path rdraw tid regs.

  Ltac reg_case :=
    cbn [nth sr_main all_regs];
          first [ rewrite (spx_val inp sp0 a0s path rdraw tid regs)
                | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                    change (edenot E (EVar n)) with (ev E n);
                    first [ rewrite (ev_junk inp sp0 a0s path rdraw tid regs (n - 6)) by lia; reflexivity | idtac ]
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

  #[using="Hav Hva Hve Hvl Hlau Hvsp Htid ME"] Theorem main_regs_ok : regs_ok E sr_main regs.
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
  Variable rdraw : EntryDraw.
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
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry inp mbase entry sp0 rdraw tid regs mem.
  Local Notation R16 := (at_random_bytes (ed_random rdraw)) (only parsing).
  Let E := E0 inp sp0 a0s path rdraw tid regs.

  Lemma kp_lo : (0x7fff80000000 <= bv_unsigned sp0)%Z. Proof. exact (proj1 Hvsp). Qed.
  Lemma kp_hi : (bv_unsigned sp0 <= 0x800000000000)%Z. Proof. exact (proj1 (proj2 Hvsp)). Qed.
  Lemma kp_al : (bv_unsigned sp0 mod 16 = 0)%Z. Proof. exact (proj2 (proj2 Hvsp)). Qed.
  Lemma ke0 : ev E 0 = sp0. Proof. reflexivity. Qed.
  Lemma ke1 : ev E 1 = p0 inp rdraw. Proof. reflexivity. Qed.
  Lemma ke2 : ev E 2 = p1 inp rdraw. Proof. reflexivity. Qed.
  Lemma ke3 : ev E 3 = auxvp inp sp0. Proof. reflexivity. Qed.
  Lemma ke4 : ev E 4 = rnd inp sp0. Proof. reflexivity. Qed.
  Lemma ke5 : ev E 5 = tid. Proof. reflexivity. Qed.
  (* [comment removed for export] *)

  Lemma know_stack : know_ok RSEGS E mem kn_stack.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    unfold kn_stack, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot]; rewrite ?ke0, ?ke1, ?ke2;
      unfold flat, estart; cbn [a_base a_off edenot]; rewrite ?ke0.
    - split; [lia | exact Hal].
    - lia.
    - split; [lia|]. intros d m Hd Hm.
      (* the floor is [wok_lo sp0] (sp0 - 6144513), at or below the window's sp0 - 6144512 *)
      apply (main_entry_store_ok_win inp mbase entry sp0 rdraw tid regs mem ME);
        rewrite u_small by lia; unfold wok_lo, stack_window_reach, stack_max_size; lia.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite (main_entry_rdn_above inp mbase entry sp0 rdraw tid regs mem ME) by lia.
      assert (Hr : rdn RSEGS (wrap_mem inp mbase RPH entry sp0 rdraw) sp0 8 = Some (word_le8 (argcN inp)))
        by (eapply (read_argc_w RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw); try eassumption; unfold sp_window_hi; lia).
      rewrite Hr. unfold argcN. rewrite Hav.
      rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above inp mbase entry sp0 rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
      assert (Hr : rdn RSEGS (wrap_mem inp mbase RPH entry sp0 rdraw) (sp0 + nat_to_word (8 + 8 * 0)) 8
                   = Some (word_le8 (cat_argv_ptr (ed_top rdraw) (in_argv inp) envv (in_execfn inp) 0)))
        by (eapply (read_argv_ptr_w RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw); try eassumption;
            first [unfold sp_window_lo; lia | unfold sp_window_hi; lia | rewrite Hav; subst av; cbn; lia]).
      rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above inp mbase entry sp0 rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
      assert (Hr : rdn RSEGS (wrap_mem inp mbase RPH entry sp0 rdraw) (sp0 + nat_to_word (8 + 8 * 1)) 8
                   = Some (word_le8 (cat_argv_ptr (ed_top rdraw) (in_argv inp) envv (in_execfn inp) 1)))
        by (eapply (read_argv_ptr_w RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw); try eassumption;
            first [unfold sp_window_lo; lia | unfold sp_window_hi; lia | rewrite Hav; subst av; cbn; lia]).
      rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 1)) with 16%Z in Hr.
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above inp mbase entry sp0 rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
      assert (Hr : rdn RSEGS (stack_to_mem sp0 (entry_stack_image inp mbase RPH entry sp0 rdraw))
                     (sp0 + nat_to_word (8 + 8 * length (in_argv inp))) 8 = Some (word_le8 (Z_to_bv 64 0)))
        by (eapply (read_argv_null RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw); try eassumption;
            first [unfold sp_window_lo; lia | unfold sp_window_hi; lia]).
      rewrite w_add_nat in Hr. rewrite Hav in Hr. subst av. change (Z.of_nat (8 + 8 * length [a0s; path])) with 24%Z in Hr.
      rewrite <- (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rdraw) in Hr by (try rewrite u_small by lia; lia).
      unfold wmem in Hr. rewrite n_to_le_8_spec in Hr. exact Hr.
  Qed.

  #[using="Hav Hva Hve Hvl Hlau Hvsp Htid ME"] Lemma auxvp_eq : auxvp inp sp0 = Z_to_bv 64 (bv_unsigned sp0 + Z.of_nat (auxv_off av envv)).
  Proof. unfold auxvp, auxv_w, auxv_off. rewrite Hav. subst av. cbn [length]. f_equal. lia. Qed.

  #[using="Hav Hva Hve Hvl Hlau Hvsp Htid ME"] Lemma auxvp_u : bv_unsigned (auxvp inp sp0) = (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z
    /\ (Z.of_nat (auxv_off av envv) + 176 <= 2240000)%Z.
  Proof.
    pose proof kp_lo. pose proof kp_hi. destruct Hve as [Hle _].
    rewrite auxvp_eq. unfold auxv_off in *. subst av. cbn [length] in *.
    rewrite u_small by lia. split; lia.
  Qed.

  #[using="Hav Hva Hve Hvl Hlau Hvsp Htid ME"] Lemma rnd_u : (bv_unsigned sp0 <= bv_unsigned (rnd inp sp0))%Z
    /\ (bv_unsigned (rnd inp sp0) + 16 <= bv_unsigned sp0 + 2240000)%Z
    /\ (bv_unsigned (rnd inp sp0) mod 8 = 0)%Z
    /\ (forall j n, (j + n <= 16)%nat ->
          rdn RSEGS (stack_to_mem sp0 (entry_stack_image inp mbase RPH entry sp0 rdraw))
              (Z_to_bv 64 (bv_unsigned (rnd inp sp0) + Z.of_nat j)) n = Some (firstn n (skipn j R16))).
  Proof.
    pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    pose proof (lay_bsb_len Sv48 inp mbase RPH entry sp0 brk rdraw Hvl Hlau) as Hl.
    assert (RF := rnd_facts RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw).
    repeat match type of RF with ?P -> _ =>
      specialize (RF ltac:(first [exact Hva | exact Hve | exact Hvl | exact Hlau | exact kp_al
                                 | (unfold sp_window_lo; lia) | (unfold sp_window_hi; lia)])) end.
    destruct RF as (A & B & C & D & F).
    unfold rnd. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption; try lia.
  Qed.

  Lemma know_auxv : know_ok RSEGS E mem kn_auxv.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    destruct auxvp_u as [Hau Hab]. destruct rnd_u as (Hr1 & Hr2 & Hr3 & Hr4).
    unfold kn_auxv, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot];
      rewrite ?ke0, ?ke3, ?ke4; unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?ke0, ?ke3, ?ke4;
      try rewrite Hau; try lia.
    - (* [comment removed for export] *) split; [lia|].
      destruct (proj1 (Z.mod_divide (bv_unsigned sp0) 16 ltac:(lia)) Hal) as [q Hq].
      replace (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z with ((2 * q + 5 + Z.of_nat (length envv)) * 8)%Z
        by (unfold auxv_off; subst av; cbn [length]; lia).
      apply Z_mod_mult.
  Qed.

  (* An auxv word of the main entry's memory, read off the stack image ([read_auxv_word]);
     both CONFIG_RSEQ layouts, [j] ranging over the vector. *)
  #[using="Hav Hva Hve Hvl Hlau Hvsp Htid ME"] Lemma rd_auxv_main : forall j w a,
    (j < 2 * auxv_count (kb_rseq (in_kernel inp)))%nat ->
    nth j (auxv_words (launch_auxv inp sp0 mbase) RPH entry uid (in_gid inp) hw (rnd inp sp0)
             (at_execfn_ptr (ed_top rdraw) (in_execfn inp))) (Z_to_bv 64 0) = w ->
    a = (bv_unsigned (auxvp inp sp0) + 8 * Z.of_nat j)%Z ->
    rdn RSEGS mem (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 w).
  Proof.
    intros j w a Hj Hw ->. pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
    destruct auxvp_u as [Hau Hab].
    assert (Hac : (auxv_count (kb_rseq (in_kernel inp)) <= 29)%nat)
      by (unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia).
    rewrite (main_entry_rdn_above inp mbase entry sp0 rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
    pose proof (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rdraw) as Hwm. unfold wmem in Hwm.
    rewrite Hwm by (rewrite u_small by lia; lia).
    replace (Z_to_bv 64 (bv_unsigned (auxvp inp sp0) + 8 * Z.of_nat j))
      with (sp0 + nat_to_word (auxv_off (in_argv inp) (in_envp inp) + 8 * j))
      by (rewrite word_add_nat; f_equal; rewrite Hav, Hau; lia).
    rewrite <- Hw. unfold rnd.
    eapply read_auxv_word; first [exact Hva | exact Hve | exact Hvl | exact Hlau | exact Hj
                                 | (unfold sp_window_lo; lia) | (unfold sp_window_hi; lia) | eassumption].
  Qed.

  (* 464 is BYTES: 29 auxv pairs * 2 words * 8. *)
  #[using="Hav Hva Hve Hvl Hlau Hvsp Htid ME"] Lemma auxvp_bounds : (bv_unsigned sp0 <= bv_unsigned (auxvp inp sp0))%Z /\ (bv_unsigned (auxvp inp sp0) + 464 <= 2 ^ 64)%Z.
  Proof. pose proof kp_lo. pose proof kp_hi. destruct auxvp_u as [Hau Hab]. lia. Qed.

  (* One row of [kn_auxw]: entry [j]'s a_type word, element [2 * j] of [auxv_words], at byte
     offset [16 * j] from [auxvp].  The bound [j < auxv_count] holds at both [kb_rseq] values. *)
  Lemma kauxv_type : forall (j : nat) (t : Z),
    (j < auxv_count (kb_rseq (in_kernel inp)))%nat ->
    nth (2 * j) (auxv_words (launch_auxv inp sp0 mbase) RPH entry uid (in_gid inp) hw (rnd inp sp0)
                   (at_execfn_ptr (ed_top rdraw) (in_execfn inp))) (Z_to_bv 64 0) = Z_to_bv 64 t ->
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
      | cbn [a_base a_off edenot]; rewrite ke3; lia ].
  Qed.

  (* AT_RANDOM's a_VAL word: element 49 of [auxv_words], byte offset 392, value [rnd inp sp0],
     which the env binds at index 4 ([ke4]). *)
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
    erewrite <- (rd_auxv_main 49%nat (rnd inp sp0));
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

  (* The terminator words ([kn_termT] / [kn_termF]) as the disjunction of the two [kb_rseq]
     cases: the flag is case-split here and never fixed. *)
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
  #[using="Hav Hva Hve Hvl Hlau Hvsp Htid ME"] Lemma D_main_auxvp : forall segs,
    rdn segs (D_main inp sp0 rdraw tid) (Z_to_bv 64 0x623f0) 8
    = Some (word_to_le_bytes 8 (auxvp inp sp0)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof kp_lo. pose proof kp_hi.
    unfold auxvp, D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma wseg_data : wseg_ok RSEGS (Z_to_bv 64 0x31000) 0x32000 = true.
  Proof. (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (EN : 0x32000%nat = 204800%nat) by (vm_cast_no_check (@eq_refl nat 204800%nat)).
    rewrite EN. exact D_Exvwg.ref_wseg_1c. Qed.

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
  Lemma kimg_ok : forall lo hi, D_main_missb lo (Z.to_nat (hi - lo)) = true -> (lo <= hi)%Z -> (hi <= 0x63000)%Z ->
    kentry_ok RSEGS E mem (KImg lo hi).
  Proof.
    intros lo hi Hb Hle Hhi. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    assert (Hlo0 : (0 <= lo)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb].
      apply Z.leb_le in Hb. exact Hb. }
    cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    rewrite (main_entry_mem_data inp mbase entry sp0 rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
    apply (D_main_none inp sp0 rdraw tid i Hva); [lia | lia |].
    apply (missb_sub lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
  Qed.

  Ltac kimg := apply kimg_ok; [vm_compute; reflexivity | lia | lia].

  Ltac kw_pre :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
  Ltac kw_data L :=
    kw_pre;
    rewrite (main_entry_rdn_data inp mbase entry sp0 rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    rewrite (L RSEGS); try reflexivity.
  Ltac kw_mem L := kw_pre; rewrite (L RSEGS); try reflexivity.

  Lemma know_image : know_ok RSEGS E mem kn_image.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof (u64_range tid) as Ht.
    unfold kn_image, know_ok.
    repeat apply Forall_cons; try apply Forall_nil;
      try kimg;
      cbn [kentry_ok a_base a_off edenot]; rewrite ?ke3, ?ke5; unfold flat, estart, elenZ; cbn [a_base a_off edenot];
      rewrite ?(u_small 0) by lia; cbn [Z.add].
    - (* [comment removed for export] *) split; [lia|]. intros d m Hd Hm.
      eapply (store_ok_window RSEGS mem (Z_to_bv 64 0x31000) (Z_to_bv 64 (0x31000 + d)) 0x32000 m 0x31000 0x63000);
        [reflexivity | reflexivity | cbn; lia | apply wseg_data | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
    - kw_data (D_main_self inp sp0 rdraw tid).
    - kw_mem (main_entry_tid inp mbase entry sp0 rdraw tid Hlo regs mem ME).
    - (* [comment removed for export] *) rewrite (u_small 8) by lia. split; [lia|]. split; [change (eb E 2) with (guard_bytes R16); rewrite length_guard_bytes; reflexivity|].
      intros i Hi. change (eb E 2) with (guard_bytes R16).
      etransitivity; [apply (main_entry_mem_data inp mbase entry sp0 rdraw tid regs mem ME); rewrite u_small by lia; unfold stack_max_size; lia|].
      etransitivity; [apply (D_main_canary_at inp sp0 rdraw tid i Hi)|].
      unfold canary_w, le_bytes_to_word.
      rewrite (word_to_le_bytes_of_lez 8 (guard_bytes R16) (length_guard_bytes R16) ltac:(lia)). reflexivity.
    - (* [comment removed for export] *) rewrite (u_small 8) by lia. split; [lia|]. split; [change (eb E 2) with (guard_bytes R16); rewrite length_guard_bytes; reflexivity|].
      intros i Hi. change (eb E 2) with (guard_bytes R16).
      rewrite (main_entry_mem_data inp mbase entry sp0 rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
      apply (D_main_guard_at inp sp0 rdraw tid); lia.
    - kw_data D_main_auxvp.
    - kw_data (D_main_pagesize inp sp0 rdraw tid Hva).
    - (* [comment removed for export] *) lia.
  Qed.


  #[using="Hav Hva Hve Hvl Hlau Hvsp Htid ME"] Theorem main_know_ok : know_ok RSEGS E mem kn_main.
  Proof.
    unfold kn_main, know_ok.
    apply Forall_app; split; [apply know_stack|].
    apply Forall_app; split; [apply know_auxv|].
    apply Forall_app; split; [apply know_auxw | apply know_image].
  Qed.

  (* [main_know_ok] plus the [kb_rseq]-split terminator rows, and the fact that the auxv sits
     above sp0 (so the rows survive every store below it). *)
  #[using="Hav Hva Hve Hvl Hlau Hvsp Htid ME"] Theorem main_know_term : (bv_unsigned sp0 <= bv_unsigned (auxvp inp sp0))%Z /\
    (know_ok RSEGS E mem (kn_main ++ kn_termT) \/ know_ok RSEGS E mem (kn_main ++ kn_termF)).
  Proof.
    split; [exact (proj1 auxvp_bounds)|].
    pose proof main_know_ok as HK.
    destruct know_auxv_term as [HT|HT]; [left | right];
      unfold know_ok in *; apply Forall_app; split; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="Hav Hva Hve Hvl Hlau Hvsp Htid ME"] Lemma main_str : forall k, (k < 2)%nat ->
    rdn RSEGS mem (cat_argv_ptr (ed_top rdraw) (in_argv inp) envv (in_execfn inp) k) (length (nth k (in_argv inp) []) + 1) = Some (nth k (in_argv inp) [] ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) envv (in_execfn inp) k))%Z
    /\ (bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) envv (in_execfn inp) k) <= bv_unsigned sp0 + 2107576)%Z
    /\ (Z.of_nat (length (nth k (in_argv inp) [])) <= 131071)%Z.
  Proof.
    intros k Hk. pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
    assert (Hk' : (k < length (in_argv inp))%nat) by (rewrite Hav; subst av; cbn; lia).
    destruct (argv_ptr_bounds Sv48 inp mbase sp0 brk rdraw k Hlau Hk') as [B1 B2].
    assert (Hu : bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) k)
                 = (bv_unsigned sp0
                    + Z.of_nat (cat_string_off (kb_rseq (in_kernel inp)) sp0 (ed_top rdraw)
                                  (in_argv inp) (in_envp inp) (in_execfn inp)
                                + total_arg_bytes_nat (firstn k (in_argv inp))))%Z)
      by (eapply (u_cat_argv_ptr Sv48 inp mbase RPH entry sp0 brk rdraw); try eassumption;
          first [unfold sp_window_lo; lia | unfold sp_window_hi; lia]).
    assert (Hsb : (cat_string_off (kb_rseq (in_kernel inp)) sp0 (ed_top rdraw)
                     (in_argv inp) (in_envp inp) (in_execfn inp)
                   + total_arg_bytes_nat (in_argv inp) + total_arg_bytes_nat (in_envp inp)
                   <= length (entry_stack_image inp mbase RPH entry sp0 rdraw))%nat)
      by (eapply struct_av_bound; eassumption).
    pose proof (lay_bsb_len Sv48 inp mbase RPH entry sp0 brk rdraw Hvl Hlau) as Hl.
    pose proof (total_arg_bytes_firstn_le k (in_argv inp)) as Hf.
    pose proof (valid_argv_str_len (in_argv inp) k Hva Hk') as Hlen.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit.
    - rewrite (main_entry_rdn_above inp mbase entry sp0 rdraw tid regs mem ME) by lia.
      pose proof (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rdraw) as Hw. unfold wmem in Hw. rewrite Hw by lia.
      exact (read_argv_cstr_k Sv48 RSEGS inp mbase RPH entry sp0 brk rdraw k Hlau Hk').
    - exact B1.
    - lia.
    - exact Hlen.
  Qed.
End KnowProofs.

(* At 727298f3 the argv strings sit at the top of the stack VMA, below [ed_top], which
   [entry_launch_ok_va] bounds by the Sv48 stack top.  Replaces [main_str_fits], whose
   [entry_stack_fits] bound described the old layout (strings just above the vectors). *)
Lemma argv_ptr_fits : forall inp mbase (sp brk : word) rdraw k,
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
  (k < length (in_argv inp))%nat ->
  (bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) k)
   + Z.of_nat (length (nth k (in_argv inp) [])) + 1 <= 0x800000000000)%Z.
Proof.
  intros inp mbase sp brk rdraw k Hlaunch Hk.
  pose proof (launch_string_base_arith Sv48 inp mbase sp brk rdraw Hlaunch) as HA.
  pose proof (u_cat_string_base Sv48 inp mbase sp brk rdraw Hlaunch) as Hu.
  pose proof (u64_range sp). pose proof (u64_range (ed_top rdraw)).
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

(* What the main phase's consumers hold about the launch, in one hypothesis: the launch facts
   [ref_startup] passes on and the state at [main]'s first instruction.  The entry point is the
   image's own ([D_Stmwg.ref_startup]). *)
Definition main_launch (inp : ProcInput) (mbase sp0 brk : word) (rdraw : EntryDraw) (tid : word)
    (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  valid_launch inp /\ entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp
  /\ main_entry inp mbase (0x17a18 : word) sp0 rdraw tid regs mem.

(* The main-entry words in the AMB world, over the old arguments plus the entry draw: the launch input
   there is [mkProcInputC [a0s; path] envv fs0 stdin0], whose argv, envp, execfn and kernel do not
   depend on fs0 / stdin0, so sections that do not carry those name the words with these.  Each is
   the [D_Manqc] word of that input by conversion ([p0_C] .. [rnd_C]). *)
Section AmbWords.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable rdraw : EntryDraw.
  Definition p0C : word := cat_argv_ptr (ed_top rdraw) [a0s; path] envv a_execfn 0.
  Definition p1C : word := cat_argv_ptr (ed_top rdraw) [a0s; path] envv a_execfn 1.
  Definition auxvpC : word :=
    Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length [a0s; path]) + 8 * Z.of_nat (length envv)).
  Definition rndC : word := at_random_ptr sp0 (kb_rseq a_kernel) [a0s; path] envv.

  Lemma p0_C : forall fs0 stdin0, p0 (mkProcInputC [a0s; path] envv fs0 stdin0) rdraw = p0C.
  Proof. reflexivity. Qed.
  Lemma p1_C : forall fs0 stdin0, p1 (mkProcInputC [a0s; path] envv fs0 stdin0) rdraw = p1C.
  Proof. reflexivity. Qed.
  Lemma auxvp_C : forall fs0 stdin0, auxvp (mkProcInputC [a0s; path] envv fs0 stdin0) sp0 = auxvpC.
  Proof. reflexivity. Qed.
  Lemma rnd_C : forall fs0 stdin0, rnd (mkProcInputC [a0s; path] envv fs0 stdin0) sp0 = rndC.
  Proof. reflexivity. Qed.
End AmbWords.
