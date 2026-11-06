(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Plain.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Amb
  PropExec CatExec StepTac StoreOk StartupTac ArgvEnv SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  MemSplit ZStores RefLayout RefStartupDefs RefStartupFacts RefStartup LibDiagKn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section AtMain.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable rnd : EntryDraw.
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis ME : main_entry sp0 av ev rnd tid regs mem.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  Lemma cells_ok_main_entry : cells_ok mem diag_cells.
  Proof.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (main_entry_rdn_image sp0 av ev rnd tid Hlo regs mem ME RSEGS) as HI.
    unfold diag_cells, cells_ok.
    repeat (apply Forall_cons); [ .. | apply Forall_nil ]; unfold cell_ok;
      rewrite HI by (vm_compute; reflexivity); vm_refl_bv.
  Qed.

  Lemma pf1_cells_main_entry : cells_ok mem pf1_cells.
  Proof.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (main_entry_rdn_image sp0 av ev rnd tid Hlo regs mem ME RSEGS) as HI.
    unfold pf1_cells, cells_ok.
    repeat (apply Forall_cons); [ .. | apply Forall_nil ]; unfold cell_ok;
      rewrite HI by (vm_compute; reflexivity); vm_refl_bv.
  Qed.

  (* [comment removed for export] *)
  Lemma canary_ok_main_entry : canary_ok mem (bv_unsigned (canary_w rnd)).
  Proof.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    split.
    - unfold CANARY. rewrite Z_to_bv_bv_unsigned, <- (canary_bytes_w rnd).
      exact (main_entry_guard sp0 av ev rnd tid Hlo regs mem ME RSEGS).
    - apply u64_range.
  Qed.

  (* [comment removed for export] *)
  Lemma main_entry_none_below : forall i, (0 <= i < 0x2dc8a8)%Z -> mem (Z_to_bv 64 i) = None.
  Proof.
    intros i Hi. pose proof SPlo as Hlo. pose proof (u64_range tid).
    rewrite (main_entry_mem_data sp0 av ev rnd tid regs mem ME) by (rewrite stack_max_size_val, u_small by lia; lia).
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
    repeat (rewrite wbytes_outside by
      (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite !u_small by lia; lia)).
    reflexivity.
  Qed.

  Corollary main_entry_ro_none : forall i, (0x10000 <= i < 0x27e000)%Z -> mem (Z_to_bv 64 i) = None.
  Proof. intros i Hi. apply main_entry_none_below. lia. Qed.

  (* [comment removed for export] *)
  Lemma main_entry_none_range : forall (lo hi : Z),
    D_main_missb lo (Z.to_nat (hi - lo)) = true ->
    forall i, (lo <= i < hi)%Z -> mem (Z_to_bv 64 i) = None.
  Proof.
    intros lo hi Hb i Hi. pose proof SPlo as Hlo. pose proof (u64_range tid) as Htid.
    assert (E : Z.of_nat (Z.to_nat (hi - lo)) = (hi - lo)%Z) by lia.
    unfold D_main_missb, D_main_cells in Hb. cbn [forallb] in Hb.
    repeat match goal with
           | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H as [? ?]
           end.
    repeat match goal with
           | H : range_disjoint_b _ _ _ = true |- _ =>
               apply range_disjoint_djw in H; cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ] in H
           | H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
           | H : true = true |- _ => clear H
           end.
    rewrite E in *. clear E.
    rewrite (main_entry_mem_data sp0 av ev rnd tid regs mem ME) by (rewrite stack_max_size_val, u_small by lia; lia).
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
    repeat (rewrite wbytes_outside by
      (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite !u_small by lia;
       first [ lia
             | lazymatch goal with |- (_ < ?c \/ _)%Z =>
                 match goal with H : djw (_ <= c \/ _)%Z |- _ => unfold djw in H; clear - H Hi; lia end end ])).
    reflexivity.
  Qed.
End AtMain.

(* [comment removed for export] *)
Ltac none_by_range Hvsp ME H :=
  lazymatch type of H with (?lo <= _ < ?hi)%Z =>
    apply (main_entry_none_range _ _ _ _ _ _ _ Hvsp ME lo hi); [vm_compute; reflexivity | exact H] end.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
