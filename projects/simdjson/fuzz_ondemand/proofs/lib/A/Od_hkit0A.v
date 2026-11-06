(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast SysStep FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Str_tac Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Export Od_hbaseA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition cli_got_nothrow (m : mem) : Prop := ro_cells asegs m 0x10d890 [C8 (Z_to_bv 64 0x2d070)].

Lemma mcost_nonneg : forall n, 0 <= n -> 0 <= mcost n.
Proof. intros n H. unfold mcost, DCOST. destruct (n <=? 64512); lia. Qed.

Lemma cells_mid_update : forall (m m' : mem) A pre k old new post,
  rw_cells asegs m A (pre ++ [CB k old] ++ post) ->
  agree_on (fun x => A <= x < A + Z.of_nat (cells_size (pre ++ [CB k old] ++ post))
                     /\ ~ (A + Z.of_nat (cells_size pre) <= x < A + Z.of_nat (cells_size pre) + Z.of_nat k)) m m' ->
  wmono asegs m m' -> bytes_at asegs m' (A + Z.of_nat (cells_size pre)) new -> length new = k ->
  rw_cells asegs m' A (pre ++ [CB k new] ++ post).
Proof.
  intros m m' A pre k old new post H AG WM HB HL.
  apply Sj_stage1_kit.rw_cells_app in H. destruct H as [H1 H2]. apply Sj_stage1_kit.rw_cells_app in H2. destruct H2 as [H2 H3].
  assert (E : cells_size (pre ++ [CB k old] ++ post) = (cells_size pre + (k + cells_size post))%nat)
    by (rewrite !cells_size_app; cbn [cells_size csize]; lia).
  cbn [cells_size csize] in H3. rewrite Nat.add_0_r in H3.
  pose proof (rw_cells_bound asegs m _ _ H1) as B1. pose proof (rw_cells_bound asegs m _ _ H3) as B3.
  apply Sj_stage1_kit.rw_cells_app. split.
  - apply (rw_cells_agree asegs m m' _ _ H1); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. rewrite E. lia.
  - apply Sj_stage1_kit.rw_cells_app. split.
    + subst k. apply rw_cells_CB_intro; [exact HB|].
      assert (W : wr_at asegs m (A + Z.of_nat (cells_size pre)) (Z.of_nat (length new))).
      { apply (rw_cells_wr_at asegs m _ _ _ H2). cbn [cells_size csize]. lia. }
      exact (wr_at_transport asegs m m' _ _ W WM).
    + cbn [cells_size csize]. rewrite Nat.add_0_r.
      apply (rw_cells_agree asegs m m' _ _ H3); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. rewrite E. lia.
Qed.

Lemma outside_of_nin : forall (W : list (Z * Z)) x, ~ in_ranges W x -> outside W x.
Proof.
  induction W as [|[l h] W IH]; intros x H; [exact I|]. cbn [outside]. split.
  - intros Hr. apply H. exists l, h. split; [left; reflexivity| exact Hr].
  - apply IH. intros (l' & h' & Hin & Hr). apply H. exists l', h'. split; [right; exact Hin| exact Hr].
Qed.

Definition vt_dpi (m : mem) : Prop :=
  ro_cells asegs m 0x109840
    [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x1098c0); C8 (Z_to_bv 64 0xc5958); C8 (Z_to_bv 64 0x9cfa0); C8 (Z_to_bv 64 0x9f8d8); C8 (Z_to_bv 64 0xb2330);
     C8 (Z_to_bv 64 0xc4a1c); C8 (Z_to_bv 64 0xc51d0); C8 (Z_to_bv 64 0xc5d0c); C8 (Z_to_bv 64 0xc5e6c); C8 (Z_to_bv 64 0xc5fd4); C8 (Z_to_bv 64 0xc60c0)].

