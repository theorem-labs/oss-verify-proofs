(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac ITree Nodes Decode SysStep InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import Stdio_pure.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PImg F_syscalls StdioFiles PIosKit PIosCert PStartU PIosX_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac sub0 IE0 k :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    replace A with (0xe1b00 + Z.of_nat k) by (vm_compute; reflexivity);
    apply (rw_cells_sub_u psegs m 0xe1b00 3723 ios_exp0 k cs IE0); [cbn; repeat split | vm_compute; reflexivity | vm_compute; lia]
  end.

(* [comment removed for export] *)
Ltac img8 NONE v :=
  lazymatch goal with |- rw_cells _ ?m ?A _ =>
    eapply (rw_cells_recast psegs m A [CB 8 (le8 (Z_to_bv 64 v))]);
      [ apply (rw_cells_image0 psegs m A (le8 (Z_to_bv 64 v)));
        [ intros a Ha; rewrite length_le8 in Ha; apply NONE; [lia | unfold pcrt_written; cbn [outside]; lia]
        | vm_compute; reflexivity | lia | rewrite length_le8; lia ]
      | cbn; repeat split | cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity | reflexivity ]
  end.

Lemma ios_cells_init : forall (m : word -> option byte) (c : word),
  (forall a : word, (0xca000 <= bv_unsigned a < 0x105000)%Z -> outside pcrt_written (bv_unsigned a) -> m a = None) ->
  rw_cells psegs m 0xe1b00 [CB 3723 ios_exp0] ->
  rw_cells psegs m 0xe3988 [C4 (Z_to_bv 64 2); CB 76 (repeat (Z_to_bv 8 0) 76); C8 (Z_to_bv 64 0xe39d8);
                            CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 0x103cf0); CB 24 (repeat (Z_to_bv 8 0) 24); C8 c;
                            C8 (Z_to_bv 64 0xe3a38); CB 16 (repeat (Z_to_bv 8 0) 16); C8 z64; CB 112 (repeat (Z_to_bv 8 0) 112)] ->
  ios_cells m.
Proof.
  intros m c NONE IE0 PTH.
  assert (LOC : rw_cells psegs m 0xe39f8 [C8 (Z_to_bv 64 0x103cf0)]).
  { change [C4 (Z_to_bv 64 2); CB 76 (repeat (Z_to_bv 8 0) 76); C8 (Z_to_bv 64 0xe39d8);
            CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 0x103cf0); CB 24 (repeat (Z_to_bv 8 0) 24); C8 c;
            C8 (Z_to_bv 64 0xe3a38); CB 16 (repeat (Z_to_bv 8 0) 16); C8 z64; CB 112 (repeat (Z_to_bv 8 0) 112)]
      with ([C4 (Z_to_bv 64 2); CB 76 (repeat (Z_to_bv 8 0) 76); C8 (Z_to_bv 64 0xe39d8); CB 24 (repeat (Z_to_bv 8 0) 24)]
            ++ [C8 (Z_to_bv 64 0x103cf0)]
            ++ [CB 24 (repeat (Z_to_bv 8 0) 24); C8 c; C8 (Z_to_bv 64 0xe3a38); CB 16 (repeat (Z_to_bv 8 0) 16); C8 z64; CB 112 (repeat (Z_to_bv 8 0) 112)]) in PTH.
    apply (proj1 (rw_cells_app psegs m _ _ _)) in PTH. destruct PTH as [_ PTH].
    apply (proj1 (rw_cells_app psegs m _ _ _)) in PTH. destruct PTH as [PTH _].
    cbn [cells_size csize Nat.add] in PTH. exact PTH. }
  unfold ios_cells, ios_char_shared, ios_cout, ios_clog, ios_wide_shared, ios_wcout, ios_wclog.
  repeat match goal with |- _ /\ _ => split end.
  all: try exact LOC.
  (* [comment removed for export] *)
  - img8 NONE 8.
  - img8 NONE 0x75e6c.
  - sub0 IE0 2688%nat.
  - img8 NONE 0x9d6f0.
  (* [comment removed for export] *)
  - sub0 IE0 600%nat.
  - sub0 IE0 616%nat.
  - sub0 IE0 640%nat.
  - sub0 IE0 648%nat.
  - sub0 IE0 744%nat.
  - sub0 IE0 8%nat.
  - sub0 IE0 72%nat.
  (* [comment removed for export] *)
  - sub0 IE0 1240%nat.
  - sub0 IE0 1256%nat.
  - sub0 IE0 1280%nat.
  - sub0 IE0 1288%nat.
  - sub0 IE0 1384%nat.
  - sub0 IE0 104%nat.
  - sub0 IE0 168%nat.
  (* [comment removed for export] *)
  - img8 NONE 8.
  - img8 NONE 0x765d0.
  - sub0 IE0 3088%nat.
  - img8 NONE 0x9debc.
  - sub0 IE0 3104%nat.
  (* [comment removed for export] *)
  - sub0 IE0 760%nat.
  - sub0 IE0 776%nat.
  - sub0 IE0 800%nat.
  - sub0 IE0 808%nat.
  - sub0 IE0 904%nat.
  - sub0 IE0 200%nat.
  - sub0 IE0 264%nat.
  (* [comment removed for export] *)
  - sub0 IE0 1400%nat.
  - sub0 IE0 1416%nat.
  - sub0 IE0 1440%nat.
  - sub0 IE0 1448%nat.
  - sub0 IE0 1544%nat.
  - sub0 IE0 296%nat.
  - sub0 IE0 360%nat.
Qed.
