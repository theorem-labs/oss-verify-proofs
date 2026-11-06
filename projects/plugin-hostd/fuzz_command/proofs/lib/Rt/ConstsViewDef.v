(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE39.v (mconsts_view, mconsts_of_rom_view, mconsts_view_keep) as consts_view, consts_view_of_rom_view, consts_view_keep, with the constant range as two parameters lo, hi in place of cgif_file's fixed range, over lib/Reusable only so both builds of libreac/fuzz_disco share it; module paths. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_disco/lib/Rt/ConstsViewDef.v
   (the version of the shared general memchr), with its module paths changed. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Definition consts_view (lo hi : Z) (W : world segs) (mem : word -> option byte) : Prop :=
forall a, lo <= a < hi -> aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
Lemma consts_view_of_rom_view : forall lo hi (W : world segs) mem,
(forall a, lo <= a < hi -> in_rom segs a) -> rom_view segs W mem -> consts_view lo hi W mem.
Proof. intros lo hi W mem Hin Hr a Ha. apply Hr. apply Hin. exact Ha. Qed.
Lemma consts_view_keep : forall lo hi (W : world segs) mem mem',
consts_view lo hi W mem -> (forall a, lo <= a < hi -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
consts_view lo hi W mem'.
Proof. intros lo hi W mem mem' Hc Hk a Ha. rewrite (Hk a Ha). exact (Hc a Ha). Qed.
End c.
End b.
