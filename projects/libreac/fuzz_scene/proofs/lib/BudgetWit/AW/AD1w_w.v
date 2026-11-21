(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1w.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AD1w.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3, with libreac/fuzz_boxreg's port of its copy of this file (proof steps and imports changed). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK15.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP0n YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.BudgetWit.AW Require Import YA0n_w YA0e_w.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0k YG0f YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.BudgetWit.AW Require Import YG0n_w YG0d_w YCe5_w.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YL02.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import AB1v AF0m AD2j.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.BudgetWit.AW Require Import AD2i_w AD1t_w AD20_w AD1v_w AD2h_w AD2f_w.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK00 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.BudgetWit.AW Require Import AE2k_w AD1u_w.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From Stdlib Require Import Permutation.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Definition STDOUT_MUT (a : Z) : Prop := (STDOUT_LO <= a < STDOUT_HI) \/ (SOBUF_LO <= a < SOBUF_HI).
Definition stdout_img (H : word -> bool) (m : word -> option byte) : Prop :=
forall a, STDOUT_LO <= a < STDOUT_HI -> aview tfibsegs H m a = option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a)).
Definition xst_frame_tfa : Prop :=
forall k (H H' : word -> bool) (m m' : word -> option byte),
xst k H m -> (forall a, STDOUT_MUT a -> aview tfibsegs H' m' a = aview tfibsegs H m a) -> xst k H' m'.
End c.
