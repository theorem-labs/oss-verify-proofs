(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: relocated from cgif_file_fuzzer.asan to omx-clap-core fuzz_manifest.asan: 4 address literal(s) rewritten, module paths changed; lib_site_x's journal footprint is sink_token :: FM_PSTAT_FP (A/FMPstat.v), as in A/ACfn.v tfib_lib_post_x; lib_site_x and loop_L_x carry the library invariant LI (call ci needs LI ci and gives LI (ci + 1)); lib_inv_stable and lib_inv_init state what the driver assumes of LI. *)
(* Modified by Theorem Labs, 2026-11: made from A/AD1w.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK15.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0n YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YK04 YA0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.BudgetWit.AW Require Import YA0n_w YA0e_w.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0k YG0f YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.BudgetWit.AW Require Import YG0n_w YG0d_w YCe5_w.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YL02.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AF0m AD2j.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.BudgetWit.AW Require Import AD2i_w AD1t_w AD20_w AD1v_w AD2h_w AD2f_w.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK00 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.BudgetWit.AW Require Import AE2k_w AD1u_w.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From Stdlib Require Import Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMPstat.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section c.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Definition STDOUT_MUT (a : Z) : Prop := (STDOUT_LO <= a < STDOUT_HI) \/ (SOBUF_LO <= a < SOBUF_HI).
Definition stdout_img (H : word -> bool) (m : word -> option byte) : Prop :=
forall a, STDOUT_LO <= a < STDOUT_HI -> aview tfibsegs H m a = option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a)).
Definition xst_frame_tfa : Prop :=
forall k (H H' : word -> bool) (m m' : word -> option byte),
xst k H m -> (forall a, STDOUT_MUT a -> aview tfibsegs H' m' a = aview tfibsegs H m a) -> xst k H' m'.
End c.
