(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset image B' (asan-ubsan, pin d663f82d7f48): the StackDepotPut contract in c-asan's cf form.
   CLdepot.depot_spec_x (lib/Reusable/CLdepot.v, taken by path from origin/cold/c-asan-cf-f1-preset 9ac4e6bed4f7, blob
   9ec3d23eb12b) is AFl0B.tfib_depot_spec over [segs] / [A_DEP] / [TPv] / [IMGC] (CLdepot.v:94); at B' it is
   instantiated at tfibsegs / AFl0B.A_StackDepotPut / TFIB_TP / img_cover and discharged by AFemB.tfib_depot_ok (the
   relocation of A' lib/A/AFem.v:1523, row A13). This is the premise c-asan's YGcfInstDepot.v:175 / :202 / :210 / :220
   (origin/cold/c-asan-cf-f1 28e723d6b10d) take, at preset B'. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0q YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1h YF0l YF0m YF0x YF0p YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require CLdepot.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AFl0B AFemB.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem depot_spec_x_B : forall B, TfibSyms B -> (forall t, as_dhash B t = tfib_dhash t) ->
  CLdepot.depot_spec_x tfibsegs A_StackDepotPut TFIB_TP img_cover B.
Proof. intros B HB HDH. exact (tfib_depot_ok B HB HDH). Qed.
End g.
