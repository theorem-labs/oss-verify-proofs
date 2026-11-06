(* Modified by Theorem Labs, 2026-10: relocated from lib/A/<same path> to fuzz_command.asan-ubsan by the image-B address relocator (the A-to-B address map, keyed by the image maps' symbol names and by code; GXA symbol keys kept), whose check table lists every changed numeral *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/B/Rt/RtWH8.v (donor image sha256 bbe55d24d096), with its module paths changed. *)
(* The world field w_H8 that omx-clap-core/fuzz_manifest's GXA route uses at one place (FMgxaSeamReady.v word_vis,
   fm :1091): the hidden map of a world is constant on each 8-aligned word of the shadow band (lib/Reusable/YA0n.v
   world field `w_H8 : forall a, YG0f.in_band_rw a -> w_H (Z_to_bv 64 a) = w_H (Z_to_bv 64 (a - a mod 8))`, as
   fuzz_manifest's). The route takes it as this Prop class, `Context {H8 : WH8}` in the sections that need it; the
   instance below is the core field, so every use resolves it and the closed theorems carry no premise for it. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v.
Local Open Scope Z_scope.

Class WH8 : Prop :=
  wh8 : forall (W : world tfibsegs) (a : Z), in_band_rw a ->
    w_H W (Z_to_bv 64 a) = w_H W (Z_to_bv 64 (a - a mod 8)).

#[global] Instance wh8_core : WH8 := fun W a Ha => w_H8 W a Ha.
