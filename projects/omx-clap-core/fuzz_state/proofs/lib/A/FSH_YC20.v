(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC20.v keeping only in_roP, arodata_okP (:43-48) and apost_base (:90-96), the image-independent definitions fm's program-part statements use; the rest of YC20.v names cgif's objects. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMH_YC20.v at a working branch 706affbdbe6 (a Theorem Labs lane), module path fuzz_manifest -> fuzz_state; fuzz_state's raw core (a working branch d579ce160e2) has no YC20.v either. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved.
   This file does not load Reusable.YI14, so it carries the sink_head probe only. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Definition in_roP (segs : list Segment) (rlo rhi : Z) (a : Z) : Prop :=
(exists s, In s segs /\ seg_writable s = false /\ Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s))
\/ (rlo <= a < rhi).
Definition arodata_okP (segs : list Segment) (rlo rhi : Z) (B : asyms) (rd : reader) : Prop :=
forall a, in_roP segs rlo rhi a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rd a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section l.
Variable segs : list Segment.
Definition apost_base (B : asyms) (STK : Z) (FP : list (Z * Z)) (regs : bvmap 5 word) ly S W mem md (k : Z)
(Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
: world segs -> config -> Prop :=
fun W' c' => exists ly' S' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
ajournal segs B STK (spZ regs) FP ly S W mem md [] ly' S' W' mem' md' k /\
aregs_preserved regs regs' /\ Q ly' S' W' regs' mem' md'.
End l.
End j.
