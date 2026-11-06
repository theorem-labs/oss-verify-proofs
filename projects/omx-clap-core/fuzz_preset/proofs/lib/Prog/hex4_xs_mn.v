(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: statement of hex4's asan / asan-ubsan walk with the memnorm keep. thex4_leafXmn is
   hex4_xs.v's thex4_leafX (the same binders and premises) with one conjunct appended last to its post:
   YAkMemnorm.memnorm segs memc -> YAkMemnorm.memnorm segs mem' (memc the entry memory, mem' the post's memory).
   No entry premise: a run from a memory that is not in memnorm states nothing about memnorm. The post has one arm;
   the conjunct follows the match on PjGrammar.hex4 BS, so it holds in both of the match's cases.
   YAkMemnorm.memnorm (lib/Reusable/YAkMemnorm.v, blob 96c72061b4d4) is the override-free closure; it loads no
   lib/Lib/LiaTwx2.v, so this file changes no lia. Proved by lib/A/Prog/hex4_mn.v and lib/B/Prog/hex4_mn.v. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI08 YN3v YI00 YI0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import hex4_xs.
Import ListNotations.
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Definition thex4_leafXmn (a : Z) : Prop :=
forall STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k (regs : bvmap 5 word) (p o : Z) (BS : list Z),
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 10 = w64 p -> getr regs 11 = w64 o ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - HEX4_STK -> spZ regs <= sp0 ->
(forall x, spZ regs - HEX4_STK <= x < spZ regs -> apresent (w_H W) memc x) ->
4096 <= p -> amem_range p 4 -> range_addressable (aview segs (w_H W) memc) SHADOW_OFF p 4 ->
garr8 segs (mrestrict (w_H W) memc) p BS -> Z.of_nat (length BS) = 4 ->
spZ regs <= o -> o + 4 <= sp0 -> o mod 4 = 0 -> range_addressable (aview segs (w_H W) memc) SHADOW_OFF o 4 ->
(forall x, o <= x < o + 4 -> apresent (w_H W) memc x) ->
(o + 4 <= p \/ p + 4 <= o) ->
(spZ regs <= p \/ p + 4 <= spZ regs - HEX4_STK) ->
SRr segs W (cfg_at segs a regs memc mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem' md' k /\
aregs_preserved regs regs' /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - HEX4_STK <= x < spZ regs) -> ~ (o <= x < o + 4) ->
aview segs (w_H W) mem' x = aview segs (w_H W) memc x) /\
match PjGrammar.hex4 BS with
| Some h => getr regs' 10 = w64 0 /\ val_mem segs (mrestrict (w_H W) mem') o 4 h
| None => getr regs' 10 = w64 (-1) /\
(forall x, o <= x < o + 4 -> aview segs (w_H W) mem' x = aview segs (w_H W) memc x)
end /\
(YAkMemnorm.memnorm segs memc -> YAkMemnorm.memnorm segs mem')).
End b.
