(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF6d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF6m.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition xrun_to {imgk : img} (stop : Z) (ss : sstate) : sstate := fst (sym_run_toN_sh tfxsegs tfxtbl_rrF FUEL stop ss).
Definition xrun {imgk : img} (ss : sstate) : sstate := fst (sym_runN_sh tfxsegs tfxtbl_rrF FUEL ss).
Definition xpin (r : bv 5) (e : sv) (ss : sstate) : sstate := mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition xadd (r : YQ0b.region) (ss : sstate) : sstate := mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition xafter (k : nat) (stklo retpc : Z) (ss : sstate) : sstate :=
ss_after_call ss (match ss_mem ss with r0 :: rest => trim_lo r0 stklo :: rest | [] => [] end) k retpc.
Definition R_SCR : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (- ASTACK) (- 2208) (- ASTACK) (- 2208) [].
Definition R_IM : YQ0b.region := YQ0b.mkRegion (Some 37%nat) 8 16 0 0 [YQ0b.mkChunk 8 (CZero 8)].
Definition R_OBJ {imgk : img} : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (- 2208) (- 64) 0 0
[YQ0b.mkChunk (-2208) (CVal 8 (SLit 1)); YQ0b.mkChunk (-2200) (CVal 8 (SLit (0x53640 + D_2c4))); YQ0b.mkChunk (-2192) (CVal 8 (SOff 10 0)); YQ0b.mkChunk (-2184) (CVal 8 (SOff 11 0));
YQ0b.mkChunk (-2176) (CVal 8 (SOff 2 0)); YQ0b.mkChunk (-2168) (CVal 8 (SLit (0x32340 + D_150))); YQ0b.mkChunk (-2152) (CVal 8 (SLit (0x536b0 + D_2c4)));
YQ0b.mkChunk (- 2136) (CVal 8 (SOff 2 (- 2120))); YQ0b.mkChunk (- 2128) (CVal 8 (SOff 36%nat 0))].
Definition R_TOP : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (-64) 0 (-64) 0
[YQ0b.mkChunk (-64) (CVal 8 (SOff 22 0)); YQ0b.mkChunk (-56) (CVal 8 (SOff 21 0)); YQ0b.mkChunk (-48) (CVal 8 (SOff 20 0)); YQ0b.mkChunk (-40) (CVal 8 (SOff 19 0));
YQ0b.mkChunk (-32) (CVal 8 (SOff 18 0)); YQ0b.mkChunk (-24) (CVal 8 (SOff 9 0)); YQ0b.mkChunk (-16) (CVal 8 (SOff 8 0)); YQ0b.mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition REGS_DC {imgk : img} : list sv :=
[SLit 0; SLit (0x32434 + D_150); SOff 2 (-2208); SOff 3 0; SLit TFX_TP; SOff 5 0; SOff 6 0; SOff 7 0; SOff 2 (-2136); SOff 10 0; SLit TFX_INST; SOff 10 0; SLit 0; SLit 0; SOff 2 (-2136); SLit 1;
SOff 16 0; SOff 17 0; SLit TFX_INST; SOff 13 0; SOff 12 0; SOff 14 0; SOff 15 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
Definition FFD {imgk : img} : facts :=
(match f_atoms (ss_facts SS0) with a2 :: a10 :: rest => mkFacts (a2 :: a10 :: (12%nat, mkAF 4096 (2 ^ 47) 0) :: rest) (f_conds (ss_facts SS0)) (f_alias (ss_facts SS0)) | _ => ss_facts SS0 end).
Definition SS_DC {imgk : img} : sstate := mkSS (0x3244c + D_150) REGS_DC (R_OBJ :: R_SCR :: R_IM :: R_TOP :: tl REG0) None FFD.
Definition SS_B {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((let s0 := SS_DC in
let s1 := xrun s0 in
let s2 := xpin 17 (SLit 2) (xpin 16 (SLit 3) (xpin 14 (SLit 2) (xpin 15 (SLit 255) s1))) in
let s3 := xrun s2 in
let s4 := xrun (xpin 11 (SLit 1) s3) in
xrun_to (0x72fcc + D_2c4) (xpin 11 (SLit 3) s4))))).
