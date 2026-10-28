(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0s YK15 YM06 YP09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 YI06 UI5b YI09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition RESET_STK : Z := 16.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Definition reset_specV : Prop :=
forall L A regs mem md (g ti lm lc li ld Lld idl lp : Z),
fn_pre ubs0_msyms MR RESET_STK L A regs mem md ->
getr regs 10 = Z_to_bv 64 g -> getr regs 11 = Z_to_bv 64 idl ->
2 <= idl <= 256 -> 0 <= lp < 2 ^ 31 -> 2 * lp + 2 <= Lld ->
In (g, 72) (blocks L A) -> In (ti, 2 * idl * idl) (blocks L A) -> In (lm, 8192) (blocks L A) ->
In (lc, 4096) (blocks L A) -> In (li, 8192) (blocks L A) -> In (ld, Lld) (blocks L A) ->
NoDup [g; ti; lm; lc; li; ld] ->
val_mem ubs0segs mem g 8 ti -> val_mem ubs0segs mem (g + 8) 8 lm -> val_mem ubs0segs mem (g + 16) 8 lc ->
val_mem ubs0segs mem (g + 24) 8 li -> val_mem ubs0segs mem (g + 40) 8 ld -> val_mem ubs0segs mem (g + 60) 4 lp ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 ubs0_A_resetDict) mem (seg_rom ubs0segs)) md)
(fun c' => exists regs' mem',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs0segs)) md /\
journal ubs0_msyms MR RESET_STK (spZ regs)
[(g + 60, g + 68); (ld + 2 * lp, ld + 2 * lp + 2); (ti, ti + 2 * idl * idl); (lm, lm + 8192); (lc, lc + 4096); (li, li + 8192)]
L A mem md L A mem' md /\
regs_preserved regs regs' /\
val_mem ubs0segs mem' (g + 60) 4 (lp + 1) /\ val_mem ubs0segs mem' (g + 64) 2 (idl + 2) /\
val_mem ubs0segs mem' (g + 66) 2 1 /\ val_mem ubs0segs mem' (ld + 2 * lp) 2 idl /\
(forall i, 0 <= i < 2 * idl * idl -> mbyte ubs0segs mem' (ti + i) = Some (Z_to_bv 8 0)) /\
(forall i, 0 <= i < 8192 -> mbyte ubs0segs mem' (lm + i) = Some (Z_to_bv 8 0)) /\
(forall i, 0 <= i < 4096 -> mbyte ubs0segs mem' (lc + i) = Some (Z_to_bv 8 0)) /\
(forall i, 0 <= i < 8192 -> mbyte ubs0segs mem' (li + i) = Some (Z_to_bv 8 0))).
End S.
End c.
