(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0s YK15 YN06 YQ0b.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition RESET_STK : Z := 16.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Definition reset_spec : Prop :=
forall L A regs mem md (g ti lm lc li ld Lld idl lp : Z),
fn_pre ubs2_msyms MR RESET_STK L A regs mem md ->
getr regs 10 = Z_to_bv 64 g -> getr regs 11 = Z_to_bv 64 idl ->
2 <= idl <= 256 -> 0 <= lp < 2 ^ 31 -> 2 * lp + 2 <= Lld ->
In (g, 72) (blocks L A) -> In (ti, 2 * idl * idl) (blocks L A) -> In (lm, 8192) (blocks L A) ->
In (lc, 4096) (blocks L A) -> In (li, 8192) (blocks L A) -> In (ld, Lld) (blocks L A) ->
NoDup [g; ti; lm; lc; li; ld] ->
val_mem ubs2segs mem g 8 ti -> val_mem ubs2segs mem (g + 8) 8 lm -> val_mem ubs2segs mem (g + 16) 8 lc ->
val_mem ubs2segs mem (g + 24) 8 li -> val_mem ubs2segs mem (g + 40) 8 ld -> val_mem ubs2segs mem (g + 60) 4 lp ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_resetDict) mem (seg_rom ubs2segs)) md)
(fun c' => exists regs' mem',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs2segs)) md /\
journal ubs2_msyms MR RESET_STK (spZ regs)
[(g + 60, g + 68); (ld + 2 * lp, ld + 2 * lp + 2); (ti, ti + 2 * idl * idl); (lm, lm + 8192); (lc, lc + 4096); (li, li + 8192)]
L A mem md L A mem' md /\
regs_preserved regs regs' /\
val_mem ubs2segs mem' (g + 60) 4 (lp + 1) /\ val_mem ubs2segs mem' (g + 64) 2 (idl + 2) /\
val_mem ubs2segs mem' (g + 66) 2 1 /\ val_mem ubs2segs mem' (ld + 2 * lp) 2 idl /\
(forall i, 0 <= i < 2 * idl * idl -> mbyte ubs2segs mem' (ti + i) = Some (Z_to_bv 8 0)) /\
(forall i, 0 <= i < 8192 -> mbyte ubs2segs mem' (lm + i) = Some (Z_to_bv 8 0)) /\
(forall i, 0 <= i < 4096 -> mbyte ubs2segs mem' (lc + i) = Some (Z_to_bv 8 0)) /\
(forall i, 0 <= i < 8192 -> mbyte ubs2segs mem' (li + i) = Some (Z_to_bv 8 0))).
End S.
End c.
