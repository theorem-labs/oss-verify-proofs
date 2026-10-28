(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03
UI1e UI1i YI07 YP14 YI08 YI0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition RD_STK : Z := 32.
Definition RD_NMAX : Z := 40000.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Definition readdata_spec : Prop :=
forall STK sp0 FP L A mem md Lc Ac memc mdc (regs : bvmap 5 word) (st dst n pdata nb cur : Z),
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
YK0s.ret_ok (getr regs 1) -> spZ regs mod 16 = 0 ->
sp0 - STK <= spZ regs - RD_STK -> spZ regs <= st -> st + 24 <= sp0 -> st mod 8 = 0 ->
getr regs 10 = Z_to_bv 64 st -> getr regs 11 = Z_to_bv 64 dst -> getr regs 12 = Z_to_bv 64 n ->
1 <= n <= RD_NMAX -> 0 <= cur <= nb -> nb < 2 ^ 63 ->
word_mem ubs2segs memc st pdata -> word_mem ubs2segs memc (st + 8) nb -> word_mem ubs2segs memc (st + 16) cur ->
(cur + n <= nb ->
4096 <= pdata /\ pdata + nb <= alloc_ceiling /\
(forall i, 0 <= i < n -> present memc (pdata + cur + i)) /\
0 <= dst /\ dst + n < 2 ^ 64 /\
(forall i, 0 <= i < n -> present memc (dst + i)) /\
(forall a, dst <= a < dst + n -> wr_byte STK sp0 FP (blocks L A) (blocks Lc Ac) a) /\
(dst + n <= pdata + cur \/ pdata + cur + n <= dst) /\
(dst + n <= st \/ st + 24 <= dst) /\
(dst + n <= spZ regs - RD_STK \/ spZ regs <= dst)) ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_readdata) memc (seg_rom ubs2segs)) mdc)
(fun c' => exists regs2 mem2,
c' = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom ubs2segs)) mdc /\
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem2 mdc /\
regs_preserved regs regs2 /\
((cur + n <= nb /\ getr regs2 10 = Z_to_bv 64 0 /\ word_mem ubs2segs mem2 (st + 16) (cur + n) /\
(forall i, 0 <= i < n -> mbyte ubs2segs mem2 (dst + i) = mbyte ubs2segs memc (pdata + cur + i))) \/
(nb < cur + n /\ getr regs2 10 = Z_to_bv 64 (2 ^ 64 - 1) /\ word_mem ubs2segs mem2 (st + 16) nb)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - RD_STK <= a < spZ regs) -> ~ (st + 16 <= a < st + 24) ->
~ (cur + n <= nb /\ dst <= a < dst + n) -> mbyte ubs2segs mem2 a = mbyte ubs2segs memc a)).
End S.
End b.
