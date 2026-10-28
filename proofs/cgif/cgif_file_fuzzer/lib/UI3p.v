(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
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
Definition LZW_STK : Z := 208 + ALLOC_STACK.
Definition lzw_rodata_ok (m : word -> option byte) : Prop :=
forall i, 0 <= i < 8 ->
mbyte ubs0segs m (ubs0_D_const_u64_0x0101010101010102 + i) =
seg_rom ubs0segs (Z_to_bv 64 (ubs0_D_const_u64_0x0101010101010102 + i)).
Section d.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Definition lzw_spec : Prop :=
forall STK sp0 FP L A mem md Lc Ac memc mdc (regs : bvmap 5 word) (pR nP img idl icl bi Li : Z),
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs 1) -> getr regs 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
getr regs 10 = Z_to_bv 64 pR -> getr regs 11 = Z_to_bv 64 nP -> getr regs 12 = Z_to_bv 64 img ->
getr regs 13 = Z_to_bv 64 idl -> getr regs 14 = Z_to_bv 64 icl ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - LZW_STK ->
spZ regs <= pR -> pR + 16 <= sp0 -> pR mod 8 = 0 ->
1 <= nP <= 100000000 -> 2 <= idl <= 256 -> 0 <= icl <= 12 ->
In (bi, Li) (blocks Lc Ac) -> bi <= img -> img + nP <= bi + Li ->
lzw_rodata_ok memc ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 ubs0_A_LZW_GenerateStream) memc (seg_rom ubs0segs)) mdc)
(fun c' => exists L2 A2 regs2 mem2 md2 (res : Z),
c' = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\ regs_preserved regs regs2 /\
getr regs2 10 = Z_to_bv 64 res /\
(forall a, alloc_ceiling <= a < 2 ^ 64 ->
~ (spZ regs - LZW_STK <= a < spZ regs) -> ~ (pR <= a < pR + 12) ->
mbyte ubs0segs mem2 a = mbyte ubs0segs memc a) /\
(forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m ->
mbyte ubs0segs mem2 (b + i) = mbyte ubs0segs memc (b + i)) /\
((res = 0 /\
exists bb Lbb M,
Permutation (blocks L2 A2) ((bb, Lbb) :: blocks Lc Ac) /\
(forall blc i, In (bb, Lbb) blc -> 0 <= i < Lbb -> wr_byte STK sp0 FP (blocks L A) blc (bb + i)) /\
word_mem ubs0segs mem2 pR bb /\ val_mem ubs0segs mem2 (pR + 8) 4 M /\ 1 <= M <= Lbb)
\/ ((res = 2 \/ res = 5) /\
Permutation (blocks L2 A2) (blocks Lc Ac) /\
(forall a, pR <= a < pR + 12 -> mbyte ubs0segs mem2 a = mbyte ubs0segs memc a)))).
End d.
End c.
