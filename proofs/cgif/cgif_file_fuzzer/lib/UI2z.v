(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0s YK15 YM06 YP09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 YI06 UI5b YI09 YI08 YI0t YI0r UI3p YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0u.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Definition cbl_specV : Prop :=
forall L A regs mem md bl Lby lz Llz lzwPos D C0 rest codes,
fn_pre ubs0_msyms MR CBL_STK_U L A regs mem md ->
getr regs 10 = Z_to_bv 64 bl -> getr regs 11 = Z_to_bv 64 lzwPos -> getr regs 12 = Z_to_bv 64 lz ->
getr regs 13 = Z_to_bv 64 D -> getr regs 14 = Z_to_bv 64 C0 ->
0 <= lzwPos < 2 ^ 28 -> 0 <= D <= 65535 -> 0 <= C0 <= 12 ->
12 * lzwPos / 8 + 3 <= Lby -> 2 * lzwPos <= Llz -> 0 < Llz ->
Permutation (blocks L A) ((bl, Lby) :: (lz, Llz) :: rest) ->
arr16 ubs0segs mem lz codes -> Z.of_nat (length codes) = lzwPos ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 ubs0_A_create_byte_list) mem (seg_rom ubs0segs)) md)
(fun c' => exists regs' mem' ret,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs0segs)) md /\
journal ubs0_msyms MR CBL_STK_U (spZ regs) [(bl, bl + Lby)] L A mem md L A mem' md /\
regs_preserved regs regs' /\
getr regs' 10 = Z_to_bv 64 ret /\ 0 <= ret /\ 8 * ret <= 12 * lzwPos /\
garr8 ubs0segs mem' bl (create_byte_list D C0 codes) /\ Z.of_nat (length (create_byte_list D C0 codes)) = ret + 1).
Definition cbb_specV : Prop :=
forall L A regs mem md bl Lbl bb Lbb n rest BL,
fn_pre ubs0_msyms MR CBB_STK L A regs mem md ->
getr regs 10 = Z_to_bv 64 bl -> getr regs 11 = Z_to_bv 64 bb -> getr regs 12 = Z_to_bv 64 n ->
0 <= n < 2 ^ 28 -> n <= Lbl -> 0 < Lbl -> cbb_len n <= Lbb ->
Permutation (blocks L A) ((bl, Lbl) :: (bb, Lbb) :: rest) ->
garr8 ubs0segs mem bl BL -> Z.of_nat (length BL) = n ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 ubs0_A_create_byte_list_block) mem (seg_rom ubs0segs)) md)
(fun c' => exists regs' mem',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs0segs)) md /\
journal ubs0_msyms MR CBB_STK (spZ regs) [(bb, bb + Lbb)] L A mem md L A mem' md /\
regs_preserved regs regs' /\
getr regs' 10 = Z_to_bv 64 (cbb_len n - 1) /\
garr8 ubs0segs mem' bb (blocks255 (S (length BL)) BL) /\ Z.of_nat (length (blocks255 (S (length BL)) BL)) = cbb_len n).
Definition lzw_vok (idl icl : Z) (PIX : list Z) (m : word -> option byte) (bb M : Z) : Prop :=
exists out, lzw_stream idl icl PIX = Some out /\ garr8 ubs0segs m bb out /\ M = Z.of_nat (length out).
Definition lzw_vnone (idl icl : Z) (PIX : list Z) : Prop := lzw_stream idl icl PIX = None.
Definition lzw_specV : Prop :=
forall STK sp0 FP L A mem md Lc Ac memc mdc (regs : bvmap 5 word) (pR nP img idl icl bi Li : Z) (PIX : list Z),
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs 1) -> getr regs 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
getr regs 10 = Z_to_bv 64 pR -> getr regs 11 = Z_to_bv 64 nP -> getr regs 12 = Z_to_bv 64 img ->
getr regs 13 = Z_to_bv 64 idl -> getr regs 14 = Z_to_bv 64 icl ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - LZW_STK ->
spZ regs <= pR -> pR + 16 <= sp0 -> pR mod 8 = 0 ->
1 <= nP <= 100000000 -> 2 <= idl <= 256 -> 0 <= icl <= 12 ->
In (bi, Li) (blocks Lc Ac) -> bi <= img -> img + nP <= bi + Li ->
lzw_rodata_ok memc ->
garr8 ubs0segs memc img PIX -> length PIX = Z.to_nat nP ->
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
word_mem ubs0segs mem2 pR bb /\ val_mem ubs0segs mem2 (pR + 8) 4 M /\ 1 <= M <= Lbb /\ M <= 2 * nP + 16 /\ lzw_vok idl icl PIX mem2 bb M)
\/ ((res = 2 \/ res = 5) /\
Permutation (blocks L2 A2) (blocks Lc Ac) /\
(forall a, pR <= a < pR + 12 -> mbyte ubs0segs mem2 a = mbyte ubs0segs memc a) /\ (res = 5 -> lzw_vnone idl icl PIX)))).
End S.
End c.
