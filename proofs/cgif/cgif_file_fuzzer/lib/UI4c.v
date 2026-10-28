(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YN32 YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e YO03
YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b
YI06 UI5b YI09 YI08 YI0r YI0o YI6a UI1w UI3p UI3m UI3t
UI4l UI3w UI4j UI4i UI4k UI4g UI43 UI44 UI45 UI46 UI47 UI48 UI49 UI4a UI4b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI00 YI02 UI5c UI2z YI0j YI0k YI6c YI01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5a YI2w UI2v UI3x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Variables (IMGV LCTV : list Z).
Hypothesis FWRITE : fwrite_spec ubs0_msyms MR ubs0_A_fwrite.
Lemma ra_t2 :
forall cx L A mem md L2 A2 md2 (regs0 regs2 : bvmap 5 word) (mem2 : word -> option byte) (p bb Lbb M : Z) (S : list Z) (b : rbound),
rcx_ok cx -> ra_origin cx regs0 ->
journal ubs0_msyms MR RAWADD_STK (spZ regs0) ((c_raw cx + 40, c_raw cx + 44) :: sink_fp (c_f cx)) L A mem md L2 A2 mem2 md2 ->
st_init_done A2 = true -> ra_rb b A2 Lbb -> Permutation (blocks L A) (c_blocks cx) ->
ra_regs regs2 cx -> getr regs2 23 = Z_to_bv 64 (c_slct cx) -> getr regs2 24 = Z_to_bv 64 p -> getr regs2 22 = Z_to_bv 64 (c_cfp cx + 30) ->
pow2_ok (c_slct cx) p ->
Permutation (blocks L2 A2) ((bb, Lbb) :: blocks L A) ->
wtok' RAWADD_STK (spZ regs0) ((c_raw cx + 40, c_raw cx + 44) :: sink_fp (c_f cx)) (blocks L A) (bb, Lbb) ->
word_mem ubs0segs mem2 (c_sp cx + 8) bb -> val_mem ubs0segs mem2 (c_sp cx + 16) 4 M -> 1 <= M <= Lbb ->
objs_at mem2 cx (c_rcur cx) -> frame_savedN ubs0_msyms 12 regs0 mem2 (spZ regs0) ->
getr regs2 19 = Z_to_bv 64 0 ->
(0 < c_slct cx <= 256 -> exists Nl, In (c_lct cx, Nl) (c_rest cx) /\ 3 * c_slct cx <= Nl /\ (c_lct cx, Nl) <> (c_f cx, FILE_BLOCK) /\
garr8 ubs0segs mem (c_lct cx) LCTV /\ 3 * c_slct cx <= Z.of_nat (length LCTV)) ->
lzw_vok (2 ^ (ra_iclen cx - 1)) (ra_iclen cx) (ra_pix cx IMGV) mem2 bb M -> M <= 2 * c_nP cx + 16 -> fbC mem2 cx ->
sink_at ubs0_msyms mem2 md2 (c_f cx) (S ++ ra_gce cx) -> Z.of_nat (length S) + 2 * c_nP cx + 2048 <= SINK_MAX ->
SR ubs0segs (mkCfg (mkst regs2 (Z_to_bv 64 PC_T2) mem2 (seg_rom ubs0segs)) md2)
(at_T3 API IMGV LCTV cx L A mem md regs0 S b).
Proof using FWRITE IMG.
intros cx L A mem md L2 A2 md2 regs0 regs2 mem2 p bb Lbb M S b Hcx HO HJ Hid HRB HB HR G23 G24 G22 Hpow HB2 Hwt W32 W40 HM Hobjs HFS G19 HLCT HVOK HM2 HFBC HSK Hroom.
pose proof (objs_fields_ok _ _ _ Hobjs) as (_ & _ & _ & _ & _ & _ & _ & _ & F8 & _).
pose proof (proj2 Hcx) as Hslct.
destruct (Z.eq_dec (c_slct cx) 0) as [Hz | Hnz].
- eapply ra_t2_nolct; eassumption.
- destruct Hpow as [_ Hpow]. specialize (Hpow Hnz). destruct Hpow as (Hp18 & Hsk & Hpp).
specialize (HLCT ltac:(lia)).
assert (Hc : p = 1 \/ p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6 \/ p = 7 \/ p = 8) by lia.
destruct Hc as [Hc | [Hc | [Hc | [Hc | [Hc | [Hc | [Hc | Hc]]]]]]];
[ eapply ra_t2_lctp1 | eapply ra_t2_lctp2 | eapply ra_t2_lctp3 | eapply ra_t2_lctp4
| eapply ra_t2_lctp5 | eapply ra_t2_lctp6 | eapply ra_t2_lctp7 | eapply ra_t2_lctp8 ]; eassumption.
Qed.
End S.
End a.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
