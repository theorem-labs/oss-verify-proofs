(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YN32 YK0w.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e YO03
YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YH00 YH03 YH02 YN3b
YI06 YI5b YI09 YI08 YI0r YI0o YI6a YI1w YI3p YI3m YI3t
YI4l YI3w YI4j YI4i YI4k YI4g YI43 YI44 YI45 YI46 YI47 YI48 YI49 YI4a YI4b.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI00 YI02 YI5c YI2z YI0j YI0k YI6c YI01.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5a YI2w YI2v YI3x.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI src0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src0_msyms MR.
Variables (IMGV LCTV : list Z).
Hypothesis FWRITE : fwrite_spec src0_msyms MR src0_A_fwrite.
Lemma ra_t2 :
forall cx L A mem md L2 A2 md2 (regs0 regs2 : bvmap 5 word) (mem2 : word -> option byte) (p bb Lbb M : Z) (S : list Z) (b : rbound),
rcx_ok cx -> ra_origin cx regs0 ->
journal src0_msyms MR RAWADD_STK (spZ regs0) ((c_raw cx + 40, c_raw cx + 44) :: sink_fp (c_f cx)) L A mem md L2 A2 mem2 md2 ->
st_init_done A2 = true -> ra_rb b A2 Lbb -> Permutation (blocks L A) (c_blocks cx) ->
ra_regs regs2 cx -> getr regs2 21 = Z_to_bv 64 (c_slct cx) -> getr regs2 22 = Z_to_bv 64 p -> pow2_ok (c_slct cx) p ->
Permutation (blocks L2 A2) ((bb, Lbb) :: blocks L A) ->
wtok' RAWADD_STK (spZ regs0) ((c_raw cx + 40, c_raw cx + 44) :: sink_fp (c_f cx)) (blocks L A) (bb, Lbb) ->
word_mem src0segs mem2 (c_sp cx + 8) bb -> val_mem src0segs mem2 (c_sp cx + 16) 4 M -> 1 <= M <= Lbb ->
objs_at mem2 cx (c_rcur cx) -> frame_savedN src0_msyms 10 regs0 mem2 (spZ regs0) ->
getr regs2 19 = Z_to_bv 64 0 ->
(0 < c_slct cx <= 256 -> exists Nl, In (c_lct cx, Nl) (c_rest cx) /\ 3 * c_slct cx <= Nl /\ (c_lct cx, Nl) <> (c_f cx, FILE_BLOCK) /\
garr8 src0segs mem (c_lct cx) LCTV /\ 3 * c_slct cx <= Z.of_nat (length LCTV)) ->
lzw_vok (2 ^ (ra_iclen cx - 1)) (ra_iclen cx) (ra_pix cx IMGV) mem2 bb M -> M <= 2 * c_nP cx + 16 -> fbC mem2 cx ->
sink_at src0_msyms mem2 md2 (c_f cx) (S ++ ra_gce cx) -> Z.of_nat (length S) + 2 * c_nP cx + 2048 <= SINK_MAX ->
SR src0segs (mkCfg (mkst regs2 (Z_to_bv 64 PC_T2) mem2 (seg_rom src0segs)) md2)
(at_T3 API IMGV LCTV cx L A mem md regs0 S b).
Proof.
intros cx L A mem md L2 A2 md2 regs0 regs2 mem2 p bb Lbb M S b Hcx HO HJ Hid HRB HB HR G21 G22 Hpow HB2 Hwt W32 W40 HM Hobjs HFS G19 HLCT HVOK HM2 HFBC HSK Hroom.
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
