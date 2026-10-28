(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AChd AChe ACgw.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YI0b YC5d YC7z YC7y YC7x YC88 YC85 YC86.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC21.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACgt ACgq ACgk ACgf ACgm ACgo ACgp ACgj ACgi ACgh ACgd ACgc ACgb ACgl ACga ACg8 ACg7 ACg4 ACg1 ACgn ACg0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Notation SB := YC81.SB.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Section c.
Variable B : asyms.
Variable K : asink_syms.
Variable MT : ameter_ops.
Variable XN : xnums.
Variable wfn : Z.
Variable CTX : list (list Z).
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AIL : asink_img_laws SEGS B K.
Hypothesis MLAW : ameter_laws MT.
Hypothesis HXNUM : af_xnums MT XN.
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA AS_asan_memcpy).
Hypothesis HTR : forall t, In t (af_sites B) -> In t (as_universe B).
Variable CTXfl : list (list Z).
Hypothesis HCTXfl : In [BASE + 0xba8] CTXfl.
Hypothesis FLUSHX : tflush_specX SEGS K B MT XN (BASE + AF_asan3_flushFrame) CTXfl wfn pa_relro_lo pa_relro_hi.
Hypothesis AMEMCMP : amemcmp_realizes SEGS B (SIGMA AS_memcmp).
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA AS_memcmp_2).
Theorem pb_cgif_addframeX : taddframe_specX SEGS K B MT XN (BASE + AF_asan3_cgif_addframe) CTX wfn pa_relro_lo pa_relro_hi.
Proof.
intros ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx f path hw rest GPAL IMG LPAL gs
HPRE Hctx Hfr7 HROD H10 H11 HFO HCF HT HWF Hf0 Hlpa HPerm XREL XSMAX XIMG XIMGL XLPAL Hev Hlive XMOK.
pose (AP := Build_af_params wfn hw CTX). pose (AX := Build_af_paramsX path f).
assert (HRET : AF_RET_stmtX K MT XN B) by (eapply af_RETX; eassumption).
assert (HRETC : AF_RETC_stmtX K MT XN B) by (eapply af_RETCX; eassumption).
assert (PE3 : AF_E3_stmtX K MT XN B) by (eapply af_E3X; eassumption).
assert (PE2 : AF_E2_stmtX K MT XN B) by (eapply af_E2X; eassumption).
assert (PE : AF_E_stmtX K MT XN B) by (eapply af_E1X; eassumption).
assert (PD3 : AF_D3_stmtX K MT XN B) by (eapply af_D3X; eassumption).
assert (PD2 : AF_D2_stmtX K MT XN B) by (eapply af_D2X; eassumption).
assert (PD : AF_D_stmtX K MT XN B) by (eapply af_D1X; eassumption).
assert (PFL : AF_FL_stmtX K MT XN B) by (eapply (af_FLX (AP := AP) (AX := AX) B K MT XN TL LAWS AIL MLAW AFREE4 (proj2 (proj2 HXNUM)) HTR CTXfl HCTXfl FLUSHX); eassumption).
assert (PC : AF_C_stmtX K MT XN B) by (eapply af_CX; eassumption).
pose proof (pb_cmpPixelF B LAWS TL AMEMCMP) as CMP.
assert (PSM : AF_SM_stmtX K MT XN B) by (eapply af_SMX; eassumption).
assert (PL : AF_L_stmtX K MT XN B) by (eapply af_LX; eassumption).
assert (PB : AF_B_stmtX K MT XN B) by (eapply af_BX; eassumption).
assert (POK : AF_OK_stmtX K MT XN B) by (eapply af_OKX; eassumption).
exact (af_AX (AP := AP) (AX := AX) B K MT XN TL LAWS AIL MLAW HXNUM POK ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx ((f, FILE_BLOCK) :: rest) GPAL IMG LPAL gs
(conj (conj HPRE (conj Hctx (conj Hfr7 (conj HROD (conj H10 (conj H11 (conj HFO (conj HCF (conj HT (conj HWF (conj Hlpa (conj HPerm (conj Hev Hlive)))))))))))))
(conj Hf0 (conj (or_introl eq_refl) (conj XREL (conj XSMAX (conj XIMG (conj XIMGL (conj XLPAL XMOK))))))))).
Qed.
End c.
End b.
End a.
