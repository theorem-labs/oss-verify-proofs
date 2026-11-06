(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 571 of its 593 lines of code are new or changed and 122 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/codec_main_owe0.v; 247 of its 266 lines of code are new or changed and 574 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe1.v; 37 of its 69 lines of code are new or changed and 234 lines of the source are left out. *)
(* Segment RD1 (BUTTON) of the image-A walk of LLVMFuzzerTestOneInput: seg_rd_run 1 of
   lib/A/Prog/codec_amain_inv.v, from the reader cut at 0x80f68 to RUN 0x820d0. k.a, k.b, k.c = fuzz_u32 each (fuzz_codec.c: case BUTTON), stored at 24(s6), 28(s6), 32(s6).
   Each fuzz_u32 is four guarded byte reads (a missing byte reads 0): the test of in.n, the cursor advanced, the
   byte's instrumented check (slow path behind a `j`, or inline for the fourth byte), lbu. The state is
   codec_amain_rdlib.v's rd_ss with the k window [24, 36); the 12 input bytes c .. c + 11 are the atoms
   AM_X0 .. (codec_amain_rdin.v rd_ys / rd_AF). The proof explores every path (codec_amain_rdin.v rd_explore, on
   lib/A/Prog/CPgTokJ.v's runs): at each undecided test of in.n it splits, and on the in.n <> 0 side it adds the next
   byte's read-only region; each check leaves one obligation, paid by the input block. At RUN, rd_fin gives the cut:
   the cut needs only the ranges of the stored words (u32 for a, b, c; int32 for delta). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CodecRo CodecGlobs CPgWalk.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv codec_amain_st CPgTokJ codec_amain_rdlib codec_amain_rdin.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require codec_owe.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem seg_rd1_holds : seg_rd_run B MT K XM_LIB 1.
Proof.
intros g pos sp1 ops W2 c2 Hrd.
destruct Hrd as (ly2 & S2 & regs2 & mem2 & md2 & k & -> & HJ & Hfr & Hk & Hmo & HC & HP).
destruct HP as (Hops & Hkind & c & pv & dv & od & Hcur & Hc1 & Hpd & R23 & Hkat).
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
unfold AM_HI in Hchi, Hpn.
pose proof Hcur as (Hc & C152 & C160).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (Hfb : FA g pos + 512 <= 2 ^ 47) by (change (fs_frame_bytes 3) with 512 in Hfceil; lia).
assert (Hfs : FA g pos + 360 <= sp1) by (change (fs_frame_bytes 3) with 512 in Hfceil; lia).
set (ys := rd_ys g c 12).
destruct (rd_start B MT K XM_LIB TL LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 k c ys (rd_AF 12) (rd_pc 1) 24 36
  [] HJ Hfr HC Hcur ltac:(lia) ltac:(lia) ltac:(lia) (Forall_nil _) eq_refl (rd_AF_ok g pos c regs2 12)) as [HS SHOK].
set (E := am_env g pos c regs2 ys) in HS, SHOK.
assert (HAE : env_agree 41 E E) by apply env_agree_refl.
pose proof HC as (_ & _ & R2 & _).
assert (B2 : bv_unsigned (ew E 2) = sp1).
{ unfold E. rewrite (am_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (B33 : bv_unsigned (ew E 33) = FA g pos) by (unfold E; rewrite (am_ew_F g pos c regs2 ys); apply unsigned_lit_small; lia).
assert (E35 : ew E 35 = Z_to_bv 64 (e_p g + c)) by (unfold E; exact (am_ew_CP g pos c regs2 ys)).
assert (E36 : ew E 36 = Z_to_bv 64 (e_n g - c)) by (unfold E; exact (am_ew_CN g pos c regs2 ys)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (unfold E; exact (am_ew_SB g pos c regs2 ys)).
assert (EYall : forall j, (j < 12)%nat -> ew E (AM_X0 + j) = Z_to_bv 64 (rd_ib g (c + Z.of_nat j)))
  by (intros j Hj; exact (rd_EY g pos c regs2 12 j Hj)).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ rd_zone g pos sp1 24 36 a ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
pose proof (rd_in_sep B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as HSEP.
cw_keep_j0 HJ HJ0.
unfold cfg_at. change (w64 (rd_pc 1)) with (Z_to_bv 64 0x80f68). change (rd_pc 1) with 0x80f68 in HS.
rd_explore LAWS HJ0 Hfr HC c E35 E32 E36 B2 B33 EFA EYall HSEP
  ltac:(idtac; rd_fin LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys 1 pv dv od 24 36).
Qed.
End b.
End a.
