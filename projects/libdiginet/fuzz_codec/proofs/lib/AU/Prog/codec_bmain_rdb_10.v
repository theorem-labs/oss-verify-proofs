(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 571 of its 593 lines of code are new or changed and 122 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/codec_main_owe0.v; 247 of its 266 lines of code are new or changed and 574 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe1.v, with its module paths and module names changed; 51 of its 82 lines of code are new or changed and 235 lines of the source are left out. *)
(* Segment RD10 (COUNTER) of the image-B walk of LLVMFuzzerTestOneInput: seg_rd_run 10 of
   lib/AU/Prog/codec_bmain_inv.v, from the reader cut at 0x813cc to RUN 0x826f4. k.b = fuzz_u8, then
   k.bytes[0 .. 8) = fuzz_u8 each (fuzz_codec.c: case COUNTER, SPEC_DIGITS = 8).
   The code: 0x813cc ld in.n; beqz -> 0x81408 (no byte: k.b is the in.n just tested, 0); 0x813d4 .. 0x81404 byte 0;
   0x81408 .. 0x81418 sw k.b, a1 = 8, a2 = &k.bytes (the spill 120(sp1)); the loop 0x8141c .. 0x81464: beqz
   in.n - j -> 0x81454 (a missing byte reads 0), else byte j (check inline, partial-granule test at 0x8146c), sb,
   a1 - 1, a2 + 1, bnez a1; j RUN.
   The state is codec_bmain_rdlib.v's rd_ss with the k window [28, 48) (k.b and the first 8 bytes); c and delta lie
   inside the window and are not written, so the window starts with their HEAD zeros as chunks (rd10_cs) and the
   end reads them back. The nine bytes are the atoms BM_X0 .. (input bytes c .. c + 8). The paths are explored
   (codec_bmain_rdb_lib.v rdb_explore; the loop counter is a literal, so the engine unrolls the loop); each byte's
   check is paid by the input block, the cursor's UBSan check is decided by the engine. At RUN, rdb_bfin gives the
   cut; k.b < 256 is the engine's range of the stored value, or in.n = 0 on the path with no byte. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CodecRo CodecGlobs CPgWalkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_inv codec_bmain_st CPgTokJU codec_bmain_rdlib codec_bmain_rdin.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_rdb_lib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require codec_owe.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Definition rd10_cs : list YP09.chunk :=
[YP09.mkChunk 224 (CVal 4 (SLit 0)); YP09.mkChunk 228 (CVal 4 (SLit 0))].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem seg_rd10_holds : seg_rd_run B MT K XM_LIB 10.
Proof.
intros g pos sp1 ops W2 c2 Hrd.
destruct Hrd as (ly2 & S2 & regs2 & mem2 & md2 & k & -> & HJ & Hfr & Hk & Hmo & HC & HP).
destruct HP as (Hops & Hkind & c & pv & dv & od & Hcur & Hc1 & Hpd & R22 & Hkat).
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
unfold BM_HI in Hchi, Hpn.
pose proof Hcur as (Hc & C184 & C192).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (Hfb : FA g pos + 512 <= 2 ^ 47) by (change (fs_frame_bytes 3) with 512 in Hfceil; lia).
assert (Hfs : FA g pos + 376 <= sp1) by (change (fs_frame_bytes 3) with 512 in Hfceil; lia).
assert (Hfs2 : FA g pos + 512 <= sp1) by (change (fs_frame_bytes 3) with 512 in Hfceil; lia).
set (ys := rd_ys g c 9).
assert (HCS : Forall (YP09.chunk_ok tfibsegs (bm_env g pos c regs2 ys) (mrestrict (w_H W2) mem2) (FA g pos)) rd10_cs).
{ pose proof Hkat as ((_ & _ & _ & _ & _ & Vc & Vd & _) & _). cbn [kz_b kz_c kz_delta k_rdZ] in Vc, Vd.
  unfold rd10_cs. constructor; [|constructor; [|constructor]].
  - apply (chunk_ok_val tfibsegs _ _ (FA g pos) 224 4 (SLit 0) 0); [reflexivity | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | lia |].
    replace (FA g pos + 224) with (FA g pos + 192 + 32) by lia. exact Vc.
  - apply (chunk_ok_val tfibsegs _ _ (FA g pos) 228 4 (SLit 0) 0); [reflexivity | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | lia |].
    replace (FA g pos + 228) with (FA g pos + 192 + 36) by lia. exact Vd. }
destruct (rd_start B MT K XM_LIB TL LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 k c ys (rd_AF 9) (rd_pc 10) 28 48
  rd10_cs HJ Hfr HC Hcur ltac:(lia) ltac:(lia) ltac:(lia) HCS eq_refl (rd_AF_ok g pos c regs2 9)) as [HS SHOK].
clear HCS.
set (E := bm_env g pos c regs2 ys) in HS, SHOK.
assert (HAE : env_agree 41 E E) by apply env_agree_refl.
pose proof HC as (_ & _ & R2 & _).
assert (B2 : bv_unsigned (ew E 2) = sp1).
{ unfold E. rewrite (bm_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (B33 : bv_unsigned (ew E 33) = FA g pos) by (unfold E; rewrite (bm_ew_F g pos c regs2 ys); apply unsigned_lit_small; lia).
assert (E35 : ew E 35 = Z_to_bv 64 (e_p g + c)) by (unfold E; exact (bm_ew_CP g pos c regs2 ys)).
assert (E36 : ew E 36 = Z_to_bv 64 (e_n g - c)) by (unfold E; exact (bm_ew_CN g pos c regs2 ys)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (unfold E; exact (bm_ew_SB g pos c regs2 ys)).
assert (EYall : forall j, (j < 9)%nat -> ew E (BM_X0 + j) = Z_to_bv 64 (rd_ib g (c + Z.of_nat j)))
  by (intros j Hj; exact (rd_EY g pos c regs2 9 j Hj)).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ rd_zone g pos sp1 28 48 a ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
pose proof (rd_in_sep B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as HSEP.
cw_keep_j0 HJ HJ0.
unfold cfg_at. change (w64 (rd_pc 10)) with (Z_to_bv 64 0x813cc). change (rd_pc 10) with 0x813cc in HS.
rdb_explore LAWS HJ0 Hfr HC c E35 E32 E36 B2 B33 EFA EYall HSEP
  ltac:(idtac; rdb_bfin LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE B2 B33 E36 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys 10 pv dv od 28 48).
Qed.
End b.
End a.
