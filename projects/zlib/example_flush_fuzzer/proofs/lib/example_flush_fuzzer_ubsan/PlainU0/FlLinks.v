(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require PropExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import ExFlushIface FlLibStmtU.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require ZIface DeflateState Deflate InflateState Inflate InflateSync HarnessKit HarnessFacts Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module ZI := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ZIface.
(* kitfix4 alias stage: Module ZD := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Deflate expanded *)
Module ZDS := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.DeflateState.
Module ZIS := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateState.
(* kitfix4 alias stage: Module ZSY := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateSync expanded *)
Module ZHF := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.HarnessFacts.
Module ZPG := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Prog.

Definition DZS0 : ZI.zstrm := ZI.mkZS 0 0 1 2 ZI.MSG_NULL.
Definition IZS0 : ZI.zstrm := ZI.mkZS 0 0 1 0 ZI.MSG_NULL.
Definition WANS (wb : ZPG.blk) : option (ZPG.blk * (Z -> Z)) := Some (wb, fun _ : Z => 0).

Section LINKS.
Context {fx : PropExec.FPState}.
Variable FL : @fl_lib fx.
Variable FLM : flush_model.
Variable wb : ZPG.blk.
Variable d : list Z.
Let n : Z := ZI.zlength d.
Let cl0 : Z := CLEN (ZI.zlength d).

Definition DZC1 : ZI.ZCall := ZI.mkZCall (firstn 3 d) cl0 DZS0.
Definition DSV1 : ZDS.deflate_state := ZDS.set_strm (fl_ds0 FL) (ZDS.cstrm_of_call DZC1).
Definition DX1 : ZDS.deflate_state := fst (OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Deflate.deflate_core DSV1 3).
Definition DRC1 : Z := snd (OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Deflate.deflate_core DSV1 3).
Definition DOUT1 : list Z := ZDS.cs_output (ZDS.ds_strm DX1).
Definition DNOUT1 : Z := Z.of_nat (length (ZDS.cs_out_rev (ZDS.ds_strm DX1))).
Definition DNIN1 : Z := ZDS.cs_next_in (ZDS.ds_strm DX1).
Definition DZR1 : ZI.zstrm := ZI.zr_strm (ZDS.zret_of_cs (ZDS.ds_strm DX1) DRC1).
Definition LC1 : list Z := DOUT1 ++ repeat 0 (Z.to_nat (cl0 - DNOUT1)).
Definition B3 : Z := nth 3 LC1 0.
Definition LC1' : list Z := firstn 3 LC1 ++ [(B3 + 1) mod 256] ++ skipn 4 LC1.
Definition DZC2 : ZI.ZCall := ZI.mkZCall (firstn (Z.to_nat (n - 3)) (skipn (Z.to_nat DNIN1) d)) (cl0 - DNOUT1) DZR1.
Definition DSV2 : ZDS.deflate_state := ZDS.set_strm DX1 (ZDS.cstrm_of_call DZC2).
Definition DX2 : ZDS.deflate_state := fst (OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Deflate.deflate_core DSV2 4).
Definition DRC2 : Z := snd (OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Deflate.deflate_core DSV2 4).
Definition DOUT2 : list Z := ZDS.cs_output (ZDS.ds_strm DX2).
Definition DNOUT2 : Z := Z.of_nat (length (ZDS.cs_out_rev (ZDS.ds_strm DX2))).
Definition DZR2 : ZI.zstrm := ZI.zr_strm (ZDS.zret_of_cs (ZDS.ds_strm DX2) DRC2).
Definition LC2 : list Z := firstn (Z.to_nat DNOUT1) LC1' ++ DOUT2 ++ skipn (Z.to_nat (DNOUT1 + DNOUT2)) LC1'.
Definition DTOT : Z := ZI.zs_total_out DZR2.

Let c : list Z := fm_compr FLM d.
Let clen : Z := fm_clen FLM d.
Definition IZC1 : ZI.ZCall := ZI.mkZCall (firstn 2 c) n IZS0.
Definition ICALL1 := ZHF.inflate_p ZIS.ivar_ref (WANS wb) (fl_is0 FL) IZC1 0.
Definition IS1 : ZIS.inflate_state := fst (fst ICALL1).
Definition IR1 : ZI.ZRet := snd (fst ICALL1).
Definition ICONS1 : Z := ZI.zr_consumed IR1.
Definition INOUT1 : Z := ZI.zlength (ZI.zr_output IR1).
Definition IZC2 : ZI.ZCall := ZI.mkZCall (firstn (Z.to_nat (clen - 2)) (skipn (Z.to_nat ICONS1) c)) (n - INOUT1) (ZI.zr_strm IR1).
Definition ISYNC := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateSync.inflateSync_m ZIS.ivar_ref IS1 IZC2.
Definition IS2 : ZIS.inflate_state := fst ISYNC.
Definition IR2 : ZI.ZRet := snd ISYNC.
Definition ICONS2 : Z := ZI.zr_consumed IR2.
Definition IZC3 : ZI.ZCall :=
  ZI.mkZCall (firstn (Z.to_nat (clen - 2 - ICONS2)) (skipn (Z.to_nat (ICONS1 + ICONS2)) c)) (n - INOUT1) (ZI.zr_strm IR2).
Definition ICALL3 := ZHF.inflate_p ZIS.ivar_ref (WANS wb) IS2 IZC3 4.
Definition IS3 : ZIS.inflate_state := fst (fst ICALL3).
Definition IR3 : ZI.ZRet := snd (fst ICALL3).

Record fl_links : Prop := FL_LINKS {
  lk_ds1   : fl_dsafe FL DSV1 3;
  lk_rc1   : DRC1 = 0;
  lk_ds2   : fl_dsafe FL DSV2 4;
  lk_st2   : ZDS.ds_status DX2 = 113 \/ ZDS.ds_status DX2 = 666;
  lk_busy  : fm_busy FLM d = (ZDS.ds_status DX2 =? 113);
  lk_tot   : fm_busy FLM d = false -> fm_tot FLM d = DTOT;
  lk_compr : fm_compr FLM d = LC2;
  lk_isf1  : fl_isafe FL (fl_is0 FL) IZC1 0;
  lk_nw1   : snd ICALL1 = None;
  lk_i1    : fm_i1 FLM c n = (if ZI.zr_rc IR1 =? 0 then I1_OK else I1_E (ZI.zr_rc IR1));
  lk_ssf   : ZI.zr_rc IR1 = ZI.Z_OK -> fl_ssafe FL IS1 IZC2;
  lk_is    : fm_is FLM c clen n = (if ZI.zr_rc IR2 =? 0 then IS_OK else IS_E (ZI.zr_rc IR2));
  lk_isf3  : ZI.zr_rc IR1 = ZI.Z_OK -> ZI.zr_rc IR2 = ZI.Z_OK -> fl_isafe FL IS2 IZC3 4;
  lk_i2    : fm_i2 FLM c clen n = match snd ICALL3 with Some _ => I2_W | None => I2_R (ZI.zr_rc IR3) end;
  lk_i2b   : snd ICALL3 <> None -> fm_i2b FLM c clen n = ZI.zr_rc IR3 }.
End LINKS.

Strategy expand [DZC1 DSV1 DX1 DRC1 DOUT1 DNOUT1 DNIN1 DZR1 LC1 B3 LC1' DZC2 DSV2 DX2 DRC2 DOUT2 DNOUT2 DZR2 LC2 DTOT
                 IZC1 ICALL1 IS1 IR1 ICONS1 INOUT1 IZC2 ISYNC IS2 IR2 ICONS2 IZC3 ICALL3 IS3 IR3 WANS DZS0 IZS0].
