(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel Require Import ZIface InflateState Inftrees InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import U2AShadow U2AArr U2AKit ItAKit IfAPure IfAStore.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import U2BObj InfBTables IfBTac IfB_base IfBKit IfB_wdefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_base | solve_load_sh0 | solve_load_image ].
Local Ltac acc_hint ::= first [ acc_hint_sh | acc_hint_var ].

Section CANSEC1. Context {rc : runConstT}.
Section P.
  Variables (RNG : footprint) (FR : bvmap 5 word) (fc : bv 32) (gp tp : word).
  Variables (SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo : Z) (rdL rdD fw : Z -> Z) (payload : list Z) (m1 : amem).
  Variables (sd : sdc) (id : idc) (ni ai no ao msg mode hw bw : word).
  Hypothesis CX : if_ctx RNG SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1.
  Notation ST := (fms SP Zs S D n OB osz la da gp tp FR fc).
  Notation INV m fo := (if_inv SP Zs S OB osz bo wsz whave wnext Wd la da lb db m1 m sd id ni ai no ao msg mode hw bw fo).
  Notation AT_LATCH := (at_latch FR fc gp tp SP Zs S D n OB osz Wd wsz whave wnext lb db la da bo m1 sd id ni ai no ao msg mode hw bw).

  Lemma if_lit : forall (m : amem) (fo : Z -> Z) (x6 x10 x11 x14 x15 x24 x28 x29 x30 : word) (ci co hold bits k : Z),
    INV m fo ->
    0 <= k < na -> code_val (rdL k) < 256 -> 0 <= co -> co + 258 <= osz ->
    evtF bsegs RNG (AT_LATCH ci (co + 1) hold bits)
      (ST x6 (Z_to_bv 64 (la + 4 * k)) x10 x11 x14 x15 x24 x28 x29 x30 ci co hold bits 0x982f0 m).
  Proof using All.
    intros until k. intros INV0 HK HV CO0 CO258.
    open_fctx CX. open_finv INV0. unfold fms, gms, xms, at_latch.
    clear ZSD WSZ WNX WIN TOKL TOKD SANE FWR WH WN BO0 DB LB Z0 ZL S0 SL D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2 SHZ DJZ SHS DJS RZ RSZ RS RSS.
    assert (TLC : bytes_at bsegs m la (u32s (fws rdL (Z.to_nat na)))).
    { eapply bytes_at_transport; [exact TLB| exact MU|]. rewrite u32s_length, fws_length.
      replace (Z.of_nat (4 * Z.to_nat na)) with (4 * na) by lia. exact DJTL. }
    pose proof (TLR k HK) as RK. pose proof (code_val_range (rdL k)) as RCV.
    pose proof (code_read_val bsegs m la (fws rdL (Z.to_nat na)) k (rdL k) TLC (f32arr_nth rdL (Z.to_nat na) k ltac:(lia)) ltac:(lia) RK) as RDV.
    zs. zs. pc_dec_ub.
    zs. zs. zs. zs. zs.
    zs. zs. zs.
    zs. rewrite zx16_small by lia.
    zs.
    f8_open_at OUT co C EC CH CC.
    zs.
    f8_close_at CH CC EC (code_val (rdL k)) OUT'; [rewrite unsigned_lit by lia; reflexivity|].
    subst C. setreg 6 (Z_to_bv 64 (OB + (co + 1))) ltac:(f_equal; lia).
    pose proof (fupd8_range fo co (code_val (rdL k)) osz FOR ltac:(lia)) as FOR'.
    apply evtF_done. eexists. do 11 eexists. exists (fupd8 fo co (code_val (rdL k))).
    split; [unfold oms, xms; reflexivity|]. close_finv.
  Qed.
End P.
End CANSEC1.
