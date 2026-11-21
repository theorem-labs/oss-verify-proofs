(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState Inftrees InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AShadow U2AArr U2AKit ItAKit IfAPure IfAStore.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U1B Require Import U2BObj IfBTac IfB_base IfBKit IfB_lenb IfB_distb.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw.
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
  Variables (sd : sdc) (id : idc) (ni ai no ao hw bw : word).
  Hypothesis CX : if_ctx RNG SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1.
  Notation ST := (fms SP Zs S D n OB osz la da gp tp FR fc).
  Notation GST := (gms SP Zs S D n OB osz la da gp tp FR fc).
  Notation OST := (oms SP Zs S D n OB osz la da gp tp FR fc).
  Notation INVM m msg mode fo := (if_inv SP Zs S OB osz bo wsz whave wnext Wd la da lb db m1 m sd id ni ai no ao msg mode hw bw fo).

  Definition at_exit (mode' : word) (ci' co' hold' bits' : Z) : machine_state -> Prop :=
    fun ms' => exists (m' : amem) (x5 x7 x10 x11 x14 x15 x19 x24 x28 x29 x30 msg' : word) (fo' : Z -> Z),
      ms' = OST x5 x7 x10 x11 x14 x15 x19 x24 x28 x29 x30 ci' co' hold' bits' 0x989f8 m' /\ INVM m' msg' mode' fo'.

  Lemma if_e318 : forall (m : amem) (msg mode : word) (fo : Z -> Z) (x5 x6 x7 x10 x14 x15 x24 x28 x29 x30 : word) (ci co hold bits : Z),
    INVM m msg mode fo ->
    evtF bsegs RNG (at_exit (Z_to_bv 64 16209) ci co hold bits)
      (GST x5 x6 x7 x10 (Z_to_bv 64 (Zs + 48)) x14 x15 x24 x28 x29 x30 ci co hold bits 0x989b0 m).
  Proof using All.
    intros until bits. intros INV0.
    open_fctx CX. open_finv INV0. unfold gms, xms, at_exit.
    clear WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHO DJO ROB RSOB.
    zrunu [0x989f8].
    apply evtF_done. eexists. do 12 eexists. exists fo. split; [unfold oms, xms; reflexivity|]. close_finv.
  Qed.

  Definition err_post (ci co hold bits : Z) : machine_state -> Prop :=
    fun ms' => exists mode' : word, (mode' = Z_to_bv 64 16191 \/ mode' = Z_to_bv 64 16209) /\ at_exit mode' ci co hold bits ms'.

  Lemma if_eob : forall (m : amem) (msg mode : word) (fo : Z -> Z) (x5 x6 x7 x10 x14 x15 x24 x28 x29 x30 : word) (op ci co hold bits : Z),
    INVM m msg mode fo -> 0 <= op < 256 ->
    evtF bsegs RNG (err_post ci co hold bits) (GST x5 x6 x7 x10 (Z_to_bv 64 op) x14 x15 x24 x28 x29 x30 ci co hold bits 0x9896c m).
  Proof using All.
    intros until bits. intros INV0 OP. pose proof INV0 as INV1.
    open_fctx CX. open_finv INV0. unfold gms, xms, err_post.
    clear WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHO DJO ROB RSOB.
    zs. zs. zbr0 K.
    -
      zrunu [0x989f8].
      apply evtF_done. exists (Z_to_bv 64 16191). split; [left; reflexivity|].
      unfold at_exit. eexists. do 12 eexists. exists fo. split; [unfold oms, xms; reflexivity|]. close_finv.
    - zrunu [0x989b0].
      eapply evtF_mono; [eapply (if_e318 m msg mode fo _ _ _ _ _ _ _ _ _ _ ci co hold bits INV1)|].
      cbv beta. intros ms' HP. exists (Z_to_bv 64 16209). split; [right; reflexivity| exact HP].
  Qed.

  Lemma if_baddist : forall (pc : Z) (m : amem) (msg mode : word) (fo : Z -> Z) (x5 x6 x7 x10 x11 x14 x15 x24 x28 x29 x30 : word) (ci co hold bits : Z),
    INVM m msg mode fo -> pc = 0x98994 \/ pc = 0x98b34 ->
    evtF bsegs RNG (err_post ci co hold bits) (GST x5 x6 x7 x10 x11 x14 x15 x24 x28 x29 x30 ci co hold bits pc m).
  Proof using All.
    intros until bits. intros INV0 PC. pose proof INV0 as INV1.
    open_fctx CX. open_finv INV0. unfold gms, xms, err_post.
    clear WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHO DJO ROB RSOB.
    destruct PC as [-> | ->].
    - zrunu [0x989b0].
      eapply evtF_mono; [eapply (if_e318 m msg mode fo _ _ _ _ _ _ _ _ _ _ ci co hold bits INV1)|].
      cbv beta. intros ms' HP. exists (Z_to_bv 64 16209). split; [right; reflexivity| exact HP].
    - zrunu [0x989b0].
      eapply evtF_mono; [eapply (if_e318 m msg mode fo _ _ _ _ _ _ _ _ _ _ ci co hold bits INV1)|].
      cbv beta. intros ms' HP. exists (Z_to_bv 64 16209). split; [right; reflexivity| exact HP].
  Qed.
End P.
End CANSEC1.
