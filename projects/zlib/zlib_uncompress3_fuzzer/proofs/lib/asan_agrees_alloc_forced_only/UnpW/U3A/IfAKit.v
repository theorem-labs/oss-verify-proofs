(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Step Frame Arr Bytes Image ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import ExecF Shadow StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2AKit ItAKit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U3A Require Import U2AObj IfA_base.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac open_fctx CX :=
  let CX' := fresh "CXc" in pose proof CX as CX'; unfold if_ctx in CX'; cbv zeta in CX';
  let G1 := fresh "G1" in let G2 := fresh "G2" in let G3 := fresh "G3" in let G4 := fresh "G4" in let G5 := fresh "G5" in
  and_elim CX' 5%nat; intros G1 G2 G3 G4 G5;
  and_elim G1 18%nat; intros Z8 S16 OB8 D8 Z0 ZL S0 SL D1 DL OB0 OBL LOC LOS SPT ZSD ZOD SOD;
  and_elim G2 9%nat; intros NR OSZ LB DB BO0 WH WN WSZ WNX;
  and_elim G3 10%nat; intros RFRM RZ RSZ RS RSS RD RSD ROB RSOB RI;
  and_elim G4 6%nat; intros SHZ SHS SHO DJZ DJS DJO;
  and_elim G5 13%nat; intros TABL TABD;
  let TLX := fresh "TLX" in
  and_elim TABL 9%nat; intros TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL TLX; destruct TLX as (sl1 & sl2 & TLX);
  and_elim TLX 5%nat; intros SHTL RSTL DJSTL TLS1 TLS2;
  let TDX := fresh "TDX" in
  and_elim TABD 9%nat; intros TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD TDX; destruct TDX as (sd1 & sd2 & TDX);
  and_elim TDX 5%nat; intros SHTD RSTD DJSTD TDS1 TDS2;
  intros TOKL TOKD PAYB PAYR PAYN UNP DJD DJP SANE FWR WIN;
  unfold ifW in DJZ, DJS, DJO, DJTL, DJSTL, DJTD, DJSTD, DJD, DJP;
  rewrite !Z.shiftr_div_pow2 in TLS1, TLS2, TDS1, TDS2 by lia; change (2 ^ 3) with 8 in TLS1, TLS2, TDS1, TDS2.
Ltac open_finv H :=
  destruct H as (MI & MU & WM & FRM & STRM & SSC & OUT & FOR);
  unfold ifW in MU; unfold if_frm, if_locals in FRM; unfold if_sc, strm_cells in STRM; unfold if_ic, istate_cells in SSC.
Ltac close_finv := unfold if_inv, ifW, if_frm, if_locals, if_sc, strm_cells, if_ic, istate_cells; do 7 (split; [eassumption|]); eassumption.

Ltac acc_hint_var :=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 (Z.shiftr ?a 3 + 2147450880), ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      match goal with
      | H : rng RNG ?lo ?len |- _ =>
          is_var lo;
          apply (rng_acc_litZ RNG lo len (Z.shiftr a 3 + 2147450880) n nz H (@eq_refl Z nz)); [first [exact (Z.le_refl 1) | lia]| sh_lia]
      end
  end.
