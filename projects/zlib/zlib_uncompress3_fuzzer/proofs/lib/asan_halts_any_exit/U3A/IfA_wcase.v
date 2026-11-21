(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState Inftrees InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AArr U2AKit ItAKit IfAPure IfAStore.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U3A Require Import U2AObj IfA_base IfAKit IfA_lit IfA_direct IfA_win IfA_wcopy IfA_wcopy2 IfA_wloop.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_base | solve_load_sh0 | solve_load_f8 | solve_load_image ].
Local Ltac acc_hint ::= first [ acc_hint_sh | acc_hint_var ].

Section CANSEC1. Context {rc : runConstT}.
Section P.
  Variables (RNG : footprint) (FR : bvmap 5 word) (fc : bv 32) (gp tp : word).
  Variables (SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo : Z) (rdL rdD fw : Z -> Z) (payload : list Z) (m1 : amem).
  Variables (sd : sdc) (id : idc) (ni ai no ao msg mode hw bw : word).
  Hypothesis CX : if_ctx RNG SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1.
  Hypothesis WNZ : wsz <> 0.
  Notation GST := (gms SP Zs S D n OB osz lb la da gp tp FR fc).
  Notation WINV := (winv SP Zs S OB osz Wd wsz whave wnext lb db la da bo fw m1 sd id ni ai no ao msg mode hw bw).
  Notation W34 := (w34 FR fc gp tp SP Zs S D n OB osz lb la da).
  Notation AT_LATCH := (at_latch FR fc gp tp SP Zs S D n OB osz Wd wsz whave wnext lb db la da bo m1 sd id ni ai no ao msg mode hw bw).
  Notation KIT9C := (if_w9c RNG FR fc gp tp SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1 sd id ni ai no ao msg mode hw bw CX WNZ).
  Notation KIT10 := (if_w10 RNG FR fc gp tp SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1 sd id ni ai no ao msg mode hw bw CX WNZ).

  Lemma if_w88 : forall (m : amem) (v0 : word) (fo : Z -> Z) (x10 x16 x21 : word) (fa len dist op ci co hold bits : Z),
    WINV m v0 fo -> 1 <= op -> op < len <= 258 -> 1 <= dist -> 0 <= co - dist -> co + (len - op) <= osz ->
    evtF asegs RNG (AT_LATCH ci (co + (len - op)) hold bits)
      (W34 (Z_to_bv 64 (OB + co)) x10 x16 x21 fa len dist op 0 ci co hold bits 0x9752c m).
  Proof using All.
    intros until bits. intros INV0 OP LEN DIST CD COL.
    pose proof INV0 as [INV1 WINC]. open_fctx CX. open_finv INV1. unfold w34, gms.
    clear ZSD WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHZ DJZ SHS DJS RZ RSZ RS RSS SHO DJO.
    zs. rewrite swrap32_small by lia. zs. zs.
    setreg 6 (Z_to_bv 64 (OB + (co - dist))) ltac:(f_equal; lia).
    zs. zs. zbr0 K.
    - eapply (KIT10 m v0 fo _ _ _ _ _ _ _ (OB + (co - dist)) co (len - op) ci co hold bits INV0); try lia. right. lia.
    - eapply (KIT9C m v0 fo _ _ _ _ _ _ _ (OB + (co - dist)) co (len - op) ci co hold bits INV0); try lia. right. lia.
  Qed.

  Lemma if_w00 : forall (m : amem) (v0 : word) (fo : Z -> Z) (x7 x10 x11 x13 x15 x16 x21 x29 : word) (fa len dist ci co hold bits : Z),
    WINV m v0 fo -> 3 <= len <= 258 -> Wd <= fa -> fa + len <= Wd + 32768 -> 0 <= co -> co + len <= osz ->
    evtF asegs RNG (AT_LATCH ci (co + len) hold bits)
      (GST (Z_to_bv 64 (Zs + 8)) (Z_to_bv 64 fa) x7 (Z_to_bv 64 len) x10 x11 x13 x15 x16 (Z_to_bv 64 dist) x21
           (Z_to_bv 64 (Zs + 32)) x29 (Z_to_bv 64 (Z.shiftr (Zs + 8) 3 + 2147450880)) ci co hold bits 0x974a4 m).
  Proof using All.
    intros until bits. intros INV0 LEN FA1 FA2 CO0 COL.
    pose proof INV0 as [INV1 WINC]. open_fctx CX. open_finv INV1. unfold gms.
    clear ZSD WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHZ DJZ SHS DJS RZ RSZ RS RSS SHO DJO.
    zs. zs. zs. zs. zbr K.
    eapply (KIT9C m v0 fo _ _ _ _ _ _ _ fa co len ci co hold bits INV0); try lia. left. lia.
  Qed.

  Notation WST := (wst FR fc gp tp SP Zs S D n OB osz lb la da).
  Notation DINV m v0 fo := (if_inv SP Zs S OB osz bo wsz whave wnext Wd la da lb db m1 m v0 (Z_to_bv 64 (Z.shiftr Zs 3 + 2147450880))
                              (Z_to_bv 64 (Z.shiftr (Zs + 32) 3 + 2147450880)) (Z_to_bv 64 (Zs + 24)) sd id ni ai no ao msg mode hw bw fo).
  Notation KITLOOP := (if_w34loop RNG FR fc gp tp SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1 sd id ni ai no ao msg mode hw bw CX WNZ).

  Lemma winv_of : forall m v0 fo, DINV m v0 fo -> WINV m v0 fo.
  Proof using CX WNZ.
    intros m v0 fo INV0. split; [exact INV0|].
    open_fctx CX. destruct INV0 as (_ & MU & WM & _). unfold ifW in MU.
    destruct (WIN WNZ) as (WARR & _ & _ & _ & _ & _ & DJW & _). unfold ifW in DJW.
    eapply f8arr_transport; [exact WARR| exact MU| exact WM|]. exact DJW.
  Qed.

  Lemma if_w0 : forall (m : amem) (v0 : word) (fo : Z -> Z) (x1 x6 x10 x15 x16 x21 : word) (len dist op ci co hold bits : Z),
    DINV m v0 fo -> 3 <= len <= 258 -> 1 <= dist -> op = dist - (co - bo) -> 1 <= op <= whave -> wnext = 0 -> bo <= co -> co + 258 <= osz ->
    evtF asegs RNG (AT_LATCH ci (co + len) hold bits)
      (WST x1 x6 x10 (Z_to_bv 64 wnext) x15 x16 x21 len dist op ci co hold bits 0x97380 m).
  Proof using All.
    intros until bits. intros INV0 LEN DIST EOP OP WN0 BCO CO258.
    pose proof (winv_of m v0 fo INV0) as WINV0.
    open_fctx CX. open_finv INV0. unfold wst, gms.
    assert (EW : wsz = 32768) by lia.
    clear ZSD WSZ WNX WIN TOKL TOKD SANE FWR DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHZ DJZ SHS DJS RZ RSZ RS RSS SHO DJO.
    zs. zs. zs. rewrite swrap32_small by lia. zs. zs. rewrite (Z.mod_small _ 4294967296) by lia.
    zs. zs.
    setreg 6 (Z_to_bv 64 (Wd + (wsz - op))) ltac:(f_equal; lia).
    zs. zbr0 K.
    -
      eapply (if_w00 m v0 fo _ _ _ _ _ _ _ _ (Wd + (wsz - op)) len dist ci co hold bits WINV0); lia.
    - zs. zs. zs.
      setreg 11 (Z_to_bv 64 (Wd + (wsz - op))) ltac:(f_equal; lia).
      eapply evtF_cut.
      { eapply (KITLOOP (Z.to_nat op) m v0 fo _ _ _ _ (Wd + (wsz - op)) len dist op op ci co hold bits 0x973ac WINV0); lia. }
      cbv beta. intros ms2 (m2 & y10 & y16 & y21 & fo2 & -> & INV2).
      replace (co + len) with (co + op + (len - op)) by lia.
      eapply (if_w88 m2 v0 fo2 _ _ _ _ len dist op ci (co + op) hold bits INV2); lia.
  Qed.

  Lemma if_wc : forall (m : amem) (v0 : word) (fo : Z -> Z) (x6 x10 x15 x16 x21 : word) (len dist op ci co hold bits : Z),
    DINV m v0 fo -> 3 <= len <= 258 -> 1 <= dist -> op = dist - (co - bo) -> 1 <= op <= whave -> op <= wnext -> bo <= co -> co + 258 <= osz ->
    evtF asegs RNG (AT_LATCH ci (co + len) hold bits)
      (WST (Z_to_bv 64 (Zs + 8)) x6 x10 (Z_to_bv 64 wnext) x15 x16 x21 len dist op ci co hold bits 0x97420 m).
  Proof using All.
    intros until bits. intros INV0 LEN DIST EOP OP WNO BCO CO258.
    pose proof (winv_of m v0 fo INV0) as WINV0.
    open_fctx CX. open_finv INV0. unfold wst, gms.
    assert (EW : wsz = 32768) by lia.
    clear ZSD WSZ WNX WIN TOKL TOKD SANE FWR DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHZ DJZ SHS DJS RZ RSZ RS RSS SHO DJO.
    zs. rewrite swrap32_small by lia. zs. zs. rewrite (Z.mod_small _ 4294967296) by lia.
    zs. zs.
    setreg 6 (Z_to_bv 64 (Wd + (wnext - op))) ltac:(f_equal; lia).
    zs. zbr0 K.
    -
      eapply (if_w00 m v0 fo _ _ _ _ _ _ _ _ (Wd + (wnext - op)) len dist ci co hold bits WINV0); lia.
    - zs. zs. zs.
      setreg 11 (Z_to_bv 64 (Wd + (wnext - op))) ltac:(f_equal; lia).
      eapply evtF_cut.
      { eapply (KITLOOP (Z.to_nat op) m v0 fo _ _ _ _ (Wd + (wnext - op)) len dist op op ci co hold bits 0x97444 WINV0); lia. }
      cbv beta. intros ms2 (m2 & y10 & y16 & y21 & fo2 & -> & INV2).
      replace (co + len) with (co + op + (len - op)) by lia.
      eapply (if_w88 m2 v0 fo2 _ _ _ _ len dist op ci (co + op) hold bits INV2); lia.
  Qed.
End P.
End CANSEC1.
