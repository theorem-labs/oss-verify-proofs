(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2AKit U2AObj ItAKit IfAPure IfA_base IfAKit IfAStore IfA_lenb IfA_win.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
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
  Notation ST := (fms SP Zs S D n OB osz lb la da gp tp FR fc).
  Notation INVM m v0 v24 v48 v56 msg mode fo := (if_inv SP Zs S OB osz bo wsz whave wnext Wd la da lb db m1 m v0 v24 v48 v56 sd id ni ai no ao msg mode hw bw fo).

  Definition at_exit (mode' : word) (ci' co' hold' bits' : Z) : machine_state -> Prop :=
    fun ms' => exists (m' : amem) (x1 x6 x10 x11 x13 x15 x16 x21 v0 v24 v48 v56 msg' : word) (fo' : Z -> Z),
      ms' = ST x1 x6 x10 x11 x13 x15 x16 x21 ci' co' hold' bits' 0x977c4 m' /\ INVM m' v0 v24 v48 v56 msg' mode' fo'.

  Lemma if_ea8 : forall (m : amem) (v0 v24 v48 v56 msg mode : word) (fo : Z -> Z) (x1 x6 x10 x13 x15 x16 x21 : word) (ci co hold bits : Z),
    INVM m v0 v24 v48 v56 msg mode fo ->
    evtF asegs RNG (at_exit (Z_to_bv 64 16209) ci co hold bits)
      (ST x1 x6 x10 (Z_to_bv 64 (Zs + 48)) x13 x15 x16 x21 ci co hold bits 0x97780 m).
  Proof using All.
    intros until bits. intros INV0.
    open_fctx CX. open_finv INV0. unfold fms, at_exit.
    clear WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHO DJO ROB RSOB.
    zrunb [0x977c4].
    apply evtF_done. eexists. do 13 eexists. exists fo. split; [unfold fms; reflexivity|]. close_finv.
  Qed.

  Definition err_post (ci co hold bits : Z) : machine_state -> Prop :=
    fun ms' => exists mode' : word, (mode' = Z_to_bv 64 16191 \/ mode' = Z_to_bv 64 16209) /\ at_exit mode' ci co hold bits ms'.

  Lemma if_eob : forall (m : amem) (v0 v24 v48 v56 msg mode : word) (fo : Z -> Z) (x1 x6 x10 x11 x15 x16 x21 : word) (op ci co hold bits : Z),
    INVM m v0 v24 v48 v56 msg mode fo -> 0 <= op < 256 ->
    evtF asegs RNG (err_post ci co hold bits) (ST x1 x6 x10 x11 (Z_to_bv 64 op) x15 x16 x21 ci co hold bits 0x9775c m).
  Proof using All.
    intros until bits. intros INV0 OP. pose proof INV0 as INV1.
    open_fctx CX. open_finv INV0. unfold fms, err_post.
    clear WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHO DJO ROB RSOB.
    zs. zs. zbr0 K.
    -
      zrunb [0x977c4].
      apply evtF_done. exists (Z_to_bv 64 16191). split; [left; reflexivity|].
      unfold at_exit. eexists. do 13 eexists. exists fo. split; [unfold fms; reflexivity|]. close_finv.
    - zrunb [0x97780].
      eapply evtF_mono; [eapply (if_ea8 m v0 v24 v48 v56 msg mode fo _ _ _ _ _ _ _ ci co hold bits INV1)|].
      cbv beta. intros ms' HP. exists (Z_to_bv 64 16209). split; [right; reflexivity| exact HP].
  Qed.

  Notation LST := (lst FR fc gp tp SP Zs S D n OB osz lb la da).
  Notation WST := (wst FR fc gp tp SP Zs S D n OB osz lb la da).

  Lemma if_baddist : forall (m : amem) (v0 v24 msg mode : word) (fo : Z -> Z) (x1 x6 x10 x11 x13 x15 x16 x21 : word) (len ci co hold bits : Z),
    INVM m v0 v24 (Z_to_bv 64 (Z.shiftr (Zs + 32) 3 + 2147450880)) (Z_to_bv 64 (Zs + 24)) msg mode fo ->
    evtF asegs RNG (err_post ci co hold bits) (LST x1 x6 x10 x11 x13 x15 x16 x21 len ci co hold bits 0x97888 m).
  Proof using All.
    intros until bits. intros INV0. pose proof INV0 as INV1.
    open_fctx CX. open_finv INV0. unfold lst, gms, err_post.
    clear WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHO DJO ROB RSOB.
    zrunb [0x97780].
    eapply evtF_mono; [eapply (if_ea8 m _ _ _ _ msg mode fo _ _ _ _ _ _ _ ci co hold bits INV1)|].
    cbv beta. intros ms' HP. exists (Z_to_bv 64 16209). split; [right; reflexivity| exact HP].
  Qed.

  Lemma if_toofar : forall (m : amem) (v0 msg mode : word) (fo : Z -> Z) (x1 x6 x10 x11 x15 x16 x21 : word) (len dist op ci co hold bits : Z),
    INVM m v0 (Z_to_bv 64 (Z.shiftr Zs 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (Zs + 32) 3 + 2147450880)) (Z_to_bv 64 (Zs + 24)) msg mode fo ->
    evtF asegs RNG (err_post ci co hold bits) (WST x1 x6 x10 x11 x15 x16 x21 len dist op ci co hold bits 0x978b4 m).
  Proof using All.
    intros until bits. intros INV0. pose proof INV0 as INV1.
    open_fctx CX. open_finv INV0. unfold wst, gms, err_post.
    clear WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHO DJO ROB RSOB.
    zrunb [0x97780].
    eapply evtF_mono; [eapply (if_ea8 m _ _ _ _ msg mode fo _ _ _ _ _ _ _ ci co hold bits INV1)|].
    cbv beta. intros ms' HP. exists (Z_to_bv 64 16209). split; [right; reflexivity| exact HP].
  Qed.
End P.
End CANSEC1.
