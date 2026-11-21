(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import Shadow ExecF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState Inftrees InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AShadow U2AArr U2AObj IfAPure.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2B Require Import U2BObj IfB_base IfBKit IfB_wdefs IfB_head IfB_declen IfB_lit IfB_lenb IfB_decdist IfB_distb IfB_direct IfB_err.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section P.
  Variables (RNG : footprint) (FR : bvmap 5 word) (fc : bv 32) (gp tp : word).
  Variables (SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo : Z) (rdL rdD fw : Z -> Z) (payload : list Z) (m1 : amem).
  Variables (sd : sdc) (id : idc) (ni ai no ao msg mode hw bw : word).
  Hypothesis CX : if_ctx RNG SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1.
  Hypothesis WINF : if_window_stmt RNG FR fc gp tp SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1
                                   sd id ni ai no ao msg mode hw bw.
  Notation ST := (fms SP Zs S D n OB osz la da gp tp FR fc).
  Notation LST := (lst FR fc gp tp SP Zs S D n OB osz la da).
  Notation INV m fo := (if_inv SP Zs S OB osz bo wsz whave wnext Wd la da lb db m1 m sd id ni ai no ao msg mode hw bw fo).
  Notation AT_LATCH := (at_latch FR fc gp tp SP Zs S D n OB osz Wd wsz whave wnext lb db la da bo m1 sd id ni ai no ao msg mode hw bw).
  Notation ERR_POST := (err_post FR fc gp tp SP Zs S D n OB osz Wd wsz whave wnext lb db la da bo m1 sd id ni ai no ao hw bw).
  Notation K7 L := (L RNG FR fc gp tp SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1 CX).
  Notation K8 L := (L RNG FR fc gp tp SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1 sd id ni ai no ao msg mode hw bw CX).
  Notation KE L := (L RNG FR fc gp tp SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1 sd id ni ai no ao hw bw CX).

  Definition iter_post (ci co A Q : Z) : machine_state -> Prop :=
    fun ms' => exists ci' co' hold' bits' : Z,
      ci <= ci' <= n /\ co <= co' <= osz /\ 0 <= bits' <= 40 /\ 0 <= hold' < 2 ^ bits'
      /\ 8 * (n - ci') + bits' <= A /\ Q <= 8 * ci' - bits'
      /\ (AT_LATCH ci' co' hold' bits' ms' \/ ERR_POST ci' co' hold' bits' ms').

  Lemma if_iter_dist : forall (m : amem) (fo : Z -> Z) (x5 x6 x7 x10 x24 x28 x29 x30 : word) (len ci co hold bits k ci0 A Q : Z),
    INV m fo ->
    0 <= k < nd -> 16 <= code_op (rdD k) <= 29 -> 1 <= code_val (rdD k) -> code_val (rdD k) + 2 ^ (code_op (rdD k) - 16) - 1 <= 32768 ->
    3 <= len <= 258 -> 0 <= ci0 <= ci -> ci <= n -> 0 <= bits <= 40 -> 0 <= hold < 2 ^ bits -> 13 <= 8 * (n - ci) + bits ->
    bo <= co -> co + 258 <= osz -> 8 * (n - ci) + bits <= A -> Q <= 8 * ci - bits ->
    evtF bsegs RNG (iter_post ci0 co A Q)
      (LST x5 x6 x7 x10 (Z_to_bv 64 (da + 4 * k)) (Z_to_bv 64 (code_op (rdD k))) x24 x28 x29 x30 len ci co hold bits 0x98408 m).
  Proof using All.
    intros until Q. intros INV0 HK HOP HV1 HV LEN CI0 CIN BITS HOLD HA BCO CO258 AB QB.
    open_fctx CX.
    eapply evtF_cut.
    { eapply (K8 if_distb m fo x5 x6 x7 x10 x24 x28 x29 x30 len ci co hold bits k INV0); lia. }
    cbv beta. intros ms2 (y5 & y6 & y7 & y10 & y11 & y14 & y24 & y28 & y29 & dist & ci2 & hold2 & bits2 & DIST & CI2 & BITS2 & HOLD2 & A2 & Q2 & CIN2 & CASE).
    destruct CASE as [[-> DCO] | [(-> & E14 & E28 & DCO & OPW) | [-> TOO]]].
    -
      eapply evtF_mono.
      { eapply (K8 if_direct m fo y5 y6 y7 y10 y11 y14 y24 y28 y29 len dist ci2 co hold2 bits2 INV0); lia. }
      cbv beta. intros ms3 HL. exists ci2, (co + len), hold2, bits2.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. left. exact HL.
    -
      assert (WNZ : wsz <> 0) by lia.
      eapply evtF_mono.
      { eapply (WINF CX m fo y5 y6 y7 y10 y11 y24 y29 len dist (dist - (co - bo)) ci2 co hold2 bits2 INV0); lia. }
      cbv beta. intros ms3 HL. exists ci2, (co + len), hold2, bits2.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. left. exact HL.
    -
      eapply evtF_mono.
      { eapply (KE if_baddist 0x98dd4 m msg mode fo y5 y6 y7 y10 y11 y14 _ y24 y28 y29 _ ci2 co hold2 bits2 INV0). right. reflexivity. }
      cbv beta. intros ms4 HE. exists ci2, co, hold2, bits2.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. right. exact HE.
  Qed.

  Lemma if_iter_len : forall (m : amem) (fo : Z -> Z) (x6 x10 x14 x15 x24 x28 x29 x30 : word) (ci co hold bits k ci0 A Q : Z),
    INV m fo ->
    0 <= k < na -> 16 <= code_op (rdL k) <= 21 -> 3 <= code_val (rdL k) -> code_val (rdL k) + 2 ^ (code_op (rdL k) - 16) - 1 <= 258 ->
    0 <= ci0 <= ci -> ci <= n -> 0 <= bits <= 40 -> 0 <= hold < 2 ^ bits -> 33 <= 8 * (n - ci) + bits ->
    bo <= co -> co + 258 <= osz -> 8 * (n - ci) + bits <= A -> Q <= 8 * ci - bits ->
    evtF bsegs RNG (iter_post ci0 co A Q)
      (ST x6 (Z_to_bv 64 (la + 4 * k)) x10 (Z_to_bv 64 (code_op (rdL k))) x14 x15 x24 x28 x29 x30 ci co hold bits 0x9824c m).
  Proof using All.
    intros until Q. intros INV0 HK HOP HV3 HV CI0 CIN BITS HOLD HA BCO CO258 AB QB.
    open_fctx CX.
    eapply evtF_cut.
    { eapply (K8 if_lenb m fo x6 x10 x14 x15 x24 x28 x29 x30 ci co hold bits k INV0); lia. }
    cbv beta. intros ms2 (y5 & y6 & y7 & y10 & y11 & y14 & y24 & y28 & y29 & y30 & len & ci2 & hold2 & bits2 & -> & LEN & CI2 & BITS2 & HOLD2 & A2 & A2' & Q2 & CIN2).
    eapply evtF_cut.
    { eapply (K8 if_decdist m fo y5 y6 y7 y10 y11 y14 y24 y28 y29 y30 len ci2 co hold2 bits2 INV0); lia. }
    cbv beta. intros ms4 (u5 & u6 & u7 & u10 & u11 & u14 & u24 & u28 & u29 & u30 & hold4 & bits4 & BITS4 & DROP4 & HOLD4 & CASE).
    destruct CASE as [(kd & -> & _ & _ & HKD & HOPD & HVD1 & HVD) | ->].
    - eapply (if_iter_dist m fo u5 u6 u7 u10 u24 u28 u29 u30 len ci2 co hold4 bits4 kd ci0 A Q INV0); lia.
    - eapply evtF_mono.
      { eapply (KE if_baddist 0x98c34 m msg mode fo u5 u6 u7 u10 u11 u14 _ u24 u28 u29 u30 ci2 co hold4 bits4 INV0). left. reflexivity. }
      cbv beta. intros ms5 HE. exists ci2, co, hold4, bits4.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. right. exact HE.
  Qed.

  Lemma if_iter : forall (m : amem) (fo : Z -> Z) (x6 x7 x10 x11 x14 x15 x24 x28 x29 x30 : word) (ci co hold bits : Z),
    INV m fo ->
    0 <= ci -> ci + 6 <= n -> 0 <= bits <= 40 -> bits <= 8 * ci -> 0 <= hold < 2 ^ bits -> bo <= co -> co + 258 <= osz ->
    evtF bsegs RNG (iter_post ci co (8 * (n - ci) + bits - 1) (8 * ci - bits))
      (ST x6 x7 x10 x11 x14 x15 x24 x28 x29 x30 ci co hold bits 0x980bc m).
  Proof using All.
    intros until bits. intros INV0 CI0 CI6 BITS B8 HOLD BCO CO258.
    open_fctx CX.
    eapply evtF_cut.
    { eapply (K7 if_head m sd id ni ai no ao msg mode hw bw fo x6 x7 x10 x11 x14 x15 x24 x28 x29 x30 ci co hold bits INV0); lia. }
    cbv beta. intros ms2 (y6 & y7 & y10 & y11 & y14 & y15 & y24 & y28 & y29 & y30 & ci2 & hold2 & bits2 & -> & CI2 & BITS2 & B82 & HOLD2 & A2).
    eapply evtF_cut.
    { eapply (K7 if_declen m sd id ni ai no ao msg mode hw bw fo y6 y7 y10 y11 y14 y15 y24 y28 y29 y30 ci2 co hold2 bits2 INV0); lia. }
    cbv beta. intros ms3 (z6 & z10 & z14 & z15 & z24 & z28 & z29 & z30 & k & hold3 & bits3 & HK & BITS3 & DROP3 & HOLD3 & CASE).
    destruct CASE as [[-> HV] | [[-> (HOP & HV3 & HV)] | (op & -> & OPR)]].
    -
      eapply evtF_mono.
      { eapply (K8 if_lit m fo z6 z10 (Z_to_bv 64 0) z14 z15 z24 z28 z29 z30 ci2 co hold3 bits3 k INV0); lia. }
      cbv beta. intros ms4 HL. exists ci2, (co + 1), hold3, bits3.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. left. exact HL.
    -
      eapply (if_iter_len m fo z6 z10 z14 z15 z24 z28 z29 z30 ci2 co hold3 bits3 k ci _ _ INV0); lia.
    -
      eapply evtF_mono.
      { eapply (KE if_eob m msg mode fo (Z_to_bv 64 14) z6 (Z_to_bv 64 (la + 4 * k)) z10 z14 z15 z24 z28 z29 z30 op ci2 co hold3 bits3 INV0 OPR). }
      cbv beta. intros ms4 HE. exists ci2, co, hold3, bits3.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. right. exact HE.
  Qed.
End P.
End CANSEC1.
