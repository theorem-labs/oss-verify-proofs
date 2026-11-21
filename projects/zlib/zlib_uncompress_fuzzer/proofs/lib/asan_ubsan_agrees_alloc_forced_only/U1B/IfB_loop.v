(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow ExecF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr IfAPure.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2BObj IfB_base IfBKit IfB_wdefs IfB_err IfB_exit IfB_iter.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section P.
  Variables (RNG : footprint) (FR : bvmap 5 word) (fc : bv 32) (gp tp : word).
  Variables (sp : word).
  Notation SP := (bv_unsigned sp).
  Variables (lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo : Z) (rdL rdD fw : Z -> Z) (payload : list Z) (m1 : amem).
  Variables (sd : sdc) (id : idc) (ni ai no ao msg mode hw bw : word).
  Hypothesis CX : if_ctx RNG SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1.
  Hypothesis WINF : if_window_stmt RNG FR fc gp tp SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1
                                   sd id ni ai no ao msg mode hw bw.
  Notation ST := (fms SP Zs S D n OB osz la da gp tp FR fc).
  Notation INV m fo := (if_inv SP Zs S OB osz bo wsz whave wnext Wd la da lb db m1 m sd id ni ai no ao msg mode hw bw fo).
  Notation AT_EXIT := (at_exit FR fc gp tp SP Zs S D n OB osz Wd wsz whave wnext lb db la da bo m1 sd id ni ai no ao hw bw).

  Definition loop_post (ci co bits : Z) : machine_state -> Prop :=
    fun ms' => exists (mode' : word) (ci' co' hold' bits' : Z),
      AT_EXIT mode' ci' co' hold' bits' ms'
      /\ ci <= ci' <= n /\ co <= co' <= osz /\ 0 <= bits' <= 40 /\ 0 <= hold' < 2 ^ bits'
      /\ 8 * (n - ci') + bits' <= 8 * (n - ci) + bits - 1 /\ 8 * ci - bits <= 8 * ci' - bits'
      /\ (mode' = mode \/ mode' = Z_to_bv 64 16191 \/ mode' = Z_to_bv 64 16209).

  Lemma if_loop : forall (N : nat) (m : amem) (fo : Z -> Z) (x6 x7 x10 x11 x14 x15 x24 x28 x29 x30 : word) (ci co hold bits : Z),
    INV m fo -> (Z.to_nat (fW n osz ci bits co) <= N)%nat ->
    0 <= ci -> ci + 6 <= n -> 0 <= bits <= 40 -> bits <= 8 * ci -> 0 <= hold < 2 ^ bits -> bo <= co -> co + 258 <= osz ->
    evtF bsegs RNG (loop_post ci co bits) (ST x6 x7 x10 x11 x14 x15 x24 x28 x29 x30 ci co hold bits 0x97e1c m).
  Proof using All.
    induction N as [|N IH]; intros until bits; intros INV0 HN CI0 CI6 BITS B8 HOLD BCO CO258.
    { unfold fW in HN. lia. }
    assert (BO0 : 0 <= bo) by (destruct CX as (_ & (_ & _ & _ & _ & X & _) & _); exact X).
    eapply evtF_cut.
    { eapply (if_iter RNG FR fc gp tp SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1
                      sd id ni ai no ao msg mode hw bw CX WINF m fo x6 x7 x10 x11 x14 x15 x24 x28 x29 x30 ci co hold bits INV0); lia. }
    cbv beta. intros ms2 (ci2 & co2 & hold2 & bits2 & CI2 & CO2 & BITS2 & HOLD2 & A2 & Q2 & CASE).
    destruct CASE as [(m2 & y5 & y7 & y10 & y11 & y14 & y15 & y19 & y24 & y28 & y29 & y30 & fo2 & -> & INV2) | (mode' & MODE' & HE)].
    -
      eapply (if_latch RNG FR fc gp tp sp lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1 CX
                       m2 y5 y7 y10 y11 y14 y15 y19 y24 y28 y29 y30 ci2 co2 hold2 bits2); [lia| lia| |].
      + intros C6 C258. eapply evtF_mono.
        { eapply (IH m2 fo2 _ y7 y10 y11 y14 y15 y24 y28 y29 y30 ci2 co2 hold2 bits2 INV2); try lia. unfold fW in *. lia. }
        cbv beta. intros ms3 (mode3 & ci3 & co3 & hold3 & bits3 & HE3 & F1 & F2 & F3 & F4 & F5 & F6 & F7).
        exists mode3, ci3, co3, hold3, bits3. split; [exact HE3|]. do 6 (split; [lia|]). exact F7.
      + intros z5 z19. apply evtF_done. exists mode, ci2, co2, hold2, bits2.
        split; [unfold at_exit; exists m2, z5, y7, y10, y11, y14, y15, z19, y24, y28, y29, y30, msg, fo2; split; [reflexivity| exact INV2]|].
        do 6 (split; [lia|]). left. reflexivity.
    - apply evtF_done. exists mode', ci2, co2, hold2, bits2. split; [exact HE|]. do 6 (split; [lia|]). right. exact MODE'.
  Qed.
End P.
End CANSEC1.
