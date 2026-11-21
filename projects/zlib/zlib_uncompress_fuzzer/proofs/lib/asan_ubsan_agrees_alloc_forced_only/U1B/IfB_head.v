(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2AKit ItAKit IfAPure.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2BObj IfBTac IfB_base IfBKit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
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
  Hypothesis CX : if_ctx RNG SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1.
  Notation ST := (fms SP Zs S D n OB osz la da gp tp FR fc).

  Definition head_post (m : amem) (ci co hold bits : Z) : machine_state -> Prop :=
    fun ms' => exists (x6 x7 x10 x11 x14 x15 x24 x28 x29 x30 : word) (ci' hold' bits' : Z),
      ms' = ST x6 x7 x10 x11 x14 x15 x24 x28 x29 x30 ci' co hold' bits' 0x97e70 m
      /\ ci <= ci' <= ci + 2 /\ 15 <= bits' <= 40 /\ bits' <= 8 * ci' /\ 0 <= hold' < 2 ^ bits'
      /\ 8 * (n - ci') + bits' = 8 * (n - ci) + bits.

  Lemma if_head : forall (m : amem) (sd : sdc) (id : idc) (ni ai no ao msg mode hw bw : word) (fo : Z -> Z)
      (x6 x7 x10 x11 x14 x15 x24 x28 x29 x30 : word) (ci co hold bits : Z),
    if_inv SP Zs S OB osz bo wsz whave wnext Wd la da lb db m1 m sd id ni ai no ao msg mode hw bw fo ->
    0 <= ci -> ci + 6 <= n -> 0 <= bits <= 40 -> bits <= 8 * ci -> 0 <= hold < 2 ^ bits ->
    evtF bsegs RNG (head_post m ci co hold bits) (ST x6 x7 x10 x11 x14 x15 x24 x28 x29 x30 ci co hold bits 0x97e1c m).
  Proof using All.
    intros until bits. intros INV CI0 CI6 BITS B8 HOLD.
    open_fctx CX. open_finv INV. unfold fms, gms, xms, head_post.
    clear ZSD ZOD SOD WSZ WNX WIN TOKL TOKD SANE FWR WH WN BO0 LB DB OSZ Z0 ZL S0 SL OB0 OBL
          TLB TL4 TL0 TLN0 TLHI RTL DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHO DJO ROB RSOB FRM STRM SSC OUT FOR.
    pose proof (pow2_40 bits BITS) as P40.
    zs. zbr0 K.
    -
      apply evtF_done. do 10 eexists. exists ci, hold, bits. split; [unfold fms, gms, xms; reflexivity|]. lia.
    -
      assert (PAYC : bytes_at bsegs m D (map (Z_to_bv 8) payload)).
      { eapply bytes_at_transport; [exact PAYB| exact MU|]. rewrite length_map, PAYN. exact DJD. }
      destruct (unp_check_mu bsegs _ _ _ _ _ (D + ci) 1 UNP MU DJP ltac:(lia) ltac:(lia) ltac:(lia) (mod8_room1 _)) as (b0 & RDB0 & CK0).
      zs. zs. pc_dec_ub. zs. pc_dec_ub.
      zs. zs. zs. rewrite sxb_sval.
      ck_branchJ 14 0x97e3c CK0.
      destruct (unp_check_mu bsegs _ _ _ _ _ (D + ci + 1) 1 UNP MU DJP ltac:(lia) ltac:(lia) ltac:(lia) (mod8_room1 _)) as (b1 & RDB1 & CK1).
      pose proof (pay_read bsegs _ D payload ci PAYC ltac:(lia)) as RDP0. fold (bz payload ci) in RDP0.
      pose proof (bz_range payload ci PAYR) as BZ0.
      zs. zs. zs. rewrite sxb_sval. zs. cbv beta. rewrite (bz_val payload ci PAYR).
      ck_branchJ 15 0x97e50 CK1.
      pose proof (pay_read bsegs _ D payload (ci + 1) PAYC ltac:(lia)) as RDP1. fold (bz payload (ci + 1)) in RDP1.
      replace (D + (ci + 1)) with (D + ci + 1) in RDP1 by lia.
      pose proof (bz_range payload (ci + 1) PAYR) as BZ1.
      zs. zs. cbv beta. rewrite (bz_val payload (ci + 1) PAYR).
      zrunb [0x97e70].
      setreg 25 (Z_to_bv 64 (hold + bz payload ci * 2 ^ bits + bz payload (ci + 1) * 2 ^ (bits + 8))) ltac:(rewrite !shl_byte by lia; f_equal; lia).
      setreg 26 (Z_to_bv 64 (bits + 16)) ltac:(rewrite lor_16 by lia; reflexivity).
      setreg 13 (Z_to_bv 64 (D + (ci + 2))) ltac:(f_equal; lia).
      pose proof (pull2_bound hold bits (bz payload ci) (bz payload (ci + 1)) ltac:(lia) HOLD BZ0 BZ1) as PB2.
      apply evtF_done. do 10 eexists. exists (ci + 2), (hold + bz payload ci * 2 ^ bits + bz payload (ci + 1) * 2 ^ (bits + 8)), (bits + 16).
      split; [unfold fms, gms, xms; reflexivity|]. lia.
  Qed.
End P.
End CANSEC1.
