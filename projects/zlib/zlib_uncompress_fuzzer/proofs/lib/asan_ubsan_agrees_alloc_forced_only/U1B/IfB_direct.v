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
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2AKit ItAKit IfAPure IfAStore.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2BObj IfBTac IfB_base IfBKit IfB_wdefs IfB_lenb IfB_distb.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_base | solve_load_sh0 | solve_load_f8 | solve_load_image ].
Local Ltac acc_hint ::= first [ acc_hint_sh | acc_hint_var ].

Ltac out_store OUT R idx CA v OUT' R' :=
  let CH := fresh "CH" in let CC := fresh "CC" in
  lazymatch type of OUT with f8arr ?segs ?m ?A ?n ?f =>
    destruct (f8_open segs m A n f idx OUT ltac:(lia)) as [CH CC]; clear OUT;
    replace (A + idx) with CA in CC by lia;
    zs;
    lazymatch type of CH with f8hole _ ?m' _ _ _ _ =>
      assert (OUT' : f8arr segs m' A n (fupd8 f idx v));
      [ lazymatch type of CC with rw_cells _ _ _ [C1 ?b] =>
          apply (f8_close segs m' A n f idx b v CH); [lia | replace (A + idx) with CA by lia; exact CC | rewrite unsigned_lit by lia; reflexivity ] end
      | clear CH CC ]
    end
  end.

Section CANSEC1. Context {rc : runConstT}.
Section P.
  Variables (RNG : footprint) (FR : bvmap 5 word) (fc : bv 32) (gp tp : word).
  Variables (SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo : Z) (rdL rdD fw : Z -> Z) (payload : list Z) (m1 : amem).
  Variables (sd : sdc) (id : idc) (ni ai no ao msg mode hw bw : word).
  Hypothesis CX : if_ctx RNG SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1.
  Notation GST := (gms SP Zs S D n OB osz la da gp tp FR fc).
  Notation DST := (dst FR fc gp tp SP Zs S D n OB osz la da).
  Notation INV m fo := (if_inv SP Zs S OB osz bo wsz whave wnext Wd la da lb db m1 m sd id ni ai no ao msg mode hw bw fo).

  Definition dloop_st (x6 x7 x10 x11 x14 x24 x28 x29 : word) (src i rem ci co hold bits pc : Z) (m : amem) : machine_state :=
    GST (Z_to_bv 64 i) x6 x7 x10 x11 x14 (Z_to_bv 64 rem) x24 x28 x29 (Z_to_bv 64 (OB + src)) ci co hold bits pc m.
  Definition dloop_post (src len ci co hold bits : Z) : machine_state -> Prop :=
    fun ms' => exists (m' : amem) (x6 x7 x10 x11 x14 x24 x28 x29 : word) (fo' : Z -> Z) (i rem : Z),
      ms' = dloop_st x6 x7 x10 x11 x14 x24 x28 x29 src i rem ci co hold bits 0x98428 m' /\ INV m' fo'
      /\ 0 <= rem <= 2 /\ i + rem = len.

  Lemma if_dloop : forall (N : nat) (m : amem) (fo : Z -> Z) (x6 x7 x10 x11 x14 x24 x28 x29 : word) (src dist len i rem ci co hold bits : Z),
    INV m fo -> (Z.to_nat rem <= N)%nat ->
    3 <= rem -> 0 <= i -> i + rem = len -> len <= 258 -> 0 <= co -> co + 258 <= osz -> 1 <= dist -> src = co - dist -> 0 <= src ->
    evtF bsegs RNG (dloop_post src len ci co hold bits)
      (dloop_st x6 x7 x10 x11 x14 x24 x28 x29 src i rem ci co hold bits 0x98328 m).
  Proof using All.
    induction N as [|N IH]; intros until bits; intros INV0 HN REM I0 ILEN LEN CO0 CO258 DIST ESRC SRC0; [lia|].
    open_fctx CX. open_finv INV0. unfold dloop_st, gms, xms.
    clear ZSD WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHZ DJZ SHS DJS RZ RSZ RS RSS.
    zrunu [0x98338]. remember (OB + co + i) as C0 eqn:EC0.
    zrunu [0x98364]. cbv beta. u8_norm FOR.
    lazymatch goal with |- context [Z_to_bv 64 (fo ?ix)] => remember (fo ix) as b0 eqn:EB0; pose proof (FOR ix ltac:(lia)) as RB0; rewrite <- EB0 in RB0; clear EB0 end.
    out_store OUT FOR (co + i) C0 b0 OUT1 FOR1.
    pose proof (fupd8_range fo (co + i) b0 osz FOR RB0) as FOR1.
    zrunu [0x98398]. cbv beta. u8_norm FOR1.
    lazymatch goal with |- context [Z_to_bv 64 (fupd8 ?f ?ii ?vv ?ix)] =>
      remember (fupd8 f ii vv ix) as b1 eqn:EB1; pose proof (FOR1 ix ltac:(lia)) as RB1; rewrite <- EB1 in RB1; clear EB1 end.
    out_store OUT1 FOR1 (co + i + 1) (C0 + 1) b1 OUT2 FOR2.
    pose proof (fupd8_range _ (co + i + 1) b1 osz FOR1 RB1) as FOR2.
    zrunu [0x983cc]. cbv beta. u8_norm FOR2.
    lazymatch goal with |- context [Z_to_bv 64 (fupd8 ?f ?ii ?vv ?ix)] =>
      remember (fupd8 f ii vv ix) as b2 eqn:EB2; pose proof (FOR2 ix ltac:(lia)) as RB2; rewrite <- EB2 in RB2; clear EB2 end.
    out_store OUT2 FOR2 (co + i + 2) (C0 + 2) b2 OUT3 FOR3.
    pose proof (fupd8_range _ (co + i + 2) b2 osz FOR2 RB2) as FOR3.
    zs. rewrite ?swrap32_small by lia. zs.
    subst C0.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (INV' : INV mx (fupd8 (fupd8 (fupd8 fo (co + i) b0) (co + i + 1) b1) (co + i + 2) b2)) by close_finv end.
    zs. zbr0 K.
    - eapply (IH _ _ _ _ _ _ _ _ _ _ src dist len (i + 3) (rem + -3) ci co hold bits INV'); lia.
    - zs. apply evtF_done. eexists. do 8 eexists. eexists. exists (i + 3), (rem + -3).
      split; [unfold dloop_st, gms, xms; reflexivity|]. split; [exact INV'|]. lia.
  Qed.

  Notation AT_LATCH := (at_latch FR fc gp tp SP Zs S D n OB osz Wd wsz whave wnext lb db la da bo m1 sd id ni ai no ao msg mode hw bw).

  Lemma if_dtail : forall (m : amem) (fo : Z -> Z) (x6 x7 x10 x11 x14 x24 x28 x29 : word) (src dist len i rem ci co hold bits : Z),
    INV m fo ->
    0 <= rem <= 2 -> 0 <= i -> i + rem = len -> len <= 258 -> 0 <= co -> co + 258 <= osz -> 1 <= dist -> src = co - dist -> 0 <= src ->
    evtF bsegs RNG (AT_LATCH ci (co + len) hold bits)
      (dloop_st x6 x7 x10 x11 x14 x24 x28 x29 src i rem ci co hold bits 0x98428 m).
  Proof using All.
    intros until bits. intros INV0 REM I0 ILEN LEN CO0 CO258 DIST ESRC SRC0.
    open_fctx CX. open_finv INV0. unfold dloop_st, gms, xms, at_latch.
    clear ZSD WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHZ DJZ SHS DJS RZ RSZ RS RSS.
    zs. zs. zbr0 K.
    -
      setreg 6 (Z_to_bv 64 (OB + (co + len))) ltac:(f_equal; lia).
      apply evtF_done. eexists. do 11 eexists. exists fo. split; [unfold oms, xms; reflexivity|]. close_finv.
    - remember (OB + co + i) as C0 eqn:EC0.
      zrunu [0x98468]. rewrite <- ?EC0. cbv beta. u8_norm FOR.
      lazymatch goal with |- context [Z_to_bv 64 (fo ?ix)] => remember (fo ix) as b0 eqn:EB0; pose proof (FOR ix ltac:(lia)) as RB0; rewrite <- EB0 in RB0; clear EB0 end.
      out_store OUT FOR (co + i) C0 b0 OUT1 FOR1.
      pose proof (fupd8_range fo (co + i) b0 osz FOR RB0) as FOR1.
      zs. zbr0 K2.
      +
        zs. zs. subst C0.
        setreg 6 (Z_to_bv 64 (OB + (co + len))) ltac:(f_equal; lia).
        apply evtF_done. eexists. do 11 eexists. eexists. split; [unfold oms, xms; reflexivity|]. close_finv.
      +
        zrunu [0x984a8]. cbv beta. u8_norm FOR1.
        lazymatch goal with |- context [Z_to_bv 64 (fupd8 ?f ?ii ?vv ?ix)] =>
          remember (fupd8 f ii vv ix) as b1 eqn:EB1; pose proof (FOR1 ix ltac:(lia)) as RB1; rewrite <- EB1 in RB1; clear EB1 end.
        out_store OUT1 FOR1 (co + i + 1) (C0 + 1) b1 OUT2 FOR2.
        pose proof (fupd8_range _ (co + i + 1) b1 osz FOR1 RB1) as FOR2.
        zs. zs. subst C0.
        setreg 6 (Z_to_bv 64 (OB + (co + len))) ltac:(f_equal; lia).
        apply evtF_done. eexists. do 11 eexists. eexists. split; [unfold oms, xms; reflexivity|]. close_finv.
  Qed.

  Lemma if_direct : forall (m : amem) (fo : Z -> Z) (x5 x6 x7 x10 x11 x14 x24 x28 x29 : word) (len dist ci co hold bits : Z),
    INV m fo ->
    3 <= len <= 258 -> 1 <= dist -> dist <= co - bo -> 0 <= co -> co + 258 <= osz ->
    evtF bsegs RNG (AT_LATCH ci (co + len) hold bits) (DST x5 x6 x7 x10 x11 x14 x24 x28 x29 len dist ci co hold bits 0x98308 m).
  Proof using All.
    intros until bits. intros INV0 LEN DIST DCO CO0 CO258. pose proof INV0 as INVK.
    pose proof CX as CX0. open_fctx CX. open_finv INV0. unfold dst, gms, xms.
    clear ZSD ZOD SOD WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHZ DJZ SHS DJS RZ RSZ RS RSS SHO DJO ROB RSOB FRM STRM SSC OUT FOR.
    zrunu [0x98328].
    setreg 30 (Z_to_bv 64 (OB + (co - dist))) ltac:(f_equal; lia).
    eapply evtF_cut.
    { eapply (if_dloop (Z.to_nat len) m fo _ _ _ _ _ _ _ _ (co - dist) dist len 0 len ci co hold bits INVK); lia. }
    cbv beta. intros ms2 (m2 & y6 & y7 & y10 & y11 & y14 & y24 & y28 & y29 & fo2 & i2 & rem2 & -> & INV2 & REM2 & IL2).
    eapply (if_dtail m2 fo2 _ _ _ _ _ _ _ _ (co - dist) dist len i2 rem2 ci co hold bits INV2); lia.
  Qed.
End P.
End CANSEC1.
