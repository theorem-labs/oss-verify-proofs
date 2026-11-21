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
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U3A Require Import U2AObj IfA_base IfAKit IfA_lit IfA_lenb IfA_distb.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
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
  Notation GST := (gms SP Zs S D n OB osz lb la da gp tp FR fc).
  Notation DST := (dst FR fc gp tp SP Zs S D n OB osz lb la da bo).
  Notation CINV m fo := (if_inv SP Zs S OB osz bo wsz whave wnext Wd la da lb db m1 m (Z_to_bv 64 (Zs + 32)) (Z_to_bv 64 (Z.shiftr Zs 3 + 2147450880))
                           (Z_to_bv 64 (Z.shiftr (Zs + 32) 3 + 2147450880)) (Z_to_bv 64 (Zs + 24)) sd id ni ai no ao msg mode hw bw fo).
  Notation SH8 := (Z_to_bv 64 (Z.shiftr (Zs + 8) 3 + 2147450880)).

  Definition dloop_st (x1 x6 x7 x10 x11 x15 x21 : word) (src dist i rem ci co hold bits pc : Z) (m : amem) : machine_state :=
    GST x1 x6 x7 (Z_to_bv 64 rem) x10 x11 (Z_to_bv 64 (- dist)) x15 (Z_to_bv 64 (OB + src + 1)) (Z_to_bv 64 (OB + src)) x21
        SH8 (Z_to_bv 64 i) (Z_to_bv 64 (Zs + 8)) ci co hold bits pc m.
  Definition dloop_post (src dist len ci co hold bits : Z) : machine_state -> Prop :=
    fun ms' => exists (m' : amem) (x1 x6 x7 x10 x11 x15 x21 : word) (fo' : Z -> Z) (i rem : Z),
      ms' = dloop_st x1 x6 x7 x10 x11 x15 x21 src dist i rem ci co hold bits 0x972d0 m' /\ CINV m' fo'
      /\ 0 <= rem <= 2 /\ i + rem = len.

  Lemma if_dloop : forall (N : nat) (m : amem) (fo : Z -> Z) (x1 x6 x7 x10 x11 x15 x21 : word) (src dist len i rem ci co hold bits : Z),
    CINV m fo -> (Z.to_nat rem <= N)%nat ->
    3 <= rem -> 0 <= i -> i + rem = len -> len <= 258 -> 0 <= co -> co + 258 <= osz -> 1 <= dist -> src = co - dist -> 0 <= src ->
    evtF asegs RNG (dloop_post src dist len ci co hold bits)
      (dloop_st x1 x6 x7 x10 x11 x15 x21 src dist i rem ci co hold bits 0x971e4 m).
  Proof using All.
    induction N as [|N IH]; intros until bits; intros INV0 HN REM I0 ILEN LEN CO0 CO258 DIST ESRC SRC0; [lia|].
    open_fctx CX. open_finv INV0. unfold dloop_st, gms.
    clear ZSD WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHZ DJZ SHS DJS RZ RSZ RS RSS.
    zrunb [0x9720c]. remember (OB + co + i) as C0 eqn:EC0.
    zrunb [0x97214]. cbv beta. u8_norm FOR.
    lazymatch goal with |- context [Z_to_bv 64 (fo ?ix)] => remember (fo ix) as b0 eqn:EB0; pose proof (FOR ix ltac:(lia)) as RB0; rewrite <- EB0 in RB0; clear EB0 end.
    out_store OUT FOR (co + i) C0 b0 OUT1 FOR1.
    pose proof (fupd8_range fo (co + i) b0 osz FOR RB0) as FOR1.
    zrunb [0x97244]. cbv beta. u8_norm FOR1.
    lazymatch goal with |- context [Z_to_bv 64 (fupd8 ?f ?ii ?vv ?ix)] =>
      remember (fupd8 f ii vv ix) as b1 eqn:EB1; pose proof (FOR1 ix ltac:(lia)) as RB1; rewrite <- EB1 in RB1; clear EB1 end.
    out_store OUT1 FOR1 (co + i + 1) (C0 + 1) b1 OUT2 FOR2.
    pose proof (fupd8_range _ (co + i + 1) b1 osz FOR1 RB1) as FOR2.
    zrunb [0x97274]. cbv beta. u8_norm FOR2.
    lazymatch goal with |- context [Z_to_bv 64 (fupd8 ?f ?ii ?vv ?ix)] =>
      remember (fupd8 f ii vv ix) as b2 eqn:EB2; pose proof (FOR2 ix ltac:(lia)) as RB2; rewrite <- EB2 in RB2; clear EB2 end.
    out_store OUT2 FOR2 (co + i + 2) (C0 + 2) b2 OUT3 FOR3.
    pose proof (fupd8_range _ (co + i + 2) b2 osz FOR2 RB2) as FOR3.
    zs. rewrite swrap32_small by lia. zs.
    subst C0.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (INV' : CINV mx (fupd8 (fupd8 (fupd8 fo (co + i) b0) (co + i + 1) b1) (co + i + 2) b2)) by close_finv end.
    zs. zbr0 K.
    - eapply (IH _ _ _ _ _ _ _ _ _ src dist len (i + 3) (rem + -3) ci co hold bits INV'); lia.
    - zs. apply evtF_done. eexists. do 7 eexists. eexists. exists (i + 3), (rem + -3).
      split; [unfold dloop_st, gms; reflexivity|]. split; [exact INV'|]. lia.
  Qed.

  Notation AT_LATCH := (at_latch FR fc gp tp SP Zs S D n OB osz Wd wsz whave wnext lb db la da bo m1 sd id ni ai no ao msg mode hw bw).

  Lemma if_dtail : forall (m : amem) (fo : Z -> Z) (x1 x6 x7 x10 x11 x15 x21 : word) (src dist len i rem ci co hold bits : Z),
    CINV m fo ->
    0 <= rem <= 2 -> 0 <= i -> i + rem = len -> len <= 258 -> 0 <= co -> co + 258 <= osz -> 1 <= dist -> src = co - dist -> 0 <= src ->
    evtF asegs RNG (AT_LATCH ci (co + len) hold bits)
      (dloop_st x1 x6 x7 x10 x11 x15 x21 src dist i rem ci co hold bits 0x972d0 m).
  Proof using All.
    intros until bits. intros INV0 REM I0 ILEN LEN CO0 CO258 DIST ESRC SRC0.
    open_fctx CX. open_finv INV0. unfold dloop_st, gms, at_latch.
    clear ZSD WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHZ DJZ SHS DJS RZ RSZ RS RSS.
    zs. zs. zbr0 K.
    -
      zrunb [0x96eac].
      setreg 17 (Z_to_bv 64 (OB + (co + len))) ltac:(f_equal; lia).
      apply evtF_done. eexists. do 12 eexists. exists fo. split; [unfold fms; reflexivity|]. close_finv.
    - remember (OB + co + i) as C0 eqn:EC0.
      zrunb [0x97308]. rewrite <- EC0. cbv beta. u8_norm FOR.
      lazymatch goal with |- context [Z_to_bv 64 (fo ?ix)] => remember (fo ix) as b0 eqn:EB0; pose proof (FOR ix ltac:(lia)) as RB0; rewrite <- EB0 in RB0; clear EB0 end.
      out_store OUT FOR (co + i) C0 b0 OUT1 FOR1.
      pose proof (fupd8_range fo (co + i) b0 osz FOR RB0) as FOR1.
      zs. zs. zbr0 K2.
      +
        zrunb [0x96eac]. subst C0.
        setreg 17 (Z_to_bv 64 (OB + (co + len))) ltac:(f_equal; lia).
        apply evtF_done. eexists. do 12 eexists. eexists. split; [unfold fms; reflexivity|]. close_finv.
      +
        zrunb [0x9735c]. cbv beta. u8_norm FOR1.
        lazymatch goal with |- context [Z_to_bv 64 (fupd8 ?f ?ii ?vv ?ix)] =>
          remember (fupd8 f ii vv ix) as b1 eqn:EB1; pose proof (FOR1 ix ltac:(lia)) as RB1; rewrite <- EB1 in RB1; clear EB1 end.
        out_store OUT1 FOR1 (co + i + 1) (C0 + 1) b1 OUT2 FOR2.
        pose proof (fupd8_range _ (co + i + 1) b1 osz FOR1 RB1) as FOR2.
        zrunb [0x96eac]. subst C0.
        setreg 17 (Z_to_bv 64 (OB + (co + len))) ltac:(f_equal; lia).
        apply evtF_done. eexists. do 12 eexists. eexists. split; [unfold fms; reflexivity|]. close_finv.
  Qed.

  Notation DINV m v0 fo := (if_inv SP Zs S OB osz bo wsz whave wnext Wd la da lb db m1 m v0 (Z_to_bv 64 (Z.shiftr Zs 3 + 2147450880))
                              (Z_to_bv 64 (Z.shiftr (Zs + 32) 3 + 2147450880)) (Z_to_bv 64 (Zs + 24)) sd id ni ai no ao msg mode hw bw fo).

  Lemma if_direct : forall (m : amem) (v0 : word) (fo : Z -> Z) (x1 x6 x10 x13 x16 x21 : word) (len dist ci co hold bits : Z),
    DINV m v0 fo ->
    3 <= len <= 258 -> 1 <= dist -> dist <= co - bo -> 0 <= co -> co + 258 <= osz ->
    evtF asegs RNG (AT_LATCH ci (co + len) hold bits) (DST x1 x6 x10 x13 x16 x21 len dist ci co hold bits 0x971c8 m).
  Proof using All.
    intros until bits. intros INV0 LEN DIST DCO CO0 CO258.
    pose proof CX as CX0. open_fctx CX. open_finv INV0. unfold dst, gms.
    clear ZSD ZOD SOD WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHZ DJZ SHS DJS RZ RSZ RS RSS SHO DJO ROB RSOB.
    zs.
    zrunb [0x971e4].
    setreg 13 (Z_to_bv 64 (- dist)) ltac:(f_equal; lia).
    setreg 16 (Z_to_bv 64 (OB + (co - dist) + 1)) ltac:(f_equal; lia).
    setreg 18 (Z_to_bv 64 (OB + (co - dist))) ltac:(f_equal; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => assert (INV' : CINV mx fo) by close_finv end.
    eapply evtF_cut.
    { eapply (if_dloop (Z.to_nat len) _ fo _ _ _ _ _ _ _ (co - dist) dist len 0 len ci co hold bits INV'); lia. }
    cbv beta. intros ms2 (m2 & y1 & y6 & y7 & y10 & y11 & y15 & y21 & fo2 & i2 & rem2 & -> & INV2 & REM2 & IL2).
    eapply (if_dtail m2 fo2 _ _ _ _ _ _ _ (co - dist) dist len i2 rem2 ci co hold bits INV2); lia.
  Qed.
End P.
End CANSEC1.
