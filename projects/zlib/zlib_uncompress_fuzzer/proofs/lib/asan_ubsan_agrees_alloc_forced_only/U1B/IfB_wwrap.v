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
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2BObj IfBTac IfB_base IfBKit IfB_wdefs IfB_direct IfB_wcopy IfB_wcase.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_base | solve_load_sh0 | solve_load_f8 | solve_load_image ].
Local Ltac acc_hint ::= first [ acc_hint_sh | acc_hint_var ].

Ltac byte_in b RB R1 R2 :=
  lazymatch goal with |- context [bv_unsigned (Z_to_bv 8 ?v)] =>
    let E := fresh "EB" in
    remember v as b eqn:E;
    assert (RB : 0 <= b < 256) by (rewrite E; first [apply R1; lia | apply R2; lia]);
    clear E; rewrite (u8_val b RB) end.

Section CANSEC1. Context {rc : runConstT}.
Section P.
  Variables (RNG : footprint) (FR : bvmap 5 word) (fc : bv 32) (gp tp : word).
  Variables (SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo : Z) (rdL rdD fw : Z -> Z) (payload : list Z) (m1 : amem).
  Variables (sd : sdc) (id : idc) (ni ai no ao msg mode hw bw : word).
  Hypothesis CX : if_ctx RNG SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1.
  Hypothesis WNZ : wsz <> 0.
  Notation XST := (xms SP Zs S D n OB osz la da gp tp FR fc).
  Notation INV m fo := (if_inv SP Zs S OB osz bo wsz whave wnext Wd la da lb db m1 m sd id ni ai no ao msg mode hw bw fo).
  Notation WINV := (winv SP Zs S OB osz Wd wsz whave wnext lb db la da bo fw m1 sd id ni ai no ao msg mode hw bw).
  Notation WST := (wst FR fc gp tp SP Zs S D n OB osz wnext la da).
  Notation AT_LATCH := (at_latch FR fc gp tp SP Zs S D n OB osz Wd wsz whave wnext lb db la da bo m1 sd id ni ai no ao msg mode hw bw).
  Notation K8 L := (L RNG FR fc gp tp SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1 sd id ni ai no ao msg mode hw bw CX WNZ).

  Definition w1st (x5 x11 x14 x29 : word) (fa cob cnt rem dist ci hold bits pc : Z) (m : amem) : machine_state :=
    XST x5 (Z_to_bv 64 cnt) (Z_to_bv 64 fa) (Z_to_bv 64 (OB + cob)) x11 x14 (Z_to_bv 64 rem) (Z_to_bv 64 (OB + cob)) (Z_to_bv 64 fa)
        (Z_to_bv 64 (OB + cob + 1)) x29 (Z_to_bv 64 dist) ci hold bits pc m.
  Definition w1_post (cob rem dist ci hold bits : Z) : machine_state -> Prop :=
    fun ms' => exists (m' : amem) (x6 x7 x10 x11 x14 x19 x24 x28 : word) (fo' : Z -> Z),
      ms' = XST (Z_to_bv 64 (OB + cob)) x6 x7 x10 x11 x14 (Z_to_bv 64 rem) x19 x24 x28 (Z_to_bv 64 (OB + cob)) (Z_to_bv 64 dist)
                ci hold bits 0x987cc m' /\ WINV m' fo'.

  Lemma if_w1loop : forall (N : nat) (m : amem) (fo : Z -> Z) (x5 x11 x14 x29 : word) (fa cob cnt rem dist ci hold bits : Z),
    WINV m fo -> (Z.to_nat cnt <= N)%nat ->
    1 <= cnt -> cnt <= 32768 -> Wd <= fa -> fa + cnt <= Wd + 32768 -> 0 <= cob -> cob + cnt <= osz ->
    evtF bsegs RNG (w1_post (cob + cnt) rem dist ci hold bits) (w1st x5 x11 x14 x29 fa cob cnt rem dist ci hold bits 0x98290 m).
  Proof using All.
    induction N as [|N IH]; intros until bits; intros [INV0 WINC] HN CNT CNT2 FA1 FA2 CO0 COC; [lia|].
    open_fctx CX. open_finv INV0. unfold w1st, xms.
    destruct (WIN WNZ) as (_ & WD8 & WD0 & WDL & RWD & RSWD & DJW & SHW & DJSW). unfold ifW in DJW, DJSW.
    assert (DWO : Wd + 32768 <= OB \/ OB + osz <= Wd) by (cbn [disjoint_from] in DJW; lia).
    pose proof FWR as FWR0.
    clear ZSD WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD DJW
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHZ DJZ SHS DJS RZ RSZ RS RSS.
    assert (E32 : Z.of_nat 32768 = 32768) by reflexivity.
    remember (OB + cob) as C0 eqn:EC0.
    zrunu [0x982d0]. cbv beta. byte_in b0 RB0 FWR0 FOR.
    out_store OUT FOR cob C0 b0 OUT1 FOR1.
    pose proof (fupd8_range fo cob b0 osz FOR RB0) as FOR1.
    do 5 zs. rewrite ?swrap32_small by lia. subst C0.
    setreg 19 (Z_to_bv 64 (OB + (cob + 1))) ltac:(f_equal; lia).
    setreg 28 (Z_to_bv 64 (OB + (cob + 1) + 1)) ltac:(f_equal; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (INV' : WINV mx (fupd8 fo cob b0)) by (split; [close_finv| eassumption]) end.
    zs. zbr K.
    - eapply evtF_mono.
      + eapply (IH _ _ _ _ _ _ (fa + 1) (cob + 1) (cnt + -1) rem dist ci hold bits INV'); lia.
      + intros ms' HP. replace (cob + 1 + (cnt + -1)) with (cob + cnt) in HP by lia. exact HP.
    - zs. replace (cob + cnt) with (cob + 1) by lia.
      apply evtF_done. eexists. do 8 eexists. eexists. split; [unfold xms; reflexivity| exact INV'].
  Qed.

  Definition w2st (x6 x7 x19 x24 x28 : word) (fa cob cnt rem dist ci hold bits pc : Z) (m : amem) : machine_state :=
    XST (Z_to_bv 64 (OB + cob)) x6 x7 (Z_to_bv 64 cnt) (Z_to_bv 64 fa) (Z_to_bv 64 fa) (Z_to_bv 64 rem) x19 x24 x28 (Z_to_bv 64 (OB + cob))
        (Z_to_bv 64 dist) ci hold bits pc m.
  Definition w2_post (cob rem dist ci hold bits : Z) : machine_state -> Prop :=
    fun ms' => exists (m' : amem) (x5 x7 x10 x11 x14 x19 x24 x28 : word) (fo' : Z -> Z),
      ms' = XST x5 (Z_to_bv 64 (OB + cob)) x7 x10 x11 x14 (Z_to_bv 64 rem) x19 x24 x28 (Z_to_bv 64 (OB + cob)) (Z_to_bv 64 dist)
                ci hold bits 0x98860 m' /\ WINV m' fo'.

  Lemma if_w2loop : forall (N : nat) (m : amem) (fo : Z -> Z) (x6 x7 x19 x24 x28 : word) (fa cob cnt rem dist ci hold bits : Z),
    WINV m fo -> (Z.to_nat cnt <= N)%nat ->
    1 <= cnt -> cnt <= 32768 -> Wd <= fa -> fa + cnt <= Wd + 32768 -> 0 <= cob -> cob + cnt <= osz ->
    evtF bsegs RNG (w2_post (cob + cnt) rem dist ci hold bits) (w2st x6 x7 x19 x24 x28 fa cob cnt rem dist ci hold bits 0x987e0 m).
  Proof using All.
    induction N as [|N IH]; intros until bits; intros [INV0 WINC] HN CNT CNT2 FA1 FA2 CO0 COC; [lia|].
    open_fctx CX. open_finv INV0. unfold w2st, xms.
    destruct (WIN WNZ) as (_ & WD8 & WD0 & WDL & RWD & RSWD & DJW & SHW & DJSW). unfold ifW in DJW, DJSW.
    assert (DWO : Wd + 32768 <= OB \/ OB + osz <= Wd) by (cbn [disjoint_from] in DJW; lia).
    pose proof FWR as FWR0.
    clear ZSD WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD DJW
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHZ DJZ SHS DJS RZ RSZ RS RSS.
    assert (E32 : Z.of_nat 32768 = 32768) by reflexivity.
    remember (OB + cob) as C0 eqn:EC0.
    zrunu [0x98818]. cbv beta. byte_in b0 RB0 FWR0 FOR.
    out_store OUT FOR cob C0 b0 OUT1 FOR1.
    pose proof (fupd8_range fo cob b0 osz FOR RB0) as FOR1.
    do 4 zs. rewrite ?swrap32_small by lia. subst C0.
    setreg 5 (Z_to_bv 64 (OB + (cob + 1))) ltac:(f_equal; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (INV' : WINV mx (fupd8 fo cob b0)) by (split; [close_finv| eassumption]) end.
    zs. zbr K.
    - eapply evtF_mono.
      + eapply (IH _ _ _ _ _ _ _ (fa + 1) (cob + 1) (cnt + -1) rem dist ci hold bits INV'); lia.
      + intros ms' HP. replace (cob + 1 + (cnt + -1)) with (cob + cnt) in HP by lia. exact HP.
    - zs. replace (cob + cnt) with (cob + 1) by lia.
      apply evtF_done. eexists. do 8 eexists. eexists. split; [unfold xms; reflexivity| exact INV'].
  Qed.

  Lemma if_w94 : forall (m : amem) (fo : Z -> Z) (x5 x7 x10 x11 x14 x19 x24 x28 x29 : word) (cob rem dist ci hold bits : Z),
    WINV m fo -> 0 <= rem <= 258 -> 1 <= dist <= cob -> cob + rem <= osz ->
    evtF bsegs RNG (AT_LATCH ci (cob + rem) hold bits)
      (XST x5 (Z_to_bv 64 (OB + cob)) x7 x10 x11 x14 (Z_to_bv 64 rem) x19 x24 x28 x29 (Z_to_bv 64 dist) ci hold bits 0x9862c m).
  Proof using All.
    intros until bits. intros INV0 REM DIST COBR.
    open_fctx CX. unfold xms.
    clear ZSD WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHZ DJZ SHS DJS RZ RSZ RS RSS SHO DJO.
    zs. setreg 24 (Z_to_bv 64 (OB + (cob - dist))) ltac:(f_equal; lia).
    eapply (K8 if_wrest 0x98630 m fo _ _ _ _ _ _ _ _ _ (OB + (cob - dist)) cob rem ci hold bits); [right; left; reflexivity | exact INV0 | lia | right; lia | lia | lia].
  Qed.

  Lemma if_ww : forall (m : amem) (fo : Z -> Z) (x5 x6 x7 x10 x11 x24 x29 : word) (len dist op ci co hold bits : Z),
    INV m fo -> 3 <= len <= 258 -> 1 <= dist <= 32768 -> op = dist - (co - bo) -> 1 <= op <= whave -> 0 < wnext < op -> bo <= co -> co + 258 <= osz ->
    evtF bsegs RNG (AT_LATCH ci (co + len) hold bits) (WST x5 x6 x7 x10 x11 x24 x29 len dist op ci co hold bits 0x98244 m).
  Proof using All.
    intros until bits. intros INV0 LEN DIST EOP OP WNO BCO CO258.
    assert (WINV0 : WINV m fo) by (eapply winv_of; eassumption).
    open_fctx CX. open_finv INV0. unfold wst, gms, xms.
    assert (EW : wsz = 32768) by lia.
    assert (EWH : whave = wsz) by lia.
    destruct (WIN WNZ) as (_ & WD8 & WD0 & WDL & _).
    clear ZSD WSZ WNX WIN TOKL TOKD SANE FWR DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHZ DJZ SHS DJS RZ RSZ RS RSS SHO DJO.
    zs. zs. rewrite ?swrap32_small by lia. zs. zs. rewrite ?(Z.mod_small _ 4294967296) by lia.
    zs. zs.
    setreg 24 (Z_to_bv 64 (Wd + (wnext + wsz - op))) ltac:(f_equal; lia).
    zs. pc_dec_ub. zs. zsb. zsb. zs. zs.
    zs. zs. setreg 6 (Z_to_bv 64 (op - wnext)) ltac:(rewrite ?swrap32_small by lia; f_equal; lia).
    zs. zbr K.
    -
      zs.
      eapply (K8 if_wrest 0x9861c m fo _ _ _ _ _ _ _ _ _ (Wd + (wnext + wsz - op)) co len ci hold bits); [left; reflexivity | exact WINV0 | lia | left; lia | lia | lia].
    - zs. setreg 15 (Z_to_bv 64 (len - (op - wnext))) ltac:(rewrite ?swrap32_small by lia; f_equal; lia).
      zs. zs. zs.
      eapply evtF_cut.
      { eapply (if_w1loop (Z.to_nat (op - wnext)) m fo _ _ _ _ (Wd + (wnext + wsz - op)) co (op - wnext) (len - (op - wnext)) dist ci hold bits WINV0); lia. }
      cbv beta. intros ms2 (m2 & z6 & z7 & z10 & z11 & z14 & z19 & z24 & z28 & fo2 & -> & INV2).
      pose proof INV2 as [INV2a _]. destruct INV2a as (_ & _ & _ & FRM2 & _). unfold if_frm, if_locals in FRM2.
      unfold xms.
      set (co1 := co + (op - wnext)) in *. set (rem1 := len - (op - wnext)) in *.
      zs. zs. zbr K1.
      +
        zs. zs.
        replace (co + len) with (co1 + rem1) by (unfold co1, rem1; lia).
        eapply (K8 if_wrest 0x98854 m2 fo2 _ _ _ _ _ _ _ _ _ Wd co1 rem1 ci hold bits); [right; right; reflexivity | exact INV2 | unfold rem1; lia | left; unfold rem1; lia | unfold co1; lia | unfold co1, rem1; lia].
      + zs. setreg 15 (Z_to_bv 64 (rem1 - wnext)) ltac:(rewrite ?swrap32_small by (unfold rem1; lia); f_equal; lia).
        zs. zs.
        eapply evtF_cut.
        { eapply (if_w2loop (Z.to_nat wnext) m2 fo2 _ _ _ _ _ Wd co1 wnext (rem1 - wnext) dist ci hold bits INV2); unfold co1, rem1; lia. }
        cbv beta. intros ms3 (m3 & u5 & u7 & u10 & u11 & u14 & u19 & u24 & u28 & fo3 & -> & INV3).
        unfold xms.
        zs. pc_dec_ub.
        replace (co + len) with (co1 + wnext + (rem1 - wnext)) by (unfold co1, rem1; lia).
        eapply (if_w94 m3 fo3 _ _ _ _ _ _ _ _ _ (co1 + wnext) (rem1 - wnext) dist ci hold bits INV3); unfold co1, rem1; lia.
  Qed.

  Lemma if_window : forall (m : amem) (fo : Z -> Z) (x5 x6 x7 x10 x11 x24 x29 : word) (len dist op ci co hold bits : Z),
    INV m fo -> 3 <= len <= 258 -> 1 <= dist <= 32768 -> op = dist - (co - bo) -> 1 <= op <= whave -> bo <= co -> co + 258 <= osz ->
    evtF bsegs RNG (AT_LATCH ci (co + len) hold bits) (WST x5 x6 x7 x10 x11 x24 x29 len dist op ci co hold bits 0x9823c m).
  Proof using All.
    intros until bits. intros INV0 LEN DIST EOP OP BCO CO258.
    pose proof (fun pc H => K8 if_w1piece pc m fo x5 x6 x7 x10 x11 x24 x29 len dist op ci co hold bits H INV0 LEN DIST EOP OP BCO CO258) as H1.
    pose proof (if_ww m fo x5 x6 x7 x10 x11 x24 x29 len dist op ci co hold bits INV0 LEN DIST EOP OP) as H2.
    open_fctx CX. unfold wst, gms, xms in *.
    assert (WB : 0 <= wnext <= 32768) by lia.
    clear ZSD WSZ WNX WIN TOKL TOKD SANE FWR DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHZ DJZ SHS DJS RZ RSZ RS RSS SHO DJO.
    zs. zbr K0.
    - apply (H1 0x984b4). left. split; [reflexivity | lia].
    - zs. zbr K1.
      + apply (H1 0x9856c). right. split; [reflexivity | lia].
      + apply H2; lia.
  Qed.
End P.
End CANSEC1.
