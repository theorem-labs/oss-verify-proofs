(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2AKit ItAKit IfAPure IfAStore.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.U1B Require Import U2BObj. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import IfBTac. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.U1B Require Import IfB_base IfBKit IfB_wdefs IfB_direct.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_base | solve_load_sh0 | solve_load_f8 | solve_load_image ].
Local Ltac acc_hint ::= first [ acc_hint_sh | acc_hint_var ].

(* [comment removed for export] *)
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
  (* [comment removed for export] *)
  Definition winv (m : amem) (fo : Z -> Z) : Prop :=
    if_inv SP Zs S OB osz bo wsz whave wnext Wd la da lb db m1 m sd id ni ai no ao msg mode hw bw fo
    /\ f8arr bsegs m Wd 32768 fw.

  (* [comment removed for export] *)
  Definition tst (x5 x7 x10 x11 x14 x19 x28 x29 x30 : word) (fa cob rem ci hold bits pc : Z) (m : amem) : machine_state :=
    XST x5 (Z_to_bv 64 (OB + cob)) x7 x10 x11 x14 (Z_to_bv 64 rem) x19 (Z_to_bv 64 fa) x28 x29 x30 ci hold bits pc m.
  (* [comment removed for export] *)
  Definition cst (x5 x7 x11 x14 x19 x28 x29 x30 : word) (fa cob i rem ci hold bits pc : Z) (m : amem) : machine_state :=
    tst x5 x7 (Z_to_bv 64 i) x11 x14 x19 x28 x29 x30 fa cob rem ci hold bits pc m.
  (* [comment removed for export] *)
  Definition src_ok (fa k : Z) : Prop := (Wd <= fa /\ fa + k <= Wd + 32768) \/ (OB <= fa /\ fa + k <= OB + osz).

  Definition c3_post (fa cob len ci hold bits : Z) : machine_state -> Prop :=
    fun ms' => exists (m' : amem) (x5 x7 x10 x11 x14 x19 x28 x29 x30 : word) (fo' : Z -> Z) (i rem : Z),
      ms' = tst x5 x7 x10 x11 x14 x19 x28 x29 x30 (fa + i) (cob + i) rem ci hold bits 0x987c0 m' /\ winv m' fo'
      /\ 0 <= rem <= 2 /\ i + rem = len /\ 3 <= i.

  Lemma if_c3loop : forall (N : nat) (m : amem) (fo : Z -> Z) (x5 x7 x11 x14 x19 x28 x29 x30 : word) (fa cob len i rem ci hold bits : Z),
    winv m fo -> (Z.to_nat rem <= N)%nat ->
    3 <= rem -> 0 <= i -> i + rem = len -> len <= 258 -> 0 <= cob -> cob + len <= osz -> src_ok fa len ->
    evtF bsegs RNG (c3_post fa cob len ci hold bits)
      (cst x5 x7 x11 x14 x19 x28 x29 x30 fa cob i rem ci hold bits 0x986b0 m).
  Proof using All.
    induction N as [|N IH]; intros until bits; intros [INV0 WINC] HN REM I0 ILEN LEN CO0 CO258 SRC; [lia|].
    open_fctx CX. open_finv INV0. unfold cst, tst, xms.
    destruct (WIN WNZ) as (_ & WD8 & WD0 & WDL & RWD & RSWD & DJW & SHW & DJSW). unfold ifW in DJW, DJSW.
    assert (DWO : Wd + 32768 <= OB \/ OB + osz <= Wd) by (cbn [disjoint_from] in DJW; lia).
    pose proof FWR as FWR0.
    clear ZSD WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD DJW
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHZ DJZ SHS DJS RZ RSZ RS RSS.
    assert (E32 : Z.of_nat 32768 = 32768) by reflexivity.
    destruct SRC as [SRC|SRC].
    all: zrunu [0x986ec]; remember (OB + cob + i) as C0 eqn:EC0; cbv beta; byte_in b0 RB0 FWR0 FOR;
         out_store OUT FOR (cob + i) C0 b0 OUT1 FOR1;
         pose proof (fupd8_range fo (cob + i) b0 osz FOR RB0) as FOR1;
         zrunu [0x98720]; cbv beta; byte_in b1 RB1 FWR0 FOR1;
         out_store OUT1 FOR1 (cob + i + 1) (C0 + 1) b1 OUT2 FOR2;
         pose proof (fupd8_range _ (cob + i + 1) b1 osz FOR1 RB1) as FOR2;
         zrunu [0x9875c]; cbv beta; byte_in b2 RB2 FWR0 FOR2;
         out_store OUT2 FOR2 (cob + i + 2) (C0 + 2) b2 OUT3 FOR3;
         pose proof (fupd8_range _ (cob + i + 2) b2 osz FOR2 RB2) as FOR3;
         zs; rewrite ?swrap32_small by lia; zs; subst C0;
         (lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
            assert (INV' : winv mx (fupd8 (fupd8 (fupd8 fo (cob + i) b0) (cob + i + 1) b1) (cob + i + 2) b2))
              by (split; [close_finv| eassumption]) end);
         zs; zbr K;
         [ eapply (IH _ _ _ _ _ _ _ _ _ _ fa cob len (i + 3) (rem + -3) ci hold bits INV'); first [lia | left; lia | right; lia]
         | zs; zs; zs;
           setreg 24 (Z_to_bv 64 (fa + (i + 3))) ltac:(f_equal; lia);
           setreg 6 (Z_to_bv 64 (OB + (cob + (i + 3)))) ltac:(f_equal; lia);
           apply evtF_done; eexists; do 9 eexists; eexists; exists (i + 3), (rem + -3);
           split; [unfold tst, xms; reflexivity|]; split; [exact INV'|]; lia ].
  Qed.

  Notation AT_LATCH := (at_latch FR fc gp tp SP Zs S D n OB osz Wd wsz whave wnext lb db la da bo m1 sd id ni ai no ao msg mode hw bw).

  (* [comment removed for export] *)
  Lemma if_wtail : forall (m : amem) (fo : Z -> Z) (x5 x7 x10 x11 x14 x19 x28 x29 x30 : word) (fa cob rem ci hold bits : Z),
    winv m fo -> 0 <= rem <= 2 -> src_ok fa rem -> 0 <= cob -> cob + rem <= osz ->
    evtF bsegs RNG (AT_LATCH ci (cob + rem) hold bits) (tst x5 x7 x10 x11 x14 x19 x28 x29 x30 fa cob rem ci hold bits 0x987c0 m).
  Proof using All.
    intros until bits. intros [INV0 WINC] REM SRC COB COB258. open_fctx CX. open_finv INV0. unfold tst, xms, at_latch.
    destruct (WIN WNZ) as (_ & WD8 & WD0 & WDL & RWD & RSWD & DJW & SHW & DJSW). unfold ifW in DJW, DJSW.
    assert (DWO : Wd + 32768 <= OB \/ OB + osz <= Wd) by (cbn [disjoint_from] in DJW; lia).
    pose proof FWR as FWR0.
    clear ZSD WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD DJW
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHZ DJZ SHS DJS RZ RSZ RS RSS.
    assert (E32 : Z.of_nat 32768 = 32768) by reflexivity.
    zs. zbr K0.
    - (* [comment removed for export] *)
      replace (cob + rem) with cob by lia.
      apply evtF_done. eexists. do 11 eexists. exists fo. split; [unfold oms, xms; reflexivity|]. close_finv.
    - remember (OB + cob) as C0 eqn:EC0.
      destruct SRC as [SRC|SRC].
      all: zrunu [0x987f8]; cbv beta; byte_in b0 RB0 FWR0 FOR;
           out_store OUT FOR cob C0 b0 OUT1 FOR1;
           pose proof (fupd8_range fo cob b0 osz FOR RB0) as FOR1;
           zs; zbr K2;
           [ zs; zs; subst C0;
             setreg 6 (Z_to_bv 64 (OB + (cob + rem))) ltac:(f_equal; lia);
             apply evtF_done; eexists; do 11 eexists; eexists; split; [unfold oms, xms; reflexivity|]; close_finv
           | zrunu [0x98830]; cbv beta; byte_in b1 RB1 FWR0 FOR1;
             out_store OUT1 FOR1 (cob + 1) (C0 + 1) b1 OUT2 FOR2;
             pose proof (fupd8_range _ (cob + 1) b1 osz FOR1 RB1) as FOR2;
             zs; subst C0;
             setreg 6 (Z_to_bv 64 (OB + (cob + rem))) ltac:(f_equal; lia);
             apply evtF_done; eexists; do 11 eexists; eexists; split; [unfold oms, xms; reflexivity|]; close_finv ].
  Qed.

  (* [comment removed for export] *)
  Lemma if_wrest : forall (pc : Z) (m : amem) (fo : Z -> Z) (x5 x7 x10 x11 x14 x19 x28 x29 x30 : word) (fa cob rem ci hold bits : Z),
    pc = 0x98690 \/ pc = 0x986a4 \/ pc = 0x988c8 ->
    winv m fo -> 0 <= rem <= 258 -> src_ok fa rem -> 0 <= cob -> cob + rem <= osz ->
    evtF bsegs RNG (AT_LATCH ci (cob + rem) hold bits) (tst x5 x7 x10 x11 x14 x19 x28 x29 x30 fa cob rem ci hold bits pc m).
  Proof using All.
    intros until bits. intros PC INV0 REM SRC COB COBR.
    assert (C3 : 3 <= rem -> forall (y5 y7 y10 y11 y14 y19 y28 y29 y30 : word),
              evtF bsegs RNG (AT_LATCH ci (cob + rem) hold bits) (tst y5 y7 y10 y11 y14 y19 y28 y29 y30 fa cob rem ci hold bits 0x986ac m)).
    { intros R3 y5 y7 y10 y11 y14 y19 y28 y29 y30. unfold tst, xms.
      zs. (* [comment removed for export] *)
      eapply evtF_cut.
      { eapply (if_c3loop (Z.to_nat rem) m fo _ _ _ _ _ _ _ _ fa cob rem 0 rem ci hold bits INV0); try lia. exact SRC. }
      cbv beta. intros ms2 (m2 & z5 & z7 & z10 & z11 & z14 & z19 & z28 & z29 & z30 & fo2 & i2 & rem2 & -> & INV2 & REM2 & IL2 & I3).
      replace (cob + rem) with (cob + i2 + rem2) by lia.
      eapply (if_wtail m2 fo2 _ _ _ _ _ _ _ _ _ (fa + i2) (cob + i2) rem2 ci hold bits INV2); try lia.
      unfold src_ok in *. destruct SRC as [SRC|SRC]; [left| right]; lia. }
    unfold tst, xms in *.
    destruct PC as [-> | [-> | ->]].
    - zs. zs. zbr K.
      + eapply (if_wtail m fo _ _ _ _ _ _ _ _ _ fa cob rem ci hold bits INV0); try lia. exact SRC.
      + zs. eapply C3. lia.
    - zs. zs. zbr K.
      + eapply (if_wtail m fo _ _ _ _ _ _ _ _ _ fa cob rem ci hold bits INV0); try lia. exact SRC.
      + eapply C3. lia.
    - zs. zs. zbr K.
      + eapply (if_wtail m fo _ _ _ _ _ _ _ _ _ fa cob rem ci hold bits INV0); try lia. exact SRC.
      + zs. eapply C3. lia.
  Qed.
End P.
End CANSEC1.
