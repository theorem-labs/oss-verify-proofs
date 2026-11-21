(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState Inftrees InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AArr U2AKit ItAKit IfAPure IfAStore.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U1A Require Import U2AObj IfA_base IfAKit IfA_lit IfA_direct.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
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
  Notation GST := (gms SP Zs S D n OB osz lb la da gp tp FR fc).
  Definition winv (m : amem) (v0 : word) (fo : Z -> Z) : Prop :=
    if_inv SP Zs S OB osz bo wsz whave wnext Wd la da lb db m1 m v0 (Z_to_bv 64 (Z.shiftr Zs 3 + 2147450880))
           (Z_to_bv 64 (Z.shiftr (Zs + 32) 3 + 2147450880)) (Z_to_bv 64 (Zs + 24)) sd id ni ai no ao msg mode hw bw fo
    /\ f8arr asegs m Wd 32768 fw.

  Definition cst (x10 x11 x13 x15 x16 x21 x29 : word) (fa cob rem ci ca hold bits pc : Z) (m : amem) : machine_state :=
    GST (Z_to_bv 64 (Zs + 8)) (Z_to_bv 64 fa) (Z_to_bv 64 (OB + cob)) (Z_to_bv 64 rem) x10 x11 x13 x15 x16
        (Z_to_bv 64 (Z.shiftr Zs 3 + 2147450880)) x21 (Z_to_bv 64 (Zs + 32)) x29 (Z_to_bv 64 (Z.shiftr (Zs + 8) 3 + 2147450880))
        ci ca hold bits pc m.
  Definition src_ok (fa k : Z) : Prop := (Wd <= fa /\ fa + k <= Wd + 32768) \/ (OB <= fa /\ fa + k <= OB + osz).

  Definition c3_post (v0 : word) (fa cob len ci hold bits : Z) : machine_state -> Prop :=
    fun ms' => exists (m' : amem) (x10 x11 x15 x16 x21 x29 : word) (fo' : Z -> Z) (i rem : Z),
      ms' = cst x10 x11 (Z_to_bv 64 i) x15 x16 x21 x29 fa cob rem ci (cob + i - 3) hold bits 0x972cc m' /\ winv m' v0 fo'
      /\ 0 <= rem <= 2 /\ i + rem = len /\ 3 <= i.

  Lemma if_c3loop : forall (N : nat) (m : amem) (v0 : word) (fo : Z -> Z) (x10 x11 x15 x16 x21 x29 : word) (fa cob len i rem ci ca hold bits : Z),
    winv m v0 fo -> (Z.to_nat rem <= N)%nat ->
    3 <= rem -> 0 <= i -> i + rem = len -> len <= 258 -> 0 <= cob -> cob + len <= osz -> src_ok fa len ->
    evtF asegs RNG (c3_post v0 fa cob len ci hold bits)
      (cst x10 x11 (Z_to_bv 64 i) x15 x16 x21 x29 fa cob rem ci ca hold bits 0x971e4 m).
  Proof using All.
    induction N as [|N IH]; intros until bits; intros [INV0 WINC] HN REM I0 ILEN LEN CO0 CO258 SRC; [lia|].
    open_fctx CX. open_finv INV0. unfold cst, gms.
    destruct (WIN WNZ) as (_ & WD8 & WD0 & WDL & RWD & RSWD & DJW & SHW & DJSW). unfold ifW in DJW, DJSW.
    assert (DWO : Wd + 32768 <= OB \/ OB + osz <= Wd) by (cbn [disjoint_from] in DJW; lia).
    pose proof FWR as FWR0.
    clear ZSD WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD DJW
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHZ DJZ SHS DJS RZ RSZ RS RSS.
    assert (E32 : Z.of_nat 32768 = 32768) by reflexivity.
    destruct SRC as [SRC|SRC].
    all: zrunb [0x97210]; remember (OB + cob + i) as C0 eqn:EC0; cbv beta; byte_in b0 RB0 FWR0 FOR;
         out_store OUT FOR (cob + i) C0 b0 OUT1 FOR1;
         pose proof (fupd8_range fo (cob + i) b0 osz FOR RB0) as FOR1;
         zrunb [0x97240]; cbv beta; byte_in b1 RB1 FWR0 FOR1;
         out_store OUT1 FOR1 (cob + i + 1) (C0 + 1) b1 OUT2 FOR2;
         pose proof (fupd8_range _ (cob + i + 1) b1 osz FOR1 RB1) as FOR2;
         zrunb [0x97270]; cbv beta; byte_in b2 RB2 FWR0 FOR2;
         out_store OUT2 FOR2 (cob + i + 2) (C0 + 2) b2 OUT3 FOR3;
         pose proof (fupd8_range _ (cob + i + 2) b2 osz FOR2 RB2) as FOR3;
         zs; rewrite swrap32_small by lia; zs; subst C0;
         (lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
            assert (INV' : winv mx v0 (fupd8 (fupd8 (fupd8 fo (cob + i) b0) (cob + i + 1) b1) (cob + i + 2) b2))
              by (split; [close_finv| eassumption]) end);
         zs; zbr K;
         [ setreg 17 (Z_to_bv 64 (OB + (cob + i))) ltac:(f_equal; lia);
           eapply (IH _ v0 _ _ _ _ _ _ _ fa cob len (i + 3) (rem + -3) ci (cob + i) hold bits INV'); first [lia | left; lia | right; lia]
         | zs; setreg 17 (Z_to_bv 64 (OB + (cob + (i + 3) - 3))) ltac:(f_equal; lia);
           apply evtF_done; eexists; do 6 eexists; eexists; exists (i + 3), (rem + -3);
           split; [unfold cst, gms; reflexivity|]; split; [exact INV'|]; lia ].
  Qed.

  Notation AT_LATCH := (at_latch FR fc gp tp SP Zs S D n OB osz Wd wsz whave wnext lb db la da bo m1 sd id ni ai no ao msg mode hw bw).

  Lemma if_wtail0 : forall (m : amem) (v0 : word) (fo : Z -> Z) (x10 x11 x13 x15 x16 x21 x29 : word) (fa cob rem ci ca hold bits : Z),
    winv m v0 fo -> 0 <= cob <= osz ->
    evtF asegs RNG (AT_LATCH ci cob hold bits) (cst x10 x11 x13 x15 x16 x21 x29 fa cob rem ci ca hold bits 0x972d8 m).
  Proof using All.
    intros until bits. intros [INV0 WINC] COB. open_fctx CX. open_finv INV0. unfold cst, gms, at_latch.
    destruct (WIN WNZ) as (_ & WD8 & WD0 & WDL & RWD & RSWD & DJW & SHW & DJSW). unfold ifW in DJW, DJSW.
    assert (DWO : Wd + 32768 <= OB \/ OB + osz <= Wd) by (cbn [disjoint_from] in DJW; lia).
    pose proof FWR as FWR0.
    clear ZSD WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD DJW
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHZ DJZ SHS DJS RZ RSZ RS RSS.
    assert (E32 : Z.of_nat 32768 = 32768) by reflexivity.
    zrunb [0x96b4c].
    apply evtF_done. eexists. do 12 eexists. exists fo. split; [unfold fms; reflexivity|]. close_finv.
  Qed.

  Lemma if_wtail12 : forall (m : amem) (v0 : word) (fo : Z -> Z) (x10 x11 x13 x15 x16 x21 x29 : word) (fa cob rem ci ca hold bits : Z),
    winv m v0 fo -> 1 <= rem <= 2 -> src_ok fa rem -> 0 <= cob -> cob + rem <= osz ->
    evtF asegs RNG (AT_LATCH ci (cob + rem) hold bits) (cst x10 x11 x13 x15 x16 x21 x29 fa cob rem ci ca hold bits 0x97158 m).
  Proof using All.
    intros until bits. intros [INV0 WINC] REM SRC COB COB258. open_fctx CX. open_finv INV0. unfold cst, gms, at_latch.
    destruct (WIN WNZ) as (_ & WD8 & WD0 & WDL & RWD & RSWD & DJW & SHW & DJSW). unfold ifW in DJW, DJSW.
    assert (DWO : Wd + 32768 <= OB \/ OB + osz <= Wd) by (cbn [disjoint_from] in DJW; lia).
    pose proof FWR as FWR0.
    clear ZSD WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD DJW
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHZ DJZ SHS DJS RZ RSZ RS RSS.
    assert (E32 : Z.of_nat 32768 = 32768) by reflexivity.
    remember (OB + cob) as C0 eqn:EC0.
    destruct SRC as [SRC|SRC].
    all: zrunb [0x97180]; cbv beta; byte_in b0 RB0 FWR0 FOR;
         out_store OUT FOR cob C0 b0 OUT1 FOR1;
         pose proof (fupd8_range fo cob b0 osz FOR RB0) as FOR1;
         zs; zbr K2;
         [ zrunb [0x96b4c]; subst C0;
           setreg 17 (Z_to_bv 64 (OB + (cob + rem))) ltac:(f_equal; lia);
           apply evtF_done; eexists; do 12 eexists; eexists; split; [unfold fms; reflexivity|]; close_finv
         | zrunb [0x971bc]; cbv beta; byte_in b1 RB1 FWR0 FOR1;
           out_store OUT1 FOR1 (cob + 1) (C0 + 1) b1 OUT2 FOR2;
           pose proof (fupd8_range _ (cob + 1) b1 osz FOR1 RB1) as FOR2;
           zrunb [0x96b4c]; subst C0;
           setreg 17 (Z_to_bv 64 (OB + (cob + rem))) ltac:(f_equal; lia);
           apply evtF_done; eexists; do 12 eexists; eexists; split; [unfold fms; reflexivity|]; close_finv ].
  Qed.

End P.
End CANSEC1.
