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
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2BObj IfBTac IfB_base IfBKit IfB_wdefs IfB_direct IfB_wcopy.
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
  Notation TST := (tst FR fc gp tp SP Zs S D n OB osz la da).
  Notation WST := (wst FR fc gp tp SP Zs S D n OB osz wnext la da).
  Notation SRC_OK := (src_ok OB osz Wd).
  Notation AT_LATCH := (at_latch FR fc gp tp SP Zs S D n OB osz Wd wsz whave wnext lb db la da bo m1 sd id ni ai no ao msg mode hw bw).
  Notation K8 L := (L RNG FR fc gp tp SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1 sd id ni ai no ao msg mode hw bw CX WNZ).

  Lemma winv_of : forall m fo, INV m fo -> WINV m fo.
  Proof using CX WNZ.
    intros m fo INV0. split; [exact INV0|].
    open_fctx CX. destruct INV0 as (_ & MU & WM & _). unfold ifW in MU.
    destruct (WIN WNZ) as (WARR & _ & _ & _ & _ & _ & DJW & _). unfold ifW in DJW.
    eapply f8arr_transport; [exact WARR| exact MU| exact WM|]. exact DJW.
  Qed.

  Definition w34 (x6 x7 x10 x14 x29 : word) (fa cob cnt rem dist ci hold bits pc : Z) (m : amem) : machine_state :=
    XST (Z_to_bv 64 fa) x6 x7 x10 (Z_to_bv 64 (OB + cob)) x14 (Z_to_bv 64 rem) (Z_to_bv 64 (OB + cob)) (Z_to_bv 64 fa) (Z_to_bv 64 cnt) x29
        (Z_to_bv 64 dist) ci hold bits pc m.
  Definition w34_post (cob rem dist ci hold bits : Z) : machine_state -> Prop :=
    fun ms' => exists (m' : amem) (x5 x10 x11 x14 x19 x24 x28 x29 : word) (fo' : Z -> Z),
      ms' = XST x5 (Z_to_bv 64 (OB + cob)) (Z_to_bv 64 (OB + cob)) x10 x11 x14 (Z_to_bv 64 rem) x19 x24 x28 x29 (Z_to_bv 64 dist)
                ci hold bits 0x98628 m' /\ WINV m' fo'.

  Lemma if_w34loop : forall (N : nat) (m : amem) (fo : Z -> Z) (x6 x7 x10 x14 x29 : word) (fa cob cnt rem dist ci hold bits pc : Z),
    WINV m fo -> (Z.to_nat cnt <= N)%nat ->
    1 <= cnt -> cnt <= 32768 -> Wd <= fa -> fa + cnt <= Wd + 32768 -> 0 <= cob -> cob + cnt <= osz ->
    pc = 0x984f4 \/ pc = 0x985a8 ->
    evtF bsegs RNG (w34_post (cob + cnt) rem dist ci hold bits) (w34 x6 x7 x10 x14 x29 fa cob cnt rem dist ci hold bits pc m).
  Proof using All.
    induction N as [|N IH]; intros until pc; intros [INV0 WINC] HN CNT CNT2 FA1 FA2 CO0 COC PC; [lia|].
    open_fctx CX. open_finv INV0. unfold w34, xms.
    destruct (WIN WNZ) as (_ & WD8 & WD0 & WDL & RWD & RSWD & DJW & SHW & DJSW). unfold ifW in DJW, DJSW.
    assert (DWO : Wd + 32768 <= OB \/ OB + osz <= Wd) by (cbn [disjoint_from] in DJW; lia).
    pose proof FWR as FWR0.
    clear ZSD WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD DJW
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHZ DJZ SHS DJS RZ RSZ RS RSS.
    assert (E32 : Z.of_nat 32768 = 32768) by reflexivity.
    remember (OB + cob) as C0 eqn:EC0.
    destruct PC as [-> | ->].
    all: first [zrunu [0x98534] | zrunu [0x985e8]]; cbv beta; byte_in b0 RB0 FWR0 FOR;
         out_store OUT FOR cob C0 b0 OUT1 FOR1;
         pose proof (fupd8_range fo cob b0 osz FOR RB0) as FOR1;
         do 3 zs; rewrite ?swrap32_small by lia; subst C0;
         setreg 19 (Z_to_bv 64 (OB + (cob + 1))) ltac:(f_equal; lia);
         (lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
            assert (INV' : WINV mx (fupd8 fo cob b0)) by (split; [close_finv| eassumption]) end);
         zs; zbr K;
         [ eapply evtF_mono;
           [ eapply (IH _ _ _ _ _ _ _ (fa + 1) (cob + 1) (cnt + -1) rem dist ci hold bits _ INV'); first [lia | left; reflexivity | right; reflexivity]
           | intros ms' HP; replace (cob + 1 + (cnt + -1)) with (cob + cnt) in HP by lia; exact HP ]
         | zs; replace (cob + cnt) with (cob + 1) by lia;
           apply evtF_done; eexists; do 8 eexists; eexists;
           split; [unfold xms; reflexivity| exact INV'] ].
  Qed.

  Lemma if_w90 : forall (m : amem) (fo : Z -> Z) (x5 x10 x11 x14 x19 x24 x28 x29 : word) (cob rem dist ci hold bits : Z),
    WINV m fo -> 0 <= rem <= 258 -> 1 <= dist <= cob -> cob + rem <= osz ->
    evtF bsegs RNG (AT_LATCH ci (cob + rem) hold bits)
      (XST x5 (Z_to_bv 64 (OB + cob)) (Z_to_bv 64 (OB + cob)) x10 x11 x14 (Z_to_bv 64 rem) x19 x24 x28 x29 (Z_to_bv 64 dist) ci hold bits 0x98628 m).
  Proof using All.
    intros until bits. intros INV0 REM DIST COBR.
    open_fctx CX. unfold xms.
    clear ZSD WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHZ DJZ SHS DJS RZ RSZ RS RSS SHO DJO.
    zs. pc_dec_ub.
    zs. setreg 24 (Z_to_bv 64 (OB + (cob - dist))) ltac:(f_equal; lia).
    eapply (K8 if_wrest 0x98630 m fo _ _ _ _ _ _ _ _ _ (OB + (cob - dist)) cob rem ci hold bits); [right; left; reflexivity | exact INV0 | lia | right; lia | lia | lia].
  Qed.

  Lemma if_w1piece : forall (pc : Z) (m : amem) (fo : Z -> Z) (x5 x6 x7 x10 x11 x24 x29 : word) (len dist op ci co hold bits : Z),
    (pc = 0x984b4 /\ wnext = 0) \/ (pc = 0x9856c /\ op <= wnext) ->
    INV m fo -> 3 <= len <= 258 -> 1 <= dist <= 32768 -> op = dist - (co - bo) -> 1 <= op <= whave -> bo <= co -> co + 258 <= osz ->
    evtF bsegs RNG (AT_LATCH ci (co + len) hold bits) (WST x5 x6 x7 x10 x11 x24 x29 len dist op ci co hold bits pc m).
  Proof using All.
    intros until bits. intros PC INV0 LEN DIST EOP OP BCO CO258.
    pose proof (winv_of m fo INV0) as WINV0.
    open_fctx CX. open_finv INV0. unfold wst, gms, xms.
    assert (EW : wsz = 32768) by lia.
    destruct (WIN WNZ) as (_ & WD8 & WD0 & WDL & _).
    clear ZSD WSZ WNX WIN TOKL TOKD SANE FWR DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHZ DJZ SHS DJS RZ RSZ RS RSS SHO DJO.
    assert (REST : forall (pcb : Z) (fa : Z) (y5 y6 y7 y10 y11 y29 : word),
              (pcb = 0x984e4 \/ pcb = 0x98598) -> Wd <= fa -> fa + op <= Wd + 32768 ->
              evtF bsegs RNG (AT_LATCH ci (co + len) hold bits)
                (XST y5 y6 y7 y10 y11 (Z_to_bv 64 wnext) (Z_to_bv 64 len) (Z_to_bv 64 (OB + co)) (Z_to_bv 64 fa) (Z_to_bv 64 op) y29 (Z_to_bv 64 dist)
                     ci hold bits pcb m)).
    { intros pcb fa y5 y6 y7 y10 y11 y29 PCB FA1 FA2. unfold xms.
      destruct PCB as [-> | ->].
      all: zs; zbr K;
        [
          zs;
          eapply (K8 if_wrest 0x9861c m fo _ _ _ _ _ _ _ _ _ fa co len ci hold bits); [left; reflexivity | exact WINV0 | lia | left; lia | lia | lia]
        | zs; setreg 15 (Z_to_bv 64 (len - op)) ltac:(rewrite ?swrap32_small by lia; f_equal; lia);
          zs; zs;
          eapply evtF_cut;
          [ first [ eapply (if_w34loop (Z.to_nat op) m fo _ _ _ _ _ fa co op (len - op) dist ci hold bits 0x984f4 WINV0); first [lia | left; reflexivity]
                  | eapply (if_w34loop (Z.to_nat op) m fo _ _ _ _ _ fa co op (len - op) dist ci hold bits 0x985a8 WINV0); first [lia | right; reflexivity] ]
          | cbv beta; intros ms2 (m2 & z5 & z10 & z11 & z14 & z19 & z24 & z28 & z29 & fo2 & -> & INV2);
            replace (co + len) with (co + op + (len - op)) by lia;
            eapply (if_w90 m2 fo2 _ _ _ _ _ _ _ _ (co + op) (len - op) dist ci hold bits INV2); lia ] ]. }
    destruct PC as [[-> WN0] | [-> WNO]].
    -
      zs. zs. rewrite ?swrap32_small by lia. zs. zs. rewrite ?(Z.mod_small _ 4294967296) by lia.
      zs. zs.
      setreg 24 (Z_to_bv 64 (Wd + (wsz - op))) ltac:(f_equal; lia).
      zs. pc_dec_ub. zs. zsb. zsb. zs. zs.
      eapply (REST 0x984e4 (Wd + (wsz - op))); [left; reflexivity | lia | lia].
    -
      zs. rewrite ?swrap32_small by lia. zs. zs. rewrite ?(Z.mod_small _ 4294967296) by lia.
      zs. zs.
      setreg 24 (Z_to_bv 64 (Wd + (wnext - op))) ltac:(f_equal; lia).
      zs. pc_dec_ub. zs. zsb. zsb. zs. zs.
      eapply (REST 0x98598 (Wd + (wnext - op))); [right; reflexivity | lia | lia].
  Qed.
End P.
End CANSEC1.
