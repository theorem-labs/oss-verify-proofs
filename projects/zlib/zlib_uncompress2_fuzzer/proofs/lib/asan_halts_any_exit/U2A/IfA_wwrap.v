(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState Inftrees InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AArr U2AKit U2AObj ItAKit IfAPure IfA_base IfAKit IfAStore IfA_lit IfA_direct
  IfA_win IfA_wcopy IfA_wcopy2 IfA_wloop IfA_wcase.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_base | solve_load_sh0 | solve_load_f8 | solve_load_image ].
Local Ltac acc_hint ::= first [ acc_hint_sh | acc_hint_var ].

Section CANSEC1. Context {rc : runConstT}.
Section P.
  Variables (RNG : footprint) (FR : bvmap 5 word) (fc : bv 32) (gp tp : word).
  Variables (SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo : Z) (rdL rdD fw : Z -> Z) (payload : list Z) (m1 : amem).
  Variables (sd : sdc) (id : idc) (ni ai no ao msg mode hw bw : word).
  Hypothesis CX : if_ctx RNG SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1.
  Hypothesis WNZ : wsz <> 0.
  Notation GST := (gms SP Zs S D n OB osz lb la da gp tp FR fc).
  Notation WINV := (winv SP Zs S OB osz Wd wsz whave wnext lb db la da bo fw m1 sd id ni ai no ao msg mode hw bw).
  Notation AT_LATCH := (at_latch FR fc gp tp SP Zs S D n OB osz Wd wsz whave wnext lb db la da bo m1 sd id ni ai no ao msg mode hw bw).
  Notation WST := (wst FR fc gp tp SP Zs S D n OB osz lb la da).
  Notation DINV m v0 fo := (if_inv SP Zs S OB osz bo wsz whave wnext Wd la da lb db m1 m v0 (Z_to_bv 64 (Z.shiftr Zs 3 + 2147450880))
                              (Z_to_bv 64 (Z.shiftr (Zs + 32) 3 + 2147450880)) (Z_to_bv 64 (Zs + 24)) sd id ni ai no ao msg mode hw bw fo).
  Notation WINV_OF := (winv_of RNG SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1 sd id ni ai no ao msg mode hw bw CX WNZ).

  Notation SH8 := (Z_to_bv 64 (Z.shiftr (Zs + 8) 3 + 2147450880)).
  Definition w1 (x10 x13 x21 : word) (fa len dist opw cnt ci co hold bits pc : Z) (m : amem) : machine_state :=
    GST (Z_to_bv 64 (Zs + 8)) (Z_to_bv 64 fa) (Z_to_bv 64 fa) (Z_to_bv 64 len) x10 (Z_to_bv 64 (OB + co + 1)) x13 (Z_to_bv 64 opw) (Z_to_bv 64 cnt)
        (Z_to_bv 64 dist) x21 (Z_to_bv 64 (Zs + 32)) (Z_to_bv 64 (OB + co)) SH8 ci co hold bits pc m.
  Definition w1_post (v0 : word) (fa len dist opw cnt ci co hold bits : Z) : machine_state -> Prop :=
    fun ms' => exists (m' : amem) (x21 : word) (fo' : Z -> Z),
      ms' = w1 (Z_to_bv 64 (OB + (co + cnt))) (Z_to_bv 64 (OB + (co + cnt))) x21 (fa + cnt) len dist opw 0 ci (co + cnt) hold bits 0x97580 m' /\ WINV m' v0 fo'.

  Lemma if_w1loop : forall (N : nat) (m : amem) (v0 : word) (fo : Z -> Z) (x10 x13 x21 : word) (fa len dist opw cnt ci co hold bits : Z),
    WINV m v0 fo -> (Z.to_nat cnt <= N)%nat ->
    1 <= cnt -> cnt <= 32768 -> Wd <= fa -> fa + cnt <= Wd + 32768 -> 0 <= co -> co + cnt <= osz ->
    evtF asegs RNG (w1_post v0 fa len dist opw cnt ci co hold bits) (w1 x10 x13 x21 fa len dist opw cnt ci co hold bits 0x97094 m).
  Proof using All.
    induction N as [|N IH]; intros until bits; intros [INV0 WINC] HN CNT CNT2 FA1 FA2 CO0 COC; [lia|].
    open_fctx CX. open_finv INV0. unfold w1, gms.
    destruct (WIN WNZ) as (_ & WD8 & WD0 & WDL & RWD & RSWD & DJW & SHW & DJSW). unfold ifW in DJW, DJSW.
    assert (DWO : Wd + 32768 <= OB \/ OB + osz <= Wd) by (cbn [disjoint_from] in DJW; lia).
    pose proof FWR as FWR0.
    clear ZSD WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD DJW
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHZ DJZ SHS DJS RZ RSZ RS RSS.
    assert (E32 : Z.of_nat 32768 = 32768) by reflexivity.
    remember (OB + co) as C0 eqn:EC0.
    zrunb [0x970c4]. cbv beta. byte_in b0 RB0 FWR0 FOR.
    out_store OUT FOR co C0 b0 OUT1 FOR1.
    pose proof (fupd8_range fo co b0 osz FOR RB0) as FOR1.
    do 5 zs. rewrite ?swrap32_small by lia. subst C0.
    setreg 17 (Z_to_bv 64 (OB + (co + 1))) ltac:(f_equal; lia).
    setreg 11 (Z_to_bv 64 (OB + (co + 1) + 1)) ltac:(f_equal; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (INV' : WINV mx v0 (fupd8 fo co b0)) by (split; [close_finv| eassumption]) end.
    zs. zbr0 K.
    - eapply evtF_mono.
      + eapply (IH _ v0 _ _ _ _ (fa + 1) len dist opw (cnt + -1) ci (co + 1) hold bits INV'); lia.
      + intros ms' HP. unfold w1_post in *.
        replace (fa + 1 + (cnt + -1)) with (fa + cnt) in HP by lia. replace (co + 1 + (cnt + -1)) with (co + cnt) in HP by lia. exact HP.
    - zs. replace (cnt + -1) with 0 by lia.
      apply evtF_done. eexists. eexists. eexists.
      split; [unfold w1, gms; replace (fa + cnt) with (fa + 1) by lia; replace (co + cnt) with (co + 1) by lia; reflexivity| exact INV'].
  Qed.

  Definition w2 (x6 x7 x11 x21 x29 : word) (fa len dist cnt ci co hold bits pc : Z) (m : amem) : machine_state :=
    GST (Z_to_bv 64 (Zs + 8)) x6 x7 (Z_to_bv 64 len) (Z_to_bv 64 (OB + co)) x11 (Z_to_bv 64 (OB + co)) (Z_to_bv 64 cnt) (Z_to_bv 64 (OB + (fa - OB)))
        (Z_to_bv 64 dist) x21 (Z_to_bv 64 (Zs + 32)) x29 SH8 ci (fa - OB) hold bits pc m.
  Definition w2_post (v0 : word) (fa len dist cnt ci co hold bits : Z) : machine_state -> Prop :=
    fun ms' => exists (m' : amem) (x6 x11 x21 x29 : word) (fo' : Z -> Z),
      ms' = w2 x6 (Z_to_bv 64 (OB + (co + cnt))) x11 x21 x29 (fa + cnt) len dist 0 ci (co + cnt) hold bits 0x9760c m' /\ WINV m' v0 fo'.

  Lemma if_w2loop : forall (N : nat) (m : amem) (v0 : word) (fo : Z -> Z) (x6 x7 x11 x21 x29 : word) (fa len dist cnt ci co hold bits : Z),
    WINV m v0 fo -> (Z.to_nat cnt <= N)%nat ->
    1 <= cnt -> cnt <= 32768 -> Wd <= fa -> fa + cnt <= Wd + 32768 -> 0 <= co -> co + cnt <= osz ->
    evtF asegs RNG (w2_post v0 fa len dist cnt ci co hold bits) (w2 x6 x7 x11 x21 x29 fa len dist cnt ci co hold bits 0x97594 m).
  Proof using All.
    induction N as [|N IH]; intros until bits; intros [INV0 WINC] HN CNT CNT2 FA1 FA2 CO0 COC; [lia|].
    open_fctx CX. open_finv INV0. unfold w2, gms.
    destruct (WIN WNZ) as (_ & WD8 & WD0 & WDL & RWD & RSWD & DJW & SHW & DJSW). unfold ifW in DJW, DJSW.
    assert (DWO : Wd + 32768 <= OB \/ OB + osz <= Wd) by (cbn [disjoint_from] in DJW; lia).
    pose proof FWR as FWR0.
    clear ZSD WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD DJW
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHZ DJZ SHS DJS RZ RSZ RS RSS.
    assert (E32 : Z.of_nat 32768 = 32768) by reflexivity.
    remember (OB + co) as C0 eqn:EC0.
    zrunb [0x975c0]. cbv beta. byte_in b0 RB0 FWR0 FOR.
    out_store OUT FOR co C0 b0 OUT1 FOR1.
    pose proof (fupd8_range fo co b0 osz FOR RB0) as FOR1.
    do 4 zs. rewrite ?swrap32_small by lia. subst C0.
    setreg 10 (Z_to_bv 64 (OB + (co + 1))) ltac:(f_equal; lia).
    setreg 17 (Z_to_bv 64 (OB + (fa + 1 - OB))) ltac:(f_equal; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (INV' : WINV mx v0 (fupd8 fo co b0)) by (split; [close_finv| eassumption]) end.
    zs. zbr0 K.
    - eapply evtF_mono.
      + eapply (IH _ v0 _ _ _ _ _ _ (fa + 1) len dist (cnt + -1) ci (co + 1) hold bits INV'); lia.
      + intros ms' HP. unfold w2_post in *.
        replace (fa + 1 + (cnt + -1)) with (fa + cnt) in HP by lia. replace (co + 1 + (cnt + -1)) with (co + cnt) in HP by lia. exact HP.
    - zs. replace (cnt + -1) with 0 by lia.
      apply evtF_done. eexists. do 4 eexists. eexists.
      split; [unfold w2, gms; replace (fa + cnt) with (fa + 1) by lia; replace (co + cnt) with (co + 1) by lia; reflexivity| exact INV'].
  Qed.

  Notation KIT9C := (if_w9c RNG FR fc gp tp SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1 sd id ni ai no ao msg mode hw bw CX WNZ).
  Notation KIT10 := (if_w10 RNG FR fc gp tp SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1 sd id ni ai no ao msg mode hw bw CX WNZ).
  Notation KIT00 := (if_w00 RNG FR fc gp tp SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1 sd id ni ai no ao msg mode hw bw CX WNZ).

  Lemma if_ww : forall (m : amem) (v0 : word) (fo : Z -> Z) (x6 x10 x15 x16 x21 : word) (len dist op ci co hold bits : Z),
    DINV m v0 fo -> 3 <= len <= 258 -> 1 <= dist -> op = dist - (co - bo) -> 1 <= op <= whave -> 0 < wnext < op -> bo <= co -> co + 258 <= osz ->
    evtF asegs RNG (AT_LATCH ci (co + len) hold bits)
      (WST (Z_to_bv 64 (Zs + 8)) x6 x10 (Z_to_bv 64 wnext) x15 x16 x21 len dist op ci co hold bits 0x97064 m).
  Proof using All.
    intros until bits. intros INV0 LEN DIST EOP OP WNO BCO CO258.
    pose proof (WINV_OF m v0 fo INV0) as WINV0.
    open_fctx CX. open_finv INV0. unfold wst, gms.
    assert (EW : wsz = 32768) by lia.
    clear ZSD WSZ WNX WIN TOKL TOKD SANE FWR DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHZ DJZ SHS DJS RZ RSZ RS RSS SHO DJO.
    zs. zs. rewrite swrap32_small by lia. zs. zs. rewrite (Z.mod_small _ 4294967296) by lia.
    zs. rewrite swrap32_small by lia. zs. zs.
    zs. zbr0 K.
    -
      eapply (KIT00 m v0 fo _ _ _ _ _ _ _ _ (Wd + (wnext + wsz - op)) len dist ci co hold bits WINV0); lia.
    - zrunb [0x97094].
      eapply evtF_cut.
      { eapply (if_w1loop (Z.to_nat (op - wnext)) m v0 fo _ _ _ (Wd + (wnext + wsz - op)) len dist (op - wnext) (op - wnext) ci co hold bits WINV0); lia. }
      cbv beta. intros ms2 (m2 & y21 & fo2 & -> & INV2).
      clear MI MU WM FRM STRM SSC OUT FOR.
      pose proof INV2 as [INV2' WINC2]. open_finv INV2'. unfold w1, gms.
      remember (co + (op - wnext)) as co2 eqn:ECO2.
      zs. rewrite swrap32_small by lia. zs. zs. zbr0 K2.
      +
        zs. zs. zs. zs. zs. replace (co + len) with (co2 + (len - (op - wnext))) by lia. zbr0 K3.
        * eapply evtF_eq; [| eapply (KIT10 m2 v0 fo2 _ _ _ _ _ _ _ Wd co2 (len - (op - wnext)) ci co2 hold bits INV2); try lia; left; lia].
          unfold cst, gms. reflexivity.
        * zs. eapply evtF_eq; [| eapply (KIT9C m2 v0 fo2 _ _ _ _ _ _ _ Wd co2 (len - (op - wnext)) ci co2 hold bits INV2); try lia; left; lia].
          unfold cst, gms. reflexivity.
      +
        zs. zs.
        setreg 17 (Z_to_bv 64 (OB + (Wd - OB))) ltac:(f_equal; lia).
        eapply evtF_cut.
        { eapply evtF_eq; [| eapply (if_w2loop (Z.to_nat wnext) m2 v0 fo2 _ _ _ _ _ Wd (len - (op - wnext)) dist wnext ci co2 hold bits INV2); lia].
          unfold w2, gms. reflexivity. }
        cbv beta. intros ms3 (m3 & z6 & z11 & z21 & z29 & fo3 & -> & INV3).
        clear MI MU WM FRM STRM SSC OUT FOR.
        pose proof INV3 as [INV3' WINC3]. open_finv INV3'. unfold w2, gms.
        remember (co2 + wnext) as co3 eqn:ECO3.
        zs. zs. rewrite swrap32_small by lia. zs.
        setreg 6 (Z_to_bv 64 (OB + (co3 - dist))) ltac:(f_equal; lia).
        zs. zs. zs. zbr0 K3.
        * replace (co + len) with (co3 + (len - (op - wnext) - wnext)) by lia.
          eapply evtF_eq; [| eapply (KIT9C m3 v0 fo3 _ _ _ _ _ _ _ (OB + (co3 - dist)) co3 (len - (op - wnext) - wnext) ci _ hold bits INV3); try lia; right; lia].
          unfold cst, gms. reflexivity.
        * zs. replace (co + len) with (co3 + (len - (op - wnext) - wnext)) by lia.
          eapply evtF_eq; [| eapply (KIT10 m3 v0 fo3 _ _ _ _ _ _ _ (OB + (co3 - dist)) co3 (len - (op - wnext) - wnext) ci _ hold bits INV3); try lia; right; lia].
          unfold cst, gms. reflexivity.
  Qed.
End P.
End CANSEC1.
