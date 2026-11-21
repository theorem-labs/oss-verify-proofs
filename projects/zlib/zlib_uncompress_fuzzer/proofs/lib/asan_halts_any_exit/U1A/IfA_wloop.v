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
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U1A Require Import U2AObj IfA_base IfAKit IfA_lit IfA_direct IfA_wcopy.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
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

  Definition w34 (x7 x10 x16 x21 : word) (fa len dist op cnt ci co hold bits pc : Z) (m : amem) : machine_state :=
    GST (Z_to_bv 64 (Zs + 8)) (Z_to_bv 64 fa) x7 (Z_to_bv 64 len) x10 (Z_to_bv 64 fa) (Z_to_bv 64 op) (Z_to_bv 64 cnt) x16
        (Z_to_bv 64 dist) x21 (Z_to_bv 64 (Zs + 32)) (Z_to_bv 64 (OB + co)) (Z_to_bv 64 (Z.shiftr (Zs + 8) 3 + 2147450880))
        ci co hold bits pc m.

  Definition w34_post (v0 : word) (fa len dist op cnt ci co hold bits : Z) : machine_state -> Prop :=
    fun ms' => exists (m' : amem) (x10 x16 x21 : word) (fo' : Z -> Z),
      ms' = w34 (Z_to_bv 64 (OB + (co + cnt))) x10 x16 x21 (fa + cnt) len dist op 0 ci (co + cnt) hold bits 0x971cc m' /\ WINV m' v0 fo'.

  Lemma if_w34loop : forall (N : nat) (m : amem) (v0 : word) (fo : Z -> Z) (x7 x10 x16 x21 : word) (fa len dist op cnt ci co hold bits pc : Z),
    WINV m v0 fo -> (Z.to_nat cnt <= N)%nat ->
    1 <= cnt -> cnt <= 32768 -> Wd <= fa -> fa + cnt <= Wd + 32768 -> 0 <= co -> co + cnt <= osz ->
    pc = 0x9704c \/ pc = 0x970e4 ->
    evtF asegs RNG (w34_post v0 fa len dist op cnt ci co hold bits) (w34 x7 x10 x16 x21 fa len dist op cnt ci co hold bits pc m).
  Proof using All.
    induction N as [|N IH]; intros until pc; intros [INV0 WINC] HN CNT CNT2 FA1 FA2 CO0 COC PC; [lia|].
    open_fctx CX. open_finv INV0. unfold w34, gms.
    destruct (WIN WNZ) as (_ & WD8 & WD0 & WDL & RWD & RSWD & DJW & SHW & DJSW). unfold ifW in DJW, DJSW.
    assert (DWO : Wd + 32768 <= OB \/ OB + osz <= Wd) by (cbn [disjoint_from] in DJW; lia).
    pose proof FWR as FWR0.
    clear ZSD WSZ WNX WIN TOKL TOKD SANE FWR WH WN DB LB D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD DJW
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHZ DJZ SHS DJS RZ RSZ RS RSS.
    assert (E32 : Z.of_nat 32768 = 32768) by reflexivity.
    remember (OB + co) as C0 eqn:EC0.
    destruct PC as [-> | ->].
    all: first [zrunb [0x97078] | zrunb [0x97110]]; cbv beta; byte_in b0 RB0 FWR0 FOR;
         out_store OUT FOR co C0 b0 OUT1 FOR1;
         pose proof (fupd8_range fo co b0 osz FOR RB0) as FOR1;
         do 4 zs; rewrite ?swrap32_small by lia; subst C0;
         setreg 17 (Z_to_bv 64 (OB + (co + 1))) ltac:(f_equal; lia);
         (lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
            assert (INV' : WINV mx v0 (fupd8 fo co b0)) by (split; [close_finv| eassumption]) end);
         zs; zbr K;
         [ eapply evtF_mono;
           [ eapply (IH _ v0 _ _ _ _ _ (fa + 1) len dist op (cnt + -1) ci (co + 1) hold bits _ INV'); first [lia | left; reflexivity | right; reflexivity]
           | intros ms' HP; unfold w34_post in *;
             replace (fa + 1 + (cnt + -1)) with (fa + cnt) in HP by lia; replace (co + 1 + (cnt + -1)) with (co + cnt) in HP by lia; exact HP ]
         | zs; replace (cnt + -1) with 0 by lia;
           apply evtF_done; eexists; do 3 eexists; eexists;
           split; [unfold w34, gms; replace (fa + cnt) with (fa + 1) by lia; replace (co + cnt) with (co + 1) by lia; reflexivity| exact INV'] ].
  Qed.
End P.
End CANSEC1.
