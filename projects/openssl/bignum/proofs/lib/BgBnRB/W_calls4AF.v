(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA UnwindA AsStruct W_smallA W_topA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitAF BnCallAF W_callsAF W_small3A W_calls3AF W_small4A.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import UbStructF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Section Calls.
  Variables (LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs) (lo SPv FB : Z) (s0w raw : word) (rasO : option (list Z)) (TOTAL : Z).
  Variables (Σ0 : rts RT) (ls0 : bstate bptr) (OW0 : list block) (m0 : mem).
  Notation CENV := (cenvA LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0).
  Hypothesis LOFBK : lo <= FB - BN_IS_ONE_STACK.

  Lemma is_one_callA : forall (POST : machine_state -> Prop) pre used Σ (ls : bstate bptr) (m : mem) (OW : list block) (r : bnref) (ar : Z)
      (ra gp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    CENV pre used Σ ls m OW -> lib_state ls m OW PL EA -> ref_at ls OW PL r ar -> r <> ROne ->
    (forall m' y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
        CENV pre used Σ ls m' OW -> lib_state ls m' OW PL EA ->
        evt bgbsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) y0 y1 y2 x8 x9 (Z_to_bv 64 (Z.b2z (is_one_pure (getbn r ls))))
                                y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom bgbsegs))) ->
    evt bgbsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_IS_ONE) fc None m (seg_rom bgbsegs)).
  Proof using LOFBK.
    intros until fc. intros ENV LS HA NRO K.
    assert (K0 : 0 <= BN_IS_ONE_STACK) by (unfold BN_IS_ONE_STACK; clear; lia).
    destruct (open_for_read _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BN_IS_ONE_STACK ENV LS HA NRO K0 LOFBK)
      as (D & BN & (OK1 & OK2 & OK3 & _) & U & ESP & ST & MI & SEP & SEPD & SHBC & ACC & AL & ACCD & ALD & BD & SLO & A0 & UBP).
    unfold BG_DMAX in OK3.
    eapply evt_cut.
    { eapply BN_is_one_specA with (lo := lo) (A := ar) (D := D) (b := getbn r ls);
        [exact BN | exact U | exact OK1 | exact OK2 | clear - OK3; lia | rewrite ESP; exact ST | rewrite ESP; exact LOFBK | exact MI
        | rewrite ESP; left; exact SEP | rewrite ESP; left; exact SEPD
        | exact SHBC | exact ACC | exact AL | exact ACCD | exact ALD | exact BD | exact SLO | exact A0 | exact UBP | reflexivity]. }
    intros ms' PO. unfold bn_small_postA in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & E & MUc & WMc & MIc & STc & RES).
    subst ms' y3. rewrite ESP in *.
    destruct (cenv_belowA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BN_IS_ONE_STACK ENV LS K0 LOFBK MUc WMc MIc STc) as (ENV' & LS').
    eapply K; [exact ENV' | exact LS'].
  Qed.

End Calls.

End WithRT.
