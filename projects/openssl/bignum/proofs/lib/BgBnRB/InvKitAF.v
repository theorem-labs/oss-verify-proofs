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
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitAF BnCallAF W_callsAF W_calls3AF AFrameKit AFrameEnv ExpKitAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation ops := (tree_ops bptr).
Local Notation ST := (bstate bptr).

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Section Kit.
  Variables (LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs) (lo SPv FB : Z) (s0w raw : word) (ras : list Z) (TOTAL : Z).
  Variables (Σ0 : rts RT) (ls0 : bstate bptr) (OW0 : list block) (m0 : mem).
  Notation CENV := (cenvA LB PL lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0).

  Lemma cenv_used_le : forall pre used used' Σ ls m OW, CENV pre used Σ ls m OW -> used <= used' -> CENV pre used' Σ ls m OW.
  Proof.
    intros pre used used' Σ ls m OW (OK & HEAP & ST & MI & AXP & CR & REST) H.
    unfold cenvA. split; [exact OK|]. split; [exact HEAP|]. split; [exact ST|]. split; [exact MI|]. split; [exact AXP|]. split; [clear - CR H; lia| exact REST].
  Qed.

  Lemma ESPs : forall pre used Σ ls m OW, CENV pre used Σ ls m OW -> bv_unsigned (Z_to_bv 64 SPv) = SPv /\ bv_unsigned (Z_to_bv 64 FB) = FB.
  Proof.
    intros pre used Σ ls m OW ((CEIL & LOFB & FBSP & SPT & _) & HEAP & _).
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _). unfold SEGTOP_A, USTACK_TOP in *.
    split; apply unsigned_lit; clear - C1 CEIL LOFB FBSP SPT; lia.
  Qed.

  Lemma kcallA : forall {A C : Type} (callee : BM (M := btree bptr) (ptr := bptr) A) (K : A -> BM (M := btree bptr) (ptr := bptr) C)
      (RES : A -> ST -> list block -> placement -> word -> Prop)
      (Q : C * ST -> rts RT -> machine_state -> Prop) (pre : list cell) (used cost used' KS : Z) (Σ : rts RT) (ls : ST) (m : mem) (OW : list block) (pc : word)
      (rax gp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    bv_unsigned x8 = SPv ->
    CENV pre used Σ ls m OW -> lib_state ls m OW PL EA -> lo <= FB - KS -> used + cost <= used' -> used' <= TOTAL ->
    (bn_preA Σ ls m OW LB PL EA (Z_to_bv 64 FB) lo KS cost ->
     uw_chain USTACK_TOP m (bv_unsigned (Z_to_bv 64 FB)) (bv_unsigned x8) (bv_unsigned raw :: ras) ->
     implA (callee ls) Σ
       (bn_postA rax (Z_to_bv 64 FB) gp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 Σ ls OW LB lo m PL EA cost RES)
       (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
           F pc fc None m (seg_rom bgbsegs))) ->
    (forall v ls' OW' PL' a0', RES v ls' OW' PL' a0' -> PL' = PL) ->
    (forall (v : A) Σ' ls' m' OW' (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word) F' fc',
       CENV pre used' Σ' ls' m' OW' -> lib_state ls' m' OW' PL EA -> refs_stable ls OW ls' OW' -> RES v ls' OW' PL y3 ->
       implA (K v ls') Σ' Q
         (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) y0 y1 y2 x8 x9 y3 y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
             F' (ret_pc rax) fc' None m' (seg_rom bgbsegs))) ->
    implA (bbind ops callee K ls) Σ Q
      (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F pc fc None m (seg_rom bgbsegs)).
  Proof.
    intros until fc. intros E8 ENV LS HK HU HT WALK HPL K1.
    pose proof ENV as (OK & HEAP & _).
    destruct (ESPs _ _ _ _ _ _ ENV) as (ES & EF).
    unfold bbind at 1. cbn [bind tree_ops].
    eapply implA_bind.
    { apply WALK.
      - eapply cenv_preA; [exact ENV | exact LS | exact HK | clear - HU HT; lia].
      - rewrite E8, EF. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV). }
    cbv beta. intros [v ls'] Σ' ms' PO.
    apply (bn_postA_cpost LB PL EA lo SPv FB TOTAL Σ0 ls0 OW0) in PO; [| exact OK | exact HEAP].
    cbn [fst snd] in *.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F' & fc' & m' & OW' & PL' & -> & CP & RES').
    pose proof (HPL _ _ _ _ _ RES') as EPL. subst PL'. specialize (CP eq_refl).
    destruct (cenv_postA LB PL EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 _ _ _ _ _ _ _ _ _ _ _ ENV CP) as (ENV' & LS').
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP) as RS'.
    eapply K1; [eapply cenv_used_le; [exact ENV' | exact HU] | exact LS' | exact RS' | exact RES'].
  Qed.

  Lemma kcallA_end : forall {A : Type} (callee : BM (M := btree bptr) (ptr := bptr) A)
      (RES : A -> ST -> list block -> placement -> word -> Prop)
      (Q : A * ST -> rts RT -> machine_state -> Prop) (pre : list cell) (used cost used' KS : Z) (Σ : rts RT) (ls : ST) (m : mem) (OW : list block) (pc : word)
      (rax gp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    bv_unsigned x8 = SPv ->
    CENV pre used Σ ls m OW -> lib_state ls m OW PL EA -> lo <= FB - KS -> used + cost <= used' -> used' <= TOTAL ->
    (bn_preA Σ ls m OW LB PL EA (Z_to_bv 64 FB) lo KS cost ->
     uw_chain USTACK_TOP m (bv_unsigned (Z_to_bv 64 FB)) (bv_unsigned x8) (bv_unsigned raw :: ras) ->
     implA (callee ls) Σ
       (bn_postA rax (Z_to_bv 64 FB) gp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 Σ ls OW LB lo m PL EA cost RES)
       (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
           F pc fc None m (seg_rom bgbsegs))) ->
    (forall v ls' OW' PL' a0', RES v ls' OW' PL' a0' -> PL' = PL) ->
    (forall (v : A) Σ' ls' m' OW' (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word) F' fc',
       CENV pre used' Σ' ls' m' OW' -> lib_state ls' m' OW' PL EA -> refs_stable ls OW ls' OW' -> RES v ls' OW' PL y3 ->
       evt bgbsegs (Q (v, ls') Σ')
         (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) y0 y1 y2 x8 x9 y3 y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
             F' (ret_pc rax) fc' None m' (seg_rom bgbsegs))) ->
    implA (callee ls) Σ Q
      (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F pc fc None m (seg_rom bgbsegs)).
  Proof.
    intros until fc. intros E8 ENV LS HK HU HT WALK HPL K1.
    pose proof ENV as (OK & HEAP & _).
    destruct (ESPs _ _ _ _ _ _ ENV) as (ES & EF).
    eapply implA_post_evt.
    { apply WALK.
      - eapply cenv_preA; [exact ENV | exact LS | exact HK | clear - HU HT; lia].
      - rewrite E8, EF. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV). }
    cbv beta. intros [v ls'] Σ' ms' PO.
    apply (bn_postA_cpost LB PL EA lo SPv FB TOTAL Σ0 ls0 OW0) in PO; [| exact OK | exact HEAP].
    cbn [fst snd] in *.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F' & fc' & m' & OW' & PL' & -> & CP & RES').
    pose proof (HPL _ _ _ _ _ RES') as EPL. subst PL'. specialize (CP eq_refl).
    destruct (cenv_postA LB PL EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 _ _ _ _ _ _ _ _ _ _ _ ENV CP) as (ENV' & LS').
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP) as RS'.
    eapply K1; [eapply cenv_used_le; [exact ENV' | exact HU] | exact LS' | exact RS' | exact RES'].
  Qed.

  Lemma cenv_frameA : forall pre pre' used Σ ls m m' OW,
    CENV pre used Σ ls m OW -> lib_state ls m OW PL EA ->
    munch [(FB, SPv)]%Z m m' -> wmono bgbsegs m m' -> stk bgbsegs m' lo FB -> mem_inv bgbsegs m' ->
    rw_cells bgbsegs m' FB (pre' ++ [C8 s0w; C8 raw]) -> Z.of_nat (cells_size pre') = SPv - FB - 16 ->
    CENV pre' used Σ ls m' OW /\ lib_state ls m' OW PL EA.
  Proof.
    intros pre pre' used Σ ls m m' OW ENV LS MU WM ST' MI' FR' FSZ'.
    pose proof ENV as (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW).
    pose proof OK as (CEIL & LOFB & FBSP & SPT & _ & _ & _ & _ & FROK & _).
    assert (WOK : Forall (w_ok OW LB ls PL EA SPv []) [(FB, SPv)]) by (constructor; [apply w_stack; cbn [fst snd]; clear - CEIL LOFB FBSP; lia| constructor]).
    assert (HWL : Forall (w_lib ls OW PL lo SPv) [(FB, SPv)]) by (constructor; [left; cbn [fst snd]; clear - LOFB FBSP; lia| constructor]).
    split.
    - eapply cenv_silentA; [exact ENV | exact LS | exact MU | exact WM | exact HWL | exact ST' | exact MI' | exact FR' | exact FSZ'].
    - exact (lib_state_frame Σ LB SPv USTACK_TOP [] ls m m' OW PL EA _ HEAP LS MU WM FROK WOK).
  Qed.

  Definition cenv_base (X : list (Z * Z)) (used : Z) (Σ : rts RT) (ls : ST) (m : mem) (OW : list block) : Prop :=
    ax_pres LB SPv X m0 m /\ rt_credit RT Σ0 - used <= rt_credit RT Σ /\ cnt_eq ls0 OW0 ls OW /\ refs_stable ls0 OW0 ls OW.

  Lemma cenv_rebaseX : forall pre pre' used Σ ls m m' OW,
    CENV pre used Σ ls m OW ->
    AHEAP Σ OW LB m' -> stk bgbsegs m' lo FB -> mem_inv bgbsegs m' ->
    rw_cells bgbsegs m' FB (pre' ++ [C8 s0w; C8 raw]) -> Z.of_nat (cells_size pre') = SPv - FB - 16 ->
    uw_chain USTACK_TOP m' SPv (bv_unsigned s0w) ras ->
    cenvA LB PL lo SPv FB s0w raw (Some ras) (TOTAL - used) Σ ls OW m' pre' 0 Σ ls m' OW.
  Proof.
    intros pre pre' used Σ ls m m' OW (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW) HEAP' ST' MI' FR' FSZ' UW'.
    pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0 & FROK & FAL & NOFR).
    unfold cenvA, cenv_ok.
    split. { split; [exact CEIL|]. split; [exact LOFB|]. split; [exact FBSP|]. split; [exact SPT|]. split; [exact SP16|]. split; [exact FB16|].
             split; [exact (cnt_ok_eq _ _ _ _ _ CNT0 CNT)|]. split; [clear - CR CRED0; lia|]. split; [exact FROK|]. split; [exact FAL | exact NOFR]. }
    split; [exact HEAP'|]. split; [exact ST'|]. split; [exact MI'|]. split; [apply ax_pres_refl|]. split; [clear; lia|].
    split; [apply cnt_eq_refl|]. split; [apply refs_stable_refl|]. split; [exact FR'|]. split; [exact FSZ'|]. exact UW'.
  Qed.

  Lemma implA_postT : forall {A} (t : btree bptr A) Σ (Q1 Q : A -> rts RT -> machine_state -> Prop) ms,
    implA t Σ Q1 ms -> (forall a Σ' ms', Q1 a Σ' ms' -> implA (TRet a) Σ' Q ms') -> implA t Σ Q ms.
  Proof.
    intros A t Σ Q1 Q ms H HK X Φ S T c Hc Hk.
    apply (H X Φ S T c Hc).
    intros c' (a & X' & Σ' & HΦ & Hc').
    destruct (ASTA_unpack RT Σ' PMc _ c' Hc') as (ms' & HQ1 & Hc'').
    exact (HK a Σ' ms' HQ1 X' Φ HΦ T c' Hc'' Hk).
  Qed.

  Lemma kcallA_last : forall {A : Type} (callee : BM (M := btree bptr) (ptr := bptr) A)
      (RES : A -> ST -> list block -> placement -> word -> Prop)
      (Q : A * ST -> rts RT -> machine_state -> Prop) (pre : list cell) (used cost used' KS : Z) (Σ : rts RT) (ls : ST) (m : mem) (OW : list block) (pc : word)
      (rax gp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    bv_unsigned x8 = SPv ->
    CENV pre used Σ ls m OW -> lib_state ls m OW PL EA -> lo <= FB - KS -> used + cost <= used' -> used' <= TOTAL ->
    (bn_preA Σ ls m OW LB PL EA (Z_to_bv 64 FB) lo KS cost ->
     uw_chain USTACK_TOP m (bv_unsigned (Z_to_bv 64 FB)) (bv_unsigned x8) (bv_unsigned raw :: ras) ->
     implA (callee ls) Σ
       (bn_postA rax (Z_to_bv 64 FB) gp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 Σ ls OW LB lo m PL EA cost RES)
       (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
           F pc fc None m (seg_rom bgbsegs))) ->
    (forall v ls' OW' PL' a0', RES v ls' OW' PL' a0' -> PL' = PL) ->
    (forall (v : A) Σ' ls' m' OW' (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word) F' fc',
       CENV pre used' Σ' ls' m' OW' -> lib_state ls' m' OW' PL EA -> refs_stable ls OW ls' OW' -> RES v ls' OW' PL y3 ->
       implA (TRet (v, ls')) Σ' Q
         (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) y0 y1 y2 x8 x9 y3 y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
             F' (ret_pc rax) fc' None m' (seg_rom bgbsegs))) ->
    implA (callee ls) Σ Q
      (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F pc fc None m (seg_rom bgbsegs)).
  Proof.
    intros until fc. intros E8 ENV LS HK HU HT WALK HPL K1.
    pose proof ENV as (OK & HEAP & _).
    destruct (ESPs _ _ _ _ _ _ ENV) as (ES & EF).
    eapply implA_postT.
    { apply WALK.
      - eapply cenv_preA; [exact ENV | exact LS | exact HK | clear - HU HT; lia].
      - rewrite E8, EF. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV). }
    cbv beta. intros [v ls'] Σ' ms' PO.
    apply (bn_postA_cpost LB PL EA lo SPv FB TOTAL Σ0 ls0 OW0) in PO; [| exact OK | exact HEAP].
    cbn [fst snd] in *.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F' & fc' & m' & OW' & PL' & -> & CP & RES').
    pose proof (HPL _ _ _ _ _ RES') as EPL. subst PL'. specialize (CP eq_refl).
    destruct (cenv_postA LB PL EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 _ _ _ _ _ _ _ _ _ _ _ ENV CP) as (ENV' & LS').
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP) as RS'.
    eapply K1; [eapply cenv_used_le; [exact ENV' | exact HU] | exact LS' | exact RS' | exact RES'].
  Qed.

  Section Small.
  Hypothesis LOFB16 : lo <= FB - 16.

  Lemma zero_callA : forall (POST : machine_state -> Prop) pre used Σ (ls : bstate bptr) (m : mem) (OW : list block) (r : bnref) (ar : Z)
      (ra gp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    CENV pre used Σ ls m OW -> lib_state ls m OW PL EA -> ref_at ls OW PL r ar -> wref PL r ->
    (forall m' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
        let ls' := setbn r (bn_zero_pure (getbn r ls)) ls in
        CENV pre used Σ ls' m' OW -> lib_state ls' m' OW PL EA ->
        evt bgbsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) y0 y1 y2 x8 x9 y3 y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom bgbsegs))) ->
    evt bgbsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_ZERO_EX) fc None m (seg_rom bgbsegs)).
  Proof using LOFB16.
    intros until fc. intros ENV LS HA WR K.
    pose proof (proj1 WR : not_one r) as NRO.
    destruct (open_for_call LB PL EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 LOFB16 _ _ _ _ _ _ _ _ ENV LS HA NRO)
      as (D0 & _ & _ & ESP & ST & MI & SEP & SHBC & ACC & AL & SLO & OFR & A0).
    pose proof ENV as (OK & HEAP & _ & _ & AXP & CR & CNT & RS & FR & FSZ & UW). pose proof OK as (CEIL & LOFB & FBSP & SPT & _ & _ & _ & _ & FROK & _ & NOFR).
    pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
    destruct (lib_state_open [] ls m OW PL EA r ar LS ND HA ltac:(intros []) NRO) as ((D & BN & ARR) & (OK1 & OK2 & OK3 & OK4) & LSH).
    set (b := getbn r ls) in *.
    destruct (bn_arr_facts_w ls OW PL EA SPv USTACK_TOP Σ LB m r D HEAP PARTS FROK HV WR ARR) as (U & _ & DD0 & DC & DI & SEPd). fold b in U, DC, DI, SEPd.
    pose proof (SEPd r ar HA) as SEPr. clear SEPd.
    unfold BG_DMAX in OK3.
    eapply evt_cut.
    { eapply BN_zero_ex_specA with (lo := lo) (A := ar) (D := D) (b := b);
        [exact BN | rewrite ESP; exact ST | rewrite ESP; exact LOFB16 | exact MI | rewrite ESP; left; exact SEP
        | exact SHBC | exact ACC | exact AL | exact SLO | exact OFR | reflexivity | exact A0]. }
    intros ms' PO. unfold bn_small_postA in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & E & MUc & WMc & MIc & STc & RES).
    subst ms'. rewrite ESP in *.
    set (b' := bn_zero_pure b) in *.
    assert (U' : u64arr bgbsegs m' D (wlimbs (bn_buf b))).
    { eapply u64arr_transport; [exact U | exact MUc | exact WMc |]. cbn [disjoint_from]. rewrite wlimbs_len. fold (bn_dmax b).
      split; [left; unfold BnHeapA.ACEIL in *; clear - DC CEIL LOFB16; lia|]. split; [clear - SEPr; lia| exact I]. }
    eapply (rw_cells_transport bgbsegs _ m m') in FR; [| exact MUc | exact WMc | cbn [disjoint_from]; split; [right; clear; lia|]; split; [right; clear - SEP; lia| exact I]].
    assert (WOK : Forall (w_ok OW LB ls PL EA SPv [r]) [(FB - 16, FB); (ar, ar + 24)]).
    { constructor; [apply w_stack; cbn [fst snd]; clear - CEIL LOFB FBSP LOFB16; lia|].
      constructor; [eapply (w_struct OW LB ls PL EA SPv false [r] _ r ar); [left; reflexivity| exact HA| exact NRO| cbn; clear; lia| cbn; clear; lia]| constructor]. }
    assert (HWL : Forall (w_lib ls OW PL lo SPv) [(FB - 16, FB); (ar, ar + 24)]).
    { constructor; [left; cbn [fst snd]; clear - LOFB FBSP LOFB16; lia|].
      constructor; [w_lib_ref HA NRO| constructor]. }
    assert (LS' : lib_state (setbn r b' ls) m' OW PL EA).
    { unfold lib_state. eapply (lib_state_close [] ls m' OW PL EA r ar); [| exact ND | exact HA | exact NRO | | |].
      - exact (lib_state_frame Σ LB SPv USTACK_TOP [r] ls m m' OW PL EA _ HEAP LSH MUc WMc FROK WOK).
      - exists D. split; [exact RES|].
        assert (ARR' : bn_arr m' OW (pl_of PL r) D b) by (eapply bn_arr_of_u64arr; [exact ARR| exact U']).
        unfold bn_arr in ARR' |- *. unfold b', bn_zero_pure, bn_dmax in *. cbn [bn_d bn_buf]. exact ARR'.
      - unfold bg_ok, b', bn_zero_pure, bn_dmax, BG_DMAX in *. cbn [bn_buf bn_top bn_flags].
        split; [exact OK1|]. split; [clear; lia|]. split; [exact OK3| exact OK4].
      - apply ids_ok_setbn_same; [exact (proj1 (proj2 (proj2 PARTS))) | exact HV | reflexivity]. }
    eapply K; [| exact LS'].
    apply cenv_setbnA; [| exact HV | reflexivity].
    eapply cenv_silentA; [exact ENV | exact LS | exact MUc | exact WMc | exact HWL | exact STc | exact MIc | exact FR | exact FSZ].
  Qed.

  Lemma cenv_struct_openA : forall pre used Σ ls m OW r a,
    CENV pre used Σ ls m OW -> lib_state ls m OW PL EA -> ref_at ls OW PL r a -> wref PL r ->
    exists D, rw_cells bgbsegs m a (BnRepDefs.bn_cells D (getbn r ls)) /\ bg_ok (getbn r ls)
      /\ acc bgbsegs m a 24 /\ a mod 8 = 0 /\ 0 < a /\ a + 24 <= FB - 16 /\ (a + 24 <= SHLO \/ SHHI <= a)
      /\ stk bgbsegs m lo FB /\ mem_inv bgbsegs m
      /\ forall m' b',
           munch [(a, a + 24)] m m' -> wmono bgbsegs m m' -> rw_cells bgbsegs m' a (BnRepDefs.bn_cells D b') ->
           bn_d b' = bn_d (getbn r ls) -> bn_buf b' = bn_buf (getbn r ls) -> bg_ok b' ->
           stk bgbsegs m' lo FB -> mem_inv bgbsegs m' ->
           CENV pre used Σ (setbn r b' ls) m' OW /\ lib_state (setbn r b' ls) m' OW PL EA.
  Proof using LOFB16.
    intros pre used Σ ls m OW r a ENV LS HA WR.
    pose proof (proj1 WR : not_one r) as NRO.
    destruct (open_for_call LB PL EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 LOFB16 _ _ _ _ _ _ _ _ ENV LS HA NRO)
      as (D0 & _ & _ & ESP & ST & MI & SEP & SHBC & ACC & AL & SLO & OFR & A0).
    pose proof ENV as (OK & HEAP & _ & _ & AXP & CR & CNT & RS & FR & FSZ & UW). pose proof OK as (CEIL & LOFB & FBSP & SPT & _ & _ & _ & _ & FROK & _ & NOFR).
    pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
    destruct (lib_state_open [] ls m OW PL EA r a LS ND HA ltac:(intros []) NRO) as ((D & BN & ARR) & OKB & LSH).
    set (b := getbn r ls) in *.
    destruct (bn_arr_facts_w ls OW PL EA SPv USTACK_TOP Σ LB m r D HEAP PARTS FROK HV WR ARR) as (U & _ & DD0 & DC & DI & SEPd). fold b in U, DC, DI, SEPd.
    pose proof (SEPd r a HA) as SEPr. clear SEPd.
    exists D. split; [exact BN|]. split; [exact OKB|]. split; [exact ACC|]. split; [exact AL|]. split; [exact A0|]. split; [exact SEP|]. split; [exact OFR|].
    split; [exact ST|]. split; [exact MI|].
    intros m' b' MUc WMc RES ED EB OKB' STc MIc.
    assert (U' : u64arr bgbsegs m' D (wlimbs (bn_buf b))).
    { eapply u64arr_transport; [exact U | exact MUc | exact WMc |]. cbn [disjoint_from]. rewrite wlimbs_len. fold (bn_dmax b).
      split; [clear - SEPr; lia| exact I]. }
    eapply (rw_cells_transport bgbsegs _ m m') in FR; [| exact MUc | exact WMc | cbn [disjoint_from]; split; [right; clear - SEP LOFB16; lia| exact I]].
    assert (WOK : Forall (w_ok OW LB ls PL EA SPv [r]) [(a, a + 24)]).
    { constructor; [eapply (w_struct OW LB ls PL EA SPv false [r] _ r a); [left; reflexivity| exact HA| exact NRO| cbn; clear; lia| cbn; clear; lia]| constructor]. }
    assert (HWL : Forall (w_lib ls OW PL lo SPv) [(a, a + 24)]).
    { constructor; [w_lib_ref HA NRO| constructor]. }
    assert (LS' : lib_state (setbn r b' ls) m' OW PL EA).
    { unfold lib_state. eapply (lib_state_close [] ls m' OW PL EA r a); [| exact ND | exact HA | exact NRO | | |].
      - exact (lib_state_frame Σ LB SPv USTACK_TOP [r] ls m m' OW PL EA _ HEAP LSH MUc WMc FROK WOK).
      - exists D. split; [exact RES|].
        assert (ARR' : bn_arr m' OW (pl_of PL r) D b) by (eapply bn_arr_of_u64arr; [exact ARR| exact U']).
        unfold bn_arr in ARR' |- *. unfold bn_dmax in *. rewrite ED, EB. exact ARR'.
      - exact OKB'.
      - apply ids_ok_setbn_same; [exact (proj1 (proj2 (proj2 PARTS))) | exact HV | unfold bn_blocks, bn_dmax; fold b; rewrite ED, EB; reflexivity]. }
    split; [| exact LS'].
    apply cenv_setbnA; [| exact HV | unfold bn_blocks, bn_dmax; fold b; rewrite ED, EB; reflexivity].
    eapply cenv_silentA; [exact ENV | exact LS | exact MUc | exact WMc | exact HWL | exact STc | exact MIc | exact FR | exact FSZ].
  Qed.
  End Small.

End Kit.
End WithRT.
