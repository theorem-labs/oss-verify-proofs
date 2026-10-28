(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnModel BnTree BnInv BnBridge BgState BgInv BgLib BgWords BgArith.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnArith BnMem BnTac BnTacX.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_small W_small2.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU2 Require Import W_small3.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep BnLeaves.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnEU Require Import ExpKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Local Notation ops := (tree_ops bptr).
Local Notation ST := (bstate bptr).

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma bn_pre_le : forall s bs m OW LB PL EA sp lo B errv K K',
  bn_pre s bs m OW LB PL EA sp lo B errv K' -> K <= K' -> bn_pre s bs m OW LB PL EA sp lo B errv K.
Proof.
  intros s bs m OW LB PL EA sp lo B errv K K' (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12) H.
  unfold bn_pre. repeat (split; [assumption|]). split; [lia|]. split; assumption.
Qed.

Section Kit.
  Variables (LB : list block) (PL : placement) (EA : BnRep.err_addrs) (lo B SPv FB : Z).
  Variables (s0 : PState) (bs0 : bstate bptr) (OW0 : list block) (m0 : mem).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis LOFB : lo <= FB.
  Hypothesis FBSP : FB <= SPv.
  Hypothesis SPB : SPv <= B.
  Hypothesis B63 : B < 2^63.
  Hypothesis SPR : SPv < 2^64.
  Hypothesis FROK : frames_ok PL SPv B.
  Variable CS : Z.
  Hypothesis CS128 : 128 <= CS.
  Hypothesis LOF : lo <= FB - CS.

  Local Notation KENV := (kenv LB PL lo B SPv FB s0 bs0 OW0 m0).

  Lemma kcall : forall {A C : Type} (callee : BM (M := btree bptr) A) (K : A -> BM (M := btree bptr) C)
      (RES : A -> ST -> list block -> placement -> word -> Prop)
      (Q : C * ST -> PState -> machine_state -> Prop) (fr : list cell) (st : PState) (bs : ST) (m : mem) (OW : list block) (pc : word)
      (rax gp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    KENV fr st bs m OW -> lib_state bs m OW PL EA ->
    (forall errv, bn_pre st bs m OW LB PL EA (Z_to_bv 64 FB) lo B errv CS ->
       implM bgusegs (interp (embed (callee bs))) st
         (bn_post rax (Z_to_bv 64 FB) gp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc st bs OW LB lo B m PL EA RES)
         (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
             F pc fc None m (seg_rom bgusegs))) ->
    (forall v bs' OW' PL' a0', RES v bs' OW' PL' a0' -> PL' = PL) ->
    (forall (v : A) st' bs' m' OW' (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word),
       KENV fr st' bs' m' OW' -> lib_state bs' m' OW' PL EA -> refs_stable bs OW bs' OW' -> RES v bs' OW' PL y3 ->
       implM bgusegs (interp (embed (K v bs'))) st' Q
         (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) y0 y1 y2 x8 x9 y3 y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
             F (ret_pc rax) fc None m' (seg_rom bgusegs))) ->
    implM bgusegs (interp (embed (bbind ops callee K bs))) st Q
      (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F pc fc None m (seg_rom bgusegs)).
  Proof using CEIL GLO LOFB FBSP SPB B63 SPR FROK LOF.
    intros until fc. intros ENV LS WALK HPL K1.
    destruct (kenv_pre LB PL EA lo B SPv FB s0 bs0 OW0 m0 CEIL GLO LOFB FBSP SPB B63 SPR FROK _ _ _ _ _ CS ENV LS LOF) as (errv1 & PRE1).
    unfold bbind at 1. cbn [bind tree_ops].
    eapply implM_embed_bind; [exact (WALK errv1 PRE1)|].
    cbv beta. intros [v bs'] st' ms' PO.
    apply (bn_post_kpost LB PL EA lo B SPv FB CEIL LOFB FBSP SPR) in PO; [|exact HPL].
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & OW' & -> & KP & RES').
    destruct (kenv_post LB PL EA lo B SPv FB s0 bs0 OW0 m0 CEIL GLO LOFB FBSP FROK _ _ _ _ _ _ _ _ _ ENV KP) as (ENV' & LS').
    pose proof (kpost_refs LB PL EA lo B FB _ _ _ _ _ _ _ _ KP) as RS'.
    cbn [fst snd] in *.
    exact (K1 v st' bs' m' OW' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 ENV' LS' RS' RES').
  Qed.

  Lemma kcall_end : forall {A : Type} (callee : BM (M := btree bptr) A)
      (RES : A -> ST -> list block -> placement -> word -> Prop)
      (Q : A * ST -> PState -> machine_state -> Prop) (fr : list cell) (st : PState) (bs : ST) (m : mem) (OW : list block) (pc : word)
      (rax gp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    KENV fr st bs m OW -> lib_state bs m OW PL EA ->
    (forall errv, bn_pre st bs m OW LB PL EA (Z_to_bv 64 FB) lo B errv CS ->
       implM bgusegs (interp (embed (callee bs))) st
         (bn_post rax (Z_to_bv 64 FB) gp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc st bs OW LB lo B m PL EA RES)
         (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
             F pc fc None m (seg_rom bgusegs))) ->
    (forall v bs' OW' PL' a0', RES v bs' OW' PL' a0' -> PL' = PL) ->
    (forall (v : A) st' bs' m' OW' (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word),
       KENV fr st' bs' m' OW' -> lib_state bs' m' OW' PL EA -> refs_stable bs OW bs' OW' -> RES v bs' OW' PL y3 ->
       evt bgusegs (Q (v, bs') st')
         (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) y0 y1 y2 x8 x9 y3 y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
             F (ret_pc rax) fc None m' (seg_rom bgusegs))) ->
    implM bgusegs (interp (embed (callee bs))) st Q
      (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F pc fc None m (seg_rom bgusegs)).
  Proof using CEIL GLO LOFB FBSP SPB B63 SPR FROK LOF.
    intros until fc. intros ENV LS WALK HPL K1.
    destruct (kenv_pre LB PL EA lo B SPv FB s0 bs0 OW0 m0 CEIL GLO LOFB FBSP SPB B63 SPR FROK _ _ _ _ _ CS ENV LS LOF) as (errv1 & PRE1).
    eapply implM_post_evt; [exact (WALK errv1 PRE1)|].
    cbv beta. intros [v bs'] st' ms' PO.
    apply (bn_post_kpost LB PL EA lo B SPv FB CEIL LOFB FBSP SPR) in PO; [|exact HPL].
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & OW' & -> & KP & RES').
    destruct (kenv_post LB PL EA lo B SPv FB s0 bs0 OW0 m0 CEIL GLO LOFB FBSP FROK _ _ _ _ _ _ _ _ _ ENV KP) as (ENV' & LS').
    pose proof (kpost_refs LB PL EA lo B FB _ _ _ _ _ _ _ _ KP) as RS'.
    cbn [fst snd] in *.
    exact (K1 v st' bs' m' OW' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 ENV' LS' RS' RES').
  Qed.

  Lemma k_is_zero : forall (POST : machine_state -> Prop) (fr : list cell) (st : PState) (bs : ST) (m : mem) (OW : list block) (r : bnref) (ar : Z)
      (ra gp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    KENV fr st bs m OW -> lib_state bs m OW PL EA -> ref_at bs OW PL r ar -> r <> ROne ->
    (forall m' (y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word),
        KENV fr st bs m' OW -> lib_state bs m' OW PL EA ->
        evt bgusegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) y0 y1 y2 x8 x9 (Z_to_bv 64 (Z.b2z (is_zero_pure (getbn r bs))))
                                y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom bgusegs))) ->
    evt bgusegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_IS_ZERO) fc None m (seg_rom bgusegs)).
  Proof using CEIL GLO LOFB FBSP SPB B63 SPR FROK LOF CS128.
    intros until fc. intros ENV LS HA NRO K.
    destruct (kenv_open_u LB PL EA lo B SPv FB s0 bs0 OW0 m0 CEIL FROK _ _ _ _ _ r ar ENV LS HA NRO) as (D & BN & U & (OK1 & OK2 & OK3 & OK4) & A0 & SEPA & SEPD & _ & AL & UP).
    pose proof ENV as (_ & _ & STK & _ & MIK & _). unfold BG_DMAX in OK3.
    assert (ESP : bv_unsigned (Z_to_bv 64 FB) = FB) by (apply unsigned_lit; clear - LOFB FBSP SPR CEIL; lia).
    eapply evt_cut.
    { eapply (BN_is_zero_spec _ (Z_to_bv 64 FB)) with (lo := lo) (A := ar) (D := D) (b := getbn r bs);
        [exact BN | exact AL | clear - OK2 OK3; lia | rewrite ESP; exact STK | rewrite ESP; clear - LOF CS128; lia | exact MIK | rewrite ESP; clear - SEPA LOFB FBSP CS128 LOF; lia | reflexivity]. }
    clear STK MIK.
    intros ms2 PO. unfold bn_small_post in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & -> & MUc & WMc & MIc & STc & ->).
    rewrite ESP in *.
    destruct (kenv_below LB PL EA lo B SPv FB s0 bs0 OW0 m0 CEIL GLO LOFB FBSP SPB B63 SPR FROK _ _ _ _ m2 _ 16 ENV LS ltac:(lia) ltac:(clear - LOF CS128; lia) MUc WMc STc MIc) as (ENV2 & LS2).
    exact (K m2 y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 ENV2 LS2).
  Qed.

  Lemma k_get_flags : forall (POST : machine_state -> Prop) (fr : list cell) (st : PState) (bs : ST) (m : mem) (OW : list block) (r : bnref) (ar : Z) (fl : Z)
      (ra gp t0 t1 t2 x8 x9 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    KENV fr st bs m OW -> lib_state bs m OW PL EA -> ref_at bs OW PL r ar -> r <> ROne -> 0 <= fl < 2^64 ->
    (forall m' (y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word),
        KENV fr st bs m' OW -> lib_state bs m' OW PL EA ->
        evt bgusegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) y0 y1 y2 x8 x9 (Z_to_bv 64 (Z.land (bn_flags (getbn r bs)) fl))
                                y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom bgusegs))) ->
    evt bgusegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) (Z_to_bv 64 fl) a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_GET_FLAGS) fc None m (seg_rom bgusegs)).
  Proof using CEIL GLO LOFB FBSP SPB B63 SPR FROK LOF CS128.
    intros until fc. intros ENV LS HA NRO HFL K.
    destruct (kenv_open_u LB PL EA lo B SPv FB s0 bs0 OW0 m0 CEIL FROK _ _ _ _ _ r ar ENV LS HA NRO) as (D & BN & U & (OK1 & OK2 & OK3 & OK4) & A0 & SEPA & SEPD & _ & AL & UP).
    pose proof ENV as (_ & _ & STK & _ & MIK & _). unfold BG_DMAX in OK3.
    assert (ESP : bv_unsigned (Z_to_bv 64 FB) = FB) by (apply unsigned_lit; clear - LOFB FBSP SPR CEIL; lia).
    eapply evt_cut.
    { eapply (BN_get_flags_spec _ (Z_to_bv 64 FB)) with (lo := lo) (A := ar) (D := D) (b := getbn r bs);
        [exact BN | exact AL | clear - OK4; destruct OK4 as [E|E]; rewrite E; lia | rewrite ESP; exact STK | rewrite ESP; clear - LOF CS128; lia | exact MIK | rewrite ESP; clear - SEPA LOFB FBSP CS128 LOF; lia | reflexivity]. }
    clear STK MIK.
    intros ms2 PO. unfold bn_small_post in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & -> & MUc & WMc & MIc & STc & ->).
    rewrite ESP in *. rewrite (unsigned_lit fl) by (clear - HFL; lia).
    destruct (kenv_below LB PL EA lo B SPv FB s0 bs0 OW0 m0 CEIL GLO LOFB FBSP SPB B63 SPR FROK _ _ _ _ m2 _ 16 ENV LS ltac:(lia) ltac:(clear - LOF CS128; lia) MUc WMc STc MIc) as (ENV2 & LS2).
    exact (K m2 y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 ENV2 LS2).
  Qed.

  Lemma k_is_odd : forall (POST : machine_state -> Prop) (fr : list cell) (st : PState) (bs : ST) (m : mem) (OW : list block) (r : bnref) (ar : Z)
      (ra gp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    KENV fr st bs m OW -> lib_state bs m OW PL EA -> ref_at bs OW PL r ar -> r <> ROne ->
    (forall m' (y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word),
        KENV fr st bs m' OW -> lib_state bs m' OW PL EA ->
        evt bgusegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) y0 y1 y2 x8 x9 (Z_to_bv 64 (Z.b2z (is_odd_pure (getbn r bs))))
                                y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom bgusegs))) ->
    evt bgusegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_IS_ODD) fc None m (seg_rom bgusegs)).
  Proof using CEIL GLO LOFB FBSP SPB B63 SPR FROK LOF CS128.
    intros until fc. intros ENV LS HA NRO K.
    destruct (kenv_open_u LB PL EA lo B SPv FB s0 bs0 OW0 m0 CEIL FROK _ _ _ _ _ r ar ENV LS HA NRO) as (D & BN & U & (OK1 & OK2 & OK3 & OK4) & A0 & SEPA & SEPD & _ & AL & UP).
    pose proof ENV as (_ & _ & STK & _ & MIK & _). unfold BG_DMAX in OK3.
    assert (ESP : bv_unsigned (Z_to_bv 64 FB) = FB) by (apply unsigned_lit; clear - LOFB FBSP SPR CEIL; lia).
    eapply evt_cut.
    { eapply (BN_is_odd_spec _ (Z_to_bv 64 FB)) with (lo := lo) (A := ar) (D := D) (b := getbn r bs);
        [exact BN | exact AL | exact UP | exact U | exact OK1 | exact OK2 | clear - OK3; lia | rewrite ESP; exact STK | rewrite ESP; clear - LOF CS128; lia | exact MIK | rewrite ESP; clear - SEPA LOFB FBSP CS128 LOF; lia | rewrite ESP; clear - SEPD LOFB FBSP CS128 LOF; lia | reflexivity]. }
    clear STK MIK.
    intros ms2 PO. unfold bn_small_post in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & -> & MUc & WMc & MIc & STc & ->).
    rewrite ESP in *.
    destruct (kenv_below LB PL EA lo B SPv FB s0 bs0 OW0 m0 CEIL GLO LOFB FBSP SPB B63 SPR FROK _ _ _ _ m2 _ 16 ENV LS ltac:(lia) ltac:(clear - LOF CS128; lia) MUc WMc STc MIc) as (ENV2 & LS2).
    exact (K m2 y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 ENV2 LS2).
  Qed.

  Lemma k_is_one : forall (POST : machine_state -> Prop) (fr : list cell) (st : PState) (bs : ST) (m : mem) (OW : list block) (r : bnref) (ar : Z)
      (ra gp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    KENV fr st bs m OW -> lib_state bs m OW PL EA -> ref_at bs OW PL r ar -> r <> ROne ->
    (forall m' (y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word),
        KENV fr st bs m' OW -> lib_state bs m' OW PL EA ->
        evt bgusegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) y0 y1 y2 x8 x9 (Z_to_bv 64 (Z.b2z (is_one_pure (getbn r bs))))
                                y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom bgusegs))) ->
    evt bgusegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_IS_ONE) fc None m (seg_rom bgusegs)).
  Proof using CEIL GLO LOFB FBSP SPB B63 SPR FROK LOF CS128.
    intros until fc. intros ENV LS HA NRO K.
    destruct (kenv_open_u LB PL EA lo B SPv FB s0 bs0 OW0 m0 CEIL FROK _ _ _ _ _ r ar ENV LS HA NRO) as (D & BN & U & (OK1 & OK2 & OK3 & OK4) & A0 & SEPA & SEPD & _ & AL & UP).
    pose proof ENV as (_ & _ & STK & _ & MIK & _). unfold BG_DMAX in OK3.
    assert (ESP : bv_unsigned (Z_to_bv 64 FB) = FB) by (apply unsigned_lit; clear - LOFB FBSP SPR CEIL; lia).
    eapply evt_cut.
    { eapply (BN_is_one_spec _ (Z_to_bv 64 FB)) with (lo := lo) (A := ar) (D := D) (b := getbn r bs);
        [exact BN | exact AL | exact UP | exact U | exact OK1 | exact OK2 | clear - OK3; lia | rewrite ESP; exact STK | rewrite ESP; clear - LOF CS128; lia | exact MIK | rewrite ESP; clear - SEPA LOFB FBSP CS128 LOF; lia | rewrite ESP; clear - SEPD LOFB FBSP CS128 LOF; lia | reflexivity]. }
    clear STK MIK.
    intros ms2 PO. unfold bn_small_post in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & -> & MUc & WMc & MIc & STc & ->).
    rewrite ESP in *.
    destruct (kenv_below LB PL EA lo B SPv FB s0 bs0 OW0 m0 CEIL GLO LOFB FBSP SPB B63 SPR FROK _ _ _ _ m2 _ 48 ENV LS ltac:(lia) ltac:(clear - LOF CS128; lia) MUc WMc STc MIc) as (ENV2 & LS2).
    exact (K m2 y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 ENV2 LS2).
  Qed.

  Lemma k_abs_is_word : forall (POST : machine_state -> Prop) (fr : list cell) (st : PState) (bs : ST) (m : mem) (OW : list block) (r : bnref) (ar : Z) (w : Z)
      (ra gp t0 t1 t2 x8 x9 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    KENV fr st bs m OW -> lib_state bs m OW PL EA -> ref_at bs OW PL r ar -> r <> ROne -> 0 <= w < 2^64 ->
    (forall m' (y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word),
        KENV fr st bs m' OW -> lib_state bs m' OW PL EA ->
        evt bgusegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) y0 y1 y2 x8 x9 (Z_to_bv 64 (Z.b2z (abs_is_word_pure (getbn r bs) w)))
                                y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom bgusegs))) ->
    evt bgusegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) (Z_to_bv 64 w) a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_ABS_IS_WORD) fc None m (seg_rom bgusegs)).
  Proof using CEIL GLO LOFB FBSP SPB B63 SPR FROK LOF CS128.
    intros until fc. intros ENV LS HA NRO HW K.
    destruct (kenv_open_u LB PL EA lo B SPv FB s0 bs0 OW0 m0 CEIL FROK _ _ _ _ _ r ar ENV LS HA NRO) as (D & BN & U & (OK1 & OK2 & OK3 & OK4) & A0 & SEPA & SEPD & _ & AL & UP).
    pose proof ENV as (_ & _ & STK & _ & MIK & _). unfold BG_DMAX in OK3.
    assert (ESP : bv_unsigned (Z_to_bv 64 FB) = FB) by (apply unsigned_lit; clear - LOFB FBSP SPR CEIL; lia).
    eapply evt_cut.
    { eapply (BN_abs_is_word_spec _ (Z_to_bv 64 FB)) with (lo := lo) (A := ar) (D := D) (b := getbn r bs);
        [exact BN | exact AL | exact UP | exact U | exact OK1 | exact OK2 | clear - OK3; lia | rewrite ESP; exact STK | rewrite ESP; clear - LOF CS128; lia | exact MIK | rewrite ESP; clear - SEPA LOFB FBSP CS128 LOF; lia | rewrite ESP; clear - SEPD LOFB FBSP CS128 LOF; lia | reflexivity]. }
    clear STK MIK.
    intros ms2 PO. unfold bn_small_post in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & -> & MUc & WMc & MIc & STc & ->).
    rewrite ESP in *. rewrite (unsigned_lit w) by (clear - HW; lia).
    destruct (kenv_below LB PL EA lo B SPv FB s0 bs0 OW0 m0 CEIL GLO LOFB FBSP SPB B63 SPR FROK _ _ _ _ m2 _ 16 ENV LS ltac:(lia) ltac:(clear - LOF CS128; lia) MUc WMc STc MIc) as (ENV2 & LS2).
    exact (K m2 y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 ENV2 LS2).
  Qed.

  Lemma k_is_bit_set : forall (POST : machine_state -> Prop) (fr : list cell) (st : PState) (bs : ST) (m : mem) (OW : list block) (r : bnref) (ar : Z) (n : Z)
      (ra gp t0 t1 t2 x8 x9 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    KENV fr st bs m OW -> lib_state bs m OW PL EA -> ref_at bs OW PL r ar -> r <> ROne -> 0 <= n < 2147483648 ->
    (forall m' (y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word),
        KENV fr st bs m' OW -> lib_state bs m' OW PL EA ->
        evt bgusegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) y0 y1 y2 x8 x9 (Z_to_bv 64 (Z.b2z (is_bit_set_pure (getbn r bs) n)))
                                y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom bgusegs))) ->
    evt bgusegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_IS_BIT_SET) fc None m (seg_rom bgusegs)).
  Proof using CEIL GLO LOFB FBSP SPB B63 SPR FROK LOF CS128.
    intros until fc. intros ENV LS HA NRO HN K.
    destruct (kenv_open_u LB PL EA lo B SPv FB s0 bs0 OW0 m0 CEIL FROK _ _ _ _ _ r ar ENV LS HA NRO) as (D & BN & U & (OK1 & OK2 & OK3 & OK4) & A0 & SEPA & SEPD & _ & AL & UP).
    pose proof ENV as (_ & _ & STK & _ & MIK & _). unfold BG_DMAX in OK3.
    assert (ESP : bv_unsigned (Z_to_bv 64 FB) = FB) by (apply unsigned_lit; clear - LOFB FBSP SPR CEIL; lia).
    eapply evt_cut.
    { eapply (BN_is_bit_set_spec _ (Z_to_bv 64 FB)) with (lo := lo) (A := ar) (D := D) (b := getbn r bs) (n := n);
        [exact BN | exact AL | exact UP | exact U | exact OK1 | exact OK2 | clear - OK3; lia | rewrite ESP; exact STK | rewrite ESP; clear - LOF CS128; lia | exact MIK | rewrite ESP; clear - SEPA LOFB FBSP CS128 LOF; lia | rewrite ESP; clear - SEPD LOFB FBSP CS128 LOF; lia | reflexivity | reflexivity | clear - HN; lia]. }
    clear STK MIK.
    intros ms2 PO. unfold bn_small_post in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & -> & MUc & WMc & MIc & STc & ->).
    rewrite ESP in *.
    destruct (kenv_below LB PL EA lo B SPv FB s0 bs0 OW0 m0 CEIL GLO LOFB FBSP SPB B63 SPR FROK _ _ _ _ m2 _ 16 ENV LS ltac:(lia) ltac:(clear - LOF CS128; lia) MUc WMc STc MIc) as (ENV2 & LS2).
    exact (K m2 y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 ENV2 LS2).
  Qed.

  Lemma k_num_bits : forall (POST : machine_state -> Prop) (fr : list cell) (st : PState) (bs : ST) (m : mem) (OW : list block) (r : bnref) (ar : Z)
      (ra gp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    KENV fr st bs m OW -> lib_state bs m OW PL EA -> ref_at bs OW PL r ar -> r <> ROne ->
    (forall m' (y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word),
        KENV fr st bs m' OW -> lib_state bs m' OW PL EA ->
        evt bgusegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) y0 y1 y2 x8 x9 (Z_to_bv 64 (num_bits_pure (getbn r bs)))
                                y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom bgusegs))) ->
    evt bgusegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_NUM_BITS) fc None m (seg_rom bgusegs)).
  Proof using CEIL GLO LOFB FBSP SPB B63 SPR FROK LOF CS128.
    intros until fc. intros ENV LS HA NRO K.
    destruct (kenv_open_u LB PL EA lo B SPv FB s0 bs0 OW0 m0 CEIL FROK _ _ _ _ _ r ar ENV LS HA NRO) as (D & BN & U & (OK1 & OK2 & OK3 & OK4) & A0 & SEPA & SEPD & _ & AL & UP).
    pose proof ENV as (_ & _ & STK & _ & MIK & _). unfold BG_DMAX in OK3.
    assert (ESP : bv_unsigned (Z_to_bv 64 FB) = FB) by (apply unsigned_lit; clear - LOFB FBSP SPR CEIL; lia).
    eapply evt_cut.
    { eapply (BN_num_bits_spec _ (Z_to_bv 64 FB)) with (lo := lo) (A := ar) (D := D) (b := getbn r bs);
        [exact BN | exact AL | exact UP | exact U | exact OK1 | exact OK2 | clear - OK3; lia | clear - OK4; destruct OK4 as [E|E]; rewrite E; lia | clear - OK4; destruct OK4 as [E|E]; rewrite E; reflexivity | rewrite ESP; exact STK | rewrite ESP; clear - LOF CS128; lia | exact MIK | rewrite ESP; clear - SEPA LOFB FBSP CS128 LOF; lia | rewrite ESP; clear - SEPD LOFB FBSP CS128 LOF; lia | reflexivity]. }
    clear STK MIK.
    intros ms2 PO. unfold bn_small_post in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & -> & MUc & WMc & MIc & STc & ->).
    rewrite ESP in *.
    destruct (kenv_below LB PL EA lo B SPv FB s0 bs0 OW0 m0 CEIL GLO LOFB FBSP SPB B63 SPR FROK _ _ _ _ m2 _ 128 ENV LS ltac:(lia) ltac:(clear - LOF CS128; lia) MUc WMc STc MIc) as (ENV2 & LS2).
    exact (K m2 y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 ENV2 LS2).
  Qed.

End Kit.
End WithCeiling0.
