(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWordsCorrect BnModel BnTree BnInv BnBridge BgState BgInv BgLib.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_small W_small2 W_top.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU2 Require Import W_ctx3.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnEU Require Import ExpKit PlaceRecp ExpKit2.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Section Env.
  Variables (LB : list block) (PL0 : placement) (EA : BnRep.err_addrs) (lo B SPv FB : Z).
  Variables (s0 : PState) (bs0 : bstate bptr) (OW0 : list block) (m0 : mem).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis LOFB : lo <= FB.
  Hypothesis FBSP : FB <= SPv.
  Hypothesis SPB : SPv <= B.
  Hypothesis B63 : B < 2^63.
  Hypothesis SPR : SPv < 2^64.
  Hypothesis FROK0 : frames_ok PL0 SPv B.
  Hypothesis AN2 : FB + 8 + 60 <= SPv.

  Lemma recp_init_call : forall (POST : machine_state -> Prop) (j0 rcj : list byte) (fr2 : list cell) (st : PState) (bs : bstate bptr) (m : mem) (OW : list block)
      (ra gp tp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    lo <= FB - 48 -> FB mod 16 = 0 -> tp = Z_to_bv 64 RATP ->
    kenv LB PL0 lo B SPv FB s0 bs0 OW0 m0 (CB 8 j0 :: CB 64 rcj :: fr2) st bs m OW -> lib_state bs m OW PL0 EA ->
    pl_bn PL0 RRecpN = None -> pl_bn PL0 RRecpNr = None -> pl_recp PL0 = None ->
    (forall m' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
        kenv2 LB PL0 lo B SPv FB (FB + 8) s0 bs0 OW0 m0 [CB 8 j0] (C4 (wz 0) :: fr2) st (st_recp_init bs) m' OW ->
        lib_state (st_recp_init bs) m' OW (pl_place_recp PL0 (FB + 8)) EA ->
        evt bgusegs POST (MS (mkR ra (Z_to_bv 64 FB) gp tp y0 y1 y2 x8 x9 y3 y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom bgusegs))) ->
    evt bgusegs POST (MS (mkR ra (Z_to_bv 64 FB) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 (FB + 8)) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_RECP_CTX_INIT) fc None m (seg_rom bgusegs)).
  Proof using CEIL GLO LOFB FBSP SPB B63 SPR FROK0 AN2.
    intros until fc. intros LO48 FB16 -> ENV LS E1 E2 E3 K.
    pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR & FSZ).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    assert (ESP : bv_unsigned (Z_to_bv 64 FB) = FB) by (apply unsigned_lit; clear - CEIL LOFB FBSP SPR; lia).
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR. unfold GLOBALS_TOP in GLO.
    change (CB 8 j0 :: CB 64 rcj :: fr2) with ([CB 8 j0] ++ [CB 64 rcj] ++ fr2) in FR.
    apply bk_rw_cells_app in FR. destruct FR as [F1 FR]. change (Z.of_nat (cells_size [CB 8 j0])) with 8 in FR.
    apply bk_rw_cells_app in FR. destruct FR as [FRC F2]. change (Z.of_nat (cells_size [CB 64 rcj])) with 64 in F2.
    cbn [cells_size csize] in FSZ.
    eapply evt_cut.
    { eapply (BN_RECP_CTX_init_spec ra (Z_to_bv 64 FB)) with (lo := lo) (A := FB + 8) (junk := rcj);
        [exact FRC | split; [lia | clear - FB16; Z.div_mod_to_equations; lia] | rewrite ESP; exact ST | rewrite ESP; exact LO48 | exact MI | rewrite ESP; right; lia | reflexivity]. }
    intros ms' PO. unfold bn_small_post in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & E & MUc & WMc & MIc & STc & RES).
    subst ms'. rewrite ESP in *.
    eapply (rw_cells_transport bgusegs _ m m') in F1; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; lia].
    eapply (rw_cells_transport bgusegs _ m m') in F2; [| exact MUc | exact WMc | cbn [disjoint_from]; clear - FSZ; lia].
    eapply (rw_cells_transport bgusegs _ m m') in ERR; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; clear - GLO LOFB LO48; lia].
    assert (HWL : Forall (w_lib bs OW PL0 lo SPv) [(FB - 48, FB); (FB + 8, FB + 8 + 64)]).
    { constructor; [left; cbn [fst snd]; lia|]. constructor; [left; cbn [fst snd]; clear - FSZ LOFB; lia| constructor]. }
    assert (WOK : Forall (w_okc OW LB bs PL0 EA SPv false []) [(FB - 48, FB); (FB + 8, FB + 8 + 64)]).
    { constructor; [apply w_stack; cbn [fst snd]; lia|]. constructor; [apply w_stack; cbn [fst snd]; clear - FSZ LOFB CEIL; lia| constructor]. }
    pose proof (lib_state_frame st LB SPv B [] bs m m' OW PL0 EA _ HEAP LS MUc WMc FROK0 WOK) as LS'.
    unfold recp_cells0 in RES.
    assert (FRN : rw_cells bgusegs m' FB ([CB 8 j0] ++ (bn_cells 0 (bn_nil 0) ++ bn_cells 0 (bn_nil 0) ++ [C4 (wz 0); C4 (wz 0); C4 (wz 0)]) ++ (C4 (wz 0) :: fr2))).
    { apply bk_rw_cells_app. split; [exact F1|]. change (Z.of_nat (cells_size [CB 8 j0])) with 8.
      apply bk_rw_cells_app. split.
      - apply (bk_rw_cells_app bgusegs m' (FB + 8) (bn_cells 0 (bn_nil 0) ++ bn_cells 0 (bn_nil 0) ++ [C4 (wz 0); C4 (wz 0); C4 (wz 0)]) [C4 (wz 0)]).
        exact RES.
      - change (Z.of_nat (cells_size (bn_cells 0 (bn_nil 0) ++ bn_cells 0 (bn_nil 0) ++ [C4 (wz 0); C4 (wz 0); C4 (wz 0)]))) with 60.
        change (C4 (wz 0) :: fr2) with ([C4 (wz 0)] ++ fr2). apply bk_rw_cells_app. split.
        + apply (bk_rw_cells_app bgusegs m' (FB + 8) (bn_cells 0 (bn_nil 0) ++ bn_cells 0 (bn_nil 0) ++ [C4 (wz 0); C4 (wz 0); C4 (wz 0)]) [C4 (wz 0)]) in RES.
          exact (proj2 RES).
        + change (Z.of_nat (cells_size [C4 (wz 0)])) with 4. replace (FB + 8 + 60 + 4) with (FB + 8 + 64) by lia. exact F2. }
    assert (ENV' : kenv LB PL0 lo B SPv FB s0 bs0 OW0 m0
                     ([CB 8 j0] ++ (bn_cells 0 (bn_nil 0) ++ bn_cells 0 (bn_nil 0) ++ [C4 (wz 0); C4 (wz 0); C4 (wz 0)]) ++ (C4 (wz 0) :: fr2)) st bs m' OW).
    { eapply (kenv_silent LB PL0 EA lo B SPv FB s0 bs0 OW0 m0 CEIL ltac:(unfold GLOBALS_TOP; exact GLO) LOFB FBSP SPB FROK0 _ _ st bs m m' OW _ errv);
        [exact ENV | exact PARTS | exact MUc | exact WMc | exact HWL | exact STc | unfold LX_ERRNO, RATP; exact ERR | exact MIc | exact FRN |].
      rewrite !cells_size_app. cbn [cells_size csize bn_cells app]. clear - FSZ. lia. }
    destruct (kenv_place LB PL0 EA lo B SPv FB (FB + 8) s0 bs0 OW0 m0 CEIL ltac:(unfold GLOBALS_TOP; exact GLO) LOFB FBSP SPB FROK0 ltac:(lia) AN2
                [CB 8 j0] (C4 (wz 0) :: fr2) st bs m' OW ENV' LS' ltac:(cbn; lia) ltac:(clear - CEIL LOFB; lia)
                ltac:(clear - FB16; Z.div_mod_to_equations; lia) E1 E2 E3) as (ENV2 & LS2).
    eapply K; [exact ENV2| exact LS2].
  Qed.

End Env.
End WithCeiling0.
