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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnBridge BgState BgInv BgLib.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit F_memset F_memcpy.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnArith BnMem BnTac BnTacX BnLoop.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnWU Require Import WU_mul_words.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_crypto.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep BnLeaves BnAssoc W_rshift.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import BgLeaves W_expand.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Ltac to_implM :=
  lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
    lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_MUL_WORD : Z := 0x10b2b0.
Definition BN_MUL_WORDS : Z := 0x102d34.
Definition BN_ZERO_EX : Z := 0xff920.
Definition BN_MUL_WORD_STACK : Z := 48 + BN_WEXPAND_STACK.

Definition mul_word_lo (b : bignum bptr) (w : Z) : bignum bptr :=
  bn_with_buf b (splice (bn_buf b) 0 (fst (mul_words (firstn (bn_top b) (bn_buf b)) w))).
Definition mul_word_hi (b : bignum bptr) (top : nat) (ll : Z) : bignum bptr :=
  mkBN (bn_d b) (upd (bn_buf b) top ll) (top + 1) (bn_neg b) (bn_flags b).

Lemma wlimbs_upd : forall l (i : nat) v, (i < length l)%nat -> Arr.upd (wlimbs l) i (Z_to_bv 64 v) = wlimbs (upd l i v).
Proof.
  induction l as [|y l IH]; intros i v H; cbn [length] in H; [lia|].
  destruct i as [|i']; [reflexivity|].
  unfold wlimbs in *. cbn [map Arr.upd]. rewrite (IH i' v) by lia.
  unfold upd, splice. cbn [firstn length Nat.add skipn app map]. reflexivity.
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma BN_mul_word_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rx : bnref) (ax w : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_MUL_WORD_STACK -> tp = wz RATP ->
    ref_at bs OW PL rx ax -> wref PL rx -> a0 = wz ax -> a1 = wz w -> 0 <= w < 2^64 ->
    implM bgusegs (interp (embed (BN_mul_word (tree_ops bptr) rx w bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = wz 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW')))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MUL_WORD) fc None m (seg_rom bgusegs)).
  Proof.
    intros until w. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> HAx WRx -> -> HW. pose proof (proj1 WRx) as NROx.
    unfold BN_MUL_WORD_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, BN_MUL_WORD, GLOBALS_TOP, MallocRep.wz in *.
    change (2 ^ 64) with 18446744073709551616 in HW.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    destruct (lib_state_open [] bs m OW PL EA rx ax LS ND HAx ltac:(intros []) NROx) as ((Dx & BNx & ARRx) & (OKx1 & OKx2 & OKx3 & OKx4) & LSH).
    destruct (bn_arr_facts s OW LB m HEAP bs PL EA _ _ PARTS FROK rx Dx ltac:(eapply ref_at_valid; [exact LS| exact HAx]) NROx ARRx) as (Ux & LENx & Dx0 & DxC & DxI & DSEPx).
    set (bx := getbn rx bs) in *.
    pose proof (DSEPx rx ax HAx) as SEPxx.
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAx NROx) as (XA0 & XAC & XAI).
    assert (ALX : 0 < ax /\ ax mod 8 = 0) by (eapply ref_at_ualign; [exact HEAP| exact PARTS| exact HAx| exact NROx]). destruct ALX as (AX0 & AX8).
    pose proof alloc_ceiling_range as ACR.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HAx) as HVx.
    unfold bn_cells in BNx. unfold BG_DMAX in OKx3.
    assert (LBX : length (bn_buf bx) = bn_dmax bx) by reflexivity.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    unfold BN_mul_word, BN_zero, bbind, bget, bset, bret. cbn [bind ret tree_ops tbind fst snd]. fold bx.
    unfold implM. iprefix.
    carve_frame 48%nat ST. do 6 step. step. ub_chk. step. step. ub_chk.
    step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (bn_top bx))) by lia.
    step.
    assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    assert (WOKh : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) [rx]) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).

    assert (EPI : forall (st1 : PState) (bs1 : bstate bptr) (m2 : mem) (OW2 : list block) (errv2 : word) (jk : list byte)
                         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word),
      RHEAP st1 (OW2 ++ LB) m2 -> lib_state bs1 m2 OW2 PL EA -> rauxv_ok m2 B -> stk bgusegs m2 lo (bv_unsigned sp + -48) ->
      rw_cells bgusegs m2 3346164 [C4 errv2] -> mem_inv bgusegs m2 -> lx_pres LB (bv_unsigned sp) (XW PL) m m2 ->
      ps_fa st1 = ps_fa s -> ps_so st1 = ps_so s -> refs_stable bs OW bs1 OW2 ->
      (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW2) ->
      rw_cells bgusegs m2 (bv_unsigned sp + -48) [CB 8 jk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      implM bgusegs (interp (embed (TRet (tt, bs1)))) st1
        (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
                 (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = Z_to_bv 64 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW')))
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 RATP) x5 x6 x7 sp (Z_to_bv 64 1) x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x10b37c) fc None m2 (seg_rom bgusegs))).
    { intros st1 bs1 m2 OW2 errv2 jk x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31
             HEAP2 LS2 AUX2 ST2 ERR2 MI2 LXP2 FA2 SO2 RST2 BST FR2.
      clear BNx ARRx Ux MU WM ST ERR MI FR HWL WOK WOKh LSH.
      cbn [embed interp]. apply implM_ret.
      step. do 5 step. release_frame FR2 ST2 (bv_unsigned sp). step. step.
      apply evt_done.
      unfold bn_post. do 15 eexists. exists m2, OW2, PL, errv2. split; [reflexivity|]. cbn [fst snd].
      split; [exact HEAP2|]. split; [exact LS2|]. split; [exact AUX2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact MI2|].
      split; [exact LXP2|]. split; [exact FA2|]. split; [exact SO2|]. split; [exact RST2|].
      split; [reflexivity|]. split; [reflexivity| exact BST]. }
    step. if_cases KT; zify_cond KT.
    -
      assert (ET : bn_top bx = 0%nat) by lia.
      replace (bn_top bx =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; exact ET).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      ihere. to_implM.
      eapply (EPI s bs m1 OW errv);
        [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)
        | exact (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK)
        | apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); unfold GLOBALS_TOP; lia
        | exact ST | exact ERR | exact MI
        | apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); unfold GLOBALS_TOP; lia
        | reflexivity | reflexivity | apply refs_stable_refl
        | intros q0 A0 n0 Hq0 _; exact Hq0 | exact FR].
    -
      assert (NT : bn_top bx <> 0%nat) by lia.
      replace (bn_top bx =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; exact NT).

      assert (HDx : exists px, bn_d bx = Some px /\ In (px, Dx, 8 * Z.of_nat (bn_dmax bx)) OW).
      { pose proof ARRx as ARRx'. unfold bn_arr in ARRx'. destruct (bn_d bx) as [px|] eqn:Edx0; [exists px; split; [reflexivity| exact (proj1 ARRx')]|].
        exfalso. destruct (bn_arr_null PL rx m OW Dx bx PWF WRx Edx0 ARRx) as [_ E]. unfold bn_dmax in OKx2. rewrite E in OKx2. cbn in OKx2. lia. }
      destruct HDx as (px & Edx & Hinpx).
      assert (ALD : 0 < Dx /\ Dx mod 8 = 0) by (eapply block_ualign; [exact HEAP| exact Hinpx]). destruct ALD as (DX0 & DX8).
      step. step. if_cases KW; zify_cond KW.
      +
        assert (EW : w = 0) by (rewrite ?unsigned_lit in KW by lia; lia).
        replace (w =? 0) with true by (symmetry; apply Z.eqb_eq; exact EW). cbn [tbind fst snd]. fold bx.
        step. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
        assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
        eapply evt_cut.
        { eapply BgBnU.W_rshift.BN_zero_ex_spec with (lo := lo) (A := ax) (D := Dx) (b := bx);
            [exact BNx | exact (conj AX0 AX8) | rewrite ESP; exact ST | rewrite ESP; lia | exact MI | rewrite ESP; lia | reflexivity]. }
        intros ms' PO. unfold BgBnU.W_small.bn_small_post in PO.
        destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & STc & BNz).
        subst ms'. rewrite ESP in *.
        lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
          replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
        eapply (rw_cells_transport bgusegs _ m1 m2) in FR; [| exact MUc | exact WMc | cbn; lia].
        eapply (rw_cells_transport bgusegs _ m1 m2) in ERR; [| exact MUc | exact WMc | cbn; lia].
        assert (Ux2 : u64arr bgusegs m2 Dx (wlimbs (bn_buf bx))).
        { eapply u64arr_transport; [exact Ux| exact MUc| exact WMc|]. cbn [disjoint_from]. rewrite wlimbs_len. fold (bn_dmax bx). lia. }
        clear ST MI BNx Ux.
        step.
        assert (MUT : munch [(bv_unsigned sp - 64, bv_unsigned sp); (ax, ax + 24)]%Z m m2).
        { eapply munch_trans; [eapply munch_weaken; [|exact MU]| eapply munch_weaken; [|exact MUc]]; unfold sub_fp; intros x Hx; cbn [outside] in *; lia. }
        assert (WMT : wmono bgusegs m m2) by (eapply wmono_trans; [exact WM| exact WMc]).
        assert (HWLT : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp - 64, bv_unsigned sp); (ax, ax + 24)]).
        { constructor; [left; cbn; lia|]. constructor; [right; right; exists rx, ax; split; [exact HAx|]; split; [exact NROx|]; cbn; lia| constructor]. }
        assert (WOKc : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) [rx]) [(bv_unsigned sp - 64, bv_unsigned sp); (ax, ax + 24)]).
        { constructor; [apply w_stack; cbn; lia|]. constructor; [eapply (w_struct OW LB bs PL EA (bv_unsigned sp) false [rx] _ rx ax); [left; reflexivity| exact HAx| exact NROx| cbn; lia| cbn; lia]| constructor]. }
        ihere. to_implM.
        eapply (EPI s (setbn rx (bn_zero_pure bx) bs) m2 OW errv);
          [ exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MUT WMT HWLT CEIL)
          | | apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MUT WMT HWLT SPB ltac:(lia)); unfold GLOBALS_TOP; lia
          | exact STc | exact ERR | exact MIc
          | apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MUT WMT HWLT CEIL); unfold GLOBALS_TOP; lia
          | reflexivity | reflexivity | apply refs_stable_setbn
          | intros q0 A0 n0 Hq0 _; exact Hq0 | exact FR ].
        unfold lib_state. eapply (lib_state_close [] bs m2 OW PL EA rx ax); [| exact ND| exact HAx| exact NROx| | |].
        * exact (lib_state_frame s LB _ _ [rx] bs m m2 OW PL EA _ HEAP LSH MUT WMT FROK WOKc).
        * exists Dx. split; [exact BNz|]. unfold bn_zero_pure. eapply bn_arr_of_u64arr; [exact ARRx|]. cbn [bn_buf]. exact Ux2.
        * unfold bg_ok, bn_zero_pure, bn_dmax in *. cbn [bn_buf bn_top bn_flags]. split; [exact OKx1|]. split; [lia|]. split; [unfold BG_DMAX; exact OKx3| exact OKx4].
        * apply ids_ok_setbn_same; [exact IDS| exact HVx| reflexivity].
      +
        assert (NW : w <> 0) by (rewrite ?unsigned_lit in KW by lia; lia).
        replace (w =? 0) with false by (symmetry; apply Z.eqb_neq; exact NW).
        pose proof (mul_words_spec (firstn (bn_top bx) (bn_buf bx)) w (limbs_firstn _ _ OKx1) ltac:(unfold limb; rewrite BW_lit; exact HW)) as MWS.
        destruct (mul_words (firstn (bn_top bx) (bn_buf bx)) w) as [l ll] eqn:EMW.
        destruct MWS as (Ll & LENl & Lll & _). rewrite firstn_length_le in LENl by lia. unfold limb in Lll. rewrite BW_lit in Lll.
        cbn [tbind fst snd]. fold bx.
        step. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
        assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
        assert (EDx : bv_unsigned (Z_to_bv 64 Dx) = Dx) by (apply unsigned_lit; lia).
        assert (ETP : bv_unsigned (Z_to_bv 64 (Z.of_nat (bn_top bx))) = Z.of_nat (bn_top bx)) by (apply unsigned_lit; lia).
        assert (EWW : bv_unsigned (Z_to_bv 64 w) = w) by (apply unsigned_lit; lia).

        apply (proj1 (limbarr_split bgusegs _ Dx (bn_buf bx) (bn_top bx) ltac:(lia))) in Ux. destruct Ux as [U1 U2].
        assert (LU2 : Z.of_nat (length (wlimbs (skipn (bn_top bx) (bn_buf bx)))) = Z.of_nat (bn_dmax bx) - Z.of_nat (bn_top bx)) by (rewrite wlimbs_len, length_skipn, LBX; lia).
        pose proof (limbs_at_of_u64arr bgusegs _ _ _ U1) as RA1. destruct U1 as [_ WR1]. rewrite wlimbs_len, firstn_length_le in WR1 by lia.
        step.
        eapply evt_cut.
        { eapply bn_mul_words_uspec with (a := firstn (bn_top bx) (bn_buf bx)) (lo := lo) (m := m1);
            rewrite ?EDx, ?ETP, ?ESP, ?EWW, ?firstn_length_le by lia;
            [ apply limbs_firstn; exact OKx1 | lia | reflexivity | exact RA1 | exact WR1 | left; reflexivity | exact ST | lia | lia | lia | exact MI
            | intros _; exact (conj DX0 DX8) | intros _; exact (conj DX0 DX8) ]. }
        intros ms' PO. unfold mw_upost, wl_post in PO.
        destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & RES & STc).
        subst ms'. rewrite ?EDx, ?ESP, ?EWW, ?firstn_length_le, ?EMW in * by lia. cbn [fst snd] in RES, MUc |- *.
        lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
          replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
        eapply (rw_cells_transport bgusegs _ m1 m2) in FR; [| exact MUc | exact WMc | cbn; lia].
        eapply (rw_cells_transport bgusegs _ m1 m2) in ERR; [| exact MUc | exact WMc | cbn; lia].
        eapply (rw_cells_transport bgusegs _ m1 m2) in BNx; [| exact MUc | exact WMc | cbn; lia].
        assert (U22 : u64arr bgusegs m2 (Dx + 8 * Z.of_nat (bn_top bx)) (wlimbs (skipn (bn_top bx) (bn_buf bx)))).
        { eapply u64arr_transport; [exact U2| exact MUc| exact WMc|]. cbn [disjoint_from]. lia. }
        pose proof (wr_at_transport bgusegs m1 m2 _ _ WR1 WMc) as WR2.
        clear ST MI U2.

        set (nb := splice (bn_buf bx) 0 l).
        assert (Enb : nb = l ++ skipn (bn_top bx) (bn_buf bx)) by (subst nb; unfold splice; rewrite firstn_O, LENl; reflexivity).
        assert (Lnb : length nb = bn_dmax bx) by (subst nb; rewrite splice_length; [exact LBX| rewrite LENl, LBX; lia]).
        assert (LMnb : limbs nb) by (subst nb; apply splice_limbs; [exact OKx1| exact Ll]).
        assert (UF : u64arr bgusegs m2 Dx (wlimbs nb)).
        { rewrite Enb. apply limbarr_app. rewrite LENl. split; [| exact U22]. apply u64arr_of_limbs_at; [exact RES| rewrite LENl; exact WR2]. }
        assert (MUT : munch [(bv_unsigned sp - 144, bv_unsigned sp); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]%Z m m2).
        { eapply munch_trans; [eapply munch_weaken; [|exact MU]| eapply munch_weaken; [|exact MUc]]; unfold sub_fp; intros x Hx; cbn [outside] in *; lia. }
        assert (WMT : wmono bgusegs m m2) by (eapply wmono_trans; [exact WM| exact WMc]).
        assert (HWLT : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp - 144, bv_unsigned sp); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]).
        { constructor; [left; cbn; lia|]. constructor; [| constructor]. right; left; exists (px, Dx, 8 * Z.of_nat (bn_dmax bx)); cbn; split; [exact Hinpx| clear; lia]. }
        assert (WOKc : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) [rx]) [(bv_unsigned sp - 144, bv_unsigned sp); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]).
        { constructor; [apply w_stack; cbn; lia|]. constructor; [| constructor].
          eapply (w_limbs OW LB bs PL EA (bv_unsigned sp) false [rx] _ rx px Dx); [left; reflexivity| exact HVx| exact Edx| exact Hinpx| cbn [fst snd]; fold bx; clear; lia| cbn [fst snd]; fold bx; clear; lia]. }
        set (bs2 := setbn rx (mul_word_lo bx w) bs).
        assert (LS2 : lib_state bs2 m2 OW PL EA).
        { unfold lib_state. eapply (lib_state_close [] bs m2 OW PL EA rx ax); [| exact ND| exact HAx| exact NROx| | |].
          - exact (lib_state_frame s LB _ _ [rx] bs m m2 OW PL EA _ HEAP LSH MUT WMT FROK WOKc).
          - exists Dx. split.
            + unfold bn_cells, bn_dmax, mul_word_lo, bn_with_buf. cbn [bn_top bn_buf bn_neg bn_flags bn_d]. rewrite EMW. cbn [fst]. fold nb. rewrite Lnb. exact BNx.
            + unfold bn_arr, bn_dmax, mul_word_lo, bn_with_buf. cbn [bn_d bn_buf]. rewrite EMW. cbn [fst]. fold nb. rewrite Edx, Lnb. split; [exact Hinpx| exact UF].
          - unfold bg_ok, bn_dmax, mul_word_lo, bn_with_buf. cbn [bn_buf bn_top bn_flags]. rewrite EMW. cbn [fst]. fold nb. rewrite Lnb. unfold BG_DMAX in *.
            split; [exact LMnb|]. split; [exact OKx2|]. split; [clear - OKx3; unfold bn_dmax in *; lia| exact OKx4].
          - apply ids_ok_setbn_same; [exact IDS| exact HVx|]. unfold bn_blocks, bn_dmax, mul_word_lo, bn_with_buf. cbn [bn_d bn_buf]. rewrite EMW. cbn [fst]. fold nb. rewrite Lnb. reflexivity. }
        pose proof (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MUT WMT HWLT CEIL) as HEAP2.
        assert (AUX2 : rauxv_ok m2 B) by (apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MUT WMT HWLT SPB ltac:(lia)); unfold GLOBALS_TOP; lia).
        assert (LXP2 : lx_pres LB (bv_unsigned sp) (XW PL) m m2) by (apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MUT WMT HWLT CEIL); unfold GLOBALS_TOP; lia).
        assert (RST2 : refs_stable bs OW bs2 OW) by (apply refs_stable_setbn).
        assert (Ebs2 : setbn rx (bn_with_buf bx (splice (bn_buf bx) 0 l)) bs = bs2) by (subst bs2; unfold mul_word_lo; rewrite EMW; reflexivity).
        rewrite Ebs2.
        clear U22 WR2 RES UF LSH MUT HWLT WOKc MUc WMc WMT.
        step. if_cases KL; zify_cond KL.
        *
          assert (EL : ll = 0) by (rewrite ?unsigned_lit in KL by lia; lia).
          replace (ll =? 0) with true by (symmetry; apply Z.eqb_eq; exact EL).
          ihere. to_implM.
          eapply (EPI s bs2 m2 OW errv);
            [exact HEAP2 | exact LS2 | exact AUX2 | exact STc | exact ERR | exact MIc | exact LXP2
            | reflexivity | reflexivity | exact RST2 | intros q0 A0 n0 Hq0 _; exact Hq0 | exact FR].
        *
          assert (NL : ll <> 0) by (rewrite ?unsigned_lit in KL by lia; lia).
          replace (ll =? 0) with false by (symmetry; apply Z.eqb_neq; exact NL).
          assert (HAx2 : ref_at bs2 OW PL rx ax) by (eapply ref_at_stable; [exact RST2| exact HAx]).
          assert (HVx2 : vref rx bs2) by (eapply ref_at_valid; [exact LS2| exact HAx2]).
          assert (ETOP2 : bn_top (getbn rx bs2) = bn_top bx) by (subst bs2; rewrite getbn_setbn_same by exact HVx; reflexivity).
          assert (OK22 : (bn_top (getbn rx bs2) <= bn_dmax (getbn rx bs2))%nat).
          { subst bs2. rewrite getbn_setbn_same by exact HVx. unfold mul_word_lo, bn_with_buf, bn_dmax. rewrite EMW. cbn [bn_top bn_buf fst]. fold nb. rewrite Lnb. exact OKx2. }
          step. step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (bn_top bx))) by lia.
          step. ub_chk. step. step.
          clear BNx.
          ihere. to_implM.
          eapply implM_embed_bind.
          { eapply BnLeaves.implM_embed_leaves; [apply (bn_wexpand_leaves rx (bn_top bx + 1) bs2 HVx2 OK22)|].
            eapply (bn_wexpand_walk HM HF) with (lo := lo) (B := B) (errv := errv) (r := rx) (a := ax) (OW := OW) (LB := LB) (PL := PL) (EA := EA) (words := (bn_top bx + 1)%nat);
              [| reflexivity | exact HAx2 | exact WRx | reflexivity | unfold MallocRep.wz; f_equal; lia | lia].
            unfold bn_pre. rewrite ESP.
            split; [exact HEAP2|]. split; [exact LS2|]. split; [eapply frames_ok_call; [exact FROK| exact CEIL| lia| lia]|]. split; [exact AUX2|]. split; [lia|]. split; [exact B63|].
            split; [exact STc|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; lia|]. split; [unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK; lia|].
            split; [unfold LX_ERRNO, RATP; exact ERR| exact MIc]. }
          cbv beta. intros [u bs3] st3 ms3 [PO LEAF]. unfold bn_post in PO. cbn [fst snd] in *.
          destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m4 & OW4 & PL4 & errv4 & -> & HEAP4 & LS4 & AUX4 & ST4 & ERR4
                          & MI4 & LXP4 & FA4 & SO4 & RST4 & -> & -> & HDM & WRES & BST4).
          rewrite ESP in *. unfold LX_ERRNO, RATP in ERR4. change (3346328 - 164) with 3346164 in ERR4.
          lazymatch goal with |- implM _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
            replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
          destruct LEAF as (LF1 & LF2 & LF3 & LF4 & LF5 & LF6). cbn [snd] in *. rewrite ETOP2 in LF2.
          lazymatch type of FR with rw_cells _ _ ?adr ?cells => assert (FR4 : rw_cells bgusegs m4 adr cells) end.
          { eapply rw_cells_agree; [apply agree_of_lx_pres; exact LXP4 | exact FR |].
            intros a Ha. cbn in Ha. eapply (xw_client PL LB _ (bv_unsigned sp) B); [exact (proj1 FROK)| lia|].
            unfold LIBW_bgr, BnRep.LIBW_bn, CONST_ONE, BN_STRUCT_SZ. cbn [rin_ivs app fst snd]. lia. }
          clear FR ERR STc MIc.

          assert (FROK4 : frames_ok PL (bv_unsigned sp) B) by exact FROK.
          pose proof (ref_at_stable _ _ _ _ _ _ _ RST4 HAx2) as HAx4.
          pose proof (RH_nodup_l _ _ _ _ HEAP4) as ND4.
          pose proof (lib_state_h_parts _ _ _ _ _ _ LS4) as PARTS4; pose proof PARTS4 as (WFS4 & PWF4 & IDS4 & PLB4 & ERRB4).
          pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS4 HAx4) as HVx4.
          destruct (lib_state_open [] bs3 m4 OW4 PL EA rx ax LS4 ND4 HAx4 ltac:(intros []) NROx) as ((Dr & BNr & ARRr) & (OKq1 & OKq2 & OKq3 & OKq4) & LSH4).
          destruct (bn_arr_facts st3 OW4 LB m4 HEAP4 bs3 PL EA _ _ PARTS4 FROK4 rx Dr HVx4 ltac:(assumption) ARRr) as (Ur & LENr & Dr0 & DrC & DrI & DSEPr).
          set (br := getbn rx bs3) in *.
          pose proof (DSEPr rx ax HAx4) as SEPrr.
          pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP4 PARTS4 FROK4 HAx4 NROx) as (XB0 & XBC & XBI).
          unfold bn_cells in BNr. unfold BG_DMAX in OKq3. rewrite LF2 in BNr.
          assert (HDr : exists pr, bn_d br = Some pr /\ In (pr, Dr, 8 * Z.of_nat (bn_dmax br)) OW4).
          { pose proof ARRr as ARRr'. unfold bn_arr in ARRr'. destruct (bn_d br) as [pr|] eqn:Edr0; [exists pr; split; [reflexivity| exact (proj1 ARRr')]|].
            exfalso. destruct (bn_arr_null PL rx m4 OW4 Dr br PWF4 WRx Edr0 ARRr) as [_ E]. unfold bn_dmax in HDM. rewrite E in HDM. cbn in HDM. lia. }
          destruct HDr as (pr & Edr & Hinpr).
          assert (ALR : 0 < Dr /\ Dr mod 8 = 0) by (eapply block_ualign; [exact HEAP4| exact Hinpr]). destruct ALR as (DR0 & DR8).

          clear LENx Dx0 DxC DxI SEPxx DSEPx XA0 XAC XAI EDx ETP EWW KT KW KL RA1 WR1 Hinpx Edx LU2 Lnb LMnb Enb.
          assert (LBR : length (bn_buf br) = bn_dmax br) by reflexivity.
          pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (ax, ax + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m4) as MU5.
          pose proof (wmono_refl bgusegs m4) as WM5.
          unfold implM. iprefix.
          step. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by lia; lia|]. clear KZ.

          step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (bn_top bx))) by lia.
          step. ub_chk.
          step. step. step. step. step.
          step. replace (Z.of_nat (bn_top bx) + 1) with (Z.of_nat (bn_top bx + 1)) in BNr by lia.
          setreg 10%Z (Z_to_bv 64 (Dr + 8 * Z.of_nat (bn_top bx))) ltac:(f_equal; rewrite (unsigned_lit (Z.of_nat (bn_top bx))) by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
          ub_chk. do 4 step. ub_chk. ub_chk. step. ub_chk.
          assert (IDX : 0 <= Z.of_nat (bn_top bx) < Z.of_nat (length (wlimbs (bn_buf br)))) by (rewrite wlimbs_len, LBR; unfold bn_dmax in HDM; lia).
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
            pose proof (u64arr_store_ok bgusegs mx Dr _ (Z.of_nat (bn_top bx)) (wa (Dr + 8 * Z.of_nat (bn_top bx))) Ur IDX eq_refl) as SOKW;
            pose proof (u64arr_write bgusegs mx Dr _ (Z.of_nat (bn_top bx)) (Z_to_bv 64 ll) Ur IDX) as U6 end.
          rewrite Nat2Z.id, (wlimbs_upd (bn_buf br) (bn_top bx)) in U6 by (rewrite LBR; unfold bn_dmax in HDM; lia).
          clear Ur. step. store_done.
          step.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
          set (nb2 := upd (bn_buf br) (bn_top bx) ll) in *.
          assert (Lnb2 : length nb2 = bn_dmax br) by (subst nb2; rewrite upd_length by (rewrite LBR; unfold bn_dmax in HDM; lia); exact LBR).
          assert (LMnb2 : limbs nb2) by (subst nb2; apply upd_limbs; [exact OKq1| unfold limb; rewrite BW_lit; exact Lll]).
          assert (HWL5 : Forall (w_lib bs3 OW4 PL lo (bv_unsigned sp)) [(bv_unsigned sp + -48, bv_unsigned sp); (ax, ax + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
          { constructor; [left; cbn; lia|]. constructor; [right; right; exists rx, ax; split; [exact HAx4|]; split; [exact NROx|]; cbn; lia|].
            constructor; [| constructor]. right; left; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn; split; [exact Hinpr| clear; lia]. }
          assert (WOK5 : Forall (w_ok OW4 LB bs3 PL EA (bv_unsigned sp) [rx]) [(bv_unsigned sp + -48, bv_unsigned sp); (ax, ax + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
          { constructor; [apply w_stack; cbn; lia|]. constructor; [eapply (w_struct OW4 LB bs3 PL EA (bv_unsigned sp) false [rx] _ rx ax); [left; reflexivity| exact HAx4| assumption| cbn; lia| cbn; lia]|].
            constructor; [| constructor].
            eapply (w_limbs OW4 LB bs3 PL EA (bv_unsigned sp) false [rx] _ rx pr Dr); [left; reflexivity| exact HVx4| exact Edr| exact Hinpr| cbn [fst snd]; fold br; clear; lia| cbn [fst snd]; fold br; clear; lia]. }
          ihere. to_implM. cbn [tbind fst snd]. fold br.
          change (mkBN (bn_d br) (upd (bn_buf br) (bn_top bx) ll) (bn_top bx + 1) (bn_neg br) (bn_flags br)) with (mul_word_hi br (bn_top bx) ll).
          eapply (EPI st3 (setbn rx (mul_word_hi br (bn_top bx) ll) bs3) m6 OW4 errv4);
            [ exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP4 PARTS4 FROK4 MU5 WM5 HWL5 CEIL)
            | | apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP4 PARTS4 FROK4 AUX4 MU5 WM5 HWL5 SPB ltac:(lia)); unfold GLOBALS_TOP; lia
            | assumption | exact ERR4 | assumption
            | eapply lx_pres_trans; [exact LXP2|]; eapply lx_pres_trans; [eapply lx_pres_weaken; [exact LXP4| lia | intros b0 Hb0; exact Hb0 | intros q0 Hq0; exact Hq0]|];
              apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP4 PARTS4 FROK4 MU5 WM5 HWL5 CEIL); unfold GLOBALS_TOP; lia
            | congruence | congruence
            | eapply refs_stable_trans; [exact RST2|]; eapply refs_stable_trans; [exact RST4| apply refs_stable_setbn]
            | intros q0 A0 n0 Hq0 Hne; apply BST4; [exact Hq0|]; subst bs2; rewrite getbn_setbn_same by exact HVx; unfold mul_word_lo, bn_with_buf; cbn [bn_d]; exact Hne
            | exact FR4 ].
          unfold lib_state. eapply (lib_state_close [] bs3 m6 OW4 PL EA rx ax); [| exact ND4| exact HAx4| exact NROx| | |].
          -- exact (lib_state_frame st3 LB _ _ [rx] bs3 m4 m6 OW4 PL EA _ HEAP4 LSH4 MU5 WM5 FROK WOK5).
          -- exists Dr. split.
             ++ unfold bn_cells, bn_dmax, mul_word_hi. cbn [bn_top bn_buf bn_neg bn_flags bn_d]. fold nb2. rewrite Lnb2. exact BNr.
             ++ unfold bn_arr, bn_dmax, mul_word_hi. cbn [bn_d bn_buf]. fold nb2. rewrite Edr, Lnb2. split; [exact Hinpr| exact U6].
          -- unfold bg_ok, bn_dmax, mul_word_hi. cbn [bn_buf bn_top bn_flags]. fold nb2. rewrite Lnb2. unfold BG_DMAX in *.
             split; [exact LMnb2|]. split; [unfold bn_dmax in HDM; lia|]. split; [clear - OKq3; unfold bn_dmax in *; lia| exact OKq4].
          -- apply ids_ok_setbn_same; [exact IDS4| exact HVx4|]. unfold bn_blocks, bn_dmax, mul_word_hi. cbn [bn_d bn_buf]. fold nb2. rewrite Lnb2. reflexivity.
  Qed.
End Proofs.
End WithCeiling0.
