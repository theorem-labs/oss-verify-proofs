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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel BnTree BnInv BnBridge BgState BgInv BgLib.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit F_memset F_memcpy.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem BnTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_crypto.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep BnLeaves.
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

Definition BN_SET_WORD : Z := 0xfe4e4.
Definition BN_SET_WORD_STACK : Z := 32 + BN_EXPAND2_STACK.

Definition set_word_bn (b : bignum bptr) (w : Z) : bignum bptr :=
  mkBN (bn_d b) (upd (bn_buf b) 0 w) (if w =? 0 then 0%nat else 1%nat) false (bn_flags b).

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma BN_set_word_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rx : bnref) (ax w : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_SET_WORD_STACK -> tp = wz RATP ->
    ref_at bs OW PL rx ax -> wref PL rx -> a0 = wz ax -> a1 = wz w -> 0 <= w < 2^64 ->
    implM bgusegs (interp (embed (BN_set_word (tree_ops bptr) rx w bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = wz 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW')))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_SET_WORD) fc None m (seg_rom bgusegs)).
  Proof.
    intros until w. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> HAx WRx -> -> HW. pose proof (proj1 WRx) as NROx.
    unfold BN_SET_WORD_STACK, BN_EXPAND2_STACK, BN_SET_WORD, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    change (2 ^ 64) with 18446744073709551616 in HW.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    destruct (lib_state_open [] bs m OW PL EA rx ax LS ND HAx ltac:(intros []) NROx) as ((Dx & BNx & ARRx) & (OKx1 & OKx2 & OKx3 & OKx4) & _).
    set (bx := getbn rx bs) in *.
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAx NROx) as (XA0 & XAC & XAI).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HAx) as HVx.
    unfold bn_cells in BNx. unfold BG_DMAX in OKx3.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    unfold BN_set_word, bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
    unfold implM. iprefix.
    assert (ALX : 0 < ax /\ ax mod 8 = 0) by (eapply ref_at_ualign; eassumption). destruct ALX as (AX0 & AX8).
    carve_frame 32%nat ST. do 6 step. ub_chk. step. step. ub_chk. step.
    step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (bn_dmax bx))) by lia.
    assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -32, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -32, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).

    assert (FIN : forall (st1 : PState) (bs1 : bstate bptr) (m2 : mem) (OW2 : list block) (errv2 : word)
                         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      RHEAP st1 (OW2 ++ LB) m2 -> lib_state bs1 m2 OW2 PL EA -> rauxv_ok m2 B -> stk bgusegs m2 lo (bv_unsigned sp + -32) ->
      rw_cells bgusegs m2 3346164 [C4 errv2] -> mem_inv bgusegs m2 -> lx_pres LB (bv_unsigned sp) (XW PL) m m2 ->
      ps_fa st1 = ps_fa s -> ps_so st1 = ps_so s -> refs_stable bs OW bs1 OW2 ->
      (1 <= bn_dmax (getbn rx bs1))%nat ->
      (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW2) ->
      rw_cells bgusegs m2 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
      implM bgusegs (interp (embed (TRet (tt, setbn rx (set_word_bn (getbn rx bs1) w) bs1)))) st1
        (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
                 (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = Z_to_bv 64 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW')))
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 RATP) x5 x6 x7 sp (Z_to_bv 64 ax) x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 w) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0xfe528) fc None m2 (seg_rom bgusegs))).
    { intros st1 bs1 m2 OW2 errv2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
             HEAP2 LS2 AUX2 ST2 ERR2 MI2 LXP2 FA2 SO2 RST2 HDM BST FR2.
      clear BNx ARRx MU WM ST ERR MI FR HWL WOK.
      assert (FROK2 : frames_ok PL (bv_unsigned sp) B) by exact FROK.
      pose proof (ref_at_stable _ _ _ _ _ _ _ RST2 HAx) as HAx2.
      pose proof (RH_nodup_l _ _ _ _ HEAP2) as ND2.
      pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as PARTS2; pose proof PARTS2 as (WFS2 & PWF2 & IDS2 & PLB2 & ERRB2).
      pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HAx2) as HVx2.
      destruct (lib_state_open [] bs1 m2 OW2 PL EA rx ax LS2 ND2 HAx2 ltac:(intros []) NROx) as ((Dr & BNr & ARRr) & (OKq1 & OKq2 & OKq3 & OKq4) & LSH).
      destruct (bn_arr_facts st1 OW2 LB m2 HEAP2 bs1 PL EA _ _ PARTS2 FROK2 rx Dr HVx2 ltac:(assumption) ARRr) as (Ur & LENr & Dr0 & DrC & DrI & DSEPr).
      set (br := getbn rx bs1) in *.
      pose proof (DSEPr rx ax HAx2) as SEPrr.
      pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROK2 HAx2 NROx) as (XB0 & XBC & XBI).
      unfold bn_cells in BNr. unfold BG_DMAX in OKq3.
      cbn [embed interp]. apply implM_ret.
      unfold MallocRep.wz in *.

      assert (HDr : exists pr, bn_d br = Some pr /\ In (pr, Dr, 8 * Z.of_nat (bn_dmax br)) OW2).
      { pose proof ARRr as ARRr'. unfold bn_arr in ARRr'. destruct (bn_d br) as [pr|] eqn:Edr0; [exists pr; split; [reflexivity| exact (proj1 ARRr')]|].
        exfalso. destruct (bn_arr_null PL rx m2 OW2 Dr br PWF2 WRx Edr0 ARRr) as [_ E]. unfold bn_dmax in HDM. rewrite E in HDM. cbn in HDM. lia. }
      destruct HDr as (pr & Edr & Hinpr).
      assert (LBR : length (bn_buf br) = bn_dmax br) by reflexivity.
      pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp); (ax, ax + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m2) as MU3.
      pose proof (wmono_refl bgusegs m2) as WM3.

      assert (ALD : 0 < Dr /\ Dr mod 8 = 0) by (eapply block_ualign; [exact HEAP2| exact Hinpr]). destruct ALD as (DR0 & DR8).
      step. step. ub_chk. step. ub_chk.

      assert (IDX : 0 <= 0 < Z.of_nat (length (wlimbs (bn_buf br)))) by (rewrite wlimbs_len, LBR; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (u64arr_store_ok bgusegs mx Dr _ 0 (wa (Dr + 8 * 0)) ltac:(eassumption) IDX eq_refl) as SOKW;
        pose proof (u64arr_write bgusegs mx Dr _ 0 (Z_to_bv 64 w) ltac:(eassumption) IDX) as U2 end.
      replace (Dr + 8 * 0) with Dr in SOKW, U2 by lia. rewrite Nat2Z.id in U2 || change (Z.to_nat 0) with 0%nat in U2.
      clear Ur. step. store_done. step. step.
      rewrite v_sltu_b2z, !unsigned_lit in BNr by lia.
      assert (ETOP : Z.b2z (0 <? w) = Z.of_nat (if w =? 0 then 0%nat else 1%nat)).
      { destruct (Z.ltb_spec 0 w); destruct (Z.eqb_spec w 0); cbn; lia. }
      rewrite ETOP in BNr.
      step. do 4 step. release_frame FR2 ST2 (bv_unsigned sp). step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mG end.
      apply evt_done.
      set (nb := upd (bn_buf br) 0 w).
      assert (Lnb : length nb = bn_dmax br) by (subst nb; rewrite upd_length by lia; exact LBR).
      assert (LMnb : limbs nb) by (subst nb; apply upd_limbs; [exact OKq1| unfold limb, BW; exact HW]).
      assert (UF : u64arr bgusegs mG Dr (wlimbs nb)).
      { subst nb. lazymatch goal with U : u64arr bgusegs mG Dr ?l |- _ => replace (wlimbs (upd (bn_buf br) 0 w)) with l; [exact U|] end.
        unfold upd, splice, wlimbs. cbn [firstn app length Nat.add]. destruct (bn_buf br) as [|b0 bt] eqn:Ebuf; [cbn in LBR; lia|].
        cbn [skipn map Arr.upd Z.to_nat]. reflexivity. }
      assert (HWL3 : Forall (w_lib bs1 OW2 PL lo (bv_unsigned sp)) [(bv_unsigned sp + -32, bv_unsigned sp); (ax, ax + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
      { constructor; [left; cbn; lia|]. constructor; [right; right; exists rx, ax; split; [exact HAx2|]; split; [exact NROx|]; cbn; lia|].
        constructor; [| constructor]. right; left; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn; split; [exact Hinpr| clear; lia]. }
      assert (WOK3 : Forall (w_ok OW2 LB bs1 PL EA (bv_unsigned sp) [rx]) [(bv_unsigned sp + -32, bv_unsigned sp); (ax, ax + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
      { constructor; [apply w_stack; cbn; lia|]. constructor; [eapply (w_struct OW2 LB bs1 PL EA (bv_unsigned sp) false [rx] _ rx ax); [left; reflexivity| exact HAx2| assumption| cbn; lia| cbn; lia]|].
        constructor; [| constructor].
        eapply (w_limbs OW2 LB bs1 PL EA (bv_unsigned sp) false [rx] _ rx pr Dr); [left; reflexivity| exact HVx2| exact Edr| exact Hinpr| cbn [fst snd]; fold br; clear; lia| cbn [fst snd]; fold br; clear; lia]. }
      unfold bn_post. do 15 eexists. exists mG, OW2, PL, errv2. split; [reflexivity|]. cbn [fst snd].
      split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROK2 MU3 WM3 HWL3 CEIL)|].
      split.
      { unfold lib_state. eapply (lib_state_close [] bs1 mG OW2 PL EA rx ax); [| exact ND2| exact HAx2| exact NROx| | |].
        - exact (lib_state_frame st1 LB _ _ [rx] bs1 m2 mG OW2 PL EA _ HEAP2 LSH MU3 WM3 FROK WOK3).
        - exists Dr. split.
          + unfold bn_cells, bn_dmax, set_word_bn. cbn [bn_top bn_buf bn_neg bn_flags bn_d Z.b2z]. fold nb. rewrite Lnb. exact BNr.
          + unfold bn_arr, bn_dmax, set_word_bn. cbn [bn_d bn_buf]. fold nb. rewrite Edr, Lnb. split; [exact Hinpr| exact UF].
        - unfold bg_ok, bn_dmax, set_word_bn. cbn [bn_buf bn_top bn_flags]. fold nb. rewrite Lnb. unfold BG_DMAX in *.
          split; [exact LMnb|]. split; [destruct (w =? 0); lia|]. split; [clear - OKq3; unfold bn_dmax in *; lia| exact OKq4].
        - apply ids_ok_setbn_same; [exact IDS2| exact HVx2|]. unfold bn_blocks, bn_dmax, set_word_bn. cbn [bn_d bn_buf]. fold nb. rewrite Lnb. reflexivity. }
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROK2 AUX2 MU3 WM3 HWL3 SPB ltac:(lia)); unfold GLOBALS_TOP; lia|]. split; [assumption|].
      split; [unfold LX_ERRNO, RATP; assumption|]. split; [assumption|].
      split. { eapply lx_pres_trans; [exact LXP2|]. apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROK2 MU3 WM3 HWL3 CEIL); unfold GLOBALS_TOP; lia. }
      split; [exact FA2|]. split; [exact SO2|].
      split. { eapply refs_stable_trans; [exact RST2| apply refs_stable_setbn]. }
      split; [reflexivity|]. split; [reflexivity| exact BST]. }
    step. if_cases KD; zify_cond KD.
    -
      assert (HD1 : (1 <= bn_dmax bx)%nat) by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      ihere. to_implM. unfold bn_wexpand, bbind, bget, bret, bset. cbn [bind ret tree_ops tbind fst snd]. fold bx.
      replace (1 <=? bn_dmax bx)%nat with true by (symmetry; apply Nat.leb_le; lia).
      cbn [tbind fst snd].
      eapply (FIN s bs m1 OW errv);
        [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)
        | exact (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK)
        | apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); unfold GLOBALS_TOP; lia
        | exact ST | exact ERR | exact MI
        | apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); unfold GLOBALS_TOP; lia
        | reflexivity | reflexivity | apply refs_stable_refl | fold bx; exact HD1
        | intros q0 A0 n0 Hq0 _; exact Hq0 | exact FR].
    -
      assert (HD0 : bn_dmax bx = 0%nat) by (apply andb_false_iff in KD; destruct KD as [KD|KD]; apply Z.ltb_ge in KD; lia). clear KD.
      step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
      pose proof (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL) as HEAP1.
      pose proof (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
      assert (AUX1 : rauxv_ok m1 B) by (apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); unfold GLOBALS_TOP; lia).
      assert (LXP1 : lx_pres LB (bv_unsigned sp) (XW PL) m m1) by (apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); unfold GLOBALS_TOP; lia).
      ihere. to_implM.
      eapply implM_embed_bind.
      { eapply (bn_expand2_walk HM HF) with (lo := lo) (B := B) (errv := errv) (r := rx) (a := ax) (OW := OW) (LB := LB) (PL := PL) (EA := EA) (words := 1%nat);
          [| reflexivity | exact HAx | exact WRx | reflexivity | reflexivity | cbn; lia].
        unfold bn_pre. rewrite ESP.
        split; [exact HEAP1|]. split; [exact LS1|]. split; [eapply frames_ok_call; [exact FROK| exact CEIL| lia| lia]|]. split; [exact AUX1|]. split; [lia|]. split; [exact B63|].
        split; [exact ST|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; lia|]. split; [unfold BN_EXPAND2_STACK; lia|].
        split; [unfold LX_ERRNO, RATP; exact ERR| exact MI]. }
      cbv beta. intros [u bs1] st1 ms1 PO. unfold bn_post in PO. cbn [fst snd] in *.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & OW2 & PL2 & errv2 & -> & HEAP2 & LS2 & AUX2 & ST2 & ERR2
                      & MI2 & LXP2 & FA2 & SO2 & RST2 & -> & -> & HDM & WRES & BST).
      rewrite ESP in *.
      replace (ret_pc (Z_to_bv 64 1041700)) with (Z_to_bv 64 1041700) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (FR2 : rw_cells bgusegs m2 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply rw_cells_agree; [apply agree_of_lx_pres; exact LXP2 | exact FR |].
        intros a Ha. cbn in Ha. eapply (xw_client PL LB _ (bv_unsigned sp) B); [exact (proj1 FROK)| lia|].
        unfold LIBW_bgr, BnRep.LIBW_bn, CONST_ONE, BN_STRUCT_SZ. cbn [rin_ivs app fst snd]. lia. }
      unfold implM. iprefix.
      step. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by lia; lia|]. clear KZ.
      ihere. to_implM. cbn [ret tree_ops].
      eapply (FIN st1 bs1 m2 OW2 errv2);
        [exact HEAP2 | exact LS2 | exact AUX2 | exact ST2 | unfold LX_ERRNO, RATP in ERR2; exact ERR2 | exact MI2
        | eapply lx_pres_trans; [exact LXP1|]; eapply lx_pres_weaken; [exact LXP2| lia | intros b0 Hb0; exact Hb0 | intros a0 Ha0; exact Ha0]
        | congruence | congruence | exact RST2 | exact HDM | exact BST | exact FR2].
  Qed.
End Proofs.
End WithCeiling0.
