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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnArith BnMem BnTac BnTacX.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_crypto.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep BnLeaves BnAssoc.
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

Definition BN_SET_BIT : Z := 0xff0e8.
Definition BN_SET_BIT_STACK : Z := 48 + BN_EXPAND2_STACK.

Definition set_bit_ext (b : bignum bptr) (i : nat) : bignum bptr :=
  mkBN (bn_d b) (splice (bn_buf b) (bn_top b) (repeat 0 (i + 1 - bn_top b))) (i + 1) (bn_neg b) (bn_flags b).
Definition set_bit_bn (b : bignum bptr) (i : nat) (j : Z) : bignum bptr :=
  bn_with_buf b (upd (bn_buf b) i (Z.lor (nth i (bn_buf b) 0) (2 ^ j))).

Lemma wlimbs_nth : forall buf (i : nat), (i < length buf)%nat -> nth_error (wlimbs buf) (Z.to_nat (Z.of_nat i)) = Some (Z_to_bv 64 (nth i buf 0)).
Proof. intros buf i H. rewrite Nat2Z.id. unfold wlimbs. rewrite nth_error_map. rewrite (nth_error_nth' buf 0) by lia. reflexivity. Qed.

Lemma wlimbs_upd : forall l (i : nat) v, (i < length l)%nat -> Arr.upd (wlimbs l) i (Z_to_bv 64 v) = wlimbs (upd l i v).
Proof.
  induction l as [|y l IH]; intros i v H; cbn [length] in H; [lia|].
  destruct i as [|i']; [reflexivity|].
  unfold wlimbs in *. cbn [map Arr.upd]. rewrite (IH i' v) by lia.
  unfold upd, splice. cbn [firstn length Nat.add skipn app map]. reflexivity.
Qed.

Lemma upd_splice_zero : forall l t j, (t + j < length l)%nat ->
  upd (splice l t (repeat 0%Z j)) (t + j) 0%Z = splice l t (repeat 0%Z (S j)).
Proof.
  intros l t j H. unfold upd, splice. rewrite !repeat_length. cbn [length].
  assert (EX : firstn t l ++ repeat 0%Z j ++ skipn (t + j) l = (firstn t l ++ repeat 0%Z j) ++ skipn (t + j) l) by apply app_assoc.
  rewrite EX. clear EX.
  assert (LA : length (firstn t l ++ repeat 0%Z j) = (t + j)%nat) by (rewrite length_app, length_firstn, repeat_length; lia).
  rewrite firstn_app, LA, firstn_all2 by lia. rewrite Nat.sub_diag. cbn [firstn]. rewrite app_nil_r.
  rewrite skipn_app, LA, skipn_all2 by lia. cbn [app]. replace (t + j + 1 - (t + j))%nat with 1%nat by lia.
  rewrite skipn_skipn. replace (1 + (t + j))%nat with (t + S j)%nat by lia.
  rewrite <- !app_assoc. f_equal. replace (S j) with (j + 1)%nat by lia. rewrite repeat_app. rewrite <- app_assoc. reflexivity.
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma BN_set_bit_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rx : bnref) (ax n : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_SET_BIT_STACK -> tp = wz RATP ->
    ref_at bs OW PL rx ax -> wref PL rx -> a0 = wz ax -> a1 = Z_to_bv 64 n -> -2^31 <= n < 2^31 ->
    implM bgusegs (interp (embed (BN_set_bit (tree_ops bptr) rx n bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = wz 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW')))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_SET_BIT) fc None m (seg_rom bgusegs)).
  Proof.
    intros until n. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> HAx WRx -> -> HN. pose proof (proj1 WRx) as NROx.
    unfold BN_SET_BIT_STACK, BN_EXPAND2_STACK, BN_SET_BIT, GLOBALS_TOP, MallocRep.wz in *.
    change (2 ^ 31) with 2147483648 in HN.

    destruct (Z.ltb_spec n 0) as [NNEG|NNEG].
    { unfold BN_set_bit. replace (n <? 0) with true by (symmetry; apply Z.ltb_lt; exact NNEG). unfold bunr. cbn [unreachable tree_ops embed]. apply implM_interp_unr. }
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    destruct (lib_state_open [] bs m OW PL EA rx ax LS ND HAx ltac:(intros []) NROx) as ((Dx & BNx & ARRx) & (OKx1 & OKx2 & OKx3 & OKx4) & _).
    set (bx := getbn rx bs) in *.
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAx NROx) as (XA0 & XAC & XAI).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HAx) as HVx.
    unfold bn_cells in BNx. unfold BG_DMAX in OKx3.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    set (i := Z.to_nat (n / 64)). set (j := n mod 64).
    assert (Ei : n / 64 = Z.of_nat i) by (subst i; Z.div_mod_to_equations; lia).
    assert (HI : 0 <= Z.of_nat i <= n) by (Z.div_mod_to_equations; lia).
    assert (HJ : 0 <= j < 64) by (subst j; Z.div_mod_to_equations; lia).
    unfold BN_set_bit. replace (n <? 0) with false by (symmetry; apply Z.ltb_ge; exact NNEG).
    cbv zeta. fold i j. unfold bbind, bget, bset, bret. cbn [bind ret tree_ops tbind fst snd]. fold bx.
    unfold implM. iprefix.
    assert (ALX : 0 < ax /\ ax mod 8 = 0) by (eapply ref_at_ualign; eassumption). destruct ALX as (AX0 & AX8).
    carve_frame 48%nat ST. do 8 step.
    step. rewrite lts_signed by lia. if_cases KN; zify_cond KN; [exfalso; lia|]. clear KN.
    step. ub_chk. step. ub_chk. step.
    step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (bn_top bx))) by lia.
    step. setreg 20%Z (Z_to_bv 64 (Z.of_nat i))
            ltac:(rewrite <- Ei; f_equal; rewrite (unsigned_lit n) by lia; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 32)%Z with 4294967296%Z;
                  rewrite (Z.mod_small n 4294967296) by lia; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 6) with 64;
                  symmetry; apply bn_swrap32_small; Z.div_mod_to_equations; lia).
    assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).

    assert (FIN : forall (st1 : PState) (bs1 : bstate bptr) (m2 : mem) (OW2 : list block) (errv2 : word)
                         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word),
      RHEAP st1 (OW2 ++ LB) m2 -> lib_state bs1 m2 OW2 PL EA -> rauxv_ok m2 B -> stk bgusegs m2 lo (bv_unsigned sp + -48) ->
      rw_cells bgusegs m2 3346164 [C4 errv2] -> mem_inv bgusegs m2 -> lx_pres LB (bv_unsigned sp) (XW PL) m m2 ->
      ps_fa st1 = ps_fa s -> ps_so st1 = ps_so s -> refs_stable bs OW bs1 OW2 ->
      (i < bn_top (getbn rx bs1))%nat ->
      (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW2) ->
      rw_cells bgusegs m2 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      implM bgusegs (interp (embed (TRet (tt, setbn rx (set_bit_bn (getbn rx bs1) i j) bs1)))) st1
        (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
                 (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = Z_to_bv 64 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW')))
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 RATP) x5 x6 x7 sp (Z_to_bv 64 n) x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 ax) x19 (Z_to_bv 64 (Z.of_nat i)) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0xff1a4) fc None m2 (seg_rom bgusegs))).
    { intros st1 bs1 m2 OW2 errv2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31
             HEAP2 LS2 AUX2 ST2 ERR2 MI2 LXP2 FA2 SO2 RST2 HIT BST FR2.
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
        exfalso. destruct (bn_arr_null PL rx m2 OW2 Dr br PWF2 WRx Edr0 ARRr) as [_ E]. unfold bn_dmax in OKq2. rewrite E in OKq2. cbn in OKq2. lia. }
      destruct HDr as (pr & Edr & Hinpr).
      assert (LBR : length (bn_buf br) = bn_dmax br) by reflexivity.
      pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m2) as MU3.
      pose proof (wmono_refl bgusegs m2) as WM3.

      step. step. step. setreg 10%Z (Z_to_bv 64 (Dr + 8 * Z.of_nat i)) ltac:(f_equal; rewrite (unsigned_lit (Z.of_nat i)) by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
      assert (ALD : 0 < Dr /\ Dr mod 8 = 0) by (eapply block_ualign; [exact HEAP2| exact Hinpr]). destruct ALD as (DR0 & DR8).
      pose proof alloc_ceiling_range as ACR.
      ub_chk. step. step. step. ub_chk. ub_chk. step. ub_chk.
      assert (NTH : nth_error (wlimbs (bn_buf br)) (Z.to_nat (Z.of_nat i)) = Some (Z_to_bv 64 (nth i (bn_buf br) 0))) by (apply wlimbs_nth; unfold bn_dmax in OKq2; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (u64arr_read bgusegs mx Dr (wlimbs (bn_buf br)) (Z.of_nat i) (Z_to_bv 64 (nth i (bn_buf br) 0)) (wa (Dr + 8 * Z.of_nat i)) Ur NTH ltac:(lia) eq_refl) as RD end.
      step. clear RD.
      pose proof (limbs_nth (bn_buf br) i OKq1) as LN. unfold limb in LN. rewrite BnArith.BW_lit in LN.
      set (x := nth i (bn_buf br) 0) in *.

      step. step. step. step.
      assert (P2J : 0 < 2 ^ j < 18446744073709551616) by (split; [apply Z.pow_pos_nonneg; lia|]; change 18446744073709551616 with (2 ^ 64); apply Z.pow_lt_mono_r; lia).
      setreg 11%Z (Z_to_bv 64 (Z.lor x (2 ^ j)))
              ltac:(f_equal; rewrite (unsigned_lit n) by lia; replace (Z.land n 63) with j by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; reflexivity);
                    rewrite (unsigned_lit j) by lia; rewrite (Z.mod_small j 64) by lia; rewrite Z.shiftl_1_l, (unsigned_lit (2 ^ j)) by lia;
                    rewrite (unsigned_lit x) by lia; reflexivity).
      assert (LOR : 0 <= Z.lor x (2 ^ j) < 18446744073709551616) by (apply (ZBridge.zr_lor x (2 ^ j)); unfold ZBridge.inr64; lia).
      assert (IDX : 0 <= Z.of_nat i < Z.of_nat (length (wlimbs (bn_buf br)))) by (rewrite wlimbs_len, LBR; unfold bn_dmax in OKq2; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (u64arr_store_ok bgusegs mx Dr _ (Z.of_nat i) (wa (Dr + 8 * Z.of_nat i)) Ur IDX eq_refl) as SOKW;
        pose proof (u64arr_write bgusegs mx Dr _ (Z.of_nat i) (Z_to_bv 64 (Z.lor x (2 ^ j))) Ur IDX) as U2 end.
      rewrite Nat2Z.id, (wlimbs_upd (bn_buf br) i) in U2 by (rewrite LBR; unfold bn_dmax in OKq2; lia).
      clear Ur. step. store_done. step. step.

      do 6 step. release_frame FR2 ST2 (bv_unsigned sp). step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mG end.
      apply evt_done.
      set (nb := upd (bn_buf br) i (Z.lor x (2 ^ j))) in *.
      assert (Lnb : length nb = bn_dmax br) by (subst nb; rewrite upd_length by (rewrite LBR; unfold bn_dmax in OKq2; lia); exact LBR).
      assert (LMnb : limbs nb) by (subst nb; apply upd_limbs; [exact OKq1| unfold limb; rewrite BnArith.BW_lit; exact LOR]).
      assert (HWL3 : Forall (w_lib bs1 OW2 PL lo (bv_unsigned sp)) [(bv_unsigned sp + -48, bv_unsigned sp); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
      { constructor; [left; cbn; lia|]. constructor; [| constructor]. right; left; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn; split; [exact Hinpr| clear; lia]. }
      assert (WOK3 : Forall (w_ok OW2 LB bs1 PL EA (bv_unsigned sp) [rx]) [(bv_unsigned sp + -48, bv_unsigned sp); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
      { constructor; [apply w_stack; cbn; lia|]. constructor; [| constructor].
        eapply (w_limbs OW2 LB bs1 PL EA (bv_unsigned sp) false [rx] _ rx pr Dr); [left; reflexivity| exact HVx2| exact Edr| exact Hinpr| cbn [fst snd]; fold br; clear; lia| cbn [fst snd]; fold br; clear; lia]. }
      unfold bn_post. do 15 eexists. exists mG, OW2, PL, errv2. split; [reflexivity|]. cbn [fst snd].
      split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROK2 MU3 WM3 HWL3 CEIL)|].
      split.
      { unfold lib_state. eapply (lib_state_close [] bs1 mG OW2 PL EA rx ax); [| exact ND2| exact HAx2| exact NROx| | |].
        - exact (lib_state_frame st1 LB _ _ [rx] bs1 m2 mG OW2 PL EA _ HEAP2 LSH MU3 WM3 FROK WOK3).
        - exists Dr. split.
          + unfold bn_cells, bn_dmax, set_bit_bn, bn_with_buf. cbn [bn_top bn_buf bn_neg bn_flags bn_d]. fold nb. rewrite Lnb. exact BNr.
          + unfold bn_arr, bn_dmax, set_bit_bn, bn_with_buf. cbn [bn_d bn_buf]. fold nb. rewrite Edr, Lnb. split; [exact Hinpr| exact U2].
        - unfold bg_ok, bn_dmax, set_bit_bn, bn_with_buf. cbn [bn_buf bn_top bn_flags]. fold nb. rewrite Lnb. unfold BG_DMAX in *.
          split; [exact LMnb|]. split; [exact OKq2|]. split; [clear - OKq3; unfold bn_dmax in *; lia| exact OKq4].
        - apply ids_ok_setbn_same; [exact IDS2| exact HVx2|]. unfold bn_blocks, bn_dmax, set_bit_bn, bn_with_buf. cbn [bn_d bn_buf]. fold nb. rewrite Lnb. reflexivity. }
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROK2 AUX2 MU3 WM3 HWL3 SPB ltac:(lia)); unfold GLOBALS_TOP; lia|]. split; [assumption|].
      split; [unfold LX_ERRNO, RATP; assumption|]. split; [assumption|].
      split. { eapply lx_pres_trans; [exact LXP2|]. apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROK2 MU3 WM3 HWL3 CEIL); unfold GLOBALS_TOP; lia. }
      split; [exact FA2|]. split; [exact SO2|].
      split. { eapply refs_stable_trans; [exact RST2| apply refs_stable_setbn]. }
      split; [reflexivity|]. split; [reflexivity| exact BST]. }

    assert (MID : forall (st1 : PState) (bs1 : bstate bptr) (m2 : mem) (OW2 : list block) (errv2 : word)
                         (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      RHEAP st1 (OW2 ++ LB) m2 -> lib_state bs1 m2 OW2 PL EA -> rauxv_ok m2 B -> stk bgusegs m2 lo (bv_unsigned sp + -48) ->
      rw_cells bgusegs m2 3346164 [C4 errv2] -> mem_inv bgusegs m2 -> lx_pres LB (bv_unsigned sp) (XW PL) m m2 ->
      ps_fa st1 = ps_fa s -> ps_so st1 = ps_so s -> refs_stable bs OW bs1 OW2 ->
      (bn_top (getbn rx bs1) <= i)%nat -> (i + 1 <= bn_dmax (getbn rx bs1))%nat ->
      (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW2) ->
      rw_cells bgusegs m2 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      implM bgusegs (interp (embed (TRet (tt, setbn rx (set_bit_bn (getbn rx (setbn rx (set_bit_ext (getbn rx bs1) i) bs1)) i j)
                                                   (setbn rx (set_bit_ext (getbn rx bs1) i) bs1))))) st1
        (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
                 (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = Z_to_bv 64 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW')))
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 RATP) x5 x6 x7 sp (Z_to_bv 64 n) (Z_to_bv 64 (Z.of_nat (bn_top (getbn rx bs1)))) x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 ax) (Z_to_bv 64 (Z.of_nat i + 1)) (Z_to_bv 64 (Z.of_nat i)) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0xff14c) fc None m2 (seg_rom bgusegs))).
    { intros st1 bs1 m2 OW2 errv2 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
             HEAP2 LS2 AUX2 ST2 ERR2 MI2 LXP2 FA2 SO2 RST2 HTI HID BST FR2.
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
      unfold implM. iprefix.
      unfold MallocRep.wz in *.

      assert (HDr : exists pr, bn_d br = Some pr /\ In (pr, Dr, 8 * Z.of_nat (bn_dmax br)) OW2).
      { pose proof ARRr as ARRr'. unfold bn_arr in ARRr'. destruct (bn_d br) as [pr|] eqn:Edr0; [exists pr; split; [reflexivity| exact (proj1 ARRr')]|].
        exfalso. destruct (bn_arr_null PL rx m2 OW2 Dr br PWF2 WRx Edr0 ARRr) as [_ E]. unfold bn_dmax in HID. rewrite E in HID. cbn in HID. lia. }
      destruct HDr as (pr & Edr & Hinpr).
      assert (LBR : length (bn_buf br) = bn_dmax br) by reflexivity.
      pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (ax, ax + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m2) as MU3.
      pose proof (wmono_refl bgusegs m2) as WM3.
      step. rewrite lts_signed by lia. if_cases KT; zify_cond KT; [exfalso; lia|]. clear KT.
      assert (ALD : 0 < Dr /\ Dr mod 8 = 0) by (eapply block_ualign; [exact HEAP2| exact Hinpr]). destruct ALD as (DR0 & DR8).
      pose proof alloc_ceiling_range as ACR.
      step. step. step.
      setreg 12%Z (Z_to_bv 64 (Dr + 8 * Z.of_nat (bn_top br))) ltac:(f_equal; rewrite (unsigned_lit (Z.of_nat (bn_top br))) by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
      step. step.
      setreg 13%Z (Z_to_bv 64 1) ltac:(rewrite v_sltu_b2z, !unsigned_lit by lia; replace (0 <? Dr) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
      set (cnt := (i + 1 - bn_top br)%nat).
      assert (Ecnt : Z.of_nat cnt = Z.of_nat i + 1 - Z.of_nat (bn_top br)) by lia.
      set (nb := splice (bn_buf br) (bn_top br) (repeat 0 cnt)).
      lazymatch type of BNr with rw_cells _ _ ?BA ?CB0 =>
      lazymatch type of FR2 with rw_cells _ _ ?FA ?FC =>
      lazymatch type of ERR2 with rw_cells _ _ ?EAd ?EC =>
      lazymatch type of MU3 with munch ?ML _ _ =>
        pose (MF := fun mk : mem => rw_cells bgusegs mk BA CB0 /\ rw_cells bgusegs mk FA FC /\ stk bgusegs mk lo (bv_unsigned sp + -48)
                    /\ rw_cells bgusegs mk EAd EC /\ mem_inv bgusegs mk /\ munch ML m2 mk /\ wmono bgusegs m2 mk)
      end end end end.
      assert (MF0 : MF m2) by exact (conj BNr (conj FR2 (conj ST2 (conj ERR2 (conj MI2 (conj MU3 WM3)))))).
      lazymatch goal with |- evt _ ?Q _ => pose (POST := Q) end.
      pose (HEAD := fun (k : nat) (mk : mem) (y15 y16 : word) =>
        MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 RATP) x5 x6 x7 sp (Z_to_bv 64 n)
                (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 Dr) (Z_to_bv 64 (Dr + 8 * Z.of_nat k)) (Z_to_bv 64 1) (Z_to_bv 64 (Dr + 8 * Z.of_nat k)) y15 y16 x17
                (Z_to_bv 64 ax) (Z_to_bv 64 (Z.of_nat i + 1)) (Z_to_bv 64 (Z.of_nat i)) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
           F (Z_to_bv 64
              0xff164) fc None mk (seg_rom bgusegs)).
      pose (HEADX := fun (k : nat) (mk : mem) (y15 y16 : word) =>
        MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 RATP) x5 x6 x7 sp (Z_to_bv 64 n)
                (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 Dr) (Z_to_bv 64 (Dr + 8 * Z.of_nat k)) (Z_to_bv 64 1) (Z_to_bv 64 (Dr + 8 * Z.of_nat k)) y15 y16 x17
                (Z_to_bv 64 ax) (Z_to_bv 64 (Z.of_nat i + 1)) (Z_to_bv 64 (Z.of_nat i)) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
           F (Z_to_bv 64
              0xff1a0) fc None mk (seg_rom bgusegs)).
      assert (ROUND : forall (zk : nat) (mk : mem) (y15 y16 : word), (bn_top br + zk < i + 1)%nat ->
          u64arr bgusegs mk Dr (wlimbs (splice (bn_buf br) (bn_top br) (repeat 0 zk))) -> MF mk ->
          ((bn_top br + S zk = i + 1)%nat -> forall (mk' : mem) (z15 z16 : word), u64arr bgusegs mk' Dr (wlimbs (splice (bn_buf br) (bn_top br) (repeat 0 (S zk)))) -> MF mk' ->
               evt bgusegs POST (HEADX (bn_top br + S zk)%nat mk' z15 z16)) ->
          ((bn_top br + S zk < i + 1)%nat -> forall (mk' : mem) (z15 z16 : word), u64arr bgusegs mk' Dr (wlimbs (splice (bn_buf br) (bn_top br) (repeat 0 (S zk)))) -> MF mk' ->
               evt bgusegs POST (HEAD (bn_top br + S zk)%nat mk' z15 z16)) ->
          evt bgusegs POST (HEAD (bn_top br + zk)%nat mk y15 y16)).
      { intros zk mk y15 y16 Hj U (BNk & FRk & STk & ERk & MIk & MUk & WMk) KE KL. unfold HEAD.
        clear MF0.
        step. ub_chk. step. step. step. step. ub_chk. ub_chk. step. ub_chk.
        assert (IDX : 0 <= Z.of_nat (bn_top br + zk) < Z.of_nat (length (wlimbs (splice (bn_buf br) (bn_top br) (repeat 0 zk))))).
        { rewrite wlimbs_len, splice_length by (rewrite repeat_length; lia). lia. }
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          pose proof (u64arr_store_ok bgusegs mx Dr _ (Z.of_nat (bn_top br + zk)) (wa (Dr + 8 * Z.of_nat (bn_top br + zk))) U IDX eq_refl) as SOKW;
          pose proof (u64arr_write bgusegs mx Dr _ (Z.of_nat (bn_top br + zk)) (Z_to_bv 64 0) U IDX) as U2 end.
        rewrite Nat2Z.id, (wlimbs_upd _ (bn_top br + zk)), upd_splice_zero in U2 by (rewrite ?splice_length; rewrite ?repeat_length; lia).
        clear U. step. try change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)). store_done.
        step. step. step.
        setreg 10%Z (Z_to_bv 64 (Z.of_nat (bn_top br + S zk)))
               ltac:(f_equal; rewrite (unsigned_lit (Z.of_nat (bn_top br + zk))) by lia; rewrite bn_swrap32_small by lia; lia).
        setreg 12%Z (Z_to_bv 64 (Dr + 8 * Z.of_nat (bn_top br + S zk))) ltac:(f_equal; lia).
        setreg 14%Z (Z_to_bv 64 (Dr + 8 * Z.of_nat (bn_top br + S zk))) ltac:(f_equal; lia).
        step. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia.
        - eapply KL; [lia | exact U2 | exact (conj BNk (conj FRk (conj STk (conj ERk (conj MIk (conj MUk WMk))))))].
        - eapply KE; [lia | exact U2 | exact (conj BNk (conj FRk (conj STk (conj ERk (conj MIk (conj MUk WMk))))))]. }
      assert (LOOP : forall (c zk : nat) (mk : mem) (y15 y16 : word), (bn_top br + zk + S c = i + 1)%nat ->
          u64arr bgusegs mk Dr (wlimbs (splice (bn_buf br) (bn_top br) (repeat 0 zk))) -> MF mk ->
          (forall (mk' : mem) (z15 z16 : word), u64arr bgusegs mk' Dr (wlimbs nb) -> MF mk' -> evt bgusegs POST (HEADX (i + 1)%nat mk' z15 z16)) ->
          evt bgusegs POST (HEAD (bn_top br + zk)%nat mk y15 y16)).
      { induction c as [|c IH]; intros zk mk y15 y16 Hc U M K.
        - eapply ROUND; [lia | exact U | exact M | | intros C; exfalso; lia].
          intros E mk' z15 z16 U' M'. replace (bn_top br + S zk)%nat with (i + 1)%nat by lia.
          apply K; [| exact M']. unfold nb, cnt. replace (i + 1 - bn_top br)%nat with (S zk) by lia. exact U'.
        - eapply ROUND; [lia | exact U | exact M | intros C; exfalso; lia | ].
          intros _ mk' z15 z16 U' M'. eapply IH; [lia | exact U' | exact M' | exact K]. }
      cut (forall (mk' : mem) (z15 z16 : word), u64arr bgusegs mk' Dr (wlimbs nb) -> MF mk' -> evt bgusegs POST (HEADX (i + 1)%nat mk' z15 z16)).
      { intros KX. pose proof (LOOP (cnt - 1)%nat 0%nat m2 x15 x16) as L0. rewrite Nat.add_0_r in L0. apply L0; [lia | | exact MF0 | exact KX].
        cbn [repeat]. unfold splice. cbn [app length]. rewrite Nat.add_0_r, firstn_skipn. exact Ur. }
      intros m4' z15 z16 UF (BNr' & FR2' & ST2' & ERR2' & MI4 & MU3' & WM3'). unfold HEADX, POST.
      clear BNr FR2 ST2 ERR2 MU3 WM3 Ur ROUND LOOP MF0.
      rename BNr' into BNr, FR2' into FR2, ST2' into ST2, ERR2' into ERR2, MU3' into MU3, WM3' into WM3.
      assert (LUF : Z.of_nat (length (wlimbs nb)) = Z.of_nat (bn_dmax br))
        by (rewrite wlimbs_len; f_equal; subst nb; rewrite splice_length; [exact LBR| rewrite repeat_length, LBR; lia]).
      step. replace (Z.of_nat i + 1) with (Z.of_nat (i + 1)) in BNr by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
      assert (Lnb : length nb = bn_dmax br) by (subst nb; rewrite splice_length; [exact LBR| rewrite repeat_length, LBR; lia]).
      assert (LMnb : limbs nb) by (subst nb; apply splice_limbs; [exact OKq1| apply limbs_repeat; unfold limb; rewrite BnArith.BW_lit; lia]).
      assert (HWL3 : Forall (w_lib bs1 OW2 PL lo (bv_unsigned sp)) [(bv_unsigned sp + -48, bv_unsigned sp); (ax, ax + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
      { constructor; [left; cbn; lia|]. constructor; [right; right; exists rx, ax; split; [exact HAx2|]; split; [exact NROx|]; cbn; lia|].
        constructor; [| constructor]. right; left; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn; split; [exact Hinpr| clear; lia]. }
      assert (WOK3 : Forall (w_ok OW2 LB bs1 PL EA (bv_unsigned sp) [rx]) [(bv_unsigned sp + -48, bv_unsigned sp); (ax, ax + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
      { constructor; [apply w_stack; cbn; lia|]. constructor; [eapply (w_struct OW2 LB bs1 PL EA (bv_unsigned sp) false [rx] _ rx ax); [left; reflexivity| exact HAx2| assumption| cbn; lia| cbn; lia]|].
        constructor; [| constructor].
        eapply (w_limbs OW2 LB bs1 PL EA (bv_unsigned sp) false [rx] _ rx pr Dr); [left; reflexivity| exact HVx2| exact Edr| exact Hinpr| cbn [fst snd]; fold br; clear; lia| cbn [fst snd]; fold br; clear; lia]. }
      assert (LS4 : lib_state (setbn rx (set_bit_ext br i) bs1) m4 OW2 PL EA).
      { unfold lib_state. eapply (lib_state_close [] bs1 m4 OW2 PL EA rx ax); [| exact ND2| exact HAx2| exact NROx| | |].
        - exact (lib_state_frame st1 LB _ _ [rx] bs1 m2 m4 OW2 PL EA _ HEAP2 LSH MU3 WM3 FROK WOK3).
        - exists Dr. split.
          + unfold bn_cells, bn_dmax, set_bit_ext. cbn [bn_top bn_buf bn_neg bn_flags bn_d]. fold cnt nb. rewrite Lnb. exact BNr.
          + unfold bn_arr, bn_dmax, set_bit_ext. cbn [bn_d bn_buf]. fold cnt nb. rewrite Edr, Lnb. split; [exact Hinpr| exact UF].
        - unfold bg_ok, bn_dmax, set_bit_ext. cbn [bn_buf bn_top bn_flags]. fold cnt nb. rewrite Lnb. unfold BG_DMAX in *.
          split; [exact LMnb|]. split; [unfold bn_dmax in HID; lia|]. split; [clear - OKq3; unfold bn_dmax in *; lia| exact OKq4].
        - apply ids_ok_setbn_same; [exact IDS2| exact HVx2|]. unfold bn_blocks, bn_dmax, set_bit_ext. cbn [bn_d bn_buf]. fold cnt nb. rewrite Lnb. reflexivity. }
      ihere. to_implM.
      eapply (FIN st1 (setbn rx (set_bit_ext br i) bs1) m4 OW2 errv2);
        [ exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROK2 MU3 WM3 HWL3 CEIL)
        | exact LS4
        | apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROK2 AUX2 MU3 WM3 HWL3 SPB ltac:(lia)); unfold GLOBALS_TOP; lia
        | exact ST2 | exact ERR2 | assumption
        | eapply lx_pres_trans; [exact LXP2|]; apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROK2 MU3 WM3 HWL3 CEIL); unfold GLOBALS_TOP; lia
        | exact FA2 | exact SO2
        | eapply refs_stable_trans; [exact RST2| apply refs_stable_setbn]
        | rewrite getbn_setbn_same by exact HVx2; cbn [bn_top set_bit_ext]; lia
        | exact BST | exact FR2 ]. }
    step. rewrite lts_signed by lia. if_cases KT; zify_cond KT.
    -
      replace (bn_top bx <=? i)%nat with false by (symmetry; apply Nat.leb_gt; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      ihere. to_implM. cbn [tbind fst snd]. fold bx.
      eapply (FIN s bs m1 OW errv);
        [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)
        | exact (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK)
        | apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); unfold GLOBALS_TOP; lia
        | exact ST | exact ERR | exact MI
        | apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); unfold GLOBALS_TOP; lia
        | reflexivity | reflexivity | apply refs_stable_refl | fold bx; lia
        | intros q0 A0 n0 Hq0 _; exact Hq0 | exact FR].
    -
      replace (bn_top bx <=? i)%nat with true by (symmetry; apply Nat.leb_le; lia).
      step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (bn_dmax bx))) by lia.
      step.
      step. rewrite lts_signed by lia. if_cases KD; zify_cond KD.
      +
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
        ihere. to_implM. unfold bn_wexpand, bbind, bget, bret, bset. cbn [bind ret tree_ops tbind fst snd]. fold bx.
        replace (i + 1 <=? bn_dmax bx)%nat with true by (symmetry; apply Nat.leb_le; lia).
        cbn [tbind fst snd]. fold bx. change (mkBN (bn_d bx) (splice (bn_buf bx) (bn_top bx) (repeat 0 (i + 1 - bn_top bx))) (i + 1) (bn_neg bx) (bn_flags bx)) with (set_bit_ext bx i).
        eapply (MID s bs m1 OW errv);
          [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)
          | exact (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK)
          | apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); unfold GLOBALS_TOP; lia
          | exact ST | exact ERR | exact MI
          | apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); unfold GLOBALS_TOP; lia
          | reflexivity | reflexivity | apply refs_stable_refl | fold bx; lia | fold bx; lia
          | intros q0 A0 n0 Hq0 _; exact Hq0 | exact FR].
      +
        step. step. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
        assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
        pose proof (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL) as HEAP1.
        pose proof (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
        assert (AUX1 : rauxv_ok m1 B) by (apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); unfold GLOBALS_TOP; lia).
        assert (LXP1 : lx_pres LB (bv_unsigned sp) (XW PL) m m1) by (apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); unfold GLOBALS_TOP; lia).
        ihere. to_implM.
        apply BnAssoc.implM_embed_assoc.
        eapply implM_embed_bind.
        { eapply BnLeaves.implM_embed_leaves; [apply (bn_wexpand_leaves rx (i + 1) bs HVx OKx2)|].
          eapply (bn_expand2_walk HM HF) with (lo := lo) (B := B) (errv := errv) (r := rx) (a := ax) (OW := OW) (LB := LB) (PL := PL) (EA := EA) (words := (i + 1)%nat);
            [| reflexivity | exact HAx | exact WRx | reflexivity | unfold MallocRep.wz; f_equal; lia | lia].
          unfold bn_pre. rewrite ESP.
          split; [exact HEAP1|]. split; [exact LS1|]. split; [eapply frames_ok_call; [exact FROK| exact CEIL| lia| lia]|]. split; [exact AUX1|]. split; [lia|]. split; [exact B63|].
          split; [exact ST|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; lia|]. split; [unfold BN_EXPAND2_STACK; lia|].
          split; [unfold LX_ERRNO, RATP; exact ERR| exact MI]. }
        cbv beta. intros [u bs1] st1 ms1 [PO LEAF]. unfold bn_post in PO. cbn [fst snd] in *.
        destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & OW2 & PL2 & errv2 & -> & HEAP2 & LS2 & AUX2 & ST2 & ERR2
                        & MI2 & LXP2 & FA2 & SO2 & RST2 & -> & -> & HDM & WRES & BST).
        rewrite ESP in *.
        lazymatch goal with |- implM _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
          replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
        destruct LEAF as (LF1 & LF2 & LF3 & LF4 & LF5 & LF6). cbn [snd] in *.
        assert (FR2 : rw_cells bgusegs m2 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
        { eapply rw_cells_agree; [apply agree_of_lx_pres; exact LXP2 | exact FR |].
          intros a Ha. cbn in Ha. eapply (xw_client PL LB _ (bv_unsigned sp) B); [exact (proj1 FROK)| lia|].
          unfold LIBW_bgr, BnRep.LIBW_bn, CONST_ONE, BN_STRUCT_SZ. cbn [rin_ivs app fst snd]. lia. }

        pose proof (ref_at_stable _ _ _ _ _ _ _ RST2 HAx) as HAx2.
        pose proof (RH_nodup_l _ _ _ _ HEAP2) as ND2.
        destruct (lib_state_open [] bs1 m2 OW2 PL EA rx ax LS2 ND2 HAx2 ltac:(intros []) NROx) as ((Dq & BNq & _) & (_ & OKq2 & OKq3 & _) & _).
        unfold bn_cells in BNq. unfold BG_DMAX in OKq3. set (bq := getbn rx bs1) in *.
        unfold implM. iprefix.
        step. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by lia; lia|]. clear KZ.
        step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (bn_top bq))) by lia.
        ihere. to_implM. cbn [tbind fst snd]. fold bq.
        change (mkBN (bn_d bq) (splice (bn_buf bq) (bn_top bq) (repeat 0 (i + 1 - bn_top bq))) (i + 1) (bn_neg bq) (bn_flags bq)) with (set_bit_ext bq i).
        eapply (MID st1 bs1 m2 OW2 errv2);
          [exact HEAP2 | exact LS2 | exact AUX2 | exact ST2 | unfold LX_ERRNO, RATP in ERR2; exact ERR2 | exact MI2
          | eapply lx_pres_trans; [exact LXP1|]; eapply lx_pres_weaken; [exact LXP2| lia | intros b0 Hb0; exact Hb0 | intros a0 Ha0; exact Ha0]
          | congruence | congruence | exact RST2 | fold bq in LF2; rewrite LF2; fold bx; lia | exact HDM | exact BST | exact FR2].
  Qed.
End Proofs.
End WithCeiling0.
