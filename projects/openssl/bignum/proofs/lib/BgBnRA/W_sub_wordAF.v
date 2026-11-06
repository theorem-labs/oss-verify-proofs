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
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib BgWordSpec.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnArith BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr ShiftPure.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR2 Require W_sub_word.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import BnAKitAF BnCallAF W_callsAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BN_SUB_WORD : Z := 0x23590c.
Definition BN_SUB_WORD_STACK : Z := 80.

Local Notation sw_l := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sub_word.sw_l.
Local Notation sw_i := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sub_word.sw_i.
Local Notation sw_buf := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sub_word.sw_buf.
Local Notation sw_top := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sub_word.sw_top.
Local Notation sw_bn := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sub_word.sw_bn.
Local Notation sw_top_le := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sub_word.sw_top_le.
Local Notation sw_top_keep := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sub_word.sw_top_keep.
Local Notation sw_top_dec := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sub_word.sw_top_dec.
Local Notation wlimbs_upd := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sub_word.wlimbs_upd.
Local Notation wlimbs_nth := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sub_word.wlimbs_nth.
Local Notation upd_mid := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sub_word.upd_mid.
Local Notation Z_to_bv_subw := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sub_word.Z_to_bv_subw.
Local Notation sub_word_limbs_ge := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sub_word.sub_word_limbs_ge.
Local Notation sub_word_limbs_lt := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sub_word.sub_word_limbs_lt.
Local Notation sub_word_limbs_zeros := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sub_word.sub_word_limbs_zeros.

Lemma shad_lit : forall a, 0 <= a < 140737488355328 -> bv_unsigned (Z_to_bv 64 (shad a)) = shad a.
Proof. intros a Ha. pose proof (shad_range a Ha) as R. unfold SHLO, SHHI in R. apply unsigned_lit. lia. Qed.

Lemma shad_next : forall a, shad a + 1 = shad (a + 8).
Proof. intros a. unfold shad. Z.div_mod_to_equations. lia. Qed.

Lemma sw_loopA : forall (Q : machine_state -> Prop) (F : bvmap 5 word) (fc : bv 32)
    (x1 x2 gp tp x8 x9 x10 x13 x14 x18 x19 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (D n : Z) (m0 : mem) (rest la pre : list Z) (x v : Z) (m1 : mem) (x6 x7 x17 : word),
  limbs pre -> limbs la -> limbs rest -> 0 <= v < 18446744073709551616 -> 1 <= lval la ->
  Z.of_nat (length pre + 1 + length la + length rest) < 2 ^ 28 -> n = Z.of_nat (length pre + 1 + length la + length rest) ->
  acc bgasegs m0 D (8 * n) -> D mod 8 = 0 -> (0 <= D /\ D + 8 * n <= 140737488355328) -> offshW [(D, D + 8 * n)] ->
  munch [(D, D + 8 * n)] m0 m1 -> wmono bgasegs m0 m1 ->
  u64arr bgasegs m1 D (wlimbs (pre ++ x :: la ++ rest)) -> mem_inv bgasegs m1 ->
  (forall (m' : mem) (zs : list Z) (y : Z) (la2 : list Z),
      la = zs ++ y :: la2 -> Forall (fun z => z = 0) zs -> 1 <= y < 18446744073709551616 ->
      u64arr bgasegs m' D (wlimbs (pre ++ v :: repeat 18446744073709551615 (length zs) ++ y :: la2 ++ rest)) ->
      munch [(D, D + 8 * n)] m0 m' -> wmono bgasegs m0 m' -> mem_inv bgasegs m' ->
      evt bgasegs Q (MS (mkR x1 x2 gp tp (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 (D + 8 * Z.of_nat (length pre + 1 + length zs)))
                              (Z_to_bv 64 (D + 8 * Z.of_nat (length pre + 1 + length zs))) x8 x9 x10
                              (Z_to_bv 64 (D + 8 * Z.of_nat (length pre + 1 + length zs))) (Z_to_bv 64 (D + 8 * Z.of_nat (length pre + 1 + length zs)))
                              x13 x14 (Z_to_bv 64 (Z.of_nat (length pre + 1 + length zs))) (Z_to_bv 64 (shad (D + 8 * Z.of_nat (length pre + 1 + length zs))))
                              (Z_to_bv 64 y) x18 x19 (Z_to_bv 64 SHB) x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                         F (Z_to_bv 64 0x235adc) fc None m' (seg_rom bgasegs))) ->
  evt bgasegs Q (MS (mkR x1 x2 gp tp (Z_to_bv 64 v) x6 x7 x8 x9 x10
                          (Z_to_bv 64 (D + 8 * Z.of_nat (length pre))) (Z_to_bv 64 (D + 8 * Z.of_nat (length pre)))
                          x13 x14 (Z_to_bv 64 (Z.of_nat (length pre))) (Z_to_bv 64 (shad (D + 8 * Z.of_nat (length pre))))
                          x17 x18 x19 (Z_to_bv 64 SHB) x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x235a9c) fc None m1 (seg_rom bgasegs)).
Proof.
  intros Q F fc x1 x2 gp tp x8 x9 x10 x13 x14 x18 x19 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 D n m0 rest.
  induction la as [|y0 la IH]; intros pre x v m1 x6 x7 x17 Lpre Lla Lrest HV HL L28 EN ACC AL BD OFF MU WM U MI K.
  - cbn [lval] in HL. lia.
  - pose proof (u64arr_bound bgasegs _ _ _ U) as UB. rewrite wlimbs_len, length_app in UB. cbn [length] in UB. rewrite length_app in UB. cbn [length] in UB, L28, EN.
    assert (LM : Z.of_nat (length (wlimbs (pre ++ x :: (y0 :: la) ++ rest))) = Z.of_nat (length pre + 1 + S (length la) + length rest))
      by (rewrite wlimbs_len, length_app; cbn [length]; rewrite length_app; cbn [length]; lia).
    apply limbs_cons_inv in Lla. destruct Lla as [[Hy0 Hy1] Lla]. rewrite BW_lit in Hy1.
    assert (NTH : nth_error (wlimbs (pre ++ x :: (y0 :: la) ++ rest)) (Z.to_nat (Z.of_nat (length pre) + 1)) = Some (Z_to_bv 64 y0)).
    { replace (Z.of_nat (length pre) + 1) with (Z.of_nat (S (length pre))) by lia.
      replace y0 with (nth (S (length pre)) (pre ++ x :: (y0 :: la) ++ rest) 0) at 2
        by (rewrite app_nth2 by lia; replace (S (length pre) - length pre)%nat with 1%nat by lia; reflexivity).
      apply wlimbs_nth. rewrite length_app. cbn [length]. rewrite length_app. cbn [length]. lia. }
    unfold SHLO, SHHI in OFF.
    assert (SHL : bv_unsigned (Z_to_bv 64 (shad (D + 8 * Z.of_nat (length pre)))) = shad (D + 8 * Z.of_nat (length pre))) by (apply shad_lit; lia).

    (let ad := cur_mem_addr in
     pose proof (acc_rd_limb bgasegs _ m0 m1 D n 0 (Z.of_nat (length pre)) ad ACC MU OFF AL BD eq_refl ltac:(clear; lia) ltac:(clear; lia) ltac:(lia)
                             ltac:(unfold wa; f_equal; f_equal; clear; lia)) as RD); step; clear RD. chk0.

    assert (IDX : 0 <= Z.of_nat (length pre) < Z.of_nat (length (wlimbs (pre ++ x :: (y0 :: la) ++ rest)))) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (u64arr_store_ok bgasegs mx D _ (Z.of_nat (length pre)) (wa (D + 8 * Z.of_nat (length pre))) U IDX eq_refl) as SOKW;
      pose proof (u64arr_write bgasegs mx D _ (Z.of_nat (length pre)) (Z_to_bv 64 v) U IDX) as U2 end.
    rewrite Nat2Z.id, wlimbs_upd in U2 by (rewrite length_app; cbn [length]; lia). rewrite upd_mid in U2.
    clear U. step. store_done.

    do 3 step.
    (let ad := cur_mem_addr in
     pose proof (acc_rd_limb bgasegs _ m0 _ D n 0 (Z.of_nat (length pre) + 1) ad ACC MU OFF AL BD eq_refl ltac:(clear; lia) ltac:(clear; lia) ltac:(lia)
                             ltac:(unfold wa, shad; f_equal; rewrite ?unsigned_lit by lia; rewrite ?Z.shiftr_div_pow2 by (clear; lia);
                                   change (2 ^ 3) with 8; unfold SHB; clear; Z.div_mod_to_equations; lia)) as RD); step; clear RD. chk0.

    assert (NTH2 : nth_error (wlimbs (pre ++ v :: (y0 :: la) ++ rest)) (Z.to_nat (Z.of_nat (length pre) + 1)) = Some (Z_to_bv 64 y0)).
    { replace (Z.of_nat (length pre) + 1) with (Z.of_nat (S (length pre))) by lia.
      replace y0 with (nth (S (length pre)) (pre ++ v :: (y0 :: la) ++ rest) 0) at 2
        by (rewrite app_nth2 by lia; replace (S (length pre) - length pre)%nat with 1%nat by lia; reflexivity).
      apply wlimbs_nth. rewrite length_app. cbn [length]. rewrite length_app. cbn [length]. lia. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (u64arr_read bgasegs mx D _ (Z.of_nat (length pre) + 1) _ (wa (D + 8 * Z.of_nat (length pre) + 8)) U2 NTH2
                              ltac:(clear; lia) ltac:(f_equal; lia)) as RD end.
    step. clear RD.
    step. step. step. rewrite (unsigned_lit (Z.of_nat (length pre))) by lia. rewrite (bn_swrap32_small (Z.of_nat (length pre) + 1)) by lia.
    step. step. step.

    step. if_cases KZ; zify_cond KZ.
    +
      assert (EY : y0 = 0) by (rewrite ?unsigned_lit in KZ by lia; lia). clear KZ. subst y0.
      cbn [lval] in HL. pose proof (lval_nonneg la Lla) as LN. rewrite BW_lit in HL.
      setreg 11%Z (Z_to_bv 64 (D + 8 * Z.of_nat (length (pre ++ [v])))) ltac:(f_equal; rewrite length_app; cbn [length]; lia).
      setreg 15%Z (Z_to_bv 64 (Z.of_nat (length (pre ++ [v])))) ltac:(f_equal; rewrite length_app; cbn [length]; lia).
      setreg 16%Z (Z_to_bv 64 (shad (D + 8 * Z.of_nat (length (pre ++ [v]))))) ltac:(f_equal; rewrite shad_next; f_equal; rewrite length_app; cbn [length]; lia).
      setreg 5%Z (Z_to_bv 64 18446744073709551615) ltac:(exact (ZBridge.Z_to_bv_mod64 (-1))).
      replace (pre ++ v :: (0 :: la) ++ rest) with ((pre ++ [v]) ++ 0 :: la ++ rest) in U2 by (rewrite <- app_assoc; reflexivity).
      eapply (IH (pre ++ [v]) 0 18446744073709551615);
        [ apply limbs_app; [exact Lpre| constructor; [unfold limb; rewrite BW_lit; lia| constructor]] | exact Lla | exact Lrest | lia | lia
        | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia | exact ACC | exact AL | exact BD | exact OFF | eassumption | eassumption | exact U2 | assumption | ].
      intros m' zs y la2 ELA HZ HY U' MU' WM' MI'.
      replace (length (pre ++ [v]) + 1 + length zs)%nat with (length pre + 1 + length (0%Z :: zs))%nat by (rewrite length_app; cbn [length]; lia).
      eapply (K m' (0 :: zs) y la2); [rewrite ELA; reflexivity | constructor; [reflexivity| exact HZ] | exact HY | | exact MU' | exact WM' | exact MI'].
      rewrite <- app_assoc in U'. exact U'.
    +
      assert (NY : 1 <= y0) by (rewrite ?unsigned_lit in KZ by lia; lia). clear KZ.
      setreg 11%Z (Z_to_bv 64 (D + 8 * Z.of_nat (length pre + 1 + length (@nil Z)))) ltac:(f_equal; cbn [length]; lia).
      setreg 15%Z (Z_to_bv 64 (Z.of_nat (length pre + 1 + length (@nil Z)))) ltac:(f_equal; cbn [length]; lia).
      setreg 16%Z (Z_to_bv 64 (shad (D + 8 * Z.of_nat (length pre + 1 + length (@nil Z))))) ltac:(f_equal; rewrite shad_next; f_equal; cbn [length]; lia).
      setreg 5%Z (Z_to_bv 64 18446744073709551615) ltac:(exact (ZBridge.Z_to_bv_mod64 (-1))).

      eapply (K _ [] y0 la); [reflexivity | constructor | lia | exact U2 | eassumption | eassumption | assumption].
Qed.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma BN_sub_word_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (rx : bnref) (ax w : Z),
  bn_preA Σ ls m OW LB PL EA sp lo BN_SUB_WORD_STACK MC ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_SUB_WORD (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> ref_at ls OW PL rx ax -> wref PL rx -> a0 = wz ax -> a1 = wz w -> 0 <= w < 2^64 ->
  w <= lval (firstn (bn_top (getbn rx ls)) (bn_buf (getbn rx ls))) ->
  implA (BN_sub_word (tree_ops bptr) rx w ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC
              (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = wz 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx ls) <> Some q -> In (q, A, n) OW')))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_SUB_WORD) fc None m (seg_rom bgasegs)).
Proof.
  intros until w. intros PRE UW CTX -> HAx WRx -> -> HW HMAG.
  pose proof (proj1 WRx : not_one rx) as NROx.
  pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
  pose proof LO as LO'. unfold BN_SUB_WORD_STACK in LO'.
  unfold BN_SUB_WORD, MallocRep.wz.
  change (2 ^ 64) with 18446744073709551616 in HW.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1' & C2' & C3'). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 64, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HAx) as HVx.
  set (bx := getbn rx ls) in *.
  assert (LBX : length (bn_buf bx) = bn_dmax bx) by reflexivity.
  unfold BN_sub_word, bbind, bget, bset, bret. cbn [bind ret tree_ops tbind fst snd]. fold bx.
  apply implA_from_evt.
  carve_frame 64%nat ST.
  do 9 step.

  lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j :: _) => set (jfr := j) in *; clearbody jfr end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -64, bv_unsigned sp)]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
  pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
  assert (EV : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MC Σ ls OW m
                 [CB 8 jfr; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] 0 Σ ls m1 OW).
  { unfold cenvA, cenv_ok.
    split; [split; [exact CEIL|]; split; [lia|]; split; [lia|]; split; [unfold USTACK_TOP; lia|]; split; [exact SP16|];
            split; [clear - SP16; Z.div_mod_to_equations; lia|]; split; [exact CNT|]; split; [exact CRED|]; split; [exact FROK|]; split; [exact FAL| exact NOFR]|].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))|].
    split; [exact ST|]. split; [exact MI|].
    split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU HWL CEIL ltac:(lia))|].
    split; [lia|]. split; [apply cnt_eq_refl|]. split; [apply refs_stable_refl|].
    split; [cbn [app]; exact FR|]. split; [cbn; lia|]. unfold uw_opt.
    eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
  pose proof EV as (OK & HEAP1 & _).

  assert (EPI : forall (Σ1 : rts RT) (ls1 : bstate bptr) (m2 : mem) (OW2 : list block) (used : Z) (FT : bvmap 5 word) (fcT : bv 32)
                       (q1 q5 q6 q7 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q21 q28 q29 q30 q31 : word),
      cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MC Σ ls OW m
            [CB 8 jfr; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] used Σ1 ls1 m2 OW2 ->
      lib_state ls1 m2 OW2 PL EA -> used <= MC ->
      (forall q A n, In (q, A, n) OW -> bn_d bx <> Some q -> In (q, A, n) OW2) ->
      implA (TRet (tt, ls1)) Σ1
        (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC
                  (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = Z_to_bv 64 1 /\ (forall q A n, In (q, A, n) OW -> bn_d bx <> Some q -> In (q, A, n) OW')))
        (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 TP_A) q5 q6 q7 sp q9 q10 q11 q12 q13 q14 q15 q16 q17
                 q18 q19 (Z_to_bv 64 1) q21 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
            FT (Z_to_bv 64 0x2359d0) fcT None m2 (seg_rom bgasegs))).
  { intros Σ1 ls1 m2 OW2 used FT fcT q1 q5 q6 q7 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q21 q28 q29 q30 q31 EV1 LS2 USED BST.
    clear MU WM ST MI FR HWL WOK LS1 HEAP1 EV OK OFF SHB1 SHB2 HEAP LS PARTS PRE UW HVx HMAG.
    pose proof EV1 as (OK1 & HEAP2 & ST2 & MI2 & AXP2 & CR2 & CNT2 & RS2 & FR2 & FSZ2 & UW2).
    cbn [app] in FR2.
    apply implA_ret_evt.
    step. do 7 step. release_frame FR2 ST2 (bv_unsigned sp). step. step.
    apply evt_done.
    unfold bn_postA. do 17 eexists. exists m2, OW2, PL. split; [reflexivity|]. cbn [fst snd].
    split; [exact HEAP2|]. split; [exact LS2|]. split; [exact ST2|]. split; [exact MI2|]. split; [exact AXP2|].
    split; [clear - CR2 USED; lia|]. split; [exact CNT2|]. split; [exact RS2|].
    split; [reflexivity|]. split; [reflexivity| exact BST]. }

  step. if_cases KW; zify_cond KW.
  -
    assert (EW : w = 0) by (rewrite ?unsigned_lit in KW by (clear - HW; lia); clear - KW; lia).
    replace (w =? 0) with true by (symmetry; apply Z.eqb_eq; exact EW).
    step. step. apply evt_done.
    eapply (EPI Σ ls m1 OW 0 F fc); [exact EV | exact LS1 | unfold MC; clear; lia | intros q0 A0 n0 Hq0 _; exact Hq0].
  -
    assert (NW : w <> 0) by (rewrite ?unsigned_lit in KW by (clear - HW; lia); clear - KW; lia).
    replace (w =? 0) with false by (symmetry; apply Z.eqb_neq; exact NW).
    cbn [tbind fst snd]. fold bx.

    do 7 step.

    assert (LOF16 : lo <= bv_unsigned sp + -64 - 16) by (clear - LO'; lia).
    eapply (is_zero_callA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MC Σ ls OW m LOF16) with (r := rx) (ar := ax);
      [exact EV | exact LS1 | exact HAx | exact NROx |].
    intros m2 y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 EV2 LS2.
    rewrite (ret_pc_even 2316624) by (clear; lia).
    fold bx.

    destruct (bn_top bx =? 0)%nat eqn:ET; cbv beta.
    { apply evt_done. unfold bunr. cbn [unreachable tree_ops]. apply implA_unr. }
    apply Nat.eqb_neq in ET. fold bx.
    destruct (bn_neg bx) eqn:EN.
    { apply evt_done. unfold bunr. cbn [unreachable tree_ops]. apply implA_unr. }

    clear MU WM OFF SHB1 SHB2 HEAP LS PARTS ST MI FR HWL WOK LS1 HEAP1 EV OK.
    pose proof EV2 as (OK2 & HEAP2 & ST2 & MI2 & _ & _ & _ & _ & FR2 & FSZ2 & _). cbn [app] in FR2.
    pose proof (AH_nodup_l _ _ _ _ HEAP2) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    destruct (lib_state_open [] ls m2 OW PL EA rx ax LS2 ND HAx ltac:(intros []) NROx) as ((Dx & BNx & ARRx) & (OKx1 & OKx2 & OKx3 & OKx4) & LSH).
    destruct (bn_arr_facts_w ls OW PL EA (bv_unsigned sp) USTACK_TOP Σ LB m2 rx Dx HEAP2 PARTS FROK HVx WRx ARRx) as (Ux & LENx & Dx0' & DxC & DxI & DSEPx).
    fold bx in BNx, ARRx, Ux, LENx, DxC, DxI, DSEPx, OKx1, OKx2, OKx3, OKx4.
    pose proof (DSEPx rx ax HAx) as SEPxx.
    destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP2 PARTS NOFR HAx NROx) as (qx & Ax & nx & Hinx & Rx1 & Rx2).
    pose proof (AH_range_in _ _ _ _ _ _ _ HEAP2 Hinx) as (AX0 & _ & _ & AXC & _).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP2 LS2 NOFR HAx NROx) as (ACX & ALX & OFX).
    pose proof ARRx as ARRo. apply (fun ARRnb__ => bn_arr_nofr PL rx m2 OW Dx _ PWF NOFR NROx ARRnb__ ltac:(solve_nbuf)) in ARRo.
    destruct (arr_shA _ _ _ _ _ _ HEAP2 ARRo) as (ACDX & ALDX & OFDX).
    unfold bn_cells, BnRepDefs.bn_cells, MallocRep.wz in BNx. unfold SHLO, SHHI in *. unfold BG_DMAX in OKx3.
    rewrite EN in BNx. cbn [Z.b2z] in BNx.
    assert (X0 : 0 < ax) by (clear - AX0 Rx1; lia).
    assert (XC : ax + 24 <= BnHeapA.ACEIL) by (clear - AXC Rx2; lia).

    assert (HDx : exists px, bn_d bx = Some px /\ In (px, Dx, 8 * Z.of_nat (bn_dmax bx)) OW).
    { unfold BnRepDefs.bn_arr in ARRo. destruct (bn_d bx) as [px|]; [exists px; split; [reflexivity| exact (proj1 ARRo)]|].
      exfalso. destruct ARRo as [_ E]. unfold bn_dmax in OKx2. rewrite E in OKx2. cbn in OKx2. clear - OKx2 ET. lia. }
    destruct HDx as (px & Edx & Hinpx).
    assert (TOPZ : 0 < Z.of_nat (bn_top bx) <= Z.of_nat (bn_dmax bx) /\ Z.of_nat (bn_dmax bx) <= 512) by (clear - ET OKx2 OKx3; unfold bn_dmax in *; lia).
    assert (BDX : 0 <= Dx /\ Dx + 8 * Z.of_nat (bn_dmax bx) <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - Dx0' DxC C1' C2' C3'; lia).
    pose proof (AH_range _ _ _ _ _ _ _ HEAP2 Hinpx) as (PX0 & PX16 & _).
    pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp); (ax, ax + 24); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]%Z m2) as MU3.
    pose proof (wmono_refl bgasegs m2) as WM3.
    assert (OFF3 : offshW [(bv_unsigned sp + -64, bv_unsigned sp); (ax, ax + 24); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]).
    { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. clear - OFX OFDX SPR LO' CEIL C1' C2' C3'. lia. }
    cbn [Z.b2z].

    step. if_cases KT; zify_cond KT; [| exfalso; rewrite ?unsigned_lit in KT by (clear; lia); clear - KT; lia]. clear KT.

    do 3 step. shl_with ACX ALX. chk0.
    step. step. if_cases KN; zify_cond KN; [| exfalso; rewrite ?unsigned_lit in KN by (clear; lia); cbn in KN; clear - KN; lia]. clear KN.

    do 3 step. shl_with ACX ALX. chk0.
    step. rewrite (sx32_small (Z.of_nat (bn_top bx))) by (clear - TOPZ; lia).
    step. step.

    setreg 12%Z (Z_to_bv 64 (ax ≫ 3)) ltac:(f_equal; rewrite unsigned_lit by (unfold BnHeapA.ACEIL in *; clear - X0 XC C1' C2' C3'; lia); reflexivity).

    set (top := bn_top bx) in *. set (buf := bn_buf bx) in *.
    assert (TOPD : (top <= length buf)%nat) by (unfold top, buf; unfold bn_dmax in OKx2; exact OKx2).
    assert (HFS : firstn top buf = nth 0 buf 0 :: skipn 1 (firstn top buf)).
    { destruct buf as [|b0 buf']; [cbn [length] in TOPD; clear - TOPD ET; lia|]. destruct top as [|top']; [clear - ET; lia|]. reflexivity. }
    set (d0 := nth 0 buf 0) in *. set (la := skipn 1 (firstn top buf)) in *.
    pose proof (limbs_firstn top buf OKx1) as LFS. rewrite HFS in LFS. apply limbs_cons_inv in LFS. destruct LFS as [[Hd0 Hd1] Lla]. rewrite BW_lit in Hd1.
    assert (LLA : length la = (top - 1)%nat) by (unfold la; rewrite length_skipn, firstn_length_le by exact TOPD; reflexivity).
    pose proof (lval_nonneg la Lla) as LAN.
    rewrite HFS in HMAG. cbn [lval] in HMAG. rewrite BW_lit in HMAG.
    assert (Hcase : ((top =? 1)%nat && (d0 <? w)) = false).
    { destruct (Nat.eqb_spec top 1) as [E1|E1]; [| reflexivity]. cbn [andb]. apply Z.ltb_ge.
      destruct la as [|y t]; [cbn [lval] in HMAG; clear - HMAG; lia| cbn [length] in LLA; clear - LLA E1; lia]. }
    rewrite Hcase.
    pose proof (sub_word_limbs_spec (firstn top buf) w 0 (limbs_firstn top buf OKx1) ltac:(rewrite BW_lit; clear - HW NW; lia) ltac:(rewrite HFS; cbn [lval]; rewrite BW_lit; exact HMAG)) as SWS.
    destruct (sub_word_limbs (firstn top buf) w 0) as [l i] eqn:ESW.
    destruct SWS as (Ll & LENl & _ & _ & Hi & _). rewrite firstn_length_le in LENl, Hi by exact TOPD.
    assert (Hi' : (i < top)%nat) by (apply Hi; rewrite HFS; discriminate). clear Hi.
    assert (EBN : mkBN (bn_d bx) (splice buf 0 l) (if (nth i (splice buf 0 l) 0 =? 0) && (i =? top - 1)%nat then (top - 1)%nat else top) false (bn_flags bx) = sw_bn bx w).
    { unfold sw_bn, sw_top, sw_buf, sw_l, sw_i, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sub_word.sw_bn, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sub_word.sw_top,
        OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sub_word.sw_buf, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sub_word.sw_l, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sub_word.sw_i.
      fold bx top buf. rewrite ESW, EN. cbn [fst snd]. reflexivity. }
    rewrite EBN. clear EBN.
    assert (ESB : sw_buf bx w = l ++ skipn top buf).
    { unfold sw_buf, sw_l, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sub_word.sw_buf, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sub_word.sw_l. fold bx top buf. rewrite ESW. cbn [fst]. unfold splice. rewrite firstn_O, LENl. reflexivity. }
    assert (ESI : sw_i bx w = i) by (unfold sw_i, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sub_word.sw_i; fold bx top buf; rewrite ESW; reflexivity).
    assert (LSB : length (sw_buf bx w) = bn_dmax bx).
    { rewrite ESB, length_app, length_skipn, LENl. unfold bn_dmax. fold buf. clear - TOPD. lia. }
    assert (LMSB : limbs (sw_buf bx w)) by (rewrite ESB; apply limbs_app; [exact Ll| apply limbs_skipn; exact OKx1]).
    assert (HWL3 : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp); (ax, ax + 24); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]).
    { constructor; [left; cbn; clear - LO'; lia|]. constructor; [w_lib_ref HAx NROx|].
      constructor; [right; left; exists (px, Dx, 8 * Z.of_nat (bn_dmax bx)); cbn [blk_addr blk_size fst snd]; split; [exact Hinpx| clear; lia]| constructor]. }
    assert (WOK3 : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) [rx]) [(bv_unsigned sp + -64, bv_unsigned sp); (ax, ax + 24); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; clear - LO' CEIL; lia|].
      constructor; [eapply (w_struct OW LB ls PL EA (bv_unsigned sp) false [rx] _ rx ax); [left; reflexivity| exact HAx| exact NROx| cbn; clear; lia| cbn; clear; lia]|].
      constructor; [eapply (w_limbs OW LB ls PL EA (bv_unsigned sp) false [rx] _ rx px Dx); [left; reflexivity| exact HVx| exact Edx| exact Hinpx| cbn [fst snd]; clear; lia| cbn [fst snd]; fold bx; clear; lia]| constructor]. }
    assert (EBL : length (bn_blocks (sw_bn bx w)) = length (bn_blocks (getbn rx ls))).
    { fold bx. unfold bn_blocks, bn_dmax, sw_bn, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sub_word.sw_bn. cbn [bn_d bn_buf]. rewrite Edx. reflexivity. }

    assert (ENVF : forall m5, munch [(bv_unsigned sp + -64, bv_unsigned sp); (ax, ax + 24); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]%Z m2 m5 -> wmono bgasegs m2 m5 ->
                     stk bgasegs m5 lo (bv_unsigned sp + -64) -> mem_inv bgasegs m5 ->
                     rw_cells bgasegs m5 (bv_unsigned sp + -64) [CB 8 jfr; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
                     cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MC Σ ls OW m
                           [CB 8 jfr; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] 0 Σ (setbn rx (sw_bn bx w) ls) m5 OW).
    { intros m5 MU5 WM5 ST5 MI5 FR5. apply cenv_setbnA; [| exact HVx | exact EBL].
      eapply cenv_silentA; [exact EV2 | exact LS2 | exact MU5 | exact WM5 | exact HWL3 | exact ST5 | exact MI5 | cbn [app]; exact FR5 | exact FSZ2]. }
    assert (CLOSE : forall m5, rw_cells bgasegs m5 ax (bn_cells Dx (sw_bn bx w)) -> u64arr bgasegs m5 Dx (wlimbs (sw_buf bx w)) ->
                     munch [(bv_unsigned sp + -64, bv_unsigned sp); (ax, ax + 24); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]%Z m2 m5 -> wmono bgasegs m2 m5 ->
                     lib_state (setbn rx (sw_bn bx w) ls) m5 OW PL EA).
    { intros m5 BN5 U5 MU5 WM5. unfold lib_state. eapply (lib_state_close [] ls m5 OW PL EA rx ax); [| exact ND| exact HAx| exact NROx| | |].
      - eapply (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP); [exact HEAP2 | exact LSH | exact MU5 | exact WM5 | exact FROK | exact WOK3].
      - exists Dx. split; [exact BN5|].
        apply (fun ARRnb__ => bn_arr_of_nofr PL rx m5 OW Dx _ PWF NOFR NROx ARRnb__ ltac:(solve_nbuf)).
        unfold BnRepDefs.bn_arr, bn_dmax, sw_bn, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sub_word.sw_bn. cbn [bn_d bn_buf]. rewrite Edx. fold (bn_dmax bx). unfold bn_dmax in LSB. rewrite LSB. split; [exact Hinpx| exact U5].
      - unfold bg_ok, bn_dmax, sw_bn, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sub_word.sw_bn in *. cbn [bn_buf bn_top bn_flags]. rewrite LSB. unfold BG_DMAX.
        split; [exact LMSB|]. split; [pose proof (sw_top_le bx w) as STL; clear - OKx2 STL; unfold top in *; lia|]. split; [exact OKx3| exact OKx4].
      - apply ids_ok_setbn_same; [exact IDS| exact HVx|]. unfold bn_blocks, bn_dmax, sw_bn, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sub_word.sw_bn in *. cbn [bn_d bn_buf]. rewrite LSB. reflexivity. }

    lazymatch goal with |- evt _ ?Q _ =>
    assert (FIN : forall (m3 : mem) (A Bs : list Z) (y w' : Z) (q5 q6 q7 q12 q16 : word),
      sw_buf bx w = A ++ (y - w') :: Bs -> length A = i -> 1 <= w' <= y -> y < 18446744073709551616 ->
      u64arr bgasegs m3 Dx (wlimbs (A ++ y :: Bs)) ->
      rw_cells bgasegs m3 ax [C8 (Z_to_bv 64 Dx); C4 (Z_to_bv 64 (Z.of_nat top)); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax bx))); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (bn_flags bx))] ->
      rw_cells bgasegs m3 (bv_unsigned sp + -64) [CB 8 jfr; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      stk bgasegs m3 lo (bv_unsigned sp + -64) -> mem_inv bgasegs m3 ->
      munch [(bv_unsigned sp + -64, bv_unsigned sp); (ax, ax + 24); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]%Z m2 m3 -> wmono bgasegs m2 m3 ->
      evt bgasegs Q (MS (mkR (Z_to_bv 64 2316624) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 TP_A) q5 q6 q7 sp (Z_to_bv 64 w') (Z_to_bv 64 (ax + 8))
                              (Z_to_bv 64 (Dx + 8 * Z.of_nat i)) q12 (Z_to_bv 64 ((ax + 8) ≫ 3 + SHB)) (Z_to_bv 64 (Z.of_nat top)) (Z_to_bv 64 (Z.of_nat i)) q16 (Z_to_bv 64 y)
                              (Z_to_bv 64 (ax + 16)) (Z_to_bv 64 ax) (Z_to_bv 64 SHB) (Z_to_bv 64 ((ax + 16) ≫ 3 + SHB))
                              s6 s7 s8 s9 s10 s11 y11 y12 y13 y14) F (Z_to_bv 64 0x235aec) fc None m3 (seg_rom bgasegs)))
    end.
    { intros m3 A Bs y w' q5 q6 q7 q12 q16 EQB LA HWY HY U3 BN3 FR3 ST3 MI3 MU4 WM4.
      clear Ux BNx FR2 ST2 MI2 MU3 WM3.
      assert (LAB : length (A ++ y :: Bs) = bn_dmax bx).
      { rewrite <- LSB, EQB, !length_app. cbn [length]. reflexivity. }
      assert (LMAB : Z.of_nat (length (wlimbs (A ++ y :: Bs))) = Z.of_nat (bn_dmax bx)) by (rewrite wlimbs_len, LAB; reflexivity).
      assert (NTHI : nth i (sw_buf bx w) 0 = y - w') by (rewrite EQB, app_nth2, LA, Nat.sub_diag by (clear - LA; lia); reflexivity).
      assert (IZ : 0 <= Z.of_nat i < Z.of_nat top) by (clear - Hi'; lia).
      do 2 step. shl_limb ACDX ALDX BDX (Z.of_nat i). chk0.
      step. rewrite ?(unsigned_lit w') by (clear - HWY HY; lia). rewrite ?(unsigned_lit y) by (clear - HWY HY; lia).
      setreg 12%Z (Z_to_bv 64 (y - w')) ltac:(f_equal; clear; lia).

      assert (IDX : 0 <= Z.of_nat i < Z.of_nat (length (wlimbs (A ++ y :: Bs)))) by (rewrite LMAB; unfold top in IZ; clear - IZ TOPZ; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (u64arr_store_ok bgasegs mx Dx _ (Z.of_nat i) (wa (Dx + 8 * Z.of_nat i)) U3 IDX eq_refl) as SOKW;
        pose proof (u64arr_write bgasegs mx Dx _ (Z.of_nat i) (Z_to_bv 64 (y - w')) U3 IDX) as U4 end.
      rewrite Nat2Z.id, wlimbs_upd in U4 by (rewrite LAB; unfold top in IZ; clear - IZ TOPZ; lia).
      replace (upd (A ++ y :: Bs) i (y - w')) with (sw_buf bx w) in U4 by (rewrite EQB, <- LA; symmetry; apply upd_mid).
      assert (LMSBZ : Z.of_nat (length (wlimbs (sw_buf bx w))) = Z.of_nat (bn_dmax bx)) by (rewrite wlimbs_len, LSB; reflexivity).
      clear U3. step. store_done.
      step.

      assert (ECELL : forall tp', sw_top bx w = tp' ->
                bn_cells Dx (sw_bn bx w) = [C8 (Z_to_bv 64 Dx); C4 (Z_to_bv 64 (Z.of_nat tp')); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax bx))); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (bn_flags bx))]).
      { intros tp' Etp. unfold bn_cells, BnRepDefs.bn_cells, sw_bn, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sub_word.sw_bn, bn_dmax, MallocRep.wz. cbn [bn_d bn_buf bn_top bn_neg bn_flags].
        unfold bn_dmax in LSB. rewrite LSB, EN, Etp. reflexivity. }
      step. if_cases KY; zify_cond KY.
      -
        assert (NY : y <> w') by (rewrite ?unsigned_lit in KY by (clear - HWY HY; lia); clear - KY; lia). clear KY.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        apply evt_done.
        eapply (EPI Σ (setbn rx (sw_bn bx w) ls) m5 OW 0);
          [ apply ENVF; [exact MU4 | exact WM4 | exact ST3 | exact MI3 | exact FR3]
          | apply CLOSE; [| exact U4 | exact MU4 | exact WM4]
          | unfold MC; clear; lia | intros q0 A0 n0 Hq0 _; exact Hq0 ].
        rewrite (ECELL top); [exact BN3|]. apply sw_top_keep. left. rewrite ESI, NTHI. clear - NY. lia.
      -
        assert (EY : y = w') by (rewrite ?unsigned_lit in KY by (clear - HWY HY; lia); clear - KY; lia). clear KY.
        step. rewrite (unsigned_lit (Z.of_nat top)) by (unfold top; clear - TOPZ; lia). rewrite (bn_swrap32_small (Z.of_nat top + -1)) by (unfold top; clear - TOPZ; lia).
        step. if_cases KI; zify_cond KI.
        +
          assert (NI : i <> (top - 1)%nat) by (rewrite ?unsigned_lit in KI by (unfold top in *; clear - TOPZ IZ; lia); clear - KI TOPZ; lia). clear KI.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
          apply evt_done.
          eapply (EPI Σ (setbn rx (sw_bn bx w) ls) m5 OW 0);
            [ apply ENVF; [exact MU4 | exact WM4 | exact ST3 | exact MI3 | exact FR3]
            | apply CLOSE; [| exact U4 | exact MU4 | exact WM4]
            | unfold MC; clear; lia | intros q0 A0 n0 Hq0 _; exact Hq0 ].
          rewrite (ECELL top); [exact BN3|]. apply sw_top_keep. right. rewrite ESI. exact NI.
        +
          assert (EI : i = (top - 1)%nat) by (rewrite ?unsigned_lit in KI by (unfold top in *; clear - TOPZ IZ; lia); clear - KI TOPZ; lia). clear KI.
          shl_with ACX ALX. chk0.
          step. step.

          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
          apply evt_done.
          eapply (EPI Σ (setbn rx (sw_bn bx w) ls) m5 OW 0);
            [ apply ENVF; [exact MU4 | exact WM4 | assumption | assumption | exact FR3]
            | apply CLOSE; [| assumption | exact MU4 | exact WM4]
            | unfold MC; clear; lia | intros q0 A0 n0 Hq0 _; exact Hq0 ].
          rewrite (ECELL i); [exact BN3|]. rewrite EI. apply sw_top_dec; [rewrite ESI, NTHI; clear - EY; lia| rewrite ESI; exact EI]. }

    assert (EBUF : buf = d0 :: la ++ skipn top buf) by (rewrite <- (firstn_skipn top buf) at 1; rewrite HFS; reflexivity).
    assert (LRS : length (skipn top buf) = (bn_dmax bx - top)%nat) by (rewrite length_skipn; reflexivity).
    assert (NTH0 : nth_error (wlimbs buf) (Z.to_nat 0) = Some (Z_to_bv 64 d0)) by (apply (wlimbs_nth buf 0); clear - TOPD ET; unfold top in *; lia).
    pose proof (u64arr_read bgasegs m2 Dx _ 0 _ (wa Dx) Ux NTH0 ltac:(clear; lia) ltac:(f_equal; clear; lia)) as RD0.

    lazymatch goal with |- evt _ ?Q _ =>
      assert (C08 : forall q11 q15 q16 : word,
        evt bgasegs Q (MS (mkR (Z_to_bv 64 2316624) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 TP_A) y0 y1 y2 sp (Z_to_bv 64 w) (Z_to_bv 64 (ax + 8))
                                q11 (Z_to_bv 64 (ax ≫ 3)) (Z_to_bv 64 ((ax + 8) ≫ 3 + SHB)) (Z_to_bv 64 (Z.of_nat top)) q15 q16 y10
                                (Z_to_bv 64 (ax + 16)) (Z_to_bv 64 ax) (Z_to_bv 64 SHB) (Z_to_bv 64 ((ax + 16) ≫ 3 + SHB))
                                s6 s7 s8 s9 s10 s11 y11 y12 y13 y14) F (Z_to_bv 64 0x235a68) fc None m2 (seg_rom bgasegs))) end.
    { intros q11 q15 q16.

      step. shl_with ACX ALX. chk0.
      step.
      do 2 step. shl_limb ACDX ALDX BDX 0. chk0.
      step.

      step. if_cases KG; zify_cond KG.
      -
        assert (GE : w <= d0) by (rewrite ?unsigned_lit in KG by (clear - HW Hd0 Hd1; lia); clear - KG; lia). clear KG.
        rewrite HFS, sub_word_limbs_ge in ESW by exact GE. injection ESW as <- <-.
        step.
        setreg 11%Z (Z_to_bv 64 (Dx + 8 * Z.of_nat 0)) ltac:(f_equal; clear; lia).

        eapply (FIN m2 [] (la ++ skipn top buf) d0 w);
          [ rewrite ESB; reflexivity | reflexivity | clear - HW NW GE; lia | clear - Hd1; lia | cbn [app]; rewrite <- EBUF; exact Ux | exact BNx | exact FR2 | exact ST2 | exact MI2 | exact MU3 | exact WM3 ].
      -
        assert (LT : d0 < w) by (rewrite ?unsigned_lit in KG by (clear - HW Hd0 Hd1; lia); clear - KG; lia). clear KG.
        assert (LV1 : 1 <= lval la) by (clear - HMAG LT LAN Hd0; lia).
        do 3 step. rewrite ?(unsigned_lit w) by (clear - HW; lia). rewrite ?(unsigned_lit d0) by (clear - Hd0 Hd1; lia).

        setreg 5%Z (Z_to_bv 64 (subw d0 w)) ltac:(symmetry; replace (d0 + - w) with (d0 - w) by (clear; lia); apply Z_to_bv_subw).
        assert (HSV : 0 <= subw d0 w < 18446744073709551616) by (unfold subw; rewrite BW_lit; apply Z.mod_pos_bound; clear; lia).
        setreg 11%Z (Z_to_bv 64 (Dx + 8 * Z.of_nat (length (@nil Z)))) ltac:(f_equal; cbn [length]; clear; lia).
        setreg 15%Z (Z_to_bv 64 (Z.of_nat (length (@nil Z)))) ltac:(reflexivity).
        setreg 16%Z (Z_to_bv 64 (shad (Dx + 8 * Z.of_nat (length (@nil Z))))) ltac:(f_equal; unfold shad; cbn [length]; rewrite ?Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3) with 8; f_equal; f_equal; clear; lia).
        assert (OFFD : offshW [(Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]) by (cbn [offshW]; unfold SHLO, SHHI; clear - OFDX; lia).
        pose proof (munch_refl [(Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]%Z m2) as MUL. pose proof (wmono_refl bgasegs m2) as WML.

        eapply (sw_loopA _ F fc) with (D := Dx) (n := Z.of_nat (bn_dmax bx)) (m0 := m2) (rest := skipn top buf) (la := la) (pre := []) (x := d0) (v := subw d0 w) (m1 := m2);
          [ constructor | exact Lla | apply limbs_skipn; exact OKx1 | exact HSV | exact LV1
          | cbn [length]; rewrite LLA, LRS; clear - OKx2 OKx3 ET; unfold top in *; lia
          | cbn [length]; rewrite LLA, LRS; clear - OKx2 ET; unfold top in *; lia
          | exact ACDX | exact ALDX | exact BDX | exact OFFD | exact MUL | exact WML | cbn [app]; rewrite <- EBUF; exact Ux | exact MI2 | ].
        intros m3 zs y la2 ELA HZ HY U3 MUl3 WM3' MI3. cbn [app length] in U3 |- *.
        assert (LZ : (1 + length zs + 1 + length la2 = top)%nat) by (clear - ELA LLA ET; apply (f_equal (@length Z)) in ELA; rewrite length_app in ELA; cbn [length] in ELA; unfold top in *; lia).
        rewrite HFS, sub_word_limbs_lt, ELA, sub_word_limbs_zeros in ESW by (first [exact LT | exact HZ | clear - HY; lia]). cbn [fst snd] in ESW. injection ESW as <- <-.
        eapply (rw_cells_transport bgasegs _ m2 m3) in FR2; [| exact MUl3 | exact WM3' | cbn; unfold BnHeapA.ACEIL in *; clear - DxC CEIL LO'; lia].
        eapply (rw_cells_transport bgasegs _ m2 m3) in BNx; [| exact MUl3 | exact WM3' | cbn; clear - SEPxx; lia].
        eapply (stk_transport_disjoint bgasegs _ m2 m3) in ST2; [| exact MUl3 | exact WM3' | cbn [disjoint_from]; unfold BnHeapA.ACEIL in *; clear - DxC CEIL LO'; lia].
        assert (MUT : munch [(bv_unsigned sp + -64, bv_unsigned sp); (ax, ax + 24); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]%Z m2 m3).
        { eapply munch_weaken; [| exact MUl3]. unfold sub_fp; cbn [outside]; intros x Hx. clear - Hx. lia. }
        clear MU3 WM3.
        do 3 step.

        eapply (FIN m3 (subw d0 w :: repeat 18446744073709551615 (length zs)) (la2 ++ skipn top buf) y 1);
          [ rewrite ESB; cbn [app]; rewrite <- app_assoc; reflexivity | cbn [length]; rewrite repeat_length; reflexivity | clear - HY; lia | clear - HY; lia
          | cbn [app]; exact U3 | exact BNx | exact FR2 | exact ST2 | exact MI3 | exact MUT | exact WM3' ]. }

    step. if_cases K1; zify_cond K1; [exact (C08 _ _ _)|].

    step. shl_with ACX ALX. chk0.
    step.
    do 2 step. shl_limb ACDX ALDX BDX 0. chk0.
    step.
    step. if_cases K2; zify_cond K2; [exact (C08 _ _ _)|].
    exfalso. rewrite ?unsigned_lit in K1, K2 by (unfold top in *; clear - TOPZ HW Hd0 Hd1; lia).
    assert (E1 : top = 1%nat) by (clear - K1; lia). rewrite E1 in Hcase. cbn [Nat.eqb andb] in Hcase. apply Z.ltb_ge in Hcase. clear - Hcase K2. lia.
Qed.

End WithRT.
