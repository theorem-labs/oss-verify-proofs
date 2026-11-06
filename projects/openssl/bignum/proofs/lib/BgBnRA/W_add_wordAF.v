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
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR2 Require W_add_word.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import BnAKitAF BnCallAF W_callsAF W_expandAF ShiftKitAF W_set_wordAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import ExpKitAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BN_ADD_WORD : Z := 0x235698.
Definition BN_ADD_WORD_STACK : Z := 80 + BN_WEXPAND_STACK.

Local Notation add_word_hi := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_add_word.add_word_hi.
Local Notation wlimbs_upd := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_add_word.wlimbs_upd.
Local Notation wlimbs_nth := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_add_word.wlimbs_nth.
Local Notation add_word_limbs_cons := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_add_word.add_word_limbs_cons.
Local Notation add_word_limbs_0 := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_add_word.add_word_limbs_0.
Local Notation add_word_limbs_length := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_add_word.add_word_limbs_length.
Local Notation add_word_limbs_limbs := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_add_word.add_word_limbs_limbs.
Local Notation addw_carry := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_add_word.addw_carry.
Local Notation Z_to_bv_addw := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_add_word.Z_to_bv_addw.
Local Notation aw_bound_machine := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_add_word.aw_bound_machine.

Lemma aw_loopA : forall (Q : machine_state -> Prop) (F : bvmap 5 word) (fc : bv 32)
    (x1 x2 gp tp x5 x6 x7 x8 x9 x11 x15 x16 x17 x20 x22 x23 s9 s10 s11 x28 x29 x30 x31 : word)
    (ax D n : Z) (c1 c2 c3 c4 : word) (top : nat) (m0 : mem) (rest la pre : list Z) (m1 : mem) (wi : Z) (x12 x13 x14 : word),
  limbs pre -> limbs la -> limbs rest -> 0 < wi < 18446744073709551616 -> (length pre + length la = top)%nat -> Z.of_nat (top + length rest) < 2 ^ 28 ->
  n = Z.of_nat (top + length rest) ->
  rw_cells bgasegs m1 ax [C8 (Z_to_bv 64 D); C4 c1; C4 c2; C4 c3; C4 c4] -> (ax + 24 <= D \/ D + 8 * n <= ax) ->
  acc bgasegs m0 ax 24 -> ax mod 8 = 0 -> (0 < ax /\ ax + 24 <= 140737488355328) ->
  acc bgasegs m0 D (8 * n) -> D mod 8 = 0 -> (0 <= D /\ D + 8 * n <= 140737488355328) -> offshW [(D, D + 8 * n)] ->
  munch [(D, D + 8 * n)] m0 m1 -> wmono bgasegs m0 m1 ->
  u64arr bgasegs m1 D (wlimbs (pre ++ la ++ rest)) -> mem_inv bgasegs m1 -> x11 = Z_to_bv 64 (8 * Z.of_nat top + 8) ->
  (forall (m' : mem) (y13 y14 : word),
      u64arr bgasegs m' D (wlimbs (pre ++ fst (add_word_limbs la wi) ++ rest)) ->
      rw_cells bgasegs m' ax [C8 (Z_to_bv 64 D); C4 c1; C4 c2; C4 c3; C4 c4] ->
      munch [(D, D + 8 * n)] m0 m' -> wmono bgasegs m0 m' -> mem_inv bgasegs m' ->
      snd (add_word_limbs la wi) <> 0 ->
      evt bgasegs Q (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (8 * Z.of_nat top)) x11 (Z_to_bv 64 (8 * Z.of_nat top + 8)) y13 y14 x15 x16 x17
                              (Z_to_bv 64 ax) (Z_to_bv 64 (snd (add_word_limbs la wi))) x20 (Z_to_bv 64 SHB) x22 x23 (Z_to_bv 64 (ax ≫ 3 + SHB)) s9 s10 s11 x28 x29 x30 x31)
                         F (Z_to_bv 64 0x235804) fc None m' (seg_rom bgasegs))) ->
  (forall (m' : mem) (y10 y12 y13 y14 : word),
      u64arr bgasegs m' D (wlimbs (pre ++ fst (add_word_limbs la wi) ++ rest)) ->
      rw_cells bgasegs m' ax [C8 (Z_to_bv 64 D); C4 c1; C4 c2; C4 c3; C4 c4] ->
      munch [(D, D + 8 * n)] m0 m' -> wmono bgasegs m0 m' -> mem_inv bgasegs m' ->
      snd (add_word_limbs la wi) = 0 ->
      evt bgasegs Q (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 y10 x11 y12 y13 y14 x15 x16 x17
                              (Z_to_bv 64 ax) (Z_to_bv 64 1) x20 (Z_to_bv 64 SHB) x22 x23 (Z_to_bv 64 (ax ≫ 3 + SHB)) s9 s10 s11 x28 x29 x30 x31)
                         F (Z_to_bv 64 0x2357fc) fc None m' (seg_rom bgasegs))) ->
  evt bgasegs Q (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (8 * Z.of_nat (length pre))) x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 ax) (Z_to_bv 64 wi) x20 (Z_to_bv 64 SHB) x22 x23 (Z_to_bv 64 (ax ≫ 3 + SHB)) s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x2357bc) fc None m1 (seg_rom bgasegs)).
Proof.
  intros Q F fc x1 x2 gp tp x5 x6 x7 x8 x9 x11 x15 x16 x17 x20 x22 x23 s9 s10 s11 x28 x29 x30 x31 ax D n c1 c2 c3 c4 top m0 rest.
  induction la as [|x la IH]; intros pre m1 wi x12 x13 x14 Lpre Lla Lrest HW LEN L28 EN BN SEP ACX ALX BX ACD ALD BD OFF MU WM U MI -> KC KN.
  -
    pose proof (u64arr_bound bgasegs _ _ _ U) as UB. rewrite wlimbs_len, !length_app in UB. cbn [length] in LEN, UB.
    step. step. if_cases KE; zify_cond KE; [| exfalso; rewrite ?unsigned_lit in KE by lia; lia]. clear KE.
    replace (length pre) with top by lia.
    eapply KC; [exact U| exact BN| exact MU| exact WM| exact MI| cbn; lia].
  - pose proof (u64arr_bound bgasegs _ _ _ U) as UB. rewrite wlimbs_len, !length_app in UB. cbn [length] in LEN, UB.
    assert (LM : Z.of_nat (length (wlimbs (pre ++ (x :: la) ++ rest))) = Z.of_nat (top + length rest)) by (rewrite wlimbs_len, !length_app; cbn [length]; lia).
    apply limbs_cons_inv in Lla. destruct Lla as [[Hx0 Hx1] Lla]. rewrite BW_lit in Hx1.
    unfold SHLO, SHHI in OFF.
    assert (BX' : 0 <= ax < 140737488355328) by lia.
    step. step. if_cases KE; zify_cond KE; [exfalso; rewrite ?unsigned_lit in KE by lia; lia|]. clear KE.

    shl_with ACX ALX. chk0.
    step. step.

    do 2 step. shl_limb ACD ALD BD (Z.of_nat (length pre)). chk0.
    assert (NTH : nth_error (wlimbs (pre ++ (x :: la) ++ rest)) (Z.to_nat (Z.of_nat (length pre))) = Some (Z_to_bv 64 x)).
    { replace x with (nth (length pre) (pre ++ (x :: la) ++ rest) 0) at 2 by (rewrite app_nth2, Nat.sub_diag by lia; reflexivity).
      apply wlimbs_nth. rewrite !length_app. cbn [length]. lia. }
    pose proof (u64arr_read bgasegs m1 D _ (Z.of_nat (length pre)) _ (wa (D + 8 * Z.of_nat (length pre))) U NTH ltac:(lia) eq_refl) as RD.
    step. clear RD. step. setreg 14%Z (Z_to_bv 64 (addw x wi)) ltac:(symmetry; apply Z_to_bv_addw).

    pose proof (conj (Z.mod_pos_bound (x + wi) BW ltac:(rewrite BW_lit; lia)) I) as HS. unfold addw in HS |- *. rewrite BW_lit in HS |- *.
    set (sx := (x + wi) mod 18446744073709551616) in *. destruct HS as [HS _].
    assert (IDX : 0 <= Z.of_nat (length pre) < Z.of_nat (length (wlimbs (pre ++ (x :: la) ++ rest)))) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (u64arr_store_ok bgasegs mx D _ (Z.of_nat (length pre)) (wa (D + 8 * Z.of_nat (length pre))) U IDX eq_refl) as SOKW;
      pose proof (u64arr_write bgasegs mx D _ (Z.of_nat (length pre)) (Z_to_bv 64 sx) U IDX) as U2 end.
    rewrite Nat2Z.id, wlimbs_upd in U2 by (rewrite !length_app; cbn [length]; lia).
    replace (upd (pre ++ (x :: la) ++ rest) (length pre) sx) with ((pre ++ [sx]) ++ la ++ rest) in U2
      by (unfold upd, splice; rewrite firstn_app, Nat.sub_diag, firstn_O, firstn_all2, app_nil_r by lia;
          rewrite skipn_app, skipn_all2 by lia; replace (length pre + 1 - length pre)%nat with 1%nat by lia; cbn [skipn app]; rewrite <- app_assoc; reflexivity).
    clear U. step. store_done.
    step. step.
    step.

    pose proof (addw_carry x wi ltac:(lia) ltac:(lia)) as EC. unfold addw in EC. rewrite BW_lit in EC. fold sx in EC.
    rewrite (add_word_limbs_cons x la wi) in KC, KN by lia. cbn [fst snd] in KC, KN. unfold addw in KC, KN. rewrite BW_lit in KC, KN. fold sx in KC, KN.
    rewrite <- EC in KC, KN.
    if_cases KCY; zify_cond KCY.
    +
      replace (sx <? x) with true in KC, KN by (symmetry; apply Z.ltb_lt; rewrite ?unsigned_lit in KCY by lia; exact KCY).
      replace (8 * Z.of_nat (length pre) + 8) with (8 * Z.of_nat (length (pre ++ [sx]))) by (rewrite length_app; cbn [length]; lia).
      eapply (IH (pre ++ [sx])); [apply limbs_app; [exact Lpre| constructor; [unfold limb; rewrite BW_lit; lia| constructor]] | exact Lla | exact Lrest | lia
        | rewrite length_app; cbn [length]; lia | exact L28 | exact EN | eassumption | exact SEP | exact ACX | exact ALX | exact BX | exact ACD | exact ALD | exact BD
        | cbn [offshW]; unfold SHLO, SHHI; exact OFF | eassumption | eassumption | exact U2 | assumption | reflexivity | |].
      * intros m' y13 y14 U' BN' MU' WM' MI' NC.
        eapply KC; [rewrite <- app_assoc in U'; exact U'| exact BN'| exact MU'| exact WM'| exact MI'| exact NC].
      * intros m' y10 y12 y13 y14 U' BN' MU' WM' MI' NC.
        eapply KN; [rewrite <- app_assoc in U'; exact U'| exact BN'| exact MU'| exact WM'| exact MI'| exact NC].
    +
      replace (sx <? x) with false in KN by (symmetry; apply Z.ltb_ge; rewrite ?unsigned_lit in KCY by lia; lia). rewrite add_word_limbs_0 in KN. cbn [fst snd] in KN.
      eapply KN; [rewrite <- app_assoc in U2; exact U2| eassumption| eassumption| assumption| assumption| reflexivity].
Qed.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma BN_add_word_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (rx : bnref) (ax w : Z),
  bn_preA Σ ls m OW LB PL EA sp lo BN_ADD_WORD_STACK MC ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_ADD_WORD (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> ref_at ls OW PL rx ax -> wref PL rx -> a0 = wz ax -> a1 = wz w -> 0 <= w < 2^64 ->
  implA (BN_add_word (tree_ops bptr) rx w ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC
              (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = wz 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx ls) <> Some q -> In (q, A, n) OW')))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_ADD_WORD) fc None m (seg_rom bgasegs)).
Proof.
  intros until w. intros PRE UW CTX -> HAx WRx -> -> HW.
  pose proof (proj1 WRx : not_one rx) as NROx.
  pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
  pose proof LO as LO'. unfold BN_ADD_WORD_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO'.
  unfold BN_ADD_WORD, MallocRep.wz.
  change (2 ^ 64) with 18446744073709551616 in HW.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1' & C2' & C3'). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 80, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HAx) as HVx.
  set (bx := getbn rx ls) in *.
  assert (LBX : length (bn_buf bx) = bn_dmax bx) by reflexivity.
  unfold BN_add_word, bbind, bget, bset, bret. cbn [bind ret tree_ops tbind fst snd]. fold bx.
  apply implA_from_evt.
  carve_frame 80%nat ST.
  do 12 step. step.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
  assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -80, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -80, bv_unsigned sp)]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
  pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
  assert (EV : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -80) s0 ra (Some ras) MC Σ ls OW m
                 [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] 0 Σ ls m1 OW).
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
                       (q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q28 q29 q30 q31 : word),
      cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -80) s0 ra (Some ras) MC Σ ls OW m
            [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] used Σ1 ls1 m2 OW2 ->
      lib_state ls1 m2 OW2 PL EA -> used <= MC ->
      (forall q A n, In (q, A, n) OW -> bn_d bx <> Some q -> In (q, A, n) OW2) ->
      implA (TRet (tt, ls1)) Σ1
        (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC
                  (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = Z_to_bv 64 1 /\ (forall q A n, In (q, A, n) OW -> bn_d bx <> Some q -> In (q, A, n) OW')))
        (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 TP_A) q5 q6 q7 sp (Z_to_bv 64 1) q10 q11 q12 q13 q14 q15 q16 q17
                 q18 q19 q20 q21 q22 q23 q24 s9 s10 s11 q28 q29 q30 q31)
            FT (Z_to_bv 64 0x23585c) fcT None m2 (seg_rom bgasegs))).
  { intros Σ1 ls1 m2 OW2 used FT fcT q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q28 q29 q30 q31 EV1 LS2 USED BST.
    clear MU WM ST MI FR HWL WOK LS1 HEAP1 EV OK OFF SHB1 SHB2 HEAP LS PARTS PRE UW HVx.
    pose proof EV1 as (OK1 & HEAP2 & ST2 & MI2 & AXP2 & CR2 & CNT2 & RS2 & FR2 & FSZ2 & UW2).
    cbn [app] in FR2.
    apply implA_ret_evt.
    step. do 10 step. release_frame FR2 ST2 (bv_unsigned sp). step. step.
    apply evt_done.
    unfold bn_postA. do 17 eexists. exists m2, OW2, PL. split; [reflexivity|]. cbn [fst snd].
    split; [exact HEAP2|]. split; [exact LS2|]. split; [exact ST2|]. split; [exact MI2|]. split; [exact AXP2|].
    split; [clear - CR2 USED; lia|]. split; [exact CNT2|]. split; [exact RS2|].
    split; [reflexivity|]. split; [reflexivity| exact BST]. }

  step. if_cases KW; zify_cond KW.
  -
    assert (EW : w = 0) by (rewrite ?unsigned_lit in KW by (clear - HW; lia); clear - KW; lia).
    replace (w =? 0) with true by (symmetry; apply Z.eqb_eq; exact EW).
    apply evt_done.
    eapply (EPI Σ ls m1 OW 0 F fc); [exact EV | exact LS1 | unfold MC; clear; lia | intros q0 A0 n0 Hq0 _; exact Hq0].
  -
    assert (NW : w <> 0) by (rewrite ?unsigned_lit in KW by (clear - HW; lia); clear - KW; lia).
    replace (w =? 0) with false by (symmetry; apply Z.eqb_neq; exact NW).
    cbn [tbind fst snd]. fold bx.

    do 7 step.

    assert (LOF16 : lo <= bv_unsigned sp + -80 - 16) by (clear - LO'; lia).
    eapply (is_zero_callA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -80) s0 ra (Some ras) MC Σ ls OW m LOF16) with (r := rx) (ar := ax);
      [exact EV | exact LS1 | exact HAx | exact NROx |].
    intros m2 y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 EV2 LS2.
    rewrite (ret_pc_even 2316012) by (clear; lia).
    fold bx.
    clear MU WM OFF SHB1 SHB2 HEAP LS PARTS ST MI FR HWL WOK LS1 HEAP1 EV OK.
    pose proof EV2 as (OK2 & HEAP2 & ST2 & MI2 & _ & _ & _ & _ & FR2 & FSZ2 & _). cbn [app] in FR2.
    destruct (bn_top bx =? 0)%nat eqn:ET; cbv beta; fold bx; step; if_cases KT; zify_cond KT; try (exfalso; rewrite ?unsigned_lit in KT by (clear; cbn; lia); cbn in KT; clear - KT; lia).
    +
      clear KT.
      step. step. do 10 step. release_frame FR2 ST2 (bv_unsigned sp). step. step.

      apply evt_done.
      destruct (cenv_tailA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -80) s0 ra (Some ras) MC Σ ls OW m _ _ _ _ _ _ BN_SET_WORD_STACK MC ras
                  ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  (fun (_ : unit) (_ : bstate bptr) (OW' : list block) (PL' : placement) (a0' : word) =>
                     PL' = PL /\ a0' = wz 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx ls) <> Some q -> In (q, A, n) OW'))
                  EV2 LS2 ST2 ltac:(clear - LO'; unfold BN_SET_WORD_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; lia)
                  ltac:(unfold MC; clear; lia) eq_refl) as (PREX & UWX & POSTX).
      rewrite Z_to_bv_bv_unsigned in PREX, POSTX.
      eapply implA_mono.
      { eapply (BN_set_word_walkA ra sp) with (lo := lo) (ras := ras) (rx := rx) (ax := ax) (w := w) (OW := OW) (LB := LB) (PL := PL) (EA := EA);
          [exact PREX | exact UWX | exact (uk_ctx_tail _ _ _ E_BN_add_word_235540 CTX) | reflexivity | exact HAx | exact WRx | reflexivity | reflexivity | exact HW]. }
      cbv beta. intros r Σ' ms' PO. apply POSTX. exact PO.
    +
      apply Nat.eqb_neq in ET. clear KT.

      destruct (bn_neg bx) eqn:ENG.
      { apply evt_done. unfold bunr. cbn [unreachable tree_ops]. apply implA_unr. }

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
      rewrite ENG in BNx. cbn [Z.b2z] in BNx.
      assert (X0 : 0 < ax) by (clear - AX0 Rx1; lia).
      assert (XC : ax + 24 <= BnHeapA.ACEIL) by (clear - AXC Rx2; lia).
      assert (HDx : exists px, bn_d bx = Some px /\ In (px, Dx, 8 * Z.of_nat (bn_dmax bx)) OW).
      { unfold BnRepDefs.bn_arr in ARRo. destruct (bn_d bx) as [px|]; [exists px; split; [reflexivity| exact (proj1 ARRo)]|].
        exfalso. destruct ARRo as [_ E]. unfold bn_dmax in OKx2. rewrite E in OKx2. cbn in OKx2. clear - OKx2 ET. lia. }
      destruct HDx as (px & Edx & Hinpx).
      assert (TOPZ : 0 < Z.of_nat (bn_top bx) <= Z.of_nat (bn_dmax bx) /\ Z.of_nat (bn_dmax bx) <= 512) by (clear - ET OKx2 OKx3; unfold bn_dmax in *; lia).
      assert (BDX : 0 <= Dx /\ Dx + 8 * Z.of_nat (bn_dmax bx) <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - Dx0' DxC C1' C2' C3'; lia).
      assert (BAX : 0 < ax /\ ax + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - X0 XC C1' C2' C3'; lia).
      pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp); (ax, ax + 24); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]%Z m2) as MU3.
      pose proof (wmono_refl bgasegs m2) as WM3.
      assert (OFF3 : offshW [(bv_unsigned sp + -80, bv_unsigned sp); (ax, ax + 24); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]).
      { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. clear - OFX OFDX SPR LO' CEIL C1' C2' C3'. lia. }
      cbn [Z.b2z].

      do 3 step. shl_with ACX ALX. chk0.
      step. step. if_cases KN; zify_cond KN; [| exfalso; rewrite ?unsigned_lit in KN by (clear; lia); cbn in KN; clear - KN; lia]. clear KN.

      do 3 step. shl_with ACX ALX. chk0.
      step. step. rewrite (sx32_small (Z.of_nat (bn_top bx))) by (clear - TOPZ; lia).
      do 7 step.

      rewrite aw_bound_machine by (clear - TOPZ; lia).
      setreg 24%Z (Z_to_bv 64 (ax ≫ 3 + SHB)) ltac:(f_equal; rewrite unsigned_lit by (clear - BAX; lia); reflexivity).

      pose proof (add_word_limbs_spec (firstn (bn_top bx) (bn_buf bx)) w (limbs_firstn _ _ OKx1) ltac:(rewrite BW_lit; exact HW)) as AWS.
      destruct (add_word_limbs (firstn (bn_top bx) (bn_buf bx)) w) as [l w'] eqn:EAW.
      destruct AWS as (Ll & LENl & Lw' & _). rewrite firstn_length_le in LENl by (clear - OKx2 LBX; lia). rewrite BW_lit in Lw'.
      cbn [tbind fst snd]. fold bx.
      set (nb := splice (bn_buf bx) 0 l).
      assert (Enb : nb = l ++ skipn (bn_top bx) (bn_buf bx)) by (subst nb; unfold splice; rewrite firstn_O, LENl; reflexivity).
      assert (Lnb : length nb = bn_dmax bx) by (subst nb; rewrite splice_length; [exact LBX| rewrite LENl, LBX; clear - OKx2; lia]).
      assert (LMnb : limbs nb) by (subst nb; apply splice_limbs; [exact OKx1| exact Ll]).
      set (ls2 := setbn rx (bn_with_buf bx nb) ls).
      assert (EBL : length (bn_blocks (bn_with_buf bx nb)) = length (bn_blocks (getbn rx ls))).
      { fold bx. unfold bn_blocks, bn_dmax, bn_with_buf. cbn [bn_d bn_buf]. destruct (bn_d bx); reflexivity. }
      assert (EBUF : bn_buf bx = firstn (bn_top bx) (bn_buf bx) ++ skipn (bn_top bx) (bn_buf bx)) by (symmetry; apply firstn_skipn).
      assert (OFFD : offshW [(Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]) by (cbn [offshW]; unfold SHLO, SHHI; clear - OFDX; lia).
      pose proof (munch_refl [(Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]%Z m2) as MUL. pose proof (wmono_refl bgasegs m2) as WML.
      assert (LFS : length (firstn (bn_top bx) (bn_buf bx)) = bn_top bx) by (apply firstn_length_le; clear - OKx2 LBX; lia).
      assert (LRS : length (skipn (bn_top bx) (bn_buf bx)) = (bn_dmax bx - bn_top bx)%nat) by (rewrite length_skipn; reflexivity).

      assert (CLS : forall m3, u64arr bgasegs m3 Dx (wlimbs nb) ->
                     rw_cells bgasegs m3 ax [C8 (Z_to_bv 64 Dx); C4 (Z_to_bv 64 (Z.of_nat (bn_top bx))); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax bx))); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (bn_flags bx))] ->
                     munch [(Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]%Z m2 m3 -> wmono bgasegs m2 m3 -> mem_inv bgasegs m3 ->
                     cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -80) s0 ra (Some ras) MC Σ ls OW m
                           [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] 0 Σ ls2 m3 OW /\ lib_state ls2 m3 OW PL EA).
      { intros m3 U3 BN3 MU3' WM3' MI3.
        assert (FR3 : rw_cells bgasegs m3 (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
        { eapply rw_cells_transport; [exact FR2 | exact MU3' | exact WM3' |]. cbn. unfold BnHeapA.ACEIL in *. clear - DxC CEIL LO'. lia. }
        assert (ST3 : stk bgasegs m3 lo (bv_unsigned sp + -80)).
        { eapply (stk_transport_disjoint bgasegs _ m2 m3); [exact ST2 | exact MU3' | exact WM3' |]. cbn [disjoint_from]. unfold BnHeapA.ACEIL in *. clear - DxC CEIL LO'. lia. }
        assert (HWLT : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]).
        { constructor; [| constructor]. right; left; exists (px, Dx, 8 * Z.of_nat (bn_dmax bx)); cbn [blk_addr blk_size fst snd]; split; [exact Hinpx| clear; lia]. }
        assert (WOKc : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) [rx]) [(Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]).
        { constructor; [| constructor].
          eapply (w_limbs OW LB ls PL EA (bv_unsigned sp) false [rx] _ rx px Dx); [left; reflexivity| exact HVx| exact Edx| exact Hinpx| cbn [fst snd]; clear; lia| cbn [fst snd]; fold bx; clear; lia]. }
        split.
        - subst ls2. apply cenv_setbnA; [| exact HVx | exact EBL].
          eapply cenv_silentA; [exact EV2 | exact LS2 | exact MU3' | exact WM3' | exact HWLT | exact ST3 | exact MI3 | cbn [app]; exact FR3 | exact FSZ2].
        - subst ls2. unfold lib_state. eapply (lib_state_close [] ls m3 OW PL EA rx ax); [| exact ND| exact HAx| exact NROx| | |].
          + eapply (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP); [exact HEAP2 | exact LSH | exact MU3' | exact WM3' | exact FROK | exact WOKc].
          + exists Dx. split.
            * unfold bn_cells, BnRepDefs.bn_cells, bn_dmax, bn_with_buf, MallocRep.wz. cbn [bn_top bn_buf bn_neg bn_flags bn_d]. rewrite Lnb, ENG. cbn [Z.b2z]. exact BN3.
            * apply (fun ARRnb__ => bn_arr_of_nofr PL rx m3 OW Dx _ PWF NOFR NROx ARRnb__ ltac:(solve_nbuf)). unfold BnRepDefs.bn_arr, bn_dmax, bn_with_buf. cbn [bn_d bn_buf]. rewrite Edx, Lnb. split; [exact Hinpx| exact U3].
          + unfold bg_ok, bn_dmax, bn_with_buf. cbn [bn_buf bn_top bn_flags]. rewrite Lnb. unfold BG_DMAX in *.
            split; [exact LMnb|]. split; [exact OKx2|]. split; [clear - OKx3; unfold bn_dmax in *; lia| exact OKx4].
          + apply ids_ok_setbn_same; [exact IDS| exact HVx|]. unfold bn_blocks, bn_dmax, bn_with_buf. cbn [bn_d bn_buf]. rewrite Lnb. reflexivity. }

      eapply (aw_loopA _ F fc) with (ax := ax) (D := Dx) (n := Z.of_nat (bn_dmax bx)) (top := bn_top bx) (m0 := m2)
                                    (rest := skipn (bn_top bx) (bn_buf bx)) (la := firstn (bn_top bx) (bn_buf bx)) (pre := []) (m1 := m2) (wi := w);
        [ constructor | apply limbs_firstn; exact OKx1 | apply limbs_skipn; exact OKx1 | clear - HW NW; lia | cbn [length]; rewrite LFS; reflexivity
        | rewrite LRS; clear - TOPZ; lia | rewrite LRS; clear - TOPZ; lia | exact BNx | exact SEPxx
        | exact ACX | exact ALX | exact BAX | exact ACDX | exact ALDX | exact BDX | exact OFFD | exact MUL | exact WML
        | cbn [app]; rewrite <- EBUF; exact Ux | exact MI2 | reflexivity | | ].
      *
        intros m3 v13 v14 U3 BN3 MU3' WM3' MI3 NC. cbn [app] in U3. rewrite EAW in U3, NC |- *. cbn [fst snd] in U3, NC |- *. rewrite <- Enb in U3.
        replace (w' =? 0) with false by (symmetry; apply Z.eqb_neq; exact NC).
        destruct (CLS m3 U3 BN3 MU3' WM3' MI3) as (EV3 & LS3).
        assert (RST2 : refs_stable ls OW ls2 OW) by (apply refs_stable_setbn).
        pose proof (ref_at_stable _ _ _ _ _ _ _ RST2 HAx) as HAx2.
        pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS3 HAx2) as HVx2.
        assert (ETOP2 : bn_top (getbn rx ls2) = bn_top bx) by (subst ls2; rewrite getbn_setbn_same by exact HVx; reflexivity).
        pose proof EV3 as (OK3 & HEAP3 & _).
        clear U3 BN3 MU3' WM3' MI3 MUL WML MU3 WM3 Ux BNx FR2 ST2 MI2 ACX ACDX LSH ARRx ARRo.
        step. rewrite (lts_signed (Z.of_nat (bn_top bx)) 0) by (clear - TOPZ; lia).
        if_cases KNEG; zify_cond KNEG; [exfalso; clear - KNEG; lia|]. clear KNEG.
        do 3 step.

        apply evt_done.
        eapply implA_bind.
        { eapply (bn_wexpand_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (r := rx) (a := ax) (words := (bn_top bx + 1)%nat) (OW := OW) (LB := LB) (PL := PL) (EA := EA);
            [| | | reflexivity | exact HAx2 | exact WRx | reflexivity
             | unfold MallocRep.wz; f_equal; rewrite ?(unsigned_lit (Z.of_nat (bn_top bx))) by (clear - TOPZ; lia); rewrite ?bn_swrap32_small by (clear - TOPZ; lia); clear; lia
             | clear - TOPZ; lia].
          - eapply cenv_preA; [exact EV3 | exact LS3 | unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO'; lia | clear; lia].
          - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV3).
          - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ (E_BN_add_word_23562c : uk_call BN_ADD_WORD 0x235814 BN_WEXPAND) CTX). }
        cbv beta. intros [u ls3] Σ3 ms3 PO.
        apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -80) MC Σ ls OW) in PO; [| exact OK3 | exact HEAP3].
        cbn [fst snd] in *.
        destruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & F3 & fc3 & m4 & OW4 & PL4 & -> & CP & (EPL & -> & HDM & WRES & BST4)).
        subst PL4. specialize (CP eq_refl).
        assert (E4 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -80) s0 ra (Some ras) MC Σ ls OW m
                       [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] (0 + MC) Σ3 ls3 m4 OW4 /\ lib_state ls3 m4 OW4 PL EA)
          by (eapply cenv_postA; [exact EV3 | exact CP]).
        destruct E4 as (EV4 & LS4).
        pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP) as RST4.
        rewrite (ret_pc_even 2316308) by (clear; lia).
        pose proof (ref_at_stable _ _ _ _ _ _ _ RST4 HAx2) as HAx4.
        assert (ETX : bn_top (getbn rx ls3) = bn_top bx) by (rewrite <- ETOP2; apply (wexpand_keeps_topA rx (bn_top bx + 1) ls2 ls3 rx WRES HVx2)).
        clear CP EV3 LS3 HEAP3 OK3 WRES.
        unfold bbind, bget, bset, bret. cbn [bind ret tree_ops tbind fst snd].

        pose proof EV4 as (OK4 & HEAP4 & ST4 & MI4 & _ & _ & _ & _ & FR4 & FSZ4 & _). cbn [app] in FR4.
        pose proof (AH_nodup_l _ _ _ _ HEAP4) as ND4.
        pose proof (lib_state_h_parts _ _ _ _ _ _ LS4) as PARTS4; pose proof PARTS4 as (WFS4 & PWF4 & IDS4 & PLB4 & ERRB4).
        pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS4 HAx4) as HVx4.
        destruct (lib_state_open [] ls3 m4 OW4 PL EA rx ax LS4 ND4 HAx4 ltac:(intros []) NROx) as ((Dr & BNr & ARRr) & (OKq1 & OKq2 & OKq3 & OKq4) & LSH4).
        destruct (bn_arr_facts_w ls3 OW4 PL EA (bv_unsigned sp) USTACK_TOP Σ3 LB m4 rx Dr HEAP4 PARTS4 FROK HVx4 WRx ARRr) as (Ur & LENr & Dr0 & DrC & DrI & DSEPr).
        set (br := getbn rx ls3) in *.
        pose proof (DSEPr rx ax HAx4) as SEPrr. fold br in SEPrr.
        destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP4 LS4 NOFR HAx4 NROx) as (ACR & ALR & OFR).
        pose proof ARRr as ARRq. apply (fun ARRnb__ => bn_arr_nofr PL rx m4 OW4 Dr _ PWF4 NOFR NROx ARRnb__ ltac:(solve_nbuf)) in ARRq.
        destruct (arr_shA _ _ _ _ _ _ HEAP4 ARRq) as (ACDR & ALDR & OFDR). fold br in ACDR, OFDR.
        unfold bn_cells, BnRepDefs.bn_cells in BNr. unfold BG_DMAX in OKq3. unfold MallocRep.wz in *. unfold SHLO, SHHI in *. rewrite ETX in BNr.
        assert (HDr : exists pr, bn_d br = Some pr /\ In (pr, Dr, 8 * Z.of_nat (bn_dmax br)) OW4).
        { unfold BnRepDefs.bn_arr in ARRq. fold br in ARRq. destruct (bn_d br) as [pr|]; [exists pr; split; [reflexivity| exact (proj1 ARRq)]|].
          exfalso. destruct ARRq as [_ E]. unfold bn_dmax in HDM. fold br in HDM. rewrite E in HDM. cbn in HDM. clear - HDM. lia. }
        destruct HDr as (pr & Edr & Hinpr).
        assert (LBR : length (bn_buf br) = bn_dmax br) by reflexivity.
        fold br in HDM.
        pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp); (ax, ax + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m4) as MU5.
        pose proof (wmono_refl bgasegs m4) as WM5.
        assert (OFF5 : offshW [(bv_unsigned sp + -80, bv_unsigned sp); (ax, ax + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
        { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. clear - OFR OFDR SPR LO' CEIL C1' C2' C3'. lia. }
        assert (BDR : 0 <= Dr /\ Dr + 8 * Z.of_nat (bn_dmax br) <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - Dr0 DrC C1' C2' C3'; lia).
        assert (HDMZ : Z.of_nat (bn_top bx) + 1 <= Z.of_nat (bn_dmax br)) by (clear - HDM; lia).
        assert (LENW : Z.of_nat (length (wlimbs (bn_buf br))) = Z.of_nat (bn_dmax br)) by (rewrite wlimbs_len; reflexivity).
        clear DSEPr DrI OFR OFDR SEPxx DxC Dx0' BDX Hinpx Edx Rx1 Rx2 Hinx Lnb LMnb Enb.
        apply implA_from_evt.
        zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by (clear - X0 XC C1' C2' C3'; unfold BnHeapA.ACEIL in *; lia). clear - KZ X0. lia. }
        clear KZ.

        shl_with ACR ALR. chk0.
        step. rewrite (sx32_small (Z.of_nat (bn_top bx))) by (clear - TOPZ; lia).
        step. step. replace (Z.of_nat (bn_top bx) + 1) with (Z.of_nat (bn_top bx + 1)) in BNr by (clear; lia).
        shl_with ACR ALR. chk0.
        step. step. step.
        setreg 10%Z (Z_to_bv 64 (Dr + 8 * Z.of_nat (bn_top bx))) ltac:(f_equal; rewrite ?(unsigned_lit (Z.of_nat (bn_top bx))) by (clear - TOPZ; lia); rewrite ?Z.shiftl_mul_pow2 by (clear; lia); rewrite ?unsigned_lit by (clear - TOPZ BDR; lia); clear; lia).
        do 2 step. shl_limb ACDR ALDR BDR (Z.of_nat (bn_top bx)). chk0.

        assert (IDX : 0 <= Z.of_nat (bn_top bx) < Z.of_nat (length (wlimbs (bn_buf br)))) by (rewrite wlimbs_len, LBR; clear - HDMZ; lia).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          pose proof (u64arr_store_ok bgasegs mx Dr _ (Z.of_nat (bn_top bx)) (wa (Dr + 8 * Z.of_nat (bn_top bx))) ltac:(eassumption) IDX eq_refl) as SOKW;
          pose proof (u64arr_write bgasegs mx Dr _ (Z.of_nat (bn_top bx)) (Z_to_bv 64 w') ltac:(eassumption) IDX) as U6 end.
        rewrite Nat2Z.id, (wlimbs_upd (bn_buf br) (bn_top bx)) in U6 by (rewrite LBR; clear - HDM; lia).
        clear Ur. step. store_done.
        step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
        apply evt_done.
        set (nb2 := upd (bn_buf br) (bn_top bx) w') in *.
        assert (Lnb2 : length nb2 = bn_dmax br) by (subst nb2; rewrite upd_length by (rewrite LBR; clear - HDM; lia); exact LBR).
        assert (LMnb2 : limbs nb2) by (subst nb2; apply upd_limbs; [exact OKq1| unfold limb, BW; exact Lw']).
        assert (HWL5 : Forall (w_lib ls3 OW4 PL lo (bv_unsigned sp)) [(bv_unsigned sp + -80, bv_unsigned sp); (ax, ax + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
        { constructor; [left; cbn; clear - LO'; lia|]. constructor; [w_lib_ref HAx4 NROx|].
          constructor; [right; left; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn [blk_addr blk_size fst snd]; split; [exact Hinpr| clear; lia]| constructor]. }
        assert (WOK5 : Forall (w_ok OW4 LB ls3 PL EA (bv_unsigned sp) [rx]) [(bv_unsigned sp + -80, bv_unsigned sp); (ax, ax + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
        { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; clear - LO' CEIL; lia|].
          constructor; [eapply (w_struct OW4 LB ls3 PL EA (bv_unsigned sp) false [rx] _ rx ax); [left; reflexivity| exact HAx4| exact NROx| cbn; clear; lia| cbn; clear; lia]|].
          constructor; [eapply (w_limbs OW4 LB ls3 PL EA (bv_unsigned sp) false [rx] _ rx pr Dr); [left; reflexivity| exact HVx4| exact Edr| exact Hinpr| cbn [fst snd]; clear; lia| cbn [fst snd]; fold br; clear; lia]| constructor]. }
        change (mkBN (bn_d br) (upd (bn_buf br) (bn_top bx) w') (bn_top bx + 1) (bn_neg br) (bn_flags br)) with (add_word_hi br (bn_top bx) w').
        assert (EBL5 : length (bn_blocks (add_word_hi br (bn_top bx) w')) = length (bn_blocks (getbn rx ls3))).
        { fold br. unfold bn_blocks, bn_dmax, add_word_hi, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_add_word.add_word_hi. cbn [bn_d bn_buf]. rewrite Edr. reflexivity. }
        eapply (EPI Σ3 (setbn rx (add_word_hi br (bn_top bx) w') ls3) m6 OW4 (0 + MC));
          [ apply cenv_setbnA; [| exact HVx4 | exact EBL5];
            eapply cenv_silentA; [exact EV4 | exact LS4 | exact MU5 | exact WM5 | exact HWL5 | assumption | assumption | cbn [app]; eassumption | exact FSZ4]
          | | clear; lia
          | intros q0 A0 n0 Hq0 Hne; apply BST4; [exact Hq0|]; subst ls2; rewrite getbn_setbn_same by exact HVx; unfold bn_with_buf; cbn [bn_d]; exact Hne ].
        unfold lib_state. eapply (lib_state_close [] ls3 m6 OW4 PL EA rx ax); [| exact ND4| exact HAx4| exact NROx| | |].
        -- eapply (lib_state_frame Σ3 LB (bv_unsigned sp) USTACK_TOP); [exact HEAP4| exact LSH4| exact MU5| exact WM5| exact FROK| exact WOK5].
        -- exists Dr. split.
           ++ unfold bn_cells, BnRepDefs.bn_cells, bn_dmax, add_word_hi, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_add_word.add_word_hi, MallocRep.wz. cbn [bn_top bn_buf bn_neg bn_flags bn_d]. fold nb2. rewrite Lnb2. exact BNr.
           ++ apply (fun ARRnb__ => bn_arr_of_nofr PL rx m6 OW4 Dr _ PWF4 NOFR NROx ARRnb__ ltac:(solve_nbuf)). unfold BnRepDefs.bn_arr, bn_dmax, add_word_hi, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_add_word.add_word_hi. cbn [bn_d bn_buf]. fold nb2. rewrite Edr, Lnb2. split; [exact Hinpr| exact U6].
        -- unfold bg_ok, bn_dmax, add_word_hi, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_add_word.add_word_hi. cbn [bn_buf bn_top bn_flags]. fold nb2. rewrite Lnb2. unfold BG_DMAX in *.
           split; [exact LMnb2|]. split; [clear - HDM; lia|]. split; [clear - OKq3; unfold bn_dmax in *; lia| exact OKq4].
        -- apply ids_ok_setbn_same; [exact IDS4| exact HVx4|]. unfold bn_blocks, bn_dmax, add_word_hi, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_add_word.add_word_hi. cbn [bn_d bn_buf]. fold nb2. rewrite Lnb2. reflexivity.
      *
        intros m3 v10 v12 v13 v14 U3 BN3 MU3' WM3' MI3 NC. cbn [app] in U3. rewrite EAW in U3, NC. cbn [fst snd] in U3, NC. rewrite <- Enb in U3.
        subst w'. change (0 =? 0) with true. cbv iota.
        destruct (CLS m3 U3 BN3 MU3' WM3' MI3) as (EV3 & LS3).
        step. step. apply evt_done.
        eapply (EPI Σ ls2 m3 OW 0); [exact EV3 | exact LS3 | unfold MC; clear; lia | intros q0 A0 n0 Hq0 _; exact Hq0].
Qed.

End WithRT.
