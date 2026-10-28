(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA ZBridge RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnMem BnTacX.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr BnLeaves ShiftPure.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA BnRepX ImplA ImplAX BnIfaceA UnwindA EdgesA AsStruct RtCallA W_cryptoA W_expandA BnAKitA BnCallA AW_lshift_arr AsStruct2 UbKit UbStruct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2247672 => 2
  | 2247684 => 1
  | 2247688 => 2
  | 2247752 => 1
  | 2247756 => 2
  | 2247760 => 1
  | 2247768 => 2
  | 2247796 => 1
  | 2247828 => 2
  | 2247832 => 2
  | 2247860 => 1
  | 2247864 => 2
  | 2247868 => 1
  | 2247872 => 1
  | 2247876 => 1
  | 2247880 => 1
  | 2247884 => 2
  | 2247892 => 2
  | 2247908 => 1
  | 2247912 => 1
  | 2247916 => 2
  | 2247920 => 1
  | 2247924 => 1
  | 2247928 => 1
  | 2247932 => 1
  | 2247936 => 2
  | 2247940 => 2
  | 2247944 => 1
  | 2247948 => 2
  | 2247976 => 1
  | 2247980 => 2
  | 2247984 => 1
  | 2247988 => 1
  | 2247992 => 1
  | 2247996 => 1
  | 2248000 => 2
  | 2248004 => 1
  | 2248008 => 2
  | 2248072 => 1
  | 2248088 => 2
  | 2248104 => 2
  | 2248108 => 1
  | 2248112 => 1
  | 2248116 => 2
  | 2248196 => 2
  | 2248200 => 2
  | 2248224 => 1
  | 2248228 => 1
  | 2248232 => 2
  | 2248252 => 2
  | 2248256 => 2
  | 2248260 => 1
  | 2248264 => 2
  | 2248296 => 2
  | 2248300 => 1
  | 2248304 => 2
  | 2248344 => 2
  | 2248348 => 2
  | 2248376 => 2
  | 2248380 => 2
  | 2248448 => 1
  | 2248452 => 2
  | 2248456 => 1
  | 2248464 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.

Ltac hide_ors := repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
Ltac unhide := repeat match goal with H : hide _ |- _ => apply hide_elim in H end.
Open Scope Z_scope.

Lemma bnref_eqb_false : forall x y, bnref_eqb x y = false -> x <> y.
Proof.
  intros x y H E. subst y. destruct x; cbn in H; try discriminate. rewrite Nat.eqb_refl in H. discriminate.
Qed.

(* [comment removed for export] *)
Definition nw_mA (n : Z) : Z :=
  bv_swrap 32 (Z.shiftr (bv_swrap 32 (Z.land (n + Z.shiftr (Z.land (Z.shiftl n 1) 18446744073709551615) 58) 18446744073709551615)) 6).
Lemma nw_mA_chk : forallb (fun n => nw_mA n =? 0) (map Z.of_nat (seq 0 64)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma nw_mA_0 : forall n, 0 <= n < 64 -> nw_mA n = 0.
Proof.
  intros n H. pose proof nw_mA_chk as A. rewrite forallb_forall in A. specialize (A n). rewrite Z.eqb_eq in A. apply A.
  apply in_map_iff. exists (Z.to_nat n). split; [lia|]. apply in_seq. lia.
Qed.

Definition BN_LSHIFT : Z := 0x224bc4.
Definition BN_LSHIFT_STACK : Z := 96 + BN_WEXPAND_STACK.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_ls_wexpand := (E_bn_lshift_fixed_top_226528 : uk_call BN_LSHIFT 0x224c64 BN_WEXPAND).

Lemma bn_lshift_fixed_top_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
    (lo : Z) (ras : list Z) (rr rx : bnref) (ar ax : Z) (n : Z),
  bn_preA Σ ls m OW LB AD EA sp lo BN_LSHIFT_STACK MC ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_LSHIFT (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> ref_at ls OW AD rr ar -> ref_at ls OW AD rx ax -> a0 = wz ar -> a1 = wz ax -> a2 = wz n -> 0 <= n < 64 ->
  implA (bn_lshift_fixed_top (tree_ops bptr) rr rx n ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA MC (fun _ _ _ a0' => a0' = wz 1))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_LSHIFT) fc None m (seg_rom bsegs)).
Proof.
  intros until n. intros PRE UW CTX -> HAr HAx -> -> -> Hn.
  pose proof PRE as (HEAP & LS & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED).
  pose proof LO as LO'. unfold BN_LSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO'.
  unfold BN_LSHIFT, MallocRep.wz.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  unfold bn_lshift_fixed_top.
  destruct (bnref_eqb rr rx) eqn:ERX; cbn [orb]. { unfold bunr. cbn [unreachable tree_ops]. apply implA_unr. }
  apply bnref_eqb_false in ERX.
  replace (n <? 64) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
  unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
  (* [comment removed for export] *)
  destruct (open_ro_sh Σ OW LB m ls AD EA rx ax HEAP LS HAx) as (Dx & BNx & (OKx1 & OKx2 & OKx3 & OKx4) & _ & X0 & XC & _ & _ & ACX & ALX & _ & _).
  set (bx := getbn rx ls) in *.
  unfold bn_cells, MallocRep.wz in BNx. unfold BN_WORDS_MAX in OKx3.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 96, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  apply implA_from_evt.
  carve_frame 96%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 96 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 13 step.
  ub. do 2 step. ub. step. do 3 step. step. do 2 step. shl_with ACX ALX. chk0.
  zstep. step. rewrite (sx32_small (Z.of_nat (bn_top bx))) by lia.
  do 3 zstep.
  setreg 23%Z (Z_to_bv 64 0) ltac:(f_equal; symmetry; apply (nw_mA_0 n Hn)).
  assert (TNW : Z.of_nat (bn_top bx) + 1 < 2147483648) by (clear - OKx2 OKx3; unfold bn_dmax in *; lia).
  zstep.
  ub. zstep. rewrite bk_swrap32_small by (clear - TNW; lia). ub.
  step. step.
  setreg 11%Z (Z_to_bv 64 (Z.of_nat (bn_top bx + 1))) ltac:(f_equal; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
  assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -96, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  assert (WOK : Forall (w_ok OW LB ls AD EA []) [(bv_unsigned sp + -96, bv_unsigned sp)]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
  pose proof (lib_state_frame Σ LB [] ls m m1 OW AD EA _ HEAP LS MU WM WOK) as LS1.
  assert (EV : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -96) s0 ra (Some ras) MC Σ ls OW m
                 [CB 8 (take 8 junk); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] 0 Σ ls m1 OW).
  { unfold cenvA, cenv_ok. split; [repeat split; try assumption; try (unfold USTACK_TOP; lia); clear - SP16; Z.div_mod_to_equations; lia|].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))|].
    split; [exact ST|]. split; [exact MI|].
    split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP MU HWL CEIL ltac:(lia))|].
    split; [lia|]. split; [apply cnt_eq_refl|]. split; [apply refs_stable_refl|].
    split; [cbn [app]; exact FR|]. split; [cbn; lia|]. unfold uw_opt.
    eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
  pose proof EV as (OK & HEAP1 & _).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HAr) as HVr.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  pose proof (st_okm_getbn rr ls SOK HVr) as (OKr1 & OKr2 & OKr3 & OKr4).
  clear HEAP LS ST MI MU WM HWL WOK FR BNx ACX OFF SHB1 SHB2 PRE.
  apply evt_done.
  eapply implA_bind.
  { eapply implA_leaves; [apply (bn_wexpand_leaves rr (bn_top bx + 1) ls HVr OKr2)|].
    eapply (bn_wexpand_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (r := rr) (a := ar) (OW := OW) (LB := LB) (AD := AD) (EA := EA);
      [| | | reflexivity | exact HAr | reflexivity | reflexivity | lia].
    - eapply cenv_preA; [exact EV | exact LS1 | unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; lia | lia].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV).
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_ls_wexpand CTX). }
  cbv beta. intros [u ls1] Σ1 ms1 [PO LEAF].
  apply (bn_postA_cpost LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -96) MC Σ ls OW) in PO; [| exact OK | exact HEAP1].
  cbn [fst snd] in *.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & -> & CP & (-> & HDM & WRES & BST)).
  assert (E1 : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -96) s0 ra (Some ras) MC Σ ls OW m
                 [CB 8 (take 8 junk); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] (0 + MC) Σ1 ls1 m2 OW2 /\ lib_state ls1 m2 OW2 AD EA)
    by (eapply cenv_postA; [exact EV | exact CP]).
  destruct E1 as (EV1 & LS2).
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP) as RST2.
  rewrite (ret_pc_even 2247780) by lia.
  destruct LEAF as (LF1 & LF2 & LF3 & LF4 & LF5). cbn [snd] in *.
  assert (Ebx : getbn rx ls1 = bx) by (apply LF1; exact ERX).
  pose proof (RST2 _ _ HAr) as HAr2. pose proof (RST2 _ _ HAx) as HAx2.
  pose proof EV1 as (_ & HEAP2 & ST2 & MI2 & AXP2 & CR2 & CNT2 & RS2 & FR2 & FSZ2 & UW2).
  cbn [app] in FR2.
  pose proof (AH_nodup_l _ _ _ _ HEAP2) as ND2.
  pose proof (AH_ceil _ _ _ _ HEAP2) as (C1' & C2' & C3').
  destruct (lib_state_h_parts _ _ _ _ _ _ LS2) as (IDS2 & ADB2 & ERRB2 & SOK2).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HAr2) as HVr2. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HAx2) as HVx2.
  (* [comment removed for export] *)
  destruct (lib_state_open [] ls1 m2 OW2 AD EA rx ax LS2 ND2 HAx2 ltac:(intros [])) as ((Dx2 & BNx2 & ARRx2) & _ & _).
  rewrite Ebx in BNx2, ARRx2.
  destruct (lib_state_open [] ls1 m2 OW2 AD EA rr ar LS2 ND2 HAr2 ltac:(intros [])) as ((Dr & BNr & ARRr) & (OKq1 & OKq2 & OKq3 & OKq4) & LSH).
  set (br := getbn rr ls1) in *.
  destruct (bn_arr_facts Σ1 OW2 LB m2 HEAP2 ls1 AD EA IDS2 ADB2 rr Dr HVr2 ARRr) as (Ur & LENr & Dr0 & DrC & DrI & DSEPr).
  fold br in Ur, LENr, DrC, DrI, DSEPr.
  pose proof (DSEPr rr ar HAr2) as SEPrr. pose proof (DSEPr rx ax HAx2) as SEPrx.
  pose proof (struct_disj Σ1 OW2 LB m2 HEAP2 ls1 AD EA IDS2 ADB2 rr rx ar ax ERX HAr2 HAx2) as SDJ.
  destruct (ref_at_inb _ _ _ _ _ ADB2 HAx2) as (qx2 & Ax2 & nx2 & Eqx2 & Hinx2 & Rx21 & Rx22).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP2 Hinx2) as (XB0 & XB16 & _ & XBC & XBI).
  destruct (ref_at_inb _ _ _ _ _ ADB2 HAr2) as (qr2 & Ar2 & nr2 & Eqr2 & Hinr2 & Rr21 & Rr22).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP2 Hinr2) as (RB0 & RB16 & _ & RBC & RBI).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP2 LS2 HAr2) as (ACR & ALR & OFR).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP2 LS2 HAx2) as (ACX2 & ALX2 & _).
  destruct (arr_shA _ _ _ _ _ _ HEAP2 ARRr) as (ACDR & ALDR & OFDR). fold br in ACDR, OFDR.
  unfold bn_cells in BNx2, BNr. unfold BN_WORDS_MAX in OKq3. unfold MallocRep.wz in *. unfold SHLO, SHHI in *.
  (* [comment removed for export] *)
  assert (HDr : exists pr, bn_d br = Some pr /\ In (pr, Dr, 8 * Z.of_nat (bn_dmax br)) OW2).
  { unfold bn_arr in ARRr. destruct (bn_d br) as [pr|]; [exists pr; split; [reflexivity| exact (proj1 ARRr)]|].
    exfalso. destruct ARRr as [_ E]. unfold bn_dmax in HDM. rewrite E in HDM. cbn in HDM. lia. }
  destruct HDr as (pr & Edr & Hinpr).
  pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m2) as MU3.
  pose proof (wmono_refl bsegs m2) as WM3.
  assert (OFF3 : offshW [(bv_unsigned sp + -96, bv_unsigned sp); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
  { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. lia. }
  apply implA_ret_evt.
  (* [comment removed for export] *)
  assert (FIN : forall mF (nb : list Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31,
            length nb = bn_dmax br -> limbs nb ->
            u64arr bsegs mF Dr (wlimbs nb) ->
            rw_cells bsegs mF ax [C8 (Z_to_bv 64 Dx2); C4 (Z_to_bv 64 (Z.of_nat (bn_top bx))); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax bx)));
                                  C4 (Z_to_bv 64 (Z.b2z (bn_neg bx))); C4 (Z_to_bv 64 (bn_flags bx))] ->
            rw_cells bsegs mF ar [C8 (Z_to_bv 64 Dr); C4 (Z_to_bv 64 (Z.of_nat (bn_top br))); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax br)));
                                  C4 (Z_to_bv 64 (Z.b2z (bn_neg br))); C4 (Z_to_bv 64 (bn_flags br))] ->
            rw_cells bsegs mF (bv_unsigned sp + -96) [CB 8 (take 8 junk); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
            stk bsegs mF lo (bv_unsigned sp + -96) -> mem_inv bsegs mF ->
            munch [(bv_unsigned sp + -96, bv_unsigned sp); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m2 mF -> wmono bsegs m2 mF ->
            evt bsegs
              (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA MC
                 (fun _ _ _ a0' => a0' = Z_to_bv 64 1)
                 (tt, setbn rr (mkBN (bn_d br) nb (bn_top bx + 1) (bn_neg bx) (bn_flags br)) ls1) Σ1)
              (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 TP_A) x5 x6 x7 sp (Z_to_bv 64 ar)
                       x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (ax + 8)) (Z_to_bv 64 ax) (Z_to_bv 64 n) (Z_to_bv 64 SHB)
                       (Z_to_bv 64 ((ax + 8) ≫ 3 + SHB)) (Z_to_bv 64 0) (Z_to_bv 64 (Z.land ar 7)) x25 s10 s11 x28 x29 x30 x31)
                  F2 (Z_to_bv 64 0x224e8c) fc2 None mF (seg_rom bsegs))).
  { intros mF nb x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 Lnb LMnb UF BNxF BNrF FRF STF MIF MUF WMF.
    clear SEPrx XBI DrI BNx2 BNr FR2 ST2 MI2 MU3 WM3 Ur.
    assert (LENnb : Z.of_nat (length (wlimbs nb)) = Z.of_nat (bn_dmax br)) by (rewrite wlimbs_len, Lnb; reflexivity).
    assert (UAR : 0 < ar /\ ar mod 8 = 0) by (split; [clear - RB0 Rr21; lia | exact ALR]).
    zstep. rewrite (bk_swrap32_small (n + 63)) by (clear - Hn; lia).
    zstep.
    zstep. if_cases KN; zify_cond KN. 2:{ exfalso. clear - KN Hn. lia. }
    ub. step. do 2 step. shl_with ACX2 ALX2. chk0.
    step. do 2 step. shl_with ACR ALR. step. rewrite (sx32_small (Z.b2z (bn_neg bx))) by (destruct (bn_neg bx); cbn; lia). chk0.
    step.
    shl_with ACX2 ALX2. chk0.
    step. rewrite (sx32_small (Z.of_nat (bn_top bx))) by lia.
    zstep.
    ub. zstep. rewrite bk_swrap32_small by (clear - TNW; lia). ub.
    step. do 2 step. shl_with ACR ALR. chk0.
    step. step.
    do 11 step. release_frame FRF STF (bv_unsigned sp). step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mG end.
    apply evt_done.
    assert (HWL3 : Forall (w_lib OW2 lo (bv_unsigned sp)) [(bv_unsigned sp + -96, bv_unsigned sp); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
    { constructor; [left; cbn; lia|]. constructor; [right; exists (qr2, Ar2, nr2); cbn; auto|].
      constructor; [right; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn; split; [exact Hinpr| lia]| constructor]. }
    assert (WOK3 : Forall (w_ok OW2 LB ls1 AD EA [rr]) [(bv_unsigned sp + -96, bv_unsigned sp); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|]. constructor; [eapply (w_struct OW2 LB ls1 AD EA false [rr] _ rr ar); [left; reflexivity| exact HAr2| cbn; lia| cbn; lia]|].
      constructor; [eapply (w_limbs OW2 LB ls1 AD EA false [rr] _ rr pr Dr); [left; reflexivity| exact HVr2| exact Edr| exact Hinpr| cbn [fst snd]; fold br; lia| cbn [fst snd]; fold br; lia]| constructor]. }
    pose proof OK as (CEIL' & _).
    unfold bn_postA. do 17 eexists. exists mG, OW2. split; [reflexivity|]. cbn [fst snd].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP2 MUF WMF HWL3 CEIL ltac:(unfold USTACK_TOP; lia))|].
    split.
    { unfold lib_state. eapply (lib_state_close [] ls1 mG OW2 AD EA rr ar); [| exact ND2| exact HAr2| | |].
      - exact (lib_state_frame Σ1 LB [rr] ls1 m2 mG OW2 AD EA _ HEAP2 LSH MUF WMF WOK3).
      - exists Dr. split.
        + unfold bn_cells, bn_dmax. cbn [bn_top bn_buf bn_neg bn_flags]. rewrite Lnb.
          replace (Z.of_nat (bn_top bx + 1)) with (Z.of_nat (bn_top bx) + 1) by lia. exact BNrF.
        + unfold bn_arr, bn_dmax. cbn [bn_d bn_buf]. rewrite Edr, Lnb. split; [exact Hinpr| exact UF].
      - unfold bn_okm, bn_dmax. cbn [bn_buf bn_top bn_flags]. rewrite Lnb. unfold BN_WORDS_MAX.
        split; [exact LMnb|]. split; [exact HDM|]. split; [lia| exact OKq4].
      - apply ids_ok_setbn_same; [exact IDS2| exact HVr2|]. unfold bn_blocks, bn_dmax. cbn [bn_d bn_buf]. rewrite Lnb. reflexivity. }
    split; [exact STF|]. split; [exact MIF|].
    split; [eapply ax_pres_trans; [exact AXP2|]; exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP2 MUF HWL3 CEIL ltac:(lia))|].
    split; [lia|].
    split. { unfold cnt_eq in *. rewrite (cnt_bal_setbn rr _ ls1 OW2 OW2 HVr2). fold br. rewrite CNT2.
             unfold bn_blocks, bn_dmax. cbn [bn_d bn_buf]. rewrite Edr, Lnb. cbn [length]. lia. }
    split. { intros r0 a0 H0. apply ref_at_setbn. apply RS2. exact H0. }
    reflexivity. }
  destruct (proj1 (limbarr_limbs_at bsegs m2 Dr (bn_buf br)) Ur) as (LAr & WRr).
  assert (LBr : length (bn_buf br) = bn_dmax br) by reflexivity.
  zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by lia. lia. }
  shl_with ACX2 ALX2. chk0.
  step. rewrite (sx32_small (Z.of_nat (bn_top bx))) by lia.
  assert (UAR : 0 < ar /\ ar mod 8 = 0) by (split; [clear - RB0 Rr21; lia | exact ALR]).
  assert (PR0 : 0 < Dr) by (pose proof (AH_range _ _ _ _ _ _ _ HEAP2 Hinpr) as (P0 & _); exact P0).
  hide_ors. ub. unhide.
  do 2 zstep.
  zstep. if_cases KT; zify_cond KT.
  - (* [comment removed for export] *)
    assert (ETOP : bn_top bx = 0%nat) by (clear - KT; lia).
    replace (bn_top bx =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; exact ETOP).
    hide_ors. ub. unhide.
    step. shl_with ACR ALR. chk0.
    step. zstep.
    assert (BDR : 0 <= Dr /\ Dr + 8 * Z.of_nat (bn_dmax br) <= 140737488355328) by (unfold BnHeapA.ACEIL in *; lia).
    hide_ors. ub.
    do 4 zstep. ub. unhide.
    do 2 step. shl_limb ACDR ALDR BDR 0. chk0.
    assert (SOKA : store_ok bsegs m2 (Z_to_bv 64 Dr) 8 = true).
    { pose proof (wr_at_store_ok bsegs m2 Dr (8 * Z.of_nat (length (bn_buf br))) 0 8 WRr ltac:(lia) ltac:(rewrite LBr; clear - HDM; lia)) as X.
      rewrite Z.add_0_r in X. exact X. }
    rewrite ?Z.add_0_r.
    zstep.
    assert (UN : u64arr bsegs (write_to_mem m2 (Z_to_bv 64 Dr) (le8 (Z_to_bv 64 0))) Dr (wlimbs (BnBase.upd (bn_buf br) 0 0))).
    { apply limbarr_limbs_at. split.
      - unfold BnBase.upd, splice. cbn [firstn app length Nat.add].
        apply (limbs_at_cons_writeA m2 Dr 0 (skipn 1 (bn_buf br))); [|exact Dr0].
        rewrite <- (firstn_skipn 1 (bn_buf br)) in LAr. apply limbs_at_app in LAr. destruct LAr as [_ LA2].
        rewrite length_firstn, LBr in LA2. replace (Nat.min 1 (bn_dmax br)) with 1%nat in LA2 by (clear - HDM; lia). exact LA2.
      - rewrite upd_length by (rewrite LBr; clear - HDM; lia). apply wr_at_write. exact WRr. }
    clear Ur LAr WRr.
    assert (L8 : length (le8 (Z_to_bv 64 0)) = 8%nat) by apply length_le8.
    assert (D8 : Dr + 8 <= Dr + 8 * Z.of_nat (bn_dmax br)) by (clear - HDM; lia).
    change (Z_to_bv 64 Dr) with (wa Dr) in *.
    apply (rw_cells_frame bsegs m2 _ _ Dr (le8 (Z_to_bv 64 0))) in BNx2; [| exact Dr0 | rewrite L8; unfold BnHeapA.ACEIL in *; lia | rewrite L8; cbn; clear - SEPrx D8; lia].
    apply (rw_cells_frame bsegs m2 _ _ Dr (le8 (Z_to_bv 64 0))) in BNr; [| exact Dr0 | rewrite L8; unfold BnHeapA.ACEIL in *; lia | rewrite L8; cbn; clear - SEPrr D8; lia].
    apply (rw_cells_frame bsegs m2 _ _ Dr (le8 (Z_to_bv 64 0))) in FR2; [| exact Dr0 | rewrite L8; unfold BnHeapA.ACEIL in *; lia | rewrite L8; cbn; unfold BnHeapA.ACEIL in *; lia].
    apply (stk_write bsegs m2 _ _ Dr (le8 (Z_to_bv 64 0))) in ST2; [| exact Dr0 | rewrite L8; unfold BnHeapA.ACEIL in *; lia].
    apply (mem_inv_store bsegs m2 (wa Dr) (le8 (Z_to_bv 64 0))) in MI2; [| rewrite L8; exact SOKA].
    apply (munch_write _ m2 m2 Dr (le8 (Z_to_bv 64 0))) in MU3; [| exact Dr0 | rewrite L8; unfold BnHeapA.ACEIL in *; lia | rewrite L8; cbn [inside]; clear - D8; lia].
    apply (wmono_write bsegs m2 m2 (wa Dr) (le8 (Z_to_bv 64 0))) in WM3.
    step.
    eapply FIN; try eassumption.
    + rewrite upd_length by (rewrite LBr; clear - HDM; lia). exact LBr.
    + apply upd_limbs; [exact OKq1 | exact limb_0].
  - (* [comment removed for export] *)
    assert (NTOP : bn_top bx <> 0%nat) by (clear - KT; lia).
    replace (bn_top bx =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; exact NTOP).
    (* [comment removed for export] *)
    destruct (bn_arr_facts Σ1 OW2 LB m2 HEAP2 ls1 AD EA IDS2 ADB2 rx Dx2 HVx2 ltac:(rewrite Ebx; exact ARRx2)) as (Ux & LENx & Dx0 & DxC & DxI & _).
    rewrite Ebx in Ux, LENx, DxC, DxI.
    assert (HDx : exists px, bn_d bx = Some px /\ In (px, Dx2, 8 * Z.of_nat (bn_dmax bx)) OW2).
    { unfold bn_arr in ARRx2. destruct (bn_d bx) as [px|]; [exists px; split; [reflexivity| exact (proj1 ARRx2)]|].
      exfalso. destruct ARRx2 as [_ E]. unfold bn_dmax in OKx2. rewrite E in OKx2. cbn in OKx2. lia. }
    destruct HDx as (px & Edx & Hinpx).
    pose proof (AH_range _ _ _ _ _ _ _ HEAP2 Hinpx) as (PX0 & PX16 & _ & _ & _).
    pose proof (limbs_limbs_disj Σ1 OW2 LB m2 HEAP2 ls1 AD EA IDS2 rx rr px Dx2 _ pr Dr _ ltac:(congruence) HVx2 HVr2
                  ltac:(rewrite Ebx; exact Edx) Edr Hinpx Hinpr) as LDJ.
    destruct (arr_shA _ _ _ _ _ _ HEAP2 ARRx2) as (ACDX & ALDX & _).
    destruct (proj1 (limbarr_limbs_at bsegs m2 Dx2 (bn_buf bx)) Ux) as (LAx & _).
    set (f := firstn (bn_top bx) (bn_buf bx)).
    assert (Lf : length f = bn_top bx) by (subst f; apply firstn_length_le; exact OKx2).
    assert (LAf : limbs_at bsegs m2 Dx2 f).
    { rewrite <- (firstn_skipn (bn_top bx) (bn_buf bx)) in LAx. apply limbs_at_app in LAx. exact (proj1 LAx). }
    assert (LArest : limbs_at bsegs m2 (Dr + 8 * Z.of_nat (bn_top bx + 1)) (skipn (bn_top bx + 1) (bn_buf br))).
    { rewrite <- (firstn_skipn (bn_top bx + 1) (bn_buf br)) in LAr. apply limbs_at_app in LAr. destruct LAr as [_ LA2].
      rewrite length_firstn, LBr in LA2. replace (Nat.min (bn_top bx + 1) (bn_dmax br)) with (bn_top bx + 1)%nat in LA2 by (clear - HDM; lia). exact LA2. }
    assert (BDX : 0 <= Dx2 /\ Dx2 + 8 * Z.of_nat (bn_dmax bx) <= 140737488355328) by (unfold BnHeapA.ACEIL in *; lia).
    assert (BDR : 0 <= Dr /\ Dr + 8 * Z.of_nat (bn_dmax br) <= 140737488355328) by (unfold BnHeapA.ACEIL in *; lia).
    pose proof (arr_ubA _ _ _ _ _ _ HEAP2 ARRx2 ltac:(unfold bn_dmax in *; clear - NTOP OKx2; lia)) as (UDX & UDX16).
    assert (TX31 : Z.of_nat (bn_top bx) < 2147483648 /\ Z.of_nat (bn_top bx) <= Z.of_nat (bn_dmax bx)) by (clear - OKx2 OKx3; unfold bn_dmax in *; lia).
    do 2 step. shl_with ACX2 ALX2. chk0.
    hide_ors. ub. unhide.
    step. shl_with ACR ALR. chk0.
    step. zstep. zstep.
    replace (Z.b2z (0 <? Dr)) with 1 by (rewrite (proj2 (Z.ltb_lt 0 Dr)) by (clear - PR0; lia); reflexivity).
    hide_ors. ub.
    zstep. rewrite (bk_swrap32_small (Z.of_nat (bn_top bx) + -1)) by (clear - NTOP TX31; lia).
    ub. unhide.
    step.
    zstep. replace (Z.shiftl (Z.of_nat (bn_top bx) + -1) 3) with (8 * Z.of_nat (bn_top bx) - 8) by (rewrite Z.shiftl_mul_pow2 by (clear; lia); clear; lia).
    zstep.
    hide_ors. ub. unhide.
    do 2 step. shl_limb ACDX ALDX BDX (Z.of_nat (bn_top bx) - 1). chk0.
    zstep. replace (Z.shiftl (Z.of_nat (bn_top bx)) 3) with (8 * Z.of_nat (bn_top bx)) by (rewrite Z.shiftl_mul_pow2 by (clear; lia); clear; lia).
    zstep.
    hide_ors. ub. unhide.
    do 2 step. shl_limb ACDR ALDR BDR (Z.of_nat (bn_top bx)). chk0.
    replace (Z.of_nat (bn_top bx)) with (Z.of_nat (length f)) by (rewrite Lf; reflexivity).
    setreg 7%Z (Z_to_bv 64 (Z.of_nat (length f) - 1)) ltac:(f_equal; clear; lia).
    setreg 11%Z (Z_to_bv 64 (Dx2 + 8 * (Z.of_nat (length f) - 1))) ltac:(f_equal; clear; lia).
    setreg 13%Z (Z_to_bv 64 (Dr + 8 * Z.of_nat (length f))) ltac:(f_equal; clear; lia).
    eapply (lsh_blockA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 f Dx2 Dr n).
    { exact Hn. }
    { subst f. apply limbs_firstn. exact OKx1. }
    { rewrite Lf. clear - NTOP OKx2 OKx3. lia. }
    { rewrite Lf. clear - LDJ OKx2 HDM. lia. }
    { rewrite Lf. eapply acc_sub; [exact ACDX | lia | clear - OKx2; lia]. }
    { rewrite Lf. eapply acc_sub; [exact ACDR | lia | clear - HDM; lia]. }
    { exact ALDX. }
    { exact ALDR. }
    { rewrite Lf. cbn [offshW]. unfold SHLO, SHHI. clear - OFDR HDM Dr0. lia. }
    { clear - PR0; lia. }
    { exact LAf. }
    { rewrite Lf. apply (wr_at_sub bsegs m2 Dr (8 * Z.of_nat (length (bn_buf br))) 0 (8 * (Z.of_nat (bn_top bx) + 1))) in WRr; [rewrite Z.add_0_r in WRr; exact WRr | clear; lia | clear; lia | rewrite LBr; clear - HDM; lia]. }
    { exact MI2. }
    intros m3 z6 z7 z11 z13 z15 z25 z28 z29 z30 z31 HR HFx MI3 MUb WMb.
    rewrite Lf in HR, MUb.
    (* [comment removed for export] *)
    assert (DJW : forall A k, (A + k <= Dr \/ Dr + 8 * Z.of_nat (bn_dmax br) <= A) ->
              disjoint_from [(Dr, Dr + 8 * (Z.of_nat (bn_top bx) + 1))] A k).
    { intros A k H. cbn [disjoint_from]. split; [|exact I]. clear - H HDM. lia. }
    eapply (rw_cells_transport bsegs _ m2 m3) in BNx2; [| exact MUb | exact WMb | apply DJW; cbn; clear - SEPrx; lia].
    eapply (rw_cells_transport bsegs _ m2 m3) in BNr; [| exact MUb | exact WMb | apply DJW; cbn; clear - SEPrr; lia].
    eapply (rw_cells_transport bsegs _ m2 m3) in FR2; [| exact MUb | exact WMb | apply DJW; cbn; unfold BnHeapA.ACEIL in *; lia].
    eapply (stk_transport_disjoint bsegs _ m2 m3) in ST2; [| exact MUb | exact WMb | apply DJW; unfold BnHeapA.ACEIL in *; lia].
    assert (MU4 : munch [(bv_unsigned sp + -96, bv_unsigned sp); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m2 m3).
    { eapply munch_weaken; [|exact MUb]. unfold sub_fp. intros x Hx. cbn [outside] in *. split; [|exact I]. clear - Hx HDM. lia. }
    assert (LArest3 : limbs_at bsegs m3 (Dr + 8 * Z.of_nat (bn_top bx + 1)) (skipn (bn_top bx + 1) (bn_buf br))).
    { eapply limbs_at_transport; [exact LArest | exact MUb |]. cbn [disjoint_from]. split; [|exact I]. rewrite length_skipn, LBr. clear - HDM. lia. }
    clear MU3 WM3.
    pose proof (lshift_limbs_seq f n) as ESEQ.
    destruct (lshift_limbs f n 0) as [ls0 mo] eqn:ELS. cbn [fst snd] in ESEQ.
    assert (Lnew : length (ls0 ++ [mo]) = (bn_top bx + 1)%nat) by (rewrite ESEQ, length_map, length_seq, Lf; lia).
    pose proof (lshift_limbs_spec f n 0 ltac:(subst f; apply limbs_firstn; exact OKx1) Hn ltac:(split; [clear; lia| apply Z.pow_pos_nonneg; clear - Hn; lia])) as LSP.
    rewrite ELS in LSP. destruct LSP as (LS0 & _ & LMO & _).
    assert (LIMBnew : limbs (ls0 ++ [mo])).
    { apply limbs_app; [exact LS0|]. apply limbs_cons; [|apply limbs_nil]. unfold limb. rewrite BW_pow.
      split; [clear - LMO; lia|]. apply Z.lt_le_trans with (2 ^ n); [clear - LMO; lia|]. apply Z.pow_le_mono_r; clear - Hn; lia. }
    eapply (FIN m3 (splice (bn_buf br) 0 (ls0 ++ [mo]))); try eassumption.
    + rewrite splice_length by (rewrite Lnew, LBr; clear - HDM; lia). exact LBr.
    + apply splice_limbs; [exact OKq1 | exact LIMBnew].
    + apply limbarr_limbs_at. split.
      * unfold splice. change (firstn 0 (bn_buf br)) with (@nil Z). change (0 + length (ls0 ++ [mo]))%nat with (length (ls0 ++ [mo])).
        change ([] ++ (ls0 ++ [mo]) ++ skipn (length (ls0 ++ [mo])) (bn_buf br)) with ((ls0 ++ [mo]) ++ skipn (length (ls0 ++ [mo])) (bn_buf br)).
        apply limbs_at_app. split; [rewrite ESEQ, Lf; exact HR|]. rewrite Lnew. exact LArest3.
      * rewrite splice_length by (rewrite Lnew, LBr; clear - HDM; lia). eapply wr_at_transport; [exact WRr | exact WMb].
Qed.

End WithRT.
