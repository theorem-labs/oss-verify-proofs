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
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr ShiftPure.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA AW_lshift_arr AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR Require W_lshift.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitAF BnCallAF W_expandAF AShiftArr ShiftKitAF.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import UbStruct.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2317732 => 2
  | 2317744 => 1
  | 2317748 => 2
  | 2317812 => 1
  | 2317816 => 2
  | 2317820 => 1
  | 2317828 => 2
  | 2317856 => 1
  | 2317888 => 2
  | 2317892 => 2
  | 2317920 => 1
  | 2317924 => 2
  | 2317928 => 1
  | 2317932 => 1
  | 2317936 => 1
  | 2317940 => 1
  | 2317944 => 2
  | 2317952 => 2
  | 2317968 => 1
  | 2317972 => 1
  | 2317976 => 2
  | 2317980 => 1
  | 2317984 => 1
  | 2317988 => 1
  | 2317992 => 1
  | 2317996 => 2
  | 2318000 => 2
  | 2318004 => 1
  | 2318008 => 2
  | 2318036 => 1
  | 2318040 => 2
  | 2318044 => 1
  | 2318048 => 1
  | 2318052 => 1
  | 2318056 => 1
  | 2318060 => 2
  | 2318064 => 1
  | 2318068 => 2
  | 2318132 => 1
  | 2318148 => 2
  | 2318164 => 2
  | 2318168 => 1
  | 2318172 => 1
  | 2318176 => 2
  | 2318256 => 2
  | 2318260 => 2
  | 2318284 => 1
  | 2318288 => 1
  | 2318292 => 2
  | 2318312 => 2
  | 2318316 => 2
  | 2318320 => 1
  | 2318324 => 2
  | 2318356 => 2
  | 2318360 => 1
  | 2318364 => 2
  | 2318404 => 2
  | 2318408 => 2
  | 2318436 => 2
  | 2318440 => 2
  | 2318508 => 1
  | 2318512 => 2
  | 2318516 => 1
  | 2318524 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.

Ltac hide_ors := repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
Ltac unhide := repeat match goal with H : hide _ |- _ => apply hide_elim in H end.
Open Scope Z_scope.

Definition BN_LSHIFT : Z := 0x235d70.
Definition BN_LSHIFT_STACK : Z := 96 + BN_WEXPAND_STACK.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_ls_wexpand := (E_bn_lshift_fixed_top_235c28 : uk_call BN_LSHIFT 0x235e10 BN_WEXPAND).

Lemma bn_lshift_fixed_top_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (rr rx : bnref) (ar ax : Z) (n : Z),
  bn_preA Σ ls m OW LB PL EA sp lo BN_LSHIFT_STACK MC ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_LSHIFT (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> ref_at ls OW PL rr ar -> hpl PL rr -> ref_at ls OW PL rx ax -> rx <> ROne -> nbuf PL rx ->
  a0 = wz ar -> a1 = wz ax -> a2 = wz n -> 0 <= n < 2^30 ->
  implA (bn_lshift_fixed_top (tree_ops bptr) rr rx n ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC (shift_res rr ls OW PL))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_LSHIFT) fc None m (seg_rom bgbsegs)).
Proof.
  intros until n. intros PRE UW CTX -> HAr HP HAx NROx NBx -> -> -> Hn.
  pose proof (proj1 (hpl_wref PL rr HP) : not_one rr) as NRO. change (not_one rx) in NROx.
  pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
  pose proof LO as LO'. unfold BN_LSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO'.
  unfold BN_LSHIFT, MallocRep.wz.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  set (nw := Z.to_nat (n / 64)). set (lb := n mod 64).
  assert (Hnw : 0 <= n / 64 < 2^24). { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  assert (Enw : Z.of_nat nw = n / 64) by (subst nw; apply Z2Nat.id; lia).
  assert (Hlb : 0 <= lb < 64) by (subst lb; apply Z.mod_pos_bound; lia).

  destruct (open_ro_sh Σ OW LB m ls PL EA _ rx ax HEAP LS FROK NOFR HAx NROx) as (Dx & BNx & (OKx1 & OKx2 & OKx3 & OKx4) & _ & X0 & XC & _ & _ & ACX & ALX & _ & _).
  set (topx := bn_top (getbn rx ls)) in *.
  unfold bn_cells, BnRepDefs.bn_cells, MallocRep.wz in BNx. unfold BN_WORDS_MAX, BG_DMAX in OKx3.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 96, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  rewrite (OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_lshift.lshift_eq rr rx n ls) by lia. fold topx nw lb.
  apply implA_from_evt.
  carve_frame 96%nat ST.
  apply (rw_cells_split_CB bgbsegs _ _ [] 96 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 13 step.

  ub. do 2 step. ub. step. do 3 step. step. do 2 step. shl_with ACX ALX. chk0.

  zstep. step. rewrite (sx32_small (Z.of_nat topx)) by (unfold bn_dmax in *; lia).
  do 3 zstep.
  setreg 23%Z (Z_to_bv 64 (Z.of_nat nw)) ltac:(rewrite Enw; f_equal; symmetry; apply (OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_lshift.nw_m_eq n); lia).
  assert (TNW : Z.of_nat topx + Z.of_nat nw + 1 < 2147483648) by (clear - OKx2 OKx3 Hnw Enw; unfold bn_dmax in *; lia).
  zstep.
  ub. zstep. rewrite (bk_swrap32_small (Z.of_nat topx + Z.of_nat nw + 1)) by (clear - TNW; lia). ub.
  step. step.
  setreg 11%Z (Z_to_bv 64 (Z.of_nat (topx + nw + 1))) ltac:(f_equal; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
  assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -96, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -96, bv_unsigned sp)]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
  pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
  assert (EV : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -96) s0 ra (Some ras) MC Σ ls OW m
                 [CB 8 (take 8 junk); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] 0 Σ ls m1 OW).
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
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HAr) as HVr.
  clear HEAP LS ST MI MU WM HWL WOK FR BNx ACX OFF SHB1 SHB2 PRE PARTS.
  apply evt_done.
  eapply implA_bind.
  { eapply (bn_wexpand_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (r := rr) (a := ar) (words := (topx + nw + 1)%nat) (OW := OW) (LB := LB) (PL := PL) (EA := EA);
      [| | | reflexivity | exact HAr | exact (hpl_wref PL rr HP) | reflexivity | reflexivity | unfold bn_dmax in *; lia].
    - eapply cenv_preA; [exact EV | exact LS1 | unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; lia | lia].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV).
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_ls_wexpand CTX). }
  cbv beta. intros [u ls1] Σ1 ms1 PO.
  apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -96) MC Σ ls OW) in PO; [| exact OK | exact HEAP1].
  cbn [fst snd] in *.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & PL2 & -> & CP & (EPL & -> & HDM & WRES & BST)).
  subst PL2. specialize (CP eq_refl).
  assert (E1 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -96) s0 ra (Some ras) MC Σ ls OW m
                 [CB 8 (take 8 junk); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] (0 + MC) Σ1 ls1 m2 OW2 /\ lib_state ls1 m2 OW2 PL EA)
    by (eapply cenv_postA; [exact EV | exact CP]).
  destruct E1 as (EV1 & LS2).
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP) as RST2.
  rewrite (ret_pc_even 2317840) by lia.
  pose proof (ref_at_stable _ _ _ _ _ _ _ RST2 HAr) as HAr2. pose proof (ref_at_stable _ _ _ _ _ _ _ RST2 HAx) as HAx2.
  pose proof EV1 as (_ & HEAP2 & ST2 & MI2 & AXP2 & CR2 & CNT2 & RS2 & FR2 & FSZ2 & UW2).
  cbn [app] in FR2.
  pose proof (AH_nodup_l _ _ _ _ HEAP2) as ND2.
  pose proof (AH_ceil _ _ _ _ HEAP2) as (C1' & C2' & C3').
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as PARTS1; pose proof PARTS1 as (WFS1 & PWF1 & IDS1 & PLB1 & ERRB1).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HAr2) as HVr2. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HAx2) as HVx2.
  assert (ETX : bn_top (getbn rx ls1) = topx) by (apply (wexpand_keeps_topA rr (topx + nw + 1) ls ls1 rx WRES HVr)).

  destruct (lib_state_open [] ls1 m2 OW2 PL EA rr ar LS2 ND2 HAr2 ltac:(intros []) NRO) as ((Dr & BNr & ARRr) & OKR' & LSH).
  pose proof OKR' as (OKq1 & OKq2 & OKq3 & OKq4). unfold BG_DMAX in OKq3.
  destruct (bn_arr_facts_w ls1 OW2 PL EA (bv_unsigned sp) USTACK_TOP Σ1 LB m2 rr Dr HEAP2 PARTS1 FROK HVr2 (hpl_wref PL rr HP) ARRr) as (Ur & LENr & Dr0 & DrC & DrI & DSEPr).
  destruct (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 HAr2 HP) as (SA0 & SAC & SAI & (qr2 & Ar2 & nr2 & Hinr2 & Rr21 & Rr22)).
  destruct (operand_cellsA Σ1 OW2 LB m2 ls1 PL EA (bv_unsigned sp) USTACK_TOP rr ar Dr rx ax topx HEAP2 LS2 FROK NOFR HAr2 HP BNr ARRr HAx2 NROx ltac:(rewrite ETX; apply Nat.le_refl) ltac:(solve_nbuf))
    as (Dx2 & ARRxo & BNx2 & OKX & LAf & X0' & XC' & DX0 & DXC & SXR & SRX & ALXD & SXD & DX8).
  set (br := getbn rr ls1) in *. set (bx := getbn rx ls1) in *.
  pose proof OKX as (OKy1 & OKy2 & OKy3 & OKy4). unfold BG_DMAX in OKy3.
  set (f := firstn topx (bn_buf bx)) in *.
  assert (Lf : length f = topx) by (subst f; apply firstn_length_le; rewrite <- ETX; exact OKy2).
  pose proof (DSEPr rr ar HAr2) as SEPrr. fold br in SEPrr.
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP2 LS2 NOFR HAr2 NRO) as (ACR & ALR & OFR).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP2 LS2 NOFR HAx2 NROx) as (ACX2 & ALX2 & _).
  pose proof ARRr as ARRo. apply (fun ARRnb__ => bn_arr_nofr PL rr m2 OW2 Dr _ PWF1 NOFR NRO ARRnb__ ltac:(solve_nbuf)) in ARRo.
  destruct (arr_shA _ _ _ _ _ _ HEAP2 ARRo) as (ACDR & ALDR & OFDR). fold br in ACDR, OFDR.
  unfold bn_cells, BnRepDefs.bn_cells in BNx2, BNr. unfold MallocRep.wz in *. unfold SHLO, SHHI in *.
  rewrite ETX in BNx2.

  assert (HDr : exists pr, bn_d br = Some pr /\ In (pr, Dr, 8 * Z.of_nat (bn_dmax br)) OW2).
  { unfold BnRepDefs.bn_arr in ARRo. fold br in ARRo. destruct (bn_d br) as [pr|]; [exists pr; split; [reflexivity| exact (proj1 ARRo)]|].
    exfalso. destruct ARRo as [_ E]. unfold bn_dmax in HDM. fold br in HDM. rewrite E in HDM. cbn in HDM. clear - HDM. lia. }
  destruct HDr as (pr & Edr & Hinpr).
  assert (LBr : length (bn_buf br) = bn_dmax br) by reflexivity.
  rewrite (OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_lshift.lshift_rest_eq rr rx nw lb ls1). fold br bx. rewrite ETX.
  pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m2) as MU3.
  pose proof (wmono_refl bgbsegs m2) as WM3.
  assert (OFF3 : offshW [(bv_unsigned sp + -96, bv_unsigned sp); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
  { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. clear - OFR OFDR SPR LO' CEIL C1 C2 C3 C1' C2' C3'. lia. }
  set (nbF := OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_lshift.lshift_buf br bx nw lb) in *.
  set (stF := setbn rr (mkBN (bn_d br) nbF (topx + nw + 1) (bn_neg bx) (bn_flags br)) ls1) in *.
  set (QF := bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC (shift_res rr ls OW PL) (tt, stF) Σ1).

  assert (TAIL2 : forall mT0 mT (FT : bvmap 5 word) (fcT : bv 32) (q1 q5 q6 q7 q11 q12 q13 q14 q15 q16 q17 q25 q28 q29 q30 q31 : word),
            length nbF = bn_dmax br -> limbs nbF ->
            AHEAP Σ1 OW2 LB mT0 -> lib_state_hc false [rr] ls1 mT0 OW2 PL EA -> ax_pres LB (bv_unsigned sp) (XW PL) m mT0 ->
            munch [(bv_unsigned sp + -96, bv_unsigned sp); (ar, ar + 24)]%Z mT0 mT -> wmono bgbsegs mT0 mT ->
            u64arr bgbsegs mT Dr (wlimbs nbF) ->
            rw_cells bgbsegs mT ar [C8 (Z_to_bv 64 Dr); C4 (Z_to_bv 64 (Z.of_nat (bn_top br))); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax br)));
                                  C4 (Z_to_bv 64 (Z.b2z (bn_neg bx))); C4 (Z_to_bv 64 (bn_flags br))] ->
            rw_cells bgbsegs mT (bv_unsigned sp + -96) [CB 8 (take 8 junk); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
            stk bgbsegs mT lo (bv_unsigned sp + -96) -> mem_inv bgbsegs mT ->
            evt bgbsegs QF
              (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 TP_A) q5 q6 q7 sp (Z_to_bv 64 ar)
                       (Z_to_bv 64 (Z.of_nat topx)) q11 q12 q13 q14 q15 q16 q17 (Z_to_bv 64 (ax + 8)) (Z_to_bv 64 ax) (Z_to_bv 64 n) (Z_to_bv 64 SHB)
                       (Z_to_bv 64 ((ax + 8) ≫ 3 + SHB)) (Z_to_bv 64 (Z.of_nat nw)) (Z_to_bv 64 (Z.land ar 7)) q25 s10 s11 q28 q29 q30 q31)
                  FT (Z_to_bv 64 0x2360a8) fcT None mT (seg_rom bgbsegs))).
  { intros mT0 mT FT fcT q1 q5 q6 q7 q11 q12 q13 q14 q15 q16 q17 q25 q28 q29 q30 q31 Lnb LMnb HEAPT LSHT AXPT MUT WMT UF BNrF FRF STF MIF.
    clear BNx2 BNr FR2 ST2 MI2 MU3 WM3 Ur LAf SXR SRX ALXD SXD DXC XC' DX8 DrI DSEPr OFF3 ACR ACX2 ACDR.
    assert (LENnb : Z.of_nat (length (wlimbs nbF)) = Z.of_nat (bn_dmax br)) by (rewrite wlimbs_len, Lnb; reflexivity).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAPT LSHT NOFR HAr2 NRO) as (ACRT0 & _ & _).
    assert (OFFT0 : offshW [(bv_unsigned sp + -96, bv_unsigned sp); (ar, ar + 24)]).
    { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. clear - OFR SPR LO' CEIL C1 C2 C3 C1' C2' C3'. lia. }
    zstep.
    ub. zstep. rewrite (bk_swrap32_small (Z.of_nat topx + Z.of_nat nw + 1)) by (clear - TNW; lia). ub.
    step. do 2 step. shl_with ACRT0 ALR. chk0.
    step. step.
    do 11 step. release_frame FRF STF (bv_unsigned sp). step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mG end.
    apply evt_done.
    assert (HWL3 : Forall (w_lib ls1 OW2 PL lo (bv_unsigned sp)) [(bv_unsigned sp + -96, bv_unsigned sp); (ar, ar + 24)]).
    { constructor; [left; cbn; clear - LO'; lia|]. constructor; [right; left; exists (qr2, Ar2, nr2); cbn [blk_addr blk_size fst snd]; split; [exact Hinr2 | clear - Rr21 Rr22; lia]| constructor]. }
    assert (WOK3 : Forall (w_ok OW2 LB ls1 PL EA (bv_unsigned sp) [rr]) [(bv_unsigned sp + -96, bv_unsigned sp); (ar, ar + 24)]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; clear - LO' CEIL; lia|].
      constructor; [eapply (w_struct OW2 LB ls1 PL EA (bv_unsigned sp) false [rr] _ rr ar); [left; reflexivity| exact HAr2| exact NRO| cbn; clear; lia| cbn; clear; lia]| constructor]. }
    assert (OKF : bg_ok (mkBN (bn_d br) nbF (topx + nw + 1) (bn_neg bx) (bn_flags br))).
    { unfold bg_ok, bn_dmax, BG_DMAX. cbn [bn_buf bn_top bn_flags]. rewrite Lnb.
      split; [exact LMnb|]. split; [clear - HDM; unfold bn_dmax in *; lia|]. split; [clear - OKq3; unfold bn_dmax in *; lia| exact OKq4]. }
    pose proof (lib_state_h_parts _ _ _ _ _ _ LSHT) as PARTST.
    unfold QF, bn_postA. do 17 eexists. exists mG, OW2, PL. split; [reflexivity|]. cbn [fst snd].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAPT PARTST FROK MUT WMT HWL3 CEIL ltac:(unfold USTACK_TOP; clear - SPT; lia))|].
    split.
    { unfold lib_state, stF. eapply (lib_state_close [] ls1 mG OW2 PL EA rr ar); [| exact ND2| exact HAr2| exact NRO| | exact OKF|].
      - eapply (lib_state_frame Σ1 LB (bv_unsigned sp) USTACK_TOP); [exact HEAPT| exact LSHT| exact MUT| exact WMT| exact FROK| exact WOK3].
      - exists Dr. split.
        + unfold bn_cells, bn_dmax, MallocRep.wz. cbn [bn_top bn_buf bn_neg bn_flags]. rewrite Lnb.
          replace (Z.of_nat (topx + nw + 1)) with (Z.of_nat topx + Z.of_nat nw + 1) by (clear; lia). exact BNrF.
        + apply (fun ARRnb__ => bn_arr_of_nofr PL rr mG OW2 Dr _ PWF1 NOFR NRO ARRnb__ ltac:(solve_nbuf)). unfold BnRepDefs.bn_arr, bn_dmax. cbn [bn_d bn_buf]. rewrite Edr, Lnb. split; [exact Hinpr| exact UF].
      - apply ids_ok_setbn_same; [exact IDS1| exact HVr2|]. fold br. unfold bn_blocks, bn_dmax. cbn [bn_d bn_buf]. rewrite Edr, Lnb. reflexivity. }
    split; [exact STF|]. split; [exact MIF|].
    split; [eapply ax_pres_trans; [exact AXPT|]; exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAPT PARTST FROK MUT HWL3 CEIL ltac:(clear - LO'; lia))|].
    split; [clear - CR2; lia|].
    split. { unfold cnt_eq in *. unfold stF. rewrite (cnt_bal_setbn rr _ ls1 OW2 OW2 HVr2). fold br. rewrite CNT2.
             unfold bn_blocks, bn_dmax. cbn [bn_d bn_buf]. rewrite Edr, Lnb. cbn [length]. clear. lia. }
    split. { eapply refs_stable_trans; [exact RS2| apply refs_stable_setbn]. }
    unfold shift_res. split; [reflexivity|]. split; [reflexivity| exact BST]. }

  assert (TAIL : forall mT (FT : bvmap 5 word) (fcT : bv 32) (q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q25 q28 q29 q30 q31 : word),
            length nbF = bn_dmax br -> limbs nbF ->
            AHEAP Σ1 OW2 LB mT -> lib_state_hc false [rr] ls1 mT OW2 PL EA -> ax_pres LB (bv_unsigned sp) (XW PL) m mT ->
            u64arr bgbsegs mT Dr (wlimbs nbF) ->
            rw_cells bgbsegs mT ar [C8 (Z_to_bv 64 Dr); C4 (Z_to_bv 64 (Z.of_nat (bn_top br))); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax br)));
                                  C4 (Z_to_bv 64 (Z.b2z (bn_neg br))); C4 (Z_to_bv 64 (bn_flags br))] ->
            ((ax = ar /\ topx = bn_top br /\ bn_neg bx = bn_neg br)
             \/ ((ax + 24 <= ar \/ ar + 24 <= ax) /\ rw_cells bgbsegs mT ax [C8 (Z_to_bv 64 Dx2); C4 (Z_to_bv 64 (Z.of_nat topx)); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax bx)));
                                  C4 (Z_to_bv 64 (Z.b2z (bn_neg bx))); C4 (Z_to_bv 64 (bn_flags bx))])) ->
            rw_cells bgbsegs mT (bv_unsigned sp + -96) [CB 8 (take 8 junk); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
            stk bgbsegs mT lo (bv_unsigned sp + -96) -> mem_inv bgbsegs mT ->
            evt bgbsegs QF
              (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 TP_A) q5 q6 q7 sp (Z_to_bv 64 ar)
                       q10 q11 q12 q13 q14 q15 q16 q17 (Z_to_bv 64 (ax + 8)) (Z_to_bv 64 ax) (Z_to_bv 64 n) (Z_to_bv 64 SHB)
                       (Z_to_bv 64 ((ax + 8) ≫ 3 + SHB)) (Z_to_bv 64 (Z.of_nat nw)) (Z_to_bv 64 (Z.land ar 7)) q25 s10 s11 q28 q29 q30 q31)
                  FT (Z_to_bv 64 0x236064) fcT None mT (seg_rom bgbsegs))).
  { intros mT FT fcT q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q25 q28 q29 q30 q31 Lnb LMnb HEAPT LSHT AXPT UF BNrF XR FRF STF MIF.
    assert (UAR : 0 < ar /\ ar mod 8 = 0) by (split; [clear - SA0; lia | exact ALR]).
    clear BNx2 BNr FR2 ST2 MI2 MU3 WM3 Ur LAf SXR SRX ALXD SXD DXC XC' DX8 DrI DSEPr OFF3 ACR ACX2 ACDR.
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAPT LSHT NOFR HAr2 NRO) as (ACRT & _ & _).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAPT LSHT NOFR HAx2 NROx) as (ACXT & _ & _).
    pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp); (ar, ar + 24)]%Z mT) as MUT. pose proof (wmono_refl bgbsegs mT) as WMT.
    assert (OFFT : offshW [(bv_unsigned sp + -96, bv_unsigned sp); (ar, ar + 24)]).
    { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. clear - OFR SPR LO' CEIL C1 C2 C3 C1' C2' C3'. lia. }
    assert (LENnb : Z.of_nat (length (wlimbs nbF)) = Z.of_nat (bn_dmax br)) by (rewrite wlimbs_len, Lnb; reflexivity).
    destruct XR as [(EAX & ET & EN)|([SEPX|SEPX] & BNxF)].
    -
      subst ax. rewrite <- ET, <- EN in BNrF.
      ub. step. do 2 step. shl_with ACXT ALX2. chk0.
      step. do 2 step. shl_with ACRT ALR. step. rewrite (sx32_small (Z.b2z (bn_neg bx))) by (destruct (bn_neg bx); cbn; clear; lia). chk0.
      step.
      shl_with ACXT ALX2. chk0.
      step. rewrite (sx32_small (Z.of_nat topx)) by (clear - OKy2 OKy3 ETX; unfold bn_dmax in *; lia).
      rewrite ET in BNrF.
      eapply (TAIL2 mT _ FT fcT); eassumption.
    - ub. step. do 2 step. shl_with ACXT ALX2. chk0.
      step. do 2 step. shl_with ACRT ALR. step. rewrite (sx32_small (Z.b2z (bn_neg bx))) by (destruct (bn_neg bx); cbn; clear; lia). chk0.
      step.
      shl_with ACXT ALX2. chk0.
      step. rewrite (sx32_small (Z.of_nat topx)) by (clear - OKy2 OKy3 ETX; unfold bn_dmax in *; lia).
      eapply (TAIL2 mT _ FT fcT); eassumption.
    - ub. step. do 2 step. shl_with ACXT ALX2. chk0.
      step. do 2 step. shl_with ACRT ALR. step. rewrite (sx32_small (Z.b2z (bn_neg bx))) by (destruct (bn_neg bx); cbn; clear; lia). chk0.
      step.
      shl_with ACXT ALX2. chk0.
      step. rewrite (sx32_small (Z.of_nat topx)) by (clear - OKy2 OKy3 ETX; unfold bn_dmax in *; lia).
      eapply (TAIL2 mT _ FT fcT); eassumption. }

  assert (FIN : forall mF (mid : list Z) (FT : bvmap 5 word) (fcT : bv 32) (q1 q5 q6 q7 q10 q11 q13 q15 q16 q17 q25 q28 q29 q30 q31 : word),
            length mid = (topx + 1)%nat -> limbs mid ->
            nbF = repeat 0 nw ++ mid ++ skipn (nw + topx + 1) (bn_buf br) ->
            AHEAP Σ1 OW2 LB mF -> lib_state_hc false [rr] ls1 mF OW2 PL EA -> ax_pres LB (bv_unsigned sp) (XW PL) m mF ->
            rw_cells bgbsegs mF Dr [CB (Z.to_nat (8 * Z.of_nat nw)) (u64s (wlimbs (firstn nw (bn_buf br))))] ->
            u64arr bgbsegs mF (Dr + 8 * Z.of_nat nw) (wlimbs mid) ->
            u64arr bgbsegs mF (Dr + 8 * Z.of_nat (nw + topx + 1)) (wlimbs (skipn (nw + topx + 1) (bn_buf br))) ->
            rw_cells bgbsegs mF ar [C8 (Z_to_bv 64 Dr); C4 (Z_to_bv 64 (Z.of_nat (bn_top br))); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax br)));
                                  C4 (Z_to_bv 64 (Z.b2z (bn_neg br))); C4 (Z_to_bv 64 (bn_flags br))] ->
            ((ax = ar /\ topx = bn_top br /\ bn_neg bx = bn_neg br)
             \/ ((ax + 24 <= ar \/ ar + 24 <= ax) /\ rw_cells bgbsegs mF ax [C8 (Z_to_bv 64 Dx2); C4 (Z_to_bv 64 (Z.of_nat topx)); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax bx)));
                                  C4 (Z_to_bv 64 (Z.b2z (bn_neg bx))); C4 (Z_to_bv 64 (bn_flags bx))])) ->
            rw_cells bgbsegs mF (bv_unsigned sp + -96) [CB 8 (take 8 junk); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
            stk bgbsegs mF lo (bv_unsigned sp + -96) -> mem_inv bgbsegs mF ->
            implA (TRet (tt, stF)) Σ1 (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC (shift_res rr ls OW PL))
              (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 TP_A) q5 q6 q7 sp (Z_to_bv 64 ar)
                       q10 q11 (Z_to_bv 64 (8 * Z.of_nat nw)) q13 (Z_to_bv 64 (ar ≫ 3)) q15 q16 q17 (Z_to_bv 64 (ax + 8)) (Z_to_bv 64 ax) (Z_to_bv 64 n) (Z_to_bv 64 SHB)
                       (Z_to_bv 64 ((ax + 8) ≫ 3 + SHB)) (Z_to_bv 64 (Z.of_nat nw)) (Z_to_bv 64 (Z.land ar 7)) q25 s10 s11 q28 q29 q30 q31)
                  FT (Z_to_bv 64 0x236038) fcT None mF (seg_rom bgbsegs))).
  { intros mF mid FT fcT q1 q5 q6 q7 q10 q11 q13 q15 q16 q17 q25 q28 q29 q30 q31 Lmid LMmid EBUF HEAPF LSHF AXPF CBF UMF UHF BNrF XR FRF STF MIF.
    assert (UAR : 0 < ar /\ ar mod 8 = 0) by (split; [clear - SA0; lia | exact ALR]).
    clear BNx2 BNr FR2 ST2 MI2 MU3 WM3 Ur LAf SXR SRX ALXD DXC XC' DX8 DrI OFF3 ACR ACX2 ACDR TAIL2.
    assert (Lnb : length nbF = bn_dmax br).
    { rewrite EBUF, !length_app, repeat_length, Lmid, length_skipn, LBr. clear - HDM. unfold bn_dmax in *. lia. }
    assert (LMnb : limbs nbF).
    { rewrite EBUF. apply limbs_app; [apply limbs_repeat; unfold limb; rewrite BnArith.BW_lit; clear; lia|]. apply limbs_app; [exact LMmid| apply limbs_skipn; exact OKq1]. }
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAPF LSHF NOFR HAr2 NRO) as (ACRF & _ & _).
    pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp)]%Z mF) as MUF. pose proof (wmono_refl bgbsegs mF) as WMF.
    assert (OFFF : offshW [(bv_unsigned sp + -96, bv_unsigned sp)]).
    { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. clear - SPR LO' CEIL C1 C2 C3 C1' C2' C3'. lia. }
    apply implA_from_evt.
    zstep. rewrite (bk_swrap32_small (n + 63)) by (clear - Hn; lia).
    zstep.
    zstep. if_cases KN; zify_cond KN.
    -
      assert (ENW0 : nw = 0%nat) by (clear - KN Hn Enw; pose proof (proj1 (OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_lshift.nw_zero_iff n ltac:(lia)) KN); lia).
      apply evt_done. apply implA_ret_evt. fold QF.
      eapply (TAIL mF FT fcT); try eassumption.
      rewrite EBUF. rewrite ENW0 in *. cbn [repeat app].
      apply limbarr_app. split.
      + replace (Dr + 8 * Z.of_nat 0) with Dr in UMF by (clear; lia). exact UMF.
      + rewrite Lmid. replace (Dr + 8 * Z.of_nat (topx + 1)) with (Dr + 8 * Z.of_nat (0 + topx + 1)) by (clear; lia). exact UHF.
    -
      assert (NW1 : (1 <= nw)%nat).
      { clear - KN Hn Enw. destruct (Nat.eq_dec nw 0) as [E|E]; [|lia]. exfalso. pose proof (proj2 (OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_lshift.nw_zero_iff n ltac:(lia)) ltac:(lia)). lia. }
      ub. step. shl_with ACRF ALR. chk0.
      step. step. step.
      apply evt_done.
      eapply implA_step_same.
      { eapply (asan_memset_cpsA) with (d := Dr) (n := 8 * Z.of_nat nw) (c := Z_to_bv 8 0) (bd := (pr, Dr, 8 * Z.of_nat (bn_dmax br))) (lo := lo) (OW := OW2) (LB := LB); try reflexivity.
        - exact HEAPF.
        - rewrite ESP. exact STF.
        - exact CEIL.
        - rewrite ESP. unfold RT_STACK. clear - LO'. lia.
        - rewrite ESP. unfold USTACK_TOP. clear - SPT. lia.
        - rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia.
        - exact MIF.
        - apply in_or_app. left. exact Hinpr.
        - cbn [blk_addr blk_size fst snd]. clear - HDM. unfold bn_dmax in *. lia.
        - clear - Hnw Enw. lia. }
      intros msM PO. unfold icall_post in PO. rewrite ?ESP in PO.
      destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F3 & fc3 & mM & -> & MIM & STM & HEAPM & WMM & AGM & BZ & WRM).
      rewrite (ret_pc_even 2318436) by (clear; lia). unfold MallocRep.wz.
      assert (HDMZ : Z.of_nat nw + Z.of_nat topx + 1 <= Z.of_nat (bn_dmax br)) by (clear - HDM; unfold bn_dmax in *; lia).
      assert (INR : In (qr2, Ar2, nr2) (OW2 ++ LB)) by (apply in_or_app; left; exact Hinr2).
      assert (INP : In (pr, Dr, 8 * Z.of_nat (bn_dmax br)) (OW2 ++ LB)) by (apply in_or_app; left; exact Hinpr).
      apply (rw_cells_agree _ _ _ _ _ AGM) in BNrF.
      2:{ intros x Hx. cbn in Hx. split; [right; right; exists (qr2, Ar2, nr2); split; [exact INR| cbn [blk_addr blk_size fst snd]; clear - Hx Rr21 Rr22; lia]| clear - Hx SEPrr HDMZ; lia]. }
      apply (rw_cells_agree _ _ _ _ _ AGM) in FRF.
      2:{ intros x Hx. cbn in Hx. split; [left; unfold USTACK_TOP; clear - Hx SPT; lia| unfold BnHeapA.ACEIL in *; clear - Hx DrC HDMZ CEIL LO'; lia]. }
      assert (UMM : u64arr bgbsegs mM (Dr + 8 * Z.of_nat nw) (wlimbs mid)).
      { eapply (LibKitA.u64arr_agree _ _ _ _ _ AGM); [exact UMF|]. intros x Hx. rewrite wlimbs_len, Lmid in Hx.
        split; [right; right; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); split; [exact INP| cbn [blk_addr blk_size fst snd]; clear - Hx HDMZ; lia]| clear - Hx; lia]. }
      assert (UHM : u64arr bgbsegs mM (Dr + 8 * Z.of_nat (nw + topx + 1)) (wlimbs (skipn (nw + topx + 1) (bn_buf br)))).
      { eapply (LibKitA.u64arr_agree _ _ _ _ _ AGM); [exact UHF|]. intros x Hx. rewrite wlimbs_len, length_skipn, LBr in Hx.
        split; [right; right; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); split; [exact INP| cbn [blk_addr blk_size fst snd]; clear - Hx HDMZ; lia]| clear - Hx; lia]. }
      assert (XRM : (ax = ar /\ topx = bn_top br /\ bn_neg bx = bn_neg br)
                    \/ ((ax + 24 <= ar \/ ar + 24 <= ax) /\ rw_cells bgbsegs mM ax [C8 (Z_to_bv 64 Dx2); C4 (Z_to_bv 64 (Z.of_nat topx)); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax bx)));
                                  C4 (Z_to_bv 64 (Z.b2z (bn_neg bx))); C4 (Z_to_bv 64 (bn_flags bx))])).
      { destruct XR as [XR|(SEPX & BNxF)]; [left; exact XR| right]. split; [exact SEPX|].
        eapply (rw_cells_agree _ _ _ _ _ AGM); [exact BNxF|]. intros x Hx. cbn in Hx. split.
        - eapply (ref_at_client ls1 OW2 PL EA (bv_unsigned sp) USTACK_TOP Σ1 LB mF rx ax (OW2 ++ LB) (bv_unsigned sp + -96) x HEAPF PARTS1 FROK HAx2 NROx);
            [clear; lia| unfold USTACK_TOP; clear; lia| intros b0 Hb0; apply in_or_app; left; exact Hb0| clear - Hx; lia| lb_in_heap].
        - clear - Hx SXD HDMZ. lia. }
      assert (LSHM : lib_state_hc false [rr] ls1 mM OW2 PL EA).
      { eapply (lib_state_h_icall Σ1 LB [rr] ls1 mF mM OW2 PL EA (bv_unsigned sp + -96) (bv_unsigned sp) Dr (8 * Z.of_nat nw) HEAPF LSHF FROK ltac:(clear; lia) AGM).
        eapply (w_limbs OW2 LB ls1 PL EA (bv_unsigned sp) false [rr] _ rr pr Dr); [left; reflexivity| exact HVr2| exact Edr| exact Hinpr| cbn [fst snd]; clear; lia| cbn [fst snd]; fold br; clear - HDMZ; lia]. }
      assert (AXPM : ax_pres LB (bv_unsigned sp) (XW PL) m mM).
      { eapply ax_pres_trans; [exact AXPF|]. eapply (ax_pres_weaken LB (bv_unsigned sp + -96)); [|clear; lia].
        eapply (ax_pres_of_icall Σ1 OW2 LB mF mM (bv_unsigned sp + -96) (XW PL) Dr (8 * Z.of_nat nw) (pr, Dr, 8 * Z.of_nat (bn_dmax br)) HEAPF Hinpr);
          [cbn [blk_addr blk_size fst snd]; clear; lia| cbn [blk_addr blk_size fst snd]; clear - HDMZ; lia| clear - CEIL LO'; lia| exact AGM]. }
      assert (PZ : rw_cells bgbsegs mM Dr [CB (8 * nw) (repeat (Z_to_bv 8 0) (8 * nw))]).
      { replace (Z.to_nat (8 * Z.of_nat nw)) with (8 * nw)%nat in BZ by (clear; lia).
        split; [split; [cbn [cells_wf cell_wf]; rewrite repeat_length; clear; tauto| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BZ]|].
        cbn [cells_size csize Nat.add]. replace (Z.of_nat (8 * nw + 0)) with (8 * Z.of_nat nw) by (clear; lia). exact WRM. }
      apply implA_ret_evt. fold QF.
      eapply (TAIL mM F3 fc3); try eassumption.
      rewrite EBUF. apply limbarr_app. split.
      + eapply CB_u64arr. rewrite lbytes_repeat0. exact PZ.
      + rewrite repeat_length. apply limbarr_app. split; [exact UMM|].
        rewrite Lmid. replace (Dr + 8 * Z.of_nat nw + 8 * Z.of_nat (topx + 1)) with (Dr + 8 * Z.of_nat (nw + topx + 1)) by (clear; lia). exact UHM. }

  clear TAIL TAIL2.
  assert (XR2 : (ax = ar /\ topx = bn_top br /\ bn_neg bx = bn_neg br)
                \/ ((ax + 24 <= ar \/ ar + 24 <= ax) /\ rw_cells bgbsegs m2 ax [C8 (Z_to_bv 64 Dx2); C4 (Z_to_bv 64 (Z.of_nat topx)); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax bx)));
                                  C4 (Z_to_bv 64 (Z.b2z (bn_neg bx))); C4 (Z_to_bv 64 (bn_flags bx))])).
  { destruct (Nat.eq_dec rx rr) as [E|NE].
    - left. pose proof HAx2 as HAx3. rewrite E in HAx3. split; [exact (ref_at_fun _ _ _ _ _ _ ND2 HAx3 HAr2)|]. subst bx br. rewrite E in *. split; [symmetry; exact ETX| reflexivity].
    - right. split; [exact (struct_disj Σ1 OW2 LB m2 HEAP2 ls1 PL EA _ _ PARTS1 FROK rx rr ax ar NE HAx2 HAr2)| exact BNx2]. }
  destruct (arr_shA _ _ _ _ _ _ HEAP2 ARRxo) as (ACDX & ALDX & _). fold bx in ACDX.
  assert (HDM' : (nw + bn_top bx + 1 <= length (bn_buf br))%nat) by (rewrite ETX, LBr; clear - HDM; unfold bn_dmax in *; lia).
  assert (HDMZ : Z.of_nat nw + Z.of_nat topx + 1 <= Z.of_nat (bn_dmax br)) by (clear - HDM; unfold bn_dmax in *; lia).
  destruct (proj1 (limbarr_split bgbsegs m2 Dr (bn_buf br) nw ltac:(rewrite LBr; clear - HDMZ; lia)) Ur) as (Ulo & Urest).
  destruct (proj1 (limbarr_split bgbsegs m2 (Dr + 8 * Z.of_nat nw) (skipn nw (bn_buf br)) (topx + 1) ltac:(rewrite length_skipn, LBr; clear - HDMZ; lia)) Urest) as (Umid & Uhi).
  pose proof (limbarr_CB bgbsegs m2 _ _ Ulo) as CBlo.
  rewrite firstn_length_le in CBlo by (rewrite LBr; clear - HDMZ; lia).
  replace (8 * nw)%nat with (Z.to_nat (8 * Z.of_nat nw)) in CBlo by (clear; lia).
  replace (Dr + 8 * Z.of_nat nw + 8 * Z.of_nat (topx + 1)) with (Dr + 8 * Z.of_nat (nw + topx + 1)) in Uhi by (clear; lia).
  rewrite skipn_skipn in Uhi. replace (topx + 1 + nw)%nat with (nw + topx + 1)%nat in Uhi by (clear; lia).
  destruct (proj1 (limbarr_limbs_at bgbsegs m2 _ _) Umid) as (_ & WRmid).
  rewrite firstn_length_le in WRmid by (rewrite length_skipn, LBr; clear - HDMZ; lia).
  clear Ulo Urest Ur.
  assert (BDR : 0 <= Dr /\ Dr + 8 * Z.of_nat (bn_dmax br) <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - Dr0 DrC C1 C2 C3 C1' C2' C3'; lia).

  assert (ENVW : forall mW, munch [(Dr + 8 * Z.of_nat nw, Dr + 8 * Z.of_nat nw + 8 * (Z.of_nat topx + 1))]%Z m2 mW -> wmono bgbsegs m2 mW ->
            AHEAP Σ1 OW2 LB mW /\ lib_state_hc false [rr] ls1 mW OW2 PL EA /\ ax_pres LB (bv_unsigned sp) (XW PL) m mW).
  { intros mW MUW WMW.
    assert (HWLW : Forall (w_lib ls1 OW2 PL lo (bv_unsigned sp)) [(Dr + 8 * Z.of_nat nw, Dr + 8 * Z.of_nat nw + 8 * (Z.of_nat topx + 1))]).
    { constructor; [right; left; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn [blk_addr blk_size fst snd]; split; [exact Hinpr| clear - HDMZ; lia]| constructor]. }
    assert (WOKW : Forall (w_ok OW2 LB ls1 PL EA (bv_unsigned sp) [rr]) [(Dr + 8 * Z.of_nat nw, Dr + 8 * Z.of_nat nw + 8 * (Z.of_nat topx + 1))]).
    { constructor; [eapply (w_limbs OW2 LB ls1 PL EA (bv_unsigned sp) false [rr] _ rr pr Dr); [left; reflexivity| exact HVr2| exact Edr| exact Hinpr| cbn [fst snd]; clear; lia| cbn [fst snd]; fold br; clear - HDMZ; lia]| constructor]. }
    split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 FROK MUW WMW HWLW CEIL ltac:(unfold USTACK_TOP; clear - SPT; lia))|].
    split; [exact (lib_state_frame Σ1 LB (bv_unsigned sp) USTACK_TOP [rr] ls1 m2 mW OW2 PL EA _ HEAP2 LSH MUW WMW FROK WOKW)|].
    eapply ax_pres_trans; [exact AXP2|]. exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 FROK MUW HWLW CEIL ltac:(clear - LO'; lia)). }
  assert (DJW : forall A k, (A + k <= Dr \/ Dr + 8 * Z.of_nat (bn_dmax br) <= A) ->
            disjoint_from [(Dr + 8 * Z.of_nat nw, Dr + 8 * Z.of_nat nw + 8 * (Z.of_nat topx + 1))] A k).
  { intros A k H. cbn [disjoint_from]. split; [|exact I]. clear - H HDMZ. lia. }
  apply implA_from_evt.
  zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by (clear - SA0 SAC; unfold BnHeapA.ACEIL in *; lia). clear - KZ SA0. lia. }
  shl_with ACX2 ALX2. chk0.
  step. rewrite (sx32_small (Z.of_nat topx)) by (clear - OKy2 OKy3 ETX; unfold bn_dmax in *; lia).
  assert (UAR : 0 < ar /\ ar mod 8 = 0) by (split; [clear - SA0; lia | exact ALR]).
  assert (PR0 : 0 < Dr) by (pose proof (AH_range _ _ _ _ _ _ _ HEAP2 Hinpr) as (P0 & _); exact P0).
  hide_ors. ub. unhide.
  do 2 zstep.
  replace (Z.of_nat nw ≪ 3) with (8 * Z.of_nat nw) by (rewrite Z.shiftl_mul_pow2 by (clear; lia); clear; lia).
  zstep. if_cases KT; zify_cond KT.
  -
    assert (ETOP : topx = 0%nat) by (clear - KT; lia).
    assert (EMID : OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_lshift.lshift_mid bx lb = [0]) by (unfold OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_lshift.lshift_mid; rewrite ETX, ETOP; reflexivity).
    pose proof (OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_lshift.lshift_buf_parts br bx nw lb ltac:(rewrite EMID, ETX, ETOP; reflexivity) HDM') as EBUF. rewrite EMID, ETX in EBUF. fold nbF in EBUF.
    hide_ors. ub. unhide.
    step. shl_with ACR ALR. chk0.
    step. zstep.
    hide_ors. ub.
    do 4 zstep. ub. unhide.
    do 2 step. shl_limb ACDR ALDR BDR (Z.of_nat nw). chk0.
    set (T := Dr + 8 * Z.of_nat nw) in *.
    assert (T0 : 0 <= T) by (subst T; clear - Dr0; lia).
    assert (TB : T + 8 <= 140737488355328) by (subst T; clear - BDR HDMZ; lia).
    assert (SOKA : store_ok bgbsegs m2 (Z_to_bv 64 T) 8 = true).
    { pose proof (wr_at_store_ok bgbsegs m2 T (8 * Z.of_nat (topx + 1)) 0 8 WRmid ltac:(clear; lia) ltac:(clear; lia)) as X.
      rewrite Z.add_0_r in X. exact X. }
    rewrite ?Z.add_0_r.
    zstep.
    assert (L8 : length (le8 (Z_to_bv 64 0)) = 8%nat) by apply length_le8.
    change (Z_to_bv 64 T) with (wa T) in *.
    pose proof (munch_refl [(T, T + 8 * (Z.of_nat topx + 1))]%Z m2) as MUb. pose proof (wmono_refl bgbsegs m2) as WMb.
    apply (munch_write _ m2 m2 T (le8 (Z_to_bv 64 0))) in MUb; [| exact T0 | rewrite L8; clear - TB; lia | rewrite L8; cbn [inside]; left; clear; lia].
    apply (wmono_write bgbsegs m2 m2 (wa T) (le8 (Z_to_bv 64 0))) in WMb.
    pose proof (mem_inv_store bgbsegs m2 (wa T) (le8 (Z_to_bv 64 0)) MI2 ltac:(rewrite L8; exact SOKA)) as MI3.
    assert (UM3 : u64arr bgbsegs (write_to_mem m2 (wa T) (le8 (Z_to_bv 64 0))) T (wlimbs [0])).
    { apply limbarr_limbs_at. split.
      - apply (limbs_at_cons_writeA m2 T 0 []); [apply limbs_at_nil; clear - T0 TB; lia| exact T0].
      - cbn [length]. apply wr_at_write. eapply (wr_at_sub bgbsegs m2 T (8 * Z.of_nat (topx + 1)) 0 (8 * Z.of_nat 1)) in WRmid; [rewrite Z.add_0_r in WRmid; exact WRmid| clear; lia| clear; lia| clear; lia]. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => set (m3 := mx) end.
    change (write_to_mem m2 (wa T) (le8 (Z_to_bv 64 0))) with m3 in MUb, WMb, MI3, UM3. clearbody m3.
    destruct (ENVW m3 MUb WMb) as (HEAP3 & LSH3 & AXP3).
    eapply (rw_cells_transport bgbsegs _ m2 m3) in BNr; [| exact MUb | exact WMb | apply DJW; cbn; clear - SEPrr; lia].
    eapply (rw_cells_transport bgbsegs _ m2 m3) in FR2; [| exact MUb | exact WMb | apply DJW; cbn; unfold BnHeapA.ACEIL in *; clear - DrC CEIL LO'; lia].
    eapply (stk_transport_disjoint bgbsegs _ m2 m3) in ST2; [| exact MUb | exact WMb | apply DJW; unfold BnHeapA.ACEIL in *; clear - DrC CEIL LO'; lia].
    eapply (rw_cells_transport bgbsegs _ m2 m3) in CBlo; [| exact MUb | exact WMb | cbn [disjoint_from cells_size csize Nat.add]; split; [|exact I]; subst T; clear; lia].
    eapply (u64arr_transport bgbsegs _ m2 m3) in Uhi; [| exact MUb | exact WMb | cbn [disjoint_from]; split; [|exact I]; subst T; clear; lia].
    assert (XR3 : (ax = ar /\ topx = bn_top br /\ bn_neg bx = bn_neg br)
                  \/ ((ax + 24 <= ar \/ ar + 24 <= ax) /\ rw_cells bgbsegs m3 ax [C8 (Z_to_bv 64 Dx2); C4 (Z_to_bv 64 (Z.of_nat topx)); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax bx)));
                                  C4 (Z_to_bv 64 (Z.b2z (bn_neg bx))); C4 (Z_to_bv 64 (bn_flags bx))])).
    { destruct XR2 as [XR|(SEPX & BNxF)]; [left; exact XR| right]. split; [exact SEPX|].
      eapply (rw_cells_transport bgbsegs _ m2 m3); [exact BNxF| exact MUb | exact WMb | apply DJW; cbn; clear - SXD; lia]. }
    step.
    apply evt_done.
    eapply (FIN m3 [0] F2 fc2); try eassumption.
    + rewrite ETOP. reflexivity.
    + constructor; [unfold limb; rewrite BnArith.BW_lit; clear; lia| constructor].
  -
    assert (NTOP : (1 <= topx)%nat) by (clear - KT; lia).
    pose proof (arr_ceilA _ _ _ _ _ _ HEAP2 ARRxo) as (_ & DXC47). fold bx in DXC47.
    assert (BDX : 0 <= Dx2 /\ Dx2 + 8 * Z.of_nat (bn_dmax bx) <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - DX0 DXC47 C1 C2 C3 C1' C2' C3'; lia).
    assert (UDX : 8 <= Dx2) by (apply DX8; clear - NTOP; lia).
    assert (TX31 : Z.of_nat topx < 2147483648 /\ Z.of_nat topx <= Z.of_nat (bn_dmax bx)) by (clear - OKy2 OKy3 ETX; unfold bn_dmax in *; lia).

    do 2 step. shl_with ACX2 ALX2. chk0.
    hide_ors. ub. unhide.
    step. shl_with ACR ALR. chk0.
    step. zstep. zstep.
    replace (Z.b2z (0 <? Dr)) with 1 by (rewrite (proj2 (Z.ltb_lt 0 Dr)) by (clear - PR0; lia); reflexivity).
    hide_ors. ub.
    zstep. rewrite (bk_swrap32_small (Z.of_nat topx + -1)) by (clear - NTOP TX31; lia).
    ub. unhide.
    step.
    zstep. replace (Z.shiftl (Z.of_nat topx + -1) 3) with (8 * Z.of_nat topx - 8) by (rewrite Z.shiftl_mul_pow2 by (clear; lia); clear; lia).
    zstep.
    hide_ors. ub. unhide.
    do 2 step. shl_limb ACDX ALDX BDX (Z.of_nat topx - 1). chk0.
    zstep. replace (Z.shiftl (Z.of_nat topx) 3) with (8 * Z.of_nat topx) by (rewrite Z.shiftl_mul_pow2 by (clear; lia); clear; lia).
    zstep.
    hide_ors. ub. unhide.
    do 2 step. shl_limb ACDR ALDR BDR (Z.of_nat nw + Z.of_nat topx). chk0.
    assert (LfZ : Z.of_nat (length f) = Z.of_nat topx) by (rewrite Lf; reflexivity).
    replace (Z.of_nat topx) with (Z.of_nat (length f)) by exact LfZ.

    setreg 7%Z (Z_to_bv 64 (Z.of_nat (length f) - 1)) ltac:(f_equal; clear; lia).
    setreg 11%Z (Z_to_bv 64 (Dx2 + 8 * (Z.of_nat (length f) - 1))) ltac:(f_equal; clear; lia).
    setreg 13%Z (Z_to_bv 64 (Dr + 8 * Z.of_nat nw + 8 * Z.of_nat (length f))) ltac:(f_equal; clear; lia).
    assert (LMf : limbs f) by (subst f; apply limbs_firstn; exact OKy1).
    pose proof (lshift_limbs_seq f lb) as ESEQ.
    pose proof (lshift_limbs_spec f lb 0 LMf Hlb ltac:(split; [clear; lia| apply Z.pow_pos_nonneg; clear - Hlb; lia])) as LSP.
    destruct (lshift_limbs f lb 0) as [ls0 mo] eqn:ELS. cbn [fst snd] in ESEQ. destruct LSP as (LS0 & LL0 & LMO & _).
    assert (Lnew : length (ls0 ++ [mo]) = (topx + 1)%nat) by (rewrite length_app, LL0, Lf; cbn [length]; clear; lia).
    assert (LIMBnew : limbs (ls0 ++ [mo])).
    { apply limbs_app; [exact LS0|]. apply limbs_cons; [|apply limbs_nil]. unfold limb. rewrite BW_pow.
      split; [clear - LMO; lia|]. apply Z.lt_le_trans with (2 ^ lb); [clear - LMO; lia|]. apply Z.pow_le_mono_r; clear - Hlb; lia. }
    assert (EMID : OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_lshift.lshift_mid bx lb = ls0 ++ [mo]).
    { unfold OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_lshift.lshift_mid. rewrite ETX. replace (topx =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; clear - NTOP; lia). fold f. rewrite ELS. reflexivity. }
    pose proof (OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_lshift.lshift_buf_parts br bx nw lb ltac:(rewrite EMID, ETX; exact Lnew) HDM') as EBUF. rewrite EMID, ETX in EBUF. fold nbF in EBUF.
    assert (DISJ : Dx2 <= Dr + 8 * Z.of_nat nw \/ Dr + 8 * Z.of_nat nw + 8 * (Z.of_nat (length f) + 1) <= Dx2) by (clear - ALXD HDMZ LfZ; lia).
    assert (HTOP : 1 <= Z.of_nat (length f) < 2147483647) by (clear - LfZ NTOP OKy2 OKy3 ETX; unfold bn_dmax in *; lia).
    assert (HFP : 8 <= Dx2) by (apply DX8; clear - NTOP; lia).
    assert (ELB : Z.land n 63 = lb) by (subst lb; change 63 with (Z.ones 6); apply Z.land_ones; clear; lia).
    assert (HN31 : 0 <= n < 2147483648) by (clear - Hn; lia).
    eapply (lshg_blockA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 f Dx2 Dr (8 * Z.of_nat nw) n lb).
    { exact HN31. }
    { exact Hlb. }
    { exact ELB. }
    { exact LMf. }
    { exact HTOP. }
    { exact HFP. }
    { exact Dr0. }
    { clear. lia. }
    { exact DISJ. }
    { eapply acc_sub; [exact ACDX | clear; lia | clear - LfZ OKy2 ETX; unfold bn_dmax in *; lia]. }
    { eapply acc_sub; [exact ACDR | clear; lia | clear - LfZ HDMZ; lia]. }
    { exact ALDX. }
    { clear - ALDR. Z.div_mod_to_equations. lia. }
    { cbn [offshW]. unfold SHLO, SHHI. clear - OFDR HDMZ Dr0 LfZ. lia. }
    { clear - PR0; lia. }
    { exact PR0. }
    { exact LAf. }
    { replace (8 * (Z.of_nat (length f) + 1)) with (8 * Z.of_nat (topx + 1)) by (clear - LfZ; lia). exact WRmid. }
    { exact MI2. }
    intros m3 z6 z7 z11 z13 z15 z25 z28 z29 z30 z31 HRES MI3 MUb WMb.
    rewrite LfZ in MUb.
    destruct (ENVW m3 MUb WMb) as (HEAP3 & LSH3 & AXP3).
    eapply (rw_cells_transport bgbsegs _ m2 m3) in BNr; [| exact MUb | exact WMb | apply DJW; cbn; clear - SEPrr; lia].
    eapply (rw_cells_transport bgbsegs _ m2 m3) in FR2; [| exact MUb | exact WMb | apply DJW; cbn; unfold BnHeapA.ACEIL in *; clear - DrC CEIL LO'; lia].
    eapply (stk_transport_disjoint bgbsegs _ m2 m3) in ST2; [| exact MUb | exact WMb | apply DJW; unfold BnHeapA.ACEIL in *; clear - DrC CEIL LO'; lia].
    eapply (rw_cells_transport bgbsegs _ m2 m3) in CBlo; [| exact MUb | exact WMb | cbn [disjoint_from cells_size csize Nat.add]; split; [|exact I]; clear; lia].
    eapply (u64arr_transport bgbsegs _ m2 m3) in Uhi; [| exact MUb | exact WMb | cbn [disjoint_from]; split; [|exact I]; clear; lia].
    assert (XR3 : (ax = ar /\ topx = bn_top br /\ bn_neg bx = bn_neg br)
                  \/ ((ax + 24 <= ar \/ ar + 24 <= ax) /\ rw_cells bgbsegs m3 ax [C8 (Z_to_bv 64 Dx2); C4 (Z_to_bv 64 (Z.of_nat topx)); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax bx)));
                                  C4 (Z_to_bv 64 (Z.b2z (bn_neg bx))); C4 (Z_to_bv 64 (bn_flags bx))])).
    { destruct XR2 as [XR|(SEPX & BNxF)]; [left; exact XR| right]. split; [exact SEPX|].
      eapply (rw_cells_transport bgbsegs _ m2 m3); [exact BNxF| exact MUb | exact WMb | apply DJW; cbn; clear - SXD; lia]. }
    apply evt_done.
    eapply (FIN m3 (ls0 ++ [mo]) F2 fc2); try eassumption.
    apply limbarr_limbs_at. split; [rewrite ESEQ; exact HRES|].
    rewrite Lnew. eapply wr_at_transport; [exact WRmid | exact WMb].
Qed.

End WithRT.
