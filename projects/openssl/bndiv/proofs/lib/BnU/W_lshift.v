(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.openssl.bndiv.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BnBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.U Require Import Layout Lib_iface Lib_kit.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bndiv.lib.BnWU Require Import BnUTac.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr ShiftPure.
From OSSVerify.Proofs.openssl.bndiv.lib.BnU Require Import BnHeap BnRep BnIface W_expand BnLeaves BnUAlign LshiftArr.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Lemma bnref_eqb_false : forall x y, bnref_eqb x y = false -> x <> y.
Proof.
  intros x y H E. subst y. destruct x; cbn in H; try discriminate. rewrite Nat.eqb_refl in H. discriminate.
Qed.

(* [comment removed for export] *)
Definition nw_m (n : Z) : Z :=
  bv_swrap 32 (Z.shiftr (bv_swrap 32 (Z.land (n + Z.shiftr (Z.land (Z.shiftl n 1) 18446744073709551615) 58) 18446744073709551615)) 6).
Lemma nw_m_chk : forallb (fun n => nw_m n =? 0) (map Z.of_nat (seq 0 64)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma nw_m_0 : forall n, 0 <= n < 64 -> nw_m n = 0.
Proof.
  intros n H. pose proof nw_m_chk as A. rewrite forallb_forall in A. specialize (A n). rewrite Z.eqb_eq in A. apply A.
  apply in_map_iff. exists (Z.to_nat n). split; [lia|]. apply in_seq. lia.
Qed.

(* [comment removed for export] *)
Definition negw_m (n : Z) : Z := (bv_swrap 32 (0 - n)) mod 18446744073709551616.
Lemma negw_m_chk : forallb (fun n => negw_m n mod 64 =? (64 - n) mod 64) (map Z.of_nat (seq 0 64)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma negw_m_eq : forall n, 0 <= n < 64 -> negw_m n mod 64 = (64 - n) mod 64.
Proof.
  intros n H. pose proof negw_m_chk as A. rewrite forallb_forall in A. specialize (A n). rewrite Z.eqb_eq in A. apply A.
  apply in_map_iff. exists (Z.to_nat n). split; [lia|]. apply in_seq. lia.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_LSHIFT : Z := 0xfef94.
Definition BN_LSHIFT_STACK : Z := 64 + BN_WEXPAND_STACK.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma bn_lshift_fixed_top_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
      (lo B : Z) (errv : word) (rr rx : bnref) (ar ax : Z) (n : Z),
    bn_pre s ls m OW LB AD EA sp lo B errv BN_LSHIFT_STACK -> tp = wz RATP ->
    ref_at ls OW AD rr ar -> ref_at ls OW AD rx ax -> a0 = wz ar -> a1 = wz ax -> a2 = wz n -> 0 <= n < 64 ->
    implM usegs (interp (embed (bn_lshift_fixed_top (tree_ops bptr) rr rx n ls))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA
               (fun _ _ _ a0' => a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_LSHIFT) fc None m (seg_rom usegs)).
  Proof.
    intros until n. intros (HEAP & LS & AUX & SPB & ST & CEIL & GLO & LO & ERR & MI) -> HAr HAx -> -> -> Hn.
    unfold BN_LSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, BN_LSHIFT, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    unfold bn_lshift_fixed_top.
    destruct (bnref_eqb rr rx) eqn:ERX; cbn [orb]. { unfold bunr. cbn [unreachable tree_ops embed interp]. apply implM_interp_unr. }
    apply bnref_eqb_false in ERX.
    replace (n <? 64) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
    unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
    (* [comment removed for export] *)
    destruct (lib_state_open [] ls m OW AD EA rx ax LS ND HAx ltac:(intros [])) as ((Dx & BNx & ARRx) & (OKx1 & OKx2 & OKx3 & OKx4) & _).
    set (bx := getbn rx ls) in *.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
    destruct (ref_at_inb _ _ _ _ _ ADB HAx) as (qx & Ax & nx & Eqx & Hinx & Rx1 & Rx2).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP Hinx) as (XA0 & XA16 & _ & XAC & XAI).
    destruct (ref_at_inb _ _ _ _ _ ADB HAr) as (qr & Ar & nr & Eqr & Hinr & Rr1 & Rr2).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP Hinr) as (RA0 & RA16 & _ & RAC & RAI).
    unfold bn_cells in BNx. unfold BN_WORDS_MAX in OKx3.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3353240 - 164) with 3353076 in ERR.
    unfold implM. iprefix.
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ HEAP ADB HAx) as (AX0 & AX8).
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ HEAP ADB HAr) as (AR0 & AR8).
    carve_frame 64%nat ST. do 9 step.
    chk ltac:(fun C => rewrite ?unsigned_lit in C by lia; lia).
    do 2 step. zstep. rewrite (land7 ax) by exact AX8.
    chk ltac:(fun C => clear - C; lia).
    step. zstep.
    step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (bn_top bx))) by lia.
    do 3 zstep.
    setreg 20%Z (Z_to_bv 64 0) ltac:(f_equal; symmetry; apply (nw_m_0 n Hn)).
    do 2 zstep.
    rewrite (bk_swrap32_small (Z.of_nat (bn_top bx) + 0)) by lia. rewrite Z.add_0_r.
    chk ltac:(fun C => clear - C; lia).
    do 2 zstep.
    rewrite (bk_swrap32_small (Z.of_nat (bn_top bx) + 0)) by lia. rewrite (bk_swrap32_small (Z.of_nat (bn_top bx) + 1)) by lia. rewrite Z.add_0_r.
    zstep. rewrite lts_signed by lia. if_cases KO; zify_cond KO. { exfalso. clear - KO. lia. } clear KO.
    do 2 zstep.
    setreg 11%Z (Z_to_bv 64 (Z.of_nat (bn_top bx + 1))) ltac:(f_equal; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
    assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB ls AD EA []) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL) as HEAP1.
    pose proof (lib_state_frame s LB [] ls m m1 OW AD EA _ HEAP LS MU WM WOK) as LS1.
    assert (AUX1 : rauxv_ok m1 B) by (apply (seg_auxv _ _ _ _ _ _ _ _ _ HEAP AUX MU WM HWL SPB); unfold GLOBALS_TOP; lia).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HAr) as HVr.
    pose proof (st_okm_getbn rr ls SOK HVr) as (OKr1 & OKr2 & OKr3 & OKr4).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply implM_embed_leaves; [apply (bn_wexpand_leaves rr (bn_top bx + 1) ls HVr OKr2)|].
      eapply (bn_wexpand_walk HM HF) with (lo := lo) (B := B) (errv := errv) (r := rr) (a := ar) (OW := OW) (LB := LB) (AD := AD) (EA := EA);
        [| reflexivity | exact HAr | reflexivity | reflexivity | lia].
      unfold bn_pre. rewrite ESP.
      split; [exact HEAP1|]. split; [exact LS1|]. split; [exact AUX1|]. split; [lia|].
      split; [exact ST|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; lia|]. split; [unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK; lia|].
      split; [unfold LX_ERRNO, RATP; exact ERR| exact MI]. }
    cbv beta. intros [u ls1] st1 ms1 [PO LEAF]. unfold bn_post in PO. cbn [fst snd] in *.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & OW2 & errv2 & -> & HEAP2 & LS2 & AUX2 & ST2 & ERR2
                    & MI2 & LXP2 & FA2 & SO2 & RST2 & -> & HDM & WRES).
    rewrite ESP in *.
    replace (ret_pc (Z_to_bv 64 1044484)) with (Z_to_bv 64 1044484) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct LEAF as (LF1 & LF2 & LF3 & LF4 & LF5). cbn [snd] in *.
    assert (Ebx : getbn rx ls1 = bx) by (apply LF1; exact ERX).
    pose proof (RST2 _ _ HAr) as HAr2. pose proof (RST2 _ _ HAx) as HAx2.
    pose proof (RH_nodup_l _ _ _ _ HEAP2) as ND2.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS2) as (IDS2 & ADB2 & ERRB2 & SOK2).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HAr2) as HVr2. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HAx2) as HVx2.
    (* [comment removed for export] *)
    destruct (lib_state_open [] ls1 m2 OW2 AD EA rx ax LS2 ND2 HAx2 ltac:(intros [])) as ((Dx2 & BNx2 & ARRx2) & _ & _).
    rewrite Ebx in BNx2, ARRx2.
    destruct (lib_state_open [] ls1 m2 OW2 AD EA rr ar LS2 ND2 HAr2 ltac:(intros [])) as ((Dr & BNr & ARRr) & (OKq1 & OKq2 & OKq3 & OKq4) & LSH).
    set (br := getbn rr ls1) in *.
    destruct (bn_arr_facts st1 OW2 LB m2 HEAP2 ls1 AD EA IDS2 ADB2 rr Dr HVr2 ARRr) as (Ur & LENr & Dr0 & DrC & DrI & DSEPr).
    fold br in Ur, LENr, DrC, DrI, DSEPr.
    pose proof (DSEPr rr ar HAr2) as SEPrr. pose proof (DSEPr rx ax HAx2) as SEPrx.
    pose proof (struct_disj st1 OW2 LB m2 HEAP2 ls1 AD EA IDS2 ADB2 rr rx ar ax ERX HAr2 HAx2) as SDJ.
    destruct (ref_at_inb _ _ _ _ _ ADB2 HAx2) as (qx2 & Ax2 & nx2 & Eqx2 & Hinx2 & Rx21 & Rx22).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP2 Hinx2) as (XB0 & XB16 & _ & XBC & XBI).
    destruct (ref_at_inb _ _ _ _ _ ADB2 HAr2) as (qr2 & Ar2 & nr2 & Eqr2 & Hinr2 & Rr21 & Rr22).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP2 Hinr2) as (RB0 & RB16 & _ & RBC & RBI).
    unfold bn_cells in BNx2, BNr. unfold BN_WORDS_MAX in OKq3.
    (* [comment removed for export] *)
    assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -64) [CB 8 (take 8 (take 16 (take 24 (take 32 (take 40 (take 48 (take 56 junk)))))));
                                                           C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply rw_cells_agree; [apply agree_of_lx_pres; exact LXP2 | exact FR |].
      intros a Ha. cbn in Ha. split; [|left; lia]. unfold LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    clear FR.
    cbn [embed interp]. apply implM_ret.
    pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m2) as MU3.
    pose proof (wmono_refl usegs m2) as WM3.
    unfold LX_ERRNO, RATP in ERR2. change (3353240 - 164) with 3353076 in ERR2.
    unfold MallocRep.wz in *.
    zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by lia. lia. }
    step. rewrite (sx32_small (Z.of_nat (bn_top bx))) by lia.
    zstep. rewrite (land7 ar) by exact AR8.
    zstep.
    (* [comment removed for export] *)
    assert (HDr : exists pr, bn_d br = Some pr /\ In (pr, Dr, 8 * Z.of_nat (bn_dmax br)) OW2).
    { unfold bn_arr in ARRr. destruct (bn_d br) as [pr|]; [exists pr; split; [reflexivity| exact (proj1 ARRr)]|].
      exfalso. destruct ARRr as [_ E]. unfold bn_dmax in HDM. rewrite E in HDM. cbn in HDM. lia. }
    destruct HDr as (pr & Edr & Hinpr).
    (* [comment removed for export] *)
    assert (FIN : forall mF (nb : list Z) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
              length nb = bn_dmax br -> limbs nb ->
              u64arr usegs mF Dr (wlimbs nb) ->
              rw_cells usegs mF ax [C8 (Z_to_bv 64 Dx2); C4 (Z_to_bv 64 (Z.of_nat (bn_top bx))); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax bx)));
                                    C4 (Z_to_bv 64 (Z.b2z (bn_neg bx))); C4 (Z_to_bv 64 (bn_flags bx))] ->
              rw_cells usegs mF ar [C8 (Z_to_bv 64 Dr); C4 (Z_to_bv 64 (Z.of_nat (bn_top br))); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax br)));
                                    C4 (Z_to_bv 64 (Z.b2z (bn_neg br))); C4 (Z_to_bv 64 (bn_flags br))] ->
              rw_cells usegs mF (bv_unsigned sp + -64) [CB 8 (take 8 (take 16 (take 24 (take 32 (take 40 (take 48 (take 56 junk)))))));
                                                       C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
              rw_cells usegs mF 3353076 [C4 errv2] -> stk usegs mF lo (bv_unsigned sp + -64) -> mem_inv usegs mF ->
              munch [(bv_unsigned sp + -64, bv_unsigned sp); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m2 mF -> wmono usegs m2 mF ->
              evt usegs
                (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA
                   (fun _ _ _ a0' => a0' = Z_to_bv 64 1)
                   (tt, setbn rr (mkBN (bn_d br) nb (bn_top bx + 1) (bn_neg bx) (bn_flags br)) ls1) st1)
                (MS (mkR (Z_to_bv 64 1044484) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 RATP) x5 x6 x7 sp (Z_to_bv 64 ar)
                         x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ax) (Z_to_bv 64 n) (Z_to_bv 64 0) (Z_to_bv 64 0)
                         s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                    F (Z_to_bv 64 0xff198) fc None mF (seg_rom usegs))).
    { intros mF nb x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Lnb LMnb UF BNxF BNrF FRF ERRF STF MIF MUF WMF.
      clear SEPrx XBI DrI RAI XAI BNx2 BNr FR2 ERR2 ST2 MI2 MU3 WM3 Ur.
      assert (LENnb : Z.of_nat (length (wlimbs nb)) = Z.of_nat (bn_dmax br)) by (rewrite wlimbs_len, Lnb; reflexivity).
      zstep. rewrite (bk_swrap32_small (n + 63)) by (clear - Hn; lia).
      zstep.
      zstep. if_cases KN; zify_cond KN. 2:{ exfalso. clear - KN Hn. lia. }
      chk ltac:(fun C => rewrite ?unsigned_lit in C by lia; lia).
      chk ltac:(fun C => clear - C; lia).
      step. rewrite (sx32_small (Z.of_nat (bn_top bx))) by lia.
      step. rewrite (sx32_small (Z.b2z (bn_neg bx))) by (destruct (bn_neg bx); cbn; lia).
      do 2 zstep.
      rewrite (bk_swrap32_small (Z.of_nat (bn_top bx) + 0)) by lia. rewrite ?Z.add_0_r.
      step.
      chk ltac:(fun C => clear - C; lia).
      do 2 zstep.
      rewrite (bk_swrap32_small (Z.of_nat (bn_top bx) + 0)) by lia. rewrite (bk_swrap32_small (Z.of_nat (bn_top bx) + 1)) by lia. rewrite ?Z.add_0_r.
      zstep. rewrite lts_signed by lia. if_cases KO; zify_cond KO. { exfalso. clear - KO. lia. } clear KO.
      step. zstep.
      do 7 step. release_frame FRF STF (bv_unsigned sp). step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mG end.
      apply evt_done.
      assert (HWL3 : Forall (w_lib OW2 lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
      { constructor; [left; cbn; lia|]. constructor; [right; exists (qr2, Ar2, nr2); cbn; auto|].
        constructor; [right; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn; split; [exact Hinpr| lia]| constructor]. }
      assert (WOK3 : Forall (w_ok OW2 LB ls1 AD EA [rr]) [(bv_unsigned sp + -64, bv_unsigned sp); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
      { constructor; [apply w_stack; cbn; lia|]. constructor; [eapply (w_struct OW2 LB ls1 AD EA false [rr] _ rr ar); [left; reflexivity| exact HAr2| cbn; lia| cbn; lia]|].
        constructor; [eapply (w_limbs OW2 LB ls1 AD EA false [rr] _ rr pr Dr); [left; reflexivity| exact HVr2| exact Edr| exact Hinpr| cbn [fst snd]; fold br; lia| cbn [fst snd]; fold br; lia]| constructor]. }
      unfold bn_post. do 15 eexists. exists mG, OW2, errv2. split; [reflexivity|]. cbn [fst snd].
      split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP2 MUF WMF HWL3 CEIL)|].
      split.
      { unfold lib_state. eapply (lib_state_close [] ls1 mG OW2 AD EA rr ar); [| exact ND2| exact HAr2| | |].
        - exact (lib_state_frame st1 LB [rr] ls1 m2 mG OW2 AD EA _ HEAP2 LSH MUF WMF WOK3).
        - exists Dr. split.
          + unfold bn_cells, bn_dmax. cbn [bn_top bn_buf bn_neg bn_flags]. rewrite Lnb.
            replace (Z.of_nat (bn_top bx + 1)) with (Z.of_nat (bn_top bx) + 1) by lia. exact BNrF.
          + unfold bn_arr, bn_dmax. cbn [bn_d bn_buf]. rewrite Edr, Lnb. split; [exact Hinpr| exact UF].
        - unfold bn_okm, bn_dmax. cbn [bn_buf bn_top bn_flags]. rewrite Lnb. unfold BN_WORDS_MAX.
          split; [exact LMnb|]. split; [exact HDM|]. split; [lia| exact OKq4].
        - apply ids_ok_setbn_same; [exact IDS2| exact HVr2|]. unfold bn_blocks, bn_dmax. cbn [bn_d bn_buf]. rewrite Lnb. reflexivity. }
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ HEAP2 AUX2 MUF WMF HWL3 SPB); unfold GLOBALS_TOP; lia|]. split; [exact STF|].
      split; [unfold LX_ERRNO, RATP; exact ERRF|]. split; [exact MIF|].
      split.
      { eapply lx_pres_trans; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL); unfold GLOBALS_TOP; lia|].
        eapply lx_pres_trans; [eapply lx_pres_weaken; [exact LXP2| lia| auto| auto]|].
        apply (seg_lx_pres _ _ _ _ _ _ _ _ _ HEAP2 MUF WMF HWL3 CEIL); unfold GLOBALS_TOP; lia. }
      split; [exact FA2|]. split; [exact SO2|].
      split. { intros r0 a0 H0. apply ref_at_setbn. apply RST2. exact H0. }
      reflexivity. }
    destruct (proj1 (limbarr_limbs_at usegs m2 Dr (bn_buf br)) Ur) as (LAr & WRr).
    assert (LBr : length (bn_buf br) = bn_dmax br) by reflexivity.
    zstep. if_cases KT; zify_cond KT.
    - (* [comment removed for export] *)
      assert (ETOP : bn_top bx = 0%nat) by (clear - KT; lia).
      replace (bn_top bx =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; exact ETOP).
      chk ltac:(fun C => rewrite ?unsigned_lit in C by lia; lia).
      chk ltac:(fun C => clear - C; lia).
      step. do 3 zstep.
      pose proof (block_ualign _ _ _ _ _ _ _ HEAP2 Hinpr) as (DR0 & DR8).
      replace (0 <? Dr) with true by (symmetry; apply Z.ltb_lt; exact DR0).
      replace (Dr <? 1) with false by (symmetry; apply Z.ltb_ge; clear - DR0; lia).
      cbn [Z.b2z].
      chk ltac:(fun C => clear - C; lia).
      do 4 zstep.
      rewrite (lxor_signbit63' n) by (clear - Hn; lia).
      replace (n + 9223372036854775808 <? 9223372036854775745) with false by (symmetry; apply Z.ltb_ge; clear - Hn; lia).
      replace (Dr <? 0) with false by (symmetry; apply Z.ltb_ge; clear - DR0; lia).
      cbn [Z.b2z Z.lxor].
      chk ltac:(fun C => clear - C; lia).
      chk ltac:(fun C => rewrite ?unsigned_lit in C by lia; lia).
      zstep. rewrite (land7 Dr) by exact DR8.
      chk ltac:(fun C => clear - C; lia).
      assert (SOKA : store_ok usegs m2 (Z_to_bv 64 Dr) 8 = true).
      { pose proof (wr_at_store_ok usegs m2 Dr (8 * Z.of_nat (length (bn_buf br))) 0 8 WRr ltac:(lia) ltac:(rewrite LBr; clear - HDM; lia)) as X.
        rewrite Z.add_0_r in X. exact X. }
      zstep. zstep.
      assert (UN : u64arr usegs (write_to_mem m2 (Z_to_bv 64 Dr) (le8 (Z_to_bv 64 0))) Dr (wlimbs (BnBase.upd (bn_buf br) 0 0))).
      { apply limbarr_limbs_at. split.
        - unfold BnBase.upd, splice. cbn [firstn app length Nat.add].
          apply (ulimbs_at_cons_write m2 Dr 0 (skipn 1 (bn_buf br))); [|exact Dr0].
          rewrite <- (firstn_skipn 1 (bn_buf br)) in LAr. apply limbs_at_app in LAr. destruct LAr as [_ LA2].
          rewrite length_firstn, LBr in LA2. replace (Nat.min 1 (bn_dmax br)) with 1%nat in LA2 by (clear - HDM; lia). exact LA2.
        - rewrite upd_length by (rewrite LBr; clear - HDM; lia). apply wr_at_write. exact WRr. }
      clear Ur LAr WRr.
      assert (L8 : length (le8 (Z_to_bv 64 0)) = 8%nat) by apply length_le8.
      assert (D8 : Dr + 8 <= Dr + 8 * Z.of_nat (bn_dmax br)) by (clear - HDM; lia).
      change (Z_to_bv 64 Dr) with (wa Dr) in *.
      apply (rw_cells_frame usegs m2 _ _ Dr (le8 (Z_to_bv 64 0))) in BNx2; [| exact Dr0 | rewrite L8; clear - DrC D8 CEIL LO SPR; lia | rewrite L8; cbn; clear - SEPrx D8; lia].
      apply (rw_cells_frame usegs m2 _ _ Dr (le8 (Z_to_bv 64 0))) in BNr; [| exact Dr0 | rewrite L8; clear - DrC D8 CEIL LO SPR; lia | rewrite L8; cbn; clear - SEPrr D8; lia].
      apply (rw_cells_frame usegs m2 _ _ Dr (le8 (Z_to_bv 64 0))) in FR2; [| exact Dr0 | rewrite L8; clear - DrC D8 CEIL LO SPR; lia | rewrite L8; cbn; clear - DrC D8 CEIL LO; lia].
      apply (rw_cells_frame usegs m2 _ _ Dr (le8 (Z_to_bv 64 0))) in ERR2; [| exact Dr0 | rewrite L8; clear - DrC D8 CEIL LO SPR; lia | rewrite L8; cbn; clear - DrI D8 HDM; lia].
      apply (stk_write usegs m2 _ _ Dr (le8 (Z_to_bv 64 0))) in ST2; [| exact Dr0 | rewrite L8; clear - DrC D8 CEIL LO SPR; lia].
      apply (mem_inv_store usegs m2 (wa Dr) (le8 (Z_to_bv 64 0))) in MI2; [| rewrite L8; exact SOKA].
      apply (munch_write _ m2 m2 Dr (le8 (Z_to_bv 64 0))) in MU3; [| exact Dr0 | rewrite L8; clear - DrC D8 CEIL LO SPR; lia | rewrite L8; cbn [inside]; clear - D8; lia].
      apply (wmono_write usegs m2 m2 (wa Dr) (le8 (Z_to_bv 64 0))) in WM3.
      eapply FIN; try eassumption.
      + rewrite upd_length by (rewrite LBr; clear - HDM; lia). exact LBr.
      + apply upd_limbs; [exact OKq1 | exact limb_0].
    - (* [comment removed for export] *)
      assert (NTOP : bn_top bx <> 0%nat) by (clear - KT; lia).
      replace (bn_top bx =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; exact NTOP).
      (* [comment removed for export] *)
      destruct (bn_arr_facts st1 OW2 LB m2 HEAP2 ls1 AD EA IDS2 ADB2 rx Dx2 HVx2 ltac:(rewrite Ebx; exact ARRx2)) as (Ux & LENx & Dx0 & DxC & DxI & _).
      rewrite Ebx in Ux, LENx, DxC, DxI.
      assert (HDx : exists px, bn_d bx = Some px /\ In (px, Dx2, 8 * Z.of_nat (bn_dmax bx)) OW2).
      { unfold bn_arr in ARRx2. destruct (bn_d bx) as [px|]; [exists px; split; [reflexivity| exact (proj1 ARRx2)]|].
        exfalso. destruct ARRx2 as [_ E]. unfold bn_dmax in OKx2. rewrite E in OKx2. cbn in OKx2. lia. }
      destruct HDx as (px & Edx & Hinpx).
      pose proof (RH_range _ _ _ _ _ _ _ HEAP2 Hinpx) as (PX0 & PX16 & _ & _ & _).
      pose proof (limbs_limbs_disj st1 OW2 LB m2 HEAP2 ls1 AD EA IDS2 rx rr px Dx2 _ pr Dr _ ltac:(congruence) HVx2 HVr2
                    ltac:(rewrite Ebx; exact Edx) Edr Hinpx Hinpr) as LDJ.
      destruct (proj1 (limbarr_limbs_at usegs m2 Dx2 (bn_buf bx)) Ux) as (LAx & _).
      set (f := firstn (bn_top bx) (bn_buf bx)).
      assert (Lf : length f = bn_top bx) by (subst f; apply firstn_length_le; exact OKx2).
      assert (LAf : limbs_at usegs m2 Dx2 f).
      { rewrite <- (firstn_skipn (bn_top bx) (bn_buf bx)) in LAx. apply limbs_at_app in LAx. exact (proj1 LAx). }
      assert (LArest : limbs_at usegs m2 (Dr + 8 * Z.of_nat (bn_top bx + 1)) (skipn (bn_top bx + 1) (bn_buf br))).
      { rewrite <- (firstn_skipn (bn_top bx + 1) (bn_buf br)) in LAr. apply limbs_at_app in LAr. destruct LAr as [_ LA2].
        rewrite length_firstn, LBr in LA2. replace (Nat.min (bn_top bx + 1) (bn_dmax br)) with (bn_top bx + 1)%nat in LA2 by (clear - HDM; lia). exact LA2. }
      pose proof (block_ualign _ _ _ _ _ _ _ HEAP2 Hinpr) as (DR0 & DR8).
      pose proof (block_ualign _ _ _ _ _ _ _ HEAP2 Hinpx) as (DX0 & DX8).
      repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
      chk ltac:(fun C => rewrite ?unsigned_lit in C by lia; lia).
      chk ltac:(fun C => clear - C; lia).
      step. do 3 zstep.
      replace (0 <? Dr) with true by (symmetry; apply Z.ltb_lt; exact DR0).
      replace (Dr <? 1) with false by (symmetry; apply Z.ltb_ge; clear - DR0; lia).
      cbn [Z.b2z].
      chk ltac:(fun C => clear - C; lia).
      do 4 zstep.
      rewrite (lxor_signbit63' n) by (clear - Hn; lia).
      replace (n + 9223372036854775808 <? 9223372036854775745) with false by (symmetry; apply Z.ltb_ge; clear - Hn; lia).
      replace (Dr <? 0) with false by (symmetry; apply Z.ltb_ge; clear - DR0; lia).
      cbn [Z.b2z Z.lxor].
      chk ltac:(fun C => clear - C; lia).
      zstep.
      rewrite (bk_swrap32_small (Z.of_nat (bn_top bx) + -1)) by lia.
      zstep. rewrite lts_signed by lia. if_cases KO; zify_cond KO. { exfalso. clear - KO. lia. } clear KO.
      step. do 2 zstep.
      replace (Dx2 + (Z.of_nat (bn_top bx) + -1) ≪ 3) with (Dx2 + 8 * (Z.of_nat (bn_top bx) - 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      do 2 zstep.
      rewrite ?land64_small by lia.
      replace (0 <? Dx2) with true by (symmetry; apply Z.ltb_lt; exact DX0).
      replace (Dx2 + 8 * (Z.of_nat (bn_top bx) - 1) <? 1) with false by (symmetry; apply Z.ltb_ge; clear - DX0 NTOP; lia).
      cbn [Z.b2z].
      chk ltac:(fun C => clear - C; lia).
      do 4 zstep.
      rewrite (lxor_signbit63' (Z.of_nat (bn_top bx) + -1)) by (clear - NTOP OKx2 OKx3; lia).
      replace (Z.of_nat (bn_top bx) + -1 + 9223372036854775808 <? 9223372036854775808) with false by (symmetry; apply Z.ltb_ge; clear - NTOP; lia).
      replace (Dx2 + 8 * (Z.of_nat (bn_top bx) - 1) <? Dx2) with false by (symmetry; apply Z.ltb_ge; clear - NTOP; lia).
      cbn [Z.b2z Z.lxor].
      chk ltac:(fun C => clear - C; lia).
      chk ltac:(fun C => rewrite ?unsigned_lit in C by lia; lia).
      zstep. rewrite (land7 (Dx2 + 8 * (Z.of_nat (bn_top bx) - 1))) by (clear - DX8; Z.div_mod_to_equations; lia).
      chk ltac:(fun C => clear - C; lia).
      do 2 zstep.
      replace (Dr + Z.of_nat (bn_top bx) ≪ 3) with (Dr + 8 * Z.of_nat (bn_top bx)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      zstep. rewrite ?land64_small by lia.
      replace (Dr + 8 * Z.of_nat (bn_top bx) <? 1) with false by (symmetry; apply Z.ltb_ge; clear - DR0; lia).
      cbn [Z.b2z].
      chk ltac:(fun C => clear - C; lia).
      do 4 zstep.
      rewrite (lxor_signbit63' (Z.of_nat (bn_top bx))) by (clear - OKx2 OKx3; lia).
      replace (Z.of_nat (bn_top bx) + 9223372036854775808 <? 9223372036854775808) with false by (symmetry; apply Z.ltb_ge; clear; lia).
      replace (Dr + 8 * Z.of_nat (bn_top bx) <? Dr) with false by (symmetry; apply Z.ltb_ge; clear; lia).
      cbn [Z.b2z Z.lxor].
      chk ltac:(fun C => clear - C; lia).
      zstep. rewrite (land7 (Dr + 8 * Z.of_nat (bn_top bx))) by (clear - DR8; Z.div_mod_to_equations; lia).
      chk ltac:(fun C => clear - C; lia).
      replace (Z.of_nat (bn_top bx) + -1) with (Z.of_nat (bn_top bx) - 1) by (clear; lia).
      replace (Z.of_nat (bn_top bx)) with (Z.of_nat (length f)) by (rewrite Lf; reflexivity).
      repeat match goal with H : hide _ |- _ => apply hide_elim in H end.
      eapply (ulsh_block _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 f Dx2 Dr n).
      { exact Hn. }
      { subst f. apply limbs_firstn. exact OKx1. }
      { rewrite Lf. clear - NTOP OKx2 OKx3. lia. }
      { clear - PX0 PX16. Z.div_mod_to_equations. lia. }
      { clear - DR0 DR8 DX8. auto. }
      { rewrite Lf. clear - LDJ OKx2 HDM. lia. }
      { exact LAf. }
      { rewrite Lf. apply (wr_at_sub usegs m2 Dr (8 * Z.of_nat (length (bn_buf br))) 0 (8 * (Z.of_nat (bn_top bx) + 1))) in WRr; [rewrite Z.add_0_r in WRr; exact WRr | clear; lia | clear; lia | rewrite LBr; clear - HDM; lia]. }
      { exact MI2. }
      intros m3 z5 z6 z7 z12 z13 z16 z17 z28 z29 z30 z31 HR HFx MI3 MUb WMb.
      rewrite Lf in HR, MUb.
      (* [comment removed for export] *)
      assert (DJW : forall A k, (A + k <= Dr \/ Dr + 8 * Z.of_nat (bn_dmax br) <= A) ->
                disjoint_from [(Dr, Dr + 8 * (Z.of_nat (bn_top bx) + 1))] A k).
      { intros A k H. cbn [disjoint_from]. split; [|exact I]. clear - H HDM. lia. }
      eapply (rw_cells_transport usegs _ m2 m3) in BNx2; [| exact MUb | exact WMb | apply DJW; cbn; clear - SEPrx; lia].
      eapply (rw_cells_transport usegs _ m2 m3) in BNr; [| exact MUb | exact WMb | apply DJW; cbn; clear - SEPrr; lia].
      eapply (rw_cells_transport usegs _ m2 m3) in FR2; [| exact MUb | exact WMb | apply DJW; cbn; clear - DrC CEIL LO; lia].
      eapply (rw_cells_transport usegs _ m2 m3) in ERR2; [| exact MUb | exact WMb | apply DJW; cbn; clear - DrI HDM; lia].
      eapply (stk_transport_disjoint usegs _ m2 m3) in ST2; [| exact MUb | exact WMb | apply DJW; clear - DrC CEIL LO; lia].
      assert (MU4 : munch [(bv_unsigned sp + -64, bv_unsigned sp); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m2 m3).
      { eapply munch_weaken; [|exact MUb]. unfold sub_fp. intros x Hx. cbn [outside] in *. split; [|exact I]. clear - Hx HDM. lia. }
      assert (LArest3 : limbs_at usegs m3 (Dr + 8 * Z.of_nat (bn_top bx + 1)) (skipn (bn_top bx + 1) (bn_buf br))).
      { eapply limbs_at_transport; [exact LArest | exact MUb |]. cbn [disjoint_from]. split; [|exact I]. rewrite length_skipn, LBr. clear - HDM. lia. }
      clear MU3 WM3.
      pose proof (lshift_limbs_seq f n) as ESEQ.
      destruct (lshift_limbs f n 0) as [ls0 mo] eqn:ELS. cbn [fst snd] in ESEQ.
      assert (Lnew : length (ls0 ++ [mo]) = (bn_top bx + 1)%nat) by (rewrite ESEQ, length_map, length_seq, Lf; lia).
      rewrite ?Lf.
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
End Proofs.
End WithCeiling0.
