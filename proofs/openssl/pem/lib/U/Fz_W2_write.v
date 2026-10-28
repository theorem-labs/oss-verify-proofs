(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy.
     From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_M_free Fz_M_secure Fz_M_clear_free Fz_M_clear_realloc Fz_W1_defs Fz_W1_sync Fz_W1_growc Fz_W1_grows Fz_W1_writec Fz_W1_read Fz_W3_iface Fz_W2_rep Fz_W2_read Fz_W2_puts.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation wz := (Z_to_bv 64) (only parsing).
Definition hideP (X : Prop) : Prop := X.
Ltac hide H := lazymatch type of H with ?X => change X with (hideP X) in H end.
Ltac trw H MUc WMc := eapply rw_cells_transport in H; [| exact MUc| exact WMc| cbn [length disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]].

(* [comment removed for export] *)
Lemma meth_bwrite : forall m meth, cimg m -> mem_inv usegs m -> (meth = M_MEM \/ meth = M_SECMEM) ->
  rw_cells usegs m (meth + 16) [C8 (wz 0x10cca0)] /\ rw_cells usegs m (meth + 24) [C8 (wz 0x1832b0)].
Proof.
  intros m meth CIMG MI [-> | ->]; unfold M_MEM, M_SECMEM.
  - cimg_cell CIMG m (0x2d3fc8 + 16) [C8 (wz 0x10cca0)] H1. cimg_cell CIMG m (0x2d3fc8 + 24) [C8 (wz 0x1832b0)] H2. split; [exact H1| exact H2].
  - cimg_cell CIMG m (0x2d4038 + 16) [C8 (wz 0x10cca0)] H1. cimg_cell CIMG m (0x2d4038 + 24) [C8 (wz 0x1832b0)] H2. split; [exact H1| exact H2].
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem bio_write0_proof : bio_write0_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB0 L f n lo Bd CST SLO -> HN.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO). unfold FZ_BIO_WRITE, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
  cprefix. ths. if_cases K0; zify_cond K0.
  2: { exfalso. clear - K1 K2 HN. change 18446744073709551615 with (Z.ones 64) in K1, K2. rewrite Z.land_ones in K1, K2 by (clear; lia).
       destruct (Z.eq_dec n 0) as [->|NZ]; [cbn in K1; lia|].
       rewrite <- (Zmod_unique n (2 ^ 64) (-1) (n + 2 ^ 64)) in K2 by lia. lia. }
  clear K0. ths. ths. chere. apply climpl_done.
  exists (wz 0), m, LBall. split; [unfold cret; do 14 eexists; reflexivity|]. split; [clear; lia|]. split; [clear; unfold cgrow; lia|].
  split; [exact CST|]. split; [apply cframe_refl|]. split; [reflexivity|]. split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem bio_write_spec : crypto_clear_realloc_null_stmt -> crypto_clear_realloc_grow_stmt -> crypto_secure_malloc_stmt -> crypto_secure_clear_free_stmt -> bio_write_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros GA GB GC GD ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB0 L f K BI meth len max IN n lo Bd src
         Hf ROOM CST SLO MB HLIM HN SRC LSRC SLOC SP16 -> -> ->.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO). unfold BWRITE_STACK, FZ_BIO_WRITE, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (WSP : 160 <= WRITE_STACK) by (unfold WRITE_STACK, GROW_STACK, CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear; lia).
  pose proof MB as [BM (BB & RP & fl & rrw & padw & nr & nw & OWNB & NDK & METH & HEAD & W1C & FLOK & TAIL & INNER)].
  pose proof INNER as (rmaxw & _ & _ & _ & _ & OFF & LENM & MAX31 & _). clear INNER TAIL.
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNB)) as (BI0 & BI16 & _ & BIC & BIIMG). hide BIIMG.
  assert (BI8 : BI mod 8 = 0) by (clear - BI16; Z.div_mod_to_equations; lia).
  assert (BIW : BI < 2 ^ 63) by (clear - BIC CEIL_RANGE__; unfold ceil_window in *; lia).
  unfold M_MEM, M_SECMEM in METH. pose proof (meth_bwrite m meth CIMG MI ltac:(unfold M_MEM, M_SECMEM; exact METH)) as [MBW MBWO].
  assert (METH8 : meth mod 8 = 0) by (clear - METH; destruct METH as [-> | ->]; reflexivity).
  assert (P24 : (bv_unsigned sp + -24) mod 8 = 0) by (clear - SP16; Z.div_mod_to_equations; lia).
  assert (P88 : (bv_unsigned sp + -88) mod 8 = 0) by (clear - SP16; Z.div_mod_to_equations; lia).
  unfold bio_head in HEAD. unfold bio_w1_cells in W1C.
  change ([C8 (wz 4294967297); C4 (wz fl); C4 rrw; C4 (wz 4294967295); C4 padw; C8 (wz BB)]) with ([C8 (wz 4294967297)] ++ [C4 (wz fl); C4 rrw; C4 (wz 4294967295); C4 padw; C8 (wz BB)]) in W1C.
  apply (proj1 (rw_cells_app usegs m _ _ _)) in W1C. destruct W1C as [ISW _].
  change 4294967297 with (1 + 2 ^ 32 * 1) in ISW. apply (proj2 (t_cells_halves usegs m (BI + 40) 1 1 ltac:(lia) ltac:(lia))) in ISW.
  assert (FPD : forall b, In b LBall -> mbio_T K (blk_id b) -> disjoint_from [(bv_unsigned sp - 128, bv_unsigned sp)]%Z (blk_addr b) (blk_size b)).
  { intros [[bp bA] bn] IN0 _. pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST IN0) as (_ & _ & _ & RC & _). unfold blk_addr, blk_size. cbn [fst snd disjoint_from]. clear - RC LO SLO WSP. lia. }
  (* [comment removed for export] *)
  assert (INA : 0 < IN /\ (IN + n <= lo \/ bv_unsigned sp <= IN)).
  { destruct SLOC as [SL|(ps & AS & ns & INS & NTS & S1 & S2)]; [clear - SL SPR LO SLO WSP GLO; lia|].
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INS) as (S0 & _ & _ & SCe & _). clear - S0 SCe S1 S2 LO HN. lia. }
  destruct INA as [IN0 INA].
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  cprefix. ths. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. clear - K0 HN. lia. } try clear K0; try clear K1; try clear K2.
  ths. th_frame 32%nat [8; 8; 8; 8]%nat ST. ths. ths. ths. ths. ths.
  (* [comment removed for export] *)
  lazymatch goal with H : stk usegs _ lo _ |- _ => rename H into ST1 end.
  ths. th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat ST1. do 6 ths. ths. ths. ths. ths. ths.
  ths. if_cases J1; zify_cond J1. { exfalso. rewrite ?unsigned_lit in J1 by lia. clear - J1 SPR SLO WSP LO GLO; lia. } clear J1.
  ths. ths. ubs_if.
  ths.
  ths. if_cases J2; zify_cond J2. { exfalso. rewrite ?unsigned_lit in J2 by lia. clear - J2 BI0 BIC LO CEIL_RANGE__; unfold ceil_window in *; lia. } clear J2.
  ths. ths. ubs_if.
  ths. ths. if_cases J3; zify_cond J3. { exfalso. rewrite ?unsigned_lit in J3 by lia. clear - J3 METH; lia. } clear J3.
  ths. ths. ubs_if.
  ths. ths. th_if_lit. ths. ths. th_if_lit. ths. ths. th_if_lit. ths. ths. th_if_lit.
  ths. ths. ubs_if. ths. ths. ubs_if. ths. ths. ths. ths. ths. ths.
  (* [comment removed for export] *)
  lazymatch goal with H : stk usegs _ lo _ |- _ => rename H into ST2 end.
  ths. th_frame 32%nat [8; 8; 8; 8]%nat ST2. ths. ths. ths. ths. ths. ths. ths.
  ths. if_cases J4; zify_cond J4. 2: { exfalso. rewrite ?unsigned_lit in J4 by lia. clear - J4 HN HLIM OFF LENM; lia. } clear J4.
  ths. ubs_if. ths. ths. ubs_if. ths. ths. ubs_if. ths. ths. ubs_if. ths. ths.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mc0 end.
  lazymatch goal with H : stk usegs mc0 lo _ |- _ => rename H into STc end. lazymatch goal with H : mem_inv usegs mc0 |- _ => rename H into MIc end.
  lazymatch goal with H : munch _ m mc0 |- _ => rename H into MUq end. lazymatch goal with H : wmono usegs m mc0 |- _ => rename H into WMq end.
  lazymatch goal with H : rw_cells usegs mc0 (bv_unsigned sp + -32) _ |- _ => rename H into FRa end.
  lazymatch goal with H : rw_cells usegs mc0 (bv_unsigned sp + -96) _ |- _ => rename H into FRb end.
  lazymatch goal with H : rw_cells usegs mc0 (bv_unsigned sp + -128) _ |- _ => rename H into FRc end.
  assert (CSTc : cstate s LBall LB0 L mc0 (wz (bv_unsigned sp + -128)) tp lo Bd).
  { eapply (cstate_seg _ s LBall LB0 L m mc0 sp _ tp lo Bd (bv_unsigned sp)); [exact CST| exact MUq| exact WMq| exact MIc| | clear - SLO SPR WSP LO; lia| exact SPB| | |].
    - apply Forall_cons; [apply cwin_stack; clear - SLO SPR WSP; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. clear - SLO SPR GLO WSP. lia.
    - rewrite unsigned_lit by lia. exact STc.
    - rewrite unsigned_lit by lia. clear - SPB; lia. }
  assert (FR0 : cframe (mbio_T K) [] (bv_unsigned sp) s LBall L m s LBall L mc0).
  { eapply cframe_seg; [apply cframe_refl| exact MUq| exact WMq| exact HP| clear - SLO SPR LO WSP; lia|]. apply Forall_cons; [apply cseg_ok_stack; clear - SLO SPR LO WSP; lia| apply Forall_nil]. }
  chere. eapply climpl_seq.
  { eapply (mem_write_specM GA GB GC GD) with (K := K) (BI := BI) (meth := meth) (len := len) (max := max) (IN := IN) (n := n) (src := src);
      [exact Hf| exact ROOM| exact CSTc| rewrite unsigned_lit by lia; unfold MW_STACK; clear - SLO WSP; lia
      | exact (mbio_rep_agree _ _ _ _ _ _ _ _ _ _ MB (munch_mbio_fp _ _ _ _ _ _ _ _ _ _ _ K CST MUq WMq FPD))| exact HLIM| clear - HN; lia| exact IN0| exact SRC| exact LSRC
      | rewrite unsigned_lit by lia; eapply src_loc_weakT; [| intros q X; exact X]; destruct SLOC as [SL|SB]; [left; clear - SL; lia| right; exact SB]
      | reflexivity| reflexivity| reflexivity]. }
  cbv beta. intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU1 & GR1' & CST1 & FRM1 & R1).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->). cret_lit. rewrite unsigned_lit in FRM1 by lia.
  destruct R1 as (pd' & max' & -> & HMAX & HFIT & MB1 & KB & KL & NB & NL & PLS).
  pose proof FRM1 as (CFR1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRa ltac:(clear; lia)) as FR1. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRb ltac:(clear; lia)) as FR2.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRc ltac:(clear; lia)) as FR3. clear FRa FRb FRc.
  pose proof MB1 as [BM1 (BB1 & RP1 & fl1 & rrw1 & padw1 & nr1 & nw1 & OWNB1 & NDK1 & _ & HEAD1 & W1C1 & FLOK1 & TAIL1 & INNER1)]. unfold bio_head in HEAD1. unfold bio_tail in TAIL1.
  cbn [k_bi k_bb k_bm k_rp k_d mbk_data] in OWNB1, INNER1, NDK1.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1' & _ & _ & MI1 & _) & _). rewrite unsigned_lit in ST1' by lia.
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST1 (proj1 OWNB1)) as (_ & _ & _ & BIC1 & BIIMG1). hide BIIMG1.
  assert (INB1 : In (k_bi K, BI, 128) LB1) by exact (proj1 OWNB1).
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (BI + 104, BI + 112)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  assert (FIN : forall m2 (nwX : word) (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
    stk usegs m2 lo (bv_unsigned sp) -> mem_inv usegs m2 -> munch [(bv_unsigned sp - 128, bv_unsigned sp); (BI + 104, BI + 112)]%Z m1 m2 -> wmono usegs m1 m2 ->
    rw_cells usegs m2 (BI + 72) [C8 (wz 0); C8 (wz 0); C4 (wz 1); C4 (wz 0); C8 nr1; C8 nwX; C8 (wz 0); C8 (wz 0)] ->
    cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB0 L f m lo Bd (mbio_T K) [] 2 (wA (grow_n (len + n))) (wB (grow_n (len + n))) (wBig (grow_n (len + n)))
      (bio_puts_res K BI meth len max n LBall L) f1 L1 st1
      (MS (mkR ra sp gp tp y5 y6 y7 s0 s1 (wz n) y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31) F (ret_pc ra) fc None m2 (seg_rom usegs))).
  { intros m2 nwX y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 ST2' MI2 MU12 WM12 TAIL2.
    exists (wz n), m2, LB1. split; [unfold cret; do 14 eexists; reflexivity|]. split; [exact FU1|]. split; [exact GR1'|].
    split. { eapply (cstate_seg _ st1 LB1 LB0 L1 m1 m2 _ sp tp lo Bd (bv_unsigned sp)); [exact CST1| exact MU12| exact WM12| exact MI2| | clear - SLO SPR WSP; lia| exact SPB| | exact ST2'| exact SPB].
      - apply Forall_cons; [apply cwin_stack; clear - SLO SPR WSP; lia|].
        apply Forall_cons; [apply (cwin_block _ _ _ (k_bi K, BI, 128)); [exact INB1| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia| apply Forall_nil].
      - cbn [disjoint_from]. unfold LX_FLAGS. unfold hideP in BIIMG1. clear - SLO SPR GLO WSP BIIMG1. lia. }
    split. { eapply cframe_seg; [eapply cframe_call; [exact FR0| exact FRM1| clear; lia| intros a X; exact X| intros q _ NT; exact NT]| exact MU12| exact WM12| exact HP1| clear - SLO SPR LO WSP; lia|].
      apply Forall_cons; [apply cseg_ok_stack; clear - SLO SPR LO WSP; lia|].
      apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (k_bi K, BI, 128)); [exact INB1| intros b0 _ NT E; apply NT; rewrite E; unfold mbio_T; cbn [blk_id fst]; left; reflexivity| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia| apply Forall_nil]. }
    exists pd', max'. split; [reflexivity|]. split; [exact HMAX|]. split; [exact HFIT|]. split; [| split; [exact KB| split; [exact KL| split; [exact NB| split; [exact NL| exact PLS]]]]].
    destruct INNER1 as (rmaxw1 & OWNbb1 & BBC1 & OWNbm1 & OWNrp1 & OFF1 & LENM1 & MAX1 & DOPT1).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST1 (proj1 OWNbb1)) as (_ & _ & _ & BBC1e & _).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST1 (proj1 OWNbm1)) as (_ & _ & _ & BMC1e & _).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST1 (proj1 OWNrp1)) as (_ & _ & _ & RPC1e & _).
    pose proof NDK1 as NDK1'. unfold mbio_blocks in NDK1; cbn [k_bi k_bb k_bm k_rp k_d mbk_data] in NDK1.
    assert (ND3 : k_bi K <> k_bb K /\ k_bi K <> k_bm K /\ k_bi K <> k_rp K).
    { clear - NDK1. apply List.NoDup_app_remove_r in NDK1. inversion NDK1 as [|x1 l1 N1 ND1]; subst. cbn [In] in N1. repeat split; intros E; rewrite E in *; tauto. }
    destruct ND3 as (M12 & M13 & M14).
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 (proj1 OWNB1) (proj1 OWNbb1) M12) as C12.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 (proj1 OWNB1) (proj1 OWNbm1) M13) as C13.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 (proj1 OWNB1) (proj1 OWNrp1) M14) as C14.
    exists BM1, BB1, RP1, fl1, rrw1, padw1, nr1, nwX. split; [exact OWNB1|]. split; [exact NDK1'|]. split; [unfold M_MEM, M_SECMEM; exact METH|].
    trw HEAD1 MU12 WM12. 2: { clear - SPR BIC1 LO SLO WSP; lia. } split; [exact HEAD1|].
    trw W1C1 MU12 WM12. 2: { unfold bio_w1_cells. cbn [length cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SPR BIC1 LO SLO WSP; lia. } split; [exact W1C1|].
    split; [exact FLOK1|]. split; [exact TAIL2|].
    exists rmaxw1. split; [exact OWNbb1|]. trw BBC1 MU12 WM12. 2: { clear - SPR BBC1e LO SLO WSP C12; lia. } split; [exact BBC1|].
    split; [exact OWNbm1|]. split; [exact OWNrp1|]. split; [exact OFF1|]. split; [exact LENM1|]. split; [exact MAX1|].
    destruct pd' as [pd1|]; cbn [k_d mbk_data] in DOPT1; cbn [k_d mbk_data].
    - destruct DOPT1 as (D1 & nm1 & jk1 & OWNd1 & MAXP1 & BMC2 & RPC2 & LJ1 & DC1). exists D1, nm1, jk1. split; [exact OWNd1|]. split; [exact MAXP1|].
      pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST1 (proj1 OWNd1)) as (_ & _ & _ & DC1e & _).
      assert (M15 : k_bi K <> pd1). { clear - NDK1. intros E. rewrite E in NDK1. cbn [app] in NDK1. inversion NDK1 as [|x1 l1 N1 ND1]; subst. apply N1. cbn [In]. tauto. }
      pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 (proj1 OWNB1) (proj1 OWNd1) M15) as C15.
      trw BMC2 MU12 WM12. 2: { clear - SPR BMC1e LO SLO WSP C13; lia. } split; [exact BMC2|].
      unfold readp_cells in RPC2. trw RPC2 MU12 WM12. 2: { clear - SPR RPC1e LO SLO WSP C14; lia. } split; [exact RPC2|]. split; [exact LJ1|].
      trw DC1 MU12 WM12. 2: { clear - SPR DC1e LO SLO WSP C15 MAXP1; rewrite ?Z2Nat.id by lia; lia. } exact DC1.
    - destruct DOPT1 as (MAX0 & BMC2 & RPC2). split; [exact MAX0|].
      trw BMC2 MU12 WM12. 2: { clear - SPR BMC1e LO SLO WSP C13; lia. } split; [exact BMC2|].
      unfold readp_cells in RPC2. trw RPC2 MU12 WM12. 2: { clear - SPR RPC1e LO SLO WSP C14; lia. } exact RPC2. }
  clear INNER1.
  assert (NR : 0 < n < 2 ^ 31) by (clear - HN; lia).
  (* [comment removed for export] *)
  cprefix. ths. ths. ths. ths.
  ths. if_cases J5; zify_cond J5. all: try (exfalso; rewrite ?unsigned_lit in J5 by lia; clear - J5 NR; lia). all: try clear J5.
  ths. if_cases JW; zify_cond JW.
  { exfalso. rewrite (ubs_land7 (bv_unsigned sp + -88)), (proj2 (Z.ltb_lt 0 (bv_unsigned sp + -88))) in JW by lia. cbv in JW. discriminate JW. }
  ths. ths. ths. ths. ths. ths. ths. ths. th_release FR3 (bv_unsigned sp - 96). ths.
  (* [comment removed for export] *)
  ths. ths. th_if_lit. ths. ths. ths. ths. ths. ths. th_if_lit. ths. ths. th_if_lit.
  ths. if_cases J6; zify_cond J6. all: try (exfalso; rewrite ?unsigned_lit in J6 by lia; clear - J6 SPR SLO WSP LO GLO; lia). all: try clear J6.
  ths. ths. ubs_if.
  ths. ths. ths. ths. do 6 ths. ths. th_release FR2 (bv_unsigned sp - 32). ths.
  (* [comment removed for export] *)
  ths. th_if_lit.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mf end.
  lazymatch type of FR1 with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3] => change [c0; c1; c2; c3] with ([c0] ++ [c1] ++ [c2; c3]) in FR1 end.
  apply (proj1 (rw_cells_app usegs mf _ _ _)) in FR1. destruct FR1 as [FR1a FR1]. apply (proj1 (rw_cells_app usegs mf _ _ _)) in FR1. destruct FR1 as [PPz FR1c].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app] in PPz, FR1c.
  replace (bv_unsigned sp + -32 + 8) with (bv_unsigned sp + -24) in PPz by (clear; lia). replace (bv_unsigned sp + -32 + 8 + 8) with (bv_unsigned sp + -16) in FR1c by (clear; lia).
  replace n with (n + 2 ^ 32 * 0) in PPz by (clear; lia). apply (proj2 (t_cells_halves usegs _ (bv_unsigned sp + -24) n 0 ltac:(clear - NR; lia) ltac:(clear; lia))) in PPz.
  ths. rewrite (t_sx32_small n) by (clear - NR; lia). ths. ths. ths.
  assert (FRm : rw_cells usegs mf (bv_unsigned sp + -24) ([C4 (wz n); C4 (wz 0)] ++ [C8 s0; C8 ra])).
  { apply (proj2 (rw_cells_app usegs mf _ _ _)). split; [exact PPz|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
    replace (bv_unsigned sp + -24 + 8) with (bv_unsigned sp + -16) by (clear; lia). exact FR1c. }
  lazymatch type of FR1a with rw_cells _ _ _ [?c0] =>
    assert (FRj : rw_cells usegs mf (bv_unsigned sp + -32) ([c0] ++ [C4 (wz n); C4 (wz 0); C8 s0; C8 ra]))
      by (apply (proj2 (rw_cells_app usegs mf _ _ _)); split; [exact FR1a|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
          replace (bv_unsigned sp + -32 + 8) with (bv_unsigned sp + -24) by (clear; lia); cbn [app] in FRm; exact FRm) end.
  cbn [app] in FRj. clear FR1a PPz FR1c FRm. th_release FRj (bv_unsigned sp). ths.
  chere. apply climpl_done. eapply FIN; [assumption| assumption| eassumption| eassumption| eassumption].
Qed.
End WithCeiling0.
