(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy.
     From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_W1_defs Fz_W1_sync Fz_W1_bits Fz_W1_write Fz_W1_read Fz_W1_ctrl Fz_W1_misc Fz_W3_iface Fz_W2_rep.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Notation wz := (Z_to_bv 64) (only parsing).
Definition hideP (X : Prop) : Prop := X.
Ltac hide H := lazymatch type of H with ?X => change X with (hideP X) in H end.

(* [comment removed for export] *)
Lemma meth_ctrl : forall m meth, cimg m -> mem_inv usegs m -> (meth = M_MEM \/ meth = M_SECMEM) -> rw_cells usegs m (meth + 64) [C8 (wz 0x183744)].
Proof.
  intros m meth CIMG MI [-> | ->]; unfold M_MEM, M_SECMEM.
  - cimg_cell CIMG m (0x2d3fc8 + 64) [C8 (wz 0x183744)] H. exact H.
  - cimg_cell CIMG m (0x2d4038 + 64) [C8 (wz 0x183744)] H. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem bio_ctrl_info_proof : bio_ctrl_info_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB0 L f K BI meth len max off lo Bd
         CST SLO MB -> -> -> ->.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  unfold BCTRL_STACK, FZ_BIO_CTRL, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  pose proof MB as [BMx (BBx & RPx & flx & rrwx & padwx & nrx & nwx & OWNB & NDK & METH & _)].
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNB)) as (BI0 & BI16 & _ & BIC & BIIMG). hide BIIMG.
  assert (BI8 : BI mod 8 = 0) by (clear - BI16; Z.div_mod_to_equations; lia).
  unfold M_MEM, M_SECMEM in METH.
  pose proof (meth_ctrl m meth CIMG MI ltac:(unfold M_MEM, M_SECMEM; exact METH)) as MCTRL.
  assert (METH8 : meth mod 8 = 0) by (clear - METH; destruct METH as [-> | ->]; reflexivity).
  (* [comment removed for export] *)
  assert (FPD : forall b, In b LBall -> mbio_T K (blk_id b) -> disjoint_from [(bv_unsigned sp - 144, bv_unsigned sp)]%Z (blk_addr b) (blk_size b)).
  { intros [[bp bA] bn] IN _. pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST IN) as (_ & _ & _ & RC & _).
    unfold blk_addr, blk_size. cbn [fst snd disjoint_from]. clear - RC LO SLO SPR. lia. }
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  pose proof MB as [BM0 (BB0 & RP0 & fl0 & rrw0 & padw0 & nr0 & nw0 & _ & _ & _ & HEAD & _)]. unfold bio_head in HEAD.
  cprefix. step. th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST. do 6 step. step.
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
  step. step. step. ubs_if.
  step. step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
  step. step. step. ubs_if.
  step. step. th_if_lit. step. step. step. step. th_if_lit. step. step. th_if_lit.
  step. ubs_if. step. step. ubs_if.
  step. step. step. step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mc0 end.
  lazymatch goal with H : stk usegs mc0 lo _ |- _ => rename H into STc end. lazymatch goal with H : mem_inv usegs mc0 |- _ => rename H into MIc end.
  lazymatch goal with H : munch _ m mc0 |- _ => rename H into MUq end. lazymatch goal with H : wmono usegs m mc0 |- _ => rename H into WMq end.
  lazymatch goal with H : rw_cells usegs mc0 (bv_unsigned sp + -48) _ |- _ => rename H into FRc end.
  (* [comment removed for export] *)
  pose proof (mbio_rep_agree _ _ _ _ _ _ _ _ _ _ MB (munch_mbio_fp _ _ _ _ _ _ _ _ _ _ _ K CST MUq WMq FPD)) as MBc.
  destruct MBc as [BMc (BBc & RPc & flc & rrwc & padwc & nrc & nwc & _ & _ & _ & HEADc & W1Cc & FLOKc & TAILc & (rmaxw & OWNbb & BBC & OWNbm & OWNrp & OFF & LENM & MAX31 & DD))]. unfold bio_head in HEADc.
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNbb)) as (BB0' & BB16 & _ & BBCe & _).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNrp)) as (RP0' & RP16 & _ & RPCe & _).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNbm)) as (BM0' & BM16 & _ & BMCe & _).
  unfold bio_w1_cells in W1Cc.
  change ([C8 (wz 4294967297); C4 (wz flc); C4 rrwc; C4 (wz 4294967295); C4 padwc; C8 (wz BBc)]) with ([C8 (wz 4294967297)] ++ [C4 (wz flc)] ++ [C4 rrwc; C4 (wz 4294967295); C4 padwc] ++ [C8 (wz BBc)]) in W1Cc.
  apply (proj1 (rw_cells_app usegs mc0 _ _ _)) in W1Cc. destruct W1Cc as [_ W1Cc].
  apply (proj1 (rw_cells_app usegs mc0 _ _ _)) in W1Cc. destruct W1Cc as [FLC W1Cc].
  apply (proj1 (rw_cells_app usegs mc0 _ _ _)) in W1Cc. destruct W1Cc as [_ PTRC]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app] in FLC, PTRC.
  replace (BI + 40 + 8) with (BI + 48) in FLC by lia. replace (BI + 40 + 8 + 4 + 12) with (BI + 64) in PTRC by lia.
  assert (RPC : exists dw mw, ro_cells usegs mc0 RPc [C8 (wz (len - off)); C8 dw; C8 mw; C8 (wz (msec meth))]).
  { destruct (k_d K) as [pd|].
    - destruct DD as (Dd & nm & ? & _ & _ & _ & RPC & _). unfold readp_cells in RPC. do 2 eexists. exact (proj1 RPC).
    - destruct DD as (MAX0 & _ & RPC). unfold readp_cells in RPC. replace (len - off) with (0 - 0) by lia. do 2 eexists. exact (proj1 RPC). }
  destruct RPC as (dw & mw & RPC).
  eapply evt_cut.
  { eapply W1_ctrl_info_proof with (lo := lo) (BI := BI) (BB := BBc) (BM := BMc) (RP := RPc) (fl := flc);
      [reflexivity| reflexivity| reflexivity| exact BI0| exact (proj1 FLC)| exact FLOKc| exact (proj1 PTRC)| exact BB0'| clear - BBCe CW; lia| exact (proj1 BBC)| exact RP0'| exact RPC
      | exact BM0'| clear - BMCe CW; lia| exact BI8| clear - BB16; Z.div_mod_to_equations; lia| clear - BM16; Z.div_mod_to_equations; lia| clear - RP16; Z.div_mod_to_equations; lia
      | rewrite unsigned_lit by lia; exact STc| clear - LO CEIL_RANGE__; unfold ceil_window in *; lia| rewrite unsigned_lit by lia; clear - SLO SPR; lia
      | clear - BIC LO; lia| clear - BBCe LO; lia| clear - RPCe LO; lia| exact MIc]. }
  cbv beta. intros ms' PO. destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mz & -> & MUc & WMc & MIz & STz).
  rewrite !unsigned_lit in MUc by lia. rewrite unsigned_lit in STz by lia. th_ret_lit.
  eapply rw_cells_transport in FRc; [| exact MUc| exact WMc| cbn [bio_head bio_tail bio_w1_cells length disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - SPR; lia].
  eapply rw_cells_transport in HEADc; [| exact MUc| exact WMc| cbn [bio_head bio_tail bio_w1_cells length disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - SPR BIC LO SLO; lia].
  assert (MUz : munch [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m mz).
  { eapply munch_trans; [exact MUq|]. eapply munch_weaken; [| exact MUc]. unfold sub_fp. cbn [outside]. clear - SPR. intros a Ha. lia. }
  pose proof (wmono_trans _ _ _ _ WMq WMc) as WMz.
  pose proof (mbio_rep_agree _ _ _ _ _ _ _ _ _ _ MB (munch_mbio_fp _ _ _ _ _ _ _ _ _ _ _ K CST MUz WMz FPD)) as MBz.
  clear MUq WMq MUc WMc STc MIc FLC PTRC BBC RPC TAILc DD.
  (* [comment removed for export] *)
  step. step. step. th_if_lit. step. step. th_if_lit. step. do 6 step.
  release_frame FRc STz (bv_unsigned sp). step. step. chere. apply climpl_done.
  exists (wz (len - off)), mz, LBall. split; [unfold cret; do 14 eexists; reflexivity|]. split; [clear; lia|]. split; [clear; unfold cgrow; lia|].
  split. { eapply (cstate_seg _ _ _ _ _ m mz _ sp _ lo Bd (bv_unsigned sp)); [exact CST| exact MUz| exact WMz| exact MIz| | clear - SLO SPR; lia| exact SPB| | exact STz| exact SPB].
    - apply Forall_cons; [apply cwin_stack; clear - SLO SPR; lia| apply Forall_nil]. - cbn [disjoint_from]. unfold LX_FLAGS. clear - SLO SPR GLO; lia. }
  split. { eapply cframe_seg; [apply cframe_refl| exact MUz| exact WMz| exact HP| clear - SLO SPR LO; lia|]. apply Forall_cons; [apply cseg_ok_stack; clear - SLO SPR LO; lia| apply Forall_nil]. }
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity| exact MBz].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem bio_ctrl_ptr_proof : bio_ctrl_ptr_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB0 L f K BI meth len max off lo Bd qs old
         CST SLO MB QS QSZ PPC PPB SP16 -> -> -> ->.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  unfold BCTRL_STACK, FZ_BIO_CTRL, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  destruct MB as [BM MBX].
  pose proof MBX as (BBx & RPx & flx & rrwx & padwx & nrx & nwx & OWNB & NDK & METH & _).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNB)) as (BI0 & BI16 & _ & BIC & BIIMG). hide BIIMG.
  assert (BI8 : BI mod 8 = 0) by (clear - BI16; Z.div_mod_to_equations; lia).
  unfold M_MEM, M_SECMEM in METH.
  pose proof (meth_ctrl m meth CIMG MI ltac:(unfold M_MEM, M_SECMEM; exact METH)) as MCTRL.
  assert (METH8 : meth mod 8 = 0) by (clear - METH; destruct METH as [-> | ->]; reflexivity).
  assert (FPD : forall b, In b LBall -> mbio_T K (blk_id b) -> disjoint_from [(bv_unsigned sp - 144, bv_unsigned sp); (bv_unsigned sp + 88, bv_unsigned sp + 96)]%Z (blk_addr b) (blk_size b)).
  { intros [[bp bA] bn] IN _. pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST IN) as (_ & _ & _ & RC & _).
    unfold blk_addr, blk_size. cbn [fst snd disjoint_from]. clear - RC LO SLO SPR. lia. }
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (bv_unsigned sp + 88, bv_unsigned sp + 96)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof MBX as (BB0_ & RP0_ & fl0 & rrw0 & padw0 & nr0 & nw0 & _ & _ & _ & HEAD & _). unfold bio_head in HEAD.
  cprefix. step. th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST. do 6 step. step.
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
  step. step. step. ubs_if.
  step. step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
  step. step. step. ubs_if.
  step. step. th_if_lit. step. step. step. step. th_if_lit. step. step. th_if_lit.
  step. ubs_if. step. step. ubs_if.
  step. step. step. step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mc0 end.
  lazymatch goal with H : stk usegs mc0 lo _ |- _ => rename H into STc end. lazymatch goal with H : mem_inv usegs mc0 |- _ => rename H into MIc end.
  lazymatch goal with H : munch _ m mc0 |- _ => rename H into MUq end. lazymatch goal with H : wmono usegs m mc0 |- _ => rename H into WMq end.
  lazymatch goal with H : rw_cells usegs mc0 (bv_unsigned sp + -48) _ |- _ => rename H into FRc end.
  lazymatch goal with H : rw_cells usegs mc0 (bv_unsigned sp) _ |- _ => rename H into QSc end.
  lazymatch goal with H : rw_cells usegs mc0 (bv_unsigned sp + 88) _ |- _ => rename H into PPc end.
  pose proof (mbio_repx_agree _ _ _ _ _ _ _ _ _ _ _ _ MBX (munch_mbio_fp _ _ _ _ _ _ _ _ _ _ _ K CST MUq WMq FPD)) as MBc.
  destruct MBc as (BBc & RPc & flc & rrwc & padwc & nrc & nwc & _ & _ & _ & HEADc & W1Cc & FLOKc & TAILc & (rmaxw & OWNbb & BBC & OWNbm & OWNrp & OFF & LENM & MAX31 & DD)). unfold bio_head in HEADc.
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNbb)) as (BB0' & BB16 & _ & BBCe & BBIMG). hide BBIMG.
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNbm)) as (BM0' & BM16 & _ & BMCe & BMIMG). hide BMIMG.
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNrp)) as (RP0' & RP16 & _ & RPCe & RPIMG). hide RPIMG.
  assert (BB8 : BBc mod 8 = 0) by (clear - BB16; Z.div_mod_to_equations; lia).
  assert (BM8 : BM mod 8 = 0) by (clear - BM16; Z.div_mod_to_equations; lia).
  assert (RP8 : RPc mod 8 = 0) by (clear - RP16; Z.div_mod_to_equations; lia).
  assert (PP8 : (bv_unsigned sp + 88) mod 8 = 0) by (clear - SP16; Z.div_mod_to_equations; lia).
  pose proof W1Cc as W1C0. unfold bio_w1_cells in W1Cc.
  change ([C8 (wz 4294967297); C4 (wz flc); C4 rrwc; C4 (wz 4294967295); C4 padwc; C8 (wz BBc)]) with ([C8 (wz 4294967297)] ++ [C4 (wz flc)] ++ [C4 rrwc; C4 (wz 4294967295); C4 padwc] ++ [C8 (wz BBc)]) in W1Cc.
  apply (proj1 (rw_cells_app usegs mc0 _ _ _)) in W1Cc. destruct W1Cc as [ISW W1Cc].
  apply (proj1 (rw_cells_app usegs mc0 _ _ _)) in W1Cc. destruct W1Cc as [FLC W1Cc].
  apply (proj1 (rw_cells_app usegs mc0 _ _ _)) in W1Cc. destruct W1Cc as [_ PTRC]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app] in FLC, PTRC.
  replace (BI + 40 + 8) with (BI + 48) in FLC by lia. replace (BI + 40 + 8 + 4 + 12) with (BI + 64) in PTRC by lia.
  change 4294967297 with (1 + 2 ^ 32 * 1) in ISW. apply (proj2 (t_cells_halves usegs mc0 (BI + 40) 1 1 ltac:(lia) ltac:(lia))) in ISW.
  change ([C4 (wz 1); C4 (wz 1)]) with ([C4 (wz 1)] ++ [C4 (wz 1)]) in ISW. apply (proj1 (rw_cells_app usegs mc0 _ _ _)) in ISW. destruct ISW as [INITC _].
  (* [comment removed for export] *)
  pose proof NDK as NDK0. unfold mbio_blocks in NDK.
  assert (ND4 : k_bi K <> k_bm K /\ k_bi K <> k_rp K /\ k_bb K <> k_bm K /\ k_bb K <> k_rp K /\ k_bm K <> k_rp K).
  { clear - NDK. apply List.NoDup_app_remove_r in NDK. inversion NDK as [|x1 l1 N1 ND1]; subst. inversion ND1 as [|x2 l2 N2 ND2]; subst. inversion ND2 as [|x3 l3 N3 ND3]; subst.
    cbn [In] in N1, N2, N3. repeat split; intros E; rewrite E in *; tauto. }
  destruct ND4 as (N13 & N14 & N23 & N24 & N34).
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNB) (proj1 OWNbm) N13) as A13.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNB) (proj1 OWNrp) N14) as A14.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNbb) (proj1 OWNbm) N23) as A23.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNbb) (proj1 OWNrp) N24) as A24.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNbm) (proj1 OWNrp) N34) as A34.
  hide N13. hide N14. hide N23. hide N24. hide N34. hide A13. hide A14. hide A23. hide A24. hide A34.
  Ltac trw2 H MUc WMc := eapply rw_cells_transport in H; [| exact MUc| exact WMc| cbn [bio_head bio_tail bio_w1_cells length disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]].
  (* [comment removed for export] *)
  assert (EXIT : forall mz Wz BMz (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    rw_cells usegs mz (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> stk usegs mz lo (bv_unsigned sp + -48) -> mem_inv usegs mz ->
    rw_cells usegs mz BI [C8 (wz 0); C8 (wz meth); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
    munch Wz m mz -> wmono usegs m mz -> Forall (cwin LBall lo (bv_unsigned sp + 96)) Wz -> disjoint_from Wz LX_FLAGS 1 -> Forall (cseg_ok (mbio_T K) [] (bv_unsigned sp + 96) LBall LBall) Wz ->
    rw_cells usegs mz (bv_unsigned sp) qs -> rw_cells usegs mz (bv_unsigned sp + 88) [C8 (wz BMz)] -> mbio_repx mz LBall L K BI BMz (wz (len - off)) meth (len - off) max 0 ->
    climpl f L s (MS (mkR (wz 0x10bc5c) (wz (bv_unsigned sp + -48)) gp tp x5 x6 x7 sp (wz 0) (wz 1) x11 x12 x13 x14 x15 x16 x17 (wz 115) (wz (bv_unsigned sp + 88)) (wz BI) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (wz 0x10bc5c) fc None mz (seg_rom usegs))
      (cpostx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB0 L f m lo Bd (mbio_T K) [] (bv_unsigned sp + 96) 0 0 0 0
         (fun v LBall' L' m' => exists BM, v = wz 1 /\ LBall' = LBall /\ L' = L /\ rw_cells usegs m' (bv_unsigned sp) qs /\ rw_cells usegs m' (bv_unsigned sp + 88) [C8 (wz BM)]
              /\ mbio_repx m' LBall L K BI BM (wz (len - off)) meth (len - off) max 0))).
  { intros mz Wz BMz x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 FRz STz MIz HEADz MUz WMz CW1 DLX CW2 QSz PPz MBz.
    cprefix. step. step. step. th_if_lit. step. step. th_if_lit. step. do 6 step.
    release_frame FRz STz (bv_unsigned sp). step. step. chere. apply climpl_done.
    exists (wz 1), mz, LBall. split; [unfold cret; do 14 eexists; reflexivity|]. split; [clear; lia|]. split; [clear; unfold cgrow; lia|].
    split. { eapply (cstate_seg _ _ _ _ _ m mz _ sp _ lo Bd (bv_unsigned sp + 96)); [exact CST| exact MUz| exact WMz| exact MIz| exact CW1| clear - SLO SPR; lia| exact PPB| exact DLX| assumption| exact SPB]. }
    split. { eapply cframe_seg; [apply cframe_refl| exact MUz| exact WMz| exact HP| clear - SLO SPR LO; lia| exact CW2]. }
    exists BMz. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact QSz|]. split; [exact PPz| exact MBz]. }
    assert (INB : In (k_bi K, BI, 128) LBall) by exact (proj1 OWNB). assert (INM : In (k_bm K, BM, 32) LBall) by exact (proj1 OWNbm). assert (INR : In (k_rp K, RPc, 32) LBall) by exact (proj1 OWNrp).
  destruct (k_d K) as [pd|] eqn:KD.
  - (* [comment removed for export] *)
    destruct DD as (D & nm & junk0 & OWNd & MAXP & BMC & RPC & LJ & DC).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNd)) as (D0 & _ & _ & DCe & DIMG). hide DIMG.
    assert (NDd : k_bi K <> pd /\ k_bb K <> pd /\ k_bm K <> pd /\ k_rp K <> pd).
    { clear - NDK. cbn [app] in NDK.
      inversion NDK as [|x1 l1 N1 ND1]; subst. inversion ND1 as [|x2 l2 N2 ND2]; subst. inversion ND2 as [|x3 l3 N3 ND3]; subst. inversion ND3 as [|x4 l4 N4 ND4]; subst.
      cbn [In] in N1, N2, N3, N4. repeat split; intros E; rewrite E in *; tauto. }
    destruct NDd as (N15 & N25 & N35 & N45).
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNB) (proj1 OWNd) N15) as A15.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNbb) (proj1 OWNd) N25) as A25.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNbm) (proj1 OWNd) N35) as A35.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNrp) (proj1 OWNd) N45) as A45.
    hide N15. hide N25. hide N35. hide N45. hide A15. hide A25. hide A35. hide A45. clear NDK.
    assert (IND : In (pd, D, max) LBall) by exact (proj1 OWNd).
    eapply evt_cut.
    { eapply W1_ctrl_ptr_proof with (lo := lo) (BI := BI) (BB := BBc) (BM := BM) (RP := RPc) (D := D) (len := len) (max := max) (off := off) (fl := flc) (PP := bv_unsigned sp + 88)
                                  (rmaxw := rmaxw) (flw := wz (msec meth)) (junk := junk0);
        [reflexivity| reflexivity| reflexivity| exact BI0| clear - SPR LO GLO SLO; lia| pose proof AV as (av & ? & ? & ? & ? & ? & ? & ? & ? & ? & AVH); clear - PPB AVH; lia
        | exact (proj1 INITC)| exact (proj1 FLC)| exact FLOKc| exact (proj1 PTRC)| exact BB0'| clear - BBCe CW; lia| exact (proj1 BBC)
        | exact BM0'| unfold bufmem_cells; exact BMC| exact RP0'| exact RPC| exact D0| exact OFF| exact LENM| clear - MAX31; lia| clear - DCe CW; lia| exact LJ| exact DC| exact PPc
        | exact BI8| exact BB8| exact BM8| exact RP8| exact PP8
        | rewrite unsigned_lit by lia; exact STc| clear - LO CEIL_RANGE__; unfold ceil_window in *; lia| rewrite unsigned_lit by lia; clear - SLO SPR; lia
        | clear - BIC LO; lia| clear - BBCe LO; lia| clear - BMCe LO; lia| clear - RPCe LO; lia| clear - DCe LO; lia
        | unfold hideP in A25; clear - A25; lia| unfold hideP in A35; clear - A35; lia| unfold hideP in A45; clear - A45; lia| unfold hideP in A34; clear - A34; lia
        | unfold tbox; unfold hideP in A23, A24; clear - A23 A24 DCe BMCe RPCe LO SLO SPR GLO; rewrite ?unsigned_lit by lia; repeat split; lia
        | exact MIc]. }
    cbv beta. intros ms' PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & rmaxw' & junk' & mz & -> & MUc & WMc & MIz & STz & BMCz & RPCz & LJ' & DCz & PPz).
    unfold bufmem_cells in BMCz. rewrite !unsigned_lit in MUc by lia. rewrite unsigned_lit in STz by lia. th_ret_lit.
    trw2 FRc MUc WMc. 2: { clear - SPR DCe BMCe RPCe LO SLO; lia. }
    trw2 QSc MUc WMc. 2: { rewrite <- (Nat2Z.id (cells_size qs)), QSZ. clear - SPR DCe BMCe RPCe LO SLO QSZ; lia. }
    trw2 HEADc MUc WMc. 2: { unfold hideP in A13, A14, A15; clear - SPR BIC DCe BMCe RPCe LO SLO A13 A14 A15 MAXP; lia. }
    trw2 W1C0 MUc WMc. 2: { unfold hideP in A13, A14, A15; clear - SPR BIC DCe BMCe RPCe LO SLO A13 A14 A15 MAXP; lia. }
    trw2 TAILc MUc WMc. 2: { unfold hideP in A13, A14, A15; clear - SPR BIC DCe BMCe RPCe LO SLO A13 A14 A15 MAXP; lia. }
    trw2 BBC MUc WMc. 2: { unfold hideP in A23, A24, A25; clear - SPR BBCe DCe BMCe RPCe LO SLO A23 A24 A25 MAXP; lia. }
    assert (MUz : munch [(bv_unsigned sp - 144, bv_unsigned sp); (bv_unsigned sp + 88, bv_unsigned sp + 96); (D, D + max); (BM, BM + 8); (RPc + 8, RPc + 16)]%Z m mz).
    { eapply munch_trans; [eapply munch_weaken; [| exact MUq]| eapply munch_weaken; [| exact MUc]]; unfold sub_fp; cbn [outside]; clear - SPR; intros a Ha; lia. }
    pose proof (wmono_trans _ _ _ _ WMq WMc) as WMz. clear MUq WMq MUc WMc STc MIc.
    chere. eapply (EXIT mz _ BM); try eassumption.
    + apply Forall_cons; [apply cwin_stack; clear - SLO SPR; lia|]. apply Forall_cons; [apply cwin_stack; clear - SLO SPR LO GLO; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pd, D, max)); [exact IND| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (k_bm K, BM, 32)); [exact INM| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (k_rp K, RPc, 32)); [exact INR| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia| apply Forall_nil].
    + cbn [disjoint_from]. unfold LX_FLAGS. unfold hideP in DIMG, BMIMG, RPIMG. clear - SLO SPR GLO DIMG BMIMG RPIMG MAXP. lia.
    + apply Forall_cons; [apply cseg_ok_stack; clear - SLO SPR LO; lia|]. apply Forall_cons; [apply cseg_ok_stack; clear - SLO SPR LO; lia|].
      apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (pd, D, max)); [exact IND| intros b0 _ NT E; apply NT; rewrite E; unfold mbio_T; cbn [blk_id fst]; do 4 right; exact KD| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia|].
      apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (k_bm K, BM, 32)); [exact INM| intros b0 _ NT E; apply NT; rewrite E; unfold mbio_T; cbn [blk_id fst]; tauto| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia|].
      apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (k_rp K, RPc, 32)); [exact INR| intros b0 _ NT E; apply NT; rewrite E; unfold mbio_T; cbn [blk_id fst]; tauto| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia| apply Forall_nil].
    + exists BBc, RPc, flc, rrwc, padwc, nrc, nwc. split; [exact OWNB|]. split; [exact NDK0|]. split; [unfold M_MEM, M_SECMEM; exact METH|]. split; [exact HEADc|].
      split; [exact W1C0|]. split; [exact FLOKc|]. split; [exact TAILc|].
      exists rmaxw'. split; [exact OWNbb|]. split; [exact BBC|]. split; [exact OWNbm|]. split; [exact OWNrp|]. split; [clear - OFF; lia|]. split; [clear - OFF LENM; lia|]. split; [exact MAX31|].
      rewrite KD. exists D, nm, junk'. split; [exact OWNd|]. split; [exact MAXP|]. split; [exact BMCz|]. split; [exact RPCz|]. split; [exact LJ'| exact DCz].
  - (* [comment removed for export] *)
    destruct DD as (MAX0 & BMC & RPC). assert (L0 : len = 0) by (clear - OFF LENM MAX0; lia). assert (O0 : off = 0) by (clear - OFF LENM MAX0; lia). subst len off.
    unfold readp_cells in RPC. change (0 - 0) with 0 in *. change (0 + 0) with 0 in RPC. clear NDK.
    eapply evt_cut.
    { eapply W1_ctrl_ptr0_proof with (lo := lo) (BI := BI) (BB := BBc) (BM := BM) (RP := RPc) (fl := flc) (PP := bv_unsigned sp + 88);
        [reflexivity| reflexivity| reflexivity| exact BI0| clear - SPR LO GLO SLO; lia| pose proof AV as (av & ? & ? & ? & ? & ? & ? & ? & ? & ? & AVH); clear - PPB AVH; lia
        | exact (proj1 INITC)| exact (proj1 FLC)| exact FLOKc| exact (proj1 PTRC)| exact BB0'| clear - BBCe CW; lia| exact (proj1 BBC)
        | exact (proj1 BMC)| exact RP0'| exact (proj1 RPC)| exact PPc
        | clear - BM0'; lia| exact BI8| exact BB8| exact BM8| exact RP8| exact PP8
        | rewrite unsigned_lit by lia; exact STc| clear - LO CEIL_RANGE__; unfold ceil_window in *; lia| rewrite unsigned_lit by lia; clear - SLO SPR; lia
        | clear - BIC LO; lia| clear - BBCe LO; lia| clear - BMCe LO; lia| clear - RPCe LO; lia| clear - LO SLO SPR GLO; rewrite ?unsigned_lit by lia; lia
        | exact MIc]. }
    cbv beta. intros ms' PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mz & -> & MUc & WMc & MIz & STz & PPz).
    rewrite !unsigned_lit in MUc by lia. rewrite unsigned_lit in STz by lia. th_ret_lit.
    trw2 FRc MUc WMc. 2: { clear - SPR LO SLO; lia. }
    trw2 QSc MUc WMc. 2: { rewrite <- (Nat2Z.id (cells_size qs)), QSZ. clear - SPR LO SLO QSZ; lia. }
    trw2 HEADc MUc WMc. 2: { clear - SPR BIC LO SLO; lia. } trw2 W1C0 MUc WMc. 2: { clear - SPR BIC LO SLO; lia. } trw2 TAILc MUc WMc. 2: { clear - SPR BIC LO SLO; lia. }
    trw2 BBC MUc WMc. 2: { clear - SPR BBCe LO SLO; lia. } trw2 BMC MUc WMc. 2: { clear - SPR BMCe LO SLO; lia. } trw2 RPC MUc WMc. 2: { clear - SPR RPCe LO SLO; lia. }
    assert (MUz : munch [(bv_unsigned sp - 144, bv_unsigned sp); (bv_unsigned sp + 88, bv_unsigned sp + 96)]%Z m mz).
    { eapply munch_trans; [exact MUq| eapply munch_weaken; [| exact MUc]]; unfold sub_fp; cbn [outside]; clear - SPR; intros a Ha; lia. }
    pose proof (wmono_trans _ _ _ _ WMq WMc) as WMz. clear MUq WMq MUc WMc STc MIc.
    chere. eapply (EXIT mz _ BM); try eassumption.
    + apply Forall_cons; [apply cwin_stack; clear - SLO SPR; lia|]. apply Forall_cons; [apply cwin_stack; clear - SLO SPR LO GLO; lia| apply Forall_nil].
    + cbn [disjoint_from]. unfold LX_FLAGS. clear - SLO SPR GLO. lia.
    + apply Forall_cons; [apply cseg_ok_stack; clear - SLO SPR LO; lia|]. apply Forall_cons; [apply cseg_ok_stack; clear - SLO SPR LO; lia| apply Forall_nil].
    + exists BBc, RPc, flc, rrwc, padwc, nrc, nwc. split; [exact OWNB|]. split; [exact NDK0|]. split; [unfold M_MEM, M_SECMEM; exact METH|]. split; [exact HEADc|].
      split; [exact W1C0|]. split; [exact FLOKc|]. split; [exact TAILc|].
      exists rmaxw. split; [exact OWNbb|]. split; [exact BBC|]. split; [exact OWNbm|]. split; [exact OWNrp|]. split; [clear; lia|]. split; [clear - MAX0; lia|]. split; [exact MAX31|].
      rewrite KD. split; [exact MAX0|]. split; [exact BMC| unfold readp_cells; change (0 - 0) with 0; change (0 + 0) with 0; exact RPC].
Qed.
End WithCeiling0.
