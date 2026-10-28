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
     From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_W1_defs Fz_W1_sync Fz_W1_bits Fz_W1_write Fz_W1_read Fz_W1_gets Fz_W1_misc Fz_W3_iface.
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
Lemma meth_bgets : forall m meth, cimg m -> mem_inv usegs m -> (meth = M_MEM \/ meth = M_SECMEM) -> rw_cells usegs m (meth + 56) [C8 (wz 0x1835f0)].
Proof.
  intros m meth CIMG MI [-> | ->]; unfold M_MEM, M_SECMEM.
  - cimg_cell CIMG m (0x2d3fc8 + 56) [C8 (wz 0x1835f0)] H. exact H.
  - cimg_cell CIMG m (0x2d4038 + 56) [C8 (wz 0x1835f0)] H. exact H.
Qed.

Theorem bio_gets_proof : bio_gets_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB0 L f K pl BI meth len max off LB lo Bd bs
         CST SLO MB OWNL NTL LBS BUF -> -> ->.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  destruct MB as (BM & BB & RP & fl & rrw & padw & nr & nw & OWNB & NDK & METH & HEAD & W1C & FLOK & TAIL & INNER).
  destruct INNER as (rmaxw & OWNbb & BBC & OWNbm & OWNrp & OFF & LENM & MAX31 & DOPT).
  unfold BGETS_STACK, FZ_BIO_GETS, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNB)) as (BI0 & BI16 & _ & BIC & BIIMG).
  assert (BI8 : BI mod 8 = 0) by (clear - BI16; Z.div_mod_to_equations; lia).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNbb)) as (BB0 & BB16 & _ & BBCe & BBIMG).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNrp)) as (RP0 & RP16 & _ & RPCe & RPIMG).
  assert (BB8 : BB mod 8 = 0) by (clear - BB16; Z.div_mod_to_equations; lia).
  assert (RP8 : RP mod 8 = 0) by (clear - RP16; Z.div_mod_to_equations; lia).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNL)) as (LB00 & _ & _ & LBC & LBIMG).
  pose proof (meth_bgets m meth CIMG MI METH) as BGETS.
  (* [comment removed for export] *)
  unfold bio_w1_cells in W1C.
  change ([C8 (wz 4294967297); C4 (wz fl); C4 rrw; C4 (wz 4294967295); C4 padw; C8 (wz BB)]) with ([C8 (wz 4294967297)] ++ [C4 (wz fl)] ++ [C4 rrw; C4 (wz 4294967295); C4 padw] ++ [C8 (wz BB)]) in W1C.
  apply (proj1 (rw_cells_app usegs m _ _ _)) in W1C. destruct W1C as [ISW W1C].
  apply (proj1 (rw_cells_app usegs m _ _ _)) in W1C. destruct W1C as [FLC W1C].
  apply (proj1 (rw_cells_app usegs m _ _ _)) in W1C. destruct W1C as [MIDC PTRC]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app] in FLC, MIDC, PTRC.
  replace (BI + 40 + 8) with (BI + 48) in FLC by lia. replace (BI + 40 + 8 + 4) with (BI + 52) in MIDC by lia. replace (BI + 40 + 8 + 4 + 12) with (BI + 64) in PTRC by lia.
  change 4294967297 with (1 + 2 ^ 32 * 1) in ISW. apply (proj2 (t_cells_halves usegs m (BI + 40) 1 1 ltac:(lia) ltac:(lia))) in ISW.
  unfold bio_head in HEAD. unfold bio_tail in TAIL. unfold M_MEM, M_SECMEM in METH.
  assert (MT8 : meth mod 8 = 0) by (clear - METH; destruct METH as [E|E]; rewrite E; reflexivity).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNbm)) as (BM0 & _ & _ & BMCe & BMIMG).
  (* [comment removed for export] *)
  pose proof NDK as NDK0. unfold mbio_blocks in NDK.
  assert (ND4 : k_bi K <> k_bb K /\ k_bi K <> k_bm K /\ k_bi K <> k_rp K /\ k_bb K <> k_bm K /\ k_bb K <> k_rp K /\ k_bm K <> k_rp K).
  { clear - NDK. apply List.NoDup_app_remove_r in NDK. inversion NDK as [|x1 l1 N1 ND1]; subst. inversion ND1 as [|x2 l2 N2 ND2]; subst. inversion ND2 as [|x3 l3 N3 ND3]; subst.
    cbn [In] in N1, N2, N3. repeat split; intros E; rewrite E in *; tauto. }
  destruct ND4 as (N12 & N13 & N14 & N23 & N24 & N34).
  assert (NL : pl <> k_bi K /\ pl <> k_bb K /\ pl <> k_bm K /\ pl <> k_rp K) by (unfold mbio_T in NTL; repeat split; intros E; apply NTL; rewrite E; tauto).
  destruct NL as (NL1 & NL2 & NL3 & NL4).
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNB) (proj1 OWNbb) N12) as A12.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNB) (proj1 OWNbm) N13) as A13.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNB) (proj1 OWNrp) N14) as A14.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNbb) (proj1 OWNbm) N23) as A23.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNbb) (proj1 OWNrp) N24) as A24.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNbm) (proj1 OWNrp) N34) as A34.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNL) (proj1 OWNB) NL1) as AL1.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNL) (proj1 OWNbb) NL2) as AL2.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNL) (proj1 OWNbm) NL3) as AL3.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNL) (proj1 OWNrp) NL4) as AL4.
  hide N12. hide N13. hide N14. hide N23. hide N24. hide N34. hide NL1. hide NL2. hide NL3. hide NL4. hide NTL. clear NDK.
  hide A12. hide A13. hide A14. hide A23. hide A24. hide A34. hide AL1. hide AL2. hide AL3. hide AL4. hide BIIMG. hide BBIMG. hide RPIMG. hide LBIMG. hide BMIMG.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp); (BI + 48, BI + 52); (LB, LB + 256); (RP, RP + 24)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  assert (EXIT : forall mz (k off' fl' : Z) (bs' : list byte) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x28 x29 x30 x31 : word),
    (k = 0 /\ off' = off /\ off = len \/ 1 <= k <= Z.min (len - off) 254 /\ off' = off + k /\ nth_error bs' (Z.to_nat k) = Some (Z_to_bv 8 0)) ->
    rw_cells usegs mz (bv_unsigned sp + -48) [C8 (wz k); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> stk usegs mz lo (bv_unsigned sp + -48) -> mem_inv usegs mz ->
    munch [(bv_unsigned sp - 176, bv_unsigned sp); (BI + 48, BI + 52); (LB, LB + 256); (RP, RP + 24)]%Z m mz -> wmono usegs m mz ->
    rw_cells usegs mz BI [C8 (wz 0); C8 (wz meth); C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> rw_cells usegs mz (BI + 40) [C4 (wz 1); C4 (wz 1)] ->
    rw_cells usegs mz (BI + 48) [C4 (wz fl')] -> fl_ok fl' -> rw_cells usegs mz (BI + 52) [C4 rrw; C4 (wz 4294967295); C4 padw] -> rw_cells usegs mz (BI + 64) [C8 (wz BB)] ->
    rw_cells usegs mz (BI + 72) [C8 (wz 0); C8 (wz 0); C4 (wz 1); C4 (wz 0); C8 nr; C8 nw; C8 (wz 0); C8 (wz 0)] ->
    rw_cells usegs mz BB [C8 (wz BM); C8 (wz RP)] ->
    mb_inner mz LBall L K BB BM RP len max off' (wz (msec meth)) (wz len) ->
    length bs' = 256%nat -> rw_cells usegs mz LB [CB 256 bs'] ->
    climpl f L s (MS (mkR (wz 0x10c5b0) (wz (bv_unsigned sp + -48)) gp tp x5 x6 x7 sp (wz 255) x10 x11 x12 x13 x14 x15 (wz (Z.min k 1)) x17 (wz LB) (wz BI) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (wz 0x10c5f4) fc None mz (seg_rom usegs))
      (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB0 L f m lo Bd (fun q => mbio_T K q \/ q = pl) [] 0 0 0 0 (bio_gets_res K BI meth len max off LB bs LBall L))).
  { intros mz k off' fl' bs' x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x28 x29 x30 x31 HK FRz STz MIz MUz WMz HEADz ISWz FLCz FLOKz MIDCz PTRCz TAILz BBCz MBz LBSz BUFz.
    assert (KR : 0 <= k <= 254) by (clear - HK LENM OFF; lia). assert (KM : 0 <= Z.min k 1 <= 1) by (clear - KR; lia).
    assert (FIN : forall (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word), stk usegs mz lo (bv_unsigned sp) ->
      cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB0 L f m lo Bd (fun q => mbio_T K q \/ q = pl) [] 0 0 0 0 (bio_gets_res K BI meth len max off LB bs LBall L)
        f L s (MS (mkR ra sp gp tp y5 y6 y7 s0 s1 (wz k) y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31) F (ret_pc ra) fc None mz (seg_rom usegs))).
    { intros y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 STf.
      assert (INB : In (k_bi K, BI, 128) LBall) by exact (proj1 OWNB). assert (INL : In (pl, LB, 256) LBall) by exact (proj1 OWNL). assert (INR : In (k_rp K, RP, 32) LBall) by exact (proj1 OWNrp).
      exists (wz k), mz, LBall. split; [unfold cret; do 14 eexists; reflexivity|]. split; [clear; lia|]. split; [clear; unfold cgrow; lia|].
      split. { eapply (cstate_seg _ _ _ _ _ m mz _ sp _ lo Bd (bv_unsigned sp)); [exact CST| exact MUz| exact WMz| exact MIz| | clear - SLO SPR; lia| exact SPB| | exact STf| exact SPB].
        - apply Forall_cons; [apply cwin_stack; clear - SLO SPR; lia|].
          apply Forall_cons; [apply (cwin_block _ _ _ (k_bi K, BI, 128)); [exact INB| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia|].
          apply Forall_cons; [apply (cwin_block _ _ _ (pl, LB, 256)); [exact INL| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia|].
          apply Forall_cons; [apply (cwin_block _ _ _ (k_rp K, RP, 32)); [exact INR| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia| apply Forall_nil].
        - cbn [disjoint_from]. unfold LX_FLAGS. unfold hideP in BIIMG, RPIMG, LBIMG. clear - SLO SPR GLO BIIMG RPIMG LBIMG. lia. }
      split. { eapply cframe_seg; [apply cframe_refl| exact MUz| exact WMz| exact HP| clear - SLO SPR LO; lia|].
        apply Forall_cons; [apply cseg_ok_stack; clear - SLO SPR LO; lia|].
        apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (k_bi K, BI, 128)); [exact INB| intros b0 _ NT E; apply NT; rewrite E; left; unfold mbio_T; cbn [blk_id fst]; tauto| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia|].
        apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (pl, LB, 256)); [exact INL| intros b0 _ NT E; apply NT; rewrite E; right; reflexivity| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia|].
        apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (k_rp K, RP, 32)); [exact INR| intros b0 _ NT E; apply NT; rewrite E; left; unfold mbio_T; cbn [blk_id fst]; tauto| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia| apply Forall_nil]. }
      exists k, bs'. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact LBSz|]. split; [exact BUFz|].
      assert (MB' : mbio_rep mz LBall L K BI meth len max off').
      { exists BM, BB, RP, fl', rrw, padw, nr, nw. split; [exact OWNB|]. split; [exact NDK0|]. split; [unfold M_MEM, M_SECMEM; exact METH|]. split; [exact HEADz|].
        split. { unfold bio_w1_cells. change ([C8 (wz 4294967297); C4 (wz fl'); C4 rrw; C4 (wz 4294967295); C4 padw; C8 (wz BB)]) with ([C8 (wz 4294967297)] ++ [C4 (wz fl')] ++ [C4 rrw; C4 (wz 4294967295); C4 padw] ++ [C8 (wz BB)]).
          apply rw_cells_app. split; [change 4294967297 with (1 + 2 ^ 32 * 1); apply (proj1 (t_cells_halves usegs mz (BI + 40) 1 1 ltac:(lia) ltac:(lia))); exact ISWz|].
          cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (BI + 40 + 8) with (BI + 48) by (clear; lia).
          apply rw_cells_app. split; [exact FLCz|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (BI + 48 + 4) with (BI + 52) by (clear; lia).
          apply rw_cells_app. split; [exact MIDCz|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (BI + 52 + 12) with (BI + 64) by (clear; lia). exact PTRCz. }
        split; [exact FLOKz|]. split; [exact TAILz| exact MBz]. }
      destruct HK as [(-> & -> & EQ)|(K1 & -> & NULk)]; [left| right]; auto. }
    cprefix. step. rewrite (t_sextw_small (Z.min k 1)) by lia. step. if_cases KZ; zify_cond KZ.
    - (* [comment removed for export] *) assert (k = 0) by (rewrite ?unsigned_lit in KZ by lia; lia). subst k. change (Z.min 0 1) with 0.
      step. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0). do 5 step.
      release_frame FRz STz (bv_unsigned sp). step. step. chere. apply climpl_done. apply FIN. assumption.
    - step. step. step. step. step.
      rewrite v_sltu_b2z. rewrite (unsigned_lit 255) by (clear; lia). rewrite (unsigned_lit k) by (clear - KR; lia).
      replace (255 <? k) with false by (symmetry; apply Z.ltb_ge; clear - KR; lia). cbn [Z.b2z].
      change (0 + - 0) with 0. rewrite (unsigned_lit 0) by (clear; lia). rewrite Z.lor_0_l.
      step. rewrite (t_sextw_small k) by (clear - KR; lia). do 5 step.
      release_frame FRz STz (bv_unsigned sp). step. step. chere. apply climpl_done. apply FIN. assumption. }
  (* [comment removed for export] *)
  Ltac trw H MUc WMc := eapply rw_cells_transport in H; [| exact MUc| exact WMc| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]].
  destruct (k_d K) as [pd|] eqn:KD.
  2: { (* [comment removed for export] *)
    destruct DOPT as (MAX0 & BMC & RPC). unfold readp_cells in RPC. change (0 - 0) with 0 in RPC. change (0 + 0) with 0 in RPC.
    destruct bs as [|b0 brest]; [cbn in LBS; lia|].
    cprefix. step. th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST. do 5 step. step. cstep.
    step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
    step. step. step. ubs_if.
    step. step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
    step. step. step. ubs_if. step. step. th_if_lit. step. step. th_if_lit. step. step. th_if_lit. step. step. th_if_lit. step. step. th_if_lit.
    step. step. ubs_if. step. step. ubs_if. step. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mc0 end.
    lazymatch goal with H : stk usegs mc0 lo _ |- _ => rename H into STc end. lazymatch goal with H : mem_inv usegs mc0 |- _ => rename H into MIc end.
    lazymatch goal with H : rw_cells usegs mc0 LB _ |- _ => rename H into BUFc end.
    destruct (rw_cells_CB_split_at usegs mc0 LB 256 (b0 :: brest) 1 ltac:(clear; lia) BUFc) as [B1 BR]. cbn [firstn skipn Nat.sub] in B1, BR. clear BUFc.
    apply (th_cells_congr usegs mc0 LB _ [C1 b0]) in B1; [| reflexivity| reflexivity| cbn; repeat split; exact I].
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp - 48); (BI + 48, BI + 52); (LB, LB + 1)]%Z mc0) as MUp. pose proof (wmono_refl usegs mc0) as WMp.
    eapply evt_cut.
    { eapply W1_gets_empty_proof with (lo := lo) (BI := BI) (BB := BB) (BM := BM) (RP := RP) (fl := fl) (size := 255) (OUT := LB);
        [reflexivity| reflexivity| reflexivity| exact BI0| exact LB00| clear; lia| eassumption| exact FLOK| eapply proj1; eassumption| exact BB0| clear - BBCe CW; lia
        | eapply proj1; eassumption| exact RP0| eapply proj1; eassumption| exact B1| exact BI8| exact BB8| exact RP8| rewrite unsigned_lit by lia; exact STc| clear - LO CEIL_RANGE__; unfold ceil_window in *; lia
        | rewrite unsigned_lit by lia; clear - SLO SPR; lia| clear - BIC LO; lia| clear - BBCe LO; lia| clear - RPCe LO; lia
        | unfold tbox; unfold hideP in A14, AL1; clear - A14 AL1 LBC LB00 LO SLO SPR; rewrite ?unsigned_lit by lia; lia| exact MIc]. }
    cbv beta. intros ms' PO. destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & fl' & mz & -> & MUc & WMc & MIz & STz & FLOK' & FLCz & B1z).
    rewrite !unsigned_lit in MUc by lia. rewrite unsigned_lit in STz by lia. th_ret_lit.
    lazymatch goal with H : rw_cells usegs mc0 (bv_unsigned sp + -48) _ |- _ => rename H into FRc end.
    lazymatch goal with H : rw_cells usegs mc0 BI _ |- _ => rename H into HEADc end.
    lazymatch goal with H : rw_cells usegs mc0 (BI + 40) _ |- _ => rename H into ISWc end.
    lazymatch goal with H : rw_cells usegs mc0 (BI + 52) _ |- _ => rename H into MIDCc end.
    lazymatch goal with H : rw_cells usegs mc0 (BI + 64) _ |- _ => rename H into PTRCc end.
    lazymatch goal with H : rw_cells usegs mc0 (BI + 72) _ |- _ => rename H into TAILc end.
    lazymatch goal with H : rw_cells usegs mc0 BB _ |- _ => rename H into BBCc end.
    lazymatch goal with H : rw_cells usegs mc0 BM _ |- _ => rename H into BMCc end.
    lazymatch goal with H : rw_cells usegs mc0 RP _ |- _ => rename H into RPCc end.
    lazymatch goal with H : munch _ m mc0 |- _ => rename H into MUq end. lazymatch goal with H : wmono usegs m mc0 |- _ => rename H into WMq end.
    trw FRc MUc WMc. 2: { clear - SPR BIC LBC LO SLO; lia. } trw HEADc MUc WMc. 2: { unfold hideP in AL1; clear - BIC LBC LO SLO SPR AL1; lia. }
    trw ISWc MUc WMc. 2: { unfold hideP in AL1; clear - BIC LBC LO SLO SPR AL1; lia. }
    trw MIDCc MUc WMc. 2: { unfold hideP in AL1; clear - BIC LBC LO SLO SPR AL1; lia. } trw PTRCc MUc WMc. 2: { unfold hideP in AL1; clear - BIC LBC LO SLO SPR AL1; lia. }
    trw TAILc MUc WMc. 2: { unfold hideP in AL1; clear - BIC LBC LO SLO SPR AL1; lia. }
    trw BBCc MUc WMc. 2: { unfold hideP in A12, AL2; clear - BIC BBCe LBC LO SLO SPR A12 AL2; lia. } trw BMCc MUc WMc. 2: { unfold hideP in A13, AL3; clear - BIC BMCe LBC LO SLO SPR A13 AL3; lia. }
    trw RPCc MUc WMc. 2: { unfold hideP in A14, AL4; clear - BIC RPCe LBC LO SLO SPR A14 AL4; lia. } trw BR MUc WMc. 2: { unfold hideP in AL1; clear - BIC LBC LO SLO SPR AL1; lia. }
    assert (MUz : munch [(bv_unsigned sp - 176, bv_unsigned sp); (BI + 48, BI + 52); (LB, LB + 256); (RP, RP + 24)]%Z m mz).
    { eapply munch_trans; [exact MUq|]. eapply munch_weaken; [| exact MUc]. unfold sub_fp. cbn [outside]. clear - SPR. intros a Ha. lia. }
    pose proof (wmono_trans _ _ _ _ WMq WMc) as WMz. clear MUq WMq MUc WMc MUp WMp STc MIc.
    (* [comment removed for export] *)
    step. step. th_if_lit. step. step. th_if_lit. step. step. th_if_lit.
    chere. eapply (EXIT mz 0 off fl' (Z_to_bv 8 0 :: brest)); try eassumption.
    - left. clear - LENM MAX0 OFF. lia.
    - exists rmaxw. split; [exact OWNbb|]. split; [exact BBCc|]. split; [exact OWNbm|]. split; [exact OWNrp|]. split; [exact OFF|]. split; [exact LENM|]. split; [exact MAX31|].
      rewrite KD. split; [exact MAX0|]. unfold readp_cells. change (0 - 0) with 0. change (0 + 0) with 0. split; [exact BMCc| exact RPCc].
    - apply (th_cells_congr usegs mz LB _ [CB 1 [Z_to_bv 8 0]]) in B1z; [| reflexivity| reflexivity| cbn; repeat split; reflexivity].
      pose proof (rw_cells_CB_join usegs mz LB 1 [Z_to_bv 8 0] 255 brest B1z BR) as J. exact J. }
  (* [comment removed for export] *)
  destruct DOPT as (D & nm & junk & OWNd & MAXP & BMC & RPC & LJ & DC). unfold readp_cells in RPC.
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNd)) as (D0 & _ & _ & DCe & DIMG). hide DIMG.
  assert (NDd : k_bi K <> pd /\ k_bb K <> pd /\ k_bm K <> pd /\ k_rp K <> pd).
  { clear - NDK0 KD. unfold mbio_blocks in NDK0. rewrite KD in NDK0. cbn [app] in NDK0.
    inversion NDK0 as [|x1 l1 N1 ND1]; subst. inversion ND1 as [|x2 l2 N2 ND2]; subst. inversion ND2 as [|x3 l3 N3 ND3]; subst. inversion ND3 as [|x4 l4 N4 ND4]; subst.
    cbn [In] in N1, N2, N3, N4. repeat split; intros E; rewrite E in *; tauto. }
  destruct NDd as (N15 & N25 & N35 & N45).
  assert (NL5 : pl <> pd) by (intros E; apply NTL; unfold mbio_T; rewrite KD, E; do 4 right; reflexivity).
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNB) (proj1 OWNd) N15) as A15.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNbb) (proj1 OWNd) N25) as A25.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNbm) (proj1 OWNd) N35) as A35.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNrp) (proj1 OWNd) N45) as A45.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNL) (proj1 OWNd) NL5) as AL5.
  hide N15. hide N25. hide N35. hide N45. hide NL5. hide A15. hide A25. hide A35. hide A45. hide AL5.
  cprefix. step. th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST. do 5 step. step. cstep.
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
  step. step. step. ubs_if.
  step. step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
  step. step. step. ubs_if. step. step. th_if_lit. step. step. th_if_lit. step. step. th_if_lit. step. step. th_if_lit. step. step. th_if_lit.
  step. step. ubs_if. step. step. ubs_if. step. step. step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mc0 end.
  lazymatch goal with H : stk usegs mc0 lo _ |- _ => rename H into STc end. lazymatch goal with H : mem_inv usegs mc0 |- _ => rename H into MIc end.
  lazymatch goal with H : rw_cells usegs mc0 LB _ |- _ => rename H into BUFc end.
  lazymatch goal with H : rw_cells usegs mc0 D _ |- _ => rename H into DCc end.
  lazymatch goal with H : rw_cells usegs mc0 RP _ |- _ => rename H into RPC0 end.
  lazymatch goal with H : munch _ m mc0 |- _ => rename H into MUq end. lazymatch goal with H : wmono usegs m mc0 |- _ => rename H into WMq end.
  destruct (Z.eq_dec off len) as [EQ|NE].
  - (* [comment removed for export] *)
    destruct bs as [|b0 brest]; [cbn in LBS; lia|].
    destruct (rw_cells_CB_split_at usegs mc0 LB 256 (b0 :: brest) 1 ltac:(clear; lia) BUFc) as [B1 BR]. cbn [firstn skipn Nat.sub] in B1, BR. clear BUFc.
    apply (th_cells_congr usegs mc0 LB _ [C1 b0]) in B1; [| reflexivity| reflexivity| cbn; repeat split; exact I].
    unfold readp_cells in RPC0. replace (len - off) with 0 in RPC0 by (clear - EQ; lia).
    eapply evt_cut.
    { eapply W1_gets_empty_proof with (lo := lo) (BI := BI) (BB := BB) (BM := BM) (RP := RP) (fl := fl) (size := 255) (OUT := LB);
        [reflexivity| reflexivity| reflexivity| exact BI0| exact LB00| clear; lia| eassumption| exact FLOK| eapply proj1; eassumption| exact BB0| clear - BBCe CW; lia
        | eapply proj1; eassumption| exact RP0| eapply proj1; exact RPC0| exact B1| exact BI8| exact BB8| exact RP8| rewrite unsigned_lit by lia; exact STc| clear - LO CEIL_RANGE__; unfold ceil_window in *; lia
        | rewrite unsigned_lit by lia; clear - SLO SPR; lia| clear - BIC LO; lia| clear - BBCe LO; lia| clear - RPCe LO; lia
        | unfold tbox; unfold hideP in A14, AL1; clear - A14 AL1 LBC LB00 LO SLO SPR; rewrite ?unsigned_lit by lia; lia| exact MIc]. }
    cbv beta. intros ms' PO. destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & fl' & mz & -> & MUc & WMc & MIz & STz & FLOK' & FLCz & B1z).
    rewrite !unsigned_lit in MUc by lia. rewrite unsigned_lit in STz by lia. th_ret_lit.
    lazymatch goal with H : rw_cells usegs mc0 (bv_unsigned sp + -48) _ |- _ => rename H into FRc end.
    lazymatch goal with H : rw_cells usegs mc0 BI _ |- _ => rename H into HEADc end.
    lazymatch goal with H : rw_cells usegs mc0 (BI + 40) _ |- _ => rename H into ISWc end.
    lazymatch goal with H : rw_cells usegs mc0 (BI + 52) _ |- _ => rename H into MIDCc end.
    lazymatch goal with H : rw_cells usegs mc0 (BI + 64) _ |- _ => rename H into PTRCc end.
    lazymatch goal with H : rw_cells usegs mc0 (BI + 72) _ |- _ => rename H into TAILc end.
    lazymatch goal with H : rw_cells usegs mc0 BB _ |- _ => rename H into BBCc end.
    lazymatch goal with H : rw_cells usegs mc0 BM _ |- _ => rename H into BMCc end.
    trw FRc MUc WMc. 2: { clear - SPR BIC LBC LO SLO; lia. } trw HEADc MUc WMc. 2: { unfold hideP in AL1; clear - BIC LBC LO SLO SPR AL1; lia. }
    trw ISWc MUc WMc. 2: { unfold hideP in AL1; clear - BIC LBC LO SLO SPR AL1; lia. }
    trw MIDCc MUc WMc. 2: { unfold hideP in AL1; clear - BIC LBC LO SLO SPR AL1; lia. } trw PTRCc MUc WMc. 2: { unfold hideP in AL1; clear - BIC LBC LO SLO SPR AL1; lia. }
    trw TAILc MUc WMc. 2: { unfold hideP in AL1; clear - BIC LBC LO SLO SPR AL1; lia. }
    trw BBCc MUc WMc. 2: { unfold hideP in A12, AL2; clear - BIC BBCe LBC LO SLO SPR A12 AL2; lia. } trw BMCc MUc WMc. 2: { unfold hideP in A13, AL3; clear - BIC BMCe LBC LO SLO SPR A13 AL3; lia. }
    trw RPC0 MUc WMc. 2: { unfold hideP in A14, AL4; clear - BIC RPCe LBC LO SLO SPR A14 AL4; lia. } trw BR MUc WMc. 2: { unfold hideP in AL1; clear - BIC LBC LO SLO SPR AL1; lia. }
    trw DCc MUc WMc. 2: { unfold hideP in A15, AL5; clear - BIC DCe LBC LO SLO SPR A15 AL5 LENM OFF; rewrite ?Z2Nat.id by lia; lia. }
    assert (MUz : munch [(bv_unsigned sp - 176, bv_unsigned sp); (BI + 48, BI + 52); (LB, LB + 256); (RP, RP + 24)]%Z m mz).
    { eapply munch_trans; [exact MUq|]. eapply munch_weaken; [| exact MUc]. unfold sub_fp. cbn [outside]. clear - SPR. intros a Ha. lia. }
    pose proof (wmono_trans _ _ _ _ WMq WMc) as WMz. clear MUq WMq MUc WMc STc MIc.
    step. step. th_if_lit. step. step. th_if_lit. step. step. th_if_lit.
    chere. eapply (EXIT mz 0 off fl' (Z_to_bv 8 0 :: brest)); try eassumption.
    + left. clear - EQ. lia.
    + exists rmaxw. split; [exact OWNbb|]. split; [exact BBCc|]. split; [exact OWNbm|]. split; [exact OWNrp|]. split; [exact OFF|]. split; [exact LENM|]. split; [exact MAX31|].
      rewrite KD. exists D, nm, junk. split; [exact OWNd|]. split; [exact MAXP|]. split; [exact BMCc|].
      split; [unfold readp_cells; replace (len - off) with 0 by (clear - EQ; lia); exact RPC0|]. split; [exact LJ| exact DCc].
    + apply (th_cells_congr usegs mz LB _ [CB 1 [Z_to_bv 8 0]]) in B1z; [| reflexivity| reflexivity| cbn; repeat split; reflexivity].
      exact (rw_cells_CB_join usegs mz LB 1 [Z_to_bv 8 0] 255 brest B1z BR).
  - (* [comment removed for export] *)
    destruct (rw_cells_CB_split_at usegs mc0 LB 256 bs 255 ltac:(clear; lia) BUFc) as [BA BZ]. change (256 - 255)%nat with 1%nat in BZ. clear BUFc.
    eapply evt_cut.
    { eapply W1_gets_data_proof with (lo := lo) (BI := BI) (BB := BB) (BM := BM) (RP := RP) (D := D) (len := len) (max := max) (off := off) (fl := fl) (size := 255) (OUT := LB)
                                   (rmaxw := rmaxw) (flw := wz (msec meth)) (junk := junk) (ojunk := firstn 255 bs);
        [reflexivity| reflexivity| reflexivity| exact BI0| exact LB00| clear; lia| eassumption| exact FLOK| eapply proj1; eassumption| exact BB0| clear - BBCe CW; lia
        | eapply proj1; eassumption| exact RP0| exact RPC0| exact D0| clear - OFF; lia| clear - OFF NE; lia| exact LENM| exact MAX31| clear - DCe CW; lia
        | exact LJ| exact DCc| rewrite firstn_length, LBS; clear; lia| exact BA| exact BI8| exact BB8| exact RP8
        | rewrite unsigned_lit by lia; exact STc| clear - LO CEIL_RANGE__; unfold ceil_window in *; lia| rewrite unsigned_lit by lia; clear - SLO SPR; lia
        | clear - BIC LO; lia| clear - BBCe LO; lia| clear - RPCe LO; lia| clear - DCe LO; lia
        | unfold hideP in A45; clear - A45; lia| unfold hideP in AL5; clear - AL5; lia| unfold hideP in AL4; clear - AL4; lia
        | unfold tbox; unfold hideP in AL1, A15, A14, A12, AL2, A24; clear - AL1 A15 A14 A12 AL2 A24 LBC LB00 LO SLO SPR; rewrite ?unsigned_lit by lia; repeat split; lia
        | exact MIc]. }
    cbv beta. intros ms' PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & rmaxw' & fl' & k & ojunk' & mz & -> & HK & MUc & WMc & MIz & STz & FLOK' & FLCz & RPCz & LOJ & NULk & OUTz).
    unfold readp_cells in RPCz. rewrite !unsigned_lit in MUc by lia. rewrite unsigned_lit in STz by lia. th_ret_lit.
    lazymatch goal with H : rw_cells usegs mc0 (bv_unsigned sp + -48) _ |- _ => rename H into FRc end.
    lazymatch goal with H : rw_cells usegs mc0 BI _ |- _ => rename H into HEADc end.
    lazymatch goal with H : rw_cells usegs mc0 (BI + 40) _ |- _ => rename H into ISWc end.
    lazymatch goal with H : rw_cells usegs mc0 (BI + 52) _ |- _ => rename H into MIDCc end.
    lazymatch goal with H : rw_cells usegs mc0 (BI + 64) _ |- _ => rename H into PTRCc end.
    lazymatch goal with H : rw_cells usegs mc0 (BI + 72) _ |- _ => rename H into TAILc end.
    lazymatch goal with H : rw_cells usegs mc0 BB _ |- _ => rename H into BBCc end.
    lazymatch goal with H : rw_cells usegs mc0 BM _ |- _ => rename H into BMCc end.
    trw FRc MUc WMc. 2: { unfold hideP in A14; clear - SPR BIC RPCe LBC LO SLO; lia. } trw HEADc MUc WMc. 2: { unfold hideP in AL1, A14; clear - BIC RPCe LBC LO SLO SPR AL1 A14; lia. }
    trw ISWc MUc WMc. 2: { unfold hideP in AL1, A14; clear - BIC RPCe LBC LO SLO SPR AL1 A14; lia. }
    trw MIDCc MUc WMc. 2: { unfold hideP in AL1, A14; clear - BIC RPCe LBC LO SLO SPR AL1 A14; lia. } trw PTRCc MUc WMc. 2: { unfold hideP in AL1, A14; clear - BIC RPCe LBC LO SLO SPR AL1 A14; lia. }
    trw TAILc MUc WMc. 2: { unfold hideP in AL1, A14; clear - BIC RPCe LBC LO SLO SPR AL1 A14; lia. }
    trw BBCc MUc WMc. 2: { unfold hideP in A12, AL2, A24; clear - BIC BBCe RPCe LBC LO SLO SPR A12 AL2 A24; lia. }
    trw BMCc MUc WMc. 2: { unfold hideP in A13, AL3, A34; clear - BIC BMCe RPCe LBC LO SLO SPR A13 AL3 A34; lia. }
    trw BZ MUc WMc. 2: { unfold hideP in AL1, AL4; clear - BIC RPCe LBC LO SLO SPR AL1 AL4; lia. }
    trw DCc MUc WMc. 2: { unfold hideP in A15, AL5, A45; clear - BIC DCe RPCe LBC LO SLO SPR A15 AL5 A45 LENM OFF; rewrite ?Z2Nat.id by lia; lia. }
    assert (MUz : munch [(bv_unsigned sp - 176, bv_unsigned sp); (BI + 48, BI + 52); (LB, LB + 256); (RP, RP + 24)]%Z m mz).
    { eapply munch_trans; [exact MUq|]. eapply munch_weaken; [| exact MUc]. unfold sub_fp. cbn [outside]. clear - SPR. intros a Ha. lia. }
    pose proof (wmono_trans _ _ _ _ WMq WMc) as WMz. clear MUq WMq MUc WMc STc MIc.
    assert (KR : 1 <= k <= 254) by (clear - HK; lia).
    step. step. if_cases KP; zify_cond KP. { exfalso. clear - KP KR. rewrite ?unsigned_lit in KP by lia. lia. }
    cstep. step. step. step. th_if_lit. step. step. th_if_lit.
    chere. lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => epose proof (EXIT mc k (off + k) fl' (ojunk' ++ skipn 255 bs)) as EX end.
    rewrite (Z.min_r k 1) in EX by (clear - KR; lia). eapply EX; clear EX; try eassumption.
    + right. split; [clear - HK; lia|]. split; [reflexivity|]. rewrite nth_error_app1 by (rewrite LOJ; clear - KR; lia). exact NULk.
    + exists rmaxw'. split; [exact OWNbb|]. split; [exact BBCc|]. split; [exact OWNbm|]. split; [exact OWNrp|]. split; [clear - HK OFF; lia|]. split; [exact LENM|]. split; [exact MAX31|].
      rewrite KD. exists D, nm, junk. split; [exact OWNd|]. split; [exact MAXP|]. split; [exact BMCc|]. split; [exact RPCz|]. split; [exact LJ| exact DCc].
    + rewrite length_app, skipn_length, LOJ, LBS. reflexivity.
    + lazymatch goal with |- rw_cells _ ?mc _ _ => exact (rw_cells_CB_join usegs mc LB 255 ojunk' 1 (skipn 255 bs) OUTz BZ) end.
Qed.
End WithCeiling0.
