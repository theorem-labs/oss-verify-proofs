(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge Mem Cells Step Frame SysStep.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF Shadow StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AU_consts AU_iface AU_kit AU_parts_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg SegLib SegBridge.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs PIosKit PIosKitA.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AHMB.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Entry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2B Require Import APS2_iface A2Lib PA2_kz PA2_exit PA2_xlib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2B Require PA2_t0nf.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegB2N Require B2N_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Import ITree.Exc.
Open Scope Z_scope.
Local Notation u := bv_unsigned.
Local Notation M64 := 18446744073709551616.
Local Notation SH := 2147450880%Z (only parsing).

Section CANSEC. Context {rc : runConstT}.

Section XD2.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Hypothesis ODAW : opdelete_arr_wild_stmtA AI.
  Variables (L : alayout) (RNG4 : footprint) (ra sp gp tp s0 : word) (m m5 : amem) (s' : APS) (LB : list ablock) (lo : Z) (tr0 : list Z)
            (F COPY n SPAX : Z) (p : AsanCtrl.aptr) (E5 : env) (R5 FR5 : bvmap 5 word) (fc5 : bv 32).
  Variables (SP16 PB : Z) (ZL4 : list Z).
  Local Notation LB4 := (HB p COPY n :: mkABlock (ABFake 5) F 2048 :: LB).
  (* [comment removed for export] *)
  Hypothesis E_SP : u sp = 16 * SP16.
  Hypothesis E_PB : u sp - 416 - SPAX = 16 * PB.
  Hypothesis HSPA : 416 <= u sp - SPAX <= 447.
  Hypothesis HSPA32 : SPAX mod 32 = 0.
  Hypothesis Z_SP : nth 1 ZL4 0 = SP16.
  Hypothesis Z_GP : nth 2 ZL4 0 = u gp.
  Hypothesis Z_TP : nth 3 ZL4 0 = u tp.
  Hypothesis Z_PB : nth 29 ZL4 0 = PB.
  Hypothesis Z_RA : nth 0 ZL4 0 = u ra.
  Hypothesis Z_S0 : nth 4 ZL4 0 = u s0.
  Hypothesis Z_CP : 8 * nth 36 ZL4 0 = COPY.
  Hypothesis HCOPY : 0x671000 <= COPY < 2^47.
  (* [comment removed for export] *)
  Hypothesis HUC : uchain m (al_top L) AFREE_PC (u sp) (u s0) (Nat.pred UDEPTH) tr0.
  Hypothesis Htr0 : (length tr0 <= 27)%nat.
  Hypothesis HS0 : u s0 < u sp \/ u sp + 16 <= u s0.
  Hypothesis Hra1 : 4096 <= u ra.
  Hypothesis Hra2 : u ra <> AFREE_PC.
  Hypothesis Hsp16 : u sp mod 16 = 0.
  Hypothesis Hsptop : u sp + 16 < al_top L.
  Hypothesis HTP : tp = Z_to_bv 64 ATP.
  Hypothesis Hlo1 : ATOP + 4096 <= lo.
  Hypothesis Hlo2 : lo <= u sp - 8640.
  Hypothesis HRS4 : rng RNG4 lo (al_top L - lo).
  Hypothesis HAOK' : aps_ok L s'.
  Hypothesis HDK' : dk (aps_m s') < DWMAX.
  (* [comment removed for export] *)
  Hypothesis Hg5 : SP.gagree 47 (mkEZ ZL4) E5.
  Hypothesis Hb5 : eb E5 = eb (mkEZ ZL4).
  Hypothesis HF5 : rfull R5.
  Hypothesis HR5 : regs_ok E5 B2N_defs.XDELB_regs R5.
  Hypothesis HK5 : know_ok bsegs E5 m5 B2N_defs.XDELB_kn.
  Hypothesis HH5 : AHMB.hmH AI L RNG4 (aps_m s') LB4 m5.
  Hypothesis STK5 : stk bsegs m5 lo (u sp).
  Hypothesis HABV : forall a, u sp <= a < al_top L -> m5 (wa a) = m (wa a).
  (* [comment removed for export] *)
  Variable Q : unit -> APS -> footprint -> machine_state -> Prop.
  Local Notation XR k := (edenot E5 (sr_get B2N_defs.XDELB_regs k)) (only parsing).
  Hypothesis CONT : forall s'' RNG'' ms6, aps_rest s'' = aps_rest s' ->
    afree_post CI (AHEAP AI) L RNG4 (Z_to_bv 64 0xa0f08) (Z_to_bv 64 SPAX) gp tp sp (Z_to_bv 64 SPAX)
      (XR 18) (XR 19) (XR 20) (XR 21) (XR 22) (XR 23) (XR 24) (XR 25) (XR 26) (XR 27) FR5 fc5 (aps_m s') LB4 p lo m5 (aps_m s'') RNG'' ms6 ->
    evtF bsegs RNG'' (Q tt s'' RNG'') ms6.

  Lemma u_rngD : forall (w : word), 0 <= u w < M64.
  Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. exact H. Qed.

  Ltac ezx e := rewrite <- (SP.edenot_gagree 47 (mkEZ ZL4) E5 e Hg5 (eq_sym Hb5) eq_refl), zden_ok by reflexivity; cbn [zden].

  Lemma xdel2_call : implMA RNG4 (HarnessP.opdelete afree_M p) s' Q (MS R5 FR5 (Z_to_bv 64 0xa0f04) fc5 None m5 (seg_rom bsegs)).
  Proof using All.
    pose proof (u_rngD sp) as Rsp. atop_facts.
    assert (ESPA : edenot E5 (sr_get B2N_defs.XDELB_regs 2) = Z_to_bv 64 SPAX).
    { change (sr_get B2N_defs.XDELB_regs 2) with (EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 1)) (ELit (-416))) (EMd M_MUL (ELit 16) (EVar 29))).
      ezx (EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 1)) (ELit (-416))) (EMd M_MUL (ELit 16) (EVar 29))).
      rewrite Z_SP, Z_PB. f_equal. lia. }
    assert (EGP : edenot E5 (sr_get B2N_defs.XDELB_regs 3) = gp).
    { change (sr_get B2N_defs.XDELB_regs 3) with (EVar 2). ezx (EVar 2). rewrite Z_GP. apply Z_to_bv_bv_unsigned. }
    assert (ETP : edenot E5 (sr_get B2N_defs.XDELB_regs 4) = tp).
    { change (sr_get B2N_defs.XDELB_regs 4) with (EVar 3). ezx (EVar 3). rewrite Z_TP. apply Z_to_bv_bv_unsigned. }
    assert (ES0 : edenot E5 (sr_get B2N_defs.XDELB_regs 8) = sp).
    { change (sr_get B2N_defs.XDELB_regs 8) with (EMd M_MUL (ELit 16) (EVar 1)). ezx (EMd M_MUL (ELit 16) (EVar 1)).
      rewrite Z_SP, <- E_SP. apply Z_to_bv_bv_unsigned. }
    assert (ES1 : edenot E5 (sr_get B2N_defs.XDELB_regs 9) = Z_to_bv 64 SPAX).
    { change (sr_get B2N_defs.XDELB_regs 9) with (EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 1)) (ELit (-416))) (EMd M_MUL (ELit 16) (EVar 29))).
      ezx (EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 1)) (ELit (-416))) (EMd M_MUL (ELit 16) (EVar 29))).
      rewrite Z_SP, Z_PB. f_equal. lia. }
    assert (EA0 : edenot E5 (sr_get B2N_defs.XDELB_regs 10) = Z_to_bv 64 COPY).
    { change (sr_get B2N_defs.XDELB_regs 10) with (EMd M_MUL (ELit 8) (EVar 36)). ezx (EMd M_MUL (ELit 8) (EVar 36)). rewrite Z_CP. reflexivity. }
    (* [comment removed for export] *)
    assert (BS0 : bytes_at bsegs m5 (u sp - 16) (le8 (Z_to_bv 64 (u s0)))).
    { assert (K : kentry_ok bsegs E5 m5 (KWord (SA B2N_defs.vSP (-16)) 8 B2N_defs.vS0))
        by (apply (proj1 (Forall_forall _ _) HK5); cbv [B2N_defs.XDELB_kn]; repeat (first [left; reflexivity | right])).
      pose proof (kx_word_g bsegs 47 ZL4 E5 m5 B2N_defs.vSP (-16) 8 B2N_defs.vS0 Hg5 (eq_sym Hb5) eq_refl eq_refl eq_refl K) as B.
      cbv [B2N_defs.vSP B2N_defs.vSP16 B2N_defs.vS0 B2N_defs.V B2N_defs.mul] in B. cbn [zden] in B. rewrite Z_SP, Z_S0 in B.
      rewrite <- E_SP, Z.mod_small in B by exact Rsp. unfold le8. replace (u sp - 16) with (u sp + -16) by lia. exact B. }
    assert (BRA : bytes_at bsegs m5 (u sp - 8) (le8 (Z_to_bv 64 (u ra)))).
    { assert (K : kentry_ok bsegs E5 m5 (KWord (SA B2N_defs.vSP (-8)) 8 B2N_defs.vRA))
        by (apply (proj1 (Forall_forall _ _) HK5); cbv [B2N_defs.XDELB_kn]; repeat (first [left; reflexivity | right])).
      pose proof (kx_word_g bsegs 47 ZL4 E5 m5 B2N_defs.vSP (-8) 8 B2N_defs.vRA Hg5 (eq_sym Hb5) eq_refl eq_refl eq_refl K) as B.
      cbv [B2N_defs.vSP B2N_defs.vSP16 B2N_defs.vRA B2N_defs.V B2N_defs.mul] in B. cbn [zden] in B. rewrite Z_SP, Z_RA in B.
      rewrite <- E_SP, Z.mod_small in B by exact Rsp. unfold le8. replace (u sp - 8) with (u sp + -8) by lia. exact B. }
    pose proof (u_rngD s0) as Rs0. pose proof (u_rngD ra) as Rra.
    assert (HUC5 : uchain m5 (al_top L) AFREE_PC SPAX (u sp) UDEPTH (u ra :: tr0)).
    { apply (stage2_uchain m m5 (al_top L) AFREE_PC (u sp) (u s0) (u ra) SPAX tr0 HUC HS0 HABV); try lia; try assumption;
        clear - Hsp16; Z.div_mod_to_equations; lia. }
    (* [comment removed for export] *)
    rewrite (regs_ok_canon E5 _ R5 HF5 HR5).
    rewrite ESPA, EGP, ETP, ES0, ES1, EA0.
    set (r1 := edenot E5 (sr_get B2N_defs.XDELB_regs 1)).
    set (r5 := edenot E5 (sr_get B2N_defs.XDELB_regs 5)). set (r6 := edenot E5 (sr_get B2N_defs.XDELB_regs 6)).
    set (r7 := edenot E5 (sr_get B2N_defs.XDELB_regs 7)).
    set (r11 := edenot E5 (sr_get B2N_defs.XDELB_regs 11)). set (r12 := edenot E5 (sr_get B2N_defs.XDELB_regs 12)).
    set (r13 := edenot E5 (sr_get B2N_defs.XDELB_regs 13)). set (r14 := edenot E5 (sr_get B2N_defs.XDELB_regs 14)).
    set (r15 := edenot E5 (sr_get B2N_defs.XDELB_regs 15)). set (r16 := edenot E5 (sr_get B2N_defs.XDELB_regs 16)).
    set (r17 := edenot E5 (sr_get B2N_defs.XDELB_regs 17)).
    set (r28 := edenot E5 (sr_get B2N_defs.XDELB_regs 28)). set (r29 := edenot E5 (sr_get B2N_defs.XDELB_regs 29)).
    set (r30 := edenot E5 (sr_get B2N_defs.XDELB_regs 30)). set (r31 := edenot E5 (sr_get B2N_defs.XDELB_regs 31)).
    clearbody r1 r5 r6 r7 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31.
    eapply (implMA_evtF RNG4 _ s' _ (fun ms' => ms' = MS (mkR (Z_to_bv 64 0xa0f08) (Z_to_bv 64 SPAX) gp tp r5 r6 r7 sp (Z_to_bv 64 SPAX) (Z_to_bv 64 COPY)
      r11 r12 r13 r14 r15 r16 r17 (XR 18) (XR 19) (XR 20) (XR 21) (XR 22) (XR 23) (XR 24) (XR 25) (XR 26) (XR 27) r28 r29 r30 r31)
      FR5 (Z_to_bv 64 AOPDEL_ARR) fc5 None m5 (seg_rom bsegs))).
    { zstep. apply evtF_done. reflexivity. }
    intros ms' ->.
    eapply (implMA_post_evtF RNG4 _ s' Q (fun _ s'' RNG'' ms6 => aps_rest s'' = aps_rest s' /\
      afree_post CI (AHEAP AI) L RNG4 (Z_to_bv 64 0xa0f08) (Z_to_bv 64 SPAX) gp tp sp (Z_to_bv 64 SPAX)
        (XR 18) (XR 19) (XR 20) (XR 21) (XR 22) (XR 23) (XR 24) (XR 25) (XR 26) (XR 27) FR5 fc5 (aps_m s') LB4 p lo m5 (aps_m s'') RNG'' ms6));
      [| intros [] s'' RNG'' ms6 [HA HP]; exact (CONT s'' RNG'' ms6 HA HP)].
    destruct HH5 as [AH5 MI5].
    destruct (stk_split bsegs m5 lo SPAX (u sp) STK5 ltac:(lia)) as [STKa _].
    eapply (ODAW L RNG4 (Z_to_bv 64 0xa0f08) (Z_to_bv 64 SPAX) gp tp r5 r6 r7 sp (Z_to_bv 64 SPAX) (Z_to_bv 64 COPY)
              r11 r12 r13 r14 r15 r16 r17 (XR 18) (XR 19) (XR 20) (XR 21) (XR 22) (XR 23) (XR 24) (XR 25) (XR 26) (XR 27) r28 r29 r30 r31
              FR5 fc5 m5 s' LB4 p COPY n lo (u ra :: tr0));
      rewrite ?unsigned_lit by lia;
      [ exact AH5 | left; reflexivity | exact MI5 | exact STKa | exact Hlo1 | unfold AFREE_STACK; lia | lia | exact HTP | reflexivity
      | exact HUC5 | exact HDK' | lia | lia | unfold AFREE_PC; lia | cbn [length]; lia | clear - HSPA32; Z.div_mod_to_equations; lia
      | exact HRS4 | exact HAOK' ].
  Qed.
End XD2.
End CANSEC.
