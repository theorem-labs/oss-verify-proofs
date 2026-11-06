(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MState Mem Cells Step Frame.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF Shadow StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AU_kit AU_iface AU_fuzz_kit AU_steptac.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs PIosKit PIosKitA.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg SegLib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Entry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2B Require Import PA2_kz APS2_iface A2Lib PA2_t0f.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegB2 Require B2F_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Import ITree.Exc.
Open Scope Z_scope.
Local Notation u := bv_unsigned.

Section CANSEC. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma a2f_xret_regs : forall (ZL : list Z) (E' : env) (R' : bvmap 5 word),
  SP.gagree 35 (mkEZ ZL) E' -> eb (mkEZ ZL) = eb E' -> rfull R' -> regs_ok E' (ST.t_regs B2F_defs.XRET) R' ->
  exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    R' = mkR (Z_to_bv 64 (nth 0 ZL 0)) (Z_to_bv 64 (16 * nth 1 ZL 0)) (Z_to_bv 64 (nth 2 ZL 0)) (Z_to_bv 64 (nth 3 ZL 0)) x5 x6 x7
             (Z_to_bv 64 (nth 4 ZL 0)) (Z_to_bv 64 (nth 5 ZL 0)) (edenot E' (EVar 35)) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (nth 6 ZL 0)) (Z_to_bv 64 (nth 7 ZL 0)) (Z_to_bv 64 (nth 8 ZL 0)) (Z_to_bv 64 (nth 9 ZL 0))
             (Z_to_bv 64 (nth 10 ZL 0)) (Z_to_bv 64 (nth 11 ZL 0)) (Z_to_bv 64 (nth 12 ZL 0)) (Z_to_bv 64 (nth 13 ZL 0))
             (Z_to_bv 64 (nth 14 ZL 0)) (Z_to_bv 64 (nth 15 ZL 0)) x28 x29 x30 x31.
Proof.
  intros ZL E' R' Hg Hb HF HR.
  rewrite (regs_ok_canon E' _ R' HF HR).
  assert (EV : forall k, (k < 35)%nat -> edenot E' (EVar k) = Z_to_bv 64 (nth k ZL 0)).
  { intros k Hk. rewrite <- (SP.edenot_gagree 35 _ _ (EVar k) Hg Hb ltac:(cbn; apply Nat.leb_le; lia)). reflexivity. }
  assert (ESP : edenot E' (EMd M_MUL (ELit 16) (EVar 1)) = Z_to_bv 64 (16 * nth 1 ZL 0)).
  { rewrite <- (SP.edenot_gagree 35 _ _ (EMd M_MUL (ELit 16) (EVar 1)) Hg Hb eq_refl), zden_ok by reflexivity. reflexivity. }
  change (sr_get (ST.t_regs B2F_defs.XRET) 1) with (EVar 0);
  change (sr_get (ST.t_regs B2F_defs.XRET) 2) with (EMd M_MUL (ELit 16) (EVar 1));
  change (sr_get (ST.t_regs B2F_defs.XRET) 3) with (EVar 2); change (sr_get (ST.t_regs B2F_defs.XRET) 4) with (EVar 3);
  change (sr_get (ST.t_regs B2F_defs.XRET) 8) with (EVar 4); change (sr_get (ST.t_regs B2F_defs.XRET) 9) with (EVar 5);
  change (sr_get (ST.t_regs B2F_defs.XRET) 10) with (EVar 35);
  change (sr_get (ST.t_regs B2F_defs.XRET) 18) with (EVar 6); change (sr_get (ST.t_regs B2F_defs.XRET) 19) with (EVar 7);
  change (sr_get (ST.t_regs B2F_defs.XRET) 20) with (EVar 8); change (sr_get (ST.t_regs B2F_defs.XRET) 21) with (EVar 9);
  change (sr_get (ST.t_regs B2F_defs.XRET) 22) with (EVar 10); change (sr_get (ST.t_regs B2F_defs.XRET) 23) with (EVar 11);
  change (sr_get (ST.t_regs B2F_defs.XRET) 24) with (EVar 12); change (sr_get (ST.t_regs B2F_defs.XRET) 25) with (EVar 13);
  change (sr_get (ST.t_regs B2F_defs.XRET) 26) with (EVar 14); change (sr_get (ST.t_regs B2F_defs.XRET) 27) with (EVar 15).
  set (a0v := edenot E' (EVar 35)).
  rewrite ESP. rewrite !EV by lia. do 14 eexists. reflexivity.
Qed.


Lemma u_rngT : forall (w : word), 0 <= u w < 18446744073709551616.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. exact H. Qed.
Lemma ez_wt : forall ZL e (w : word), zok e = true -> zden ZL e mod 18446744073709551616 = u w -> edenot (mkEZ ZL) e = w.
Proof.
  intros ZL e w Hz H. rewrite zden_ok by exact Hz. apply bv_eq. rewrite u_Z_to_bv. exact H.
Qed.

Section TAIL.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Hypothesis SF5 : stack_free_5_stmt AI fflag.
  Variables (L : alayout) (RNG RNG3 : footprint) (s s3 : APS) (LB : list ablock) (m0 m3 : amem) (lo : Z) (W : list (Z * Z))
            (F SPA RC : Z) (ra sp gp tp s0 s1 s2 s3' s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
            (F3 : bvmap 5 word) (fc3 : bv 32).
  Hypothesis AH3 : AHEAP AI L RNG3 (aps_m s3) (mkABlock (ABFake 5) F 2048 :: LB) m3.
  Hypothesis MI3 : mem_inv bsegs m3.
  Hypothesis STK3 : stk bsegs m3 lo (u sp).
  Hypothesis Hlo1 : ATOP + 4096 <= lo.
  Hypothesis Hlo2 : lo <= u sp - 8640.
  Hypothesis Hsp16 : u sp mod 16 = 0.
  Hypothesis Hsp47 : u sp <= 2^47.
  Hypothesis HSPA : 416 <= u sp - SPA <= 447.
  Hypothesis HSPA32 : SPA mod 32 = 0.
  Hypothesis HFL : rw_cells bsegs m3 (F + 2040) [C8 (Z_to_bv 64 (fflag L 5 F))].
  Hypothesis SAVED3 : forall k, 0 <= k < 13 ->
    bytes_at bsegs m3 (u sp - 8 - 8 * k) (word_to_le_bytes 8 (Z_to_bv 64 (nth (Z.to_nat k) [u ra; u s0; u s1; u s2; u s3'; u s4; u s5; u s6; u s7; u s8; u s9; u s10; u s11] 0))).
  Hypothesis HRC : 0 <= RC <= 63.
  Hypothesis HRCM : bytes_at bsegs m3 (SPA + 272) (word_to_le_bytes 8 (Z_to_bv 64 RC)).   (* [comment removed for export] *)
  Hypothesis RNGS : rng RNG3 lo (u sp - lo).
  Hypothesis PW3 : aheap_pres_W CI LB (u sp) W m0 m3.
  Hypothesis FPL : fp_le RNG RNG3.
  Hypothesis APS : aps_rest s3 = aps_rest s.
  Hypothesis HZ3 : frm0 fc3.

  Lemma xsf_tail :
    evtF bsegs RNG3 (s2_postA AI L RNG ra sp gp tp s0 s1 s2 s3' s4 s5 s6 s7 s8 s9 s10 s11 s LB lo W m0 tt s3 RNG3)
      (MS (mkR (Z_to_bv 64 0xb13f8) (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) (Z_to_bv 64 F) (Z_to_bv 64 1312)
               x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F3 (Z_to_bv 64 ASTKFREE5) fc3 None m3 (seg_rom bsegs)).
  Proof.
    atop_facts. pose proof (u_rngT sp) as Rsp.
    assert (HSPAr : 0 <= SPA < 2^64) by lia.
    eapply evtF_cut.
    { eapply (SF5 L RNG3 (Z_to_bv 64 0xb13f8) (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) (Z_to_bv 64 F) (Z_to_bv 64 1312)
                x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F3 fc3 m3 (aps_m s3) LB lo F);
        [exact AH3 | exact MI3 | | lia | rewrite unsigned_lit by lia; unfold SF5_STACK; lia | reflexivity | exact HFL |].
      - rewrite unsigned_lit by lia. destruct (stk_split bsegs m3 lo SPA (u sp) STK3 ltac:(lia)) as [S _]; exact S.
      - rewrite unsigned_lit by lia. eapply rng_sub; [exact RNGS | lia | lia]. }
    intros ms4 (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m4 & -> & MI4 & STK4 & PRES4 & AH4 & SHB4).
    rewrite (ret_pc_even 0xb13f8) by (lia || reflexivity).
    rewrite unsigned_lit in STK4, PRES4 by lia.
    (* [comment removed for export] *)
    assert (SAVED4 : forall k, 0 <= k < 13 ->
      bytes_at bsegs m4 (u sp - 8 - 8 * k) (word_to_le_bytes 8 (Z_to_bv 64 (nth (Z.to_nat k) [u ra; u s0; u s1; u s2; u s3'; u s4; u s5; u s6; u s7; u s8; u s9; u s10; u s11] 0)))).
    { intros k Hk. eapply aheap_pres_bytes_at; [exact PRES4 | exact (SAVED3 k Hk) | left; left; rewrite length_word_to_le_bytes; lia]. }
    assert (RCM4 : bytes_at bsegs m4 (SPA + 272) (word_to_le_bytes 8 (Z_to_bv 64 RC))).
    { eapply aheap_pres_bytes_at; [exact PRES4 | exact HRCM | left; left; rewrite length_word_to_le_bytes; lia]. }
    assert (STK4' : stk bsegs m4 lo (u sp)).
    { apply (stk_merge bsegs m4 lo SPA (u sp)); [exact STK4 | | lia].
      destruct (stk_split bsegs m3 lo SPA (u sp) STK3 ltac:(lia)) as [_ SU].
      eapply aheap_pres_stk; [exact PRES4 | exact SU | lia | lia]. }
    (* [comment removed for export] *)
    assert (E_SP : u sp = 16 * (u sp / 16)) by (pose proof (Z.div_mod (u sp) 16 ltac:(lia)); lia).
    set (PB := (u sp - 416 - SPA) / 16).
    assert (E_PB : u sp - 416 - SPA = 16 * PB) by (unfold PB; Z.div_mod_to_equations; lia).
    pose (ZF := PA2_t0f.ZL_t0f (u ra) (u sp / 16) (u gp) (u tp) (u s0) (u s1) (u s2) (u s3') (u s4) (u s5) (u s6) (u s7) (u s8) (u s9) (u s10)
                 (u s11) 0 0 0 0 0 0 0 0 0 0 0 0 0 PB 0 0 0 0 0 RC
                 [0xb13f8; u t0'; u t1'; u t2'; u a0'; u a1'; u a2'; u a3'; u a4'; u a5'; u a6'; u a7';
                  u x18; u x19; u x20; u x21; u x22; u x23; u x24; u x25; u x26; u x27; u t3'; u t4'; u t5'; u t6']).
    assert (RGF : regs_ok (mkEZ ZF) B2F_defs.T0_regs
                    (mkR (Z_to_bv 64 0xb13f8) (Z_to_bv 64 SPA) gp tp t0' t1' t2' sp (Z_to_bv 64 SPA) a0' a1' a2' a3' a4' a5' a6' a7'
                         x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')).
    { apply regs_ok_mkR.
      change (map (fun k => edenot ?E (sr_get B2F_defs.T0_regs (Z_to_bv 5 k))) rkeys) with (map (edenot E) (tl B2F_defs.T0_regs)).
      cbn [tl B2F_defs.T0_regs map].
      repeat (apply (f_equal2 (@cons word)); [apply ez_wt; [reflexivity|];
            cbv [B2F_defs.vSPA B2F_defs.vSP B2F_defs.vSP16 B2F_defs.vGP B2F_defs.vTP B2F_defs.vPB B2F_defs.V B2F_defs.mul B2F_defs.add
                 B2F_defs.sub];
            unfold ZF; cbn [zden nth PA2_t0f.ZL_t0f app]; rewrite ?u_Z_to_bv;
            first [ reflexivity | (apply Z.mod_small; apply u_rngT) | (rewrite Z.mod_mod by lia; reflexivity) | (f_equal; lia) ] |]).
      reflexivity. }
    assert (KNF : know_ok bsegs (mkEZ ZF) m4 B2F_defs.T0_kn).
    { assert (RCM4' : bytes_at bsegs m4 (u sp - 416 - 16 * PB + 272) (word_to_le_bytes 8 (Z_to_bv 64 RC)))
        by (replace (u sp - 416 - 16 * PB + 272) with (SPA + 272) by lia; exact RCM4).
      unfold ZF. eapply PA2_t0f.t0f_kn with (zsp := u sp); first [exact E_SP | exact SAVED4 | exact RCM4' | lia | (unfold PB; clear - HSPA HSPA32 Hsp16; Z.div_mod_to_equations; lia)]. }
    assert (WF : Forall (fun w => rng RNG3 (fst (SX.awin_den (mkEZ ZF) w)) (snd (SX.awin_den (mkEZ ZF) w) - fst (SX.awin_den (mkEZ ZF) w)))
                   [(B2F_defs.vSP, -104, ELit 104); (B2F_defs.vSPA, 272, ELit 8)]).
    { apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [SX.awin_den fst snd]; rewrite !u_zden by reflexivity;
      unfold ZF; cbv [B2F_defs.vSP B2F_defs.vSP16 B2F_defs.vSPA B2F_defs.vPB B2F_defs.V B2F_defs.mul B2F_defs.add B2F_defs.sub];
      cbn [zden nth PA2_t0f.ZL_t0f app]; rewrite <- ?E_SP.
      - rewrite !Z.mod_small by lia. eapply rng_sub'; [exact RNGS | lia].
      - replace (u sp + -416 - 16 * PB) with SPA by lia. rewrite !Z.mod_small by lia. eapply rng_sub'; [exact RNGS | lia]. }
    eapply evtF_cut.
    { eapply evtF_weaken; [exact (fp_of_le _ _ _ WF)|].
      exact (PA2_t0f.a2f_run (mkEZ ZF) m4 (seg_rom bsegs) _ F3 fc3 (aw_genuine_of_rng _ _ _ WF)
               (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) RGF KNF MI4 HZ3). }
    intros ms5 (X & E' & m5 & R5 & F5 & fc5 & HinX & -> & HZ5 & HF5 & HR5 & HK5 & _ & Hg & Hb & FR5 & WM5 & MI5 & STK5).
    cbn [SP.p_ex B2F_defs.B2F SP.PGCA SP.PGX] in HinX. destruct HinX as [<-|[]].
    destruct (a2f_xret_regs ZF E' R5 Hg (eq_sym Hb) HF5 HR5)
      as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & ->).
    assert (M45 : forall x, m5 x = m4 x) by (intros x; apply FR5; unfold SP.outside_wins; cbn [SP.p_W B2F_defs.B2F SP.PGCA SP.PGX]; constructor).
    unfold ZF. cbn [nth PA2_t0f.ZL_t0f app]. rewrite <- E_SP. rewrite !Z_to_bv_bv_unsigned.
    change (Z_to_bv 64 (ST.t_pc B2F_defs.XRET)) with (Z_to_bv 64 0xb1448).
    (* [comment removed for export] *)
    zstep. apply evtF_done. unfold s2_postA. split; [exact FPL|].
    exists y5, y6, y7, (edenot E' (EVar 35)), y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, F5, fc5, m5.
    split; [reflexivity|].
    split. { (* [comment removed for export] *)
             pose proof (know_nth _ _ _ _ 0 _ HK5 eq_refl) as KA0. cbn [kentry_ok] in KA0. change (B2F_defs.V 35) with (EVar 35) in KA0.
             clear - KA0. lia. }
    split; [exact HZ5|]. split; [exact MI5|]. split; [exact (STK5 _ _ STK4')|].
    split.
    { eapply aheap_pres_W_trans; [exact PW3|]. eapply aheap_pres_W_trans.
      - apply aheap_pres_W_of_pres. eapply aheap_pres_weaken; [exact PRES4 | lia | tauto].
      - intros a Ha Hc Hx. rewrite M45. split; [reflexivity|]. intros Hw. apply WM5. exact Hw. }
    split; [exact APS|].
    eapply (AI_frame AI); [exact AH4 | | exact WM5 | apply Forall_nil]. intros x _. apply M45.
  Qed.
End TAIL.
End CANSEC.
