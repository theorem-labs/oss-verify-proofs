(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore CatSim.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Mem Cells Step Frame.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require ExecF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Stdio_pure.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs PIosKitA PIosKit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface ROpNew ROpNew_nt.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require RMalloc_ifaceP RF_free_spec RDriver_facts F_stdio_exit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad HarnessP ProgP SjStage1 SjS1Bytes SjInv.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import RunDraw PU_iface PC_kit PC_s12iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg SegLib SegVCx.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA Require Import MuslMemU.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SFPU_sum PFFU_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SFPCU_sum PFFCU_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2G2 S2WalkVC S2WalkVCok S2Entry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require Import S2TabU U2_defs U2_cert.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2U Require Import PU2_t0 PU2_entry PU2_stmt PU2_reg PU2_p2n PU2_p2d.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require U2N_defs U2D_defs U2N_cert U2D_cert.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2U Require PU2_t0n PU2_t0nb PU2_t0d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Import ITree.Exc.
Open Scope Z_scope.
Local Notation u := bv_unsigned.
Local Notation M64 := 18446744073709551616.

Ltac rcr_blk I := right; right; eexists; split; [exact I | cbn [blk_addr blk_size fst snd cells_size csize]; lia].

Section XN.
  Context {rc : runConstT}.
  Hypothesis ONT : opnew_nt_stmt.
  Hypothesis ODA : opdelete_arr_stmt.
  Hypothesis SFPCSU_ok : forall GP, SP.summ_okH SG GP MMU.hmH MMU.hmA MMU.hmC MMU.hmR SFPCSU.
  Hypothesis PFFCSU_ok : forall GP, SP.summ_okH SG GP MMU.hmH MMU.hmA MMU.hmC MMU.hmR PFFCSU.

  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (m : mem) (s : PState) (LB : list block) (lo B : Z) (errv : word) (d idx : list Z)
            (pim psi pcp ptp psb poc pia : bptr) (THIS ASI ACP ATP ASB AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia : Z)
            (x24 x88 : word) (jtp jsb joc jia : list byte).
  Hypothesis HR : RHEAP s LB m.
  Hypothesis ND : List.NoDup [pim; psi; pcp; ptp; psb; poc; pia].
  Hypothesis Ith : In (pim, THIS, nim) LB.
  Hypothesis Hnim : 96 <= nim.
  Hypothesis Isi : In (psi, ASI, nsi) LB.
  Hypothesis Hnsi : 4 * zlength idx + 12 <= nsi.
  Hypothesis Icp : In (pcp, ACP, ncp) LB.
  Hypothesis Hb1 : ACP <= BUF.
  Hypothesis Hb2 : BUF + zlength d + 64 <= ACP + ncp.
  Hypothesis Itp : In (ptp, ATP, ntp) LB.
  Hypothesis Isb : In (psb, ASB, nsb) LB.
  Hypothesis Ioc : In (poc, AOC, noc) LB.
  Hypothesis Hnoc : 8192 <= noc.
  Hypothesis Iia : In (pia, AIA, nia) LB.
  Hypothesis Hnia : 1024 <= nia.
  Hypothesis Hntp8 : ntp mod 8 = 0.
  Hypothesis Hntp : 8 * (zlength idx + 3) <= ntp <= 2^27.
  Hypothesis Hnsb3 : 5 * zlength d + 182 <= 3 * nsb.
  Hypothesis Hnsb : zlength d + 60 <= nsb <= 2^24.
  Hypothesis Hbuf : bytes_at usegs m BUF (s1buf d).
  Hypothesis Hd : Forall (fun c => 0 <= c < 256) d.
  Hypothesis Hlen : zlength d + 64 <= 2^20.
  Hypothesis Hscan : scan d = (true, idx).
  Hypothesis HIDX : rw_cells usegs m ASI [CB (4 * (length idx + 3)) (u32bytes (idx ++ [zlength d; zlength d; 0]))].
  Hypothesis HO8 : rw_cells usegs m (THIS + 8) [C4 (Z_to_bv 64 (zlength idx))].
  Hypothesis HO16 : rw_cells usegs m (THIS + 16) [C8 (Z_to_bv 64 ASI)].
  Hypothesis HO24 : rw_cells usegs m (THIS + 24) [C4 x24].
  Hypothesis HO40 : rw_cells usegs m (THIS + 40) [C8 (Z_to_bv 64 MAX_DEPTH); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Hypothesis HO56 : rw_cells usegs m (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA); C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 (zlength d)); C8 x88].
  Hypothesis HDOC : rw_cells usegs m DOC [C8 (Z_to_bv 64 ATP); C8 (Z_to_bv 64 ASB)].
  Hypothesis Hspd : u sp <= DOC.
  Hypothesis Hdb : DOC + 16 <= B.
  Hypothesis Hda : DOC mod 8 = 0.
  Hypothesis HTB : rw_cells usegs m ATP [CB (Z.to_nat ntp) jtp].
  Hypothesis HFM : rw_cells usegs m PFMIN fmin_cells.
  Hypothesis HGOT : rw_cells usegs m PGOT_NOTHROW [C8 (Z_to_bv 64 PNOTHROW)].
  Hypothesis HAUX : rauxv_ok m B.
  Hypothesis Hspb : u sp <= B.
  Hypothesis HSTK : stk usegs m lo (u sp).
  Hypothesis Hlo1 : ATOP <= lo.
  Hypothesis Hlo2 : lo <= u sp - PS2_STACK.
  Hypothesis Hsp16 : u sp mod 16 = 0.
  Hypothesis Hsp47 : u sp <= 2^47.
  Hypothesis HERR : rw_cells usegs m (errno_addr tp) [C4 errv].
  Hypothesis HMI : mem_inv usegs m.
  Hypothesis HTP : tp = Z_to_bv 64 RATP.

  Let EZ := mkEZ (ZLe ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                      THIS DOC BUF (zlength d) ASI (zlength idx) ATP (ntp / 8) ASB nsb AOC AIA).
  Let W2 := [(u sp - 2976, u sp); (THIS + 24, THIS + 28); (THIS + 88, THIS + 96); (ATP, ATP + ntp); (ASB, ASB + nsb);
             (AOC, AOC + 8192); (AIA, AIA + 1024)].
  Let WS := s2_win THIS ATP ntp ASB nsb AOC AIA.
  Let Q := s2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo B WS m.

  (* [comment removed for export] *)
  Variables (E1 : env) (m1 : mem) (R1 F1 : bvmap 5 word) (fc1 : bv 32).
  Hypothesis X_Z : frm0 fc1.
  Hypothesis X_F : rfull R1.
  Hypothesis X_R : regs_ok E1 XNEW_regs R1.
  Hypothesis X_K : know_ok usegs E1 m1 XNEW_kn.
  Hypothesis X_G : SG.gholds (gp2 SG d (idx ++ [zlength d; zlength d; 0])) E1 m1 (ST.t_ghost XNEW).
  Hypothesis X_g : SP.gagree 28 EZ E1.
  Hypothesis X_b : eb E1 = eb EZ.
  Hypothesis X_MU : munch W2 m m1.
  Hypothesis X_WM : wmono usegs m m1.
  Hypothesis X_MI : mem_inv usegs m1.
  Hypothesis X_STK : forall lo hi, stk usegs m lo hi -> stk usegs m1 lo hi.

  Theorem xnew_branch :
    implM usegs (rn_copy d idx) s Q (MS R1 F1 (Z_to_bv 64 0x29e08) fc1 None m1 (seg_rom usegs)).
  Proof.
    pose proof (scan_S1OUT d idx Hscan) as S1. pose proof (s1_n _ _ _ S1) as Sn.
    pose proof Hlo2 as Hlo2'. unfold PS2_STACK, OPNEW_NT_STACK, OPNEW_STACK, RMALLOC_STACK in Hlo2'. atop_facts.
    pose proof (u_rng' sp) as Rsp.
    assert (HAUXB : B <= 2 ^ 64 - 160) by (destruct HAUX as (av & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbb & Hav & _); lia).
    pose proof (s2_reg_of s LB m sp lo B d idx pim psi pcp ptp psb poc pia THIS ASI ACP ATP ASB AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia
                  HR ND Ith Hnim Isi Hnsi Icp Hb1 Hb2 Itp Isb Ioc Hnoc Iia Hnia Hntp8 Hntp Hnsb3 Hnsb Hlen ltac:(lia) Hspd Hdb Hda HAUXB Hlo1
                  ltac:(lia) Hsp16 Hsp47) as REG.
    destruct_s2_reg REG.
    assert (HCAPT : 8 * (ntp / 8) = ntp) by (pose proof (Z.div_mod ntp 8 ltac:(lia)); lia).
    assert (UP : DJ 0x10000 0xa3000 ATP ntp) by (rewrite <- HCAPT; exact HU_TB).
    (* [comment removed for export] *)
    destruct (p2_frame_facts sp tp s LB lo B errv THIS ATP ntp ASB nsb AOC AIA pim ptp psb poc pia nim noc nia m m1
                HR Ith Hnim Itp Isb Ioc Hnoc Iia Hnia HU_THIS UP HU_SB HU_OC HU_IA Hlo1 ltac:(lia) Hspb HERR HTP HAUX X_MU X_WM)
      as (HR1 & HAUX1 & HERR1 & PW1).
    (* [comment removed for export] *)
    destruct idx as [|i0 idx']; [exfalso; unfold zlength in Sn; cbn [length Z.of_nat] in Sn; lia|].
    pose proof (s1_lt _ _ _ S1 0 ltac:(lia)) as Hi0. change (znth ((i0 :: idx') ++ [zlength d; zlength d; 0]) 0) with i0 in Hi0.
    unfold SG.gholds in X_G. cbn [ST.t_ghost XNEW] in X_G.
    apply Forall_inv_tail, Forall_inv_tail in X_G. pose proof (Forall_inv X_G) as GT. apply Forall_inv_tail, Forall_inv in X_G as GS.
    cbn [ST.g_id ST.g_args map gp2] in GT, GS. rewrite edenot_lit in GT. rewrite u_Z_to_bv, Zmod_0_l, Zdiv_0_l in GT.
    change (znth ((i0 :: idx') ++ [zlength d; zlength d; 0]) 0) with i0 in GT, GS. destruct GT as (_ & _ & GT).
    assert (E28 : ev E1 28 = Z_to_bv 64 i0) by (cbn [edenot V] in GT; rewrite <- GT; symmetry; apply Z_to_bv_bv_unsigned).
    unfold rn_copy. rewrite GS.
    (* [comment removed for export] *)
    set (GZ := [u ra; u sp; u gp; u tp; u s0; u s1; u s2; u s3; u s4; u s5; u s6; u s7; u s8; u s9; u s10; u s11;
                THIS; DOC; BUF; zlength d; ASI; zlength (i0 :: idx'); ATP; ntp / 8; ASB; nsb; AOC; AIA]).
    assert (Hg28 : SP.gagree 28 (mkEZ GZ) E1).
    { intros j Hj. rewrite <- (X_g j Hj). symmetry.
      exact (firstn28_ZLe ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               THIS DOC BUF (zlength d) ASI (zlength (i0 :: idx')) ATP (ntp / 8) ASB nsb AOC AIA j Hj). }
    assert (Hg29 : SP.gagree 29 (mkEZ (GZ ++ [i0])) E1) by (apply gagree_ext1; [reflexivity | exact Hg28 | exact E28]).
    assert (Hb29 : eb (mkEZ (GZ ++ [i0])) = eb E1) by (rewrite X_b; reflexivity).
    destruct (xnew_regs GZ E1 R1 i0 eq_refl Hg29 Hb29 X_F X_R)
      as (x1 & x5 & x6 & x7 & x9 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x20 & x22 & x23 & x24r & x25 & x27 & x28 & x29 & x30 & x31 & ->).
    unfold GZ; cbn [nth]. rewrite !Z_to_bv_bv_unsigned.
    assert (STK1 : stk usegs m1 lo (u sp - 368)) by (destruct (stk_split usegs m1 lo (u sp - 368) (u sp) (X_STK _ _ HSTK) ltac:(lia)) as [S _]; exact S).
    eapply implM_bind.
    { apply Stdio_pure.implM_from_evt. zstep. apply evt_done.
      eapply (proj2 ONT) with (lo := lo) (B := B) (errv := errv) (LB := LB).
      - exact HR1.
      - exact HAUX1.
      - rewrite unsigned_lit by lia. lia.
      - rewrite unsigned_lit by lia. exact STK1.
      - exact Hlo1.
      - rewrite unsigned_lit by lia. unfold OPNEW_NT_STACK, OPNEW_STACK, RMALLOC_STACK. lia.
      - exact HERR1.
      - exact X_MI.
      - exact HTP.
      - reflexivity.
      - clear - Hi0 Hlen. lia. }
    cbv beta. intros c s1' ms2 PO.
    destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & errv2 &
                    -> & MI2 & STK2 & ERR2 & AUX2 & PRES2 & FA2 & SO2 & A & junk & -> & BR & HR2 & CP2 & _).
    rewrite unsigned_lit in STK2, PRES2 by lia.
    rewrite (ret_pc_even 171532) by (lia || reflexivity).
    (* [comment removed for export] *)
    pose proof (copy_reg_of s1' LB m2 (u sp) c A pim psi pcp ptp psb poc pia THIS ASI ACP ATP ASB AOC AIA BUF nim nsi ncp ntp nsb noc nia
                  (zlength d) (zlength (i0 :: idx')) i0 HR2 BR Ith Hnim Isi Hnsi Icp Hb1 Hb2 Itp Isb Ioc Hnoc Iia Hnia Hntp8
                  ltac:(lia) ltac:(lia) ltac:(lia)) as CREG.
    destruct_copy_reg CREG.
    (* [comment removed for export] *)
    assert (PW2 : rheap_pres_W LB (u sp) WS m m2).
    { eapply PW_trans; [exact PW1|]. eapply PW_of_pres with (LB' := LB) (SP' := u sp - 368); [exact PRES2 | lia | auto]. }
    assert (M_O8 : rw_cells usegs m2 (THIS + 8) [C4 (Z_to_bv 64 (zlength (i0 :: idx')))]).
    { eapply PW_rw_cells; [exact PW2 | exact HO8 | rcr_blk Ith |].
      intros a Ha; cbn [cells_size csize] in Ha; unfold WS, s2_win; cbn [outside]; clear - Ha D3 D4 D5 D6 HCAPT; unfold DJ in *; lia. }
    assert (M_O16 : rw_cells usegs m2 (THIS + 16) [C8 (Z_to_bv 64 ASI)]).
    { eapply PW_rw_cells; [exact PW2 | exact HO16 | rcr_blk Ith |].
      intros a Ha; cbn [cells_size csize] in Ha; unfold WS, s2_win; cbn [outside]; clear - Ha D3 D4 D5 D6 HCAPT; unfold DJ in *; lia. }
    assert (M_O40 : rw_cells usegs m2 (THIS + 40) [C8 (Z_to_bv 64 1024); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
    { eapply PW_rw_cells; [exact PW2 | exact HO40 | rcr_blk Ith |].
      intros a Ha; cbn [cells_size csize] in Ha; unfold WS, s2_win; cbn [outside]; clear - Ha D3 D4 D5 D6 HCAPT; unfold DJ in *; lia. }
    assert (M_O56 : rw_cells usegs m2 (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA); C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 (zlength d))]).
    { pose proof (rw_cells_app_split usegs m (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA); C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 (zlength d))]
                    [C8 x88] HO56) as [HO56a _].
      eapply PW_rw_cells; [exact PW2 | exact HO56a | rcr_blk Ith |].
      intros a Ha; cbn [cells_size csize] in Ha; unfold WS, s2_win; cbn [outside]; clear - Ha D3 D4 D5 D6 HCAPT; unfold DJ in *; lia. }
    assert (M_DOC : rw_cells usegs m2 DOC [C8 (Z_to_bv 64 ATP); C8 (Z_to_bv 64 ASB)]).
    { eapply PW_rw_cells; [exact PW2 | exact HDOC | left; lia |].
      intros a Ha; cbn [cells_size csize] in Ha; unfold WS, s2_win; cbn [outside]; clear - Ha H_DOC H_THIS H_TB H_SB H_OC H_IA HCAPT; lia. }
    assert (M_TB : wr_at usegs m2 ATP (8 * (ntp / 8))).
    { rewrite HCAPT. eapply rheap_pres_wr_at; [exact PRES2 | | rcr_blk Itp].
      eapply wr_at_transport; [exact (rw_cells_wr_at _ _ _ _ ntp HTB ltac:(cbn; lia)) | exact X_WM]. }
    assert (M_CP : rw_cells usegs m2 A [CB (Z.to_nat (zlength d - i0 + 64)) junk]) by exact CP2.
    assert (M_BUF : bytes_at usegs m2 BUF (s1buf d)).
    { eapply PW_bytes_at; [exact PW2 | exact Hbuf | rewrite s1buf_length; rcr_blk Icp |].
      rewrite s1buf_length. intros a Ha; unfold WS, s2_win; cbn [outside]; clear - Ha D1 D8 D9 D10 D11 HCAPT; unfold DJ in *; lia. }
    assert (M_BUFl : Z.of_nat (length (s1buf d)) = zlength d + 64) by exact (s1buf_length d).
    assert (M_BUFz : forall i, 0 <= i < 64 -> nth_error (s1buf d) (Z.to_nat (zlength d + i)) = Some (Z_to_bv 8 0)) by exact (s1buf_zero d).
    assert (M_FMIN : rw_cells usegs m2 0x80f30 [C4 (Z_to_bv 64 8388608)]).
    { eapply PW_rw_cells; [exact PW2 | exact HFM | right; left; cbn [cells_size csize fmin_cells];
        unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; lia |].
      intros a Ha; cbn [cells_size csize fmin_cells] in Ha; unfold WS, s2_win; cbn [outside];
        clear - Ha HU_THIS HU_TB HU_SB HU_OC HU_IA HCAPT; unfold DJ in *; lia. }
    assert (M_GOT : rw_cells usegs m2 0x7fb20 [C8 (Z_to_bv 64 0x1b8d0)]).
    { eapply PW_rw_cells; [exact PW2 | exact HGOT | right; left; cbn [cells_size csize];
        unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; lia |].
      intros a Ha; cbn [cells_size csize] in Ha; unfold WS, s2_win; cbn [outside];
        clear - Ha HU_THIS HU_TB HU_SB HU_OC HU_IA HCAPT; unfold DJ in *; lia. }
    (* [comment removed for export] *)
    assert (XW : forall n b k w v, nth_error XNEW_kn n = Some (KWord (SA b k) w v) ->
                   expr_vars_lt 29 b = true -> expr_vars_lt 29 v = true -> (zok b && zok v)%bool = true ->
                   rclient_range LB (u sp - 368) (zden (GZ ++ [i0]) b mod M64 + k) (Z.of_nat (length (word_to_le_bytes w (Z_to_bv 64 (zden (GZ ++ [i0]) v))))) ->
                   bytes_at usegs m2 (zden (GZ ++ [i0]) b mod M64 + k) (word_to_le_bytes w (Z_to_bv 64 (zden (GZ ++ [i0]) v)))).
    { intros n b k w v Hn H1 H2 H3 Hr. eapply rheap_pres_bytes_at; [exact PRES2 | | exact Hr].
      exact (kx_word_g usegs 29 (GZ ++ [i0]) E1 m1 b k w v Hg29 Hb29 H1 H2 H3 (know_nth _ _ _ _ n _ X_K Hn)). }
    assert (M_O88 : bytes_at usegs m2 (THIS + 88) (word_to_le_bytes 8 (Z_to_bv 64 DOC))).
    { pose proof (XW 30%nat _ _ _ _ eq_refl eq_refl eq_refl eq_refl) as H. unfold GZ in H; cbv [vTHIS vDOC vSP vTBASE vSBASE vIDX vRA vS0 vS1 vS2 vS3 vS4 vS5 vS6 vS7 vS8 vS9 vS10 vS11 V add] in H; cbn [zden nth app] in H.
      rewrite Z.mod_small in H by lia. apply H. rewrite length_word_to_le_bytes. rcr_blk Ith. }
    assert (M_F328 : bytes_at usegs m2 (u sp - 328) (word_to_le_bytes 8 (Z_to_bv 64 (ATP + 8)))).
    { pose proof (XW 0%nat _ _ _ _ eq_refl eq_refl eq_refl eq_refl) as H. unfold GZ in H; cbv [vTHIS vDOC vSP vTBASE vSBASE vIDX vRA vS0 vS1 vS2 vS3 vS4 vS5 vS6 vS7 vS8 vS9 vS10 vS11 V add] in H; cbn [zden nth app] in H.
      rewrite Z.mod_small in H by lia. replace (u sp - 328) with (u sp + -328) by lia. apply H. rewrite length_word_to_le_bytes. left; lia. }
    assert (M_F320 : bytes_at usegs m2 (u sp - 320) (word_to_le_bytes 8 (Z_to_bv 64 (ASI + 4)))).
    { pose proof (XW 1%nat _ _ _ _ eq_refl eq_refl eq_refl eq_refl) as H. unfold GZ in H; cbv [vTHIS vDOC vSP vTBASE vSBASE vIDX vRA vS0 vS1 vS2 vS3 vS4 vS5 vS6 vS7 vS8 vS9 vS10 vS11 V add] in H; cbn [zden nth app] in H.
      rewrite Z.mod_small in H by lia. replace (u sp - 320) with (u sp + -320) by lia. apply H. rewrite length_word_to_le_bytes. left; lia. }
    assert (M_F312 : bytes_at usegs m2 (u sp - 312) (word_to_le_bytes 8 (Z_to_bv 64 ASB))).
    { pose proof (XW 2%nat _ _ _ _ eq_refl eq_refl eq_refl eq_refl) as H. unfold GZ in H; cbv [vTHIS vDOC vSP vTBASE vSBASE vIDX vRA vS0 vS1 vS2 vS3 vS4 vS5 vS6 vS7 vS8 vS9 vS10 vS11 V add] in H; cbn [zden nth app] in H.
      rewrite Z.mod_small in H by lia. replace (u sp - 312) with (u sp + -312) by lia. apply H. rewrite length_word_to_le_bytes. left; lia. }
    assert (M_F304 : bytes_at usegs m2 (u sp - 304) (word_to_le_bytes 8 (Z_to_bv 64 THIS))).
    { pose proof (XW 3%nat _ _ _ _ eq_refl eq_refl eq_refl eq_refl) as H. unfold GZ in H; cbv [vTHIS vDOC vSP vTBASE vSBASE vIDX vRA vS0 vS1 vS2 vS3 vS4 vS5 vS6 vS7 vS8 vS9 vS10 vS11 V add] in H; cbn [zden nth app] in H.
      rewrite Z.mod_small in H by lia. replace (u sp - 304) with (u sp + -304) by lia. apply H. rewrite length_word_to_le_bytes. left; lia. }
    assert (M_SAVED : forall k, 0 <= k < 13 ->
      bytes_at usegs m2 (u sp - 8 - 8 * k) (word_to_le_bytes 8 (Z_to_bv 64 (nth (Z.to_nat k) [u ra; u s0; u s1; u s2; u s3; u s4; u s5; u s6; u s7; u s8; u s9; u s10; u s11] 0)))).
    { intros k Hk.
      assert (Hk' : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12) by lia.
      destruct Hk' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]]]]];
      match goal with |- bytes_at _ _ (_ - 8 - 8 * ?k) _ =>
        let n := eval vm_compute in (Z.to_nat (6 + k)) in
        pose proof (XW n _ _ _ _ eq_refl eq_refl eq_refl eq_refl) as H; unfold GZ in H; cbv [vTHIS vDOC vSP vTBASE vSBASE vIDX vRA vS0 vS1 vS2 vS3 vS4 vS5 vS6 vS7 vS8 vS9 vS10 vS11 V add] in H; cbn [zden nth app] in H;
        rewrite Z.mod_small in H by lia; cbn [nth Z.to_nat Pos.to_nat Pos.iter_op Nat.add];
        replace (u sp - 8 - 8 * k) with (u sp + (- 8 - 8 * k)) by lia; apply H; rewrite length_word_to_le_bytes; left; lia
      end. }
    assert (M_STK : stk usegs m2 lo (u sp)).
    { destruct (stk_split usegs m1 lo (u sp - 368) (u sp) (X_STK _ _ HSTK) ltac:(lia)) as [_ SU].
      apply (stk_merge usegs m2 lo (u sp - 368) (u sp)); [exact STK2 | | lia].
      eapply rheap_pres_stk; [exact PRES2 | exact SU | lia]. }
    assert (M_LO : lo <= u sp - 2976) by lia.
    assert (M_IDX : rw_cells usegs m2 ASI [CB (4 * (length (i0 :: idx') + 3)) (u32bytes ((i0 :: idx') ++ [zlength d; zlength d; 0]))]).
    { eapply PW_rw_cells; [exact PW2 | exact HIDX | cbn [cells_size csize]; right; right; eexists; split; [exact Isi | cbn [blk_addr blk_size fst snd]; unfold zlength in *; lia] |].
      intros a Ha; cbn [cells_size csize] in Ha; unfold WS, s2_win; cbn [outside];
        clear - Ha D2 D12 D13 D14 D15 HCAPT; unfold zlength in *; cbn [length] in *; unfold DJ in *; lia. }
    assert (M_IDX0 : bytes_at usegs m2 ASI (word_to_le_bytes 4 (Z_to_bv 64 i0))).
    { destruct (cb_bytes m2 _ _ _ M_IDX) as [BI _]. cbn [app u32bytes] in BI.
      exact (proj1 (bytes_at_app_split _ _ _ _ _ BI)). }
    (* [comment removed for export] *)
    pose proof (PU2_t0nb.t0n_kn (u ra) (u sp) (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9) (u s10) (u s11)
                  THIS DOC BUF (zlength d) ASI (zlength (i0 :: idx')) ATP (ntp / 8) ASB nsb AOC AIA i0 A
                  [u (Z_to_bv 64 171532); u t0'; u t1'; u t2'; u x9; u a1'; u a2'; u a3'; u a4'; u a5'; u a6'; u a7';
                   u x20; u x22; u x23; u x24r; u x25; u x27; u t3'; u t4'; u t5'; u t6']
                  m2 lo (s1buf d) junk H_LEN H_N H_CAPT H_CAPS H_CAPS3 H_V H_SP H_SPa H_DOC H_THIS H_BUF H_IDX H_TB H_SB H_OC H_IA H_CP
                  HU_THIS HU_BUF HU_IDX HU_TB HU_SB HU_OC HU_IA HU_CP D1 D2 D3 D4 D5 D6 D7 D8 D9 D10 D11 D12 D13 D14 D15 D16 D17 D18
                  D19 D20 D21 D22 D23 D24 D25 D26 D27 D28 M_O8 M_O16 M_O40 M_O56 M_O88 M_DOC M_TB M_CP M_BUF M_BUFl M_BUFz M_FMIN M_GOT
                  M_F328 M_F320 M_F312 M_F304 M_IDX0 M_SAVED M_STK M_LO MI2) as KN2.
    eapply implM_evt.
    { eapply ExecF.evtF_evt.
      exact (u2n_run SFPCSU_ok PFFCSU_ok (u ra) (u sp) (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9)
               (u s10) (u s11) THIS DOC BUF (zlength d) ASI (zlength (i0 :: idx')) ATP (ntp / 8) ASB nsb AOC AIA i0 A
               (Z_to_bv 64 171532) t0' t1' t2' x9 a1' a2' a3' a4' a5' a6' a7' x20 x22 x23 x24r x25 x27 t3' t4' t5' t6' gp tp F1 fc1 m2 d
               (i0 :: idx') eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
               KN2 eq_refl eq_refl Hd Hscan M_BUF HU_BUF ltac:(lia) M_IDX HU_IDX ltac:(lia) MI2 X_Z). }
    intros ms3 HX3.
    destruct HX3 as (X & E3 & m3 & R3 & F3 & fc3 & HinX & -> & HZ3 & HF3 & HR3 & HK3 & HG3 & Hg3 & Hb3 & HH3 & FR3 & WM3 & MI3 & STK3).
    (* [comment removed for export] *)
    unfold SP.frame_ok in FR3. cbn [SP.p_PS U2N_defs.U2N SP.PGC] in FR3.
    (pose proof (u2n_munch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR3
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as MU3).
    cbv beta in MU3.
    (assert (M_W24 : wr_at usegs m2 (THIS + 24) 4) by
      (eapply rheap_pres_wr_at; [exact PRES2 | | rcr_blk Ith];
       eapply wr_at_transport; [exact (rw_cells_wr_at _ _ _ _ 4 HO24 ltac:(cbn; lia)) | exact X_WM])).
    (assert (HR3' : RHEAP s1' ((c, A, zlength d - i0 + 64) :: LB) m3) by
      (eapply Ubsan.RMalloc_ifaceP.RHEAP_frame_proof; [exact HR2 | exact MU3 | exact WM3 |];
       repeat apply Forall_cons; [..| apply Forall_nil]; unfold rclient_write_ok; cbn [fst snd];
       [ left; lia
       | left; lia
       | right; right; exists (ptp, ATP, ntp); cbn [fst snd blk_addr blk_size]; split; [right; exact Itp | lia]
       | right; right; exists (c, A, zlength d - i0 + 64); cbn [fst snd blk_addr blk_size]; split; [left; reflexivity | lia] ])).
    (assert (AUX3 : rauxv_ok m3 B) by
      (eapply Ubsan.RF_free_spec.rauxv_ok_pres_B with (C := fun a => u sp - 368 <= a < u sp \/ u sp - 2976 <= a < u sp - 368 \/
                     ATP <= a < ATP + 8 * (ntp / 8) \/ A <= a < A + (zlength d - i0 + 64)); [exact AUX2 | | |];
       [ intros a Ha Hc; split; [apply MU3; rewrite unsigned_lit by (clear - Ha; lia); cbn [outside]; clear - Hc; lia|]; apply WM3
       | intros a Ha Hc; clear - Ha Hc Hspb H_TB H_CP HCAPT H_SP; lia
       | intros a Ha Hc; unfold RAUXV_CELL in Ha; clear - Ha Hc HU_TB HU_CP H_SP HCAPT; unfold DJ in *; lia ])).
    (assert (ERR3 : rw_cells usegs m3 (errno_addr tp) [C4 errv2]) by
      (rewrite HTP, errno_lit in ERR2 |- *; eapply rw_cells_transport; [exact ERR2 | exact MU3 | exact WM3 |];
       unfold RERRNO; cbn [disjoint_from cells_size csize]; unfold DJ in HU_TB, HU_CP; lia)).
    assert (STK3' : stk usegs m3 lo (u sp)) by (apply STK3; exact M_STK).
    (assert (PW3 : rheap_pres_W LB (u sp) WS m m3) by
      (eapply PW_trans; [exact PW2|]; eapply PW_of_munch; [exact MU3 | exact WM3 |];
       intros a Ha Hc Ho; unfold WS, s2_win in Ho; cbn [outside] in Ho |- *;
       destruct Hc as [Hc|[Hc|(b & Hb & B1 & B2)]];
       [ clear - Hc H_TB H_CP HCAPT H_SP; lia
       | destruct Hc as [Hc _]; clear - Hc H_SP HU_TB HU_CP HCAPT; unfold DJ in *; lia
       | pose proof (new_block_disj _ _ _ _ _ _ _ HR2 Hb) as Bn; cbn [blk_addr blk_size fst snd] in Bn;
         pose proof (Ubsan.RMalloc_ifaceP.RHEAP_block_range_proof s LB m b HR Hb) as (_ & _ & _ & Rb4 & _);
         destruct Ho as (_ & _ & Ht & _); clear - B1 B2 Bn Rb4 Ht HCAPT Hlo1 Hlo2'; lia ])).
    (assert (M3_O8 : rw_cells usegs m3 (THIS + 8) [C4 (Z_to_bv 64 (zlength (i0 :: idx')))]) by
      (eapply rw_cells_transport; [exact M_O8 | exact MU3 | exact WM3 |]; cbn [disjoint_from cells_size csize];
       clear - D3 D22 H_THIS H_SP HCAPT; unfold DJ in *; lia)).
    (assert (M3_O16 : rw_cells usegs m3 (THIS + 16) [C8 (Z_to_bv 64 ASI)]) by
      (eapply rw_cells_transport; [exact M_O16 | exact MU3 | exact WM3 |]; cbn [disjoint_from cells_size csize];
       clear - D3 D22 H_THIS H_SP HCAPT; unfold DJ in *; lia)).
    (assert (M3_DOC : rw_cells usegs m3 DOC [C8 (Z_to_bv 64 ATP); C8 (Z_to_bv 64 ASB)]) by
      (eapply rw_cells_transport; [exact M_DOC | exact MU3 | exact WM3 |]; cbn [disjoint_from cells_size csize];
       clear - H_DOC H_TB H_CP HCAPT; lia)).
    (assert (M3_O88 : bytes_at usegs m3 (THIS + 88) (word_to_le_bytes 8 (Z_to_bv 64 DOC))) by
      (eapply bytes_at_transport; [exact M_O88 | exact MU3 |]; rewrite length_word_to_le_bytes; cbn [disjoint_from];
       clear - D3 D22 H_THIS H_SP HCAPT; unfold DJ in *; lia)).
    assert (M3_W24 : wr_at usegs m3 (THIS + 24) 4) by (eapply wr_at_transport; [exact M_W24 | exact WM3]).
    assert (M3_TB : wr_at usegs m3 ATP (8 * (ntp / 8))) by (eapply wr_at_transport; [exact M_TB | exact WM3]).
    clear MU3 FR3.
    (* [comment removed for export] *)
    set (ZL30 := [u ra; u sp; u gp; u tp; u s0; u s1; u s2; u s3; u s4; u s5; u s6; u s7; u s8; u s9; u s10; u s11;
                  THIS; DOC; BUF; zlength d; ASI; zlength (i0 :: idx'); ATP; ntp / 8; ASB; nsb; AOC; AIA; i0; A]).
    assert (Hg30 : SP.gagree 30 (mkEZ ZL30) E3) by (eapply gagree_app_l; [reflexivity | exact Hg3]).
    assert (Hb30 : eb (mkEZ ZL30) = eb E3) by (rewrite Hb3; reflexivity).
    cbn [SP.p_ex U2N_defs.U2N] in HinX.
    assert (H_N' : 1 <= zlength (i0 :: idx') <= 1048512) by lia.
    assert (H_TW8 : 8 <= 8 <= 24 /\ 8 mod 8 = 0) by (split; [lia | reflexivity]).
    assert (STK3a : stk usegs m3 lo (u sp - 368)) by (destruct (stk_split usegs m3 lo (u sp - 368) (u sp) STK3' ltac:(lia)) as [S _]; exact S).
    assert (STK3b : stk usegs m3 (u sp - 368) (u sp)) by (destruct (stk_split usegs m3 lo (u sp - 368) (u sp) STK3' ltac:(lia)) as [_ S]; exact S).
    assert (ND3 : lb_remove c ((c, A, zlength d - i0 + 64) :: LB) = LB)
      by (apply (Ubsan.RDriver_facts.lb_remove_head (c, A, zlength d - i0 + 64) LB); exact (Ubsan.RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HR3')).
    destruct HinX as [<-|[<-|[<-|[]]]].
    - (* [comment removed for export] *)
      destruct (xdel_regsA ZL30 E3 R3 eq_refl Hg30 Hb30 HF3 HR3)
        as (y1 & y5 & y6 & y7 & y8 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20 & y21 & y22 & y23 & y24 & y25 & y26 &
            y27 & y28 & y29 & y30 & y31 & ->).
      unfold ZL30; cbn [nth]. rewrite !Z_to_bv_bv_unsigned. change (ST.t_pc U2N_defs.XDELA) with 0x29f00.
      eapply Ubsan.F_stdio_exit.implM_post_evt'.
      { apply Stdio_pure.implM_from_evt. zstep. apply evt_done.
        eapply ODA with (p := c) (A := A) (n := zlength d - i0 + 64) (LB := (c, A, zlength d - i0 + 64) :: LB) (lo := lo) (B := B)
                        (errv := errv2).
        - exact HR3'.
        - left; reflexivity.
        - exact AUX3.
        - rewrite unsigned_lit by lia. lia.
        - rewrite unsigned_lit by lia. exact STK3a.
        - exact Hlo1.
        - rewrite unsigned_lit by lia. unfold RFREE_STACK. lia.
        - exact ERR3.
        - exact MI3.
        - exact HTP.
        - reflexivity. }
      intros [] st4 ms4 RP.
      destruct RP as (t0'' & t1'' & t2'' & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & t3'' & t4'' & t5'' & t6'' & m4 &
                      -> & MI4 & STK4 & ERR4 & AUX4 & PRES4 & FA4 & SO4 & HR4).
      rewrite unsigned_lit in STK4, PRES4 by lia. rewrite ND3 in PRES4, HR4.
      rewrite (ret_pc_even 0x29f04) by (lia || reflexivity).
      (* [comment removed for export] *)
      assert (M4_STK : stk usegs m4 lo (u sp)).
      { apply (stk_merge usegs m4 lo (u sp - 368) (u sp)); [exact STK4 | | lia].
        eapply rheap_pres_stk; [exact PRES4 | exact STK3b | lia]. }
      assert (M4_W24 : wr_at usegs m4 (THIS + 24) 4) by (eapply rheap_pres_wr_at; [exact PRES4 | exact M3_W24 | rcr_blk Ith]).
      assert (M4_TB : wr_at usegs m4 ATP (8 * (ntp / 8))) by (eapply rheap_pres_wr_at; [exact PRES4 | exact M3_TB | rcr_blk Itp]).
      assert (XW3 : forall n b k w v, nth_error (ST.t_know U2N_defs.XDELA) n = Some (KWord (SA b k) w v) ->
                   expr_vars_lt 30 b = true -> expr_vars_lt 30 v = true -> (zok b && zok v)%bool = true ->
                   rclient_range LB (u sp - 368) (zden ZL30 b mod M64 + k) (Z.of_nat (length (word_to_le_bytes w (Z_to_bv 64 (zden ZL30 v))))) ->
                   bytes_at usegs m4 (zden ZL30 b mod M64 + k) (word_to_le_bytes w (Z_to_bv 64 (zden ZL30 v)))).
      { intros n b k w v Hn H1 H2 H3 Hr. eapply rheap_pres_bytes_at; [exact PRES4 | | exact Hr].
        exact (kx_word_g usegs 30 ZL30 E3 m3 b k w v Hg30 Hb30 H1 H2 H3 (know_nth _ _ _ _ n _ HK3 Hn)). }
      assert (M4_SAVED : forall k, 0 <= k < 13 ->
        bytes_at usegs m4 (u sp - 8 - 8 * k) (word_to_le_bytes 8 (Z_to_bv 64 (nth (Z.to_nat k) [u ra; u s0; u s1; u s2; u s3; u s4; u s5; u s6; u s7; u s8; u s9; u s10; u s11] 0)))).
      { intros k Hk.
        assert (Hk' : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12) by lia.
        destruct Hk' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]]]]];
        match goal with |- bytes_at _ _ (_ - 8 - 8 * ?k) _ =>
          let n := eval vm_compute in (Z.to_nat (4 + k)) in
          pose proof (XW3 n _ _ _ _ eq_refl eq_refl eq_refl eq_refl) as H; unfold ZL30 in H;
          cbv [U2N_defs.vSP U2N_defs.vRA U2N_defs.vS0 U2N_defs.vS1 U2N_defs.vS2 U2N_defs.vS3 U2N_defs.vS4 U2N_defs.vS5 U2N_defs.vS6
               U2N_defs.vS7 U2N_defs.vS8 U2N_defs.vS9 U2N_defs.vS10 U2N_defs.vS11 U2N_defs.V] in H; cbn [zden nth app] in H;
          rewrite Z.mod_small in H by lia; cbn [nth Z.to_nat Pos.to_nat Pos.iter_op Nat.add];
          replace (u sp - 8 - 8 * k) with (u sp + (- 8 - 8 * k)) by lia; apply H; rewrite length_word_to_le_bytes; left; lia
        end. }
      assert (H_RC0 : 0 <= 0 <= 63) by lia.
      assert (M4_F304 : bytes_at usegs m4 (u sp - 304) (word_to_le_bytes 8 (Z_to_bv 64 THIS))).
      { pose proof (XW3 3%nat _ _ _ _ eq_refl eq_refl eq_refl eq_refl) as H. unfold ZL30 in H;
        cbv [U2N_defs.vSP U2N_defs.vTHIS U2N_defs.V] in H; cbn [zden nth app] in H.
        rewrite Z.mod_small in H by lia. replace (u sp - 304) with (u sp + -304) by lia. apply H. rewrite length_word_to_le_bytes. left; lia. }
      (* [comment removed for export] *)
      assert (KN4 : know_ok usegs (mkEZ (PU2_t0d.ZLD1 (u ra) (u sp) (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8)
                    (u s9) (u s10) (u s11) THIS DOC BUF (zlength d) ASI (zlength (i0 :: idx')) ATP (ntp / 8) ASB nsb AOC AIA 0 
                    [u (Z_to_bv 64 0x29f04); u t0''; u t1''; u t2''; u y8; u (Z_to_bv 64 A); u b0; u b1; u b2; u b3; u b4; u b5; u b6; u b7;
                     u y18; u y19; u y20; u y21; u y22; u y23; u y24; u y25; u y26; u y27; u t3''; u t4''; u t5''; u t6''])) m4 U2D_defs.DA_kn)
        by (eapply PU2_t0d.dA_kn; eassumption).
      eapply evt_cut.
      { eapply ExecF.evtF_evt.
        exact (u2d_runA (u ra) (u sp) (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9) (u s10)
                 (u s11) THIS DOC BUF (zlength d) ASI (zlength (i0 :: idx')) ATP (ntp / 8) ASB nsb AOC AIA 0
                 (Z_to_bv 64 0x29f04) t0'' t1'' t2'' y8 (Z_to_bv 64 A) b0 b1 b2 b3 b4 b5 b6 b7 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
                 t3'' t4'' t5'' t6'' gp tp F3 fc3 m4 eq_refl eq_refl ltac:(lia) KN4 MI4 HZ3). }
      intros ms5 HX5.
      destruct HX5 as (X5 & E5 & m5 & R5 & F5 & fc5 & HinX5 & -> & HZ5 & HF5 & HR5 & HK5 & HG5 & Hg5 & Hb5 & FR5 & WM5 & MI5 & STK5).
      cbn [SP.p_ex U2D_defs.U2D] in HinX5. destruct HinX5 as [<-|[]].
      pose proof (know_nth _ _ _ _ XRET_RC _ HK5 eq_refl) as KA0. cbn [kentry_ok] in KA0. change (U2D_defs.V 28) with (EVar 28) in KA0.
      destruct (u2d_xret_regs _ E5 R5 Hg5 (eq_sym Hb5) HF5 HR5)
        as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & ->).
      cbn [nth PU2_t0d.ZLD1 app]. rewrite !Z_to_bv_bv_unsigned. change (ST.t_pc U2D_defs.XRET) with 0x323b8.
      assert (MU5 : munch [(u sp - 368, u sp); (THIS + 24, THIS + 28); (ATP, ATP + 8 * (ntp / 8))] m4 m5)
        by (eapply u2d_munch; [| | | | exact FR5 | lia..]; reflexivity).
      clear FR5.
      eapply xret_post2 with (errv := errv2) (x10 := edenot E5 (EVar 28)).
      { eapply Ubsan.RMalloc_ifaceP.RHEAP_frame_proof; [exact HR4 | exact MU5 | exact WM5 |].
        repeat apply Forall_cons; [..| apply Forall_nil]; unfold rclient_write_ok; cbn [fst snd].
        - left. lia.
        - right; right. exists (pim, THIS, nim). cbn [fst snd blk_addr blk_size]. split; [exact Ith | lia].
        - right; right. exists (ptp, ATP, ntp). cbn [fst snd blk_addr blk_size]. split; [exact Itp | lia]. }
      { eapply Ubsan.RF_free_spec.rauxv_ok_pres_B with (C := fun a => u sp - 368 <= a < u sp \/ THIS + 24 <= a < THIS + 28 \/
                     ATP <= a < ATP + 8 * (ntp / 8)); [exact AUX4 | | |].
        - intros a Ha Hc; split; [apply MU5; rewrite unsigned_lit by (clear - Ha; lia); cbn [outside]; clear - Hc; lia|]; apply WM5.
        - intros a Ha Hc; clear - Ha Hc Hspb H_TB H_THIS HCAPT H_SP; lia.
        - intros a Ha Hc; unfold RAUXV_CELL in Ha; clear - Ha Hc HU_TB HU_THIS H_SP HCAPT; unfold DJ in *; lia. }
      { rewrite HTP, errno_lit in ERR4 |- *. eapply rw_cells_transport; [exact ERR4 | exact MU5 | exact WM5 |].
        unfold RERRNO. cbn [disjoint_from cells_size csize]. clear - HU_TB HU_THIS H_SP HCAPT; unfold DJ in *. lia. }
      { exact (STK5 _ _ M4_STK). }
      { exact MI5. }
      { eapply PW_trans; [exact PW3|]. eapply PW_trans.
        - eapply PW_of_pres with (LB' := LB) (SP' := u sp - 368); [exact PRES4 | lia | auto].
        - eapply PW_of_munch; [exact MU5 | exact WM5 |].
          intros a Ha Hc Ho. unfold WS, s2_win in Ho. cbn [outside] in Ho |- *.
          destruct Hc as [Hc|[Hc|(b & Hb & B1 & B2)]].
          + clear - Hc H_TB H_THIS HCAPT H_SP; lia.
          + destruct Hc as [Hc _]; clear - Hc H_SP HU_TB HU_THIS HCAPT; unfold DJ in *; lia.
          + pose proof (Ubsan.RMalloc_ifaceP.RHEAP_block_range_proof s LB m b HR Hb) as (_ & _ & _ & Rb4 & _).
            destruct Ho as (Hw24 & _ & Ht & _); clear - B1 B2 Rb4 Ht Hw24 HCAPT Hlo1 Hlo2'; lia. }
      { rewrite FA4. exact FA2. }
      { rewrite SO4. exact SO2. }
      { exact HZ5. }
      { lia. }
      { reflexivity. }
    - (* [comment removed for export] *)
      destruct (xdel_regsBC U2N_defs.XDELB ZL30 E3 R3 (or_introl eq_refl) eq_refl Hg30 Hb30 HF3 HR3)
        as (y1 & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20 & y21 & y22 & y23 & y24 & y25 & y26 & y27 &
            y28 & y29 & y30 & y31 & ->).
      unfold ZL30; cbn [nth]. rewrite !Z_to_bv_bv_unsigned. change (ST.t_pc U2N_defs.XDELB) with 0x2d358.
      eapply Ubsan.F_stdio_exit.implM_post_evt'.
      { apply Stdio_pure.implM_from_evt. zstep. apply evt_done.
        eapply ODA with (p := c) (A := A) (n := zlength d - i0 + 64) (LB := (c, A, zlength d - i0 + 64) :: LB) (lo := lo) (B := B)
                        (errv := errv2).
        - exact HR3'.
        - left; reflexivity.
        - exact AUX3.
        - rewrite unsigned_lit by lia. lia.
        - rewrite unsigned_lit by lia. exact STK3a.
        - exact Hlo1.
        - rewrite unsigned_lit by lia. unfold RFREE_STACK. lia.
        - exact ERR3.
        - exact MI3.
        - exact HTP.
        - reflexivity. }
      intros [] st4 ms4 RP.
      destruct RP as (t0'' & t1'' & t2'' & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & t3'' & t4'' & t5'' & t6'' & m4 &
                      -> & MI4 & STK4 & ERR4 & AUX4 & PRES4 & FA4 & SO4 & HR4).
      rewrite unsigned_lit in STK4, PRES4 by lia. rewrite ND3 in PRES4, HR4.
      rewrite (ret_pc_even 0x2d35c) by (lia || reflexivity).
      (* [comment removed for export] *)
      assert (M4_STK : stk usegs m4 lo (u sp)).
      { apply (stk_merge usegs m4 lo (u sp - 368) (u sp)); [exact STK4 | | lia].
        eapply rheap_pres_stk; [exact PRES4 | exact STK3b | lia]. }
      assert (M4_W24 : wr_at usegs m4 (THIS + 24) 4) by (eapply rheap_pres_wr_at; [exact PRES4 | exact M3_W24 | rcr_blk Ith]).
      assert (M4_TB : wr_at usegs m4 ATP (8 * (ntp / 8))) by (eapply rheap_pres_wr_at; [exact PRES4 | exact M3_TB | rcr_blk Itp]).
      assert (XW3 : forall n b k w v, nth_error (ST.t_know U2N_defs.XDELB) n = Some (KWord (SA b k) w v) ->
                   expr_vars_lt 30 b = true -> expr_vars_lt 30 v = true -> (zok b && zok v)%bool = true ->
                   rclient_range LB (u sp - 368) (zden ZL30 b mod M64 + k) (Z.of_nat (length (word_to_le_bytes w (Z_to_bv 64 (zden ZL30 v))))) ->
                   bytes_at usegs m4 (zden ZL30 b mod M64 + k) (word_to_le_bytes w (Z_to_bv 64 (zden ZL30 v)))).
      { intros n b k w v Hn H1 H2 H3 Hr. eapply rheap_pres_bytes_at; [exact PRES4 | | exact Hr].
        exact (kx_word_g usegs 30 ZL30 E3 m3 b k w v Hg30 Hb30 H1 H2 H3 (know_nth _ _ _ _ n _ HK3 Hn)). }
      assert (M4_SAVED : forall k, 0 <= k < 13 ->
        bytes_at usegs m4 (u sp - 8 - 8 * k) (word_to_le_bytes 8 (Z_to_bv 64 (nth (Z.to_nat k) [u ra; u s0; u s1; u s2; u s3; u s4; u s5; u s6; u s7; u s8; u s9; u s10; u s11] 0)))).
      { intros k Hk.
        assert (Hk' : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12) by lia.
        destruct Hk' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]]]]];
        match goal with |- bytes_at _ _ (_ - 8 - 8 * ?k) _ =>
          let n := eval vm_compute in (Z.to_nat (5 + k)) in
          pose proof (XW3 n _ _ _ _ eq_refl eq_refl eq_refl eq_refl) as H; unfold ZL30 in H;
          cbv [U2N_defs.vSP U2N_defs.vRA U2N_defs.vS0 U2N_defs.vS1 U2N_defs.vS2 U2N_defs.vS3 U2N_defs.vS4 U2N_defs.vS5 U2N_defs.vS6
               U2N_defs.vS7 U2N_defs.vS8 U2N_defs.vS9 U2N_defs.vS10 U2N_defs.vS11 U2N_defs.V] in H; cbn [zden nth app] in H;
          rewrite Z.mod_small in H by lia; cbn [nth Z.to_nat Pos.to_nat Pos.iter_op Nat.add];
          replace (u sp - 8 - 8 * k) with (u sp + (- 8 - 8 * k)) by lia; apply H; rewrite length_word_to_le_bytes; left; lia
        end. }
      pose proof (know_nth _ _ _ _ 4 _ HK3 eq_refl) as KRC. cbn [kentry_ok edenot U2N_defs.V] in KRC.
      assert (H_RC : 0 <= u (ev E3 30) <= 63) by exact KRC.
      assert (M4_F304 : bytes_at usegs m4 (u sp - 304) (word_to_le_bytes 8 (Z_to_bv 64 THIS))).
      { pose proof (XW3 3%nat _ _ _ _ eq_refl eq_refl eq_refl eq_refl) as H. unfold ZL30 in H;
        cbv [U2N_defs.vSP U2N_defs.vTHIS U2N_defs.V] in H; cbn [zden nth app] in H.
        rewrite Z.mod_small in H by lia. replace (u sp - 304) with (u sp + -304) by lia. apply H. rewrite length_word_to_le_bytes. left; lia. }
      (* [comment removed for export] *)
      assert (KN4 : know_ok usegs (mkEZ (PU2_t0d.ZLD1 (u ra) (u sp) (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8)
                    (u s9) (u s10) (u s11) THIS DOC BUF (zlength d) ASI (zlength (i0 :: idx')) ATP (ntp / 8) ASB nsb AOC AIA (u (ev E3 30)) 
                    [u (Z_to_bv 64 0x2d35c); u t0''; u t1''; u t2''; u (Z_to_bv 64 A); u b0; u b1; u b2; u b3; u b4; u b5; u b6; u b7;
                     u y18; u y19; u y20; u y21; u y22; u y23; u y24; u y25; u y26; u y27; u t3''; u t4''; u t5''; u t6''])) m4 U2D_defs.DB_kn)
        by (eapply PU2_t0d.dB_kn; eassumption).
      eapply evt_cut.
      { eapply ExecF.evtF_evt.
        exact (u2d_runB (u ra) (u sp) (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9) (u s10)
                 (u s11) THIS DOC BUF (zlength d) ASI (zlength (i0 :: idx')) ATP (ntp / 8) ASB nsb AOC AIA 
                 (Z_to_bv 64 0x2d35c) t0'' t1'' t2'' (ev E3 30) (Z_to_bv 64 A) b0 b1 b2 b3 b4 b5 b6 b7 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
                 t3'' t4'' t5'' t6'' gp tp F3 fc3 m4 eq_refl eq_refl ltac:(lia) KN4 MI4 HZ3). }
      intros ms5 HX5.
      destruct HX5 as (X5 & E5 & m5 & R5 & F5 & fc5 & HinX5 & -> & HZ5 & HF5 & HR5 & HK5 & HG5 & Hg5 & Hb5 & FR5 & WM5 & MI5 & STK5).
      cbn [SP.p_ex U2D_defs.U2D] in HinX5. destruct HinX5 as [<-|[]].
      pose proof (know_nth _ _ _ _ XRET_RC _ HK5 eq_refl) as KA0. cbn [kentry_ok] in KA0. change (U2D_defs.V 28) with (EVar 28) in KA0.
      destruct (u2d_xret_regs _ E5 R5 Hg5 (eq_sym Hb5) HF5 HR5)
        as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & ->).
      cbn [nth PU2_t0d.ZLD1 app]. rewrite !Z_to_bv_bv_unsigned. change (ST.t_pc U2D_defs.XRET) with 0x323b8.
      assert (MU5 : munch [(u sp - 368, u sp); (THIS + 24, THIS + 28); (ATP, ATP + 8 * (ntp / 8))] m4 m5)
        by (eapply u2d_munch; [| | | | exact FR5 | lia..]; reflexivity).
      clear FR5.
      eapply xret_post2 with (errv := errv2) (x10 := edenot E5 (EVar 28)).
      { eapply Ubsan.RMalloc_ifaceP.RHEAP_frame_proof; [exact HR4 | exact MU5 | exact WM5 |].
        repeat apply Forall_cons; [..| apply Forall_nil]; unfold rclient_write_ok; cbn [fst snd].
        - left. lia.
        - right; right. exists (pim, THIS, nim). cbn [fst snd blk_addr blk_size]. split; [exact Ith | lia].
        - right; right. exists (ptp, ATP, ntp). cbn [fst snd blk_addr blk_size]. split; [exact Itp | lia]. }
      { eapply Ubsan.RF_free_spec.rauxv_ok_pres_B with (C := fun a => u sp - 368 <= a < u sp \/ THIS + 24 <= a < THIS + 28 \/
                     ATP <= a < ATP + 8 * (ntp / 8)); [exact AUX4 | | |].
        - intros a Ha Hc; split; [apply MU5; rewrite unsigned_lit by (clear - Ha; lia); cbn [outside]; clear - Hc; lia|]; apply WM5.
        - intros a Ha Hc; clear - Ha Hc Hspb H_TB H_THIS HCAPT H_SP; lia.
        - intros a Ha Hc; unfold RAUXV_CELL in Ha; clear - Ha Hc HU_TB HU_THIS H_SP HCAPT; unfold DJ in *; lia. }
      { rewrite HTP, errno_lit in ERR4 |- *. eapply rw_cells_transport; [exact ERR4 | exact MU5 | exact WM5 |].
        unfold RERRNO. cbn [disjoint_from cells_size csize]. clear - HU_TB HU_THIS H_SP HCAPT; unfold DJ in *. lia. }
      { exact (STK5 _ _ M4_STK). }
      { exact MI5. }
      { eapply PW_trans; [exact PW3|]. eapply PW_trans.
        - eapply PW_of_pres with (LB' := LB) (SP' := u sp - 368); [exact PRES4 | lia | auto].
        - eapply PW_of_munch; [exact MU5 | exact WM5 |].
          intros a Ha Hc Ho. unfold WS, s2_win in Ho. cbn [outside] in Ho |- *.
          destruct Hc as [Hc|[Hc|(b & Hb & B1 & B2)]].
          + clear - Hc H_TB H_THIS HCAPT H_SP; lia.
          + destruct Hc as [Hc _]; clear - Hc H_SP HU_TB HU_THIS HCAPT; unfold DJ in *; lia.
          + pose proof (Ubsan.RMalloc_ifaceP.RHEAP_block_range_proof s LB m b HR Hb) as (_ & _ & _ & Rb4 & _).
            destruct Ho as (Hw24 & _ & Ht & _); clear - B1 B2 Rb4 Ht Hw24 HCAPT Hlo1 Hlo2'; lia. }
      { rewrite FA4. exact FA2. }
      { rewrite SO4. exact SO2. }
      { exact HZ5. }
      { lia. }
      { reflexivity. }
    - (* [comment removed for export] *)
      destruct (xdel_regsBC U2N_defs.XDELC ZL30 E3 R3 (or_intror eq_refl) eq_refl Hg30 Hb30 HF3 HR3)
        as (y1 & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20 & y21 & y22 & y23 & y24 & y25 & y26 & y27 &
            y28 & y29 & y30 & y31 & ->).
      unfold ZL30; cbn [nth]. rewrite !Z_to_bv_bv_unsigned. change (ST.t_pc U2N_defs.XDELC) with 0x2d584.
      eapply Ubsan.F_stdio_exit.implM_post_evt'.
      { apply Stdio_pure.implM_from_evt. zstep. apply evt_done.
        eapply ODA with (p := c) (A := A) (n := zlength d - i0 + 64) (LB := (c, A, zlength d - i0 + 64) :: LB) (lo := lo) (B := B)
                        (errv := errv2).
        - exact HR3'.
        - left; reflexivity.
        - exact AUX3.
        - rewrite unsigned_lit by lia. lia.
        - rewrite unsigned_lit by lia. exact STK3a.
        - exact Hlo1.
        - rewrite unsigned_lit by lia. unfold RFREE_STACK. lia.
        - exact ERR3.
        - exact MI3.
        - exact HTP.
        - reflexivity. }
      intros [] st4 ms4 RP.
      destruct RP as (t0'' & t1'' & t2'' & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & t3'' & t4'' & t5'' & t6'' & m4 &
                      -> & MI4 & STK4 & ERR4 & AUX4 & PRES4 & FA4 & SO4 & HR4).
      rewrite unsigned_lit in STK4, PRES4 by lia. rewrite ND3 in PRES4, HR4.
      rewrite (ret_pc_even 0x2d588) by (lia || reflexivity).
      (* [comment removed for export] *)
      assert (M4_STK : stk usegs m4 lo (u sp)).
      { apply (stk_merge usegs m4 lo (u sp - 368) (u sp)); [exact STK4 | | lia].
        eapply rheap_pres_stk; [exact PRES4 | exact STK3b | lia]. }
      assert (M4_W24 : wr_at usegs m4 (THIS + 24) 4) by (eapply rheap_pres_wr_at; [exact PRES4 | exact M3_W24 | rcr_blk Ith]).
      assert (M4_TB : wr_at usegs m4 ATP (8 * (ntp / 8))) by (eapply rheap_pres_wr_at; [exact PRES4 | exact M3_TB | rcr_blk Itp]).
      assert (XW3 : forall n b k w v, nth_error (ST.t_know U2N_defs.XDELC) n = Some (KWord (SA b k) w v) ->
                   expr_vars_lt 30 b = true -> expr_vars_lt 30 v = true -> (zok b && zok v)%bool = true ->
                   rclient_range LB (u sp - 368) (zden ZL30 b mod M64 + k) (Z.of_nat (length (word_to_le_bytes w (Z_to_bv 64 (zden ZL30 v))))) ->
                   bytes_at usegs m4 (zden ZL30 b mod M64 + k) (word_to_le_bytes w (Z_to_bv 64 (zden ZL30 v)))).
      { intros n b k w v Hn H1 H2 H3 Hr. eapply rheap_pres_bytes_at; [exact PRES4 | | exact Hr].
        exact (kx_word_g usegs 30 ZL30 E3 m3 b k w v Hg30 Hb30 H1 H2 H3 (know_nth _ _ _ _ n _ HK3 Hn)). }
      assert (M4_SAVED : forall k, 0 <= k < 13 ->
        bytes_at usegs m4 (u sp - 8 - 8 * k) (word_to_le_bytes 8 (Z_to_bv 64 (nth (Z.to_nat k) [u ra; u s0; u s1; u s2; u s3; u s4; u s5; u s6; u s7; u s8; u s9; u s10; u s11] 0)))).
      { intros k Hk.
        assert (Hk' : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12) by lia.
        destruct Hk' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]]]]];
        match goal with |- bytes_at _ _ (_ - 8 - 8 * ?k) _ =>
          let n := eval vm_compute in (Z.to_nat (6 + k)) in
          pose proof (XW3 n _ _ _ _ eq_refl eq_refl eq_refl eq_refl) as H; unfold ZL30 in H;
          cbv [U2N_defs.vSP U2N_defs.vRA U2N_defs.vS0 U2N_defs.vS1 U2N_defs.vS2 U2N_defs.vS3 U2N_defs.vS4 U2N_defs.vS5 U2N_defs.vS6
               U2N_defs.vS7 U2N_defs.vS8 U2N_defs.vS9 U2N_defs.vS10 U2N_defs.vS11 U2N_defs.V] in H; cbn [zden nth app] in H;
          rewrite Z.mod_small in H by lia; cbn [nth Z.to_nat Pos.to_nat Pos.iter_op Nat.add];
          replace (u sp - 8 - 8 * k) with (u sp + (- 8 - 8 * k)) by lia; apply H; rewrite length_word_to_le_bytes; left; lia
        end. }
      pose proof (know_nth _ _ _ _ 3 _ HK3 eq_refl) as KRC. cbn [kentry_ok edenot U2N_defs.V] in KRC.
      assert (H_RC : 0 <= u (ev E3 30) <= 63) by exact KRC.
      pose proof (know_nth _ _ _ _ 4 _ HK3 eq_refl) as KTW1. pose proof (know_nth _ _ _ _ 5 _ HK3 eq_refl) as KTW2.
      cbn [kentry_ok edenot U2N_defs.V] in KTW1, KTW2.
      set (TW := u (ev E3 31)) in *.
      assert (H_TW : 8 <= TW <= 24 /\ TW mod 8 = 0) by (destruct KTW2; lia).
      assert (M4_F320 : bytes_at usegs m4 (u sp - 320) (word_to_le_bytes 8 (Z_to_bv 64 (ASI + 4)))).
      { pose proof (XW3 1%nat _ _ _ _ eq_refl eq_refl eq_refl eq_refl) as H. unfold ZL30 in H;
        cbv [U2N_defs.vSP U2N_defs.vIDX U2N_defs.V U2N_defs.add] in H; cbn [zden nth app] in H.
        rewrite Z.mod_small in H by lia. replace (u sp - 320) with (u sp + -320) by lia. apply H. rewrite length_word_to_le_bytes. left; lia. }
      assert (M4_F304 : bytes_at usegs m4 (u sp - 304) (word_to_le_bytes 8 (Z_to_bv 64 THIS))).
      { pose proof (XW3 2%nat _ _ _ _ eq_refl eq_refl eq_refl eq_refl) as H. unfold ZL30 in H;
        cbv [U2N_defs.vSP U2N_defs.vTHIS U2N_defs.V] in H; cbn [zden nth app] in H.
        rewrite Z.mod_small in H by lia. replace (u sp - 304) with (u sp + -304) by lia. apply H. rewrite length_word_to_le_bytes. left; lia. }
      assert (Hg32 : SP.gagree 32 (mkEZ (ZL30 ++ [u (ev E3 30); TW])) E3).
      { intros j Hj. destruct (Nat.lt_ge_cases j 30) as [L|G].
        - rewrite <- (Hg30 j L). cbn [ev mkEZ]. rewrite app_nth1 by (unfold ZL30; cbn [length]; lia). reflexivity.
        - assert (j = 30 \/ j = 31)%nat as [->| ->] by lia; cbn [ev mkEZ]; unfold ZL30; cbn [app nth]; unfold TW;
            apply Z_to_bv_bv_unsigned. }
      assert (M4_F328 : bytes_at usegs m4 (u sp - 328) (word_to_le_bytes 8 (Z_to_bv 64 (ATP + TW)))).
      { pose proof (kx_word_g usegs 32 (ZL30 ++ [u (ev E3 30); TW]) E3 m3 U2N_defs.vSP (-328) 8 (U2N_defs.add U2N_defs.vTBASE (U2N_defs.V 31)) Hg32
                      ltac:(rewrite <- Hb30; reflexivity) eq_refl eq_refl eq_refl (know_nth _ _ _ _ 0 _ HK3 eq_refl)) as H.
        unfold ZL30 in H; cbv [U2N_defs.vSP U2N_defs.vTBASE U2N_defs.V U2N_defs.add] in H; cbn [zden nth app] in H.
        rewrite Z.mod_small in H by lia. replace (u sp - 328) with (u sp + -328) by lia.
        eapply rheap_pres_bytes_at; [exact PRES4 | exact H | rewrite length_word_to_le_bytes; left; lia]. }
      assert (M4_O8 : rw_cells usegs m4 (THIS + 8) [C4 (Z_to_bv 64 (zlength (i0 :: idx')))])
        by (eapply rheap_pres_rw_cells; [exact PRES4 | exact M3_O8 | rcr_blk Ith]).
      assert (M4_O16 : rw_cells usegs m4 (THIS + 16) [C8 (Z_to_bv 64 ASI)])
        by (eapply rheap_pres_rw_cells; [exact PRES4 | exact M3_O16 | rcr_blk Ith]).
      assert (M4_DOC : rw_cells usegs m4 DOC [C8 (Z_to_bv 64 ATP); C8 (Z_to_bv 64 ASB)])
        by (eapply rheap_pres_rw_cells; [exact PRES4 | exact M3_DOC | left; lia]).
      assert (M4_O88 : bytes_at usegs m4 (THIS + 88) (word_to_le_bytes 8 (Z_to_bv 64 DOC)))
        by (eapply rheap_pres_bytes_at; [exact PRES4 | exact M3_O88 | rewrite length_word_to_le_bytes; rcr_blk Ith]).
      (* [comment removed for export] *)
      assert (KN4 : know_ok usegs (mkEZ (PU2_t0d.ZLD2 (u ra) (u sp) (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8)
                    (u s9) (u s10) (u s11) THIS DOC BUF (zlength d) ASI (zlength (i0 :: idx')) ATP (ntp / 8) ASB nsb AOC AIA (u (ev E3 30)) TW
                    [u (Z_to_bv 64 0x2d588); u t0''; u t1''; u t2''; u (Z_to_bv 64 A); u b0; u b1; u b2; u b3; u b4; u b5; u b6; u b7;
                     u y18; u y19; u y20; u y21; u y22; u y23; u y24; u y25; u y26; u y27; u t3''; u t4''; u t5''; u t6''])) m4 U2D_defs.DC_kn)
        by (eapply PU2_t0d.dC_kn; eassumption).
      eapply evt_cut.
      { eapply ExecF.evtF_evt.
        exact (u2d_runC (u ra) (u sp) (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9) (u s10)
                 (u s11) THIS DOC BUF (zlength d) ASI (zlength (i0 :: idx')) ATP (ntp / 8) ASB nsb AOC AIA  TW
                 (Z_to_bv 64 0x2d588) t0'' t1'' t2'' (ev E3 30) (Z_to_bv 64 A) b0 b1 b2 b3 b4 b5 b6 b7 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
                 t3'' t4'' t5'' t6'' gp tp F3 fc3 m4 eq_refl eq_refl ltac:(lia) KN4 MI4 HZ3). }
      intros ms5 HX5.
      destruct HX5 as (X5 & E5 & m5 & R5 & F5 & fc5 & HinX5 & -> & HZ5 & HF5 & HR5 & HK5 & HG5 & Hg5 & Hb5 & FR5 & WM5 & MI5 & STK5).
      cbn [SP.p_ex U2D_defs.U2D] in HinX5. destruct HinX5 as [<-|[]].
      pose proof (know_nth _ _ _ _ XRET_RC _ HK5 eq_refl) as KA0. cbn [kentry_ok] in KA0. change (U2D_defs.V 28) with (EVar 28) in KA0.
      destruct (u2d_xret_regs _ E5 R5 Hg5 (eq_sym Hb5) HF5 HR5)
        as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & ->).
      cbn [nth PU2_t0d.ZLD2 app]. rewrite !Z_to_bv_bv_unsigned. change (ST.t_pc U2D_defs.XRET) with 0x323b8.
      assert (MU5 : munch [(u sp - 368, u sp); (THIS + 24, THIS + 28); (ATP, ATP + 8 * (ntp / 8))] m4 m5)
        by (eapply u2d_munch; [| | | | exact FR5 | lia..]; reflexivity).
      clear FR5.
      eapply xret_post2 with (errv := errv2) (x10 := edenot E5 (EVar 28)).
      { eapply Ubsan.RMalloc_ifaceP.RHEAP_frame_proof; [exact HR4 | exact MU5 | exact WM5 |].
        repeat apply Forall_cons; [..| apply Forall_nil]; unfold rclient_write_ok; cbn [fst snd].
        - left. lia.
        - right; right. exists (pim, THIS, nim). cbn [fst snd blk_addr blk_size]. split; [exact Ith | lia].
        - right; right. exists (ptp, ATP, ntp). cbn [fst snd blk_addr blk_size]. split; [exact Itp | lia]. }
      { eapply Ubsan.RF_free_spec.rauxv_ok_pres_B with (C := fun a => u sp - 368 <= a < u sp \/ THIS + 24 <= a < THIS + 28 \/
                     ATP <= a < ATP + 8 * (ntp / 8)); [exact AUX4 | | |].
        - intros a Ha Hc; split; [apply MU5; rewrite unsigned_lit by (clear - Ha; lia); cbn [outside]; clear - Hc; lia|]; apply WM5.
        - intros a Ha Hc; clear - Ha Hc Hspb H_TB H_THIS HCAPT H_SP; lia.
        - intros a Ha Hc; unfold RAUXV_CELL in Ha; clear - Ha Hc HU_TB HU_THIS H_SP HCAPT; unfold DJ in *; lia. }
      { rewrite HTP, errno_lit in ERR4 |- *. eapply rw_cells_transport; [exact ERR4 | exact MU5 | exact WM5 |].
        unfold RERRNO. cbn [disjoint_from cells_size csize]. clear - HU_TB HU_THIS H_SP HCAPT; unfold DJ in *. lia. }
      { exact (STK5 _ _ M4_STK). }
      { exact MI5. }
      { eapply PW_trans; [exact PW3|]. eapply PW_trans.
        - eapply PW_of_pres with (LB' := LB) (SP' := u sp - 368); [exact PRES4 | lia | auto].
        - eapply PW_of_munch; [exact MU5 | exact WM5 |].
          intros a Ha Hc Ho. unfold WS, s2_win in Ho. cbn [outside] in Ho |- *.
          destruct Hc as [Hc|[Hc|(b & Hb & B1 & B2)]].
          + clear - Hc H_TB H_THIS HCAPT H_SP; lia.
          + destruct Hc as [Hc _]; clear - Hc H_SP HU_TB HU_THIS HCAPT; unfold DJ in *; lia.
          + pose proof (Ubsan.RMalloc_ifaceP.RHEAP_block_range_proof s LB m b HR Hb) as (_ & _ & _ & Rb4 & _).
            destruct Ho as (Hw24 & _ & Ht & _); clear - B1 B2 Rb4 Ht Hw24 HCAPT Hlo1 Hlo2'; lia. }
      { rewrite FA4. exact FA2. }
      { rewrite SO4. exact SO2. }
      { exact HZ5. }
      { lia. }
      { reflexivity. }
  Qed.
End XN.
