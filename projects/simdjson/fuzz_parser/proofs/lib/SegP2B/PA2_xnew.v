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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps SjStage1 SjS1Bytes SjInv.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AU_consts AU_iface AU_kit AU_parts_iface AU_client_kit AU_fuzz_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg SegLib SegBridge.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs PIosKit PIosKitA.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AHMB SFPB_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Entry S2G2.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import APC_mpres.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2B Require Import APS2_iface A2Lib PA2_kz PA2_reg PA2_exit PA2_xlib PA2_dk PA2_xnpw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2B Require PA2_t0c PA2_t0nf PA2_xsf PA2_xn0 PA2_xd1 PA2_xd2 PA2_xd3 PA2_xda PA2_xdb PA2_xdc.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegB2D Require B2D_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegB2N Require B2N_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegB2 Require B2_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Import ITree.Exc.
Open Scope Z_scope.
Local Notation u := bv_unsigned.
Local Notation M64 := 18446744073709551616.
Local Notation SH := 2147450880%Z (only parsing).

(* [comment removed for export] *)
Lemma dm8 : forall x, 0 <= x - 8 * (x / 8) <= 7. Proof. intros x. Z.div_mod_to_equations. lia. Qed.
Lemma dm8c : forall x, 0 <= 8 * ((x + 7) / 8) - x <= 7. Proof. intros x. Z.div_mod_to_equations. lia. Qed.
Lemma dm64 : forall x, 0 <= x - 64 * (x / 64) <= 63. Proof. intros x. Z.div_mod_to_equations. lia. Qed.
Lemma dm64c : forall x, 0 <= 64 * ((x + 63) / 64) - x <= 63. Proof. intros x. Z.div_mod_to_equations. lia. Qed.
Lemma dzp : forall x, 0 <= (8 - x mod 8) / 8 <= 1 /\ 1 <= x - 8 * (x / 8) + 8 * ((8 - x mod 8) / 8) <= 8.
Proof. intros x. Z.div_mod_to_equations. lia. Qed.

Section CANSEC. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma xnew_v2 : forall d idx E' m3,
  SG.gholds (gp2 bsegs d (idx ++ [zlength d; zlength d; 0])) E' m3 (ST.t_ghost B2_defs.XNEW) ->
  u (edenot E' (EVar 36)) = znth (idx ++ [zlength d; zlength d; 0]) 0.
Proof.
  intros d idx E' m3 HG3. unfold SG.gholds in HG3.
  pose proof (proj1 (Forall_forall _ _) HG3 (ST.GA 3 [ELit 0; B2_defs.V 36]) ltac:(cbn [ST.t_ghost B2_defs.XNEW In]; tauto)) as GT.
  cbn [ST.g_id ST.g_args map S2G2.gp2 edenot B2_defs.V] in GT. rewrite u_Z_to_bv in GT.
  destruct GT as (_ & _ & GT). change (0 mod M64 / 4) with 0 in GT. change (ev E' 36) with (edenot E' (EVar 36)) in GT.
  first [exact GT | exact (eq_sym GT)].
Qed.

Section XNB.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Hypothesis SF5 : stack_free_5_stmt AI fflag.
  Variables (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (s : APS) (LB : list ablock) (lo : Z) (d idx : list Z) (m : amem)
            (THIS TPA ntp SBA nsb AOC AIA : Z) (pim ptp psb poc pia : AsanCtrl.aptr) (nim noc nia : Z).
  Hypothesis Ith : In (HB pim THIS nim) LB.
  Hypothesis Hnim : 96 <= nim.
  Hypothesis Itp : In (HB ptp TPA ntp) LB.
  Hypothesis Isb : In (HB psb SBA nsb) LB.
  Hypothesis Ioc : In (HB poc AOC noc) LB.
  Hypothesis Hnoc : 8192 <= noc.
  Hypothesis Iia : In (HB pia AIA nia) LB.
  Hypothesis Hnia : 1024 <= nia.
  Hypothesis Sn : 1 <= zlength idx.
  Hypothesis HRS : rng RNG lo (al_top L - lo).
  Hypothesis Hlo1 : ATOP + 4096 <= lo.
  Hypothesis Hlo2 : lo <= u sp - STAGE2_STACK_A.
  Hypothesis Hsp16 : u sp mod 16 = 0.
  Hypothesis Hsptop : u sp + 16 < al_top L.
  Hypothesis NO5 : forall FA FN, ~ In (mkABlock (ABFake 5) FA FN) LB.
  Variables (SP16 T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG : Z) (rest : list Z).
  Let ZL : list Z := PA2_t0c.ZL_t0'' (u ra) SP16 (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9)
                       (u s10) (u s11) T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG rest.
  Variables (F SPAX : Z) (m2 : amem).
  Hypothesis E_SP : u sp = 16 * SP16.
  Hypothesis E_T8 : THIS = 8 * T8.
  Hypothesis E_TB8 : TPA = 8 * TB8.
  Hypothesis E_CAPT : ntp = 8 * CAPT.
  Hypothesis E_SB8 : SBA = 8 * SB8.
  Hypothesis E_CAPS : nsb = CAPS.
  Hypothesis E_OC8 : AOC = 8 * OC8.
  Hypothesis E_IA8 : AIA = 8 * IA8.
  Hypothesis E_F11 : F = 2048 * F11.
  Hypothesis E_PB : u sp - 416 - SPAX = 16 * PB.
  Hypothesis E_FLAG : FLAG = fflag L 5 F.
  Hypothesis B_T : 0 <= THIS /\ THIS + 96 < M64.
  Hypothesis B_TB : 0 <= TPA /\ TPA + ntp < M64 /\ 0 <= ntp.
  Hypothesis B_SB : 0 <= SBA /\ SBA + nsb < M64 /\ 0 <= nsb.
  Hypothesis B_OC : 0 <= AOC /\ AOC + 8192 < M64.
  Hypothesis B_IA : 0 <= AIA /\ AIA + 1024 < M64.
  Hypothesis HSPA32 : SPAX mod 32 = 0.
  Hypothesis HSPA : 416 <= u sp - SPAX <= 447.
  Hypothesis AH2 : AHEAP AI L RNG (aps_m s) (mkABlock (ABFake 5) F 2048 :: LB) m2.
  Hypothesis PRES2 : aheap_pres CI LB (u sp) m m2.
  Hypothesis STK2 : stk bsegs m2 lo (u sp).
  Hypothesis HFm : F mod 2048 = 0.
  Hypothesis HFb : ablk F (F + 2048).
  Hypothesis HFt : F + 2048 <= ATOP.
  Hypothesis HFL2 : rw_cells bsegs m2 (F + 2040) [C8 (Z_to_bv 64 (fflag L 5 F))].
  Hypothesis HSHF : forall a, aclient_addr CI LB SPAX a -> a < shad F \/ shad F + 256 <= a.
  (* [comment removed for export] *)
  Variables (psi pcp : AsanCtrl.aptr) (ASI ACP DOC BUF nsi ncp : Z) (x88 : word) (cls FA FN : Z) (tr0 : list Z).
  Hypothesis E_DOC8 : DOC = 8 * DOC8.
  Hypothesis E_B8 : BUF = 8 * B8 + BO.
  Hypothesis E_I8 : ASI = 8 * I8.
  Hypothesis E_LEN : LEN = zlength d.
  Hypothesis E_N : N = zlength idx.
  Hypothesis D_BO : 0 <= BO <= 7.
  Hypothesis D_BG : 0 <= LEN + BO + 64 - 8 * BG <= 7.
  Hypothesis D_IG : 0 <= 8 * IG - (4 * N + 12) <= 7.
  Hypothesis D_SG : 0 <= CAPS - 8 * SG <= 7.
  Hypothesis ND : List.NoDup [pim; psi; pcp; ptp; psb; poc; pia].
  Hypothesis Isi : In (HB psi ASI nsi) LB.
  Hypothesis Hnsi : 4 * zlength idx + 16 <= nsi.
  Hypothesis Icp : In (HB pcp ACP ncp) LB.
  Hypothesis Hb1 : ACP <= BUF.
  Hypothesis Hb2 : BUF + zlength d + 64 <= ACP + ncp.
  Hypothesis Hntp8 : ntp mod 8 = 0.
  Hypothesis Hntp : 8 * (zlength idx + 3) <= ntp <= 2^27.
  Hypothesis Hnsb3 : 5 * zlength d + 182 <= 3 * nsb.
  Hypothesis Hnsb : zlength d + 60 <= nsb <= 2^24.
  Hypothesis Hbuf : bytes_at bsegs m BUF (s1buf d).
  Hypothesis Hd : Forall (fun c => 0 <= c < 256) d.
  Hypothesis Hlen : zlength d + 64 <= 2^20.
  Hypothesis Hscan : scan d = (true, idx).
  Hypothesis HIDX : rw_cells bsegs m ASI [CB (4 * (length idx + 3)) (u32bytes (idx ++ [zlength d; zlength d; 0]))].
  Hypothesis HO8 : rw_cells bsegs m (THIS + 8) [C4 (Z_to_bv 64 (zlength idx))].
  Hypothesis HO16 : rw_cells bsegs m (THIS + 16) [C8 (Z_to_bv 64 ASI)].
  Hypothesis HO40 : rw_cells bsegs m (THIS + 40) [C8 (Z_to_bv 64 MAX_DEPTH); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Hypothesis HO56 : rw_cells bsegs m (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA); C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 (zlength d)); C8 x88].
  Hypothesis HDOC : rw_cells bsegs m DOC [C8 (Z_to_bv 64 TPA); C8 (Z_to_bv 64 SBA)].
  Hypothesis Hda : DOC mod 8 = 0.
  Hypothesis Ifk : In (mkABlock (ABFake cls) FA FN) LB.
  Hypothesis Hfk1 : FA <= DOC.
  Hypothesis Hfk2 : DOC + 16 <= FA + FN.
  Hypothesis Hfk3 : ablk FA (FA + FN).
  Hypothesis HCIMG : client_img m.
  Hypothesis HCI : forall iv, In iv client_ranges -> In iv CI.
  Hypothesis HUC : uchain m (al_top L) AFREE_PC (u sp) (u s0) (Nat.pred UDEPTH) tr0.
  Hypothesis Htr0 : (length tr0 <= 27)%nat.
  Hypothesis HS0 : u s0 < u sp \/ u sp + 16 <= u s0.
  Hypothesis Hra1 : 4096 <= u ra.
  Hypothesis Hra2 : u ra <> AFREE_PC.
  Hypothesis HTP : tp = Z_to_bv 64 ATP.
  Hypothesis HRI : rng_aimg RNG.
  Hypothesis HRIS : rng_aimg_sh RNG.
  Hypothesis HAOK : aps_ok L s.
  Hypothesis HFR : AFRESH (aps_m s).
  Hypothesis HDK : dk (aps_m s) < DWMAX.
  Hypothesis HRF : rng RNG F 2048.
  Hypothesis HRFS : rng RNG (shad F) 256.
  Hypothesis HDR : rng RNG DOC 16.
  Hypothesis HDSR : rng RNG (Z.shiftr DOC 3 + 2147450880) 2.
  Hypothesis R_STKSH : rng RNG (2 * SP16 + SH - 1080) 1080.
  (* [comment removed for export] *)
  Hypothesis ODAW : opdelete_arr_wild_stmtA AI.
  Local Notation IDXS := (idx ++ [zlength d; zlength d; 0]).
  Local Notation LB6 := (mkABlock (ABFake 5) F 2048 :: LB).
  (* [comment removed for export] *)
  Hypothesis SFPCBS_ok : forall RNG4 st4 p COPY n, fp_le RNG RNG4 ->
    SP.summ_okHSC bsegs (gp2 bsegs d IDXS) (AHMB.hmH AI L RNG4 st4 (HB p COPY n :: LB6)) (AHMB.hmA AI (HB p COPY n :: LB6))
      (AHMB.hmC AI (HB p COPY n :: LB6)) AHMB.hmR (AHMB.hmF RNG4) (AHMB.hmS L RNG4) SFPCBS.
  Hypothesis PFFCBS_ok : forall RNG4 st4 p COPY n, fp_le RNG RNG4 ->
    SP.summ_okHSC bsegs (gp2 bsegs d IDXS) (AHMB.hmH AI L RNG4 st4 (HB p COPY n :: LB6)) (AHMB.hmA AI (HB p COPY n :: LB6))
      (AHMB.hmC AI (HB p COPY n :: LB6)) AHMB.hmR (AHMB.hmF RNG4) (AHMB.hmS L RNG4) PFFCBS.
  (* [comment removed for export] *)
  Variables (E' : env) (m3 : amem) (R3 F3 : bvmap 5 word) (fc3 : bv 32).
  Hypothesis Hg : SP.gagree 35 (mkEZ ZL) E'.
  Hypothesis Hb : eb E' = eb (mkEZ ZL).
  Hypothesis HF3 : rfull R3.
  Hypothesis HR3 : regs_ok E' (ST.t_regs B2_defs.XNEW) R3.
  Hypothesis HK3 : know_ok bsegs E' m3 (ST.t_know B2_defs.XNEW).
  Hypothesis HG3 : SG.gholds (gp2 bsegs d IDXS) E' m3 (ST.t_ghost B2_defs.XNEW).
  (* [comment removed for export] *)
  Hypothesis AH3 : AHEAP AI L RNG (aps_m s) LB6 m3.
  Hypothesis PW3 : aheap_pres_W CI LB (u sp) (s2_winA THIS TPA ntp SBA nsb AOC AIA) m m3.
  Hypothesis MI3 : mem_inv bsegs m3.
  Hypothesis STK3 : forall lo hi, stk bsegs m2 lo hi -> stk bsegs m3 lo hi.
  Hypothesis HZ3 : frm0 fc3.
  Hypothesis HV2 : u (edenot E' (EVar 36)) = znth IDXS 0.

  Local Notation XR k := (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) k)) (only parsing).
  Notation Q := (s2_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo (s2_winA THIS TPA ntp SBA nsb AOC AIA) m).

  (* [comment removed for export] *)
  Lemma xnb_i0 : 0 <= znth idx 0 /\ zlength d - znth idx 0 >= 1 /\ u (edenot E' (EVar 35)) = znth idx 0 /\ u (edenot E' (EVar 36)) = znth idx 0.
  Proof using All.
    assert (Z0 : znth IDXS 0 = znth idx 0).
    { clear - Sn. destruct idx as [|x idx']; [exfalso; unfold zlength in Sn; cbn [length Z.of_nat] in Sn; lia | reflexivity]. }
    assert (KV : kentry_ok bsegs E' m3 (KRange (B2_defs.V 35) 0 1048512)).
    { apply (proj1 (Forall_forall _ _) HK3). cbn [ST.t_know B2_defs.XNEW B2_defs.XNEW_kn]. repeat (first [left; reflexivity | right]). }
    assert (KLV : kentry_ok bsegs E' m3 (KRange (B2_defs.sub B2_defs.vLEN (B2_defs.V 35)) 1 1048512)).
    { apply (proj1 (Forall_forall _ _) HK3). cbn [ST.t_know B2_defs.XNEW B2_defs.XNEW_kn]. repeat (first [left; reflexivity | right]). }
    cbn [kentry_ok] in KV, KLV. cbv [B2_defs.V B2_defs.sub B2_defs.vLEN] in KV, KLV.
    change (edenot E' (EAlu ALU_SUB (EVar 19) (EVar 35))) with (alu64 ALU_SUB (edenot E' (EVar 19)) (edenot E' (EVar 35))) in KLV.
    assert (ELEN : edenot E' (EVar 19) = Z_to_bv 64 LEN).
    { rewrite <- (SP.edenot_gagree 35 (mkEZ ZL) E' (EVar 19) Hg (eq_sym Hb) eq_refl). reflexivity. }
    rewrite alu_sub, ELEN in KLV. unfold v_sub in KLV. rewrite !u_Z_to_bv in KLV.
    pose proof (u_rngE (edenot E' (EVar 35))) as RV.
    unfold SG.gholds in HG3.
    pose proof (proj1 (Forall_forall _ _) HG3 (ST.GA 3 [ELit 0; B2_defs.V 35]) ltac:(cbn [ST.t_ghost B2_defs.XNEW In]; tauto)) as GT.
    cbn [ST.g_id ST.g_args map S2G2.gp2 edenot B2_defs.V] in GT. rewrite u_Z_to_bv in GT.
    destruct GT as (_ & _ & GT). change (0 mod M64 / 4) with 0 in GT. change (ev E' 35) with (edenot E' (EVar 35)) in GT.
    rewrite Z0 in GT. pose proof HV2 as HV2'. rewrite Z0 in HV2'.
    assert (LEN0 : 0 <= LEN) by (rewrite E_LEN; unfold zlength; lia).
    assert (HlenL : LEN + 64 <= 2^20) by (rewrite E_LEN; exact Hlen).
    assert (HI0 : 0 <= znth idx 0 /\ LEN - znth idx 0 >= 1)
      by (first [rewrite <- GT | rewrite GT]; clear - KV KLV RV HlenL LEN0; Z.div_mod_to_equations; lia).
    rewrite <- E_LEN. split; [lia|]. split; [lia|]. split; [first [exact GT | exact (eq_sym GT)] | exact HV2'].
  Qed.

  (* [comment removed for export] *)
  Ltac ezg e := rewrite <- (SP.edenot_gagree 35 (mkEZ ZL) E' e Hg (eq_sym Hb) eq_refl), zden_ok by reflexivity; unfold ZL; cbn [zden nth PA2_t0c.ZL_t0'' app].
  Lemma xnew_regs :
    XR 2 = Z_to_bv 64 SPAX /\ XR 3 = gp /\ XR 4 = tp /\ XR 8 = sp /\ XR 9 = Z_to_bv 64 SPAX /\
    XR 18 = Z_to_bv 64 (I8 + SH) /\ XR 19 = Z_to_bv 64 (256 * F11 + SH) /\ XR 21 = Z_to_bv 64 SH /\ XR 22 = Z_to_bv 64 (T8 + SH + 10) /\
    XR 24 = Z_to_bv 64 (BUF + znth idx 0) /\ XR 25 = Z_to_bv 64 (THIS + 80) /\ XR 26 = Z_to_bv 64 F /\ XR 27 = Z_to_bv 64 ASI.
  Proof using All.
    destruct xnb_i0 as (_ & _ & GT & _).
    assert (ESPA0 : 16 * SP16 + -416 - 16 * PB = SPAX) by lia.
    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]]]].
    - change (sr_get (ST.t_regs B2_defs.XNEW) 2) with (EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 1)) (ELit (-416))) (EMd M_MUL (ELit 16) (EVar 29))).
      ezg (EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 1)) (ELit (-416))) (EMd M_MUL (ELit 16) (EVar 29))). rewrite ESPA0. reflexivity.
    - change (sr_get (ST.t_regs B2_defs.XNEW) 3) with (EVar 2). ezg (EVar 2). apply Z_to_bv_bv_unsigned.
    - change (sr_get (ST.t_regs B2_defs.XNEW) 4) with (EVar 3). ezg (EVar 3). apply Z_to_bv_bv_unsigned.
    - change (sr_get (ST.t_regs B2_defs.XNEW) 8) with (EMd M_MUL (ELit 16) (EVar 1)). ezg (EMd M_MUL (ELit 16) (EVar 1)).
      rewrite <- E_SP. apply Z_to_bv_bv_unsigned.
    - change (sr_get (ST.t_regs B2_defs.XNEW) 9) with (EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 1)) (ELit (-416))) (EMd M_MUL (ELit 16) (EVar 29))).
      ezg (EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 1)) (ELit (-416))) (EMd M_MUL (ELit 16) (EVar 29))). rewrite ESPA0. reflexivity.
    - change (sr_get (ST.t_regs B2_defs.XNEW) 18) with (EAlu ALU_ADD (EAlu ALU_ADD (EVar 20) (ELit 0)) (ELit 2147450880)).
      ezg (EAlu ALU_ADD (EAlu ALU_ADD (EVar 20) (ELit 0)) (ELit 2147450880)). f_equal. lia.
    - change (sr_get (ST.t_regs B2_defs.XNEW) 19) with (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 28)) (ELit 2147450880)).
      ezg (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 28)) (ELit 2147450880)). reflexivity.
    - change (sr_get (ST.t_regs B2_defs.XNEW) 21) with (ELit 2147450880). reflexivity.
    - change (sr_get (ST.t_regs B2_defs.XNEW) 22) with (EAlu ALU_ADD (EAlu ALU_ADD (EVar 16) (ELit 2147450880)) (ELit 10)).
      ezg (EAlu ALU_ADD (EAlu ALU_ADD (EVar 16) (ELit 2147450880)) (ELit 10)). reflexivity.
    - change (sr_get (ST.t_regs B2_defs.XNEW) 24) with (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 18)) (EVar 31)) (EVar 35)).
      change (edenot E' (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 18)) (EVar 31)) (EVar 35)))
        with (alu64 ALU_ADD (edenot E' (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 18)) (EVar 31))) (edenot E' (EVar 35))).
      rewrite alu_add. unfold v_add. rewrite GT.
      ezg (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 18)) (EVar 31)). rewrite u_Z_to_bv. apply Z_to_bv_congr. rewrite <- E_B8.
      rewrite Zplus_mod_idemp_l. reflexivity.
    - change (sr_get (ST.t_regs B2_defs.XNEW) 25) with (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 16)) (ELit 16)) (ELit 64)).
      ezg (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 16)) (ELit 16)) (ELit 64)). rewrite E_T8. f_equal. lia.
    - change (sr_get (ST.t_regs B2_defs.XNEW) 26) with (EMd M_MUL (ELit 2048) (EVar 28)). ezg (EMd M_MUL (ELit 2048) (EVar 28)).
      rewrite <- E_F11. reflexivity.
    - change (sr_get (ST.t_regs B2_defs.XNEW) 27) with (EMd M_MUL (ELit 8) (EVar 20)). ezg (EMd M_MUL (ELit 8) (EVar 20)).
      rewrite <- E_I8. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma xnb : forall p s' RNG' ms',
    opnew_postA AI L RNG (Z_to_bv 64 0x9b528) (XR 2) (XR 3) (XR 4) (XR 8) (XR 9) (XR 18) (XR 19) (XR 20) (XR 21) (XR 22) (XR 23) (XR 24)
      (XR 25) (XR 26) (XR 27) F3 fc3 s LB6 (zlength d - znth idx 0 + 64) lo m3 p s' RNG' ms' ->
    DK 0 s s' ->
    implMA RNG' (HarnessP.opdelete afree_M p) s' Q ms'.
  Proof using All.
    intros p s' RNG' ms' HP HD.
    destruct xnb_i0 as (HI0a & HI0b & GT & HV2').
    destruct xnew_regs as (ESPA & EGP & ETP & ES0 & ES1 & E18 & E19 & E21 & E22 & E24 & E25 & E26 & E27).
    destruct HP as (FPL4 & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m4 & COPY & junk & -> & MI4 & STK4 & PRES4
                    & APS4 & ABRB & AH4 & CB4 & RC4 & RCS4).
    pose proof (u_rngE sp) as Rsp. pose proof Hlo2 as Hlo2'. unfold STAGE2_STACK_A in Hlo2'. atop_facts.
    pose proof (AI_layout AI _ _ _ _ _ AH2) as (_ & _ & HTOP & _).
    assert (Hsp47 : u sp <= 2 ^ 47) by (clear - HTOP Hsptop; lia).
    assert (USPA : u (Z_to_bv 64 SPAX) = SPAX) by (rewrite u_Z_to_bv; apply Z.mod_small; clear - HSPA Rsp Hlo1 Hlo2'; atop_facts; lia).
    rewrite ESPA, USPA in STK4, PRES4.
    rewrite ESPA, EGP, ETP, ES0, ES1, E18, E19, E21, E22, E24, E25, E26, E27.
    assert (ERP : ret_pc (Z_to_bv 64 0x9b528) = Z_to_bv 64 0x9b528) by (apply bv_eq; vm_compute; reflexivity).
    rewrite ERP.
    set (x20 := XR 20). set (x23 := XR 23).
    set (i0 := znth idx 0) in *.
    clearbody x20 x23.
    (* [comment removed for export] *)
    destruct ABRB as (ABk & ABn & ABt & ABm).
    pose (CP8 := COPY / 8). pose (CGF := (LEN - i0 + 64) / 8). pose (ZP := (8 - (LEN - i0 + 64) mod 8) / 8).
    pose (DG := (LEN - i0 + 7) / 8). pose (SD := (BO + i0) / 8). pose (SRG := (BO + LEN - 8 * SD + 7) / 8).
    pose (HC := COPY / 64). pose (HCE := (COPY + (LEN - i0 + 64) + 63) / 64). pose (HBG := (BUF + i0) / 64).
    pose (HBGE := (BUF + LEN + 63) / 64). pose (MD := (LEN - i0) / 8).
    assert (E_CP8 : COPY = 8 * CP8) by (unfold CP8; clear - ABm; Z.div_mod_to_equations; lia).
    pose proof (dm8 (LEN - i0 + 64)) as D_CGF. pose proof (dzp (LEN - i0 + 64)) as D_ZP. pose proof (dm8c (LEN - i0)) as D_DG.
    pose proof (dm8 (BO + i0)) as D_SD. pose proof (dm8c (BO + LEN - 8 * SD)) as D_SRG. pose proof (dm64 COPY) as D_HC.
    pose proof (dm64c (COPY + (LEN - i0 + 64))) as D_HCE. pose proof (dm64 (BUF + i0)) as D_HBG. pose proof (dm64c (BUF + LEN)) as D_HBGE.
    pose proof (dm8 (LEN - i0)) as D_MD.
    change (0 <= LEN - i0 + 64 - 8 * CGF <= 7) in D_CGF.
    change (0 <= ZP <= 1 /\ 1 <= LEN - i0 + 64 - 8 * CGF + 8 * ZP <= 8) in D_ZP.
    change (0 <= 8 * DG - (LEN - i0) <= 7) in D_DG. change (0 <= BO + i0 - 8 * SD <= 7) in D_SD.
    change (0 <= 8 * SRG - (BO + LEN - 8 * SD) <= 7) in D_SRG. change (0 <= COPY - 64 * HC <= 63) in D_HC.
    change (0 <= 64 * HCE - (COPY + (LEN - i0 + 64)) <= 63) in D_HCE. change (0 <= BUF + i0 - 64 * HBG <= 63) in D_HBG.
    change (0 <= 64 * HBGE - (BUF + LEN) <= 63) in D_HBGE. change (0 <= LEN - i0 - 8 * MD <= 7) in D_MD.
    pose (rest4 := [0x9b528; u t0; u t1; u t2; u a1; u a2; u a3; u a4; u a5; u a6; u a7; u x20; u x23; u t3; u t4; u t5; u t6]).
    (* [comment removed for export] *)
    pose proof (s1_n _ _ _ (scan_S1OUT d idx Hscan)) as Sn2.
    pose proof (STK3 _ _ STK2) as STK3'.
    assert (HV2'' : u (edenot E' (EVar 36)) = i0) by exact HV2'. clear HV2'. rename HV2'' into HV2'.
    assert (HI0 : 0 <= i0 /\ zlength d - i0 >= 1) by (split; assumption).
    assert (R_STK4 : rng RNG' (16 * SP16 - 8640) 8640)
      by (eapply rng_sub'; [exact (rng_fp_le _ _ _ _ FPL4 HRS) | clear - Hlo1 Hlo2' E_SP Hsptop; lia]).
    pose proof (rng_fp_le _ _ _ _ FPL4 R_STKSH) as R_STKSH4.
    pose proof (rng_fp_le _ _ _ _ FPL4 HRI) as HRI4. pose proof (rng_fp_le _ _ _ _ FPL4 HRIS) as HRIS4.
    assert (R_D4 : rng RNG' (8 * DOC8) 16) by (rewrite <- E_DOC8; exact (rng_fp_le _ _ _ _ FPL4 HDR)).
    assert (R_DS4 : rng RNG' (DOC8 + SH) 2).
    { pose proof (rng_fp_le _ _ _ _ FPL4 HDSR) as X. rewrite Z.shiftr_div_pow2 in X by (clear; lia). change (2 ^ 3) with 8 in X.
      rewrite E_DOC8, Z.mul_comm, Z_div_mult in X by (clear; lia). exact X. }
    assert (R_F4 : rng RNG' (2048 * F11) 2048) by (rewrite <- E_F11; exact (rng_fp_le _ _ _ _ FPL4 HRF)).
    assert (ESF : shad F = 256 * F11 + SH) by (rewrite shad_div; unfold ASHOFF; rewrite E_F11; clear; Z.div_mod_to_equations; lia).
    assert (R_FS4 : rng RNG' (256 * F11 + SH) 256) by (rewrite <- ESF; exact (rng_fp_le _ _ _ _ FPL4 HRFS)).
    pose proof (rng_fp_le _ _ _ _ FPL4 HRS) as HRS4.
    pose proof (SFPCBS_ok RNG' (aps_m s') p COPY (zlength d - i0 + 64) FPL4) as SFP.
    pose proof (PFFCBS_ok RNG' (aps_m s') p COPY (zlength d - i0 + 64) FPL4) as PFF.
    (* [comment removed for export] *)
    pose proof (PA2_xn0.a2n_evt4 AI fflag L RNG RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m m3 m4 (aps_m s) (aps_m s') LB lo d idx i0 pim psi pcp ptp psb poc pia THIS ASI
              ACP TPA SBA AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia x88 cls FA FN F SPAX rest rest4 E' p COPY junk SP16 T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8
              IA8 F11 PB FLAG BO BG IG SG i0 CP8 CGF ZP DG SD SRG HC HCE HBG HBGE MD E_SP E_T8 E_DOC8 E_B8 E_I8 E_TB8 E_SB8 E_OC8 E_IA8 E_F11 E_CP8 E_LEN E_N E_CAPT
              E_CAPS E_PB E_FLAG (eq_refl i0) D_BO D_BG D_IG D_SG D_CGF D_ZP D_DG D_SD D_SRG D_HC D_HCE D_HBG D_HBGE D_MD ND Ith Hnim Isi Hnsi Icp Hb1 Hb2 Itp Isb
              Ioc Hnoc Iia Hnia Hntp8 Hntp Hnsb3 Hnsb Hbuf Hlen Sn2 HO8 HO16 HO40 HO56 HDOC Hda Ifk Hfk1 Hfk2 Hfk3 HCIMG HCI Hlo1 Hlo2 Hsp16 Hsp47 HTP AH3 PW3
              HSPA32 HSPA HFm HFb HFt Hg Hb HK3 HV2' (eq_refl i0) HI0 STK3' MI4 STK4 PRES4 AH4 CB4 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x20 x23 t3 t4 t5 t6 F3 fc3
              (eq_refl rest4) HZ3 Hd Hscan HIDX R_STK4 R_STKSH4 HRI4 HRIS4 R_D4 R_DS4 R_F4 R_FS4 SFP PFF HRS4 Hsptop) as EV4.
    pose proof (PA2_xn0.a2d_wins4 AI fflag L RNG RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m m3 m4 (aps_m s) (aps_m s') LB lo d idx i0 pim psi pcp ptp psb poc pia THIS ASI
              ACP TPA SBA AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia x88 cls FA FN F SPAX rest rest4 E' p COPY junk SP16 T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8
              IA8 F11 PB FLAG BO BG IG SG i0 CP8 CGF ZP DG SD SRG HC HCE HBG HBGE MD E_SP E_T8 E_DOC8 E_B8 E_I8 E_TB8 E_SB8 E_OC8 E_IA8 E_F11 E_CP8 E_LEN E_N E_CAPT
              E_CAPS E_PB E_FLAG (eq_refl i0) D_BO D_BG D_IG D_SG D_CGF D_ZP D_DG D_SD D_SRG D_HC D_HCE D_HBG D_HBGE D_MD ND Ith Hnim Isi Hnsi Icp Hb1 Hb2 Itp Isb
              Ioc Hnoc Iia Hnia Hntp8 Hntp Hnsb3 Hnsb Hbuf Hlen Sn2 HO8 HO16 HO40 HO56 HDOC Hda Ifk Hfk1 Hfk2 Hfk3 HCIMG HCI Hlo1 Hlo2 Hsp16 Hsp47 HTP AH3 PW3
              HSPA32 HSPA HFm HFb HFt Hg Hb HK3 HV2' (eq_refl i0) HI0 STK3' MI4 STK4 PRES4 AH4 CB4 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x20 x23 t3 t4 t5 t6 F3 fc3
              (eq_refl rest4) HZ3 Hd Hscan HIDX R_STK4 R_STKSH4 HRI4 HRIS4 R_D4 R_DS4 R_F4 R_FS4 SFP PFF HRS4 Hsptop) as WIN_D.
    eapply (implMA_evtF RNG' _ s' Q _ _ EV4).
    intros ms5 (X & E5 & m5 & R5 & F5 & fc5 & HinX & -> & HZ5 & HF5 & HR5 & HK5 & HG5 & Hg5 & Hb5 & HH5 & FO5 & WM5 & MI5 & STKP5).
    (* [comment removed for export] *)
    pose (ZL4 := PA2_t0nf.ZL_t0n''''' (u ra) SP16 (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9)
                   (u s10) (u s11) T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG i0 CP8 CGF ZP DG SD SRG HC HCE HBG HBGE MD rest4).
    change (SP.gagree 47 (mkEZ ZL4) E5) in Hg5. change (eb E5 = eb (mkEZ ZL4)) in Hb5.
    assert (HCOPY : 0x671000 <= COPY < 2^47) by (clear - ABk ABt ABn; unfold ablk, AIMG_HI, KLS in ABk; atop_facts; lia).
    assert (M_STK4 : stk bsegs m4 lo (u sp)).
    { apply (stk_merge bsegs m4 lo SPAX (u sp)); [exact STK4 | | clear - HSPA Hlo1 Hlo2'; lia].
      destruct (stk_split bsegs m3 lo SPAX (u sp) STK3' ltac:(clear - HSPA Hlo1 Hlo2'; lia)) as [_ SU].
      eapply aheap_pres_stk; [exact PRES4 | exact SU | clear; lia | clear - Hsp47; lia]. }
    pose proof (STKP5 _ _ M_STK4) as STK5.
    assert (PW34 : aheap_pres_W CI LB (u sp) (s2_winA THIS TPA ntp SBA nsb AOC AIA) m3 m4).
    { eapply (aheap_pres_W_weaken CI LB6 LB SPAX (u sp) _ _ m3 m4); [apply aheap_pres_W_of_pres; exact PRES4 | clear - HSPA; lia | | ].
      - intros b Hb'. right. exact Hb'.
      - intros a Ha. exact Ha. }
    assert (H_PB : 0 <= PB <= 1) by (clear - E_PB HSPA; lia).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH4 (or_intror (or_intror Ith))) as (_ & Ht0 & Ht1 & Ht2 & _).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH4 (or_intror (or_intror Itp))) as (_ & Hp0 & Hp1 & Hp2 & Hp3).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH4 (or_intror (or_intror Isb))) as (_ & Hs0 & Hs1 & Hs2 & Hs3).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH4 (or_intror (or_intror Ioc))) as (_ & Ho0 & Ho1 & Ho2 & _).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH4 (or_intror (or_intror Iia))) as (_ & Ha0 & Ha1 & Ha2 & _).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH4 (or_intror (or_intror Isi))) as (_ & Hi0' & Hi1' & Hi2' & _).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH4 (or_intror (or_intror Icp))) as (_ & Hc0 & Hc1 & Hc2 & _).
    assert (HFN : 0 <= FN) by (clear - Hfk1 Hfk2; lia).
    pose proof (fake_band FA FN Hfk3 HFN) as (_ & Hf0 & Hf1).
    assert (FR45 : forall a, 0 <= a < M64 ->
              outside [(u sp - 8640, u sp); (THIS + 24, THIS + 28); (THIS + 88, THIS + 96); (TPA, TPA + ntp); (SBA, SBA + nsb);
                       (AOC, AOC + 8192); (AIA, AIA + 1024); (F, F + 2048); (shad F, shad F + 256); (COPY, COPY + (zlength d - i0 + 64))] a ->
              (SPAX <= a < 2^47 \/ AHMB.hmA AI (HB p COPY (zlength d - i0 + 64) :: LB6) a) -> m5 (wa a) = m4 (wa a)).
    { intros a Ha HO HPa.
      eapply (a2n_frame AI (HB p COPY (zlength d - i0 + 64) :: LB6) (u ra) SP16 (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5)
                (u s6) (u s7) (u s8) (u s9) (u s10) (u s11) T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG
                i0 CP8 CGF ZP DG SD SRG HC HCE HBG HBGE MD rest4 m4 m5);
      [ clear - E_SP Hlo1 Hlo2' Hsp47; atop_facts; lia
      | clear - E_T8 Ht0 Ht1 Hnim; atop_facts; lia
      | clear - E_TB8 E_CAPT Hp0 Hp1 Hp3; atop_facts; lia
      | clear - E_CAPT Hp3; lia
      | clear - E_SB8 E_CAPS Hs0 Hs1 Hs3; atop_facts; lia
      | clear - E_CAPS Hs3; lia
      | clear - E_OC8 Ho0 Ho1 Hnoc; atop_facts; lia
      | clear - E_IA8 Ha0 Ha1 Hnia; atop_facts; lia
      | clear - E_F11 HFb HFt; unfold ablk, AIMG_HI, KLS in HFb; atop_facts; lia
      | clear - E_F11 HFb HFt; unfold ablk, AIMG_HI, KLS in HFb; atop_facts; lia
      | exact H_PB
      | clear - E_CP8 ABk ABt ABn E_LEN; unfold ablk, AIMG_HI, KLS in ABk; atop_facts; lia
      | clear - HI0 E_LEN; lia
      | exact FO5
      | exact Ha
      | rewrite <- E_SP, <- E_T8, <- E_TB8, <- E_CAPT, <- E_SB8, <- E_CAPS, <- E_OC8, <- E_IA8, <- E_F11, <- ESF, <- E_CP8, E_LEN; exact HO
      | replace (16 * SP16 - 416 - 16 * PB) with SPAX by (clear - E_PB E_SP; lia); exact HPa ]. }
    pose proof (a2n_pres_W AI L RNG' (aps_m s') LB m4 m5 (u sp) SPAX F COPY (zlength d - i0 + 64) THIS TPA ntp SBA nsb AOC AIA p
                  AH4 NO5 HFb HFt ltac:(clear - Hlo1 Hlo2'; lia) Hsp47 ltac:(clear - HSPA; lia) HSHF FR45 WM5) as PW45.
    assert (PW5 : aheap_pres_W CI LB (u sp) (s2_winA THIS TPA ntp SBA nsb AOC AIA) m m5)
      by (eapply aheap_pres_W_trans; [eapply aheap_pres_W_trans; [exact PW3 | exact PW34] | exact PW45]).
    assert (HABV : forall a, u sp <= a < al_top L -> m5 (wa a) = m (wa a)).
    { intros a Ha.
      assert (OW : outside (s2_winA THIS TPA ntp SBA nsb AOC AIA) a).
      { unfold s2_winA. cbn [outside]. clear - Ha Ht1 Hp1 Hs1 Ho1 Ha1 Hlo1 Hlo2' E_CAPT E_CAPS Hnim Hnoc Hnia Hp3 Hs3 Hsptop.
        atop_facts. repeat split; lia. }
      exact (proj1 (PW5 a ltac:(clear - Ha Hsptop HTOP Hlo1 Hlo2'; atop_facts; lia) ltac:(left; clear - Ha Hsptop HTOP; lia) OW)). }
    assert (H_SP : 0x7fff00000000 <= u sp <= 2^47) by (clear - Hlo1 Hlo2' Hsp47; atop_facts; lia).
    assert (H_LEN : 1 <= LEN <= 1048512) by (clear - Sn2 Hlen E_LEN; lia).
    assert (H_N : 1 <= N <= LEN) by (clear - Sn2 E_LEN E_N; lia).
    assert (H_SZ : 0 <= CAPT /\ 0 <= CAPS) by (clear - E_CAPT E_CAPS Hp3 Hs3; lia).
    assert (Hnsi' : 4 * N + 12 <= nsi) by (clear - Hnsi E_N; lia).
    assert (Hb2' : BUF + LEN + 64 <= ACP + ncp) by (clear - Hb2 E_LEN; lia).
    assert (B_ALL : 0x671000 <= THIS /\ THIS + 96 <= ATOP /\ 0x671000 <= DOC /\ DOC + 16 <= ATOP /\ 0x671000 <= BUF /\ BUF + LEN + 64 <= ATOP
                  /\ 0x671000 <= ASI /\ ASI + 4 * N + 12 <= ATOP /\ 0x671000 <= TPA /\ TPA + 8 * CAPT <= ATOP /\ 0x671000 <= SBA /\ SBA + CAPS <= ATOP
                  /\ 0x671000 <= AOC /\ AOC + 8192 <= ATOP /\ 0x671000 <= AIA /\ AIA + 1024 <= ATOP /\ 0x671000 <= F /\ F + 2048 <= ATOP).
    { clear - Ht0 Ht1 Hnim Hf0 Hf1 Hfk1 Hfk2 Hc0 Hc1 Hb1 Hb2' Hi0' Hi1' Hnsi' Hp0 Hp1 E_CAPT Hs0 Hs1 E_CAPS Ho0 Ho1 Hnoc Ha0 Ha1 Hnia HFb HFt.
      unfold ablk, AIMG_HI, KLS in HFb. atop_facts. repeat split; lia. }
    pose proof (aps_ok_rest L s' s APS4 HAOK) as HAOK'.
    assert (HDK' : dk (aps_m s') < DWMAX) by (destruct HD as [HD _]; destruct (HD HFR) as [_ XD]; clear - XD HDK; lia).
    pose proof (proj1 HH5) as AH5.
    cbn [SP.p_ex B2N_defs.B2N SP.PGH] in HinX. destruct HinX as [<-|[<-|[<-|[]]]].
    - (* [comment removed for export] *)
      exact (PA2_xd1.xdel1_call AI ODAW L RNG' ra sp gp tp s0 m m5 s' LB lo tr0 F COPY (zlength d - i0 + 64) SPAX p E5 R5 F5 fc5 SP16 PB ZL4 E_SP E_PB HSPA HSPA32 eq_refl eq_refl
                eq_refl eq_refl eq_refl eq_refl (eq_sym E_CP8) HCOPY HUC Htr0 HS0 Hra1 Hra2 Hsp16 Hsptop HTP Hlo1 Hlo2 HRS4 HAOK' HDK' Hg5 Hb5 HF5 HR5 HK5 HH5 STK5
                HABV Q (PA2_xda.xda_cont AI fflag SF5 L RNG RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s s' LB lo m m5 pim psi pcp ptp psb poc pia THIS ASI ACP TPA SBA AOC AIA DOC
                  BUF nim nsi ncp ntp nsb noc nia cls FA FN F SPAX COPY (zlength d - i0 + 64) p E5 F5 fc5 SP16 T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG
                  BO BG IG SG i0 CP8 CGF ZP DG SD SRG HC HCE HBG HBGE MD rest4 E_SP E_T8 E_DOC8 E_B8 E_I8 E_TB8 E_SB8 E_OC8 E_IA8 E_F11 E_CAPT E_CAPS E_PB E_FLAG D_BO
                  H_SZ H_LEN H_N H_SP B_ALL Ith Hnim Isi Hnsi' Icp Hb1 Hb2' Itp Isb Ioc Hnoc Iia Hnia Ifk Hfk1 Hfk2 HCI NO5 Hlo1 Hlo2 Hsp16 Hsptop HSPA32 HSPA HFm HFb
                  HFt HSHF Hg5 Hb5 HK5 AH5 STK5 PW5 HZ5 FPL4 HRS4 WIN_D APS4)).
    - (* [comment removed for export] *)
      exact (PA2_xd2.xdel2_call AI ODAW L RNG' ra sp gp tp s0 m m5 s' LB lo tr0 F COPY (zlength d - i0 + 64) SPAX p E5 R5 F5 fc5 SP16 PB ZL4 E_SP E_PB HSPA HSPA32 eq_refl eq_refl
                eq_refl eq_refl eq_refl eq_refl (eq_sym E_CP8) HCOPY HUC Htr0 HS0 Hra1 Hra2 Hsp16 Hsptop HTP Hlo1 Hlo2 HRS4 HAOK' HDK' Hg5 Hb5 HF5 HR5 HK5 HH5 STK5
                HABV Q (PA2_xdb.xdb_cont AI fflag SF5 L RNG RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s s' LB lo m m5 pim psi pcp ptp psb poc pia THIS ASI ACP TPA SBA AOC AIA DOC
                  BUF nim nsi ncp ntp nsb noc nia cls FA FN F SPAX COPY (zlength d - i0 + 64) p E5 F5 fc5 SP16 T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG
                  BO BG IG SG i0 CP8 CGF ZP DG SD SRG HC HCE HBG HBGE MD rest4 E_SP E_T8 E_DOC8 E_B8 E_I8 E_TB8 E_SB8 E_OC8 E_IA8 E_F11 E_CAPT E_CAPS E_PB E_FLAG D_BO
                  H_SZ H_LEN H_N H_SP B_ALL Ith Hnim Isi Hnsi' Icp Hb1 Hb2' Itp Isb Ioc Hnoc Iia Hnia Ifk Hfk1 Hfk2 HCI NO5 Hlo1 Hlo2 Hsp16 Hsptop HSPA32 HSPA HFm HFb
                  HFt HSHF Hg5 Hb5 HK5 AH5 STK5 PW5 HZ5 FPL4 HRS4 WIN_D APS4)).
    - (* [comment removed for export] *)
      exact (PA2_xd3.xdel3_call AI ODAW L RNG' ra sp gp tp s0 m m5 s' LB lo tr0 F COPY (zlength d - i0 + 64) SPAX p E5 R5 F5 fc5 SP16 PB ZL4 E_SP E_PB HSPA HSPA32 eq_refl eq_refl
                eq_refl eq_refl eq_refl eq_refl (eq_sym E_CP8) HCOPY HUC Htr0 HS0 Hra1 Hra2 Hsp16 Hsptop HTP Hlo1 Hlo2 HRS4 HAOK' HDK' Hg5 Hb5 HF5 HR5 HK5 HH5 STK5
                HABV Q (PA2_xdc.xdc_cont AI fflag SF5 L RNG RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s s' LB lo m m5 pim psi pcp ptp psb poc pia THIS ASI ACP TPA SBA AOC AIA DOC
                  BUF nim nsi ncp ntp nsb noc nia cls FA FN F SPAX COPY (zlength d - i0 + 64) p E5 F5 fc5 SP16 T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG
                  BO BG IG SG i0 CP8 CGF ZP DG SD SRG HC HCE HBG HBGE MD rest4 E_SP E_T8 E_DOC8 E_B8 E_I8 E_TB8 E_SB8 E_OC8 E_IA8 E_F11 E_CAPT E_CAPS E_PB E_FLAG D_BO
                  H_SZ H_LEN H_N H_SP B_ALL Ith Hnim Isi Hnsi' Icp Hb1 Hb2' Itp Isb Ioc Hnoc Iia Hnia Ifk Hfk1 Hfk2 HCI NO5 Hlo1 Hlo2 Hsp16 Hsptop HSPA32 HSPA HFm HFb
                  HFt HSHF Hg5 Hb5 HK5 AH5 STK5 PW5 HZ5 FPL4 HRS4 WIN_D APS4)).
  Qed.
End XNB.
End CANSEC.
