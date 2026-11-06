(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge Mem Cells Step Frame SysStep.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF Shadow StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps SjStage1 SjS1Bytes SjInv.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AU_consts AU_iface AU_kit AU_parts_iface AU_fuzz_kit Stdio_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg SegLib SegBridge.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs PIosKit PIosKitA.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Entry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require S2G2.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import APC_mpres.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2B Require Import APS2_iface A2Lib PA2_exit PA2_tail.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2B Require PA2_t0c.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegB2 Require B2_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Import ITree.Exc.
Open Scope Z_scope.
Local Notation u := bv_unsigned.
Local Notation M64 := 18446744073709551616.
Local Notation SH := 2147450880%Z (only parsing).

Section CANSEC. Context {rc : runConstT}.

Section X.
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
  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
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
  Lemma a2_after : forall (m3 : amem),
    (forall x : word, SP.outside_wins (mkEZ ZL) (SP.p_W B2_defs.B2) (u x) -> m3 x = m2 x) -> wmono bsegs m2 m3 ->
    munch [(u sp - 8640, u sp); (THIS + 24, THIS + 28); (THIS + 88, THIS + 96); (TPA, TPA + ntp); (SBA, SBA + nsb);
           (AOC, AOC + 8192); (AIA, AIA + 1024); (F, F + 2048); (shad F, shad F + 256)] m2 m3
    /\ AHEAP AI L RNG (aps_m s) (mkABlock (ABFake 5) F 2048 :: LB) m3
    /\ aheap_pres_W CI LB (u sp) (s2_winA THIS TPA ntp SBA nsb AOC AIA) m m3.
  Proof using All.
    intros m3 FR3 WM3.
    unfold STAGE2_STACK_A in Hlo2. atop_facts. pose proof (u_rngE sp) as Rsp.
    pose proof (AI_layout AI _ _ _ _ _ AH2) as (_ & _ & HTOP & _).
    assert (Hsp47 : u sp <= 2 ^ 47) by lia.
    pose proof (a2_munch (u ra) SP16 (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9) (u s10) (u s11)
                  T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG rest m2 m3
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(unfold ablk, AIMG_HI, KLS in HFb; lia) ltac:(unfold ablk, AIMG_HI, KLS in HFb; lia) ltac:(lia) FR3) as MU.
    assert (ESF : shad F = 256 * F11 + SH) by (rewrite shad_div; unfold ASHOFF; rewrite E_F11; clear; Z.div_mod_to_equations; lia).
    rewrite <- E_SP, <- E_T8, <- E_TB8, <- E_CAPT, <- E_SB8, <- E_CAPS, <- E_OC8, <- E_IA8, <- E_F11, <- ESF in MU.
    split; [exact MU|]. split.
    - eapply (AI_frame AI); [exact AH2 | exact MU | exact WM3 |].
      assert (FF : shad F - ASHOFF = F / 8) by (rewrite shad_div; lia).
      repeat apply Forall_cons; [ .. | apply Forall_nil]; cbn [fst snd].
      + left; left. lia.
      + right; left. exists (HB pim THIS nim). split; [right; exact Ith | cbn; lia].
      + right; left. exists (HB pim THIS nim). split; [right; exact Ith | cbn; lia].
      + right; left. exists (HB ptp TPA ntp). split; [right; exact Itp | cbn; lia].
      + right; left. exists (HB psb SBA nsb). split; [right; exact Isb | cbn; lia].
      + right; left. exists (HB poc AOC noc). split; [right; exact Ioc | cbn; lia].
      + right; left. exists (HB pia AIA nia). split; [right; exact Iia | cbn; lia].
      + left; right; right. exists 5, F, 2048. split; [left; reflexivity | lia].
      + right; right. right; right. exists 5, F, 2048. split; [left; reflexivity|].
        replace (shad F + 256 - shad F) with 256 by ring. rewrite FF. clear - HFm; Z.div_mod_to_equations; lia.
    - eapply (a2_pres_W AI L RNG (aps_m s) LB m m2 m3 (u sp) SPAX F THIS TPA ntp SBA nsb AOC AIA);
        [exact AH2 | exact NO5 | exact HFb | exact HFt | lia | exact Hsp47 | lia | exact HSHF | exact PRES2 | exact MU | exact WM3].
  Qed.

  Lemma xsf_branch : forall (E' : env) (m3 : amem) (R3 F3 : bvmap 5 word) (fc3 : bv 32),
    SP.gagree 35 (mkEZ ZL) E' -> eb E' = eb (mkEZ ZL) ->
    rfull R3 -> regs_ok E' (ST.t_regs B2_defs.XSF) R3 -> know_ok bsegs E' m3 (ST.t_know B2_defs.XSF) ->
    SG.gholds (S2G2.gp2 bsegs d (idx ++ [zlength d; zlength d; 0])) E' m3 (ST.t_ghost B2_defs.XSF) ->
    AHEAP AI L RNG (aps_m s) (mkABlock (ABFake 5) F 2048 :: LB) m3 ->
    aheap_pres_W CI LB (u sp) (s2_winA THIS TPA ntp SBA nsb AOC AIA) m m3 ->
    wmono bsegs m2 m3 -> mem_inv bsegs m3 -> (forall lo hi, stk bsegs m2 lo hi -> stk bsegs m3 lo hi) -> frm0 fc3 ->
    implMA RNG (rn_copyA d idx) s
      (s2_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo (s2_winA THIS TPA ntp SBA nsb AOC AIA) m)
      (MS R3 F3 (Z_to_bv 64 (ST.t_pc B2_defs.XSF)) fc3 None m3 (seg_rom bsegs)).
  Proof using All.
    intros E' m3 R3 F3 fc3 Hg Hb HF3 HR3 HK3 HG3 AH3 PW3 WM3 MI3 STK3 HZ3.
    unfold STAGE2_STACK_A in Hlo2. atop_facts. pose proof (u_rngE sp) as Rsp.
    pose proof (AI_layout AI _ _ _ _ _ AH2) as (_ & _ & HTOP & _).
    assert (Hsp47 : u sp <= 2 ^ 47) by lia.
    (* [comment removed for export] *)
    unfold SG.gholds in HG3. cbn [ST.t_ghost B2_defs.XSF] in HG3. apply Forall_inv in HG3 as GN. cbn [ST.g_id ST.g_args map S2G2.gp2] in GN.
    destruct idx as [|i0 idx']; [exfalso; unfold zlength in Sn; cbn [length Z.of_nat] in Sn; lia|].
    change (znth ((i0 :: idx') ++ [zlength d; zlength d; 0]) 0) with i0 in GN.
    unfold rn_copyA. rewrite GN. apply implMA_ret.
    (* [comment removed for export] *)
    destruct (xsf_regs ZL E' R3 Hg (eq_sym Hb) HF3 HR3)
      as (x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x27 & x28 & x29 & x30 & x31 & ->).
    destruct (xsf_kfacts (u ra) SP16 (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9) (u s10) (u s11)
                T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG rest E' m3 Hg (eq_sym Hb) HK3 ltac:(lia) ltac:(lia))
      as (HRC & HRCM & SAVED).
    rewrite <- E_SP in SAVED.
    (* [comment removed for export] *)
    replace (16 * SP16 + -416 - 16 * PB + 272) with (SPAX + 272) in HRCM by lia.
    rewrite <- (Z_to_bv_bv_unsigned (edenot E' (EVar 35))) in HRCM.
    unfold ZL; cbn [nth PA2_t0c.ZL_t0'' app].
    replace (16 * SP16 + -416 - 16 * PB) with SPAX by lia. rewrite <- E_SP, <- E_F11. rewrite !Z_to_bv_bv_unsigned.
    change (Z_to_bv 64 (ST.t_pc B2_defs.XSF)) with (Z_to_bv 64 ASTKFREE5).
    (* [comment removed for export] *)
    assert (HFL3 : rw_cells bsegs m3 (F + 2040) [C8 (Z_to_bv 64 (fflag L 5 F))]).
    { pose proof (know_nth _ _ _ _ 2 _ HK3 eq_refl) as K.   (* [comment removed for export] *)
      assert (EF : edenot E' B2_defs.vF = Z_to_bv 64 F).
      { rewrite <- (SP.edenot_gagree 35 (mkEZ ZL) E' B2_defs.vF Hg (eq_sym Hb) eq_refl), zden_ok by reflexivity.
        unfold ZL; cbn [zden nth PA2_t0c.ZL_t0'' app B2_defs.vF B2_defs.vF11 B2_defs.V B2_defs.mul]. rewrite <- E_F11. reflexivity. }
      assert (EV : edenot E' B2_defs.vFLAG = Z_to_bv 64 (fflag L 5 F)).
      { rewrite <- (SP.edenot_gagree 35 (mkEZ ZL) E' B2_defs.vFLAG Hg (eq_sym Hb) eq_refl).
        unfold ZL; cbn [edenot ev mkEZ nth PA2_t0c.ZL_t0'' app B2_defs.vFLAG B2_defs.V]. rewrite E_FLAG. reflexivity. }
      pose proof (SB.kx_rw8 bsegs E' m2 m3 B2_defs.vF 2040 B2_defs.vFLAG (Z_to_bv 64 (fflag L 5 F)) K) as X.
      rewrite EF, EV, u_Z_to_bv, Z.mod_small in X by (unfold ablk, AIMG_HI, KLS in HFb; lia).
      exact (X HFL2 WM3). }
    eapply (xsf_tail AI fflag SF5 L RNG RNG s s LB m m3 lo (s2_winA THIS TPA ntp SBA nsb AOC AIA) F SPAX (u (edenot E' (EVar 35))));
      [ exact AH3 | exact MI3 | exact (STK3 _ _ STK2) | exact Hlo1 | lia | exact Hsp16 | exact Hsp47 | exact HSPA | exact HSPA32 | exact HFL3
      | exact SAVED | exact HRC | exact HRCM | eapply rng_sub'; [exact HRS | lia] | exact PW3 | intros b j Hj; exact Hj | reflexivity | exact HZ3 ].
  Qed.

  (* [comment removed for export] *)
  Notation Q := (s2_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo (s2_winA THIS TPA ntp SBA nsb AOC AIA) m).
  Notation XR k := (edenot _ (sr_get (ST.t_regs B2_defs.XNEW) k)) (only parsing).

  Lemma xnew_call : forall (E' : env) (m3 : amem) (R3 F3 : bvmap 5 word) (fc3 : bv 32),
    opnew_nt_stmtA AI -> tp = Z_to_bv 64 ATP -> In [AMALLOC_PC; AOPNEW_RET] (al_U L) -> aps_ok L s -> LEN = zlength d ->
    zlength d + 64 <= 2^20 ->
    SP.gagree 35 (mkEZ ZL) E' -> eb E' = eb (mkEZ ZL) ->
    rfull R3 -> regs_ok E' (ST.t_regs B2_defs.XNEW) R3 -> know_ok bsegs E' m3 (ST.t_know B2_defs.XNEW) ->
    SG.gholds (S2G2.gp2 bsegs d (idx ++ [zlength d; zlength d; 0])) E' m3 (ST.t_ghost B2_defs.XNEW) ->
    AHEAP AI L RNG (aps_m s) (mkABlock (ABFake 5) F 2048 :: LB) m3 ->
    aheap_pres_W CI LB (u sp) (s2_winA THIS TPA ntp SBA nsb AOC AIA) m m3 ->
    wmono bsegs m2 m3 -> mem_inv bsegs m3 -> (forall lo hi, stk bsegs m2 lo hi -> stk bsegs m3 lo hi) -> frm0 fc3 ->
    u (edenot E' (EVar 36)) = znth (idx ++ [zlength d; zlength d; 0]) 0 ->
    (forall p s' RNG' ms',
       opnew_postA AI L RNG (Z_to_bv 64 0x9b528) (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 2))
         (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 3)) (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 4))
         (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 8)) (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 9))
         (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 18)) (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 19))
         (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 20)) (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 21))
         (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 22)) (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 23))
         (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 24)) (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 25))
         (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 26)) (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 27))
         F3 fc3 s (mkABlock (ABFake 5) F 2048 :: LB) (zlength d - znth idx 0 + 64) lo m3 p s' RNG' ms' ->
       DK 0 s s' ->
       implMA RNG' (HarnessP.opdelete afree_M p) s' Q ms') ->
    implMA RNG (rn_copyA d idx) s Q (MS R3 F3 (Z_to_bv 64 (ST.t_pc B2_defs.XNEW)) fc3 None m3 (seg_rom bsegs)).
  Proof using All.
    intros E' m3 R3 F3 fc3 ONT HTP HUM HAOK E_LEN Hlen Hg Hb HF3 HR3 HK3 HG3 AH3 PW3 WM3 MI3 STK3 HZ3 HV2 K.
    unfold STAGE2_STACK_A in Hlo2. atop_facts. pose proof (u_rngE sp) as Rsp.
    pose proof (AI_layout AI _ _ _ _ _ AH2) as (_ & _ & HTOP & _).
    assert (Hsp47 : u sp <= 2 ^ 47) by lia.
    (* [comment removed for export] *)
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
    (* [comment removed for export] *)
    unfold SG.gholds in HG3.
    pose proof (proj1 (Forall_forall _ _) HG3 (ST.GA 9 []) ltac:(cbn [ST.t_ghost B2_defs.XNEW In]; tauto)) as GN.
    pose proof (proj1 (Forall_forall _ _) HG3 (ST.GA 3 [ELit 0; B2_defs.V 35]) ltac:(cbn [ST.t_ghost B2_defs.XNEW In]; tauto)) as GT.
    cbn [ST.g_id ST.g_args map S2G2.gp2 edenot B2_defs.V] in GN, GT. rewrite u_Z_to_bv in GT.
    destruct GT as (_ & _ & GT). change (0 mod M64 / 4) with 0 in GT. change (ev E' 35) with (edenot E' (EVar 35)) in GT.
    destruct idx as [|i0 idx']; [exfalso; unfold zlength in Sn; cbn [length Z.of_nat] in Sn; lia|].
    change (znth ((i0 :: idx') ++ [zlength d; zlength d; 0]) 0) with i0 in GN, GT, HV2.
    change (znth (i0 :: idx') 0) with i0 in K.
    rewrite <- E_LEN in Hlen.
    assert (LEN0 : 0 <= LEN) by (rewrite E_LEN; unfold zlength; lia).
    assert (HI0 : 0 <= i0 /\ LEN - i0 >= 1) by (rewrite <- GT; clear - KV KLV RV Hlen LEN0; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    unfold rn_copyA. rewrite GN.
    eapply (implMA_bind RNG _ _ s (fun p s' RNG' ms' =>
      opnew_postA AI L RNG (Z_to_bv 64 0x9b528) (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 2))
         (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 3)) (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 4))
         (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 8)) (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 9))
         (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 18)) (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 19))
         (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 20)) (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 21))
         (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 22)) (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 23))
         (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 24)) (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 25))
         (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 26)) (edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 27))
         F3 fc3 s (mkABlock (ABFake 5) F 2048 :: LB) (zlength d - i0 + 64) lo m3 p s' RNG' ms'
      /\ DK 0 s s')); [apply (implMA_leaves RNG _ s _ (fun _ s' => DK 0 s s')); [| apply (opnew_dk _ s)]
                     | intros p s' RNG' ms' [HP HD]; exact (K p s' RNG' ms' HP HD)].
    (* [comment removed for export] *)
    assert (ESPA : edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 2) = Z_to_bv 64 SPAX).
    { change (sr_get (ST.t_regs B2_defs.XNEW) 2)
        with (EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 1)) (ELit (-416))) (EMd M_MUL (ELit 16) (EVar 29))).
      rewrite <- (SP.edenot_gagree 35 (mkEZ ZL) E' (EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 1)) (ELit (-416)))
                    (EMd M_MUL (ELit 16) (EVar 29))) Hg (eq_sym Hb) eq_refl), zden_ok by reflexivity.
      unfold ZL; cbn [zden nth PA2_t0c.ZL_t0'' app]. f_equal. lia. }
    assert (ETP : edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 4) = tp).
    { change (sr_get (ST.t_regs B2_defs.XNEW) 4) with (EVar 3).
      rewrite <- (SP.edenot_gagree 35 (mkEZ ZL) E' (EVar 3) Hg (eq_sym Hb) eq_refl).
      unfold ZL; cbn [edenot ev mkEZ nth PA2_t0c.ZL_t0'' app]. apply Z_to_bv_bv_unsigned. }
    assert (EA0 : edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 10) = Z_to_bv 64 (zlength d - i0 + 64)).
    { change (sr_get (ST.t_regs B2_defs.XNEW) 10) with (EAlu ALU_ADD (EAlu ALU_SUB (EVar 19) (EVar 36)) (ELit 64)).
      change (edenot E' (EAlu ALU_ADD (EAlu ALU_SUB (EVar 19) (EVar 36)) (ELit 64)))
        with (alu64 ALU_ADD (alu64 ALU_SUB (edenot E' (EVar 19)) (edenot E' (EVar 36))) (Z_to_bv 64 64)).
      rewrite alu_add, alu_sub, ELEN. unfold v_add, v_sub. rewrite !u_Z_to_bv, HV2. apply Z_to_bv_congr. rewrite <- E_LEN.
      clear - HI0 Hlen. Z.div_mod_to_equations. lia. }
    rewrite (regs_ok_canon E' _ R3 HF3 HR3).
    change (Z_to_bv 64 (ST.t_pc B2_defs.XNEW)) with (Z_to_bv 64 0x9b524).
    rewrite ESPA, ETP, EA0 in *.
    set (r1 := edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 1)) in *.
    set (r3 := edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 3)) in *.
    set (r5 := edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 5)) in *.
    set (r6 := edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 6)) in *.
    set (r7 := edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 7)) in *.
    set (r8 := edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 8)) in *.
    set (r9 := edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 9)) in *.
    set (r11 := edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 11)) in *.
    set (r12 := edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 12)) in *.
    set (r13 := edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 13)) in *.
    set (r14 := edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 14)) in *.
    set (r15 := edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 15)) in *.
    set (r16 := edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 16)) in *.
    set (r17 := edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 17)) in *.
    set (r18 := edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 18)) in *.
    set (r19 := edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 19)) in *.
    set (r20 := edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 20)) in *.
    set (r21 := edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 21)) in *.
    set (r22 := edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 22)) in *.
    set (r23 := edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 23)) in *.
    set (r24 := edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 24)) in *.
    set (r25 := edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 25)) in *.
    set (r26 := edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 26)) in *.
    set (r27 := edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 27)) in *.
    set (r28 := edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 28)) in *.
    set (r29 := edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 29)) in *.
    set (r30 := edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 30)) in *.
    set (r31 := edenot E' (sr_get (ST.t_regs B2_defs.XNEW) 31)) in *.
    clearbody r1 r3 r5 r6 r7 r8 r9 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31.
    eapply (implMA_evtF RNG _ s _ (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x9b528) (Z_to_bv 64 SPAX) r3 tp r5 r6 r7 r8 r9 (Z_to_bv 64 (zlength d - i0 + 64)) r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31) F3 (Z_to_bv 64 AOPNEW_ARR_NT) fc3 None m3 (seg_rom bsegs))).
    { zstep. apply evtF_done. reflexivity. }
    intros ms' ->.
    assert (HSPX : 0 <= SPAX < M64) by lia.
    destruct (stk_split bsegs m3 lo SPAX (u sp) (STK3 _ _ STK2) ltac:(lia)) as [STKa _].
    eapply (proj2 ONT); rewrite ?ESPA, ?ETP, ?EA0, ?unsigned_lit by lia;
      [ exact AH3 | exact MI3 | exact STKa | exact Hlo1 | unfold OPNEW_NT_STACK_A, OPNEW_STACK_A, AMALLOC_STACK; lia | lia
      | clear - HSPA32; Z.div_mod_to_equations; lia | exact HTP | reflexivity | unfold AREQMAX; rewrite <- E_LEN; lia | exact HUM
      | exact HRS | exact HAOK ].
  Qed.
End X.
End CANSEC.
