(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge Mem Cells Step Frame SysStep.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF Shadow StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AU_consts AU_iface AU_kit AU_parts_iface AU_client_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg SegLib SegBridge SegCall.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs PIosKit PIosKitA.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AHM.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Entry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import APS2_iface A2Lib PA2_kz PA2_exit PA2_xlib PA2_surv PA2_xd0 PA2_xdpr PA2_winN PA2_xdg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require PA2_t0c A2N_defs A2D_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Import ITree.Exc.
Open Scope Z_scope.
Local Notation u := bv_unsigned.
Local Notation M64 := 18446744073709551616.
Local Notation SH := 2147450880%Z (only parsing).

(* [comment removed for export] *)
Definition sgA36 : list expr := map EVar (seq 0 35) ++ [EVar 47].
Definition sgA (ra6 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : list expr :=
  sgA36 ++ [ELit (bv_unsigned ra6); ELit (bv_unsigned t0); ELit (bv_unsigned t1); ELit (bv_unsigned t2);
            ELit (bv_unsigned a0); ELit (bv_unsigned a1); ELit (bv_unsigned a2); ELit (bv_unsigned a3); ELit (bv_unsigned a4);
            ELit (bv_unsigned a5); ELit (bv_unsigned a6); ELit (bv_unsigned a7);
            EVar 59; EVar 60; EVar 61; EVar 62; EVar 63; EVar 64; EVar 65;
            ELit (bv_unsigned t3); ELit (bv_unsigned t4); ELit (bv_unsigned t5); ELit (bv_unsigned t6)].
Definition EXTRA_A : list kentry :=
  [KWr (SA A2N_defs.vSP (-8608)) (ELit 8608); KUnk (SA A2N_defs.vSP (-8608)) (ELit 8224)].

(* [comment removed for export] *)
Lemma incl_DA : incl_kn (map (ST.ksub sgA36) (ST.t_know A2D_defs.DA)) (List.filter (survivesQ A2N_defs.XDEL1_kn PRd) A2N_defs.XDEL1_kn ++ EXTRA_A) = true.
Proof. vm_compute. reflexivity. Qed.

Section CANSEC. Context {rc : runConstT}.

Section XDA.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Hypothesis SF5 : stack_free_5_stmt AI fflag.
  Variables (L : alayout) (RNG RNG4 : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (s s' : APS) (LB : list ablock) (lo : Z) (m m5 : amem)
            (pim psi pcp ptp psb poc pia : AsanCtrl.aptr) (THIS ASI ACP TPA SBA AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia : Z)
            (cls FA FN : Z) (F SPAX COPY n : Z) (p : AsanCtrl.aptr) (E5 : env) (FR5 : bvmap 5 word) (fc5 : bv 32).
  Variables (SP16 T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG : Z) (V CP8 CGF ZP DG SD SRG HC HCE HBG HBGE MD : Z)
            (rest4 : list Z).
  Local Notation ZL4 := (ZLwn (u ra) SP16 (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9) (u s10) (u s11)
                           T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG V CP8 CGF ZP DG SD SRG HC HCE HBG HBGE MD rest4).
  Local Notation LB4 := (HB p COPY n :: mkABlock (ABFake 5) F 2048 :: LB).
  Local Notation LB6 := (mkABlock (ABFake 5) F 2048 :: LB).
  Local Notation W := (s2_winA THIS TPA ntp SBA nsb AOC AIA).
  Local Notation XR k := (edenot E5 (sr_get A2N_defs.XDEL1_regs k)) (only parsing).
  (* [comment removed for export] *)
  Hypothesis E_SP : u sp = 16 * SP16.
  Hypothesis E_T8 : THIS = 8 * T8.
  Hypothesis E_DOC8 : DOC = 8 * DOC8.
  Hypothesis E_B8 : BUF = 8 * B8 + BO.
  Hypothesis E_I8 : ASI = 8 * I8.
  Hypothesis E_TB8 : TPA = 8 * TB8.
  Hypothesis E_SB8 : SBA = 8 * SB8.
  Hypothesis E_OC8 : AOC = 8 * OC8.
  Hypothesis E_IA8 : AIA = 8 * IA8.
  Hypothesis E_F11 : F = 2048 * F11.
  Hypothesis E_CAPT : ntp = 8 * CAPT.
  Hypothesis E_CAPS : nsb = CAPS.
  Hypothesis E_PB : u sp - 384 - SPAX = 16 * PB.
  Hypothesis E_FLAG : FLAG = fflag L 5 F.
  Hypothesis D_BO : 0 <= BO <= 7.
  Hypothesis H_SZ : 0 <= CAPT /\ 0 <= CAPS.
  Hypothesis H_LEN : 1 <= LEN <= 1048512.
  Hypothesis H_N : 1 <= N <= LEN.
  Hypothesis H_SP : 0x7fff00000000 <= u sp <= 2^47.
  (* [comment removed for export] *)
  Hypothesis B_ALL : 0x665000 <= THIS /\ THIS + 96 <= ATOP /\ 0x665000 <= DOC /\ DOC + 16 <= ATOP /\ 0x665000 <= BUF /\ BUF + LEN + 64 <= ATOP
                  /\ 0x665000 <= ASI /\ ASI + 4 * N + 12 <= ATOP /\ 0x665000 <= TPA /\ TPA + 8 * CAPT <= ATOP /\ 0x665000 <= SBA /\ SBA + CAPS <= ATOP
                  /\ 0x665000 <= AOC /\ AOC + 8192 <= ATOP /\ 0x665000 <= AIA /\ AIA + 1024 <= ATOP /\ 0x665000 <= F /\ F + 2048 <= ATOP.
  Hypothesis Ith : In (HB pim THIS nim) LB.
  Hypothesis Hnim : 96 <= nim.
  Hypothesis Isi : In (HB psi ASI nsi) LB.
  Hypothesis Hnsi : 4 * N + 12 <= nsi.
  Hypothesis Icp : In (HB pcp ACP ncp) LB.
  Hypothesis Hb1 : ACP <= BUF.
  Hypothesis Hb2 : BUF + LEN + 64 <= ACP + ncp.
  Hypothesis Itp : In (HB ptp TPA ntp) LB.
  Hypothesis Isb : In (HB psb SBA nsb) LB.
  Hypothesis Ioc : In (HB poc AOC noc) LB.
  Hypothesis Hnoc : 8192 <= noc.
  Hypothesis Iia : In (HB pia AIA nia) LB.
  Hypothesis Hnia : 1024 <= nia.
  Hypothesis Ifk : In (mkABlock (ABFake cls) FA FN) LB.
  Hypothesis Hfk1 : FA <= DOC.
  Hypothesis Hfk2 : DOC + 16 <= FA + FN.
  Hypothesis HCI : forall iv, In iv client_ranges -> In iv CI.
  Hypothesis NO5 : forall FA FN, ~ In (mkABlock (ABFake 5) FA FN) LB.
  Hypothesis Hlo1 : ATOP + 4096 <= lo.
  Hypothesis Hlo2 : lo <= u sp - 8608.
  Hypothesis Hsp16 : u sp mod 16 = 0.
  Hypothesis Hsptop : u sp + 16 < al_top L.
  Hypothesis HSPA32 : SPAX mod 32 = 0.
  Hypothesis HSPA : 384 <= u sp - SPAX <= 415.
  Hypothesis HFm : F mod 2048 = 0.
  Hypothesis HFb : ablk F (F + 2048).
  Hypothesis HFt : F + 2048 <= ATOP.
  Hypothesis HSHF : forall a, aclient_addr CI LB SPAX a -> a < shad F \/ shad F + 256 <= a.
  (* [comment removed for export] *)
  Hypothesis Hg5 : SP.gagree 47 (mkEZ ZL4) E5.
  Hypothesis Hb5 : eb E5 = eb (mkEZ ZL4).
  Hypothesis HK5 : know_ok asegs E5 m5 A2N_defs.XDEL1_kn.
  Hypothesis AH5 : AHEAP AI L RNG4 (aps_m s') LB4 m5.
  Hypothesis STK5 : stk asegs m5 lo (u sp).
  Hypothesis PW5 : aheap_pres_W CI LB (u sp) W m m5.
  Hypothesis HZ5 : frm0 fc5.
  (* [comment removed for export] *)
  Hypothesis FPLR : fp_le RNG RNG4.
  Hypothesis HRS4 : rng RNG4 lo (al_top L - lo).
  Hypothesis WIN_D : fp_le (SX.fp_of (SP.p_A A2D_defs.A2D) (mkEZ ZL4)) RNG4 /\ SX.aw_genuine (mkEZ ZL4) (SP.p_A A2D_defs.A2D).
  Hypothesis APS' : aps_rest s' = aps_rest s.

  Lemma lb_remove4 : lb_remove p LB4 = LB6.
  Proof.
    pose proof (AI_hb_ids AI _ _ _ _ _ AH5) as ND. cbn [hb_ids flat_map ab_kind app] in ND. apply NoDup_cons_iff in ND as [NP _].
    unfold lb_remove. rewrite filter_cons, decide_False.
    - change (lb_remove p LB6 = LB6). apply lb_remove_id. exact NP.
    - cbn [ab_kind abkind_eqb]. rewrite N.eqb_refl. cbn. tauto.
  Qed.

  Ltac ezx e := rewrite <- (SP.edenot_gagree 47 (mkEZ ZL4) E5 e Hg5 (eq_sym Hb5) eq_refl), zden_ok by reflexivity; cbn [zden nth ZLwn app].

  Lemma xda_cont : forall s'' RNG'' ms6, aps_rest s'' = aps_rest s' ->
    afree_post CI (AHEAP AI) L RNG4 (Z_to_bv 64 0x9a8b0) (Z_to_bv 64 SPAX) gp tp sp (Z_to_bv 64 SPAX)
      (XR 18) (XR 19) (XR 20) (XR 21) (XR 22) (XR 23) (XR 24) (XR 25) (XR 26) (XR 27) FR5 fc5 (aps_m s') LB4 p lo m5 (aps_m s'') RNG'' ms6 ->
    evtF asegs RNG'' (s2_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo W m tt s'' RNG'') ms6.
  Proof using All.
    intros s'' RNG'' ms6 HA (FPL6 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m6 & -> & MI6 & STK6a & PRES6 & AH6).
    rewrite lb_remove4 in PRES6, AH6.
    pose proof (u_rngE sp) as Rsp. atop_facts.
    assert (USPA : u (Z_to_bv 64 SPAX) = SPAX) by (rewrite u_Z_to_bv; apply Z.mod_small; lia).
    rewrite USPA in STK6a, PRES6.
    assert (ERP : ret_pc (Z_to_bv 64 0x9a8b0) = Z_to_bv 64 (ST.t_pc A2D_defs.DA)) by (apply bv_eq; vm_compute; reflexivity).
    rewrite ERP.
    assert (ESPA0 : 16 * SP16 + -384 - 16 * PB = SPAX) by lia.
    (* [comment removed for export] *)
    assert (ESPA : edenot E5 (EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 1)) (ELit (-384))) (EMd M_MUL (ELit 16) (EVar 29)))
                   = Z_to_bv 64 SPAX).
    { ezx (EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 1)) (ELit (-384))) (EMd M_MUL (ELit 16) (EVar 29))).
      rewrite ESPA0. reflexivity. }
    assert (EGP : edenot E5 (EVar 2) = gp) by (ezx (EVar 2); apply Z_to_bv_bv_unsigned).
    assert (ETP : edenot E5 (EVar 3) = tp) by (ezx (EVar 3); apply Z_to_bv_bv_unsigned).
    assert (ES0 : edenot E5 (EMd M_MUL (ELit 16) (EVar 1)) = sp) by (ezx (EMd M_MUL (ELit 16) (EVar 1)); rewrite <- E_SP; apply Z_to_bv_bv_unsigned).
    (* [comment removed for export] *)
    pose (sg := sgA (Z_to_bv 64 0x9a8b0) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
    pose (E6 := ST.senv E5 sg).
    assert (GI : SP.globals_id 35 sg = true) by (unfold sg; vm_compute; reflexivity).
    assert (G56 : SP.gagree 35 E5 E6) by exact (SP.senv_gagree 35 E5 sg GI).
    assert (G46 : SP.gagree 35 (mkEZ ZL4) E6) by (intros j Hj; rewrite (Hg5 j ltac:(lia)); exact (G56 j Hj)).
    assert (Hb6' : eb E6 = eb (mkEZ ZL4)) by (unfold E6; cbn [ST.senv eb]; exact Hb5).
    (* [comment removed for export] *)
    assert (STK6 : stk asegs m6 lo (u sp)).
    { apply (stk_merge asegs m6 lo SPAX (u sp)); [exact STK6a | | lia].
      destruct (stk_split asegs m5 lo SPAX (u sp) STK5 ltac:(lia)) as [_ STKb].
      eapply (aheap_pres_W_stk CI LB6 SPAX [] m5 m6 SPAX (u sp)); [apply aheap_pres_W_of_pres; exact PRES6 | exact STKb | lia | lia |].
      intros a _. cbn [outside]. exact I. }
    assert (PW6 : aheap_pres_W CI LB (u sp) W m m6).
    { eapply aheap_pres_W_trans; [exact PW5|].
      eapply (aheap_pres_W_weaken CI LB6 LB SPAX (u sp) W W m5 m6); [apply aheap_pres_W_of_pres; exact PRES6 | lia | |].
      - intros b Hb. right. exact Hb.
      - intros a Ha. exact Ha. }
    (* [comment removed for export] *)
    assert (HKX : know_ok asegs E5 m6 EXTRA_A).
    { apply (know_ok_agree asegs 47 (mkEZ ZL4) E5); [split; [exact Hg5 | exact (eq_sym Hb5)] | vm_compute; reflexivity |].
      unfold EXTRA_A. cbv [A2N_defs.vSP A2N_defs.vSP16 A2N_defs.V A2N_defs.mul].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      - apply (kz_wr asegs ZL4 m6); cbn [zden nth ZLwn app]; rewrite ?(Z.mod_small _ M64) by lia; [reflexivity | lia | lia | lia |].
        eapply (stk_wr_atA m6 lo (u sp)); [exact STK6 | lia | lia | lia].
      - eapply (stk_unkA ZL4 m6 lo (u sp)); [exact STK6 | reflexivity | lia | lia | |];
          cbn [zden nth ZLwn app]; rewrite ?(Z.mod_small _ M64) by lia; lia. }
    assert (PRF : forall x : word, SC.in_PR E5 PRd (u x) -> m6 x = m5 x).
    { eapply (pr_frame AI LB F pim psi pcp ptp psb poc pia THIS ASI ACP TPA SBA AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia cls FA FN
                (u ra) SP16 (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9) (u s10) (u s11)
                T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG V CP8 CGF ZP DG SD SRG HC HCE HBG HBGE MD rest4);
        try eassumption; try lia.
      rewrite ESPA0. exact PRES6. }
    pose proof (know_transport asegs A2N_defs.XDEL1_kn (ST.t_know A2D_defs.DA) EXTRA_A sgA36 PRd E5 m5 m6 HK5 PRF HKX incl_DA) as HKD0.
    assert (HKD : know_ok asegs E6 m6 (ST.t_know A2D_defs.DA)).
    { apply (know_ok_agree asegs 36 (ST.senv E5 sgA36) E6); [| vm_compute; reflexivity | exact HKD0].
      split; [|reflexivity]. intros j Hj. unfold E6, sg. cbn [ST.senv ev]. unfold vals_ev, sgA.
      rewrite map_app, app_nth1; [reflexivity|]. rewrite length_map. unfold sgA36. rewrite length_app, length_map, length_seq. cbn. lia. }
    (* [comment removed for export] *)
    assert (HRD : regs_ok E6 (ST.t_regs A2D_defs.DA)
                    (mkR (Z_to_bv 64 0x9a8b0) (Z_to_bv 64 SPAX) gp tp t0 t1 t2 sp (Z_to_bv 64 SPAX) a0 a1 a2 a3 a4 a5 a6 a7
                         (XR 18) (XR 19) (XR 20) (XR 21) (XR 22) (XR 23) (XR 24) (XR 25) (XR 26) (XR 27) t3 t4 t5 t6)).
    { apply regs_ok_mkR.
      change (map (fun k => edenot ?E (sr_get (ST.t_regs A2D_defs.DA) (Z_to_bv 5 k))) rkeys) with (map (edenot E) (tl A2D_defs.DA_regs)).
      cbn [tl A2D_defs.DA_regs map]. unfold E6, sg. rewrite !ST.esub_den.
      cbv [A2D_defs.vSPA A2D_defs.vSP A2D_defs.vSP16 A2D_defs.vGP A2D_defs.vTP A2D_defs.vPB A2D_defs.vF A2D_defs.vF11 A2D_defs.vSHF
           A2D_defs.V A2D_defs.mul A2D_defs.add A2D_defs.sub].
      cbn [ST.esub nth sgA sgA36 app map seq].
      rewrite ESPA, EGP, ETP, ES0.
      cbn [edenot]. rewrite !Z_to_bv_bv_unsigned. reflexivity. }
    (* [comment removed for export] *)
    destruct WIN_D as [FPD AWD].
    assert (CL : SX.aw_closed 35 (SP.p_A A2D_defs.A2D) = true) by (vm_compute; reflexivity).
    pose proof (SP.aw_genuine_gagree 35 (mkEZ ZL4) E6 _ G46 (eq_sym Hb6') CL AWD) as AWG6.
    assert (FPL6' : fp_le (SX.fp_of (SP.p_A A2D_defs.A2D) E6) RNG'').
    { eapply fp_le_trans; [|eapply fp_le_trans; [exact FPD | exact FPL6]].
      intros b j Hbj. exact (SP.fp_of_gagree 35 (mkEZ ZL4) E6 _ G46 (eq_sym Hb6') CL b j Hbj). }
    (* [comment removed for export] *)
    assert (Hg6 : SP.gagree 35 (mkEZ (PA2_t0c.ZL_t0'' (u ra) SP16 (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8)
                                   (u s9) (u s10) (u s11) T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG [])) E6).
    { intros j Hj. rewrite <- (G46 j Hj). cbn [mkEZ ev]. f_equal. unfold PA2_t0c.ZL_t0'', ZLwn.
      do 35 (destruct j as [|j]; [reflexivity|]). lia. }
    assert (Hb6 : eb E6 = eb (mkEZ (PA2_t0c.ZL_t0'' (u ra) SP16 (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8)
                                   (u s9) (u s10) (u s11) T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG []))).
    { rewrite Hb6'. reflexivity. }
    assert (HinD : In A2D_defs.DA (SP.p_tm A2D_defs.A2D)) by (cbn [SP.p_tm A2D_defs.A2D SP.PGCA In]; left; reflexivity).
    assert (HFLD : In (KWord (SA A2D_defs.vF 2040) 8 A2D_defs.vFLAG) (ST.t_know A2D_defs.DA))
      by (cbv [ST.t_know A2D_defs.DA A2D_defs.DA_kn]; repeat (first [left; reflexivity | right])).
    assert (HFWD : In (KWr (SA A2D_defs.vF 0) (ELit 2048)) (ST.t_know A2D_defs.DA))
      by (cbv [ST.t_know A2D_defs.DA A2D_defs.DA_kn]; repeat (first [left; reflexivity | right])).
    assert (RNGS6 : rng RNG'' lo (u sp - lo)) by (eapply rng_sub; [exact (rng_fp_le _ _ _ _ FPL6 HRS4) | lia | lia]).
    assert (FPLR6 : fp_le RNG RNG'') by exact (fp_le_trans _ _ _ FPLR FPL6).
    assert (APSD : aps_rest s'' = aps_rest s) by congruence.
    destruct B_ALL as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8' & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17 & B18).
    exact (xd_tail AI fflag SF5 L RNG RNG'' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s s'' LB lo m m6
             THIS TPA ntp SBA nsb AOC AIA pim ptp psb poc pia nim noc nia F SPAX
             Ith Hnim Itp Isb Ioc Hnoc Iia Hnia NO5 Hlo1 Hlo2 Hsp16 ltac:(lia) HSPA32 HSPA HFm HFb HFt HSHF
             SP16 T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG []
             E_SP E_T8 E_TB8 E_CAPT E_SB8 E_CAPS E_OC8 E_IA8 E_F11 E_PB E_FLAG
             ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
             E6 A2D_defs.DA _ FR5 fc5 Hg6 Hb6 HinD (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) HRD HKD HFLD HFWD HZ5
             AWG6 FPL6' AH6 MI6 STK6 PW6 RNGS6 FPLR6 APSD).
  Qed.
End XDA.
End CANSEC.
