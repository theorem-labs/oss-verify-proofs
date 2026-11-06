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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim AsanCtrl AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells ABase AMalloc_iface AU_iface AU_kit AU_fuzz_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AHM.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Entry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import APS2_iface PA2_kz PA2_reg PA2_winN.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require A2N_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.
Local Notation u := bv_unsigned.
Local Notation M64 := 18446744073709551616.
Local Notation SH := 2147450880%Z (only parsing).

Section CANSEC. Context {rc : runConstT}.

Section C.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (LB : list ablock) (lo : Z) (F : Z) (p : AsanCtrl.aptr) (COPY n : Z)
            (pim psi pcp ptp psb poc pia : AsanCtrl.aptr) (THIS ASI ACP TPA SBA AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia : Z)
            (cls FA FN : Z).
  Variables (zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 : Z)
            (T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG : Z)
            (V CP8 CGF ZP DG SD SRG HC HCE HBG HBGE MD : Z) (rest : list Z).
  Local Notation ZL := (ZLwn zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8
                          F11 PB FLAG BO BG IG SG V CP8 CGF ZP DG SD SRG HC HCE HBG HBGE MD rest).
  Local Notation LB4 := (HB p COPY n :: mkABlock (ABFake 5) F 2048 :: LB).
  Hypothesis E_SP : 0x7fff00000000 <= 16 * SP16 <= 2^47.
  Hypothesis E_T8 : THIS = 8 * T8.
  Hypothesis E_DOC8 : DOC = 8 * DOC8.
  Hypothesis E_B8 : BUF = 8 * B8 + BO.
  Hypothesis E_I8 : ASI = 8 * I8.
  Hypothesis E_TB8 : TPA = 8 * TB8.
  Hypothesis E_SB8 : SBA = 8 * SB8.
  Hypothesis E_OC8 : AOC = 8 * OC8.
  Hypothesis E_IA8 : AIA = 8 * IA8.
  Hypothesis E_F11 : F = 2048 * F11.
  Hypothesis E_CP8 : COPY = 8 * CP8.
  Hypothesis E_CAPT : ntp = 8 * CAPT.
  Hypothesis E_CAPS : nsb = CAPS.
  Hypothesis E_n : n = LEN - V + 64.
  Hypothesis D_BO : 0 <= BO <= 7.
  Hypothesis D_BG : 0 <= LEN + BO + 64 - 8 * BG <= 7.
  Hypothesis D_IG : 0 <= 8 * IG - (4 * N + 12) <= 7.
  Hypothesis D_SG : 0 <= CAPS - 8 * SG <= 7.
  Hypothesis D_CGF : 0 <= LEN - V + 64 - 8 * CGF <= 7.
  Hypothesis H_PB : 0 <= PB <= 1.
  Hypothesis H_SZ : 0 <= CAPT /\ 0 <= CAPS /\ 0 <= BG /\ 0 <= IG /\ 0 <= SG /\ 0 <= CGF.
  Hypothesis H_LEN : 1 <= LEN <= 1048512.
  Hypothesis H_N : 1 <= N <= LEN.
  Hypothesis H_V : 0 <= V /\ 1 <= LEN - V.
  Hypothesis H_LO : ATOP + 4096 <= lo /\ lo <= 16 * SP16 - 8608.
  Hypothesis B_ALL : 0x665000 <= THIS /\ THIS + 96 <= ATOP /\ 0x665000 <= DOC /\ DOC + 16 <= ATOP /\ 0x665000 <= BUF /\ BUF + LEN + 64 <= ATOP
                  /\ 0x665000 <= ASI /\ ASI + 4 * N + 12 <= ATOP /\ 0x665000 <= TPA /\ TPA + 8 * CAPT <= ATOP /\ 0x665000 <= SBA /\ SBA + CAPS <= ATOP
                  /\ 0x665000 <= AOC /\ AOC + 8192 <= ATOP /\ 0x665000 <= AIA /\ AIA + 1024 <= ATOP /\ 0x665000 <= F /\ F + 2048 <= ATOP
                  /\ 0x665000 <= COPY /\ COPY + n <= ATOP.
  Hypothesis Ith : In (HB pim THIS nim) LB.
  Hypothesis Hnim : 96 <= nim.
  Hypothesis Isi : In (HB psi ASI nsi) LB.
  Hypothesis Hnsi : 4 * N + 12 <= nsi.
  Hypothesis Icp : In (HB pcp ACP ncp) LB.
  Hypothesis Hb1 : ACP <= BUF.
  Hypothesis Hac : ACP mod 8 = 0.
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

  Lemma wd_agree : forall E b off k, SP.gagree 47 (mkEZ ZL) E -> eb E = eb (mkEZ ZL) ->
    expr_vars_lt 47 b = true -> expr_vars_lt 47 k = true -> zok b = true -> zok k = true ->
    SP.win_den E (b, off, k) = (zden ZL b mod M64 + off, zden ZL b mod M64 + off + zden ZL k mod M64).
  Proof.
    intros E b off k Hg Hb H1 H2 H3 H4. cbn [SP.win_den].
    rewrite <- (SP.edenot_gagree 47 (mkEZ ZL) E b Hg (eq_sym Hb) H1), <- (SP.edenot_gagree 47 (mkEZ ZL) E k Hg (eq_sym Hb) H2).
    rewrite !u_zden by assumption. reflexivity.
  Qed.

  Ltac wd := rewrite wd_agree by (assumption || reflexivity); cbn [fst snd zden nth ZLwn app];
             rewrite ?(Z.mod_small _ M64) by (atop_facts; lia).
  Ltac inLB4 I := right; right; exact I.

  (* [comment removed for export] *)
  Lemma cnd_W : forall E, SP.gagree 47 (mkEZ ZL) E -> eb E = eb (mkEZ ZL) -> SP.wins_client (AHM.hmC AI LB4) E (SP.p_W A2N_defs.A2N).
  Proof.
    intros E Hg Hb. unfold SP.wins_client, AHM.hmC. cbn [SP.p_W A2N_defs.A2N SP.PGH SP.PGX].
    cbv [A2N_defs.vSP A2N_defs.vSP16 A2N_defs.vTHIS A2N_defs.vT8 A2N_defs.vTBASE A2N_defs.vTB8 A2N_defs.vCAPT A2N_defs.vSBASE
         A2N_defs.vSB8 A2N_defs.vCAPS A2N_defs.vOCB A2N_defs.vOC8 A2N_defs.vIAB A2N_defs.vIA8 A2N_defs.vF A2N_defs.vF11 A2N_defs.vSHF
         A2N_defs.vSPA A2N_defs.vPB A2N_defs.vCOPY A2N_defs.vC8 A2N_defs.vLEN A2N_defs.vV A2N_defs.V A2N_defs.mul A2N_defs.add A2N_defs.sub].
    atop_facts.
    repeat apply Forall_cons; try apply Forall_nil; wd.
    - left; left. lia.
    - right; left. exists (HB pim THIS nim). split; [inLB4 Ith | cbn; lia].
    - right; left. exists (HB pim THIS nim). split; [inLB4 Ith | cbn; lia].
    - right; left. exists (HB ptp TPA ntp). split; [inLB4 Itp | cbn; lia].
    - right; left. exists (HB psb SBA nsb). split; [inLB4 Isb | cbn; lia].
    - right; left. exists (HB poc AOC noc). split; [inLB4 Ioc | cbn; lia].
    - right; left. exists (HB pia AIA nia). split; [inLB4 Iia | cbn; lia].
    - right; left. exists (mkABlock (ABFake 5) F 2048). split; [right; left; reflexivity | cbn; lia].
    - right; right. right; right. exists 5, F, 2048. split; [right; left; reflexivity | unfold ASHOFF; lia].
    - left; left. lia.
    - right; left. exists (HB p COPY n). split; [left; reflexivity | cbn; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma tab_ci : forall lo' hi', In (lo', hi') IMG_TABS -> In (lo', hi') CI.
  Proof. intros lo' hi' H. apply HCI. unfold client_ranges. apply in_or_app. right. exact H. Qed.
  Ltac hmb b I := apply (AHM.hmA_of_block AI LB4 b); [I | cbn [ab_addr ab_size]; lia].
  Ltac hms b I z := replace z with (shad (8 * (z - SH))) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia);
    apply AHM.hmA_of_block_shadow; exists b; split; [I | cbn [ab_addr ab_size]; lia].
  Lemma cnd_CR : forall E, SP.gagree 47 (mkEZ ZL) E -> eb E = eb (mkEZ ZL) ->
    forall w, In w (SP.p_CR A2N_defs.A2N) -> forall z, fst (SP.win_den E w) <= z < snd (SP.win_den E w) -> AHM.hmA AI LB4 z.
  Proof.
    intros E Hg Hb w Hw z Hz. cbn [SP.p_CR A2N_defs.A2N SP.PGH SP.PGX] in Hw.
    cbv [A2N_defs.vSP A2N_defs.vSP16 A2N_defs.vTHIS A2N_defs.vT8 A2N_defs.vDOC A2N_defs.vDOC8 A2N_defs.vBUF A2N_defs.vB8 A2N_defs.vBO
         A2N_defs.vLEN A2N_defs.vIDX A2N_defs.vI8 A2N_defs.vN A2N_defs.vTBASE A2N_defs.vTB8 A2N_defs.vCAPT A2N_defs.vSBASE A2N_defs.vSB8
         A2N_defs.vCAPS A2N_defs.vOCB A2N_defs.vOC8 A2N_defs.vIAB A2N_defs.vIA8 A2N_defs.vBG A2N_defs.vIG A2N_defs.vSG A2N_defs.vF
         A2N_defs.vF11 A2N_defs.vSHF A2N_defs.vCOPY A2N_defs.vC8 A2N_defs.vCGF A2N_defs.vV A2N_defs.V A2N_defs.mul A2N_defs.add
         A2N_defs.sub] in Hw.
    atop_facts.
    repeat (destruct Hw as [<-|Hw]; [rewrite wd_agree in Hz by (assumption || reflexivity); cbn [fst snd zden nth ZLwn app] in Hz;
                                      rewrite ?(Z.mod_small _ M64) in Hz by (atop_facts; lia) |]); [..| destruct Hw].
    - hmb (HB pim THIS nim) ltac:(inLB4 Ith).
    - hmb (mkABlock (ABFake cls) FA FN) ltac:(inLB4 Ifk).
    - hmb (HB pcp ACP ncp) ltac:(inLB4 Icp).
    - hmb (HB psi ASI nsi) ltac:(inLB4 Isi).
    - hmb (HB ptp TPA ntp) ltac:(inLB4 Itp).
    - hmb (HB psb SBA nsb) ltac:(inLB4 Isb).
    - hmb (HB poc AOC noc) ltac:(inLB4 Ioc).
    - hmb (HB pia AIA nia) ltac:(inLB4 Iia).
    - hms (HB pim THIS nim) ltac:(inLB4 Ith) z.
    - hms (mkABlock (ABFake cls) FA FN) ltac:(inLB4 Ifk) z.
    - hms (HB pcp ACP ncp) ltac:(inLB4 Icp) z.
    - hms (HB psi ASI nsi) ltac:(inLB4 Isi) z.
    - hms (HB ptp TPA ntp) ltac:(inLB4 Itp) z.
    - hms (HB psb SBA nsb) ltac:(inLB4 Isb) z.
    - hms (HB poc AOC noc) ltac:(inLB4 Ioc) z.
    - hms (HB pia AIA nia) ltac:(inLB4 Iia) z.
    - hmb (mkABlock (ABFake 5) F 2048) ltac:(right; left; reflexivity).
    - hms (mkABlock (ABFake 5) F 2048) ltac:(right; left; reflexivity) z.
    - replace z with (shad (8 * (z - SH))) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
      apply AHM.hmA_of_stack_shadow. lia.
    - replace z with (shad (8 * (z - SH))) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
      apply AHM.hmA_of_ci_shadow. exists (0x23500, 0x23600). split; [apply tab_ci; cbn; tauto | cbn; lia].
    - replace z with (shad (8 * (z - SH))) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
      apply AHM.hmA_of_ci_shadow. exists (0x23640, 0x24418). split; [apply tab_ci; cbn; tauto | cbn; lia].
    - replace z with (shad (8 * (z - SH))) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
      apply AHM.hmA_of_ci_shadow. exists (0x24780, 0x24838). split; [apply tab_ci; cbn; tauto | cbn; lia].
    - replace z with (shad (8 * (z - SH))) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
      apply AHM.hmA_of_ci_shadow. exists (0x24860, 0x27110). split; [apply tab_ci; cbn; tauto | cbn; lia].
    - replace z with (shad (8 * (z - SH))) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
      apply AHM.hmA_of_ci_shadow. exists (0x28280, 0x28380). split; [apply tab_ci; cbn; tauto | cbn; lia].
    - replace z with (shad (8 * (z - SH))) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
      apply AHM.hmA_of_ci_shadow. exists (0x283c0, 0x2ad20). split; [apply tab_ci; cbn; tauto | cbn; lia].
    - replace z with (shad (8 * (z - SH))) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
      apply AHM.hmA_of_ci_shadow. exists (0x2ad40, 0x2afc0). split; [apply tab_ci; cbn; tauto | cbn; lia].
    - apply (AHM.hmA_of_ci AI LB4 (0x10b978, 0x10b97c)); [apply HCI; unfold client_ranges; cbn [In app]; tauto | cbn; lia].
    - hmb (HB p COPY n) ltac:(left; reflexivity).
    - hms (HB p COPY n) ltac:(left; reflexivity) z.
  Qed.
  (* [comment removed for export] *)
  Ltac kwc0 H k := solve [ unshelve eapply (kz_word_cells asegs [] _ _ _ _ _ _ _ k _ _ H); first [ reflexivity | lia | (cbn; lia) ] ].
  Lemma cnd_IK : forall (L : alayout) (RNGh : ExecF.footprint) (st : astate) E M0, AHM.hmH AI L RNGh st LB4 M0 -> know_ok asegs E M0 (SP.p_IK A2N_defs.A2N).
  Proof.
    intros L RNGh st E M0 [AH MI].
    destruct (client_rt_of_aheap AI L RNGh st _ M0 AH) as (M_GOT & _ & _ & M_SHB & M_SUAR & _ & _).
    pose proof (client_got_of_aheap AI L RNGh st _ M0 AH MI) as M_SUARG.
    pose proof (got_nothrow_cell AI L RNGh st _ M0 AH MI) as M_NT.
    unfold know_ok. cbn [SP.p_IK A2N_defs.A2N SP.PGH SP.PGX].
    repeat apply Forall_cons; try apply Forall_nil;
      match goal with |- kentry_ok _ _ _ ?K => change (kentry_ok asegs (mkEZ []) M0 K) end.
    - kwc0 M_GOT 16%nat.
    - kwc0 M_SHB 0%nat.
    - kwc0 M_SUARG 0%nat.
    - kwc0 M_SUAR 0%nat.
    - kwc0 M_NT 0%nat.
    - apply kz_img; [lia | lia | exact MI | intros a Ha; rewrite a_ro_addr; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; clear - Ha; lia].
  Qed.
End C.
End CANSEC.
