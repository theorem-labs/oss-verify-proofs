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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg RtCells ABase AMalloc_iface AU_iface AU_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost SegProg SegCall.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Entry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2B Require Import APS2_iface PA2_kz PA2_reg PA2_winN.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegB2N Require B2N_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.
Local Notation u := bv_unsigned.
Local Notation M64 := 18446744073709551616.
Local Notation SH := 2147450880%Z (only parsing).

Import B2N_defs.
Definition PRd : option (list SC.wn) := Some
  [(vSPA, 0, EAlu ALU_SUB (ELit (2^47)) vSPA); (vTHIS, 0, ELit 96); (vDOC, 0, ELit 16); (vBUF, 0, add vLEN (ELit 64));
   (vIDX, 0, add (mul 4 vN) (ELit 12)); (vTBASE, 0, mul 8 vCAPT); (vSBASE, 0, vCAPS); (vOCB, 0, ELit 8192); (vIAB, 0, ELit 1024);
   (vF, 0, ELit 2048); (vSHF, 0, ELit 256); (vDOC8, 2147450880, ELit 2); (mul 2 vSP16, 2147449800, ELit 1080);
   (ELit 0, 2147468976, ELit 32); (ELit 0, 2147469016, ELit 443); (ELit 0, 2147469568, ELit 23); (ELit 0, 2147469596, ELit 1302);
   (ELit 0, 2147471336, ELit 32); (ELit 0, 2147471376, ELit 1324); (ELit 0, 2147472704, ELit 80); (ELit 0, 0x1174c0, ELit 4)].

Section CANSEC. Context {rc : runConstT}.

Section P.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (LB : list ablock) (F : Z)
            (pim psi pcp ptp psb poc pia : AsanCtrl.aptr) (THIS ASI ACP TPA SBA AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia : Z)
            (cls FA FN : Z).
  Variables (zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 : Z)
            (T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG : Z)
            (V CP8 CGF ZP DG SD SRG HC HCE HBG HBGE MD : Z) (rest : list Z).
  Local Notation ZL := (ZLwn zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8
                          F11 PB FLAG BO BG IG SG V CP8 CGF ZP DG SD SRG HC HCE HBG HBGE MD rest).
  Local Notation LB6 := (mkABlock (ABFake 5) F 2048 :: LB).
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
  Hypothesis E_CAPT : ntp = 8 * CAPT.
  Hypothesis E_CAPS : nsb = CAPS.
  Hypothesis D_BO : 0 <= BO <= 7.
  Hypothesis H_PB : 0 <= PB <= 1.
  Hypothesis H_SZ : 0 <= CAPT /\ 0 <= CAPS.
  Hypothesis H_LEN : 1 <= LEN <= 1048512.
  Hypothesis H_N : 1 <= N <= LEN.
  Hypothesis H_ST : ATOP + 4096 <= 16 * SP16 - 8640.
  Hypothesis B_ALL : 0x671000 <= THIS /\ THIS + 96 <= ATOP /\ 0x671000 <= DOC /\ DOC + 16 <= ATOP /\ 0x671000 <= BUF /\ BUF + LEN + 64 <= ATOP
                  /\ 0x671000 <= ASI /\ ASI + 4 * N + 12 <= ATOP /\ 0x671000 <= TPA /\ TPA + 8 * CAPT <= ATOP /\ 0x671000 <= SBA /\ SBA + CAPS <= ATOP
                  /\ 0x671000 <= AOC /\ AOC + 8192 <= ATOP /\ 0x671000 <= AIA /\ AIA + 1024 <= ATOP /\ 0x671000 <= F /\ F + 2048 <= ATOP.
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

  Lemma wdg_agree : forall E b off k, SP.gagree 47 (mkEZ ZL) E -> eb E = eb (mkEZ ZL) ->
    expr_vars_lt 47 b = true -> expr_vars_lt 47 k = true -> zok b = true -> zok k = true ->
    SG.win_den E (b, off, k) = (zden ZL b mod M64 + off, zden ZL b mod M64 + off + zden ZL k mod M64).
  Proof.
    intros E b off k Hg Hb H1 H2 H3 H4. cbn [SG.win_den].
    rewrite <- (SP.edenot_gagree 47 (mkEZ ZL) E b Hg (eq_sym Hb) H1), <- (SP.edenot_gagree 47 (mkEZ ZL) E k Hg (eq_sym Hb) H2).
    rewrite !u_zden by assumption. reflexivity.
  Qed.

  Lemma tab_ci' : forall lo' hi', In (lo', hi') IMG_TABS -> In (lo', hi') CI.
  Proof. intros lo' hi' H. apply HCI. unfold client_ranges. apply in_or_app. right. exact H. Qed.
  Ltac shz' z := exists (8 * (z - SH)); split; [| rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia].
  Ltac inblk b I := right; right; left; exists b; split; [I | cbn [ab_addr ab_size]; lia].

  Lemma pr_client : forall E x, SP.gagree 47 (mkEZ ZL) E -> eb E = eb (mkEZ ZL) -> SC.in_PR E PRd x ->
    aclient_addr CI LB6 (16 * SP16 + -416 - 16 * PB) x.
  Proof using All.
    intros E x Hg Hb (w & Hw & Hx). unfold PRd in Hw.
    cbv [B2N_defs.vSP B2N_defs.vSP16 B2N_defs.vTHIS B2N_defs.vT8 B2N_defs.vDOC B2N_defs.vDOC8 B2N_defs.vBUF B2N_defs.vB8 B2N_defs.vBO
         B2N_defs.vLEN B2N_defs.vIDX B2N_defs.vI8 B2N_defs.vN B2N_defs.vTBASE B2N_defs.vTB8 B2N_defs.vCAPT B2N_defs.vSBASE B2N_defs.vSB8
         B2N_defs.vCAPS B2N_defs.vOCB B2N_defs.vOC8 B2N_defs.vIAB B2N_defs.vIA8 B2N_defs.vF B2N_defs.vF11 B2N_defs.vSHF B2N_defs.vSPA
         B2N_defs.vPB B2N_defs.V B2N_defs.mul B2N_defs.add B2N_defs.sub] in Hw.
    atop_facts.
    repeat (destruct Hw as [<-|Hw]; [unfold SC.in_win in Hx; rewrite wdg_agree in Hx by (assumption || reflexivity);
                                      cbn [fst snd zden nth ZLwn app] in Hx; rewrite ?(Z.mod_small _ M64) in Hx by (atop_facts; lia) |]);
      [..| destruct Hw].
    - left. lia.
    - inblk (HB pim THIS nim) ltac:(right; exact Ith).
    - inblk (mkABlock (ABFake cls) FA FN) ltac:(right; exact Ifk).
    - inblk (HB pcp ACP ncp) ltac:(right; exact Icp).
    - inblk (HB psi ASI nsi) ltac:(right; exact Isi).
    - inblk (HB ptp TPA ntp) ltac:(right; exact Itp).
    - inblk (HB psb SBA nsb) ltac:(right; exact Isb).
    - inblk (HB poc AOC noc) ltac:(right; exact Ioc).
    - inblk (HB pia AIA nia) ltac:(right; exact Iia).
    - inblk (mkABlock (ABFake 5) F 2048) ltac:(left; reflexivity).
    - right; right; right. shz' x. right; right. exists 5, F, 2048. split; [left; reflexivity | lia].
    - right; right; right. shz' x. right; right. exists cls, FA, FN. split; [right; exact Ifk | lia].
    - right; right; right. shz' x. left. lia.
    - right; right; right. shz' x. right; left. exists (0x23580, 0x23680). split; [apply tab_ci'; cbn; tauto | cbn; lia].
    - right; right; right. shz' x. right; left. exists (0x236c0, 0x24498). split; [apply tab_ci'; cbn; tauto | cbn; lia].
    - right; right; right. shz' x. right; left. exists (0x24800, 0x248b8). split; [apply tab_ci'; cbn; tauto | cbn; lia].
    - right; right; right. shz' x. right; left. exists (0x248e0, 0x27190). split; [apply tab_ci'; cbn; tauto | cbn; lia].
    - right; right; right. shz' x. right; left. exists (0x27f40, 0x28040). split; [apply tab_ci'; cbn; tauto | cbn; lia].
    - right; right; right. shz' x. right; left. exists (0x28080, 0x2a9e0). split; [apply tab_ci'; cbn; tauto | cbn; lia].
    - right; right; right. shz' x. right; left. exists (0x2aa00, 0x2ac80). split; [apply tab_ci'; cbn; tauto | cbn; lia].
    - right; left. exists (0x1174c0, 0x1174c4). split; [apply HCI; unfold client_ranges; cbn [In app]; tauto | cbn; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma pr_frame : forall E (m5 m6 : amem), SP.gagree 47 (mkEZ ZL) E -> eb E = eb (mkEZ ZL) ->
    aheap_pres CI LB6 (16 * SP16 + -416 - 16 * PB) m5 m6 ->
    forall x : word, SC.in_PR E PRd (u x) -> m6 x = m5 x.
  Proof using All.
    intros E m5 m6 Hg Hb HP x Hx.
    pose proof (pr_client E (u x) Hg Hb Hx) as HCL.
    assert (Rx : 0 <= u x < 2^64) by (pose proof (bv_unsigned_in_range 64 x) as H; unfold bv_modulus in H; exact H).
    destruct (HP (u x) Rx HCL) as [HE _].
    unfold wa in HE. rewrite Z_to_bv_bv_unsigned in HE. exact HE.
  Qed.
End P.
End CANSEC.
