(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_ContStmt LbB_ContVot.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablStmt LbB_TablLO LbB_TablOS LbB_TablPT1 LbB_TablPT2 LbB_TablPT4 LbB_TablPT5 LbB_TablPT6 LbB_TablPT8.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section PT7.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HB : asan_rt_hyps H.

  Lemma pt_elem : forall e mL i, ppre H e -> 0 <= i < pn e -> mem_inv asegs mL -> ACONST mL ->
    let t := Znth (pn e - 1 - i) (p_l e) in
    cell4 ASEGS mL (p_p e + 4 * (pn e - 1 - i)) t /\ 0 <= t < 2 ^ 31
    /\ exists k, LbB_Kit.shk mL (p_p e + 4 * (pn e - 1 - i)) k
                 /\ (k = 0 \/ ((p_p e + 4 * (pn e - 1 - i)) mod 8 = 0 /\ 4 <= k < 8)).
  Proof.
    intros e mL i P Hi MI AC t.
    destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SPN & _ & LR & _).
    destruct SPN as (PL & PH & P4 & SPF).
    destruct (SPF mL (conj MI AC)) as [FE ACC].
    unfold pn in *.
    destruct (FE (Zlen (p_l e) - 1 - i) ltac:(lia)) as [TR FL].
    assert (TR31 : 0 <= t < 2 ^ 31).
    { subst t. rewrite Forall_forall in LR. apply LR. unfold Znth. apply nth_In. unfold Zlen in *. lia. }
    split; [split; [cbn; lia | exact FL]|]. split; [exact TR31|].
    destruct (pt_shk_word mL (p_p e) (4 * Zlen (p_l e)) (p_p e + 4 * (Zlen (p_l e) - 1 - i)) ACC ltac:(lia) ltac:(lia)
                ltac:(clear - P4; Z.div_mod_to_equations; lia)) as (k & SK & KC).
    exists k. split; [exact SK|]. destruct KC as [K0|K1]; [left; exact K0|].
    right. assert (M4 : (p_p e + 4 * (Zlen (p_l e) - 1 - i)) mod 4 = 0) by (clear - P4; Z.div_mod_to_equations; lia).
    assert (M8 : (p_p e + 4 * (Zlen (p_l e) - 1 - i)) mod 8 = 0 \/ (p_p e + 4 * (Zlen (p_l e) - 1 - i)) mod 8 = 4)
      by (clear - M4; Z.div_mod_to_equations; lia).
    lia.
  Qed.

  Lemma pt_span : forall e mL, ppre H e -> mem_inv asegs mL -> ACONST mL -> xpres H (p_LB e) (pSP e) (pXE H e) (p_m e) mL ->
    rw_cells asegs mL (p_ps e) [C8 (Z_to_bv 64 (p_p e))] /\ sh0 mL (p_ps e) /\ 0 <= p_ps e /\ p_ps e + 16 <= 2 ^ 47.
  Proof.
    intros e mL P MI AC XP.
    pose proof P as (FF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SK & PS8 & _).
    assert (FS : Forall (fs_scratch H (p_LF e)) (pXS H e)).
    { pose proof (fs_scratch_of_fresh H (p_LF e) 0 (p_ff e) (p_fp e) FF) as K. exact K. }
    destruct (SK (pXS H e) mL FS AC MI XP) as [CS ACC].
    pose proof ACC as (A0 & A1 & _).
    split; [apply (rw_cells_app asegs mL (p_ps e) [C8 (Z_to_bv 64 (p_p e))] [C8 (Z_to_bv 64 (pn e))]) in CS as [CS _]; exact CS|].
    split; [apply sh0_of_acc8; [eapply accessible_sub; [exact ACC | lia | lia | lia] | exact PS8]|].
    unfold AAPP_HI in A1. lia.
  Qed.

  Lemma pt_local_pvec : forall e ys mL M sL LBi bi capi pidi, ppre H e -> as_RHEAP H sL LBi mL ->
    pvec H e ys mL LBi bi capi pidi -> munch [(p_ff e + 32, p_ff e + 36)] mL M -> wmono asegs mL M ->
    pvec H e ys M LBi bi capi pidi.
  Proof.
    intros e ys mL M sL LBi bi capi pidi P RH PV MU WM.
    pose proof (pgeo_of H e P) as G.
    destruct G as (_ & _ & _ & _ & _ & _ & _ & _ & F64 & FL & FH & P1 & P2 & P3 & P4 & FS1 & FS2 & SH1 & SH2 & SH3 & SH4 & FB & PB
                   & V8 & VB & VL & VF & _).
    destruct (pvec_blk H HB e ys mL sL LBi bi capi pidi RH PV) as (LEN & BK & _).
    eapply pvec_munch; [exact PV | exact MU | exact WM | | | |].
    - cbn. split; [|exact I]. lia.
    - destruct BK as [(C0 & B0)|(C0 & HIn & (A0 & A16 & An & AI & AC & AF & AP))]; [subst bi; cbn; split; [lia | exact I]|].
      cbn. split; [|exact I]. unfold AFS_SIZE, AFS_HDR in *. lia.
    - intros Hc. destruct BK as [(C0 & B0)|(C0 & HIn & (A0 & A16 & An & AI & AC & AF & AP))]; [lia|].
      cbn. split; [|exact I]. destruct (pt_app_sh (p_ff e + 32) 4 bi (4 * capi) ltac:(lia) ltac:(lia) ltac:(pose proof aceil_facts; lia)
                                   ltac:(destruct FB; [left | right]; lia)) as [X|X]; lia.
    - cbn. split; [|exact I]. destruct (pt_app_sh (p_ff e + 32) 4 (p_v e) 24 ltac:(lia) ltac:(lia) ltac:(destruct VB; lia)
                                   ltac:(destruct FB; [left | right]; lia)) as [X|X]; lia.
  Qed.

  Lemma pt_step_skip : forall (e : ptent H) i msF mo (Q : config -> Prop),
    ppre H e -> 0 <= i < pn e -> Znth (pn e - 1 - i) (p_l e) = 0 ->
    pt_head H e i (mkCfg msF mo) ->
    (forall cf', pt_skip H e i cf' -> as_SR H Q cf') ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros e i msF mo Q P Hi T0 HD K.
    destruct HD as (R & mL & sL & LBi & bi & capi & pidi & eL & VIS & HF & G3 & G4 & RP & KR & MP & PM).
    destruct PM as (PF & PV & XP & AL).
    pose proof PF as (MI & AC & ST & _ & _ & _ & _ & SL & _ & _ & _ & _ & WL & _ & _ & RH & _).
    destruct (pt_span e mL P MI AC XP) as (CS & SHP & PS0 & PS16).
    destruct (pt_elem e mL i P Hi MI AC) as (CE & TR & k & SK & KC').
    pose proof P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PS8 & _ & (PL & PH & P4 & _) & _).
    pose proof (pgeo_of H e P) as G.
    destruct G as (_ & G45 & _ & GSS & _ & G47 & _ & _ & F64 & FL & FH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                   & _ & _ & _ & _ & _ & _ & _ & _ & (N0 & N48) & TP).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    destruct (pslots_parts H e mL SL ltac:(lia)) as (_ & _ & C48).
    destruct (pt_r1a R (p_F e) (p_fc e) mL (seg_rom asegs) (pSP e) (pS1 e) (p_ff e) (p_ps e) (p_v e) (pn e) i (p_p e)
                (Znth (pn e - 1 - i) (p_l e)) k RP ltac:(lia) ltac:(lia) N48 F64 ltac:(lia) ltac:(lia) WL PS0 PS16 PS8 CS SHP G45 GSS G47 C48
                PL PH P4 CE TR SK KC')
      as (R1 & M1 & RUN1 & PX1 & L10 & KK1 & MU1 & WM1 & SK1 & MI1 & CL1).
    rewrite T0 in L10.
    destruct (pt_r1z R1 (p_F e) (p_fc e) M1 (seg_rom asegs) (pSP e) (pS1 e) (p_ff e) (p_ps e) (p_v e) (pn e) i PX1 L10)
      as (R2 & RUN2 & PX2 & M8 & KK2).
    pose proof (CatSim.msteps_trans _ _ _ _ RUN1 RUN2) as RUN.
    pose proof (msteps_full asegs _ _ RUN HF) as HF2. cbn [ms_regs] in HF2.
    eapply (sr_blk H HB); [exact KR | exact VIS | exact HF | exact RUN |].
    intros msF' mo' KR' MP' VIS'. rewrite <- (rfull_eq R2 HF2) in VIS'.
    apply K. exists R2, M1, sL, LBi, bi, capi, pidi, eL.
    split; [exact VIS'|]. split; [exact HF2|].
    split; [rewrite (KK2 3%bv ltac:(inb)), (KK1 3%bv ltac:(inb)); exact G3|].
    split; [rewrite (KK2 4%bv ltac:(inb)), (KK1 4%bv ltac:(inb)); exact G4|].
    split; [split; [exact PX2 | exact M8]|]. split; [exact KR'|]. split; [exact (ah_mpres_trans H HB _ _ _ MP MP')|].
    rewrite pys_step by lia. rewrite T0. cbn [Z.eqb]. rewrite app_nil_r.
    destruct (pt_ok0_local H e LBi P) as [OK0 OKS].
    split; [eapply (pframe_munch H HB e 4 mL M1 sL LBi eL); [exact P | exact PF | exact MU1 | exact WM1 | exact (MI1 MI) | exact (SK1 _ _ ST)
                                                          | apply Forall_cons; [exact OK0 | apply Forall_nil]
                                                          | apply Forall_cons; [exact OKS | apply Forall_nil]]|].
    split; [exact (pt_local_pvec e _ mL M1 sL LBi bi capi pidi P RH PV MU1 WM1)|].
    split; [|exact AL].
    pose proof P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RH0 & _).
    eapply (xpres_trans H); [exact XP|].
    eapply (xpres_of_munch H (p_s e) (p_LB e) (pSP e) (pXE H e) _ (p_m e) mL M1); [exact HB | exact RH0 | exact MU1 | exact WM1 |].
    apply Forall_cons; [|apply Forall_nil]. right. intros a Ha. cbn [fst snd] in Ha.
    unfold pXE. cbn [rin_ivs]. right. apply rin_ivs_app. right. unfold pXS. cbn [rin_ivs fst snd]. lia.
  Qed.
End PT7.
