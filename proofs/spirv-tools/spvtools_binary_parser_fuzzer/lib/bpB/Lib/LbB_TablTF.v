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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_DStat LbB_ContStmt LbB_ContV4R LbB_ContV4 LbB_ContVot.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablStmt LbB_TablOS LbB_TablPT1 LbB_TablPT4 LbB_TablPT6 LbB_TablPT8 LbB_TablPT9 LbB_TablPT11.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablXP1 LbB_TablXPk1 LbB_TablXPm1 LbB_TablXP LbB_TablTF1 LbB_TablTFk LbB_TablTF2.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma Zlen_removelast : forall (xs : list Z), xs <> [] -> Zlen (removelast xs) = Zlen xs - 1.
Proof.
  intros xs NE. rewrite (app_removelast_last 0 NE) at 2. unfold Zlen. rewrite length_app. cbn [length]. lia.
Qed.

Lemma expand_props : forall t l, PrsGrammar.expand t = Some l ->
  l <> [] /\ PrsGrammar.expand (last l 0) = None /\ expandA (last l 0) = [] /\ xres (last l 0) = 0.
Proof.
  intros t l E. unfold PrsGrammar.expand in E. cbv -[Z.eqb] in E.
  repeat (destruct (t =? _); [injection E as <-; cbv; repeat split; try reflexivity; intros X; discriminate X|]).
  discriminate E.
Qed.

Lemma tf_ret_ok : v4_ret_ok TF_RET.
Proof.
  intros Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m HQ.
  unfold TF_RET. step. apply evt_done. exact HQ.
Qed.

Section TF.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps_bp H.

  Definition tQ (e : tfent H) (ys : list Z) (t : Z) : config -> Prop :=
    pat_post H (t_ra e) (t_sp e) (t_gp e) (t_tp e) (t_s0 e) (t_s1 e) (t_s2 e) (t_s3 e) (t_s4 e) (t_s5 e) (t_s6 e) (t_s7 e) (t_s8 e)
             (t_s9 e) (t_s10 e) (t_s11 e) (t_F e) (t_fc e) (t_s e) (t_LB e) (t_LF e) (t_v e) (t_b e) (t_cap e) (tcapm e)
             ys (t_pid e) (t_lo e) (t_B e) (t_shi e) (t_m e) (t_mo e) (fun r0 => r0 = Z_to_bv 64 t).

  Lemma tf_fin : forall (e : tfent H) ys t XS LBi bi capi pidi msF mo,
    tpre H e -> tx H e ys t 0 XS LBi bi capi pidi (mkCfg msF mo) -> as_SR H (tQ e ys t) (mkCfg msF mo).
  Proof.
    intros e ys t XS LBi bi capi pidi msF mo P TX.
    pose proof (rt_bp_base H HH) as HB.
    destruct TX as (R & mL & sL & eL & VIS & HF & TR & R19 & R10 & KR & MP & TM).
    cbn [cfg_ms cfg_model] in VIS, MP.
    destruct TM as (TFm & TV & FS & XP & AL).
    pose proof TFm as (MI & AC & ST & S00 & ER & RA & SV & RF & RH & OW & RR).
    pose proof TV as (VEC & SH & AD & WV & OB & GR & F31).
    pose proof P as (SP16 & SPH & SPB & SPS & CE & LO & FSB & LFL & TP & RAE & V8 & VB & OBJ & OLD & ND & RH0 & BU1 & BU2 & BU3 & BU4
                     & TRO & TRO2 & AL0 & XL & BNZ & BB & BD & XS31 & RR0).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    unfold TF_STACK, XP_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO.
    destruct TR as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27).
    destruct (tf_exit R (t_F e) (t_fc e) mL (seg_rom asegs) (t_ra e) (t_s0 e) (t_s1 e) (t_s2 e) (t_s3 e) (t_s4 e) (t_s5 e) (t_s6 e) (t_s7 e)
                (t_s8 e) (tSP e) R10 Q2 HF ltac:(clear - LO CE ACF1 SPH; lia) SV MI)
      as (R1 & RUN & HF1 & KK & L1 & L2 & L8 & L9 & L18 & L19 & L20 & L21 & L22 & L23 & K24 & L10).
    assert (SPv : Z_to_bv 64 (tSP e) = t_sp e) by (unfold tSP; apply Z_to_bv_bv_unsigned).
    rewrite SPv in L2. rewrite R19 in L10.
    assert (K3 : getr R1 3 = t_gp e) by (rewrite (KK 3%bv ltac:(inb)); exact Q3).
    assert (K4 : getr R1 4 = t_tp e) by (rewrite (KK 4%bv ltac:(inb)); exact Q4).
    assert (K25 : getr R1 25 = t_s9 e) by (rewrite (KK 25%bv ltac:(inb)); exact Q25).
    assert (K26 : getr R1 26 = t_s10 e) by (rewrite (KK 26%bv ltac:(inb)); exact Q26).
    assert (K27 : getr R1 27 = t_s11 e) by (rewrite (KK 27%bv ltac:(inb)); exact Q27).
    eapply (sr_evt H HB) with
      (P := fun ms => ms = MS (mkR (t_ra e) (t_sp e) (t_gp e) (t_tp e) (getr R1 5) (getr R1 6) (getr R1 7) (t_s0 e) (t_s1 e)
                                   (Z_to_bv 64 t) (getr R1 11) (getr R1 12) (getr R1 13) (getr R1 14) (getr R1 15) (getr R1 16) (getr R1 17)
                                   (t_s2 e) (t_s3 e) (t_s4 e) (t_s5 e) (t_s6 e) (t_s7 e) (t_s8 e) (t_s9 e) (t_s10 e) (t_s11 e)
                                   (getr R1 28) (getr R1 29) (getr R1 30) (getr R1 31))
                              (t_F e) (ret_pc (t_ra e)) (t_fc e) None mL (seg_rom asegs));
      [exact KR | exact VIS | |].
    { eapply evt_of_msteps; [exact RUN|]. rewrite (rfull_eq R1 HF1). apply tf_ret_ok.
      rewrite L1, L2, K3, K4, L8, L9, L10, L18, L19, L20, L21, L22, L23, K24, K25, K26, K27. reflexivity. }
    intros msF' mo' KR' MP' HP. cbv beta in HP.
    unfold tQ, pat_post.
    exists (getr R1 5), (getr R1 6), (getr R1 7), (Z_to_bv 64 t), (getr R1 11), (getr R1 12), (getr R1 13), (getr R1 14),
      (getr R1 15), (getr R1 16), (getr R1 17), (getr R1 28), (getr R1 29), (getr R1 30), (getr R1 31), mL, eL, sL, LBi, bi, capi, XS.
    cbn [cfg_ms cfg_model].
    split; [exact HP|]. split; [reflexivity|]. split; [exact KR'|]. split; [exact (ah_mpres_trans H HB _ _ _ MP MP')|].
    split; [exact MI|]. split; [exact ST|]. split; [exact ER|]. split; [exact RA|].
    split; [exact VEC|]. split; [exact RH|]. split; [exact SH|]. split; [exact AD|]. split; [exact WV|]. split; [exact OW|].
    split; [exact FS|].
    split.
    { unfold tSP, tXE in XP. destruct GR as [(E1 & E2 & E3 & E4)|(G1 & G2 & G3')].
      - left. split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
        eapply (xpres_weaken H); [exact XP | lia | intros bb Hb; exact Hb |].
        intros a Ha. unfold v4_oldx in Ha. destruct (Z.eqb_spec (t_b e) 0) as [X|_]; [exfalso; exact (BNZ X)|]. exact Ha.
      - right. split; [exact G1|]. split; [exists pidi; split; [exact G2 | exact G3']|]. exact XP. }
    split; [exact RF|]. split; [exact AC|]. split; [exact S00|]. exact AL.
  Qed.

  Lemma tf_loop : forall (e : tfent H) ys t XS LBi bi capi pidi msF mo (Q : config -> Prop),
    tx H e ys t 1 XS LBi bi capi pidi (mkCfg msF mo) ->
    (forall msF' mo', th H e ys XS LBi bi capi pidi (mkCfg msF' mo') -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros e ys t XS LBi bi capi pidi msF mo Q TX K.
    pose proof (rt_bp_base H HH) as HB.
    destruct TX as (R & mL & sL & eL & VIS & HF & TR & R19 & R10 & KR & MP & TM).
    cbn [cfg_ms cfg_model] in VIS, MP.
    destruct (tf_back R (t_F e) (t_fc e) mL (seg_rom asegs) R10 HF) as (R1 & RUN & HF1 & KK).
    eapply (sr_blk H HB); [exact KR | exact VIS | exact HF | exact RUN |].
    intros msF' mo' KR' MP' VIS'. rewrite <- (rfull_eq R1 HF1) in VIS'.
    apply K. exists R1, mL, sL, eL. cbn [cfg_ms cfg_model].
    split; [exact VIS'|]. split; [exact HF1|].
    split.
    { destruct TR as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27). unfold tregs.
      rewrite (KK 2%bv ltac:(inb)), (KK 3%bv ltac:(inb)), (KK 4%bv ltac:(inb)), (KK 8%bv ltac:(inb)), (KK 9%bv ltac:(inb)),
        (KK 18%bv ltac:(inb)), (KK 20%bv ltac:(inb)), (KK 21%bv ltac:(inb)), (KK 22%bv ltac:(inb)), (KK 23%bv ltac:(inb)),
        (KK 24%bv ltac:(inb)), (KK 25%bv ltac:(inb)), (KK 26%bv ltac:(inb)), (KK 27%bv ltac:(inb)).
      repeat (split; [assumption|]). exact Q27. }
    split; [exact KR'|]. split; [exact (ah_mpres_trans H HB _ _ _ MP MP')|]. exact TM.
  Qed.

  Theorem take_first_okA : take_first_stmtA H.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LB LF
      v b cap xs pid lo B shi errv VIS Ha0 XNE XS31 RR PRE.
    pose proof (rt_bp_base H HH) as HB.
    destruct PRE as (VEC & V8 & ADV & OBJ & VB & WV & OWN & OLD & OSH & BU1 & BU2 & BU3 & BU4 & RH & KR & AL0 & TRO & TRO2
                     & RA & SPB & SP16 & SP47 & ST & CE & LO & ER & MI & TP & RA2 & AC & RF & LFL & S0 & SHI).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    set (SP := bv_unsigned sp) in *.
    assert (Hsp : sp = Z_to_bv 64 SP) by (subst SP; symmetry; apply Z_to_bv_bv_unsigned).
    assert (LO' : lo <= SP - 80 - 192 - 1024 - 2 * 4096 - 2 * 8304)
      by (unfold TF_STACK, XP_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO; lia).
    set (e := TFEnt H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF v b cap xs pid lo B shi).
    pose proof VEC as (_ & _ & _ & LEN & BK & _).
    assert (XL1 : 1 <= Zlen xs) by (destruct xs; [exfalso; exact (XNE eq_refl) | unfold Zlen; cbn [length]; lia]).
    destruct BK as [(B0 & C0)|(B0 & B16 & C0 & BC & HIn' & DJ)]; [lia|].
    destruct OLD as [(X & _)|(_ & HIn)]; [lia|].
    pose proof (ah_blocks H HB _ _ _ _ RH HIn) as ABR. cbn [blk_addr blk_size fst snd] in ABR.
    pose proof ABR as (A0 & A16 & An & AI & ACe & AF & AP).
    assert (P : tpre H e).
    { unfold tpre. cbn [tSP t_v t_LB t_LF t_lo t_B t_shi t_tp t_ra t_b t_cap t_pid t_s t_m t_xs tcapm e]. fold SP.
      split; [exact SP16|]. split; [exact SP47|]. split; [exact SPB|]. split; [exact SHI|]. split; [exact CE|]. split; [exact LO|].
      split; [exact (RFS_fsb H HB _ _ RF)|]. split; [exact LFL|]. split; [exact TP|]. split; [exact RA2|].
      split; [exact V8|]. split; [exact VB|]. split; [exact OBJ|]. split; [right; split; [exact C0 | exact HIn]|]. split; [exact (ah_nodup H HB _ _ _ RH)|]. split; [exact RH|].
      split; [exact BU1|]. split; [exact BU2|]. split; [exact BU3|]. split; [exact BU4|]. split; [exact TRO|]. split; [exact TRO2|]. split; [exact AL0|].
      split; [lia|]. split; [lia|].
      split; [unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in AP; destruct AP; [left | right]; lia|].
      split; [exact DJ|]. split; [exact XS31|]. exact RR. }

    remember (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    destruct (tf_b1 R F fc m (seg_rom asegs) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 SP v lo ltac:(rewrite HR0; reflexivity) ltac:(rewrite HR0, Hsp; reflexivity)
                ltac:(rewrite HR0; reflexivity) ltac:(rewrite HR0; reflexivity) ltac:(rewrite HR0; reflexivity) ltac:(rewrite HR0; reflexivity)
                ltac:(rewrite HR0; reflexivity) ltac:(rewrite HR0; reflexivity) ltac:(rewrite HR0; reflexivity) ltac:(rewrite HR0; reflexivity)
                ltac:(rewrite HR0; reflexivity)
                ltac:(rewrite HR0; exact Ha0) HF SP16 ltac:(lia) ltac:(destruct VB; lia) ltac:(destruct VB; lia) ltac:(destruct VB; lia) V8 ST ltac:(lia) MI AC)
      as (R1 & m1 & RUN1 & HF1 & KK1 & L2 & L8 & L9 & L18 & L20 & L21 & L22 & L23 & L24 & MU1 & WM1 & MI1 & SK1 & CS1).
    eapply (sr_blk H HB); [exact KR | exact VIS | exact HF | exact RUN1 |].
    intros msF1 mo1 KR1 MP1 VIS1. rewrite <- (rfull_eq R1 HF1) in VIS1.

    assert (X2 : as_FSB H + AFS_SIZE <= aceil) by (pose proof (ah_RFS_range H HB _ _ RF) as [(_ & X & _) _]; exact X).
    assert (X1 : aceil <= SP - 80) by (clear - CE LO'; lia).
    pose proof (stack_window_ok H LB LF (SP - 80) SP X1 X2) as (W1a & W1b & W1c).
    assert (TH : th H e (removelast xs ++ [last xs 0]) [] LB b cap pid (mkCfg msF1 mo1)).
    { rewrite <- (app_removelast_last 0 XNE).
      exists R1, m1, s, errv. cbn [cfg_ms cfg_model].
      split; [exact VIS1|]. split; [exact HF1|].
      split.
      { unfold tregs. cbn [tSP t_v t_gp t_tp t_s8 t_s9 t_s10 t_s11 e]. fold SP.
        rewrite (KK1 3%bv ltac:(inb)), (KK1 4%bv ltac:(inb)), (KK1 25%bv ltac:(inb)), (KK1 26%bv ltac:(inb)), (KK1 27%bv ltac:(inb)).
        rewrite HR0. repeat (split; [first [assumption | reflexivity]|]). reflexivity. }
      split; [exact KR1|]. split; [exact MP1|].
      split.
      { unfold tframe. cbn [tSP t_lo t_shi t_tp t_B t_LF tsaved t_s0 t_s1 t_s2 t_s3 t_s4 t_s5 t_s6 t_s7 t_s8 t_ra e]. fold SP.
        split; [exact MI1|]. split; [eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 | apply Forall_cons; [exact W1c | apply Forall_nil]]|].
        split; [exact (SK1 _ _ ST)|].
        split; [eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 | apply Forall_cons; [left; cbn [fst]; unfold AHI_LO; lia | apply Forall_nil]]|].
        split.
        { eapply rw_cells_transport; [exact ER | exact MU1 | exact WM1 |].
          assert (ERA : errno_addr tp = ATP - 164) by (rewrite TP, HLib.u64_of_Z by (unfold ATP; lia); lia).
          rewrite ERA. unfold ATP. cbn. clear - CE LO' ACF1. split; [lia | exact I]. }
        split; [eapply (ah_rauxv_frame H HB); [exact RA | exact MU1 | exact WM1 | apply Forall_cons; [exact W1a | apply Forall_nil]]|].
        split; [exact CS1|].
        split; [eapply (ah_RFS_frame H HB); [exact RF | exact MU1 | exact WM1 | apply Forall_cons; [exact W1b | apply Forall_nil]]|].
        split; [eapply (ah_RHEAP_frame H HB); [exact RH | exact MU1 | exact WM1 | apply Forall_cons; [exact W1a | apply Forall_nil]]|].
        split; [exact (lb_own_wmono _ _ _ OWN WM1)|].
        intros i Hi. rewrite (MU1 (Z_to_bv 64 i)); [apply RR; exact Hi|]. rewrite u64_of_Z by lia. cbn [outside]. clear - Hi CE LO' ACF1. lia. }
      split.
      { unfold tvec. cbn [t_v t_b t_cap t_pid e].
        destruct OBJ as (_ & _ & _ & _ & _ & VL).
        split.
        { eapply (vec32A_munch LB m m1 v b xs cap _ VEC MU1); cbn; [clear - VL CE LO'; split; [lia | exact I]|].
          clear - ACe CE LO' LEN XL1. split; [lia | exact I]. }
        split.
        { intros Hc. eapply SHAD_transport; [exact (OSH Hc) | exact MU1 | exact WM1 |]. rewrite cc_gen_length by lia. cbn.
          assert (SHB : sh b + nsh (4 * cap) <= sh (b + 4 * cap) + 1) by (clear; unfold sh, nsh; Z.div_mod_to_equations; lia).
          pose proof (sh_lt_2_45 (b + 4 * cap) ltac:(clear - A0 C0 ACe ACF2; lia)) as SB2.
          clear - SHB SB2 CE LO' ACF1. split; [lia | exact I]. }
        split.
        { eapply addressable_transport; [exact ADV | exact MU1 | exact WM1 |]. change (nsh 24) with 3. cbn.
          pose proof (sh_lt_2_45 (v + 24) ltac:(clear - VB; destruct VB; lia)) as SV.
          assert (sh v + 3 <= sh (v + 24) + 1) by (clear; unfold sh; Z.div_mod_to_equations; lia).
          clear - SV H0 CE LO' ACF1. split; [lia | exact I]. }
        split; [exact (wr_at_wmono _ _ _ _ WV WM1)|].
        split; [right; split; [exact C0 | exact HIn]|]. split; [left; repeat split; reflexivity | exact XS31]. }
      split; [apply Forall_nil|].
      split.
      { unfold tSP, tXE. cbn [t_LB t_v t_b t_cap t_m e]. fold SP.
        eapply (xpres_of_munch H s LB SP _ _ m m m1); [exact HB | exact RH | exact MU1 | exact WM1 |].
        apply Forall_cons; [left; cbn [fst snd]; clear - CE LO'; lia | apply Forall_nil]. }
      cbn [t_s t_cap e]. rewrite closs_refl. lia. }
    clear VIS1 MU1 WM1 SK1 CS1.

    eapply (tf_iter H HH e (removelast xs) (last xs 0) [] LB b cap pid msF1 mo1 _ P TH).
    { intros _. cbn [t_cap t_b t_LB t_pid t_xs e]. repeat (split; [reflexivity|]). exact (Zlen_removelast xs XNE). }
    intros msF2 mo2 XS' LB' b' cap' pid' TX. cbn [app] in TX.
    change (pat_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF v b cap (capmax (Zlen xs - 1) cap 3)
              (snd (take_first xs)) pid lo B shi m mo (fun r0 => r0 = Z_to_bv 64 (fst (take_first xs))))
      with (tQ e (snd (take_first xs)) (fst (take_first xs))).
    unfold take_first.
    destruct (PrsGrammar.expand (last xs 0)) as [l|] eqn:ET.
    -
      destruct (expand_props _ _ ET) as (LNE & EN2 & EA2 & XR2).
      unfold expandA, xres in TX. rewrite ET in TX. cbn [fst snd].
      eapply (tf_loop e _ _ _ _ _ _ _ msF2 mo2 _ TX).
      intros msF3 mo3 TH3.
      rewrite (app_removelast_last 0 LNE), app_assoc in TH3.
      eapply (tf_iter H HH e (removelast xs ++ removelast l) (last l 0) XS' LB' b' cap' pid' msF3 mo3 _ P TH3).
      { intros X. exfalso. exact (X EN2). }
      intros msF4 mo4 XS'' LB'' b'' cap'' pid'' TX4.
      rewrite EA2, XR2, app_nil_r in TX4.
      exact (tf_fin e _ _ _ _ _ _ _ msF4 mo4 P TX4).
    -
      unfold expandA, xres in TX. rewrite ET, app_nil_r in TX. cbn [fst snd].
      exact (tf_fin e _ _ _ _ _ _ _ msF2 mo2 P TX).
  Qed.
End TF.
