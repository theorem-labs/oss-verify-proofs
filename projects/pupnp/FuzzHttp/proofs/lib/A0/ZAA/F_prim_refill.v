(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimRefill APrimQ APrimFrame F_prim_icr F_prim_gfa2 ATacFix.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac post_callA_u segs m UNF :=
  let a := fresh "r" in let H' := fresh "H'" in let ms' := fresh "ms'" in let PO := fresh "POST" in let MC := fresh "MC" in
  intros a H' ms' [PO MC];
  destruct_exs PO;
  let E := fresh "E" in let EH := fresh "EH" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [EH [MUc [WMc PO]]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms'; subst H'; clean_ms_mem MC;
  try destruct_ands PO;
  UNF MUc;
  lazymatch type of MUc with
  | munch _ m ?m' =>
      absorb_footprint MUc m; transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with Hh : mem_inv segs m |- _ => clear Hh end;
      try clear m
  end;
  lz_cont MC;
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
       end).
Tactic Notation "callAu" uconstr(SPEC) "unfolding" tactic3(UNF) :=
  lz_here;
  lazymatch goal with
  | |- ITreeLZ.implL ?segs _ _ _ _ _ (MS _ _ _ _ _ ?m _) =>
      let C := find_mclean m in
      eapply implA_ebind; [ eapply implA_mclean; [ exact C | eapply SPEC ] | clear C; post_callA_u segs m UNF ]
  end.

Section RFL.
  Context {HC : HasCeiling}.
  Variables (AL : alayout) (E : penv).
  Notation THR := (at_thr (al_thread AL)).
  Notation CACHE := (at_thr (al_thread AL) + CACHE_OFF).

  #[using="Type"] Lemma gfa_W_miss : forall lo q c c' (k k' k0 : pclass),
    alayout_ok AL -> 1 <= c <= 31 -> 1 <= c' <= 31 -> c' <> c ->
    0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q ->
    0 <= p_nf k -> 0 <= p_mfa k <= K_FA_SIZE -> 0 <= p_mu k <= FA_OFF -> 0 <= p_mfa k' <= K_FA_SIZE -> 0 <= p_mu k' <= FA_OFF ->
    Forall (cls_miss AL c' k0) (gfa_W AL lo q c k k').
  Proof.
    intros lo q c c' k k' k0 AO Hc Hc' NE LOH CLO LQ NF0 MF0 MU0 MFK MUK.
    layout_facts AO 0%nat SPF. destruct SPF as (S1 & S2 & _ & _ & S5 & _ & S7).
    pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (_ & _ & T3 & T4 & _).
    layout_apart_fact AO 0%nat 3%nat LP03.
    pose proof (region_range AL c Hc) as [R1 R2]. pose proof (region_range AL c' Hc') as [R1' R2'].
    assert (SHS : forall x, region AL c <= x <= region AL c + K_REGION -> sh (region AL c) <= sh x <= sh (region AL c + K_REGION))
      by (intros x Hx; split; apply sh_le; lia).
    pose proof (SHS (region AL c + p_mu k) ltac:(lia)) as X1. pose proof (SHS (region AL c + p_mu k') ltac:(lia)) as X2.
    pose proof (SHS (fa_base AL c + p_mfa k) ltac:(unfold fa_base; lia)) as X3. pose proof (SHS (fa_base AL c + p_mfa k') ltac:(unfold fa_base; lia)) as X4.
    clear SHS.
    pose proof (sh_le 0 (region AL c) ltac:(lia)) as L0. change (sh 0) with 2147450880 in L0.
    pose proof (sh_le 0 (region AL c') ltac:(lia)) as L0'. change (sh 0) with 2147450880 in L0'.
    pose proof (sh_le (region AL c + K_REGION) (2^47) ltac:(lia)) as U0. change (sh (2^47)) with 17594333495296 in U0.
    pose proof (sh_le (region AL c' + K_REGION) (2^47) ltac:(lia)) as U0'. change (sh (2^47)) with 17594333495296 in U0'.
    pose proof (S7 (region AL c + K_REGION) ltac:(lia)) as V0. pose proof (S7 (region AL c' + K_REGION) ltac:(lia)) as V0'.
    assert (ORD : sh (region AL c + K_REGION) <= sh (region AL c') \/ sh (region AL c' + K_REGION) <= sh (region AL c)).
    { destruct (Z_lt_le_dec c c') as [LT|GE]; [left| right]; apply sh_le; unfold region; lia. }
    assert (ORB : region AL c + K_REGION <= region AL c' \/ region AL c' + K_REGION <= region AL c) by (unfold region; lia).
    unfold gfa_W, cls_miss, cls_miss_body, pcl_addr, ri_addr, RIB, fa_base in *.
    repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; (split; [lia| split; [lia| left; lia]]).
  Qed.

  #[using="Type"] Lemma refill_tail : forall (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32)
         (m : mem) (H : word -> bool) (q lo c : Z) (P : prim) (m1 : mem) (junk8 : list byte)
         (rra x5 x6 x7 xs1 a3 a5 a6 a7 x28 x29 x30 x31 : word),
    alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q - REFILL_STACK -> q <= 2^47 -> q mod 16 = 0 ->
    1 <= c <= 31 -> p_cnt (get_cls P c) = 0 -> refill_budget c (get_cls P c) ->
    0 <= pr_calloc P -> 0 <= pr_cmapped P -> pr_cmapped P + K_REGION < 2^63 ->
    munch [(q - 32, q); (CACHE, CACHE + 2592)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
    shvis H m1 -> poison_env E m1 -> thread_env (al_thread AL) m1 ->
    stk asegs m1 lo (q - 32) -> rw_cells asegs m1 (q - 32) [CB 8 junk8; C8 s1; C8 s0; C8 ra] ->
    RPRIM AL (mkPRIM (pr_cls P) true (pr_calloc P) (pr_cmapped P)) m1 ->
    evt asegs (lzk H (t_refill AL c (get_cls P c))
                   (refill_post AL E ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc q lo c P H m))
      (MS (mkR rra (wz (q - 32)) gp (wz A0_TP) x5 x6 x7 (wz (pcl_addr AL c)) xs1 (wz CACHE) (wz (max_count c)) (wz INSTANCE) a3 (wz c) a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F_ (wz 0x38468) fc None m1 (seg_rom asegs)).
  Proof.
    intros until x31. intros AO LOH CLO LO QH Q16 Hc C0 RB CA0 CM0 CMB MU WM MI1 SV1 PE1 TE1 ST1 FR1 RP1.
    unfold REFILL_STACK, POP_STACK, MF_STACK in *.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & _).
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
    layout_apart_fact AO 0%nat 3%nat LP03.
    hide T1. hide T5. hide T6. hide T7. hide SPM.
    set (Pi := mkPRIM (pr_cls P) true (pr_calloc P) (pr_cmapped P)) in *.
    set (k := get_cls P c) in *.
    assert (EKi : forall c', get_cls Pi c' = get_cls P c') by reflexivity.
    pose proof RP1 as (LEN & PENV & CLS & STAT & (ts & TS)). cbn [pr_inited pr_calloc pr_cmapped Pi] in CLS, STAT.
    pose proof (CLS c Hc) as CR. rewrite EKi in CR. fold k in CR.
    pose proof (max_count_range c Hc) as (MR & _).
    unfold pcl_addr. unfold t_refill.
    zstep.
    replace (bv_swrap 32 (Z.shiftr (bv_wrap 32 (max_count c)) 1)) with (max_count c / 2).
    2: { unfold bv_wrap, bv_modulus. rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
         rewrite STRW_merge.swrap32_small; [reflexivity|]. clear - MR. Z.div_mod_to_equations. lia. }
    do 2 zstep.
    zstep.
    do 3 zstep.
    zstep.

    assert (CLSo : forall c', 1 <= c' <= 31 -> c' <> c -> cls_rep AL m1 true c' (get_cls P c')) by (intros c' Hc' _; rewrite <- EKi; exact (CLS c' Hc')).
    destruct CR as (WF & CRr).
    pose proof (refill_wf c k Hc WF (proj1 RB) (proj2 RB) C0) as WFR.
    clear CLS.
    pose proof (munch_refl [(lo, q - 32); (ri_addr AL c, ri_addr AL c + 128); (fa_base AL c + 4 * p_nf k, fa_base AL c + p_mfa (refill k c));
       (region AL c + p_mu k, region AL c + p_mu (refill k c)); (fa_base AL c + p_mfa k, fa_base AL c + p_mfa (refill k c));
       (sh (region AL c + p_mu k), sh (region AL c + p_mu (refill k c))); (sh (fa_base AL c + p_mfa k), sh (fa_base AL c + p_mfa (refill k c)));
       (pcl_addr AL c + 16, pcl_addr AL c + 80);
       (at_thr (al_thread AL) + CSTATS_OFF + 16, at_thr (al_thread AL) + CSTATS_OFF + 32);
       (at_thr (al_thread AL) + TSTATS_OFF, at_thr (al_thread AL) + TSTATS_OFF + 368)] m1) as MUx.
    pose proof (wmono_refl asegs m1) as WMx.
    lazymatch type of MUx with munch ?Wx _ _ => apply (munch_extend _ Wx) in MU; cbn [List.app] in MU end.
    hide FR1.
    callAu (gfa_spec AL E _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc m1 H (q - 32) lo c k (pr_calloc P) (pr_cmapped P) AO MI1) unfolding (fun h => unfold gfa_W in h);
      [ assumption | exact SV1 | exact PE1 | exact TE1 | exact PENV | exact ST1 | exact LOH | exact CLO
      | unfold GFA_STACK, POP_STACK, MF_STACK; clear - LO; lia | clear - QH; lia | clear - Q16; Z.div_mod_to_equations; lia
      | exact Hc | split; [exact WF| exact CRr] | exact C0 | split; [exact STAT| exists ts; exact TS] | exact RB | exact CA0 | exact CM0 | exact CMB | ].
    destruct r.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mG end.
    rename PC into STG, PC0 into PEG, PC1 into TEG, PC2 into PENVG, PC3 into SVG, PC4 into WFG, PC5 into RIG, PC6 into PCG, PC7 into PAG,
           PC8 into FAG, PC9 into TLG, PC10 into FCHG, POST into SRG, MI into MIG.
    unfold pcl_addr in PCG.

    unhide FR1.
    assert (FRG : rw_cells asegs mG (q - 32) [CB 8 junk8; C8 s1; C8 s0; C8 ra]).
    { destruct WFR as (_ & _ & _ & _ & MFAr & _ & AUr & MUFr & _). destruct WF as (Lnf & _ & _ & _ & MFAk & _ & AUk & MUFk & _).
      pose proof (region_range AL c Hc) as [R1 R2].
      pose proof (sh_le (region AL c + p_mu (refill k c)) (2^47) ltac:(lia)) as U1. change (sh (2^47)) with 17594333495296 in U1.
      pose proof (sh_le (fa_base AL c + p_mfa (refill k c)) (2^47) ltac:(unfold fa_base; lia)) as U2. change (sh (2^47)) with 17594333495296 in U2.
      eapply rw_cells_transport; [exact FR1| exact MUx| exact WMx|]. cbn [disjoint_from cells_size csize Nat.add].
      unfold ri_addr, RIB, fa_base, pcl_addr in *. clear - LO CLO LOH ACR SP2 R1 R2 Hc T4 U1 U2 MFAr MUFr. lia. }
    clear FR1. hide MUx. hide WMx.

    pose proof (munch_refl [(q - 32, q); (CACHE + 80 * c, CACHE + 80 * c + 4)] mG) as MUy. pose proof (wmono_refl asegs mG) as WMy.
    zstep. if_false_z.
    remember (CACHE + 80 * c) as pcb eqn:Hpcb in *.
    zstep.
    do 3 zstep.
    zstep. replace (q - 32 + 32) with q by lia. zstep.
    release_frame FRG STG q.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
    unhide MUx. unhide WMx. unhide T1. unhide T5.
    pose proof (region_range AL c Hc) as [R1 R2].
    assert (PCB : THR + 288 <= pcb /\ pcb + 80 <= THR + 2768) by (rewrite Hpcb; clear - Hc; lia).
    assert (SHc : 2147450880 <= sh (region AL c) /\ sh (region AL c + K_REGION) <= 17594333495296).
    { split; [pose proof (sh_le 0 (region AL c) ltac:(lia)) as X; exact X| pose proof (sh_le (region AL c + K_REGION) (2^47) ltac:(lia)) as X; exact X]. }

    assert (AIy : above_img [(q - 32, q); (pcb, pcb + 4)]) by (clear - PCB T3 T4 LO CLO ACR; env_clear).
    assert (TCy : thread_clear (al_thread AL) [(q - 32, q); (pcb, pcb + 4)]) by (clear - PCB T1 T2 T3 T4 T5 LO CLO ACR; env_clear).
    assert (BMy : forall c' k', 1 <= c' <= 31 -> Forall (cls_miss_body AL c' k') [(q - 32, q); (pcb, pcb + 4)]).
    { intros c' k' Hc'. pose proof (region_range AL c' Hc') as [R1' R2'].
      pose proof (sh_le 0 (region AL c') ltac:(lia)) as L1. change (sh 0) with 2147450880 in L1.
      pose proof (sh_le (region AL c' + K_REGION) (2^47) ltac:(lia)) as L2. change (sh (2^47)) with 17594333495296 in L2.
      unfold cls_miss_body, ri_addr, RIB. clear - PCB T3 T4 LP03 LO CLO LOH ACR SP1 SP2 R1' R2' L1 L2 Hc'.
      repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; (split; [lia| left; lia]). }
    unfold t_none. lz_ret. unfold refill_post. cbv zeta. fold k.
    finish.
    - reflexivity.
    - eapply munch_weaken; [| exact MU]. destruct WF as (_ & _ & _ & NF4 & _).
      unfold sub_fp, prim_W, ri_addr, RIB, pcl_addr, fa_base, region; cbn [outside]. clear - NF4 LO Hc. intros; lia.
    - eapply poison_env_frame; [exact PEG| exact MUy| exact WMy| exact AIy].
    - eapply thread_env_frame; [exact TEG| exact MUy| exact WMy| exact TCy].
    - eapply shvis_wmono; [exact SVG| exact WMy].
    -
      unfold refill_prim. fold k.
      split; [cbn [pr_cls]; rewrite set_nth_length; exact LEN|].
      split; [eapply prim_env_frame; [exact PENVG| exact MUy| exact WMy| exact AIy]|].
      split.
      { intros c' Hc'. cbn [pr_inited]. destruct (Z.eq_dec c' c) as [->|NE].
        - rewrite get_cls_set_same by (try exact LEN; lia).
          destruct (cls_body_frame AL AO c (refill k c) Hc WFG _ mG mF (conj RIG (conj FAG (conj TLG FCHG))) MUy WMy (BMy c _ Hc)) as (RI' & FA' & TL' & FCH').
          split; [exact WFG|]. split; [exact RI'|]. split; [| split; [exact FA'| split; [exact TL'| exact FCH']]].
          split; [unfold pcl_addr; rewrite <- Hpcb; exact PCG|].
          destruct PAG as (cs & CA & CL & CX). exists cs. split; [| split; [exact CL| exact CX]].
          eapply u32arr_transport; [exact CA| exact MUy| exact WMy|]. rewrite CL. unfold pcl_addr. rewrite <- Hpcb.
          cbn [disjoint_from]. clear - PCB T4 LO CLO ACR. lia.
        - assert (EO : get_cls (mkPRIM (set_nth (Z.to_nat c) (refill k c) (pr_cls P)) true (pr_calloc P) (pr_cmapped P + (p_mu (refill k c) - p_mu k))) c' = get_cls P c').
          { unfold get_cls. cbn [pr_cls]. apply nth_set_nth_other. lia. }
          rewrite EO. pose proof (CLSo c' Hc' NE) as CRo. pose proof CRo as (WFo & _).
          destruct WF as (Lnf & _ & _ & _ & MFAk & _ & AUk & MUFk & _). destruct WFG as (_ & _ & _ & _ & MFAr & _ & AUr & MUFr & _).
          pose proof (cls_rep_frame AL AO c' (get_cls P c') Hc' WFo true _ m1 mG CRo MUx WMx
                        (gfa_W_miss lo (q - 32) c c' k (refill k c) (get_cls P c') AO Hc Hc' NE LOH CLO ltac:(clear - LO; lia) ltac:(lia) MFAk ltac:(lia) MFAr ltac:(lia))) as CRg.
          apply (cls_rep_frame AL AO c' (get_cls P c') Hc' WFo true _ mG mF CRg MUy WMy).
          pose proof (BMy c' (get_cls P c') Hc') as B. apply Forall_cons_iff in B as [B1 B2]. apply Forall_cons_iff in B2 as [B2 _].
          repeat (apply Forall_cons || apply Forall_nil); (split; [cbn [fst snd]; unfold pcl_addr; clear - PCB T4 LO CLO ACR NE Hc Hc' Hpcb; lia| assumption]). }
      destruct SRG as [STCG (tsg & TSG)].
      split.
      { eapply rw_cells_transport; [exact STCG| exact MUy| exact WMy|]. cbn [disjoint_from cells_size csize Nat.add]. clear - PCB T4 LO CLO ACR. lia. }
      exists tsg. eapply rw_cells_transport; [exact TSG| exact MUy| exact WMy|]. cbn [disjoint_from cells_size csize Nat.add]. clear - PCB T4 LO CLO ACR. lia.
    - unfold prim_ok, refill_prim. cbn [pr_inited]. intros X. discriminate.
  Qed.

  #[using="Type"] Theorem refill_spec : refill_stmt AL E.
  Proof.
    unfold refill_stmt.
    intros ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m H q lo c P
           AO MI MC SV PE TE ST LOH CLO LO QH Q16 Hc RP POK C0 RB CA0 CM0 CMB.
    unfold refill_entry, REFILL_STACK, GFA_STACK, POP_STACK, MF_STACK in *.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & _).
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
    layout_apart_fact AO 0%nat 3%nat LP03.
    hide T1. hide T5. hide T6. hide T7. hide SPM.
    pose proof RP as (LEN & PENV & CLS & STAT & (ts & TS)).
    set (k := get_cls P c) in *.
    pose proof (CLS c Hc) as CR. fold k in CR.
    destruct CR as (WF & RIc & (PC1 & PAX) & FAc & TLc & FCHc).
    unfold pcl_addr in PC1 |- *.

    pose proof (munch_refl [(q - 32, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 32%nat ST.
    lz_go.
    do 4 zstep.
    do 2 zstep.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    assert (SHS : sh (al_space AL + K_SPACE + 4096) <= 17594333495296) by (unfold sh, SHADOW_OFF; clear - SP5; Z.div_mod_to_equations; lia).
    assert (RPA : RPRIM AL P mA).
    { apply (RPRIM_frame AL AO P _ m mA RP MU WM). unfold prim_clear.
      repeat (apply Forall_cons || apply Forall_nil). left. unfold prim_out. cbn [fst snd]. clear - LO CLO ACR T3 T4 SP2 SHS. repeat split; lia. }
    assert (SVA : shvis H mA) by (eapply shvis_wmono; [exact SV| exact WM]).
    assert (PEA : poison_env E mA) by (eapply poison_env_frame; [exact PE| exact MU| exact WM|]; clear - LO CLO ACR; env_clear).
    assert (TEA : thread_env (al_thread AL) mA).
    { eapply thread_env_frame; [exact TE| exact MU| exact WM|]. unhide T1. unhide T5. clear - LO CLO ACR T1 T2 T3 T4 T5. env_clear. }
    destruct (pr_inited P) eqn:INI.
    {
      pose proof (max_count_range c Hc) as (MR & _).
      rewrite (sx32_lit (max_count c)) by lia.
      zstep. if_false_z.
      assert (EP : mkPRIM (pr_cls P) true (pr_calloc P) (pr_cmapped P) = P) by (destruct P; cbn in INI |- *; rewrite INI; reflexivity).
      eapply (refill_tail ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m H q lo c P mA _ _ _ _ _ _ _ _ _ _ _ _ _ _ AO LOH CLO LO QH Q16 Hc C0 RB CA0 CM0 CMB).
      - refine (munch_weaken _ _ _ _ _ MU). clear. sub_fp_solve.
      - exact WM.
      - assumption.
      - exact SVA.
      - exact PEA.
      - exact TEA.
      - exact ST.
      - exact FR.
      - rewrite EP. exact RPA. }
    {
      change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
      zstep. if_true_z.
      pose proof RPA as (LENA & PENVA & CLSA & STATA & (tsA & TSA)). rewrite INI in CLSA.
      assert (FAM0 : forall c', 1 <= c' <= 31 -> pcl_rep AL mA false c' (get_cls P c')) by (intros c' Hc'; exact (proj1 (proj2 (proj2 (CLSA c' Hc'))))).
      assert (THR_OK : 0 < THR /\ THR + 4096 <= 2^47) by (clear - T3 T4 ACR; lia).
      clear PC1.
      apply (munch_extend _ [(CACHE, CACHE + 2592)]) in MU. cbn [List.app] in MU.
      pose proof (munch_refl [(THR + 292, THR + 2704)] mA) as MUi. pose proof (wmono_refl asegs mA) as WMi.
      call (ic_r_all ra (wz (q - 32)) gp (wz A0_TP) _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ F_ fc THR THR_OK AL eq_refl mA P _ _ _ _ _ _ _ _ _ _ _ FAM0); [assumption|].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mI end.
      match goal with FX : forall c0, 1 <= c0 <= 31 -> pcl_rep AL mI true c0 (get_cls P c0) |- _ => rename FX into FAM1 end.
      destruct (FAM1 c Hc) as (PC1 & _). unfold pcl_addr in PC1. fold k in PC1.
      zstep.
      pose proof (max_count_range c Hc) as (MR & _).
      rewrite (sx32_lit (max_count c)) by lia.
      zstep.
      clear PC1.
      assert (AIi : above_img [(THR + 292, THR + 2704)]) by (clear - T3 T4; env_clear).
      eapply (refill_tail ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m H q lo c P mI _ _ _ _ _ _ _ _ _ _ _ _ _ _ AO LOH CLO LO QH Q16 Hc C0 RB CA0 CM0 CMB).
      - exact MU.
      - exact WM.
      - assumption.
      - eapply shvis_wmono; [exact SVA| exact WMi].
      - eapply poison_env_frame; [exact PEA| exact MUi| exact WMi| exact AIi].
      - eapply thread_env_frame; [exact TEA| exact MUi| exact WMi|]. unhide T1. unhide T5. clear - T1 T2 T3 T4 T5. env_clear.
      - exact ST.
      - exact FR.
      -
        split; [exact LENA|].
        split; [eapply prim_env_frame; [exact PENVA| exact MUi| exact WMi| exact AIi]|].
        split.
        { intros c' Hc'. cbn [pr_inited]. change (get_cls (mkPRIM (pr_cls P) true (pr_calloc P) (pr_cmapped P)) c') with (get_cls P c').
          destruct (CLSA c' Hc') as (WFc' & RIc' & _ & FAc' & TLc' & FCHc').
          assert (BM : Forall (cls_miss_body AL c' (get_cls P c')) [(THR + 292, THR + 2704)]).
          { pose proof (region_range AL c' Hc') as [R1' R2'].
            pose proof (sh_le 0 (region AL c') ltac:(lia)) as L1. change (sh 0) with 2147450880 in L1.
            pose proof (sh_le (region AL c' + K_REGION) (2^47) ltac:(lia)) as L2. change (sh (2^47)) with 17594333495296 in L2.
            unfold cls_miss_body, ri_addr, RIB. clear - T3 T4 LP03 SP1 SP2 R1' R2' L1 L2 Hc'.
            repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; (split; [lia| left; lia]). }
          destruct (cls_body_frame AL AO c' (get_cls P c') Hc' WFc' _ mA mI (conj RIc' (conj FAc' (conj TLc' FCHc'))) MUi WMi BM) as (RI' & FA' & TL' & FCH').
          split; [exact WFc'|]. split; [exact RI'|]. split; [exact (FAM1 c' Hc')|]. split; [exact FA'|]. split; [exact TL'| exact FCH']. }
        split; [cbn [pr_calloc pr_cmapped]; exact STATA|]. exists tsA. exact TSA. }
  Qed.
End RFL.
