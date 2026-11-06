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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimDealloc F_prim_efa F_prim_rta F_prim_rta2 ATacFix.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition drain_entry : Z := 0x36030.
Definition uod_entry : Z := 0x6ba24.
Definition DRAIN_STACK : Z := 64 + RTA_STACK.

Lemma uod_null : forall (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F_ : bvmap 5 word) (fc : bv 32) (q lo : Z) (m0 : mem),
  stk asegs m0 lo q -> 0 <= lo -> lo <= q - 48 -> q <= 2^47 -> mem_inv asegs m0 ->
  evt asegs (fun ms' => exists m', ms' =
      MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(q - 48, q)] m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m' /\ stk asegs m' lo q)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz uod_entry) fc None m0 (seg_rom asegs)).
Proof.
  intros until m0. intros ST LO0 LO QH MI. unfold uod_entry.
  pose proof (munch_refl [(q - 48, q)] m0) as MU. pose proof (wmono_refl asegs m0) as WM.
  assert (E : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  rewrite <- E in ST. carve_frame 48%nat ST. rewrite !E in *.
  do 5 sstep.
  zstep. lit_branch.
  do 4 zstep.
  zstep. replace (q + -48 + 48) with q by lia. zstep.
  release_frame FR ST q.
  apply evt_done. eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end; eassumption.
Qed.

Section DRAIN.
  Context {HC : HasCeiling}.
  Variables (AL : alayout) (E : penv).
  Notation THR := (at_thr (al_thread AL)).
  Notation CACHE := (at_thr (al_thread AL) + CACHE_OFF).

  Definition drain_post (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (q lo c : Z) (k : pclass) (H : word -> bool) (m : mem) : unit -> (word -> bool) -> machine_state -> Prop :=
    fun _ H' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      let k' := drain_cls k c in
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ H' = H_efa AL c k (p_nf k + max_count c / 2) H
      /\ munch (drain_W AL lo q c k k') m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo q /\ poison_env E m' /\ thread_env (al_thread AL) m' /\ prim_env AL m' /\ shvis H' m'
      /\ ri_rep AL m' c k' /\ pcl_rep AL m' true c k' /\ fa_rep AL m' c k'
      /\ (exists ts, rw_cells asegs m' (THR + TSTATS_OFF) [CB 368 ts]).

  #[using="Type"] Theorem drain_spec :
    forall (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32)
           (m : mem) (H : word -> bool) (q lo c : Z) (k : pclass),
    alayout_ok AL ->
    mem_inv asegs m -> mclean H m -> shvis H m -> poison_env E m -> thread_env (al_thread AL) m -> prim_env AL m ->
    stk asegs m lo q -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q - DRAIN_STACK -> q <= 2^47 -> q mod 16 = 0 ->
    1 <= c <= 31 -> pclass_wf c k -> max_count c / 2 <= p_cnt k -> drain_budget c k ->
    ri_rep AL m c k -> pcl_rep AL m true c k -> fa_rep AL m c k ->
    (exists ts, rw_cells asegs m (THR + TSTATS_OFF) [CB 368 ts]) ->
    implA H (t_efa AL c k (p_nf k + max_count c / 2))
          (drain_post ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc q lo c k H m)
          (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz CACHE) (wz (pcl_addr AL c)) (wz INSTANCE) (wz c) a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F_ (wz drain_entry) fc None m (seg_rom asegs)).
  Proof.
    intros ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m H q lo c k
           AO MI MC SV PE TE PRE ST LOH CLO LO QH Q16 Hc WF HCNT DB RIR (PC1 & cs & CHA & CL & CX) FAR TSX.
    unfold DRAIN_STACK, RTA_STACK, MF_STACK in LO. unfold drain_entry.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    layout_facts AO 0%nat SPF. layout_facts AO 3%nat THF.
    destruct SPF as (SP1 & SP2 & _ & _ & SP5 & _ & _). destruct THF as (TH1 & TH2 & _ & _ & TH5 & _ & _).
    pose proof AO as AO'. destruct AO' as (_ & _ & _ & TLO & _ & _).
    layout_apart_fact AO 0%nat 3%nat AP03.
    pose proof (max_count_range c Hc) as (MR & MR2).
    pose proof WF as WF0. unfold pclass_wf in WF0.
    destruct WF0 as (Lnf & Lcnt & CNT & NF4 & MFA & MFAM & AU & MUF & _ & _ & _ & ND & FB & NA & NFR).
    set (h := max_count c / 2) in *.
    assert (Hh : 1 <= h <= 8 /\ 2 * h = max_count c) by (unfold h; clear - MR MR2; Z.div_mod_to_equations; lia).
    clearbody h. clear MR2.
    unfold pcl_addr in PC1, CHA |- *.
    assert (PCB : THR + 288 <= THR + 208 + 80 * c /\ THR + 208 + 80 * c + 80 <= THR + 2768) by (clear - Hc; lia).
    remember (THR + 208 + 80 * c) as pcb eqn:Hpcb in *.
    pose proof (munch_refl [(q - 64, q); (pcb, pcb + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    rewrite <- EQ in ST. carve_frame 64%nat ST. rewrite !EQ in *. clear EQ.
    lz_go.
    do 4 sstep.
    zstep.
    zstep.
    sstep.
    do 3 sstep.
    rewrite (sx32_lit (p_cnt k)) by (clear - CNT MR; lia).
    replace (zx32 (Z_to_bv 64 (max_count c))) with (Z_to_bv 64 (max_count c)) by (unfold zx32; rewrite unsigned_lit by (clear - MR; lia); rewrite Z.mod_small by (clear - MR; lia); reflexivity).
    zstep.
    replace (Z.shiftr (max_count c) 1) with h by (rewrite Z.shiftr_div_pow2 by lia; change (2^1) with 2; clear - Hh; Z.div_mod_to_equations; lia).
    zstep. zstep.
    rewrite (Z.mod_small (p_cnt k) 4294967296) by (clear - CNT MR; lia).
    zstep. if_cases KB; zify_cond KB. { exfalso. clear - KB HCNT Hh CNT. lia. } clear KB.
    zstep.
    zstep.
    zstep.
    do 4 zstep.
    do 3 zstep.
    zstep.
    set (vals := skipn (Z.to_nat (p_cnt k - h)) (p_chunks k)).
    assert (LV : Z.of_nat (length vals) = h) by (unfold vals; rewrite length_skipn; clear - Lcnt HCNT Hh; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mC end.

    assert (AIW : above_img [(q - 64, q); (pcb, pcb + 4)]) by (clear - PCB TH1 TH2 LO CLO ACR; env_clear).
    assert (TCW : thread_clear (al_thread AL) [(q - 64, q); (pcb, pcb + 4)]).
    { pose proof TLO as TL'. unfold thread_layout_ok in TL'. destruct TL' as (CX1 & CX2 & _ & _ & CXT & _).
      clear - CX1 CX2 CXT PCB TH1 TH2 LO CLO ACR. env_clear. }
    assert (SVC : shvis H mC) by (eapply shvis_wmono; [exact SV| exact WM]).
    assert (PEC : poison_env E mC) by (eapply poison_env_frame; [exact PE| exact MU| exact WM| exact AIW]).
    assert (TEC : thread_env (al_thread AL) mC) by (eapply thread_env_frame; [exact TE| exact MU| exact WM| exact TCW]).
    assert (PREC : prim_env AL mC) by (eapply prim_env_frame; [exact PRE| exact MU| exact WM| exact AIW]).
    pose proof (region_range AL c Hc) as RR. unfold region in RR.
    assert (RIRC : ri_rep AL mC c k).
    { destruct RIR as (j8 & j64 & j88 & j96 & j104 & j112 & jpad & RIC). exists j8, j64, j88, j96, j104, j112, jpad.
      eapply rw_cells_transport; [exact RIC| exact MU| exact WM|]. unfold ri_addr, RIB, ri_cells. cbn [disjoint_from cells_size csize Nat.add].
      clear - PCB AP03 Hc SP2 CLO LO. lia. }
    assert (FARC : fa_rep AL mC c k).
    { destruct FAR as (ws & FAA & LEN & FX). exists ws. split; [| split; [exact LEN| exact FX]].
      eapply u32arr_transport; [exact FAA| exact MU| exact WM|]. unfold fa_base, region. cbn [disjoint_from].
      clear - PCB AP03 RR LEN MFA SP2 CLO LO. lia. }
    assert (TSC : exists ts, rw_cells asegs mC (THR + TSTATS_OFF) [CB 368 ts]).
    { destruct TSX as (ts & TS). exists ts. eapply rw_cells_transport; [exact TS| exact MU| exact WM|]. cbn [disjoint_from cells_size csize Nat.add].
      clear - PCB TH2 CLO LO. lia. }
    clear SV PE TE PRE RIR FAR TSX.

    replace (Z_to_bv 64 (pcb + Z.shiftl (p_cnt k - h) 2 + 16)) with (Z_to_bv 64 (pcb + 16 + 4 * (p_cnt k - h)))
      by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    rewrite <- LV.
    rewrite <- (ebind_ret_r (t_efa AL c k (p_nf k + Z.of_nat (length vals)))).
    hide FR.
    callA0 (rta_spec AL E _ gp _ _ _ s0 s1 _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F_ fc mC H (q + -64) lo c k vals (pcb + 16) (p_cnt k - Z.of_nat (length vals)) (q + -56) (THR + 2768) cs AO).
    1: assumption.
    1: assumption.
    1: exact SVC.
    1: exact PEC.
    1: exact TEC.
    1: exact PREC.
    1: exact ST.
    1: exact LOH.
    1: exact CLO.
    1: unfold RTA_STACK, MF_STACK; clear - LO; lia.
    1: clear - QH; lia.
    1: clear - Q16; Z.div_mod_to_equations; lia.
    1: exact Hc.
    1: exact WF.
    1: exact RIRC.
    1: exact FARC.
    1: exact TSC.
    1: rewrite LV; clear - Hh; lia.
    1: rewrite LV; unfold drain_budget in DB; clear - DB Hh; Z.div_mod_to_equations; lia.
    1: exact CHA.
    1: rewrite LV; clear - HCNT; lia.
    1: { intros j Hj. rewrite LV.
         assert (LJ : (Z.to_nat (p_cnt k - h) + j < length (p_chunks k))%nat) by (clear - Hj LV Lcnt HCNT Hh; lia).
         unfold vals. rewrite nth_skipn.
         pose proof (nth_error_firstn (length (p_chunks k)) cs (Z.to_nat (p_cnt k - h) + j)) as NF.
         destruct (Nat.ltb_spec (Z.to_nat (p_cnt k - h) + j) (length (p_chunks k))) as [_|GE]; [| exfalso; clear - GE LJ; lia].
         rewrite CX in NF. rewrite (map_nth_error wz _ _ (nth_error_nth' (p_chunks k) 0 LJ)) in NF. symmetry. exact NF. }
    1: { apply Forall_forall. intros v Hv.
         assert (IN : In v (p_fa k ++ p_chunks k)).
         { apply in_or_app. right. rewrite <- (firstn_skipn (Z.to_nat (p_cnt k - h)) (p_chunks k)). apply in_or_app. right. exact Hv. }
         pose proof (proj1 (Forall_forall _ _) FB v IN) as (V0 & V1 & _). cbv beta in V0, V1.
         pose proof (class_size_pos c Hc) as CS. clear - V0 V1 AU MUF CS. lia. }
    1: clear - PCB; lia.
    1: rewrite CL; clear - PCB; lia.

    intros r H' ms' [PO MCx]. destruct r. unfold rta_post in PO. cbv zeta in PO.
    destruct PO as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & mR & -> & -> & MUc & WMc & MIR & STR & PER & TER & PRER & SVR & RIRR & FARR & CHAR & TSR).
    clean_ms_mem MCx.
    rewrite LV in *.
    set (k1 := return_to_allocator k vals) in *.
    assert (EK1 : p_nf k1 = p_nf k + h /\ p_mfa k1 = efa_new k (p_nf k + h) /\ p_au k1 = p_au k /\ p_mu k1 = p_mu k /\ p_nalloc k1 = p_nalloc k
                  /\ p_nfreed k1 = p_nfreed k + h /\ p_fa k1 = p_fa k ++ vals /\ p_cnt k1 = p_cnt k /\ p_chunks k1 = p_chunks k).
    { unfold k1, return_to_allocator. cbn [p_nf p_mfa p_au p_mu p_nalloc p_nfreed p_fa p_cnt p_chunks ensure_fa]. rewrite LV. repeat split; reflexivity. }
    destruct EK1 as (K_nf & K_mfa & K_au & K_mu & K_na & K_nfr & K_fa & K_cnt & K_ch).
    set (tot := p_nf k + h) in *.
    assert (TB : 4 * tot <= 536870912) by (unfold drain_budget in DB; clear - DB Hh; unfold tot; Z.div_mod_to_equations; lia).
    assert (EFN : p_mfa k <= efa_new k tot <= K_FA_SIZE /\ efa_new k tot mod K_MAP = 0 /\ 4 * tot <= efa_new k tot).
    { unfold efa_new. destruct (Z.leb_spec (4 * tot) (p_mfa k)) as [LE|GT]; [clear - LE MFA MFAM; lia|].
      pose proof (rup_ge (4 * tot) K_MAP ltac:(lia)). pose proof (rup_mod (4 * tot) K_MAP ltac:(lia)).
      pose proof (rup_le (4 * tot) K_FA_SIZE K_MAP ltac:(lia) ltac:(clear - TB; lia) ltac:(reflexivity)). clear - H0 H1 H2 GT NF4. lia. }
    set (mfa1 := efa_new k tot) in *.
    set (FAB := al_space AL + c * 4294967296 + 3758096384) in *.
    assert (FABR : al_space AL + 4294967296 <= FAB /\ FAB + 536870912 <= al_space AL + 137438953472) by (unfold FAB; clear - RR; lia).
    assert (SHL2 : 2147450880 <= sh (FAB + p_mfa k)) by (pose proof (sh_le 0 (FAB + p_mfa k) ltac:(clear - FABR SP1 MFA; lia)) as X; exact X).
    assert (SHU2 : sh (FAB + p_mfa k) + (mfa1 - p_mfa k) / 8 <= 17594333495296).
    { pose proof (sh_le (FAB + mfa1) (2^47) ltac:(clear - FABR SP5 EFN; lia)) as X. change (sh (2^47)) with 17594333495296 in X.
      revert X. unfold sh. clear. intros X. Z.div_mod_to_equations. lia. }
    pose proof (sw_range (FAB + p_mfa k) (mfa1 - p_mfa k) ltac:(clear - FABR SP1 MFA; lia) ltac:(clear - EFN; lia) ltac:(clear - FABR SP5 EFN; lia)) as SWR.
    unfold rta_W, ri_addr, RIB, fa_base, region in MUc. rewrite K_mfa in MUc. fold FAB in MUc. fold mfa1 in MUc.

    unhide FR.
    pose proof (rw_cells_transport asegs _ mC mR _ _ FR MUc WMc ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - LO CLO LOH SP2 FABR Hc TH2 SHU2 SWR EFN MFA; lia)) as FRR.
    pose proof (rw_cells_transport asegs _ mC mR _ _ PC1 MUc WMc ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - PCB LO CLO LOH SP1 SP2 FABR Hc TH1 TH2 AP03 SHL2 SHU2 SWR EFN MFA Lnf; lia)) as PC1R.
    clear FR PC1 CHA.
    lz_cont MCx.
    replace (ret_pc (Z_to_bv 64 221332)) with (Z_to_bv 64 221332) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    zstep. zstep.
    zstep.
    zstep.
    eapply evt_cut.
    { eapply (uod_null _ gp (wz A0_TP) _ _ _ s0 s1 _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F_ fc (q + -64) lo mR).
      - exact STR.
      - clear - LOH; lia.
      - clear - LO; lia.
      - clear - QH; lia.
      - exact MIR. }
    cbv beta. intros ms2 (mU & -> & MUu & WMu & MIU & STU).
    replace (ret_pc (Z_to_bv 64 221348)) with (Z_to_bv 64 221348) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    pose proof (rw_cells_transport asegs _ mR mU _ _ FRR MUu WMu ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear; lia)) as FRU.
    clear FRR.
    zstep.
    zstep. replace (q + -64 + 64) with q by lia. zstep.
    release_frame FRU STU q.

    assert (Eh : max_count c / 2 = h) by (clear - Hh; Z.div_mod_to_equations; lia).
    assert (MUS : munch [(lo, q)] mR mU).
    { eapply munch_weaken; [| exact MUu]. unfold sub_fp; cbn [outside]. intros xo (O1 & _). split; [intros R; apply O1; clear - R LO; lia| exact I]. }
    assert (AIS : above_img [(lo, q)]) by (clear - LOH; env_clear).
    assert (TCS : thread_clear (al_thread AL) [(lo, q)]).
    { pose proof TLO as TL'. unfold thread_layout_ok in TL'. destruct TL' as (CX1 & CX2 & _ & _ & CXT & _). clear - CX1 CX2 TH1 TH2 CLO LOH. env_clear. }
    lz_ret. unfold drain_post, drain_cls. cbv zeta. rewrite Eh. fold vals. fold k1.
    cbn [p_nf p_mfa p_au p_mu p_nalloc p_nfreed p_fa p_cnt p_chunks].
    apply evt_done.
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, mU. split; [reflexivity|].
    split; [reflexivity|].
    split.
    { unfold drain_W, ri_addr, RIB, fa_base, region, pcl_addr. cbn [p_mfa]. rewrite K_mfa. fold FAB. fold tot. fold mfa1. rewrite <- Hpcb.
      eapply munch_trans; [eapply munch_weaken; [| exact MU]|].
      { unfold sub_fp; cbn [outside]. intros xo (O1 & _ & _ & _ & _ & _ & O7 & _). split; [intros R; apply O1; clear - R LO; lia|]. split; [exact O7| exact I]. }
      eapply munch_trans; [eapply munch_weaken; [| exact MUc]|].
      { unfold sub_fp; cbn [outside]. intros xo (O1 & O2 & O3 & O4 & O5 & O6 & _).
        split; [intros R; apply O1; clear - R; lia|]. split; [exact O2|]. split; [exact O3|]. split; [exact O4|]. split; [exact O5|]. split; [exact O6| exact I]. }
      eapply munch_weaken; [| exact MUS]. unfold sub_fp; cbn [outside]. intros xo (O1 & _). split; [exact O1| exact I]. }
    split; [exact (wmono_trans asegs _ _ _ WM (wmono_trans asegs _ _ _ WMc WMu))|].
    split; [exact MIU|]. split; [exact STU|].
    split; [eapply poison_env_frame; [exact PER| exact MUS| exact WMu| exact AIS]|].
    split; [eapply thread_env_frame; [exact TER| exact MUS| exact WMu| exact TCS]|].
    split; [eapply prim_env_frame; [exact PRER| exact MUS| exact WMu| exact AIS]|].
    split; [eapply shvis_wmono; [exact SVR| exact WMu]|].
    split.
    { destruct RIRR as (j8 & j64 & j88 & j96 & j104 & j112 & jpad & RIC). exists j8, j64, j88, j96, j104, j112, jpad.
      unfold ri_cells in RIC |- *. cbn [p_nf p_mfa p_au p_mu p_nalloc p_nfreed].
      eapply rw_cells_transport; [exact RIC| exact MUS| exact WMu|]. unfold ri_addr, RIB. cbn [disjoint_from cells_size csize Nat.add].
      clear - Hc SP2 CLO. lia. }
    split.
    { unfold pcl_rep. cbn [p_cnt p_chunks]. unfold pcl_addr. rewrite <- Hpcb. split.
      - eapply rw_cells_transport; [exact PC1R| exact MUS| exact WMu|]. cbn [disjoint_from cells_size csize Nat.add]. clear - PCB TH2 CLO. lia.
      - exists cs. split; [| split; [exact CL|]].
        + eapply u32arr_transport; [exact CHAR| exact MUS| exact WMu|]. rewrite CL. cbn [disjoint_from]. clear - PCB TH2 CLO. lia.
        + rewrite length_firstn, Nat.min_l by (clear - Lcnt HCNT Hh; lia).
          rewrite <- firstn_map, <- CX, firstn_firstn, Nat.min_l by (clear - Lcnt HCNT Hh; lia). reflexivity. }
    split.
    { destruct FARR as (ws & FAA & LEN & FX). exists ws. split; [| split; [exact LEN| exact FX]].
      eapply u32arr_transport; [exact FAA| exact MUS| exact WMu|]. unfold fa_base, region. fold FAB. cbn [disjoint_from].
      rewrite K_mfa in LEN. fold tot in LEN. fold mfa1 in LEN. clear - LEN EFN FABR SP2 CLO. lia. }
    destruct TSR as (ts & TS). exists ts.
    eapply rw_cells_transport; [exact TS| exact MUS| exact WMu|]. cbn [disjoint_from cells_size csize Nat.add]. clear - TH2 CLO. lia.
  Qed.
End DRAIN.
