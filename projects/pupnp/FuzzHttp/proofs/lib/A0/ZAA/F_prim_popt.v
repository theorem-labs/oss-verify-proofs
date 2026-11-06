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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ PEnv F_poison F_mm_D F_prim_L0 APrimSpec APrimLem AFrame F_prim_efa APrimPop F_prim_pop F_prim_popf ATacFix APrimPopR.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Tactic Notation "callAx" uconstr(SPEC) "dropping" ne_hyp_list(HS) :=
  lz_here;
  lazymatch goal with
  | |- ITreeLZ.implL ?segs _ _ _ _ _ (MS _ _ _ _ _ ?m _) =>
      let C := find_mclean m in
      eapply implA_ebind; [ eapply implA_mclean; [ exact C | eapply SPEC ] | clear C; clear HS; post_callA segs m ]
  end.

Definition BUD2P (c r : Z) (k : pclass) : Prop :=
  4 * (p_nf k + (p_mu k + r * class_size c + K_MAP - p_au k) / class_size c) + K_MAP <= K_FA_SIZE.

Section POPE.
  Context {HC : HasCeiling}.
  Variables (ra gp : word) (F_ : bvmap 5 word) (fc : bv 32) (q c : Z).
  Notation SZ := (class_size c).
  #[using="HC"] Lemma pop_end : forall (ria nf mfa au mu cnt nal nfr : Z) (m : mem) (x1 t0 t1 t2 s1v a0 a1 a2 a4 a5 a6 a7 s2v s4v s6v t3 t4 t5 t6 : word)
        (s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 : word) (j8 j64 j88 j96 j104 j112 : word) (jpad : list byte),
      1 <= c <= 31 -> 0 <= cnt -> 0 <= nf -> nf + cnt < 2^40 -> 0 <= au -> au + cnt * SZ <= mu -> mu <= FA_OFF ->
      0x10007fff8000 <= ria -> ria + 128 <= q - 64 -> q <= 2^47 ->
      rw_cells asegs m ria [C8 (wz KWL); C8 j8; C8 (wz nf); C8 (wz mfa); C8 (wz au); C8 (wz 0); C8 (wz mu); C8 (wz 0);
                            C4 j64; C1 (Z_to_bv 8 0); CB 3 jpad; C8 (wz nal); C8 (wz nfr); C8 j88; C8 j96; C8 j104; C8 j112; CB 8 (repeat (Z_to_bv 8 0) 8)] ->
      rw_cells asegs m (q - 64) [C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 ra] ->
      mem_inv asegs m ->
      evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
          ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0' t1' t2' s0o s1o (wz 1) a1' a2' a3' a4' a5' a6' a7' s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F_ (ret_pc ra) fc None m' (seg_rom asegs)
          /\ munch [(ria + 16, ria + 40); (ria + 68, ria + 69)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
          /\ rw_cells asegs m' ria [C8 (wz KWL); C8 j8; C8 (wz (nf + cnt)); C8 (wz mfa); C8 (wz (au + cnt * SZ)); C8 (wz 0); C8 (wz mu); C8 (wz 0);
                            C4 j64; C1 (Z_to_bv 8 0); CB 3 jpad; C8 (wz nal); C8 (wz nfr); C8 j88; C8 j96; C8 j104; C8 j112; CB 8 (repeat (Z_to_bv 8 0) 8)]
          /\ rw_cells asegs m' (q - 64) [C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 ra])
        (MS (mkR x1 (wz (q - 64)) gp (wz A0_TP) t0 t1 t2 (wz ria) s1v a0 a1 a2 (wz au) a4 a5 a6 a7
                 s2v (wz cnt) s4v (wz SZ) s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F_ (wz 0x38a2c) fc None m (seg_rom asegs)).
  Proof.
    intros until jpad. intros Hc' C0 NF0 NFB AU0' AUB MUB RL RH QH' RIC FR MI.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (class_size_pos c Hc') as CS.
    assert (CSZ : 0 <= cnt * SZ) by (apply Z.mul_nonneg_nonneg; lia).
    pose proof (munch_refl [(ria + 16, ria + 40); (ria + 68, ria + 69)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. zstep.
    do 6 zstep.
    if_cases KA; zify_cond KA. { exfalso. lia. } clear KA.
    zstep. zstep. zstep. if_cases KB; zify_cond KB. { exfalso. lia. } clear KB.
    zstep. lit_store_fix.
    do 2 zstep. do 8 zstep. zstep.
    replace (q - 64 + 64) with q by lia. zstep.
    apply evt_done.
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; eassumption.
  Qed.
End POPE.

Section POPT.
  Context {HC : HasCeiling}.
  Variables (AL : alayout) (E : penv).
  Hypothesis AO : alayout_ok AL.
  Notation THR := (at_thr (al_thread AL)).
  Notation STAT := (at_thr (al_thread AL) + CSTATS_OFF).
  Variables (ra gp : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q lo c r : Z) (k : pclass) (inited : bool) (m1 : mem) (H1 : word -> bool).
  Variables (mu1 cnt mfa2 : Z).
  Notation RI := (ri_addr AL c).
  Notation FA := (fa_base AL c).
  Notation SZ := (class_size c).
  Notation REG := (al_space AL + c * 4294967296).
  Notation tot := (p_nf k + cnt).

  Definition k1 : pclass := mkPCL (p_nf k) (p_mfa k) (p_au k) mu1 (p_nalloc k) (p_nfreed k) (p_fa k) (p_cnt k) (p_chunks k).

  Definition popT_W : list (Z * Z) :=
    [(lo, q - 64); (RI + 16, RI + 40); (RI + 68, RI + 69); (FA + 4 * p_nf k, FA + 4 * tot);
     (FA + p_mfa k, FA + mfa2); (sh (FA + p_mfa k), sh (FA + p_mfa k) + (mfa2 - p_mfa k) / 8);
     (swlo (FA + p_mfa k), swhi (FA + p_mfa k) (mfa2 - p_mfa k)); (THR + TSTATS_OFF, THR + TSTATS_OFF + 368)].

  Definition popT_post (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (calloc cm1 : Z) : unit -> (word -> bool) -> machine_state -> Prop :=
    fun _ H' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ H' = H_efa AL c k1 tot H1
      /\ munch popT_W m1 m' /\ wmono asegs m1 m' /\ mem_inv asegs m'
      /\ stk asegs m' lo q /\ poison_env E m' /\ thread_env (al_thread AL) m' /\ prim_env AL m' /\ shvis H' m'
      /\ cls_open AL m' inited c (populate k c r) /\ stats_rep AL m' calloc cm1.

  #[using="AO"] Lemma pop_tail : forall (x1 t0 t1 t2 s1v s3v s6v a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 : word)
      (j8 j64 j88 j96 j104 j112 : word) (jpad jt : list byte) (nb nsh : nat) (calloc cm1 : Z) (ts : list byte),
    mem_inv asegs m1 -> mclean H1 m1 -> shvis H1 m1 -> poison_env E m1 -> thread_env (al_thread AL) m1 -> prim_env AL m1 ->
    stk asegs m1 lo (q - 64) -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q - 64 - 48 - 400 -> q <= 2^47 -> q mod 16 = 0 ->
    1 <= c <= 31 -> 1 <= r <= 8 -> pclass_wf c k ->
    p_mu k + r * class_size c + K_MAP <= FA_OFF ->
    4 * (p_nf k + (p_mu k + r * class_size c + K_MAP - p_au k) / class_size c) + K_MAP <= K_FA_SIZE ->
    mu1 = pop_mu k c r -> cnt = pop_new k c r -> mfa2 = efa_new k1 tot ->
    rw_cells asegs m1 RI (ri_cells KWL k1 j8 j64 j88 j96 j104 j112 jpad) ->
    pcl_rep AL m1 inited c k -> fa_rep AL m1 c k ->
    rw_cells asegs m1 (REG + p_au k) [CB nb jt] -> Z.of_nat nb = mu1 - p_au k ->
    rw_cells asegs m1 (sh (REG + p_au k)) [CB nsh (repeat (Z_to_bv 8 250) nsh)] -> 8 * Z.of_nat nsh = mu1 - p_au k ->
    (forall v, In v (p_fa k ++ p_chunks k) -> free_chunk AL m1 c v) ->
    rw_cells asegs m1 (q - 64) [C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 ra] ->
    rw_cells asegs m1 (STAT + 16) [C8 (wz calloc); C8 (wz cm1)] ->
    rw_cells asegs m1 (THR + TSTATS_OFF) [CB 368 ts] ->
    implA H1 (t_efa AL c k1 tot) (popT_post s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 calloc cm1)
      (MS (mkR x1 (wz (q - 64)) gp (wz A0_TP) t0 t1 t2 (wz RI) s1v (wz INSTANCE) a1 a2 (wz (p_au k)) a4 a5 a6 a7
               (wz REG) s3v (wz mu1) (wz SZ) s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x389c4) fc None m1 (seg_rom asegs)).
  Proof.
    intros until ts. intros MI MC SV PE TE PRE ST LOH CLO LO QH AL16 Hc Hr WF BUD1 BUD2 Hmu1 Hcnt Hmfa2 RIC PCL FAR TL Hnb TSH Hnsh FCH FR STC TS.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    layout_facts AO 0%nat SPF. layout_facts AO 3%nat THF.
    destruct SPF as (SP1 & SP2 & SP3 & _ & SP5 & _ & _). destruct THF as (TH1 & TH2 & TH3 & _ & TH5 & _ & _).
    pose proof AO as AO'. destruct AO' as (_ & _ & SPAL & TLO & _ & _).
    pose proof (region_range AL c Hc) as RR.
    assert (Hreg : region AL c = REG) by reflexivity. assert (Hfa : FA = region AL c + FA_OFF) by reflexivity.
    layout_apart_fact AO 0%nat 3%nat AP03.

    pose proof (SZ_facts c r k Hc Hr) as (CS & CS16 & RS & RS8).
    pose proof (pop_mu_facts c r k Hc Hr WF BUD1) as (M1 & M2 & M3 & M4 & M5 & _). rewrite <- ?Hmu1 in M1, M2, M3, M4, M5.
    pose proof (pop_new_facts c r k Hc Hr WF BUD1) as (N0 & N1 & N2 & N3). rewrite <- ?Hmu1, <- ?Hcnt in N0, N1, N2, N3.
    pose proof WF as WF0. unfold pclass_wf in WF0.
    destruct WF0 as (Lnf & Lcnt & CNT & NF4 & MFA & MFAM & AU & MUF & MUM & AUS & GAP & ND & FB & NA & NFR).
    pose proof (au_mod16 c r k Hc Hr WF) as AU16.
    assert (TB : 4 * tot + K_MAP <= K_FA_SIZE) by lia.
    assert (B2 : BUD2P c r k) by exact BUD2.
    pose proof (efa_new_facts c r k k1 tot ltac:(cbn; lia) ltac:(cbn; exact MFAM) ltac:(lia) TB) as (F1 & F2 & F3 & F4).
    cbn [k1 p_mfa] in F1, F2, F3, F4. rewrite <- Hmfa2 in F1, F2, F3, F4.
    assert (CSZ : 0 <= cnt * SZ /\ cnt * SZ = SZ * cnt) by (split; [apply Z.mul_nonneg_nonneg; lia| apply Z.mul_comm]).
    demod SP3. demod SPAL. demod AL16. demod TH3. demod CS16. demod AU16. demod MUM. demod MFAM. demod M4. demod F3. clear AUS.
    destruct FAR as (ws & FAA & LEN & FX).
    unfold ri_cells in RIC. cbn [k1 p_nf p_mfa p_au p_mu p_nalloc p_nfreed p_fa p_cnt p_chunks] in RIC. unfold ri_addr, RIB in *. unfold prim_env in PRE.
    replace (at_thr (al_thread AL) + CSTATS_OFF + 16) with (at_thr (al_thread AL) + 2784) in STC by lia.
    assert (SHF : sh (FA + p_mfa k + (mfa2 - p_mfa k)) = sh (FA + p_mfa k) + (mfa2 - p_mfa k) / 8) by (unfold sh; Z.div_mod_to_equations; lia).
    pose proof (sw_range (FA + p_mfa k) (mfa2 - p_mfa k) ltac:(lia) ltac:(lia) ltac:(lia)) as SWR.
    pose proof (sw_bounds (FA + p_mfa k) (mfa2 - p_mfa k) ltac:(lia) ltac:(lia)) as (SW1 & SW2 & _ & _ & SW5 & _).
    set (W := popT_W). unfold popT_W in W. unfold ri_addr, RIB in W.
    set (m8 := (mfa2 - p_mfa k) / 8) in *. assert (Hm8 : 8 * m8 = mfa2 - p_mfa k) by (subst m8; Z.div_mod_to_equations; lia). clearbody m8.
    assert (AIW : above_img W).
    { subst W. env_clear. }
    assert (TCW : thread_clear (al_thread AL) W).
    { subst W. pose proof TLO as TL'. unfold thread_layout_ok in TL'. layout_apart_fact AO 0%nat 2%nat AP02.
      clear RIC PRE TS TL TSH STC ST MI MC SV PE TE PCL FAA FX FCH FR.
      destruct TL' as (CX1 & CX2 & _ & _ & CXT & _). clear AIW. env_clear. }
    pose proof (munch_refl W m1) as MU. pose proof (wmono_refl asegs m1) as WM. subst W.
    hide TL. hide TSH.
    rewrite <- (ebind_ret_r (t_efa _ _ _ _)).
    lz_go.
    zstep.
    zstep.
    zstep.
    rewrite m_divu_lit by lia. replace ((mu1 - p_au k) / SZ) with cnt by (rewrite Hcnt; unfold pop_new; rewrite <- Hmu1; reflexivity).
    zstep.
    do 3 zstep.
    zstep.

    assert (ERI : ri_addr AL c = al_space AL + K_SPACE + 128 * c) by reflexivity.
    assert (EK1 : p_mfa k1 = p_mfa k) by reflexivity.
    assert (ESH : sh (FA + p_mfa k1) = sh (FA + p_mfa k)) by reflexivity.
    assert (ESL : swlo (FA + p_mfa k1) = swlo (FA + p_mfa k)) by reflexivity.
    assert (ESW : swhi (FA + p_mfa k1) (efa_new k1 tot - p_mfa k1) = swhi (FA + p_mfa k) (mfa2 - p_mfa k)) by (rewrite Hmfa2; reflexivity).
    idtac "MARK1".
    clear FB ND GAP NA NFR CNT Lcnt RS8 N3 M5 MUF BUD2.
    callAx (efa_spec AL E AO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (q - 64) lo c tot k1 KWL) dropping RIC TS FAA;
      [ assumption | assumption
      | eapply shvis_wmono; [exact SV| exact WM]
      | eapply poison_env_frame; [exact PE| exact MU| exact WM| exact AIW]
      | eapply thread_env_frame; [exact TE| exact MU| exact WM| exact TCW]
      | exact PRE
      | exact ST | lia | lia | lia | lia | lia | exact Hc | lia | lia
      | cbn; exact Lnf | cbn; lia | cbn; lia | cbn; lia
      | unfold ri_cells; cbn [k1 p_nf p_mfa p_au p_mu p_nalloc p_nfreed p_fa p_cnt p_chunks]; exact RIC
      | exists ws; split; [exact FAA| split; [exact LEN| exact FX]]
      | exists ts; exact TS |].
    idtac "MARK2".
    cbv beta. try clear SWR0; try clear SWB0; try clear SWB.
    match goal with P : stk asegs _ lo _, E0 : poison_env E _, T0 : thread_env _ _, Pp : prim_env AL _, S0 : shvis _ _, R0 : rw_cells asegs _ _ (ri_cells _ _ _ _ _ _ _ _ _), F0 : fa_rep AL _ c _, X0 : (exists ts0, _) |- _ =>
      rename P into ST2; rename E0 into PE2; rename T0 into TE2; rename Pp into PRE2; rename S0 into SV2; rename R0 into RIC2; rename F0 into FAR2; rename X0 into TS2 end.
    unfold ri_cells, ensure_fa in RIC2. cbn [k1 p_nf p_mfa p_au p_mu p_nalloc p_nfreed p_fa p_cnt p_chunks] in RIC2. unfold ri_addr, RIB in RIC2. rewrite <- Hmfa2 in RIC2.
    destruct FAR2 as (ws2 & FAA2 & LEN2 & FX2). cbn [ensure_fa k1 p_mfa p_fa] in LEN2, FX2. rewrite <- Hmfa2 in LEN2.
    destruct TS2 as (ts2 & TS2). unfold prim_env in PRE2.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => pose proof (wmono_refl asegs mX) as WMa end.
    idtac "MARK3".
    zstep. if_cases K0; zify_cond K0. { exfalso. lia. } clear K0.
    zstep.
    rewrite <- Hmu1 in N1, N2.
    zstep. if_cases KL; zify_cond KL.
    {   exfalso. lia. }
    do 7 zstep.
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      call (pop_fill AL AO gp (wz A0_TP) F_ fc q c (p_au k) tot cnt ws2 mx (Z.to_nat cnt) 0 mx) end.
    1: f_equal; lia.
    1: destruct (Z.eq_dec cnt 0) as [E0|NE0]; [rewrite E0 in N2; lia| lia].
    1-3: lia.
    1-4: lia.
    1: unfold fa_base, region; lia.
    1: change (Z.to_nat 0) with 0%nat; rewrite LF_0; exact FAA2.
    1: apply munch_refl.
    1: apply wmono_refl.
    1: exact MI0.
    idtac "MARK4".
    rename POST into FAA3.
    pose proof (LF_length c (p_au k) tot ws2 (Z.to_nat cnt) ltac:(lia) ltac:(lia)) as LFL.
    remember (LF c (p_au k) tot ws2 (Z.to_nat cnt)) as ws3 eqn:Hws3.
    call (pop_end ra gp F_ fc q c (al_space AL + 137438953472 + 128 * c) (p_nf k) mfa2 (p_au k) mu1 cnt (p_nalloc k) (p_nfreed k)).
    1-10: lia.
    1: exact RIC2.
    1: exact FR.
    1: exact MI.
    idtac "MARK5".
    match goal with H : stk asegs _ lo _ |- _ => release_frame POST H q end.
    lz_ret. unfold popT_post. finish.
    - reflexivity.
    - assert (E8 : (mfa2 - p_mfa k) / 8 = m8) by (rewrite <- Hm8, Z.mul_comm, Z.div_mul by lia; reflexivity).
      unfold popT_W, ri_addr, RIB. rewrite E8. exact MU.
    - eapply poison_env_frame; [exact PE| exact MU| exact WM| exact AIW].
    - eapply thread_env_frame; [exact TE| exact MU| exact WM| exact TCW].
    - eapply shvis_wmono; [exact SV2| exact WMa].
    - assert (SHB : sh (REG + mu1) <= 17594333495296).
      { pose proof (sh_le (REG + mu1) (2^47) ltac:(lia)) as X. change (sh (2^47)) with 17594333495296 in X. exact X. }
      assert (SHR0 : 2147450880 <= sh REG) by (pose proof (sh_le 0 REG ltac:(unfold region; lia)) as X; exact X).
      assert (SHG : sh (REG + mu1) + 4096 <= sh (FA + p_mfa k)).
      { pose proof (sh_le (REG + mu1 + 8 * 4096) (FA + p_mfa k) ltac:(unfold fa_base; lia)) as X.
        rewrite sh_off8 in X; [exact X|]. unfold region. rewrite SP0, M0. clear. Z.div_mod_to_equations. lia. }
      assert (SWL : sh (FA + p_mfa k) - 4095 <= swlo (FA + p_mfa k)) by (unfold swlo; clear; Z.div_mod_to_equations; lia).
      unhide TL. unhide TSH. unfold k1 in Hmfa2.
      eapply (cls_open_populate AL AO c r k Hc Hr WF BUD1 B2 m1 _ inited _ ws2 nb nsh jt j8 j64 j88 j96 j104 j112 jpad);
        [ exact MU | exact WM | | | exact PCL | | | exact FX2 | exact TL | rewrite <- Hmu1; exact Hnb | exact TSH | rewrite <- Hmu1; exact Hnsh | exact FCH ].
      + unfold pop_clear. rewrite <- Hmu1. unfold pcl_addr.
        pose proof TLO as TL'. unfold thread_layout_ok in TL'. destruct TL' as (CX1 & CX2 & _ & _ & CXT & _).
        repeat match goal with
          | H : rw_cells _ _ _ _ |- _ => clear H | H : u32arr _ _ _ _ |- _ => clear H | H : stk _ _ _ _ |- _ => clear H
          | H : munch _ _ _ |- _ => clear H | H : wmono _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H
          | H : shvis _ _ |- _ => clear H | H : poison_env _ _ |- _ => clear H | H : thread_env _ _ |- _ => clear H
          | H : pcl_rep _ _ _ _ _ |- _ => clear H | H : above_img _ |- _ => clear H | H : thread_clear _ _ |- _ => clear H end.
        clear FCH FX2 FX.
        unfold region in *. unfold fa_base, region in *.
        repeat first [apply Forall_nil | apply Forall_cons]; cbn [fst snd]; repeat split; lia.
      + unfold populate, ensure_fa, ri_cells, ri_addr, RIB. cbn [p_nf p_mfa p_au p_mu p_nalloc p_nfreed p_fa p_cnt p_chunks].
        rewrite <- Hmu1, <- Hcnt, <- Hmfa2. exact PC.
      + rewrite <- Hcnt, <- Hws3. exact FAA3.
      + unfold populate, ensure_fa. cbn [p_mfa]. rewrite <- Hmu1, <- Hcnt, <- Hmfa2. exact LEN2.
    - split; [replace (at_thr (al_thread AL) + CSTATS_OFF + 16) with (at_thr (al_thread AL) + 2784) by lia; exact STC| exists ts2; exact TS2].
  Qed.
End POPT.
