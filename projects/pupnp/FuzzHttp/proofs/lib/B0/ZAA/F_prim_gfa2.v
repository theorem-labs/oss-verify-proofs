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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimRefill F_prim_gfa F_prim_pop2 ATacFix.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition gfa_entry2 : Z := 0x38530.
Definition GFA_STACK : Z := 128 + POP_STACK.

Tactic Notation "callAx" uconstr(SPEC) "dropping" ne_hyp_list(HS) :=
  lz_here;
  lazymatch goal with
  | |- ITreeLZ.implL ?segs _ _ _ _ _ (MS _ _ _ _ _ ?m _) =>
      let C := find_mclean m in
      eapply implA_ebind; [ eapply implA_mclean; [ exact C | eapply SPEC ] | clear C; clear HS; post_callA segs m ]
  end.

Section GFA2.
  Context {HC : HasCeiling}.
  Variables (AL : alayout) (E : penv).
  Notation THR := (at_thr (al_thread AL)).
  Notation STAT := (at_thr (al_thread AL) + CSTATS_OFF).

  Definition gfa_W (lo q c : Z) (k k' : pclass) : list (Z * Z) :=
    [(lo, q); (ri_addr AL c, ri_addr AL c + 128); (fa_base AL c + 4 * p_nf k, fa_base AL c + p_mfa k');
     (region AL c + p_mu k, region AL c + p_mu k'); (fa_base AL c + p_mfa k, fa_base AL c + p_mfa k');
     (sh (region AL c + p_mu k), sh (region AL c + p_mu k')); (sh (fa_base AL c + p_mfa k), sh (fa_base AL c + p_mfa k'));
     (pcl_addr AL c + 16, pcl_addr AL c + 80);
     (at_thr (al_thread AL) + CSTATS_OFF + 16, at_thr (al_thread AL) + CSTATS_OFF + 32);
     (at_thr (al_thread AL) + TSTATS_OFF, at_thr (al_thread AL) + TSTATS_OFF + 368)].

  Definition gfa_post (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (q lo c : Z) (k : pclass) (calloc cmapped : Z) (H : word -> bool) (m : mem) : unit -> (word -> bool) -> machine_state -> Prop :=
    fun _ H' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      let k' := refill k c in
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ H' = H_gfa AL c k (max_count c / 2) H
      /\ munch (gfa_W lo q c k k') m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo q /\ poison_env E m' /\ thread_env (al_thread AL) m' /\ prim_env AL m' /\ shvis H' m'
      /\ pclass_wf c k' /\ ri_rep AL m' c k'
      /\ rw_cells asegs m' (pcl_addr AL c) [C4 (wz 0); C4 (wz (max_count c)); C8 (wz (class_size c))]
      /\ (exists cs, u32arr asegs m' (pcl_addr AL c + 16) cs /\ length cs = 16%nat /\ firstn (length (p_chunks k')) cs = map wz (p_chunks k'))
      /\ fa_rep AL m' c k' /\ tail_rep AL m' c k'
      /\ (forall v, In v (p_fa k' ++ p_chunks k') -> free_chunk AL m' c v)
      /\ stats_rep AL m' calloc (cmapped + (p_mu k' - p_mu k)).

  #[using="Type"] Theorem gfa_spec :
    forall (ra gp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32)
           (m : mem) (H : word -> bool) (q lo c : Z) (k : pclass) (calloc cmapped : Z),
    alayout_ok AL ->
    mem_inv asegs m -> mclean H m -> shvis H m -> poison_env E m -> thread_env (al_thread AL) m -> prim_env AL m ->
    stk asegs m lo q -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q - GFA_STACK -> q <= 2^47 -> q mod 16 = 0 ->
    1 <= c <= 31 -> cls_rep AL m true c k -> p_cnt k = 0 -> stats_rep AL m calloc cmapped -> refill_budget c k ->
    0 <= calloc -> 0 <= cmapped -> cmapped + K_REGION < 2^63 ->
    implA H (t_gfa AL c k (max_count c / 2))
          (gfa_post ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc q lo c k calloc cmapped H m)
          (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz INSTANCE) (wz (at_thr (al_thread AL) + CSTATS_OFF)) (wz c) (wz (pcl_addr AL c + 16)) (wz (max_count c / 2)) a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F_ (wz gfa_entry2) fc None m (seg_rom asegs)).
  Proof.
    intros ra gp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m H q lo c k calloc cmapped
           AO MI MC SV PE TE PRE ST LOH CLO LO QH Q16 Hc CR C0 SR RB CA0 CM0 CMB.
    destruct CR as (WF & (j8 & j64 & j88 & j96 & j104 & j112 & jpad & RIC) & PCL & FAR & TLR & FCH).
    destruct RB as [BUD1 BUD2].
    unfold GFA_STACK, POP_STACK, MF_STACK in LO.
    pose proof (half_range c k Hc) as (NR & N2).
    pose proof (max_count_range c Hc) as (MR & _).
    set (n := max_count c / 2) in *.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    layout_facts AO 0%nat SPF. layout_facts AO 3%nat THF.
    destruct SPF as (SP1 & SP2 & SP3 & _ & SP5 & _ & _). destruct THF as (TH1 & TH2 & TH3 & _ & TH5 & _ & _).
    pose proof AO as AO'. destruct AO' as (_ & _ & SPAL & TLO & _ & _).
    pose proof (region_range AL c Hc) as RR. unfold region in RR.
    layout_apart_fact AO 0%nat 3%nat AP03.
    pose proof (class_size_pos c Hc) as CS.
    pose proof WF as WF0. unfold pclass_wf in WF0.
    destruct WF0 as (Lnf & Lcnt & CNT & NF4 & MFA & MFAM & AU & MUF & MUM & AUS & GAP & ND & FB & NA & NFR).
    destruct SR as [STC (ts & TS)]. destruct TLR as [(jt & TL) TSH].
    destruct PCL as [PC1 (wsc & PA & PL & PX)]. destruct FAR as (ws & FAA & LEN & FX).
    cbv iota in PC1.
    demod SP3. demod TH3. demod SPAL. demod MFAM. demod MUM. demod Q16. clear AUS GAP.
    unfold ri_rep in *. unfold ri_addr, RIB in *. unfold ri_cells in RIC. unfold pcl_addr in *. unfold fa_base, region in *.
    assert (SHT : sh (al_space AL + c * 4294967296 + p_au k) + (p_mu k - p_au k) / 8 <= 17594333495296).
    { pose proof (sh_le (al_space AL + c * 4294967296 + p_mu k) (2^47) ltac:(lia)) as X. change (sh (2^47)) with 17594333495296 in X.
      assert (A8 : p_au k mod 8 = 0).
      { pose proof (class_size_mod16 c Hc) as C16. destruct (Z.eq_dec (p_au k mod 8) 0) as [E0|NE]; [exact E0| exfalso].
        pose proof (proj1 (Z.mod_divide (p_au k) (class_size c) ltac:(lia))) as DV.
        clear - NE C16 CS DV WF. unfold pclass_wf in WF. destruct WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & AUS & _).
        destruct (DV AUS) as [z Hz]. rewrite Hz in NE. apply NE. Z.div_mod_to_equations. nia. }
      revert X. unfold sh. rewrite MUM0, SP0. clear - A8. intros X. Z.div_mod_to_equations. lia. }
    assert (SHT0 : 2147450880 <= sh (al_space AL + c * 4294967296 + p_au k)) by (pose proof (sh_le 0 (al_space AL + c * 4294967296 + p_au k) ltac:(lia)) as X; exact X).
    set (t8 := (p_mu k - p_au k) / 8) in *. assert (Ht8 : 0 <= t8) by (subst t8; apply Z.div_pos; lia).
    assert (ERIB : RIB AL = al_space AL + 137438953472) by reflexivity.
    destruct (gfa_A AL AO ra gp (wz A0_TP) F_ fc q c n (THR + 208 + 80 * c + 16) (THR + CSTATS_OFF) m Hc lo s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a5 a6 a7 k j8 j64 j88 j96 j104 j112 jpad
                ST CLO ltac:(lia) ltac:(rewrite Q0; apply Z_mod_mult) QH PRE RIC MI) as [junk GA].
    assert (FV : Forall (fun v => 0 <= v < 2^31) (p_fa k)).
    { apply Forall_forall. intros v Hv. pose proof (proj1 (Forall_forall _ _) FB v ltac:(apply in_or_app; left; exact Hv)) as (V0 & V1 & _). cbv beta in V0, V1. lia. }
    destruct (Z.ltb_spec (p_nf k) n) as [LT|GE].
    2: {

      assert (EK1 : gfa_pre k c n = k) by (unfold gfa_pre; replace (p_nf k <? n) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
      unfold t_gfa. fold n. replace (p_nf k <? n) with false by (symmetry; apply Z.ltb_ge; lia). unfold t_none.
      pose proof (munch_refl [(lo, q); (al_space AL + 137438953472 + 128 * c, al_space AL + 137438953472 + 128 * c + 128);
                              (THR + 208 + 80 * c + 16, THR + 208 + 80 * c + 80)] m) as MU.
      pose proof (wmono_refl asegs m) as WM.
      lz_go.
      eapply evt_cut; [exact GA|]. clear GA. post_call asegs m.
      match goal with P : rw_cells asegs _ (RIB AL + 128 * c) _ |- _ => rename P into RIC2 end.
      unfold ri_cells, RIB in RIC2. unfold RIB, fa_base, region.
      zstep.
      zstep. if_cases K1; zify_cond K1. { exfalso. lia. } clear K1.
      zstep. zstep.
      zstep. if_cases K2; zify_cond K2. { exfalso. lia. } clear K2.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        call (gfa_B AL AO ra gp (wz A0_TP) F_ fc q c n (THR + 208 + 80 * c + 16) Hc lo s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ _ _ _ _ _ _ _ _ _ _ _ _
                 (mkPCL (p_nf k - n) (p_mfa k) (p_au k) (p_mu k) (p_nalloc k) (p_nfreed k) (p_fa k) (p_cnt k) (p_chunks k))
                 j8 j64 j88 j96 j104 j112 jpad ws wsc (p_fa k) (p_nf k - n) junk mx) end.
      1: reflexivity.
      1: lia.
      1: replace (p_nf k - n + n) with (p_nf k) by lia; lia.
      1: lia.
      1: exact PL.
      1: lia.
      1: exact FX.
      1: exact FV.
      1: assumption.
      1: assumption.
      1: lia.
      1-2: lia.
      1: lia.
      1: unfold ri_cells, RIB; cbn [p_nf p_mfa p_au p_mu p_nalloc p_nfreed]; assumption.
      1: assumption.
      1: assumption.
      1-2: lia.
      1: rewrite Q0; apply Z_mod_mult.
      1: lia.
      1: assumption.
      cbn [p_nf p_mfa p_au p_mu p_nalloc p_nfreed p_fa p_cnt p_chunks] in *.
      lz_ret. unfold gfa_post. cbv zeta. rewrite (refill_shape c k). cbv zeta. fold n. rewrite EK1.
      finish.
      - unfold H_gfa. fold n. replace (p_nf k <? n) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
      - eapply munch_weaken; [| exact MU]. unfold sub_fp, gfa_W, ri_addr, RIB, pcl_addr, fa_base, region; cbn [outside p_nf p_mfa p_mu]; intros; lia.
      - eapply poison_env_frame; [exact PE| exact MU| exact WM| env_clear].
      - eapply thread_env_frame; [exact TE| exact MU| exact WM|].
        pose proof TLO as TL'. unfold thread_layout_ok in TL'. layout_apart_fact AO 0%nat 2%nat AP02.
        destruct TL' as (CX1 & CX2 & _ & _ & CXT & _). env_clear.
      - eapply prim_env_frame; [exact PRE| exact MU| exact WM| env_clear].
      - eapply shvis_wmono; [exact SV| exact WM].
      - pose proof (refill_wf c k Hc WF BUD1 BUD2 C0) as WFR. rewrite (refill_shape c k) in WFR. cbv zeta in WFR. fold n in WFR. rewrite EK1 in WFR. exact WFR.
      - unfold ri_rep, ri_addr. exists j8, j64, j88, j96, j104, j112, jpad. exact PC.
      - unfold pcl_addr. rewrite C0 in PC1. exact PC1.
      - cbn [p_chunks].
        assert (LS : length (skipn (Z.to_nat (p_nf k - n)) (p_fa k)) = Z.to_nat n) by (rewrite length_skipn; lia).
        exists (cp_list (p_fa k) (p_nf k - n) (Z.to_nat n) wsc). split; [unfold pcl_addr; exact PC4|]. split.
        + rewrite cp_list_length by lia. exact PL.
        + unfold cp_list. rewrite LS. rewrite <- LS at 2. rewrite firstn_all.
          rewrite <- (length_map wz) in LS. rewrite <- LS. rewrite firstn_app_le by lia. apply firstn_all.
      - unfold fa_rep. cbn [p_mfa p_fa]. exists ws. split; [exact PC3|]. split; [exact LEN|].
        rewrite length_firstn, Nat.min_l by lia.
        rewrite <- firstn_map, <- FX, firstn_firstn. f_equal. lia.
      - unfold tail_rep. cbn [p_au p_mu]. unfold region. split; [exists jt; exact TL| subst t8; exact TSH].
      - cbn [p_fa p_chunks]. rewrite firstn_skipn. intros v Hv.
        eapply (free_chunks_frame AL AO c k Hc WF _ m _ MU WM); [| exact FCH| apply in_or_app; left; exact Hv].
        assert (SHB : sh (region AL c + p_au k) <= 17594333495296) by (pose proof (sh_le (region AL c + p_au k) (2^47) ltac:(unfold region; lia)) as X; exact X).
        assert (SHR : sh (region AL c) <= sh (region AL c + p_au k)) by (apply sh_le; lia).
        assert (SHR0 : 2147450880 <= sh (region AL c)) by (pose proof (sh_le 0 (region AL c) ltac:(unfold region; lia)) as X; exact X).
        unfold carved_clear. unfold region in *.
        clear - SHB SHR SHR0 SP1 SP2 RR AP03 TH1 TH2 AU MUF CLO LO Hc ACR.
        repeat first [apply Forall_nil | apply Forall_cons]; cbn [fst snd]; repeat split; lia.
      - cbn [p_mu]. replace (cmapped + (p_mu k - p_mu k)) with cmapped by lia. split; [exact STC| exists ts; exact TS].
    }

    destruct (gfa_req c k Hc WF BUD1 BUD2 LT) as (RQ & B1 & B2). fold n in RQ, B1, B2.
    assert (EK1 : gfa_pre k c n = populate k c (n - p_nf k)) by (unfold gfa_pre; replace (p_nf k <? n) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
    pose proof (populate_wf c (n - p_nf k) k Hc RQ WF B1 B2) as WFP.
    pose proof (populate_shape c (n - p_nf k) k) as (S_nf & S_au & S_mu & S_fa & S_cnt & S_ch & S_na & S_nfr & S_mfa).
    pose proof (pop_mu_facts c (n - p_nf k) k Hc RQ WF B1) as (M1 & M2 & M3 & M4 & M5 & _). rewrite <- S_mu in M1, M5.
    pose proof (gfa_pre_enough c k Hc WF BUD1 BUD2) as EN. fold n in EN. rewrite EK1 in EN.
    pose proof WFP as WFP0. unfold pclass_wf in WFP0.
    destruct WFP0 as (Lnf' & _ & _ & NF4' & MFA' & MFAM' & AU' & MUF' & _ & _ & _ & _ & FB' & NA' & _).
    assert (MFAle : p_mfa k <= p_mfa (populate k c (n - p_nf k))).
    { rewrite S_mfa. unfold efa_new. cbn [p_mfa].
      destruct (Z.leb_spec (4 * (p_nf k + pop_new k c (n - p_nf k))) (p_mfa k)) as [LE|GT]; [lia|].
      pose proof (rup_ge (4 * (p_nf k + pop_new k c (n - p_nf k))) K_MAP ltac:(lia)). lia. }
    clear M2 M3 M4 S_mfa.
    unfold t_gfa. fold n. replace (p_nf k <? n) with true by (symmetry; apply Z.ltb_lt; lia).
    assert (SHL1 : 2147450880 <= sh (al_space AL + c * 4294967296 + p_mu k)) by (pose proof (sh_le 0 (al_space AL + c * 4294967296 + p_mu k) ltac:(lia)) as X; exact X).
    assert (SHL2 : 2147450880 <= sh (al_space AL + c * 4294967296 + 3758096384 + p_mfa k)) by (pose proof (sh_le 0 (al_space AL + c * 4294967296 + 3758096384 + p_mfa k) ltac:(lia)) as X; exact X).
    assert (SHU1 : sh (al_space AL + c * 4294967296 + p_mu (populate k c (n - p_nf k))) <= 17594333495296) by (pose proof (sh_le (al_space AL + c * 4294967296 + p_mu (populate k c (n - p_nf k))) (2^47) ltac:(lia)) as X; exact X).
    assert (SHU2 : sh (al_space AL + c * 4294967296 + 3758096384 + p_mfa (populate k c (n - p_nf k))) <= 17594333495296) by (pose proof (sh_le (al_space AL + c * 4294967296 + 3758096384 + p_mfa (populate k c (n - p_nf k))) (2^47) ltac:(lia)) as X; exact X).
    pose proof (munch_refl [(lo, q); (al_space AL + 137438953472 + 128 * c, al_space AL + 137438953472 + 128 * c + 128);
              (al_space AL + c * 4294967296 + 3758096384 + 4 * p_nf k, al_space AL + c * 4294967296 + 3758096384 + p_mfa (populate k c (n - p_nf k)));
              (al_space AL + c * 4294967296 + p_mu k, al_space AL + c * 4294967296 + p_mu (populate k c (n - p_nf k)));
              (al_space AL + c * 4294967296 + 3758096384 + p_mfa k, al_space AL + c * 4294967296 + 3758096384 + p_mfa (populate k c (n - p_nf k)));
              (sh (al_space AL + c * 4294967296 + p_mu k), sh (al_space AL + c * 4294967296 + p_mu (populate k c (n - p_nf k))));
              (sh (al_space AL + c * 4294967296 + 3758096384 + p_mfa k), sh (al_space AL + c * 4294967296 + 3758096384 + p_mfa (populate k c (n - p_nf k))));
              (THR + 208 + 80 * c + 16, THR + 208 + 80 * c + 80);
              (THR + 2768 + 16, THR + 2768 + 32); (THR + 2800, THR + 2800 + 368)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    lazymatch type of MU with munch ?W0 _ _ => assert (AIW : above_img W0) by env_clear end.
    lazymatch type of MU with munch ?W0 _ _ => assert (TCW : thread_clear (al_thread AL) W0) end.
    { pose proof TLO as TL'. unfold thread_layout_ok in TL'. layout_apart_fact AO 0%nat 2%nat AP02.
      destruct TL' as (CX1 & CX2 & _ & _ & CXT & _).
      clear - CX1 CX2 CXT AP02 AP03 SP1 SP2 TH1 TH2 CLO LO RR Hc SHL1 SHL2 SHU1 SHU2 M1 M5 MFA MFAle MFA' Lnf ACR AU MUF.
      env_clear. }
    lz_go.
    eapply evt_cut; [exact GA|]. clear GA. post_call asegs m.
    match goal with P : rw_cells asegs _ (RIB AL + 128 * c) _ |- _ => rename P into RIC2 end.
    unfold ri_cells, RIB in RIC2. unfold RIB, fa_base, region.
    zstep.
    zstep. if_cases K1; zify_cond K1. 2: { exfalso. lia. } clear K1.
    do 6 zstep. zstep.
    assert (ERI : ri_addr AL c = al_space AL + 137438953472 + 128 * c) by reflexivity.
    assert (EFA : fa_base AL c = al_space AL + c * 4294967296 + 3758096384) by reflexivity.
    assert (EREG : region AL c = al_space AL + c * 4294967296) by reflexivity.
    assert (SHB : sh (region AL c + p_au k) <= 17594333495296) by (pose proof (sh_le (region AL c + p_au k) (2^47) ltac:(unfold region; lia)) as X; exact X).
    assert (SHR : sh (region AL c) <= sh (region AL c + p_au k)) by (apply sh_le; lia).
    assert (SHA : sh (region AL c + p_au k) <= sh (al_space AL + c * 4294967296 + p_mu k)) by (apply sh_le; unfold region; lia).
    assert (SHF : sh (region AL c + p_au k) <= sh (al_space AL + c * 4294967296 + 3758096384 + p_mfa k)) by (apply sh_le; unfold region; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (FCHx : forall v, In v (p_fa k ++ p_chunks k) -> free_chunk AL mx c v) end.
    { eapply (free_chunks_frame AL AO c k Hc WF _ m _ MU WM); [| exact FCH].
      assert (SHR0 : 2147450880 <= sh (region AL c)) by (pose proof (sh_le 0 (region AL c) ltac:(unfold region; lia)) as X; exact X).
      unfold carved_clear. rewrite EREG in *.
      clear - SHB SHR SHR0 SHA SHF SHU1 SHU2 SP1 SP2 RR AP03 TH1 TH2 AU MUF CLO LO Hc ACR M1 MFA Lnf.
      repeat first [apply Forall_nil | apply Forall_cons]; cbn [fst snd]; repeat split; lia. }
    clear SHB SHR SHA SHF.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mC end.
    hide PC0.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (munch_refl [(lo, q - 128); (ri_addr AL c, ri_addr AL c + 128); (fa_base AL c + 4 * p_nf k, fa_base AL c + p_mfa (populate k c (n - p_nf k)));
              (region AL c + p_mu k, region AL c + p_mu (populate k c (n - p_nf k))); (fa_base AL c + p_mfa k, fa_base AL c + p_mfa (populate k c (n - p_nf k)));
              (sh (region AL c + p_mu k), sh (region AL c + p_mu (populate k c (n - p_nf k)))); (sh (fa_base AL c + p_mfa k), sh (fa_base AL c + p_mfa (populate k c (n - p_nf k))));
              (at_thr (al_thread AL) + CSTATS_OFF + 16, at_thr (al_thread AL) + CSTATS_OFF + 32);
              (at_thr (al_thread AL) + TSTATS_OFF, at_thr (al_thread AL) + TSTATS_OFF + 368)] mx) as MUx;
      pose proof (wmono_refl asegs mx) as WMx;
      callAx (populate_spec AL E _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc mx H (q - 128) lo c (n - p_nf k) k true calloc cmapped AO MI0) dropping RIC2 PC1 PA FAA TL TSH STC TS;
      [ assumption
      | eapply shvis_wmono; [exact SV| exact WM]
      | eapply poison_env_frame; [exact PE| exact MU| exact WM| exact AIW]
      | eapply thread_env_frame; [exact TE| exact MU| exact WM| exact TCW]
      | exact POST | exact PC2 | exact LOH | exact CLO | unfold POP_STACK, MF_STACK; lia | lia | rewrite Q0; replace (qz4 * 16 - 128) with ((qz4 - 8) * 16) by lia; apply Z_mod_mult
      | exact Hc | exact RQ
      | split; [exact WF|]; split; [exists j8, j64, j88, j96, j104, j112, jpad; unfold ri_cells, ri_addr, RIB; exact RIC2|];
        split; [split; [unfold pcl_addr; exact PC1| exists wsc; split; [unfold pcl_addr; exact PA| split; [exact PL| exact PX]]]|];
        split; [exists ws; split; [unfold fa_base, region; exact FAA| split; [exact LEN| exact FX]]|];
        split; [split; [exists jt; unfold region; exact TL| unfold region; subst t8; exact TSH]| exact FCHx]
      | split; [exact STC| exists ts; exact TS]
      | exact B1 | exact B2 | exact CA0 | exact CM0 | exact CMB | ] end.
    destruct r.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mP end.
    rename PC into STP, PC1 into PEP, PC3 into TEP, PC4 into PREP, PC5 into SVP, PC6 into COP, POST0 into SRP, MI into MIP.
    set (kp := populate k c (n - p_nf k)) in *.
    destruct COP as (_ & (p8 & p64 & p88 & p96 & p104 & p112 & ppad & RICP) & PCLP & FARP & TLRP & FCHP).
    destruct SRP as [STCP (tsp & TSP)]. destruct PCLP as [PC1P (wscp & PAP & PLP & PXP)]. destruct FARP as (wsp & FAAP & LENP & FXP). destruct TLRP as [(jtp & TLP) TSHP].
    unfold ri_cells in RICP. unfold ri_addr, RIB in RICP. unfold pcl_addr in PC1P, PAP. unfold fa_base, region in FAAP. unfold prim_env in PREP.

    unhide PC0. rewrite ERI, EFA, EREG in MUx.
    pose proof (rw_cells_transport asegs _ mC mP _ _ PC0 MUx WMx ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - LO CLO LOH ACR SP1 SP2 RR Hc TH2 SHU1 SHU2 MFA' MUF' Lnf MFA AU MUF; lia)) as FRP.
    clear PC0 MUx WMx.

    pose proof (munch_refl [(q - 128, q); (al_space AL + 137438953472 + 128 * c, al_space AL + 137438953472 + 128 * c + 128);
                            (THR + 208 + 80 * c + 16, THR + 208 + 80 * c + 80)] mP) as MUy.
    pose proof (wmono_refl asegs mP) as WMy.
    hide TLP. hide TSHP. hide TSP. hide STCP. hide PC1P.
    zstep. if_false_z.
    zstep.
    zstep.
    zstep. if_cases K2; zify_cond K2. { exfalso. clear - K2 EN Lnf' NR. lia. } clear K2.
    zstep.
    zstep. zstep.
    zstep. zstep.
    assert (FVp : Forall (fun v => 0 <= v < 2^31) (p_fa kp)).
    { apply Forall_forall. intros v Hv. pose proof (proj1 (Forall_forall _ _) FB' v ltac:(apply in_or_app; left; exact Hv)) as (V0 & V1 & _). cbv beta in V0, V1. lia. }

    assert (Hn : n = max_count c / 2) by reflexivity. hide Hn. clearbody n. hide BUD2. hide B2. hide MFAM'. clear SHT Ht8. clear t8.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      call (gfa_B AL AO ra gp (wz A0_TP) F_ fc q c n (THR + 208 + 80 * c + 16) Hc lo s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 (mkPCL (p_nf kp - n) (p_mfa kp) (p_au kp) (p_mu kp) (p_nalloc kp) (p_nfreed kp) (p_fa kp) (p_cnt kp) (p_chunks kp))
                 p8 p64 p88 p96 p104 p112 ppad wsp wscp (p_fa kp) (p_nf kp - n) junk mx) end.
    1: reflexivity.
    1: lia.
    1: replace (p_nf kp - n + n) with (p_nf kp) by lia; lia.
    1: lia.
    1: exact PLP.
    1: lia.
    1: exact FXP.
    1: exact FVp.
    1: assumption.
    1: assumption.
    1: lia.
    1-2: lia.
    1: lia.
    1: unfold ri_cells, RIB; cbn [p_nf p_mfa p_au p_mu p_nalloc p_nfreed]; assumption.
    1: assumption.
    1: assumption.
    1-2: lia.
    1: rewrite Q0; apply Z_mod_mult.
    1: lia.
    1: assumption.
    cbn [p_nf p_mfa p_au p_mu p_nalloc p_nfreed p_fa p_cnt p_chunks] in *.
    unhide Hn. unhide BUD2.

    assert (SHP0 : 2147450880 <= sh (region AL c + p_au kp) /\ sh (region AL c + p_mu kp) <= 17594333495296
                   /\ sh (region AL c + p_au kp) + (p_mu kp - p_au kp) / 8 <= sh (region AL c + p_mu kp)).
    { split; [pose proof (sh_le 0 (region AL c + p_au kp) ltac:(unfold region; lia)) as X; exact X|].
      split; [pose proof (sh_le (region AL c + p_mu kp) (2^47) ltac:(unfold region; lia)) as X; exact X|].
      unfold sh. clear. Z.div_mod_to_equations. lia. }
    unhide TLP. unhide TSHP. unhide STCP. unhide TSP. unhide PC1P.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
    pose proof (rw_cells_transport asegs _ mP mF _ _ TLP MUy WMy ltac:(cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; unfold region; clear - LO CLO ACR SP1 SP2 RR Hc TH1 TH2 AP03 AU' MUF'; lia)) as TLF.
    pose proof (rw_cells_transport asegs _ mP mF _ _ TSHP MUy WMy ltac:(cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (apply Z.div_pos; lia); clear - SHP0 LO CLO LOH ACR SP1 SP2 TH1 TH2 Hc; lia)) as TSHF.
    pose proof (rw_cells_transport asegs _ mP mF _ _ STCP MUy WMy ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - LO CLO ACR SP1 SP2 TH1 TH2 AP03 Hc; lia)) as STCF.
    pose proof (rw_cells_transport asegs _ mP mF _ _ TSP MUy WMy ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - LO CLO ACR SP1 SP2 TH1 TH2 AP03 Hc; lia)) as TSF.
    pose proof (rw_cells_transport asegs _ mP mF _ _ PC1P MUy WMy ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - LO CLO ACR SP1 SP2 TH1 TH2 AP03 Hc; lia)) as PC1F.
    clear TLP TSHP STCP TSP PC1P.
    lz_ret. unfold gfa_post. cbv zeta. rewrite (refill_shape c k). cbv zeta. rewrite <- Hn. rewrite EK1. fold kp.
    finish.
    - unfold H_gfa. replace (p_nf k <? n) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    - eapply poison_env_frame; [exact PEP| exact MUy| exact WMy|]. clear - LO CLO ACR SP1 SP2 TH1 TH2 Hc. env_clear.
    - eapply thread_env_frame; [exact TEP| exact MUy| exact WMy|].
      pose proof TLO as TL'. unfold thread_layout_ok in TL'. layout_apart_fact AO 0%nat 2%nat AP02.
      destruct TL' as (CX1 & CX2 & _ & _ & CXT & _). clear - CX1 CX2 CXT AP02 AP03 SP1 SP2 TH1 TH2 CLO LO Hc ACR. env_clear.
    - eapply shvis_wmono; [exact SVP| exact WMy].
    - pose proof (refill_wf c k Hc WF BUD1 BUD2 C0) as WFR. rewrite (refill_shape c k) in WFR. cbv zeta in WFR. rewrite <- Hn in WFR. rewrite EK1 in WFR. exact WFR.
    - unfold ri_rep, ri_addr. exists p8, p64, p88, p96, p104, p112, ppad. exact PC.
    - unfold pcl_addr. rewrite S_cnt, C0 in PC1F. exact PC1F.
    - cbn [p_chunks].
      assert (LS : length (skipn (Z.to_nat (p_nf kp - n)) (p_fa kp)) = Z.to_nat n) by (rewrite length_skipn; lia).
      exists (cp_list (p_fa kp) (p_nf kp - n) (Z.to_nat n) wscp). split; [unfold pcl_addr; exact PC1|]. split.
      + rewrite cp_list_length by lia. exact PLP.
      + unfold cp_list. rewrite LS. rewrite <- LS at 2. rewrite firstn_all.
        rewrite <- (length_map wz) in LS. rewrite <- LS. rewrite firstn_app_le by lia. apply firstn_all.
    - unfold fa_rep. cbn [p_mfa p_fa]. exists wsp. split; [exact PC0|]. split; [exact LENP|].
      rewrite length_firstn, Nat.min_l by lia.
      rewrite <- firstn_map, <- FXP, firstn_firstn. f_equal. lia.
    - unfold tail_rep. cbn [p_au p_mu]. split; [exists jtp; exact TLF| exact TSHF].
    - cbn [p_fa p_chunks]. rewrite firstn_skipn. intros v Hv.
      eapply (free_chunks_frame AL AO c kp Hc WFP _ mP _ MUy WMy); [| exact FCHP| apply in_or_app; left; exact Hv].
      assert (SHB : sh (region AL c + p_au kp) <= 17594333495296) by (pose proof (sh_le (region AL c + p_au kp) (2^47) ltac:(unfold region; lia)) as X; exact X).
      assert (SHR : sh (region AL c) <= sh (region AL c + p_au kp)) by (apply sh_le; lia).
      assert (SHR0 : 2147450880 <= sh (region AL c)) by (pose proof (sh_le 0 (region AL c) ltac:(unfold region; lia)) as X; exact X).
      unfold carved_clear. unfold region in *.
      clear - SHB SHR SHR0 SP1 SP2 RR AP03 TH1 TH2 AU' MUF' CLO LO Hc ACR.
      repeat first [apply Forall_nil | apply Forall_cons]; cbn [fst snd]; repeat split; lia.
    - cbn [p_mu]. split; [exact STCF| exists tsp; exact TSF].
  Qed.
End GFA2.
