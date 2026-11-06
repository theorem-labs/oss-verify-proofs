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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR F_prim_efa F_prim_rta ATacFix.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition RTA_STACK : Z := 128 + 48 + MF_STACK + 64.

Tactic Notation "callAx" uconstr(SPEC) "dropping" ne_hyp_list(HS) :=
  lz_here;
  lazymatch goal with
  | |- ITreeLZ.implL ?segs _ _ _ _ _ (MS _ _ _ _ _ ?m _) =>
      let C := find_mclean m in
      eapply implA_ebind; [ eapply implA_mclean; [ exact C | eapply SPEC ] | clear C; clear HS; post_callA segs m ]
  end.

Tactic Notation "callA0" uconstr(SPEC) :=
  lz_here;
  lazymatch goal with
  | |- ITreeLZ.implL ?segs _ _ _ _ _ (MS _ _ _ _ _ ?m _) =>
      let C := find_mclean m in
      eapply implA_ebind; [ eapply implA_mclean; [ exact C | eapply SPEC ] | clear C ]
  end.

Lemma rc_list_prefix : forall (ws : list word) (fa vals : list Z) (n : nat),
  firstn (length fa) ws = map wz fa -> length vals = n -> (length fa + n <= length ws)%nat ->
  firstn (length (fa ++ vals)) (rc_list ws (Z.of_nat (length fa)) n vals) = map wz (fa ++ vals).
Proof.
  intros ws fa vals n FX LV LW. unfold rc_list. rewrite Nat2Z.id, length_app, map_app, <- FX.
  rewrite <- LV, firstn_all. rewrite app_assoc.
  rewrite firstn_app. rewrite firstn_all2 by (rewrite length_app, length_firstn, length_map; lia).
  rewrite length_app, length_firstn, length_map, Nat.min_l by lia.
  replace (length fa + length vals - (length fa + length vals))%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

Section RTA2.
  Context {HC : HasCeiling}.
  Variables (AL : alayout) (E : penv).
  Notation THR := (at_thr (al_thread AL)).

  Definition rta_W (lo q c : Z) (k k' : pclass) : list (Z * Z) :=
    [(lo, q); (ri_addr AL c, ri_addr AL c + 128); (fa_base AL c + 4 * p_nf k, fa_base AL c + p_mfa k');
     (sh (fa_base AL c + p_mfa k), sh (fa_base AL c + p_mfa k) + (p_mfa k' - p_mfa k) / 8);
     (swlo (fa_base AL c + p_mfa k), swhi (fa_base AL c + p_mfa k) (p_mfa k' - p_mfa k));
     (THR + TSTATS_OFF, THR + TSTATS_OFF + 368)].

  Definition rta_post (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (q lo c : Z) (k : pclass) (vals : list Z) (CHB : Z) (cs : list word) (H : word -> bool) (m : mem) : unit -> (word -> bool) -> machine_state -> Prop :=
    fun _ H' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      let k' := return_to_allocator k vals in
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ H' = H_efa AL c k (p_nf k + Z.of_nat (length vals)) H
      /\ munch (rta_W lo q c k k') m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo q /\ poison_env E m' /\ thread_env (al_thread AL) m' /\ prim_env AL m' /\ shvis H' m'
      /\ ri_rep AL m' c k' /\ fa_rep AL m' c k'
      /\ u32arr asegs m' CHB cs
      /\ (exists ts, rw_cells asegs m' (THR + TSTATS_OFF) [CB 368 ts]).

  #[using="Type"] Theorem rta_spec :
    forall (ra gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32)
           (m : mem) (H : word -> bool) (q lo c : Z) (k : pclass) (vals : list Z) (CHB c0 MM STATx : Z) (cs : list word),
    alayout_ok AL ->
    mem_inv asegs m -> mclean H m -> shvis H m -> poison_env E m -> thread_env (al_thread AL) m -> prim_env AL m ->
    stk asegs m lo q -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q - RTA_STACK -> q <= 2^47 -> q mod 16 = 0 ->
    1 <= c <= 31 -> pclass_wf c k -> ri_rep AL m c k -> fa_rep AL m c k ->
    (exists ts, rw_cells asegs m (THR + TSTATS_OFF) [CB 368 ts]) ->
    1 <= Z.of_nat (length vals) <= 16 -> 4 * (p_nf k + Z.of_nat (length vals)) <= K_FA_SIZE ->
    u32arr asegs m CHB cs -> 0 <= c0 ->
    (forall j, (j < length vals)%nat -> nth_error cs (Z.to_nat c0 + j) = Some (wz (nth j vals 0))) ->
    Forall (fun v => 0 <= v < 2^31) vals ->
    THR + CACHE_OFF <= CHB -> CHB + 4 * Z.of_nat (length cs) <= THR + CSTATS_OFF ->
    implA H (t_efa AL c k (p_nf k + Z.of_nat (length vals)))
          (rta_post ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc q lo c k vals CHB cs H m)
          (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz INSTANCE) (wz MM) (wz STATx) (wz c) (wz (CHB + 4 * c0)) (wz (Z.of_nat (length vals))) a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F_ (wz rta_entry) fc None m (seg_rom asegs)).
  Proof.
    intros ra gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m H q lo c k vals CHB c0 MM STATx cs
           AO MI MC SV PE TE PRE ST LOH CLO LO QH Q16 Hc WF (j8 & j64 & j88 & j96 & j104 & j112 & jpad & RIC) FAR TSX NB TB CHA C0 RD SM CHL CHH.
    unfold RTA_STACK, MF_STACK in LO.
    set (n := Z.of_nat (length vals)) in *.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    layout_facts AO 0%nat SPF. layout_facts AO 3%nat THF.
    destruct SPF as (SP1 & SP2 & SP3 & _ & SP5 & _ & _). destruct THF as (TH1 & TH2 & TH3 & _ & TH5 & _ & _).
    pose proof AO as AO'. destruct AO' as (_ & _ & SPAL & TLO & _ & _).
    pose proof (region_range AL c Hc) as RR. unfold region in RR.
    layout_apart_fact AO 0%nat 3%nat AP03.
    pose proof WF as WF0. unfold pclass_wf in WF0.
    destruct WF0 as (Lnf & Lcnt & CNT & NF4 & MFA & MFAM & AU & MUF & MUM & AUS & GAP & ND & FB & NA & NFR).
    unfold ri_addr, RIB in RIC.
    destruct (rta_A AL AO ra gp (wz A0_TP) F_ fc q c n (CHB + 4 * c0) STATx MM m Hc lo s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a6 a7 k j8 j64 j88 j96 j104 j112 jpad
                ST CLO ltac:(lia) Q16 QH PRE ltac:(unfold RIB; exact RIC) MI) as [junk GA].
    set (tot := p_nf k + n) in *.
    assert (EFN : p_mfa k <= efa_new k tot <= K_FA_SIZE /\ efa_new k tot mod K_MAP = 0 /\ 4 * tot <= efa_new k tot).
    { unfold efa_new. destruct (Z.leb_spec (4 * tot) (p_mfa k)) as [LE|GT]; [lia|].
      pose proof (rup_ge (4 * tot) K_MAP ltac:(lia)). pose proof (rup_mod (4 * tot) K_MAP ltac:(lia)).
      pose proof (rup_le (4 * tot) K_FA_SIZE K_MAP ltac:(lia) ltac:(lia) ltac:(reflexivity)). lia. }
    set (mfa1 := efa_new k tot) in *.
    destruct FAR as (ws & FAA & LEN & FX). destruct TSX as (ts & TS).
    assert (ERIB : RIB AL = al_space AL + 137438953472) by reflexivity.
    unfold fa_base, region in FAA.
    assert (SHL2 : 2147450880 <= sh (al_space AL + c * 4294967296 + 3758096384 + p_mfa k)) by (pose proof (sh_le 0 (al_space AL + c * 4294967296 + 3758096384 + p_mfa k) ltac:(lia)) as X; exact X).
    assert (SHU2 : sh (al_space AL + c * 4294967296 + 3758096384 + p_mfa k) + (mfa1 - p_mfa k) / 8 <= 17594333495296).
    { pose proof (sh_le (al_space AL + c * 4294967296 + 3758096384 + mfa1) (2^47) ltac:(lia)) as X. change (sh (2^47)) with 17594333495296 in X.
      revert X. unfold sh. clear. intros X. Z.div_mod_to_equations. lia. }
    pose proof (sw_range (al_space AL + c * 4294967296 + 3758096384 + p_mfa k) (mfa1 - p_mfa k) ltac:(lia) ltac:(lia) ltac:(lia)) as SWR.
    pose proof (sw_bounds (al_space AL + c * 4294967296 + 3758096384 + p_mfa k) (mfa1 - p_mfa k) ltac:(lia) ltac:(lia)) as (SW1 & SW2 & _ & _ & SW5 & _).
    pose proof (munch_refl [(lo, q); (al_space AL + 137438953472 + 128 * c, al_space AL + 137438953472 + 128 * c + 128);
              (al_space AL + c * 4294967296 + 3758096384 + 4 * p_nf k, al_space AL + c * 4294967296 + 3758096384 + mfa1);
              (sh (al_space AL + c * 4294967296 + 3758096384 + p_mfa k), sh (al_space AL + c * 4294967296 + 3758096384 + p_mfa k) + (mfa1 - p_mfa k) / 8);
              (swlo (al_space AL + c * 4294967296 + 3758096384 + p_mfa k), swhi (al_space AL + c * 4294967296 + 3758096384 + p_mfa k) (mfa1 - p_mfa k));
              (THR + 2800, THR + 2800 + 368)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    lazymatch type of MU with munch ?W0 _ _ => assert (AIW : above_img W0) by (clear - LOH SP1 RR Hc TH1 SHL2 SWR Lnf MFA EFN; env_clear) end.
    lazymatch type of MU with munch ?W0 _ _ => assert (TCW : thread_clear (al_thread AL) W0) end.
    { pose proof TLO as TL'. unfold thread_layout_ok in TL'. layout_apart_fact AO 0%nat 2%nat AP02.
      destruct TL' as (CX1 & CX2 & _ & _ & CXT & _).
      clear - CX1 CX2 CXT AP02 AP03 SP1 SP2 TH1 TH2 CLO LO LOH RR Hc SHL2 SHU2 SWR SW1 SW2 EFN MFA Lnf ACR.
      env_clear. }
    rewrite <- (ebind_ret_r (t_efa AL c k tot)).
    lz_go.
    eapply evt_cut; [exact GA|]. clear GA. post_call asegs m.
    match goal with P : rw_cells asegs _ (RIB AL + 128 * c) _ |- _ => rename P into RIC2 end.
    unfold ri_cells, RIB in RIC2. unfold RIB, fa_base, region.
    zstep.
    do 5 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mC end.
    assert (ERI : ri_addr AL c = al_space AL + 137438953472 + 128 * c) by reflexivity.
    assert (EFA : fa_base AL c = al_space AL + c * 4294967296 + 3758096384) by reflexivity.
    assert (EREG : region AL c = al_space AL + c * 4294967296) by reflexivity.
    hide PC0. hide CHA.
    callA0 (efa_spec AL E AO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (q - 128) lo c tot k KWL);
      [ assumption | assumption
      | eapply shvis_wmono; [exact SV| exact WM]
      | eapply poison_env_frame; [exact PE| exact MU| exact WM| exact AIW]
      | eapply thread_env_frame; [exact TE| exact MU| exact WM| exact TCW]
      | exact POST
      | exact PC1 | exact LOH | exact CLO | clear - LO; lia | clear - QH; lia | clear - Q16; Z.div_mod_to_equations; lia | exact Hc
      | unfold tot, n; clear - Lnf; lia | exact TB
      | exact Lnf | exact NF4 | exact MFA | exact MFAM
      | unfold ri_cells, ri_addr, RIB; exact RIC2
      | exists ws; split; [unfold fa_base, region; exact FAA| split; [exact LEN| exact FX]]
      | exists ts; exact TS |].

    intros r H' ms' [PO MC]. destruct r.
    destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & mE & -> & -> & MUc & WMc & MIE & STE & PEE & TEE & PREE & SVE & RICE & FARE & TSE).
    clean_ms_mem MC.
    rewrite ERI, EFA in MUc. fold mfa1 in MUc.
    unhide PC0. unhide CHA.
    pose proof (rw_cells_transport asegs _ mC mE _ _ PC0 MUc WMc ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - LO CLO LOH ACR SP1 SP2 RR Hc TH2 SHU2 SWR EFN MFA; lia)) as FRE.
    pose proof (u32arr_bound asegs _ _ _ CHA) as CHBD.
    pose proof (u32arr_transport asegs _ mC mE _ _ CHA MUc WMc ltac:(cbn [disjoint_from]; clear - CHL CHH CHBD LO CLO LOH ACR SP1 SP2 RR Hc TH1 TH2 AP03 SHL2 SHU2 SWR EFN MFA; lia)) as CHAE.
    lazymatch type of MU with munch ?W0 _ _ => assert (MU' : munch W0 m mE) end.
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUc].
      unfold sub_fp; cbn [outside]. intros xo (O1 & O2 & O3 & O4 & O5 & O6 & _).
      split; [intros R; apply O1; clear - R; lia|]. split; [intros R; apply O2; clear - R; lia|].
      split; [intros R; apply O3; clear - R NF4; lia|]. split; [exact O4|]. split; [exact O5|]. split; [exact O6| exact I]. }
    pose proof (wmono_trans asegs _ _ _ WM WMc) as WM'.
    clear PC0 CHA MU WM MUc WMc POST PC1 RIC2 TS FAA. rename MU' into MU, WM' into WM.
    lz_cont MC.
    replace (ret_pc (Z_to_bv 64 222008)) with (Z_to_bv 64 222008) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    pose proof TEE as TE1. te_split TE1. clear TE_tsd TE_inited TE_tp TE_ctx TE_thr TE_bounds TE_sw TE_unw.
    destruct FARE as (ws1 & FAA1 & LEN1 & FX1). destruct TSE as (ts1 & TS1).
    unfold ri_cells, ri_addr, RIB in RICE. cbn [ensure_fa p_nf p_mfa p_au p_mu p_nalloc p_nfreed p_fa] in RICE, LEN1, FX1. fold mfa1 in RICE, LEN1.
    unfold prim_env in PREE.
    zstep. if_false_z.
    zstep. if_false_z.
    do 4 zstep.
    rewrite !Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
    replace (al_space AL + c * 4294967296 + 3758096384 + p_nf k * 4) with (fa_base AL c + 4 * (p_nf k + Z.of_nat 0)) by (unfold fa_base, region; lia).
    replace (CHB + 4 * c0 + n * 4) with (CHB + 4 * (c0 + n)) by lia.
    replace (Z_to_bv 64 (CHB + 4 * c0)) with (Z_to_bv 64 (CHB + 4 * (c0 + Z.of_nat 0))) by (f_equal; lia).
    assert (LW1 : (Z.to_nat (p_nf k + n) <= length ws1)%nat) by (clear - LEN1 EFN Lnf NB; unfold tot in EFN; lia).
    pose proof (u32arr_bound asegs _ _ _ FAA1) as FB1. pose proof (u32arr_bound asegs _ _ _ CHAE) as CB1.

    pose proof (wmono_refl asegs mE) as WMy.
    eapply evt_cut.
    { eapply (rta_copy AL gp (wz A0_TP) F_ fc c n (Z.to_nat n - 0) 0 mE mE ws1 cs vals (p_nf k) c0 CHB).
      - reflexivity.
      - clear - NB. lia.
      - clear - Lnf. lia.
      - exact LW1.
      - exact C0.
      - unfold n. rewrite Nat2Z.id. reflexivity.
      - exact NB.
      - intros j Hj. apply RD. unfold n in Hj. rewrite Nat2Z.id in Hj. exact Hj.
      - exact SM.
      - rewrite rc_list_0. exact FAA1.
      - exact CHAE.
      - unfold fa_base, region. clear - CHL CHH AP03 RR LEN1 EFN. lia.
      - apply munch_refl.
      - apply wmono_refl.
      - exact MIE. }
    cbv beta. intros ms1 (x12' & m1 & -> & MU1 & WM1 & MI1 & FAA2 & CHA2).

    assert (FAIN : al_space AL + 4294967296 <= fa_base AL c + 4 * p_nf k /\ fa_base AL c + 4 * (p_nf k + n) <= al_space AL + 137438953472)
      by (unfold fa_base, region; clear - RR EFN Lnf NB; unfold tot in EFN; lia).
    set (falo := fa_base AL c + 4 * p_nf k) in *. set (fahi := fa_base AL c + 4 * (p_nf k + n)) in *.
    pose proof (stk_transport_disjoint asegs _ mE m1 _ _ STE MU1 WM1 ltac:(cbn [disjoint_from]; clear - FAIN CLO SP2; lia)) as ST1.
    pose proof (rw_cells_transport asegs _ mE m1 _ _ PREE MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - FAIN SP1; lia)) as PRE1.
    pose proof (rw_cells_transport asegs _ mE m1 _ _ RICE MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - FAIN Hc; lia)) as RIC1.
    pose proof (rw_cells_transport asegs _ mE m1 _ _ TS1 MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - FAIN AP03; lia)) as TS2.
    pose proof (rw_cells_transport asegs _ mE m1 _ _ FRE MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - FAIN CLO SP2 LO; lia)) as FR1.
    pose proof (rw_cells_transport asegs _ mE m1 _ _ TE_gotpg MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - FAIN SP1; lia)) as GP1.
    pose proof (rw_cells_transport asegs _ mE m1 _ _ TE_pg MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - FAIN SP1; lia)) as PG1.
    assert (MU' : munch [(lo, q); (al_space AL + 137438953472 + 128 * c, al_space AL + 137438953472 + 128 * c + 128);
              (al_space AL + c * 4294967296 + 3758096384 + 4 * p_nf k, al_space AL + c * 4294967296 + 3758096384 + mfa1);
              (sh (al_space AL + c * 4294967296 + 3758096384 + p_mfa k), sh (al_space AL + c * 4294967296 + 3758096384 + p_mfa k) + (mfa1 - p_mfa k) / 8);
              (swlo (al_space AL + c * 4294967296 + 3758096384 + p_mfa k), swhi (al_space AL + c * 4294967296 + 3758096384 + p_mfa k) (mfa1 - p_mfa k));
              (THR + 2800, THR + 2800 + 368)] m m1).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU1].
      unfold sub_fp; cbn [outside]. intros xo (_ & _ & O3 & _). split; [| exact I].
      intros R. apply O3. subst falo fahi. unfold fa_base, region in R. clear - R EFN. unfold tot in EFN. lia. }
    pose proof (wmono_trans asegs _ _ _ WM WM1) as WM'. pose proof (wmono_trans asegs _ _ _ WMy WM1) as WMy'.
    clear STE PREE RICE TS1 FRE TE_gotpg TE_pg MU WM WMy MU1 WM1 MIE CHAE. subst falo fahi. clear FAIN.

    replace (Z_to_bv 64 (al_space AL + 137438953472 + 128 * c)) with (Z_to_bv 64 (RIB AL + 128 * c)) by (unfold RIB; reflexivity).
    eapply evt_cut.
    { eapply (rta_B AL AO ra gp (wz A0_TP) F_ fc q c n MM m1 Hc lo s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 (mkPCL (p_nf k) mfa1 (p_au k) (p_mu k) (p_nalloc k) (p_nfreed k) (p_fa k) (p_cnt k) (p_chunks k))
                 (p_nf k + n) j8 j64 j88 j96 j104 j112 jpad junk).
      - clear - Lnf NB TB. unfold tot in TB. lia.
      - exact NB.
      - unfold ri_cells, RIB. cbn [p_nf p_mfa p_au p_mu p_nalloc p_nfreed]. exact RIC1.
      - exact FR1.
      - exact ST1.
      - exact CLO.
      - clear - LO. lia.
      - exact Q16.
      - exact QH.
      - unfold prim_env. exact PRE1.
      - exact GP1.
      - exact PG1.
      - exact MI1. }
    cbv beta. unfold rtaB_post. intros ms2 (b5 & b6 & b7 & b10 & b11 & b12 & b13 & b14 & b15 & b16 & b17 & b28 & b29 & b30 & b31 & m2 & -> & MU2 & WM2 & MI2 & RIC2 & ST2).
    cbn [p_nf p_mfa p_au p_mu p_nalloc p_nfreed p_fa p_cnt p_chunks] in RIC2.
    assert (RIIN : al_space AL + 137438953472 <= RIB AL + 128 * c /\ RIB AL + 128 * c + 128 <= al_space AL + 137438953472 + 4096) by (unfold RIB; clear - Hc; lia).
    set (ria := RIB AL + 128 * c) in *.
    pose proof (u32arr_bound asegs _ _ _ FAA2) as FB2.
    assert (LRC : length (rc_list ws1 (p_nf k) (Z.to_nat n) vals) = length ws1) by (apply rc_list_length; [unfold n; lia| clear - LW1 Lnf NB; lia]).
    pose proof (rw_cells_transport asegs _ m1 m2 _ _ PRE1 MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - RIIN SP1 CLO ACR LO; lia)) as PRE2.
    pose proof (rw_cells_transport asegs _ m1 m2 _ _ TS2 MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - RIIN AP03 TH2 CLO LO; lia)) as TS3.
    pose proof (u32arr_transport asegs _ m1 m2 _ _ FAA2 MU2 WM2 ltac:(cbn [disjoint_from]; rewrite LRC; unfold fa_base, region; clear - RIIN RR LEN1 EFN SP2 CLO LO; lia)) as FAA3.
    pose proof (u32arr_transport asegs _ m1 m2 _ _ CHA2 MU2 WM2 ltac:(cbn [disjoint_from]; clear - RIIN CHL CHH CHBD AP03 TH2 CLO LO; lia)) as CHA3.
    lazymatch type of MU' with munch ?W0 _ _ => assert (MUL : munch W0 m m2) end.
    { eapply munch_trans; [exact MU'|]. eapply munch_weaken; [| exact MU2].
      unfold sub_fp; cbn [outside]. intros xo (O1 & O2 & _). subst ria. unfold RIB in *.
      repeat split; try exact I; intros R; first [apply O1; clear - R LO; lia | apply O2; clear - R; lia]. }
    pose proof (wmono_trans asegs _ _ _ WM' WM2) as WM3. pose proof (wmono_trans asegs _ _ _ WMy' WM2) as WMy3.
    lz_ret. unfold rta_post. cbv zeta. apply evt_done.
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, m2. split; [reflexivity|].
    split; [reflexivity|].
    split; [exact MUL|]. split; [exact WM3|]. split; [exact MI2|]. split; [exact ST2|].
    split; [eapply poison_env_frame; [exact PE| exact MUL| exact WM3| exact AIW]|].
    split; [eapply thread_env_frame; [exact TE| exact MUL| exact WM3| exact TCW]|].
    split; [unfold prim_env; exact PRE2|].
    split; [eapply shvis_wmono; [exact SVE| exact WMy3]|].
    split; [unfold ri_rep; exists j8, j64, j88, j96, j104, j112, jpad; exact RIC2|].
    split.
    { unfold fa_rep. exists (rc_list ws1 (p_nf k) (Z.to_nat n) vals). split; [exact FAA3|]. split; [rewrite LRC; exact LEN1|].
      cbn [return_to_allocator p_fa]. rewrite Lnf. apply rc_list_prefix; [exact FX1| unfold n; rewrite Nat2Z.id; reflexivity|].
      clear - LW1 Lnf NB. unfold n in *. lia. }
    split; [exact CHA3|]. exists ts1. exact TS3.
  Qed.
End RTA2.
