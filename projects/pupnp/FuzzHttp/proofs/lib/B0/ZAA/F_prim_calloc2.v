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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimRefill APrimQ APrimFrame APrimPopLens F_prim_cid F_prim_calloc F_prim_refill ATacFix.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Lemma class_of_cid : forall size, class_of size = (if size <=? 512 then (size + 31) / 32 else cid_code (Z.log2 size) size).
Proof. intros size. unfold class_of, cid_code. destruct (size <=? 512); [reflexivity| cbv zeta; lia]. Qed.

Lemma class_of_range : forall size, 1 <= size <= 65536 -> 1 <= class_of size <= 31.
Proof.
  intros size Hs.
  pose proof (check_from_ok (fun s => (1 <=? class_of s) && (class_of s <=? 31)) (Z.to_nat 65536) 1 ltac:(vm_compute; reflexivity) size ltac:(lia)) as X.
  cbv beta in X. apply andb_true_iff in X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. lia.
Qed.

Lemma set_nth_set_nth : forall {A} (l : list A) i x y, set_nth i x (set_nth i y l) = set_nth i x l.
Proof. induction l as [|h t IH]; intros [|i] x y; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma cache_alloc_refill : forall P c, length (pr_cls P) = 32%nat -> 0 <= c < 32 -> p_cnt (get_cls P c) = 0 -> 0 < max_count c / 2 ->
  cache_alloc P c = cache_alloc (refill_prim P c) c.
Proof.
  intros P c LEN Hc C0 N0. unfold cache_alloc at 2. unfold refill_prim. rewrite get_cls_set_same by assumption.
  unfold cache_alloc, cache_alloc_cls. rewrite C0. cbn [Z.eqb].
  assert (EC : p_cnt (refill (get_cls P c) c) = max_count c / 2) by reflexivity.
  rewrite EC. replace (max_count c / 2 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  cbn [pr_cls pr_calloc pr_cmapped p_mu]. rewrite set_nth_set_nth. f_equal. f_equal. lia.
Qed.

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

Section CA2.
  Context {HC : HasCeiling}.
  Variables (AL : alayout) (E : penv).
  Notation L := (al_thread AL).
  Notation THR := (at_thr (al_thread AL)).
  Notation CACHE := (at_thr (al_thread AL) + CACHE_OFF).

  #[using="Type"] Lemma calloc_tail : forall (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32)
        (m : mem) (H H1 : word -> bool) (q lo c : Z) (P P1 : prim) (m1 : mem)
        (x1 t0 t1 t2 a4 a5 a6 a7 xs2 xs3 xs4 t3 t4 t5 t6 : word),
    alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q - 48 -> q <= 2^47 -> 1 <= c <= 31 ->
    cache_alloc P c = cache_alloc P1 c ->
    H1 = (if p_cnt (get_cls P c) =? 0 then H_gfa AL c (get_cls P c) (max_count c / 2) H else H) ->
    0 < p_cnt (get_cls P1 c) ->
    munch (prim_W AL lo q c (get_cls P c) (get_cls P1 c)) m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
    shvis H1 m1 -> poison_env E m1 -> thread_env L m1 -> RPRIM AL P1 m1 -> prim_ok P1 ->
    stk asegs m1 lo (q - 48) -> rw_cells asegs m1 (q - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    evt asegs (lzk H1 (Ret (Ok tt)) (cache_alloc_post AL E ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc q lo c P H m))
      (MS (mkR x1 (wz (q - 48)) gp (wz A0_TP) t0 t1 t2 (wz c) (wz (CACHE + 80 * c)) (wz INSTANCE) (wz CACHE) (wz (p_cnt (get_cls P1 c))) (wz 8) a4 a5 a6 a7
               xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x37e94) fc None m1 (seg_rom asegs)).
  Proof.
    intros until t6. intros AO LOH CLO LO QH Hc ECA EH1 CNT1 MU1 WM1 MI1 SV1 PE1 TE1 RP1 POK1 ST1 FR1.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & _).
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
    layout_apart_fact AO 0%nat 3%nat LP03.

    destruct (RPRIM_pop AL AO P1 m1 c RP1 POK1 Hc CNT1) as (INI & V0 & VAU & VAL & AUF & PENV & PCL & (ws & ARR & LWS & NTHW) & STATS & FCH & CLOSE).
    set (k1 := get_cls P1 c) in *. set (cnt := p_cnt k1) in *.
    set (v := nth (Z.to_nat (cnt - 1)) (p_chunks k1) 0) in *.
    assert (WFk : 1 <= cnt <= 16).
    { destruct RP1 as (_ & _ & CLS & _). destruct (CLS c Hc) as ((_ & _ & CR & _) & _). fold k1 in CR. fold cnt in CR.
      pose proof (max_count_range c Hc) as (MR & _). lia. }
    pose proof (class_size_pos c Hc) as CS.
    assert (NTH : nth_error ws (Z.to_nat (cnt - 1)) = Some (wz v)) by (rewrite <- NTHW; apply nth_error_nth'; rewrite LWS; lia).
    unfold pcl_addr in PCL, ARR. unfold prim_env in PENV.
    apply (proj1 (rw_cells_app asegs m1 724728 [_] _)) in PENV as [PENV0 _].
    replace (THR + CSTATS_OFF + 16) with (CACHE + 2576) in STATS by lia.
    apply (proj1 (rw_cells_app asegs m1 (CACHE + 2576) [_] [_])) in STATS as [STATS0 STATS1]. cbn [cells_size csize Nat.add] in STATS1.
    unfold prim_W in MU1.
    pose proof (munch_refl [(CACHE + 80 * c, CACHE + 80 * c + 4); (CACHE + 2576, CACHE + 2584)] m1) as MUc. pose proof (wmono_refl asegs m1) as WMc.
    hide STATS1. hide T1. hide T5. hide T6. hide SPM.
    assert (CB8 : CACHE mod 8 = 0) by (clear - T7; Z.div_mod_to_equations; lia).
    hide T7.
    call (calloc_hit ra gp (wz A0_TP) F_ fc q CACHE m1 lo c cnt (class_size c) (pr_calloc P1) (al_space AL) v (wz (max_count c)) ws
            _ _ _ _ _ _ _ _ _ _ _ s5 s6 s7 s8 s9 s10 s11 _ _ _ _ s0 s1 s2 s3 s4).
    1: assumption.
    1: exact Hc.
    1: exact WFk.
    1: clear - CS; lia.
    1: clear - SP1; lia.
    1: clear - SP5; lia.
    1: clear - V0 VAU AUF CS; lia.
    1: exact CB8.
    1: clear - T3; lia.
    1: clear - T3; lia.
    1: clear - T4 CLO; lia.
    1: exact CLO.
    1: exact LO.
    1: exact QH.
    1: exact PCL.
    1: exact ARR.
    1: exact LWS.
    1: exact NTH.
    1: exact STATS0.
    1: exact PENV0.
    1: exact FR1.
    1: exact ST1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
    unhide STATS1. unhide T1. unhide T5.
    pose proof (rw_cells_transport asegs _ m1 mF _ _ STATS1 MUc WMc ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - Hc; lia)) as STATS1F.
    assert (STF : rw_cells asegs mF (THR + CSTATS_OFF + 16) [C8 (wz (pr_calloc P1 + class_size c)); C8 (wz (pr_cmapped P1))]).
    { replace (THR + CSTATS_OFF + 16) with (CACHE + 2576) by lia. apply (proj2 (rw_cells_app asegs mF (CACHE + 2576) [_] [_])). split; [exact PC1| exact STATS1F]. }
    assert (MUc' : munch [(pcl_addr AL c, pcl_addr AL c + 4); (THR + CSTATS_OFF + 16, THR + CSTATS_OFF + 24)] m1 mF).
    { refine (munch_weaken _ _ _ _ _ MUc). unfold pcl_addr. clear. sub_fp_solve. }
    destruct (CLOSE mF MUc' WMc PC STF) as (RPF & POKF & EV). clear CLOSE MUc'.

    pose proof RP1 as (LEN1 & _).
    assert (EKF : get_cls (fst (cache_alloc P1 c)) c = pop_cls k1).
    { rewrite (cache_alloc_hit P1 c CNT1). cbn [fst]. apply get_cls_set_same; [exact LEN1| lia]. }

    pose proof (region_range AL c Hc) as [R1 R2].
    assert (FCHF : free_chunk AL mF c v).
    { assert (E8 : exists v8 z8, 16 * v = 8 * v8 /\ class_size c = 8 * z8 /\ 0 <= v8 /\ 0 < z8).
      { pose proof (class_size_mod16 c Hc) as C16. exists (2 * v), (class_size c / 8). split; [lia|]. split; [clear - C16; Z.div_mod_to_equations; lia|]. split; [lia| clear - CS C16; Z.div_mod_to_equations; lia]. }
      destruct E8 as (v8 & z8 & E1 & E2 & V80 & Z80).
      assert (SZD : class_size c / 8 = z8) by (rewrite E2, Z.mul_comm, Z.div_mul by lia; reflexivity).
      pose proof (REG_mod8 AL AO c) as R8.
      pose proof (sh_le 0 (region AL c + 16 * v) ltac:(lia)) as L1. change (sh 0) with 2147450880 in L1.
      pose proof (sh_le (region AL c + 8 * (v8 + z8)) (2^47) ltac:(lia)) as L2. change (sh (2^47)) with 17594333495296 in L2. rewrite (sh_off8 _ _ R8) in L2.
      eapply free_chunk_frame; [exact FCH| exact MUc| exact WMc| exact Hc| |].
      - cbn [disjoint_from]. clear - LP03 R1 R2 V0 VAU AUF Hc T4. lia.
      - rewrite SZD. rewrite E1, (sh_off8 _ _ R8) in L1 |- *. cbn [disjoint_from]. clear - L1 L2 T3 T4 Hc. lia. }
    lz_ret. apply evt_done. unfold cache_alloc_post. cbv zeta. rewrite ECA, EV. fold k1.
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, mF.
    split; [reflexivity|]. split; [exact EH1|].
    split. { rewrite EKF. exact MU1. }
    split; [exact WM1|]. split; [assumption|]. split; [exact POST|].
    split. { eapply poison_env_frame; [exact PE1| exact MUc| exact WMc|]. clear - T3 T4 Hc. env_clear. }
    split. { eapply thread_env_frame; [exact TE1| exact MUc| exact WMc|]. clear - T1 T2 T3 T4 T5 Hc. env_clear. }
    split; [eapply shvis_wmono; [exact SV1| exact WMc]|].
    split; [exact RPF|]. split; [exact POKF|]. split; [exact FCHF|].
    rewrite EKF. unfold pop_cls. cbn [p_au]. split; [exact V0|]. split; [exact VAU| exact VAL].
  Qed.

  #[using="Type"] Theorem cache_alloc_spec : cache_alloc_stmt AL E.
  Proof.
    unfold cache_alloc_stmt.
    intros ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m H q lo size P
           AO MI MC SV PE TE ST LOH CLO LO QH Q16 SZ RP POK RB CA0 CM0 CMB.
    cbv zeta. set (c := class_of size) in *.
    unfold cache_alloc_entry, CALLOC_STACK, REFILL_STACK, POP_STACK, MF_STACK in *.
    pose proof (class_of_range size SZ) as Hc. fold c in Hc.
    pose proof (class_of_cid size) as Hcid. fold c in Hcid.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & _).
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
    layout_apart_fact AO 0%nat 3%nat LP03.
    set (k := get_cls P c) in *.
    pose proof (max_count_range c Hc) as (MR & _).
    pose proof (munch_refl [(q - 48, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    lz_go.
    call (calloc_A ra gp (wz A0_TP) F_ fc q CACHE m lo size c t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6);
      [ exact ST | exact CLO | clear - LO; lia | exact QH | exact MI | exact SZ | clear - T3 T4 ACR; lia | exact Hcid | exact Hc | ].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    rename PC into FRA, POST into STA, MI0 into MIA.
    assert (SHS : sh (al_space AL + K_SPACE + 4096) <= 17594333495296) by (unfold sh, SHADOW_OFF; clear - SP5; Z.div_mod_to_equations; lia).
    assert (RPA : RPRIM AL P mA).
    { apply (RPRIM_frame AL AO P _ m mA RP MU WM). unfold prim_clear.
      repeat (apply Forall_cons || apply Forall_nil). left. unfold prim_out. cbn [fst snd]. clear - LO CLO ACR T3 T4 SP2 SHS. repeat split; lia. }
    assert (SVA : shvis H mA) by (eapply shvis_wmono; [exact SV| exact WM]).
    assert (PEA : poison_env E mA) by (eapply poison_env_frame; [exact PE| exact MU| exact WM|]; clear - LO CLO ACR; env_clear).
    assert (TEA : thread_env (al_thread AL) mA) by (eapply thread_env_frame; [exact TE| exact MU| exact WM|]; clear - LO CLO ACR T1 T2 T3 T4 T5; env_clear).
    hide T1. hide T5. hide T6. hide T7. hide SPM.
    pose proof RPA as (LENA & _ & CLSA & _). destruct (CLSA c Hc) as (WFk & _ & (PCL & _) & _). fold k in WFk, PCL. clear CLSA.
    assert (CNTR : 0 <= p_cnt k <= 16) by (destruct WFk as (_ & _ & CR & _); clear - CR MR; lia).
    unfold pcl_addr in PCL.
    remember (CACHE + 80 * c) as pcb eqn:Hpcb in *.
    zstep.
    rewrite (sx32_lit (p_cnt k)) by lia.
    clear PCL.
    zstep. if_cases KC; zify_cond KC.
    2: {
      replace (p_cnt k =? 0) with false by (symmetry; apply Z.eqb_neq; exact KC). unfold t_none.
      subst pcb.
      eapply (calloc_tail ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m H H q lo c P P mA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AO LOH CLO ltac:(clear - LO; lia) QH Hc eq_refl).
      - fold k. replace (p_cnt k =? 0) with false by (symmetry; apply Z.eqb_neq; exact KC). reflexivity.
      - fold k. clear - KC CNTR. lia.
      - fold k. refine (munch_weaken _ _ _ _ _ MU). unfold prim_W. clear - LO. sub_fp_solve.
      - exact WM.
      - exact MIA.
      - exact SVA.
      - exact PEA.
      - exact TEA.
      - exact RPA.
      - exact POK.
      - exact STA.
      - exact FRA. }

    rewrite KC. cbn [Z.eqb]. rewrite <- (ebind_ret_r (t_refill AL c k)).
    do 7 zstep.
    zstep.
    subst pcb.
    pose proof (refill_wf c k Hc WFk (proj1 RB) (proj2 RB) KC) as WFR.
    pose proof (munch_refl [(lo, q - 48); (ri_addr AL c, ri_addr AL c + 128);
       (fa_base AL c + 4 * Z.min (p_nf k) (p_nf (refill k c)), fa_base AL c + p_mfa (refill k c));
       (region AL c + p_mu k, region AL c + p_mu (refill k c));
       (sh (region AL c + p_mu k), sh (region AL c + p_mu (refill k c))); (sh (fa_base AL c + p_mfa k), sh (fa_base AL c + p_mfa (refill k c)));
       (CACHE, CACHE + 2592); (THR + TSTATS_OFF, THR + TSTATS_OFF + 368)] mA) as MUx.
    pose proof (wmono_refl asegs mA) as WMx.
    lazymatch type of MUx with munch ?Wx _ _ => apply (munch_extend _ Wx) in MU; cbn [List.app] in MU end.
    hide FRA.
    callAu (refill_spec AL E _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc mA H (q - 48) lo c P AO MIA) unfolding (fun h => unfold prim_W in h);
      [ assumption | exact SVA | exact PEA | exact TEA | exact STA | exact LOH | exact CLO
      | unfold REFILL_STACK, POP_STACK, MF_STACK; clear - LO; lia | clear - QH; lia | clear - Q16; Z.div_mod_to_equations; lia
      | exact Hc | exact RPA | exact POK | exact KC | exact RB | exact CA0 | exact CM0 | exact CMB | ].
    destruct r.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mR end.
    rename PC into STR, PC0 into PER, PC1 into TER, PC2 into SVR, PC3 into RPR, POST into POKR, MI into MIR.

    unhide FRA.
    assert (FRR : rw_cells asegs mR (q - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { destruct WFR as (_ & _ & _ & _ & MFAr & _ & AUr & MUFr & _).
      pose proof (region_range AL c Hc) as [R1 R2].
      pose proof (sh_le (region AL c + p_mu (refill k c)) (2^47) ltac:(lia)) as U1. change (sh (2^47)) with 17594333495296 in U1.
      pose proof (sh_le (fa_base AL c + p_mfa (refill k c)) (2^47) ltac:(unfold fa_base; lia)) as U2. change (sh (2^47)) with 17594333495296 in U2.
      eapply rw_cells_transport; [exact FRA| exact MUx| exact WMx|]. cbn [disjoint_from cells_size csize Nat.add].
      unfold ri_addr, RIB, fa_base in *. clear - LO CLO LOH ACR SP2 R1 R2 Hc T4 U1 U2 MFAr MUFr. lia. }
    clear FRA MUx WMx.

    pose proof RPR as (_ & _ & CLSR & _). destruct (CLSR c Hc) as (_ & _ & (PCLR & _) & _). clear CLSR.
    assert (EKR : get_cls (refill_prim P c) c = refill k c) by (unfold refill_prim; apply get_cls_set_same; [exact LENA| lia]).
    assert (ECR : p_cnt (refill k c) = max_count c / 2) by reflexivity.
    rewrite EKR, ECR in PCLR. unfold pcl_addr in PCLR.
    remember (CACHE + 80 * c) as pcb eqn:Hpcb in *.
    zstep. if_false_z.
    zstep.
    rewrite (sx32_lit (max_count c / 2)) by (clear - MR; Z.div_mod_to_equations; lia).
    clear PCLR.
    do 3 zstep.
    zstep.
    subst pcb.
    replace (Z_to_bv 64 (max_count c / 2)) with (wz (p_cnt (get_cls (refill_prim P c) c))) by (rewrite EKR, ECR; reflexivity).
    assert (N0 : 0 < max_count c / 2) by (clear - MR; Z.div_mod_to_equations; lia).
    eapply (calloc_tail ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m H _ q lo c P (refill_prim P c) mR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AO LOH CLO ltac:(clear - LO; lia) QH Hc
              (cache_alloc_refill P c LENA ltac:(lia) KC N0)).
    - fold k. rewrite KC. reflexivity.
    - rewrite EKR, ECR. exact N0.
    - rewrite EKR. fold k. refine (munch_weaken _ _ _ _ _ MU). unfold prim_W. clear - LO. sub_fp_solve.
    - exact WM.
    - exact MIR.
    - exact SVR.
    - exact PER.
    - exact TER.
    - exact RPR.
    - exact POKR.
    - exact STR.
    - exact FRR.
  Qed.
End CA2.
