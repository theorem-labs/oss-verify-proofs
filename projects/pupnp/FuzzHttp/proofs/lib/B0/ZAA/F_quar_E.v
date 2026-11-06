(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep SysMm.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require InitStack.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout ATacA PEnv LJ LJU APrim APrimLem APrimPop APrimRefill APrimSpec APrimSpec2 APrimQ AFrame ASec AQuar F_quar_Ep.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition enqueue_entry : Z := 0x37afc.
Definition ENQ_STACK : Z := 64 + REFILL_STACK.

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

Section ENQ.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv).
Notation L := (al_thread AL).
Notation THR := (at_thr (al_thread AL)).
Notation TQ := (at_thr (al_thread AL) + TQ_OFF).
Notation CACHE := (at_thr (al_thread AL) + CACHE_OFF).

Definition enq_P1 (P : prim) : prim := if p_cnt (get_cls P K_BCLASS) =? 0 then refill_prim P K_BCLASS else P.
Definition enq_prim (P : prim) (l : list qbatch) : prim * Z :=
  if need_batch l then cache_alloc (enq_P1 P) K_BCLASS else (P, 0).
Definition enq_refills (P : prim) (l : list qbatch) : bool := need_batch l && (p_cnt (get_cls P K_BCLASS) =? 0).
Definition t_enq (P : prim) (l : list qbatch) : itree nodeL (exc unit) :=
  if enq_refills P l then t_refill AL K_BCLASS (get_cls P K_BCLASS) else Ret (Ok tt).
Definition H_enq (P : prim) (l : list qbatch) (H : word -> bool) : word -> bool :=
  if enq_refills P l then H_gfa AL K_BCLASS (get_cls P K_BCLASS) (max_count K_BCLASS / 2) H else H.

Hypothesis RF : refill_stmt AL E.
Hypothesis RP : RPRIM_pop_stmt AL.
Hypothesis RPF : RPRIM_frame_stmt AL.

Variables (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (q lo : Z) (m : mem) (H : word -> bool) (P : prim) (l : list qbatch) (ch : qchunk) (hs : list (Z * Z)).

Notation K24 := (get_cls P K_BCLASS).
Notation PN := (fst (enq_prim P l)).
Notation VN := (snd (enq_prim P l)).

Definition enq_W : list (Z * Z) :=
  (if need_batch l then prim_W AL lo q K_BCLASS K24 (get_cls (enq_P1 P) K_BCLASS) else [(lo, q)])
  ++ [(TQ, TQ + 32)] ++ qlast_iv AL l
  ++ (if need_batch l then [(region AL K_BCLASS + 16 * VN, region AL K_BCLASS + 16 * VN + Q_BBYTES)] else []).

Definition enqueue_post : unit -> (word -> bool) -> machine_state -> Prop :=
  fun _ H' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ H' = H_enq P l H
    /\ munch enq_W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ poison_env E m' /\ thread_env L m' /\ shvis H' m'
    /\ RPRIM AL PN m' /\ prim_ok PN
    /\ held_ok PN (if need_batch l then (K_BCLASS, VN) :: hs else hs)
    /\ qcache_rep AL m' TQ (q_enq l ch VN)
    /\ (need_batch l = true -> pclass_wf K_BCLASS (get_cls (enq_P1 P) K_BCLASS)).

#[using="Type"] Lemma qlast_iv_space : forall (l0 : list qbatch) (bound : Z), Forall (qb_in bound) l0 -> bound <= FA_OFF ->
  Forall (fun iv : Z * Z => al_space AL + K_REGION <= fst iv /\ snd iv <= al_space AL + K_SPACE) (qlast_iv AL l0).
Proof.
  intros l0 bound FI BF. unfold qlast_iv. destruct (rev l0) as [|b r] eqn:ER; [constructor|].
  constructor; [| constructor]. cbn [fst snd].
  assert (IN : In b l0) by (apply in_rev; rewrite ER; left; reflexivity).
  pose proof (proj1 (Forall_forall _ _) FI b IN) as (V0 & _ & VB). unfold qb_addr, region. lia.
Qed.

#[using="RP RPF"] Lemma enq_new_tail : forall (P1 : prim) (H1 : word -> bool) (m1 : mem) (junk8 : list byte)
    (rra x5 x6 x7 r0 r1 a2 a6 a7 r2 r3 r4 r5 x28 x29 x30 x31 : word),
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q - 64 -> q <= 2^47 ->
  need_batch l = true -> enq_P1 P = P1 -> H_enq P l H = H1 ->
  munch (prim_W AL lo q K_BCLASS K24 (get_cls P1 K_BCLASS)) m m1 -> wmono asegs m m1 ->
  poison_env E m1 -> thread_env L m1 -> shvis H1 m1 ->
  RPRIM AL P1 m1 -> prim_ok P1 -> 0 < p_cnt (get_cls P1 K_BCLASS) ->
  held_ok P1 hs -> incl (map (fun b => (K_BCLASS, qb_v b)) l) hs -> List.NoDup (map qb_v l) ->
  Z.of_nat (length l) < 2^32 -> qchunk_wf ch ->
  qcache_rep AL m1 TQ l -> mem_inv asegs m1 -> stk asegs m1 lo (q + -64) ->
  rw_cells asegs m1 (q + -64) [CB 8 junk8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  evt asegs (lzk H1 (Ret (Ok tt)) enqueue_post)
    (MS (mkR rra (wz (q + -64)) gp (wz A0_TP) x5 x6 x7 r0 r1 (wz TQ) (wz CACHE) a2 (wz (qc_hdr AL ch)) (wz (qc_n ch))
             (wz (p_cnt (get_cls P1 K_BCLASS))) a6 a7 r2 r3 r4 r5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz 0x37b3c) fc None m1 (seg_rom asegs)).
Proof.
  intros until x31. intros AO HLO CLO LOQ QHI NB EP1 EH1 MU1 WM1 PE1 TE1 SV1 RPR1 POK1 CNT1 HOK1 INC NDV LEN32 CHW QC1 MI1 ST1 FR1.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof AO as (_ & _ & _ & TL & _). pose proof TL as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & _).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
  layout_apart_fact AO 0%nat 3%nat LP03. layout_apart_fact AO 0%nat 2%nat LP02.
  pose proof (held_qb_in P1 hs l HOK1 INC) as QBI.
  assert (BF : p_au (get_cls P1 K_BCLASS) <= FA_OFF).
  { destruct RPR1 as (_ & _ & CLS & _). destruct (CLS K_BCLASS ltac:(lia)) as ((_ & _ & _ & _ & _ & _ & AU & MUF & _) & _). lia. }
  pose proof (qlast_iv_space l _ QBI BF) as QLS.

  assert (HOKN : held_ok (fst (cache_alloc P1 K_BCLASS)) ((K_BCLASS, snd (cache_alloc P1 K_BCLASS)) :: hs)).
  { destruct RPR1 as (LEN1 & _ & CLS1 & _). destruct (CLS1 K_BCLASS ltac:(lia)) as (WF1 & _).
    apply cache_alloc_held_ok; [exact HOK1| lia| exact LEN1| exact WF1| exact CNT1]. }
  eapply evt_cut.
  { apply (enq_pop AL RP RPF ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc q lo l ch hs P1 m1 junk8 rra x5 x6 x7 r0 r1 a2 a6 a7 r2 r3 r4 r5 x28 x29 x30 x31
             AO HLO CLO LOQ QHI RPR1 POK1 CNT1 HOK1 INC NDV LEN32 CHW NB QC1 MI1 ST1 FR1). }
  intros ms' (t0 & t1 & t2 & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3 & t4 & t5 & t6 & m' & -> & MUp & WMp & MIp & STp & RPRp & POKp & QCp).
  set (PN1 := fst (cache_alloc P1 K_BCLASS)) in *. set (v := snd (cache_alloc P1 K_BCLASS)) in *.
  assert (VF : 0 <= v /\ 16 * v + Q_BBYTES <= FA_OFF).
  { destruct HOKN as [_ HF]. pose proof (Forall_inv HF) as (_ & V0 & VB & _). cbn [fst snd] in V0, VB. change (class_size K_BCLASS) with Q_BBYTES in VB.
    destruct RPRp as (_ & _ & CLS & _). destruct (CLS K_BCLASS ltac:(lia)) as ((_ & _ & _ & _ & _ & _ & AU & MUF & _) & _). lia. }
  assert (ERG : region AL K_BCLASS = al_space AL + 24 * K_REGION) by reflexivity.
  lz_ret. apply evt_done. unfold enqueue_post, enq_W, enq_prim. rewrite NB, EP1. cbn [fst snd]. fold PN1. fold v.
  exists t0, t1, t2, a0', a1', a2', a3', a4', a5', a6', a7', t3, t4, t5, t6, m'.
  split; [reflexivity|]. split; [symmetry; exact EH1|].
  split.
  { apply (munch_trans _ m m1 m').
    - apply munch_extend. exact MU1.
    - refine (munch_weaken _ _ _ _ _ MUp). intros x Hx. unfold enq_popW. fold v.
      apply outside_app in Hx as [HxP Hx]. apply outside_app in Hx as [HxT Hx].
      apply outside_app. split; [| exact Hx].
      unfold prim_W in HxP. cbn [outside] in HxP, HxT |- *. clear - HxP HxT LOQ. lia. }
  split; [exact (wmono_trans asegs m m1 m' WM1 WMp)|]. split; [exact MIp|]. split; [exact STp|].
  split.
  { eapply (poison_env_frame E _ m1 m' PE1 MUp WMp). unfold above_img, enq_popW. fold v.
    apply Forall_app. split; [repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; clear - LOQ CLO ACR T3; lia|].
    apply Forall_app. split; [eapply Forall_impl; [| exact QLS]; intros [a b] [Ha Hb]; cbn [fst snd] in *; clear - Ha SP1; lia|].
    repeat (apply Forall_cons || apply Forall_nil). cbn [fst snd]. clear - VF ERG SP1. lia. }
  split.
  { eapply (thread_env_frame L _ m1 m' TE1 MUp WMp). unfold thread_clear, enq_popW. fold v.
    apply Forall_app. split; [repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; clear - LOQ CLO ACR T1 T2 T3 T4 T5; repeat split; lia|].
    apply Forall_app. split; [eapply Forall_impl; [| exact QLS]; intros [a b] [Ha Hb]; cbn [fst snd] in *; clear - Ha Hb SP1 LP02 LP03 T1 T3; repeat split; lia|].
    repeat (apply Forall_cons || apply Forall_nil). cbn [fst snd]. clear - VF ERG SP1 LP02 LP03 T1 T3. repeat split; lia. }
  split; [eapply shvis_wmono; [exact SV1| exact WMp]|].
  split; [exact RPRp|]. split; [exact POKp|]. split; [exact HOKN|]. split; [exact QCp|].
  intros _. destruct RPR1 as (_ & _ & CLS1 & _). exact (proj1 (CLS1 K_BCLASS ltac:(lia))).
Qed.

#[using="RF RP RPF"] Lemma enq_new : forall (m0 : mem) (junk8 : list byte) (x5 x6 x7 a2 a5 a6 a7 x28 x29 x30 x31 : word),
  alayout_ok AL -> shvis H m -> poison_env E m -> thread_env L m ->
  0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q - ENQ_STACK -> q <= 2^47 -> q mod 16 = 0 ->
  RPRIM AL P m -> prim_ok P -> refill_budget K_BCLASS K24 ->
  0 <= pr_calloc P -> 0 <= pr_cmapped P -> pr_cmapped P + K_REGION < 2^63 ->
  held_ok P hs -> incl (map (fun b => (K_BCLASS, qb_v b)) l) hs -> List.NoDup (map qb_v l) ->
  Forall (fun b => 1 <= qb_count b <= Q_BATCH) l -> Z.of_nat (length l) < 2^32 ->
  qcache_rep AL m TQ l -> qchunk_wf ch ->
  need_batch l = true ->
  munch [(q - 64, q)] m m0 -> wmono asegs m m0 -> mem_inv asegs m0 -> stk asegs m0 lo (q + -64) ->
  rw_cells asegs m0 (q + -64) [CB 8 junk8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  evt asegs (lzk H (t_enq P l) enqueue_post)
    (MS (mkR ra (wz (q + -64)) gp (wz A0_TP) x5 x6 x7 s0 s1 (wz TQ) (wz CACHE) a2 (wz (qc_hdr AL ch)) (wz (qc_n ch)) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz 0x37b34) fc None m0 (seg_rom asegs)).
Proof.
  intros until x31. intros AO SV PE TE HLO CLO LOQ QHI Q16 RPR POK RB CA0 CM0 CM1 HOK INC NDV CNT LEN32 QC CHW NB MU0 WM0 MI0 ST0 FR0.
  unfold ENQ_STACK, REFILL_STACK, POP_STACK, MF_STACK in *.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof AO as (_ & _ & _ & TL & _). pose proof TL as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & _).
  destruct QC as [TQC QL].
  pose proof (held_qb_in P hs l HOK INC) as QBI.
  assert (AUF : p_au K24 <= FA_OFF /\ p_au K24 mod 8 = 0).
  { destruct RPR as (_ & _ & CLS & _). destruct (CLS K_BCLASS ltac:(lia)) as ((_ & _ & _ & _ & _ & _ & AU & MUF & _ & AUM & _) & _).
    split; [lia|]. change (class_size K_BCLASS) with 8192 in AUM. clear - AUM. Z.div_mod_to_equations. lia. }
  destruct AUF as [BF B8].
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
  layout_apart_fact AO 0%nat 3%nat LP03. layout_apart_fact AO 0%nat 2%nat LP02.
  assert (PE0 : poison_env E m0).
  { eapply (poison_env_frame E _ m _ PE MU0 WM0). unfold above_img. clear - LOQ CLO ACR.
    repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; lia. }
  assert (TE0 : thread_env L m0).
  { eapply (thread_env_frame L _ m _ TE MU0 WM0). unfold thread_clear. clear - LOQ CLO ACR T1 T2 T3 T4 T5.
    repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; repeat split; lia. }
  assert (SV0 : shvis H m0) by (eapply shvis_wmono; [exact SV| exact WM0]).
  assert (RPR0 : RPRIM AL P m0).
  { apply (RPF P _ m _ RPR MU0 WM0). unfold prim_clear.
    assert (SHS : sh (al_space AL + K_SPACE + 4096) <= 17594333495296) by (unfold sh, SHADOW_OFF; clear - SP5; Z.div_mod_to_equations; lia).
    repeat (apply Forall_cons || apply Forall_nil). left. unfold prim_out. cbn [fst snd]. clear - LOQ CLO ACR T3 T4 SP2 SHS. repeat split; lia. }
  assert (TQC0 : rw_cells asegs m0 TQ [C8 (wz (Z.of_nat (length l))); C8 (wz (qfirst AL l)); C8 (wz (qlast AL l)); C8 (wz (qbytes l))]).
  { eapply rw_cells_transport; [exact TQC| exact MU0| exact WM0|]. cbn [disjoint_from cells_size csize]. clear - LOQ CLO ACR T3 T4. simpl_sizes. lia. }

  pose proof RPR0 as (_ & PENV0 & CLS0 & CST0 & _).
  destruct (CLS0 K_BCLASS ltac:(lia)) as (WF24 & _ & (PCL24 & ARR24) & _).
  unfold pcl_addr in PCL24, ARR24. replace (THR + CACHE_OFF + 80 * K_BCLASS) with (CACHE + 1920) in PCL24, ARR24 by lia.
  replace (CACHE + 1920) with (THR + 2128) in PCL24, ARR24 by lia. replace (THR + 2128 + 16) with (THR + 2144) in ARR24 by lia.
  zstep.
  assert (CNTR : 0 <= p_cnt K24 <= 2) by (destruct WF24 as (_ & _ & CR & _); change (max_count 24) with 2 in CR; exact CR).
  rewrite (sx32_lit (p_cnt K24)) by lia.
  zstep. if_cases KC; zify_cond KC.
  {
    assert (ER : enq_refills P l = true) by (unfold enq_refills; rewrite NB, KC; reflexivity).
    assert (EP1 : enq_P1 P = refill_prim P K_BCLASS) by (unfold enq_P1; rewrite KC; reflexivity).
    unfold t_enq. rewrite ER. rewrite <- (ebind_ret_r (t_refill AL K_BCLASS K24)).
    do 12 zstep.
    zstep.
    replace (Z_to_bv 64 (THR + 2128)) with (wz (pcl_addr AL K_BCLASS)) by (unfold pcl_addr; f_equal; lia).
    clear PCL24 ARR24 CST0 PENV0 CLS0.

    pose proof (APrimRefill.refill_wf K_BCLASS K24 ltac:(lia) WF24 (proj1 RB) (proj2 RB) KC) as WFR.
    assert (KR : 0 <= p_nf (refill K24 K_BCLASS) /\ 0 <= p_mfa (refill K24 K_BCLASS) <= K_FA_SIZE /\ 0 <= p_mu (refill K24 K_BCLASS) <= FA_OFF).
    { destruct WFR as (Lnf' & _ & _ & _ & MFA' & _ & AU' & MUF' & _). lia. }
    assert (KO : 0 <= p_nf K24 /\ 0 <= p_mfa K24 <= K_FA_SIZE /\ 0 <= p_mu K24 <= FA_OFF).
    { destruct WF24 as (Lnf' & _ & _ & _ & MFA' & _ & AU' & MUF' & _). lia. }
    assert (ERI : ri_addr AL K_BCLASS = al_space AL + K_SPACE + 3072) by reflexivity.
    assert (ERG : region AL K_BCLASS = al_space AL + 24 * K_REGION) by reflexivity.
    assert (EFA : fa_base AL K_BCLASS = al_space AL + 24 * K_REGION + FA_OFF) by reflexivity.
    assert (SHB : forall x, al_space AL <= x <= al_space AL + K_SPACE -> 2147450880 <= sh x <= 17594333495296)
      by (intros x Hx; unfold sh, SHADOW_OFF; clear - Hx SP1 SP5; Z.div_mod_to_equations; lia).
    pose proof (SHB (region AL K_BCLASS + p_mu K24) ltac:(clear - ERG KO; lia)) as SHB1.
    pose proof (SHB (region AL K_BCLASS + p_mu (refill K24 K_BCLASS)) ltac:(clear - ERG KR; lia)) as SHB2.
    pose proof (SHB (fa_base AL K_BCLASS + p_mfa K24) ltac:(clear - EFA KO; lia)) as SHB3.
    pose proof (SHB (fa_base AL K_BCLASS + p_mfa (refill K24 K_BCLASS)) ltac:(clear - EFA KR; lia)) as SHB4.
    clear SHB.
    callAu (RF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 H (q + -64) lo K_BCLASS P AO MI0) unfolding (fun h => unfold prim_W in h);
      [ assumption | exact SV0 | exact PE0 | exact TE0 | exact ST0 | exact HLO | exact CLO
      | unfold REFILL_STACK, POP_STACK, MF_STACK; clear - LOQ; lia | clear - QHI; lia | clear - Q16; Z.div_mod_to_equations; lia | lia
      | exact RPR0 | exact POK | exact KC | exact RB | exact CA0 | exact CM0 | exact CM1 | ].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mR end.
    rename PC into STR, PC0 into PER, PC1 into TER, PC2 into SVR, PC3 into RPRR, POST into POKR, MI into MIR.
    pose proof RPRR as (LENR & _ & CLSR & _). destruct (CLSR K_BCLASS ltac:(lia)) as (_ & _ & (PCLR & _) & _). clear CLSR.
    assert (EKR : get_cls (refill_prim P K_BCLASS) K_BCLASS = refill K24 K_BCLASS).
    { unfold refill_prim. apply get_cls_set_same; [destruct RPR as (LEN0 & _); exact LEN0| lia]. }
    assert (ECR : p_cnt (refill K24 K_BCLASS) = 1) by reflexivity.
    rewrite EKR, ECR in PCLR.
    zstep.
    zstep. if_false_z.
    do 3 zstep.
    zstep.
    do 2 zstep.
    rewrite (sx32_lit 1) by lia. destruct r.
    replace (Z_to_bv 64 1) with (wz (p_cnt (get_cls (refill_prim P K_BCLASS) K_BCLASS))) by (rewrite EKR, ECR; reflexivity).
    assert (SHS1 : sh (al_space AL + K_SPACE) <= 17594333495296) by (unfold sh, SHADOW_OFF; clear - SP5; Z.div_mod_to_equations; lia).
    assert (SHS0 : 2147450880 <= sh (al_space AL)) by (unfold sh, SHADOW_OFF; clear - SP1; Z.div_mod_to_equations; lia).
    assert (AU24 : 0 <= p_au K24 <= p_mu K24 /\ p_au K24 mod 16 = 0).
    { destruct WF24 as (_ & _ & _ & _ & _ & _ & AU & _ & _ & AUM & _). split; [exact AU|].
      change (class_size K_BCLASS) with 8192 in AUM. clear - AUM. Z.div_mod_to_equations. lia. }
    apply (enq_new_tail (refill_prim P K_BCLASS) _ mR junk8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AO HLO CLO ltac:(clear - LOQ; lia) QHI NB EP1).
    - unfold H_enq. rewrite ER. reflexivity.
    - rewrite EKR. refine (munch_weaken _ _ _ _ _ MU0). unfold prim_W. clear - LOQ. sub_fp_solve.
    - exact WM0.
    - exact PER.
    - exact TER.
    - exact SVR.
    - exact RPRR.
    - exact POKR.
    - rewrite EKR, ECR. lia.
    -
      apply (held_ok_mono P _ hs HOK). intros c v0 Hin.
      destruct HOK as [_ HF]. pose proof (proj1 (Forall_forall _ _) HF _ Hin) as (Hc & _). cbn [fst] in Hc.
      destruct (Z.eq_dec c K_BCLASS) as [->|NE].
      + rewrite EKR. split; [apply refill_au; [lia| exact (proj2 (proj1 AU24))]|].
        intros X. apply (refill_free K24 K_BCLASS v0 ltac:(lia) (proj2 AU24) X).
      + assert (EO : get_cls (refill_prim P K_BCLASS) c = get_cls P c).
        { unfold refill_prim, get_cls. cbn [pr_cls]. apply nth_set_nth_other. lia. }
        rewrite EO. split; [lia| intros X; left; exact X].
    - exact INC.
    - exact NDV.
    - exact LEN32.
    - exact CHW.
    - split; [exact TQC0|].
      eapply (qlist_rep_frame_clear AL _ (p_au K24) m mR l 0 AO BF B8 QL MU0 WM0 QBI).
      assert (SHM : forall xa ya, xa <= ya -> sh xa <= sh ya) by (intros xa ya Hxy; unfold sh; apply Z.add_le_mono_r; apply Z.div_le_mono; lia).
      pose proof (SHM (region AL K_BCLASS + p_au K24) (region AL K_BCLASS + p_mu K24) ltac:(clear - AU24; lia)) as SM1.
      pose proof (SHM (region AL K_BCLASS + p_au K24) (fa_base AL K_BCLASS + p_mfa K24) ltac:(clear - EFA ERG BF KO; lia)) as SM2.
      repeat (apply Forall_cons || apply Forall_nil).
      + left. unfold space_out. cbn [fst snd]. clear - LOQ CLO ACR SP2 SHS1. split; right; lia.
      + left. unfold space_out. cbn [fst snd]. clear - LOQ CLO ACR SP2 SHS1 HLO. split; right; lia.
      + left. unfold space_out. cbn [fst snd]. clear - ERI SHS1 SP1. split; right; lia.
      + right. right. left. cbn [fst snd]. clear - EFA ERG BF KO KR. lia.
      + right. right. left. cbn [fst snd]. clear - AU24. lia.
      + right. right. right. cbn [fst snd]. clear - SM1 SHB2. lia.
      + right. right. right. cbn [fst snd]. clear - SM2 SHB4. lia.
      + left. unfold space_out. cbn [fst snd]. clear - LP03 T3 T4 SHS1 SHS0 SP1. split; lia.
      + left. unfold space_out. cbn [fst snd]. clear - LP03 T3 T4 SHS1 SHS0 SP1. split; lia.
    - exact MIR.
    - exact STR.
    - exact FR0.
  }
  {
    assert (C0 : 0 < p_cnt K24) by lia.
    assert (ER : enq_refills P l = false) by (unfold enq_refills; rewrite NB; cbn [andb]; apply Z.eqb_neq; exact KC).
    assert (EP1 : enq_P1 P = P) by (unfold enq_P1; rewrite (proj2 (Z.eqb_neq _ _) KC); reflexivity).
    assert (SHS1 : sh (al_space AL + K_SPACE) <= 17594333495296) by (unfold sh, SHADOW_OFF; clear - SP5; Z.div_mod_to_equations; lia).
    unfold t_enq. rewrite ER.
    apply (enq_new_tail P H m0 junk8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AO HLO CLO ltac:(clear - LOQ; lia) QHI NB EP1).
    - unfold H_enq. rewrite ER. reflexivity.
    - refine (munch_weaken _ _ _ _ _ MU0). unfold prim_W. clear - LOQ. sub_fp_solve.
    - exact WM0.
    - exact PE0.
    - exact TE0.
    - exact SV0.
    - exact RPR0.
    - exact POK.
    - exact C0.
    - exact HOK.
    - exact INC.
    - exact NDV.
    - exact LEN32.
    - exact CHW.
    - split; [exact TQC0|].
      eapply (qlist_rep_frame_clear AL _ (p_au K24) m m0 l 0 AO BF B8 QL MU0 WM0 QBI).
      repeat (apply Forall_cons || apply Forall_nil).
      left. unfold space_out. cbn [fst snd]. clear - LOQ CLO ACR SP2 SHS1. split; right; lia.
    - exact MI0.
    - exact ST0.
    - exact FR0.
  }
Qed.

#[using="RF RP RPF"] Lemma enqueue_spec : forall (t0 t1 t2 a2 a5 a6 a7 t3 t4 t5 t6 : word),
  alayout_ok AL -> mem_inv asegs m -> mclean H m -> shvis H m -> poison_env E m -> thread_env L m ->
  stk asegs m lo q -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q - ENQ_STACK -> q <= 2^47 -> q mod 16 = 0 ->
  RPRIM AL P m -> prim_ok P -> refill_budget K_BCLASS K24 ->
  0 <= pr_calloc P -> 0 <= pr_cmapped P -> pr_cmapped P + K_REGION < 2^63 ->
  held_ok P hs -> incl (map (fun b => (K_BCLASS, qb_v b)) l) hs -> List.NoDup (map qb_v l) ->
  Forall (fun b => 1 <= qb_count b <= Q_BATCH) l -> Z.of_nat (length l) < 2^32 ->
  qcache_rep AL m TQ l -> qchunk_wf ch ->
  implA H (t_enq P l) enqueue_post
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz TQ) (wz CACHE) a2 (wz (qc_hdr AL ch)) (wz (qc_n ch)) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz enqueue_entry) fc None m (seg_rom asegs)).
Proof.
  intros until t6. intros AO MI C SV PE TE ST HLO CLO LOQ QHI Q16 RPR POK RB CA0 CM0 CM1 HOK INC NDV CNT LEN32 QC CHW. unfold enqueue_entry, ENQ_STACK, REFILL_STACK, POP_STACK, MF_STACK in *.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof AO as (_ & _ & _ & TL & _). pose proof TL as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & _).
  pose proof QC as QCF. pose proof CNT as CNTF. pose proof INC as INCF. pose proof NDV as NDVF. destruct QC as [TQC QL].
  pose proof (held_qb_in P hs l HOK INC) as QBI.
  assert (AUF : p_au K24 <= FA_OFF /\ p_au K24 mod 8 = 0).
  { destruct RPR as (_ & _ & CLS & _). destruct (CLS K_BCLASS ltac:(lia)) as ((_ & _ & _ & _ & _ & _ & AU & MUF & _ & AUM & _) & _).
    split; [lia|]. change (class_size K_BCLASS) with 8192 in AUM. clear - AUM. Z.div_mod_to_equations. lia. }
  destruct AUF as [BF B8].
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
  layout_apart_fact AO 0%nat 3%nat LP03.
  pose proof MI as MI0. change (mem_inv asegs m) with (id (mem_inv asegs m)) in MI0.
  assert (LSPLIT : l = [] \/ exists l' b, l = l' ++ [b]).
  { destruct (rev l) as [|b r] eqn:ER; [left; apply (f_equal (@rev _)) in ER; rewrite rev_involutive in ER; exact ER|].
    right. exists (rev r), b. rewrite <- (rev_involutive l), ER. reflexivity. }
  destruct LSPLIT as [EL|(l' & b & EL)].
  2: {
    assert (LENP : Z.of_nat (length l) = Z.of_nat (length l') + 1) by (rewrite EL, length_app; cbn [length]; lia).
    rewrite EL in QL, CNT, INC, NDV, QBI. apply qlist_rep_snoc in QL as [QLp QB]. destruct QB as (BC & (ws & BARR & LWS & FWS) & BSH).
    apply Forall_app in QBI as [QBIp QBIb]. apply Forall_cons_iff in QBIb as [(BV0 & BVA & BVF) _].
    assert (BVF2 := Z.le_trans _ _ _ BVF BF). clear BVF. rename BVF2 into BVF.
    apply Forall_app in CNT as [_ CNTb]. apply Forall_cons_iff in CNTb as [CNTb _].
    assert (SHB : 2147450880 <= sh (qb_addr AL b) /\ sh (qb_addr AL b) + 1024 <= 17594333495296) by (unfold sh, SHADOW_OFF, qb_addr, region; clear - BV0 BVF SP1 SP5; Z.div_mod_to_equations; lia).
    assert (BA : al_space AL + K_REGION <= qb_addr AL b /\ qb_addr AL b + Q_BBYTES <= al_space AL + K_SPACE) by (unfold qb_addr, region; clear - BV0 BVF; lia).
    assert (ELA : qlast AL l = qb_addr AL b) by (rewrite EL; apply qlast_snoc).
    rewrite ELA in TQC.
    pose proof (munch_refl [(q - 64, q); (TQ, TQ + 32); (qb_addr AL b, qb_addr AL b + Q_BBYTES)] m) as MU.
    pose proof (munch_refl [(q - 64, q)] m) as MUF.
    pose proof (wmono_refl asegs m) as WM.
    carve_frame 64%nat ST.
    lz_go.
    do 8 zstep.
    zstep.
    zstep. if_false_z.
    zstep.
    zstep.
    zstep.
    zstep. if_cases KF; zify_cond KF.
    {
      clear MUF QCF CNTF INCF NDVF.
      zstep. if_false_z.
      zstep.
      do 4 zstep.
      do 2 zstep.
      assert (CB0 : 0 <= qb_count b) by (unfold qb_count; lia).
      rewrite (Z.shiftl_mul_pow2 (qb_count b) 3) by lia. change (2 ^ 3) with 8.
      replace (qb_addr AL b + qb_count b * 8) with (qb_addr AL b + 24 + 8 * qb_count b + -24) by lia.
      pose proof (u64arr_store_ok asegs _ (qb_addr AL b + 24) ws (qb_count b) (wa (qb_addr AL b + 24 + 8 * qb_count b)) BARR ltac:(rewrite LWS; lia) eq_refl) as SOK.
      zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mx _ _) _) =>
        pose proof (u64arr_write asegs mx (qb_addr AL b + 24) ws (qb_count b) (wz (qc_hdr AL ch)) BARR ltac:(rewrite LWS; lia)) as BARR2 end.
      clear BARR SOK. store_done. rename BARR2 into BARR.
      zstep.
      do 3 zstep.
      do 7 zstep.
      zstep. replace (q + -64 + 64) with q by lia. zstep.
      release_frame FR ST q.
      assert (NB : need_batch l = false) by (rewrite EL, need_batch_snoc; apply Z.eqb_neq; exact KF).
      unfold t_enq, enq_refills. rewrite NB. cbn [andb].
      lz_ret. unfold enqueue_post, H_enq, enq_refills, enq_prim. rewrite NB. cbn [andb fst snd].
      finish.
      { reflexivity. }
      { unfold enq_W, prim_W, qlast_iv. rewrite NB. rewrite EL, rev_app_distr. cbn [rev List.app]. refine (munch_weaken _ _ _ _ _ MU). clear - LOQ. sub_fp_solve1. }
      { unfold id in MI0. refine (mem_inv_munch_above _ m _ MI0 MU _). clear - LOQ CLO ACR T3 BA SP1.
        repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; lia. }
      { eapply (poison_env_frame E _ m _ PE MU WM). unfold above_img. clear - LOQ CLO ACR T3 BA SP1.
        repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; lia. }
      { eapply (thread_env_frame L _ m _ TE MU WM). unfold thread_clear.
        layout_apart_fact AO 0%nat 2%nat LP02.
        clear - LOQ CLO ACR T1 T2 T3 T4 T5 BA SP1 LP02 LP03.
        repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; repeat split; lia. }
      { eapply shvis_wmono; [exact SV| exact WM]. }
      { apply (RPF P _ m _ RPR MU WM). unfold prim_clear.
        assert (SHS : sh (al_space AL + K_SPACE + 4096) <= 17594333495296) by (unfold sh, SHADOW_OFF; clear - SP5; Z.div_mod_to_equations; lia).
        assert (SHS0 : 2147450880 <= sh (al_space AL)) by (unfold sh, SHADOW_OFF; clear - SP1; Z.div_mod_to_equations; lia).
        repeat (apply Forall_cons || apply Forall_nil).
        - left. unfold prim_out. cbn [fst snd]. clear - LOQ CLO ACR T3 T4 SP2 SHS. repeat split; lia.
        - left. unfold prim_out. cbn [fst snd]. clear - LP03 T3 T4 SHS SHS0 SP1. repeat split; lia.
        - right. exists K_BCLASS, (qb_v b). split.
          + destruct HOK as [_ HF]. apply (proj1 (Forall_forall _ _) HF). apply INC. rewrite map_app. apply in_or_app. right. left. reflexivity.
          + left. unfold chunk_iv. cbn [fst snd]. unfold qb_addr. change (class_size K_BCLASS) with Q_BBYTES. lia. }
      {
        rewrite EL at 1. rewrite q_enq_snoc, (proj2 (Z.eqb_neq _ _) KF).
        set (b' := mkQB (qb_v b) (qb_size b + qc_n ch) (qb_chunks b ++ [ch])).
        assert (AB' : qb_addr AL b' = qb_addr AL b) by reflexivity.
        assert (CB' : qb_count b' = qb_count b + 1) by (unfold qb_count, b'; cbn [qb_chunks]; rewrite length_app; cbn [length]; lia).
        unfold qcache_rep. split.
        - replace (Z.of_nat (length (l' ++ [b']))) with (Z.of_nat (length l)) by (rewrite EL, !length_app; reflexivity).
          replace (qfirst AL (l' ++ [b'])) with (qfirst AL l) by (rewrite EL; destruct l'; reflexivity).
          rewrite qlast_snoc, AB'.
          replace (qbytes (l' ++ [b'])) with (qbytes l + qc_n ch) by (rewrite EL, !qbytes_app; unfold qbytes, b'; cbn [fold_right qb_size]; lia).
          exact TQC.
        - apply qlist_rep_snoc. rewrite AB'. split.
          + eapply (qlist_rep_frame_clear AL _ (p_au K24) m m2 l' _ AO BF B8 QLp MU WM QBIp).
            assert (SHS : sh (al_space AL + K_SPACE) <= 17594333495296) by (unfold sh, SHADOW_OFF; clear - SP5; Z.div_mod_to_equations; lia).
            assert (SHS0 : 2147450880 <= sh (al_space AL)) by (unfold sh, SHADOW_OFF; clear - SP1; Z.div_mod_to_equations; lia).
            repeat (apply Forall_cons || apply Forall_nil).
            * left. unfold space_out. cbn [fst snd]. clear - LOQ CLO ACR SP2 SHS. split; right; lia.
            * left. unfold space_out. cbn [fst snd]. clear - LP03 T3 T4 SHS SHS0 SP1. split; lia.
            * right. left. exists (qb_v b). split.
              { rewrite map_app in NDV. cbn [map] in NDV. apply NoDup_remove in NDV as [_ NI]. rewrite app_nil_r in NI. exact NI. }
              split; [exact BV0|]. split; [exact BVA|]. split; [clear - BVF BF; lia|]. left. cbn [fst snd]. unfold qb_addr. lia.
          + split; [| split].
            * rewrite CB'. exact BC.
            * eexists. split; [exact BARR|]. split; [rewrite upd_length; exact LWS|].
              unfold b'. cbn [qb_chunks]. rewrite length_app, map_app. cbn [length map].
              replace (length (qb_chunks b) + 1)%nat with (Datatypes.S (length (qb_chunks b))) by lia.
              replace (Z.to_nat (qb_count b)) with (length (qb_chunks b)) by (unfold qb_count; lia).
              apply firstn_upd_snocQ; [exact FWS| unfold qb_count in *; lia].
            * exact BSH. }
      { intros C. discriminate C. }
    }
    {
      assert (NB : need_batch l = true) by (rewrite EL, need_batch_snoc; apply Z.eqb_eq; exact KF).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        lazymatch goal with MIx : mem_inv asegs mx |- _ =>
          apply (enq_new mx _ _ _ _ _ _ _ _ _ _ _ _ AO SV PE TE HLO CLO LOQ QHI Q16 RPR POK RB CA0 CM0 CM1 HOK INCF NDVF CNTF LEN32 QCF CHW NB MUF WM MIx ST FR) end end. }
  }

  assert (NB : need_batch l = true) by (rewrite EL; reflexivity).
  assert (LEN0 : Z.of_nat (length l) = 0) by (rewrite EL; reflexivity).
  pose proof (munch_refl [(q - 64, q)] m) as MUF. pose proof (wmono_refl asegs m) as WM.
  carve_frame 64%nat ST.
  lz_go.
  do 8 zstep.
  zstep.
  rewrite LEN0. zstep. if_true_z.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with MIx : mem_inv asegs mx |- _ =>
      apply (enq_new mx _ _ _ _ _ _ _ _ _ _ _ _ AO SV PE TE HLO CLO LOQ QHI Q16 RPR POK RB CA0 CM0 CM1 HOK INCF NDVF CNTF LEN32 QCF CHW NB MUF WM MIx ST FR) end end.
Qed.

End ENQ.
