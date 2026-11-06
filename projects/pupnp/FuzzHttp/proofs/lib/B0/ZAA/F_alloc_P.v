(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ LJU PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimPopLens APrimQ APrimFrame AFrameM
                        APrimDealloc ASec ASecD AQuar AQuarM AHeap AFoot F_prim_refill F_prim_cdealloc F_poison F_quar_Ep F_quar_E F_quar_A AQuarR AQuarS AQuarP ATacFix
                        AQuarT F_gct F_depot F_depot_C F_prim_L0 F_hooks F_prim_calloc2 F_alloc_env F_alloc_A F_alloc_B F_alloc_C AAllocInv AAllocCarve AAllocEnvF.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac post_callA_k segs m UNF :=
  let a := fresh "r" in let H' := fresh "H'" in let ms' := fresh "ms'" in let PO := fresh "POST" in let MC := fresh "MC" in
  intros a H' ms' [PO MC];
  destruct_exs PO;
  let E := fresh "E" in let EH := fresh "EH" in let MUc := fresh "MUk" in let WMc := fresh "WMk" in let MIc := fresh "MI" in
  destruct PO as [E [EH [MUc [WMc PO]]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms'; subst H'; clean_ms_mem MC;
  try destruct_ands PO;
  UNF MUc;
  lazymatch type of MUc with
  | munch _ m ?m' => transport_after_call segs m m' MUc WMc
  end;
  lz_cont MC;
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
       end).
Tactic Notation "callAk" uconstr(SPEC) "unfolding" tactic3(UNF) :=
  lz_here;
  lazymatch goal with
  | |- ITreeLZ.implL ?segs _ _ _ _ _ (MS _ _ _ _ _ ?m _) =>
      let C := find_mclean m in
      eapply implA_ebind; [ eapply implA_mclean; [ exact C | eapply SPEC ] | clear C; post_callA_k segs m UNF ]
  end.

Lemma munch_joinP : forall W1 W2 (m0 m m' : mem), munch W1 m0 m -> munch W2 m m' -> munch (W1 ++ W2) m0 m'.
Proof.
  intros W1 W2 m0 m m' M1 M2 x Hx. apply outside_app in Hx as [H1 H2]. rewrite (M2 x H2). exact (M1 x H1).
Qed.

Lemma al_cls_eq : forall n, 0 <= n -> a0_need n <= 65536 -> class_of (a0_need n) = a0_cls (al_n n).
Proof.
  intros n N0 NP. unfold a0_cls.
  assert (EN : a0_need (al_n n) = a0_need n) by (unfold al_n; destruct (Z.eqb_spec n 0) as [->|NE]; reflexivity).
  rewrite EN. replace (a0_need n <=? 65536) with true by (symmetry; apply Z.leb_le; exact NP). reflexivity.
Qed.

Definition ALLOC_STACK : Z := 128 + CALLOC_STACK.

Definition al_chunk_p (P : prim) (n : Z) : qchunk :=
  mkQC (QPrim (class_of (a0_need n)) (snd (cache_alloc P (class_of (a0_need n))))) (al_rz n) (al_n n).

Section ALLOCP.
  Context {HC : HasCeiling}.
  Variables (AL : alayout) (E : penv).
  Notation L := (al_thread AL).
  Notation D := (al_depot AL).
  Notation THR := (at_thr (al_thread AL)).
  Hypothesis AO : alayout_ok AL.
  Variables (gp : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q lo : Z).
  Hypothesis LOH : 0x10007fff8000 <= lo.
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis LOQ : lo <= q - ALLOC_STACK.
  Hypothesis QH : q <= 2^47.
  Hypothesis Q16 : q mod 16 = 0.

  Definition allocate_post_p (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (X : pstate) (H : word -> bool) (m : mem) (n : Z)
      (WB : list qbatch) (WC : list qchunk) (hrest : list (Z * Z)) (hs : list Z) (total : Z) (tr : list Z) : unit -> (word -> bool) -> machine_state -> Prop :=
    fun _ H' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' W hs' total',
      let P := fst X in let c := class_of (a0_need n) in let P' := fst (cache_alloc P c) in let v := snd (cache_alloc P c) in
      let ch := al_chunk_p P n in let X' := (P', snd X) in
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz (qc_hdr AL ch + 16)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ H' = (if p_cnt (get_cls P c) =? 0 then H_gfa AL c (get_cls P c) (max_count c / 2) H else H)
      /\ munch W m m' /\ wmono asegs m m'
      /\ Forall (fun iv => atouch AL lo q (fst X) (snd X) [] [] iv \/ chunk_iv AL c v iv \/ chunk_sh_iv AL c v iv \/ dstat iv \/ dreg AL iv) W
      /\ dr_inv AL E X' H' m' WB WC (prim_of ch ++ hrest)
      /\ qchunk_wf ch /\ held_kind X' ch /\ lchunk_rep AL m' ch
      /\ stk asegs m' lo q
      /\ 1 <= c <= 30 /\ c = a0_cls (al_n n) /\ 0 <= v /\ 16 * v + class_size c <= p_au (get_cls P' c) /\ (16 * v) mod class_size c = 0
      /\ RDEPOT D hs' total' m'
      /\ ((dfind hs (depot_hash tr) <> 0 /\ hs' = hs /\ total' = total)
          \/ (dfind hs (depot_hash tr) = 0 /\ hs' = hs ++ [depot_hash tr] /\ total' = total + Z.of_nat (length tr) + 1)).

  #[using="AO LOH CLO LOQ QH Q16"] Theorem allocate_prim_spec : forall (ra t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
        (X : pstate) (H : word -> bool) (m : mem) (n : Z) (WB : list qbatch) (WC : list qchunk) (hrest : list (Z * Z))
        (STK TR total : Z) (hs : list Z) (ws : list word) (tr : list Z),
    mclean H m -> stk asegs m lo q ->
    dr_inv AL E X H m WB WC hrest ->
    0 <= n <= A0_MAXREQ -> a0_need n <= 65536 ->
    refill_budget (class_of (a0_need n)) (get_cls (fst X) (class_of (a0_need n))) ->
    0 <= pr_calloc (fst X) -> 0 <= pr_cmapped (fst X) -> pr_cmapped (fst X) + K_REGION < 2^63 ->
    alloc_env m -> thread_env2 AL m -> hooks_env m -> RDEPOT D hs total m ->
    rw_cells asegs m STK [C8 (wz TR); C8 (wz (Z.of_nat (length tr)))] -> q <= STK -> STK + 16 <= 2^47 ->
    u64arr asegs m TR ws -> firstn (length tr) ws = map wz tr -> (length tr <= length ws)%nat -> (1 <= length tr <= 30)%nat ->
    Forall (fun x => 0 <= x < 2^64) tr -> q <= TR -> TR + 8 * Z.of_nat (length ws) <= 2^47 ->
    16 * (zlen hs + 2) <= 2^20 -> 8 * (total + Z.of_nat (length tr) + 1) <= SWIN D -> total + Z.of_nat (length tr) + 1 < 2^20 ->
    implA H (if p_cnt (get_cls (fst X) (class_of (a0_need n))) =? 0 then t_refill AL (class_of (a0_need n)) (get_cls (fst X) (class_of (a0_need n))) else t_none)
      (allocate_post_p ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X H m n WB WC hrest hs total tr)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz INSTANCE) (wz n) (wz 8) (wz STK) (wz 1) (wz 1) a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz allocate_entry) fc None m (seg_rom asegs)).
  Proof.
    intros ra t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 X H m n WB WC hrest STK TR total hs ws tr
      MC ST INV NR NP RB CA0 CM0 CM1 AE TE2 HKE RD SOBJ QSTK STKH BUF TRW LENW LTR RNG QTR TRH ROOM_N ROOM_F ROOM_T.

    unfold allocate_entry.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (CS : 224 <= CALLOC_STACK) by (vm_compute; discriminate).
    unfold ALLOC_STACK in LOQ.
    pose proof INV as (RP & POK & RS & MI & PE & TE & SV & WFS & REPS & HKS & HOK & NDS & BWF & BREP).
    pose proof AO as (_ & _ & _ & TLO & DLO & SWB). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & _).
    set (c := class_of (a0_need n)) in *.
    assert (RZF : 16 <= al_rz n <= 2048 /\ al_rz n mod 16 = 0).
    { unfold al_rz. pose proof (a0_rzlog_range n) as RZL. remember (a0_rzlog n) as rzl eqn:Erzl. clear - RZL.
      assert (C : rzl = 0 \/ rzl = 1 \/ rzl = 2 \/ rzl = 3 \/ rzl = 4 \/ rzl = 5 \/ rzl = 6 \/ rzl = 7) by lia.
      destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; (split; [split; apply Z.leb_le; reflexivity| reflexivity]). }
    assert (NEED1 : exists k, a0_need n = 8 * k + al_rz n /\ Z.max n 8 <= 8 * k < Z.max n 8 + 8).
    { exists ((Z.max n 8 + 7) / 8). unfold a0_need, al_rz. split; [lia|]. clear. Z.div_mod_to_equations. lia. }
    destruct NEED1 as (rk & NEED & RK).
    assert (CR : 1 <= c <= 30) by (exact (a0_class_of_range (a0_need n) ltac:(clear - NEED RK RZF NP; lia))).

    lz_go.
    pose proof TE as TE'. te_split TE'.
    callk (front_spec gp F_ fc q lo n STK CLO ltac:(clear - LOQ CS; lia) QH Q16 NR ltac:(clear - QSTK STKH QH LOQ CS ACR CLO; lia));
      [ exact ST | exact MI | exact TE_inited | exact AE | ].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    rename MUk into MU1, WMk into WM1. hideB MU1. hideB WM1.
    lazymatch goal with HS : stk asegs m1 _ _ |- _ => rename HS into ST1 end. lazymatch goal with HM : mem_inv asegs m1 |- _ => rename HM into MI1 end.
    lazymatch goal with HF : rw_cells asegs m1 (q - 128) _ |- _ => rename HF into FR end.

    assert (EPR : al_prim n = true) by (unfold al_prim; apply Z.leb_le; exact NP).
    unfold al_need. rewrite EPR.

    zstep.
    assert (TE1 : thread_env L m1) by (unfold thread_env; repeat match goal with |- _ /\ _ => split end; assumption).
    callk (gct_spec L _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc (q - 128) m1 lo _ _);
      [ exact ST1 | exact CLO | clear - LOQ CS; lia | clear - Q16; Z.div_mod_to_equations; lia | clear - QH; lia | exact TE1 | exact TLO | exact MI1 | ].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    rename MUk into MU2, WMk into WM2. hideB MU2. hideB WM2.
    lazymatch goal with HS : stk asegs m2 _ _ |- _ => rename HS into ST2 end. lazymatch goal with HM : mem_inv asegs m2 |- _ => rename HM into MI2 end.
    lazymatch goal with HT : thread_env L m2 |- _ => rename HT into TEG end.
    clear TE1.
    zstep. zstep. if_cases KT; zify_cond KT. { exfalso. clear - KT T3. lia. } clear KT.
    zstep. zstep. zstep. zstep. zstep.

    unhideB MU1. unhideB WM1. unhideB MU2. unhideB WM2.
    pose proof (munch_joinP _ _ _ _ _ MU1 MU2) as MU12. cbn [app] in MU12. pose proof (wmono_trans asegs _ _ _ WM1 WM2) as WM12.
    assert (INV2 : dr_inv AL E X H m2 WB WC hrest).
    { eapply (dr_inv_frame_d AL E X H m m2 WB WC hrest lo _ AO LOH CLO INV MU12 WM12 MI2).
      repeat (apply Forall_cons || apply Forall_nil); unfold dzone; cbn [fst snd]; left; clear - LOQ CS; lia. }
    hideB MU1. hideB WM1. hideB MU2. hideB WM2. hideB MU12. hideB WM12.
    pose proof INV2 as (RP2 & POK2 & RS2 & _ & PE2 & _ & SV2 & _).

    set (P := fst X) in *. set (k := get_cls P c) in *.
    destruct (clear_ctx AL X m2 RP2 RS2) as (WF0 & SOK & SSEP). fold P in WF0.
    pose proof (WF0 c ltac:(clear - CR; lia)) as WFk. fold k in WFk.
    set (k1 := if p_cnt k =? 0 then refill k c else k).
    assert (WF1 : pclass_wf c k1).
    { unfold k1. destruct (Z.eqb_spec (p_cnt k) 0) as [C0|CN]; [| exact WFk].
      exact (APrimRefill.refill_wf c k ltac:(clear - CR; lia) WFk (proj1 RB) (proj2 RB) C0). }
    assert (LEN0 : length (pr_cls P) = 32%nat) by (destruct RP2 as (LEN0 & _); exact LEN0).
    assert (EK' : get_cls (fst (cache_alloc P c)) c
                  = mkPCL (p_nf k1) (p_mfa k1) (p_au k1) (p_mu k1) (p_nalloc k1) (p_nfreed k1) (p_fa k1) (p_cnt k1 - 1) (firstn (Z.to_nat (p_cnt k1 - 1)) (p_chunks k1))).
    { unfold cache_alloc, cache_alloc_cls. fold k. fold k1. cbn [fst]. apply get_cls_set_same; [exact LEN0| clear - CR; lia]. }
    assert (KO : 0 <= p_nf k /\ 0 <= p_mfa k <= K_FA_SIZE /\ 0 <= p_mu k <= FA_OFF).
    { destruct WFk as (Lnf' & _ & _ & _ & MFA' & _ & AU' & MUF' & _). clear - Lnf' MFA' AU' MUF'. lia. }
    assert (KR : 0 <= p_nf (get_cls (fst (cache_alloc P c)) c) /\ 0 <= p_mfa (get_cls (fst (cache_alloc P c)) c) <= K_FA_SIZE
                 /\ 0 <= p_mu (get_cls (fst (cache_alloc P c)) c) <= FA_OFF).
    { rewrite EK'. cbn [p_nf p_mfa p_mu]. destruct WF1 as (Lnf' & _ & _ & _ & MFA' & _ & AU' & MUF' & _). clear - Lnf' MFA' AU' MUF'. lia. }
    clear TE_tsd TE_inited TE_tp TE_ctx TE_thr TE_bounds TE_sw TE_unw TE_gotpg TE_pg.
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
    assert (ERI : ri_addr AL c = al_space AL + K_SPACE + 128 * c) by reflexivity.
    assert (ERG : region AL c = al_space AL + c * K_REGION) by reflexivity.
    assert (EFA : fa_base AL c = al_space AL + c * K_REGION + FA_OFF) by reflexivity.
    assert (SHB : forall xa, al_space AL <= xa <= al_space AL + K_SPACE -> 2147450880 <= sh xa <= 17594333495296)
      by (intros xa Hx; unfold sh, SHADOW_OFF; clear - Hx SP1 SP5; Z.div_mod_to_equations; lia).
    pose proof (SHB (region AL c + p_mu k) ltac:(clear - ERG KO CR; lia)) as SHB1.
    pose proof (SHB (region AL c + p_mu (get_cls (fst (cache_alloc P c)) c)) ltac:(clear - ERG KR CR; lia)) as SHB2.
    pose proof (SHB (fa_base AL c + p_mfa k) ltac:(clear - EFA KO CR; lia)) as SHB3.
    pose proof (SHB (fa_base AL c + p_mfa (get_cls (fst (cache_alloc P c)) c)) ltac:(clear - EFA KR CR; lia)) as SHB4.
    rewrite <- (ebind_ret_r (if p_cnt k =? 0 then t_refill AL c k else t_none)).
    hideB FR. hideB SOBJ. hideB BUF.
    callAk (cache_alloc_spec AL E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc m2 H (q - 128) lo (a0_need n) P AO MI2) unfolding (fun h => unfold prim_W in h);
      [ assumption | exact SV2 | exact PE2 | exact TEG | exact ST2 | exact LOH | exact CLO | clear - LOQ; lia | clear - QH; lia
      | clear - Q16; Z.div_mod_to_equations; lia | clear - NEED RK RZF NP; lia | exact RP2 | exact POK2 | exact RB | exact CA0 | exact CM0 | exact CM1 | ].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    rename MUk into MU3, WMk into WM3.
    fold c in MU3, PC3, PC4, PC5, PC6, PC7, POST |- *.
    lazymatch type of MU3 with munch ?w _ _ => assert (DJ3 : forall A k0, q - 128 <= A -> disjoint_from w A k0) end.
    { intros A k0 HA. cbn [disjoint_from]. clear - HA LOQ CS LOH CLO SP2 T4 ERI ERG EFA KO KR CR SHB1 SHB2 SHB3 SHB4. lia. }
    unhideB FR. eapply (rw_cells_transport asegs _ m2 m3) in FR; [| exact MU3| exact WM3| apply DJ3; clear; lia].
    unhideB SOBJ. eapply (rw_cells_transport asegs _ m2 m3) in SOBJ; [| exact MU3| exact WM3| apply DJ3; clear - QSTK; lia].
    unhideB BUF. eapply (u64arr_transport asegs _ m2 m3) in BUF; [| exact MU3| exact WM3| apply DJ3; clear - QTR; lia].
    rename MI0 into MI3, PC into ST3, PC0 into PE3, PC1 into TE3, PC2 into SV3, PC3 into RP3, PC4 into POK3, PC5 into FCH, PC6 into V0, PC7 into VAU, POST into VAL.
    set (P' := fst (cache_alloc P c)) in *. set (v := snd (cache_alloc P c)) in *.
    assert (HOK3 : held_ok P' ((c, v) :: map bpair WB ++ flat_map prim_of WC ++ hrest)).
    { apply calloc_held_ok; [exact HOK| clear - CR; lia| exact LEN0| exact WF0| exact RB]. }
    pose proof (dr_inv_calloc AL E X _ _ m2 m3 WB WC hrest lo (q - 128) c AO LOH CLO ltac:(clear - LOQ CS; lia) ltac:(clear - CR; lia)
                  INV2 MU3 WM3 MI3 PE3 TE3 SV3 RP3 POK3 HOK3) as INV3.
    cbv zeta in INV3. fold P P' v in INV3.

    pose proof INV3 as (_ & _ & RS3 & _).
    destruct (clear_ctx AL (P', snd X) m3 RP3 RS3) as (WFN & _ & _). cbn [fst] in WFN.
    assert (HELD : held1 P' (c, v)) by (destruct HOK3 as [_ FH3]; exact (Forall_inv FH3)).
    pose proof (held_geo AL P' AO WFN c v HELD) as G. cbv zeta in G. destruct G as (_ & G1 & G2 & G3 & GCS & G5 & G6 & G7).
    pose proof (class_size_mod16 c ltac:(clear - CR; lia)) as CM16.
    pose proof (class_of_fits (a0_need n) ltac:(clear - NEED RK RZF NP; lia)) as FITS. fold c in FITS.
    pose proof (region_range AL c ltac:(clear - CR; lia)) as [RR1 RR2].
    set (B := region AL c + 16 * v) in *.
    assert (B8 : B mod 8 = 0) by (unfold B; rewrite ERG; clear - SPM; Z.div_mod_to_equations; lia).
    assert (BLO : 17594333495296 <= B /\ B + class_size c <= alloc_ceiling) by (clear - G1 G2 G3 ERG SP1 SP2 CR RR1 RR2; lia).
    zstep. zstep. if_cases KZ; zify_cond KZ. { exfalso. clear - KZ BLO ACR. lia. } clear KZ.
    set (rz := al_rz n) in *. set (size := al_n n) in *.
    assert (SZR : 1 <= size <= 2^28 /\ size <= Z.max n 8) by (unfold size, al_n, A0_MAXREQ in *; destruct (Z.eqb_spec n 0); clear - NR e || clear - NR n0; lia).
    assert (FIT : rz + rup8 size <= class_size c) by (unfold rup8; clear - SZR RK NEED FITS; Z.div_mod_to_equations; lia).
    destruct FCH as ((jb & FCB) & FCS). fold B in FCB, FCS.
    destruct (carve_free m3 B (class_size c) rz size jb ltac:(clear - BLO; lia) B8 ltac:(clear - CM16; Z.div_mod_to_equations; lia)
                (proj1 (proj1 RZF)) (proj2 RZF) (proj1 (proj1 SZR)) FIT FCB FCS)
      as ((j0 & LRZ) & (b0 & b1 & j2 & j4 & j8 & HD1 & HD2) & (ub & UB) & (sl & SLK) & SHL & (ju & SHU) & SHP & SHR).
    set (M := B + rz - 16) in *.
    assert (EB : B = region AL c + 16 * v) by reflexivity. assert (EM : M = B + rz - 16) by reflexivity.
    assert (Erz : rz = al_rz n) by reflexivity. assert (Esize : size = al_n n) by reflexivity.
    replace (B + rz - 16 + 8) with (M + 8) in HD2 by (clear - EM; lia).
    replace (B + rz) with (M + 16) in UB, SLK, SHU, SHP, SHR by (clear - EM; lia).
    clearbody M. clearbody B. clearbody rz. clearbody size.
    assert (MR : B <= M /\ M + 16 + rup8 size <= B + class_size c /\ M mod 8 = 0 /\ size <= rup8 size < size + 8)
      by (unfold rup8 in *; clear - EM FIT RZF B8 SZR; Z.div_mod_to_equations; lia).

    pose proof FR as FRc. split_chunk FRc 1%nat FRa FRb. split_chunk FRb 1%nat FR8 FRd. split_chunk FRd 1%nat FR16 FRe. clear FRa FRe.
    change (Z.of_nat 8) with 8 in FR8.
    assert (BRp : 0 <= B /\ B mod 8 = 0 /\ B + a0_need n <= 2^47) by (split; [clear - BLO; lia| split; [exact B8| clear - BLO FITS ACR; lia]]).
    assert (SZp : 1 <= size <= 2^28 /\ rz + size <= a0_need n /\ 0 <= n <= 2^28) by (unfold A0_MAXREQ in NR; clear - SZR NEED RK NR; lia).

    assert (Ec : c = class_of (a0_need n)) by reflexivity. assert (EP : P = fst X) by reflexivity.
    assert (EP' : P' = fst (cache_alloc P c)) by reflexivity. assert (Ev : v = snd (cache_alloc P c)) by reflexivity.
    assert (Ek : k = get_cls P c) by reflexivity.
    clear WF1 EK'. clearbody P' v k. clear k1. clearbody c. clearbody P.
    rewrite <- Ek in *.

    layout_apart_fact AO 0%nat 2%nat A02. layout_apart_fact AO 0%nat 3%nat A03. layout_apart_fact AO 0%nat 5%nat A05. layout_apart_fact AO 0%nat 6%nat A06.
    layout_apart_fact AO 3%nat 5%nat A35. layout_apart_fact AO 3%nat 6%nat A36.
    layout_facts AO 6%nat LSS. destruct LSS as (SS1 & SS2 & _).
    pose proof DLO as (DL1 & DL2 & _ & DL4 & _).
    unhideB MU12. unhideB WM12.
    pose proof (munch_joinP _ _ _ _ _ MU12 MU3) as MU13. cbn [app] in MU13. pose proof (wmono_trans asegs _ _ _ WM12 WM3) as WM13.
    assert (MINF : 0 <= Z.min (p_nf k) (p_nf (get_cls P' c))) by (clear - KO KR; lia).
    assert (TE23 : thread_env2 AL m3).
    { eapply thread_env2_frame_m; [exact TE2| exact MU13| |]; cbn [disjoint_from].
      - clear - LOQ CS CLO T3 T4 A03 ERI ERG EFA KO KR CR MINF SHB1 SHB2 SHB3 SHB4. lia.
      - clear - LOQ CS CLO T1 T2 T5 A02 ERI ERG EFA KO KR CR MINF SHB1 SHB2 SHB3 SHB4. lia. }
    assert (RD3 : RDEPOT D hs total m3).
    { eapply RDEPOT_frame_m; [exact DLO| exact SWB| exact RD| exact MU13| | |]; cbn [disjoint_from].
      - clear - LOQ CS LOH SP1 T3 ERI ERG EFA KO KR CR MINF SHB1 SHB2 SHB3 SHB4. lia.
      - clear - LOQ CS CLO DL1 DL2 A05 A35 ERI ERG EFA KO KR CR MINF SHB1 SHB2 SHB3 SHB4. lia.
      - clear - LOQ CS CLO SS1 SS2 A06 A36 ERI ERG EFA KO KR CR MINF SHB1 SHB2 SHB3 SHB4. lia. }
    hideB MU12. hideB WM12. hideB MU13. hideB WM13.

    destruct TE23 as (THC & tidw & TIDC).
    hideB FR. hideB SOBJ. hideB BUF. hideB FCB. hideB FCS. hideB LRZ. hideB HD1. hideB HD2. hideB UB. hideB SLK. hideB SHL. hideB SHU. hideB SHR.
    hideB FR8. hideB FR16. hideB MU3. hideB WM3. hideB THC. hideB TIDC.
    assert (SPRm : (q - 128) mod 16 = 0 /\ q - 128 + 128 <= 2^47) by (split; [clear - Q16; Z.div_mod_to_equations; lia| clear - QH; lia]).
    assert (THRm : 0 < THR < 2^64) by (clear - T3 T4 ACR; lia).
    assert (MDJm : 6328320 <= M /\ M + 16 <= lo /\ (M + 16 <= DN0 D \/ DN0 D + 2^20 <= M) /\ (M + 16 <= SS0 D \/ SS0 D + SWIN D <= M)).
    { pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 DLO)))))) as SW0. destruct MR as (MR1 & MR2 & _ & MR4).
      clear - MR1 MR2 MR4 SZR BLO CLO A05 A06 SS2 SWB SW0 G1 G2 G3 ERG CR SP1 SP2. lia. }
    assert (DJTm : THR + 8 <= M \/ M + 16 <= THR) by (destruct MR as (MR1 & MR2 & _ & MR4); clear - MR1 MR2 MR4 SZR A03 G1 G2 G3 ERG CR; lia).
    assert (DJCm : at_ctx L + 12 <= M \/ M + 16 <= at_ctx L + 8) by (destruct MR as (MR1 & MR2 & _ & MR4); clear - MR1 MR2 MR4 SZR A02 G1 G2 G3 ERG CR; lia).
    eapply evt_cut.
    { eapply (back1_spec D gp _ _ _ _ _ _ _ F_ fc (q - 128) lo B M rz size (a0_need n) n THR (at_ctx L) STK TR total m3 hs ws tr
               DLO CLO ltac:(clear - LOQ CS; lia) SPRm THRm BRp RZF SZp EM MDJm _ _ _ _ _ _ _ _ _ _ _ tidw b0 b1 j2 j4 j8);
        [ exact MI3 | exact ST3 | exact FR16 | exact HD1 | exact HD2 | exact THC | exact TIDC | exact SOBJ | exact RD3 | exact BUF | exact TRW | exact LENW | exact LTR | exact RNG
        | clear - QTR; lia | exact TRH | clear - QSTK; lia | exact STKH | exact ROOM_N | exact ROOM_F | exact ROOM_T | exact DJTm | exact DJCm ]. }
    cbv beta. intros msB PB. unfold back1_post in PB.
    destruct PB as (ra5 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & m4 & mD & m5 & hs' & total' & bits1 & actx & -> & MS4 & MSD & MS5 & ST5 & RD5 & RES & B31 & HDN & ACX).

    assert (WFch : qchunk_wf (mkQC (QPrim c v) rz size)).
    { unfold qchunk_wf. cbn [qc_rz qc_n qc_kind qc_bsize]. split; [exact (proj1 (proj1 RZF))|]. split; [exact (proj2 RZF)|]. split; [clear - SZR; lia|].
      split; [exact FIT|]. split; [clear - CR; lia|]. split; [exact V0| exact VAL]. }
    assert (BLKSTEP : forall (ma mb : mem) Hh A k0 sa sb, dr_inv AL E (P', snd X) Hh ma WB WC ((c, v) :: hrest) ->
              munch [(sa, sb); (A, A + k0)] ma mb -> wmono asegs ma mb -> mem_inv asegs mb -> lo <= sa -> sb <= q -> B <= A -> A + k0 <= B + class_size c ->
              dr_inv AL E (P', snd X) Hh mb WB WC ((c, v) :: hrest)).
    { intros ma mb Hh A k0 sa sb IV MUab WMab MIb L1 L2 L3 L4.
      eapply (dr_inv_blk AL E (P', snd X) Hh ma mb WB WC hrest (mkQC (QPrim c v) rz size) lo q sa sb A k0 AO LOH CLO IV HELD WFch ltac:(intros sc []) MUab WMab MIb L1 L2).
      - unfold qc_blk. cbn [qc_kind]. rewrite <- EB. exact L3.
      - unfold qc_blk, qc_bsize. cbn [qc_kind]. rewrite <- EB. exact L4. }
    assert (SHSTEP : forall (ma mb : mem) Hh A k0 sa sb, dr_inv AL E (P', snd X) Hh ma WB WC ((c, v) :: hrest) ->
              munch [(sa, sb); (A, A + k0)] ma mb -> wmono asegs ma mb -> mem_inv asegs mb -> lo <= sa -> sb <= q -> sh B <= A -> A + k0 <= sh B + class_size c / 8 ->
              dr_inv AL E (P', snd X) Hh mb WB WC ((c, v) :: hrest)).
    { intros ma mb Hh A k0 sa sb IV MUab WMab MIb L1 L2 L3 L4.
      eapply (dr_inv_poison AL E (P', snd X) Hh ma mb WB WC hrest (mkQC (QPrim c v) rz size) lo q sa sb A k0 AO LOH CLO IV HELD WFch ltac:(intros sc []) MUab WMab MIb L1 L2).
      - unfold qc_blk. cbn [qc_kind]. rewrite <- EB. exact L3.
      - unfold qc_blk, qc_bsize. cbn [qc_kind]. rewrite <- EB. exact L4. }
    assert (WK1 : forall a b (ma mb : mem), munch [(a, b)] ma mb -> munch [(lo, lo); (a, b)] ma mb).
    { intros a b ma mb MUab. eapply munch_weaken; [| exact MUab]. unfold sub_fp. cbn [outside]. intros xo (_ & O2 & _). split; [exact O2| exact I]. }
    destruct MS4 as (MU4 & WM4 & MI4). destruct MSD as (MUD & WMD & MID). destruct MS5 as (MU5 & WM5 & MI5).
    pose proof (BLKSTEP m3 m4 _ M 8 lo lo INV3 (WK1 _ _ _ _ MU4) WM4 MI4 ltac:(clear; lia) ltac:(clear - LOQ CS; lia)
                  ltac:(clear - MR; lia) ltac:(destruct MR as (MR1 & MR2 & _ & MR4); clear - MR1 MR2 MR4 SZR; lia)) as INV4.
    layout_facts AO 5%nat LDN. destruct LDN as (N1d & N2d & _). pose proof (bkt_range (depot_hash tr)) as BKR.
    assert (T0 : 0 <= total) by (destruct RD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & T0 & _); exact T0).
    assert (FZD : Forall (dzone AL lo) [(q - 128 - 224, q - 128); (DT + 4 * bkt (depot_hash tr), DT + 4 * bkt (depot_hash tr) + 4); (DNI, DNI + 4);
                  (DN0 D + 16 * (zlen hs + 1), DN0 D + 16 * (zlen hs + 1) + 16); (SSA, SSA + 8); (SSD + 8, SSD + 12);
                  (SS0 D + 8 * total, SS0 D + 8 * total + 8 + 8 * Z.of_nat (length tr))]).
    { unfold zlen in *. repeat (apply Forall_cons || apply Forall_nil); unfold dzone, dstat, dreg; cbn [fst snd].
      - left. clear - LOQ CS. lia.
      - right; left. clear - BKR. lia.
      - right; left. clear. lia.
      - right; right; left. clear - ROOM_N. lia.
      - right; left. clear. lia.
      - right; left. clear. lia.
      - right; right; right. clear - ROOM_F SWB T0. lia. }
    pose proof (dr_inv_frame_d AL E _ _ m4 mD WB WC _ lo _ AO LOH CLO INV4 MUD WMD MID FZD) as INVD.
    replace (M + 16) with (M + 8 + 8) in MU5 by (clear; lia).
    pose proof (BLKSTEP mD m5 _ (M + 8) 8 lo lo INVD (WK1 _ _ _ _ MU5) WM5 MI5 ltac:(clear; lia) ltac:(clear - LOQ CS; lia)
                  ltac:(clear - MR; lia) ltac:(destruct MR as (MR1 & MR2 & _ & MR4); clear - MR1 MR2 MR4 SZR; lia)) as INV5.
    clear INV4 INVD.

    unhideB SHL. pose proof SHL as SHL0. hideB SHL.
    assert (RZ8 : (1 + 0 <= Z.to_nat (rz / 8))%nat) by (destruct RZF as (RZa & RZb); clear - RZa RZb; Z.div_mod_to_equations; lia).
    unfold fa_bytes in SHL0. destruct (cb_split3_rep m3 (sh B) _ _ 1 0 RZ8 SHL0) as (SB1 & _ & _). clear SHL0.
    assert (SBC : rw_cells asegs m3 (sh B) [C1 (Z_to_bv 8 250)]) by (eapply rw_cells_rebytes; [exact SB1| clear; cbn; tauto| reflexivity| reflexivity]).
    clear SB1.
    assert (SHBR : 2147450880 <= sh B /\ sh B + 1 <= 17594333495296) by (assert (4 <= class_size c / 8) by (clear - GCS; Z.div_mod_to_equations; lia); clear - G5 G6 G7 H0; lia).
    pose proof N1d as N1d'.
    eapply (rw_cells_transport asegs _ m3 m4) in SBC; [| exact MU4| exact WM4| cbn [disjoint_from cells_size csize Nat.add]; destruct MR as (MR1 & _); clear - SHBR MR1 BLO; lia].
    eapply (rw_cells_transport asegs _ m4 mD) in SBC; [| exact MUD| exact WMD| cbn [disjoint_from cells_size csize Nat.add]; unfold zlen in *; clear - SHBR LOH LOQ CS BKR N1d N2d SS1 SS2 ROOM_N ROOM_F SWB T0; lia].
    eapply (rw_cells_transport asegs _ mD m5) in SBC; [| exact MU5| exact WM5| cbn [disjoint_from cells_size csize Nat.add]; destruct MR as (MR1 & _); clear - SHBR MR1 BLO; lia].
    pose proof INV5 as (_ & _ & _ & _ & PE5 & TE5 & _). pose proof PE5 as PE5s. pe_split PE5s.
    assert (SHA : 2147450880 + Z.shiftr B 3 = sh B) by (rewrite Z.shiftr_div_pow2 by lia; unfold sh, SHADOW_OFF; change (2^3) with 8; clear; lia).
    hideB HDN. hideB ACX.
    zstep. if_false.
    zstep. zstep. zstep. zstep. zstep.
    rewrite SHA. remember (sh B) as SBA eqn:ESBA.
    zstep.
    cbv beta. change (bv_unsigned (Z_to_bv 8 250)) with 250.
    zstep. if_true.
    subst SBA. clear PE_gotcf PE_thr PE_limit PE_decor PE_gotaf PE_psg PE_gotshb PE_shb PE_gotmem PE_hme PE_rms PE_canp PE_sealed PE_gotpg PE_pg PE_dd PE_nh PE_gotguard PE_guard PE_libcpg PE_ddr PE_nhr SBC.

    unhideB MU13. unhideB WM13.
    pose proof (munch_joinP _ _ _ _ _ MU13 MU4) as MUa. pose proof (munch_joinP _ _ _ _ _ MUa MUD) as MUb. pose proof (munch_joinP _ _ _ _ _ MUb MU5) as MU15.
    cbn [app] in MU15. clear MUa MUb.
    destruct MR as (MR1 & MR2 & MR3 & MR4).
    lazymatch type of MU15 with munch ?w _ _ => assert (FO15 : Forall aenv_out w) end.
    { unfold zlen in *. repeat (apply Forall_cons || apply Forall_nil); unfold aenv_out; cbn [fst snd];
        clear - LOQ CS LOH SP1 ERI ERG EFA KO KR CR MINF SHB1 SHB2 SHB3 SHB4 T3 MR1 BLO BKR N1d SS1 ROOM_N ROOM_F T0; lia. }
    pose proof (alloc_env_frame_m _ m m5 AE MU15 FO15) as AE5. pose proof (hooks_env_frame_m _ m m5 HKE MU15 FO15) as HKE5.
    hideB MU13. hideB WM13. hideB MU15.

    assert (C8F : 4 <= class_size c / 8 /\ class_size c mod 8 = 0) by (clear - GCS CM16; Z.div_mod_to_equations; lia).
    assert (SHUB : sh B <= sh (M + 16) /\ sh (M + 16) + size / 8 <= sh B + class_size c / 8 /\ (size mod 8 <> 0 -> sh (M + 16) + size / 8 + 1 <= sh B + class_size c / 8) /\ 0 <= size / 8).
    { unfold sh, rup8 in *. destruct RZF as (RZa & RZb). clear - EM RZa RZb B8 MR2 MR4 SZR CM16 BLO. Z.div_mod_to_equations. lia. }
    assert (DJ45 : forall A k0, ((B <= A /\ A + k0 <= M) \/ (M + 16 <= A /\ A + k0 <= B + class_size c + 8) \/ (sh B <= A /\ A + k0 <= sh B + class_size c / 8) \/ q - 128 <= A) -> 0 <= k0 ->
              disjoint_from [(M, M + 8)] A k0
              /\ disjoint_from [(q - 128 - 224, q - 128); (DT + 4 * bkt (depot_hash tr), DT + 4 * bkt (depot_hash tr) + 4); (DNI, DNI + 4);
                   (DN0 D + 16 * (zlen hs + 1), DN0 D + 16 * (zlen hs + 1) + 16); (SSA, SSA + 8); (SSD + 8, SSD + 12);
                   (SS0 D + 8 * total, SS0 D + 8 * total + 8 + 8 * Z.of_nat (length tr))] A k0
              /\ disjoint_from [(M + 8, M + 8 + 8)] A k0).
    { intros A k0 HA HK. unfold zlen in *. cbn [disjoint_from].
      clear - HA HK MR1 MR2 MR4 SZR BLO CLO LOQ CS LOH A05 A06 SS1 SS2 N1d N2d SWB G1 G2 G3 G5 G6 G7 ERG CR SP1 SP2 C8F BKR ROOM_N ROOM_F T0. lia. }
    assert (TR45 : forall A cs, rw_cells asegs m3 A cs ->
              ((B <= A /\ A + Z.of_nat (cells_size cs) <= M) \/ (M + 16 <= A /\ A + Z.of_nat (cells_size cs) <= B + class_size c + 8)
               \/ (sh B <= A /\ A + Z.of_nat (cells_size cs) <= sh B + class_size c / 8) \/ q - 128 <= A) -> rw_cells asegs m5 A cs).
    { intros A cs HC0 HA. destruct (DJ45 A (Z.of_nat (cells_size cs)) HA ltac:(clear; lia)) as (D4 & DD & D5).
      eapply (rw_cells_transport asegs _ mD m5); [| exact MU5| exact WM5| exact D5].
      eapply (rw_cells_transport asegs _ m4 mD); [| exact MUD| exact WMD| exact DD].
      eapply (rw_cells_transport asegs _ m3 m4); [exact HC0| exact MU4| exact WM4| exact D4]. }
    unhideB FR. apply TR45 in FR; [| right; right; right; clear; lia].
    unhideB UB. apply TR45 in UB; [| right; left; cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear - SZR; lia); clear - MR2 MR4; lia].
    unhideB SHU. apply TR45 in SHU; [| right; right; left; cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (exact (proj2 (proj2 (proj2 SHUB)))); clear - SHUB; lia].
    assert (SHP5 : size mod 8 <> 0 -> exists bp, rw_cells asegs m5 (sh (M + 16) + size / 8) [C1 bp]).
    { intros NE. destruct (SHP NE) as (bp & PC0). exists bp. apply TR45; [exact PC0|]. right; right; left. cbn [cells_size csize Nat.add].
      destruct SHUB as (SU1 & SU2 & SU3 & SU4). pose proof (SU3 NE) as SU5. clear - SU1 SU4 SU5. lia. }
    assert (LCH5 : B <> M -> exists lj, rw_cells asegs m5 B [CB 16 lj]).
    { intros NE. assert (RZ32 : 32 <= rz) by (destruct RZF as (RZa & RZb); clear - NE EM RZa RZb; Z.div_mod_to_equations; lia).
      unhideB LRZ. assert (LE32 : (16 + Z.to_nat (rz - 32) <= Z.to_nat (rz - 16))%nat) by (clear - RZ32; lia).
      destruct (cb_split3 m3 B (Z.to_nat (rz - 16)) j0 16 (Z.to_nat (rz - 32)) LE32 LRZ) as (lj & _ & _ & LC16 & _ & _).
      exists lj. apply TR45; [exact LC16|]. left. cbn [cells_size csize Nat.add]. clear - EM RZ32. lia. }
    pose proof INV5 as (RP5 & _). pose proof RP5 as (_ & _ & _ & _ & (ts5 & TS5)).
    unhideB HDN. split_chunk HDN 2%nat HDa HDb. hideB HDb.
    assert (BR2 : 6328320 <= B /\ (B = M \/ B + 16 <= M) /\ M mod 8 = 0 /\ M + 16 + size + 8 <= lo).
    { destruct RZF as (RZa & RZb). split; [clear - BLO; lia|]. split; [clear - EM RZa RZb; Z.div_mod_to_equations; lia|]. split; [exact MR3|].
      clear - MR2 MR4 G2 G3 ERG CR SP2 CLO. lia. }
    assert (SZ2 : 1 <= size <= 2^28 /\ size + 16 <= a0_need n <= 2^40) by (destruct RZF as (RZa & _); clear - SZR SZp RZa NP; lia).
    assert (UG2 : M + 16 + size + 8 <= 2147450880 \/ 17594333495296 <= B) by (right; clear - BLO; lia).
    assert (TB2 : THR + 4096 <= B \/ M + 16 + size + 8 <= THR) by (clear - A03 MR2 MR4 G1 G2 G3 ERG CR; lia).
    hideB HDa. hideB FR. hideB UB. hideB SHU. hideB TS5.
    eapply evt_cut.
    { eapply (back2_spec E L gp F_ fc ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (q - 128) lo B M size (a0_need n) m5
               LOH CLO ltac:(clear - LOQ CS; lia) SPRm TLO BR2 SZ2 UG2 TB2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b0 bits1 _ _ _ _ _);
        [ exact MI5 | exact ST5 | exact PE5 | exact AE5 | exact HKE5 | exact TE5 | exact FR | exact HDa | exact B31 | exact LCH5 | exact UB | exact SHU | exact SHP5 | exact TS5 ]. }
    cbv beta. intros msZ PZ. unfold back2_post in PZ.
    destruct PZ as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m6 & m7 & m8 & m9 & mZ & bitsZ & ubZ & tsZ
                    & -> & MS6 & MS7 & MS8 & MS9 & MSZ & STZ & B3Z & HDZ & LCHZ & UBZ & SHZ & SHPZ & TS8 & EQ7 & MUZp).
    destruct MS6 as (MU6 & WM6 & MI6). destruct MS7 as (MU7 & WM7 & MI7). destruct MS8 as (MU8 & WM8 & MI8). destruct MS9 as (MU9 & WM9 & MI9). destruct MSZ as (MUZ & WMZ & MIZ).
    destruct SHUB as (SU1 & SU2 & SU3 & SU4).
    pose proof (SHSTEP m5 m6 _ (sh (M + 16)) (size / 8) (q - 128 - 64) (q - 128) INV5 MU6 WM6 MI6 ltac:(clear - LOQ CS; lia) ltac:(clear; lia) SU1 SU2) as INV6.
    assert (SU6 : sh (M + 16) + size / 8 + 1 <= sh B + class_size c / 8 \/ size mod 8 = 0) by (destruct (Z.eq_dec (size mod 8) 0) as [EZ|NZ]; [right; exact EZ| left; exact (SU3 NZ)]).
    lazymatch type of INV6 with dr_inv _ _ _ ?hh _ _ _ _ => assert (INV7 : dr_inv AL E (P', snd X) hh m7 WB WC ((c, v) :: hrest)) end.
    { destruct (Z.eq_dec (size mod 8) 0) as [EZ|NZ].
      - pose proof (EQ7 EZ) as E76. rewrite E76. exact INV6.
      - exact (SHSTEP m6 m7 _ (sh (M + 16) + size / 8) 1 lo lo INV6 (WK1 _ _ _ _ MU7) WM7 MI7 ltac:(clear; lia) ltac:(clear - LOQ CS; lia)
                 ltac:(clear - SU1 SU4; lia) (SU3 NZ)). }
    pose proof (dr_inv_tstats AL E _ _ m7 m8 WB WC _ lo q (q - 128 - 32) (q - 128) AO LOH CLO ltac:(clear - LOQ CS; lia) ltac:(clear; lia) ltac:(clear; lia)
                  INV7 MU8 WM8 MI8 (ex_intro _ tsZ TS8)) as INV8.
    pose proof (BLKSTEP m8 m9 _ (M + 16) (Z.min size 4096) lo lo INV8 (WK1 _ _ _ _ MU9) WM9 MI9 ltac:(clear; lia) ltac:(clear - LOQ CS; lia)
                  ltac:(clear - MR1; lia) ltac:(clear - MR2 MR4 SZR; lia)) as INV9.
    assert (MUZw : munch [(q - 128 - 32, q - 128); (B, B + (M + 16 - B))] m9 mZ).
    { eapply munch_weaken; [| exact MUZ]. unfold sub_fp. cbn [outside]. intros xo (O1 & O2 & _). split; [exact O1|]. split; [clear - O2 MR1; lia|]. split; [clear - O2 MR1 BR2; lia| exact I]. }
    pose proof (BLKSTEP m9 mZ _ B (M + 16 - B) (q - 128 - 32) (q - 128) INV9 MUZw WMZ MIZ ltac:(clear - LOQ CS; lia) ltac:(clear; lia)
                  ltac:(clear; lia) ltac:(clear - MR2 MR4 SZR; lia)) as INVZ.
    clear INV6 INV7 INV8 INV9.

    assert (SHF : sh (M + 16) = sh B + rz / 8 /\ sh (M + 16 + rup8 size) = sh (M + 16) + rup8 size / 8 /\ size / 8 <= rup8 size / 8
                  /\ (size mod 8 <> 0 -> size / 8 + 1 <= rup8 size / 8) /\ 0 <= rz / 8 /\ sh (M + 16) + rup8 size / 8 <= sh B + class_size c / 8).
    { unfold sh, rup8 in *. destruct RZF as (RZa & RZb). clear - EM RZa RZb B8 MR2 MR4 SZR CM16 BLO. Z.div_mod_to_equations. lia. }
    destruct SHF as (SF1 & SF2 & SF3 & SF4 & SF5 & SF6).
    assert (SHBB : 2147450880 <= sh B /\ sh B + class_size c / 8 <= 17594333495296) by (clear - G5 G6 G7; lia).
    assert (TB3 : THR + 4096 <= B \/ B + class_size c <= THR) by (clear - A03 G1 G2 G3 ERG CR; lia).
    assert (TR5Z : forall A cs, rw_cells asegs m5 A cs ->
              ((B + 16 <= A /\ A + Z.of_nat (cells_size cs) <= M /\ B <> M) \/ (M + 2 <= A /\ A + Z.of_nat (cells_size cs) <= M + 16)
               \/ (M + 16 + size <= A /\ A + Z.of_nat (cells_size cs) <= B + class_size c)
               \/ (sh B <= A /\ A + Z.of_nat (cells_size cs) <= sh B + rz / 8)
               \/ (sh (M + 16) + rup8 size / 8 <= A /\ A + Z.of_nat (cells_size cs) <= sh B + class_size c / 8)) -> rw_cells asegs mZ A cs).
    { intros A cs HC0 HA. remember (Z.of_nat (cells_size cs)) as k0 eqn:Ek0. assert (K0 : 0 <= k0) by (rewrite Ek0; clear; lia).
      assert (H6 : rw_cells asegs m6 A cs).
      { eapply (rw_cells_transport asegs _ m5 m6); [exact HC0| exact MU6| exact WM6|]. rewrite <- Ek0. cbn [disjoint_from].
        clear - HA K0 SF1 SF3 SF6 SU4 SHBB BLO MR1 MR2 MR4 SZR LOH LOQ CS CLO. lia. }
      assert (H7 : rw_cells asegs m7 A cs).
      { destruct (Z.eq_dec (size mod 8) 0) as [EZ|NZ]; [rewrite (EQ7 EZ); exact H6|].
        eapply (rw_cells_transport asegs _ m6 m7); [exact H6| exact MU7| exact WM7|]. rewrite <- Ek0. cbn [disjoint_from]. pose proof (SF4 NZ) as SF4'.
        clear - HA K0 SF1 SF4' SF6 SU4 SHBB BLO MR1 MR2 MR4 SZR. lia. }
      assert (H8 : rw_cells asegs m8 A cs).
      { eapply (rw_cells_transport asegs _ m7 m8); [exact H7| exact MU8| exact WM8|]. rewrite <- Ek0. cbn [disjoint_from].
        clear - HA K0 SF1 SF3 SU4 SF5 SF6 SHBB BLO MR1 MR2 MR4 SZR LOH LOQ CS CLO TB3 T3 T4 ACR. lia. }
      assert (H9 : rw_cells asegs m9 A cs).
      { eapply (rw_cells_transport asegs _ m8 m9); [exact H8| exact MU9| exact WM9|]. rewrite <- Ek0. cbn [disjoint_from].
        clear - HA K0 SF1 SF3 SU4 SF5 SF6 SHBB BLO MR1 MR2 MR4 SZR. lia. }
      destruct (Z.eq_dec B M) as [EBM|NBM].
      - eapply (rw_cells_transport asegs _ m9 mZ); [exact H9| exact (MUZp EBM)| exact WMZ|]. rewrite <- Ek0. cbn [disjoint_from].
        clear - HA K0 EBM SF1 SF3 SU4 SF5 SF6 SHBB BLO MR1 MR2 MR4 SZR LOH LOQ CS CLO. lia.
      - eapply (rw_cells_transport asegs _ m9 mZ); [exact H9| exact MUZ| exact WMZ|]. rewrite <- Ek0. cbn [disjoint_from].
        clear - HA K0 NBM BR2 SF1 SF3 SU4 SF5 SF6 SHBB BLO MR1 MR2 MR4 SZR LOH LOQ CS CLO. lia. }

    assert (LREP : lchunk_rep AL mZ (mkQC (QPrim c v) rz size)).
    { unfold lchunk_rep. cbn [qc_kind qc_rz qc_n]. unfold qc_hdr, qc_blk, qc_bsize. cbn [qc_kind qc_rz]. rewrite <- EB.
      replace (B + rz - 16) with M by (clear - EM; lia).
      split.
      { exists bitsZ, actx. split; [exact B3Z|]. unhideB HDb. unhideB ACX. change (Z.of_nat 2) with 2 in HDb.
        apply (hdr_join mZ M bitsZ size actx HDZ).
        - apply TR5Z; [exact HDb|]. right; left. cbn [cells_size csize Nat.add]. clear; lia.
        - apply TR5Z; [exact ACX|]. right; left. cbn [cells_size csize Nat.add]. clear; lia. }
      split.
      { intros RZ16. assert (NBM : B <> M) by (clear - RZ16 EM; lia). split; [exact (LCHZ NBM)|].
        assert (LE32 : (16 + Z.to_nat (rz - 32) <= Z.to_nat (rz - 16))%nat) by (clear - RZ16 RZF; destruct RZF as (_ & RZb); Z.div_mod_to_equations; lia).
        unhideB LRZ. destruct (cb_split3 m3 B (Z.to_nat (rz - 16)) j0 16 (Z.to_nat (rz - 32)) LE32 LRZ) as (_ & lr & _ & _ & LRest & _).
        exists lr. change (Z.of_nat 16) with 16 in LRest. apply TR5Z; [apply TR45; [exact LRest|]|].
        - left. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (clear - RZ16 RZF; destruct RZF as (_ & RZb); Z.div_mod_to_equations; lia). clear - EM. lia.
        - left. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (clear - RZ16 RZF; destruct RZF as (_ & RZb); Z.div_mod_to_equations; lia). clear - EM NBM. lia. }
      split; [exists ubZ; exact UBZ|].
      split.
      { exists sl. unhideB SLK. replace (M + 16 + size) with (M + 16 + size) by reflexivity.
        assert (SLN : 0 <= class_size c - rz - size) by (clear - MR2 MR4 EM; lia).
        apply TR5Z; [apply TR45; [exact SLK|]|].
        - right; left. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by exact SLN. clear - EM SZR. lia.
        - right; right; left. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by exact SLN. clear - EM. lia. }
      split.
      { unhideB SHL. apply TR5Z; [apply TR45; [exact SHL|]|].
        - right; right; left. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by exact SF5. clear - SF1 SF3 SF6 SU4. lia.
        - right; right; right; left. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by exact SF5. clear. lia. }
      split; [exact (block_shadow_cells mZ (sh (M + 16)) size ltac:(clear - SZR; lia) SHZ SHPZ)|].
      split; [| exact I].
      unhideB SHR. assert (SRN : 0 <= (class_size c - rz - rup8 size) / 8) by (apply Z.div_pos; [clear - FIT; lia| clear; lia]).
      assert (SRE : sh (M + 16) + rup8 size / 8 + (class_size c - rz - rup8 size) / 8 = sh B + class_size c / 8).
      { unfold sh, rup8 in *. destruct RZF as (RZa & RZb). clear - EM RZa RZb B8 MR2 MR4 SZR CM16. Z.div_mod_to_equations. lia. }
      apply TR5Z; [apply TR45; [exact SHR|]|].
      - right; right; left. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by exact SRN. rewrite SF2. clear - SRE SF1 SF3 SF5 SU4. lia.
      - right; right; right; right. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by exact SRN. rewrite SF2. clear - SRE. lia. }

    pose proof (munch_joinP _ _ _ _ _ MU6 MU7) as MUa. pose proof (munch_joinP _ _ _ _ _ MUa MU8) as MUb. pose proof (munch_joinP _ _ _ _ _ MUb MU9) as MUc.
    pose proof (munch_joinP _ _ _ _ _ MUc MUZ) as MU5Z. cbn [app] in MU5Z. clear MUa MUb MUc.
    assert (SHB8 : sh B + class_size c / 8 + 8 <= 17594333495296) by (rewrite <- G5; unfold sh, SHADOW_OFF; clear - BLO ACR; Z.div_mod_to_equations; lia).
    assert (RDZ : RDEPOT D hs' total' mZ).
    { eapply RDEPOT_frame_m; [exact DLO| exact SWB| exact RD5| exact MU5Z| | |]; cbn [disjoint_from].
      - clear - LOQ CS LOH SHB8 SHBB SU1 SU2 SU4 SF1 SF3 SF6 BLO MR1 MR2 MR4 SZR T3 BR2. lia.
      - clear - LOQ CS CLO N1d N2d SHB8 SHBB SU1 SU2 SU4 SF1 SF3 SF6 BLO MR1 MR2 MR4 SZR A05 A35 G1 G2 G3 ERG CR BR2. lia.
      - clear - LOQ CS CLO SS1 SS2 SHB8 SHBB SU1 SU2 SU4 SF1 SF3 SF6 BLO MR1 MR2 MR4 SZR A06 A36 G1 G2 G3 ERG CR BR2. lia. }

    unhideB MU12. unhideB WM12. unhideB MU3. unhideB WM3.
    lazymatch type of MU3 with munch ?w _ _ => change w with (prim_W AL lo (q - 128) c k (get_cls P' c)) in MU3 end.
    assert (MU7c : munch (if size mod 8 =? 0 then [] else [(sh (M + 16) + size / 8, sh (M + 16) + size / 8 + 1)]) m6 m7).
    { destruct (Z.eqb_spec (size mod 8) 0) as [EZ|NZ]; [rewrite (EQ7 EZ); apply munch_refl| exact MU7]. }
    pose proof (munch_joinP _ _ _ _ _ MU12 MU3) as J1. pose proof (munch_joinP _ _ _ _ _ J1 MU4) as J2. pose proof (munch_joinP _ _ _ _ _ J2 MUD) as J3.
    pose proof (munch_joinP _ _ _ _ _ J3 MU5) as J4. pose proof (munch_joinP _ _ _ _ _ J4 MU6) as J5. pose proof (munch_joinP _ _ _ _ _ J5 MU7c) as J6.
    pose proof (munch_joinP _ _ _ _ _ J6 MU8) as J7. pose proof (munch_joinP _ _ _ _ _ J7 MU9) as J8. pose proof (munch_joinP _ _ _ _ _ J8 MUZ) as MUfin.
    clear J1 J2 J3 J4 J5 J6 J7 J8.
    pose proof (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _
                 (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _ WM12 WM3) WM4) WMD) WM5) WM6) WM7) WM8) WM9) WMZ) as WMfin.
    set (cls := fun iv : Z * Z => atouch AL lo q P (snd X) [] [] iv \/ chunk_iv AL c v iv \/ chunk_sh_iv AL c v iv \/ dstat iv \/ dreg AL iv).
    assert (CST : forall a b, lo <= a -> b <= q -> cls (a, b)) by (intros a b Ha Hb; left; left; unfold sub_iv; cbn [fst snd]; lia).
    assert (CBL : forall a b, B <= a -> b <= B + class_size c -> cls (a, b)) by (intros a b Ha Hb; right; left; unfold chunk_iv; cbn [fst snd]; rewrite <- EB; lia).
    assert (CSH : forall a b, sh B <= a -> b <= sh B + class_size c / 8 -> cls (a, b)) by (intros a b Ha Hb; right; right; left; unfold chunk_sh_iv; cbn [fst snd]; rewrite <- EB; lia).
    lazymatch type of MUfin with munch ?w _ _ => assert (FCLS : Forall cls w) end.
    { repeat (apply Forall_app; split).
      - repeat (apply Forall_cons || apply Forall_nil); apply CST; clear - LOQ CS; lia.
      - pose proof WFk as (K1 & _ & _ & _ & K5 & _ & K7 & K8 & _). pose proof (WFN c ltac:(clear - CR; lia)) as (D1 & _ & _ & _ & D5 & _ & D7 & D8 & _).
        eapply Forall_impl; [| eapply (Forall_atouch_mono AL lo q P (snd X) [] [] lo (q - 128) P (snd X) [] []);
          [clear; lia| clear; lia| intros c0 _; clear; lia| apply incl_refl| apply incl_refl| apply incl_refl|
           apply atouch_prim_W; [clear - CR; lia| rewrite <- Ek; clear - K7; lia| clear - D8; lia| clear - K1; lia| clear - D1; lia| clear - D5; lia| clear - K5; lia| rewrite <- Ek; clear - K7 K8; lia]]].
        intros iv AT. left. exact AT.
      - repeat (apply Forall_cons || apply Forall_nil). apply CBL; clear - MR1 MR2 MR4 SZR; lia.
      - unfold zlen in *. repeat (apply Forall_cons || apply Forall_nil).
        + apply CST; clear - LOQ CS; lia.
        + right; right; right; left. unfold dstat. cbn [fst snd]. clear - BKR. lia.
        + right; right; right; left. unfold dstat. cbn [fst snd]. clear. lia.
        + right; right; right; right. unfold dreg. cbn [fst snd]. left. clear - ROOM_N. lia.
        + right; right; right; left. unfold dstat. cbn [fst snd]. clear. lia.
        + right; right; right; left. unfold dstat. cbn [fst snd]. clear. lia.
        + right; right; right; right. unfold dreg. cbn [fst snd]. right. clear - ROOM_F SWB T0. lia.
      - repeat (apply Forall_cons || apply Forall_nil). apply CBL; clear - MR1 MR2 MR4 SZR; lia.
      - repeat (apply Forall_cons || apply Forall_nil); [apply CST; clear - LOQ CS; lia| apply CSH; [exact SU1| exact SU2]].
      - destruct (Z.eqb_spec (size mod 8) 0) as [EZ|NZ]; [apply Forall_nil|]. repeat (apply Forall_cons || apply Forall_nil). apply CSH; [clear - SU1 SU4; lia| exact (SU3 NZ)].
      - repeat (apply Forall_cons || apply Forall_nil); [apply CST; clear - LOQ CS; lia|]. left. right; right; left. unfold sub_iv. cbn [fst snd]. clear. lia.
      - repeat (apply Forall_cons || apply Forall_nil). apply CBL; clear - MR1 MR2 MR4 SZR; lia.
      - repeat (apply Forall_cons || apply Forall_nil); [apply CST; clear - LOQ CS; lia| apply CBL; clear - MR1 MR2 MR4 SZR; lia| apply CBL; [clear; lia| clear - GCS; lia]]. }

    replace (q - 128 + 128) with q in * by (clear; lia).
    pose proof (al_cls_eq n (proj1 NR) NP) as CLSEQ.
    subst M. subst B. subst rz. subst size. subst k. subst v. subst P'. subst c. subst P.
    lz_ret. apply evt_done. unfold allocate_post_p. cbv zeta.
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, mZ, _, hs', total'.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact MUfin|]. split; [exact WMfin|]. split; [exact FCLS|].
    split; [exact INVZ|]. split; [exact WFch|]. split; [exact HELD|]. split; [exact LREP|]. split; [exact STZ|].
    split; [exact CR|]. split; [exact CLSEQ|]. split; [exact V0|]. split; [exact VAU|]. split; [exact VAL|]. split; [exact RDZ| exact RES].
  Qed.
End ALLOCP.

