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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ LJU PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimPopLens APrimQ APrimFrame AFrameM
                        APrimDealloc ASec ASecD AQuar AQuarM AHeap AFoot F_prim_refill F_prim_cdealloc F_poison F_quar_Ep F_quar_E F_quar_A AQuarR AQuarS AQuarP ATacFix
                        AQuarT F_depot F_hooks F_prim_calloc2 F_alloc_env F_alloc_A F_alloc_B AAllocEnvF F_alloc_P.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition asan_malloc_entry : Z := 0x335fc.
Definition AMALLOC_STACK : Z := 16 + ALLOC_STACK.

Section AMALLOC.
  Context {HC : HasCeiling}.
  Variables (AL : alayout) (E : penv).
  Notation L := (al_thread AL).
  Notation D := (al_depot AL).
  Notation THR := (at_thr (al_thread AL)).
  Hypothesis AO : alayout_ok AL.

  #[using="AO"] Lemma alloc_W_above : forall (X : pstate) (m : mem) lo q c v W A k,
    0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q ->
    RPRIM AL (fst X) m -> RSEC AL (snd X) m -> 1 <= c <= 31 -> 0 <= v -> 16 * v + class_size c <= FA_OFF ->
    Forall (fun iv => atouch AL lo q (fst X) (snd X) [] [] iv \/ chunk_iv AL c v iv \/ chunk_sh_iv AL c v iv \/ dstat iv \/ dreg AL iv) W ->
    q <= A -> disjoint_from W A k.
  Proof.
    intros X m lo q c v W A k LOH CLO LQ RP RS Hc V0 V1 FW HA.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
    layout_facts AO 5%nat LDN. destruct LDN as (N1d & N2d & _). layout_facts AO 6%nat LSS. destruct LSS as (S1d & S2d & _).
    pose proof (region_range AL c Hc) as [RN1 RN2]. assert (RG : region AL c = al_space AL + c * K_REGION) by reflexivity.
    pose proof (class_size_pos c Hc) as CSP.
    induction FW as [|[a b] W' HIV FW' IH]; cbn [disjoint_from]; [exact I|]. split; [| exact IH].
    destruct HIV as [AT|[CI|[CI|[DS|DR]]]].
    - assert (FA1 : Forall (atouch AL lo q (fst X) (snd X) [] []) [(a, b)]) by (constructor; [exact AT| constructor]).
      assert (TS0 : incl (@nil schunk) (se_chunks (snd X))) by (intros d []).
      assert (TC0 : Forall (held1 (fst X)) []) by constructor.
      pose proof (atouch_above AL X m lo q [(a, b)] [] [] A k AO LOH CLO LQ RP RS TC0 TS0 FA1 HA) as DD.
      cbn [disjoint_from] in DD. exact (proj1 DD).
    - unfold chunk_iv in CI. cbn [fst snd] in CI. clear - CI V0 V1 RN1 RN2 RG SP1 SP2 SP5 HA CLO LQ Hc. lia.
    - assert (BBR : 0 <= region AL c + 16 * v /\ region AL c + 16 * v + class_size c <= 2^47) by (clear - V0 V1 RN1 RN2 RG SP1 SP5 Hc CSP; lia).
      unfold chunk_sh_iv in CI. cbn [fst snd] in CI. unfold sh, SHADOW_OFF in CI. clear - CI BBR HA LOH LQ CSP. Z.div_mod_to_equations. lia.
    - unfold dstat in DS. cbn [fst snd] in DS. clear - DS HA LOH LQ. lia.
    - unfold dreg in DR. cbn [fst snd] in DR. clear - DR HA N2d S2d CLO LQ. lia.
  Qed.

  Variables (gp : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q lo : Z).
  Hypothesis LOH : 0x10007fff8000 <= lo.
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis LOQ : lo <= q - AMALLOC_STACK.
  Hypothesis QH : q <= 2^47.
  Hypothesis Q16 : q mod 16 = 0.

  Definition amalloc_post_p (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (X : pstate) (H : word -> bool) (m : mem) (n : Z)
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
          \/ (dfind hs (depot_hash tr) = 0 /\ hs' = hs ++ [depot_hash tr] /\ total' = total + Z.of_nat (length tr) + 1))
      /\ (forall A k, q <= A -> disjoint_from W A k).

  #[using="AO LOH CLO LOQ QH Q16"] Theorem asan_malloc_prim_spec : forall (ra t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
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
      (amalloc_post_p ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X H m n WB WC hrest hs total tr)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz n) (wz STK) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz asan_malloc_entry) fc None m (seg_rom asegs)).
  Proof.
    intros ra t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 X H m n WB WC hrest STK TR total hs ws tr
      MC ST INV NR NP RB CA0 CM0 CM1 AE TE2 HKE RD SOBJ QSTK STKH BUF TRW LENW LTR RNG QTR TRH ROOM_N ROOM_F ROOM_T.
    unfold asan_malloc_entry.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (AS : 128 <= ALLOC_STACK) by (vm_compute; discriminate). unfold AMALLOC_STACK in LOQ.
    pose proof AO as (_ & _ & _ & TLO & DLO & SWB). pose proof TLO as (T1 & T2 & T3 & T4 & _).
    layout_facts AO 5%nat LDN. destruct LDN as (_ & N2d & _). layout_facts AO 6%nat LSS. destruct LSS as (_ & S2d & _).
    pose proof (munch_refl [(q - 16, q)] m) as MU0. pose proof (wmono_refl asegs m) as WM0.
    pose proof INV as (_ & _ & _ & MI & _).
    lz_go.
    assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; clear - QH LOQ LOH AS; lia).
    rewrite <- EQ in ST. carve_frame 16%nat ST. rewrite !EQ in *.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.

    replace (q - 16) with (q + -16) in MU0 by (clear; lia).
    assert (INV0 : dr_inv AL E X H m0 WB WC hrest).
    { eapply (dr_inv_frame_d AL E X H m m0 WB WC hrest lo _ AO LOH CLO INV MU0 WM0); [assumption|]. constructor; [| constructor]. unfold dzone. cbn [fst snd]. left. clear - LOQ AS. lia. }
    assert (FO0 : Forall aenv_out [(q + -16, q)]) by (constructor; [unfold aenv_out; cbn [fst snd]; clear - LOQ AS LOH; lia| constructor]).
    pose proof (alloc_env_frame_m _ m m0 AE MU0 FO0) as AE0. pose proof (hooks_env_frame_m _ m m0 HKE MU0 FO0) as HKE0.
    assert (TE20 : thread_env2 AL m0).
    { eapply thread_env2_frame_m; [exact TE2| exact MU0| |]; cbn [disjoint_from]; [clear - LOQ AS CLO T4; lia| clear - LOQ AS CLO T2; lia]. }
    assert (RD0 : RDEPOT D hs total m0).
    { eapply RDEPOT_frame_m; [exact DLO| exact SWB| exact RD| exact MU0| | |]; cbn [disjoint_from]; [clear - LOQ AS LOH; lia| clear - LOQ AS CLO N2d; lia| clear - LOQ AS CLO S2d; lia]. }
    do 8 zstep.
    assert (LOQ' : lo <= q + -16 - ALLOC_STACK) by (clear - LOQ; lia).
    assert (QH' : q + -16 <= 2^47) by (clear - QH; lia).
    assert (Q16' : (q + -16) mod 16 = 0) by (clear - Q16; Z.div_mod_to_equations; lia).
    lazymatch goal with |- evt _ (lzk _ ?t _) _ => rewrite <- (ebind_ret_r t) end.
    lz_here.
    eapply implA_ebind.
    { eapply implA_mclean; [exact MC|].
      eapply (allocate_prim_spec AL E AO gp F_ fc (q + -16) lo LOH CLO LOQ' QH' Q16' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X H m0 n WB WC hrest STK TR total hs ws tr);
        [ exact MC | exact ST | exact INV0 | exact NR | exact NP | exact RB | exact CA0 | exact CM0 | exact CM1 | exact AE0 | exact TE20 | exact HKE0 | exact RD0
        | assumption | clear - QSTK; lia | exact STKH | assumption | exact TRW | exact LENW | exact LTR | exact RNG | clear - QTR; lia | exact TRH | exact ROOM_N | exact ROOM_F | exact ROOM_T ]. }
    intros r H' ms' [PO MC']. unfold allocate_post_p in PO. cbv zeta in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m' & W & hs' & total'
                    & -> & -> & MUW & WMW & FW & INVW & WFC & HK & LREP & STW & CR & CLSEQ & V0 & VAU & VAL & RDW & RES).
    clean_ms_mem MC'. lz_cont MC'.
    replace (ret_pc (Z_to_bv 64 210472)) with (Z_to_bv 64 210472) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    pose proof INV0 as (RP0 & _ & RS0 & _). pose proof INVW as (RPW & _ & RSW & _).
    destruct (clear_ctx AL _ m' RPW RSW) as (WFW & _ & _). cbn [fst] in WFW.
    pose proof (WFW (class_of (a0_need n)) ltac:(clear - CR; lia)) as (_ & _ & _ & _ & _ & _ & K7 & K8 & _).
    assert (V1 : 16 * snd (cache_alloc (fst X) (class_of (a0_need n))) + class_size (class_of (a0_need n)) <= FA_OFF) by (clear - VAU K7 K8; lia).
    assert (LQ0 : lo <= q + -16) by (clear - LOQ AS; lia). assert (HC31 : 1 <= class_of (a0_need n) <= 31) by (clear - CR; lia). assert (QQ : q + -16 <= q + -16) by (clear; lia).
    pose proof (alloc_W_above X m0 lo (q + -16) (class_of (a0_need n)) (snd (cache_alloc (fst X) (class_of (a0_need n)))) W (q + -16) 16 LOH CLO LQ0 RP0 RS0 HC31 V0 V1 FW QQ) as DJF.
    eapply (rw_cells_transport asegs _ m0 m') in FR; [| exact MUW| exact WMW| exact DJF].
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & _ & _ & _ & SP5 & _ & _).
    assert (UPOS : 0 < qc_hdr AL (al_chunk_p (fst X) n) + 16 < 2^47).
    { unfold qc_hdr, qc_blk, al_chunk_p. cbn [qc_kind qc_rz]. pose proof (region_range AL (class_of (a0_need n)) ltac:(clear - CR; lia)) as [RN1 RN2].
      assert (RG : region AL (class_of (a0_need n)) = al_space AL + class_of (a0_need n) * K_REGION) by reflexivity.
      destruct WFC as (RZa & _ & N1c & FITc & _). unfold al_chunk_p in RZa, N1c, FITc. cbn [qc_rz qc_n qc_bsize qc_kind] in RZa, N1c, FITc. unfold rup8 in FITc.
      clear - RN1 RN2 RG SP1 SP5 V0 V1 RZa N1c FITc CR. Z.div_mod_to_equations. lia. }
    remember (qc_hdr AL (al_chunk_p (fst X) n) + 16) as UA eqn:EUA.
    zstep. if_cases KZ; zify_cond KZ. { exfalso. clear - KZ UPOS. lia. } clear KZ.
    zstep. zstep. zstep.
    replace (q + -16 + 16) with q by (clear; lia).
    zstep.
    release_frame FR STW q.
    lz_ret. apply evt_done. unfold amalloc_post_p. cbv zeta. subst UA.
    eexists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, m', ((q + -16, q) :: W), hs', total'.
    split; [reflexivity|]. split; [reflexivity|].
    split; [exact (munch_joinP _ _ _ _ _ MU0 MUW)|]. split; [exact (wmono_trans asegs _ _ _ WM0 WMW)|].
    split.
    { constructor; [left; left; unfold sub_iv; cbn [fst snd]; clear - LOQ AS; lia|].
      eapply Forall_impl; [| exact FW]. intros iv [AT|R]; [left| right; exact R].
      eapply (atouch_mono AL lo q (fst X) (snd X) [] [] lo (q + -16) (fst X) (snd X) [] []); [clear; lia| clear; lia| intros c0 _; clear; lia| apply incl_refl| apply incl_refl| apply incl_refl| exact AT]. }
    split; [exact INVW|]. split; [exact WFC|]. split; [exact HK|]. split; [exact LREP|]. split; [exact STW|].
    split; [exact CR|]. split; [exact CLSEQ|]. split; [exact V0|]. split; [exact VAU|]. split; [exact VAL|]. split; [exact RDW|]. split; [exact RES|].
    intros A k HA. cbn [disjoint_from]. split; [clear - HA; lia|].
    exact (alloc_W_above X m0 lo (q + -16) (class_of (a0_need n)) (snd (cache_alloc (fst X) (class_of (a0_need n)))) W A k LOH CLO LQ0 RP0 RS0 HC31 V0 V1 FW ltac:(clear - HA; lia)).
  Qed.
End AMALLOC.
