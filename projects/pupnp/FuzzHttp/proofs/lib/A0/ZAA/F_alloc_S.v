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
                        AQuarT F_gct F_depot F_depot_C F_prim_L0 F_hooks F_prim_calloc2 F_sec_A F_alloc_env F_alloc_A F_alloc_B F_alloc_C AAllocInv AAllocCarve AAllocEnvF F_alloc_P
                        AFrameG AQuarG AAllocInvS AAllocCarveS F_alloc_S1 F_alloc_S2.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section ALLOCS.
  Context {HC : HasCeiling}.
  Variables (AL : alayout) (E : penv).
  Notation L := (al_thread AL).
  Notation D := (al_depot AL).
  Notation THR := (at_thr (al_thread AL)).
  Notation PARR := (al_parr AL).
  Hypothesis AO : alayout_ok AL.
  Variables (gp : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q lo : Z).
  Hypothesis LOH : 0x10007fff8000 <= lo.
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis LOQ : lo <= q - ALLOC_STACK.
  Hypothesis QH : q <= 2^47.
  Hypothesis Q16 : q mod 16 = 0.

  Definition salloc_iv (X : pstate) (a n : Z) (iv : Z * Z) : Prop :=
    atouch AL lo q (fst X) (snd X) [] [] iv
    \/ sub_iv a (a + sec_msize (al_sneed n)) iv
    \/ sub_iv (swlo a) (swhi a (sec_msize (al_sneed n))) iv
    \/ sub_iv (swlo (PARR + 8 * se_nres (snd X))) (swhi (PARR + 8 * se_nres (snd X)) K_PARR_STEP) iv
    \/ dstat iv \/ dreg AL iv.
  Definition salloc_giv (X : pstate) (a n : Z) (iv : Z * Z) : Prop :=
    atouch AL lo q (fst X) (snd X) [] [] iv
    \/ sub_iv a (a + sec_msize (al_sneed n)) iv
    \/ sub_iv (sh a) (sh a + sec_msize (al_sneed n) / 8) iv
    \/ dstat iv \/ dreg AL iv.

  Definition allocate_post_s (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (X : pstate) (H : word -> bool) (m : mem) (n : Z)
      (WB : list qbatch) (WC : list qchunk) (hrest : list (Z * Z)) (hs : list Z) (total : Z) (tr : list Z) (avoid : list (Z * Z))
      : Z -> (word -> bool) -> machine_state -> Prop :=
    fun a H' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' W Wg hs' total',
      let S := snd X in let sc := al_schunk a n in let ch := al_chunk_s a n in let X' := (fst X, sec_alloc S a (al_sneed n)) in
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz (qc_hdr AL ch + 16)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ H' = sec_alloc_H AL S (al_sneed n) a H
      /\ munch W m m' /\ wmono asegs m m' /\ Forall (salloc_iv X a n) W
      /\ gmunch Wg m m' /\ Forall (salloc_giv X a n) Wg
      /\ dr_inv AL E X' H' m' WB WC (prim_of ch ++ hrest)
      /\ qchunk_wf ch /\ held_kind X' ch /\ lchunk_rep AL m' ch
      /\ stk asegs m' lo q
      /\ se_chunks (snd X') = se_chunks S ++ [sc] /\ se_n (snd X') = se_n S + 1 /\ chunk_ok AL sc
      /\ a mod 4096 = 0 /\ 0x609000 <= a /\ app_mem a (sc_msize sc) /\ anon_place a (sc_msize sc)
      /\ Forall (fun iv => a + sc_msize sc <= fst iv \/ snd iv <= a) avoid
      /\ qc_rz ch + rup8 (qc_n ch) + 16 <= qc_bsize ch
      /\ a0_cls (qc_n ch) = 0
      /\ RDEPOT D hs' total' m'
      /\ ((dfind hs (depot_hash tr) <> 0 /\ hs' = hs /\ total' = total)
          \/ (dfind hs (depot_hash tr) = 0 /\ hs' = hs ++ [depot_hash tr] /\ total' = total + Z.of_nat (length tr) + 1)).

  #[using="AO LOH CLO LOQ QH Q16"] Theorem allocate_sec_spec : forall (ra t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
        (X : pstate) (H : word -> bool) (m : mem) (n : Z) (WB : list qbatch) (WC : list qchunk) (hrest : list (Z * Z))
        (STK TR total : Z) (hs : list Z) (ws : list word) (tr : list Z) (avoid : list (Z * Z)) (alo ahi : Z),
    mclean H m -> stk asegs m lo q ->
    dr_inv AL E X H m WB WC hrest ->
    0 <= n <= A0_MAXREQ -> 65536 < a0_need n ->
    In (alo, ahi) avoid -> alo <= lo -> q <= ahi ->
    Forall (fun rg : Z * Z => In (fst rg, fst rg + snd rg) avoid) (al_regions AL) ->
    Forall (fun c => In (sc_beg c, sc_beg c + sc_msize c) avoid) (se_chunks (snd X)) -> se_n (snd X) < K_MAX_CHUNKS ->
    alloc_env m -> thread_env2 AL m -> hooks_env m -> RDEPOT D hs total m ->
    rw_cells asegs m STK [C8 (wz TR); C8 (wz (Z.of_nat (length tr)))] -> q <= STK -> STK + 16 <= 2^47 ->
    u64arr asegs m TR ws -> firstn (length tr) ws = map wz tr -> (length tr <= length ws)%nat -> (1 <= length tr <= 30)%nat ->
    Forall (fun x => 0 <= x < 2^64) tr -> q <= TR -> TR + 8 * Z.of_nat (length ws) <= 2^47 ->
    16 * (zlen hs + 2) <= 2^20 -> 8 * (total + Z.of_nat (length tr) + 1) <= SWIN D -> total + Z.of_nat (length tr) + 1 < 2^20 ->
    implA H (sec_alloc_tree AL (snd X) (al_sneed n) avoid)
      (allocate_post_s ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X H m n WB WC hrest hs total tr avoid)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz INSTANCE) (wz n) (wz 8) (wz STK) (wz 1) (wz 1) a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz allocate_entry) fc None m (seg_rom asegs)).
  Proof.
    intros ra t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 X H m n WB WC hrest STK TR total hs ws tr avoid alo ahi
      MC ST INV NR NS AIN ALO AHI AREG ACH WMAX AE TE2 HKE RD SOBJ QSTK STKH BUF TRW LENW LTR RNG QTR TRH ROOM_N ROOM_F ROOM_T.

    unfold allocate_entry.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (CS : 880 <= ALLOC_STACK) by (vm_compute; discriminate).
    pose proof INV as (RP & POK & RS & MI & PE & TE & SV & WFS & REPS & HKS & HOK & NDS & BWF & BREP).
    pose proof AO as (_ & _ & _ & TLO & DLO & SWB). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & _).
    destruct (al_sec_facts n NR NS) as (N1 & EALN & ERZ & EPR & ENEED & ECLS & (rk & NEED & RK & ER8)).
    assert (RZF : 16 <= al_rz n <= 2048 /\ al_rz n mod 16 = 0) by (rewrite ERZ; split; [clear; lia| reflexivity]).

    lz_go.
    pose proof TE as TE'. te_split TE'.
    callk (front_spec gp F_ fc q lo n STK CLO ltac:(clear - LOQ CS; lia) QH Q16 NR ltac:(clear - QSTK STKH QH LOQ CS ACR CLO; lia));
      [ exact ST | exact MI | exact TE_inited | exact AE | ].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    rename MUk into MU1, WMk into WM1. hideB MU1. hideB WM1.
    lazymatch goal with HS : stk asegs m1 _ _ |- _ => rename HS into ST1 end. lazymatch goal with HM : mem_inv asegs m1 |- _ => rename HM into MI1 end.
    lazymatch goal with HF : rw_cells asegs m1 (q - 128) _ |- _ => rename HF into FR end.

    rewrite ENEED.

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
    rewrite EPR.

    unhideB MU1. unhideB WM1. unhideB MU2. unhideB WM2.
    pose proof (munch_joinP _ _ _ _ _ MU1 MU2) as MU12. cbn [app] in MU12. pose proof (wmono_trans asegs _ _ _ WM1 WM2) as WM12.
    assert (INV2 : dr_inv AL E X H m2 WB WC hrest).
    { eapply (dr_inv_frame_d AL E X H m m2 WB WC hrest lo _ AO LOH CLO INV MU12 WM12 MI2).
      repeat (apply Forall_cons || apply Forall_nil); unfold dzone; cbn [fst snd]; left; clear - LOQ CS; lia. }
    hideB MU1. hideB WM1. hideB MU2. hideB WM2. hideB MU12. hideB WM12.
    pose proof INV2 as (RP2 & POK2 & RS2 & _ & PE2 & _ & SV2 & _).
    pose proof RP2 as (_ & _ & _ & _ & (ts2 & TS2)).
    clear TE_tsd TE_inited TE_tp TE_ctx TE_thr TE_bounds TE_sw TE_unw TE_gotpg TE_pg.
    assert (SNR : 65536 < al_sneed n /\ al_sneed n mod 8 = 0 /\ al_sneed n <= 2^40 /\ al_sneed n = 8 * rk + 4096).
    { unfold al_sneed. rewrite ERZ, NEED. unfold A0_MAXREQ in NR. clear - NR RK N1. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; lia. }
    destruct SNR as (SN1 & SN2 & SN3 & SN4).
    rewrite <- (ebind_ret_r (sec_alloc_tree AL (snd X) (al_sneed n) avoid)).
    hideB FR. hideB SOBJ. hideB BUF.
    callAk (calloc_sec_spec E AL _ gp _ _ _ _ _ _ _ _ _ _ _ _ F_ fc (q - 128) lo (al_sneed n) m2 H (snd X) avoid _ _ _ _ _ _ _ _ _ _ _ _ ts2 alo ahi MI2) unfolding (fun h => idtac);
      [ assumption | exact SV2 | exact PE2 | exact TEG | exact TLO | exact AO | exact RS2 | exact TS2 | exact ST2 | exact LOH | exact CLO | clear - LOQ CS; lia
      | clear - Q16; Z.div_mod_to_equations; lia | clear - QH; lia | exact SN1 | exact SN2 | exact SN3 | exact AIN | exact ALO | clear - AHI; lia | exact AREG | exact ACH | exact WMAX | ].

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    rename MUk into MU3, WMk into WM3, POST into GM3.
    rename MI0 into MI3, PC into ST3, PC0 into PE3, PC1 into TE3, PC2 into RS3, PC3 into TS3, PC4 into A4K, PC5 into ALOW, PC6 into AM, PC7 into APL, PC8 into AV,
           PC9 into HPG, PC10 into BLK, PC11 into SHH, PC12 into SHJ, PC13 into SHT, PC14 into SV3.

    assert (MSZF : exists bs, sec_msize (al_sneed n) = bs + 4096 /\ bs = rup4k (al_sneed n) /\ al_sneed n <= bs < al_sneed n + 4096 /\ bs mod 4096 = 0).
    { exists (rup4k (al_sneed n)). unfold sec_msize, rup4k. clear - SN1. split; [reflexivity|]. split; [reflexivity|]. Z.div_mod_to_equations. lia. }
    destruct MSZF as (bs & EMSZ & EBS & BSR & BS4K).
    remember (sec_msize (al_sneed n)) as msz eqn:Emsz.
    remember (al_sneed n) as needed eqn:Eneeded.
    pose proof APL as [_ ATOP].
    layout_facts AO 1%nat LPARR. destruct LPARR as (P1 & P2 & _).
    assert (SHR3 : 2147450880 <= sh r /\ sh r + msz / 8 <= 17594333495296) by (unfold sh, SHADOW_OFF; clear - ATOP ACR EMSZ BSR SN1 ALOW; Z.div_mod_to_equations; lia).

    lazymatch type of GM3 with gmunch ?w _ _ => assert (DJ3 : forall A k0, q - 128 <= A -> disjoint_from w A k0) end.
    { intros A k0 HA. cbn [disjoint_from]. clear - HA LOQ CS LOH CLO T4 P2 ATOP SHR3 EMSZ BSR SN1. lia. }
    unhideB FR. eapply (rw_cells_gtransport _ m2 m3) in FR; [| exact GM3| exact WM3| apply DJ3; clear; lia].
    unhideB SOBJ. eapply (rw_cells_gtransport _ m2 m3) in SOBJ; [| exact GM3| exact WM3| apply DJ3; clear - QSTK; lia].
    unhideB BUF. eapply (u64arr_gtransport _ m2 m3) in BUF; [| exact GM3| exact WM3| apply DJ3; clear - QTR; lia].

    assert (GM3w : gmunch [(lo, q); (SEC, SEC + 620); (GSTATS_A, GSTATS_A + 16); (THR + 2800, THR + 3168); (PARR, PARR + 2^23); (r, r + msz); (sh r, sh r + msz / 8)] m2 m3).
    { refine (gmunch_weaken _ _ _ _ _ GM3). unfold sub_fp. cbn [outside]. intros xo_ Hxo_. clear - Hxo_ LOQ CS. destruct Hxo_ as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & _). repeat split; try assumption. lia. }
    assert (INV3 : dr_inv AL E (fst X, sec_alloc (snd X) r needed) (sec_alloc_H AL (snd X) needed r H) m3 WB WC hrest).
    { rewrite Emsz in GM3w, AM, AV.
      exact (dr_inv_salloc AL E X H _ m2 m3 WB WC hrest lo q r needed avoid AO LOH CLO ltac:(clear - LOQ CS; lia) INV2 GM3w WM3 MI3 PE3 TE3 SV3 RS3 TS3
               A4K ALOW AM ltac:(clear - SN1; lia) AV AREG ACH). }
    zstep. zstep. if_cases KZ; zify_cond KZ. { exfalso. clear - KZ ALOW ATOP ACR EMSZ BSR SN1. lia. } clear KZ.

    set (B := r + 4096) in *. set (rz := al_rz n) in *. set (size := al_n n) in *.
    assert (B4K : B mod 4096 = 0) by (unfold B; clear - A4K; Z.div_mod_to_equations; lia).
    assert (B8 : B mod 8 = 0) by (clear - B4K; Z.div_mod_to_equations; lia).
    assert (SZR : 1 <= size <= 2^28 /\ size = n) by (unfold A0_MAXREQ in NR; clear - NR N1 EALN; lia).
    assert (R8F : rup8 size = 8 * rk) by (rewrite EALN; exact ER8).
    assert (FIT : rz + rup8 size + 2048 = needed /\ rz = 2048) by (rewrite R8F; clear - SN4 ERZ; lia).
    destruct SHJ as (jsa & SHJ).
    assert (SHJN : sh (B + needed) = sh B + Z.of_nat (Z.to_nat (needed / 8)) /\ (Z.to_nat (needed / 8) + Z.to_nat ((msz - 4096 - needed) / 8))%nat = Z.to_nat (bs / 8)).
    { unfold sh. clear - B8 SN2 SN1 EMSZ BSR BS4K. split; Z.div_mod_to_equations; lia. }
    destruct SHJN as (SHJ1 & SHJ2).
    replace (r + 4096 + needed) with (B + needed) in SHT by (unfold B; clear; lia). rewrite SHJ1 in SHT.
    pose proof (cb_join m3 (sh B) _ _ _ _ SHJ SHT) as SHB. rewrite SHJ2 in SHB. clear SHJ SHT SHJ1 SHJ2.
    replace (msz - 4096) with bs in BLK by (clear - EMSZ; lia).
    destruct (carve_map m3 B bs rz size _ _ ltac:(unfold B; clear - ALOW; lia) B8 ltac:(clear - BS4K; Z.div_mod_to_equations; lia)
                (proj1 (proj1 RZF)) (proj2 RZF) (proj1 (proj1 SZR)) ltac:(clear - FIT BSR; lia) BLK SHB)
      as ((j0 & LRZ) & (b0 & b1 & j2 & j4 & j8 & HD1 & HD2) & (ub & UB) & (sl & SLK) & (j1 & SH1) & (ju & SHU) & SHP & (jt & SH2)).
    clear BLK SHB.
    set (M := B + rz - 16) in *.
    assert (EB : B = r + 4096) by reflexivity. assert (EM : M = B + rz - 16) by reflexivity.
    assert (Erz : rz = al_rz n) by reflexivity. assert (Esize : size = al_n n) by reflexivity.
    replace (B + rz - 16 + 8) with (M + 8) in HD2 by (clear - EM; lia).
    replace (B + rz) with (M + 16) in UB, SLK, SHU, SHP, SH2 by (clear - EM; lia).
    clearbody M. clearbody B. clearbody rz. clearbody size.
    destruct FIT as (FIT & RZV).
    assert (MR : B <= M /\ M + 16 + rup8 size + 2048 <= B + bs /\ M mod 8 = 0 /\ size <= rup8 size < size + 8 /\ B + 16 <= M)
      by (clear - EM FIT RZV B8 SZR BSR RK R8F; Z.div_mod_to_equations; lia).
    assert (BLO : 6328320 + 4096 <= B /\ B + bs <= alloc_ceiling /\ (B + bs <= 0x7fff8000 \/ 0x10007fff8000 <= B))
      by (unfold app_mem in AM; clear - EB ALOW ATOP EMSZ AM; lia).

    pose proof FR as FRc. split_chunk FRc 1%nat FRa FRb. split_chunk FRb 1%nat FR8 FRd. split_chunk FRd 1%nat FR16 FRe. clear FRa FRe FR8.
    assert (BRp : 0 <= B /\ B mod 8 = 0 /\ B + needed <= 2^47) by (split; [clear - BLO; lia| split; [exact B8| clear - BLO BSR ACR; lia]]).
    assert (SZp : 1 <= size <= 2^28 /\ rz + size <= needed /\ 0 <= n <= 2^28) by (unfold A0_MAXREQ in NR; clear - SZR FIT MR NR; lia).

    assert (RAP : forall rg, In rg (al_regions AL) -> r + msz <= fst rg \/ fst rg + snd rg <= r).
    { intros rg Hrg. pose proof (proj1 (Forall_forall _ _) AV _ (proj1 (Forall_forall _ _) AREG rg Hrg)) as X0. cbn [fst snd] in X0. exact X0. }
    pose proof (RAP _ (or_introl eq_refl)) as APS. pose proof (RAP _ (or_intror (or_introl eq_refl))) as APP.
    pose proof (RAP _ (or_intror (or_intror (or_introl eq_refl)))) as APC. pose proof (RAP _ (or_intror (or_intror (or_intror (or_introl eq_refl))))) as APT.
    pose proof (RAP _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))) as ADN.
    pose proof (RAP _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))) as ASS.
    cbn [fst snd] in APS, APP, APC, APT, ADN, ASS. clear RAP.

    pose proof RS2 as ((NRES0 & _ & NRES2 & _) & _).
    remember (PARR + 8 * se_nres (snd X)) as pw eqn:Epw.
    assert (PWR : 6328320 <= pw /\ pw + 131072 <= 2^47) by (rewrite Epw; clear - P1 P2 ACR NRES0 NRES2; lia).
    pose proof (sw_range r msz ALOW ltac:(clear - EMSZ BSR SN1; lia) ltac:(clear - ATOP ACR; lia)) as SWA.
    pose proof (sw_range pw 131072 (proj1 PWR) ltac:(clear; lia) (proj2 PWR)) as SWP.
    remember (swlo r) as wal eqn:Ewal. remember (swhi r msz) as wah eqn:Ewah. remember (swlo pw) as wpl eqn:Ewpl. remember (swhi pw 131072) as wph eqn:Ewph.
    layout_apart_fact AO 1%nat 2%nat A12. layout_apart_fact AO 1%nat 3%nat A13. layout_apart_fact AO 1%nat 5%nat A15. layout_apart_fact AO 1%nat 6%nat A16.
    layout_apart_fact AO 3%nat 5%nat A35. layout_apart_fact AO 3%nat 6%nat A36.
    layout_facts AO 5%nat LDN. destruct LDN as (N1d & N2d & _). layout_facts AO 6%nat LSS. destruct LSS as (SS1 & SS2 & _).
    pose proof DLO as (DL1 & DL2 & _ & DL4 & _).
    unhideB MU12. unhideB WM12.
    pose proof (munch_joinP _ _ _ _ _ MU12 MU3) as MU13. cbn [app] in MU13. pose proof (wmono_trans asegs _ _ _ WM12 WM3) as WM13.
    assert (TE23 : thread_env2 AL m3).
    { eapply thread_env2_frame_m; [exact TE2| exact MU13| |]; cbn [disjoint_from].
      - clear - LOQ CS CLO T3 T4 A13 APT SWA SWP P1 EMSZ BSR SN1. lia.
      - clear - LOQ CS CLO T1 T2 T5 A12 APC SWA SWP P1 EMSZ BSR SN1. lia. }
    assert (RD3 : RDEPOT D hs total m3).
    { eapply RDEPOT_frame_m; [exact DLO| exact SWB| exact RD| exact MU13| | |]; cbn [disjoint_from].
      - clear - LOQ CS LOH T3 P1 ALOW SWA SWP. lia.
      - clear - LOQ CS CLO N1d N2d A15 A35 ADN SWA SWP T3 EMSZ BSR SN1. lia.
      - clear - LOQ CS CLO SS1 SS2 A16 A36 ASS SWA SWP T3 EMSZ BSR SN1. lia. }
    hideB MU12. hideB WM12. hideB MU13. hideB WM13.

    destruct TE23 as (THC & tidw & TIDC).
    hideB FR. hideB SOBJ. hideB BUF. hideB LRZ. hideB HD1. hideB HD2. hideB UB. hideB SLK. hideB SH1. hideB SHU. hideB SH2. hideB HPG. hideB SHH.
    hideB FR16. hideB MU3. hideB WM3. hideB GM3. hideB GM3w. hideB THC. hideB TIDC.
    assert (SPRm : (q - 128) mod 16 = 0 /\ q - 128 + 128 <= 2^47) by (split; [clear - Q16; Z.div_mod_to_equations; lia| clear - QH; lia]).
    assert (THRm : 0 < THR < 2^64) by (clear - T3 T4 ACR; lia).
    assert (MDJm : 6328320 <= M /\ M + 16 <= lo /\ (M + 16 <= DN0 D \/ DN0 D + 2^20 <= M) /\ (M + 16 <= SS0 D \/ SS0 D + SWIN D <= M)).
    { pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 DLO)))))) as SW0. destruct MR as (MR1 & MR2 & _ & MR4 & _).
      clear - MR1 MR2 MR4 SZR BLO CLO ADN ASS SS2 SWB SW0 EB EMSZ. lia. }
    assert (DJTm : THR + 8 <= M \/ M + 16 <= THR) by (destruct MR as (MR1 & MR2 & _ & MR4 & _); clear - MR1 MR2 MR4 SZR APT EB EMSZ; lia).
    assert (DJCm : at_ctx L + 12 <= M \/ M + 16 <= at_ctx L + 8) by (destruct MR as (MR1 & MR2 & _ & MR4 & _); clear - MR1 MR2 MR4 SZR APC EB EMSZ; lia).
    eapply evt_cut.
    { eapply (back1_spec D gp _ _ _ _ _ _ _ F_ fc (q - 128) lo B M rz size needed n THR (at_ctx L) STK TR total m3 hs ws tr
               DLO CLO ltac:(clear - LOQ CS; lia) SPRm THRm BRp RZF SZp EM MDJm _ _ _ _ _ _ _ _ _ _ _ tidw b0 b1 j2 j4 j8);
        [ exact MI3 | exact ST3 | exact FR16 | exact HD1 | exact HD2 | exact THC | exact TIDC | exact SOBJ | exact RD3 | exact BUF | exact TRW | exact LENW | exact LTR | exact RNG
        | clear - QTR; lia | exact TRH | clear - QSTK; lia | exact STKH | exact ROOM_N | exact ROOM_F | exact ROOM_T | exact DJTm | exact DJCm ]. }
    cbv beta. intros msB PB. unfold back1_post in PB.
    destruct PB as (ra5 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & m4 & mD & m5 & hs' & total' & bits1 & actx & -> & MS4 & MSD & MS5 & ST5 & RD5 & RES & B31 & HDN & ACX).

    assert (WFch : qchunk_wf (mkQC (QSec (mkSC r msz needed)) rz size)).
    { unfold qchunk_wf. cbn [qc_rz qc_n qc_kind qc_bsize sc_msize]. split; [exact (proj1 (proj1 RZF))|]. split; [exact (proj2 RZF)|]. split; [clear - SZR; lia|].
      split; [clear - FIT BSR EMSZ; lia| exact I]. }
    assert (HELD : held_kind (fst X, sec_alloc (snd X) r needed) (mkQC (QSec (mkSC r msz needed)) rz size)).
    { unfold held_kind, sec_alloc. cbn [qc_kind snd se_chunks]. apply in_or_app. right. left. rewrite Emsz. reflexivity. }
    assert (NSC : forall sc, In sc (sec_of (mkQC (QSec (mkSC r msz needed)) rz size)) -> ~ In sc (flat_map sec_of WC)).
    { intros sc0 [<-|[]] Hin. apply in_flat_map in Hin. destruct Hin as (ch' & Hch & Hsc).
      pose proof (proj1 (Forall_forall _ _) HKS ch' Hch) as HK'. destruct ch' as [[c' v'|sc'] rz' n']; cbn [sec_of qc_kind] in Hsc; [destruct Hsc|].
      destruct Hsc as [->|[]]. unfold held_kind in HK'. cbn [qc_kind] in HK'.
      pose proof (proj1 (Forall_forall _ _) AV _ (proj1 (Forall_forall _ _) ACH _ HK')) as X0. cbn [fst snd sc_beg sc_msize] in X0. clear - X0 EMSZ BSR SN1. lia. }
    assert (BLKSTEP : forall (ma mb : mem) Hh A k0 sa sb, dr_inv AL E (fst X, sec_alloc (snd X) r needed) Hh ma WB WC hrest ->
              munch [(sa, sb); (A, A + k0)] ma mb -> wmono asegs ma mb -> mem_inv asegs mb -> lo <= sa -> sb <= q -> B <= A -> A + k0 <= B + bs ->
              dr_inv AL E (fst X, sec_alloc (snd X) r needed) Hh mb WB WC hrest).
    { intros ma mb Hh A k0 sa sb IV MUab WMab MIb L1 L2 L3 L4.
      eapply (dr_inv_blk AL E (fst X, sec_alloc (snd X) r needed) Hh ma mb WB WC hrest (mkQC (QSec (mkSC r msz needed)) rz size) lo q sa sb A k0 AO LOH CLO IV HELD WFch NSC MUab WMab MIb L1 L2).
      - unfold qc_blk. cbn [qc_kind sc_beg]. rewrite <- EB. exact L3.
      - unfold qc_blk, qc_bsize. cbn [qc_kind sc_beg sc_msize]. rewrite <- EB. replace (msz - 4096) with bs by (clear - EMSZ; lia). exact L4. }
    assert (SHSTEP : forall (ma mb : mem) Hh A k0 sa sb, dr_inv AL E (fst X, sec_alloc (snd X) r needed) Hh ma WB WC hrest ->
              munch [(sa, sb); (A, A + k0)] ma mb -> wmono asegs ma mb -> mem_inv asegs mb -> lo <= sa -> sb <= q -> sh B <= A -> A + k0 <= sh B + bs / 8 ->
              dr_inv AL E (fst X, sec_alloc (snd X) r needed) Hh mb WB WC hrest).
    { intros ma mb Hh A k0 sa sb IV MUab WMab MIb L1 L2 L3 L4.
      eapply (dr_inv_poison AL E (fst X, sec_alloc (snd X) r needed) Hh ma mb WB WC hrest (mkQC (QSec (mkSC r msz needed)) rz size) lo q sa sb A k0 AO LOH CLO IV HELD WFch NSC MUab WMab MIb L1 L2).
      - unfold qc_blk. cbn [qc_kind sc_beg]. rewrite <- EB. exact L3.
      - unfold qc_blk, qc_bsize. cbn [qc_kind sc_beg sc_msize]. rewrite <- EB. replace (msz - 4096) with bs by (clear - EMSZ; lia). exact L4. }
    assert (WK1 : forall a b (ma mb : mem), munch [(a, b)] ma mb -> munch [(lo, lo); (a, b)] ma mb).
    { intros a b ma mb MUab. eapply munch_weaken; [| exact MUab]. unfold sub_fp. cbn [outside]. intros xo_ (_ & O2 & _). split; [exact O2| exact I]. }
    destruct MS4 as (MU4 & WM4 & MI4). destruct MSD as (MUD & WMD & MID). destruct MS5 as (MU5 & WM5 & MI5).
    destruct MR as (MR1 & MR2 & MR3 & MR4 & MR5).
    pose proof (BLKSTEP m3 m4 _ M 8 lo lo INV3 (WK1 _ _ _ _ MU4) WM4 MI4 ltac:(clear; lia) ltac:(clear - LOQ CS; lia)
                  ltac:(clear - MR1; lia) ltac:(clear - MR1 MR2 MR4 SZR; lia)) as INV4.
    pose proof (bkt_range (depot_hash tr)) as BKR.
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
                  ltac:(clear - MR1; lia) ltac:(clear - MR1 MR2 MR4 SZR; lia)) as INV5.
    clear INV4 INVD.

    assert (SHG : sh B = sh r + 512 /\ bs / 8 + 512 = msz / 8 /\ 0 <= bs / 8) by (unfold sh; clear - EB A4K EMSZ BS4K BSR SN1; Z.div_mod_to_equations; lia).
    destruct SHG as (SHG1 & SHG2 & SHG3).
    assert (DJ35 : forall A k0, ((r <= A /\ A + k0 <= M) \/ (M + 16 <= A /\ A + k0 <= r + msz) \/ (sh r <= A /\ A + k0 <= sh r + msz / 8) \/ q - 128 <= A) -> 0 <= k0 ->
              disjoint_from [(M, M + 8)] A k0
              /\ disjoint_from [(q - 128 - 224, q - 128); (DT + 4 * bkt (depot_hash tr), DT + 4 * bkt (depot_hash tr) + 4); (DNI, DNI + 4);
                   (DN0 D + 16 * (zlen hs + 1), DN0 D + 16 * (zlen hs + 1) + 16); (SSA, SSA + 8); (SSD + 8, SSD + 12);
                   (SS0 D + 8 * total, SS0 D + 8 * total + 8 + 8 * Z.of_nat (length tr))] A k0
              /\ disjoint_from [(M + 8, M + 8 + 8)] A k0).
    { intros A k0 HA HK. unfold zlen in *. cbn [disjoint_from].
      clear - HA HK MR1 MR2 MR4 SZR BLO CLO LOQ CS LOH ADN ASS SS1 SS2 N1d N2d SWB EB EMSZ SHR3 ALOW BKR ROOM_N ROOM_F T0. lia. }
    assert (TR35 : forall A cs, rw_cells asegs m3 A cs ->
              ((r <= A /\ A + Z.of_nat (cells_size cs) <= M) \/ (M + 16 <= A /\ A + Z.of_nat (cells_size cs) <= r + msz)
               \/ (sh r <= A /\ A + Z.of_nat (cells_size cs) <= sh r + msz / 8) \/ q - 128 <= A) -> rw_cells asegs m5 A cs).
    { intros A cs HC0 HA. destruct (DJ35 A (Z.of_nat (cells_size cs)) HA ltac:(clear; lia)) as (D4 & DD & D5).
      eapply (rw_cells_transport asegs _ mD m5); [| exact MU5| exact WM5| exact D5].
      eapply (rw_cells_transport asegs _ m4 mD); [| exact MUD| exact WMD| exact DD].
      eapply (rw_cells_transport asegs _ m3 m4); [exact HC0| exact MU4| exact WM4| exact D4]. }
    assert (SHF : sh (M + 16) = sh B + rz / 8 /\ sh (M + 16 + rup8 size) = sh (M + 16) + rup8 size / 8 /\ size / 8 <= rup8 size / 8
                  /\ (size mod 8 <> 0 -> size / 8 + 1 <= rup8 size / 8) /\ 0 <= rz / 8 /\ sh (M + 16) + rup8 size / 8 + 256 <= sh B + bs / 8
                  /\ 0 <= size / 8 /\ (bs - rz - rup8 size) / 8 = bs / 8 - rz / 8 - rup8 size / 8 /\ rz / 8 = 256).
    { unfold sh. rewrite R8F. clear - EM RZV B8 MR2 MR4 SZR BS4K BLO R8F RK. Z.div_mod_to_equations. lia. }
    destruct SHF as (SF1 & SF2 & SF3 & SF4 & SF5 & SF6 & SF7 & SF8 & SF9).
    unhideB SH1. apply TR35 in SH1; [| right; right; left; cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by exact SF5; clear - SHG1 SHG2 SF9 SHG3 SF1 SF3 SF6 SF7; lia].
    unhideB SH2. apply TR35 in SH2; [| right; right; left; cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (rewrite SF8; clear - SF6 SF1; lia);
                                       rewrite SF2, SF8; clear - SHG1 SHG2 SF1 SF5 SF6 SF3 SF7; lia].
    pose proof INV5 as (RP5 & _ & RS5 & _ & PE5 & TE5 & _).
    pose proof RP5 as (_ & PENV5 & _ & _ & (ts5 & TS5)). unfold prim_env in PENV5.
    lazymatch type of PENV5 with rw_cells _ _ _ (?c1 :: ?rest) => change (rw_cells asegs m5 721592 ([c1] ++ rest)) in PENV5 end.
    apply rw_cells_app in PENV5. destruct PENV5 as [SPC5 _].
    pose proof RS5 as (_ & (SENV5 & _ & _) & _ & _ & HDRS5).
    lazymatch type of SENV5 with rw_cells _ _ _ (?c1 :: ?rest) => change (rw_cells asegs m5 SEC ([c1] ++ rest)) in SENV5 end. apply rw_cells_app in SENV5. destruct SENV5 as [PGS5 _].
    assert (HSZ5 : rw_cells asegs m5 (B - 4096 + 16) [C8 (wz needed)]).
    { pose proof (HDRS5 (length (se_chunks (snd X))) (mkSC r (sec_msize needed) needed)) as HH.
      unfold sec_alloc in HH. cbn [se_chunks snd] in HH. rewrite nth_error_app2, Nat.sub_diag in HH by (clear; lia). specialize (HH eq_refl).
      unfold hdr_cells in HH. cbn [sc_beg sc_msize sc_size] in HH.
      lazymatch type of HH with rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4] => change (rw_cells asegs m5 r ([c1; c2] ++ [c3] ++ [c4])) in HH end.
      apply rw_cells_take3 in HH. destruct HH as (_ & HH & _). cbn [cells_size csize Nat.add] in HH.
      replace (B - 4096 + 16) with (r + Z.of_nat 16) by (rewrite EB; clear; lia). exact HH. }
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & _ & _ & SP5 & _ & _).
    assert (BRr : 6328320 <= B /\ B mod 4096 = 0 /\ B + bs <= 2^47 /\ (B + bs <= 0x7fff8000 \/ 0x10007fff8000 <= B))
      by (split; [clear - BLO; lia| split; [exact B4K| split; [clear - BLO ACR; lia| exact (proj2 (proj2 BLO))]]]).
    assert (BSPr : 0 <= al_space AL /\ al_space AL + K_SPACE < 2^64 /\ (B < al_space AL \/ al_space AL + K_SPACE <= B)) by (clear - SP1 SP5 APS EB EMSZ BSR SN1; lia).
    assert (SZr : 1 <= size <= 2^28 /\ rz + rup8 size + 8 <= bs /\ 0 < needed <= 2^40 /\ bs = rup4k needed)
      by (split; [exact (proj1 SZR)| split; [clear - FIT BSR; lia| split; [clear - SN1 SN3; lia| exact EBS]]]).
    hideB HDN. hideB ACX. hideB TS5.
    eapply evt_cut.
    { eapply (rzs_spec E gp _ _ _ _ F_ fc (q - 128) lo B M rz size needed bs (al_space AL) m5 LOH ltac:(clear - LOQ CS; lia) ltac:(clear - QH; lia) BRr BSPr RZF EM SZr
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j1 jt);
        [ exact MI5 | exact ST5 | exact PE5 | exact SPC5 | exact PGS5 | exact HSZ5 | exact SH1 | exact SH2 ]. }
    cbv beta. intros msR PR. unfold rzs_post in PR.
    destruct PR as (ra6 & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & m5a & m5b & -> & MS5a & MS5b & ST5b & PE5b & SHL & SHRr).
    destruct MS5a as (MU5a & WM5a & MI5a). destruct MS5b as (MU5b & WM5b & MI5b).
    pose proof (SHSTEP m5 m5a _ (sh B) (rz / 8) (q - 128 - 64) (q - 128) INV5 MU5a WM5a MI5a ltac:(clear - LOQ CS; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(clear - SF1 SF3 SF6 SF7 SF5; lia)) as INV5a.
    pose proof (SHSTEP m5a m5b _ (sh (M + 16 + rup8 size)) ((bs - rz - rup8 size) / 8) (q - 128 - 64) (q - 128) INV5a MU5b WM5b MI5b ltac:(clear - LOQ CS; lia) ltac:(clear; lia)
                  ltac:(rewrite SF2; clear - SF1 SF3 SF5 SF7; lia) ltac:(rewrite SF2, SF8; clear - SF1; lia)) as INV5b.
    clear INV5a.

    unhideB MU12. unhideB GM3. unhideB WM3.
    assert (ENV3 : alloc_env m3 /\ hooks_env m3).
    { lazymatch type of MU12 with munch ?w _ _ => assert (FO12 : Forall aenv_out w) end.
      { repeat (apply Forall_cons || apply Forall_nil); unfold aenv_out; cbn [fst snd]; clear - LOQ CS LOH; lia. }
      pose proof (alloc_env_frame_m _ m m2 AE MU12 FO12) as AE2. pose proof (hooks_env_frame_m _ m m2 HKE MU12 FO12) as HKE2.
      assert (TRG : forall A cs, rw_cells asegs m2 A cs -> 0x10000 <= A ->
                (A + Z.of_nat (cells_size cs) <= 721624 \/ (722280 <= A /\ A + Z.of_nat (cells_size cs) <= 0x609000)) -> rw_cells asegs m3 A cs).
      { intros A cs HC0 HA HB. eapply (rw_cells_gtransport _ m2 m3); [exact HC0| exact GM3| exact WM3|]. cbn [disjoint_from].
        clear - HA HB LOQ CS LOH T3 P1 ALOW SHR3. lia. }
      ae_split AE2. unfold alloc_env, hooks_env in *.
      repeat match goal with |- _ /\ _ => split end;
        (apply TRG; [assumption| cbn [cells_size csize Nat.add]; clear; lia| cbn [cells_size csize Nat.add]; clear; lia]). }
    destruct ENV3 as (AE3 & HKE3).
    pose proof (munch_joinP _ _ _ _ _ MU4 MUD) as MUa. pose proof (munch_joinP _ _ _ _ _ MUa MU5) as MUb. pose proof (munch_joinP _ _ _ _ _ MUb MU5a) as MUc.
    pose proof (munch_joinP _ _ _ _ _ MUc MU5b) as MU35. cbn [app] in MU35. clear MUa MUb MUc.
    lazymatch type of MU35 with munch ?w _ _ => assert (FO35 : Forall aenv_out w) end.
    { unfold zlen in *. repeat (apply Forall_cons || apply Forall_nil); unfold aenv_out; cbn [fst snd]; rewrite ?SF2;
        clear - LOQ CS LOH MR1 BLO BKR N1d SS1 ROOM_N ROOM_F T0 SHG1 SHR3 SF1 SF3 SF5 SF7; lia. }
    pose proof (alloc_env_frame_m _ m3 m5b AE3 MU35 FO35) as AE5. pose proof (hooks_env_frame_m _ m3 m5b HKE3 MU35 FO35) as HKE5.
    hideB MU12. hideB GM3. hideB WM3. hideB MU35.
    assert (TR5b : forall A cs, rw_cells asegs m5 A cs ->
              ((r <= A /\ A + Z.of_nat (cells_size cs) <= r + msz) \/ (sh (M + 16) <= A /\ A + Z.of_nat (cells_size cs) <= sh (M + 16) + rup8 size / 8)
               \/ (sh r <= A /\ A + Z.of_nat (cells_size cs) <= sh r + 512) \/ q - 128 <= A \/ (THR <= A /\ A + Z.of_nat (cells_size cs) <= THR + 4096)) -> rw_cells asegs m5b A cs).
    { intros A cs HC0 HA. remember (Z.of_nat (cells_size cs)) as k0 eqn:Ek0. assert (K0 : 0 <= k0) by (rewrite Ek0; clear; lia).
      eapply (rw_cells_transport asegs _ m5a m5b); [| exact MU5b| exact WM5b|].
      - eapply (rw_cells_transport asegs _ m5 m5a); [exact HC0| exact MU5a| exact WM5a|]. rewrite <- Ek0. cbn [disjoint_from].
        clear - HA K0 LOQ CS LOH CLO SHR3 SHG1 SHG2 SF1 SF3 SF5 SF6 SF7 SF9 T3 T4 ALOW ATOP ACR AM EMSZ. unfold app_mem in AM. lia.
      - rewrite <- Ek0. cbn [disjoint_from]. rewrite SF2, SF8.
        clear - HA K0 LOQ CS LOH CLO SHR3 SHG1 SHG2 SF1 SF3 SF5 SF6 SF7 SF9 T3 T4 ALOW ATOP ACR AM EMSZ. unfold app_mem in AM. lia. }
    unhideB FR. apply TR35 in FR; [| right; right; right; clear; lia]. apply TR5b in FR; [| right; right; right; left; clear; lia].
    unhideB UB. apply TR35 in UB; [| right; left; cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear - SZR; lia); clear - MR2 MR4 EB EMSZ; lia].
    apply TR5b in UB; [| left; cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear - SZR; lia); clear - MR1 MR2 MR4 EB EMSZ; lia].
    unhideB SHU. apply TR35 in SHU; [| right; right; left; cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by exact SF7; clear - SHG1 SHG2 SF1 SF3 SF5 SF6 SF7; lia].
    apply TR5b in SHU; [| right; left; cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by exact SF7; clear - SF3; lia].
    assert (SHP5 : size mod 8 <> 0 -> exists bp, rw_cells asegs m5b (sh (M + 16) + size / 8) [C1 bp]).
    { intros NE. destruct (SHP NE) as (bp & PC0). exists bp. pose proof (SF4 NE) as SF4'. apply TR5b; [apply TR35; [exact PC0|]|].
      - right; right; left. cbn [cells_size csize Nat.add]. clear - SHG1 SHG2 SF1 SF4' SF5 SF6 SF7. lia.
      - right; left. cbn [cells_size csize Nat.add]. clear - SF4' SF7. lia. }
    assert (LCH5 : B <> M -> exists lj, rw_cells asegs m5b B [CB 16 lj]).
    { intros _. unhideB LRZ. assert (LE32 : (16 + Z.to_nat (rz - 32) <= Z.to_nat (rz - 16))%nat) by (clear - RZV; lia).
      destruct (cb_split3 m3 B (Z.to_nat (rz - 16)) j0 16 (Z.to_nat (rz - 32)) LE32 LRZ) as (lj & _ & _ & LC16 & _ & _).
      exists lj. apply TR5b; [apply TR35; [exact LC16|]|].
      - left. cbn [cells_size csize Nat.add]. clear - EM RZV EB. lia.
      - left. cbn [cells_size csize Nat.add]. clear - EM RZV EB EMSZ BSR SN1. lia. }
    unhideB TS5. apply TR5b in TS5; [| right; right; right; right; cbn [cells_size csize Nat.add]; clear; lia].
    unhideB HDN. split_chunk HDN 2%nat HDa HDb. hideB HDb.
    apply TR5b in HDa; [| left; cbn [cells_size csize Nat.add]; clear - MR1 MR2 MR4 EB EMSZ SZR; lia].
    pose proof INV5b as (_ & _ & _ & _ & _ & TE5b & _).
    assert (BR2 : 6328320 <= B /\ (B = M \/ B + 16 <= M) /\ M mod 8 = 0 /\ M + 16 + size + 8 <= lo).
    { split; [clear - BLO; lia|]. split; [right; exact MR5|]. split; [exact MR3|]. clear - MR2 MR4 BLO CLO. lia. }
    assert (SZ2 : 1 <= size <= 2^28 /\ size + 16 <= needed <= 2^40) by (clear - SZR FIT MR4 SN3 RZV; lia).
    assert (UG2 : M + 16 + size + 8 <= 2147450880 \/ 17594333495296 <= B) by (clear - BLO MR2 MR4; lia).
    assert (TB2 : THR + 4096 <= B \/ M + 16 + size + 8 <= THR) by (clear - APT MR2 MR4 EB EMSZ; lia).
    hideB HDa. hideB FR. hideB UB. hideB SHU. hideB TS5. hideB SHL. hideB SHRr.
    eapply evt_cut.
    { eapply (back2_spec E L gp F_ fc ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (q - 128) lo B M size needed m5b
               LOH CLO ltac:(clear - LOQ CS; lia) SPRm TLO BR2 SZ2 UG2 TB2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b0 bits1 _ _ _ _ _);
        [ exact MI5b | exact ST5b | exact PE5b | exact AE5 | exact HKE5 | exact TE5b | exact FR | exact HDa | exact B31 | exact LCH5 | exact UB | exact SHU | exact SHP5 | exact TS5 ]. }
    cbv beta. intros msZ PZ. unfold back2_post in PZ.
    destruct PZ as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m6 & m7 & m8 & m9 & mZ & bitsZ & ubZ & tsZ
                    & -> & MS6 & MS7 & MS8 & MS9 & MSZ & STZ & B3Z & HDZ & LCHZ & UBZ & SHZ & SHPZ & TS8 & EQ7 & MUZp).
    destruct MS6 as (MU6 & WM6 & MI6). destruct MS7 as (MU7 & WM7 & MI7). destruct MS8 as (MU8 & WM8 & MI8). destruct MS9 as (MU9 & WM9 & MI9). destruct MSZ as (MUZ & WMZ & MIZ).
    assert (SU : sh B <= sh (M + 16) /\ sh (M + 16) + size / 8 <= sh B + bs / 8 /\ (size mod 8 <> 0 -> sh (M + 16) + size / 8 + 1 <= sh B + bs / 8))
      by (split; [clear - SF1 SF5; lia| split; [clear - SF3 SF6; lia| intros NE; pose proof (SF4 NE) as SF4'; clear - SF4' SF6; lia]]).
    destruct SU as (SU1 & SU2 & SU3).
    pose proof (SHSTEP m5b m6 _ (sh (M + 16)) (size / 8) (q - 128 - 64) (q - 128) INV5b MU6 WM6 MI6 ltac:(clear - LOQ CS; lia) ltac:(clear; lia) SU1 SU2) as INV6.
    lazymatch type of INV6 with dr_inv _ _ _ ?hh _ _ _ _ => assert (INV7 : dr_inv AL E (fst X, sec_alloc (snd X) r needed) hh m7 WB WC hrest) end.
    { destruct (Z.eq_dec (size mod 8) 0) as [EZ|NZ].
      - pose proof (EQ7 EZ) as E76. rewrite E76. exact INV6.
      - exact (SHSTEP m6 m7 _ (sh (M + 16) + size / 8) 1 lo lo INV6 (WK1 _ _ _ _ MU7) WM7 MI7 ltac:(clear; lia) ltac:(clear - LOQ CS; lia)
                 ltac:(clear - SU1 SF7; lia) (SU3 NZ)). }
    pose proof (dr_inv_tstats AL E _ _ m7 m8 WB WC _ lo q (q - 128 - 32) (q - 128) AO LOH CLO ltac:(clear - LOQ CS; lia) ltac:(clear; lia) ltac:(clear; lia)
                  INV7 MU8 WM8 MI8 (ex_intro _ tsZ TS8)) as INV8.
    pose proof (BLKSTEP m8 m9 _ (M + 16) (Z.min size 4096) lo lo INV8 (WK1 _ _ _ _ MU9) WM9 MI9 ltac:(clear; lia) ltac:(clear - LOQ CS; lia)
                  ltac:(clear - MR1; lia) ltac:(clear - MR2 MR4 SZR; lia)) as INV9.
    assert (MUZw : munch [(q - 128 - 32, q - 128); (B, B + (M + 16 - B))] m9 mZ).
    { eapply munch_weaken; [| exact MUZ]. unfold sub_fp. cbn [outside]. intros xo_ (O1 & O2 & _). split; [exact O1|]. split; [clear - O2 MR1; lia|]. split; [clear - O2 MR1 MR5; lia| exact I]. }
    pose proof (BLKSTEP m9 mZ _ B (M + 16 - B) (q - 128 - 32) (q - 128) INV9 MUZw WMZ MIZ ltac:(clear - LOQ CS; lia) ltac:(clear; lia)
                  ltac:(clear; lia) ltac:(clear - MR2 MR4 SZR; lia)) as INVZ.
    clear INV6 INV7 INV8 INV9.

    pose proof AM as AMu. unfold app_mem in AMu.
    assert (TRbZ : forall A cs, rw_cells asegs m5b A cs ->
              ((B + 16 <= A /\ A + Z.of_nat (cells_size cs) <= M) \/ (M + 2 <= A /\ A + Z.of_nat (cells_size cs) <= M + 16)
               \/ (M + 16 + size <= A /\ A + Z.of_nat (cells_size cs) <= B + bs)
               \/ (sh B <= A /\ A + Z.of_nat (cells_size cs) <= sh B + rz / 8)
               \/ (sh (M + 16) + rup8 size / 8 <= A /\ A + Z.of_nat (cells_size cs) <= sh B + bs / 8)
               \/ (r + 32 <= A /\ A + Z.of_nat (cells_size cs) <= r + 4096)
               \/ (sh r <= A /\ A + Z.of_nat (cells_size cs) <= sh r + 512)) -> rw_cells asegs mZ A cs).
    { intros A cs HC0 HA. remember (Z.of_nat (cells_size cs)) as k0 eqn:Ek0. assert (K0 : 0 <= k0) by (rewrite Ek0; clear; lia).
      assert (H6 : rw_cells asegs m6 A cs).
      { eapply (rw_cells_transport asegs _ m5b m6); [exact HC0| exact MU6| exact WM6|]. rewrite <- Ek0. cbn [disjoint_from].
        clear - HA K0 SF1 SF3 SF5 SF6 SF7 SHG1 SHG2 SHR3 BLO MR1 MR2 MR4 MR5 SZR LOH LOQ CS CLO EB ALOW AMu EMSZ. lia. }
      assert (H7 : rw_cells asegs m7 A cs).
      { destruct (Z.eq_dec (size mod 8) 0) as [EZ|NZ]; [rewrite (EQ7 EZ); exact H6|].
        eapply (rw_cells_transport asegs _ m6 m7); [exact H6| exact MU7| exact WM7|]. rewrite <- Ek0. cbn [disjoint_from]. pose proof (SF4 NZ) as SF4'.
        clear - HA K0 SF1 SF4' SF5 SF6 SF7 SHG1 SHG2 SHR3 BLO MR1 MR2 MR4 MR5 SZR EB ALOW LOH AMu EMSZ. lia. }
      assert (H8 : rw_cells asegs m8 A cs).
      { eapply (rw_cells_transport asegs _ m7 m8); [exact H7| exact MU8| exact WM8|]. rewrite <- Ek0. cbn [disjoint_from].
        clear - HA K0 SF1 SF3 SF5 SF6 SF7 SHG1 SHG2 SHR3 BLO MR1 MR2 MR4 MR5 SZR LOH LOQ CS CLO APT T3 T4 ACR EB EMSZ ALOW AMu. lia. }
      assert (H9 : rw_cells asegs m9 A cs).
      { eapply (rw_cells_transport asegs _ m8 m9); [exact H8| exact MU9| exact WM9|]. rewrite <- Ek0. cbn [disjoint_from].
        clear - HA K0 SF1 SF3 SF5 SF6 SF7 SHG1 SHG2 SHR3 BLO MR1 MR2 MR4 MR5 SZR EB ALOW LOH AMu EMSZ. lia. }
      eapply (rw_cells_transport asegs _ m9 mZ); [exact H9| exact MUZ| exact WMZ|]. rewrite <- Ek0. cbn [disjoint_from].
      clear - HA K0 SF1 SF3 SF5 SF6 SF7 SHG1 SHG2 SHR3 BLO MR1 MR2 MR4 MR5 SZR LOH LOQ CS CLO EB ALOW AMu EMSZ. lia. }

    assert (T3Z : forall A cs, rw_cells asegs m3 A cs ->
              ((B + 16 <= A /\ A + Z.of_nat (cells_size cs) <= M) \/ (M + 16 + size <= A /\ A + Z.of_nat (cells_size cs) <= B + bs)
               \/ (r + 32 <= A /\ A + Z.of_nat (cells_size cs) <= r + 4096) \/ (sh r <= A /\ A + Z.of_nat (cells_size cs) <= sh r + 512)) -> rw_cells asegs mZ A cs).
    { intros A cs HC0 HA. apply TRbZ; [apply TR5b; [apply TR35; [exact HC0|]|]|].
      - clear - HA EB EMSZ MR1 MR2 MR4 SZR SHG2 SHG3. lia.
      - clear - HA EB EMSZ MR1 MR2 MR4 SZR. lia.
      - clear - HA. lia. }
    assert (LREP : lchunk_rep AL mZ (mkQC (QSec (mkSC r msz needed)) rz size)).
    { unfold lchunk_rep. cbn [qc_kind qc_rz qc_n]. unfold qc_hdr, qc_blk, qc_bsize. cbn [qc_kind qc_rz sc_beg sc_msize]. rewrite <- EB.
      replace (B + rz - 16) with M by (clear - EM; lia). replace (msz - 4096) with bs by (clear - EMSZ; lia).
      split.
      { exists bitsZ, actx. split; [exact B3Z|]. unhideB HDb. unhideB ACX. change (Z.of_nat 2) with 2 in HDb.
        apply (hdr_join mZ M bitsZ size actx HDZ).
        - apply TRbZ; [apply TR5b; [exact HDb|]|]; [left| right; left]; cbn [cells_size csize Nat.add]; [clear - MR1 MR2 MR4 SZR EB EMSZ; lia| clear; lia].
        - apply TRbZ; [apply TR5b; [exact ACX|]|]; [left| right; left]; cbn [cells_size csize Nat.add]; [clear - MR1 MR2 MR4 SZR EB EMSZ; lia| clear; lia]. }
      split.
      { intros RZ16. assert (NBM : B <> M) by (clear - MR5; lia). split; [exact (LCHZ NBM)|].
        assert (LE32 : (16 + Z.to_nat (rz - 32) <= Z.to_nat (rz - 16))%nat) by (clear - RZV; lia).
        unhideB LRZ. destruct (cb_split3 m3 B (Z.to_nat (rz - 16)) j0 16 (Z.to_nat (rz - 32)) LE32 LRZ) as (_ & lr & _ & _ & LRest & _).
        exists lr. change (Z.of_nat 16) with 16 in LRest. apply T3Z; [exact LRest|].
        left. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (clear - RZV; lia). clear - EM. lia. }
      split; [exists ubZ; exact UBZ|].
      split.
      { exists sl. unhideB SLK. assert (SLN : 0 <= bs - rz - size) by (clear - MR2 MR4 EM; lia).
        apply T3Z; [exact SLK|]. right; left. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by exact SLN. clear - EM. lia. }
      split.
      { unhideB SHL. unfold fa_bytes. apply TRbZ; [exact SHL|]. right; right; right; left. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by exact SF5. clear. lia. }
      split; [exact (block_shadow_cells mZ (sh (M + 16)) size ltac:(clear - SZR; lia) SHZ SHPZ)|].
      split.
      { unhideB SHRr. unfold fa_bytes. apply TRbZ; [exact SHRr|]. right; right; right; right; left. cbn [cells_size csize Nat.add].
        rewrite Nat.add_0_r, Z2Nat.id by (rewrite SF8; clear - SF6 SF1; lia). rewrite SF2, SF8. clear - SF1. lia. }
      split.
      - exists (repeat (Z_to_bv 8 0) (Z.to_nat 4064)). unhideB HPG. apply T3Z; [exact HPG|]. right; right; left. cbn [cells_size csize Nat.add]. clear. lia.
      - unhideB SHH. unfold fa_bytes. apply T3Z; [exact SHH|]. right; right; right. cbn [cells_size csize Nat.add]. clear. lia. }

    pose proof (munch_joinP _ _ _ _ _ MU5a MU5b) as MUa. pose proof (munch_joinP _ _ _ _ _ MUa MU6) as MUb. pose proof (munch_joinP _ _ _ _ _ MUb MU7) as MUc.
    pose proof (munch_joinP _ _ _ _ _ MUc MU8) as MUd. pose proof (munch_joinP _ _ _ _ _ MUd MU9) as MUe. pose proof (munch_joinP _ _ _ _ _ MUe MUZ) as MU5Z.
    cbn [app] in MU5Z. clear MUa MUb MUc MUd MUe.
    assert (SHB8 : sh B + bs / 8 + 8 <= 17594333495296) by (unfold sh, SHADOW_OFF; clear - BLO ACR BS4K; Z.div_mod_to_equations; lia).
    assert (RDZ : RDEPOT D hs' total' mZ).
    { eapply RDEPOT_frame_m; [exact DLO| exact SWB| exact RD5| exact MU5Z| | |]; cbn [disjoint_from]; rewrite ?SF2, ?SF8.
      - clear - LOQ CS LOH SHB8 SHR3 SHG1 SHG2 SU1 SU2 SF1 SF3 SF5 SF6 SF7 BLO MR1 MR2 MR4 MR5 SZR T3. lia.
      - clear - LOQ CS CLO N1d N2d SHB8 SHR3 SHG1 SHG2 SU1 SU2 SF1 SF3 SF5 SF6 SF7 BLO MR1 MR2 MR4 MR5 SZR ADN A35 EB EMSZ. lia.
      - clear - LOQ CS CLO SS1 SS2 SHB8 SHR3 SHG1 SHG2 SU1 SU2 SF1 SF3 SF5 SF6 SF7 BLO MR1 MR2 MR4 MR5 SZR ASS A36 EB EMSZ. lia. }

    unhideB MU12. unhideB WM12. unhideB MU3. unhideB WM3. unhideB GM3.
    assert (MU7c : munch (if size mod 8 =? 0 then [] else [(sh (M + 16) + size / 8, sh (M + 16) + size / 8 + 1)]) m6 m7).
    { destruct (Z.eqb_spec (size mod 8) 0) as [EZ|NZ]; [rewrite (EQ7 EZ); apply munch_refl| exact MU7]. }
    pose proof (munch_joinP _ _ _ _ _ MU4 MUD) as K1. pose proof (munch_joinP _ _ _ _ _ K1 MU5) as K2. pose proof (munch_joinP _ _ _ _ _ K2 MU5a) as K3.
    pose proof (munch_joinP _ _ _ _ _ K3 MU5b) as K4. pose proof (munch_joinP _ _ _ _ _ K4 MU6) as K5. pose proof (munch_joinP _ _ _ _ _ K5 MU7c) as K6.
    pose proof (munch_joinP _ _ _ _ _ K6 MU8) as K7. pose proof (munch_joinP _ _ _ _ _ K7 MU9) as K8. pose proof (munch_joinP _ _ _ _ _ K8 MUZ) as MU3Z.
    clear K1 K2 K3 K4 K5 K6 K7 K8.
    pose proof (munch_joinP _ _ _ _ _ (munch_joinP _ _ _ _ _ MU12 MU3) MU3Z) as MUfin.
    pose proof (gmunch_munch _ _ _ _ _ (gmunch_join _ _ _ _ _ (gmunch_of_munch _ _ _ MU12) GM3) MU3Z) as GMfin.
    pose proof (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _
                 (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _ WM12 WM3) WM4) WMD) WM5) WM5a) WM5b) WM6) WM7) WM8) WM9) WMZ) as WMfin.
    pose proof (sw_bounds r msz ALOW ltac:(clear - EMSZ BSR SN1; lia)) as (SWB1 & SWB2 & _). rewrite <- Ewal in SWB1. rewrite <- Ewah in SWB2.
    assert (SHE : sh (r + msz) = sh r + msz / 8) by (unfold sh; clear - A4K EMSZ BS4K; Z.div_mod_to_equations; lia).
    rewrite SHE in SWB2.

    set (cls := fun iv : Z * Z => atouch AL lo q (fst X) (snd X) [] [] iv \/ sub_iv r (r + msz) iv \/ sub_iv wal wah iv \/ sub_iv wpl wph iv \/ dstat iv \/ dreg AL iv).
    set (gcls := fun iv : Z * Z => atouch AL lo q (fst X) (snd X) [] [] iv \/ sub_iv r (r + msz) iv \/ sub_iv (sh r) (sh r + msz / 8) iv \/ dstat iv \/ dreg AL iv).
    assert (CG : forall iv, atouch AL lo q (fst X) (snd X) [] [] iv \/ sub_iv r (r + msz) iv \/ sub_iv (sh r) (sh r + msz / 8) iv \/ dstat iv \/ dreg AL iv -> cls iv /\ gcls iv).
    { intros iv C0. unfold cls, gcls. split; [| exact C0].
      destruct C0 as [C0|[C0|[C0|[C0|C0]]]].
      - left; exact C0.
      - right; left; exact C0.
      - right; right; left. unfold sub_iv in *. clear - C0 SWB1 SWB2. lia.
      - right; right; right; right; left; exact C0.
      - right; right; right; right; right; exact C0. }
    assert (CST : forall a b, lo <= a -> b <= q -> cls (a, b) /\ gcls (a, b)) by (intros a b Ha Hb; apply CG; left; left; unfold sub_iv; cbn [fst snd]; lia).
    assert (CBL : forall a b, r <= a -> b <= r + msz -> cls (a, b) /\ gcls (a, b)) by (intros a b Ha Hb; apply CG; right; left; unfold sub_iv; cbn [fst snd]; lia).
    assert (CSH : forall a b, sh r <= a -> b <= sh r + msz / 8 -> cls (a, b) /\ gcls (a, b)) by (intros a b Ha Hb; apply CG; right; right; left; unfold sub_iv; cbn [fst snd]; lia).
    assert (CDS : forall a b, 1595336 <= a -> b <= 5855224 -> cls (a, b) /\ gcls (a, b)) by (intros a b Ha Hb; apply CG; right; right; right; left; unfold dstat; cbn [fst snd]; lia).
    lazymatch type of MU3Z with munch ?w _ _ => assert (F3Z : Forall (fun iv => cls iv /\ gcls iv) w) end.
    { unfold zlen in *. repeat (apply Forall_app; split); repeat (apply Forall_cons || apply Forall_nil).
      all: try (apply CST; clear - LOQ CS; lia).
      all: try (apply CDS; clear - BKR; lia).
      all: try (apply CBL; clear - MR1 MR2 MR4 MR5 SZR EB EMSZ; lia).
      all: try (apply CSH; rewrite ?SF2, ?SF8; clear - SHG1 SHG2 SF1 SF3 SF5 SF6 SF7 SU1 SU2; lia).
      - apply CG. right; right; right; right. unfold dreg. cbn [fst snd]. left. clear - ROOM_N. lia.
      - apply CG. right; right; right; right. unfold dreg. cbn [fst snd]. right. clear - ROOM_F SWB T0. lia.
      - destruct (Z.eqb_spec (size mod 8) 0) as [EZ|NZ]; [apply Forall_nil|]. repeat (apply Forall_cons || apply Forall_nil). pose proof (SF4 NZ) as SF4'.
        apply CSH; clear - SHG1 SHG2 SF1 SF4' SF5 SF6 SF7; lia.
      - apply CG. left. right; right; left. unfold sub_iv. cbn [fst snd]. clear. lia. }
    lazymatch type of MU12 with munch ?w _ _ => assert (F12 : Forall (fun iv => cls iv /\ gcls iv) w) end.
    { repeat (apply Forall_cons || apply Forall_nil); apply CST; clear - LOQ CS; lia. }
    lazymatch type of MU3 with munch ?w _ _ => assert (F3m : Forall cls w) end.
    { repeat (apply Forall_cons || apply Forall_nil).
      - apply CST; clear - LOQ CS; lia.
      - left. right; left. unfold sub_iv. cbn [fst snd]. clear. lia.
      - left. right; left. unfold sub_iv. cbn [fst snd]. clear. lia.
      - left. right; right; left. unfold sub_iv. cbn [fst snd]. clear. lia.
      - left. do 7 right. unfold sub_iv. cbn [fst snd]. clear. lia.
      - apply CBL; clear; lia.
      - right; right; left. unfold sub_iv. cbn [fst snd]. clear. lia.
      - right; right; right; left. unfold sub_iv. cbn [fst snd]. clear. lia. }
    lazymatch type of GM3 with gmunch ?w _ _ => assert (F3g : Forall gcls w) end.
    { repeat (apply Forall_cons || apply Forall_nil).
      - apply CST; clear - LOQ CS; lia.
      - left. right; left. unfold sub_iv. cbn [fst snd]. clear. lia.
      - left. right; left. unfold sub_iv. cbn [fst snd]. clear. lia.
      - left. right; right; left. unfold sub_iv. cbn [fst snd]. clear. lia.
      - left. do 7 right. unfold sub_iv. cbn [fst snd]. clear. lia.
      - apply CBL; clear; lia.
      - apply CSH; clear; lia. }
    lazymatch type of MUfin with munch ?w _ _ => assert (FCLS : Forall cls w) end.
    { apply Forall_app; split; [apply Forall_app; split|]; [eapply Forall_impl; [| exact F12]; intros iv [C0 _]; exact C0| exact F3m| eapply Forall_impl; [| exact F3Z]; intros iv [C0 _]; exact C0]. }
    lazymatch type of GMfin with gmunch ?w _ _ => assert (FGCLS : Forall gcls w) end.
    { apply Forall_app; split; [apply Forall_app; split|]; [eapply Forall_impl; [| exact F12]; intros iv [_ C0]; exact C0| exact F3g| eapply Forall_impl; [| exact F3Z]; intros iv [_ C0]; exact C0]. }
    clear F12 F3m F3g F3Z.

    assert (CKN : chunk_ok AL (mkSC r msz needed)).
    { pose proof RS3 as ((_ & _ & _ & _ & _ & COK & _) & _). unfold sec_alloc in COK. cbn [se_chunks] in COK.
      apply Forall_app in COK. destruct COK as [_ COK]. rewrite Emsz. exact (Forall_inv COK). }
    assert (SEN : se_n (sec_alloc (snd X) r needed) = se_n (snd X) + 1).
    { unfold se_n, sec_alloc. cbn [se_chunks]. rewrite length_app. cbn [length]. clear. lia. }
    assert (SLACK : rz + rup8 size + 16 <= msz - 4096) by (clear - FIT BSR EMSZ; lia).
    assert (CLS0 : a0_cls size = 0) by (rewrite EALN; exact ECLS).

    replace (q - 128 + 128) with q in * by (clear; lia).
    clear ERZ RZV EALN.
    subst M. subst B. subst rz. subst size. subst wal. subst wah. subst wpl. subst wph. subst pw. subst msz. subst needed.
    lz_ret. apply evt_done. unfold allocate_post_s. cbv zeta.
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, mZ, _, _, hs', total'.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact MUfin|]. split; [exact WMfin|]. split; [exact FCLS|].
    split; [exact GMfin|]. split; [exact FGCLS|].
    split; [exact INVZ|]. split; [exact WFch|]. split; [exact HELD|]. split; [exact LREP|]. split; [exact STZ|].
    split; [reflexivity|]. split; [exact SEN|]. split; [exact CKN|].
    split; [exact A4K|]. split; [exact ALOW|]. split; [exact AM|]. split; [exact APL|]. split; [exact AV|].
    split; [exact SLACK|]. split; [exact CLS0|]. split; [exact RDZ| exact RES].
  Qed.
End ALLOCS.

