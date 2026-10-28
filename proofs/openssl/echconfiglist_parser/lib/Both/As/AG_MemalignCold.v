(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocBudget AllocRep AllocRepFacts AllocRepFacts2 AllocRepX CidBits CidBits2
     AsDepotInv AsDepotHash AsUnwind AW_DepotFrame AW_MallocBase AW_AllocBase AW_InitCache AW_Efs AW_Populate
     AW_Refill AW_MallocHead AW_MallocTail AW_AllocBaseAl AW_Memalign AW_MemalignHead AW_MemalignTail AG_WFHit AG_MallocModel AG_RefillModel AG_ColdModel AG_Malloc AG_Malloc2 AG_Memalign2 AG_WriteSet AG_MallocCold
     AS_Refill1 AS_Refill2 AS_Refill4 AG_Refill1 AG_Refill2 AG_Refill3 SecLazy AllocWalkKit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section MemalignColdGlue.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo size : Z) (CH : list (Z * Z)).

  (* [comment removed for export] *)
  Let st := a_st s.
  Let TH := a_thr s.
  Let sb := a_sb s.
  Let CTX := a_ctx s.
  Let rz := rz_size size.
  Let needed := round_up (Z.max size 8) 8 + rz.
  Let c := class_id needed.
  Let csz := class_size c.
  Let csz8 := csz / 8.
  Let CA := TH + 208.
  Let P := CA + 80 * c.
  Let RI := a_ri s + 128 * c.
  (* [comment removed for export] *)
  Let r := get_region st c.
  Let nf := rg_num_freed r. Let mfa := rg_mapped_free_array r. Let au := rg_allocated_user r. Let mu := rg_mapped_user r. Let fl := rg_free_array r.
  Let n := rf_n c.
  Let mu' := rf_mu' c nf au mu. Let nnew := rf_nnew c nf au mu. Let nf1 := rf_nf1 c nf au mu. Let mfa' := rf_mfa' c nf mfa au mu.
  Let au' := rf_au' c nf au mu. Let fl1 := rf_fl1 c nf au mu fl.
  (* [comment removed for export] *)
  Let st2 := refilled st c.
  Let chunks2 := firstn (Z.to_nat n) fl1.
  Let cp := hd 0 chunks2.
  Let AB := compact_to_addr st2 c cp.
  Let U := AB + rz.
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CH.
  Let T := utrace 0x1bfb98 (bv_unsigned sp) (a_top s) (a_bot s) 30 CHI.
  Let nT := Z.of_nat (length T).
  Let id := d_putid d (depot_hash T).
  Let d' := d_put d (depot_hash T) nT.
  (* [comment removed for export] *)
  Let L2 : list (word * word) :=
    if mfa <? mfa' then maps_subtract (if mu <? mu' then maps_subtract (a_L s) (RB s c + mu) (RB s c + mu') else a_L s) (FA s c + mfa) (FA s c + mfa')
    else (if mu <? mu' then maps_subtract (a_L s) (RB s c + mu) (RB s c + mu') else a_L s).
  Let S2 : list (word * word) :=
    (if mfa <? mfa' then [(wz (sh (FA s c + mfa)), wz ((mfa' - mfa) / 8))] else [])
    ++ (if mu <? mu' then [(wz (sh (RB s c + mu)), wz ((mu' - mu) / 8))] else []) ++ a_S s.
  Let sR := mkAst st2 (a_thr s) (a_ctx s) (a_fsb s) L2 S2 (a_Zr s) (a_AL s) (a_top s) (a_bot s).   (* [comment removed for export] *)
  Let ch := mkChunk AB U size rz c CAllocated.
  Let st3 := hit_state st2 c n (tl chunks2) ch.
  Let sF := mkAst st3 (a_thr s) (a_ctx s) (a_fsb s) L2 S2 (a_Zr s) (a_AL s) (a_top s) (a_bot s).
  (* [comment removed for export] *)
  Let Wr : list ivl := (lo, bv_unsigned sp) :: (TH + 3168, TH + 3169) :: rf_W lo (bv_unsigned sp) P RI (FA s c) (RB s c) TH CA nf mfa mu mfa' mu'.
  Let Wt : list ivl := (lo, bv_unsigned sp) :: (P, P + 4) :: (CA + 2576, CA + 2584) :: (AB, AB + csz) :: (sh AB, sh AB + csz8)
                       :: (TH + 2800, TH + 3169) :: depot_W d.
  Let mc_W : list ivl := Wr ++ Wt.

  Hypothesis HR : ARHEAP s LB m.
  Hypothesis AX : awin_vis s m /\ flagsx_rep m.
  Hypothesis AMX : AMODELX s mo.
  Hypothesis DEP : DEPOT asegs d m.
  Hypothesis DPL : depot_placed s d.
  Hypothesis DCOV : depot_cov d mo.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 3040 <= bv_unsigned sp.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis SZ : 1 <= size /\ needed <= kMaxSize.
  Hypothesis MISS : pc_count (get_pc st c) = 0.
  Hypothesis TP : tp = wz ATP.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + 31 <= 131072.
  Hypothesis FCH : goodframe (a_bot s) (bv_unsigned sp) (a_top s) = true -> goodframe (bv_unsigned sp) (bv_unsigned s0) (a_top s) = true ->
                   bv_unsigned sp + 16 <= bv_unsigned s0 /\ frame_chain asegs m (a_top s) (bv_unsigned s0) CH.
  (* [comment removed for export] *)
  Hypothesis PROOM : pusage st + COLD_COST <= B_PRIM.      (* [comment removed for export] *)
  Hypothesis ROOM : mu + 2 * kUserMapSize <= kFreeArrayOffset.
  Hypothesis OK : lzok asegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo).
  Hypothesis VISE : restrict (a_L s) (a_S s) msF
    = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1bfaf8) fc None m (seg_rom asegs).
  (* [comment removed for export] *)
  Variable MP : Z. Variable pjunk : word.
  Hypothesis Ha0 : a0 = wz MP. Hypothesis Ha1 : a1 = wz 64. Hypothesis Ha2 : a2 = wz size.
  Hypothesis SZP : hidden (size = 32768).
  Hypothesis MPR : 0 <= MP /\ MP + 8 <= 2^64.
  Hypothesis MPDJ : hidden (forall a, MP <= a < MP + 8 -> outside mc_W a).
  Hypothesis PW : rw_cells asegs m MP [C8 pjunk].
  Let neededA := round_up (Z.max size 8) 64 + 64 + rz.

  (* [comment removed for export] *)
  Definition memalign_cold_gpost (msF' : machine_state) (mo' : Model) : Prop :=
    exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m1 m' : mem),
       lzok asegs (a_L sF) (a_S sF) (a_Zr sF) (mkCfg msF' mo')
    /\ restrict (a_L sF) (a_S sF) msF'
       = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ ARHEAP sF ((U, size) :: LB) m1 /\ awin_vis sF m1 /\ flagsx_rep m1 /\ AMODELX sF mo' /\ nonvm_same mo mo'
    /\ DEPOT asegs d' m1 /\ depot_placed sF d' /\ depot_cov d' mo'
    /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp)
    /\ munch mc_W m m1 /\ wmono asegs m m1
    /\ avmx s sF mo mo'
    /\ (exists junk, rw_cells asegs m1 U [CB (Z.to_nat size) junk]) /\ addressable m1 U size
    /\ (forall kaddr, exists st'' ev, am_malloc_k st size kaddr = Some (U, st'', ev) /\ same_but_shadow st'' st3)
    /\ U mod 64 = 0
    /\ munch [(MP, MP + 8)]%Z m1 m' /\ wmono asegs m1 m' /\ mem_inv asegs m' /\ rw_cells asegs m' MP [C8 (wz U)] /\ stk asegs m' lo (bv_unsigned sp)
    /\ m' = write_to_mem m1 (wa MP) (le8 (wz U)).

  Let R : AREP s m. Proof. exact (proj1 HR). Qed.
  Let OKs : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OKs). Qed.
  Let WFs : WF st. Proof. exact (proj2 OKs). Qed.

  (* [comment removed for export] *)
  Let RQ : rq_rz (compute_req size) = rz /\ rq_needed (compute_req size) = needed /\ rq_primary (compute_req size) = true
           /\ rq_size (compute_req size) = size /\ 16 <= rz <= 2048 /\ size + rz <= needed /\ needed < size + rz + 8 /\ 8 + rz <= needed.
  Proof.
    pose proof (rz_size_facts size) as (RZ & _). unfold compute_req. replace (size =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn -[Z.add Z.mul Z.max round_up rz_size Z.leb Z.ltb Z.eqb].
    replace (round_up (Z.max size 8) 8 + rz_size size <=? kMaxSize) with true by (symmetry; apply Z.leb_le; subst needed rz; lia).
    subst needed rz. unfold round_up. repeat split; try reflexivity; Z.div_mod_to_equations; (first [clear - RZ H0 H SZ; lia | lia]).
  Qed.
  Let HC : 1 <= c <= 30.
  Proof. subst c. apply class_id_le30. destruct RQ as (_ & _ & _ & _ & A & B & _). unfold kMaxSize in SZ. lia. Qed.
  Let CSZ : 32 <= csz <= 65536 /\ needed <= csz /\ csz mod 32 = 0 /\ 8 * csz8 = csz.
  Proof.
    pose proof (class_size_table_facts c ltac:(hci; lia)) as (T1 & T2 & T3 & _). subst csz8 csz.
    pose proof (class_size_ge needed ltac:(hci; unfold kMaxSize in SZ; destruct RQ as (_ & _ & _ & _ & A & B & _); lia)). subst c.
    repeat split; try (first [clear - T3 HC T1 H T2; lia | lia]); Z.div_mod_to_equations; lia.
  Qed.
  Let RF := rf_facts st c WFs HC ROOM.
  Let PURE := refill_pure s m c R HC MISS.
  Let NR : 1 <= n <= 8 /\ n + n = max_count c.
  Proof.
    pose proof (max_count_facts c ltac:(hci; clear - HC; try acb; lia)) as MCF. clear - MCF; try acb. subst n; unfold rf_n; destruct MCF as [M1 M2].
    destruct (proj1 (Z.even_spec _) M2) as [k Hk]; rewrite Hk in *; rewrite (Z.mul_comm 2 k), Z.div_mul by lia; lia.
  Qed.

  (* [comment removed for export] *)
  Tactic Notation "bands_as" simple_intropattern(p) :=
    (let X := fresh "BX" in
     lazymatch goal with B : hidden ((TH + 4096 <= 65536 \/ _) /\ _) |- _ => pose proof B as X; destruct X as [p] end).

  Theorem memalign_arep_cold :
    (forall msF' mo', memalign_cold_gpost msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF mo).
  Proof.
    intros K.
    pose proof PL as (Y1 & Y2 & Y3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    pose proof DPL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    destruct AX as [AWV FXR]. destruct AMX as [AM AK]. pose proof AM as AM'. destruct AM' as (AIL & ASV & AB0). destruct AIL as (IL1 & IL2 & IL3 & NOV & NW & NWA).
    pose proof (ienv_of_arep s m R) as IEN. rewrite <- TP in IEN.
    assert (UNW : rw_cells asegs m (TH + 3168) [C1 (b8 0)]).
    { pose proof (proj1 HR) as RR. destruct RR as (_ & _ & _ & THR & _). destruct THR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & U0). exact U0. }
    destruct (refill_cells_of_arep s m c R HC MISS) as (q0 & q1 & q2 & q3 & PC1 & PCJ & FAM & QST & TST & RIC & RIJ & EXH & RST & FARR & FAJ & USJ & REN).
    pose proof PURE as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9 & U10 & PCS).
    fold st in U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, RIC, FARR, FAJ, USJ. fold r in U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, RIC, FARR, FAJ, USJ.
    fold nf mfa au mu fl in U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, RIC, FARR, FAJ, USJ.
    assert (BND : 4096 <= TH /\ TH + 4096 <= aceil /\ TH mod 4096 = 0 /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil
            /\ sb mod 65536 = 0 /\ 12599296 <= CTX /\ CTX + 160 <= aceil /\ 12599296 <= a_pa s /\ a_pa s + 8388608 <= aceil
            /\ 12599296 <= d_nb d /\ d_nb d + 16 * 65536 <= aceil /\ 12599296 <= d_sb d /\ d_sb d + 8 * 131072 <= aceil
            /\ 4096 <= a_top s <= 2^47 /\ 0 <= a_bot s < a_top s /\ aceil <= lo /\ 1 <= c <= 30
            /\ P = TH + 208 + 80 * c /\ CA = TH + 208 /\ RI = sb + 137438953472 + 128 * c /\ RB s c = sb + c * 4294967296 /\ FA s c = RB s c + 3758096384).
    { assert (E1 : RB s c = sb + c * 4294967296) by (unfold RB, sb, a_sb; rewrite region_beg_eq; reflexivity).
      assert (E2 : FA s c = RB s c + 3758096384) by (unfold FA, RB; rewrite free_array_base_eq; reflexivity).
      pose proof (akobj_env _ _ T2 ltac:(unfold kPageSize; clear; lia)) as T2e. pose proof (aapp_env _ _ P2 ltac:(unfold kPtrArrayReserve; clear; lia)) as P2e.
      pose proof (aapp_env _ _ X2 ltac:(clear; lia)) as X2e. pose proof (aapp_env _ _ G10 ltac:(clear; lia)) as G10e. pose proof (aapp_env _ _ G12 ltac:(clear; lia)) as G12e.
      clear - Y1 Y2 Y3 P1 P2e P3 T1 T2e T3 X1 X2e X3 TCX G10e G11 G12e G13 LO HC E1 E2; try acb. unfold TH, sb, CTX, P, CA, RI, a_ri. unfold a_sb in *.
      acb. unfold AHI_LO, kSpaceSize, kPageSize, kPtrArrayReserve in *. repeat split; (first [clear - T2e T1 Y2 Y3 Y1 X2e P2e G10e G12e TCX LO HC E1; lia | lia]). }
    (* [comment removed for export] *)
    assert (BANDS : hidden ((TH + 4096 <= 65536 \/ (12599296 <= TH /\ TH + 4096 <= 2147446784) \/ 17594333495296 <= TH)
                   /\ (CTX + 160 <= 2147446784 \/ 17594333495296 <= CTX)
                   /\ (a_pa s + 8388608 <= 2147446784 \/ 17594333495296 <= a_pa s)
                   /\ (d_nb d + 16 * 65536 <= 2147446784 \/ 17594333495296 <= d_nb d)
                   /\ (d_sb d + 8 * 131072 <= 2147446784 \/ 17594333495296 <= d_sb d))).
    { split. split; [exact (akobj_lit _ _ T2)|]. split; [exact (aapp_lit _ _ X2)|].
      split; [pose proof (aapp_lit _ _ P2) as L; unfold kPtrArrayReserve in L; exact L|].
      split; [exact (aapp_lit _ _ G10)| exact (aapp_lit _ _ G12)]. }
    assert (BDJ : (TH + 4096 <= sb \/ sb + 137438953472 + 4096 <= TH) /\ (TH + 4096 <= CTX \/ CTX + 160 <= TH) /\ (CTX + 160 <= sb \/ sb + 137438953472 + 4096 <= CTX)).
    { clear - D2 D3 TCX; try acb. unfold TH, sb, CTX. unfold disj, a_sb, kSpaceSize, kPageSize in *. repeat split; lia. }
    pose proof BDJ as (BDJ1 & BDJ2 & BDJ3).
    (* [comment removed for export] *)
    assert (ERZ : rz = 1024) by (destruct SZP as [SZP']; unfold rz; rewrite SZP'; reflexivity).
    assert (ENA : neededA = 33856) by (destruct SZP as [SZP']; unfold neededA; rewrite ERZ, SZP'; reflexivity).
    assert (EC : c = 29) by (destruct SZP as [SZP']; unfold c, needed; rewrite ERZ, SZP'; reflexivity).
    assert (ECA : class_id neededA = c) by (rewrite ENA, EC; reflexivity).
    assert (ECSZ : csz = 49152) by (unfold csz; rewrite EC; reflexivity).
    assert (SZA : 1 <= size /\ neededA <= kMaxSize) by (split; [exact (proj1 SZ)| rewrite ENA; unfold kMaxSize; clear; lia]).
    pose proof MPDJ as [MPDJ']. unfold mc_W in MPDJ'.
    assert (MPDJr : forall a, MP <= a < MP + 8 -> outside Wr a) by (intros xa Hxa; exact (proj1 (proj1 (outside_app Wr Wt xa) (MPDJ' xa Hxa)))).
    assert (MPDJt : hidden (forall a, MP <= a < MP + 8 -> outside Wt a)) by (constructor; intros xa Hxa; exact (proj2 (proj1 (outside_app Wr Wt xa) (MPDJ' xa Hxa)))).
    clear MPDJ'.
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs (a_L s) (a_S s) (a_Zr s) _ msF _ mo Q OK VISE).
    { eapply (@memalign_head _ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo size d
                ATSD CTX TH (a_top s) (a_bot s) CH sb (wz (if as_cache_inited st then max_count c else 0)) MP rz neededA c CA P).
      - constructor. repeat split; try reflexivity. symmetry; exact ECA.
      - exact LO.
      - clear - HI; try acb; lia.
      - constructor. exact SPA.
      - constructor. exact SPT.
      - exact SZA.
      - constructor. rewrite TP. unfold wz, ATP, AIMG_TOP. rewrite unsigned_lit by (clear; lia). clear; lia.
      - constructor. unfold ATSD, AIMG_TOP. unfold kPageSize in T2. clear - BND T2 X2; try acb.   (* [comment removed for export] *)
        repeat match goal with |- _ /\ _ => split end; first [assumption | lia | Z.div_mod_to_equations; lia].
      - constructor. unfold kSpaceSize. clear - BDJ; try acb. lia.
      - constructor. unfold kSpaceSize. unfold disj, kSpaceSize, kPageSize in G1, G2, G3, G4, G5, G6. clear - G1 G2 G3 G4 G5 G6 G10 G12 BND; try acb. unfold TH, sb, CTX in *. unfold a_sb in *.
        repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
      - constructor. unfold AHI_LO, kSpaceSize. acb. clear - BND; try acb. lia.
      - constructor. clear - BND; try acb. lia.
      - clear - BND; try acb. lia.
      - exact FCH.
      - exact Ha0.
      - exact Ha1.
      - exact Ha2.
      - exact IEN.
      - exact MI.
      - exact ST.
      - exact PC1.
      - exact UNW.
      - exact DEP. }
    cbv beta. intros msF1 mo1 OK1 SBM1 _ PO1.
    destruct PO1 as (t0_1 & t1_1 & t2_1 & a4_1 & a5_1 & a6_1 & a7_1 & t3_1 & t4_1 & t5_1 & t6_1 & jk & j8 & rest & m1 & VIS1 & MU1 & WM1 & MI1 & AEN1 & LR & TRNG & NRT
                     & ST1 & FRC1 & AFR1 & FRA1 & FRB1 & FRM1 & PC1' & UNW1 & DEP1).
    (* [comment removed for export] *)
    pose proof (munch_agree _ _ _ MU1) as AG1.
    assert (PW1 : rw_cells asegs m1 MP [C8 pjunk]).
    { eapply (rw_cells_transport_pt _ _ _ AG1 WM1); [exact PW|]. change (Z.of_nat (cells_size [C8 pjunk])) with 8. intros xa Hxa.
      pose proof (MPDJr xa Hxa) as D. unfold Wr in D. cbn [outside] in D |- *. clear - D. tauto. }
    assert (Z1 : forall a, a < lo /\ a <> TH + 3168 -> outside [(lo, bv_unsigned sp); (TH + 3168, TH + 3169)] a).
    { intros a Ha. cbn [outside]. clear - Ha; try acb. repeat split; try exact I; lia. }
    pose proof CSZ as (CS1 & CS2 & CS3 & CS4).
    assert (BR : 0 <= nf /\ 4 * nf <= mfa /\ mfa <= 536870912 /\ 0 <= au <= mu /\ mu + 262144 <= 3758096384 /\ Z.of_nat (length (wlist (rev fl))) = nf /\ 32 <= csz <= 65536)
      by (clear - U1 U2 U4 U5 U8 CS1; try acb; unfold kFreeArraySize, kUserMapSize, kFreeArrayOffset in *; repeat split; lia).
    name_bands.
    pose proof (conj BND (conj BR BDJ1)) as BB. pose proof (conj BND BDJ1) as BD1.
    assert (PCJ1 : stk asegs m1 (a_cache s + PCLASS_SIZE * c + 16) (a_cache s + PCLASS_SIZE * c + 80)) by (unfold a_cache, OT_CACHE, PCLASS_SIZE in *; trp stk_transport_pt AG1 WM1 PCJ Z1 BND).
    assert (FAM1 : forall c', 1 <= c' <= 31 -> exists mc cs, rw_cells asegs m1 (a_cache s + 80 * c' + 4) [C4 mc] /\ rw_cells asegs m1 (a_cache s + 80 * c' + 8) [C8 cs]
                                              /\ (as_cache_inited st = true -> mc = wz (max_count c') /\ cs = wz (class_size c'))).
    { intros c' Hc'. destruct (FAM c' Hc') as (mc & cs & V1 & V2 & V3). exists mc, cs. unfold a_cache, OT_CACHE in *. pose proof (conj BND Hc') as B2.
      split; [trp rw_cells_transport_pt AG1 WM1 V1 Z1 B2|]. split; [trp rw_cells_transport_pt AG1 WM1 V2 Z1 B2| exact V3]. }
    assert (QST1 : rw_cells asegs m1 (TH + 2768) [C8 q0; C8 q1; C8 q2; C8 q3]) by (trp rw_cells_transport_pt AG1 WM1 QST Z1 BND).
    assert (TST1 : stk asegs m1 (TH + 2800) (TH + 3168)) by (trp stk_transport_pt AG1 WM1 TST Z1 BND).
    assert (RIC1 : rw_cells asegs m1 RI [C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz nf); C8 (wz mfa); C8 (wz au); C8 (wz 0); C8 (wz mu); C8 (wz 0)]) by (trp rw_cells_transport_pt AG1 WM1 RIC Z1 BD1).
    assert (RIJ1 : stk asegs m1 (RI + 64) (RI + 68)) by (trp stk_transport_pt AG1 WM1 RIJ Z1 BD1).
    assert (EXH1 : rw_cells asegs m1 (RI + 68) [C1 (b8 0)]) by (trp rw_cells_transport_pt AG1 WM1 EXH Z1 BD1).
    assert (RST1 : stk asegs m1 (RI + 69) (RI + 128)) by (trp stk_transport_pt AG1 WM1 RST Z1 BD1).
    assert (FARR1 : u32arr asegs m1 (FA s c) (wlist (rev fl))) by (trp u32arr_transport_pt AG1 WM1 FARR Z1 BB).
    assert (FAJ1 : stk asegs m1 (FA s c + 4 * nf) (FA s c + mfa)) by (trp stk_transport_pt AG1 WM1 FAJ Z1 BB).
    assert (USJ1 : stk asegs m1 (RB s c + au) (RB s c + mu)) by (trp stk_transport_pt AG1 WM1 USJ Z1 BB).
    assert (REN1 : RENV (wz ATP) ATSD (a_ctx s) TH sb (a_ri s) m1).
    { apply (renv_transport (wz ATP) ATSD (a_ctx s) TH sb (a_ri s) m m1 _ REN MU1 WM1); cbn [disjoint_from]; unfold wz, ATP, ATSD; rewrite ?unsigned_lit by (clear; lia); clear - BND BDJ2; try acb; unfold CTX in *; lia. }
    (* [comment removed for export] *)
    pose proof (AMODELX_mat s mo mo1 (conj AM AK) SBM1) as AMX1. pose proof AMX1 as AMX1'. destruct AMX1' as [AM1 AK1].
    pose proof AM1 as AM1'. destruct AM1' as (AIL1 & ASV1 & AB1). destruct AIL1 as (_ & _ & _ & NOV1 & NW1 & NWA1). destruct AB1 as [AB1a AB1b].
    (* [comment removed for export] *)
    eapply (refill_sreach (a_L s) (a_S s) (a_Zr s) msF1 mo1 Q (wz 0x19b90c) (Z_to_bv 64 (bv_unsigned sp + -2368)) gp tp t0_1 t1_1 t2_1
              (Z_to_bv 64 c) (wz P) a4_1 a5_1 a6_1 a7_1 (wz 8) (wz CA) (wz AINST) (wz size) (wz AINST) (wz (bv_unsigned sp + -2144))
              (Z_to_bv 64 (-64)) (wz 63) (wz TH) (wz 1) t3_1 t4_1 t5_1 t6_1 F fc m1 lo sb c CA TH CTX ATSD nf mfa au mu fl (as_cache_inited st)).
    all: pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64) in SPR.
    { exact LO. }
    { rewrite unsigned_lit by (clear - SPR HI BND; try acb; lia). clear - HI; try acb; lia. }
    { rewrite unsigned_lit by (clear - SPR HI BND; try acb; lia). clear - SPT; try acb; lia. }
    { constructor. rewrite unsigned_lit by (clear - SPR HI BND; try acb; lia). clear - SPA; try acb. Z.div_mod_to_equations. lia. }
    { exact HC. }
    { reflexivity. }
    { unfold AHI_LO, kSpaceSize, kPageSize. acb. clear - BND; try acb. lia. }
    { constructor. clear - BND; try acb. lia. }
    { rewrite TP. unfold wz, ATP, AIMG_TOP. rewrite unsigned_lit by (clear; lia). clear; lia. }
    { unfold ATSD, AIMG_TOP. unfold kPageSize in T2. clear - BND T2 X2; try acb. repeat match goal with |- _ /\ _ => split end; first [assumption | lia]. }
    { constructor. clear - BND; try acb. Z.div_mod_to_equations. lia. }
    { constructor. unfold kSpaceSize. clear - BDJ; try acb. lia. }
    { unfold kFreeArraySize. clear - BR; try acb. lia. }
    { constructor. exact U3. }
    { unfold kUserMapSize, kFreeArrayOffset. clear - BR; try acb. lia. }
    { constructor. exact U6. }
    { exact U7. }
    { exact OK1. }
    { exact VIS1. }
    { exact MI1. }
    { rewrite unsigned_lit by (clear - SPR HI BND; try acb; lia). exact ST1. }
    { rewrite TP. exact REN1. }
    { exact U8. }
    { exact PC1'. }
    { exact PCJ1. }
    { exact FAM1. }
    { exact QST1. }
    { exact TST1. }
    { exact RIC1. }
    { exact RIJ1. }
    { exact EXH1. }
    { exact RST1. }
    all: try replace (sb + c * 2 ^ 32) with (RB s c) by (clear - BND; try acb; lia).
    all: try replace (RB s c + kFreeArrayOffset) with (FA s c) by (unfold kFreeArrayOffset; clear - BND; try acb; lia).
    { exact FARR1. }
    { exact FAJ1. }
    { exact USJ1. }
    { intros a k Ha. exact (ak_resf_hi s mo1 AK1 a k Ha). }
    { intros a k Ha Hk. apply (ak_prim s mo1 AK1 a k c); [unfold kNumClasses; clear - HC; try acb; lia| exact Ha| unfold kRegionSize; exact Hk]. }
    { exact NW1. }
    { exact NWA1. }
    { exact NOV1. }
    { intros x Hx. apply (ak_zr_sb s mo1 AK1). unfold kSpaceSize, kPageSize. clear - Hx BND; try acb. unfold sb in *. lia. }
    { exact (ak_zrsh s mo1 AK1). }
    { exact (ak_lsh s mo1 AK1). }
    { intros x Hx. apply WM1. exact (AWV x Hx). }
    { unfold ABUDGET, aPhi in AB1b. change (a_st s) with st in AB1b. unfold COLD_COST in PROOM. unfold page_size in AB1b. clear - AB1a AB1b PROOM; try acb. lia. }
    { exact U9. }
    { exact U10. }
    { exact (ak_atop s mo1 AK1). }   (* [comment removed for export] *)
    cbv beta. intros msF2 mo2 RD.
    destruct RD as (t0_2 & t1_2 & t2_2 & a1_2 & a2_2 & a3_2 & a4_2 & a5_2 & a6_2 & a7_2 & t3_2 & t4_2 & t5_2 & t6_2 & q0' & q1' & q2' & q3' & m2 & L' & S' & RD).
    lazy zeta in RD.
    destruct RD as (OK2 & VIS2 & EL & ES & NVS & VMM & VMR & VML & VMB & VBRK & VMN & EAG & MU2 & WM2 & MI2 & ST2 & PCN & FAM2 & CHA & CHJ
                    & RI2 & RIJ2 & EXH2 & RST2 & FARR2 & FAJ2 & USJ2 & POIu & POIf & QST2 & TST2).
    fold mu' nnew nf1 mfa' au' fl1 n in VIS2, EL, ES, VMN, EAG, MU2, PCN, CHA, CHJ, RI2, FARR2, FAJ2, USJ2, POIu, POIf.
    rewrite unsigned_lit in MU2, ST2 by (clear - SPR HI BND; try acb; lia).
    subst L' S'. fold L2 in OK2, VIS2. fold S2 in OK2, VIS2.
    (* [comment removed for export] *)
    pose proof RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15).
    fold st r in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11, Q12, Q13. fold nf mfa au mu fl n in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11, Q12, Q13.
    fold mu' nnew nf1 mfa' au' fl1 in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11, Q12, Q13.
    pose proof (rf_mfa_delta st c WFs HC ROOM) as FD. fold r in FD. fold nf mfa au mu in FD. fold mfa' in FD.
    assert (BR2 : mu <= mu' <= mu + 262144 /\ mfa <= mfa' <= mfa + 262144 /\ mfa' <= 536870912 /\ 1 <= n <= 8 /\ n <= nf1 /\ 4 * nf1 <= mfa' /\ au <= au' <= mu').
    { unfold kUserMapSize, kFreeArraySize, kFreeArrayMapSize in Q7, Q12, FD. clear - Q1 Q6 Q7 Q11 Q12 FD NR; try acb. repeat split; lia. }
    assert (SHB : 0x2008fff7000 <= sh (RB s c + mu) /\ sh (RB s c + mu) + (mu' - mu) / 8 <= (sh aceil)
                /\ 0x2008fff7000 <= sh (FA s c + mfa) /\ sh (FA s c + mfa) + (mfa' - mfa) / 8 <= (sh aceil)).
    { clear - BND BR BR2; try acb. unfold sh, ASHADOW_BASE. Z.div_mod_to_equations. lia. }
    pose proof (conj BND (conj BR BR2)) as BB2.
    (* [comment removed for export] *)
    assert (UNW2 : rw_cells asegs m2 (TH + 3168) [C1 (b8 0)]).
    { eapply rw_cells_transport; [exact UNW1| exact MU2| exact WM2|]. unfold rf_W. cbn [disjoint_from cells_size csize Z.of_nat Nat.add Pos.of_succ_nat].
      unfold PCLASS_SIZE, REGIONINFO_SIZE, kSpaceSize.
      bands_as (BT & _).
      repeat lazymatch goal with
        | |- disjoint_from (icW _) _ _ => apply icW_disjoint; clear - BND; try acb; lia
        | |- _ /\ _ => split; [clear - BB2 SHB BDJ1 BT; try acb; (first [clear - BB2 BDJ1 ACEILB BT SHB; lia | lia])|]
        end. }
    (* [comment removed for export] *)
    pose proof (wmono_trans _ _ _ _ WM1 WM2) as WM02.
    assert (AG02 : agree_on (outside Wr) m m2).
    { intros x Hx Hr. transitivity (m1 (wa x)).
      - apply MU2. rewrite wa_unsigned by exact Hr. revert Hx. unfold Wr, rf_W. cbn [outside app]. clear - HI; try acb. intros (X1 & X2 & X3 & REST).
        split; [clear - X1 HI; try acb; lia| exact REST].
      - apply MU1. rewrite wa_unsigned by exact Hr. revert Hx. unfold Wr. cbn [outside]. clear. intros (X1 & X2 & _). repeat split; try exact I; assumption. }
    pose proof (arep_after_refill s m m2 c L2 S2 (a_AL s) lo (bv_unsigned sp) q0' q1' q2' q3' R HC MISS ROOM LO AG02 WM02
                  PCN FAM2 CHA CHJ RI2 RIJ2 EXH2 RST2 FARR2 FAJ2 USJ2 POIu POIf QST2 TST2 UNW2) as R2.
    pose proof (flagsx_after_refill s m m2 c lo (bv_unsigned sp) R HC MISS ROOM LO AG02 WM02 FXR) as FX2.
    assert (HAL : 0 <= a_AL s <= a_AL s) by (clear - AB1a; lia).   (* [comment removed for export] *)
    pose proof (amodelx_after_refill s mo1 mo2 c L2 S2 (a_AL s) AMX1 OKs HC ROOM (lazy_ranges_okb_nowrap asegs _ (lzok_ranges OK))
                  eq_refl eq_refl VMM VMR VML (nonvm_same_atop _ _ NVS) VMN EAG HAL) as AMX2.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (rfd_pc_c st c WFs HC ROOM) as PCc.
    assert (HIT2 : pc_count (get_pc st2 c) <> 0) by (unfold st2; rewrite PCc; cbn [pc_count refill_pc]; fold n; clear - NR; try acb; lia).
    pose proof (hit_cells_of_arep sR m2 R2 c ltac:(hci; unfold kNumClasses; clear - HC; try acb; lia) HIT2) as HCL. cbv zeta in HCL.
    cbn [a_st a_cache a_sb a_thr] in HCL. fold st TH in HCL. unfold st2 in HIT2. fold st2 in HCL, HIT2.
    rewrite PCc in HCL. cbn [pc_count pc_chunks refill_pc] in HCL. fold n in HCL. fold fl1 in HCL. fold chunks2 in HCL. fold cp in HCL.
    destruct HCL as (j0 & j1 & j2 & j3 & QC1 & QC2 & QC3 & QC4 & QSTb & CHUNK & SHK & TSTb & UNWb & CC & CR & CPS & ABlo & ABhi & INI).
    assert (ABE : AB = sb + c * 2^32 + cp * 16) by (unfold AB; rewrite compact_to_addr_eq, region_beg_eq; reflexivity).
    rewrite <- ABE in CHUNK, SHK, ABlo, ABhi. change (a_sb sR) with sb in ABlo, ABhi. unfold kSpaceSize in ABhi.
    (* [comment removed for export] *)
    assert (ABA : AB mod 64 = 0).
    { assert (WF2a : WF st2) by exact (WF_refill st c WFs HC MISS ROOM).
      assert (TK0a : forall l : list Z, n = zlen l -> l = hd 0 l :: tl l).
      { intros [|y l] H; [exfalso; unfold zlen in H; cbn in H; clear - H NR; try acb; lia| reflexivity]. }
      pose proof (TK0a chunks2 CC) as TKa. clear TK0a. change (hd 0 chunks2) with cp in TKa.
      assert (CV2a : carved st2 c AB).
      { apply carved_cache; [exact WF2a| unfold kNumClasses; clear - HC; try acb; lia|]. unfold st2. rewrite PCc. change (pc_chunks (refill_pc st c)) with chunks2. rewrite TKa. left. reflexivity. }
      pose proof CV2a as (_ & _ & _ & CVm2 & _). rewrite region_beg_eq in CVm2. change (as_space_beg st2) with sb in CVm2. fold csz in CVm2. rewrite ECSZ in CVm2.
      destruct BND as (_ & _ & _ & _ & _ & SB64 & _). clear - CVm2 SB64 HC. Z.div_mod_to_equations. nia. }
    (* [comment removed for export] *)
    assert (GD : (TH + 4096 <= d_nb d \/ d_nb d + 1048576 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 1048576 <= TH)
                 /\ (sb + 137438953472 + 4096 <= d_nb d \/ d_nb d + 1048576 <= sb) /\ (sb + 137438953472 + 4096 <= d_sb d \/ d_sb d + 1048576 <= sb)).
    { unfold disj, kPageSize, kSpaceSize in G1, G2, G3, G4. clear - G1 G2 G3 G4; try acb. unfold TH, sb. lia. }
    assert (DAV : depot_avoid (rf_W lo (bv_unsigned sp + -2368) (CA + PCLASS_SIZE * c) (sb + kSpaceSize + REGIONINFO_SIZE * c) (FA s c) (RB s c) TH CA nf mfa mu mfa' mu') d).
    { pose proof GD as (GD1 & GD2 & GD3 & GD4). unfold depot_avoid, avoids, rf_W, PCLASS_SIZE, REGIONINFO_SIZE, kSpaceSize.
      bands_as (BT & _ & _ & BN & BS).
      split; [| split; [| split]].
      - do 13 (apply Forall_cons; [cbn [fst snd]; clear - BB2 SHB BT; try acb; (first [clear - BB2 BT SHB; lia | lia])|]). apply icW_avoids. clear - BND BT; try acb; lia.
      - do 13 (apply Forall_cons; [cbn [fst snd]; clear - BB2 SHB BT; try acb; lia|]). apply icW_avoids. clear - BND BT; try acb; lia.
      - do 13 (apply Forall_cons; [cbn [fst snd]; clear - BB2 SHB GD1 GD3 BN; try acb; (first [clear - BB2 ACEILB GD1 GD3 SHB BN; lia | lia])|]). apply icW_avoids. clear - BND GD1; try acb; lia.
      - do 13 (apply Forall_cons; [cbn [fst snd]; clear - BB2 SHB GD2 GD4 BS; try acb; (first [clear - BB2 ACEILB GD2 GD4 SHB BS; lia | lia])|]). apply icW_avoids. clear - BND GD2; try acb; lia. }
    pose proof (DEPOT_transport asegs d m1 m2 _ DEP1 MU2 WM2 DAV) as DEP2.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (ZR : forall a, (65536 <= a < 12599296 \/ TH <= a < TH + 288 \/ CTX <= a < CTX + 160 \/ bv_unsigned sp + -2368 <= a) ->
                 outside (rf_W lo (bv_unsigned sp + -2368) (CA + PCLASS_SIZE * c) (sb + kSpaceSize + REGIONINFO_SIZE * c) (FA s c) (RB s c) TH CA nf mfa mu mfa' mu') a).
    { intros a Ha. unfold rf_W, PCLASS_SIZE, REGIONINFO_SIZE, kSpaceSize. cbn [outside]. bands_as (BT & BC & _).
      (* [comment removed for export] *)
      destruct BDJ as (BDJa & BDJb & BDJc). destruct Ha as [Ha|[Ha|[Ha|Ha]]].
      - clear BDJa BDJb BDJc BDJ2 BC. destruct BT as [BT|[BT|BT]]; repeat lazymatch goal with
        | |- outside (icW _) _ => apply outside_icW_far; clear - Ha BND HI BT; try acb; lia
        | |- _ /\ _ => split; [clear - Ha BB2 SHB HI BT; try acb; (first [clear - Ha BB2 BT SHB; lia | lia])|]
        end.
      - clear BDJb BDJc BDJ2 BC. repeat lazymatch goal with
        | |- outside (icW _) _ => apply outside_icW_far; clear - Ha BND HI BT; try acb; lia
        | |- _ /\ _ => split; [clear - Ha BB2 SHB HI BT BDJa; try acb; (first [clear - Ha BB2 BDJa ACEILB BT SHB; lia | lia])|]
        end.
      - clear BDJa BDJ2 BT. repeat lazymatch goal with
        | |- outside (icW _) _ => apply outside_icW_far; clear - Ha BND HI BDJb; try acb; lia
        | |- _ /\ _ => split; [clear - Ha BB2 SHB HI BC BDJb BDJc; try acb; (first [clear - BB2 Ha ACEILB BDJb BDJc SHB BC; lia | lia])|]
        end.
      - clear BDJa BDJb BDJc BDJ2 BT BC. repeat lazymatch goal with
        | |- outside (icW _) _ => apply outside_icW_far; clear - Ha BND HI; try acb; lia
        | |- _ /\ _ => split; [clear - Ha BB2 SHB HI; try acb; lia|]
        end. }
    pose proof (munch_agree _ _ _ MU2) as AG2.
    assert (PW2 : rw_cells asegs m2 MP [C8 pjunk]).
    { eapply (rw_cells_transport_pt _ _ _ AG2 WM2); [exact PW1|]. change (Z.of_nat (cells_size [C8 pjunk])) with 8. intros xa Hxa.
      pose proof (MPDJr xa Hxa) as D. unfold Wr in D. cbn [outside] in D. destruct D as (Dlo & _ & D).
      replace (CA + PCLASS_SIZE * c) with P by (unfold PCLASS_SIZE; clear - BND; try acb; lia).
      replace (sb + kSpaceSize + REGIONINFO_SIZE * c) with RI by (unfold kSpaceSize, REGIONINFO_SIZE; clear - BND; try acb; lia).
      revert D. unfold rf_W. cbn [outside]. clear - Dlo HI. intros D. split; [lia| exact (proj2 D)]. }
    assert (AEN2 : AENV tp ATSD CTX TH sb (bv_unsigned sp + -2144) T rest m2).
    { eapply (aenv_transport_pt _ tp ATSD CTX TH sb _ T rest m1 m2 AEN1 AG2 WM2).
      - intros a Ha. apply ZR. left. unfold AIMG_LO, AIMG_TOP in Ha. clear - Ha; try acb. lia.
      - intros a Ha. apply ZR. clear - Ha; try acb. lia.
      - intros a Ha. apply ZR. clear - Ha; try acb. lia.
      - intros a Ha. apply ZR. clear - Ha; try acb. lia.
      - rewrite TP. unfold wz, ATP, AIMG_TOP. rewrite unsigned_lit by (clear; lia). clear; lia.
      - unfold ATSD, AIMG_TOP. clear; lia. }
    assert (FRC2 : rw_cells asegs m2 (bv_unsigned sp + -2368) [C8 (wz rz); C8 (wz neededA); C8 (wz 64); C8 (wz size); C8 (wz 1); C8 (wz 1667228)]) by (trp rw_cells_transport_pt AG2 WM2 FRC1 ZR BND).
    assert (AFR2 : aframeAl (Z_to_bv 64 (bv_unsigned sp + -2192)) (wz 1669828) (wz MP) (wz 64) (wz 64) (wz 63) (wz 1833880) (wz 1) (Z_to_bv 64 (bv_unsigned sp + -2144))
                          (Z_to_bv 64 (bv_unsigned sp + -97)) s8 s9 s10 s11 m2 j8).
    { unfold aframeAl in AFR1 |- *. rewrite unsigned_lit in AFR1 |- * by (clear - SPR HI BND; try acb; lia). trp rw_cells_transport_pt AG2 WM2 AFR1 ZR BND. }
    assert (FRA2 : rw_cells asegs m2 (bv_unsigned sp + -2192) [C8 (wz 1833880); C8 (wz MP); C8 (wz 64); C8 (wz size); C8 sp; C8 (wz 1833996)]) by (trp rw_cells_transport_pt AG2 WM2 FRA1 ZR BND).
    assert (FRB2 : rw_cells asegs m2 (bv_unsigned sp + -88) [C8 sp]) by (trp rw_cells_transport_pt AG2 WM2 FRB1 ZR BND).
    assert (FRM2 : rw_cells asegs m2 (bv_unsigned sp + -80) [CB 8 jk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (trp rw_cells_transport_pt AG2 WM2 FRM1 ZR BND).
    (* [comment removed for export] *)
    unfold wz in VIS2. rewrite (ret_pc_even 1685772) in VIS2 by (clear; lia).
    eapply (evt_sreach_lazy_at asegs L2 S2 (a_Zr s) _ msF2 _ mo2 Q OK2 VIS2).
    { eapply (memalign_from_refill ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m2 lo size d ATSD CTX TH (a_top s) (a_bot s) T rest
                sb n (max_count c) chunks2 j0 j1 j2 j3 MP pjunk rz neededA c csz csz8 (Z.min size 4096) CA P cp AB U nT id).
      - constructor. repeat split; try reflexivity. { symmetry; exact ECA. } exact ABE.
      - exact MPR.
      - exact MPDJt.
      - exact LO.
      - clear - HI; try acb; lia.
      - constructor. exact SPA.
      - constructor. exact SPT.
      - exact SZA.
      - constructor. rewrite TP. unfold wz, ATP, AIMG_TOP. rewrite unsigned_lit by (clear; lia). clear; lia.
      - constructor. unfold ATSD, AIMG_TOP. unfold kPageSize in T2. clear - BND T2 X2; try acb.
        repeat match goal with |- _ /\ _ => split end; first [assumption | lia | Z.div_mod_to_equations; lia].
      - constructor. unfold kSpaceSize. clear - BDJ; try acb. lia.
      - constructor. unfold kSpaceSize. clear - GD G5 G6 G10 G12 BND; try acb. unfold disj in *. unfold CTX in *.
        repeat match goal with |- _ /\ _ => split end; first [assumption | (first [clear - GD; lia | lia])].
      - constructor. unfold AHI_LO, kSpaceSize. acb. clear - BND; try acb. lia.
      - exact CC.
      - exact CR.
      - exact CPS.
      - constructor. split; [exact ABlo| exact ABhi].
      - constructor. exact ABA.
      - constructor. rewrite ERZ. reflexivity.
      - constructor. clear - BND; try acb. lia.
      - exact DCAP.
      - clear - BND; try acb. lia.
      - exact NRT.
      - exact LR.
      - exact TRNG.
      - exact AEN2.
      - exact MI2.
      - exact ST2.
      - exact FRC2.
      - exact AFR2.
      - exact FRA2.
      - exact FRB2.
      - exact FRM2.
      - exact QC1.
      - exact QC2.
      - exact QC3.
      - exact QC4.
      - exact QSTb.
      - exact CHUNK.
      - exact SHK.
      - exact TSTb.
      - exact UNWb.
      - exact DEP2.
      - exact PW2. }
    cbv beta. intros msF3 mo3 OK3 SBM3 _ PO3.
    destruct PO3 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & j0' & j1' & j2' & j3' & b1 & m3 & m4 & VIS3 & MU3 & WM3 & MI3 & ST3 &
                    QC1' & QC3' & QC4' & QST' & HDR & B1 & LEFT & FILL & SLACK & SHA & TST' & UNW' & DEP' & UA & MU4 & WM4 & MI4 & PW4 & ST4 & EQM).
    (* [comment removed for export] *)
    assert (HR2 : ARHEAP sR LB m2) by (destruct HR as (_ & ND & EQ); split; [exact R2| split; [exact ND| exact EQ]]).
    assert (DPL2 : depot_placed sR d) by exact DPL.
    pose proof (arheap_after ra sp s0 m2 sR LB d lo size CH HR2 DPL2 LO ltac:(hci; clear - HI; try acb; lia) SZ HIT2 m3 j0' j1' j2' j3' b1) as AH.
    pose proof (new_block ra sp s0 m2 sR LB d lo size CH HR2 DPL2 LO ltac:(hci; clear - HI; try acb; lia) SZ HIT2 DCAP m3) as NB.
    cbn [a_st a_thr a_ctx a_fsb a_L a_S a_Zr a_AL a_top a_bot] in AH, NB. fold st TH rz needed in AH, NB. fold c in AH, NB. fold st2 csz in AH, NB. fold csz8 in AH.
    rewrite PCc in AH, NB. cbn [pc_count pc_chunks refill_pc] in AH, NB. fold n fl1 in AH, NB. fold chunks2 in AH, NB. fold cp in AH, NB. fold AB in AH, NB. fold U in AH, NB.
    specialize (AH MU3 WM3 QC1' QC3' QC4' QST' HDR B1 LEFT FILL SLACK SHA TST' UNW').
    specialize (NB FILL SLACK SHA).
    pose proof RQ as (RQ1 & RQ2 & RQ3 & RQ4 & RQ5 & RQ6 & RQ7 & RQ8). rewrite RQ4 in AH. fold ch in AH. fold st3 in AH.
    apply K. unfold memalign_cold_gpost.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m3, m4.
    split; [exact OK3|]. split; [exact VIS3|]. split; [exact AH|].
    split.
    { (* [comment removed for export] *)
      intros x Hx. cbn [a_S] in Hx. unfold S2 in Hx. rewrite !in_rangesb_app in Hx.
      apply Bool.orb_true_iff in Hx. destruct Hx as [Hx|Hx]; [| apply Bool.orb_true_iff in Hx; destruct Hx as [Hx|Hx]].
      - apply in_rangesb_if in Hx.
        apply in_window1 in Hx; [| clear - SHB; try acb; lia| clear - BR2; try acb; Z.div_mod_to_equations; lia| clear - SHB; try acb; lia].
        apply (poisoned_visible m2 m3 _ _ _ x POIf WM3). rewrite Z2Nat.id by (clear - BR2; try acb; Z.div_mod_to_equations; lia). exact Hx.
      - apply in_rangesb_if in Hx.
        apply in_window1 in Hx; [| clear - SHB; try acb; lia| clear - BR2; try acb; Z.div_mod_to_equations; lia| clear - SHB; try acb; lia].
        apply (poisoned_visible m2 m3 _ _ _ x POIu WM3). rewrite Z2Nat.id by (clear - BR2; try acb; Z.div_mod_to_equations; lia). exact Hx.
      - apply WM3, WM02. exact (AWV x Hx). }
    split.
    { (* [comment removed for export] *)
      pose proof (munch_agree _ _ _ MU3) as AG3.
      assert (ZT : forall a, (65536 <= a < 7849928 \/ 7849956 <= a < 7915480 \/ 12109808 <= a < 12599296) -> outside Wt a).   (* [comment removed for export] *)
      { intros a Ha. unfold Wt, depot_W. cbn [outside app]. bands_as (BT & _). clear - Ha BND ABlo SHB CSZ BT; try acb. unfold sb in *.
        assert (0x2008fff7000 <= sh AB) by (unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; (first [clear - H0 H ABlo BND; lia | lia])).
        destruct Ha as [Ha|[Ha|Ha]]; (repeat split; try exact I; (first [clear - Ha BND BT ABlo H; lia | lia])). }   (* [comment removed for export] *)
      destruct FX2 as (FXa & FXb & [g FXc] & FXd & [bb FXe]). unfold flagsx_rep, ALIBCPGSZ, AGOT_SSP, ASSPGUARD, ACFLAGS in *.
      split; [trp rw_cells_transport_pt AG3 WM3 FXa ZT BND|]. split; [trp rw_cells_transport_pt AG3 WM3 FXb ZT BND|].
      split; [exists g; trp rw_cells_transport_pt AG3 WM3 FXc ZT BND|]. split; [trp rw_cells_transport_pt AG3 WM3 FXd ZT BND|].
      exists bb; trp rw_cells_transport_pt AG3 WM3 FXe ZT BND. }
    split; [exact (amodelx_hit sR mo3 c n (tl chunks2) ch (AMODELX_mat sR mo2 mo3 AMX2 SBM3))|].
    split; [exact (nonvm_same_trans _ _ _ (nonvm_same_mat _ _ SBM1) (nonvm_same_trans _ _ _ NVS (nonvm_same_mat _ _ SBM3)))|].
    split; [exact DEP'|].
    split; [unfold depot_placed; unfold d'; rewrite d_nb_put, d_sb_put; exact DPL|].
    split.
    { unfold depot_cov. unfold d'. rewrite d_nb_put, d_sb_put. intros x Hx.
      rewrite (same_but_materialized_vmmaps mo2 mo3 SBM3), VMM, (same_but_materialized_vmmaps mo mo1 SBM1). exact (DCOV x Hx). }
    split; [exact MI3|]. split; [exact ST3|].
    split.
    { intros x Hx. unfold mc_W in Hx. apply outside_app in Hx. destruct Hx as [Hx1 Hx2]. rewrite (MU3 x Hx2).
      pose proof (AG02 (bv_unsigned x) Hx1 (bv_unsigned_in_range _ x)) as E. unfold wa in E. rewrite Z_to_bv_bv_unsigned in E. exact E. }
    split; [eapply wmono_trans; [exact WM02| exact WM3]|].
    split. { apply avmx_same; [| reflexivity]. rewrite (same_but_materialized_vmmaps mo2 mo3 SBM3), VMM, (same_but_materialized_vmmaps mo mo1 SBM1). reflexivity. }
    split; [exact (proj1 NB)|]. split; [exact (proj2 NB)|].
    split. 2:{ split; [exact UA|]. split; [exact MU4|]. split; [exact WM4|]. split; [exact MI4|]. split; [exact PW4|]. split; [exact ST4| exact EQM]. }
    (* [comment removed for export] *)
    intros kaddr.
    assert (WF2 : WF st2) by exact (WF_refill st c WFs HC MISS ROOM).
    assert (TK0 : forall l : list Z, n = zlen l -> l = hd 0 l :: tl l).
    { intros [|y l] H; [exfalso; unfold zlen in H; cbn in H; clear - H NR; try acb; lia| reflexivity]. }
    pose proof (TK0 chunks2 CC) as TK. clear TK0. change (hd 0 chunks2) with cp in TK.
    assert (CV2 : carved st2 c AB).
    { apply carved_cache; [exact WF2| unfold kNumClasses; clear - HC; try acb; lia|]. unfold st2. rewrite PCc. change (pc_chunks (refill_pc st c)) with chunks2. rewrite TK. left. reflexivity. }
    pose proof CV2 as (_ & _ & CVa & CVm & CVle). rewrite region_beg_eq in CVa, CVm, CVle. change (as_space_beg st2) with sb in CVa, CVm, CVle. fold csz in CVm, CVle.
    pose proof (rz_size_facts size) as (_ & RZ16 & RZC). fold rz in RZ16, RZC. pose proof SZ as SZ2. unfold kMaxSize in SZ2.
    assert (UM8 : U mod 8 = 0).
    { (* [comment removed for export] *)
      unfold U. destruct BND as (_ & _ & _ & _ & _ & SB64 & _). clear - CVm RZ16 SB64 CS3 CS1.
      assert (Zcsz : csz <> 0) by lia.
      destruct (proj1 (Z.mod_divide _ csz Zcsz) CVm) as [q Hq].
      destruct (proj1 (Z.mod_divide rz 16 ltac:(lia)) RZ16) as [u Hu].
      destruct (proj1 (Z.mod_divide sb 65536 ltac:(lia)) SB64) as [t Ht].
      destruct (proj1 (Z.mod_divide csz 32 ltac:(lia)) CS3) as [k Hk].
      apply Z.mod_divide; [lia|]. exists (4 * q * k + 8192 * t + 536870912 * c + 2 * u). (first [clear - Hk Ht Hu Hq; nia | nia]). }
    assert (IM : forall a, sb <= a -> a + 1 <= aceil -> addr_is_in_mem a = true).
    { intros a Ha Hb. apply in_mem_high. unfold kHighMemBeg, kHighMemEnd. clear - Ha Hb BND; try acb. lia. }
    assert (HM : kHighMemBeg <= as_space_beg st /\ as_space_beg st + kSpaceSize <= kHighMemEnd + 1 /\ as_space_beg st mod 4096 = 0).
    { change (as_space_beg st) with sb. unfold kHighMemBeg, kHighMemEnd, kSpaceSize. clear - BND; try acb. Z.div_mod_to_equations. lia. }
    destruct (am_malloc_cold st c WFs HC MISS ROOM HM size kaddr cp (tl chunks2) ltac:(hci; clear - SZ; try acb; lia)) as (st'' & ev & EQ & SB).
    - unfold size_too_big, kMaxAllowedMalloc. rewrite RQ2, RQ4. change (rq_n (compute_req size)) with size. change (2^40) with 1099511627776.
      replace (1099511627776 <? size) with false by (symmetry; apply Z.ltb_ge; clear - SZ2 RQ6 RQ5; try acb; lia).
      replace (1099511627776 <? needed) with false by (symmetry; apply Z.ltb_ge; clear - SZ2; try acb; lia). reflexivity.
    - rewrite RQ2. exact (proj2 SZ).
    - rewrite RQ2. reflexivity.
    - exact TK.
    - rewrite RQ1. change (compact_to_addr st c cp + rz) with U. rewrite land7_mod8. exact UM8.
    - rewrite RQ1. change (compact_to_addr st c cp + rz) with U. apply IM; unfold U; clear - BND ABlo ABhi RQ6 CS2 RQ5 SZ2; try acb; lia.
    - rewrite RQ1, RQ4. change (compact_to_addr st c cp + rz) with U. rewrite land_lnot7'. apply IM; unfold U; clear - BND ABlo ABhi RQ6 CS2 RQ5 SZ2; try acb; Z.div_mod_to_equations; lia.
    - rewrite RQ1, RQ4. change (compact_to_addr st c cp + rz) with U. rewrite land_lnot7'. apply IM; unfold U; clear - BND ABlo ABhi RQ6 CS2 RQ5 RQ7 SZ2; try acb; Z.div_mod_to_equations; lia.
    - rewrite RQ1. clear - RZC; try acb. clearbody rz. lia.
    - exact RQ3.
    - rewrite RQ1, RQ2, RQ4. clear - RQ6; try acb. lia.
    - exists st'', ev. rewrite RQ1 in EQ. rewrite RQ1, RQ4 in SB. split; [exact EQ| exact SB].
  Qed.
End MemalignColdGlue.

