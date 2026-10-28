(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
     AW_Refill AG_WFHit AG_MallocModel AG_RefillModel AG_ColdModel AG_Malloc AG_Malloc2
     AS_Refill1 AG_Refill1 AG_Refill2 AG_MallocCold AG_Frame SecLazy AG_WriteSet.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma icW_inside : forall CA, Forall (fun iv : ivl => CA + 84 <= fst iv /\ snd iv <= CA + 2496 /\ fst iv <= snd iv) (icW CA).
Proof. intros CA. unfold icW. cbn. repeat (constructor; [cbn; lia|]). constructor. Qed.
End HCW.

Section MallocPrimGlue.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo size : Z) (CH : list (Z * Z)).

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
  Let r := get_region st c.
  Let nf := rg_num_freed r. Let mfa := rg_mapped_free_array r. Let au := rg_allocated_user r. Let mu := rg_mapped_user r. Let fl := rg_free_array r.
  Let n := rf_n c.
  Let mu' := rf_mu' c nf au mu. Let nnew := rf_nnew c nf au mu. Let nf1 := rf_nf1 c nf au mu. Let mfa' := rf_mfa' c nf mfa au mu.
  Let au' := rf_au' c nf au mu. Let fl1 := rf_fl1 c nf au mu fl.
  Let st2 := refilled st c.
  Let chunks2 := firstn (Z.to_nat n) fl1.
  Let cp2 := hd 0 chunks2.
  Let AB2 := compact_to_addr st2 c cp2.
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CH.
  Let T := utrace 0x1bf41c (bv_unsigned sp) (a_top s) (a_bot s) 30 CHI.
  Let nT := Z.of_nat (length T).
  Let d' := d_put d (depot_hash T) nT.
  Let Wr : list ivl := (lo, bv_unsigned sp) :: (TH + 3168, TH + 3169) :: rf_W lo (bv_unsigned sp) P RI (FA s c) (RB s c) TH CA nf mfa mu mfa' mu'.
  Let Wt : list ivl := (lo, bv_unsigned sp) :: (P, P + 4) :: (CA + 2576, CA + 2584) :: (AB2, AB2 + csz) :: (sh AB2, sh AB2 + csz8)
                       :: (TH + 2800, TH + 3169) :: depot_W d.
  Let L2 : list (word * word) :=
    if mfa <? mfa' then maps_subtract (if mu <? mu' then maps_subtract (a_L s) (RB s c + mu) (RB s c + mu') else a_L s) (FA s c + mfa) (FA s c + mfa')
    else (if mu <? mu' then maps_subtract (a_L s) (RB s c + mu) (RB s c + mu') else a_L s).
  Let S2 : list (word * word) :=
    (if mfa <? mfa' then [(wz (sh (FA s c + mfa)), wz ((mfa' - mfa) / 8))] else [])
    ++ (if mu <? mu' then [(wz (sh (RB s c + mu)), wz ((mu' - mu) / 8))] else []) ++ a_S s.
  Let chC := mkChunk AB2 (AB2 + rz) size rz c CAllocated.
  Let sC := mkAst (hit_state st2 c n (tl chunks2) chC) (a_thr s) (a_ctx s) (a_fsb s) L2 S2 (a_Zr s) (a_AL s) (a_top s) (a_bot s).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Let cnt := pc_count (get_pc st c).
  Let chunks := pc_chunks (get_pc st c).
  Let cp1 := hd 0 chunks.
  Let AB1 := compact_to_addr st c cp1.
  Let chH := mkChunk AB1 (AB1 + rz) size rz c CAllocated.
  Let sH := mkAst (hit_state st c cnt (tl chunks) chH) (a_thr s) (a_ctx s) (a_fsb s) (a_L s) (a_S s) (a_Zr s) (a_AL s) (a_top s) (a_bot s).

  Hypothesis HR : ARHEAP s LB m.
  Hypothesis AX : awin_vis s m /\ flagsx_rep m.
  Hypothesis AMX : AMODELX s mo.
  Hypothesis DEP : DEPOT asegs d m.
  Hypothesis DPL : depot_placed s d.
  Hypothesis DFS : disj (a_fsb s) AFS_SIZE (d_nb d) (16 * 65536) /\ disj (a_fsb s) AFS_SIZE (d_sb d) (8 * 131072).
  Hypothesis DCOV : depot_cov d mo.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 2992 <= bv_unsigned sp.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis SZ : 1 <= size /\ needed <= kMaxSize.
  Hypothesis TP : tp = wz ATP.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + 31 <= 131072.
  Hypothesis FCH : goodframe (a_bot s) (bv_unsigned sp) (a_top s) = true -> goodframe (bv_unsigned sp) (bv_unsigned s0) (a_top s) = true ->
                   bv_unsigned sp + 16 <= bv_unsigned s0 /\ frame_chain asegs m (a_top s) (bv_unsigned s0) CH.
  Hypothesis Ha0 : a0 = wz size.
  Hypothesis PROOM : pusage st + COLD_COST <= B_PRIM.      (* [comment removed for export] *)
  Hypothesis ROOM : mu + 2 * kUserMapSize <= kFreeArrayOffset.
  Hypothesis OK : lzok asegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo).
  Hypothesis VISE : restrict (a_L s) (a_S s) msF
    = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1bf354) fc None m (seg_rom asegs).

  (* [comment removed for export] *)
  Definition malloc_prim_gpost (msF' : machine_state) (mo' : Model) : Prop :=
    exists (s' : ast) (U : Z) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
       a_thr s' = a_thr s /\ a_ctx s' = a_ctx s /\ a_fsb s' = a_fsb s /\ a_Zr s' = a_Zr s /\ a_top s' = a_top s /\ a_bot s' = a_bot s
    /\ as_sec (a_st s') = as_sec (a_st s) /\ a_AL s <= a_AL s'     (* [comment removed for export] *)
    /\ lzok asegs (a_L s') (a_S s') (a_Zr s') (mkCfg msF' mo')
    /\ restrict (a_L s') (a_S s') msF'
       = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz U) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ ARHEAP s' ((U, size) :: LB) m' /\ awin_vis s' m' /\ flagsx_rep m' /\ AMODELX s' mo' /\ nonvm_same mo mo'   (* [comment removed for export] *)
    /\ DEPOT asegs d' m' /\ depot_placed s' d' /\ depot_cov d' mo'
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ amframe s LB (bv_unsigned sp) m m' /\ wmono asegs m m'
    /\ acompl s s' d lo (bv_unsigned sp) m m' /\ avmx s s' mo mo'                      (* [comment removed for export] *)
    /\ (exists junk, rw_cells asegs m' U [CB (Z.to_nat size) junk]) /\ addressable m' U size
    /\ (forall kaddr, exists st'' ev, am_malloc_k st size kaddr = Some (U, st'', ev) /\ same_but_shadow st'' (a_st s')).

  Let R : AREP s m. Proof. exact (proj1 HR). Qed.
  Let OKs : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OKs). Qed.
  (* [comment removed for export] *)
  Let TBAND : TH + 4096 <= 65536 \/ (12599296 <= TH /\ TH + 4096 <= 2147446784) \/ 17594333495296 <= TH.
  Proof. pose proof PL as (_ & _ & _ & _ & _ & _ & _ & T2 & _). exact (akobj_lit _ _ T2). Qed.
  Let WFs : WF st. Proof. exact (proj2 OKs). Qed.
  Let HLB : forall b, In b LB -> In b (alb s). Proof. intros b Hb. exact (proj1 (proj2 (proj2 HR) b) Hb). Qed.
  Ltac thr := apply (apriv_thread s OKs LB HLB); [| | |assumption]; cbn [fst snd]; unfold kPageSize.
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
  Let BND : 4096 <= TH /\ TH + 4096 <= aceil /\ TH mod 4096 = 0 /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil
            /\ sb mod 65536 = 0 /\ 12599296 <= CTX /\ CTX + 160 <= aceil /\ 12599296 <= a_pa s /\ a_pa s + 8388608 <= aceil
            /\ 12599296 <= d_nb d /\ d_nb d + 16 * 65536 <= aceil /\ 12599296 <= d_sb d /\ d_sb d + 8 * 131072 <= aceil
            /\ 4096 <= a_top s <= 2^47 /\ 0 <= a_bot s < a_top s /\ aceil <= lo /\ 1 <= c <= 30
            /\ P = TH + 208 + 80 * c /\ CA = TH + 208 /\ RI = sb + 137438953472 + 128 * c /\ RB s c = sb + c * 4294967296 /\ FA s c = RB s c + 3758096384.
  Proof.
    pose proof PL as (Y1 & Y2 & Y3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    pose proof DPL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    assert (E1 : RB s c = sb + c * 4294967296) by (unfold RB, sb, a_sb; rewrite region_beg_eq; reflexivity).
    assert (E2 : FA s c = RB s c + 3758096384) by (unfold FA, RB; rewrite free_array_base_eq; reflexivity).
    pose proof (akobj_env _ _ T2 ltac:(unfold kPageSize; clear; lia)) as T2e. pose proof (aapp_env _ _ P2 ltac:(unfold kPtrArrayReserve; clear; lia)) as P2e.
    pose proof (aapp_env _ _ X2 ltac:(clear; lia)) as X2e. pose proof (aapp_env _ _ G10 ltac:(clear; lia)) as G10e. pose proof (aapp_env _ _ G12 ltac:(clear; lia)) as G12e.
    clear - Y1 Y2 Y3 P1 P2e P3 T1 T2e T3 X1 X2e X3 TCX G10e G11 G12e G13 LO HC E1 E2; try acb. unfold TH, sb, CTX, P, CA, RI, a_ri. unfold a_sb in *.
    acb. unfold AHI_LO, kSpaceSize, kPageSize, kPtrArrayReserve in *. repeat split; (first [clear - T2e T1 Y2 Y3 Y1 X2e P2e G10e G12e TCX LO HC E1; lia | lia]).
  Qed.

  (* [comment removed for export] *)
  Let DEPF : Forall (fun iv : ivl => apriv s LB (bv_unsigned sp) (fst iv) (snd iv)) (depot_W d).
  Proof.
    pose proof DPL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13). destruct DFS as [FN FB].
    assert (SPc : aceil <= bv_unsigned sp) by (clear - LO HI; try acb; lia).
    destruct (apriv_depot_statics s OKs LB HLB (bv_unsigned sp) SPc) as [A1 A2].
    destruct (apriv_depot_blocks s OKs LB HLB (bv_unsigned sp) (d_nb d) (d_sb d) G10 G12 G3 G4 G9 FN FB SPc) as [A3 A4].   (* [comment removed for export] *)
    unfold depot_W. repeat constructor; cbn [fst snd]; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma cold_frame : forall m', munch (mc_W sp s d lo size) m m' -> amframe s LB (bv_unsigned sp) m m'.
  Proof.
    intros m' MU. apply (amframe_of_munch s LB (bv_unsigned sp) _ m m' MU). clear MU.
    assert (SPc : aceil <= bv_unsigned sp) by (clear - LO HI; try acb; lia).
    pose proof (rf_facts st c WFs HC ROOM) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & _).
    fold st r in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11, Q12, Q13. fold nf mfa au mu fl n in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11, Q12, Q13.
    fold mu' nnew nf1 mfa' au' fl1 in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11, Q12, Q13.
    pose proof (WF_region st c WFs ltac:(hci; unfold kNumClasses; clear - HC; try acb; lia)) as RO.
    pose proof (ro_alloc_nonneg _ _ RO) as W1. pose proof (ro_alloc_le _ _ RO) as W2. pose proof (ro_mapped_bound _ _ RO) as W3.
    pose proof (ro_fa_le _ _ RO) as W4. pose proof (ro_fa_bound _ _ RO) as W5. pose proof (ro_numfreed _ _ RO) as W6. pose proof (ro_fa_mod _ _ RO) as W7.
    pose proof (ro_alloc_mod _ _ RO ltac:(hci; clear - CSZ; try acb; unfold csz in CSZ; lia)) as W8. pose proof (ro_mapped_mod _ _ RO) as W9.
    fold st r in W1, W2, W3, W4, W5, W6, W7, W8, W9. fold nf mfa au mu fl in W1, W2, W3, W4, W5, W6, W7, W8, W9. fold csz in W8, Q5, Q9, Q10. unfold zlen in W6.
    unfold kUserMapSize, kFreeArrayOffset, kFreeArraySize, kFreeArrayMapSize in *.
    assert (BR : 0 <= au <= mu /\ mu <= mu' /\ mu' + 262144 <= 3758096384 /\ 0 <= nf /\ 4 * nf <= mfa /\ mfa <= mfa' <= 536870912 /\ 1 <= n <= nf1 /\ au <= au' <= mu' /\ 0 <= nnew)
      by (clear - W1 W2 W3 W4 W5 W6 Q1 Q3 Q6 Q7 Q12 ROOM HC; try acb; split; [lia|]; repeat split; try lia; unfold n, rf_n; pose proof (max_count_facts c ltac:(hci; lia)); Z.div_mod_to_equations; lia).
    assert (ALN : (RB s c + mu) mod 8 = 0 /\ (FA s c + mfa) mod 8 = 0 /\ au mod 16 = 0).
    { (* [comment removed for export] *)
      pose proof CSZ as (C1 & _ & C3 & _).
      destruct BND as (_ & _ & _ & _ & _ & SB64 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ERB & EFA).
      clear - SB64 ERB EFA W7 W8 W9 C1 C3.
      destruct (proj1 (Z.mod_divide sb 65536 ltac:(lia)) SB64) as [t Ht].
      destruct (proj1 (Z.mod_divide mfa 262144 ltac:(lia)) W7) as [f Hf].
      destruct (proj1 (Z.mod_divide mu 262144 ltac:(lia)) W9) as [u Hu].
      assert (Zc : csz <> 0) by lia. destruct (proj1 (Z.mod_divide au csz Zc) W8) as [q Hq].
      destruct (proj1 (Z.mod_divide csz 32 ltac:(lia)) C3) as [k Hk].
      rewrite EFA, ERB.
      split; [|split].
      - apply Z.mod_divide; [lia|]. exists (8192 * t + 536870912 * c + 32768 * u). lia.
      - apply Z.mod_divide; [lia|]. exists (8192 * t + 536870912 * c + 469762048 + 32768 * f). lia.
      - apply Z.mod_divide; [lia|]. exists (2 * q * k). (first [clear - Hk Hq; nia | nia]). }
    change (mc_W sp s d lo size) with (Wr ++ Wt). apply Forall_app. split.
    - (* [comment removed for export] *)
      constructor; [cbn [fst snd]; apply (apriv_stack s OKs LB HLB); exact LO|].
      constructor; [thr; clear - BND; try acb; lia|].
      unfold rf_W.
      constructor; [cbn [fst snd]; apply (apriv_stack s OKs LB HLB); exact LO|].
      constructor; [thr; clear - BND; try acb; lia|].
      constructor; [thr; clear - BND; try acb; lia|].
      do 5 (constructor; [cbn [fst snd]; apply (apriv_rinfo s OKs LB HLB); [| | |assumption]; unfold a_ri, kSpaceSize, kPageSize; clear - BND; try acb; unfold sb in *; (first [clear - BND; lia | lia])|]).
      constructor. { cbn [fst snd]. apply (apriv_region_hi s OKs LB HLB _ c); [unfold kNumClasses; clear - HC; try acb; lia| | | |assumption]; change (rg_allocated_user (get_region (a_st s) c)) with au; unfold kRegionSize; clear - BND BR; try acb; lia. }
      constructor. { cbn [fst snd]. apply (apriv_region_hi s OKs LB HLB _ c); [unfold kNumClasses; clear - HC; try acb; lia| | | |assumption]; change (rg_allocated_user (get_region (a_st s) c)) with au; unfold kRegionSize; clear - BND BR; try acb; lia. }
      constructor. { cbn [fst snd]. replace ((mfa' - mfa) / 8) with ((FA s c + mfa' - (FA s c + mfa)) / 8) by (f_equal; clear; lia).
                     apply (apriv_region_hi_sh s OKs LB HLB _ c); [unfold kNumClasses; clear - HC; try acb; lia| | | | |assumption]; try (change (rg_allocated_user (get_region (a_st s) c)) with au); unfold kRegionSize; clear - BND BR ALN; try acb; (first [clear - BR BND ALN; lia | lia]). }
      constructor. { cbn [fst snd]. replace ((mu' - mu) / 8) with ((RB s c + mu' - (RB s c + mu)) / 8) by (f_equal; clear; lia).
                     apply (apriv_region_hi_sh s OKs LB HLB _ c); [unfold kNumClasses; clear - HC; try acb; lia| | | | |assumption]; try (change (rg_allocated_user (get_region (a_st s) c)) with au); unfold kRegionSize; clear - BND BR ALN; try acb; lia. }
      constructor; [thr; clear - BND; try acb; lia|].
      eapply Forall_impl; [| apply icW_inside]. intros [x y] (I1 & I2 & I3). cbn [fst snd] in I1, I2, I3 |- *. thr; clear - BND I1 I2 I3; try acb; lia.
    - (* [comment removed for export] *)
      assert (HIN : In cp2 fl1).
      { assert (L : length chunks2 = Z.to_nat n) by (unfold chunks2; rewrite length_firstn; unfold zlen in Q2; clear - Q1 Q2 BR; try acb; lia).
        unfold cp2. rewrite <- (firstn_skipn (Z.to_nat n) fl1). fold chunks2. apply in_or_app. left.
        destruct chunks2 as [|x l] eqn:E; [exfalso; cbn in L; clear - L BR; try acb; lia| left; reflexivity]. }
      assert (ABP : apriv s LB (bv_unsigned sp) AB2 (AB2 + csz) /\ apriv s LB (bv_unsigned sp) (sh AB2) (sh AB2 + csz8)).
      { unfold fl1, rf_fl1 in HIN. fold n csz nnew in HIN. apply in_app_or in HIN. destruct HIN as [HIN|HIN].
        - (* [comment removed for export] *) apply in_carve_asc in HIN. destruct HIN as (j & Hj & Ecp).
          assert (EAB : AB2 = RB s c + au + j * csz).
          { unfold AB2. rewrite compact_to_addr_eq. change (region_beg st2 c) with (RB s c). rewrite Ecp.
            replace (au + (0 + j) * csz) with (((au + j * csz) / 16) * 16) by (clear - ALN CSZ Hj; try acb; Z.div_mod_to_equations; nia).
            rewrite shiftr4_mul16. clear - ALN CSZ Hj; try acb. Z.div_mod_to_equations. nia. }
          rewrite Z2Nat.id in Hj by (clear - BR; try acb; lia).
          assert (ABR : RB s c + au <= AB2 /\ AB2 + csz <= RB s c + au' /\ AB2 mod 8 = 0).
          { (* [comment removed for export] *)
            rewrite EAB, Q5. pose proof CSZ as (C1 & _ & C3 & _). pose proof BR as (_ & _ & _ & _ & _ & _ & _ & _ & NN).
            split; [clear - Hj C1; nia|]. split; [clear - Hj C1 NN; nia|].
            destruct BND as (_ & _ & _ & _ & _ & SB64 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ERB & _). destruct ALN as (_ & _ & AU16).
            clear - SB64 ERB C3 AU16 Hj C1. rewrite ERB.
            destruct (proj1 (Z.mod_divide sb 65536 ltac:(lia)) SB64) as [t Ht].
            destruct (proj1 (Z.mod_divide au 16 ltac:(lia)) AU16) as [u Hu].
            destruct (proj1 (Z.mod_divide csz 32 ltac:(lia)) C3) as [k Hk].
            apply Z.mod_divide; [lia|]. exists (8192 * t + 536870912 * c + 2 * u + 4 * j * k). nia. }
          split.
          + apply (apriv_region_hi s OKs LB HLB _ c); [unfold kNumClasses; clear - HC; try acb; lia| | | |assumption]; try (change (rg_allocated_user (get_region (a_st s) c)) with au); unfold kRegionSize; clear - BND BR ABR CSZ; try acb; lia.
          + replace csz8 with ((AB2 + csz - AB2) / 8) by (unfold csz8; f_equal; clear; lia).
            apply (apriv_region_hi_sh s OKs LB HLB _ c); [unfold kNumClasses; clear - HC; try acb; lia| | | | |assumption]; try (change (rg_allocated_user (get_region (a_st s) c)) with au); unfold kRegionSize; clear - BND BR ABR CSZ; try acb; lia.
        - (* [comment removed for export] *)
          split.
          + exact (apriv_freech s OKs LB HLB (bv_unsigned sp) c cp2 ltac:(hci; unfold kNumClasses; clear - HC; try acb; lia) (or_introl HIN) SPc).
          + exact (apriv_freech_sh s OKs LB HLB (bv_unsigned sp) c cp2 ltac:(hci; unfold kNumClasses; clear - HC; try acb; lia) (or_introl HIN) SPc). }
      destruct ABP as [ABP1 ABP2]. unfold Wt.
      constructor; [cbn [fst snd]; apply (apriv_stack s OKs LB HLB); exact LO|].
      constructor; [thr; clear - BND; try acb; lia|].
      constructor; [thr; clear - BND; try acb; lia|].
      constructor; [exact ABP1|]. constructor; [exact ABP2|].
      constructor; [thr; clear - BND; try acb; lia|].
      exact DEPF.
  Qed.

  (* [comment removed for export] *)
  Lemma cold_compl : forall s' m', as_sec (a_st s') = as_sec st -> munch (mc_W sp s d lo size) m m' -> acompl s s' d lo (bv_unsigned sp) m m'.
  Proof.
    intros s' m' ES MU. apply (acompl_of_munchF s s' d lo (bv_unsigned sp) _ m m' MU). clear MU.
    pose proof (rf_facts st c WFs HC ROOM) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & _).
    fold st r in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11, Q12, Q13. fold nf mfa au mu fl n in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11, Q12, Q13.
    fold mu' nnew nf1 mfa' au' fl1 in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11, Q12, Q13.
    pose proof (WF_region st c WFs ltac:(hci; unfold kNumClasses; clear - HC; try acb; lia)) as RO.
    pose proof (ro_alloc_nonneg _ _ RO) as W1. pose proof (ro_alloc_le _ _ RO) as W2. pose proof (ro_mapped_bound _ _ RO) as W3.
    pose proof (ro_fa_le _ _ RO) as W4. pose proof (ro_fa_bound _ _ RO) as W5. pose proof (ro_numfreed _ _ RO) as W6. pose proof (ro_fa_mod _ _ RO) as W7.
    pose proof (ro_alloc_mod _ _ RO ltac:(hci; clear - CSZ; try acb; unfold csz in CSZ; lia)) as W8. pose proof (ro_mapped_mod _ _ RO) as W9. pose proof (ro_fa_elems _ _ RO) as W10.
    fold st r in W1, W2, W3, W4, W5, W6, W7, W8, W9, W10. fold nf mfa au mu fl in W1, W2, W3, W4, W5, W6, W7, W8, W9, W10. fold csz in W8, W10, Q5, Q9, Q10. unfold zlen in W6.
    unfold kUserMapSize, kFreeArrayOffset, kFreeArraySize, kFreeArrayMapSize in *.
    assert (BR : 0 <= au <= mu /\ mu <= mu' /\ mu' + 262144 <= 3758096384 /\ 0 <= nf /\ 4 * nf <= mfa /\ mfa <= mfa' <= 536870912 /\ 1 <= n <= nf1 /\ au <= au' <= mu' /\ 0 <= nnew)
      by (clear - W1 W2 W3 W4 W5 W6 Q1 Q3 Q6 Q7 Q12 ROOM HC; try acb; split; [lia|]; repeat split; try lia; unfold n, rf_n; pose proof (max_count_facts c ltac:(hci; lia)); Z.div_mod_to_equations; lia).
    assert (ALN : (RB s c + mu) mod 8 = 0 /\ (FA s c + mfa) mod 8 = 0 /\ au mod 16 = 0).
    { (* [comment removed for export] *)
      pose proof CSZ as (C1 & _ & C3 & _).
      destruct BND as (_ & _ & _ & _ & _ & SB64 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ERB & EFA).
      clear - SB64 ERB EFA W7 W8 W9 C1 C3.
      destruct (proj1 (Z.mod_divide sb 65536 ltac:(lia)) SB64) as [t Ht].
      destruct (proj1 (Z.mod_divide mfa 262144 ltac:(lia)) W7) as [f Hf].
      destruct (proj1 (Z.mod_divide mu 262144 ltac:(lia)) W9) as [u Hu].
      assert (Zc : csz <> 0) by lia. destruct (proj1 (Z.mod_divide au csz Zc) W8) as [q Hq].
      destruct (proj1 (Z.mod_divide csz 32 ltac:(lia)) C3) as [k Hk].
      rewrite EFA, ERB.
      split; [|split].
      - apply Z.mod_divide; [lia|]. exists (8192 * t + 536870912 * c + 32768 * u). lia.
      - apply Z.mod_divide; [lia|]. exists (8192 * t + 536870912 * c + 469762048 + 32768 * f). lia.
      - apply Z.mod_divide; [lia|]. exists (2 * q * k). (first [clear - Hk Hq; nia | nia]). }
    (* [comment removed for export] *)
    assert (HIN : In cp2 fl1).
    { assert (L : length chunks2 = Z.to_nat n) by (unfold chunks2; rewrite length_firstn; unfold zlen in Q2; clear - Q1 Q2 BR; try acb; lia).
      unfold cp2. rewrite <- (firstn_skipn (Z.to_nat n) fl1). fold chunks2. apply in_or_app. left.
      destruct chunks2 as [|x l] eqn:E; [exfalso; cbn in L; clear - L BR; try acb; lia| left; reflexivity]. }
    assert (ABB : RB s c <= AB2 /\ AB2 + csz <= RB s c + 4294967296).
    { assert (CP : 0 <= cp2 /\ cp2 * 16 + csz <= au' + csz).
      { unfold fl1, rf_fl1 in HIN. fold n csz nnew in HIN. apply in_app_or in HIN. destruct HIN as [HIN|HIN].
        - apply in_carve_asc in HIN. destruct HIN as (j & Hj & ->). rewrite Z2Nat.id in Hj by (clear - BR; try acb; lia).
          unfold kCompactPtrScale. rewrite Z.shiftr_div_pow2 by (clear; lia). change (2 ^ 4) with 16. rewrite Q5.
          clear - Hj BR W1 CSZ; try acb. split; [apply Z.div_pos; nia|]. Z.div_mod_to_equations. (first [clear - H0 H Hj CSZ; nia | nia]).
        - destruct (W10 cp2 HIN) as (A1 & A2 & _). unfold kCompactPtrScale in A2. rewrite Z.shiftl_mul_pow2 in A2 by (clear; lia). change (2 ^ 4) with 16 in A2.
          clear - A1 A2 BR; try acb. lia. }
      unfold AB2. rewrite compact_to_addr_eq. change (region_beg st2 c) with (RB s c). clear - CP BR CSZ; try acb. lia. }
    Ltac awthr := cbn [fst snd]; intros aa Haa; right; left; unfold kPageSize.
    Ltac awsp := cbn [fst snd]; intros aa Haa; right; right; left; unfold kSpaceSize, kPageSize.
    Ltac awsh := cbn [fst snd]; intros aa Haa; right; right; right; left; unfold kSpaceSize, kPageSize, sh, ASHADOW_BASE in *.
    change (mc_W sp s d lo size) with (Wr ++ Wt). apply Forall_app. split.
    - (* [comment removed for export] *)
      constructor; [cbn [fst snd]; intros aa Haa; left; exact Haa|].
      constructor; [awthr; clear - BND Haa; try acb; lia|].
      unfold rf_W.
      constructor; [cbn [fst snd]; intros aa Haa; left; exact Haa|].
      constructor; [awthr; clear - BND Haa; try acb; lia|].
      constructor; [awthr; clear - BND Haa; try acb; lia|].
      do 5 (constructor; [awsp; unfold sb in *; clear - BND Haa; try acb; lia|]).
      constructor; [awsp; unfold sb in *; clear - BND BR Haa; try acb; lia|].
      constructor; [awsp; unfold sb in *; clear - BND BR Haa; try acb; lia|].
      constructor; [awsh; unfold sb in *; clear - BND BR ALN Haa; try acb; Z.div_mod_to_equations; lia|].
      constructor; [awsh; unfold sb in *; clear - BND BR ALN Haa; try acb; Z.div_mod_to_equations; lia|].
      constructor; [awthr; clear - BND Haa; try acb; lia|].
      eapply Forall_impl; [| apply icW_inside]. intros [x y] (I1 & I2 & I3). cbn [fst snd] in I1, I2, I3. awthr; clear - BND I1 I2 I3 Haa; try acb; lia.
    - unfold Wt.
      constructor; [cbn [fst snd]; intros aa Haa; left; exact Haa|].
      constructor; [awthr; clear - BND Haa; try acb; lia|].
      constructor; [awthr; clear - BND Haa; try acb; lia|].
      constructor; [awsp; unfold sb in *; clear - BND ABB CSZ Haa; try acb; lia|].
      constructor; [awsh; unfold sb, csz8 in *; clear - BND ABB CSZ Haa; try acb; Z.div_mod_to_equations; lia|].
      constructor; [awthr; clear - BND Haa; try acb; lia|].
      unfold depot_W. constructor; [cbn [fst snd]; intros aa Haa; do 6 right; left; right; left; clear - Haa; lia|].
      constructor; [cbn [fst snd]; intros aa Haa; do 6 right; left; right; left; clear - Haa; lia|].
      constructor; [cbn [fst snd]; intros aa Haa; do 7 right; left; clear - Haa; lia|].
      constructor; [cbn [fst snd]; intros aa Haa; do 7 right; right; clear - Haa; lia|].
      constructor.
  Qed.


  (* [comment removed for export] *)
  Let Wh : list ivl := (lo, bv_unsigned sp) :: (P, P + 4) :: (CA + 2576, CA + 2584) :: (AB1, AB1 + csz) :: (sh AB1, sh AB1 + csz8)
                       :: (TH + 2800, TH + 3169) :: depot_W d.
  Lemma hit_frame : forall m', cnt <> 0 -> munch Wh m m' -> amframe s LB (bv_unsigned sp) m m'.
  Proof.
    intros m' HIT MU. apply (amframe_of_munch s LB (bv_unsigned sp) _ m m' MU). clear MU.
    assert (SPc : aceil <= bv_unsigned sp) by (clear - LO HI; try acb; lia).
    assert (HIN : In cp1 chunks).
    { pose proof (co_count _ _ (WF_cache st c WFs ltac:(hci; unfold kNumClasses; clear - HC; try acb; lia))) as CC. fold cnt chunks in CC.
      unfold cp1. destruct chunks as [|x l]; [exfalso; apply HIT; rewrite CC; reflexivity| left; reflexivity]. }
    unfold Wh.
    constructor; [cbn [fst snd]; apply (apriv_stack s OKs LB HLB); exact LO|].
    constructor; [thr; clear - BND; try acb; lia|].
    constructor; [thr; clear - BND; try acb; lia|].
    constructor; [exact (apriv_freech s OKs LB HLB (bv_unsigned sp) c cp1 ltac:(hci; unfold kNumClasses; clear - HC; try acb; lia) (or_intror HIN) SPc)|].
    constructor; [exact (apriv_freech_sh s OKs LB HLB (bv_unsigned sp) c cp1 ltac:(hci; unfold kNumClasses; clear - HC; try acb; lia) (or_intror HIN) SPc)|].
    constructor; [thr; clear - BND; try acb; lia|].
    exact DEPF.
  Qed.

  (* [comment removed for export] *)
  Lemma hit_compl : forall s' m', cnt <> 0 -> as_sec (a_st s') = as_sec st -> munch Wh m m' -> acompl s s' d lo (bv_unsigned sp) m m'.
  Proof.
    intros s' m' HIT ES MU. apply (acompl_of_munchF s s' d lo (bv_unsigned sp) _ m m' MU). clear MU.
    assert (HIN : In cp1 chunks).
    { pose proof (co_count _ _ (WF_cache st c WFs ltac:(hci; unfold kNumClasses; clear - HC; try acb; lia))) as CC. fold cnt chunks in CC.
      unfold cp1. destruct chunks as [|x l]; [exfalso; apply HIT; rewrite CC; reflexivity| left; reflexivity]. }
    pose proof (WF_region st c WFs ltac:(hci; unfold kNumClasses; clear - HC; try acb; lia)) as RO.
    pose proof (ro_alloc_le _ _ RO) as W2. pose proof (ro_mapped_bound _ _ RO) as W3. fold st r in W2, W3. fold au mu in W2, W3.
    destruct (co_elems _ _ (WF_cache st c WFs ltac:(hci; unfold kNumClasses; clear - HC; try acb; lia)) cp1 HIN) as (E1 & E2 & _).
    unfold kCompactPtrScale in E2. rewrite Z.shiftl_mul_pow2 in E2 by (clear; lia). change (2 ^ 4) with 16 in E2. fold st r in E2. fold au in E2.
    unfold kUserMapSize, kFreeArrayOffset in W3.
    assert (ABB : RB s c <= AB1 /\ AB1 + csz <= RB s c + 4294967296 /\ AB1 mod 8 = 0).
    { unfold AB1. rewrite compact_to_addr_eq. change (region_beg st c) with (RB s c). pose proof CSZ as (C1 & _).
      split; [clear - E1; lia|]. split; [clear - E1 E2 W2 W3 C1; lia|].
      destruct BND as (_ & _ & _ & _ & _ & SB64 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ERB & _).
      clear - SB64 ERB. rewrite ERB. destruct (proj1 (Z.mod_divide sb 65536 ltac:(lia)) SB64) as [t Ht].
      apply Z.mod_divide; [lia|]. exists (8192 * t + 536870912 * c + 2 * cp1). lia. }
    Ltac awthr1 := cbn [fst snd]; intros aa Haa; right; left; unfold kPageSize.
    Ltac awsp1 := cbn [fst snd]; intros aa Haa; right; right; left; unfold kSpaceSize, kPageSize.
    Ltac awsh1 := cbn [fst snd]; intros aa Haa; right; right; right; left; unfold kSpaceSize, kPageSize, sh, ASHADOW_BASE in *.
    unfold Wh.
    constructor; [cbn [fst snd]; intros aa Haa; left; exact Haa|].
    constructor; [awthr1; clear - BND Haa; try acb; lia|].
    constructor; [awthr1; clear - BND Haa; try acb; lia|].
    constructor; [awsp1; unfold sb in *; clear - BND ABB CSZ Haa; try acb; lia|].
    constructor; [awsh1; unfold sb, csz8 in *; clear - BND ABB CSZ Haa; try acb; Z.div_mod_to_equations; lia|].
    constructor; [awthr1; clear - BND Haa; try acb; lia|].
    unfold depot_W. constructor; [cbn [fst snd]; intros aa Haa; do 6 right; left; right; left; clear - Haa; lia|].
    constructor; [cbn [fst snd]; intros aa Haa; do 6 right; left; right; left; clear - Haa; lia|].
    constructor; [cbn [fst snd]; intros aa Haa; do 7 right; left; clear - Haa; lia|].
    constructor; [cbn [fst snd]; intros aa Haa; do 7 right; right; clear - Haa; lia|].
    constructor.
  Qed.


  (* [comment removed for export] *)
  Lemma flagsx_keep : forall W m', munch W m m' -> wmono asegs m m' ->
    (forall a, (65536 <= a < 7849928 \/ 7849956 <= a < 7915480 \/ 12109808 <= a < 12599296) -> outside W a) -> flagsx_rep m -> flagsx_rep m'.   (* [comment removed for export] *)
  Proof.
    intros W m' MU WM ZT FX. pose proof (munch_agree _ _ _ MU) as AG.
    destruct FX as (FXa & FXb & [g FXc] & FXd & [bb FXe]). unfold flagsx_rep, ALIBCPGSZ, AGOT_SSP, ASSPGUARD, ACFLAGS in *.
    Ltac trq AG WM H ZT := eapply (rw_cells_transport_pt _ _ _ AG WM); [exact H|];
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Z.mul length];
      let Ha := fresh in intros ? Ha; apply ZT; clear - Ha; try acb; lia.
    split; [trq AG WM FXa ZT|]. split; [trq AG WM FXb ZT|]. split; [exists g; trq AG WM FXc ZT|]. split; [trq AG WM FXd ZT|]. exists bb; trq AG WM FXe ZT.
  Qed.

  (* [comment removed for export] *)
  Lemma am_malloc_k_prim_kaddr : forall kaddr, am_malloc_k st size kaddr = am_malloc_k st size 0.
  Proof.
    intros kaddr. destruct RQ as (_ & RQ2 & _). unfold am_malloc_k. rewrite RQ2.
    replace (kMaxSize <? needed) with false by (symmetry; apply Z.ltb_ge; clear - SZ; try acb; lia). reflexivity.
  Qed.

  Theorem malloc_arep_prim :
    (forall msF' mo', malloc_prim_gpost msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF mo).
  Proof.
    intros K. destruct AX as [AWV FXR]. pose proof RQ as (RQ1 & RQ2 & RQ3 & RQ4 & RQ5 & RQ6 & RQ7 & RQ8).
    destruct (Z.eq_dec cnt 0) as [MISS|HIT].
    - (* [comment removed for export] *)
      eapply (malloc_arep_cold ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m msF mo Q s LB d lo size CH
                HR (conj AWV FXR) AMX DEP DPL DCOV MI ST LO HI SPA SPT SZ MISS TP DCAP FCH Ha0 PROOM ROOM OK VISE).
      intros msF' mo' PO.
      destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & OK' & VIS' & HR' & AWV' & FX' & AMX' & NV' & DEP' & DPL' & DCOV'
                      & MI' & ST' & MU' & WM' & AVX' & BLK & ADDR & MODEL).
      apply K. unfold malloc_prim_gpost.
      exists sC, (AB2 + rz), t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [change (a_AL sC) with (a_AL s); clear; lia|].
      split; [exact OK'|]. split; [exact VIS'|]. split; [exact HR'|]. split; [exact AWV'|]. split; [exact FX'|]. split; [exact AMX'|]. split; [exact NV'|].
      split; [exact DEP'|]. split; [exact DPL'|]. split; [exact DCOV'|]. split; [exact MI'|]. split; [exact ST'|].
      split; [exact (cold_frame m' MU')|]. split; [exact WM'|].
      split; [exact (cold_compl sC m' eq_refl MU')|]. split; [exact AVX'|].
      split; [exact BLK|]. split; [exact ADDR|]. exact MODEL.
    - (* [comment removed for export] *)
      eapply (evt_sreach_lazy_at asegs (a_L s) (a_S s) (a_Zr s) _ msF _ mo Q OK VISE).
      { eapply (malloc_arep_hit ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB d lo size CH);
          first [exact HR| exact DEP| exact DPL| exact MI| exact ST| exact LO| clear - HI; try acb; lia| exact SPA| exact SPT| exact SZ| exact HIT| exact TP| exact DCAP| exact FCH| exact Ha0]. }
      cbv beta. intros msF1 mo1 OK1 SBM1 _ PO1.
      destruct PO1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & VIS1 & MU1 & WM1 & MI1 & ST1 & HR1 & DEP1 & BLK & ADDR).
      rewrite RQ4 in HR1. change (munch Wh m m1) in MU1.
      apply K. unfold malloc_prim_gpost.
      exists sH, (AB1 + rz), t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m1.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [change (a_AL sH) with (a_AL s); clear; lia|].
      split; [exact OK1|]. split; [exact VIS1|]. split; [exact HR1|].
      split; [intros x Hx; apply WM1; exact (AWV x Hx)|].
      assert (HIN1 : In cp1 chunks).
      { pose proof (co_count _ _ (WF_cache st c WFs ltac:(hci; unfold kNumClasses; clear - HC; try acb; lia))) as CC. fold cnt chunks in CC.
        unfold cp1. destruct chunks as [|x l]; [exfalso; apply HIT; rewrite CC; reflexivity| left; reflexivity]. }
      pose proof (carved_in_space s OKs c AB1 (carved_cache st c cp1 WFs ltac:(hci; unfold kNumClasses; clear - HC; try acb; lia) HIN1)) as CIS.
      assert (SHB1 : 0x2008fff7000 <= sh AB1) by (clear - CIS BND; try acb; unfold sb in *; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
      split.
      { apply (flagsx_keep _ m1 MU1 WM1); [| exact FXR]. intros a Ha. unfold Wh, depot_W. cbn [outside app]. fold csz in CIS.
        pose proof TBAND as BT. clear - Ha BND CIS CSZ SHB1 BT; try acb. unfold sb in *. repeat split; try exact I; (first [clear - Ha BND BT CIS SHB1; lia | lia]). }
      split; [exact (amodelx_hit s mo1 c cnt (tl chunks) _ (AMODELX_mat s mo mo1 AMX SBM1))|].
      split; [exact (nonvm_same_mat _ _ SBM1)|].
      split; [exact DEP1|].
      split; [unfold depot_placed; unfold d'; rewrite d_nb_put, d_sb_put; exact DPL|].
      split; [unfold depot_cov; unfold d'; rewrite d_nb_put, d_sb_put; intros x Hx; rewrite (same_but_materialized_vmmaps mo mo1 SBM1); exact (DCOV x Hx)|].
      split; [exact MI1|]. split; [exact ST1|].
      split; [exact (hit_frame m1 HIT MU1)|]. split; [exact WM1|].
      split; [exact (hit_compl sH m1 HIT eq_refl MU1)|].
      split; [apply avmx_same; [rewrite (same_but_materialized_vmmaps mo mo1 SBM1); reflexivity| reflexivity]|].
      split; [exact BLK|]. split; [exact ADDR|].
      intros kaddr. rewrite (am_malloc_k_prim_kaddr kaddr).
      destruct (malloc_hit_model ra sp s0 m s LB d lo size CH HR DPL LO ltac:(hci; clear - HI; try acb; lia) SZ HIT) as (st'' & ev & E1 & E2).
      exists st'', ev. rewrite RQ4 in E2. split; [exact E1| exact E2].
  Qed.
End MallocPrimGlue.

