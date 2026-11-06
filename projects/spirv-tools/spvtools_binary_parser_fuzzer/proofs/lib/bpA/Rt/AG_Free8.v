(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require AW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HImage HZBridge HSysStep HSFModel CellsX HArr TacX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AsanAllocModel SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AllocWf AllocKit AllocBudget AllocRep AllocRepFacts AllocRepFacts2 AllocRepX CidBits CidBits2 AsDepotInv AsDepotHash AsDepotPut AsUnwind AW_DepotFrame AW_MallocBase AW_AllocBase AW_LargeAlloc1 AW_InitCache AW_IAInit AW_FreePre AW_Refill AW_Put1 AW_Enqueue1 AW_Enqueue2 AW_Put2 AS_Free1 AS_Free2 AS_Free3 AllocWalkKit AG_MallocModel AG_WFHit AG_Malloc AG_Malloc2 AG_RefillModel AG_ColdModel AS_Refill1 AS_Refill2 AS_Refill4 AG_Refill1 AG_Refill2 AG_Refill3 AG_MallocCold AG_FreeModel AG_WFFree AG_Free1 AG_FreeFacts AG_Free2 AG_Free3 AG_Free4 AG_Free5 AG_Free6 AG_Free7 SecLazy.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_AG_Free8 () := "I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib3bpA2Rt9AllocRepX7AMODELXC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3bpA2Rt8AllocRep3ast00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I69OSSVerify5KrLib3bpA2Rt>AsanAllocModel5chunk00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3bpA2Rt>AsanAllocModel6qcache00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3bpA2Rt>AsanAllocModel6pclass00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep4AREPC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I46Stdlib5Lists4List5NoDup00C46Stdlib5Lists4List2InC69OSSVerify5KrLib3bpA2Rt8AllocRep3albC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffI47Corelib4Init5Logic3and00C47Corelib4Init5Logic5proj1I47Corelib7Numbers7BinNums1Z00C69OSSVerify5KrLib3bpA2Rt8AllocRep6ast_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep8inst_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep9flags_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep:thread_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep7sec_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep6ia_repC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltC69OSSVerify5KrLib3bpA2Rt8AllocRep:region_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep:pclass_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRepAregion_shadow_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep?region_junk_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep4a_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt>AsanAllocModel:chunk_listC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep9chunk_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt>AsanAllocModel5as_tqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt>AsanAllocModel7qc_listC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep;batches_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt>AsanAllocModel5as_gqC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib3bpA2Rt>AsanAllocModel;kNumClassesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep9placed_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt7AllocWf2WFC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C69OSSVerify5KrLib3bpA2Rt8AllocRep4a_ALC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib3bpA2Rt>AsanAllocModel?compact_to_addrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC69OSSVerify5KrLib3bpA2Rt:AS_Refill16rf_au'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt:AS_Refill17rf_mfa'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt:AS_Refill16rf_nf1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt:AS_Refill17rf_nnewC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt:AS_Refill16rf_mu'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt:AS_Refill14rf_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt>AsanAllocModel>rg_mapped_userC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt>AsanAllocModelArg_allocated_userC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt>AsanAllocModelDrg_mapped_free_arrayC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt>AsanAllocModel<rg_num_freedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep4a_riC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive01K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib3bpA2Rt>AsanAllocModel7qb_addrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt>AsanAllocModel4zlenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt>AsanAllocModel7ch_usedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt>AsanAllocModel;ch_user_begC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep4a_sbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep5a_ctxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep5a_thrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib3bpA2Rt>AsanAllocModel;kBatchClassC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3bpA2Rt>AsanAllocModel6qbatch00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib3bpA2Rt>AsanAllocModel@as_internal_initC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF3Lib4TacX2b8C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF3Lib6HCells4cell04C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF3Lib4TacX2wzC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF3Lib6HCells4cell03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF3Lib6HCells4cell02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF3Lib6HCells4cell01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC79OSSVerify5KrLib3bpA2HF3Lib5HStep8rw_cellsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4list02K79OSSVerify5KrLib3bpA2HF3Lib6HCells4cell05C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep5zboolC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatC47Corelib5Lists7ListDef3mapI79OSSVerify5KrLib3bpA2HF3Lib6HCells4cell00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt5ASegs5asegsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep7AIAINITC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep6AFLAGSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep7ACFLAGSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep<ASHBASE_CELLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt5ASegs<ASHADOW_BASEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep;AHIGHMEMENDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep:ACANPOISONC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep7AINITEDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep8ACTXSIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep8ATSDINITC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib3bpA2Rt8AllocRep;AALLOCFLAGSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep6AHOOKSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep6ADYINGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep;AREALMEMSETC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep7AMEMSETC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep7AGOT_LOC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep9AGOT_VALSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep7APAGESZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep8ASECNAMEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep9APRIMNAMEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep8ATLSSLOTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep4ATSDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep8ALSANDISC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep5AGOT2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt9AW_IAInit8ia_afterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt9AW_IAInit;ia_pristineC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

Ltac trp lem AG WM H Z B :=
  eapply (lem _ _ _ AG WM); [exact H|];
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Z.mul length];
  let Ha := fresh in intros ? Ha; apply Z; clear - Ha B; try acb; lia.

Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma amodelx_free : forall s mo ch tq' cache',
  AMODELX s mo -> AMODELX (free_s' s ch tq' cache' (a_L s) (a_S s) (a_AL s)) mo.
Proof.
ltac2:(KReplay.run1 (kr_t_AG_Free8 ()) ["HCW"] "h01Ah16cache'h22chh32moh41sh53tq'p;1p;3g0000j11Tg000Pj30Tg001Mg002Gg003=g004?g005B#1p,5HCEILf4f330f0W0W1W5W2W3W4o"). Qed.

Section FreeRefillGlue.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo : Z) (CH : list (Z * Z)) (ch : chunk) (bs sbs : list byte).

  Let st := a_st s.
  Let TH := a_thr s.
  Let CTX := a_ctx s.
  Let sb := a_sb s.
  Let U := ch_user_beg ch.
  Let size := ch_used ch.
  Let tq := as_tq st.
  Let l := qc_list tq.
  Let k := zlen l.
  Let lb := last l (mkQB 0 0 0 []).
  Let LA := qb_addr lb.

  Let c := kBatchClass.
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
  Let cp := hd 0 chunks2.
  Let B := compact_to_addr st2 c cp.

  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CH.
  Let T := utrace 0xba604 (bv_unsigned sp) (a_top s) (a_bot s) 30 CHI.
  Let nT := Z.of_nat (length T).
  Let d' := d_put d (depot_hash T) nT.

  Let L2 : list (word * word) :=
    if mfa <? mfa' then maps_subtract (if mu <? mu' then maps_subtract (a_L s) (RB s c + mu) (RB s c + mu') else a_L s) (FA s c + mfa) (FA s c + mfa')
    else (if mu <? mu' then maps_subtract (a_L s) (RB s c + mu) (RB s c + mu') else a_L s).
  Let S2 : list (word * word) :=
    (if mfa <? mfa' then [(wz (sh (FA s c + mfa)), wz ((mfa' - mfa) / 8))] else [])
    ++ (if mu <? mu' then [(wz (sh (RB s c + mu)), wz ((mu' - mu) / 8))] else []) ++ a_S s.
  Let AL' := a_AL s.
  Let sR := mkAst st2 (a_thr s) (a_ctx s) (a_fsb s) L2 S2 (a_Zr s) AL' (a_top s) (a_bot s).
  Let tq' := tq_new tq B (ch_chunk_beg ch) size.
  Let cache' := upd_nth (as_cache st2) (zidx c) (mkPC (n - 1) (tl chunks2)).
  Let sF := free_s' sR ch tq' cache' L2 S2 AL'.

  Let Wh : list ivl := free_head_W lo (bv_unsigned sp) TH U size d.
  Let WR : list ivl := (lo, bv_unsigned sp) :: (TH + 3168, TH + 3169) :: rf_W lo (bv_unsigned sp) P RI (FA s c) (RB s c) TH CA nf mfa mu mfa' mu'.
  Let Wn : list ivl := enq_new_W lo (bv_unsigned sp) TH B LA.
  Definition fr_W : list ivl := WR ++ (Wh ++ Wn).

  Hypothesis HR : ARHEAP s LB m.
  Hypothesis CHIN : In ch (chunk_list st).
  Hypothesis ALLOC : ch_state ch = CAllocated.
  Hypothesis UHI : aapp (ch_user_beg ch - 16) (16 + round_up (ch_used ch) 8).
  Hypothesis AX : awin_vis s m /\ flagsx_rep m.
  Hypothesis AMX : AMODELX s mo.
  Hypothesis DEP : DEPOT asegs d m.
  Hypothesis DPL : depot_placed s d.
  Hypothesis DCOV : depot_cov d mo.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 2944 <= bv_unsigned sp.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis TP : tp = wz ATP.
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 32768 <= lo.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + 31 <= 32768.
  Hypothesis FCH : goodframe (a_bot s) (bv_unsigned sp) (a_top s) = true -> goodframe (bv_unsigned sp) (bv_unsigned s0) (a_top s) = true ->
                   bv_unsigned sp + 16 <= bv_unsigned s0 /\ frame_chain asegs m (a_top s) (bv_unsigned s0) CH.
  Hypothesis Ha0 : a0 = wz U.
  Hypothesis BLK : rw_cells asegs m U [CB (Z.to_nat size) bs].
  Hypothesis SHB : SHAD m U sbs /\ Z.of_nat (length sbs) = nsh size.

  Hypothesis QSZ : size <= kQuarantineMaxSize /\ size < 2^32.
  Hypothesis NN : need_new tq = true.
  Hypothesis MISS : pc_count (get_pc st c) = 0.
  Hypothesis NOD : qc_bytes tq + size + kBatchSize <= kMaxCacheSize.

  Hypothesis PROOM : pusage st + COLD_COST <= B_PRIM.
  Hypothesis ROOM : mu + 2 * kUserMapSize <= kFreeArrayOffset.

  Hypothesis OK : lzok asegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo).
  Hypothesis VISE : restrict (a_L s) (a_S s) msF
    = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xba4cc) fc None m (seg_rom asegs).

  Definition free_refill_gpost (msF' : machine_state) (mo' : Model) : Prop :=
    exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
       lzok asegs (a_L sF) (a_S sF) (a_Zr sF) (mkCfg msF' mo')
    /\ restrict (a_L sF) (a_S sF) msF'
       = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ ARHEAP sF (lb_remove U LB) m' /\ awin_vis sF m' /\ flagsx_rep m' /\ AMODELX sF mo'
    /\ DEPOT asegs d' m' /\ depot_placed sF d' /\ depot_cov d' mo'
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ munch fr_W m m' /\ wmono asegs m m'
    /\ (exists st'' ev, am_free_full st U = Some (st'', ev) /\ same_but_shadow st'' (a_st sF)).

  Let R : AREP s m. Proof. exact (proj1 HR). Qed.
  Let OKs : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OKs). Qed.
  Let WFs : WF st. Proof. exact (proj2 OKs). Qed.
  Let HC : 1 <= c <= 30. Proof. unfold c, kBatchClass. lia. Qed.

  Let FLG4 : rw_cells asegs m AIAINIT [C1 (b8 (if as_internal_init st then 1 else 0)); C1 (b8 0); C2 (wz 0)].
  Proof.
    pose proof R as RR. destruct RR as (_ & _ & FL & _).
    destruct FL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F16 & _). exact F16.
  Qed.
  Let IAX : if as_internal_init st then ia_after m else ia_pristine m.
  Proof. pose proof R as RR. destruct RR as (_ & _ & _ & _ & _ & IA & _). unfold ia_rep in IA. unfold ia_after, ia_pristine. exact IA. Qed.
  Let PURE := free_pure s m ch R CHIN UHI.
  Let RPURE := refill_pure s m c R HC MISS.
  Let RF := rf_facts st c WFs HC ROOM.
  Let PCc := rfd_pc_c st c WFs HC ROOM.
  Ltac zlets := repeat match goal with H := _ |- _ => subst H end.

End FreeRefillGlue.
End HCW.
