(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel BReach BazyRestrict BazyLedger BazySR BazyNodes.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocBudget BllocRep BllocRepFacts BllocRepFacts2 BllocRepX BidBits BidBits2 BsDepotInv BsDepotHash BsDepotPut BsUnwind BW_DepotFrame BW_MallocBase BW_AllocBase BW_LargeAlloc1 BW_InitCache BW_IAInit BW_FreePre BW_Refill BW_Put1 BW_Enqueue1 BW_Enqueue2 BW_Put2 BS_Free1 BS_Free2 BS_Free3 BllocWalkKit BG_MallocModel BG_WFHit BG_Malloc BG_Malloc2 BG_RefillModel BG_ColdModel BS_Refill1 BS_Refill2 BS_Refill4 BG_Refill1 BG_Refill2 BG_Refill3 BG_MallocCold BG_FreeModel BG_WFFree BG_Free1 BG_FreeFacts BG_Free2 BG_Free3 BG_Free4 BG_Free5 BG_Free6 BG_Free7 BecLazy.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BG_Free8 () := "I47Corelib4Init9Datatypes4list00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BllocRepX7AMODELXI6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep3ast00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I6ARocqVerifyHarness?AgentSubmission3bpB2Rt>BothAllocModel5chunk00I6ARocqVerifyHarness?AgentSubmission3bpB2Rt>BothAllocModel6qcache00I6ARocqVerifyHarness?AgentSubmission3bpB2Rt>BothAllocModel6pclass00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep4AREPI47Corelib4Init9Datatypes4prod00I46Stdlib5Lists4List5NoDup00C46Stdlib5Lists4List2InC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep3albC47Corelib4Init5Logic3iffI47Corelib4Init5Logic3and00C47Corelib4Init5Logic5proj1I47Corelib7Numbers7BinNums1Z00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep6ast_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep8inst_repC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep9flags_repC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep:thread_repC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep7sec_repC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep6ia_repC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep:region_repC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep:pclass_repC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRepAregion_shadow_repC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep?region_junk_repC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep4a_stC6ARocqVerifyHarness?AgentSubmission3bpB2Rt>BothAllocModel:chunk_listC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep9chunk_repC6ARocqVerifyHarness?AgentSubmission3bpB2Rt>BothAllocModel5as_tqC6ARocqVerifyHarness?AgentSubmission3bpB2Rt>BothAllocModel7qc_listC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep;batches_repC6ARocqVerifyHarness?AgentSubmission3bpB2Rt>BothAllocModel5as_gqK47Corelib7Numbers7BinNums1Z01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt>BothAllocModel;kNumClassesC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep9placed_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BllocWf2WFC47Corelib4Init5Logic5proj2C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep4a_ALC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC6ARocqVerifyHarness?AgentSubmission3bpB2Rt>BothAllocModel?compact_to_addrC46Stdlib5Lists4List2hdC6ARocqVerifyHarness?AgentSubmission3bpB2Rt:BS_Refill16rf_au'C6ARocqVerifyHarness?AgentSubmission3bpB2Rt:BS_Refill17rf_mfa'C6ARocqVerifyHarness?AgentSubmission3bpB2Rt:BS_Refill16rf_nf1C6ARocqVerifyHarness?AgentSubmission3bpB2Rt:BS_Refill17rf_nnewC6ARocqVerifyHarness?AgentSubmission3bpB2Rt:BS_Refill16rf_mu'C6ARocqVerifyHarness?AgentSubmission3bpB2Rt:BS_Refill14rf_nC6ARocqVerifyHarness?AgentSubmission3bpB2Rt>BothAllocModel>rg_mapped_userC6ARocqVerifyHarness?AgentSubmission3bpB2Rt>BothAllocModelArg_allocated_userC6ARocqVerifyHarness?AgentSubmission3bpB2Rt>BothAllocModelDrg_mapped_free_arrayC6ARocqVerifyHarness?AgentSubmission3bpB2Rt>BothAllocModel<rg_num_freedC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep4a_riK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive01K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt>BothAllocModel7qb_addrC6ARocqVerifyHarness?AgentSubmission3bpB2Rt>BothAllocModel4zlenC6ARocqVerifyHarness?AgentSubmission3bpB2Rt>BothAllocModel7ch_usedC6ARocqVerifyHarness?AgentSubmission3bpB2Rt>BothAllocModel;ch_user_begC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep4a_sbC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep5a_ctxC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep5a_thrC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03C6ARocqVerifyHarness?AgentSubmission3bpB2Rt>BothAllocModel;kBatchClassI6ARocqVerifyHarness?AgentSubmission3bpB2Rt>BothAllocModel6qbatch00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt>BothAllocModel@as_internal_initC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BacX2b8K7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell04C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BacX2wzK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell03K7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell02K7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell01C56Stdlib6ZArith6BinInt1Z3subC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BStep8rw_cellsK47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4list02K7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell05C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep5zboolC47Corelib5Lists7ListDef6repeatC47Corelib5Lists7ListDef3mapI7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep7AIAINITC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep6AFLAGSC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep7ACFLAGSC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep<ASHBASE_CELLC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs<ASHADOW_BASEC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep;AHIGHMEMENDC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep:ACANPOISONC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep7AINITEDC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep8ACTXSIZEC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep8ATSDINITK47Corelib4Init9Datatypes3nat01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep;AALLOCFLAGSC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep6AHOOKSC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep6ADYINGC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep;AREALMEMSETC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep7AMEMSETC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep7AGOT_LOC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep9AGOT_VALSC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep7APAGESZC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep8ASECNAMEC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep9APRIMNAMEC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep8ATLSSLOTC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep4ATSDC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep8ALSANDISC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep5AGOT2C6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BW_IAInit8ia_afterC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BW_IAInit;ia_pristine".
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
ltac2:(KReplay.run1 (kr_t_BG_Free8 ()) ["HCW"] "h01Ah16cache'h22chh32moh41sh53tq'p;1p;3g0000j11Tg000Pj30Tg001Mg002Gg003=g004?g005B#1p,5HCEILf4f330f0W0W1W5W2W3W4o"). Qed.

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
  Let T := utrace 0xba24c (bv_unsigned sp) (a_top s) (a_bot s) 30 CHI.
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
    = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xba114) fc None m (seg_rom asegs).

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
