(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel BReach BazyRestrict BazyLedger BazySR BazyNodes.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocBudget BllocRep BllocRepFacts BllocRepFacts2 BllocRepX BidBits BidBits2 BsDepotInv BsDepotHash BsDepotPut BsUnwind BW_DepotFrame BW_MallocBase BW_AllocBase BW_IAInit BW_FreePre BW_Put1 BW_Enqueue1 BW_Enqueue2 BW_Put2 BS_Free1 BS_Free2 BS_Free3 BllocWalkKit BG_MallocModel BG_WFHit BG_Malloc BG_Malloc2 BG_RefillModel BG_Refill1 BG_Refill2 BG_Frame BG_MallocCold BG_MallocTop BG_FreeModel BG_WFFree BG_Free1 BG_FreeFacts BG_Free2 BG_Free3 BG_Free4 BG_Free5 BG_Free6 BG_Free7 BG_Free8 BG_Free9 BecLazy.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition FREE_COST : Z := 0.

Lemma need_new_false_inv : forall t, need_new t = false -> qc_list t <> [] /\ qb_count (last (qc_list t) (mkQB 0 0 0 [])) < kBatchCount.
Proof.
  intros t. unfold need_new. destruct (qc_list t) as [|b q] eqn:E; intros H; [discriminate H|].
  split; [discriminate| apply Z.leb_gt in H; exact H].
Qed.

Lemma flagsx_transport : forall (P : Z -> Prop) ma mb, agree_on P ma mb -> wmono asegs ma mb ->
  (forall a, 65536 <= a < AIMG_TOP -> ~ (AIAINIT <= a < AIAINIT + 4) -> ~ (AIAINST <= a < AIAINST + 0x81030) ->
             ~ (2567960 <= a < 6762288) -> ~ (2502408 <= a < 2502436) -> P a) ->
  flagsx_rep ma -> flagsx_rep mb.
Proof.
  intros P ma mb AG WM ZT FX.
  destruct FX as (FXa & FXb & [g FXc] & FXd & [bb FXe]). unfold flagsx_rep, ALIBCPGSZ, AGOT_SSP, ASSPGUARD, ACFLAGS, AIAINIT, AIAINST, AIMG_TOP in *.
  Ltac trz AG WM H ZT := eapply (rw_cells_transport_pt _ _ _ AG WM); [exact H|];
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Z.mul length];
    let Ha := fresh in intros ? Ha; apply ZT; clear - Ha; lia.
  split; [trz AG WM FXa ZT|]. split; [trz AG WM FXb ZT|]. split; [exists g; trz AG WM FXc ZT|]. split; [trz AG WM FXd ZT|]. exists bb; trz AG WM FXe ZT.
Qed.

Section FreeGlue.
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
  Let lcount := qb_count lb.
  Let c := kBatchClass.
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CH.
  Let T := utrace 0xba24c (bv_unsigned sp) (a_top s) (a_bot s) 30 CHI.
  Let nT := Z.of_nat (length T).
  Let d' := d_put d (depot_hash T) nT.

  Hypothesis HR : ARHEAP s LB m.
  Hypothesis CHIN : In ch (chunk_list st).
  Hypothesis ALLOC : ch_state ch = CAllocated.
  Hypothesis UHI : aapp (ch_user_beg ch - 16) (16 + round_up (ch_used ch) 8).
  Hypothesis AX : awin_vis s m /\ flagsx_rep m.
  Hypothesis AMX : AMODELX s mo.
  Hypothesis DEP : DEPOT asegs d m.
  Hypothesis DPL : depot_placed s d.
  Hypothesis DFS : disj (a_fsb s) AFS_SIZE (d_nb d) (16 * 65536) /\ disj (a_fsb s) AFS_SIZE (d_sb d) (8 * 32768).
  Hypothesis DCOV : depot_cov d mo.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 2944 <= bv_unsigned sp.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis TP : tp = wz ATP.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + 31 <= 32768.
  Hypothesis FCH : goodframe (a_bot s) (bv_unsigned sp) (a_top s) = true -> goodframe (bv_unsigned sp) (bv_unsigned s0) (a_top s) = true ->
                   bv_unsigned sp + 16 <= bv_unsigned s0 /\ frame_chain asegs m (a_top s) (bv_unsigned s0) CH.
  Hypothesis Ha0 : a0 = wz U.

  Hypothesis BLK : rw_cells asegs m U [CB (Z.to_nat size) bs].
  Hypothesis SHB : SHAD m U sbs /\ Z.of_nat (length sbs) = nsh size.

  Hypothesis QSZ : size <= kQuarantineMaxSize.
  Hypothesis NOD : qc_bytes tq + size + kBatchSize <= kMaxCacheSize.

  Hypothesis PROOM : pusage st + COLD_COST <= B_PRIM.
  Hypothesis ROOM : rg_mapped_user (get_region st c) + 2 * kUserMapSize <= kFreeArrayOffset.

  Hypothesis OK : lzok asegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo).
  Hypothesis VISE : restrict (a_L s) (a_S s) msF
    = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xba114) fc None m (seg_rom asegs).

  Definition free_gpost (msF' : machine_state) (mo' : Model) : Prop :=
    exists (s' : ast) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
       a_thr s' = a_thr s /\ a_ctx s' = a_ctx s /\ a_fsb s' = a_fsb s /\ a_Zr s' = a_Zr s /\ a_top s' = a_top s /\ a_bot s' = a_bot s
    /\ as_sec (a_st s') = as_sec (a_st s) /\ a_AL s - FREE_COST <= a_AL s'
    /\ lzok asegs (a_L s') (a_S s') (a_Zr s') (mkCfg msF' mo')
    /\ restrict (a_L s') (a_S s') msF'
       = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ ARHEAP s' (lb_remove U LB) m' /\ awin_vis s' m' /\ flagsx_rep m' /\ AMODELX s' mo'
    /\ DEPOT asegs d' m' /\ depot_placed s' d' /\ depot_cov d' mo'
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ amframe s (lb_remove U LB) (bv_unsigned sp) m m' /\ wmono asegs m m'
    /\ (exists st'' ev, am_free_full st U = Some (st'', ev) /\ same_but_shadow st'' (a_st s')).

  Let R : AREP s m. Proof. exact (proj1 HR). Qed.
  Let OKs : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OKs). Qed.
  Let WFs : WF st. Proof. exact (proj2 OKs). Qed.
  Ltac zlets := repeat match goal with H := _ |- _ => subst H end.
  Let HC24 : 0 <= c < kNumClasses. Proof. unfold c, kBatchClass, kNumClasses. lia. Qed.
  Let QSZ2 : size <= kQuarantineMaxSize /\ size < 2^32.
  Proof. split; [exact QSZ|]. unfold kQuarantineMaxSize in QSZ. clear - QSZ. lia. Qed.
  Let DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 32768 <= lo.
  Proof. pose proof DPL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G10 & G11 & G12 & G13). clear - G11 G13 LO. lia. Qed.

  Let ZHs : forall a, 65536 <= a < AIMG_TOP -> ~ (AIAINIT <= a < AIAINIT + 4) -> ~ (AIAINST <= a < AIAINST + 0x81030) ->
                      ~ (2567960 <= a < 6762288) -> ~ (2502408 <= a < 2502436) -> outside (free_head_W lo (bv_unsigned sp) TH U size d) a.
  Proof. intros a Ha N1 N2 N3 N4. apply (ZH_lo s m d lo (bv_unsigned sp) ch R CHIN UHI DPL LO QSZ2 a); [clear - Ha; lia| assumption| assumption| assumption| assumption]. Qed.

End FreeGlue.
End HCW.
