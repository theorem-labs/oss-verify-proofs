(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AsConst.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocBudget AllocRep AllocRepFacts AllocRepFacts2 AllocRepX CidBits CidBits2
     AsDepotInv AsDepotHash AsUnwind AW_DepotFrame AW_MallocBase AW_AllocBase AW_InitCache AW_Efs AW_Populate AW_IAInit AW_FreePre
     AW_Refill AW_MallocHead AW_MallocTail AW_ReallocPre AW_ReallocHead AW_ReallocTail AW_ReallocMid F_memcpy
     AG_WFHit AG_MallocModel AG_RefillModel AG_ColdModel AG_Malloc AG_Malloc2 AG_WriteSet AG_MallocAll
     AS_Refill1 AS_Refill2 AS_Refill4 AG_Refill1 AG_Refill2 AG_Refill3 AG_MallocCold AG_Free1 AG_Free6 AG_Free7 AG_Free AG_ReallocF2 SecLazy AllocWalkKit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaGuard.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac lia ::=
  dle_wrap ltac:(first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ]).

(* [comment removed for export] *)
(* [comment removed for export] *)

Section ReallocColdGlue.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo size : Z) (CH : list (Z * Z)).
  (* [comment removed for export] *)
  Variables (och : chunk) (bs sbs : list byte).

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
  Let r := get_region st c.
  Let nf := rg_num_freed r. Let mfa := rg_mapped_free_array r. Let au := rg_allocated_user r. Let mu := rg_mapped_user r. Let fl := rg_free_array r.
  Let n := rf_n c.
  Let mu' := rf_mu' c nf au mu. Let nnew := rf_nnew c nf au mu. Let nf1 := rf_nf1 c nf au mu. Let mfa' := rf_mfa' c nf mfa au mu.
  Let au' := rf_au' c nf au mu. Let fl1 := rf_fl1 c nf au mu fl.
  Let st2 := refilled st c.
  Let chunks2 := firstn (Z.to_nat n) fl1.
  Let cp := hd 0 chunks2.
  Let AB := compact_to_addr st2 c cp.
  Let U := AB + rz.
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CH.
  Let T := utrace 0x1bf8f0 (bv_unsigned sp) (a_top s) (a_bot s) 30 CHI.   (* [comment removed for export] *)
  Let nT := Z.of_nat (length T).
  Let id := d_putid d (depot_hash T).
  Let d' := d_put d (depot_hash T) nT.
  Let L2 : list (word * word) :=
    if mfa <? mfa' then maps_subtract (if mu <? mu' then maps_subtract (a_L s) (RB s c + mu) (RB s c + mu') else a_L s) (FA s c + mfa) (FA s c + mfa')
    else (if mu <? mu' then maps_subtract (a_L s) (RB s c + mu) (RB s c + mu') else a_L s).
  Let S2 : list (word * word) :=
    (if mfa <? mfa' then [(wz (sh (FA s c + mfa)), wz ((mfa' - mfa) / 8))] else [])
    ++ (if mu <? mu' then [(wz (sh (RB s c + mu)), wz ((mu' - mu) / 8))] else []) ++ a_S s.
  Let sR := mkAst st2 (a_thr s) (a_ctx s) (a_fsb s) L2 S2 (a_Zr s) (a_AL s) (a_top s) (a_bot s).
  Let ch := mkChunk AB U size rz c CAllocated.
  Let stH := hit_state st2 c n (tl chunks2) ch.
  Let st3 := set_internal_init stH.
  Let sF := mkAst st3 (a_thr s) (a_ctx s) (a_fsb s) L2 S2 (a_Zr s) (a_AL s) (a_top s) (a_bot s).
  (* [comment removed for export] *)
  Let P0 := ch_user_beg och.
  Let old := ch_used och.
  (* [comment removed for export] *)
  Let Wr : list ivl := (lo, bv_unsigned sp) :: (TH + 3168, TH + 3169) :: (AIAINIT, AIAINIT + 4) :: (AIAINST, AIAINST + 0x81030) :: (TH + 2856, TH + 2872)
                       :: rf_W lo (bv_unsigned sp) P RI (FA s c) (RB s c) TH CA nf mfa mu mfa' mu'.
  Let Wt : list ivl := (lo, bv_unsigned sp) :: (P, P + 4) :: (CA + 2576, CA + 2584) :: (AB, AB + csz) :: (sh AB, sh AB + csz8)
                       :: (TH + 2800, TH + 3169) :: (AIAINIT, AIAINIT + 4) :: (AIAINST, AIAINST + 0x81030) :: depot_W d.
  Definition rc_W : list ivl := Wr ++ Wt.

  Hypothesis HR : ARHEAP s LB m.
  Hypothesis AX : awin_vis s m /\ flagsx_rep m.
  Hypothesis AMX : AMODELX s mo.
  Hypothesis DEP : DEPOT asegs d m.
  Hypothesis DPL : depot_placed s d.
  Hypothesis DCOV : depot_cov d mo.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 3072 <= bv_unsigned sp.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis SZ : 1 <= size /\ needed <= kMaxSize.
  Hypothesis MISS : pc_count (get_pc st c) = 0.
  Hypothesis TP : tp = wz ATP.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + 31 <= 131072.
  Hypothesis FCH : goodframe (a_bot s) (bv_unsigned sp) (a_top s) = true -> goodframe (bv_unsigned sp) (bv_unsigned s0) (a_top s) = true ->
                   bv_unsigned sp + 16 <= bv_unsigned s0 /\ frame_chain asegs m (a_top s) (bv_unsigned s0) CH.
  Hypothesis Ha0 : a0 = wz P0.
  Hypothesis Ha1 : a1 = wz size.
  Hypothesis CHIN0 : In och (chunk_list st).
  Hypothesis ALLOC0 : ch_state och = CAllocated.
  Hypothesis OLDSZ : old <= 64512.
  Hypothesis SZB : size <= 64512.
  Hypothesis BLK0 : rw_cells asegs m P0 [CB (Z.to_nat old) bs].
  Hypothesis SHB0 : SHAD m P0 sbs /\ Z.of_nat (length sbs) = nsh old.
  Hypothesis AC : ACONST m.
  (* [comment removed for export] *)
  Hypothesis PROOM : pusage st + COLD_COST <= B_PRIM.
  Hypothesis ROOM : mu + 2 * kUserMapSize <= kFreeArrayOffset.
  Hypothesis OK : lzok asegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo).
  Hypothesis VISE : restrict (a_L s) (a_S s) msF
    = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1bf7b4) fc None m (seg_rom asegs).

  (* [comment removed for export] *)
  Definition realloc_cold_gpost (msF' : machine_state) (mo' : Model) : Prop :=
    exists (t0' t1' t2' a6' a7' t3' t4' t5' t6' cfu : word) (jk jr1 jr2 junk : list byte) (rest : list word) (m' : mem),
       lzok asegs (a_L sF) (a_S sF) (a_Zr sF) (mkCfg msF' mo')
    /\ restrict (a_L sF) (a_S sF) msF'
       = MS (mkR (wz 0x197a10) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0' t1' t2'
                 (Z_to_bv 64 (bv_unsigned sp + -2136)) (wz P0) (wz AINST) (wz P0) (wz 0) (wz 0) (Z_to_bv 64 (bv_unsigned sp + -2136)) (wz 1) a6' a7'
                 (wz AINST) (wz (Z.min size old)) (wz U) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (bv_unsigned sp + -89)) s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x196ae8) fc None m' (seg_rom asegs)
    /\ ARHEAP sF ((U, size) :: LB) m' /\ awin_vis sF m' /\ flagsx_rep m' /\ AMODELX sF mo' /\ nonvm_same mo mo'
    /\ DEPOT asegs d' m' /\ depot_placed sF d' /\ depot_cov d' mo'
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + -2208)
    /\ munch rc_W m m' /\ wmono asegs m m'
    /\ avmx s sF mo mo'
    /\ rw_cells asegs m' U [CB (Z.to_nat size) (firstn (Z.to_nat (Z.min size old)) bs ++ skipn (Z.to_nat (Z.min size old)) junk)] /\ length junk = Z.to_nat size
    /\ addressable m' U size
    /\ (forall kaddr, exists st'' ev, am_malloc_k st size kaddr = Some (U, st'', ev) /\ same_but_shadow st'' stH)
    (* [comment removed for export] *)
    /\ rw_cells asegs m' (bv_unsigned sp + -2208) [C8 cfu; C8 (wz 0x1bf8f0); C8 (wz P0); C8 (wz size); C8 sp; C8 (wz 0x197900)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2160) [CB 8 jr1; C8 (wz 0x1bf960)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2144) [CB 8 jr2]
    /\ rw_cells asegs m' (bv_unsigned sp + -2136) [C8 (wz (bv_unsigned sp + -2136 + 16)); C8 (wz nT)]
    /\ u64arr asegs m' (bv_unsigned sp + -2136 + 16) (map wz T ++ rest) /\ length rest = (255 - length T)%nat
    /\ rw_cells asegs m' (bv_unsigned sp + -80) [C8 sp]
    /\ rw_cells asegs m' (bv_unsigned sp + -72) [CB 8 jk; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' P0 [CB (Z.to_nat old) bs] /\ SHAD m' P0 sbs
    /\ rw_cells asegs m' AIAINIT [C1 (b8 1); C1 (b8 0); C2 (wz 0)] /\ ia_after m'
    /\ Forall (fun x => 0 <= x < 2^64) T /\ (1 <= length T <= 30)%nat.

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
  Let UHI0 : aapp (ch_user_beg och - 16) (16 + round_up (ch_used och) 8). Proof. exact (uhi_of_arep s m och R CHIN0). Qed.

  (* [comment removed for export] *)
  Tactic Notation "bands_as" simple_intropattern(p) :=
    (let X := fresh "BX" in
     lazymatch goal with B : hidden ((TH + 4096 <= 65536 \/ _) /\ _) |- _ => pose proof B as X; destruct X as [p] end).

  Theorem realloc_arep_cold :
    (forall msF' mo', realloc_cold_gpost msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF mo).
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
    destruct (free_cells s m och R CHIN0 ALLOC0 UHI0) as (b1o & actxo & q0o & q1o & q2o & q3o & HDR0 & Hb1o & ACR0 & _ & _ & _ & _ & _ & _ & _).
    fold P0 old in HDR0.
    pose proof (free_pure s m och R CHIN0 UHI0) as (O1 & (O2a & O2b & O2c) & O3 & O4 & O5 & O6 & _). fold P0 old in O1, O2a, O2b, O2c, O3, O4, O5, O6. unfold AIMG_TOP in O2c.
    assert (P0R : 12599312 <= P0 /\ P0 + old <= aceil /\ aceil <= 2^47) by (acb; clear - O1 O2c O3 O5 ACEILB; try acb; lia).
    assert (RU8 : old <= round_up old 8 /\ round_up old 8 = 8 * nsh old /\ 0 <= nsh old) by (unfold round_up, nsh; clear - O1; Z.div_mod_to_equations; lia).
    pose proof (ext_facts s OKs och CHIN0) as (EX1 & EX2 & EX3 & EX4 & _).
    pose proof (chunk_geom s OKs och CHIN0) as CG. cbv zeta in CG. destruct CG as (CG1 & CG2 & CG3 & CG4 & CG5 & CG6 & _). fold P0 old in CG2, CG3, CG4, CG5, CG6.
    assert (PRIM0 : ch_primary och = true).
    { pose proof (WF_chunk st och WFs CHIN0) as CK. unfold chunk_ok in CK. destruct CK as (_ & _ & _ & _ & CK5).
      destruct (ch_primary och) eqn:PX; [reflexivity| exfalso]. destruct CK5 as (NP & _). fold old in NP.
      change (rq_primary (compute_req old)) with (mprimary old) in NP.
      rewrite (proj2 (mprimary_iff old O1) OLDSZ) in NP. discriminate NP. }
    destruct (EX4 PRIM0) as (CV0 & CE0 & CS0a & CS0b).
    assert (LO0 : ch_lo och = ch_alloc_beg och) by (unfold ch_lo; rewrite PRIM0; reflexivity).
    (* [comment removed for export] *)
    assert (FLG4 : rw_cells asegs m AIAINIT [C1 (b8 (if as_internal_init st then 1 else 0)); C1 (b8 0); C2 (wz 0)]).
    { pose proof R as RR. destruct RR as (_ & _ & FL & _).
      destruct FL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F16 & _). exact F16. }
    assert (IAX : if as_internal_init st then ia_after m else ia_pristine m).
    { pose proof R as RR. destruct RR as (_ & _ & _ & _ & _ & IA & _). unfold ia_rep in IA. unfold ia_after, ia_pristine. exact IA. }
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs (a_L s) (a_S s) (a_Zr s) _ msF _ mo Q OK VISE).
    { eapply (@realloc_head _ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo size d
                ATSD CTX TH (a_top s) (a_bot s) CH sb (wz (if as_cache_inited st then max_count c else 0)) P0 (as_internal_init st) rz needed c CA P).
      - constructor. repeat split; reflexivity.
      - exact LO.
      - clear - HI; try acb; lia.
      - constructor. exact SPA.
      - constructor. exact SPT.
      - exact SZ.
      - constructor. rewrite TP. unfold wz, ATP, AIMG_TOP. rewrite unsigned_lit by (clear; lia). clear; lia.
      - constructor. unfold ATSD, AIMG_TOP. unfold kPageSize in T2. clear - BND T2 X2; try acb.
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
      - unfold AIMG_TOP. clear - P0R O1; lia.
      - exact SZB.
      - exact FLG4.
      - exact IAX.
      - exact IEN.
      - exact MI.
      - exact ST.
      - exact PC1.
      - exact UNW.
      - exact TST.
      - exact DEP. }
    cbv beta. intros msF1 mo1 OK1 SBM1 _ PO1.
    destruct PO1 as (t0_1 & t1_1 & t2_1 & a4_1 & a5_1 & a6_1 & a7_1 & t3_1 & t4_1 & t5_1 & t6_1 & cfu & jk & j8 & jr1 & jr2 & rest & m1 & VIS1 & MU1 & WM1 & MI1 & AEN1 & LR & TRNG & NRT
                     & ST1 & FRC1 & AFR1 & FRR1 & FRA1 & FP1 & TFB1 & F81 & PC1' & UNW1 & DEP1 & FLG1 & IA1 & TST1).
    change (length rest = (255 - length T)%nat) in LR. change (Forall (fun x => 0 <= x < 2^64) T) in TRNG. change ((1 <= length T <= 30)%nat) in NRT.
    change (AENV tp ATSD CTX TH sb (bv_unsigned sp + -2136) T rest m1) in AEN1.
    (* [comment removed for export] *)
    pose proof (munch_agree _ _ _ MU1) as AG1.
    assert (Z1 : forall a, a < lo /\ a <> TH + 3168 /\ ~ (AIAINIT <= a < AIAINIT + 4) /\ ~ (AIAINST <= a < AIAINST + 0x81030) /\ ~ (TH + 2856 <= a < TH + 2872) ->
                 outside [(lo, bv_unsigned sp); (TH + 3168, TH + 3169); (AIAINIT, AIAINIT + 4); (AIAINST, AIAINST + 0x81030); (TH + 2856, TH + 2872)] a).
    { intros a Ha. cbn [outside]. clear - Ha; try acb. repeat split; try exact I; lia. }
    pose proof CSZ as (CS1 & CS2 & CS3 & CS4).
    assert (BR : 0 <= nf /\ 4 * nf <= mfa /\ mfa <= 536870912 /\ 0 <= au <= mu /\ mu + 262144 <= 3758096384 /\ Z.of_nat (length (wlist (rev fl))) = nf /\ 32 <= csz <= 65536)
      by (clear - U1 U2 U4 U5 U8 CS1; try acb; unfold kFreeArraySize, kUserMapSize, kFreeArrayOffset in *; repeat split; lia).
    name_bands.
    bands_as (BT & _).
    assert (BI : AIAINIT = 7578504 /\ AIAINST = 6994688 /\ (TH + 4096 <= 65536 \/ (12599296 <= TH /\ TH + 4096 <= 2147446784) \/ 17594333495296 <= TH))
      by (split; [reflexivity| split; [reflexivity| exact BT]]).
    pose proof (conj BND (conj BR (conj BDJ1 BI))) as BB. pose proof (conj BND (conj BDJ1 BI)) as BD1. pose proof (conj BND BI) as BNDI.
    assert (PCJ1 : stk asegs m1 (a_cache s + PCLASS_SIZE * c + 16) (a_cache s + PCLASS_SIZE * c + 80)) by (unfold a_cache, OT_CACHE, PCLASS_SIZE in *; trp stk_transport_pt AG1 WM1 PCJ Z1 BNDI).
    assert (FAM1 : forall c', 1 <= c' <= 31 -> exists mc cs, rw_cells asegs m1 (a_cache s + 80 * c' + 4) [C4 mc] /\ rw_cells asegs m1 (a_cache s + 80 * c' + 8) [C8 cs]
                                              /\ (as_cache_inited st = true -> mc = wz (max_count c') /\ cs = wz (class_size c'))).
    { intros c' Hc'. destruct (FAM c' Hc') as (mc & cs & V1 & V2 & V3). exists mc, cs. unfold a_cache, OT_CACHE in *. pose proof (conj BNDI Hc') as B2.
      split; [trp rw_cells_transport_pt AG1 WM1 V1 Z1 B2|]. split; [trp rw_cells_transport_pt AG1 WM1 V2 Z1 B2| exact V3]. }
    assert (QST1 : rw_cells asegs m1 (TH + 2768) [C8 q0; C8 q1; C8 q2; C8 q3]) by (trp rw_cells_transport_pt AG1 WM1 QST Z1 BNDI).
    assert (RIC1 : rw_cells asegs m1 RI [C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz nf); C8 (wz mfa); C8 (wz au); C8 (wz 0); C8 (wz mu); C8 (wz 0)]) by (trp rw_cells_transport_pt AG1 WM1 RIC Z1 BD1).
    assert (RIJ1 : stk asegs m1 (RI + 64) (RI + 68)) by (trp stk_transport_pt AG1 WM1 RIJ Z1 BD1).
    assert (EXH1 : rw_cells asegs m1 (RI + 68) [C1 (b8 0)]) by (trp rw_cells_transport_pt AG1 WM1 EXH Z1 BD1).
    assert (RST1 : stk asegs m1 (RI + 69) (RI + 128)) by (trp stk_transport_pt AG1 WM1 RST Z1 BD1).
    assert (FARR1 : u32arr asegs m1 (FA s c) (wlist (rev fl))) by (trp u32arr_transport_pt AG1 WM1 FARR Z1 BB).
    assert (FAJ1 : stk asegs m1 (FA s c + 4 * nf) (FA s c + mfa)) by (trp stk_transport_pt AG1 WM1 FAJ Z1 BB).
    assert (USJ1 : stk asegs m1 (RB s c + au) (RB s c + mu)) by (trp stk_transport_pt AG1 WM1 USJ Z1 BB).
    assert (REN1 : RENV (wz ATP) ATSD (a_ctx s) TH sb (a_ri s) m1).
    { apply (renv_transport (wz ATP) ATSD (a_ctx s) TH sb (a_ri s) m m1 _ REN MU1 WM1); cbn [disjoint_from]; unfold wz, ATP, ATSD, AIAINIT, AIAINST; rewrite ?unsigned_lit by (clear; lia); clear - BND BDJ2; try acb; unfold CTX in *; lia. }
    (* [comment removed for export] *)
    pose proof (ACONST_memcpyp m AC) as MCP. unfold AMEMCPYP_CELL in MCP.
    assert (MCP1 : rw_cells asegs m1 6204008 [C8 (wz AREAL_MEMCPY)]) by (trp rw_cells_transport_pt AG1 WM1 MCP Z1 BNDI).
    assert (K0 : 12599312 <= P0 /\ P0 + old <= aceil /\ aceil <= lo /\ 16 <= ch_rz och /\ 1 <= old /\ sb + 16 <= P0 /\ P0 + old <= sb + 137438953472).
    { unfold kSpaceSize in CS0b. unfold sb. clear - P0R LO CG1 O1 CG2 CG4 CS0a CS0b RU8; try acb. lia. }
    pose proof (conj K0 (conj BNDI BDJ1)) as K0B.
    assert (HDR1 : rw_cells asegs m1 (P0 + -16) [C1 (b8 2); C1 (b8 b1o); C2 (wz 0); C4 (wz old); C8 (wz actxo)]) by (trp rw_cells_transport_pt AG1 WM1 HDR0 Z1 K0B).
    assert (BLK1 : rw_cells asegs m1 P0 [CB (Z.to_nat old) bs]).
    { eapply (rw_cells_transport_pt _ m m1 AG1 WM1); [exact BLK0|]. cbn [cells_size csize Nat.add Nat.mul]. rewrite Nat.add_0_r, Z2Nat.id by (clear - O1; lia).
      intros a Ha. apply Z1. clear - Ha K0B; try acb. lia. }
    destruct SHB0 as [SHB0a SHB0l].
    assert (SHB1 : SHAD m1 P0 sbs).
    { eapply (SHAD_transport_pt _ m m1 AG1 WM1); [exact SHB0a|]. rewrite SHB0l. intros a Ha. apply Z1.
      assert (SR0 : 0x7fff8000 + 12599312 / 8 <= sh P0 /\ sh P0 + nsh old <= 0x10007fff8000) by (clear - K0 RU8 O3; try acb; unfold sh, ASHADOW_BASE, nsh, round_up in *; Z.div_mod_to_equations; lia).
      clear - Ha SR0 BNDI BND; try acb. lia. }
    (* [comment removed for export] *)
    pose proof (AMODELX_mat s mo mo1 (conj AM AK) SBM1) as AMX1. pose proof AMX1 as AMX1'. destruct AMX1' as [AM1 AK1].
    pose proof AM1 as AM1'. destruct AM1' as (AIL1 & ASV1 & AB1). destruct AIL1 as (_ & _ & _ & NOV1 & NW1 & NWA1). destruct AB1 as [AB1a AB1b].
    (* [comment removed for export] *)
    eapply (refill_sreach (a_L s) (a_S s) (a_Zr s) msF1 mo1 Q (wz 0x19b90c) (Z_to_bv 64 (bv_unsigned sp + -2384)) gp tp t0_1 t1_1 t2_1
              (Z_to_bv 64 c) (wz P) a4_1 a5_1 a6_1 a7_1 (wz 8) (wz CA) (wz AINST) (wz size) (wz AINST) (wz (bv_unsigned sp + -2136))
              (Z_to_bv 64 (-8)) (wz 7) (wz TH) (wz 1) t3_1 t4_1 t5_1 t6_1 F fc m1 lo sb c CA TH CTX ATSD nf mfa au mu fl (as_cache_inited st)).
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
    { exact (ak_atop s mo1 AK1). }
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
      repeat lazymatch goal with
        | |- disjoint_from (icW _) _ _ => apply icW_disjoint; clear - BND; try acb; lia
        | |- _ /\ _ => split; [clear - BB2 SHB BDJ1 BT; try acb; (first [clear - BB2 BDJ1 ACEILB BT SHB; lia | lia])|]
        end. }
    (* [comment removed for export] *)
    pose proof (wmono_trans _ _ _ _ WM1 WM2) as WM02.
    assert (AG02 : agree_on (outside Wr) m m2).
    { intros x Hx Hr. transitivity (m1 (wa x)).
      - apply MU2. rewrite wa_unsigned by exact Hr. revert Hx. unfold Wr, rf_W. cbn [outside app]. clear - HI; try acb. intros (X1 & X2 & X3 & X4 & X5 & X6 & REST).
        split; [clear - X1 HI; try acb; lia| exact REST].
      - apply MU1. rewrite wa_unsigned by exact Hr. revert Hx. unfold Wr. cbn [outside]. clear. intros (X1 & X2 & X3 & X4 & X5 & _). repeat split; try exact I; assumption. }
    (* [comment removed for export] *)
    set (Wo := [(AIAINIT, AIAINIT + 4); (AIAINST, AIAINST + 0x81030)]).
    set (mR := chim Wo m m2).
    assert (ZWo : forall a, a < 65536 \/ 12599296 <= a -> outside Wo a) by (intros a Ha; subst Wo; cbn [outside]; unfold AIAINIT, AIAINST; clear - Ha; lia).
    assert (MIR : mem_inv asegs mR) by exact (chim_mem_inv Wo m m2 MI MI2).
    pose proof (chim_agree_out Wo m m2 : agree_on (outside Wo) m2 mR) as AGoR.
    pose proof (agree_on_sym _ _ _ AGoR) as AGRo.
    assert (WM0R : wmono asegs m mR) by exact (chim_wmono_in Wo m m2 WM02).
    assert (AG0R : agree_on (outside ((lo, bv_unsigned sp) :: (TH + 3168, TH + 3169) :: rf_W lo (bv_unsigned sp) P RI (FA s c) (RB s c) TH CA nf mfa mu mfa' mu')) m mR).
    { intros x Hx Hr. subst mR. unfold chim. rewrite wa_unsigned by exact Hr. destruct (inb Wo x) eqn:E; [reflexivity|].
      apply inb_false_outside in E. apply (AG02 x); [| exact Hr]. revert Hx E. subst Wo. unfold Wr, rf_W. cbn [outside]. clear.
      intros (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & REST) (Y1 & Y2 & _).
      repeat (lazymatch goal with |- outside (icW _) _ => exact REST | |- _ /\ _ => split | |- _ => first [assumption | clear - X15; lia] end). }
    (* [comment removed for export] *)
    Ltac toR lem AGX H Z B := eapply (lem (outside _) _ _ AGX); [exact H|];
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Z.mul length];
      let Ha := fresh in intros ? Ha; apply Z; clear - Ha B; try acb; lia.
    pose proof (conj BND (conj BR (conj BR2 BT))) as BBT.
    assert (PCNR : rw_cells asegs mR P [C4 (wz n)]) by (toR rw_cells_pteq AGoR PCN ZWo BBT).
    assert (FAMR : forall c', 1 <= c' <= 31 -> rw_cells asegs mR (CA + 80 * c' + 4) [C4 (wz (max_count c'))] /\ rw_cells asegs mR (CA + 80 * c' + 8) [C8 (wz (class_size c'))]).
    { intros c' Hc'. destruct (FAM2 c' Hc') as [V1 V2]. pose proof (conj BBT Hc') as B2. split; [toR rw_cells_pteq AGoR V1 ZWo B2| toR rw_cells_pteq AGoR V2 ZWo B2]. }
    assert (CHAR : u32arr asegs mR (P + 16) (wlist (rev (firstn (Z.to_nat n) fl1)))).
    { eapply (u32arr_pteq (outside Wo) m2 mR AGoR); [exact CHA|]. unfold wlist. rewrite length_map, length_rev, length_firstn. intros a Ha. apply ZWo. clear - Ha BBT. lia. }
    assert (CHJR : stk asegs mR (P + 16 + 4 * n) (P + 80)) by (toR stk_pteq AGoR CHJ ZWo BBT).
    assert (RI2R : rw_cells asegs mR RI [C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz (nf1 - n)); C8 (wz mfa'); C8 (wz au'); C8 (wz 0); C8 (wz mu'); C8 (wz 0)]) by (toR rw_cells_pteq AGoR RI2 ZWo BBT).
    assert (RIJR : stk asegs mR (RI + 64) (RI + 68)) by (toR stk_pteq AGoR RIJ2 ZWo BBT).
    assert (EXHR : rw_cells asegs mR (RI + 68) [C1 (b8 0)]) by (toR rw_cells_pteq AGoR EXH2 ZWo BBT).
    assert (RSTR : stk asegs mR (RI + 69) (RI + 128)) by (toR stk_pteq AGoR RST2 ZWo BBT).
    assert (FARRR : u32arr asegs mR (FA s c) (wlist (rev fl1))).
    { eapply (u32arr_pteq (outside Wo) m2 mR AGoR); [exact FARR2|]. unfold wlist. rewrite length_map, length_rev. intros a Ha. apply ZWo. clear - Ha BBT. lia. }
    assert (FAJR : stk asegs mR (FA s c + 4 * nf1) (FA s c + mfa')) by (toR stk_pteq AGoR FAJ2 ZWo BBT).
    assert (USJR : stk asegs mR (RB s c + au) (RB s c + mu')) by (toR stk_pteq AGoR USJ2 ZWo BBT).
    assert (POIuR : poisoned mR (RB s c + mu) (Z.to_nat ((mu' - mu) / 8)) 0xfa).
    { eapply (poisoned_pteq (outside Wo) m2 mR AGoR); [exact POIu|]. intros a Ha. apply ZWo. clear - Ha BBT SHB. unfold sh, ASHADOW_BASE in *. lia. }
    assert (POIfR : poisoned mR (FA s c + mfa) (Z.to_nat ((mfa' - mfa) / 8)) 0xfa).
    { eapply (poisoned_pteq (outside Wo) m2 mR AGoR); [exact POIf|]. intros a Ha. apply ZWo. clear - Ha BBT SHB. unfold sh, ASHADOW_BASE in *. lia. }
    assert (QSTR : rw_cells asegs mR (TH + 2768) [C8 q0'; C8 q1'; C8 q2'; C8 q3']) by (toR rw_cells_pteq AGoR QST2 ZWo BBT).
    assert (TSTR : stk asegs mR (TH + 2800) (TH + 3168)) by (toR stk_pteq AGoR TST2 ZWo BBT).
    assert (UNWR : rw_cells asegs mR (TH + 3168) [C1 (b8 0)]) by (toR rw_cells_pteq AGoR UNW2 ZWo BBT).
    pose proof (arep_after_refill s m mR c L2 S2 (a_AL s) lo (bv_unsigned sp) q0' q1' q2' q3' R HC MISS ROOM LO AG0R WM0R
                  PCNR FAMR CHAR CHJR RI2R RIJR EXHR RSTR FARRR FAJR USJR POIuR POIfR QSTR TSTR UNWR) as R2.
    pose proof (flagsx_after_refill s m mR c lo (bv_unsigned sp) R HC MISS ROOM LO AG0R WM0R FXR) as FX2.
    assert (HAL : 0 <= a_AL s <= a_AL s) by (clear - AB1a; lia).   (* [comment removed for export] *)
    pose proof (amodelx_after_refill s mo1 mo2 c L2 S2 (a_AL s) AMX1 OKs HC ROOM (lazy_ranges_okb_nowrap asegs _ (lzok_ranges OK))
                  eq_refl eq_refl VMM VMR VML (nonvm_same_atop _ _ NVS) VMN EAG HAL) as AMX2.
    (* [comment removed for export] *)
    pose proof (rfd_pc_c st c WFs HC ROOM) as PCc.
    assert (HIT2 : pc_count (get_pc st2 c) <> 0) by (unfold st2; rewrite PCc; cbn [pc_count refill_pc]; fold n; clear - NR; try acb; lia).
    pose proof (hit_cells_of_arep sR mR R2 c ltac:(hci; unfold kNumClasses; clear - HC; try acb; lia) HIT2) as HCL. cbv zeta in HCL.
    cbn [a_st a_cache a_sb a_thr] in HCL. fold st TH in HCL. unfold st2 in HIT2. fold st2 in HCL, HIT2.
    rewrite PCc in HCL. cbn [pc_count pc_chunks refill_pc] in HCL. fold n in HCL. fold fl1 in HCL. fold chunks2 in HCL. fold cp in HCL.
    destruct HCL as (j0 & j1 & j2 & j3 & QC1 & QC2 & QC3 & QC4 & QSTb & CHUNK & SHK & TSTb & UNWb & CC & CR & CPS & ABlo & ABhi & INI).
    change (n = zlen chunks2) in CC.
    assert (ABE : AB = sb + c * 2^32 + cp * 16) by (unfold AB; rewrite compact_to_addr_eq, region_beg_eq; reflexivity).
    rewrite <- ABE in CHUNK, SHK, ABlo, ABhi. change (a_sb sR) with sb in ABlo, ABhi. unfold kSpaceSize in ABhi.
    pose proof (conj BBT (conj ABlo (conj ABhi CS1))) as BBA.
    Ltac to2 lem AGX H Z B := eapply (lem (outside _) _ _ AGX); [exact H|];
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Z.mul length];
      let Ha := fresh in intros ? Ha; apply Z; clear - Ha B; try acb; lia.
    assert (QC1m : rw_cells asegs m2 P [C4 (wz n); C4 (wz (max_count c))]) by (to2 rw_cells_pteq AGRo QC1 ZWo BBT).
    assert (QC2m : rw_cells asegs m2 (P + 8) [C8 (wz (class_size c))]) by (to2 rw_cells_pteq AGRo QC2 ZWo BBT).
    assert (LENC4 : 4 * Z.of_nat (length (wlist (rev chunks2))) = 4 * n).
    { unfold wlist. rewrite length_map, length_rev. pose proof CC as CC'. change (n = zlen chunks2) in CC'. unfold zlen in CC'. clear - CC'. lia. }
    assert (QC3m : u32arr asegs m2 (P + 16) (wlist (rev chunks2))).
    { eapply (u32arr_pteq (outside Wo) mR m2 AGRo); [exact QC3|]. rewrite LENC4. intros a Ha. apply ZWo. clear - Ha BBT. lia. }
    assert (QC4m : stk asegs m2 (P + 16 + 4 * n) (P + 80)) by (to2 stk_pteq AGRo QC4 ZWo BBT).
    assert (QSTm : rw_cells asegs m2 (TH + 208 + 2560) [C8 j0; C8 j1; C8 j2; C8 j3]) by (to2 rw_cells_pteq AGRo QSTb ZWo BBT).
    assert (CHUNKm : stk asegs m2 AB (AB + csz)) by (to2 stk_pteq AGRo CHUNK ZWo BBA).
    assert (SHKm : u8arr asegs m2 (sh AB) (repeat (b8 0xfa) (Z.to_nat csz8))).
    { eapply (u8arr_pteq (outside Wo) mR m2 AGRo); [exact SHK|]. intros a Ha. apply ZWo. clear - Ha BBA. unfold sh, ASHADOW_BASE in *. lia. }
    (* [comment removed for export] *)
    assert (GD : (TH + 4096 <= d_nb d \/ d_nb d + 1048576 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 1048576 <= TH)
                 /\ (sb + 137438953472 + 4096 <= d_nb d \/ d_nb d + 1048576 <= sb) /\ (sb + 137438953472 + 4096 <= d_sb d \/ d_sb d + 1048576 <= sb)).
    { unfold disj, kPageSize, kSpaceSize in G1, G2, G3, G4. clear - G1 G2 G3 G4; try acb. unfold TH, sb. lia. }
    assert (DAV : depot_avoid (rf_W lo (bv_unsigned sp + -2384) (CA + PCLASS_SIZE * c) (sb + kSpaceSize + REGIONINFO_SIZE * c) (FA s c) (RB s c) TH CA nf mfa mu mfa' mu') d).
    { pose proof GD as (GD1 & GD2 & GD3 & GD4). unfold depot_avoid, avoids, rf_W, PCLASS_SIZE, REGIONINFO_SIZE, kSpaceSize.
      bands_as (_ & _ & _ & BN & BS).
      split; [| split; [| split]].
      - do 13 (apply Forall_cons; [cbn [fst snd]; clear - BB2 SHB BT; try acb; (first [clear - BB2 BT SHB; lia | lia])|]). apply icW_avoids. clear - BND BT; try acb; lia.
      - do 13 (apply Forall_cons; [cbn [fst snd]; clear - BB2 SHB BT; try acb; lia|]). apply icW_avoids. clear - BND BT; try acb; lia.
      - do 13 (apply Forall_cons; [cbn [fst snd]; clear - BB2 SHB GD1 GD3 BN; try acb; (first [clear - BB2 ACEILB GD1 GD3 SHB BN; lia | lia])|]). apply icW_avoids. clear - BND GD1; try acb; lia.
      - do 13 (apply Forall_cons; [cbn [fst snd]; clear - BB2 SHB GD2 GD4 BS; try acb; (first [clear - BB2 ACEILB GD2 GD4 SHB BS; lia | lia])|]). apply icW_avoids. clear - BND GD2; try acb; lia. }
    pose proof (DEPOT_transport asegs d m1 m2 _ DEP1 MU2 WM2 DAV) as DEP2.
    (* [comment removed for export] *)
    assert (ZR : forall a, (65536 <= a < 12599296 \/ TH <= a < TH + 288 \/ CTX <= a < CTX + 160 \/ bv_unsigned sp + -2384 <= a) ->
                 outside (rf_W lo (bv_unsigned sp + -2384) (CA + PCLASS_SIZE * c) (sb + kSpaceSize + REGIONINFO_SIZE * c) (FA s c) (RB s c) TH CA nf mfa mu mfa' mu') a).
    { intros a Ha. unfold rf_W, PCLASS_SIZE, REGIONINFO_SIZE, kSpaceSize. cbn [outside]. bands_as (_ & BC & _).
      destruct BDJ as (BDJa & BDJb & BDJc). destruct Ha as [Ha|[Ha|[Ha|Ha]]].
      - clear BDJa BDJb BDJc BDJ2 BC. destruct BT as [BT'|[BT'|BT']]; repeat lazymatch goal with
        | |- outside (icW _) _ => apply outside_icW_far; clear - Ha BND HI BT'; try acb; lia
        | |- _ /\ _ => split; [clear - Ha BB2 SHB HI BT'; try acb; (first [clear - Ha BB2 BT' SHB; lia | lia])|]
        end.
      - clear BDJb BDJc BDJ2 BC. repeat lazymatch goal with
        | |- outside (icW _) _ => apply outside_icW_far; clear - Ha BND HI BT; try acb; lia
        | |- _ /\ _ => split; [clear - Ha BB2 SHB HI BT BDJa; try acb; (first [clear - Ha BB2 BDJa ACEILB BT SHB; lia | lia])|]
        end.
      - clear BDJa BDJ2. repeat lazymatch goal with
        | |- outside (icW _) _ => apply outside_icW_far; clear - Ha BND HI BDJb; try acb; lia
        | |- _ /\ _ => split; [clear - Ha BB2 SHB HI BC BDJb BDJc; try acb; (first [clear - BB2 Ha ACEILB BDJb BDJc SHB BC; lia | lia])|]
        end.
      - clear BDJa BDJb BDJc BDJ2 BC. repeat lazymatch goal with
        | |- outside (icW _) _ => apply outside_icW_far; clear - Ha BND HI; try acb; lia
        | |- _ /\ _ => split; [clear - Ha BB2 SHB HI; try acb; lia|]
        end. }
    pose proof (munch_agree _ _ _ MU2) as AG2.
    assert (AEN2 : AENV tp ATSD CTX TH sb (bv_unsigned sp + -2136) T rest m2).
    { eapply (aenv_transport_pt _ tp ATSD CTX TH sb _ T rest m1 m2 AEN1 AG2 WM2).
      - intros a Ha. apply ZR. left. unfold AIMG_LO, AIMG_TOP in Ha. clear - Ha; try acb. lia.
      - intros a Ha. apply ZR. clear - Ha; try acb. lia.
      - intros a Ha. apply ZR. clear - Ha; try acb. lia.
      - intros a Ha. apply ZR. clear - Ha; try acb. lia.
      - rewrite TP. unfold wz, ATP, AIMG_TOP. rewrite unsigned_lit by (clear; lia). clear; lia.
      - unfold ATSD, AIMG_TOP. clear; lia. }
    assert (FRC2 : rw_cells asegs m2 (bv_unsigned sp + -2384) [C8 (wz rz); C8 (wz needed); C8 (wz 8); C8 (wz size); C8 (wz 1); C8 (wz 1667228)]) by (trp rw_cells_transport_pt AG2 WM2 FRC1 ZR BND).
    assert (AFR2 : aframe (Z_to_bv 64 (bv_unsigned sp + -2208)) (wz 0x19797c) (Z_to_bv 64 (bv_unsigned sp + -2136)) (wz P0) (wz AINST) (wz size)
                          cfu (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (bv_unsigned sp + -89)) s7 s8 s9 s10 s11 m2 j8).
    { unfold aframe in AFR1 |- *. rewrite unsigned_lit in AFR1 |- * by (clear - SPR HI BND; try acb; lia). trp rw_cells_transport_pt AG2 WM2 AFR1 ZR BND. }
    assert (FRR2 : rw_cells asegs m2 (bv_unsigned sp + -2208) [C8 cfu; C8 (wz 0x1bf8f0); C8 (wz P0); C8 (wz size); C8 sp; C8 (wz 0x197900)]) by (trp rw_cells_transport_pt AG2 WM2 FRR1 ZR BND).
    assert (FRA2 : rw_cells asegs m2 (bv_unsigned sp + -2160) [CB 8 jr1; C8 (wz 0x1bf960)]) by (trp rw_cells_transport_pt AG2 WM2 FRA1 ZR BND).
    assert (FP2 : rw_cells asegs m2 (bv_unsigned sp + -2144) [CB 8 jr2]) by (trp rw_cells_transport_pt AG2 WM2 FP1 ZR BND).
    assert (TFB2 : rw_cells asegs m2 (bv_unsigned sp + -80) [C8 sp]) by (trp rw_cells_transport_pt AG2 WM2 TFB1 ZR BND).
    assert (F82 : rw_cells asegs m2 (bv_unsigned sp + -72) [CB 8 jk; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (trp rw_cells_transport_pt AG2 WM2 F81 ZR BND).
    assert (FLG2 : rw_cells asegs m2 AIAINIT [C1 (b8 1); C1 (b8 0); C2 (wz 0)]) by (unfold AIAINIT in *; trp rw_cells_transport_pt AG2 WM2 FLG1 ZR BND).
    assert (IA2 : ia_after m2).
    { apply (ia_if_transport true _ m1 m2 IA1 MU2 WM2). unfold rf_W. cbn [disjoint_from]. unfold PCLASS_SIZE, REGIONINFO_SIZE, kSpaceSize.
      repeat lazymatch goal with
        | |- disjoint_from (icW _) _ _ => apply icW_disjoint; clear - BND BT; try acb; lia
        | |- _ /\ _ => split; [clear - BB2 SHB BDJ1 BT; try acb; (first [clear - BB2 BDJ1 ACEILB BT SHB; lia | lia])|]
        | |- _ => clear - BB2 SHB BDJ1 BT; try acb; (first [clear - BB2 BDJ1 ACEILB BT SHB; lia | lia])
        end. }
    assert (MCP2 : rw_cells asegs m2 6204008 [C8 (wz AREAL_MEMCPY)]) by (trp rw_cells_transport_pt AG2 WM2 MCP1 ZR BND).
    (* [comment removed for export] *)
    assert (ZRo : forall a, ch_lo och <= a < ch_end och ->
                  outside (rf_W lo (bv_unsigned sp + -2384) (CA + PCLASS_SIZE * c) (sb + kSpaceSize + REGIONINFO_SIZE * c) (FA s c) (RB s c) TH CA nf mfa mu mfa' mu') a).
    { intros a Ha. pose proof (Z_carved s m c lo (bv_unsigned sp + -2384) R HC MISS ROOM LO (ch_class och) (ch_alloc_beg och) a CV0 ltac:(hci; clear - Ha CE0 LO0; lia)) as Z.
      cbn [outside] in Z. unfold a_cache, OT_CACHE, PCLASS_SIZE, REGIONINFO_SIZE, kSpaceSize in Z |- *. unfold a_ri in Z. fold TH sb in Z.
      exact (proj2 (proj2 Z)). }
    assert (ZRosh : forall a, sh P0 <= a < sh P0 + nsh old ->
                  outside (rf_W lo (bv_unsigned sp + -2384) (CA + PCLASS_SIZE * c) (sb + kSpaceSize + REGIONINFO_SIZE * c) (FA s c) (RB s c) TH CA nf mfa mu mfa' mu') a).
    { intros a Ha.
      pose proof (Z_carved_sh s m c lo (bv_unsigned sp + -2384) R HC MISS ROOM LO (ch_class och) (ch_alloc_beg och) P0 (nsh old) a CV0
                    ltac:(hci; clear - CG1 CG2; lia) ltac:(hci; clear - CG2 CG4 CG6 CE0; lia) ltac:(hci; clear - O4; Z.div_mod_to_equations; lia) ltac:(hci; clear - RU8; lia) Ha) as Z.
      cbn [outside] in Z. unfold a_cache, OT_CACHE, PCLASS_SIZE, REGIONINFO_SIZE, kSpaceSize in Z |- *. unfold a_ri in Z. fold TH sb in Z.
      exact (proj2 (proj2 Z)). }
    assert (HDR2 : rw_cells asegs m2 (P0 + -16) [C1 (b8 2); C1 (b8 b1o); C2 (wz 0); C4 (wz old); C8 (wz actxo)]).
    { eapply (rw_cells_transport_pt _ m1 m2 AG2 WM2); [exact HDR1|]. cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add length].
      intros a Ha. apply ZRo. clear - Ha CG1 CG2 CG4 LO0 RU8. lia. }
    assert (BLK2 : rw_cells asegs m2 P0 [CB (Z.to_nat old) bs]).
    { eapply (rw_cells_transport_pt _ m1 m2 AG2 WM2); [exact BLK1|]. cbn [cells_size csize Nat.add Nat.mul]. rewrite Nat.add_0_r, Z2Nat.id by (clear - O1; lia).
      intros a Ha. apply ZRo. clear - Ha CG1 CG2 CG4 LO0 RU8. lia. }
    assert (SHB2 : SHAD m2 P0 sbs).
    { eapply (SHAD_transport_pt _ m1 m2 AG2 WM2); [exact SHB1|]. rewrite SHB0l. exact ZRosh. }
    (* [comment removed for export] *)
    unfold wz in VIS2. rewrite (ret_pc_even 1685772) in VIS2 by (clear; lia).
    eapply (evt_sreach_lazy_at asegs L2 S2 (a_Zr s) _ msF2 _ mo2 Q OK2 VIS2).
    { eapply (realloc_from_refill sp gp tp s7 s8 s9 s10 s11 F fc m2 lo size d ATSD CTX TH (a_top s) (a_bot s) T rest
                sb n (max_count c) chunks2 j0 j1 j2 j3 rz needed c csz csz8 (Z.min size 4096) CA P cp AB U nT id P0 cfu).
      - constructor. repeat split; try reflexivity. exact ABE.
      - exact LO.
      - clear - HI; try acb; lia.
      - constructor. exact SPA.
      - constructor. exact SPT.
      - exact SZ.
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
      - exact QC1m.
      - exact QC2m.
      - exact QC3m.
      - exact QC4m.
      - exact QSTm.
      - exact CHUNKm.
      - exact SHKm.
      - exact TST2.
      - exact UNW2.
      - exact DEP2. }
    cbv beta. intros msF3 mo3 OK3 SBM3 _ PO3.
    destruct PO3 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & j0' & j1' & j2' & j3' & b1 & m3 & VIS3 & MU3 & WM3 & MI3 & ST3 &
                    QC1' & QC3' & QC4' & QST' & HDR & B1 & LEFT & FILL & SLACK & SHA & TST' & DEP').
    rewrite ?unsigned_lit in MU3 by (clear - SPR HI BND; try acb; lia). rewrite ?unsigned_lit in ST3 by (clear - SPR HI BND; try acb; lia).
    (* [comment removed for export] *)
    pose proof RQ as (RQ1 & RQ2 & RQ3 & RQ4 & RQ5 & RQ6 & RQ7 & RQ8).
    assert (MN : 1 <= Z.min size 4096 <= size) by (clear - SZ; try acb; lia).
    destruct (stk_split asegs _ _ (U + size) _ SLACK ltac:(hci; clear K; subst U; clear - MN RQ6 CS2 RQ5; try acb; lia)) as [SL SLACK2].
    destruct (stk_cells _ _ _ SL ltac:(hci; clear - MN; try acb; lia)) as [junk J].
    assert (LJ0 : length junk = Z.to_nat (U + size - (U + Z.min size 4096))) by (destruct J as [[[L _] _] _]; exact L).
    apply u8arr_of_rw_cells in J.
    assert (FL : Z.of_nat (length (repeat (b8 190) (Z.to_nat (Z.min size 4096)))) = Z.min size 4096) by (rewrite repeat_length; clear - MN; try acb; lia).
    assert (NEWJ : u8arr asegs m3 U (repeat (b8 190) (Z.to_nat (Z.min size 4096)) ++ junk)).
    { apply (proj2 (AsDepotInv.u8arr_app asegs m3 U _ _)). split; [exact FILL|]. rewrite FL. exact J. }
    apply rw_cells_of_u8arr in NEWJ. rewrite length_app, repeat_length, LJ0 in NEWJ.
    replace (Z.to_nat (Z.min size 4096) + Z.to_nat (U + size - (U + Z.min size 4096)))%nat with (Z.to_nat size) in NEWJ by (clear - MN; try acb; lia).
    clear SL J FL FILL.
    set (junk2 := repeat (b8 190) (Z.to_nat (Z.min size 4096)) ++ junk) in NEWJ.
    assert (LJ : length junk2 = Z.to_nat size) by (destruct NEWJ as [[[L _] _] _]; exact L).
    (* [comment removed for export] *)
    assert (HR2 : ARHEAP sR LB mR) by (destruct HR as (_ & ND & EQ); split; [exact R2| split; [exact ND| exact EQ]]).
    assert (DPL2 : depot_placed sR d) by exact DPL.
    assert (CHIN0R : In och (chunk_list (a_st sR))) by exact CHIN0.
    assert (ZF : forall a, ch_lo och <= a < ch_end och -> ~ (AB <= a < AB + csz)).
    { intros a Ha. pose proof (AG_ReallocF2.Z_REC ra sp s0 mR sR LB d lo size CH HR2 DPL2 LO HI SZ HIT2 och a CHIN0R Ha) as Z.
      cbn [outside a_thr a_st] in Z. fold st2 in Z. rewrite PCc in Z. cbn [pc_chunks refill_pc] in Z. fold n fl1 in Z. fold chunks2 in Z. fold cp in Z. fold AB in Z. fold rz needed c csz in Z.
      exact (proj1 (proj2 (proj2 (proj2 Z)))). }
    assert (SEP0 : P0 + old <= U - 16 \/ U + size <= P0 - 16).
    { pose proof (ZF AB) as Z1'. pose proof (ZF (ch_lo och)) as Z2'. clear K. subst U.
      clear - Z1' Z2' CG1 CG2 CG4 CG5 CG6 LO0 CE0 RU8 RQ5 RQ6 CS1 CS2 O1 SZ.
      destruct (Z.lt_ge_cases AB (ch_end och)) as [L1|G1]; [| left; lia].
      destruct (Z.lt_ge_cases (ch_lo och) (AB + csz)) as [L2|G2]; [| right; lia].
      exfalso. destruct (Z.le_gt_cases (ch_lo och) AB) as [L3|G3]; [apply Z1'; lia| apply Z2'; lia]. }
    (* [comment removed for export] *)
    assert (SHB1' : 0x2008fff7000 <= sh AB /\ sh AB + csz8 <= 0x10007fff8000) by (clear - BBA CS4; try acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    assert (K3 : (aceil <= lo /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil /\ sb <= AB /\ AB + csz <= sb + 137438953472
                 /\ 1 <= c < 32 /\ P = TH + 208 + 80 * c /\ 1 <= n <= 16 /\ 8 * csz8 = csz /\ 32 <= csz
                 /\ (TH + 4096 <= 65536 \/ (12599296 <= TH /\ TH + 4096 <= 2147446784) \/ 17594333495296 <= TH)
                 /\ 0x2008fff7000 <= sh AB /\ sh AB + csz8 <= 0x10007fff8000
                 /\ (TH + 4096 <= sb \/ sb + 137438953472 + 4096 <= TH))
                 /\ (12599296 <= d_nb d /\ d_nb d + 16 * 65536 <= aceil /\ 12599296 <= d_sb d /\ d_sb d + 8 * 131072 <= aceil)
                 /\ (AB + 16 <= U /\ U + size <= AB + csz /\ 1 <= size /\ 1 <= old /\ lo + 3072 <= bv_unsigned sp)).
    { split; [| split; [clear - BND; lia| clear K; subst U; clear - RQ5 RQ6 CS2 SZ O1 HI; lia]].
      clear - BND ABlo ABhi HC NR CS4 CS1 BT SHB1' BDJ1. unfold P, CA. repeat match goal with |- _ /\ _ => split end; try tauto; lia. }
    Ltac djK2 K := cbn [disjoint_from cells_size csize length Nat.add Nat.mul depot_W app]; unfold AIAINIT, AIAINST; clear - K; first [lia | nia].
    Ltac trX H MU WM K := eapply rw_cells_transport in H; [| exact MU| exact WM| djK2 K].
    (* [comment removed for export] *)
    trX MCP2 MU3 WM3 K3.
    pose proof AEN2 as E'. open_env E'.
    clear Etsdi Etp Etsd Ectx Elsan Egot2 Ethr Etid Einit Eafl Ecan Eshb Ehme Ethresh Erms Efill Epart Ehooks Einst1 Einst2.
    do 9 (apply (proj1 (rw_cells_app asegs _ _ [_] _)) in Egot; apply proj2 in Egot).
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in Egot. destruct Egot as [GOTM _].
    lazymatch type of GOTM with rw_cells ?sg ?mm ?a ?cs => let a' := eval vm_compute in a in change (rw_cells sg mm a cs) with (rw_cells sg mm a' cs) in GOTM end.
    trX GOTM MU3 WM3 K3.
    (* [comment removed for export] *)
    pose proof (munch_agree _ _ _ MU3) as AG3.
    assert (ZT3 : forall a, ch_lo och <= a < ch_end och -> outside ((lo, bv_unsigned sp + -2208) :: (P, P + 4) :: (CA + 2576, CA + 2584) :: (AB, AB + csz) :: (sh AB, sh AB + csz8) :: (TH + 2800, TH + 3168) :: depot_W d) a).
    { intros a Ha. pose proof (ZF a Ha) as Fa. rewrite LO0 in Ha. unfold kSpaceSize in CS0b. pose proof GD as (GD1 & GD2 & GD3 & GD4).
      cbn [outside depot_W app]. clear - Ha Fa CS0a CS0b CE0 BND BDJ1 SHB1' GD3 GD4 LO. unfold P, CA.
      repeat split; try exact I; try (clear GD3 GD4 BDJ1; lia); lia. }
    assert (HDR3 : rw_cells asegs m3 (P0 + -16) [C1 (b8 2); C1 (b8 b1o); C2 (wz 0); C4 (wz old); C8 (wz actxo)]).
    { eapply (rw_cells_transport_pt _ m2 m3 AG3 WM3); [exact HDR2|]. cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add length].
      intros a Ha. apply ZT3. clear - Ha CG1 CG2 CG4 LO0 RU8. lia. }
    assert (BLK3 : rw_cells asegs m3 P0 [CB (Z.to_nat old) bs]).
    { eapply (rw_cells_transport_pt _ m2 m3 AG3 WM3); [exact BLK2|]. cbn [cells_size csize Nat.add Nat.mul]. rewrite Nat.add_0_r, Z2Nat.id by (clear - O1; lia).
      intros a Ha. apply ZT3. clear - Ha CG1 CG2 CG4 LO0 RU8. lia. }
    assert (LBS : length bs = Z.to_nat old) by (destruct BLK0 as [[[L _] _] _]; exact L).
    (* [comment removed for export] *)
    change (ret_pc (Z_to_bv 64 1669500)) with (ret_pc (Z_to_bv 64 1669500)) in VIS3. rewrite (ret_pc_even 1669500) in VIS3 by (clear; lia).
    eapply (evt_sreach_lazy_at asegs L2 S2 (a_Zr s) _ msF3 _ mo3 Q OK3 VIS3).
    { eapply (realloc_mid (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0' t1' t2' (Z_to_bv 64 (bv_unsigned sp + -2136)) (wz P0) a1' a2' a3' a4' a5' a6' a7'
                cfu (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (bv_unsigned sp + -89)) s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m3
                U P0 size old bs junk2 (b8 b1o) (wz actxo)).
      - reflexivity.
      - unfold AIMG_TOP. clear - K3. try acb. lia.
      - unfold AIMG_TOP. clear - P0R. lia.
      - clear - SZ SZB. lia.
      - clear - O1 OLDSZ. lia.
      - exact SEP0.
      - exact LBS.
      - exact LJ.
      - exact MI3.
      - exact MCP2.
      - exact GOTM.
      - exact HDR3.
      - exact BLK3.
      - exact NEWJ. }
    cbv beta. intros msF4 mo4 OK4 SBM4 _ PO4. destruct PO4 as (u0 & u1 & u2 & u6 & u7 & u3 & u4 & u5 & u8 & m4 & VIS4 & MU4 & WM4 & MI4 & NEWB).
    (* [comment removed for export] *)
    assert (TK : chunks2 = cp :: tl chunks2).
    { assert (TK0 : forall l : list Z, n = zlen l -> l = hd 0 l :: tl l)
        by (intros [|y l] H; [exfalso; unfold zlen in H; cbn in H; clear - H NR; try acb; lia| reflexivity]).
      exact (TK0 chunks2 CC). }
    assert (LENC3 : 4 * Z.of_nat (length (wlist (rev (tl chunks2)))) = 4 * (n - 1)).
    { unfold wlist. rewrite length_map, length_rev. pose proof CC as CC'. rewrite TK in CC'. unfold zlen in CC'. cbn [length] in CC'. clear - CC'. lia. }
    trX QC1' MU4 WM4 K3.
    eapply u32arr_transport in QC3'; [| exact MU4| exact WM4| rewrite LENC3; djK2 K3].
    eapply stk_transport_disjoint in QC4'; [| exact MU4| exact WM4| djK2 K3].
    trX QST' MU4 WM4 K3. trX HDR MU4 WM4 K3.
    assert (LEFT4 : rz = 16 \/ (rw_cells asegs m4 AB [C8 (wz kAllocBegMagic); C8 (wz (U + -16))] /\ stk asegs m4 (AB + 16) (U + -16))).
    { destruct LEFT as [L|[Lf1 Lf2]]; [left; exact L| right]. split.
      - trX Lf1 MU4 WM4 K3. exact Lf1.
      - eapply stk_transport_disjoint in Lf2; [exact Lf2| exact MU4| exact WM4| djK2 K3]. }
    clear LEFT.
    eapply stk_transport_disjoint in SLACK2; [| exact MU4| exact WM4| djK2 K3].
    assert (LSH : Z.of_nat (length (alloc_shadow rz size csz)) <= csz8).
    { unfold alloc_shadow. rewrite length_app, length_app, !repeat_length, !Nat2Z.inj_add, shadow_of_length by (clear - SZ; try acb; lia).
      pose proof (rz_size_facts size) as (_ & RZ16 & _). fold rz in RZ16.
      clear - RQ5 RQ6 CS2 CS3 CS4 SZ RZ16 MN. unfold nsh, round_up in *. Z.div_mod_to_equations. lia. }
    eapply u8arr_transport in SHA; [| exact MU4| exact WM4| cbn [disjoint_from]; split; [left; clear - LSH K3; lia| exact I]].
    eapply stk_transport_disjoint in TST'; [| exact MU4| exact WM4| djK2 K3].
    assert (DEP4 : DEPOT asegs d' m4).
    { eapply DEPOT_transport; [exact DEP'| exact MU4| exact WM4|]. unfold depot_avoid, avoids. unfold d'. rewrite ?d_nb_put, ?d_sb_put.
      pose proof GD as (_ & _ & G3' & G4').
      repeat split; (apply Forall_cons; [cbn beta iota delta [fst snd]| apply Forall_nil]); clear - K3 G3' G4'; lia. }
    eapply stk_transport_disjoint in ST3; [| exact MU4| exact WM4| djK2 K3].
    (* [comment removed for export] *)
    pose proof (conj K3 GD) as K3U. trX UNW2 MU3 WM3 K3U. trX UNW2 MU4 WM4 K3.   (* [comment removed for export] *)
    trX FLG2 MU3 WM3 K3. trX FLG2 MU4 WM4 K3.
    pose proof (ia_if_transport true _ _ _ IA2 MU3 WM3 ltac:(djK2 K3U)) as IA3. pose proof (ia_if_transport true _ _ _ IA3 MU4 WM4 ltac:(djK2 K3)) as IA4.
    change (ia_after m4) in IA4. clear IA3.
    trX FRR2 MU3 WM3 K3. trX FRR2 MU4 WM4 K3. trX FRA2 MU3 WM3 K3. trX FRA2 MU4 WM4 K3. trX FP2 MU3 WM3 K3. trX FP2 MU4 WM4 K3.
    trX Eso MU3 WM3 K3. trX Eso MU4 WM4 K3. trX TFB2 MU3 WM3 K3. trX TFB2 MU4 WM4 K3. trX F82 MU3 WM3 K3. trX F82 MU4 WM4 K3.
    assert (LTB : (length (map wz T ++ rest) = 255)%nat) by (rewrite length_app, length_map, LR; clear - NRT; lia).
    eapply u64arr_transport in Etr; [| exact MU3| exact WM3| rewrite LTB; djK2 K3]. eapply u64arr_transport in Etr; [| exact MU4| exact WM4| rewrite LTB; djK2 K3].
    (* [comment removed for export] *)
    assert (BLK4 : rw_cells asegs m4 P0 [CB (Z.to_nat old) bs]).
    { eapply rw_cells_transport in BLK3; [exact BLK3| exact MU4| exact WM4|]. cbn [disjoint_from cells_size csize Nat.add Nat.mul]. rewrite Nat.add_0_r, Z2Nat.id by (clear - O1; lia).
      split; [clear - SEP0 MN O1; lia| exact I]. }
    assert (SPm : forall x, lo <= x < bv_unsigned sp + -2208 -> lo <= x < bv_unsigned sp) by (intros; lia).
    assert (THm : forall x, TH + 2800 <= x < TH + 3168 -> TH + 2800 <= x < TH + 3169) by (intros; lia).
    assert (SPm2 : forall x, lo <= x < bv_unsigned sp + -2384 -> lo <= x < bv_unsigned sp) by (intros; lia).
    assert (ZT3sh : forall a, sh P0 <= a < sh P0 + nsh old -> outside ((lo, bv_unsigned sp + -2208) :: (P, P + 4) :: (CA + 2576, CA + 2584) :: (AB, AB + csz) :: (sh AB, sh AB + csz8) :: (TH + 2800, TH + 3168) :: depot_W d) a).
    { intros a Ha.
      pose proof (AG_ReallocF2.Z_RECSH ra sp s0 mR sR LB d lo size CH HR2 DPL2 LO HI SZ HIT2 och P0 (nsh old) a CHIN0R
                    ltac:(hci; clear - CG1 CG2 LO0; lia) ltac:(hci; clear - CG2 CG4 CG6; lia) ltac:(hci; clear - O4; Z.div_mod_to_equations; lia) ltac:(hci; clear - RU8; lia) Ha) as Z.
      cbn [outside a_thr a_st] in Z. fold st2 in Z. rewrite PCc in Z. cbn [pc_chunks refill_pc] in Z. fold n fl1 in Z. fold chunks2 in Z. fold cp in Z. fold AB in Z. fold rz needed c csz in Z. fold csz8 in Z.
      cbn [outside depot_W app] in Z |- *. destruct Z as (z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & zD).
      exact (conj (fun C => z1 (SPm a C)) (conj z2 (conj z3 (conj z4 (conj z5 (conj (fun C => z6 (THm a C)) zD)))))). }
    assert (SHB3 : SHAD m3 P0 sbs) by (eapply (SHAD_transport_pt _ m2 m3 AG3 WM3); [exact SHB2| rewrite SHB0l; exact ZT3sh]).
    assert (SHB4 : SHAD m4 P0 sbs).
    { eapply (SHAD_transport_pt _ m3 m4 (munch_agree _ _ _ MU4) WM4); [exact SHB3|]. rewrite SHB0l. intros a Ha. cbn [outside].
      assert (SR0 : 0x7fff8000 + 12599312 / 8 <= sh P0 /\ sh P0 + nsh old <= 0x10007fff8000) by (clear - K0 RU8 O3; try acb; unfold sh, ASHADOW_BASE, nsh, round_up in *; Z.div_mod_to_equations; lia).
      split; [clear - Ha SR0 K3; lia| exact I]. }
    (* [comment removed for export] *)
    assert (MU_R4 : munch ((lo, bv_unsigned sp) :: (P, P + 4) :: (CA + 2576, CA + 2584) :: (AB, AB + csz) :: (sh AB, sh AB + csz8)
                           :: (TH + 2800, TH + 3169) :: (AIAINIT, AIAINIT + 4) :: (AIAINST, AIAINST + 0x81030) :: depot_W d) mR m4).
    { intros x Hx. cbn [outside depot_W app] in Hx. destruct Hx as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & VD1 & VD2 & VD3 & VD4 & _).
      transitivity (m3 x); [apply MU4; cbn [outside]; split; [intros C; apply V4; clear - C K3; lia| exact I]|].
      transitivity (m2 x); [apply MU3; cbn [outside depot_W app]; repeat split; try exact I; first [assumption | exact (fun C => V1 (SPm _ C)) | exact (fun C => V6 (THm _ C))]|].
      pose proof (bv_unsigned_in_range _ x) as XR. change (bv_modulus 64) with (2^64) in XR.
      pose proof (AGoR (bv_unsigned x)) as E. unfold wa in E. rewrite Z_to_bv_bv_unsigned in E. symmetry. apply E; [| exact XR].
      subst Wo. cbn [outside]. repeat split; try exact I; assumption. }
    assert (WM24 : wmono asegs m2 m4) by (eapply wmono_trans; [exact WM3| exact WM4]).
    assert (WM04 : wmono asegs m m4) by (eapply wmono_trans; [exact WM02| exact WM24]).
    assert (WM_R4 : wmono asegs mR m4) by exact (chim_wmono_out Wo m m2 m4 WM04 WM24).
    (* [comment removed for export] *)
    pose proof (AG_ReallocF2.arheap_after ra sp s0 mR sR LB d lo size CH HR2 DPL2 LO HI SZ HIT2 m4 j0' j1' j2' j3' b1) as AH.
    pose proof (AG_ReallocF2.new_block ra sp s0 mR sR LB d lo size CH HR2 DPL2 LO HI SZ HIT2 DCAP m4) as NB.
    cbn [a_st a_thr a_ctx a_fsb a_L a_S a_Zr a_AL a_top a_bot] in AH, NB. fold st TH rz needed in AH, NB. fold c in AH, NB. fold st2 csz in AH, NB. fold csz8 in AH.
    rewrite PCc in AH, NB. cbn [pc_count pc_chunks refill_pc] in AH, NB. fold n fl1 in AH, NB. fold chunks2 in AH, NB. fold cp in AH, NB. fold AB in AH, NB. fold U in AH, NB.
    specialize (AH MU_R4 WM_R4 QC1' QC3' QC4' QST' HDR B1 LEFT4 _ NEWB SLACK2 SHA TST' UNW2 FLG2 IA4).
    specialize (NB _ NEWB SHA).
    rewrite RQ4 in AH. fold ch in AH. fold stH in AH. fold st3 in AH.
    apply K. unfold realloc_cold_gpost.
    exists u0, u1, u2, u6, u7, u3, u4, u5, u8, cfu. exists jk, jr1, jr2, junk2, rest, m4.
    split; [exact OK4|]. split; [exact VIS4|]. split; [exact AH|].
    split.
    { (* [comment removed for export] *)
      intros x Hx. cbn [a_S] in Hx. unfold S2 in Hx. rewrite !in_rangesb_app in Hx.
      apply Bool.orb_true_iff in Hx. destruct Hx as [Hx|Hx]; [| apply Bool.orb_true_iff in Hx; destruct Hx as [Hx|Hx]].
      - apply in_rangesb_if in Hx.
        apply in_window1 in Hx; [| clear - SHB; try acb; lia| clear - BR2; try acb; Z.div_mod_to_equations; lia| clear - SHB; try acb; lia].
        apply (poisoned_visible m2 m4 _ _ _ x POIf WM24). rewrite Z2Nat.id by (clear - BR2; try acb; Z.div_mod_to_equations; lia). exact Hx.
      - apply in_rangesb_if in Hx.
        apply in_window1 in Hx; [| clear - SHB; try acb; lia| clear - BR2; try acb; Z.div_mod_to_equations; lia| clear - SHB; try acb; lia].
        apply (poisoned_visible m2 m4 _ _ _ x POIu WM24). rewrite Z2Nat.id by (clear - BR2; try acb; Z.div_mod_to_equations; lia). exact Hx.
      - apply WM04. exact (AWV x Hx). }
    split.
    { (* [comment removed for export] *)
      apply (flagsx_transport _ mR m4 (munch_agree _ _ _ MU_R4) WM_R4); [| exact FX2]. intros a Ha N1 N2 N3 N4.
      cbn [outside depot_W app]. unfold AIMG_TOP in Ha. clear - Ha N1 N2 N3 N4 K3. repeat split; try exact I; try assumption; lia. }
    split; [exact (amodelx_hit sR mo4 c n (tl chunks2) ch (AMODELX_mat sR mo3 mo4 (AMODELX_mat sR mo2 mo3 AMX2 SBM3) SBM4))|].
    split; [exact (nonvm_same_trans _ _ _ (nonvm_same_mat _ _ SBM1) (nonvm_same_trans _ _ _ NVS (nonvm_same_trans _ _ _ (nonvm_same_mat _ _ SBM3) (nonvm_same_mat _ _ SBM4))))|].
    split; [exact DEP4|].
    split; [unfold depot_placed; unfold d'; rewrite d_nb_put, d_sb_put; exact DPL|].
    split.
    { unfold depot_cov. unfold d'. rewrite d_nb_put, d_sb_put. intros x Hx.
      rewrite (same_but_materialized_vmmaps mo3 mo4 SBM4), (same_but_materialized_vmmaps mo2 mo3 SBM3), VMM, (same_but_materialized_vmmaps mo mo1 SBM1). exact (DCOV x Hx). }
    split; [exact MI4|]. split; [exact ST3|].
    split.
    { (* [comment removed for export] *)
      intros x Hx. unfold rc_W in Hx. apply outside_app in Hx. destruct Hx as [HWr HWt].
      unfold Wt in HWt. cbn [outside depot_W app] in HWt. destruct HWt as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & VD1 & VD2 & VD3 & VD4 & _).
      unfold Wr in HWr. cbn [outside] in HWr. destruct HWr as (Y1' & Y2' & Y3' & Y4' & Y5' & Y6' & YR).
      transitivity (m3 x); [apply MU4; cbn [outside]; split; [intros C; apply V4; clear - C K3; lia| exact I]|].
      transitivity (m2 x); [apply MU3; cbn [outside depot_W app]; repeat split; try exact I; first [assumption | exact (fun C => V1 (SPm _ C)) | exact (fun C => V6 (THm _ C))]|].
      transitivity (m1 x); [apply MU2; unfold rf_W; unfold rf_W in YR; cbn [outside] in YR |- *; split; [exact (fun C => Y1' (SPm2 _ C))| exact YR]|].
      apply MU1. cbn [outside]. repeat split; try exact I; assumption. }
    split; [exact WM04|].
    split. { apply avmx_same; [| reflexivity]. rewrite (same_but_materialized_vmmaps mo3 mo4 SBM4), (same_but_materialized_vmmaps mo2 mo3 SBM3), VMM, (same_but_materialized_vmmaps mo mo1 SBM1). reflexivity. }
    split; [exact (proj1 NB)|]. split; [exact LJ|]. split; [exact (proj2 NB)|].
    split.
    { (* [comment removed for export] *)
      intros kaddr.
      assert (WF2 : WF st2) by exact (WF_refill st c WFs HC MISS ROOM).
      assert (CV2 : carved st2 c AB).
      { apply carved_cache; [exact WF2| unfold kNumClasses; clear - HC; try acb; lia|]. unfold st2. rewrite PCc. change (pc_chunks (refill_pc st c)) with chunks2. rewrite TK. left. reflexivity. }
      pose proof CV2 as (_ & _ & CVa & CVm & CVle). rewrite region_beg_eq in CVa, CVm, CVle. change (as_space_beg st2) with sb in CVa, CVm, CVle. fold csz in CVm, CVle.
      pose proof (rz_size_facts size) as (_ & RZ16 & RZC). fold rz in RZ16, RZC. pose proof SZ as SZ2. unfold kMaxSize in SZ2.
      assert (UM8 : U mod 8 = 0).
      { unfold U. destruct BND as (_ & _ & _ & _ & _ & SB64 & _). clear - CVm RZ16 SB64 CS3 CS1.
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
      - exists st'', ev. rewrite RQ1 in EQ. rewrite RQ1, RQ4 in SB. split; [exact EQ| exact SB]. }
    repeat match goal with |- _ /\ _ => split end; try assumption.
    all: try (clear - NRT; lia).
  Qed.
End ReallocColdGlue.
