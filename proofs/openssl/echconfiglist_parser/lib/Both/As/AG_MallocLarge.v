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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel AllocSim MmapSim SReach LazyRestrict LazyLedger LazySR LazyNodes RefNodes.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocBudget AllocRep AllocRepFacts AllocRepFacts2 AllocRepX AsAtomics AsDepotInv AsDepotHash AsDepotPut AsUnwind AllocWalkKit F_memset AG_Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_Leaves AW_PoisonShadow AW_DepotFrame AW_AllocBase AW_MallocBase AW_LargeAlloc1 AW_SysconfPg
     AW_AllocSec1 AW_AllocSec2 SecLazy SecLazy2 SecGap AS_LargeAlloc AS_AllocSec1 AS_AllocSec AS_MallocLarge1 AS_MallocLarge
     AG_MallocModel AG_WFHit AG_Malloc AG_Malloc2 AG_LargeModel AG_MallocLarge1 AG_MallocLarge2 AG_MallocLarge3 AllocTacX AG_WriteSet.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section MallocLargeGlue.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo size : Z) (CH : list (Z * Z)).
  Let st := a_st s.
  Let TH := a_thr s.
  Let sb := a_sb s.
  Let pa := a_pa s.
  Let CTX := a_ctx s.
  Let r := compute_req size.
  Let needed := rq_needed r.
  Let msz := round_up needed kPageSize + kPageSize.
  Let nch := zlen (as_sec st).
  Let nres := as_n_reserved st.
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CH.
  Let T := utrace 0x1bf41c (bv_unsigned sp) (a_top s) (a_bot s) 30 CHI.
  Let nT := Z.of_nat (length T).
  Let d' := d_put d (depot_hash T) nT.
  Let Wsh (a : Z) : word * word := (wz (sh a), wz (msz / 8)).
  Let L2 := lg_L (a_L s) pa nres nch.   (* [comment removed for export] *)
  Let sx (a : Z) := mkAst (large_state st a size) (a_thr s) (a_ctx s) (a_fsb s) L2 (Wsh a :: a_S s) (a_Zr s) (a_AL s - lg_cost msz) (a_top s) (a_bot s).
  Let U (a : Z) := a + kPageSize + 2048.

  Hypothesis HR : ARHEAP s LB m.
  Hypothesis AX : awin_vis s m /\ flagsx_rep m.
  Hypothesis AMX : AMODELX s mo.
  Hypothesis DEP : DEPOT asegs d m.
  Hypothesis DPL : depot_placed s d.
  Hypothesis DCOV : depot_cov d mo.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 2912 <= bv_unsigned sp.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis SZ : 64512 < size < 2^32.
  Hypothesis TP : tp = wz ATP.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + 31 <= 131072.
  Hypothesis FCH : goodframe (a_bot s) (bv_unsigned sp) (a_top s) = true -> goodframe (bv_unsigned sp) (bv_unsigned s0) (a_top s) = true ->
                   bv_unsigned sp + 16 <= bv_unsigned s0 /\ frame_chain asegs m (a_top s) (bv_unsigned s0) CH.
  Hypothesis Ha0 : a0 = wz size.
  (* [comment removed for export] *)
  Hypothesis ALLOW : lg_cost msz <= a_AL s.
  Hypothesis PNN : pusage st <= B_PRIM.        (* [comment removed for export] *)
  Hypothesis AGP : AGAP msz mo.
  (* [comment removed for export] *)
  Hypothesis NSEC : nch + 1 <= kChunksBlockCount.
  (* [comment removed for export] *)
  Hypothesis DFS : disj (a_fsb s) AFS_SIZE (d_nb d) (16 * 65536) /\ disj (a_fsb s) AFS_SIZE (d_sb d) (8 * 131072).
  Hypothesis OK : lzok asegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo).
  Hypothesis VISE : restrict (a_L s) (a_S s) msF
    = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1bf354) fc None m (seg_rom asegs).

  (* [comment removed for export] *)
  Definition malloc_large_gpost (msF' : machine_state) (mo' : Model) : Prop :=
    exists (a : Z) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
       aapp a msz /\ a + msz <= aceil /\ a mod 4096 = 0    (* [comment removed for export] *)
    /\ lzok asegs (a_L (sx a)) (a_S (sx a)) (a_Zr (sx a)) (mkCfg msF' mo')
    /\ restrict (a_L (sx a)) (a_S (sx a)) msF'
       = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz (U a)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ ARHEAP (sx a) ((U a, size) :: LB) m' /\ awin_vis (sx a) m' /\ flagsx_rep m' /\ AMODELX (sx a) mo' /\ nonvm_same mo mo'   (* [comment removed for export] *)
    /\ DEPOT asegs d' m' /\ depot_placed (sx a) d' /\ depot_cov d' mo'
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ munch (ml_W lo sp a msz pa nch nres TH d) m m' /\ wmono asegs m m' /\ amframe s LB (bv_unsigned sp) m m'
    /\ acompl s (sx a) d lo (bv_unsigned sp) m m' /\ avmx s (sx a) mo mo'                 (* [comment removed for export] *)
    /\ (exists junk, rw_cells asegs m' (U a) [CB (Z.to_nat size) junk]) /\ addressable m' (U a) size
    /\ (exists st'' ev, am_malloc_k st size a = Some (U a, st'', ev) /\ same_but_shadow st'' (large_state st a size)).

  Theorem malloc_arep_large :
    (forall msF' mo', malloc_large_gpost msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF mo).
  Proof.
    intros K.
    pose proof (proj1 HR) as R. pose proof (proj1 R) as OKs. destruct OKs as [PL WFs].
    pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    pose proof DPL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    destruct (large_cells_of_arep s m R) as (INST64 & NRES & SST & MTX & GST & TST & UNW & PA & PAJ & NB1 & NB2).
    pose proof (senv_of_arep s m R) as SEN. destruct AX as [AWV FXR].   (* [comment removed for export] *)
    pose proof (ienv_of_arep s m R) as IEN. rewrite <- TP in IEN, SEN.
    destruct AMX as [AM AK]. pose proof (ak_hsm_full s mo AK) as HSMF. pose proof AM as AM'. destruct AM' as (AIL & ASV & AB). destruct AIL as (_ & _ & _ & NOV & NW & NWA). destruct AB as [AB0 AB1].
    pose proof (large_req size SZ) as RQ. fold r in RQ. destruct RQ as (RS & RZ & RR & ND & RP & RN & TB & BIG). fold needed in ND, BIG.
    assert (MSZ : needed + 4096 <= msz /\ msz < needed + 8192 /\ msz mod 4096 = 0 /\ size + 8 <= needed - 4088 /\ needed <= size + 4104).
    { unfold msz. rewrite ND. unfold round_up, kPageSize. clear - SZ; try acb. Z.div_mod_to_equations. nia. }
    assert (BND : 4096 <= TH /\ TH + 4096 <= aceil /\ TH mod 4096 = 0 /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil
            /\ 12599296 <= CTX /\ CTX + 160 <= aceil /\ 12599296 <= pa /\ pa + 8388608 <= aceil /\ pa mod 4096 = 0
            /\ 12599296 <= d_nb d /\ d_nb d + 16 * 65536 <= aceil /\ 12599296 <= d_sb d /\ d_sb d + 8 * 131072 <= aceil
            /\ 4096 <= a_top s <= 2^47 /\ 0 <= a_bot s < a_top s /\ aceil <= lo).   (* [comment removed for export] *)
    { pose proof (akobj_env _ _ T2 ltac:(unfold kPageSize; clear; lia)) as T2e. pose proof (aapp_env _ _ P2 ltac:(unfold kPtrArrayReserve; clear; lia)) as P2e.
      pose proof (aapp_env _ _ X2 ltac:(clear; lia)) as X2e. pose proof (aapp_env _ _ G10 ltac:(clear; lia)) as G10e. pose proof (aapp_env _ _ G12 ltac:(clear; lia)) as G12e.
      clear - S1 S2 S3 P1 P2e P3 T1 T2e T3 X1 X2e X3 TCX G10e G11 G12e G13 LO; try acb. unfold TH, sb, pa, CTX. unfold a_sb in *.
      acb. unfold AHI_LO, kSpaceSize, kPageSize, kPtrArrayReserve in *. repeat split; (first [clear - T2e T1 S2 S3 X2e P2e P1 G10e G12e TCX LO; lia | lia]). }
    (* [comment removed for export] *)
    eapply (malloc_large_sreach (a_L s) (a_S s) (a_Zr s) msF mo Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m lo size needed msz d ATSD CTX TH (a_top s) (a_bot s) sb pa nres nch CH (map sc_map_beg (as_sec st))).
    { constructor. split; [exact ND| reflexivity]. }
    { exact LO. } { exact HI. } { constructor. exact SPA. } { constructor. exact SPT. } { exact SZ. }
    { constructor. rewrite TP. unfold wz, ATP, AIMG_TOP. rewrite unsigned_lit by (clear; lia). clear; lia. }
    { constructor. unfold ATSD, AIMG_TOP. unfold kPageSize in T2. clear - BND T2 X2; try acb.   (* [comment removed for export] *)
      repeat match goal with |- _ /\ _ => split end; first [assumption | lia | Z.div_mod_to_equations; lia]. }
    { constructor. unfold disj, kSpaceSize, kPageSize in *. clear - D2 D3 TCX; try acb. subst TH sb CTX. lia. }
    { constructor. unfold disj, kSpaceSize, kPageSize, kPtrArrayReserve in *. clear - D4 D5 TCX; try acb. subst TH pa CTX. lia. }
    { constructor. unfold disj, kSpaceSize, kPageSize, kPtrArrayReserve in *. clear - G1 G2 G3 G4 G5 G6 G10 G12 BND; try acb. subst TH sb CTX.
      repeat match goal with |- _ /\ _ => split end; first [assumption | lia]. }
    { constructor. unfold disj, kPtrArrayReserve in *. clear - G7 G8; try acb. subst pa. lia. }
    { constructor. acb. unfold AHI_LO, kSpaceSize. clear - BND; try acb. lia. }
    { constructor. clear - BND; try acb. lia. }
    { all: (clear - G11 G13 BND; try acb; lia). }
    { exact DCAP. }
    { split; [exact P2| split; [exact P3| unfold kPageSize in P1; exact P1]]. }   (* [comment removed for export] *)
    { unfold kChunksBlockCount in NB2. clear - NB1 NB2; try acb. subst nch nres st. lia. }
    { unfold kChunksBlockCount in NB2. clear - NB2; try acb. subst nres st. destruct NB2 as [E|E]; rewrite E; [exists 0| exists 32]; reflexivity. }
    { unfold nch, zlen. rewrite length_map. reflexivity. }
    { exact FCH. } { exact Ha0. } { exact IEN. } { exact SEN. } { exact MI. } { exact ST. } { exact UNW. }
    { exact INST64. } { exact NRES. } { exact SST. } { exact MTX. } { exact GST. } { exact TST. } { exact PA. } { exact PAJ. } { exact DEP. }
    { exact NW. } { exact NWA. } { exact NOV. }
    { unfold aPhi, lg_cost, page_size in *. clear - AB0 AB1 ALLOW PNN; try acb. subst st. lia. }
    { (* [comment removed for export] *)
      pose proof (ak_atop s mo AK) as AT.
      exact (gap_witness_fit_top _ AHI_LO msz ltac:(clear - MSZ SZ; lia) ltac:(unfold AHI_LO; clear; lia) ltac:(clear; reflexivity)
               ltac:(rewrite AT; hcb; clear - HCEILB; lia) AGP). }
    { exact (ak_imgr s mo AK). } { exact (ak_shland s mo AK). }   (* [comment removed for export] *)
    { exact (ak_atop s mo AK). }
    { exact (ak_zrsh2 s mo AK). } { exact AWV. }   (* [comment removed for export] *)
    { intros x Hx. apply (ak_tmaps s mo AK). unfold kPageSize. exact Hx. }
    { exact (ak_cmaps s mo AK). } { exact (ak_pmaps s mo AK). }
    { intros x Hx. apply (ak_sbmaps s mo AK). unfold kPageSize. clear - Hx; try acb. subst sb. lia. }
    { intros x Hx. apply DCOV. left. exact Hx. } { intros x Hx. apply DCOV. right. exact Hx. }
    { intros E. clear - AK BND NB1 NB2 E; try acb. subst nch nres pa st. unfold kChunksBlockCount, kPtrArrayReserve in *.
      apply (ak_pamc s mo AK); unfold wz, kPtrArrayReserve; rewrite ?unsigned_lit by lia; lia. }
    { intros E. clear - AK BND NB1 NB2 E; try acb. subst nch nres pa st. unfold kChunksBlockCount in *. apply (ak_resf s mo AK). unfold wz, AIMG_TOP; rewrite unsigned_lit by lia; lia. }   (* [comment removed for export] *)
    { intros E x Hx. clear - AK BND NB1 NB2 Hx E; try acb. subst nch nres pa st. unfold kChunksBlockCount in *. apply (ak_zr_pa s mo AK). unfold kPtrArrayReserve. lia. }
    { exact OK. } { exact VISE. }
    (* [comment removed for export] *)
    cbv beta. intros msF' mo' P.
    destruct P as (a & y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & b1 & rest & m' & AHI & CE & AL & FREE & OK' & VIS' & MO' & MU' & WM' & MI' & ST' & AEN'
                 & UNW' & INST' & NRES' & SST' & MTX' & GST' & PA' & PAJ' & LHDR' & LHJ' & CH' & B1 & MAG' & MAGJ' & FILL' & SLK' & SHA' & SHU' & TST' & DEP').
    fold CHI T nT d' in AEN', CH', DEP'. fold CHI in AEN', CH', DEP'. fold T in AEN', CH', DEP'. fold nT in DEP'. fold d' in DEP'.
    pose proof (aapp_env _ _ AHI ltac:(clear - MSZ SZ; lia)) as [AHI' _]. pose proof CE as CE'. acb.   (* [comment removed for export] *)
    pose proof (aapp_lit _ _ AHI) as ALIT.
    assert (AR3 : aapp a msz /\ a + msz <= aceil /\ a mod 4096 = 0) by (exact (conj AHI (conj CE AL))).
    (* [comment removed for export] *)
    assert (PNEW : disj a msz sb (kSpaceSize + kPageSize) /\ disj a msz pa kPtrArrayReserve /\ disj a msz TH kPageSize /\ disj a msz CTX 160
                   /\ disj a msz (a_fsb s) AFS_SIZE /\ disj a msz (d_nb d) (16 * 65536) /\ disj a msz (d_sb d) (8 * 131072)
                   /\ (forall sc, In sc (as_sec st) -> disj a msz (sc_map_beg sc) (sc_map_size sc))).
    { unfold disj. pose proof (bv_unsigned_in_range _ sp) as SPR.
      assert (FS : 12599296 <= a_fsb s /\ a_fsb s + AFS_SIZE <= aceil) by (exact (aapp_env _ _ F1 ltac:(unfold AFS_SIZE; clear; lia))).
      unfold kSpaceSize, kPageSize, kPtrArrayReserve, AFS_SIZE in *.
      split; [apply (free_vs_mapped _ _ a msz sb (137438953472 + 4096) FREE ltac:(hci; lia) ltac:(hci; (first [clear - MSZ SZ; lia | lia])) ltac:(hci; (first [clear - AR3 ACEILB; lia | lia])) ltac:(hci; lia) ltac:(hci; (first [clear - ACEILB BND; lia | lia])) ltac:(hci; lia)); intros x Hx; apply (ak_sbmaps s mo AK); unfold kSpaceSize, kPageSize; clear - Hx; try acb; subst sb; lia|].
      split; [apply (free_vs_mapped _ _ a msz pa 8388608 FREE ltac:(hci; lia) ltac:(hci; (first [clear - MSZ SZ; lia | lia])) ltac:(hci; (first [clear - AR3 ACEILB; lia | lia])) ltac:(hci; lia) ltac:(hci; (first [clear - ACEILB BND; lia | lia])) ltac:(hci; lia)); intros x Hx; apply (ak_pmaps s mo AK); unfold kPtrArrayReserve; clear - Hx; try acb; subst pa; lia|].
      split; [apply (free_vs_mapped _ _ a msz TH 4096 FREE ltac:(hci; lia) ltac:(hci; (first [clear - MSZ SZ; lia | lia])) ltac:(hci; (first [clear - AR3 ACEILB; lia | lia])) ltac:(hci; lia) ltac:(hci; (first [clear - ACEILB BND; lia | lia])) ltac:(hci; lia)); intros x Hx; apply (ak_tmaps s mo AK); unfold kPageSize; clear - Hx; try acb; subst TH; lia|].
      split; [apply (free_vs_mapped _ _ a msz CTX 160 FREE ltac:(hci; lia) ltac:(hci; (first [clear - MSZ SZ; lia | lia])) ltac:(hci; (first [clear - AR3 ACEILB; lia | lia])) ltac:(hci; lia) ltac:(hci; (first [clear - ACEILB BND; lia | lia])) ltac:(hci; lia)); intros x Hx; apply (ak_cmaps s mo AK); clear - Hx; try acb; subst CTX; lia|].
      split; [apply (free_vs_mapped _ _ a msz (a_fsb s) 11571200 FREE ltac:(hci; lia) ltac:(hci; (first [clear - MSZ SZ; lia | lia])) ltac:(hci; (first [clear - AR3 ACEILB; lia | lia])) ltac:(hci; lia) ltac:(hci; (first [clear - FS ACEILB; lia | lia])) ltac:(hci; lia)); intros x Hx; apply (ak_fsmaps s mo AK); unfold AFS_SIZE; clear - Hx; try acb; lia|].
      split; [apply (free_vs_mapped _ _ a msz (d_nb d) (16 * 65536) FREE ltac:(hci; lia) ltac:(hci; (first [clear - MSZ SZ; lia | lia])) ltac:(hci; (first [clear - AR3 ACEILB; lia | lia])) ltac:(hci; lia) ltac:(hci; (first [clear - ACEILB BND; lia | lia])) ltac:(hci; lia)); intros x Hx; apply DCOV; left; exact Hx|].
      split; [apply (free_vs_mapped _ _ a msz (d_sb d) (8 * 131072) FREE ltac:(hci; lia) ltac:(hci; (first [clear - MSZ SZ; lia | lia])) ltac:(hci; (first [clear - AR3 ACEILB; lia | lia])) ltac:(hci; lia) ltac:(hci; (first [clear - ACEILB BND; lia | lia])) ltac:(hci; lia)); intros x Hx; apply DCOV; right; exact Hx|].
      intros sc Hin. pose proof (ak_secmaps s mo AK sc Hin) as IN. pose proof (SEC sc Hin) as (Q1 & Q2 & Q3 & Q4 & _).
      acb. apply aapp_env in Q2; [| unfold kPageSize in Q4; clear - Q4; lia].
      pose proof (region_free_In _ _ _ _ _ (region_free_app_r _ _ _ _ FREE) IN) as D. unfold wz in D. rewrite !unsigned_lit in D by (clear - AHI' CE' MSZ SZ Q2 Q3 Q4; try acb; lia).
      clear - D; try acb. lia. }
    pose proof (munch_agree _ _ _ MU') as AG'. 
    assert (NSEC' : nch = nres -> nres = 0) by (intros E; unfold kChunksBlockCount in NSEC, NB2; clear - E NSEC NB2; try acb; subst nch nres st; lia).
    apply K. unfold malloc_large_gpost.
    exists a, y0, y1, y2, ya1, ya2, ya3, ya4, ya5, ya6, ya7, y3, y4, y5, y6, m'.
    split; [exact AHI|]. split; [exact CE|]. split; [exact AL|]. split; [exact OK'|]. split; [unfold U, kPageSize; replace (a + 4096 + 2048) with (a + 6144) by (clear; lia); exact VIS'|].
    split.
    { (* [comment removed for export] *)
      eapply (arheap_after s m m' a size lo (bv_unsigned sp) d); [exact HR | exact DPL | exact SZ | exact AR3 | exact LO | exact PNEW | exact NSEC' | exact AG' | exact WM' | exact NRES' | exact SST' | exact MTX' | exact GST' | exact PA' | exact PAJ' | exact LHDR' | exact LHJ' | exact CH' | exact B1 | exact MAG' | exact MAGJ' | exact FILL' | exact SLK' | exact SHA' | exact SHU' | exact TST' | exact UNW'].
      all: match goal with |- ?g => idtac "AH:" g end. }
    split.
    { (* [comment removed for export] *)
      intros x Hx. cbn [a_S] in Hx. rewrite in_rangesb_cons in Hx. apply orb_true_iff in Hx. destruct Hx as [Hx|Hx].
      - apply (zin_W (sh a) (msz / 8)) in Hx; [| clear - AHI' CE' MSZ SZ; try acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia | clear - AHI' CE' MSZ SZ; try acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia | clear - AHI' CE' MSZ SZ; try acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia].
        assert (SHALL : u8arr asegs m' (sh a) (repeat (b8 250) 512 ++ sec_shadow size msz)).
        { apply (proj2 (u8arr_app2 m' (sh a) _ _)). split; [exact SHA'|]. rewrite repeat_length.
          replace (sh a + Z.of_nat 512) with (sh (a + 4096)) by (clear - AL; try acb; unfold sh; Z.div_mod_to_equations; lia). exact SHU'. }
        destruct SHALL as [_ (W1 & W2 & W3)]. rewrite length_app, repeat_length in W3. unfold sec_shadow in W3. rewrite !length_app, !repeat_length in W3.
        match type of W3 with forall i, 0 <= i < ?n -> _ => assert (LEN : n = msz / 8) end.
        { destruct (Z.eqb_spec (size mod 8) 0) as [E|E]; cbn [length]; unfold round_up; clear - E MSZ SZ; try acb; Z.div_mod_to_equations; lia. }
        rewrite LEN in W3. specialize (W3 (bv_unsigned x - sh a) ltac:(hci; clear - Hx; try acb; lia)). replace (sh a + (bv_unsigned x - sh a)) with (bv_unsigned x) in W3 by (clear; lia).
        unfold wa in W3. rewrite Z_to_bv_bv_unsigned in W3. exact W3.
      - apply WM'. exact (AWV x Hx). }
    assert (SHB : 2148314624 <= sh a) by (clear - AHI'; try acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    split.
    { (* [comment removed for export] *)
      destruct FXR as (FX1 & FX2 & [gg FX3] & FX4 & [bb FX5]).
      (* [comment removed for export] *)
      pose proof (akobj_lit _ _ T2) as THL. unfold kPageSize in THL.
      split; [(eapply rw_cells_transport; [exact FX1| exact MU'| exact WM'|]; unfold ml_W, depot_W; cbn [disjoint_from cells_size csize length Nat.add]; unfold AINST, AllocRepX.ALIBCPGSZ, AllocRepX.AGOT_SSP, AllocRepX.ASSPGUARD, ACFLAGS; clear - BND AHI' SHB SPR NB1; try acb; subst nch nres st; (first [clear - NB1 BND AHI' SHB ACEILB; lia | lia]))|].
      split; [(eapply rw_cells_transport; [exact FX2| exact MU'| exact WM'|]; unfold ml_W, depot_W; cbn [disjoint_from cells_size csize length Nat.add]; unfold AINST, AllocRepX.ALIBCPGSZ, AllocRepX.AGOT_SSP, AllocRepX.ASSPGUARD, ACFLAGS; clear - BND AHI' SHB SPR NB1; try acb; subst nch nres st; lia)|].
      split; [exists gg; (eapply rw_cells_transport; [exact FX3| exact MU'| exact WM'|]; unfold ml_W, depot_W; cbn [disjoint_from cells_size csize length Nat.add]; unfold AINST, AllocRepX.ALIBCPGSZ, AllocRepX.AGOT_SSP, AllocRepX.ASSPGUARD, ACFLAGS; clear - BND AHI' SHB SPR NB1 THL; try acb; subst nch nres st; lia)|].
      split; [(eapply rw_cells_transport; [exact FX4| exact MU'| exact WM'|]; unfold ml_W, depot_W; cbn [disjoint_from cells_size csize length Nat.add]; unfold AINST, AllocRepX.ALIBCPGSZ, AllocRepX.AGOT_SSP, AllocRepX.ASSPGUARD, ACFLAGS; clear - BND AHI' SHB SPR NB1; try acb; subst nch nres st; lia)| exists bb; (eapply rw_cells_transport; [exact FX5| exact MU'| exact WM'|]; unfold ml_W, depot_W; cbn [disjoint_from cells_size csize length Nat.add]; unfold AINST, AllocRepX.ALIBCPGSZ, AllocRepX.AGOT_SSP, AllocRepX.ASSPGUARD, ACFLAGS; clear - BND AHI' SHB SPR NB1; try acb; subst nch nres st; lia)]. }
    assert (PAR' : aapp pa kPtrArrayReserve /\ pa + kPtrArrayReserve <= aceil) by (exact (conj P2 P3)).
    assert (NCH' : 0 <= nch <= nres /\ nres + 16384 <= 2^20) by (unfold kChunksBlockCount in NB2; clear - NB1 NB2; try acb; subst nch nres st; lia).
    pose proof (amodelx_after s mo mo' a size d (conj AM AK) DCOV SZ AR3 FREE (lzok_LM OK) (lazy_ranges_okb_nowrap asegs _ (lzok_ranges OK)) ALLOW PAR' NCH' MO') as AMA.
    destruct AMA as [AMX2 DC2].
    split; [exact AMX2|].
    split; [pose proof MO' as M; unfold as_model in M; cbv beta iota zeta in M; exact (proj1 M)|].   (* [comment removed for export] *)
    split; [exact DEP'|].
    split.
    { unfold depot_placed. unfold d'. rewrite !d_nb_put, !d_sb_put. eapply depot_placed_after; try eassumption. }
    split; [intros x Hx; apply DC2; unfold d' in Hx; rewrite !d_nb_put, !d_sb_put in Hx; exact Hx|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact MU'|]. split; [exact WM'|].
    split.
    { (* [comment removed for export] *)
      assert (OKs : ast_ok s) by exact (conj PL WFs).
      assert (HLB : forall b, In b LB -> In b (alb s)) by (intros b Hb; exact (proj1 (proj2 (proj2 HR) b) Hb)).
      assert (SPhi : aceil <= bv_unsigned sp) by (clear - LO HI; try acb; lia).
      pose proof PNEW as PN. destruct PN as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
      assert (BS1 : a + msz <= a_sb s \/ a_sb s + kSpaceSize <= a) by (clear - N1; try acb; unfold disj, kSpaceSize, kPageSize in *; subst sb; lia).
      assert (BS2 : forall sc, In sc (as_sec (a_st s)) -> a + msz <= sc_map_beg sc \/ sc_map_beg sc + sc_map_size sc <= a)
        by (intros sc Hsc; pose proof (N8 sc Hsc) as D; clear - D; try acb; unfold disj in D; lia).
      pose proof (bsep_outside s OKs LB HLB a (a + msz) BS1 BS2) as BSEP.
      apply (amframe_of_munch s LB (bv_unsigned sp) _ m m' MU'). unfold ml_W, depot_W.
      destruct (apriv_depot_statics s OKs LB HLB (bv_unsigned sp) SPhi) as [AP1 AP2].
      destruct (apriv_depot_blocks s OKs LB HLB (bv_unsigned sp) (d_nb d) (d_sb d) G10 G12 G3 G4 G9 (proj1 DFS) (proj2 DFS) SPhi) as [AP3 AP4].
      repeat apply Forall_cons; cbn [fst snd]; try apply Forall_nil.
      - apply (apriv_stack s OKs LB HLB); exact LO.
      - apply (apriv_thread s OKs LB HLB); unfold kPageSize; try exact SPhi; clear; subst TH; lia.
      - apply (apriv_app s OKs LB HLB); [exact (arng_of_aapp _ _ AHI)| clear - CE SPhi; try acb; lia| exact BSEP| clear - N5; try acb; unfold disj in N5; lia].
      - replace (msz / 8) with ((a + msz - a) / 8) by (f_equal; clear; lia).
        apply (apriv_shadow s OKs LB HLB); [exact (arng_of_aapp _ _ AHI)| clear - MSZ SZ; try acb; lia| clear - AL; try acb; Z.div_mod_to_equations; lia| exact SPhi| exact BSEP| clear - N5; try acb; unfold disj in N5; lia].
      - apply (apriv_ptrarr s OKs LB HLB); unfold kPtrArrayReserve; try exact SPhi; clear - NCH'; try acb; subst pa; lia.
      - apply (apriv_inst s OKs LB HLB); [clear; lia| clear; lia| exact SPhi].
      - apply (apriv_thread s OKs LB HLB); unfold kPageSize; try exact SPhi; clear; subst TH; lia.
      - exact AP1.
      - exact AP2.
      - exact AP3.
      - exact AP4. }
    split.
    { (* [comment removed for export] *)
      apply (acompl_of_munchF s (sx a) d lo (bv_unsigned sp) _ m m' MU'). unfold ml_W, depot_W.
      assert (NEWSC : In (mkSC a msz needed) (as_sec (a_st (sx a)))).
      { change (as_sec (a_st (sx a))) with (as_sec st ++ [mkSC a msz needed]). apply in_app_iff. right. left. reflexivity. }
      repeat apply Forall_cons; cbn [fst snd]; try apply Forall_nil; intros aa Haa.
      - left. exact Haa.
      - right; left. unfold kPageSize. clear - Haa BND; try acb. subst TH. lia.
      - do 5 right; left. exists (mkSC a msz needed). split; [right; exact NEWSC| left; cbn [sc_map_beg sc_map_size]; exact Haa].
      - do 5 right; left. exists (mkSC a msz needed). split; [right; exact NEWSC| right; cbn [sc_map_beg sc_map_size]; exact Haa].
      - do 4 right; left. unfold kPtrArrayReserve. clear - Haa NCH' BND; try acb. subst pa. lia.
      - do 6 right; left. left. clear - Haa. lia.
      - right; left. unfold kPageSize. clear - Haa BND; try acb. subst TH. lia.
      - do 6 right; left. right; left. clear - Haa. lia.
      - do 6 right; left. right; left. clear - Haa. lia.
      - do 7 right; left. clear - Haa. lia.
      - do 7 right; right. clear - Haa. lia. }
    split.
    { (* [comment removed for export] *)
      pose proof MO' as MOx. unfold as_model in MOx. cbv beta iota zeta in MOx. destruct MOx as (_ & VM2 & _).
      apply (avmx_cons s (sx a) mo mo' a msz needed).
      - clear - AHI'; try acb. lia.
      - clear - MSZ SZ; try acb. lia.
      - clear - CE AHI'; try acb. lia.
      - exact (region_free_app_r _ _ _ _ FREE).
      - intros x Hx. rewrite VM2, in_rangesb_cons, Hx. apply Bool.orb_true_r.
      - intros sc Hin. change (as_sec (a_st (sx a))) with (as_sec st ++ [mkSC a msz needed]) in Hin. apply in_app_iff in Hin.
        destruct Hin as [Hin|[<-|[]]]; [left; exact Hin| right; reflexivity]. }
    split. { eapply new_block; [exact HR | exact DPL | exact SZ | exact AR3 | exact LO | exact NSEC' | exact NRES' | exact PAJ' | exact FILL' | exact SLK' | exact SHA' | exact SHU']. }
    split. { eapply new_block; [exact HR | exact DPL | exact SZ | exact AR3 | exact LO | exact NSEC' | exact NRES' | exact PAJ' | exact FILL' | exact SLK' | exact SHA' | exact SHU']. }
    (* [comment removed for export] *)
    apply (am_malloc_large st a size SZ); fold r; fold needed; fold msz.
    - unfold kPageSize. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by (clear - AHI'; try acb; lia). exact AL.
    - unfold kHighMemBeg, kHighMemEnd, kLowMemEnd, kShadowOffset. clear - ALIT AHI' CE'; try acb. lia.   (* [comment removed for export] *)
    - destruct PNEW as (N1 & _). unfold disj, kSpaceSize, kPageSize in N1. unfold in_primary. apply andb_false_iff.
      clear - N1 MSZ SZ; try acb. subst sb st. unfold a_sb, kSpaceSize, kPageSize in *. destruct N1 as [N1|N1]; [left; apply Z.leb_gt; lia| right; apply Z.ltb_ge; lia].
    - intros h Hh Hle. destruct PNEW as (_ & _ & _ & _ & _ & _ & _ & N8). pose proof (N8 h Hh) as D. pose proof (SEC h Hh) as (_ & _ & _ & Q4 & _).
      unfold disj, kPageSize in *. clear - Hle D Q4 MSZ SZ; try acb. lia.
    - unfold kMaxNumChunks, kChunksBlockCount in *. clear - NB1 NB2 NSEC; try acb. subst nch. try subst nres. subst st. lia.
  Qed.
End MallocLargeGlue.
