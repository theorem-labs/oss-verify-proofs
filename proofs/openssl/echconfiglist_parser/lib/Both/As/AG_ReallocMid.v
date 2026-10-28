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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AsConst.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocBudget AllocRep AllocRepFacts AllocRepFacts2 AllocRepX CidBits CidBits2
     AsDepotInv AsDepotHash AsUnwind AW_DepotFrame AW_MallocBase AW_AllocBase AW_IAInit AW_FreePre
     AW_ReallocPre AW_ReallocMid AW_ReallocRet
     AG_WFHit AG_MallocModel AG_RefillModel AG_ColdModel AG_Malloc AG_Malloc2 AG_WriteSet AG_Frame AG_MallocAll
     AS_Refill1 AG_Refill1 AG_Refill2 AG_Refill3 AG_MallocCold AG_MallocTop AG_Free1 AG_Free6 AG_Free7 AG_Free AG_ReallocF2 AG_ReallocCold AG_RecycleDefs SecLazy AllocWalkKit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaGuard.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac lia ::=
  dle_wrap ltac:(first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ]).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section ChimBridge.
  Context {HCEIL : HeapCeil}.

  Lemma munch_chim : forall (Wbig Wsmall X : list ivl) (m m' : mem),
    munch Wbig m m' -> (forall x, outside Wsmall x -> outside X x -> outside Wbig x) -> munch Wsmall m (chim X m m').
  Proof.
    intros Wbig Wsmall X m m' MU SUB x Hx. unfold chim. destruct (inb X (bv_unsigned x)) eqn:E; [reflexivity|].
    apply MU. apply SUB; [exact Hx| apply inb_false_outside; exact E].
  Qed.

  Lemma amframe_chim_ext : forall s LB SP X m m',
    amframe s LB SP m (chim X m m') -> (forall a, ~ outside X a -> ~ aclient s LB SP a) -> amframe s LB SP m m'.
  Proof.
    intros s LB SP X m m' AF NC a Ha CL. pose proof (AF a Ha CL) as E. unfold chim in E. rewrite wa_unsigned in E by exact Ha.
    destruct (inb X a) eqn:I; [| exact E]. exfalso. apply (NC a); [| exact CL]. apply inb_true_not_outside. exact I.
  Qed.

  Lemma acompl_chim_ext : forall s s' d lo SP X m m',
    acompl s s' d lo SP m (chim X m m') -> (forall a, ~ outside X a -> awrit s s' d lo SP a) -> acompl s s' d lo SP m m'.
  Proof.
    intros s s' d lo SP X m m' AC WR a Ha NW. pose proof (AC a Ha NW) as E. unfold chim in E. rewrite wa_unsigned in E by exact Ha.
    destruct (inb X a) eqn:I; [| exact E]. exfalso. apply NW. apply WR. apply inb_true_not_outside. exact I.
  Qed.
End ChimBridge.

(* [comment removed for export] *)
Section ReallocMidGlue.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo size : Z) (CH : list (Z * Z)).
  Variables (och : chunk) (bs sbs : list byte).

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
  Let cnt := pc_count (get_pc st c).
  Let chunks := pc_chunks (get_pc st c).
  Let cp1 := hd 0 chunks.
  Let AB1 := compact_to_addr st c cp1.
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CH.
  Let T := utrace 0x1bf8f0 (bv_unsigned sp) (a_top s) (a_bot s) 30 CHI.
  Let nT := Z.of_nat (length T).
  Let d' := d_put d (depot_hash T) nT.
  Let P0 := ch_user_beg och.
  Let old := ch_used och.

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
  Hypothesis HI : lo + 3072 <= bv_unsigned sp.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis SZ : 1 <= size /\ needed <= kMaxSize.
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
  Hypothesis PROOM : pusage st + COLD_COST <= B_PRIM.
  Hypothesis ROOM : rg_mapped_user (get_region st c) + 2 * kUserMapSize <= kFreeArrayOffset.
  Hypothesis OK : lzok asegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo).
  Hypothesis VISE : restrict (a_L s) (a_S s) msF
    = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1bf7b4) fc None m (seg_rom asegs).

  (* [comment removed for export] *)
  Definition realloc_mid_gpost (sM : ast) (UM : Z) (stM : astate) (msF' : machine_state) (mo' : Model) : Prop :=
    exists (t0' t1' t2' a6' a7' t3' t4' t5' t6' cfu : word) (jk jr1 jr2 junk : list byte) (rest : list word) (m' : mem),
       a_thr sM = a_thr s /\ a_ctx sM = a_ctx s /\ a_fsb sM = a_fsb s /\ a_Zr sM = a_Zr s /\ a_top sM = a_top s /\ a_bot sM = a_bot s
    /\ a_sb sM = a_sb s /\ a_pa sM = a_pa s /\ as_sec (a_st sM) = as_sec st /\ a_AL sM = a_AL s
    /\ a_st sM = set_internal_init stM
    /\ lzok asegs (a_L sM) (a_S sM) (a_Zr sM) (mkCfg msF' mo')
    /\ restrict (a_L sM) (a_S sM) msF'
       = MS (mkR (wz 0x197a10) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0' t1' t2'
                 (Z_to_bv 64 (bv_unsigned sp + -2136)) (wz P0) (wz AINST) (wz P0) (wz 0) (wz 0) (Z_to_bv 64 (bv_unsigned sp + -2136)) (wz 1) a6' a7'
                 (wz AINST) (wz (Z.min size old)) (wz UM) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (bv_unsigned sp + -89)) s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x196ae8) fc None m' (seg_rom asegs)
    /\ ARHEAP sM ((UM, size) :: LB) m' /\ awin_vis sM m' /\ flagsx_rep m' /\ AMODELX sM mo' /\ nonvm_same mo mo'
    /\ DEPOT asegs d' m' /\ depot_placed sM d' /\ depot_cov d' mo'
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + -2208)
    /\ amframe s LB (bv_unsigned sp) m m' /\ wmono asegs m m' /\ acompl s sM d lo (bv_unsigned sp) m m' /\ avmx s sM mo mo'
    /\ rw_cells asegs m' UM [CB (Z.to_nat size) (firstn (Z.to_nat (Z.min size old)) bs ++ skipn (Z.to_nat (Z.min size old)) junk)] /\ length junk = Z.to_nat size
    /\ addressable m' UM size
    /\ (forall kaddr, exists st'' ev, am_malloc_k st size kaddr = Some (UM, st'', ev) /\ same_but_shadow st'' stM)
    /\ rframes sp ra s0 s1 s2 s3 s4 s5 s6 T rest jk jr1 jr2 cfu P0 size m'
    /\ rw_cells asegs m' P0 [CB (Z.to_nat old) bs] /\ SHAD m' P0 sbs
    /\ rw_cells asegs m' AIAINIT [C1 (b8 1); C1 (b8 0); C2 (wz 0)] /\ ia_after m'
    /\ Forall (fun x => 0 <= x < 2^64) T /\ (1 <= length T <= 30)%nat /\ length rest = (255 - length T)%nat.

  Let R : AREP s m. Proof. exact (proj1 HR). Qed.
  Let OKs : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OKs). Qed.
  Let WFs : WF st. Proof. exact (proj2 OKs). Qed.
  Let HLB : forall b, In b LB -> In b (alb s). Proof. intros b Hb. exact (proj1 (proj2 (proj2 HR) b) Hb). Qed.
  Let UHI0 : aapp (ch_user_beg och - 16) (16 + round_up (ch_used och) 8). Proof. exact (uhi_of_arep s m och R CHIN0). Qed.
  Let HC : 1 <= c <= 30.
  Proof.
    subst c. apply class_id_le30. pose proof (rz_size_facts size) as (RZ & _). unfold kMaxSize in SZ. subst needed rz. unfold round_up in *.
    Z.div_mod_to_equations. lia.
  Qed.
  Let TBAND : TH + 4096 <= 65536 \/ (12599296 <= TH /\ TH + 4096 <= 2147446784) \/ 17594333495296 <= TH.
  Proof. pose proof PL as (_ & _ & _ & _ & _ & _ & _ & T2 & _). exact (akobj_lit _ _ T2). Qed.
  Let BTH : 4096 <= TH /\ TH + 4096 <= aceil.
  Proof. pose proof PL as (_ & _ & _ & _ & _ & _ & T1 & T2 & T3 & _). pose proof (akobj_env _ _ T2 ltac:(unfold kPageSize; clear; lia)) as E. unfold kPageSize in *. clear - E T3. unfold TH. lia. Qed.

  (* [comment removed for export] *)
  Let XH : list ivl := [(AIAINIT, AIAINIT + 4); (AIAINST, AIAINST + 0x81030)].
  Let XC : list ivl := [(AIAINIT, AIAINIT + 4); (AIAINST, AIAINST + 0x81030); (TH + 2856, TH + 2872)].
  Let NCX : forall a, ~ outside XC a -> ~ aclient s LB (bv_unsigned sp) a.
  Proof.
    intros a Ha. assert (SPc : aceil <= bv_unsigned sp) by (clear - LO HI; try acb; lia).
    assert (D : (AIAINIT <= a < AIAINIT + 4) \/ (AIAINST <= a < AIAINST + 0x81030) \/ (TH + 2856 <= a < TH + 2872)).
    { unfold XC in Ha. cbn [outside] in Ha. clear - Ha. unfold AIAINIT, AIAINST in *.
      destruct (Z.lt_ge_cases a 7578504); destruct (Z.lt_ge_cases a 7578508); destruct (Z.lt_ge_cases a 6994688); destruct (Z.lt_ge_cases a 7523120);
      destruct (Z.lt_ge_cases a (TH + 2856)); destruct (Z.lt_ge_cases a (TH + 2872)); try lia; exfalso; apply Ha; repeat split; try exact I; lia. }
    destruct D as [D|[D|D]].
    - apply (apriv_static s OKs LB HLB (bv_unsigned sp) AIAINIT (AIAINIT + 4)); [unfold AIAINIT, AIMG_TOP; clear; lia| exact SPc| unfold AIAINIT; clear; lia| exact D].
    - apply (apriv_static s OKs LB HLB (bv_unsigned sp) AIAINST (AIAINST + 0x81030)); [unfold AIAINST, AIMG_TOP; clear; lia| exact SPc| unfold AIAINST; clear; lia| exact D].
    - apply (apriv_thread s OKs LB HLB (bv_unsigned sp) (TH + 2856) (TH + 2872)); [unfold TH; clear; lia| unfold TH, kPageSize; clear; lia| clear; lia| exact SPc| exact D].
  Qed.
  Let NHX : forall a, ~ outside XH a -> ~ aclient s LB (bv_unsigned sp) a.
  Proof. intros a Ha. apply NCX. intros O. apply Ha. unfold XC in O. unfold XH. cbn [outside] in O |- *. tauto. Qed.
  Let WCX : forall sX, awrit s sX d lo (bv_unsigned sp) = awrit s sX d lo (bv_unsigned sp) -> forall a, ~ outside XC a -> awrit s sX d lo (bv_unsigned sp) a.
  Proof.
    intros sX _ a Ha.
    assert (D : (AIAINIT <= a < AIAINIT + 4) \/ (AIAINST <= a < AIAINST + 0x81030) \/ (TH + 2856 <= a < TH + 2872)).
    { unfold XC in Ha. cbn [outside] in Ha. clear - Ha. unfold AIAINIT, AIAINST in *.
      destruct (Z.lt_ge_cases a 7578504); destruct (Z.lt_ge_cases a 7578508); destruct (Z.lt_ge_cases a 6994688); destruct (Z.lt_ge_cases a 7523120);
      destruct (Z.lt_ge_cases a (TH + 2856)); destruct (Z.lt_ge_cases a (TH + 2872)); try lia; exfalso; apply Ha; repeat split; try exact I; lia. }
    unfold awrit. destruct D as [D|[D|D]].
    - do 6 right. left. unfold astatw. clear - D. tauto.
    - do 6 right. left. unfold astatw. clear - D. tauto.
    - right. left. unfold kPageSize. fold TH. clear - D. lia.
  Qed.
  Let WHX : forall sX, awrit s sX d lo (bv_unsigned sp) = awrit s sX d lo (bv_unsigned sp) -> forall a, ~ outside XH a -> awrit s sX d lo (bv_unsigned sp) a.
  Proof. intros sX E a Ha. apply (WCX sX E). intros O. apply Ha. unfold XC in O. unfold XH. cbn [outside] in O |- *. tauto. Qed.

  Theorem realloc_arep_mid :
    (forall sM UM stM msF' mo', realloc_mid_gpost sM UM stM msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF mo).
  Proof.
    intros K. destruct AX as [AWV FXR].
    destruct (Z.eq_dec cnt 0) as [MISS|HIT].
    - (* [comment removed for export] *)
      eapply (realloc_arep_cold ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m msF mo Q s LB d lo size CH och bs sbs
                HR (conj AWV FXR) AMX DEP DPL DCOV MI ST LO HI SPA SPT SZ MISS TP DCAP FCH Ha0 Ha1 CHIN0 ALLOC0 OLDSZ SZB BLK0 SHB0 AC PROOM ROOM OK VISE).
      intros msF' mo' PO.
      destruct PO as (t0' & t1' & t2' & a6' & a7' & t3' & t4' & t5' & t6' & cfu & jk & jr1 & jr2 & junk & rest & m' & OK' & VIS' & HR' & AWV' & FX' & AMX' & NV' & DEP' & DPL' & DCOV'
                      & MI' & ST' & MU' & WM' & AVX' & BLK & LJ & ADDR & MODEL & FRR & FRA & FP & ESO & ETR & LR & TFB & F8 & OBLK & OSH & FLG & IA & TRNG & NRT).
      lazymatch type of HR' with ARHEAP ?sX ((?UX, _) :: _) _ =>
        lazymatch type of MODEL with context [same_but_shadow _ ?stX] =>
          apply (K sX UX stX) end end.
      unfold realloc_mid_gpost.
      exists t0', t1', t2', a6', a7', t3', t4', t5', t6', cfu. exists jk, jr1, jr2, junk, rest, m'.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact OK'|]. split; [exact VIS'|]. split; [exact HR'|]. split; [exact AWV'|]. split; [exact FX'|]. split; [exact AMX'|]. split; [exact NV'|].
      split; [exact DEP'|]. split; [exact DPL'|]. split; [exact DCOV'|]. split; [exact MI'|]. split; [exact ST'|].
      split.
      { (* [comment removed for export] *)
        apply (amframe_chim_ext s LB (bv_unsigned sp) XC m m'); [| exact NCX].
        apply (AG_MallocTop.cold_frame ra sp s0 m s LB d lo size CH HR DPL DFS LO ltac:(clear - HI; lia) SZ ROOM).
        apply (munch_chim _ _ XC m m' MU'). intros x Hx HX. unfold rc_W. unfold AG_MallocCold.mc_W in Hx. cbv zeta in Hx.
        apply outside_app in Hx. destruct Hx as [Hr Ht]. apply outside_app. unfold XC in HX. cbn [outside] in HX. destruct HX as (X1 & X2 & X3 & _).
        cbn [outside] in Hr |- *. destruct Hr as (R1 & R2 & RR). destruct Ht as (T1 & T2 & T3 & T4 & T5 & T6 & TD).
        split; [exact (conj R1 (conj R2 (conj X1 (conj X2 (conj X3 RR)))))|].
        exact (conj T1 (conj T2 (conj T3 (conj T4 (conj T5 (conj T6 (conj X1 (conj X2 TD)))))))). }
      split; [exact WM'|].
      split.
      { apply (acompl_chim_ext s _ d lo (bv_unsigned sp) XC m m'); [| exact (WCX _ eq_refl)].
        apply (AG_MallocTop.cold_compl ra sp s0 m s LB d lo size CH HR DPL LO SZ ROOM _ _ eq_refl).
        apply (munch_chim _ _ XC m m' MU'). intros x Hx HX. unfold rc_W. unfold AG_MallocCold.mc_W in Hx. cbv zeta in Hx.
        apply outside_app in Hx. destruct Hx as [Hr Ht]. apply outside_app. unfold XC in HX. cbn [outside] in HX. destruct HX as (X1 & X2 & X3 & _).
        cbn [outside] in Hr |- *. destruct Hr as (R1 & R2 & RR). destruct Ht as (T1 & T2 & T3 & T4 & T5 & T6 & TD).
        split; [exact (conj R1 (conj R2 (conj X1 (conj X2 (conj X3 RR)))))|].
        exact (conj T1 (conj T2 (conj T3 (conj T4 (conj T5 (conj T6 (conj X1 (conj X2 TD)))))))). }
      split; [exact AVX'|]. split; [exact BLK|]. split; [exact LJ|]. split; [exact ADDR|]. split; [exact MODEL|].
      split; [exact (conj FRR (conj FRA (conj FP (conj ESO (conj ETR (conj TFB F8))))))|].
      split; [exact OBLK|]. split; [exact OSH|]. split; [exact FLG|]. split; [exact IA|]. split; [exact TRNG|]. split; [exact NRT| exact LR].
    - (* [comment removed for export] *)
      eapply (evt_sreach_lazy_at asegs (a_L s) (a_S s) (a_Zr s) _ msF _ mo Q OK VISE).
      { eapply (realloc_front_hit ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB d lo size CH
                  HR DEP DPL MI ST LO HI SPA SPT SZ HIT TP DCAP FCH och bs sbs);
          first [exact Ha0| exact Ha1| exact CHIN0| exact ALLOC0| exact UHI0| exact OLDSZ| exact SZB| exact BLK0| exact SHB0| exact AC]. }
      cbv beta. intros msF1 mo1 OK1 SBM1 _ PO1.
      destruct PO1 as (t0' & t1' & t2' & a6' & a7' & t3' & t4' & t5' & t6' & cfu & jk & jr1 & jr2 & junk & rest & m1 & VIS1 & MU1 & WM1 & MI1 & ST1 & HR1 & DEP1
                       & BLK & LJ & ADDR & FRR & FRA & FP & ESO & ETR & LR & TFB & F8 & OBLK & OSH & FLG & IA & TRNG & NRT).
      pose proof SZ as SZ'. destruct (realloc_front_model ra sp s0 m s LB d lo size CH HR DPL LO HI SZ HIT) as (stX & evX & MK & SBS).
      lazymatch type of HR1 with ARHEAP ?sX ((?UX, _) :: _) _ =>
        lazymatch type of SBS with same_but_shadow _ ?stX' => apply (K sX UX stX') end end.
      unfold realloc_mid_gpost.
      exists t0', t1', t2', a6', a7', t3', t4', t5', t6', cfu. exists jk, jr1, jr2, junk, rest, m1.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact OK1|]. split; [exact VIS1|]. split; [exact HR1|].
      split; [intros x Hx; apply WM1; exact (AWV x Hx)|].
      assert (HIN1 : In cp1 chunks).
      { pose proof (co_count _ _ (WF_cache st c WFs ltac:(hci; unfold kNumClasses; clear - HC; try acb; lia))) as CC. fold cnt chunks in CC.
        unfold cp1. destruct chunks as [|x l]; [exfalso; apply HIT; rewrite CC; reflexivity| left; reflexivity]. }
      pose proof (carved_in_space s OKs c AB1 (carved_cache st c cp1 WFs ltac:(hci; unfold kNumClasses; clear - HC; try acb; lia) HIN1)) as CIS.
      pose proof PL as (Y1 & Y2 & Y3 & _). unfold AHI_LO, kSpaceSize, kPageSize in Y2, Y3. fold sb in Y2, Y3. change (a_sb s) with sb in CIS. fold csz in CIS. unfold kSpaceSize in CIS.
      assert (SHB1 : 0x2008fff7000 <= sh AB1) by (clear - CIS Y2; try acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
      pose proof DPL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G10 & G11 & G12 & G13).
      pose proof (aapp_env _ _ G10 ltac:(clear; lia)) as G10e. pose proof (aapp_env _ _ G12 ltac:(clear; lia)) as G12e.
      split.
      { (* [comment removed for export] *)
        apply (flagsx_transport _ m m1 (munch_agree _ _ _ MU1) WM1); [| exact FXR]. intros a Ha N1 N2 N3 N4.
        cbn [outside depot_W app]. unfold AIMG_TOP in Ha. fold st TH. fold rz. fold needed. fold c. fold csz. fold csz8. fold chunks. fold cp1. fold AB1.
        clear - Ha N1 N2 N3 N4 LO BTH TBAND Y2 Y3 G10e G12e CIS SHB1 HC. acb.
        repeat split; try exact I; try assumption; try (first [clear - Ha LO ACEILB; lia | clear - Ha BTH TBAND HC; lia | clear - Ha CIS Y2; lia | clear - Ha SHB1; lia | clear - Ha G10e; lia | clear - Ha G12e; lia | lia]). }
      split; [exact (amodelx_hit s mo1 c cnt (tl chunks) _ (AMODELX_mat s mo mo1 AMX SBM1))|].
      split; [exact (nonvm_same_mat _ _ SBM1)|].
      split; [exact DEP1|].
      split; [unfold depot_placed; unfold d'; rewrite d_nb_put, d_sb_put; exact DPL|].
      split; [unfold depot_cov; unfold d'; rewrite d_nb_put, d_sb_put; intros x Hx; rewrite (same_but_materialized_vmmaps mo mo1 SBM1); exact (DCOV x Hx)|].
      split; [exact MI1|]. split; [exact ST1|].
      split.
      { apply (amframe_chim_ext s LB (bv_unsigned sp) XH m m1); [| exact NHX].
        apply (AG_MallocTop.hit_frame ra sp s0 m s LB d lo size CH HR DPL DFS LO ltac:(clear - HI; lia) SZ _ HIT).
        apply (munch_chim _ _ XH m m1 MU1). intros x Hx HX. unfold XH in HX. cbn [outside] in HX. destruct HX as (X1 & X2 & _).
        cbn [outside] in Hx |- *. destruct Hx as (T1 & T2 & T3 & T4 & T5 & T6 & TD).
        exact (conj T1 (conj T2 (conj T3 (conj T4 (conj T5 (conj T6 (conj X1 (conj X2 TD)))))))). }
      split; [exact WM1|].
      split.
      { apply (acompl_chim_ext s _ d lo (bv_unsigned sp) XH m m1); [| exact (WHX _ eq_refl)].
        apply (AG_MallocTop.hit_compl ra sp s0 m s LB d lo size CH HR DPL LO SZ _ _ HIT eq_refl).
        apply (munch_chim _ _ XH m m1 MU1). intros x Hx HX. unfold XH in HX. cbn [outside] in HX. destruct HX as (X1 & X2 & _).
        cbn [outside] in Hx |- *. destruct Hx as (T1 & T2 & T3 & T4 & T5 & T6 & TD).
        exact (conj T1 (conj T2 (conj T3 (conj T4 (conj T5 (conj T6 (conj X1 (conj X2 TD)))))))). }
      split; [apply avmx_same; [rewrite (same_but_materialized_vmmaps mo mo1 SBM1); reflexivity| reflexivity]|].
      split; [exact BLK|]. split; [exact LJ|]. split; [exact ADDR|].
      split; [intros kaddr; rewrite (AG_MallocTop.am_malloc_k_prim_kaddr ra sp s0 s size CH SZ kaddr); exists stX, evX; split; [exact MK| exact SBS]|].
      split; [exact (conj FRR (conj FRA (conj FP (conj ESO (conj ETR (conj TFB F8))))))|].
      split; [exact OBLK|]. split; [exact OSH|]. split; [exact FLG|]. split; [exact IA|]. split; [exact TRNG|]. split; [exact NRT| exact LR].
  Qed.
End ReallocMidGlue.
