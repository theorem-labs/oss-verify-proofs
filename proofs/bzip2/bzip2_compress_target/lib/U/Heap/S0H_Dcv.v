(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec CatSim ShapeAlg MmapSim RefNodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep Arr.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode SFMisc EvtBridge.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.EvtBridge.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require STree Malloc MallocCtrl Monad MSafe Prog KInv KStep KStepC MI_Inv MI_Kit MI_Geom MI_Contracts MTight.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require MI_Bits.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require MI_Arith MShapeA MShapeB MShapeC MShape21 MShapeF MI_WFree2 MI_Ledger.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Monad OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MSafe OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prog OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.KInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.KStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.KStepC OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Inv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Kit OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Geom OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Contracts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MTight OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Bits.MI_Cnt OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Arith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MShapeA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MShapeB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MShapeC OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MShape21 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MShapeF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WFree2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Ledger.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import MallocBlocks Malloc_iface MallocHINV.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP RF_malloc_spec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require S0H_Iface.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_iface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_ifaceP OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_malloc_spec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap.S0H_Iface.RF_free_spec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require Import AllocLayout0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocCover AllocTight TreeBridge TightBridge CoverBridge. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require Import S0H_Iface S0H_Tight S0H_Cover. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocDcv.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLia.

Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section BIGD.
Variables (LB : list ablock) (s : PState) (MD : Model) (n : Z).
Hypothesis HO : OWNX (map blk_id LB) (vmG MD) s MD.
Hypothesis Hn : MMAP_THRESHOLD <= n <= MAX_REQ_D.
Hypothesis HC : 1 <= cnt s.

Lemma bigd_MM : exists K, cmalloc (ps_m s) n = SVis (EMmap 0 (n + IB + UNIT) PROT_RW MAPF0) K /\
  MMAP1 (live_ranges (ps_m s)) (cmalloc (ps_m s) n)
    (fun t => t = SRet (ps_m s, @None cptr))
    (fun z t => exists cs' c g bg, t = SRet (cs', Some c) /\ AFR (fun x => x = 63) 1 (Some g) (ps_m s) cs'
                /\ hosts cs' bg g /\ m_sizeclass (MR cs' g) = 63 /\ m_last_idx (MR cs' g) = 0 /\ c = (fst bg, sstart (MR cs' g) 0)).
Proof.
  destruct HO as [(L & SR & HK & _) _].
  cps_destruct (cmalloc_big_shape (ps_m s) L n SR ltac:(lia) ltac:(unfold size_overflows, MAX_REQ_D in *; apply Z.leb_gt; lia) HC) as (K & E & KK).
  exists K. split; [exact E|]. exists (n + IB + UNIT), K. split; [exact E|]. split; [unfold IB, UNIT, MAX_REQ_D, MMAP_THRESHOLD in *; lia|].
  split; intros z AOK ER; destruct (KK z AOK) as [F S]; [exact (F ER)| exact (S ER)].
Qed.

Lemma bigd_classify tr r s' MD' :
  tpath nstep (raw_malloc n s) MD tr (Ok (r, s')) MD' -> tr = [] /\ BIGCL' s MD n r s' MD'.
Proof.
  intros Hp. cps_destruct bigd_MM as (K0 & E0 & MM).
  cps_destruct (raw_malloc_paths (map blk_id LB) (vmG MD) s MD n _ _
              (fun x => x = (ps_m s, @None cptr))
              (fun z x => exists cs' c g bg, x = (cs', Some c) /\ AFR (fun x => x = 63) 1 (Some g) (ps_m s) cs'
                 /\ hosts cs' bg g /\ m_sizeclass (MR cs' g) = 63 /\ m_last_idx (MR cs' g) = 0 /\ c = (fst bg, sstart (MR cs' g) 0))
              HO ltac:(unfold MMAP_THRESHOLD in Hn; lia) MM
              ltac:(intros t ->; eexists; split; reflexivity)
              ltac:((intros z t; cps_intros (cs' & c & g & bg & -> & REST)); eexists; split; [reflexivity| exists cs', c, g, bg; auto])
              tr r s' MD' Hp) as (len & K & z & x & E & Hlen & -> & -> & -> & CASES).
  split; [reflexivity|]. rewrite E0 in E. injection E as El _. subst len.
  destruct CASES as [(ERR & -> & ->)|(NERR & (cs' & c & g & bg & -> & AF & Hh & SC & LI & Ec) & VO & LZ & HH & VM' & AOK & MAT' & RF)].
  - left. cbn. auto.
  - right. exists cs', c, g, bg, z. cbn [fst snd]. unfold ONEMAP. auto 12.
Qed.

Lemma bigd_acvm k tr r s' MD' :
  S0_acvm (S k) s MD -> tpath nstep (raw_malloc n s) MD tr (Ok (r, s')) MD' -> S0_acvm k s' MD'.
Proof.
  intros [CNT VM] Hp. destruct (bigd_classify tr r s' MD' Hp) as [_ CL].
  unfold S0_acvm, cnt in *.
  destruct CL as [(-> & -> & ->)|(cs' & c & g & bg & z & -> & -> & (VO & LZ & HH & VM' & AOK & MAT') & AF & _)]; cbn [ps_m set_m].
  - split; [lia| eapply VMB_le; [exact VM| lia]].
  - pose proof (afr_cnt _ _ _ _ _ AF) as CC. split; [lia|].
    apply (VMB_add k MD MD' z (n + IB + UNIT)); [exact VM| unfold IB, UNIT, MAX_REQ_D, MMAP_THRESHOLD in *; lia| exact AOK| exact VM'| exact MAT'].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

End BIGD.

(* [comment removed for export] *)
Lemma t_leaves_if_same {A} : forall (t : itree node (exc A)) MD (f : A -> bool) (T : TSet) (P : exc A -> Model -> Prop),
  twf t MD P -> (forall MD', ~ P Unr MD') ->
  t_eq (t_leaves t MD (fun a _ => if f a then T else T)) T.
Proof.
  intros t MD f T P Htwf HP tr. unfold t_leaves. split.
  - cps_intros (a & MD' & _ & HT). destruct (f a); exact HT.
  - intros HT. cps_destruct (twf_reaches t MD P Htwf) as (r & MD' & Hp & HPr).
    destruct r as [|a]; [exfalso; exact (HP _ HPr)|]. exists a, MD'. split; [exact Hp|]. destruct (f a); exact HT.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma S0_malloc_dcv_big : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
      (s : PState) (LB : list ablock) (k : nat) (n lo B : Z) (errv : word) (T : TSet),
    S0_inv s LB m MD -> S0_acvm (S k) s MD -> MMAP_THRESHOLD <= n <= MAX_REQ_D ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk s0segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack S0_layout ->
    rw_cells s0segs m (errno_cell S0_layout) [C4 errv] ->
    mem_inv s0segs m ->
    tp = Z_to_bv 64 (al_tp S0_layout) ->
    a0 = Z_to_bv 64 n ->
    (forall (s' : PState) (LB' : list ablock) (m' : word -> option byte) (MD' : Model) (r : Z)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word),
        S0_inv s' LB' m' MD' -> vm_only MD MD' -> S0_acvm k s' MD' ->
        mem_inv s0segs m' -> stk s0segs m' lo (bv_unsigned sp) -> rw_cells s0segs m' (errno_cell S0_layout) [C4 errv'] -> rauxv_ok m' B ->
        heap_pres s0segs S0_layout LB (bv_unsigned sp) m m' ->
        ((r = 0 /\ LB' = LB)
         \/ (r <> 0 /\ block_ok S0_layout r n /\ (exists p, LB' = (p, r, n) :: LB /\ ~ In p (map blk_id LB))
             /\ exists junk, rw_cells s0segs m' r [CB (Z.to_nat n) junk])) ->
        realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom s0segs)) MD') T) ->
    realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_malloc S0_layout)) fc None m (seg_rom s0segs)) MD) T.
Proof.
  intros until T. intros HI HV Hn AUX SB ST CLO LO ERR MI TP A0 K.
  destruct HI as [HR HO]. pose proof (S0_inv_model s LB m MD (conj HR HO)) as [Hh Hl].
  cbn [al_stack S0_layout] in LO. cbn [al_tp S0_layout] in TP.
  rewrite <- (errno_cell_S0 tp TP) in ERR.
  pose proof (rmalloc_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv
                HR AUX SB ST ltac:(bz_ceil; exact CLO) ltac:(unfold RMALLOC_STACK; lia) ERR MI TP A0 ltac:(unfold MMAP_THRESHOLD, MAX_REQ_D in Hn; lia)) as HM.
  pose proof (raw_malloc_spec_c (map blk_id LB) (vmG MD) n (vmG_frame MD) ltac:(unfold MMAP_THRESHOLD in Hn; lia)) as HS0.
  pose proof (OWN_vmG _ _ _ HO) as HOv.
  assert (HC1 : 1 <= cnt s) by (destruct HV as [CNT _]; lia).
  pose proof (mspec_strengthen (OWNX (map blk_id LB) (vmG MD)) (raw_malloc n) _
                (fun sx mo0 r s' mo' => sx = s -> mo0 = MD -> BIGCL' s MD n r s' mo' /\ S0_acvm k s' mo') HS0) as HS1.
  assert (HRR : forall sx mox tr ax sx' mox', OWNX (map blk_id LB) (vmG MD) sx mox -> tpath nstep (raw_malloc n sx) mox tr (Ok (ax, sx')) mox' ->
                 sx = s -> mox = MD -> BIGCL' s MD n ax sx' mox' /\ S0_acvm k sx' mox').
  { intros sx mox tr ax sx' mox' HO0 Hp -> ->. split.
    - destruct (bigd_classify LB s MD n HO0 Hn HC1 tr ax sx' mox' Hp) as [_ CL]. exact CL.
    - exact (bigd_acvm LB s MD n HO0 Hn HC1 k tr ax sx' mox' HV Hp). }
  specialize (HS1 HRR s MD HOv). clear HRR.
  eapply rz_conseq.
  - apply (implM_mspec_realizes s0segs (raw_malloc n) s _ (fun s1 mo1 => s1 = s /\ mo1 = MD) _
             (fun _ _ => T) _ MD HM HS1 (conj eq_refl eq_refl) Hh Hl).
    intros r s' ms' MD' HQm [HQk CLV]. destruct (CLV eq_refl eq_refl) as [CL HV'].
    cps_destruct HQm as (u0 & u1 & u2 & ra0 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & HP' & _ & _ & Hrr).
    rewrite (errno_cell_S0 tp TP) in ERR'.
    destruct r as [p|].
    + cps_destruct Hrr as (A & junk & -> & BR & HR' & CH & _). destruct HQk as [HO' _].
      pose proof (OWNX_G _ _ _ _ HO') as V. unfold vmG in V.
      pose proof (RHEAP_blocks_nodup_proof _ _ _ HR') as ND. cbn [map] in ND. inversion ND; subst.
      unfold rblock_range in BR. bz_ceil.
      assert (HI' : S0_inv s' ((p, A, n) :: LB) m' MD') by (split; [exact HR'| cbn [map blk_id fst]; exact (OWN_TrueG _ _ _ _ HO')]).
      assert (HPP : heap_pres s0segs S0_layout LB (bv_unsigned sp) m m') by (apply heap_pres_of_r; exact HP').
      assert (BOK : block_ok S0_layout A n) by (unfold block_ok; cbn [al_img_lo al_img_hi S0_layout]; exact BR).
      apply (K s' ((p, A, n) :: LB) m' MD' A u0 u1 u2 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 errv'); try assumption.
      right. split; [lia|]. split; [exact BOK|]. split; [exists p; split; [reflexivity| assumption]| exists junk; exact CH].
    + destruct Hrr as [-> HR']. pose proof (OWNX_G _ _ _ _ HQk) as V. unfold vmG in V.
      assert (HI' : S0_inv s' LB m' MD') by (split; [exact HR'| exact (OWN_TrueG _ _ _ _ HQk)]).
      assert (HPP : heap_pres s0segs S0_layout LB (bv_unsigned sp) m m') by (apply heap_pres_of_r; exact HP').
      apply (K s' LB m' MD' 0 u0 u1 u2 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 errv'); try assumption.
      left. split; reflexivity.
  - eapply t_leaves_const; [exact (HS1 s MD (conj eq_refl eq_refl))|]. intros MD' HF. exact HF.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma S0_malloc_dcv_small : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
      (s : PState) (LB : list ablock) (k : nat) (n lo B : Z) (errv : word) (T : TSet),
    S0_inv s LB m MD -> S0_acvm (ac_cost n + k) s MD -> 0 <= n < MMAP_THRESHOLD ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk s0segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack S0_layout ->
    rw_cells s0segs m (errno_cell S0_layout) [C4 errv] ->
    mem_inv s0segs m ->
    tp = Z_to_bv 64 (al_tp S0_layout) ->
    a0 = Z_to_bv 64 n ->
    (forall (s' : PState) (LB' : list ablock) (m' : word -> option byte) (MD' : Model) (r : Z)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word),
        S0_inv s' LB' m' MD' -> vm_only MD MD' -> S0_acvm k s' MD' ->
        mem_inv s0segs m' -> stk s0segs m' lo (bv_unsigned sp) -> rw_cells s0segs m' (errno_cell S0_layout) [C4 errv'] -> rauxv_ok m' B ->
        heap_pres s0segs S0_layout LB (bv_unsigned sp) m m' ->
        ((r = 0 /\ LB' = LB)
         \/ (r <> 0 /\ block_ok S0_layout r n /\ (exists p, LB' = (p, r, n) :: LB /\ ~ In p (map blk_id LB))
             /\ exists junk, rw_cells s0segs m' r [CB (Z.to_nat n) junk])) ->
        realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom s0segs)) MD') T) ->
    realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_malloc S0_layout)) fc None m (seg_rom s0segs)) MD) T.
Proof.
  intros until T. intros HI HV Hn AUX SB ST CLO LO ERR MI TP A0 K.
  pose proof HI as [HR HOx0]. pose proof (OWN_vmG _ _ _ HOx0) as HOx.
  assert (HC4 : ZC (eff_class (ps_m s) n) (ps_m s) -> cost (eff_class (ps_m s) n) <= cnt s).
  { intros _. destruct HV as [CNT _]. pose proof (cost_eff_le (ps_m s) n Hn). unfold cnt in *. lia. }
  eapply rz_conseq.
  - apply (S0_malloc_small ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m MD s LB k n lo B errv T T
             HI HC4 (fun tr r s' MD' Hp => small_acvm LB s MD n HOx Hn HC4 k tr r s' MD' HV Hp) Hn AUX SB ST CLO LO ERR MI TP A0).
    + intros s' m' MD' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' HI' VO HV' HO HO' CL PATHN MI' ST' ERR' AUX' HP'.
      apply (K s' LB m' MD' 0 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv'); try assumption. left. split; reflexivity.
    + intros s' m' MD' r p t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' junk HI' VO HV' HO HO' CL MI' ST' ERR' AUX' HP' Hr BOK NIN CB'.
      apply (K s' ((p, r, n) :: LB) m' MD' r t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv'); try assumption.
      right. split; [exact Hr|]. split; [exact BOK|]. split; [exists p; split; [reflexivity| exact NIN]| exists junk; exact CB'].
  - pose proof (raw_malloc_spec_c (map blk_id LB) (vmG MD) n (vmG_frame MD) ltac:(lia)) as HS0.
    eapply t_leaves_if_same; [exact (HS0 s MD HOx)|]. intros MD' HF. exact HF.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem S0_dcv : alloc_dcv_law s0segs S0_layout S0_alloc S0_cover.
Proof.
  unfold alloc_dcv_law. cbn [ai_inv ai_aux ac_vm S0_alloc S0_cover].
  intros until T. intros HI HV AUX SB ST CLO LO ERR MI TP A0 Hn K.
  destruct (Z.lt_ge_cases n MMAP_THRESHOLD) as [SM|BG].
  - eapply S0_malloc_dcv_small; try eassumption. lia.
  - eapply S0_malloc_dcv_big; try eassumption.
    + eapply S0_acvm_le; [exact HV|]. pose proof (ac_cost_le n). lia.
    + split; [exact BG| lia].
Qed.

Theorem S0_freev : alloc_freev_law s0segs S0_layout S0_alloc S0_cover.
Proof.
  unfold alloc_freev_law. cbn [ai_inv ai_aux ac_vm S0_alloc S0_cover].
  intros until T. intros HI HV Hin AUX SB ST CLO LO ERR MI TP A0 K.
  destruct HI as [HR HO]. pose proof (S0_inv_model s LB m MD (conj HR HO)) as [Hh Hl].
  cbn [al_stack S0_layout] in LO. cbn [al_tp S0_layout] in TP.
  rewrite <- (errno_cell_S0 tp TP) in ERR.
  pose proof (rfree_spec_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv
                HR Hin AUX SB ST ltac:(bz_ceil; exact CLO) ltac:(unfold RFREE_STACK; lia) ERR MI TP A0) as HM.
  pose proof (raw_free_spec_c (map blk_id (lb_remove p LB)) (vmG MD) p (vmG_frame MD)) as HS0.
  pose proof (RHEAP_blocks_nodup_proof _ _ _ HR) as NDL.
  pose proof (OWN_vmG _ _ _ HO) as HOx.
  assert (HO' : OWNX (p :: map blk_id (lb_remove p LB)) (vmG MD) s MD).
  { eapply OWNX_perm; [| exact HOx]. eapply perm_remove_id; [exact NDL| exact Hin]. }
  pose proof (mspec_strengthen (OWNX (p :: map blk_id (lb_remove p LB)) (vmG MD)) (raw_free p) _
                (fun s0' mo0 r s' mo' => s0' = s -> mo0 = MD ->
                   S0_acvm k s' mo' /\ exists cs', s' = set_m cs' s /\ FFR (ps_m s) cs') HS0) as HS1.
  assert (HRR : forall sx mox tr ax sx' mox', OWNX (p :: map blk_id (lb_remove p LB)) (vmG MD) sx mox ->
                 tpath nstep (raw_free p sx) mox tr (Ok (ax, sx')) mox' -> sx = s -> mox = MD ->
                 S0_acvm k sx' mox' /\ exists cs', sx' = set_m cs' s /\ FFR (ps_m s) cs').
  { intros sx mox tr ax sx' mox' HO0 Hp -> ->. split; [exact (free_acvm LB s MD p A n HOx Hin k tr ax sx' mox' HV Hp)|].
    cps_destruct (free_classify LB s MD p A n HOx Hin tr ax sx' mox' Hp) as (_ & cs' & Hs' & FR & _). exists cs'. auto. }
  specialize (HS1 HRR s MD HO'). clear HRR.
  eapply rz_conseq.
  - apply (implM_mspec_realizes s0segs (raw_free p) s _ (fun s1' mo1 => s1' = s /\ mo1 = MD) _ (fun _ _ => T) _ MD HM HS1 (conj eq_refl eq_refl) Hh Hl).
    intros [] s' ms' MD' HQm [HQk CL]. specialize (CL eq_refl eq_refl).
    cps_destruct HQm as (u0 & u1 & u2 & ra0 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m' & -> & MI' & ST' & ERR' & AUX' & HP' & _ & _ & HR').
    rewrite (errno_cell_S0 tp TP) in ERR'. rewrite lb_remove_cj in HP', HR'.
    pose proof (OWNX_G _ _ _ _ HQk) as V. unfold vmG in V.
    cps_destruct CL as (HV' & cs' & -> & FR).
    assert (HI2 : S0_inv (set_m cs' s) (lb_remove p LB) m' MD') by (split; [exact HR'| exact (OWN_TrueG _ _ _ _ HQk)]).
    assert (HPP : heap_pres s0segs S0_layout (lb_remove p LB) (bv_unsigned sp) m m') by (apply heap_pres_of_r; exact HP').
    apply (K (set_m cs' s) m' MD' u0 u1 u2 ra0 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14); try assumption.
  - eapply t_leaves_const; [exact (HS1 s MD (conj eq_refl eq_refl))|]. intros MD' HF. exact HF.
Qed.

End ACeilS1.
