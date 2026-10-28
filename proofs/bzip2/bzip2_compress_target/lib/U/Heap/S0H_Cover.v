(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require Import AllocLayout0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocCover AllocTight TreeBridge TightBridge CoverBridge. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require Import S0H_Iface S0H_Tight.
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

Definition cnt (s : PState) : Z := c_avail_meta_count (s_ctx (ps_m s)).

(* [comment removed for export] *)
Definition VMB (k : nat) (MD : Model) : Prop :=
  let h := m_vmmaps MD in
  target_alloc_limit <= vm_limit h
  /\ m_vm_materialized MD = []
  /\ Forall (fun e => 0 < bv_unsigned (snd e) <= 2^27 + 8192 /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= 2^64) (vm_reserved h ++ vm_maps h)
  /\ (length (vm_reserved h ++ vm_maps h) + k <= 100)%nat.

Definition S0_acvm (k : nat) (s : PState) (MD : Model) : Prop := Z.of_nat k <= cnt s /\ VMB k MD.

Definition S0_can (n : Z) (s : PState) (LB : list ablock) (MD : Model) : Prop :=
  exists p s' MD', tpath nstep (raw_malloc n s) MD [] (Ok (Some p, s')) MD'.

(* [comment removed for export] *)
Definition named (o : c21_occ) : list cptr :=
  match o with
  | C21_none | C21_idle => []
  | C21_one f1 => [fst f1]
  | C21_two f1 f2 => [fst f1; fst f2]
  end.

Definition nbids (o : c21_occ) : list bid :=
  match o with
  | C21_none | C21_idle => []
  | C21_one f1 => [f1]
  | C21_two f1 f2 => [f1; f2]
  end.

(* [comment removed for export] *)
Definition NO21 (cs : mstate) : Prop := forall g b, hosts cs b g -> m_sizeclass (MR cs g) <> FILE_CLASS.

(* [comment removed for export] *)
Definition NAMEDIN (cs : mstate) (LB : list ablock) (f : bid) : Prop :=
  INSLOT cs (fst f) /\ exists r, In (f, r, FILE_SZ) LB.

(* [comment removed for export] *)
Definition ndist (o : c21_occ) : Prop := match o with C21_two f1 f2 => f1 <> f2 | _ => True end.

Definition S0_c21 (o : c21_occ) (s : PState) (LB : list ablock) : Prop :=
  match o with
  | C21_none => NO21 (ps_m s)
  | _ => (exists w, (length w <= 1)%nat /\ C21 (named o ++ w) (ps_m s) /\ ndist o) /\ Forall (NAMEDIN (ps_m s) LB) (nbids o)
  end.

Lemma NAMEDIN_mono cs cs' LB LB' f : (INSLOT cs (fst f) -> INSLOT cs' (fst f)) -> (forall x, In x LB -> In x LB') ->
  NAMEDIN cs LB f -> NAMEDIN cs' LB' f.
Proof. intros HI HL [A (r & B)]. split; [exact (HI A)| exists r; exact (HL _ B)]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma VMB_le k k' MD : VMB k MD -> (k' <= k)%nat -> VMB k' MD.
Proof. (cps_intros (A & B & C & D); intros Hk). repeat split; auto. lia. Qed.

Lemma VMB_frame k MD MD' : VMB k MD -> m_vm MD' = m_vm MD -> VMB k MD'.
Proof.
  intros H E. unfold VMB, m_vmmaps, m_vm_materialized in *. rewrite E. exact H.
Qed.

Lemma VMB_grant k MD : VMB (S k) MD -> m_vm_lazy MD = [] ->
  Forall (fun p => bv_unsigned (snd p) <= 2^35) (vm_reserved (m_vmmaps MD) ++ vm_maps (m_vmmaps MD))
  /\ Z.of_nat (length (vm_reserved (m_vmmaps MD) ++ vm_maps (m_vmmaps MD))) <= 1000
  /\ vm_backing_used MD + 2^27 <= vm_limit (m_vmmaps MD).
Proof.
  (cps_intros (LIM & MAT & SZ & LEN); intros HL). split; [| split].
  - eapply Forall_impl; [| exact SZ]. intros e [H _]. lia.
  - lia.
  - eapply Z.le_trans; [| exact LIM]. unfold target_alloc_limit.
    pose proof (vm_backing_used_le MD HL MAT) as B.
    apply Forall_app in SZ as [_ SZ]. rewrite length_app in LEN.
    pose proof (live_bytes_le_len _ (2^27 + 8192) SZ ltac:(lia)) as B2.
    assert (Z.of_nat (length (vm_maps (m_vmmaps MD))) <= 99) by lia. nia.
Qed.

(* [comment removed for export] *)
Lemma VMB_add k MD MD' z len :
  VMB (S k) MD -> 0 < len <= 2^27 + 20 -> mmap_addr_ok len [] z = true ->
  (let h := m_vmmaps MD in
   m_vmmaps MD' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 z, Z_to_bv 64 (mmap_len len)) :: vm_maps h)
                               (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) ->
  m_vm_materialized MD' = m_vm_materialized MD ->
  VMB k MD'.
Proof.
  (cps_intros (LIM & MAT & SZ & LEN); intros Hlen AOK VM' MAT').
  apply mmap_addr_ok_true in AOK as [(A1 & A2 & A3) _]. unfold page_size in A1. bz_ceil.
  pose proof (mmap_len_ge len ltac:(lia)) as MG.
  unfold VMB. rewrite VM', MAT'. cbn [vm_reserved vm_maps vm_limit].
  split; [exact LIM|]. split; [exact MAT|]. split.
  - apply Forall_app in SZ as [SZ1 SZ2]. apply Forall_app. split; [exact SZ1|]. constructor; [| exact SZ2].
    cbn [fst snd]. rewrite !unsigned_lit by lia. lia.
  - rewrite length_app in *. cbn [length] in *. lia.
Qed.

Lemma S0_acvm_frame k s MD MD' : S0_acvm k s MD -> m_vm MD' = m_vm MD -> m_halted MD' = None -> S0_acvm k s MD'.
Proof. intros [A B] E _. split; [exact A| exact (VMB_frame _ _ _ B E)]. Qed.

Lemma S0_acvm_le k k' s MD : S0_acvm k s MD -> (k' <= k)%nat -> S0_acvm k' s MD.
Proof. intros [A B] Hk. split; [lia| exact (VMB_le _ _ _ B Hk)]. Qed.

Lemma ac_cost_le n : (ac_cost n <= 4)%nat /\ (1 <= ac_cost n)%nat.
Proof. unfold ac_cost. destruct (n <? 1024); lia. Qed.

Definition nonest_hi_f (c : Z) : bool := nonest c.
Lemma nonest_hi : forallb nonest_hi_f (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Bits.MI_Cnt.zrange 20 28) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cost_eff_le cs n : 0 <= n < MMAP_THRESHOLD -> cost (eff_class cs n) <= Z.of_nat (ac_cost n).
Proof.
  intros Hn. pose proof (cost_range (eff_class cs n)) as CR. unfold ac_cost.
  destruct (Z.ltb_spec n 1024) as [LT|GE]; [cbn; lia|]. cbn [Z.of_nat Pos.of_succ_nat].
  cps_destruct (eff_class_cases cs n ltac:(lia)) as (EC & SC & FIT).
  assert (S20 : 20 <= eff_class cs n).
  { destruct (Z.lt_ge_cases (eff_class cs n) 20) as [LT20|]; [| lia]. exfalso.
    pose proof (size_class_le (eff_class cs n) 19 ltac:(lia) ltac:(lia) ltac:(lia)) as SL.
    change (size_class 19) with 63 in SL. unfold IB, UNIT in FIT. lia. }
  unfold cost. replace (nonest (eff_class cs n)) with true; [lia|]. symmetry.
  exact (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Bits.MI_Cnt.forallb_zrange nonest_hi_f 20 28 (eff_class cs n) nonest_hi ltac:(lia) ltac:(lia)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CLS.
Variables (LB : list ablock) (s : PState) (MD : Model) (n : Z).
Hypothesis HO : OWNX (map blk_id LB) (vmG MD) s MD.
Hypothesis Hn : 0 <= n < MMAP_THRESHOLD.
Hypothesis HC : ZC (eff_class (ps_m s) n) (ps_m s) -> cost (eff_class (ps_m s) n) <= cnt s.
Let cs := ps_m s.
Let sc := eff_class (ps_m s) n.

Lemma simrel_of : exists L, SIMREL cs L /\ KL L (ps_brk s) MD.
Proof. destruct HO as [(L & SR & HK & _) _]. exists L. auto. Qed.

(* [comment removed for export] *)
Definition ONEMAP (MD MD' : Model) (len z : Z) : Prop :=
  vm_only MD MD' /\ m_vm_lazy MD' = [] /\ m_halted MD' = None
  /\ (let h := m_vmmaps MD in
      m_vmmaps MD' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 z, Z_to_bv 64 (mmap_len len)) :: vm_maps h)
                                  (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h))
  /\ mmap_addr_ok len [] z = true /\ m_vm_materialized MD' = m_vm_materialized MD.

Lemma small_classify tr r s' MD' :
  tpath nstep (raw_malloc n s) MD tr (Ok (r, s')) MD' ->
  tr = [] /\ exists cs', s' = set_m cs' s /\
    ( (r = None /\ MD' = MD /\ AFR (chain sc) (cost sc) None cs cs' /\ ZC sc cs)
    \/ (exists c, r = Some (c, fresh_off cs' c n) /\
          ( (MD' = MD /\ KSUCC (chain sc) (cost sc) sc (OPURE sc cs) cs cs' c)
          \/ (ZC sc cs /\ KSUCC (chain sc) (cost sc) sc (OMMAP sc n cs) cs cs' c /\ exists len z, 0 < len <= 2^20 /\ ONEMAP MD MD' len z))) ).
Proof.
  intros Hp. cps_destruct simrel_of as (L & SR & HK).
  destruct (cmalloc_shape cs L n SR ltac:(lia) HC) as [(cs' & c & E & KS)|(len & K & E & LEN & Z0 & KK)].
  - cps_destruct (raw_malloc_pure_path s MD n cs' c tr r s' MD' E Hp) as (-> & -> & -> & ->).
    split; [reflexivity|]. exists cs'. split; [reflexivity|]. right. exists c. split; [reflexivity|]. left. split; [reflexivity| exact KS].
  - assert (MM : MMAP1 (live_ranges (ps_m s)) (cmalloc (ps_m s) n)
                   (fun t => exists cs', t = SRet (cs', @None cptr) /\ AFR (chain sc) (cost sc) None cs cs')
                   (fun z t => exists cs' c, t = SRet (cs', Some c) /\ KSUCC (chain sc) (cost sc) sc (OMMAP sc n cs) cs cs' c)).
    { exists len, K. split; [exact E|]. split; [lia|]. split; intros z AOK ER; destruct (KK z AOK) as [F S]; [exact (F ER)| exact (S ER)]. }
    cps_destruct (raw_malloc_paths (map blk_id LB) (vmG MD) s MD n _ _
                (fun x => exists cs', x = (cs', @None cptr) /\ AFR (chain sc) (cost sc) None cs cs')
                (fun z x => exists cs' c, x = (cs', Some c) /\ KSUCC (chain sc) (cost sc) sc (OMMAP sc n cs) cs cs' c)
                HO ltac:(lia) MM
                ltac:((intros t; cps_intros (cs' & -> & AF)); eexists; split; [reflexivity| exists cs'; auto])
                ltac:((intros z t; cps_intros (cs' & c & -> & KS)); eexists; split; [reflexivity| exists cs', c; auto])
                tr r s' MD' Hp) as (len' & K' & z & x & E' & Hlen & -> & -> & -> & CASES).
    split; [reflexivity|].
    destruct CASES as [(ERR & (cs' & -> & AF) & ->)|(NERR & (cs' & c & -> & KS) & VO & LZ & HH & VM' & AOK & MAT' & RF)].
    + exists cs'. split; [reflexivity|]. left. cbn. auto.
    + exists cs'. split; [reflexivity|]. right. exists c. cbn [fst snd]. split; [reflexivity|].
      right. split; [exact Z0|]. split; [exact KS|]. rewrite E in E'. injection E' as El _. subst len'.
      exists len, z. split; [lia|]. unfold ONEMAP. auto 10.
Qed.

(* [comment removed for export] *)
Lemma small_acvm k tr r s' MD' :
  S0_acvm (ac_cost n + k) s MD -> tpath nstep (raw_malloc n s) MD tr (Ok (r, s')) MD' -> S0_acvm k s' MD'.
Proof.
  intros [CNT VM] Hp. pose proof (ac_cost_le n) as [C4 C1]. pose proof (cost_eff_le (ps_m s) n Hn) as CE. fold sc in CE. pose proof (cost_range sc) as CR.
  cps_destruct (small_classify tr r s' MD' Hp) as (_ & cs' & -> & CASES).
  assert (KLh : m_vm_lazy MD = []) by (destruct HO as [(L & _ & HK & _) _]; exact (kl_lazy _ _ _ HK)).
  unfold S0_acvm, cnt in *. cbn [ps_m set_m].
  destruct CASES as [(-> & -> & AF & _)|(c & -> & [(-> & (g & bg & idx & AF & _))|(_ & (g & bg & idx & AF & _) & len & z & Hlen & (VO & LZ & HH & VM' & AOK & MAT'))])].
  - pose proof (afr_cnt _ _ _ _ _ AF) as CC. unfold cs in CC. split; [lia| eapply VMB_le; [exact VM| lia]].
  - pose proof (afr_cnt _ _ _ _ _ AF) as CC. unfold cs in CC. split; [lia| eapply VMB_le; [exact VM| lia]].
  - pose proof (afr_cnt _ _ _ _ _ AF) as CC. unfold cs in CC. split; [lia|].
    apply (VMB_add k MD MD' z len); [eapply VMB_le; [exact VM| lia]| unfold MMAP_THRESHOLD in Hn; lia| exact AOK| exact VM'| exact MAT'].
Qed.
End CLS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition NON21SLOT (cs : mstate) (x : cptr) : Prop :=
  exists g bg idx, hosts cs bg g /\ m_sizeclass (MR cs g) <> FILE_CLASS /\ 0 <= idx <= m_last_idx (MR cs g) /\ x = (fst bg, sstart (MR cs g) idx).

Lemma perm_in_iff {A} (l l' : list A) x : Permutation l l' -> (In x l <-> In x l').
Proof. intros P. split; intros H; [eapply Permutation_in; [exact P| exact H]| eapply Permutation_in; [apply Permutation_sym; exact P| exact H]]. Qed.

Lemma c21_pres : forall X X' G G' (s s' : PState) MD MD' C d e (LB LB' : list ablock) W W',
  OWNX X G s MD -> OWNX X' G' s' MD' -> X = map blk_id LB -> X' = map blk_id LB' ->
  AFR C d e (ps_m s) (ps_m s') ->
  (forall x b, hosts (ps_m s') b x -> m_sizeclass (MR (ps_m s') x) = FILE_CLASS -> exists b0, hosts (ps_m s) b0 x) ->
  (forall x, In x (map fst X') -> In x (map fst X) \/ In x W' \/ NON21SLOT (ps_m s') x) ->
  (forall x, In x W -> In x W') ->
  C21 W (ps_m s) -> C21 W' (ps_m s').
Proof.
  intros X X' G G' s s' MD MD' C d e LB LB' W W' [(L & (st & BL & LS & Est & INV & LIVE) & _ & PX) _] [(L' & (st' & BL' & LS' & Est' & INV' & LIVE') & _ & PX') _] -> -> AF NC NB HW HC.
  rewrite <- Est' in *. rewrite <- Est in *.
  apply (proj1 (C21_strip W' st')). apply (C21_frame W W' st st' L L' BL BL' LS LS' C d e INV INV').
  - apply AFR_unstrip. exact AF.
  - exact NC.
  - intros x Hx. rewrite <- LIVE' in Hx. apply (perm_in_iff _ _ x PX') in Hx.
    destruct (NB x Hx) as [H|[H|H]]; [left| right; left; exact H| right; right; exact H].
    rewrite <- LIVE. apply (perm_in_iff _ _ x PX). exact H.
  - exact HW.
  - apply (proj2 (C21_strip W st)). exact HC.
Qed.

(* [comment removed for export] *)
Lemma S0_c21_pres : forall X X' G G' (s s' : PState) MD MD' C d e (LB : list ablock) (nb : list ablock),
  OWNX X G s MD -> OWNX X' G' s' MD' -> X = map blk_id LB -> X' = map blk_id (nb ++ LB) ->
  AFR C d e (ps_m s) (ps_m s') ->
  (forall x b, hosts (ps_m s') b x -> m_sizeclass (MR (ps_m s') x) = FILE_CLASS -> exists b0, hosts (ps_m s) b0 x) ->
  (forall b, In b nb -> NON21SLOT (ps_m s') (fst (blk_id b))) ->
  forall o, S0_c21 o s LB -> S0_c21 o s' (nb ++ LB).
Proof.
  intros X X' G G' s s' MD MD' C d e LB nb HO HO' EX EX' AF NC NB o HC.
  assert (NBX : forall W, forall x, In x (map fst X') -> In x (map fst X) \/ In x W \/ NON21SLOT (ps_m s') x).
  { intros W x Hx. rewrite EX' in Hx. rewrite map_map, map_app, in_app_iff in Hx. destruct Hx as [Hx|Hx].
    - right. right. apply in_map_iff in Hx as (b & <- & Hb). exact (NB b Hb).
    - left. rewrite EX, map_map. exact Hx. }
  destruct o; cbn [S0_c21 named nbids ndist] in *.
  - intros g b Hh Hs. destruct (NC g b Hh Hs) as [b0 H0]. destruct (afr_host _ _ _ _ _ AF b0 g H0) as [_ G0].
    apply (HC g b0 H0). rewrite <- (geo_sc _ _ G0). exact Hs.
  - destruct HC as [(w & Hw & HCw & ND) HI]. split; [| constructor].
    exists w. split; [exact Hw|]. split; [| exact ND]. exact (c21_pres X X' G G' s s' MD MD' C d e LB (nb ++ LB) _ _ HO HO' EX EX' AF NC (NBX _) ltac:(intros x H; exact H) HCw).
  - destruct HC as [(w & Hw & HCw & ND) HI]. split.
    + exists w. split; [exact Hw|]. split; [| exact ND]. exact (c21_pres X X' G G' s s' MD MD' C d e LB (nb ++ LB) _ _ HO HO' EX EX' AF NC (NBX _) ltac:(intros x H; exact H) HCw).
    + eapply Forall_impl; [| exact HI]. intros c Hc. exact (NAMEDIN_mono _ _ _ _ c (INSLOT_afr _ _ _ _ _ _ AF) (fun x Hx => proj2 (in_app_iff nb LB x) (or_intror Hx)) Hc).
  - destruct HC as [(w & Hw & HCw & ND) HI]. split.
    + exists w. split; [exact Hw|]. split; [| exact ND]. exact (c21_pres X X' G G' s s' MD MD' C d e LB (nb ++ LB) _ _ HO HO' EX EX' AF NC (NBX _) ltac:(intros x H; exact H) HCw).
    + eapply Forall_impl; [| exact HI]. intros c Hc. exact (NAMEDIN_mono _ _ _ _ c (INSLOT_afr _ _ _ _ _ _ AF) (fun x Hx => proj2 (in_app_iff nb LB x) (or_intror Hx)) Hc).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition SMALLCL (s : PState) (MD : Model) (n : Z) (r : option bptr) (s' : PState) (MD' : Model) : Prop :=
  let cs := ps_m s in let sc := eff_class cs n in
  exists cs', s' = set_m cs' s /\
    ( (r = None /\ MD' = MD /\ AFR (chain sc) (cost sc) None cs cs' /\ ZC sc cs)
    \/ (exists c, r = Some (c, fresh_off cs' c n) /\
          ( (MD' = MD /\ KSUCC (chain sc) (cost sc) sc (OPURE sc cs) cs cs' c)
          \/ (ZC sc cs /\ KSUCC (chain sc) (cost sc) sc (OMMAP sc n cs) cs cs' c /\ exists len z, 0 < len <= 2^20 /\ ONEMAP MD MD' len z))) ).

Lemma S0_malloc_small : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
      (s : PState) (LB : list ablock) (k : nat) (n lo B : Z) (errv : word) (Tfail Tok : TSet),
    S0_inv s LB m MD ->
    (ZC (eff_class (ps_m s) n) (ps_m s) -> cost (eff_class (ps_m s) n) <= cnt s) ->
    (forall tr r s' MD', tpath nstep (raw_malloc n s) MD tr (Ok (r, s')) MD' -> S0_acvm k s' MD') ->
    0 <= n < MMAP_THRESHOLD ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk s0segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack S0_layout ->
    rw_cells s0segs m (errno_cell S0_layout) [C4 errv] ->
    mem_inv s0segs m ->
    tp = Z_to_bv 64 (al_tp S0_layout) ->
    a0 = Z_to_bv 64 n ->
    (forall (s' : PState) (m' : word -> option byte) (MD' : Model)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word),
        S0_inv s' LB m' MD' -> vm_only MD MD' -> S0_acvm k s' MD' ->
        OWNX (map blk_id LB) (vmG MD) s MD -> OWNX (map blk_id LB) TrueG s' MD' -> SMALLCL s MD n None s' MD' ->
        (exists tr, tpath nstep (raw_malloc n s) MD tr (Ok (@None bptr, s')) MD') ->   (* [comment removed for export] *)
        mem_inv s0segs m' -> stk s0segs m' lo (bv_unsigned sp) -> rw_cells s0segs m' (errno_cell S0_layout) [C4 errv'] -> rauxv_ok m' B ->
        heap_pres s0segs S0_layout LB (bv_unsigned sp) m m' ->
        realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom s0segs)) MD') Tfail) ->
    (forall (s' : PState) (m' : word -> option byte) (MD' : Model) (r : Z) (p : bid)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word) (junk : list byte),
        S0_inv s' ((p, r, n) :: LB) m' MD' -> vm_only MD MD' -> S0_acvm k s' MD' ->
        OWNX (map blk_id LB) (vmG MD) s MD -> OWNX (map blk_id ((p, r, n) :: LB)) TrueG s' MD' -> SMALLCL s MD n (Some p) s' MD' ->
        mem_inv s0segs m' -> stk s0segs m' lo (bv_unsigned sp) -> rw_cells s0segs m' (errno_cell S0_layout) [C4 errv'] -> rauxv_ok m' B ->
        heap_pres s0segs S0_layout LB (bv_unsigned sp) m m' ->
        r <> 0 -> block_ok S0_layout r n -> ~ In p (map blk_id LB) -> rw_cells s0segs m' r [CB (Z.to_nat n) junk] ->
        realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom s0segs)) MD') Tok) ->
    realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_malloc S0_layout)) fc None m (seg_rom s0segs)) MD)
             (t_leaves (raw_malloc n s) MD (fun a _ => if match fst a with None => false | Some _ => true end then Tok else Tfail)).
Proof.
  intros until Tok. intros HI HC4 HVT Hn AUX SB ST CLO LO ERR MI TP A0 Kf Kt.
  destruct HI as [HR HO]. pose proof (S0_inv_model s LB m MD (conj HR HO)) as [Hh Hl].
  cbn [al_stack S0_layout] in LO. cbn [al_tp S0_layout] in TP.
  rewrite <- (errno_cell_S0 tp TP) in ERR.
  pose proof (rmalloc_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv
                HR AUX SB ST ltac:(bz_ceil; exact CLO) ltac:(unfold RMALLOC_STACK; lia) ERR MI TP A0 ltac:(unfold MMAP_THRESHOLD in Hn; lia)) as HM.
  pose proof (raw_malloc_spec_c (map blk_id LB) (vmG MD) n (vmG_frame MD) ltac:(lia)) as HS0.
  pose proof (OWN_vmG _ _ _ HO) as HOv.
  pose proof (mspec_strengthen (OWNX (map blk_id LB) (vmG MD)) (raw_malloc n) _
                (fun sx mo0 r s' mo' => sx = s -> mo0 = MD -> SMALLCL s MD n r s' mo' /\ S0_acvm k s' mo' /\ exists tr, tpath nstep (raw_malloc n s) MD tr (Ok (r, s')) mo') HS0) as HS1.
  assert (HRR : forall sx mox tr ax sx' mox', OWNX (map blk_id LB) (vmG MD) sx mox -> tpath nstep (raw_malloc n sx) mox tr (Ok (ax, sx')) mox' ->
                 sx = s -> mox = MD -> SMALLCL s MD n ax sx' mox' /\ S0_acvm k sx' mox' /\ exists tr0, tpath nstep (raw_malloc n s) MD tr0 (Ok (ax, sx')) mox').
  { intros sx mox tr ax sx' mox' HO0 Hp -> ->. split; [| split; [| exists tr; exact Hp]].
    - destruct (small_classify LB s MD n HO0 Hn HC4 tr ax sx' mox' Hp) as [_ CL]. exact CL.
    - exact (HVT tr ax sx' mox' Hp). }
  specialize (HS1 HRR s MD HOv). clear HRR.
  apply (implM_mspec_realizes s0segs (raw_malloc n) s _ (fun s1 mo1 => s1 = s /\ mo1 = MD) _
           (fun a _ => if match fst a with None => false | Some _ => true end then Tok else Tfail) _ MD HM HS1
           (conj eq_refl eq_refl) Hh Hl).
  intros r s' ms' MD' HQm [HQk CLV]. destruct (CLV eq_refl eq_refl) as (CL & HV' & PATHN).
  cps_destruct HQm as (u0 & u1 & u2 & ra0 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & HP' & _ & _ & Hrr).
  rewrite (errno_cell_S0 tp TP) in ERR'. cbn [fst].
  destruct r as [p|].
  - cps_destruct Hrr as (A & junk & -> & BR & HR' & CH & _). destruct HQk as [HO' _].
    pose proof (OWNX_G _ _ _ _ HO') as V. unfold vmG in V.
    pose proof (RHEAP_blocks_nodup_proof _ _ _ HR') as ND. cbn [map] in ND. inversion ND; subst.
    unfold rblock_range in BR. bz_ceil.
    assert (HI' : S0_inv s' ((p, A, n) :: LB) m' MD') by (split; [exact HR'| cbn [map blk_id fst]; exact (OWN_TrueG _ _ _ _ HO')]).
    assert (HPP : heap_pres s0segs S0_layout LB (bv_unsigned sp) m m') by (apply heap_pres_of_r; exact HP').
    assert (BOK : block_ok S0_layout A n) by (unfold block_ok; cbn [al_img_lo al_img_hi S0_layout]; exact BR).
    apply (Kt s' m' MD' A p u0 u1 u2 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 errv' junk); try assumption; try lia.
    cbn [map blk_id fst]. exact (OWN_TrueG _ _ _ _ HO').
  - destruct Hrr as [-> HR']. pose proof (OWNX_G _ _ _ _ HQk) as V. unfold vmG in V.
    assert (HI' : S0_inv s' LB m' MD') by (split; [exact HR'| exact (OWN_TrueG _ _ _ _ HQk)]).
    assert (HPP : heap_pres s0segs S0_layout LB (bv_unsigned sp) m m') by (apply heap_pres_of_r; exact HP').
    apply (Kf s' m' MD' u0 u1 u2 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 errv'); try assumption.
    exact (OWN_TrueG _ _ _ _ HQk).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition BIGCL' (s : PState) (MD : Model) (n : Z) (r : option bptr) (s' : PState) (MD' : Model) : Prop :=
  let cs := ps_m s in
  (r = None /\ MD' = MD /\ s' = set_m cs s)
  \/ (exists cs' c g bg z, s' = set_m cs' s /\ r = Some (c, fresh_off cs' c n) /\ ONEMAP MD MD' (n + IB + UNIT) z
        /\ AFR (fun x => x = 63) 1 (Some g) cs cs' /\ hosts cs' bg g /\ m_sizeclass (MR cs' g) = 63 /\ m_last_idx (MR cs' g) = 0
        /\ c = (fst bg, sstart (MR cs' g) 0)).

Section BIGCLS.
Variables (LB : list ablock) (s : PState) (MD : Model) (n : Z).
Hypothesis HO : OWNX (map blk_id LB) (vmG MD) s MD.
Hypothesis Hn : MMAP_THRESHOLD <= n <= MAX_REQ_C.
Hypothesis HC : 1 <= cnt s.

Lemma big_MM : exists K, cmalloc (ps_m s) n = SVis (EMmap 0 (n + IB + UNIT) PROT_RW MAPF0) K /\
  MMAP1 (live_ranges (ps_m s)) (cmalloc (ps_m s) n)
    (fun t => t = SRet (ps_m s, @None cptr))
    (fun z t => exists cs' c g bg, t = SRet (cs', Some c) /\ AFR (fun x => x = 63) 1 (Some g) (ps_m s) cs'
                /\ hosts cs' bg g /\ m_sizeclass (MR cs' g) = 63 /\ m_last_idx (MR cs' g) = 0 /\ c = (fst bg, sstart (MR cs' g) 0)).
Proof.
  destruct HO as [(L & SR & HK & _) _].
  cps_destruct (cmalloc_big_shape (ps_m s) L n SR ltac:(lia) ltac:(unfold size_overflows, MAX_REQ_C in *; apply Z.leb_gt; lia) HC) as (K & E & KK).
  exists K. split; [exact E|]. exists (n + IB + UNIT), K. split; [exact E|]. split; [unfold IB, UNIT, MAX_REQ_C, MMAP_THRESHOLD in *; lia|].
  split; intros z AOK ER; destruct (KK z AOK) as [F S]; [exact (F ER)| exact (S ER)].
Qed.

Lemma big_classify tr r s' MD' :
  tpath nstep (raw_malloc n s) MD tr (Ok (r, s')) MD' -> tr = [] /\ BIGCL' s MD n r s' MD'.
Proof.
  intros Hp. cps_destruct big_MM as (K0 & E0 & MM).
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

Lemma big_acvm k tr r s' MD' :
  S0_acvm (S k) s MD -> tpath nstep (raw_malloc n s) MD tr (Ok (r, s')) MD' -> S0_acvm k s' MD'.
Proof.
  intros [CNT VM] Hp. destruct (big_classify tr r s' MD' Hp) as [_ CL].
  unfold S0_acvm, cnt in *.
  destruct CL as [(-> & -> & ->)|(cs' & c & g & bg & z & -> & -> & (VO & LZ & HH & VM' & AOK & MAT') & AF & _)]; cbn [ps_m set_m].
  - split; [lia| eapply VMB_le; [exact VM| lia]].
  - pose proof (afr_cnt _ _ _ _ _ AF) as CC. split; [lia|].
    apply (VMB_add k MD MD' z (n + IB + UNIT)); [exact VM| unfold IB, UNIT, MAX_REQ_C, MMAP_THRESHOLD in *; lia| exact AOK| exact VM'| exact MAT'].
Qed.

(* [comment removed for export] *)
Lemma big_ok_exists k : S0_acvm (S k) s MD -> exists p s' MD', tpath nstep (raw_malloc n s) MD [] (Ok (Some p, s')) MD'.
Proof.
  intros [CNT VM]. cps_destruct big_MM as (K0 & E0 & MM).
  assert (KLh : m_vm_lazy MD = []) by (destruct HO as [(L & _ & HK & _) _]; exact (kl_lazy _ _ _ HK)).
  cps_destruct (VMB_grant k MD VM KLh) as (SZ & LEN & BUD).
  apply (raw_malloc_ok_exists27 (map blk_id LB) (vmG MD) s MD n _ _ (fun _ x => exists c, snd x = Some c) HO ltac:(unfold MMAP_THRESHOLD in Hn; lia) MM
           ltac:((intros z t; cps_intros (cs' & c & g & bg & -> & REST)); eexists; split; [reflexivity| exists c; reflexivity])).
  - intros len K E. rewrite E0 in E. injection E as <- _. unfold IB, UNIT, MAX_REQ_C in *. lia.
  - intros z x Hx. exact Hx.
  - exact SZ.
  - exact LEN.
  - exact BUD.
Qed.
End BIGCLS.

(* [comment removed for export] *)
Lemma S0_leaves_same : forall s LB m MD n (T : TSet), S0_inv s LB m MD -> 0 <= n ->
  t_eq (t_leaves (raw_malloc n s) MD (fun a _ => if match fst a with None => false | Some _ => true end then T else T)) T.
Proof.
  intros s LB m MD n T [HR HO] Hn.
  pose proof (raw_malloc_spec_c (map blk_id LB) (vmG MD) n (vmG_frame MD) Hn) as HS0.
  apply (t_leaves_same (raw_malloc n s) MD (fun a => match fst a with None => false | Some _ => true end) T _ (HS0 s MD (OWN_vmG _ _ _ HO))).
  intros MD' HF. exact HF.
Qed.

Lemma S0_malloc_big' : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
      (s : PState) (LB : list ablock) (k : nat) (n lo B : Z) (errv : word) (Tfail Tok : TSet),
    S0_inv s LB m MD -> S0_acvm (S k) s MD -> MMAP_THRESHOLD <= n <= MAX_REQ_C ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk s0segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack S0_layout ->
    rw_cells s0segs m (errno_cell S0_layout) [C4 errv] ->
    mem_inv s0segs m ->
    tp = Z_to_bv 64 (al_tp S0_layout) ->
    a0 = Z_to_bv 64 n ->
    (forall (s' : PState) (m' : word -> option byte) (MD' : Model)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word),
        S0_inv s' LB m' MD' -> vm_only MD MD' -> S0_acvm k s' MD' ->
        OWNX (map blk_id LB) (vmG MD) s MD -> OWNX (map blk_id LB) TrueG s' MD' -> BIGCL' s MD n None s' MD' ->
        (exists tr, tpath nstep (raw_malloc n s) MD tr (Ok (@None bptr, s')) MD') ->   (* [comment removed for export] *)
        mem_inv s0segs m' -> stk s0segs m' lo (bv_unsigned sp) -> rw_cells s0segs m' (errno_cell S0_layout) [C4 errv'] -> rauxv_ok m' B ->
        heap_pres s0segs S0_layout LB (bv_unsigned sp) m m' ->
        realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom s0segs)) MD') Tfail) ->
    (forall (s' : PState) (m' : word -> option byte) (MD' : Model) (r : Z) (p : bid)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word),
        S0_inv s' ((p, r, n) :: LB) m' MD' -> vm_only MD MD' -> S0_acvm k s' MD' ->
        OWNX (map blk_id LB) (vmG MD) s MD -> OWNX (map blk_id ((p, r, n) :: LB)) TrueG s' MD' -> BIGCL' s MD n (Some p) s' MD' ->
        mem_inv s0segs m' -> stk s0segs m' lo (bv_unsigned sp) -> rw_cells s0segs m' (errno_cell S0_layout) [C4 errv'] -> rauxv_ok m' B ->
        heap_pres s0segs S0_layout LB (bv_unsigned sp) m m' ->
        r <> 0 -> block_ok S0_layout r n -> ~ In p (map blk_id LB) ->
        rw_cells s0segs m' r [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))] ->   (* [comment removed for export] *)
        realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom s0segs)) MD') Tok) ->
    realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_malloc S0_layout)) fc None m (seg_rom s0segs)) MD)
             (t_leaves (raw_malloc n s) MD (fun a _ => if match fst a with None => false | Some _ => true end then Tok else Tfail)).   (* [comment removed for export] *)
Proof.
  intros until Tok. intros HI HV Hn AUX SB ST CLO LO ERR MI TP A0 Kf Kt.
  destruct HI as [HR HO]. pose proof (S0_inv_model s LB m MD (conj HR HO)) as [Hh Hl].
  cbn [al_stack S0_layout] in LO. cbn [al_tp S0_layout] in TP.
  rewrite <- (errno_cell_S0 tp TP) in ERR.
  pose proof (rmalloc_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv
                HR AUX SB ST ltac:(bz_ceil; exact CLO) ltac:(unfold RMALLOC_STACK; lia) ERR MI TP A0 ltac:(unfold MMAP_THRESHOLD, MAX_REQ_C in Hn; lia)) as HM.
  pose proof (raw_malloc_spec_c (map blk_id LB) (vmG MD) n (vmG_frame MD) ltac:(unfold MMAP_THRESHOLD in Hn; lia)) as HS0.
  pose proof (OWN_vmG _ _ _ HO) as HOv.
  assert (HC1 : 1 <= cnt s) by (destruct HV as [CNT _]; lia).
  pose proof (mspec_strengthen (OWNX (map blk_id LB) (vmG MD)) (raw_malloc n) _
                (fun sx mo0 r s' mo' => sx = s -> mo0 = MD -> BIGCL' s MD n r s' mo' /\ S0_acvm k s' mo' /\ exists tr, tpath nstep (raw_malloc n s) MD tr (Ok (r, s')) mo') HS0) as HS1.
  assert (HRR : forall sx mox tr ax sx' mox', OWNX (map blk_id LB) (vmG MD) sx mox -> tpath nstep (raw_malloc n sx) mox tr (Ok (ax, sx')) mox' ->
                 sx = s -> mox = MD -> BIGCL' s MD n ax sx' mox' /\ S0_acvm k sx' mox' /\ exists tr0, tpath nstep (raw_malloc n s) MD tr0 (Ok (ax, sx')) mox').
  { intros sx mox tr ax sx' mox' HO0 Hp -> ->. split; [| split; [| exists tr; exact Hp]].
    - destruct (big_classify LB s MD n HO0 Hn HC1 tr ax sx' mox' Hp) as [_ CL]. exact CL.
    - exact (big_acvm LB s MD n HO0 Hn HC1 k tr ax sx' mox' HV Hp). }
  specialize (HS1 HRR s MD HOv). clear HRR.
  (apply (implM_mspec_realizes s0segs (raw_malloc n) s _ (fun s1 mo1 => s1 = s /\ mo1 = MD) _
             (fun a _ => if match fst a with None => false | Some _ => true end then Tok else Tfail) _ MD HM HS1
             (conj eq_refl eq_refl) Hh Hl)).
  {   intros r s' ms' MD' HQm [HQk CLV]. destruct (CLV eq_refl eq_refl) as (CL & HV' & PATHN).
    cps_destruct HQm as (u0 & u1 & u2 & ra0 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & HP' & _ & _ & Hrr).
    rewrite (errno_cell_S0 tp TP) in ERR'. cbn [fst].
    destruct r as [p|].
    + cps_destruct Hrr as (A & junk & -> & BR & HR' & CH & _ & ZJ). destruct HQk as [HO' _].
      rewrite (ZJ ltac:(clear - Hn; lia)) in CH. unfold b8 in CH.
      pose proof (OWNX_G _ _ _ _ HO') as V. unfold vmG in V.
      pose proof (RHEAP_blocks_nodup_proof _ _ _ HR') as ND. cbn [map] in ND. inversion ND; subst.
      unfold rblock_range in BR. bz_ceil.
      assert (HI' : S0_inv s' ((p, A, n) :: LB) m' MD') by (split; [exact HR'| cbn [map blk_id fst]; exact (OWN_TrueG _ _ _ _ HO')]).
      assert (HPP : heap_pres s0segs S0_layout LB (bv_unsigned sp) m m') by (apply heap_pres_of_r; exact HP').
      assert (BOK : block_ok S0_layout A n) by (unfold block_ok; cbn [al_img_lo al_img_hi S0_layout]; exact BR).
      apply (Kt s' m' MD' A p u0 u1 u2 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 errv'); try assumption; try lia.
      cbn [map blk_id fst]. exact (OWN_TrueG _ _ _ _ HO').
    + destruct Hrr as [-> HR']. pose proof (OWNX_G _ _ _ _ HQk) as V. unfold vmG in V.
      assert (HI' : S0_inv s' LB m' MD') by (split; [exact HR'| exact (OWN_TrueG _ _ _ _ HQk)]).
      assert (HPP : heap_pres s0segs S0_layout LB (bv_unsigned sp) m m') by (apply heap_pres_of_r; exact HP').
      apply (Kf s' m' MD' u0 u1 u2 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 errv'); try assumption.
      exact (OWN_TrueG _ _ _ _ HQk).
  }
Qed.

(* [comment removed for export] *)
Lemma small_ok_exists LB s MD n k :
  OWNX (map blk_id LB) (vmG MD) s MD -> 0 <= n < MMAP_THRESHOLD -> S0_acvm (ac_cost n + k) s MD ->
  exists p s' MD', tpath nstep (raw_malloc n s) MD [] (Ok (Some p, s')) MD'.
Proof.
  intros HO Hn [CNT VM].
  pose proof (cost_eff_le (ps_m s) n Hn) as CE. pose proof (ac_cost_le n) as [C4 C1].
  destruct HO as [(L & SR & HK & PX) [ND HG]].
  destruct (cmalloc_shape (ps_m s) L n SR Hn ltac:(intros _; unfold cnt in CNT; lia)) as [(cs' & c & E & KS)|(len & K & E & LEN & Z0 & KK)].
  - exists (c, fresh_off cs' c n), (set_m cs' s), MD. apply raw_malloc_pure_exists. exact E.
  - assert (KLh : m_vm_lazy MD = []) by exact (kl_lazy _ _ _ HK).
    cps_destruct (VMB_grant (pred (ac_cost n + k)) MD ltac:(replace (S (pred (ac_cost n + k))) with (ac_cost n + k)%nat by lia; exact VM) KLh) as (SZ & LENb & BUD).
    set (sc := eff_class (ps_m s) n) in *.
    assert (MM : MMAP1 (live_ranges (ps_m s)) (cmalloc (ps_m s) n)
                   (fun t => exists cs', t = SRet (cs', @None cptr) /\ AFR (chain sc) (cost sc) None (ps_m s) cs')
                   (fun z t => exists cs' c, t = SRet (cs', Some c) /\ KSUCC (chain sc) (cost sc) sc (OMMAP sc n (ps_m s)) (ps_m s) cs' c)).
    { exists len, K. split; [exact E|]. split; [lia|]. split; intros z AOK ER; destruct (KK z AOK) as [F S]; [exact (F ER)| exact (S ER)]. }
    apply (raw_malloc_ok_exists27 (map blk_id LB) (vmG MD) s MD n _ _ (fun _ x => exists c, snd x = Some c)
             ltac:(split; [exists L; auto| split; [exact ND| exact HG]]) ltac:(lia) MM).
    + (intros z t; cps_intros (cs' & c & -> & _)). eexists. split; [reflexivity|]. exists c. reflexivity.
    + intros len' K' E'. rewrite E in E'. injection E' as <- _. lia.
    + intros z x Hx. exact Hx.
    + exact SZ.
    + exact LENb.
    + exact BUD.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma chain_21 sc : chain sc FILE_CLASS -> sc = FILE_CLASS.
Proof. unfold chain, FILE_CLASS. lia. Qed.

Lemma NC_none C d cs cs' : AFR C d None cs cs' ->
  forall x b, hosts cs' b x -> m_sizeclass (MR cs' x) = FILE_CLASS -> exists b0, hosts cs b0 x.
Proof.
  intros AF x b Hh Hs. destruct (afr_new _ _ _ _ _ AF b x Hh) as [H0|(_ & HE & _)]; [exists b; exact H0|].
  destruct HE as [HM|HE]; [| discriminate]. exfalso. rewrite Hs in HM. unfold midclass, FILE_CLASS in HM. lia.
Qed.

Lemma NC_notC C d e cs cs' : AFR C d e cs cs' -> ~ C FILE_CLASS ->
  forall x b, hosts cs' b x -> m_sizeclass (MR cs' x) = FILE_CLASS -> exists b0, hosts cs b0 x.
Proof.
  intros AF NC x b Hh Hs. destruct (afr_new _ _ _ _ _ AF b x Hh) as [H0|(HC & _ & _)]; [exists b; exact H0|].
  exfalso. apply NC. rewrite <- Hs. exact HC.
Qed.

Lemma stc_36 : size_to_class 36 = 2. Proof. vm_compute. reflexivity. Qed.
Lemma stc_5104 : size_to_class 5104 = 29. Proof. vm_compute. reflexivity. Qed.
Lemma stc_55768 : size_to_class 55768 = 43. Proof. vm_compute. reflexivity. Qed.
Lemma stc_64144 : size_to_class 64144 = 43. Proof. vm_compute. reflexivity. Qed.
Lemma stc_1264 : size_to_class 1264 = 21. Proof. vm_compute. reflexivity. Qed.

Lemma eff_foreign cs n : c21_foreign n -> n < MMAP_THRESHOLD -> eff_class cs n <> FILE_CLASS.
Proof.
  intros HF Hn. unfold c21_foreign, MMAP_THRESHOLD_C, MMAP_THRESHOLD in *.
  assert (Hn0 : 0 <= n < MMAP_THRESHOLD) by (unfold MMAP_THRESHOLD; lia).
  cps_destruct (eff_class_cases cs n Hn0) as (EC & _ & _). unfold FILE_CLASS.
  destruct HF as [->|[->|[->|[->|HF]]]]; [rewrite stc_36 in EC| rewrite stc_5104 in EC| rewrite stc_55768 in EC| rewrite stc_64144 in EC| lia]; lia.
Qed.

(* [comment removed for export] *)
Lemma c21_after_fail LB s s' MD MD' G' C d :
  OWNX (map blk_id LB) (vmG MD) s MD -> OWNX (map blk_id LB) G' s' MD' -> AFR C d None (ps_m s) (ps_m s') ->
  forall o, S0_c21 o s LB -> S0_c21 o s' LB.
Proof.
  intros HO HO' AF o HC. change LB with ([] ++ LB).
  apply (S0_c21_pres _ _ _ _ s s' MD MD' _ _ _ LB [] HO HO' eq_refl eq_refl AF (NC_none _ _ _ _ AF)); [intros b []| exact HC].
Qed.

Lemma c21_after_same LB s s' MD MD' G' :
  OWNX (map blk_id LB) (vmG MD) s MD -> OWNX (map blk_id LB) G' s' MD' -> ps_m s' = ps_m s ->
  forall o, S0_c21 o s LB -> S0_c21 o s' LB.
Proof.
  intros HO HO' E o HC. change LB with ([] ++ LB).
  apply (S0_c21_pres _ _ _ _ s s' MD MD' (fun _ => False) 0 None LB [] HO HO' eq_refl eq_refl); [| | intros b []| exact HC].
  - rewrite E. apply AFR_of_PF; [lia| apply PF_refl].
  - rewrite E. intros x b Hh _. exists b. exact Hh.
Qed.

Lemma c21_after_ok LB s s' MD MD' G' C d g bg idx (p : bid) r n :
  OWNX (map blk_id LB) (vmG MD) s MD -> OWNX (map blk_id ((p, r, n) :: LB)) G' s' MD' -> AFR C d (Some g) (ps_m s) (ps_m s') ->
  hosts (ps_m s') bg g -> m_sizeclass (MR (ps_m s') g) <> FILE_CLASS -> 0 <= idx <= m_last_idx (MR (ps_m s') g) ->
  fst p = (fst bg, sstart (MR (ps_m s') g) idx) -> ~ C FILE_CLASS ->
  forall o, S0_c21 o s LB -> S0_c21 o s' ((p, r, n) :: LB).
Proof.
  intros HO HO' AF Hh SC Hidx Ep NC o HC. change ((p, r, n) :: LB) with ([(p, r, n)] ++ LB).
  apply (S0_c21_pres _ _ _ _ s s' MD MD' _ _ _ LB [(p, r, n)] HO HO' eq_refl eq_refl AF (NC_notC _ _ _ _ _ AF NC)); [| exact HC].
  intros b [<-|[]]. cbn [blk_id fst]. exists g, bg, idx. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma S0_malloc_cover : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
      (s : PState) (LB : list ablock) (k : nat) (n lo B : Z) (errv : word) (Tf To : TSet),
    S0_inv s LB m MD -> S0_acvm (ac_cost n + k) s MD -> S0_can n s LB MD ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk s0segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack S0_layout ->
    rw_cells s0segs m (errno_cell S0_layout) [C4 errv] ->
    mem_inv s0segs m ->
    tp = Z_to_bv 64 (al_tp S0_layout) ->
    a0 = Z_to_bv 64 n -> 0 <= n < MMAP_THRESHOLD_C ->
    (forall (s' : PState) (m' : word -> option byte) (MD' : Model)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word),
        S0_inv s' LB m' MD' -> vm_only MD MD' -> S0_acvm k s' MD' ->
        mem_inv s0segs m' -> stk s0segs m' lo (bv_unsigned sp) -> rw_cells s0segs m' (errno_cell S0_layout) [C4 errv'] -> rauxv_ok m' B ->
        heap_pres s0segs S0_layout LB (bv_unsigned sp) m m' ->
        (forall o, S0_c21 o s LB -> n <> FILE_SZ -> S0_c21 o s' LB) ->
        realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom s0segs)) MD') Tf) ->
    (forall (s' : PState) (m' : word -> option byte) (MD' : Model) (r : Z) (p : bid)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word) (junk : list byte),
        S0_inv s' ((p, r, n) :: LB) m' MD' -> vm_only MD MD' -> S0_acvm k s' MD' ->
        mem_inv s0segs m' -> stk s0segs m' lo (bv_unsigned sp) -> rw_cells s0segs m' (errno_cell S0_layout) [C4 errv'] -> rauxv_ok m' B ->
        heap_pres s0segs S0_layout LB (bv_unsigned sp) m m' ->
        r <> 0 -> block_ok S0_layout r n -> ~ In p (map blk_id LB) -> rw_cells s0segs m' r [CB (Z.to_nat n) junk] ->
        (forall o, S0_c21 o s LB -> c21_foreign n -> S0_c21 o s' ((p, r, n) :: LB)) ->
        realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom s0segs)) MD') To) ->
    t_incl Tf To ->
    realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_malloc S0_layout)) fc None m (seg_rom s0segs)) MD) To.
Proof.
  intros until To. intros HI HV CAN AUX SB ST CLO LO ERR MI TP A0 Hn Kf Kt INCL.
  unfold MMAP_THRESHOLD_C in Hn.
  eapply (rz_conseq) with (T := t_leaves (raw_malloc n s) MD (fun a _ => if match fst a with None => false | Some _ => true end then To else Tf)).
  - pose proof HI as [_ HOx]. apply OWN_vmG in HOx.
    assert (HC4 : ZC (eff_class (ps_m s) n) (ps_m s) -> cost (eff_class (ps_m s) n) <= cnt s) by (intros _; destruct HV as [CNT _]; pose proof (cost_eff_le (ps_m s) n ltac:(unfold MMAP_THRESHOLD; lia)); unfold cnt in *; lia).
    apply (S0_malloc_small ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m MD s LB k n lo B errv Tf To
             HI HC4 (fun tr r s' MD' Hp => small_acvm LB s MD n HOx ltac:(unfold MMAP_THRESHOLD; lia) HC4 k tr r s' MD' HV Hp) ltac:(unfold MMAP_THRESHOLD; lia) AUX SB ST CLO LO ERR MI TP A0).
    + intros s' m' MD' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' HI' VO HV' HO HO' CL PATHN MI' ST' ERR' AUX' HP'.
      apply (Kf s' m' MD' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv'); try assumption.
      intros o HC _. cps_destruct CL as (cs' & Es & [(_ & _ & AF & _)|(c & Ep & _)]); [| discriminate].
      assert (E' : ps_m s' = cs') by (rewrite Es; reflexivity). rewrite <- E' in AF.
      exact (c21_after_fail LB s s' MD MD' _ _ _ HO HO' AF o HC).
    + intros s' m' MD' r p t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' junk HI' VO HV' HO HO' CL MI' ST' ERR' AUX' HP' Hr BOK NIN CB'.
      apply (Kt s' m' MD' r p t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' junk); try assumption.
      intros o HC HF. cps_destruct CL as (cs' & Es & [(EN & _)|(c & Ep & CASES)]); [discriminate|]. injection Ep as ->.
      assert (KS : exists O, KSUCC (chain (eff_class (ps_m s) n)) (cost (eff_class (ps_m s) n)) (eff_class (ps_m s) n) O (ps_m s) cs' c).
      { destruct CASES as [(_ & KS)|(_ & KS & _)]; eexists; exact KS. }
      cps_destruct KS as (O & g & bg & idx & AF & Hh & SC & Hidx & Ec & _).
      assert (E' : ps_m s' = cs') by (rewrite Es; reflexivity). rewrite <- E' in AF, Hh, SC, Hidx, Ec.
      pose proof (eff_foreign (ps_m s) n HF ltac:(unfold MMAP_THRESHOLD; lia)) as NE.
      apply (c21_after_ok LB s s' MD MD' _ _ _ g bg idx _ r n HO HO' AF Hh ltac:(rewrite SC; exact NE) Hidx Ec
               ltac:(intros HC21; apply NE; exact (chain_21 _ HC21)) o HC).
  - intros tr. rewrite <- (t_leaves_cover_pair (raw_malloc n s) MD Tf To ltac:(cps_destruct CAN as (p & s' & MD' & Hp); exists p, s', MD'; exact Hp) INCL tr).
    unfold t_leaves. split; cps_intros (a & M & P & T); exists a, M; (split; [exact P|]); destruct (fst a); exact T.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma S0_malloc_bigc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
      (s : PState) (LB : list ablock) (k : nat) (n lo B : Z) (errv : word) (T : TSet),
    S0_inv s LB m MD -> S0_acvm (S k) s MD -> S0_can n s LB MD -> MMAP_THRESHOLD_C <= n <= MAX_REQ_C ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk s0segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack S0_layout ->
    rw_cells s0segs m (errno_cell S0_layout) [C4 errv] ->
    mem_inv s0segs m ->
    tp = Z_to_bv 64 (al_tp S0_layout) ->
    a0 = Z_to_bv 64 n ->
    (forall (s' : PState) (m' : word -> option byte) (MD' : Model)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word),
        S0_inv s' LB m' MD' -> vm_only MD MD' -> S0_acvm k s' MD' ->
        mem_inv s0segs m' -> stk s0segs m' lo (bv_unsigned sp) -> rw_cells s0segs m' (errno_cell S0_layout) [C4 errv'] -> rauxv_ok m' B ->
        heap_pres s0segs S0_layout LB (bv_unsigned sp) m m' ->
        (forall o, S0_c21 o s LB -> S0_c21 o s' LB) ->
        realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom s0segs)) MD') T) ->
    (forall (s' : PState) (m' : word -> option byte) (MD' : Model) (r : Z) (p : bid)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word) (junk : list byte),
        S0_inv s' ((p, r, n) :: LB) m' MD' -> vm_only MD MD' -> S0_acvm k s' MD' ->
        mem_inv s0segs m' -> stk s0segs m' lo (bv_unsigned sp) -> rw_cells s0segs m' (errno_cell S0_layout) [C4 errv'] -> rauxv_ok m' B ->
        heap_pres s0segs S0_layout LB (bv_unsigned sp) m m' ->
        r <> 0 -> block_ok S0_layout r n -> ~ In p (map blk_id LB) -> rw_cells s0segs m' r [CB (Z.to_nat n) junk] ->
        (forall o, S0_c21 o s LB -> S0_c21 o s' ((p, r, n) :: LB)) ->
        realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom s0segs)) MD') T) ->
    realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_malloc S0_layout)) fc None m (seg_rom s0segs)) MD) T.
Proof.
  intros until T. intros HI HV CAN Hn AUX SB ST CLO LO ERR MI TP A0 Kf Kt.
  unfold MMAP_THRESHOLD_C in Hn.
  eapply rz_conseq; [| exact (S0_leaves_same s LB m MD n T HI ltac:(lia))].   (* [comment removed for export] *)
  apply (S0_malloc_big' ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m MD s LB k n lo B errv T T
           HI HV ltac:(unfold MMAP_THRESHOLD; lia) AUX SB ST CLO LO ERR MI TP A0).
  - intros s' m' MD' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' HI' VO HV' HO HO' CL PATHN MI' ST' ERR' AUX' HP'.
    apply (Kf s' m' MD' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv'); try assumption.
    intros o HC. destruct CL as [(_ & _ & Es)|(cs' & c & g & bg & z & Es & Ep & _)]; [| discriminate].
    exact (c21_after_same LB s s' MD MD' _ HO HO' ltac:(rewrite Es; reflexivity) o HC).
  - intros s' m' MD' r p t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' HI' VO HV' HO HO' CL MI' ST' ERR' AUX' HP' Hr BOK NIN CB'.
    apply (Kt s' m' MD' r p t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' (repeat (Z_to_bv 8 0) (Z.to_nat n))); try assumption.
    intros o HC. destruct CL as [(EN & _)|(cs' & c & g & bg & z & Es & Ep & _ & AF & Hh & SC & LI & Ec)]; [discriminate|]. injection Ep as ->.
    assert (E' : ps_m s' = cs') by (rewrite Es; reflexivity). rewrite <- E' in AF, Hh, SC, LI, Ec.
    apply (c21_after_ok LB s s' MD MD' _ _ _ g bg 0 _ r n HO HO' AF Hh ltac:(rewrite SC; unfold FILE_CLASS; lia) ltac:(rewrite LI; lia) Ec
             ltac:(unfold FILE_CLASS; lia) o HC).
Qed.

Lemma S0_malloc_bigzc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
      (s : PState) (LB : list ablock) (k : nat) (n lo B : Z) (errv : word) (T : TSet),
    S0_inv s LB m MD -> S0_acvm (S k) s MD -> S0_can n s LB MD -> MMAP_THRESHOLD_C <= n <= MAX_REQ_C ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk s0segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack S0_layout ->
    rw_cells s0segs m (errno_cell S0_layout) [C4 errv] ->
    mem_inv s0segs m ->
    tp = Z_to_bv 64 (al_tp S0_layout) ->
    a0 = Z_to_bv 64 n ->
    (forall (s' : PState) (m' : word -> option byte) (MD' : Model)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word),
        S0_inv s' LB m' MD' -> vm_only MD MD' -> S0_acvm k s' MD' ->
        mem_inv s0segs m' -> stk s0segs m' lo (bv_unsigned sp) -> rw_cells s0segs m' (errno_cell S0_layout) [C4 errv'] -> rauxv_ok m' B ->
        heap_pres s0segs S0_layout LB (bv_unsigned sp) m m' ->
        (forall o, S0_c21 o s LB -> S0_c21 o s' LB) ->
        realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom s0segs)) MD') T) ->
    (forall (s' : PState) (m' : word -> option byte) (MD' : Model) (r : Z) (p : bid)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word),
        S0_inv s' ((p, r, n) :: LB) m' MD' -> vm_only MD MD' -> S0_acvm k s' MD' ->
        mem_inv s0segs m' -> stk s0segs m' lo (bv_unsigned sp) -> rw_cells s0segs m' (errno_cell S0_layout) [C4 errv'] -> rauxv_ok m' B ->
        heap_pres s0segs S0_layout LB (bv_unsigned sp) m m' ->
        r <> 0 -> block_ok S0_layout r n -> ~ In p (map blk_id LB) ->
        rw_cells s0segs m' r [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))] ->
        (forall o, S0_c21 o s LB -> S0_c21 o s' ((p, r, n) :: LB)) ->
        realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom s0segs)) MD') T) ->
    realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_malloc S0_layout)) fc None m (seg_rom s0segs)) MD) T.
Proof.
  intros until T. intros HI HV CAN Hn AUX SB ST CLO LO ERR MI TP A0 Kf Kt.
  unfold MMAP_THRESHOLD_C in Hn.
  eapply rz_conseq; [| exact (S0_leaves_same s LB m MD n T HI ltac:(lia))].   (* [comment removed for export] *)
  apply (S0_malloc_big' ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m MD s LB k n lo B errv T T
           HI HV ltac:(unfold MMAP_THRESHOLD; lia) AUX SB ST CLO LO ERR MI TP A0).
  - intros s' m' MD' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' HI' VO HV' HO HO' CL PATHN MI' ST' ERR' AUX' HP'.
    apply (Kf s' m' MD' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv'); try assumption.
    intros o HC. destruct CL as [(_ & _ & Es)|(cs' & c & g & bg & z & Es & Ep & _)]; [| discriminate].
    exact (c21_after_same LB s s' MD MD' _ HO HO' ltac:(rewrite Es; reflexivity) o HC).
  - intros s' m' MD' r p t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' HI' VO HV' HO HO' CL MI' ST' ERR' AUX' HP' Hr BOK NIN CB'.
    apply (Kt s' m' MD' r p t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv'); try assumption.
    intros o HC. destruct CL as [(EN & _)|(cs' & c & g & bg & z & Es & Ep & _ & AF & Hh & SC & LI & Ec)]; [discriminate|]. injection Ep as ->.
    assert (E' : ps_m s' = cs') by (rewrite Es; reflexivity). rewrite <- E' in AF, Hh, SC, LI, Ec.
    apply (c21_after_ok LB s s' MD MD' _ _ _ g bg 0 _ r n HO HO' AF Hh ltac:(rewrite SC; unfold FILE_CLASS; lia) ltac:(rewrite LI; lia) Ec
             ltac:(unfold FILE_CLASS; lia) o HC).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma none_idle s LB : S0_c21 C21_none s LB -> S0_c21 C21_idle s LB.
Proof.
  intros NO. cbn. split; [| constructor]. exists []. split; [cbn; lia|]. cbn. split; [| exact I].
  constructor.
  - intros g b Hh Hs. exfalso. exact (NO g b Hh Hs).
  - intros g g' b b' Hh _ Hs _. exfalso. exact (NO g b Hh Hs).
  - intros g b i Hh Hs _. exfalso. exact (NO g b Hh Hs).
Qed.

Lemma create21 LB s s' MD MD' G' O (p : bid) r n c :
  OWNX (map blk_id LB) (vmG MD) s MD -> OWNX (map blk_id ((p, r, n) :: LB)) G' s' MD' ->
  KSUCC (chain FILE_CLASS) (cost FILE_CLASS) FILE_CLASS O (ps_m s) (ps_m s') c -> fst p = c ->
  (forall g li, O (ps_m s') g li -> OPURE FILE_CLASS (ps_m s) (ps_m s') g li \/ OMMAP FILE_CLASS n (ps_m s) (ps_m s') g li) ->
  NO21 (ps_m s) -> 1 <= n <= 4076 ->
  (forall W, C21 (c :: W) (ps_m s')) /\ INSLOT (ps_m s') c.
Proof.
  (intros [(L & (st & BL & LS & Est & INV & LIVE) & _ & PX) _] [(L' & (st' & BL' & LS' & Est' & INV' & LIVE') & _ & PX') _]; cps_intros (g & bg & idx & AF & Hh & SC & Hidx & Ec & HO); intros Ep OO NO Hn).
  assert (LI : m_last_idx (MR (ps_m s') g) = 2).
  { destruct (OO _ _ HO) as [[[[b0 H0] _]|[E HB]]|OM].
    - exfalso. destruct (afr_host _ _ _ _ _ AF b0 g H0) as [_ G]. apply (NO g b0 H0). rewrite <- (geo_sc _ _ G). exact SC.
    - exfalso. pose proof (nonest_mmap FILE_CLASS (usage (ps_m s) FILE_CLASS) nonest21). lia.
    - unfold OMMAP in OM. rewrite <- Est in OM. change (usage (strip st) FILE_CLASS) with (usage st FILE_CLASS) in OM.
      rewrite (no21_usage0 x0 st L BL LS INV ltac:(rewrite <- Est in NO; exact NO)) in OM. exact (newcnt21 n _ Hn OM). }
  split.
  - intros W. rewrite <- Est' in *. rewrite <- Est in *. rewrite Ec. apply (proj1 (C21_strip _ st')).
    apply (C21_create W st st' L L' BL BL' LS LS' (cost FILE_CLASS) g bg idx INV INV' (AFR_unstrip _ _ _ _ _ AF) NO Hh SC LI ltac:(lia)).
    intros x Hx. rewrite <- LIVE' in Hx. apply (perm_in_iff _ _ x PX') in Hx. cbn [map blk_id fst] in Hx. rewrite Ep, Ec in Hx.
    destruct Hx as [<-|Hx]; [right; reflexivity| left]. rewrite <- LIVE. apply (perm_in_iff _ _ x PX). exact Hx.
  - exists g, bg, idx. rewrite LI in Hidx. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma eff21_range cs n : 0 < n < MMAP_THRESHOLD -> eff_class cs n = FILE_CLASS -> 1 <= n <= 4076.
Proof.
  intros Hn E. cps_destruct (eff_class_cases cs n ltac:(lia)) as (_ & _ & FIT). rewrite E in FIT.
  change (UNIT * size_class FILE_CLASS) with 1344 in FIT. unfold IB in FIT. lia.
Qed.

Lemma S0_malloc_sysc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
      (s : PState) (LB : list ablock) (k : nat) (n lo B : Z) (errv : word) (Tok : TSet),
    S0_inv s LB m MD -> S0_sys_ok s LB n MD -> S0_acvm (ac_cost n + k) s MD -> S0_c21 C21_none s LB ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk s0segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack S0_layout ->
    rw_cells s0segs m (errno_cell S0_layout) [C4 errv] -> mem_inv s0segs m -> tp = Z_to_bv 64 (al_tp S0_layout) ->
    a0 = Z_to_bv 64 n -> 0 < n <= MAX_REQ_C ->
    (forall (s' : PState) (m' : word -> option byte) (MD' : Model) (r : Z) (p : bid)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word) (junk : list byte),
        S0_inv s' ((p, r, n) :: LB) m' MD' -> vm_only MD MD' -> S0_acvm k s' MD' -> S0_c21 C21_idle s' ((p, r, n) :: LB) ->
        mem_inv s0segs m' -> stk s0segs m' lo (bv_unsigned sp) -> rw_cells s0segs m' (errno_cell S0_layout) [C4 errv'] -> rauxv_ok m' B ->
        heap_pres s0segs S0_layout LB (bv_unsigned sp) m m' ->
        r <> 0 -> block_ok S0_layout r n -> ~ In p (map blk_id LB) -> rw_cells s0segs m' r [CB (Z.to_nat n) junk] ->
        realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom s0segs)) MD') Tok) ->
    realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_malloc S0_layout)) fc None m (seg_rom s0segs)) MD) Tok.
Proof.
  intros until Tok. intros HI NF HV NO AUX SB ST CLO LO ERR MI TP A0 Hn Kt.
  (* [comment removed for export] *)
  eapply rz_conseq; [| exact (S0_leaves_same s LB m MD n Tok HI ltac:(lia))].
  destruct (Z.lt_ge_cases n MMAP_THRESHOLD) as [SMALL|BIG].
  - idtac.
    + pose proof HI as [_ HOx]. apply OWN_vmG in HOx.
      assert (HC4 : ZC (eff_class (ps_m s) n) (ps_m s) -> cost (eff_class (ps_m s) n) <= cnt s) by (intros _; destruct HV as [CNT _]; pose proof (cost_eff_le (ps_m s) n ltac:(lia)); unfold cnt in *; lia).
      apply (S0_malloc_small ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m MD s LB k n lo B errv Tok Tok
               HI HC4 (fun tr r s' MD' Hp => small_acvm LB s MD n HOx ltac:(lia) HC4 k tr r s' MD' HV Hp) ltac:(lia) AUX SB ST CLO LO ERR MI TP A0).
      * intros s' m' MD' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' HI' VO HV' HO HO' CL PATHN MI' ST' ERR' AUX' HP'.
        exfalso. destruct PATHN as [tr0 Hp0]. exact (NF tr0 s' MD' Hp0).
      * intros s' m' MD' r p t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' junk HI' VO HV' HO HO' CL MI' ST' ERR' AUX' HP' Hr BOK NIN CB'.
        apply (Kt s' m' MD' r p t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' junk); try assumption.
        cps_destruct CL as (cs' & Es & [(EN & _)|(c & Ep & CASES)]); [discriminate|]. injection Ep as Ep.
        assert (KS : exists O, KSUCC (chain (eff_class (ps_m s) n)) (cost (eff_class (ps_m s) n)) (eff_class (ps_m s) n) O (ps_m s) cs' c
                        /\ forall g li, O cs' g li -> OPURE (eff_class (ps_m s) n) (ps_m s) cs' g li \/ OMMAP (eff_class (ps_m s) n) n (ps_m s) cs' g li).
        { destruct CASES as [(_ & KS)|(_ & KS & _)]; eexists; (split; [exact KS| intros; auto]). }
        cps_destruct KS as (O & KS & OO).
        assert (E' : ps_m s' = cs') by (rewrite Es; reflexivity). rewrite <- E' in KS, OO.
        destruct (Z.eq_dec (eff_class (ps_m s) n) FILE_CLASS) as [E21|NE].
        -- rewrite E21 in KS, OO.
           destruct (create21 LB s s' MD MD' _ O p r n c HO HO' KS ltac:(rewrite Ep; reflexivity) OO NO (eff21_range (ps_m s) n ltac:(lia) E21)) as [CW IS].
           cbn. split; [| constructor]. exists [c]. split; [cbn; lia|]. split; [exact (CW [])| exact I].
        -- apply none_idle. cps_destruct KS as (g & bg & idx & AF & Hh & SC & Hidx & Ec & _).
           apply (c21_after_ok LB s s' MD MD' _ _ _ g bg idx _ r n HO HO' AF Hh ltac:(rewrite SC; exact NE) Hidx ltac:(rewrite Ep; exact Ec)
                    ltac:(intros HC21; apply NE; exact (chain_21 _ HC21)) C21_none NO).
  - apply (S0_malloc_big' ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m MD s LB k n lo B errv Tok Tok
             HI (S0_acvm_le (ac_cost n + k) (S k) s MD HV ltac:(pose proof (ac_cost_le n); lia)) ltac:(lia) AUX SB ST CLO LO ERR MI TP A0).
    + intros s' m' MD' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' HI' VO HV' HO HO' CL PATHN MI' ST' ERR' AUX' HP'.
      exfalso. destruct PATHN as [tr0 Hp0]. exact (NF tr0 s' MD' Hp0).
    + intros s' m' MD' r p t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' HI' VO HV' HO HO' CL MI' ST' ERR' AUX' HP' Hr BOK NIN CB'.
      apply (Kt s' m' MD' r p t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' (repeat (Z_to_bv 8 0) (Z.to_nat n))); try assumption.
      apply none_idle. destruct CL as [(EN & _)|(cs' & c & g & bg & z & Es & Ep & _ & AF & Hh & SC & LI & Ec)]; [discriminate|]. injection Ep as ->.
      assert (E' : ps_m s' = cs') by (rewrite Es; reflexivity). rewrite <- E' in AF, Hh, SC, LI, Ec.
      apply (c21_after_ok LB s s' MD MD' _ _ _ g bg 0 _ r n HO HO' AF Hh ltac:(rewrite SC; unfold FILE_CLASS; lia) ltac:(rewrite LI; lia) Ec
               ltac:(unfold FILE_CLASS; lia) C21_none NO).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma one_head LB s MD f1 :
  OWNX (map blk_id LB) (vmG MD) s MD -> S0_c21 (C21_one f1) s LB ->
  exists g, active (ps_m s) FILE_CLASS = Some g /\ (m_avail (MR (ps_m s) g) <> 0 \/ m_freed (MR (ps_m s) g) <> 0)
            /\ (exists b, hosts (ps_m s) b g) /\ m_sizeclass (MR (ps_m s) g) = FILE_CLASS.
Proof.
  intros [(L & (st & BL & LS & Est & INV & LIVE) & _ & PX) _] [(w & Hw & HC & _) HI].
  apply Forall_inv in HI. destruct HI as [(g & b & i1 & Hh & Hs & Hi1 & Ef) _]. cbn [named] in HC.
  rewrite <- Est in *.
  cps_destruct (c21_unnamed st x0 L BL LS g b (fst f1) w i1 INV Hh Hw Hi1 Ef) as (i & Hi & NW).
  destruct (c21_head st L BL LS (fst f1 :: w) INV (proj2 (C21_strip _ st) HC) g b i Hh Hs Hi NW) as [HA NZ].
  exists g. split; [exact HA|]. split; [exact NZ|]. split; [exists b; exact Hh| exact Hs].
Qed.

Lemma eff_1264 cs g : active cs FILE_CLASS = Some g -> eff_class cs FILE_SZ = FILE_CLASS.
Proof. intros HA. unfold eff_class, FILE_SZ. rewrite stc_1264. change 21 with FILE_CLASS. rewrite HA. reflexivity. Qed.

Lemma S0_malloc_fastc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
      (s : PState) (LB : list ablock) (k : nat) (f1 : bid) (lo B : Z) (errv : word) (T : TSet),
    S0_inv s LB m MD -> S0_c21 (C21_one f1) s LB -> S0_acvm k s MD ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk s0segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack S0_layout ->
    rw_cells s0segs m (errno_cell S0_layout) [C4 errv] ->
    mem_inv s0segs m ->
    tp = Z_to_bv 64 (al_tp S0_layout) ->
    a0 = Z_to_bv 64 FILE_SZ ->
    (forall (s' : PState) (m' : word -> option byte) (r : Z) (p : bid)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word) (junk : list byte),
        S0_inv s' ((p, r, FILE_SZ) :: LB) m' MD -> S0_acvm k s' MD ->
        mem_inv s0segs m' -> stk s0segs m' lo (bv_unsigned sp) -> rw_cells s0segs m' (errno_cell S0_layout) [C4 errv'] -> rauxv_ok m' B ->
        heap_pres s0segs S0_layout LB (bv_unsigned sp) m m' ->
        r <> 0 -> block_ok S0_layout r FILE_SZ -> ~ In p (map blk_id LB) -> rw_cells s0segs m' r [CB (Z.to_nat FILE_SZ) junk] ->
        S0_c21 (C21_two f1 p) s' ((p, r, FILE_SZ) :: LB) ->
        realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom s0segs)) MD) T) ->
    realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_malloc S0_layout)) fc None m (seg_rom s0segs)) MD) T.
Proof.
  intros until T. intros HI H1 HV AUX SB ST CLO LO ERR MI TP A0 K.
  pose proof HI as [_ HOx]. apply OWN_vmG in HOx.
  cps_destruct (one_head LB s MD f1 HOx H1) as (g21 & HA & NZ & [b21 Hh21] & SC21).
  pose proof (eff_1264 (ps_m s) g21 HA) as E21.
  assert (NZC : ~ ZC (eff_class (ps_m s) FILE_SZ) (ps_m s)).
  { rewrite E21. intros [Z0|(m0 & HA' & A0' & F0')]; [congruence|]. rewrite HA in HA'. injection HA' as <-. unfold MR in NZ. lia. }
  assert (PUREV : forall tr r s' MD', tpath nstep (raw_malloc FILE_SZ s) MD tr (Ok (r, s')) MD' -> S0_acvm k s' MD').
  { intros tr r s' MD' Hp. cps_destruct (small_classify LB s MD FILE_SZ HOx ltac:(unfold FILE_SZ, MMAP_THRESHOLD; lia) ltac:(intros Z0; exfalso; exact (NZC Z0)) tr r s' MD' Hp)
      as (_ & cs' & -> & CASES).
    destruct CASES as [(_ & _ & _ & Z0)|(c & _ & CASES)]; [exfalso; exact (NZC Z0)|].
    destruct CASES as [[-> KS]|(Z0 & _)]; [| exfalso; exact (NZC Z0)].
    cps_destruct KS as (g & bg & idx & AF & _ & _ & _ & _ & HO).
    rewrite E21 in HO. destruct HO as [[_ CE]|[_ HB]]; [| exfalso; pose proof (nonest_mmap FILE_CLASS (usage (ps_m s) FILE_CLASS) nonest21); lia].
    destruct HV as [CNT VM]. split; [unfold cnt in *; cbn; rewrite CE; exact CNT| exact VM]. }
  eapply (rz_conseq) with (T := t_leaves (raw_malloc FILE_SZ s) MD (fun a _ => if match fst a with None => false | Some _ => true end then T else T)).
  - apply (S0_malloc_small ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m MD s LB k FILE_SZ lo B errv T T
             HI ltac:(intros Z0; exfalso; exact (NZC Z0)) PUREV ltac:(unfold FILE_SZ, MMAP_THRESHOLD; lia) AUX SB ST CLO LO ERR MI TP A0).
    + intros s' m' MD' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' HI' VO HV' HO HO' CL PATHN MI' ST' ERR' AUX' HP'.
      exfalso. cps_destruct CL as (cs' & Es & [(_ & _ & _ & Z0)|(c & Ep & _)]); [exact (NZC Z0)| discriminate].
    + intros s' m' MD' r p t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' junk HI' VO HV' HO HO' CL MI' ST' ERR' AUX' HP' Hr BOK NIN CB'.
      cps_destruct CL as (cs' & Es & [(EN & _)|(c & Ep & CASES)]); [discriminate|].
      destruct CASES as [[-> KS]|(Z0 & _)]; [| exfalso; exact (NZC Z0)].
      apply (K s' m' r p t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' junk); try assumption.
      (* [comment removed for export] *)
      injection Ep as Ep. assert (E' : ps_m s' = cs') by (rewrite Es; reflexivity). rewrite <- E' in KS.
      rewrite E21 in KS. cps_destruct KS as (g & bg & idx & AF & Hh & SC & Hidx & Ec & HO0).
      assert (OLD : exists b0, hosts (ps_m s) b0 g).
      { destruct HO0 as [[OLD _]|[_ HB]]; [exact OLD|]. exfalso. pose proof (nonest_mmap FILE_CLASS (usage (ps_m s) FILE_CLASS) nonest21). lia. }
      destruct H1 as [(w & Hw & HC & _) HI1].
      assert (NC : forall x b, hosts (ps_m s') b x -> m_sizeclass (MR (ps_m s') x) = FILE_CLASS -> exists b0, hosts (ps_m s) b0 x).
      { intros x b Hx Hsx. destruct (afr_new _ _ _ _ _ AF b x Hx) as [H0|(_ & HE & _)]; [exists b; exact H0|].
        destruct HE as [HM|HE]; [exfalso; rewrite Hsx in HM; unfold midclass, FILE_CLASS in HM; lia|]. injection HE as ->. exact OLD. }
      cbn [S0_c21 named nbids ndist]. split.
      * exists w. split; [exact Hw|]. cbn [app]. split.
        2:{ intros ->. apply NIN. pose proof (Forall_inv HI1) as [_ (r1 & Hr1)]. apply in_map_iff. exists (p, r1, FILE_SZ). split; [reflexivity| exact Hr1]. }
        apply (c21_pres _ _ _ _ s s' MD MD _ _ _ LB ((p, r, FILE_SZ) :: LB) (fst f1 :: w) (fst f1 :: fst p :: w) HO HO' eq_refl eq_refl AF NC).
        -- intros x Hx. cbn [map blk_id fst] in Hx. destruct Hx as [<-|Hx]; [right; left; right; left; reflexivity| left; exact Hx].
        -- intros x [<-|Hx]; [left; reflexivity| right; right; exact Hx].
        -- exact HC.
      * constructor; [| constructor; [| constructor]].
        -- apply Forall_inv in HI1. exact (NAMEDIN_mono _ _ LB ((p, r, FILE_SZ) :: LB) f1 (INSLOT_afr _ _ _ _ _ _ AF) (fun x Hx => or_intror Hx) HI1).
        -- split; [| exists r; left; reflexivity]. exists g, bg, idx. rewrite Ep.
           destruct OLD as [b0 H0]. destruct (afr_host _ _ _ _ _ AF b0 g H0) as [H0' G].
           pose proof (c21_three _ _ HC g b0 H0 ltac:(rewrite <- (geo_sc _ _ G); exact SC)) as L2. rewrite <- (geo_li _ _ G) in L2. rewrite L2 in Hidx. auto.
  - intros tr. unfold t_leaves. split.
    + cps_intros (a & M & P & HT). destruct (fst a); exact HT.
    + intros HT. destruct HI as [_ HO0].
      destruct HO0 as [(L & SR & HK & PX) [ND HG]].
      destruct (cmalloc_shape (ps_m s) L FILE_SZ SR ltac:(unfold FILE_SZ, MMAP_THRESHOLD; lia) ltac:(intros Z0; exfalso; exact (NZC Z0))) as [(cs' & c & E & KS)|(len & Kx & E & LEN & Z0 & KK)]; [| exfalso; exact (NZC Z0)].
      exists (Some (c, fresh_off cs' c FILE_SZ), set_m cs' s), MD. split; [apply raw_malloc_pure_exists; exact E| exact HT].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma S0_can_intro n k s LB m MD : S0_inv s LB m MD -> S0_acvm (ac_cost n + k) s MD ->
  (c21_foreign n \/ (n = FILE_SZ /\ S0_c21 C21_idle s LB)) -> S0_can n s LB MD.
Proof.
  intros [_ HO] HV HN. apply OWN_vmG in HO. unfold S0_can.
  assert (Hn : (0 <= n < MMAP_THRESHOLD) \/ (MMAP_THRESHOLD <= n <= MAX_REQ_C)).
  { unfold c21_foreign, FILE_SZ, MMAP_THRESHOLD_C, MMAP_THRESHOLD in *. lia. }
  destruct Hn as [SM|BG].
  - exact (small_ok_exists LB s MD n k HO SM HV).
  - pose proof (ac_cost_le n) as [_ C1].
    apply (big_ok_exists LB s MD n HO BG ltac:(destruct HV as [CNT _]; lia) k). eapply S0_acvm_le; [exact HV| lia].
Qed.

(* [comment removed for export] *)
Lemma c21_unnamed0 st X L BL LS g b (w : list cptr) :
  INVL X st L BL LS -> hosts st b g -> (length w <= 1)%nat ->
  exists i, 0 <= i <= 2 /\ ~ In (fst b, sstart (MR st g) i) w.
Proof.
  intros INV Hh Hw.
  pose proof (stride_ge X st LS (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) b g Hh) as [SG _].
  destruct w as [|x [|y l]]; [exists 0; split; [lia| intros []]| | cbn in Hw; lia].
  destruct (aptr_eq_dec x (fst b, sstart (MR st g) 0)) as [->|NE].
  - exists 1. split; [lia|]. intros [E|[]]. injection E as E. unfold sstart in E. unfold UNIT in SG. nia.
  - exists 0. split; [lia|]. intros [E|[]]. exact (NE E).
Qed.

Lemma S0_malloc_firstc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
      (s : PState) (LB : list ablock) (k : nat) (lo B : Z) (errv : word) (Tf To : TSet),
    S0_inv s LB m MD -> S0_c21 C21_idle s LB -> S0_acvm (S k) s MD ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk s0segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack S0_layout ->
    rw_cells s0segs m (errno_cell S0_layout) [C4 errv] ->
    mem_inv s0segs m ->
    tp = Z_to_bv 64 (al_tp S0_layout) ->
    a0 = Z_to_bv 64 FILE_SZ ->
    (forall (s' : PState) (m' : word -> option byte) (MD' : Model)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word),
        S0_inv s' LB m' MD' -> vm_only MD MD' -> S0_acvm k s' MD' ->
        mem_inv s0segs m' -> stk s0segs m' lo (bv_unsigned sp) -> rw_cells s0segs m' (errno_cell S0_layout) [C4 errv'] -> rauxv_ok m' B ->
        heap_pres s0segs S0_layout LB (bv_unsigned sp) m m' -> S0_c21 C21_idle s' LB ->
        realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom s0segs)) MD') Tf) ->
    (forall (s' : PState) (m' : word -> option byte) (MD' : Model) (r : Z) (p : bid)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word) (junk : list byte),
        S0_inv s' ((p, r, FILE_SZ) :: LB) m' MD' -> vm_only MD MD' -> S0_acvm k s' MD' ->
        mem_inv s0segs m' -> stk s0segs m' lo (bv_unsigned sp) -> rw_cells s0segs m' (errno_cell S0_layout) [C4 errv'] -> rauxv_ok m' B ->
        heap_pres s0segs S0_layout LB (bv_unsigned sp) m m' ->
        r <> 0 -> block_ok S0_layout r FILE_SZ -> ~ In p (map blk_id LB) -> rw_cells s0segs m' r [CB (Z.to_nat FILE_SZ) junk] ->
        S0_c21 (C21_one p) s' ((p, r, FILE_SZ) :: LB) ->
        realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom s0segs)) MD') To) ->
    t_incl Tf To ->
    realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_malloc S0_layout)) fc None m (seg_rom s0segs)) MD) To.
Proof.
  intros until To. intros HI HID HV AUX SB ST CLO LO ERR MI TP A0 Kf Kt INCL.
  pose proof HI as [_ HOx]. apply OWN_vmG in HOx.
  assert (Hn : 0 <= FILE_SZ < MMAP_THRESHOLD) by (unfold FILE_SZ, MMAP_THRESHOLD; lia).
  assert (HV' : S0_acvm (ac_cost FILE_SZ + k) s MD) by exact HV.
  assert (E21 : eff_class (ps_m s) FILE_SZ = FILE_CLASS).
  { cps_destruct (eff_class_cases (ps_m s) FILE_SZ Hn) as (EC & _ & _). unfold FILE_SZ in EC. rewrite stc_1264 in EC.
    unfold FILE_CLASS. destruct EC as [EC|(EC & EV & _)]; [exact EC|]. cbv in EV. discriminate. }
  assert (HC4 : ZC (eff_class (ps_m s) FILE_SZ) (ps_m s) -> cost (eff_class (ps_m s) FILE_SZ) <= cnt s).
  { intros _. destruct HV as [CNT _]. pose proof (cost_eff_le (ps_m s) FILE_SZ Hn) as CE. unfold cnt in *. cbn in CE. lia. }
  eapply (rz_conseq) with (T := t_leaves (raw_malloc FILE_SZ s) MD (fun a _ => if match fst a with None => false | Some _ => true end then To else Tf)).
  - apply (S0_malloc_small ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m MD s LB k FILE_SZ lo B errv Tf To
             HI HC4 (fun tr r s' MD' Hp => small_acvm LB s MD FILE_SZ HOx Hn HC4 k tr r s' MD' HV' Hp) Hn AUX SB ST CLO LO ERR MI TP A0).
    + intros s' m' MD' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' HI' VO HVk HO HO' CL PATHN MI' ST' ERR' AUX' HP'.
      apply (Kf s' m' MD' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv'); try assumption.
      cps_destruct CL as (cs' & Es & [(_ & _ & AF & _)|(c & Ep & _)]); [| discriminate].
      assert (E' : ps_m s' = cs') by (rewrite Es; reflexivity). rewrite <- E' in AF.
      exact (c21_after_fail LB s s' MD MD' _ _ _ HO HO' AF C21_idle HID).
    + intros s' m' MD' r p t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' junk HI' VO HVk HO HO' CL MI' ST' ERR' AUX' HP' Hr BOK NIN CB'.
      apply (Kt s' m' MD' r p t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' junk); try assumption.
      cps_destruct CL as (cs' & Es & [(EN & _)|(c & Ep & CASES)]); [discriminate|]. injection Ep as Ep.
      assert (E' : ps_m s' = cs') by (rewrite Es; reflexivity).
      destruct HID as [(w & Hw & HC & _) _].
      assert (KS : exists O, KSUCC (chain FILE_CLASS) (cost FILE_CLASS) FILE_CLASS O (ps_m s) (ps_m s') c
                 /\ (forall g li, O (ps_m s') g li -> OPURE FILE_CLASS (ps_m s) (ps_m s') g li \/ OMMAP FILE_CLASS FILE_SZ (ps_m s) (ps_m s') g li)
                 /\ ((exists g li, O (ps_m s') g li /\ OMMAP FILE_CLASS FILE_SZ (ps_m s) (ps_m s') g li /\ ~ OPURE FILE_CLASS (ps_m s) (ps_m s') g li) -> ZC FILE_CLASS (ps_m s))).
      { rewrite <- E21. rewrite E'. destruct CASES as [(_ & KS)|(Z0 & KS & _)]; eexists; (split; [exact KS|]); split; intros; auto.
        cps_destruct H as (g & li & HO1 & _ & NP). exfalso. exact (NP HO1). }
      cps_destruct KS as (O & KS & OO & ZZ).
      cps_pose KS as (g & bg & idx & AF & Hh & SC & Hidx & Ec & HO0).
      (* [comment removed for export] *)
      destruct (Classical_Prop.classic (exists b0, hosts (ps_m s) b0 g)) as [OLD|NEW].
      * (* [comment removed for export] *)
        assert (NC : forall x b, hosts (ps_m s') b x -> m_sizeclass (MR (ps_m s') x) = FILE_CLASS -> exists b0, hosts (ps_m s) b0 x).
        { intros x b Hx Hsx. destruct (afr_new _ _ _ _ _ AF b x Hx) as [H0|(_ & HE & _)]; [exists b; exact H0|].
          destruct HE as [HM|HE]; [exfalso; rewrite Hsx in HM; unfold midclass, FILE_CLASS in HM; lia|]. injection HE as ->. exact OLD. }
        cbn [S0_c21 named nbids ndist]. split.
        -- exists w. split; [exact Hw|]. cbn [app]. split; [| exact I].
           apply (c21_pres _ _ _ _ s s' MD MD' _ _ _ LB ((p, r, FILE_SZ) :: LB) w (fst p :: w) HO HO' eq_refl eq_refl AF NC).
           ++ intros x Hx. cbn [map blk_id fst] in Hx. destruct Hx as [<-|Hx]; [right; left; left; reflexivity| left; exact Hx].
           ++ intros x Hx. right. exact Hx.
           ++ exact HC.
        -- constructor; [| constructor]. split; [| exists r; left; reflexivity]. exists g, bg, idx. rewrite Ep.
           destruct OLD as [b0 H0]. destruct (afr_host _ _ _ _ _ AF b0 g H0) as [H0' G].
           pose proof (c21_three _ _ HC g b0 H0 ltac:(rewrite <- (geo_sc _ _ G); exact SC)) as L2. rewrite <- (geo_li _ _ G) in L2. rewrite L2 in Hidx. auto.
      * (* [comment removed for export] *)
        assert (NO : NO21 (ps_m s)).
        { intros g' b' Hh' Hs'. destruct HO as [(L & (st & BL & LS & Est & INV & LIVE) & _ & PX) _].
          rewrite <- Est in Hh', Hs', HC.
          cps_destruct (c21_unnamed0 st x0 L BL LS g' b' w INV Hh' Hw) as (i & Hi & NW).
          destruct (c21_head st L BL LS w INV (proj2 (C21_strip _ st) HC) g' b' i Hh' Hs' Hi NW) as [HA NZ].
          (* [comment removed for export] *)
          destruct (OO _ _ HO0) as [[[OLD _]|[_ HB]]|OM]; [exact (NEW OLD)| |].
          - pose proof (nonest_mmap FILE_CLASS (usage (ps_m s) FILE_CLASS) nonest21). lia.
          - assert (Z0 : ZC FILE_CLASS (ps_m s)).
            { apply ZZ. exists g, (m_last_idx (MR (ps_m s') g)). split; [exact HO0|]. split; [exact OM|]. intros [[OLD _]|[_ HB]]; [exact (NEW OLD)|].
              pose proof (nonest_mmap FILE_CLASS (usage (ps_m s) FILE_CLASS) nonest21). lia. }
            rewrite <- Est in Z0. destruct Z0 as [Z0|(m0 & HA' & A0' & F0')]; [change (active (strip st)) with (active st) in Z0; congruence|].
            change (active (strip st) FILE_CLASS) with (active st FILE_CLASS) in HA'. rewrite HA in HA'. injection HA' as <-.
            change (get_meta_rec (strip st) g') with (MR st g') in A0', F0'. lia. }
        destruct (create21 LB s s' MD MD' _ O p r FILE_SZ c HO HO' KS ltac:(rewrite Ep; reflexivity) OO NO ltac:(unfold FILE_SZ; lia)) as [CW IS].
        cbn [S0_c21 named nbids ndist]. split; [| constructor; [split; [rewrite Ep; exact IS| exists r; left; reflexivity]| constructor]].
        exists w. split; [exact Hw|]. cbn [app]. rewrite Ep. split; [exact (CW w)| exact I].
  - intros tr. rewrite <- (t_leaves_cover_pair (raw_malloc FILE_SZ s) MD Tf To
                              ltac:(cps_destruct (small_ok_exists LB s MD FILE_SZ k HOx Hn HV') as (p & s' & MD' & Hp); exists p, s', MD'; exact Hp) INCL tr).
    unfold t_leaves. split; cps_intros (a & M & P & T); exists a, M; (split; [exact P|]); destruct (fst a); exact T.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma VMB_remove k MD MD' a n :
  VMB k MD -> In (a, n) (vm_maps (m_vmmaps MD)) ->
  (let h := m_vmmaps MD in
   m_vmmaps MD' = mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) a) (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) ->
  m_vm_materialized MD' = [] -> VMB k MD'.
Proof.
  (cps_intros (V1 & V2 & V3 & V4); intros Hin VM' MAT'). unfold VMB. rewrite VM'. cbn [vm_limit vm_reserved vm_maps].
  split; [exact V1|]. split; [exact MAT'|]. split.
  - apply Forall_app in V3 as [F1 F2]. apply Forall_app. split; [exact F1| apply Forall_map_remove; exact F2].
  - rewrite length_app in V4 |- *. pose proof (map_remove_length_in (vm_maps (m_vmmaps MD)) a n Hin). lia.
Qed.

Section FCLS.
Variables (LB : list ablock) (s : PState) (MD : Model) (p : bid) (A n : Z).
Hypothesis HO : OWNX (map blk_id LB) (vmG MD) s MD.
Hypothesis Hin : In (p, A, n) LB.

Lemma live_of : forall L, Permutation (map fst (map blk_id LB)) (ld_live L) -> In (fst p) (ld_live L).
Proof.
  intros L PX. eapply Permutation_in; [exact PX|]. rewrite map_map. apply in_map_iff. exists (p, A, n). split; [reflexivity| exact Hin].
Qed.

(* [comment removed for export] *)
Lemma free_classify tr r s' MD' :
  tpath nstep (raw_free p s) MD tr (Ok (r, s')) MD' ->
  tr = [] /\ exists cs', s' = set_m cs' s /\ FFR (ps_m s) cs' /\
    (MD' = MD
     \/ (vm_only MD MD' /\ m_vm_lazy MD' = [] /\ m_halted MD' = None /\ (m_vm_materialized MD = [] -> m_vm_materialized MD' = [])
         /\ exists aw nw, In (aw, nw) (vm_maps (m_vmmaps MD)) /\
            let h := m_vmmaps MD in
            m_vmmaps MD' = mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) aw) (maps_subtract (vm_noaccess h) (bv_unsigned aw) (bv_unsigned aw + bv_unsigned nw))
                             (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h))).
Proof.
  intros Hp. destruct HO as [(L & SR & HK & PX) [Hnd HG]].
  pose proof (live_of L PX) as Hc.
  unfold raw_free, mbind, mget in Hp.
  tp_bind Hp. cps_destruct Hp as (tr1 & [s0 s0'] & mo1 & tr2 & H1 & H2 & ->).
  apply tpath_ret_inv in H1 as (E1 & -> & ->). injection E1 as <- <-. cbn [fst snd] in H2.
  tp_bind H2. cps_destruct H2 as (tr3 & [st' s1] & mo2 & tr4 & H3 & H4 & ->).
  destruct (cfree_shape (ps_m s) L (fst p) SR Hc) as [(cs' & E & FR)|(a & l0 & K & E & HinG & Hpos & KOK)].
  - rewrite E in H3. cbn [membed] in H3. apply tpath_ret_inv in H3 as (E3 & -> & ->). injection E3 as E3a E3b. subst st' s1.
    unfold mupd in H4. apply tpath_ret_inv in H4 as (E4 & -> & ->). injection E4 as E4a E4b. subst r s'.
    split; [reflexivity|]. exists cs'. split; [reflexivity|]. split; [exact FR|]. left. reflexivity.
  - rewrite E in H3. cbn [membed] in H3. unfold mbind in H3.
    tp_bind H3. cps_destruct H3 as (tr5 & [z s2] & mo3 & tr6 & H5 & H6 & ->).
    unfold ev_step in H5. unfold mbind in H5.
    tp_bind H5. cps_destruct H5 as (tr7 & [a7 s3] & mo4 & tr8 & H7 & H8 & ->).
    unfold msys in H7. apply tpath_enode in H7 as (rsp & NS & ER).
    cps_pose (kl_groups _ _ _ HK a l0 HinG) as (A1 & A2 & A3 & A4 & A5 & A6).
    pose proof KStep.alloc_ceiling_lt as ACL. pose proof (mmap_len_ge l0 ltac:(lia)) as ML. pose proof (mmap_len_aligned l0) as MA.
    rewrite round_up_pg_eq in E, Hpos, NS, ER. fold (mmap_len l0) in E, Hpos, NS, ER.
    assert (MM : mmap_len (mmap_len l0) = mmap_len l0) by (apply mmap_len_of_aligned; [lia| exact MA]).
    assert (HAS : map_has (vm_maps (m_vmmaps MD)) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len (mmap_len l0))) = true).
    { rewrite MM. unfold map_has. apply existsb_exists. exists (went a (mmap_len l0)). split; [exact A5|]. unfold went, wz. cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity. }
    cps_pose (nstep_munmap_exact a (mmap_len l0) MD rsp mo4 tr7 ltac:(lia) ltac:(unfold PGSZ in A3; exact A3) ltac:(lia) ltac:(rewrite MM; unfold TASK_SIZE; lia) HAS NS)
      as (-> & VO & LZ & HH & MAT & DX & VM4).
    rewrite DX in ER. injection ER as -> ->.
    apply tpath_ret_inv in H8 as (E8 & -> & ->). injection E8 as E8a E8b. subst z s2.
    cbn [fst snd] in H6, H4.
    cps_destruct (KOK 0 eq_refl) as (cs' & EK & FR).
    rewrite EK in H6. cbn [membed] in H6.
    apply tpath_ret_inv in H6 as (E6 & -> & ->). injection E6 as E6a E6b. subst st' s1.
    unfold mupd in H4. apply tpath_ret_inv in H4 as (E4 & -> & ->). injection E4 as E4a E4b. subst r s'.
    split; [reflexivity|]. exists cs'. split; [reflexivity|]. split; [exact FR|]. right.
    split; [exact VO|]. split; [apply LZ; exact (kl_lazy _ _ _ HK)|]. split; [rewrite HH; exact (kl_halt _ _ _ HK)|]. split; [exact MAT|].
    exists (Z_to_bv 64 a), (Z_to_bv 64 (mmap_len l0)). split; [exact A5|].
    rewrite VM4, MM. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma free_acvm k tr r s' MD' :
  S0_acvm k s MD -> tpath nstep (raw_free p s) MD tr (Ok (r, s')) MD' -> S0_acvm k s' MD'.
Proof.
  intros [CNT VM] Hp. cps_destruct (free_classify tr r s' MD' Hp) as (_ & cs' & -> & FR & CASES).
  unfold S0_acvm, cnt in *. cbn [ps_m set_m]. rewrite (ffr_cnt _ _ FR). split; [exact CNT|].
  destruct CASES as [->|(VO & LZ & HH & MAT & aw & nw & Hin' & VM')]; [exact VM|].
  apply (VMB_remove k MD MD' aw nw VM Hin' VM'). apply MAT. exact (proj1 (proj2 VM)).
Qed.
End FCLS.

(* [comment removed for export] *)
Lemma c21_free : forall (LB : list ablock) (s s' : PState) MD MD' G' (p : bid) A n,
  OWNX (map blk_id LB) (vmG MD) s MD -> OWNX (map blk_id (lb_remove p LB)) G' s' MD' ->
  In (p, A, n) LB -> List.NoDup (map blk_id LB) -> FFR (ps_m s) (ps_m s') ->
  forall o, S0_c21 o s LB -> S0_c21 (c21_after_free o p n) s' (lb_remove p LB).
Proof.
  intros LB s s' MD MD' G' p A n [(L & (st & BL & LS & Est & INV & LIVE) & _ & PX) [Hnd _]] [(L' & (st' & BL' & LS' & Est' & INV' & LIVE') & _ & PX') _] Hin NDL FR o HC.
  assert (FR' : FFR st st').
  { rewrite <- Est, <- Est' in FR. apply (proj2 (FFR_strip_l _ _)), (proj2 (FFR_strip_r _ _)) in FR. exact FR. }
  assert (CS : forall W, C21 W (ps_m s) -> C21 W st) by (intros W H; rewrite <- Est in H; exact (proj2 (C21_strip W st) H)).
  assert (CS' : forall W, C21 W st' -> C21 W (ps_m s')) by (intros W H; rewrite <- Est'; exact (proj1 (C21_strip W st') H)).
  assert (IS0 : forall x, INSLOT (ps_m s) x -> INSLOT st x) by (intros x H; rewrite <- Est in H; exact (proj2 (INSLOT_strip st x) H)).
  assert (IS' : forall x, INSLOT st' x -> INSLOT (ps_m s') x) by (intros x H; rewrite <- Est'; exact (proj1 (INSLOT_strip st' x) H)).
  (* [comment removed for export] *)
  pose proof (perm_remove_id p LB A n NDL Hin) as PR.
  assert (PXc : Permutation (fst p :: map fst (map blk_id (lb_remove p LB))) (map bslot BL)).
  { rewrite <- LIVE. eapply Permutation_trans; [| exact PX].
    change (fst p :: map fst (map blk_id (lb_remove p LB))) with (map fst (p :: map blk_id (lb_remove p LB))). apply Permutation_map. apply Permutation_sym. exact PR. }
  assert (Hc : In (fst p) (map bslot BL)) by (eapply Permutation_in; [exact PXc| left; reflexivity]).
  assert (NDc : List.NoDup (fst p :: map fst (map blk_id (lb_remove p LB)))).
  { apply (Permutation_NoDup (Permutation_sym PXc)). apply NoDup_ListNoDup. exact (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))). }
  assert (HBL : forall x, In x (map bslot BL') -> In x (map bslot BL) /\ x <> fst p).
  { intros x Hx. rewrite <- LIVE' in Hx. apply (perm_in_iff _ _ x PX') in Hx. split.
    - eapply Permutation_in; [exact PXc|]. right. exact Hx.
    - intros ->. inversion NDc; subst. apply H1. exact Hx. }
  assert (INS : forall W f r, C21 W st -> In (f, r, FILE_SZ) (lb_remove p LB) -> INSLOT (ps_m s) (fst f) -> INSLOT (ps_m s') (fst f)).
  { intros W f r HCW Hf HI. apply IS'. apply (INSLOT_free W st st' L L' BL BL' LS LS' (fst f) INV INV' FR' HCW); [| exact (IS0 _ HI)].
    rewrite <- LIVE'. apply (perm_in_iff _ _ _ PX'). rewrite map_map. apply in_map_iff. exists (f, r, FILE_SZ). split; [reflexivity| exact Hf]. }
  assert (KEEP : forall f r, In (f, r, FILE_SZ) LB -> f <> p -> In (f, r, FILE_SZ) (lb_remove p LB)).
  { intros f r Hf NE. apply (lb_remove_keep p LB (f, r, FILE_SZ)); [exact Hf| exact NE]. }
  assert (FRAME : forall W W', (forall x, In x W -> x <> fst p -> In x W') -> C21 W (ps_m s) -> C21 W' (ps_m s')).
  { intros W W' HW HCW. apply CS'. exact (C21_free W W' st st' L L' BL BL' LS LS' (fst p) INV INV' FR' Hc HBL HW (CS _ HCW)). }
  destruct o as [| |f1|f1 f2]; cbn [c21_after_free S0_c21 named nbids ndist] in *.
  - (* [comment removed for export] *) intros g b Hh. rewrite <- Est' in Hh |- *. rewrite <- Est in HC. destruct FR' as [FH FG _ _].
    change (hosts st' b g) in Hh. change (m_sizeclass (MR st' g) <> FILE_CLASS).
    rewrite (geo_sc _ _ (FG _ _ Hh)). exact (HC g b (FH _ _ Hh)).
  - (* [comment removed for export] *) destruct HC as [(w & Hw & HCw & _) _]. split; [| constructor]. exists w. split; [exact Hw|]. split; [| exact I]. cbn [app] in *.
    apply (FRAME w w); [intros x Hx _; exact Hx| exact HCw].
  - (* [comment removed for export] *) destruct HC as [(w & Hw & HCw & _) HI]. apply Forall_inv in HI. destruct HI as [HI1 (r1 & Hr1)].
    destruct (bid_eqb_spec p f1) as [->|NE]; cbn [S0_c21 named nbids ndist app].
    + split; [| constructor]. exists w. split; [exact Hw|]. split; [| exact I]. apply (FRAME ([fst f1] ++ w) w); [| exact HCw].
      intros x [<-|Hx] NE; [exfalso; exact (NE eq_refl)| exact Hx].
    + split.
      * exists w. split; [exact Hw|]. split; [| exact I]. apply (FRAME ([fst f1] ++ w) ([fst f1] ++ w)); [intros x Hx _; exact Hx| exact HCw].
      * constructor; [| constructor]. split; [| exists r1; apply KEEP; [exact Hr1| congruence]].
        apply (INS _ f1 r1 (CS _ HCw)); [apply KEEP; [exact Hr1| congruence]| exact HI1].
  - (* [comment removed for export] *) destruct HC as [(w & Hw & HCw & ND) HI].
    apply Forall_cons_iff in HI as [[HI1 (r1 & Hr1)] HI]. apply Forall_inv in HI. destruct HI as [HI2 (r2 & Hr2)].
    destruct (bid_eqb_spec p f1) as [->|NE1]; [| destruct (bid_eqb_spec p f2) as [->|NE2]]; cbn [S0_c21 named nbids ndist app].
    + (* [comment removed for export] *)
      split.
      * exists w. split; [exact Hw|]. split; [| exact I]. apply (FRAME ([fst f1; fst f2] ++ w) ([fst f2] ++ w)); [| exact HCw].
        intros x [<-|Hx] NE; [exfalso; exact (NE eq_refl)| exact Hx].
      * constructor; [| constructor]. split; [| exists r2; apply KEEP; [exact Hr2| congruence]].
        apply (INS _ f2 r2 (CS _ HCw)); [apply KEEP; [exact Hr2| congruence]| exact HI2].
    + (* [comment removed for export] *)
      split.
      * exists w. split; [exact Hw|]. split; [| exact I]. apply (FRAME ([fst f1; fst f2] ++ w) ([fst f1] ++ w)); [| exact HCw].
        intros x [<-|[<-|Hx]] NE; [left; reflexivity| exfalso; exact (NE eq_refl)| right; exact Hx].
      * constructor; [| constructor]. split; [| exists r1; apply KEEP; [exact Hr1| congruence]].
        apply (INS _ f1 r1 (CS _ HCw)); [apply KEEP; [exact Hr1| congruence]| exact HI1].
    + (* [comment removed for export] *)
      split.
      * exists w. split; [exact Hw|]. split; [| exact ND]. apply (FRAME ([fst f1; fst f2] ++ w) ([fst f1; fst f2] ++ w)); [intros x Hx _; exact Hx| exact HCw].
      * constructor; [| constructor; [| constructor]].
        -- split; [| exists r1; apply KEEP; [exact Hr1| congruence]]. apply (INS _ f1 r1 (CS _ HCw)); [apply KEEP; [exact Hr1| congruence]| exact HI1].
        -- split; [| exists r2; apply KEEP; [exact Hr2| congruence]]. apply (INS _ f2 r2 (CS _ HCw)); [apply KEEP; [exact Hr2| congruence]| exact HI2].
Qed.

Lemma S0_freec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
      (s : PState) (LB : list ablock) (k : nat) (p : bid) (A n lo B : Z) (errv : word) (T : TSet),
    S0_inv s LB m MD -> S0_acvm k s MD -> In (p, A, n) LB -> (c21_foreign n \/ n = FILE_SZ) ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk s0segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack S0_layout ->
    rw_cells s0segs m (errno_cell S0_layout) [C4 errv] ->
    mem_inv s0segs m ->
    tp = Z_to_bv 64 (al_tp S0_layout) ->
    a0 = Z_to_bv 64 A ->
    (forall (s' : PState) (m' : word -> option byte) (MD' : Model)
            (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        S0_inv s' (lb_remove p LB) m' MD' -> vm_only MD MD' -> S0_acvm k s' MD' ->
        mem_inv s0segs m' -> stk s0segs m' lo (bv_unsigned sp) -> rw_cells s0segs m' (errno_cell S0_layout) [C4 errv] -> rauxv_ok m' B ->
        heap_pres s0segs S0_layout (lb_remove p LB) (bv_unsigned sp) m m' ->
        (forall o, S0_c21 o s LB -> S0_c21 (c21_after_free o p n) s' (lb_remove p LB)) ->
        realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom s0segs)) MD') T) ->
    realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_free S0_layout)) fc None m (seg_rom s0segs)) MD) T.
Proof.
  intros until T. intros HI HV Hin _ AUX SB ST CLO LO ERR MI TP A0 K.
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
                (fun s0 mo0 r s' mo' => s0 = s -> mo0 = MD ->
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
    intros o HC. exact (c21_free LB s (set_m cs' s) MD MD' _ p A n HOx HQk Hin NDL FR o HC).
  - eapply t_leaves_const; [exact (HS1 s MD (conj eq_refl eq_refl))|]. intros MD' HF. exact HF.
Qed.

Lemma S0_c21_perm o s LB LB' : Permutation LB LB' -> S0_c21 o s LB -> S0_c21 o s LB'.
Proof.
  intros P HC. destruct o; cbn [S0_c21] in *; [exact HC| | |];
    (destruct HC as [HW HI]; split; [exact HW|]; eapply Forall_impl; [| exact HI];
     intros f [A (r & B)]; split; [exact A| exists r; eapply Permutation_in; [exact P| exact B]]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition S0_cover : AllocCover s0segs S0_layout S0_alloc :=
  mkAllocCover s0segs S0_layout S0_alloc
    S0_can S0_acvm S0_acvm_frame S0_acvm_le S0_c21
    S0_malloc_cover S0_malloc_bigc S0_malloc_bigzc S0_malloc_sysc S0_malloc_fastc S0_can_intro S0_malloc_firstc S0_freec
    S0_c21_perm none_idle.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma S0_tight_cover0 : forall s LB m MD,
  S0_inv s LB m MD -> S0_tightP s LB MD -> S0_c21 C21_none s LB /\ exists K0, S0_acvm K0 s MD /\ (80 <= K0)%nat.
Proof.
  (intros s LB m MD [_ HO]; cps_intros (STR & HI & HT & POT & VM & H0 & W & FW & _ & _ & _ & _ & LEN & _)).
  split.
  - cbn [S0_c21]. intros g b Hh Hs. destruct HO as [(L & (st & BL & LS & Est & INV & LIVE) & _ & _) _].
    rewrite <- Est in Hh, Hs, H0.
    exact (C21none_no21 x0 st L BL LS g b INV (fun g0 b0 H => H0 b0 g0 H) Hh Hs).
  - exists 80%nat. split; [| lia]. split.
    + unfold cnt. unfold fl_len in POT. destruct (c_free_meta_head (s_ctx (ps_m s))); cbn [length] in *; lia.
    + cps_destruct VM as (LIM & MAT & SZ & LENM). unfold VMB. split; [exact LIM|]. split; [exact MAT|]. split; [| lia].
      eapply Forall_impl; [| exact SZ]. cbv beta. intros e He. lia.
Qed.

End ACeilS1.
