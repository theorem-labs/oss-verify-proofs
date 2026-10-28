(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec CatSim ShapeAlg MmapSim RefNodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep Arr.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode SFMisc EvtBridge.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.EvtBridge.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Monad MSafe Prog KInv KStep KStepC MI_Inv MI_Kit MI_Contracts MTight.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import MallocBlocks Malloc_iface MallocHINV.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP RF_malloc_spec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require S0H_Iface.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_iface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_ifaceP OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_malloc_spec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap.S0H_Iface.RF_free_spec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require Import AllocLayout0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocTight TreeBridge TightBridge. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require Import S0H_Iface.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Common Require AllocRefusal.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLiaP.
Local Ltac lia ::= lia_acp.   (* [comment removed for export] *)

Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record TBW := mkTBW { tw_g : aptr; tw_rid : N; tw_sc : Z; tw_ml : Z; tw_base : Z; tw_len : Z }.

Definition TB (cs : mstate) (p : bid) (w : TBW) : Prop :=
  let g := tw_g w in let rid := tw_rid w in let sc := tw_sc w in let ml := tw_ml w in
  s_slots cs !! (fst p) = Some (g, 0)
  /\ (exists pv nx, MR cs g = mkMeta pv nx (Some (rid, 0)) 0 0 0 1 sc ml
       /\ ((sc = 63 /\ nx = None) \/ (39 <= sc < 48 /\ nx = Some g /\ active cs sc = Some g /\ ml * 4096 - UNIT < UNIT * size_class sc)))
  /\ 0 < ml /\ ~ in_pool cs g
  /\ (forall a, active cs a = Some g -> a = sc /\ sc < 48)
  /\ fst p = (rid, UNIT)
  /\ s_regions cs !! rid = Some (mkRegion RKGroup (tw_base w) (tw_len w)) /\ mmap_len (tw_len w) = ml * 4096 /\ 0 < tw_len w
  /\ 0 < tw_base w /\ tw_base w mod 4096 = 0 /\ tw_base w + ml * 4096 <= alloc_ceiling
  /\ (rid < s_next_rid cs)%N.

Definition fl_len (cs : mstate) : Z := match c_free_meta_head (s_ctx cs) with Some _ => 1 | None => 0 end.

(* [comment removed for export] *)
Definition VMT (k : nat) (MD : Model) : Prop :=
  let h := m_vmmaps MD in
  target_alloc_limit <= vm_limit h
  /\ m_vm_materialized MD = []
  /\ Forall (fun e => 0 < bv_unsigned (snd e) <= 2^27 /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= 2^64) (vm_reserved h ++ vm_maps h)
  /\ (length (vm_reserved h ++ vm_maps h) <= 16 + k)%nat.

(* [comment removed for export] *)
Definition HOST0 (cs : mstate) : Prop := forall b g, hosts cs b g -> m_last_idx (MR cs g) = 0.

Definition S0_tightP (s : PState) (LB : list ablock) (MD : Model) : Prop :=
  let cs := ps_m s in
  strip cs = cs /\ INJ cs /\ TT (c_avail_meta_count (s_ctx cs)) cs
  /\ 101 <= c_avail_meta_count (s_ctx cs) + fl_len cs + Z.of_nat (length LB)
  /\ VMT (length LB) MD
  /\ HOST0 cs
  /\ exists W : list TBW,
       Forall2 (fun b w => TB cs (blk_id b) w) LB W
       /\ List.NoDup (map tw_rid W) /\ List.NoDup (map tw_g W) /\ List.NoDup (map tw_base W)
       /\ Forall (fun w => In (Z_to_bv 64 (tw_base w), Z_to_bv 64 (tw_ml w * 4096)) (vm_maps (m_vmmaps MD))) W
       /\ (length LB <= 2)%nat /\ (length LB = 2%nat -> c_free_meta_head (s_ctx cs) = None).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma live_bytes_le_len : forall l b, Forall (fun e : word * word => 0 < bv_unsigned (snd e) <= b /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= 2^64) l ->
  0 <= b -> live_bytes l <= Z.of_nat (length l) * b.
Proof.
  intros l b HF Hb. induction l as [|[a n] l IH]; cbn [live_bytes length]; [lia|].
  apply Forall_cons_iff in HF as [[H1 _] HF]. cbn [snd] in H1. specialize (IH HF). rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma vm_backing_used_le : forall MD, m_vm_lazy MD = [] -> m_vm_materialized MD = [] ->
  vm_backing_used MD <= live_bytes (vm_maps (m_vmmaps MD)).
Proof.
  intros MD HL HM. unfold vm_backing_used. rewrite HL, HM. cbn [maps_subtract_all length Z.of_nat]. rewrite Z.mul_0_l, Z.add_0_r.
  unfold vm_backed_maps. apply live_bytes_maps_subtract_all_le.
Qed.

Lemma VMT_budget : forall k MD, (k <= 2)%nat -> VMT k MD -> m_vm_lazy MD = [] ->
  vm_backing_used MD + 2^31 <= vm_limit (m_vmmaps MD).
Proof.
  (intros k MD Hk; cps_intros (LIM & MAT & SZ & LEN); intros HL). eapply Z.le_trans; [| exact LIM]. unfold target_alloc_limit.
  pose proof (vm_backing_used_le MD HL MAT) as B.
  apply Forall_app in SZ as [_ SZ]. rewrite length_app in LEN.
  pose proof (live_bytes_le_len _ (2^27) SZ ltac:(lia)) as B2.
  assert (Z.of_nat (length (vm_maps (m_vmmaps MD))) <= 18) by lia. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma S0_at_sys : forall s LB m MD n, S0_inv s LB m MD -> S0_tightP s LB MD -> 0 < n <= MAX_REQ -> S0_sys_ok s LB n MD.
Proof.
  (intros s LB m MD n [HR HO]; cps_intros (STR & HI & HT & POT & VM & H0 & W & FW & _ & _ & _ & _ & LEN & _); intros Hn).
  unfold MAX_REQ in Hn.
  assert (Hc : 64 <= c_avail_meta_count (s_ctx (ps_m s))).
  { unfold fl_len in POT. destruct (c_free_meta_head (s_ctx (ps_m s))); lia. }
  pose proof (S0_inv_model s LB m MD (conj HR HO)) as [Hh Hl].
  cps_destruct VM as (LIM & MAT & SZ & LENM).
  assert (SZ' : Forall (fun p : word * word => bv_unsigned (snd p) <= 2^35) (vm_reserved (m_vmmaps MD) ++ vm_maps (m_vmmaps MD))).
  { eapply Forall_impl; [| exact SZ]. cbn. intros e [H _]. lia. }
  pose proof (VMT_budget (length LB) MD LEN (conj LIM (conj MAT (conj SZ LENM))) Hl) as BUD.
  assert (ATOP : atop_ok (m_vmmaps MD)) by (destruct HO as [(L & _ & HK & _) _]; exact (kl_atop _ _ _ HK)).
  assert (NFORCED : forall len, 0 < len <= 2^30 -> AllocRefusal.mmap_grant_refusable (Z_to_bv 64 MAPF) MD (mmap_len len) = false).
  { intros len Hlen. pose proof (mmap_len_bound len ltac:(lia)) as MLB.
    apply (mmap_not_forced_big len MD ltac:(lia) ltac:(lia) ATOP SZ' ltac:(lia) ltac:(lia)). }
  intros tr s' MD' Hp.
  destruct (Z_lt_le_dec n MMAP_THRESHOLD) as [SMALL|BIG].
  - pose proof (cmalloc_small_tight _ (ps_m s) n HT HI ltac:(unfold FUEL; cbn; lia) ltac:(lia)) as MM.
    cps_destruct (raw_malloc_paths04 (map blk_id LB) TrueG s MD n CQF CQS (fun x => snd x = None) (fun _ x => exists c, snd x = Some c) HO ltac:(lia) MM
                ltac:(intros t (cs' & ->); eexists; split; [reflexivity| reflexivity])
                ltac:((intros z t; cps_intros (cs' & p & ->)); eexists; split; [reflexivity| eexists; reflexivity])
                tr None s' MD' Hp) as (len & K & z & x & E & Hlen & _ & _ & Hr & CASES).
    destruct CASES as [(_ & _ & _ & FORCED)|(_ & (c & Hc') & _)].
    + rewrite (NFORCED len Hlen) in FORCED. discriminate FORCED.
    + rewrite Hc' in Hr. discriminate Hr.
  - pose proof (cmalloc_big_tight _ (ps_m s) n HT HI ltac:(lia) BIG ltac:(unfold IB, UNIT; lia) STR) as MM.
    cps_destruct (raw_malloc_paths04 (map blk_id LB) TrueG s MD n _ _ (fun x => snd x = None) (fun _ x => exists c, snd x = Some c) HO ltac:(lia) MM
                ltac:(intros t ->; eexists; split; [reflexivity| reflexivity])
                ltac:((intros z t; cps_intros (cs' & g & c' & -> & _)); eexists; split; [reflexivity| eexists; reflexivity])
                tr None s' MD' Hp) as (len & K & z & x & E & Hlen & _ & _ & Hr & CASES).
    destruct CASES as [(_ & _ & _ & FORCED)|(_ & (c & Hc') & _)].
    + rewrite (NFORCED len Hlen) in FORCED. discriminate FORCED.
    + rewrite Hc' in Hr. discriminate Hr.
Qed.

Lemma S0_at_mat : forall s LB MD, S0_tightP s LB MD -> m_vm_materialized MD = [].
Proof. (intros s LB MD; cps_intros (_ & _ & _ & _ & (_ & MAT & _) & _)). exact MAT. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma S0_at_model_frame : forall s LB MD MD', S0_tightP s LB MD -> m_vm MD' = m_vm MD -> m_halted MD' = None -> S0_tightP s LB MD'.
Proof.
  (intros s LB MD MD'; cps_intros (STR & HI & HT & POT & VM & H0 & W & FW & N1 & N2 & N3 & INM & REST); intros EV _).
  assert (E1 : m_vmmaps MD' = m_vmmaps MD) by (unfold m_vmmaps; rewrite EV; reflexivity).
  assert (E2 : m_vm_materialized MD' = m_vm_materialized MD) by (unfold m_vm_materialized; rewrite EV; reflexivity).
  split; [exact STR|]. split; [exact HI|]. split; [exact HT|]. split; [exact POT|]. split; [| split; [exact H0|]].
  - cps_destruct VM as (LIM & MAT & SZ & LEN). unfold VMT. rewrite E1, E2. auto.
  - exists W. rewrite E1. auto 10.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma TT_recount c st : TT c st -> TT (c_avail_meta_count (s_ctx st)) st.
Proof. intros HT. apply (TT_frame c _ st st HT).
  all: first [reflexivity | apply (tt_bnc _ _ HT) | apply (tt_useq _ _ HT) | (left; reflexivity) | apply (tt_avail _ _ HT) | apply cursor_sub_refl | (intros; reflexivity) | lia].
Qed.

Lemma ps_m_set_m cs s : ps_m (set_m cs s) = cs. Proof. reflexivity. Qed.

(* [comment removed for export] *)

Lemma mmap_len_pages x : 0 < x -> mmap_len x = (x + 4095) / 4096 * 4096.
Proof. intros Hx. unfold mmap_len, page_round_up_Z, page_size. f_equal. f_equal. lia. Qed.

Lemma Forall2_In_r {A B} (R : A -> B -> Prop) : forall l1 l2 y, Forall2 R l1 l2 -> In y l2 -> exists x, In x l1 /\ R x y.
Proof.
  intros l1 l2 y H. induction H as [|a b0 l1' l2' Hab H IH]; intros Hin; [destruct Hin|].
  destruct Hin as [<-|Hin]; [exists a; split; [left; reflexivity| exact Hab]|].
  cps_destruct (IH Hin) as (x & Hx & Rx). exists x. split; [right; exact Hx| exact Rx].
Qed.

Lemma tightP_big_ok : forall s LB MD n z cs' g c' MD' (b : ablock),
  S0_tightP s LB MD -> length LB = 1%nat ->
  BIGPOST (ps_m s) n z cs' g c' -> TT (c_avail_meta_count (s_ctx (ps_m s)) - 1) cs' -> INJ cs' -> strip cs' = cs' ->
  MMAP_THRESHOLD <= n <= MAX_REQ -> mmap_addr_ok (n + IB + UNIT) [] z = true ->
  region_free (vm_reserved (m_vmmaps MD) ++ vm_maps (m_vmmaps MD)) (Z_to_bv 64 z) (Z_to_bv 64 (mmap_len (n + IB + UNIT))) = true ->
  (let h := m_vmmaps MD in
   m_vmmaps MD' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 z, Z_to_bv 64 (mmap_len (n + IB + UNIT))) :: vm_maps h)
                               (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) ->
  m_vm_materialized MD' = m_vm_materialized MD ->
  fst (blk_id b) = c' ->
  S0_tightP (set_m cs' s) (b :: LB) MD'.
Proof.
  (intros s LB MD n z cs' g c' MD' b; cps_intros (STR & HI & HT & POT & VM & H0 & W & FW & NDr & NDg & NDb & INM & LEN & HD2); intros L1 BP HT' HI' STR' Hn AOK RF VM' MAT' Hb).
  apply mmap_addr_ok_true in AOK as [(A1 & A2 & A3) _]. unfold page_size in A1. bz_ceil.
  unfold MMAP_THRESHOLD, MAX_REQ in Hn.
  pose proof BP as [[R1 R2] SL SLo MRg MRo [PM [NPM PL]] [ai GR] RG NR RS ACT FH INI BN UQ AV CNT].
  set (cs := ps_m s) in *.
  assert (ML : 32 <= (n + IB + UNIT + 4095) / 4096).
  { apply Z.div_le_lower_bound; [lia|]. unfold IB, UNIT in *. lia. }
  assert (MLE : mmap_len (n + IB + UNIT) = (n + IB + UNIT + 4095) / 4096 * 4096) by (apply mmap_len_pages; unfold IB, UNIT; lia).
  unfold S0_tightP. rewrite ps_m_set_m.
  split; [exact STR'|]. split; [exact HI'|]. split; [apply (TT_recount _ _ HT')|]. split.
  { cbn [length]. rewrite Nat2Z.inj_succ. unfold fl_len in *. rewrite FH. rewrite CNT. unfold cs in *.
    destruct (c_free_meta_head (s_ctx (ps_m s))); lia. }
  split.
  { cps_destruct VM as (LIM & MAT & SZ & LENM). unfold VMT. rewrite VM', MAT'. cbn [vm_reserved vm_maps vm_limit].
    split; [exact LIM|]. split; [exact MAT|]. split.
    - apply Forall_app in SZ as [SZ1 SZ2]. apply Forall_app. split; [exact SZ1|]. constructor; [| exact SZ2].
      cbn [fst snd]. pose proof (mmap_len_ge (n + IB + UNIT) ltac:(unfold IB, UNIT; lia)) as MG.
      rewrite !unsigned_lit by (unfold MAX_REQ, IB, UNIT in *; lia).
      unfold MAX_REQ, IB, UNIT in *. lia.
    - rewrite length_app in *. cbn [length] in *. lia. }
  split.
  { intros b0 x Hx. destruct (aptr_eq_dec x g) as [->|NEx]; [rewrite MRg; reflexivity|].
    rewrite (MRo _ NEx). apply (H0 b0 x). destruct Hx as [aix Hx]. rewrite GR in Hx.
    destruct (aptr_eq_dec b0 (s_next_rid cs, 0)) as [->|NEb]; [rewrite lookup_insert_eq in Hx; injection Hx as E _; exfalso; exact (NEx (eq_sym E))|].
    rewrite lookup_insert_ne in Hx by congruence. exists aix. exact Hx. }
  exists (mkTBW g (s_next_rid cs) 63 ((n + IB + UNIT + 4095) / 4096) z (n + IB + UNIT) :: W).
  assert (NAg : forall a, active cs a <> Some g).
  { intros a Ha. destruct (tt_act _ _ HT a) as [H|(g' & H & _ & NP)]; [congruence|]. unfold cs in *. rewrite Ha in H. injection H as <-. exact (NP PM). }
  assert (Ec : c' = (s_next_rid cs, UNIT)) by (destruct c'; cbn in R1, R2; subst; reflexivity).
  split.
  - constructor.
    + (* [comment removed for export] *)
      unfold TB. cbn [tw_g tw_rid tw_sc tw_ml tw_base tw_len]. rewrite Hb.
      split; [exact SL|]. split; [exists None, None; split; [exact MRg| left; auto]|].
      split; [lia|]. split; [exact NPM|]. split; [intros a Ha; exfalso; rewrite ACT in Ha; exact (NAg a Ha)|].
      split; [exact Ec|]. split; [rewrite RG; apply lookup_insert_eq|]. split; [exact MLE|]. split; [unfold IB, UNIT; lia|].
      split; [lia|]. split; [lia|]. split; [rewrite <- MLE; exact A3|]. rewrite NR. lia.
    + (* [comment removed for export] *)
      eapply Forall2_impl; [| exact FW]. (intros b0 w; cps_intros (TS & (pv & nx & TM & TC) & Tml & TP & TA & Tc & TR & TL & Tl & Tb & Ta & Tce & Tn)).
      assert (NEg : tw_g w <> g) by (intros E; apply TP; rewrite E; exact PM).
      unfold TB. split; [rewrite SLo; [exact TS| rewrite Tc, Ec; intros E; injection E; lia]|].
      split; [exists pv, nx; rewrite (MRo _ NEg); split; [exact TM|]; destruct TC as [TC|(X1 & X2 & X3 & X4)]; [left; exact TC| right; rewrite ACT; auto]|].
      split; [exact Tml|]. split; [intros P; exact (TP (proj1 (PL _ P)))|]. split; [intros a; rewrite ACT; apply TA|].
      split; [exact Tc|]. split; [rewrite RG, lookup_insert_ne by lia; exact TR|]. split; [exact TL|]. split; [exact Tl|].
      split; [exact Tb|]. split; [exact Ta|]. split; [exact Tce|]. rewrite NR. lia.
  - split.
    { cbn [map tw_rid]. constructor; [| exact NDr]. intros Hin. apply in_map_iff in Hin as (w & Ew & Hw).
      cps_destruct (Forall2_In_r _ _ _ _ FW Hw) as (b0 & _ & Tw). cbn in Ew.
      cps_destruct Tw as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Tn). rewrite Ew in Tn. lia. }
    split.
    { cbn [map tw_g]. constructor; [| exact NDg]. intros Hin. apply in_map_iff in Hin as (w & Ew & Hw).
      cps_destruct (Forall2_In_r _ _ _ _ FW Hw) as (b0 & _ & Tw). cbn in Ew.
      cps_destruct Tw as (_ & _ & _ & TP & _). rewrite Ew in TP. exact (TP PM). }
    split.
    { cbn [map tw_base]. constructor; [| exact NDb]. intros Hin. apply in_map_iff in Hin as (w & Ew & Hw).
      pose proof (proj1 (Forall_forall _ _) INM w Hw) as IN. cbn beta in IN. rewrite Ew in IN.
      cps_destruct (Forall2_In_r _ _ _ _ FW Hw) as (b0 & _ & Tw).
      cps_destruct Tw as (_ & _ & Tml & _ & _ & _ & _ & _ & _ & Tb & Ta & Tce & _).
      pose proof (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.KStepC.KLink.region_free_disj _ _ _ _ (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.KStepC.KLink.region_free_app_r _ _ _ _ RF) IN) as D.
      unfold elo, ehi in D. cbn [fst snd] in D. pose proof (mmap_len_ge (n + IB + UNIT) ltac:(unfold IB, UNIT; lia)).
      rewrite !unsigned_lit in D by (unfold IB, UNIT in *; lia). unfold IB, UNIT in *. lia. }
    split.
    { constructor.
      - cbn [tw_base tw_ml]. rewrite VM'. cbn [vm_maps]. left. rewrite MLE. reflexivity.
      - eapply Forall_impl; [| exact INM]. intros w Hw. rewrite VM'. cbn [vm_maps]. right. exact Hw. }
    split; [cbn [length]; lia|]. intros _. exact FH.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma map_remove_length_in : forall l (a n : word), In (a, n) l -> (length (map_remove l a) + 1 <= length l)%nat.
Proof.
  induction l as [|[b m] l IH]; intros a n Hin; [destruct Hin|].
  unfold map_remove. cbn [List.filter fst]. destruct Hin as [E|Hin].
  - injection E as -> ->. rewrite bv_eqb_refl. cbn [negb]. pose proof (map_remove_length l a) as L. unfold map_remove in L. cbn [length]. lia.
  - destruct (bv_eqb b a); cbn [negb length]; [pose proof (map_remove_length l a) as L; unfold map_remove in L; lia|].
    specialize (IH a n Hin). unfold map_remove in IH. lia.
Qed.

Lemma Forall_map_remove {P : word * word -> Prop} l a : Forall P l -> Forall P (map_remove l a).
Proof. intros H. unfold map_remove. apply Forall_forall. intros x Hx. apply filter_In in Hx as [Hx _]. exact (proj1 (Forall_forall _ _) H x Hx). Qed.

Lemma In_map_remove (l : list (word * word)) (a b n : word) : In (b, n) l -> b <> a -> In (b, n) (map_remove l a).
Proof. intros Hin NE. unfold map_remove. apply filter_In. split; [exact Hin|]. cbn [fst]. destruct (bv_eqb b a) eqn:E; [apply bv_eqb_eq in E; congruence| reflexivity]. Qed.

(* [comment removed for export] *)
Lemma lb_remove_two (p : bid) (b1 b2 : ablock) :
  List.NoDup (map blk_id [b1; b2]) -> In p (map blk_id [b1; b2]) ->
  (p = blk_id b1 /\ lb_remove p [b1; b2] = [b2]) \/ (p = blk_id b2 /\ lb_remove p [b1; b2] = [b1]).
Proof.
  intros ND Hin. cbn in ND, Hin. inversion ND as [|x l N1 N2]; subst. unfold lb_remove. cbn [List.filter].
  destruct Hin as [<-|[<-|[]]].
  - left. split; [reflexivity|]. rewrite bid_eqb_refl. cbn [negb]. destruct (bid_eqb_spec (blk_id b2) (blk_id b1)) as [E|NE]; [exfalso; apply N1; left; exact E|]. reflexivity.
  - right. split; [reflexivity|]. destruct (bid_eqb_spec (blk_id b1) (blk_id b2)) as [E|NE]; [exfalso; apply N1; left; symmetry; exact E|]. cbn [negb]. rewrite bid_eqb_refl. reflexivity.
Qed.

Lemma tightP_free : forall s LB MD (p : bid) (A n : Z),
  S0_tightP s LB MD -> length LB = 2%nat -> In (p, A, n) LB -> List.NoDup (map blk_id LB) ->
  exists w, TB (ps_m s) p w
    /\ FREEPRE (ps_m s) (fst p) (tw_g w) (tw_rid w, 0) (tw_sc w) (tw_ml w)
    /\ In (Z_to_bv 64 (tw_base w), Z_to_bv 64 (tw_ml w * 4096)) (vm_maps (m_vmmaps MD))
    /\ forall cs' MD',
         FREEPOST (ps_m s) (fst p) (tw_g w) (tw_rid w, 0) (tw_sc w) cs' ->
         TT (c_avail_meta_count (s_ctx (ps_m s))) cs' -> INJ cs' -> strip cs' = cs' ->
         (let h := m_vmmaps MD in
          m_vmmaps MD' = mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) (Z_to_bv 64 (tw_base w)))
                           (maps_subtract (vm_noaccess h) (tw_base w) (tw_base w + tw_ml w * 4096))
                           (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) ->
         (m_vm_materialized MD = [] -> m_vm_materialized MD' = []) ->
         S0_tightP (set_m cs' s) (lb_remove p LB) MD'.
Proof.
  (intros s LB MD p A n; cps_intros (STR & HI & HT & POT & VM & H0 & W & FW & NDr & NDg & NDb & INM & LEN & HD2); intros L2 Hin ND).
  destruct LB as [|b1 [|b2 [|? ?]]]; cbn in L2; try lia. clear L2 LEN.
  pose proof FW as FW0. inversion FW as [|xb1 w1 lb' W1 T1 FW1]; subst. inversion FW1 as [|xb2 w2 lb'' W2 T2 FW2]; subst. inversion FW2; subst.
  cbn [map] in NDr, NDg, NDb. apply Forall_cons_iff in INM as [IN1 INM]. apply Forall_cons_iff in INM as [IN2 _].
  inversion NDr as [|? ? NR1 _]; subst. inversion NDg as [|? ? NG1 _]; subst. inversion NDb as [|? ? NB1 _]; subst. cbn in NR1, NG1, NB1.
  assert (Hp : In p (map blk_id [b1; b2])) by (apply in_map_iff; exists (p, A, n); split; [reflexivity| exact Hin]).
  specialize (HD2 eq_refl).
  (* [comment removed for export] *)
  assert (GEN : forall bf bk wf wk, TB (ps_m s) (blk_id bf) wf -> TB (ps_m s) (blk_id bk) wk ->
     tw_rid wf <> tw_rid wk -> tw_g wf <> tw_g wk -> tw_base wf <> tw_base wk ->
     In (Z_to_bv 64 (tw_base wf), Z_to_bv 64 (tw_ml wf * 4096)) (vm_maps (m_vmmaps MD)) ->
     In (Z_to_bv 64 (tw_base wk), Z_to_bv 64 (tw_ml wk * 4096)) (vm_maps (m_vmmaps MD)) ->
     p = blk_id bf -> lb_remove p [b1; b2] = [bk] ->
     exists w, TB (ps_m s) p w
       /\ FREEPRE (ps_m s) (fst p) (tw_g w) (tw_rid w, 0) (tw_sc w) (tw_ml w)
       /\ In (Z_to_bv 64 (tw_base w), Z_to_bv 64 (tw_ml w * 4096)) (vm_maps (m_vmmaps MD))
       /\ forall cs' MD',
            FREEPOST (ps_m s) (fst p) (tw_g w) (tw_rid w, 0) (tw_sc w) cs' ->
            TT (c_avail_meta_count (s_ctx (ps_m s))) cs' -> INJ cs' -> strip cs' = cs' ->
            (let h := m_vmmaps MD in
             m_vmmaps MD' = mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) (Z_to_bv 64 (tw_base w)))
                              (maps_subtract (vm_noaccess h) (tw_base w) (tw_base w + tw_ml w * 4096))
                              (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) ->
            (m_vm_materialized MD = [] -> m_vm_materialized MD' = []) ->
            S0_tightP (set_m cs' s) (lb_remove p [b1; b2]) MD').
  { intros bf bk wf wk Tf Tk NR NG NB INf INk -> ER. exists wf.
    cps_destruct Tf as (fS & (fpv & fnx & fM & fC) & fml & fP & fA & fc & fR & fL & fl & fb & fa & fce & fn).
    split; [unfold TB; repeat (split; [solve [eauto 8] |]); try exact fn; eauto 10|].
    split.
    { constructor.
      - exact fS.
      - exists fpv, fnx. split; [exact fM| exact fC].
      - exact fml.
      - exact fP.
      - exact HD2.
      - exact fA.
      - rewrite fc. reflexivity. }
    split; [exact INf|].
    intros cs' MD' FQ HT' HI' STR' VM' MAT'. rewrite ER.
    destruct FQ as [qS qG qR qRs qN qM qMo qA qF qI qB qU qAv qC].
    cps_destruct Tk as (kS & (kpv & knx & kM & kC) & kml & kP & kA & kc & kR & kL & kl & kb & ka & kce & kn).
    unfold S0_tightP. rewrite ps_m_set_m.
    split; [exact STR'|]. split; [exact HI'|]. split; [exact (TT_recount _ _ HT')|].
    split.
    { cbn [length]. unfold fl_len in *. rewrite qF, qC. rewrite HD2 in POT. cbn [length] in POT. lia. }
    cps_destruct VM as (LIM & MAT & SZ & LENM).
    bz_ceil.
    split.
    { unfold VMT. rewrite VM'. cbn [vm_reserved vm_maps vm_limit]. split; [exact LIM|]. split; [exact (MAT' MAT)|]. split.
      - apply Forall_app in SZ as [SZ1 SZ2]. apply Forall_app. split; [exact SZ1| apply Forall_map_remove; exact SZ2].
      - rewrite length_app in *. cbn [length] in LENM. change (length [bk]) with 1%nat. pose proof (map_remove_length_in _ _ _ INf). lia. }
    split.
    { intros b0 x Hx. destruct (aptr_eq_dec x (tw_g wf)) as [->|NEx]; [rewrite qM; reflexivity|].
      rewrite (qMo _ NEx). apply (H0 b0 x). destruct Hx as [aix Hx]. rewrite qG in Hx.
      destruct (aptr_eqb b0 (tw_rid wf, 0)); [discriminate|]. exists aix. exact Hx. }
    exists [wk]. split.
    { constructor; [| constructor]. unfold TB.
      split; [rewrite qS; destruct (aptr_eqb_spec (fst (blk_id bk)) (fst (blk_id bf))) as [E|NE]; [exfalso; rewrite kc, fc in E; injection E; congruence| exact kS]|].
      split.
      { exists kpv, knx. rewrite (qMo (tw_g wk)) by congruence. split; [exact kM|].
        destruct kC as [kC|(X1 & X2 & X3 & X4)]; [left; exact kC| right]. split; [exact X1|]. split; [exact X2|]. split; [| exact X4].
        rewrite qA. destruct (Z.eqb_spec (tw_sc wk) (tw_sc wf)) as [Esc|NEsc]; cbn [andb]; [| exact X3].
        destruct (Z.ltb_spec (tw_sc wf) 48) as [L48|L48]; [| exact X3].
        exfalso. rewrite Esc in X3. destruct fC as [(E63 & _)|(_ & _ & Y3 & _)]; [lia|].
        rewrite X3 in Y3. injection Y3. congruence. }
      split; [exact kml|]. split.
      { intros [P|(am & i & P & Hi & E)]; [rewrite qF in P; injection P; congruence|]. apply kP. right. exists am, i. rewrite qAv in P. auto. }
      split.
      { intros a Ha. rewrite qA in Ha. destruct ((a =? tw_sc wf) && (tw_sc wf <? 48)); [discriminate|]. exact (kA a Ha). }
      split; [exact kc|]. split; [rewrite qR; destruct (N.eqb_spec (tw_rid wk) (fst (tw_rid wf, 0))) as [E|NE]; [cbn in E; congruence| exact kR]|].
      split; [exact kL|]. split; [exact kl|]. split; [exact kb|]. split; [exact ka|]. split; [exact kce|]. rewrite qN. exact kn. }
    split; [constructor; [intros []| constructor]|]. split; [constructor; [intros []| constructor]|]. split; [constructor; [intros []| constructor]|].
    split.
    { constructor; [| constructor]. rewrite VM'. cbn [vm_maps]. apply In_map_remove; [exact INk|].
      intros E. apply NB. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. congruence. }
    split; [cbn; lia|]. cbn. lia. }
  assert (NR : tw_rid w1 <> tw_rid w2) by (intros E; apply NR1; left; congruence).
  assert (NG : tw_g w1 <> tw_g w2) by (intros E; apply NG1; left; congruence).
  assert (NB : tw_base w1 <> tw_base w2) by (intros E; apply NB1; left; congruence).
  destruct (lb_remove_two p b1 b2 ND Hp) as [[-> ER]|[-> ER]].
  - exact (GEN b1 b2 w1 w2 T1 T2 NR NG NB IN1 IN2 eq_refl ER).
  - exact (GEN b2 b1 w2 w1 T2 T1 (not_eq_sym NR) (not_eq_sym NG) (not_eq_sym NB) IN2 IN1 eq_refl ER).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition BIGCL (s : PState) (MD : Model) (n : Z) (r : option bptr) (s' : PState) (MD' : Model) : Prop :=
  exists len (K : Z -> Malloc.M (mstate * option cptr)) z (x : mstate * option cptr),
    cmalloc (ps_m s) n = SVis (EMmap 0 len PROT_RW MAPF) K /\ 0 < len <= 2^30
    /\ s' = set_m (fst x) s
    /\ r = match snd x with Some c => Some (c, fresh_off (fst x) c n) | None => None end
    /\ ( (is_err z = true /\ x = (ps_m s, @None cptr) /\ MD' = MD)
       \/ (is_err z = false
           /\ (exists cs' g c', x = (cs', Some c') /\ BIGPOST (ps_m s) n z cs' g c' /\ TT (c_avail_meta_count (s_ctx (ps_m s)) - 1) cs' /\ INJ cs' /\ strip cs' = cs')
           /\ vm_only MD MD' /\ m_vm_lazy MD' = [] /\ m_halted MD' = None
           /\ (let h := m_vmmaps MD in
               m_vmmaps MD' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 z, Z_to_bv 64 (mmap_len len)) :: vm_maps h)
                                           (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h))
           /\ mmap_addr_ok len [] z = true /\ m_vm_materialized MD' = m_vm_materialized MD
           /\ region_free (vm_reserved (m_vmmaps MD) ++ vm_maps (m_vmmaps MD)) (Z_to_bv 64 z) (Z_to_bv 64 (mmap_len len)) = true) ).

Lemma S0_at_malloc_big : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
      (s : PState) (LB : list ablock) (n lo B : Z) (errv : word) (Tok : TSet),
    S0_inv s LB m MD -> S0_tightP s LB MD -> length LB = 1%nat -> MMAP_THRESHOLD_Z <= n <= MAX_REQ ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk s0segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack S0_layout ->
    rw_cells s0segs m (errno_cell S0_layout) [C4 errv] ->
    mem_inv s0segs m ->
    tp = Z_to_bv 64 (al_tp S0_layout) ->
    a0 = Z_to_bv 64 n ->
    (forall (s' : PState) (m' : word -> option byte) (MD' : Model) (r : Z) (p : bid)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word) (junk : list byte),
        S0_inv s' ((p, r, n) :: LB) m' MD' -> S0_tightP s' ((p, r, n) :: LB) MD' -> vm_only MD MD' ->
        mem_inv s0segs m' -> stk s0segs m' lo (bv_unsigned sp) -> rw_cells s0segs m' (errno_cell S0_layout) [C4 errv'] -> rauxv_ok m' B ->
        heap_pres s0segs S0_layout LB (bv_unsigned sp) m m' ->
        r <> 0 -> block_ok S0_layout r n -> ~ In p (map blk_id LB) -> rw_cells s0segs m' r [CB (Z.to_nat n) junk] ->
        realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom s0segs)) MD') Tok) ->
    realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_malloc S0_layout)) fc None m (seg_rom s0segs)) MD) Tok.
Proof.
  intros until Tok. intros HI TG L1 Hn AUX SB ST CLO LO ERR MI TP A0 Kt.
  pose proof (S0_at_sys s LB m MD n HI TG ltac:(unfold MMAP_THRESHOLD_Z in Hn; lia)) as NF.   (* [comment removed for export] *)
  destruct HI as [HR HO]. pose proof (S0_inv_model s LB m MD (conj HR HO)) as [Hh Hl].
  cbn [al_stack S0_layout] in LO. cbn [al_tp S0_layout] in TP.
  rewrite <- (errno_cell_S0 tp TP) in ERR.
  unfold MMAP_THRESHOLD_Z, MAX_REQ in Hn.
  pose proof (rmalloc_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv
                HR AUX SB ST ltac:(bz_ceil; exact CLO) ltac:(unfold RMALLOC_STACK; lia) ERR MI TP A0 ltac:(lia)) as HM.
  pose proof (raw_malloc_spec_c (map blk_id LB) (vmG MD) n (vmG_frame MD) ltac:(lia)) as HS0.
  (* [comment removed for export] *)
  cps_pose TG as (STR & HINJ & HT & POT & VM & _).
  assert (Hc : 1 <= c_avail_meta_count (s_ctx (ps_m s))) by (unfold fl_len in POT; destruct (c_free_meta_head (s_ctx (ps_m s))); cbn in L1; lia).
  pose proof (cmalloc_big_tight _ (ps_m s) n HT HINJ Hc ltac:(unfold MMAP_THRESHOLD; lia) ltac:(unfold IB, UNIT; lia) STR) as MM.
  pose proof (mspec_strengthen (OWNX (map blk_id LB) (vmG MD)) (raw_malloc n) _
                (fun s0 mo0 r s' mo' => s0 = s -> mo0 = MD -> BIGCL s MD n r s' mo' /\ r <> None) HS0) as HS1.
  assert (HRR : forall sx mox tr ax sx' mox', OWNX (map blk_id LB) (vmG MD) sx mox -> tpath nstep (raw_malloc n sx) mox tr (Ok (ax, sx')) mox' ->
                 sx = s -> mox = MD -> BIGCL s MD n ax sx' mox' /\ ax <> None).
  { intros sx mox tr ax sx' mox' HO0 Hp -> ->. split; [| intros ->; exact (NF tr sx' mox' Hp)].
    cps_destruct (raw_malloc_paths (map blk_id LB) (vmG MD) s MD n _ _ (fun x => x = (ps_m s, @None cptr))
                (fun z x => exists cs' g c', x = (cs', Some c') /\ BIGPOST (ps_m s) n z cs' g c' /\ TT (c_avail_meta_count (s_ctx (ps_m s)) - 1) cs' /\ INJ cs' /\ strip cs' = cs')
                HO0 ltac:(lia) MM ltac:(intros t ->; eexists; split; reflexivity)
                ltac:((intros z t; cps_intros (cs' & g & c' & -> & REST)); eexists; split; [reflexivity| exists cs', g, c'; auto])
                tr ax sx' mox' Hp) as (len & K & z & x & E & Hlen & _ & Hs' & Hr & CASES).
    exists len, K, z, x. auto 10. }
  specialize (HS1 HRR s MD (OWN_vmG _ _ _ HO)). clear HRR.
  eapply rz_conseq.
  - apply (implM_mspec_realizes s0segs (raw_malloc n) s _ (fun s1 mo1 => s1 = s /\ mo1 = MD) _
             (fun _ _ => Tok) _ MD HM HS1
             (conj eq_refl eq_refl) Hh Hl).
    intros r s' ms' MD' HQm [HQk CL].
    destruct (CL eq_refl eq_refl) as [CL0 NN]. clear CL. rename CL0 into CL.
    cps_destruct HQm as (u0 & u1 & u2 & ra0 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & HP' & _ & _ & Hrr).
    rewrite (errno_cell_S0 tp TP) in ERR'. cbn [fst].
    cps_destruct CL as (len & K & z & x & E & Hlen & Hs' & Hr & CASES).
    destruct r as [p|].
    + cps_destruct Hrr as (A & junk & -> & BR & HR' & CH & _). destruct HQk as [HO' _].
      pose proof (OWNX_G _ _ _ _ HO') as V. unfold vmG in V.
      pose proof (RHEAP_blocks_nodup_proof _ _ _ HR') as ND. cbn [map] in ND. inversion ND; subst.
      unfold rblock_range in BR. bz_ceil.
      assert (HI' : S0_inv (set_m (fst x) s) ((p, A, n) :: LB) m' MD') by (split; [exact HR'| cbn [map blk_id fst]; exact (OWN_TrueG _ _ _ _ HO')]).
      assert (HPP : heap_pres s0segs S0_layout LB (bv_unsigned sp) m m') by (apply heap_pres_of_r; exact HP').
      assert (BOK : block_ok S0_layout A n) by (unfold block_ok; cbn [al_img_lo al_img_hi S0_layout]; exact BR).
      destruct CASES as [(_ & -> & _)|(_ & (cs' & g & c' & -> & BP & HT' & HI2 & STR') & VO & LZ & HH & VM' & AOK & MAT' & RF)]; [discriminate|].
      cbn [fst snd] in Hr. injection Hr as ->.
      destruct (cmalloc_big_event (ps_m s) n ltac:(unfold MMAP_THRESHOLD; lia) ltac:(unfold IB, UNIT; lia)) as [K0 E0].
      rewrite E in E0. injection E0 as El _. subst len.
      assert (TG' : S0_tightP (set_m cs' s) (((c', fresh_off cs' c' n), A, n) :: LB) MD').
      { apply (tightP_big_ok s LB MD n z cs' g c' MD' _ TG L1 BP HT' HI2 STR' ltac:(unfold MAX_REQ, MMAP_THRESHOLD; lia) AOK RF VM' MAT'). reflexivity. }
      cbn [fst] in HI'.
      apply (Kt (set_m cs' s) m' MD' A (c', fresh_off cs' c' n) u0 u1 u2 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 errv' junk); try assumption. lia.
    + exfalso. exact (NN eq_refl).
  - eapply t_leaves_const; [exact (HS1 s MD (conj eq_refl eq_refl))|]. intros MD' HF. exact HF.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma S0_at_free : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
      (s : PState) (LB : list ablock) (p : bid) (A n lo B : Z) (errv : word) (T : TSet),
    S0_inv s LB m MD -> S0_tightP s LB MD -> length LB = 2%nat -> In (p, A, n) LB ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk s0segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack S0_layout ->
    rw_cells s0segs m (errno_cell S0_layout) [C4 errv] ->
    mem_inv s0segs m ->
    tp = Z_to_bv 64 (al_tp S0_layout) ->
    a0 = Z_to_bv 64 A ->
    (forall (s' : PState) (m' : word -> option byte) (MD' : Model)
            (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        S0_inv s' (lb_remove p LB) m' MD' -> S0_tightP s' (lb_remove p LB) MD' -> vm_only MD MD' ->
        mem_inv s0segs m' -> stk s0segs m' lo (bv_unsigned sp) -> rw_cells s0segs m' (errno_cell S0_layout) [C4 errv] -> rauxv_ok m' B ->
        heap_pres s0segs S0_layout (lb_remove p LB) (bv_unsigned sp) m m' ->
        realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom s0segs)) MD') T) ->
    realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_free S0_layout)) fc None m (seg_rom s0segs)) MD) T.
Proof.
  intros until T. intros HI TG L2 Hin AUX SB ST CLO LO ERR MI TP A0 K.
  destruct HI as [HR HO]. pose proof (S0_inv_model s LB m MD (conj HR HO)) as [Hh Hl].
  cbn [al_stack S0_layout] in LO. cbn [al_tp S0_layout] in TP.
  rewrite <- (errno_cell_S0 tp TP) in ERR.
  pose proof (rfree_spec_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv
                HR Hin AUX SB ST ltac:(bz_ceil; exact CLO) ltac:(unfold RFREE_STACK; lia) ERR MI TP A0) as HM.
  pose proof (raw_free_spec_c (map blk_id (lb_remove p LB)) (vmG MD) p (vmG_frame MD)) as HS0.
  pose proof (RHEAP_blocks_nodup_proof _ _ _ HR) as NDL.
  assert (HO' : OWNX (p :: map blk_id (lb_remove p LB)) (vmG MD) s MD).
  { eapply OWNX_perm; [| apply OWN_vmG; exact HO]. eapply perm_remove_id; [exact NDL| exact Hin]. }
  (* [comment removed for export] *)
  cps_pose TG as (STR & HINJ & HT & _).
  cps_destruct (tightP_free s LB MD p A n TG L2 Hin NDL) as (w & TBw & FP & INw & POST).
  cps_destruct TBw as (wS & (wpv & wnx & wM & wC) & wml & wP & wA & wc & wR & wL & wl & wb & wa & wce & wn).
  assert (HAS : map_has (vm_maps (m_vmmaps MD)) (Z_to_bv 64 (tw_base w)) (Z_to_bv 64 (tw_ml w * 4096)) = true).
  { unfold map_has. apply existsb_exists. eexists. split; [exact INw|]. cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity. }
  bz_ceil.
  pose proof (mspec_strengthen (OWNX (p :: map blk_id (lb_remove p LB)) (vmG MD)) (raw_free p) _
                (fun s0 mo0 r s' mo' => s0 = s -> mo0 = MD ->
                   exists cs', s' = set_m cs' s
                     /\ FREEPOST (ps_m s) (fst p) (tw_g w) (tw_rid w, 0) (tw_sc w) cs' /\ TT (c_avail_meta_count (s_ctx (ps_m s))) cs' /\ INJ cs' /\ strip cs' = cs'
                     /\ vm_only MD mo' /\ m_vm_lazy mo' = [] /\ m_halted mo' = None
                     /\ (m_vm_materialized MD = [] -> m_vm_materialized mo' = [])
                     /\ let h := m_vmmaps MD in
                        m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) (Z_to_bv 64 (tw_base w)))
                                         (maps_subtract (vm_noaccess h) (tw_base w) (tw_base w + tw_ml w * 4096))
                                         (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) HS0) as HS1.
  assert (HRR : forall sx mox tr ax sx' mox', OWNX (p :: map blk_id (lb_remove p LB)) (vmG MD) sx mox ->
                 tpath nstep (raw_free p sx) mox tr (Ok (ax, sx')) mox' -> sx = s -> mox = MD ->
                 exists cs', sx' = set_m cs' s
                     /\ FREEPOST (ps_m s) (fst p) (tw_g w) (tw_rid w, 0) (tw_sc w) cs' /\ TT (c_avail_meta_count (s_ctx (ps_m s))) cs' /\ INJ cs' /\ strip cs' = cs'
                     /\ vm_only MD mox' /\ m_vm_lazy mox' = [] /\ m_halted mox' = None
                     /\ (m_vm_materialized MD = [] -> m_vm_materialized mox' = [])
                     /\ let h := m_vmmaps MD in
                        m_vmmaps mox' = mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) (Z_to_bv 64 (tw_base w)))
                                         (maps_subtract (vm_noaccess h) (tw_base w) (tw_base w + tw_ml w * 4096))
                                         (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
  { intros sx mox tr ax sx' mox' HO0 Hp -> ->.
    cps_destruct (raw_free_paths (p :: map blk_id (lb_remove p LB)) (vmG MD) s MD p _ (tw_g w) (tw_rid w, 0) (tw_sc w) (tw_ml w)
                HO0 HT HINJ STR FP (tw_base w) ltac:(cbn [fst]; eexists; eexists; exact wR) eq_refl HAS ltac:(lia) tr ax sx' mox' Hp)
      as (cs' & _ & Hs' & FQ & HT' & HI' & STR' & VO & LZ & HH & MAT & VM').
    exists cs'. split; [exact Hs'|]. auto 12. }
  specialize (HS1 HRR s MD HO'). clear HRR.
  eapply rz_conseq.
  - apply (implM_mspec_realizes s0segs (raw_free p) s _ (fun s1' mo1 => s1' = s /\ mo1 = MD) _ (fun _ _ => T) _ MD HM HS1 (conj eq_refl eq_refl) Hh Hl).
    intros [] s' ms' MD' HQm [HQk CL]. specialize (CL eq_refl eq_refl).
    cps_destruct HQm as (u0 & u1 & u2 & ra0 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m' & -> & MI' & ST' & ERR' & AUX' & HP' & _ & _ & HR').
    rewrite (errno_cell_S0 tp TP) in ERR'. rewrite lb_remove_cj in HP', HR'.
    pose proof (OWNX_G _ _ _ _ HQk) as V. unfold vmG in V.
    cps_destruct CL as (cs' & -> & FQ & HT' & HI' & STR' & VO & LZ & HH & MAT & VM').
    assert (HI2 : S0_inv (set_m cs' s) (lb_remove p LB) m' MD') by (split; [exact HR'| exact (OWN_TrueG _ _ _ _ HQk)]).
    assert (HPP : heap_pres s0segs S0_layout (lb_remove p LB) (bv_unsigned sp) m m') by (apply heap_pres_of_r; exact HP').
    assert (TG' : S0_tightP (set_m cs' s) (lb_remove p LB) MD') by (apply (POST cs' MD' FQ HT' HI' STR' VM' MAT)).
    apply (K (set_m cs' s) m' MD' u0 u1 u2 ra0 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14); assumption.
  - eapply t_leaves_const; [exact (HS1 s MD (conj eq_refl eq_refl))|]. intros MD' HF. exact HF.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition S0_tight : AllocTight s0segs S0_layout S0_alloc :=
  mkAllocTight s0segs S0_layout S0_alloc S0_tightP S0_at_sys S0_at_model_frame S0_at_mat S0_at_malloc_big S0_at_free.

End ACeilS1.
