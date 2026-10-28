(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr AEvt Shape HeapIface HeapRz.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_layout.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad MSafe Prog KInv KStep KStepC
     MallocTree MallocBlocks MallocHINV Malloc_iface ImplAevt ImplRz
     MI_Inv MI_List MI_Contracts VirginDefs KReach MReach MStrat MSplit KCost MAll MPack.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_F_syscalls HP_RMallocRep HP_RMallocTree HP_RMalloc_iface HP_RMalloc_ifaceP HP_RF_malloc_spec HP_RF_free_spec U_heap.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_heap_rz () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.Heap.KReach.kmaps"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Lists.ListDef.Forall"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.pow"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_live_bytes"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_limit"; "RocqVerifyHarness.AgentSubmission.Heap.KStep.OWN"; "RocqVerifyHarness.AgentSubmission.U.U_heap.GT"; "RocqVerifyHarness.AgentSubmission.Heap.MAll.DRVc"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.ps_m"; "RocqVerifyHarness.AgentSubmission.Heap.MStrat.UND"; "RocqVerifyHarness.AgentSubmission.Heap.MStrat.shift"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ghdr"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.decidable.prod_eq_dec"; "Corelib.Numbers.BinNums.N"; "stdpp.numbers.N.eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.N_countable"; "stdpp.countable.Z_countable"; "stdpp.gmap.gmap_lookup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_groups"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mkGhdr"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.optr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_mem"; "RocqVerifyHarness.AgentSubmission.Heap.MI_Inv.MR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.U.U_heap.h_s"; "PHeapRz.U_DRV"; "RocqVerifyHarness.AgentSubmission.Heap.MStrat.GB"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Heap.KCost.sall"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cptr"; "RocqVerifyHarness.AgentSubmission.Heap.MAll.MPOST"; "RocqVerifyHarness.AgentSubmission.Heap.MAll.KM"; "RocqVerifyHarness.AgentSubmission.Heap.MAll.CM"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cmalloc"; "PHeapRz.COND"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.Run.segments_reserved"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "PHeapRz.KD"; "RocqVerifyHarness.AgentSubmission.U.U_heap.U_heap_init_hyps"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.U.U_heap.hst"; "RocqVerifyHarness.AgentSubmission.U.U_heap.PHEAP"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.U.U_heap.h_top"; "PHeapRz.U_nosmall"].


Section PHeapRz.
Variable sp0 : word.
Local Notation PL := (U_layout sp0).
Local Notation PHI := (U_HI sp0).
Local Notation PHEAP := (PHEAP sp0).
Local Notation ACEIL := (@alloc_ceiling (U_layout sp0)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition KD (k : nat) (mo : Model) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_heap_rz ()) "(0.(1.(2.(3.&40.))(4.O1.)(5.(3.&40.)))(0.(6.(7.(8.(9.(:.(3.&40.)(3.&40.))(;.O1.)))(<.+4.(8.O2.)))+3>8.)(0.(=.(:.(3.&40.)(3.&40.))Lp,(:.(3.&40.)(3.&40.))(6.(>.&40.(?.(3.&40.)(3.&40.)R1.))(10.+2.+23.))(;.O1.))(6.(7.(11.(12.O1.))(<.(8.O2.)(7.(10.+2.+1;.)(10.+2.+15.))))(13.(12.O1.))))))")
(* [comment removed for export] *).

Definition U_DRV (k : nat) (h : hst) (mo : Model) : Prop :=
  DRVc (ps_m (h_s h)) /\ shift (ps_m (h_s h)) + Z.of_nat k <= 14 /\ KD k mo.

Definition U_nosmall (h : hst) : Prop := nosmallb (ps_m (h_s h)) = true.

#[using="Type"] Lemma U_drv_mo : drv_mo_stmt usegs PL PHI U_DRV.
Proof.
  (intros k h mo mo' dd_H; ddestruct dd_H as (D & S & (M & L & F & B)); intros E1 E2 E3 E4). split; [exact D|]. split; [exact S|].
  unfold KD, kmaps in *. rewrite E1, E3. auto.
Qed.

#[using="Type"] Lemma U_drv_le : drv_le_stmt usegs PL PHI U_DRV.
Proof.
  (intros k k' h mo dd_H; ddestruct dd_H as (D & S & (M & L & F & B)); intros Hk). split; [exact D|]. split; [lia|]. split; [exact M|]. split; [lia|]. split; [exact F| nia].
Qed.

#[using="Type"] Lemma KD_kres k mo : KD (S k) mo -> kres 2 (GB + MA) mo.
Proof.
  (intros dd_H; ddestruct dd_H as (M & L & F & B)). constructor; [exact M| lia| exact F| unfold GB, MA; lia| unfold GB, MA; nia].
Qed.

#[using="Type"] Lemma KD_grow k mo mo' : KD (S k) mo -> kgrow KM CM mo mo' -> KD k mo'.
Proof.
  (intros dd_H; ddestruct dd_H as (M & L & F & B); intros [C0 GM GL GR GLI GLV GS]). unfold KD in *. rewrite GLI.
  split; [auto|]. split; [unfold KM in GL; lia|]. split.
  - apply GS; [unfold CM, GB, CAM, MA, PGSZ; lia| exact F].
  - unfold CM, GB, CAM, MA, PGSZ in GLV. nia.
Qed.

#[using="Type"] Lemma KD_keep k mo mo' : KD k mo -> kgrow 0 0 mo mo' -> KD k mo'.
Proof.
  (intros dd_H; ddestruct dd_H as (M & L & F & B); intros [C0 GM GL GR GLI GLV GS]). unfold KD in *. rewrite GLI.
  split; [auto|]. split; [lia|]. split; [apply GS; [lia| exact F]| lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma strip_facts st : UND st -> UND (strip st). Proof. intros U m. exact (U m). Qed.

#[using="Type"] Lemma drv_ctrl X s mo : ltac2:(CDefT.buildp (gd_tbl_P_heap_rz ()) "P,(14.O3.$15.O2.O1.)P,(16.(17.O2.))(0.(18.(17.O2.))(0.(6.=(19.(17.O2.)))Pb,$1:.Pm,$1:.Pai,$1;.P,(1.(1<.$1=.)(1>.$1:.$1=.(1?.$1:.(20.$21.$22.$1;.$23.)(24.$21.$22.$25.$1;.$23.$26.)$1=.)(27.$1:.(20.$21.$22.$1;.$23.)(24.$21.$22.$25.$1;.$23.$26.)$1=.)R3.(28.(17.O2.)))(29.$1=.(2:.(29.$1:.R2.)R1.)))(2;.(1.$2<.(2=.(2>.(17.O2.)R3.))(2?.$1:.)))))")
(* [comment removed for export] *).
Proof.
  intros [(L & CR & _ & _) _] D. destruct (creach_sim _ _ CR) as (st & BL & LS & Est & INV & _). rewrite <- Est in *.
  split; [apply strip_facts; apply (inv_UND st L BL LS INV); exact D|].
  split; [rewrite shift_strip; apply (inv_shift_nonneg st L BL LS INV)|].
  intros b m ai Hb. cbn in Hb. change (MR (strip st) m) with (MR st m). rewrite (inv_group_mem st L BL LS INV b m ai Hb). discriminate.
Qed.

#[using="Type"] Lemma drv_mem_set X s mo : ltac2:(CDefT.buildp (gd_tbl_P_heap_rz ()) "P,(14.O3.$15.O2.O1.)Pb,$1:.Pm,$1:.Pai,$1;.P,(1.(1<.$1=.)(1>.$1:.$1=.(1?.$1:.(20.$21.$22.$1;.$23.)(24.$21.$22.$25.$1;.$23.$26.)$1=.)(27.$1:.(20.$21.$22.$1;.$23.)(24.$21.$22.$25.$1;.$23.$26.)$1=.)R3.(28.(17.O2.)))(29.$1=.(2:.(29.$1:.R2.)R1.)))(2;.(1.$2<.(2=.(2>.(17.O2.)R3.))(2?.$1:.)))")
(* [comment removed for export] *).
Proof.
  intros [(L & CR & _ & _) _] b m ai Hb. destruct (creach_sim _ _ CR) as (st & BL & LS & Est & INV & _). rewrite <- Est in *.
  cbn in Hb. change (MR (strip st) m) with (MR st m). rewrite (inv_group_mem st L BL LS INV b m ai Hb). discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition COND (n : Z) (h : hst) : Prop := (n = 65536 /\ U_nosmall h) \/ MMAP_THRESHOLD_Z <= n.

#[using="Type"] Lemma cond_sall n h X mo : ltac2:(CDefT.buildp (gd_tbl_P_heap_rz ()) "P,(14.O2.$15.(30.O3.)O1.)P,(31.#1.O3.O1.)P,(6.=O4.)P,(6.(7.O4.+2014.)$32.)(33.(34.(:.$35.(1<.$36.))(37.(17.(30.O3.)))$38.$39.(3:.(17.(30.O3.))O4.))(2;.(3;.O4.O3.)))")
(* [comment removed for export] *).
Proof.
  (intros OW dd_H; ddestruct dd_H as (D & S & _); intros Hn HnB).
  pose proof (drv_ctrl _ _ _ OW D) as (U & S0 & _).
  destruct (Z_le_dec MMAP_THRESHOLD_Z n) as [BIG|NBIG].
  { left. apply cmalloc_sall_big; [lia| exact BIG| exact HnB]. }
  destruct (Z.eq_dec n 65536) as [->|NE]; [| right; intros [[E _]|E]; lia].
  destruct (nosmallb (ps_m (h_s h))) eqn:NS; [| right; intros [[_ E]|E]; [unfold U_nosmall in E; congruence| lia]].
  left. pose proof OW as [(L & CR & _ & _) _]. destruct (creach_sim _ _ CR) as (st & BL & LS & Est & INV & _).
  apply nosmallb_sound in NS. rewrite <- Est in NS |- *.
  apply cmalloc_sall_65536; [rewrite shift_strip; split; [apply (inv_shift_nonneg st L BL LS INV)| rewrite <- (shift_strip st), Est; lia]| |].
  - change (active (strip st) 44) with (active st 44). apply (inv_nosmall_active44 st L BL LS INV). exact NS.
  - change (usage (strip st) 44) with (usage st 44). apply (inv_nosmall_usage44 st L BL LS INV). exact NS.
Qed.

#[using="Type"] Theorem U_malloc_rz : malloc_rz_stmt usegs PL PHI U_DRV U_nosmall.
Proof.
  intros k ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB n lo A B
         HH DRV ST CLO LO MI TP SPB A0 N HA HB KA KB.
  cbn [HEAP heap_top U_HI] in *. change (hl_stack PL) with 8224 in *. change (hl_tp PL) with RATP in *. change (hl_malloc PL) with RMALLOC_SYM in *.
  dpose HH as (ELB & RH & OW & AUX & [errv ERR] & MRP). set (hRP := HRP sp0 (h_rc h)) in *.
  assert (ERR' : rw_cells rsegs m (errno_addr tp) [C4 errv]) by (rewrite (errno_addr_RATP tp TP); exact ERR).
  pose proof (rmalloc_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                (h_s h) (h_blocks h) n lo (h_top h) errv RH AUX SPB ST CLO ltac:(unfold RMALLOC_STACK; lia) ERR' MI TP A0 ltac:(lia)) as IM.
  pose proof OW as [(L & CR & HK & _) _].
  dpose DRV as (D & SH & KDk).
  pose proof (drv_ctrl _ _ _ OW D) as (U & SH0 & _).
  assert (HnB : n + 8212 <= GB) by (unfold GB; lia).
  assert (PRE : split_pre (map blk_id (h_blocks h)) GT n (h_s h) mo).
  { split; [exact OW|]. split; [exact U|]. split; [lia|]. split; [lia|]. split; [exact HnB| exact (KD_kres _ _ KDk)]. }
  pose proof (raw_malloc_splits _ _ n (h_s h) mo frame_ok_GT PRE) as SPL.
  (* [comment removed for export] *)
  pose proof (raw_malloc_spec_c (map blk_id (h_blocks h)) GT n frame_ok_GT ltac:(lia) (h_s h) mo OW) as W1.
  set (PC := fun (p : option bptr * PState) (mo' : Model) =>
         COND n h -> (exists st r, MPOST (ps_m (h_s h)) (st, r) /\ ps_m (snd p) = st) /\ kgrow KM CM mo mo').
  assert (W2 : etwf (raw_malloc n (h_s h)) mo (fun p mo' =>
            match fst p with Some q => OWN (q :: map blk_id (h_blocks h)) GT (snd p) mo' /\ n < 2 ^ 63 | None => OWN (map blk_id (h_blocks h)) GT (snd p) mo' end
            /\ PC p mo')).
  { destruct (cond_sall n h _ mo OW ltac:(eapply U_drv_le; [exact DRV| lia]) ltac:(lia) HnB) as [SA|NC].
    - eapply etwf_mono; [eapply eall_twf_conj; [exact (raw_malloc_eall _ GT frame_ok_GT n (h_s h) mo _ KM CM OW ltac:(lia) SA)| exact W1]|].
      cbn beta. intros p mo' [[HQ KG] HW]. split; [exact HW|]. intros _. split; [exact HQ| exact KG].
    - eapply etwf_mono; [exact W1|]. cbn beta. intros p mo' HW. split; [exact HW|]. intros HC. destruct (NC HC). }
  clear W1.
  unfold implM in IM.
  apply (impl_realizes_alt2 rsegs (raw_malloc n (h_s h)) _ _ is_none_leaf A B _ mo (tmm_raw_malloc n (h_s h)) IM W2
           (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) SPL HA HB).
  - (* [comment removed for export] *)
    intros [|[[p|] s']] ms' mo' HL HQ HP M1 M2 M3; cbn in HL, HP; [destruct HP| discriminate|].
    destruct HP as [OW' _]. cbn in HQ.
    ddestruct HQ as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & errv' & -> & MI2 & ST2 & ERR2 & AUX2 & PRES & _ & _ & -> & RH').
    rewrite (errno_addr_RATP tp TP) in ERR2.
    apply (KA u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m' mo' (mkHST (h_rc h) s' (h_blocks h) (h_top h))).
    + exact MI2.
    + exact ST2.
    + apply mo_frame_of_vm_only. exact M3.
    + rewrite ELB. apply heap_pres_of_r. exact PRES.
    + reflexivity.
    + split; [exact ELB|]. split; [exact RH'|]. split; [exact OW'|]. split; [exact AUX2|]. split; [exists errv'; exact ERR2| exact (malloc_replaced_pres _ _ _ _ PRES MRP)].
    + split; [exact M2| exact M1].
  - (* [comment removed for export] *)
    intros [|[[p|] s']] ms' mo' HL HQ HP M1 M2 M3; cbn in HL, HP; [destruct HP| | discriminate].
    destruct HP as [[OW' _] HPC]. cbn in HQ.
    ddestruct HQ as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & errv' & -> & MI2 & ST2 & ERR2 & AUX2 & PRES & _ & _ & A0' & junk & -> & BR & RH' & UCH & _ & _).
    rewrite (errno_addr_RATP tp TP) in ERR2.
    apply (KB u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m' mo' (mkHST (h_rc h) s' ((p, A0', n) :: h_blocks h) (h_top h)) A0' junk).
    + exact MI2.
    + exact ST2.
    + apply mo_frame_of_vm_only. exact M3.
    + rewrite ELB. apply heap_pres_of_r. exact PRES.
    + reflexivity.
    + apply (block_range_r sp0 (h_rc h)). exact BR.
    + split; [rewrite ELB; reflexivity|]. split; [exact RH'|]. split; [exact OW'|]. split; [exact AUX2|]. split; [exists errv'; exact ERR2| exact (malloc_replaced_pres _ _ _ _ PRES MRP)].
    + split; [exact M2| exact M1].
    + exact UCH.
    + intros HC. ddestruct (HPC HC) as ((st & r & [MG HS] & Est) & KG). cbn [fst snd h_s] in Est, MG, HS. subst st.
      unfold U_DRV. cbn [h_s]. split; [| split; [lia| exact (KD_grow _ _ _ KDk KG)]].
      eapply mgok_DRVc; [exact MG| exact (drv_mem_set _ _ _ OW')| exact D].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem U_free_c : free_c_stmt usegs PL PHI U_DRV.
Proof.
  intros k ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB A n lo
         HH DRV HIN ST CLO LO MI TP SPB A0.
  cbn [HEAP heap_top U_HI] in *. change (hl_stack PL) with 8224 in *. change (hl_tp PL) with RATP in *. change (hl_free PL) with RFREE_SYM in *.
  dpose HH as (ELB & RH & OW & AUX & [errv ERR] & MRP). set (hRP := HRP sp0 (h_rc h)) in *.
  assert (ERR' : rw_cells rsegs m (errno_addr tp) [C4 errv]) by (rewrite (errno_addr_RATP tp TP); exact ERR).
  rewrite ELB in HIN.
  destruct (lb_remove_first (h_blocks h) A n (RHEAP_blocks_nodup_proof _ _ _ RH) HIN) as (b & n' & Hb & Eb & EM & PERM).
  set (p := blk_id b) in *. set (X' := map blk_id (Malloc_iface.lb_remove p (h_blocks h))) in *.
  assert (OW' : OWN (p :: X') GT (h_s h) mo) by (eapply OWN_perm; [apply Permutation_sym; exact PERM| exact OW]).
  pose proof (rfree_spec_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                (h_s h) (h_blocks h) p A n' lo (h_top h) errv RH ltac:(rewrite <- Eb; exact Hb) AUX SPB ST CLO ltac:(unfold RFREE_STACK; lia) ERR' MI TP A0) as IM.
  pose proof OW' as [(L & CR & HK & INCL) _].
  dpose DRV as (D & SH & KDk).
  pose proof (drv_ctrl _ _ _ OW D) as (U & SH0 & _).
  (* [comment removed for export] *)
  assert (SA : sall (FPOST (ps_m (h_s h))) 0%nat 0 (cfree (ps_m (h_s h)) (Some (fst p)))).
  { destruct (creach_sim _ _ CR) as (st & BL & LS & Est & INV & LIVE).
    assert (Hc : In (fst p) (map bslot BL)) by (rewrite <- LIVE; apply INCL; left; reflexivity).
    apply in_map_iff in Hc as ([[c off] sz] & Ec & HinBL). cbn [bslot fst] in Ec. subst c.
    assert (D' : DRVc st). { intros bb mm ai H. pose proof (D bb mm ai) as X. rewrite <- Est in X. exact (X H). }
    ddestruct (inv_free_facts st L BL LS INV (fst p) off sz D' HinBL) as (g & bb & H1 & H2 & H3 & H4 & H5).
    rewrite <- Est. apply (cfree_sall (strip st) (fst p) g bb); try assumption.
    - apply strip_facts. apply (inv_UND st L BL LS INV D').
    - rewrite shift_strip. apply (inv_shift_nonneg st L BL LS INV). }
  pose proof (raw_free_spec_c X' GT p frame_ok_GT (h_s h) mo OW') as W1.
  pose proof (raw_free_eall X' GT frame_ok_GT p (h_s h) mo _ 0%nat 0 OW' SA) as W2.
  pose proof (eall_twf_conj _ _ _ _ W2 W1) as W. clear W1 W2.
  unfold implM in IM.
  pose proof (impl_twf_aevt rsegs (raw_free p (h_s h)) _ _ _ mo (tmm_raw_free p (h_s h)) IM W (kl_minv _ _ _ HK) (kl_halt _ _ _ HK)) as AE.
  eapply aevt_mono; [exact AE|]. clear AE IM W.
  (intros [ms' mo'] dd_H; ddestruct dd_H as ([|[[] s']] & HQ & HP & MI' & HH' & VO)); cbn [cfg_ms cfg_model] in *; [destruct HP|].
  ddestruct HP as [[[MG HSf] KG] OWf]. cbn [fst snd] in MG, HSf, OWf.
  ddestruct HQ as (u0 & u1 & u2 & v & v0 & v1 & v2 & v3 & v4 & v5 & v6 & u3 & u4 & u5 & u6 & m' & -> & MI2 & ST2 & ERR2 & AUX2 & PRES & _ & _ & RH').
  unfold call_post. deexists 17. split; [reflexivity|].
  split; [exact MI2|]. split; [exact ST2|]. split; [apply mo_frame_of_vm_only; exact VO|].
  split; [rewrite ELB, <- EM; apply heap_pres_of_r; exact PRES|].
  rewrite (errno_addr_RATP tp TP) in ERR2.
  exists (mkHST (h_rc h) s' (Malloc_iface.lb_remove p (h_blocks h)) (h_top h)). split; [reflexivity|]. split.
  - split; [rewrite ELB; symmetry; exact EM|]. split; [exact RH'|]. split; [exact OWf|]. split; [exact AUX2|]. split; [exists errv; exact ERR2| exact (malloc_replaced_pres _ _ _ _ PRES MRP)].
  - split; [| split; [cbn [h_s]; rewrite HSf; exact SH| exact (KD_keep _ _ _ KDk KG)]].
    cbn [h_s]. eapply mgok_DRVc; [exact MG| exact (drv_mem_set _ _ _ OWf)| exact D].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma KD_init mo : ltac2:(CDefT.buildp (gd_tbl_P_heap_rz ()) "P,(1.(2.(:.(3.&40.)(3.&40.)))(3<.(12.O1.))(5.(:.(3.&40.)(3.&40.))))P,(1.(2.(:.(3.&40.)(3.&40.)))(3=.(12.O1.))(3>.$3?.))P,(1.(2.(3.&40.))(4.O1.)(5.(3.&40.)))P,(6.(10.+2.+1?.)(13.(12.O1.)))(40.#>.O1.)")
(* [comment removed for export] *).
Proof.
  intros M R MT LIM. unfold KD, kmaps, vm_live_bytes. rewrite M, R, app_nil_r.
  split; [exact MT|]. split; [| split; [| change (live_bytes []) with 0; lia]].
  - match goal with |- Z.of_nat ?l + _ <= _ => let v := eval vm_compute in l in change l with v end. lia.
  - match goal with |- Forall _ ?l => let v := eval vm_compute in l in change l with v end.
    repeat (constructor; [match goal with |- bv_unsigned ?x <= _ => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia|]). constructor.
Qed.

#[using="Type"] Theorem U_heap_init_drv rc m mo top : ltac2:(CDefT.buildp (gd_tbl_P_heap_rz ()) "P,(41.Vsp0,O4.O3.O2.O1.)P,(1.(2.(3.&40.))(4.O2.)(5.(3.&40.)))P,(6.(10.+2.+1?.)(13.(12.O2.)))(42.$43.Lh,$43.(0.(44.Vsp0,R1.(5.$45.)O3.O2.)(0.(1.$1;.(46.R1.)O1.)(0.(31.#>.R1.O2.)(47.R1.)))))")
(* [comment removed for export] *).
Proof.
  intros HI MT LIM. ddestruct (U_heap_init_s sp0 rc m mo top HI) as (h & HP & HT & HS & HB & HRC).
  exists h. split; [exact HP|]. split; [exact HT|]. split.
  - split; [| split; [rewrite HS; match goal with |- shift ?x + _ <= _ => change (shift x) with 0 end; lia| apply KD_init; [apply (phi_maps _ _ _ _ _ HI)| apply (phi_resv _ _ _ _ _ HI)| exact MT| exact LIM]]].
    rewrite HS. intros b mm ai H. match type of H with s_groups ?x !! _ = _ => change (s_groups x) with (∅ : gmap aptr ghdr) in H end. rewrite lookup_empty in H. discriminate.
  - unfold U_nosmall. rewrite HS. reflexivity.
Qed.

End PHeapRz.
