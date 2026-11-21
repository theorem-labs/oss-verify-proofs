(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: the ubsan binary's copy of Ref/MallocSRI.v: the heap theorems of Ub/MallocSR.v at the instance HSI, whose reach over usegs carries a configuration invariant to every reached state (SReachTreeInv.v); the invariant is kept by the machine steps (INV_MS) and by each mm node's step (INV_NODE). *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac ITree Nodes SysStep Exec.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim Monad MSafeP STree Malloc MallocCtrl Prog KInv MI_Inv MmNodes GapGrid KLink KLink2 KLink3.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require MI_Contracts.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Agent Require Import MallocBlocks MallocHINV MallocFacts_inv.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Agent Require Import Malloc_iface.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP RF_malloc_spec RF_free_spec.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import RBand.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require HeapSR_iface RMalloc_iface_stmt.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import SReach SReachTree SReachCjNodes.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import SReachTreeInv.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import MallocSR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [sreachI Inv Q c]: from a configuration where [Inv] holds, [c] reaches [Q] over the binary's
   own list ([sreach usegs]) and [Inv] holds where it arrives.  [HSI Inv] is [MallocSR.HS] with
   this reach in place of [sreach usegs]; every other field is [HS]'s.  The caller picks [Inv]:
   the run instance takes "the overlay holds no byte of the vDSO/vvar pair, and the pair stays
   the launch's reserved pair" (Ub/HeapSRRun.v, [run_inv]).  [INV_MS] and [INV_NODE] are the two
   obligations of [SReachTreeInv.impl_sreach_post_inv] at the mm nodes [MallocSR.bridge] passes
   to [SReachTree.impl_sreach_post]: [Inv] is kept by the machine steps between nodes, and by
   each node's step where the node's own safety holds. *)
Definition sreachI {HCEIL : HeapCeil} (Inv : config -> Prop) (Q : config -> Prop) (c : config) : Prop :=
  Inv c -> sreach usegs (fun c' => Q c' /\ Inv c') c.
Definition HSI {HCEIL : HeapCeil} {HSEC : HeapSecret} (Inv : config -> Prop) : HeapSR_iface.hsr :=
  HeapSR_iface.Build_hsr (sreachI Inv) KM vm_only RHEAP rauxv_ok lb_remove alloc_ok HBYTES HCNT HBIG hcanary.
Definition INV_MS (Inv : config -> Prop) : Prop :=
  forall ms ms' mo, Exec.msteps usegs ms ms' -> Inv (mkCfg ms mo) -> Inv (mkCfg ms' mo).
Definition INV_NODE (Inv : config -> Prop) : Prop :=
  forall n ms mo rsp mo' evs, at_node usegs n ms -> m_halted mo = None -> mminv mo -> mmsafe n mo ->
    Nodes.nstep n mo rsp mo' evs -> Inv (mkCfg ms mo) -> Inv (mkCfg (ITree.nret ms rsp) mo').

Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

(* The laws of [sreachI] the copied proofs use.  A finished reach needs [Inv] of the
   configuration it finishes at; [sreachI]'s premise supplies it. *)
Lemma sreachI_done : forall (Inv Q : config -> Prop) c, Q c -> sreachI Inv Q c.
Proof. intros Inv Q c HQ HI. apply sr_done. cbv beta. split; [exact HQ| exact HI]. Qed.

Lemma sreachI_mono : forall (Inv Q Q' : config -> Prop) c,
  sreachI Inv Q c -> (forall c', Q c' -> Q' c') -> sreachI Inv Q' c.
Proof.
  intros Inv Q Q' c H K HI. unfold sreachI in H.
  eapply sreach_mono; [exact (H HI)|].
  intros c' [HQ HI']. cbv beta. split; [exact (K c' HQ)| exact HI'].
Qed.

Lemma sreachI_seq : forall (Inv Q1 Q2 : config -> Prop) c,
  sreachI Inv Q1 c -> (forall c', Q1 c' -> sreachI Inv Q2 c') -> sreachI Inv Q2 c.
Proof.
  intros Inv Q1 Q2 c H K HI. unfold sreachI in H.
  eapply sreach_seq; [exact (H HI)|].
  intros c' [HQ1 HI']. exact (K c' HQ1 HI').
Qed.

(* [SReachTree.cj_evt_sreach] and [cj_evt_sreach_k] with [Inv] carried over the machine steps
   ([SReachTreeInv.cj_evt_sreach_inv], [cj_evt_sreach_k_inv]) *)
Lemma cj_evt_sreachI : forall (Inv : config -> Prop), INV_MS Inv ->
  forall (P : machine_state -> Prop) ms model,
  m_halted model = None -> m_vm_lazy model = [] ->
  Exec.evt usegs P ms ->
  sreachI Inv (fun c => P (cfg_ms c) /\ cfg_model c = model) (mkCfg ms model).
Proof.
  intros Inv HIms P ms model Hh Hl Hev HI.
  eapply sreach_mono; [exact (cj_evt_sreach_inv usegs Inv HIms P ms model Hh Hl Hev HI)|].
  intros c (HP & Hmo & HIc). cbv beta. split; [split; [exact HP| exact Hmo]| exact HIc].
Qed.

Lemma cj_evt_sreachI_k : forall (Inv : config -> Prop), INV_MS Inv ->
  forall (P : machine_state -> Prop) ms model (Q : config -> Prop),
  m_halted model = None -> m_vm_lazy model = [] ->
  Exec.evt usegs P ms ->
  (forall ms', P ms' -> sreachI Inv Q (mkCfg ms' model)) ->
  sreachI Inv Q (mkCfg ms model).
Proof.
  intros Inv HIms P ms model Q Hh Hl Hev K HI.
  apply (cj_evt_sreach_k_inv usegs Inv HIms P ms model (fun c' => Q c' /\ Inv c') Hh Hl Hev HI).
  intros ms' HP HI'. exact (K ms' HP HI').
Qed.

(* [MallocSR.bridge] with [Inv] carried: [SReachTreeInv.impl_sreach_post_inv] in place of
   [SReachTree.impl_sreach_post], with the same arguments plus [Inv], its two obligations and
   [Inv] of the start configuration (the premise of [sreachI]). *)
Lemma bridge_I : forall (Inv : config -> Prop), INV_MS Inv -> INV_NODE Inv ->
  forall (A : Type) (c : Monad.M PState A) (s : PState) (Qm : A -> PState -> machine_state -> Prop)
    (P : assn PState) (Qk : A -> assn PState) ms mo,
  implM usegs c s Qm ms ->
  MSafeP.mspec mmsafe P c Qk -> P s mo -> m_halted mo = None -> mminv mo ->
  tforall mm_only (c s) ->
  sreachI Inv (fun cf => exists a s', Qm a s' (cfg_ms cf) /\ Qk a s' (cfg_model cf)
                           /\ m_halted (cfg_model cf) = None /\ mminv (cfg_model cf)) (mkCfg ms mo).
Proof. try hcb. try hsb.
  intros Inv HIms HInode A c s Qm P Qk ms mo IM MS HP HH MI TF HI.
  pose proof (MS s mo HP) as TW. unfold etwf in TW.
  eapply sreach_mono.
  { eapply (impl_sreach_post_inv usegs (at_node usegs) Nodes.nstep Nodes.nexit mminv mmsafe (fun _ => nret) (mm_node_sound usegs) mminv_lazy
              Inv HIms HInode (c s) _ ms mo (fun r mo' => match r with Unr => False | Ok p => Qk (fst p) (snd p) mo' end)).
    - exact IM.
    - exact HH.
    - exact MI.
    - eapply twf_tsafe. exact TW.
    - apply tsilent_of_mm. exact TF.
    - exact HI.
    - intros r mo' TP. exact (twf_tpath mmsafe _ _ _ _ _ _ TW TP). }
  intros cf (r & HQ & HMQ & HH' & MI' & HIc). destruct r as [|[a s']]; [destruct HMQ|]. cbn in HQ, HMQ.
  cbv beta. split; [exists a, s'; auto| exact HIc].
Qed.

Theorem malloc_sr_at_I : forall (P2 : PHASE2) (Inv : config -> Prop), INV_MS Inv -> INV_NODE Inv ->
  forall entry stack,
  (forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv,
     RHEAP s LB m -> rauxv_ok m B -> bv_unsigned sp <= B ->
     stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - stack ->
     rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = Z_to_bv 64 RATP -> a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
     implM usegs (raw_malloc n) s (rmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 entry) fc None m (seg_rom usegs))) ->
  HeapSR_iface.malloc_sr_stmt_at (HSI Inv) entry stack.
Proof. try hcb. try hsb.
  intros P2 Inv HIms HInode entry stack SPEC. unfold HeapSR_iface.malloc_sr_stmt_at. cbn [HeapSR_iface.hs_SR HeapSR_iface.hs_KREL HeapSR_iface.hs_MPRES HeapSR_iface.hs_RHEAP HeapSR_iface.hs_rauxv_ok HeapSR_iface.hs_alloc_ok HSI].
  intros until mo. intros HR KMs AOK AUX HB ST CLO LO ERR MI TP A0 N.
  pose proof KMs as (L & CR & K & B0).
  pose proof (SPEC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv HR AUX HB ST CLO LO ERR MI TP A0 ltac:(lia)) as IM.
  pose proof (raw_malloc_spec [] (Gvm mo) n (Gvm_frame mo) ltac:(lia)) as MSP.
  assert (PRE : OWN [] (Gvm mo) s mo /\ MBUD (ps_m s) n).
  { split; [| exact (MBUD_of_bounds P2 s LB m n HR AOK)]. split; [exists L; splits; auto; intros c []|]. split; [constructor| apply vm_only_refl]. }
  eapply sreachI_mono; [apply (bridge_I Inv HIms HInode _ _ _ _ _ _ _ _ IM MSP PRE (kb_halt _ _ _ K) (kb_minv _ _ _ K) (tforall_raw_malloc n s))|].
  intros cf (r & s' & HQ & HK & HH' & MI'). cbn in HK.
  destruct r as [p|]; [| destruct HK].
  destruct HK as [((L' & CR' & K' & _ & B') & _ & VO) _].
  unfold rmalloc_post in HQ.
  destruct HQ as (u0 & u1 & u2 & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m' & errv' & Ems & MI2 & ST2 & ERR2 & AUX2 & PRES & _ & _ & (A & junk & -> & RNG & HR2 & CELLS & _)).
  unfold HeapSR_iface.malloc_sr_post.
  exists u0, u1, u2, w1, w2, w3, w4, w5, w6, w7, u3, u4, u5, u6, m', errv', A, junk, p, s'.
  splits; auto.
  - exists L'. splits; auto.
Qed.

Theorem malloc_sr_at_off_I : forall (P2 : PHASE2) (Inv : config -> Prop), INV_MS Inv -> INV_NODE Inv ->
  forall entry stack,
  (forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv,
     RHEAP s LB m -> rauxv_ok m B -> bv_unsigned sp <= B ->
     stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - stack ->
     rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = Z_to_bv 64 RATP -> a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
     implM usegs (raw_malloc n) s (rmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 entry) fc None m (seg_rom usegs))) ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (n lo B : Z) (errv : word) (mo : Model),
    RHEAP s LB m -> KM s mo -> alloc_ok s LB n ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - stack ->
    rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = Z_to_bv 64 RATP ->
    a0 = Z_to_bv 64 n -> 1 <= n < HeapSR_iface.RMMAP_THRESHOLD ->
    sreachI Inv (malloc_sr_post_off ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m mo)
       (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 entry) fc None m (seg_rom usegs)) mo).
Proof. try hcb. try hsb.
  intros P2 Inv HIms HInode entry stack SPEC.
  intros until mo. intros HR KMs AOK AUX HB ST CLO LO ERR MI TP A0 N. unfold HeapSR_iface.RMMAP_THRESHOLD in N.
  pose proof KMs as (L & CR & K & B0).
  pose proof (SPEC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv HR AUX HB ST CLO LO ERR MI TP A0 ltac:(lia)) as IM.
  pose proof (raw_malloc_spec [] (Gvm mo) n (Gvm_frame mo) ltac:(lia)) as MSP.
  assert (PRE : OWN [] (Gvm mo) s mo /\ MBUD (ps_m s) n).
  { split; [| exact (MBUD_of_bounds P2 s LB m n HR AOK)]. split; [exists L; splits; auto; intros c []|]. split; [constructor| apply vm_only_refl]. }
  eapply sreachI_mono; [apply (bridge_I Inv HIms HInode _ _ _ _ _ _ _ _ IM MSP PRE (kb_halt _ _ _ K) (kb_minv _ _ _ K) (tforall_raw_malloc n s))|].
  intros cf (r & s' & HQ & HK & HH' & MI'). cbn in HK.
  destruct r as [p|]; [| destruct HK].
  destruct HK as [((L' & CR' & K' & _ & B') & _ & VO) _].
  unfold rmalloc_post in HQ.
  destruct HQ as (u0 & u1 & u2 & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m' & errv' & Ems & MI2 & ST2 & ERR2 & AUX2 & PRES & _ & _ & (A & junk & -> & RNG & HR2 & CELLS & _ & OFF & CLSP)).
  unfold malloc_sr_post_off.
  exists u0, u1, u2, w1, w2, w3, w4, w5, w6, w7, u3, u4, u5, u6, m', errv', A, junk, p, s'.
  splits; auto.
  - exists L'. splits; auto.
Qed.

Theorem malloc_sr_I : forall (P2 : PHASE2) Inv, INV_MS Inv -> INV_NODE Inv -> HeapSR_iface.malloc_sr_stmt (HSI Inv).
Proof. try hcb. try hsb.
  intros P2 Inv HIms HInode.
  apply (malloc_sr_at_I P2 Inv HIms HInode). intros. eapply rmalloc_spec; eauto.
Qed.

Theorem free_sr_at_I : forall (Inv : config -> Prop), INV_MS Inv -> INV_NODE Inv ->
  forall entry,
  (forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv,
     RHEAP s LB m -> In (p, A, n) LB -> rauxv_ok m B -> bv_unsigned sp <= B ->
     stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
     rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = Z_to_bv 64 RATP -> a0 = Z_to_bv 64 A ->
     implM usegs (raw_free p) s (rfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 entry) fc None m (seg_rom usegs))) ->
  HeapSR_iface.free_sr_stmt_at (HSI Inv) entry.
Proof. try hcb. try hsb.
  intros Inv HIms HInode entry SPEC. unfold HeapSR_iface.free_sr_stmt_at. cbn [HeapSR_iface.hs_SR HeapSR_iface.hs_KREL HeapSR_iface.hs_MPRES HeapSR_iface.hs_RHEAP HeapSR_iface.hs_rauxv_ok HeapSR_iface.hs_lb_remove HSI].
  intros until mo. intros HR KMs HIN AUX HB ST CLO LO ERR MI TP A0.
  pose proof KMs as (L & CR & K & B0).
  pose proof (SPEC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv HR HIN AUX HB ST CLO LO ERR MI TP A0) as IM.
  pose proof (raw_free_spec [] (Gvm mo) p (Gvm_frame mo)) as MSP.
  assert (PRE : OWN [p] (Gvm mo) s mo).
  { split; [exists L; splits; auto|].
    - intros c [<-|[]]. exact (rheap_block_live s LB m L (p, A, n) HR HIN (hreach_creach _ _ CR)).
    - split; [| apply vm_only_refl]. cbn. constructor; [intros []| constructor]. }
  eapply sreachI_mono; [apply (bridge_I Inv HIms HInode _ _ _ _ _ _ _ _ IM MSP PRE (kb_halt _ _ _ K) (kb_minv _ _ _ K) (tforall_raw_free p s))|].
  intros cf (r & s' & HQ & HK & HH' & MI'). cbn in HK.
  destruct HK as ((L' & CR' & K' & _ & B') & _ & VO).
  unfold rfree_post in HQ.
  destruct HQ as (u0 & u1 & u2 & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m' & Ems & MI2 & ST2 & ERR2 & AUX2 & PRES & _ & _ & HR2).
  unfold HeapSR_iface.free_sr_post.
  exists u0, u1, u2, w0, w1, w2, w3, w4, w5, w6, w7, u3, u4, u5, u6, m', s'.
  splits; auto.
  exists L'. splits; auto.
Qed.

Theorem free_sr_I : forall (P2 : PHASE2) Inv, INV_MS Inv -> INV_NODE Inv -> HeapSR_iface.free_sr_stmt (HSI Inv).
Proof. try hcb. try hsb.
  intros P2 Inv HIms HInode.
  apply (free_sr_at_I Inv HIms HInode). intros. eapply rfree_spec_proof; eauto.
Qed.

Theorem free_null_sr_I : forall (P2 : PHASE2) Inv, INV_MS Inv -> INV_NODE Inv -> HeapSR_iface.free_null_sr_stmt (HSI Inv).
Proof. try hcb. try hsb.
  intros P2 Inv HIms HInode.
  unfold HeapSR_iface.free_null_sr_stmt, HeapSR_iface.free_null_sr_stmt_at. cbn [HeapSR_iface.hs_SR HSI]. intros until mo. intros HH HL.
  unfold HeapSR_iface.free_null_post.
  eapply sreachI_mono; [eapply (cj_evt_sreachI Inv HIms _ _ mo HH HL); apply (RMalloc_iface_stmt.rfree_null_spec); reflexivity|].
  intros c [H1 H2]. split; [exact H1| exact H2].
Qed.

End HCW.

