(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil HeapSecret.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac ITree Nodes SysStep Exec.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim Monad MSafeP STree Malloc MallocCtrl Prog KInv MI_Inv MmNodes GapGrid KLink KLink2 KLink3.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require MI_Contracts.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Agent Require Import MallocBlocks MallocHINV MallocFacts_inv.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Agent Require Import Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP RF_malloc_spec RF_free_spec.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import RBand.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ub Require HeapSR_iface RMalloc_iface_stmt.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import SReach SReachTree SReachCjNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma invl_live_transfer : forall st1 L1 BL1 LS1 st2 L2 BL2 LS2 c,
  INVL x0 st1 L1 BL1 LS1 -> INVL x0 st2 L2 BL2 LS2 -> strip st1 = strip st2 ->
  In c (map bslot BL1) -> In c (map bslot BL2).
Proof. try hcb. try hsb.
  intros st1 L1 BL1 LS1 st2 L2 BL2 LS2 c I1 I2 ES Hin.
  assert (EG : s_groups st2 = s_groups st1) by (apply (f_equal s_groups) in ES; cbn in ES; congruence).
  assert (EM : s_metas st2 = s_metas st1) by (apply (f_equal s_metas) in ES; cbn in ES; congruence).
  assert (ESL : s_slots st2 = s_slots st1) by (apply (f_equal s_slots) in ES; cbn in ES; congruence).
  assert (ER : forall m, MR st2 m = MR st1 m) by (intros m; unfold MR, get_meta_rec; rewrite EM; reflexivity).
  destruct I1 as (_ & _ & _ & _ & _ & S1 & _). destruct I2 as (_ & _ & _ & _ & _ & S2 & _).
  apply in_map_iff in Hin as (k & Ek & Hk).
  destruct (is_blocks _ _ _ S1 k Hk) as (m & i & Hs & _). rewrite Ek in Hs.
  destruct (is_valid _ _ _ S1 c m i Hs) as ((b & ai & Hb) & Hi & Ec).
  pose proof (is_part _ _ _ S1 b m ai i Hb Hi) as P1. pose proof (is_part _ _ _ S2 b m ai i ltac:(rewrite EG; exact Hb) ltac:(rewrite ER; exact Hi)) as P2.
  cbn zeta in P1, P2. rewrite ER, EG, <- Ec in P2. rewrite <- Ec in P1.
  assert (U1 : In c (map bslot BL1)) by (rewrite <- Ek; apply in_map; exact Hk).
  unfold one5 in P1, P2. cbn [x_pend x0] in P1, P2.
  destruct P2 as (D2 & _ & NAC & _ & _ & NFC & _). destruct P1 as (_ & _ & NAU & _ & _ & NFU & _ & _ & NUH & _).
  destruct D2 as [A|[F|[U|[H|X]]]]; [exfalso; (first [clear; solve [repeat split; exact I] | clear; tauto | (lazymatch goal with H1 : _ |- _ => revert H1; clear; tauto end) | tauto])| exfalso; (first [clear; solve [repeat split; exact I] | clear; tauto | (lazymatch goal with H1 : _ |- _ => revert H1; clear; tauto end) | tauto])| exact U| exfalso; (first [clear; solve [repeat split; exact I] | clear; tauto | (lazymatch goal with H1 : _ |- _ => revert H1; clear; tauto end) | tauto])| discriminate X].
Qed.

(* [comment removed for export] *)
Lemma rheap_block_live : forall s LB m L b,
  RHEAP s LB m -> In b LB -> creach (ps_m s) L -> In (blk_slot b) (ld_live L).
Proof. try hcb. try hsb.
  intros s LB m L b (st & LB0 & HP & Hst & MR & [_ AR] & _) Hb CR.
  destruct (areach_inv _ _ _ AR) as (L1 & LS1 & BL1 & I1 & LIVE1 & _ & _ & CORR1).
  destruct (MI_Contracts.creach_sim _ _ CR) as (st2 & BL2 & LS2 & Est2 & I2 & LIVE2).
  rewrite LIVE2. apply (invl_live_transfer st L1 BL1 LS1 st2 L BL2 LS2); [exact I1| exact I2| rewrite Est2; exact Hst|].
  assert (Hb0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hb]).
  destruct (Forall2_In_l _ _ _ _ CORR1 Hb0) as (k & Hk & (C1 & _ & _)). rewrite C1. apply in_map. exact Hk.
Qed.

Lemma Forall2_In_r {A B} (P : A -> B -> Prop) l1 l2 b : Forall2 P l1 l2 -> In b l2 -> exists a, In a l1 /\ P a b.
Proof. try hcb. try hsb.
  intros H. induction H as [|x y l1' l2' Hxy H IH]; intros Hin; [destruct Hin|].
  destruct Hin as [<-|Hin]; [exists x; split; [left; reflexivity| exact Hxy]|].
  destruct (IH Hin) as (a & Ha & HP). exists a. split; [right; exact Ha| exact HP].
Qed.

(* [comment removed for export] *)
Lemma rheap_live_block : forall s LB m L c,
  RHEAP s LB m -> creach (ps_m s) L -> In c (ld_live L) -> In c (map blk_slot LB).
Proof. try hcb. try hsb.
  intros s LB m L c (st & LB0 & HP & Hst & MR & [_ AR] & _) CR Hc.
  destruct (areach_inv _ _ _ AR) as (L1 & LS1 & BL1 & I1 & LIVE1 & _ & _ & CORR1).
  destruct (MI_Contracts.creach_sim _ _ CR) as (st2 & BL2 & LS2 & Est2 & I2 & LIVE2).
  rewrite LIVE2 in Hc.
  assert (H1 : In c (map bslot BL1)).
  { apply (invl_live_transfer st2 L BL2 LS2 st L1 BL1 LS1); [exact I2| exact I1| rewrite Est2, Hst; reflexivity| exact Hc]. }
  apply in_map_iff in H1 as (k & <- & Hk).
  destruct (Forall2_In_r _ _ _ _ CORR1 Hk) as (b & Hb0 & (C1 & _)).
  rewrite <- C1. apply in_map. eapply Permutation_in; [exact HP| exact Hb0].
Qed.

Lemma rheap_live_cnt_ok : forall s LB m L,
  RHEAP s LB m -> creach (ps_m s) L -> Z.of_nat (length LB) + 1 <= HCNT -> live_cnt_ok L.
Proof. try hcb. try hsb.
  intros s LB m L HR CR HL. exists (map blk_slot LB). split; [| rewrite map_length; exact HL].
  intros c Hc. exact (rheap_live_block s LB m L c HR CR Hc).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition KM (s : PState) (mo : Model) : Prop :=
  exists L, hreach (ps_m s) L /\ KLB L (ps_brk s) mo /\ BUD L mo 0 0.

Lemma KM_halted_lazy : forall s mo, KM s mo -> m_halted mo = None /\ m_vm_lazy mo = [].
Proof. try hcb. try hsb. intros s mo (L & _ & K & _). split; [exact (kb_halt _ _ _ K)| exact (proj1 (kb_minv _ _ _ K))]. Qed.

(* [comment removed for export] *)
Lemma KM_vm : forall s mo mo', KM s mo -> mminv mo' -> m_halted mo' = None -> m_vmmaps mo' = m_vmmaps mo -> KM s mo'.
Proof. try hcb. try hsb.
  intros s mo mo' (L & CR & K & B) MI HH E. exists L. split; [exact CR|]. split; [eapply KLB_vm_eq; eauto|].
  unfold BUD in *. rewrite E. exact B.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition HBYTES : Z := 2^30.
Definition HBIG : Z := 512.
Definition alloc_ok (s : PState) (LB : list block) (n : Z) : Prop :=
  0 <= n /\ HeapSR_iface.lb_bytes LB + n <= HBYTES /\ Z.of_nat (length LB) + 1 <= HCNT
  /\ HeapSR_iface.lb_big LB + HeapSR_iface.big1 n <= HBIG.

(* [comment removed for export] *)
Definition PHASE2 : Prop :=
  forall s LB m L n,
    RHEAP s LB m -> hreach (ps_m s) L ->
    0 <= n -> HeapSR_iface.lb_bytes LB + n <= HBYTES -> Z.of_nat (length LB) + 1 <= HCNT ->
    HeapSR_iface.lb_big LB + HeapSR_iface.big1 n <= HBIG ->
    ltotal L <= BUDCAP -> lcount L + RESV_MAX < GRID_J ->
    exists cb ck, 0 <= cb <= CBMAX /\ 0 <= ck
      /\ tbound (cmalloc (ps_m s) n) cb ck (fun r => snd r <> None)
      /\ ltotal L + cb <= BUDCAP /\ lcount L + ck + RESV_MAX < GRID_J.

Lemma MBUD_of_bounds : PHASE2 -> forall s LB m n,
  RHEAP s LB m -> alloc_ok s LB n -> MBUD (ps_m s) n.
Proof. try hcb. try hsb.
  intros P2 s LB m n HR (N0 & NB & NC & NG) L HRC B1 B2.
  pose proof (hreach_creach _ _ HRC) as CR.
  split; [exact (rheap_live_cnt_ok s LB m L HR CR NC)|].
  exact (P2 s LB m L n HR HRC N0 NB NC NG B1 B2).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mm_only (nd : node) : Prop := is_silent_kind nd = true.

Lemma tforall_msys {A} : forall n (dec : resp -> option A) (s : PState), is_silent_kind n = true -> tforall mm_only (msys (St:=PState) n dec s).
Proof. try hcb. try hsb. intros n dec s H. unfold msys, enode. cbn. split; [exact H|]. intros rsp. destruct (dec rsp); exact I. Qed.

Lemma tforall_mbind {A B} : forall (m : Monad.M PState A) (f : A -> Monad.M PState B) s,
  tforall mm_only (m s) -> (forall a s', tforall mm_only (f a s')) -> tforall mm_only (mbind m f s).
Proof. try hcb. try hsb. intros m f s Hm Hf. unfold mbind. apply tforall_ebind; [exact Hm|]. intros [a s']. apply Hf. Qed.

Lemma tforall_ev_step : forall e s, tforall mm_only (ev_step e s).
Proof. try hcb. try hsb.
  intros e s. destruct e as [req|addr len prot flags|addr len|addr len prot|? ? ?|?]; cbn -[msys mbind mret mupd mget munr tforall Z.eqb].
  - destruct (req =? 0).
    + apply tforall_mbind; [apply tforall_msys; reflexivity|]. intros a s'. apply tforall_mbind; [exact I|]. intros; exact I.
    + apply tforall_mbind; [exact I|]. intros a s'. apply tforall_mbind; [apply tforall_msys; reflexivity|].
      intros [|] s''; [apply tforall_mbind; [exact I| intros; exact I]| exact I].
  - destruct (negb _); [| destruct (prot =? 0)]; (apply tforall_mbind; [apply tforall_msys; reflexivity| intros; exact I]).
  - apply tforall_mbind; [apply tforall_msys; reflexivity| intros; exact I].
  - apply tforall_mbind; [apply tforall_msys; reflexivity| intros; exact I].
  - exact I.
  - exact I.
Qed.

Lemma tforall_membed {R} : forall (t : stree ev Z R) s, tforall mm_only (membed t s).
Proof. try hcb. try hsb.
  intros t. induction t as [r|e k IH]; intros s; cbn [membed]; [exact I|].
  apply tforall_mbind; [apply tforall_ev_step| intros; apply IH].
Qed.

Lemma tforall_raw_malloc : forall n s, tforall mm_only (raw_malloc n s).
Proof. try hcb. try hsb.
  intros n s. unfold raw_malloc. apply tforall_mbind; [exact I|]. intros s0 s'.
  apply tforall_mbind; [apply tforall_membed|]. intros [st' p] s''. apply tforall_mbind; [exact I|]. intros; exact I.
Qed.

Lemma tforall_raw_free : forall p s, tforall mm_only (raw_free p s).
Proof. try hcb. try hsb.
  intros p s. unfold raw_free. apply tforall_mbind; [exact I|]. intros s0 s'.
  apply tforall_mbind; [apply tforall_membed|]. intros; exact I.
Qed.

Lemma tsilent_of_mm {R} : forall (t : itree node R) mo, tforall mm_only t -> tsilent Nodes.nstep Nodes.nexit t mo.
Proof. try hcb. try hsb.
  intros t mo H. apply tforall_tsilent. revert H. induction t as [r|n k IH]; cbn; [auto|].
  intros [Hn Hk]. split; [exact (is_silent_kind_sound n Hn)|]. intros rsp. apply IH. apply Hk.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition Gvm (mo0 : Model) : PState -> Model -> Prop := fun _ mo => vm_only mo0 mo.
Lemma Gvm_frame : forall mo0, frame_ok (Gvm mo0).
Proof. try hcb. try hsb. intros mo0 s s' mo mo' _ _ VO H. unfold Gvm in *. eapply vm_only_trans; eauto. Qed.

Lemma bridge : forall {A} (c : Monad.M PState A) (s : PState) (Qm : A -> PState -> machine_state -> Prop)
    (P : assn PState) (Qk : A -> assn PState) ms mo,
  implM usegs c s Qm ms ->
  MSafeP.mspec mmsafe P c Qk -> P s mo -> m_halted mo = None -> mminv mo ->
  tforall mm_only (c s) ->
  sreach usegs (fun cf => exists a s', Qm a s' (cfg_ms cf) /\ Qk a s' (cfg_model cf)
                           /\ m_halted (cfg_model cf) = None /\ mminv (cfg_model cf)) (mkCfg ms mo).
Proof. try hcb. try hsb.
  intros A c s Qm P Qk ms mo IM MS HP HH MI TF.
  pose proof (MS s mo HP) as TW. unfold etwf in TW.
  eapply sreach_mono.
  { eapply (impl_sreach_post usegs (at_node usegs) Nodes.nstep Nodes.nexit mminv mmsafe (mm_node_sound usegs) mminv_lazy
              (c s) _ ms mo (fun r mo' => match r with Unr => False | Ok p => Qk (fst p) (snd p) mo' end)).
    - exact IM.
    - exact HH.
    - exact MI.
    - eapply twf_tsafe. exact TW.
    - apply tsilent_of_mm. exact TF.
    - intros r mo' TP. exact (twf_tpath mmsafe _ _ _ _ _ _ TW TP). }
  intros cf (r & HQ & HMQ & HH' & MI'). destruct r as [|[a s']]; [destruct HMQ|]. cbn in HQ, HMQ.
  exists a, s'. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition HS : HeapSR_iface.hsr :=
  HeapSR_iface.Build_hsr (sreach usegs) KM vm_only RHEAP rauxv_ok lb_remove alloc_ok HBYTES HCNT HBIG hcanary.

(* [comment removed for export] *)
Theorem alloc_ok_of_live_proof : HeapSR_iface.alloc_ok_of_live HS.
Proof. try hcb. try hsb. intros s LB m n _ H0 H1 H2 H3. cbn. unfold alloc_ok. auto. Qed.

Section WithPhase2.
Hypothesis P2 : PHASE2.

Lemma unsigned_sp_range : forall sp : word, 0 <= bv_unsigned sp < 2^64.
Proof. try hcb. try hsb. intros sp. pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. lia. Qed.

Theorem malloc_sr_at : forall entry stack,
  (forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv,
     RHEAP s LB m -> rauxv_ok m B -> bv_unsigned sp <= B ->
     stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - stack ->
     rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = Z_to_bv 64 RATP -> a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
     implM usegs (raw_malloc n) s (rmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 entry) fc None m (seg_rom usegs))) ->
  HeapSR_iface.malloc_sr_stmt_at HS entry stack.
Proof. try hcb. try hsb.
  intros entry stack SPEC. unfold HeapSR_iface.malloc_sr_stmt_at. cbn [HeapSR_iface.hs_SR HeapSR_iface.hs_KREL HeapSR_iface.hs_MPRES HeapSR_iface.hs_RHEAP HeapSR_iface.hs_rauxv_ok HeapSR_iface.hs_alloc_ok HS].
  intros until mo. intros HR KMs AOK AUX HB ST CLO LO ERR MI TP A0 N.
  pose proof KMs as (L & CR & K & B0).
  pose proof (SPEC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv HR AUX HB ST CLO LO ERR MI TP A0 ltac:(lia)) as IM.
  pose proof (raw_malloc_spec [] (Gvm mo) n (Gvm_frame mo) ltac:(lia)) as MSP.
  assert (PRE : OWN [] (Gvm mo) s mo /\ MBUD (ps_m s) n).
  { split; [| exact (MBUD_of_bounds P2 s LB m n HR AOK)]. split; [exists L; splits; auto; intros c []|]. split; [constructor| apply vm_only_refl]. }
  eapply sreach_mono; [apply (bridge _ _ _ _ _ _ _ IM MSP PRE (kb_halt _ _ _ K) (kb_minv _ _ _ K) (tforall_raw_malloc n s))|].
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

(* [comment removed for export] *)
Definition malloc_sr_post_off (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (n lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
  fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (A : Z) junk (p : bptr) (s' : PState),
    cfg_ms c = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ KM s' (cfg_model c) /\ vm_only mo (cfg_model c)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' B
    /\ rheap_pres LB (bv_unsigned sp) m m'
    /\ rblock_range A n /\ RHEAP s' ((p, A, n) :: LB) m'
    /\ rw_cells usegs m' A [CB (Z.to_nat n) junk]
    /\ (exists o, 0 <= o <= 255 /\ A = conc (ps_m s') (fst p) + UNIT * o)
    /\ (forall g i, s_slots (ps_m s') !! (fst p) = Some (g, i) -> m_sizeclass (get_meta_rec (ps_m s') g) < 48 ->
          m_sizeclass (get_meta_rec (ps_m s') g) <= size_to_class n + 1).

Theorem malloc_sr_at_off : forall entry stack,
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
    sreach usegs (malloc_sr_post_off ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m mo)
       (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 entry) fc None m (seg_rom usegs)) mo).
Proof. try hcb. try hsb.
  intros entry stack SPEC.
  intros until mo. intros HR KMs AOK AUX HB ST CLO LO ERR MI TP A0 N. unfold HeapSR_iface.RMMAP_THRESHOLD in N.
  pose proof KMs as (L & CR & K & B0).
  pose proof (SPEC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv HR AUX HB ST CLO LO ERR MI TP A0 ltac:(lia)) as IM.
  pose proof (raw_malloc_spec [] (Gvm mo) n (Gvm_frame mo) ltac:(lia)) as MSP.
  assert (PRE : OWN [] (Gvm mo) s mo /\ MBUD (ps_m s) n).
  { split; [| exact (MBUD_of_bounds P2 s LB m n HR AOK)]. split; [exists L; splits; auto; intros c []|]. split; [constructor| apply vm_only_refl]. }
  eapply sreach_mono; [apply (bridge _ _ _ _ _ _ _ IM MSP PRE (kb_halt _ _ _ K) (kb_minv _ _ _ K) (tforall_raw_malloc n s))|].
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

Theorem malloc_sr : HeapSR_iface.malloc_sr_stmt HS.
Proof. try hcb. try hsb.
  apply malloc_sr_at. intros. eapply rmalloc_spec; eauto.
Qed.

Theorem free_sr_at : forall entry,
  (forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv,
     RHEAP s LB m -> In (p, A, n) LB -> rauxv_ok m B -> bv_unsigned sp <= B ->
     stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
     rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = Z_to_bv 64 RATP -> a0 = Z_to_bv 64 A ->
     implM usegs (raw_free p) s (rfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 entry) fc None m (seg_rom usegs))) ->
  HeapSR_iface.free_sr_stmt_at HS entry.
Proof. try hcb. try hsb.
  intros entry SPEC. unfold HeapSR_iface.free_sr_stmt_at. cbn [HeapSR_iface.hs_SR HeapSR_iface.hs_KREL HeapSR_iface.hs_MPRES HeapSR_iface.hs_RHEAP HeapSR_iface.hs_rauxv_ok HeapSR_iface.hs_lb_remove HS].
  intros until mo. intros HR KMs HIN AUX HB ST CLO LO ERR MI TP A0.
  pose proof KMs as (L & CR & K & B0).
  pose proof (SPEC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv HR HIN AUX HB ST CLO LO ERR MI TP A0) as IM.
  pose proof (raw_free_spec [] (Gvm mo) p (Gvm_frame mo)) as MSP.
  assert (PRE : OWN [p] (Gvm mo) s mo).
  { split; [exists L; splits; auto|].
    - intros c [<-|[]]. exact (rheap_block_live s LB m L (p, A, n) HR HIN (hreach_creach _ _ CR)).
    - split; [| apply vm_only_refl]. cbn. constructor; [intros []| constructor]. }
  eapply sreach_mono; [apply (bridge _ _ _ _ _ _ _ IM MSP PRE (kb_halt _ _ _ K) (kb_minv _ _ _ K) (tforall_raw_free p s))|].
  intros cf (r & s' & HQ & HK & HH' & MI'). cbn in HK.
  destruct HK as ((L' & CR' & K' & _ & B') & _ & VO).
  unfold rfree_post in HQ.
  destruct HQ as (u0 & u1 & u2 & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m' & Ems & MI2 & ST2 & ERR2 & AUX2 & PRES & _ & _ & HR2).
  unfold HeapSR_iface.free_sr_post.
  exists u0, u1, u2, w0, w1, w2, w3, w4, w5, w6, w7, u3, u4, u5, u6, m', s'.
  splits; auto.
  exists L'. splits; auto.
Qed.

Theorem free_sr : HeapSR_iface.free_sr_stmt HS.
Proof. try hcb. try hsb.
  apply free_sr_at. intros. eapply rfree_spec_proof; eauto.
Qed.

Theorem KREL_laws_proof : HeapSR_iface.KREL_laws HS.
Proof. try hcb. try hsb. intros s mo. apply KM_halted_lazy. Qed.

Theorem MPRES_laws_proof : HeapSR_iface.MPRES_laws HS.
Proof. try hcb. try hsb. split; [apply vm_only_refl| apply vm_only_trans]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rmalloc_stmt_mirror : RMalloc_iface_stmt.rmalloc_stmt RHEAP rauxv_ok raddr_exposed.
Proof. try hcb. try hsb.
  unfold RMalloc_iface_stmt.rmalloc_stmt. intros. eapply implM_mono; [eapply rmalloc_spec; eassumption|].
  intros r s' ms' HQ. unfold rmalloc_post in HQ. unfold RMalloc_iface_stmt.rmalloc_post.
  destruct HQ as (u0 & u1 & u2 & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m' & errv' & E & MI2 & ST2 & ERR2 & AUX2 & PRES & F1 & F2 & RR).
  exists u0, u1, u2, w0, w1, w2, w3, w4, w5, w6, w7, u3, u4, u5, u6, m', errv'. repeat (split; [assumption|]).
  destruct r as [p|]; [| exact RR]. destruct RR as (A & junk & HA & RNG & HR & CH & EX & _). exists A, junk. auto 6.
Qed.
Lemma rfree_stmt_mirror : RMalloc_iface_stmt.rfree_stmt RHEAP rauxv_ok lb_remove.
Proof. try hcb. try hsb. exact rfree_spec_proof. Qed.
Lemma RHEAP_frame_mirror : RMalloc_iface_stmt.RHEAP_frame_stmt RHEAP. Proof. try hcb. try hsb. exact RHEAP_frame_proof. Qed.
Lemma rauxv_frame_mirror : RMalloc_iface_stmt.rauxv_ok_frame_stmt rauxv_ok. Proof. try hcb. try hsb. exact rauxv_ok_frame. Qed.
Lemma RHEAP_block_range_mirror : RMalloc_iface_stmt.RHEAP_block_range_stmt RHEAP. Proof. try hcb. try hsb. exact RHEAP_block_range_proof. Qed.

(* [comment removed for export] *)

Theorem free_null_sr : HeapSR_iface.free_null_sr_stmt HS.
Proof. try hcb. try hsb.
  unfold HeapSR_iface.free_null_sr_stmt, HeapSR_iface.free_null_sr_stmt_at. cbn [HeapSR_iface.hs_SR HS]. intros until mo. intros HH HL.
  unfold HeapSR_iface.free_null_post.
  eapply sreach_mono; [eapply (cj_evt_sreach usegs _ _ mo HH HL); apply (RMalloc_iface_stmt.rfree_null_spec); reflexivity|].
  intros c [H1 H2]. split; [exact H1| exact H2].
Qed.

End WithPhase2.

End HCW.

