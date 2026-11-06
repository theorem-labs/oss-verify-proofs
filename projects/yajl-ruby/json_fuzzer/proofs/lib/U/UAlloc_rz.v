(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree ITreeCfg Nodes NodesCfg NodesMat Decode Exec.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import ImplRz ImplRzCfg SuccBridge.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Monad RawAlloc MSafe MSil KLink MSuccIface MSuccTall MSuccRaw.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks MallocHINV MallocKown.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import LB_Raw.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import Malloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UMallocRep UMallocTree UMalloc_iface UMalloc_ifaceP UF_malloc_spec UF_free_spec UF_realloc UF_realloc_spec UF_realloc_big.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Realloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocRealloc MallocSuccR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition GTrue : PState -> Model -> Prop := fun _ _ => True.

Lemma frame_ok_GTrue : frame_ok GTrue.
Proof. intros s s' mo mo' _ _ _ _. exact I. Qed.

(* [comment removed for export] *)
Definition sigb (b : block) : bptr * Z := (blk_id b, blk_size b).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lb_remove_cons : forall p b LB,
  lb_remove p (b :: LB) = if bptr_eqb (blk_id b) p then lb_remove p LB else b :: lb_remove p LB.
Proof.
  intros p b LB. unfold lb_remove. rewrite filter_cons.
  destruct (bptr_eqb (blk_id b) p); case_decide; cbn in *; try reflexivity; try contradiction.
Qed.

Lemma bptr_eqb_refl' : forall p, bptr_eqb p p = true.
Proof. intros [a o]. unfold bptr_eqb. cbn. rewrite aptr_eqb_refl, Z.eqb_refl. reflexivity. Qed.

Lemma bptr_eqb_true : forall p q, bptr_eqb p q = true -> p = q.
Proof.
  intros [a o] [a' o'] H. unfold bptr_eqb in H. cbn in H. apply andb_prop in H as [H1 H2].
  apply aptr_eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.

Lemma lb_remove_notin' : forall p LB, ~ In p (map blk_id LB) -> lb_remove p LB = LB.
Proof.
  intros p LB. induction LB as [|b LB IH]; intros Hn; [reflexivity|].
  rewrite lb_remove_cons. destruct (bptr_eqb (blk_id b) p) eqn:E.
  - exfalso. apply Hn. left. apply bptr_eqb_true in E. exact E.
  - f_equal. apply IH. intros Hi. apply Hn. right. exact Hi.
Qed.

Lemma perm_lb_remove : forall LB (p : bptr) A n,
  List.NoDup (map blk_id LB) -> In (p, A, n) LB -> Permutation LB ((p, A, n) :: lb_remove p LB).
Proof.
  induction LB as [|b LB IH]; intros p A n ND Hin; [destruct Hin|].
  cbn [map] in ND. inversion ND as [|x l Hni ND']; subst.
  destruct Hin as [->|Hin].
  - rewrite lb_remove_cons. cbn [blk_id fst snd]. rewrite bptr_eqb_refl'.
    rewrite lb_remove_notin' by exact Hni. apply Permutation_refl.
  - rewrite lb_remove_cons. destruct (bptr_eqb (blk_id b) p) eqn:E.
    + exfalso. apply Hni. apply bptr_eqb_true in E. rewrite E.
      change p with (blk_id (p, A, n)). apply in_map. exact Hin.
    + eapply Permutation_trans; [apply perm_skip; apply (IH p A n ND' Hin)|]. apply perm_swap.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section G.
Variable G : PState -> Model -> Prop.

Definition RHKG (s : PState) (LB : list block) (m : mem) (mo : Model) : Prop :=
  RHEAP s LB m /\ KOWN G s mo /\ HEADc (map sigb LB) s mo.

Lemma RHKG_G : forall s LB m mo, RHKG s LB m mo -> G s mo.
Proof. intros s LB m mo (_ & HO & _). exact (KOWN_G _ _ _ HO). Qed.

Lemma RHKG_silent : forall s LB m mo, RHKG s LB m mo -> m_halted mo = None /\ m_vm_lazy mo = [].
Proof.
  intros s LB m mo (_ & HO & _). destruct (KOWN_minv _ _ _ HO) as [Hmi Hh]. split; [exact Hh|].
  exact (minv_lazy _ Hmi).
Qed.

Lemma RHKG_minv : forall s LB m mo, RHKG s LB m mo -> minv mo /\ m_halted mo = None.
Proof. intros s LB m mo (_ & HO & _). exact (KOWN_minv _ _ _ HO). Qed.

Lemma RHKG_run : forall s LB m mo, RHKG s LB m mo -> minv mo /\ m_halted mo = None /\ m_vm_lazy mo = [].
Proof.
  intros s LB m mo H. destruct (RHKG_minv _ _ _ _ H) as [Hmi Hh]. split; [exact Hmi|]. split; [exact Hh|].
  exact (minv_lazy _ Hmi).
Qed.

Lemma RHKG_perm : forall s LB LB' m mo, RHKG s LB m mo -> Permutation LB LB' -> RHKG s LB' m mo.
Proof.
  intros s LB LB' m mo (HR & HO & HH) HP. split; [eapply RHEAP_perm; eauto|]. split; [exact HO|].
  eapply HEADc_perm; [apply Permutation_map; exact HP| exact HH].
Qed.

Lemma RHKG_frame : forall s LB m m' mo W,
  RHKG s LB m mo -> munch W m m' -> wmono usegs m m' -> Forall (rclient_write_ok LB) W -> RHKG s LB m' mo.
Proof. intros s LB m m' mo W (HR & HO & HH) MU WM FW. split; [eapply RHEAP_frame_proof; eauto| split; [exact HO| exact HH]]. Qed.

Lemma RHKG_blocks : forall s LB m mo, RHKG s LB m mo ->
    (forall b, In b LB -> rblock_range (blk_addr b) (blk_size b))
    /\ (forall b1 b2, In b1 LB -> In b2 LB -> blk_id b1 <> blk_id b2 ->
          blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1)
    /\ List.NoDup (map blk_id LB).
Proof.
  intros s LB m mo (HR & _ & _). split; [|split].
  - intros b Hb. eapply RHEAP_block_range_proof; eauto.
  - intros b1 b2 H1 H2 Hne. eapply RHEAP_blocks_disjoint_proof; eauto.
  - eapply RHEAP_blocks_nodup_proof; eauto.
Qed.

(* [comment removed for export] *)
Lemma RHKG_so : forall s LB m mo v, RHKG s LB m mo -> G (set_so_ps v s) mo -> RHKG (set_so_ps v s) LB m mo.
Proof.
  intros s LB m mo v (HR & HO & HH) HG. split; [| split].
  - eapply RHEAP_ext; [exact HR | |]; destruct s; reflexivity.
  - eapply KOWN_other; [exact HO | | | exact HG]; destruct s; reflexivity.
  - eapply HEADc_other; [exact HH | |]; destruct s; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma KL_vm_same : forall L pbrk mo mo',
  KL L pbrk mo -> minv mo' -> m_halted mo' = None -> m_vmmaps mo' = m_vmmaps mo ->
  (m_vm_materialized mo = [] -> m_vm_materialized mo' = []) -> KL L pbrk mo'.
Proof.
  intros L pbrk mo mo' H Hmi Hh E HM. destruct H. constructor; rewrite ?E; auto.
Qed.

Lemma RHKG_mo : forall s LB m mo n rsp mo' evs,
  RHKG s LB m mo -> lazy_free_node n -> nstep n mo rsp mo' evs -> m_vmmaps mo' = m_vmmaps mo ->
  G s mo' -> RHKG s LB m mo'.
Proof.
  intros s LB m mo n rsp mo' evs (HR & [(L & HS & HKL) _] & HH) LF Hst VM HG. split; [exact HR|].
  destruct (minv_preserved n mo rsp mo' evs LF (kl_minv _ _ _ HKL) (kl_halt _ _ _ HKL) Hst) as [Hh' Hmi'].
  split.
  - split; [| exact HG]. exists L. split; [exact HS|]. eapply KL_vm_same; eauto. exact (nstep_mat_shape _ _ _ _ _ Hst).
  - eapply HEADc_after_node; [exact HH | reflexivity | reflexivity | exact LF | exact Hst | exact VM].
Qed.

Lemma RHKG_ssp : forall s LB m mo, RHKG s LB m mo ->
    rw_cells usegs m RGOT_SSP [C8 (Z_to_bv 64 RSSP_GUARD)] /\ rw_cells usegs m RSSP_GUARD [C8 rc_guard].
Proof.
  intros s LB m mo ((st & LB0 & _ & _ & MREP & _) & _). destruct MREP as (_ & _ & (_ & _ & _ & G1 & G2) & _).
  split; [exact G1 | exact G2].
Qed.

(* [comment removed for export] *)
Lemma RHKG_need_locks : forall s LB m mo, RHKG s LB m mo -> rw_cells usegs m RNEED_LOCKS [C1 (b8 0)].
Proof.
  intros s LB m mo ((st & LB0 & _ & _ & MREP & _) & _). destruct MREP as (_ & _ & (_ & NL & _) & _). exact NL.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Hypothesis FG : frame_ok G.

Local Notation realizesC := (realizes_cfg acfg usegs).

(* [comment removed for export] *)
Theorem rmalloc_rz :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (n lo B : Z) (errv : word) (K : TSet),
  K [] ->
  RHKG s LB m mo ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = wz RATP ->
  a0 = wz n -> 0 <= n <= NUSERc -> Z.of_nat (length LB) < NHELDc ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState) (errv' : word) (p : bptr) (A : Z),
     mem_inv usegs m' -> stk usegs m' lo (bv_unsigned sp) -> rw_cells usegs m' (errno_addr tp) [C4 errv'] ->
     rauxv_ok m' B -> rheap_pres LB (bv_unsigned sp) m m' ->
     a0' = wz A -> rblock_range A n -> RHKG s' ((p, A, n) :: LB) m' mo' ->
     (exists junk, rw_cells usegs m' A [CB (Z.to_nat n) junk]) ->
     realizesC (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom usegs)) mo') K) ->
  realizesC (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RMALLOC_SYM) fc None m (seg_rom usegs)) mo) K.
Proof.
  intros until K. intros HK0 (HR & HO & HH) AUX HB ST LO1 LO2 ERR MI TP A0 N NL CONT.
  pose proof (rmalloc_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m s LB n lo B errv HR AUX HB ST LO1 LO2 ERR MI TP A0 ltac:(unfold NUSERc in N; lia)) as IM.
  pose proof (raw_malloc_tsil G n s mo FG ltac:(lia) HO) as TS.
  pose proof (malloc_succ (map sigb LB) n s mo HH ltac:(rewrite length_map; lia) N) as SC.
  pose proof (tsil_cfg_pack _ mo _ _ TS SC) as TS'.
  destruct (KOWN_minv _ _ _ HO) as [Hmi Hh].
  unfold implM in IM.
  eapply (impl_tsil_realizes_cfg acfg node usegs (at_node usegs) (nstep_cfg acfg) nexit minv nsafe (nodes_sound_cfg acfg usegs)
            _ _ _ mo _ K IM TS' Hh Hmi HK0).
  intros [|[r s']] ms' mo' HQ HP Hh' Hmi'; cbn in HQ, HP; [destruct HP|].
  destruct HP as [[HO' Hn'] [q [Eq HH']]]. cbn [fst snd] in Eq, HH'. subst r.
  destruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' &
                  -> & MI' & ST' & ERR' & AUX' & PRES & _ & _ & HRr).
  destruct HRr as (A & junk & Ha0 & RG & HR' & RW & _).
  apply (CONT t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' mo' s' errv' q A MI' ST' ERR' AUX' PRES Ha0 RG).
  - split; [exact HR'|]. split; [exact HO'|]. exact HH'.
  - exists junk. exact RW.
Qed.

(* [comment removed for export] *)
Theorem rfree_rz :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word) (K : TSet),
  K [] ->
  RHKG s LB m mo -> In (p, A, n) LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = wz RATP ->
  a0 = wz A ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState),
     mem_inv usegs m' -> stk usegs m' lo (bv_unsigned sp) -> rw_cells usegs m' (errno_addr tp) [C4 errv] ->
     rauxv_ok m' B -> rheap_pres (lb_remove p LB) (bv_unsigned sp) m m' ->
     RHKG s' (lb_remove p LB) m' mo' ->
     realizesC (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom usegs)) mo') K) ->
  realizesC (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RFREE_SYM) fc None m (seg_rom usegs)) mo) K.
Proof.
  intros until K. intros HK0 (HR & HO & HH) IN AUX HB ST LO1 LO2 ERR MI TP A0 CONT.
  pose proof (rfree_spec_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m s LB p A n lo B errv HR IN AUX HB ST LO1 LO2 ERR MI TP A0) as IM.
  pose proof (RHEAP_blocks_nodup_proof _ _ _ HR) as ND.
  destruct HR as (st & LB0 & HP & Hst & MR & HI).
  assert (IN0 : In (p, A, n) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact IN]).
  pose proof (raw_free_tsil G ref_reserved st LB0 (p, A, n) p s mo FG HO Hst HI IN0 eq_refl) as TS.
  assert (HH1 : HEADc ((p, n) :: map sigb (lb_remove p LB)) s mo).
  { change ((p, n) :: map sigb (lb_remove p LB)) with (map sigb ((p, A, n) :: lb_remove p LB)).
    eapply HEADc_perm; [apply Permutation_map; apply (perm_lb_remove LB p A n ND IN)| exact HH]. }
  pose proof (free_ctall (map sigb (lb_remove p LB)) p n s mo HH1) as SC.
  pose proof (tsil_cfg_pack _ mo _ _ TS SC) as TS'.
  destruct (KOWN_minv _ _ _ HO) as [Hmi Hh].
  unfold implM in IM.
  eapply (impl_tsil_realizes_cfg acfg node usegs (at_node usegs) (nstep_cfg acfg) nexit minv nsafe (nodes_sound_cfg acfg usegs)
            _ _ _ mo _ K IM TS' Hh Hmi HK0).
  intros [|[r s']] ms' mo' HQ HP' Hh' Hmi'; cbn in HQ, HP'; [destruct HP'|].
  destruct HP' as [HO' HH']. cbn [fst snd] in HH'.
  destruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  -> & MI' & ST' & ERR' & AUX' & PRES & _ & _ & HR').
  apply (CONT t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' mo' s' MI' ST' ERR' AUX' PRES).
  split; [exact HR'| split; [exact HO'| exact HH']].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem rrealloc_null_rz :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (n lo B : Z) (errv : word) (K : TSet),
  K [] ->
  RHKG s LB m mo ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RREALLOC_STACK_MIN ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = wz RATP ->
  a0 = wz 0 -> a1 = wz n -> 0 <= n <= NUSERc -> Z.of_nat (length LB) < NHELDc ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState) (errv' : word) (p : bptr) (A : Z),
     mem_inv usegs m' -> stk usegs m' lo (bv_unsigned sp) -> rw_cells usegs m' (errno_addr tp) [C4 errv'] ->
     rauxv_ok m' B -> rheap_pres LB (bv_unsigned sp) m m' ->
     a0' = wz A -> rblock_range A n -> RHKG s' ((p, A, n) :: LB) m' mo' ->
     (exists junk, rw_cells usegs m' A [CB (Z.to_nat n) junk]) ->
     realizesC (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom usegs)) mo') K) ->
  realizesC (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RREALLOC_SYM) fc None m (seg_rom usegs)) mo) K.
Proof.
  intros until K. intros HK0 (HR & HO & HH) AUX HB ST LO1 LO2 ERR MI TP A0 A1 N NL CONT.
  pose proof (rrealloc_null_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m s LB n lo B errv HR AUX HB ST LO1 LO2 ERR MI TP A0 A1 ltac:(unfold NUSERc in N; lia)) as IM.
  pose proof (raw_malloc_tsil G n s mo FG ltac:(lia) HO) as TS.
  pose proof (malloc_succ (map sigb LB) n s mo HH ltac:(rewrite length_map; lia) N) as SC.
  pose proof (tsil_cfg_pack _ mo _ _ TS SC) as TS'.
  destruct (KOWN_minv _ _ _ HO) as [Hmi Hh].
  unfold implM in IM.
  eapply (impl_tsil_realizes_cfg acfg node usegs (at_node usegs) (nstep_cfg acfg) nexit minv nsafe (nodes_sound_cfg acfg usegs)
            _ _ _ mo _ K IM TS' Hh Hmi HK0).
  intros [|[r s']] ms' mo' HQ HP Hh' Hmi'; cbn in HQ, HP; [destruct HP|].
  destruct HP as [[HO' Hn'] [q [Eq HH']]]. cbn [fst snd] in Eq, HH'. subst r.
  destruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' &
                  -> & MI' & ST' & ERR' & AUX' & PRES & _ & _ & HRr).
  destruct HRr as (A & junk & Ha0 & RG & HR' & RW).
  apply (CONT t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' mo' s' errv' q A MI' ST' ERR' AUX' PRES Ha0 RG).
  - split; [exact HR'|]. split; [exact HO'|]. exact HH'.
  - exists junk. exact RW.
Qed.

(* [comment removed for export] *)
Lemma map_sigb_xs : forall L : list block, map xs (map sigb L) = map sig L.
Proof. induction L as [|b L IH]; [reflexivity|]. cbn [map]. rewrite IH. reflexivity. Qed.

Theorem rrealloc_rz_of : rrealloc_stmt ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (p : bptr) (A sz n lo B : Z) (old : list byte) (errv : word) (K : TSet),
  K [] ->
  RHKG s LB m mo -> In (p, A, sz) LB -> bytes_at usegs m A old -> Z.of_nat (length old) = sz ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RREALLOC_STACK_MIN ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = wz RATP ->
  a0 = wz A -> a1 = wz n -> 0 <= n <= NUSERc -> Z.of_nat (length LB) < NHELDc ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState) (errv' : word) (p' : bptr) (A' : Z),
     mem_inv usegs m' -> stk usegs m' lo (bv_unsigned sp) -> rw_cells usegs m' (errno_addr tp) [C4 errv'] ->
     rauxv_ok m' B ->
     a0' = wz A' -> rblock_range A' n -> RHKG s' ((p', A', n) :: lb_remove p LB) m' mo' ->
     rheap_pres (lb_remove p LB) (bv_unsigned sp) m m' ->
     (exists junk, rw_cells usegs m' A' [CB (Z.to_nat (Z.min n sz)) (firstn (Z.to_nat (Z.min n sz)) old);
                                      CB (Z.to_nat (n - Z.min n sz)) junk]) ->
     realizesC (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom usegs)) mo') K) ->
  realizesC (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RREALLOC_SYM) fc None m (seg_rom usegs)) mo) K.
Proof.
  intros RS. intros until K. intros HK0 (HR & HO & HH) IN BY LEN AUX HB ST LO1 LO2 ERR MI TP A0 A1 N NL CONT.
  pose proof (RHEAP_blocks_nodup_proof _ _ _ HR) as ND.
  destruct HR as (st & LB0 & HP & Hst & MR & HI).
  assert (IN0 : In (p, A, sz) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact IN]).
  destruct (rheap_live_aptr st s LB0 (p, A, sz) HI IN0) as (pf & Hpf1 & Hpf2). cbn in Hpf2.
  pose proof (RS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m s LB st LB0 (p, A, sz) pf n lo B old errv HP Hst MR HI IN Hpf1 Hpf2 BY LEN AUX HB ST LO1 LO2 ERR MI TP
                A0 A1 ltac:(unfold NUSERc in N; lia)) as IM.
  pose proof (realloc_tsil G ref_reserved st LB0 (p, A, sz) pf n m s mo FG HO Hst HI IN0 Hpf1 Hpf2 ltac:(lia)) as TS.
  (* [comment removed for export] *)
  pose proof (perm_lb_remove LB p A sz ND IN) as PLB.
  assert (HH1 : HEADc ((p, sz) :: map sigb (lb_remove p LB)) s mo).
  { change ((p, sz) :: map sigb (lb_remove p LB)) with (map sigb ((p, A, sz) :: lb_remove p LB)).
    eapply HEADc_perm; [apply Permutation_map; exact PLB| exact HH]. }
  assert (HX : Permutation (map xs ((p, blk_size (p, A, sz)) :: map sigb (lb_remove p LB))) (map sig LB0)).
  { cbn [blk_size snd]. change ((p, sz) :: map sigb (lb_remove p LB)) with (map sigb ((p, A, sz) :: lb_remove p LB)).
    rewrite map_sigb_xs. apply Permutation_map. eapply Permutation_trans; [apply Permutation_sym; exact PLB| apply Permutation_sym; exact HP]. }
  assert (HL : Z.of_nat (length (map sigb (lb_remove p LB))) + 2 <= NHELDc).
  { rewrite length_map. pose proof (Permutation_length PLB) as E. cbn [length] in E. lia. }
  pose proof (realloc_succB G ref_reserved st LB0 (p, A, sz) p (map sigb (lb_remove p LB)) pf n m s mo
                FG HO Hst HI IN0 Hpf1 Hpf2 eq_refl HX HH1 HL N) as SC.
  pose proof (tsil_cfg_pack _ mo _ _ TS SC) as TS'.
  destruct (KOWN_minv _ _ _ HO) as [Hmi Hh].
  unfold implM in IM.
  eapply (impl_tsil_realizes_cfg acfg node usegs (at_node usegs) (nstep_cfg acfg) nexit minv nsafe (nodes_sound_cfg acfg usegs)
            _ _ _ mo _ K IM TS' Hh Hmi HK0).
  intros [|[[st' q] s']] ms' mo' HQ HP' Hh' Hmi'; cbn in HQ, HP'; [destruct HP'|].
  destruct HP' as [(HO' & Epm & _ & _) (q0 & Eq & HB' & _ & _)]. cbn [fst snd] in Eq, HB', Epm. subst q.
  destruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' &
                  -> & MI' & ST' & ERR' & AUX' & _ & _ & HRr).
  cbn [blk_id blk_size fst snd] in HRr.
  destruct HRr as (p' & A' & junk & Ha0 & EA & RG & HR' & PRES & RW).
  apply (CONT t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' mo' s' errv' p' A' MI' ST' ERR' AUX' Ha0 RG).
  - split; [exact HR'|]. split; [exact HO'|].
    destruct HR' as (st2 & LB2 & HP2 & Hst2 & _ & HI2).
    change (map sigb ((p', A', n) :: lb_remove p LB)) with ((blk_id (p', A', n), n) :: map sigb (lb_remove p LB)).
    apply (HB' ref_reserved st2 LB2 (p', A', n)).
    + rewrite Hst2. exact Epm.
    + exact (proj2 HI2).
    + eapply Permutation_in; [apply Permutation_sym; exact HP2| left; reflexivity].
    + cbn [blk_addr fst snd]. exact EA.
  - exact PRES.
  - exists junk. exact RW.
Qed.

(* [comment removed for export] *)
Definition rrealloc_rz := rrealloc_rz_of rrealloc_spec.


End G.

(* [comment removed for export] *)
Lemma RHKG_weak : forall (G G' : PState -> Model -> Prop) s LB m mo,
  RHKG G s LB m mo -> (G s mo -> G' s mo) -> RHKG G' s LB m mo.
Proof. intros G G' s LB m mo (HR & HO & HH) HGG. split; [exact HR|]. split; [eapply KOWN_weakG; eauto| exact HH]. Qed.

(* [comment removed for export] *)
Definition RHK : PState -> list block -> mem -> Model -> Prop := RHKG GTrue.

End RC__1.
