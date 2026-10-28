(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Prog LibProg ProgG BnTree.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApLogic.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit R_cache_defs R_prim_defs R_sec_defs D_defs D_cs I_lkit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct RtCallA W_cryptoA UnwindA EdgesA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import RtGenStmtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApErrKitA2 W_akit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Import ListNotations.
Open Scope Z_scope.

Definition RA_CR_REALLOC : Z := 0x1fd2bc.          (* [comment removed for export] *)
Definition CRYPTO_REALLOC2_STACK : Z := 48 + RT_STACK.
Definition CRYPTO_REALLOC_ARRAY_A : Z := 0x2025f4.
Definition CRYPTO_REALLOC_ARRAY_STACK_A : Z := CRYPTO_REALLOC2_STACK.   (* [comment removed for export] *)

Local Notation E_rea_leaf := (E_CRYPTO_realloc_1fc65c : uk_leaf 0x1fd224 0x1fd2bc).                 (* [comment removed for export] *)
Local Notation E_reaa_tail := (E_CRYPTO_realloc_array_1f8a90 : uk_tail 0x2025f4 0x1fd224).         (* [comment removed for export] *)

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
(* [comment removed for export] *)
Hypothesis REA : realloc_contract_gen RT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma AH_realloc : forall Σ Σ' OW LB m m' p A n0 p' A' n SP,
  AHEAP Σ OW LB m -> In (p, A, n0) OW -> ART RT Σ' m' ->
  rt_live RT Σ' = (A', n) :: live_remove A (rt_live RT Σ) -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
  A' mod 16 = 0 -> 0 < n -> gsz p' = n -> ~ In p' (map blk_id (OW ++ LB)) ->      (* [comment removed for export] *)
  rt_pres (live_remove A (rt_live RT Σ)) (rt_frames RT Σ) SP m m' ->
  AHEAP Σ' ((p', A', n) :: lb_remove p OW) LB m'.
Proof.
  intros Σ Σ' OW LB m m' p A n0 p' A' n SP H Hin HA' HL' HFr' HS' A16 Hn Hg Hp' PRES.
  pose proof (AH_nodup _ _ _ _ H) as ND.
  assert (HinL : In (p, A, n0) (OW ++ LB)) by (apply in_or_app; left; exact Hin).
  assert (U1 : forall b, In b (OW ++ LB) -> blk_addr b = A -> blk_id b = p).
  { intros b Hb EA. destruct (decide (blk_id b = p)) as [E|NE]; [exact E|]. exfalso.
    pose proof (AH_disjoint_gen _ _ _ _ b (p, A, n0) H Hb HinL NE) as D.
    pose proof (AH_pos_gen _ _ _ _ b H Hb) as P1. pose proof (AH_pos_gen _ _ _ _ _ H HinL) as P2. cbn in D, P2. lia. }
  assert (U2 : forall b, In b (OW ++ LB) -> blk_id b = p -> blk_addr b = A).
  { intros b Hb E. destruct b as [[q Ax] nx]. cbn in E. subst q.
    destruct (AH_addr_unique (OW ++ LB) p Ax nx A n0 ND Hb HinL) as [-> _]. reflexivity. }
  destruct H as (HA & HS & HFr & SPL & _ & HF1 & HF2).
  rewrite HFr in PRES. pose proof (fr_agree_of_rt_pres _ _ _ _ PRES) as AG.
  split; [exact HA'|]. split; [rewrite HS'; exact HS|]. split; [rewrite HFr'; exact HFr|].
  split. { destruct (heap_split_agree _ _ _ _ _ SPL AG) as (FW & PB & LBr & P1 & P2 & F & AP). split; [exact FW|]. exists PB, LBr.
           assert (SUB : forall b, In b (OW ++ LBr) -> In b (OW ++ LB)).
           { intros b Hb. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb | right].
             eapply Permutation_in; [symmetry; exact P1|]. apply in_or_app. right. exact Hb. }
           assert (NDr : List.NoDup (map blk_id (OW ++ LBr))).
           { assert (PX : Permutation (OW ++ LB) (PB ++ (OW ++ LBr))).
             { eapply Permutation_trans; [apply Permutation_app_head; exact P1|]. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. }
             pose proof (nodup_ids_perm _ _ PX ND) as X. rewrite map_app in X. apply NoDup_app_remove_l in X. exact X. }
           split; [exact P1|]. split; [| split; [exact F | exact AP]].
           rewrite HL'. change (map blk_an (((p', A', n) :: lb_remove p OW) ++ LBr)) with ((A', n) :: map blk_an (lb_remove p OW ++ LBr)). apply perm_skip.
           eapply Permutation_trans; [apply live_remove_perm; exact P2|].
           rewrite (live_remove_map p A (OW ++ LBr) (fun b Hb => U1 b (SUB b Hb)) (fun b Hb => U2 b (SUB b Hb))), BnHeapA.lb_remove_app_l; [reflexivity | exact NDr |].
           apply in_map_iff. exists (p, A, n0). split; [reflexivity | exact Hin]. }
  split. { change (map blk_id (((p', A', n) :: lb_remove p OW) ++ LB)) with (p' :: map blk_id (lb_remove p OW ++ LB)). constructor.
           - intros Hi. apply Hp'. rewrite map_app in Hi |- *. apply in_app_or in Hi. apply in_or_app. destruct Hi as [Hi|Hi]; [left| right; exact Hi].
             apply in_map_iff in Hi as (b' & E & Hb'). apply in_map_iff. exists b'. split; [exact E | eapply BnHeapA.lb_remove_incl; exact Hb'].
           - rewrite <- (BnHeapA.lb_remove_app_l p OW LB ND) by (apply in_map_iff; exists (p, A, n0); split; [reflexivity | exact Hin]).
             clear - ND. induction (OW ++ LB) as [|b L IH]; [constructor|]. rewrite BnHeapA.lb_remove_cons. cbn [map] in ND. apply NoDup_cons_iff in ND as [N1 N2].
             destruct (bptr_eqb (blk_id b) p); [exact (IH N2)|]. cbn [map]. constructor; [|exact (IH N2)].
             intros Hi. apply N1. apply in_map_iff in Hi as (b' & E & Hb'). apply in_map_iff. exists b'. split; [exact E | eapply BnHeapA.lb_remove_incl; exact Hb']. }
  split; [| exact HF2]. constructor; [split; [exact A16| split; [exact Hn| exact Hg]]|].
  apply Forall_forall. intros b Hb. apply BnHeapA.lb_remove_incl in Hb. exact (proj1 (Forall_forall _ _) HF1 b Hb).
Qed.

(* [comment removed for export] *)
Lemma AH_aclient_remove : forall Σ OW LB m p A n0 SP a,
  AHEAP Σ OW LB m -> In (p, A, n0) OW -> aclient_addr (lb_remove p OW ++ LB) SP a -> aclient (live_remove A (rt_live RT Σ)) FR SP a.
Proof.
  intros Σ OW LB m p A n0 SP a H Hin [Ha|[Ha|(b & Hb & Hr)]]; [left; exact Ha | right; left; exact Ha |].
  pose proof (AH_nodup _ _ _ _ H) as ND.
  assert (HinL : In (p, A, n0) (OW ++ LB)) by (apply in_or_app; left; exact Hin).
  assert (HbL : In b (OW ++ LB)) by (apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; eapply BnHeapA.lb_remove_incl; exact Hb| right; exact Hb]).
  assert (NE : blk_id b <> p).
  { apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (proj2 (proj1 (BnHeapA.lb_remove_In _ _ _) Hb))|].
    destruct b as [[q Ab] nb]. cbn. exact (ids_disj OW LB p A n0 ND Hin _ Hb). }
  assert (NA : blk_addr b <> A).
  { intros EA. apply NE. pose proof (AH_disjoint_gen _ _ _ _ b (p, A, n0) H HbL HinL NE) as D.
    pose proof (AH_pos_gen _ _ _ _ b H HbL) as P1. pose proof (AH_pos_gen _ _ _ _ _ H HinL) as P2. cbn in D, P2. exfalso. lia. }
  destruct (AH_cases _ _ _ _ b H HbL) as [HL|(PI & _)].
  - right; right; left. exists (blk_addr b), (blk_size b). split; [| exact Hr].
    revert HL. generalize (rt_live RT Σ) as l. induction l as [|e l IH]; [intros []|].
    intros [->|Hl]; rewrite live_remove_cons; [| destruct (fst e =? A); [exact (IH Hl)| right; exact (IH Hl)]].
    cbn [fst]. destruct (Z.eqb_spec (blk_addr b) A); [contradiction| left; reflexivity].
  - right; right; right; left. exact (pb_in_fframe b a PI Hr).
Qed.

(* [comment removed for export] *)
Lemma live_remove_len : forall Σ OW LB m p A n, AHEAP Σ OW LB m -> In (p, A, n) OW ->
  S (length (live_remove A (rt_live RT Σ))) = length (rt_live RT Σ).
Proof.
  intros Σ OW LB m p A n H Hin.
  pose proof (AH_nodup _ _ _ _ H) as ND. pose proof (AH_nodup_l _ _ _ _ H) as NDl.
  assert (HinL : In (p, A, n) (OW ++ LB)) by (apply in_or_app; left; exact Hin).
  assert (U1 : forall b, In b (OW ++ LB) -> blk_addr b = A -> blk_id b = p).
  { intros b Hb EA. destruct (decide (blk_id b = p)) as [E|NE]; [exact E|]. exfalso.
    pose proof (AH_disjoint_gen _ _ _ _ b (p, A, n) H Hb HinL NE) as DJ.
    pose proof (AH_pos_gen _ _ _ _ b H Hb) as P1. pose proof (AH_pos_gen _ _ _ _ _ H HinL) as P2. cbn in DJ, P2. lia. }
  assert (U2 : forall b, In b (OW ++ LB) -> blk_id b = p -> blk_addr b = A).
  { intros b Hb E. destruct b as [[q A'] n']. cbn in E. subst q.
    destruct (AH_addr_unique (OW ++ LB) p A' n' A n ND Hb HinL) as [-> _]. reflexivity. }
  destruct H as (HA & HS & HFr & (FW & PB & LBr & P1 & P2 & F & AP) & _ & HF1 & HF2).
  assert (SUB : forall b, In b (OW ++ LBr) -> In b (OW ++ LB)).
  { intros b Hb. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb | right].
    eapply Permutation_in; [symmetry; exact P1|]. apply in_or_app. right. exact Hb. }
  assert (NDr : List.NoDup (map blk_id (OW ++ LBr))).
  { assert (PX : Permutation (OW ++ LB) (PB ++ (OW ++ LBr))).
    { eapply Permutation_trans; [apply Permutation_app_head; exact P1|]. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. }
    pose proof (nodup_ids_perm _ _ PX ND) as X. rewrite map_app in X. apply NoDup_app_remove_l in X. exact X. }
  assert (INP : In p (map blk_id OW)) by (apply in_map_iff; exists (p, A, n); split; [reflexivity | exact Hin]).
  rewrite (Permutation_length (live_remove_perm A _ _ P2)), (Permutation_length P2).
  rewrite (live_remove_map p A (OW ++ LBr) (fun b Hb => U1 b (SUB b Hb)) (fun b Hb => U2 b (SUB b Hb))), (BnHeapA.lb_remove_app_l _ _ _ NDr INP).
  rewrite !length_map, !length_app, <- (lb_remove_length p OW NDl INP). lia.
Qed.

(* [comment removed for export] *)
Lemma AH_remove_perm : forall Σ OW LB m p A n, AHEAP Σ OW LB m -> In (p, A, n) OW ->
  Permutation (rt_live RT Σ) ((A, n) :: live_remove A (rt_live RT Σ)).
Proof.
  intros Σ OW LB m p A n H Hin.
  pose proof (AH_nodup _ _ _ _ H) as ND. pose proof (AH_nodup_l _ _ _ _ H) as NDl.
  assert (HinL : In (p, A, n) (OW ++ LB)) by (apply in_or_app; left; exact Hin).
  assert (U1 : forall b, In b (OW ++ LB) -> blk_addr b = A -> blk_id b = p).
  { intros b Hb EA. destruct (decide (blk_id b = p)) as [E|NE]; [exact E|]. exfalso.
    pose proof (AH_disjoint_gen _ _ _ _ b (p, A, n) H Hb HinL NE) as DJ.
    pose proof (AH_pos_gen _ _ _ _ b H Hb) as P1. pose proof (AH_pos_gen _ _ _ _ _ H HinL) as P2. cbn in DJ, P2. lia. }
  assert (U2 : forall b, In b (OW ++ LB) -> blk_id b = p -> blk_addr b = A).
  { intros b Hb E. destruct b as [[q A'] n']. cbn in E. subst q.
    destruct (AH_addr_unique (OW ++ LB) p A' n' A n ND Hb HinL) as [-> _]. reflexivity. }
  destruct H as (HA & HS & HFr & (FW & PB & LBr & P1 & P2 & F & AP) & _ & HF1 & HF2).
  assert (SUB : forall b, In b (OW ++ LBr) -> In b (OW ++ LB)).
  { intros b Hb. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb | right].
    eapply Permutation_in; [symmetry; exact P1|]. apply in_or_app. right. exact Hb. }
  assert (NDr : List.NoDup (map blk_id (OW ++ LBr))).
  { assert (PX : Permutation (OW ++ LB) (PB ++ (OW ++ LBr))).
    { eapply Permutation_trans; [apply Permutation_app_head; exact P1|]. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. }
    pose proof (nodup_ids_perm _ _ PX ND) as X. rewrite map_app in X. apply NoDup_app_remove_l in X. exact X. }
  assert (INP : In p (map blk_id OW)) by (apply in_map_iff; exists (p, A, n); split; [reflexivity | exact Hin]).
  assert (POW : Permutation OW ((p, A, n) :: lb_remove p OW)).
  { clear - NDl Hin. induction OW as [|b OW IH]; [destruct Hin|]. rewrite BnHeapA.lb_remove_cons. cbn [map] in NDl. apply NoDup_cons_iff in NDl as [N1 N2].
    destruct Hin as [->|Hin].
    - cbn [blk_id fst]. rewrite bptr_eqb_refl. rewrite (BnHeapA.lb_remove_notin p OW N1). apply Permutation_refl.
    - assert (NE : bptr_eqb (blk_id b) p = false).
      { apply bptr_eqb_neq. intros E. apply N1. rewrite E. apply in_map_iff. exists (p, A, n). split; [reflexivity| exact Hin]. }
      rewrite NE. eapply Permutation_trans; [apply perm_skip; exact (IH Hin N2)|]. apply perm_swap. }
  eapply Permutation_trans; [exact P2|].
  eapply Permutation_trans; [| apply perm_skip; apply live_remove_perm; symmetry; exact P2].
  rewrite (live_remove_map p A _ (fun b Hb => U1 b (SUB b Hb)) (fun b Hb => U2 b (SUB b Hb))), (BnHeapA.lb_remove_app_l _ _ _ NDr INP).
  rewrite !map_app. change ((A, n) :: map blk_an (lb_remove p OW) ++ map blk_an LBr) with (map blk_an ((p, A, n) :: lb_remove p OW) ++ map blk_an LBr).
  apply Permutation_app_tail. apply Permutation_map. exact POW.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rea_R (Σ : rts RT) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (A n0 n lo : Z) (m : mem) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms => exists q m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q) m' ms
    /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (live_remove A (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) m m'
    /\ wr_at ctasegs m' q n /\ acc ctasegs m' q n
    /\ (forall old, bytes_at ctasegs m A old -> Z.of_nat (length old) = Z.min n0 n -> bytes_at ctasegs m' q old)
    /\ rt_live RT Σ' = (q, n) :: live_remove A (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
    /\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < q /\ q mod 16 = 0 /\ q + n < USTACK_TOP.

Lemma realloc_post_RL : forall Σ OW LB m0 p ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 A n0 n lo m c,
  AHEAP Σ OW LB m0 -> In (p, A, n0) OW ->
  realloc_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 A n0 n lo m c ->
  exists Σ', ASTA RT Σ' PMc (rea_R Σ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 A n0 n lo m Σ') c
             /\ exists a b, Permutation ((a, gsz p) :: rt_live RT Σ') ((b, n) :: rt_live RT Σ).      (* [comment removed for export] *)
Proof.
  intros until c. intros HEAP IN (Σ' & q & HA & P1 & P2 & P3 & P4 & P5 & P6 & P7). exists Σ'.
  split.
  - eapply ASTA_conseq; [exact HA|]. intros ms (m' & H1 & H2 & H3 & H4 & H5 & H6). exists q, m'. auto 16.
  - exists A, q. rewrite (AH_gsz _ _ _ _ _ _ _ HEAP IN), P1.
    eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. symmetry. exact (AH_remove_perm _ _ _ _ _ _ _ HEAP IN).
Qed.

(* [comment removed for export] *)
Definition realloc_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (p : bptr) (A n0 n lo : Z) (m : mem) (p' : bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' A',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz A') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ agree_on (aclient_addr (lb_remove p OW ++ LB) (bv_unsigned sp)) m m'
    /\ rt_credit RT Σ - mcost n <= rt_credit RT Σ'
    /\ ablock_range A' n /\ AHEAP Σ' ((p', A', n) :: lb_remove p OW) LB m' /\ acc ctasegs m' A' n
    /\ (exists junk, rw_cells ctasegs m' A' [CB (Z.to_nat n) junk])
    /\ (forall old, bytes_at ctasegs m A old -> Z.of_nat (length old) = Z.min n0 n -> bytes_at ctasegs m' A' old).
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition RA_SAVE (sp : word) (ra s0 s1 s2 s3 : word) (j0 : list byte) (m0 : mem) : Prop :=
  rw_cells ctasegs m0 (bv_unsigned sp - 48) [CB 8 j0; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Lemma rea_proA : forall {X} (t : aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (A n lo : Z) (ras : list Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - CRYPTO_REALLOC2_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> mem_inv ctasegs m -> tp = wz TP_A ->
  realloc_statics m -> a0 = wz A -> a1 = wz n -> 0 < A < 2^64 -> 1 <= n < 2^64 ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras ->
  (forall m0 j0 (x12 x14 : word), munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m0 -> wmono ctasegs m m0 -> mem_inv ctasegs m0 ->
     stk ctasegs m0 lo (bv_unsigned sp - 48) -> AHEAP Σ OW LB m0 -> RA_SAVE sp ra s0 s1 s2 s3 j0 m0 ->
     uw_chain USTACK_TOP m0 (bv_unsigned sp - 48) (bv_unsigned sp) (bv_unsigned ra :: ras) ->
     implAp t Σ Q (MS (mkR (wz RA_CR_REALLOC) (Z_to_bv 64 (bv_unsigned sp - 48)) gp (wz TP_A) t0 t1 t2 sp a3 (wz A) (wz n) x12 a3 x14 a5 a6 a7 a2 (wz n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (wz e_realloc) fc None m0 (seg_rom ctasegs))) ->
  implAp t Σ Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz CRYPTO_REALLOC) fc None m (seg_rom ctasegs)).
Proof.
  intros until ras. intros HEAP ST CEIL LO SPT SP16 MI -> RS -> -> HA Hn UW K.
  unfold CRYPTO_REALLOC2_STACK, RT_STACK, CRYPTO_REALLOC, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof RS as RS'. unfold realloc_statics, CR_REALLOC_IMPL, CRYPTO_REALLOC, MallocRep.wz in RS'.
  destruct (af_client_consts RT AF Σ m (AH_art _ _ _ _ HEAP)) as (_ & _ & _ & _ & RRO).
  assert (GR : ro_cells ctasegs m 0x5aa898 [C8 (Z_to_bv 64 0x1fd224)]).
  { apply (relro_ro_cells m _ _ RRO); try (vm_compute; reflexivity); try (cbn; repeat split); unfold RELRO_LO, RELRO_HI; cbn; lia. }
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  apply implAp_from_evt.
  carve_frame 48%nat ST.
  apply (rw_cells_split_CB ctasegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 10 step. do 4 step. step. if_true.
  step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
  step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
  step. step.
  name_mem m0.
  assert (HEAP0 : AHEAP Σ OW LB m0).
  { eapply (seg_heap Σ OW LB m m0 _ lo (bv_unsigned sp) HEAP MU WM); [| exact CEIL | unfold USTACK_TOP; lia]. constructor; [left; cbn; lia | constructor]. }
  apply evt_done. unfold RA_CR_REALLOC, e_realloc, TP_A, MallocRep.wz.
  replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) in * by lia.
  match goal with H : rw_cells ctasegs m0 (bv_unsigned sp - 48) [CB 8 _; _; _; _; _; _] |- _ => rename H into FRS end.
  eapply (K m0); [exact MU| exact WM| assumption| assumption| exact HEAP0| exact FRS|].
  replace (bv_unsigned sp - 48) with (bv_unsigned sp + - 48) in FRS |- * by lia.
  uw_call_mu_tac m 48 UW MU FRS; [intros a Ha; cbn [outside fst snd]; lia | lia | uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia | unfold USTACK_TOP in *; lia].
Qed.

(* [comment removed for export] *)
Lemma rea_epiA : forall {X} (t : aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop)
    (ra sp gp s0 s1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (m m0 : mem) (Σ Σ' : rts RT) (OW LB : list block) (p p' : bptr) (A n0 n lo : Z) (j0 : list byte) (ms' : machine_state),
  AHEAP Σ OW LB m -> AHEAP Σ OW LB m0 -> In (p, A, n0) OW -> ACEIL <= lo -> lo <= bv_unsigned sp - CRYPTO_REALLOC2_STACK -> bv_unsigned sp + 16 <= USTACK_TOP ->
  mem_inv ctasegs m0 -> munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m0 -> RA_SAVE sp ra s0 s1 s2 s3 j0 m0 -> 1 <= n -> bv_unsigned ra mod 2 = 0 ->
  rea_R Σ (wz RA_CR_REALLOC) (Z_to_bv 64 (bv_unsigned sp - 48)) gp (wz TP_A) sp a3 a2 (wz n) s4 s5 s6 s7 s8 s9 s10 s11 A n0 n lo m0 Σ' ms' ->
  ~ In p' (map blk_id (OW ++ LB)) -> gsz p' = n ->
  (forall ms'', realloc_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB p A n0 n lo m p' Σ' ms'' -> implAp t Σ' Q ms'') ->
  implAp t Σ' Q ms'.
Proof.
  intros until ms'. intros HEAP HEAP0 IN CEIL LO SPT MI0 MU FRS Hn RAEV HR Hp' Hg K.
  unfold CRYPTO_REALLOC2_STACK, RT_STACK, RA_CR_REALLOC, RA_SAVE, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  destruct HR as (q & m1 & RS & (ART1 & MI1 & ST1) & PRES & WR1 & ACC1 & OLD & LV1 & FR1 & SP1 & CR1 & Q0 & Q16 & QTOP).
  destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 48)) = bv_unsigned sp - 48) by (apply unsigned_lit; lia).
  rewrite ESP in ST1, PRES. rewrite (ret_pc_even 2085564) by (clear; lia).
  assert (EQq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; unfold USTACK_TOP in QTOP; lia).
  pose proof HEAP0 as (_ & HS0 & HF0 & _).
  assert (HEAP1 : AHEAP Σ' ((p', q, n) :: lb_remove p OW) LB m1).
  { eapply (AH_realloc Σ Σ' OW LB m0 m1 p A n0 p' q n _ HEAP0 IN ART1 LV1 FR1 SP1 Q16); [lia| exact Hg| exact Hp'| exact PRES]. }
  assert (AG1 : agree_on (aclient_addr (lb_remove p OW ++ LB) (bv_unsigned sp - 48)) m0 m1).
  { intros a Ha Hc. apply PRES. unfold wa. rewrite unsigned_lit by lia. rewrite HF0. exact (AH_aclient_remove _ _ _ _ p A n0 _ a HEAP0 IN Hc). }
  apply (rw_cells_agree _ _ _ _ _ AG1) in FRS; [| intros a Ha; left; cbn in Ha; unfold USTACK_TOP; lia].
  apply implAp_from_evt.
  step. if_cases KA; zify_cond KA; [exfalso; rewrite ?EQq in KA; lia|]. clear KA.
  step. do 6 step.
  release_frame FRS ST1 (bv_unsigned sp).
  step.
  replace (bv_unsigned sp - 48 + 48) with (bv_unsigned sp) by lia. rewrite (Z_to_bv_bv_unsigned sp).
  apply evt_done. apply K. unfold realloc_postA, MallocRep.wz.
  do 16 eexists. exists m1, q. split; [reflexivity|].
  split; [exact MI1|]. split; [exact ST1|].
  split.
  { eapply agree_on_trans.
    - eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|]. intros a [Ha|[Ha|Ha]]; cbn [outside]; (split; [|exact I]).
      + lia.
      + destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
        destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; unfold BnHeapA.ACEIL in *; lia.
      + destruct Ha as (b & Hb & Hr). assert (HbL : In b (OW ++ LB)) by (apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; eapply BnHeapA.lb_remove_incl; exact Hb| right; exact Hb]).
        pose proof (AH_range_gen _ _ _ _ b HEAP HbL) as (_ & _ & _ & BC & _). unfold BnHeapA.ACEIL in *. lia.
    - eapply agree_on_mono; [exact AG1|]. intros a [Ha|[Ha|Ha]]; [left; lia | right; left; exact Ha | right; right; exact Ha]. }
  split; [rewrite CR1; lia|].
  split; [exact (AH_range _ _ _ _ p' q n HEAP1 (or_introl eq_refl))|].
  split; [exact HEAP1|]. split; [exact ACC1|].
  split; [exact (wr_at_rw_CB m1 q n WR1 ltac:(lia))|].
  intros old HO HL. apply OLD; [| exact HL].
  pose proof (AH_range _ _ _ _ p A n0 HEAP IN) as (B0 & _ & _ & BC & _).
  eapply (bytes_at_agree _ m m0); [apply (agree_on_of_munch_nw _ _ _ MU)| exact HO|]. intros a Ha. cbn [outside]. split; [| exact I]. unfold BnHeapA.ACEIL in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma CRYPTO_realloc_walkAp : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (p : bptr) (A n0 n lo : Z) (ras : list Z)
    (k : option bptr -> aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m -> In (p, A, n0) OW ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - CRYPTO_REALLOC2_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> bv_unsigned ra mod 2 = 0 ->
  realloc_statics m -> a0 = wz A -> a1 = wz n -> 1 <= n <= 0x8000000 ->
  mcost n <= rt_credit RT Σ ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx CRYPTO_REALLOC (bv_unsigned ra :: ras) ->
  (forall p' Σ' ms', ~ In p' (map blk_id (OW ++ LB)) ->
     realloc_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB p A n0 n lo m p' Σ' ms' ->
     implAp (k (Some p')) Σ' Q ms') ->
  implAp (ARealloc p n k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz CRYPTO_REALLOC) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. intros HEAP IN ST CEIL LO SPT SP16 MI TP RAEV RS HA0 HA1 Hn CRED UW CTX K.
  pose proof (AH_range _ _ _ _ p A n0 HEAP IN) as (A0 & A16 & N0 & AC & AI). pose proof (AH_okA _ _ _ _ p A n0 HEAP IN) as [_ N0'].
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3).
  eapply (rea_proA (ARealloc p n k) Q) with (lo := lo) (ras := ras); [exact HEAP| exact ST| exact CEIL| exact LO| exact SPT| exact SP16| exact MI| exact TP| exact RS| exact HA0| exact HA1
    | clear - A0 AC C3 N0; unfold BnHeapA.ACEIL, STACK_WIN, USTACK_TOP in *; lia| clear - Hn; lia| exact UW|].
  intros m0 j0 x12 x14 MU WM MI0 ST0 HEAP0 FRS UW0.
  pose proof LO as LO'. unfold CRYPTO_REALLOC2_STACK, RT_STACK in LO'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 48)) = bv_unsigned sp - 48) by (apply unsigned_lit; clear - SPR LO' CEIL C1; unfold SEGTOP_A, BnHeapA.ACEIL in *; lia).
  eapply implAp_realloc with (avoid := map blk_id (OW ++ LB)).
  - intros Hn' HLIVE.
    eapply cps_conseq; [ eapply (REA Σ PMc) with (p := A) (n0 := n0) (n := n) (lo := lo); try reflexivity | intros c Hc; exact Hc
                       | intros c Hc; exact (realloc_post_RL Σ OW LB m0 p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A n0 n lo m0 c HEAP0 IN Hc) ].
    + exact ar_PMc_fdfs.
    + exact ar_PMc_ms.
    + exact (AH_live_ow _ _ _ _ (p, A, n0) HEAP0 IN).
    + exact Hn.
    + exact HLIVE.
    + exact CRED.
    + exact (AH_art _ _ _ _ HEAP0).
    + exact MI0.
    + eapply (call_okA Σ OW LB m0 lo); [exact HEAP0| exact ST0| exact CEIL| clear - LO'; unfold RT_STACK; lia| unfold USTACK_TOP in *; clear - SPT; lia| rewrite Zminus_mod, SP16; reflexivity].
    + eapply unwind_ch_intro with (ras := bv_unsigned ra :: ras); [unfold RA_CR_REALLOC; rewrite unsigned_lit by (clear; lia); exact (uk_ctx_leaf _ _ _ E_rea_leaf CTX)|].
      rewrite ESP. exact UW0.
  - intros p' Σ' ms' Hn' Hp' Hg HR.
    eapply (rea_epiA (k (Some p')) Q) with (lo := lo) (Σ := Σ) (OW := OW) (LB := LB) (m := m) (m0 := m0) (p := p) (A := A) (n0 := n0) (n := n) (sp := sp); [exact HEAP| exact HEAP0| exact IN| exact CEIL| exact LO| exact SPT| exact MI0| exact MU| exact FRS| clear - Hn; lia| exact RAEV
      | exact HR| exact Hp'| exact Hg| intros ms'' PO; exact (K p' Σ' ms'' Hp' PO)].
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma CRYPTO_realloc_array_walkAp : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (p : bptr) (A n0 num size lo : Z) (ras : list Z)
    (k : option bptr -> aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m -> In (p, A, n0) OW ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - CRYPTO_REALLOC_ARRAY_STACK_A ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> bv_unsigned ra mod 2 = 0 ->
  realloc_statics m -> a0 = wz A -> a1 = wz num -> a2 = wz size -> 0 < num -> 0 < size -> num * size <= 0x8000000 ->
  mcost (num * size) <= rt_credit RT Σ ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx CRYPTO_REALLOC_ARRAY_A (bv_unsigned ra :: ras) ->
  (forall p' Σ' ms', ~ In p' (map blk_id (OW ++ LB)) ->
     realloc_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB p A n0 (num * size) lo m p' Σ' ms' ->
     implAp (k (Some p')) Σ' Q ms') ->
  implAp (ARealloc p (num * size) k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz CRYPTO_REALLOC_ARRAY_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. intros HEAP IN ST CEIL LO SPT SP16 MI -> RAEV RS -> -> -> Hnum Hsize Hn CRED UW CTX K.
  unfold CRYPTO_REALLOC_ARRAY_A, MallocRep.wz. unfold CRYPTO_REALLOC_ARRAY_STACK_A, CRYPTO_REALLOC2_STACK, RT_STACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. unfold USTACK_TOP in SPT.
  pose proof (AH_range _ _ _ _ p A n0 HEAP IN) as (BA0 & BA16 & BN0 & BAC & BAI).
  assert (Hsz : num < 2^32 /\ size < 2^32) by nia.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  apply implAp_from_evt.
  (* [comment removed for export] *)
  carve_frame 32%nat ST. do 5 step. step. step. step. step.
  step. if_cases K0; zify_cond K0.
  2: { exfalso. apply K0. rewrite Z.shiftr_div_pow2, Z.div_small by nia. reflexivity. }
  clear K0.
  (* [comment removed for export] *)
  step. setreg 11%Z (Z_to_bv 64 (num * size)) ltac:(rewrite (unsigned_lit num), (unsigned_lit size) by lia; reflexivity).
  step. step. do 4 step. release_frame FR ST (bv_unsigned sp). step. step.
  name_mem m1.
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn; alia| constructor]. }
  assert (RS1 : realloc_statics m1).
  { unfold realloc_statics in *. eapply ro_cells_agree; [apply (agree_on_of_munch_nw _ _ _ MU1)| exact RS|].
    intros a Ha. cbn [outside]. unfold CR_REALLOC_IMPL in Ha. cbn in Ha. unfold BnHeapA.ACEIL in *. lia. }
  assert (UW1 : uw_chain USTACK_TOP m1 (bv_unsigned sp) (bv_unsigned s0) ras).
  { eapply uw_chain_munchP; [exact MU1| exact UW| intros a H1 Ha; cbn [outside fst snd]; lia]. }
  apply evt_done.
  eapply CRYPTO_realloc_walkAp with (A := A) (n0 := n0) (lo := lo) (ras := ras);
    [exact HEAP1| exact IN| exact ST| exact CEIL| unfold CRYPTO_REALLOC2_STACK, RT_STACK; lia| unfold USTACK_TOP; lia| exact SP16| exact MI| reflexivity| exact RAEV
    | exact RS1| reflexivity| reflexivity| lia| exact CRED| exact UW1| exact (uk_ctx_tail _ _ _ E_reaa_tail CTX)|].
  intros p' Σ' ms' Hp' PO. apply (K p' Σ' ms' Hp'). unfold realloc_postA in *.
  destruct PO as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & F' & fc' & m' & A' & -> & MI' & ST' & AG' & CR' & BR' & HEAP' & ACC' & HJ' & OLD').
  do 16 eexists. exists m', A'. split; [reflexivity|].
  split; [exact MI'|]. split; [exact ST'|].
  split.
  { eapply agree_on_trans; [| exact AG'].
    eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)|]. intros a [Ha|[Ha|Ha]]; cbn [outside]; (split; [|exact I]).
    - lia.
    - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; alia.
    - destruct Ha as (b & Hb & Hr). assert (HbL : In b (OW ++ LB)) by (apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; eapply BnHeapA.lb_remove_incl; exact Hb| right; exact Hb]).
      pose proof (AH_range_gen _ _ _ _ b HEAP HbL) as (_ & _ & _ & BC & _). unfold BnHeapA.ACEIL in *. lia. }
  split; [exact CR'|]. split; [exact BR'|]. split; [exact HEAP'|]. split; [exact ACC'|]. split; [exact HJ'|].
  intros old HO HL. apply OLD'; [| exact HL].
  eapply (bytes_at_agree _ m m1); [apply (agree_on_of_munch_nw _ _ _ MU1)| exact HO|]. intros a Ha. cbn [outside]. split; [| exact I]. unfold BnHeapA.ACEIL in *. lia.
Qed.

End WithRT.
