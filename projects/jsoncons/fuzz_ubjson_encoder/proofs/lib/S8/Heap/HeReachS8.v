(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Spec Require Import KInvS8 MI_InvS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import MI_Kit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Spec Require Import MI_ListS8 MI_ExtS8 MI_SimS8 MI_ContractsS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Lib Require Import DecodeS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Bridge Require Import BrResS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Heap Require Import HeTreeS8 HeAbsS8 HeEmptyS8 HeWNtfS8 HeMetaS8 HeWFreeS8 HeWSlotS8 HeWGrpS8 HeWMallocS8 HeResS8 HeStepS8.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HMREACH.
Context {RUNp : RunP}.

Theorem reach_init resv K : 0 <= K ->
  RES (strip (minit secret_val resv)) [] K /\ Phi (strip (minit secret_val resv)) = 0 /\ Psi (strip (minit secret_val resv)) = 0.
Proof.
  intros HK. split; [exact (RES_init secret_val resv K HK)|].
  unfold Phi, Psi, ngreg, nareas, brk_dead_w. cbn [s_regions s_areas s_ctx strip minit c_brk ctx0]. rewrite !map_to_list_empty, map_size_empty. cbn. lia.
Qed.

Theorem reach_malloc cs L n L' cs' p c k SZ K :
  creach cs L -> 0 <= n -> RES cs SZ K -> Permutation (map fst SZ) (ld_live L) ->
  cpathw ecost L (cmalloc cs n) L' (cs', Some p) c k -> Z.of_nat (length (ld_live L)) + 1 <= K ->
  creach cs' (set_live (p :: ld_live L') L') /\ ld_live L' = ld_live L
  /\ RES cs' ((p, n) :: SZ) K /\ c <= Phi cs' - Phi cs /\ Z.of_nat k <= Psi cs' - Psi cs /\ ~ In p (ld_live L).
Proof.
  intros CR Hn R SZP CPW HK.
  pose proof (cpathw_cpath_inv _ _ _ _ _ _ _ CPW) as CP.
  assert (CR' : creach cs' (set_live (p :: ld_live L') L')) by exact (creach_malloc cs L n L' cs' (Some p) CR Hn CP).
  pose proof (cpath_live CP) as EL.
  destruct (creach_sim cs L CR) as (st & BL & LS & Est & INV & LIVE).
  pose proof (INVC_strip x0 st L BL LS INV) as INVC0. rewrite Est in INVC0.
  destruct (creach_sim _ _ CR') as (st' & BL' & LS' & Est' & INV' & LIVE'). cbn [ld_live set_live] in LIVE'.
  pose proof (INVC_strip x0 st' _ BL' LS' INV') as INVC1. rewrite Est' in INVC1.
  pose proof (apw_cpathw ecost _ _ _ _ _ _ CPW 0 0%nat _ (cmalloc_walk cs L BL LS n INVC0 (rs_marith _ _ _ R) Hn)) as MQ.
  rewrite Z.add_0_l, Nat.add_0_l in MQ.
  assert (SZP' : Permutation (map fst SZ) (map bslot BL)) by (rewrite <- LIVE; exact SZP).
  assert (EBL : map bslot BL' = p :: map bslot BL) by (rewrite <- LIVE', EL, LIVE; reflexivity).
  assert (HK' : Z.of_nat (length BL') <= K).
  { pose proof (f_equal (@length _) EBL) as LEN. rewrite !length_map in LEN. cbn [length] in LEN. rewrite length_map in LEN.
    rewrite LIVE in HK. rewrite length_map in HK. lia. }
  destruct (RES_malloc cs L BL LS n c k cs' p _ BL' LS' SZ K INVC0 R SZP' MQ INVC1 EBL HK') as (R' & HC & HN & _ & _).
  split; [exact CR'|]. split; [exact EL|]. split; [exact R'|]. split; [exact HC|]. split; [exact HN|].

  pose proof (cmalloc_contract_proof cs L n CR Hn) as CT.
  assert (FR : forall t Lx (P : mled -> mstate * option cptr -> Prop) Ly r, ctree_ok Lx t P -> cpath Lx t Ly r -> P Ly r).
  { clear. intros t. induction t as [r0|e kk IH]; intros Lx P Ly r CTk CPk.
    - inversion CPk; subst. exact CTk.
    - inversion CPk; subst. cbn [ctree_ok] in CTk. destruct CTk as [_ Hk]. eapply IH; [apply Hk; eassumption| eassumption]. }
  pose proof (FR _ _ _ _ _ CT CP) as NI. cbn [snd] in NI. rewrite <- EL. exact NI.
Qed.

Theorem reach_free cs L c0 L' cs' u k SZ SZ' K n0 :
  creach cs L -> In (c0, n0) SZ -> RES cs SZ K -> Permutation (map fst SZ) (ld_live L) ->
  cpathw unmap_len L (cfree cs (Some c0)) L' cs' u k -> (forall e, In e SZ' -> In e SZ) ->
  creach cs' (set_live (ap_remove c0 (ld_live L')) L') /\ ld_live L' = ld_live L
  /\ RES cs' SZ' K /\ Phi cs' = Phi cs - u /\ Psi cs' = Psi cs - Z.of_nat k.
Proof.
  intros CR Hin R SZP CPW SUB.
  pose proof (cpathw_cpath_inv _ _ _ _ _ _ _ CPW) as CP.
  assert (Hc : In c0 (ld_live L)) by (apply (Permutation_in _ SZP); apply in_map_iff; exists (c0, n0); auto).
  assert (CR' : creach cs' (set_live (ap_remove c0 (ld_live L')) L')) by exact (creach_free cs L c0 L' cs' CR Hc CP).
  pose proof (cpath_live CP) as EL.
  destruct (creach_sim cs L CR) as (st & BL & LS & Est & INV & LIVE).
  pose proof (INVC_strip x0 st L BL LS INV) as INVC0. rewrite Est in INVC0.
  destruct (creach_sim _ _ CR') as (st' & BL' & LS' & Est' & INV' & LIVE').
  pose proof (INVC_strip x0 st' _ BL' LS' INV') as INVC1. rewrite Est' in INVC1.
  rewrite LIVE in Hc. destruct (In_bslot _ _ Hc) as (off & n1 & Hk).
  pose proof (apw_cpathw unmap_len _ _ _ _ _ _ CPW 0 0%nat _ (cfree_walk cs L BL LS c0 off n1 INVC0 (rs_einv _ _ _ R) Hk)) as FR.
  rewrite Z.add_0_l, Nat.add_0_l in FR.
  destruct (RES_free cs L BL LS cs' u k _ BL' LS' SZ SZ' K INVC0 R FR INVC1 SUB) as (R' & PH & PS & _).
  split; [exact CR'|]. split; [exact EL|]. split; [exact R'|]. split; [exact PH| exact PS].
Qed.

Theorem reach_bounds cs L SZ K :
  creach cs L -> RES cs SZ K -> Permutation (map fst SZ) (ld_live L) ->
  Phi cs <= zsum (map (fun e => csz (snd e)) SZ) + 32 * 2 ^ 20 + PGSZ * (6 * NAMAX K + 8)
  /\ Psi cs <= Z.of_nat (length SZ) + 32 + 4 * NAMAX K
  /\ pot cs <= NSLOTS * (2 + 2 * NAMAX K)
  /\ 0 <= nareas cs <= NAMAX K.
Proof.
  intros CR R SZP. destruct (creach_sim cs L CR) as (st & BL & LS & Est & INV & LIVE).
  pose proof (INVC_strip x0 st L BL LS INV) as INVC0. rewrite Est in INVC0.
  assert (SZP' : Permutation (map fst SZ) (map bslot BL)) by (rewrite <- LIVE; exact SZP).
  pose proof (nareas_K cs L BL LS SZ K INVC0 R) as NA.
  pose proof (Phi_bound cs L BL LS SZ INVC0 (rs_einv _ _ _ R) (rs_l63 _ _ _ R) SZP' (rs_marith _ _ _ R)) as PH.
  pose proof (Psi_bound cs L BL LS SZ INVC0 (rs_einv _ _ _ R) (rs_l63 _ _ _ R) SZP') as PS.
  pose proof (pot_bound cs L BL LS INVC0 (rs_marith _ _ _ R)) as PT.
  assert (LEN : length BL = length SZ).
  { pose proof (Permutation_length SZP') as E. rewrite !length_map in E. lia. }
  assert (NA0 : 0 <= nareas cs) by (unfold nareas; lia).
  unfold PGSZ, NSLOTS in *. rewrite LEN in PS. split; [nia| split; [lia| split; [nia| lia]]].
Qed.

End HMREACH.
