(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Agent Require MallocKit_A2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Agent Require Import F_syscalls_u5 F_mm_syscalls_u5 MallocRep_u5 F_malloc_free_u5 MallocTree_u5 MallocFacts_B_u5 MallocFacts_Bpres_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Agent Require Import MallocKit_B_u5 MallocModel_B_u5 MallocKit_B2_u5 MallocKit_B3_u5 F_ntf_B_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Agent Require Import F_am_A_u5 F_am_K_u5 F_am_K2_u5 F_am_C_u5 F_am_D_u5 F_am_E_u5 F_am_F_u5 F_am_G_u5 F_am_H_u5 F_am_P_u5.
Import ListNotations.
Open Scope Z_scope.

Module A2 := MallocKit_A2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition magree (C : Z -> Prop) (m m' : mem) : Prop := forall a, 0 <= a < 2^64 -> ~ C a -> m' (wa a) = m (wa a).

Lemma magree_refl C m : magree C m m. Proof. intros a _ _; reflexivity. Qed.
Lemma magree_trans (C1 C2 C3 : Z -> Prop) m1 m2 m3 :
  magree C1 m1 m2 -> magree C2 m2 m3 -> (forall a, C1 a -> C3 a) -> (forall a, C2 a -> C3 a) -> magree C3 m1 m3.
Proof. intros A B I1 I2 a Ha Hc. rewrite (B a Ha) by (intros X; apply Hc, I2, X). apply A; [exact Ha|]. intros X; apply Hc, I1, X. Qed.
Lemma magree_of_pres C m m' : pres_except C m m' -> magree C m m'.
Proof. intros P a Ha Hc. exact (proj1 (P a Ha Hc)). Qed.
Lemma pres_of_magree C m m' : magree C m m' -> pres_except C m m'.
Proof. intros A a Ha Hc. split; [exact (A a Ha Hc)|]. rewrite (wview_ext m m' (wa a) (A a Ha Hc)). auto. Qed.
Lemma magree_of_munch C W m m' : munch W m m' -> ivs_covered C W -> magree C m m'.
Proof.
  intros MU COV a Ha Hc. apply MU. rewrite wa_unsigned by lia.
  revert COV Hc. clear. induction W as [|[lo hi] W IH]; cbn; intros COV Hc; [exact I|].
  destruct COV as [C1 COV]. split; [| apply IH; assumption]. intros Hin. apply Hc. apply C1. exact Hin.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_magree C m m' A cs :
  rw_cells asegs m A cs -> magree C m m' -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> ~ C a) -> rw_cells asegs m' A cs.
Proof.
  intros H AG HC. pose proof (rw_cells_bound _ _ _ _ H). eapply A2.rw_cells_agree; [exact H|]. intros a Ha. apply AG; [lia| apply HC; exact Ha].
Qed.
Lemma bytes_at_magree C m m' A bs :
  bytes_at asegs m A bs -> magree C m m' -> (forall a, A <= a < A + Z.of_nat (length bs) -> ~ C a) -> bytes_at asegs m' A bs.
Proof.
  intros H AG HC. pose proof (bytes_at_bound _ _ _ _ H). eapply A2.bytes_at_agree; [exact H|]. intros a Ha. apply AG; [lia| apply HC; exact Ha].
Qed.
Lemma wr_at_magree C m m' A n :
  wr_at asegs m A n -> magree C m m' -> (forall a, A <= a < A + n -> ~ C a) -> 0 <= A -> A + n <= 2^64 -> wr_at asegs m' A n.
Proof. intros H AG HC H0 H1. eapply A2.wr_at_agree; [exact H|]. intros a Ha. apply AG; [lia| apply HC; exact Ha]. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Section ASM.
Variables (R : Type) (k : mstate -> optr -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word).
(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis TK : ticks_ok st.
Hypothesis BL : brk_link_ps st s.
(* [comment removed for export] *)
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - AM_STACK.
Hypothesis ERR : rw_cells asegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv asegs m.
Hypothesis GP : gp = Z_to_bv 64 0x1a948.
Hypothesis TP : tp = Z_to_bv 64 0x1a768.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ETP : errno_addr tp = 0x1a768 - 164.
Proof. rewrite TP, unsigned_lit by lia. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma brk_am_took X q c : c_brk (ctx (am_took X q c)) = c_brk (ctx X). Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma am_take_took {RR} (Xst : mstate) (pp : aptr) (kk : mstate -> optr -> Malloc.M RR) (bl : Malloc.M RR) :
  am_take (upd_ctx (fun c => set_avail_meta (Some (aadd pp AREA_HDR)) (set_avail_meta_count NSLOTS c)) Xst) kk bl
  = kk (am_took Xst (aadd pp AREA_HDR) 100) (Some (aadd pp AREA_HDR)).
Proof. reflexivity. Qed.
Lemma conc_am_took X q c y : conc (am_took X q c) y = conc X y. Proof. reflexivity. Qed.
Lemma brk_carve stY p : c_brk (ctx (carve_st stY p)) = c_brk (ctx stY).
Proof.
  unfold carve_st. cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail].
  destruct (c_meta_area_tail (s_ctx stY)); reflexivity.
Qed.
Lemma conc_carve stY p y : conc (carve_st stY p) y = conc stY y.
Proof. unfold conc, get_region. rewrite carve_st_regions. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma live_ranges_same stA stB : s_regions stB = s_regions stA -> s_reserved stB = s_reserved stA -> live_ranges stB = live_ranges stA.
Proof. intros E1 E2. unfold live_ranges. rewrite E1, E2. reflexivity. Qed.

Lemma fresh_of_ranges_free stY x L a :
  s_regions stY = s_regions st -> s_reserved stY = s_reserved st ->
  ranges_free (live_ranges stY) x L = true -> x + L <= alloc_ceiling -> x <= a < x + L -> fresh_addr st a.
Proof.
  intros E1 E2 RF XC Ha. split; [lia|]. rewrite (live_ranges_same st stY E1 E2) in RF.
  eapply ranges_free_sub; [exact RF| lia| lia| lia].
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End ASM.
End CEIL_WRAP_1.

(* [comment removed for export] *)
