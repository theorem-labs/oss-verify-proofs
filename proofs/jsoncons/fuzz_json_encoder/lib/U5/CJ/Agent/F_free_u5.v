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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Agent Require Import F_syscalls_u5 MallocRep_u5 F_malloc_free_u5 F_malloc_enframe_u5 F_mm_syscalls_u5 MallocTree_u5 MallocBlocks_u5 MallocHINV_u5 MallocFacts_B_u5 MallocFacts_B_reach_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Agent Require Import MallocKit_B_u5 MallocKit_B2_u5 MallocModel_B_u5 MallocKit_B3_u5 MallocFacts_Bpres_u5 F_ntf_u5 F_free_A_u5 F_free_B_u5 F_free_C_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Agent Require Import F_free_K_u5.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition DROPPED (st st' : mstate) (a : Z) : Prop :=
  exists rid r, (s_regions st) !! rid = Some r /\ (s_regions st') !! rid = None /\ r_kind r = RKGroup
                /\ r_base r <= a < r_base r + round_up_pg (r_len r).

(* [comment removed for export] *)
Definition lbrm (LB : list block) (blk : block) : list block :=
  filter (fun b' => negb (aptr_eqb (blk_slot b') (blk_slot blk))) LB.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma oracle_ok_refl m st : oracle_ok m m st.
Proof. intros rid r q h _ _ _ _ _. reflexivity. Qed.

Lemma oracle_ok_hdr_st o m st pf : ticks_ok st -> oracle_ok o m st -> oracle_ok o m (hdr_st st pf).
Proof.
  intros TK OK rid r q h Hr Hk Hq M8 Hc. change (s_regions (hdr_st st pf)) with (s_regions st) in Hr.
  rewrite hdr_st_cell_read in Hc by exact TK.
  destruct (N.eqb rid (fst pf) && ((q =? snd pf - 1) || (q =? snd pf - 2) || (q =? snd pf - 3)))%bool; [discriminate|].
  exact (OK rid r q h Hr Hk Hq M8 Hc).
Qed.
(* [comment removed for export] *)

Lemma munmap_ok_range_val a : match a with RgErr e => 1 <= e <= 4095 | _ => True end -> munmap_answer_ok (range_val a) = true.
Proof.
  destruct a as [e|c]; cbn [range_val]; intros He; unfold munmap_answer_ok, is_errno_form, neg_errno, TWO64.
  - apply orb_true_intro. right. apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
  - reflexivity.
Qed.

Lemma round_up_pg_mod x : round_up_pg x mod 4096 = 0.
Proof. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096. Z.div_mod_to_equations. lia. Qed.

Lemma mmap_len_round x : mmap_len (round_up_pg x) = round_up_pg x.
Proof.
  pose proof (round_up_pg_mod x) as M. unfold mmap_len, page_round_up_Z, page_size.
  set (y := round_up_pg x) in *. Z.div_mod_to_equations. nia.
Qed.
End CEIL_WRAP_1.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac cover_intervals tac :=
  let lo0 := fresh "ilo" in let hi0 := fresh "ihi" in let HW := fresh "HinW" in let y := fresh "y" in let Hy := fresh "Hy" in
  intros lo0 hi0 HW y Hy; cbn [In] in HW;
  repeat (destruct HW as [HW|HW]); try contradiction;
  injection HW; intros; subst lo0 hi0; tac y Hy.
Section CEIL_WRAP_2.
Context {RUNp : RunP}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma NoDup_map_inj_in {A B} (f : A -> B) (l : list A) :
  List.NoDup (map f l) -> forall x y, In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|a l IH]; intros ND x y Hx Hy E; [destruct Hx|].
  cbn [map] in ND. inversion ND; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | | apply IH; assumption].
  - exfalso. apply H1. rewrite E. apply in_map. exact Hy.
  - exfalso. apply H1. rewrite <- E. apply in_map. exact Hx.
Qed.

Lemma filter_ext_in {A} (P1 P2 : A -> Prop) `{forall x, Decision (P1 x)} `{forall x, Decision (P2 x)} (l : list A) :
  (forall x, In x l -> (P1 x <-> P2 x)) -> filter P1 l = filter P2 l.
Proof.
  induction l as [|a l IH]; intros HE; [reflexivity|]. rewrite !filter_cons.
  rewrite IH by (intros x Hx; apply HE; right; exact Hx).
  destruct (decide (P1 a)) as [Y|N]; destruct (decide (P2 a)) as [Y'|N']; try reflexivity; exfalso;
    pose proof (HE a (or_introl eq_refl)); tauto.
Qed.
End CEIL_WRAP_2.

