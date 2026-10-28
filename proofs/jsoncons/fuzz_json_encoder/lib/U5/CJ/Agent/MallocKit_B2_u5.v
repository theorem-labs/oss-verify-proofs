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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Agent Require Import F_syscalls_u5 MallocRep_u5 F_malloc_free_u5 F_malloc_enframe_u5 MallocTree_u5 MallocKit_B_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma implT_guard {R} o t (c : bool) (k bail : Malloc.M R) s Q ms :
  (c = true -> implT o k s Q ms) -> implT o (guard t c k bail) s Q ms.
Proof. intros H. unfold guard. destruct c; [apply H; reflexivity| apply implT_undef]. Qed.

Lemma peek_ok_pans o p c h : peek_answer_ok (pans_mem o p c h) = true.
Proof.
  pose proof (pans_mem_range o p c h). unfold peek_answer_ok.
  apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.

Lemma implT_rd8 {R} o st q (k : Z -> Malloc.M R) s Q ms :
  implT o (k (rdv pans_mem o st q)) s Q ms -> implT o (rd8 st q k) s Q ms.
Proof.
  intros H. unfold rd8. unfold rdv in H.
  destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h]; [exact H|].
  apply implT_peek. rewrite peek_ok_pans. exact H.
Qed.

Lemma implT_rd16 {R} o st q (k : Z -> Malloc.M R) s Q ms :
  implT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1))) s Q ms -> implT o (rd16 st q k) s Q ms.
Proof. intros H. unfold rd16. apply implT_rd8, implT_rd8. exact H. Qed.

Lemma implT_rd32 {R} o st q (k : Z -> Malloc.M R) s Q ms :
  implT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1)
             + 65536 * rdv pans_mem o st (aadd q 2) + 16777216 * rdv pans_mem o st (aadd q 3))) s Q ms ->
  implT o (rd32 st q k) s Q ms.
Proof. intros H. unfold rd32. apply implT_rd8, implT_rd8, implT_rd8, implT_rd8. exact H. Qed.

(* [comment removed for export] *)
Lemma implT_if {R} o (c : bool) (t1 t2 : Malloc.M R) s Q ms :
  (c = true -> implT o t1 s Q ms) -> (c = false -> implT o t2 s Q ms) -> implT o (if c then t1 else t2) s Q ms.
Proof. intros H1 H2. destruct c; auto. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wview_ext : forall m m' a, m' a = m a -> wview asegs m' a = wview asegs m a.
Proof. intros m m' a E. unfold wview. rewrite E. reflexivity. Qed.

Lemma wr_at_agree : forall m m' A n, wr_at asegs m A n -> agree_on m m' A n -> wr_at asegs m' A n.
Proof.
  intros m m' A n (H0 & H1 & HW) AG. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (wview_ext m m') by (apply AG; lia). apply HW. exact Hi.
Qed.

Lemma rw_cells_agree' : forall m m' A cs,
  rw_cells asegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells asegs m' A cs.
Proof.
  intros m m' A cs [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
  - eapply bytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
  - eapply wr_at_agree; eauto.
Qed.

Lemma u64arr_agree' : forall m m' A ws,
  u64arr asegs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> u64arr asegs m' A ws.
Proof.
  intros m m' A ws [HB HW] AG. split.
  - eapply bytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
  - eapply wr_at_agree; [exact HW|]. exact AG.
Qed.

Lemma u8arr_agree' : forall m m' A bs,
  u8arr asegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> u8arr asegs m' A bs.
Proof. intros m m' A bs [HB HW] AG. split; [eapply bytes_at_agree; eauto| eapply wr_at_agree; eauto]. Qed.

Lemma stk_agree : forall m m' lo hi, stk asegs m lo hi -> agree_on m m' lo (hi - lo) -> stk asegs m' lo hi.
Proof.
  intros m m' lo hi (H0 & H1 & HS) AG. split; [exact H0|]. split; [exact H1|].
  intros a Ha. rewrite (wview_ext m m') by (apply AG; lia). unfold mrd. rewrite (AG a) by lia. apply HS. exact Ha.
Qed.



(* [comment removed for export] *)
Definition grp_region_addr (st : mstate) (a : Z) : Prop :=
  exists rid r, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup /\ r_base r <= a < r_base r + round_up_pg (r_len r).
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pres_except_of_munch_nw : forall C W m m',
  munch W m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> pres_except C m m'.
Proof.
  intros C W m m' MU HW a Ha Hc.
  assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_unsigned by lia; apply HW; assumption).
  split; [exact E|]. rewrite (wview_ext m m' (wa a) E). tauto.
Qed.

Lemma pres_except_agree : forall C m m' A n,
  pres_except C m m' -> 0 <= A -> A + n <= 2^64 -> (forall a, A <= a < A + n -> ~ C a) -> agree_on m m' A n.
Proof. intros C m m' A n HP HA HB HC a Ha. apply (HP a); [lia| apply HC; exact Ha]. Qed.

Lemma u64arr_pres : forall C m m' A ws,
  pres_except C m m' -> u64arr asegs m A ws -> (forall a, A <= a < A + 8 * Z.of_nat (length ws) -> ~ C a) -> u64arr asegs m' A ws.
Proof.
  intros C m m' A ws HP H HC. pose proof (u64arr_bound asegs m A ws H).
  eapply u64arr_agree'; [exact H|]. eapply pres_except_agree; eauto; lia.
Qed.

Lemma u8arr_pres : forall C m m' A bs,
  pres_except C m m' -> u8arr asegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> ~ C a) -> u8arr asegs m' A bs.
Proof.
  intros C m m' A bs HP H HC. pose proof (u8arr_bound asegs m A bs H).
  eapply u8arr_agree'; [exact H|]. eapply pres_except_agree; eauto; lia.
Qed.
End CEIL_WRAP_1.

