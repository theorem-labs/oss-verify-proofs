(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Lib Require Import TacS8 ImageS8 ZBridgeS8 SysStepS8 SFModelS8 ITreeS8 NodesS8 DecodeS8 ArrS8.

From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Agent Require Import F_syscallsS8 MallocRepS8 F_malloc_freeS8 F_malloc_fastS8 F_malloc_entryS8 F_malloc_enframeS8 MallocTreeS8 MallocFacts_AS8 MallocHINVS8 MallocKit_AS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Agent Require Import MallocKit_ABS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Spec Require Import MonadS8 ProgS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Agent Require Import Malloc_fpS8 MallocKit_A2S8 AllocSlot_ifaceS8 F_malloc_joinS8 Malloc_ifaceS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Agent Require Import MallocNatS8 MallocFacts_ASS8 MallocKit_A3S8 ASlot_W0S8 ASlot_W1S8 ASlot_W2S8 ASlot_W8S8 ASlot_W9S8 ASlot_W10S8 ASlot_W12S8 ASlot_IS8 ASlot_M0S8 ASlot_M1S8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Agent Require MallocFacts_inv4S8.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.

Definition epi_frame (jj : list byte) (s4v s3v s2v s1v s0v rav : word) : list cell :=
  [CB 48 jj; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

Lemma ag_frame_epi m A sc j s4v s3v s2v s1v s0v rav :
  rw_cells asegs m A (ag_frame sc j s4v s3v s2v s1v s0v rav) ->
  rw_cells asegs m A (epi_frame (cells_bytes [C8 (Z_to_bv 64 (sc * 2)); CB 40 j]) s4v s3v s2v s1v s0v rav).
Proof.
  intros FR. unfold ag_frame in FR. unfold epi_frame.
  pose proof (rw_cells_merge asegs m A [] [C8 (Z_to_bv 64 (sc * 2)); CB 40 j] [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] FR) as X.
  cbn [app cells_size csize Nat.add] in X. exact X.
Qed.

Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).

Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.

Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.

Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK (S f).
Hypothesis ERR : rw_cells asegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv asegs m.

Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.

Lemma errno_lit2 : errno_addr tp = 107900.
Proof. rewrite TP. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma unk_agree_keep stE mE :
  s_shadow stE = s_shadow st ->
  (forall rid r, r_kind r = RKGroup -> (s_regions stE) !! rid = Some r -> (s_regions st) !! rid = Some r) ->
  (forall b, is_Some ((s_groups stE) !! b) <-> is_Some ((s_groups st) !! b)) ->
  (forall rid r off h, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) ->
      cell_read (get_shadow st rid) off = Unknown h -> ~ grp_hdr_cov st rid off -> mE (wa (r_base r + off)) = m (wa (r_base r + off))) ->
  unk_agree stE o mE.
Proof.
  intros ES ERG EG AG rid r off h Hr Hk Ho Hc NG.
  pose proof (ERG rid r Hk Hr) as Hr0.
  assert (Hc0 : cell_read (get_shadow st rid) off = Unknown h) by (revert Hc; unfold get_shadow; rewrite ES; intros X; exact X).
  assert (NG0 : ~ grp_hdr_cov st rid off).
  { intros (bq & gh & Hbq & Hf & Hoff). apply NG. destruct (proj2 (EG bq) (ex_intro _ gh Hbq)) as [gh1 Hbq1]. exists bq, gh1. auto. }
  rewrite (AG rid r off h Hr0 Hk Ho Hc0 NG0). exact (UA rid r off h Hr0 Hk Ho Hc0 NG0).
Qed.

End LEVEL.
End CEIL_WRAP_1.

