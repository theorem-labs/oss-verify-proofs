(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (2 recorded proofs replaced by written proofs (dequeue_self_eq, dequeue_other_eq)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp MallocKit_A2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_A3 ASlot_W1.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASlot_W5 () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib4Spec6Malloc:m_set_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_set_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8optr_eqbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8set_headC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_W53clrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8put_metaC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib6Malloc<MallocKit_AB<upd_meta_putC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8aptr_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_AB;aptr_eqb_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib4Spec6Malloc7dequeueC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes4bool01C47Corelib4Init5Logic3notC59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib6Malloc<MallocKit_ABFget_meta_rec_put_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_AB>rec_set_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_AB<aptr_eqb_neqC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02".
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition clr (r : meta) : meta := m_set_prev None (m_set_next None r).

Lemma dequeue_self_eq sc g st :
  m_next (get_meta_rec st g) = Some g ->
  dequeue (LActive sc) g st = put_meta g (clr (get_meta_rec st g)) (set_active sc None st).
Proof.
  intros GN. unfold dequeue. rewrite GN. cbn [optr_eqb negb]. rewrite (proj2 (aptr_eqb_eq g g) eq_refl). cbn [negb set_head].
  rewrite upd_meta_put. reflexivity.
Qed.

Lemma dequeue_other_eq sc g nx pv st :
  m_next (get_meta_rec st g) = Some nx -> m_prev (get_meta_rec st g) = Some pv -> nx <> g -> pv <> g ->
  active st sc = Some g ->
  dequeue (LActive sc) g st =
    let st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st in
    let st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1 in
    let st3 := set_active sc (Some nx) st2 in
    put_meta g (clr (get_meta_rec st g)) st3.
Proof.
  intros GN GP NEn NEp HA. unfold dequeue. rewrite GN, GP. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx g NEn). cbn [negb get_head set_head].
  rewrite !upd_meta_put.
  match goal with |- context [optr_eqb (active ?s sc) (Some g)] => change (active s sc) with (active st sc) end.
  rewrite HA. cbn [optr_eqb]. rewrite (proj2 (aptr_eqb_eq g g) eq_refl). cbv zeta.
  f_equal. f_equal. rewrite rec_set_active. rewrite (get_meta_rec_put_other _ nx) by (intros E; apply NEn; symmetry; exact E).
  rewrite (get_meta_rec_put_other _ pv) by (intros E; apply NEp; symmetry; exact E). reflexivity.
Qed.

Section DEQ.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis HA : active st sc = Some g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis FR0 : m_freed mr = 0.

Definition deq_regs (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 CTX) a0 a1 a2 (Z_to_bv 64 (CTX + 8 * (sc + 10))) a4 a5 a6 a7
      (Z_to_bv 64 (sc + 10)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.
End DEQ.


End CANSEC1.
