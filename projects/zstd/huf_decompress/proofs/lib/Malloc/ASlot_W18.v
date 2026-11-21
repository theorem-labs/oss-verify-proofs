(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (4 recorded proofs replaced by written proofs (as_queue_eq, as_free_meta_eq, outside_In and 1 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr Bytes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp MallocKit_A2 F_malloc_big.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_A3.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASlot_W18 () := "C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5queueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib4Spec6Malloc8optr_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_set_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_set_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8set_headC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K59OSSVerify5KrLib4Spec6Malloc<undef_reason01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_W18;as_queue_stC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00I47Corelib4Init9Datatypes6option00I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03c59OSSVerify5KrLib6Malloc9ASlot_W18;as_queue_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9free_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8put_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_ABEget_meta_rec_put_sameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_W188as_fm_stC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C46Stdlib5Lists4List2InK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00C47Corelib4Init5Logic7f_equalC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7and_indC47Corelib4Init5Logic3notC47Corelib4Init9Datatypes8list_indK47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00c59OSSVerify5KrLib6Malloc9ASlot_W18:outside_InC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01".
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition as_fm_link (st0 : mstate) (g head : aptr) : mstate :=
  let hprev := m_prev (get_meta_rec st0 head) in
  let st1 := upd_meta g (fun r => m_set_prev hprev (m_set_next (Some head) r)) st0 in
  let st2 := match hprev with Some pv => upd_meta pv (m_set_next (Some g)) st1 | None => st1 end in
  upd_meta head (m_set_prev (Some g)) st2.

Definition as_fm_single (st0 : mstate) (h : lhead) (g : aptr) : mstate :=
  set_head h (Some g) (upd_meta g (fun r => m_set_prev (Some g) (m_set_next (Some g) r)) st0).

Definition as_queue_st (h : lhead) (g : aptr) (st0 : mstate) : mstate :=
  match get_head st0 h with
  | Some head => as_fm_link st0 g head
  | None => as_fm_single st0 h g
  end.

Lemma as_queue_eq : forall R h g st0 (k : mstate -> Malloc.M R) (bail : Malloc.M R),
  m_next (get_meta_rec st0 g) = None -> m_prev (get_meta_rec st0 g) = None ->
  queue h g st0 k bail = k (as_queue_st h g st0).
Proof.
  intros R h g st0 k bail Hn Hp. unfold queue, guard. rewrite Hn, Hp. cbn [optr_eqb].
  unfold as_queue_st, as_fm_link, as_fm_single. destruct (get_head st0 h); reflexivity.
Qed.

Definition as_fm_st (st : mstate) (g : aptr) : mstate := as_queue_st LFree g (put_meta g meta0 st).

Lemma as_free_meta_eq : forall R st g (k : mstate -> Malloc.M R) (bail : Malloc.M R), free_meta g st k bail = k (as_fm_st st g).
Proof.
  intros. unfold free_meta, as_fm_st. apply as_queue_eq; rewrite get_meta_rec_put_same; reflexivity.
Qed.

Lemma outside_In W x lo hi : outside W x -> In (lo, hi) W -> ~ (lo <= x < hi).
Proof.
  induction W as [|[a b] W IH]; cbn; intros HO HI; [destruct HI|].
  destruct HI as [E|HI]; [inversion E; subst; tauto|]. apply IH; tauto.
Qed.

Lemma sub_fp_single W lo hi : In (lo, hi) W -> sub_fp [(lo, hi)] W.
Proof. intros HI x HO. cbn. split; [exact (outside_In W x lo hi HO HI)| exact I]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FAILM.
Variables (st : mstate) (mt : aptr).
Let G := conc st mt.
Hypothesis MST : meta_slot st mt.
(* [comment removed for export] *)
Hypothesis FL : forall h, c_free_meta_head (ctx st) = Some h ->
  meta_slot st h /\ h <> mt /\ exists p, m_prev (get_meta_rec st h) = Some p /\ meta_slot st p /\ p <> mt.

Definition failW : list (Z * Z) :=
  (G, G + 40) :: (CTX + 16, CTX + 24)
  :: match c_free_meta_head (ctx st) with
     | Some h => (conc st h, conc st h + 40)
                 :: match m_prev (get_meta_rec st h) with Some p => [(conc st p, conc st p + 40)] | None => [] end
     | None => []
     end.
End FAILM.


End CANSEC1.
