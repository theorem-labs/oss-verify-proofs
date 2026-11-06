(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Frame Step Tac Image ZBridge SysStep SFModel ITree Nodes NodesM Decode Arr.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Prelim STree Malloc MallocCtrl KInv.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad Prog MSafe KLink KStep KOwn A_MallocBlocks A_MallocHINV A_MallocFacts_A A_Malloc_iface A_MallocFacts_inv2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import F_syscalls RMallocRep RMallocTree RMallocKit_B RMalloc_iface RMalloc_ifaceP RF_aligned16.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import StateGlue KRel Room HeapCore MF.

Set Keyed Unification.
Import ListNotations.
Import HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition IMGX : list iv := [(RIMG_LO, RMLOCK - RIMG_LO); (RCTX + 936, RIMG_HI - (RCTX + 936))].

Lemma in_IMGX : forall a, in_ivs IMGX a <-> rclient_img a.
Proof.
  intros a. unfold IMGX, in_ivs, rclient_img, in_iv. rewrite Exists_cons, Exists_cons, Exists_nil. cbn [fst snd].
  unfold RIMG_LO, RIMG_HI, RMLOCK, RCTX. lia.
Qed.

Definition blocks_of (LBf : list block) : blocks := map (fun b => (blk_addr b, blk_size b)) LBf.

Lemma in_user_blocks_of : forall LBf LB a, Permutation (blocks_of LBf) LB ->
  (in_user LB a <-> exists blk, In blk LBf /\ blk_addr blk <= a < blk_addr blk + blk_size blk).
Proof.
  intros LBf LB a P. unfold in_user. rewrite in_ivs_In. split.
  - intros (v & Hv & Ha). assert (Hv' : In v (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact P| exact Hv]).
    apply in_map_iff in Hv' as (blk & <- & Hblk). exists blk. split; [exact Hblk|]. unfold in_iv in Ha. cbn [fst snd] in Ha. exact Ha.
  - intros (blk & Hblk & Ha). exists (blk_addr blk, blk_size blk). split.
    + eapply Permutation_in; [exact P|]. apply in_map_iff. exists blk. auto.
    + unfold in_iv. cbn [fst snd]. exact Ha.
Qed.

Definition hprot (nb : Z) (s : PState) (LBf : list block) : Prop :=
  (nb = 0 /\ s = s0 /\ LBf = [])
  \/ (nb = 1 /\ exists k p A, (k <= 10)%nat /\ histR k s p /\ LBf = [(p, A, bufsz k)])
  \/ (nb = 2 /\ exists k p A p' A' sp, (k < 10)%nat /\ histR k sp p /\ mtr_malloc sp (bufsz (S k)) (Some p') s
        /\ Permutation LBf [(p', A', bufsz (S k)); (p, A, bufsz k)]).

Definition pclaim (a : Z) (s : PState) (LBf : list block) (mo : Model) : Prop :=
  a < 768 -> room mo (a mod 256) /\ hprot (a / 256) s LBf.

Lemma pclaim_none : forall a s LBf mo, 768 <= a -> pclaim a s LBf mo.
Proof. intros a s LBf mo H L. lia. Qed.

Lemma pclaim_mono : forall a a' s LBf mo, pclaim a s LBf mo -> 0 <= a -> a < 768 ->
  a mod 256 <= a' mod 256 -> a' / 256 = a / 256 -> a' < 768 -> pclaim a' s LBf mo.
Proof.
  intros a a' s LBf mo H Ha Hl Hj Hnb _ _. destruct (H Hl) as [R P]. split; [| rewrite Hnb; exact P].
  eapply room_mono; [| exact R]. pose proof (Z.mod_pos_bound a 256 ltac:(lia)). lia.
Qed.

Definition aw_holdsI (A : word) (LB : blocks) (m : word -> option byte) (mo : Model) : Prop :=
  exists s LBf, Permutation (blocks_of LBf) LB /\ RHEAP_core s LBf m /\ KREL s LBf mo /\ m_vm_materialized mo = []
                /\ pclaim (bv_unsigned A) s LBf mo /\ rw_cells rsegs m RMREPL [C4 (wz 0)].

Definition aw_depI (LB : blocks) (m : word -> option byte) (mo : Model) (a : Z) : Prop :=
  0 <= a < alloc_ceiling /\ ~ in_user LB a /\ ~ in_ivs IMGX a.

Lemma RMREPL_dep : forall LB m mo a s LBf, Permutation (blocks_of LBf) LB -> RHEAP_core s LBf m ->
  RMREPL <= a < RMREPL + 4 -> aw_depI LB m mo a.
Proof.
  intros LB m mo a s LBf P RC Ha. pose_ceil. unfold aw_depI, RMREPL, CEIL_MIN in *. split; [lia|]. split.
  - intros U. apply (in_user_blocks_of LBf LB a P) in U as (blk & Hblk & R).
    destruct (RHEAP_core_block_range s LBf m blk RC Hblk) as (_ & _ & _ & B4 & _). unfold RIMG_LO, RIMG_HI in B4. lia.
  - intros I. apply in_IMGX in I. destruct I as [_ I2]. unfold RMLOCK, RCTX in I2. lia.
Qed.

Lemma aw_frameI : forall A LB m m' mo, aw_holdsI A LB m mo ->
  (forall a, 0 <= a < W64.two64 -> aw_depI LB m mo a -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < W64.two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  aw_holdsI A LB m' mo /\ (forall a, aw_depI LB m' mo a <-> aw_depI LB m mo a).
Proof.
  intros A LB m m' mo (s & LBf & P & RC & K & MT & RM & RP) AG DOM. split; [| intros a; reflexivity].
  exists s, LBf. split; [exact P|]. split; [| split; [exact K| split; [exact MT| split; [exact RM|]]]].
  - eapply RHEAP_core_frame; [exact RC| |].
    + intros a Ha AC NB NI. symmetry. unfold wa. apply AG; [unfold W64.two64; lia|].
      split; [lia|]. split.
      * intros U. apply NB. apply (in_user_blocks_of LBf LB a P). exact U.
      * intros I. apply NI. apply in_IMGX. exact I.
    + intros x Hx. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R.
      rewrite <- (Z_to_bv_bv_unsigned x) in Hx |- *. apply DOM; [unfold W64.two64; cbn in R; lia| exact Hx].
  -
    assert (AGR : forall a, RMREPL <= a < RMREPL + 4 -> m' (wa a) = m (wa a)).
    { intros a Ha. symmetry. unfold wa. apply AG; [unfold RMREPL, W64.two64 in *; lia|]. eapply RMREPL_dep; eauto. }
    eapply rrw_cells_agree; [exact RP| | apply wmono_of_dom].
    + intros a Ha. apply AGR. cbn [cells_size csize length Nat.add] in Ha. lia.
    + intros x Hx. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R.
      rewrite <- (Z_to_bv_bv_unsigned x) in Hx |- *. apply DOM; [unfold W64.two64; cbn in R; lia| exact Hx].
Qed.

Lemma aw_dep_okI : forall A LB m mo a, aw_holdsI A LB m mo -> aw_depI LB m mo a ->
  0 <= a < alloc_ceiling /\ ~ in_user LB a /\ ~ in_ivs IMGX a.
Proof. intros A LB m mo a _ H. exact H. Qed.

Lemma aw_blocks_okI : forall A LB m mo b, aw_holdsI A LB m mo -> In b LB ->
  0 <= fst b /\ 0 <= snd b /\ fst b + snd b <= alloc_ceiling /\ alloc_ceiling < W64.two64 /\
  (forall a, in_iv b a -> ~ in_ivs IMGX a).
Proof.
  intros A LB m mo b (s & LBf & P & RC & K & MT & RM & _) Hb.
  assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact P| exact Hb]).
  apply in_map_iff in Hb' as (blk & <- & Hblk).
  destruct (RHEAP_core_block_range s LBf m blk RC Hblk) as (B1 & B2 & B3 & B4 & B5). cbn [fst snd].
  pose proof alloc_ceiling_lt64 as C64. unfold W64.two64. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  intros a Ha I. apply in_IMGX in I. destruct I as [I1 I2]. unfold in_iv in Ha. cbn [fst snd] in Ha. unfold RIMG_LO, RIMG_HI in *. lia.
Qed.

Lemma aw_user_okI : forall A LB m mo b a, aw_holdsI A LB m mo -> In b LB -> in_iv b a ->
  m (Z_to_bv 64 a) <> None /\ find_segment rsegs a 1 = None.
Proof.
  intros A LB m mo b a (s & LBf & P & RC & K & MT & RM & _) Hb Ha.
  assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact P| exact Hb]).
  apply in_map_iff in Hb' as (blk & <- & Hblk). unfold in_iv in Ha. cbn [fst snd] in Ha.
  destruct (RHEAP_core_block_range s LBf m blk RC Hblk) as (B1 & B2 & B3 & B4 & B5).
  split; [exact (B5 a Ha)|]. apply ref_find_segment_none; [lia|]. unfold RIMG_LO, RIMG_HI in B4. lia.
Qed.

Lemma aw_blocks_disjI : forall A LB m mo b b' a, aw_holdsI A LB m mo -> In b LB -> In b' LB -> fst b <> fst b' ->
  in_iv b a -> ~ in_iv b' a.
Proof.
  intros A LB m mo b b' a (s & LBf & P & RC & _) Hb Hb' NE Ha.
  assert (X : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact P| exact Hb]).
  assert (X' : In b' (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact P| exact Hb']).
  apply in_map_iff in X as (blk & <- & Hblk). apply in_map_iff in X' as (blk' & <- & Hblk').
  cbn [fst snd] in NE. unfold in_iv in *. cbn [fst snd] in *.
  exact (RHEAP_core_blocks_disjoint_addr s LBf m blk blk' a RC Hblk Hblk' NE Ha).
Qed.

Lemma aw_vm_frame : forall A LB m mo mo', m_vm mo' = m_vm mo -> m_halted mo' = None -> aw_holdsI A LB m mo -> aw_holdsI A LB m mo'.
Proof.
  intros A LB m mo mo' Hvm Hh (s & LBf & P & RC & KR & MAT & PC & RP).
  exists s, LBf. split; [exact P|]. split; [exact RC|]. split; [exact (KREL_frame s LBf mo mo' Hvm Hh KR)|].
  split; [unfold m_vm_materialized in *; rewrite Hvm; exact MAT|]. split; [| exact RP].
  intros L. destruct (PC L) as [RM HP]. split; [| exact HP].
  apply (room_frame mo mo'); [unfold m_vmmaps; rewrite Hvm; reflexivity| exact RM].
Qed.

Lemma aw_fds : forall A LB m mo fds, aw_holdsI A LB m mo -> aw_holdsI A LB m (with_fds fds mo).
Proof.
  intros A LB m mo fds H. apply (aw_vm_frame A LB m mo); [reflexivity| | exact H].
  destruct H as (s & LBf & _ & _ & KR & _). exact (KREL_halted _ _ _ KR).
Qed.

Lemma aw_blocks_loI : forall A LB m mo b, aw_holdsI A LB m mo -> In b LB -> 4096 <= fst b.
Proof.
  intros A LB m mo b (s & LBf & P & RC & _) Hb.
  assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact P| exact Hb]).
  apply in_map_iff in Hb' as (blk & <- & Hblk).
  destruct (RHEAP_core_block_range s LBf m blk RC Hblk) as (B1 & _). cbn [fst]. exact B1.
Qed.

Lemma aw_ceiling_smallI : forall mo : Model, alloc_ceiling <= Mem.two62Z.
Proof. intros _. pose proof alloc_ceiling_lt47. unfold Mem.two62Z. lia. Qed.

Definition NG (ws : list window) : Prop := forall w, In w ws -> w_kind w < K_GHOST.
Lemma NG_incl : forall ws ws', NG ws -> (forall w, In w ws' -> In w ws) -> NG ws'.
Proof. intros ws ws' H I w Hw. exact (H w (I w Hw)). Qed.
Lemma NG_app_block : forall ws a n, NG ws -> NG (ws ++ [Win a n K_BLOCK]).
Proof. intros ws a n H w Hw. apply in_app_or in Hw as [Hw|[<-|[]]]; [exact (H w Hw)| cbn [w_kind]; unfold K_BLOCK, K_GHOST; lia]. Qed.
Definition aw_holdsW (A : word) (LB : blocks) (ws : list window) (m : word -> option byte) (mo : Model) : Prop :=
  aw_holdsI A LB m mo /\ NG ws.
Lemma aw_frameW : forall A LB ws m m' mo, aw_holdsW A LB ws m mo ->
  (forall a, 0 <= a < W64.two64 -> aw_depI LB m mo a -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < W64.two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  aw_holdsW A LB ws m' mo /\ (forall a, aw_depI LB m' mo a <-> aw_depI LB m mo a).
Proof. intros A LB ws m m' mo [H N] F M. destruct (aw_frameI A LB m m' mo H F M) as [H' D]. split; [split; [exact H'| exact N]| exact D]. Qed.
Lemma aw_keepW : forall A LB ws ws' m mo, aw_holdsW A LB ws m mo -> wins_keep LB ws ws' -> aw_holdsW A LB ws' m mo.
Proof.
  intros A LB ws ws' m mo [H N] (KA & _). split; [exact H|]. intros w Hw.
  destruct (Z_lt_dec (w_kind w) K_GHOST) as [L|G]; [exact L|]. exfalso.
  assert (TI : aw_tied w) by (right; lia). apply (KA w TI) in Hw. specialize (N w Hw). lia.
Qed.
Lemma aw_ghost_apartW : forall A LB ws m mo, aw_holdsW A LB ws m mo -> ghost_apart ws.
Proof. intros A LB ws m mo [_ N] w w' Hw _ K. specialize (N w Hw). lia. Qed.
Definition AWI : alloc_world rsegs IMGX :=
  AW rsegs IMGX aw_holdsW aw_depI (fun _ => alloc_ceiling) aw_frameW aw_keepW aw_ghost_apartW
     (fun A LB ws m mo a H => aw_dep_okI A LB m mo a (proj1 H)) (fun A LB ws m mo b H => aw_blocks_okI A LB m mo b (proj1 H))
     (fun A LB ws m mo b a H => aw_user_okI A LB m mo b a (proj1 H)) (fun A LB ws m mo b b' a H => aw_blocks_disjI A LB m mo b b' a (proj1 H))
     aw_ceiling_smallI (fun A LB ws m mo b H => aw_blocks_loI A LB m mo b (proj1 H)).

Lemma aw_holdsW_intro : forall A LB ws m mo, aw_holdsI A LB m mo -> NG ws -> aw_holds rsegs IMGX AWI A LB ws m mo.
Proof. intros A LB ws m mo H N. split; [exact H| exact N]. Qed.

End CEIL.

From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Module TwinB.
Import stdpp.base stdpp.decidable stdpp.list stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Image OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.NodesM OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Arr.
Import OSSVerify.msgpack_c.unpack_pack_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Prelim OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Malloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.KInv.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Monad OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Prog OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.MSafe OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KLink OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KOwn OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocBlocks OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocHINV OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocFacts_A OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_Malloc_iface OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocFacts_inv2.
Import F_syscalls.TwinB RMallocRep.TwinB RMallocTree.TwinB RMallocKit_B.TwinB RMalloc_iface.TwinB RMalloc_ifaceP.TwinB RF_aligned16.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.StateGlue OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.KRel OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.Room.
Import HeapCore.TwinB MF.TwinB.

Set Keyed Unification.
Import ListNotations.
Import HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.CeilLia.
Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition IMGX : list iv := [(RIMG_LO, RMLOCK - RIMG_LO); (RCTX + 936, RIMG_HI - (RCTX + 936))].

Lemma in_IMGX : forall a, in_ivs IMGX a <-> rclient_img a.
Proof.
  intros a. unfold IMGX, in_ivs, rclient_img, in_iv. rewrite Exists_cons, Exists_cons, Exists_nil. cbn [fst snd].
  unfold RIMG_LO, RIMG_HI, RMLOCK, RCTX. lia.
Qed.

Definition blocks_of (LBf : list block) : blocks := map (fun b => (blk_addr b, blk_size b)) LBf.

Lemma in_user_blocks_of : forall LBf LB a, Permutation (blocks_of LBf) LB ->
  (in_user LB a <-> exists blk, In blk LBf /\ blk_addr blk <= a < blk_addr blk + blk_size blk).
Proof.
  intros LBf LB a P. unfold in_user. rewrite in_ivs_In. split.
  - intros (v & Hv & Ha). assert (Hv' : In v (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact P| exact Hv]).
    apply in_map_iff in Hv' as (blk & <- & Hblk). exists blk. split; [exact Hblk|]. unfold in_iv in Ha. cbn [fst snd] in Ha. exact Ha.
  - intros (blk & Hblk & Ha). exists (blk_addr blk, blk_size blk). split.
    + eapply Permutation_in; [exact P|]. apply in_map_iff. exists blk. auto.
    + unfold in_iv. cbn [fst snd]. exact Ha.
Qed.

Definition hprot (nb : Z) (s : PState) (LBf : list block) : Prop :=
  (nb = 0 /\ s = s0 /\ LBf = [])
  \/ (nb = 1 /\ exists k p A, (k <= 10)%nat /\ histR k s p /\ LBf = [(p, A, bufsz k)])
  \/ (nb = 2 /\ exists k p A p' A' sp, (k < 10)%nat /\ histR k sp p /\ mtr_malloc sp (bufsz (S k)) (Some p') s
        /\ Permutation LBf [(p', A', bufsz (S k)); (p, A, bufsz k)]).

Definition pclaim (a : Z) (s : PState) (LBf : list block) (mo : Model) : Prop :=
  a < 768 -> room mo (a mod 256) /\ hprot (a / 256) s LBf.

Lemma pclaim_none : forall a s LBf mo, 768 <= a -> pclaim a s LBf mo.
Proof. intros a s LBf mo H L. lia. Qed.

Lemma pclaim_mono : forall a a' s LBf mo, pclaim a s LBf mo -> 0 <= a -> a < 768 ->
  a mod 256 <= a' mod 256 -> a' / 256 = a / 256 -> a' < 768 -> pclaim a' s LBf mo.
Proof.
  intros a a' s LBf mo H Ha Hl Hj Hnb _ _. destruct (H Hl) as [R P]. split; [| rewrite Hnb; exact P].
  eapply room_mono; [| exact R]. pose proof (Z.mod_pos_bound a 256 ltac:(lia)). lia.
Qed.

Definition aw_holdsI (A : word) (LB : blocks) (m : word -> option byte) (mo : Model) : Prop :=
  exists s LBf, Permutation (blocks_of LBf) LB /\ RHEAP_core s LBf m /\ KREL s LBf mo /\ m_vm_materialized mo = []
                /\ pclaim (bv_unsigned A) s LBf mo /\ rw_cells rsegs m RMREPL [C4 (wz 0)].

Definition aw_depI (LB : blocks) (m : word -> option byte) (mo : Model) (a : Z) : Prop :=
  0 <= a < alloc_ceiling /\ ~ in_user LB a /\ ~ in_ivs IMGX a.

Lemma RMREPL_dep : forall LB m mo a s LBf, Permutation (blocks_of LBf) LB -> RHEAP_core s LBf m ->
  RMREPL <= a < RMREPL + 4 -> aw_depI LB m mo a.
Proof.
  intros LB m mo a s LBf P RC Ha. pose_ceil. unfold aw_depI, RMREPL, CEIL_MIN in *. split; [lia|]. split.
  - intros U. apply (in_user_blocks_of LBf LB a P) in U as (blk & Hblk & R).
    destruct (RHEAP_core_block_range s LBf m blk RC Hblk) as (_ & _ & _ & B4 & _). unfold RIMG_LO, RIMG_HI in B4. lia.
  - intros I. apply in_IMGX in I. destruct I as [_ I2]. unfold RMLOCK, RCTX in I2. lia.
Qed.

Lemma aw_frameI : forall A LB m m' mo, aw_holdsI A LB m mo ->
  (forall a, 0 <= a < W64.two64 -> aw_depI LB m mo a -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < W64.two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  aw_holdsI A LB m' mo /\ (forall a, aw_depI LB m' mo a <-> aw_depI LB m mo a).
Proof.
  intros A LB m m' mo (s & LBf & P & RC & K & MT & RM & RP) AG DOM. split; [| intros a; reflexivity].
  exists s, LBf. split; [exact P|]. split; [| split; [exact K| split; [exact MT| split; [exact RM|]]]].
  - eapply RHEAP_core_frame; [exact RC| |].
    + intros a Ha AC NB NI. symmetry. unfold wa. apply AG; [unfold W64.two64; lia|].
      split; [lia|]. split.
      * intros U. apply NB. apply (in_user_blocks_of LBf LB a P). exact U.
      * intros I. apply NI. apply in_IMGX. exact I.
    + intros x Hx. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R.
      rewrite <- (Z_to_bv_bv_unsigned x) in Hx |- *. apply DOM; [unfold W64.two64; cbn in R; lia| exact Hx].
  -
    assert (AGR : forall a, RMREPL <= a < RMREPL + 4 -> m' (wa a) = m (wa a)).
    { intros a Ha. symmetry. unfold wa. apply AG; [unfold RMREPL, W64.two64 in *; lia|]. eapply RMREPL_dep; eauto. }
    eapply rrw_cells_agree; [exact RP| | apply wmono_of_dom].
    + intros a Ha. apply AGR. cbn [cells_size csize length Nat.add] in Ha. lia.
    + intros x Hx. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R.
      rewrite <- (Z_to_bv_bv_unsigned x) in Hx |- *. apply DOM; [unfold W64.two64; cbn in R; lia| exact Hx].
Qed.

Lemma aw_dep_okI : forall A LB m mo a, aw_holdsI A LB m mo -> aw_depI LB m mo a ->
  0 <= a < alloc_ceiling /\ ~ in_user LB a /\ ~ in_ivs IMGX a.
Proof. intros A LB m mo a _ H. exact H. Qed.

Lemma aw_blocks_okI : forall A LB m mo b, aw_holdsI A LB m mo -> In b LB ->
  0 <= fst b /\ 0 <= snd b /\ fst b + snd b <= alloc_ceiling /\ alloc_ceiling < W64.two64 /\
  (forall a, in_iv b a -> ~ in_ivs IMGX a).
Proof.
  intros A LB m mo b (s & LBf & P & RC & K & MT & RM & _) Hb.
  assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact P| exact Hb]).
  apply in_map_iff in Hb' as (blk & <- & Hblk).
  destruct (RHEAP_core_block_range s LBf m blk RC Hblk) as (B1 & B2 & B3 & B4 & B5). cbn [fst snd].
  pose proof alloc_ceiling_lt64 as C64. unfold W64.two64. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  intros a Ha I. apply in_IMGX in I. destruct I as [I1 I2]. unfold in_iv in Ha. cbn [fst snd] in Ha. unfold RIMG_LO, RIMG_HI in *. lia.
Qed.

Lemma aw_user_okI : forall A LB m mo b a, aw_holdsI A LB m mo -> In b LB -> in_iv b a ->
  m (Z_to_bv 64 a) <> None /\ find_segment rsegs a 1 = None.
Proof.
  intros A LB m mo b a (s & LBf & P & RC & K & MT & RM & _) Hb Ha.
  assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact P| exact Hb]).
  apply in_map_iff in Hb' as (blk & <- & Hblk). unfold in_iv in Ha. cbn [fst snd] in Ha.
  destruct (RHEAP_core_block_range s LBf m blk RC Hblk) as (B1 & B2 & B3 & B4 & B5).
  split; [exact (B5 a Ha)|]. apply ref_find_segment_none; [lia|]. unfold RIMG_LO, RIMG_HI in B4. lia.
Qed.

Lemma aw_blocks_disjI : forall A LB m mo b b' a, aw_holdsI A LB m mo -> In b LB -> In b' LB -> fst b <> fst b' ->
  in_iv b a -> ~ in_iv b' a.
Proof.
  intros A LB m mo b b' a (s & LBf & P & RC & _) Hb Hb' NE Ha.
  assert (X : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact P| exact Hb]).
  assert (X' : In b' (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact P| exact Hb']).
  apply in_map_iff in X as (blk & <- & Hblk). apply in_map_iff in X' as (blk' & <- & Hblk').
  cbn [fst snd] in NE. unfold in_iv in *. cbn [fst snd] in *.
  exact (RHEAP_core_blocks_disjoint_addr s LBf m blk blk' a RC Hblk Hblk' NE Ha).
Qed.

Lemma aw_vm_frame : forall A LB m mo mo', m_vm mo' = m_vm mo -> m_halted mo' = None -> aw_holdsI A LB m mo -> aw_holdsI A LB m mo'.
Proof.
  intros A LB m mo mo' Hvm Hh (s & LBf & P & RC & KR & MAT & PC & RP).
  exists s, LBf. split; [exact P|]. split; [exact RC|]. split; [exact (KREL_frame s LBf mo mo' Hvm Hh KR)|].
  split; [unfold m_vm_materialized in *; rewrite Hvm; exact MAT|]. split; [| exact RP].
  intros L. destruct (PC L) as [RM HP]. split; [| exact HP].
  apply (room_frame mo mo'); [unfold m_vmmaps; rewrite Hvm; reflexivity| exact RM].
Qed.

Lemma aw_fds : forall A LB m mo fds, aw_holdsI A LB m mo -> aw_holdsI A LB m (with_fds fds mo).
Proof.
  intros A LB m mo fds H. apply (aw_vm_frame A LB m mo); [reflexivity| | exact H].
  destruct H as (s & LBf & _ & _ & KR & _). exact (KREL_halted _ _ _ KR).
Qed.

Lemma aw_blocks_loI : forall A LB m mo b, aw_holdsI A LB m mo -> In b LB -> 4096 <= fst b.
Proof.
  intros A LB m mo b (s & LBf & P & RC & _) Hb.
  assert (Hb' : In b (blocks_of LBf)) by (eapply Permutation_in; [apply Permutation_sym; exact P| exact Hb]).
  apply in_map_iff in Hb' as (blk & <- & Hblk).
  destruct (RHEAP_core_block_range s LBf m blk RC Hblk) as (B1 & _). cbn [fst]. exact B1.
Qed.

Lemma aw_ceiling_smallI : forall mo : Model, alloc_ceiling <= Mem.two62Z.
Proof. intros _. pose proof alloc_ceiling_lt47. unfold Mem.two62Z. lia. Qed.

Definition NG (ws : list window) : Prop := forall w, In w ws -> w_kind w < K_GHOST.
Lemma NG_incl : forall ws ws', NG ws -> (forall w, In w ws' -> In w ws) -> NG ws'.
Proof. intros ws ws' H I w Hw. exact (H w (I w Hw)). Qed.
Lemma NG_app_block : forall ws a n, NG ws -> NG (ws ++ [Win a n K_BLOCK]).
Proof. intros ws a n H w Hw. apply in_app_or in Hw as [Hw|[<-|[]]]; [exact (H w Hw)| cbn [w_kind]; unfold K_BLOCK, K_GHOST; lia]. Qed.
Definition aw_holdsW (A : word) (LB : blocks) (ws : list window) (m : word -> option byte) (mo : Model) : Prop :=
  aw_holdsI A LB m mo /\ NG ws.
Lemma aw_frameW : forall A LB ws m m' mo, aw_holdsW A LB ws m mo ->
  (forall a, 0 <= a < W64.two64 -> aw_depI LB m mo a -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < W64.two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  aw_holdsW A LB ws m' mo /\ (forall a, aw_depI LB m' mo a <-> aw_depI LB m mo a).
Proof. intros A LB ws m m' mo [H N] F M. destruct (aw_frameI A LB m m' mo H F M) as [H' D]. split; [split; [exact H'| exact N]| exact D]. Qed.
Lemma aw_keepW : forall A LB ws ws' m mo, aw_holdsW A LB ws m mo -> wins_keep LB ws ws' -> aw_holdsW A LB ws' m mo.
Proof.
  intros A LB ws ws' m mo [H N] (KA & _). split; [exact H|]. intros w Hw.
  destruct (Z_lt_dec (w_kind w) K_GHOST) as [L|G]; [exact L|]. exfalso.
  assert (TI : aw_tied w) by (right; lia). apply (KA w TI) in Hw. specialize (N w Hw). lia.
Qed.
Lemma aw_ghost_apartW : forall A LB ws m mo, aw_holdsW A LB ws m mo -> ghost_apart ws.
Proof. intros A LB ws m mo [_ N] w w' Hw _ K. specialize (N w Hw). lia. Qed.
Definition AWI : alloc_world rsegs IMGX :=
  AW rsegs IMGX aw_holdsW aw_depI (fun _ => alloc_ceiling) aw_frameW aw_keepW aw_ghost_apartW
     (fun A LB ws m mo a H => aw_dep_okI A LB m mo a (proj1 H)) (fun A LB ws m mo b H => aw_blocks_okI A LB m mo b (proj1 H))
     (fun A LB ws m mo b a H => aw_user_okI A LB m mo b a (proj1 H)) (fun A LB ws m mo b b' a H => aw_blocks_disjI A LB m mo b b' a (proj1 H))
     aw_ceiling_smallI (fun A LB ws m mo b H => aw_blocks_loI A LB m mo b (proj1 H)).

Lemma aw_holdsW_intro : forall A LB ws m mo, aw_holdsI A LB m mo -> NG ws -> aw_holds rsegs IMGX AWI A LB ws m mo.
Proof. intros A LB ws m mo H N. split; [exact H| exact N]. Qed.

End CEIL.
End TwinB.
