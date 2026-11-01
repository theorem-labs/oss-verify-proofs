(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_sa Fz_I3_base Fz_I3_fxi Fz_W2_exd.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition wboxed (P : Prop) : Prop := P.
Ltac wbox H := lazymatch type of H with ?P => change P with (wboxed P) in H end.
Ltac wunbox H := unfold wboxed in H.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition TSD_MAIN : Z := 0x351cd0.        (* [comment removed for export] *)
Definition TH_ONCE : Z := 0x32dea4.         (* [comment removed for export] *)
Definition TH_KEY : Z := 0x32dea8.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition libenv_static (a : Z) : Prop :=
  (IC_S + 8 <= a < IC_S + 9) \/ (IC_S + 32 <= a < IC_S + 40) \/ (IC_S + 96 <= a < IC_S + 104)
  \/ (TH_ONCE <= a < TH_ONCE + 4) \/ (TH_KEY <= a < TH_KEY + 4)
  \/ (RATP - 88 <= a < RATP - 80) \/ (TSD_MAIN <= a < TSD_MAIN + 8 * 128)
  \/ (DC_S <= a < DC_S + 24) \/ (DC_GLOBAL_LOCK <= a < DC_GLOBAL_LOCK + 8) \/ (DC_IP12 <= a < DC_IP12 + 8).

Definition libenv_fp (LBL : list block) (a : Z) : Prop :=
  libenv_static a \/ (exists b, In b LBL /\ blk_addr b <= a < blk_addr b + blk_size b).

Definition libenv (m : mem) (LBL : list block) (E : Z) : Prop :=
  exists (od pad tw ne : word) (k MK SA NODES : Z) (pm psa pn pk : bptr) (kd LK : Z),
    LBL = [(pm, MK, 72); (psa, SA, 32); (pn, NODES, 128); (pk, LK, 40)]
    /\ rw_cells usegs m (IC_S + 8) [C1 (Z_to_bv 8 0)]
    /\ rw_cells usegs m (IC_S + 32) [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)]
    /\ rw_cells usegs m (IC_S + 96) [C8 od]
    /\ rw_cells usegs m TH_ONCE [C4 (Z_to_bv 64 2)]
    /\ rw_cells usegs m TH_KEY [C4 (Z_to_bv 64 k)] /\ 0 <= k < 128
    /\ rw_cells usegs m (RATP + -88) [C8 (Z_to_bv 64 TSD_MAIN)]
    /\ rw_cells usegs m (TSD_MAIN + 8 * k) [C8 (Z_to_bv 64 MK)] /\ 0 < MK < 2 ^ 64
    /\ rw_cells usegs m (MK + 8 * 3) [C8 (Z_to_bv 64 SA)] /\ 0 < SA < 2 ^ 64
    /\ rw_cells usegs m SA (sa_hdr (Z_to_bv 64 1) pad tw ne (Z_to_bv 64 NODES)) /\ 0 < NODES < 2 ^ 64
    /\ bv_unsigned ne <> 0
    /\ rw_cells usegs m NODES [C8 (Z_to_bv 64 E)]
    /\ rw_cells usegs m DC_S [C1 (Z_to_bv 8 1)]
    /\ rw_cells usegs m (DC_S + 4) [C4 (Z_to_bv 64 kd)] /\ 0 <= kd < 128
    /\ rw_cells usegs m (DC_S + 8) [C4 (Z_to_bv 64 2)] /\ rw_cells usegs m (DC_S + 12) [C4 (Z_to_bv 64 1)]
    /\ rw_cells usegs m (DC_S + 16) [C4 (Z_to_bv 64 2)] /\ rw_cells usegs m (DC_S + 20) [C4 (Z_to_bv 64 1)]
    /\ rw_cells usegs m (TSD_MAIN + 8 * kd) [C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m DC_GLOBAL_LOCK [C8 (Z_to_bv 64 LK)] /\ 0 < LK /\ LK mod 4 = 0
    /\ rw_cells usegs m LK (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
    /\ rw_cells usegs m DC_IP12 [C8 (Z_to_bv 64 0)].

(* [comment removed for export] *)
Theorem libenv_fp_where : forall LBL a, libenv_fp LBL a ->
  (0x2c0000 <= a < 0x353000 /\ ~ ralloc_static a /\ a <> LX_FLAGS) \/ (exists b, In b LBL /\ blk_addr b <= a < blk_addr b + blk_size b).
Proof.
  intros LBL a [H|H]; [left| right; exact H].
  unfold libenv_static, IC_S, TH_ONCE, TH_KEY, RMallocRep.RATP, TSD_MAIN, DC_S, DC_GLOBAL_LOCK, DC_IP12 in H. unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, LX_FLAGS in *. lia.
Qed.

Theorem libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
Proof.
  intros m m' LBL E ENV SAME.
  destruct ENV as (od & pad & tw & ne & k & MK & SA & NODES & pm & psa & pn & pk & kd & LK
    & e_lbl & c_ic8 & c_ic32 & c_ic96 & c_once & c_key & r_k & c_tsdp & c_slot & r_mk & c_mk24 & r_sa
    & c_hdr & r_nodes & r_ne & c_nodes & c_dc0 & c_dc4 & r_kd & c_dc8 & c_dc12 & c_dc16 & c_dc20
    & c_dslot & c_glock & r_lk & r_lkal & c_mtx & c_ip12).
  exists od, pad, tw, ne, k, MK, SA, NODES, pm, psa, pn, pk, kd, LK.
  refine (conj e_lbl (conj _ (conj _ (conj _ (conj _ (conj _ (conj r_k (conj _ (conj _ (conj r_mk
    (conj _ (conj r_sa (conj _ (conj r_nodes (conj r_ne (conj _ (conj _ (conj _ (conj r_kd
    (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj r_lk (conj r_lkal (conj _ _)))))))))))))))))))))))))))).
  all: apply (rw_cells_agree _ m m' _ _ SAME); [assumption|].
  all: intros a INSIDE; cbn [cells_size csize sa_hdr mutex_cells Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in INSIDE.
  all: first
    [ left; unfold libenv_static; clear - INSIDE r_k r_kd; lia
    | right; rewrite e_lbl; apply Exists_exists;
      solve [repeat first [apply Exists_cons_hd; cbn [blk_addr blk_size fst snd]; clear - INSIDE; lia | apply Exists_cons_tl]] ].
Qed.

(* [comment removed for export] *)
Lemma libenv_cells : forall m LBL E, libenv m LBL E ->
  exists (od pad tw ne : word) (k MK SA NODES : Z) (pm psa pn pk : bptr) (LK : Z),
       LBL = [(pm, MK, 72); (psa, SA, 32); (pn, NODES, 128); (pk, LK, 40)]
    /\ rw_cells usegs m (IC_S + 8) [C1 (Z_to_bv 8 0)] /\ rw_cells usegs m (IC_S + 32) [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)] /\ rw_cells usegs m (IC_S + 96) [C8 od]
    /\ ro_cells usegs m 0x32dea4 [C4 (Z_to_bv 64 2)] /\ ro_cells usegs m 0x32dea8 [C4 (Z_to_bv 64 k)] /\ 0 <= k < 128
    /\ ro_cells usegs m (RATP + -88) [C8 (Z_to_bv 64 TSD_MAIN)]
    /\ ro_cells usegs m (TSD_MAIN + 8 * k) [C8 (Z_to_bv 64 MK)] /\ 0 < MK < 2 ^ 64
    /\ ro_cells usegs m (MK + 8 * 3) [C8 (Z_to_bv 64 SA)] /\ 0 < SA < 2 ^ 64
    /\ ro_cells usegs m SA (sa_hdr (Z_to_bv 64 1) pad tw ne (Z_to_bv 64 NODES)) /\ 0 < NODES < 2 ^ 64 /\ bv_unsigned ne <> 0
    /\ ro_cells usegs m NODES [C8 (Z_to_bv 64 E)].
Proof.
  intros m LBL E (od & pad & tw & ne & k & MK & SA & NODES & pm & psa & pn & pk & kd & LK
    & e_lbl & c_ic8 & c_ic32 & c_ic96 & c_once & c_key & r_k & c_tsdp & c_slot & r_mk & c_mk24 & r_sa
    & c_hdr & r_nodes & r_ne & c_nodes & _).
  exists od, pad, tw, ne, k, MK, SA, NODES, pm, psa, pn, pk, LK.
  exact (conj e_lbl (conj c_ic8 (conj c_ic32 (conj c_ic96 (conj (proj1 c_once) (conj (proj1 c_key)
    (conj r_k (conj (proj1 c_tsdp) (conj (proj1 c_slot) (conj r_mk (conj (proj1 c_mk24) (conj r_sa
    (conj (proj1 c_hdr) (conj r_nodes (conj r_ne (proj1 c_nodes)))))))))))))))).
Qed.

(* [comment removed for export] *)
Lemma libenv_exd_cells : forall m LBL E, libenv m LBL E ->
  exists (kd LK : Z) (pk : bptr),
       In (pk, LK, 40) LBL
    /\ ro_cells usegs m DC_S [C1 (Z_to_bv 8 1)] /\ ro_cells usegs m (DC_S + 4) [C4 (Z_to_bv 64 kd)] /\ 0 <= kd < 128
    /\ ro_cells usegs m (DC_S + 8) [C4 (Z_to_bv 64 2)] /\ ro_cells usegs m (DC_S + 12) [C4 (Z_to_bv 64 1)]
    /\ ro_cells usegs m (DC_S + 16) [C4 (Z_to_bv 64 2)] /\ ro_cells usegs m (DC_S + 20) [C4 (Z_to_bv 64 1)]
    /\ ro_cells usegs m (RATP + -88) [C8 (Z_to_bv 64 TSD_MAIN)]
    /\ ro_cells usegs m (TSD_MAIN + 8 * kd) [C8 (Z_to_bv 64 0)]
    /\ ro_cells usegs m DC_GLOBAL_LOCK [C8 (Z_to_bv 64 LK)] /\ 0 < LK /\ LK mod 4 = 0
    /\ rw_cells usegs m LK (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
    /\ ro_cells usegs m DC_IP12 [C8 (Z_to_bv 64 0)].
Proof.
  intros m LBL E ENV.
  destruct ENV as (od & pad & tw & ne & k & MK & SA & NODES & pm & psa & pn & pk & kd & LK
    & e_lbl & _ & _ & _ & _ & _ & _ & c_tsdp & _ & _ & _ & _ & _ & _ & _ & _
    & c_dc0 & c_dc4 & r_kd & c_dc8 & c_dc12 & c_dc16 & c_dc20 & c_dslot & c_glock & r_lk & r_lkal & c_mtx & c_ip12).
  assert (pk_in : In (pk, LK, 40) LBL) by (rewrite e_lbl; cbn [In]; tauto).
  exists kd, LK, pk.
  exact (conj pk_in (conj (proj1 c_dc0) (conj (proj1 c_dc4) (conj r_kd (conj (proj1 c_dc8) (conj (proj1 c_dc12)
    (conj (proj1 c_dc16) (conj (proj1 c_dc20) (conj (proj1 c_tsdp) (conj (proj1 c_dslot) (conj (proj1 c_glock)
    (conj r_lk (conj r_lkal (conj c_mtx (proj1 c_ip12))))))))))))))).
Qed.

End WithCeiling0.
