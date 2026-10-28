(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire ApBase.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem SFModel RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit R_cache_defs R_prim_defs R_sec_defs D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells ApRepDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApFrame.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require W_sct_list_free SctRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncP Require Import EncPure.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma cb_join2A : forall (m : mem) A a b bs1 bs2,
  rw_cells ctasegs m A [CB (Z.to_nat a) bs1] -> rw_cells ctasegs m (A + a) [CB (Z.to_nat b) bs2] -> 0 <= a -> 0 <= b ->
  rw_cells ctasegs m A [CB (Z.to_nat (a + b)) (bs1 ++ bs2)].
Proof.
  intros m A a b bs1 bs2 H1 H2 Ha Hb.
  pose proof H1 as [[W1 _] _]. pose proof H2 as [[W2 _] _]. cbn in W1, W2.
  assert (H : rw_cells ctasegs m A ([CB (Z.to_nat a) bs1] ++ [CB (Z.to_nat b) bs2])).
  { apply rw_cells_app_join; [exact H1|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact H2. }
  eapply (rw_cells_recast m A _ _ H).
  - cbn. rewrite length_app. repeat split; lia.
  - cbn. rewrite !app_nil_r. reflexivity.
  - cbn. lia.
Qed.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).

(* [comment removed for export] *)
Lemma sct_ok_of_repA : forall Σ OW LB m adr x, AHEAP Σ OW LB m -> sct_repA m LB adr x -> sct_ok adr x.
Proof.
  intros Σ OW LB m adr x HEAP (H1 & H1' & H2 & H3 & H4 & H5 & H6 & ND & VR & VN & HR & GR & TS & EL & OE & OS & OB).
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP, BnHeapA.ACEIL in C1, C2, C3.
  assert (ARR : forall q n, arr_repA m LB adr (Some (q, n)) -> 0 < adr q < 2^64 /\ 0 < n /\ adr q + n <= ACEIL).
  { intros q n (Hn & HIn & _). pose proof (AH_range_gen _ _ _ _ _ HEAP (in_or_app _ _ _ (or_intror HIn))) as (B1 & _ & B3 & B4 & B5).
    cbn [blk_addr blk_size fst snd] in B1, B4. unfold BnHeapA.ACEIL in B4 |- *. lia. }
  unfold sct_ok. split; [exact VR|]. split; [exact HR|]. split; [exact GR|].
  split. { intros q n E. rewrite E in H5. pose proof (ARR q n H5). unfold olen, MAX_SCT_SIZE in OS. rewrite E in OS. lia. }
  split. { intros q n E. rewrite E in H6. pose proof (ARR q n H6). lia. }
  split. { intros q E. rewrite E in H3. cbn [osz32 option_map] in H3. pose proof (ARR q 32 H3). lia. }
  unfold olen, MAX_SCT_SIZE in OE, OB, EL.
  split. { rewrite EL. destruct (sc_ext x) as [[q n]|]; [pose proof (proj1 H4); lia| lia]. }
  split. { rewrite SctRep.sc_bloblen_olen. unfold olen. destruct (sc_blob x) as [[q n]|]; [pose proof (proj1 H6); lia| lia]. }
  split. { intros q n E. rewrite E in H4. pose proof (ARR q n H4). lia. }
  split. { rewrite EL. destruct (sc_ext x) as [[q n]|]; reflexivity. }
  rewrite SctRep.sc_bloblen_olen. unfold olen. destruct (sc_blob x) as [[q n]|]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma arr_bytes : forall m LB adr q n, arr_repA m LB adr (Some (q, n)) ->
  exists bs, bytes_at ctasegs m (adr q) bs /\ length bs = Z.to_nat n /\ In (q, adr q, n) LB /\ 0 < n.
Proof.
  intros m LB adr q n (Hn & HIn & (bs & HC)). exists bs. pose proof HC as [[W B] _]. cbn in W, B. rewrite app_nil_r in B.
  split; [exact B|]. split; [lia|]. split; [exact HIn| exact Hn].
Qed.

End WithRT.
