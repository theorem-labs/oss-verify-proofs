(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocIface MallocInv_defs MallocInv_live MallocInv_ops MallocInv_ameta_iface MallocInv_ametax_iface MallocSureCap MallocSurePot.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition noroomX (dc db da dx M : Z) (A : astate) (h : VmMaps) : Prop :=
  exists A1 s1, WF A1 /\ VMok A1 (ms_vm s1) /\ sgrow dc db da A A1 h (ms_vm s1) /\
                lsum (a_xmaps A1) <= lsum (a_xmaps A) + dx /\
                (~ am_room A1 s1 \/
                 exists len, 0 < len <= M /\ len mod 4096 = 0 /\
                             vm_backed_bytes (ms_vm s1) + len <= vm_backed_bytes h + db /\
                             forall a, mmap_grant_ok MMrw (ms_vm s1) a len = false).

Lemma snoroom_noroomX : forall sp0 argv envp cb dc db da dx M A s,
  snoroom sp0 argv envp cb dc db da dx M A s -> noroomX dc db da dx M A (ms_vm s).
Proof.
  intros sp0 argv envp cb dc db da dx M A s (D1 & A1 & s1 & H1 & H2 & H3 & H4).
  exists A1, s1. split; [exact (is_wf _ _ _ _ _ _ (ii_is H1))|]. split; [exact (ii_vm H1)|].
  split; [exact H2|]. split; [exact H3 | exact H4].
Qed.

(* [comment removed for export] *)
Definition malloc_growX (n : Z) (A A' : astate) (h h' : VmMaps) : Prop :=
  sgrow 5 (malloc_db n) 4 A A' h h' /\
  (* [comment removed for export] *)
  pgrow (malloc_dp n) A A' h h'.
Definition malloc_noroomX (n : Z) (A : astate) (h : VmMaps) : Prop :=
  noroomX 5 (malloc_db n) 4 (n + 4115) (malloc_db n) A h.

Definition free_postX (A : astate) (p : word) (s : mstate) : unit -> mstate -> Prop :=
  fun _ s' => exists A', a_xmaps A' = [] /\
    minv A' (ms_mem s') (ms_vm s') /\ ms_lo s' = ms_lo s /\ ms_hi s' = ms_hi s /\
    mlive A' p = None /\ (forall q, q <> p -> mlive A' q = mlive A q) /\
    (forall a : word, ~ mowned A a -> ~ mowned A' a -> ~ errno_slot a -> ms_mem s' a = ms_mem s a) /\
    (forall q k i, mlive A' q = Some k -> 0 <= i < k -> ms_mem s' (at_ q i) = ms_mem s (at_ q i)) /\
    (forall a : word, ms_mem s a <> None -> mowned A a \/ ms_mem s' a <> None) /\
    vm_fixed (ms_vm s) (ms_vm s') /\ vm_live_bytes (ms_vm s') <= vm_live_bytes (ms_vm s) /\
    (* [comment removed for export] *)
    sgrow 0 0 0 A A' (ms_vm s) (ms_vm s').

Definition malloc_postX (A : astate) (n : Z) (s : mstate) : word -> mstate -> Prop :=
  fun res s' => exists A', a_xmaps A' = [] /\
    minv A' (ms_mem s') (ms_vm s') /\ ms_lo s' = ms_lo s /\ ms_hi s' = ms_hi s /\
    ( (res = Z_to_bv 64 0 /\ (forall q, mlive A' q = mlive A q))
      \/ (bv_unsigned res <> 0 /\ mlive A res = None /\ mlive A' res = Some n /\
          (forall q, q <> res -> mlive A' q = mlive A q) /\
          (forall i, 0 <= i < round16 n -> mowned A (at_ res i) \/ ms_mem s (at_ res i) = None) /\
          (zgroup A' (bv_unsigned res) -> forall i, 0 <= i < n -> ms_mem s' (at_ res i) = Some (Z_to_bv 8 0))) ) /\
    (forall a : word, ~ mowned A a -> ~ mowned A' a -> ~ errno_slot a -> ms_mem s' a = ms_mem s a) /\
    (forall q k i, mlive A q = Some k -> 0 <= i < k -> ms_mem s' (at_ q i) = ms_mem s (at_ q i)) /\
    (forall a : word, ms_mem s a <> None -> bv_unsigned a < IMG_HI \/ mowned A a \/ ms_mem s' a <> None) /\
    vm_fixed (ms_vm s) (ms_vm s') /\
    (* [comment removed for export] *)
    malloc_growX n A A' (ms_vm s) (ms_vm s') /\ (bv_unsigned res = 0 -> malloc_noroomX n A (ms_vm s)).

(* [comment removed for export] *)
Definition calloc_postX (A : astate) (n : Z) (s : mstate) : word -> mstate -> Prop :=
  fun res s' => exists A', a_xmaps A' = [] /\
    minv A' (ms_mem s') (ms_vm s') /\ ms_lo s' = ms_lo s /\ ms_hi s' = ms_hi s /\
    ( (res = Z_to_bv 64 0 /\ (forall q, mlive A' q = mlive A q))
      \/ (bv_unsigned res <> 0 /\ mlive A res = None /\ mlive A' res = Some n /\
          (forall q, q <> res -> mlive A' q = mlive A q) /\
          (forall i, 0 <= i < round16 n -> mowned A (at_ res i) \/ ms_mem s (at_ res i) = None) /\
          (forall i, 0 <= i < n -> ms_mem s' (at_ res i) = Some (Z_to_bv 8 0))) ) /\
    (forall a : word, ~ mowned A a -> ~ mowned A' a -> ~ errno_slot a -> ms_mem s' a = ms_mem s a) /\
    (forall q k i, mlive A q = Some k -> 0 <= i < k -> ms_mem s' (at_ q i) = ms_mem s (at_ q i)) /\
    (forall a : word, ms_mem s a <> None -> bv_unsigned a < IMG_HI \/ mowned A a \/ ms_mem s' a <> None) /\
    vm_fixed (ms_vm s) (ms_vm s') /\
    (* [comment removed for export] *)
    malloc_growX n A A' (ms_vm s) (ms_vm s') /\ (bv_unsigned res = 0 -> malloc_noroomX n A (ms_vm s)).

(* [comment removed for export] *)
Definition replaced_clear (m : word -> option byte) : Prop :=
  forall a : word, bv_unsigned A_MALLOC_REPLACED <= bv_unsigned a < bv_unsigned A_MALLOC_REPLACED + 4 -> m a = None.

Lemma free_postX_post : forall A p s r s', free_postX A p s r s' -> free_post A p s r s'.
Proof.
  intros A p s r s' (A' & _ & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & _). exists A'.
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 H10))))))))).
Qed.

Lemma malloc_postX_post : forall A n s res s', malloc_postX A n s res s' -> malloc_post A n s res s'.
Proof.
  intros A n s res s' (A' & _ & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _ & _). exists A'.
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 H8))))))).
Qed.

End WithLayout.
