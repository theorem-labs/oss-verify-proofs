(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim Hoare StoreOk MmapSim AllocSim ShapeAlg PureModel VmLedger AllocIface AsanCeil.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require Import RefStep.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocTree MallocOps MallocShape.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Section WithLayout.
Context {fx : FPState} {ML : MallocLayout}.

(* [comment removed for export] *)
Definition getmeta_stmt : Prop :=
  forall md regs mm rom (s : mstate) (p sp ret : word)
         (P : word -> mstate -> Prop) (L : word -> mstate -> TSet),
  md_pure md -> ms_vm s = m_vmmaps md -> magree s mm ->
  getr regs 2 = sp -> bv_unsigned sp mod 16 = 0 ->
  0 <= ms_lo s -> ms_lo s <= bv_unsigned sp - 0 -> bv_unsigned sp <= ms_hi s -> ms_hi s <= 2^64 ->
  wtop s ->
  (forall a, bv_unsigned sp - 0 <= bv_unsigned a < bv_unsigned sp -> mm a <> None) ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = A_TP -> getr regs 10 = p ->
  tsafe (m_get_meta p s) P ->
  (forall r s' mm' regs',
     P r s' -> magree s' mm' -> ms_lo s' = ms_lo s -> ms_hi s' = ms_hi s ->
     alloc_top (ms_vm s') = alloc_top (ms_vm s) ->
     getr regs' 10 = r -> getr regs' 2 = sp ->
     (forall x, callee_saved x -> getr regs' x = getr regs x) ->
     (forall a, ms_lo s <= bv_unsigned a < ms_hi s ->
                ~ (bv_unsigned sp - 0 <= bv_unsigned a < bv_unsigned sp) -> mm' a = mm a) ->
     (forall a, bv_unsigned sp - 0 <= bv_unsigned a < bv_unsigned sp -> mm' a <> None) ->
     realizes ml_segs (mkCfg (mkst regs' ret mm' rom) (with_vmmaps (ms_vm s') md)) (L r s')) ->
  realizes ml_segs (mkCfg (mkst regs PC_GET_META mm rom) md) (tshape (m_get_meta p s) L).

(* [comment removed for export] *)
Definition enframe_stmt : Prop :=
  forall md regs mm rom (s : mstate) (g idx n ctr sp ret : word)
         (P : word -> mstate -> Prop) (L : word -> mstate -> TSet),
  md_pure md -> ms_vm s = m_vmmaps md -> magree s mm ->
  getr regs 2 = sp -> bv_unsigned sp mod 16 = 0 ->
  0 <= ms_lo s -> ms_lo s <= bv_unsigned sp - 0 -> bv_unsigned sp <= ms_hi s -> ms_hi s <= 2^64 ->
  wtop s ->
  (forall a, bv_unsigned sp - 0 <= bv_unsigned a < bv_unsigned sp -> mm a <> None) ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = A_TP ->
  getr regs 10 = g -> getr regs 11 = idx -> getr regs 12 = n -> getr regs 13 = ctr ->
  tsafe (m_enframe g idx n ctr s) P ->
  (forall r s' mm' regs',
     P r s' -> magree s' mm' -> ms_lo s' = ms_lo s -> ms_hi s' = ms_hi s ->
     alloc_top (ms_vm s') = alloc_top (ms_vm s) ->
     getr regs' 10 = r -> getr regs' 2 = sp ->
     (forall x, callee_saved x -> getr regs' x = getr regs x) ->
     (forall a, ms_lo s <= bv_unsigned a < ms_hi s ->
                ~ (bv_unsigned sp - 0 <= bv_unsigned a < bv_unsigned sp) -> mm' a = mm a) ->
     (forall a, bv_unsigned sp - 0 <= bv_unsigned a < bv_unsigned sp -> mm' a <> None) ->
     realizes ml_segs (mkCfg (mkst regs' ret mm' rom) (with_vmmaps (ms_vm s') md)) (L r s')) ->
  realizes ml_segs (mkCfg (mkst regs PC_ENFRAME mm rom) md) (tshape (m_enframe g idx n ctr s) L).

(* [comment removed for export] *)
Definition munmap_stmt : Prop :=
  forall md regs mm rom (s : mstate) (addr len sp ret : word)
         (P : word -> mstate -> Prop) (L : word -> mstate -> TSet),
  md_pure md -> ms_vm s = m_vmmaps md -> magree s mm ->
  getr regs 2 = sp -> bv_unsigned sp mod 16 = 0 ->
  0 <= ms_lo s -> ms_lo s <= bv_unsigned sp - 32 -> bv_unsigned sp <= ms_hi s -> ms_hi s <= 2^64 ->
  wtop s ->
  (forall a, bv_unsigned sp - 32 <= bv_unsigned a < bv_unsigned sp -> mm a <> None) ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = A_TP ->
  getr regs 10 = addr -> getr regs 11 = len ->
  tsafe (sys_munmap addr len s) P ->
  (forall r s' mm' regs',
     P r s' -> magree s' mm' -> ms_lo s' = ms_lo s -> ms_hi s' = ms_hi s ->
     alloc_top (ms_vm s') = alloc_top (ms_vm s) ->
     getr regs' 10 = r -> getr regs' 2 = sp ->
     (forall x, callee_saved x -> getr regs' x = getr regs x) ->
     (forall a, ms_lo s <= bv_unsigned a < ms_hi s ->
                ~ (bv_unsigned sp - 32 <= bv_unsigned a < bv_unsigned sp) -> mm' a = mm a) ->
     (forall a, bv_unsigned sp - 32 <= bv_unsigned a < bv_unsigned sp -> mm' a <> None) ->
     (forall x, wreg [10;11;17]%Z x = false -> getr regs' x = getr regs x) ->
     realizes ml_segs (mkCfg (mkst regs' ret mm' rom) (with_vmmaps (ms_vm s') md)) (L r s')) ->
  realizes ml_segs (mkCfg (mkst regs PC_MUNMAP mm rom) md) (tshape (sys_munmap addr len s) L).

(* [comment removed for export] *)
Definition mmap_prot (k : mmkind) : Z := match k with MMrw => 3 | MMnone => 0 end.

Definition mmap_stmt (k : mmkind) : Prop :=
  forall md regs mm rom (s : mstate) (len sp ret : word)
         (P : word -> mstate -> Prop) (L : word -> mstate -> TSet),
  md_pure md -> ms_vm s = m_vmmaps md -> magree s mm ->
  getr regs 2 = sp -> bv_unsigned sp mod 16 = 0 ->
  0 <= ms_lo s -> ms_lo s <= bv_unsigned sp - 80 -> bv_unsigned sp <= ms_hi s -> ms_hi s <= 2^64 ->
  wtop s ->
  (forall a, bv_unsigned sp - 80 <= bv_unsigned a < bv_unsigned sp -> mm a <> None) ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = A_TP ->
  getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = len -> bv_unsigned (getr regs 12) = mmap_prot k ->
  getr regs 13 = Z_to_bv 64 34 -> getr regs 14 = Z_to_bv 64 18446744073709551615 -> getr regs 15 = Z_to_bv 64 0 ->
  tsafe (sys_mmap k len s) P ->
  (forall r s' mm' regs',
     P r s' -> magree s' mm' -> ms_lo s' = ms_lo s -> ms_hi s' = ms_hi s ->
     alloc_top (ms_vm s') = alloc_top (ms_vm s) ->
     getr regs' 10 = r -> getr regs' 2 = sp ->
     (forall x, callee_saved x -> getr regs' x = getr regs x) ->
     (forall a, ms_lo s <= bv_unsigned a < ms_hi s ->
                ~ (bv_unsigned sp - 80 <= bv_unsigned a < bv_unsigned sp) -> mm' a = mm a) ->
     (forall a, bv_unsigned sp - 80 <= bv_unsigned a < bv_unsigned sp -> mm' a <> None) ->
     (forall x, wreg [5;10;11;16;17]%Z x = false -> getr regs' x = getr regs x) ->
     realizes ml_segs (mkCfg (mkst regs' ret mm' rom) (with_vmmaps (ms_vm s') md)) (L r s')) ->
  realizes ml_segs (mkCfg (mkst regs PC_MMAP mm rom) md) (tshape (sys_mmap k len s) L).

(* [comment removed for export] *)
Definition mmap_fixed_stmt : Prop :=
  forall md regs mm rom (s : mstate) (addr len sp ret : word)
         (P : word -> mstate -> Prop) (L : word -> mstate -> TSet),
  md_pure md -> ms_vm s = m_vmmaps md -> magree s mm ->
  getr regs 2 = sp -> bv_unsigned sp mod 16 = 0 ->
  0 <= ms_lo s -> ms_lo s <= bv_unsigned sp - 80 -> bv_unsigned sp <= ms_hi s -> ms_hi s <= 2^64 ->
  wtop s ->
  (forall a, bv_unsigned sp - 80 <= bv_unsigned a < bv_unsigned sp -> mm a <> None) ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = A_TP ->
  getr regs 10 = addr -> getr regs 11 = len -> getr regs 12 = Z_to_bv 64 0 ->
  getr regs 13 = Z_to_bv 64 50 -> getr regs 14 = Z_to_bv 64 18446744073709551615 -> getr regs 15 = Z_to_bv 64 0 ->
  tsafe (sys_mmap_fixed_none addr len s) P ->
  (forall r s' mm' regs',
     P r s' -> magree s' mm' -> ms_lo s' = ms_lo s -> ms_hi s' = ms_hi s ->
     alloc_top (ms_vm s') = alloc_top (ms_vm s) ->
     getr regs' 10 = r -> getr regs' 2 = sp ->
     (forall x, callee_saved x -> getr regs' x = getr regs x) ->
     (forall a, ms_lo s <= bv_unsigned a < ms_hi s ->
                ~ (bv_unsigned sp - 80 <= bv_unsigned a < bv_unsigned sp) -> mm' a = mm a) ->
     (forall a, bv_unsigned sp - 80 <= bv_unsigned a < bv_unsigned sp -> mm' a <> None) ->
     (forall x, wreg [5;10;11;16;17]%Z x = false -> getr regs' x = getr regs x) ->
     realizes ml_segs (mkCfg (mkst regs' ret mm' rom) (with_vmmaps (ms_vm s') md)) (L r s')) ->
  realizes ml_segs (mkCfg (mkst regs PC_MMAP mm rom) md) (tshape (sys_mmap_fixed_none addr len s) L).

(* [comment removed for export] *)
Definition mprotect_stmt : Prop :=
  forall md regs mm rom (s : mstate) (addr len sp ret : word) (pgbs : list byte)
         (P : word -> mstate -> Prop) (L : word -> mstate -> TSet),
  md_pure md -> ms_vm s = m_vmmaps md -> magree s mm ->
  getr regs 2 = sp -> bv_unsigned sp mod 16 = 0 ->
  0 <= ms_lo s -> ms_lo s <= bv_unsigned sp - 32 -> bv_unsigned sp <= ms_hi s -> ms_hi s <= 2^64 ->
  wtop s ->
  (forall a, bv_unsigned sp - 32 <= bv_unsigned a < bv_unsigned sp -> mm a <> None) ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = A_TP ->
  getr regs 10 = addr -> getr regs 11 = len -> getr regs 12 = Z_to_bv 64 3 ->
  rdn ml_segs mm A_PAGE_SIZE 8 = Some pgbs -> bytes_le_to_Z pgbs = 4096 ->
  tsafe (sys_mprotect_rw addr len s) P ->
  (forall r s' mm' regs',
     P r s' -> magree s' mm' -> ms_lo s' = ms_lo s -> ms_hi s' = ms_hi s ->
     alloc_top (ms_vm s') = alloc_top (ms_vm s) ->
     getr regs' 10 = r -> getr regs' 2 = sp ->
     (forall x, callee_saved x -> getr regs' x = getr regs x) ->
     (forall a, ms_lo s <= bv_unsigned a < ms_hi s ->
                ~ (bv_unsigned sp - 32 <= bv_unsigned a < bv_unsigned sp) -> mm' a = mm a) ->
     (forall a, bv_unsigned sp - 32 <= bv_unsigned a < bv_unsigned sp -> mm' a <> None) ->
     (forall x, wreg [10;11;13;14;17]%Z x = false -> getr regs' x = getr regs x) ->
     realizes ml_segs (mkCfg (mkst regs' ret mm' rom) (with_vmmaps (ms_vm s') md)) (L r s')) ->
  realizes ml_segs (mkCfg (mkst regs PC_MPROTECT mm rom) md) (tshape (sys_mprotect_rw addr len s) L).

(* [comment removed for export] *)
Definition ntfree_stmt : Prop :=
  forall md regs mm rom (s : mstate) (fuel : nat) (g i sp ret : word)
         (P : word * word -> mstate -> Prop) (L : word * word -> mstate -> TSet),
  md_pure md -> ms_vm s = m_vmmaps md -> magree s mm ->
  getr regs 2 = sp -> bv_unsigned sp mod 16 = 0 ->
  0 <= ms_lo s -> ms_lo s <= bv_unsigned sp - 96 * Z.of_nat fuel -> bv_unsigned sp <= ms_hi s -> ms_hi s <= 2^64 ->
  wtop s ->
  (forall a, bv_unsigned sp - 96 * Z.of_nat fuel <= bv_unsigned a < bv_unsigned sp -> mm a <> None) ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = A_TP ->
  getr regs 10 = g -> getr regs 11 = i ->
  tsafe (m_nontrivial_free fuel g i s) P ->
  (forall r s' mm' regs',
     P r s' -> magree s' mm' -> ms_lo s' = ms_lo s -> ms_hi s' = ms_hi s ->
     alloc_top (ms_vm s') = alloc_top (ms_vm s) ->
     getr regs' 10 = fst r ->
     getr regs' 11 = snd r ->
     getr regs' 2 = sp ->
     (forall x, callee_saved x -> getr regs' x = getr regs x) ->
     (forall a, ms_lo s <= bv_unsigned a < ms_hi s ->
                ~ (bv_unsigned sp - 96 * Z.of_nat fuel <= bv_unsigned a < bv_unsigned sp) -> mm' a = mm a) ->
     (forall a, bv_unsigned sp - 96 * Z.of_nat fuel <= bv_unsigned a < bv_unsigned sp -> mm' a <> None) ->
     realizes ml_segs (mkCfg (mkst regs' ret mm' rom) (with_vmmaps (ms_vm s') md)) (L r s')) ->
  realizes ml_segs (mkCfg (mkst regs PC_NTFREE mm rom) md) (tshape (m_nontrivial_free fuel g i s) L).

(* [comment removed for export] *)
Definition free_stmt : Prop :=
  forall md regs mm rom (s : mstate) (p sp ret : word)
         (P : unit -> mstate -> Prop) (L : unit -> mstate -> TSet),
  md_pure md -> ms_vm s = m_vmmaps md -> magree s mm ->
  getr regs 2 = sp -> bv_unsigned sp mod 16 = 0 ->
  0 <= ms_lo s -> ms_lo s <= bv_unsigned sp - ALLOC_STACK -> bv_unsigned sp <= ms_hi s -> ms_hi s <= 2^64 ->
  wtop s ->
  (forall a, bv_unsigned sp - ALLOC_STACK <= bv_unsigned a < bv_unsigned sp -> mm a <> None) ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = A_TP ->
  getr regs 10 = p ->
  tsafe (m_free p s) P ->
  (forall r s' mm' regs',
     P r s' -> magree s' mm' -> ms_lo s' = ms_lo s -> ms_hi s' = ms_hi s ->
     alloc_top (ms_vm s') = alloc_top (ms_vm s) ->
     getr regs' 2 = sp ->
     (forall x, callee_saved x -> getr regs' x = getr regs x) ->
     (forall a, ms_lo s <= bv_unsigned a < ms_hi s ->
                ~ (bv_unsigned sp - ALLOC_STACK <= bv_unsigned a < bv_unsigned sp) -> mm' a = mm a) ->
     (forall a, bv_unsigned sp - ALLOC_STACK <= bv_unsigned a < bv_unsigned sp -> mm' a <> None) ->
     realizes ml_segs (mkCfg (mkst regs' ret mm' rom) (with_vmmaps (ms_vm s') md)) (L r s')) ->
  realizes ml_segs (mkCfg (mkst regs PC_FREE mm rom) md) (tshape (m_free p s) L).

(* [comment removed for export] *)
Definition alloc_slot_D (fuel : nat) : Z := 144 * Z.of_nat fuel + 144.

(* [comment removed for export] *)
Definition alloc_meta_stmt : Prop :=
  forall md regs mm rom (s : mstate) (sp ret : word)
         (P : word -> mstate -> Prop) (L : word -> mstate -> TSet),
  md_pure md -> ms_vm s = m_vmmaps md -> magree s mm ->
  getr regs 2 = sp -> bv_unsigned sp mod 16 = 0 ->
  0 <= ms_lo s -> ms_lo s <= bv_unsigned sp - 144 -> bv_unsigned sp <= ms_hi s -> ms_hi s <= 2^64 ->
  wtop s ->
  (forall a, bv_unsigned sp - 144 <= bv_unsigned a < bv_unsigned sp -> mm a <> None) ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = A_TP ->
  tsafe (m_alloc_meta (at_ sp (-64)) s) P ->
  (forall r s' mm' regs',
     P r s' -> magree s' mm' -> ms_lo s' = ms_lo s -> ms_hi s' = ms_hi s ->
     alloc_top (ms_vm s') = alloc_top (ms_vm s) ->
     getr regs' 10 = r ->
     getr regs' 2 = sp ->
     (forall x, callee_saved x -> getr regs' x = getr regs x) ->
     (forall a, ms_lo s <= bv_unsigned a < ms_hi s ->
                ~ (bv_unsigned sp - 144 <= bv_unsigned a < bv_unsigned sp) -> mm' a = mm a) ->
     (forall a, bv_unsigned sp - 144 <= bv_unsigned a < bv_unsigned sp -> mm' a <> None) ->
     realizes ml_segs (mkCfg (mkst regs' ret mm' rom) (with_vmmaps (ms_vm s') md)) (L r s')) ->
  realizes ml_segs (mkCfg (mkst regs PC_ALLOC_META mm rom) md) (tshape (m_alloc_meta (at_ sp (-64)) s) L).

(* [comment removed for export] *)
Definition alloc_slot_stmt : Prop :=
  forall md regs mm rom (s : mstate) (fuel : nat) (sc req sp ret : word)
         (P : word -> mstate -> Prop) (L : word -> mstate -> TSet),
  md_pure md -> ms_vm s = m_vmmaps md -> magree s mm ->
  getr regs 2 = sp -> bv_unsigned sp mod 16 = 0 ->
  0 <= ms_lo s -> ms_lo s <= bv_unsigned sp - alloc_slot_D fuel -> bv_unsigned sp <= ms_hi s -> ms_hi s <= 2^64 ->
  wtop s ->
  (forall a, bv_unsigned sp - alloc_slot_D fuel <= bv_unsigned a < bv_unsigned sp -> mm a <> None) ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = A_TP ->
  getr regs 10 = sc -> getr regs 11 = req ->
  tsafe (m_alloc_slot fuel (at_ sp (-144)) sc req s) P ->
  (forall r s' mm' regs',
     P r s' -> magree s' mm' -> ms_lo s' = ms_lo s -> ms_hi s' = ms_hi s ->
     alloc_top (ms_vm s') = alloc_top (ms_vm s) ->
     getr regs' 10 = r ->
     getr regs' 2 = sp ->
     (forall x, callee_saved x -> getr regs' x = getr regs x) ->
     (forall a, ms_lo s <= bv_unsigned a < ms_hi s ->
                ~ (bv_unsigned sp - alloc_slot_D fuel <= bv_unsigned a < bv_unsigned sp) -> mm' a = mm a) ->
     (forall a, bv_unsigned sp - alloc_slot_D fuel <= bv_unsigned a < bv_unsigned sp -> mm' a <> None) ->
     realizes ml_segs (mkCfg (mkst regs' ret mm' rom) (with_vmmaps (ms_vm s') md)) (L r s')) ->
  realizes ml_segs (mkCfg (mkst regs PC_ALLOC_SLOT mm rom) md) (tshape (m_alloc_slot fuel (at_ sp (-144)) sc req s) L).

(* [comment removed for export] *)
Definition malloc_stmt : Prop :=
  forall md regs mm rom (s : mstate) (n sp ret : word)
         (P : word -> mstate -> Prop) (L : word -> mstate -> TSet),
  md_pure md -> ms_vm s = m_vmmaps md -> magree s mm ->
  getr regs 2 = sp -> bv_unsigned sp mod 16 = 0 ->
  0 <= ms_lo s -> ms_lo s <= bv_unsigned sp - ALLOC_STACK -> bv_unsigned sp <= ms_hi s -> ms_hi s <= 2^64 ->
  wtop s ->
  (forall a, bv_unsigned sp - ALLOC_STACK <= bv_unsigned a < bv_unsigned sp -> mm a <> None) ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = A_TP ->
  getr regs 10 = n ->
  tsafe (m_malloc (at_ sp (-48)) n s) P ->
  (forall r s' mm' regs',
     P r s' -> magree s' mm' -> ms_lo s' = ms_lo s -> ms_hi s' = ms_hi s ->
     alloc_top (ms_vm s') = alloc_top (ms_vm s) ->
     getr regs' 10 = r ->
     getr regs' 2 = sp ->
     (forall x, callee_saved x -> getr regs' x = getr regs x) ->
     (forall a, ms_lo s <= bv_unsigned a < ms_hi s ->
                ~ (bv_unsigned sp - ALLOC_STACK <= bv_unsigned a < bv_unsigned sp) -> mm' a = mm a) ->
     (forall a, bv_unsigned sp - ALLOC_STACK <= bv_unsigned a < bv_unsigned sp -> mm' a <> None) ->
     realizes ml_segs (mkCfg (mkst regs' ret mm' rom) (with_vmmaps (ms_vm s') md)) (L r s')) ->
  realizes ml_segs (mkCfg (mkst regs PC_MALLOC mm rom) md) (tshape (m_malloc (at_ sp (-48)) n s) L).

(* [comment removed for export] *)
Definition allzerop_stmt : Prop :=
  forall md regs mm rom (s : mstate) (p sp ret : word)
         (P : word -> mstate -> Prop) (L : word -> mstate -> TSet),
  md_pure md -> ms_vm s = m_vmmaps md -> magree s mm ->
  getr regs 2 = sp -> bv_unsigned sp mod 16 = 0 ->
  0 <= ms_lo s -> ms_lo s <= bv_unsigned sp - 0 -> bv_unsigned sp <= ms_hi s -> ms_hi s <= 2^64 ->
  wtop s ->
  (forall a, bv_unsigned sp - 0 <= bv_unsigned a < bv_unsigned sp -> mm a <> None) ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = A_TP -> getr regs 10 = p ->
  tsafe (m_allzerop p s) P ->
  (forall r s' mm' regs',
     P r s' -> magree s' mm' -> ms_lo s' = ms_lo s -> ms_hi s' = ms_hi s ->
     alloc_top (ms_vm s') = alloc_top (ms_vm s) ->
     getr regs' 10 = r -> getr regs' 2 = sp ->
     (forall x, callee_saved x -> getr regs' x = getr regs x) ->
     (forall a, ms_lo s <= bv_unsigned a < ms_hi s ->
                ~ (bv_unsigned sp - 0 <= bv_unsigned a < bv_unsigned sp) -> mm' a = mm a) ->
     (forall a, bv_unsigned sp - 0 <= bv_unsigned a < bv_unsigned sp -> mm' a <> None) ->
     realizes ml_segs (mkCfg (mkst regs' ret mm' rom) (with_vmmaps (ms_vm s') md)) (L r s')) ->
  realizes ml_segs (mkCfg (mkst regs PC_ALLZEROP mm rom) md) (tshape (m_allzerop p s) L).

(* [comment removed for export] *)
Definition memset0_stmt : Prop :=
  forall md regs mm rom (s : mstate) (d n sp ret : word)
         (P : word -> mstate -> Prop) (L : word -> mstate -> TSet),
  md_pure md -> ms_vm s = m_vmmaps md -> magree s mm ->
  getr regs 2 = sp -> bv_unsigned sp mod 16 = 0 ->
  0 <= ms_lo s -> ms_lo s <= bv_unsigned sp - 0 -> bv_unsigned sp <= ms_hi s -> ms_hi s <= 2^64 ->
  wtop s ->
  (forall a, bv_unsigned sp - 0 <= bv_unsigned a < bv_unsigned sp -> mm a <> None) ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = A_TP ->
  getr regs 10 = d -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = n ->
  tsafe (m_memset0 d n s) P ->
  (forall r s' mm' regs',
     P r s' -> magree s' mm' -> ms_lo s' = ms_lo s -> ms_hi s' = ms_hi s ->
     alloc_top (ms_vm s') = alloc_top (ms_vm s) ->
     getr regs' 10 = r -> getr regs' 2 = sp ->
     (forall x, callee_saved x -> getr regs' x = getr regs x) ->
     (forall a, ms_lo s <= bv_unsigned a < ms_hi s ->
                ~ (bv_unsigned sp - 0 <= bv_unsigned a < bv_unsigned sp) -> mm' a = mm a) ->
     (forall a, bv_unsigned sp - 0 <= bv_unsigned a < bv_unsigned sp -> mm' a <> None) ->
     realizes ml_segs (mkCfg (mkst regs' ret mm' rom) (with_vmmaps (ms_vm s') md)) (L r s')) ->
  realizes ml_segs (mkCfg (mkst regs PC_MEMSET mm rom) md) (tshape (m_memset0 d n s) L).

(* [comment removed for export] *)
Definition CALLOC_D : Z := ALLOC_STACK + 32.

(* [comment removed for export] *)
Definition calloc_stmt : Prop :=
  forall md regs mm rom (s : mstate) (fuel : nat) (m n sp ret : word)
         (P : word -> mstate -> Prop) (L : word -> mstate -> TSet),
  md_pure md -> ms_vm s = m_vmmaps md -> magree s mm ->
  getr regs 2 = sp -> bv_unsigned sp mod 16 = 0 ->
  0 <= ms_lo s -> ms_lo s <= bv_unsigned sp - CALLOC_D -> bv_unsigned sp <= ms_hi s -> ms_hi s <= 2^64 ->
  wtop s ->
  (forall a, bv_unsigned sp - CALLOC_D <= bv_unsigned a < bv_unsigned sp -> mm a <> None) ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = A_TP ->
  getr regs 10 = m -> getr regs 11 = n ->
  tsafe (m_calloc fuel (at_ sp (-32)) m n s) P ->
  (forall r s' mm' regs',
     P r s' -> magree s' mm' -> ms_lo s' = ms_lo s -> ms_hi s' = ms_hi s ->
     alloc_top (ms_vm s') = alloc_top (ms_vm s) ->
     getr regs' 10 = r ->
     getr regs' 2 = sp ->
     (forall x, callee_saved x -> getr regs' x = getr regs x) ->
     (forall a, ms_lo s <= bv_unsigned a < ms_hi s ->
                ~ (bv_unsigned sp - CALLOC_D <= bv_unsigned a < bv_unsigned sp) -> mm' a = mm a) ->
     (forall a, bv_unsigned sp - CALLOC_D <= bv_unsigned a < bv_unsigned sp -> mm' a <> None) ->
     realizes ml_segs (mkCfg (mkst regs' ret mm' rom) (with_vmmaps (ms_vm s') md)) (L r s')) ->
  realizes ml_segs (mkCfg (mkst regs PC_CALLOC mm rom) md) (tshape (m_calloc fuel (at_ sp (-32)) m n s) L).

End WithLayout.
