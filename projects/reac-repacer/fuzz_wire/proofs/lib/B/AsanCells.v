(* Modified by Theorem Labs: copied from this unit's lib/A/AsanCells.v (commit 8c3eb0365c8c; itself from proofs/libreac/fuzz_decode/lib/A/AsanCells.v at recipes commit 88154566652a) for reac-repacer/fuzz_uci's image B, as fuzz_decode's released lib/B/AsanCells.v twins its lib/A/AsanCells.v: module paths changed (Img0 is lib/B/Img0.v); every cell address and value measured on fuzz_uci.asan-ubsan (the pinned image's .got and .data words, the unstripped twin's symbols) and checked against the B core's record lib/B/YF0m.v Tfib_const_abs; the toolchain's shadow constants are unchanged. *)
(* AsanCells: the ASan shadow mapping (the toolchain's constants and address predicates) and asan_cells, the runtime
   cells of fuzz_wire.asan-ubsan that the program's leaves read through the image view mrd, at their start-up values.
   Addresses (symbol of the unstripped twin; GOT words read from the pinned image's .got):
     CELL_K     0xa07f8  __asan_shadow_memory_dynamic_address          GOT_CELL_K       0x98878 -> 0xa07f8
     UAR        0xa0800  __asan_option_detect_stack_use_after_return  GOT_UAR          0x988d0 -> 0xa0800
     INITED     0xa14d8  __asan::asan_inited
     REPLACE    0xa14d9  __asan::replace_intrin_cached                GOT_REPLACE      0x993e0 -> 0xa14d9
     CANPOISON  0xa005c  __asan::can_poison_memory
     HIEND      0xa14e0  __asan::kHighMemEnd                          GOT_HIEND        0x98890 -> 0xa14e0
     MIDBEG     0xa14e8  __asan::kMidMemBeg                           GOT_MIDBEG       0x98880 -> 0xa14e8
     MIDEND     0xa14f0  __asan::kMidMemEnd                           GOT_MIDEND       0x98888 -> 0xa14f0
     REAL_MEMCPY 0x9a6d8 __interception::real_memcpy = 0x91ba8        GOT_REAL_MEMCPY  0x988a0 -> 0x9a6d8
     REAL_MEMSET 0x9a6e0 __interception::real_memset = 0x91fac        GOT_REAL_MEMSET  0x98898 -> 0x9a6e0
     REAL_BCMP   0x9a598 __interception::real_bcmp = 0x91aa8
   The GOT words and the three REAL cells are file-backed (.got, .data) and hold these values in the image; the other
   cells are .bss, written by start-up. Each row is a constant cell of the B core's record (lib/B/YF0m.v Tfib_const_abs)
   with the same width and value. The program functions read only GOT_CELL_K and CELL_K (every function) and GOT_UAR
   and UAR (check_meter, check_read); the interceptors the program calls read others. REAL_MEMSET and GOT_REAL_MEMSET
   are kept so that both images state the same rows (image B links no __asan_memset). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import Mem.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition ASAN_K : Z := 0x7fff8000.
Definition LOWMEM_END : Z := 0x7fff8000.
Definition LOWSHADOW_END : Z := 0x8fff7000.
Definition HIGHSHADOW_BEG : Z := 0x2008fff7000.
Definition HIGHMEM_BEG : Z := 0x10007fff8000.
Definition APPMEM_END : Z := 0x800000000000.

Definition app_mem (a : Z) : Prop := (0 <= a < LOWMEM_END) \/ (HIGHMEM_BEG <= a < APPMEM_END).
Definition in_shadow (a : Z) : Prop := (LOWMEM_END <= a < LOWSHADOW_END) \/ (HIGHSHADOW_BEG <= a < HIGHMEM_BEG).
Definition shadow_addr (a : Z) : Z := a / 8 + ASAN_K.
Definition shadow_ok (a k : Z) : Prop := k = 0 \/ (a mod 8 < k /\ k <= 7).

Definition addr_byte (m : word -> option byte) (a : Z) : Prop :=
  app_mem a /\ exists b, mrd rsegs m (wa (shadow_addr a)) = Some b /\ shadow_ok a (bv_signed b).

Definition addressable (m : word -> option byte) (p n : Z) : Prop :=
  0 <= p /\ 0 <= n /\ p + n <= APPMEM_END /\ forall i, 0 <= i < n -> addr_byte m (p + i).

Definition end_in_app (p n : Z) : Prop := n = 0 \/ app_mem (p + n).

Definition shadow_rw (m : word -> option byte) : Prop :=
  forall a, in_shadow a -> wview rsegs m (wa a) <> None /\ exists b, mrd rsegs m (wa a) = Some b.

Definition CELL_K : Z := 0xa07f8.
Definition UAR : Z := 0xa0800.
Definition INITED : Z := 0xa14d8.
Definition REPLACE : Z := 0xa14d9.
Definition CANPOISON : Z := 0xa005c.
Definition HIEND : Z := 0xa14e0.
Definition MIDBEG : Z := 0xa14e8.
Definition MIDEND : Z := 0xa14f0.
Definition REAL_MEMCPY : Z := 0x9a6d8.
Definition REAL_MEMSET : Z := 0x9a6e0.
Definition REAL_BCMP : Z := 0x9a598.
Definition MUSL_MEMCPY : Z := 0x91ba8.
Definition MUSL_MEMSET : Z := 0x91fac.
Definition MUSL_BCMP : Z := 0x91aa8.
Definition GOT_CELL_K : Z := 0x98878.
Definition GOT_UAR : Z := 0x988d0.
Definition GOT_REPLACE : Z := 0x993e0.
Definition GOT_HIEND : Z := 0x98890.
Definition GOT_MIDBEG : Z := 0x98880.
Definition GOT_MIDEND : Z := 0x98888.
Definition GOT_REAL_MEMCPY : Z := 0x988a0.
Definition GOT_REAL_MEMSET : Z := 0x98898.

Definition asan_cells (m : word -> option byte) : Prop :=
  bytes_at rsegs m CELL_K (le8 (wa ASAN_K)) /\ bytes_at rsegs m GOT_CELL_K (le8 (wa CELL_K))
  /\ bytes_at rsegs m INITED [Z_to_bv 8 1] /\ bytes_at rsegs m REPLACE [Z_to_bv 8 1]
  /\ bytes_at rsegs m GOT_REPLACE (le8 (wa REPLACE))
  /\ bytes_at rsegs m UAR (le4 (wa 1)) /\ bytes_at rsegs m GOT_UAR (le8 (wa UAR))
  /\ bytes_at rsegs m CANPOISON [Z_to_bv 8 1]
  /\ bytes_at rsegs m HIEND (le8 (wa 0x7fffffffffff)) /\ bytes_at rsegs m GOT_HIEND (le8 (wa HIEND))
  /\ bytes_at rsegs m MIDBEG (le8 (wa 0)) /\ bytes_at rsegs m GOT_MIDBEG (le8 (wa MIDBEG))
  /\ bytes_at rsegs m MIDEND (le8 (wa 0)) /\ bytes_at rsegs m GOT_MIDEND (le8 (wa MIDEND))
  /\ bytes_at rsegs m REAL_MEMCPY (le8 (wa MUSL_MEMCPY)) /\ bytes_at rsegs m GOT_REAL_MEMCPY (le8 (wa REAL_MEMCPY))
  /\ bytes_at rsegs m REAL_MEMSET (le8 (wa MUSL_MEMSET)) /\ bytes_at rsegs m GOT_REAL_MEMSET (le8 (wa REAL_MEMSET))
  /\ bytes_at rsegs m REAL_BCMP (le8 (wa MUSL_BCMP)).
