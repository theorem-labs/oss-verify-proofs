(* AsanCells: the ASan shadow mapping (the toolchain's constants and address predicates) and asan_cells, the runtime
   cells of fuzz_transport.asan-ubsan (41113a03c82f) that the program's leaves read through the image view mrd, at
   their start-up values. Image B's twin of lib/A/AsanCells.v: the same names, over lib/B/Img0.v rsegs.
   Addresses (symbol of the unstripped twin e217cb0a84f1; GOT words read from the pinned image's .got, equal in both):
     CELL_K      0xac678  __asan_shadow_memory_dynamic_address          GOT_CELL_K       0xa3cf0 -> 0xac678
     UAR         0xac680  __asan_option_detect_stack_use_after_return  GOT_UAR          0xa3d48 -> 0xac680
     INITED      0xad358  __asan::asan_inited
     REPLACE     0xad359  __asan::replace_intrin_cached                GOT_REPLACE      0xa4858 -> 0xad359
     CANPOISON   0xabedc  __asan::can_poison_memory
     HIEND       0xad360  __asan::kHighMemEnd                          GOT_HIEND        0xa3d08 -> 0xad360
     MIDBEG      0xad368  __asan::kMidMemBeg                           GOT_MIDBEG       0xa3cf8 -> 0xad368
     MIDEND      0xad370  __asan::kMidMemEnd                           GOT_MIDEND       0xa3d00 -> 0xad370
     REAL_MEMCPY 0xa5b50  __interception::real_memcpy = 0x9ce6c
     REAL_MEMSET 0xa5b58  __interception::real_memset = 0x9d270        GOT_REAL_MEMSET  0xa3d10 -> 0xa5b58
   MUSL_MEMCPY / MUSL_MEMSET are the twin's symbols memcpy (0x9ce6c) / memset (0x9d270). The GOT words and the two
   REAL cells are file-backed (.got, .data) and hold these values in the image; the other cells are .bss, written by
   start-up. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0.
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

Definition CELL_K : Z := 0xac678.
Definition UAR : Z := 0xac680.
Definition INITED : Z := 0xad358.
Definition REPLACE : Z := 0xad359.
Definition CANPOISON : Z := 0xabedc.
Definition HIEND : Z := 0xad360.
Definition MIDBEG : Z := 0xad368.
Definition MIDEND : Z := 0xad370.
Definition REAL_MEMCPY : Z := 0xa5b50.
Definition REAL_MEMSET : Z := 0xa5b58.
Definition MUSL_MEMCPY : Z := 0x9ce6c.
Definition MUSL_MEMSET : Z := 0x9d270.
Definition GOT_CELL_K : Z := 0xa3cf0.
Definition GOT_UAR : Z := 0xa3d48.
Definition GOT_REPLACE : Z := 0xa4858.
Definition GOT_HIEND : Z := 0xa3d08.
Definition GOT_MIDBEG : Z := 0xa3cf8.
Definition GOT_MIDEND : Z := 0xa3d00.
Definition GOT_REAL_MEMSET : Z := 0xa3d10.

Definition asan_cells (m : word -> option byte) : Prop :=
  bytes_at rsegs m CELL_K (le8 (wa ASAN_K)) /\ bytes_at rsegs m GOT_CELL_K (le8 (wa CELL_K))
  /\ bytes_at rsegs m INITED [Z_to_bv 8 1] /\ bytes_at rsegs m REPLACE [Z_to_bv 8 1]
  /\ bytes_at rsegs m GOT_REPLACE (le8 (wa REPLACE))
  /\ bytes_at rsegs m UAR (le4 (wa 1)) /\ bytes_at rsegs m GOT_UAR (le8 (wa UAR))
  /\ bytes_at rsegs m CANPOISON [Z_to_bv 8 1]
  /\ bytes_at rsegs m HIEND (le8 (wa 0x7fffffffffff)) /\ bytes_at rsegs m GOT_HIEND (le8 (wa HIEND))
  /\ bytes_at rsegs m MIDBEG (le8 (wa 0)) /\ bytes_at rsegs m GOT_MIDBEG (le8 (wa MIDBEG))
  /\ bytes_at rsegs m MIDEND (le8 (wa 0)) /\ bytes_at rsegs m GOT_MIDEND (le8 (wa MIDEND))
  /\ bytes_at rsegs m REAL_MEMCPY (le8 (wa MUSL_MEMCPY)) /\ bytes_at rsegs m REAL_MEMSET (le8 (wa MUSL_MEMSET))
  /\ bytes_at rsegs m GOT_REAL_MEMSET (le8 (wa REAL_MEMSET)).
