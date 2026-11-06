(* Modified by Theorem Labs: copied from proofs/libreac/fuzz_decode/lib/A/AsanCells.v (origin/ossv/recipes 88154566652a) for reac-repacer/fuzz_uci's image A: module paths changed; every cell address and value measured on fuzz_uci.asan (the pinned image's .got and .data words, the unstripped twin's symbols); fuzz_decode's real_memset cell and its GOT word replaced by real_memchr (the memchr interceptor's REAL, which rp_uci_int's call reaches) and the GOT word of real_memcpy (the one __asan_memcpy reads). *)
(* AsanCells: the ASan shadow mapping (the toolchain's constants and address predicates) and asan_cells, the runtime
   cells of fuzz_uci.asan that the program's leaves read through the image view mrd, at their start-up values.
   Addresses (symbol of the unstripped twin; GOT words read from the pinned image's .got):
     CELL_K     0x9eff8  __asan_shadow_memory_dynamic_address          GOT_CELL_K       0x97020 -> 0x9eff8
     UAR        0x9f000  __asan_option_detect_stack_use_after_return  GOT_UAR          0x97078 -> 0x9f000
     INITED     0x9fcd8  __asan::asan_inited
     REPLACE    0x9fcd9  __asan::replace_intrin_cached                GOT_REPLACE      0x97b88 -> 0x9fcd9
     CANPOISON  0x9e85c  __asan::can_poison_memory
     HIEND      0x9fce0  __asan::kHighMemEnd                          GOT_HIEND        0x97038 -> 0x9fce0
     MIDBEG     0x9fce8  __asan::kMidMemBeg                           GOT_MIDBEG       0x97028 -> 0x9fce8
     MIDEND     0x9fcf0  __asan::kMidMemEnd                           GOT_MIDEND       0x97030 -> 0x9fcf0
     REAL_MEMCPY 0x98e78 __interception::real_memcpy = 0x90350        GOT_REAL_MEMCPY  0x97048 -> 0x98e78
     REAL_MEMCHR 0x98d40 __interception::real_memchr = 0x90254
   The GOT words and the two REAL cells are file-backed (.got, .data) and hold these values in the image; the other
   cells are .bss, written by start-up. Each row is a constant cell of the core's record (lib/A/AF0m.v Tfib_const_abs)
   with the same width and value. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import Mem.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import Img0.
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

Definition CELL_K : Z := 0x9eff8.
Definition UAR : Z := 0x9f000.
Definition INITED : Z := 0x9fcd8.
Definition REPLACE : Z := 0x9fcd9.
Definition CANPOISON : Z := 0x9e85c.
Definition HIEND : Z := 0x9fce0.
Definition MIDBEG : Z := 0x9fce8.
Definition MIDEND : Z := 0x9fcf0.
Definition REAL_MEMCPY : Z := 0x98e78.
Definition REAL_MEMCHR : Z := 0x98d40.
Definition MUSL_MEMCPY : Z := 0x90350.
Definition MUSL_MEMCHR : Z := 0x90254.
Definition GOT_CELL_K : Z := 0x97020.
Definition GOT_UAR : Z := 0x97078.
Definition GOT_REPLACE : Z := 0x97b88.
Definition GOT_HIEND : Z := 0x97038.
Definition GOT_MIDBEG : Z := 0x97028.
Definition GOT_MIDEND : Z := 0x97030.
Definition GOT_REAL_MEMCPY : Z := 0x97048.

Definition asan_cells (m : word -> option byte) : Prop :=
  bytes_at rsegs m CELL_K (le8 (wa ASAN_K)) /\ bytes_at rsegs m GOT_CELL_K (le8 (wa CELL_K))
  /\ bytes_at rsegs m INITED [Z_to_bv 8 1] /\ bytes_at rsegs m REPLACE [Z_to_bv 8 1]
  /\ bytes_at rsegs m GOT_REPLACE (le8 (wa REPLACE))
  /\ bytes_at rsegs m UAR (le4 (wa 1)) /\ bytes_at rsegs m GOT_UAR (le8 (wa UAR))
  /\ bytes_at rsegs m CANPOISON [Z_to_bv 8 1]
  /\ bytes_at rsegs m HIEND (le8 (wa 0x7fffffffffff)) /\ bytes_at rsegs m GOT_HIEND (le8 (wa HIEND))
  /\ bytes_at rsegs m MIDBEG (le8 (wa 0)) /\ bytes_at rsegs m GOT_MIDBEG (le8 (wa MIDBEG))
  /\ bytes_at rsegs m MIDEND (le8 (wa 0)) /\ bytes_at rsegs m GOT_MIDEND (le8 (wa MIDEND))
  /\ bytes_at rsegs m REAL_MEMCPY (le8 (wa MUSL_MEMCPY)) /\ bytes_at rsegs m REAL_MEMCHR (le8 (wa MUSL_MEMCHR))
  /\ bytes_at rsegs m GOT_REAL_MEMCPY (le8 (wa REAL_MEMCPY)).
