(* AsanCells: split VERBATIM from lib/B/AsanRT.v @ dmig 0260981d028, lines 1-6 (imports), 8-49 (constants and
   address predicates) and 77-87 (asan_cells), to keep asan_cf_cells (malloc_context_size = 1, toolchain N) and
   the rest of AsanRT.v (RT_* cells, asan_opt/cf/uw/real/im/exit/fs cells) out of the leaf closure (a Theorem Labs lane's
   decision 2026-10-28 20:25Z). Nothing is changed in the copied text. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0.
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

Definition CELL_K : Z := 0xa1338.
Definition UAR : Z := 0xa1340.
Definition INITED : Z := 0xa2018.
Definition REPLACE : Z := 0xa2019.
Definition CANPOISON : Z := 0xa0b9c.
Definition HIEND : Z := 0xa2020.
Definition MIDBEG : Z := 0xa2028.
Definition MIDEND : Z := 0xa2030.
Definition REAL_MEMCPY : Z := 0x9b160.
Definition REAL_MEMSET : Z := 0x9b168.
Definition MUSL_MEMCPY : Z := 0x92618.
Definition MUSL_MEMSET : Z := 0x92a1c.
Definition GOT_CELL_K : Z := 0x992e8.
Definition GOT_UAR : Z := 0x99340.
Definition GOT_REPLACE : Z := 0x99e50.
Definition GOT_HIEND : Z := 0x99300.
Definition GOT_MIDBEG : Z := 0x992f0.
Definition GOT_MIDEND : Z := 0x992f8.
Definition GOT_REAL_MEMSET : Z := 0x99308.

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
