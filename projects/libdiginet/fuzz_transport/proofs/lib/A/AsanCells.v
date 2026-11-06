(* AsanCells: the memory map constants of the ASan runtime, its address predicates, and the runtime cells of
   fuzz_transport.asan that the program reads (asan_cells): each cell by its symbol, each GOT word by the .got slot
   that holds the cell's address, each value as the record's constant cell (lib/A/AF0m.v Tfib_const_abs) states it. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0.
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

Definition CELL_K : Z := 0xac9f8.
Definition UAR : Z := 0xaca00.
Definition INITED : Z := 0xad6d8.
Definition REPLACE : Z := 0xad6d9.
Definition CANPOISON : Z := 0xac25c.
Definition HIEND : Z := 0xad6e0.
Definition MIDBEG : Z := 0xad6e8.
Definition MIDEND : Z := 0xad6f0.
Definition REAL_MEMCPY : Z := 0xa5ef0.
Definition REAL_MEMSET : Z := 0xa5ef8.
Definition MUSL_MEMCPY : Z := 0x9d210.
Definition MUSL_MEMSET : Z := 0x9d614.
Definition GOT_CELL_K : Z := 0xa4090.
Definition GOT_UAR : Z := 0xa40e8.
Definition GOT_REPLACE : Z := 0xa4bf8.
Definition GOT_HIEND : Z := 0xa40a8.
Definition GOT_MIDBEG : Z := 0xa4098.
Definition GOT_MIDEND : Z := 0xa40a0.
Definition GOT_REAL_MEMSET : Z := 0xa40b0.

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
