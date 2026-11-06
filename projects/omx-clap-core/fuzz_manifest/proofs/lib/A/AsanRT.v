From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import Img0.
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

Definition CELL_K : Z := 0xa1d78.
Definition UAR : Z := 0xa1d80.
Definition INITED : Z := 0xa2a58.
Definition REPLACE : Z := 0xa2a59.
Definition CANPOISON : Z := 0xa15dc.
Definition HIEND : Z := 0xa2a60.
Definition MIDBEG : Z := 0xa2a68.
Definition MIDEND : Z := 0xa2a70.
Definition REAL_MEMCPY : Z := 0x9b840.
Definition REAL_MEMSET : Z := 0x9b848.
Definition MUSL_MEMCPY : Z := 0x925a4.
Definition MUSL_MEMSET : Z := 0x929a8.
Definition GOT_CELL_K : Z := 0x999b0.
Definition GOT_UAR : Z := 0x99a08.
Definition GOT_REPLACE : Z := 0x9a518.
Definition GOT_HIEND : Z := 0x999c8.
Definition GOT_MIDBEG : Z := 0x999b8.
Definition GOT_MIDEND : Z := 0x999c0.
Definition GOT_REAL_MEMSET : Z := 0x999d0.
Definition RT_LO : Z := 0x999b0.
Definition RT_HI : Z := 0xa2a78.
Definition RT_AF : Z := 0x9f578.
Definition RT_GOT_AF : Z := 0x999a8.
Definition RT_VERB : Z := 0x131818.
Definition RT_GOT_VERB : Z := 0x99a00.
Definition RT_CF : Z := 0x1338a8.
Definition RT_GOT_CF : Z := 0x999a0.
Definition RT_TSDI : Z := 0xa15e0.
Definition RT_TSDK : Z := 0xa15e4.
Definition RT_PGSZ : Z := 0x131820.
Definition RT_TSDMAIN : Z := 0x5f6118.
Definition RT_BTLS : Z := 0x5d4ca8.
Definition RT_IMAP : Z := 0xa15c0.
Definition RT_IMEM : Z := 0xa15c8.
Definition RT_TP : Z := 0x5d4d70.
Definition RT_GT : Z := 0x5f7000.
Definition RT_TLSIDX : Z := 0x9a690.
Definition RT_DTPOFF : Z := 0x9a6a0.
Definition RT_REALS : list (Z * Z) := [(0x9b780, 0x938d0); (0x9b770, 0x982f4); (0x9b700, 0x924a4); (0x9b750, 0x95c30); (0x9b788, 0x8e5ec); (0x9b710, 0x8b22c); (0x9b720, 0x8eb58); (0x9b730, 0x960ec); (0x9b708, 0x924a8); (0x9b6f8, 0x92574); (0x9b840, 0x925a4); (0x9b848, 0x929a8); (0x9b778, 0x939c8); (0x9b7c0, 0x9529c); (0x9b718, 0x983e0); (0x9b798, 0x95364); (0x9b790, 0x9536c); (0x9b7b8, 0x953b4); (0x9b7b0, 0x95474); (0x9b7a8, 0x955e4); (0x9b7a0, 0x95638); (0x9b7c8, 0x8d8d0); (0x9b7d0, 0x8d8dc); (0x9b7e0, 0x8dccc); (0x9b7d8, 0x8ddc4); (0x9b6f0, 0x92ab4); (0x9b6d0, 0x92bd0); (0x9b768, 0x88a8c); (0x9b6c8, 0x92c08); (0x9b6e0, 0x92c98); (0x9b6d8, 0x92dd0); (0x9b7f0, 0x92f68); (0x9b6e8, 0x92fac); (0x9b728, 0x98294); (0x9b740, 0x8ede0); (0x9b738, 0x91ef0); (0x9b748, 0x91f0c); (0x9b758, 0x8d73c); (0x9b760, 0x8d868); (0x999d8, 0x9b840); (0x999d0, 0x9b848); (0x99990, 0x131820)].
Definition RT_REAL_LO : Z := 0x99990.
Definition RT_REAL_HI : Z := 0x9b850.
Definition RT_MUG : Z := 0x9f630.
Definition RT_AGLOB : Z := 0x9e2c0.
Definition RT_AGLOB_LEN : Z := 1024.
Definition RT_AGLOB_Z : list Z := [0; 13; 2; 0; 0; 0; 0; 0; 7; 0; 0; 0; 0; 0; 0; 0; 32; 0; 0; 0; 0; 0; 0; 0; 208; 191; 1; 0; 0; 0; 0; 0; 96; 15; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 255; 255; 255; 255; 255; 255; 255; 255; 32; 13; 2; 0; 0; 0; 0; 0; 7; 0; 0; 0; 0; 0; 0; 0; 32; 0; 0; 0; 0; 0; 0; 0; 66; 135; 1; 0; 0; 0; 0; 0; 96; 15; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 255; 255; 255; 255; 255; 255; 255; 255; 64; 13; 2; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 32; 0; 0; 0; 0; 0; 0; 0; 41; 231; 1; 0; 0; 0; 0; 0; 96; 15; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 255; 255; 255; 255; 255; 255; 255; 255; 96; 13; 2; 0; 0; 0; 0; 0; 25; 0; 0; 0; 0; 0; 0; 0; 64; 0; 0; 0; 0; 0; 0; 0; 126; 4; 2; 0; 0; 0; 0; 0; 96; 15; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 255; 255; 255; 255; 255; 255; 255; 255; 160; 13; 2; 0; 0; 0; 0; 0; 26; 0; 0; 0; 0; 0; 0; 0; 64; 0; 0; 0; 0; 0; 0; 0; 147; 71; 1; 0; 0; 0; 0; 0; 96; 15; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 255; 255; 255; 255; 255; 255; 255; 255; 224; 13; 2; 0; 0; 0; 0; 0; 45; 0; 0; 0; 0; 0; 0; 0; 96; 0; 0; 0; 0; 0; 0; 0; 17; 55; 1; 0; 0; 0; 0; 0; 96; 15; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 255; 255; 255; 255; 255; 255; 255; 255; 64; 14; 2; 0; 0; 0; 0; 0; 42; 0; 0; 0; 0; 0; 0; 0; 96; 0; 0; 0; 0; 0; 0; 0; 123; 207; 1; 0; 0; 0; 0; 0; 96; 15; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 255; 255; 255; 255; 255; 255; 255; 255; 160; 14; 2; 0; 0; 0; 0; 0; 43; 0; 0; 0; 0; 0; 0; 0; 96; 0; 0; 0; 0; 0; 0; 0; 86; 135; 1; 0; 0; 0; 0; 0; 96; 15; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 255; 255; 255; 255; 255; 255; 255; 255; 0; 15; 2; 0; 0; 0; 0; 0; 46; 0; 0; 0; 0; 0; 0; 0; 96; 0; 0; 0; 0; 0; 0; 0; 63; 164; 1; 0; 0; 0; 0; 0; 96; 15; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 255; 255; 255; 255; 255; 255; 255; 255; 160; 15; 2; 0; 0; 0; 0; 0; 5; 0; 0; 0; 0; 0; 0; 0; 32; 0; 0; 0; 0; 0; 0; 0; 208; 191; 1; 0; 0; 0; 0; 0; 0; 16; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 255; 255; 255; 255; 255; 255; 255; 255; 192; 15; 2; 0; 0; 0; 0; 0; 7; 0; 0; 0; 0; 0; 0; 0; 32; 0; 0; 0; 0; 0; 0; 0; 41; 231; 1; 0; 0; 0; 0; 0; 0; 16; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 255; 255; 255; 255; 255; 255; 255; 255; 224; 15; 2; 0; 0; 0; 0; 0; 7; 0; 0; 0; 0; 0; 0; 0; 32; 0; 0; 0; 0; 0; 0; 0; 126; 4; 2; 0; 0; 0; 0; 0; 0; 16; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 255; 255; 255; 255; 255; 255; 255; 255; 128; 223; 9; 0; 0; 0; 0; 0; 8; 0; 0; 0; 0; 0; 0; 0; 32; 0; 0; 0; 0; 0; 0; 0; 115; 45; 1; 0; 0; 0; 0; 0; 117; 15; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 255; 255; 255; 255; 255; 255; 255; 255; 0; 68; 93; 0; 0; 0; 0; 0; 8; 0; 0; 0; 0; 0; 0; 0; 32; 0; 0; 0; 0; 0; 0; 0; 39; 27; 1; 0; 0; 0; 0; 0; 117; 15; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 255; 255; 255; 255; 255; 255; 255; 255; 32; 68; 93; 0; 0; 0; 0; 0; 8; 0; 0; 0; 0; 0; 0; 0; 32; 0; 0; 0; 0; 0; 0; 0; 254; 200; 1; 0; 0; 0; 0; 0; 117; 15; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 255; 255; 255; 255; 255; 255; 255; 255; 64; 68; 93; 0; 0; 0; 0; 0; 8; 0; 0; 0; 0; 0; 0; 0; 32; 0; 0; 0; 0; 0; 0; 0; 46; 27; 1; 0; 0; 0; 0; 0; 117; 15; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 255; 255; 255; 255; 255; 255; 255; 255].

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

Definition asan_opt_cells (m : word -> option byte) : Prop :=
  bytes_at rsegs m RT_GOT_AF (le8 (Z_to_bv 64 RT_AF)) /\ bytes_at rsegs m (RT_AF + 60) [Z_to_bv 8 1]
  /\ bytes_at rsegs m RT_GOT_VERB (le8 (Z_to_bv 64 RT_VERB)) /\ bytes_at rsegs m RT_VERB (le4 (Z_to_bv 64 0)).

Definition cf_b (l : list Z) : list byte := map (Z_to_bv 8) l.

Definition asan_cf_cells (m : word -> option byte) : Prop :=
  bytes_at rsegs m RT_GOT_CF (le8 (Z_to_bv 64 RT_CF))
  /\ bytes_at rsegs m (RT_CF + 32) (cf_b [0; 0; 1; 0; 30; 0; 0; 0])
  /\ bytes_at rsegs m (RT_CF + 64) (cf_b [0]) /\ bytes_at rsegs m (RT_CF + 84) (cf_b [1])
  /\ bytes_at rsegs m (RT_CF + 120) (le8 (Z_to_bv 64 (2^64 - 1))) /\ bytes_at rsegs m (RT_CF + 137) (cf_b [1])
  /\ bytes_at rsegs m (RT_CF + 240) (cf_b [0; 0; 0; 0; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0])
  /\ bytes_at rsegs m (RT_AF + 29) (cf_b [1]).

Definition asan_uw_cells (m : word -> option byte) : Prop :=
  bytes_at rsegs m RT_TSDI (cf_b [1]) /\ bytes_at rsegs m RT_TSDK (le4 (Z_to_bv 64 0))
  /\ bytes_at rsegs m RT_PGSZ (le8 (Z_to_bv 64 4096)) /\ bytes_at rsegs m (RT_TP - 88) (le8 (Z_to_bv 64 RT_TSDMAIN))
  /\ exists c, bytes_at rsegs m RT_TSDMAIN (le8 c).

Definition asan_real_cells (m : word -> option byte) : Prop :=
  Forall (fun p => bytes_at rsegs m (fst p) (le8 (wa (snd p)))) RT_REALS.

Lemma RT_REALS_span : Forall (fun p => RT_REAL_LO <= fst p /\ fst p + 8 <= RT_REAL_HI) RT_REALS.
Proof. unfold RT_REALS, RT_REAL_LO, RT_REAL_HI. repeat constructor; cbn; lia. Qed.

Definition asan_im_cells (m : word -> option byte) : Prop :=
  bytes_at rsegs m RT_IMAP (le8 (Z_to_bv 64 RT_IMEM)) /\ exists t, bytes_at rsegs m RT_IMEM (le8 t).

Definition asan_exit_cells (m : word -> option byte) : Prop :=
  bytes_at rsegs m (RT_CF + 185) (cf_b [0]) /\ bytes_at rsegs m (RT_AF + 24) (le4 (Z_to_bv 64 1))
  /\ bytes_at rsegs m RT_MUG (le8 (Z_to_bv 64 0)) /\ bytes_at rsegs m RT_AGLOB (cf_b RT_AGLOB_Z).

Lemma RT_AGLOB_len : Z.of_nat (length (cf_b RT_AGLOB_Z)) = RT_AGLOB_LEN.
Proof. reflexivity. Qed.

Definition RT_FS_SIZE : Z := 11571200.

Definition fs_value_ok (FS : Z) : Prop :=
  0 < FS /\ FS mod 4096 = 0 /\ RT_GT <= FS /\ (forall a, FS <= a < FS + RT_FS_SIZE -> app_mem a).

Definition asan_fs_cells (m : word -> option byte) : Prop :=
  bytes_at rsegs m RT_TLSIDX (le8 (Z_to_bv 64 1) ++ le8 (Z_to_bv 64 (-2048)))
  /\ bytes_at rsegs m RT_DTPOFF (le8 (Z_to_bv 64 8))
  /\ bytes_at rsegs m (RT_TP - 8) (le8 (Z_to_bv 64 (RT_TP + 32)))
  /\ bytes_at rsegs m (RT_TP + 40) (le8 (Z_to_bv 64 (RT_TP + 2048)))
  /\ (exists FS : word, bytes_at rsegs m RT_TP (le8 FS) /\ fs_value_ok (bv_unsigned FS))
  /\ (exists DB : word, bytes_at rsegs m (RT_TP + 8) (le8 DB) /\ bv_unsigned DB <> 0 /\ app_mem (bv_unsigned DB)).
