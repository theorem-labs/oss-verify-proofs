(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/AsanRT.v at a working branch 5d8d8a15571, relocated A->B by Theorem Labs tools over the unstripped twins; every image numeral re-derived by symbol / section (a Theorem Labs lane reloc report). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import Img0.
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

Definition CELL_K : Z := 0xa2078.
Definition UAR : Z := 0xa2080.
Definition INITED : Z := 0xa2d58.
Definition REPLACE : Z := 0xa2d59.
Definition CANPOISON : Z := 0xa18dc.
Definition HIEND : Z := 0xa2d60.
Definition MIDBEG : Z := 0xa2d68.
Definition MIDEND : Z := 0xa2d70.
Definition REAL_MEMCPY : Z := 0x9bb20.
Definition REAL_MEMSET : Z := 0x9bb28.
Definition MUSL_MEMCPY : Z := 0x9288c.
Definition MUSL_MEMSET : Z := 0x92c90.
Definition GOT_CELL_K : Z := 0x99c98.
Definition GOT_UAR : Z := 0x99cf0.
Definition GOT_REPLACE : Z := 0x9a800.
Definition GOT_HIEND : Z := 0x99cb0.
Definition GOT_MIDBEG : Z := 0x99ca0.
Definition GOT_MIDEND : Z := 0x99ca8.
Definition GOT_REAL_MEMSET : Z := 0x99cb8.
Definition RT_LO : Z := 0x99c98.
Definition RT_HI : Z := 0xa2d78.
Definition RT_AF : Z := 0x9f878.
Definition RT_GOT_AF : Z := 0x99c90.
Definition RT_VERB : Z := 0x131b18.
Definition RT_GOT_VERB : Z := 0x99ce8.
Definition RT_CF : Z := 0x133ba8.
Definition RT_GOT_CF : Z := 0x99c88.
Definition RT_TSDI : Z := 0xa18e0.
Definition RT_TSDK : Z := 0xa18e4.
Definition RT_PGSZ : Z := 0x131b20.
Definition RT_TSDMAIN : Z := 0x5f6418.
Definition RT_BTLS : Z := 0x5d4fa8.
Definition RT_IMAP : Z := 0xa18c0.
Definition RT_IMEM : Z := 0xa18c8.
Definition RT_TP : Z := 0x5d5070.
Definition RT_GT : Z := 0x5f7000.
Definition RT_TLSIDX : Z := 0x9a978.
Definition RT_DTPOFF : Z := 0x9a988.
Definition RT_REALS : list (Z * Z) := [(0x9ba60, 0x93bb8); (0x9ba50, 0x985dc); (0x9b9e0, 0x9278c); (0x9ba30, 0x95f18); (0x9ba68, 0x8e8d4); (0x9b9f0, 0x8b514); (0x9ba00, 0x8ee40); (0x9ba10, 0x963d4); (0x9b9e8, 0x92790); (0x9b9d8, 0x9285c); (0x9bb20, 0x9288c); (0x9bb28, 0x92c90); (0x9ba58, 0x93cb0); (0x9baa0, 0x95584); (0x9b9f8, 0x986c8); (0x9ba78, 0x9564c); (0x9ba70, 0x95654); (0x9ba98, 0x9569c); (0x9ba90, 0x9575c); (0x9ba88, 0x958cc); (0x9ba80, 0x95920); (0x9baa8, 0x8dbb8); (0x9bab0, 0x8dbc4); (0x9bac0, 0x8dfb4); (0x9bab8, 0x8e0ac); (0x9b9d0, 0x92d9c); (0x9b9b0, 0x92eb8); (0x9ba48, 0x88d74); (0x9b9a8, 0x92ef0); (0x9b9c0, 0x92f80); (0x9b9b8, 0x930b8); (0x9bad0, 0x93250); (0x9b9c8, 0x93294); (0x9ba08, 0x9857c); (0x9ba20, 0x8f0c8); (0x9ba18, 0x921d8); (0x9ba28, 0x921f4); (0x9ba38, 0x8da24); (0x9ba40, 0x8db50); (0x99cc0, 0x9bb20); (0x99cb8, 0x9bb28); (0x99c78, 0x131b20)].
Definition RT_REAL_LO : Z := 0x99c78.
Definition RT_REAL_HI : Z := 0x9bb30.
Definition RT_MUG : Z := 0x9f930.
Definition RT_AGLOB : Z := 0x9e5a0.
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
