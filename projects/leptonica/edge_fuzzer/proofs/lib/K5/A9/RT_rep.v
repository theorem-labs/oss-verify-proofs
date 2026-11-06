(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Permutation.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require BackingAlgebra.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Mem Frame Cells Step Arr.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require NodesA_madv.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import AsanAcct.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import RT_iface.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import R_sizeclass.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import R_cache_defs R_prim_defs R_thread R_m2s R_poison R_leaves R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state TopA_iodefs.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition cpw (c i : Z) : word := Z_to_bv 64 ((i * ClassSize c) / 16).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition icells_rep (L : layoutA) (m : mem) : Prop :=
  rw_cells asegs m (l_T L + 0xc60) [C1 (Z_to_bv 8 0)]
  /\ ro_cells asegs m 0x26acdd [C1 (Z_to_bv 8 0)] /\ ro_cells asegs m 0x26ace4 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x1c3bd8 [C8 (Z_to_bv 64 0x1d68b8)] /\ ro_cells asegs m 0x1c3c08 [C8 (Z_to_bv 64 0x1c5cd8)]
  /\ ro_cells asegs m 0x1c5cd8 [C8 (Z_to_bv 64 0x1b5fa8)] /\ ro_cells asegs m 0x1d68d5 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x1d9dbc [C4 (Z_to_bv 64 30)] /\ ro_cells asegs m 0x26ac0a [C1 (Z_to_bv 8 1)]
  (* [comment removed for export] *)
  /\ ro_cells asegs m 0x1c4868 [C8 (Z_to_bv 64 0x1c8420)] /\ ro_cells asegs m 0x1c4a18 [C8 (Z_to_bv 64 0x72c478)]
  (* [comment removed for export] *)
  /\ ro_cells asegs m 0x1c4750 [C8 (Z_to_bv 64 0x1d9d99)] /\ ro_cells asegs m 0x1d9d99 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x1c5ce0 [C8 (Z_to_bv 64 0x1b63dc)] /\ ro_cells asegs m 0x1c5af8 [C8 (Z_to_bv 64 0x1b5eac)]
  /\ ro_cells asegs m 0x1c5c88 [C8 (Z_to_bv 64 0x1b6954)] /\ ro_cells asegs m 0x1c5ac8 [C8 (Z_to_bv 64 0x1b6714)]
  /\ ro_cells asegs m 0x26ace3 [C1 (Z_to_bv 8 1)]    (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0x1d6878 [C8 (Z_to_bv 64 (2 ^ 40))] /\ rw_cells asegs m 0x1d6880 [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)]
  /\ rw_cells asegs m 0x25b322 [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m 0x26ac0a [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x1c3bd8 [C8 (Z_to_bv 64 0x1d68b8)] /\ rw_cells asegs m (0x1d68b8 + 44) [C4 (Z_to_bv 64 4096)]
  /\ rw_cells asegs m (0x1d68b8 + 52) [C4 (Z_to_bv 64 190)] /\ rw_cells asegs m (0x1d68b8 + 85) [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m (0x70c438 + 32) [C4 (Z_to_bv 64 0)] /\ rw_cells asegs m 0x1c4848 [C8 (Z_to_bv 64 32)]
  /\ rw_cells asegs m 0x26ab80 [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m 0x1d891c [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m (l_TCX L + 8) [C4 (Z_to_bv 64 0)]
  /\ stk asegs m (l_T L + 2768) (l_T L + 3168)
  (* [comment removed for export] *)
  /\ rw_cells asegs m (l_T L) [C8 (Z_to_bv 64 (l_TCX L))]
  (* [comment removed for export] *)
  /\ rw_cells asegs m (g_MFHooks + 8) [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m i_q_max [C8 (Z_to_bv 64 0x10000000); C8 (Z_to_bv 64 0xE666661); C8 (Z_to_bv 64 0x100000)]
  /\ rw_cells asegs m (g_asan_flags + 48) [C4 (Z_to_bv 64 0)]
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0x1c3c20 [C8 (Z_to_bv 64 1)] /\ rw_cells asegs m 0x26acc3 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x26acdc [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m 0x1c4a18 [C8 (Z_to_bv 64 0x72c478)]
  /\ rw_cells asegs m 0x72c6f8 [C8 (Z_to_bv 64 4096)]
  (* [comment removed for export] *)
  /\ Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro.

(* [comment removed for export] *)
Definition consts_rep (L : layoutA) (m : mem) : Prop :=
  inst_cells (l_SB L) m /\ mm_gcells m /\ thread_cells (l_TCX L) (l_T L) m /\ m2s_cells m /\ ps_cells m
  /\ stack_cells (l_T L) (l_top L) (l_top L - 0x800000) m /\ client_consts m /\ icells_rep L m.

(* [comment removed for export] *)
Definition reg_rep (SB c : Z) (r : regst) (m : mem) : Prop :=
  let R := rinfo (RIS_of SB) c in
  let auser := ClassSize c * Z.of_nat (length (r_st r)) in
  ri_lock m R 0 /\ ri_core m R (Z.of_nat (length (r_fl r))) (r_mfa r) auser (r_muser r)
  /\ (exists rand exh pad nal nfr r0 r1 r2 r3, ri_tail m R rand exh pad nal nfr r0 r1 r2 r3)
  /\ (exists ws, fl_arr m SB c ws /\ 4 * Z.of_nat (length ws) = r_mfa r /\ firstn (length (r_fl r)) ws = map (cpw c) (r_fl r))
  /\ stk asegs m (rb SB c + auser) (rb SB c + r_muser r)
  /\ bytes_at asegs m (shad (rb SB c + auser)) (farun ((r_muser r - auser) / 8))
  /\ stk asegs m (shad (rb SB c)) (shad (rb SB c + 2 ^ 32)).
Definition prim_rep (Σ : rtsA) (m : mem) : Prop := forall c, 1 <= c <= 31 -> reg_rep (l_SB (lay Σ)) c (pr Σ c) m.

(* [comment removed for export] *)
Definition pclass_rep (T c : Z) (init : bool) (l : list Z) (m : mem) : Prop :=
  pc_cells m (pc_addr T c) (Z.of_nat (length l)) (if init then MaxCount c else 0) (if init then ClassSize c else 0)
  /\ exists chs, u32arr asegs m (pc_addr T c + 16) chs /\ length chs = 16%nat /\ firstn (length l) chs = map (cpw c) l.
Definition cache_rep (Σ : rtsA) (m : mem) : Prop :=
  forall c, 1 <= c <= 31 -> pclass_rep (l_T (lay Σ)) c (ca_init Σ) (ca Σ c) m.

(* [comment removed for export] *)
Definition pchunk (SB c : Z) (i : nat) (st : ckst) (m : mem) : Prop :=
  let AB := p_abeg SB c i in let S := ClassSize c in
  match st with
  | CkIdle => stk asegs m AB (AB + S) /\ pshadow_idle m AB S
  | CkBatch => pshadow_idle m AB S
  | CkAlloc n => wr_at asegs m AB S /\ ahdr m (AB + rz_size n - 16) n /\ lch_if m AB (AB + rz_size n - 16) n
                 /\ pshadow_alloc m AB S n
  | CkQuar n => wr_at asegs m AB S /\ qhdr3 m (AB + rz_size n - 16) n /\ lch_if m AB (AB + rz_size n - 16) n
                /\ pshadow_quar m AB S n
  end.
(* [comment removed for export] *)
Definition schunk (k : nat) (s : secst) (m : mem) : Prop :=
  let mb := s_mb s in let msz := smsz (s_n s) in let AB := mb + 4096 in let M := AB + 2032 in let n := s_n s in
  shdr m mb msz (needed n + rz_size n) (Z.of_nat k) /\ wr_at asegs m mb msz /\ lch m AB M
  /\ (if s_quar s then qhdr3 m M n else ahdr m M n)
  /\ stk asegs m (shad mb) (shad (mb + msz))     (* [comment removed for export] *)
  /\ bytes_at asegs m (shad mb) (farun ((4096 + 2048) / 8))
  /\ bytes_at asegs m (shad (AB + 2048)) (if s_quar s then fdrun (ru8 n / 8) else ushadow n)
  /\ bytes_at asegs m (shad (AB + 2048 + ru8 n)) (farun ((msz - 4096 - 2048 - ru8 n) / 8)).
Definition chunk_rep (Σ : rtsA) (m : mem) : Prop :=
  (forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> pchunk (l_SB (lay Σ)) c i st m)
  /\ (forall k s, nth_error (sec Σ) k = Some s -> schunk k s m).

(* [comment removed for export] *)
Definition sec_rep (Σ : rtsA) (m : mem) : Prop :=
  sec_core m (l_PAB (lay Σ)) (sec_nres Σ) (Z.of_nat (length (sec Σ))) /\ sec_pad m
  /\ (exists ws, u64arr asegs m (l_PAB (lay Σ)) ws /\ Z.of_nat (length ws) = sec_nres Σ
                 /\ firstn (length (sec Σ)) ws = map (fun s => Z_to_bv 64 (s_mb s)) (sec Σ))
  /\ sec_page m /\ sec_range m (l_PAB (lay Σ)) /\ sec_junk m /\ name_cells m    (* [comment removed for export] *).

(* [comment removed for export] *)
Definition quar_rep (Σ : rtsA) (m : mem) : Prop :=
  qcache_rep m (qcacheT (l_T (lay Σ))) (ql Σ) /\ qcache_rep m i_q_global (qg Σ)
  /\ rw_cells asegs m i_q_cmutex [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (Z_to_bv 64 0)].   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition dep_rep (L : layoutA) (d : depot) (m : mem) : Prop := depot_rep d (DEP_BK (hash_of (d_hs d) 1)) (l_DNB L) (l_SSB L) m.

(* [comment removed for export] *)
Definition fs_cls_rep (FSB c : Z) (f : fsst) (m : mem) : Prop :=
  fs_hint FSB c m (fss_hint f) /\ fs_flags FSB c m (fss_flags f) /\ fs_free_frames FSB c m (fss_flags f).
(* [comment removed for export] *)
Definition fs_busy (L : layoutA) (frs : list (Z * nat)) (m : mem) : Prop :=
  Forall (fun fk => exists p, fst fk = frame_addr (l_FSB L) (Z.of_nat (snd fk)) p
            /\ wr_at asegs m (fst fk) (fs_size (snd fk)) /\ wr_at asegs m (shad (fst fk)) (fs_size (snd fk) / 8)
            /\ rw_cells asegs m (fst fk + fs_size (snd fk) - 8) [C8 (Z_to_bv 64 (fl_base (l_FSB L) (Z.of_nat (snd fk)) + p))]) frs.
Definition fs_rep (Σ : rtsA) (m : mem) : Prop :=
  let L := lay Σ in let FSB := l_FSB L in
  fs_const FSB m /\ (forall k, (k <= 10)%nat -> fs_cls_rep FSB (Z.of_nat k) (fs_of Σ k) m)
  /\ rw_cells asegs m tpA [C8 (Z_to_bv 64 FSB)]
  /\ (exists dtvbeg, 0 < dtvbeg < 2 ^ 64 /\ tga_cells (l_DTV L) dtvbeg m)
  /\ (exists tb te, ttls_cells (l_T L) m tb te)
  /\ fs_busy L (frames Σ) m.

(* [comment removed for export] *)
Definition ia_rep (Σ : rtsA) (m : mem) : Prop := exists b, ia_state b m.

(* [comment removed for export] *)
Definition CS_W : list (Z * Z) :=
  [(0x1c81f0, 0x1c8424); (0x1c8440, 0x1c8448); (0x1c8460, 0x1c8464); (0x1c8480, 0x1c8488); (0x1c84a0, 0x1c84a8); (0x1c84c0, 0x1c84c8); (0x1c84e0, 0x1c84e4); (0x1c8500, 0x1c8504); (0x1c8520, 0x1d5a58);
   (0x6fb710, 0x70b710);
   (0x70b710, 0x70c3e0); (0x70c3e8, 0x70c430);
   (0x70c460, 0x70c468); (0x70c478, 0x72c6f8); (0x72c700, 0x72d7e0); (0x72d7e8, 0x72dd18)].
(* [comment removed for export] *)
Definition CS_ACC : list (Z * Z) :=
  [(0x1c81f0, 0x1c8424); (0x1c8440, 0x1c8448); (0x1c8460, 0x1c8464); (0x1c8480, 0x1c8488); (0x1c84a0, 0x1c84a8); (0x1c84c0, 0x1c84c8); (0x1c84e0, 0x1c84e4); (0x1c8500, 0x1c8504); (0x1c8520, 0x1c8870); (0x1d59f0, 0x1d5a58);
   (0x6fb710, 0x70b710);
   (0x70b710, 0x70c3e0); (0x70c3e8, 0x70c430);
   (0x70c460, 0x70c468); (0x70c478, 0x72d7e0); (0x72d7e8, 0x72dd18);
   (* [comment removed for export] *)
   (0x30e00, 0x30e0e); (0x30e20, 0x30e2a); (0x30e40, 0x30e50); (0x30e60, 0x30e7d); (0x30f60, 0x30f87); (0x30fc0, 0x30fd0); (0x30fe0, 0x30ff2); (0x31020, 0x31033); (0x310c0, 0x310cc); (0x310e0, 0x310f8); (0x312c0, 0x312cb); (0x31460, 0x31470); (0x31480, 0x3148c); (0x31500, 0x3150d); (0x31560, 0x3156c); (0x315c0, 0x315d1); (0x31680, 0x3168a); (0x317e0, 0x317ef); (0x31800, 0x31816); (0x31880, 0x3188b); (0x31a80, 0x31a90); (0x31c60, 0x31c6e); (0x323c0, 0x323cf); (0x323e0, 0x323f3); (0x32420, 0x3242f); (0x32440, 0x32451); (0x32480, 0x32497); (0x327e0, 0x327f6); (0x32820, 0x3282f); (0x32b40, 0x32b51); (0x32cc0, 0x32ccf); (0x32ce0, 0x32cfd); (0x32d20, 0x32d2b); (0x32d40, 0x32d4e); (0x32e20, 0x32e31); (0x32f20, 0x32f36); (0x32f60, 0x32f74); (0x32fa0, 0x32fc5); (0x33b00, 0x33b13); (0x33b40, 0x33b48); (0x33b60, 0x33b70); (0x36c20, 0x36c2d); (0x36c40, 0x36c51); (0x36e60, 0x36e79); (0x36f00, 0x36f12); (0x36f40, 0x36f4e); (0x36f60, 0x36f6f); (0x36f80, 0x36f8f); (0x36fa0, 0x36fb0); (0x36fc0, 0x36fd6); (0x37080, 0x3708e); (0x370a0, 0x370b2); (0x370e0, 0x370f9); (0x2dec0, 0x2ded1); (0x31060, 0x3108f); (0x31120, 0x31150); (0x31180, 0x311b4); (0x311e0, 0x31215); (0x31260, 0x31285); (0x32360, 0x32385); (0x31c80, 0x31c9b); (0x324c0, 0x324e5); (0x32520, 0x3254f); (0x32580, 0x325ae); (0x325e0, 0x325ff); (0x32620, 0x32653); (0x32680, 0x326b8); (0x326e0, 0x3271a); (0x32740, 0x3278d); (0x36ea0, 0x36ec3); (0x37000, 0x37054); (0x31cc0, 0x31d44);
   (* [comment removed for export] *)
   (0x1149b, 0x114a5); (0x17742, 0x17746); (0x19300, 0x19380); (0x20360, 0x20381); (0x27cb9, 0x27cce); (0x27cce, 0x27ce5);
   (0x2b740, 0x2b7c0); (0x2d671, 0x2d678); (0x2de38, 0x2de48); (0x6fb700, 0x6fb710);
   (* [comment removed for export] *)
   (0x2df00, 0x2df1f); (0x2df40, 0x2df52); (0x2df80, 0x2df96); (0x2dfc0, 0x2dfd3); (0x2e000, 0x2e014); (0x2e040, 0x2e052); (0x2e080, 0x2e093); (0x2e0c0, 0x2e0cd);
   (0x2e0e0, 0x2e0ed); (0x2e140, 0x2e160); (0x2e180, 0x2e18a); (0x2e1a0, 0x2e1ae); (0x2e1c0, 0x2e1d1); (0x2e200, 0x2e20b); (0x2e220, 0x2e232); (0x2e260, 0x2e26e);
   (0x2e280, 0x2e294); (0x2e2c0, 0x2e2cd); (0x2e2e0, 0x2e30e); (0x2e340, 0x2e34a); (0x2e360, 0x2e378); (0x2e3a0, 0x2e3ba); (0x2e3e0, 0x2e3f1); (0x2e420, 0x2e42b);
   (0x2e440, 0x2e455); (0x2e480, 0x2e48f); (0x2e4a0, 0x2e4c1); (0x2e500, 0x2e512); (0x2e540, 0x2e55f); (0x2e580, 0x2e597); (0x2e5c0, 0x2e5cb); (0x2e5e0, 0x2e5f1);
   (0x2e620, 0x2e634); (0x2e660, 0x2e66d); (0x2e680, 0x2e695); (0x2e6c0, 0x2e6d7); (0x2e700, 0x2e714); (0x2e740, 0x2e753); (0x2e780, 0x2e78f); (0x2e7a0, 0x2e7c3);
   (0x2e800, 0x2e813); (0x2e840, 0x2e859); (0x2e880, 0x2e893); (0x2e8c0, 0x2e8ee); (0x2e920, 0x2e935); (0x2e960, 0x2e991); (0x2e9c0, 0x2e9d2); (0x2ea00, 0x2ea10);
   (0x2ea20, 0x2ea2e); (0x2ea40, 0x2ea5a); (0x2ea80, 0x2ea8e); (0x2eaa0, 0x2eab2); (0x2eae0, 0x2eaed); (0x2eb00, 0x2eb10); (0x2eb20, 0x2eb32); (0x2eb60, 0x2eb63);
   (0x2eb80, 0x2ebc1); (0x2ec00, 0x2ec0f); (0x2ec20, 0x2ec31); (0x2ec60, 0x2ec82); (0x2ecc0, 0x2ecc2); (0x2ece0, 0x2ece5); (0x2ed00, 0x2ed1c); (0x2ed40, 0x2ed4c);
   (0x2ed60, 0x2ed61); (0x2ed80, 0x2ed95); (0x2edc0, 0x2edc9); (0x2ede0, 0x2edf7); (0x2ee20, 0x2ee31); (0x2ee60, 0x2ee76); (0x2eea0, 0x2eea9); (0x2eec0, 0x2eecc);
   (0x2eee0, 0x2eef5); (0x2ef20, 0x2ef31); (0x2ef60, 0x2ef71); (0x2efa0, 0x2efb3); (0x2efe0, 0x2eff0); (0x2f000, 0x2f02e); (0x2f060, 0x2f077); (0x2f0a0, 0x2f0b3);
   (0x2f0e0, 0x2f0ed); (0x2f100, 0x2f10f); (0x2f160, 0x2f176); (0x2f1a0, 0x2f1ac); (0x2f1c0, 0x2f1e4); (0x2f220, 0x2f22d); (0x2f240, 0x2f24f); (0x2f260, 0x2f26f);
   (0x2f280, 0x2f291); (0x2f2c0, 0x2f2ce); (0x2f2e0, 0x2f2fb); (0x2f320, 0x2f331); (0x2f360, 0x2f36f); (0x2f380, 0x2f390); (0x2f3a0, 0x2f3b2); (0x2f3e0, 0x2f3ef);
   (0x2f400, 0x2f40f); (0x2f420, 0x2f42f); (0x2f440, 0x2f451); (0x2f480, 0x2f4a1); (0x2f520, 0x2f534); (0x2f560, 0x2f56e); (0x2f580, 0x2f5a4); (0x2f5e0, 0x2f5ef);
   (0x2f600, 0x2f61a); (0x2f640, 0x2f660); (0x2f680, 0x2f6a9); (0x2f6e0, 0x2f6ef); (0x2f700, 0x2f70c); (0x2f720, 0x2f730); (0x2f740, 0x2f751); (0x2f780, 0x2f791);
   (0x2f7c0, 0x2f7d3); (0x2f800, 0x2f81b); (0x2f840, 0x2f84d); (0x2f860, 0x2f871); (0x2f8a0, 0x2f8bc); (0x2f8e0, 0x2f8f2); (0x2f960, 0x2f973); (0x2f9a0, 0x2f9ad);
   (0x2f9c0, 0x2f9e5); (0x2fa20, 0x2fa2e); (0x2fa40, 0x2fa4f); (0x2fa60, 0x2fa70); (0x2fa80, 0x2fa93); (0x2fac0, 0x2fad1); (0x2fb00, 0x2fb11); (0x2fb40, 0x2fb4f);
   (0x2fb60, 0x2fb70); (0x2fb80, 0x2fb90); (0x2fba0, 0x2fbaf); (0x2fbc0, 0x2fbd4); (0x2fc00, 0x2fc12); (0x2fc40, 0x2fc41); (0x2fc60, 0x2fc62); (0x2fc80, 0x2fc82);
   (0x2fca0, 0x2fca2); (0x2fcc0, 0x2fcd0); (0x2fce0, 0x2fcee); (0x2fd00, 0x2fd0e); (0x2fd20, 0x2fd32); (0x2fd60, 0x2fd70); (0x2fd80, 0x2fd97); (0x2fdc0, 0x2fdd2);
   (0x2fe00, 0x2fe25); (0x2fe60, 0x2fe7b); (0x2fee0, 0x2fef0); (0x2ff00, 0x2ff10); (0x2ff20, 0x2ff2a); (0x2ff80, 0x2ff96); (0x2ffc0, 0x2ffcb); (0x2ffe0, 0x30004);
   (0x30040, 0x3004c); (0x30060, 0x3006f); (0x30080, 0x3008e); (0x300a0, 0x300b1); (0x300e0, 0x300ed); (0x30100, 0x3011b); (0x30140, 0x30151); (0x30180, 0x3018e);
   (0x301a0, 0x301b0); (0x301c0, 0x301d2); (0x30200, 0x3020e); (0x30220, 0x30230); (0x30240, 0x30255); (0x30280, 0x3029c); (0x30340, 0x30350); (0x30360, 0x30369);
   (0x30380, 0x30392); (0x303c0, 0x303c4); (0x303e0, 0x303f2); (0x30420, 0x3043a); (0x30460, 0x30473); (0x304a0, 0x304af); (0x304c0, 0x304cf); (0x30520, 0x30536);
   (0x30560, 0x3056a); (0x30580, 0x30598); (0x305c0, 0x305d8); (0x30600, 0x30610); (0x30620, 0x30645); (0x30680, 0x3068b); (0x306a0, 0x306af); (0x306c0, 0x306cf);
   (0x30720, 0x30744); (0x30780, 0x3078b); (0x307a0, 0x307b3); (0x307e0, 0x30804); (0x30840, 0x3084c); (0x30860, 0x3089a); (0x308c0, 0x308cf); (0x308e0, 0x308e8);
   (0x30900, 0x30911); (0x30940, 0x30952); (0x30980, 0x3098b); (0x309a0, 0x309ba); (0x309e0, 0x309f1); (0x30a20, 0x30a3e); (0x30a60, 0x30a70); (0x30a80, 0x30a9b);
   (0x30b00, 0x30b1d); (0x30b40, 0x30b4a); (0x30b60, 0x30b85); (0x30bc0, 0x30bcb); (0x30be0, 0x30bf0); (0x30c00, 0x30c09); (0x30c20, 0x30c31); (0x30c60, 0x30c69);
   (0x30c80, 0x30c8e); (0x30ca0, 0x30ca9); (0x30cc0, 0x30cd0); (0x30ce0, 0x30d02); (0x30d40, 0x30d59); (0x30d80, 0x30d99); (0x30ea0, 0x30eb1); (0x30ee0, 0x30ef2);
   (0x30f20, 0x30f38); (0x31240, 0x31249); (0x312e0, 0x312e8); (0x31300, 0x3131c); (0x31340, 0x31353); (0x31380, 0x31391); (0x313c0, 0x313d0); (0x313e0, 0x313ff);
   (0x31420, 0x3142f); (0x31440, 0x3144f); (0x314a0, 0x314ac); (0x314c0, 0x314d3); (0x31520, 0x3152d); (0x31540, 0x3154f); (0x31580, 0x3158c); (0x315a0, 0x315af);
   (0x31600, 0x3160a); (0x31620, 0x3162a); (0x31640, 0x31651); (0x316a0, 0x316ab); (0x316c0, 0x316cb); (0x316e0, 0x316f2); (0x31720, 0x31732); (0x31760, 0x31773);
   (0x317a0, 0x317ab); (0x317c0, 0x317cf); (0x31840, 0x31853); (0x31a20, 0x31a31); (0x31a60, 0x31a6c); (0x31aa0, 0x31ac5); (0x31b00, 0x31b0c); (0x31b20, 0x31b31);
   (0x31b60, 0x31b73); (0x31ba0, 0x31bd8); (0x31c00, 0x31c40); (0x31d80, 0x31d8e); (0x31da0, 0x31db3); (0x31de0, 0x31df0); (0x31e00, 0x31e0d); (0x31e20, 0x31e37);
   (0x31e60, 0x31e71); (0x31ea0, 0x31ebd); (0x31ee0, 0x31ef1); (0x31f20, 0x31f33); (0x31f60, 0x31f70); (0x31f80, 0x31f91); (0x31fc0, 0x31fd5); (0x32000, 0x32012);
   (0x32040, 0x32058); (0x32080, 0x320a3); (0x320e0, 0x320f1); (0x32120, 0x3213d); (0x32160, 0x32173); (0x321e0, 0x321f7); (0x32220, 0x3222e); (0x32240, 0x32256);
   (0x32280, 0x32294); (0x322c0, 0x322d0); (0x322e0, 0x322f2); (0x32320, 0x3232c); (0x32340, 0x3234d); (0x327c0, 0x327d0); (0x32840, 0x32850); (0x32860, 0x32884);
   (0x328c0, 0x328d0); (0x328e0, 0x328f4); (0x32920, 0x3292f); (0x32940, 0x32953); (0x32980, 0x32990); (0x329a0, 0x329b4); (0x329e0, 0x329f0); (0x32a00, 0x32a1b);
   (0x32a40, 0x32a58); (0x32a80, 0x32a97); (0x32ac0, 0x32ad2); (0x32b00, 0x32b15); (0x32b80, 0x32b92); (0x32bc0, 0x32be4); (0x32c20, 0x32c30); (0x32c40, 0x32c59);
   (0x32c80, 0x32c95); (0x32d60, 0x32d74); (0x32da0, 0x32daa); (0x32dc0, 0x32dc5); (0x32e60, 0x32e75); (0x32ea0, 0x32eb8); (0x32ee0, 0x32eff); (0x331e0, 0x331f1);
   (0x33220, 0x3322f); (0x33240, 0x3324e); (0x33260, 0x33272); (0x332a0, 0x332d6); (0x33300, 0x3331b); (0x33340, 0x33360); (0x33380, 0x33399); (0x333c0, 0x333f7);
   (0x33420, 0x3343c); (0x33460, 0x3348a); (0x334c0, 0x334de); (0x33500, 0x33514); (0x33540, 0x3354d); (0x33560, 0x33577); (0x335a0, 0x335b4); (0x335e0, 0x335f0);
   (0x33600, 0x3363b); (0x33660, 0x33670); (0x33680, 0x33690); (0x336a0, 0x336af); (0x336c0, 0x336d2); (0x33700, 0x33710); (0x33720, 0x33730); (0x33740, 0x33753);
   (0x33780, 0x3378f); (0x337a0, 0x337af); (0x337c0, 0x337cf); (0x337e0, 0x337ef); (0x33800, 0x3380f); (0x33820, 0x3382f); (0x33840, 0x3385d); (0x33880, 0x3388e);
   (0x338a0, 0x338af); (0x338c0, 0x338e1); (0x33920, 0x33930); (0x33940, 0x33951); (0x33980, 0x33990); (0x339a0, 0x339b4); (0x339e0, 0x33a02); (0x33a80, 0x33a91);
   (0x33ac0, 0x33aca); (0x33ae0, 0x33aee); (0x33bc0, 0x33bd1); (0x33c00, 0x33c0c); (0x33c20, 0x33c31); (0x33c60, 0x33c7f); (0x33f00, 0x33f22); (0x33f60, 0x33f76);
   (0x33fa0, 0x33fb6); (0x34020, 0x34032); (0x34060, 0x34072); (0x340a0, 0x340b1); (0x340e0, 0x340f5); (0x34120, 0x34138); (0x34160, 0x3416f); (0x34180, 0x34199);
   (0x341c0, 0x341dd); (0x34200, 0x34210); (0x34220, 0x34235); (0x34260, 0x34292); (0x34300, 0x34315); (0x34340, 0x34354); (0x34380, 0x3438f); (0x343a0, 0x343af);
   (0x343c0, 0x343ce); (0x34460, 0x34473); (0x344a0, 0x344ad); (0x344c0, 0x344e5); (0x34520, 0x34526); (0x34540, 0x34561); (0x345e0, 0x345f3); (0x34620, 0x34634);
   (0x34660, 0x34675); (0x346a0, 0x346af); (0x346c0, 0x346e6); (0x34720, 0x34735); (0x34760, 0x34778); (0x347e0, 0x347f1); (0x348e0, 0x348f5); (0x34920, 0x34933);
   (0x34960, 0x34962); (0x34980, 0x3498f); (0x349a0, 0x349b0); (0x349c0, 0x349c2); (0x349e0, 0x349f5); (0x34a20, 0x34a4b); (0x34a80, 0x34ac8); (0x34b00, 0x34b10);
   (0x34b20, 0x34b32); (0x34b60, 0x34b63); (0x34b80, 0x34b96); (0x34bc0, 0x34bcd); (0x34be0, 0x34bef); (0x34c00, 0x34c2d); (0x34c60, 0x34c81); (0x34cc0, 0x34cd2);
   (0x34d00, 0x34d16); (0x34d40, 0x34d54); (0x34d80, 0x34d92); (0x34dc0, 0x34dd6); (0x34e00, 0x34e14); (0x34e40, 0x34e59); (0x34e80, 0x34e9a); (0x34ec0, 0x34ed0);
   (0x34ee0, 0x34ef1); (0x34f20, 0x34f3c); (0x34f60, 0x34f82); (0x34fc0, 0x34fe9); (0x35020, 0x35033); (0x35060, 0x35075); (0x350a0, 0x350d7); (0x35100, 0x3513d);
   (0x35160, 0x35195); (0x351c0, 0x351e5); (0x35220, 0x35238); (0x35260, 0x35274); (0x352a0, 0x352b7); (0x352e0, 0x352f9); (0x35320, 0x35339); (0x35360, 0x35366);
   (0x35380, 0x35389); (0x353a0, 0x353d9); (0x35400, 0x3540c); (0x35420, 0x35429); (0x35440, 0x35443); (0x35460, 0x35477); (0x354a0, 0x354ba); (0x354e0, 0x354e9);
   (0x35500, 0x35508); (0x35520, 0x35523); (0x35540, 0x3554a); (0x35560, 0x35564); (0x35580, 0x35592); (0x355c0, 0x355c6); (0x355e0, 0x355f1); (0x35620, 0x35641);
   (0x35680, 0x35698); (0x356c0, 0x356e6); (0x35720, 0x3572a); (0x35740, 0x35757); (0x35780, 0x3578b); (0x357a0, 0x357a9); (0x35860, 0x35875); (0x358a0, 0x358b2);
   (0x35920, 0x35935); (0x35960, 0x3596d); (0x35980, 0x35993); (0x35a00, 0x35a15); (0x35a40, 0x35a55); (0x35a80, 0x35a94); (0x35ac0, 0x35acf); (0x35ae0, 0x35af5);
   (0x35b20, 0x35b33); (0x35b60, 0x35b70); (0x35b80, 0x35b9a); (0x35bc0, 0x35be1); (0x35c20, 0x35c33); (0x35c60, 0x35c72); (0x35ca0, 0x35cb0); (0x35cc0, 0x35ccd);
   (0x35ce0, 0x35ce4); (0x35d00, 0x35d1a); (0x35d40, 0x35d50); (0x35d60, 0x35d73); (0x35da0, 0x35db1); (0x35de0, 0x35e12); (0x35e40, 0x35e85); (0x35ec0, 0x35ee9);
   (0x35f20, 0x35f2d); (0x35f40, 0x35f75); (0x35fa0, 0x35fba); (0x36020, 0x36035); (0x36060, 0x36073); (0x360e0, 0x360f3); (0x36120, 0x36132); (0x36160, 0x36170);
   (0x36180, 0x361b3); (0x361e0, 0x361ec); (0x36200, 0x36213); (0x36240, 0x3624f); (0x36260, 0x36273); (0x362a0, 0x362b1); (0x362e0, 0x362f6); (0x36320, 0x36343);
   (0x36380, 0x363bf); (0x363e0, 0x363f8); (0x36460, 0x36467); (0x36480, 0x36491); (0x364c0, 0x364d2); (0x36500, 0x36513); (0x36540, 0x36556); (0x36580, 0x36590);
   (0x365a0, 0x365b0); (0x365c0, 0x365d2); (0x36600, 0x3660e); (0x366e0, 0x366ef); (0x36700, 0x36712); (0x36740, 0x36750); (0x36760, 0x3677c); (0x367a0, 0x367e2);
   (0x36820, 0x36865); (0x368a0, 0x368e6); (0x36920, 0x36931); (0x36960, 0x36972); (0x369a0, 0x369e2); (0x36a20, 0x36a2a); (0x36a40, 0x36a4b); (0x36a60, 0x36a6a);
   (0x36a80, 0x36a8b); (0x36aa0, 0x36ab8); (0x36ae0, 0x36af4); (0x36b20, 0x36b2e); (0x36b40, 0x36b54); (0x36b80, 0x36b88); (0x36be0, 0x36bf3); (0x36c80, 0x36c93);
   (0x36cc0, 0x36cd0); (0x36ce0, 0x36cff); (0x36d20, 0x36d43); (0x36d80, 0x36d95); (0x36dc0, 0x36dd1); (0x36e00, 0x36e13); (0x36e40, 0x36e4e); (0x37160, 0x37175);
   (0x371a0, 0x371af); (0x371c0, 0x371d5); (0x37200, 0x37210); (0x37220, 0x3722d); (0x37240, 0x37251); (0x37280, 0x37292); (0x372c0, 0x372ca); (0x372e0, 0x372ed);
   (0x37300, 0x37305); (0x37320, 0x3733b); (0x37360, 0x37379); (0x373a0, 0x373b9); (0x373e0, 0x373fc); (0x37420, 0x37439); (0x37460, 0x37474); (0x374a0, 0x374b2);
   (0x374e0, 0x374f3); (0x37520, 0x37541); (0x37580, 0x37596); (0x375c0, 0x375eb); (0x37620, 0x3765c); (0x37680, 0x376b0); (0x376e0, 0x3770e); (0x37800, 0x37812);
   (0x37840, 0x37852); (0x37880, 0x37899); (0x378c0, 0x378d0); (0x378e0, 0x378f7); (0x37920, 0x37932); (0x37960, 0x37972); (0x379a0, 0x379c3); (0x37a00, 0x37a0f);
   (0x37a60, 0x37a72); (0x37aa0, 0x37ab4); (0x37ae0, 0x37af4); (0x37b20, 0x37b30); (0x37b40, 0x37b50); (0x37b60, 0x37b6d); (0x37b80, 0x37b8d); (0x37ba0, 0x37bb4);
   (0x37be0, 0x37bf1); (0x37c20, 0x37c2e); (0x37c40, 0x37c52); (0x37c80, 0x37c90); (0x37ca0, 0x37cd4); (0x37d00, 0x37d37); (0x37d60, 0x37d97); (0x37dc0, 0x37dd3);
   (0x37e00, 0x37e13); (0x37e40, 0x37e51); (0x37e80, 0x37e94); (0x37ec0, 0x37ed2); (0x37f00, 0x37f12); (0x37f40, 0x37f53); (0x37f80, 0x37f93); (0x37fc0, 0x37fd2);
   (0x38000, 0x38013); (0x38040, 0x38050); (0x38060, 0x38071); (0x380a0, 0x380df); (0x38100, 0x38117); (0x38140, 0x38152); (0x38180, 0x38191); (0x381c0, 0x381cf);
   (0x381e0, 0x381f2); (0x38220, 0x38251); (0x38280, 0x38293); (0x382c0, 0x382d2); (0x38300, 0x38315); (0x38340, 0x38352); (0x38380, 0x38392); (0x383c0, 0x383d4);
   (0x38400, 0x38412); (0x38440, 0x38459); (0x38480, 0x384ab); (0x384e0, 0x384f4); (0x38520, 0x38535); (0x38560, 0x38572); (0x385a0, 0x385af); (0x385c0, 0x385ce);
   (0x385e0, 0x385f0); (0x38600, 0x3860a); (0x38620, 0x38652); (0x38680, 0x3868c); (0x386a0, 0x386b6); (0x386e0, 0x386fb); (0x38720, 0x38737); (0x38760, 0x3876b);
   (0x38780, 0x387a8); (0x387e0, 0x387f8); (0x38820, 0x3882b); (0x38840, 0x38875); (0x388a0, 0x388b3); (0x388e0, 0x388e6); (0x38900, 0x38905); (0x38920, 0x38922);
   (0x38940, 0x38954); (0x38980, 0x38996); (0x389c0, 0x389d0); (0x389e0, 0x389ee); (0x38ac0, 0x38ad9); (0x38b00, 0x38b2f); (0x38b60, 0x38b6e); (0x38b80, 0x38bb4);
   (0x38be0, 0x38bee); (0x38c00, 0x38c17); (0x38c40, 0x38c68); (0x38ca0, 0x38cb8); (0x38ce0, 0x38d06); (0x38d40, 0x38d45); (0x38d60, 0x38d66); (0x38d80, 0x38dca);
   (0x38e00, 0x38e17); (0x38e40, 0x38e58); (0x38e80, 0x38ea8); (0x38ee0, 0x38ef4); (0x38f20, 0x38f33); (0x38f60, 0x38f8c); (0x38fc0, 0x38fd3); (0x39000, 0x39013);
   (0x39040, 0x39066); (0x390a0, 0x390cb); (0x39100, 0x39115); (0x39140, 0x39155); (0x39180, 0x391d6); (0x39200, 0x39201); (0x39220, 0x39273); (0x392a0, 0x392ae);
   (0x392c0, 0x392d4); (0x39300, 0x3931b); (0x39340, 0x3936f); (0x393a0, 0x393b6); (0x393e0, 0x393f5); (0x39420, 0x39432); (0x39460, 0x39475); (0x394a0, 0x394bf);
   (0x394e0, 0x394f0); (0x39500, 0x39545); (0x395c0, 0x395d2); (0x39600, 0x3960e); (0x39620, 0x39645); (0x39680, 0x3968f); (0x396a0, 0x396af); (0x396c0, 0x396d2);
   (0x39700, 0x39710); (0x39720, 0x39731); (0x39760, 0x39774); (0x397a0, 0x397b0); (0x397c0, 0x397d9); (0x39800, 0x39815); (0x39840, 0x39857); (0x39880, 0x398aa);
   (0x398e0, 0x398f7); (0x39960, 0x39970); (0x39980, 0x3998f); (0x399a0, 0x399b0); (0x399c0, 0x399d4); (0x39a00, 0x39a0f); (0x39a20, 0x39a31); (0x39a60, 0x39a74);
   (0x39aa0, 0x39ab6); (0x39ae0, 0x39aee); (0x39b40, 0x39b84); (0x39bc0, 0x39bcd); (0x39be0, 0x39c12); (0x39c40, 0x39c51); (0x39c80, 0x39ca5); (0x39ce0, 0x39cee);
   (0x39d00, 0x39d11); (0x39d40, 0x39d4d); (0x39d60, 0x39d6b); (0x39d80, 0x39d8d); (0x39da0, 0x39dbb); (0x39e20, 0x39e31); (0x39e60, 0x39e75); (0x39ea0, 0x39ead);
   (0x39ec0, 0x39ed7); (0x39f00, 0x39f3c); (0x39fa0, 0x39fb4); (0x39fe0, 0x39ff9); (0x3a020, 0x3a03e); (0x3a060, 0x3a06d); (0x3a080, 0x3a09e); (0x3a0c0, 0x3a0e2);
   (0x3a120, 0x3a136); (0x3a160, 0x3a17c); (0x3a1a0, 0x3a1b2); (0x3a1e0, 0x3a1f8); (0x3a220, 0x3a237); (0x3a2a0, 0x3a2b0); (0x3a2c0, 0x3a2d1); (0x3a300, 0x3a310);
   (0x3a320, 0x3a32e); (0x3a340, 0x3a350); (0x3a360, 0x3a371); (0x3a3a0, 0x3a3b1); (0x3a3e0, 0x3a3ed); (0x3a400, 0x3a411); (0x3a440, 0x3a454); (0x3a480, 0x3a497);
   (0x3a4c0, 0x3a4cb); (0x3a4e0, 0x3a509); (0x3a540, 0x3a546); (0x3a560, 0x3a58b); (0x3a5c0, 0x3a5ed); (0x3a620, 0x3a658); (0x3a680, 0x3a6b6); (0x3a6e0, 0x3a716);
   (0x3a740, 0x3a779); (0x3a7a0, 0x3a7ca); (0x3a800, 0x3a837); (0x3a860, 0x3a88f); (0x3a8c0, 0x3a8fc); (0x3a920, 0x3a92a); (0x3a940, 0x3a94a); (0x3a960, 0x3a97e);
   (0x3a9a0, 0x3a9e4); (0x3aa20, 0x3aa36); (0x3aa60, 0x3aa85); (0x3aac0, 0x3aae6); (0x3ab20, 0x3ab47); (0x3ab80, 0x3aba5); (0x33d80, 0x33e04); (0x33e40, 0x33ec4);
   (0x343e0, 0x343f4); (0x347a0, 0x347a4); (0x347c0, 0x347cc); (0x34820, 0x34858); (0x357c0, 0x357f8); (0x38a00, 0x38aa0)].
(* [comment removed for export] *)
Definition static_acc (m : mem) : Prop := Forall (fun r => acc asegs m (fst r) (snd r - fst r)) CS_ACC.

(* [comment removed for export] *)
Definition shadow_rep (L : layoutA) (m : mem) : Prop :=
  bytes_at asegs m (shad (l_ACEIL L)) (zrun ((2 ^ 47 - l_ACEIL L) / 8))
  /\ stk asegs m (shad (l_ACEIL L)) (shad (2 ^ 47))
  /\ stk asegs m (pg_dn (shad 0x10000)) (shad SEGTOP_A)
  /\ static_acc m.

(* [comment removed for export] *)
Definition shreg (z : Z) : Prop := (K_LOW_SHADOW_lo <= z < K_LOW_SHADOW_hi) \/ (K_HIGH_SHADOW_lo <= z < K_HIGH_SHADOW_hi).
(* [comment removed for export] *)
Definition vis_rep (L : layoutA) (A : list (Z * Z)) (m : mem) : Prop :=
  forall a : word, shreg (bv_unsigned a) -> page_allowedb A (page_base a) = true ->
    bv_unsigned a < shad (pg_dn (l_ACEIL L)) ->
    (forall e, In e (l_maps0 L) -> ~ (shad (bv_unsigned (fst e)) <= bv_unsigned a < shad (bv_unsigned (fst e) + bv_unsigned (snd e)))) ->
    m a <> None.

(* [comment removed for export] *)
Lemma vis_rep_wmono : forall {L} A (m m' : mem), vis_rep L A m -> wmono asegs m m' -> vis_rep L A m'.
Proof.
  intros L A m m' H WM a Hs Hp Hlo Hx. pose proof (H a Hs Hp Hlo Hx) as Ha.
  assert (NS : find_segment asegs (bv_unsigned a) 1 = None).
  { unfold asegs, Asan.M.loaded_segments, Asan.Asan_loaded_segments.
    cbn [find_segment].
    unfold Asan.Asan_segment_000, Asan.Asan_segment_001,
      Asan.Asan_segment_002, Asan.Asan_segment_003.
    cbn [seg_base seg_size]. unfold shreg, K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in Hs.
    destruct Hs as [Hs|Hs];
      repeat match goal with |- context [Z.leb ?x ?y] =>
        first [ rewrite (proj2 (Z.leb_le x y)) by lia | rewrite (proj2 (Z.leb_gt x y)) by lia ]; cbn [andb] end; reflexivity. }
  assert (W0 : wview asegs m a <> None) by (unfold wview; destruct (m a); [discriminate | congruence]).
  pose proof (WM a W0) as W1. unfold wview in W1. destruct (m' a) eqn:E; [discriminate|]. rewrite NS in W1. exact W1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ART_A (Σ : rtsA) (m : mem) : Prop :=
  rt_wf Σ /\ consts_rep (lay Σ) m /\ prim_rep Σ m /\ cache_rep Σ m /\ chunk_rep Σ m /\ sec_rep Σ m /\ quar_rep Σ m
  /\ dep_rep (lay Σ) (dep Σ) m /\ fs_rep Σ m /\ ia_rep Σ m /\ shadow_rep (lay Σ) m /\ vis_rep (lay Σ) (rtA_allow Σ) m.

(* [comment removed for export] *)
Definition lazy_in_maps_A (mo : Model) : Prop :=
  forall iv, In iv (m_vm_lazy mo) -> 0 < bv_unsigned (snd iv) ->
    exists e, In e (vm_maps (m_vmmaps mo)) /\ bv_unsigned (fst e) <= bv_unsigned (fst iv)
              /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= bv_unsigned (fst e) + bv_unsigned (snd e).
Definition iv_apart (p q : word * word) : Prop :=
  bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned (fst q) \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst p).
(* [comment removed for export] *)
Definition confined0 (Σ : rtsA) (mo : Model) : Prop :=
  forall z, BackingAlgebra.covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) z = true -> BackingAlgebra.covered (l_maps0 (lay Σ)) z = true.
(* [comment removed for export] *)
Definition shadow_lazy (mo : Model) : Prop :=
  forall a : word, shreg (bv_unsigned a) ->
    page_in_ranges (page_base a) (m_vm_lazy mo) = true /\ BackingAlgebra.covered (vm_noaccess (m_vmmaps mo)) (bv_unsigned a) = false.
(* [comment removed for export] *)
Definition maps_zbound (mo : Model) : Prop :=
  Z.of_nat (length (vm_maps (m_vmmaps mo))) <= Z.of_nat (length (List.filter vpos (vm_maps (m_vmmaps mo)))) + 1.
Definition artm_sys (Σ : rtsA) (mo : Model) : Prop :=
  BackingAlgebra.model_ivs_wf mo /\ lazy_in_maps_A mo /\ ForallOrdPairs iv_apart (vm_maps (m_vmmaps mo))
  /\ bv_unsigned (vm_init_sp (m_vmmaps mo)) = l_sp0 (lay Σ) /\ confined0 Σ mo /\ shadow_lazy mo /\ maps_zbound mo
  (* [comment removed for export] *)
  /\ NodesA_madv.noaccess_pos mo.

(* [comment removed for export] *)
Definition ARTM_A (Σ : rtsA) (mo : Model) : Prop :=
  Permutation (List.filter vpos (vm_maps (m_vmmaps mo))) (rt_maps Σ) /\ vm_reserved (m_vmmaps mo) = segments_reserved asegs
  /\ vm_limit (m_vmmaps mo) = VMLIMIT /\ eager_used mo <= E0_MAX + rt_eager Σ /\ artm_sys Σ mo.

Definition RTA : rt_sig := mkRTS rtsA ART_A ARTM_A rtA_live rtA_frames rtA_allow rtA_sp0 rtA_credit.

(* [comment removed for export] *)
Lemma filter_map_remove : forall (l : list (word * word)) (a : word), List.filter vpos (map_remove l a) = map_remove (List.filter vpos l) a.
Proof.
  intros l a. unfold map_remove. induction l as [|e l IH]; [reflexivity|]. cbn [List.filter].
  destruct (negb (bv_eqb (fst e) a)) eqn:Eb; destruct (vpos e) eqn:Ev; cbn [List.filter]; rewrite ?Eb, ?Ev, IH; reflexivity.
Qed.

Lemma perm_filter' : forall {T : Type} (f : T -> bool) (l l' : list T), Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
  intros T f l l' H. induction H as [|x l l' H IH|x y l|l l' l'' H1 IH1 H2 IH2]; cbn [List.filter].
  - constructor.
  - destruct (f x); [constructor; exact IH | exact IH].
  - destruct (f x); destruct (f y); cbn [List.filter]; [apply perm_swap | apply Permutation_refl | apply Permutation_refl | apply Permutation_refl].
  - exact (Permutation_trans IH1 IH2).
Qed.

Lemma perm_map_remove : forall (l l' : list (word * word)) (a : word), Permutation l l' -> Permutation (map_remove l a) (map_remove l' a).
Proof. intros l l' a H. unfold map_remove. apply perm_filter'. exact H. Qed.

Lemma filter_cons_pos : forall (e : word * word) (l : list (word * word)), 0 < bv_unsigned (snd e) -> List.filter vpos (e :: l) = e :: List.filter vpos l.
Proof. intros e l H. cbn [List.filter]. unfold vpos. rewrite (proj2 (Z.ltb_lt 0 _) H). reflexivity. Qed.

Lemma filter_vpos_pos : forall (l : list (word * word)), Forall (fun e => 0 < bv_unsigned (snd e)) (List.filter vpos l).
Proof.
  intros l. apply Forall_forall. intros e He. apply List.filter_In in He as [_ He]. unfold vpos in He. apply Z.ltb_lt in He. exact He.
Qed.

Lemma filter_vpos_id : forall (l : list (word * word)), Forall (fun e => 0 < bv_unsigned (snd e)) l -> List.filter vpos l = l.
Proof.
  intros l H. induction H as [|e l He _ IH]; [reflexivity|]. rewrite (filter_cons_pos e l He), IH. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma covered_filter_vpos : forall (l : list (word * word)) (z : Z), BackingAlgebra.covered (List.filter vpos l) z = BackingAlgebra.covered l z.
Proof.
  intros l z. induction l as [|e l IH]; [reflexivity|]. cbn [List.filter]. destruct (vpos e) eqn:Ev.
  - unfold BackingAlgebra.covered in *. cbn [existsb]. rewrite IH. reflexivity.
  - unfold BackingAlgebra.covered in *. cbn [existsb]. rewrite IH. unfold vpos in Ev. apply Z.ltb_ge in Ev.
    pose proof (bv_unsigned_in_range _ (snd e)) as Hr. unfold BackingAlgebra.in_iv, BackingAlgebra.in_rng, BackingAlgebra.B, BackingAlgebra.S.
    replace (bv_unsigned (snd e)) with 0 by (unfold bv_modulus in Hr; lia).
    destruct (bv_unsigned (fst e) <=? z) eqn:E1; destruct (z <? bv_unsigned (fst e) + 0) eqn:E2; cbn [andb orb]; try reflexivity.
    apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.

(* [comment removed for export] *)
Lemma vis_premise_filter : forall (l : list (word * word)) (x : Z),
  (forall e, In e (List.filter vpos l) -> ~ (shad (bv_unsigned (fst e)) <= x < shad (bv_unsigned (fst e) + bv_unsigned (snd e)))) ->
  forall e, In e l -> ~ (shad (bv_unsigned (fst e)) <= x < shad (bv_unsigned (fst e) + bv_unsigned (snd e))).
Proof.
  intros l x H e He. destruct (vpos e) eqn:Ev.
  - exact (H e (proj2 (List.filter_In _ _ _) (conj He Ev))).
  - unfold vpos in Ev. apply Z.ltb_ge in Ev. pose proof (bv_unsigned_in_range _ (snd e)) as Hr.
    replace (bv_unsigned (snd e)) with 0 by (unfold bv_modulus in Hr; lia). rewrite Z.add_0_r. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Proj.
Variables (Σ : rtsA) (m : mem).
Hypothesis HA : ART_A Σ m.
Lemma ART_wf : rt_wf Σ. Proof. exact (proj1 HA). Qed.
Lemma ART_consts : consts_rep (lay Σ) m. Proof. exact (proj1 (proj2 HA)). Qed.
Lemma ART_prim : prim_rep Σ m. Proof. exact (proj1 (proj2 (proj2 HA))). Qed.
Lemma ART_cache : cache_rep Σ m. Proof. exact (proj1 (proj2 (proj2 (proj2 HA)))). Qed.
Lemma ART_chunk : chunk_rep Σ m. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 HA))))). Qed.
Lemma ART_sec : sec_rep Σ m. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HA)))))). Qed.
Lemma ART_quar : quar_rep Σ m. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HA))))))). Qed.
Lemma ART_dep : dep_rep (lay Σ) (dep Σ) m. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HA)))))))). Qed.
Lemma ART_fs : fs_rep Σ m. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HA))))))))). Qed.
Lemma ART_ia : ia_rep Σ m. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HA)))))))))). Qed.
Lemma ART_shadow : shadow_rep (lay Σ) m. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HA))))))))))). Qed.
Lemma ART_vis : vis_rep (lay Σ) (rtA_allow Σ) m. Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HA))))))))))). Qed.
End Proj.

Lemma ART_intro : forall Σ m, rt_wf Σ -> consts_rep (lay Σ) m -> prim_rep Σ m -> cache_rep Σ m -> chunk_rep Σ m ->
  sec_rep Σ m -> quar_rep Σ m -> dep_rep (lay Σ) (dep Σ) m -> fs_rep Σ m -> ia_rep Σ m -> shadow_rep (lay Σ) m ->
  vis_rep (lay Σ) (rtA_allow Σ) m -> ART_A Σ m.
Proof. intros. unfold ART_A. repeat (split; [assumption|]). assumption. Qed.
