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
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require NodesA_madv.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import AsanAcct.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import RT_iface.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import R_sizeclass.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import R_cache_defs R_prim_defs R_thread R_m2s R_poison R_leaves R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state TopA_iodefs.
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
  /\ ro_cells asegs m 0x27675d [C1 (Z_to_bv 8 0)] /\ ro_cells asegs m 0x276764 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x1cf3f8 [C8 (Z_to_bv 64 0x1e2338)] /\ ro_cells asegs m 0x1cf428 [C8 (Z_to_bv 64 0x1d14f8)]
  /\ ro_cells asegs m 0x1d14f8 [C8 (Z_to_bv 64 0x1c17c8)] /\ ro_cells asegs m 0x1e2355 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x1e583c [C4 (Z_to_bv 64 30)] /\ ro_cells asegs m 0x27668a [C1 (Z_to_bv 8 1)]
  (* [comment removed for export] *)
  /\ ro_cells asegs m 0x1d0088 [C8 (Z_to_bv 64 0x1d3c40)] /\ ro_cells asegs m 0x1d0238 [C8 (Z_to_bv 64 0x737ef8)]
  (* [comment removed for export] *)
  /\ ro_cells asegs m 0x1cff70 [C8 (Z_to_bv 64 0x1e5819)] /\ ro_cells asegs m 0x1e5819 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x1d1500 [C8 (Z_to_bv 64 0x1c1bfc)] /\ ro_cells asegs m 0x1d1318 [C8 (Z_to_bv 64 0x1c16cc)]
  /\ ro_cells asegs m 0x1d14a8 [C8 (Z_to_bv 64 0x1c2178)] /\ ro_cells asegs m 0x1d12e8 [C8 (Z_to_bv 64 0x1c1f34)]
  /\ ro_cells asegs m 0x276763 [C1 (Z_to_bv 8 1)]    (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0x1e22f8 [C8 (Z_to_bv 64 (2 ^ 40))] /\ rw_cells asegs m 0x1e2300 [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)]
  /\ rw_cells asegs m 0x266da2 [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m 0x27668a [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x1cf3f8 [C8 (Z_to_bv 64 0x1e2338)] /\ rw_cells asegs m (0x1e2338 + 44) [C4 (Z_to_bv 64 4096)]
  /\ rw_cells asegs m (0x1e2338 + 52) [C4 (Z_to_bv 64 190)] /\ rw_cells asegs m (0x1e2338 + 85) [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m (0x717eb8 + 32) [C4 (Z_to_bv 64 0)] /\ rw_cells asegs m 0x1d0068 [C8 (Z_to_bv 64 32)]
  /\ rw_cells asegs m 0x276600 [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m 0x1e439c [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m (l_TCX L + 8) [C4 (Z_to_bv 64 0)]
  /\ stk asegs m (l_T L + 2768) (l_T L + 3168)
  (* [comment removed for export] *)
  /\ rw_cells asegs m (l_T L) [C8 (Z_to_bv 64 (l_TCX L))]
  (* [comment removed for export] *)
  /\ rw_cells asegs m (g_MFHooks + 8) [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m i_q_max [C8 (Z_to_bv 64 0x10000000); C8 (Z_to_bv 64 0xE666661); C8 (Z_to_bv 64 0x100000)]
  /\ rw_cells asegs m (g_asan_flags + 48) [C4 (Z_to_bv 64 0)]
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0x1cf440 [C8 (Z_to_bv 64 1)] /\ rw_cells asegs m 0x276743 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x27675c [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m 0x1d0238 [C8 (Z_to_bv 64 0x737ef8)]
  /\ rw_cells asegs m 0x738178 [C8 (Z_to_bv 64 4096)]
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
  [(0x1d3a10, 0x1d3c44); (0x1d3c60, 0x1d3c68); (0x1d3c80, 0x1d3c84); (0x1d3ca0, 0x1d3ca8); (0x1d3cc0, 0x1d3cc8); (0x1d3ce0, 0x1d3ce8); (0x1d3d00, 0x1d3d04); (0x1d3d20, 0x1d3d24); (0x1d3d40, 0x1e14d8);
   (0x707190, 0x717190);
   (0x717190, 0x717e60); (0x717e68, 0x717eb0);
   (0x717ee0, 0x717ee8); (0x717ef8, 0x738178); (0x738180, 0x739260); (0x739268, 0x739798)].
(* [comment removed for export] *)
Definition CS_ACC : list (Z * Z) :=
  [(0x1d3a10, 0x1d3c44); (0x1d3c60, 0x1d3c68); (0x1d3c80, 0x1d3c84); (0x1d3ca0, 0x1d3ca8); (0x1d3cc0, 0x1d3cc8); (0x1d3ce0, 0x1d3ce8); (0x1d3d00, 0x1d3d04); (0x1d3d20, 0x1d3d24); (0x1d3d40, 0x1d4090); (0x1e1450, 0x1e14f8);
   (0x707190, 0x717190);
   (0x717190, 0x717e60); (0x717e68, 0x717eb0);
   (0x717ee0, 0x717ee8); (0x717ef8, 0x739260); (0x739268, 0x739798);
   (* [comment removed for export] *)
   (0x30ce0, 0x30cee); (0x30d00, 0x30d0a); (0x30d20, 0x30d30); (0x30d40, 0x30d5d); (0x30e40, 0x30e67); (0x30ea0, 0x30eb0); (0x30ec0, 0x30ed2); (0x30f00, 0x30f13); (0x30fa0, 0x30fac); (0x30fc0, 0x30fd8); (0x311a0, 0x311ab); (0x31340, 0x31350); (0x31360, 0x3136c); (0x313e0, 0x313ed); (0x31440, 0x3144c); (0x314a0, 0x314b1); (0x31560, 0x3156a); (0x316c0, 0x316cf); (0x316e0, 0x316f6); (0x31760, 0x3176b); (0x31960, 0x31970); (0x31b40, 0x31b4e); (0x322a0, 0x322af); (0x322c0, 0x322d3); (0x32300, 0x3230f); (0x32320, 0x32331); (0x32360, 0x32377); (0x326c0, 0x326d6); (0x32700, 0x3270f); (0x32ac0, 0x32ad1); (0x32c40, 0x32c4f); (0x32c60, 0x32c7d); (0x32ca0, 0x32cab); (0x32cc0, 0x32cce); (0x32da0, 0x32db1); (0x32ea0, 0x32eb6); (0x32ee0, 0x32ef4); (0x32f20, 0x32f45); (0x33a80, 0x33a93); (0x33ac0, 0x33ac8); (0x33ae0, 0x33af0); (0x36ba0, 0x36bad); (0x36bc0, 0x36bd1); (0x36de0, 0x36df9); (0x36e80, 0x36e92); (0x36ec0, 0x36ece); (0x36ee0, 0x36eef); (0x36f00, 0x36f0f); (0x36f20, 0x36f30); (0x36f40, 0x36f56); (0x37000, 0x3700e); (0x37020, 0x37032); (0x37060, 0x37079); (0x2dca0, 0x2dcb1); (0x30f40, 0x30f6f); (0x31000, 0x31030); (0x31060, 0x31094); (0x310c0, 0x310f5); (0x31140, 0x31165); (0x32240, 0x32265); (0x31b60, 0x31b7b); (0x323a0, 0x323c5); (0x32400, 0x3242f); (0x32460, 0x3248e); (0x324c0, 0x324df); (0x32500, 0x32533); (0x32560, 0x32598); (0x325c0, 0x325fa); (0x32620, 0x3266d); (0x36e20, 0x36e43); (0x36f80, 0x36fd4); (0x31ba0, 0x31c24);
   (* [comment removed for export] *)
   (0x114bb, 0x114c5); (0x177bb, 0x177bf); (0x19380, 0x19400); (0x203bc, 0x203dd); (0x27a98, 0x27aad); (0x27aad, 0x27ac4);
   (0x2b540, 0x2b5c0); (0x2d450, 0x2d457); (0x2dc18, 0x2dc28); (0x707180, 0x707190);
   (* [comment removed for export] *)
   (0x2dce0, 0x2dcff); (0x2dd20, 0x2dd32); (0x2dd60, 0x2dd76); (0x2dda0, 0x2ddb3); (0x2dde0, 0x2ddf4); (0x2de20, 0x2de32); (0x2de60, 0x2de6d); (0x2de80, 0x2de8e);
   (0x2dea0, 0x2deb3); (0x2dee0, 0x2deed); (0x2df00, 0x2df0d); (0x2df60, 0x2df80); (0x2dfa0, 0x2dfaa); (0x2dfc0, 0x2dfce); (0x2dfe0, 0x2dff1); (0x2e020, 0x2e02b);
   (0x2e040, 0x2e052); (0x2e080, 0x2e08e); (0x2e0a0, 0x2e0b4); (0x2e0e0, 0x2e0ed); (0x2e100, 0x2e12e); (0x2e160, 0x2e16a); (0x2e180, 0x2e198); (0x2e1c0, 0x2e1da);
   (0x2e200, 0x2e211); (0x2e240, 0x2e24b); (0x2e260, 0x2e275); (0x2e2a0, 0x2e2af); (0x2e2c0, 0x2e2e1); (0x2e320, 0x2e332); (0x2e360, 0x2e37f); (0x2e3a0, 0x2e3b7);
   (0x2e3e0, 0x2e3eb); (0x2e400, 0x2e411); (0x2e440, 0x2e454); (0x2e480, 0x2e48d); (0x2e4a0, 0x2e4b5); (0x2e4e0, 0x2e4f7); (0x2e520, 0x2e534); (0x2e560, 0x2e573);
   (0x2e5a0, 0x2e5af); (0x2e5c0, 0x2e5e3); (0x2e620, 0x2e633); (0x2e660, 0x2e679); (0x2e6a0, 0x2e6b3); (0x2e6e0, 0x2e70e); (0x2e740, 0x2e755); (0x2e780, 0x2e7b1);
   (0x2e7e0, 0x2e7f2); (0x2e820, 0x2e830); (0x2e840, 0x2e84e); (0x2e860, 0x2e87a); (0x2e8a0, 0x2e8ae); (0x2e8c0, 0x2e8d2); (0x2e900, 0x2e90d); (0x2e920, 0x2e930);
   (0x2e940, 0x2e952); (0x2e980, 0x2e983); (0x2e9a0, 0x2e9e1); (0x2ea20, 0x2ea2f); (0x2ea40, 0x2ea51); (0x2ea80, 0x2eaa2); (0x2eae0, 0x2eae2); (0x2eb00, 0x2eb05);
   (0x2eb20, 0x2eb3c); (0x2eb60, 0x2eb6c); (0x2eb80, 0x2eb9c); (0x2ebc0, 0x2ebd5); (0x2ec00, 0x2ec15); (0x2ec40, 0x2ec41); (0x2ec60, 0x2ec75); (0x2eca0, 0x2eca9);
   (0x2ecc0, 0x2ecd7); (0x2ed00, 0x2ed11); (0x2ed40, 0x2ed56); (0x2ed80, 0x2ed89); (0x2eda0, 0x2edac); (0x2edc0, 0x2edd5); (0x2ee00, 0x2ee11); (0x2ee40, 0x2ee51);
   (0x2ee80, 0x2ee93); (0x2eec0, 0x2eed0); (0x2eee0, 0x2ef0e); (0x2ef40, 0x2ef57); (0x2ef80, 0x2ef93); (0x2efc0, 0x2efcd); (0x2efe0, 0x2efef); (0x2f040, 0x2f056);
   (0x2f080, 0x2f08c); (0x2f0a0, 0x2f0c4); (0x2f100, 0x2f10d); (0x2f120, 0x2f12f); (0x2f140, 0x2f14f); (0x2f160, 0x2f171); (0x2f1a0, 0x2f1ae); (0x2f1c0, 0x2f1db);
   (0x2f200, 0x2f211); (0x2f240, 0x2f24f); (0x2f260, 0x2f270); (0x2f280, 0x2f292); (0x2f2c0, 0x2f2cf); (0x2f2e0, 0x2f2ef); (0x2f300, 0x2f30f); (0x2f320, 0x2f331);
   (0x2f360, 0x2f381); (0x2f400, 0x2f414); (0x2f440, 0x2f44e); (0x2f460, 0x2f484); (0x2f4c0, 0x2f4cf); (0x2f4e0, 0x2f4fa); (0x2f520, 0x2f540); (0x2f560, 0x2f589);
   (0x2f5c0, 0x2f5cf); (0x2f5e0, 0x2f5ec); (0x2f600, 0x2f610); (0x2f620, 0x2f631); (0x2f660, 0x2f671); (0x2f6a0, 0x2f6b3); (0x2f6e0, 0x2f6fb); (0x2f720, 0x2f72d);
   (0x2f740, 0x2f751); (0x2f780, 0x2f79c); (0x2f7c0, 0x2f7d2); (0x2f840, 0x2f853); (0x2f880, 0x2f88d); (0x2f8a0, 0x2f8c5); (0x2f900, 0x2f90e); (0x2f920, 0x2f92f);
   (0x2f940, 0x2f950); (0x2f960, 0x2f973); (0x2f9a0, 0x2f9b1); (0x2f9e0, 0x2f9f1); (0x2fa20, 0x2fa2f); (0x2fa40, 0x2fa50); (0x2fa60, 0x2fa70); (0x2fa80, 0x2fa8f);
   (0x2faa0, 0x2fab4); (0x2fae0, 0x2faf2); (0x2fb20, 0x2fb21); (0x2fb40, 0x2fb42); (0x2fb60, 0x2fb62); (0x2fb80, 0x2fb82); (0x2fba0, 0x2fbb0); (0x2fbc0, 0x2fbce);
   (0x2fbe0, 0x2fbee); (0x2fc00, 0x2fc12); (0x2fc40, 0x2fc50); (0x2fc60, 0x2fc77); (0x2fca0, 0x2fcb2); (0x2fce0, 0x2fd05); (0x2fd40, 0x2fd5b); (0x2fdc0, 0x2fdd0);
   (0x2fde0, 0x2fdf0); (0x2fe00, 0x2fe0a); (0x2fe60, 0x2fe76); (0x2fea0, 0x2feab); (0x2fec0, 0x2fee4); (0x2ff20, 0x2ff2c); (0x2ff40, 0x2ff4f); (0x2ff60, 0x2ff6e);
   (0x2ff80, 0x2ff91); (0x2ffc0, 0x2ffcd); (0x2ffe0, 0x2fffb); (0x30020, 0x30031); (0x30060, 0x3006e); (0x30080, 0x30090); (0x300a0, 0x300b2); (0x300e0, 0x300ee);
   (0x30100, 0x30110); (0x30120, 0x30135); (0x30160, 0x3017c); (0x30220, 0x30230); (0x30240, 0x30249); (0x30260, 0x30272); (0x302a0, 0x302a4); (0x302c0, 0x302d2);
   (0x30300, 0x3031a); (0x30340, 0x30353); (0x30380, 0x3038f); (0x303a0, 0x303af); (0x30400, 0x30416); (0x30440, 0x3044a); (0x30460, 0x30478); (0x304a0, 0x304b8);
   (0x304e0, 0x304f0); (0x30500, 0x30525); (0x30560, 0x3056b); (0x30580, 0x3058f); (0x305a0, 0x305af); (0x30600, 0x30624); (0x30660, 0x3066b); (0x30680, 0x30693);
   (0x306c0, 0x306e4); (0x30720, 0x3072c); (0x30740, 0x3077a); (0x307a0, 0x307af); (0x307c0, 0x307c8); (0x307e0, 0x307f1); (0x30820, 0x30832); (0x30860, 0x3086b);
   (0x30880, 0x3089a); (0x308c0, 0x308d1); (0x30900, 0x3091e); (0x30940, 0x30950); (0x30960, 0x3097b); (0x309e0, 0x309fd); (0x30a20, 0x30a2a); (0x30a40, 0x30a65);
   (0x30aa0, 0x30aab); (0x30ac0, 0x30ad0); (0x30ae0, 0x30ae9); (0x30b00, 0x30b11); (0x30b40, 0x30b49); (0x30b60, 0x30b6e); (0x30b80, 0x30b89); (0x30ba0, 0x30bb0);
   (0x30bc0, 0x30be2); (0x30c20, 0x30c39); (0x30c60, 0x30c79); (0x30d80, 0x30d91); (0x30dc0, 0x30dd2); (0x30e00, 0x30e18); (0x31120, 0x31129); (0x311c0, 0x311c8);
   (0x311e0, 0x311fc); (0x31220, 0x31233); (0x31260, 0x31271); (0x312a0, 0x312b0); (0x312c0, 0x312df); (0x31300, 0x3130f); (0x31320, 0x3132f); (0x31380, 0x3138c);
   (0x313a0, 0x313b3); (0x31400, 0x3140d); (0x31420, 0x3142f); (0x31460, 0x3146c); (0x31480, 0x3148f); (0x314e0, 0x314ea); (0x31500, 0x3150a); (0x31520, 0x31531);
   (0x31580, 0x3158b); (0x315a0, 0x315ab); (0x315c0, 0x315d2); (0x31600, 0x31612); (0x31640, 0x31653); (0x31680, 0x3168b); (0x316a0, 0x316af); (0x31720, 0x31733);
   (0x31900, 0x31911); (0x31940, 0x3194c); (0x31980, 0x319a5); (0x319e0, 0x319ec); (0x31a00, 0x31a11); (0x31a40, 0x31a53); (0x31a80, 0x31ab8); (0x31ae0, 0x31b20);
   (0x31c60, 0x31c6e); (0x31c80, 0x31c93); (0x31cc0, 0x31cd0); (0x31ce0, 0x31ced); (0x31d00, 0x31d17); (0x31d40, 0x31d51); (0x31d80, 0x31d9d); (0x31dc0, 0x31dd1);
   (0x31e00, 0x31e13); (0x31e40, 0x31e50); (0x31e60, 0x31e71); (0x31ea0, 0x31eb5); (0x31ee0, 0x31ef2); (0x31f20, 0x31f38); (0x31f60, 0x31f83); (0x31fc0, 0x31fd1);
   (0x32000, 0x3201d); (0x32040, 0x32053); (0x320c0, 0x320d7); (0x32100, 0x3210e); (0x32120, 0x32136); (0x32160, 0x32174); (0x321a0, 0x321b0); (0x321c0, 0x321d2);
   (0x32200, 0x3220c); (0x32220, 0x3222d); (0x326a0, 0x326b0); (0x32720, 0x32730); (0x32740, 0x32764); (0x327a0, 0x327b0); (0x327c0, 0x327d4); (0x32800, 0x3282b);
   (0x32860, 0x3286f); (0x32880, 0x32893); (0x328c0, 0x328d0); (0x328e0, 0x328f9); (0x32920, 0x32934); (0x32960, 0x32970); (0x32980, 0x3299b); (0x329c0, 0x329d8);
   (0x32a00, 0x32a17); (0x32a40, 0x32a52); (0x32a80, 0x32a95); (0x32b00, 0x32b12); (0x32b40, 0x32b64); (0x32ba0, 0x32bb0); (0x32bc0, 0x32bd9); (0x32c00, 0x32c15);
   (0x32ce0, 0x32cf4); (0x32d20, 0x32d2a); (0x32d40, 0x32d45); (0x32de0, 0x32df5); (0x32e20, 0x32e38); (0x32e60, 0x32e7f); (0x33160, 0x33171); (0x331a0, 0x331af);
   (0x331c0, 0x331ce); (0x331e0, 0x331f2); (0x33220, 0x33256); (0x33280, 0x3329b); (0x332c0, 0x332e0); (0x33300, 0x33319); (0x33340, 0x33377); (0x333a0, 0x333bc);
   (0x333e0, 0x3340a); (0x33440, 0x3345e); (0x33480, 0x33494); (0x334c0, 0x334cd); (0x334e0, 0x334f7); (0x33520, 0x33534); (0x33560, 0x33570); (0x33580, 0x335bb);
   (0x335e0, 0x335f0); (0x33600, 0x33610); (0x33620, 0x3362f); (0x33640, 0x33652); (0x33680, 0x33690); (0x336a0, 0x336b0); (0x336c0, 0x336d3); (0x33700, 0x3370f);
   (0x33720, 0x3372f); (0x33740, 0x3374f); (0x33760, 0x3376f); (0x33780, 0x3378f); (0x337a0, 0x337af); (0x337c0, 0x337dd); (0x33800, 0x3380e); (0x33820, 0x3382f);
   (0x33840, 0x33861); (0x338a0, 0x338b0); (0x338c0, 0x338d1); (0x33900, 0x33910); (0x33920, 0x33934); (0x33960, 0x33982); (0x33a00, 0x33a11); (0x33a40, 0x33a4a);
   (0x33a60, 0x33a6e); (0x33b40, 0x33b51); (0x33b80, 0x33b8c); (0x33ba0, 0x33bb1); (0x33be0, 0x33bff); (0x33e80, 0x33ea2); (0x33ee0, 0x33ef6); (0x33f20, 0x33f36);
   (0x33fa0, 0x33fb2); (0x33fe0, 0x33ff2); (0x34020, 0x34031); (0x34060, 0x34075); (0x340a0, 0x340b8); (0x340e0, 0x340ef); (0x34100, 0x34119); (0x34140, 0x3415d);
   (0x34180, 0x34190); (0x341a0, 0x341b5); (0x341e0, 0x34212); (0x34280, 0x34295); (0x342c0, 0x342d4); (0x34300, 0x3430f); (0x34320, 0x3432f); (0x34340, 0x3434e);
   (0x343e0, 0x343f3); (0x34420, 0x3442d); (0x34440, 0x34465); (0x344a0, 0x344a6); (0x344c0, 0x344e1); (0x34560, 0x34573); (0x345a0, 0x345b4); (0x345e0, 0x345f5);
   (0x34620, 0x3462f); (0x34640, 0x34666); (0x346a0, 0x346b5); (0x346e0, 0x346f8); (0x34760, 0x34771); (0x34860, 0x34875); (0x348a0, 0x348b3); (0x348e0, 0x348e2);
   (0x34900, 0x3490f); (0x34920, 0x34930); (0x34940, 0x34942); (0x34960, 0x34975); (0x349a0, 0x349cb); (0x34a00, 0x34a48); (0x34a80, 0x34a90); (0x34aa0, 0x34ab2);
   (0x34ae0, 0x34ae3); (0x34b00, 0x34b16); (0x34b40, 0x34b4d); (0x34b60, 0x34b6f); (0x34b80, 0x34bad); (0x34be0, 0x34c01); (0x34c40, 0x34c52); (0x34c80, 0x34c96);
   (0x34cc0, 0x34cd4); (0x34d00, 0x34d12); (0x34d40, 0x34d56); (0x34d80, 0x34d94); (0x34dc0, 0x34dd9); (0x34e00, 0x34e1a); (0x34e40, 0x34e50); (0x34e60, 0x34e71);
   (0x34ea0, 0x34ebc); (0x34ee0, 0x34f02); (0x34f40, 0x34f69); (0x34fa0, 0x34fb3); (0x34fe0, 0x34ff5); (0x35020, 0x35057); (0x35080, 0x350bd); (0x350e0, 0x35115);
   (0x35140, 0x35165); (0x351a0, 0x351b8); (0x351e0, 0x351f4); (0x35220, 0x35237); (0x35260, 0x35279); (0x352a0, 0x352b9); (0x352e0, 0x352e6); (0x35300, 0x35309);
   (0x35320, 0x35359); (0x35380, 0x3538c); (0x353a0, 0x353a9); (0x353c0, 0x353c3); (0x353e0, 0x353f7); (0x35420, 0x3543a); (0x35460, 0x35469); (0x35480, 0x35488);
   (0x354a0, 0x354a3); (0x354c0, 0x354ca); (0x354e0, 0x354e4); (0x35500, 0x35512); (0x35540, 0x35546); (0x35560, 0x35571); (0x355a0, 0x355c1); (0x35600, 0x35618);
   (0x35640, 0x35666); (0x356a0, 0x356aa); (0x356c0, 0x356d7); (0x35700, 0x3570b); (0x35720, 0x35729); (0x357e0, 0x357f5); (0x35820, 0x35832); (0x358a0, 0x358b5);
   (0x358e0, 0x358ed); (0x35900, 0x35913); (0x35980, 0x35995); (0x359c0, 0x359d5); (0x35a00, 0x35a14); (0x35a40, 0x35a4f); (0x35a60, 0x35a75); (0x35aa0, 0x35ab3);
   (0x35ae0, 0x35af0); (0x35b00, 0x35b1a); (0x35b40, 0x35b61); (0x35ba0, 0x35bb3); (0x35be0, 0x35bf2); (0x35c20, 0x35c30); (0x35c40, 0x35c4d); (0x35c60, 0x35c64);
   (0x35c80, 0x35c9a); (0x35cc0, 0x35cd0); (0x35ce0, 0x35cf3); (0x35d20, 0x35d31); (0x35d60, 0x35d92); (0x35dc0, 0x35e05); (0x35e40, 0x35e69); (0x35ea0, 0x35ead);
   (0x35ec0, 0x35ef5); (0x35f20, 0x35f3a); (0x35fa0, 0x35fb5); (0x35fe0, 0x35ff3); (0x36060, 0x36073); (0x360a0, 0x360b2); (0x360e0, 0x360f0); (0x36100, 0x36133);
   (0x36160, 0x3616c); (0x36180, 0x36193); (0x361c0, 0x361cf); (0x361e0, 0x361f3); (0x36220, 0x36231); (0x36260, 0x36276); (0x362a0, 0x362c3); (0x36300, 0x3633f);
   (0x36360, 0x36378); (0x363e0, 0x363e7); (0x36400, 0x36411); (0x36440, 0x36452); (0x36480, 0x36493); (0x364c0, 0x364d6); (0x36500, 0x36510); (0x36520, 0x36530);
   (0x36540, 0x36552); (0x36580, 0x3658e); (0x36660, 0x3666f); (0x36680, 0x36692); (0x366c0, 0x366d0); (0x366e0, 0x366fc); (0x36720, 0x36762); (0x367a0, 0x367e5);
   (0x36820, 0x36866); (0x368a0, 0x368b1); (0x368e0, 0x368f2); (0x36920, 0x36962); (0x369a0, 0x369aa); (0x369c0, 0x369cb); (0x369e0, 0x369ea); (0x36a00, 0x36a0b);
   (0x36a20, 0x36a38); (0x36a60, 0x36a74); (0x36aa0, 0x36aae); (0x36ac0, 0x36ad4); (0x36b00, 0x36b08); (0x36b60, 0x36b73); (0x36c00, 0x36c13); (0x36c40, 0x36c50);
   (0x36c60, 0x36c7f); (0x36ca0, 0x36cc3); (0x36d00, 0x36d15); (0x36d40, 0x36d51); (0x36d80, 0x36d93); (0x36dc0, 0x36dce); (0x370e0, 0x370f5); (0x37120, 0x3712f);
   (0x37140, 0x37155); (0x37180, 0x37190); (0x371a0, 0x371ad); (0x371c0, 0x371d1); (0x37200, 0x37212); (0x37240, 0x3724a); (0x37260, 0x3726d); (0x37280, 0x37285);
   (0x372a0, 0x372bb); (0x372e0, 0x372f9); (0x37320, 0x37339); (0x37360, 0x3737c); (0x373a0, 0x373b9); (0x373e0, 0x373f4); (0x37420, 0x37432); (0x37460, 0x37473);
   (0x374a0, 0x374c1); (0x37500, 0x37516); (0x37540, 0x3756b); (0x375a0, 0x375dc); (0x37600, 0x37630); (0x37660, 0x3768e); (0x37780, 0x37792); (0x377c0, 0x377d2);
   (0x37800, 0x37819); (0x37840, 0x37850); (0x37860, 0x37877); (0x378a0, 0x378b2); (0x378e0, 0x378f2); (0x37920, 0x37943); (0x37980, 0x3798f); (0x379e0, 0x379f2);
   (0x37a20, 0x37a34); (0x37a60, 0x37a74); (0x37aa0, 0x37ab0); (0x37ac0, 0x37ad0); (0x37ae0, 0x37aed); (0x37b00, 0x37b14); (0x37b40, 0x37b51); (0x37b80, 0x37b8e);
   (0x37ba0, 0x37bb2); (0x37be0, 0x37bf0); (0x37c00, 0x37c34); (0x37c60, 0x37c97); (0x37cc0, 0x37cf7); (0x37d20, 0x37d33); (0x37d60, 0x37d73); (0x37da0, 0x37db1);
   (0x37de0, 0x37df4); (0x37e20, 0x37e32); (0x37e60, 0x37e72); (0x37ea0, 0x37eb3); (0x37ee0, 0x37ef3); (0x37f20, 0x37f32); (0x37f60, 0x37f73); (0x37fa0, 0x37fb0);
   (0x37fc0, 0x37fd1); (0x38000, 0x3803f); (0x38060, 0x38077); (0x380a0, 0x380b2); (0x380e0, 0x380f1); (0x38120, 0x3812f); (0x38140, 0x38152); (0x38180, 0x381b1);
   (0x381e0, 0x38205); (0x38240, 0x38250); (0x38260, 0x38273); (0x382a0, 0x382b2); (0x382e0, 0x382f5); (0x38320, 0x38332); (0x38360, 0x38372); (0x383a0, 0x383b4);
   (0x383e0, 0x383f2); (0x38420, 0x38439); (0x38460, 0x3848b); (0x384c0, 0x384d4); (0x38500, 0x38515); (0x38540, 0x38552); (0x38580, 0x3858f); (0x385a0, 0x385ae);
   (0x385c0, 0x385d0); (0x385e0, 0x385ea); (0x38600, 0x38632); (0x38660, 0x3866c); (0x38680, 0x38696); (0x386c0, 0x386db); (0x38700, 0x38717); (0x38740, 0x3874b);
   (0x38760, 0x38788); (0x387c0, 0x387d8); (0x38800, 0x3880b); (0x38820, 0x38855); (0x38880, 0x38893); (0x388c0, 0x388c6); (0x388e0, 0x388e5); (0x38900, 0x38902);
   (0x38920, 0x38934); (0x38960, 0x38976); (0x389a0, 0x389b0); (0x389c0, 0x389ce); (0x38aa0, 0x38ab9); (0x38ae0, 0x38b0f); (0x38b40, 0x38b4e); (0x38b60, 0x38b94);
   (0x38bc0, 0x38bce); (0x38be0, 0x38bf7); (0x38c20, 0x38c48); (0x38c80, 0x38c98); (0x38cc0, 0x38ce6); (0x38d20, 0x38d25); (0x38d40, 0x38d46); (0x38d60, 0x38daa);
   (0x38de0, 0x38df7); (0x38e20, 0x38e38); (0x38e60, 0x38e88); (0x38ec0, 0x38ed4); (0x38f00, 0x38f13); (0x38f40, 0x38f6c); (0x38fa0, 0x38fb3); (0x38fe0, 0x38ff3);
   (0x39020, 0x39046); (0x39080, 0x390ab); (0x390e0, 0x390f5); (0x39120, 0x39135); (0x39160, 0x391b6); (0x391e0, 0x391e1); (0x39200, 0x39253); (0x39280, 0x3928e);
   (0x392a0, 0x392b4); (0x392e0, 0x392fb); (0x39320, 0x3934f); (0x39380, 0x39396); (0x393c0, 0x393d5); (0x39400, 0x39412); (0x39440, 0x39455); (0x39480, 0x3949f);
   (0x394c0, 0x394d0); (0x394e0, 0x39525); (0x395a0, 0x395b2); (0x395e0, 0x395ee); (0x39600, 0x39625); (0x39660, 0x3966f); (0x39680, 0x3968f); (0x396a0, 0x396b2);
   (0x396e0, 0x396f0); (0x39700, 0x39711); (0x39740, 0x39754); (0x39780, 0x39790); (0x397a0, 0x397b9); (0x397e0, 0x397f5); (0x39820, 0x39837); (0x39860, 0x3988a);
   (0x398c0, 0x398d7); (0x39940, 0x39950); (0x39960, 0x3996f); (0x39980, 0x39990); (0x399a0, 0x399b4); (0x399e0, 0x399ef); (0x39a00, 0x39a11); (0x39a40, 0x39a54);
   (0x39a80, 0x39a96); (0x39ac0, 0x39ace); (0x39b20, 0x39b64); (0x39ba0, 0x39bad); (0x39bc0, 0x39bf2); (0x39c20, 0x39c31); (0x39c60, 0x39c85); (0x39cc0, 0x39cce);
   (0x39ce0, 0x39cf1); (0x39d20, 0x39d2d); (0x39d40, 0x39d4b); (0x39d60, 0x39d6d); (0x39d80, 0x39d9b); (0x39e00, 0x39e11); (0x39e40, 0x39e55); (0x39e80, 0x39e8d);
   (0x39ea0, 0x39eb7); (0x39ee0, 0x39f1c); (0x39f80, 0x39f94); (0x39fc0, 0x39fd9); (0x3a000, 0x3a01e); (0x3a040, 0x3a04d); (0x3a060, 0x3a07e); (0x3a0a0, 0x3a0c2);
   (0x3a100, 0x3a116); (0x3a140, 0x3a15c); (0x3a180, 0x3a192); (0x3a1c0, 0x3a1d1); (0x3a200, 0x3a218); (0x3a240, 0x3a257); (0x3a2c0, 0x3a2d0); (0x3a2e0, 0x3a2f1);
   (0x3a320, 0x3a330); (0x3a340, 0x3a34e); (0x3a360, 0x3a370); (0x3a380, 0x3a391); (0x3a3c0, 0x3a3d1); (0x3a400, 0x3a40d); (0x3a420, 0x3a431); (0x3a460, 0x3a474);
   (0x3a4a0, 0x3a4b7); (0x3a4e0, 0x3a4eb); (0x3a500, 0x3a529); (0x3a560, 0x3a566); (0x3a580, 0x3a5ab); (0x3a5e0, 0x3a60d); (0x3a640, 0x3a678); (0x3a6a0, 0x3a6d6);
   (0x3a700, 0x3a736); (0x3a760, 0x3a799); (0x3a7c0, 0x3a7ea); (0x3a820, 0x3a857); (0x3a880, 0x3a8af); (0x3a8e0, 0x3a91c); (0x3a940, 0x3a94a); (0x3a960, 0x3a96a);
   (0x3a980, 0x3a99e); (0x3a9c0, 0x3aa04); (0x3aa40, 0x3aa56); (0x3aa80, 0x3aaa5); (0x3aae0, 0x3ab06); (0x3ab40, 0x3ab67); (0x3aba0, 0x3abc5); (0x33d00, 0x33d84);
   (0x33dc0, 0x33e44); (0x34360, 0x34374); (0x34720, 0x34724); (0x34740, 0x3474c); (0x347a0, 0x347d8); (0x35740, 0x35778); (0x389e0, 0x38a80)].
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
  { unfold asegs, AsanUbsan.M.loaded_segments, AsanUbsan.AsanUbsan_loaded_segments.
    cbn [find_segment].
    unfold AsanUbsan.AsanUbsan_segment_000, AsanUbsan.AsanUbsan_segment_001,
      AsanUbsan.AsanUbsan_segment_002, AsanUbsan.AsanUbsan_segment_003.
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
