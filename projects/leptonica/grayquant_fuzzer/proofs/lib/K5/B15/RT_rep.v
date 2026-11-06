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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require BackingAlgebra.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Mem Frame Cells Step Arr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require NodesA_madv.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import R_sizeclass.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import R_cache_defs R_prim_defs R_thread R_m2s R_poison R_leaves R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state TopA_iodefs.
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
  /\ ro_cells asegs m 0x18925d [C1 (Z_to_bv 8 0)] /\ ro_cells asegs m 0x189264 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0xeb9d8 [C8 (Z_to_bv 64 0xf4e38)] /\ ro_cells asegs m 0xeba08 [C8 (Z_to_bv 64 0xed8b8)]
  /\ ro_cells asegs m 0xed8b8 [C8 (Z_to_bv 64 0xe1d18)] /\ ro_cells asegs m 0xf4e55 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0xf833c [C4 (Z_to_bv 64 30)] /\ ro_cells asegs m 0x18918a [C1 (Z_to_bv 8 1)]
  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xec658 [C8 (Z_to_bv 64 0xf0000)] /\ ro_cells asegs m 0xec6b8 [C8 (Z_to_bv 64 0x64a848)]
  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xec548 [C8 (Z_to_bv 64 0xf8319)] /\ ro_cells asegs m 0xf8319 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0xed8c0 [C8 (Z_to_bv 64 0xe211c)] /\ ro_cells asegs m 0xed770 [C8 (Z_to_bv 64 0xe1c1c)]
  /\ ro_cells asegs m 0xed868 [C8 (Z_to_bv 64 0xe25a4)] /\ ro_cells asegs m 0xed748 [C8 (Z_to_bv 64 0xe2368)]
  /\ ro_cells asegs m 0x189263 [C1 (Z_to_bv 8 1)]    (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xf4df8 [C8 (Z_to_bv 64 (2 ^ 40))] /\ rw_cells asegs m 0xf4e00 [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)]
  /\ rw_cells asegs m 0x1798a2 [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m 0x18918a [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0xeb9d8 [C8 (Z_to_bv 64 0xf4e38)] /\ rw_cells asegs m (0xf4e38 + 44) [C4 (Z_to_bv 64 4096)]
  /\ rw_cells asegs m (0xf4e38 + 52) [C4 (Z_to_bv 64 190)] /\ rw_cells asegs m (0xf4e38 + 85) [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m (0x62a808 + 16) [C4 (Z_to_bv 64 0)] /\ rw_cells asegs m 0xec638 [C8 (Z_to_bv 64 16)]
  /\ rw_cells asegs m 0x189100 [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m 0xf6e9c [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m (l_TCX L + 8) [C4 (Z_to_bv 64 0)]
  /\ stk asegs m (l_T L + 2768) (l_T L + 3168)
  (* [comment removed for export] *)
  /\ rw_cells asegs m (l_T L) [C8 (Z_to_bv 64 (l_TCX L))]
  (* [comment removed for export] *)
  /\ rw_cells asegs m (g_MFHooks + 8) [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m i_q_max [C8 (Z_to_bv 64 0x10000000); C8 (Z_to_bv 64 0xE666661); C8 (Z_to_bv 64 0x100000)]
  /\ rw_cells asegs m (g_asan_flags + 48) [C4 (Z_to_bv 64 0)]
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xeba20 [C8 (Z_to_bv 64 1)] /\ rw_cells asegs m 0x189243 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x18925c [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m 0xec6b8 [C8 (Z_to_bv 64 0x64a848)]
  /\ rw_cells asegs m 0x64aac8 [C8 (Z_to_bv 64 4096)]
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
  [(0xefdd0, 0xf0004); (0xf0020, 0xf0028); (0xf0040, 0xf0048); (0xf0060, 0xf0068); (0xf0080, 0xf3fd8);
   (0x619c90, 0x629c90);
   (0x629c90, 0x62a7b0); (0x62a7b8, 0x62a800);
   (0x62a820, 0x62a828); (0x62a838, 0x64aac8); (0x64aad0, 0x64bbb0); (0x64bbb8, 0x64c0e8)].
(* [comment removed for export] *)
Definition CS_ACC : list (Z * Z) :=
  [(0xefdd0, 0xf0004); (0xf0020, 0xf0028); (0xf0040, 0xf0048); (0xf0060, 0xf0068); (0xf0080, 0xf03c0); (0xf3f80, 0xf3ff8);
   (0x619c90, 0x629c90);
   (0x629c90, 0x62a7b0); (0x62a7b8, 0x62a800);
   (0x62a820, 0x62a828); (0x62a838, 0x64bbb0); (0x64bbb8, 0x64c0e8);
   (* [comment removed for export] *)
   (0x24040, 0x2404e); (0x24060, 0x2406a); (0x24080, 0x24090); (0x240a0, 0x240bd); (0x241a0, 0x241c7); (0x24200, 0x24210); (0x24220, 0x24232); (0x24260, 0x24273); (0x24300, 0x2430c); (0x24320, 0x24338); (0x24500, 0x2450b); (0x246a0, 0x246b0); (0x246c0, 0x246cc); (0x24740, 0x2474d); (0x247a0, 0x247ac); (0x24800, 0x24811); (0x248a0, 0x248aa); (0x24960, 0x2496f); (0x24980, 0x24996); (0x24a00, 0x24a0b); (0x24a60, 0x24a70); (0x24a80, 0x24a8e); (0x24e60, 0x24e6f); (0x24e80, 0x24e93); (0x24ec0, 0x24ecf); (0x24ee0, 0x24ef1); (0x24f20, 0x24f37); (0x25280, 0x25296); (0x252c0, 0x252cf); (0x25680, 0x25691); (0x25740, 0x2574f); (0x25760, 0x2577d); (0x257a0, 0x257ab); (0x257c0, 0x257ce); (0x25820, 0x25831); (0x25860, 0x25876); (0x258a0, 0x258b4); (0x258e0, 0x25905); (0x266a0, 0x266b3); (0x266e0, 0x266e8); (0x26700, 0x26710); (0x26bc0, 0x26bcd); (0x26be0, 0x26bf1); (0x26c20, 0x26c39); (0x26cc0, 0x26cd2); (0x26d00, 0x26d0e); (0x26d20, 0x26d2f); (0x26d40, 0x26d4f); (0x26d60, 0x26d70); (0x26d80, 0x26d96); (0x26e40, 0x26e4e); (0x26e60, 0x26e72); (0x26ea0, 0x26eb9); (0x236a0, 0x236b1); (0x242a0, 0x242cf); (0x24360, 0x24390); (0x243c0, 0x243f4); (0x24420, 0x24455); (0x244a0, 0x244c5); (0x24e00, 0x24e25); (0x24aa0, 0x24abb); (0x24f60, 0x24f85); (0x24fc0, 0x24fef); (0x25020, 0x2504e); (0x25080, 0x2509f); (0x250c0, 0x250f3); (0x25120, 0x25158); (0x25180, 0x251ba); (0x251e0, 0x2522d); (0x26c60, 0x26c83); (0x26dc0, 0x26e14); (0x24ae0, 0x24b64);
   (* [comment removed for export] *)
   (0x10d84, 0x10d8e); (0x14f49, 0x14f4d); (0x16340, 0x163c0); (0x1acb5, 0x1acd6); (0x1f64f, 0x1f664); (0x1f664, 0x1f67b);
   (0x21e00, 0x21e80); (0x22e5e, 0x22e65); (0x239d8, 0x239e8); (0x619c80, 0x619c90);
   (* [comment removed for export] *)
   (0x23620, 0x2362e); (0x23720, 0x23740); (0x23760, 0x2376a); (0x23780, 0x2378e); (0x237a0, 0x237b1); (0x237e0, 0x237eb); (0x23800, 0x23812); (0x23840, 0x2384e);
   (0x23860, 0x23871); (0x238a0, 0x238ab); (0x238c0, 0x238d5); (0x23900, 0x23917); (0x23940, 0x2394b); (0x23960, 0x23971); (0x23a00, 0x23a16); (0x23a40, 0x23a4b);
   (0x23a60, 0x23a84); (0x23ac0, 0x23acc); (0x23ae0, 0x23aef); (0x23b00, 0x23b09); (0x23b20, 0x23b2d); (0x23b40, 0x23b4e); (0x23b60, 0x23b71); (0x23ba0, 0x23bad);
   (0x23bc0, 0x23bdb); (0x23c00, 0x23c10); (0x23c20, 0x23c32); (0x23c60, 0x23c6e); (0x23c80, 0x23c8c); (0x23ca0, 0x23caf); (0x23cc0, 0x23cce); (0x23ce0, 0x23cf0);
   (0x23d00, 0x23d15); (0x23d40, 0x23d5c); (0x23dc0, 0x23dcf); (0x23de0, 0x23dfc); (0x23e20, 0x23e33); (0x23e60, 0x23e71); (0x23ea0, 0x23ea9); (0x23ec0, 0x23ed6);
   (0x23f00, 0x23f1f); (0x23f40, 0x23f51); (0x23f80, 0x23f92); (0x23fc0, 0x23fcf); (0x23fe0, 0x23ff0); (0x240e0, 0x240f1); (0x24120, 0x24132); (0x24160, 0x24178);
   (0x24480, 0x24489); (0x24520, 0x24528); (0x24540, 0x2455c); (0x24580, 0x24593); (0x245c0, 0x245d1); (0x24600, 0x24610); (0x24620, 0x2463f); (0x24660, 0x2466f);
   (0x24680, 0x2468f); (0x246e0, 0x246ec); (0x24700, 0x24713); (0x24760, 0x2476d); (0x24780, 0x2478f); (0x247c0, 0x247cc); (0x247e0, 0x247ef); (0x24840, 0x2484a);
   (0x24860, 0x24871); (0x248c0, 0x248d2); (0x24900, 0x24913); (0x24940, 0x2494f); (0x249c0, 0x249d3); (0x24ba0, 0x24bb3); (0x24be0, 0x24bf0); (0x24c00, 0x24c11);
   (0x24c80, 0x24c97); (0x24cc0, 0x24cce); (0x24ce0, 0x24cf6); (0x24d20, 0x24d34); (0x24d60, 0x24d70); (0x24d80, 0x24d92); (0x24dc0, 0x24dcc); (0x24de0, 0x24ded);
   (0x25260, 0x25270); (0x252e0, 0x252f3); (0x25320, 0x25338); (0x25360, 0x25370); (0x25380, 0x253a4); (0x253e0, 0x253f0); (0x25400, 0x25414); (0x25440, 0x25452);
   (0x25480, 0x25493); (0x254c0, 0x254d0); (0x254e0, 0x254f9); (0x25520, 0x25534); (0x25560, 0x25570); (0x25580, 0x25598); (0x255c0, 0x255d7); (0x25600, 0x25618);
   (0x25640, 0x2565d); (0x256c0, 0x256e4); (0x25720, 0x25730); (0x25980, 0x25991); (0x259c0, 0x259d2); (0x25a00, 0x25a36); (0x25a60, 0x25a7b); (0x25aa0, 0x25ac0);
   (0x25ae0, 0x25af9); (0x25b20, 0x25b57); (0x25b80, 0x25b9c); (0x25bc0, 0x25bea); (0x25c60, 0x25c71); (0x25ca0, 0x25cb2); (0x25ce0, 0x25cfc); (0x25d20, 0x25d36);
   (0x25d60, 0x25d7c); (0x25da0, 0x25dbc); (0x25de0, 0x25dee); (0x25e00, 0x25e0e); (0x25e20, 0x25e3b); (0x25e60, 0x25e72); (0x25ea0, 0x25eb6); (0x25ee0, 0x25efc);
   (0x25f20, 0x25f37); (0x25f60, 0x25f76); (0x25fa0, 0x25fb5); (0x25fe0, 0x25ff0); (0x26000, 0x26014); (0x26040, 0x2604f); (0x26060, 0x26074); (0x260a0, 0x260b5);
   (0x260e0, 0x260f1); (0x26120, 0x26125); (0x26140, 0x26155); (0x26180, 0x261b5); (0x261e0, 0x261f1); (0x26220, 0x26236); (0x26260, 0x26272); (0x262a0, 0x262af);
   (0x262c0, 0x262db); (0x26300, 0x2630e); (0x26320, 0x26338); (0x26360, 0x2636b); (0x26380, 0x2639b); (0x263c0, 0x263dd); (0x26400, 0x2644b); (0x26480, 0x26499);
   (0x264c0, 0x264d1); (0x26500, 0x26519); (0x26540, 0x26550); (0x26560, 0x26579); (0x265a0, 0x265b7); (0x26620, 0x26631); (0x26660, 0x2666a); (0x26680, 0x2668e);
   (0x26760, 0x26771); (0x267a0, 0x267ac); (0x267c0, 0x267d1); (0x26800, 0x2681f); (0x26aa0, 0x26ac2); (0x26b00, 0x26b16); (0x26b40, 0x26b56); (0x26f20, 0x26f30);
   (0x26f40, 0x26f56); (0x26920, 0x269a4); (0x269e0, 0x26a64)].
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
