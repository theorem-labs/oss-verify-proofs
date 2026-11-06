(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Permutation.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require BackingAlgebra.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Mem Frame Cells Step Arr.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require NodesA_madv.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import RT_iface.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import R_sizeclass.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import R_cache_defs R_prim_defs R_thread R_m2s R_poison R_leaves R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state TopA_iodefs.
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
  /\ ro_cells asegs m 0x18aadd [C1 (Z_to_bv 8 0)] /\ ro_cells asegs m 0x18aae4 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0xec8a0 [C8 (Z_to_bv 64 0xf66b8)] /\ ro_cells asegs m 0xec8d0 [C8 (Z_to_bv 64 0xee778)]
  /\ ro_cells asegs m 0xee778 [C8 (Z_to_bv 64 0xe2be4)] /\ ro_cells asegs m 0xf66d5 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0xf9bbc [C4 (Z_to_bv 64 30)] /\ ro_cells asegs m 0x18aa0a [C1 (Z_to_bv 8 1)]
  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xed520 [C8 (Z_to_bv 64 0xf0ec0)] /\ ro_cells asegs m 0xed580 [C8 (Z_to_bv 64 0x64c0c8)]
  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xed410 [C8 (Z_to_bv 64 0xf9b99)] /\ ro_cells asegs m 0xf9b99 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0xee780 [C8 (Z_to_bv 64 0xe2fe8)] /\ ro_cells asegs m 0xee630 [C8 (Z_to_bv 64 0xe2ae8)]
  /\ ro_cells asegs m 0xee728 [C8 (Z_to_bv 64 0xe3470)] /\ ro_cells asegs m 0xee608 [C8 (Z_to_bv 64 0xe3234)]
  /\ ro_cells asegs m 0x18aae3 [C1 (Z_to_bv 8 1)]    (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xf6678 [C8 (Z_to_bv 64 (2 ^ 40))] /\ rw_cells asegs m 0xf6680 [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)]
  /\ rw_cells asegs m 0x17b122 [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m 0x18aa0a [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0xec8a0 [C8 (Z_to_bv 64 0xf66b8)] /\ rw_cells asegs m (0xf66b8 + 44) [C4 (Z_to_bv 64 4096)]
  /\ rw_cells asegs m (0xf66b8 + 52) [C4 (Z_to_bv 64 190)] /\ rw_cells asegs m (0xf66b8 + 85) [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m (0x62c088 + 16) [C4 (Z_to_bv 64 0)] /\ rw_cells asegs m 0xed500 [C8 (Z_to_bv 64 16)]
  /\ rw_cells asegs m 0x18a980 [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m 0xf871c [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m (l_TCX L + 8) [C4 (Z_to_bv 64 0)]
  /\ stk asegs m (l_T L + 2768) (l_T L + 3168)
  (* [comment removed for export] *)
  /\ rw_cells asegs m (l_T L) [C8 (Z_to_bv 64 (l_TCX L))]
  (* [comment removed for export] *)
  /\ rw_cells asegs m (g_MFHooks + 8) [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m i_q_max [C8 (Z_to_bv 64 0x10000000); C8 (Z_to_bv 64 0xE666661); C8 (Z_to_bv 64 0x100000)]
  /\ rw_cells asegs m (g_asan_flags + 48) [C4 (Z_to_bv 64 0)]
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xec8e8 [C8 (Z_to_bv 64 1)] /\ rw_cells asegs m 0x18aac3 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x18aadc [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m 0xed580 [C8 (Z_to_bv 64 0x64c0c8)]
  /\ rw_cells asegs m 0x64c348 [C8 (Z_to_bv 64 4096)]
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
  [(0xf0c90, 0xf0ec4); (0xf0ee0, 0xf0ee8); (0xf0f00, 0xf0f08); (0xf0f20, 0xf0f28); (0xf0f40, 0xf1260); (0xf1320, 0xf5858);
   (0x61b510, 0x62b510);
   (0x62b510, 0x62c030); (0x62c038, 0x62c080);
   (0x62c0a0, 0x62c0a8); (0x62c0b8, 0x64c348); (0x64c350, 0x64d430); (0x64d438, 0x64d968)].
(* [comment removed for export] *)
Definition CS_ACC : list (Z * Z) :=
  [(0xf0c90, 0xf0ec4); (0xf0ee0, 0xf0ee8); (0xf0f00, 0xf0f08); (0xf0f20, 0xf0f28); (0xf0f40, 0xf1260); (0xf1320, 0xf1660); (0xf57e0, 0xf5878);
   (0x61b510, 0x62b510);
   (0x62b510, 0x62c030); (0x62c038, 0x62c080);
   (0x62c0a0, 0x62c0a8); (0x62c0b8, 0x64d430); (0x64d438, 0x64d968);
   (* [comment removed for export] *)
   (0x23900, 0x2390e); (0x23920, 0x2392a); (0x23940, 0x23950); (0x23960, 0x2397d); (0x23a60, 0x23a87); (0x23ac0, 0x23ad0); (0x23ae0, 0x23af2); (0x23b20, 0x23b33); (0x23bc0, 0x23bcc); (0x23be0, 0x23bf8); (0x23dc0, 0x23dcb); (0x23f60, 0x23f70); (0x23f80, 0x23f8c); (0x24000, 0x2400d); (0x24060, 0x2406c); (0x240c0, 0x240d1); (0x241a0, 0x241aa); (0x24260, 0x2426f); (0x24280, 0x24296); (0x24300, 0x2430b); (0x24360, 0x24370); (0x24540, 0x2454e); (0x24ee0, 0x24eef); (0x24f00, 0x24f13); (0x24f40, 0x24f4f); (0x24f60, 0x24f71); (0x24fa0, 0x24fb7); (0x25300, 0x25316); (0x25340, 0x2534f); (0x25640, 0x25651); (0x25700, 0x2570f); (0x25720, 0x2573d); (0x25760, 0x2576b); (0x25780, 0x2578e); (0x257e0, 0x257f1); (0x25820, 0x25836); (0x25860, 0x25874); (0x258a0, 0x258c5); (0x26140, 0x26153); (0x26180, 0x26188); (0x261a0, 0x261b0); (0x26660, 0x2666d); (0x26680, 0x26691); (0x266c0, 0x266d9); (0x26760, 0x26772); (0x267a0, 0x267ae); (0x267c0, 0x267cf); (0x267e0, 0x267ef); (0x26800, 0x26810); (0x26820, 0x26836); (0x268e0, 0x268ee); (0x26900, 0x26912); (0x26940, 0x26959); (0x236c0, 0x236d1); (0x23b60, 0x23b8f); (0x23c20, 0x23c50); (0x23c80, 0x23cb4); (0x23ce0, 0x23d15); (0x23d60, 0x23d85); (0x24e80, 0x24ea5); (0x24560, 0x2457b); (0x24fe0, 0x25005); (0x25040, 0x2506f); (0x250a0, 0x250ce); (0x25100, 0x2511f); (0x25140, 0x25173); (0x251a0, 0x251d8); (0x25200, 0x2523a); (0x25260, 0x252ad); (0x26700, 0x26723); (0x26860, 0x268b4); (0x245a0, 0x24624);
   (* [comment removed for export] *)
   (0x10d4d, 0x10d57); (0x14f26, 0x14f2a); (0x162c0, 0x16340); (0x1accd, 0x1acee); (0x1f5be, 0x1f5d3); (0x1f5d3, 0x1f5ea);
   (0x21e40, 0x21ec0); (0x22efb, 0x22f02); (0x2a2c0, 0x2a2d0); (0x61b500, 0x61b510);
   (* [comment removed for export] *)
   (0x23740, 0x23760); (0x23780, 0x2378a); (0x237a0, 0x237ae); (0x237c0, 0x237d2); (0x23800, 0x2380e); (0x23820, 0x23837); (0x23860, 0x2386b); (0x23880, 0x23891);
   (0x239a0, 0x239b1); (0x239e0, 0x239f2); (0x23a20, 0x23a38); (0x23d40, 0x23d49); (0x23de0, 0x23de8); (0x23e00, 0x23e1c); (0x23e40, 0x23e53); (0x23e80, 0x23e91);
   (0x23ec0, 0x23ed0); (0x23ee0, 0x23eff); (0x23f20, 0x23f2f); (0x23f40, 0x23f4f); (0x23fa0, 0x23fac); (0x23fc0, 0x23fd3); (0x24020, 0x2402d); (0x24040, 0x2404f);
   (0x24080, 0x2408c); (0x240a0, 0x240af); (0x24100, 0x2410a); (0x24120, 0x2412a); (0x24140, 0x24151); (0x24180, 0x2418b); (0x241c0, 0x241d2); (0x24200, 0x24213);
   (0x24240, 0x2424f); (0x242c0, 0x242d3); (0x24380, 0x24391); (0x243c0, 0x243d3); (0x24400, 0x24438); (0x24460, 0x244a0); (0x244c0, 0x244d2); (0x24500, 0x2451f);
   (0x24660, 0x2466e); (0x24680, 0x2468d); (0x246a0, 0x246b4); (0x246e0, 0x246f7); (0x24720, 0x24730); (0x24740, 0x24757); (0x24780, 0x24799); (0x247c0, 0x247d2);
   (0x24800, 0x24813); (0x24840, 0x2485f); (0x24880, 0x24899); (0x248c0, 0x248da); (0x24900, 0x24910); (0x24920, 0x24933); (0x24960, 0x24970); (0x24980, 0x2498d);
   (0x249a0, 0x249b1); (0x249e0, 0x249f3); (0x24a20, 0x24a2f); (0x24a40, 0x24a67); (0x24aa0, 0x24ab7); (0x24ae0, 0x24af1); (0x24b20, 0x24b3d); (0x24b60, 0x24b71);
   (0x24ba0, 0x24bbf); (0x24be0, 0x24bf4); (0x24c20, 0x24c33); (0x24c60, 0x24c70); (0x24c80, 0x24c91); (0x24d00, 0x24d17); (0x24d40, 0x24d4e); (0x24d60, 0x24d76);
   (0x24da0, 0x24db4); (0x24de0, 0x24df0); (0x24e00, 0x24e12); (0x24e40, 0x24e4c); (0x24e60, 0x24e6d); (0x252e0, 0x252f0); (0x25360, 0x25370); (0x25380, 0x253a4);
   (0x253e0, 0x253f0); (0x25400, 0x25414); (0x25440, 0x25453); (0x25480, 0x25490); (0x254a0, 0x254b9); (0x254e0, 0x254f4); (0x25520, 0x25530); (0x25540, 0x25558);
   (0x25580, 0x25597); (0x255c0, 0x255d2); (0x25600, 0x25615); (0x25680, 0x256a4); (0x256e0, 0x256f0); (0x259c0, 0x259d1); (0x25a00, 0x25a0e); (0x25a20, 0x25a32);
   (0x25a60, 0x25a96); (0x25ac0, 0x25adb); (0x25b00, 0x25b20); (0x25b40, 0x25b59); (0x25b80, 0x25bb7); (0x25be0, 0x25bfc); (0x25c20, 0x25c4a); (0x25c80, 0x25c9e);
   (0x25cc0, 0x25cd4); (0x25d00, 0x25d0d); (0x25d20, 0x25d37); (0x25d60, 0x25d74); (0x25da0, 0x25db0); (0x25dc0, 0x25dfb); (0x25e20, 0x25e30); (0x25e40, 0x25e50);
   (0x25e60, 0x25e6f); (0x25e80, 0x25e92); (0x25ec0, 0x25ed3); (0x25f00, 0x25f0f); (0x25f20, 0x25f2f); (0x25f40, 0x25f4f); (0x25f60, 0x25f6f); (0x25f80, 0x25f8f);
   (0x25fa0, 0x25faf); (0x25fc0, 0x25fdd); (0x26000, 0x2600e); (0x26020, 0x26031); (0x26060, 0x26070); (0x260c0, 0x260d1); (0x26100, 0x2610a); (0x26120, 0x2612e);
   (0x26200, 0x26211); (0x26240, 0x2624c); (0x26260, 0x26271); (0x262a0, 0x262bf); (0x26540, 0x26562); (0x265a0, 0x265b6); (0x265e0, 0x265f6); (0x269c0, 0x269d3);
   (0x26a00, 0x26a0a); (0x26a20, 0x26a45); (0x26a80, 0x26a8b); (0x26aa0, 0x26ab0); (0x26ac0, 0x26ac8); (0x26ae0, 0x26af2); (0x26b20, 0x26b39); (0x26b60, 0x26b6f);
   (0x26b80, 0x26b99); (0x26bc0, 0x26bcd); (0x26be0, 0x26bf1); (0x26c20, 0x26c31); (0x26c60, 0x26c71); (0x26ca0, 0x26cb1); (0x26ce0, 0x26ceb); (0x26d00, 0x26d19);
   (0x26d40, 0x26d51); (0x26d80, 0x26d8e); (0x26da0, 0x26db1); (0x26de0, 0x26ded); (0x26e00, 0x26e0b); (0x26e20, 0x26e2e); (0x26e40, 0x26e4b); (0x26e60, 0x26e76);
   (0x26ea0, 0x26eb6); (0x26ee0, 0x26eee); (0x26f00, 0x26f10); (0x26f20, 0x26f3b); (0x26fa0, 0x26fae); (0x26fc0, 0x26fcf); (0x26fe0, 0x26fe8); (0x27000, 0x27008);
   (0x27020, 0x27028); (0x27040, 0x27048); (0x27060, 0x27068); (0x27080, 0x27088); (0x270a0, 0x270a8); (0x270c0, 0x270c8); (0x270e0, 0x270e8); (0x27100, 0x27108);
   (0x27160, 0x27171); (0x271a0, 0x271ac); (0x271c0, 0x271d3); (0x27200, 0x2720d); (0x27220, 0x27234); (0x27260, 0x2726e); (0x27280, 0x2728e); (0x263c0, 0x26444);
   (0x26480, 0x26504)].
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
