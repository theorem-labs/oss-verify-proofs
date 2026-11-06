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
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require NodesA_madv.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import RT_iface.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import R_sizeclass.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import R_cache_defs R_prim_defs R_thread R_m2s R_poison R_leaves R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state TopA_iodefs.
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
  /\ ro_cells asegs m 0x1821dd [C1 (Z_to_bv 8 0)] /\ ro_cells asegs m 0x1821e4 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0xe4000 [C8 (Z_to_bv 64 0xeddb8)] /\ ro_cells asegs m 0xe4030 [C8 (Z_to_bv 64 0xe5ed8)]
  /\ ro_cells asegs m 0xe5ed8 [C8 (Z_to_bv 64 0xda340)] /\ ro_cells asegs m 0xeddd5 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0xf12bc [C4 (Z_to_bv 64 30)] /\ ro_cells asegs m 0x18210a [C1 (Z_to_bv 8 1)]
  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xe4c80 [C8 (Z_to_bv 64 0xe8620)] /\ ro_cells asegs m 0xe4ce0 [C8 (Z_to_bv 64 0x6437c8)]
  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xe4b70 [C8 (Z_to_bv 64 0xf1299)] /\ ro_cells asegs m 0xf1299 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0xe5ee0 [C8 (Z_to_bv 64 0xda744)] /\ ro_cells asegs m 0xe5d90 [C8 (Z_to_bv 64 0xda244)]
  /\ ro_cells asegs m 0xe5e88 [C8 (Z_to_bv 64 0xdabcc)] /\ ro_cells asegs m 0xe5d68 [C8 (Z_to_bv 64 0xda990)]
  /\ ro_cells asegs m 0x1821e3 [C1 (Z_to_bv 8 1)]    (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xedd78 [C8 (Z_to_bv 64 (2 ^ 40))] /\ rw_cells asegs m 0xedd80 [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)]
  /\ rw_cells asegs m 0x172822 [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m 0x18210a [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0xe4000 [C8 (Z_to_bv 64 0xeddb8)] /\ rw_cells asegs m (0xeddb8 + 44) [C4 (Z_to_bv 64 4096)]
  /\ rw_cells asegs m (0xeddb8 + 52) [C4 (Z_to_bv 64 190)] /\ rw_cells asegs m (0xeddb8 + 85) [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m (0x623788 + 16) [C4 (Z_to_bv 64 0)] /\ rw_cells asegs m 0xe4c60 [C8 (Z_to_bv 64 16)]
  /\ rw_cells asegs m 0x182080 [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m 0xefe1c [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m (l_TCX L + 8) [C4 (Z_to_bv 64 0)]
  /\ stk asegs m (l_T L + 2768) (l_T L + 3168)
  (* [comment removed for export] *)
  /\ rw_cells asegs m (l_T L) [C8 (Z_to_bv 64 (l_TCX L))]
  (* [comment removed for export] *)
  /\ rw_cells asegs m (g_MFHooks + 8) [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m i_q_max [C8 (Z_to_bv 64 0x10000000); C8 (Z_to_bv 64 0xE666661); C8 (Z_to_bv 64 0x100000)]
  /\ rw_cells asegs m (g_asan_flags + 48) [C4 (Z_to_bv 64 0)]
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xe4048 [C8 (Z_to_bv 64 1)] /\ rw_cells asegs m 0x1821c3 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x1821dc [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m 0xe4ce0 [C8 (Z_to_bv 64 0x6437c8)]
  /\ rw_cells asegs m 0x643a48 [C8 (Z_to_bv 64 4096)]
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
  [(0xe83f0, 0xe8624); (0xe8640, 0xe8648); (0xe8660, 0xe8668); (0xe8680, 0xe8688); (0xe86a0, 0xe89c0); (0xe8a80, 0xecf58);
   (0x612c10, 0x622c10);
   (0x622c10, 0x623730); (0x623738, 0x623780);
   (0x6237a0, 0x6237a8); (0x6237b8, 0x643a48); (0x643a50, 0x644b30); (0x644b38, 0x645068)].
(* [comment removed for export] *)
Definition CS_ACC : list (Z * Z) :=
  [(0xe83f0, 0xe8624); (0xe8640, 0xe8648); (0xe8660, 0xe8668); (0xe8680, 0xe8688); (0xe86a0, 0xe89c0); (0xe8a80, 0xe8dc0); (0xecf00, 0xecf58);
   (0x612c10, 0x622c10);
   (0x622c10, 0x623730); (0x623738, 0x623780);
   (0x6237a0, 0x6237a8); (0x6237b8, 0x644b30); (0x644b38, 0x645068);
   (* [comment removed for export] *)
   (0x238e0, 0x238ee); (0x23900, 0x2390a); (0x23920, 0x23930); (0x23940, 0x2395d); (0x23a40, 0x23a67); (0x23aa0, 0x23ab0); (0x23ac0, 0x23ad2); (0x23b00, 0x23b13); (0x23ba0, 0x23bac); (0x23bc0, 0x23bd8); (0x23da0, 0x23dab); (0x23f40, 0x23f50); (0x23f60, 0x23f6c); (0x23fe0, 0x23fed); (0x24040, 0x2404c); (0x240a0, 0x240b1); (0x24180, 0x2418a); (0x24240, 0x2424f); (0x24260, 0x24276); (0x242e0, 0x242eb); (0x24340, 0x24350); (0x24520, 0x2452e); (0x24ec0, 0x24ecf); (0x24ee0, 0x24ef3); (0x24f20, 0x24f2f); (0x24f40, 0x24f51); (0x24f80, 0x24f97); (0x252e0, 0x252f6); (0x25320, 0x2532f); (0x255e0, 0x255f1); (0x256a0, 0x256af); (0x256c0, 0x256dd); (0x25700, 0x2570b); (0x25720, 0x2572e); (0x25780, 0x25791); (0x257c0, 0x257d6); (0x25800, 0x25814); (0x25840, 0x25865); (0x260e0, 0x260f3); (0x26120, 0x26128); (0x26140, 0x26150); (0x26600, 0x2660d); (0x26620, 0x26631); (0x26660, 0x26679); (0x26700, 0x26712); (0x26740, 0x2674e); (0x26760, 0x2676f); (0x26780, 0x2678f); (0x267a0, 0x267b0); (0x267c0, 0x267d6); (0x26880, 0x2688e); (0x268a0, 0x268b2); (0x268e0, 0x268f9); (0x236a0, 0x236b1); (0x23b40, 0x23b6f); (0x23c00, 0x23c30); (0x23c60, 0x23c94); (0x23cc0, 0x23cf5); (0x23d40, 0x23d65); (0x24e60, 0x24e85); (0x24540, 0x2455b); (0x24fc0, 0x24fe5); (0x25020, 0x2504f); (0x25080, 0x250ae); (0x250e0, 0x250ff); (0x25120, 0x25153); (0x25180, 0x251b8); (0x251e0, 0x2521a); (0x25240, 0x2528d); (0x266a0, 0x266c3); (0x26800, 0x26854); (0x24580, 0x24604);
   (* [comment removed for export] *)
   (0x10d35, 0x10d3f); (0x14f06, 0x14f0a); (0x16280, 0x16340); (0x1acad, 0x1acce); (0x1f59e, 0x1f5b3); (0x1f5b3, 0x1f5ca);
   (0x21e40, 0x21ec0); (0x22edb, 0x22ee2); (0x2a260, 0x2a270); (0x612c00, 0x612c10);
   (* [comment removed for export] *)
   (0x23720, 0x23740); (0x23760, 0x2376a); (0x23780, 0x2378e); (0x237a0, 0x237b2); (0x237e0, 0x237ee); (0x23800, 0x23817); (0x23840, 0x2384b); (0x23860, 0x23871);
   (0x23980, 0x23991); (0x239c0, 0x239d2); (0x23a00, 0x23a18); (0x23d20, 0x23d29); (0x23dc0, 0x23dc8); (0x23de0, 0x23dfc); (0x23e20, 0x23e33); (0x23e60, 0x23e71);
   (0x23ea0, 0x23eb0); (0x23ec0, 0x23edf); (0x23f00, 0x23f0f); (0x23f20, 0x23f2f); (0x23f80, 0x23f8c); (0x23fa0, 0x23fb3); (0x24000, 0x2400d); (0x24020, 0x2402f);
   (0x24060, 0x2406c); (0x24080, 0x2408f); (0x240e0, 0x240ea); (0x24100, 0x2410a); (0x24120, 0x24131); (0x24160, 0x2416b); (0x241a0, 0x241b2); (0x241e0, 0x241f3);
   (0x24220, 0x2422f); (0x242a0, 0x242b3); (0x24360, 0x24371); (0x243a0, 0x243b3); (0x243e0, 0x24418); (0x24440, 0x24480); (0x244a0, 0x244b2); (0x244e0, 0x244ff);
   (0x24640, 0x2464e); (0x24660, 0x2466d); (0x24680, 0x24694); (0x246c0, 0x246d7); (0x24700, 0x24710); (0x24720, 0x24737); (0x24760, 0x24779); (0x247a0, 0x247b2);
   (0x247e0, 0x247f3); (0x24820, 0x2483f); (0x24860, 0x24879); (0x248a0, 0x248ba); (0x248e0, 0x248f0); (0x24900, 0x24913); (0x24940, 0x24950); (0x24960, 0x2496d);
   (0x24980, 0x24991); (0x249c0, 0x249d3); (0x24a00, 0x24a0f); (0x24a20, 0x24a47); (0x24a80, 0x24a97); (0x24ac0, 0x24ad1); (0x24b00, 0x24b1d); (0x24b40, 0x24b51);
   (0x24b80, 0x24b9f); (0x24bc0, 0x24bd4); (0x24c00, 0x24c13); (0x24c40, 0x24c50); (0x24c60, 0x24c71); (0x24ce0, 0x24cf7); (0x24d20, 0x24d2e); (0x24d40, 0x24d56);
   (0x24d80, 0x24d94); (0x24dc0, 0x24dd0); (0x24de0, 0x24df2); (0x24e20, 0x24e2c); (0x24e40, 0x24e4d); (0x252c0, 0x252d0); (0x25340, 0x25350); (0x25360, 0x25384);
   (0x253c0, 0x253d0); (0x253e0, 0x253f4); (0x25420, 0x25433); (0x25460, 0x25470); (0x25480, 0x25494); (0x254c0, 0x254d0); (0x254e0, 0x254f8); (0x25520, 0x25537);
   (0x25560, 0x25572); (0x255a0, 0x255b5); (0x25620, 0x25644); (0x25680, 0x25690); (0x25960, 0x25971); (0x259a0, 0x259ae); (0x259c0, 0x259d2); (0x25a00, 0x25a36);
   (0x25a60, 0x25a7b); (0x25aa0, 0x25ac0); (0x25ae0, 0x25af9); (0x25b20, 0x25b57); (0x25b80, 0x25b9c); (0x25bc0, 0x25bea); (0x25c20, 0x25c3e); (0x25c60, 0x25c74);
   (0x25ca0, 0x25cad); (0x25cc0, 0x25cd7); (0x25d00, 0x25d14); (0x25d40, 0x25d50); (0x25d60, 0x25d9b); (0x25dc0, 0x25dd0); (0x25de0, 0x25df0); (0x25e00, 0x25e0f);
   (0x25e20, 0x25e32); (0x25e60, 0x25e73); (0x25ea0, 0x25eaf); (0x25ec0, 0x25ecf); (0x25ee0, 0x25eef); (0x25f00, 0x25f0f); (0x25f20, 0x25f2f); (0x25f40, 0x25f4f);
   (0x25f60, 0x25f7d); (0x25fa0, 0x25fae); (0x25fc0, 0x25fd1); (0x26000, 0x26010); (0x26060, 0x26071); (0x260a0, 0x260aa); (0x260c0, 0x260ce); (0x261a0, 0x261b1);
   (0x261e0, 0x261ec); (0x26200, 0x26211); (0x26240, 0x2625f); (0x264e0, 0x26502); (0x26540, 0x26556); (0x26580, 0x26596); (0x26960, 0x26973); (0x269a0, 0x269aa);
   (0x269c0, 0x269e5); (0x26a20, 0x26a2b); (0x26a40, 0x26a50); (0x26a60, 0x26a68); (0x26a80, 0x26a92); (0x26ac0, 0x26ad9); (0x26b00, 0x26b0f); (0x26b20, 0x26b39);
   (0x26b60, 0x26b6d); (0x26b80, 0x26b91); (0x26bc0, 0x26bd1); (0x26c00, 0x26c11); (0x26c40, 0x26c51); (0x26c80, 0x26c8b); (0x26ca0, 0x26cb9); (0x26ce0, 0x26cf1);
   (0x26d20, 0x26d2e); (0x26d40, 0x26d51); (0x26d80, 0x26d8d); (0x26da0, 0x26dab); (0x26dc0, 0x26dce); (0x26de0, 0x26deb); (0x26e00, 0x26e16); (0x26e40, 0x26e56);
   (0x26e80, 0x26e8e); (0x26ea0, 0x26eb0); (0x26ec0, 0x26edb); (0x26f40, 0x26f4e); (0x26f60, 0x26f6f); (0x26f80, 0x26f88); (0x26fa0, 0x26fa8); (0x26fc0, 0x26fc8);
   (0x26fe0, 0x26fe8); (0x27000, 0x27008); (0x27020, 0x27028); (0x27040, 0x27048); (0x27060, 0x27068); (0x27080, 0x27088); (0x270a0, 0x270a8); (0x27100, 0x27111);
   (0x27140, 0x2714c); (0x27160, 0x27173); (0x271a0, 0x271ad); (0x271c0, 0x271d4); (0x27200, 0x2720e); (0x27220, 0x2722e); (0x26360, 0x263e4); (0x26420, 0x264a4)].
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
