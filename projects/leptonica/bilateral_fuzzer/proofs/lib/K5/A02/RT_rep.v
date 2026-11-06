(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Permutation.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require BackingAlgebra.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Mem Frame Cells Step Arr.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require NodesA_madv.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import RT_iface.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import R_sizeclass.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import R_cache_defs R_prim_defs R_thread R_m2s R_poison R_leaves R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state TopA_iodefs.
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
  /\ ro_cells asegs m 0x19e89d [C1 (Z_to_bv 8 0)] /\ ro_cells asegs m 0x19e8a4 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0xfdb08 [C8 (Z_to_bv 64 0x10a478)] /\ ro_cells asegs m 0xfdb38 [C8 (Z_to_bv 64 0xff9d8)]
  /\ ro_cells asegs m 0xff9d8 [C8 (Z_to_bv 64 0xf3e48)] /\ ro_cells asegs m 0x10a495 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x10d97c [C4 (Z_to_bv 64 30)] /\ ro_cells asegs m 0x19e7ca [C1 (Z_to_bv 8 1)]
  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xfe788 [C8 (Z_to_bv 64 0x102120)] /\ ro_cells asegs m 0xfe7e8 [C8 (Z_to_bv 64 0x65fe88)]
  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xfe678 [C8 (Z_to_bv 64 0x10d959)] /\ ro_cells asegs m 0x10d959 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0xff9e0 [C8 (Z_to_bv 64 0xf424c)] /\ ro_cells asegs m 0xff890 [C8 (Z_to_bv 64 0xf3d4c)]
  /\ ro_cells asegs m 0xff988 [C8 (Z_to_bv 64 0xf46d4)] /\ ro_cells asegs m 0xff868 [C8 (Z_to_bv 64 0xf4498)]
  /\ ro_cells asegs m 0x19e8a3 [C1 (Z_to_bv 8 1)]    (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0x10a438 [C8 (Z_to_bv 64 (2 ^ 40))] /\ rw_cells asegs m 0x10a440 [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)]
  /\ rw_cells asegs m 0x18eee2 [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m 0x19e7ca [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0xfdb08 [C8 (Z_to_bv 64 0x10a478)] /\ rw_cells asegs m (0x10a478 + 44) [C4 (Z_to_bv 64 4096)]
  /\ rw_cells asegs m (0x10a478 + 52) [C4 (Z_to_bv 64 190)] /\ rw_cells asegs m (0x10a478 + 85) [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m (0x63fe48 + 16) [C4 (Z_to_bv 64 0)] /\ rw_cells asegs m 0xfe768 [C8 (Z_to_bv 64 16)]
  /\ rw_cells asegs m 0x19e740 [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m 0x10c4dc [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m (l_TCX L + 8) [C4 (Z_to_bv 64 0)]
  /\ stk asegs m (l_T L + 2768) (l_T L + 3168)
  (* [comment removed for export] *)
  /\ rw_cells asegs m (l_T L) [C8 (Z_to_bv 64 (l_TCX L))]
  (* [comment removed for export] *)
  /\ rw_cells asegs m (g_MFHooks + 8) [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m i_q_max [C8 (Z_to_bv 64 0x10000000); C8 (Z_to_bv 64 0xE666661); C8 (Z_to_bv 64 0x100000)]
  /\ rw_cells asegs m (g_asan_flags + 48) [C4 (Z_to_bv 64 0)]
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xfdb50 [C8 (Z_to_bv 64 1)] /\ rw_cells asegs m 0x19e883 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x19e89c [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m 0xfe7e8 [C8 (Z_to_bv 64 0x65fe88)]
  /\ rw_cells asegs m 0x660108 [C8 (Z_to_bv 64 4096)]
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
  fs_const FSB m /\ fs_cls_rep FSB 0 (fs0 Σ) m /\ fs_cls_rep FSB 1 (fs2 Σ) m /\ (fs_cls_rep FSB 6 (fs4 Σ) m /\ fs_cls_rep FSB 2 (fs1 Σ) m)
  /\ rw_cells asegs m tpA [C8 (Z_to_bv 64 FSB)]
  /\ (exists dtvbeg, 0 < dtvbeg < 2 ^ 64 /\ tga_cells (l_DTV L) dtvbeg m)
  /\ (exists tb te, ttls_cells (l_T L) m tb te)
  /\ fs_busy L (frames Σ) m.

(* [comment removed for export] *)
Definition ia_rep (Σ : rtsA) (m : mem) : Prop := exists b, ia_state b m.

(* [comment removed for export] *)
Definition CS_W : list (Z * Z) :=
  [(0x101ef0, 0x102124); (0x102140, 0x102148); (0x102160, 0x102168); (0x102180, 0x102188); (0x1021a0, 0x1021a4); (0x1021c0, 0x1021c4); (0x1021e0, 0x109618);
   (0x62f2d0, 0x63f2d0);
   (0x63f2d0, 0x63fdf0); (0x63fdf8, 0x63fe40);
   (0x63fe60, 0x63fe68); (0x63fe78, 0x660108); (0x660110, 0x6611f0); (0x6611f8, 0x661728)].
(* [comment removed for export] *)
Definition CS_ACC : list (Z * Z) :=
  [(0x101ef0, 0x102124); (0x102140, 0x102148); (0x102160, 0x102168); (0x102180, 0x102188); (0x1021a0, 0x1021a4); (0x1021c0, 0x1021c4); (0x1021e0, 0x102520); (0x1095a0, 0x109618);
   (0x62f2d0, 0x63f2d0);
   (0x63f2d0, 0x63fdf0); (0x63fdf8, 0x63fe40);
   (0x63fe60, 0x63fe68); (0x63fe78, 0x6611f0); (0x6611f8, 0x661728);
   (* [comment removed for export] *)
   (0x251c0, 0x251ce); (0x251e0, 0x251ea); (0x25200, 0x25210); (0x25220, 0x2523d); (0x25320, 0x25347); (0x25380, 0x25390); (0x253a0, 0x253b2); (0x253e0, 0x253f3); (0x25480, 0x2548c); (0x254a0, 0x254b8); (0x25680, 0x2568b); (0x25820, 0x25830); (0x25840, 0x2584c); (0x258c0, 0x258cd); (0x25920, 0x2592c); (0x25980, 0x25991); (0x25a40, 0x25a4a); (0x2a9c0, 0x2a9cd); (0x25ba0, 0x25baf); (0x25bc0, 0x25bd6); (0x25c40, 0x25c4b); (0x25ea0, 0x25eb0); (0x26100, 0x2610e); (0x26ba0, 0x26baf); (0x26bc0, 0x26bd3); (0x26c00, 0x26c0f); (0x26c20, 0x26c31); (0x26c60, 0x26c77); (0x26fc0, 0x26fd6); (0x27000, 0x2700f); (0x27380, 0x27391); (0x27440, 0x2744f); (0x27460, 0x2747d); (0x274a0, 0x274ab); (0x274c0, 0x274ce); (0x27520, 0x27531); (0x276e0, 0x276f6); (0x27720, 0x27734); (0x27760, 0x27785); (0x289e0, 0x289f3); (0x28a20, 0x28a28); (0x28a40, 0x28a50); (0x2a980, 0x2a99c); (0x2a9e0, 0x2a9f5); (0x29b40, 0x29b4d); (0x29b60, 0x29b71); (0x29ba0, 0x29bb9); (0x29c40, 0x29c52); (0x29c80, 0x29c8e); (0x29ca0, 0x29caf); (0x29cc0, 0x29ccf); (0x29ce0, 0x29cf0); (0x29d00, 0x29d16); (0x29dc0, 0x29dce); (0x29de0, 0x29df2); (0x29e20, 0x29e39); (0x24640, 0x24651); (0x25420, 0x2544f); (0x254e0, 0x25510); (0x25540, 0x25574); (0x255a0, 0x255d5); (0x25620, 0x25645); (0x26b40, 0x26b65); (0x26120, 0x2613b); (0x26ca0, 0x26cc5); (0x26d00, 0x26d2f); (0x26d60, 0x26d8e); (0x26dc0, 0x26ddf); (0x26e00, 0x26e33); (0x26e60, 0x26e98); (0x26ec0, 0x26efa); (0x26f20, 0x26f6d); (0x29be0, 0x29c03); (0x29d40, 0x29d94); (0x26160, 0x261e4);
   (* [comment removed for export] *)
   (0x24880, 0x24895); (0x248c0, 0x248cb); (0x248e0, 0x24905); (0x24940, 0x2494c); (0x24960, 0x24971); (0x249a0, 0x249b1); (0x249e0, 0x249eb); (0x24a00, 0x24a10); (0x24a20, 0x24a2e); (0x24a40, 0x24a51); (0x24be0, 0x24bed); (0x24c00, 0x24c0b); (0x24c20, 0x24c30); (0x24c40, 0x24c61); (0x24ca0, 0x24caf); (0x24cc0, 0x24cd3); (0x24d00, 0x24d15); (0x24d40, 0x24d52); (0x24d80, 0x24d90); (0x24da0, 0x24daf); (0x24dc0, 0x24dd4); (0x24e00, 0x24e10); (0x24e20, 0x24e38); (0x24e60, 0x24e71); (0x24ee0, 0x24f05); (0x24f60, 0x24f73); (0x24fa0, 0x24fab); (0x25000, 0x2500c); (0x25260, 0x25271); (0x252a0, 0x252b2); (0x25740, 0x25751); (0x25a60, 0x25a72); (0x25c60, 0x25c6f); (0x25c80, 0x25c8f); (0x25f40, 0x25f51); (0x262e0, 0x262ee); (0x26300, 0x26314); (0x26340, 0x26357); (0x26380, 0x26395); (0x263c0, 0x263d1); (0x26400, 0x26410); (0x26420, 0x26431); (0x26460, 0x26472); (0x264a0, 0x264b1); (0x264e0, 0x264f1); (0x26520, 0x26538); (0x26560, 0x26574); (0x265a0, 0x265b5); (0x265e0, 0x265f3); (0x26620, 0x26630); (0x26640, 0x2664d); (0x26660, 0x26671); (0x266a0, 0x266b3); (0x266e0, 0x266ef); (0x26700, 0x26727); (0x27560, 0x2757d); (0x275a0, 0x275b5); (0x275e0, 0x275f3); (0x27620, 0x2762d); (0x27640, 0x2765f); (0x27680, 0x276a1); (0x28aa0, 0x28ab1); (0x28ae0, 0x28aec); (0x28b00, 0x28b11); (0x28b40, 0x28b5f); (0x2a580, 0x2a591); (0x2a5e0, 0x2a5ee); (0x2a600, 0x2a613); (0x2a6c0, 0x2a6d0); (0x2a720, 0x2a734); (0x2a760, 0x2a770); (0x2a800, 0x2a80d); (0x2a8e0, 0x2a8ed); (0x2a900, 0x2a913); (0x2aa20, 0x2aa32); (0x2aa60, 0x2aaad); (0x2aae0, 0x2aaed); (0x2ab00, 0x2ab13); (0x2ab40, 0x2ab59); (0x2ab80, 0x2ab9d); (0x2abc0, 0x2abd1); (0x2ac00, 0x2ac14); (0x2ac40, 0x2ac4d); (0x2ac60, 0x2ac71); (0x2aca0, 0x2acb2); (0x2ace0, 0x2acf0); (0x2ad00, 0x2ad17); (0x2ad40, 0x2ad56); (0x2ad80, 0x2ad92); (0x2adc0, 0x2add8); (0x2ae00, 0x2ae56); (0x2ae80, 0x2ae97); (0x2aec0, 0x2aece); (0x2aee0, 0x2aef7); (0x2af20, 0x2af36); (0x2af60, 0x2af74); (0x2afa0, 0x2afb3); (0x2afe0, 0x2aff0); (0x2b000, 0x2b00d); (0x2b020, 0x2b02e); (0x2b040, 0x2b050); (0x2b060, 0x2b06f); (0x2b080, 0x2b08f); (0x2b0a0, 0x2b0b8); (0x2b0e0, 0x2b0ee); (0x252e0, 0x252f8); (0x259e0, 0x259ea); (0x25a00, 0x25a11); (0x256a0, 0x256a8); (0x25780, 0x25790); (0x257e0, 0x257ef); (0x25800, 0x2580f); (0x26b00, 0x26b0c); (0x26b20, 0x26b2d); (0x26fa0, 0x26fb0); (0x2aa60, 0x2aaad); (0x2ae00, 0x2ae56); (0x28c60, 0x28ce4); (0x28d20, 0x28da4);
   (* [comment removed for export] *)
   (0x10d97, 0x10da1); (0x1522f, 0x15233); (0x166c0, 0x16780); (0x1b48e, 0x1b4af); (0x201b4, 0x201c9); (0x201c9, 0x201e0);
   (0x22c00, 0x22c80); (0x23e89, 0x23e90); (0x2e240, 0x2e250); (0x62f2c0, 0x62f2d0)].
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
Lemma ART_wf : rt_wf Σ.
Proof using Σ m HA. exact (proj1 HA). Qed.
Lemma ART_consts : consts_rep (lay Σ) m.
Proof using Σ m HA. exact (proj1 (proj2 HA)). Qed.
Lemma ART_prim : prim_rep Σ m.
Proof using Σ m HA. exact (proj1 (proj2 (proj2 HA))). Qed.
Lemma ART_cache : cache_rep Σ m.
Proof using Σ m HA. exact (proj1 (proj2 (proj2 (proj2 HA)))). Qed.
Lemma ART_chunk : chunk_rep Σ m.
Proof using Σ m HA. exact (proj1 (proj2 (proj2 (proj2 (proj2 HA))))). Qed.
Lemma ART_sec : sec_rep Σ m.
Proof using Σ m HA. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HA)))))). Qed.
Lemma ART_quar : quar_rep Σ m.
Proof using Σ m HA. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HA))))))). Qed.
Lemma ART_dep : dep_rep (lay Σ) (dep Σ) m.
Proof using Σ m HA. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HA)))))))). Qed.
Lemma ART_fs : fs_rep Σ m.
Proof using Σ m HA. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HA))))))))). Qed.
Lemma ART_ia : ia_rep Σ m.
Proof using Σ m HA. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HA)))))))))). Qed.
Lemma ART_shadow : shadow_rep (lay Σ) m.
Proof using Σ m HA. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HA))))))))))). Qed.
Lemma ART_vis : vis_rep (lay Σ) (rtA_allow Σ) m.
Proof using Σ m HA. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HA))))))))))). Qed.
End Proj.

Lemma ART_intro : forall Σ m, rt_wf Σ -> consts_rep (lay Σ) m -> prim_rep Σ m -> cache_rep Σ m -> chunk_rep Σ m ->
  sec_rep Σ m -> quar_rep Σ m -> dep_rep (lay Σ) (dep Σ) m -> fs_rep Σ m -> ia_rep Σ m -> shadow_rep (lay Σ) m ->
  vis_rep (lay Σ) (rtA_allow Σ) m -> ART_A Σ m.
Proof. intros. unfold ART_A. repeat (split; [assumption|]). assumption. Qed.
