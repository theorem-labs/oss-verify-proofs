(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Permutation.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require BackingAlgebra.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Mem Frame Cells Step Arr.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require NodesA_madv.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import R_sizeclass.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import R_cache_defs R_prim_defs R_thread R_m2s R_poison R_leaves R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state TopA_iodefs.
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
  /\ ro_cells asegs m 0x1ab99d [C1 (Z_to_bv 8 0)] /\ ro_cells asegs m 0x1ab9a4 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x10ab58 [C8 (Z_to_bv 64 0x117578)] /\ ro_cells asegs m 0x10ab88 [C8 (Z_to_bv 64 0x10ca38)]
  /\ ro_cells asegs m 0x10ca38 [C8 (Z_to_bv 64 0x100e9c)] /\ ro_cells asegs m 0x117595 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x11aa7c [C4 (Z_to_bv 64 30)] /\ ro_cells asegs m 0x1ab8ca [C1 (Z_to_bv 8 1)]
  (* [comment removed for export] *)
  /\ ro_cells asegs m 0x10b7d8 [C8 (Z_to_bv 64 0x10f180)] /\ ro_cells asegs m 0x10b838 [C8 (Z_to_bv 64 0x66cf88)]
  (* [comment removed for export] *)
  /\ ro_cells asegs m 0x10b6c8 [C8 (Z_to_bv 64 0x11aa59)] /\ ro_cells asegs m 0x11aa59 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x10ca40 [C8 (Z_to_bv 64 0x1012a0)] /\ ro_cells asegs m 0x10c8f0 [C8 (Z_to_bv 64 0x100da0)]
  /\ ro_cells asegs m 0x10c9e8 [C8 (Z_to_bv 64 0x101728)] /\ ro_cells asegs m 0x10c8c8 [C8 (Z_to_bv 64 0x1014ec)]
  /\ ro_cells asegs m 0x1ab9a3 [C1 (Z_to_bv 8 1)]    (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0x117538 [C8 (Z_to_bv 64 (2 ^ 40))] /\ rw_cells asegs m 0x117540 [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)]
  /\ rw_cells asegs m 0x19bfe2 [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m 0x1ab8ca [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x10ab58 [C8 (Z_to_bv 64 0x117578)] /\ rw_cells asegs m (0x117578 + 44) [C4 (Z_to_bv 64 4096)]
  /\ rw_cells asegs m (0x117578 + 52) [C4 (Z_to_bv 64 190)] /\ rw_cells asegs m (0x117578 + 85) [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m (0x64cf48 + 16) [C4 (Z_to_bv 64 0)] /\ rw_cells asegs m 0x10b7b8 [C8 (Z_to_bv 64 16)]
  /\ rw_cells asegs m 0x1ab840 [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m 0x1195dc [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m (l_TCX L + 8) [C4 (Z_to_bv 64 0)]
  /\ stk asegs m (l_T L + 2768) (l_T L + 3168)
  (* [comment removed for export] *)
  /\ rw_cells asegs m (l_T L) [C8 (Z_to_bv 64 (l_TCX L))]
  (* [comment removed for export] *)
  /\ rw_cells asegs m (g_MFHooks + 8) [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m i_q_max [C8 (Z_to_bv 64 0x10000000); C8 (Z_to_bv 64 0xE666661); C8 (Z_to_bv 64 0x100000)]
  /\ rw_cells asegs m (g_asan_flags + 48) [C4 (Z_to_bv 64 0)]
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0x10aba0 [C8 (Z_to_bv 64 1)] /\ rw_cells asegs m 0x1ab983 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x1ab99c [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m 0x10b838 [C8 (Z_to_bv 64 0x66cf88)]
  /\ rw_cells asegs m 0x66d208 [C8 (Z_to_bv 64 4096)]
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
  [(0x10ef50, 0x10f184); (0x10f1a0, 0x10f1a8); (0x10f1c0, 0x10f1c8); (0x10f1e0, 0x10f1e8); (0x10f200, 0x10f204); (0x10f220, 0x10f224); (0x10f240, 0x116718);
   (0x63c3d0, 0x64c3d0);
   (0x64c3d0, 0x64cef0); (0x64cef8, 0x64cf40);
   (0x64cf60, 0x64cf68); (0x64cf78, 0x66d208); (0x66d210, 0x66e2f0); (0x66e2f8, 0x66e828)].
(* [comment removed for export] *)
Definition CS_ACC : list (Z * Z) :=
  [(0x10ef50, 0x10f184); (0x10f1a0, 0x10f1a8); (0x10f1c0, 0x10f1c8); (0x10f1e0, 0x10f1e8); (0x10f200, 0x10f204); (0x10f220, 0x10f224); (0x10f240, 0x10f580); (0x1166c0, 0x116718);
   (0x63c3d0, 0x64c3d0);
   (0x64c3d0, 0x64cef0); (0x64cef8, 0x64cf40);
   (0x64cf60, 0x64cf68); (0x64cf78, 0x66e2f0); (0x66e2f8, 0x66e828);
   (* [comment removed for export] *)
   (0x25200, 0x2520e); (0x25220, 0x2522a); (0x25240, 0x25250); (0x25260, 0x2527d); (0x25360, 0x25387); (0x253c0, 0x253d0); (0x253e0, 0x253f2); (0x25420, 0x25433); (0x254c0, 0x254cc); (0x254e0, 0x254f8); (0x256c0, 0x256cb); (0x25860, 0x25870); (0x25880, 0x2588c); (0x25900, 0x2590d); (0x25960, 0x2596c); (0x259c0, 0x259d1); (0x25a80, 0x25a8a); (0x2aaa0, 0x2aaad); (0x25be0, 0x25bef); (0x25c00, 0x25c16); (0x25c80, 0x25c8b); (0x25ee0, 0x25ef0); (0x26140, 0x2614e); (0x26be0, 0x26bef); (0x26c00, 0x26c13); (0x26c40, 0x26c4f); (0x26c60, 0x26c71); (0x26ca0, 0x26cb7); (0x27000, 0x27016); (0x27040, 0x2704f); (0x27400, 0x27411); (0x274c0, 0x274cf); (0x274e0, 0x274fd); (0x27520, 0x2752b); (0x27540, 0x2754e); (0x275a0, 0x275b1); (0x27760, 0x27776); (0x277a0, 0x277b4); (0x277e0, 0x27805); (0x28a60, 0x28a73); (0x28aa0, 0x28aa8); (0x28ac0, 0x28ad0); (0x2aa60, 0x2aa7c); (0x2aac0, 0x2aad5); (0x29bc0, 0x29bcd); (0x29be0, 0x29bf1); (0x29c20, 0x29c39); (0x29cc0, 0x29cd2); (0x29d00, 0x29d0e); (0x29d20, 0x29d2f); (0x29d40, 0x29d4f); (0x29d60, 0x29d70); (0x29d80, 0x29d96); (0x29e40, 0x29e4e); (0x29e60, 0x29e72); (0x29ea0, 0x29eb9); (0x24680, 0x24691); (0x25460, 0x2548f); (0x25520, 0x25550); (0x25580, 0x255b4); (0x255e0, 0x25615); (0x25660, 0x25685); (0x26b80, 0x26ba5); (0x26160, 0x2617b); (0x26ce0, 0x26d05); (0x26d40, 0x26d6f); (0x26da0, 0x26dce); (0x26e00, 0x26e1f); (0x26e40, 0x26e73); (0x26ea0, 0x26ed8); (0x26f00, 0x26f3a); (0x26f60, 0x26fad); (0x29c60, 0x29c83); (0x29dc0, 0x29e14); (0x261a0, 0x26224);
   (* [comment removed for export] *)
   (0x248c0, 0x248d5); (0x24900, 0x2490b); (0x24920, 0x24945); (0x24980, 0x2498c); (0x249a0, 0x249b1); (0x249e0, 0x249f1); (0x24a20, 0x24a2b); (0x24a40, 0x24a50); (0x24a60, 0x24a6e); (0x24a80, 0x24a91); (0x24c20, 0x24c2d); (0x24c40, 0x24c4b); (0x24c60, 0x24c70); (0x24c80, 0x24ca1); (0x24ce0, 0x24cef); (0x24d00, 0x24d13); (0x24d40, 0x24d55); (0x24d80, 0x24d92); (0x24dc0, 0x24dd0); (0x24de0, 0x24def); (0x24e00, 0x24e14); (0x24e40, 0x24e50); (0x24e60, 0x24e78); (0x24ea0, 0x24eb1); (0x24f20, 0x24f45); (0x24fa0, 0x24fb3); (0x24fe0, 0x24feb); (0x25040, 0x2504c); (0x252a0, 0x252b1); (0x252e0, 0x252f2); (0x25780, 0x25791); (0x25aa0, 0x25ab2); (0x25ca0, 0x25caf); (0x25cc0, 0x25ccf); (0x25f80, 0x25f91); (0x26320, 0x2632e); (0x26340, 0x26354); (0x26380, 0x26397); (0x263c0, 0x263d5); (0x26400, 0x26411); (0x26440, 0x26450); (0x26460, 0x26471); (0x264a0, 0x264b2); (0x264e0, 0x264f1); (0x26520, 0x26531); (0x26560, 0x26578); (0x265a0, 0x265b4); (0x265e0, 0x265f5); (0x26620, 0x26633); (0x26660, 0x26670); (0x26680, 0x2668d); (0x266a0, 0x266b1); (0x266e0, 0x266f3); (0x26720, 0x2672f); (0x26740, 0x26767); (0x275e0, 0x275fd); (0x27620, 0x27635); (0x27660, 0x27673); (0x276a0, 0x276ad); (0x276c0, 0x276df); (0x27700, 0x27721); (0x28b20, 0x28b31); (0x28b60, 0x28b6c); (0x28b80, 0x28b91); (0x28bc0, 0x28bdf); (0x2a600, 0x2a611); (0x2a660, 0x2a66e); (0x2a680, 0x2a693); (0x2a740, 0x2a750); (0x2a7a0, 0x2a7b4); (0x2a7e0, 0x2a7f0); (0x2a8e0, 0x2a8ed); (0x2a9c0, 0x2a9cd); (0x2a9e0, 0x2a9f3); (0x2ab00, 0x2ab12); (0x2ab40, 0x2ab8d); (0x2abc0, 0x2abcd); (0x2abe0, 0x2abf3); (0x2ac20, 0x2ac39); (0x2ac60, 0x2ac7d); (0x2aca0, 0x2acb1); (0x2ace0, 0x2acf4); (0x2ad20, 0x2ad2d); (0x2ad40, 0x2ad51); (0x2ad80, 0x2ad92); (0x2adc0, 0x2add0); (0x2ade0, 0x2adf7); (0x2ae20, 0x2ae36); (0x2ae60, 0x2ae72); (0x2aea0, 0x2aeb8); (0x2aee0, 0x2af36); (0x2af60, 0x2af77); (0x2afa0, 0x2afae); (0x2afc0, 0x2afd7); (0x2b000, 0x2b016); (0x2b040, 0x2b054); (0x2b080, 0x2b093); (0x2b0c0, 0x2b0d0); (0x2b0e0, 0x2b0ed); (0x2b100, 0x2b10e); (0x2b120, 0x2b130); (0x2b140, 0x2b14f); (0x2b160, 0x2b16f); (0x2b180, 0x2b198); (0x2b1c0, 0x2b1ce); (0x25320, 0x25338); (0x25a20, 0x25a2a); (0x25a40, 0x25a51); (0x256e0, 0x256e8); (0x257c0, 0x257d0); (0x25820, 0x2582f); (0x25840, 0x2584f); (0x26b40, 0x26b4c); (0x26b60, 0x26b6d); (0x26fe0, 0x26ff0); (0x2ab40, 0x2ab8d); (0x2aee0, 0x2af36); (0x28ce0, 0x28d64); (0x28da0, 0x28e24);
   (* [comment removed for export] *)
   (0x10db7, 0x10dc1); (0x15265, 0x15269); (0x16700, 0x16780); (0x1b4c4, 0x1b4e5); (0x201ea, 0x201ff); (0x201ff, 0x20216);
   (0x22c40, 0x22cc0); (0x23ebf, 0x23ec6); (0x2e320, 0x2e330); (0x63c3c0, 0x63c3d0)].
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
