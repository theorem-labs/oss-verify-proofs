(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Permutation.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require BackingAlgebra.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Mem Frame Cells Step Arr.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require NodesA_madv.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import AsanAcct.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import R_sizeclass.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import R_cache_defs R_prim_defs R_thread R_m2s R_poison R_leaves R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state TopA_iodefs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_RT_rep () := "C46Stdlib5Lists4List2hdI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC69OSSVerify5KrLib2K53B238RT_state5batchC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53B238RT_iface6rt_sig01C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C46Stdlib5Lists4List6filterI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib2K53B238RT_state4vposC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes8list_indC4ELinuxProcessSemantics?LinuxProcessSem5State:map_removeC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbK47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02I46Stdlib7Sorting;Permutation;Permutation00K46Stdlib7Sorting;Permutation;Permutation01K46Stdlib7Sorting;Permutation;Permutation02K46Stdlib7Sorting;Permutation;Permutation03C46Stdlib7Sorting;Permutation@Permutation_reflC46Stdlib7Sorting;PermutationAPermutation_transC46Stdlib7Sorting;Permutation?Permutation_indc69OSSVerify5KrLib2K53B236RT_rep<perm_filter'C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init5Logic5proj2K47Corelib7Numbers7BinNums1Z01C46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallI47Corelib4Init5Logic3and00C46Stdlib5Lists4List9filter_InI46Stdlib5Lists4List6Exists00C46Stdlib5Lists4List7existsbI47Corelib7Numbers7BinNums1Z00c69OSSVerify5KrLib2K53B236RT_rep?filter_cons_posC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef:Forall_indC69OSSVerify5KrLib2K52AS>BackingAlgebra7coveredC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS>BackingAlgebra5in_ivC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6ltb_geC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z3powC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z6leb_leK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03C47Corelib4Init5Logic6eq_indC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1N00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205C69OSSVerify5KrLib2K52AG6Shadow4shadC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notK47Corelib4Init5Logic3and01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7add_0_rI47Corelib4Init5Logic5False00C69OSSVerify5KrLib2K53B238RT_state5rt_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state3layC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B236RT_rep:consts_repC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B236RT_rep8prim_repC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B236RT_rep9cache_repC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B236RT_rep9chunk_repC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B236RT_rep7sec_repC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B236RT_rep8quar_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state3depC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B236RT_rep7dep_repC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B236RT_rep6fs_repC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B236RT_rep6ia_repC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B236RT_rep:shadow_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state9rtA_allowC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B236RT_rep7vis_repC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1I47Corelib4Init9Datatypes6option00c69OSSVerify5KrLib2K53B236RT_rep5ART_AC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53B238RT_state4rtsA00C1?~~~~~~~~~~~~~~~".
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
  /\ ro_cells asegs m 0x2d66dd [C1 (Z_to_bv 8 0)] /\ ro_cells asegs m 0x2d66e4 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x225d18 [C8 (Z_to_bv 64 0x2422b8)] /\ ro_cells asegs m 0x225d48 [C8 (Z_to_bv 64 0x227e90)]
  /\ ro_cells asegs m 0x227e90 [C8 (Z_to_bv 64 0x217f04)] /\ ro_cells asegs m 0x2422d5 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x2457bc [C4 (Z_to_bv 64 30)] /\ ro_cells asegs m 0x2d660a [C1 (Z_to_bv 8 1)]
  (* [comment removed for export] *)
  /\ ro_cells asegs m 0x2269b8 [C8 (Z_to_bv 64 0x22a5e0)] /\ ro_cells asegs m 0x226b70 [C8 (Z_to_bv 64 0x797ed8)]
  (* [comment removed for export] *)
  /\ ro_cells asegs m 0x2268a0 [C8 (Z_to_bv 64 0x245799)] /\ ro_cells asegs m 0x245799 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x227e98 [C8 (Z_to_bv 64 0x218338)] /\ ro_cells asegs m 0x227c58 [C8 (Z_to_bv 64 0x217e08)]
  /\ ro_cells asegs m 0x227e40 [C8 (Z_to_bv 64 0x2188b4)] /\ ro_cells asegs m 0x227c28 [C8 (Z_to_bv 64 0x218670)]
  /\ ro_cells asegs m 0x2d66e3 [C1 (Z_to_bv 8 1)]    (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0x242278 [C8 (Z_to_bv 64 (2 ^ 40))] /\ rw_cells asegs m 0x242280 [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)]
  /\ rw_cells asegs m 0x2c6d22 [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m 0x2d660a [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x225d18 [C8 (Z_to_bv 64 0x2422b8)] /\ rw_cells asegs m (0x2422b8 + 44) [C4 (Z_to_bv 64 4096)]
  /\ rw_cells asegs m (0x2422b8 + 52) [C4 (Z_to_bv 64 190)] /\ rw_cells asegs m (0x2422b8 + 85) [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m (0x777e98 + 32) [C4 (Z_to_bv 64 0)] /\ rw_cells asegs m 0x226998 [C8 (Z_to_bv 64 32)]
  /\ rw_cells asegs m 0x2d6580 [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m 0x24431c [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m (l_TCX L + 8) [C4 (Z_to_bv 64 0)]
  /\ stk asegs m (l_T L + 2768) (l_T L + 3168)
  (* [comment removed for export] *)
  /\ rw_cells asegs m (l_T L) [C8 (Z_to_bv 64 (l_TCX L))]
  (* [comment removed for export] *)
  /\ rw_cells asegs m (g_MFHooks + 8) [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m i_q_max [C8 (Z_to_bv 64 0x10000000); C8 (Z_to_bv 64 0xE666661); C8 (Z_to_bv 64 0x100000)]
  /\ rw_cells asegs m (g_asan_flags + 48) [C4 (Z_to_bv 64 0)]
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0x225d60 [C8 (Z_to_bv 64 1)] /\ rw_cells asegs m 0x2d66c3 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x2d66dc [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m 0x226b70 [C8 (Z_to_bv 64 0x797ed8)]
  /\ rw_cells asegs m 0x798158 [C8 (Z_to_bv 64 4096)]
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ ro_cells asegs m 0x227c38 [C8 (Z_to_bv 64 0x218430)]    (* [comment removed for export] *)
  /\ ro_cells asegs m 0x227cb0 [C8 (Z_to_bv 64 0x216d80)]    (* [comment removed for export] *)
  /\ ro_cells asegs m 0x227cb8 [C8 (Z_to_bv 64 0x2132c4)]    (* [comment removed for export] *)
  /\ ro_cells asegs m 0x2d66e5 [C1 (Z_to_bv 8 1)]    (* [comment removed for export] *)
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
  fs_const FSB m /\ fs_cls_rep FSB 0 (fs0 Σ) m /\ fs_cls_rep FSB 1 (fs2 Σ) m /\ (fs_cls_rep FSB 6 (fs4 Σ) m /\ fs_cls_rep FSB 2 (fs1 Σ) m /\ fs_cls_rep FSB 3 (fc3 Σ) m /\ fs_cls_rep FSB 4 (fc4 Σ) m /\ fs_cls_rep FSB 7 (fc7 Σ) m)
  /\ rw_cells asegs m tpA [C8 (Z_to_bv 64 FSB)]
  /\ (exists dtvbeg, 0 < dtvbeg < 2 ^ 64 /\ tga_cells (l_DTV L) dtvbeg m)
  /\ (exists tb te, ttls_cells (l_T L) m tb te)
  /\ fs_busy L (frames Σ) m.

(* [comment removed for export] *)
Definition ia_rep (Σ : rtsA) (m : mem) : Prop := exists b, ia_state b m.

(* [comment removed for export] *)
Definition CS_W : list (Z * Z) :=
  [(0x22a3b0, 0x22a5e4); (0x22a600, 0x22a608); (0x22a620, 0x22a624); (0x22a640, 0x22a644); (0x22a660, 0x22a668); (0x22a680, 0x22a688); (0x22a6a0, 0x22a6b0); (0x22a6c0, 0x22a6c8); (0x22a6e0, 0x22a6e4); (0x22a700, 0x22a704); (0x22a720, 0x22a724); (0x22a740, 0x241458);
   (* [comment removed for export] *)
   (0x767110, 0x777110);
   (0x777110, 0x777164); (0x777180, 0x777184); (0x7771a0, 0x777e40); (0x777e48, 0x777e90); (0x777ea0, 0x777eb0); (0x777ec0, 0x777ec8); (0x777ed8, 0x798158); (0x798160, 0x799240); (0x799248, 0x799778)].
(* [comment removed for export] *)
Definition CS_ACC : list (Z * Z) :=
  [(0x22a3b0, 0x22a5e4); (0x22a600, 0x22a608); (0x22a620, 0x22a624); (0x22a640, 0x22a644); (0x22a660, 0x22a668); (0x22a680, 0x22a688); (0x22a6a0, 0x22a6b0); (0x22a6c0, 0x22a6c8); (0x22a6e0, 0x22a6e4); (0x22a700, 0x22a704); (0x22a720, 0x22a724); (0x22a740, 0x22aa90); (0x2413d0, 0x241458);
   (* [comment removed for export] *)
   (0x767110, 0x777110);
   (0x777110, 0x777164); (0x777180, 0x777184); (0x7771a0, 0x777e40); (0x777e48, 0x777e90); (0x777ea0, 0x777eb0); (0x777ec0, 0x777ec8); (0x777ed8, 0x798158); (0x798160, 0x799240); (0x799248, 0x799778);
   (0x35b00, 0x35b0e);
   (0x35b20, 0x35b2a);
   (0x35b40, 0x35b50);
   (0x35b60, 0x35b7d);
   (0x35c60, 0x35c87);
   (0x35cc0, 0x35cd0);
   (0x35ce0, 0x35cf2);
   (0x35d20, 0x35d33);
   (0x35dc0, 0x35dcc);
   (0x35de0, 0x35df8);
   (0x35fc0, 0x35fcb);
   (0x36240, 0x36250);
   (0x36260, 0x3626c);
   (0x362e0, 0x362ed);
   (0x36340, 0x3634c);
   (0x363a0, 0x363b1);
   (0x36480, 0x3648a);
   (0x366e0, 0x366ef);
   (0x36700, 0x36716);
   (0x36780, 0x3678b);
   (0x36a20, 0x36a30);
   (0x36d00, 0x36d0e);
   (0x37bc0, 0x37bcf);
   (0x37be0, 0x37bf3);
   (0x37c20, 0x37c2f);
   (0x37c40, 0x37c51);
   (0x37c80, 0x37c97);
   (0x37fe0, 0x37ff6);
   (0x38020, 0x3802f);
   (0x38440, 0x38451);
   (0x385c0, 0x385cf);
   (0x385e0, 0x385fd);
   (0x38620, 0x3862b);
   (0x38640, 0x3864e);
   (0x38720, 0x38731);
   (0x38820, 0x38836);
   (0x38860, 0x38874);
   (0x388a0, 0x388c5);
   (0x3a280, 0x3a293);
   (0x3a2c0, 0x3a2c8);
   (0x3a2e0, 0x3a2f0);
   (0x3f4a0, 0x3f4ad);
   (0x3f4c0, 0x3f4d1);
   (0x3f6e0, 0x3f6f9);
   (0x3f780, 0x3f792);
   (0x3f7c0, 0x3f7ce);
   (0x3f7e0, 0x3f7ef);
   (0x3f800, 0x3f80f);
   (0x3f820, 0x3f830);
   (0x3f840, 0x3f856);
   (0x3f900, 0x3f90e);
   (0x3f920, 0x3f932);
   (0x3f960, 0x3f979);
   (0x30b00, 0x30b11);
   (0x35d60, 0x35d8f);
   (0x35e20, 0x35e50);
   (0x35e80, 0x35eb4);
   (0x35ee0, 0x35f15);
   (0x35f60, 0x35f85);
   (0x37b60, 0x37b85);
   (0x36d20, 0x36d3b);
   (0x37cc0, 0x37ce5);
   (0x37d20, 0x37d4f);
   (0x37d80, 0x37dae);
   (0x37de0, 0x37dff);
   (0x37e20, 0x37e53);
   (0x37e80, 0x37eb8);
   (0x37ee0, 0x37f1a);
   (0x37f40, 0x37f8d);
   (0x3f720, 0x3f743);
   (0x3f880, 0x3f8d4);
   (0x36d60, 0x36de4);
   (0x34400, 0x34415);
   (0x34440, 0x3444b);
   (0x34460, 0x34485);
   (0x344c0, 0x344cc);
   (0x344e0, 0x344f1);
   (0x34520, 0x34531);
   (0x34560, 0x3456b);
   (0x34580, 0x34590);
   (0x345a0, 0x345ae);
   (0x345c0, 0x345d1);
   (0x34760, 0x3476d);
   (0x34780, 0x3478b);
   (0x347a0, 0x347b0);
   (0x347c0, 0x347e1);
   (0x34820, 0x3482f);
   (0x34840, 0x34853);
   (0x34880, 0x34895);
   (0x34a40, 0x34a65);
   (0x34b00, 0x34b13);
   (0x34b40, 0x34b4b);
   (0x34c80, 0x34c8c);
   (0x35ba0, 0x35bb1);
   (0x35be0, 0x35bf2);
   (0x36080, 0x36091);
   (0x36520, 0x36532);
   (0x36ac0, 0x36ad1);
   (0x36ee0, 0x36eee);
   (0x36f20, 0x36f34);
   (0x36f60, 0x36f77);
   (0x37180, 0x37190);
   (0x37260, 0x37271);
   (0x372a0, 0x372b2);
   (0x372e0, 0x372f1);
   (0x37320, 0x37331);
   (0x37360, 0x37378);
   (0x373a0, 0x373b4);
   (0x373e0, 0x373f5);
   (0x37420, 0x37433);
   (0x37460, 0x37470);
   (0x37480, 0x3748d);
   (0x374a0, 0x374b1);
   (0x374e0, 0x374f3);
   (0x37520, 0x3752f);
   (0x37540, 0x37567);
   (0x3a5c0, 0x3a5d1);
   (0x3a600, 0x3a60c);
   (0x3a620, 0x3a631);
   (0x3a660, 0x3a67f);
   (0x35c20, 0x35c38);
   (0x36400, 0x3640a);
   (0x36420, 0x36431);
   (0x35fe0, 0x35fe8);
   (0x360c0, 0x360d0);
   (0x36120, 0x3612f);
   (0x36140, 0x3614f);
   (0x37b20, 0x37b2c);
   (0x37b40, 0x37b4d);
   (0x37fc0, 0x37fd0);
   (0x3a780, 0x3a804);
   (0x3a840, 0x3a8c4);
   (0x11697, 0x116a1);
   (0x1848b, 0x1848f);
   (0x1a2c0, 0x1a340);
   (0x21cd0, 0x21cf1);
   (0x29ec6, 0x29edb);
   (0x29edb, 0x29ef2);
   (0x2df40, 0x2dfc0);
   (0x302b3, 0x302ba);
   (0x30a78, 0x30a88);
   (0x767100, 0x767110);
   (* [comment removed for export] *)
   (0x30dc0, 0x30de0);
   (0x30e00, 0x30e0a);
   (0x30e20, 0x30e2e);
   (0x30e40, 0x30e51);
   (0x30e80, 0x30e8b);
   (0x30ea0, 0x30eb0);
   (0x30ec0, 0x30ed2);
   (0x30f00, 0x30f0e);
   (0x31080, 0x31091);
   (0x310c0, 0x310cb);
   (0x310e0, 0x310f5);
   (0x31120, 0x31132);
   (0x312a0, 0x312b7);
   (0x312e0, 0x312eb);
   (0x31300, 0x31311);
   (0x32dc0, 0x32dd3);
   (0x32e00, 0x32e0d);
   (0x32f60, 0x32f85);
   (0x32fc0, 0x32fce);
   (0x32fe0, 0x32fef);
   (0x33000, 0x33010);
   (0x33020, 0x33033);
   (0x33060, 0x33071);
   (0x330a0, 0x330b1);
   (0x330e0, 0x330ef);
   (0x33100, 0x33110);
   (0x33120, 0x33130);
   (0x332c0, 0x332d2);
   (0x33300, 0x33310);
   (0x33320, 0x33337);
   (0x334e0, 0x334f2);
   (0x33520, 0x33545);
   (0x33580, 0x3359b);
   (0x35f40, 0x35f49);
   (0x36000, 0x3601c);
   (0x36040, 0x36053);
   (0x360e0, 0x360ff);
   (0x36280, 0x3628c);
   (0x362a0, 0x362b3);
   (0x36300, 0x3630d);
   (0x36320, 0x3632f);
   (0x36360, 0x3636c);
   (0x36380, 0x3638f);
   (0x363e0, 0x363ea);
   (0x36460, 0x3646b);
   (0x36560, 0x36573);
   (0x365a0, 0x365b6);
   (0x36620, 0x36633);
   (0x366c0, 0x366cf);
   (0x36b00, 0x36b0c);
   (0x36b20, 0x36b2a);
   (0x36b40, 0x36b5a);
   (0x36f00, 0x36f0d);
   (0x36fa0, 0x36fb0);
   (0x36fc0, 0x36fd7);
   (0x37000, 0x37019);
   (0x37040, 0x37052);
   (0x37080, 0x37093);
   (0x37ae0, 0x37af2);
   (0x38080, 0x38090);
   (0x3a100, 0x3a10e);
   (0x3a120, 0x3a132);
   (0x3a160, 0x3a166);
   (0x3a180, 0x3a192);
   (0x3a1c0, 0x3a1da);
   (0x3a200, 0x3a218);
   (0x3a300, 0x3a313);
   (0x3a340, 0x3a34f);
   (0x3a360, 0x3a37e);
   (0x3a900, 0x3a922);
   (0x3a960, 0x3a976);
   (0x3a9a0, 0x3a9b6);
   (0x3c920, 0x3c931);
   (0x3c960, 0x3c96e);
   (0x3c980, 0x3c997);
   (0x3c9c0, 0x3c9cd);
   (0x3c9e0, 0x3ca00);
   (0x3ca20, 0x3ca2e);
   (0x3ca40, 0x3ca4c);
   (0x3ca60, 0x3ca72);
   (0x3caa0, 0x3cac0);
   (0x3cae0, 0x3caea);
   (0x3cb00, 0x3cb10);
   (0x3cb20, 0x3cb2a);
   (0x40000, 0x40019);
   (0x40040, 0x4004a);
   (0x40060, 0x40069);
   (0x40080, 0x40087);
   (0x40100, 0x4010e);
   (0x40140, 0x40151);
   (0x40180, 0x40190);
   (0x401a0, 0x401af);
   (0x401e0, 0x401f9);
   (0x40360, 0x40384);
   (0x403c0, 0x403d5);
   (0x40400, 0x40419);
   (0x40440, 0x40452);
   (0x40480, 0x40492);
   (0x404c0, 0x404d6);
   (0x40500, 0x40521);
   (0x405a0, 0x405b4);
   (0x405e0, 0x405f3);
   (0x406e0, 0x406f6);
   (0x40720, 0x40732);
   (0x40760, 0x4076e);
   (0x40780, 0x4078e);
   (0x40820, 0x40833);
   (0x40860, 0x4086a);
   (0x40880, 0x408a5);
   (0x408e0, 0x408eb);
   (0x40900, 0x40910);
   (0x40920, 0x40939);
   (0x40960, 0x4096f);
   (0x40980, 0x40999);
   (0x409c0, 0x409cd);
   (0x409e0, 0x409f5);
   (0x40a20, 0x40a2e);
   (0x40a40, 0x40a52);
   (0x40a80, 0x40a93);
   (0x40ac0, 0x40ad2);
   (0x40b00, 0x40b11);
   (0x40b40, 0x40b51);
   (0x40b80, 0x40b91);
   (0x40bc0, 0x40bd6);
   (0x40c00, 0x40c16);
   (0x40c40, 0x40c4e);
   (0x40c60, 0x40c71);
   (0x40ca0, 0x40cad);
   (0x40cc0, 0x40cd2);
   (0x40d00, 0x40d17);
   (0x40d40, 0x40d58);
   (0x40d80, 0x40d94);
   (0x40dc0, 0x40dd3);
   (0x40e00, 0x40e12);
   (0x40e40, 0x40e53);
   (0x40e80, 0x40e8d);
   (0x40ea0, 0x40ee7);
   (0x41200, 0x41211);
   (0x41280, 0x41295);
   (0x412c0, 0x412c2);
   (0x412e0, 0x412f3);
   (0x41320, 0x41324);
   (0x41340, 0x41346);
   (0x41360, 0x41363);
   (0x41380, 0x4139c);
   (0x413c0, 0x413d5);
   (0x41440, 0x4144f);
   (0x41460, 0x41474);
   (0x414a0, 0x414b4);
   (0x414e0, 0x4150e);
   (0x41540, 0x41574);
   (0x415a0, 0x415c8);
   (0x41600, 0x4161a);
   (0x41640, 0x41660);
   (0x41680, 0x4169f);
   (0x416c0, 0x416d9);
   (0x41700, 0x4172a);
   (0x417a0, 0x417b6);
   (0x417e0, 0x417ee);
   (0x41800, 0x4180d);
   (0x41820, 0x41831);
   (0x41860, 0x4187b);
   (0x418a0, 0x418b4);
   (0x418e0, 0x418f9);
   (0x41920, 0x41954);
   (0x41980, 0x41995);
   (0x419c0, 0x419d0);
   (0x419e0, 0x419ff);
   (0x45f40, 0x45f5c);
   (0x45f80, 0x45f91);
   (0x45fc0, 0x45ffa);
   (0x46020, 0x4604e);
   (0x46080, 0x460bb);
   (0x460e0, 0x46111);
   (0x46140, 0x4617d);
   (0x461a0, 0x461c3);
   (0x46200, 0x4621e);
   (0x46240, 0x46254);
   (0x46280, 0x46293);
   (0x462c0, 0x462f6);
   (0x46320, 0x46342);
   (0x46380, 0x463ad);
   (0x463e0, 0x463f6);
   (0x46420, 0x4643c);
   (0x46460, 0x46475);
   (0x464a0, 0x464bb);
   (0x464e0, 0x464f2);
   (0x46520, 0x46530);
   (0x46540, 0x4654c);
   (0x46560, 0x4656d);
   (0x46580, 0x46586);
   (0x465a0, 0x465b8);
   (0x465e0, 0x465fa);
   (0x46620, 0x4663b);
   (0x46660, 0x4668a);
   (0x466c0, 0x466df);
   (0x46700, 0x4671f);
   (0x46740, 0x4675f);
   (0x46780, 0x4679f);
   (0x467c0, 0x467c5);
   (0x41400, 0x41414)].
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
ltac2:(KReplay.run1 (kr_t_RT_rep ()) [] "p'0h02Evh11bi001bh21ph31lh42Ebh52IHh61ah71ep;1p;2p;3p;6p;5p-1R0p10000p4p710p8P0p1000Gp4p710p8P0g000hR1p4p710p8P0P1p4p7210p8p1001Ep4p70p1002?p4p710p8g003<j17Tg003aj1BTg004?j1=Tg004bj2<Tg005Bj1ATP1j35Tg005bj31Tg006=j30Tg006Wj1;Tg0077j29Tg007Qj34Tg0081R1j18Tg008jj66Tg009Hj5@Tg009jj2:Tg00:cj3>Tg00;Pj1?Tf2R0f1R2f0R33>#?p=3A1213p=2g00;n#7#7#7#7#7#7#BR1#=R4/<4R5#AR6P5A5443R7=310X25R8=153,251253R99158506X36A3172X25%;5,25515,96f3R89317X25R:=153,25A15:9506A5440=318g00<SR:19:3R9A5448f4R;531=0:3P:f5R<9544f6R=531=0:3P:P6P2f8R>9317X25R?=15<R@945=P@n0100000020000,25P:P6%8=R@125<RA945=PAn0100000020000915?506]4P2A544;=31<R?g00=3RA50:%8<R<P:P9A0:@3R@P:%8>RB=0:3RCf9RDf;9317X25RE=15>RF545,25P:P6P2125>RG945DPGn0100000020000915ERH506]0P2f7RI#8RJ=0:ARKP:PAP:P6%8D125FRF945DRLPFn0100000020000P:P6P3A15EGRG945DREPGn0100000020000RM506X1:P:PAP:P6P3PLPFn0100000020000RL=06EX1:P6f:9317X25RA125IRN515ROA45D3=06EX36A45>O,96A15AIRI,25REP=E6PBP3E6A544>=31DRDP8E6A45>I,25RIA45>N915ARA506eW0g00=SRN90:JRJP:PNA06LGX1:P6POA063GX36196OPEP=E6R=PBP3E6A06IOeW0n0110001020101P3O1b0b1W4A0:?NP<P:P9P@P:A06FH^0CP2P:PNA06FMX1:P=PDP8E6A06EAeX0KP=A06EOeX0Jn0110001020101P3O1b0b1W4n0110001020101P3O1b4b1A317;X25R;A4502R0515,251250915;506eW5X36X75P2D@1:23,251252/:3506eX64W3o"). Qed.

Lemma perm_filter' : forall {T : Type} (f : T -> bool) (l l' : list T), Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
ltac2:(KReplay.run1 (kr_t_RT_rep ()) [] "p'0h01lh11bi001bh22l'h31Hh41xh52H1h62H2h72IHh83IH1h93IH2h:1Th;1fh<3l''h=1yp;1p;3p;5p;4p;2p;6p;9p200R0g00>3R1p4p710p8P0g005bR2p4p710p8g005Bj13TP1j30TP2j32Tg00>^j15Tg006Wj1:Tg007Qj31Tg00?Ij59Tg00@4j46Tg00@_j24Tg00AMj67Tg00B<l98Tf0R2g00<SR1[f1R3#3f2R4#3f3R5?032f4R6%36R7f5R8#3R9f6R:A2:83A2:8230W2W0%56%:69265R;=06;e%3:R;f7R<?032f8R=A2=<4R>A2=<330P=P6O1P1P1f;R?P1f<#3R@P2f:RA=2?8RB91?:PBn0100000020000P1P@P2A2?A6R@91?:P@n010000002000030P2PAP8f9RC=2A6RDA2AC5REP3D9P3n0110000020000b1A1C6592C=A1C6492C=50CeW7W3W2X09X46P:P4O1P1P1P1%3ARFP=P5O1RGP1PFP2A2C=4RH91C6RIPHn0100000020000RJ91C5PJn0100000020000P1PFP2P1PFPGA1C5HRGPHn0100000020000RF91C6PFn010000002000050CP2P<P4O1RFP1P1P1%3?RJP2A1A8ERK91A6PKn0100000020000P1PJP2A1A6EPEn0100000020000RJ91A850AP2PCP6P5PHC6A1C5IA1C6G50Ce14CIA0CIIen0110000020000b1PFP1P1A0AJJP214CGA0CGGe14CHA0CHHen0110000020000b1n0110000020000b1A1<4291<392<:A1<3291<492<:50<eX0;X=8X46A0<43A2=<5=0=>A0C54A0ADEP?A2?A:RAPBP@P4P2E7A0?A@eW9W6W8W5X<;X29X07P4P3P2M98W3W2W0W;X:0o"). Qed.

Lemma perm_map_remove : forall (l l' : list (word * word)) (a : word), Permutation l l' -> Permutation (map_remove l a) (map_remove l' a).
Proof.
ltac2:(KReplay.run1 (kr_t_RT_rep ()) [] "h01Hh11ah21lh32l'h41pp;1p;2p;3p;5g003<j10Tg003aj1:Tg004?j14Tg004bj23Tg005Bj19Tg00>3j32Tg000hj38Tg00:cj35Tg00;Pj16Tg00Bij57Tg009jj21Tg00;n#0#0#0#0#0#0#:R0#4R1/31R2#9R3f2R4f1R5522P2f0R69811=504#6X42f3R0P4P6D711051145522eW0X11X33W2o"). Qed.

Lemma filter_cons_pos : forall (e : word * word) (l : list (word * word)), 0 < bv_unsigned (snd e) -> List.filter vpos (e :: l) = e :: List.filter vpos l.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_rep ()) [] "h01eh11Hh21bh31lp;1p;2p;3p;4p;6g003<j10Tg003aj1@Tg004?j19Tg004bj28Tg005Bj1?Tg00Chj35Tg00DEj24Tg00Doj27Tg00EKj26Tg005bj32Tg007Qj33Tg006=j31Tg0077j2:Tg00Ehj2>Tg00FHj4=Tg008jj6<Tg0081R0j1;Tg00;n#0#0#0#0#0#0#@R1#9R2/82R3%?3R4g00FcR5f1R69522,41'7g00<SR7g00=3R8P7P4f0R9f3R:A5229,41,65X03R;f2R<523R=533R>P=n0100000020000=14>X27A23;6933<,:4A522<,41R;,65R>A17>8A522:,41R1,75[175;1651=178[1>5;P9C=E<P7P4%;<A2306R7933<R9P7n0100000020000=149eA33<69230=149eW1W3W0o"). Qed.

Lemma filter_vpos_pos : forall (l : list (word * word)), Forall (fun e => 0 < bv_unsigned (snd e)) (List.filter vpos l).
Proof.
ltac2:(KReplay.run1 (kr_t_RT_rep ()) [] "h01lh11Ah22Heh31xh41Hh51Ph61eh71fh81mh91nh:2_Hp;1p;2p;3p;4g003<j12Tg003aj1BTg004?j1>Tg004bj2<Tg005Bj1:Tg000Gj39Tg00GAj30Tg00GXj3=Tg00Chj37Tg00DEj26Tg00Doj23Tg005bj34Tg00H:R0j25Tg00HUj4ATg0081R1j18Tg00EKj2;Tg00Ehj2@Tg006=j3?Tg00<SR2f0R3g00=33?p=1g00;n#2#2#2#2#2#2#BR4#>R5/<5R6#:g00I3p4p710R7p-0\3R8f1R9#:R:P0f2R;?993f3R<f4R=?03;P=P9O1[]3R>[A0<39P<P9O1[^3;A9<;9[R?A9=<;\>A=;93P3n2001000000120000000W0W5W1P?^0:^58^17P3P6g00FcR7A7553,64'3X66A4619A461;9063g00IPp4p710R8P2\3R2%:;R:P0A4<;390<9A0=;9P<P;O1#1'5[R?A0<93P;P9O1#1'5A4=<990=;R>[f5R@?0<;P=P<O1#1'5\>P<P;P9P3CAP9n2001000000120000000W0X39W7W1P?^0:^39^72^18P3P6P1P;P=P9O5A06;=%8;#1'5P0A06<@%8<#1A755=,64,37P3f7906@f6#8#1g00IlR@P01;93#113;9[R013931;;9#1R=[13<;\=1@93P9n2001000000120000000X8@W9P0^8@^9@P3P7f89755,64R4P9O31374P3b2b4W2W:P9P3O2n2001000000120000000b2b4W2X66O4b4W0o"). Qed.

Lemma filter_vpos_id : forall (l : list (word * word)), Forall (fun e => 0 < bv_unsigned (snd e)) l -> List.filter vpos l = l.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_rep ()) [] "h01lh11eh21Hh32Heh42IHh52_Hp;1p;2p;3p;6p;7g003<j10Tg003aj1@Tg004?j1<Tg004bj2;Tg005Bj1?Tg00Chj38Tg00DEj27Tg00Doj25Tg000Gj36Tg005bj31Tg006=j33Tg006Wj1:Tg0077j24Tg007Qj32Tg008jj69Tg00JJj3>Tg00KLj7=Tg00;n#0#0#0#0#0#0#@R0#<R1/;1R2#?R3g00FcR4f0R59811,70'5X12R6=625P2P6g0081R7=125=335X03%:2,43f1R89811,70,54A6268f2R69127=336P3f4R4f3R09127R1522f5R9=224R:9335X03P3P0A2295=33:X03A2240R:,43P1P5E9A127:A>406E9W4W5W3X03X12P8P5F=W2W0o"). Qed.

(* [comment removed for export] *)
Lemma covered_filter_vpos : forall (l : list (word * word)) (z : Z), BackingAlgebra.covered (List.filter vpos l) z = BackingAlgebra.covered l z.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_rep ()) [] "p'0h02E2h11ch21bi001bh32E1h42Evh51mh61nh71xh81Hh94__p1h:4__x1h;1lh<1yh=2Hah>7__arithh?4__ffh@6__sat1hA8__varmaphB5__withC4__x2hD1zhE2HrhF3Hr0hG2IHhH6__sat0hI1ep&0p;1p;2p;3p;6p;4p;<p;7p;5p;Bp;8g003<j1ATg003ak100Tg004?j1hTg004bj2`Tg005Bj1WTg005bj3HTg00Koj21Tg006Wj1PTg0077j22Tg0081R0j1GTg007Qj3CTg00M0j2BTg00IPj37Tg00Moj2FTg008jj6STg00EKj24Tg00NLj28Tg00Nhj2jTg00Chj3@Tg00DEj2<Tg00OHj2eTg00P;j1cTg00DoR1j23Tg00H:R2j2ITg00Pdj1RTg00QBR3j1QTg00Q`R4j2KTg006=j3:Tg00R=j3_Tg00Rcj1^Tg00SAj4]Tg00Sdl<ZTg00TIj6YTg00U2j4XTg00UYj2~Tg00VAj3}Tg00Vej2|Tg00WFj2UTg00Wdj1{Tg00XBj1zTg00Xmj2uTg00YPj2OTg00Z3j7qTg00ZWj1pTg00[9j4NTg00[dj2oTg00\Fj2nTg00]2j3lTg00]Qj4kTg00^Cj26Tg00^`j2MTg00_=j2>Tg00_[j2iTg00Ehj2mTg00`;j1gTg00`Yj4VTg00a7j1fTg00a\j3rTg00b?j6sTg009Hj5dTg00b[l<vTg00c@lBwTg00cfj7bTg00dJj6xTg00dnj8yTg000hj3aTg00<SR5f1R6f0R73:p=0g00=3R89:57p=9g00=SR99:57p=Dg00FcR:/87p==g00eRR;g00IlR<P<P<P3P3f5R3f4R=f3R>f2R?P6P7M<vp=\P<P<P<P<P<P<P4P7P6P?P4P>P=P3f6R4f7R@f8RAf9RBMBwp=[P<P6g00f0P7CNp=LP6g00fWRCg00g6RDPDg00gVREP7g00h6Fbp=EP6PCPDPDPEP7Exp=TP>PCPDPDPEP?P6P7Gyp=JAa?67,<>p=51>?6/F79:5>p=;1M7:p=?1F679:5?p=tg00;nRF#ARG#ARH#A#A#A#ARI$00RJ#hRK/`KRL#WRMPLAHL07RN/161176'0X;M%PL/17,2511N?117?'0%G?P51257RN%G>/07P5%G3/07P5PMP6AHL03RO9CL4POn0100000020000/1@ACL43/1@'0]4P6%G=RO#9P51B7@X1LRP=7L=RQ1B4@RR/F71B7AX1L=7L3,FRRR'0X251B34/FQ,25AHL0=RS97LPRTP>ESACL3SRU97LPACL3=R397LPRP'0e11U41134R3'0eW4%DOP5PQ107RX25P21467RR#D186?RQ[RO187614?6RU#DRV[18?>\V1j67P6n2001000000120000000X<<X7<PO^<<^7<P7P:A@KK4,<JROP6O318O:A@KK@RO,eJ1<JORO#=%cJ,3O'IA@KKA,<JRO#=RV%RGRG%QJRW'KRX,3ORY'I%RIRI,KGRZ,3O,IVR[PVPYPVP7X7<RYPIO1R\,KGR],3Op-0R^/2VA:^VVe9_VVP<P<P1PYP11367R1#^X<<X7<POPO12<OPXP]PYPYPYP<P<g00hV1K67C],2<X5<X6<PGPG12<GPWP\PYPY%Q7,2<X7;PJPI12<IE\M:[M<ZEYP7CXP[1~GI13:GR[%=I13:Z[R;[%=GRYg00i:R\A}GI6UW=%=Z\\^=YP6g00iV1|:G'2P[eO1P;g00j<R;#PR[%W;R;1U<6RG%{<RY%z<R\P\PCPDPDPE1u<:RC1O<FRI'L,E\1T\>Fq%pDRDP\1LIC,E\PDP<PCg00jhPICN,E\CJCJ1o\EREP7P?12581n7?#9dAl<:6CkRIb?bAbBX:<X9^%=7/I6186:A:<:?[[^:<^9^P7f=RW9@KK,<JR]/3ZP]P=P4O4b>b@bHb@bFA:<:OP<P:PJPKPKP7C5R:f<RO'6A@KK7,<J,M:R],4O'>X1L=7LBRZPJPKPKf:RXC5RVf;R_'6R`1MV7,4_PZC;XD<PJPKPKPBC5/6XP5PN10`7P5PJPKPKPOC5R`/6W/07f?RZ,6:14Z]'>X1L=7LORVP6f>RaPJPKPKPWC5#?'4RbPVC;]3P6PJPKPKP_C5/6ORO#9%?`,4WRWP5PN10b7RbP5f@R`PJPKPKPZC5#?'4/07R_fBRV,6:14V]'>X1L=7LZRcP8P6PcC;]0P6PJPKPKPaC5#?,4ZRZ#9RdP21667#918?6[Re186716?6#9Rf[18>?\f1i67P6n2001000000120000000X5<X6<Pe^5<^6<P7PJPKPKP`C5R`fAReP=O318`eP2%9R13?6[RR%9URU\113>?\U1m67P6n2001000000120000000X5<X6<PR^5<^6<P7fCRRPJPKPKPVC5#?RVP>O313RVP[P;P<P<1U<?P?%g<CVP?PGCVPYP\P<1O<HRHg00kO%fF,O<RF=r<CCN,E\PDP\1LFH,E\PD1T\=CJCJPEPIb?bAbBX:<XC<X9^%?7,36P=\Q[^:<^C<^9^P7fFR^,6:14^]'>X1L=7LR#9fEPJPKPKfDC5P6P>O5b>b0b8b3b816:e14e]'>X1L=7LaRaP8P8PaC;eW0%DZRZ125aRePaP8P9PaC;eW0n0110001020101P7O1b0b2W3%DOPWP5PNPbP5PcP9P6PcC;^0_P6PePaP9P8PaC;eX0dPePaP9P9PaC;eX0Zn0110001020101P7O1b0b2W3n0110001020101P7O1b3b2A@KKB,<JP7Esb81B7XX1L=7L@R@1BAB;t@ebEb4b8PTP>ES10TPe11S4/03eW4n0110000020101P7O1b4b2ACL?6R?9HL0/1>11?>'0eWGX;MXILP6DdXD<W;o"). Qed.

(* [comment removed for export] *)
Lemma vis_premise_filter : forall (l : list (word * word)) (x : Z),
  (forall e, In e (List.filter vpos l) -> ~ (shad (bv_unsigned (fst e)) <= x < shad (bv_unsigned (fst e) + bv_unsigned (snd e)))) ->
  forall e, In e l -> ~ (shad (bv_unsigned (fst e)) <= x < shad (bv_unsigned (fst e) + bv_unsigned (snd e))).
Proof.
ltac2:(KReplay.run1 (kr_t_RT_rep ()) [] "p'0h01xh12Evh24__x1h31yh42H0h52Hah67__arithh74__ffh84__p1h96__sat1h:8__varmaph;5__with<4__x2h=1eh>1zh?1Hh@2HehA2HrhB3Hr0hC6__sat0hD1bi001bhE1lhF1mhG1np;1p;2p;3p;4p;<p;6p;Bp;7p;8g003<j1:Tg003aj1vTg004?j1]Tg004bj2VTg005Bj1MTg005bj3DTg00GAj38Tg000hj3?Tg00DEj22Tg00l6j15Tg00NLj24Tg00Chj37Tg00^`j2=Tg00DoR0j20Tg00H:R1j21Tg00llj1@Tg0081R2j1;Tg0077j23Tg006=j36Tg00HUj4_Tg00mEj4^Tg00FHj4\Tg00EKj2GTg00Nhj2YTg00OHj2XTg00P;j1WTg00Pdj1FTg00QBR3j1JTg00Q`R4j2>Tg00R=j3UTg00Rcj1TTg00SAj4OTg00Sdl<NTg00TIj6RTg00U2j4STg00UYj2uTg00VAj3tTg00Vej2sTg006Wj1rTg00WFj2KTg00Wdj1qTg00XBj1gTg00Xmj2fTg00YPj2ITg00dJj6dTg00ZWj1cTg00[9j4CTg00[dj2bTg00\Fj2eTg00]2j3aTg00]Qj4`Tg00`;j1hTg00`Yj4iTg00m`j6jTg00nDj1kTg008jj6lTg00b?j6mTg00b[l<nTg00c@lB[Tg00cfj7oTg00Z3j7pTg00dnj8ZTg00<SR5f0R6g00=3R736p=Ag00=S9656p=Eg00FcR8/46p=9g00eRR9g00IlR:P:P:P3P3f5R3f4R;f3R<f2R=f1R>P6M<np=PP:P:P:P:P:P:P4P6P>P=P4P<P;P3f6R4f7R?f8R@f9RAMB[p=QP:P>g00f0P6CCp=BP>g00fWRBg00g6RCPCg00gVRDP6g00h6Fop=<P=PBPCPCPDP>P6Fpp=HP<PBPCPCPDP=P>P6GZp=Lg00;nRE#:RF#:#:#:#:#:RG#vRH#]RI/VIRJ#MADJ2=98J6A?II>,2HRK#5/4=A7II>,2H,=K#5,0='1#@[^=JA8J6<%;>P51356%;==656P5%;;RK=656A?II3,2HRL#5/4?A7II3,2HRM,=L#5,0?'1#@]1P>%;<RL#AP3P;ADJ2?98J;A8J3@%;3#A'1[A8J;?RN%AKRK'1ADJ2@98J3[PJP2P;P?C_PNPKP<P6C^C\O2W1%ELP11G>6#E14>=[R1146>RL1G=>#ERK[14=<\K1Y>6P>n2001000000120000000X3:X0:P1^3:^0:P6P8PMP>O314M8A7II4RM,XH12HMRM#9%WH,0M'1A7II?,2HR?#9RM%FFR1%JHRK'>RN,0?R2'1%FGRG,>1R3,0?,1MROPMP2PMP6X0:R2PGO1RP,>1RQ,0?p-0RR/3MA6RMMe9UMMP:P:P0P2P010>6R0#TX3:X0:P?P?13:?PNPQP2P2P2P:P:g00hV1>>6CO,3:XF:XG:P1P113:1PKPPP2P2%J6,3:X09PHPG13:GEPM:QM<NERP6CSPO1u1G1081RO%9G1083[R9[%91R2g00i:RPAt1G>UW5%93\P^52P>g00iV1s81'3POeO1P9g00j<R9#rRO%M9R91K:>%q:R1%g:R21f:8RP1I:ERE'B,<2P2PBPCPCPDP<Ed5H2%cCR<P21BEP,<2P<P:PPg00jhPECC,<2CLCL1b2DRPP6P=13571e6=#AdAa:8>C`R7b7b:b;X2:X8R%96/1>14>8A6:8=[[^2:^8RP6f<97II,2HRR/03PRP;P4O4b6b9bCb9bBA6:8?P:P8A?IIA,2HRA#5R?f;R4'4R;1=A6#5,04'1#@X>:P:A?II@,2HRA%56,04,1;#@X>:POP9P:1K:=P>%h:CiP1P2PBPCPCPD1I:FRF,BE,<2P:PFg00kOPECC,<25H2EjPPP7b7b:b;X2:X<:11L0g00ne[^2:^<:P6P4P?O2b61=A8%kAElA7II@,2HP6Emb4bAb1b4W1n0110000020101P6O1b1bDW@X=JW?X0:WEo"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Proj.
Variables (Σ : rtsA) (m : mem).
Hypothesis HA : ART_A Σ m.
Lemma ART_wf : rt_wf Σ.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_rep ()) ["Proj"] "p;1p;2p;3g00oBj1ATg010<j1@Tg0114j23Tg0121j22Tg012lj2?Tg013hj2;Tg014dj2:Tg015^j24Tg016Yj15Tg017Qj36Tg018Kj27Tg019Dj28Tg01:=j29Tg01;:j1>Tg01<8j3=Tg01=2j3<Tg00H:j21Tf2f1f0'1'1p=0p,2ΣR0#A%@0R1p,1mR2'312021?021;021:021402%50=612170218021912%>0==123030303030p,2HA3<o"). Qed.
Lemma ART_consts : consts_rep (lay Σ) m.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_rep ()) ["Proj"] "p;1p;2p;3g010<j1BTg0114j2ATg0121j23Tg012lj22Tg013hj2@Tg014dj2;Tg015^j2:Tg016Yj14Tg017Qj35Tg018Kj26Tg019Dj27Tg01:=j28Tg01;:j19Tg01<8j3?Tg00H:j20Tg00oBj1<Tg00FHj3=Tg01=2j3>Tf2f1f0'0'0p=1p,2ΣR0#BR1p,1mR2'AR3130212021@021;021:02%40=512160217021812%90=?12'031313131R2%<01032p,2HA3=3>o"). Qed.
Lemma ART_prim : prim_rep Σ m.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_rep ()) ["Proj"] "p;2p;1p;3g0121j2ATg012lj2@Tg013hj23Tg014dj22Tg015^j2?Tg010<j1;Tg016Yj1:Tg017Qj34Tg018Kj25Tg019Dj26Tg01:=j27Tg01;:j18Tg01<8j39Tg00H:j20Tg0114j2>Tg00oBj1<Tg00FHj31Tg01=2j3=Tp,2ΣR0p,1mR1'AR21@01130112011?01%;0R3%:0;41150116011731%80=931'0'0'0'0'0'0'0'0R41>31R31024R4%<01034p,2HA31313=o"). Qed.
Lemma ART_cache : cache_rep Σ m.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_rep ()) ["Proj"] "p;2p;1p;3g012lj2ATg013hj2@Tg014dj23Tg015^j22Tg010<j1?Tg016Yj1:Tg017Qj39Tg018Kj24Tg019Dj25Tg01:=j26Tg01;:j17Tg01<8j38Tg00H:j20Tg0121j2>Tg0114j2<Tg00oBj1;Tg00FHj31Tg01=2j3=Tp,2ΣR0p,1mR1'AR21@0113011201%?0R3%:0;91140115011631%70=831'0'0'0'0'0'0'0R41>01R51024R41<31R31054R4%;01034p,2HA3131313=o"). Qed.
Lemma ART_chunk : chunk_rep Σ m.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_rep ()) ["Proj"] "p;2p;1p;3g013hj2ATg014dj2@Tg015^j23Tg010<j12Tg016Yj1?Tg017Qj3:Tg018Kj28Tg019Dj24Tg01:=j25Tg01;:j16Tg01<8j37Tg00H:j20Tg012lj29Tg0121j2>Tg0114j2<Tg00oBj1;Tg00FHj31Tg01=2j3=Tp,2ΣR0p,1mR1'AR21@011301%20R3%?0;:1180114011531%60=731'0'0'0'0'0'0R41901R51024R41>01R21054R41<31R31024R4%;01034p,2HA313131313=o"). Qed.
Lemma ART_sec : sec_rep Σ m.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_rep ()) ["Proj"] "p;2p;1p;3g014dj2ATg015^j2@Tg010<j13Tg016Yj12Tg017Qj3?Tg018Kj2:Tg019Dj27Tg01:=j24Tg01;:j15Tg01<8j36Tg00H:j20Tg013hj28Tg012lj29Tg0121j2>Tg0114j2<Tg00oBj1;Tg00FHj31Tg01=2j3=Tp,2ΣR0p,1mR1'AR21@01%30R3%20;?11:0117011431%50=631'0'0'0'0'0R41801R51024R41901R21054R41>01R51024R41<31R31054R4%;01034p,2HA31313131313=o"). Qed.
Lemma ART_quar : quar_rep Σ m.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_rep ()) ["Proj"] "p;2p;1p;3g015^j2ATg010<j1@Tg016Yj13Tg017Qj32Tg018Kj2?Tg019Dj2:Tg01:=j26Tg01;:j14Tg01<8j35Tg00H:j20Tg014dj27Tg013hj28Tg012lj29Tg0121j2>Tg0114j2<Tg00oBj1;Tg00FHj31Tg01=2j3=Tp,2ΣR0p,1mR1'AR2%@0R3%30;211?011:011631%40=531'0'0'0'0R41701R51024R41801R21054R41901R51024R41>01R21054R41<31R31024R4%;01034p,2HA3131313131313=o"). Qed.
Lemma ART_dep : dep_rep (lay Σ) (dep Σ) m.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_rep ()) ["Proj"] "p;1p;3p;2g010<j1ATg016Yj1@Tg017Qj33Tg018Kj22Tg019Dj2?Tg01:=j2:Tg01;:j15Tg01<8j34Tg00H:j20Tg015^j26Tg014dj27Tg013hj28Tg012lj29Tg0121j2>Tg0114j2<Tg00oBj1;Tg00FHj31Tg01=2j3=Tp,2ΣR0#AR1%@0p,1mR233R312021?021:12%50=412'0'0'0R41602R51034R41702R31054R41802R51034R41902R31054R41>02R51034R41<12R21054R4%;01024p,2HA313131313131313=o"). Qed.
Lemma ART_fs : fs_rep Σ m.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_rep ()) ["Proj"] "p;2p;1p;3g018Kj2ATg019Dj2@Tg010<j13Tg01:=j22Tg01;:j1?Tg01<8j3:Tg00H:j20Tg016Yj14Tg017Qj35Tg015^j26Tg014dj27Tg013hj28Tg012lj29Tg0121j2>Tg0114j2<Tg00oBj1;Tg00FHj31Tg01=2j3=Tp,2ΣR0p,1mR1'AR21@01%30R3/21%?0=:31'0'0R4%40=531R51024R41601R21054R41701R51024R41801R21054R41901R51024R41>01R21054R41<31R31024R4%;01034p,2HA31313131313131313=o"). Qed.
Lemma ART_ia : ia_rep Σ m.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_rep ()) ["Proj"] "p;2p;1p;3g019Dj2BTg010<j1ATg01:=j24Tg01;:j13Tg01<8j3@Tg00H:j20Tg018Kj2;Tg016Yj15Tg017Qj36Tg015^j27Tg014dj28Tg013hj29Tg012lj2:Tg0121j2?Tg0114j2>Tg00oBj1=Tg00FHj32Tg01=2j3<Tf4f3f2f1f03232p=1p,2ΣR0p,1mR1'BR2%A0R3/41%30=@31'0R41;01R51024R4%50=631R21054R41701R51024R41801R21054R41901R51024R41:01R21054R41?01R51024R41>31R31054R4%=01034p,2HA32D1D1D1D13<o"). Qed.
Lemma ART_shadow : shadow_rep (lay Σ) m.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_rep ()) ["Proj"] "p;1p;2p;3g010<j1BTg01:=j2ATg01;:j14Tg01<8j33Tg019Dj2@Tg00H:j20Tg018Kj2;Tg016Yj15Tg017Qj36Tg015^j27Tg014dj28Tg013hj29Tg012lj2:Tg0121j2?Tg0114j2>Tg00oBj1=Tg01=2j3<Tg00FHj32Tf4f3f2f1f03232p=1p,2ΣR0#BR1p,1mR2'AR3%40=312R41@02R51034R41;02R31054R4%50=612R51034R41702R31054R41802R51034R41902R31054R41:02R51034R41?02R31054R41>12R21034R4%=01024p,2HAD1D1D1D1D13<o"). Qed.
Lemma ART_vis : vis_rep (lay Σ) (rtA_allow Σ) m.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_rep ()) ["Proj"] "p;1p;2p;3g010<j1ATg01:=j2@Tg01;:j14Tg01<8j33Tg019Dj2?Tg00H:j20Tg018Kj2;Tg016Yj15Tg017Qj36Tg015^j27Tg014dj28Tg013hj29Tg012lj2:Tg0121j2>Tg0114j2=Tg00oBj1<Tg00FHj32Tf4f3f2f1f03232p=1p,2ΣR0#AR1p,1mR2'@R3%40=312R41?02R51034R41;02R31054R4%50=612R51034R41702R31054R41802R51034R41902R31054R41:02R51034R41>02R31054R41=12R21034R4%<01024p,2HA32D1D1D1D1D1o"). Qed.
End Proj.

Lemma ART_intro : forall Σ m, rt_wf Σ -> consts_rep (lay Σ) m -> prim_rep Σ m -> cache_rep Σ m -> chunk_rep Σ m ->
  sec_rep Σ m -> quar_rep Σ m -> dep_rep (lay Σ) (dep Σ) m -> fs_rep Σ m -> ia_rep Σ m -> shadow_rep (lay Σ) m ->
  vis_rep (lay Σ) (rtA_allow Σ) m -> ART_A Σ m.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_rep ()) [] "h01mh12Σp;1p;2p;3p;4g003<j11Tg003aj1DTg004?j1;Tg01=Mj1ETg00oBj1CTg010<j12Tg0114j2<Tg0121j2:Tg012lj27Tg013hj26Tg014dj25Tg015^j28Tg016Yj19Tg017Qj3BTg018Kj2ATg019Dj2@Tg01:=j2=Tg01;:j1>Tg01<8j3?Tg00H:j20Tg00mEj44Tg01=oj2FTf6R0f5R1f4R2f3R3f2R4f1R5f0R6C4C4p=3g01>gg00;n#1#1#1R7#1#1#1#D#;%D7#;#E[%C5%24/<51:34172316121501f7R7/80f8R8#2%98;B7f9R9/A8f:R:/@9f;R;#2/=:f<R<#2%><;?;f=R=#C%2=R>/<<R?1:=<R@17=<RA16=<RB15=<RC18=<RD%9==B><RE1A=<RF1@=<RG1=><RH%>==?><R>'0RI'0RJ'0RK'0RL'0RM'0RN'0RO'0RP'0RQ'0P;P?PQP:P@PPP9PAPOP8PBPNP7PCPMP0PDPLP1PEPKP2PFPJP3PGPIP4PHP>P5P6C4F3F3F3F3F31F=<eUUUUUUUUUUUUW0W1o"). Qed.
