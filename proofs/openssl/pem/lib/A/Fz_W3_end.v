(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_pploc Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_aux.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation wz := (Z_to_bv 64) (only parsing).
Definition SITE_end_cfree : Z := 0x30c464.   (* [comment removed for export] *)
Definition SITE_end_pfree : Z := 0x30c478.   (* [comment removed for export] *)
Definition SITE_end_bf1 : Z := 0x30c480.     (* [comment removed for export] *)
Definition SITE_end_bf2 : Z := 0x30c488.     (* [comment removed for export] *)
Definition SITE_end_rel : Z := 0x30c4ec.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ff_shadow_ret : list cell := repeat (C1 (Z_to_bv 8 (-11))) 16.

(* [comment removed for export] *)
Definition end_c_post (sp1 : Z) (ra' : Z) (pc' : Z) (gp s0 s1 a0' a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ms = MS (mkR (wz ra') (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pc') fc None m (seg_rom asegs).

Lemma end_c0_walk : forall ra sp1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => end_c_post sp1 SITE_end_cfree FZ_EVP_CTX_FREE gp s0 s1 s11 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m ms /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_END) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros SP0 SPH MI. unfold J_END, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep.
  unfold end_c_post, SITE_end_cfree, FZ_EVP_CTX_FREE. apply evt_done. split; [| exact I]. do 11 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma end_c1_walk : forall ra sp1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => end_c_post sp1 SITE_end_pfree FZ_PEM_FREE gp s0 s1 s10 s4 (wz 0) (wz 1025) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m ms /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_end_cfree) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros SP0 SPH MI. unfold SITE_end_cfree, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. zstep. zstep.
  unfold end_c_post, SITE_end_pfree, FZ_PEM_FREE. apply evt_done. split; [| exact I]. do 11 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma end_c2_walk : forall ra sp1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => end_c_post sp1 SITE_end_bf1 FZ_BIO_FREE gp s0 s1 s7 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m ms /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_end_pfree) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros SP0 SPH MI. unfold SITE_end_pfree, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep.
  unfold end_c_post, SITE_end_bf1, FZ_BIO_FREE. apply evt_done. split; [| exact I]. do 11 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma end_c3_walk : forall ra sp1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => end_c_post sp1 SITE_end_bf2 FZ_BIO_FREE gp s0 s1 s3 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m ms /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_end_bf1) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros SP0 SPH MI. unfold SITE_end_bf1, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep.
  unfold end_c_post, SITE_end_bf2, FZ_BIO_FREE. apply evt_done. split; [| exact I]. do 11 eexists. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma end_e1_walk : forall ra sp1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (wz 0) s6 s7 s8 s9 (wz 0) (wz 0) t3 t4 t5 t6) F (wz J_END) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_END1) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI. unfold J_END1, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep.
  unfold J_END. apply evt_done. split; [reflexivity| exact I].
Qed.
(* [comment removed for export] *)
Lemma end_rl_walk : forall ra sp1 gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 112) [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13] ->
  evt asegs (fun ms => ms = MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 c3 s3 c7 s5 c6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_END) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_RELOAD) fc None m (seg_rom asegs)).
Proof.
  intros until c13. intros SP0 SPH MI FRE. unfold J_RELOAD, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  zstep. zstep. zstep. zstep.
  unfold J_END. apply evt_done. split; [reflexivity| exact I].
Qed.
(* [comment removed for export] *)
Lemma end_fx_walk : forall ra sp1 gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 112) [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13] ->
  evt asegs (fun ms => ms = MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 c3 c5 s4 (wz 0) c6 c4 s8 s9 s10 (wz 0) t3 t4 t5 t6) F (wz J_END) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_FREE1X) fc None m (seg_rom asegs)).
Proof.
  intros until c13. intros SP0 SPH MI FRE. unfold J_FREE1X, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  unfold J_END. apply evt_done. split; [reflexivity| exact I].
Qed.
(* [comment removed for export] *)
Definition end_r1_post (sp1 : Z) (gp s0 s1 s3 s4 s5 s7 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (f : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (wz f) s3 s4 s5 (wz f) s7 (wz (shad f)) s9 s10 s11 t3 t4 t5 t6)
            F (wz SITE_end_rel) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 8); (shad f, shad f + 16)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' f [C8 (wz FF_MAGIC_RET)] /\ rw_cells asegs m' (shad f) ff_shadow_ret.

Lemma end_r1_walk : forall ra sp1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (f lo : Z) mg (sj : list byte),
  0 < f -> f mod 64 = 0 -> 0xbc6000 <= f -> f + 128 <= lo -> (f + 128 <= 0x7fff8000 \/ 0x10007fff8000 <= f) -> 0x10007fff8000 <= lo -> lo <= sp1 -> sp1 + 368 <= 2 ^ 47 ->
  rw_cells asegs m f [C8 mg] -> rw_cells asegs m (shad f) (ff_shadow sj) -> stk asegs m lo sp1 -> mem_inv asegs m ->
  evt asegs (end_r1_post sp1 gp s0 s1 s3 s4 s5 s7 s9 s10 s11 F fc f m)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (wz f) s3 s4 s5 (wz f) s7 (wz (shad f)) s9 s10 s11 t3 t4 t5 t6)
        F (wz SITE_end_bf2) fc None m (seg_rom asegs)).
Proof.
  intros until sj. intros F0 F64 FIMG FLO FSH HLOS LOSP SPH HDR SB ST MI. unfold SITE_end_bf2, TP_A, shad, SHB, ff_shadow in *.
  pose proof (munch_refl [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 16 <= 0x10007fff8000).
  { pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)). assert (f / 8 + 16 <= 2^44) by (Z.div_mod_to_equations; lia). lia. }
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  pose proof (div8_facts f) as Q1.
  zstep. zstep; lfix. zstep; lfix. zstep; lfix. zstep. zstep. zstep; lfix.
  zstep. if_cases KF; zify_cond KF; [exfalso; lia|].
  zstep. do 16 (zstep; lfix).
  unfold end_r1_post, SITE_end_rel, FF_MAGIC_RET, ff_shadow_ret, shad, SHB. apply evt_done. do 17 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption| cbn [repeat]; assumption].
Qed.

(* [comment removed for export] *)
Definition end_r2_post (usp : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv : word) (F : bvmap 5 word) (fc : bv 32) (fl lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra (wz usp) gp (wz TP_A) t0 t1 t2 s0 s1 rv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(fl, fl + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
    /\ rw_cells asegs m' fl [C1 (Z_to_bv 8 0)].

Lemma end_r2_walk : forall ra0 ra sp1 usp pd gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6
    (s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (F : bvmap 5 word) fc (m : mem) (f fl lo : Z) nj jj,
  (pd = 0 \/ pd = 16) -> sp1 = usp - 352 - pd -> 0x10007fff8000 <= lo -> lo <= sp1 -> usp + 16 <= 2 ^ 47 ->
  0 < f -> f + 128 <= lo -> 0 < fl -> fl + 1 <= lo ->
  stk asegs m lo sp1 -> rw_cells asegs m sp1 [CB nj jj] -> Z.of_nat nj = 248 + pd ->
  rw_cells asegs m (usp + -104) [C8 s11'; C8 s10'; C8 s9'; C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra] ->
  ro_cells asegs m (f + 120) [C8 (wz fl)] -> rw_cells asegs m fl [C1 (Z_to_bv 8 1)] -> mem_inv asegs m ->
  evt asegs (end_r2_post usp ra gp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' s5 F fc fl lo m)
    (MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 (wz usp) (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 (wz f) s3 s4 s5 (wz f) s7 (wz (shad f)) s9 s10 s11 t3 t4 t5 t6)
        F (wz SITE_end_rel) fc None m (seg_rom asegs)).
Proof.
  intros until jj. intros HP ESP1 HLOS LOSP SPH F0 FLO FL0 FLLO ST FRJ NJ SAVED FLG FLB MI. unfold SITE_end_rel, TP_A in *.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EUfl : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  assert (EUu : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep. clear FLG.
  zstep; lfix.
  zstep. zstep. zstep.
  do 13 zstep.
  lazymatch type of FRJ with rw_cells _ ?mx _ _ =>
    assert (FRA : rw_cells asegs mx sp1 ([CB nj jj] ++ [C8 s11'; C8 s10'; C8 s9'; C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra])) end.
  { apply (proj2 (rw_cells_app _ sp1 _ _)). split; [exact FRJ|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, NJ.
    replace (sp1 + (248 + pd)) with (usp + -104) by lia. exact SAVED. }
  clear FRJ SAVED.
  lazymatch goal with H : stk asegs ?mx lo sp1 |- _ => eapply stk_release in FRA; [| exact H| lia]; clear H end.
  cbn [cells_size csize Nat.add app] in FRA. rewrite Nat2Z.inj_add, NJ in FRA.
  replace (sp1 + (248 + pd + Z.of_nat 104)) with usp in FRA by lia.
  zstep. zstep.
  unfold end_r2_post. apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FRA| assumption].
Qed.

(* [comment removed for export] *)
Ltac fix_addr sp1 K := lazymatch goal with |- rw_cells _ _ ?a _ /\ _ => replace a with (sp1 + K) by lia | |- rw_cells _ _ ?a _ => replace a with (sp1 + K) by lia end.

Lemma rw_cells_blur_all' : forall (m : mem) A cs, rw_cells asegs m A cs -> rw_cells asegs m A [CB (cells_size cs) (cells_bytes cs)].
Proof. intros m A cs H. apply (rw_cells_blur m A cs []). rewrite app_nil_r. exact H. Qed.

(* [comment removed for export] *)
Lemma pem_frame_blob : forall RT (en : pem_entry RT) (m : mem) j0 lH lF endv hBv dBv x1 x2 gap,
  pem_frame RT en m j0 lH lF endv hBv dBv x1 x2 gap -> (e_pd RT en = 0 \/ e_pd RT en = 16) ->
  exists nj jj, rw_cells asegs m (e_sp1 RT en) [CB nj jj] /\ Z.of_nat nj = 248 + e_pd RT en.
Proof.
  intros RT en m j0 lH lF endv hBv dBv x1 x2 gap (FR0 & FRH & SZH & FRF & SZF & FR104 & FRE & FR224 & FRG) PD.
  set (sp1 := e_sp1 RT en) in *.
  assert (FRA : rw_cells asegs m sp1 ([CB 24 j0] ++ lH ++ lF ++ [C8 endv] ++ loc_E RT en hBv dBv ++ [C8 x1; C8 x2; C8 (Z_to_bv 64 (e_f RT en))] ++ [CB (Z.to_nat (e_pd RT en)) gap])).
  { apply (proj2 (rw_cells_app _ sp1 _ _)). split; [exact FR0|]. cbn [cells_size csize Nat.add]. fix_addr sp1 24.
    apply (proj2 (rw_cells_app _ _ _ _)). split; [exact FRH|]. rewrite <- (Nat2Z.id (cells_size lH)), SZH. fix_addr sp1 80.
    apply (proj2 (rw_cells_app _ _ _ _)). split; [exact FRF|]. rewrite <- (Nat2Z.id (cells_size lF)), SZF. fix_addr sp1 104.
    apply (proj2 (rw_cells_app _ _ _ _)). split; [exact FR104|]. cbn [cells_size csize Nat.add]. fix_addr sp1 112.
    apply (proj2 (rw_cells_app _ _ _ _)). split; [exact FRE|]. unfold loc_E. cbn [cells_size csize Nat.add]. fix_addr sp1 224.
    apply (proj2 (rw_cells_app _ _ _ _)). split; [exact FR224|]. cbn [cells_size csize Nat.add]. fix_addr sp1 248. exact FRG. }
  apply rw_cells_blur_all' in FRA. do 2 eexists. split; [exact FRA|].
  rewrite ?cells_size_app, ?Nat2Z.inj_add, SZH, SZF. unfold loc_E. cbn [cells_size csize Nat.add]. lia.
Qed.

Section CEnd.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Variable libenv : mem -> list (Z * Z) -> Z -> Prop.
Variable libenv_fp : list (Z * Z) -> Z -> Prop.
Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a -> (in_ranges LIB_W a /\ client_static a /\ ~ cl_cell a) \/ in_live LBL a.
Variable errst_at_rest : Z -> list (Z * Z) -> mem -> Prop.
Variable errst_live : Z -> Z -> Z -> list (Z * Z) -> mem -> Prop.
Variable errst_fp : Z -> list (Z * Z) -> Z -> Prop.
Hypothesis errst_rest_agree : forall m m' E strs, errst_at_rest E strs m -> agree_on (errst_fp E strs) m m' -> errst_at_rest E strs m'.
Hypothesis errst_live_agree : forall m m' E top bot strs, errst_live E top bot strs m -> agree_on (errst_fp E strs) m m' -> errst_live E top bot strs m'.
Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ in_live strs a.
Hypothesis errst_rest_live : forall m E, errst_at_rest E [] m -> errst_live E 0 0 [] m.
Variables FZ_SITES FZ_CALLS : list (Z * Z).
Hypothesis C_CF : evp_ctx_free_stmt RT FZ_SITES FZ_CALLS.
Hypothesis C_CFN : evp_ctx_free_null_stmt RT FZ_SITES FZ_CALLS.
Hypothesis C_PF : pem_free_stmt RT libenv FZ_SITES FZ_CALLS.
Hypothesis C_PFN : pem_free_null_stmt RT libenv FZ_SITES FZ_CALLS.
Hypothesis C_BF : bio_free_mem_stmt RT libenv FZ_SITES FZ_CALLS.
Hypothesis C_BFN : bio_free_null_stmt RT.

Local Notation pem_entry := (pem_entry RT).
Local Notation pem_com := (pem_com RT libenv FZ_SITES FZ_CALLS).
Local Notation pem_err := (pem_err RT errst_at_rest errst_live).
Local Notation pem_frame := (pem_frame RT).
Local Notation pem_post := (pem_post RT libenv errst_live).
Local Notation pem_ms := (pem_ms RT).
Local Notation pem_out := (pem_out).

(* [comment removed for export] *)
Lemma end_retire : forall T (en : pem_entry) Σ m off crem lrem strs news (nj : nat) (jj : list byte) hj lenv j1 tav j2 bmv j3 ret
    (F : bvmap 5 word) (fc : bv 32) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s7 s10 s11 t3 t4 t5 t6 : word) c,
  pem_com en Σ m off crem lrem (strs ++ news) -> pem_err en Σ strs m -> rw_cells asegs m (e_sp1 RT en) [CB nj jj] -> Z.of_nat nj = 248 + e_pd RT en ->
  rw_cells asegs m (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3) ->
  Fz_W3_iface.pem_out ret m (e_PN RT en) (e_PH RT en) (e_PD RT en) (e_PLN RT en) news -> 254 * news_sz news <= 255 * (off - e_boff RT en) + 254 * 512 ->
  (forall c', pem_post en c' -> realizes asegs c' T) ->
  ASTA RT Σ (e_PMc RT en) (eq (pem_ms en SITE_end_bf2 m F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz (e_f RT en)) s3 s4 (wz ret) (wz (e_f RT en)) s7 s10 s11 t3 t4 t5 t6)) c ->
  realizes asegs c T.
Proof.
  intros T en Σ m off crem lrem strs news nj jj hj lenv j1 tav j2 bmv j3 ret F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s7 s10 s11 t3 t4 t5 t6 c
         COM PE FRB NJ FFC PO NB Hk HA.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  pose proof (af_sp0_range RT AF Σ m ART0) as SPR. pose proof (af_sp0_win RT AF Σ m ART0) as SPW.
  assert (INF : In (e_f RT en, 1%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  set (f := e_f RT en) in *. set (usp := e_PL RT en) in *. set (sp1 := e_sp1 RT en) in *.
  assert (ESP1 : sp1 = usp - 352 - e_pd RT en) by reflexivity.
  (* [comment removed for export] *)
  assert (HLO : e_lo RT en <= sp1) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  pose proof (af_frames_range RT AF Σ m f 1%nat ART0 INF) as (_ & FLO' & _ & FLV). change (fs_size 1) with 128 in FLO', FLV.
  assert (FLO : f + 128 <= e_lo RT en) by (clear - FLO' LOW; lia). clear FLO'.
  pose proof (div8_facts f) as Q1.
  assert (SHR : 0x7fff8000 <= shad f /\ shad f + 16 <= 0x10007fff8000).
  { unfold shad, SHB. pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)). assert (f / 8 + 16 <= 2^44) by (clear - FTOP Q1; unfold USTACK_TOP in *; Z.div_mod_to_equations; lia). lia. }
  (* [comment removed for export] *)
  pose proof (rw_cells_head m f _ _ FFC) as HDR.
  pose proof (end_r1_walk xra sp1 (e_gp RT en) t0 t1 t2 (e_sp RT en) (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 (wz ret) s7 (wz SHB) s10 s11 t3 t4 t5 t6 F fc m f (e_lo RT en) _ (e_fsj RT en)
                F0 F64 ltac:(unfold SEGTOP_A in FSEG; exact FSEG) FLO FSH HLOS HLO ltac:(unfold sp1, e_sp1, usp, USTACK_TOP in *; lia) HDR FFS ST MI) as W1.
  cl_lift W1 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (ra1 & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & HDR1 & SB1) & Hc1'). clear Hc1.
  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 sp1 ART0 ltac:(clear - LOW HLO; lia)); [| exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Ha.
    - apply (acl_frame _ _ _ f 1%nat); [exact INF | change (fs_size 1) with 128; lia].
    - apply (acl_fshadow _ _ _ f 1%nat); [exact INF | change (fs_size 1) with (64 * 2); rewrite (shad_add64 f 2 F64); lia]. }
  (* [comment removed for export] *)
  destruct (af_frame_release RT AF Σ m1 f 1%nat (e_frames RT en) ART1 FRS) as (Σ5 & flg & FLC & NAC & FL0 & FLW & FW & REL).
  change (fs_size 1) with 128 in FW. replace (f + 128 - 8) with (f + 120) in FW by lia. rewrite SP0 in FLW.
  (* [comment removed for export] *)
  assert (AG1 : forall A cs, rw_cells asegs m A cs -> (A + Z.of_nat (cells_size cs) <= f \/ f + 8 <= A) -> A + Z.of_nat (cells_size cs) <= 0x7fff8000 \/ 0x10007fff8000 <= A ->
                rw_cells asegs m1 A cs).
  { intros A cs C D1 D2. eapply rw_cells_agree; [exact C| | exact WM1]. intros a Ha. cbv beta in Ha. apply MU1. cbn [outside]. split; [lia|]. split; [| exact I]. clear - Ha D2 SHR. lia. }
  assert (SPLO : 0x10007fff8000 <= sp1) by (clear - HLOS HLO; lia).
  assert (FRA : rw_cells asegs m1 sp1 [CB nj jj]) by (apply (AG1 _ _ FRB); cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, NJ; clear - FLO HLO SPLO PD; lia).
  pose proof (AG1 _ _ SAVED ltac:(unfold pem_saved; cbn [cells_size csize Nat.add]; lia) ltac:(unfold pem_saved; cbn [cells_size csize Nat.add]; lia)) as SAVED1.
  unfold pem_saved in SAVED1.
  assert (ST1 : stk asegs m1 (e_lo RT en) sp1).
  { apply (stk_agree asegs m m1 _ _ ST); [| exact WM1]. intros a Ha. cbv beta in Ha. apply MU1. cbn [outside]. clear - Ha FLO SHR HLOS. lia. }
  assert (TOP47 : usp + 16 <= 2 ^ 47) by (unfold USTACK_TOP in TOP; clear - TOP; lia).
  assert (FLLO : flg + 1 <= e_lo RT en) by (clear - FLW LOW SP0; lia).
  pose proof (end_r2_walk ra1 (e_ra RT en) sp1 usp (e_pd RT en) (e_gp RT en) u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s3 s4 (wz ret) s7 (wz SHB) s10 s11 u3 u4 u5 u6
                (e_s0 RT en) (e_s1 RT en) (e_s2 RT en) (e_s3 RT en) (e_s4 RT en) (e_s5 RT en) (e_s6 RT en) (e_s7 RT en) (e_s8 RT en) (e_s9 RT en) (e_s10 RT en) (e_s11 RT en)
                F fc m1 f flg (e_lo RT en) _ _
                PD ESP1 HLOS HLO TOP47 F0 FLO FL0 FLLO ST1 FRA NJ SAVED1 FW FLC MI1) as W2.
  rewrite <- (Z_to_bv_bv_unsigned (e_sp RT en)) in Hc1'. change (bv_unsigned (e_sp RT en)) with usp in Hc1'.
  cl_lift W2 Hc1' c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & FLC2) & Hc2'). clear Hc2.
  destruct (REL m2 MU2 WM2 FLC2) as (ART2 & FRS2 & LV2 & SP2 & CR2 & AL2 & AM2 & CG2).
  (* [comment removed for export] *)
  assert (A02 : forall a : word, aclient (e_live RT en) (e_frames RT en) usp (bv_unsigned a) -> m2 a = m a).
  { intros a Ha.
    assert (NF : ~ (f <= bv_unsigned a < f + 8) /\ ~ (shad f <= bv_unsigned a < shad f + 16)).
    { split; intros R; [apply (proj1 (proj2 (seg_byte_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem (strs ++ news) (f, f + 8) (bv_unsigned a) COM ltac:(right; right; cbn; lia) ltac:(cbn; exact R))) Ha)|].
      destruct Ha as [H|[H|[H|[H|H]]]].
      - clear - H R SHR HLOS HLO ESP1 PD. lia.
      - pose proof (client_static_range _ H). clear - H0 R SHR. unfold SEGTOP_A in *. lia.
      - destruct H as (p & n & Hin & Hp). destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV _].
        pose proof (proj1 (af_fshadow_apart RT AF Σ m f 1%nat ART0 INF) p n (ELV _ Hin)) as X. change (fs_size 1) with (64 * 2) in X. rewrite (shad_add64 f 2 F64) in X. lia.
      - destruct H as (f' & k' & Hin & Hf). assert (Hin' : In (f', k') (rt_frames RT Σ)) by (rewrite FRS; right; exact Hin).
        pose proof (proj2 (af_fshadow_apart RT AF Σ m f 1%nat ART0 INF) f' k' Hin') as X. change (fs_size 1) with (64 * 2) in X. rewrite (shad_add64 f 2 F64) in X.
        pose proof (Z.shiftl_nonneg 64 (Z.of_nat k')). unfold fs_size in *. lia.
      - destruct H as (f' & k' & Hin & Hf). assert (Hin' : In (f', k') ([] ++ e_frames RT en)) by exact Hin.
        pose proof (af_frames_disj RT AF Σ m f 1%nat f' k' [] _ ART0 FRS Hin') as D. change (fs_size 1) with 128 in D.
        pose proof (Z.shiftl_nonneg 64 (Z.of_nat k')). unfold shad, SHB, fs_size in *. Z.div_mod_to_equations. lia. }
    destruct NF as [NF1 NF2].
    rewrite (MU2 a). 2: { cbn [outside]. split; [| exact I]. intros R.
      assert (Ea : bv_unsigned a = flg) by (clear - R; lia).
      destruct Ha as [H|H]; [clear - H Ea FLW SP0 LOW HLO ESP1 PD; lia|].
      apply NAC. rewrite <- Ea. destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV _].
      destruct H as [H|[H|[H|H]]]; [right; left; exact H
        | right; right; left; destruct H as (p & n & Hin & Hp); exists p, n; split; [exact (ELV _ Hin)| exact Hp]
        | right; right; right; left; destruct H as (f' & k' & Hin & Hf); exists f', k'; split; [rewrite FRS; right; exact Hin| exact Hf]
        | right; right; right; right; destruct H as (f' & k' & Hin & Hf); exists f', k'; split; [rewrite FRS; right; exact Hin| exact Hf]]. }
    apply MU1. cbn [outside]. split; [exact NF1|]. split; [exact NF2| exact I]. }
  apply Hk. unfold Fz_W3_defs.pem_post. exists Σ5.
  split; [| split; [exact FRS2| split; [rewrite SP2; exact SP0| split; [rewrite CR2; clear - CR CR0; lia| rewrite CG2; exact CG]]]].
  unfold apost. eapply ASTA_conseq; [exact (ASTA_switch RT Σ Σ5 _ _ c2 Hc2' AL2 AM2)|]. intros ms <-. exists (wz ret), m2.
  split; [unfold ret_st; do 16 eexists; unfold usp, e_PL; rewrite Z_to_bv_bv_unsigned; reflexivity|].
  split; [exact (conj ART2 (conj MI2 ST2))|].
  split; [eapply pres_fp_trans; [exact PRES| intros a Ha _; exact (A02 a Ha)]|].
  (* [comment removed for export] *)
  assert (ALV : forall p n (a : word), In (p, n) (rt_live RT Σ) -> p <= bv_unsigned a < p + n -> m2 a = m a).
  { intros p n a Hin Ha.
    rewrite (MU2 a). 2: { cbn [outside]. split; [| exact I]. intros R. apply NAC. right; right; left. exists p, n. split; [exact Hin| clear - R Ha; lia]. }
    apply MU1. cbn [outside]. split; [| split; [| exact I]].
    - destruct (FLV p n Hin); lia.
    - pose proof (proj1 (af_fshadow_apart RT AF Σ m f 1%nat ART0 INF) p n Hin) as X. change (fs_size 1) with (64 * 2) in X. rewrite (shad_add64 f 2 F64) in X. lia. }
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
  split; [apply (cl_env_agree m m2 _ _ CLE); intros a Ha; apply A02; apply acl_static; exact (cl_cell_static _ Ha)|].
  split; [apply (sec_off_agree m m2 SEC); intros a Ea; apply A02; apply acl_static; apply client_static_intro; rewrite Ea; unfold SEC_INIT; lia|].
  unfold pem_read_res.
  assert (PEX : exists top bot, errst_live (e_E RT en) top bot strs m2 /\ (length strs <= 2)%nat).
  { destruct PE as (PE1 & SZ & SLV & SFR).
    assert (AG : agree_on (errst_fp (e_E RT en) strs) m m2).
    { intros a Ha. destruct (errst_fp_where _ _ _ Ha) as [R|(p & n & Hin & Hp)].
      - apply A02. apply (acl_live _ _ _ (e_E RT en) 904); [exact INE| exact R].
      - apply (ALV p n); [exact (SLV _ Hin)| exact Hp]. }
    destruct PE1 as [[-> R]|(top & bot & L & LEN)].
    - exists 0, 0. split; [apply errst_rest_live; exact (errst_rest_agree _ _ _ _ R AG)| cbn; lia].
    - exists top, bot. split; [exact (errst_live_agree _ _ _ _ _ _ L AG)| exact LEN]. }
  destruct PEX as (top & bot & EL & LEN).
  exists ret, off, top, bot, strs, news.
  split; [reflexivity|]. split; [exact OFF|].
  split. { rewrite LV2. eapply mbio_rep_agree; [exact MB|]. intros a (e & He & Ha). destruct e as [p n]. apply A02. apply (acl_live _ _ _ p n); [exact (KLV _ He)| exact Ha]. }
  split. { eapply libenv_agree; [exact LE|]. intros a Ha. apply A02. destruct (libenv_fp_where _ _ Ha) as [(_ & CS & _)|(p & n & Hin & Hp)]; [apply acl_static; exact CS| apply (acl_live _ _ _ p n); [exact (INCL _ Hin)| exact Hp]]. }
  split; [exact EL|]. split; [exact LEN|]. split; [exact (proj1 (proj2 PE))|].
  split; [exact (proj1 (nd_split _ _ ND))|]. split; [exact NB|].
  split.
  { (* [comment removed for export] *)
    assert (OC : forall P (cl : cell), In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m P [cl] -> Z.of_nat (cells_size [cl]) = 8 -> rw_cells asegs m2 P [cl]).
    { intros P cl HP C SZ. eapply rw_cells_agree_nw; [exact C|]. intros a Ha. cbv beta in Ha. rewrite SZ in Ha. apply A02.
      pose proof (proj1 (Forall_forall _ _) OUTS P HP) as [AL LOC]. destruct LOC as [[L1 L2]|(f' & k' & Hin & L1 & L2 & _)].
      - exfalso. clear - L1 L2. lia.
      - apply (acl_frame _ _ _ f' k'); [exact Hin| lia]. }
    assert (BC : forall p n cs, In (p, n) news -> rw_cells asegs m p cs -> Z.of_nat (cells_size cs) = n -> rw_cells asegs m2 p cs).
    { intros p n cs Hin C SZ. eapply rw_cells_agree_nw; [exact C|]. intros a Ha. cbv beta in Ha. rewrite SZ in Ha. apply (ALV p n); [| exact Ha].
      apply CLV. apply in_or_app. right. exact Hin. }
    destruct PO as [(R0 & NN & C1 & C2 & C3 & (lw & C4))|(R1 & NM & HD & DT & nn' & nh & dlen & bn & bh & bd & NE & B1 & B2 & B3 & C1 & C2 & C3 & C4 & L1 & CN & IN1 & L2 & CH & NTH & L3 & CD)].
    - left. split; [exact R0|]. split; [exact NN|]. split; [apply OC; [cbn; tauto| exact C1| reflexivity]|]. split; [apply OC; [cbn; tauto| exact C2| reflexivity]|].
      split; [apply OC; [cbn; tauto| exact C3| reflexivity]|]. exists lw. apply OC; [cbn; tauto| exact C4| reflexivity].
    - right. split; [exact R1|]. exists NM, HD, DT, nn', nh, dlen, bn, bh, bd. split; [exact NE|]. split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
      split; [apply OC; [cbn; tauto| exact C1| reflexivity]|]. split; [apply OC; [cbn; tauto| exact C2| reflexivity]|].
      split; [apply OC; [cbn; tauto| exact C3| reflexivity]|]. split; [apply OC; [cbn; tauto| exact C4| reflexivity]|].
      split; [exact L1|]. split; [apply (BC NM nn'); [rewrite NE; cbn; tauto| exact CN| cbn; clear - B1; lia]|]. split; [exact IN1|].
      split; [exact L2|]. split; [apply (BC HD nh); [rewrite NE; cbn; tauto| exact CH| cbn; clear - B2; lia]|]. split; [exact NTH|].
      split; [exact L3|]. apply (BC DT dlen); [rewrite NE; cbn; tauto| exact CD| cbn; clear - B3; lia]. }
  split; [rewrite LV2, app_assoc; exact PERM| exact CFR].
Qed.

(* [comment removed for export] *)
Lemma end_sC : forall T (en : pem_entry) Σ m off crem lrem strs news j0 lH lF endv x1 x2 gap hj lenv j1 tav j2 bmv j3 (eH eD hBv dBv ret : Z)
    KY BMY blwY methY lenY maxY offY (F : bvmap 5 word) (fc : bv 32) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s7 s10 s11 t3 t4 t5 t6 : word) c,
  pem_com en Σ m off crem lrem (mbio_ent KY maxY ++ strs ++ news) -> pem_err en Σ strs m -> 1 <= crem ->
  pem_frame en m j0 lH lF endv eH eD x1 x2 gap -> rw_cells asegs m (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3) ->
  mbio_repx (rt_live RT Σ) m KY dBv BMY blwY methY lenY maxY offY ->
  Fz_W3_iface.pem_out ret m (e_PN RT en) (e_PH RT en) (e_PD RT en) (e_PLN RT en) news -> 254 * news_sz news <= 255 * (off - e_boff RT en) + 254 * 512 ->
  (forall c', pem_post en c' -> realizes asegs c' T) ->
  ASTA RT Σ (e_PMc RT en) (eq (pem_ms en SITE_end_bf1 m F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz (e_f RT en)) (wz dBv) s4 (wz ret) (wz (e_f RT en)) s7 s10 s11 t3 t4 t5 t6)) c ->
  realizes asegs c T.
Proof.
  intros until c. intros COM PE CRM PFR FFC MBY PO NB Hk HA.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
  pose proof (com_W_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as WOK. pose proof WOK as (HWS & HWFR & HWFF & HWF & HWL & HWP).
  assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  assert (INF : In (e_f RT en, 1%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  pose proof (end_c3_walk xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) a0 a1 a2 a3 a4 a5 a6 a7 (wz (e_f RT en)) (wz dBv) s4 (wz ret) (wz (e_f RT en)) s7
                (wz (shad (e_f RT en))) (wz SHB) s10 s11 t3 t4 t5 t6 F fc m ltac:(clear - HLO HLOS; lia) ltac:(clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia) MI) as W.
  cl_lift W HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & ((u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->) & _) & Hc1'). clear Hc1.
  eapply (pem_call_bfree RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_BF T en Σ m off crem lrem (strs ++ news) KY dBv BMY blwY methY lenY maxY offY SITE_end_bf2
            F fc u0 u1 u2 a1 a2 a3 b4 b5 b6 b7 (wz (e_f RT en)) (wz dBv) s4 (wz ret) (wz (e_f RT en)) s7 s10 s11 u3 u4 u5 u6 c1 COM MBY CRM ltac:(cbn; tauto) Hc1').
  intros Σ' m' F' fc' y0 y1 y2 b1 b2 b3 d4 d5 d6 d7 y3 y4 y5 y6 c' COM' LV' FRS' PR RL Hc'.
  assert (SL' : forall e, In e (strs ++ news) -> In e (rt_live RT Σ')) by (intros e He; apply RL; apply in_or_app; left; exact He).
  destruct (pem_frame_blob RT en m' j0 lH lF endv eH eD x1 x2 gap (pem_frame_keep RT en m m' _ _ _ j0 lH lF endv eH eD x1 x2 gap PFR PR PD TOP HWS) PD) as (nj & jj & FRB & NJ).
  refine (end_retire T en Σ' m' off (crem - 1) lrem strs news nj jj hj lenv j1 tav j2 bmv j3 ret F' fc' (wz SITE_end_bf2) y0 y1 y2 (wz 1) b1 b2 b3 d4 d5 d6 d7
           (wz dBv) s4 s7 s10 s11 y3 y4 y5 y6 c' COM' _ FRB NJ _ _ NB Hk Hc').
  - eapply (com_err_keep RT AF GOBJ AFP libenv errst_at_rest errst_live errst_fp errst_rest_agree errst_live_agree errst_fp_where FZ_SITES FZ_CALLS en Σ Σ' m m');
      [exact COM| exact PE| exact PR| intros e He; apply in_or_app; right; apply in_or_app; left; exact He| | intros e He; apply SL'; apply in_or_app; left; exact He].
    apply RL. apply in_or_app; right. exact INE.
  - exact (ff_keep m m' (e_f RT en) _ _ _ _ hj lenv j1 tav j2 bmv j3 FFC PR INF HWFF).
  - eapply (pem_out_agree ret m m'); [exact PO| exact (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m m' off crem lrem _ _ _ COM HWS HWFR PR)|].
    intros e He. eapply (com_cur_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m m'); [exact COM| exact HWL| intros e0 H0; right; exact H0| exact PR| apply in_or_app; right; apply in_or_app; right; exact He|].
    apply SL'. apply in_or_app; right; exact He.
Qed.

(* [comment removed for export] *)
Lemma end_sB : forall T (en : pem_entry) Σ m off crem lrem strs news j0 lH lF endv x1 x2 gap hj lenv j1 tav j2 bmv j3 (eH eD hBv dBv ret : Z)
    KX KY BMX BMY blwX blwY methX methY lenX maxX offX lenY maxY offY (F : bvmap 5 word) (fc : bv 32) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s10 s11 t3 t4 t5 t6 : word) c,
  pem_com en Σ m off crem lrem (mbio_ent KX maxX ++ mbio_ent KY maxY ++ strs ++ news) -> pem_err en Σ strs m -> 2 <= crem ->
  pem_frame en m j0 lH lF endv eH eD x1 x2 gap -> rw_cells asegs m (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3) ->
  mbio_repx (rt_live RT Σ) m KX hBv BMX blwX methX lenX maxX offX -> mbio_repx (rt_live RT Σ) m KY dBv BMY blwY methY lenY maxY offY ->
  Fz_W3_iface.pem_out ret m (e_PN RT en) (e_PH RT en) (e_PD RT en) (e_PLN RT en) news -> 254 * news_sz news <= 255 * (off - e_boff RT en) + 254 * 512 ->
  (forall c', pem_post en c' -> realizes asegs c' T) ->
  ASTA RT Σ (e_PMc RT en) (eq (pem_ms en SITE_end_pfree m F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz (e_f RT en)) (wz dBv) s4 (wz ret) (wz (e_f RT en)) (wz hBv) s10 s11 t3 t4 t5 t6)) c ->
  realizes asegs c T.
Proof.
  intros until c. intros COM PE CRM PFR FFC MBX MBY PO NB Hk HA.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
  pose proof (com_W_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as WOK. pose proof WOK as (HWS & HWFR & HWFF & HWF & HWL & HWP).
  assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  assert (INF : In (e_f RT en, 1%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  pose proof (end_c2_walk xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) a0 a1 a2 a3 a4 a5 a6 a7 (wz (e_f RT en)) (wz dBv) s4 (wz ret) (wz (e_f RT en)) (wz hBv)
                (wz (shad (e_f RT en))) (wz SHB) s10 s11 t3 t4 t5 t6 F fc m ltac:(clear - HLO HLOS; lia) ltac:(clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia) MI) as W.
  cl_lift W HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & ((u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->) & _) & Hc1'). clear Hc1.
  eapply (pem_call_bfree RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_BF T en Σ m off crem lrem (mbio_ent KY maxY ++ strs ++ news) KX hBv BMX blwX methX lenX maxX offX SITE_end_bf1
            F fc u0 u1 u2 a1 a2 a3 b4 b5 b6 b7 (wz (e_f RT en)) (wz dBv) s4 (wz ret) (wz (e_f RT en)) (wz hBv) s10 s11 u3 u4 u5 u6 c1 COM MBX ltac:(clear - CRM; lia) ltac:(cbn; tauto) Hc1').
  intros Σ' m' F' fc' y0 y1 y2 b1 b2 b3 d4 d5 d6 d7 y3 y4 y5 y6 c' COM' LV' FRS' PR RL Hc'.
  assert (SL' : forall e, In e (mbio_ent KY maxY ++ strs ++ news) -> In e (rt_live RT Σ')) by (intros e He; apply RL; apply in_or_app; left; exact He).
  refine (end_sC T en Σ' m' off (crem - 1) lrem strs news j0 lH lF endv x1 x2 gap hj lenv j1 tav j2 bmv j3 eH eD hBv dBv ret KY BMY blwY methY lenY maxY offY F' fc'
            (wz SITE_end_bf1) y0 y1 y2 (wz 1) b1 b2 b3 d4 d5 d6 d7 s4 (wz hBv) s10 s11 y3 y4 y5 y6 c' COM' _ ltac:(clear - CRM; lia) _ _ _ _ NB Hk Hc').
  - eapply (com_err_keep RT AF GOBJ AFP libenv errst_at_rest errst_live errst_fp errst_rest_agree errst_live_agree errst_fp_where FZ_SITES FZ_CALLS en Σ Σ' m m');
      [exact COM| exact PE| exact PR| intros e He; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact He| apply RL; apply in_or_app; right; exact INE
      | intros e He; apply SL'; apply in_or_app; right; apply in_or_app; left; exact He].
  - exact (pem_frame_keep RT en m m' _ _ _ j0 lH lF endv eH eD x1 x2 gap PFR PR PD TOP HWS).
  - exact (ff_keep m m' (e_f RT en) _ _ _ _ hj lenv j1 tav j2 bmv j3 FFC PR INF HWFF).
  - eapply (mbio_repx_keep (rt_live RT Σ)); [exact MBY| exact PR| intros e He; split; apply SL'; apply in_or_app; left; exact He|].
    intros e x He Hx. exact (com_cur_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ _ COM HWL (fun e0 H0 => or_intror H0) e x ltac:(apply in_or_app; right; apply in_or_app; left; exact He) Hx).
  - eapply (pem_out_agree ret m m'); [exact PO| exact (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m m' off crem lrem _ _ _ COM HWS HWFR PR)|].
    intros e He. eapply (com_cur_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m m'); [exact COM| exact HWL| intros e0 H0; right; exact H0| exact PR| do 3 (apply in_or_app; right); exact He|].
    apply SL'. do 2 (apply in_or_app; right); exact He.
Qed.

(* [comment removed for export] *)
Lemma end_sA : forall T (en : pem_entry) Σ m off crem lrem strs news j0 lH lF endv x1 x2 gap hj lenv j1 tav j2 bmv j3 (eH eD hBv dBv ret : Z) (oname : option (Z * Z)) namev nn
    KX KY BMX BMY blwX blwY methX methY lenX maxX offX lenY maxY offY (F : bvmap 5 word) (fc : bv 32) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) c,
  pem_com en Σ m off crem lrem (mbio_ent KX maxX ++ mbio_ent KY maxY ++ opt_ent oname ++ strs ++ news) -> pem_err en Σ strs m -> 2 <= crem ->
  pem_frame en m j0 lH lF endv eH eD x1 x2 gap -> rw_cells asegs m (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3) ->
  match oname with None => namev = 0 | Some e => e = (namev, nn) /\ 1 <= nn end ->
  mbio_repx (rt_live RT Σ) m KX hBv BMX blwX methX lenX maxX offX -> mbio_repx (rt_live RT Σ) m KY dBv BMY blwY methY lenY maxY offY ->
  Fz_W3_iface.pem_out ret m (e_PN RT en) (e_PH RT en) (e_PD RT en) (e_PLN RT en) news -> 254 * news_sz news <= 255 * (off - e_boff RT en) + 254 * 512 ->
  (forall c', pem_post en c' -> realizes asegs c' T) ->
  ASTA RT Σ (e_PMc RT en) (eq (pem_ms en SITE_end_cfree m F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz (e_f RT en)) (wz dBv) (wz (e_flags RT en)) (wz ret) (wz (e_f RT en)) (wz hBv) (wz namev) s11 t3 t4 t5 t6)) c ->
  realizes asegs c T.
Proof.
  intros until c. intros COM PE CRM PFR FFC HNAME MBX MBY PO NB Hk HA.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
  pose proof (com_W_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as WOK. pose proof WOK as (HWS & HWFR & HWFF & HWF & HWL & HWP).
  assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  assert (INF : In (e_f RT en, 1%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  pose proof (end_c1_walk xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) a0 a1 a2 a3 a4 a5 a6 a7 (wz (e_f RT en)) (wz dBv) (wz (e_flags RT en)) (wz ret) (wz (e_f RT en)) (wz hBv)
                (wz (shad (e_f RT en))) (wz SHB) (wz namev) s11 t3 t4 t5 t6 F fc m ltac:(clear - HLO HLOS; lia) ltac:(clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia) MI) as W.
  cl_lift W HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & ((u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->) & _) & Hc1'). clear Hc1.
  (* [comment removed for export] *)
  assert (KB : forall Σ' (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (v y0 y1 y2 b1 b2 b3 d4 d5 d6 d7 y3 y4 y5 y6 : word) c',
    pem_com en Σ' m' off crem lrem (mbio_ent KX maxX ++ mbio_ent KY maxY ++ strs ++ news) ->
    rt_frames RT Σ' = rt_frames RT Σ -> rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (e_sp1 RT en) (lib_W (e_LBL RT en)) m m' ->
    (forall e, In e ((mbio_ent KX maxX ++ mbio_ent KY maxY ++ strs ++ news) ++ e_live RT en) -> In e (rt_live RT Σ')) ->
    ASTA RT Σ' (e_PMc RT en) (eq (pem_ms en SITE_end_pfree m' F' fc' (wz SITE_end_pfree) y0 y1 y2 v b1 b2 b3 d4 d5 d6 d7 (wz (e_f RT en)) (wz dBv) (wz (e_flags RT en)) (wz ret) (wz (e_f RT en)) (wz hBv) (wz namev) s11 y3 y4 y5 y6)) c' ->
    realizes asegs c' T).
  { intros Σ' m' F' fc' v y0 y1 y2 b1 b2 b3 d4 d5 d6 d7 y3 y4 y5 y6 c' COM' FRS' PR RL Hc'.
    assert (SL' : forall e, In e (mbio_ent KX maxX ++ mbio_ent KY maxY ++ strs ++ news) -> In e (rt_live RT Σ')) by (intros e He; apply RL; apply in_or_app; left; exact He).
    assert (CUR : forall e, In e (mbio_ent KX maxX ++ mbio_ent KY maxY ++ strs ++ news) -> In e (mbio_ent KX maxX ++ mbio_ent KY maxY ++ opt_ent oname ++ strs ++ news)).
    { intros e He. rewrite !in_app_iff in He. rewrite !in_app_iff. clear - He. tauto. }
    refine (end_sB T en Σ' m' off crem lrem strs news j0 lH lF endv x1 x2 gap hj lenv j1 tav j2 bmv j3 eH eD hBv dBv ret KX KY BMX BMY blwX blwY methX methY lenX maxX offX lenY maxY offY F' fc'
              (wz SITE_end_pfree) y0 y1 y2 v b1 b2 b3 d4 d5 d6 d7 (wz (e_flags RT en)) (wz namev) s11 y3 y4 y5 y6 c' COM' _ CRM _ _ _ _ _ NB Hk Hc').
    - eapply (com_err_keep RT AF GOBJ AFP libenv errst_at_rest errst_live errst_fp errst_rest_agree errst_live_agree errst_fp_where FZ_SITES FZ_CALLS en Σ Σ' m m');
        [exact COM| exact PE| exact PR| intros e He; apply CUR; do 2 (apply in_or_app; right); apply in_or_app; left; exact He| apply RL; apply in_or_app; right; exact INE
        | intros e He; apply SL'; do 2 (apply in_or_app; right); apply in_or_app; left; exact He].
    - exact (pem_frame_keep RT en m m' _ _ _ j0 lH lF endv eH eD x1 x2 gap PFR PR PD TOP HWS).
    - exact (ff_keep m m' (e_f RT en) _ _ _ _ hj lenv j1 tav j2 bmv j3 FFC PR INF HWFF).
    - eapply (mbio_repx_keep (rt_live RT Σ)); [exact MBX| exact PR| intros e He; split; apply SL'; apply in_or_app; left; exact He|].
      intros e x He Hx. exact (com_cur_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ _ COM HWL (fun e0 H0 => or_intror H0) e x (CUR _ ltac:(apply in_or_app; left; exact He)) Hx).
    - eapply (mbio_repx_keep (rt_live RT Σ)); [exact MBY| exact PR| intros e He; split; apply SL'; apply in_or_app; right; apply in_or_app; left; exact He|].
      intros e x He Hx. exact (com_cur_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ _ COM HWL (fun e0 H0 => or_intror H0) e x (CUR _ ltac:(apply in_or_app; right; apply in_or_app; left; exact He)) Hx).
    - eapply (pem_out_agree ret m m'); [exact PO| exact (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m m' off crem lrem _ _ _ COM HWS HWFR PR)|].
      intros e He. eapply (com_cur_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m m'); [exact COM| exact HWL| intros e0 H0; right; exact H0| exact PR| apply CUR; do 3 (apply in_or_app; right); exact He|].
      apply SL'. do 3 (apply in_or_app; right); exact He. }
  destruct oname as [e|].
  - (* [comment removed for export] *)
    destruct HNAME as [-> NN].
    assert (HP : Permutation (mbio_ent KX maxX ++ mbio_ent KY maxY ++ opt_ent (Some (namev, nn)) ++ strs ++ news) ((namev, nn) :: mbio_ent KX maxX ++ mbio_ent KY maxY ++ strs ++ news)).
    { apply Permutation_sym. cbn [opt_ent app]. rewrite (app_assoc (mbio_ent KX maxX) (mbio_ent KY maxY) (strs ++ news)), (app_assoc (mbio_ent KX maxX) (mbio_ent KY maxY) ((namev, nn) :: strs ++ news)).
      apply Permutation_middle. }
    pose proof (com_perm RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ COM HP) as COM1.
    eapply (pem_call_pfree RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_PF T en Σ m off crem lrem _ namev nn 0 SITE_end_pfree
              F fc u0 u1 u2 (wz 1025) b4 b5 b6 b7 (wz (e_f RT en)) (wz dBv) (wz (e_flags RT en)) (wz ret) (wz (e_f RT en)) (wz hBv) (wz namev) s11 u3 u4 u5 u6 c1 COM1 ltac:(clear - NN; lia) ltac:(cbn; tauto) Hc1').
    intros Σ' m' F' fc' v y0 y1 y2 b1 b2 b3 d4 d5 d6 d7 y3 y4 y5 y6 c' COM' LV' FRS' PR RL Hc'. exact (KB Σ' m' F' fc' v y0 y1 y2 b1 b2 b3 d4 d5 d6 d7 y3 y4 y5 y6 c' COM' FRS' PR RL Hc').
  - (* [comment removed for export] *)
    subst namev. cbn [opt_ent] in COM.
    eapply (pem_call_pfree_null RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_PFN T en Σ m off crem lrem _ 0 SITE_end_pfree
              F fc u0 u1 u2 (wz 1025) b4 b5 b6 b7 (wz (e_f RT en)) (wz dBv) (wz (e_flags RT en)) (wz ret) (wz (e_f RT en)) (wz hBv) (wz 0) s11 u3 u4 u5 u6 c1 COM ltac:(clear; lia) ltac:(cbn; tauto) Hc1').
    intros Σ' m' F' fc' v y0 y1 y2 b1 b2 b3 d4 d5 d6 d7 y3 y4 y5 y6 c' COM' LV' FRS' PR Hc'.
    apply (KB Σ' m' F' fc' v y0 y1 y2 b1 b2 b3 d4 d5 d6 d7 y3 y4 y5 y6 c' COM' FRS' PR); [| exact Hc'].
    intros e He. rewrite LV'. apply (Permutation_in _ (Permutation_sym PERM)). cbn [opt_ent app] in He |- *. exact He.
Qed.

Theorem END_proof : END_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Proof.
  intros en Σ m off crem lrem strs news j0 lH lF endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F fc eH eD xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
         octx oname ctxv namev nn hBv dBv ret KX KY BMX BMY methX methY lenX maxX offX lenY maxY offY blwX blwY.
  cbv zeta. intros COM PE REM PFR FFC HCTX HNAME MBX MBY PO NB. unfold pem_at, cps. intros T c HA Hk.
  rewrite <- !app_assoc in COM.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
  pose proof (com_W_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as WOK. pose proof WOK as (HWS & HWFR & HWFF & HWF & HWL & HWP).
  assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  assert (INF : In (e_f RT en, 1%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  unfold C_END in REM.
  pose proof (end_c0_walk xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) a0 a1 a2 a3 a4 a5 a6 a7 (wz (e_f RT en)) (wz dBv) (wz (e_flags RT en)) (wz ret) (wz (e_f RT en)) (wz hBv)
                (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz ctxv) t3 t4 t5 t6 F fc m ltac:(clear - HLO HLOS; lia) ltac:(clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia) MI) as W.
  cl_lift W HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & ((u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->) & _) & Hc1'). clear Hc1.
  assert (HNAME' : match oname with None => namev = 0 | Some e => e = (namev, nn) /\ 1 <= nn end) by (destruct oname; [exact (conj (proj1 HNAME) (proj1 (proj2 HNAME)))| exact HNAME]).
  (* [comment removed for export] *)
  assert (KA : forall Σ' (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (v y0 y1 y2 b1 b2 b3 d4 d5 d6 d7 y3 y4 y5 y6 : word) c',
    pem_com en Σ' m' off crem lrem (mbio_ent KX maxX ++ mbio_ent KY maxY ++ opt_ent oname ++ strs ++ news) ->
    rt_frames RT Σ' = rt_frames RT Σ -> rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (e_sp1 RT en) [] m m' ->
    (forall e, In e ((mbio_ent KX maxX ++ mbio_ent KY maxY ++ opt_ent oname ++ strs ++ news) ++ e_live RT en) -> In e (rt_live RT Σ')) ->
    ASTA RT Σ' (e_PMc RT en) (eq (pem_ms en SITE_end_cfree m' F' fc' (wz SITE_end_cfree) y0 y1 y2 v b1 b2 b3 d4 d5 d6 d7 (wz (e_f RT en)) (wz dBv) (wz (e_flags RT en)) (wz ret) (wz (e_f RT en)) (wz hBv) (wz namev) (wz ctxv) y3 y4 y5 y6)) c' ->
    realizes asegs c' T).
  { intros Σ' m' F' fc' v y0 y1 y2 b1 b2 b3 d4 d5 d6 d7 y3 y4 y5 y6 c' COM' FRS' PR0 RL Hc'.
    assert (PR : rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (e_sp1 RT en) (lib_W (e_LBL RT en)) m m') by (intros a Ha _; exact (PR0 a Ha I)).
    assert (SL' : forall e, In e (mbio_ent KX maxX ++ mbio_ent KY maxY ++ opt_ent oname ++ strs ++ news) -> In e (rt_live RT Σ')) by (intros e He; apply RL; apply in_or_app; left; exact He).
    assert (CUR : forall e, In e (mbio_ent KX maxX ++ mbio_ent KY maxY ++ opt_ent oname ++ strs ++ news) -> In e (mbio_ent KX maxX ++ mbio_ent KY maxY ++ opt_ent octx ++ opt_ent oname ++ strs ++ news)).
    { intros e He. rewrite !in_app_iff in He. rewrite !in_app_iff. clear - He. tauto. }
    refine (end_sA T en Σ' m' off crem lrem strs news j0 lH lF endv x1 x2 gap hj lenv j1 tav j2 bmv j3 eH eD hBv dBv ret oname namev nn KX KY BMX BMY blwX blwY methX methY lenX maxX offX lenY maxY offY F' fc'
              (wz SITE_end_cfree) y0 y1 y2 v b1 b2 b3 d4 d5 d6 d7 (wz ctxv) y3 y4 y5 y6 c' COM' _ ltac:(clear - REM; lia) _ _ HNAME' _ _ _ NB Hk Hc').
    - eapply (com_err_keep RT AF GOBJ AFP libenv errst_at_rest errst_live errst_fp errst_rest_agree errst_live_agree errst_fp_where FZ_SITES FZ_CALLS en Σ Σ' m m');
        [exact COM| exact PE| exact PR| intros e He; apply CUR; do 3 (apply in_or_app; right); apply in_or_app; left; exact He| apply RL; apply in_or_app; right; exact INE
        | intros e He; apply SL'; do 3 (apply in_or_app; right); apply in_or_app; left; exact He].
    - exact (pem_frame_keep RT en m m' _ _ _ j0 lH lF endv eH eD x1 x2 gap PFR PR PD TOP HWS).
    - exact (ff_keep m m' (e_f RT en) _ _ _ _ hj lenv j1 tav j2 bmv j3 FFC PR INF HWFF).
    - eapply (mbio_repx_keep (rt_live RT Σ)); [exact MBX| exact PR| intros e He; split; apply SL'; apply in_or_app; left; exact He|].
      intros e x He Hx. exact (com_cur_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ _ COM HWL (fun e0 H0 => or_intror H0) e x (CUR _ ltac:(apply in_or_app; left; exact He)) Hx).
    - eapply (mbio_repx_keep (rt_live RT Σ)); [exact MBY| exact PR| intros e He; split; apply SL'; apply in_or_app; right; apply in_or_app; left; exact He|].
      intros e x He Hx. exact (com_cur_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ _ COM HWL (fun e0 H0 => or_intror H0) e x (CUR _ ltac:(apply in_or_app; right; apply in_or_app; left; exact He)) Hx).
    - eapply (pem_out_agree ret m m'); [exact PO| exact (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m m' off crem lrem _ _ _ COM HWS HWFR PR)|].
      intros e He. eapply (com_cur_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m m'); [exact COM| exact HWL| intros e0 H0; right; exact H0| exact PR| apply CUR; do 4 (apply in_or_app; right); exact He|].
      apply SL'. do 4 (apply in_or_app; right); exact He. }
  destruct octx as [e|].
  - (* [comment removed for export] *)
    subst e.
    assert (HP : Permutation (mbio_ent KX maxX ++ mbio_ent KY maxY ++ opt_ent (Some (ctxv, ECTX)) ++ opt_ent oname ++ strs ++ news) ((ctxv, ECTX) :: mbio_ent KX maxX ++ mbio_ent KY maxY ++ opt_ent oname ++ strs ++ news)).
    { apply Permutation_sym. cbn [opt_ent app]. rewrite (app_assoc (mbio_ent KX maxX) (mbio_ent KY maxY) (opt_ent oname ++ strs ++ news)),
        (app_assoc (mbio_ent KX maxX) (mbio_ent KY maxY) ((ctxv, ECTX) :: opt_ent oname ++ strs ++ news)).
      apply Permutation_middle. }
    pose proof (com_perm RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ COM HP) as COM1.
    eapply (pem_call_cfree RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_CF T en Σ m off crem lrem _ ctxv SITE_end_cfree
              F fc u0 u1 u2 a1 a2 a3 b4 b5 b6 b7 (wz (e_f RT en)) (wz dBv) (wz (e_flags RT en)) (wz ret) (wz (e_f RT en)) (wz hBv) (wz namev) (wz ctxv) u3 u4 u5 u6 c1 COM1 ltac:(cbn; tauto) Hc1').
    intros Σ' m' F' fc' v y0 y1 y2 b1 b2 b3 d4 d5 d6 d7 y3 y4 y5 y6 c' COM' LV' FRS' PR RL Hc'. exact (KA Σ' m' F' fc' v y0 y1 y2 b1 b2 b3 d4 d5 d6 d7 y3 y4 y5 y6 c' COM' FRS' PR RL Hc').
  - (* [comment removed for export] *)
    subst ctxv. cbn [opt_ent app] in COM.
    eapply (pem_call_cfree_null RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_CFN T en Σ m off crem lrem _ SITE_end_cfree
              F fc u0 u1 u2 a1 a2 a3 b4 b5 b6 b7 (wz (e_f RT en)) (wz dBv) (wz (e_flags RT en)) (wz ret) (wz (e_f RT en)) (wz hBv) (wz namev) (wz 0) u3 u4 u5 u6 c1 COM ltac:(cbn; tauto) Hc1').
    intros m' F' fc' v y0 y1 y2 b1 b2 b3 d4 d5 d6 d7 y3 y4 y5 y6 c' COM' PR Hc'.
    apply (KA Σ m' F' fc' v y0 y1 y2 b1 b2 b3 d4 d5 d6 d7 y3 y4 y5 y6 c' COM' eq_refl PR); [| exact Hc'].
    intros e He. apply (Permutation_in _ (Permutation_sym PERM)). cbn [opt_ent app] in He |- *. exact He.
Qed.

(* [comment removed for export] *)
Theorem END0_proof : END0_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Proof.
  intros en Σ m off crem lrem strs nj jj hj lenv j1 tav j2 bmv j3 F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s10 s11 t3 t4 t5 t6 COM PE REM FRB NJ FFC ON.
  unfold pem_at, cps. intros T c HA Hk.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
  pose proof (com_W_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as WOK. pose proof WOK as (HWS & HWFR & HWFF & HWF & HWL & HWP).
  assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  assert (INF : In (e_f RT en, 1%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  assert (SP0' : 0 <= e_sp1 RT en) by (clear - HLO HLOS; lia). assert (SPH : e_sp1 RT en + 368 <= 2 ^ 47) by (clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia).
  (* [comment removed for export] *)
  pose proof (end_e1_walk xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) a0 a1 a2 a3 a4 a5 a6 a7 (wz (e_f RT en)) (wz 0) (wz (e_flags RT en)) s5 (wz (e_f RT en)) (wz 0)
                (wz (shad (e_f RT en))) (wz SHB) s10 s11 t3 t4 t5 t6 F fc m MI) as W.
  cl_lift W HA c0 Hc0. destruct (ASTA_unpack RT Σ _ _ c0 Hc0) as (ms0 & (-> & _) & Hc0'). clear Hc0.
  (* [comment removed for export] *)
  pose proof (end_c0_walk xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) a0 a1 a2 a3 a4 a5 a6 a7 (wz (e_f RT en)) (wz 0) (wz (e_flags RT en)) (wz 0) (wz (e_f RT en)) (wz 0)
                (wz (shad (e_f RT en))) (wz SHB) (wz 0) (wz 0) t3 t4 t5 t6 F fc m SP0' SPH MI) as W.
  cl_lift W Hc0' c1 Hc1. destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & ((u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->) & _) & Hc1'). clear Hc1 Hc0'.
  eapply (pem_call_cfree_null RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_CFN T en Σ m off crem lrem _ SITE_end_cfree
            F fc u0 u1 u2 a1 a2 a3 b4 b5 b6 b7 (wz (e_f RT en)) (wz 0) (wz (e_flags RT en)) (wz 0) (wz (e_f RT en)) (wz 0) (wz 0) (wz 0) u3 u4 u5 u6 c1 COM ltac:(cbn; tauto) Hc1').
  clear Hc1' u0 u1 u2 b4 b5 b6 b7 u3 u4 u5 u6. intros m1 F1 fc1 v1 z0 z1 z2 d1 d2 d3 d4 d5 d6 d7 z3 z4 z5 z6 c1' COM1 PR1 Hc1.
  pose proof COM1 as (_ & MI1 & _).
  (* [comment removed for export] *)
  pose proof (end_c1_walk (wz SITE_end_cfree) (e_sp1 RT en) (e_gp RT en) z0 z1 z2 (e_sp RT en) (wz (e_sp1 RT en)) v1 d1 d2 d3 d4 d5 d6 d7 (wz (e_f RT en)) (wz 0) (wz (e_flags RT en)) (wz 0) (wz (e_f RT en)) (wz 0)
                (wz (shad (e_f RT en))) (wz SHB) (wz 0) (wz 0) z3 z4 z5 z6 F1 fc1 m1 SP0' SPH MI1) as W.
  cl_lift W Hc1 c2 Hc2. destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & ((u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->) & _) & Hc2'). clear Hc2 Hc1.
  eapply (pem_call_pfree_null RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_PFN T en Σ m1 off crem lrem _ 0 SITE_end_pfree
            F1 fc1 u0 u1 u2 (wz 1025) b4 b5 b6 b7 (wz (e_f RT en)) (wz 0) (wz (e_flags RT en)) (wz 0) (wz (e_f RT en)) (wz 0) (wz 0) (wz 0) u3 u4 u5 u6 c2 COM1 ltac:(clear; lia) ltac:(cbn; tauto) Hc2').
  clear Hc2' u0 u1 u2 b4 b5 b6 b7 u3 u4 u5 u6. intros Σ2 m2 F2 fc2 v2 w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 c2' COM2 LV2 FRS2 PR2 Hc2.
  pose proof COM2 as (_ & MI2 & _).
  (* [comment removed for export] *)
  pose proof (end_c2_walk (wz SITE_end_pfree) (e_sp1 RT en) (e_gp RT en) w0 w1 w2 (e_sp RT en) (wz (e_sp1 RT en)) v2 e1 e2 e3 e4 e5 e6 e7 (wz (e_f RT en)) (wz 0) (wz (e_flags RT en)) (wz 0) (wz (e_f RT en)) (wz 0)
                (wz (shad (e_f RT en))) (wz SHB) (wz 0) (wz 0) w3 w4 w5 w6 F2 fc2 m2 SP0' SPH MI2) as W.
  cl_lift W Hc2 c3 Hc3. destruct (ASTA_unpack RT Σ2 _ _ c3 Hc3) as (ms3 & ((u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->) & _) & Hc3'). clear Hc3 Hc2.
  eapply (pem_call_bfree_null RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_BFN T en Σ2 m2 off crem lrem _ SITE_end_bf1
            F2 fc2 u0 u1 u2 e1 e2 e3 b4 b5 b6 b7 (wz (e_f RT en)) (wz 0) (wz (e_flags RT en)) (wz 0) (wz (e_f RT en)) (wz 0) (wz 0) (wz 0) u3 u4 u5 u6 c3 COM2 ltac:(cbn; tauto) Hc3').
  clear Hc3' u0 u1 u2 b4 b5 b6 b7 u3 u4 u5 u6. intros m3 F3 fc3 x0 y1 y2 g1 g2 g3 g4 g5 g6 g7 x3 x4 x5 x6 c3' COM3 PR3 Hc3.
  pose proof COM3 as (_ & MI3 & _).
  pose proof (end_c3_walk (wz SITE_end_bf1) (e_sp1 RT en) (e_gp RT en) x0 y1 y2 (e_sp RT en) (wz (e_sp1 RT en)) (wz 0) g1 g2 g3 g4 g5 g6 g7 (wz (e_f RT en)) (wz 0) (wz (e_flags RT en)) (wz 0) (wz (e_f RT en)) (wz 0)
                (wz (shad (e_f RT en))) (wz SHB) (wz 0) (wz 0) x3 x4 x5 x6 F3 fc3 m3 SP0' SPH MI3) as W.
  cl_lift W Hc3 c4 Hc4. destruct (ASTA_unpack RT Σ2 _ _ c4 Hc4) as (ms4 & ((u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->) & _) & Hc4'). clear Hc4 Hc3.
  eapply (pem_call_bfree_null RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_BFN T en Σ2 m3 off crem lrem _ SITE_end_bf2
            F3 fc3 u0 u1 u2 g1 g2 g3 b4 b5 b6 b7 (wz (e_f RT en)) (wz 0) (wz (e_flags RT en)) (wz 0) (wz (e_f RT en)) (wz 0) (wz 0) (wz 0) u3 u4 u5 u6 c4 COM3 ltac:(cbn; tauto) Hc4').
  clear Hc4' u0 u1 u2 b4 b5 b6 b7 u3 u4 u5 u6. intros m4 F4 fc4 k0 k1 k2 h1 h2 h3 h4 h5 h6 h7 k3 k4 k5 k6 c4' COM4 PR4 Hc4.
  (* [comment removed for export] *)
  assert (PR : rt_pres_fp (rt_live RT Σ2) (rt_frames RT Σ) (e_sp1 RT en) (lib_W (e_LBL RT en)) m m4).
  { intros a Ha Ho. rewrite FRS2 in PR3, PR4. rewrite (PR4 a Ha I), (PR3 a Ha I). rewrite (PR2 a Ha Ho). rewrite LV2 in Ha. exact (PR1 a Ha I). }
  assert (COM5 : pem_com en Σ2 m4 off crem lrem (strs ++ [])) by (rewrite app_nil_r; exact COM4).
  refine (end_retire T en Σ2 m4 off crem lrem strs [] nj jj hj lenv j1 tav j2 bmv j3 0 F4 fc4 (wz SITE_end_bf2) k0 k1 k2 (wz 0) h1 h2 h3 h4 h5 h6 h7
            (wz 0) (wz (e_flags RT en)) (wz 0) (wz 0) (wz 0) k3 k4 k5 k6 c4' COM5 _ _ NJ _ _ _ Hk Hc4).
  - eapply (com_err_keep RT AF GOBJ AFP libenv errst_at_rest errst_live errst_fp errst_rest_agree errst_live_agree errst_fp_where FZ_SITES FZ_CALLS en Σ Σ2 m m4);
      [exact COM| exact PE| exact PR| intros e He; exact He| rewrite LV2; exact (ELV _ INE)| intros e He; rewrite LV2; exact (CLV _ He)].
  - eapply stack_keep; [exact FRB| exact PR| lia| cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, NJ; unfold e_sp1; clear - TOP PD; lia|].
    intros x Hx. apply HWS. cbn [cells_size csize Nat.add] in Hx. rewrite Nat.add_0_r, NJ in Hx. unfold e_sp1 in *. clear - Hx TOP PD. lia.
  - exact (ff_keep m m4 (e_f RT en) _ _ _ _ hj lenv j1 tav j2 bmv j3 FFC PR INF HWFF).
  - destruct ON as (O1 & O2 & O3 & O4). pose proof (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m m4 off crem lrem _ _ _ COM HWS HWFR PR) as AGP.
    assert (G8 : forall P v, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m P [C8 v] -> rw_cells asegs m4 P [C8 v]).
    { intros P v HP C. eapply rw_cells_agree_nw; [exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact (AGP P HP). }
    left. split; [reflexivity|]. split; [reflexivity|]. split; [apply G8; [cbn; tauto| exact O1]|]. split; [apply G8; [cbn; tauto| exact O2]|].
    split; [apply G8; [cbn; tauto| exact O3]|]. exists (wz 0). apply G8; [cbn; tauto| exact O4].
  - cbn. clear - OFF. lia.
Qed.

(* [comment removed for export] *)
Theorem RELOAD_proof : RELOAD_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Proof.
  intros en Σ m off crem lrem strs news j0 lH lF endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F fc eH eD xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 t3 t4 t5 t6
         octx oname ctxv namev nn hBv dBv ret KX KY BMX BMY methX methY lenX maxX offX lenY maxY offY blwX blwY.
  cbv zeta. intros COM PE REM PFR FFC HCTX HNAME MBX MBY PO NB. unfold pem_at, cps. intros T c HA Hk.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  pose proof PFR as (_ & _ & _ & _ & _ & _ & FRE & _). unfold loc_E in FRE.
  pose proof (end_rl_walk xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz dBv) s4 (wz ret) s6 (wz hBv) (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz ctxv) t3 t4 t5 t6 F fc m
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(clear - HLO HLOS; lia) ltac:(clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia) MI FRE) as W.
  cl_lift W HA c1 Hc1. destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (-> & _) & Hc1'). clear Hc1.
  exact (END_proof en Σ m off crem lrem strs news j0 lH lF endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F fc eH eD xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
           octx oname ctxv namev nn hBv dBv ret KX KY BMX BMY methX methY lenX maxX offX lenY maxY offY blwX blwY COM PE REM PFR FFC HCTX HNAME MBX MBY PO NB T c1 Hc1' Hk).
Qed.

(* [comment removed for export] *)
Theorem FREE1X_proof : FREE1X_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Proof.
  intros en Σ m off crem lrem strs j0 lH lF endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s11 t3 t4 t5 t6
         oname namev nn hBv dBv KX KY methX methY lenX maxX lenY maxY.
  cbv zeta. intros COM PE REM PFR FFC ON HNAME MBX MBY. unfold pem_at, cps. intros T c HA Hk.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  pose proof PFR as (_ & _ & _ & _ & _ & _ & FRE & _). unfold loc_E in FRE.
  pose proof (end_fx_walk xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (wz (e_flags RT en)) s5 s6 s7 (wz (shad (e_f RT en))) (wz SHB) (wz namev) s11 t3 t4 t5 t6 F fc m
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(clear - HLO HLOS; lia) ltac:(clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia) MI FRE) as W.
  cl_lift W HA c1 Hc1. destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (-> & _) & Hc1'). clear Hc1.
  destruct MBX as [BMX MBX']. destruct MBY as [BMY MBY'].
  assert (COM1 : pem_com en Σ m off crem lrem ((mbio_ent KX maxX ++ mbio_ent KY maxY ++ opt_ent None ++ opt_ent oname) ++ strs ++ [])).
  { rewrite app_nil_r. cbn [opt_ent]. rewrite (app_nil_l (opt_ent oname)). exact COM. }
  refine (END_proof en Σ m off crem lrem strs [] j0 lH lF endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F fc hBv dBv xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
           None oname 0 namev nn hBv dBv 0 KX KY BMX BMY methX methY lenX maxX 0 lenY maxY 0 (wz lenX) (wz lenY) COM1 PE REM PFR FFC eq_refl HNAME MBX' MBY' _ _ T c1 Hc1' Hk).
  - destruct ON as (O1 & O2 & O3 & O4). left. split; [reflexivity|]. split; [reflexivity|]. split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. exists (wz 0). exact O4.
  - cbn. clear - OFF. lia.
Qed.
End CEnd.
