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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg IcptSpec.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_M_malloc Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_grow Fz_W1_pploc Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_aux Fz_W3_aux2 Fz_W3_aux3 Fz_W3_aux4 Fz_W3_lits Fz_W4_defs Fz_W4_init Fz_W4_update Fz_W4_final.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_W4_defs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation wz := (Z_to_bv 64) (only parsing).
Definition SITE_in_dinit : Z := 0x30c95c.   (* [comment removed for export] *)
Definition SITE_in_dupd : Z := 0x30c990.    (* [comment removed for export] *)
Definition SITE_in_dfin : Z := 0x30c9cc.    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition LIT_B64TAB : Z := 672160.        Definition LIT_B64TAB_SZ : Z := 128.

Local Ltac zsh := cbv beta; try change (bv_unsigned (Z_to_bv 8 0)) with 0; try change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0); try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).
(* [comment removed for export] *)
Lemma sx32_small : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold sx32. rewrite unsigned_lit by lia. rewrite swrap32_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma in_c0_walk : forall ra sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte) (p : Z),
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR (wz SITE_in_dinit) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 (wz p) t3 t4 t5 t6) F (wz e_EVP_DecodeInit) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_INI) fc None m (seg_rom asegs)).
Proof.
  intros until p. intros MI. unfold J_INI, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. unfold SITE_in_dinit, e_EVP_DecodeInit. apply evt_done. split; [reflexivity| exact I].
Qed.

(* [comment removed for export] *)
Lemma in_c1_walk : forall sp1 gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte)
    (f BM C d n : Z) (hj : list byte) (j1 : list byte) (tav : word) (j2 j3 : list byte) (blw w2 w3 q0 : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 0 < f -> f + 128 <= sp1 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 80) [C8 q0; C8 (wz (f + 32)); C8 (wz (f + 64))] -> rw_cells asegs m f (ff_cells hj (wz n) j1 tav j2 (wz BM) j3) ->
  rw_cells asegs m BM [C8 blw; C8 (wz d); C8 w2; C8 w3] -> acc asegs m BM 32 -> BM mod 8 = 0 -> 0 < BM -> BM + 32 <= sp1 -> 0 <= n < 2 ^ 31 ->
  evt asegs (fun ms => ms = MS (mkR (wz SITE_in_dupd) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz C) (wz d) (wz (f + 32)) (wz d) (wz n) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (wz SHB) s10 (wz C) t3 t4 t5 t6)
                          F (wz e_EVP_DecodeUpdate) fc None m (seg_rom asegs) /\ True)
    (MS (mkR (wz SITE_in_dinit) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (wz SHB) s10 (wz C) t3 t4 t5 t6)
        F (wz SITE_in_dinit) fc None m (seg_rom asegs)).
Proof.
  intros until q0. intros SP0 SPH F0 FH MI FRF FFC BMC ACC BAL B0 BH NR. unfold SITE_in_dinit, TP_A, SHB in *. unfold ff_cells in FFC.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  assert (EUf : bv_unsigned (Z_to_bv 64 (f + 64)) = f + 64) by (apply unsigned_lit; lia).
  assert (EUg : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  assert (EUb : bv_unsigned (Z_to_bv 64 BM) = BM) by (apply unsigned_lit; lia).
  zstep. zstep. zstep. lfix.
  zstep. zstep. zstep. zsh. zstep. if_false.
  zstep. zstep. zstep. rewrite (sx32_small n) by lia.
  zstep. zstep. zstep.
  unfold SITE_in_dupd, e_EVP_DecodeUpdate. apply evt_done. split; [reflexivity| exact I].
Qed.

(* [comment removed for export] *)
Lemma in_c2r_walk : forall ra sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_RZT) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_in_dupd) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI. unfold SITE_in_dupd, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. th_if_lit. unfold J_RZT. apply evt_done. split; [reflexivity| exact I].
Qed.
Lemma in_c3r_walk : forall ra sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_RZT) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_in_dfin) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI. unfold SITE_in_dfin, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. th_if_lit. unfold J_RZT. apply evt_done. split; [reflexivity| exact I].
Qed.

(* [comment removed for export] *)
Lemma in_c2_walk : forall sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte)
    (f BM C d n rv : Z) (hj : list byte) (j1 : list byte) (tav : word) (j2 j3 : list byte) (blw w2 w3 : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 0 < f -> f + 128 <= sp1 -> 0 <= rv <= 1 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 80) [C8 (wz (f + 48)); C8 (wz (f + 32)); C8 (wz (f + 64))] -> rw_cells asegs m f (ff_cells hj (wz n) j1 tav j2 (wz BM) j3) ->
  rw_cells asegs m BM [C8 blw; C8 (wz d); C8 w2; C8 w3] -> acc asegs m BM 32 -> BM mod 8 = 0 -> 0 < BM -> BM + 32 <= sp1 -> 0 <= n < 2 ^ 31 -> 0 < d -> d + n < 2 ^ 47 ->
  evt asegs (fun ms => ms = MS (mkR (wz SITE_in_dfin) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz C) (wz (d + n)) (wz (f + 48)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (wz SHB) s10 (wz C) t3 t4 t5 t6)
                          F (wz e_EVP_DecodeFinal) fc None m (seg_rom asegs) /\ True)
    (MS (mkR (wz SITE_in_dupd) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (wz SHB) s10 (wz C) t3 t4 t5 t6)
        F (wz SITE_in_dupd) fc None m (seg_rom asegs)).
Proof.
  intros until w3. intros SP0 SPH F0 FH RV MI FRF FFC BMC ACC BAL B0 BH NR D0 DH. unfold SITE_in_dupd, TP_A, SHB in *. unfold ff_cells in FFC.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  assert (EUf : bv_unsigned (Z_to_bv 64 (f + 64)) = f + 64) by (apply unsigned_lit; lia).
  assert (EUg : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  assert (EUb : bv_unsigned (Z_to_bv 64 BM) = BM) by (apply unsigned_lit; lia).
  assert (EUd : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K RV; lia|]. clear K.
  zstep. zstep. zstep. lfix.
  zstep. zstep. zstep. zsh. zstep. if_false.
  zstep. zstep. zstep. rewrite (sx32_small n) by lia.
  zstep.
  zstep. zstep. zstep.
  try replace (n + d) with (d + n) by lia.
  unfold SITE_in_dfin, e_EVP_DecodeFinal. apply evt_done. split; [reflexivity| exact I].
Qed.

(* [comment removed for export] *)
Lemma in_c3_walk : forall sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte)
    (f BM C d ret dl rv : Z) (hj : list byte) (j1 : list byte) (j2 j3 : list byte) (blw w2 w3 : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 0 < f -> f + 128 <= sp1 -> (f + 128 <= 2147450880 \/ 17594333495296 <= f) -> 0 <= rv <= 1 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 80) [C8 (wz (f + 48)); C8 (wz (f + 32)); C8 (wz (f + 64))] -> rw_cells asegs m f (ff_cells hj (wz ret) j1 (wz dl) j2 (wz BM) j3) ->
  rw_cells asegs m BM [C8 blw; C8 (wz d); C8 w2; C8 w3] -> acc asegs m BM 32 -> BM mod 8 = 0 -> 17594333495296 <= BM -> BM + 32 <= sp1 -> (BM + 32 <= f \/ f + 128 <= BM) ->
  0 <= ret -> 0 <= dl -> ret + dl < 2 ^ 31 ->
  evt asegs (fun ms => exists (m' : word -> option byte),
       ms = MS (mkR (wz SITE_in_dfin) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz BM) (wz (ret + dl)) (wz 0) (wz (f + 32)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (wz SHB) s10 (wz C) t3 t4 t5 t6)
               F (wz J_DEC) fc None m' (seg_rom asegs)
       /\ munch [(f + 32, f + 36); (BM, BM + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' f (ff_cells hj (wz (ret + dl)) j1 (wz dl) j2 (wz BM) j3) /\ rw_cells asegs m' BM [C8 (wz (ret + dl)); C8 (wz d); C8 w2; C8 w3])
    (MS (mkR (wz SITE_in_dfin) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (wz SHB) s10 (wz C) t3 t4 t5 t6)
        F (wz SITE_in_dfin) fc None m (seg_rom asegs)).
Proof.
  intros until w3. intros SP0 SPH F0 FH FSH RV MI FRF FFC BMC ACC BAL BHI BH BF R0 DL0 RD. unfold SITE_in_dfin, TP_A, SHB in *. unfold ff_cells in FFC.
  pose proof (munch_refl [(f + 32, f + 36); (BM, BM + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (SHFP : sh_fp [(f + 32, f + 36); (BM, BM + 8)]) by sh_fp_lia.
  assert (EU : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  assert (EUf : bv_unsigned (Z_to_bv 64 (f + 64)) = f + 64) by (apply unsigned_lit; lia).
  assert (EUg : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  assert (EUh : bv_unsigned (Z_to_bv 64 (f + 48)) = f + 48) by (apply unsigned_lit; lia).
  assert (EUb : bv_unsigned (Z_to_bv 64 BM) = BM) by (apply unsigned_lit; lia).
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K RV; lia|]. clear K.
  zstep. zstep. rewrite (sx32_small dl) by lia.
  zstep. zstep. rewrite (sx32_small ret) by lia.
  zstep. zstep.
  zstep. rewrite ?(ubs_sw32 (ret + dl)) by lia. rewrite ?(ubs_sw32 (dl + ret)) by lia. try replace (dl + ret) with (ret + dl) by lia.
  zstep. zstep. lfix.
  zstep. zstep. zsh. zstep. if_false.
  zstep. lfix. change Startup_glue.z64 with (Z_to_bv 64 0).
  unfold J_DEC. apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FFC| exact BMC].
Qed.

(* [comment removed for export] *)
Lemma ff_acc4 : forall (m : word -> option byte) f (sj : list byte), f mod 64 = 0 -> 0 < f -> rw_cells asegs m (shad f) (ff_shadow sj) -> acc asegs m (f + 32) 4 /\ acc asegs m (f + 48) 4.
Proof.
  intros m f sj F64 F0 FFS. unfold ff_shadow in FFS.
  assert (E32 : shad (f + 32) = shad f + 4) by (rewrite (shad_aligned_add f 32) by lia; reflexivity).
  assert (E48 : shad (f + 48) = shad f + 6) by (rewrite (shad_aligned_add f 48) by lia; reflexivity).
  split.
  - apply (acc_ushadow asegs m (f + 32) 4); [clear - F64; Z.div_mod_to_equations; lia| lia| lia|]. rewrite E32. unfold ushadow. cbn.
    exact (rw_C1_bytes m _ _ (rw_cells_head m _ _ _ (rw_cells_skip m (shad f) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15))] _ FFS))).
  - apply (acc_ushadow asegs m (f + 48) 4); [clear - F64; Z.div_mod_to_equations; lia| lia| lia|]. rewrite E48. unfold ushadow. cbn.
    exact (rw_C1_bytes m _ _ (rw_cells_head m _ _ _ (rw_cells_skip m (shad f)
             [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14))] _ FFS))).
Qed.

(* [comment removed for export] *)
Lemma ff_upd32 : forall (m m' : word -> option byte) f hj lv lv' j1 tav j2 bmv j3,
  rw_cells asegs m f (ff_cells hj lv j1 tav j2 bmv j3) -> (forall a : word, f <= bv_unsigned a < f + 120 -> ~ (f + 32 <= bv_unsigned a < f + 36) -> m' a = m a) ->
  rw_cells asegs m' (f + 32) [C4 lv'] -> rw_cells asegs m' f (ff_cells hj lv' j1 tav j2 bmv j3).
Proof.
  intros m m' f hj lv lv' j1 tav j2 bmv j3 FFC AG C. unfold ff_cells in *.
  change [C8 (Z_to_bv 64 FF_MAGIC); C8 (Z_to_bv 64 FF_DESCR); CB 16 hj; C4 lv; CB 12 j1; C4 tav; CB 12 j2; C8 bmv; CB 48 j3]
    with ([C8 (Z_to_bv 64 FF_MAGIC); C8 (Z_to_bv 64 FF_DESCR); CB 16 hj] ++ [C4 lv] ++ [CB 12 j1; C4 tav; CB 12 j2; C8 bmv; CB 48 j3]) in FFC.
  pose proof (proj1 (rw_cells_app m _ _ _) FFC) as [FA FBC]. pose proof (proj1 (rw_cells_app m _ _ _) FBC) as [_ FC]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in FA, FC.
  change [C8 (Z_to_bv 64 FF_MAGIC); C8 (Z_to_bv 64 FF_DESCR); CB 16 hj; C4 lv'; CB 12 j1; C4 tav; CB 12 j2; C8 bmv; CB 48 j3]
    with ([C8 (Z_to_bv 64 FF_MAGIC); C8 (Z_to_bv 64 FF_DESCR); CB 16 hj] ++ [C4 lv'] ++ [CB 12 j1; C4 tav; CB 12 j2; C8 bmv; CB 48 j3]).
  apply (proj2 (rw_cells_app m' _ _ _)). split.
  - eapply rw_cells_agree_nw; [exact FA|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply AG; lia.
  - apply (proj2 (rw_cells_app m' _ _ _)). cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. split; [exact C|].
    eapply rw_cells_agree_nw; [exact FC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply AG; lia.
Qed.
Lemma ff_upd48 : forall (m m' : word -> option byte) f hj lv j1 tav tav' j2 bmv j3,
  rw_cells asegs m f (ff_cells hj lv j1 tav j2 bmv j3) -> (forall a : word, f <= bv_unsigned a < f + 120 -> ~ (f + 48 <= bv_unsigned a < f + 52) -> m' a = m a) ->
  rw_cells asegs m' (f + 48) [C4 tav'] -> rw_cells asegs m' f (ff_cells hj lv j1 tav' j2 bmv j3).
Proof.
  intros m m' f hj lv j1 tav tav' j2 bmv j3 FFC AG C. unfold ff_cells in *.
  change [C8 (Z_to_bv 64 FF_MAGIC); C8 (Z_to_bv 64 FF_DESCR); CB 16 hj; C4 lv; CB 12 j1; C4 tav; CB 12 j2; C8 bmv; CB 48 j3]
    with ([C8 (Z_to_bv 64 FF_MAGIC); C8 (Z_to_bv 64 FF_DESCR); CB 16 hj; C4 lv; CB 12 j1] ++ [C4 tav] ++ [CB 12 j2; C8 bmv; CB 48 j3]) in FFC.
  pose proof (proj1 (rw_cells_app m _ _ _) FFC) as [FA FBC]. pose proof (proj1 (rw_cells_app m _ _ _) FBC) as [_ FC]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in FA, FC.
  change [C8 (Z_to_bv 64 FF_MAGIC); C8 (Z_to_bv 64 FF_DESCR); CB 16 hj; C4 lv; CB 12 j1; C4 tav'; CB 12 j2; C8 bmv; CB 48 j3]
    with ([C8 (Z_to_bv 64 FF_MAGIC); C8 (Z_to_bv 64 FF_DESCR); CB 16 hj; C4 lv; CB 12 j1] ++ [C4 tav'] ++ [CB 12 j2; C8 bmv; CB 48 j3]).
  apply (proj2 (rw_cells_app m' _ _ _)). split.
  - eapply rw_cells_agree_nw; [exact FA|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply AG; lia.
  - apply (proj2 (rw_cells_app m' _ _ _)). cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. split; [exact C|].
    eapply rw_cells_agree_nw; [exact FC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply AG; lia.
Qed.
(* [comment removed for export] *)
Lemma ff_cell32 : forall (m : word -> option byte) f hj lv j1 tav j2 bmv j3, rw_cells asegs m f (ff_cells hj lv j1 tav j2 bmv j3) -> rw_cells asegs m (f + 32) [C4 lv].
Proof.
  intros m f hj lv j1 tav j2 bmv j3 FFC. unfold ff_cells in FFC.
  change [C8 (Z_to_bv 64 FF_MAGIC); C8 (Z_to_bv 64 FF_DESCR); CB 16 hj; C4 lv; CB 12 j1; C4 tav; CB 12 j2; C8 bmv; CB 48 j3]
    with ([C8 (Z_to_bv 64 FF_MAGIC); C8 (Z_to_bv 64 FF_DESCR); CB 16 hj] ++ C4 lv :: [CB 12 j1; C4 tav; CB 12 j2; C8 bmv; CB 48 j3]) in FFC.
  pose proof (rw_cells_head m _ _ _ (rw_cells_skip m f _ _ FFC)) as C. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in C. exact C.
Qed.
Lemma ff_cell48 : forall (m : word -> option byte) f hj lv j1 tav j2 bmv j3, rw_cells asegs m f (ff_cells hj lv j1 tav j2 bmv j3) -> rw_cells asegs m (f + 48) [C4 tav].
Proof.
  intros m f hj lv j1 tav j2 bmv j3 FFC. unfold ff_cells in FFC.
  change [C8 (Z_to_bv 64 FF_MAGIC); C8 (Z_to_bv 64 FF_DESCR); CB 16 hj; C4 lv; CB 12 j1; C4 tav; CB 12 j2; C8 bmv; CB 48 j3]
    with ([C8 (Z_to_bv 64 FF_MAGIC); C8 (Z_to_bv 64 FF_DESCR); CB 16 hj; C4 lv; CB 12 j1] ++ C4 tav :: [CB 12 j2; C8 bmv; CB 48 j3]) in FFC.
  pose proof (rw_cells_head m _ _ _ (rw_cells_skip m f _ _ FFC)) as C. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in C. exact C.
Qed.
(* [comment removed for export] *)
Lemma rw_CB_of_bytes' : forall (m : word -> option byte) a bs, bytes_at asegs m a bs -> wr_at asegs m a (Z.of_nat (length bs)) -> rw_cells asegs m a [CB (length bs) bs].
Proof.
  intros m a bs BA WR. split.
  - split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact BA].
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact WR.
Qed.

(* [comment removed for export] *)
Section CInik.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Variable libenv : mem -> list (Z * Z) -> Z -> Prop.
Variable libenv_fp : list (Z * Z) -> Z -> Prop.
Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a -> (in_ranges LIB_W a /\ client_static a /\ ~ cl_cell a) \/ in_live LBL a.
Variables FZ_SITES FZ_CALLS : list (Z * Z).

Local Notation pem_entry := (pem_entry RT).
Local Notation pem_com := (pem_com RT libenv FZ_SITES FZ_CALLS).

(* [comment removed for export] *)
Lemma com_leaf : forall (en : pem_entry) Σ (m m' : mem) off crem lrem cur Wall,
  pem_com en Σ m off crem lrem cur -> munch Wall m m' -> wmono asegs m m' -> mem_inv asegs m' -> stk asegs m' (e_lo RT en) (e_sp1 RT en) ->
  (forall iv, In iv Wall -> seg_ok RT en cur iv \/ (e_sp1 RT en - PEM_CALLEE_STACK <= fst iv /\ snd iv <= e_sp1 RT en)) ->
  pem_com en Σ m' off crem lrem cur.
Proof using AF AFP libenv_agree libenv_fp_where.
  intros en Σ m m' off crem lrem cur Wall COM MU WM MI' ST' HW.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  assert (ELV : incl_live (e_live RT en) (rt_live RT Σ)) by (intros e0 He0; apply (Permutation_in _ (Permutation_sym PERM)); apply in_or_app; right; exact He0).
  assert (AGo : forall (P : Z -> Prop), (forall x iv, P x -> In iv Wall -> ~ (fst iv <= x < snd iv)) -> agree_on P m m').
  { intros P HP a Ha. apply MU. apply outside_intro. intros iv Hiv. exact (HP _ _ Ha Hiv). }
  assert (BF : forall iv a, In iv Wall -> fst iv <= a < snd iv ->
       aclient (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en - PEM_CALLEE_STACK) a /\ ~ aclient (e_live RT en) (e_frames RT en) (e_PL RT en) a
    /\ ~ client_static a /\ ~ (0x7fff8000 <= a < 0x10007fff8000) /\ a < e_PL RT en - 104 /\ (forall p n, In (p, n) (e_live RT en) -> ~ (p <= a < p + n))).
  { intros iv a Hiv Ha. destruct (HW iv Hiv) as [OK | [S1 S2]].
    - pose proof (seg_byte_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem cur iv a COM OK Ha) as (B1 & B2). split; [| exact B2].
      exact (aclient_mono _ _ _ _ _ (e_sp1 RT en - PEM_CALLEE_STACK) _ B1 (fun e He => He) (fun e He => He) ltac:(unfold PEM_CALLEE_STACK; clear; lia)).
    - (* [comment removed for export] *)
      assert (R : e_sp1 RT en - PEM_CALLEE_STACK <= a < e_sp1 RT en) by (clear - Ha S1 S2; lia).
      assert (RL : e_lo RT en + RT_STACK <= a) by (clear - R LOR; lia). clear S1 S2 Ha. unfold e_sp1 in *.
      split; [left; clear - R PD TOP; unfold USTACK_TOP, PEM_CALLEE_STACK in *; lia|].
      split. { intros AC. destruct AC as [H|[H|[H|[H|H]]]].
        + clear - H R PD. unfold PEM_CALLEE_STACK in *. lia.
        + pose proof (client_static_range a H). clear - H0 RL HLOS. unfold SEGTOP_A, RT_STACK in *. lia.
        + destruct H as (p & n & Hin & Hp). pose proof (af_live_range RT AF Σ m p n ART0 (ELV _ Hin)) as (_ & X & _). clear - X Hp RL LOW. unfold RT_STACK in *. lia.
        + destruct H as (f & k & Hin & Hf). assert (Hin' : In (f, k) (rt_frames RT Σ)) by (rewrite FRS; right; exact Hin).
          pose proof (af_frames_range RT AF Σ m f k ART0 Hin') as (_ & X & _). pose proof (Z.shiftl_nonneg 64 (Z.of_nat k)). clear - X H Hf RL LOW. unfold fs_size, RT_STACK in *. lia.
        + destruct H as (f & k & Hin & Hf). assert (Hin' : In (f, k) (rt_frames RT Σ)) by (rewrite FRS; right; exact Hin).
          pose proof (af_frames_range RT AF Σ m f k ART0 Hin') as (X0 & X & _). pose proof (Z.shiftl_nonneg 64 (Z.of_nat k)).
          pose proof (af_sp0_range RT AF Σ m ART0). clear - X0 X H Hf RL LOW HLOS H0. unfold shad, SHB, fs_size, STACK_WIN, RT_STACK, USTACK_TOP in *. Z.div_mod_to_equations. lia. }
      split; [intros H; pose proof (client_static_range a H); clear - H0 RL HLOS; unfold SEGTOP_A, RT_STACK in *; lia|].
      split; [clear - RL HLOS; unfold RT_STACK in *; lia|]. split; [clear - R PD; unfold PEM_CALLEE_STACK in *; lia|].
      intros p n Hin Hp. pose proof (af_live_range RT AF Σ m p n ART0 (ELV _ Hin)) as (_ & X & _). clear - X Hp RL LOW. unfold RT_STACK in *. lia. }
  split. { apply (af_frame RT AF Σ m m' (e_sp1 RT en - PEM_CALLEE_STACK) ART0); [clear - LOW LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia| | exact WM].
           intros a NA. apply MU. apply outside_intro. intros iv Hiv R. exact (NA (proj1 (BF iv _ Hiv R))). }
  split; [exact MI'|]. split; [exact ST'|]. split; [exact PD|]. split; [exact PDM|]. split; [exact TOP|]. split; [exact LOW|]. split; [exact LOR|]. split; [exact HLOS|].
  split. { eapply cl_env_seg; [exact CLE| exact MU|]. intros x Hx. apply outside_intro. intros iv Hiv R. exact (proj1 (proj2 (proj2 (BF iv x Hiv R))) (cl_cell_static _ Hx)). }
  split. { eapply sec_off_agree; [exact SEC|]. intros a Ea. apply MU. apply outside_intro. intros iv Hiv R.
           apply (proj1 (proj2 (proj2 (BF iv _ Hiv R)))). apply client_static_intro. rewrite Ea. unfold SEC_INIT. lia. }
  split. { eapply libenv_agree; [exact LE|]. apply AGo. intros x iv Hx Hiv R. destruct (libenv_fp_where _ _ Hx) as [(_ & CS & _)|(p & n & Hin & Hp)].
           - exact (proj1 (proj2 (proj2 (BF iv x Hiv R))) CS).
           - exact (proj2 (proj2 (proj2 (proj2 (proj2 (BF iv x Hiv R))))) p n (INCL _ Hin) Hp). }
  split; [exact INCL|]. split; [exact INE|]. split; [exact NLE|]. split; [exact NTL|].
  split. { eapply mbio_rep_agree; [exact MB|]. apply AGo. intros x iv (e & He & Hx) Hiv R. destruct e as [p n].
           exact (proj2 (proj2 (proj2 (proj2 (proj2 (BF iv x Hiv R))))) p n (KLV _ He) Hx). }
  split; [exact OFF|]. split; [exact BLT|]. split; [exact KLV|]. split; [exact PERM|]. split; [exact CFR|]. split; [exact ND|]. split; [exact LPOS|].
  split; [exact FRS|]. split; [exact FRN|]. split; [exact SP0|]. split; [exact CG|]. split; [exact LIV|]. split; [exact LR0|]. split; [exact CR|]. split; [exact CR0|]. split; [exact CRE|].
  split; [exact CGH|]. split; [exact CGS|]. split; [exact CTX|].
  split. { eapply uw_chain_agree; [exact UWC|]. apply AGo. intros x iv Hx Hiv R. cbv beta in Hx.
           pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (BF iv _ Hiv R)))))). unfold e_PL in *. lia. }
  split; [exact F0|]. split; [exact F64|]. split; [exact FTOP|]. split; [exact FSEG|]. split; [exact FSH|].
  split. { eapply rw_cells_agree; [exact FFS| | exact WM]. apply AGo. intros x iv Hx Hiv R. cbv beta in Hx.
           pose proof (proj1 (proj2 (proj2 (proj2 (BF iv x Hiv R))))) as NS. apply NS. unfold ff_shadow in Hx. cbn [cells_size csize Nat.add] in Hx.
           pose proof (af_sp0_range RT AF Σ m ART0). pose proof (af_sp0_win RT AF Σ m ART0). unfold shad, SHB, USTACK_TOP, STACK_WIN in *.
           clear - Hx F0 FTOP. Z.div_mod_to_equations. lia. }
  split. { eapply rw_cells_agree; [exact SAVED| | exact WM]. apply AGo. intros x iv Hx Hiv R. cbv beta in Hx. unfold pem_saved in Hx. cbn [cells_size csize Nat.add] in Hx.
           pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (BF iv x Hiv R)))))). lia. }
  split. { eapply pres_fp_trans; [exact PRES|]. intros a Ha Ho. apply MU. apply outside_intro. intros iv Hiv R. exact (proj1 (proj2 (BF iv _ Hiv R)) Ha). }
  split; [exact FLR|]. split; [exact NDO|]. split; [exact OUTS|]. split; [exact FDO| exact MST].
Qed.

(* [comment removed for export] *)
Lemma outside_mem : forall (W : list (Z * Z)) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi).
Proof.
  intros W x lo hi. induction W as [|[a b] W IH]; intros HO HI; [destruct HI|].
  cbn [outside] in HO. destruct HO as [H1 H2]. destruct HI as [E|HI]; [injection E as <- <-; exact H1| exact (IH H2 HI)].
Qed.

(* [comment removed for export] *)
Lemma out_byte_facts : forall (en : pem_entry) Σ (m : mem) off crem lrem cur P f k a,
  pem_com en Σ m off crem lrem cur -> In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] ->
  In (f, k) (e_frames RT en) -> f <= P -> P + 8 <= f + fs_size k - 8 -> P <= a < P + 8 ->
     aclient (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) a /\ In (P, P + 8) (pem_W RT en)
  /\ ~ client_static a /\ ~ (0x7fff8000 <= a < 0x10007fff8000) /\ a < e_PL RT en - 104
  /\ (forall p n, In (p, n) (rt_live RT Σ) -> ~ (p <= a < p + n)) /\ (a + 8 <= e_f RT en \/ e_f RT en + 128 <= a).
Proof using AF AFP.
  intros en Σ m off crem lrem cur P f k a COM HP HF F1 F2 Ha.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  assert (HF' : In (f, k) (rt_frames RT Σ)) by (rewrite FRS; right; exact HF).
  pose proof (af_frames_range RT AF Σ m f k ART0 HF') as (X0 & X1 & X2 & X3). pose proof (afp_frame_mem RT GOBJ AFP Σ m f k ART0 HF') as (Y1 & Y2).
  pose proof (Z.shiftl_nonneg 64 (Z.of_nat k)) as KN.
  split; [exact (acl_frame _ _ _ f k a HF' ltac:(clear - F1 F2 Ha; lia))|].
  split; [unfold pem_W; apply in_or_app; left; destruct HP as [<-|[<-|[<-|[<-|[]]]]]; cbn; tauto|].
  split; [intros H; pose proof (client_static_range a H); clear - H0 X2 F1 F2 Ha KN; unfold fs_size, SEGTOP_A in *; lia|].
  split; [clear - Y1 F1 F2 Ha KN; unfold fs_size in *; lia|].
  split; [clear - X1 F1 F2 Ha KN LOW LOR TOP PD; unfold e_sp1, fs_size, RT_STACK, PEM_CALLEE_STACK in *; lia|].
  split; [intros p n Hin Hp; destruct (X3 p n Hin) as [Q|Q]; clear - Q Hp F1 F2 Ha KN; unfold fs_size in *; lia|].
  pose proof (af_frames_disj RT AF Σ m (e_f RT en) 1%nat f k [] _ ART0 FRS ltac:(exact HF)) as D. change (fs_size 1) with 128 in D.
  clear - D F1 F2 Ha KN. unfold fs_size in *. lia.
Qed.

(* [comment removed for export] *)
Lemma out_sh0 : forall (en : pem_entry) Σ (m : mem) off crem lrem cur P f k,
  pem_com en Σ m off crem lrem cur -> In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] ->
  In (f, k) (e_frames RT en) -> f <= P -> P + 8 <= f + fs_size k - 8 -> bytes_at asegs (e_m RT en) (shad P) [z8] ->
  ro_cells asegs m (shad P) [C1 z8].
Proof using AF AFP.
  intros en Σ m off crem lrem cur P f k COM HP HF F1 F2 B0.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  assert (ELV : incl_live (e_live RT en) (rt_live RT Σ)) by (intros e0 He0; apply (Permutation_in _ (Permutation_sym PERM)); apply in_or_app; right; exact He0).
  assert (HF' : In (f, k) (rt_frames RT Σ)) by (rewrite FRS; right; exact HF).
  pose proof (af_frames_range RT AF Σ m f k ART0 HF') as (X0 & X1 & X2 & X3). pose proof (afp_frame_mem RT GOBJ AFP Σ m f k ART0 HF') as (Y1 & Y2).
  pose proof (Z.shiftl_nonneg 64 (Z.of_nat k)) as KN.
  assert (SR : 0x7fff8000 <= shad P < 0x10007fff8000) by (clear - X0 F1 F2 Y2 KN; unfold shad, SHB, fs_size in *; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  assert (OW : outside (pem_W RT en) (shad P)).
  { apply outside_intro. intros [lo hi] Hiv R. cbn [fst snd] in R. unfold pem_W in Hiv. apply in_app_iff in Hiv. destruct Hiv as [Hiv|Hiv].
    - assert (CASES : (exists Q, In Q [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] /\ lo = Q /\ hi = Q + 8) \/ (lo = e_E RT en /\ hi = e_E RT en + 904)).
      { destruct Hiv as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-;
          [left; eexists; split; [left; reflexivity| split; reflexivity]| left; eexists; split; [right; left; reflexivity| split; reflexivity]
          | left; eexists; split; [do 2 right; left; reflexivity| split; reflexivity]| left; eexists; split; [do 3 right; left; reflexivity| split; reflexivity]| right; split; reflexivity]. }
      destruct CASES as [(Q & HQ & -> & ->)|(-> & ->)].
      + pose proof (proj2 (proj1 (Forall_forall _ _) OUTS Q HQ)) as [[H1 H2]|(f' & k' & Hin & G1 & G2 & _)].
        * clear - H1 H2 R SR TOP LOR LOW HLOS PD. unfold e_sp1, USTACK_TOP, RT_STACK, PEM_CALLEE_STACK in *. lia.
        * assert (Hin' : In (f', k') (rt_frames RT Σ)) by (rewrite FRS; right; exact Hin).
          pose proof (afp_frame_mem RT GOBJ AFP Σ m f' k' ART0 Hin') as (Z1 & _). pose proof (Z.shiftl_nonneg 64 (Z.of_nat k')). clear - Z1 G1 G2 R SR H. unfold fs_size in *. lia.
      + pose proof (afp_live_mem RT GOBJ AFP Σ m (e_E RT en) 904 ART0 (ELV _ INE) ltac:(clear; lia)) as (Z1 & _). clear - Z1 R SR. lia.
    - apply in_app_iff in Hiv. destruct Hiv as [Hiv|Hiv].
      + unfold mbio_W in Hiv. apply in_map_iff in Hiv. destruct Hiv as ([p n] & E & Hin). cbn [fst snd] in E. injection E as <- <-.
        pose proof (ELV _ (KLV _ Hin)) as INp. pose proof (afp_live_mem RT GOBJ AFP Σ m p n ART0 INp ltac:(pose proof (LPOS _ INp); cbn in H; clear - H; lia)) as (Z1 & _). clear - Z1 R SR. lia.
      + unfold lib_W in Hiv. apply in_app_iff in Hiv. destruct Hiv as [Hiv|Hiv].
        * unfold LIB_W in Hiv. destruct Hiv as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; injection E as <- <-; clear - R SR; lia.
        * apply in_map_iff in Hiv. destruct Hiv as ([p n] & E & Hin). cbn [fst snd] in E. injection E as <- <-.
          pose proof (ELV _ (INCL _ Hin)) as INp. pose proof (afp_live_mem RT GOBJ AFP Σ m p n ART0 INp ltac:(pose proof (LPOS _ INp); cbn in H; clear - H; lia)) as (Z1 & _). clear - Z1 R SR. lia. }
  assert (B : bytes_at asegs m (shad P) [z8]).
  { apply (bytes_at_agree asegs (e_m RT en) m _ _ B0). intros a Ha. cbn [length] in Ha. assert (Ea : bv_unsigned a = shad P) by (clear - Ha; lia).
    apply PRES; rewrite Ea; [| exact OW]. right; right; right; right. exists f, k. split; [exact HF|].
    clear - F1 F2 X0 KN. unfold shad, fs_size in *. Z.div_mod_to_equations. lia. }
  unfold ro_cells, cells_at. cbn [cells_wf cells_bytes cbytes]. rewrite app_nil_r. split; [split; [reflexivity | exact I] | exact B].
Qed.

(* [comment removed for export] *)
Lemma com_out_store : forall (en : pem_entry) Σ (m m' : mem) off crem lrem cur P f k,
  pem_com en Σ m off crem lrem cur -> In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] ->
  In (f, k) (e_frames RT en) -> f <= P -> P + 8 <= f + fs_size k - 8 ->
  munch [(P, P + 8)] m m' -> wmono asegs m m' -> mem_inv asegs m' -> stk asegs m' (e_lo RT en) (e_sp1 RT en) ->
  pem_com en Σ m' off crem lrem cur.
Proof using AF AFP libenv_agree libenv_fp_where.
  intros en Σ m m' off crem lrem cur P f k COM HP HF F1 F2 MU WM MI' ST'.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  assert (ELV : incl_live (e_live RT en) (rt_live RT Σ)) by (intros e0 He0; apply (Permutation_in _ (Permutation_sym PERM)); apply in_or_app; right; exact He0).
  assert (BF : forall a, P <= a < P + 8 ->
       aclient (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) a /\ In (P, P + 8) (pem_W RT en)
    /\ ~ client_static a /\ ~ (0x7fff8000 <= a < 0x10007fff8000) /\ a < e_PL RT en - 104
    /\ (forall p n, In (p, n) (rt_live RT Σ) -> ~ (p <= a < p + n)) /\ (a + 8 <= e_f RT en \/ e_f RT en + 128 <= a))
    by (intros a Ha; exact (out_byte_facts en Σ m off crem lrem cur P f k a COM HP HF F1 F2 Ha)).
  assert (AGo : forall (Q : Z -> Prop), (forall x, Q x -> ~ (P <= x < P + 8)) -> agree_on Q m m').
  { intros Q HQ a Ha. apply MU. cbn. split; [exact (HQ _ Ha)| exact I]. }
  split. { apply (af_frame RT AF Σ m m' (e_sp1 RT en) ART0); [clear - LOW LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia| | exact WM].
           intros a NA. apply MU. cbn. split; [| exact I]. intros R. exact (NA (proj1 (BF _ R))). }
  split; [exact MI'|]. split; [exact ST'|]. split; [exact PD|]. split; [exact PDM|]. split; [exact TOP|]. split; [exact LOW|]. split; [exact LOR|]. split; [exact HLOS|].
  split. { eapply cl_env_seg; [exact CLE| exact MU|]. intros x Hx. cbn. split; [| exact I]. intros R. exact (proj1 (proj2 (proj2 (BF x R))) (cl_cell_static _ Hx)). }
  split. { eapply sec_off_agree; [exact SEC|]. intros a Ea. apply MU. cbn. split; [| exact I]. intros R.
           apply (proj1 (proj2 (proj2 (BF _ R)))). apply client_static_intro. rewrite Ea. unfold SEC_INIT. lia. }
  split. { eapply libenv_agree; [exact LE|]. apply AGo. intros x Hx R. destruct (libenv_fp_where _ _ Hx) as [(_ & CS & _)|(p & n & Hin & Hp)].
           - exact (proj1 (proj2 (proj2 (BF x R))) CS).
           - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (BF x R)))))) p n (ELV _ (INCL _ Hin)) Hp). }
  split; [exact INCL|]. split; [exact INE|]. split; [exact NLE|]. split; [exact NTL|].
  split. { eapply mbio_rep_agree; [exact MB|]. apply AGo. intros x (e & He & Hx) R. destruct e as [p n].
           exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (BF x R)))))) p n (ELV _ (KLV _ He)) Hx). }
  split; [exact OFF|]. split; [exact BLT|]. split; [exact KLV|]. split; [exact PERM|]. split; [exact CFR|]. split; [exact ND|]. split; [exact LPOS|].
  split; [exact FRS|]. split; [exact FRN|]. split; [exact SP0|]. split; [exact CG|]. split; [exact LIV|]. split; [exact LR0|]. split; [exact CR|]. split; [exact CR0|]. split; [exact CRE|].
  split; [exact CGH|]. split; [exact CGS|]. split; [exact CTX|].
  split. { eapply uw_chain_agree; [exact UWC|]. apply AGo. intros x Hx R. cbv beta in Hx. pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (BF _ R)))))). unfold e_PL in *. lia. }
  split; [exact F0|]. split; [exact F64|]. split; [exact FTOP|]. split; [exact FSEG|]. split; [exact FSH|].
  split. { eapply rw_cells_agree; [exact FFS| | exact WM]. apply AGo. intros x Hx R. cbv beta in Hx.
           pose proof (proj1 (proj2 (proj2 (proj2 (BF x R))))) as NS. apply NS. unfold ff_shadow in Hx. cbn [cells_size csize Nat.add] in Hx.
           pose proof (af_sp0_range RT AF Σ m ART0). pose proof (af_sp0_win RT AF Σ m ART0). unfold shad, SHB, USTACK_TOP, STACK_WIN in *.
           clear - Hx F0 FTOP. Z.div_mod_to_equations. lia. }
  split. { eapply rw_cells_agree; [exact SAVED| | exact WM]. apply AGo. intros x Hx R. cbv beta in Hx. unfold pem_saved in Hx. cbn [cells_size csize Nat.add] in Hx.
           pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (BF x R)))))). lia. }
  split. { eapply pres_fp_trans; [exact PRES|]. intros a Ha Ho. apply MU. cbn. split; [| exact I]. intros R. exact (outside_mem _ _ _ _ Ho (proj1 (proj2 (BF _ R))) R). }
  split; [exact FLR|]. split; [exact NDO|]. split; [exact OUTS|]. split; [exact FDO| exact MST].
Qed.

(* [comment removed for export] *)
Lemma mbio_repx_upd : forall Σ (m m' : mem) K BI BM blw blw' meth len max off d junk',
  ART RT Σ m -> mbio_repx (rt_live RT Σ) m K BI BM blw meth len max off -> k_d K = Some d ->
  (forall (e : Z * Z) (a : word), In e (mbio_ent K max) -> e <> (d, max) -> fst e <= bv_unsigned a < fst e + snd e -> ~ (BM <= bv_unsigned a < BM + 8) -> m' a = m a) ->
  rw_cells asegs m' BM [C8 blw'] -> length junk' = Z.to_nat max -> rw_cells asegs m' d [CB (Z.to_nat max) junk'] ->
  mbio_repx (rt_live RT Σ) m' K BI BM blw' meth len max off.
Proof using AF.
  intros Σ m m' K BI BM blw blw' meth len max off d junk' ART0 MB KD AG CBM LJ CD.
  destruct MB as (fl & rrw & numw & padw & nr & nw & EBI & EBM & INBI & BI16 & NDK & METH & HEAD & W1C & FLOK & TAILC & (rmw & INBB & BB16 & BBC & INBM & BM16 & INRP & RP16 & O1 & O2 & O3 & INNER)).
  rewrite KD in INNER. destruct INNER as (junk & IND & MPOS & BMC & RPC & LJ0 & DC). subst BI BM.
  (* [comment removed for export] *)
  pose proof NDK as NDK0. unfold mbio_blocks in NDK. rewrite KD in NDK. cbn [app] in NDK.
  pose proof (proj1 (List.NoDup_cons_iff _ _) NDK) as [N1 NDK2]. pose proof (proj1 (List.NoDup_cons_iff _ _) NDK2) as [N2 NDK3].
  pose proof (proj1 (List.NoDup_cons_iff _ _) NDK3) as [N3 NDK4]. pose proof (proj1 (List.NoDup_cons_iff _ _) NDK4) as [N4 _]. cbn [In] in N1, N2, N3, N4.
  assert (E1 : In (k_bi K, 128) (mbio_ent K max)) by (unfold mbio_ent; left; reflexivity).
  assert (E2 : In (k_bb K, 16) (mbio_ent K max)) by (unfold mbio_ent; right; left; reflexivity).
  assert (E3 : In (k_bm K, 32) (mbio_ent K max)) by (unfold mbio_ent; right; right; left; reflexivity).
  assert (E4 : In (k_rp K, 32) (mbio_ent K max)) by (unfold mbio_ent; right; right; right; left; reflexivity).
  (* [comment removed for export] *)
  assert (A1 : forall a : word, k_bi K <= bv_unsigned a < k_bi K + 128 -> m' a = m a).
  { intros a Ha. apply (AG (k_bi K, 128) a E1); [intros E; injection E as X Y; apply N1; right; right; right; left; exact (eq_sym X)| exact Ha|].
    destruct (live_ne_apart RT AF Σ m (k_bi K) 128 (k_bm K) 32 ART0 INBI INBM ltac:(intros E; injection E as X Y; apply N1; right; left; exact (eq_sym X))); lia. }
  assert (A2 : forall a : word, k_bb K <= bv_unsigned a < k_bb K + 16 -> m' a = m a).
  { intros a Ha. apply (AG (k_bb K, 16) a E2); [intros E; injection E as X Y; apply N2; right; right; left; exact (eq_sym X)| exact Ha|].
    destruct (live_ne_apart RT AF Σ m (k_bb K) 16 (k_bm K) 32 ART0 INBB INBM ltac:(intros E; injection E as X Y; apply N2; left; exact (eq_sym X))); lia. }
  assert (A4 : forall a : word, k_rp K <= bv_unsigned a < k_rp K + 32 -> m' a = m a).
  { intros a Ha. apply (AG (k_rp K, 32) a E4); [intros E; injection E as X Y; apply N4; left; exact (eq_sym X)| exact Ha|].
    destruct (live_ne_apart RT AF Σ m (k_rp K) 32 (k_bm K) 32 ART0 INRP INBM ltac:(intros E; injection E as X; apply N3; left; exact X)); lia. }
  assert (A3 : forall a : word, k_bm K + 8 <= bv_unsigned a < k_bm K + 32 -> m' a = m a).
  { intros a Ha. apply (AG (k_bm K, 32) a E3); [intros E; injection E as X Y; apply N3; right; left; exact (eq_sym X)| cbn [fst snd]; lia| lia]. }
  exists fl, rrw, numw, padw, nr, nw. split; [reflexivity|]. split; [reflexivity|]. split; [exact INBI|]. split; [exact BI16|]. split; [exact NDK0|]. split; [exact METH|].
  split; [eapply rw_cells_agree_nw; [exact HEAD|]; intros a Ha; apply A1; unfold bio_head in Ha; cbn [cells_size csize Nat.add] in Ha; lia|].
  split; [eapply rw_cells_agree_nw; [exact W1C|]; intros a Ha; apply A1; unfold bio_w1_cells in Ha; cbn [cells_size csize Nat.add] in Ha; lia|].
  split; [exact FLOK|].
  split; [eapply rw_cells_agree_nw; [exact TAILC|]; intros a Ha; apply A1; unfold bio_tail in Ha; cbn [cells_size csize Nat.add] in Ha; lia|].
  exists rmw. split; [exact INBB|]. split; [exact BB16|].
  split; [eapply rw_cells_agree_nw; [exact BBC|]; intros a Ha; apply A2; cbn [cells_size csize Nat.add] in Ha; lia|].
  split; [exact INBM|]. split; [exact BM16|]. split; [exact INRP|]. split; [exact RP16|]. split; [exact O1|]. split; [exact O2|]. split; [exact O3|].
  rewrite KD. exists junk'. split; [exact IND|]. split; [exact MPOS|].
  split.
  { change [C8 blw'; C8 (wz d); C8 (wz max); C8 (wz (msec meth))] with ([C8 blw'] ++ [C8 (wz d); C8 (wz max); C8 (wz (msec meth))]).
    apply (proj2 (rw_cells_app m' _ _ _)). split; [exact CBM|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
    eapply rw_cells_agree_nw; [exact (rw_cells_skip m (k_bm K) [C8 blw] _ BMC)|]. intros a Ha. apply A3. cbn [cells_size csize Nat.add] in Ha. lia. }
  split; [eapply rw_cells_agree_nw; [exact RPC|]; intros a Ha; apply A4; unfold readp_cells in Ha; cbn [cells_size csize Nat.add] in Ha; lia|].
  split; [exact LJ| exact CD].
Qed.
End CInik.
