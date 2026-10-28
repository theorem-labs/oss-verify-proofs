(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Sj_num_walk Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit D_libiface Sj_akit Sj_acps Sj_hkit Atp_fzwA Atp_pidiA Atp_defsA Pj_defsA Pj_os_defsA El_defsA Drt_hdefsA Drt_lftoi1A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma drt_walkG_err : forall (usp sp' f d n : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word) (r : word) (j20 : list byte) F fc (m : mem),
  0 < f -> f + 512 < 2^63 -> 0 <= sp' -> sp' + 40 < 2^63 -> 1 <= bv_unsigned r < 64 ->
  rw_cells bsegs m (sp' + 24) (res_cellsA (f + 56) r j20) -> mem_inv bsegs m ->
  evt bsegs (eq (lf_regs e_pdtor (wz DRT_PDRET_A) sp' gp t0 t1 t2 usp (wz (f + 32)) (wz 64) a2 a3 a4 a5 a6 a7 f (wz n) (wz d) (wz (f + 56)) s9 s10 s11 t3 t4 t5 t6 F fc m))
    (lf_regs DRT_PIDRET_A x1 sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f (wz n) (wz d) (wz (f + 56)) s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH SP0 SPH RR RC MI. unfold lf_regs, e_pdtor, res_cellsA, DRT_PIDRET_A, DRT_PDRET_A, TPV_A in *.
  assert (NZ : bv_eqb r (wz 0) = false).
  { destruct (bv_eqb r (wz 0)) eqn:E; [| reflexivity]. exfalso. apply bv_eqb_eq in E. subst r. rewrite unsigned_lit in RR by lia. lia. }
  rewrite NZ in RC.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [C4 r; CB 4 j20] [16]%nat) in RC; [| reflexivity]. cbn [mk_CB_cells app] in RC.
  assert (ER : r = wz (bv_unsigned r)) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ER in RC.
  zstep. zstep. zstep. if_cases KU; zify_cond KU; [exfalso; try rewrite ER in KU; rewrite ?sx32_small in KU by lia; rewrite ?unsigned_lit in KU by lia; lia|].
  zstep. if_cases K; zify_cond K; [| exfalso; rewrite ER in K; rewrite sx32_small in K by lia; rewrite unsigned_lit in K by lia; lia].
  zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma drt_walkG_ok : forall (usp sp' f d n : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word) (j20 : list byte) F fc (m : mem),
  0 < f -> f + 512 < 2^63 -> 0 <= sp' -> sp' + 40 < 2^63 ->
  rw_cells bsegs m (sp' + 24) (res_cellsA (f + 56) (wz 0) j20) -> mem_inv bsegs m ->
  evt bsegs (eq (lf_regs DRT_OKARM_A x1 sp' gp t0 t1 t2 usp (wz 0) (wz 64) a2 a3 a4 a5 a6 a7 f (wz n) (wz d) (wz (f + 56)) s9 s10 s11 t3 t4 t5 t6 F fc m))
    (lf_regs DRT_PIDRET_A x1 sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f (wz n) (wz d) (wz (f + 56)) s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH SP0 SPH RC MI. unfold lf_regs, res_cellsA, DRT_PIDRET_A, DRT_OKARM_A, TPV_A in *.
  rewrite bv_eqb_refl in RC.
  zstep. zstep. zstep. if_cases KU; zify_cond KU; [exfalso; rewrite ?sx32_small in KU by lia; rewrite ?unsigned_lit in KU by lia; lia|].
  zstep. if_cases K; zify_cond K; [exfalso; rewrite sx32_small in K by lia; rewrite unsigned_lit in K by lia; lia|].
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma cells_bytes_map_C1 : forall l : list byte, cells_bytes (map C1 l) = l.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [map cells_bytes cbytes app]. rewrite IH. reflexivity. Qed.
Lemma drt_sh_os : forall (m : mem) (f : Z) (par : Z), f mod 8 = 0 -> rw_cells bsegs m (shad f) (map C1 (drt_sh par 0)) -> bytes_at bsegs m (shad (f + 144)) (repeat z8 36).
Proof.
  intros m f par F8 H. pose proof (rw_cells_bytes_at bsegs m (shad f) _ H) as X. rewrite cells_bytes_map_C1 in X. unfold drt_sh in X.
  lazymatch type of X with bytes_at _ _ _ ?l => pose proof (bytes_at_skipn m (shad f) l 18 X ltac:(cbn; lia)) as Y end.
  cbn [skipn app repeat] in Y. apply (bytes_at_firstn m _ _ 36) in Y. cbn [firstn app repeat] in Y.
  replace (shad (f + 144)) with (shad f + Z.of_nat 18) by (unfold shad; Z.div_mod_to_equations; lia). exact Y.
Qed.

Lemma drt_sh_doc : forall (m : mem) (f : Z) (os : Z), f mod 8 = 0 -> rw_cells bsegs m (shad f) (map C1 (drt_sh 0 os)) -> bytes_at bsegs m (shad (f + 56)) [z8; z8].
Proof.
  intros m f os F8 H. pose proof (rw_cells_bytes_at bsegs m (shad f) _ H) as X. rewrite cells_bytes_map_C1 in X. unfold drt_sh in X.
  lazymatch type of X with bytes_at _ _ _ ?l => pose proof (bytes_at_skipn m (shad f) l 7 X ltac:(cbn; lia)) as Y end.
  cbn [skipn app repeat] in Y. apply (bytes_at_firstn m _ _ 2) in Y. cbn [firstn app repeat] in Y.
  replace (shad (f + 56)) with (shad f + Z.of_nat 7) by (unfold shad; Z.div_mod_to_equations; lia). exact Y.
Qed.
Lemma drt_sh_parser : forall (m : mem) (f : Z) (os : Z), f mod 8 = 0 -> rw_cells bsegs m (shad f) (map C1 (drt_sh 0 os)) -> bytes_at bsegs m (shad (f + 32)) (repeat z8 10).
Proof.
  intros m f os F8 H. pose proof (rw_cells_bytes_at bsegs m (shad f) _ H) as X. rewrite cells_bytes_map_C1 in X. unfold drt_sh in X.
  lazymatch type of X with bytes_at _ _ _ ?l => pose proof (bytes_at_skipn m (shad f) l 4 X ltac:(cbn; lia)) as Y end.
  cbn [skipn app repeat] in Y. apply (bytes_at_firstn m _ _ 10) in Y. cbn [firstn app repeat] in Y.
  replace (shad (f + 32)) with (shad f + Z.of_nat 4) by (unfold shad; Z.div_mod_to_equations; lia). exact Y.
Qed.

Lemma drt_walkO1 : forall (usp sp' f : Z) (ra gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s9 s10 s11 t3 t4 t5 t6 : word) (j20 : list byte) F fc (m : mem),
  0 < f -> f + 512 < 2^63 -> 0 <= shad f -> shad f + 64 < 2^63 -> SEGTOP_A <= sp' -> sp' + 48 < 2^63 ->
  (sp' + 48 <= shad f \/ shad f + 64 <= sp') ->
  rw_cells bsegs m (shad f) (map C1 drt_sh_pro) -> rw_cells bsegs m (sp' + 24) (res_cellsA (f + 56) (wz 0) j20) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = lf_regs PJ_OS_CTOR_A (wz DRT_CTORRET_A) sp' gp t0 t1 t2 usp (wz (f + 144)) a1 a2 a3 a4 a5 a6 a7 f (wz (f + 144)) (wz (f + 56)) (wz (f + 56)) s9 s10 s11 t3 t4 t5 t6 F fc m1
      /\ munch [(shad f + 18, shad f + 54)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (shad f) (map C1 drt_sh_ok))
    (lf_regs DRT_OKARM_A ra sp' gp t0 t1 t2 usp (wz 0) a1 a2 a3 a4 a5 a6 a7 f s5 s6 (wz (f + 56)) s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH SH0 SHH GLO SPH APART FS RC MI.
  unfold lf_regs, res_cellsA, drt_sh_pro, drt_sh_ok, drt_sh, DRT_OKARM_A, DRT_CTORRET_A, PJ_OS_CTOR_A, TPV_A, SEGTOP_A, shad, SHB in *. cbn [map app repeat] in *.
  rewrite bv_eqb_refl in RC.
  pose proof (munch_refl [(f / 8 + 2147450880 + 18, f / 8 + 2147450880 + 54)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (wz f) = f) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (wz (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (wz sp') = sp') by (apply unsigned_lit; lia).
  zstep. step.
  do 36 ls.
  zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. eassumption.
Qed.

Lemma drt_walkO2 : forall (usp sp' f : Z) (gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 512 < 2^63 -> f mod 8 = 0 -> mem_inv bsegs m ->
  evt bsegs (eq (lf_regs EL_DUMP_A (wz EL_DUMPRET_A) sp' gp t0 t1 t2 usp (wz (f + 56)) (wz (f + 144 + 128)) a2 a3 a4 a5 a6 a7 f (wz (f + 144)) (wz (f + 56)) (wz (f + 272)) s9 s10 s11 t3 t4 t5 t6 F fc m))
    (lf_regs DRT_CTORRET_A (wz DRT_CTORRET_A) sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f (wz (f + 144)) (wz (f + 56)) s7 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH F8 MI. unfold lf_regs, EL_DUMP_A, EL_DUMPRET_A, DRT_CTORRET_A, TPV_A in *.
  assert (E5 : bv_unsigned (wz (f + 144)) = f + 144) by (apply unsigned_lit; lia).
  assert (L7 : Z.land (f + 56) 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia).
  step. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. clear K1.
  zstep. step. rewrite L7. if_false.
  zstep. zstep. zstep. zstep. apply evt_done. cbv delta [mkR]. replace (f + 272) with (f + 144 + 128) by lia. reflexivity.
Qed.

Lemma drt_walkR1 : forall (usp sp' f : Z) (gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word) (pb pp ep : word) (fill : Z) (dum j148 j284 : list byte) F fc (m : mem),
  0 < f -> f + 512 < 2^63 ->
  rw_cells bsegs m (f + 144) (os_cellsA (f + 144) pb pp ep fill dum j148 j284) -> ro_cells bsegs m PJ_GOT_VT_A [C8 (wz PJ_SB_BVT_A); C8 (wz PJ_IOS_BVT_A)] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a1' : word),
      ms = lf_regs PJ_LOC_DTOR_A (wz DRT_LOCRET_A) sp' gp t0 t1 t2 usp (wz (f + 144 + 8)) a1' a2 a3 a4 a5 a6 a7 f (wz (f + 144)) (wz (f + 56)) (wz (f + 272)) s9 s10 s11 t3 t4 t5 t6 F fc m1
      /\ munch [(f + 144, f + 152)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (f + 144) (C8 (wz (PJ_SB_BVT_A + 16)) :: tl (os_cellsA (f + 144) pb pp ep fill dum j148 j284)))
    (lf_regs EL_DUMPRET_A (wz EL_DUMPRET_A) sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f (wz (f + 144)) (wz (f + 56)) (wz (f + 272)) s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH FO GOT MI.
  unfold lf_regs, EL_DUMPRET_A, DRT_LOCRET_A, PJ_LOC_DTOR_A, PJ_GOT_VT_A, TPV_A in *. unfold os_cellsA, sb_cellsA, ios_cellsA in *. cbn [app tl] in *.
  pose proof (munch_refl [(f + 144, f + 152)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EO : bv_unsigned (wz (f + 144)) = f + 144) by (apply unsigned_lit; lia).

  zstep. zstep. zstep. zstep. zstep. zstep.

  zstep. step. zstep. lstep. astep. zstep.
  apply evt_done. eexists _, _. split; [cbv delta [mkR]; replace (f + 144 + 8) with (f + 152) by lia; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. eassumption.
Qed.

Lemma drt_walkR2 : forall (usp sp' f : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 512 < 2^63 -> mem_inv bsegs m ->
  evt bsegs (eq (lf_regs PJ_IOS_DTOR_A (wz DRT_IOSRET_A) sp' gp t0 t1 t2 usp (wz (f + 144 + 136)) a1 a2 a3 a4 a5 a6 a7 f (wz (f + 144)) (wz (f + 56)) (wz (f + 272)) s9 s10 s11 t3 t4 t5 t6 F fc m))
    (lf_regs DRT_LOCRET_A ra sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f (wz (f + 144)) (wz (f + 56)) (wz (f + 272)) s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH MI. unfold lf_regs, PJ_IOS_DTOR_A, DRT_LOCRET_A, DRT_IOSRET_A, TPV_A in *.
  assert (EO : bv_unsigned (wz (f + 144)) = f + 144) by (apply unsigned_lit; lia).
  zstep. zstep. replace (f + 144 + 136) with (f + 280) by lia. apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma drt_walkR3 : forall (usp sp' f lo : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 512 <= lo -> shad f + 64 <= lo -> 0 <= shad f -> (f + 512 <= shad f \/ shad f + 64 <= f) -> lo < 2^63 ->
  rw_cells bsegs m (shad f) (map C1 drt_sh_ok) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = lf_regs DRT_JOIN_A ra sp' gp t0 t1 t2 usp (wz (-8)) a1 a2 a3 a4 a5 a6 a7 f (wz (f + 144)) (wz (f + 56)) (wz (f + 272)) s9 s10 s11 t3 t4 t5 t6 F fc m1
      /\ munch [(shad f + 18, shad f + 54)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (shad f) (map C1 drt_sh_pro))
    (lf_regs DRT_IOSRET_A ra sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f (wz (f + 144)) (wz (f + 56)) (wz (f + 272)) s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FLO SLO SH0 SEP LOH FS MI.
  unfold lf_regs, drt_sh_ok, drt_sh_pro, drt_sh, DRT_IOSRET_A, DRT_JOIN_A, TPV_A, shad, SHB in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(f / 8 + 2147450880 + 18, f / 8 + 2147450880 + 54)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (wz f) = f) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (wz (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  zstep. do 36 ls.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. eassumption.
Qed.

Lemma drt_walkJ : forall (usp sp' f : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 512 < 2^63 ->
  evt bsegs (eq (lf_regs e_pdtor (wz DRT_PDRET_A) sp' gp t0 t1 t2 usp (wz (f + 32)) a1 a2 a3 a4 a5 a6 a7 f s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 F fc m))
    (lf_regs DRT_JOIN_A x1 sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH. unfold lf_regs, e_pdtor, DRT_JOIN_A, DRT_PDRET_A, TPV_A in *.
  zstep. zstep. apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma drt_walkX1 : forall (usp sp' f lo : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) (h3 : list byte) F fc (m : mem),
  0 < f -> f + 512 <= lo -> shad f + 64 <= lo -> 0 <= shad f -> (f + 512 <= shad f \/ shad f + 64 <= f) -> lo < 2^63 ->
  rw_cells bsegs m f (fz_hdr (C8 (wz DRT_MAGIC0)) (C8 (wz DRT_HDR_DESC_A)) (C8 (wz e_fuzz)) h3) -> rw_cells bsegs m (shad f) (map C1 drt_sh_pro) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem),
      ms = lf_regs (e_set_shadow 245) (wz DRT_SSRET_A) sp' gp t0 t1 t2 usp (wz (shad f)) (wz 64) a2 a3 a4 a5 a6 a7 f s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 F fc m'
      /\ munch [(f, f + 8); (shad f + 4, shad f + 14)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' f (fz_hdr (C8 (wz DRT_MAGIC1)) (C8 (wz DRT_HDR_DESC_A)) (C8 (wz e_fuzz)) h3)
      /\ rw_cells bsegs m' (shad f) (map C1 drt_sh_x))
    (lf_regs DRT_PDRET_A ra sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FLO SLO SH0 SEP LOH FH FS MI.
  unfold lf_regs, fz_hdr, drt_sh_pro, drt_sh_x, drt_sh, e_set_shadow, e_fuzz, DRT_PDRET_A, DRT_SSRET_A, DRT_MAGIC0, DRT_MAGIC1, DRT_HDR_DESC_A, TPV_A, shad, SHB in *.
  cbn [map app repeat] in *.
  pose proof (munch_refl [(f, f + 8); (f / 8 + 2147450880 + 4, f / 8 + 2147450880 + 14)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (wz f) = f) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (wz (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  zstep. do 10 ls.
  zstep. zstep. ls.
  zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|].
  zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; eassumption.
Qed.

Lemma drt_walkX2 : forall (usp sp' f fl lo : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
    (xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 : word) (LC : list cell) F fc (m : mem),
  0 < f -> f + 512 <= lo -> 0 < fl -> fl + 1 <= lo ->
  0x6d5000 <= lo -> lo <= sp' -> cells_size LC = 48%nat -> sp' + 48 <= usp - 80 -> usp < 2^63 ->
  stk bsegs m lo sp' -> rw_cells bsegs m sp' LC -> stk bsegs m (sp' + 48) (usp - 80) ->
  rw_cells bsegs m (usp - 80) (drt_saved xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9) ->
  ro_cells bsegs m (f + 504) [C8 (wz fl)] -> rw_cells bsegs m fl [C1 (Z_to_bv 8 1)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem), ret_st xra (wz usp) gp (wz TPV_A) xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 s9 s10 s11 (wz 0) m' ms
      /\ ms_fcsr ms = fc /\ munch [(fl, fl + 1)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp /\ rw_cells bsegs m' fl [C1 (Z_to_bv 8 0)])
    (lf_regs DRT_SSRET_A ra sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FLO FL0 FLLO GLO LSP SZ LUSP SPH ST FRl STp FRs FW FLC MI.
  unfold lf_regs, drt_saved, DRT_SSRET_A, TPV_A in *.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (wz f) = f) by (apply unsigned_lit; lia).
  assert (EFL : bv_unsigned (wz fl) = fl) by (apply unsigned_lit; lia).
  assert (EUS : bv_unsigned (wz usp) = usp) by (apply unsigned_lit; lia).
  zstep. ls. zstep. zstep.
  replace (usp - 80) with (usp + -80) in FRs by lia.
  zstep. do 10 zstep. zstep.
  replace (usp + -80) with (usp - 80) in FRs by lia.
  pose proof (stk_release bsegs _ _ _ _ ST FRl ltac:(lia)) as ST1. rewrite SZ in ST1. change (Z.of_nat 48%nat) with 48 in ST1.
  pose proof (stk_merge bsegs _ _ _ _ ST1 STp ltac:(lia)) as ST2.
  pose proof (stk_release bsegs _ _ _ _ ST2 FRs ltac:(lia)) as ST3. cbn [cells_size csize Nat.add] in ST3.
  replace (usp - 80 + Z.of_nat 80) with usp in ST3 by lia.
  zstep.
  apply evt_done. eexists. split; [unfold ret_st; do 16 eexists; cbv delta [mkR]; reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST3| eassumption].
Qed.
