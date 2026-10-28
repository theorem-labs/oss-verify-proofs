(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_num_walk Sj_stage1_kit Pj_os_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Atp_fzwA Pj_lftoi1A Pj_rtkA Pj_defsA Pj_os_defsA Imp_hdefsA Imp_oss_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma imp_sh_len3 : forall a b c, cells_size (map C1 (imp_sh a b c)) = 156%nat.
Proof. intros. unfold imp_sh. rewrite !map_app, !cells_size_app. cbn. reflexivity. Qed.

Definition ok_walk1_S : Prop :=
  forall (S1 usp f szw dw : Z) (ra gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s6 s8 s9 s10 t3 t4 t5 t6 : word) (j4 j8 : list byte) (sa sc : Z) F fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> 0 <= shad f -> shad f + 156 < 2^63 -> (f + 2048 <= shad f \/ shad f + 156 <= f) ->
  0 <= S1 -> S1 + 336 < 2^63 -> f + 2048 <= S1 -> shad f + 156 <= S1 ->
  rw_cells bsegs m (f + 248) [C8 (wz (f + 192)); C8 (wz 1); CB 4 j4; CB 4 j8] ->
  rw_cells bsegs m (S1 + 64) (imp_locals f szw dw) ->
  rw_cells bsegs m (shad f) (map C1 (imp_sh sa (-8) sc)) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = imp_regsA OSS_CTOR_A (wz 0xb51c4) S1 gp t0 t1 t2 usp (wz (f + 832)) a1 a2 a3 a4 a5 a6 a7 f s2 (wz (f + 248)) s6 (wz (f + 160)) s8 s9 s10 s9 t3 t4 t5 t6 F fc m1
      /\ munch [(f + 264, f + 268); (shad f + 104, shad f + 137)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (f + 248) [C8 (wz (f + 192)); C8 (wz 1); C4 (wz 0); CB 4 j8]
      /\ rw_cells bsegs m1 (shad f) (map C1 (imp_sh sa 0 sc)))
    (imp_regsA 0xb5134 ra S1 gp t0 t1 t2 usp (wz (f + 248)) a1 a2 a3 a4 a5 a6 a7 f s2 (wz (f + 248)) s6 (wz (f + 160)) s8 s9 s10 s9 t3 t4 t5 t6 F fc m).

Definition ok_walk2_S : Prop :=
  forall (S1 usp f szw dw : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s8 s9 s10 t3 t4 t5 t6 : word) (j8 : list byte) (sb sc : Z) F fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> 0 <= shad f -> shad f + 156 < 2^63 -> (f + 2048 <= shad f \/ shad f + 156 <= f) ->
  0 <= S1 -> S1 + 336 < 2^63 -> f + 2048 <= S1 -> shad f + 156 <= S1 ->
  rw_cells bsegs m (f + 248) [C8 (wz (f + 192)); C8 (wz 1); C4 (wz 0); CB 4 j8] ->
  rw_cells bsegs m (S1 + 64) (imp_locals f szw dw) ->
  rw_cells bsegs m (shad f) (map C1 (imp_sh (-8) sb sc)) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = imp_regsA IMP_AMEMSET_A (wz 0xb520c) S1 gp t0 t1 t2 usp (wz (f + 32)) (wz 0) (wz 64) a3 a4 a5 a6 a7 f (wz 1) (wz (f + 192)) s6 (wz (f + 160)) s8 (wz (f + 32)) s10 s9 t3 t4 t5 t6 F fc m1
      /\ munch [(shad f + 4, shad f + 15)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (shad f) (map C1 (imp_sh 0 sb sc)))
    (imp_regsA 0xb51c4 ra S1 gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s2 (wz (f + 248)) s6 (wz (f + 160)) s8 s9 s10 s9 t3 t4 t5 t6 F fc m).

Definition ok_walk3_S : Prop :=
  forall (S1 usp f szw dw : Z) (ra gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s10 t3 t4 t5 t6 : word) (j64 j72 j80 : list byte) F fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> 0 <= shad f -> shad f + 156 < 2^63 -> (f + 2048 <= shad f \/ shad f + 156 <= f) ->
  0 <= S1 -> S1 + 336 < 2^63 -> f + 2048 <= S1 -> shad f + 156 <= S1 ->
  shz m (f + 96) 8 ->
  rw_cells bsegs m (f + 96) [CB 8 j64; CB 8 j72; CB 8 j80] ->
  rw_cells bsegs m (S1 + 64) (imp_locals f szw dw) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = imp_regsA IMP_APPEND_A (wz 0xb5244) S1 gp t0 t1 t2 usp (wz (f + 32)) (wz (f + 192)) (wz 1) a3 a4 a5 a6 a7 f (wz 1) (wz (f + 192)) s6 (wz (f + 160)) s8 (wz (f + 32)) s10 s9 t3 t4 t5 t6 F fc m1
      /\ munch [(f + 96, f + 120)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (f + 96) [C8 (wz (f + 32)); C8 (wz 0); C8 (wz 64)])
    (imp_regsA 0xb520c ra S1 gp t0 t1 t2 usp (wz (f + 32)) a1 a2 a3 a4 a5 a6 a7 f (wz 1) (wz (f + 192)) s6 (wz (f + 160)) s8 (wz (f + 32)) s10 s9 t3 t4 t5 t6 F fc m).

Definition ok_walk4_S : Prop :=
  forall (S1 usp f szw dw buf size cap : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s10 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> 0 <= buf < 2^64 -> 0 <= size < 2^64 -> 0 <= cap < 2^64 ->
  0 <= S1 -> S1 + 336 < 2^63 -> f + 2048 <= S1 ->
  rw_cells bsegs m (f + 96) [C8 (wz buf); C8 (wz size); C8 (wz cap)] ->
  rw_cells bsegs m (S1 + 64) (imp_locals f szw dw) ->
  mem_inv bsegs m ->
  evt bsegs (eq (imp_regsA OSS_PUT_A (wz 0xb5254) S1 gp t0 t1 t2 usp (wz (f + 832)) (wz buf) (wz size) a3 a4 a5 a6 a7 f (wz 1) (wz (f + 192)) s6 (wz (f + 160)) s8 (wz (f + 32)) s10 s9 t3 t4 t5 t6 F fc m))
    (imp_regsA 0xb5244 ra S1 gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f (wz 1) (wz (f + 192)) s6 (wz (f + 160)) s8 (wz (f + 32)) s10 s9 t3 t4 t5 t6 F fc m).

Definition ok_walk5_S : Prop :=
  forall (S1 usp f szw dw buf size cap : Z) (gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s10 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> 0 < buf < 2^64 -> 0 <= size < 2^64 -> 0 <= cap < 2^64 ->
  0 <= S1 -> S1 + 336 < 2^63 -> f + 2048 <= S1 ->
  rw_cells bsegs m (f + 96) [C8 (wz buf); C8 (wz size); C8 (wz cap)] ->
  rw_cells bsegs m (S1 + 64) (imp_locals f szw dw) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms =>
      (buf = f + 32 /\ ms = imp_regsA 0xb526c (wz 0xb5254) S1 gp t0 t1 t2 usp (wz buf) a1 a2 a3 a4 a5 a6 a7 f (wz (f + 1168)) (wz SHB) s6 (wz (f + 160)) s8 (wz (f + 32)) s10 s9 t3 t4 t5 t6 F fc m)
      \/ (buf <> f + 32 /\ ms = imp_regsA OPDELARR_A (wz 0xb526c) S1 gp t0 t1 t2 usp (wz buf) a1 a2 a3 a4 a5 a6 a7 f (wz (f + 1168)) (wz SHB) s6 (wz (f + 160)) s8 (wz (f + 32)) s10 s9 t3 t4 t5 t6 F fc m))
    (imp_regsA 0xb5254 (wz 0xb5254) S1 gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f (wz 1) (wz (f + 192)) s6 (wz (f + 160)) s8 (wz (f + 32)) s10 s9 t3 t4 t5 t6 F fc m).

Definition ok_walk6_S : Prop :=
  forall (S1 usp f szw dw : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s10 t3 t4 t5 t6 : word) (os : Z) F fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> 0 <= shad f -> shad f + 156 < 2^63 -> (f + 2048 <= shad f \/ shad f + 156 <= f) ->
  0 <= S1 -> S1 + 336 < 2^63 -> f + 2048 <= S1 -> shad f + 156 <= S1 ->
  rw_cells bsegs m (S1 + 64) (imp_locals f szw dw) ->
  rw_cells bsegs m (shad f) (map C1 (imp_sh 0 os (-8))) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = imp_regsA OSS_STR_A (wz 0xb52b0) S1 gp t0 t1 t2 usp (wz (f + 1168)) (wz (f + 840)) a2 a3 a4 a5 a6 a7 f (wz (f + 1168)) (wz SHB) s6 (wz (f + 160)) s8 (wz (f + 32)) s10 s9 t3 t4 t5 t6 F fc m1
      /\ munch [(shad f + 4, shad f + 15); (shad f + 146, shad f + 149)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (shad f) (map C1 (imp_sh (-8) os 0)))
    (imp_regsA 0xb526c ra S1 gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f (wz (f + 1168)) (wz SHB) s6 (wz (f + 160)) s8 (wz (f + 32)) s10 s9 t3 t4 t5 t6 F fc m).

Lemma ok_walk1 : ok_walk1_S.
Proof.
  unfold ok_walk1_S. intros until m. intros F0 FH SH0 SHH SEP S0 S1H FS1 SHS1 EL LOC FS MI.
  unfold imp_regsA. remember (shad f) as fs eqn:EFS.
  unfold imp_sh, imp_locals, OSS_CTOR_A in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(f + 264, f + 268); (fs + 104, fs + 137)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 (f + 160)) = f + 160) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 fs) = fs) by (apply unsigned_lit; lia).
  replace (f + 832 + 16) with (f + 848) in LOC by lia. replace (f + 832 + 8) with (f + 840) in LOC by lia. replace (f + 832 + 112) with (f + 944) in LOC by lia.
  lstep.
  do 33 ls.
  zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact EL| exact FS].
Qed.

Lemma ok_walk2 : ok_walk2_S.
Proof.
  unfold ok_walk2_S. intros until m. intros F0 FH SH0 SHH SEP S0 S1H FS1 SHS1 EL LOC FS MI.
  unfold imp_regsA. remember (shad f) as fs eqn:EFS.
  unfold imp_sh, imp_locals, IMP_AMEMSET_A in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(fs + 4, fs + 15)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 (f + 160)) = f + 160) by (apply unsigned_lit; lia).
  assert (EE : bv_unsigned (Z_to_bv 64 (f + 248)) = f + 248) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 fs) = fs) by (apply unsigned_lit; lia).
  replace (f + 832 + 16) with (f + 848) in LOC by lia. replace (f + 832 + 8) with (f + 840) in LOC by lia. replace (f + 832 + 112) with (f + 944) in LOC by lia.
  zstep. zstep.
  do 11 ls.
  zstep. zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact FS].
Qed.

Lemma ok_walk3 : ok_walk3_S.
Proof.
  unfold ok_walk3_S. intros until m. intros F0 FH SH0 SHH SEP S0 S1H FS1 SHS1 SHZ SBW LOC MI.
  unfold imp_regsA, imp_locals, IMP_APPEND_A, SHB in *.
  pose proof (munch_refl [(f + 96, f + 120)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  assert (EF96 : bv_unsigned (Z_to_bv 64 (f + 96)) = f + 96) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply unsigned_lit; lia).
  replace (f + 832 + 16) with (f + 848) in LOC by lia. replace (f + 832 + 8) with (f + 840) in LOC by lia. replace (f + 832 + 112) with (f + 944) in LOC by lia.
  zstep. zstep. rewrite ?shr3_div. zstep. zstep.
  shz_pose SHZ (f + 96). zstep. shz_norm. zstep. if_false.
  lstep. lstep. zstep. lstep.
  zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact SBW].
Qed.

Lemma ok_walk4 : ok_walk4_S.
Proof.
  unfold ok_walk4_S. intros until m. intros F0 FH BR SR CR S0 S1H FS1 SC LOC MI.
  unfold imp_regsA, imp_locals, OSS_PUT_A in *.
  assert (E32 : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply unsigned_lit; lia).
  replace (f + 832 + 16) with (f + 848) in LOC by lia. replace (f + 832 + 8) with (f + 840) in LOC by lia. replace (f + 832 + 112) with (f + 944) in LOC by lia.
  zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma ok_walk5 : ok_walk5_S.
Proof.
  unfold ok_walk5_S. intros until m. intros F0 FH BR SR CR S0 S1H FS1 SC LOC MI.
  unfold imp_regsA, OPDELARR_A, imp_locals in *.
  assert (E32 : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply unsigned_lit; lia).
  replace (f + 832 + 16) with (f + 848) in LOC by lia. replace (f + 832 + 8) with (f + 840) in LOC by lia. replace (f + 832 + 112) with (f + 944) in LOC by lia.
  zstep. zstep. zstep.
  zstep. if_cases K; zify_cond K.
  - apply evt_done. left. split; [lia| cbv delta [mkR]; reflexivity].
  - zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
    zstep. apply evt_done. right. split; [lia| cbv delta [mkR]; reflexivity].
Qed.

Lemma ok_walk6 : ok_walk6_S.
Proof.
  unfold ok_walk6_S. intros until m. intros F0 FH SH0 SHH SEP S0 S1H FS1 SHS1 LOC FS MI.
  unfold imp_regsA. remember (shad f) as fs eqn:EFS.
  unfold imp_sh, imp_locals, OSS_STR_A in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(fs + 4, fs + 15); (fs + 146, fs + 149)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 fs) = fs) by (apply unsigned_lit; lia).
  do 11 ls.
  do 3 ls.
  replace (f + 832 + 16) with (f + 848) in LOC by lia. replace (f + 832 + 8) with (f + 840) in LOC by lia. replace (f + 832 + 112) with (f + 944) in LOC by lia.
  zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact FS].
Qed.

Definition ok_W1 (S1 : Z) : list (Z * Z) := [(S1 - 32, S1)].
Definition ok_Wt (f : Z) : list (Z * Z) := [(f + 1168, f + 1170)].
Definition ok_W8 (f : Z) : list (Z * Z) := [(shad f + 146, shad f + 149); (f + 832, f + 840); (f + 944, f + 952); (f + 840, f + 848)].

Definition mv_walk1_S : Prop :=
  forall (S1 usp f lo : Z) (gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s10 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> 0 <= shad f -> shad f + 156 < 2^63 -> (f + 2048 <= shad f \/ shad f + 156 <= f) ->
  0 <= S1 -> S1 + 336 < 2^63 -> f + 2048 <= S1 -> shad f + 156 <= S1 -> 0 <= lo -> lo <= S1 - 32 -> S1 <= usp < 2^63 ->
  0x6e0000 <= lo -> stk bsegs m lo S1 ->
  ro_cells bsegs m 0x17fec8 [C8 (wz 0x189978)] -> ro_cells bsegs m 0x189978 [C8 (wz SHB)] ->
  (forall m', munch (ok_W1 S1) m m' -> wmono bsegs m m' -> shz m' (f + 272) 8) ->
  rw_cells bsegs m (f + 272) [C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (wz 0xb5ad8) (wz (S1 - 32)) gp (wz TPV_A) t0 t1 t2 (wz (f + 272)) (wz (f + 1168)) (wz (f + 272)) (wz (f + 1168)) (wz 24) a3 a4 a5 a6 a7
                   (wz SHB) (wz (shad f)) (wz SHB) (wz (-8)) s6 (wz (f + 160)) s8 (wz (f + 32)) s10 s9 t3 t4 t5 t6)
              F (wz e_asan_memcpy) fc None m1 (seg_rom bsegs)
      /\ munch (ok_W1 S1) m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (S1 - 32)
      /\ rw_cells bsegs m1 (S1 - 32) [C8 (wz (f + 1168)); C8 (wz S1); C8 (wz usp); C8 (wz 0xb52bc)]
      /\ rw_cells bsegs m1 (f + 272) [C8 (wz 0); C8 (wz 0); C8 (wz 0)])
    (imp_regsA 0xb52b0 (wz 0xb52b0) S1 gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f (wz (f + 1168)) (wz SHB) s6 (wz (f + 160)) s8 (wz (f + 32)) s10 s9 t3 t4 t5 t6 F fc m).

Definition mv_walk2_S : Prop :=
  forall (S1 usp f lo : Z) (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s10 t3 t4 t5 t6 : word) (b0 b1 : byte) (jr : list byte) F fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> 0 <= shad f -> shad f + 156 < 2^63 -> (f + 2048 <= shad f \/ shad f + 156 <= f) ->
  0 <= S1 -> S1 + 336 < 2^63 -> f + 2048 <= S1 -> shad f + 156 <= S1 -> 0 <= lo -> lo <= S1 - 32 -> S1 <= usp < 2^63 ->
  stk bsegs m lo (S1 - 32) ->
  rw_cells bsegs m (S1 - 32) [C8 (wz (f + 1168)); C8 (wz S1); C8 (wz usp); C8 (wz 0xb52bc)] ->
  (forall m', munch (ok_Wt f) m m' -> wmono bsegs m m' -> shz m' (f + 1168) 8) ->
  rw_cells bsegs m (f + 1168) [C1 b0; C1 b1; CB 22 jr] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a0' a1' : word),
      ms = imp_regsA 0xb52dc (wz 0xb52bc) S1 gp t0 t1 t2 usp a0' a1' a2 a3 a4 a5 a6 a7 f (wz (f + 1168)) (wz SHB) s6 (wz (f + 160)) s8 s9 s10 s9 t3 t4 t5 t6 F fc m1
      /\ munch (ok_Wt f) m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo S1
      /\ rw_cells bsegs m1 (f + 1168) [C1 z8; C1 z8; CB 22 jr])
    (MS (mkR (wz 0xb5ad8) (wz (S1 - 32)) gp (wz TPV_A) t0 t1 t2 (wz (f + 272)) (wz (f + 1168)) (wz (f + 272)) a1 a2 a3 a4 a5 a6 a7
             (wz SHB) (wz (shad f)) (wz SHB) (wz (-8)) s6 (wz (f + 160)) s8 (wz (f + 32)) s10 s9 t3 t4 t5 t6)
        F (wz 0xb5ad8) fc None m (seg_rom bsegs)).

Definition ok_walk8_S : Prop :=
  forall (S1 usp f szw dw : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) (os : Z) (b72 : byte) F fc (m : mem),
  0x6d2000 <= f -> f + 2048 < 2^63 -> 0x7fff8000 <= shad f -> shad f + 156 < 2^63 -> (f + 2048 <= shad f \/ shad f + 156 <= f) -> f mod 64 = 0 ->
  0 <= S1 -> S1 + 336 < 2^63 -> f + 2048 <= S1 -> shad f + 156 <= S1 ->
  (forall m', munch (ok_W8 f) m m' -> wmono bsegs m m' -> shz m' OSS_VTT_A 40) ->
  (forall m', munch (ok_W8 f) m m' -> wmono bsegs m m' -> shz m' OSS_VBOFF_A 8) ->
  (forall m', munch (ok_W8 f) m m' -> wmono bsegs m m' -> shz m' (f + 832) 264) ->
  (forall m', munch (ok_W8 f) m m' -> wmono bsegs m m' -> ov_read_bytes bsegs m' (wa (f + 904)) 1 = Some [b72]) ->
  rw_cells bsegs m (f + 832) [C8 (wz OSS_OS_VPTR_A)] -> rw_cells bsegs m (f + 840) [C8 (wz OSS_SB_VPTR_A)] -> rw_cells bsegs m (f + 944) [C8 (wz OSS_IOS_VPTR_A)] ->
  rw_cells bsegs m (shad f) (map C1 (imp_sh (-8) os 0)) ->
  rw_cells bsegs m (S1 + 64) (imp_locals f szw dw) ->
  ro_cells bsegs m OSS_GOT_VT_A [C8 (wz OSS_VTT_A); C8 (wz (OSS_SB_VPTR_A - 16)); C8 (wz (OSS_SBB_VPTR_A - 16)); C8 (wz OSS_VBOFF_A)] ->
  ro_cells bsegs m OSS_VTT_A [C8 (wz OSS_OS_VPTR_A); C8 (wz OSS_OS_CVPTR_A); C8 (wz OSS_IOS_CVPTR_A); C8 (wz OSS_IOS_VPTR_A); C8 (wz 0x70)] ->
  ro_cells bsegs m OSS_VBOFF_A [C8 (wz 0x70)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a2' : word),
      ms = imp_regsA 0xb5370 ra S1 gp t0 t1 t2 usp (wz OSS_SB_VPTR_A) (wz (Z.land (bv_unsigned b72) 1)) a2' a3 a4 a5 a6 a7 f (wz OSS_VTT_A) (wz SHB) s6 (wz (f + 832)) s8 s9 s10 (wz 0x88) t3 t4 t5 t6 F fc m1
      /\ munch (ok_W8 f) m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (f + 832) [C8 (wz OSS_OS_VPTR_A)] /\ rw_cells bsegs m1 (f + 840) [C8 (wz OSS_SB_VPTR_A)] /\ rw_cells bsegs m1 (f + 944) [C8 (wz OSS_IOS_VPTR_A)]
      /\ rw_cells bsegs m1 (shad f) (map C1 (imp_sh (-8) os (-8))))
    (imp_regsA 0xb52dc ra S1 gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f (wz (f + 1168)) (wz SHB) s6 (wz (f + 160)) s8 s9 s10 s11 t3 t4 t5 t6 F fc m).

Definition ok_walk8b_S : Prop :=
  forall (S1 usp f capw capm dat : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s10 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> 0 <= capw < 2^64 -> 0 <= dat < 2^64 ->
  rw_cells bsegs m (f + 904) [C8 (wz capw); C8 (wz capm); C8 (wz dat)] ->
  mem_inv bsegs m ->
  evt bsegs (eq (imp_regsA OPDEL_A (wz 0xb5384) S1 gp t0 t1 t2 usp (wz dat) (wz (Z.land capw 18446744073709551614)) a2 a3 a4 a5 a6 a7 f (wz OSS_VTT_A) (wz SHB) s6 (wz (f + 832)) s8 s9 s10 (wz 0x88) t3 t4 t5 t6 F fc m))
    (imp_regsA 0xb5374 ra S1 gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f (wz OSS_VTT_A) (wz SHB) s6 (wz (f + 832)) s8 s9 s10 (wz 0x88) t3 t4 t5 t6 F fc m).

Definition ok_walk9_S : Prop :=
  forall (S1 usp f szw dw : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s10 t3 t4 t5 t6 sbv : word) F fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> 0 <= S1 -> S1 + 336 < 2^63 -> f + 2048 <= S1 ->
  rw_cells bsegs m (f + 840) [C8 sbv] ->
  rw_cells bsegs m (S1 + 64) (imp_locals f szw dw) ->
  ro_cells bsegs m OSS_GOT_VT_A [C8 (wz OSS_VTT_A); C8 (wz (OSS_SB_VPTR_A - 16)); C8 (wz (OSS_SBB_VPTR_A - 16)); C8 (wz OSS_VBOFF_A)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = imp_regsA IMP_LOC_DTOR_A (wz 0xb539c) S1 gp t0 t1 t2 usp (wz (f + 848)) a1 a2 a3 a4 a5 a6 a7 f (wz OSS_VTT_A) (wz SHB) s6 (wz (f + 832)) s8 s9 s10 (wz 0x88) t3 t4 t5 t6 F fc m1
      /\ munch [(f + 840, f + 848)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (f + 840) [C8 (wz OSS_SBB_VPTR_A)])
    (imp_regsA 0xb5384 ra S1 gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f (wz OSS_VTT_A) (wz SHB) s6 (wz (f + 832)) s8 s9 s10 (wz 0x88) t3 t4 t5 t6 F fc m).

Definition ok_walk10_S : Prop :=
  forall (S1 usp f szw dw : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s10 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> 0 <= S1 -> S1 + 336 < 2^63 ->
  rw_cells bsegs m (S1 + 64) (imp_locals f szw dw) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (a1' : word),
      ms = imp_regsA IMP_IOS_DTOR_A (wz 0xb53b0) S1 gp t0 t1 t2 usp (wz (f + 944)) a1' a2 a3 a4 a5 a6 a7 f (wz OSS_VTT_A) (wz SHB) s6 (wz (f + 832)) s8 s9 s10 (wz 0x88) t3 t4 t5 t6 F fc m)
    (imp_regsA 0xb539c ra S1 gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f (wz OSS_VTT_A) (wz SHB) s6 (wz (f + 832)) s8 s9 s10 (wz 0x88) t3 t4 t5 t6 F fc m).

Definition ok_walk11_S : Prop :=
  forall (S1 usp f : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (sb sc : Z) F fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> 0 <= shad f -> shad f + 156 < 2^63 ->
  rw_cells bsegs m (shad f) (map C1 (imp_sh sb 0 sc)) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = imp_regsA IMP_OKARM_END_A ra S1 gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
      /\ munch [(shad f + 104, shad f + 137)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (shad f) (map C1 (imp_sh sb (-8) sc)))
    (imp_regsA 0xb53b0 ra S1 gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).

Local Ltac step_to tgt :=
  let t := eval cbv in tgt in
  repeat lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
             tryif (assert_succeeds (assert (pc = t) by reflexivity)) then fail else ls
         end.
Local Ltac lit16 H := repeat match type of H with context [?a - 16] => is_Zlit a; let v := eval cbv in (a - 16) in change (a - 16) with v in H end.

Lemma ok_walk9 : ok_walk9_S.
Proof.
  unfold ok_walk9_S. intros until m. intros F0 FH S0 S1H FS1 VP LOC V1 MI.
  unfold imp_regsA, imp_locals, OSS_GOT_VT_A, OSS_VTT_A, OSS_SB_VPTR_A, OSS_SBB_VPTR_A, OSS_VBOFF_A in *.
  lit16 V1.
  pose proof (munch_refl [(f + 840, f + 848)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 (f + 832)) = f + 832) by (apply unsigned_lit; lia).
  replace (f + 832 + 16) with (f + 848) in LOC by lia. replace (f + 832 + 8) with (f + 840) in LOC by lia. replace (f + 832 + 112) with (f + 944) in LOC by lia.
  step_to IMP_LOC_DTOR_A.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption| eassumption].
Qed.

Lemma ok_walk10 : ok_walk10_S.
Proof.
  unfold ok_walk10_S. intros until m. intros F0 FH S0 S1H LOC MI.
  unfold imp_regsA, imp_locals in *.
  assert (ES : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply unsigned_lit; lia).
  replace (f + 832 + 16) with (f + 848) in LOC by lia. replace (f + 832 + 8) with (f + 840) in LOC by lia. replace (f + 832 + 112) with (f + 944) in LOC by lia.
  step_to IMP_IOS_DTOR_A.
  apply evt_done. eexists. cbv delta [mkR]. reflexivity.
Qed.

Lemma ok_walk11 : ok_walk11_S.
Proof.
  unfold ok_walk11_S. intros until m. intros F0 FH SH0 SHH FS MI.
  unfold imp_regsA in *.
  remember (shad f) as fs eqn:EFS.
  unfold imp_sh in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(fs + 104, fs + 137)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (ESH : bv_unsigned (Z_to_bv 64 fs) = fs) by (apply unsigned_lit; lia).
  step_to IMP_OKARM_END_A.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact FS].
Qed.

Lemma ok_walk8b : ok_walk8b_S.
Proof.
  unfold ok_walk8b_S. intros until m. intros F0 FH CW DT C MI.
  unfold imp_regsA in *.
  step_to OPDEL_A.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Local Ltac lit_addr H := match type of H with context [wa ?e] => let e' := eval cbv in e in change e with e' in H end.
Local Ltac to_if := repeat lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep end.
Local Ltac chkV2 SHZ a := let H := fresh "VRD" in shz_pose_with SHZ a H; lit_addr H; zstep; shz_norm; to_if; if_false; try clear H.

Lemma ok_walk8 : ok_walk8_S.
Proof.
  unfold ok_walk8_S. intros until m. intros F0 FH SH0 SHH SEP F64 S0 S1H FS1 SHS1 SHZV SHZB SHZ RD72 VP VSB VIOS FS LOC V1 V2 V3 MI.
  unfold imp_regsA, imp_locals, ok_W8 in *. remember (shad f) as fs eqn:EFS.
  unfold imp_sh, OSS_GOT_VT_A, OSS_VTT_A, OSS_SB_VPTR_A, OSS_SBB_VPTR_A, OSS_VBOFF_A, OSS_OS_VPTR_A, OSS_OS_CVPTR_A, OSS_IOS_CVPTR_A, OSS_IOS_VPTR_A, SHB in *.
  cbn [map app repeat] in *.
  lit16 V1.
  replace (f + 832 + 16) with (f + 848) in LOC by lia. replace (f + 832 + 8) with (f + 840) in LOC by lia. replace (f + 832 + 112) with (f + 944) in LOC by lia.
  pose proof (munch_refl [(fs + 146, fs + 149); (f + 832, f + 840); (f + 944, f + 952); (f + 840, f + 848)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 (f + 832)) = f + 832) by (apply unsigned_lit; lia).
  assert (EF2 : bv_unsigned (Z_to_bv 64 (f + 944)) = f + 944) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 fs) = fs) by (apply unsigned_lit; lia).
  zstep. zstep.
  do 3 ls.
  zstep. rewrite ?shr3_div. zstep. chkV2 SHZV 1562888.
  zstep. zstep. zstep. rewrite ?shr3_div.
  lstep.
  zstep. chkV2 SHZV 1562912.
  zstep. zstep. rewrite ?shr3_div. zstep. chkV2 SHZB 1562808.
  zstep. zstep.
  zstep. rewrite ?shr3_div. zstep.
  shz_pose SHZ (f + 944). replace (f + 832 + 112) with (f + 944) by lia. subst fs. zstep. shz_norm. zstep. if_false.
  remember (shad f) as fs eqn:EFS.
  zstep. lstep.
  zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (RD72 mx MU WM) as RD end.
  zstep.
  zstep. zstep.
  lstep.
  apply evt_done. eexists. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption| exact FS].
Qed.

Lemma mv_walk1 : mv_walk1_S.
Proof.
  unfold mv_walk1_S. intros until m. intros F0 FH SH0 SHH SEP S0 S1H FS1 SHS1 LO0 LO SPH LOB ST G1 G2 SHZ CL MI.
  unfold imp_regsA, ok_W1 in *.
  pose proof (munch_refl [(S1 - 32, S1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply unsigned_lit; lia).
  zstep. zstep. zstep. zstep.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  do 10 ls.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHZ mm MU' WM' (f + 272) ltac:(lia)) as RD0 end.
  unfold shad in RD0. rewrite ?shr3_div.
  zstep. shz_norm. to_if. if_false.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (rw_cells_C8_read1_g bsegs mx (f + 272) _ _ CL) as RB end.
  change (Z_to_bv 8 (bv_unsigned (wz 0))) with (Z_to_bv 8 0) in RB.
  zstep.
  ls. ls. if_true.
  do 4 ls.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FR| exact CL].
Qed.

Lemma mv_walk2 : mv_walk2_S.
Proof.
  unfold mv_walk2_S. intros until m. intros F0 FH SH0 SHH SEP S0 S1H FS1 SHS1 LO0 LO SPH ST FR SHZ CT MI.
  unfold imp_regsA, ok_Wt in *.
  pose proof (munch_refl [(f + 1168, f + 1170)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 (S1 - 32)) = S1 - 32) by (apply unsigned_lit; lia).
  pose proof (SHZ m MU WM (f + 1168) ltac:(lia)) as RD0. unfold shad in RD0.
  ls. ls. rewrite ?shr3_div.
  zstep. shz_norm. to_if. if_false.
  do 4 ls.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHZ mm MU' WM' (f + 1169) ltac:(lia)) as RD1 end.
  unfold shad in RD1. rewrite ?shr3_div.
  zstep. shz_norm. to_if. if_false.
  do 12 ls. if_true.
  release_frame FR ST S1.
  replace (S1 - 32 + 32) with S1 by lia.
  apply evt_done. do 3 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| eassumption].
Qed.
