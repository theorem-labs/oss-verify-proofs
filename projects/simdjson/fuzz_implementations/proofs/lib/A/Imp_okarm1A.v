(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP ZBridge.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_num_walk Sj_stage1_kit Pj_os_kit.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Layout Shadow RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Atp_fzwA
     Pj_lftoi1A Pj_defsA Pj_os_defsA Imp_hdefsA Imp_oss_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma imp_sh_len3 : forall a b c, cells_size (map C1 (imp_sh a b c)) = 156%nat.
Proof. intros. unfold imp_sh. rewrite !map_app, !cells_size_app. cbn. reflexivity. Qed.

Lemma ok_walk1 : forall (S1 usp f : Z) (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 s10 t3 t4 t5 t6 : word) (j4 j8 : list byte) (sa sc : Z) F fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> 0 <= shad f -> shad f + 156 < 2^63 -> (f + 2048 <= shad f \/ shad f + 156 <= f) ->
  rw_cells asegs m (f + 248) [C8 (wz (f + 192)); C8 (wz 1); CB 4 j4; CB 4 j8] ->
  rw_cells asegs m (shad f) (map C1 (imp_sh sa (-8) sc)) ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (wz 0xb5030) (wz S1) gp (wz TPV_A) t0 t1 t2 (wz usp) (wz S1) (wz (f + 832)) a1 a2 a3 a4 a5 a6 a7
                   (wz (-8)) (wz (shad f)) s4 s5 (wz (f + 160)) s7 (wz SHB) (wz (f + 832)) s10 (wz (f + 248)) t3 t4 t5 t6)
              F (wz 0xb50bc) fc None m1 (seg_rom asegs)
      /\ munch [(f + 264, f + 268); (shad f + 104, shad f + 137)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (f + 248) [C8 (wz (f + 192)); C8 (wz 1); C4 (wz 0); CB 4 j8]
      /\ rw_cells asegs m1 (shad f) (map C1 (imp_sh sa 0 sc)))
    (MS (mkR (wz 0xb5030) (wz S1) gp (wz TPV_A) t0 t1 t2 (wz usp) (wz S1) (wz (f + 248)) a1 a2 a3 a4 a5 a6 a7
             (wz (-8)) (wz (shad f)) s4 s5 (wz (f + 160)) s7 (wz SHB) (wz (f + 832)) s10 (wz (f + 248)) t3 t4 t5 t6)
        F (wz 0xb5030) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros F0 FH SH0 SHH SEP EL FS MI.
  remember (shad f) as fs eqn:EFS.
  unfold imp_sh in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(f + 264, f + 268); (fs + 104, fs + 137)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 (f + 160)) = f + 160) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 fs) = fs) by (apply unsigned_lit; lia).
  lstep.
  do 33 ls.
  zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact EL| exact FS].
Qed.

Lemma ok_walk2 : forall (S1 usp f szw dw : Z) (gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 s10 t3 t4 t5 t6 : word) (j8 : list byte) (sb sc : Z) F fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> 0 <= shad f -> shad f + 156 < 2^63 -> (f + 2048 <= shad f \/ shad f + 156 <= f) ->
  0 <= S1 -> S1 + 336 < 2^63 -> (f + 2048 <= S1) -> (shad f + 156 <= S1) ->
  rw_cells asegs m (f + 248) [C8 (wz (f + 192)); C8 (wz 1); C4 (wz 0); CB 4 j8] ->
  rw_cells asegs m (S1 + 80) (imp_locals f (shad f) szw dw) ->
  rw_cells asegs m (shad f) (map C1 (imp_sh (-8) sb sc)) ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (wz 0xb5108) (wz S1) gp (wz TPV_A) t0 t1 t2 (wz usp) (wz S1) (wz (f + 32)) (wz 0) (wz 64) a3 a4 a5 a6 a7
                   (wz (-8)) (wz (shad f)) (wz 1) (wz (f + 32)) (wz (f + 160)) s7 (wz SHB) (wz (f + 832)) s10 (wz (f + 192)) t3 t4 t5 t6)
              F (wz IMP_AMEMSET_A) fc None m1 (seg_rom asegs)
      /\ munch [(shad f + 4, shad f + 15)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (shad f) (map C1 (imp_sh 0 sb sc)))
    (MS (mkR (wz 0xb50c0) (wz S1) gp (wz TPV_A) t0 t1 t2 (wz usp) (wz S1) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (-8)) (wz (shad f)) s4 s5 (wz (f + 160)) s7 (wz SHB) (wz (f + 832)) s10 (wz (f + 248)) t3 t4 t5 t6)
        F (wz 0xb50c0) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros F0 FH SH0 SHH SEP S0 S1H FS1 SHS1 EL LOC FS MI.
  remember (shad f) as fs eqn:EFS.
  unfold imp_sh, imp_locals, IMP_AMEMSET_A in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(fs + 4, fs + 15)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 (f + 160)) = f + 160) by (apply unsigned_lit; lia).
  assert (EE : bv_unsigned (Z_to_bv 64 (f + 248)) = f + 248) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 fs) = fs) by (apply unsigned_lit; lia).
  zstep. zstep.
  do 11 ls.
  zstep. zstep. zstep. zstep.
  replace (f + 832 + 16) with (f + 848) in LOC by lia. replace (f + 832 + 8) with (f + 840) in LOC by lia. replace (f + 832 + 112) with (f + 944) in LOC by lia.
  zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact FS].
Qed.

Lemma ok_walk3 : forall (S1 usp f szw dw : Z) (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s10 t3 t4 t5 t6 : word) (j64 j72 j80 : list byte) (sb sc : Z) F fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> 0 <= shad f -> shad f + 156 < 2^63 -> (f + 2048 <= shad f \/ shad f + 156 <= f) ->
  0 <= S1 -> S1 + 336 < 2^63 -> (f + 2048 <= S1) -> (shad f + 156 <= S1) ->
  rw_cells asegs m (f + 96) [CB 8 j64; CB 8 j72; CB 8 j80] ->
  rw_cells asegs m (S1 + 80) (imp_locals f (shad f) szw dw) ->
  rw_cells asegs m (shad f) (map C1 (imp_sh 0 sb sc)) ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (wz 0xb5134) (wz S1) gp (wz TPV_A) t0 t1 t2 (wz usp) (wz S1) (wz (f + 32)) (wz (f + 192)) (wz 1) a3 a4 a5 a6 a7
                   (wz (-8)) (wz (shad f)) (wz 1) (wz (f + 32)) (wz (f + 160)) s7 (wz SHB) (wz (f + 832)) s10 (wz (f + 192)) t3 t4 t5 t6)
              F (wz IMP_APPEND_A) fc None m1 (seg_rom asegs)
      /\ munch [(f + 96, f + 120)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (f + 96) [C8 (wz (f + 32)); C8 (wz 0); C8 (wz 64)])
    (MS (mkR (wz 0xb5108) (wz S1) gp (wz TPV_A) t0 t1 t2 (wz usp) (wz S1) (wz (f + 32)) a1 a2 a3 a4 a5 a6 a7
             (wz (-8)) (wz (shad f)) (wz 1) (wz (f + 32)) (wz (f + 160)) s7 (wz SHB) (wz (f + 832)) s10 (wz (f + 192)) t3 t4 t5 t6)
        F (wz 0xb5108) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros F0 FH SH0 SHH SEP S0 S1H FS1 SHS1 SBW LOC FS MI.
  remember (shad f) as fs eqn:EFS.
  unfold imp_sh, imp_locals, IMP_APPEND_A in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(f + 96, f + 120)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (fs + 12)) = fs + 12) by (apply unsigned_lit; lia).
  zstep.
  zstep. cbv beta. rewrite ?lbu_z8, ?zxb_z8. zstep. if_false.
  lstep. lstep. zstep. lstep.
  zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact SBW].
Qed.

Lemma ok_walk6 : forall (S1 usp f szw dw : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 s10 t3 t4 t5 t6 : word) (os : Z) F fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> 0 <= shad f -> shad f + 156 < 2^63 -> (f + 2048 <= shad f \/ shad f + 156 <= f) ->
  0 <= S1 -> S1 + 336 < 2^63 -> (f + 2048 <= S1) -> (shad f + 156 <= S1) ->
  rw_cells asegs m (S1 + 80) (imp_locals f (shad f) szw dw) ->
  rw_cells asegs m (shad f) (map C1 (imp_sh 0 os (-8))) ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (wz 0xb519c) (wz S1) gp (wz TPV_A) t0 t1 t2 (wz usp) (wz S1) (wz (f + 1168)) (wz (f + 840)) a2 a3 a4 a5 a6 a7
                   (wz (-8)) (wz (shad f)) s4 s5 (wz (f + 160)) s7 (wz SHB) (wz (f + 832)) s10 (wz dw) t3 t4 t5 t6)
              F (wz IMP_STR_A) fc None m1 (seg_rom asegs)
      /\ munch [(shad f + 4, shad f + 15); (shad f + 146, shad f + 149)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (shad f) (map C1 (imp_sh (-8) os 0)))
    (MS (mkR ra (wz S1) gp (wz TPV_A) t0 t1 t2 (wz usp) (wz S1) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (-8)) (wz (shad f)) s4 s5 (wz (f + 160)) s7 (wz SHB) (wz (f + 832)) s10 (wz dw) t3 t4 t5 t6)
        F (wz 0xb5158) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros F0 FH SH0 SHH SEP S0 S1H FS1 SHS1 LOC FS MI.
  remember (shad f) as fs eqn:EFS.
  unfold imp_sh, imp_locals, IMP_STR_A in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(fs + 4, fs + 15); (fs + 146, fs + 149)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 fs) = fs) by (apply unsigned_lit; lia).
  do 11 ls.
  do 3 ls.
  replace (f + 832 + 16) with (f + 848) in LOC by lia. replace (f + 832 + 8) with (f + 840) in LOC by lia. replace (f + 832 + 112) with (f + 944) in LOC by lia.
  zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact FS].
Qed.

Lemma ok_walk7 : forall (S1 usp f szw dw : Z) (gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 s10 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> 0 <= shad f -> shad f + 156 < 2^63 -> 0 <= S1 -> S1 + 336 < 2^63 ->
  rw_cells asegs m (f + 272) [C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
  rw_cells asegs m (S1 + 80) (imp_locals f (shad f) szw dw) ->
  mem_inv asegs m ->
  evt asegs (eq (MS (mkR (wz 0xb51d0) (wz S1) gp (wz TPV_A) t0 t1 t2 (wz usp) (wz S1) (wz (f + 272)) (wz (f + 1168)) (wz 24) a3 a4 a5 a6 a7
                        (wz (-8)) (wz (shad f)) (wz (f + 272)) (wz szw) (wz (f + 160)) s7 (wz SHB) (wz (f + 832)) s10 (wz dw) t3 t4 t5 t6)
                   F (wz IMP_AMEMCPY_A) fc None m (seg_rom asegs)))
    (MS (mkR (wz 0xb519c) (wz S1) gp (wz TPV_A) t0 t1 t2 (wz usp) (wz S1) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (-8)) (wz (shad f)) s4 s5 (wz (f + 160)) s7 (wz SHB) (wz (f + 832)) s10 (wz dw) t3 t4 t5 t6)
        F (wz 0xb519c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros F0 FH SH0 SHH S0 S1H OUT LOC MI.
  unfold imp_locals, IMP_AMEMCPY_A in *.
  assert (ES : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 (f + 160)) = f + 160) by (apply unsigned_lit; lia).
  pose proof (rw_cells_C8_read1_g asegs m _ _ _ OUT) as RD. change (bv_unsigned (Z_to_bv 64 0)) with 0 in RD.
  replace (f + 832 + 16) with (f + 848) in LOC by lia. replace (f + 832 + 8) with (f + 840) in LOC by lia. replace (f + 832 + 112) with (f + 944) in LOC by lia.
  zstep. zstep. rewrite ?zxb_u, ?u8_lit. change (Z.land (0 mod 256) 1) with 0.
  zstep. zstep.
  zstep. if_true.
  zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma ok_walk9 : forall (S1 usp f szw dw : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 s10 t3 t4 t5 t6 sbv : word) F fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> 0 <= S1 -> S1 + 336 < 2^63 -> (f + 2048 <= S1) ->
  rw_cells asegs m (f + 840) [C8 sbv] ->
  rw_cells asegs m (S1 + 80) (imp_locals f (shad f) szw dw) ->
  ro_cells asegs m OSS_GOT_VT_A [C8 (wz OSS_VTT_A); C8 (wz (OSS_SB_VPTR_A - 16)); C8 (wz (OSS_SBB_VPTR_A - 16)); C8 (wz OSS_VBOFF_A)] ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (wz 0xb5288) (wz S1) gp (wz TPV_A) t0 t1 t2 (wz usp) (wz S1) (wz (f + 848)) a1 a2 a3 a4 a5 a6 a7
                   (wz (-8)) (wz (shad f)) s4 s5 (wz (f + 160)) s7 (wz SHB) (wz (f + 832)) s10 (wz dw) t3 t4 t5 t6)
              F (wz IMP_LOC_DTOR_A) fc None m1 (seg_rom asegs)
      /\ munch [(f + 840, f + 848)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (f + 840) [C8 (wz OSS_SBB_VPTR_A)])
    (MS (mkR ra (wz S1) gp (wz TPV_A) t0 t1 t2 (wz usp) (wz S1) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (-8)) (wz (shad f)) s4 s5 (wz (f + 160)) s7 (wz SHB) (wz (f + 832)) s10 (wz dw) t3 t4 t5 t6)
        F (wz 0xb5270) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros F0 FH S0 S1H FS1 VP LOC V1 MI.
  unfold imp_locals, IMP_LOC_DTOR_A, OSS_GOT_VT_A, OSS_VTT_A, OSS_SB_VPTR_A, OSS_SBB_VPTR_A, OSS_VBOFF_A in *.
  replace (0x16f9c0 - 16) with 0x16f9b0 in V1 by reflexivity. replace (0x16f780 - 16) with 0x16f770 in V1 by reflexivity.
  pose proof (munch_refl [(f + 840, f + 848)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 (f + 832)) = f + 832) by (apply unsigned_lit; lia).
  replace (f + 832 + 16) with (f + 848) in LOC by lia. replace (f + 832 + 8) with (f + 840) in LOC by lia. replace (f + 832 + 112) with (f + 944) in LOC by lia.
  zstep. zstep. zstep.
  lstep.
  zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption| eassumption].
Qed.

Lemma ok_walk10 : forall (S1 usp f szw dw : Z) (gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 s10 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> 0 <= S1 -> S1 + 336 < 2^63 ->
  rw_cells asegs m (S1 + 80) (imp_locals f (shad f) szw dw) ->
  mem_inv asegs m ->
  evt asegs (eq (MS (mkR (wz 0xb529c) (wz S1) gp (wz TPV_A) t0 t1 t2 (wz usp) (wz S1) (wz (f + 944)) (bv_add s4 (wz 8)) a2 a3 a4 a5 a6 a7
                        (wz (-8)) (wz (shad f)) s4 s5 (wz (f + 160)) s7 (wz SHB) (wz (f + 832)) s10 (wz dw) t3 t4 t5 t6)
                   F (wz IMP_IOS_DTOR_A) fc None m (seg_rom asegs)))
    (MS (mkR (wz 0xb5288) (wz S1) gp (wz TPV_A) t0 t1 t2 (wz usp) (wz S1) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (-8)) (wz (shad f)) s4 s5 (wz (f + 160)) s7 (wz SHB) (wz (f + 832)) s10 (wz dw) t3 t4 t5 t6)
        F (wz 0xb5288) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros F0 FH S0 S1H LOC MI.
  unfold imp_locals, IMP_IOS_DTOR_A in *.
  assert (ES : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply unsigned_lit; lia).
  replace (f + 832 + 16) with (f + 848) in LOC by lia. replace (f + 832 + 8) with (f + 840) in LOC by lia. replace (f + 832 + 112) with (f + 944) in LOC by lia.
  zstep. zstep. zstep.
  zstep.
  zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma ok_walk11 : forall (S1 usp f dw : Z) (gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 s10 t3 t4 t5 t6 : word) (sb sc : Z) F fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> 0 <= shad f -> shad f + 156 < 2^63 ->
  rw_cells asegs m (shad f) (map C1 (imp_sh sb 0 sc)) ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (wz 0xb529c) (wz S1) gp (wz TPV_A) t0 t1 t2 (wz usp) (wz S1) a0 a1 a2 a3 a4 a5 a6 a7
                   (wz (-8)) (wz (shad f)) s4 s5 (wz (f + 160)) s7 (wz SHB) (wz (f + 832)) s10 (wz dw) t3 t4 t5 t6)
              F (wz IMP_OKARM_END_A) fc None m1 (seg_rom asegs)
      /\ munch [(shad f + 104, shad f + 137)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (shad f) (map C1 (imp_sh sb (-8) sc)))
    (MS (mkR (wz 0xb529c) (wz S1) gp (wz TPV_A) t0 t1 t2 (wz usp) (wz S1) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (-8)) (wz (shad f)) s4 s5 (wz (f + 160)) s7 (wz SHB) (wz (f + 832)) s10 (wz dw) t3 t4 t5 t6)
        F (wz 0xb529c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros F0 FH SH0 SHH FS MI.
  remember (shad f) as fs eqn:EFS.
  unfold imp_sh, IMP_OKARM_END_A in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(fs + 104, fs + 137)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (ESH : bv_unsigned (Z_to_bv 64 fs) = fs) by (apply unsigned_lit; lia).
  do 33 ls.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact FS].
Qed.

Local Ltac lit_addr H := match type of H with context [wa ?e] => let e' := eval cbv in e in change e with e' in H end.
Local Ltac chkV2 SHZ a := let H := fresh "VRD" in shz_pose_with SHZ a H; lit_addr H; zstep; shz_norm; zstep; if_false; try clear H.

Definition ok_W8 (f : Z) : list (Z * Z) := [(shad f + 146, shad f + 149); (f + 832, f + 840); (f + 944, f + 952); (f + 840, f + 848)].

Lemma ok_walk8 : forall (S1 usp f szw dw : Z) (gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s10 t3 t4 t5 t6 : word) (os : Z) (b72 : byte) F fc (m : mem),
  0x6d2000 <= f -> f + 2048 < 2^63 -> 0x7fff8000 <= shad f -> shad f + 156 < 2^63 -> (f + 2048 <= shad f \/ shad f + 156 <= f) -> f mod 64 = 0 ->
  0 <= S1 -> S1 + 336 < 2^63 -> (f + 2048 <= S1) -> (shad f + 156 <= S1) ->
  (forall m', munch (ok_W8 f) m m' -> wmono asegs m m' -> shz m' OSS_VTT_A 40) ->
  (forall m', munch (ok_W8 f) m m' -> wmono asegs m m' -> shz m' OSS_VBOFF_A 8) ->
  (forall m', munch (ok_W8 f) m m' -> wmono asegs m m' -> shz m' (f + 832) 264) ->
  (forall m', munch (ok_W8 f) m m' -> wmono asegs m m' -> ov_read_bytes asegs m' (wa (f + 904)) 1 = Some [b72]) ->
  rw_cells asegs m (f + 832) [C8 (wz OSS_OS_VPTR_A)] -> rw_cells asegs m (f + 840) [C8 (wz OSS_SB_VPTR_A)] -> rw_cells asegs m (f + 944) [C8 (wz OSS_IOS_VPTR_A)] ->
  rw_cells asegs m (shad f) (map C1 (imp_sh (-8) os 0)) ->
  ro_cells asegs m OSS_GOT_VT_A [C8 (wz OSS_VTT_A); C8 (wz (OSS_SB_VPTR_A - 16)); C8 (wz (OSS_SBB_VPTR_A - 16)); C8 (wz OSS_VBOFF_A)] ->
  ro_cells asegs m OSS_VTT_A [C8 (wz OSS_OS_VPTR_A); C8 (wz OSS_OS_CVPTR_A); C8 (wz OSS_IOS_CVPTR_A); C8 (wz OSS_IOS_VPTR_A); C8 (wz 0x70)] ->
  ro_cells asegs m OSS_VBOFF_A [C8 (wz 0x70)] ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (wz 0xb51d0) (wz S1) gp (wz TPV_A) t0 t1 t2 (wz usp) (wz S1) (wz OSS_SB_VPTR_A) (wz (Z.land (bv_unsigned b72) 1)) (wz 0) a3 a4 a5 a6 a7
                   (wz (-8)) (wz (shad f)) (wz OSS_VTT_A) (wz szw) (wz (f + 160)) s7 (wz SHB) (wz (f + 832)) s10 (wz dw) t3 t4 t5 t6)
              F (wz 0xb525c) fc None m1 (seg_rom asegs)
      /\ munch (ok_W8 f) m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (f + 832) [C8 (wz OSS_OS_VPTR_A)] /\ rw_cells asegs m1 (f + 840) [C8 (wz OSS_SB_VPTR_A)] /\ rw_cells asegs m1 (f + 944) [C8 (wz OSS_IOS_VPTR_A)]
      /\ rw_cells asegs m1 (shad f) (map C1 (imp_sh (-8) os (-8))))
    (MS (mkR (wz 0xb51d0) (wz S1) gp (wz TPV_A) t0 t1 t2 (wz usp) (wz S1) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (-8)) (wz (shad f)) (wz (f + 272)) (wz szw) (wz (f + 160)) s7 (wz SHB) (wz (f + 832)) s10 (wz dw) t3 t4 t5 t6)
        F (wz 0xb51d0) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros F0 FH SH0 SHH SEP F64 S0 S1H FS1 SHS1 SHZV SHZB SHZ RD72 VP VSB VIOS FS V1 V2 V3 MI.
  unfold ok_W8 in *. remember (shad f) as fs eqn:EFS.
  unfold imp_sh, OSS_GOT_VT_A, OSS_VTT_A, OSS_SB_VPTR_A, OSS_SBB_VPTR_A, OSS_VBOFF_A, OSS_OS_VPTR_A, OSS_OS_CVPTR_A, OSS_IOS_CVPTR_A, OSS_IOS_VPTR_A, SHB in *.
  cbn [map app repeat] in *.
  replace (0x16f9c0 - 16) with 0x16f9b0 in V1 by reflexivity. replace (0x16f780 - 16) with 0x16f770 in V1 by reflexivity.
  pose proof (munch_refl [(fs + 146, fs + 149); (f + 832, f + 840); (f + 944, f + 952); (f + 840, f + 848)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 (f + 832)) = f + 832) by (apply unsigned_lit; lia).
  assert (EF2 : bv_unsigned (Z_to_bv 64 (f + 944)) = f + 944) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 fs) = fs) by (apply unsigned_lit; lia).
  zstep. zstep.
  do 3 ls.

  zstep. rewrite ?shr3_div. zstep. chkV2 SHZV 1506184.
  zstep. zstep. zstep. rewrite ?shr3_div.
  lstep.
  zstep. chkV2 SHZV 1506208.
  zstep. zstep. rewrite ?shr3_div. zstep. chkV2 SHZB 1506104.
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
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption| exact FS].
Qed.
