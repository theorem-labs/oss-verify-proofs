(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim SjModel PjModel.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Sj_num_walk Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit
     Sj_num_akit Atp_fzwA Pj_rtkA Pj_defsA Pj_hdefsA Pj_cpsA Pj_os_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition pj_shadow_o : list byte :=
  repeat (Z_to_bv 8 (-15)) 4 ++ repeat (Z_to_bv 8 (-8)) 11 ++ repeat (Z_to_bv 8 (-14)) 5 ++ repeat (Z_to_bv 8 0) 10 ++ repeat (Z_to_bv 8 (-14)) 4
  ++ repeat (Z_to_bv 8 0) 36 ++ repeat (Z_to_bv 8 (-13)) 10.
Definition pj_shadow_oo : list byte :=
  repeat (Z_to_bv 8 (-15)) 4 ++ repeat (Z_to_bv 8 0) 11 ++ repeat (Z_to_bv 8 (-14)) 5 ++ repeat (Z_to_bv 8 0) 10 ++ repeat (Z_to_bv 8 (-14)) 4
  ++ repeat (Z_to_bv 8 0) 36 ++ repeat (Z_to_bv 8 (-13)) 10.

Lemma cells_bytes_map_C1 : forall l : list byte, cells_bytes (map C1 l) = l.
Proof. induction l as [|b l IH]; [reflexivity|]. cbn [map cells_bytes cbytes app]. rewrite IH. reflexivity. Qed.

Lemma shadow_oo_sb : forall (m : mem) A, rw_cells asegs m A (map C1 pj_shadow_oo) -> bytes_at asegs m (A + 4) (repeat z8 11).
Proof.
  intros m A H. apply rw_cells_bytes_at in H. rewrite cells_bytes_map_C1 in H.
  change pj_shadow_oo with (repeat (Z_to_bv 8 (-15)) 4 ++ (repeat z8 11 ++ (repeat (Z_to_bv 8 (-14)) 5 ++ repeat (Z_to_bv 8 0) 10 ++ repeat (Z_to_bv 8 (-14)) 4
  ++ repeat (Z_to_bv 8 0) 36 ++ repeat (Z_to_bv 8 (-13)) 10))) in H.
  apply bytes_at_app in H. destruct H as [_ H]. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.
Lemma shadow_oo_os : forall (m : mem) A, rw_cells asegs m A (map C1 pj_shadow_oo) -> bytes_at asegs m (A + 34) (repeat z8 36).
Proof.
  intros m A H. apply rw_cells_bytes_at in H. rewrite cells_bytes_map_C1 in H.
  change pj_shadow_oo with ((repeat (Z_to_bv 8 (-15)) 4 ++ repeat (Z_to_bv 8 0) 11 ++ repeat (Z_to_bv 8 (-14)) 5 ++ repeat (Z_to_bv 8 0) 10 ++ repeat (Z_to_bv 8 (-14)) 4)
  ++ (repeat z8 36 ++ repeat (Z_to_bv 8 (-13)) 10)) in H.
  apply bytes_at_app in H. destruct H as [_ H]. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.
Lemma shadow_o_os : forall (m : mem) A, rw_cells asegs m A (map C1 pj_shadow_o) -> bytes_at asegs m (A + 34) (repeat z8 36).
Proof.
  intros m A H. apply rw_cells_bytes_at in H. rewrite cells_bytes_map_C1 in H.
  change pj_shadow_o with ((repeat (Z_to_bv 8 (-15)) 4 ++ repeat (Z_to_bv 8 (-8)) 11 ++ repeat (Z_to_bv 8 (-14)) 5 ++ repeat (Z_to_bv 8 0) 10 ++ repeat (Z_to_bv 8 (-14)) 4)
  ++ (repeat z8 36 ++ repeat (Z_to_bv 8 (-13)) 10)) in H.
  apply bytes_at_app in H. destruct H as [_ H]. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.
Lemma cells_size_map_C1' : forall bs : list byte, cells_size (map C1 bs) = length bs.
Proof. induction bs as [|b bs IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite IH. reflexivity. Qed.

Definition pk_regs (pc : Z) (ra : word) (sp' : Z) (gp t0 t1 t2 : word) (usp : Z) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (f : Z) (s3 s5 s6 s7 s8 s9 : word)
    (t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 sp') gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 f) s3 (Z_to_bv 64 (f / 8 + 2147450880)) s5 s6 s7 s8 s9 (Z_to_bv 64 f) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom asegs).
Local Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma pj_walkO1 : forall (usp sp' f lo : Z) (ra gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word) (j24 : list byte) F fc (m : mem),
  0 < f -> f + 1024 <= lo -> f / 8 + 2147450880 + 128 <= lo -> 0 <= f / 8 -> (f + 1024 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 128 <= f) ->
  lo <= sp' -> sp' + 192 <= usp -> usp < 2^63 ->
  rw_cells asegs m (sp' + 24) [CB 8 j24] -> rw_cells asegs m (sp' + 64) [C8 (wz (f + 184)); C8 (wz 1); C4 (wz 0)] ->
  rw_cells asegs m (f / 8 + 2147450880) (map C1 pj_shadow_cut) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = pk_regs PJ_OS_CTOR_A (wz 0xb1928) sp' gp t0 t1 t2 usp (wz (f + 272)) a1 a2 a3 a4 a5 a6 a7 f (wz (f + 160)) (wz (f + 272)) (wz (f + 184)) (wz 1) s8 s9 t3 t4 t5 t6 F fc m1
      /\ munch [(sp' + 24, sp' + 32); (f / 8 + 2147450880 + 34, f / 8 + 2147450880 + 70)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (sp' + 24) [C8 (wz (f + 160))] /\ rw_cells asegs m1 (sp' + 64) [C8 (wz (f + 184)); C8 (wz 1); C4 (wz 0)]
      /\ rw_cells asegs m1 (f / 8 + 2147450880) (map C1 pj_shadow_o))
    (pk_regs PJ_OKARM_A ra sp' gp t0 t1 t2 usp (wz 0) a1 a2 a3 a4 a5 a6 a7 f (wz (f + 160)) s5 s6 s7 s8 s9 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FLO SLO FD SEP LSP SPU UH F24 RES FS MI.
  unfold pk_regs, PJ_OKARM_A, PJ_OS_CTOR_A, pj_shadow_cut, pj_shadow_o in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(sp' + 24, sp' + 32); (f / 8 + 2147450880 + 34, f / 8 + 2147450880 + 70)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  ls. zstep. zstep. zstep.
  do 36 ls.
  zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma pj_walkO2 : forall (usp sp' f lo : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 1024 <= lo -> f / 8 + 2147450880 + 128 <= lo -> 0 <= f / 8 -> (f + 1024 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 128 <= f) ->
  lo <= sp' -> sp' + 192 < 2^63 ->
  rw_cells asegs m (f / 8 + 2147450880) (map C1 pj_shadow_o) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = pk_regs e_asan_memset (wz 0xb1970) sp' gp t0 t1 t2 usp (wz (f + 32)) (wz 0) (wz 64) a3 a4 a5 a6 a7 f (wz 64) s5 s6 s7 (wz (f + 32)) (wz (f + 96)) t3 t4 t5 t6 F fc m1
      /\ munch [(f / 8 + 2147450880 + 4, f / 8 + 2147450880 + 15)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (f / 8 + 2147450880) (map C1 pj_shadow_oo))
    (pk_regs 0xb1928 ra sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s3 s5 s6 s7 s8 s9 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FLO SLO FD SEP LSP SPH FS MI.
  unfold pk_regs, e_asan_memset, pj_shadow_o, pj_shadow_oo in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(f / 8 + 2147450880 + 4, f / 8 + 2147450880 + 15)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  zstep. do 11 ls.
  zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. eassumption.
Qed.

Lemma pj_walkS : forall (usp sp' f lo : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 : word) (j64 j72 j80 : list byte) F fc (m : mem),
  0 < f -> f + 1024 <= lo -> f / 8 + 2147450880 + 128 <= lo -> 0 <= f / 8 -> (f + 1024 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 128 <= f) ->
  lo <= sp' -> sp' + 192 < 2^63 ->
  rw_cells asegs m (f + 96) [CB 8 j64; CB 8 j72; CB 8 j80] ->
  rw_cells asegs m (f / 8 + 2147450880) (map C1 pj_shadow_oo) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (a3' : word),
      ms = pk_regs PJ_APPEND_ELEM_A (wz 0xb199c) sp' gp t0 t1 t2 usp (wz (f + 32)) (wz (f + 184)) (wz 1) a3' a4 a5 a6 a7 f (wz 64) s5 (wz (f + 184)) (wz 1) (wz (f + 32)) (wz (f + 96))
             t3 t4 t5 t6 F fc m1
      /\ munch [(f + 96, f + 120)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (f + 96) [C8 (wz (f + 32)); C8 (wz 0); C8 (wz 64)]
      /\ rw_cells asegs m1 (f / 8 + 2147450880) (map C1 pj_shadow_oo))
    (pk_regs 0xb1970 ra sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f (wz 64) s5 (wz (f + 184)) (wz 1) (wz (f + 32)) (wz (f + 96)) t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FLO SLO FD SEP LSP SPH SC FS MI.
  unfold pk_regs, PJ_APPEND_ELEM_A, pj_shadow_oo in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(f + 96, f + 120)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (E96 : bv_unsigned (Z_to_bv 64 (f + 96)) = f + 96) by (apply unsigned_lit; lia).
  assert (E32 : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  zstep. rewrite shr3_div. zstep.
  replace ((f + 96) / 8 + 2147450880) with (f / 8 + 2147450880 + 12) by (Z.div_mod_to_equations; lia).
  zstep. zstep. if_false.
  replace (f + 32 + 64) with (f + 96) by lia.
  ls. ls. ls.
  zstep. zstep. zstep. zstep.
  apply evt_done. eexists _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma pj_walkP : forall (usp sp' f buf size cap : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 1024 < 2^63 -> 0 <= buf < 2^64 -> 0 <= size < 2^64 -> 0 <= cap < 2^64 ->
  rw_cells asegs m (f + 96) [C8 (wz buf); C8 (wz size); C8 (wz cap)] -> mem_inv asegs m ->
  evt asegs (eq (pk_regs PJ_OSPUT_A (wz 0xb19b0) sp' gp t0 t1 t2 usp (wz (f + 272 + 128)) (wz buf) (wz size) a3 a4 a5 a6 a7 f s3 (wz (f + 272)) (wz (f + 272 + 128)) s7
                 (wz (f + 32)) (wz (f + 96)) t3 t4 t5 t6 F fc m))
    (pk_regs 0xb199c ra sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s3 (wz (f + 272)) s6 s7 (wz (f + 32)) (wz (f + 96)) t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH BR SR CR SC MI. unfold pk_regs, PJ_OSPUT_A in *. replace (f + 272 + 128) with (f + 400) by lia.
  assert (E32 : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  zstep. zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma pj_walkD : forall (usp sp' f buf size cap : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 1024 < 2^63 -> 0 < buf < 2^64 -> 0 <= size < 2^64 -> 0 <= cap < 2^64 -> 0 <= sp' -> sp' + 192 < 2^63 ->
  rw_cells asegs m (f + 96) [C8 (wz buf); C8 (wz size); C8 (wz cap)] -> rw_cells asegs m (sp' + 24) [C8 (wz (f + 160))] -> mem_inv asegs m ->
  evt asegs (fun ms =>
      (buf = f + 32 /\ ms = pk_regs 0xb19c4 ra sp' gp t0 t1 t2 usp (wz buf) a1 a2 a3 a4 a5 a6 a7 f (wz (f + 160)) (wz (f + 272)) s6 s7 (wz (f + 32)) (wz (f + 96)) t3 t4 t5 t6 F fc m)
      \/ (buf <> f + 32 /\ ms = pk_regs OPDELARR_A (wz 0xb19c4) sp' gp t0 t1 t2 usp (wz buf) a1 a2 a3 a4 a5 a6 a7 f (wz (f + 160)) (wz (f + 272)) s6 s7 (wz (f + 32)) (wz (f + 96))
                                    t3 t4 t5 t6 F fc m))
    (pk_regs 0xb19b0 ra sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s3 (wz (f + 272)) s6 s7 (wz (f + 32)) (wz (f + 96)) t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH BR SR CR SP0 SPH SC F24 MI. unfold pk_regs, OPDELARR_A in *.
  assert (E32 : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  zstep. zstep. zstep. if_cases K; zify_cond K.
  - apply evt_done. left. split; [lia| cbv delta [mkR]; reflexivity].
  - zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
    zstep. apply evt_done. right. split; [lia| cbv delta [mkR]; reflexivity].
Qed.

Lemma pj_walkR1 : forall (usp sp' f lo : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 t3 t4 t5 t6 : word) (jv : list byte) F fc (m : mem),
  0 < f -> f + 1024 <= lo -> f / 8 + 2147450880 + 128 <= lo -> 0 <= f / 8 -> (f + 1024 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 128 <= f) ->
  lo <= sp' -> sp' + 192 < 2^63 ->
  rw_cells asegs m (f + 272) [CB 8 jv] -> ro_cells asegs m 0x16a930 [C8 (wz 0x1678f0); C8 (wz 0x167970)] ->
  rw_cells asegs m (f / 8 + 2147450880) (map C1 pj_shadow_oo) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (a1' : word),
      ms = pk_regs PJ_LOC_DTOR_A (wz 0xb1a20) sp' gp t0 t1 t2 usp (wz (f + 280)) a1' a2 a3 a4 a5 a6 a7 f s3 (wz (f + 272)) s6 (wz (-8)) (wz (f + 32)) (wz (f + 96))
             t3 t4 t5 t6 F fc m1
      /\ munch [(f / 8 + 2147450880 + 4, f / 8 + 2147450880 + 15); (f + 272, f + 280)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (f + 272) [C8 (wz 0x167900)]
      /\ rw_cells asegs m1 (f / 8 + 2147450880) (map C1 pj_shadow_o))
    (pk_regs 0xb19c4 ra sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s3 (wz (f + 272)) s6 s7 (wz (f + 32)) (wz (f + 96)) t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FLO SLO FD SEP LSP SPH FO GOT FS MI.
  unfold pk_regs, PJ_LOC_DTOR_A, pj_shadow_o, pj_shadow_oo in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(f / 8 + 2147450880 + 4, f / 8 + 2147450880 + 15); (f + 272, f + 280)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (Z_to_bv 64 (f + 272)) = f + 272) by (apply unsigned_lit; lia).
  zstep. do 11 ls.
  zstep. zstep. zstep. zstep.

  zstep. zstep.

  zstep. zstep. zstep. ls. zstep. zstep.
  apply evt_done. eexists _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma pj_walkR2 : forall (usp sp' f : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 1024 < 2^63 -> mem_inv asegs m ->
  evt asegs (eq (pk_regs PJ_IOS_DTOR_A (wz 0xb1a28) sp' gp t0 t1 t2 usp (wz (f + 272 + 136)) a1 a2 a3 a4 a5 a6 a7 f s3 (wz (f + 272)) s6 s7 (wz (f + 32)) (wz (f + 96)) t3 t4 t5 t6 F fc m))
    (pk_regs 0xb1a20 ra sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s3 (wz (f + 272)) s6 s7 (wz (f + 32)) (wz (f + 96)) t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH MI. unfold pk_regs, PJ_IOS_DTOR_A in *. replace (f + 272 + 136) with (f + 408) by lia.
  zstep. zstep. apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma pj_walkR3 : forall (usp sp' f lo : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s6 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 1024 <= lo -> f / 8 + 2147450880 + 128 <= lo -> 0 <= f / 8 -> (f + 1024 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 128 <= f) ->
  lo <= sp' -> sp' + 192 < 2^63 ->
  rw_cells asegs m (f / 8 + 2147450880) (map C1 pj_shadow_o) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = pk_regs PJ_JOIN_A ra sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s3 (wz (f + 272)) s6 (wz (-8)) (wz (f + 32)) (wz (f + 96)) t3 t4 t5 t6 F fc m1
      /\ munch [(f / 8 + 2147450880 + 34, f / 8 + 2147450880 + 70)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (f / 8 + 2147450880) (map C1 pj_shadow_cut))
    (pk_regs 0xb1a28 ra sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s3 (wz (f + 272)) s6 (wz (-8)) (wz (f + 32)) (wz (f + 96)) t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FLO SLO FD SEP LSP SPH FS MI.
  unfold pk_regs, PJ_JOIN_A, pj_shadow_o, pj_shadow_cut in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(f / 8 + 2147450880 + 34, f / 8 + 2147450880 + 70)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  do 36 ls.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. eassumption.
Qed.

Lemma loc_static : forall x, PJ_LOC_LO_A <= x < PJ_LOC_HI_A -> client_static x.
Proof.
  intros x Hx. assert (H : in_ranges LIB_FP x); [| exact (proj1 (lib_fp_static x H))].
  exists PJ_LOC_LO_A, PJ_LOC_HI_A. split; [unfold LIB_FP, PJ_LOC_LO_A, PJ_LOC_HI_A; cbn; tauto| exact Hx].
Qed.

Definition okcl (S1 usp f : Z) (L : list (Z * Z)) (x : Z) : Prop :=
  (S1 <= x < usp) \/ (f <= x < f + 1016) \/ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 128) \/ (PJ_LOC_LO_A <= x < PJ_LOC_HI_A) \/ in_live L x.

Definition okW (S1 f : Z) : list (Z * Z) :=
  [(S1 + 24, S1 + 32); (f + 32, f + 32 + 88); (f + 272, f + 560); (f / 8 + 2147450880 + 4, f / 8 + 2147450880 + 15);
   (f / 8 + 2147450880 + 34, f / 8 + 2147450880 + 70); (PJ_LOC_LO_A, PJ_LOC_HI_A)].

Section Okarm.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.
Variables OSFRESHA OSUSEDA OSIOSA : mem -> Z -> Prop.

Hypothesis OSF_loc : forall m m' OS, OSFRESHA m OS -> agree_on (fun a => OS <= a < OS + 288) m m' -> OSFRESHA m' OS.
Hypothesis OSU_imp : forall m OS, OSUSEDA m OS -> rw_cells asegs m (OS + 8) [C8 (Z_to_bv 64 PJ_LOC_IMP_A)].
Hypothesis OSU_ios : forall m m' OS, OSUSEDA m OS -> agree_on (fun a => OS + 136 <= a < OS + 288) m m' -> OSIOSA m' OS.

Hypothesis ROA : forall Σ m, ART RT Σ m -> pj_os_roA m.

Hypothesis CTOR : ctor_cpsA RT PMc OSFRESHA.
Hypothesis SER : ser_cpsA RT PMc TAPE_MAX_DEPTH.
Hypothesis PUT : put_cpsA RT PMc OSFRESHA OSUSEDA.
Hypothesis LOCD : locdtor_evtA.
Hypothesis IOSD : iosdtor_cpsA RT PMc OSIOSA.

Local Ltac ul := unfold PJ_OKARM_STACK_A, PJ_SER_STACK_A, PJ_OS_CTOR_STACK_A, PJ_LOC_STACK_A, PJ_OS_PUT_STACK_A, PJ_IOS_DTOR_STACK_A, ser_needA, PJ_TC_STACK_A in *;
                 unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, LIVE_MAX in *; lia.
Local Ltac outW Ho := cbn [okW outside] in Ho |- *; repeat split; try exact I; lia.

Theorem pj_okarm_okA : pj_okarm_cpsA RT PMc.
Proof using AF RC OSF_loc OSU_imp OSU_ios ROA CTOR SER PUT LOCD IOSD.
  intros Σ K E S1 usp ra gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 t3 t4 t5 t6 F fc m j24 jsb jos
    FDO MST OK KF ESB EDOC LV DR0 LOC0 NL0 LOCKW0 IOS0 F24 RES0 FB0 FO0 FS0 ART0 MI0 ST0 LOQ UT S32 USP FRM FRS LVB CR0 HK.
  destruct E as [lo f kF SB DOC TAPE NT SBUF NS tws sbs len L].
  cbn [pa_lo pa_F pa_kF pa_SB pa_DOC pa_TAPE pa_NT pa_SBUF pa_NS pa_tws pa_sbs pa_len pa_L] in *. subst kF SB DOC.
  pose proof (ok_sb _ OK) as (SB32 & _ & _). pose proof (ok_frame _ OK) as (F64 & FSEG & FLO). pose proof (ok_lo _ OK) as LOW.
  pose proof (ok_len _ OK) as LEN. pose proof (ok_Lpos _ OK) as LPOS. pose proof (ok_wfS _ OK) as WFS.
  pose proof (ok_tape _ OK) as (_ & TN8 & _ & _ & INT). pose proof (ok_sbuf _ OK) as (_ & SNS & _ & _ & INS).
  cbn [pa_lo pa_F pa_kF pa_SB pa_DOC pa_TAPE pa_NT pa_SBUF pa_NS pa_tws pa_sbs pa_len pa_L] in SB32, F64, FSEG, FLO, LOW, LEN, LPOS, WFS, TN8, INT, SNS, INS.
  change (fs_size 4) with 1024 in FLO.
  unfold tape_wfS in WFS. destruct WFS as (N2 & SNB & _ & _ & ELS).
  pose proof LV as (LVE & INF & SPLO). cbn [pa_lo pa_F pa_kF pa_SB pa_L sbchunkA sbA0 sa_heap app] in LVE, INF, SPLO.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (fframe_ranges RT AF Σ m f 4 ART0 INF) as (FPOS & FR1 & _ & SHB0 & SHT).
  pose proof (proj2 (af_fshadow_apart RT AF Σ m f 4%nat ART0 INF) f 4%nat INF) as FSELF.
  change (fs_size 4) with 1024 in FR1, SHT, FSELF.
  assert (SHF : shad (f + 1024) = shad f + 128) by (unfold shad; Z.div_mod_to_equations; lia).
  rewrite SHF in SHT, FSELF. unfold shad, SHB in SHB0, SHT, FSELF, FS0. unfold SEGTOP_A in FSEG.
  assert (FD0 : 0 <= f / 8) by (apply Z.div_pos; lia).
  assert (EU : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply unsigned_lit; ul). assert (LOS1 : lo + 64 <= S1) by ul.
  pose proof (PJ_CAPMAX_bound len LEN) as CAPB. pose proof (pj_psi_root len (f + 32) LEN) as PSI0.

  assert (LRNG : forall p k, In (p, k) L -> 0 < p /\ p + k <= lo /\ (f + 1024 <= p \/ p + k <= f)
            /\ (p + k <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 128 <= p) /\ (p + k <= 0x10000 \/ 0x6c9000 <= p)).
  { intros p k Hin. rewrite <- LVE in Hin.
    pose proof (af_live_range RT AF Σ m p k ART0 Hin) as (Y0 & Y1 & Y2).
    pose proof (proj2 (proj2 (proj2 (af_frames_range RT AF Σ m f 4%nat ART0 INF))) p k Hin) as Y3.
    pose proof (proj1 (af_fshadow_apart RT AF Σ m f 4%nat ART0 INF) p k Hin) as Y4.
    change (fs_size 4) with 1024 in Y3, Y4. rewrite SHF in Y4. unfold shad, SHB, SEGTOP_A in Y2, Y4. lia. }

  assert (CLA : forall (Σx : rts RT) x, rt_frames RT Σx = [(f, 4%nat)] -> (forall e, In e L -> In e (rt_live RT Σx)) ->
            okcl S1 usp f L x -> aclient (rt_live RT Σx) (rt_frames RT Σx) S1 x).
  { intros Σx x FRSx INCL [H|[H|[H|[H|H]]]].
    - left. ul.
    - right; right; right; left. exists f, 4%nat. rewrite FRSx. split; [left; reflexivity| change (fs_size 4) with 1024; lia].
    - right; right; right; right. exists f, 4%nat. rewrite FRSx. split; [left; reflexivity| unfold shad, SHB; change (fs_size 4) with 1024; Z.div_mod_to_equations; lia].
    - right; left. exact (loc_static x H).
    - right; right; left. destruct H as (p & k & Hin & Hr). exists p, k. split; [exact (INCL _ Hin)| exact Hr]. }

  assert (CLW : forall (Σx : rts RT) (mx my : mem) W, rt_frames RT Σx = [(f, 4%nat)] -> (forall e, In e L -> In e (rt_live RT Σx)) -> munch W mx my ->
            Forall (fun iv => forall x, fst iv <= x < snd iv -> okcl S1 usp f L x) W ->
            agree_on (fun a => ~ aclient (rt_live RT Σx) (rt_frames RT Σx) S1 a) mx my).
  { intros Σx mx my W FRSx INCL MU HW a Ha. apply MU. clear MU. induction W as [|[lo' hi'] W IH]; [exact I|].
    apply Forall_cons_iff in HW. destruct HW as [H1 HW]. cbn [outside fst snd] in *. split; [| exact (IH HW)].
    intros Hin. apply Ha. apply (CLA Σx _ FRSx INCL). apply H1. exact Hin. }

  assert (DRC : forall x, docrep_rng (mkPJA lo f 4%nat (f + 32) (f + 184) TAPE NT SBUF NS tws sbs len L) x ->
            (f + 120 <= x < f + 272) \/ (f / 8 + 2147450880 + 15 <= x < f / 8 + 2147450880 + 34) \/ in_live L x).
  { intros x Hx. unfold docrep_rng in Hx. cbn [pa_DOC pa_TAPE pa_SBUF pa_tws pa_sbs] in Hx. unfold shad, SHB in Hx.
    destruct Hx as [H|[H|[H|H]]]; [left; lia| right; left; Z.div_mod_to_equations; lia| right; right| right; right].
    - exists TAPE, NT. split; [exact INT| lia].
    - exists SBUF, NS. split; [exact INS| lia]. }
  unfold shad, SHB.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_walkO1 usp S1 f lo ra gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 t3 t4 t5 t6 j24 F fc m);
                   [lia| lia| lia| exact FD0| exact FSELF| ul| lia| ul| exact F24| exact RES0| exact FS0| exact MI0]|].
  cbv beta. intros ms1 (m1 & -> & MU1 & WM1 & MI1 & F24a & _ & FS1). apply evt_done.
  assert (INCL0 : forall e, In e L -> In e (rt_live RT Σ)) by (intros e He; rewrite LVE; exact He).
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 S1 ART0 ltac:(ul)); [| exact WM1]. eapply (CLW Σ); [exact FRS| exact INCL0| exact MU1|].
    constructor; [intros x Hx; cbn [fst snd] in Hx; left; lia|].
    constructor; [intros x Hx; cbn [fst snd] in Hx; right; right; left; lia|]. constructor. }
  assert (AG01 : forall P : Z -> Prop, (forall x, P x -> ~ (S1 + 24 <= x < S1 + 32) /\ ~ (f / 8 + 2147450880 + 34 <= x < f / 8 + 2147450880 + 70)) -> agree_on P m m1).
  { intros P HP a Ha. apply MU1. cbn [outside]. destruct (HP _ Ha) as [H1 H2]. split; [exact H1| split; [exact H2| exact I]]. }
  assert (ST1 : stk asegs m1 lo S1) by (apply (stk_agree asegs m m1 _ _ ST0); [| exact WM1]; apply AG01; intros x Hx; lia).
  assert (LOC1 : pj_locA m1) by (apply (pj_locA_agree m m1 LOC0); apply AG01; intros x Hx; unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx; ul).
  assert (NL1 : libc_nl m1) by (apply (libc_nl_agree m m1 NL0); apply AG01; intros x Hx; unfold LIBC_NL in Hx; ul).
  assert (LOCKW1 : lockwA m1) by (apply (lockwA_agree m m1 LOCKW0); apply AG01; intros x Hx; unfold PJ_LOCKW_A in Hx; ul).
  assert (IOS1 : io_ssp m1).
  { destruct IOS0 as (g & G1 & G2). exists g. split; [apply (ro_cells_agree asegs m m1 _ _ G1)| apply (ro_cells_agree asegs m m1 _ _ G2)]; apply AG01; intros x Hx;
      cbn [cells_size csize Nat.add] in Hx; ul. }
  assert (FO1 : rw_cells asegs m1 (f + 272) [CB 288 jos]) by (eapply rw_cells_agree_nw; [exact FO0|]; apply AG01; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia).
  assert (FB1 : rw_cells asegs m1 (f + 32) [CB 88 jsb]) by (eapply rw_cells_agree_nw; [exact FB0|]; apply AG01; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia).
  assert (OSH1 : os_hullA m1 (f + 272)).
  { split; [exists jos; exact FO1|]. unfold shad, SHB. replace ((f + 272) / 8 + 2147450880) with (f / 8 + 2147450880 + 34) by (Z.div_mod_to_equations; lia).
    exact (shadow_o_os m1 _ FS1). }
  assert (DR1 : DOCREPA (mkPJA lo f 4%nat (f + 32) (f + 184) TAPE NT SBUF NS tws sbs len L) m1).
  { apply (DOCREPA_agree _ m m1 DR0). apply AG01. intros x Hx. destruct (DRC x Hx) as [H|[H|(p & k & Hin & Hr)]]; [lia| lia| pose proof (LRNG p k Hin); lia]. }
  assert (PRES1 : forall a : word, aclient L [(f, 4%nat)] S1 (bv_unsigned a) -> outside (okW S1 f) (bv_unsigned a) -> m1 a = m a).
  { intros a _ Ho. apply MU1. outW Ho. }
  clear MU1 WM1 ST0 MI0 LOC0 NL0 LOCKW0 IOS0 FO0 FB0 FS0 F24 RES0 DR0.

  unfold pk_regs.
  eapply (CTOR Σ K (f + 272) S1 lo f 4%nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1
            FDO MST ltac:(rewrite FRS; left; reflexivity) ltac:(lia) ltac:(change (fs_size 4) with 1024; lia) ltac:(Z.div_mod_to_equations; lia)
            OSH1 LOC1 NL1 LOCKW1 IOS1 ART1 MI1 ST1 SPLO ltac:(ul) ltac:(ul) ltac:(Z.div_mod_to_equations; lia)).
  intros u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 m2 ART2 MI2 ST2 OSF2 OSH2 LOCB2 PRES2.
  rewrite (ret_pc_even 0xb1928) by lia.
  assert (AG12 : forall P : Z -> Prop, (forall x, P x -> okcl S1 usp f L x /\ ~ (PJ_LOC_LO_A <= x < PJ_LOC_HI_A) /\ ~ (f + 272 <= x < f + 560)) -> agree_on P m1 m2).
  { intros P HP a Ha. destruct (HP _ Ha) as (H1 & H2 & H3). apply PRES2; [exact (CLA Σ _ FRS INCL0 H1)|].
    cbn [outside]. split; [exact H2| split; [lia| exact I]]. }
  assert (FS2 : rw_cells asegs m2 (f / 8 + 2147450880) (map C1 pj_shadow_o)).
  { eapply rw_cells_agree_nw; [exact FS1|]. apply AG12. intros x Hx. rewrite cells_size_map_C1' in Hx. unfold pj_shadow_o in Hx.
    rewrite !app_length, !repeat_length in Hx. unfold PJ_LOC_LO_A, PJ_LOC_HI_A. split; [right; right; left; lia| lia]. }
  assert (F24b : rw_cells asegs m2 (S1 + 24) [C8 (Z_to_bv 64 (f + 160))]).
  { eapply rw_cells_agree_nw; [exact F24a|]. apply AG12. intros x Hx. cbn [cells_size csize Nat.add] in Hx. unfold PJ_LOC_LO_A, PJ_LOC_HI_A. split; [left; lia| ul]. }
  assert (FB2 : rw_cells asegs m2 (f + 32) [CB 88 jsb]).
  { eapply rw_cells_agree_nw; [exact FB1|]. apply AG12. intros x Hx. cbn [cells_size csize Nat.add] in Hx. unfold PJ_LOC_LO_A, PJ_LOC_HI_A. split; [right; left; lia| lia]. }
  assert (DR2 : DOCREPA (mkPJA lo f 4%nat (f + 32) (f + 184) TAPE NT SBUF NS tws sbs len L) m2).
  { apply (DOCREPA_agree _ m1 m2 DR1). apply AG12. intros x Hx. unfold PJ_LOC_LO_A, PJ_LOC_HI_A.
    destruct (DRC x Hx) as [H|[H|(p & k & Hin & Hr)]]; [split; [right; left; lia| lia]| split; [right; right; left; lia| lia]|].
    pose proof (LRNG p k Hin). split; [do 4 right; exists p, k; split; [exact Hin| lia]| lia]. }
  assert (PRES2' : forall a : word, aclient L [(f, 4%nat)] S1 (bv_unsigned a) -> outside (okW S1 f) (bv_unsigned a) -> m2 a = m a).
  { intros a Ha Ho. rewrite <- (PRES1 a Ha Ho). apply PRES2; [rewrite LVE, FRS; exact Ha|]. outW Ho. }
  clear AG01 PRES1 ART1 MI1 ST1 LOC1 NL1 LOCKW1 IOS1 FO1 FB1 OSH1 FS1 F24a DR1.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_walkO2 usp S1 f lo (Z_to_bv 64 0xb1928) gp u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 (f + 160)) (Z_to_bv 64 (f + 272))
                             (Z_to_bv 64 (f + 184)) (Z_to_bv 64 1) s8 s9 u3 u4 u5 u6 F2 fc m2); [lia| lia| lia| exact FD0| exact FSELF| ul| ul| exact FS2| exact MI2]|].
  cbv beta. intros ms3 (m3 & -> & MU3 & WM3 & MI3 & FS3). apply evt_done.
  assert (ART3 : ART RT Σ m3).
  { apply (art_client_write RT AF Σ m2 m3 S1 ART2 ltac:(ul)); [| exact WM3]. eapply (CLW Σ); [exact FRS| exact INCL0| exact MU3|].
    constructor; [intros x Hx; cbn [fst snd] in Hx; right; right; left; lia|]. constructor. }
  assert (AG23 : forall P : Z -> Prop, (forall x, P x -> ~ (f / 8 + 2147450880 + 4 <= x < f / 8 + 2147450880 + 15)) -> agree_on P m2 m3).
  { intros P HP a Ha. apply MU3. cbn [outside]. split; [exact (HP _ Ha)| exact I]. }
  assert (ST3 : stk asegs m3 lo S1) by (apply (stk_agree asegs m2 m3 _ _ ST2); [| exact WM3]; apply AG23; intros x Hx; lia).
  assert (FB3 : rw_cells asegs m3 (f + 32) [CB 88 jsb]) by (eapply rw_cells_agree_nw; [exact FB2|]; apply AG23; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia).
  assert (PRES3 : forall a : word, aclient L [(f, 4%nat)] S1 (bv_unsigned a) -> outside (okW S1 f) (bv_unsigned a) -> m3 a = m a).
  { intros a Ha Ho. rewrite <- (PRES2' a Ha Ho). apply MU3. outW Ho. }

  assert (CD3 : checked_dst RT Σ m3 (Z_to_bv 64 S1) (f + 32) 64).
  { unfold checked_dst. rewrite EU. split; [| split].
    - intros _. split.
      + apply (acc_sub asegs m3 (f + 32) 88); [| lia| lia]. change 88 with (8 * Z.of_nat 11).
        apply (acc_zero_run asegs m3 (f + 32) 11); [Z.div_mod_to_equations; lia| lia|].
        unfold shad, SHB. replace ((f + 32) / 8 + 2147450880) with (f / 8 + 2147450880 + 4) by (Z.div_mod_to_equations; lia). exact (shadow_oo_sb m3 _ FS3).
      + right; left. exists f, 4%nat. change (fs_size 4) with 1024. split; [rewrite FRS; left; reflexivity| lia].
    - intros i Hi. right; right; right; left. exists f, 4%nat. change (fs_size 4) with 1024. split; [rewrite FRS; left; reflexivity| lia].
    - apply (rw_cells_wr_at asegs m3 (f + 32) [CB 88 jsb] 64 FB3). cbn. lia. }
  assert (COK3 : call_ok RT Σ m3 (Z_to_bv 64 S1) lo).
  { unfold call_ok. rewrite EU. split; [exact ST3|]. split; [exact SPLO|]. split; [ul|]. split; [ul| Z.div_mod_to_equations; lia]. }
  unfold pk_regs.
  eapply (aevt_memsetP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc m3 (f + 32) 64 z8 lo eq_refl eq_refl eq_refl
            ltac:(ul) ltac:(lia) CD3 ART3 MI3 COK3).
  intros v0 v1 v2 e1 e2 e3 e4 e5 e6 e7 v3 v4 v5 v6 F4 m4 (ART4 & MI4 & WM4 & ST4) PRES4 BY4. rewrite EU in ST4, PRES4.
  rewrite (ret_pc_even 0xb1970) by lia. change (Z.to_nat 64) with 64%nat in BY4.
  assert (AG34 : forall P : Z -> Prop, (forall x, P x -> okcl S1 usp f L x /\ ~ (f + 32 <= x < f + 32 + 64)) -> agree_on P m3 m4).
  { intros P HP a Ha. destruct (HP _ Ha) as (H1 & H2). apply PRES4; [exact (CLA Σ _ FRS INCL0 H1)| exact H2]. }
  assert (FS4 : rw_cells asegs m4 (f / 8 + 2147450880) (map C1 pj_shadow_oo)).
  { eapply rw_cells_agree_nw; [exact FS3|]. apply AG34. intros x Hx. rewrite cells_size_map_C1' in Hx. unfold pj_shadow_oo in Hx.
    rewrite !app_length, !repeat_length in Hx. split; [right; right; left; lia| lia]. }
  assert (F24d : rw_cells asegs m4 (S1 + 24) [C8 (Z_to_bv 64 (f + 160))]).
  { eapply rw_cells_agree_nw; [exact F24b|]. eapply agree_trans; [apply AG23| apply AG34]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; [lia| split; [left; lia| ul]]. }
  assert (OSAG24 : agree_on (fun a => f + 272 <= a < f + 272 + 288) m2 m4).
  { eapply agree_trans; [apply AG23| apply AG34]; intros x Hx; [lia| split; [right; left; lia| lia]]. }
  assert (LOCB4 : LOCBA m4).
  { apply (LOCBA_agree m2 m4 LOCB2). eapply agree_trans; [apply AG23| apply AG34]; intros x Hx; unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx; [lia| split; [right; right; right; left; unfold PJ_LOC_LO_A, PJ_LOC_HI_A; lia| lia]]. }
  assert (DR4 : DOCREPA (mkPJA lo f 4%nat (f + 32) (f + 184) TAPE NT SBUF NS tws sbs len L) m4).
  { apply (DOCREPA_agree _ m2 m4 DR2). eapply agree_trans; [apply AG23| apply AG34]; intros x Hx;
      (destruct (DRC x Hx) as [H|[H|(p & k & Hin & Hr)]]; [| | pose proof (LRNG p k Hin)]); [lia| lia| lia| | |].
    - split; [right; left; lia| lia]. - split; [right; right; left; lia| lia]. - split; [do 4 right; exists p, k; split; [exact Hin| lia]| lia]. }
  assert (PRES4' : forall a : word, aclient L [(f, 4%nat)] S1 (bv_unsigned a) -> outside (okW S1 f) (bv_unsigned a) -> m4 a = m a).
  { intros a Ha Ho. rewrite <- (PRES3 a Ha Ho). apply PRES4; [rewrite LVE, FRS; exact Ha|]. outW Ho. }

  destruct (wr_at_rw_CB m4 (f + 32) 88 (wr_at_transport asegs m3 m4 _ _ (rw_cells_wr_at asegs m3 (f + 32) [CB 88 jsb] 88 FB3 ltac:(cbn; lia)) WM4) ltac:(lia)) as (jsb4 & FB4).
  change (Z.to_nat 88) with 88%nat in FB4.
  pose proof FB4 as SC4. apply (rw_cells_split_CB asegs _ _ [] 88 _ [] [64; 8; 8; 8]%nat) in SC4; [| reflexivity]. cbn [mk_CB_cells app] in SC4.
  repeat match type of SC4 with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "q" in set (j := t) in SC4; clearbody j end.
  lazymatch type of SC4 with rw_cells _ _ _ (?c0 :: ?rest) => change (c0 :: rest) with ([c0] ++ rest) in SC4 end.
  apply Sj_stage1_kit.rw_cells_app in SC4. destruct SC4 as [ARR4 SC4]. cbn [cells_size csize Nat.add] in SC4.
  replace (f + 32 + Z.of_nat 64) with (f + 96) in SC4 by lia.
  clear AG12 AG23 PRES2' PRES3 ART2 MI2 ST2 FS2 F24b FB2 DR2 ART3 MI3 ST3 FB3 FS3 CD3 COK3 MU3 WM3.

  apply (aevt_evt RT AF PMc MST).
  lazymatch type of SC4 with rw_cells _ _ _ [CB 8 ?x0; CB 8 ?x1; CB 8 ?x2] =>
    eapply evt_cut; [eapply (pj_walkS usp S1 f lo (Z_to_bv 64 0xb1970) gp v0 v1 v2 (Z_to_bv 64 (f + 32)) e1 e2 e3 e4 e5 e6 e7 (Z_to_bv 64 (f + 272)) v3 v4 v5 v6
                               x0 x1 x2 F4 fc m4); [lia| lia| lia| exact FD0| exact FSELF| ul| ul| exact SC4| exact FS4| exact MI4]|]
  end.
  cbv beta. intros ms5 (m5 & a3' & -> & MU5 & WM5 & MI5 & SC5 & FS5). apply evt_done.
  assert (ART5 : ART RT Σ m5).
  { apply (art_client_write RT AF Σ m4 m5 S1 ART4 ltac:(ul)); [| exact WM5]. eapply (CLW Σ); [exact FRS| exact INCL0| exact MU5|].
    constructor; [intros x Hx; cbn [fst snd] in Hx; right; left; lia|]. constructor. }
  assert (AG45 : forall P : Z -> Prop, (forall x, P x -> ~ (f + 96 <= x < f + 120)) -> agree_on P m4 m5).
  { intros P HP a Ha. apply MU5. cbn [outside]. split; [exact (HP _ Ha)| exact I]. }
  assert (ST5 : stk asegs m5 lo S1) by (apply (stk_agree asegs m4 m5 _ _ ST4); [| exact WM5]; apply AG45; intros x Hx; lia).
  lazymatch type of ARR4 with rw_cells _ _ _ [CB 64 ?ji] =>
    assert (ARR5 : rw_cells asegs m5 (f + 32) [CB 64 ji]) by (eapply rw_cells_agree_nw; [exact ARR4|]; apply AG45; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia)
  end.
  assert (I5 : SBINVA (mkPJA lo f 4%nat (f + 32) (f + 184) TAPE NT SBUF NS tws sbs len L) m5 (sbA0 (f + 32))).
  { unfold SBINVA. cbn [pa_SB pa_len pa_lo sa_buf sa_size sa_cap sa_heap sa_k sbA0].
    replace (f + 32 + 64) with (f + 96) by lia. change (Z.to_nat 64) with 64%nat. change (64 * 2 ^ 0) with 64.
    split; [exact SC5|]. split; [lia|]. split; [eexists; exact ARR5|]. split; [eexists; exact ARR5|].
    split; [unfold shad, SHB; replace ((f + 32) / 8 + 2147450880) with (f / 8 + 2147450880 + 4) by (Z.div_mod_to_equations; lia); exact (shadow_oo_sb m5 _ FS5)|].
    split; [lia|]. repeat split; reflexivity. }
  assert (DR5 : DOCREPA (mkPJA lo f 4%nat (f + 32) (f + 184) TAPE NT SBUF NS tws sbs len L) m5).
  { apply (DOCREPA_agree _ m4 m5 DR4). apply AG45. intros x Hx. destruct (DRC x Hx) as [H|[H|(p & k & Hin & Hr)]]; [lia| lia| pose proof (LRNG p k Hin); lia]. }
  assert (F24e : rw_cells asegs m5 (S1 + 24) [C8 (Z_to_bv 64 (f + 160))]) by (eapply rw_cells_agree_nw; [exact F24d|]; apply AG45; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia).
  assert (OSAG25 : agree_on (fun a => f + 272 <= a < f + 272 + 288) m2 m5) by (eapply agree_trans; [exact OSAG24|]; apply AG45; intros x Hx; lia).
  assert (LOCB5 : LOCBA m5) by (apply (LOCBA_agree m4 m5 LOCB4); apply AG45; intros x Hx; unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx; lia).
  assert (PRES5 : forall a : word, aclient L [(f, 4%nat)] S1 (bv_unsigned a) -> outside (okW S1 f) (bv_unsigned a) -> m5 a = m a).
  { intros a Ha Ho. rewrite <- (PRES4' a Ha Ho). apply MU5. outW Ho. }
  assert (CR5 : 2 * (Z.of_nat (length tws) - 1 - 1) + pj_psi len (sbA0 (f + 32)) <= rt_credit RT Σ) by lia.
  assert (FC3 : fcount 3 (rt_frames RT Σ) + Z.of_nat TAPE_MAX_DEPTH + 1 <= FRAMES_MAX3).
  { rewrite FRS, fcount_cons, fcount_nil. unfold TAPE_MAX_DEPTH, FRAMES_MAX3. change (Z.of_nat 1024) with 1024. cbn. lia. }
  assert (FT : Z.of_nat (length (rt_frames RT Σ)) + 2 * Z.of_nat TAPE_MAX_DEPTH + 2 <= FRAMES_TOT).
  { rewrite FRS. unfold TAPE_MAX_DEPTH, FRAMES_TOT. change (Z.of_nat 1024) with 1024. change (Z.of_nat (length [(f, 4%nat)])) with 1. lia. }
  clear AG34 AG45 PRES4 PRES4' ART4 MI4 ST4 WM4 BY4 FB4 ARR4 SC4 FS4 MU5 WM5 F24d OSAG24 LOCB4.

  unfold pk_regs.
  eapply (SER Σ K (mkPJA lo f 4%nat (f + 32) (f + 184) TAPE NT SBUF NS tws sbs len L) (sbA0 (f + 32)) 1 (Z.of_nat (length tws) - 1) 0 (Z.of_nat (length sbs)) S1
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F4 fc m5 FDO MST OK LV I5 DR5 ELS ltac:(lia) ltac:(cbn [pa_tws]; lia) ltac:(lia) ltac:(cbn [pa_sbs]; lia)
            ltac:(unfold sb_acc1A; cbn [sa_size sbA0]; lia) ART5 MI5 ST5 ltac:(exact LOQ) ltac:(ul) ltac:(Z.div_mod_to_equations; lia) FRM FC3 FT LVB CR5).
  intros Σ6 st' y0 y1 y2 d0 d1 d2 d3 d4 d5 d6 d7 y3 y4 y5 y6 F6 fc6 m6 FRM6 ART6 MI6 ST6 I6 DR6 _ LV6 FRS6 SP6 CR6 PRES6.
  cbn [pa_lo pa_F pa_kF pa_SB pa_DOC pa_TAPE pa_NT pa_SBUF pa_NS pa_tws pa_sbs pa_len pa_L] in ST6, LV6, CR6, PRES6.
  rewrite (ret_pc_even 0xb199c) by lia.
  pose proof LV6 as (LVE6 & INF6 & _). rewrite FRS in FRS6.
  assert (INCL6 : forall e, In e L -> In e (rt_live RT Σ6)) by (intros e He; rewrite LVE6; apply in_or_app; right; exact He).
  pose proof (pj_psi_nonneg _ m6 st' OK I6) as PSI6. cbn [pa_len] in PSI6.
  pose proof I6 as (SC6 & SZC6 & (bs6 & BUF6) & (ji6 & ARR6) & SH6 & (K6 & KC6 & KM6) & HB6). cbn [pa_SB pa_len pa_lo] in SC6, BUF6, ARR6, SH6, KM6, HB6.
  replace (f + 32 + 64) with (f + 96) in SC6 by lia.
  pose proof (SBINVA_cap_pos _ m6 st' I6) as CAP64.
  assert (BUFR : 0 < sa_buf st' /\ sa_buf st' + sa_cap st' <= lo /\ (sa_heap st' = true -> f + 1024 <= sa_buf st' \/ sa_buf st' + sa_cap st' <= f) /\ (sa_heap st' = false -> sa_buf st' = f + 32)).
  { destruct (sa_heap st') eqn:HP.
    - destruct HB6 as (B1 & B2 & B3). pose proof (proj2 (proj2 (proj2 (af_frames_range RT AF Σ6 m6 f 4%nat ART6 INF6))) (sa_buf st') (sa_cap st')
                                                       ltac:(rewrite LVE6; unfold sbchunkA; rewrite HP; left; reflexivity)) as Y. change (fs_size 4) with 1024 in Y.
      split; [lia|]. split; [lia|]. split; [intros _; lia| intros; congruence].
    - destruct HB6 as (B1 & B2 & _). split; [lia|]. split; [lia|]. split; [intros; congruence| intros _; exact B1]. }
  destruct BUFR as (BUFP & BUFLO & BHEAP & BINL).
  assert (AG56 : forall P : Z -> Prop, (forall x, P x -> okcl S1 usp f L x /\ ~ (f + 32 <= x < f + 32 + 88)) -> agree_on P m5 m6).
  { intros P HP a Ha. destruct (HP _ Ha) as (H1 & H2). apply PRES6; [| cbn [outside]; split; [exact H2| exact I]].
    rewrite FRS. pose proof (CLA Σ _ FRS INCL0 H1) as C. rewrite LVE, FRS in C. exact C. }
  assert (FS6 : rw_cells asegs m6 (f / 8 + 2147450880) (map C1 pj_shadow_oo)).
  { eapply rw_cells_agree_nw; [exact FS5|]. apply AG56. intros x Hx. rewrite cells_size_map_C1' in Hx. unfold pj_shadow_oo in Hx.
    rewrite !app_length, !repeat_length in Hx. split; [right; right; left; lia| lia]. }
  assert (F24f : rw_cells asegs m6 (S1 + 24) [C8 (Z_to_bv 64 (f + 160))]).
  { eapply rw_cells_agree_nw; [exact F24e|]. apply AG56. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; lia| ul]. }
  assert (OSF6 : OSFRESHA m6 (f + 272)).
  { apply (OSF_loc m2 m6 _ OSF2). eapply agree_trans; [exact OSAG25|]. apply AG56. intros x Hx. split; [right; left; lia| lia]. }
  assert (OSH6 : os_hullA m6 (f + 272)).
  { split.
    - destruct OSH2 as [(bo & FO2) _]. exists bo. eapply rw_cells_agree_nw; [exact FO2|]. eapply agree_trans; [exact OSAG25|]. apply AG56.
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [right; left; lia| lia].
    - unfold shad, SHB. replace ((f + 272) / 8 + 2147450880) with (f / 8 + 2147450880 + 34) by (Z.div_mod_to_equations; lia). exact (shadow_oo_os m6 _ FS6). }
  assert (LOCB6 : LOCBA m6).
  { apply (LOCBA_agree m5 m6 LOCB5). apply AG56. intros x Hx. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. split; [right; right; right; left; unfold PJ_LOC_LO_A, PJ_LOC_HI_A; lia| lia]. }
  assert (PRES6' : forall a : word, aclient L [(f, 4%nat)] S1 (bv_unsigned a) -> outside (okW S1 f) (bv_unsigned a) -> m6 a = m a).
  { intros a Ha Ho. rewrite <- (PRES5 a Ha Ho). apply PRES6; [rewrite FRS; exact Ha|]. outW Ho. }
  assert (ACC6 : acc asegs m6 (sa_buf st') (sa_size st')).
  { apply (acc_sub asegs m6 (sa_buf st') (sa_cap st')); [| lia| lia]. exact (SBINVA_acc RT AF Σ6 _ m6 st' OK LV6 ART6 I6). }
  assert (BCLS : buf_clsA RT Σ6 f 4%nat (sa_buf st') (sa_cap st')).
  { unfold buf_clsA. destruct (sa_heap st') eqn:HP.
    - left. exists (sa_buf st'), (sa_cap st'). split; [rewrite LVE6; unfold sbchunkA; rewrite HP; left; reflexivity| lia].
    - right. rewrite (BINL eq_refl). destruct HB6 as (_ & -> & _). change (fs_size 4) with 1024. lia. }
  assert (BSEP : sa_buf st' + sa_cap st' <= f + 272 \/ f + 272 + 288 <= sa_buf st').
  { destruct (sa_heap st') eqn:HP; [destruct (BHEAP eq_refl); lia|]. rewrite (BINL eq_refl). destruct HB6 as (_ & -> & _). lia. }
  assert (BR : 0 <= sa_buf st' < 2^64 /\ 0 <= sa_size st' < 2^64 /\ 0 <= sa_cap st' < 2^64) by ul.
  clear PRES5 ART5 MI5 ST5 I5 DR5 FS5 SC5 ARR5 F24e LOCB5 DR4 OSAG25 CR5.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_walkP usp S1 f (sa_buf st') (sa_size st') (sa_cap st') (Z_to_bv 64 0xb199c) gp y0 y1 y2 d0 d1 d2 d3 d4 d5 d6 d7 (Z_to_bv 64 64)
                             (Z_to_bv 64 (f + 184)) (Z_to_bv 64 1) y3 y4 y5 y6 F6 fc6 m6); [lia| ul| lia| lia| lia| exact SC6| exact MI6]|].
  cbv beta. intros ms7 <-. apply evt_done.

  unfold pk_regs.
  eapply (PUT Σ6 K (f + 272) (sa_buf st') (sa_size st') (sa_cap st') S1 lo f 4%nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F6 fc6 m6 bs6
            FDO MST ltac:(rewrite FRS6; left; reflexivity) ltac:(lia) ltac:(change (fs_size 4) with 1024; lia) ltac:(Z.div_mod_to_equations; lia)
            OSF6 OSH6 LOCB6 BUF6 SZC6 BUFP BUFLO ACC6 BCLS BSEP ART6 MI6 ST6 ltac:(rewrite SP6; exact SPLO) ltac:(ul) ltac:(ul) ltac:(Z.div_mod_to_equations; lia)
            ltac:(rewrite FRS6; change (Z.of_nat (length [(f, 4%nat)])) with 1; unfold FRAMES_TOT; lia) ltac:(lia)).
  intros Σ7 x0 x1 x2 c0 c1 c2 c3 c4 c5 c6 c7 x3 x4 x5 x6 F7 m7 ART7 MI7 ST7 OSU7 OSH7 LV7 FRS7 SP7 CR7 PRES7.
  rewrite (ret_pc_even 0xb19b0) by lia. rewrite FRS6 in FRS7, PRES7.
  assert (INCL7 : forall e, In e L -> In e (rt_live RT Σ7)) by (intros e He; rewrite LV7; exact (INCL6 e He)).
  assert (AG67 : forall P : Z -> Prop, (forall x, P x -> okcl S1 usp f L x /\ ~ (f + 272 <= x < f + 272 + 288)) -> agree_on P m6 m7).
  { intros P HP a Ha. destruct (HP _ Ha) as (H1 & H2). apply PRES7; [| cbn [outside]; split; [exact H2| exact I]].
    pose proof (CLA Σ6 _ FRS6 INCL6 H1) as C. rewrite FRS6 in C. exact C. }
  assert (FS7 : rw_cells asegs m7 (f / 8 + 2147450880) (map C1 pj_shadow_oo)).
  { eapply rw_cells_agree_nw; [exact FS6|]. apply AG67. intros x Hx. rewrite cells_size_map_C1' in Hx. unfold pj_shadow_oo in Hx.
    rewrite !app_length, !repeat_length in Hx. split; [right; right; left; lia| lia]. }
  assert (F24g : rw_cells asegs m7 (S1 + 24) [C8 (Z_to_bv 64 (f + 160))]).
  { eapply rw_cells_agree_nw; [exact F24f|]. apply AG67. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; lia| ul]. }
  assert (SC7 : rw_cells asegs m7 (f + 96) [C8 (Z_to_bv 64 (sa_buf st')); C8 (Z_to_bv 64 (sa_size st')); C8 (Z_to_bv 64 (sa_cap st'))]).
  { eapply rw_cells_agree_nw; [exact SC6|]. apply AG67. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [right; left; lia| lia]. }
  assert (FB7 : exists bb, rw_cells asegs m7 (f + 32) [CB 88 bb]).
  { assert (ARR7 : rw_cells asegs m7 (f + 32) [CB 64 ji6]) by (eapply rw_cells_agree_nw; [exact ARR6|]; apply AG67; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]).
    assert (FB7' : rw_cells asegs m7 (f + 32) ([CB 64 ji6] ++ [C8 (Z_to_bv 64 (sa_buf st')); C8 (Z_to_bv 64 (sa_size st')); C8 (Z_to_bv 64 (sa_cap st'))])).
    { apply Sj_stage1_kit.rw_cells_app. split; [exact ARR7|]. cbn [cells_size csize Nat.add]. replace (f + 32 + Z.of_nat 64) with (f + 96) by lia. exact SC7. }
    exact (rw_cells_forget asegs m7 (f + 32) _ FB7'). }
  assert (LOCB7 : LOCBA m7).
  { apply (LOCBA_agree m6 m7 LOCB6). apply AG67. intros x Hx. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. split; [right; right; right; left; unfold PJ_LOC_LO_A, PJ_LOC_HI_A; lia| lia]. }
  assert (PRES7' : forall a : word, aclient L [(f, 4%nat)] S1 (bv_unsigned a) -> outside (okW S1 f) (bv_unsigned a) -> m7 a = m a).
  { intros a Ha Ho. rewrite <- (PRES6' a Ha Ho). apply PRES7; [| outW Ho].
    apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact INCL6| intros e He; exact He| lia]. }
  destruct OSH7 as [(bo7 & FO7) _].
  pose proof (OSU_imp m7 _ OSU7) as IMP7. replace (f + 272 + 8) with (f + 280) in IMP7 by lia.
  assert (IOS7 : forall m', agree_on (fun a => f + 408 <= a < f + 560) m7 m' -> OSIOSA m' (f + 272)).
  { intros m' AG. apply (OSU_ios m7 m' _ OSU7). intros a Ha. apply AG. lia. }
  assert (CRED7 : rt_credit RT Σ - (2 * Z.of_nat (length tws) + 2 + 2^30) <= rt_credit RT Σ7) by lia.
  clear AG56 AG67 PRES6 PRES6' ART6 MI6 ST6 FS6 F24f OSF6 OSH6 LOCB6 ACC6 BCLS BSEP SC6 ARR6 BUF6 SH6 OSF2 OSH2 LOCB2 PRES2 CR6 OSU7.

  assert (TAILR : forall (Σy : rts RT) (my : mem) (ra' w0 w1 w2 b0' b1' b2' b3' b4' b5' b6' b7' z6 z7 w3 w4 w5 w6 : word) (Fy : bvmap 5 word) (bo bb : list byte),
    rt_live RT Σy = L -> rt_frames RT Σy = [(f, 4%nat)] -> rt_sp0 RT Σy = rt_sp0 RT Σ ->
    rt_credit RT Σ - (2 * Z.of_nat (length tws) + 2 + 2^30) <= rt_credit RT Σy ->
    ART RT Σy my -> mem_inv asegs my -> stk asegs my lo S1 ->
    rw_cells asegs my (f + 272) [CB 288 bo] -> rw_cells asegs my (f + 280) [C8 (Z_to_bv 64 PJ_LOC_IMP_A)] ->
    (forall m', agree_on (fun a => f + 408 <= a < f + 560) my m' -> OSIOSA m' (f + 272)) ->
    rw_cells asegs my (f / 8 + 2147450880) (map C1 pj_shadow_oo) ->
    rw_cells asegs my (S1 + 24) [C8 (Z_to_bv 64 (f + 160))] -> rw_cells asegs my (f + 32) [CB 88 bb] -> LOCBA my ->
    (forall a : word, aclient L [(f, 4%nat)] S1 (bv_unsigned a) -> outside (okW S1 f) (bv_unsigned a) -> my a = m a) ->
    aevt RT PMc Σy K (pk_regs 0xb19c4 ra' S1 gp w0 w1 w2 usp b0' b1' b2' b3' b4' b5' b6' b7' f (Z_to_bv 64 (f + 160)) (Z_to_bv 64 (f + 272)) z6 z7
                               (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) w3 w4 w5 w6 Fy fc6 my)).
  { intros Σy my ra' w0 w1 w2 b0' b1' b2' b3' b4' b5' b6' b7' z6 z7 w3 w4 w5 w6 Fy bo bb LVy FRSy SPy CRy ARTy MIy STy FOy IMPy IOSy FSy F24y FBy LOCBy PRESy.
    assert (INCLy : forall e, In e L -> In e (rt_live RT Σy)) by (intros e He; rewrite LVy; exact He).
    assert (SPLOy : rt_sp0 RT Σy - STACK_WIN <= lo) by (rewrite SPy; exact SPLO).

    pose proof (proj1 (proj2 (ROA Σy my ARTy))) as GOT. unfold PJ_GOT_VT_A, PJ_SB_BVT_A, PJ_IOS_BVT_A in GOT.

    pose proof FOy as FO8. apply (rw_cells_split_CB asegs _ _ [] 288 _ [] [8; 280]%nat) in FO8; [| reflexivity]. cbn [mk_CB_cells app] in FO8.
    lazymatch type of FO8 with rw_cells _ _ _ (?c0 :: ?rest) => change (c0 :: rest) with ([c0] ++ rest) in FO8 end.
    apply Sj_stage1_kit.rw_cells_app in FO8. destruct FO8 as [FV8 FO8]. cbn [cells_size csize Nat.add] in FO8. replace (f + 272 + Z.of_nat 8) with (f + 280) in FO8 by lia.
    repeat match type of FO8 with context [CB ?k ?t] => lazymatch t with skipn _ _ => idtac end; let j := fresh "q" in set (j := t) in FO8; clearbody j end.
    repeat match type of FV8 with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "q" in set (j := t) in FV8; clearbody j end.

    apply (aevt_evt RT AF PMc MST).
    lazymatch type of FV8 with rw_cells _ _ _ [CB 8 ?jv] =>
      eapply evt_cut; [eapply (pj_walkR1 usp S1 f lo ra' gp w0 w1 w2 b0' b1' b2' b3' b4' b5' b6' b7' (Z_to_bv 64 (f + 160)) z6 z7 w3 w4 w5 w6 jv Fy fc6 my);
                       [lia| lia| lia| exact FD0| exact FSELF| ul| ul| exact FV8| exact GOT| exact FSy| exact MIy]|]
    end.
    cbv beta. intros ms9 (m9 & a1' & -> & MU9 & WM9 & MI9 & FV9 & FS9).
    assert (ART9 : ART RT Σy m9).
    { apply (art_client_write RT AF Σy my m9 S1 ARTy ltac:(ul)); [| exact WM9]. eapply (CLW Σy); [exact FRSy| exact INCLy| exact MU9|].
      constructor; [intros x Hx; cbn [fst snd] in Hx; right; right; left; lia|].
      constructor; [intros x Hx; cbn [fst snd] in Hx; right; left; lia|]. constructor. }
    assert (AG89 : forall P : Z -> Prop, (forall x, P x -> ~ (f / 8 + 2147450880 + 4 <= x < f / 8 + 2147450880 + 15) /\ ~ (f + 272 <= x < f + 280)) -> agree_on P my m9).
    { intros P HP a Ha. apply MU9. cbn [outside]. destruct (HP _ Ha) as [H1 H2]. split; [exact H1| split; [exact H2| exact I]]. }
    assert (ST9 : stk asegs m9 lo S1) by (apply (stk_agree asegs my m9 _ _ STy); [| exact WM9]; apply AG89; intros x Hx; lia).
    assert (IMP9 : rw_cells asegs m9 (f + 280) [C8 (Z_to_bv 64 PJ_LOC_IMP_A)]) by (eapply rw_cells_agree_nw; [exact IMPy|]; apply AG89; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia).
    assert (LOCB9 : LOCBA m9) by (apply (LOCBA_agree my m9 LOCBy); apply AG89; intros x Hx; unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx; lia).
    assert (FO9 : exists bo9, rw_cells asegs m9 (f + 272) [CB 288 bo9]).
    { lazymatch type of FO8 with rw_cells _ _ _ [CB 280 ?t] =>
        assert (FO9' : rw_cells asegs m9 (f + 280) [CB 280 t]) by (eapply rw_cells_agree_nw; [exact FO8|]; apply AG89; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia);
        assert (FO9'' : rw_cells asegs m9 (f + 272) ([C8 (Z_to_bv 64 0x167900)] ++ [CB 280 t]))
          by (apply Sj_stage1_kit.rw_cells_app; split; [exact FV9|]; cbn [cells_size csize Nat.add]; replace (f + 272 + Z.of_nat 8) with (f + 280) by lia; exact FO9');
        exact (rw_cells_forget asegs m9 (f + 272) _ FO9'')
      end. }
    assert (IOS9 : OSIOSA m9 (f + 272)) by (apply IOSy; apply AG89; intros x Hx; lia).
    assert (PRES9 : forall a : word, aclient L [(f, 4%nat)] S1 (bv_unsigned a) -> outside (okW S1 f) (bv_unsigned a) -> m9 a = m a).
    { intros a Ha Ho. rewrite <- (PRESy a Ha Ho). apply MU9. outW Ho. }

    unfold pk_regs.
    eapply evt_cut; [eapply LOCD; [exact IMP9| exact LOCB9| exact MI9]|].
    cbv beta. intros ms10 (k0 & k1 & k2 & r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & k3 & k4 & k5 & k6 & ->).
    rewrite (ret_pc_even 0xb1a20) by lia.

    eapply evt_cut; [eapply (pj_walkR2 usp S1 f _ gp k0 k1 k2 r0 r1 r2 r3 r4 r5 r6 r7 (Z_to_bv 64 (f + 160)) z6 (Z_to_bv 64 (-8)) k3 k4 k5 k6 Fy fc6 m9); [lia| ul| exact MI9]|].
    cbv beta. intros ms11 <-. apply evt_done.

    assert (OSH9 : os_hullA m9 (f + 272)).
    { split; [exact FO9|]. unfold shad, SHB. replace ((f + 272) / 8 + 2147450880) with (f / 8 + 2147450880 + 34) by (Z.div_mod_to_equations; lia). exact (shadow_o_os m9 _ FS9). }
    unfold pk_regs.
    eapply (IOSD Σy K (f + 272) S1 lo f 4%nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fy fc6 m9
              FDO MST ltac:(rewrite FRSy; left; reflexivity) ltac:(lia) ltac:(change (fs_size 4) with 1024; lia) ltac:(Z.div_mod_to_equations; lia)
              IOS9 OSH9 LOCB9); [unfold unwind_ok; rewrite EU, unsigned_lit by ul; right; right; lia| exact ART9| exact MI9| exact ST9| exact SPLOy| ul| ul| Z.div_mod_to_equations; lia|].
    intros p0 p1 p2 o0 o1 o2 o3 o4 o5 o6 o7 p3 p4 p5 p6 F10 m10 ART10 MI10 ST10 OSH10 PRES10.
    rewrite (ret_pc_even 0xb1a28) by lia. rewrite FRSy in PRES10.
    assert (AG910 : forall P : Z -> Prop, (forall x, P x -> okcl S1 usp f L x /\ ~ (f + 272 + 136 <= x < f + 272 + 144)) -> agree_on P m9 m10).
    { intros P HP a Ha. destruct (HP _ Ha) as (H1 & H2). apply PRES10; [| cbn [outside]; split; [exact H2| exact I]].
      pose proof (CLA Σy _ FRSy INCLy H1) as C. rewrite FRSy in C. exact C. }
    assert (FS10 : rw_cells asegs m10 (f / 8 + 2147450880) (map C1 pj_shadow_o)).
    { eapply rw_cells_agree_nw; [exact FS9|]. apply AG910. intros x Hx. rewrite cells_size_map_C1' in Hx. unfold pj_shadow_o in Hx.
      rewrite !app_length, !repeat_length in Hx. split; [right; right; left; lia| lia]. }

    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [eapply (pj_walkR3 usp S1 f lo (Z_to_bv 64 0xb1a28) gp p0 p1 p2 o0 o1 o2 o3 o4 o5 o6 o7 (Z_to_bv 64 (f + 160)) z6 p3 p4 p5 p6 F10 fc6 m10);
                     [lia| lia| lia| exact FD0| exact FSELF| ul| ul| exact FS10| exact MI10]|].
    cbv beta. intros ms12 (m11 & -> & MU11 & WM11 & MI11 & FS11). apply evt_done.
    assert (ART11 : ART RT Σy m11).
    { apply (art_client_write RT AF Σy m10 m11 S1 ART10 ltac:(ul)); [| exact WM11]. eapply (CLW Σy); [exact FRSy| exact INCLy| exact MU11|].
      constructor; [intros x Hx; cbn [fst snd] in Hx; right; right; left; lia|]. constructor. }
    assert (AG911 : forall P : Z -> Prop, (forall x, P x -> okcl S1 usp f L x /\ ~ (f + 272 + 136 <= x < f + 272 + 144) /\ ~ (f / 8 + 2147450880 + 34 <= x < f / 8 + 2147450880 + 70)) ->
                     agree_on P m9 m11).
    { intros P HP. eapply agree_trans; [apply AG910; intros x Hx; destruct (HP _ Hx) as (H1 & H2 & _); split; [exact H1| exact H2]|].
      intros a Ha. apply MU11. cbn [outside]. split; [exact (proj2 (proj2 (HP _ Ha)))| exact I]. }
    unfold pk_regs. eapply HK.
    - exact FRM6.
    - exact ART11.
    - exact MI11.
    - apply (stk_agree asegs m10 m11 _ _ ST10); [| exact WM11]. intros a Ha. apply MU11. cbn [outside]. split; [lia| exact I].
    - rewrite LVy, LVE. reflexivity.
    - rewrite FRSy, FRS. reflexivity.
    - exact SPy.
    - exact CRy.
    - unfold rt_pres_fp, pj_okarm_W. cbn [pa_SB pa_F]. unfold shad, SHB. rewrite LVE, FRS. intros a Ha Ho.
      assert (Ho' : outside (okW S1 f) (bv_unsigned a)) by (outW Ho).
      rewrite <- (PRES9 a Ha Ho'). cbn [okW outside] in Ho'. rewrite (MU11 a) by (cbn [outside]; split; [lia| exact I]).
      apply PRES10; [rewrite LVy; exact Ha| cbn [outside]; split; [lia| exact I]].
    - apply (LOCBA_agree m9 m11 LOCB9). apply AG911. intros x Hx. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. split; [right; right; right; left; unfold PJ_LOC_LO_A, PJ_LOC_HI_A; lia| lia].
    - assert (F24z : rw_cells asegs m11 (S1 + 24) [C8 (Z_to_bv 64 (f + 160))]).
      { eapply rw_cells_agree_nw; [exact F24y|]. eapply agree_trans; [apply AG89| apply AG911]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; [lia| split; [left; lia| ul]]. }
      destruct (rw_cells_forget asegs m11 (S1 + 24) _ F24z) as (j24' & H24).
      destruct OSH10 as [(bo10 & FO10) _].
      exists j24', bb, bo10. split; [exact H24| split].
      + eapply rw_cells_agree_nw; [exact FBy|]. eapply agree_trans; [apply AG89| apply AG911]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; [lia| split; [right; left; lia| lia]].
      + eapply rw_cells_agree_nw; [exact FO10|]. intros a Ha. apply MU11. cbn [cells_size csize Nat.add] in Ha. cbn [outside]. split; [lia| exact I].
    - exact FS11. }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_walkD usp S1 f (sa_buf st') (sa_size st') (sa_cap st') (Z_to_bv 64 0xb19b0) gp x0 x1 x2 c0 c1 c2 c3 c4 c5 c6 c7 (Z_to_bv 64 64)
                             (Z_to_bv 64 (f + 272 + 128)) (Z_to_bv 64 1) x3 x4 x5 x6 F7 fc6 m7); [lia| ul| lia| lia| lia| ul| ul| exact SC7| exact F24g| exact MI7]|].
  destruct FB7 as (bb7 & FB7).
  cbv beta. intros ms8 [(EB & ->)|(NB & ->)]; apply evt_done.
  -
    destruct (sa_heap st') eqn:HP; [destruct (BHEAP eq_refl); exfalso; lia|].
    apply (TAILR Σ7 m7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F7 bo7 bb7);
      [rewrite LV7, LVE6; unfold sbchunkA; rewrite HP; reflexivity| exact FRS7| rewrite SP7; exact SP6| exact CRED7| exact ART7| exact MI7| exact ST7
      | exact FO7| exact IMP7| exact IOS7| exact FS7| exact F24g| exact FB7| exact LOCB7| exact PRES7'].
  -
    destruct (sa_heap st') eqn:HP; [| exfalso; exact (NB (BINL eq_refl))].
    assert (INB : In (sa_buf st', sa_cap st') (rt_live RT Σ7)) by (rewrite LV7, LVE6; unfold sbchunkA; rewrite HP; left; reflexivity).
    unfold pk_regs.
    eapply (aevt_delarr RT AF RC PMc FDO MST Σ7 K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F7 fc6 m7 (sa_buf st') (sa_cap st') lo INB eq_refl ART7 MI7).
    { unfold call_ok. rewrite EU, SP7, SP6. split; [exact ST7|]. split; [exact SPLO|]. split; [ul|]. split; [ul| Z.div_mod_to_equations; lia]. }
    { unfold unwind_ok. rewrite EU, unsigned_lit by ul. right; right. lia. }
    intros Σ8 v w0' w1' w2' g1 g2 g3 g4 g5 g6 g7 w3' w4' w5' w6' F8 m8 (ART8 & MI8 & ST8) PRES8 LV8 FRS8 SP8 CR8.
    rewrite EU in ST8, PRES8. rewrite (ret_pc_even 0xb19c4) by lia. rewrite FRS7 in FRS8, PRES8.
    assert (LV8' : rt_live RT Σ8 = L).
    { rewrite LV8. apply (live_remove_head RT AF Σ7 m7 (sa_buf st') (sa_cap st') L ART7); [rewrite LV7, LVE6; unfold sbchunkA; rewrite HP; reflexivity| lia| exact LPOS]. }
    rewrite LV8' in PRES8.
    assert (AG78 : forall P : Z -> Prop, (forall x, P x -> okcl S1 usp f L x) -> agree_on P m7 m8).
    { intros P HPP a Ha. apply PRES8. pose proof (CLA Σ8 _ FRS8 ltac:(intros e He; rewrite LV8'; exact He) (HPP _ Ha)) as C. rewrite LV8', FRS8 in C. exact C. }
    apply (TAILR Σ8 m8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F8 bo7 bb7);
      [exact LV8'| exact FRS8| rewrite SP8, SP7; exact SP6| rewrite CR8; exact CRED7| exact ART8| exact MI8| exact ST8| | | | | | | |].
    + eapply rw_cells_agree_nw; [exact FO7|]. apply AG78. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; left. lia.
    + eapply rw_cells_agree_nw; [exact IMP7|]. apply AG78. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; left. lia.
    + intros m' AG. apply IOS7. eapply agree_trans; [| exact AG]. apply AG78. intros x Hx. right; left. lia.
    + eapply rw_cells_agree_nw; [exact FS7|]. apply AG78. intros x Hx. rewrite cells_size_map_C1' in Hx. unfold pj_shadow_oo in Hx. rewrite !app_length, !repeat_length in Hx. right; right; left. lia.
    + eapply rw_cells_agree_nw; [exact F24g|]. apply AG78. intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. ul.
    + eapply rw_cells_agree_nw; [exact FB7|]. apply AG78. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; left. lia.
    + apply (LOCBA_agree m7 m8 LOCB7). apply AG78. intros x Hx. right; right; right; left. exact Hx.
    + intros a Ha Ho. rewrite <- (PRES7' a Ha Ho). apply PRES8. exact Ha.
Qed.

End Okarm.
