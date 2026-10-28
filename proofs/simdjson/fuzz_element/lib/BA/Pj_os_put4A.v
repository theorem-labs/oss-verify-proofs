(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_num_walk Sj_stage1_kit Pj_os_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Pj_lftoi1A Pj_defsA Pj_os_defsA Pj_os_put1A Pj_os_put3A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition ios_midA (OS : Z) (b0 b1 b2 b3 : Z) (j148 j284 : list byte) : list cell :=
  [C8 (wz PJ_OS_VPTR_A); C8 (wz PJ_IOS_VPTR_A); CB 4 [Z_to_bv 8 2; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0]; CB 4 j148; C8 (wz 6); C8 (wz 0); C4 (wz 0); C4 (wz 0);
   C8 (wz OS); C8 (wz PJ_LOC_IMP_A);
   C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0);
   C8 (wz 0); C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C1 (Z_to_bv 8 b2); C1 (Z_to_bv 8 b3); CB 4 j284].

Definition op_sh12 (b4 : Z) : list byte :=
  repeat (Z_to_bv 8 (-15)) 4 ++ [Z_to_bv 8 b4] ++ repeat (Z_to_bv 8 (-14)) 3 ++ [Z_to_bv 8 0; Z_to_bv 8 0] ++ repeat (Z_to_bv 8 (-13)) 2.

Lemma op_segA : forall (usp sp' f OS BUF N lo : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s9 s10 t3 t4 t5 t6 : word)
    (j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 h0 h1 h2 e0 e1 e2 j148 j284 : list byte) (ls : list (list byte)) F fc (m : mem),
  length ls = 16%nat ->
  0 < f -> f + 128 <= lo -> 0xd9400 <= f / 8 -> f / 8 + 2147450880 + 16 <= lo -> (f + 128 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= f) ->
  0 < OS -> OS + 288 <= lo -> OS mod 16 = 0 ->
  (OS + 288 <= f \/ f + 128 <= OS) -> (OS + 288 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= OS) ->
  0x7fff7f800000 <= lo -> lo <= sp' -> sp' + 88 <= usp -> usp < 2^63 -> 0 < BUF -> 0 <= N -> BUF + N < 2^63 ->
  rw_cells asegs m sp' (op_locals0 j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10) ->
  rw_cells asegs m f [CB 8 h0; CB 8 h1; CB 8 h2] -> rw_cells asegs m (f + 64) [CB 1 e0; CB 7 e1; CB 8 e2] ->
  rw_cells asegs m (f / 8 + 2147450880) (map (fun l => CB 1 l) ls) ->
  rw_cells asegs m (OS + 128) (ios_midA OS 255 255 255 255 j148 j284) ->
  ro_cells asegs m PJ_NULSB_VT_A [C8 (wz PJ_XSPUTN_A); C8 (wz PJ_OVERFLOW_A); C8 (wz 8)] ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (wz 0xb821c) (wz sp') gp tp t0 t1 t2 (wz usp) (wz sp') (wz ((OS + 128) / 8 + 2147450880)) (wz 1) (wz 0) (wz (-14)) a4 a5 a6 a7
                   (wz f) (wz (OS + 128)) (wz (f + 64)) (wz (f / 8 + 2147450880)) s6 (wz BUF) (wz N) (wz f) s10 (wz 2147450880) t3 t4 t5 t6)
              F (wz 0xb8230) fc None m1 (seg_rom asegs)
      /\ munch [(sp', sp' + 88); (f, f + 24); (f + 64, f + 80); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 sp' [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; C8 (wz ((OS + 128) / 8 + 2147450880)); CB 8 j8; CB 8 j9; C8 (wz f)]
      /\ rw_cells asegs m1 f [C8 (wz 0x41b58ab3); C8 (wz 0x22601); C8 (wz 0xb80f4)]
      /\ rw_cells asegs m1 (f + 64) [C1 (Z_to_bv 8 1); CB 7 e1; C8 (wz (OS + 128))]
      /\ rw_cells asegs m1 (f / 8 + 2147450880) (map C1 (op_sh12 (-8)) ++ map (fun l => CB 1 l) (skipn 12 ls)))
    (MS (mkR (wz 0xb816c) (wz sp') gp tp t0 t1 t2 (wz usp) (wz sp') (wz f) a1 a2 a3 a4 a5 a6 a7
             s2 (wz (OS + 128)) s4 s5 s6 (wz BUF) (wz N) s9 s10 (wz 2147450880) t3 t4 t5 t6)
        F (wz 0xb816c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros LS F0 FLO FD8 SLO SEP O0 OLO O16 OF OSH2 LOW LSP SPU UH B0 N0 BNH FRl FH SEN FS IOS VT MI.
  do 16 (destruct ls as [|? ls]; [discriminate LS|]). destruct ls; [| discriminate LS]. clear LS.
  unfold op_sh12, op_locals0, ios_midA, PJ_NULSB_VT_A, PJ_XSPUTN_A, PJ_OVERFLOW_A, PJ_OS_VPTR_A, PJ_IOS_VPTR_A, PJ_LOC_IMP_A in *. cbn [map app repeat skipn] in *.
  pose proof (munch_refl [(sp', sp' + 88); (f, f + 24); (f + 64, f + 80); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (E64 : bv_unsigned (Z_to_bv 64 (f + 64)) = f + 64) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (Z_to_bv 64 (OS + 128)) = OS + 128) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  do 3 zstep.
  zstep. if_cases K0; zify_cond K0; [| exfalso; lia].
  lstep.
  zstep.
  do 3 zstep. zstep. rewrite shr3_div. do 4 zstep.
  do 3 lstep.
  zstep. zstep.
  do 4 ls.
  zstep. do 4 ls.
  zstep. do 4 ls.
  do 3 zstep.
  zstep.
  ls.
  lstep.
  zstep. zstep.
  zstep. zstep. if_true.
  zstep. zstep. if_true.
  zstep. ls.
  zstep.
  zstep. zstep. if_false.
  zstep. rewrite shr3_div. zstep.
  lstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma op_segB : forall (usp sp' f OS BUF N lo : Z) (gp tp t0 t1 t2 a4 a5 a6 a7 s6 s10 t3 t4 t5 t6 : word)
    (j0 j1 j2 j3 j4 j5 j6 j8 j9 tb j148 j284 : list byte) (ls4 : list (list byte)) F fc (m : mem),
  length ls4 = 4%nat ->
  0 < f -> f + 128 <= lo -> 0xd9400 <= f / 8 -> f / 8 + 2147450880 + 16 <= lo -> (f + 128 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= f) ->
  0 < OS -> OS + 288 <= lo -> OS mod 16 = 0 ->
  (OS + 288 <= f \/ f + 128 <= OS) -> (OS + 288 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= OS) ->
  0x7fff7f800000 <= lo -> lo <= sp' - 16 -> sp' + 88 <= usp -> usp < 2^63 -> 0 < BUF -> 0 <= N -> BUF + N < 2^63 ->
  shz m OS 288 -> shz m PJ_NULSB_VT_A 24 -> stk asegs m lo sp' ->
  rw_cells asegs m sp' [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; C8 (wz ((OS + 128) / 8 + 2147450880)); CB 8 j8; CB 8 j9; C8 (wz f)] ->
  rw_cells asegs m (f + 32) [CB 8 tb] ->
  rw_cells asegs m (f / 8 + 2147450880) (map C1 (op_sh12 (-8)) ++ map (fun l => CB 1 l) ls4) ->
  rw_cells asegs m (OS + 128) (ios_midA OS 255 255 255 255 j148 j284) ->
  ro_cells asegs m PJ_NULSB_VT_A [C8 (wz PJ_XSPUTN_A); C8 (wz PJ_OVERFLOW_A); C8 (wz 8)] ->
  ro_cells asegs m PJ_GOT_CTYPE_ID_A [C8 (wz PJ_CTYPE_ID_A)] ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (a5' a6' : word) (m1 : mem),
      ms = MS (mkR (wz 0xb8334) (wz sp') gp tp t0 t1 t2 (wz usp) (wz sp') (wz (f + 32)) (wz PJ_CTYPE_ID_A) (wz PJ_LOC_IMP_A) (wz (BUF + N)) (wz OS) a5' a6' a7
                   (wz f) (wz (OS + 128)) (wz (f + 64)) (wz (f / 8 + 2147450880)) (wz (OS + 136)) (wz (f + 32)) (wz ((OS + 280) / 8 + 2147450880)) (wz f)
                   (wz (OS + 280)) (wz 2147450880) t3 t4 t5 t6)
              F (wz PJ_USE_FACET_A) fc None m1 (seg_rom asegs)
      /\ munch [(sp' - 16, sp'); (sp' + 16, sp' + 56); (f + 32, f + 40); (f / 8 + 2147450880 + 4, f / 8 + 2147450880 + 5)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ stk asegs m1 lo sp'
      /\ rw_cells asegs m1 sp' [CB 8 j0; CB 8 j1; C8 (wz (OS + 283)); C8 (wz BUF); C8 (wz (BUF + N)); C8 (wz OS); C8 (wz BUF); C8 (wz ((OS + 128) / 8 + 2147450880)); CB 8 j8; CB 8 j9; C8 (wz f)]
      /\ rw_cells asegs m1 (f + 32) [C8 (wz PJ_LOC_IMP_A)]
      /\ rw_cells asegs m1 (f / 8 + 2147450880) (map C1 (op_sh12 0) ++ map (fun l => CB 1 l) ls4)
      /\ rw_cells asegs m1 (OS + 128) (ios_midA OS 255 255 255 255 j148 j284))
    (MS (mkR (wz 0xb821c) (wz sp') gp tp t0 t1 t2 (wz usp) (wz sp') (wz ((OS + 128) / 8 + 2147450880)) (wz 1) (wz 0) (wz (-14)) a4 a5 a6 a7
             (wz f) (wz (OS + 128)) (wz (f + 64)) (wz (f / 8 + 2147450880)) s6 (wz BUF) (wz N) (wz f) s10 (wz 2147450880) t3 t4 t5 t6)
        F (wz 0xb8230) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros LS4 F0 FLO FD8 SLO SEP O0 OLO O16 OF OSH2 LOW LSP SPU UH B0 N0 BNH SHZ0 SHV ST FRl TMP FS IOS VT GOT MI.
  do 4 (destruct ls4 as [|? ls4]; [discriminate LS4|]). destruct ls4; [| discriminate LS4]. clear LS4.
  unfold op_sh12, ios_midA, PJ_NULSB_VT_A, PJ_XSPUTN_A, PJ_OVERFLOW_A, PJ_OS_VPTR_A, PJ_IOS_VPTR_A, PJ_LOC_IMP_A, PJ_GOT_CTYPE_ID_A, PJ_CTYPE_ID_A, PJ_USE_FACET_A in *.
  cbn [map app repeat] in *.
  pose proof (munch_refl [(sp' - 16, sp'); (sp' + 16, sp' + 56); (f + 32, f + 40); (f / 8 + 2147450880 + 4, f / 8 + 2147450880 + 5)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (E32 : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (Z_to_bv 64 (OS + 128)) = OS + 128) by (apply unsigned_lit; lia).
  assert (EO136 : bv_unsigned (Z_to_bv 64 (OS + 136)) = OS + 136) by (apply unsigned_lit; lia).
  assert (EO144 : bv_unsigned (Z_to_bv 64 (OS + 144)) = OS + 144) by (apply unsigned_lit; lia).
  assert (EO280 : bv_unsigned (Z_to_bv 64 (OS + 280)) = OS + 280) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).

  shz_pose SHZ0 (OS + 128). zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. zstep.
  pose proof (SHV 0x164638 ltac:(lia)) as RD1. change (0x164638 / 8 + 2147450880) with 2147633351 in RD1.
  zstep. shz_norm. zstep. if_false.
  zstep. zstep.    replace (OS + 128 + 8) with (OS + 136) by lia.
  zstep. zstep. rewrite shr3_div. zstep.
  shz_pose SHZ0 (OS + 176). replace (OS + 136 + 40) with (OS + 176) by lia. zstep. shz_norm. zstep. if_false.
  zstep. zstep. rewrite shr3_div. zstep.
  shz_pose SHZ0 (OS + 144). replace (OS + 136 + 8) with (OS + 144) by lia. zstep. shz_norm.
  zstep.
  zstep. if_false.
  zstep. zstep. zstep.
  zstep. zstep.
  zstep. if_false.
  zstep.
  zstep.    replace (OS + 136 + 144) with (OS + 280) by lia.
  zstep. rewrite shr3_div. zstep.
  shz_pose SHZ0 (OS + 280). zstep. shz_norm. zstep. if_false.
  zstep.    replace (OS + 136 + 147) with (OS + 283) by lia.
  zstep. rewrite shr3_div. zstep.
  shz_pose SHZ0 (OS + 283). zstep. shz_norm. zstep. if_false.
  do 4 zstep.
  do 6 zstep.
  zstep. zstep.    replace (OS + 280 + 3) with (OS + 283) by lia.
  zstep. if_false.
  do 5 lstep.
  zstep.
  ls.
  do 3 zstep.
  carve_frame 16%nat ST.
  lstep. lstep.
  zstep.    replace (OS + 136 + 48) with (OS + 184) by lia.
  zstep.
  zstep.
  zstep. zstep.
  lstep.
  zstep. if_true.
  zstep.
  zstep. zstep.
  release_frame FR ST sp'.
  zstep.
  zstep. zstep.
  zstep. zstep.
  apply evt_done. eexists _, _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma op_segC : forall (usp sp' f OS BUF N lo : Z) (gp tp t0 t1 t2 a1 a2 a5 a6 a7 t3 t4 t5 t6 : word)
    (j0 j1 j8 j9 j148 j284 : list byte) (ls4 : list (list byte)) F fc (m : mem),
  length ls4 = 4%nat ->
  0 < f -> f + 128 <= lo -> 0xd9400 <= f / 8 -> f / 8 + 2147450880 + 16 <= lo -> (f + 128 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= f) ->
  0 < OS -> OS + 288 <= lo -> OS mod 16 = 0 -> OS / 8 + 2147450880 + 37 <= lo ->
  (OS + 288 <= f \/ f + 128 <= OS) -> (OS + 288 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= OS) ->
  (OS + 288 <= OS / 8 + 2147450880 \/ OS / 8 + 2147450880 + 37 <= OS) ->
  0x7fff7f800000 <= lo -> lo <= sp' -> sp' + 88 <= usp -> usp < 2^63 -> 0 < BUF -> 0 <= N -> BUF + N < 2^63 ->
  shz m PJ_CTYPE_FACET_A 8 -> shz m PJ_WIDEN_SLOT_A 8 -> bytes_at asegs m (OS / 8 + 2147450880) (repeat z8 36) ->
  rw_cells asegs m PJ_CTYPE_FACET_A [C8 (wz PJ_CTYPE_VPTR_A)] -> ro_cells asegs m PJ_WIDEN_SLOT_A [C8 (wz PJ_DO_WIDEN_A)] ->
  rw_cells asegs m sp' [CB 8 j0; CB 8 j1; C8 (wz (OS + 283)); C8 (wz BUF); C8 (wz (BUF + N)); C8 (wz OS); C8 (wz BUF); C8 (wz ((OS + 128) / 8 + 2147450880)); CB 8 j8; CB 8 j9; C8 (wz f)] ->
  rw_cells asegs m (f + 32) [C8 (wz PJ_LOC_IMP_A)] ->
  rw_cells asegs m (f / 8 + 2147450880) (map C1 (op_sh12 0) ++ map (fun l => CB 1 l) ls4) ->
  rw_cells asegs m (OS + 128) (ios_midA OS 255 255 255 255 j148 j284) ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (wz 0xb83e8) (wz sp') gp tp t0 t1 t2 (wz usp) (wz sp') (wz OS) (wz BUF) (wz BUF) (wz (BUF + N)) (wz (OS + 136)) (wz 32) a6 a7
                   (wz f) (wz (OS + 128)) (wz (f + 64)) (wz (f / 8 + 2147450880)) (wz (OS + 136)) (wz BUF) (wz ((OS + 280) / 8 + 2147450880)) (wz f)
                   (wz (OS + 280)) (wz 2147450880) t3 t4 t5 t6)
              F (wz PJ_PADOUT_A) fc None m1 (seg_rom asegs)
      /\ munch [(sp' + 8, sp' + 16); (f / 8 + 2147450880 + 4, f / 8 + 2147450880 + 5); (OS + 280, OS + 284)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 sp' [CB 8 j0; C8 (wz 32); C8 (wz (OS + 283)); C8 (wz BUF); C8 (wz (BUF + N)); C8 (wz OS); C8 (wz BUF); C8 (wz ((OS + 128) / 8 + 2147450880)); CB 8 j8; CB 8 j9; C8 (wz f)]
      /\ rw_cells asegs m1 (f / 8 + 2147450880) (map C1 (op_sh12 (-8)) ++ map (fun l => CB 1 l) ls4)
      /\ rw_cells asegs m1 (OS + 128) (ios_midA OS 32 0 0 0 j148 j284))
    (MS (mkR (wz 0xb8334) (wz sp') gp tp t0 t1 t2 (wz usp) (wz sp') (wz PJ_CTYPE_FACET_A) a1 a2 (wz (BUF + N)) (wz OS) a5 a6 a7
             (wz f) (wz (OS + 128)) (wz (f + 64)) (wz (f / 8 + 2147450880)) (wz (OS + 136)) (wz (f + 32)) (wz ((OS + 280) / 8 + 2147450880)) (wz f)
             (wz (OS + 280)) (wz 2147450880) t3 t4 t5 t6)
        F (wz 0xb8334) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros LS4 F0 FLO FD8 SLO SEP O0 OLO O16 OSLO OF OSH2 OSELF LOW LSP SPU UH B0 N0 BNH SHF SHW SHZ0 FACV WRO FRl TMP FS IOS MI.
  do 4 (destruct ls4 as [|? ls4]; [discriminate LS4|]). destruct ls4; [| discriminate LS4]. clear LS4.
  unfold op_sh12, ios_midA, PJ_OS_VPTR_A, PJ_IOS_VPTR_A, PJ_LOC_IMP_A, PJ_CTYPE_FACET_A, PJ_CTYPE_VPTR_A, PJ_WIDEN_SLOT_A, PJ_DO_WIDEN_A, PJ_PADOUT_A in *.
  cbn [map app repeat] in *.
  pose proof (munch_refl [(sp' + 8, sp' + 16); (f / 8 + 2147450880 + 4, f / 8 + 2147450880 + 5); (OS + 280, OS + 284)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (E32 : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (Z_to_bv 64 (OS + 128)) = OS + 128) by (apply unsigned_lit; lia).
  assert (EO136 : bv_unsigned (Z_to_bv 64 (OS + 136)) = OS + 136) by (apply unsigned_lit; lia).
  assert (EO280 : bv_unsigned (Z_to_bv 64 (OS + 280)) = OS + 280) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  assert (ESH280 : bv_unsigned (Z_to_bv 64 ((OS + 280) / 8 + 2147450880)) = (OS + 280) / 8 + 2147450880) by (apply unsigned_lit; Z.div_mod_to_equations; lia).
  assert (SHZ : forall m', munch [(sp' + 8, sp' + 16); (f / 8 + 2147450880 + 4, f / 8 + 2147450880 + 5); (OS + 280, OS + 284)] m m' -> wmono asegs m m' -> shz m' OS 288).
  { intros m' MU' _. change 288 with (8 * Z.of_nat 36). apply (shz_of_zero_run m' OS 36); [clear - O16; Z.div_mod_to_equations; lia| lia|].
    eapply bytes_at_agree; [exact SHZ0|]. apply (agree_of_munch _ _ _ _ MU'). intros x Hx. rewrite repeat_length in Hx. cbn [outside]. unfold shad, SHB in *.
    clear - Hx OSLO LSP OF OSELF FD8 F0 O0. split; [| split; [| split; [| exact I]]]; Z.div_mod_to_equations; lia. }
  change (id (bytes_at asegs m (OS / 8 + 2147450880) (repeat z8 36))) in SHZ0.
  zstep. zstep.
  pose proof (SHF 0x6a6bc8 ltac:(lia)) as RD1. change (0x6a6bc8 / 8 + 2147450880) with 2148322681 in RD1.
  zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. zstep.
  pose proof (SHW 0x168050 ltac:(lia)) as RD2. change (0x168050 / 8 + 2147450880) with 2147635210 in RD2.
  zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep.
  zstep. zstep.
  lstep.
  zstep. zstep.
  zstep. zstep. zstep. zstep. if_true. zstep.
  zstep. ls.
  shz_pose SHZ (OS + 280). zstep. shz_norm. zstep. if_false.
  zstep.
  zstep. rewrite shr3_div. zstep.
  shz_pose SHZ (OS + 283). zstep. shz_norm.
  do 4 zstep.
  zstep. if_false.
  zstep.
  do 4 ls.
  shz_pose SHZ (OS + 280). zstep. shz_norm. zstep. if_false.
  zstep. rewrite shr3_div. zstep.
  shz_pose SHZ (OS + 283). zstep. shz_norm. zstep. if_false.
  zstep.    replace (OS + 136 + 144) with (OS + 280) by lia.
  do 4 zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.
