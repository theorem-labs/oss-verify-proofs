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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Pj_lftoi1A Pj_defsA Pj_os_defsA Pj_os_put1A Pj_os_put3A Pj_os_put4A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma op_segAX : forall (b0 b1 b2 b3 : Z) (usp sp' f OS BUF N lo : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s9 s10 t3 t4 t5 t6 : word)
    (j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 h0 h1 h2 e0 e1 e2 j148 j284 : list byte) (ls : list (list byte)) F fc (m : mem),
  length ls = 16%nat ->
  0 < f -> f + 128 <= lo -> 0xd9400 <= f / 8 -> f / 8 + 2147450880 + 16 <= lo -> (f + 128 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= f) ->
  0 < OS -> OS + 288 <= lo -> OS mod 16 = 0 ->
  (OS + 288 <= f \/ f + 128 <= OS) -> (OS + 288 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= OS) ->
  0x7fff7f800000 <= lo -> lo <= sp' -> sp' + 88 <= usp -> usp < 2^63 -> 0 < BUF -> 0 <= N -> BUF + N < 2^63 ->
  rw_cells asegs m sp' (op_locals0 j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10) ->
  rw_cells asegs m f [CB 8 h0; CB 8 h1; CB 8 h2] -> rw_cells asegs m (f + 64) [CB 1 e0; CB 7 e1; CB 8 e2] ->
  rw_cells asegs m (f / 8 + 2147450880) (map (fun l => CB 1 l) ls) ->
  rw_cells asegs m (OS + 128) (ios_midA OS b0 b1 b2 b3 j148 j284) ->
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

Lemma op_segB2 : forall (FL usp sp' f OS BUF N lo : Z) (gp tp t0 t1 t2 a4 a5 a6 a7 s6 s10 t3 t4 t5 t6 : word)
    (j0 j1 j2 j3 j4 j5 j6 j8 j9 tb j148 j284 : list byte) (ls4 : list (list byte)) F fc (m : mem),
  length ls4 = 4%nat ->
  0 < f -> f + 128 <= lo -> 0xd9400 <= f / 8 -> f / 8 + 2147450880 + 16 <= lo -> (f + 128 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= f) ->
  0 < OS -> OS + 288 <= lo -> OS mod 16 = 0 ->
  (OS + 288 <= f \/ f + 128 <= OS) -> (OS + 288 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= OS) ->
  0x7fff7f800000 <= lo -> lo <= sp' - 16 -> sp' + 88 <= usp -> usp < 2^63 -> 0 < BUF -> 0 <= N -> BUF + N < 2^63 ->
  (FL = 0x20 \/ FL = 0x30) ->
  shz m OS 288 -> shz m PJ_NULSB_VT_A 24 -> stk asegs m lo sp' ->
  rw_cells asegs m sp' [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; C8 (wz ((OS + 128) / 8 + 2147450880)); CB 8 j8; CB 8 j9; C8 (wz f)] ->
  rw_cells asegs m (f + 32) [CB 8 tb] ->
  rw_cells asegs m (f / 8 + 2147450880) (map C1 (op_sh12 (-8)) ++ map (fun l => CB 1 l) ls4) ->
  rw_cells asegs m (OS + 128) (ios_midA OS FL 0 0 0 j148 j284) ->
  ro_cells asegs m PJ_NULSB_VT_A [C8 (wz PJ_XSPUTN_A); C8 (wz PJ_OVERFLOW_A); C8 (wz 8)] ->
  ro_cells asegs m PJ_GOT_CTYPE_ID_A [C8 (wz PJ_CTYPE_ID_A)] ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (a6' : word) (m1 : mem),
      ms = MS (mkR (wz 0xb83e8) (wz sp') gp tp t0 t1 t2 (wz usp) (wz sp') (wz OS) (wz BUF) (wz BUF) (wz (BUF + N)) (wz (OS + 136)) (wz FL) a6' a7
                   (wz f) (wz (OS + 128)) (wz (f + 64)) (wz (f / 8 + 2147450880)) (wz (OS + 136)) (wz BUF) (wz ((OS + 280) / 8 + 2147450880)) (wz f)
                   (wz (OS + 280)) (wz 2147450880) t3 t4 t5 t6)
              F (wz PJ_PADOUT_A) fc None m1 (seg_rom asegs)
      /\ munch [(sp' - 16, sp')] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ stk asegs m1 lo sp'
      /\ rw_cells asegs m1 sp' [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; C8 (wz ((OS + 128) / 8 + 2147450880)); CB 8 j8; CB 8 j9; C8 (wz f)]
      /\ rw_cells asegs m1 (f + 32) [CB 8 tb]
      /\ rw_cells asegs m1 (f / 8 + 2147450880) (map C1 (op_sh12 (-8)) ++ map (fun l => CB 1 l) ls4)
      /\ rw_cells asegs m1 (OS + 128) (ios_midA OS FL 0 0 0 j148 j284))
    (MS (mkR (wz 0xb821c) (wz sp') gp tp t0 t1 t2 (wz usp) (wz sp') (wz ((OS + 128) / 8 + 2147450880)) (wz 1) (wz 0) (wz (-14)) a4 a5 a6 a7
             (wz f) (wz (OS + 128)) (wz (f + 64)) (wz (f / 8 + 2147450880)) s6 (wz BUF) (wz N) (wz f) s10 (wz 2147450880) t3 t4 t5 t6)
        F (wz 0xb8230) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros LS4 F0 FLO FD8 SLO SEP O0 OLO O16 OF OSH2 LOW LSP SPU UH B0 N0 BNH HFL SHZ0 SHV ST FRl TMP FS IOS VT GOT MI.
  destruct HFL as [-> | ->].
  all: do 4 (destruct ls4 as [|? ls4]; [discriminate LS4|]). all: destruct ls4; [| discriminate LS4]. all: clear LS4.
  all: unfold op_sh12, ios_midA, PJ_NULSB_VT_A, PJ_XSPUTN_A, PJ_OVERFLOW_A, PJ_OS_VPTR_A, PJ_IOS_VPTR_A, PJ_LOC_IMP_A, PJ_GOT_CTYPE_ID_A, PJ_CTYPE_ID_A, PJ_USE_FACET_A, PJ_PADOUT_A in *.
  all: cbn [map app repeat] in *.
  all: pose proof (munch_refl [(sp' - 16, sp')] m) as MU. all: pose proof (wmono_refl asegs m) as WM.
  all: assert (ES : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  all: assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  all: assert (E32 : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  all: assert (EO : bv_unsigned (Z_to_bv 64 (OS + 128)) = OS + 128) by (apply unsigned_lit; lia).
  all: assert (EO136 : bv_unsigned (Z_to_bv 64 (OS + 136)) = OS + 136) by (apply unsigned_lit; lia).
  all: assert (EO144 : bv_unsigned (Z_to_bv 64 (OS + 144)) = OS + 144) by (apply unsigned_lit; lia).
  all: assert (EO280 : bv_unsigned (Z_to_bv 64 (OS + 280)) = OS + 280) by (apply unsigned_lit; lia).
  all: assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).

  all: shz_pose SHZ0 (OS + 128). all: zstep. all: shz_norm. all: zstep. all: if_false.
  all: zstep. all: zstep. all: zstep. all: zstep.
  all: pose proof (SHV 0x164638 ltac:(lia)) as RD1. all: change (0x164638 / 8 + 2147450880) with 2147633351 in RD1.
  all: zstep. all: shz_norm. all: zstep. all: if_false.
  all: zstep. all: zstep. all: replace (OS + 128 + 8) with (OS + 136) by lia.
  all: zstep. all: zstep. all: rewrite shr3_div. all: zstep.
  all: shz_pose SHZ0 (OS + 176). all: replace (OS + 136 + 40) with (OS + 176) by lia. all: zstep. all: shz_norm. all: zstep. all: if_false.
  all: zstep. all: zstep. all: rewrite shr3_div. all: zstep.
  all: shz_pose SHZ0 (OS + 144). all: replace (OS + 136 + 8) with (OS + 144) by lia. all: zstep. all: shz_norm.
  all: zstep.
  all: zstep. all: if_false.
  all: zstep. all: zstep. all: zstep.
  all: zstep. all: zstep.
  all: zstep. all: if_false.
  all: zstep.
  all: zstep. all: replace (OS + 136 + 144) with (OS + 280) by lia.
  all: zstep. all: rewrite shr3_div. all: zstep.
  all: shz_pose SHZ0 (OS + 280). all: zstep. all: shz_norm. all: zstep. all: if_false.
  all: zstep. all: replace (OS + 136 + 147) with (OS + 283) by lia.
  all: zstep. all: rewrite shr3_div. all: zstep.
  all: shz_pose SHZ0 (OS + 283). all: zstep. all: shz_norm. all: zstep. all: if_false.
  all: do 4 zstep.
  all: do 6 zstep.
  all: zstep. all: zstep. all: replace (OS + 280 + 3) with (OS + 283) by lia.

  all: zstep. all: if_true.
  all: shz_pose SHZ0 (OS + 280). all: zstep. all: shz_norm. all: zstep. all: if_false.
  all: zstep. all: rewrite shr3_div. all: zstep.
  all: shz_pose SHZ0 (OS + 283). all: zstep. all: shz_norm. all: zstep. all: if_false.
  all: zstep. all: replace (OS + 136 + 144) with (OS + 280) by lia.
  all: zstep. all: zstep. all: zstep.
  all: zstep.
  all: apply evt_done. all: eexists _, _. all: split; [cbv delta [mkR]; reflexivity|].
  all: split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. all: split; [exact WM|]. all: split; [eassumption|].
  all: split; [eassumption|]. all: split; [eassumption|]. all: split; [eassumption|]. all: split; [eassumption|]. all: eassumption.
Qed.

