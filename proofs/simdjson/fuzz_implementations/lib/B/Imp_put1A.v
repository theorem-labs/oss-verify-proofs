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
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Atp_fzwA Pj_lftoi1A Pj_defsA Pj_os_defsA Pj_os_put1A Pj_os_put2A Imp_oss_defsA Imp_pad1A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition ios_midI (O : Z) (b0 b1 b2 b3 : Z) (j148 j284 : list byte) : list cell :=
  [C8 (wz OSS_IOS_VPTR_A); CB 4 [Z_to_bv 8 2; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0]; CB 4 j148; C8 (wz 6); C8 (wz 0); C4 (wz 0); C4 (wz 0);
   C8 (wz (O + 8)); C8 (wz PJ_LOC_IMP_A);
   C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0);
   C8 (wz 0); C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C1 (Z_to_bv 8 b2); C1 (Z_to_bv 8 b3); CB 4 j284].

Definition op_sh12 (b4 : Z) : list byte :=
  repeat (Z_to_bv 8 (-15)) 4 ++ [Z_to_bv 8 b4] ++ repeat (Z_to_bv 8 (-14)) 3 ++ [Z_to_bv 8 0; Z_to_bv 8 0] ++ repeat (Z_to_bv 8 (-13)) 2.

Lemma op_segAI : forall (usp sp' f O BUF N lo : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s7 s8 s10 t3 t4 t5 t6 : word)
    (j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 h0 h1 h2 e0 e1 e2 j148 j284 : list byte) (ls : list (list byte)) F fc (m : mem),
  length ls = 16%nat ->
  0 < f -> f + 128 <= lo -> 0xdc000 <= f / 8 -> f / 8 + 2147450880 + 16 <= lo -> (f + 128 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= f) ->
  0 < O -> O + 264 <= lo -> O mod 16 = 0 ->
  (O + 264 <= f \/ f + 128 <= O) -> (O + 264 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= O) ->
  0x7fff7f800000 <= lo -> lo <= sp' -> sp' + 88 <= usp -> usp < 2^63 -> 0 < BUF -> 0 <= N -> BUF + N < 2^63 ->
  rw_cells bsegs m sp' (op_locals0 j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10) ->
  rw_cells bsegs m f [CB 8 h0; CB 8 h1; CB 8 h2] -> rw_cells bsegs m (f + 64) [CB 1 e0; CB 7 e1; CB 8 e2] ->
  rw_cells bsegs m (f / 8 + 2147450880) (map (fun l => CB 1 l) ls) ->
  rw_cells bsegs m O [C8 (wz OSS_OS_VPTR_A)] -> rw_cells bsegs m (O + 112) (ios_midI O 255 255 255 255 j148 j284) ->
  ro_cells bsegs m OSS_VBOFF_A [C8 (wz 0x70)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (wz 0xbdfdc) (wz sp') gp tp t0 t1 t2 (wz usp) (wz sp') (wz (O / 8 + 2147450880)) (wz 2) (wz 0) (wz (-14)) a4 a5 a6 a7
                   (wz f) (wz O) (wz (f + 64)) (wz BUF) s6 s7 (wz (f / 8 + 2147450880)) (wz N) s10 (wz 2147450880) t3 t4 t5 t6)
              F (wz 0xbdffc) fc None m1 (seg_rom bsegs)
      /\ munch [(sp', sp' + 88); (f, f + 24); (f + 64, f + 80); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 sp' [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; C8 (wz (O / 8 + 2147450880)); C8 (wz f); CB 8 j8; CB 8 j9; C8 (wz f)]
      /\ rw_cells bsegs m1 f [C8 (wz 0x41b58ab3); C8 (wz 0x227ed); C8 (wz 0xbdeb4)]
      /\ rw_cells bsegs m1 (f + 64) [C1 (Z_to_bv 8 1); CB 7 e1; C8 (wz O)]
      /\ rw_cells bsegs m1 (f / 8 + 2147450880) (map C1 (op_sh12 (-8)) ++ map (fun l => CB 1 l) (skipn 12 ls)))
    (MS (mkR (wz 0xbdf2c) (wz sp') gp tp t0 t1 t2 (wz usp) (wz sp') (wz f) a1 a2 a3 a4 a5 a6 a7
             s2 (wz O) s4 (wz BUF) s6 s7 s8 (wz N) s10 (wz 2147450880) t3 t4 t5 t6)
        F (wz 0xbdf2c) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LS F0 FLO FD8 SLO SEP O0 OLO O16 OF OSH2 LOW LSP SPU UH B0 N0 BNH FRl FH SEN FS VP IOS VT MI.
  do 16 (destruct ls as [|? ls]; [discriminate LS|]). destruct ls; [| discriminate LS]. clear LS.
  unfold op_sh12, op_locals0, ios_midI, OSS_VBOFF_A, OSS_OS_VPTR_A, OSS_IOS_VPTR_A, PJ_LOC_IMP_A in *. cbn [map app repeat skipn] in *.
  pose proof (munch_refl [(sp', sp' + 88); (f, f + 24); (f + 64, f + 80); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (E64 : bv_unsigned (Z_to_bv 64 (f + 64)) = f + 64) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (Z_to_bv 64 O) = O) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  zstep. zstep.
  zstep. if_cases K0; zify_cond K0; [| exfalso; lia].
  lstep. lstep.
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
  zstep. zstep.
  zstep. if_false.
  zstep.
  zstep. if_false.
  zstep. rewrite shr3_div. zstep.
  lstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma op_segBI : forall (usp sp' f O BUF N lo : Z) (gp tp t0 t1 t2 a4 a5 a6 a7 s6 s7 s10 t3 t4 t5 t6 : word)
    (j0 j1 j2 j3 j4 j5 j8 j9 tb j148 j284 : list byte) (ls4 : list (list byte)) F fc (m : mem),
  length ls4 = 4%nat ->
  0 < f -> f + 128 <= lo -> 0xdc000 <= f / 8 -> f / 8 + 2147450880 + 16 <= lo -> (f + 128 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= f) ->
  0 < O -> O + 264 <= lo -> O mod 16 = 0 ->
  (O + 264 <= f \/ f + 128 <= O) -> (O + 264 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= O) ->
  0x7fff7f800000 <= lo -> lo <= sp' - 16 -> sp' + 88 <= usp -> usp < 2^63 -> 0 < BUF -> 0 <= N -> BUF + N < 2^63 ->
  shz m O 264 -> shz m OSS_VBOFF_A 8 -> stk bsegs m lo sp' ->
  rw_cells bsegs m sp' [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; C8 (wz (O / 8 + 2147450880)); C8 (wz f); CB 8 j8; CB 8 j9; C8 (wz f)] ->
  rw_cells bsegs m (f + 32) [CB 8 tb] ->
  rw_cells bsegs m (f / 8 + 2147450880) (map C1 (op_sh12 (-8)) ++ map (fun l => CB 1 l) ls4) ->
  rw_cells bsegs m O [C8 (wz OSS_OS_VPTR_A)] -> rw_cells bsegs m (O + 112) (ios_midI O 255 255 255 255 j148 j284) ->
  ro_cells bsegs m OSS_VBOFF_A [C8 (wz 0x70)] ->
  ro_cells bsegs m PJ_GOT_CTYPE_ID_A [C8 (wz PJ_CTYPE_ID_A)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (a5' a6' : word) (m1 : mem),
      ms = MS (mkR (wz 0xbe134) (wz sp') gp tp t0 t1 t2 (wz usp) (wz sp') (wz (f + 32)) (wz PJ_CTYPE_ID_A) (wz PJ_LOC_IMP_A) (wz (BUF + N)) (wz (O + 8)) a5' a6' a7
                  (wz f) (wz O) (wz (f + 64)) (wz BUF) (wz (O + 112)) (wz (f + 32)) (wz (f / 8 + 2147450880)) (wz ((O + 256) / 8 + 2147450880))
                   (wz (O + 256)) (wz 2147450880) t3 t4 t5 t6)
              F (wz PJ_USE_FACET_A) fc None m1 (seg_rom bsegs)
      /\ munch [(sp' - 16, sp'); (sp' + 16, sp' + 48); (f + 32, f + 40); (f / 8 + 2147450880 + 4, f / 8 + 2147450880 + 5)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ stk bsegs m1 lo sp'
      /\ rw_cells bsegs m1 sp' [CB 8 j0; CB 8 j1; C8 (wz (O + 259)); C8 (wz BUF); C8 (wz (BUF + N)); C8 (wz (O + 8)); C8 (wz (O / 8 + 2147450880)); C8 (wz f); CB 8 j8; CB 8 j9; C8 (wz f)]
      /\ rw_cells bsegs m1 (f + 32) [C8 (wz PJ_LOC_IMP_A)]
      /\ rw_cells bsegs m1 (f / 8 + 2147450880) (map C1 (op_sh12 0) ++ map (fun l => CB 1 l) ls4)
      /\ rw_cells bsegs m1 (O + 112) (ios_midI O 255 255 255 255 j148 j284))
    (MS (mkR (wz 0xbdfdc) (wz sp') gp tp t0 t1 t2 (wz usp) (wz sp') (wz (O / 8 + 2147450880)) (wz 2) (wz 0) (wz (-14)) a4 a5 a6 a7
             (wz f) (wz O) (wz (f + 64)) (wz BUF) s6 s7 (wz (f / 8 + 2147450880)) (wz N) s10 (wz 2147450880) t3 t4 t5 t6)
        F (wz 0xbdffc) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LS4 F0 FLO FD8 SLO SEP O0 OLO O16 OF OSH2 LOW LSP SPU UH B0 N0 BNH SHZ0 SHV ST FRl TMP FS VP IOS VT GOT MI.
  do 4 (destruct ls4 as [|? ls4]; [discriminate LS4|]). destruct ls4; [| discriminate LS4]. clear LS4.
  unfold op_sh12, ios_midI, OSS_VBOFF_A, OSS_OS_VPTR_A, OSS_IOS_VPTR_A, PJ_LOC_IMP_A, PJ_GOT_CTYPE_ID_A, PJ_CTYPE_ID_A, PJ_USE_FACET_A in *.
  cbn [map app repeat] in *.
  pose proof (munch_refl [(sp' - 16, sp'); (sp' + 16, sp' + 48); (f + 32, f + 40); (f / 8 + 2147450880 + 4, f / 8 + 2147450880 + 5)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (E32 : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (Z_to_bv 64 O) = O) by (apply unsigned_lit; lia).
  assert (EO136 : bv_unsigned (Z_to_bv 64 (O + 112)) = O + 112) by (apply unsigned_lit; lia).
  assert (EO144 : bv_unsigned (Z_to_bv 64 (O + 120)) = O + 120) by (apply unsigned_lit; lia).
  assert (EO280 : bv_unsigned (Z_to_bv 64 (O + 256)) = O + 256) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).

  shz_pose SHZ0 O. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. zstep.
  pose proof (SHV 0x17d8b8 ltac:(lia)) as RD1. change (0x17d8b8 / 8 + 2147450880) with 2147646231 in RD1.
  zstep. shz_norm. zstep. if_false.
  zstep. zstep.
  zstep.
  replace (Z.land (O + 112) 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; clear - O16; Z.div_mod_to_equations; lia).
  zstep. if_false.
  zstep. zstep. rewrite shr3_div. zstep.
  shz_pose SHZ0 (O + 152). replace (O + 112 + 40) with (O + 152) by lia. zstep. shz_norm. zstep. if_false.
  zstep.    replace (O + 112 + 8) with (O + 120) by lia.
  zstep. rewrite shr3_div. zstep.
  shz_pose SHZ0 (O + 120). zstep. shz_norm.
  zstep.
  zstep. if_false.
  zstep. zstep. zstep.
  zstep.
  zstep.
  zstep. if_true.
  zstep. zstep.
  zstep. if_cases KU; zify_cond KU; [exfalso; lia|].
  zstep. zstep.
  replace (0 <? BUF) with true by (symmetry; apply Z.ltb_lt; lia). replace (BUF + N <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.lxor].
  zstep. if_false.
  zstep.    replace (O + 112 + 144) with (O + 256) by lia.
  zstep. rewrite shr3_div. zstep.
  shz_pose SHZ0 (O + 256). zstep. shz_norm. zstep. if_false.
  zstep.    replace (O + 112 + 147) with (O + 259) by lia.
  zstep. rewrite shr3_div. zstep.
  shz_pose SHZ0 (O + 259). zstep. shz_norm. zstep. if_false.
  do 4 zstep.
  do 6 zstep.
  zstep. zstep.    replace (O + 256 + 3) with (O + 259) by lia.
  zstep. if_false.
  do 4 lstep.
  zstep.
  ls.
  do 3 zstep.
  carve_frame 16%nat ST.
  lstep. lstep.
  zstep.    replace (O + 112 + 48) with (O + 160) by lia.
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

Lemma op_segCI : forall (usp sp' f O BUF N lo : Z) (gp tp t0 t1 t2 a1 a2 a5 a6 a7 t3 t4 t5 t6 : word)
    (j0 j1 j8 j9 j148 j284 : list byte) (ls4 : list (list byte)) F fc (m : mem),
  length ls4 = 4%nat ->
  0 < f -> f + 128 <= lo -> 0xdc000 <= f / 8 -> f / 8 + 2147450880 + 16 <= lo -> (f + 128 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= f) ->
  0 < O -> O + 264 <= lo -> O mod 16 = 0 -> O / 8 + 2147450880 + 34 <= lo ->
  (O + 264 <= f \/ f + 128 <= O) -> (O + 264 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= O) ->
  (O + 264 <= O / 8 + 2147450880 \/ O / 8 + 2147450880 + 34 <= O) ->
  0x7fff7f800000 <= lo -> lo <= sp' -> sp' + 88 <= usp -> usp < 2^63 -> 0 < BUF -> 0 <= N -> BUF + N < 2^63 ->
  shz m PJ_CTYPE_FACET_A 8 -> shz m PJ_WIDEN_SLOT_A 8 -> bytes_at bsegs m (O / 8 + 2147450880) (repeat z8 33) ->
  rw_cells bsegs m PJ_CTYPE_FACET_A [C8 (wz PJ_CTYPE_VPTR_A)] -> ro_cells bsegs m PJ_WIDEN_SLOT_A [C8 (wz PJ_DO_WIDEN_A)] ->
  rw_cells bsegs m sp' [CB 8 j0; CB 8 j1; C8 (wz (O + 259)); C8 (wz BUF); C8 (wz (BUF + N)); C8 (wz (O + 8)); C8 (wz (O / 8 + 2147450880)); C8 (wz f); CB 8 j8; CB 8 j9; C8 (wz f)] ->
  rw_cells bsegs m (f + 32) [C8 (wz PJ_LOC_IMP_A)] ->
  rw_cells bsegs m (f / 8 + 2147450880) (map C1 (op_sh12 0) ++ map (fun l => CB 1 l) ls4) ->
  rw_cells bsegs m O [C8 (wz OSS_OS_VPTR_A)] -> rw_cells bsegs m (O + 112) (ios_midI O 255 255 255 255 j148 j284) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (wz 0xbe1f0) (wz sp') gp tp t0 t1 t2 (wz usp) (wz sp') (wz (O + 8)) (wz BUF) (wz BUF) (wz (BUF + N)) (wz (O + 112)) (wz 32) a6 a7
                  (wz f) (wz O) (wz (f + 64)) (wz BUF) (wz (O + 112)) (wz (f + 32)) (wz (f / 8 + 2147450880)) (wz ((O + 256) / 8 + 2147450880))
                   (wz (O + 256)) (wz 2147450880) t3 t4 t5 t6)
              F (wz OSS_PADOUT_A) fc None m1 (seg_rom bsegs)
      /\ munch [(sp' + 8, sp' + 16); (f / 8 + 2147450880 + 4, f / 8 + 2147450880 + 5); (O + 256, O + 260)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 sp' [CB 8 j0; C8 (wz 32); C8 (wz (O + 259)); C8 (wz BUF); C8 (wz (BUF + N)); C8 (wz (O + 8)); C8 (wz (O / 8 + 2147450880)); C8 (wz f); CB 8 j8; CB 8 j9; C8 (wz f)]
      /\ rw_cells bsegs m1 (f / 8 + 2147450880) (map C1 (op_sh12 (-8)) ++ map (fun l => CB 1 l) ls4)
      /\ rw_cells bsegs m1 (O + 112) (ios_midI O 32 0 0 0 j148 j284))
    (MS (mkR (wz 0xbe134) (wz sp') gp tp t0 t1 t2 (wz usp) (wz sp') (wz PJ_CTYPE_FACET_A) a1 a2 (wz (BUF + N)) (wz (O + 8)) a5 a6 a7
            (wz f) (wz O) (wz (f + 64)) (wz BUF) (wz (O + 112)) (wz (f + 32)) (wz (f / 8 + 2147450880)) (wz ((O + 256) / 8 + 2147450880))
             (wz (O + 256)) (wz 2147450880) t3 t4 t5 t6)
        F (wz 0xbe134) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LS4 F0 FLO FD8 SLO SEP O0 OLO O16 OSLO OF OSH2 OSELF LOW LSP SPU UH B0 N0 BNH SHF SHW SHZ0 FACV WRO FRl TMP FS VP IOS MI.
  do 4 (destruct ls4 as [|? ls4]; [discriminate LS4|]). destruct ls4; [| discriminate LS4]. clear LS4.
  unfold op_sh12, ios_midI, OSS_OS_VPTR_A, OSS_IOS_VPTR_A, PJ_LOC_IMP_A, PJ_CTYPE_FACET_A, PJ_CTYPE_VPTR_A, PJ_WIDEN_SLOT_A, PJ_DO_WIDEN_A, OSS_PADOUT_A in *.
  cbn [map app repeat] in *.
  pose proof (munch_refl [(sp' + 8, sp' + 16); (f / 8 + 2147450880 + 4, f / 8 + 2147450880 + 5); (O + 256, O + 260)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (E32 : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (Z_to_bv 64 O) = O) by (apply unsigned_lit; lia).
  assert (EO136 : bv_unsigned (Z_to_bv 64 (O + 112)) = O + 112) by (apply unsigned_lit; lia).
  assert (EO280 : bv_unsigned (Z_to_bv 64 (O + 256)) = O + 256) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  assert (ESH280 : bv_unsigned (Z_to_bv 64 ((O + 256) / 8 + 2147450880)) = (O + 256) / 8 + 2147450880) by (apply unsigned_lit; Z.div_mod_to_equations; lia).
  assert (SHZ : forall m', munch [(sp' + 8, sp' + 16); (f / 8 + 2147450880 + 4, f / 8 + 2147450880 + 5); (O + 256, O + 260)] m m' -> wmono bsegs m m' -> shz m' O 264).
  { intros m' MU' _. change 288 with (8 * Z.of_nat 33). apply (shz_of_zero_run m' O 33); [clear - O16; Z.div_mod_to_equations; lia| lia|].
    eapply bytes_at_agree; [exact SHZ0|]. apply (agree_of_munch _ _ _ _ MU'). intros x Hx. rewrite repeat_length in Hx. cbn [outside]. unfold shad, SHB in *.
    clear - Hx OSLO LSP OF OSELF FD8 F0 O0. split; [| split; [| split; [| exact I]]]; Z.div_mod_to_equations; lia. }
  change (id (bytes_at bsegs m (O / 8 + 2147450880) (repeat z8 33))) in SHZ0.
  zstep. if_false.
  zstep. zstep. if_false.
  zstep. zstep.
  pose proof (SHF 0x6bd148 ltac:(lia)) as RD1. change (0x6bd148 / 8 + 2147450880) with 2148334121 in RD1.
  zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. zstep.
  pose proof (SHW 0x17dce0 ltac:(lia)) as RD2. change (0x17dce0 / 8 + 2147450880) with 2147646364 in RD2.
  zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep.
  zstep. zstep.
  lstep.
  zstep. zstep.
  zstep. zstep. zstep. zstep. if_true. zstep.
  zstep. ls.
  shz_pose SHZ (O + 256). zstep. shz_norm. zstep. if_false.
  zstep.
  zstep. rewrite shr3_div. zstep.
  shz_pose SHZ (O + 259). zstep. shz_norm.
  do 3 zstep.
  zstep. if_false.
  zstep.
  do 4 ls.
  shz_pose SHZ (O + 256). zstep. shz_norm. zstep. if_false.
  zstep. rewrite shr3_div. zstep.
  shz_pose SHZ (O + 259). zstep. shz_norm. zstep. if_false.
  zstep.    replace (O + 112 + 144) with (O + 256) by lia.
  do 4 zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma op_exit1I : forall (usp sp' f lo O ivp : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s9 s10 t3 t4 t5 t6 : word)
    (h0 : word) (j7 j148 : list byte) (sh : list byte) (ls4 : list (list byte)) F fc (m : mem),
  length sh = 12%nat -> length ls4 = 4%nat ->
  0 < f -> f + 128 <= lo -> 0 <= f / 8 -> f / 8 + 2147450880 + 16 <= lo -> (f + 128 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= f) ->
  0 < O -> O + 264 <= lo -> (O + 264 <= f \/ f + 128 <= O) -> (O + 264 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= O) ->
  0x6e0000 <= lo -> lo <= sp' - 16 -> sp' < 2^63 -> 0 <= ivp < 2^64 ->
  stk bsegs m lo sp' -> rw_cells bsegs m (sp' + 56) [C8 (wz f)] ->
  rw_cells bsegs m (f + 64) [C1 (Z_to_bv 8 1); CB 7 j7; C8 (wz O)] ->
  rw_cells bsegs m O [C8 (wz OSS_OS_VPTR_A)] ->
  rw_cells bsegs m (O + 112) [C8 (wz ivp); CB 4 [Z_to_bv 8 2; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0]; CB 4 j148;
                               C8 (wz 6); C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz (O + 8))] ->
  ro_cells bsegs m OSS_VBOFF_A [C8 (wz 0x70)] ->
  rw_cells bsegs m f [C8 h0] -> rw_cells bsegs m (f / 8 + 2147450880) (map C1 sh ++ map (fun l => CB 1 l) ls4) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (a2' : word) (m1 : mem),
      ms = MS (mkR (wz 0xbe250) (wz sp') gp tp t0 t1 t2 (wz usp) (wz sp') (wz (-11)) (wz f) a2' a3 a4 a5 a6 a7
                   (wz f) s3 (wz (f + 64)) s5 s6 s7 (wz (f / 8 + 2147450880)) s9 s10 (wz 2147450880) t3 t4 t5 t6)
              F (wz 0xbe2b4) fc None m1 (seg_rom bsegs)
      /\ munch [(sp' - 16, sp'); (f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ stk bsegs m1 lo sp' /\ rw_cells bsegs m1 f [C8 (wz 0x45e0360e)]
      /\ rw_cells bsegs m1 (f / 8 + 2147450880) (map C1 f5x16))
    (MS (mkR ra (wz sp') gp tp t0 t1 t2 (wz usp) (wz sp') a0 a1 a2 a3 a4 a5 a6 a7
             (wz f) s3 (wz (f + 64)) s5 s6 s7 (wz (f / 8 + 2147450880)) s9 s10 (wz 2147450880) t3 t4 t5 t6)
        F (wz 0xbe248) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LS LS4 F0 FLO FD SLO SEP O0 OLO OF OSH GLO LSP SPH IVR ST L7 SEN VP IOS VT FH FS MI.
  do 12 (destruct sh as [|? sh]; [discriminate LS|]). destruct sh; [| discriminate LS]. clear LS.
  do 4 (destruct ls4 as [|? ls4]; [discriminate LS4|]). destruct ls4; [| discriminate LS4]. clear LS4.
  unfold f5x16, OSS_VBOFF_A, OSS_OS_VPTR_A in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(sp' - 16, sp'); (f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (E64 : bv_unsigned (Z_to_bv 64 (f + 64)) = f + 64) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (Z_to_bv 64 O) = O) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  zstep. zstep.
  carve_frame 16%nat ST.
  do 3 lstep.
  do 4 zstep.
  zstep.
  zstep. if_cases K; zify_cond K; [exfalso; lia|].
  zstep. zstep. if_false.
  zstep. zstep.
  zstep. if_true.
  do 3 zstep.
  release_frame FR ST sp'.
  zstep.
  zstep. ls. ls.
  zstep. zstep. lstep.
  assert (ES56 : bv_unsigned (Z_to_bv 64 (sp' + 56)) = sp' + 56) by (apply unsigned_lit; lia).
  zstep.
  zstep. if_cases K'; zify_cond K'; [exfalso; lia|].
  zstep.
  do 16 ls.
  apply evt_done. eexists _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma op_exit2I : forall (usp sp' f fl lo OSP : Z) (ra gp tp t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 : word) (LC : list cell) F fc (m : mem),
  0 < f -> f + 128 <= lo -> 0 < fl -> fl + 1 <= lo -> 0 <= OSP < 2^64 ->
  0x6e0000 <= lo -> lo <= sp' -> cells_size LC = 88%nat -> sp' + 88 <= usp - 104 -> usp < 2^63 ->
  stk bsegs m lo sp' -> rw_cells bsegs m sp' LC -> stk bsegs m (sp' + 88) (usp - 104) ->
  rw_cells bsegs m (usp - 104) (fa_saved xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11) ->
  ro_cells bsegs m (f + 120) [C8 (Z_to_bv 64 fl)] -> rw_cells bsegs m fl [C1 (Z_to_bv 8 1)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem),
      ms = MS (mkR xra (wz usp) gp tp t0 t1 t2 xs0 xs1 (wz OSP) (wz f) a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3 t4 t5 t6)
              F (ret_pc xra) fc None m' (seg_rom bsegs)
      /\ munch [(fl, fl + 1)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp /\ rw_cells bsegs m' fl [C1 (Z_to_bv 8 0)])
    (MS (mkR ra (wz sp') gp tp t0 t1 t2 (wz usp) (wz sp') a0 (wz f) a2 a3 a4 a5 a6 a7 s2 (wz OSP) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0xbe2b4) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros F0 FLO FL0 FLLO OR GLO LSP SZ LUSP SPH ST FRl STp FRs FW FLC MI.
  unfold fa_saved in *.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EFL : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  assert (EUS : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep. ls. zstep. zstep. zstep.
  replace (usp - 104) with (usp + -104) in FRs by lia.
  do 13 zstep. zstep.
  replace (usp + -104) with (usp - 104) in FRs by lia.
  pose proof (stk_release bsegs _ _ _ _ ST FRl ltac:(lia)) as ST1. rewrite SZ in ST1. change (Z.of_nat 88%nat) with 88 in ST1.
  pose proof (stk_merge bsegs _ _ _ _ ST1 STp ltac:(lia)) as ST2.
  pose proof (stk_release bsegs _ _ _ _ ST2 FRs ltac:(lia)) as ST3. cbn [cells_size csize Nat.add] in ST3.
  replace (usp - 104 + Z.of_nat 104) with usp in ST3 by lia.
  zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST3| eassumption].
Qed.
