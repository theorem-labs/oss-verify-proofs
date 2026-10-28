(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Sj_num_walk Sj_stage1_kit Pj_os_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Atp_fzwA Pj_lftoi1A Pj_defsA Pj_os_defsA Pj_os_put1A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma acc_agreeP : forall (m m' : mem) a n, acc bsegs m a n -> agree_on (fun x => shad a <= x <= shad (a + n)) m m' -> acc bsegs m' a n.
Proof.
  intros m m' a n H AG i Hi. destruct (H i Hi) as (b & Hb & Hok). exists b. split; [| exact Hok].
  apply (bytes_at_agree bsegs m m' _ _ Hb). intros x Hx. cbn [length] in Hx. apply AG. unfold shad in *. Z.div_mod_to_equations. lia.
Qed.

Lemma cells_size_map_C1p : forall bs : list byte, cells_size (map C1 bs) = length bs.
Proof. induction bs as [|b bs IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite IH. reflexivity. Qed.
Lemma cells_size_map_CB1 : forall ls : list (list byte), cells_size (map (fun l => CB 1 l) ls) = length ls.
Proof. induction ls as [|b ls IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite IH. reflexivity. Qed.

Definition pad_sh12 : list byte := repeat (Z_to_bv 8 (-15)) 4 ++ repeat (Z_to_bv 8 (-8)) 3 ++ repeat (Z_to_bv 8 (-13)) 5.

Lemma pad_segA : forall (S f OS BUF N FILL lo : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s7 s9 s11 t3 t4 t5 t6 : word)
    (j0 j1 j2 j3 j4 j5 j6 j8 j9 j10 h0 h1 h2 : list byte) (ls : list (list byte)) F fc (m : mem),
  length ls = 16%nat ->
  0 < f -> f + 128 <= lo -> 0xd9c00 <= f / 8 -> f / 8 + 2147450880 + 16 <= lo -> (f + 128 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= f) ->
  0 < OS -> OS + 288 <= lo -> OS mod 16 = 0 -> OS / 8 + 2147450880 + 37 <= lo ->
  (OS + 288 <= f \/ f + 128 <= OS) -> (f + 128 <= OS / 8 + 2147450880 \/ (OS + 288) / 8 + 2147450880 <= f) ->
  (OS + 288 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= OS) ->
  0x7fff7f800000 <= lo -> lo <= S - 192 -> S < 2^63 -> 0 < BUF -> 0 <= N -> BUF + N < 2^63 -> 0 <= FILL < 256 ->
  bytes_at bsegs m (OS / 8 + 2147450880) (repeat z8 36) ->
  rw_cells bsegs m (S - 192) (pad_locals0 j0 j1 j2 j3 j4 j5 j6 (BUF + N) j8 j9 j10) -> rw_cells bsegs m (OS + 160) [C8 (wz 0)] ->
  rw_cells bsegs m f [CB 8 h0; CB 8 h1; CB 8 h2] -> rw_cells bsegs m (f / 8 + 2147450880) (map (fun l => CB 1 l) ls) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (wz 0xb1a28) (wz (S - 192)) gp tp t0 t1 t2 (wz S) (wz (S - 192)) (wz BUF) (wz (BUF + N)) (wz 0xb19a4) (wz (-13)) (wz (-8)) a5 a6 a7
                   (wz f) (wz OS) (wz 2147450880) (wz N) (wz 0) (wz f) (wz BUF) (wz 0) (wz 0) (wz (f / 8 + 2147450880)) t3 t4 t5 t6)
              F (wz 0xb1c1c) fc None m1 (seg_rom bsegs)
      /\ munch [(S - 192, S - 104); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (S - 192) [CB 8 j0; CB 8 j1; CB 8 j2; C8 (wz ((OS + 160) / 8 + 2147450880)); C8 (wz (OS + 160)); C8 (wz BUF); C8 (wz (OS / 8)); C8 (wz (BUF + N)); CB 8 j8; CB 8 j9; C8 (wz f)]
      /\ rw_cells bsegs m1 (OS + 160) [C8 (wz 0)]
      /\ rw_cells bsegs m1 f [C8 (wz 0x41b58ab3); C8 (wz 0x16a74); C8 (wz 0xb19a4)]
      /\ rw_cells bsegs m1 (f / 8 + 2147450880) (map C1 pad_sh12 ++ map (fun l => CB 1 l) (skipn 12 ls)))
    (MS (mkR (wz 0xb1a28) (wz (S - 192)) gp tp t0 t1 t2 (wz S) (wz (S - 192)) (wz f) a1 a2 a3 a4 a5 a6 a7
             s2 (wz OS) (wz 2147450880) (wz FILL) (wz (OS + 136)) s7 (wz BUF) s9 (wz BUF) s11 t3 t4 t5 t6)
        F (wz 0xb1a28) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LS F0 FLO FD8 SLO SEP O0 OLO O16 OSLO OF OSH OSH2 LOW LSP SPH B0 N0 BNH FIR SHZ0 FRl WID FH FS MI.
  do 16 (destruct ls as [|? ls]; [discriminate LS|]). destruct ls; [| discriminate LS]. clear LS.
  unfold pad_sh12, pad_locals0 in *. cbn [map app repeat skipn] in *.
  pose proof (munch_refl [(S - 192, S - 104); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 (S - 192)) = S - 192) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (Z_to_bv 64 (OS + 160)) = OS + 160) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  assert (SHZ : forall m', munch [(S - 192, S - 104); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m m' -> wmono bsegs m m' -> shz m' OS 288).
  { intros m' MU' _. change 288 with (8 * Z.of_nat 36). apply (shz_of_zero_run m' OS 36); [clear - O16; Z.div_mod_to_equations; lia| lia|].
    eapply bytes_at_agree; [exact SHZ0|]. apply (agree_of_munch _ _ _ _ MU'). intros x Hx. rewrite repeat_length in Hx. cbn [outside]. unfold shad, SHB in *.
    clear - Hx OSLO LSP OSH OF FD8 F0 O0. split; [| split; [| split; [| exact I]]]; Z.div_mod_to_equations; lia. }
  change (id (bytes_at bsegs m (OS / 8 + 2147450880) (repeat z8 36))) in SHZ0.
  do 3 zstep.
  zstep. if_cases K0; zify_cond K0; [| exfalso; lia].
  lstep.
  do 3 zstep. zstep. rewrite shr3_div. do 5 zstep.
  do 3 lstep.
  zstep. zstep.
  do 12 ls.
  zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
  zstep.    replace (OS + 136 + 24) with (OS + 160) by lia.
  zstep. rewrite shr3_div. zstep.
  shz_pose SHZ (OS + 160). zstep. shz_norm. zstep. if_false.
  lstep.
  zstep.
  zstep.
  zstep.    replace (BUF + N - BUF) with N by lia.
  lstep.
  zstep. if_cases K2; zify_cond K2; [| exfalso; lia].
  zstep.
  lstep.
  zstep.    replace (BUF - BUF) with 0 by lia.
  zstep.
  replace (Z.land OS 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; clear - O16; Z.div_mod_to_equations; lia).
  zstep. rewrite shr3_div. lstep.
  zstep. if_true.
  zstep. if_true.
  zstep. zstep.
  zstep.    replace (BUF + N - BUF) with N by lia.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma pad_segB : forall (S f OS BUF N lo : Z) (gp tp t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (j0 j1 j2 j8 j9 : list byte) F fc (m : mem),
  0 < f -> f + 128 < 2^63 -> 0 < OS -> OS + 288 < 2^63 -> OS mod 16 = 0 -> 0 <= S - 192 -> S < 2^63 -> 0 < BUF -> BUF + N < 2^63 -> 0 < N < 2^63 ->
  shz m OS 288 -> shz m PJ_NULSB_VT_A 24 ->
  rw_cells bsegs m (S - 192) [CB 8 j0; CB 8 j1; CB 8 j2; C8 (wz ((OS + 160) / 8 + 2147450880)); C8 (wz (OS + 160)); C8 (wz BUF); C8 (wz (OS / 8)); C8 (wz (BUF + N)); CB 8 j8; CB 8 j9; C8 (wz f)] ->
  rw_cells bsegs m OS [C8 (wz PJ_SB_VPTR_A)] ->
  ro_cells bsegs m PJ_NULSB_VT_A [C8 (wz PJ_XSPUTN_A); C8 (wz PJ_OVERFLOW_A); C8 (wz 8)] ->
  mem_inv bsegs m ->
  evt bsegs (eq (MS (mkR (wz 0xb1c60) (wz (S - 192)) gp tp t0 t1 t2 (wz S) (wz (S - 192)) (wz OS) (wz BUF) (wz N) (wz PJ_XSPUTN_A) (wz (-8)) a5 a6 a7
                        (wz f) (wz OS) (wz 2147450880) (wz N) (wz 0) (wz f) (wz BUF) (wz 0) (wz 0) (wz (f / 8 + 2147450880)) t3 t4 t5 t6)
                   F (wz PJ_XSPUTN_A) fc None m (seg_rom bsegs)))
    (MS (mkR (wz 0xb1a28) (wz (S - 192)) gp tp t0 t1 t2 (wz S) (wz (S - 192)) (wz BUF) (wz (BUF + N)) (wz 0xb19a4) (wz (-13)) (wz (-8)) a5 a6 a7
             (wz f) (wz OS) (wz 2147450880) (wz N) (wz 0) (wz f) (wz BUF) (wz 0) (wz 0) (wz (f / 8 + 2147450880)) t3 t4 t5 t6)
        F (wz 0xb1c1c) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros F0 FH O0 OH O16 S0 SPH B0 BNH NR SHZ0 SHV FRl SB VT MI.
  unfold PJ_NULSB_VT_A, PJ_XSPUTN_A, PJ_OVERFLOW_A, PJ_SB_VPTR_A in *.
  assert (ES : bv_unsigned (Z_to_bv 64 (S - 192)) = S - 192) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (Z_to_bv 64 OS) = OS) by (apply unsigned_lit; lia).
  zstep. if_cases K0; zify_cond K0; [exfalso; lia|].
  zstep. if_false.
  zstep. zstep.
  shz_pose SHZ0 OS. zstep. shz_norm. zstep. if_false.
  zstep. zstep.
  zstep. zstep.
  pose proof (SHV 0x168e08 ltac:(lia)) as RD. change (0x168e08 / 8 + 2147450880) with 2147635649 in RD.
  zstep. shz_norm.
  zstep.
  zstep. if_false.
  zstep.
  do 3 zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.
