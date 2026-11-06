(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP ZBridge.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Sj_num_walk Sj_stage1_kit Pj_os_kit El_os_pad.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Layout Shadow RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Atp_defsA Atp_fzwA
     Pj_lftoi1A Pj_defsA Pj_os_defsA Pj_os_put1A Pj_os_put2A Pj_os_put3A.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import El_os_pad3A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma pad_segAW : forall (S sp2 f OS BUF N FILL W lo : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s7 s10 s11 t3 t4 t5 t6 : word)
    (j0 j1 j2 j4 j5 j6 h0 h1 h2 : list byte) (ls : list (list byte)) F fc (m : mem),
  length ls = 16%nat ->
  0 < f -> f + 128 <= lo -> 0xd8400 <= f / 8 -> f / 8 + 2147450880 + 16 <= lo -> (f + 128 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= f) ->
  0 < OS -> OS + 288 <= lo -> OS mod 16 = 0 -> OS / 8 + 2147450880 + 37 <= lo ->
  (OS + 288 <= f \/ f + 128 <= OS) -> (f + 128 <= OS / 8 + 2147450880 \/ (OS + 288) / 8 + 2147450880 <= f) ->
  (OS + 288 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= OS) ->
  0x7fff7f800000 <= lo -> lo <= sp2 -> S - 176 <= sp2 <= S - 160 -> S < 2^63 -> 0 < BUF -> 0 <= N -> BUF + N < 2^63 -> 0 <= FILL < 256 -> 0 <= W < 2^63 ->
  bytes_at asegs m (OS / 8 + 2147450880) (repeat z8 36) ->
  rw_cells asegs m sp2 (pad_locals0 j0 j1 j2 (BUF + N) j4 j5 j6) -> rw_cells asegs m (OS + 160) [C8 (wz W)] ->
  rw_cells asegs m f [CB 8 h0; CB 8 h1; CB 8 h2] -> rw_cells asegs m (f / 8 + 2147450880) (map (fun l => CB 1 l) ls) ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (a0' a1' : word) (m1 : mem),
      ms = MS (mkR (wz 0xb1a88) (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) a0' a1' (wz 0xb1a04) (wz (-13)) (wz (-8)) a5 a6 a7
                   (wz f) (wz OS) (wz 2147450880) (wz FILL) (wz (OS + 160)) (wz W) (wz (pad_ns N W)) (wz 0) (wz (f / 8 + 2147450880)) (wz f) t3 t4 t5 t6)
              F (wz 0xb1bb0) fc None m1 (seg_rom asegs)
      /\ munch [(sp2, sp2 + 56); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 sp2 [C8 (wz ((OS + 160) / 8 + 2147450880)); C8 (wz BUF); C8 (wz (OS / 8)); C8 (wz (BUF + N)); CB 8 j4; CB 8 j5; C8 (wz f)]
      /\ rw_cells asegs m1 (OS + 160) [C8 (wz W)]
      /\ rw_cells asegs m1 f [C8 (wz 0x41b58ab3); C8 (wz 0x16a82); C8 (wz 0xb1a04)]
      /\ rw_cells asegs m1 (f / 8 + 2147450880) (map C1 pad_sh12 ++ map (fun l => CB 1 l) (skipn 12 ls)))
    (MS (mkR (wz 0xb1a88) (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) (wz f) a1 a2 a3 a4 a5 a6 a7
             s2 (wz OS) (wz 2147450880) (wz FILL) (wz (OS + 136)) s7 (wz BUF) (wz BUF) s10 s11 t3 t4 t5 t6)
        F (wz 0xb1a88) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros LS F0 FLO FD8 SLO SEP O0 OLO O16 OSLO OF OSH OSH2 LOW LSP SP2R SPH B0 N0 BNH FIR WR SHZ0 FRl WID FH FS MI.
  do 16 (destruct ls as [|? ls]; [discriminate LS|]). destruct ls; [| discriminate LS]. clear LS.
  unfold pad_sh12, pad_locals0 in *. cbn [map app repeat skipn] in *.
  pose proof (munch_refl [(sp2, sp2 + 56); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 sp2) = sp2) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (Z_to_bv 64 (OS + 160)) = OS + 160) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  assert (SHZ : forall m', munch [(sp2, sp2 + 56); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m m' -> wmono asegs m m' -> shz m' OS 288).
  { intros m' MU' _. change 288 with (8 * Z.of_nat 36). apply (shz_of_zero_run m' OS 36); [clear - O16; Z.div_mod_to_equations; lia| lia|].
    eapply bytes_at_agree; [exact SHZ0|]. apply (agree_of_munch _ _ _ _ MU'). intros x Hx. rewrite repeat_length in Hx. cbn [outside]. unfold shad, SHB in *.
    clear - Hx OSLO LSP OSH OF FD8 F0 O0. split; [| split; [| split; [| exact I]]]; Z.div_mod_to_equations; lia. }
  change (id (bytes_at asegs m (OS / 8 + 2147450880) (repeat z8 36))) in SHZ0.
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
  lstep.
  shz_pose SHZ (OS + 160). zstep. shz_norm. zstep. if_false.
  zstep.
  lstep.
  zstep.    replace (BUF - BUF) with 0 by lia.
  zstep. rewrite shr3_div. lstep.
  zstep. if_true.
  zstep.
  zstep.    replace (BUF + N - BUF) with N by lia.
  zstep.
  zstep.
  zstep.
  zstep.
  rewrite (pad_ns_eq N W) by lia.
  apply evt_done. eexists _, _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Definition padW_locals (OS BUF N f : Z) (j4 j5 : list byte) : list cell :=
  [C8 (wz ((OS + 160) / 8 + 2147450880)); C8 (wz BUF); C8 (wz (OS / 8)); C8 (wz (BUF + N)); CB 8 j4; CB 8 j5; C8 (wz f)].
Definition pad_sh12u : list byte := repeat (Z_to_bv 8 (-15)) 4 ++ repeat (Z_to_bv 8 0) 3 ++ repeat (Z_to_bv 8 (-13)) 5.

Lemma pad_joinW : forall (S sp2 f OS BUF N : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 t3 t4 t5 t6 : word) (j4 j5 : list byte) F fc (m : mem),
  0 <= sp2 -> sp2 + 56 < 2^63 -> 0 < BUF -> 0 <= N -> BUF + N < 2^63 ->
  rw_cells asegs m sp2 (padW_locals OS BUF N f j4 j5) ->
  evt asegs (eq (MS (mkR (wz 0xb1a88) (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) (wz (BUF + N)) (wz BUF) a2 a3 a4 a5 a6 a7
                        (wz f) (wz OS) (wz 2147450880) (wz N) (wz (OS + 160)) s7 s8 s9 (wz (f / 8 + 2147450880)) (wz f) t3 t4 t5 t6)
                   F (wz 0xb1c64) fc None m (seg_rom asegs)))
    (MS (mkR (wz 0xb1a88) (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) a0 a1 a2 a3 a4 a5 a6 a7
             (wz f) (wz OS) (wz 2147450880) s8 (wz (OS + 160)) s7 s8 s9 (wz (f / 8 + 2147450880)) (wz f) t3 t4 t5 t6)
        F (wz 0xb1c58) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros S0 SH B0 N0 BNH FRl. unfold padW_locals in FRl.
  assert (ES : bv_unsigned (Z_to_bv 64 sp2) = sp2) by (apply unsigned_lit; lia).
  zstep. zstep.
  zstep.    replace (BUF + N - BUF) with N by lia.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma pad_w1 : forall (S sp2 f OS FILL W ns lo : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (ls4 : list (list byte)) F fc (m : mem),
  length ls4 = 4%nat -> 0 < f -> f + 128 <= lo -> 0 <= f / 8 -> f / 8 + 2147450880 + 16 <= lo -> lo < 2^63 -> 0 < ns < 2^63 ->
  rw_cells asegs m (f / 8 + 2147450880) (map C1 pad_sh12 ++ map (fun l => CB 1 l) ls4) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (wz 0xb1bd4) (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) (wz (f + 32)) (wz ns) (wz FILL) a3 a4 a5 a6 a7
                   (wz f) (wz OS) (wz 2147450880) (wz FILL) (wz (OS + 160)) (wz W) (wz ns) (wz (f + 32)) (wz (f / 8 + 2147450880)) (wz f) t3 t4 t5 t6)
              F (wz 0xb1e8c) fc None m1 (seg_rom asegs)
      /\ munch [(f / 8 + 2147450880 + 4, f / 8 + 2147450880 + 7)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (f / 8 + 2147450880) (map C1 pad_sh12u ++ map (fun l => CB 1 l) ls4))
    (MS (mkR (wz 0xb1a88) (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) a0 a1 a2 a3 a4 a5 a6 a7
             (wz f) (wz OS) (wz 2147450880) (wz FILL) (wz (OS + 160)) (wz W) (wz ns) (wz 0) (wz (f / 8 + 2147450880)) (wz f) t3 t4 t5 t6)
        F (wz 0xb1bb0) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros LS4 F0 FLO FD SLO LOH NS FS MI.
  do 4 (destruct ls4 as [|? ls4]; [discriminate LS4|]). destruct ls4; [| discriminate LS4]. clear LS4.
  unfold pad_sh12 in FS. cbn [map app repeat] in FS.
  pose proof (munch_refl [(f / 8 + 2147450880 + 4, f / 8 + 2147450880 + 7)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  zstep. if_cases K0; zify_cond K0; [exfalso; apply Bool.andb_false_iff in K0; destruct K0 as [K0|K0]; apply Z.ltb_ge in K0; lia|].
  zstep.
  do 3 ls.
  do 3 zstep.
  zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  unfold pad_sh12u. cbn [map app repeat]. eassumption.
Qed.

Lemma sn_walk1 : forall (sp D n c lo : Z) (ra gp tp t0 t1 t2 a3 a4 a5 a6 a7 xs0 xs1 xs2 xs3 xs4 xs5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (b1 : list byte) F fc (m : mem),
  stk asegs m lo sp -> lo <= sp - 64 -> 0x6c2000 <= lo -> sp < 2^63 -> 0 < D -> D + 24 <= lo -> D mod 8 = 0 -> D / 8 + 2147450880 + 3 <= lo ->
  (D + 24 <= D / 8 + 2147450880 \/ D / 8 + 2147450880 + 3 <= D) ->
  1 <= n < 23 -> 0 <= c < 256 ->
  client_consts m -> bytes_at asegs m (D / 8 + 2147450880) [z8; z8; z8] -> rw_cells asegs m D [CB 1 b1] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (j : list byte),
      ms = MS (mkR (wz 0xb1f70) (wz (sp - 64)) gp tp t0 t1 t2 (wz n) (wz c) (wz (D + 1)) (wz c) (wz n) a3 a4 a5 a6 a7
                   (wz D) (wz (D + 1)) xs4 (wz 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz e_asan_memset) fc None m1 (seg_rom asegs)
      /\ munch [(sp - 64, sp); (D, D + 1)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (sp - 64)
      /\ rw_cells asegs m1 (sp - 64) [CB 8 j; C8 xs5; C8 xs4; C8 xs3; C8 xs2; C8 xs1; C8 xs0; C8 ra]
      /\ rw_cells asegs m1 D [C1 (Z_to_bv 8 (2 * n))])
    (MS (mkR ra (wz sp) gp tp t0 t1 t2 xs0 xs1 (wz D) (wz n) (wz c) a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0xb1e8c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO GLO SPH D0 DLO D8 SLO DSH RN RC (G1 & G2 & G3 & G4) SHD X1 MI.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in *.
  pose proof (munch_refl [(sp - 64, sp); (D, D + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (SHZ : forall m', munch [(sp - 64, sp); (D, D + 1)] m m' -> wmono asegs m m' -> shz m' D 24).
  { intros m' MU' _. change 24 with (8 * Z.of_nat 3). apply (shz_of_zero_run m' D 3); [exact D8| lia|].
    eapply bytes_at_agree; [exact SHD|]. apply (agree_of_munch _ _ _ _ MU'). intros x Hx. cbn [repeat length] in Hx. cbn [outside]. unfold shad, SHB in *.
    clear - Hx SLO DSH LO D8. repeat split; try exact I; Z.div_mod_to_equations; lia. }
  change (id (bytes_at asegs m (D / 8 + 2147450880) [z8; z8; z8])) in SHD.
  zstep. carve_frame 64%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 64 _ [] [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR. forget_junk FR.
  do 7 lstep.
  zstep. zstep.
  zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?Z.mod_small in K0 by lia; lia|].
  do 2 zstep.
  do 3 zstep.
  clear G1 G2 G3 G4.
  zstep.
  zstep. if_cases K1; zify_cond K1; [exfalso; rewrite ?Z.mod_small in K1 by lia; lia|].
  zstep. rewrite shr3_div. zstep.
  shz_pose SHZ D. zstep. shz_norm. zstep. if_false.
  zstep.    replace (Z.shiftl n 1) with (2 * n) by (rewrite Z.shiftl_mul_pow2; lia).
  ls.
  zstep.
  zstep. if_cases K2; zify_cond K2; [| exfalso; rewrite ?Z.mod_small in K2 by lia; lia].
  do 3 zstep. zstep.
  apply evt_done. eexists _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|].
  split; [eassumption| eassumption].
Qed.

Lemma sn_walk2 : forall (sp D n c lo : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs0 xs1 xs2 xs3 xs4 xs5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (j b4 : list byte) F fc (m : mem),
  stk asegs m lo (sp - 64) -> lo <= sp - 64 -> 0x6c2000 <= lo -> sp < 2^63 -> 0 < D -> D + 24 <= lo -> D mod 8 = 0 -> D / 8 + 2147450880 + 3 <= lo ->
  (D + 24 <= D / 8 + 2147450880 \/ D / 8 + 2147450880 + 3 <= D) ->
  1 <= n < 23 ->
  bytes_at asegs m (D / 8 + 2147450880) [z8; z8; z8] ->
  rw_cells asegs m (sp - 64) [CB 8 j; C8 xs5; C8 xs4; C8 xs3; C8 xs2; C8 xs1; C8 xs0; C8 ra] ->
  rw_cells asegs m (D + 1 + n) [CB 1 b4] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = MS (mkR ra (wz sp) gp tp t0 t1 t2 xs0 xs1 (wz (D + 1 + n)) (wz 0) a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m1 (seg_rom asegs)
      /\ munch [(D + 1 + n, D + 1 + n + 1)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo sp
      /\ rw_cells asegs m1 (D + 1 + n) [C1 (Z_to_bv 8 0)])
    (MS (mkR (wz 0xb1f70) (wz (sp - 64)) gp tp t0 t1 t2 (wz n) (wz c) a0 a1 a2 a3 a4 a5 a6 a7
             (wz D) (wz (D + 1)) xs4 (wz 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0xb1f70) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO GLO SPH D0 DLO D8 SLO DSH RN SHD FR X4 MI.
  pose proof (munch_refl [(D + 1 + n, D + 1 + n + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 (sp - 64)) = sp - 64) by (apply unsigned_lit; lia).
  assert (SHZ : forall m', munch [(D + 1 + n, D + 1 + n + 1)] m m' -> wmono asegs m m' -> shz m' D 24).
  { intros m' MU' _. change 24 with (8 * Z.of_nat 3). apply (shz_of_zero_run m' D 3); [exact D8| lia|].
    eapply bytes_at_agree; [exact SHD|]. apply (agree_of_munch _ _ _ _ MU'). intros x Hx. cbn [repeat length] in Hx. cbn [outside]. unfold shad, SHB in *.
    clear - Hx SLO DSH LO D8 RN. repeat split; try exact I; Z.div_mod_to_equations; lia. }
  change (id (bytes_at asegs m (D / 8 + 2147450880) [z8; z8; z8])) in SHD.
  zstep.    replace (D + 1 + n) with (D + (1 + n)) in X4 |- * by lia.
  set (E1 := D + (1 + n)) in *.
  assert (EE : bv_unsigned (Z_to_bv 64 E1) = E1) by (apply unsigned_lit; lia).
  zstep. rewrite shr3_div. zstep.
  shz_pose SHZ E1. zstep. shz_norm. zstep. if_false.
  ls.
  replace (sp - 64) with (sp + -64) in * by lia.
  do 7 zstep. zstep.
  replace (sp + -64 + 64) with sp by lia.
  pose proof (stk_release asegs _ _ _ _ ST FR ltac:(lia)) as ST1. cbn [cells_size csize Nat.add] in ST1. replace (sp + -64 + Z.of_nat 64) with sp in ST1 by lia.
  zstep.
  subst E1.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST1| eassumption].
Qed.

Lemma pad_w2 : forall (S sp2 f OS BUF N FILL W ns : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j4 j5 : list byte) F fc (m : mem),
  0 < f -> f + 128 < 2^63 -> 0 < OS -> OS + 288 < 2^63 -> OS mod 16 = 0 -> 0 <= sp2 -> sp2 + 56 < 2^63 -> 0 < BUF -> 0 <= N -> BUF + N < 2^63 -> 1 <= ns < 23 ->
  shz m OS 288 -> shz m PJ_NULSB_VT_A 24 ->
  rw_cells asegs m sp2 (padW_locals OS BUF N f j4 j5) -> rw_cells asegs m (f + 32) [C1 (Z_to_bv 8 (2 * ns))] ->
  rw_cells asegs m OS [C8 (wz PJ_SB_VPTR_A)] ->
  ro_cells asegs m PJ_NULSB_VT_A [C8 (wz PJ_XSPUTN_A); C8 (wz PJ_OVERFLOW_A); C8 (wz 8)] ->
  mem_inv asegs m ->
  evt asegs (eq (MS (mkR (wz 0xb1c24) (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) (wz OS) (wz (f + 33)) (wz ns) (wz PJ_XSPUTN_A) a4 a5 a6 a7
                        (wz f) (wz OS) (wz 2147450880) (wz FILL) (wz (OS + 160)) (wz W) (wz ns) (wz (f + 32)) (wz (f / 8 + 2147450880)) (wz f) t3 t4 t5 t6)
                   F (wz PJ_XSPUTN_A) fc None m (seg_rom asegs)))
    (MS (mkR (wz 0xb1bd4) (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) a0 a1 a2 a3 a4 a5 a6 a7
             (wz f) (wz OS) (wz 2147450880) (wz FILL) (wz (OS + 160)) (wz W) (wz ns) (wz (f + 32)) (wz (f / 8 + 2147450880)) (wz f) t3 t4 t5 t6)
        F (wz 0xb1bd4) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros F0 FH O0 OH O16 S0 SP2R B0 N0 BNH NS SHZ0 SHV FRl STR SB VT MI.
  unfold PJ_NULSB_VT_A, PJ_XSPUTN_A, PJ_OVERFLOW_A, PJ_SB_VPTR_A, padW_locals in *.
  assert (ES : bv_unsigned (Z_to_bv 64 sp2) = sp2) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (Z_to_bv 64 OS) = OS) by (apply unsigned_lit; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  zstep.
  zstep.    rewrite (land1_double ns) by lia.
  zstep. if_false.
  zstep.    replace (f + 32 + 1) with (f + 33) by lia.
  zstep.
  zstep. zstep.
  shz_pose SHZ0 OS. zstep. shz_norm. zstep. if_false.
  zstep. zstep.
  zstep. zstep.
  pose proof (SHV 0x15d4a8 ltac:(lia)) as RD. change (0x15d4a8 / 8 + 2147450880) with 2147629717 in RD.
  zstep. shz_norm. zstep. if_false.
  zstep.
  do 3 zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma pad_w3 : forall (S sp2 f OS BUF N FILL W ns lo : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j4 j5 : list byte) (ls4 : list (list byte)) F fc (m : mem),
  length ls4 = 4%nat -> 0 < f -> f + 128 <= lo -> 0 <= f / 8 -> f / 8 + 2147450880 + 16 <= lo -> lo <= sp2 -> sp2 + 56 < 2^63 ->
  (f + 128 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= f) ->
  0 < BUF -> 0 <= N -> BUF + N < 2^63 -> 1 <= ns < 23 ->
  rw_cells asegs m sp2 (padW_locals OS BUF N f j4 j5) -> rw_cells asegs m (f + 32) [C1 (Z_to_bv 8 (2 * ns))] ->
  rw_cells asegs m (f / 8 + 2147450880) (map C1 pad_sh12u ++ map (fun l => CB 1 l) ls4) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (wz 0xb1c24) (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) (wz (BUF + N)) (wz BUF) a2 a3 a4 a5 a6 a7
                   (wz f) (wz OS) (wz 2147450880) (wz N) (wz (OS + 160)) (wz ns) (wz ns) (wz (f + 32)) (wz (f / 8 + 2147450880)) (wz f) t3 t4 t5 t6)
              F (wz 0xb1c64) fc None m1 (seg_rom asegs)
      /\ munch [(f / 8 + 2147450880 + 4, f / 8 + 2147450880 + 7)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (f / 8 + 2147450880) (map C1 pad_sh12 ++ map (fun l => CB 1 l) ls4))
    (MS (mkR (wz 0xb1c24) (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) (wz ns) a1 a2 a3 a4 a5 a6 a7
             (wz f) (wz OS) (wz 2147450880) (wz FILL) (wz (OS + 160)) (wz W) (wz ns) (wz (f + 32)) (wz (f / 8 + 2147450880)) (wz f) t3 t4 t5 t6)
        F (wz 0xb1c24) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros LS4 F0 FLO FD SLO LSP SPH SEP B0 N0 BNH NS FRl STR FS MI.
  do 4 (destruct ls4 as [|? ls4]; [discriminate LS4|]). destruct ls4; [| discriminate LS4]. clear LS4.
  unfold pad_sh12u, padW_locals in *. cbn [map app repeat] in FS.
  pose proof (munch_refl [(f / 8 + 2147450880 + 4, f / 8 + 2147450880 + 7)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 sp2) = sp2) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  zstep.
  zstep.
  zstep.    rewrite (land1_double ns) by lia.
  zstep. if_true.
  zstep. do 3 ls.
  zstep. if_false.
  zstep. zstep.
  zstep.    replace (BUF + N - BUF) with N by lia.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  unfold pad_sh12. cbn [map app repeat]. eassumption.
Qed.

Lemma pad_segBW : forall (S sp2 f OS BUF N lo : Z) (ra gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s7 s8 s9 t3 t4 t5 t6 : word) (j4 j5 : list byte) F fc (m : mem),
  0 < f -> f + 128 < 2^63 -> 0 < OS -> OS + 288 < 2^63 -> OS mod 16 = 0 -> 0 <= sp2 -> S - 176 <= sp2 <= S - 160 -> S < 2^63 -> 0 < BUF -> BUF + N < 2^63 -> 0 < N < 2^63 ->
  shz m OS 288 -> shz m PJ_NULSB_VT_A 24 ->
  rw_cells asegs m sp2 (padW_locals OS BUF N f j4 j5) ->
  rw_cells asegs m OS [C8 (wz PJ_SB_VPTR_A)] ->
  ro_cells asegs m PJ_NULSB_VT_A [C8 (wz PJ_XSPUTN_A); C8 (wz PJ_OVERFLOW_A); C8 (wz 8)] ->
  mem_inv asegs m ->
  evt asegs (eq (MS (mkR (wz 0xb1ca0) (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) (wz OS) (wz BUF) (wz N) (wz PJ_XSPUTN_A) a4 a5 a6 a7
                        (wz f) (wz OS) (wz 2147450880) (wz N) (wz (OS + 160)) s7 s8 s9 (wz (f / 8 + 2147450880)) (wz f) t3 t4 t5 t6)
                   F (wz PJ_XSPUTN_A) fc None m (seg_rom asegs)))
    (MS (mkR ra (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) (wz (BUF + N)) (wz BUF) a2 a3 a4 a5 a6 a7
             (wz f) (wz OS) (wz 2147450880) (wz N) (wz (OS + 160)) s7 s8 s9 (wz (f / 8 + 2147450880)) (wz f) t3 t4 t5 t6)
        F (wz 0xb1c64) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros F0 FH O0 OH O16 S0 SP2R SPH B0 BNH NR SHZ0 SHV FRl SB VT MI. unfold padW_locals in FRl.
  unfold PJ_NULSB_VT_A, PJ_XSPUTN_A, PJ_OVERFLOW_A, PJ_SB_VPTR_A in *.
  assert (ES : bv_unsigned (Z_to_bv 64 sp2) = sp2) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (Z_to_bv 64 OS) = OS) by (apply unsigned_lit; lia).
  zstep. if_cases K0; zify_cond K0; [exfalso; lia|].
  zstep. zstep.
  shz_pose SHZ0 OS. zstep. shz_norm. zstep. if_false.
  zstep. zstep.
  zstep. zstep.
  pose proof (SHV 0x15d4a8 ltac:(lia)) as RD. change (0x15d4a8 / 8 + 2147450880) with 2147629717 in RD.
  zstep. shz_norm. zstep. if_false.
  zstep.
  do 3 zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma pad_exit1W : forall (S sp2 f lo OS N W : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 t3 t4 t5 t6 h0 : word) (sh : list byte) (ls4 : list (list byte)) F fc (m : mem),
  length sh = 12%nat -> length ls4 = 4%nat ->
  0 < f -> f + 128 <= lo -> 0 <= f / 8 -> f / 8 + 2147450880 + 16 <= lo -> (f + 128 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= f) ->
  0 <= OS -> OS + 288 <= lo -> (OS + 288 <= f \/ f + 128 <= OS) -> (OS + 288 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= OS) ->
  lo <= sp2 -> sp2 + 8 < 2^63 -> 0 <= N < 2^64 -> 0 <= W < 2^64 ->
  shz m OS 288 ->
  rw_cells asegs m sp2 [C8 (wz ((OS + 160) / 8 + 2147450880))] -> rw_cells asegs m (OS + 160) [C8 (wz W)] ->
  rw_cells asegs m f [C8 h0] -> rw_cells asegs m (f / 8 + 2147450880) (map C1 sh ++ map (fun l => CB 1 l) ls4) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = MS (mkR ra (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) (wz (-11)) a1 a2 a3 a4 a5 a6 a7
                   (wz f) (wz OS) (wz 2147450880) (wz N) (wz (OS + 160)) s7 s8 s9 (wz (f / 8 + 2147450880)) (wz f) t3 t4 t5 t6)
              F (wz 0xb1d10) fc None m1 (seg_rom asegs)
      /\ munch [(OS + 160, OS + 168); (f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (OS + 160) [C8 (wz 0)] /\ rw_cells asegs m1 f [C8 (wz 0x45e0360e)]
      /\ rw_cells asegs m1 (f / 8 + 2147450880) (map C1 f5x16))
    (MS (mkR ra (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) a0 a1 a2 a3 a4 a5 a6 a7
             (wz f) (wz OS) (wz 2147450880) (wz N) (wz (OS + 160)) s7 s8 s9 (wz (f / 8 + 2147450880)) (wz f) t3 t4 t5 t6)
        F (wz 0xb1ca4) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros LS LS4 F0 FLO FD SLO SEP O0 OLO OF OSH LSP SPH NR WR SHZ0 L0 WID FH FS MI.
  do 12 (destruct sh as [|? sh]; [discriminate LS|]). destruct sh; [| discriminate LS]. clear LS.
  do 4 (destruct ls4 as [|? ls4]; [discriminate LS4|]). destruct ls4; [| discriminate LS4]. clear LS4.
  cbn [map app repeat] in FS.
  pose proof (munch_refl [(OS + 160, OS + 168); (f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 sp2) = sp2) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (Z_to_bv 64 (OS + 160)) = OS + 160) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  zstep.
  shz_pose SHZ0 (OS + 160). zstep. shz_norm. zstep. if_false.
  lstep.
  zstep.
  zstep. zstep. lstep.
  zstep. if_false.
  zstep.
  do 16 ls.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. unfold f5x16. cbn [map app repeat]. eassumption.
Qed.
