(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2 Sj_new Sj_h_dtor Sj_h_alloc Atp_fzwA Atp_pdtorA Sj_h_layout Atp_hkit3A Sj_h_parsew Pj_pidwA Sj_hkitB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation PIREGF ra sp gp tp t0 t1 t2 s1 RES P BUF blen a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 :=
  (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 RES) s1
       a0 a1 a2 a3 a4 a5 a6 a7
       (Z_to_bv 64 blen) (Z_to_bv 64 BUF) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 (P + 64)) (Z_to_bv 64 (P + 72)) (Z_to_bv 64 0) (Z_to_bv 64 (P + 24))
       (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6) (only parsing).

Lemma pi_walk9 : forall (RES P BUF blen IMPL : Z) (b0 b16 b48 b49 : byte) (p1 p17 p57 p12 p28 p50 : list byte)
    (err tape sbuf dcap maxcap lb lbcap nsi idx nxt cap md oc ia bufv lenv docv : word)
    (ra sp gp tp t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  0x6e0000 <= P -> P + 80 < 2^63 -> 0 < IMPL -> IMPL + 96 < 2^63 -> (IMPL + 96 <= 0x10000 \/ 0x6e0000 <= IMPL) -> (P + 80 <= IMPL \/ IMPL + 96 <= P) -> IMPL mod 8 = 0 ->
  pt_shz [(IMPL, IMPL + 96)] m P IMPL -> vt_dpi m ->
  rw_cells bsegs m P (pid_cells b0 p1 (Z_to_bv 64 IMPL) b16 p17 err tape sbuf dcap maxcap z8 p57 lb lbcap) ->
  rw_cells bsegs m IMPL (impl16 (Z_to_bv 64 0x17a150) nsi p12 idx nxt p28 cap md b48 b49 p50 oc ia bufv lenv docv) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = entry_st (Z_to_bv 64 0xb78e4) sp gp tp t0 t1 t2 (Z_to_bv 64 RES) s1x
             (Z_to_bv 64 IMPL) (Z_to_bv 64 BUF) (Z_to_bv 64 blen) (Z_to_bv 64 (P + 24)) (Z_to_bv 64 0xf5768) a5 a6 a7
             (Z_to_bv 64 blen) (Z_to_bv 64 BUF) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 (P + 64)) (Z_to_bv 64 (P + 72)) (Z_to_bv 64 0) (Z_to_bv 64 (P + 24))
             (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6 F fc e_parse m1
      /\ munch [(IMPL, IMPL + 96)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 P (pid_cells b0 p1 (Z_to_bv 64 IMPL) b16 p17 err tape sbuf dcap maxcap z8 p57 lb lbcap)
      /\ rw_cells bsegs m1 IMPL (impl16 (Z_to_bv 64 0x17a150) nsi p12 idx nxt p28 cap md z8 b49 p50 oc ia bufv lenv docv))
    (MS (PIREGF ra sp gp tp t0 t1 t2 s1x RES P BUF blen a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xb785c) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros P0 PH I0 IH IS SEP I8 SHZ VT PC IC MI.
  unfold entry_st, e_parse, pid_cells, impl16, vt_dpi in *.
  pose proof (munch_refl [(IMPL, IMPL + 96)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EUI : bv_unsigned (Z_to_bv 64 IMPL) = IMPL) by (apply unsigned_lit; lia).
  destruct (SHZ m MU WM) as (SHP & SHI & _).
  pose proof (SHP (P + 56) ltac:(lia)) as RD0. pose proof (SHP (P + 8) ltac:(lia)) as RD1. pose proof (SHI (IMPL + 48) ltac:(lia)) as RD2.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. if_false.
  zstep. shz_norm. zstep. if_false.
  zstep.
  zstep. if_cases KZ; zify_cond KZ; [exfalso; lia|].
  zstep. rewrite (land7_mod8 IMPL I8). zstep. if_false.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  ls.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => destruct (SHZ mm MU' WM') as (_ & SHI' & SHV) end.
  pose proof (SHI' IMPL ltac:(lia)) as RD3. pose proof (SHV 0x17a150 ltac:(lia)) as RD4.
  change (0x17a150 / 8 + 2147450880) with 2147644458 in RD4.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep.
  zstep. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; eassumption.
Qed.

Definition res_cells0 (j0 j8 j16 j20 : list byte) : list cell := [CB 8 j0; CB 8 j8; CB 4 j16; CB 4 j20].

Lemma pi_walk10a : forall (usp lo RES P BUF blen : Z) (j0 j8 j16 j20 : list byte)
    (gp tp t0 t1 t2 s1x a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c : word) F fc (m : mem),
  stk bsegs m lo (usp + -112) -> lo <= usp - 112 -> 0x6e0000 <= lo -> usp <= RES -> RES + 24 < 2^63 -> 0x6e0000 <= P -> P + 80 <= lo ->
  (forall m' : mem, munch [(usp - 112, usp); (RES, RES + 24)] m m' -> wmono bsegs m m' -> shz m' RES 24) ->
  rw_cells bsegs m RES (res_cells0 j0 j8 j16 j20) ->
  rw_cells bsegs m (usp + -112) (pid_frame (C8 (Z_to_bv 64 (P + 24))) rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem), ret_st rac (Z_to_bv 64 usp) gp tp s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c (Z_to_bv 64 (RES + 16)) m1 ms
      /\ ms_fcsr ms = fc /\ munch [(usp - 112, usp); (RES, RES + 24)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp
      /\ rw_cells bsegs m1 RES [C8 (Z_to_bv 64 (P + 24)); C8 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); CB 4 j20])
    (MS (PIREGF (Z_to_bv 64 0xb78e4) (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 s1x RES P BUF blen (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb78e4) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO GLO RLO RH P0 PLO SHZ RC FR MI.
  unfold res_cells0, pid_frame in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 112, usp); (RES, RES + 24)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (SHZ m MU WM RES ltac:(lia)) as RD0.
  zstep. zstep. if_false.
  zstep. zstep. if_true.
  zstep. if_cases KR; zify_cond KR; [exfalso; lia|].
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHZ mm MU' WM' (RES + 8) ltac:(lia)) as RD1 end.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. lstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHZ mm MU' WM' (RES + 16) ltac:(lia)) as RD2 end.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  ls. zstep.
  do 13 zstep. zstep.
  release_frame FR ST usp.
  zstep.
  apply evt_done. eexists. split; [unfold ret_st; do 16 eexists; cbv delta [mkR]; reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| eassumption].
Qed.

Lemma pi_walk10b : forall (RES P BUF blen : Z) (v : word)
    (sp gp tp t0 t1 t2 s1x a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  bv_unsigned v <> 0 -> bv_unsigned v < 64 -> 0 < RES -> RES + 24 < 2^63 ->
  evt bsegs (eq (entry_st (Z_to_bv 64 0xb790c) sp gp tp t0 t1 t2 (Z_to_bv 64 RES) (Z_to_bv 64 (RES + 16))
                   (Z_to_bv 64 RES) (Z_to_bv 64 0) (Z_to_bv 64 16) a3 a4 a5 a6 a7
                   v (Z_to_bv 64 BUF) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 (P + 64)) (Z_to_bv 64 (P + 72)) (Z_to_bv 64 0) (Z_to_bv 64 (P + 24))
                   (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6 F fc e_asan_memset m))
    (MS (PIREGF (Z_to_bv 64 0xb78e4) sp gp tp t0 t1 t2 s1x RES P BUF blen v a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb78e4) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros V0 V64 R0 RH.
  unfold entry_st, e_asan_memset in *.
  zstep. zstep. if_cases KV; zify_cond KV; [exfalso; lia|].
  zstep.
  zstep. if_cases K; [exfalso; zify_cond K; exact (V0 K)|].
  zstep. if_cases KR; zify_cond KR; [exfalso; lia|].
  zstep. zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma pi_walk11 : forall (usp lo RES : Z) (z16 j16 j20 : list byte) (c0 : word)
    (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c : word) F fc (m : mem),
  stk bsegs m lo (usp + -112) -> lo <= usp - 112 -> 0x6e0000 <= lo -> usp <= RES -> RES + 24 < 2^63 ->
  shz m RES 24 ->
  rw_cells bsegs m RES [CB 16 z16; CB 4 j16; CB 4 j20] ->
  rw_cells bsegs m (usp + -112) (pid_frame (C8 c0) rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem), ret_st rac (Z_to_bv 64 usp) gp tp s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c (Z_to_bv 64 0) m1 ms
      /\ ms_fcsr ms = fc /\ munch [(usp - 112, usp); (RES, RES + 24)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp
      /\ rw_cells bsegs m1 RES [CB 16 z16; C4 s2; CB 4 j20])
    (MS (mkR (Z_to_bv 64 0xb790c) (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 RES) (Z_to_bv 64 (RES + 16)) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb790c) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO GLO RLO RH SHZ RC FR MI.
  unfold pid_frame in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 112, usp); (RES, RES + 24)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (SHZ (RES + 16) ltac:(lia)) as RD0.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep.
  do 13 zstep. zstep.
  release_frame FR ST usp.
  zstep.
  apply evt_done. eexists. split; [unfold ret_st; do 16 eexists; cbv delta [mkR]; reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| eassumption].
Qed.

Lemma pi_walk12 : forall (usp lo RES : Z) (z16 j16 j20 : list byte) (c0 : word)
    (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c : word) F fc (m : mem),
  stk bsegs m lo (usp + -112) -> lo <= usp - 112 -> 0x6e0000 <= lo -> usp <= RES -> RES + 24 < 2^63 ->
  shz m RES 24 ->
  rw_cells bsegs m RES [CB 16 z16; CB 4 j16; CB 4 j20] ->
  rw_cells bsegs m (usp + -112) (pid_frame (C8 c0) rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem), ret_st rac (Z_to_bv 64 usp) gp tp s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c (Z_to_bv 64 2) m1 ms
      /\ ms_fcsr ms = fc /\ munch [(usp - 112, usp); (RES, RES + 24)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp
      /\ rw_cells bsegs m1 RES [CB 16 z16; C4 (Z_to_bv 64 2); CB 4 j20])
    (MS (mkR (Z_to_bv 64 0xb7a1c) (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 RES) (Z_to_bv 64 (RES + 16)) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb7a1c) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO GLO RLO RH SHZ RC FR MI.
  unfold pid_frame in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 112, usp); (RES, RES + 24)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (SHZ (RES + 16) ltac:(lia)) as RD0.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. ls. zstep.
  do 13 zstep. zstep.
  release_frame FR ST usp.
  zstep.
  apply evt_done. eexists. split; [unfold ret_st; do 16 eexists; cbv delta [mkR]; reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| eassumption].
Qed.
