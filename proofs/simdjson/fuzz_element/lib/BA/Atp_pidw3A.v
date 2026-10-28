(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2 Sj_new Sj_h_dtor Sj_h_alloc. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Atp_pdtorA. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_layout. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_hkit3A. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_parsew. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_pidwA Sj_hkitB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation PIREGT ra sp gp tp t0 t1 t2 RES P BUF blen a0 a1 a2 a3 a4 a5 a6 a7 s1v s6v s7v s8v t3 t4 t5 t6 :=
  (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 RES) s1v
       a0 a1 a2 a3 a4 a5 a6 a7
       (Z_to_bv 64 blen) (Z_to_bv 64 BUF) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) s6v s7v s8v (Z_to_bv 64 (P + 24))
       (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6) (only parsing).

Lemma pi_walk9 : forall (RES P BUF blen IMPL : Z) (b0 b16 b48 b49 : byte) (p1 p17 p57 p12 p28 p50 : list byte)
    (err tape sbuf dcap maxcap lb lbcap nsi idx nxt cap md oc ia bufv lenv docv : word)
    (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1v s6v s7v s8v t3 t4 t5 t6 : word) F fc (m : mem),
  0x6ca000 <= P -> P + 80 < 2^63 -> 0 < IMPL -> IMPL + 96 < 2^63 -> (IMPL + 96 <= 0x10000 \/ 0x6ca000 <= IMPL) -> (P + 80 <= IMPL \/ IMPL + 96 <= P) ->
  pt_shz [(IMPL, IMPL + 96)] m P IMPL -> vt_dpi m ->
  rw_cells asegs m P (pid_cells b0 p1 (Z_to_bv 64 IMPL) b16 p17 err tape sbuf dcap maxcap z8 p57 lb lbcap) ->
  rw_cells asegs m IMPL (impl16 (Z_to_bv 64 0x164ad0) nsi p12 idx nxt p28 cap md b48 b49 p50 oc ia bufv lenv docv) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = entry_st (Z_to_bv 64 0xb58d0) sp gp tp t0 t1 t2 (Z_to_bv 64 RES) s1v
             (Z_to_bv 64 IMPL) (Z_to_bv 64 BUF) (Z_to_bv 64 blen) (Z_to_bv 64 (P + 24)) (Z_to_bv 64 0xe2cdc) a5 a6 a7
             (Z_to_bv 64 blen) (Z_to_bv 64 BUF) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) s6v s7v s8v (Z_to_bv 64 (P + 24))
             (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6 F fc e_parse m1
      /\ munch [(IMPL, IMPL + 96)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 P (pid_cells b0 p1 (Z_to_bv 64 IMPL) b16 p17 err tape sbuf dcap maxcap z8 p57 lb lbcap)
      /\ rw_cells asegs m1 IMPL (impl16 (Z_to_bv 64 0x164ad0) nsi p12 idx nxt p28 cap md z8 b49 p50 oc ia bufv lenv docv))
    (MS (PIREGT ra sp gp tp t0 t1 t2 RES P BUF blen a0 a1 a2 a3 a4 a5 a6 a7 s1v s6v s7v s8v t3 t4 t5 t6) F (Z_to_bv 64 0xb585c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros P0 PH I0 IH IS SEP SHZ VT PC IC MI.
  unfold entry_st, e_parse, pid_cells, impl16, vt_dpi in *.
  pose proof (munch_refl [(IMPL, IMPL + 96)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUI : bv_unsigned (Z_to_bv 64 IMPL) = IMPL) by (apply unsigned_lit; lia).
  destruct (SHZ m MU WM) as (SHP & SHI & _).
  pose proof (SHP (P + 56) ltac:(lia)) as RD0. pose proof (SHP (P + 8) ltac:(lia)) as RD1. pose proof (SHI (IMPL + 48) ltac:(lia)) as RD2.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  ls.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => destruct (SHZ mm MU' WM') as (_ & SHI' & SHV) end.
  pose proof (SHI' IMPL ltac:(lia)) as RD3. pose proof (SHV 0x164ad0 ltac:(lia)) as RD4.
  change (0x164ad0 / 8 + 2147450880) with 2147633498 in RD4.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep.
  zstep. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; eassumption.
Qed.

Definition res_cells0 (j0 j8 j16 j20 : list byte) : list cell := [CB 8 j0; CB 8 j8; CB 4 j16; CB 4 j20].

Lemma pi_walk10a : forall (usp lo RES P BUF blen : Z) (j0 j8 j16 j20 jf : list byte)
    (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1v s6v s7v s8v t3 t4 t5 t6 rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c : word) F fc (m : mem),
  stk asegs m lo (usp + -112) -> lo <= usp - 112 -> 0x6ca000 <= lo -> usp <= RES -> RES + 24 < 2^63 -> 0x6ca000 <= P -> P + 80 <= lo ->
  (forall m' : mem, munch [(usp - 112, usp); (RES, RES + 24)] m m' -> wmono asegs m m' -> shz m' RES 24) ->
  rw_cells asegs m RES (res_cells0 j0 j8 j16 j20) ->
  rw_cells asegs m (usp + -112) (pid_frame (CB 8 jf) rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem), ret_st rac (Z_to_bv 64 usp) gp tp s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c (Z_to_bv 64 (RES + 16)) m1 ms
      /\ ms_fcsr ms = fc /\ munch [(usp - 112, usp); (RES, RES + 24)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp
      /\ rw_cells asegs m1 RES [C8 (Z_to_bv 64 (P + 24)); C8 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); CB 4 j20])
    (MS (PIREGT (Z_to_bv 64 0xb58d0) (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 RES P BUF blen (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s1v s6v s7v s8v t3 t4 t5 t6)
        F (Z_to_bv 64 0xb58d0) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO GLO RLO RH P0 PLO SHZ RC FR MI.
  unfold res_cells0, pid_frame in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 112, usp); (RES, RES + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (SHZ m MU WM RES ltac:(lia)) as RD0.
  zstep. if_true.
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
    (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1v s6v s7v s8v t3 t4 t5 t6 : word) F fc (m : mem),
  bv_unsigned v <> 0 -> 0 < RES -> RES + 24 < 2^63 ->
  evt asegs (eq (entry_st (Z_to_bv 64 0xb58ec) sp gp tp t0 t1 t2 (Z_to_bv 64 RES) (Z_to_bv 64 (RES + 16))
                   (Z_to_bv 64 RES) (Z_to_bv 64 0) (Z_to_bv 64 16) a3 a4 a5 a6 a7
                   v (Z_to_bv 64 BUF) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) s6v s7v s8v (Z_to_bv 64 (P + 24))
                   (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6 F fc e_asan_memset m))
    (MS (PIREGT (Z_to_bv 64 0xb58d0) sp gp tp t0 t1 t2 RES P BUF blen v a1 a2 a3 a4 a5 a6 a7 s1v s6v s7v s8v t3 t4 t5 t6)
        F (Z_to_bv 64 0xb58d0) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros V0 R0 RH.
  unfold entry_st, e_asan_memset in *.
  zstep. if_cases K; [exfalso; zify_cond K; exact (V0 K)|].
  zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma pi_walk11 : forall (usp lo RES : Z) (z16 j16 j20 jf : list byte)
    (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c : word) F fc (m : mem),
  stk asegs m lo (usp + -112) -> lo <= usp - 112 -> 0x6ca000 <= lo -> usp <= RES -> RES + 24 < 2^63 ->
  shz m RES 24 ->
  rw_cells asegs m RES [CB 16 z16; CB 4 j16; CB 4 j20] ->
  rw_cells asegs m (usp + -112) (pid_frame (CB 8 jf) rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem), ret_st rac (Z_to_bv 64 usp) gp tp s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c (Z_to_bv 64 0) m1 ms
      /\ ms_fcsr ms = fc /\ munch [(usp - 112, usp); (RES, RES + 24)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp
      /\ rw_cells asegs m1 RES [CB 16 z16; C4 s2; CB 4 j20])
    (MS (mkR (Z_to_bv 64 0xb58ec) (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 RES) (Z_to_bv 64 (RES + 16)) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb58ec) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO GLO RLO RH SHZ RC FR MI.
  unfold pid_frame in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 112, usp); (RES, RES + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (SHZ (RES + 16) ltac:(lia)) as RD0.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep.
  do 13 zstep. zstep.
  release_frame FR ST usp.
  zstep.
  apply evt_done. eexists. split; [unfold ret_st; do 16 eexists; cbv delta [mkR]; reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| eassumption].
Qed.

