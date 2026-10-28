(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Sj_h_arith.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_new Sj_h_dtor Sj_h_alloc Atp_fzwA Atp_setcapA Sj_h_setmd Atp_pdtorA Sj_hkitB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_create : Z := 0xb3470.

Definition cr_frame (ra s0 s1 s2 s3 s4 s5 : word) (j : list byte) : list cell := [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma cr_walk1 : forall (usp lo : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 64 -> 0x6ce000 <= lo -> usp < 2^63 ->
  shb_consts m -> cli_got_nothrow m -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (j : list byte),
      ms = entry_st (Z_to_bv 64 0xb34b8) (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 a2 a3
             (Z_to_bv 64 96) (Z_to_bv 64 0x2d450) a2 a3 a4 a5 a6 a7 a1 s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc e_new_nt m1
      /\ munch [(usp - 64, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -64)
      /\ rw_cells bsegs m1 (usp + -64) (cr_frame ra s0 s1 s2 s3 s4 s5 j))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc e_create m).
Proof.
  intros until m. intros ST LO GLO SPH (G1 & G2) GN MI.
  unfold entry_st, e_create, e_new_nt, cr_frame, cli_got_nothrow in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 64, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 64%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 64 _ [] [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  do 7 zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| exact FR].
Qed.

Definition cr_cells0 (j0 j8 j12 j16 j24 j28 j32 j50 j56 : list byte) : list cell :=
  [CB 8 j0; CB 4 j8; CB 4 j12; CB 8 j16; CB 4 j24; CB 4 j28; CB 18 j32; CB 6 j50; CB 40 j56].
Definition cr_cells1 (c0 : cell) (j12 j28 : list byte) (c32 : cell) (j50 : list byte) (c56 : cell) : list cell :=
  [c0; C4 (Z_to_bv 64 0); CB 4 j12; C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 j28; c32; CB 6 j50; c56].

Definition cr_shz (W : list ivl) (m0 : mem) (p : Z) : Prop :=
  forall m' : mem, munch W m0 m' -> wmono bsegs m0 m' -> shz m' p 96.

Lemma cr_walk2 : forall (p DST : Z) (j0 j8 j12 j16 j24 j28 j32 j50 j56 : list byte)
    (sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < p -> p + 96 < 2^63 -> (p + 96 <= 0x10000 \/ 0x6ce000 <= p) -> p mod 16 = 0 -> 0 <= DST < 2^63 ->
  cr_shz [(p, p + 96)] m p ->
  rw_cells bsegs m p (cr_cells0 j0 j8 j12 j16 j24 j28 j32 j50 j56) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a3' : word),
      ms = entry_st (Z_to_bv 64 0xb3524) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 DST)
             (Z_to_bv 64 (p + 32)) (Z_to_bv 64 0) (Z_to_bv 64 18) a3' a4 a5 a6 a7 s2 (Z_to_bv 64 p) (Z_to_bv 64 2147450880) (Z_to_bv 64 (DST / 8)) s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc e_asan_memset m1
      /\ munch [(p, p + 96)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 p (cr_cells1 (CB 8 j0) j12 j28 (CB 18 j32) j50 (CB 40 j56)))
    (MS (mkR (Z_to_bv 64 0xb34b8) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 DST) (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb34b8) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros P0 PH PS P16 DR SHZ PC MI.
  unfold entry_st, e_asan_memset, cr_cells0, cr_cells1 in *.
  pose proof (munch_refl [(p, p + 96)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EUP : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  zstep. rewrite shr3_div.
  zstep. if_cases K; zify_cond K; [exfalso; lia|].
  zstep. zstep. rewrite (land15_mod16 p P16). zstep. if_false.
  pose proof (SHZ m MU WM (p + 8) ltac:(lia)) as RD0.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  ls.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHZ mm MU' WM' (p + 16) ltac:(lia)) as RD1 end.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  ls.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHZ mm MU' WM' (p + 24) ltac:(lia)) as RD2 end.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  ls.
  zstep. zstep. zstep. zstep.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; eassumption.
Qed.

Lemma cr_walk3 : forall (p : Z) (j0 j12 j28 z32 j50 j56 : list byte)
    (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < p -> p + 96 < 2^63 -> (p + 96 <= 0x10000 \/ 0x6ce000 <= p) ->
  cr_shz [(p, p + 96)] m p ->
  rw_cells bsegs m p (cr_cells1 (CB 8 j0) j12 j28 (CB 18 z32) j50 (CB 40 j56)) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = entry_st (Z_to_bv 64 0xb3550) sp gp tp t0 t1 t2 s0 s1
             (Z_to_bv 64 (p + 56)) (Z_to_bv 64 0) (Z_to_bv 64 40) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 p) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc e_asan_memset m1
      /\ munch [(p, p + 96)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 p (cr_cells1 (C8 (Z_to_bv 64 0x169010)) j12 j28 (CB 18 z32) j50 (CB 40 j56)))
    (MS (mkR (Z_to_bv 64 0xb3524) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 p) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb3524) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros P0 PH PS SHZ PC MI.
  unfold entry_st, e_asan_memset, cr_cells1 in *.
  pose proof (munch_refl [(p, p + 96)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (SHZ m MU WM p ltac:(lia)) as RD0.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. lstep.
  zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; eassumption.
Qed.

Definition cr_shz4 (W : list ivl) (m0 : mem) (DST p : Z) : Prop :=
  forall m' : mem, munch W m0 m' -> wmono bsegs m0 m' -> shz m' DST 8 /\ shz m' p 96 /\ shz m' 0x169000 96.

Lemma cr_walk4 : forall (p DST cap : Z) (nsi idx cap0 : word) (p12 p24 rest : list byte)
    (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < p -> p + 96 < 2^63 -> (p + 96 <= 0x10000 \/ 0x6ce000 <= p) -> 0x6ce000 <= DST -> DST + 8 < 2^63 -> (p + 96 <= DST \/ DST + 8 <= p) -> p mod 16 = 0 ->
  cr_shz4 [(DST, DST + 8)] m DST p -> vt_dpi m ->
  rw_cells bsegs m DST [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m p (impl_cells (Z_to_bv 64 0x169010) nsi p12 idx p24 cap0 rest) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = entry_st (Z_to_bv 64 0xb3610) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 DST)
             (Z_to_bv 64 p) (Z_to_bv 64 cap) (Z_to_bv 64 0xe7338) a3 a4 a5 a6 a7 (Z_to_bv 64 cap) (Z_to_bv 64 p) (Z_to_bv 64 2147450880)
             (Z_to_bv 64 (DST / 8)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_setcap m1
      /\ munch [(DST, DST + 8)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 DST [C8 (Z_to_bv 64 p)]
      /\ rw_cells bsegs m1 p (impl_cells (Z_to_bv 64 0x169010) nsi p12 idx p24 cap0 rest))
    (MS (mkR (Z_to_bv 64 0xb3550) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 DST) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 cap) (Z_to_bv 64 p) (Z_to_bv 64 2147450880) (Z_to_bv 64 (DST / 8)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb3550) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros P0 PH PS D0 DH SEP P16 SHZ VT DC PC MI.
  unfold entry_st, e_setcap, impl_cells, vt_dpi in *.
  pose proof (munch_refl [(DST, DST + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EUP : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  destruct (SHZ m MU WM) as (SHD & _ & _). pose proof (SHD DST ltac:(lia)) as RD0.
  zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. if_false.
  zstep.
  zstep. rewrite (land7_mod16 p P16). zstep. if_false.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => destruct (SHZ mm MU' WM') as (_ & SHI & SHV) end.
  pose proof (SHI p ltac:(lia)) as RD1. pose proof (SHV 0x169040 ltac:(lia)) as RD2.
  change (0x169040 / 8 + 2147450880) with 2147635720 in RD2.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep.
  zstep. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma cr_walk5 : forall (p DST md : Z) (nsi idx cap0 : word) (p12 p24 rest : list byte)
    (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2x s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < p -> p + 96 < 2^63 -> (p + 96 <= 0x10000 \/ 0x6ce000 <= p) -> 0x6ce000 <= DST -> DST + 8 < 2^63 -> p mod 16 = 0 ->
  shz m DST 8 -> shz m p 96 -> shz m 0x169000 96 -> vt_dpi m ->
  rw_cells bsegs m DST [C8 (Z_to_bv 64 p)] ->
  rw_cells bsegs m p (impl_cells (Z_to_bv 64 0x169010) nsi p12 idx p24 cap0 rest) -> mem_inv bsegs m ->
  evt bsegs (fun ms =>
      ms = entry_st (Z_to_bv 64 0xb366c) sp gp tp t0 t1 t2 (Z_to_bv 64 md) (Z_to_bv 64 DST)
             (Z_to_bv 64 p) (Z_to_bv 64 md) (Z_to_bv 64 0xe74ac) a3 a4 a5 a6 a7 s2x (Z_to_bv 64 p) (Z_to_bv 64 2147450880)
             (Z_to_bv 64 (DST / 8 + 2147450880)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_setmd m)
    (MS (mkR (Z_to_bv 64 0xb3610) sp gp tp t0 t1 t2 (Z_to_bv 64 md) (Z_to_bv 64 DST) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
             s2x (Z_to_bv 64 p) (Z_to_bv 64 2147450880) (Z_to_bv 64 (DST / 8)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb3610) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros P0 PH PS D0 DH P16 SHD SHI SHV VT DC PC MI.
  unfold entry_st, e_setmd, impl_cells, vt_dpi in *.
  assert (EUP : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  pose proof (SHD DST ltac:(lia)) as RD0. pose proof (SHI p ltac:(lia)) as RD1. pose proof (SHV 0x169048 ltac:(lia)) as RD2.
  change (0x169048 / 8 + 2147450880) with 2147635721 in RD2.
  zstep. zstep. if_false.
  zstep. if_false.
  zstep. zstep. shz_norm. zstep. if_false.
  zstep.
  zstep. if_cases K; zify_cond K; [exfalso; lia|].
  zstep. rewrite (land7_mod16 p P16). zstep. if_false.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep.
  zstep. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma cr_walk6 : forall (usp lo code : Z) (j : list byte)
    (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rac s0c s1c s2c s3c s4c s5c : word) F fc (m : mem),
  stk bsegs m lo (usp + -64) -> lo <= usp - 64 -> 0x6ce000 <= lo -> usp < 2^63 -> 0 <= code < 64 ->
  rw_cells bsegs m (usp + -64) (cr_frame rac s0c s1c s2c s3c s4c s5c j) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ret_st rac (Z_to_bv 64 usp) gp tp s0c s1c s2c s3c s4c s5c s6 s7 s8 s9 s10 s11 (Z_to_bv 64 code) m1 ms
      /\ ms_fcsr ms = fc /\ munch [] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp)
    (MS (mkR (Z_to_bv 64 0xb366c) (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb366c) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO GLO SPH CD FR MI.
  unfold cr_frame in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. zstep. if_cases K; zify_cond K; [| exfalso; lia].
  do 7 zstep. zstep.
  release_frame FR ST usp.
  zstep.
  apply evt_done. eexists. split; [unfold ret_st; do 16 eexists; cbv delta [mkR]; reflexivity|].
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ST].
Qed.
