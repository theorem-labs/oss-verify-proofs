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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_new Sj_h_dtor Sj_h_alloc. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Atp_activewA Atp_createwA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition pid_cells (b0 : byte) (p1 : list byte) (impl : word) (b16 : byte) (p17 : list byte) (err tape sbuf dcap maxcap : word) (nas : byte)
    (p57 : list byte) (lb lbcap : word) : list cell :=
  [C1 b0; CB 7 p1; C8 impl; C1 b16; CB 3 p17; C4 err; C8 tape; C8 sbuf; C8 dcap; C8 maxcap; C1 nas; CB 7 p57; C8 lb; C8 lbcap].

Definition pid_frame (c0 : cell) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [c0; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition vt_impl (m : mem) : Prop :=
  ro_cells asegs m 0x164a00
    [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x164a60); C8 (Z_to_bv 64 0xe2d30); C8 (Z_to_bv 64 0xe2ebc); C8 (Z_to_bv 64 0xe3048); C8 (Z_to_bv 64 0xba0c8);
     C8 (Z_to_bv 64 0xbc6b8); C8 (Z_to_bv 64 0xbc848)].

Lemma pi_walk1a : forall (usp lo RES P d len : Z) (ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 112 -> 0x6ca000 <= lo -> usp < 2^63 -> 0 <= len < 2^63 ->
  shb_consts m -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (j : list byte) (a0' : word),
      ms = MS (mkR ra (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 RES) s1
                   a0' (Z_to_bv 64 P) (Z_to_bv 64 (P + 24)) (Z_to_bv 64 d) (Z_to_bv 64 len) (Z_to_bv 64 0) a6 a7
                   (Z_to_bv 64 len) (Z_to_bv 64 d) s4 (Z_to_bv 64 P) (Z_to_bv 64 0) s7 (Z_to_bv 64 (Z.max len 32)) (Z_to_bv 64 (P + 24))
                   (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb56b4) fc None m1 (seg_rom asegs)
      /\ munch [(usp - 112, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -112)
      /\ rw_cells asegs m1 (usp + -112) (pid_frame (CB 8 j) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 RES) (Z_to_bv 64 P) (Z_to_bv 64 (P + 24)) (Z_to_bv 64 d) (Z_to_bv 64 len) (Z_to_bv 64 0) a6 a7
       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pid m).
Proof.
  intros until m. intros ST LO GLO SPH LEN (G1 & G2) MI.
  unfold entry_st, e_pid, pid_frame in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 112, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EUL : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 112%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 112 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  do 13 zstep.
  do 6 zstep.
  zstep. zstep. zstep. zstep. zstep. zstep.
  if_cases K; zify_cond K.
  - apply evt_done. do 3 eexists. split; [cbv delta [mkR]; rewrite (Z.max_l len 32) by lia; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| exact FR].
  - zstep.
    apply evt_done. do 3 eexists. split; [cbv delta [mkR]; rewrite (Z.max_r len 32) by lia; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| exact FR].
Qed.

Lemma pi_walk1b : forall (RES P d len cap : Z) (b0 b16 nas : byte) (p1 p17 p57 : list byte) (err tape sbuf lb lbcap : word)
    (ra sp gp tp t0 t1 t2 s1 a0 a6 a7 s4 s7 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0x6ca000 <= P -> P + 80 < 2^63 -> 32 <= cap <= 2^26 ->
  shz m P 80 ->
  rw_cells asegs m P (pid_cells b0 p1 (Z_to_bv 64 0) b16 p17 err tape sbuf (Z_to_bv 64 0) (Z_to_bv 64 4294967295) nas p57 lb lbcap) ->
  evt asegs (eq (entry_st (Z_to_bv 64 0xb57cc) sp gp tp t0 t1 t2 (Z_to_bv 64 RES) s1
                   (Z_to_bv 64 (P + 24)) (Z_to_bv 64 cap) (Z_to_bv 64 (P + 24)) (Z_to_bv 64 d) (Z_to_bv 64 len) (Z_to_bv 64 0) a6 a7
                   (Z_to_bv 64 len) (Z_to_bv 64 d) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 0) s7 (Z_to_bv 64 cap) (Z_to_bv 64 (P + 24))
                   (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6 F fc e_allocate m))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 RES) s1
             a0 (Z_to_bv 64 P) (Z_to_bv 64 (P + 24)) (Z_to_bv 64 d) (Z_to_bv 64 len) (Z_to_bv 64 0) a6 a7
             (Z_to_bv 64 len) (Z_to_bv 64 d) s4 (Z_to_bv 64 P) (Z_to_bv 64 0) s7 (Z_to_bv 64 cap) (Z_to_bv 64 (P + 24))
             (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb56b4) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros P0 PH CAP SHZ PC.
  unfold entry_st, e_allocate, pid_cells in *.
  pose proof (SHZ (P + 8) ltac:(lia)) as RD0. pose proof (SHZ (P + 48) ltac:(lia)) as RD1. pose proof (SHZ (P + 24 + 16) ltac:(lia)) as RD2.
  zstep.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. if_true.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. if_cases K1; zify_cond K1; [| exfalso; lia].
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
  zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma pi_walk2 : forall (RES P d len cap : Z) (b0 b16 nas : byte) (p1 p17 p57 : list byte) (err tape sbuf dcap maxcap lb lbcap : word)
    (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word) F fc (m : mem),
  0x6ca000 <= P -> P + 80 < 2^63 ->
  shz m P 80 ->
  rw_cells asegs m P (pid_cells b0 p1 (Z_to_bv 64 0) b16 p17 err tape sbuf dcap maxcap nas p57 lb lbcap) ->
  evt asegs (eq (entry_st (Z_to_bv 64 0xb5a04) sp gp tp t0 t1 t2 (Z_to_bv 64 RES) s1
                   (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 len) (Z_to_bv 64 d) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 cap) (Z_to_bv 64 (P + 24))
                   (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6 F fc e_getact m))
    (MS (mkR (Z_to_bv 64 0xb57cc) sp gp tp t0 t1 t2 (Z_to_bv 64 RES) s1
             (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 len) (Z_to_bv 64 d) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 0) s7 (Z_to_bv 64 cap) (Z_to_bv 64 (P + 24))
             (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6) F (Z_to_bv 64 0xb57cc) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros P0 PH SHZ PC.
  unfold entry_st, e_getact, pid_cells in *.
  pose proof (SHZ (P + 8) ltac:(lia)) as RD0.
  zstep. zstep.
  zstep. shz_norm. zstep. if_false.
  zstep. zstep. if_true.
  zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma pi_walk3 : forall (RES P d len cap : Z)
    (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  0x6ca000 <= P -> P + 80 < 2^63 -> 0 <= cap < 2^63 ->
  shz m 0x6a6340 8 -> shz m 0x6a63e0 8 -> shz m 0x164a00 64 -> lib1 m -> vt_impl m ->
  evt asegs (eq (entry_st (Z_to_bv 64 0xb5a5c) sp gp tp t0 t1 t2 (Z_to_bv 64 RES) s1
                   (Z_to_bv 64 0x6a63e0) (Z_to_bv 64 cap) (Z_to_bv 64 1024) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 0xba0c8) a5 a6 a7
                   (Z_to_bv 64 len) (Z_to_bv 64 d) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 cap) (Z_to_bv 64 (P + 24))
                   (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6 F fc e_create m))
    (MS (mkR (Z_to_bv 64 0xb5a04) sp gp tp t0 t1 t2 (Z_to_bv 64 RES) s1
             (Z_to_bv 64 0x6a6340) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 len) (Z_to_bv 64 d) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 cap) (Z_to_bv 64 (P + 24))
             (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6) F (Z_to_bv 64 0xb5a04) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros P0 PH CAP SHA SHS SHV (L1 & L2 & L3 & L4) VT.
  unfold entry_st, e_create, vt_impl in *.
  pose proof (SHA 0x6a6340 ltac:(lia)) as RD0. pose proof (SHS 0x6a63e0 ltac:(lia)) as RD1. pose proof (SHV 0x164a28 ltac:(lia)) as RD2.
  change (0x6a6340 / 8 + 2147450880) with 2148322408 in RD0.
  change (0x6a63e0 / 8 + 2147450880) with 2148322428 in RD1.
  change (0x164a28 / 8 + 2147450880) with 2147633477 in RD2.
  zstep. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep.
  zstep. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep.
  zstep. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

