(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout R_small R_thread I_qck X_atexit I_pck.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition zb8 (l : list Z) : list byte := map (Z_to_bv 8) l.

Lemma zb8_nonul : forall l, forallb (fun c => (0 <? c) && (c <? 256)) l = true -> ~ In z8 (zb8 l).
Proof.
  intros l H IN. unfold zb8 in IN. apply in_map_iff in IN. destruct IN as (c & E & Hc).
  rewrite forallb_forall in H. specialize (H c Hc). apply andb_prop in H. destruct H as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
  assert (E' : bv_unsigned (Z_to_bv 8 c) = bv_unsigned z8) by (rewrite E; reflexivity).
  rewrite Z_to_bv_unsigned in E'. unfold bv_wrap, bv_modulus in E'. change (2 ^ Z.of_N 8) with 256 in E'.
  rewrite Z.mod_small in E' by lia. change (bv_unsigned z8) with 0 in E'. lia.
Qed.

Lemma cstr_image : forall m a l, mem_inv bsegs m -> 0 <= a -> a + Z.of_nat (length l) + 1 <= 2^64 ->
  forallb (fun c => (0 <? c) && (c <? 256)) l = true ->
  ro_bytes_b bsegs a (zb8 l ++ [z8]) = true -> cstr_at m a (zb8 l).
Proof.
  intros m a l MI H0 H1 HF HB. split; [| exact (zb8_nonul l HF)].
  apply ro_bytes_at; [exact MI | lia | rewrite length_app; unfold zb8; rewrite length_map; cbn [length]; lia|].
  apply ro_bytes_b_sound. exact HB.
Qed.

Lemma cells_byte : forall m A cs j b a, rw_cells bsegs m A cs -> nth_error (cells_bytes cs) j = Some b -> a = A + Z.of_nat j ->
  bytes_at bsegs m a [b].
Proof. intros m A cs j b a [[_ H] _] E ->. exact (bytes_at_nth1 bsegs m A _ j b H E). Qed.

Ltac cstr_tac := intros m MI; apply cstr_image; [exact MI | lia | cbn; lia | vm_compute; reflexivity | vm_compute; reflexivity].

Definition F_EMIT : list Z := [37; 100; 10].
Definition F_USAGE : list Z := [117; 115; 97; 103; 101; 58; 32; 37; 115; 32; 73; 78; 80; 85; 84; 10].
Definition F_COPEN : list Z := [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 37; 115; 10].

Definition F_RERR : list Z := [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32; 37; 115; 10].

Definition F_TOOBIG : list Z := [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32; 37; 117; 32; 98; 121; 116; 101;
                                 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10].

Lemma cstr_f_emit : forall m, mem_inv bsegs m -> cstr_at m 0x14f66 (zb8 F_EMIT). Proof. cstr_tac. Qed.
Lemma cstr_f_usage : forall m, mem_inv bsegs m -> cstr_at m 0x162fa (zb8 F_USAGE). Proof. cstr_tac. Qed.
Lemma cstr_f_copen : forall m, mem_inv bsegs m -> cstr_at m 0x1f488 (zb8 F_COPEN). Proof. cstr_tac. Qed.
Lemma cstr_f_rerr : forall m, mem_inv bsegs m -> cstr_at m 0x1f49d (zb8 F_RERR). Proof. cstr_tac. Qed.
Lemma cstr_f_toobig : forall m, mem_inv bsegs m -> cstr_at m 0x1ad48 (zb8 F_TOOBIG). Proof. cstr_tac. Qed.

Definition S_FLAGS : list Z := [39; 45; 43; 32; 35; 48].
Definition S_QUAL : list Z := [106; 122; 116; 76; 113].
Definition S_CCSS : list Z := [99; 67; 115; 83].
Definition S_CS : list Z := [67; 83].
Definition S_CSB : list Z := [99; 115; 91].
Definition S_SS : list Z := [115; 83].
Definition S_FLT : list Z := [97; 65; 101; 69; 102; 70; 103; 71].
Definition S_DIOUX : list Z := [100; 105; 111; 117; 120; 88; 110].

Lemma cstr_s_flags : forall m, mem_inv bsegs m -> cstr_at m 0x15d47 (zb8 S_FLAGS). Proof. cstr_tac. Qed.
Lemma cstr_s_qual : forall m, mem_inv bsegs m -> cstr_at m 0x1cc51 (zb8 S_QUAL). Proof. cstr_tac. Qed.
Lemma cstr_s_ccss : forall m, mem_inv bsegs m -> cstr_at m 0x14838 (zb8 S_CCSS). Proof. cstr_tac. Qed.
Lemma cstr_s_cs : forall m, mem_inv bsegs m -> cstr_at m 0x1b148 (zb8 S_CS). Proof. cstr_tac. Qed.
Lemma cstr_s_csb : forall m, mem_inv bsegs m -> cstr_at m 0x1087e (zb8 S_CSB). Proof. cstr_tac. Qed.
Lemma cstr_s_ss : forall m, mem_inv bsegs m -> cstr_at m 0x140a6 (zb8 S_SS). Proof. cstr_tac. Qed.
Lemma cstr_s_flt : forall m, mem_inv bsegs m -> cstr_at m 0x16f3d (zb8 S_FLT). Proof. cstr_tac. Qed.
Lemma cstr_s_dioux : forall m, mem_inv bsegs m -> cstr_at m 0x1dfc2 (zb8 S_DIOUX). Proof. cstr_tac. Qed.

Lemma fgvs_int_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (c qa lo : Z),
  a0 = Z_to_bv 64 c -> a1 = Z_to_bv 64 qa -> a2 = Z_to_bv 64 1 -> (c = 100 \/ c = 117) ->
  bytes_at bsegs m qa [z8] -> bv_unsigned sp <= qa < 2^64 ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp < 2^63 -> mem_inv bsegs m ->
  evt bsegs (frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 4 [(bv_unsigned sp - 32, bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x74e58) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros -> -> -> CC QAb QA0 ST LO SPH MI.
  pose proof (ro_C1_of_bytes m qa z8 QAb) as QA. clear QAb.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(usp - 32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EUq : bv_unsigned (Z_to_bv 64 qa) = qa) by (apply unsigned_lit; lia).
  carve_frame 32%nat ST.
  do 12 lstep.
  destruct CC as [-> | ->].
  all: call internal_strchr_spec; [reflexivity| reflexivity| lia| apply cstr_s_dioux; assumption| assumption|].
  all: match goal with |- context [strchr_res ?a ?c ?l] => let v := eval vm_compute in (strchr_res a c l) in change (strchr_res a c l) with v end.
  all: lstep; if_false.
  all: lstep; lstep; lstep; lstep; if_true.
  all: lstep; if_true.
  all: do 6 lstep.
  all: release_frame FR ST usp.
  all: lstep.
  all: apply evt_done; unfold frame_post; do 15 eexists; split; [rewrite ESP; reflexivity|].
  all: rewrite EU; split; [assumption|]; split; [assumption|]; split; [assumption| exact ST].
Qed.
