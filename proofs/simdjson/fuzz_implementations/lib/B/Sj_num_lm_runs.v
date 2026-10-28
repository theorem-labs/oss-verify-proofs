(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem Sj_num_lm_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section RUNS.
  Variables (f : Z) (m0 : mem).
  Notation S := (f / 8 + 2147450880)%Z.
  Hypothesis FS0 : (0 <= S /\ S + 255 < 2^63)%Z.
  Variable Q : machine_state -> Prop.

  Lemma lm_runP2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6  F fc j (mm : mem),
    rw_cells bsegs mm (f / 8 + 2147450884)%Z [CB 63 j] ->
    mem_inv bsegs mm -> munch [(f / 8 + 2147450884, f / 8 + 2147450947)%Z] m0 mm -> wmono bsegs m0 mm ->
    (forall j' (mm' : mem), rw_cells bsegs mm' (f / 8 + 2147450884)%Z [CB 63 j'] ->
       mem_inv bsegs mm' -> munch [(f / 8 + 2147450884, f / 8 + 2147450947)%Z] m0 mm' -> wmono bsegs m0 mm' ->
       evt bsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 S) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0xfbfec) fc None mm' (seg_rom bsegs))) ->
    evt bsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 S) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0xfbefc) fc None mm (seg_rom bsegs)).
  Proof using FS0.
    intros until mm. intros SH MI MU WM HK.
    apply (rw_cells_split_CB bsegs _ _ [] 63 j [] (repeat 1%nat 63)) in SH; [| reflexivity]. cbn [app] in SH. rewrite app_nil_r in SH.
    cbn [mk_CB_cells repeat] in SH.
    repeat match goal with H : rw_cells _ _ _ ?l |- _ => match l with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in H; clearbody j end end.
    awalk ltac:(fun pc => lazymatch pc with 0xfbfec%Z => idtac end).
    destruct (rw_cells_forget bsegs _ _ _ SH) as [j' SH']. cbn [cells_size csize Nat.add] in SH'.
    eapply HK; [exact SH' | exact MI | exact MU | exact WM].
  Qed.

  Lemma lm_run1 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6  F fc j (mm : mem),
    rw_cells bsegs mm (f / 8 + 2147450884)%Z [CB 63 j] ->
    mem_inv bsegs mm -> munch [(f / 8 + 2147450884, f / 8 + 2147450947)%Z] m0 mm -> wmono bsegs m0 mm ->
    (forall (mm' : mem), rw_cells bsegs mm' (f / 8 + 2147450884)%Z [CB 63 (repeat (Z_to_bv 8 0) 63)] ->
       mem_inv bsegs mm' -> munch [(f / 8 + 2147450884, f / 8 + 2147450947)%Z] m0 mm' -> wmono bsegs m0 mm' ->
       evt bsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 S) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0xfc228) fc None mm' (seg_rom bsegs))) ->
    evt bsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 S) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0xfc12c) fc None mm (seg_rom bsegs)).
  Proof using FS0.
    intros until mm. intros SH MI MU WM HK.
    apply (rw_cells_split_CB bsegs _ _ [] 63 j [] (repeat 1%nat 63)) in SH; [| reflexivity]. cbn [app] in SH. rewrite app_nil_r in SH.
    cbn [mk_CB_cells repeat] in SH.
    repeat match goal with H : rw_cells _ _ _ ?l |- _ => match l with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in H; clearbody j end end.
    awalk ltac:(fun pc => lazymatch pc with 0xfc228%Z => idtac end).
    pose proof (rw_cells_merge_all _ _ _ SH) as SH'.
    eapply HK; [exact SH' | exact MI | exact MU | exact WM].
  Qed.

  Lemma lm_run5 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6  F fc j (mm : mem),
    rw_cells bsegs mm (f / 8 + 2147450884)%Z [CB 63 j] ->
    mem_inv bsegs mm -> munch [(f / 8 + 2147450884, f / 8 + 2147450947)%Z] m0 mm -> wmono bsegs m0 mm ->
    (forall j' (mm' : mem), rw_cells bsegs mm' (f / 8 + 2147450884)%Z [CB 63 j'] ->
       mem_inv bsegs mm' -> munch [(f / 8 + 2147450884, f / 8 + 2147450947)%Z] m0 mm' -> wmono bsegs m0 mm' ->
       evt bsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 S) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0xfcbd0) fc None mm' (seg_rom bsegs))) ->
    evt bsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 S) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0xfcad4) fc None mm (seg_rom bsegs)).
  Proof using FS0.
    intros until mm. intros SH MI MU WM HK.
    apply (rw_cells_split_CB bsegs _ _ [] 63 j [] (repeat 1%nat 63)) in SH; [| reflexivity]. cbn [app] in SH. rewrite app_nil_r in SH.
    cbn [mk_CB_cells repeat] in SH.
    repeat match goal with H : rw_cells _ _ _ ?l |- _ => match l with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in H; clearbody j end end.
    awalk ltac:(fun pc => lazymatch pc with 0xfcbd0%Z => idtac end).
    destruct (rw_cells_forget bsegs _ _ _ SH) as [j' SH']. cbn [cells_size csize Nat.add] in SH'.
    eapply HK; [exact SH' | exact MI | exact MU | exact WM].
  Qed.
End RUNS.
