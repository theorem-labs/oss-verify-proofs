(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjNumber SjNumU SjNumN SjNumSwar.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem
  Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_pm_kit Sj_num_fc_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_ptr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.

Section FCBPRO2.
  Variable E : fcbenv.
  Hypothesis OK : fcb_ok E.
  Variable Q : machine_state -> Prop.
  Notation f := (q_f E).
  Notation spq := (q_spq E).
  Notation W2 := [(spq + 64, spq + 72); (f, f + 32); (q_S E, q_S E + 76)]%Z.

  Lemma fcb_poison : forall ra gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc h j64 j0 jz j1 (mm : mem),
    (forall a0' a1' a2' a3' h' j0' jz' j1' (mm' : mem), rw_cells bsegs mm' f [CB 32 h'] -> rw_cells bsegs mm' (spq + 64) [C8 (Z_to_bv 64 f)] ->
       rw_cells bsegs mm' (q_S E) [CB 4 j0'] -> rw_cells bsegs mm' (f / 8 + 2147450884) [CB 63 jz'] -> rw_cells bsegs mm' (f / 8 + 2147450947) [CB 9 j1'] ->
       mem_inv bsegs mm' -> munch W2 (q_m0 E) mm' -> wmono bsegs (q_m0 E) mm' ->
       evt bsegs Q
         (MS (mkR ra (Z_to_bv 64 spq) gp tp t0 t1 s2 s0 (Z_to_bv 64 spq) a0' a1' a2' a3' a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) s5 s6 s7 s8 s9 s10
                  (Z_to_bv 64 f) t3 t4 t5 t6)
             F (Z_to_bv 64 0xe7988) fc None mm' (seg_rom bsegs))) ->
    rw_cells bsegs mm f (mk_CB_cells [8;8;8;8]%nat h) -> rw_cells bsegs mm (spq + 64) [CB 8 j64] ->
    rw_cells bsegs mm (q_S E) [CB 4 j0] -> rw_cells bsegs mm (f / 8 + 2147450884) [CB 63 jz] -> rw_cells bsegs mm (f / 8 + 2147450947) [CB 9 j1] ->
    mem_inv bsegs mm -> munch W2 (q_m0 E) mm -> wmono bsegs (q_m0 E) mm ->
    evt bsegs Q
      (MS (mkR ra (Z_to_bv 64 spq) gp tp t0 t1 t2 s0 (Z_to_bv 64 spq) (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xe77e0) fc None mm (seg_rom bsegs)).
  Proof using OK.
    intros until mm. intros KC HDR S64 SH0 SHZ SH1 MI MU WM. pose proof OK as OK'. fcb_env OK'. destruct SPQ as [SPQ1 SPQ2].
    assert (F8 : (f mod 8 = 0)%Z) by (Z.div_mod_to_equations; lia).
    apply (rw_cells_split_CB bsegs _ _ [] 4 j0 [] (repeat 1%nat 4)) in SH0; [| reflexivity]. cbn [app] in SH0. rewrite app_nil_r in SH0.
    apply (rw_cells_split_CB bsegs _ _ [] 63 jz [] (repeat 1%nat 63)) in SHZ; [| reflexivity]. cbn [app] in SHZ. rewrite app_nil_r in SHZ.
    apply (rw_cells_split_CB bsegs _ _ [] 9 j1 [] (repeat 1%nat 9)) in SH1; [| reflexivity]. cbn [app] in SH1. rewrite app_nil_r in SH1.
    cbn [mk_CB_cells repeat] in HDR, SH0, SHZ, SH1.
    repeat match goal with H : rw_cells _ _ _ ?l |- _ => match l with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in H; clearbody j end end.
    apply (num_cb8_c8 bsegs _ _ []) in S64. cbn [app] in S64.
    bwalk ltac:(fun pc => lazymatch pc with 0xe9bd8%Z => u_trap pc | 0xe7988%Z => idtac end).
    destruct (rw_cells_forget bsegs _ _ _ HDR) as [h' HDR']. cbn [cells_size csize Nat.add] in HDR'.
    destruct (rw_cells_forget bsegs _ _ _ SH0) as [j0' SH0']. cbn [cells_size csize Nat.add] in SH0'.
    destruct (rw_cells_forget bsegs _ _ _ SHZ) as [jz' SHZ']. cbn [cells_size csize Nat.add] in SHZ'.
    destruct (rw_cells_forget bsegs _ _ _ SH1) as [j1' SH1']. cbn [cells_size csize Nat.add] in SH1'.
    eapply evt_eq; [| eapply KC; [exact HDR' | eassumption | exact SH0' | exact SHZ' | exact SH1' | eassumption | eassumption | eassumption]].
    num_st_eq.
  Qed.
End FCBPRO2.
