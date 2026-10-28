(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjNumber SjNumU SjNumN SjNumSwar.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem
  Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_pm_kit Sj_num_fc_defs Sj_num_fc_tail Sj_num_fc_dc.
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

Section FCBDC2.
  Variable E : fcbenv.
  Hypothesis OK : fcb_ok E.
  Hypothesis PV : fcb_prov E.
  Variable Q : machine_state -> Prop.
  Hypothesis KMSET : fcb_kmset E Q.
  Notation OUT := (q_OUT E).
  Notation f := (q_f E).

  Lemma fcb_7dc : forall (s p2 : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xt3 xt4 xt5 xt6 xF xfc mm js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL,
    FCINV E mm true js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL -> frm0 xfc ->
    fcb_spans E IP IL FPT FL -> (-342 <= s <= 327)%Z -> (-963368 <= p2 <= 963368)%Z ->
    evt bsegs Q (FCB E 0xe9be0 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs5 xs6 xs7 (Z_to_bv 64 s) (Z_to_bv 64 p2) (Z_to_bv 64 OUT)
                     xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV KMSET.
    intros until FL. intros INV FRM SPN HS HP2. pose proof INV as INV0. fc_open INV0. fcb_env OK. fcb_prov PV.
    apply (rw_cells_split_CB bsegs _ _ [] 63 js [] (repeat 1%nat 63)) in BSH; [| reflexivity]. cbn [app] in BSH. rewrite app_nil_r in BSH.
    cbn [mk_CB_cells repeat] in BSH.
    repeat match type of BSH with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in BSH; clearbody j end.
    apply (num_cb8_c8 bsegs _ _ []) in DGC. cbn [app] in DGC.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xe9f5c%Z => u_trap pc
      | 0x7f338%Z => first [ pose proof (fcb_merge_all _ _ _ BSH) as BSH'; clear BSH; cbn [cells_size csize Nat.add cells_bytes cbytes app] in BSH';
                             lazymatch type of BSH' with rw_cells _ ?m1 ?a _ => assert (BSZ : rw_cells bsegs m1 a [CB 63 (repeat (Z_to_bv 8 0) 63)]) by exact BSH' end; clear BSH';
                             num_cur_mem ltac:(fun m1 => assert (INV1 : FCINV E m1 true (repeat (Z_to_bv 8 0) 63) c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL) by fc_close);
                             eapply evt_eq; [| eapply KMSET with (sci := s) (p2 := p2)]; [num_st_eq | exact INV1 | exact FRM | exact SPN | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

End FCBDC2.
