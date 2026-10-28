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
  Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_pm_kit Sj_num_fc_defs Sj_num_fc_pdefs Sj_num_fc_tail Sj_num_fc_k14 Sj_num_fc_pp1 Sj_num_fc_pp2 Sj_num_fc_pp2b Sj_num_fc_pp2c Sj_num_fc_pp3 Sj_num_fc_pp4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_ptr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_w.

Local Ltac num_abstract_data ::= num_abstract_data_u.

Section FCBPP5.
  Variable E : fcbenv.
  Hypothesis OK : fcb_ok E.
  Hypothesis PV : fcb_prov E.
  Variable Q : machine_state -> Prop.
  Hypothesis K14 : fcb_kf14 E Q.
  Hypothesis KERR1 : fcb_kerr1 E Q.
  Notation A := (q_A E).
  Notation FIRST := (q_FIRST E).
  Notation LAST := (q_LAST E).
  Notation OUT := (q_OUT E).
  Notation f := (q_f E).
  Notation P2 L := (L E OK PV Q K14) (only parsing).
  Notation P4 L := (L E OK PV Q K14 KERR1) (only parsing).

  Ltac kwalk_abs PCS K :=
    kwalk ltac:(fun pc => first [ K pc | (lazymatch PCS with context [pc] => idtac end; num_abstract_loads; num_abstract_data; kstep; kwalk_abs PCS K) ]).

  Ltac fcp_cur :=
    num_cur_mem ltac:(fun m1 => lazymatch goal with
      | SP : rw_cells bsegs m1 (q_spq E) [C8 ?d0; C8 ?d8; C8 ?d16; C8 ?d24; C8 ?d32; C8 ?d40; C8 ?d48; C8 ?d56; C8 _] |- _ =>
          assert (INV1 : FCPINV E m1 d0 d8 d16 d24 d32 d40 d48 d56) by fcp_close end).

  Lemma fcb_L2 : forall (f : nat) (IP IL p : Z) c0 c8 c48 xt0 xt2 xa2 xa3 xa4 xa5 xa7 xs7 xs10 xt4 xt5 xt6 xF xfc mm,
    FCPINV E mm c0 c8 (Z_to_bv 64 53) (Z_to_bv 64 46) (Z_to_bv 64 OUT) (Z_to_bv 64 IL) c48 (Z_to_bv 64 (IP + IL + 1)) -> frm0 xfc -> sp_ffacts E IP IL p -> (FIRST <= IP)%Z -> (p + 8 <= LAST)%Z -> (LAST - p <= 8 * Z.of_nat f)%Z ->
    evt bsegs Q (FCS E 0xe80f8 (Z_to_bv 64 (5063812098665367110)) xt0 (Z_to_bv 64 (9259542123273814144)) xt2 (q_sp E) (Z_to_bv 64 (q_spq E)) (Z_to_bv 64 (p + 7)) (Z_to_bv 64 (14974415777481871312)) xa2 xa3 xa4 xa5 (Z_to_bv 64 (LAST - p)) xa7 (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) (Z_to_bv 64 (IP)) (Z_to_bv 64 LAST) xs7 (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 (p)) xs10 (Z_to_bv 64 (q_f E)) (Z_to_bv 64 (p / 8 + 2147450880)) xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV K14 KERR1.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM FF HIP Hp Hf; [exfalso; lia|].
    pose proof INV as INV0. fcp_open INV0. pose proof OK as OK'. fcb_env OK'. clear FSH TSEP. fcb_prov PV.
    pose proof FF as ((F1 & F2 & F3 & F4) & _).
    kstep.
    kwalk_abs (0xe8198%Z) ltac:(fun pc => lazymatch pc with
      | 0xe9bd8%Z => u_trap_b pc
      | 0xe847c%Z => first [ eapply evt_eq; [| eapply (P4 fcb_3fc IP IL p c0 c8 (Z_to_bv 64 53) (Z_to_bv 64 46) c48)]; [num_st_eq | exact INV | assumption | exact FF | exact HIP | lia]
                           | fail 100 "cut" pc ]
      | 0xe8474%Z => first [ eapply evt_eq; [| eapply (P4 fcb_3f4 IP IL (p + 8)%Z c0 c8 (Z_to_bv 64 53) (Z_to_bv 64 46) c48)]; [num_st_eq | exact INV | assumption | | exact HIP];
                             apply sp_ffacts_app; [exact FF | lia | lia |];
                             lazymatch goal with KB : Z.land _ 9259542123273814144 = 0%Z |- _ => exact (sp_swar8 E p _ KB) end
                           | fail 100 "cut" pc ]
      | 0xe80f8%Z => first [ eapply evt_eq; [| eapply (IH IP IL (p + 8)%Z c0 c8 c48)];
                             [replace ((p + 8) / 8)%Z with (p / 8 + 1)%Z by (Z.div_mod_to_equations; lia); num_st_eq | exact INV | assumption | | exact HIP | lia | lia];
                             apply sp_ffacts_app; [exact FF | lia | lia |];
                             lazymatch goal with KB : Z.land _ 9259542123273814144 = 0%Z |- _ => exact (sp_swar8 E p _ KB) end
                           | fail 100 "cut" pc ]
      end).
  Qed.

End FCBPP5.
