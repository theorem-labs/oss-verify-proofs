(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber SjNumSwar SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_num_kitu Sj_num_kitn Sj_num_kitw Sj_num_sp_defs Sj_num_sp_dc Sj_num_sp_pdefs Sj_num_sp_acc Sj_num_sp_exp Sj_num_ff_defs Sj_num_ff_cf Sj_num_ff_pn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac num_abstract_data ::= num_abstract_data_u.
Local Ltac nnorm ::= nnorm_x.

Section FFUTOP.
  Hypothesis HSPATH : ffu_spath_stmt.
  Variable E : ffuenv.
  Hypothesis OK : ffu_ok E.
  Notation A := (f_A E).
  Notation TL := (f_TL E).
  Notation FIRST := (f_FIRST E).
  Notation LAST := (f_LAST E).

  Notation TS pc xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm :=
    (FFS E pc xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) xa2 xa3 xa4 xa5 xa6 xa7
         xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).

  Lemma ffu_22c : forall (IP IL : Z) xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFUINV E mm -> frm0 xfc -> (FIRST < LAST)%Z -> (A <= IP)%Z -> (1 <= IL)%Z -> (IP + IL <= LAST)%Z ->
    evt usegs (ffu_post E) (TS 0x40dbc xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 (Z_to_bv 64 IP) (Z_to_bv 64 IL) (Z_to_bv 64 (IP + IL)) xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros until mm. intros INV FRM HLT H1 H2 H3. pose proof INV as INV0. ffu_open INV0. ffu_env OK.
    assert (D3 : IsData xa3) by exact I.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x41538%Z => u_trap_b pc
      | 0x41008%Z => first [ eapply evt_eq; [| eapply (ffu_478 HSPATH E OK IP IL 0%Z (IP + IL)%Z)]; [num_st_eq | exact INV | assumption | exact HLT | lia | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x40f0c%Z => first [ eapply evt_eq; [| eapply (ffu_37c HSPATH E OK IP IL (IP + IL + 1)%Z (IP + IL + 1)%Z)]; [num_st_eq | exact INV | assumption | unfold ffu_bfacts; lia] | fail 100 "cut" pc ]
      | 0x40e48%Z => first [ eapply evt_eq; [| eapply (ffu_L2 HSPATH E OK (Z.to_nat LAST) IP IL (IP + IL + 1)%Z (IP + IL + 1)%Z)];
                             [num_st_eq | exact INV | assumption | unfold ffu_bfacts; lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ffu_21c : forall (IP IL : Z) xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFUINV E mm -> frm0 xfc -> (FIRST < LAST)%Z -> (A <= IP)%Z -> (1 <= IL)%Z -> (IP + IL <= LAST)%Z ->
    evt usegs (ffu_post E) (TS 0x40dac xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 (Z_to_bv 64 IP) (Z_to_bv 64 IL) (Z_to_bv 64 (IP + IL)) xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros until mm. intros INV FRM HLT H1 H2 H3. pose proof INV as INV0. ffu_open INV0. ffu_env OK.
    assert (D7 : IsData xa7) by exact I.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x41538%Z => u_trap_b pc
      | 0x413f4%Z => first [ eapply evt_eq; [| eapply (ffu_864 E OK)]; [num_st_eq | exact INV | assumption] | fail 100 "cut" pc ]
      | 0x40dbc%Z => first [ eapply evt_eq; [| eapply (ffu_22c IP IL)]; [num_st_eq | exact INV | assumption | exact HLT | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Ltac top_cuts INV HLT IP :=
    fun pc => lazymatch pc with
      | 0x41538%Z => u_trap_b pc
      | 0x413f4%Z => first [ eapply evt_eq; [| eapply (ffu_864 E OK)]; [num_st_eq | exact INV | assumption] | fail 100 "cut" pc ]
      | 0x41400%Z => first [ eapply evt_eq; [| eapply (ffu_870 E OK)]; [num_st_eq | exact INV | assumption] | fail 100 "cut" pc ]
      | 0x40dac%Z => first [ eapply evt_eq; [| eapply (ffu_21c IP _)]; [num_st_eq | exact INV | assumption | exact HLT | lia | lia | lia] | fail 100 "cut" pc ]
      end.

  Lemma ffu_L1 : forall (f : nat) (IP p : Z) xra xs0 xs1 xa2 xa3 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFUINV E mm -> frm0 xfc -> (FIRST < LAST)%Z -> (A <= IP < p)%Z -> (p <= LAST)%Z -> (LAST - p <= Z.of_nat f)%Z ->
    evt usegs (ffu_post E) (TS 0x40d5c xra (Z_to_bv 64 10) (Z_to_bv 64 p) (Z_to_bv 64 9) xs0 xs1 xa2 xa3 (Z_to_bv 64 IP) (Z_to_bv 64 2) (Z_to_bv 64 p) xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM HLT H1 H2 Hf.
    { assert (p = LAST) by lia. subst p. pose proof INV as INV0. ffu_open INV0. ffu_env OK. assert (D3 : IsData xa3) by exact I.
      uwalk ltac:(top_cuts INV HLT IP). }
    pose proof INV as INV0. ffu_open INV0. ffu_env OK. assert (D3 : IsData xa3) by exact I.
    nstep.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x40d5c%Z => first [ eapply evt_eq; [| eapply (IH IP (p + 1)%Z)]; [num_st_eq | exact INV | assumption | exact HLT | lia | lia | lia] | fail 100 "cut" pc ]
      | _ => top_cuts INV HLT IP pc
      end).
  Qed.

  Lemma ffu_0d0 : forall (IP : Z) xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFUINV E mm -> frm0 xfc -> (FIRST <= IP < LAST)%Z ->
    evt usegs (ffu_post E) (TS 0x40c60 xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 (Z_to_bv 64 IP) xa5 xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros until mm. intros INV FRM H1. pose proof INV as INV0. ffu_open INV0. ffu_env OK.
    assert (HLT : (FIRST < LAST)%Z) by lia. assert (D7 : IsData xa7) by exact I.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x40d5c%Z => first [ eapply evt_eq; [| eapply (ffu_L1 (Z.to_nat LAST) IP (IP + 5)%Z)]; [num_st_eq | exact INV | assumption | exact HLT | lia | lia | lia] | fail 100 "cut" pc ]
      | _ => top_cuts INV HLT IP pc
      end).
  Qed.

  Lemma ffu_090 : forall xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFUINV E mm -> frm0 xfc ->
    evt usegs (ffu_post E) (TS 0x40c20 xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros until mm. intros INV FRM. pose proof INV as INV0. ffu_open INV0. ffu_env OK.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x41538%Z => u_trap_b pc
      | 0x413f4%Z => first [ eapply evt_eq; [| eapply (ffu_864 E OK)]; [num_st_eq | exact INV | assumption] | fail 100 "cut" pc ]
      | 0x41400%Z => first [ eapply evt_eq; [| eapply (ffu_870 E OK)]; [num_st_eq | exact INV | assumption] | fail 100 "cut" pc ]
      | 0x40c60%Z => first [ eapply evt_eq; [| eapply (ffu_0d0 _)]; [num_st_eq | exact INV | assumption | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Theorem ffu_body_spec : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc,
    mem_inv usegs (f_m0 E) -> frm0 fc -> stk usegs (f_m0 E) (f_lo E) (f_SP E) -> bytes_at usegs (f_m0 E) A (f_txt E) ->
    evt usegs (ffu_post E)
      (MS (mkR (f_ra E) (f_sp E) (f_gp E) (f_tp E) t0 t1 t2 (f_s0 E) (f_s1 E) (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) a2 a3 a4 a5 a6 a7
               (f_s2 E) (f_s3 E) (f_s4 E) (f_s5 E) (f_s6 E) (f_s7 E) (f_s8 E) (f_s9 E) (f_s10 E) (f_s11 E) t3 t4 t5 t6)
          F (Z_to_bv 64 FFU_ENTRY) fc None (f_m0 E) (seg_rom usegs)).
  Proof using HSPATH OK.
    intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc MI FRM ST TXT.
    unfold FFU_ENTRY.
    pose proof (munch_refl [(f_SP E - FFU_STACK, f_SP E)]%Z (f_m0 E)) as MU. pose proof (wmono_refl usegs (f_m0 E)) as WM.
    pose proof OK as OK0. ffu_env OK0.
    assert (LO0 : (0 <= f_lo E)%Z) by (destruct ST as [? _]; assumption).
    set (m := f_m0 E) in MI, ST, TXT, MU at 2, WM at 2 |- * at 2. clearbody m.
    step.
    carve_frame 112%nat ST.
    apply (rw_cells_split_CB usegs m _ [] 112 junk [] [8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 13 step. nstep.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x40c20%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV : FFUINV E m1) by ffu_close);
                             eapply ffu_090; [exact INV | assumption] | fail 100 "cut" pc ]
      end).
  Qed.
End FFUTOP.

Theorem ffu_spec : ffu_spath_stmt -> ffu_stmt_g usegs FFU_ENTRY NUMU_GTOP.
Proof.
  intros HS. unfold ffu_stmt_g. intros until txt. intros MI FRM ST ROOM GTOP SP16 TXT TLO TMAX A0 HF HL.
  set (E := mkFfuEnv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 A FIRST LAST lo txt m).
  assert (OK : ffu_ok E) by (constructor; cbn; assumption).
  exact (ffu_body_spec HS E OK t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc MI FRM ST TXT).
Qed.
