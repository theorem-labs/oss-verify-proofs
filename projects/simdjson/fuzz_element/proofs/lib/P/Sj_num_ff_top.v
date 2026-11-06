(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_num_kit Sj_num_walk Sj_num_ff_defs Sj_num_ff_cf Sj_num_ff_pn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section FFTOP.
  Hypothesis HSPATH : ff_spath_stmt.
  Variable E : ffenv.
  Hypothesis OK : ff_ok E.
  Notation A := (f_A E).
  Notation TL := (f_TL E).
  Notation FIRST := (f_FIRST E).
  Notation LAST := (f_LAST E).

  Lemma ff_334 : forall (p p4 : Z) xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E mm -> frm0 xfc -> (A <= FIRST <= p4)%Z -> (p4 < p <= LAST)%Z ->
    evt psegs (ff_post E) (FFS E 0x3f1e0 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) xa2 xa3 (Z_to_bv 64 p4) (Z_to_bv 64 (p - p4)) (Z_to_bv 64 p) xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros until mm. intros INV FRM Hp4 Hp. pose proof INV as INV0. ff_open INV0. ff_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3f490%Z => first [ eapply evt_eq; [| eapply (ff_5e4 HSPATH E OK p4 (p - p4)%Z)]; [num_st_eq | exact INV | assumption | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x3f3f8%Z => first [ eapply evt_eq; [| eapply (ff_54c HSPATH E OK p p4 (p - p4)%Z)]; [num_st_eq | exact INV | assumption | lia | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x3f31c%Z => first [ eapply evt_eq; [| eapply (ff_470 HSPATH E OK (p + 1)%Z (p + 1)%Z p4 (p - p4)%Z)]; [num_st_eq | exact INV | assumption | lia | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x3f260%Z => first [ eapply evt_eq; [| eapply (ff_L2 HSPATH E OK (Z.to_nat LAST) (p + 1)%Z (p + 1)%Z p4 (p - p4)%Z)];
                             [num_st_eq | exact INV | assumption | lia | lia | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ff_31c : forall (p p4 : Z) xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E mm -> frm0 xfc -> (A <= FIRST <= p4)%Z -> (p4 <= p <= LAST)%Z ->
    evt psegs (ff_post E) (FFS E 0x3f1c8 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) xa2 xa3 (Z_to_bv 64 p4) xa5 (Z_to_bv 64 p) xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros until mm. intros INV FRM Hp4 Hp. pose proof INV as INV0. ff_open INV0. ff_env OK.
    assert (DA7 : IsData xa7) by exact I.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3f77c%Z => first [ eapply (ff_exit E OK); [exact INV | assumption] | fail 100 "cut" pc ]
      | 0x3f1e0%Z => first [ eapply evt_eq; [| eapply (ff_334 p p4)]; [num_st_eq | exact INV | assumption | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ff_L1 : forall (f : nat) (p p4 : Z) xra xt2 xs0 xs1 xa2 xa3 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E mm -> frm0 xfc -> (A <= FIRST <= p4)%Z -> (p4 <= p < LAST)%Z -> (LAST - p <= Z.of_nat f)%Z ->
    evt psegs (ff_post E) (FFS E 0x3f190 xra (Z_to_bv 64 LAST) (Z_to_bv 64 9) xt2 xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) xa2 xa3 (Z_to_bv 64 p4) (Z_to_bv 64 10) (Z_to_bv 64 p) xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM Hp4 Hp Hf; [exfalso; lia|].
    pose proof INV as INV0. ff_open INV0. ff_env OK.
    assert (DA3 : IsData xa3) by exact I.
    nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3f1c8%Z => first [ eapply evt_eq; [| eapply (ff_31c _ p4)]; [num_st_eq | exact INV | assumption | lia | lia] | fail 100 "cut" pc ]
      | 0x3f190%Z => first [ eapply evt_eq; [| eapply (IH (p + 1)%Z p4)]; [num_st_eq | exact INV | assumption | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ff_1e0 : forall xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E mm -> frm0 xfc ->
    evt psegs (ff_post E) (FFS E 0x3f08c xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) xa2 xa3 xa4 xa5 xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSPATH OK.
    intros until mm. intros INV FRM. pose proof INV as INV0. ff_open INV0. ff_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3f77c%Z => first [ eapply (ff_exit E OK); [exact INV | assumption] | fail 100 "cut" pc ]
      | 0x3f1c8%Z => first [ eapply evt_eq; [| eapply (ff_31c _ _)]; [num_st_eq | exact INV | assumption | lia | lia] | fail 100 "cut" pc ]
      | 0x3f190%Z => first [ eapply evt_eq; [| eapply (ff_L1 (Z.to_nat LAST) _ _)]; [num_st_eq | exact INV | assumption | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Theorem ff_body_spec : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc,
    mem_inv psegs (f_m0 E) -> frm0 fc -> stk psegs (f_m0 E) (f_lo E) (f_SP E) -> bytes_at psegs (f_m0 E) A (f_txt E) ->
    evt psegs (ff_post E)
      (MS (mkR (f_ra E) (f_sp E) (f_gp E) (f_tp E) t0 t1 t2 (f_s0 E) (f_s1 E) (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) a2 a3 a4 a5 a6 a7
               (f_s2 E) (f_s3 E) (f_s4 E) (f_s5 E) (f_s6 E) (f_s7 E) (f_s8 E) (f_s9 E) (f_s10 E) (f_s11 E) t3 t4 t5 t6)
          F (Z_to_bv 64 FF_ENTRY) fc None (f_m0 E) (seg_rom psegs)).
  Proof using HSPATH OK.
    intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc MI FRM ST TXT.
    unfold FF_ENTRY.
    pose proof (munch_refl [(f_SP E - FF_STACK, f_SP E)]%Z (f_m0 E)) as MU. pose proof (wmono_refl psegs (f_m0 E)) as WM.
    pose proof OK as OK0. ff_env OK0.
    assert (LO0 : (0 <= f_lo E)%Z) by (destruct ST as [? _]; assumption).
    set (m := f_m0 E) in MI, ST, TXT, MU at 2, WM at 2 |- * at 2. clearbody m.
    step.
    carve_frame 96%nat ST.
    apply (rw_cells_split_CB psegs m _ [] 96 junk [] [8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 10 step. nstep. zstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3f08c%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV : FFINV E m1) by ff_close);
                             eapply ff_1e0; [exact INV | assumption] | fail 100 "cut" pc ]
      end).
  Qed.
End FFTOP.

Theorem ff_spec : ff_spath_stmt -> ff_stmt_g psegs FF_ENTRY FF_GTOP.
Proof.
  intros HS. unfold ff_stmt_g. intros until txt. intros MI FRM ST ROOM GTOP TXT TLO TMAX HF HL.
  set (E := mkFfEnv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 A FIRST LAST lo txt m).
  assert (OK : ff_ok E) by (constructor; cbn; assumption).
  exact (ff_body_spec HS E OK t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc MI FRM ST TXT).
Qed.
