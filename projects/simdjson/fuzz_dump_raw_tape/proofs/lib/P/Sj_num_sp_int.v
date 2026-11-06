(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjNumber SjNumSwar.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Sj_num_kit Sj_num_walk Sj_num_sp_defs Sj_num_sp_cl Sj_num_sp_dc Sj_num_sp_cf1 Sj_num_sp_pdefs Sj_num_sp_acc Sj_num_sp_exp Sj_num_sp_frac Sj_num_sp_frac2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section SPINT.
  Hypothesis HSET : sp_memset_stmt.
  Hypothesis HPM : sp_pm_stmt.
  Hypothesis HPDC : sp_pdc_stmt.
  Hypothesis HNDC : sp_ndc_stmt.
  Variable E : spenv.
  Hypothesis OK : sp_ok E.
  Notation A := (q_A E).
  Notation LAST := (q_LAST E).
  Notation OUT := (q_OUT E).

  Notation IS pc IP xra xt0 xt1 xt2 xs0 xs1 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm :=
    (SPS E pc xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 IP) (Z_to_bv 64 LAST) (Z_to_bv 64 OUT) (Z_to_bv 64 53)
         (Z_to_bv 64 SPATH_A4) xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).

  Lemma sp_930 : forall (IP IL : Z) xra xt1 xt2 xs0 xs1 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc -> (A <= IP)%Z -> (1 <= IL)%Z -> (IP + IL <= LAST)%Z -> sp_ge48 E IP (IP + IL) ->
    evt psegs (sp_post E) (IS 0x4d824 IP xra (Z_to_bv 64 (IP + IL)) xt1 xt2 xs0 xs1 (Z_to_bv 64 IL) xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros until mm. intros INV FRM H1 H2 H3 G1.
    pose proof INV as INV0. sp_open INV0. sp_env OK.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x4dec0%Z => first [ eapply (sp_fcc E OK); [exact INV | assumption] | fail 100 "cut" pc ]
      | 0x4d83c%Z => first [ eapply evt_eq; [| eapply (sp_948 HSET HPM HPDC HNDC E OK IP IL)]; [num_st_eq | exact INV | assumption | lia | lia | lia | exact G1]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Ltac int_cuts INV IP :=
    fun pc => lazymatch pc with
      | 0x4dec0%Z => first [ eapply (sp_fcc E OK); [exact INV | assumption] | fail 100 "cut" pc ]
      | 0x4d824%Z => first [ eapply evt_eq; [| eapply (sp_930 IP _)]; [num_st_eq | exact INV | assumption | lia | lia | lia |];
                             first [ assumption
                                   | lazymatch goal with G : sp_ge48 E IP ?pe |- sp_ge48 E IP ?pe' => replace pe' with pe by lia; exact G end ]
                           | fail 100 "cut" pc ]
      end.

  Lemma sp_928 : forall (IP pe : Z) xra xt1 xt2 xs0 xs1 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc -> (A <= IP <= pe)%Z -> (pe <= LAST)%Z -> sp_ge48 E IP pe ->
    evt psegs (sp_post E) (IS 0x4d81c IP xra (Z_to_bv 64 pe) xt1 xt2 xs0 xs1 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros until mm. intros INV FRM H1 H2 G1.
    pose proof INV as INV0. sp_open INV0. sp_env OK.
    kwalk ltac:(int_cuts INV IP).
  Qed.

  Lemma sp_L1 : forall (f : nat) (IP pe : Z) xra xt1 xs0 xs1 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc -> (A <= IP <= pe)%Z -> (pe < LAST)%Z -> sp_ge48 E IP pe -> (LAST - pe <= Z.of_nat f)%Z ->
    evt psegs (sp_post E) (IS 0x4d654 IP xra (Z_to_bv 64 pe) xt1 (Z_to_bv 64 9) xs0 xs1 (Z_to_bv 64 10) xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM H1 H2 G1 Hf; [exfalso; lia|].
    pose proof INV as INV0. sp_open INV0. sp_env OK.
    pose proof (sp_tb_range E pe) as Rp. unfold sp_tb in Rp.
    kstep.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x4dec0%Z => first [ eapply (sp_fcc E OK); [exact INV | assumption] | fail 100 "cut" pc ]
      | 0x4d81c%Z => first [ eapply evt_eq; [| eapply (sp_928 IP pe)]; [num_st_eq | exact INV | assumption | lia | lia | exact G1] | fail 100 "cut" pc ]
      | 0x4d824%Z => first [ eapply evt_eq; [| eapply (sp_930 IP (pe + 1 - IP)%Z)]; [num_st_eq | exact INV | assumption | lia | lia | lia |];
                             replace (IP + (pe + 1 - IP))%Z with (pe + 1)%Z by lia; apply sp_ge48_snoc; [exact G1 | unfold sp_tb; lia]
                           | fail 100 "cut" pc ]
      | 0x4d654%Z => first [ eapply evt_eq; [| eapply (IH IP (pe + 1)%Z)]; [num_st_eq | exact INV | assumption | lia | lia | | lia];
                             apply sp_ge48_snoc; [exact G1 | unfold sp_tb; lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Ltac ge48_peel IP :=
    let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
    assert (C : (i = IP \/ i = IP + 1 \/ i = IP + 2 \/ i = IP + 3 \/ i = IP + 4)%Z) by lia;
    destruct C as [-> | [-> | [-> | [-> | ->]]]]; unfold sp_tb; lia.

  Lemma sp_69c : forall (IP : Z) xra xt0 xt2 xs0 xs1 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc -> (A <= IP <= LAST)%Z ->
    evt psegs (sp_post E) (IS 0x4d590 IP xra xt0 (Z_to_bv 64 (sp_tb E IP)) xt2 xs0 xs1 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros until mm. intros INV FRM H1.
    pose proof INV as INV0. sp_open INV0. sp_env OK.
    pose proof (sp_tb_range E IP) as R0. pose proof (sp_tb_range E (IP + 1)) as R1. pose proof (sp_tb_range E (IP + 2)) as R2.
    pose proof (sp_tb_range E (IP + 3)) as R3. pose proof (sp_tb_range E (IP + 4)) as R4.
    unfold sp_tb in R0, R1, R2, R3, R4 |- *.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x4dec0%Z => first [ eapply (sp_fcc E OK); [exact INV | assumption] | fail 100 "cut" pc ]
      | 0x4d81c%Z => first [ eapply evt_eq; [| eapply (sp_928 IP _)]; [num_st_eq | exact INV | assumption | lia | lia | ge48_peel IP] | fail 100 "cut" pc ]
      | 0x4d824%Z => first [ eapply evt_eq; [| eapply (sp_930 IP _)]; [num_st_eq | exact INV | assumption | lia | lia | lia | ge48_peel IP] | fail 100 "cut" pc ]
      | 0x4d654%Z => first [ eapply evt_eq; [| eapply (sp_L1 (Z.to_nat LAST) IP (IP + 5)%Z)]; [num_st_eq | exact INV | assumption | lia | lia | ge48_peel IP | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma sp_668 : forall xra xt0 xt1 xt2 xs0 xs1 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc ->
    evt psegs (sp_post E) (IS 0x4d55c (q_FIRST E) xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 1) xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros until mm. intros INV FRM.
    pose proof INV as INV0. sp_open INV0. sp_env OK.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x4dec0%Z => first [ eapply (sp_fcc E OK); [exact INV | assumption] | fail 100 "cut" pc ]
      | 0x4d590%Z => first [ eapply evt_eq; [| eapply (sp_69c _)]; [unfold sp_tb; num_st_eq | exact INV | assumption | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Ltac peel_cell FR H :=
    lazymatch type of FR with
    | rw_cells ?s ?m ?A0 (?c :: ?rest) =>
        change (c :: rest) with ([c] ++ rest) in FR; apply num_rw_cells_app in FR; destruct FR as [H FR];
        cbn [cells_size csize Nat.add] in FR;
        lazymatch type of FR with
        | rw_cells _ _ (?b + ?k + Z.of_nat ?n)%Z _ =>
            let v := eval vm_compute in (k + Z.of_nat n)%Z in replace (b + k + Z.of_nat n)%Z with (b + v)%Z in FR by lia
        end
    end.

  Theorem sp_body_spec : forall t0 t1 t2 a6 a7 t3 t4 t5 t6 F fc v0,
    mem_inv psegs (q_m0 E) -> frm0 fc -> stk psegs (q_m0 E) (q_lo E) (q_SP E) -> bytes_at psegs (q_m0 E) A (q_txt E) ->
    rw_cells psegs (q_m0 E) OUT [C8 v0] ->
    evt psegs (sp_post E)
      (MS (mkR (q_ra E) (q_sp E) (q_gp E) (q_tp E) t0 t1 t2 (q_s0 E) (q_s1 E) (Z_to_bv 64 (q_FIRST E)) (Z_to_bv 64 LAST) (Z_to_bv 64 OUT)
               (Z_to_bv 64 53) (Z_to_bv 64 SPATH_A4) (Z_to_bv 64 1) a6 a7
               (q_s2 E) (q_s3 E) (q_s4 E) (q_s5 E) (q_s6 E) (q_s7 E) (q_s8 E) (q_s9 E) (q_s10 E) (q_s11 E) t3 t4 t5 t6)
          F (Z_to_bv 64 SPATH_ENTRY) fc None (q_m0 E) (seg_rom psegs)).
  Proof using HSET HPM HPDC HNDC OK.
    intros t0 t1 t2 a6 a7 t3 t4 t5 t6 F fc v0 MI FRM ST TXT OUTC.
    unfold SPATH_ENTRY.
    pose proof (munch_refl (sp_W E) (q_m0 E)) as MU. pose proof (wmono_refl psegs (q_m0 E)) as WM. unfold sp_W in MU.
    pose proof OK as OK0. sp_env OK0.
    assert (LO0 : (0 <= q_lo E)%Z) by (destruct ST as [? _]; assumption).
    set (m := q_m0 E) in MI, ST, TXT, OUTC, MU at 2, WM at 2 |- * at 2. clearbody m.
    step.
    carve_frame 688%nat ST.
    apply (rw_cells_split_CB psegs m _ [] 688 junk [] [32;32;8;496;2;6;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 13 step.
    peel_cell FR PNS. peel_cell FR SPANS. peel_cell FR PERR. peel_cell FR BG. peel_cell FR BGN. peel_cell FR BGP. peel_cell FR DGC.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) => assert (INV : SPINV E m1) by (unfold sp_W, SPATH_STACK, NDC_STACK, P5_STACK, LM_STACK; sp_close) end.
    eapply evt_eq; [| eapply sp_668]; [num_st_eq | exact INV | exact FRM].
  Qed.
End SPINT.

Theorem sp_spec : sp_memset_stmt -> sp_pm_stmt -> sp_pdc_stmt -> sp_ndc_stmt -> spath_stmt_g psegs SPATH_ENTRY SPATH_GTOP.
Proof.
  intros HSET HPM HPDC HNDC. unfold spath_stmt_g. intros until v0. intros MI FRM ST ROOM GTOP TXT TLO TMAX HF HL OUTC HOUT.
  set (E := mkSpEnv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 A FIRST LAST OUT lo txt m).
  assert (OK : sp_ok E) by (constructor; cbn; assumption).
  exact (sp_body_spec HSET HPM HPDC HNDC E OK t0 t1 t2 a6 a7 t3 t4 t5 t6 F fc v0 MI FRM ST TXT OUTC).
Qed.
