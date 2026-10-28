(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_num_kitu Sj_num_kitn Sj_num_pm_defs Sj_num_pm_round Sj_num_pm_tf Sj_num_pm_frac Sj_num_pm_fent Sj_num_pm_int.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.
Local Ltac unorm_in H ::= unorm_in_n H.

Section PMUTOP.
  Variable E : pmuenv.
  Hypothesis OK : pmu_ok E.
  Notation X := (p_X E).
  Notation IP := (p_IP E).
  Notation IL := (p_IL E).
  Notation FPT := (p_FPT E).
  Notation FL := (p_FL E).

  Lemma pm_tp_294 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa5 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm v16 p,
    PMUINV E mm 0 0 v16 ->
    (IP <= p <= IP + IL)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d2f0 xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 (X + -72)) (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 116824) xa5 (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 p) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until p. intros INV Hp. pose proof INV as INV0. pm_open INV0. pm_env OK.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5d658%Z => first [ eapply evt_eq; [| eapply (pm_fent E OK) with (len := 0%Z) (D := 0%Z)]; [num_st_eq | exact INV | lia | lia] | fail 100 "cut" pc ]
      | 0x5d364%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 0 0 (Z_to_bv 64 761) (0 < PMU_NORM_DG)%Z) by (pm_close_with ltac:(exact NB))); eapply evt_eq; [| eapply (in_body E OK (Z.to_nat (IP + IL - p)) (in_head E OK (Z.to_nat (IP + IL - p)))) with (len := 0%Z) (D := 0%Z) (p := p)]; [num_st_eq | exact INV1 | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_tp_Z1a : forall (f : nat) (p : Z) xra xt1 xt2 xs0 xs1 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm v16,
    PMUINV E mm 0 0 v16 ->
    (IP <= p < IP + IL)%Z ->
    (IP + IL - p <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d2d4 xra (Z_to_bv 64 18446744073709551615) xt1 xt2 xs0 xs1 (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 (X + -72)) (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 116824) (Z_to_bv 64 48) (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 p) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until v16; intros INV Hp Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV0. pm_env OK.
    nstep.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5d2f0%Z => first [ first [ eapply evt_eq; [| eapply pm_tp_294 with (p := p)]; [num_st_eq | exact INV | lia] | eapply evt_eq; [| eapply pm_tp_294 with (p := (IP + IL)%Z)]; [num_st_eq | exact INV | lia] ] | fail 100 "cut" pc ]
      | 0x5d2d4%Z => first [ eapply evt_eq; [| eapply (IH (p + 1)%Z)]; [num_st_eq | exact INV | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_tp_25c : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa4 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm v16 p,
    PMUINV E mm 0 0 v16 ->
    (IP <= p <= IP + IL)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d2b8 xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 (X + -72)) (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) xa4 (Z_to_bv 64 p) (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 p) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until p. intros INV Hp. pose proof INV as INV0. pm_open INV0. pm_env OK.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5d658%Z => first [ eapply evt_eq; [| eapply (pm_fent E OK) with (len := 0%Z) (D := 0%Z)]; [num_st_eq | exact INV | lia | lia] | fail 100 "cut" pc ]
      | 0x5d2d4%Z => first [ eapply evt_eq; [| eapply (pm_tp_Z1a (Z.to_nat (IP + IL - p)) p)]; [num_st_eq | exact INV | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_tp_Z8a : forall (f : nat) (p : Z) xra xs0 xs1 xa0 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm v16,
    PMUINV E mm 0 0 v16 ->
    (IP <= p)%Z ->
    (p + 8 <= IP + IL)%Z ->
    (IP + IL - p <= Z.of_nat f)%Z ->
    evt usegs (pmu_post E) (PM E 0x5d240 xra (Z_to_bv 64 8) (Z_to_bv 64 3472328296227680304) (Z_to_bv 64 7) xs0 xs1 xa0 (Z_to_bv 64 (X + -72)) (Z_to_bv 64 769) (Z_to_bv 64 (X + 504)) (Z_to_bv 64 (IP + IL - p)) (Z_to_bv 64 p) (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 p) (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until v16; intros INV Hp Hp8 Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV0. pm_env OK.
    nstep.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5d2b8%Z => first [ first [ eapply evt_eq; [| eapply pm_tp_25c with (p := p)]; [num_st_eq | exact INV | lia] | eapply evt_eq; [| eapply pm_tp_25c with (p := (p + 8)%Z)]; [num_st_eq | exact INV | lia] ] | fail 100 "cut" pc ]
      | 0x5d240%Z => first [ eapply evt_eq; [| eapply (IH (p + 8)%Z)]; [num_st_eq | exact INV | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Ltac peel_cell FR H :=
    lazymatch type of FR with
    | rw_cells ?s ?m ?A0 (?c :: ?rest) =>
        change (c :: rest) with ([c] ++ rest) in FR; apply num_rw_cells_app in FR; destruct FR as [H FR];
        cbn [cells_size csize Nat.add] in FR
    end.

  Lemma pm_body_spec : forall t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ws jd,
    mem_inv usegs (p_m0 E) -> stk usegs (p_m0 E) (p_lo E) (p_SP E) -> bigint_at usegs (p_m0 E) X ws 0 ->
    rw_cells usegs (p_m0 E) (X + 504) [CB 8 jd] -> rw_cells usegs (p_m0 E) (X + -40) (pmu_spans E) ->
    bytes_at usegs (p_m0 E) (p_A E) (p_txt E) ->
    evt usegs (pmu_post E)
      (MS (mkR (p_ra E) (p_sp E) (p_gp E) (p_tp E) t0 t1 t2 (p_s0 E) (p_s1 E) (Z_to_bv 64 X) (Z_to_bv 64 (X - 72)) (Z_to_bv 64 PM_MAXD) (Z_to_bv 64 (X + 504))
               a4 a5 a6 a7 (p_s2 E) (p_s3 E) (p_s4 E) (p_s5 E) (p_s6 E) (p_s7 E) (p_s8 E) (p_s9 E) (p_s10 E) (p_s11 E) t3 t4 t5 t6)
          (p_F E) (Z_to_bv 64 PMU_ENTRY) (p_fc E) None (p_m0 E) (seg_rom usegs)).
  Proof using OK.
    intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ws jd MI ST (WA & WL & XN & LEN) DG SPANS TXT.
    unfold PMU_ENTRY, PM_MAXD. pose proof OK as OK'. pm_env OK'. unfold pmu_spans in SPANS.
    replace (X - 72)%Z with (X + -72)%Z by lia.
    assert (LO0 : (0 <= p_lo E)%Z) by (destruct ST as [? _]; assumption).
    pose proof (pmu_pow10_at _ MI) as TBL. unfold PMU_POW10 in TBL. pose proof pmu_pow10_len as TBLL.
    pose proof (bytes_at_bound _ _ _ _ TXT) as TXB.
    pose proof (munch_refl (pmu_W E) (p_m0 E)) as MU. pose proof (wmono_refl usegs (p_m0 E)) as WM. unfold pmu_W, PMU_STACK in MU.
    set (m := p_m0 E) in MI, ST, WA, XN, DG, SPANS, TXT, TBL, MU at 2, WM at 2 |- * at 2. clearbody m.
    step.
    carve_frame 128%nat ST.
    apply (rw_cells_split_CB usegs m _ [] 128 junk [] [8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 13 step.
    apply (num_cb8_c8 usegs _ _ [CB 8 j]) in FR. apply (num_cb8_c8 usegs _ _ [CB 8 j; C8 _]) in FR. cbn [app] in FR.
    pose proof (u8arr_of_u64arr_s usegs _ X ws WA) as XA. assert (XL : length (u64s ws) = 496%nat) by (rewrite u64s_length, WL; reflexivity).
    assert (NB : (0 < PMU_NORM_DG)%Z -> bignorm_b (u64s ws) 0) by (intros _; left; reflexivity).
    clear WA.
    nstep.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e158%Z => u_trap pc
      | 0x5d2b8%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 0 0 _ (0 < PMU_NORM_DG)%Z) by (pm_close_with ltac:(exact NB))); eapply evt_eq; [| eapply pm_tp_25c with (p := IP)]; [num_st_eq | exact INV1 | lia] | fail 100 "cut" pc ]
      | 0x5d240%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : PMUINVg E m1 0 0 _ (0 < PMU_NORM_DG)%Z) by (pm_close_with ltac:(exact NB))); eapply evt_eq; [| eapply (pm_tp_Z8a (Z.to_nat IL) IP)]; [num_st_eq | exact INV1 | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End PMUTOP.

Theorem pmu_spec : pmu_stmt_g usegs PMU_ENTRY NUMU_GTOP.
Proof.
  unfold pmu_stmt_g. intros until jd. intros MI ST ROOM GTOP BIG XLO XHI DG SPANS TXT TLO TMAX A0 SPN.
  set (E := mkPmuEnv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X A IP IL FPT FL lo txt m).
  assert (OK : pmu_ok E) by (constructor; assumption).
  replace (X - 40)%Z with (X + -40)%Z in SPANS by lia.
  exact (pm_body_spec E OK t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ws jd MI ST BIG DG SPANS TXT).
Qed.
