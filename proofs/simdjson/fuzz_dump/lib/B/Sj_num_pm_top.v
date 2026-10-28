(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjNumber SjNumU SjNumN.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem
  Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_pm_kit Sj_num_pm_defs Sj_num_pm_round Sj_num_pm_ti Sj_num_pm_tf Sj_num_pm_frac1 Sj_num_pm_frac2 Sj_num_pm_frac3 Sj_num_pm_frac4 Sj_num_pm_frac5 Sj_num_pm_fent Sj_num_pm_int1 Sj_num_pm_int2 Sj_num_pm_int3 Sj_num_pm_int4 Sj_num_pm_int5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac addr_near k ::= let inb := eval vm_compute in (andb (Z.leb 0 k) (Z.ltb k 16384))%Z in lazymatch inb with true => idtac end.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_ptr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.
Local Ltac unorm_in H ::= unorm_in_n H.

Section PMBTOP.
  Variable E : pmbenv.
  Hypothesis OK : pmb_ok E.
  Hypothesis PV : pmb_prov E.
  Notation X := (p_X E).
  Notation DGA := (p_DG E).
  Notation IP := (p_IP E).
  Notation IL := (p_IL E).
  Notation FPT := (p_FPT E).
  Notation FL := (p_FL E).

  Lemma pm_tp_034 : forall xra xt2 xs0 xs1 xa0 xa1 xa4 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt6 mm w8 w16 w32 w40 w48 w56 p,
    PMBINV E mm 0 0 w8 w16 (Z_to_bv 64 (p_N E)) w32 w40 w48 w56 (Z_to_bv 64 (X / 8)) ->
    (IP <= p <= IP + IL)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xea0b4 xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 xa1 (Z_to_bv 64 769) (Z_to_bv 64 DGA) xa4 (Z_to_bv 64 p) xa6 xa7 xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 176064) xt4 (Z_to_bv 64 (IP + IL)) xt6 mm).
  Proof using OK PV.
    intros until p. intros INV Hp. pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xea684%Z => first [ eapply evt_eq; [| eapply (pm_fent E OK PV) with (len := 0%Z) (D := 0%Z)]; [num_st_eq | exact INV | lia | lia] | fail 100 "cut" pc ]
      | 0xea144%Z => first [ eapply evt_eq; [| eapply (in_body E OK PV (Z.to_nat (IP + IL - p)) (in_head E OK PV (Z.to_nat (IP + IL - p)))) with (len := 0%Z) (D := 0%Z) (p := p)]; [num_st_eq | pm_close_with ltac:(exact NB) | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_tp_Z1a : forall (f : nat) (p : Z) xra xt2 xs0 xs1 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt6 mm w8 w16 w32 w40 w48 w56,
    PMBINV E mm 0 0 w8 w16 (Z_to_bv 64 (p_N E)) w32 w40 w48 w56 (Z_to_bv 64 (X / 8)) ->
    (IP <= p < IP + IL)%Z ->
    (IP + IL - p <= Z.of_nat f)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xea068 xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 48) (Z_to_bv 64 769) (Z_to_bv 64 DGA) (Z_to_bv 64 p) (Z_to_bv 64 p) (Z_to_bv 64 18446744073709551615) xa7 xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 176064) xt4 (Z_to_bv 64 (IP + IL)) xt6 mm).
  Proof using OK PV.
    intros f. induction f as [|f IH]; intros until w56; intros INV Hp Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV.
    bstep.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xeb8b4%Z => u_trap pc
      | 0xea0b4%Z => first [ first [ eapply evt_eq; [| eapply pm_tp_034 with (p := p)]; [num_st_eq | exact INV | lia] | eapply evt_eq; [| eapply pm_tp_034 with (p := (IP + IL)%Z)]; [num_st_eq | exact INV | lia] ] | fail 100 "cut" pc ]
      | 0xea068%Z => first [ eapply evt_eq; [| eapply (IH (p + 1)%Z)]; [num_st_eq | exact INV | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_tp_fc0 : forall xra xt2 xs0 xs1 xa0 xa1 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt6 mm w8 w16 w32 w40 w48 w56 w64 p,
    PMBINV E mm 0 0 w8 w16 (Z_to_bv 64 (p_N E)) w32 w40 w48 w56 w64 ->
    (IP <= p <= IP + IL)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xea040 xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 xa0 xa1 (Z_to_bv 64 769) (Z_to_bv 64 DGA) (Z_to_bv 64 p) (Z_to_bv 64 p) xa6 xa7 xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 (Z_to_bv 64 (IP + IL)) xt6 mm).
  Proof using OK PV.
    intros until p. intros INV Hp. pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xeb8b4%Z => u_trap pc
      | 0xea684%Z => first [ eapply evt_eq; [| eapply (pm_fent E OK PV) with (len := 0%Z) (D := 0%Z)]; [num_st_eq | pm_close_with ltac:(exact NB) | lia | lia] | fail 100 "cut" pc ]
      | 0xea068%Z => first [ eapply evt_eq; [| eapply (pm_tp_Z1a (Z.to_nat (IP + IL - p)) p)]; [num_st_eq | pm_close_with ltac:(exact NB) | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_tp_Z8a : forall (f : nat) (k : Z) xra xs0 xs1 xa0 xa1 xa6 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 mm w8 w16 w32 w40 w48 w56 w64,
    PMBINV E mm 0 0 w8 w16 (Z_to_bv 64 (p_N E)) w32 w40 w48 w56 w64 ->
    (0 <= k)%Z ->
    (IP + 8 * k + 8 <= IP + IL)%Z ->
    (IL - 8 * k <= Z.of_nat f)%Z ->
    evt bsegs (pmb_post E) (PMB E 0xe9f84 xra (Z_to_bv 64 (DGA / 8 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 8) xs0 xs1 xa0 xa1 (Z_to_bv 64 769) (Z_to_bv 64 DGA) (Z_to_bv 64 (IP + 8 * k)) (Z_to_bv 64 (IP + 8 * k)) xa6 (Z_to_bv 64 (IL - 8 * k)) xs2 xs3 (Z_to_bv 64 X) xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (2147450880 + IP / 8 + k)) (Z_to_bv 64 3472328296227680304) (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 7) mm).
  Proof using OK PV.
    intros f. induction f as [|f IH]; intros until w64; intros INV Hk Hp8 Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV0. pm_env OK. pm_prov PV.
    bstep.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xeb8b4%Z => u_trap pc
      | 0xea040%Z => first [ first [ eapply evt_eq; [| eapply pm_tp_fc0 with (p := (IP + 8 * k)%Z)]; [num_st_eq | exact INV | lia] | eapply evt_eq; [| eapply pm_tp_fc0 with (p := (IP + 8 * k + 8)%Z)]; [num_st_eq | exact INV | lia] ] | fail 100 "cut" pc ]
      | 0xe9f84%Z => first [ eapply evt_eq; [| eapply (IH (k + 1)%Z)]; [num_st_eq | exact INV | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_body_spec : forall t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 bs jd,
    b_consts (p_m0 E) -> mem_inv bsegs (p_m0 E) -> stk bsegs (p_m0 E) (p_lo E) (p_SP E) ->
    u8arr bsegs (p_m0 E) X bs -> length bs = 496%nat -> rw_cells bsegs (p_m0 E) (X + 496) [C2 (Z_to_bv 64 0)] ->
    bytes_at bsegs (p_m0 E) (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) ->
    rw_cells bsegs (p_m0 E) DGA [CB 8 jd] -> rw_cells bsegs (p_m0 E) (p_N E + 32) (pmb_spans E) ->
    bytes_at bsegs (p_m0 E) (p_A E) (p_txt E) ->
    evt bsegs (pmb_post E)
      (MS (mkR (p_ra E) (p_sp E) (p_gp E) (p_tp E) t0 t1 t2 (p_s0 E) (p_s1 E) (Z_to_bv 64 X) (Z_to_bv 64 (p_N E)) (Z_to_bv 64 769) (Z_to_bv 64 DGA)
               a4 a5 a6 a7 (p_s2 E) (p_s3 E) (p_s4 E) (p_s5 E) (p_s6 E) (p_s7 E) (p_s8 E) (p_s9 E) (p_s10 E) (p_s11 E) t3 t4 t5 t6)
          (p_F E) (Z_to_bv 64 B_PM) (p_fc E) None (p_m0 E) (seg_rom bsegs)).
  Proof using OK PV.
    intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 bs jd (G1 & G2) MI ST XA XL XN ZR DG SPANS TXT.
    unfold B_PM. pose proof OK as OK'. pm_env OK'. unfold pmb_spans in SPANS. pm_prov PV.
    assert (LO0 : (0 <= p_lo E)%Z) by (destruct ST as [? _]; assumption).
    pose proof (pmb_pow10_at _ MI) as TBL. unfold PMB_POW10 in TBL. pose proof pmb_pow10_len as TBLL.
    pose proof (bytes_at_bound _ _ _ _ TXT) as TXB.
    pose proof (repeat_length (Z_to_bv 8 0) 63) as RL.
    pose proof (munch_refl (pmb_W E) (p_m0 E)) as MU. pose proof (wmono_refl bsegs (p_m0 E)) as WM. unfold pmb_W, PMB_STACK in MU.
    set (m := p_m0 E) in G1, G2, MI, ST, XA, XN, ZR, DG, SPANS, TXT, TBL, MU at 2, WM at 2 |- * at 2. clearbody m.
    step.
    carve_frame 176%nat ST.
    apply (rw_cells_split_CB bsegs m _ [] 176 junk [] [8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 13 step.
    apply (num_cb8_c8 bsegs _ _ [CB 8 j]) in FR. apply (num_cb8_c8 bsegs _ _ [CB 8 j; C8 _]) in FR. apply (num_cb8_c8 bsegs _ _ [CB 8 j; C8 _; C8 _]) in FR.
    apply (num_cb8_c8 bsegs _ _ [CB 8 j; C8 _; C8 _; C8 _]) in FR. apply (num_cb8_c8 bsegs _ _ [CB 8 j; C8 _; C8 _; C8 _; C8 _]) in FR.
    apply (num_cb8_c8 bsegs _ _ [CB 8 j; C8 _; C8 _; C8 _; C8 _; C8 _]) in FR. apply (num_cb8_c8 bsegs _ _ [CB 8 j; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _]) in FR.
    apply (num_cb8_c8 bsegs _ _ [CB 8 j; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _]) in FR. cbn [app] in FR.
    assert (NB : (0 < PMB_NORM_DG)%Z -> bignorm_b bs 0) by (intros _; left; reflexivity). unfold PMB_NORM_DG in NB.
    bstep.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xeb8b4%Z => u_trap pc
      | 0xea040%Z => first [ eapply evt_eq; [| eapply pm_tp_fc0 with (p := IP)]; [num_st_eq | pm_close_with ltac:(exact NB) | lia] | fail 100 "cut" pc ]
      | 0xe9f84%Z => first [ eapply evt_eq; [| eapply (pm_tp_Z8a (Z.to_nat IL) 0%Z)]; [num_st_eq | pm_close_with ltac:(exact NB) | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End PMBTOP.

Definition pmb_stmt : Prop :=
  forall (E : pmbenv) t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 bs jd,
    pmb_ok E -> pmb_prov E ->
    b_consts (p_m0 E) -> mem_inv bsegs (p_m0 E) -> stk bsegs (p_m0 E) (p_lo E) (p_SP E) ->
    u8arr bsegs (p_m0 E) (p_X E) bs -> length bs = 496%nat -> rw_cells bsegs (p_m0 E) (p_X E + 496) [C2 (Z_to_bv 64 0)] ->
    bytes_at bsegs (p_m0 E) (p_X E / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) ->
    rw_cells bsegs (p_m0 E) (p_DG E) [CB 8 jd] -> rw_cells bsegs (p_m0 E) (p_N E + 32) (pmb_spans E) ->
    bytes_at bsegs (p_m0 E) (p_A E) (p_txt E) ->
    evt bsegs (pmb_post E)
      (MS (mkR (p_ra E) (p_sp E) (p_gp E) (p_tp E) t0 t1 t2 (p_s0 E) (p_s1 E) (Z_to_bv 64 (p_X E)) (Z_to_bv 64 (p_N E)) (Z_to_bv 64 769) (Z_to_bv 64 (p_DG E))
               a4 a5 a6 a7 (p_s2 E) (p_s3 E) (p_s4 E) (p_s5 E) (p_s6 E) (p_s7 E) (p_s8 E) (p_s9 E) (p_s10 E) (p_s11 E) t3 t4 t5 t6)
          (p_F E) (Z_to_bv 64 B_PM) (p_fc E) None (p_m0 E) (seg_rom bsegs)).
Theorem pmb_spec : pmb_stmt.
Proof. unfold pmb_stmt. intros E t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 bs jd OK PV. exact (pm_body_spec E OK PV t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 bs jd). Qed.
