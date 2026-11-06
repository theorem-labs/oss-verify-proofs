(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_num_kit Sj_num_walk Sj_num_pm_defs Sj_num_pm_fent Sj_num_pm_int.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section PMTOP.
  Variable E : pmenv.
  Hypothesis OK : pm_ok E.
  Notation X := (p_X E).
  Notation A := (p_A E).
  Notation TL := (p_TL E).
  Notation IP := (p_IP E).
  Notation PE := (p_IP E + p_IL E)%Z.

  Lemma pm_b90 : forall (q : Z) xt0 xt1 xt2 xs0 xs1 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (IP <= q <= PE)%Z -> (0 <= dg < 769)%Z ->
    evt psegs (pm_post E) (PMX E 0x51a3c xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (X + -72)) (Z_to_bv 64 769) (Z_to_bv 64 110104) (Z_to_bv 64 PE) (Z_to_bv 64 q) xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until dg. intros INV Hq Hd.
    pose proof INV as INV0. pm_open INV. pm_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x51d14%Z => first [ eapply (pm_int_done E OK); [exact INV0 | lia] | fail 100 "cut" pc ]
      | 0x51ab8%Z => first [ eapply evt_eq; [| eapply (pm_i_head E OK _ _ _ _ _ (Z.to_nat (PE - q)) q len dg)]; [num_st_eq | exact INV0 | lia | lia | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_szib : forall (f : nat) (q : Z) xt1 xt2 xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (IP <= q < PE)%Z -> (0 <= dg < 769)%Z -> (PE - q <= Z.of_nat f)%Z ->
    evt psegs (pm_post E) (PMX E 0x51a28 (Z_to_bv 64 48) xt1 xt2 xs0 xs1 (Z_to_bv 64 (X + -72)) (Z_to_bv 64 769) (Z_to_bv 64 110104) (Z_to_bv 64 PE) (Z_to_bv 64 q) (Z_to_bv 64 PE)
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until dg; intros INV Hq Hd Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV. pm_env OK. nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x51a3c%Z => first [ eapply evt_eq; [| eapply (pm_b90 _)]; [num_st_eq | exact INV0 | lia | lia] | fail 100 "cut" pc ]
      | 0x51a28%Z => first [ eapply evt_eq; [| eapply (IH (q + 1)%Z)]; [num_st_eq | exact INV0 | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_b64 : forall (q : Z) xt0 xt1 xt2 xs0 xs1 xa4 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (IP <= q <= PE)%Z -> (0 <= dg < 769)%Z ->
    evt psegs (pm_post E) (PMX E 0x51a10 xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (X + -72)) (Z_to_bv 64 769) xa4 (Z_to_bv 64 PE) (Z_to_bv 64 q) (Z_to_bv 64 q)
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros until dg. intros INV Hq Hd.
    pose proof INV as INV0. pm_open INV. pm_env OK.
    walk ltac:(fun pc => lazymatch pc with
      | 0x51d14%Z => first [ eapply (pm_int_done E OK); [exact INV0 | lia] | fail 100 "cut" pc ]
      | 0x51a28%Z => first [ eapply evt_eq; [| eapply (pm_szib (Z.to_nat (PE - q)) q)]; [num_st_eq | exact INV0 | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pm_szi8 : forall (f : nat) (q : Z) xt2 xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm len dg,
    PMINV E mm len dg -> (IP <= q)%Z -> (8 <= PE - q)%Z -> (0 <= dg < 769)%Z -> (PE - q <= 8 * Z.of_nat f)%Z ->
    evt psegs (pm_post E) (PMX E 0x5199c (Z_to_bv 64 3472328296227680304) (Z_to_bv 64 7) xt2 xs0 xs1 (Z_to_bv 64 (X + -72)) (Z_to_bv 64 769) (Z_to_bv 64 (PE - q))
                               (Z_to_bv 64 PE) (Z_to_bv 64 q) (Z_to_bv 64 q)
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until dg; intros INV Hq H8 Hd Hf; [exfalso; lia|].
    pose proof INV as INV0. pm_open INV. pm_env OK. nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x51a10%Z => first [ eapply evt_eq; [| eapply (pm_b64 _)]; [num_st_eq | exact INV0 | lia | lia] | fail 100 "cut" pc ]
      | 0x5199c%Z => first [ eapply evt_eq; [| eapply (IH (q + 8)%Z)]; [num_st_eq | exact INV0 | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Theorem pm_body_spec : forall t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ws len jd,
    mem_inv psegs (p_m0 E) -> stk psegs (p_m0 E) (p_lo E) (p_SP E) -> bigint_at psegs (p_m0 E) X ws len ->
    rw_cells psegs (p_m0 E) (X + 504) [CB 8 jd] -> rw_cells psegs (p_m0 E) (X - 40) (pm_spans E) ->
    bytes_at psegs (p_m0 E) A (p_txt E) ->
    evt psegs (pm_post E)
      (MS (mkR (p_ra E) (p_sp E) (p_gp E) (p_tp E) t0 t1 t2 (p_s0 E) (p_s1 E) (Z_to_bv 64 X) (Z_to_bv 64 (X - 72)) (Z_to_bv 64 PM_MAXD) (Z_to_bv 64 (X + 504))
               a4 a5 a6 a7 (p_s2 E) (p_s3 E) (p_s4 E) (p_s5 E) (p_s6 E) (p_s7 E) (p_s8 E) (p_s9 E) (p_s10 E) (p_s11 E) t3 t4 t5 t6)
          (p_F E) (Z_to_bv 64 PM_ENTRY) (p_fc E) None (p_m0 E) (seg_rom psegs)).
  Proof using OK.
    intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ws len jd MI ST (WA & WL & XN & LEN) DG SPANS TXT.
    unfold PM_ENTRY, PM_MAXD.
    replace (X - 72)%Z with (X + -72)%Z by lia. replace (X - 40)%Z with (X + -40)%Z in SPANS by lia.
    pm_env OK.
    assert (LO0 : (0 <= p_lo E)%Z) by (destruct ST as [? _]; assumption).
    destruct (u8arr_of_u64arr psegs _ X ws WA WL) as (bs & XL & XA). clear WA WL ws.
    destruct (image_readable_b psegs (p_m0 E) 160 PM_POW10 ltac:(vm_compute; reflexivity) ltac:(unfold PM_POW10; lia) ltac:(unfold PM_POW10; cbn; lia))
      as (tb & TBLL & TBL).
    unfold PM_POW10 in TBL. unfold pm_spans in SPANS.
    pose proof (bytes_at_bound _ _ _ _ TXT) as TXB.
    pose proof (munch_refl (pm_W E) (p_m0 E)) as MU. pose proof (wmono_refl psegs (p_m0 E)) as WM. unfold pm_W, PM_STACK in MU.
    set (m := p_m0 E) in MI, ST, XA, XN, DG, SPANS, TXT, TBL, MU at 2, WM at 2 |- * at 2. clearbody m.
    step.
    carve_frame 96%nat ST.
    apply (rw_cells_split_CB psegs m _ [] 96 junk [] [8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 11 step.
    walk ltac:(fun pc => lazymatch pc with
      | 0x51a10%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV : PMINV E m1 len 0) by pm_close);
                             eapply evt_eq; [| eapply (pm_b64 IP)]; [num_st_eq | exact INV | lia | lia] | fail 100 "cut" pc ]
      | 0x5199c%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV : PMINV E m1 len 0) by pm_close);
                             eapply evt_eq; [| eapply (pm_szi8 (Z.to_nat (p_IL E)) IP)]; [num_st_eq | exact INV | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End PMTOP.

Theorem pm_spec : pm_stmt_g psegs PM_ENTRY PM_GTOP.
Proof.
  unfold pm_stmt_g. intros until jd. intros MI ST ROOM GTOP BIG XHI DG SPANS TXT TLO TMAX SPN.
  set (E := mkPmEnv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X A IP IL FPT FL lo txt m).
  assert (OK : pm_ok E) by (constructor; cbn; assumption).
  exact (pm_body_spec E OK t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ws len jd MI ST BIG DG SPANS TXT).
Qed.
