(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Sj_num_kit Sj_num_walk Sj_num_iface Sj_num_wrap.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Definition PFF_ENTRY : Z := 0x50314.

Section PFF.
  Hypothesis HFF : nw_ff_stmt.
  Variable E : nwenv.
  Hypothesis OK : nw_ok E.
  Notation A := (w_A E).
  Notation OUT := (w_OUT E).
  Notation nw_post := (numw_post_g psegs 0 1 (w_ra E) (w_sp E) (w_gp E) (w_tp E) (w_s0 E) (w_s1 E) (w_s2 E) (w_s3 E) (w_s4 E) (w_s5 E)
                          (w_s6 E) (w_s7 E) (w_s8 E) (w_s9 E) (w_s10 E) (w_s11 E) OUT (w_lo E) (w_m0 E)).

  Lemma pf_3f0 : forall (e : Z) xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm,
    NWINV E mm -> frm0 xfc -> (w_off E <= e <= w_stop E)%Z ->
    evt psegs nw_post (NWS E 0x5036c xra xt0 xt1 xt2 (Z_to_bv 64 OUT) (Z_to_bv 64 (A + w_off E)) (Z_to_bv 64 (A + e)) xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HFF OK.
    intros until mm. intros INV FRM He. nw_open INV. nw_env OK.
    assert (LO0 : (0 <= w_lo E)%Z) by (destruct ST as [? _]; assumption).
    assert (SL : (w_stop E < w_TL E)%Z).
    { assert (X : nth_error (w_txt E) (Z.to_nat (w_stop E)) <> None) by (rewrite HSTOP; discriminate). apply nth_error_Some in X. lia. }
    zstep.
    pose proof HFF as HS. unfold nw_ff_stmt, ff_stmt_g in HS.
    eapply evt_cut.
    { eapply evt_eq; [| eapply HS with (A := A) (FIRST := (A + w_off E)%Z) (LAST := (A + e)%Z) (lo := w_lo E) (txt := w_txt E)];
        [ num_st_eq | .. ]; rewrite ?unsigned_lit by lia; unfold FF_STACK, SPATH_STACK, NDC_STACK, P5_STACK, LM_STACK, NUM_TXT_MAX, NUMW_GTOP;
        [ exact MI | exact FRM | exact ST | lia | lia | exact TXT | lia | lia | lia | lia ]. }
    cbv beta. intros ms' P. unfold ff_post_g in P.
    destruct P as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F3 & fc3 & m3 & -> & FRM3 & MUc & WMc & MI3 & ST3).
    rewrite !unsigned_lit in MUc, ST3 by lia. unfold FF_STACK, SPATH_STACK, NDC_STACK, P5_STACK, LM_STACK in MUc.
    clear ST.
    lazymatch type of MUc with munch _ ?mo ?mn => transport_after_call psegs mo mn MUc WMc end.
    clear MUc WMc MI HS.
    num_ret_pc.
    do 4 zstep.
    match goal with |- context [bword ?f] => set (flag := f); clearbody flag end.
    assert (X1 : bv_xor (Z_to_bv 64 1) (Z_to_bv 64 1) = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    assert (X0 : bv_xor (Z_to_bv 64 0) (Z_to_bv 64 1) = Z_to_bv 64 1) by (apply bv_eq; vm_compute; reflexivity).
    destruct flag; unfold bword; zstep; nstep; do 4 zstep; release_frame FR ST3 (w_SP E);
      lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ ?m1 _) =>
        apply evt_done; unfold numw_post_g; do 16 eexists; exists m1; eexists;
        first [ exists true; split; [cbv delta [mkR]; reflexivity|] | exists false; split; [cbv delta [mkR]; reflexivity|] ];
        unfold NUM_STACK;
        (split; [exact FRM|]); (split; [exact MU|]); (split; [exact WM|]); (split; [exact MI3|]); (split; [exact OUTC | exact ST3])
      end.
  Qed.

  Lemma pf_iter : forall (cur : Z) xra xt0 xt1 xt2 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm,
    NWINV E mm -> frm0 xfc -> (w_off E <= cur <= w_stop E)%Z ->
    (forall xa5' xa6', (cur + 1 <= w_stop E)%Z ->
       evt psegs nw_post (NWS E 0x5034c xra xt0 xt1 xt2 (Z_to_bv 64 OUT) (Z_to_bv 64 (A + w_off E)) (Z_to_bv 64 (A + (cur + 1))) (Z_to_bv 64 10) (Z_to_bv 64 58)
                              (Z_to_bv 64 NUMMASK) xa5' xa6' xa7 xt3 xt4 xt5 xt6 xF xfc mm)) ->
    evt psegs nw_post (NWS E 0x5034c xra xt0 xt1 xt2 (Z_to_bv 64 OUT) (Z_to_bv 64 (A + w_off E)) (Z_to_bv 64 (A + cur)) (Z_to_bv 64 10) (Z_to_bv 64 58)
                              (Z_to_bv 64 NUMMASK) xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HFF OK.
    intros until mm. intros INV FRM Hc K. pose proof INV as INV0. nw_open INV0. nw_env OK.
    assert (SL : (w_stop E < w_TL E)%Z).
    { assert (X : nth_error (w_txt E) (Z.to_nat (w_stop E)) <> None) by (rewrite HSTOP; discriminate). apply nth_error_Some in X. lia. }
    unfold NUMMASK in *.
    zstep.
    replace (A + cur - A)%Z with cur by lia.
    set (c := nth (Z.to_nat cur) (w_txt E) (Z_to_bv 8 0)).
    assert (CR : (0 <= bv_unsigned c < 256)%Z) by (pose proof (bv_unsigned_in_range 8 c) as R; unfold bv_modulus in R; cbn in R; lia).
    assert (CS : cur = w_stop E -> numchar (bv_unsigned c) = false).
    { intros ->. unfold c. rewrite (nth_error_nth _ _ _ HSTOP). exact HNC. }
    clearbody c.
    zstep. zstep. if_cases K0; zify_cond K0.
    { assert (NC : numchar (bv_unsigned c) = true).
      { unfold numchar. rewrite (proj2 (Z.leb_le 48 (bv_unsigned c))), (proj2 (Z.leb_le (bv_unsigned c) 57)) by lia. reflexivity. }
      assert (cur <> w_stop E) by (intros X; specialize (CS X); congruence).
      zstep. eapply evt_eq; [| eapply K]; [num_st_eq | lia]. }
    zstep. zstep. if_cases K1; zify_cond K1.
    { eapply evt_eq; [| eapply (pf_3f0 cur)]; [num_st_eq | exact INV | exact FRM | lia]. }
    zstep. zstep. zstep.
    assert (K43 : (43 <= bv_unsigned c <= 101)%Z) by lia.
    replace ((bv_unsigned c + -43) mod 64)%Z with (bv_unsigned c - 43)%Z by (rewrite Z.mod_small; lia).
    assert (ND : ~ (48 <= bv_unsigned c <= 57)%Z) by lia.
    pose proof (numchar_mask (bv_unsigned c) CR ND K43) as NM. unfold NUMMASK in NM. rewrite NM. clear NM.
    destruct (numchar (bv_unsigned c)) eqn:NC.
    - assert (cur <> w_stop E) by (intros X; specialize (CS X); congruence).
      change (negb (bv_eqb (Z_to_bv 64 1) (Z_to_bv 64 0))) with true. cbv iota.
      zstep. eapply evt_eq; [| eapply K]; [num_st_eq | lia].
    - change (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false. cbv iota.
      eapply evt_eq; [| eapply (pf_3f0 cur)]; [num_st_eq | exact INV | exact FRM | lia].
  Qed.

  Lemma pf_scan : forall (f : nat) (cur : Z) xra xt0 xt1 xt2 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm,
    NWINV E mm -> frm0 xfc -> (w_off E <= cur <= w_stop E)%Z -> (w_stop E - cur <= Z.of_nat f)%Z ->
    evt psegs nw_post (NWS E 0x5034c xra xt0 xt1 xt2 (Z_to_bv 64 OUT) (Z_to_bv 64 (A + w_off E)) (Z_to_bv 64 (A + cur)) (Z_to_bv 64 10) (Z_to_bv 64 58)
                              (Z_to_bv 64 NUMMASK) xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HFF OK.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM Hc Hf; eapply pf_iter; try eassumption; intros xa5' xa6' Hn.
    - exfalso; lia.
    - eapply IH; [exact INV | exact FRM | lia | lia].
  Qed.

  Theorem pf_body_spec : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc junk,
    mem_inv psegs (w_m0 E) -> frm0 fc -> stk psegs (w_m0 E) (w_lo E) (w_SP E) -> bytes_at psegs (w_m0 E) A (w_txt E) ->
    rw_cells psegs (w_m0 E) OUT [CB 8 junk] ->
    evt psegs nw_post
      (MS (mkR (w_ra E) (w_sp E) (w_gp E) (w_tp E) t0 t1 t2 (w_s0 E) (w_s1 E) (Z_to_bv 64 (A + w_off E)) (Z_to_bv 64 OUT) a2 a3 a4 a5 a6 a7
               (w_s2 E) (w_s3 E) (w_s4 E) (w_s5 E) (w_s6 E) (w_s7 E) (w_s8 E) (w_s9 E) (w_s10 E) (w_s11 E) t3 t4 t5 t6)
          F (Z_to_bv 64 PFF_ENTRY) fc None (w_m0 E) (seg_rom psegs)).
  Proof using HFF OK.
    intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc junk MI FRM ST TXT OUTC.
    unfold PFF_ENTRY.
    pose proof (munch_refl [(w_SP E - NUM_STACK, w_SP E); (OUT, OUT + 8)]%Z (w_m0 E)) as MU. pose proof (wmono_refl psegs (w_m0 E)) as WM.
    pose proof OK as OK0. nw_env OK0.
    assert (LO0 : (0 <= w_lo E)%Z) by (destruct ST as [? _]; assumption).
    set (m := w_m0 E) in MI, ST, TXT, OUTC, MU at 2, WM at 2 |- * at 2. clearbody m.
    step.
    carve_frame 16%nat ST.
    apply (rw_cells_split_CB psegs m _ [] 16 junk0 [] [8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 2 step. do 10 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) => assert (INV : NWINV E m1) by nw_close end.
    eapply evt_eq; [| eapply (pf_scan (Z.to_nat (w_stop E)) (w_off E))]; [unfold NUMMASK; num_st_eq | exact INV | exact FRM | lia | lia].
  Qed.
End PFF.

Theorem pff_spec : nw_ff_stmt -> pff_stmt_g psegs PFF_ENTRY NUMW_GTOP.
Proof.
  intros HS. unfold pff_stmt_g, numw_stmt_g. intros until junk. intros MI FRM ST ROOM GTOP TXT TLO TMAX HOFF HSTOP HNC OUTC HOUT.
  set (E := mkNwEnv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 A off stop OUT lo txt b m).
  assert (OK : nw_ok E) by (constructor; cbn; assumption).
  exact (pf_body_spec HS E OK t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc junk MI FRM ST TXT OUTC).
Qed.
