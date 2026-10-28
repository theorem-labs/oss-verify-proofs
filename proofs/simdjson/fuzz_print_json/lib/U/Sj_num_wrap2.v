(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_num_iface Sj_num_kitu Sj_num_wrap.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.

Definition PFFU_ENTRY : Z := 0x5f1b4.

Section PFFU.
  Hypothesis HFF : nwu_ff_stmt.
  Variable E : nwenv.
  Hypothesis OK : nw_ok E.
  Notation A := (w_A E).
  Notation OUT := (w_OUT E).
  Notation nw_post := (numwu_post_g usegs 0 1 (w_ra E) (w_sp E) (w_gp E) (w_tp E) (w_s0 E) (w_s1 E) (w_s2 E) (w_s3 E) (w_s4 E) (w_s5 E)
                          (w_s6 E) (w_s7 E) (w_s8 E) (w_s9 E) (w_s10 E) (w_s11 E) OUT (w_lo E) (w_m0 E)).

  Notation SC pc e xra xt0 xt1 xt2 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm :=
    (NWS E pc xra xt0 xt1 xt2 (Z_to_bv 64 OUT) (Z_to_bv 64 (A + w_off E)) (Z_to_bv 64 (A + e)) (Z_to_bv 64 10) (Z_to_bv 64 18446744073709551615)
         (Z_to_bv 64 58) (Z_to_bv 64 NUMMASK) xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm).

  Lemma pu_118 : forall (e : Z) xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm,
    NWINV E mm -> frm0 xfc -> (w_off E <= e <= w_stop E)%Z ->
    evt usegs nw_post (NWS E 0x5f224 xra xt0 xt1 xt2 (Z_to_bv 64 OUT) (Z_to_bv 64 (A + w_off E)) (Z_to_bv 64 (A + e)) xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HFF OK.
    intros until mm. intros INV FRM He. nw_open INV. nw_env OK.
    assert (LO0 : (0 <= w_lo E)%Z) by (destruct ST as [? _]; assumption).
    assert (SL : (w_stop E < w_TL E)%Z).
    { assert (X : nth_error (w_txt E) (Z.to_nat (w_stop E)) <> None) by (rewrite HSTOP; discriminate). apply nth_error_Some in X. lia. }
    assert (OB : (OUT + 8 <= 18446744073709551616)%Z).
    { pose proof OUTC as [[Hwf Hb] _]. cbn in Hwf. destruct Hwf as [Hn _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
      pose proof (bytes_at_bound _ _ _ _ Hb) as B. rewrite Hn in B. change (2 ^ 64)%Z with 18446744073709551616%Z in B. lia. }
    zstep.
    pose proof HFF as HS. unfold nwu_ff_stmt, ffu_stmt_g in HS.
    eapply evt_cut.
    { eapply evt_eq; [| eapply HS with (A := A) (FIRST := (A + w_off E)%Z) (LAST := (A + e)%Z) (lo := w_lo E) (txt := w_txt E)];
        [ num_st_eq | .. ]; rewrite ?unsigned_lit by lia; unfold FFU_STACK, SPATHU_STACK, NDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK, NUM_TXT_MAX, NUMU_GTOP;
        [ exact MI | exact FRM | exact ST | lia | lia | Z.div_mod_to_equations; lia | exact TXT | lia | lia | lia | lia | lia ]. }
    cbv beta. intros ms' P. unfold ffu_post_g in P.
    destruct P as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F3 & fc3 & m3 & -> & FRM3 & MUc & WMc & MI3 & ST3).
    rewrite !unsigned_lit in MUc, ST3 by lia. unfold FFU_STACK, SPATHU_STACK, NDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK in MUc.
    clear ST.
    lazymatch type of MUc with munch _ ?mo ?mn => transport_after_call usegs mo mn MUc WMc end.
    clear MUc WMc MI HS.
    num_ret_pc.
    zstep. if_cases KN; zify_cond KN; [exfalso; lia|].
    nstep. zstep. if_cases KA; zify_cond KA; [exfalso; lia|].
    do 4 zstep.
    match goal with |- context [bword ?f] => set (flag := f); clearbody flag end.
    destruct flag; unfold bword; zstep; nstep; do 4 zstep; release_frame FR ST3 (w_SP E);
      lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ ?m1 _) =>
        apply evt_done; unfold numwu_post_g; do 16 eexists; exists m1; eexists;
        first [ exists true; split; [cbv delta [mkR]; reflexivity|] | exists false; split; [cbv delta [mkR]; reflexivity|] ];
        unfold NUMU_STACK;
        (split; [exact FRM|]); (split; [exact MU|]); (split; [exact WM|]); (split; [exact MI3|]); (split; [exact OUTC | exact ST3])
      end.
  Qed.

  Lemma pu_0ec : forall (e c : Z) xra xt0 xt1 xt2 xa7 xt3 xt4 xt5 xt6 xF xfc mm,
    NWINV E mm -> frm0 xfc -> (w_off E <= e <= w_stop E)%Z -> (0 <= c < 256)%Z -> ~ (48 <= c <= 57)%Z -> (e = w_stop E -> numchar c = false) ->
    (forall xa6' xa7', (e < w_stop E)%Z -> evt usegs nw_post (SC 0x5f20c e xra xt0 xt1 xt2 xa6' xa7' xt3 xt4 xt5 xt6 xF xfc mm)) ->
    evt usegs nw_post (SC 0x5f1f8 e xra xt0 xt1 xt2 (Z_to_bv 64 c) xa7 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HFF OK.
    intros until mm. intros INV FRM He Hc ND CS K. unfold NUMMASK in *.
    zstep. zstep. if_cases K1; zify_cond K1.
    { eapply evt_eq; [| eapply (pu_118 e)]; [num_st_eq | exact INV | exact FRM | lia]. }
    zstep. zstep. zstep.
    assert (K43 : (43 <= c <= 101)%Z) by lia.
    replace ((c + -43) mod 64)%Z with (c - 43)%Z by (rewrite Z.mod_small; lia).
    pose proof (numchar_mask c Hc ND K43) as NM. unfold NUMMASK in NM. rewrite NM. clear NM.
    destruct (numchar c) eqn:NC.
    - assert (e <> w_stop E) by (intros X; specialize (CS X); congruence).
      change (bv_eqb (Z_to_bv 64 1) (Z_to_bv 64 0)) with false. cbv iota.
      eapply evt_eq; [| eapply K]; [num_st_eq | lia].
    - change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota.
      eapply evt_eq; [| eapply (pu_118 e)]; [num_st_eq | exact INV | exact FRM | lia].
  Qed.

  Lemma pu_byte : forall e, (0 <= e)%Z ->
    let c := bv_unsigned (nth (Z.to_nat e) (w_txt E) (Z_to_bv 8 0)) in
    (0 <= c < 256)%Z /\ (e = w_stop E -> numchar c = false).
  Proof using OK.
    intros e He c. split.
    - pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat e) (w_txt E) (Z_to_bv 8 0))) as R. unfold bv_modulus in R. cbn in R. unfold c. lia.
    - intros ->. unfold c. destruct OK as [_ _ _ _ _ HSTOP HNC _ _ _ _]. rewrite (nth_error_nth _ _ _ HSTOP). exact HNC.
  Qed.

  Lemma numchar_digit : forall c, (48 <= c <= 57)%Z -> numchar c = true.
  Proof. intros c H. unfold numchar. rewrite (proj2 (Z.leb_le 48 c)), (proj2 (Z.leb_le c 57)) by lia. reflexivity. Qed.

  Lemma pu_iter : forall (cur : Z) xra xt0 xt1 xt2 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm,
    NWINV E mm -> frm0 xfc -> (w_off E <= cur < w_stop E)%Z ->
    (forall xa6' xa7', (cur + 1 < w_stop E)%Z -> evt usegs nw_post (SC 0x5f20c (cur + 1) xra xt0 xt1 xt2 xa6' xa7' xt3 xt4 xt5 xt6 xF xfc mm)) ->
    evt usegs nw_post (SC 0x5f20c cur xra xt0 xt1 xt2 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HFF OK.
    intros until mm. intros INV FRM Hc K. pose proof INV as INV0. nw_open INV0. pose proof OK as OK0. nw_env OK0.
    assert (SL : (w_stop E < w_TL E)%Z).
    { assert (X : nth_error (w_txt E) (Z.to_nat (w_stop E)) <> None) by (rewrite HSTOP; discriminate). apply nth_error_Some in X. lia. }
    zstep. if_cases KM; zify_cond KM; [exfalso; lia|].
    zstep. zstep.
    replace (A + cur + 1 - A)%Z with (cur + 1)%Z by lia.
    destruct (pu_byte (cur + 1)%Z ltac:(lia)) as [CR CS].
    set (c := bv_unsigned (nth (Z.to_nat (cur + 1)) (w_txt E) (Z_to_bv 8 0))) in *. clearbody c.
    zstep. zstep. if_cases K0; zify_cond K0.
    - eapply evt_eq; [| eapply (pu_0ec (cur + 1)%Z c)]; [num_st_eq | exact INV | exact FRM | lia | lia | lia | exact CS |].
      intros. eapply evt_eq; [| eapply K]; [num_st_eq | lia].
    - assert (NC : numchar c = true) by (apply numchar_digit; lia).
      assert (cur + 1 <> w_stop E)%Z by (intros X; specialize (CS X); congruence).
      zstep. eapply evt_eq; [| eapply K]; [num_st_eq | lia].
  Qed.

  Lemma pu_scan : forall (f : nat) (cur : Z) xra xt0 xt1 xt2 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm,
    NWINV E mm -> frm0 xfc -> (w_off E <= cur < w_stop E)%Z -> (w_stop E - cur <= Z.of_nat f)%Z ->
    evt usegs nw_post (SC 0x5f20c cur xra xt0 xt1 xt2 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HFF OK.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM Hc Hf; [exfalso; lia|].
    eapply pu_iter; [exact INV | exact FRM | lia |]. intros xa6' xa7' Hn.
    eapply IH; [exact INV | exact FRM | lia | lia].
  Qed.

  Theorem pu_body_spec : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc junk,
    mem_inv usegs (w_m0 E) -> frm0 fc -> stk usegs (w_m0 E) (w_lo E) (w_SP E) -> bytes_at usegs (w_m0 E) A (w_txt E) ->
    rw_cells usegs (w_m0 E) OUT [CB 8 junk] ->
    evt usegs nw_post
      (MS (mkR (w_ra E) (w_sp E) (w_gp E) (w_tp E) t0 t1 t2 (w_s0 E) (w_s1 E) (Z_to_bv 64 (A + w_off E)) (Z_to_bv 64 OUT) a2 a3 a4 a5 a6 a7
               (w_s2 E) (w_s3 E) (w_s4 E) (w_s5 E) (w_s6 E) (w_s7 E) (w_s8 E) (w_s9 E) (w_s10 E) (w_s11 E) t3 t4 t5 t6)
          F (Z_to_bv 64 PFFU_ENTRY) fc None (w_m0 E) (seg_rom usegs)).
  Proof using HFF OK.
    intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc junk MI FRM ST TXT OUTC.
    unfold PFFU_ENTRY.
    pose proof (munch_refl [(w_SP E - NUMU_STACK, w_SP E); (OUT, OUT + 8)]%Z (w_m0 E)) as MU. pose proof (wmono_refl usegs (w_m0 E)) as WM.
    pose proof OK as OK0. nw_env OK0.
    assert (LO0 : (0 <= w_lo E)%Z) by (destruct ST as [? _]; assumption).
    assert (SL : (w_stop E < w_TL E)%Z).
    { assert (X : nth_error (w_txt E) (Z.to_nat (w_stop E)) <> None) by (rewrite HSTOP; discriminate). apply nth_error_Some in X. lia. }
    set (m := w_m0 E) in MI, ST, TXT, OUTC, MU at 2, WM at 2 |- * at 2. clearbody m.
    step.
    carve_frame 16%nat ST.
    apply (rw_cells_split_CB usegs m _ [] 16 junk0 [] [8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 2 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) => assert (INV : NWINV E m1) by nw_close end.
    zstep. if_cases KN; zify_cond KN; [exfalso; lia|].
    do 10 zstep.
    pose proof (bytes_at_bound _ _ _ _ TXT) as TXB.
    zstep.
    replace (A + w_off E - A)%Z with (w_off E) by lia.
    destruct (pu_byte (w_off E) ltac:(lia)) as [CR CS].
    set (c := bv_unsigned (nth (Z.to_nat (w_off E)) (w_txt E) (Z_to_bv 8 0))) in *. clearbody c.
    zstep. zstep. if_cases K0; zify_cond K0.
    - assert (NC : numchar c = true) by (apply numchar_digit; lia).
      assert (w_off E <> w_stop E)%Z by (intros X; specialize (CS X); congruence).
      eapply evt_eq; [| eapply (pu_scan (Z.to_nat (w_stop E)) (w_off E))]; [unfold NUMMASK; num_st_eq | exact INV | exact FRM | lia | lia].
    - eapply evt_eq; [| eapply (pu_0ec (w_off E) c)]; [unfold NUMMASK; num_st_eq | exact INV | exact FRM | lia | lia | lia | exact CS |].
      intros. eapply evt_eq; [| eapply (pu_scan (Z.to_nat (w_stop E)) (w_off E))]; [num_st_eq | exact INV | exact FRM | lia | lia].
  Qed.
End PFFU.

Theorem pffu_spec : nwu_ff_stmt -> pffu_stmt_g usegs PFFU_ENTRY NUMU_GTOP.
Proof.
  intros HS. unfold pffu_stmt_g, numwu_stmt_g. intros until junk. intros MI FRM ST ROOM GTOP SP16 TXT TLO TMAX HA0 HOFF HSTOP HNC OUTC HOUT OUT8.
  set (E := mkNwEnv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 A off stop OUT lo txt b m).
  assert (OK : nw_ok E) by (constructor; cbn; assumption).
  exact (pu_body_spec HS E OK t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc junk MI FRM ST TXT OUTC).
Qed.
