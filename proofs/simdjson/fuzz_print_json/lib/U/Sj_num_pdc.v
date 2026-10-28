(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_num_kitu Sj_num_kitn.
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

Definition PDCU_ENTRY : Z := 0x5e15c.
Definition pdcu_p5_stmt : Prop := p5uN_stmt_g usegs 0x5e880 NUMU_GTOP.
Definition pdcu_shl_stmt : Prop := shluN_stmt_g usegs 0x5ef9c.
Definition pdcu_hi64_stmt : Prop := hi64u_stmt_g usegs 0x5e634.

Section PDCU.
  Hypothesis HP5 : pdcu_p5_stmt.
  Hypothesis HSHL : pdcu_shl_stmt.
  Hypothesis HHI : pdcu_hi64_stmt.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X e lo : Z) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Hypothesis ROOM : (lo + PDCU_STACK <= SP)%Z.
  Hypothesis GTOP : (NUMU_GTOP <= lo)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis XLO : (SP <= X)%Z.
  Hypothesis XHI : (X + 498 <= 2^64)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis ER : (0 <= e <= 328)%Z.

  Notation W := [(SP - PDCU_STACK, SP); (X, X + 498)]%Z.
  Notation POST := (bigu_post_g PDCU_STACK usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m0).
  Notation PD pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 (SP + -32)) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2
             s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Definition PDINV (mm : mem) (len : Z) (tb : byte) : Prop :=
    (exists j, rw_cells usegs mm (SP + -32) [CB 7 j]) /\ rw_cells usegs mm (SP + -25) [C1 tb] /\
    rw_cells usegs mm (SP + -24) [C8 s1; C8 s0; C8 ra] /\
    (exists bs, u8arr usegs mm X bs /\ length bs = 496%nat /\ bignorm_b bs len) /\
    rw_cells usegs mm (X + 496) [C2 (Z_to_bv 64 len)] /\ (0 <= len <= 62)%Z /\
    mem_inv usegs mm /\ munch W m0 mm /\ wmono usegs m0 mm /\ stk usegs mm lo (SP + -32).

  Ltac pd_open H :=
    let j := fresh "j" in let bs := fresh "bs" in
    destruct H as ((j & PAD) & TC & FR & (bs & XA & ?XL & NB) & XN & ?LEN & MI & MU & WM & ST); unfold PDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK in MU.
  Ltac pd_close :=
    lazymatch goal with
    | |- PDINV _ _ _ =>
        split; [eexists; eassumption|]; split; [eassumption|]; split; [eassumption|];
        split; [eexists; split; [eassumption| split; [lia| eassumption]]|]; split; [eassumption|]; split; [lia|];
        split; [eassumption|]; split; [eassumption|]; split; eassumption
    end.
  Ltac pd_env :=
    pose proof ROOM as ROOM'; pose proof GTOP as GTOP'; unfold PDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK, NUMU_GTOP in ROOM', GTOP';
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof XHI as XHI'; change (2 ^ 64)%Z with 18446744073709551616%Z in XHI';
    pose proof XLO as XLO'; pose proof SP16 as SP16'; pose proof ER as ER'.

  Lemma pd_exit : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mm len tb,
    PDINV mm len tb ->
    evt usegs POST (PD 0x5e31c xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM GTOP SP16 XLO XHI X8 ER.
    intros until tb. intros INV. pd_open INV. pd_env.
    do 3 zstep. zstep. zstep.
    release_frame PAD ST (SP + -25)%Z.
    release_frame TC ST (SP + -24)%Z.
    release_frame FR ST (bv_unsigned sp).
    destruct (u64arr_of_u8arr usegs mm X bs XA XL) as (ws & WL & WA).
    apply evt_done. unfold bigu_post_g. do 15 eexists. exists mm, ws, len.
    split; [cbv delta [mkR]; reflexivity|].
    unfold PDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK, bigint_at.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [split; [exact WA| split; [exact WL| split; [exact XN| lia]]] | exact ST].
  Qed.

  Lemma pd_13c : forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mm len t,
    PDINV mm len (Z_to_bv 8 t) -> (0 <= t <= 1)%Z ->
    evt usegs POST (PD 0x5e198 xra xt0 xt1 xt2 (Z_to_bv 64 X) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM GTOP SP16 XLO XHI X8 ER.
    intros until t. intros INV Ht. pose proof INV as INV0. pd_open INV. pd_env.
    assert (DA0 : IsData xa0) by exact I.
    pose proof (unsigned_lit8 t ltac:(lia)) as HT8.
    ukwalk ltac:(fun pc => lazymatch pc with 0x5e2b8%Z => u_trap pc | 0x5e1c0%Z => idtac | 0x5e2a8%Z => idtac end).
    -
      uwalk ltac:(fun pc => lazymatch pc with
        | 0x5e2b8%Z => u_trap pc
        | 0x5e31c%Z => first [ eapply pd_exit; exact INV0 | fail 100 "cut" pc ]
        end).
    - zstep. if_cases KBz; zify_cond KBz; [u_clz_dead NB KBz|].
      uwalk ltac:(fun pc => lazymatch pc with
        | 0x5e2b8%Z => u_trap pc
        | 0x5e31c%Z => first [ eapply pd_exit; exact INV0 | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma pd_body : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ws len,
    mem_inv usegs m0 -> stk usegs m0 lo SP -> bigint_at usegs m0 X ws len -> bignorm ws len -> (len + 21 <= 62)%Z ->
    evt usegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PDCU_ENTRY) fc None m0 (seg_rom usegs)).
  Proof using HP5 HSHL HHI ROOM GTOP SP16 XLO XHI X8 ER.
    intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ws len MI ST (WA & WL & XN & LEN) NORM CAP.
    unfold PDCU_ENTRY. pd_env.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl usegs m0) as WM. unfold PDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK in MU.
    set (m := m0) in MI, ST, WA, XN, MU at 2, WM at 2 |- * at 2. clearbody m.
    step.
    carve_frame 32%nat ST.
    apply (rw_cells_split_CB usegs m _ [] 32 junk [] [7;1;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 3 step.
    uwalk ltac:(fun pc => lazymatch pc with | 0x5e880%Z => idtac end).

    pose proof HP5 as HM. unfold pdcu_p5_stmt, p5uN_stmt_g in HM.
    eapply evt_cut.
    { eapply evt_eq; [| eapply HM with (X := X) (e := e) (lo := lo) (ws := ws) (len := len)]; [num_st_eq | ..];
        rewrite ?unsigned_lit by lia; unfold P5U_STACK, LMU_STACK, LAFU_STACK, NUMU_GTOP;
        [ exact MI | exact ST | lia | lia | Z.div_mod_to_equations; lia | split; [exact WA| split; [exact WL| split; [exact XN| lia]]] | lia | lia | lia ]. }
    cbv beta. intros ms' P. unfold biguN_post_g in P.
    destruct P as (? & ? & ? & r0 & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & ws3 & len3 & -> & MUc & WMc & MIc & BIG & STc & G).
    rewrite !unsigned_lit in MUc, STc by lia. unfold P5U_STACK, LMU_STACK, LAFU_STACK in MUc.
    destruct (G NORM ltac:(lia) ER) as (-> & NORM3 & L3). clear G.
    clear WA XN ST.
    lazymatch type of MUc with munch _ ?mo ?mn => transport_after_call usegs mo mn MUc WMc end.
    clear MUc WMc MI HM. destruct BIG as (WA & WL3 & XN & LEN3).
    num_ret_pc. rename MIc into MI. rename STc into ST.
    uwalk ltac:(fun pc => lazymatch pc with | 0x5ef9c%Z => idtac end).

    rewrite (Z.mod_small e 4294967296) by lia.
    pose proof HSHL as HM. unfold pdcu_shl_stmt, shluN_stmt_g in HM.
    eapply evt_cut.
    { eapply HM with (X := X) (lo := lo) (ws := ws3) (len := len3);
        rewrite ?unsigned_lit by lia; unfold SHLU_STACK;
        [ exact MI | exact ST | lia | split; [exact WA| split; [exact WL3| split; [exact XN| lia]]] | lia | lia | lia | exact X8 ]. }
    cbv beta. intros ms' P. unfold biguN_post_g in P.
    destruct P as (? & ? & ? & r0 & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & ws4 & len4 & -> & MUc & WMc & MIc & BIG & STc & G).
    rewrite !unsigned_lit in MUc, STc by lia. unfold SHLU_STACK in MUc.
    unfold shluN_G in G. rewrite unsigned_lit in G by lia.
    destruct (G NORM3 ltac:(Z.div_mod_to_equations; lia)) as (_ & NORM4 & L4). clear G.
    clear WA XN ST.
    lazymatch type of MUc with munch _ ?mo ?mn => transport_after_call usegs mo mn MUc WMc end.
    clear MUc WMc MI HM. destruct BIG as (WA & WL4 & XN & LEN4).
    num_ret_pc. rename MIc into MI. rename STc into ST.
    uwalk ltac:(fun pc => lazymatch pc with | 0x5e634%Z => idtac end).

    change [CB 7 j; CB 1 j0; C8 s1; C8 s0; C8 ra] with ([CB 7 j] ++ [CB 1 j0] ++ [C8 s1; C8 s0; C8 ra]) in FR.
    apply num_rw_cells_app in FR. destruct FR as [PAD FR]. apply num_rw_cells_app in FR. destruct FR as [TC FR].
    cbn [cells_size csize Nat.add] in TC, FR.
    replace (SP + -32 + Z.of_nat 7)%Z with (SP + -25)%Z in TC, FR by lia.
    replace (SP + -25 + Z.of_nat 1)%Z with (SP + -24)%Z in FR by lia.
    destruct (num_cb1_c1 _ _ _ _ TC) as [b0 TC1]. clear TC.
    pose proof HHI as HM. unfold pdcu_hi64_stmt, hi64u_stmt_g in HM.
    eapply evt_cut.
    { eapply HM with (X := X) (T := (SP + -25)%Z) (ws := ws4) (len := len4) (tb0 := b0);
        [ exact MI | split; [exact WA| split; [exact WL4| split; [exact XN| lia]]] | exact NORM4 | lia | exact TC1 | lia | lia ]. }
    cbv beta. intros ms' P. unfold hi64u_post_g in P.
    destruct P as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & tb & -> & MUc & WMc & MIc & TC & TB).
    clear TC1.
    lazymatch type of MUc with munch _ ?mo ?mn => transport_after_call usegs mo mn MUc WMc end.
    clear MUc WMc MI HM.
    num_ret_pc. rename MIc into MI.
    pose proof (u8arr_of_u64arr_s usegs _ X ws4 WA) as XA.
    assert (XL : length (u64s ws4) = 496%nat) by (rewrite u64s_length, WL4; reflexivity).
    assert (NB : bignorm_b (u64s ws4) len4) by (apply bignorm_b_of; [exact NORM4 | lia]).
    clear WA.
    assert (INV : PDINV m5 len4 (Z_to_bv 8 tb)) by pd_close.
    eapply evt_eq; [| eapply pd_13c]; [num_st_eq | exact INV | lia].
  Qed.
End PDCU.

Theorem pdcu_spec : pdcu_p5_stmt -> pdcu_shl_stmt -> pdcu_hi64_stmt -> pdcu_stmt_g usegs PDCU_ENTRY NUMU_GTOP.
Proof.
  intros H5 HS HH. unfold pdcu_stmt_g. intros until len. intros MI ST ROOM GTOP SP16 BIG XLO XHI X8 NORM CAP ER.
  eapply pd_body; eassumption.
Qed.
