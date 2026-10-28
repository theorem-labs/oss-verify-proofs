(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_num_kitu Sj_num_kitn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Ltac nnorm_ndc :=
  repeat match goal with
  | |- context [bv_swrap 32 (?p mod 4294967296 + ?k)] => rewrite (swrap32_zext_add p k) by lia
  | |- context [bv_swrap 32 (?p mod 4294967296)] => rewrite (swrap32_zext p) by lia
  end;
  nnorm_u.
Local Ltac nnorm ::= nnorm_ndc.
Local Ltac num_abstract_data ::= num_abstract_data_u.

Definition NDCU_ENTRY : Z := 0x5e020.
Definition ndcu_p5_stmt : Prop := p5u_stmt_g usegs 0x5e570 NUMU_GTOP.
Definition ndcu_shl_stmt : Prop := shlu_stmt_g usegs 0x5ec8c.
Definition ndcu_memset_stmt : Prop := memsetZ_stmt_g usegs 0xd0c68.

Section NDCU.
  Hypothesis HP5 : ndcu_p5_stmt.
  Hypothesis HSHL : ndcu_shl_stmt.
  Hypothesis HSET : ndcu_memset_stmt.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X p2 e lo : Z) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Hypothesis ROOM : (lo + NDCU_STACK <= SP)%Z.
  Hypothesis GTOP : (NUMU_GTOP <= lo)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis XLO : (SP <= X)%Z.
  Hypothesis XHI : (X + 498 <= 2^64)%Z.
  Hypothesis PR : (- NDCU_RANGE <= p2 <= NDCU_RANGE)%Z.
  Hypothesis ER : (- NDCU_RANGE <= e <= NDCU_RANGE)%Z.

  Notation W := [(SP - NDCU_STACK, SP); (X, X + 498)]%Z.
  Notation POST := (bigu_post_g NDCU_STACK usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m0).
  Notation FB := (SP + -576)%Z.
  Notation ND pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 FB) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7
             s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Definition ndcu_saved : list cell := [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition NDINV (mm : mem) (len tlen : Z) : Prop :=
    (exists tb, u8arr usegs mm FB tb /\ length tb = 496%nat) /\
    rw_cells usegs mm (SP + -80) [C2 (Z_to_bv 64 tlen)] /\ (0 <= tlen <= 62)%Z /\
    (exists j, rw_cells usegs mm (SP + -78) [CB 6 j]) /\
    rw_cells usegs mm (SP + -72) ndcu_saved /\
    (exists bs, u8arr usegs mm X bs /\ length bs = 496%nat) /\
    rw_cells usegs mm (X + 496) [C2 (Z_to_bv 64 len)] /\ (0 <= len <= 62)%Z /\
    mem_inv usegs mm /\ munch W m0 mm /\ wmono usegs m0 mm /\ stk usegs mm lo FB.

  Ltac nd_open H :=
    let tb := fresh "tb" in let j := fresh "j" in let bs := fresh "bs" in
    destruct H as ((tb & TA & ?TL) & TN & ?TLEN & (j & TP) & SAVED & (bs & XA & ?XL) & XN & ?LEN & MI & MU & WM & ST);
    unfold ndcu_saved in SAVED; unfold NDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK in MU.
  Ltac nd_close :=
    lazymatch goal with
    | |- NDINV _ _ _ =>
        split; [eexists; split; [eassumption| lia]|]; split; [eassumption|]; split; [lia|]; split; [eexists; eassumption|];
        split; [eassumption|]; split; [eexists; split; [eassumption| lia]|]; split; [eassumption|]; split; [lia|];
        split; [eassumption|]; split; [eassumption|]; split; eassumption
    end.
  Ltac nd_env :=
    pose proof ROOM as ROOM'; pose proof GTOP as GTOP'; unfold NDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK, NUMU_GTOP in ROOM', GTOP';
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof XHI as XHI'; change (2 ^ 64)%Z with 18446744073709551616%Z in XHI';
    pose proof XLO as XLO'; pose proof SP16 as SP16'; pose proof PR as PR'; pose proof ER as ER'; unfold NDCU_RANGE in PR', ER'.

  Lemma nd_exit : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xt3 xt4 xt5 xt6 mm len tlen,
    NDINV mm len tlen ->
    evt usegs POST (ND 0x5e2bc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM GTOP SP16 XLO XHI PR ER.
    intros until tlen. intros INV. nd_open INV. nd_env.
    do 9 zstep. zstep. zstep.
    apply (rw_cells_of_u8arr usegs) in TA. rewrite TL in TA.
    release_frame TA ST (SP + -80)%Z.
    release_frame TN ST (SP + -78)%Z.
    release_frame TP ST (SP + -72)%Z.
    release_frame SAVED ST (bv_unsigned sp).
    destruct (u64arr_of_u8arr usegs mm X bs XA XL) as (ws & WL & WA).
    apply evt_done. unfold bigu_post_g. do 15 eexists. exists mm, ws, len.
    split; [cbv delta [mkR]; reflexivity|].
    unfold NDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK, bigint_at.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [split; [exact WA| split; [exact WL| split; [exact XN| lia]]] | exact ST].
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

  Lemma nd_4bc : forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xt3 xt4 xt5 xt6 mm len tlen,
    NDINV mm len tlen ->
    evt usegs POST (ND 0x5e208 xra xt0 xt1 xt2 (Z_to_bv 64 (p2 mod 4294967296)) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       (Z_to_bv 64 X) (Z_to_bv 64 e) (Z_to_bv 64 p2) (Z_to_bv 64 (0 - p2)) xs6 xs7 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM GTOP SP16 XLO XHI PR ER.
    intros until tlen. intros INV. pose proof INV as INV0. nd_open INV0. nd_env.
    assert (DS1 : IsData xs1) by exact I. assert (DA0 : IsData xa0) by exact I. assert (DA1 : IsData xa1) by exact I.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e320%Z => u_trap pc
      | 0x5e2bc%Z => first [ eapply nd_exit; exact INV | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma nd_C : forall (f : nat) (k : Z) xra xt0 xt1 xt2 xs1 xa1 xa7 xs6 xs7 xt3 xt4 xt5 xt6 mm len tlen,
    NDINV mm len tlen -> (0 <= k <= 62)%Z -> (k <= Z.of_nat f)%Z ->
    evt usegs POST (ND 0x5e1d0 xra xt0 xt1 xt2 (Z_to_bv 64 (p2 mod 4294967296)) xs1 (Z_to_bv 64 1) xa1 (Z_to_bv 64 (18446744073709551615 - X))
                       (Z_to_bv 64 FB) (Z_to_bv 64 (18446744073709551615 - FB)) (Z_to_bv 64 18446744073709551600) (Z_to_bv 64 (8 * k + -8)) xa7
                       (Z_to_bv 64 X) (Z_to_bv 64 e) (Z_to_bv 64 p2) (Z_to_bv 64 (0 - p2)) xs6 xs7 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM GTOP SP16 XLO XHI PR ER.
    intros f. induction f as [|f IH]; intros until tlen; intros INV Hk Hf.
    - assert (k = 0)%Z by lia. subst k. pose proof INV as INV0. nd_open INV0. nd_env.
      nstep.
      uwalk ltac:(fun pc => lazymatch pc with
        | 0x5e320%Z => u_trap pc
        | 0x5e208%Z => first [ eapply evt_eq; [| eapply nd_4bc]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
        end).
    - pose proof INV as INV0. nd_open INV0. nd_env.
      nstep.
      uwalk ltac:(fun pc => lazymatch pc with
        | 0x5e320%Z => u_trap pc
        | 0x5e208%Z => first [ eapply evt_eq; [| eapply nd_4bc]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
        | 0x5e1d0%Z => first [ eapply evt_eq; [| eapply (IH (k - 1)%Z)]; [num_st_eq | exact INV | lia | lia] | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma nd_434 : forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xt3 xt4 xt5 xt6 mm len tlen,
    NDINV mm len tlen ->
    evt usegs POST (ND 0x5e180 xra xt0 xt1 xt2 (Z_to_bv 64 (p2 mod 4294967296)) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       (Z_to_bv 64 X) (Z_to_bv 64 e) (Z_to_bv 64 p2) (Z_to_bv 64 (0 - p2)) xs6 xs7 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM GTOP SP16 XLO XHI PR ER.
    intros until tlen. intros INV. pose proof INV as INV0. nd_open INV0. nd_env.
    assert (DS1 : IsData xs1) by exact I.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e320%Z => u_trap pc
      | 0x5e208%Z => first [ eapply evt_eq; [| eapply nd_4bc]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
      | 0x5e1d0%Z => first [ eapply evt_eq; [| eapply (nd_C (Z.to_nat len) len)]; [num_st_eq | exact INV | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Ltac nd_after_call MUc WMc MIc STc BIG :=
    rewrite !unsigned_lit in MUc, STc by lia; unfold P5U_STACK, LMU_STACK, LAFU_STACK, SHLU_STACK in MUc;
    lazymatch type of MUc with munch _ ?mo ?mn => transport_after_call usegs mo mn MUc WMc end;
    clear MUc WMc;
    repeat match goal with MI : mem_inv usegs ?m |- _ => lazymatch type of MIc with mem_inv _ m => fail | _ => clear MI end end;
    num_ret_pc.

  Lemma nd_418 : forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xt3 xt4 xt5 xt6 mm len tlen q2,
    NDINV mm len tlen -> (-2000000 <= q2 <= 2000000)%Z ->
    evt usegs POST (ND 0x5e164 xra xt0 xt1 xt2 (Z_to_bv 64 (p2 mod 4294967296)) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       (Z_to_bv 64 X) (Z_to_bv 64 e) (Z_to_bv 64 p2) (Z_to_bv 64 (0 - p2)) (Z_to_bv 64 q2) xs7 xt3 xt4 xt5 xt6 mm).
  Proof using HSHL ROOM GTOP SP16 XLO XHI PR ER.
    intros until q2. intros INV HQ. pose proof INV as INV0. nd_open INV0. nd_env.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    assert (DS1 : IsData xs1) by exact I.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e320%Z => u_trap pc
      | 0x5e180%Z => first [ eapply evt_eq; [| eapply nd_434]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
      | 0x5ec8c%Z => idtac
      end).
    -
      destruct (u64arr_of_u8arr usegs mm X bs XA XL) as (xws & XWL & XWA).
      pose proof HSHL as HM. unfold ndcu_shl_stmt, shlu_stmt_g in HM.
      eapply evt_cut.
      { eapply evt_eq; [| eapply HM with (X := X) (lo := lo) (ws := xws) (len := len)]; [num_st_eq | ..];
          rewrite ?unsigned_lit by lia; unfold SHLU_STACK;
          [ exact MI | exact ST | lia | split; [exact XWA| split; [exact XWL| split; [exact XN| lia]]] | lia | lia | lia ]. }
      cbv beta. intros ms' P. unfold bigu_post_g in P.
      destruct P as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & ws3 & len3 & -> & MUc & WMc & MIc & BIG & STc).
      clear XA XN XWA ST.
      nd_after_call MUc WMc MIc STc BIG.
      destruct BIG as (WA3 & WL3 & XN & LEN3).
      destruct (u8arr_of_u64arr usegs m3 X ws3 WA3 WL3) as (bs3 & XL3 & XA). clear WA3 WL3.
      rename MIc into MI. rename STc into ST.
      assert (INV3 : NDINV m3 len3 tlen) by nd_close.
      uwalk ltac:(fun pc => lazymatch pc with
        | 0x5e180%Z => first [ eapply evt_eq; [| eapply nd_434]; [num_st_eq | exact INV3] | fail 100 "cut" pc ]
        end).
    -
      destruct (u64arr_of_u8arr usegs mm FB tb TA TL) as (tws & TWL & TWA).
      replace (SP + -80)%Z with (FB + 496)%Z in TN by lia.
      pose proof HSHL as HM. unfold ndcu_shl_stmt, shlu_stmt_g in HM.
      eapply evt_cut.
      { eapply evt_eq; [| eapply HM with (X := FB) (lo := lo) (ws := tws) (len := tlen)]; [num_st_eq | ..];
          rewrite ?unsigned_lit by lia; unfold SHLU_STACK;
          [ exact MI | exact ST | lia | split; [exact TWA| split; [exact TWL| split; [exact TN| lia]]] | lia | lia | lia ]. }
      cbv beta. intros ms' P. unfold bigu_post_g in P.
      destruct P as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & ws3 & len3 & -> & MUc & WMc & MIc & BIG & STc).
      clear TA TN TWA ST.
      nd_after_call MUc WMc MIc STc BIG.
      destruct BIG as (WA3 & WL3 & TN & LEN3).
      destruct (u8arr_of_u64arr usegs m3 FB ws3 WA3 WL3) as (tb3 & TL3 & TA). clear WA3 WL3.
      replace (FB + 496)%Z with (SP + -80)%Z in TN by lia.
      rename MIc into MI. rename STc into ST.
      assert (INV3 : NDINV m3 len len3) by nd_close.
      uwalk ltac:(fun pc => lazymatch pc with
        | 0x5e180%Z => first [ eapply evt_eq; [| eapply nd_434]; [num_st_eq | exact INV3] | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma nd_40c : forall xra xt0 xt1 xt2 xs1 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xt3 xt4 xt5 xt6 mm len tlen q2,
    NDINV mm len tlen -> (-2000000 <= q2 <= 2000000)%Z ->
    evt usegs POST (ND 0x5e158 xra xt0 xt1 xt2 (Z_to_bv 64 (p2 mod 4294967296)) xs1 xa0 (Z_to_bv 64 (0 - e)) xa2 xa3 xa4 xa5 xa6 xa7
                       (Z_to_bv 64 X) (Z_to_bv 64 e) (Z_to_bv 64 p2) (Z_to_bv 64 (0 - p2)) (Z_to_bv 64 q2) xs7 xt3 xt4 xt5 xt6 mm).
  Proof using HP5 HSHL ROOM GTOP SP16 XLO XHI PR ER.
    intros until q2. intros INV HQ. pose proof INV as INV0. nd_open INV0. nd_env.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    assert (DS1 : IsData xs1) by exact I.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e320%Z => u_trap pc
      | 0x5e164%Z => first [ eapply evt_eq; [| eapply nd_418]; [num_st_eq | exact INV | lia] | fail 100 "cut" pc ]
      | 0x5e570%Z => idtac
      end).
    destruct (u64arr_of_u8arr usegs mm FB tb TA TL) as (tws & TWL & TWA).
    replace (SP + -80)%Z with (FB + 496)%Z in TN by lia.
    pose proof HP5 as HM. unfold ndcu_p5_stmt, p5u_stmt_g in HM.
    eapply evt_cut.
    { eapply evt_eq; [| eapply HM with (X := FB) (e := (0 - e)%Z) (lo := lo) (ws := tws) (len := tlen)]; [num_st_eq | ..];
        rewrite ?unsigned_lit by lia; unfold P5U_STACK, LMU_STACK, LAFU_STACK, NUMU_GTOP;
        [ exact MI | exact ST | lia | lia | Z.div_mod_to_equations; lia | split; [exact TWA| split; [exact TWL| split; [exact TN| lia]]] | lia | lia | lia ]. }
    cbv beta. intros ms' P. unfold bigu_post_g in P.
    destruct P as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & ws3 & len3 & -> & MUc & WMc & MIc & BIG & STc).
    clear TA TN TWA ST.
    nd_after_call MUc WMc MIc STc BIG.
    destruct BIG as (WA3 & WL3 & TN & LEN3).
    destruct (u8arr_of_u64arr usegs m3 FB ws3 WA3 WL3) as (tb3 & TL3 & TA). clear WA3 WL3.
    replace (FB + 496)%Z with (SP + -80)%Z in TN by lia.
    rename MIc into MI. rename STc into ST.
    assert (INV3 : NDINV m3 len len3) by nd_close.
    eapply evt_eq; [| eapply nd_418]; [num_st_eq | exact INV3 | lia].
  Qed.

  Definition NDINV0 (mm : mem) (len : Z) : Prop :=
    (exists j j0, rw_cells usegs mm FB [CB 8 j; CB 496 j0]) /\
    rw_cells usegs mm (SP + -72) ndcu_saved /\
    (exists bs, u8arr usegs mm X bs /\ length bs = 496%nat) /\
    rw_cells usegs mm (X + 496) [C2 (Z_to_bv 64 len)] /\ (0 <= len <= 62)%Z /\
    mem_inv usegs mm /\ munch W m0 mm /\ wmono usegs m0 mm /\ stk usegs mm lo FB.
  Ltac nd_open0 H :=
    let j := fresh "j" in let j0 := fresh "j" in let bs := fresh "bs" in
    destruct H as ((j & j0 & FR) & SAVED & (bs & XA & ?XL) & XN & ?LEN & MI & MU & WM & ST);
    unfold ndcu_saved in SAVED; unfold NDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK in MU.

  Lemma nd_3d8 : forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xt3 xt4 xt5 xt6 mm len t7,
    NDINV0 mm len -> (-1076 <= t7 <= 3020)%Z ->
    evt usegs POST (ND 0x5e124 xra xt0 xt1 xt2 (Z_to_bv 64 (p2 mod 4294967296)) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       (Z_to_bv 64 X) (Z_to_bv 64 e) (Z_to_bv 64 p2) (Z_to_bv 64 (0 - p2)) xs6 (Z_to_bv 64 t7) xt3 xt4 xt5 xt6 mm).
  Proof using HP5 HSHL HSET ROOM GTOP SP16 XLO XHI PR ER.
    intros until t7. intros INV H7. nd_open0 INV. nd_env.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    assert (DS6 : IsData xs6) by exact I. assert (DS1 : IsData xs1) by exact I.
    uwalk ltac:(fun pc => lazymatch pc with | 0xd0c68%Z => idtac end).
    peel_cell FR L0. rename FR into ZC.
    pose proof HSET as HS. unfold ndcu_memset_stmt, memsetZ_stmt_g in HS.
    eapply evt_cut.
    { eapply evt_eq; [| eapply HS with (D := (SP + -568)%Z) (C := 0%Z) (N := 496%Z) (junk := j0)]; [num_st_eq | ..];
        [ exact ZC | exact MI | lia | lia | lia | lia ]. }
    cbv beta. intros ms' P. unfold memsetZ_post_g in P.
    destruct P as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & -> & MUc & WMc & MIc & DSTc).
    clear ZC.
    lazymatch type of MUc with munch _ ?mo ?mn => transport_after_call usegs mo mn MUc WMc end.
    clear MUc WMc MI HS. rename MIc into MI. num_ret_pc.
    change (Z.to_nat 496) with 496%nat in DSTc.
    set (zs := repeat (Z_to_bv 8 (0 mod 256)) 496) in DSTc. clearbody zs.
    uwalk ltac:(fun pc => lazymatch pc with | 0x5e320%Z => u_trap pc | 0x5e158%Z => idtac end).
    peel_cell DSTc Z1. peel_cell DSTc TN. rename DSTc into TP.
    assert (L01 : rw_cells usegs m1 FB ([C8 xs6] ++ [CB 488 (firstn 488 zs)])).
    { apply num_rw_cells_app. split; [exact L0|]. cbn [cells_size csize Nat.add]. replace (FB + Z.of_nat 8)%Z with (SP + -568)%Z by lia. exact Z1. }
    destruct (rw_cells_forget usegs m1 FB _ L01) as [tb TB]. cbn [cells_size csize Nat.add app] in TB.
    pose proof (u8arr_of_rw_cells usegs _ _ _ _ TB) as TA.
    assert (TL : length tb = 496%nat) by (destruct TB as [[Hwf _] _]; cbn in Hwf; tauto).
    clear L0 Z1 L01 TB.
    assert (INV1 : NDINV m1 len 1) by nd_close.
    eapply evt_eq; [| eapply nd_40c]; [num_st_eq | exact INV1 | lia].
  Qed.

  Lemma nd_body : forall t0 t1 t2 a1 a4 a5 a6 a7 t3 t4 t5 t6 ws len,
    mem_inv usegs m0 -> stk usegs m0 lo SP -> bigint_at usegs m0 X ws len ->
    evt usegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) a1 (Z_to_bv 64 (p2 mod 4294967296)) (Z_to_bv 64 e) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 NDCU_ENTRY) fc None m0 (seg_rom usegs)).
  Proof using HP5 HSHL HSET ROOM GTOP SP16 XLO XHI PR ER.
    intros t0 t1 t2 a1 a4 a5 a6 a7 t3 t4 t5 t6 ws len MI ST (WA & WL & XN & LEN).
    unfold NDCU_ENTRY. nd_env.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl usegs m0) as WM. unfold NDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK in MU.
    set (m := m0) in MI, ST, WA, XN, MU at 2, WM at 2 |- * at 2. clearbody m.
    step.
    carve_frame 576%nat ST.
    apply (rw_cells_split_CB usegs m _ [] 576 junk [] [8;496;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 9 step.
    assert (DA1 : IsData a1) by exact I.
    destruct (u8arr_of_u64arr usegs _ X ws WA WL) as (bs & XL & XA). clear WA WL.
    peel_cell FR L0. peel_cell FR L1.
    assert (L01 : rw_cells usegs m1 FB ([CB 8 j] ++ [CB 496 j0])).
    { apply num_rw_cells_app. split; [exact L0|]. cbn [cells_size csize Nat.add]. replace (FB + Z.of_nat 8)%Z with (SP + -568)%Z by lia. exact L1. }
    cbn [app] in L01. clear L0 L1.
    replace (SP + -576 + 504)%Z with (SP + -72)%Z in FR by lia.
    assert (INV : NDINV0 m1 len).
    { split; [exists j, j0; exact L01|]. split; [exact FR|]. split; [exists bs; split; [exact XA | exact XL]|]. split; [exact XN|]. split; [lia|].
      split; [exact MI|]. split; [exact MU|]. split; [exact WM | exact ST]. }
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e320%Z => u_trap pc
      | 0x5e124%Z => first [ eapply evt_eq; [| eapply nd_3d8]; [num_st_eq | exact INV | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End NDCU.

Theorem ndcu_spec : ndcu_p5_stmt -> ndcu_shl_stmt -> ndcu_memset_stmt -> ndcu_stmt_g usegs NDCU_ENTRY NUMU_GTOP.
Proof.
  intros H5 HS HM. unfold ndcu_stmt_g. intros until len. intros MI ST ROOM GTOP SP16 BIG XLO XHI PR ER.
  eapply nd_body; eassumption.
Qed.
