(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber SjNumDiv.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_num_kit Sj_num_walk Sj_num_sp_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Definition sp_memset_stmt : Prop := memsetZ_stmt_g psegs 0xc5488.
Definition sp_pm_stmt : Prop := pm_stmt_g psegs 0x528dc SPATH_GTOP.
Definition sp_pdc_stmt : Prop := pdc_stmt_g psegs 0x535d0 SPATH_GTOP.
Definition sp_ndc_stmt : Prop := ndc_stmt_g psegs 0x53934 SPATH_GTOP.

Section SPDC.
  Hypothesis HSET : sp_memset_stmt.
  Hypothesis HPM : sp_pm_stmt.
  Hypothesis HPDC : sp_pdc_stmt.
  Hypothesis HNDC : sp_ndc_stmt.
  Variable E : spenv.
  Hypothesis OK : sp_ok E.
  Notation X := (q_SP E + -616)%Z.

  Lemma sp_a04 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc ->
    evt psegs (sp_post E) (SPS E 0x52850 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 (Z_to_bv 64 (q_OUT E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK.
    intros until mm. intros INV FRM. pose proof INV as INV0. sp_open INV. sp_env OK.
    assert (IsData xa0) by exact I. assert (IsData xa1) by exact I.
    walk ltac:(fun pc => lazymatch pc with
      | 0x52868%Z => first [ eapply sp_a1c; [exact OK | exact INV0 | exact FRM] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma sp_99c : forall (IP IL FPT FL : Z) xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPINV2 E mm IP IL FPT FL -> frm0 xfc -> pm_spans_ok (q_A E) (q_txt E) IP IL FPT FL ->
    evt psegs (sp_post E) (SPS E 0x527e8 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 (Z_to_bv 64 (q_OUT E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros until mm. intros INV FRM SPN. sp_open2 INV. sp_env OK.
    assert (LO0 : (0 <= q_lo E)%Z) by (destruct ST as [? _]; assumption).
    assert (DS0 : IsData xs0) by exact I. assert (DS2 : IsData xs2) by exact I.
    walk ltac:(fun pc => lazymatch pc with | 0xc5488%Z => idtac end).

    lazymatch type of BGN with rw_cells _ ?mc _ [CB 2 ?jn] => lazymatch type of BGP with rw_cells _ _ _ [CB 6 ?jp] =>
      lazymatch type of BG with rw_cells _ _ _ [CB 496 ?jl] =>
        assert (B2 : rw_cells psegs mc (q_SP E + -120) ([CB 2 jn] ++ [CB 6 jp]));
        [ apply num_rw_cells_app; split; [exact BGN|]; cbn [cells_size csize Nat.add];
          replace (q_SP E + -120 + Z.of_nat 2)%Z with (q_SP E + -118)%Z by lia; exact BGP |];
        assert (B3 : rw_cells psegs mc (q_SP E + -616) ([CB 496 jl] ++ ([CB 2 jn] ++ [CB 6 jp])));
        [ apply num_rw_cells_app; split; [exact BG|]; cbn [cells_size csize Nat.add];
          replace (q_SP E + -616 + Z.of_nat 496)%Z with (q_SP E + -120)%Z by lia; exact B2 |]
      end end end.
    clear BG BGN BGP B2. cbn [app] in B3.
    destruct (rw_cells_forget psegs _ _ _ B3) as [jb BGALL]. cbn [cells_size csize Nat.add] in BGALL. clear B3.
    pose proof HSET as HS. unfold sp_memset_stmt, memsetZ_stmt_g in HS.
    eapply evt_cut.
    { eapply evt_eq; [| eapply HS with (D := X) (C := 0%Z) (N := 504%Z) (junk := jb); [exact BGALL | exact MI | lia | lia | lia | lia]].
      num_st_eq. }
    cbv beta. intros ms' P. unfold memsetZ_post_g in P.
    destruct P as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & -> & MUc & WMc & MIc & DSTc).
    clear BGALL.
    lazymatch type of MUc with munch _ ?mo ?mn => transport_after_call psegs mo mn MUc WMc end.
    clear MUc WMc MI HS.
    num_ret_pc.
    change (Z.to_nat 504) with 504%nat in DSTc.
    apply (rw_cells_split_CB psegs m3 _ [] 504 _ [] [496;2;6]%nat) in DSTc; [|reflexivity].
    cbn [mk_CB_cells app] in DSTc.
    lazymatch type of DSTc with rw_cells _ _ _ [CB 496 ?b0; CB 2 ?b1; CB 6 ?b2] =>
      change [CB 496 b0; CB 2 b1; CB 6 b2] with ([CB (8 * 62) b0] ++ [CB 2 (le2 (Z_to_bv 64 0))] ++ [CB 6 b2]) in DSTc end.
    apply num_rw_cells_app in DSTc. destruct DSTc as [BG R]. apply num_rw_cells_app in R. destruct R as [BGN BGP].
    cbn [cells_size csize Nat.add Nat.mul] in BGN, BGP.
    replace (q_SP E + -616 + Z.of_nat 496)%Z with (X + 496)%Z in BGN by lia.
    replace (q_SP E + -616 + Z.of_nat 496 + Z.of_nat 2)%Z with (q_SP E + -118)%Z in BGP by lia.
    destruct (u64arr_of_rw_cells psegs m3 _ 62 _ BG) as (ws & WL & WA). clear BG.
    apply num_cb2_c2 in BGN.
    walk ltac:(fun pc => lazymatch pc with | 0x528dc%Z => idtac end).

    destruct (rw_cells_forget psegs _ _ _ DGC) as [jd DGC']. cbn [cells_size csize Nat.add] in DGC'. clear DGC.
    replace (q_SP E + -112)%Z with (X + 504)%Z in DGC' by lia.
    replace (q_SP E + -656)%Z with (X - 40)%Z in SPANS by lia.
    pose proof HPM as HP. unfold sp_pm_stmt, pm_stmt_g in HP.
    eapply evt_cut.
    { eapply evt_eq; [| eapply HP with (X := X) (A := q_A E) (IP := IP) (IL := IL) (FPT := FPT) (FL := FL) (lo := q_lo E)
                            (ws := ws) (len := 0%Z) (txt := q_txt E) (jd := jd)];
        [ unfold PM_MAXD; num_st_eq | .. ]; rewrite ?unsigned_lit by lia; unfold PM_STACK, SPATH_GTOP, NUM_TXT_MAX;
        [ exact MIc | exact ST | lia | lia | split; [exact WA| split; [exact WL| split; [exact BGN| lia]]] | lia
        | exact DGC' | exact SPANS | exact TXT | lia | lia | exact SPN ]. }
    cbv beta. intros ms' P. unfold pm_post_g in P.
    destruct P as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & ws4 & len4 & dg4 & -> & MUc & WMc & MI4 & BIG4 & DG4 & SPANS4 & ST4).
    rewrite !unsigned_lit in MUc, ST4 by lia. unfold PM_STACK in MUc.
    clear WA BGN DGC' SPANS ST.
    lazymatch type of MUc with munch _ ?mo ?mn => transport_after_call psegs mo mn MUc WMc end.
    clear MUc WMc MIc HP.
    num_ret_pc.
    destruct BIG4 as (WA & WL4 & BGN & LEN4).
    destruct (rw_cells_forget psegs _ _ _ DG4) as [jd4 DGC]. cbn [cells_size csize Nat.add] in DGC. clear DG4.
    replace (X + 504)%Z with (q_SP E + -112)%Z in DGC by lia.
    replace (X - 40)%Z with (q_SP E + -656)%Z in SPANS4 by lia.
    walk ltac:(fun pc => lazymatch pc with | 0x535d0%Z => idtac | 0x53934%Z => idtac end).
    -
      pose proof HNDC as HD. unfold sp_ndc_stmt, ndc_stmt_g in HD.
      eapply evt_cut.
      { eapply evt_eq; [| eapply HD with (X := X) (lo := q_lo E) (ws := ws4) (len := len4)];
          [ num_st_eq | .. ]; rewrite ?unsigned_lit by lia; unfold NDC_STACK, P5_STACK, LM_STACK, SPATH_GTOP;
          [ eassumption | exact ST4 | lia | lia | split; [exact WA| split; [exact WL4| split; [exact BGN| lia]]] | lia | first [eassumption | (rewrite bv_swrap32; apply swrap32_range)] ]. }
      cbv beta. intros ms' P. unfold ndc_post_g in P.
      destruct P as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & ws5 & len5 & -> & MUc & WMc & MI5 & BIG5 & ST5).
      rewrite !unsigned_lit in MUc, ST5 by lia. unfold NDC_STACK, P5_STACK, LM_STACK in MUc.
      clear WA BGN ST4.
      lazymatch type of MUc with munch _ ?mo ?mn => transport_after_call psegs mo mn MUc WMc end.
      clear MUc WMc HD. repeat match goal with MIo : mem_inv psegs ?mo |- _ => lazymatch mo with m5 => fail | _ => clear MIo end end.
      num_ret_pc.
      destruct BIG5 as (WA & WL5 & BGN & LEN5).
      apply rw_cells_of_u64arr in WA. rewrite WL5 in WA.
      replace (X + 496)%Z with (q_SP E + -120)%Z in BGN by lia.
      rename ST5 into ST. rename SPANS4 into SPANS. rename WA into BG. rename MI5 into MI.
      eapply sp_a04; [sp_close | eassumption].
    -
      pose proof HPDC as HD. unfold sp_pdc_stmt, pdc_stmt_g in HD.
      eapply evt_cut.
      { eapply evt_eq; [| eapply HD with (X := X) (lo := q_lo E) (ws := ws4) (len := len4)];
          [ num_st_eq | .. ]; rewrite ?unsigned_lit by lia; unfold PDC_STACK, P5_STACK, LM_STACK, SPATH_GTOP;
          [ eassumption | exact ST4 | lia | lia | split; [exact WA| split; [exact WL4| split; [exact BGN| lia]]] | lia | first [eassumption | (rewrite bv_swrap32; apply swrap32_range)] ]. }
      cbv beta. intros ms' P. unfold pdc_post_g in P.
      destruct P as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & ws5 & len5 & -> & MUc & WMc & MI5 & BIG5 & ST5).
      rewrite !unsigned_lit in MUc, ST5 by lia. unfold PDC_STACK, P5_STACK, LM_STACK in MUc.
      clear WA BGN ST4.
      lazymatch type of MUc with munch _ ?mo ?mn => transport_after_call psegs mo mn MUc WMc end.
      clear MUc WMc HD. repeat match goal with MIo : mem_inv psegs ?mo |- _ => lazymatch mo with m5 => fail | _ => clear MIo end end.
      num_ret_pc.
      destruct BIG5 as (WA & WL5 & BGN & LEN5).
      apply rw_cells_of_u64arr in WA. rewrite WL5 in WA.
      replace (X + 496)%Z with (q_SP E + -120)%Z in BGN by lia.
      rename ST5 into ST. rename SPANS4 into SPANS. rename WA into BG. rename MI5 into MI.
      zstep.
      eapply sp_a04; [sp_close | eassumption].
  Qed.

  Ltac dc_measure x M k L :=
    lazymatch goal with
    | |- (bv_unsigned (Z_to_bv 64 ?T) <= _)%Z =>
        let D := fresh "D" in
        pose proof (L x M k ltac:(lia) ltac:(lia) ltac:(lia)) as D;
        rewrite unsigned_lit by lia; lia
    end.

  Lemma sp_LC : forall (f : nat) (xa1 : word) (IP IL FPT FL : Z) xra xt0 xt1 xt2 xs0 xs1 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPINV2 E mm IP IL FPT FL -> frm0 xfc -> pm_spans_ok (q_A E) (q_txt E) IP IL FPT FL -> (bv_unsigned xa1 <= Z.of_nat f)%Z ->
    evt psegs (sp_post E) (SPS E 0x527d4 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 14757395258967641293) xa1 (Z_to_bv 64 99) xa3 xa4 xa5 xa6 xa7
                               xs2 xs3 (Z_to_bv 64 (q_OUT E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM SPN Hf;
      pose proof (bv_unsigned_in_range 64 xa1) as R1; unfold bv_modulus in R1; cbn in R1.
    - nstep. walk ltac:(fun pc => lazymatch pc with
        | 0x527e8%Z => first [ eapply (sp_99c IP IL FPT FL); [exact INV | exact FRM | exact SPN] | fail 100 "cut" pc ]
        end).
    - nstep. walk ltac:(fun pc => lazymatch pc with
        | 0x527e8%Z => first [ eapply (sp_99c IP IL FPT FL); [exact INV | exact FRM | exact SPN] | fail 100 "cut" pc ]
        | 0x527d4%Z => first [ eapply evt_eq; [| eapply (IH _ IP IL FPT FL)];
                               [ num_st_eq | exact INV | exact FRM | exact SPN | dc_measure (bv_unsigned xa1) 14757395258967641293%Z 3%Z divstep_lt ]
                             | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma sp_964 : forall (xa1 : word) (IP IL FPT FL : Z) xra xt0 xt1 xt2 xs0 xs1 xa0 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPINV2 E mm IP IL FPT FL -> frm0 xfc -> pm_spans_ok (q_A E) (q_txt E) IP IL FPT FL ->
    evt psegs (sp_post E) (SPS E 0x527b0 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 (Z_to_bv 64 (q_OUT E)) xa3 xa4 xa5 xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros until mm. intros INV FRM SPN.
    walk ltac:(fun pc => lazymatch pc with
      | 0x527e8%Z => first [ eapply (sp_99c IP IL FPT FL); [exact INV | exact FRM | exact SPN] | fail 100 "cut" pc ]
      | 0x527d4%Z => first [ eapply (sp_LC (Z.to_nat (bv_unsigned xa1)) xa1 IP IL FPT FL); [exact INV | exact FRM | exact SPN | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma sp_LB : forall (f : nat) (xa7 : word) (IP IL FPT FL : Z) xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPINV2 E mm IP IL FPT FL -> frm0 xfc -> pm_spans_ok (q_A E) (q_txt E) IP IL FPT FL -> (bv_unsigned xa7 <= Z.of_nat f)%Z ->
    evt psegs (sp_post E) (SPS E 0x5278c xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 (Z_to_bv 64 (q_OUT E)) (Z_to_bv 64 2951479051793528259) (Z_to_bv 64 624) xa5 xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM SPN Hf;
      pose proof (bv_unsigned_in_range 64 xa7) as R7; unfold bv_modulus in R7; cbn in R7;
      pose proof (shr_le (bv_unsigned xa7) 4 ltac:(lia) ltac:(lia)) as S4.
    - nstep. walk ltac:(fun pc => lazymatch pc with
        | 0x527b0%Z => first [ eapply (sp_964 _ IP IL FPT FL); [exact INV | exact FRM | exact SPN] | fail 100 "cut" pc ]
        end).
    - nstep. walk ltac:(fun pc => lazymatch pc with
        | 0x527b0%Z => first [ eapply (sp_964 _ IP IL FPT FL); [exact INV | exact FRM | exact SPN] | fail 100 "cut" pc ]
        | 0x5278c%Z => first [ eapply evt_eq; [| eapply (IH _ IP IL FPT FL)];
                               [ num_st_eq | exact INV | exact FRM | exact SPN
                               | dc_measure (bv_unsigned xa7) 2951479051793528259%Z 2%Z divstep2_lt ]
                             | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma sp_92c : forall (xa7 : word) (IP IL FPT FL : Z) xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa3 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPINV2 E mm IP IL FPT FL -> frm0 xfc -> pm_spans_ok (q_A E) (q_txt E) IP IL FPT FL ->
    evt psegs (sp_post E) (SPS E 0x52778 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 (Z_to_bv 64 (q_OUT E)) xa3 xa4 xa5 xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros until mm. intros INV FRM SPN. pose proof INV as INV0. sp_open2 INV0.
    walk ltac:(fun pc => lazymatch pc with
      | 0x527b0%Z => first [ eapply (sp_964 _ IP IL FPT FL); [exact INV | exact FRM | exact SPN] | fail 100 "cut" pc ]
      | 0x5278c%Z => first [ eapply (sp_LB (Z.to_nat (bv_unsigned xa7)) xa7 IP IL FPT FL); [exact INV | exact FRM | exact SPN | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma sp_LA : forall (f : nat) (xa7 : word) (IP IL FPT FL : Z) xra xt0 xt1 xt2 xs0 xs1 xa0 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPINV2 E mm IP IL FPT FL -> frm0 xfc -> pm_spans_ok (q_A E) (q_txt E) IP IL FPT FL -> (bv_unsigned xa7 <= Z.of_nat f)%Z ->
    evt psegs (sp_post E) (SPS E 0x52764 xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 3777893186295716171) (Z_to_bv 64 (q_OUT E)) (Z_to_bv 64 99999999) xa4 xa5 xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM SPN Hf;
      pose proof (bv_unsigned_in_range 64 xa7) as R7; unfold bv_modulus in R7; cbn in R7.
    - nstep. walk ltac:(fun pc => lazymatch pc with
        | 0x52778%Z => first [ eapply (sp_92c _ IP IL FPT FL); [exact INV | exact FRM | exact SPN] | fail 100 "cut" pc ]
        end).
    - nstep. walk ltac:(fun pc => lazymatch pc with
        | 0x52778%Z => first [ eapply (sp_92c _ IP IL FPT FL); [exact INV | exact FRM | exact SPN] | fail 100 "cut" pc ]
        | 0x52764%Z => first [ eapply evt_eq; [| eapply (IH _ IP IL FPT FL)];
                               [ num_st_eq | exact INV | exact FRM | exact SPN
                               | dc_measure (bv_unsigned xa7) 3777893186295716171%Z 11%Z divstep_lt ]
                             | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma sp_8fc : forall (xa7 : word) (IP IL FPT FL : Z) xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa3 xa4 xa5 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    SPINV2 E mm IP IL FPT FL -> frm0 xfc -> pm_spans_ok (q_A E) (q_txt E) IP IL FPT FL ->
    evt psegs (sp_post E) (SPS E 0x52748 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 (Z_to_bv 64 (q_OUT E)) xa3 xa4 xa5 xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros until mm. intros INV FRM SPN. pose proof INV as INV0. sp_open2 INV0.
    walk ltac:(fun pc => lazymatch pc with
      | 0x52778%Z => first [ eapply (sp_92c _ IP IL FPT FL); [exact INV | exact FRM | exact SPN] | fail 100 "cut" pc ]
      | 0x52764%Z => first [ eapply (sp_LA (Z.to_nat (bv_unsigned xa7)) xa7 IP IL FPT FL); [exact INV | exact FRM | exact SPN | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End SPDC.
