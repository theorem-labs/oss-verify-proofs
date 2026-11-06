(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Od_defs Od_plus Od_head Od_loop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section Begin.
  Variable E : odenv.
  Hypothesis OK : od_ok E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation n := (o_n E).

  Definition low_cells (E : odenv) (v192 v200 v224 : Z) (j0 j8 j16 j56 j64 j72 j80 j88 j128 j136 j232 : list byte) : list cell :=
    [CB 8 j0; CB 8 j8; CB 8 j16] ++ fr_k24 ++ [CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88] ++ fr_k96 ++ [CB 8 j128; CB 8 j136]
    ++ [C8 (wz 0xffffffff80808080); C8 (wz 0xffffffffcfcfcfd0); C8 (wz 0x46464646); C8 (wz 0x736c6166); C8 (wz (o_COPY E)); C8 (wz 0x65757274);
        C8 (wz v192); C8 (wz v200); C8 (wz 0x1100000000); C8 (wz 0x6c6c756e); C8 (wz v224); CB 8 j232].

  Definition consts_post (vs0 vs1 vs7 v192 : Z) (xF : bvmap 5 word) (xfc : bv 32) (m : mem) : machine_state -> Prop :=
    fun ms' => exists xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs8 xt3 xt4 xt5 (m' : mem) j0 j8 j16 j56 j64 j72 j80 j88 j128 j136 j232 xs5,
      ms' = MS (mkR (Z_to_bv 64 1) (Z_to_bv 64 (FR E)) (o_gp E) (o_tp E) xt0 xt1 xt2
                    (Z_to_bv 64 vs0) (Z_to_bv 64 vs1) (Z_to_bv 64 vs1) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                    (Z_to_bv 64 0x640001) (Z_to_bv 64 (o_act E)) (Z_to_bv 64 91) xs5 xs6 (Z_to_bv 64 vs7) xs8
                    (Z_to_bv 64 10) (Z_to_bv 64 125) (Z_to_bv 64 122) xt3 xt4 xt5 (Z_to_bv 64 v192))
               xF (Z_to_bv 64 0x27654) xfc None m' (seg_rom psegs)
      /\ munch [(FR E, bv_unsigned (o_sp E) + -272)%Z] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ rw_cells psegs m' (FR E) (low_cells E v192 (vs1 - 1) vs1 j0 j8 j16 j56 j64 j72 j80 j88 j128 j136 j232).

  Lemma od_consts : forall vs0 vs1 vs7 v192 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1
      j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 j16 j17 j18 j19 j20 j21 j23 j25 j26 j27 j28 j29,
    mem_inv psegs m1 -> (0 <= vs1 <= 1)%Z ->
    rw_cells psegs m1 (FR E)
      [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; CB 8 j7; CB 8 j8; CB 8 j9; CB 8 j10; CB 8 j11; CB 8 j12; CB 8 j13; CB 8 j14;
       CB 8 j15; CB 8 j16; CB 8 j17; CB 8 j18; CB 8 j19; CB 8 j20; CB 8 j21; C8 (Z_to_bv 64 (o_COPY E)); CB 8 j23; C8 (Z_to_bv 64 v192); CB 8 j25; CB 8 j26;
       CB 8 j27; CB 8 j28; CB 8 j29] ->
    evt psegs (consts_post vs0 vs1 vs7 v192 xF xfc m1)
      (MS (mkR (Z_to_bv 64 1) (Z_to_bv 64 (FR E)) (o_gp E) (o_tp E) xt0 xt1 xt2 (Z_to_bv 64 vs0) (Z_to_bv 64 vs1) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               xs2 (Z_to_bv 64 (o_act E)) (Z_to_bv 64 91) xs5 xs6 (Z_to_bv 64 vs7) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
          xF (Z_to_bv 64 0x2756c) xfc None m1 (seg_rom psegs)).
  Proof using OK.
    intros until j29. intros MI VS FRL.
    od_env OK.
    pose proof (munch_refl [(FR E, bv_unsigned (o_sp E) + -272)%Z] m1) as MU. pose proof (wmono_refl psegs m1) as WM.
    set (mm0 := m1) in MU at 1, WM at 1 |- * at 1.

    zstep. zstep.

    do 18 zstep.

    zstep. lstep. zstep. lstep. zstep. lstep. zstep. lstep. zstep. zstep. zstep.

    zstep. lstep. zstep. lstep. zstep. lstep. zstep. lstep. zstep. lstep. zstep. lstep. zstep. lstep.

    zstep. lstep. zstep. zstep. lstep. zstep. lstep. zstep. zstep. lstep.

    zstep. zstep. zstep.
    apply evt_done. unfold consts_post. do 28 eexists.
    split; [cbv delta [mkR]; reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    eapply rw_cells_eq; [eassumption|]. unfold low_cells, fr_k24, fr_k96, K104, K112. cbn [app]. od_cells_eq.
  Qed.

  Lemma od_low_split : forall (m : mem) v192 v200 v224 v232 j0 j8 j16 j56 j64 j72 j80 j88 j128 j136,
    rw_cells psegs m (FR E)
      ([CB 8 j0; CB 8 j8; CB 8 j16] ++ fr_k24 ++ [CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88] ++ fr_k96 ++ [CB 8 j128; CB 8 j136]
       ++ fr_k144 E v192 v200 v224 v232) ->
    rw_cells psegs m (FR E) [CB 8 j0; CB 8 j8; CB 8 j16] /\
    rw_cells psegs m (bv_unsigned (o_sp E) + -488)%Z fr_k24 /\
    rw_cells psegs m (bv_unsigned (o_sp E) + -456)%Z [CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88] /\
    rw_cells psegs m (bv_unsigned (o_sp E) + -416)%Z fr_k96 /\
    rw_cells psegs m (bv_unsigned (o_sp E) + -384)%Z [CB 8 j128; CB 8 j136] /\
    rw_cells psegs m (bv_unsigned (o_sp E) + -368)%Z (fr_k144 E v192 v200 v224 v232).
  Proof.
    intros m v192 v200 v224 v232 j0 j8 j16 j56 j64 j72 j80 j88 j128 j136 H.
    apply rw_cells_app in H. destruct H as [H0 H]. cbn [cells_size csize Nat.add] in H.
    replace (FR E + Z.of_nat 24)%Z with (bv_unsigned (o_sp E) + -488)%Z in H by lia.
    apply rw_cells_app in H. destruct H as [H1 H]. unfold fr_k24 at 1 in H. cbn [cells_size csize Nat.add] in H.
    replace (bv_unsigned (o_sp E) + -488 + Z.of_nat 32)%Z with (bv_unsigned (o_sp E) + -456)%Z in H by lia.
    apply rw_cells_app in H. destruct H as [H2 H]. cbn [cells_size csize Nat.add] in H.
    replace (bv_unsigned (o_sp E) + -456 + Z.of_nat 40)%Z with (bv_unsigned (o_sp E) + -416)%Z in H by lia.
    apply rw_cells_app in H. destruct H as [H3 H]. unfold fr_k96 at 1 in H. cbn [cells_size csize Nat.add] in H.
    replace (bv_unsigned (o_sp E) + -416 + Z.of_nat 32)%Z with (bv_unsigned (o_sp E) + -384)%Z in H by lia.
    apply rw_cells_app in H. destruct H as [H4 H]. cbn [cells_size csize Nat.add] in H.
    replace (bv_unsigned (o_sp E) + -384 + Z.of_nat 16)%Z with (bv_unsigned (o_sp E) + -368)%Z in H by lia.
    split; [exact H0|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4| exact H].
  Qed.

  Hypothesis ARM_STR  : arm_stmt E 0x27870.
  Hypothesis ARM_BOOL : arm_stmt E 0x27898.
  Hypothesis ARM_ARR  : arm_stmt E 0x276d4.
  Hypothesis ARM_I64  : arm_stmt E 0x27734.
  Hypothesis ARM_DBL  : arm_stmt E 0x277e0.
  Hypothesis ARM_OBJ  : arm_stmt E 0x27924.
  Hypothesis ARM_U64  : arm_stmt E 0x2794c.
  Hypothesis ARM_RAW  : arm_stmt E 0x27a64.
  Hypothesis ARM_NULL : arm_stmt E 0x27a04.
  Hypothesis ARM_NEST : arm_stmt E 0x27710.

  Ltac cells_split_at H k :=
    lazymatch type of H with
    | rw_cells _ _ _ ?cs =>
        let l1 := eval cbv beta iota delta [firstn] in (firstn k cs) in
        let l2 := eval cbv beta iota delta [skipn] in (skipn k cs) in
        change cs with (l1 ++ l2) in H
    end.

  Definition OD_REST (m1 : mem) : Prop :=
    rw_cells psegs m1 (FR_PA E) (od_parser_cells E) /\
    rw_cells psegs m1 (bv_unsigned (o_sp E) + -152)%Z (o_hi E) /\
    rw_cells psegs m1 (o_IMPL E) (dpi_cells E) /\
    (exists ws, u32arr psegs m1 (o_IDX E) ws /\ idx_ok E ws) /\
    bytes_at psegs m1 (o_BUF E) (padded_bytes (o_bs E)) /\
    wr_at psegs m1 (o_SB E) (o_CAP E) /\
    (exists v0 v1 v2 v3 v5 v6 v7 v8 v9, rw_cells psegs m1 OD_DPI_VPTR (od_vt_cells v0 v1 v2 v3 v5 v6 v7 v8 v9)) /\
    rw_cells psegs m1 OD_GOT_TABS [C8 (wz 0x137e8); C8 (wz 0x14878); C8 (wz 0x138e8)] /\
    mem_inv psegs m1 /\ munch (od_W E) (o_m0 E) m1 /\ wmono psegs (o_m0 E) m1 /\
    stk psegs m1 (o_lo E) (FR E).

  Ltac rest_open H :=
    let ws := fresh "ws" in
    let v0 := fresh "v0" in let v1 := fresh "v1" in let v2 := fresh "v2" in let v3 := fresh "v3" in let v5 := fresh "v5" in
    let v6 := fresh "v6" in let v7 := fresh "v7" in let v8 := fresh "v8" in let v9 := fresh "v9" in
    destruct H as (PARS & FRHI & DPI & (ws & IDXA & IDXL & IDXF) & BUFRO & SBW & (v0 & v1 & v2 & v3 & v5 & v6 & v7 & v8 & v9 & VT) & GOT & MI & MU & WM & ST);
    unfold od_parser_cells in PARS; unfold dpi_cells in DPI; unfold od_vt_cells, OD_DPI_VPTR in VT; unfold OD_GOT_TABS in GOT; unfold od_W in MU;
    unfold wz in PARS, DPI, VT, GOT;
    lazymatch type of BUFRO with
    | bytes_at _ _ _ (padded_bytes ?bs) => let PBL := fresh "PBL" in pose proof (padded_bytes_blen bs) as PBL
    end.
  Ltac rest_close :=
    unfold OD_REST, od_parser_cells, dpi_cells, od_vt_cells, od_W, OD_DPI_VPTR, OD_GOT_TABS, idx_ok;
    split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
    split; [ eexists; split; [eassumption| split; eassumption] | ];
    split; [eassumption|]; split; [eassumption|];
    split; [ do 9 eexists; eassumption | ];
    split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption.

  Lemma ODINVg_intro : forall (m : mem) st v192 v200 v224 v232 j0 j8 j16 j56 j64 j72 j80 j88 j128 j136 j289 j300,
    rw_cells psegs m (FR E)
      ([CB 8 j0; CB 8 j8; CB 8 j16] ++ fr_k24 ++ [CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88] ++ fr_k96 ++ [CB 8 j128; CB 8 j136]
       ++ fr_k144 E v192 v200 v224 v232) ->
    rw_cells psegs m (FR_IT E) (iter_cells E st j289 j300) ->
    OD_REST m ->
    ODINVg E v192 v200 v224 v232 st m.
  Proof.
    intros m st v192 v200 v224 v232 j0 j8 j16 j56 j64 j72 j80 j88 j128 j136 j289 j300 LOW ITER REST.
    apply od_low_split in LOW. destruct LOW as (H0 & H1 & H2 & H3 & H4 & H5).
    destruct REST as (PARS & FRHI & DPI & IDX & BUFRO & SBW & VT & GOT & MI & MU & WM & ST).
    unfold ODINVg.
    split; [do 3 eexists; exact H0|]. split; [exact H1|]. split; [do 5 eexists; exact H2|]. split; [exact H3|]. split; [do 2 eexists; exact H4|].
    split; [exact H5|]. split; [do 2 eexists; exact ITER|].
    split; [exact PARS|]. split; [exact FRHI|]. split; [exact DPI|]. split; [exact IDX|]. split; [exact BUFRO|]. split; [exact SBW|].
    split; [exact VT|]. split; [exact GOT|]. split; [exact MI|]. split; [exact MU|]. split; [exact WM| exact ST].
  Qed.

  Lemma od_invalid : forall (Q : machine_state -> Prop) st xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1
      j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 j16 j17 j18 j19 j20 j21 j23 j24 j25 j26 j27 j28 j29 j289 j300,
    rw_cells psegs m1 (FR E)
      [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; CB 8 j7; CB 8 j8; CB 8 j9; CB 8 j10; CB 8 j11; CB 8 j12; CB 8 j13; CB 8 j14;
       CB 8 j15; CB 8 j16; CB 8 j17; CB 8 j18; CB 8 j19; CB 8 j20; CB 8 j21; C8 (Z_to_bv 64 (o_COPY E)); CB 8 j23; CB 8 j24; CB 8 j25; CB 8 j26;
       CB 8 j27; CB 8 j28; CB 8 j29] ->
    rw_cells psegs m1 (FR_IT E) (iter_cells E st j289 j300) ->
    OD_REST m1 -> frm0 xfc -> od_exit_k E Q ->
    evt psegs Q (MS (mkR (Z_to_bv 64 1) (Z_to_bv 64 (FR E)) (o_gp E) (o_tp E) xt0 xt1 xt2 (Z_to_bv 64 0) (Z_to_bv 64 0) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         xs2 (Z_to_bv 64 (o_act E)) (Z_to_bv 64 91) xs5 xs6 (Z_to_bv 64 0) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                    xF (Z_to_bv 64 0x27564) xfc None m1 (seg_rom psegs)).
  Proof using OK.
    intros until j300. intros LOW ITER REST FRM KX.
    od_env OK. pose proof KX as KX0. unfold od_exit_k, OD_EXIT in KX0.
    rest_open REST. unfold iter_cells in ITER. unfold wz in ITER.
    assert (LO0 : (0 <= o_lo E)%Z) by (destruct ST as [? _]; assumption).

    zstep. lstep.

    eapply evt_cut.
    { od_cur_mem ltac:(fun mm => eapply (od_consts 0 0 0 1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm); [assumption| lia| eassumption]). }
    cbv beta. intros ms' P. unfold consts_post in P.
    destruct P as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q22 & q24 & q28 & q29 & q30 & m3 & k0 & k8 & k16 & k56 & k64 & k72 & k80 & k88 & k128 & k136 & k232
                   & q21 & -> & MUc & WMc & MIc & LOWc).
    clear LOW.
    lazymatch type of ITER with rw_cells _ ?m _ _ => transport_after_call psegs m m3 MUc WMc end.
    clear MUc WMc.
    unfold low_cells, fr_k24, fr_k96, wz in LOWc. cbn [app] in LOWc.

    zstep. lstep. zstep. if_true. zstep. zstep. if_false. zstep. zstep. zstep. zstep.

    eapply evt_eq; [| eapply (od_disp_err Q (o_act E)); [exact ACT| eassumption| intros xa0' xa1' xa2' xa3' xs5' xs6']]; [unfold OD_DISP; od_st_eq|].
    unfold OD_PLUS.

    zstep. zstep. if_true. zstep. zstep. zstep. lstep. zstep. if_true. zstep. zstep. if_true.
    eapply evt_eq; [| eapply (KX0 st 1%Z (-1)%Z 0%Z 1%Z); [exact FRM|]]; [od_st_eq|].
    eapply ODINVg_intro; [| unfold iter_cells, wz; eassumption| rest_close].
    eapply rw_cells_eq; [eassumption|]. unfold fr_k24, fr_k96, fr_k144, K104, K112. cbn [app]. od_cells_eq.
  Qed.

  Theorem od_iterate : forall (Q : machine_state -> Prop) xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    OD_PRE E m1 -> frm0 xfc -> o_m0 E = m1 -> od_exit_k E Q ->
    evt psegs Q (MS (mkR xra (Z_to_bv 64 (FR E)) (o_gp E) (o_tp E) xt0 xt1 xt2 xs0 (Z_to_bv 64 (o_BUF E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         (Z_to_bv 64 (o_len E)) (Z_to_bv 64 (o_act E)) xs4 (Z_to_bv 64 (o_COPY E)) xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                    xF (Z_to_bv 64 OD_ITER) xfc None m1 (seg_rom psegs)).
  Proof using OK ARM_STR ARM_BOOL ARM_ARR ARM_I64 ARM_DBL ARM_OBJ ARM_U64 ARM_RAW ARM_NULL ARM_NEST.
    intros Q xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1 PRE FRM EM0 KX.
    destruct PRE as ((junk & FRJ) & PARS & FRHI & DPI & (ws & IDXA & IDXL & IDXF) & BUFRO & SBW & (v0 & v1 & v2 & v3 & v5 & v6 & v7 & v8 & v9 & VT) & GOT & MI & ST).
    od_env OK. unfold OD_ITER.
    unfold od_parser_cells in PARS. unfold dpi_cells in DPI. unfold od_vt_cells, OD_DPI_VPTR in VT. unfold OD_GOT_TABS in GOT.
    unfold wz in PARS, DPI, VT, GOT.
    pose proof (padded_bytes_blen bs) as PBL.
    pose proof (munch_refl (od_W E) m1) as MU. pose proof (wmono_refl psegs m1) as WM. unfold od_W in MU.
    rewrite <- EM0 in MU at 1. rewrite <- EM0 in WM at 1.
    assert (LO0 : (0 <= o_lo E)%Z) by (destruct ST as [? _]; assumption).

    apply (rw_cells_split_CB psegs m1 _ [] 304 junk []
             [8;8;8; 8;8;8;8; 8;8;8;8;8; 8;8;8;8; 8;8; 8;8;8;8;8;8;8;8;8;8;8;8; 8;8;8;8; 8; 8; 1;7; 4;4]%nat) in FRJ; [|reflexivity].
    cbn [mk_CB_cells app] in FRJ.
    repeat match type of FRJ with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FRJ; clearbody j end.

    zstep. zstep. zstep. zstep. zstep. zstep.

    zstep. zstep. zstep. zstep. lstep. zstep. lstep. lstep.

    cells_split_at FRJ 30%nat. apply rw_cells_app in FRJ. destruct FRJ as [LOW ITER]. cbn [cells_size csize Nat.add] in ITER.
    replace (FR E + Z.of_nat 240)%Z with (FR_IT E) in ITER by lia.
    apply (rw_cells_C8_C4 psegs _ _ [C8 _; C8 _; C8 _; C8 _] _ (Z_to_bv 64 0) (Z_to_bv 64 1)) in ITER; [| exact od_le8_err_depth]. cbn [app] in ITER.

    od_cur_mem ltac:(fun mm => assert (REST : OD_REST mm) by rest_close).

    pose proof (od_tokI_range E S1 0 ltac:(lia)) as TR0. pose proof (od_tokT_range E BOK 0) as CR0.
    pose proof (od_tokI_range E S1 (n - 1) ltac:(lia)) as TRL. pose proof (od_tokT_range E BOK (n - 1)) as CRL.
    pose proof (od_tokI_range E S1 n ltac:(lia)) as TRN.
    pose proof (od_tokI_range E S1 1 ltac:(lia)) as TR1. pose proof (od_tokT_range E BOK 1) as CR1.
    pose proof (tokT_n bs idxs S1) as TN0.
    od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws 0 IDXA (conj IDXL IDXF) ltac:(lia)) as RDI0;
                               pose proof (tokB_read mm E (tokI bs idxs 0) BUFRO ltac:(lia)) as RDB0).
    replace (o_IDX E + 4 * 0)%Z with (o_IDX E) in RDI0 by lia.
    fold (tokT bs idxs 0) in RDB0.
    set (c0 := tokT bs idxs 0) in *. set (off0 := tokI bs idxs 0) in *.

    zstep. odnorm. zstep. zstep. odnorm. zstep. zstep. zstep.
    clear REST. od_cur_mem ltac:(fun mm => assert (REST : OD_REST mm) by rest_close).
    if_cases K0; zify_cond K0.
    {
      zstep. zstep. zstep. zstep.
      eapply evt_eq; [| eapply (od_invalid Q (mkO 0 1 0 true 0)); [eassumption| | exact REST| exact FRM| exact KX]]; [od_st_eq|].
      eapply rw_cells_eq; [exact ITER|]. unfold iter_cells. od_cells_eq. }

    clear REST.
    zstep. zstep. zstep. zstep. odnorm. zstep. zstep. zstep. zstep.
    rewrite (od_shl32_shr30 (n + -1)) by lia.
    zstep.
    od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (n - 1) IDXA (conj IDXL IDXF) ltac:(lia)) as RDIL;
                               pose proof (tokB_read mm E (tokI bs idxs (n - 1)) BUFRO ltac:(lia)) as RDBL;
                               pose proof (tokI_read mm E ws n IDXA (conj IDXL IDXF) ltac:(lia)) as RDIN;
                               pose proof (tokB_read mm E (tokI bs idxs n) BUFRO ltac:(lia)) as RDBN;
                               pose proof (tokI_read mm E ws 1 IDXA (conj IDXL IDXF) ltac:(lia)) as RDI1;
                               pose proof (tokB_read mm E (tokI bs idxs 1) BUFRO ltac:(lia)) as RDB1).
    fold (tokT bs idxs (n - 1)) in RDBL. fold (tokT bs idxs n) in RDBN. fold (tokT bs idxs 1) in RDB1. rewrite TN0 in RDBN.
    set (cl := tokT bs idxs (n - 1)) in *. set (offl := tokI bs idxs (n - 1)) in *.
    set (c1 := tokT bs idxs 1) in *. set (off1 := tokI bs idxs 1) in *. set (offn := tokI bs idxs n) in *.
    od_cur_mem ltac:(fun mm => assert (REST : OD_REST mm) by rest_close).

    zstep. odnorm. zstep. zstep. odnorm. zstep. zstep.
    if_cases KL; zify_cond KL.
    {
      clear REST.

      lstep. lstep. zstep. zstep. zstep. zstep. lstep.
      od_cur_mem ltac:(fun mm => assert (REST : OD_REST mm) by rest_close).
      eapply evt_eq; [| eapply (od_invalid Q (mkO 1 0 28 false 0)); [eassumption| | exact REST| exact FRM| exact KX]]; [od_st_eq|].
      eapply rw_cells_eq; [exact ITER|]. unfold iter_cells. od_cells_eq. }
    assert (HLAST : tokT bs idxs (n - 1) = C_RBRACKET) by (unfold C_RBRACKET; fold cl; lia).

    zstep. odnorm. zstep. zstep. odnorm. zstep. zstep. odnorm. zstep. if_true.

    replace (o_IDX E + 4 * 1)%Z with (o_IDX E + 4)%Z in RDI1 by lia.
    zstep. odnorm. zstep. zstep. odnorm. zstep. zstep. zstep.
    assert (N2 : (2 <= n)%Z).
    { destruct (Z.eq_dec n 1) as [N1|N1]; [|lia]. exfalso.
      assert (EQ : cl = c0) by (unfold cl, c0; f_equal; lia). lia. }
    clear REST.

    assert (K_C4 : forall st xa0' xa2' xa3' xa4' mm j289' j300' jj0 jj1 jj2 jj3 jj4 jj5 jj6 jj7 jj8 jj9 jj10 jj11 jj12 jj13 jj14 jj15 jj16 jj17 jj18 jj19 jj20 jj21 jj23 jj24 jj25 jj26 jj27 jj28 jj29,
              (st = mkO 1 2 0 true 0 \/ (st = mkO 2 0 0 true 0 /\ c1 = 93%Z)) ->
              rw_cells psegs mm (FR E)
                [CB 8 jj0; CB 8 jj1; CB 8 jj2; CB 8 jj3; CB 8 jj4; CB 8 jj5; CB 8 jj6; CB 8 jj7; CB 8 jj8; CB 8 jj9; CB 8 jj10; CB 8 jj11; CB 8 jj12; CB 8 jj13; CB 8 jj14;
                 CB 8 jj15; CB 8 jj16; CB 8 jj17; CB 8 jj18; CB 8 jj19; CB 8 jj20; CB 8 jj21; C8 (Z_to_bv 64 (o_COPY E)); CB 8 jj23; CB 8 jj24; CB 8 jj25; CB 8 jj26;
                 CB 8 jj27; CB 8 jj28; CB 8 jj29] ->
              rw_cells psegs mm (FR_IT E)
                [C8 (Z_to_bv 64 (o_BUF E)); C8 (Z_to_bv 64 (o_IDX E + 4 * o_pos st)); C8 (Z_to_bv 64 (FR_PA E)); C8 (Z_to_bv 64 (o_SB E));
                 C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 (o_IDX E)); C1 (Z_to_bv 8 0); CB 7 j289'; C4 (Z_to_bv 64 0); CB 4 j300'] ->
              OD_REST mm ->
              evt psegs Q (MS (mkR (Z_to_bv 64 1) (Z_to_bv 64 (FR E)) (o_gp E) (o_tp E) xt0 xt1 xt2 (Z_to_bv 64 (o_IDX E)) (Z_to_bv 64 (o_BUF E))
                                   xa0' (Z_to_bv 64 (o_depth st)) xa2' xa3' xa4' xa5 xa6 xa7
                                   (Z_to_bv 64 (o_len E)) (Z_to_bv 64 (o_act E)) (Z_to_bv 64 91) (Z_to_bv 64 (o_COPY E)) xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                              xF (Z_to_bv 64 0x2751c) xfc None mm (seg_rom psegs))).
    { intros st xa0' xa2' xa3' xa4' mm j289' j300' jj0 jj1 jj2 jj3 jj4 jj5 jj6 jj7 jj8 jj9 jj10 jj11 jj12 jj13 jj14 jj15 jj16 jj17 jj18 jj19 jj20 jj21 jj23 jj24 jj25 jj26 jj27 jj28 jj29
             HST LOW2 ITER2 REST2.
      clear LOW ITER PARS FRHI DPI IDXA IDXL IDXF BUFRO SBW VT GOT MI MU WM ST RDI0 RDB0 RDIL RDBL RDIN RDBN RDI1 RDB1.
      rest_open REST2.
      assert (DR : (0 <= o_depth st <= 2)%Z) by (destruct HST as [->|[-> _]]; cbn; lia).

      zstep. lstep. zstep. zstep. zstep. zstep. zstep.
      eapply evt_cut.
      { od_cur_mem ltac:(fun mm' => eapply evt_eq; [| eapply (od_consts (FR_IT E) 1 1 2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm'); [assumption| lia| eassumption]]).
        od_st_eq. }
      cbv beta. intros ms' P. unfold consts_post in P.
      destruct P as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q22 & q24 & q28 & q29 & q30 & mc3 & k0 & k8 & k16 & k56 & k64 & k72 & k80 & k88 & k128 & k136 & k232
                     & q21 & -> & MUc & WMc & MIc & LOWc).
      clear LOW2.
      lazymatch type of ITER2 with rw_cells _ ?m _ _ => transport_after_call psegs m mc3 MUc WMc end.
      clear MUc WMc.
      unfold low_cells, fr_k24, fr_k96, wz in LOWc. cbn [app] in LOWc.

      zstep. lstep.

      eapply evt_eq; [| eapply (od_loop E OK HLAST ARM_STR ARM_BOOL ARM_ARR ARM_I64 ARM_DBL ARM_OBJ ARM_U64 ARM_RAW ARM_NULL ARM_NEST Q KX
                                        (Z.to_nat (n + 1)) od_init st)]; [unfold OD_HEAD; od_st_eq| | | exact FRM|].
      - unfold o_left. destruct HST as [->|[-> _]]; cbn [o_pos]; lia.
      - left. unfold od_next_ok, od_head_ok, sbo_ok, od_init.
        pose proof (od_tokI_range E S1 (Z.min 1 n) ltac:(lia)). pose proof (od_tokI_range E S1 (Z.min 2 n) ltac:(lia)).
        destruct HST as [->|[-> HC1]]; cbn [o_pos o_depth o_err o_alive o_sbo].
        + split; [lia|]. split; [reflexivity|]. split; [split; [lia| fold bs idxs; lia]|]. split; [reflexivity|].
          right; right. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| fold bs idxs; lia].
        + split; [lia|]. split; [reflexivity|]. split; [split; [lia| fold bs idxs; lia]|]. split; [reflexivity|].
          right; left. split; [reflexivity|]. split; [reflexivity| lia].
      - eapply ODINVg_intro; [| | rest_close].
        + eapply rw_cells_eq; [eassumption|]. unfold fr_k24, fr_k96, fr_k144, K104, K112. cbn [app]. od_cells_eq.
        + eapply rw_cells_eq; [eassumption|]. unfold iter_cells. destruct HST as [->|[-> _]]; od_cells_eq. }
    if_cases K1; zify_cond K1.
    -
      od_cur_mem ltac:(fun mm => assert (REST : OD_REST mm) by rest_close).
      eapply evt_eq; [| eapply (K_C4 (mkO 1 2 0 true 0)); [left; reflexivity| eassumption| | exact REST]]; [od_st_eq|].
      eapply rw_cells_eq; [exact ITER|]. od_cells_eq.
    -
      zstep. zstep. zstep.
      od_cur_mem ltac:(fun mm => assert (REST : OD_REST mm) by rest_close).
      eapply evt_eq; [| eapply (K_C4 (mkO 2 0 0 true 0)); [right; split; [reflexivity| lia]| eassumption| | exact REST]]; [od_st_eq|].
      eapply rw_cells_eq; [exact ITER|]. od_cells_eq.
  Qed.
End Begin.
