(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Export Od_defs Od_tables.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition DBLINVc (E : odenv) (st : ost) (c0 c56 c128 : list cell) (m1 : mem) : Prop :=
  rw_cells psegs m1 (FR E) c0 /\
  rw_cells psegs m1 (bv_unsigned (o_sp E) + -488) fr_k24 /\
  rw_cells psegs m1 (bv_unsigned (o_sp E) + -456) c56 /\
  rw_cells psegs m1 (bv_unsigned (o_sp E) + -416) fr_k96 /\
  rw_cells psegs m1 (bv_unsigned (o_sp E) + -384) c128 /\
  rw_cells psegs m1 (bv_unsigned (o_sp E) + -368) (fr_k144 E 2 0 1 1) /\
  (exists j289 j300, rw_cells psegs m1 (FR_IT E) (iter_cells E st j289 j300)) /\
  rw_cells psegs m1 (FR_PA E) (od_parser_cells E) /\
  rw_cells psegs m1 (bv_unsigned (o_sp E) + -152) (o_hi E) /\
  rw_cells psegs m1 (o_IMPL E) (dpi_cells E) /\
  (exists ws, u32arr psegs m1 (o_IDX E) ws /\ idx_ok E ws) /\
  bytes_at psegs m1 (o_BUF E) (padded_bytes (o_bs E)) /\
  wr_at psegs m1 (o_SB E) (o_CAP E) /\
  (exists v0 v1 v2 v3 v5 v6 v7 v8 v9, rw_cells psegs m1 OD_DPI_VPTR (od_vt_cells v0 v1 v2 v3 v5 v6 v7 v8 v9)) /\
  rw_cells psegs m1 OD_GOT_TABS [C8 (wz 0x137e8); C8 (wz 0x14878); C8 (wz 0x138e8)] /\
  mem_inv psegs m1 /\ munch (od_W E) (o_m0 E) m1 /\ wmono psegs (o_m0 E) m1 /\
  stk psegs m1 (o_lo E) (FR E).

Ltac dbl_open_inv H :=
  let j289 := fresh "j289" in let j300 := fresh "j300" in let ws := fresh "ws" in
  let v0 := fresh "v0" in let v1 := fresh "v1" in let v2 := fresh "v2" in let v3 := fresh "v3" in let v5 := fresh "v5" in
  let v6 := fresh "v6" in let v7 := fresh "v7" in let v8 := fresh "v8" in let v9 := fresh "v9" in
  destruct H as (FR0 & FR24 & FR56 & FR96 & FR128 & FR144
                 & (j289 & j300 & ITER) & PARS & FRHI & DPI & (ws & IDXA & IDXOK) & BUFRO & SBW
                 & (v0 & v1 & v2 & v3 & v5 & v6 & v7 & v8 & v9 & VT) & GOT & MI & MU & WM & ST);
  unfold fr_k24 in FR24; unfold fr_k96 in FR96; unfold fr_k144 in FR144; unfold iter_cells in ITER; unfold dpi_cells in DPI;
  unfold od_parser_cells in PARS;
  unfold od_vt_cells in VT; unfold od_W in MU; unfold OD_DPI_VPTR in VT; unfold OD_GOT_TABS in GOT;
  unfold wz in FR0, FR24, FR56, FR96, FR128, FR144, ITER, PARS, DPI, VT, GOT;
  let IDXL := fresh "IDXL" in let IDXF := fresh "IDXF" in destruct IDXOK as [IDXL IDXF];
  lazymatch type of BUFRO with
  | bytes_at _ _ _ (padded_bytes ?bs) => let PBL := fresh "PBL" in pose proof (padded_bytes_blen bs) as PBL
  end.

Ltac dbl_close_inv :=
  lazymatch goal with
  | |- DBLINVc _ _ _ _ _ _ =>
      unfold DBLINVc, fr_k24, fr_k96, fr_k144, iter_cells, od_parser_cells, dpi_cells, od_vt_cells, od_W, OD_DPI_VPTR, OD_GOT_TABS, idx_ok;
      split; [od_ass|];
      split; [eassumption|];
      split; [od_ass|];
      split; [eassumption|];
      split; [od_ass|];
      split; [eassumption|];
      split; [ do 2 eexists; od_ass | ];
      split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
      split; [ eexists; split; [eassumption| split; eassumption] | ];
      split; [eassumption|]; split; [eassumption|];
      split; [ do 9 eexists; eassumption | ];
      split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.

Ltac forget_C8_1 H :=
  match type of H with
  | rw_cells ?s ?m ?A (C8 ?v :: ?post) => apply (rw_cells_forget_C8 s m A [] v post) in H; cbn [app] in H
  | rw_cells ?s ?m ?A (?c0 :: C8 ?v :: ?post) => apply (rw_cells_forget_C8 s m A [c0] v post) in H; cbn [app] in H
  | rw_cells ?s ?m ?A (?c0 :: ?c1 :: C8 ?v :: ?post) => apply (rw_cells_forget_C8 s m A [c0; c1] v post) in H; cbn [app] in H
  | rw_cells ?s ?m ?A (?c0 :: ?c1 :: ?c2 :: C8 ?v :: ?post) => apply (rw_cells_forget_C8 s m A [c0; c1; c2] v post) in H; cbn [app] in H
  | rw_cells ?s ?m ?A (?c0 :: ?c1 :: ?c2 :: ?c3 :: C8 ?v :: ?post) => apply (rw_cells_forget_C8 s m A [c0; c1; c2; c3] v post) in H; cbn [app] in H
  end.
Ltac forget_C8 H := repeat (forget_C8_1 H).

Lemma dbl_of_od : forall E st m1, ODINV E st m1 ->
  exists j0 j8 j16 j56 j64 j72 j80 j88 j128 j136,
    DBLINVc E st [CB 8 j0; CB 8 j8; CB 8 j16] [CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88] [CB 8 j128; CB 8 j136] m1.
Proof.
  intros E st m1 ((j0 & j8 & j16 & FR0) & FR24 & (j56 & j64 & j72 & j80 & j88 & FR56) & FR96 & (j128 & j136 & FR128) & REST).
  exists j0, j8, j16, j56, j64, j72, j80, j88, j128, j136. split; [exact FR0|]. split; [exact FR24|]. split; [exact FR56|].
  split; [exact FR96|]. split; [exact FR128|]. exact REST.
Qed.

Lemma od_of_dbl : forall E st j0 j8 j16 j56 j64 j72 j80 j88 j128 j136 m1,
  DBLINVc E st [CB 8 j0; CB 8 j8; CB 8 j16] [CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88] [CB 8 j128; CB 8 j136] m1 -> ODINV E st m1.
Proof.
  intros E st j0 j8 j16 j56 j64 j72 j80 j88 j128 j136 m1 (FR0 & FR24 & FR56 & FR96 & FR128 & REST).
  split; [exists j0, j8, j16; exact FR0|]. split; [exact FR24|]. split; [exists j56, j64, j72, j80, j88; exact FR56|].
  split; [exact FR96|]. split; [exists j128, j136; exact FR128|]. exact REST.
Qed.

Ltac dbl_close_od :=
  lazymatch goal with
  | |- ODINVg _ _ _ _ _ _ _ =>
      try (match goal with H : rw_cells _ _ (bv_unsigned (o_sp _) + -512)%Z _ |- _ => progress (forget_C8 H) end);
      try (match goal with H : rw_cells _ _ (bv_unsigned (o_sp _) + -456)%Z _ |- _ => progress (forget_C8 H) end);
      try (match goal with H : rw_cells _ _ (bv_unsigned (o_sp _) + -384)%Z _ |- _ => progress (forget_C8 H) end);
      eapply od_of_dbl; dbl_close_inv
  end.

Definition dbl_pos (E : odenv) (st : ost) (neg q0 : Z) : Prop :=
  (0 <= neg <= 1 /\ q0 = tokI (o_bs E) (o_idxs E) (o_pos st) + neg /\ q0 <= o_len E)%Z.

Definition dbl_A_k (E : odenv) (Q : machine_state -> Prop) (st : ost) : Prop :=
  forall neg q0 q v128 j0 j8 j16 j56 j64 j72 j80 j136 xt0 xt1 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt4 xt5 xF xfc m1,
    (0 <= neg <= 1)%Z -> q0 = (tokI (o_bs E) (o_idxs E) (o_pos st) + neg)%Z -> (q0 <= q <= o_len E + 2)%Z -> frm0 xfc ->
    DBLINVc E st [CB 8 j0; CB 8 j8; CB 8 j16] [CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 neg)] [C8 v128; CB 8 j136] m1 ->
    evt psegs Q (ODST E 0x27b28 xt0 xt1 (Z_to_bv 64 (o_BUF E + q)) xa0 (Z_to_bv 64 (o_BUF E + q0)) xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (B (o_bs E) q)) xt4 xt5 xF xfc m1).

Definition DBL_K0 : Z := 0x12b30.
Definition DBL_K8 : Z := 0x12b34.

Definition dbl_E_k (E : odenv) (Q : machine_state -> Prop) (st : ost) : Prop :=
  forall neg q0 q j56 j64 j72 j80 j128 j136 xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt4 xF xfc m1,
    (0 <= neg <= 1)%Z -> q0 = (tokI (o_bs E) (o_idxs E) (o_pos st) + neg)%Z -> (q0 <= q <= o_len E + 2)%Z -> frm0 xfc ->
    DBLINVc E st [C8 (Z_to_bv 64 DBL_K0); C8 (Z_to_bv 64 DBL_K8); C8 (Z_to_bv 64 (o_IDX E + 4 * o_pos st))]
                 [CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 neg)] [CB 8 j128; CB 8 j136] m1 ->
    evt psegs Q (ODST E 0x28224 xt0 xt1 xt2 xa0 (Z_to_bv 64 (o_BUF E + q0)) xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (B (o_bs E) q)) xt4 (Z_to_bv 64 (o_BUF E + q)) xF xfc m1).

Definition dbl_T_k (E : odenv) (Q : machine_state -> Prop) (st : ost) : Prop :=
  forall neg q0 c j56 j64 j72 j80 j128 j136 xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt4 xt5 xF xfc m1,
    (0 <= neg <= 1)%Z -> q0 = (tokI (o_bs E) (o_idxs E) (o_pos st) + neg)%Z -> (0 <= c < 256)%Z -> frm0 xfc ->
    DBLINVc E st [C8 (Z_to_bv 64 DBL_K0); C8 (Z_to_bv 64 DBL_K8); C8 (Z_to_bv 64 (o_IDX E + 4 * o_pos st))]
                 [CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 neg)] [CB 8 j128; CB 8 j136] m1 ->
    evt psegs Q (ODST E 0x282a8 xt0 xt1 xt2 xa0 (Z_to_bv 64 (o_BUF E + q0)) xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 c) xt4 xt5 xF xfc m1).

Definition dbl_F_k (E : odenv) (Q : machine_state -> Prop) (st : ost) : Prop :=
  forall neg q0 q v128 j56 j64 j72 j80 j136 xt0 xt1 xa0 xa2 xa3 xa4 xa7 xt3 xt4 xt5 xF xfc m1,
    (0 <= neg <= 1)%Z -> q0 = (tokI (o_bs E) (o_idxs E) (o_pos st) + neg)%Z -> (q0 <= q <= o_len E + 2)%Z -> B (o_bs E) q = 46%Z -> frm0 xfc ->
    DBLINVc E st [C8 (Z_to_bv 64 DBL_K0); C8 (Z_to_bv 64 DBL_K8); C8 (Z_to_bv 64 (o_IDX E + 4 * o_pos st))]
                 [CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 neg)] [C8 v128; CB 8 j136] m1 ->
    evt psegs Q (ODST E 0x27b48 xt0 xt1 (Z_to_bv 64 (o_BUF E + q)) xa0 (Z_to_bv 64 (o_BUF E + q0)) xa2 xa3 xa4
                      (Z_to_bv 64 DBL_K0) (Z_to_bv 64 DBL_K8) xa7
                      (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xt3 xt4 xt5 xF xfc m1).

Definition dbl_frac_stmt (E : odenv) : Prop :=
  forall (Q : machine_state -> Prop) st,
    tokT (o_bs E) (o_idxs E) (o_n E - 1) = C_RBRACKET -> od_head_ok (o_bs E) (o_idxs E) 1 st ->
    od_plus_k E Q st -> dbl_E_k E Q st -> dbl_F_k E Q st.
Definition dbl_cf_stmt (E : odenv) : Prop :=
  forall (Q : machine_state -> Prop) st,
    tokT (o_bs E) (o_idxs E) (o_n E - 1) = C_RBRACKET -> od_head_ok (o_bs E) (o_idxs E) 1 st ->
    od_plus_k E Q st -> dbl_T_k E Q st.

Definition dbl_R_k (E : odenv) (Q : machine_state -> Prop) (st : ost) : Prop :=
  forall neg q0 q k1 w56 w64 v128 xt0 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xF xfc m1,
    (0 <= neg <= 1)%Z -> q0 = (tokI (o_bs E) (o_idxs E) (o_pos st) + neg)%Z -> (q0 <= q)%Z -> (1 <= k1)%Z -> (q + k1 <= o_len E + 2)%Z -> frm0 xfc ->
    DBLINVc E st [C8 (Z_to_bv 64 DBL_K0); C8 (Z_to_bv 64 DBL_K8); C8 (Z_to_bv 64 (o_IDX E + 4 * o_pos st))]
                 [C8 w56; C8 w64; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 (o_act E)); C8 (Z_to_bv 64 neg)] [C8 v128; C8 (Z_to_bv 64 0x640001)] m1 ->
    evt psegs Q (ODST E 0x281c0 xt0 (Z_to_bv 64 k1) (Z_to_bv 64 (o_BUF E + q)) xa0 (Z_to_bv 64 (o_BUF E + q0)) xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xt3 xt4 xt5 xF xfc m1).

Ltac forget_56 H :=
  repeat match type of H with
  | rw_cells ?s ?m ?A (C8 ?v :: ?post) => apply (rw_cells_forget_C8 s m A [] v post) in H; cbn [app] in H
  | rw_cells ?s ?m ?A (?c0 :: C8 ?v :: ?post) => apply (rw_cells_forget_C8 s m A [c0] v post) in H; cbn [app] in H
  | rw_cells ?s ?m ?A (?c0 :: ?c1 :: C8 ?v :: ?post) => apply (rw_cells_forget_C8 s m A [c0; c1] v post) in H; cbn [app] in H
  | rw_cells ?s ?m ?A (?c0 :: ?c1 :: ?c2 :: C8 ?v :: ?post) => apply (rw_cells_forget_C8 s m A [c0; c1; c2] v post) in H; cbn [app] in H
  end.

Definition dbl_fhead_stmt (E : odenv) : Prop :=
  forall (Q : machine_state -> Prop) st,
    tokT (o_bs E) (o_idxs E) (o_n E - 1) = C_RBRACKET -> od_head_ok (o_bs E) (o_idxs E) 1 st ->
    od_plus_k E Q st -> dbl_R_k E Q st -> dbl_F_k E Q st.
