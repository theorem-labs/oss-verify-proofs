(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Export ZifyBool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast FP ZBridge.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Export Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Export Od_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition DBLINVu (E : odenv) (st : ost) (c24 c88 c168 : list cell) (m1 : mem) : Prop :=
  rw_cells usegs m1 (FR E) fr_k0 /\
  rw_cells usegs m1 (bv_unsigned (o_sp E) + -472) c24 /\
  rw_cells usegs m1 (bv_unsigned (o_sp E) + -440) fr_k56 /\
  rw_cells usegs m1 (bv_unsigned (o_sp E) + -408) c88 /\
  rw_cells usegs m1 (bv_unsigned (o_sp E) + -400) (fr_k96 0) /\
  rw_cells usegs m1 (bv_unsigned (o_sp E) + -328) c168 /\
  rw_cells usegs m1 (bv_unsigned (o_sp E) + -320) (fr_k176 2 1 (o_IDX E) 1 1) /\
  (exists j273 j284, rw_cells usegs m1 (FR_IT E) (iter_cells E st j273 j284)) /\
  rw_cells usegs m1 (FR_PA E) (od_parser_cells E) /\
  rw_cells usegs m1 (bv_unsigned (o_sp E) + -152) (o_hi E) /\
  rw_cells usegs m1 (o_IMPL E) (dpi_cells E) /\
  (exists ws, u32arr usegs m1 (o_IDX E) ws /\ idx_ok E ws) /\
  bytes_at usegs m1 (o_BUF E) (padded_bytes (o_bs E)) /\
  wr_at usegs m1 (o_SB E) (o_CAP E) /\
  (exists v0 v1 v2 v3 v5 v6 v7 v8 v9, rw_cells usegs m1 OD_DPI_VPTR (od_vt_cells v0 v1 v2 v3 v5 v6 v7 v8 v9)) /\
  rw_cells usegs m1 OD_GOT_TABS [C8 (wz 0x137e8); C8 (wz 0x147c0); C8 (wz 0x14878); C8 (wz 0x138e8)] /\
  mem_inv usegs m1 /\ munch (od_W E) (o_m0 E) m1 /\ wmono usegs (o_m0 E) m1 /\
  stk usegs m1 (o_lo E) (FR E).

Ltac dbl_open_inv H :=
  let j273 := fresh "j273" in let j284 := fresh "j284" in let ws := fresh "ws" in
  let v0 := fresh "v0" in let v1 := fresh "v1" in let v2 := fresh "v2" in let v3 := fresh "v3" in let v5 := fresh "v5" in
  let v6 := fresh "v6" in let v7 := fresh "v7" in let v8 := fresh "v8" in let v9 := fresh "v9" in
  destruct H as (FR0 & FR24 & FR56 & FR88 & FR96 & FR168 & FR176
                 & (j273 & j284 & ITER) & PARS & FRHI & DPI & (ws & IDXA & IDXOK) & BUFRO & SBW
                 & (v0 & v1 & v2 & v3 & v5 & v6 & v7 & v8 & v9 & VT) & GOT & MI & MU & WM & ST);
  unfold fr_k0 in FR0; unfold fr_k56 in FR56; unfold fr_k96 in FR96; unfold fr_k176 in FR176; unfold iter_cells in ITER; unfold dpi_cells in DPI;
  unfold od_parser_cells in PARS;
  unfold od_vt_cells in VT; unfold od_W in MU; unfold OD_DPI_VPTR in VT; unfold OD_GOT_TABS in GOT;
  unfold wz, K104, K112 in FR0, FR24, FR56, FR88, FR96, FR168, FR176, ITER, PARS, DPI, VT, GOT;
  let IDXL := fresh "IDXL" in let IDXF := fresh "IDXF" in destruct IDXOK as [IDXL IDXF];
  lazymatch type of BUFRO with
  | bytes_at _ _ _ (padded_bytes ?bs) => let PBL := fresh "PBL" in pose proof (padded_bytes_blen bs) as PBL
  end.

Ltac dbl_close_inv :=
  lazymatch goal with
  | |- DBLINVu _ _ _ _ _ _ =>
      try match goal with
          | HV : o_vptr ?E = ?v, HD : rw_cells _ _ (o_IMPL ?E) (C8 ?v :: _) |- _ => rewrite <- HV in HD
          end;
      unfold DBLINVu, fr_k0, fr_k56, fr_k96, fr_k176, iter_cells, od_parser_cells, dpi_cells, od_vt_cells, od_W, OD_DPI_VPTR, OD_GOT_TABS, idx_ok;
      split; [od_ass|];
      split; [od_ass|];
      split; [od_ass|];
      split; [od_ass|];
      split; [od_ass|];
      split; [od_ass|];
      split; [od_ass|];
      split; [ do 2 eexists; od_ass | ];
      split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
      split; [ eexists; split; [eassumption| split; eassumption] | ];
      split; [eassumption|]; split; [eassumption|];
      split; [ do 9 eexists; eassumption | ];
      split; [od_ass|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.

Ltac forget_C8_1 H :=
  match type of H with
  | rw_cells ?s ?m ?A (C8 ?v :: ?post) => apply (rw_cells_forget_C8 s m A [] v post) in H; cbn [app] in H
  | rw_cells ?s ?m ?A (?c0 :: C8 ?v :: ?post) => apply (rw_cells_forget_C8 s m A [c0] v post) in H; cbn [app] in H
  | rw_cells ?s ?m ?A (?c0 :: ?c1 :: C8 ?v :: ?post) => apply (rw_cells_forget_C8 s m A [c0; c1] v post) in H; cbn [app] in H
  | rw_cells ?s ?m ?A (?c0 :: ?c1 :: ?c2 :: C8 ?v :: ?post) => apply (rw_cells_forget_C8 s m A [c0; c1; c2] v post) in H; cbn [app] in H
  end.
Ltac forget_C8 H := repeat (forget_C8_1 H).

Lemma dbl_of_od : forall E st m1, ODINV E st m1 ->
  exists j24 j32 j40 j48 j88 j168, DBLINVu E st [CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48] [CB 8 j88] [CB 8 j168] m1.
Proof.
  intros E st m1 (FR0 & (j24 & j32 & j40 & j48 & FR24) & FR56 & (j88 & FR88) & FR96 & (j168 & FR168) & REST).
  exists j24, j32, j40, j48, j88, j168. split; [exact FR0|]. split; [exact FR24|]. split; [exact FR56|]. split; [exact FR88|].
  split; [exact FR96|]. split; [exact FR168|]. exact REST.
Qed.

Lemma od_of_dbl : forall E st j24 j32 j40 j48 j88 j168 m1,
  DBLINVu E st [CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48] [CB 8 j88] [CB 8 j168] m1 -> ODINV E st m1.
Proof.
  intros E st j24 j32 j40 j48 j88 j168 m1 (FR0 & FR24 & FR56 & FR88 & FR96 & FR168 & REST).
  split; [exact FR0|]. split; [exists j24, j32, j40, j48; exact FR24|]. split; [exact FR56|]. split; [exists j88; exact FR88|].
  split; [exact FR96|]. split; [exists j168; exact FR168|]. exact REST.
Qed.

Ltac dbl_close_od :=
  lazymatch goal with
  | |- ODINVg _ _ _ _ _ _ _ _ _ =>
      try (match goal with H : rw_cells _ _ (bv_unsigned (o_sp _) + -472)%Z _ |- _ => progress (forget_C8 H) end);
      try (match goal with H : rw_cells _ _ (bv_unsigned (o_sp _) + -408)%Z _ |- _ => progress (forget_C8 H) end);
      try (match goal with H : rw_cells _ _ (bv_unsigned (o_sp _) + -328)%Z _ |- _ => progress (forget_C8 H) end);
      eapply od_of_dbl; dbl_close_inv
  end.

Lemma d_shl1 : forall x, Z.shiftl x 1 = (2 * x)%Z.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. change (2^1)%Z with 2%Z. lia. Qed.
Lemma d_shl3 : forall x, Z.shiftl x 3 = (8 * x)%Z.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia. Qed.
Ltac dnorm :=
  odnorm;
  repeat match goal with
  | |- context [Z.shiftl ?x 1] => rewrite (d_shl1 x)
  | |- context [Z.shiftl ?x 3] => rewrite (d_shl3 x)
  end.

Ltac ddata w := let M := fresh "DM" in assert (M : IsData w) by exact I.
Ltac dstep := step; od_fix_lit_store; zsimp; dnorm; num_abstract_data.

Ltac dstep0 := step; od_fix_lit_store; zsimp.

Lemma d_lxor_sign : forall x, (0 <= x < 18446744073709551616)%Z ->
  Z.lxor x 9223372036854775808 = ((x + 9223372036854775808) mod 18446744073709551616)%Z.
Proof. intros x H. apply (zb_lxor_sign x). exact H. Qed.

Ltac dsgn H :=
  repeat match type of H with
  | context [Z.lxor ?x 9223372036854775808] => rewrite (d_lxor_sign x) in H by first [ lia | apply Z.mod_pos_bound; lia ]
  end.
Ltac dkill H := first [ lia | ulx; lia | (apply Z.lor_eq_0_iff in H; lia) | (Z.div_mod_to_equations; lia)
                      | (progress (dsgn H); first [ lia | Z.div_mod_to_equations; lia ]) ].
Ltac dtrace pc := idtac.

Ltac d_is_trap pc :=
  lazymatch pc with
  | 0x29320%Z => idtac | 0x279b8%Z => idtac | 0x279c4%Z => idtac | 0x279d4%Z => idtac | 0x279e0%Z => idtac | 0x279f4%Z => idtac | 0x27e70%Z => idtac
  | 0x27e78%Z => idtac | 0x27e84%Z => idtac | 0x27e8c%Z => idtac | 0x27e98%Z => idtac | 0x27eac%Z => idtac | 0x27ec0%Z => idtac | 0x27ec8%Z => idtac
  | 0x27ee4%Z => idtac | 0x27f04%Z => idtac | 0x27f38%Z => idtac | 0x27f7c%Z => idtac | 0x27fac%Z => idtac
  end.

Ltac d_real_kill H cont := zify_cond H; try (odsig H); first [ solve [exfalso; lia] | cont ].
Ltac d_real_live H cont := try clear H; cont.
Ltac d_real_keep H cont := zify_cond H; cont.
Ltac dbranch real cont :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then Z_to_bv 64 ?a else Z_to_bv 64 ?b) _ _ _ _) =>
      ual; unz;
      let H := fresh "KB" in
      tryif d_is_trap a
      then (if_cases H; zify_cond H; try (odsig H);
            [ first [ solve [exfalso; dkill H] | fail 100 "guard: cannot refute the TAKEN arm to" a ] | try clear H; cont ])
      else tryif d_is_trap b
      then (if_cases H; zify_cond H; try (odsig H);
            [ try clear H; cont | first [ solve [exfalso; dkill H] | fail 100 "guard: cannot refute the FALL-THROUGH arm to" b ] ])
      else (if_cases H; real H cont)
  end.
Ltac dwalk_fuel real n K :=
  lazymatch n with
  | O => lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail 100 "dwalk: out of fuel at" pc end
  | S ?n' =>
      lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => dtrace pc; first [ K pc | (dstep; dwalk_fuel real n' K) ]
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => dbranch real ltac:(idtac; dwalk_fuel real n' K)
      end
  end.
Ltac dwalk K := dwalk_fuel d_real_kill 300%nat K.
Ltac dwalkv K := dwalk_fuel d_real_live 300%nat K.
Ltac dwalkk K := dwalk_fuel d_real_keep 300%nat K.

Ltac dwalkn n K :=
  lazymatch n with
  | O => idtac
  | S ?n' =>
      lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => dtrace pc; first [ K pc | (dstep; dwalkn n' K) ]
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => dbranch d_real_kill ltac:(idtac; dwalkn n' K)
      end
  end.

Ltac d_trap pc := lazymatch pc with 0x29320%Z => fail 100 "TRAP reachable" end.

Definition dbl_sgn (neg : Z) (v24 : word) : Prop := (0 <= neg <= 1)%Z /\ (neg = 0%Z -> bv_unsigned v24 <> 0%Z).

Definition DBL_K168 : Z := 0x12f8c.
Definition DBL_K88 : Z := 0x12f94.

Definition dbl_F_k (E : odenv) (Q : machine_state -> Prop) (st : ost) : Prop :=
  forall neg q0 q v24 v32 j40 j48 xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xt3 xt4 xt5 xt6 xF xfc m1,
    dbl_sgn neg v24 -> q0 = (tokI (o_bs E) (o_idxs E) (o_pos st) + neg)%Z -> (q0 <= q <= o_len E + 2)%Z -> B (o_bs E) q = 46%Z -> frm0 xfc ->
    DBLINVu E st [C8 v24; C8 v32; CB 8 j40; CB 8 j48] [C8 (Z_to_bv 64 DBL_K88)] [C8 (Z_to_bv 64 DBL_K168)] m1 ->
    evt usegs Q (ODST E 0x27fa8 xra xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 (o_BUF E + q0)) xa3 xa4 xa5 xa6 (Z_to_bv 64 (o_BUF E + q))
                      (Z_to_bv 64 2) (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 neg) xt3 xt4 xt5 xt6 xF xfc m1).

Definition dbl_R_k (E : odenv) (Q : machine_state -> Prop) (st : ost) : Prop :=
  forall neg q0 q k1 v24 v32 xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    dbl_sgn neg v24 -> q0 = (tokI (o_bs E) (o_idxs E) (o_pos st) + neg)%Z -> (q0 <= q)%Z -> (1 <= k1)%Z -> (q + k1 <= o_len E + 2)%Z -> frm0 xfc ->
    DBLINVu E st [C8 v24; C8 v32; C8 (Z_to_bv 64 neg); C8 (Z_to_bv 64 (o_act E))] [C8 (Z_to_bv 64 DBL_K88)] [C8 (Z_to_bv 64 DBL_K168)] m1 ->
    evt usegs Q (ODST E 0x288ec xra xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 (o_BUF E + q0)) xa3 xa4 xa5 (Z_to_bv 64 k1) (Z_to_bv 64 (o_BUF E + q))
                      (Z_to_bv 64 2) (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xs11 xt3 xt4 xt5 xt6 xF xfc m1).

Definition dbl_E_k (E : odenv) (Q : machine_state -> Prop) (st : ost) : Prop :=
  forall neg q0 p v24 v32 j40 j48 xra xt0 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt4 xt5 xt6 xF xfc m1,
    dbl_sgn neg v24 -> q0 = (tokI (o_bs E) (o_idxs E) (o_pos st) + neg)%Z -> (q0 <= p <= o_len E + 2)%Z -> frm0 xfc ->
    DBLINVu E st [C8 v24; C8 v32; CB 8 j40; CB 8 j48] [C8 (Z_to_bv 64 DBL_K88)] [C8 (Z_to_bv 64 DBL_K168)] m1 ->
    evt usegs Q (ODST E 0x28978 xra xt0 (Z_to_bv 64 (B (o_bs E) p)) xt2 xa0 xa1 (Z_to_bv 64 (o_BUF E + q0)) xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 neg)
                      (Z_to_bv 64 (o_BUF E + p)) xt4 xt5 xt6 xF xfc m1).

Definition dbl_T_k (E : odenv) (Q : machine_state -> Prop) (st : ost) : Prop :=
  forall neg q0 c v24 v32 j40 j48 xra xt0 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc m1,
    dbl_sgn neg v24 -> q0 = (tokI (o_bs E) (o_idxs E) (o_pos st) + neg)%Z -> (0 <= c < 256)%Z -> frm0 xfc ->
    DBLINVu E st [C8 v24; C8 v32; CB 8 j40; CB 8 j48] [C8 (Z_to_bv 64 DBL_K88)] [C8 (Z_to_bv 64 DBL_K168)] m1 ->
    evt usegs Q (ODST E 0x28e4c xra xt0 (Z_to_bv 64 c) xt2 xa0 xa1 (Z_to_bv 64 (o_BUF E + q0)) xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 neg) xt3 xt4 xt5 xt6 xF xfc m1).

Ltac forget_40 H :=
  repeat match type of H with
  | rw_cells ?s ?m ?A (?c0 :: ?c1 :: C8 ?v :: ?post) => apply (rw_cells_forget_C8 s m A [c0; c1] v post) in H; cbn [app] in H
  | rw_cells ?s ?m ?A (?c0 :: ?c1 :: ?c2 :: C8 ?v :: ?post) => apply (rw_cells_forget_C8 s m A [c0; c1; c2] v post) in H; cbn [app] in H
  end.

Lemma ori32_e_nonzero : forall c, (0 <= c < 256)%Z -> Z.lor c 32 = 101%Z -> c <> 0%Z.
Proof. intros c Hc H ->. vm_compute in H. discriminate. Qed.
Lemma sign_nonzero : forall c, (0 <= c < 256)%Z -> (Z.land ((c + -43) mod 18446744073709551616) 18446744073709551613 < 1)%Z -> c <> 0%Z.
Proof. intros c Hc H ->. vm_compute in H. discriminate. Qed.
