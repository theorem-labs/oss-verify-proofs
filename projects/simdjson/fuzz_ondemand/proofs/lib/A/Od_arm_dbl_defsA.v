(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA StoreFast FP ZBridge.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Export Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow Sj_akit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Export Od_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition DBLINVa (E : oaenv) (st : ost) (c0 c104 c176 : list cell) (m1 : mem) : Prop :=
  rw_cells asegs m1 (oa_S1 E) c0 /\
  rw_cells asegs m1 (oa_S1 E + 32) (fr_k32 (oa_F E + 192)) /\
  rw_cells asegs m1 (oa_S1 E + 104) c104 /\
  rw_cells asegs m1 (oa_S1 E + 128) (fr_k128 E) /\
  rw_cells asegs m1 (oa_S1 E + 176) c176 /\
  rw_cells asegs m1 (oa_S1 E + 184) (fr_k184 E (oa_F E + 192) 0 2 1 1 1 1) /\
  (exists j241 j252, rw_cells asegs m1 (oa_F E + 192) (iter_cells E st j241 j252)) /\
  rw_cells asegs m1 (oa_F E + 96) (od_parser_cells E) /\
  rw_cells asegs m1 (o_IMPL E) (dpi_cells E) /\
  (exists ws, u32arr asegs m1 (o_IDX E) ws /\ idx_ok E ws) /\
  bytes_at asegs m1 (o_BUF E) (padded_bytes (o_bs E)) /\
  wr_at asegs m1 (o_SB E) (o_CAP E) /\
  ro_cells asegs m1 OD_DPI_VT od_vt_cells /\
  ro_cells asegs m1 OD_GOT_TABS od_got_cells /\
  mem_inv asegs m1 /\ munch (od_W E) (o_m0 E) m1 /\ wmono asegs (o_m0 E) m1 /\
  stk asegs m1 (o_lo E) (oa_S1 E).

Ltac dbl_open_inv H :=
  let j241 := fresh "j241" in let j252 := fresh "j252" in let ws := fresh "ws" in
  destruct H as (FR0 & FR32 & FR104 & FR128 & FR176 & FR184
                 & (j241 & j252 & ITER) & PARS & DPI & (ws & IDXA & IDXOK) & BUFRO & SBW & VT & GOT & MI & MU & WM & ST);
  unfold fr_k32 in FR32; unfold fr_k128 in FR128; unfold fr_k184 in FR184; unfold iter_cells in ITER; unfold dpi_cells in DPI;
  unfold od_parser_cells in PARS;
  unfold od_vt_cells, OD_DPI_VT in VT; unfold od_got_cells, OD_GOT_TABS in GOT; unfold od_W in MU;
  unfold wz in FR0, FR32, FR104, FR128, FR176, FR184, ITER, PARS, DPI;
  let IDXL := fresh "IDXL" in let IDXF := fresh "IDXF" in destruct IDXOK as [IDXL IDXF];
  lazymatch type of BUFRO with
  | bytes_at _ _ _ (padded_bytes ?bs) => let PBL := fresh "PBL" in pose proof (padded_bytes_blen bs) as PBL
  end.

Ltac dbl_close_inv :=
  lazymatch goal with
  | |- DBLINVa _ _ _ _ _ _ =>
      try match goal with
          | HV : o_vptr ?E = ?v, HD : rw_cells _ _ (o_IMPL ?E) (C8 ?v :: _) |- _ => rewrite <- HV in HD
          end;
      unfold DBLINVa, fr_k32, fr_k128, fr_k184, iter_cells, od_parser_cells, dpi_cells, od_vt_cells, od_got_cells, od_W, OD_DPI_VT, OD_GOT_TABS, idx_ok;
      split; [od_ass|];
      split; [od_ass|];
      split; [od_ass|];
      split; [eassumption|];
      split; [od_ass|];
      split; [od_ass|];
      split; [ do 2 eexists; od_ass | ];
      split; [eassumption|]; split; [eassumption|];
      split; [ eexists; split; [eassumption| split; eassumption] | ];
      split; [eassumption|]; split; [eassumption|];
      split; [eassumption|]; split; [eassumption|];
      split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.

Ltac forget_C8_1 H :=
  match type of H with
  | rw_cells ?s ?m ?A (C8 ?v :: ?post) => apply (rw_cells_forget_C8 s m A [] v post) in H; cbn [app] in H
  | rw_cells ?s ?m ?A (?c0 :: C8 ?v :: ?post) => apply (rw_cells_forget_C8 s m A [c0] v post) in H; cbn [app] in H
  | rw_cells ?s ?m ?A (?c0 :: ?c1 :: C8 ?v :: ?post) => apply (rw_cells_forget_C8 s m A [c0; c1] v post) in H; cbn [app] in H
  | rw_cells ?s ?m ?A (?c0 :: ?c1 :: ?c2 :: C8 ?v :: ?post) => apply (rw_cells_forget_C8 s m A [c0; c1; c2] v post) in H; cbn [app] in H
  end.
Ltac forget_C8 H := repeat (forget_C8_1 H).

Ltac forget_2 H :=
  repeat match type of H with
  | rw_cells ?s ?m ?A (C8 ?v :: ?post) => apply (rw_cells_forget_C8 s m A [] v post) in H; cbn [app] in H
  | rw_cells ?s ?m ?A (?c0 :: C8 ?v :: ?c2 :: ?post) => apply (rw_cells_forget_C8 s m A [c0] v (c2 :: post)) in H; cbn [app] in H
  end.

Lemma dbl_of_od : forall E st m1, ODINV E st m1 ->
  exists j0 j8 j16 j24 j104 j112 j120 j176,
    DBLINVa E st [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24] [CB 8 j104; CB 8 j112; CB 8 j120] [CB 8 j176] m1.
Proof.
  intros E st m1 ((j0 & j8 & j16 & j24 & FR0) & FR32 & (j104 & j112 & j120 & FR104) & FR128 & (j176 & FR176) & REST).
  exists j0, j8, j16, j24, j104, j112, j120, j176. split; [exact FR0|]. split; [exact FR32|]. split; [exact FR104|]. split; [exact FR128|].
  split; [exact FR176|]. exact REST.
Qed.
Lemma od_of_dbl : forall E st j0 j8 j16 j24 j104 j112 j120 j176 m1,
  DBLINVa E st [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24] [CB 8 j104; CB 8 j112; CB 8 j120] [CB 8 j176] m1 -> ODINV E st m1.
Proof.
  intros E st j0 j8 j16 j24 j104 j112 j120 j176 m1 (FR0 & FR32 & FR104 & FR128 & FR176 & REST).
  split; [exists j0, j8, j16, j24; exact FR0|]. split; [exact FR32|]. split; [exists j104, j112, j120; exact FR104|]. split; [exact FR128|].
  split; [exists j176; exact FR176|]. exact REST.
Qed.

Ltac dbl_close_od :=
  lazymatch goal with
  | |- ODINVg _ _ _ _ _ _ _ _ _ _ =>
      try (match goal with H : rw_cells _ _ (oa_S1 _) _ |- _ => progress (forget_C8 H) end);
      try (match goal with H : rw_cells _ _ (oa_S1 _ + 104)%Z _ |- _ => progress (forget_C8 H) end);
      try (match goal with H : rw_cells _ _ (oa_S1 _ + 176)%Z _ |- _ => progress (forget_C8 H) end);
      eapply od_of_dbl; dbl_close_inv
  end.

Ltac ddata w := let M := fresh "DM" in assert (M : IsData w) by exact I.
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
Ltac dstep := step; od_fix_lit_store; zsimp; anorm; dnorm; num_abstract_data.

Ltac dstep0 := step; od_fix_lit_store; zsimp; anorm.
Ltac dtrace pc := idtac.
Ltac d_closed c := match c with | context [?x] => is_var x; fail 1 | _ => idtac end.
Ltac d_real_live H cont := try clear H; cont.
Ltac d_real_keep H cont := zify_cond H; cont.
Ltac dbranch real cont :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      tryif d_closed c then (first [ if_true | if_false ]; cont)
      else lazymatch c with
           | bv_eqb ?x ?x => if_true; cont
           | negb (bv_eqb ?x ?x) => if_false; cont
           | _ => let H := fresh "KB" in if_cases H; real H cont
           end
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
Ltac dwalkk K := dwalk_fuel d_real_keep 300%nat K.
Ltac dwalkv K := dwalk_fuel d_real_live 300%nat K.

Ltac dwalkn n K :=
  lazymatch n with
  | O => idtac
  | S ?n' =>
      lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => dtrace pc; first [ K pc | (dstep; dwalkn n' K) ]
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => dbranch d_real_keep ltac:(idtac; dwalkn n' K)
      end
  end.

Definition DBL_K16 : Z := 0xfccc.
Definition DBL_K24 : Z := 0xfcc8.

Notation DINVa E st neg j0 j8 j104 j112 v176 m1 :=
  (DBLINVa E st [CB 8 j0; CB 8 j8; C8 (Z_to_bv 64 DBL_K16); C8 (Z_to_bv 64 DBL_K24)] [CB 8 j104; CB 8 j112; C8 (Z_to_bv 64 neg)] [C8 v176] m1).
Definition dbl_pos (E : oaenv) (st : ost) (neg q0 : Z) : Prop :=
  (0 <= neg <= 1)%Z /\ q0 = (tokI (o_bs E) (o_idxs E) (o_pos st) + neg)%Z.

Definition dbl_F_k (E : oaenv) (Q : machine_state -> Prop) (st : ost) : Prop :=
  forall neg q0 q j0 j8 j104 j112 v176 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa7 xF xfc m1,
    dbl_pos E st neg q0 -> (q0 <= q <= o_len E + 2)%Z -> B (o_bs E) q = 46%Z -> frm0 xfc ->
    DINVa E st neg j0 j8 j104 j112 v176 m1 ->
    evt asegs Q (ODST E 0x97ce4 (Z_to_bv 64 DBL_K16) xt1 xt2 xa0 xa1 xa2 xa3 (Z_to_bv 64 (o_BUF E + q)) xa5 (Z_to_bv 64 DBL_K24) xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (oa_F E + 192)) (Z_to_bv 64 (o_BUF E + q0))
                      (Z_to_bv 64 (o_BUF E)) (Z_to_bv 64 (tokI (o_bs E) (o_idxs E) (o_pos st))) xF xfc m1).

Definition dbl_R_k (E : oaenv) (Q : machine_state -> Prop) (st : ost) : Prop :=
  forall neg q0 q k1 j0 j8 j104 j112 v176 xt2 xa0 xa1 xa2 xa3 xa5 xa7 xt4 xF xfc m1,
    dbl_pos E st neg q0 -> (q0 <= q)%Z -> (1 <= k1)%Z -> (q + k1 <= o_len E + 2)%Z -> frm0 xfc ->
    DINVa E st neg j0 j8 j104 j112 v176 m1 ->
    evt asegs Q (ODST E 0x99298 (Z_to_bv 64 (o_BUF E)) (Z_to_bv 64 (tokI (o_bs E) (o_idxs E) (o_pos st))) xt2 xa0 xa1 xa2 xa3
                      (Z_to_bv 64 (o_BUF E + q)) xa5 (Z_to_bv 64 10) xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (oa_F E + 192)) (Z_to_bv 64 (o_BUF E + q0))
                      (Z_to_bv 64 k1) xt4 xF xfc m1).

Definition dbl_E_k (E : oaenv) (Q : machine_state -> Prop) (st : ost) : Prop :=
  forall neg q0 p j0 j8 j104 j112 v176 xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xF xfc m1,
    dbl_pos E st neg q0 -> (q0 <= p <= o_len E + 2)%Z -> frm0 xfc ->
    DINVa E st neg j0 j8 j104 j112 v176 m1 ->
    evt asegs Q (ODST E 0x9933c xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 (o_BUF E + p)) xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (oa_F E + 192)) (Z_to_bv 64 (o_BUF E + q0)) xt3 xt4 xF xfc m1).
Definition dbl_T_k (E : oaenv) (Q : machine_state -> Prop) (st : ost) : Prop :=
  forall neg q0 r j0 j8 j104 j112 v176 xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xF xfc m1,
    dbl_pos E st neg q0 -> (q0 <= r <= o_len E + 2)%Z -> frm0 xfc ->
    DINVa E st neg j0 j8 j104 j112 v176 m1 ->
    evt asegs Q (ODST E 0x99440 xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 (o_BUF E + r)) xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (oa_F E + 192)) (Z_to_bv 64 (o_BUF E + q0)) xt3 xt4 xF xfc m1).

Lemma ori32_e_nonzero : forall c, (0 <= c < 256)%Z -> Z.lor c 32 = 101%Z -> c <> 0%Z.
Proof. intros c Hc H ->. vm_compute in H. discriminate. Qed.
Lemma sign_nonzero : forall c, (0 <= c < 256)%Z -> (Z.land ((c + -43) mod 18446744073709551616) 18446744073709551613 < 1)%Z -> c <> 0%Z.
Proof. intros c Hc H ->. vm_compute in H. discriminate. Qed.
