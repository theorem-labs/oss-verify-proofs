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
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Sj_akit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Export Od_defsB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Notation HLASTP E := (tokT (o_bs E) (o_idxs E) (o_n E - 1) = C_RBRACKET).

Definition DBLINVs (E : oaenv) (st : ost) (m1 : mem) : Prop :=
  exists j96 j104 j224 j232 j272,
    ODINVc E (oa_F E + 192) 0 2 1 (o_IDX E) 1 1 (o_IDX E + 4 * o_pos st)
           (CB 8 j96) (CB 8 j104) (CB 8 j224) (CB 8 j232) (CB 8 j272)
           (C8 (wz (oa_F E + 200))) (C8 (wz (oa_F E + 192))) (C8 (wz 2)) st m1.

Notation DBLCST E pc xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m :=
  (MS (mkR (Z_to_bv 64 0x9b15c) (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) xt0 xt1 xt2
           (Z_to_bv 64 (oa_USP E)) (Z_to_bv 64 (oa_S1 E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           (Z_to_bv 64 ((oa_F E + 200) / 8 + 2147450880)) (Z_to_bv 64 (oa_F E + 224)) (Z_to_bv 64 (o_act E)) xs5 xs6
           (Z_to_bv 64 2147450880) (Z_to_bv 64 (oa_F E + 228)) (Z_to_bv 64 4)
           xs10 xs11 xt3 xt4 xt5 xt6)
      xF (Z_to_bv 64 pc) xfc None m (seg_rom bsegs)).

Definition od_slow_k (E : oaenv) (Q : machine_state -> Prop) (st : ost) : Prop :=
  forall xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    frm0 xfc -> DBLINVs E st m1 ->
    evt bsegs Q (DBLCST E OD_FROMCH xt0 xt1 xt2 (Z_to_bv 64 (o_BUF E + tokI (o_bs E) (o_idxs E) (o_pos st))) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                        xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1).
Definition arm_dbl_evt (E : oaenv) : Prop :=
  forall (Q : machine_state -> Prop) st,
    HLASTP E -> od_head_ok (o_bs E) (o_idxs E) 1 st ->
    od_plus_k E Q st -> od_slow_k E Q st ->
    arm_k E Q 0x97818 st.

Definition dbl_resume_stmt (E : oaenv) : Prop :=
  forall (Q : machine_state -> Prop) st xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    HLASTP E -> od_head_ok (o_bs E) (o_idxs E) 1 st ->
    od_plus_k E Q st ->
    frm0 xfc -> DBLINVs E st m1 ->
    evt bsegs Q (DBLCST E 0x9b15c xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1).

Ltac dgok := first [ if_true | uok ].
Ltac dgtrap := first [ if_false | utrap ].

Ltac dsstep := step; od_fix_lit_store; zsimp; anorm.

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

Definition dbl_pos (E : oaenv) (st : ost) (neg q0 : Z) : Prop :=
  (0 <= neg <= 1)%Z /\ q0 = (tokI (o_bs E) (o_idxs E) (o_pos st) + neg)%Z.

Definition dbl_sgn (neg : Z) (v4 : word) : Prop := (neg = 0%Z -> bv_unsigned v4 <> 0%Z).

Definition DBL_KT0 : Z := 0x101d0.
Definition DBL_KA7 : Z := 0x101cc.

Notation DBLST E pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m :=
  (MS (mkR xra (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) xt0 xt1 xt2
           (Z_to_bv 64 (oa_USP E)) (Z_to_bv 64 (oa_S1 E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           (Z_to_bv 64 ((oa_F E + 200) / 8 + 2147450880)) xs3 xs4 xs5 xs6
           (Z_to_bv 64 2147450880) (Z_to_bv 64 (oa_F E + 228)) (Z_to_bv 64 4)
           xs10 xs11 xt3 xt4 xt5 xt6)
      xF (Z_to_bv 64 pc) xfc None m (seg_rom bsegs)).

Definition dbl_E_k (E : oaenv) (Q : machine_state -> Prop) (st : ost) : Prop :=
  forall neg q0 p v4 xra xt1 xt2 xa1 xa3 xa6 xs6 xs10 xt3 xt4 xt5 xt6 xF xfc m1,
    dbl_pos E st neg q0 -> dbl_sgn neg v4 -> (q0 <= p <= o_len E + 2)%Z -> frm0 xfc -> DBLINVs E st m1 ->
    evt bsegs Q (DBLST E 0x9991c xra (Z_to_bv 64 DBL_KT0) xt1 xt2 (Z_to_bv 64 (o_BUF E + q0)) xa1 (Z_to_bv 64 (o_BUF E + p)) xa3 v4 (Z_to_bv 64 neg) xa6
                       (Z_to_bv 64 DBL_KA7) (Z_to_bv 64 (oa_F E + 224)) (Z_to_bv 64 (o_act E)) (Z_to_bv 64 2) xs6 xs10 (Z_to_bv 64 (oa_F E + 192))
                       xt3 xt4 xt5 xt6 xF xfc m1).
Definition dbl_T_k (E : oaenv) (Q : machine_state -> Prop) (st : ost) : Prop :=
  forall neg q0 r v4 xra xt1 xt2 xa1 xa3 xa6 xs6 xs10 xt3 xt4 xt6 xF xfc m1,
    dbl_pos E st neg q0 -> dbl_sgn neg v4 -> (q0 <= r <= o_len E + 2)%Z -> frm0 xfc -> DBLINVs E st m1 ->
    evt bsegs Q (DBLST E 0x9ac18 xra (Z_to_bv 64 DBL_KT0) xt1 xt2 (Z_to_bv 64 (o_BUF E + q0)) xa1 (Z_to_bv 64 (o_BUF E + r)) xa3 v4 (Z_to_bv 64 neg) xa6
                       (Z_to_bv 64 DBL_KA7) (Z_to_bv 64 (oa_F E + 224)) (Z_to_bv 64 (o_act E)) (Z_to_bv 64 2) xs6 xs10 (Z_to_bv 64 (oa_F E + 192))
                       xt3 xt4 (Z_to_bv 64 2) xt6 xF xfc m1).

Definition dbl_F_k (E : oaenv) (Q : machine_state -> Prop) (st : ost) : Prop :=
  forall neg q0 q v4 (w2 w6 : word) xra xt1 xa2 xa3 xs3 xs4 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    dbl_pos E st neg q0 -> dbl_sgn neg v4 -> (q0 <= q <= o_len E + 2)%Z -> B (o_bs E) q = 46%Z -> frm0 xfc -> DBLINVs E st m1 ->
    evt bsegs Q (DBLST E 0x981e4 xra (Z_to_bv 64 DBL_KT0) xt1 w2 (Z_to_bv 64 (o_BUF E + q0)) (Z_to_bv 64 (o_BUF E + q)) xa2 xa3 v4 (Z_to_bv 64 neg) w6
                       (Z_to_bv 64 DBL_KA7) xs3 xs4 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1).
Definition dbl_R_k (E : oaenv) (Q : machine_state -> Prop) (st : ost) : Prop :=
  forall neg q0 q k1 v4 (w2 w6 : word) xra xa2 xa3 xs5 xs6 xs10 xt3 xt4 xt5 xt6 xF xfc m1,
    dbl_pos E st neg q0 -> dbl_sgn neg v4 -> (q0 <= q)%Z -> (1 <= k1)%Z -> (q + k1 <= o_len E + 2)%Z -> frm0 xfc -> DBLINVs E st m1 ->
    evt bsegs Q (DBLST E 0x99848 xra (Z_to_bv 64 DBL_KT0) (Z_to_bv 64 k1) w2 (Z_to_bv 64 (o_BUF E + q0)) (Z_to_bv 64 (o_BUF E + q)) xa2 xa3 v4 (Z_to_bv 64 neg) w6
                       (Z_to_bv 64 DBL_KA7) (Z_to_bv 64 (oa_F E + 224)) (Z_to_bv 64 (o_act E)) xs5 xs6 xs10 (Z_to_bv 64 (oa_F E + 192))
                       xt3 xt4 xt5 xt6 xF xfc m1).

Definition dbl_C_k (E : oaenv) (Q : machine_state -> Prop) (st : ost) : Prop :=
  forall neg q0 v4 (w1 w6 : word) xra xt2 xa1 xa2 xa3 xs6 xs10 xt3 xt4 xt6 xF xfc m1,
    dbl_pos E st neg q0 -> dbl_sgn neg v4 -> (bv_unsigned w1 < 309 \/ 18446744073709551274 <= bv_unsigned w1)%Z -> frm0 xfc -> DBLINVs E st m1 ->
    evt bsegs Q (DBLST E 0x9ac74 xra (Z_to_bv 64 DBL_KT0) w1 xt2 (Z_to_bv 64 (o_BUF E + q0)) xa1 xa2 xa3 v4 (Z_to_bv 64 neg) w6
                       (Z_to_bv 64 DBL_KA7) (Z_to_bv 64 (oa_F E + 224)) (Z_to_bv 64 (o_act E)) (Z_to_bv 64 2) xs6 xs10 (Z_to_bv 64 (oa_F E + 192))
                       xt3 xt4 (Z_to_bv 64 2) xt6 xF xfc m1).

Lemma ori32_e_nonzero : forall c, (0 <= c < 256)%Z -> Z.lor c 32 = 101%Z -> c <> 0%Z.
Proof. intros c Hc H ->. vm_compute in H. discriminate. Qed.
Lemma sign_nonzero : forall c, (0 <= c < 256)%Z -> (Z.land ((c + -43) mod 18446744073709551616) 18446744073709551613 < 1)%Z -> c <> 0%Z.
Proof. intros c Hc H ->. vm_compute in H. discriminate. Qed.
