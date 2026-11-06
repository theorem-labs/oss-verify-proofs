(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFau.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqdR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqdR.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSCw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSCw.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= Q6q3.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= Q6q3.mkr__nia_1. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := tt.
End GwI.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.tyspec) (@QSCw.tyspec) (Q6nq.gwt_def (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.parse_flags) (@QSCw.parse_flags) (Q6nq.gwt_def (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.parse_dir) (@QSCw.parse_dir) (Q6nq.gwt_def (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.is_digit) (@QSCw.is_digit) (Q6nq.gwt_def (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.getint) (@QSCw.getint) (Q6nq.gwt_def (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.flag_bit) (@QSCw.flag_bit) (Q6nq.gwt_def (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.dir_ty_ok) (@QSCw.dir_ty_ok) (Q6nq.gwt_def (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.conv_type_l) (@QSCw.conv_type_l) (Q6nq.gwt_def (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.conv_type) (@QSCw.conv_type) (Q6nq.gwt_def (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.T_LONG) (@QSCw.T_LONG) Q6nq.gwt_nil)))))))))).
Lemma Zrange_forallb : ltac2:(Q6nq.tyx '(@QFau.Zrange_forallb) [] '(@nil Z) 'gwt_X).
Proof. first [GwInst.gw_exact (@QFau.Zrange_forallb) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.Zrange_forallb)]. Qed.

Notation M64 := 18446744073709551615.

Lemma digit_testb : forall c, 0 <= c < 0 + Z.of_nat 256 ->
Bool.eqb (Z.land (c + -48) M64 <=? 9) (is_digit c) = true.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_M64__3; @gw_eq_M64__2; @gw_eq_M64]; [@gw_eq_is_digit__3; @gw_eq_is_digit__2; @gw_eq_is_digit]]); first [GwInst.gw_exact (@QFau.digit_testb) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.digit_testb)]. Qed.
Lemma digit_test : forall c, 0 <= c < 256 -> (Z.land (c + -48) M64 <= 9 <-> is_digit c = true).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_M64__3; @gw_eq_M64__2; @gw_eq_M64]; [@gw_eq_is_digit__3; @gw_eq_is_digit__2; @gw_eq_is_digit]]); first [GwInst.gw_exact (@QFau.digit_test) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.digit_test)]. Qed.
Lemma digit_range : forall c, is_digit c = true <-> 48 <= c <= 57.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_is_digit__3; @gw_eq_is_digit__2; @gw_eq_is_digit]]); first [GwInst.gw_exact (@QFau.digit_range) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.digit_range)]. Qed.

Lemma sp_testb : forall c, 0 <= c < 0 + Z.of_nat 256 ->
Bool.eqb (Z.land (c + -32) M64 <? 32) ((32 <=? c) && (c <? 64)) = true.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_M64__3; @gw_eq_M64__2; @gw_eq_M64]]); first [GwInst.gw_exact (@QFau.sp_testb) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.sp_testb)]. Qed.
Lemma sp_test : forall c, 0 <= c < 256 -> (Z.land (c + -32) M64 < 32 <-> 32 <= c < 64).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_M64__3; @gw_eq_M64__2; @gw_eq_M64]]); first [GwInst.gw_exact (@QFau.sp_test) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.sp_test)]. Qed.

Definition flagw (c : Z) : Z := Z.land (bv_swrap 32 (Z.shiftl 1 ((c + -32) mod 32))) M64.
Lemma gw_eq_flagw : @flagw = ltac:(GwInst.gw_term (@QFau.flagw) (@flagw)). Proof. unfold flagw, QFau.flagw; ltac2:(GwEq.gw_rw [[@gw_eq_M64__3; @gw_eq_M64__2; @gw_eq_M64]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_flagw : gw_eqs.

Lemma flag_noneb : ltac2:(Q6nq.ty1 'GwI.segs '(@QFau.flag_noneb) [[@gw_eq_flag_bit__3; @gw_eq_flag_bit__2; @gw_eq_flag_bit]; [@gw_eq_flagw]] '([75913]%Z : list Z) '(Q6nq.gwt_unf (@FLAGMASK) gwt_X)).
Proof. rewrite ?gw_eq_flagw; ltac2:(GwEq.gw_rw [[@gw_eq_flag_bit__3; @gw_eq_flag_bit__2; @gw_eq_flag_bit]]); first [GwApply.gw_by_name GwI.segs (@QFau.flag_noneb) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QFau.flag_noneb)]. Qed.
Lemma flag_none : forall c, 32 <= c < 64 -> (Z.land (flagw c) 75913 = 0 <-> flag_bit c = None).
Proof. rewrite ?gw_eq_flagw; ltac2:(GwEq.gw_rw [[@gw_eq_flag_bit__3; @gw_eq_flag_bit__2; @gw_eq_flag_bit]]); first [GwApply.gw_by_name GwI.segs (@QFau.flag_none) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QFau.flag_none)]. Qed.
Lemma flag_someb : ltac2:(Q6nq.tyx '(@QFau.flag_someb) [[@gw_eq_flag_bit__3; @gw_eq_flag_bit__2; @gw_eq_flag_bit]; [@gw_eq_flagw]] '([131072]%Z : list Z) 'gwt_X).
Proof. rewrite ?gw_eq_flagw; ltac2:(GwEq.gw_rw [[@gw_eq_flag_bit__3; @gw_eq_flag_bit__2; @gw_eq_flag_bit]]); first [GwInst.gw_exact (@QFau.flag_someb) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.flag_someb)]. Qed.
Lemma flag_some : forall c b, 32 <= c < 64 -> flag_bit c = Some b -> flagw c = b /\ 0 <= b < 131072.
Proof. rewrite ?gw_eq_flagw; ltac2:(GwEq.gw_rw [[@gw_eq_flag_bit__3; @gw_eq_flag_bit__2; @gw_eq_flag_bit]]); first [GwInst.gw_exact (@QFau.flag_some) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.flag_some)]. Qed.
Lemma flag_bit_range : forall c, flag_bit c <> None -> 32 <= c < 64.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_flag_bit__3; @gw_eq_flag_bit__2; @gw_eq_flag_bit]]); first [GwInst.gw_exact (@QFau.flag_bit_range) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.flag_bit_range)]. Qed.

Lemma lor_bound17 : forall a b, 0 <= a < 131072 -> 0 <= b < 131072 -> 0 <= Z.lor a b < 131072.
Proof. first [GwInst.gw_exact (@QFau.lor_bound17) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.lor_bound17)]. Qed.

Lemma parse_flags_cons_some : forall c s fl b, flag_bit c = Some b -> parse_flags (c :: s) fl = parse_flags s (Z.lor fl b).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_flag_bit__3; @gw_eq_flag_bit__2; @gw_eq_flag_bit]; [@gw_eq_parse_flags__3; @gw_eq_parse_flags__2; @gw_eq_parse_flags]]); first [GwInst.gw_exact (@QFau.parse_flags_cons_some) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.parse_flags_cons_some)]. Qed.
Lemma parse_flags_cons_none : forall c s fl, flag_bit c = None -> parse_flags (c :: s) fl = (fl, c :: s).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_flag_bit__3; @gw_eq_flag_bit__2; @gw_eq_flag_bit]; [@gw_eq_parse_flags__3; @gw_eq_parse_flags__2; @gw_eq_parse_flags]]); first [GwInst.gw_exact (@QFau.parse_flags_cons_none) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.parse_flags_cons_none)]. Qed.
Lemma parse_flags_range : forall s fl, 0 <= fl < 131072 -> 0 <= fst (parse_flags s fl) < 131072.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_parse_flags__3; @gw_eq_parse_flags__2; @gw_eq_parse_flags]]); first [GwInst.gw_exact (@QFau.parse_flags_range) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.parse_flags_range)]. Qed.

Lemma getint_cons_digit : ltac2:(Q6nq.tyx '(@QFau.getint_cons_digit) [[@gw_eq_getint__3; @gw_eq_getint__2; @gw_eq_getint]; [@gw_eq_is_digit__3; @gw_eq_is_digit__2; @gw_eq_is_digit]; [@gw_eq_flagw__3; @gw_eq_flagw__2; @gw_eq_flagw]] '([214748364]%Z : list Z) '(Q6nq.gwt_zc INT_MAX gwt_X)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_getint__3; @gw_eq_getint__2; @gw_eq_getint]; [@gw_eq_is_digit__3; @gw_eq_is_digit__2; @gw_eq_is_digit]]); first [GwInst.gw_exact (@QFau.getint_cons_digit) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.getint_cons_digit)]. Qed.
Lemma getint_cons_nondigit : forall c s i, is_digit c = false -> getint (c :: s) i = Some (i, c :: s).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_getint__3; @gw_eq_getint__2; @gw_eq_getint]; [@gw_eq_is_digit__3; @gw_eq_is_digit__2; @gw_eq_is_digit]]); first [GwInst.gw_exact (@QFau.getint_cons_nondigit) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.getint_cons_nondigit)]. Qed.
Lemma getint_some_range : forall s i w s', 0 <= i <= INT_MAX -> getint s i = Some (w, s') -> 0 <= w <= INT_MAX.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_getint__3; @gw_eq_getint__2; @gw_eq_getint]]); first [GwInst.gw_exact (@QFau.getint_some_range) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.getint_some_range)]. Qed.

Lemma lxor_imax : forall x, 0 <= x <= 2147483647 -> Z.lxor x 2147483647 = 2147483647 - x.
Proof. first [GwInst.gw_exact (@QFau.lxor_imax) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.lxor_imax)]. Qed.

Lemma parse_dir_shape : ltac2:(Q6nq.tyx '(@QFau.parse_dir_shape) [[@gw_eq_getint__3; @gw_eq_getint__2; @gw_eq_getint]; [@gw_eq_is_digit__3; @gw_eq_is_digit__2; @gw_eq_is_digit]; [@gw_eq_parse_dir__3; @gw_eq_parse_dir__2; @gw_eq_parse_dir]; [@gw_eq_parse_flags__3; @gw_eq_parse_flags__2; @gw_eq_parse_flags]; [@gw_eq_tyspec__3; @gw_eq_tyspec__2; @gw_eq_tyspec]; [@gw_eq_flagw__3; @gw_eq_flagw__2; @gw_eq_flagw]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_getint__3; @gw_eq_getint__2; @gw_eq_getint]; [@gw_eq_is_digit__3; @gw_eq_is_digit__2; @gw_eq_is_digit]; [@gw_eq_parse_dir__3; @gw_eq_parse_dir__2; @gw_eq_parse_dir]; [@gw_eq_parse_flags__3; @gw_eq_parse_flags__2; @gw_eq_parse_flags]; [@gw_eq_tyspec__3; @gw_eq_tyspec__2; @gw_eq_tyspec]]); first [GwInst.gw_exact (@QFau.parse_dir_shape) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.parse_dir_shape)]. Qed.

Lemma tyspec_shape : ltac2:(Q6nq.tyx '(@QFau.tyspec_shape) [[@gw_eq_conv_type__3; @gw_eq_conv_type__2; @gw_eq_conv_type]; [@gw_eq_conv_type_l__3; @gw_eq_conv_type_l__2; @gw_eq_conv_type_l]; [@gw_eq_tyspec__3; @gw_eq_tyspec__2; @gw_eq_tyspec]; [@gw_eq_flagw__3; @gw_eq_flagw__2; @gw_eq_flagw]] '([108]%Z : list Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_conv_type__3; @gw_eq_conv_type__2; @gw_eq_conv_type]; [@gw_eq_conv_type_l__3; @gw_eq_conv_type_l__2; @gw_eq_conv_type_l]; [@gw_eq_tyspec__3; @gw_eq_tyspec__2; @gw_eq_tyspec]]); first [GwInst.gw_exact (@QFau.tyspec_shape) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.tyspec_shape)]. Qed.
Lemma conv_type_l_ty : forall t ty, conv_type_l t = Some ty -> (ty = T_LONG /\ (t = 100 \/ t = 105)) \/ (ty = T_ULONG /\ t = 117).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_T_LONG__3; @gw_eq_T_LONG__2; @gw_eq_T_LONG]; [@gw_eq_conv_type_l__3; @gw_eq_conv_type_l__2; @gw_eq_conv_type_l]]); first [GwInst.gw_exact (@QFau.conv_type_l_ty) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.conv_type_l_ty)]. Qed.
Lemma conv_type_l_conv_type : forall t ty, conv_type_l t = Some ty -> exists ty0, conv_type t = Some ty0.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_conv_type__3; @gw_eq_conv_type__2; @gw_eq_conv_type]; [@gw_eq_conv_type_l__3; @gw_eq_conv_type_l__2; @gw_eq_conv_type_l]]); first [GwInst.gw_exact (@QFau.conv_type_l_conv_type) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.conv_type_l_conv_type)]. Qed.

Definition STATES1 : list Z :=
[25; 0; 0; 0; 25; 25; 25; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 14; 0; 0; 0; 0; 0; 0; 0; 0; 25; 0; 11; 13; 25; 25; 25; 0; 13; 0; 0; 2; 0; 9; 14; 0; 0; 0; 9; 0; 14; 0; 0; 14; 0; 0].
Lemma gw_eq_STATES1 : @STATES1 = ltac:(GwInst.gw_term (@QFau.STATES1) (@STATES1)). Proof. unfold STATES1, QFau.STATES1; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_STATES1 : gw_eqs.
Lemma states1_conv : forall t ty, conv_type_l t = Some ty -> znth STATES1 (t - 65) = ty.
Proof. rewrite ?gw_eq_STATES1; ltac2:(GwEq.gw_rw [[@gw_eq_conv_type_l__3; @gw_eq_conv_type_l__2; @gw_eq_conv_type_l]]); first [GwInst.gw_exact (@QFau.states1_conv) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.states1_conv)]. Qed.
Lemma parse_dir_ty_ok : forall s d rest, parse_dir s = Some (d, rest) -> dir_ty_ok d.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_dir_ty_ok__3; @gw_eq_dir_ty_ok__2; @gw_eq_dir_ty_ok]; [@gw_eq_parse_dir__3; @gw_eq_parse_dir__2; @gw_eq_parse_dir]]); first [GwInst.gw_exact (@QFau.parse_dir_ty_ok) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.parse_dir_ty_ok)]. Qed.

Lemma parse_flags_suffix : forall s acc fl s1, parse_flags s acc = (fl, s1) -> exists n, s1 = skipn n s /\ (n <= length s)%nat.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_parse_flags__3; @gw_eq_parse_flags__2; @gw_eq_parse_flags]]); first [GwInst.gw_exact (@QFau.parse_flags_suffix) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.parse_flags_suffix)]. Qed.
Lemma getint_suffix : forall s acc w s1, getint s acc = Some (w, s1) -> exists n, s1 = skipn n s /\ (n <= length s)%nat.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_getint__3; @gw_eq_getint__2; @gw_eq_getint]]); first [GwInst.gw_exact (@QFau.getint_suffix) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.getint_suffix)]. Qed.

Definition STATES0 : list Z :=
[25; 0; 11; 0; 25; 25; 25; 0; 0; 0; 0; 5; 0; 0; 0; 0; 0; 0; 9; 0; 0; 0; 0; 11; 0; 0; 0; 0; 0; 0; 0; 0; 25; 0; 10; 10; 25; 25; 25; 3; 10; 7; 0; 1; 27; 9; 11; 24; 0; 0; 9; 6; 11; 0; 0; 11; 0; 6].
Lemma gw_eq_STATES0 : @STATES0 = ltac:(GwInst.gw_term (@QFau.STATES0) (@STATES0)). Proof. unfold STATES0, QFau.STATES0; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_STATES0 : gw_eqs.
Lemma conv_type_range : forall t ty, conv_type t = Some ty -> 65 <= t <= 122.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_conv_type__3; @gw_eq_conv_type__2; @gw_eq_conv_type]]); first [GwInst.gw_exact (@QFau.conv_type_range) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.conv_type_range)]. Qed.
Lemma states0_conv : forall t ty, conv_type t = Some ty -> znth STATES0 (t - 65) = ty.
Proof. rewrite ?gw_eq_STATES0; ltac2:(GwEq.gw_rw [[@gw_eq_conv_type__3; @gw_eq_conv_type__2; @gw_eq_conv_type]]); first [GwInst.gw_exact (@QFau.states0_conv) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.states0_conv)]. Qed.

Definition conv_target (t : Z) : Z :=
if t =? 115 then 0x1d850
else if (t =? 100) || (t =? 105) then 0x1d808
else if t =? 99 then 0x1d978
else if t =? 117 then 0x1d940
else if (t =? 120) || (t =? 88) then 0x1d9b8
else 0x1d7b8.

Lemma conv_type_ty : forall t ty, conv_type t = Some ty -> ty = 9 \/ ty = 10 \/ ty = 11 \/ ty = 25.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_conv_type__3; @gw_eq_conv_type__2; @gw_eq_conv_type]]); first [GwInst.gw_exact (@QFau.conv_type_ty) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.conv_type_ty)]. Qed.

Lemma land_M64_neg : forall x, - 2^64 <= x < 0 -> Z.land x 18446744073709551615 = x + 2^64.
Proof. first [GwInst.gw_exact (@QFau.land_M64_neg) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.land_M64_neg)]. Qed.

Lemma nzmask_bits : ltac2:(Q6nq.ty1 'GwI.segs '(@QFau.nzmask_bits) [[@gw_eq_flagw__3; @gw_eq_flagw__2; @gw_eq_flagw]; [@gw_eq_STATES1__3; @gw_eq_STATES1__2; @gw_eq_STATES1]; [@gw_eq_STATES0__3; @gw_eq_STATES0__2; @gw_eq_STATES0]] '([65536; 18446744073709486079]%Z : list Z) '(Q6nq.gwt_unf (@ZERO_PAD) gwt_X)).
Proof. first [GwApply.gw_by_name GwI.segs (@QFau.nzmask_bits) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QFau.nzmask_bits)]. Qed.
Lemma nzmask_eq : forall fl, 0 <= fl < 131072 -> Z.land fl 18446744073709486079 = Z.land fl (Z.lnot 65536).
Proof. first [GwApply.gw_by_name GwI.segs (@QFau.nzmask_eq) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QFau.nzmask_eq)]. Qed.
Lemma land_bound : forall a m, 0 <= a -> 0 <= m -> 0 <= Z.land a m <= a.
Proof. first [GwInst.gw_exact (@QFau.land_bound) | autorewrite with gw_eqs; GwInst.gw_exact (@QFau.land_bound)]. Qed.
