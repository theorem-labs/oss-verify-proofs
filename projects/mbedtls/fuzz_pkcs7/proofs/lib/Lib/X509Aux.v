(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk CellsX AStep Asn1Aux.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac is_closed_term x :=
  match goal with
  | y : _ |- _ => lazymatch x with context [y] => fail 1 | _ => fail end
  | _ => idtac
  end.

Ltac fin_goal ::=
  lazymatch goal with
  | |- Z_to_bv _ ?x = Z_to_bv _ ?r =>
      first [ lazymatch x with
              | context [Z.b2z ?bb] =>
                  lazymatch bb with true => idtac | false => idtac end;
                  let v := eval vm_compute in (let u := x mod 2^64 in if u <? 2^63 then u else u - 2^64) in
                  unify r v; apply bv_eq; vm_compute; reflexivity
              end
            | is_evar r; is_closed_term x;
              (* [comment removed for export] *)
              let v := eval vm_compute in (let u := x mod 2^64 in if u <? 2^63 then u else u - 2^64) in
              is_Zlit v; unify r v; apply bv_eq; vm_compute; reflexivity
            | reflexivity ]
  | |- @eq (bv _) ?a _ => first [ reflexivity | match goal with H : a = _ |- _ => exact H end ]
  | |- rw_cells _ ?m ?A _ => match goal with H : rw_cells _ m A _ |- _ => exact H end
  | |- ro_cells _ ?m ?A _ => match goal with H : ro_cells _ m A _ |- _ => exact H end
  | |- bytes_at _ ?m ?A _ => match goal with H : bytes_at _ m A _ |- _ => exact H end
  | |- u8arr _ ?m ?A _ => match goal with H : u8arr _ m A _ |- _ => exact H end
  | |- stk _ ?m _ _ => match goal with H : stk _ m _ _ |- _ => exact H end
  | |- statics_ok _ _ ?m => match goal with H : statics_ok _ _ m |- _ => exact H end
  | |- _ => prune_disj; lia
  end.

(* [comment removed for export] *)
Ltac norm_lit e :=
  is_closed_term e;
  let v := eval vm_compute in (let u := e mod 2^64 in if u <? 2^63 then u else u - 2^64) in
  is_Zlit v;
  replace (Z_to_bv 64 e) with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity).

Lemma x509_err_addw : forall r base, -0x1000 < r <= 0 -> -0x8000 <= base <= 0 ->
  bv_swrap 32 (r + base) = r + base.
Proof. intros r base Hr Hb. apply swrap32_id. lia. Qed.

(* [comment removed for export] *)
Lemma swrap32_errsum : forall r c, -0x10000 < r <= 0 -> 2^64 - 0x10000 <= c < 2^64 ->
  bv_swrap 32 (r mod 2^64 + c) = r + (c - 2^64).
Proof.
  intros r c Hr Hc. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296.
  change (4294967296 `div` 2) with 2147483648.
  assert (E : r mod 2^64 = r + 18446744073709551616 \/ r mod 2^64 = r).
  { destruct (Z.eq_dec r 0) as [->|Hn]; [right; reflexivity| left].
    rewrite <- (Z.mod_add r 1) by lia. rewrite Z.mod_small by lia. lia. }
  destruct E as [E|E]; rewrite E.
  - replace (r + 18446744073709551616 + c + 2147483648) with ((r + (c - 2^64) + 2147483648) + 8589934592 * 4294967296) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
  - replace (r + c + 2147483648) with ((r + (c - 2^64) + 2147483648) + 4294967296 * 4294967296) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma signed_lit64 : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  destruct (Z.lt_ge_cases z 0).
  - rewrite <- (Z.mod_add z 1 (2^64)) by lia. rewrite Z.mod_small by lia.
    destruct (Z.ltb_spec (z + 1 * 2^64) (2^63)); lia.
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec z (2^63)); lia.
Qed.

(* [comment removed for export] *)
Ltac lia_nodisj := clear_disj; lia.
Ltac lia_one_disj :=
  match goal with H : _ \/ _ |- _ => destruct H as [H|H]; clear_disj; lia end.
Ltac lia_sep := first [ lia_nodisj | lia_one_disj | prune_disj; lia ].
Ltac slia ::=
  first [ exact I
        | lazymatch goal with |- _ /\ _ => split; [ lia_sep | slia ] end
        | lia_sep ].


(* [comment removed for export] *)
Ltac sf_a0x := first [ assumption | lia_nodisj ].
Ltac transport_chunks segs m a bs ::=
  let Ha := fresh "Ha_st" in let Hl := fresh "Hl_st" in
  try (assert (Ha : (0 <= a)%Z) by first [tb_light_a a | lia_nodisj]);
  try (assert (Hl : (a + Z.of_nat (length bs) <= 2^64)%Z) by first [tb_light_l a | (simpl_sizes; slia)]);
  (lazymatch goal with
   | Ha' : (0 <= a)%Z, Hl' : (a + Z.of_nat (length bs) <= 2^64)%Z |- _ => transport_batch segs m a bs Ha' Hl'
   | _ => idtac
   end);
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
              [ | sf_a0x | sf_al | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
              [ | sf_a0x | sf_al | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
              [ | sf_a0x | sf_al | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_frame segs m A2 xs a bs) in H;
              [ | sf_a0x | sf_al | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_frame segs m A2 xs a bs) in H;
              [ | sf_a0x | sf_al | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_frame segs m A2 xs a bs) in H;
              [ | sf_a0x | sf_al | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_frame segs m A2 xs a bs) in H;
              [ | sf_a0x | sf_al | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : HEAP _ _ ?HI ?h ?LB m ?mo |- _ =>
      first [ eapply (heap_write segs _ HI h LB m mo _ a bs) in H;
              [ | eassumption | simpl_sizes; solve_client_wrange | lia_nodisj | simpl_sizes; lia_nodisj ]
            | idtac "note: could not carry HEAP across the store (dropping):" H; clear H ]
  | H : pristine ?lo ?hi ?E m |- _ =>
      first [ apply (pristine_write lo hi E m a bs) in H;
              [ | lia_nodisj | simpl_sizes; lia_nodisj | intros; simpl_sizes; lia_sep ]
            | idtac "note: could not carry pristine across the store (dropping):" H; clear H ]
  | H : statics_ok segs ?L m |- _ =>
      first [ apply (statics_ok_write segs L m a bs) in H;
              [ | lia_nodisj | simpl_sizes; lia_nodisj | simpl_sizes; lia_sep ]
            | idtac "note: could not carry statics_ok across the store (dropping):" H; clear H ]
  end;
  try clear Ha; try clear Hl.

Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  (* [comment removed for export] *)
  repeat match goal with
  | H : rw_cells segs m ?A2 _ |- _ => lazymatch W with context [(A2, _)] => clear H end
  | H : bytes_at segs m ?A2 _ |- _ => lazymatch W with context [(A2, _)] => clear H end
  end;
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : statics_ok segs ?L m |- _ =>
      first [ apply (statics_ok_munch segs L W m m') in H; [ | exact MU | cbn [outside]; intros; slia ]
            | idtac "note: dropping statics_ok (callee footprint not provably outside the data range):" H; clear H ]
  | H : pristine ?lo ?hi ?E m |- _ =>
      first [ apply (pristine_munch lo hi E W m m') in H; [ | exact MU | cbn [outside]; intros; slia ]
            | idtac "note: dropping pristine (callee footprint not provably outside its range):" H; clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; cbn [outside]; intros; slia | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

(* [comment removed for export] *)
Lemma Z_to_bv64_mod : forall x, Z_to_bv 64 (x mod 2^64) = Z_to_bv 64 x.
Proof.
  intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). apply Z.mod_mod. lia.
Qed.

Lemma x509_err_select : forall r c, -0x1000 < r <= 0 -> 2^64 - 0x10000 <= c < 2^64 - 0x1000 ->
  exists r', Z_to_bv 64 (Z.land ((Z.b2z (r mod 18446744073709551616 <? 1) + -1) mod 18446744073709551616)
                                ((bv_swrap 32 (r mod 18446744073709551616 + c)) mod 18446744073709551616))
             = Z_to_bv 64 r'
          /\ -0x11000 < r' <= 0 /\ (r' = 0 <-> r = 0) /\ (r <> 0 -> r' = r + (c - 2^64)).
Proof.
  intros r c Hr Hc. change 18446744073709551616 with (2^64). destruct (Z.eq_dec r 0) as [->|Hn].
  - exists 0. rewrite Z.mod_0_l by lia. cbn [Z.ltb Z.b2z]. change ((1 + -1) mod 2^64) with 0. rewrite Z.land_0_l.
    repeat split; lia.
  - exists (r + (c - 2^64)).
    assert (E : r mod 2^64 = r + 2^64) by (rewrite <- (Z.mod_add r 1) by lia; rewrite Z.mod_small by lia; lia).
    rewrite swrap32_errsum by lia.
    rewrite E at 1. replace (r + 2^64 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
    change ((0 + -1) mod 2^64) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
    rewrite Z.mod_mod by lia. rewrite Z_to_bv64_mod.
    repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma x509_mismatch_select : forall a b c, 0 <= a -> 0 <= b -> 0 <= c < 2^64 ->
  exists r', Z_to_bv 64 (Z.land ((Z.b2z (Z.lxor a b <? 1) + -1) mod 18446744073709551616) c) = Z_to_bv 64 r'
          /\ (r' = 0 <-> a = b) /\ (a <> b -> r' = c - 2^64).
Proof.
  intros a b c Ha Hb Hc. change 18446744073709551616 with (2^64). destruct (Z.eq_dec a b) as [<-|Hn].
  - exists 0. replace (Z.lxor a a <? 1) with true by (symmetry; apply Z.ltb_lt; apply lxor_eq_small).
    cbn [Z.b2z]. change ((1 + -1) mod 2^64) with 0. rewrite Z.land_0_l. repeat split; lia.
  - exists (c - 2^64).
    replace (Z.lxor a b <? 1) with false.
    2:{ symmetry. apply Z.ltb_ge. destruct (Z_lt_le_dec (Z.lxor a b) 1) as [Hl|Hl]; [| lia]. exfalso. apply Hn. apply lxor_small_eq; assumption. }
    cbn [Z.b2z]. change ((0 + -1) mod 2^64) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
    rewrite Z.mod_small by lia. rewrite <- (Z_to_bv64_mod (c - 2^64)).
    replace ((c - 2^64) mod 2^64) with c by (rewrite <- (Z.mod_add (c - 2^64) 1) by lia; rewrite Z.mod_small by lia; lia).
    repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma ltb_true_of : forall x y, x < y -> (x <? y) = true.
Proof. intros. apply Z.ltb_lt. assumption. Qed.
Lemma ltb_false_of : forall x y, y <= x -> (x <? y) = false.
Proof. intros. apply Z.ltb_ge. assumption. Qed.
Lemma eqb_false_of : forall x y, x <> y -> (x =? y) = false.
Proof. intros. apply Z.eqb_neq. assumption. Qed.
Lemma eqb_true_of : forall x y, x = y -> (x =? y) = true.
Proof. intros. apply Z.eqb_eq. assumption. Qed.

(* [comment removed for export] *)
Ltac decide_atoms_in K :=
  repeat first [ rewrite ltb_true_of in K by (clear_disj; lia)
               | rewrite ltb_false_of in K by (clear_disj; lia)
               | rewrite eqb_true_of in K by (clear_disj; lia)
               | rewrite eqb_false_of in K by (clear_disj; lia) ].
Ltac kill_bool K := exfalso; rewrite ?land_7_mod, ?land_3_mod, ?land_1_mod, ?land_15_mod in K; decide_atoms_in K; cbv in K;
  first [ lia | congruence | exact K | apply K; reflexivity ].

(* [comment removed for export] *)
Lemma mask_select : forall (b : bool) c, 0 <= c < 2^64 ->
  exists r', Z_to_bv 64 (Z.land ((Z.b2z b + -1) mod 18446744073709551616) c) = Z_to_bv 64 r'
          /\ (r' = 0 \/ r' = c - 2^64).
Proof.
  intros b c Hc. change 18446744073709551616 with (2^64). destruct b; cbn [Z.b2z].
  - exists 0. change ((1 + -1) mod 2^64) with 0. rewrite Z.land_0_l. split; [reflexivity| left; reflexivity].
  - exists (c - 2^64). change ((0 + -1) mod 2^64) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
    rewrite Z.mod_small by lia. rewrite <- (Z_to_bv64_mod (c - 2^64)).
    replace ((c - 2^64) mod 2^64) with c by (rewrite <- (Z.mod_add (c - 2^64) 1) by lia; rewrite Z.mod_small by lia; lia).
    split; [reflexivity| right; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma land_le_l : forall a b, 0 <= a -> Z.land a b <= a.
Proof.
  intros a b Ha. pose proof (Z.sub_land_same_l a b) as E. rewrite <- Z.ldiff_land in E.
  pose proof (proj2 (Z.ldiff_nonneg a b) (or_introl Ha)). lia.
Qed.

Ltac kill_land K :=
  exfalso;
  match type of K with
  | Z.land ?a ?b = _ => pose proof (land_le_l a b ltac:(clear_disj; lia)); clear_disj; lia
  | _ = Z.land ?a ?b => pose proof (land_le_l a b ltac:(clear_disj; lia)); clear_disj; lia
  end.
