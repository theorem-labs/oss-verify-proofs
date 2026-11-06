(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YChd.v, with its module paths and module names changed; 551 of its 591 lines of code are new or changed and 505 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntObsS2.v, with its module paths and module names changed; 550 of its 725 lines of code are new or changed and 416 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC81 YC1g YC1h YC4b YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_disco_table_observe_c slot_observe slot_known CtrlParsed SightLib.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoYEntObsCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma s9_u_at_fb : forall (S : list byte) (k : nat), (k < length S)%nat -> u_at S (Z.of_nat k) 1 = CtrlParsed.fb S k.
Proof.
intros S k. unfold u_at, sub, CtrlParsed.fb. rewrite Nat2Z.id. revert S. induction k as [|k IH]; intros [|b S] Hk; cbn [length] in Hk; try lia.
- cbn [skipn firstn nth bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity.
- cbn [skipn nth]. apply IH. lia.
Qed.
Lemma s9_sight_S12 : forall S : list byte, disco_classify_c.sighting_ok S -> sighting_S1 S /\ sighting_S2 S.
Proof.
intros S (HL & HR & HD).
assert (Hb : 0 <= CtrlParsed.fu S 8 4 < 2 ^ 32).
{ unfold CtrlParsed.fu, CtrlParsed.fld. pose proof (bytes_le_to_Z_nonneg (firstn 4 (skipn 8 S))).
  pose proof (bytes_le_to_Z_bound (firstn 4 (skipn 8 S))) as Hu. rewrite length_firstn, length_skipn, HL in Hu. cbn in Hu. lia. }
assert (SW : bv_swrap 32 (CtrlParsed.fu S 8 4) = CtrlParsed.s32 (CtrlParsed.fu S 8 4)).
{ unfold CtrlParsed.s32. change (bv_swrap 32 (CtrlParsed.fu S 8 4)) with ((CtrlParsed.fu S 8 4 + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31).
  destruct (Z.ltb_spec (CtrlParsed.fu S 8 4) (2 ^ 31)); lia. }
split.
- unfold sighting_S1, s_role, s32_at. change (u_at S 8 4) with (CtrlParsed.fu S 8 4). rewrite SW. lia.
- unfold sighting_S2, s_hd, s_din, s_dout.
  change 12 with (Z.of_nat 12). change 13 with (Z.of_nat 13). change 14 with (Z.of_nat 14).
  rewrite !s9_u_at_fb by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *. lia.
Qed.

Lemma s9_bits_hi : forall x i, 0 <= x < 2 ^ 64 -> 64 <= i -> Z.testbit x i = false.
Proof.
intros x i Hx Hi. destruct (Z.eq_dec x 0) as [->|Hn]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply (proj1 (Z.log2_lt_pow2 x 64 ltac:(lia))); lia | lia].
Qed.
Lemma s9_xor_rng : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= Z.lxor a b < 2 ^ 64.
Proof.
intros a b Ha Hb.
assert (E : Z.lxor a b mod 2 ^ 64 = Z.lxor a b).
{ apply Z.bits_inj'. intros n Hn. destruct (Z.lt_ge_cases n 64).
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia. rewrite Z.lxor_spec, !s9_bits_hi by lia. reflexivity. }
rewrite <- E. apply Z.mod_pos_bound. lia.
Qed.
Lemma s9_or_rng : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= Z.lor a b < 2 ^ 64.
Proof.
intros a b Ha Hb.
assert (E : Z.lor a b mod 2 ^ 64 = Z.lor a b).
{ apply Z.bits_inj'. intros n Hn. destruct (Z.lt_ge_cases n 64).
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia. rewrite Z.lor_spec, !s9_bits_hi by lia. reflexivity. }
rewrite <- E. apply Z.mod_pos_bound. lia.
Qed.
Lemma s9_diff : forall a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7,
  0 <= a1 < 2 ^ 64 -> 0 <= b1 < 2 ^ 64 -> 0 <= a2 < 2 ^ 64 -> 0 <= b2 < 2 ^ 64 ->
  0 <= a3 < 2 ^ 64 -> 0 <= b3 < 2 ^ 64 -> 0 <= a4 < 2 ^ 64 -> 0 <= b4 < 2 ^ 64 ->
  0 <= a5 < 2 ^ 64 -> 0 <= b5 < 2 ^ 64 -> 0 <= a6 < 2 ^ 64 -> 0 <= b6 < 2 ^ 64 ->
  0 <= a7 < 2 ^ 64 -> 0 <= b7 < 2 ^ 64 ->
  (0 <? Z.lor (Z.lor (Z.lor (Z.lxor a1 b1) (Z.lor (Z.lxor a2 b2) (Z.lxor a3 b3)))
                     (Z.lor (Z.lor (Z.lxor a4 b4) (Z.lxor a5 b5)) (Z.lxor a6 b6))) (Z.lxor a7 b7)) =
  negb ((a1 =? b1) && (a2 =? b2) && (a3 =? b3) && (a4 =? b4) && (a5 =? b5) && (a6 =? b6) && (a7 =? b7)).
Proof.
intros.
assert (NN : 0 <= Z.lor (Z.lor (Z.lor (Z.lxor a1 b1) (Z.lor (Z.lxor a2 b2) (Z.lxor a3 b3)))
                     (Z.lor (Z.lor (Z.lxor a4 b4) (Z.lxor a5 b5)) (Z.lxor a6 b6))) (Z.lxor a7 b7))
  by (repeat first [apply Z.lor_nonneg; split | apply Z.lxor_nonneg; split]; intros; lia).
apply Bool.eq_iff_eq_true. rewrite Z.ltb_lt, Bool.negb_true_iff, <- Bool.not_true_iff_false.
rewrite !andb_true_iff, !Z.eqb_eq.
split.
- intros Hc ((((((E1 & E2) & E3) & E4) & E5) & E6) & E7).
  rewrite E1, E2, E3, E4, E5, E6, E7, !Z.lxor_nilpotent in Hc. vm_compute in Hc. discriminate.
- intros Hc. destruct (Z.eq_dec (Z.lor (Z.lor (Z.lor (Z.lxor a1 b1) (Z.lor (Z.lxor a2 b2) (Z.lxor a3 b3)))
                     (Z.lor (Z.lor (Z.lxor a4 b4) (Z.lxor a5 b5)) (Z.lxor a6 b6))) (Z.lxor a7 b7)) 0) as [Z0|Z0]; [|lia].
  exfalso. apply Hc. rewrite !Z.lor_eq_0_iff in Z0.
  destruct Z0 as (((Z1 & (Z2 & Z3)) & ((Z4 & Z5) & Z6)) & Z7).
  apply (proj1 (Z.lxor_eq_0_iff _ _)) in Z1, Z2, Z3, Z4, Z5, Z6, Z7.
  repeat split; assumption.
Qed.

Lemma s9_bool : forall A1 A2 A3 A4 A5 A6 A7 CH : bool,
  (negb A1 || negb (A2 && A3 && A4) || negb A5 || negb A6 || CH || negb A7) =
  (negb (A1 && A2 && A3 && A4 && A5 && A6 && A7) || CH).
Proof. intros [|] [|] [|] [|] [|] [|] [|] [|]; reflexivity. Qed.
Lemma s9_ltu : forall a b, 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 ->
  (u64 (bv_swrap 32 a) <? u64 (bv_swrap 32 b)) = (a <? b).
Proof.
intros a b Ha Hb. unfold u64.
change (bv_swrap 32 a) with ((a + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31).
change (bv_swrap 32 b) with ((b + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31).
apply Bool.eq_iff_eq_true. rewrite !Z.ltb_lt. lia.
Qed.
Ltac s9_rng :=
  lazymatch goal with
  | |- 0 <= Z.lor _ _ < 2 ^ 64 => apply s9_or_rng; s9_rng
  | |- 0 <= Z.lxor _ _ < 2 ^ 64 => apply s9_xor_rng; s9_rng
  | |- 0 <= _ mod 2 ^ 64 < 2 ^ 64 => apply Z.mod_pos_bound; lia
  | |- 0 <= (if ?b then 1 else 0) < 2 ^ 64 => destruct b; lia
  | |- _ => lia
  end.

Lemma s9_fields : forall (T Sg T' : list byte) (ow now ret ai : Z),
  length T = 400%nat -> length Sg = 24%nat -> 0 <= ai < n_of T -> 0 <= ai < 8 ->
  tbl_T2 T -> tbl_T4 T -> sighting_S1 Sg -> sighting_S2 Sg -> 0 <= ow <= 1 -> 0 <= now < 2 ^ 64 ->
  (T', ret) = reac_disco_table_observe_c.observe_known T Sg ow now ai ->
  role_of_e T' ai = slot_known.want_role (s_role Sg) (role_of_e T ai) /\
  hd_of T' ai = (if s_hd Sg =? 0 then hd_of T ai else 1) /\
  din_of T' ai = (if s_hd Sg =? 0 then din_of T ai else s_din Sg) /\
  dout_of T' ai = (if s_hd Sg =? 0 then dout_of T ai else s_dout Sg) /\
  reac_disco_table_observe_c.fam_of T' ai =
    (if s_fam Sg =? 0 then reac_disco_table_observe_c.fam_of T ai else s_fam Sg) /\
  reac_disco_table_observe_c.slots_of T' ai =
    (if s_slots Sg =? 0 then reac_disco_table_observe_c.slots_of T ai else s_slots Sg) /\
  s32_at T' (48 * ai + 20) =
    bv_swrap 32 (if reac_disco_table_observe_c.ch_of T ai <? s_ch Sg then s_ch Sg
                 else reac_disco_table_observe_c.ch_of T ai) /\
  owned_of T' ai = (if ow =? 0 then owned_of T ai else 1) /\
  u_at T' (48 * ai + 32) 8 = u_at T (48 * ai + 32) 8 /\
  u_at T' (48 * ai + 40) 8 = now /\
  ret = Z.b2z (slot_observe.c_any T Sg ow ai).
Proof.
intros T Sg T' ow now ret ai LT LS Hn Hr8 T2 T4 S1 S2 How Hnow E.
destruct (slot_observe.ok_facts T Sg ow now ai T' ret LT LS Hr8 E)
  as (_ & _ & _ & E8 & E12 & E13 & E14 & E15 & E16 & E20 & E24 & E32 & E40 & _ & Eret).
destruct (T4 ai Hn) as (HD & _ & OW).
split; [unfold role_of_e, s32_at, u_at; rewrite E8; apply slot_known.role_field; [exact S1 | exact (T2 ai Hn)]|].
split; [unfold hd_of, u_at; rewrite E12; apply slot_known.hd_field; [exact S2 | exact HD]|].
split; [unfold din_of, u_at; rewrite E13; apply slot_known.din_field; exact S2|].
split; [unfold dout_of, u_at; rewrite E14; apply slot_known.dout_field; exact S2|].
split; [unfold reac_disco_table_observe_c.fam_of, u_at; rewrite E15; apply slot_known.fam_field|].
split; [unfold reac_disco_table_observe_c.slots_of, u_at; rewrite E16; apply slot_known.slots_field|].
split; [unfold s32_at, u_at; rewrite E20; apply slot_known.ch_field|].
split; [unfold owned_of, s32_at, u_at; rewrite E24; apply slot_known.own_field; [exact How | exact OW]|].
split; [unfold u_at; rewrite E32; reflexivity|].
split; [unfold u_at; rewrite E40; rewrite Mem.bytes_le_to_Z_to_le_bytes by lia;
  replace (8 * Z.of_nat 8) with 64 by reflexivity; apply Z.mod_small; exact Hnow|].
rewrite Eret. destruct (slot_observe.c_any T Sg ow ai); reflexivity.
Qed.

Definition s9_sr (o : Z) : list sv :=
  map (fun r => match r with
                | 26%nat => SOff AT_F o
                | 7%nat => SExt true 32 (SOff 564 0)
                | _ => sr_x r end) (seq 0 32).
Definition s9_acs : list YP09.chunk :=
  [YP09.mkChunk 8 (CVal 8 (SExt true 32 (SOff 563 0))); YP09.mkChunk 48 (CVal 8 (SOff 565 0));
   YP09.mkChunk 320 (CVal 8 (SOff 566 0));
   YP09.mkChunk 352 (CVal 8 (SOff 567 0)); YP09.mkChunk 192 (CVal 8 (SOff 568 0));
   YP09.mkChunk 104 (CVal 8 (SOff 569 0)); YP09.mkChunk 96 (CVal 8 (SOff 570 0));
   YP09.mkChunk 80 (CVal 8 (SOff 571 0)); YP09.mkChunk 88 (CVal 8 (SOff 572 0));
   YP09.mkChunk 72 (CVal 8 (SOff 573 0)); YP09.mkChunk 296 (CVal 8 (SOff 574 0));
   YP09.mkChunk 0 (CVal 8 (SOff 575 0))].
Definition s9_fcs (ai : Z) : list YP09.chunk :=
  [YP09.mkChunk (2160 + 48 * ai + 20) (CVal 4 (SOff 563 0)); YP09.mkChunk (2160 + 48 * ai + 24) (CVal 4 (SOff 564 0));
   YP09.mkChunk (2160 + 48 * ai + 32) (CVal 8 (SOff 565 0)); YP09.mkChunk (2160 + 48 * ai + 40) (CVal 8 (SOff 566 0))].
Definition s9_x (T T' Sg : list byte) (ai : Z) : list word :=
  [w64 (u_at T' (48 * ai + 20) 4); w64 (u_at T' (48 * ai + 24) 4); w64 (u_at T' (48 * ai + 32) 8);
   w64 (u_at T' (48 * ai + 40) 8);
   w64 (role_of_e T ai); w64 (hd_of T ai); w64 (din_of T ai); w64 (dout_of T ai);
   w64 (reac_disco_table_observe_c.slots_of T ai); w64 (reac_disco_table_observe_c.fam_of T ai);
   w64 (owned_of T ai); w64 (u64 (s32_at T (48 * ai + 20))); w64 (u64 (bv_swrap 32 (s_ch Sg)))].

Section u.
Variable E : env.
Lemma s9_dn_sx32 : forall a u, ew E a = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff a 0)) = Z_to_bv 64 (bv_swrap 32 u).
Proof.
intros a u H Hu. rewrite denot_lit_U, U_SExt, (U_atom E a u H) by lia. cbv iota.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small u) by lia. exact (Z_to_bv64_canon _).
Qed.
Lemma s9_br_ne_refl : forall a, branch_taken BC_NE (sv_denot E a) (sv_denot E a) = false.
Proof. intros a. rewrite branch_ne_U, Z.eqb_refl. reflexivity. Qed.
Lemma s9_flag : forall a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 u7 a7 b7 c d r,
  ew E 546 = Z_to_bv 64 a1 -> ew E 567 = Z_to_bv 64 b1 -> ew E 555 = Z_to_bv 64 a2 -> ew E 568 = Z_to_bv 64 b2 ->
  ew E 552 = Z_to_bv 64 a3 -> ew E 569 = Z_to_bv 64 b3 -> ew E 545 = Z_to_bv 64 a4 -> ew E 570 = Z_to_bv 64 b4 ->
  ew E 554 = Z_to_bv 64 a5 -> ew E 571 = Z_to_bv 64 b5 -> ew E 553 = Z_to_bv 64 a6 -> ew E 572 = Z_to_bv 64 b6 ->
  ew E 564 = Z_to_bv 64 u7 -> ew E 573 = Z_to_bv 64 b7 -> ew E 574 = Z_to_bv 64 c -> ew E 575 = Z_to_bv 64 d ->
  ew E 536 = Z_to_bv 64 r ->
  0 <= a1 < 2 ^ 64 -> 0 <= b1 < 2 ^ 64 -> 0 <= a2 < 2 ^ 64 -> 0 <= b2 < 2 ^ 64 ->
  0 <= a3 < 2 ^ 64 -> 0 <= b3 < 2 ^ 64 -> 0 <= a4 < 2 ^ 64 -> 0 <= b4 < 2 ^ 64 ->
  0 <= a5 < 2 ^ 64 -> 0 <= b5 < 2 ^ 64 -> 0 <= a6 < 2 ^ 64 -> 0 <= b6 < 2 ^ 64 ->
  0 <= u7 < 2 ^ 32 -> bv_swrap 32 u7 = a7 -> 0 <= a7 < 2 ^ 64 -> 0 <= b7 < 2 ^ 64 ->
  0 <= c < 2 ^ 64 -> 0 <= d < 2 ^ 64 -> 0 <= r < 2 ^ 64 ->
  r = Z.b2z (negb ((a1 =? b1) && (a2 =? b2) && (a3 =? b3) && (a4 =? b4) && (a5 =? b5) && (a6 =? b6) && (a7 =? b7)) ||
             (c <? d)) ->
  sv_denot E
      (SAlu ALU_OR
         (SAlu ALU_SLTU (SLit 0)
            (SAlu ALU_OR
               (SAlu ALU_OR
                  (SAlu ALU_OR (SAlu ALU_XOR (SOff 546 0) (SOff 567 0))
                     (SAlu ALU_OR (SAlu ALU_XOR (SOff 555 0) (SOff 568 0))
                        (SAlu ALU_XOR (SOff 552 0) (SOff 569 0))))
                  (SAlu ALU_OR
                     (SAlu ALU_OR (SAlu ALU_XOR (SOff 545 0) (SOff 570 0))
                        (SAlu ALU_XOR (SOff 554 0) (SOff 571 0)))
                     (SAlu ALU_XOR (SOff 553 0) (SOff 572 0))))
               (SAlu ALU_XOR (SExt true 32 (SOff 564 0)) (SOff 573 0))))
         (SAlu ALU_SLTU (SOff 574 0) (SOff 575 0))) = sv_denot E (SOff 536 0).
Proof.
intros a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 u7 a7 b7 c d r
  E1 F1 E2 F2 E3 F3 E4 F4 E5 F5 E6 F6 E7 F7 EC ED ER
  R1 Q1 R2 Q2 R3 Q3 R4 Q4 R5 Q5 R6 Q6 R7 SW Ra7 Q7 RC RD RR Hr.
rewrite (denot_lit_U E (SOff 536 0)), (U_atom E 536 r ER RR).
rewrite denot_lit_U. f_equal.
rewrite !U_SAlu, U_SExt, U_SLit.
rewrite (U_atom E 546 a1 E1 R1), (U_atom E 567 b1 F1 Q1), (U_atom E 555 a2 E2 R2), (U_atom E 568 b2 F2 Q2),
  (U_atom E 552 a3 E3 R3), (U_atom E 569 b3 F3 Q3), (U_atom E 545 a4 E4 R4), (U_atom E 570 b4 F4 Q4),
  (U_atom E 554 a5 E5 R5), (U_atom E 571 b5 F5 Q5), (U_atom E 553 a6 E6 R6), (U_atom E 572 b6 F6 Q6),
  (U_atom E 564 u7 E7 ltac:(lia)), (U_atom E 573 b7 F7 Q7), (U_atom E 574 c EC RC), (U_atom E 575 d ED RD).
cbn [zalu_raw]. change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small u7 (2 ^ 32)) by lia. rewrite SW.
unfold zcanon, M64.
repeat (rewrite Z.mod_small by s9_rng).
rewrite s9_diff by lia. subst r.
destruct (negb ((a1 =? b1) && (a2 =? b2) && (a3 =? b3) && (a4 =? b4) && (a5 =? b5) && (a6 =? b6) && (a7 =? b7))),
  (c <? d); reflexivity.
Qed.
End u.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Lemma s9_vm_u64 : forall m a v, val_mem SEGS m a 8 v <-> val_mem SEGS m a 8 (u64 v).
Proof.
intros m a v. unfold val_mem, u64.
split; intros H k Hk; rewrite (H k Hk); first [unfold YO0f.le_byte | unfold YG0f.le_byte];
change (8 * Z.of_nat 8) with 64; rewrite ?Zmod_mod; reflexivity.
Qed.
Lemma s9_u_rng : forall (T : list byte) p (n : nat), 0 <= u_at T p n < 2 ^ (8 * Z.of_nat n).
Proof.
intros T p n. unfold u_at. pose proof (YK11.bytes_le_to_Z_nonneg (sub T p n)) as H0.
pose proof (YK11.bytes_le_to_Z_bound (sub T p n)) as H1.
assert (L : (length (sub T p n) <= n)%nat) by (unfold sub; rewrite length_firstn; lia).
split; [exact H0|]. eapply Z.lt_le_trans; [exact H1|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma s9_garr8_nth : forall (m : word -> option byte) base (L : list byte) j b,
  garr8 SEGS m base (map (fun b : byte => bv_unsigned b) L) -> nth_error L j = Some b ->
  mbyte SEGS m (base + Z.of_nat j) = Some b.
Proof.
intros m base L j b G Hj.
assert (Hl : (j < length L)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
rewrite (garr8_mbyte SEGS m base _ j G) by (rewrite length_map; exact Hl).
f_equal. rewrite (nth_error_nth _ j 0 (map_nth_error (fun b : byte => bv_unsigned b) j L Hj)). apply Z_to_bv_bv_unsigned.
Qed.
Lemma s9_ble_cons : forall (b : byte) bs, bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
intros b bs. cbn [bytes_le_to_Z]. pose proof (u8_range b) as Hb. pose proof (YK11.bytes_le_to_Z_nonneg bs) as Hr.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite <- Z.lxor_lor.
- rewrite Z.add_nocarry_lxor; [reflexivity|].
  apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
  + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
  + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
- apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
  + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
  + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
Qed.
Lemma s9_nth_le_byte : forall bs k (b : byte),
  nth_error bs k = Some b -> bv_unsigned b = (bytes_le_to_Z bs / 2 ^ (8 * Z.of_nat k)) mod 256.
Proof.
induction bs as [|b0 bs IHbs]; intros k b H; [destruct k; discriminate H|].
rewrite s9_ble_cons. pose proof (u8_range b0) as Hb0. pose proof (YK11.bytes_le_to_Z_nonneg bs) as Hr.
destruct k as [|k].
- cbn in H. injection H as <-. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r. lia.
- cbn [nth_error] in H. rewrite (IHbs k b H).
  replace (8 * Z.of_nat (Datatypes.S k)) with (8 + 8 * Z.of_nat k) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
  rewrite <- Z.div_div by lia. f_equal. f_equal. lia.
Qed.
Lemma s9_u_val : forall (m : word -> option byte) t (T : list byte) p (n : nat),
  length T = 400%nat -> garr8 SEGS m t (map (fun b : byte => bv_unsigned b) T) ->
  0 <= p -> p + Z.of_nat n <= 400 ->
  val_mem SEGS m (t + p) n (u_at T p n).
Proof.
intros m t T p n LT GT Hp Hpn k Hk.
assert (Hlen : length (sub T p n) = n) by (unfold sub; rewrite length_firstn, length_skipn, LT; lia).
pose proof (s9_u_rng T p n) as Hb.
destruct (nth_error T (Z.to_nat p + k)) as [b|] eqn:Hb2; [|apply nth_error_None in Hb2; lia].
replace (t + p + Z.of_nat k) with (t + Z.of_nat (Z.to_nat p + k)) by lia.
rewrite (s9_garr8_nth m t T _ b GT Hb2). f_equal.
rewrite le_byte_small by first [exact Hk | exact Hb].
assert (Hs : nth_error (sub T p n) k = Some b).
{ unfold sub. rewrite nth_error_firstn. destruct (Nat.ltb_spec k n); [|lia]. rewrite nth_error_skipn. exact Hb2. }
pose proof (s9_nth_le_byte _ _ _ Hs) as Hv.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite Z.shiftr_div_pow2 by lia. unfold u_at. rewrite <- Hv. first [reflexivity | symmetry; apply Z.mod_small; apply (u8_range b)].
Qed.
Lemma s9_reg_atom : forall cx E (regs : bvmap 5 word) X (r : nat), (r < 32)%nat ->
  ew (d_env cx E (obs_vals regs ++ X)) (AT_X + r) = getr regs (Z_to_bv 5 (Z.of_nat r)).
Proof.
intros cx E regs X r Hr.
assert (L : length (obs_vals regs) = 32%nat) by (unfold obs_vals; rewrite length_map, length_seq; reflexivity).
rewrite oy_d_env_x by (rewrite length_app; lia).
rewrite app_nth1 by lia. unfold obs_vals.
rewrite (nth_indep _ _ (getr regs (Z_to_bv 5 (Z.of_nat 0)))) by (rewrite length_map, length_seq; lia).
rewrite (map_nth (fun r0 => getr regs (Z_to_bv 5 (Z.of_nat r0)))), seq_nth by lia. reflexivity.
Qed.
Lemma s9_atom : forall cx E (regs : bvmap 5 word) X j, (j < length X)%nat ->
  ew (d_env cx E (obs_vals regs ++ X)) (563 + j) = nth j X (Z_to_bv 64 0).
Proof.
intros cx E regs X j Hj.
assert (L : length (obs_vals regs) = 32%nat) by (unfold obs_vals; rewrite length_map, length_seq; reflexivity).
replace (563 + j)%nat with (AT_X + (32 + j))%nat by (unfold AT_X; lia).
rewrite oy_d_env_x by (rewrite length_app; lia).
rewrite app_nth2 by lia. rewrite L. f_equal. lia.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis SEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis FACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BRT : d_body_rt_stmt B.
#[local] Notation DAT := (d_at B MT XM_LIB RLO RHI tfib_K).
#[local] Notation oc := (oc B).
#[local] Notation ob_c12 := (ob_c12 B MT XM_LIB RLO RHI tfib_K).
#[local] Notation r27 := (r27_in B MT XM_LIB RLO RHI tfib_K).

Lemma s9_regs_ok : forall cx E (regs : bvmap 5 word) o X, d_E cx E -> d_rL B cx regs -> 0 <= d_A cx < 2 ^ 64 ->
  getr regs 26 = w64 (d_FB cx + o) ->
  getr regs 7 = sv_denot (d_env cx E (obs_vals regs ++ X)) (SExt true 32 (SOff 564 0)) ->
  regs_ok (d_env cx E (obs_vals regs ++ X)) (s9_sr o) regs.
Proof.
intros cx E regs o X HE HL HA R26 R7.
pose proof HE as (EE & E32 & HEI & E60 & EF & ESH).
pose proof HL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
assert (LO : length (obs_vals regs) = 32%nat) by (unfold obs_vals; rewrite length_map, length_seq; reflexivity).
assert (D60 : sv_denot (d_env cx E (obs_vals regs ++ X)) (SOff 60 0) = w64 (d_A cx))
  by (rewrite sv_denot_SOff0, oy_d_env_old by (unfold AT_FL; lia); exact E60).
assert (D2 : sv_denot (d_env cx E (obs_vals regs ++ X)) (SOff 2 0) = w64 (d_S cx))
  by (rewrite sv_denot_SOff0, oy_d_env_old by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl);
      unfold w64, d_S, spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (D32 : sv_denot (d_env cx E (obs_vals regs ++ X)) (SOff 32 0) = w64 SHADOW_OFF)
  by (rewrite sv_denot_SOff0, oy_d_env_old by (unfold AT_FL; lia); exact E32).
assert (D529 : sv_denot (d_env cx E (obs_vals regs ++ X)) (SOff 529 0) = w64 (shadow_addr (d_FB cx)))
  by (rewrite sv_denot_SOff0, oy_d_env_old by (unfold AT_FL; lia); exact ESH).
assert (D516 : sv_denot (d_env cx E (obs_vals regs ++ X)) (SOff 516 o) = w64 (d_FB cx + o)).
{ cbn [sv_denot]. rewrite oy_d_env_old by (unfold AT_FL; lia). change 516%nat with AT_F. rewrite EF.
  unfold w64. rewrite oy_w64_add_w. reflexivity. }
assert (DX : forall j q, q = (AT_X + j)%nat -> (j < 32)%nat ->
  sv_denot (d_env cx E (obs_vals regs ++ X)) (SOff q 0) = nth j (obs_vals regs) (Z_to_bv 64 0)).
{ intros j q -> Hj. rewrite sv_denot_SOff0. rewrite oy_d_env_x by (rewrite length_app; lia).
  apply app_nth1. lia. }
apply regs_ok_by_cases. intros z Hz. cbv [all_regs In] in Hz.
repeat (destruct Hz as [<-|Hz];
  [ match goal with |- _ = sv_denot ?E0 (sr_get ?sr ?r0) =>
      let v := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with v end;
    lazymatch goal with
    | |- _ = sv_denot _ (SLit 0) => rewrite getr_zero; reflexivity
    | |- _ = sv_denot _ (SLit _) => cbn [sv_denot]; first [ exact H18 | exact H20 ]
    | |- _ = sv_denot _ (SExt true 32 (SOff 564 0)) => exact R7
    | |- _ = sv_denot _ (SOff 60 0) => rewrite D60;
        first [ exact H9 | unfold w64; rewrite <- Hsp; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned ]
    | |- _ = sv_denot _ (SOff 2 0) => rewrite D2; exact H8
    | |- _ = sv_denot _ (SOff 32 0) => rewrite D32; exact H19
    | |- _ = sv_denot _ (SOff 529 0) => rewrite D529; exact H27
    | |- _ = sv_denot _ (SOff 516 _) => rewrite D516; exact R26
    | |- _ = sv_denot _ (SOff ?q 0) =>
        let j := eval vm_compute in (q - 531)%nat in
        rewrite (DX j q eq_refl ltac:(lia)); unfold obs_vals; cbn [nth map seq];
        f_equal; vm_compute; reflexivity
    end
  | ]).
destruct Hz.
Qed.

Lemma s9_body_n : forall cx h n n' xb shf ly S W m, d_body B cx h n xb shf ly S W m ->
  0 <= n' <= Z.max 0 (c_n cx - 7) -> d_body B cx h n' xb shf ly S W m.
Proof.
intros cx h n n' xb shf ly S W m (T & G & Lk & H & Hf & Hs & Ho & Hb & (_ & Hg & Hoi) & Hi & Hoff & Hgeo & Hcn & Hstk & Haw) Hn.
exists T, G, Lk, H. exact (conj Hf (conj Hs (conj Ho (conj Hb (conj (conj Hn (conj Hg Hoi)) (conj Hi (conj Hoff (conj Hgeo (conj Hcn (conj Hstk Haw)))))))))).
Qed.

Lemma s9_land : forall (fq : YK11.FPState) cx h i n now op nb fr len Sg T' (regs : bvmap 5 word) ly3 S3 W mem3 md' k acc
    E ss ms,
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md' k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] -> 0 <= k <= EV_HEAD i + 1 ->
  st_nev S3 <= st_nev (c_S cx) + (EV_HEAD i + 1) ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT i + mo_malloc MT REC_MAX ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = R27_OFF ->
  (forall x, ms_mem ms x = mem3 x) -> d_rL B cx (ms_regs ms) ->
  oc cx h i n now op nb fr len Sg T' regs ly3 S3 W mem3 ->
  r27 cx h i (nb - len) now nb fr len W (mkCfg ms md').
Proof.
intros fq cx h i n now op nb fr len Sg T' regs ly3 S3 W mem3 md' k acc E ss ms
  HFRM0 HB HJ HFR Hk Hnev Hmo Hacc HS Hrv Hpc MEQ HrL' HOC.
pose proof (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hrv) as Hms. rewrite Hpc in Hms.
pose proof (oy_oc_pt B cx h i n now op nb fr len Sg T' regs (ms_regs ms) ly3 S3 W mem3 (ms_mem ms) BRT MEQ HrL' HOC) as HOC'.
destruct HOC' as (Hi & Hn & Hnow & Hop & Hop2 & HrL2 & Hsp0 & Hfrm & HSgl & HSg & HSf & HREC & Hlen & Hnb & HTl & HT & HTok & Hbody).
unfold r27_in, d_arm_at_pf, d_at.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md', k, acc.
split; [unfold cfg_at; rewrite Hms at 1; reflexivity|].
split; [exact HFRM0|]. split; [exact HB|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact Hk|]. split; [exact Hnev|].
split; [exact Hmo|]. split; [exact Hacc|].
split; [exact Hi|]. split; [lia|]. split; [exact Hnow|]. split; [exact HrL2|]. split; [exact I|].
split; [split; [exact Hfrm|]; split; [exact HREC|]; split; [exact Hlen | reflexivity]|].
split; [exact Hsp0|].
exact (s9_body_n cx h n (nb - len) _ _ _ _ _ _ Hbody ltac:(lia)).
Qed.

Lemma s9_seat : forall (fq : YK11.FPState) cx h i n now op nb fr len Sg T T' ai ow ret
    (regs : bvmap 5 word) ly3 S3 W mem3 md3 k E,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k ->
  d_E cx E -> Forall (region_ok SEGS E (rd W mem3)) (d_regions cx dsh_rec) ->
  rdword (aview SEGS (w_H W) mem3) (d_FB cx + fs_frame_bytes DFRAME_CLASS - 8) =
    Some (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) ->
  oc cx h i n now op nb fr len Sg T' regs ly3 S3 W mem3 ->
  length T = 400%nat -> tbl_T2 T -> tbl_T4 T -> 0 <= ai < n_of T -> 0 <= ai < 8 ->
  sighting_S1 Sg -> sighting_S2 Sg -> (ow = 0 \/ ow = 1) ->
  (T', ret) = reac_disco_table_observe_c.observe_known T Sg ow now ai ->
  ob_sp24 cx T Sg ai ow ret W mem3 -> ob_r12 cx T Sg ai ow ret regs ->
  regs_ok (d_env cx E (obs_vals regs ++ s9_x T T' Sg ai)) (s9_sr (2160 + 48 * ai)) regs /\
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E (obs_vals regs ++ s9_x T T' Sg ai))
    (ss_d OB_C12 (s9_sr (2160 + 48 * ai)) dsh_rec s9_acs (s9_fcs ai) [] (d_facts [] []))
    (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + OB_C12)) mem3 (YK11.seg_rom SEGS))).
Proof.
intros fq cx h i n now op nb fr len Sg T T' ai ow ret regs ly3 S3 W mem3 md3 k E
  HC HE HRG HFL HOC HTl HT2 HT4 Hai Hai8 HS1 HS2 How EK HSP HR.
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & (V208 & V320) & Hfrm & HSgl & HSg & HSf & HREC &
  Hlen & Hnb & HT'l & HT' & HT'ok & Hbody).
pose proof HC as (_ & HJ & _).
destruct (oy_A_range B cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_val as Hac.
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
destruct (s9_fields T Sg T' ow now ret ai HTl HSgl Hai Hai8 HT2 HT4 HS1 HS2 ltac:(lia) Hnow EK)
  as (F8 & F12 & F13 & F14 & F15 & F16 & F20 & F24 & F32 & F40 & Fret).
destruct (HT4 ai Hai) as (HD & _ & OW).
pose proof (HT2 ai Hai) as HRo.
destruct HSP as (S352 & S192 & S104 & S96 & S88 & S80 & S296 & S72 & S48 & S64 & S56 & S360 & S8 & S0).
destruct HR as (R26 & R24 & R21 & R14 & R23 & R22 & R15 & R7 & R5).
assert (Ho : forall v, oldv ai v = v) by (intros v; unfold oldv; destruct (Z.ltb_spec ai 0); [lia | reflexivity]).
rewrite !Ho in S352, S192, S104, S96, S88, S80, S296, S72, S48.
assert (XA : forall j, (j < 13)%nat -> ew (d_env cx E (obs_vals regs ++ s9_x T T' Sg ai)) (563 + j) =
  nth j (s9_x T T' Sg ai) (Z_to_bv 64 0)) by (intros j Hj; apply s9_atom; cbn; lia).
pose proof (XA 0%nat ltac:(lia)) as X0. pose proof (XA 1%nat ltac:(lia)) as X1. pose proof (XA 2%nat ltac:(lia)) as X2.
pose proof (XA 3%nat ltac:(lia)) as X3. pose proof (XA 4%nat ltac:(lia)) as X4. pose proof (XA 5%nat ltac:(lia)) as X5.
pose proof (XA 6%nat ltac:(lia)) as X6. pose proof (XA 7%nat ltac:(lia)) as X7. pose proof (XA 8%nat ltac:(lia)) as X8.
pose proof (XA 9%nat ltac:(lia)) as X9. pose proof (XA 10%nat ltac:(lia)) as X10. pose proof (XA 11%nat ltac:(lia)) as X11.
pose proof (XA 12%nat ltac:(lia)) as X12.
cbn [nth s9_x Nat.add] in X0, X1, X2, X3, X4, X5, X6, X7, X8, X9, X10, X11, X12.
clear XA.
pose proof (s9_u_rng T' (48 * ai + 20) 4) as U20. pose proof (s9_u_rng T' (48 * ai + 24) 4) as U24.
pose proof (s9_u_rng T' (48 * ai + 32) 8) as U32. pose proof (s9_u_rng T' (48 * ai + 40) 8) as U40.
pose proof (s9_u_rng T (48 * ai + 12) 1) as U12. pose proof (s9_u_rng T (48 * ai + 13) 1) as U13.
pose proof (s9_u_rng T (48 * ai + 14) 1) as U14. pose proof (s9_u_rng T (48 * ai + 15) 1) as U15.
pose proof (s9_u_rng T (48 * ai + 16) 1) as U16.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in U20, U24.
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in U32, U40.
change (2 ^ (8 * Z.of_nat 1)) with 256 in U12, U13, U14, U15, U16.
assert (W64U : forall v, Z_to_bv 64 (u64 v) = Z_to_bv 64 v) by (intros v; unfold u64; exact (Z_to_bv64_canon v)).
assert (SV : forall q v, ew (d_env cx E (obs_vals regs ++ s9_x T T' Sg ai)) q = w64 v ->
  sv_denot (d_env cx E (obs_vals regs ++ s9_x T T' Sg ai)) (SOff q 0) = Z_to_bv 64 v)
  by (intros q v Hq; rewrite sv_denot_SOff0, Hq; reflexivity).
assert (RK : regs_ok (d_env cx E (obs_vals regs ++ s9_x T T' Sg ai)) (s9_sr (2160 + 48 * ai)) regs).
{ apply (s9_regs_ok cx E regs (2160 + 48 * ai) _ HE HrL HAr2).
  { rewrite R26. unfold w64, d_obj, dobj_off. f_equal. lia. }
  rewrite R7, (s9_dn_sx32 _ 564 _ X1 U24).
  change (bv_swrap 32 (u_at T' (48 * ai + 24) 4)) with (owned_of T' ai). rewrite F24.
  destruct How as [-> | ->]; cbn [Z.eqb]; [|reflexivity].
  unfold w64. rewrite W64U. reflexivity. }
split; [exact RK|].
apply (SEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E OB_C12 (s9_sr (2160 + 48 * ai)) (obs_vals regs ++ s9_x T T' Sg ai)
  s9_acs (s9_fcs ai) [] (d_facts [] []) HC HE HRG HFL).
- exact RK.
- exact (FACTS LAWS cx ly3 S3 W mem3 md3 k E _ [] [] HC HE I I).
- unfold s9_acs. repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val SEGS _ _ _ 8 8 _ (u64 (bv_swrap 32 (u_at T' (48 * ai + 20) 4)))).
    * rewrite (s9_dn_sx32 _ 563 _ X0 U20). symmetry. apply W64U.
    * apply oy_u64_rng.
    * cbn; lia.
    * apply (proj1 (s9_vm_u64 _ _ _)). change (bv_swrap 32 (u_at T' (48 * ai + 20) 4)) with (s32_at T' (48 * ai + 20)).
      rewrite F20. exact S8.
  + apply (chunk_ok_val SEGS _ _ _ 48 8 _ (u_at T' (48 * ai + 32) 8)).
    * exact (SV 565%nat _ X2).
    * exact U32.
    * cbn; lia.
    * rewrite F32. apply (proj2 (s9_vm_u64 _ _ _)). exact S48.
  + apply (chunk_ok_val SEGS _ _ _ 320 8 _ (u_at T' (48 * ai + 40) 8)).
    * exact (SV 566%nat _ X3).
    * exact U40.
    * cbn; lia.
    * rewrite F40. exact V320.
  + apply (chunk_ok_val SEGS _ _ _ 352 8 _ (role_of_e T ai)).
    * exact (SV 567%nat _ X4).
    * lia.
    * cbn; lia.
    * apply (proj2 (s9_vm_u64 _ _ _)). exact S352.
  + apply (chunk_ok_val SEGS _ _ _ 192 8 _ (hd_of T ai)).
    * exact (SV 568%nat _ X5).
    * unfold hd_of. lia.
    * cbn; lia.
    * apply (proj2 (s9_vm_u64 _ _ _)). exact S192.
  + apply (chunk_ok_val SEGS _ _ _ 104 8 _ (din_of T ai)).
    * exact (SV 569%nat _ X6).
    * unfold din_of. lia.
    * cbn; lia.
    * apply (proj2 (s9_vm_u64 _ _ _)). exact S104.
  + apply (chunk_ok_val SEGS _ _ _ 96 8 _ (dout_of T ai)).
    * exact (SV 570%nat _ X7).
    * unfold dout_of. lia.
    * cbn; lia.
    * apply (proj2 (s9_vm_u64 _ _ _)). exact S96.
  + apply (chunk_ok_val SEGS _ _ _ 80 8 _ (reac_disco_table_observe_c.slots_of T ai)).
    * exact (SV 571%nat _ X8).
    * unfold reac_disco_table_observe_c.slots_of. lia.
    * cbn; lia.
    * apply (proj2 (s9_vm_u64 _ _ _)). exact S80.
  + apply (chunk_ok_val SEGS _ _ _ 88 8 _ (reac_disco_table_observe_c.fam_of T ai)).
    * exact (SV 572%nat _ X9).
    * unfold reac_disco_table_observe_c.fam_of. lia.
    * cbn; lia.
    * apply (proj2 (s9_vm_u64 _ _ _)). exact S88.
  + apply (chunk_ok_val SEGS _ _ _ 72 8 _ (owned_of T ai)).
    * exact (SV 573%nat _ X10).
    * destruct OW as [-> | ->]; lia.
    * cbn; lia.
    * apply (proj2 (s9_vm_u64 _ _ _)). exact S72.
  + apply (chunk_ok_val SEGS _ _ _ 296 8 _ (u64 (s32_at T (48 * ai + 20)))).
    * exact (SV 574%nat _ X11).
    * apply oy_u64_rng.
    * cbn; lia.
    * exact S296.
  + apply (chunk_ok_val SEGS _ _ _ 0 8 _ (u64 (bv_swrap 32 (s_ch Sg)))).
    * exact (SV 575%nat _ X12).
    * apply oy_u64_rng.
    * cbn; lia.
    * apply (proj1 (s9_vm_u64 _ _ _)). exact S0.
- unfold s9_fcs. repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val SEGS _ _ _ (2160 + 48 * ai + 20) 4 _ (u_at T' (48 * ai + 20) 4)).
    * exact (SV 563%nat _ X0).
    * exact U20.
    * cbn; lia.
    * replace (d_FB cx + (2160 + 48 * ai + 20)) with (d_obj cx OT + (48 * ai + 20)) by (unfold d_obj, dobj_off; lia).
      exact (s9_u_val _ _ T' (48 * ai + 20) 4 HT'l HT' ltac:(lia) ltac:(lia)).
  + apply (chunk_ok_val SEGS _ _ _ (2160 + 48 * ai + 24) 4 _ (u_at T' (48 * ai + 24) 4)).
    * exact (SV 564%nat _ X1).
    * exact U24.
    * cbn; lia.
    * replace (d_FB cx + (2160 + 48 * ai + 24)) with (d_obj cx OT + (48 * ai + 24)) by (unfold d_obj, dobj_off; lia).
      exact (s9_u_val _ _ T' (48 * ai + 24) 4 HT'l HT' ltac:(lia) ltac:(lia)).
  + apply (chunk_ok_val SEGS _ _ _ (2160 + 48 * ai + 32) 8 _ (u_at T' (48 * ai + 32) 8)).
    * exact (SV 565%nat _ X2).
    * exact U32.
    * cbn; lia.
    * replace (d_FB cx + (2160 + 48 * ai + 32)) with (d_obj cx OT + (48 * ai + 32)) by (unfold d_obj, dobj_off; lia).
      exact (s9_u_val _ _ T' (48 * ai + 32) 8 HT'l HT' ltac:(lia) ltac:(lia)).
  + apply (chunk_ok_val SEGS _ _ _ (2160 + 48 * ai + 40) 8 _ (u_at T' (48 * ai + 40) 8)).
    * exact (SV 566%nat _ X3).
    * exact U40.
    * cbn; lia.
    * replace (d_FB cx + (2160 + 48 * ai + 40)) with (d_obj cx OT + (48 * ai + 40)) by (unfold d_obj, dobj_off; lia).
      exact (s9_u_val _ _ T' (48 * ai + 40) 8 HT'l HT' ltac:(lia) ltac:(lia)).
- apply Forall_nil.
- exact I.
- apply Forall_nil.
- assert (Hc : ai = 0 \/ ai = 1 \/ ai = 2 \/ ai = 3 \/ ai = 4 \/ ai = 5 \/ ai = 6 \/ ai = 7) by lia.
  repeat (destruct Hc as [-> | Hc]; [vm_compute; reflexivity|]). subst ai. vm_compute; reflexivity.
Qed.

Lemma y2_rL_keep_s9 : forall cx (regs regs' : bvmap 5 word),
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv -> getr regs' r = getr regs r) ->
  d_rL B cx regs -> d_rL B cx regs'.
Proof.
intros cx regs regs' RG (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27). unfold d_rL, spZ in *.
rewrite (RG 2%bv ltac:(cbv; tauto)), (RG 3%bv ltac:(cbv; tauto)), (RG 4%bv ltac:(cbv; tauto)),
  (RG 8%bv ltac:(cbv; tauto)), (RG 9%bv ltac:(cbv; tauto)), (RG 19%bv ltac:(cbv; tauto)),
  (RG 18%bv ltac:(cbv; tauto)), (RG 20%bv ltac:(cbv; tauto)), (RG 27%bv ltac:(cbv; tauto)).
repeat split; assumption.
Qed.

Ltac s9_upd :=
  lazymatch goal with HF : frame_of _ _ ?m1 ?m2, MP : forall x, ?m1 x = ?m0 x |- _ =>
    let MP2 := fresh "MP" in
    assert (MP2 : forall x, m2 x = m0 x)
      by (intros x; rewrite (oy_frame_eq _ _ _ _ HF ltac:(vm_compute; reflexivity) x); apply MP);
    clear MP; rename MP2 into MP end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

Theorem ob_s9b2 : ob_seg9b2 B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op nb fr len Sg W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  T & T' & ai & ow & ret & HOC & HTl & HTok & HFR & Hai & How & HOM & HSP & HR).
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & HREC &
  Hlen & Hnb & HT'l & HT' & HT'ok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & _).
pose proof Hframe as (E & HdE & Hregs & Hflag & _).
pose proof HTok as (HT1 & HT2 & HT3 & HT4).
assert (Hai8 : 0 <= ai < 8) by (unfold tbl_T1 in HT1; lia).
pose proof HSf as (Hs50 & Hs1 & Hs2 & Hs3 & Hs4 & HSok & Hs5).
destruct (s9_sight_S12 Sg HSok) as (HS1 & HS2).
pose proof (slot_observe.known_arm T Sg ow now T' ret ai HFR (proj1 Hai) HOM) as EK.
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (oy_A_range B cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_val as Hac.
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
pose proof (s9_seat fq cx h i n now op nb fr len Sg T T' ai ow ret regs ly3 S3 W mem3 md3 k E HC HdE Hregs Hflag HOC
  HTl HT2 HT4 Hai Hai8 HS1 HS2 How EK HSP HR) as (RK & HS).
destruct (s9_fields T Sg T' ow now ret ai HTl HSgl Hai Hai8 HT2 HT4 HS1 HS2 ltac:(lia) Hnow EK)
  as (F8 & F12 & F13 & F14 & F15 & F16 & F20 & F24 & F32 & F40 & Fret).
destruct (HT4 ai Hai) as (HD & _ & OW).
pose proof (HT2 ai Hai) as HRo.
destruct HR as (R26 & R24 & R21 & R14 & R23 & R22 & R15 & R7 & R5).
assert (XA : forall j, (j < 13)%nat -> ew (d_env cx E (obs_vals regs ++ s9_x T T' Sg ai)) (563 + j) =
  nth j (s9_x T T' Sg ai) (Z_to_bv 64 0)) by (intros j Hj; apply s9_atom; cbn; lia).
pose proof (XA 1%nat ltac:(lia)) as X1. pose proof (XA 4%nat ltac:(lia)) as X4. pose proof (XA 5%nat ltac:(lia)) as X5.
pose proof (XA 6%nat ltac:(lia)) as X6. pose proof (XA 7%nat ltac:(lia)) as X7. pose proof (XA 8%nat ltac:(lia)) as X8.
pose proof (XA 9%nat ltac:(lia)) as X9. pose proof (XA 10%nat ltac:(lia)) as X10. pose proof (XA 11%nat ltac:(lia)) as X11.
pose proof (XA 12%nat ltac:(lia)) as X12.
cbn [nth s9_x Nat.add] in X1, X4, X5, X6, X7, X8, X9, X10, X11, X12.
clear XA.
assert (RA : forall (r : nat) w, (r < 32)%nat -> getr regs (Z_to_bv 5 (Z.of_nat r)) = w ->
  ew (d_env cx E (obs_vals regs ++ s9_x T T' Sg ai)) (AT_X + r) = w)
  by (intros r w Hr Hw; rewrite s9_reg_atom by exact Hr; exact Hw).
pose proof (RA 15%nat _ ltac:(lia) R15) as A15. pose proof (RA 24%nat _ ltac:(lia) R24) as A24.
pose proof (RA 21%nat _ ltac:(lia) R21) as A21. pose proof (RA 14%nat _ ltac:(lia) R14) as A14.
pose proof (RA 23%nat _ ltac:(lia) R23) as A23. pose proof (RA 22%nat _ ltac:(lia) R22) as A22.
pose proof (RA 5%nat _ ltac:(lia) R5) as A5.
cbn [AT_X Nat.add] in A15, A24, A21, A14, A23, A22, A5. clear RA.
pose proof (s9_u_rng T' (48 * ai + 24) 4) as U24. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in U24.
assert (B1 : forall (L : list byte) p, 0 <= u_at L p 1 < 256)
  by (intros L p; pose proof (s9_u_rng L p 1) as Hx; change (2 ^ (8 * Z.of_nat 1)) with 256 in Hx; exact Hx).
assert (Hret : ret = 0 \/ ret = 1) by (rewrite Fret; destruct (slot_observe.c_any T Sg ow ai); [right | left]; reflexivity).
assert (HWR : 0 <= slot_known.want_role (s_role Sg) (role_of_e T ai) <= 2)
  by (unfold slot_known.want_role; unfold sighting_S1 in HS1;
      destruct (s_role Sg =? 0), ((role_of_e T ai =? 1) && (s_role Sg =? 2)); lia).
assert (BOOL : ret = Z.b2z (negb
  ((u64 (if s_role Sg =? 0 then role_of_e T ai
         else if (role_of_e T ai =? 1) && (s_role Sg =? 2) then 1 else s_role Sg) =? role_of_e T ai) &&
   ((if s_hd Sg =? 0 then hd_of T ai else 1) =? hd_of T ai) &&
   ((if s_hd Sg =? 0 then din_of T ai else s_din Sg) =? din_of T ai) &&
   ((if s_hd Sg =? 0 then dout_of T ai else s_dout Sg) =? dout_of T ai) &&
   ((if s_slots Sg =? 0 then reac_disco_table_observe_c.slots_of T ai else s_slots Sg) =?
      reac_disco_table_observe_c.slots_of T ai) &&
   ((if s_fam Sg =? 0 then reac_disco_table_observe_c.fam_of T ai else s_fam Sg) =?
      reac_disco_table_observe_c.fam_of T ai) &&
   ((if ow =? 0 then owned_of T ai else 1) =? owned_of T ai)) ||
  (u64 (s32_at T (48 * ai + 20)) <? u64 (bv_swrap 32 (s_ch Sg))))).
{ rewrite Fret. f_equal. unfold slot_observe.c_any.
  rewrite <- (slot_known.fr_role T Sg ai HS1 HRo), <- (slot_known.fr_decl T Sg ai HS2 HD),
    <- (slot_known.fr_slots T Sg ai), <- (slot_known.fr_fam T Sg ai), <- (slot_known.fr_own T ow ai ltac:(lia) OW).
  unfold slot_observe.c_ch.
  change (s32_at T (48 * ai + 20)) with (bv_swrap 32 (reac_disco_table_observe_c.ch_of T ai)).
  pose proof (s9_u_rng T (48 * ai + 20) 4) as UC1. pose proof (s9_u_rng Sg 20 4) as UC2.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in UC1, UC2.
  rewrite s9_ltu by (unfold reac_disco_table_observe_c.ch_of, s_ch; lia).
  rewrite oy_u64_small by (unfold slot_known.want_role in HWR; lia).
  unfold slot_known.want_role. apply s9_bool. }
pose proof (s9_flag (d_env cx E (obs_vals regs ++ s9_x T T' Sg ai)) _ _ _ _ _ _ _ _ _ _ _ _ _
  (if ow =? 0 then owned_of T ai else 1) _ _ _ _
  A15 X4 A24 X5 A21 X6 A14 X7 A23 X8 A22 X9 X1 X10 X11 X12 A5
  (oy_u64_rng _) ltac:(lia)
  ltac:(destruct (s_hd Sg =? 0); [unfold hd_of; pose proof (B1 T (48 * ai + 12)) | ]; lia)
  ltac:(unfold hd_of; pose proof (B1 T (48 * ai + 12)); lia)
  ltac:(destruct (s_hd Sg =? 0); [unfold din_of; pose proof (B1 T (48 * ai + 13)) | unfold s_din; pose proof (B1 Sg 13)]; lia)
  ltac:(unfold din_of; pose proof (B1 T (48 * ai + 13)); lia)
  ltac:(destruct (s_hd Sg =? 0); [unfold dout_of; pose proof (B1 T (48 * ai + 14)) | unfold s_dout; pose proof (B1 Sg 14)]; lia)
  ltac:(unfold dout_of; pose proof (B1 T (48 * ai + 14)); lia)
  ltac:(destruct (s_slots Sg =? 0); [unfold reac_disco_table_observe_c.slots_of; pose proof (B1 T (48 * ai + 16)) |
        unfold s_slots; pose proof (B1 Sg 16)]; lia)
  ltac:(unfold reac_disco_table_observe_c.slots_of; pose proof (B1 T (48 * ai + 16)); lia)
  ltac:(destruct (s_fam Sg =? 0); [unfold reac_disco_table_observe_c.fam_of; pose proof (B1 T (48 * ai + 15)) |
        unfold s_fam; pose proof (B1 Sg 15)]; lia)
  ltac:(unfold reac_disco_table_observe_c.fam_of; pose proof (B1 T (48 * ai + 15)); lia)
  U24
  ltac:(change (bv_swrap 32 (u_at T' (48 * ai + 24) 4)) with (owned_of T' ai); exact F24)
  ltac:(destruct (ow =? 0); lia) ltac:(lia) (oy_u64_rng _) (oy_u64_rng _) ltac:(lia) BOOL) as FLAG.
pose proof (oy_d_E_env cx E (obs_vals regs ++ s9_x T T' Sg ai) HdE) as HdE'.
assert (HEI : img_env VAL A_LIM (d_env cx E (obs_vals regs ++ s9_x T T' Sg ai))) by exact (proj1 (proj2 (proj2 HdE'))).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (obs_vals regs ++ s9_x T T' Sg ai)) (rd W mem3)) by constructor.
set (Ev := d_env cx E (obs_vals regs ++ s9_x T T' Sg ai)) in *. clearbody Ev.
pose (RUN := paj_run (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS).
pose proof (paj_run_to (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
assert (MP : forall x, mem3 x = mem3 x) by reflexivity.
unfold cfg_at. change (w64 (BASE + OB_C12)) with (Z_to_bv 64 (BASE + OB_C12)).
assert (Hc : ai = 0 \/ ai = 1 \/ ai = 2 \/ ai = 3 \/ ai = 4 \/ ai = 5 \/ ai = 6 \/ ai = 7) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]].
all: unfold ss_d in HS; ro_base HS 516%nat; ro_base HS 529%nat; ro_base HS 60%nat.
all: paj_run_tok RUN HS HJ SHOK OBspan; [cbn [ss_mem]; repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil | s9_upd].
all: psrr_branch_tok RUN BR HS SHOK OBspan;
  [ exfalso; rewrite FLAG, s9_br_ne_refl in Hc; discriminate Hc
  | clear Hc;
    paj_run_to_tok RUNTO HS HJ SHOK OBspan R27_OFF;
    [cbn [ss_mem]; repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil | s9_upd];
    repeat rewrite wvb_collapse in HJ |- *;
    apply SRr_ret;
    lazymatch goal with HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msx) |- _ =>
      assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv -> getr (ms_regs msx) r = getr regs r)
        by (let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr;
            rewrite (st_ok_pi_restrict_reg _ _ _ msx r HSx), (RK r);
            cbv [In] in Hr; repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]); destruct Hr);
      apply (s9_land fq cx h i n now op nb fr len Sg T' regs ly3 S3 W mem3 _ k acc Ev ssx msx HFRM0 Hbase HJ Hfrs Hk Hnev Hmo Hacc
        HSx ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) MP
        (y2_rL_keep_s9 cx regs (ms_regs msx) RG HrL) HOC)
    end ].
Qed.

End h.
End f.
End d.
