(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 501 of its 566 lines of code are new or changed and 1213 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntBodyStmt DiscoEntSeat DiscoArm3 DiscoArm3AgeSt DiscoArm3AgeKit ReacDiscoTableAge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c reac_disco_table_age_c slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition lf_sx (r : nat) : sv :=
  match r with
  | 0%nat => SLit 0 | 2%nat => SOff AT_A 0 | 8%nat => SOff AT_STK 0 | 9%nat => SOff AT_A 0 | 18%nat => SOff 32 0
  | 19%nat => SOff (AT_X + 22) 0 | 24%nat => SOff AT_F 2160
  | _ => SOff (AT_X + r) 0
  end.
Definition lf_sr : list sv := map lf_sx (seq 0 32).
Definition lf_vals (regs : bvmap 5 word) (now : Z) (T1 : list byte) : list word :=
  map (fun r => getr regs (Z_to_bv 5 (Z.of_nat r))) (seq 0 32) ++
  [Z_to_bv 64 now; Z_to_bv 64 (u_at T1 384 4); Z_to_bv 64 (seq_of T1)] ++
  map (fun j => Z_to_bv 64 (last_of T1 (Z.of_nat j))) (seq 0 8).
Definition lf_acs : list YP09.chunk := [YP09.mkChunk 344 (CVal 8 (SOff (AT_X + 32) 0))].
Definition lf_ls : list YP09.chunk :=
  map (fun j => YP09.mkChunk (2200 + 48 * Z.of_nat j) (CVal 8 (SOff (AT_X + 35 + j) 0))) (seq 0 8).
Definition lf_fcs : list YP09.chunk :=
  YP09.mkChunk 2544 (CVal 4 (SOff (AT_X + 33) 0)) :: YP09.mkChunk 2552 (CVal 4 (SOff (AT_X + 34) 0)) :: lf_ls.

Lemma zbv_eq : forall x y, x mod 2 ^ 64 = y mod 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof. intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). exact H. Qed.
Lemma U_any : forall E x a, sv_denot E x = Z_to_bv 64 a -> U E x = a mod 2 ^ 64.
Proof. intros E x a H. unfold U. rewrite H, Z_to_bv_unsigned. reflexivity. Qed.
Lemma mod64_32 : forall a, (a mod 2 ^ 64) mod 2 ^ 32 = a mod 2 ^ 32.
Proof. intros a. Z.div_mod_to_equations. lia. Qed.
Lemma sw32_congr : forall x y, x mod 2 ^ 32 = y mod 2 ^ 32 -> bv_swrap 32 x = bv_swrap 32 y.
Proof.
intros x y H. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
rewrite (Zplus_mod x), (Zplus_mod y), H. reflexivity.
Qed.
Lemma sw32_mod : forall z, bv_swrap 32 z mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
intros z. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
Z.div_mod_to_equations. lia.
Qed.
Lemma sw32_id : forall z, - 2 ^ 31 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
rewrite Z.mod_small by lia. lia.
Qed.
Lemma sw64_id : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> bv_swrap 64 z = z.
Proof.
intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_small by lia. lia.
Qed.
Lemma dn_lit : forall E c, sv_denot E (SLit c) = Z_to_bv 64 c.
Proof. reflexivity. Qed.
Lemma dn_atom : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma dn_add : forall E x y a b, sv_denot E x = Z_to_bv 64 a -> sv_denot E y = Z_to_bv 64 b ->
  sv_denot E (SAlu ALU_ADD x y) = Z_to_bv 64 (a + b).
Proof.
intros E x y a b Hx Hy. rewrite denot_lit_U, U_SAlu. cbn [zalu_raw].
rewrite (U_any E x a Hx), (U_any E y b Hy). apply zbv_eq. unfold zcanon, M64.
rewrite Z.mod_mod by lia. rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma dn_mul : forall E x y a b, sv_denot E x = Z_to_bv 64 a -> sv_denot E y = Z_to_bv 64 b ->
  sv_denot E (SMd M_MUL x y) = Z_to_bv 64 (a * b).
Proof.
intros E x y a b Hx Hy. rewrite denot_lit_U, U_SMd. cbn [zmd_raw].
rewrite (U_any E x a Hx), (U_any E y b Hy). apply zbv_eq. unfold zcanon, M64.
rewrite Z.mod_mod by lia. rewrite <- Zmult_mod. reflexivity.
Qed.
Lemma dn_sltu : forall E x y a b, sv_denot E x = Z_to_bv 64 a -> sv_denot E y = Z_to_bv 64 b ->
  sv_denot E (SAlu ALU_SLTU x y) = Z_to_bv 64 (if a mod 2 ^ 64 <? b mod 2 ^ 64 then 1 else 0).
Proof.
intros E x y a b Hx Hy. rewrite denot_lit_U, U_SAlu. cbn [zalu_raw].
rewrite (U_any E x a Hx), (U_any E y b Hy). apply zbv_eq. unfold zcanon, M64. apply Z.mod_mod. lia.
Qed.
Lemma dn_and : forall E x y a b, sv_denot E x = Z_to_bv 64 a -> sv_denot E y = Z_to_bv 64 b ->
  sv_denot E (SAlu ALU_AND x y) = Z_to_bv 64 (Z.land (a mod 2 ^ 64) (b mod 2 ^ 64)).
Proof.
intros E x y a b Hx Hy. rewrite denot_lit_U, U_SAlu. cbn [zalu_raw].
rewrite (U_any E x a Hx), (U_any E y b Hy). apply zbv_eq. unfold zcanon, M64. apply Z.mod_mod. lia.
Qed.
Lemma dn_sext32 : forall E x a, sv_denot E x = Z_to_bv 64 a ->
  sv_denot E (SExt true 32 x) = Z_to_bv 64 (bv_swrap 32 a).
Proof.
intros E x a Hx. rewrite denot_lit_U, U_SExt. rewrite (U_any E x a Hx). apply zbv_eq. unfold zcanon, M64.
rewrite Z.mod_mod by lia. f_equal. change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite mod64_32.
apply sw32_congr. apply Z.mod_mod. lia.
Qed.
Lemma dn_S : forall E v, sv_denot E v = Z_to_bv 64 (Sg E v).
Proof.
intros E v. rewrite denot_lit_U, U_of_S. apply zbv_eq. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_mod. lia.
Qed.
Lemma dn_addw : forall E x y a b, sv_denot E x = Z_to_bv 64 a -> sv_denot E y = Z_to_bv 64 b ->
  sv_denot E (SAluw ALU_ADD x y) = Z_to_bv 64 (bv_swrap 32 (a + b)).
Proof.
intros E x y a b Hx Hy. rewrite dn_S, S_SAluw. cbn [zalu_raw].
rewrite (U_any E x a Hx), (U_any E y b Hy), !mod64_32. f_equal. apply sw32_congr.
rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma dn_subw : forall E x y a b, sv_denot E x = Z_to_bv 64 a -> sv_denot E y = Z_to_bv 64 b ->
  sv_denot E (SAluw ALU_SUB x y) = Z_to_bv 64 (bv_swrap 32 (a - b)).
Proof.
intros E x y a b Hx Hy. rewrite dn_S, S_SAluw. cbn [zalu_raw].
rewrite (U_any E x a Hx), (U_any E y b Hy), !mod64_32. f_equal. apply sw32_congr.
rewrite <- Zminus_mod. reflexivity.
Qed.
Lemma dn_kx : forall E n op, ew E n = Z_to_bv 64 op -> 0 <= op < 256 ->
  sv_denot E (SAlu ALU_SRL (SAlu ALU_SLL (SOff n 0) (SLit 57)) (SLit 59)) = Z_to_bv 64 (slot_ser_defs.ser_k op).
Proof.
intros E n op Hn Hop. rewrite denot_lit_U, U_SAlu, U_SAlu, !U_SLit, (U_atom E n op Hn) by lia.
cbn [zalu_raw]. change (Z.land (zcanon 57) 63) with 57. change (Z.land (zcanon 59) 63) with 59.
unfold slot_ser_defs.ser_k. change 31 with (Z.ones 5). rewrite Z.land_ones by lia.
rewrite Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
apply zbv_eq. unfold zcanon, M64. Z.div_mod_to_equations. lia.
Qed.
Lemma ser_k_range : forall op, 0 <= slot_ser_defs.ser_k op < 32.
Proof.
intros op. unfold slot_ser_defs.ser_k. change 31 with (Z.ones 5). rewrite Z.land_ones by lia.
apply Z.mod_pos_bound. lia.
Qed.
Lemma dn_stale0 : forall E nl nn ns l t, ew E nl = Z_to_bv 64 l -> ew E nn = Z_to_bv 64 t ->
  ew E ns = Z_to_bv 64 REAC_DISCO_STALE_NS -> 0 <= l < 2 ^ 64 -> 0 <= t < 2 ^ 64 ->
  ((l <? t) && (REAC_DISCO_STALE_NS <? t - l))%bool = false ->
  sv_denot E (SAlu ALU_AND (SAlu ALU_SLTU (SOff nl 0) (SOff nn 0))
    (SAlu ALU_SLTU (SOff ns 0) (SAlu ALU_ADD (SOff nn 0) (SMd M_MUL (SOff nl 0) (SLit (-1)))))) = Z_to_bv 64 0.
Proof.
intros E nl nn ns l t Hl Ht Hs Rl Rt Hb.
rewrite (dn_and E _ _ _ _ (dn_sltu E _ _ _ _ (dn_atom E nl l Hl) (dn_atom E nn t Ht))
  (dn_sltu E _ _ _ _ (dn_atom E ns _ Hs) (dn_add E _ _ _ _ (dn_atom E nn t Ht) (dn_mul E _ _ _ _ (dn_atom E nl l Hl) (dn_lit E (-1)))))).
rewrite (Z.mod_small l), (Z.mod_small t) by lia.
change (REAC_DISCO_STALE_NS mod 2 ^ 64) with REAC_DISCO_STALE_NS.
destruct (Z.ltb_spec l t) as [Hlt|Hge].
- cbn [andb] in Hb. replace (t + l * -1) with (t - l) by lia. rewrite (Z.mod_small (t - l)) by lia. rewrite Hb. reflexivity.
- rewrite Z.mod_0_l by lia. rewrite Z.land_0_l. reflexivity.
Qed.
Lemma dn_add00 : forall E x y, sv_denot E x = Z_to_bv 64 0 -> sv_denot E y = Z_to_bv 64 0 ->
  sv_denot E (SAlu ALU_ADD x y) = Z_to_bv 64 0.
Proof. intros E x y Hx Hy. exact (dn_add E x y 0 0 Hx Hy). Qed.
Lemma dn_sltu1 : forall E x, sv_denot E x = Z_to_bv 64 0 -> sv_denot E (SAlu ALU_SLTU x (SLit 1)) = Z_to_bv 64 1.
Proof. intros E x Hx. rewrite (dn_sltu E x (SLit 1) 0 1 Hx (dn_lit E 1)). reflexivity. Qed.
Lemma bt_eq_s : forall u v, - 2 ^ 63 <= u < 2 ^ 63 -> - 2 ^ 63 <= v < 2 ^ 63 ->
  branch_taken BC_EQ (Z_to_bv 64 u) (Z_to_bv 64 v) = (u =? v).
Proof.
intros u v Hu Hv. cbn [branch_taken]. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64).
destruct (Z.eqb_spec u v) as [->|Hne]; [apply Z.eqb_refl|]. apply Z.eqb_neq. intros Hm. apply Hne.
Z.div_mod_to_equations. lia.
Qed.
Lemma bt_ne_s : forall u v, - 2 ^ 63 <= u < 2 ^ 63 -> - 2 ^ 63 <= v < 2 ^ 63 ->
  branch_taken BC_NE (Z_to_bv 64 u) (Z_to_bv 64 v) = negb (u =? v).
Proof.
intros u v Hu Hv. change (branch_taken BC_NE (Z_to_bv 64 u) (Z_to_bv 64 v)) with (negb (branch_taken BC_EQ (Z_to_bv 64 u) (Z_to_bv 64 v))).
rewrite bt_eq_s by assumption. reflexivity.
Qed.
Lemma bt_lt_s : forall u v, - 2 ^ 63 <= u < 2 ^ 63 -> - 2 ^ 63 <= v < 2 ^ 63 ->
  branch_taken BC_LT (Z_to_bv 64 u) (Z_to_bv 64 v) = (u <? v).
Proof.
intros u v Hu Hv. cbn [branch_taken]. unfold bv_lts. rewrite !Z_to_bv_signed, !sw64_id by assumption. reflexivity.
Qed.
Lemma bt_ge_s : forall u v, - 2 ^ 63 <= u < 2 ^ 63 -> - 2 ^ 63 <= v < 2 ^ 63 ->
  branch_taken BC_GE (Z_to_bv 64 u) (Z_to_bv 64 v) = negb (u <? v).
Proof.
intros u v Hu Hv. change (branch_taken BC_GE (Z_to_bv 64 u) (Z_to_bv 64 v)) with (negb (branch_taken BC_LT (Z_to_bv 64 u) (Z_to_bv 64 v))).
rewrite bt_lt_s by assumption. reflexivity.
Qed.
Lemma ck_sub : forall E t n0 rm,
  sv_denot E (SExt true 32 (SOff 564 0)) = Z_to_bv 64 t -> ew E 554 = Z_to_bv 64 n0 -> ew E 553 = Z_to_bv 64 rm ->
  0 <= t < 2 ^ 31 -> t = n0 - rm ->
  branch_taken BC_EQ (sv_denot E (SExt true 32 (SOff 564 0))) (sv_denot E (SAluw ALU_SUB (SOff 554 0) (SOff 553 0))) = true.
Proof.
intros E t n0 rm Ht H554 H553 Rt Heq.
rewrite Ht, (dn_subw E _ _ _ _ (dn_atom E 554 n0 H554) (dn_atom E 553 rm H553)), <- Heq, sw32_id by lia.
rewrite bt_eq_s by lia. apply Z.eqb_refl.
Qed.
Lemma ck_seq : forall E s1 s0 rm,
  ew E 565 = Z_to_bv 64 s1 -> ew E 552 = Z_to_bv 64 s0 -> ew E 553 = Z_to_bv 64 rm -> 0 <= rm < 2 ^ 64 ->
  s1 mod 2 ^ 32 = (s0 + (if 0 <? rm then 1 else 0)) mod 2 ^ 32 ->
  branch_taken BC_EQ (sv_denot E (SExt true 32 (SOff 565 0)))
    (sv_denot E (SAluw ALU_ADD (SOff 552 0) (SAlu ALU_SLTU (SLit 0) (SOff 553 0)))) = true.
Proof.
intros E s1 s0 rm H565 H552 H553 Rrm Hm.
rewrite (dn_sext32 E _ _ (dn_atom E 565 s1 H565)),
  (dn_addw E _ _ _ _ (dn_atom E 552 s0 H552) (dn_sltu E _ _ _ _ (dn_lit E 0) (dn_atom E 553 rm H553))).
rewrite Z.mod_0_l, (Z.mod_small rm) by lia. rewrite (sw32_congr s1 _ Hm).
cbn [branch_taken]. unfold bv_eqb. apply Z.eqb_refl.
Qed.
Lemma seq_rel : forall (b : bool) a, 0 <= a < 2 ^ 32 ->
  (if b then (a + 1) mod 2 ^ 32 else a) mod 2 ^ 32 = (bv_swrap 32 a + (if b then 1 else 0)) mod 2 ^ 32.
Proof.
intros b a Ha. destruct b.
- rewrite Z.mod_mod by lia. rewrite (Zplus_mod (bv_swrap 32 a)), sw32_mod, <- Zplus_mod. reflexivity.
- rewrite Z.add_0_r, sw32_mod. reflexivity.
Qed.

Ltac lf_ro HS n :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.

Ltac lf_dn TNX KX :=
lazymatch goal with
| |- sv_denot _ (SLit _) = _ => apply dn_lit
| |- sv_denot _ (SExt true 32 (SOff 564 0)) = _ => exact TNX
| |- sv_denot _ (SAlu ALU_SRL (SAlu ALU_SLL (SOff 558 0) (SLit 57)) (SLit 59)) = _ => exact KX
| |- sv_denot _ (SAlu ALU_ADD _ _) = _ => eapply dn_add; [lf_dn TNX KX | lf_dn TNX KX]
| |- sv_denot _ (SMd M_MUL _ _) = _ => eapply dn_mul; [lf_dn TNX KX | lf_dn TNX KX]
end.

Ltac lf_bp H :=
repeat lazymatch type of H with
  | negb _ = true => apply (proj1 (Bool.negb_true_iff _)) in H
  | negb _ = false => apply (proj1 (Bool.negb_false_iff _)) in H
  | (_ =? _) = true => apply (proj1 (Z.eqb_eq _ _)) in H
  | (_ =? _) = false => apply (proj1 (Z.eqb_neq _ _)) in H
  | (_ <? _) = true => apply (proj1 (Z.ltb_lt _ _)) in H
  | (_ <? _) = false => apply (proj1 (Z.ltb_ge _ _)) in H
  end.

Lemma lf_ro_pt : forall E rs (m m' : word -> option byte), frame_of E rs m m' ->
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> forall x, m' x = m x.
Proof.
intros E rs m m' HF Hro x. apply HF. intros (r & Hin & Ha).
rewrite forallb_forall in Hro. specialize (Hro r Hin). apply Z.leb_le in Hro. lia.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma lf_vm_pt : forall (m m' : word -> option byte) a n v, (forall x, m' x = m x) ->
  val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof. intros m m' a n v Hpt H kk Hk. pose proof (H kk Hk) as H1. unfold mbyte in H1 |- *. rewrite Hpt. exact H1. Qed.
Lemma lf_ga_pt : forall (m m' : word -> option byte) a l, (forall x, m' x = m x) ->
  garr8 SEGS m a l -> garr8 SEGS m' a l.
Proof. intros m m' a l Hpt H j Hj. destruct (H j Hj) as [H1 H2]. split; [exact (lf_vm_pt m m' _ _ _ Hpt H1) | exact H2]. Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DBKEEP : d_body_keep_stmt B.

Lemma lf_regs_ok : forall cx E regs now T1, d_E cx E -> d_rL B cx regs ->
  getr regs 19 = getr regs 22 -> getr regs 24 = w64 (d_obj cx OT) ->
  0 <= d_A cx < 2 ^ 64 -> 0 <= d_FB cx -> d_FB cx + 4096 <= 2 ^ 64 ->
  regs_ok (d_env cx E (lf_vals regs now T1)) lf_sr regs.
Proof.
intros cx E regs now T1 HE HL H1922 H24 HA HF0 HF1.
destruct HE as (HER & H32 & _ & HA60 & HF516 & _).
destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
apply regs_ok_by_cases. intros r Hr.
cbv [all_regs In] in Hr.
assert (H2 : getr regs 2 = Z_to_bv 64 (d_A cx)) by (rewrite <- Hsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HS2 : ew E 2 = Z_to_bv 64 (d_S cx)).
{ rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
change AT_A with 60%nat in HA60. change AT_F with 516%nat in HF516.
repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
all: match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
  let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
  cbn [sv_denot].
all: first
  [ rewrite getr_zero; reflexivity
  | rewrite Z.add_0_r; rewrite d_env_old by (cbv; lia);
    first [ rewrite HA60, Z_to_bv_bv_unsigned; first [exact H2 | exact H9]
          | rewrite HS2, Z_to_bv_bv_unsigned; exact H8
          | rewrite H32; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H18 ]
  | rewrite d_env_old by (cbv; lia); rewrite HF516, unsigned_lit_small by lia; rewrite H24;
    unfold w64, d_obj, dobj_off; reflexivity
  | rewrite Z.add_0_r; unfold d_env, havoc; cbn [ew Nat.ltb Nat.leb Nat.sub nth lf_vals map seq Nat.add app AT_X AT_FL];
    match goal with |- getr ?rg _ = Z_to_bv 64 (bv_unsigned (getr ?rg ?x)) =>
      let y := eval vm_compute in x in change x with y end;
    rewrite Z_to_bv_bv_unsigned; first [reflexivity | exact H1922] ].
Qed.

Lemma lf_ew : forall cx E regs now T1,
  ew (d_env cx E (lf_vals regs now T1)) 563 = Z_to_bv 64 now /\
  ew (d_env cx E (lf_vals regs now T1)) 564 = Z_to_bv 64 (u_at T1 384 4) /\
  ew (d_env cx E (lf_vals regs now T1)) 565 = Z_to_bv 64 (seq_of T1) /\
  ew (d_env cx E (lf_vals regs now T1)) 552 = getr regs 21 /\
  ew (d_env cx E (lf_vals regs now T1)) 553 = getr regs 22 /\
  ew (d_env cx E (lf_vals regs now T1)) 554 = getr regs 23 /\
  ew (d_env cx E (lf_vals regs now T1)) 557 = getr regs 26 /\
  ew (d_env cx E (lf_vals regs now T1)) 558 = getr regs 27 /\
  (forall j, (j < 8)%nat -> ew (d_env cx E (lf_vals regs now T1)) (566 + j) = Z_to_bv 64 (last_of T1 (Z.of_nat j))).
Proof.
intros cx E regs now T1.
repeat match goal with |- _ /\ _ => split end;
  try (unfold d_env, havoc; cbn [ew Nat.ltb Nat.leb Nat.sub nth lf_vals map seq Nat.add app AT_X AT_FL];
       first [ reflexivity
             | match goal with |- getr ?rg ?x = getr ?rg ?y =>
                 let x' := eval vm_compute in x in let y' := eval vm_compute in y in
                 change x with x'; change y with y'; reflexivity end ]).
intros j Hj.
do 8 (destruct j as [|j]; [unfold d_env, havoc; cbn [ew Nat.ltb Nat.leb Nat.sub nth lf_vals map seq Nat.add app AT_X AT_FL]; reflexivity|]).
lia.
Qed.

Lemma lf_fcs_ok : forall cx E regs now T1 (m : word -> option byte),
  length T1 = 400%nat -> 0 <= n_of T1 ->
  garr8 SEGS m (d_obj cx OT) (map (fun b : byte => bv_unsigned b) T1) ->
  Forall (YP09.chunk_ok SEGS (d_env cx E (lf_vals regs now T1)) m (d_FB cx)) lf_fcs.
Proof.
intros cx E regs now T1 m HL Hn HG.
pose proof (lf_ew cx E regs now T1) as (_ & E564 & E565 & _ & _ & _ & _ & _ & ELS).
assert (HOT : d_obj cx OT = d_FB cx + 2160) by reflexivity.
assert (UB : forall k (nn : nat), 0 <= u_at T1 k nn < 2 ^ (8 * Z.of_nat nn)).
{ intros k nn. unfold u_at. pose proof (PropExec.bytes_le_to_Z_bound (sub T1 k nn)) as Hb.
  pose proof (PropExec.bytes_le_to_Z_nonneg (sub T1 k nn)) as Hb0.
  assert (LS : (length (sub T1 k nn) <= nn)%nat) by (unfold sub; rewrite length_firstn; lia).
  split; [exact Hb0|]. eapply Z.lt_le_trans; [exact Hb|]. apply Z.pow_le_mono_r; lia. }
constructor; [|constructor].
- apply (chunk_ok_val SEGS _ m (d_FB cx) 2544 4 (SOff (AT_X + 33) 0) (u_at T1 384 4));
    [apply dn_atom; exact E564 | exact (UB 384 4%nat) | lia |].
  replace (d_FB cx + 2544) with (d_obj cx OT + 384) by (rewrite HOT; lia).
  apply (age_val m T1 (d_obj cx OT) 384 4 HG); [lia | rewrite HL; lia].
- apply (chunk_ok_val SEGS _ m (d_FB cx) 2552 4 (SOff (AT_X + 34) 0) (seq_of T1));
    [apply dn_atom; exact E565 | exact (UB 392 4%nat) | lia |].
  replace (d_FB cx + 2552) with (d_obj cx OT + 392) by (rewrite HOT; lia).
  apply (age_val m T1 (d_obj cx OT) 392 4 HG); [lia | rewrite HL; lia].
- unfold lf_ls. apply Forall_map. apply Forall_forall. intros j Hj. apply in_seq in Hj.
  apply (chunk_ok_val SEGS _ m (d_FB cx) (2200 + 48 * Z.of_nat j) 8 (SOff (AT_X + 35 + j) 0) (last_of T1 (Z.of_nat j)));
    [apply dn_atom; replace (AT_X + 35 + j)%nat with (566 + j)%nat by (unfold AT_X; lia); apply ELS; lia
    | exact (UB (48 * Z.of_nat j + 40) 8%nat) | lia |].
  replace (d_FB cx + (2200 + 48 * Z.of_nat j)) with (d_obj cx OT + (48 * Z.of_nat j + 40)) by (rewrite HOT; lia).
  apply (age_val m T1 (d_obj cx OT) (48 * Z.of_nat j + 40) 8 HG); [lia | rewrite HL; lia].
Qed.

Lemma lf_leaf : forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (removed : Z)
  (W : world SEGS) (fq : YK11.FPState) ly3 S3 (regs : bvmap 5 word) mem3 k acc (E : env) (vals : list word)
  (ss : sstate) (ms : machine_state) (md : Model),
  a3_from B MT XM_LIB RLO RHI tfib_K cx h i n now op T0 W0 c0 W ->
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx -> frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= EV_HEAD i -> st_nev S3 <= st_nev (c_S cx) + EV_HEAD i ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT i + mo_malloc MT REC_MAX ->
  0 <= i < MAX_OPS -> 0 <= n -> 0 <= now < 2 ^ 64 ->
  d_rL B cx regs -> d_sp0 cx i now W mem3 -> d_sp1 cx i n now W mem3 -> a3_aged cx now T0 T1 removed W mem3 ->
  d_body B cx h n [] dsh_loop ly3 S3 W mem3 -> d_E cx E ->
  st_ok (fx := fq) SEGS (d_env cx E vals) ss (restrict (w_H W) ms) ->
  ss_pc ss = SIGMA DS___interceptor_trampoline_malloc -> ss_resv ss = None ->
  d_land_chk dsh_loop (ss_mem ss) = true ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md k ->
  (forall x, ms_mem ms x = mem3 x) -> (forall x, rd W (ms_mem ms) x = rd W mem3 x) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 25]%bv -> getr (ms_regs ms) r = getr regs r) ->
  getr (ms_regs ms) 1 = w64 (BASE + P_MAL_RA) -> getr (ms_regs ms) 10 = w64 (a3_cap op) ->
  getr (ms_regs ms) 19 = w64 (a3_cap op) ->
  p_mal B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 W (mkCfg ms md).
Proof.
intros cx h i n now op W0 c0 T0 T1 removed W fq ly3 S3 regs mem3 k acc E vals ss ms md
  HFROM Hfrm0 Hbase Hfrs Hk Hnev Hmo Hacc Hi Hn Hnow HrL Hsp0 Hsp1 Hag Hbody HdE HS Hpc Hrv Hchk HJ HPT HPTR RG R1 R10 R19.
destruct ss as [p0 r0 f0 m0 v0 g0]. cbn [ss_pc ss_resv ss_mem] in Hpc, Hrv, Hchk. subst p0 v0.
assert (HSpi : st_ok_pi SEGS VAL (d_env cx E vals)
  (mkSST (SIGMA DS___interceptor_trampoline_malloc - BASE) r0 f0 m0 None g0) (restrict (w_H W) ms)).
{ unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
  replace (BASE + (SIGMA DS___interceptor_trampoline_malloc - BASE)) with (SIGMA DS___interceptor_trampoline_malloc) by ring.
  exact HS. }
assert (R2 := RG 2%bv ltac:(cbv; tauto)). assert (R3 := RG 3%bv ltac:(cbv; tauto)). assert (R4 := RG 4%bv ltac:(cbv; tauto)).
assert (R8 := RG 8%bv ltac:(cbv; tauto)). assert (R9 := RG 9%bv ltac:(cbv; tauto)). assert (R18 := RG 18%bv ltac:(cbv; tauto)).
assert (R20 := RG 20%bv ltac:(cbv; tauto)). assert (R25 := RG 25%bv ltac:(cbv; tauto)).
destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
destruct Hsp0 as (Hs1 & Hs2). destruct Hsp1 as ((Ht1 & Ht2) & Ht3 & Ht4). destruct Hag as (Hmod & Hpost & HT1).
unfold p_mal. split; [exact HFROM|].
apply (a3_land_keep B MT XM_LIB RLO RHI tfib_K LAWS FFL DLAND DBKEEP fq cx
  (SIGMA DS___interceptor_trampoline_malloc - BASE) (EV_HEAD i) h i n n now _ _ W ly3 S3 mem3 md k acc
  (d_env cx E vals) _ ms (d_S cx) (d_S cx)
  Hfrm0 Hbase HJ Hfrs Hk Hnev Hmo Hacc Hi ltac:(lia) Hnow Hbody HSpi eq_refl eq_refl
  (d_E_env cx E vals HdE) (d_env_fl cx E vals) Hchk).
- unfold LLVMF_STK. lia.
- lia.
- intros a Ha _. apply aview_eq_of. apply HPTR.
- intros a _ (Hh & b & Hb). split; [exact Hh|]. exists b. rewrite HPT. exact Hb.
- intros a _ Ha. lia.
- split; [unfold spZ in *; rewrite R2; exact Hsp|].
  split; [rewrite R3; exact Hgp|]. split; [rewrite R4; exact Htp|]. split; [rewrite R8; exact H8|].
  split; [rewrite R9; exact H9|]. split; [rewrite R18; exact H18|]. split; [rewrite R20; exact H20|].
  rewrite R25; exact H25.
- split; [exact R1 | split; [exact R10 | exact R19]].
- split.
  + split; [split; [exact (lf_vm_pt _ _ _ _ _ HPTR Ht1) | exact (lf_vm_pt _ _ _ _ _ HPTR Ht2)]|].
    split; [exact (lf_vm_pt _ _ _ _ _ HPTR Ht3) | exact (lf_vm_pt _ _ _ _ _ HPTR Ht4)].
  + split; [exists removed; split; [exact Hmod | exact Hpost]|]. exact (lf_ga_pt _ _ _ _ HPTR HT1).
- split; [exact (lf_vm_pt _ _ _ _ _ HPTR Hs1) | exact (lf_vm_pt _ _ _ _ _ HPTR Hs2)].
Qed.

Theorem a3_e_left : e_left_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W0 c0 T0 T1 removed W c [HFROM HQ].
destruct HQ as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Hi & Hn & Hnow & HrL & (H19 & H22 & H21 & H23 & H24 & H26 & H27) & (Hsp1 & Hag) & Hsp0 & Hbody).
assert (Hop : 0 <= op < 256).
{ destruct HFROM as (Harm & _). destruct Harm as (fq0 & ly0 & S0 & regs0 & mem0 & md0 & k0 & acc0 & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & Hop0 & _). exact Hop0. }
pose proof Hag as (Hmod & Hpost & HT1).
pose proof Hpost as (HlenT1 & Hrem & Hrem0 & HnT1 & Hstale & Hseq & Hok1 & _ & _).
pose proof Hok1 as (HT1n & _). unfold tbl_T1 in HT1n.
pose proof Hbody as (Tb & Gb & Lkb & Hb & Hframe & Hshadow & _).
pose proof Hframe as (E & HdE & Hregs & Hflag & Hh216 & Hh152).
assert (Hctx : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k Hctx)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
pose proof asan_consts as (Hac & _).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
set (vals := lf_vals regs now T1).
assert (HSro : regs_ok (d_env cx E vals) lf_sr regs).
{ apply lf_regs_ok; [exact HdE | exact HrL | rewrite H19, H22; reflexivity | exact H24 | unfold MFRAME, LLVMF_STK in *; lia | lia | lia]. }
pose proof (DFACTS LAWS cx ly3 S3 W mem3 md3 k E vals [] [] Hctx HdE I I) as Hfacts.
assert (Hacs : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_A cx)) lf_acs).
{ constructor; [|constructor].
  pose proof (lf_ew cx E regs now T1) as (E563 & _).
  apply (chunk_ok_val SEGS _ _ (d_A cx) 344 8 (SOff (AT_X + 32) 0) now); [apply dn_atom; exact E563 | lia | lia |].
  exact (proj2 Hsp0). }
pose proof (lf_fcs_ok cx E regs now T1 (rd W mem3) HlenT1 ltac:(lia) HT1) as Hfcs.
pose proof (DSEAT LAWS TL fq cx dsh_loop ly3 S3 W regs mem3 md3 k E 0x9c4 lf_sr vals lf_acs lf_fcs [] (d_facts [] [])
  Hctx HdE Hregs Hflag HSro Hfacts Hacs Hfcs (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
lf_ro HS 516%nat. lf_ro HS 529%nat. lf_ro HS 60%nat.
assert (HEI : img_env VAL A_LIM (d_env cx E vals)).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. rewrite d_env_old by (unfold A_LIM, AT_FL in *; lia). exact (HI a Ha). }
pose proof (lf_ew cx E regs now T1) as (E563 & E564 & E565 & E552 & E553 & E554 & E557 & E558 & ELS).
fold vals in E563, E564, E565, E552, E553, E554, E557, E558, ELS.
rewrite H21 in E552. rewrite H22 in E553. rewrite H23 in E554. rewrite H26 in E557. rewrite H27 in E558.
assert (HnU : u_at T1 384 4 = n_of T1) by (apply u_of_n; [exact HlenT1 | lia]).
assert (TNX : sv_denot (d_env cx E vals) (SExt true 32 (SOff 564 0)) = Z_to_bv 64 (n_of T1)).
{ rewrite (dn_sext32 _ _ _ (dn_atom _ 564 _ E564)). reflexivity. }
assert (KX : sv_denot (d_env cx E vals) (SAlu ALU_SRL (SAlu ALU_SLL (SOff 558 0) (SLit 57)) (SLit 59)) =
  Z_to_bv 64 (slot_ser_defs.ser_k op)) by (exact (dn_kx _ 558 op E558 Hop)).
pose proof (ser_k_range op) as KR.
assert (CK1 := ck_sub (d_env cx E vals) (n_of T1) (n_of T0) removed TNX E554 E553 ltac:(lia) HnT1).
assert (CK3 : branch_taken BC_EQ (sv_denot (d_env cx E vals) (SExt true 32 (SOff 565 0)))
    (sv_denot (d_env cx E vals) (SAluw ALU_ADD (SOff 552 0) (SAlu ALU_SLTU (SLit 0) (SOff 553 0)))) = true).
{ assert (HnT0 : n_of T0 < 2 ^ 31).
  { unfold n_of, s32_at, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
    pose proof (Z.mod_pos_bound (u_at T0 384 4 + 2 ^ 31) (2 ^ 32) ltac:(lia)). lia. }
  assert (Hrm64 : 0 <= removed < 2 ^ 64) by lia.
  apply (ck_seq _ (seq_of T1) (s32_at T0 392) removed E565 E552 E553 Hrm64).
  assert (Hs0 : 0 <= seq_of T0 < 2 ^ 32).
  { unfold seq_of, u_at. pose proof (PropExec.bytes_le_to_Z_bound (sub T0 392 4)) as Hb1.
    pose proof (PropExec.bytes_le_to_Z_nonneg (sub T0 392 4)) as Hb0.
    assert (LS : (length (sub T0 392 4) <= 4)%nat) by (unfold sub; rewrite length_firstn; lia).
    split; [exact Hb0|]. eapply Z.lt_le_trans; [exact Hb1|]. apply Z.pow_le_mono_r; lia. }
  rewrite Hseq. exact (seq_rel (0 <? removed) (seq_of T0) Hs0). }
assert (LSR : forall j, 0 <= last_of T1 j < 2 ^ 64).
{ intros j. unfold last_of, u_at. pose proof (PropExec.bytes_le_to_Z_bound (sub T1 (48 * j + 40) 8)) as Hb1.
  pose proof (PropExec.bytes_le_to_Z_nonneg (sub T1 (48 * j + 40) 8)) as Hb0.
  assert (LS : (length (sub T1 (48 * j + 40) 8) <= 8)%nat) by (unfold sub; rewrite length_firstn; lia).
  split; [exact Hb0|]. eapply Z.lt_le_trans; [exact Hb1|]. apply Z.pow_le_mono_r; lia. }
assert (ESTALE : ew (d_env cx E vals) 557 = Z_to_bv 64 REAC_DISCO_STALE_NS) by exact E557.
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)).
unfold cfg_at, P_CHK_RA. change (w64 (BASE + 2500)) with (Z_to_bv 64 (BASE + 2500)).
assert (HPT : forall x, mem3 x = mem3 x) by reflexivity.
assert (HPTR : forall x, rd W mem3 x = rd W mem3 x) by reflexivity.
clear Hregs Hflag Hh216 Hh152 Hacs Hfcs Hfacts.
assert (PC : True) by exact I.
let rec go := idtac;
  paj_run_shc RUNP RUNC HS HJ;
  [ cbn [ss_mem add_cond]; repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil
  | lazymatch type of HF with frame_of _ _ _ ?m1 => lazymatch type of HFr with frame_of _ _ _ ?r1 =>
      let P := fresh "P" in let Pr := fresh "Pr" in
      pose proof (lf_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)) as P;
      pose proof (lf_ro_pt _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as Pr;
      clear HF HFr;
      let Q := fresh "Q" in let Qr := fresh "Qr" in
      assert (Q : forall x, m1 x = mem3 x) by (intro x; rewrite P; apply HPT);
      assert (Qr : forall x, r1 x = rd W mem3 x) by (intro x; rewrite Pr; apply HPTR);
      clear HPT HPTR P Pr; rename Q into HPT; rename Qr into HPTR
    end end;
    repeat match goal with H : mem_grows _ _ |- _ => clear H end;
    lazymatch goal with
    | HS' : st_ok _ ?Ev ?ssx (restrict _ ?msx) |- _ => leaf HS' Ev ssx msx
    | HS' : st_ok_pi _ _ _ _ _ |- _ => psrr_branch_pi RUNP BR HS'; [side | side]
    end ]
with side := idtac;
  lazymatch type of Hc with
  | branch_taken BC_EQ (sv_denot _ (SExt true 32 (SOff 564 0))) (sv_denot _ (SAluw _ _ _)) = ?bb =>
      lazymatch bb with false => rewrite CK1 in Hc; discriminate Hc | true => clear Hc; go end
  | branch_taken BC_EQ (sv_denot _ (SExt true 32 (SOff 565 0))) (sv_denot _ (SAluw _ _ _)) = ?bb =>
      lazymatch bb with false => rewrite CK3 in Hc; discriminate Hc | true => clear Hc; go end
  | branch_taken BC_NE (sv_denot ?Ev (SAlu ALU_SLTU ?s (SLit 1))) (sv_denot _ (SLit 0)) = ?bb =>
      lazymatch bb with
      | false =>
          let Hs := fresh "Hs" in
          assert (Hs : sv_denot Ev s = Z_to_bv 64 0) by zsum;
          rewrite (dn_sltu1 Ev s Hs), (dn_lit Ev 0) in Hc; vm_compute in Hc; discriminate Hc
      | true => clear Hc; go
      end
  | branch_taken ?cc (sv_denot ?Ev ?a) (sv_denot ?Ev ?b) = ?bb =>
      let Ha := fresh "Ha" in let Hb := fresh "Hb" in
      eassert (Ha : sv_denot Ev a = Z_to_bv 64 _) by (lf_dn TNX KX);
      eassert (Hb : sv_denot Ev b = Z_to_bv 64 _) by (lf_dn TNX KX);
      rewrite Ha, Hb in Hc; clear Ha Hb;
      lazymatch cc with
      | BC_EQ => rewrite bt_eq_s in Hc by (clear - HT1n KR; lia)
      | BC_NE => rewrite bt_ne_s in Hc by (clear - HT1n KR; lia)
      | BC_LT => rewrite bt_lt_s in Hc by (clear - HT1n KR; lia)
      | BC_GE => rewrite bt_ge_s in Hc by (clear - HT1n KR; lia)
      end;
      lf_bp Hc;
      let PC' := fresh "PC" in pose proof (conj Hc PC) as PC'; clear Hc PC; rename PC' into PC;
      tryif (exfalso; clear - HT1n KR PC; lia) then idtac else go
  end
with zsum := idtac;
  lazymatch goal with
  | |- sv_denot _ (SLit 0) = _ => reflexivity
  | |- sv_denot ?Ev (SAlu ALU_ADD ?x (SAlu ALU_AND (SAlu ALU_SLTU (SOff ?nl 0) (SOff 563 0)) _)) = _ =>
      apply dn_add00; [zsum|];
      let j := eval vm_compute in (nl - 566)%nat in
      apply (dn_stale0 Ev nl 563 557 (last_of T1 (Z.of_nat j)) now (ELS j ltac:(clear - HT1n; lia)) E563 ESTALE (LSR _) Hnow);
      exact (Hstale (Z.of_nat j) ltac:(clear - HT1n PC; lia))
  end
with leaf HS' Ev ssx msx := idtac;
  let RG := fresh "RG" in let R1 := fresh "R1" in let R10 := fresh "R10" in let R19 := fresh "R19" in
  assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 25]%bv -> getr (ms_regs msx) r = getr regs r)
    by (intros r Hr; rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ msx r HS'), (HSro r);
        cbv [In] in Hr; repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]); destruct Hr);
  assert (R1 : getr (ms_regs msx) 1 = w64 (BASE + P_MAL_RA))
    by (rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ msx 1 HS');
        let v := eval vm_compute in (sr_get (ss_regs ssx) 1%bv) in change (sr_get (ss_regs ssx) 1%bv) with v;
        apply codeptr_val; exact HEI);
  assert (R19 : getr (ms_regs msx) 19 = w64 (a3_cap op))
    by (rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ msx 19 HS');
        let v := eval vm_compute in (sr_get (ss_regs ssx) 19%bv) in change (sr_get (ss_regs ssx) 19%bv) with v;
        let Hv := fresh "Hv" in eassert (Hv : sv_denot Ev v = Z_to_bv 64 _) by (lf_dn TNX KX); rewrite Hv;
        unfold w64, a3_cap, slot_ser_defs.ser_cap; destruct (Z.eqb_spec (slot_ser_defs.ser_k op) 0) as [Ek|Ek]; f_equal; clear - PC Ek KR; lia);
  assert (R10 : getr (ms_regs msx) 10 = w64 (a3_cap op))
    by (rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ msx 10 HS');
        let v := eval vm_compute in (sr_get (ss_regs ssx) 10%bv) in change (sr_get (ss_regs ssx) 10%bv) with v;
        let Hv := fresh "Hv" in eassert (Hv : sv_denot Ev v = Z_to_bv 64 _) by (lf_dn TNX KX); rewrite Hv;
        unfold w64, a3_cap, slot_ser_defs.ser_cap; destruct (Z.eqb_spec (slot_ser_defs.ser_k op) 0) as [Ek|Ek]; f_equal; clear - PC Ek KR; lia);
  apply SRr_ret;
  exact (lf_leaf cx h i n now op W0 c0 T0 T1 removed W fq ly3 S3 regs mem3 k acc E vals ssx msx _
    HFROM Hfrm0 Hbase Hfrs Hk Hnev Hmo Hacc Hi Hn Hnow HrL Hsp0 Hsp1 Hag Hbody HdE HS' eq_refl eq_refl
    ltac:(vm_compute; reflexivity) HJ HPT HPTR RG R1 R10 R19)
in go.
Qed.

End h.
End f.
End d.
