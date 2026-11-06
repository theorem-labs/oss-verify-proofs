(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:2300-2306, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Segment I of LLVMFuzzerTestOneInput's ASan+UBSan walk (image B, fuzz_identity.asan-ubsan): seg_I of
   lib/B/Prog/LLVMFuzzerTestOneInput_inv.v, from inv_H_end (+0x128c, 0x81a00) to inv_I_end (+0x1388, 0x81afc).

   The code: the re-poisoning of `f` / `ef`'s shadow (0x81a08..0x81a10); the family (0x81a14 bltz: the input's
   own family byte when t_fam_raw >= 128, else reac_box_family_of on `id` at 0x81a1c); reac_box_family_stem
   (0x81a30) and its NULL abort (0x81a34, refuted from the table's non-null words); the said_name mask
   (0x81a3c..0x81a54); the three buffers through buf_of (0x81a5c, 0x81a68, 0x81a74); reac_box_name twice with the
   two stack arguments at sp+0 / sp+8: the refusing call (name = NULL, 0x81aac, its -1 checked at 0x81ab8) and the
   real one (0x81aec), each between a 16-byte push and pop.

   The walk is cut at four slots of this file's own (si_C1 at +0x12b8, si_C2 at +0x12e8, si_C3 at +0x1304,
   si_C4 at +0x1348); one lemma per step (si_L_fam, si_L_stem, si_L_bufs, si_L_ref, si_L_real), chained by
   si_compose into seg_I. Each call goes through si_call (YC85.v cl_callS with the entry's frame chain built
   here); the memory facts cross every run and call as si_vals, kept on si_area. The plain model of reac_box_name
   and reac_box_family_of is related to SlotModel in Module SIM (proof ideas from the released plain walk
   lib/Prog/Seg/G07.v, which is address-bound and not imported). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require
buf_of reac_box_family_of reac_box_family_stem reac_box_name reac_box_name_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require
IdentSpec RcIdentModel SlotModel disco_box_name_model reac_box_name_c reac_box_family_of_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off for every file that loads it; the address arithmetic of
   this segment (shadow_addr, the frame's alignment) needs it, so this file turns it back on. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
(* ---- the plain model of reac_box_name and reac_box_family_of against SlotModel ------------------------- *)
Module SIM.
Import IdentSpec RcIdentModel SlotModel disco_box_name_model.
Import ListNotations.
Open Scope Z_scope.


(* Segment I model lemmas: the plain model of reac_box_name (disco_box_name_model, reac_box_name_c) and
   of reac_box_family_of (famof_res) against the harness model SlotModel. Proof ideas copied from the
   released plain lib/Prog/Seg/G07.v (address-bound, not imported). *)

Definition si_sdZ (inp : list byte) : list Z := if n_said inp then map bz (name_str (idT inp)) else [].

(* ---------- byte / list helpers ---------- *)

Lemma si_bz0 : bz (zb 0) = 0.
Proof. unfold bz, zb. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma si_leq_eq : forall a b, bn_leq a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn [bn_leq] in H; try discriminate; [reflexivity|].
  apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. subst y. f_equal. apply IH. exact H2.
Qed.

Lemma si_leq_map : forall a b, bn_leq (map bz a) (map bz b) = bytes_eqb a b.
Proof.
  induction a as [|x a IH]; intros [|y b]; cbn [map bn_leq bytes_eqb]; try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma si_skipn_map : forall (f : byte -> Z) n l, skipn n (map f l) = map f (skipn n l).
Proof. intros f n. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. apply IH. Qed.

Lemma si_nth_skipn : forall {A : Type} (l : list A) k n d, nth n (skipn k l) d = nth (k + n) l d.
Proof.
  intros A l k. revert l. induction k as [|k IH]; intros l n d; [reflexivity|].
  destruct l as [|x l]; cbn [skipn].
  - destruct n; reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma si_nth_firstn : forall {A : Type} (l : list A) k n d, (n < k)%nat -> nth n (firstn k l) d = nth n l d.
Proof.
  intros A l. induction l as [|x l IH]; intros [|k] [|n] d H; cbn [firstn nth]; try reflexivity; try lia.
  apply IH. lia.
Qed.

Lemma si_nth_map_bz : forall (l : list byte) n, nth n (map bz l) 0 = bz (nth n l (zb 0)).
Proof.
  induction l as [|x l IH]; intros [|n]; cbn [map nth]; try (symmetry; apply si_bz0); try reflexivity.
  apply IH.
Qed.

(* ---------- reac_box_name model vs the harness model (G07 template) ---------- *)

Lemma si_dec : forall x, 0 <= x <= 40 -> bn_dec x 1 = map bz (DEC x 1) /\ bn_dec x 2 = map bz (DEC x 2).
Proof.
  intros x Hx.
  pose proof (z_all_spec (fun x => bn_leq (bn_dec x 1) (map bz (DEC x 1)) && bn_leq (bn_dec x 2) (map bz (DEC x 2)))
    (Z.to_nat 41) 0 ltac:(vm_compute; reflexivity) x ltac:(rewrite Z2Nat.id by lia; lia)) as H.
  cbv beta in H. apply andb_true_iff in H as [H1 H2]. split; apply si_leq_eq; assumption.
Qed.

Lemma si_STEM : forall f, bn_STEM f = map bz (stem_img f).
Proof.
  intros f. unfold bn_STEM, stem_img.
  destruct (f =? 1); [vm_compute; reflexivity|]. destruct (f =? 2); [vm_compute; reflexivity|].
  destruct (f =? 3); vm_compute; reflexivity.
Qed.

Lemma si_stem : forall inp, bn_stem (n_fam inp) (si_sdZ inp) = map bz (n_stem inp).
Proof.
  intros inp. unfold si_sdZ, n_stem, n_use_said. destruct (n_said inp); cbn [andb].
  - unfold name_str. destruct (model_name (idT inp)) as [|b r].
    + cbn [first_zero firstn map bn_stem]. assert (E : negb (bz (nthb [] 0) =? 0) = false) by reflexivity.
      rewrite E. apply si_STEM.
    + cbn [first_zero]. unfold nthb. cbn [nth]. destruct (bz b =? 0).
      * cbn [firstn map bn_stem negb]. apply si_STEM.
      * cbn [firstn map bn_stem negb]. reflexivity.
  - cbn [bn_stem]. apply si_STEM.
Qed.

Lemma si_NM : forall inp, n_wok inp = true ->
  bn_NM (n_fam inp) (si_sdZ inp) (t_in inp) (t_out inp) = map bz (n_EXP_NM inp).
Proof.
  intros inp W. destruct (wok_chans inp W) as [Hi Ho].
  unfold bn_NM. rewrite si_stem. unfold bn_w4.
  destruct (si_dec _ Hi) as [_ Di]. destruct (si_dec _ Ho) as [_ Do]. rewrite Di, Do, <- map_app.
  change (DEC (t_in inp) 2 ++ DEC (t_out inp) 2) with (n_W4 inp). cbv zeta.
  rewrite length_map, si_skipn_map, si_leq_map.
  unfold n_EXP_NM, n_ends_w4.
  rewrite (firstn_all2 (n := 4%nat) (n_W4 inp))
    by (unfold n_W4; rewrite length_app, (DEC2_len _ Hi), (DEC2_len _ Ho); lia).
  assert (E4 : (4 <=? Z.of_nat (length (n_stem inp))) = (4 <=? length (n_stem inp))%nat).
  { destruct (Z.leb_spec 4 (Z.of_nat (length (n_stem inp)))); destruct (Nat.leb_spec 4 (length (n_stem inp)));
      reflexivity || lia. }
  rewrite E4.
  destruct (_ && _); [reflexivity|]. rewrite !map_app. reflexivity.
Qed.

Lemma si_lower : forall b, bz (lower b) = if (65 <=? bz b) && (bz b <=? 90) then bz b + 32 else bz b.
Proof.
  intro b. unfold lower. destruct ((65 <=? bz b) && (bz b <=? 90)) eqn:E; [|reflexivity].
  apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1, E2.
  unfold zb, bz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. unfold bz in *. lia.
Qed.

Lemma si_tk : forall l d, bn_tk d (map bz l) = map bz (tok_go d l).
Proof.
  induction l as [|b r IH]; intros d; [reflexivity|]. cbn [map bn_tk tok_go].
  rewrite andb_comm. destruct (negb d && (bz b =? 45)); [apply IH|].
  cbn [map]. rewrite si_lower, IH. reflexivity.
Qed.

Lemma si_TK : forall inp, n_wok inp = true ->
  bn_TK (bn_NM (n_fam inp) (si_sdZ inp) (t_in inp) (t_out inp)) = map bz (n_TK inp).
Proof. intros inp W. rewrite (si_NM inp W). unfold bn_TK. rewrite si_tk. reflexivity. Qed.

Lemma si_DP0 : forall inp, n_wok inp = true ->
  bn_DP (map bz (n_EXP_NM inp)) (t_in inp) (t_out inp) = map bz (n_EXP_DP inp).
Proof.
  intros inp W. destruct (wok_chans inp W) as [Hi Ho].
  destruct (si_dec _ Hi) as [Di _]. destruct (si_dec _ Ho) as [Do _].
  unfold bn_DP, n_EXP_DP. rewrite Di, Do. rewrite !map_app. reflexivity.
Qed.

Lemma si_DP : forall inp, n_wok inp = true ->
  bn_DP (bn_NM (n_fam inp) (si_sdZ inp) (t_in inp) (t_out inp)) (t_in inp) (t_out inp) = map bz (n_EXP_DP inp).
Proof. intros inp W. rewrite (si_NM inp W). apply si_DP0. exact W. Qed.

Lemma si_has_dash_len : forall l, has_dash l = true -> (1 <= length l)%nat.
Proof. intros [|b r] H; [discriminate H | cbn; lia]. Qed.

Lemma si_tok_len : forall l d,
  length (tok_go d l) = (length l - (if negb d && has_dash l then 1 else 0))%nat.
Proof.
  induction l as [|b r IH]; intros d; [reflexivity|].
  assert (HD : has_dash (b :: r) = (bz b =? 45) || has_dash r) by reflexivity. rewrite HD. destruct d.
  - cbn [tok_go negb andb Datatypes.length]. rewrite IH. cbn [negb andb]. lia.
  - destruct (bz b =? 45) eqn:E; cbn [tok_go negb andb orb Datatypes.length]; rewrite E; cbn [andb orb].
    + rewrite IH. cbn [negb andb]. lia.
    + cbn [Datatypes.length]. rewrite IH. cbn [negb andb]. destruct (has_dash r) eqn:D; [|lia].
      pose proof (si_has_dash_len r D). lia.
Qed.

Lemma si_tk_len : forall inp, Z.of_nat (length (n_TK inp)) = n_lt inp.
Proof.
  intro inp. unfold n_TK, TOK, n_lt, n_ln. rewrite si_tok_len. cbn [negb andb].
  destruct (has_dash (n_EXP_NM inp)) eqn:D; [|lia]. pose proof (si_has_dash_len _ D). lia.
Qed.

Lemma si_r_cases : forall inp, n_r inp = 0 \/ n_r inp = -1.
Proof. intros inp. unfold n_r. destruct (n_wok inp && n_fits inp); [left | right]; reflexivity. Qed.

Lemma si_r0_fits : forall inp, n_r inp = 0 -> n_wok inp = true /\ n_fits inp = true.
Proof.
  intros inp H. unfold n_r in H. destruct (n_wok inp && n_fits inp) eqn:E; [|discriminate].
  apply andb_true_iff in E. exact E.
Qed.

Lemma si_r0 : forall inp, n_r inp = 0 -> n_wok inp = true.
Proof. intros inp H. exact (proj1 (si_r0_fits inp H)). Qed.

Lemma si_accept : forall inp nm tk dp, nm <> 0 -> tk <> 0 -> dp <> 0 ->
  reac_box_name_c.bn_accept (n_fam inp) (si_sdZ inp) (t_in inp) (t_out inp) nm (t_cap_name inp) tk (t_cap_tok inp)
    dp (t_cap_disp inp) = (n_r inp =? 0).
Proof.
  intros inp nm tk dp Hn Ht Hd.
  unfold reac_box_name_c.bn_accept, reac_box_name_c.bn_args_ok, n_r. change bn_ok with okw.
  rewrite (proj2 (Z.eqb_neq nm 0) Hn), (proj2 (Z.eqb_neq tk 0) Ht), (proj2 (Z.eqb_neq dp 0) Hd).
  cbn [negb andb].
  destruct (n_wok inp) eqn:W.
  - pose proof W as W'. unfold n_wok in W'. apply andb_true_iff in W' as [W1 W3]. apply andb_true_iff in W1 as [W1 W2].
    rewrite W1, W2, W3.
    assert (R0 : bn_ret (n_fam inp) (si_sdZ inp) (t_in inp) (t_out inp) = 0).
    { unfold bn_ret. change bn_ok with okw. rewrite W1, W2, W3, (si_NM inp W), length_map.
      pose proof (n_ln_le inp W) as HL.
      unfold n_ln in HL. destruct (Z.leb_spec (Z.of_nat (length (n_EXP_NM inp))) 23); [reflexivity | lia]. }
    rewrite R0. rewrite (si_NM inp W). unfold bn_TK. rewrite si_tk. rewrite (si_DP0 inp W). rewrite !length_map.
    change (tok_go false (n_EXP_NM inp)) with (n_TK inp).
    change (Z.of_nat (length (n_EXP_NM inp))) with (n_ln inp).
    change (Z.of_nat (length (n_EXP_DP inp))) with (n_ld inp). rewrite si_tk_len.
    pose proof (n_ln_le inp W) as HL.
    assert (HT : 0 <= n_lt inp) by (pose proof (si_tk_len inp); lia).
    assert (HD : 0 <= n_ld inp) by (unfold n_ld; lia).
    unfold n_fits. cbn [andb].
    destruct (Z.eqb_spec (t_cap_name inp) 0); destruct (Z.eqb_spec (t_cap_tok inp) 0);
      destruct (Z.eqb_spec (t_cap_disp inp) 0);
      destruct (Z.ltb_spec (n_ln inp) (t_cap_name inp)); destruct (Z.ltb_spec (n_lt inp) (t_cap_tok inp));
      destruct (Z.ltb_spec (n_ld inp) (t_cap_disp inp)); cbn; try reflexivity; lia.
  - revert W. unfold n_wok.
    destruct (okw (t_in inp)); destruct (okw (t_out inp)); destruct (negb ((t_in inp =? 0) && (t_out inp =? 0)));
      cbn [andb]; intros W; try discriminate W; rewrite ?andb_false_r; cbn [andb]; reflexivity.
Qed.

(* the refusing call: name = NULL *)
Lemma si_refuse : forall f sd i o nl tk tl dp dl, reac_box_name_c.bn_accept f sd i o 0 nl tk tl dp dl = false.
Proof. intros. reflexivity. Qed.

Lemma si_args_refuse : forall i o nl tk tl dp dl, reac_box_name_c.bn_args_ok 0 nl tk tl dp dl i o = false.
Proof. intros. reflexivity. Qed.

(* ---------- the identity struct's model name ---------- *)

Lemma si_mn_len : forall idb, length idb = ID_SIZE -> length (model_name idb) = 17%nat.
Proof.
  intros idb H. unfold model_name, get, OFF_NAME, NAME_CAP. rewrite length_firstn, length_skipn.
  unfold ID_SIZE in H. lia.
Qed.

Lemma si_fz_le16 : forall inp, (first_zero (model_name (idT inp)) <= 16)%nat.
Proof.
  intro inp. unfold idT. generalize (nrecn inp) as i. intro i.
  pose proof (rec_id_length inp i) as Hl.
  assert (Lm : length (model_name (rec_id inp i)) = 17%nat) by (apply si_mn_len; exact Hl).
  assert (Hm : nth 16 (model_name (rec_id inp i)) (zb 0) = nth 19 (rec_id inp i) (zb 0)).
  { unfold model_name, get, OFF_NAME, NAME_CAP. rewrite nth_first by lia.
    rewrite (nth_skip0 (skipn 3 (rec_id inp i))), skipn_skipn, <- nth_skip0. reflexivity. }
  pose proof (first_zero_le (model_name (rec_id inp i)) 16 ltac:(lia)) as F.
  rewrite Hm in F. exact (F (rec_id_b19 inp i)).
Qed.

Lemma si_firstn_fz : forall l, (first_zero l < length l)%nat -> firstn (first_zero l + 1) l = firstn (first_zero l) l ++ [zb 0].
Proof.
  induction l as [|b r IH]; intros H; cbn [length first_zero] in *; [lia|].
  revert H. destruct (Z.eqb_spec (bz b) 0) as [E|E]; intro H; cbn [firstn app Nat.add] in *.
  - f_equal. unfold zb. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bz in E. rewrite E. reflexivity.
  - f_equal. apply IH. lia.
Qed.

Lemma si_fz_nz : forall l, Forall (fun b => bz b <> 0) (firstn (first_zero l) l).
Proof.
  induction l as [|b r IH]; cbn [first_zero firstn]; [constructor|].
  destruct (Z.eqb_spec (bz b) 0) as [E|E]; cbn [firstn]; constructor; assumption.
Qed.

Lemma si_name_len : forall inp, (length (name_str (idT inp)) <= 16)%nat.
Proof. intro inp. exact (name_str_len inp (nrecn inp)). Qed.

Lemma si_name_nz : forall inp, Forall (fun c => 0 < c < 256) (map bz (name_str (idT inp))).
Proof.
  intro inp. unfold name_str. apply Forall_map.
  pose proof (si_fz_nz (model_name (idT inp))) as H. revert H. apply Forall_impl.
  intros b Hb. cbv beta in *. pose proof (bz_range b). lia.
Qed.

Lemma si_name_bytes : forall inp,
  firstn (length (name_str (idT inp)) + 1) (skipn 3 (idT inp)) = name_str (idT inp) ++ [zb 0].
Proof.
  intro inp. pose proof (si_fz_le16 inp) as F.
  pose proof (si_mn_len (idT inp) (rec_id_length inp (nrecn inp))) as Lm.
  unfold name_str. rewrite length_firstn, Lm.
  replace (Nat.min (first_zero (model_name (idT inp))) 17) with (first_zero (model_name (idT inp))) by lia.
  rewrite <- (si_firstn_fz (model_name (idT inp))) by lia.
  set (k := first_zero (model_name (idT inp))) in *. clearbody k.
  unfold model_name, get, OFF_NAME, NAME_CAP. rewrite firstn_firstn. f_equal. lia.
Qed.

(* ---------- the said-name decision of the harness ---------- *)

Lemma si_said_nil : forall inp, has_model_name (idT inp) = 0 -> si_sdZ inp = [].
Proof. intros inp H. unfold si_sdZ, n_said. rewrite H. reflexivity. Qed.

Lemma si_said_cons : forall inp, has_model_name (idT inp) <> 0 -> si_sdZ inp = map bz (name_str (idT inp)).
Proof.
  intros inp H. unfold si_sdZ, n_said.
  destruct (Z.eqb_spec (has_model_name (idT inp)) 0); [contradiction | reflexivity].
Qed.

Lemma si_hmn_byte : forall inp, has_model_name (idT inp) = bz (nth 20 (idT inp) (zb 0)).
Proof. intro inp. reflexivity. Qed.

(* ---------- reac_box_family_of's result ---------- *)

Definition si_HW_ROWS : list Z :=
  [1; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0;
   2; 0; 0; 0; 0; 0; 0; 2; 0; 3; 0; 2;
   3; 0; 0; 0; 0; 0; 0; 2; 0; 1; 0; 2].

Lemma si_FAM_eq : forall idb, FAM idb =
  if bz (nth 36 idb (zb 0)) =? 0 then 0
  else if list_eq_dec Z.eq_dec (map bz (firstn 8 (skipn 28 idb))) reac_box_family_of_c.FAMOF_HW1 then 1
  else if list_eq_dec Z.eq_dec (map bz (firstn 8 (skipn 28 idb))) reac_box_family_of_c.FAMOF_HW2 then 2
  else if list_eq_dec Z.eq_dec (map bz (firstn 8 (skipn 28 idb))) reac_box_family_of_c.FAMOF_HW3 then 3
  else 0.
Proof. intro idb. reflexivity. Qed.

Lemma si_FAM_range : forall idb, 0 <= FAM idb <= 3.
Proof.
  intro idb. rewrite si_FAM_eq.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia.
Qed.

Lemma si_row_iff : forall (rd : Z -> option Z) p t idb (i : Z) (k : nat),
  length idb = 38%nat ->
  (forall j, (j < 38)%nat -> rd (p + Z.of_nat j) = Some (bz (nth j idb (zb 0)))) ->
  (forall j, (j < 36)%nat -> rd (t + Z.of_nat j) = Some (nth j si_HW_ROWS 0)) ->
  Z.of_nat k = 12 * i + 4 -> (k + 8 <= 36)%nat ->
  (reac_box_family_of.famof_row rd p t i <-> map bz (firstn 8 (skipn 28 idb)) = firstn 8 (skipn k si_HW_ROWS)).
Proof.
  intros rd p t idb i k Hl Hp Ht Hk Hk8.
  assert (LA : forall n, (n < 8)%nat -> nth n (map bz (firstn 8 (skipn 28 idb))) 0 = bz (nth (28 + n) idb (zb 0))).
  { intros n Hn. rewrite si_nth_map_bz, si_nth_firstn by exact Hn. rewrite si_nth_skipn. reflexivity. }
  assert (LB : forall n, (n < 8)%nat -> nth n (firstn 8 (skipn k si_HW_ROWS)) 0 = nth (k + n) si_HW_ROWS 0).
  { intros n Hn. rewrite si_nth_firstn by exact Hn. apply si_nth_skipn. }
  assert (EP : forall n, (n < 8)%nat -> rd (p + 28 + Z.of_nat n) = Some (bz (nth (28 + n) idb (zb 0)))).
  { intros n Hn. rewrite <- (Hp (28 + n)%nat) by lia. f_equal. lia. }
  assert (ET : forall n, (n < 8)%nat -> rd (t + 12 * i + 4 + Z.of_nat n) = Some (nth (k + n) si_HW_ROWS 0)).
  { intros n Hn. rewrite <- (Ht (k + n)%nat) by lia. f_equal. lia. }
  unfold reac_box_family_of.famof_row. split.
  - intros Hrow. apply nth_ext with (d := 0) (d' := 0).
    + rewrite length_map, !length_firstn, !length_skipn, Hl. change (length si_HW_ROWS) with 36%nat. lia.
    + intros n Hn. rewrite length_map, length_firstn, length_skipn, Hl in Hn.
      specialize (Hrow (Z.of_nat n) ltac:(lia)). rewrite EP, ET in Hrow by lia. injection Hrow as Hrow.
      rewrite LA, LB by lia. exact Hrow.
  - intros Heq j Hj.
    assert (Ej : j = Z.of_nat (Z.to_nat j)) by lia. rewrite Ej.
    rewrite EP, ET by lia. f_equal. rewrite <- LA, <- LB by lia. rewrite Heq. reflexivity.
Qed.

Lemma si_famof : forall (rd : Z -> option Z) p t idb r,
  length idb = 38%nat -> p <> 0 ->
  (forall j, (j < 38)%nat -> rd (p + Z.of_nat j) = Some (bz (nth j idb (zb 0)))) ->
  (forall j, (j < 36)%nat -> rd (t + Z.of_nat j) = Some (nth j si_HW_ROWS 0)) ->
  reac_box_family_of.famof_res rd p t 1 2 3 r -> r = FAM idb.
Proof.
  intros rd p t idb r Hl Hp0 Hp Ht Hres.
  assert (H36 : rd (p + 36) = Some (bz (nth 36 idb (zb 0)))) by exact (Hp 36%nat ltac:(lia)).
  pose proof (si_row_iff rd p t idb 0 4 Hl Hp Ht ltac:(reflexivity) ltac:(lia)) as R0.
  pose proof (si_row_iff rd p t idb 1 16 Hl Hp Ht ltac:(reflexivity) ltac:(lia)) as R1.
  pose proof (si_row_iff rd p t idb 2 28 Hl Hp Ht ltac:(reflexivity) ltac:(lia)) as R2.
  change (firstn 8 (skipn 4 si_HW_ROWS)) with reac_box_family_of_c.FAMOF_HW1 in R0.
  change (firstn 8 (skipn 16 si_HW_ROWS)) with reac_box_family_of_c.FAMOF_HW2 in R1.
  change (firstn 8 (skipn 28 si_HW_ROWS)) with reac_box_family_of_c.FAMOF_HW3 in R2.
  rewrite si_FAM_eq. unfold reac_box_family_of.famof_res in Hres.
  destruct (Z.eqb_spec (bz (nth 36 idb (zb 0))) 0) as [Z36|Z36].
  - rewrite Z36 in H36.
    destruct Hres as [(HA0 & _) | [(_ & _ & HB) | [(_ & HC & _) | [(_ & HD & _) | [(_ & HE & _) | (_ & HF & _)]]]]];
      [contradiction | exact HB | contradiction | contradiction | contradiction | contradiction].
  - assert (N36 : rd (p + 36) <> Some 0) by (rewrite H36; intro E; injection E as E; contradiction).
    set (hw := map bz (firstn 8 (skipn 28 idb))) in *.
    destruct Hres as [(HA0 & _) | [(_ & HB & _) | [(_ & _ & W0 & Er) | [(_ & _ & W0 & W1 & Er) |
      [(_ & _ & W0 & W1 & W2 & Er) | (_ & _ & W0 & W1 & W2 & Er)]]]]].
    + contradiction.
    + contradiction.
    + assert (E0 : hw = reac_box_family_of_c.FAMOF_HW1) by (apply R0; exact W0).
      destruct (list_eq_dec Z.eq_dec hw reac_box_family_of_c.FAMOF_HW1) as [_|C]; [exact Er | contradiction].
    + assert (N0 : hw <> reac_box_family_of_c.FAMOF_HW1) by (intro E; apply W0; apply R0; exact E).
      assert (E1 : hw = reac_box_family_of_c.FAMOF_HW2) by (apply R1; exact W1).
      destruct (list_eq_dec Z.eq_dec hw reac_box_family_of_c.FAMOF_HW1) as [C|_]; [contradiction|].
      destruct (list_eq_dec Z.eq_dec hw reac_box_family_of_c.FAMOF_HW2) as [_|C]; [exact Er | contradiction].
    + assert (N0 : hw <> reac_box_family_of_c.FAMOF_HW1) by (intro E; apply W0; apply R0; exact E).
      assert (N1 : hw <> reac_box_family_of_c.FAMOF_HW2) by (intro E; apply W1; apply R1; exact E).
      assert (E2 : hw = reac_box_family_of_c.FAMOF_HW3) by (apply R2; exact W2).
      destruct (list_eq_dec Z.eq_dec hw reac_box_family_of_c.FAMOF_HW1) as [C|_]; [contradiction|].
      destruct (list_eq_dec Z.eq_dec hw reac_box_family_of_c.FAMOF_HW2) as [C|_]; [contradiction|].
      destruct (list_eq_dec Z.eq_dec hw reac_box_family_of_c.FAMOF_HW3) as [_|C]; [exact Er | contradiction].
    + assert (N0 : hw <> reac_box_family_of_c.FAMOF_HW1) by (intro E; apply W0; apply R0; exact E).
      assert (N1 : hw <> reac_box_family_of_c.FAMOF_HW2) by (intro E; apply W1; apply R1; exact E).
      assert (N2 : hw <> reac_box_family_of_c.FAMOF_HW3) by (intro E; apply W2; apply R2; exact E).
      destruct (list_eq_dec Z.eq_dec hw reac_box_family_of_c.FAMOF_HW1) as [C|_]; [contradiction|].
      destruct (list_eq_dec Z.eq_dec hw reac_box_family_of_c.FAMOF_HW2) as [C|_]; [contradiction|].
      destruct (list_eq_dec Z.eq_dec hw reac_box_family_of_c.FAMOF_HW3) as [C|_]; [contradiction | exact Er].
Qed.

(* ---------- n_fam ---------- *)

Lemma si_nfam_lo : forall inp, t_fam_raw inp < 128 -> n_fam inp = FAM (idT inp).
Proof.
  intros inp H. unfold n_fam. destruct (Z.leb_spec 128 (t_fam_raw inp)); [lia | reflexivity].
Qed.

Lemma si_nfam_hi : forall inp, 128 <= t_fam_raw inp -> n_fam inp = Z.land (t_fam_raw inp) 127.
Proof.
  intros inp H. unfold n_fam. destruct (Z.leb_spec 128 (t_fam_raw inp)); [reflexivity | lia].
Qed.

Lemma si_nfam_range : forall inp, 0 <= n_fam inp <= 127.
Proof.
  intro inp. unfold n_fam. destruct (Z.leb_spec 128 (t_fam_raw inp)) as [H|H].
  - pose proof (Z.land_ones (t_fam_raw inp) 7 ltac:(lia)) as E.
    change (Z.ones 7) with 127 in E. change (2 ^ 7) with 128 in E. rewrite E.
    pose proof (Z.mod_pos_bound (t_fam_raw inp) 128 ltac:(lia)). lia.
  - pose proof (si_FAM_range (idT inp)). lia.
Qed.

End SIM.



Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v, in the same order, and the registered globals G. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variable G : list (Z * Z).
#[local] Notation ACUT := (acut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).
#[local] Notation EPRE := (e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).
#[local] Notation AJ g pos := (ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
  [(4, pos)]).
#[local] Notation INV_H := (inv_H_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).
#[local] Notation INV_I := (inv_I_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).
#[local] Notation SEG_I := (seg_I_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis HLIVE : LIVE_LLVMF <= LIVE_LIB.
Hypothesis HBUF : buf_of.tbuf_of_spec B MT (CTX_BUF_OF RA_LLVMF).
Hypothesis HSTEM : reac_box_family_stem.treac_box_family_stem_spec B.
Hypothesis HFAM : reac_box_family_of.treac_box_family_of_spec B.
Let si_RUNP := SRr_run_pi_AJ B LAWS.
Let si_RUNC := SRr_run_pi_AJ_call B LAWS.
Let si_RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let si_BR := paj_branch (PI := PI).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Hypothesis PSIG : identb_prog_sig_ok (PI := PI).
Hypothesis HMT0 : forall s s' : astate, mo_le MT s s' 0.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Hypothesis HIMG : forall (W : world SEGS) mem,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> llvmf_img B G W mem.
Hypothesis HBN : reac_box_name.treac_box_name_spec B G.
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).

(* The three entries of switch.table.reac_box_family_stem (object 18) are non-null words below 2 ^ 64: llvmf_img's
   table clause, at any state whose read-only image is intact. It decides the abort at 0x81a34. *)
Lemma si_stem_nz : forall (W : world SEGS) mem,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  exists t1 t2 t3,
    val_mem SEGS (rd W mem) (VAL (A_OBJ 18)) 8 t1 /\
    val_mem SEGS (rd W mem) (VAL (A_OBJ 18) + 8) 8 t2 /\
    val_mem SEGS (rd W mem) (VAL (A_OBJ 18) + 16) 8 t3 /\
    0 < t1 < 2 ^ 64 /\ 0 < t2 < 2 ^ 64 /\ 0 < t3 < 2 ^ 64.
Proof.
intros W mem H.
destruct (HIMG W mem H) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (t1 & t2 & t3 & V1 & V2 & V3 & R1 & R2 & R3) & _).
exists t1, t2, t3. exact (conj V1 (conj V2 (conj V3 (conj R1 (conj R2 R3))))).
Qed.

(* ---- the bytes a step of segment I keeps -------------------------------------------------------------------- *)
(* Every value fact the segment carries lives in one of these zones: the machine frame and the saved words above
   it, except the slots segment I writes (mf+128, mf+144, mf+152, mf+184); the class-4 frame; the frame's shadow,
   except the six bytes of `f` / `ef` the segment poisons again (0x81a08..0x81a10, shadow bytes 58..63); and the
   input block. *)
Definition si_area (g : ectx) (pos mf a : Z) : Prop :=
  (mf <= a < mf + 128 \/ mf + 136 <= a < mf + 144 \/ mf + 160 <= a < mf + 184 \/ mf + 192 <= a < e_sp0 g) \/
  (SFa g pos <= a < SFa g pos + 1024) \/
  (shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 58 \/
   shadow_addr (SFa g pos) + 64 <= a < shadow_addr (SFa g pos) + 128) \/
  (e_p g <= a < e_p g + e_n g).

(* The memory part of ecommon, the identity struct, and the four tail slots the segment reads. *)
Definition si_vals (g : ectx) (pos mf : Z) (W2 : world SEGS) (mem2 : word -> option byte) : Prop :=
  val_mem SEGS (rd W2 mem2) (mf + 16) 8 (SFa g pos) /\
  val_mem SEGS (rd W2 mem2) (mf + 64) 8 (SFa g pos) /\
  val_mem SEGS (rd W2 mem2) (mf + 192) 8 (SFa g pos) /\
  val_mem SEGS (rd W2 mem2) (mf + 168) 8 SHADOW_OFF /\
  val_mem SEGS (rd W2 mem2) (e_sp0 g - 8) 8 RA_LLVMF /\
  val_mem SEGS (rd W2 mem2) (e_sp0 g - 16) 8 (s0Z (e_regs g)) /\
  val_mem SEGS (rd W2 mem2) (e_sp0 g - 24) 8 (bv_unsigned (getr (e_regs g) 9)) /\
  val_mem SEGS (rd W2 mem2) (e_sp0 g - 32) 8 (bv_unsigned (getr (e_regs g) 18)) /\
  val_mem SEGS (rd W2 mem2) (e_sp0 g - 40) 8 (bv_unsigned (getr (e_regs g) 19)) /\
  val_mem SEGS (rd W2 mem2) (e_sp0 g - 48) 8 (bv_unsigned (getr (e_regs g) 20)) /\
  val_mem SEGS (rd W2 mem2) (e_sp0 g - 56) 8 (bv_unsigned (getr (e_regs g) 21)) /\
  val_mem SEGS (rd W2 mem2) (e_sp0 g - 64) 8 (bv_unsigned (getr (e_regs g) 22)) /\
  val_mem SEGS (rd W2 mem2) (e_sp0 g - 72) 8 (bv_unsigned (getr (e_regs g) 23)) /\
  val_mem SEGS (rd W2 mem2) (e_sp0 g - 80) 8 (bv_unsigned (getr (e_regs g) 24)) /\
  val_mem SEGS (rd W2 mem2) (e_sp0 g - 88) 8 (bv_unsigned (getr (e_regs g) 25)) /\
  val_mem SEGS (rd W2 mem2) (e_sp0 g - 96) 8 (bv_unsigned (getr (e_regs g) 26)) /\
  val_mem SEGS (rd W2 mem2) (e_sp0 g - 104) 8 (bv_unsigned (getr (e_regs g) 27)) /\
  val_mem SEGS (rd W2 mem2) (SFa g pos + 1016) 8 (flag_addr (e_ly g) 4 pos) /\
  bytes_at8 W2 mem2 (e_p g) (e_pl g) /\
  id_at g pos (m_nrec g) W2 mem2 /\
  val_mem SEGS (rd W2 mem2) (mf + 112) 8 (SlotModel.t_row (e_pl g)) /\
  val_mem SEGS (rd W2 mem2) (mf + 120) 8 (SlotModel.t_cap_disp (e_pl g)) /\
  val_mem SEGS (rd W2 mem2) (mf + 136) 8 (SFa g pos + V_id + 3) /\
  val_mem SEGS (rd W2 mem2) (mf + 160) 8 (SlotModel.t_out (e_pl g)) /\
  val_mem SEGS (rd W2 mem2) (mf + 176) 8 (SlotModel.t_in (e_pl g)).

Lemma si_vals_moved : forall g pos mf W mem W' mem',
  mf + 320 <= e_sp0 g -> SFa g pos mod 8 = 0 -> e_n g = Z.of_nat (length (e_pl g)) ->
  (forall a, si_area g pos mf a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  si_vals g pos mf W mem -> si_vals g pos mf W' mem'.
Proof.
intros g pos mf W mem W' mem' Hsp HSF Hn HK H.
assert (VM : forall a (n : nat) v, (forall k, 0 <= k < Z.of_nat n -> si_area g pos mf (a + k)) ->
  val_mem SEGS (rd W mem) a n v -> val_mem SEGS (rd W' mem') a n v).
{ intros a n v Ha Hv. apply (val_mem_kept SEGS (w_H W) (w_H W') mem mem' a n v); [|exact Hv].
  intros k Hk. apply HK, Ha, Hk. }
assert (GA : forall a l, (forall k, 0 <= k < Z.of_nat (length l) -> si_area g pos mf (a + k)) ->
  garr8 SEGS (rd W mem) a l -> garr8 SEGS (rd W' mem') a l).
{ intros a l Ha Hg. apply (garr8_frame SEGS _ _ a l Hg). intros x Hx.
  apply (mbyte_of_aview SEGS). replace x with (a + (x - a)) by lia. apply HK, Ha. lia. }
assert (Hid : length (m_id g (m_nrec g)) = 38%nat) by apply SlotModel.rec_id_length.
assert (ESH : shadow_of_addr SHADOW_OFF (SFa g pos + V_id) = shadow_addr (SFa g pos) + 44).
{ unfold shadow_of_addr, shadow_addr, V_id. clear - HSF. Z.div_mod_to_equations. lia. }
destruct H as (V16 & V64 & V192 & V168 & Vra & Vs0 & S9 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27 &
  Vflag & Hinp & (Hidb & Hidz & Hidk) & V112 & V120 & V136 & V160 & V176).
unfold si_area in VM, GA.
split; [apply VM; [intros k Hk; cbn in Hk; clear - Hk Hsp; lia | exact V16]|].
split; [apply VM; [intros k Hk; cbn in Hk; clear - Hk Hsp; lia | exact V64]|].
split; [apply VM; [intros k Hk; cbn in Hk; clear - Hk Hsp; lia | exact V192]|].
split; [apply VM; [intros k Hk; cbn in Hk; clear - Hk Hsp; lia | exact V168]|].
do 13 (split; [apply VM; [intros k Hk; cbn in Hk; clear - Hk Hsp; lia | assumption]|]).
split; [apply VM; [intros k Hk; cbn in Hk; clear - Hk; lia | exact Vflag]|].
split.
{ unfold bytes_at8 in *. apply GA; [|exact Hinp]. rewrite length_map. intros k Hk. clear - Hk Hn. lia. }
split.
{ unfold id_at, bytes_at8, sh_zero in *. split.
  - apply GA; [|exact Hidb]. rewrite length_map, Hid. intros k Hk. unfold V_id. clear - Hk. lia.
  - split.
    + unfold zero_shadow in *. intros i Hi. rewrite HK; [exact (Hidz i Hi)|]. rewrite ESH.
      unfold si_area, N_id in *. clear - Hi. right; right; left; left. lia.
    + unfold sh_blk, block_shadow in *. destruct Hidk as (Hm & Hn0 & Hb). split; [exact Hm|]. split; [exact Hn0|].
      intros i Hi. rewrite HK; [exact (Hb i Hi)|]. rewrite ESH. unfold si_area, N_id in *. clear - Hi.
      right; right; left; left. lia. }
split; [apply VM; [intros k Hk; cbn in Hk; clear - Hk Hsp; lia | exact V112]|].
split; [apply VM; [intros k Hk; cbn in Hk; clear - Hk Hsp; lia | exact V120]|].
split; [apply VM; [intros k Hk; cbn in Hk; clear - Hk Hsp; lia | exact V136]|].
split; [apply VM; [intros k Hk; cbn in Hk; clear - Hk Hsp; lia | exact V160]|].
apply VM; [intros k Hk; cbn in Hk; clear - Hk Hsp; lia | exact V176].
Qed.

Lemma si_vals_of_ecommon : forall g pos mf ly2 S2 W2 regs2 mem2 md2,
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  id_at g pos (m_nrec g) W2 mem2 ->
  val_mem SEGS (rd W2 mem2) (mf + 112) 8 (SlotModel.t_row (e_pl g)) ->
  val_mem SEGS (rd W2 mem2) (mf + 120) 8 (SlotModel.t_cap_disp (e_pl g)) ->
  val_mem SEGS (rd W2 mem2) (mf + 136) 8 (SFa g pos + V_id + 3) ->
  val_mem SEGS (rd W2 mem2) (mf + 160) 8 (SlotModel.t_out (e_pl g)) ->
  val_mem SEGS (rd W2 mem2) (mf + 176) 8 (SlotModel.t_in (e_pl g)) ->
  si_vals g pos mf W2 mem2.
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 HC Hid V112 V120 V136 V160 V176.
destruct HC as (_ & _ & _ & _ & _ & _ & _ & V16 & V64 & V192 & V168 & Vra & Vs0 & S9 & S18 & S19 & S20 & S21 & S22 &
  S23 & S24 & S25 & S26 & S27 & Vflag & _ & _ & _ & Hinp).
unfold si_vals. repeat (split; [assumption|]). repeat split; assumption.
Qed.

Lemma si_ecommon : forall g pos mf ly2 S2 W2 regs2 mem2 md2,
  getr regs2 2 = w64 mf -> getr regs2 9 = w64 mf -> getr regs2 8 = w64 (e_sp0 g) ->
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
  getr regs2 3 = w64 (as_gp B) -> getr regs2 4 = w64 (as_tp B) ->
  si_vals g pos mf W2 mem2 -> EPRE g ->
  (forall fd, fd_lookup (m_fds md2) fd = fd_lookup (m_fds (e_md g)) fd) -> m_fs md2 = m_fs (e_md g) ->
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2.
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 R2 R9 R8 Hmf Hal R3 R4 HM HPRE Hfd Hfs.
destruct HM as (V16 & V64 & V192 & V168 & Vra & Vs0 & S9 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27 &
  Vflag & Hinp & _).
unfold ecommon. repeat (split; [assumption|]). exact Hinp.
Qed.

(* ---- where things are -------------------------------------------------------------------------------------- *)
Lemma si_geo : forall g pos mf ly2 S2 W2 mem2 md2 k,
  AJ g pos ly2 S2 W2 mem2 md2 k -> frames S2 = [(4, pos)] -> e_sp0 g - 336 <= mf <= e_sp0 g - 320 ->
  alloc_ceiling + 16 + ASTACK <= mf /\ e_sp0 g <= 2 ^ 47 /\ e_sp0 g mod 16 = 0 /\
  e_sp0 g - LLVMF_STK >= alloc_ceiling /\
  frame_addr ly2 4 pos = SFa g pos /\ 4096 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling /\
  SFa g pos mod 64 = 0 /\ in_app (SFa g pos) 1024.
Proof.
intros g pos mf ly2 S2 W2 mem2 md2 k HJ Hfrs Hmf.
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF64 & _ & _).
rewrite EFa in HSF0, HSF1, HSFapp, HSF64.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity. rewrite HFB in HSF1, HSFapp.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
assert (Has : ASTACK = 16384) by reflexivity.
change (spZ (e_regs g)) with (e_sp0 g) in *.
split; [clear - Hmf Hceil Hslo HSTK' Has; lia|].
split; [clear - H47 Hshi; lia|].
split; [exact Hsp0al|].
split; [clear - Hceil Hslo; lia|].
split; [exact EFa|]. split; [exact HSF0|]. split; [exact HSF1|]. split; [exact HSF64 | exact HSFapp].
Qed.

(* ---- what a call keeps ------------------------------------------------------------------------------------- *)
(* A call made below mf whose own write tokens lie in heap blocks other than the input keeps every zone. *)
Lemma si_area_kept_call : forall g pos mf ly2 S2 W2 mem2 md2 k ly3 S3 W3 mem3 md3 STK1 sp1 FP1 k1,
  AJ g pos ly2 S2 W2 mem2 md2 k -> frames S2 = [(4, pos)] ->
  ajournal SEGS B STK1 sp1 FP1 ly2 S2 W2 mem2 md2 [] ly3 S3 W3 mem3 md3 k1 ->
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> sp1 <= mf -> 0 <= STK1 ->
  (0 < e_n g -> In (e_p g, e_n g) (ablocks B ly2 S2) /\ In (e_p g, e_n g) (ablocks B ly3 S3)) ->
  (forall a, inFP FP1 a -> exists b n, In (b, n) (ablocks B ly2 S2) /\ (b, n) <> (e_p g, e_n g) /\
     b <= a < b + req_size n) ->
  forall a, si_area g pos mf a -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a.
Proof.
intros g pos mf ly2 S2 W2 mem2 md2 k ly3 S3 W3 mem3 md3 STK1 sp1 FP1 k1 HJ Hfrs HJ1 Hmf Hsp1 HSTK1 Hinp HFP a Ha.
destruct (si_geo g pos mf ly2 S2 W2 mem2 md2 k HJ Hfrs Hmf) as (Hmf0 & H47 & _ & _ & EFa & HSF0 & HSF1 & HSF64 & _).
pose proof HJ as (HAR2 & _).
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & _ & G4 & _).
pose proof (asan_consts) as (C1 & _).
assert (Has : ASTACK = 16384) by reflexivity.
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
(* a byte of the frame or its shadow is in no write token *)
assert (NFP : forall x, (in_zr x (frame_rng ly2 (4, pos)) \/
    in_zr x (shadow_addr (frame_addr ly2 4 pos), fs_frame_bytes 4 / 8)) -> ~ inFP FP1 x).
{ intros x Hx Hf. destruct (HFP x Hf) as (b & n & Hb & _ & Hbx).
  apply (block_not_frame_zone SEGS B LAWS ly2 S2 W2 mem2 md2 b n (x - b) 4 pos HAR2 Hb Hin4); [lia|].
  replace (b + (x - b)) with x by lia. exact Hx. }
unfold si_area in Ha. destruct Ha as [Hs | [Hf | [Hsh | Hi]]].
- apply G1; [clear - Hs Hmf Hmf0 H47 Has C1; lia | clear - Hs Hsp1; lia].
- apply (G4 4 pos a Hin4); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFa, HFB; clear - Hf; lia|].
  apply NFP. left. unfold in_zr, frame_rng; cbn [fst snd]. rewrite EFa, HFB. clear - Hf. lia.
- assert (Hz : in_zr a (shadow_addr (frame_addr ly2 4 pos), fs_frame_bytes 4 / 8)).
  { unfold in_zr. cbn [fst snd]. rewrite EFa, HFB. clear - Hsh. change (1024 / 8) with 128. lia. }
  apply (G4 4 pos a Hin4); [right; exact Hz|]. apply NFP. right. exact Hz.
- assert (Hn0 : 0 < e_n g) by (clear - Hi; lia).
  destruct (Hinp Hn0) as [Hb2 Hb3].
  pose proof (req_size_pos (e_n g) ltac:(lia)) as Hrq.
  replace a with (e_p g + (a - e_p g)) by lia.
  apply (G2 (e_p g) (e_n g) (a - e_p g) Hb2 Hb3); [clear - Hi Hrq; lia|].
  intros Hf. destruct (HFP _ Hf) as (b & n & Hb & Hne & Hbx).
  pose proof (sep_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 b n (e_p g) (e_n g) HAR2 Hb Hb2 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. clear - Hd Hbx Hi Hrq. lia.
Qed.

(* ---- the call chain at a call site: the entry's frame record at sp0 on top of the entry's empty chain ------- *)
Lemma si_chain : forall g pos ly2 S2 W2 mem2 md2 k sp',
  AJ g pos ly2 S2 W2 mem2 md2 k -> EPRE g ->
  val_mem SEGS (rd W2 mem2) (e_sp0 g - 8) 8 RA_LLVMF ->
  val_mem SEGS (rd W2 mem2) (e_sp0 g - 16) 8 (s0Z (e_regs g)) ->
  alloc_ceiling <= sp' -> sp' + 16 <= e_sp0 g ->
  exists ch, achain ly2 (aview SEGS (w_H W2) mem2) sp' (e_sp0 g) ch /\
    (ch = [] \/ ch = [(e_sp0 g, RA_LLVMF, s0Z (e_regs g))]).
Proof.
intros g pos ly2 S2 W2 mem2 md2 k sp' HJ HPRE Vra Vs0 Hsp1 Hsp2.
pose proof HPRE as (HFN & Hraz & _).
pose proof HFN as (_ & _ & Hra4 & _ & _ & _ & _ & Hch0 & _).
pose proof HJ as (_ & Hly2 & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & ETop & _).
change (spZ (e_regs g)) with (e_sp0 g) in *.
assert (Has : ASTACK = 16384) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
assert (Hac : alloc_ceiling + LLVMF_STK <= e_sp0 g) by (clear - Hceil Hslo; lia).
assert (HS0 : 0 <= LLVMF_STK) by (clear - HSTK' Has; lia).
assert (Hach : achain ly2 (aview SEGS (w_H (e_W g)) (e_mem g)) (e_sp0 g) (s0Z (e_regs g)) []).
{ apply (achain_ly_top (e_ly g)); [exact ETop | exact Hch0]. }
destruct (Z_lt_le_dec (e_sp0 g) (ly_top ly2 - 16)) as [Hlt | Hge].
- exists [(e_sp0 g, RA_LLVMF, s0Z (e_regs g))]. split; [|right; reflexivity].
  pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 1)) as Rra. change (bv_modulus 64) with (2 ^ 64) in Rra.
  pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 8)) as Rs0r. change (bv_modulus 64) with (2 ^ 64) in Rs0r.
  apply (achain_push ly2 _ _ (e_sp0 g) (s0Z (e_regs g)) RA_LLVMF [] sp' Hach).
  + rewrite ETop. clear - Htop1 H47. lia.
  + intros a Ha. apply F1; clear - Ha Hac HS0; lia.
  + apply rdword_of_val_mem; [exact Vra | unfold raZ in Hraz; clear - Hraz Rra; lia].
  + apply rdword_of_val_mem; [exact Vs0 | unfold s0Z; clear - Rs0r; lia].
  + rewrite <- Hraz. exact Hra4.
  + clear - Hac HS0. lia.
  + clear - Hsp0al. Z.div_mod_to_equations. lia.
  + exact Hlt.
  + exact Hsp2.
- exists []. split; [|left; reflexivity]. left. split; [right; left; exact Hge | reflexivity].
Qed.

(* ---- a program call from the entry's frame (lib/B/Prog/YC85.v cl_callS, with the chain built here) ---------- *)
Lemma si_call : forall g pos (W2 : world SEGS) (regsc : bvmap 5 word) memc pc ly2 S2 md2 k STK1 FP1 EV1 o raw
  (K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  AJ g pos ly2 S2 W2 memc md2 k -> EPRE g ->
  spZ regsc = e_sp0 g + o -> o mod 16 = 0 -> o <= -16 -> 0 <= STK1 -> STK1 - o <= LLVMF_STK ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  s0Z regsc = e_sp0 g ->
  val_mem SEGS (rd W2 memc) (e_sp0 g - 8) 8 RA_LLVMF ->
  val_mem SEGS (rd W2 memc) (e_sp0 g - 16) 8 (s0Z (e_regs g)) ->
  (forall ch1, (ch1 = [] \/ ch1 = [(e_sp0 g, RA_LLVMF, s0Z (e_regs g))]) ->
    afn_pre SEGS B STK1 ly2 S2 W2 regsc memc md2 ch1 ->
    SRr SEGS W2 (mkCfg (mkst regsc pc memc (seg_rom SEGS)) md2)
      (fun W3 c3 => exists ly3 S3 regs3 mem3 md3, c3 = mkCfg (mkst regs3 raw mem3 (seg_rom SEGS)) md3 /\
        ajournal SEGS B STK1 (spZ regsc) FP1 ly2 S2 W2 memc md2 [] ly3 S3 W3 mem3 md3 EV1 /\
        aregs_preserved regsc regs3 /\ K ly3 S3 W3 regs3 mem3 md3)) ->
  (forall a, inFP FP1 a -> in_tmp_block (ablocks B (e_ly g) (e_S g)) (ablocks B ly2 S2) a) ->
  SRr SEGS W2 (mkCfg (mkst regsc pc memc (seg_rom SEGS)) md2)
    (fun W3 c3 => exists ly3 S3 regs3 mem3 md3, c3 = mkCfg (mkst regs3 raw mem3 (seg_rom SEGS)) md3 /\
      AJ g pos ly3 S3 W3 mem3 md3 (k + EV1) /\
      ajournal SEGS B STK1 (e_sp0 g + o) FP1 ly2 S2 W2 memc md2 [] ly3 S3 W3 mem3 md3 EV1 /\
      aregs_preserved regsc regs3 /\ K ly3 S3 W3 regs3 mem3 md3).
Proof.
intros g pos W2 regsc memc pc ly2 S2 md2 k STK1 FP1 EV1 o raw K HJ HPRE Hsp Hal Hneg Hstk1 Hbud Hgp Htp Hra
  Hraw Hra4 Hs0 Vra Vs0 Hcallee HFP.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (_ & _ & Hceil & Hslo & _).
destruct (si_chain g pos ly2 S2 W2 memc md2 k (e_sp0 g + o) HJ HPRE Vra Vs0) as (ch & Hch & Hchs);
  [change (spZ (e_regs g)) with (e_sp0 g) in *; clear - Hceil Hslo Hbud Hstk1; lia | clear - Hneg; lia|].
eapply (cl_callS B LAWS W2 regsc memc pc LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
  [(4, pos)] ly2 S2 md2 k STK1 FP1 EV1 o raw ch K HJ Hsp Hal); try eassumption.
- clear - Hneg. lia.
- rewrite Hs0. exact Hch.
- intros HP. exact (Hcallee ch Hchs HP).
- intros a Ha. right. exact (HFP a Ha).
Qed.

(* ---- the meter, event by event ----------------------------------------------------------------------------- *)
Lemma si_MEV_nonneg : 0 <= MEV MT.
Proof.
unfold MEV. pose proof (mo_malloc_nonneg MT MTL 256 ltac:(lia)). pose proof (mo_free_nonneg MT MTL). lia.
Qed.
Lemma si_meter : forall S0 S2 S3 k m e, 0 <= e -> 0 <= m <= e * MEV MT -> k + e <= EV_LLVMF ->
  mo_le MT S0 S2 (k * MEV MT) -> mo_ok MT S2 ((EV_LLVMF - k) * MEV MT) -> mo_le MT S2 S3 m ->
  mo_le MT S0 S3 ((k + e) * MEV MT) /\ mo_ok MT S3 ((EV_LLVMF - (k + e)) * MEV MT).
Proof.
intros S0 S2 S3 k m e He Hm Hk MLE MOK M23. pose proof si_MEV_nonneg as H0.
split.
- eapply (mo_le_mono MT MTL); [exact (mo_le_trans MT MTL _ _ _ _ _ MLE M23)|]. clear - Hm H0. nia.
- apply (mo_ok_step MT MTL S2 S3 m); [|exact M23].
  apply (mo_ok_le MT MTL _ _ _ MOK). clear - Hm Hk H0. nia.
Qed.
Lemma si_meter_room : forall S2 k n, 0 <= n <= 256 -> k + 1 <= EV_LLVMF ->
  mo_ok MT S2 ((EV_LLVMF - k) * MEV MT) -> mo_ok MT S2 (mo_malloc MT n) /\ 0 <= mo_malloc MT n <= MEV MT.
Proof.
intros S2 k n Hn Hk MOK. pose proof si_MEV_nonneg as H0.
pose proof (mo_malloc_mono MT MTL n 256 Hn) as Hmono. pose proof (mo_malloc_nonneg MT MTL n ltac:(lia)) as Hnn.
pose proof (mo_free_nonneg MT MTL) as Hf.
assert (HM : mo_malloc MT n <= MEV MT) by (unfold MEV; lia).
split; [|lia].
apply (mo_ok_le MT MTL _ _ _ MOK). clear - HM Hk H0 Hnn. nia.
Qed.

(* ---- what the frame and its shadow hold ---------------------------------------------------------------- *)
(* Every byte of the entry's own class-4 frame and of that frame's 128 shadow bytes is present: the journal's
   own list holds (4, pos), so awr_byte's frame disjunct applies and awr_byte_present gives apresent. *)
Lemma si_frame_present : forall g pos ly2 S2 W2 mem2 md2 k a,
  AJ g pos ly2 S2 W2 mem2 md2 k ->
  (SFa g pos <= a < SFa g pos + 1024 \/
   shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128) ->
  aview SEGS (w_H W2) mem2 a <> None.
Proof.
intros g pos ly2 S2 W2 mem2 md2 k a HJ Ha.
pose proof HJ as (_ & Hly2 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
assert (HW : awr_byte LLVMF_STK (e_sp0 g) [] (ablocks B (e_ly g) (e_S g)) (ablocks B ly2 S2) ly2 [(4, pos)] a).
{ right; right; right. exists 4, pos. split; [left; reflexivity|].
  unfold in_zr. cbn [fst snd]. rewrite EFa, HFB. change (1024 / 8) with 128.
  destruct Ha as [H|H]; [left | right]; clear - H; lia. }
assert (HPW : apresent (w_H W2) mem2 a /\ ~ aowned B ly2 S2 a)
  by (eapply (awr_byte_present SEGS B LAWS); [exact HJ | exact HW]).
destruct HPW as ((Hh & b & Hb) & _).
unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
Qed.

(* The shadow of a block tells every byte of a sub-range it is addressable. *)
Lemma si_ra_sub : forall W2 mem2 a n q k,
  sh_blk W2 mem2 a n -> 0 <= n -> a <= q -> 0 <= k -> q + k <= a + n ->
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF q k.
Proof.
intros W2 mem2 a n q k Hb Hn Hq Hk Hqk x Hx.
unfold sh_blk, block_shadow in Hb. destruct Hb as (Hm & _ & Hbb).
set (i := (x - a) / 8).
assert (Hi : 0 <= i < (n + 7) / 8) by (unfold i; clear - Hx Hq Hqk Hk Hn; Z.div_mod_to_equations; lia).
exists (if i <? n / 8 then 0 else n mod 8). split.
- replace (shadow_of_addr SHADOW_OFF x) with (shadow_of_addr SHADOW_OFF a + i).
  + exact (Hbb i Hi).
  + unfold shadow_of_addr, i. clear - Hm Hx Hq Hqk. Z.div_mod_to_equations. lia.
- unfold saddr_ok. destruct (Z.ltb_spec i (n / 8)) as [Hlt | Hge]; [left; reflexivity|].
  right. assert (Hx8 : x mod 8 = (x - a) mod 8) by (clear - Hm; Z.div_mod_to_equations; lia).
  rewrite Hx8. unfold i in Hge. clear - Hx Hq Hqk Hk Hn Hge. Z.div_mod_to_equations. lia.
Qed.

(* A slice of a byte array. *)
Lemma si_garr8_slice : forall W2 mem2 a (l : list byte) (i k : nat),
  bytes_at8 W2 mem2 a l -> (i + k <= length l)%nat ->
  bytes_at8 W2 mem2 (a + Z.of_nat i) (firstn k (skipn i l)).
Proof.
intros W2 mem2 a l i k H Hik. unfold bytes_at8 in *.
assert (Hd : bv_unsigned (Z_to_bv 8 0) = 0) by reflexivity.
assert (E : forall (m : list byte) (j0 : nat),
  nth j0 (map (fun b : byte => bv_unsigned b) m) 0 = bv_unsigned (nth j0 m (Z_to_bv 8 0))).
{ intros m j0. rewrite <- Hd at 1. apply (map_nth (fun b : byte => bv_unsigned b) m (Z_to_bv 8 0) j0). }
intros j Hj. rewrite length_map, length_firstn, length_skipn in Hj.
assert (Hj' : (j < k)%nat) by (clear - Hj Hik; lia).
assert (EQ : nth j (map (fun b : byte => bv_unsigned b) (firstn k (skipn i l))) 0 =
             nth (i + j) (map (fun b : byte => bv_unsigned b) l) 0).
{ rewrite !E. f_equal. rewrite SIM.si_nth_firstn by exact Hj'. apply SIM.si_nth_skipn. }
rewrite EQ. replace (a + Z.of_nat i + Z.of_nat j) with (a + Z.of_nat (i + j)) by (clear; lia).
apply H. rewrite length_map. clear - Hik Hj'. lia.
Qed.

(* ---- the three heap buffers ------------------------------------------------------------------------------ *)
Lemma si_blocks3 : forall g ly2 S2 W2 mem2 md2 nm tk dp a b c,
  AR SEGS B ly2 S2 W2 mem2 md2 -> hblocks B g ly2 S2 [(nm, a); (tk, b); (dp, c)] ->
  In (nm, a) (ablocks B ly2 S2) /\ In (tk, b) (ablocks B ly2 S2) /\ In (dp, c) (ablocks B ly2 S2) /\
  4096 <= nm /\ 4096 <= tk /\ 4096 <= dp /\ 0 <= a /\ 0 <= b /\ 0 <= c /\
  zdisjoint (nm, req_size a) (tk, req_size b) /\ zdisjoint (nm, req_size a) (dp, req_size c) /\
  zdisjoint (tk, req_size b) (dp, req_size c).
Proof.
intros g ly2 S2 W2 mem2 md2 nm tk dp a b c HAR (Hperm & Hpos).
inversion Hpos as [|x xs Hx Hxs]; subst. inversion Hxs as [|y ys Hy Hys]; subst.
inversion Hys as [|z zs Hz Hzs]; subst. cbn [fst snd] in Hx, Hy, Hz.
assert (Hin : forall u, In u [(nm, a); (tk, b); (dp, c)] -> In u (ablocks B ly2 S2)).
{ intros u Hu. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. exact Hu. }
split; [apply Hin; cbn; tauto|]. split; [apply Hin; cbn; tauto|]. split; [apply Hin; cbn; tauto|].
split; [clear - Hx; lia|]. split; [clear - Hy; lia|]. split; [clear - Hz; lia|].
split; [clear - Hx; lia|]. split; [clear - Hy; lia|]. split; [clear - Hz; lia|].
assert (P1 : Permutation (ablocks B ly2 S2) ((nm, a) :: (tk, b) :: ((dp, c) :: ablocks B (e_ly g) (e_S g)))).
{ eapply Permutation_trans; [exact Hperm|]. cbn [app]. apply Permutation_refl. }
assert (P2 : Permutation (ablocks B ly2 S2) ((nm, a) :: (dp, c) :: ((tk, b) :: ablocks B (e_ly g) (e_S g)))).
{ eapply Permutation_trans; [exact P1|]. apply perm_skip. apply perm_swap. }
assert (P3 : Permutation (ablocks B ly2 S2) ((tk, b) :: (dp, c) :: ((nm, a) :: ablocks B (e_ly g) (e_S g)))).
{ eapply Permutation_trans; [exact P1|]. eapply Permutation_trans; [apply perm_swap|].
  apply perm_skip. apply perm_swap. }
split; [exact (sep_blocks_perm SEGS B LAWS _ _ _ _ _ _ _ _ HAR P1)|].
split; [exact (sep_blocks_perm SEGS B LAWS _ _ _ _ _ _ _ _ HAR P2)|].
exact (sep_blocks_perm SEGS B LAWS _ _ _ _ _ _ _ _ HAR P3).
Qed.

(* ---- the cut points of segment I ------------------------------------------------------------------------- *)
(* The said_name argument of reac_box_name: &id.model_name when the identity has a name, NULL otherwise
   (0x81a3c..0x81a54: s11 = id[20], a2 = (s11 == 0) - 1, s4 = a2 & mf+136). *)
Definition si_said (g : ectx) (pos : Z) : Z :=
  if RcIdentModel.has_model_name (m_id g (m_nrec g)) =? 0 then 0 else SFa g pos + V_id + 3.

(* +0x12b8 (0x81a2c), the join of the family branch: s2 = the family. *)
Definition si_C1 (g : ectx) (pos mf : Z) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 4) (BASE + 0x12b8)
(fun ly2 S2 W2 regs2 mem2 md2 =>
si_vals g pos mf W2 mem2 /\ hblocks B g ly2 S2 [] /\ sh_reg g pos regs2 /\
getr regs2 18 = w64 (SlotModel.n_fam (e_pl g)) /\
getr regs2 21 = w64 (SlotModel.t_cap_tok (e_pl g)) /\
getr regs2 26 = w64 (SlotModel.t_cap_name (e_pl g)) /\
getr regs2 22 = w64 (SlotModel.t_cap_disp (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 184) 8 (SFa g pos + V_id)).

(* +0x12e8 (0x81a5c), the first buf_of call: a0 = cap_name, s3 = cap_tok, s4 = said_name, s11 = id[20]. *)
Definition si_C2 (g : ectx) (pos mf : Z) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 4) (BASE + 0x12e8)
(fun ly2 S2 W2 regs2 mem2 md2 =>
si_vals g pos mf W2 mem2 /\ hblocks B g ly2 S2 [] /\ sh_reg g pos regs2 /\
getr regs2 10 = w64 (SlotModel.t_cap_name (e_pl g)) /\
getr regs2 18 = w64 (SlotModel.n_fam (e_pl g)) /\
getr regs2 19 = w64 (SlotModel.t_cap_tok (e_pl g)) /\
getr regs2 20 = w64 (si_said g pos) /\
getr regs2 22 = w64 (SlotModel.t_cap_disp (e_pl g)) /\
getr regs2 27 = w64 (RcIdentModel.has_model_name (m_id g (m_nrec g))) /\
val_mem SEGS (rd W2 mem2) (mf + 184) 8 (SFa g pos + V_id) /\
val_mem SEGS (rd W2 mem2) (mf + 144) 8 (SlotModel.t_cap_name (e_pl g))).

(* +0x1304 (0x81a78), the three buffers made: a0 = dp, s5 = tk, mf+152 = nm. *)
Definition si_C3 (g : ectx) (pos mf nm tk dp : Z) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x1304)
(fun ly2 S2 W2 regs2 mem2 md2 =>
si_vals g pos mf W2 mem2 /\ sh_reg g pos regs2 /\
hblocks B g ly2 S2 [(nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1);
(tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1);
(dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1)] /\
getr regs2 10 = w64 dp /\
getr regs2 18 = w64 (SlotModel.n_fam (e_pl g)) /\
getr regs2 19 = w64 (SlotModel.t_cap_tok (e_pl g)) /\
getr regs2 20 = w64 (si_said g pos) /\ getr regs2 21 = w64 tk /\
getr regs2 22 = w64 (SlotModel.t_cap_disp (e_pl g)) /\
getr regs2 27 = w64 (RcIdentModel.has_model_name (m_id g (m_nrec g))) /\
val_mem SEGS (rd W2 mem2) (mf + 184) 8 (SFa g pos + V_id) /\
val_mem SEGS (rd W2 mem2) (mf + 152) 8 nm /\
val_mem SEGS (rd W2 mem2) (mf + 144) 8 (SlotModel.t_cap_name (e_pl g))).

(* +0x1348 (0x81abc), past the refusing call and its check: mf+184 = dp, mf+128 = cap_tok, sp = mf. *)
Definition si_C4 (g : ectx) (pos mf nm tk dp : Z) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x1348)
(fun ly2 S2 W2 regs2 mem2 md2 =>
si_vals g pos mf W2 mem2 /\ sh_reg g pos regs2 /\
hblocks B g ly2 S2 [(nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1);
(tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1);
(dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1)] /\
getr regs2 18 = w64 (SlotModel.n_fam (e_pl g)) /\
getr regs2 19 = w64 (SlotModel.t_cap_tok (e_pl g)) /\
getr regs2 20 = w64 (si_said g pos) /\ getr regs2 21 = w64 tk /\
getr regs2 22 = w64 (SlotModel.t_cap_disp (e_pl g)) /\
getr regs2 27 = w64 (RcIdentModel.has_model_name (m_id g (m_nrec g))) /\
val_mem SEGS (rd W2 mem2) (mf + 184) 8 dp /\
val_mem SEGS (rd W2 mem2) (mf + 152) 8 nm /\
val_mem SEGS (rd W2 mem2) (mf + 144) 8 (SlotModel.t_cap_name (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 128) 8 (SlotModel.t_cap_tok (e_pl g))).

(* ---- the said-name premise of reac_box_name at the real call (0x81aec) ------------------------------------ *)
(* said = &id.model_name (SF + 352 + 3) when the identity has a name, NULL otherwise; the name and its NUL lie in
   id (bytes 3 .. 3 + len), its shadow is id's block shadow, the 8-byte word tail and the shadow hull lie in the
   class-4 frame and its shadow, both present. *)
Lemma si_real_said : forall g pos mf ly2 S2 W2 mem2 md2 k,
  AJ g pos ly2 S2 W2 mem2 md2 k -> frames S2 = [(4, pos)] -> e_sp0 g - 336 <= mf <= e_sp0 g - 320 ->
  id_at g pos (m_nrec g) W2 mem2 ->
  reac_box_name_inv.rbn_said ly2 S2 W2 mem2 (si_said g pos) (SIM.si_sdZ (e_pl g)).
Proof.
intros g pos mf ly2 S2 W2 mem2 md2 k HJ Hfrs Hmf (HB & _ & HSB).
destruct (si_geo g pos mf ly2 S2 W2 mem2 md2 k HJ Hfrs Hmf)
  as (_ & _ & _ & _ & EFa & HSF0 & HSF1 & HSF64 & Hin).
change (m_id g (m_nrec g)) with (SlotModel.idT (e_pl g)) in HB.
unfold si_said, reac_box_name_inv.rbn_said. change (m_id g (m_nrec g)) with (SlotModel.idT (e_pl g)).
destruct (Z.eqb_spec (RcIdentModel.has_model_name (SlotModel.idT (e_pl g))) 0) as [H0 | H0].
{ left. split; [reflexivity | exact (SIM.si_said_nil _ H0)]. }
right. rewrite (SIM.si_said_cons _ H0).
pose proof (SIM.si_name_len (e_pl g)) as HL.
pose proof (SlotModel.rec_id_length (e_pl g) (SlotModel.nrecn (e_pl g))) as HLI.
change (SlotModel.rec_id (e_pl g) (SlotModel.nrecn (e_pl g))) with (SlotModel.idT (e_pl g)) in HLI.
unfold RcIdentModel.ID_SIZE in HLI.
pose proof (si_garr8_slice W2 mem2 (SFa g pos + V_id) (SlotModel.idT (e_pl g)) 3%nat
  (length (SlotModel.name_str (SlotModel.idT (e_pl g))) + 1)%nat HB ltac:(clear - HL HLI; lia)) as HS.
assert (HG : garr8 SEGS (rd W2 mem2) (SFa g pos + V_id + 3)
  (map RcIdentModel.bz (SlotModel.name_str (SlotModel.idT (e_pl g))) ++ [0])).
{ replace (map RcIdentModel.bz (SlotModel.name_str (SlotModel.idT (e_pl g))) ++ [0])
    with (map RcIdentModel.bz (SlotModel.name_str (SlotModel.idT (e_pl g)) ++ [RcIdentModel.zb 0]))
    by (rewrite map_app; cbn [map]; rewrite SIM.si_bz0; reflexivity).
  rewrite <- SIM.si_name_bytes. exact HS. }
pose proof (SIM.si_name_nz (e_pl g)) as HNZ.
assert (Hsd : (length (map RcIdentModel.bz (SlotModel.name_str (SlotModel.idT (e_pl g)))) <= 16)%nat)
  by (rewrite length_map; exact HL).
clear HS HB HL HLI H0.
set (sd := map RcIdentModel.bz (SlotModel.name_str (SlotModel.idT (e_pl g)))) in *.
clearbody sd.
change V_id with 352 in HG, HSB |- *. change N_id with 38 in HSB.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
assert (HP : forall a, (SFa g pos <= a < SFa g pos + 1024 \/
    SHADOW_OFF + SFa g pos / 8 <= a < SHADOW_OFF + SFa g pos / 8 + 128) ->
  aview SEGS (w_H W2) mem2 a <> None).
{ intros a Ha. exact (si_frame_present g pos ly2 S2 W2 mem2 md2 k a HJ Ha). }
assert (Hn : 0 <= Z.of_nat (length sd) <= 16) by (clear - Hsd; lia).
split; [clear - HSF0; lia|].
split.
- unfold reac_box_name_inv.rbn_cstr.
  split; [exact HNZ|].
  split; [clear - Hn; lia|].
  split; [clear - HSF0; lia|].
  split.
  { apply (YC1h.amem_range_sub_app (SFa g pos) 1024); [exact Hin | exact HSF1 | clear - Hn; lia ..]. }
  split; [exact HG|].
  split.
  { apply (si_ra_sub W2 mem2 (SFa g pos + 352) 38); [exact HSB | clear - Hn; lia ..]. }
  split.
  { intros s Hs. apply HP. right. unfold shadow_addr in Hs. clear - Hs Hn HSF64. unfold SHADOW_OFF in *. lia. }
  intros x Hx. apply HP. left. clear - Hx Hn. lia.
- exists 4, pos. rewrite EFa, HFB.
  split; [rewrite Hfrs; left; reflexivity|].
  clear - Hn; lia.
Qed.
Check (si_real_said : forall g pos mf ly2 S2 W2 mem2 md2 k, AJ g pos ly2 S2 W2 mem2 md2 k -> frames S2 = [(4, pos)] -> e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> id_at g pos (m_nrec g) W2 mem2 -> reac_box_name_inv.rbn_said ly2 S2 W2 mem2 (si_said g pos) (SIM.si_sdZ (e_pl g))).

(* ---- si_L_ref: +0x1304 .. +0x1348 (0x81a78 .. 0x81abc), the refusing reac_box_name call -------------------- *)
(* The symbolic state at +0x1304: the two machine-frame slots the run writes (mf+184 at 0x81a88, mf+128 at 0x81aa4;
   base s1 = atom 9) and the two stack-argument words below mf (display at 0x81a8c, display_len at 0x81a90; base
   the entry value of sp = atom 2 = mf, which 0x81a78 moves down by 16). All writable, no value known at entry. *)
Definition si_ref_m128 : YP09.region := YP09.mkRegion (Some 9%nat) 128 136 128 136 [].
Definition si_ref_m184 : YP09.region := YP09.mkRegion (Some 9%nat) 184 192 184 192 [].
Definition si_ref_args : YP09.region := YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [].
Definition si_ref_ss : sstate := mkSS 0x1304 sr_atoms [si_ref_m128; si_ref_m184; si_ref_args] None (mkFacts [] [] []).

(* The read-only image at any state of the entry's journal (as lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_pre.v j_img). *)
Lemma si_ref_img : forall (g : ectx) pos k ly2 S2 (W2 : world SEGS) mem2 md2,
  AJ g pos ly2 S2 W2 mem2 md2 k -> EPRE g ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mem2).
Proof.
intros g pos k ly2 S2 W2 mem2 md2 HJ HPRE.
apply (IdentBase.arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B LLVMF_STK (e_sp0 g) [] (e_ly g)
  (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 mem2 md2 k HJ).
destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROD & _). apply HRO. exact HROD.
Qed.

(* A block that hblocks names is not a block of the entry state: it would appear twice in the permutation. *)
Lemma si_ref_fresh : forall (g : ectx) ly2 S2 (W2 : world SEGS) mem2 md2 hs x,
  AR SEGS B ly2 S2 W2 mem2 md2 -> hblocks B g ly2 S2 hs -> In x hs -> ~ In x (ablocks B (e_ly g) (e_S g)).
Proof.
intros g ly2 S2 W2 mem2 md2 hs x HAR (Hperm & Hpos) Hx Hin.
assert (Hx0 : 0 <= snd x) by exact (proj2 (proj1 (Forall_forall _ _) Hpos x Hx)).
apply in_split in Hx as (l1 & l2 & El). apply in_split in Hin as (m1 & m2 & Em).
assert (P : Permutation (ablocks B ly2 S2) (x :: x :: (l1 ++ l2 ++ m1 ++ m2))).
{ eapply Permutation_trans; [exact Hperm|]. rewrite El, Em.
  eapply Permutation_trans; [apply Permutation_app; apply Permutation_sym, Permutation_middle|].
  cbn [app]. apply perm_skip.
  eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|].
  rewrite <- app_assoc. apply Permutation_refl. }
pose proof (sep_blocks_perm SEGS B LAWS _ _ _ _ _ _ _ _ HAR P) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. pose proof (req_size_pos (snd x) Hx0) as Hr.
clear - Hd Hr. lia.
Qed.

(* The step: run to the call (two frame slots and the two stack arguments stored), reac_box_name with name = NULL
   (refused: a0 = -1, buffers and frame kept), run to the bne at +0x1344 (not taken), then to +0x1348. *)
Lemma si_L_ref : forall g pos mf nm tk dp W2 c2, si_C3 g pos mf nm tk dp W2 c2 ->
  SRr SEGS W2 c2 (si_C4 g pos mf nm tk dp).
Proof.
intros g pos mf nm tk dp W2 c2 Hstart.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HP as (HV & Hshr & Hbl & R10 & R18 & R19 & R20 & R21 & R22 & R27 & V184 & V152 & V144).
pose proof HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & _ & _ & _ & _ & Vra & Vs0 &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRE & _ & _ & _).
pose proof HPRE as (_ & _ & _ & _ & Hinp & Hlen & _ & _ & Hnev0 & _).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
assert (Has : ASTACK = 16384) by reflexivity.
destruct (si_geo g pos mf ly2 S2 W2 mem2 md2 _ HJ Hfrs Hmfb)
  as (Hmf0 & H47 & Hsp0al & Hceil & EFa & HSF0 & HSF1 & HSF64 & HSFapp).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & Hnev2 & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (Hct : 0 <= SlotModel.t_cap_tok (e_pl g) < 40) by (unfold SlotModel.t_cap_tok; apply Z.mod_pos_bound; lia).
assert (Hcd : 0 <= SlotModel.t_cap_disp (e_pl g) < 64) by (unfold SlotModel.t_cap_disp; apply Z.mod_pos_bound; lia).
pose proof (SIM.si_nfam_range (e_pl g)) as Hfam.
destruct (si_blocks3 g ly2 S2 W2 mem2 md2 nm tk dp _ _ _ HAR2 Hbl)
  as (Inm & Itk & Idp & Hnm4 & Htk4 & Hdp4 & _ & _ & _ & _ & _ & _).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 tk _ HAR2 Itk) as (_ & _ & Htkce & _).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 dp _ HAR2 Idp) as (_ & _ & Hdpce & _).
pose proof (req_size_pos (Z.max (SlotModel.t_cap_tok (e_pl g)) 1) ltac:(lia)) as Rtk.
pose proof (req_size_pos (Z.max (SlotModel.t_cap_disp (e_pl g)) 1) ltac:(lia)) as Rdp.
assert (Ftk : ~ In (tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1) (ablocks B (e_ly g) (e_S g)))
  by (apply (si_ref_fresh g ly2 S2 W2 mem2 md2 _ _ HAR2 Hbl); cbn; tauto).
assert (Fdp : ~ In (dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1) (ablocks B (e_ly g) (e_S g)))
  by (apply (si_ref_fresh g ly2 S2 W2 mem2 md2 _ _ HAR2 Hbl); cbn; tauto).
(* the environment: the registers only *)
remember (Eimg (Ereg regs2 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
clear HE.
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), Rs1. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Has C1. lia. }
assert (U2 : bv_unsigned (ew E 2) = mf).
{ rewrite (EE 2%nat 2%bv eq_refl), Rsp. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Has C1. lia. }
(* the symbolic state at +0x1304 *)
assert (HS : st_ok_pi SEGS VAL E si_ref_ss
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x1304)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold si_ref_ss. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil;
    unfold si_ref_m128, si_ref_m184, si_ref_args, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite ?U9, ?U2;
    (split; [clear - Hmf0 Has C1; lia|]); (split; [clear - Hmfb H47; lia|]); (split; [|constructor]);
    intros o Ho; apply (apresent_writable SEGS); apply Hpres2; clear - Ho Hmfb HSTK' Has; lia.
  - apply pairwise_disjoint_of_extents. unfold si_ref_m128, si_ref_m184, si_ref_args, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U2.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I]. }
unfold cfg_at. change (w64 (BASE + 0x1304)) with (Z_to_bv 64 (BASE + 0x1304)).
(* ---- run 1: +0x1304 .. the call at +0x1338 ---- *)
paj_run_shc RUNP RUNC HS HJ.
{ intros a (r & Hr & Ha). unfold si_ref_ss in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; unfold si_ref_m128, si_ref_m184, si_ref_args in Ha;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?U9, ?U2 in Ha;
  left; clear - Ha Hmfb HSTK' Has; lia. }
rename ms into ms1, HJ into HJ1, HFr into HFr1, mat into mat1. clear HF HG.
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (mf - 16 <= a < mf \/ mf + 128 <= a < mf + 136 \/ mf + 184 <= a < mf + 192) ->
  aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw.
  apply (kept_of_frame E _ (w_H W2) mem2 (ms_mem ms1)
    (fun x => mf - 16 <= x < mf \/ mf + 128 <= x < mf + 136 \/ mf + 184 <= x < mf + 192) HFr1); [|exact Ha|exact Hw].
  intros bb wlo whi aa Hin Hr. unfold si_ref_ss, windows in Hin. cbn in Hin.
  destruct Hin as [Eq | [Eq | [Eq | []]]]; injection Eq as <- <- <-; cbn [base_val] in Hr; rewrite ?U9, ?U2 in Hr;
  clear - Hr; lia. }
(* the registers at the call *)
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14.
prreg HS (15%bv : bv 5) Q15. prreg HS (16%bv : bv 5) Q16. prreg HS (17%bv : bv 5) Q17.
rewrite U2 in Q2.
rewrite (EE 3%nat 3%bv eq_refl), Rgp in Q3. rewrite (EE 4%nat 4%bv eq_refl), Rtp in Q4.
rewrite (EE 8%nat 8%bv eq_refl), Rs0 in Q8. rewrite (EE 18%nat 18%bv eq_refl), R18 in Q10.
rewrite (EE 20%nat 20%bv eq_refl), R20 in Q11. rewrite (EE 21%nat 21%bv eq_refl), R21 in Q16.
rewrite (EE 19%nat 19%bv eq_refl), R19 in Q17.
assert (Usp1 : spZ (ms_regs ms1) = mf - 16).
{ unfold spZ. rewrite Q2. rewrite unsigned_lit_small by (clear - Hmf0 H47 Hmfb Has C1; lia). lia. }
assert (Us01 : s0Z (ms_regs ms1) = e_sp0 g).
{ unfold s0Z. rewrite Q8. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Has C1. lia. }
assert (Vra1 : val_mem SEGS (rd W2 (ms_mem ms1)) (e_sp0 g - 8) 8 RA_LLVMF).
{ apply (val_mem_kept SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms1) _ 8%nat _); [|exact Vra].
  intros kk Hkk. apply KEEP1; clear - Hkk Hmfb H47 Hmf0 Has C1; lia. }
assert (Vs01 : val_mem SEGS (rd W2 (ms_mem ms1)) (e_sp0 g - 16) 8 (s0Z (e_regs g))).
{ apply (val_mem_kept SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms1) _ 8%nat _); [|exact Vs0].
  intros kk Hkk. apply KEEP1; clear - Hkk Hmfb H47 Hmf0 Has C1; lia. }
(* the two stack arguments the run stored *)
pose proof (st_ok_region_nth E _ _ 2 _ HS eq_refl) as RG2. cbn [ms_mem restrict] in RG2.
assert (VD : val_mem SEGS (rd W2 (ms_mem ms1)) (spZ (ms_regs ms1)) 8 dp).
{ rewrite Usp1. replace (mf - 16) with (mf + -16) by lia.
  apply (field_of_region E _ 2%nat mf _ (-16) 0 (-16) 0 (-16) 8%N (SOff 10 0) dp RG2 U2);
  [cbn [In]; auto | | clear - Hdp4 Hdpce Rdp C1; lia | lia].
  cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 10%nat 10%bv eq_refl). exact R10. }
assert (VDL : val_mem SEGS (rd W2 (ms_mem ms1)) (spZ (ms_regs ms1) + 8) 8 (SlotModel.t_cap_disp (e_pl g))).
{ rewrite Usp1. replace (mf - 16 + 8) with (mf + -8) by lia.
  apply (field_of_region E _ 2%nat mf _ (-16) 0 (-16) 0 (-8) 8%N (SOff 22 0) _ RG2 U2);
  [cbn [In]; auto | | clear - Hcd; lia | lia].
  cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 22%nat 22%bv eq_refl). exact R22. }
clear RG2.
(* ---- the call reac_box_name (f, said, 8, 8, NULL, 8, tk, cap_tok, dp, cap_disp) at +0x1338 ---- *)
pmkst HS. rewrite (PSIG IB_reac_box_name AF_reac_box_name eq_refl).
assert (HROc : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) (ms_mem ms1)))
  by exact (si_ref_img g pos _ ly2 S2 W2 (ms_mem ms1) _ HJ1 HPRE).
destruct (HIMG W2 (ms_mem ms1) HROc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrbn & _).
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
eapply SRr_bind.
{ refine (si_call g pos W2 (ms_regs ms1) (ms_mem ms1) _ ly2 S2 _ _ reac_box_name.REAC_BOX_NAME_STK
    (reac_box_name_inv.rbn_fp 0 8 tk (SlotModel.t_cap_tok (e_pl g)) dp (SlotModel.t_cap_disp (e_pl g)))
    reac_box_name.EV_REAC_BOX_NAME (mf - 16 - e_sp0 g) (getr (ms_regs ms1) 1)
    (fun ly3 S3 W3 regs3 mem3 md3 => reac_box_name_inv.rbn_postQ B ly2 S2 W2 (ms_mem ms1)
       (SlotModel.n_fam (e_pl g)) [] 8 8 0 8 tk (SlotModel.t_cap_tok (e_pl g)) dp (SlotModel.t_cap_disp (e_pl g))
       ly3 S3 W3 regs3 mem3 md3)
    HJ1 HPRE _ _ _ _ _ Q3 Q4 eq_refl _ _ Us01 Vra1 Vs01 _ _).
  - rewrite Usp1. lia.
  - clear - Hmf32 Hsp0al. lia.
  - clear - Hmfb. lia.
  - unfold reac_box_name.REAC_BOX_NAME_STK, ESTACK. lia.
  - unfold reac_box_name.REAC_BOX_NAME_STK, ESTACK. clear - Hmfb HSTK' Has. lia.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Q1, unsigned_lit_small by (clear - HBASE; lia). clear - HBLO. lia.
  - intros ch1 Hchs HFN.
    refine (HBN ly2 S2 W2 (ms_regs ms1) (ms_mem ms1) _ ch1 (SlotModel.n_fam (e_pl g)) (si_said g pos) 8 8 0 8 tk
      (SlotModel.t_cap_tok (e_pl g)) dp (SlotModel.t_cap_disp (e_pl g)) [] HFN HROc Q10 _ Q11 _ Q12 _ Q13 _ Q14 _
      Q15 _ Q16 _ Q17 _ _ VD _ VDL _ Hrbn _ _ _ _).
    + clear - Hfam. lia.
    + unfold si_said. destruct (_ =? 0); unfold V_id; clear - HSF0 HSF1 C1; lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + clear - Htk4 Htkce Rtk C1. lia.
    + clear - Hct. lia.
    + intros a Ha. rewrite Usp1 in Ha. apply Hpres1. clear - Ha Hmfb HSTK' Has. lia.
    + clear - Hdp4 Hdpce Rdp C1. lia.
    + clear - Hcd. lia.
    + intros Hok. rewrite SIM.si_args_refuse in Hok. discriminate Hok.
    + rewrite Hfrs. cbn. lia.
    + unfold reac_box_name.EV_REAC_BOX_NAME. clear - Hnev2 Hnev0 Hk HEV. lia.
    + pose proof (wf_live _ _ _ _ _ (am_wf _ _ _ _ (proj1 HAR2))) as HL.
      unfold reac_box_name.LIVE_REAC_BOX_NAME. clear - HL. lia.
  - intros a Ha. apply reac_box_name_inv.rbn_fp_in in Ha.
    destruct Ha as [[Hn0 _] | [[_ Ha] | [_ Ha]]]; [exfalso; exact (Hn0 eq_refl) | |].
    + exists tk, (Z.max (SlotModel.t_cap_tok (e_pl g)) 1). split; [exact Itk|]. split; [exact Ftk|].
      clear - Ha Rtk Hct. lia.
    + exists dp, (Z.max (SlotModel.t_cap_disp (e_pl g)) 1). split; [exact Idp|]. split; [exact Fdp|].
      clear - Ha Rdp Hcd. lia. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc & HP3 & HQ3).
unfold reac_box_name_inv.rbn_postQ in HQ3. rewrite SIM.si_refuse in HQ3.
destruct HQ3 as (-> & Hperm3 & Ha0 & Hkeep3).
rewrite Q1.
(* back at +0x133c: the three regions survive the call (all at or above the call's sp = mf - 16) *)
jafter_call_keep_hi HS 512%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0; 1; 2]%nat HS3.
match type of HS3 with ?Q -> _ => assert (HQ : Q); [|specialize (HS3 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  (eapply (region_kept_stack_sub SEGS B E); [exact HJc | exact HJ3 | first [exact U9 | exact U2] | ..]);
  clear - Hmfb HSTK' Has; unfold reac_box_name.REAC_BOX_NAME_STK, ESTACK; lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
pose proof (img_env_havoc_hi E 512%nat (map (getr regs3) CLOB) HEI ltac:(cbv; lia)) as HEI3.
assert (U9' : bv_unsigned (ew (havoc E 512 (map (getr regs3) CLOB)) 9) = mf)
  by (rewrite ew_havoc_old by (cbv; lia); exact U9).
assert (U2' : bv_unsigned (ew (havoc E 512 (map (getr regs3) CLOB)) 2) = mf)
  by (rewrite ew_havoc_old by (cbv; lia); exact U2).
(* ---- run 2: +0x133c .. the check at +0x1344 ---- *)
paj_run_sh RUNP HS HJ3.
{ intros a (r & Hr & Ha). cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
  rewrite ew_havoc_old in Ha by (cbv; lia); rewrite ?U9, ?U2 in Ha; left; clear - Ha Hmfb HSTK' Has; lia. }
rename ms into ms2, HFr into HFr2, mat into mat2. clear HF HG.
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (mf - 16 <= a < mf \/ mf + 128 <= a < mf + 136 \/ mf + 184 <= a < mf + 192) ->
  aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) mem3 a).
{ intros a Ha Hw.
  apply (kept_of_frame _ _ (w_H W2) mem3 (ms_mem ms2)
    (fun x => mf - 16 <= x < mf \/ mf + 128 <= x < mf + 136 \/ mf + 184 <= x < mf + 192) HFr2); [|exact Ha|exact Hw].
  intros bb wlo whi aa Hin Hr. cbn in Hin.
  destruct Hin as [Eq | [Eq | [Eq | []]]]; injection Eq as <- <- <-; cbn [base_val] in Hr; rewrite ?U9', ?U2' in Hr;
  clear - Hr; lia. }
(* 0x81ab8: a0 = -1 (the call refused), so the bne to the abort path is not taken *)
psrr_branch_pi RUNP BR HS.
{ exfalso.
  assert (A516 : ew (havoc E 512 (map (getr regs3) CLOB)) 516 = Z_to_bv 64 (-1)).
  { change 516%nat with (512 + 4)%nat.
    rewrite (ew_havoc_new E 512 _ 4 (Z_to_bv 64 0)) by (rewrite length_map; apply Nat.ltb_lt; reflexivity).
    change (nth 4 (map (getr regs3) CLOB) (Z_to_bv 64 0)) with (getr regs3 10). exact Ha0. }
  cbn [sv_denot] in Hc. rewrite A516 in Hc. vm_compute in Hc. discriminate Hc. }
(* ---- run 3: the not-taken branch, to +0x1348 ---- *)
paj_run_to_sh RUNTOP HS HJ3 0x1348.
{ intros a (r & Hr & Ha). cbn in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
  rewrite ?U9', ?U2' in Ha; left; clear - Ha Hmfb HSTK' Has; lia. }
rename ms into ms3, HFr into HFr3, mat into mat3. clear HF HG.
assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (mf - 16 <= a < mf \/ mf + 128 <= a < mf + 136 \/ mf + 184 <= a < mf + 192) ->
  aview SEGS (w_H W2) (ms_mem ms3) a = aview SEGS (w_H W2) (ms_mem ms2) a).
{ intros a Ha Hw.
  apply (kept_of_frame _ _ (w_H W2) (ms_mem ms2) (ms_mem ms3)
    (fun x => mf - 16 <= x < mf \/ mf + 128 <= x < mf + 136 \/ mf + 184 <= x < mf + 192) HFr3); [|exact Ha|exact Hw].
  intros bb wlo whi aa Hin Hr. cbn in Hin.
  destruct Hin as [Eq | [Eq | [Eq | []]]]; injection Eq as <- <- <-; cbn [base_val] in Hr; rewrite ?U9', ?U2' in Hr;
  clear - Hr; lia. }
(* ---- what the step kept: si_area through the two runs, the call and the third run ---- *)
assert (HINP : 0 < e_n g -> In (e_p g, e_n g) (ablocks B ly2 S2) /\ In (e_p g, e_n g) (ablocks B ly3 S3)).
{ intros Hn0. destruct Hinp as [[Hn _] | [_ Hine]]; [clear - Hn Hn0; lia|].
  assert (I2 : In (e_p g, e_n g) (ablocks B ly2 S2))
    by (apply (Permutation_in _ (Permutation_sym (proj1 Hbl))); apply in_or_app; right; exact Hine).
  split; [exact I2 | apply (Permutation_in _ (Permutation_sym Hperm3)); exact I2]. }
assert (HFPK : forall a,
  inFP (reac_box_name_inv.rbn_fp 0 8 tk (SlotModel.t_cap_tok (e_pl g)) dp (SlotModel.t_cap_disp (e_pl g))) a ->
  exists b n, In (b, n) (ablocks B ly2 S2) /\ (b, n) <> (e_p g, e_n g) /\ b <= a < b + req_size n).
{ intros a Ha. apply reac_box_name_inv.rbn_fp_in in Ha.
  destruct Ha as [[Hn0 _] | [[_ Ha] | [_ Ha]]]; [exfalso; exact (Hn0 eq_refl) | |].
  - exists tk, (Z.max (SlotModel.t_cap_tok (e_pl g)) 1). split; [exact Itk|]. split; [|clear - Ha Rtk Hct; lia].
    intros Heq. destruct Hinp as [[Hn _] | [_ Hine]].
    + injection Heq as Hp Hm. clear - Hm Hn. lia.
    + apply Ftk. rewrite Heq. exact Hine.
  - exists dp, (Z.max (SlotModel.t_cap_disp (e_pl g)) 1). split; [exact Idp|]. split; [|clear - Ha Rdp Hcd; lia].
    intros Heq. destruct Hinp as [[Hn _] | [_ Hine]].
    + injection Heq as Hp Hm. clear - Hm Hn. lia.
    + apply Fdp. rewrite Heq. exact Hine. }
assert (AREA : forall a, si_area g pos mf a -> 0 <= a < 2 ^ 64 /\
  ~ (mf - 16 <= a < mf \/ mf + 128 <= a < mf + 136 \/ mf + 184 <= a < mf + 192)).
{ intros a Ha. unfold si_area in Ha.
  assert (Esh : shadow_addr (SFa g pos) = SHADOW_OFF + SFa g pos / 8) by reflexivity.
  assert (Hsh : 0 <= shadow_addr (SFa g pos) /\ shadow_addr (SFa g pos) + 128 <= alloc_ceiling)
    by (clear - Esh HSF0 HSF1 C1; unfold SHADOW_OFF in Esh; lia).
  destruct Ha as [Hs | [Hf | [Hs2 | Hi]]].
  - clear - Hs Hmfb H47 Hmf0 Has C1. lia.
  - clear - Hf HSF0 HSF1 Hmf0 Has C1. lia.
  - clear - Hs2 Hsh Hmf0 Has C1. lia.
  - assert (Hn0 : 0 < e_n g) by (clear - Hi; lia).
    destruct (HINP Hn0) as [I2 _].
    destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 I2) as (_ & Hp4 & Hpce & _).
    pose proof (req_size_pos (e_n g) ltac:(lia)) as Hrq.
    clear - Hi Hp4 Hpce Hrq Hmf0 Has C1. lia. }
assert (HK : forall a, si_area g pos mf a -> aview SEGS (w_H W2) (ms_mem ms3) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. destruct (AREA a Ha) as [Hr Hw].
  rewrite (KEEP3 a Hr Hw), (KEEP2 a Hr Hw).
  rewrite (si_area_kept_call g pos mf ly2 S2 W2 (ms_mem ms1) _ _ ly3 S3 W2 mem3 md3 _ _ _ _ HJ1 Hfrs HJc Hmfb
    ltac:(clear; lia) ltac:(unfold reac_box_name.REAC_BOX_NAME_STK, ESTACK; lia) HINP HFPK a Ha).
  exact (KEEP1 a Hr Hw). }
assert (HVf : si_vals g pos mf W2 (ms_mem ms3)).
{ apply (si_vals_moved g pos mf W2 mem2 W2 (ms_mem ms3)); [clear - Hmfb; lia | clear - HSF64; lia | exact Hlen | exact HK | exact HV]. }
pose proof HJc as (_ & _ & _ & _ & _ & Hfrs3 & _ & _ & F1c & _).
assert (STACKK : forall a, mf <= a < e_sp0 g -> ~ (mf + 128 <= a < mf + 136 \/ mf + 184 <= a < mf + 192) ->
  aview SEGS (w_H W2) (ms_mem ms3) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw.
  assert (Hr : 0 <= a < 2 ^ 64) by (clear - Ha Hmf0 H47 Has C1; lia).
  assert (Hw' : ~ (mf - 16 <= a < mf \/ mf + 128 <= a < mf + 136 \/ mf + 184 <= a < mf + 192)) by (clear - Ha Hw; lia).
  rewrite (KEEP3 a Hr Hw'), (KEEP2 a Hr Hw').
  rewrite F1c; [exact (KEEP1 a Hr Hw') | clear - Ha Hmf0 H47 Has C1; lia | clear - Ha; lia]. }
assert (V152f : val_mem SEGS (rd W2 (ms_mem ms3)) (mf + 152) 8 nm).
{ apply (val_mem_kept SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms3) _ 8%nat _); [|exact V152].
  intros kk Hkk. apply STACKK; clear - Hkk Hmfb; lia. }
assert (V144f : val_mem SEGS (rd W2 (ms_mem ms3)) (mf + 144) 8 (SlotModel.t_cap_name (e_pl g))).
{ apply (val_mem_kept SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms3) _ 8%nat _); [|exact V144].
  intros kk Hkk. apply STACKK; clear - Hkk Hmfb; lia. }
(* the two machine-frame slots the step stored, from the state's chunks *)
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
assert (V128f : val_mem SEGS (rd W2 (ms_mem ms3)) (mf + 128) 8 (SlotModel.t_cap_tok (e_pl g))).
{ apply (field_of_region _ _ 9%nat mf _ 128 136 128 136 128 8%N (SOff 19 0) _ RG0 U9');
  [cbn [In]; auto | | clear - Hct; lia | lia].
  cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, ew_havoc_old by (cbv; lia).
  rewrite (EE 19%nat 19%bv eq_refl). exact R19. }
assert (V184f : val_mem SEGS (rd W2 (ms_mem ms3)) (mf + 184) 8 dp).
{ apply (field_of_region _ _ 9%nat mf _ 184 192 184 192 184 8%N (SOff 10 0) _ RG1 U9');
  [cbn [In]; auto | | clear - Hdp4 Hdpce Rdp C1; lia | lia].
  cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, ew_havoc_old by (cbv; lia).
  rewrite (EE 10%nat 10%bv eq_refl). exact R10. }
clear RG0 RG1.
(* the registers at +0x1348 *)
prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18. prreg HS (19%bv : bv 5) F19. prreg HS (20%bv : bv 5) F20.
prreg HS (21%bv : bv 5) F21. prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23. prreg HS (27%bv : bv 5) F27.
unfold sh_reg in Hshr.
rewrite (EE 2%nat 2%bv eq_refl), Rsp in F2. rewrite (EE 3%nat 3%bv eq_refl), Rgp in F3.
rewrite (EE 4%nat 4%bv eq_refl), Rtp in F4. rewrite (EE 8%nat 8%bv eq_refl), Rs0 in F8.
rewrite (EE 9%nat 9%bv eq_refl), Rs1 in F9. rewrite (EE 18%nat 18%bv eq_refl), R18 in F18.
rewrite (EE 19%nat 19%bv eq_refl), R19 in F19. rewrite (EE 20%nat 20%bv eq_refl), R20 in F20.
rewrite (EE 21%nat 21%bv eq_refl), R21 in F21. rewrite (EE 22%nat 22%bv eq_refl), R22 in F22.
rewrite (EE 23%nat 23%bv eq_refl), Hshr in F23. rewrite (EE 27%nat 27%bv eq_refl), R27 in F27.
unfold reac_box_name.EV_REAC_BOX_NAME in HJ3. rewrite Z.add_0_r in HJ3.
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as [Efd Efs].
destruct (si_meter (e_S g) S2 S3 (4 * Z.of_nat (m_nrec g) + 7) 0 0 ltac:(lia) ltac:(lia) ltac:(clear - Hk; lia)
  MLE MOK (HMT0 S2 S3)) as [MLE3 MOK3].
rewrite Z.add_0_r in MLE3, MOK3.
(* ---- the cut si_C4 at +0x1348 ---- *)
apply SRr_ret. unfold si_C4, acut. pmkst HS.
exists ly3, S3, (ms_regs ms3), (ms_mem ms3). eexists.
split; [reflexivity|].
split; [exact HJ3|].
split; [rewrite Hfrs3; exact Hfrs|].
split; [exact Hk|].
split; [exact MLE3|].
split; [exact MOK3|].
split.
{ apply (si_ecommon g pos mf ly3 S3 W2 (ms_regs ms3) (ms_mem ms3) _ F2 F9 F8 Hmfb Hmf32 F3 F4 HVf HPRE).
  - intros fd. rewrite Efd. reflexivity.
  - exact Efs. }
split; [exact HVf|].
split; [unfold sh_reg; exact F23|].
split; [split; [eapply Permutation_trans; [exact Hperm3 | exact (proj1 Hbl)] | exact (proj2 Hbl)]|].
split; [exact F18|]. split; [exact F19|]. split; [exact F20|]. split; [exact F21|].
split; [exact F22|]. split; [exact F27|].
split; [exact V184f|]. split; [exact V152f|]. split; [exact V144f|]. exact V128f.
Qed.

Check (si_L_ref : forall g pos mf nm tk dp W2 c2, si_C3 g pos mf nm tk dp W2 c2 -> SRr SEGS W2 c2 (si_C4 g pos mf nm tk dp)).

(* ---- si_L_fam: +0x128c .. +0x12b8 (0x81a00 .. 0x81a2c) ------------------------------------------------------ *)
(* 0x81a00 li a0,-8; 0x81a04 slli a1,s11,0x38; 0x81a08/0c/10 sb a0,58(s7) / 62(s7) / 63(s7) (the frame's shadow
   bytes of `f` and `ef`, re-poisoned); 0x81a14 bltz a1 (taken exactly when t_fam_raw >= 128); on the taken side
   0x81a28 andi s2,s11,127; on the other side 0x81a18 ld a0,184(s1), 0x81a1c jal reac_box_family_of,
   0x81a20 mv s2,a0, 0x81a24 j 0x81a2c. *)

Lemma si_wvb_fds : forall (md : Model) mat, m_fds (with_vm_backing (m_vm_lazy md) mat md) = m_fds md.
Proof. intros md mat. destruct md as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity. Qed.
Lemma si_wvb_fs : forall (md : Model) mat, m_fs (with_vm_backing (m_vm_lazy md) mat md) = m_fs md.
Proof. intros md mat. destruct md as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity. Qed.

(* A byte of a byte array, as the reader sees it. *)
Lemma si_aview_garr8 : forall (W : world SEGS) mem a (l : list Z) (j : nat),
  garr8 SEGS (rd W mem) a l -> (j < length l)%nat ->
  aview SEGS (w_H W) mem (a + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W mem a l j Hg Hj. unfold aview. rewrite (garr8_mbyte SEGS _ a l j Hg Hj).
cbn [option_map]. f_equal. destruct (Hg j Hj) as (_ & Hr).
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hr.
Qed.

(* A four-byte little-endian field of a byte array whose three high bytes are zero. *)
Lemma si_vm4 : forall (W : world SEGS) mem a (l : list Z) (i : nat) v,
  garr8 SEGS (rd W mem) a l -> (i + 4 <= length l)%nat -> 0 <= v < 256 ->
  nth i l 0 = v -> nth (S i) l 0 = 0 -> nth (S (S i)) l 0 = 0 -> nth (S (S (S i))) l 0 = 0 ->
  val_mem SEGS (rd W mem) (a + Z.of_nat i) 4 v.
Proof.
intros W mem a l i v Hg Hi Hv H0 H1 H2 H3.
assert (Em : forall j, (j < length l)%nat -> mbyte SEGS (rd W mem) (a + Z.of_nat j) = Some (Z_to_bv 8 (nth j l 0)))
  by (intros j Hj; exact (garr8_mbyte SEGS _ a l j Hg Hj)).
assert (Hvp : 0 <= v < 2 ^ (8 * Z.of_nat 4)) by (cbn [Z.of_nat]; lia).
intros k Hk. rewrite (le_byte_small v 4 k Hvp Hk).
destruct k as [|[|[|[|k]]]]; [| | | | clear - Hk; cbn in Hk; lia].
- replace (a + Z.of_nat i + Z.of_nat 0) with (a + Z.of_nat i) by (cbn [Z.of_nat]; lia).
  rewrite (Em i ltac:(clear - Hi; lia)), H0. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- replace (a + Z.of_nat i + Z.of_nat 1) with (a + Z.of_nat (S i)) by (cbn [Z.of_nat]; lia).
  rewrite (Em (S i) ltac:(clear - Hi; lia)), H1. f_equal. f_equal.
  change (8 * Z.of_nat 1) with 8. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  symmetry. apply Z.div_small. exact Hv.
- replace (a + Z.of_nat i + Z.of_nat 2) with (a + Z.of_nat (S (S i))) by (cbn [Z.of_nat]; lia).
  rewrite (Em (S (S i)) ltac:(clear - Hi; lia)), H2. f_equal. f_equal.
  change (8 * Z.of_nat 2) with 16. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536.
  symmetry. apply Z.div_small. clear - Hv; lia.
- replace (a + Z.of_nat i + Z.of_nat 3) with (a + Z.of_nat (S (S (S i)))) by (cbn [Z.of_nat]; lia).
  rewrite (Em (S (S (S i))) ltac:(clear - Hi; lia)), H3. f_equal. f_equal.
  change (8 * Z.of_nat 3) with 24. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 24) with 16777216.
  symmetry. apply Z.div_small. clear - Hv; lia.
Qed.

(* The value of a symbolic register, from its unsigned reading. *)
Lemma si_den_of_U : forall E v z, U E v = z -> sv_denot E v = w64 z.
Proof. intros E v z H. unfold w64. rewrite <- H. unfold U. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

(* The signed branch, and the family test `bltz (t << 56)`. *)
Lemma si_branch_lt_S : forall E a b, branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (Sg E a <? Sg E b).
Proof. intros E a b. cbn [branch_taken]. unfold bv_lts, Sg. reflexivity. Qed.

Lemma si_swrap_sh : forall t, 0 <= t < 256 -> (bv_swrap 64 (t * 2 ^ 56) <? 0) = (128 <=? t).
Proof.
intros t Ht.
assert (EM : bv_modulus 64 = 2 ^ 64) by reflexivity.
assert (EH : bv_half_modulus 64 = 2 ^ 63) by reflexivity.
unfold bv_swrap, bv_wrap. rewrite EM, EH.
destruct (Z.leb_spec 128 t) as [Hh|Hl].
- replace (t * 2 ^ 56 + 2 ^ 63) with ((t * 2 ^ 56 + 2 ^ 63 - 2 ^ 64) + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. apply Z.ltb_lt. lia.
- rewrite Z.mod_small by lia. apply Z.ltb_ge. lia.
Qed.

Lemma si_bltz_shift : forall E (n : nat) t, ew E n = Z_to_bv 64 t -> 0 <= t < 256 ->
  branch_taken BC_LT (sv_denot E (SAlu ALU_SLL (SOff n 0) (SLit 56))) (sv_denot E (SLit 0)) = (128 <=? t).
Proof.
intros E n t H Ht.
rewrite si_branch_lt_S, S_SAlu, S_SLit, (U_atom E n t H ltac:(clear - Ht; lia)), U_SLit.
rewrite (zcanon_id 56) by (unfold M64; lia). cbn [zalu_raw].
change (Z.land 56 63) with 56. rewrite Z.shiftl_mul_pow2 by lia.
replace (bv_swrap 64 0) with 0 by reflexivity.
apply si_swrap_sh. exact Ht.
Qed.

Lemma si_and127 : forall E (n : nat) t, ew E n = Z_to_bv 64 t -> 0 <= t < 256 ->
  sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 127)) = w64 (Z.land t 127).
Proof.
intros E n t H Ht. apply si_den_of_U.
rewrite U_SAlu, (U_atom E n t H ltac:(clear - Ht; lia)), U_SLit.
rewrite (zcanon_id 127) by (unfold M64; lia). cbn [zalu_raw].
apply zcanon_id. unfold M64.
pose proof (Z.land_ones t 7 ltac:(lia)) as Eo. change (Z.ones 7) with 127 in Eo. change (2 ^ 7) with 128 in Eo.
rewrite Eo. pose proof (Z.mod_pos_bound t 128 ltac:(lia)). lia.
Qed.

(* The symbolic state at +0x128c. Region 0: the machine-frame word mf+184 (&id, atom 32), base s1 (atom 9),
   read-only. Region 1: the frame's shadow bytes 58..63 (base s7, atom 23), writable: the three stores at
   0x81a08..0x81a10 write bytes 58, 62 and 63. *)
Definition si_fam_mf : YP09.region :=
  YP09.mkRegion (Some 9%nat) 184 192 184 184 [YP09.mkChunk 184 (CVal 8 (SOff 32 0))].
Definition si_fam_sh : YP09.region := YP09.mkRegion (Some 23%nat) 58 64 58 64 [].
Definition si_fam_ss : sstate := mkSS 0x128c sr_atoms [si_fam_mf; si_fam_sh] None (mkFacts [] [] []).
Definition si_fam_E (regs : bvmap 5 word) (a : Z) : env := Eimg (Ereg regs [Z_to_bv 64 a]).

Lemma si_fam_entry : forall g pos mf ly2 S2 W2 regs2 mem2 md2 k,
  AJ g pos ly2 S2 W2 mem2 md2 k -> frames S2 = [(4, pos)] ->
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 ->
  getr regs2 9 = w64 mf -> sh_reg g pos regs2 ->
  val_mem SEGS (rd W2 mem2) (mf + 184) 8 (SFa g pos + V_id) ->
  st_ok_pi SEGS VAL (si_fam_E regs2 (SFa g pos + V_id)) si_fam_ss
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x128c)) mem2 (seg_rom SEGS))).
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 k HJ Hfrs Hmf R9 Rsh V184.
destruct (si_geo g pos mf ly2 S2 W2 mem2 md2 k HJ Hfrs Hmf)
  as (Hmf0 & H47 & Hal & Hstk & EFa & HSF0 & HSF1 & HSF64 & HSFapp).
pose proof asan_consts as (C1 & _).
assert (Has : ASTACK = 16384) by reflexivity.
assert (Esh : shadow_addr (SFa g pos) = SHADOW_OFF + SFa g pos / 8) by reflexivity.
assert (Hsh : 0 <= shadow_addr (SFa g pos) /\ shadow_addr (SFa g pos) + 128 <= alloc_ceiling)
  by (clear - Esh HSF0 HSF1 C1; unfold SHADOW_OFF in Esh; lia).
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
set (E := si_fam_E regs2 (SFa g pos + V_id)).
assert (E9 : ew E 9 = getr regs2 9) by exact (ew_Eimg_Ereg_nat regs2 _ 9 9%bv eq_refl).
assert (E23 : ew E 23 = getr regs2 23) by exact (ew_Eimg_Ereg_nat regs2 _ 23 23%bv eq_refl).
assert (E32 : ew E 32 = Z_to_bv 64 (SFa g pos + V_id))
  by (subst E; unfold si_fam_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (U9 : bv_unsigned (ew E 9) = mf)
  by (rewrite E9, R9; apply unsigned_lit_small; clear - Hmf0 H47 Hmf C1 Has; lia).
assert (U23 : bv_unsigned (ew E 23) = shadow_addr (SFa g pos))
  by (rewrite E23; unfold sh_reg in Rsh; rewrite Rsh; apply unsigned_lit_small; clear - Hsh C1; lia).
rewrite restrict_mkst_fx. unfold si_fam_ss. apply pa_entry_st_ok_full.
- subst E. unfold si_fam_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, si_fam_mf, si_fam_sh;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U9. split; [clear - Hmf0 C1 Has; lia|].
    split; [clear - Hmf0 H47 Hmf; lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ mf 184 8 (SOff 32 0) (SFa g pos + V_id));
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | clear - HSF0 HSF1 C1; unfold V_id; lia | lia | exact V184].
  + rewrite U23. split; [clear - Hsh; lia|]. split; [clear - Hsh C1; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS).
    apply (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
      [(4, pos)] ly2 S2 W2 mem2 md2 k (shadow_addr (SFa g pos) + o) HJ ltac:(
      right; right; right; exists 4, pos; split; [left; reflexivity|]; right;
      unfold in_zr; cbn [fst snd]; rewrite EFa, HFB; change (1024 / 8) with 128; clear - Ho; lia))).
- apply pairwise_disjoint_of_extents. unfold si_fam_mf, si_fam_sh, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U23.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  clear - Hmf0 Hsh Has C1. repeat split; lia.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [exact I | split; exact I].
Qed.

(* The cut at +0x12b8, from the pieces each path ends with. *)
Lemma si_fam_mk : forall g pos mf ly3 S3 (W3 : world SEGS) regs3 mem3 md3,
  AJ g pos ly3 S3 W3 mem3 md3 (4 * Z.of_nat (m_nrec g) + 4) ->
  frames S3 = [(4, pos)] ->
  0 <= 4 * Z.of_nat (m_nrec g) + 4 <= EV_LLVMF ->
  mo_le MT (e_S g) S3 ((4 * Z.of_nat (m_nrec g) + 4) * MEV MT) ->
  mo_ok MT S3 ((EV_LLVMF - (4 * Z.of_nat (m_nrec g) + 4)) * MEV MT) ->
  getr regs3 2 = w64 mf -> getr regs3 9 = w64 mf -> getr regs3 8 = w64 (e_sp0 g) ->
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
  getr regs3 3 = w64 (as_gp B) -> getr regs3 4 = w64 (as_tp B) ->
  si_vals g pos mf W3 mem3 -> EPRE g ->
  (forall fd, fd_lookup (m_fds md3) fd = fd_lookup (m_fds (e_md g)) fd) -> m_fs md3 = m_fs (e_md g) ->
  hblocks B g ly3 S3 [] -> sh_reg g pos regs3 ->
  getr regs3 18 = w64 (SlotModel.n_fam (e_pl g)) ->
  getr regs3 21 = w64 (SlotModel.t_cap_tok (e_pl g)) ->
  getr regs3 26 = w64 (SlotModel.t_cap_name (e_pl g)) ->
  getr regs3 22 = w64 (SlotModel.t_cap_disp (e_pl g)) ->
  val_mem SEGS (rd W3 mem3) (mf + 184) 8 (SFa g pos + V_id) ->
  si_C1 g pos mf W3 (cfg_at SEGS (BASE + 0x12b8) regs3 mem3 md3).
Proof.
intros g pos mf ly3 S3 W3 regs3 mem3 md3 HJ Hfrs Hk MLE MOK R2 R9 R8 Hmfb Hmf32 R3 R4 HV HPRE Hfds Hfs
  Hbl Rsh R18 R21 R26 R22 V184.
unfold si_C1, acut. exists ly3, S3, regs3, mem3, md3.
split; [reflexivity|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact MLE|]. split; [exact MOK|].
split; [exact (si_ecommon g pos mf ly3 S3 W3 regs3 mem3 md3 R2 R9 R8 Hmfb Hmf32 R3 R4 HV HPRE Hfds Hfs)|].
split; [exact HV|]. split; [exact Hbl|]. split; [exact Rsh|]. split; [exact R18|].
split; [exact R21|]. split; [exact R26|]. split; [exact R22 | exact V184].
Qed.

Lemma si_L_fam : forall g pos mf W2 c2, INV_H g pos mf W2 c2 -> SRr SEGS W2 c2 (si_C1 g pos mf).
Proof.
intros g pos mf W2 c2 Hst.
destruct Hst as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ0 & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HP as (Hid & Hbl & Rsh & Hmid3 & Hmid & Hef & R27 & R21 & R26 & R22 & V176 & V160 & V120 & V112).
pose proof HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
  Z9 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27 & Vflag & HPRE & Hfds & Hfs & Hinb).
(* ---- geometry ---- *)
destruct (si_geo g pos mf ly2 S2 W2 mem2 md2 _ HJ0 Hfrs Hmfb)
  as (Hmf0 & H47 & Hsp0al & Hstk & EFa & HSF0 & HSF1 & HSF64 & HSFapp).
pose proof asan_consts as (C1 & _).
assert (Has : ASTACK = 16384) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hstk1 : reac_box_family_of.REAC_BOX_FAMILY_OF_STK = 8256) by reflexivity.
assert (HSTK' : STK_LLVMF <= LLVMF_STK) by exact HSTK.
unfold STK_LLVMF in HSTK'.
assert (Esh : shadow_addr (SFa g pos) = SHADOW_OFF + SFa g pos / 8) by reflexivity.
assert (Hsh : 0 <= shadow_addr (SFa g pos) /\ shadow_addr (SFa g pos) + 128 <= alloc_ceiling)
  by (clear - Esh HSF0 HSF1 C1; unfold SHADOW_OFF in Esh; lia).
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
assert (HSF8 : SFa g pos mod 8 = 0) by (clear - HSF64; Z.div_mod_to_equations; lia).
assert (Hlen : e_n g = Z.of_nat (length (e_pl g)))
  by (destruct HPRE as (_ & _ & _ & _ & _ & Hl & _); exact Hl).
assert (Hmf320 : mf + 320 <= e_sp0 g) by (clear - Hmfb; lia).
assert (Hmfr : 0 <= mf /\ mf <= 2 ^ 47 /\ 0 <= e_sp0 g <= 2 ^ 47)
  by (clear - Hmf0 H47 Hmfb C1 Has; lia).
(* ---- the zones the segment carries: their range, and that they are not the bytes it writes ---- *)
assert (HIN : 0 < e_n g -> In (e_p g, e_n g) (ablocks B ly2 S2)).
{ intros Hn0. destruct HPRE as (_ & _ & _ & _ & Hinp0 & _).
  destruct Hinp0 as [(Hn & _) | (_ & Hine)]; [clear - Hn Hn0; lia|].
  destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). cbn [app]. exact Hine. }
assert (HARG : forall a, si_area g pos mf a -> 0 <= a < 2 ^ 64 /\ (a + 16384 <= mf \/ mf <= a)).
{ intros a Ha. unfold si_area in Ha. destruct Ha as [Hs | [Hf | [Hs2 | Hi]]].
  - clear - Hs Hmf0 H47 Hmfb C1 Has. split; [lia | right; lia].
  - clear - Hf HSF0 HSF1 C1 Hmf0 Has. split; [lia | left; lia].
  - clear - Hs2 Hsh C1 Hmf0 Has. split; [lia | left; lia].
  - assert (Hn0 : 0 < e_n g) by (clear - Hi; lia).
    destruct (al_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 (e_p g) (e_n g) (proj1 HJ0) (HIN Hn0))
      as (_ & Hp4096 & Hpce & _).
    pose proof (req_size_pos (e_n g) ltac:(clear - Hn0; lia)) as (Hr1 & Hr2).
    clear - Hi Hp4096 Hpce Hr2 C1 Hmf0 Has. split; [lia | left; lia]. }
assert (HAP : forall a, si_area g pos mf a ->
  ~ (shadow_addr (SFa g pos) + 58 <= a < shadow_addr (SFa g pos) + 64)).
{ intros a Ha Hw. unfold si_area in Ha. destruct Ha as [Hs | [Hf | [Hs2 | Hi]]].
  - clear - Hs Hw Hmf0 Hsh Has C1. lia.
  - apply (fshadow_not_app (SFa g pos) 128 (SFa g pos) 1024 a);
    [clear - HSF0; lia | clear - HSF1 C1; lia | exact HSFapp
    | clear - Hw Esh; unfold SHADOW_OFF in Esh; lia | clear - Hf; lia].
  - clear - Hs2 Hw. lia.
  - assert (Hn0 : 0 < e_n g) by (clear - Hi; lia).
    destruct (al_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 (e_p g) (e_n g) (proj1 HJ0) (HIN Hn0))
      as (_ & Hp4096 & Hpce & Hpapp & _).
    pose proof (req_size_pos (e_n g) ltac:(clear - Hn0; lia)) as (Hr1 & Hr2).
    apply (fshadow_not_app (SFa g pos) 128 (e_p g) (req_size (e_n g)) a);
    [clear - HSF0; lia | clear - HSF1 C1; lia | exact Hpapp
    | clear - Hw Esh; unfold SHADOW_OFF in Esh; lia | clear - Hi Hr2; lia]. }
assert (HV0 : si_vals g pos mf W2 mem2)
  by exact (si_vals_of_ecommon g pos mf ly2 S2 W2 regs2 mem2 md2 HC Hid V112 V120 Hmid3 V160 V176).
(* ---- the symbolic state at the cut ---- *)
pose proof (si_fam_entry g pos mf ly2 S2 W2 regs2 mem2 md2 _ HJ0 Hfrs Hmfb Rs1 Rsh Hmid) as HS.
set (E := si_fam_E regs2 (SFa g pos + V_id)) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold si_fam_E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs2 [Z_to_bv 64 (SFa g pos + V_id)]) E)
  by (subst E; unfold si_fam_E; split;
      [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (ELr : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; subst E; unfold si_fam_E; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (ELr 2%nat 2%bv eq_refl) as E2.
pose proof (ELr 3%nat 3%bv eq_refl) as E3.
pose proof (ELr 4%nat 4%bv eq_refl) as E4.
pose proof (ELr 8%nat 8%bv eq_refl) as E8.
pose proof (ELr 9%nat 9%bv eq_refl) as E9.
pose proof (ELr 23%nat 23%bv eq_refl) as E23.
pose proof (ELr 27%nat 27%bv eq_refl) as E27a.
assert (E32 : ew E 32 = Z_to_bv 64 (SFa g pos + V_id))
  by (subst E; unfold si_fam_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (U9 : bv_unsigned (ew E 9) = mf)
  by (rewrite E9, Rs1; apply unsigned_lit_small; clear - Hmfr; lia).
assert (U23 : bv_unsigned (ew E 23) = shadow_addr (SFa g pos))
  by (rewrite E23; unfold sh_reg in Rsh; rewrite Rsh; apply unsigned_lit_small; clear - Hsh C1; lia).
assert (E27 : ew E 27 = Z_to_bv 64 (SlotModel.t_fam_raw (e_pl g))) by (rewrite E27a; exact R27).
assert (Htr : 0 <= SlotModel.t_fam_raw (e_pl g) < 256)
  by (unfold SlotModel.t_fam_raw; apply SlotModel.inb_range).
unfold cfg_at. change (w64 (BASE + 0x128c)) with (Z_to_bv 64 (BASE + 0x128c)).
(* ---- run 1: the three shadow stores, up to the family branch ---- *)
paj_run_sh si_RUNP HS HJ0.
{ apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo si_fam_mf]; lia|].
  intros a (r & Hin & Ha). destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi si_fam_sh base_val] in Ha. rewrite U23 in Ha.
  right; right; right. exists 4, pos. split; [left; reflexivity|]. right.
  unfold in_zr. cbn [fst snd]. rewrite EFa, HFB. change (1024 / 8) with 128. clear - Ha. lia. }
rename ms into ms1. rename HFr into HFr1. rename HJ0 into HJ1. clear HF HG.
assert (KP1 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (shadow_addr (SFa g pos) + 58 <= a < shadow_addr (SFa g pos) + 64) ->
  aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W2) mem2 a).
{ apply (kept_of_frame E (ss_mem si_fam_ss) (w_H W2) mem2 (ms_mem ms1)
          (fun x => shadow_addr (SFa g pos) + 58 <= x < shadow_addr (SFa g pos) + 64) HFr1).
  intros bb wlo whi aa Hin Hr. unfold si_fam_ss in Hin.
  cbn [ss_mem windows map si_fam_mf si_fam_sh YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
  destruct Hin as [Eq | [Eq | []]]; injection Eq as <- <- <-; cbn [base_val] in Hr.
  - rewrite U9 in Hr. clear - Hr. lia.
  - rewrite U23 in Hr. exact Hr. }
assert (HV1 : si_vals g pos mf W2 (ms_mem ms1)).
{ apply (si_vals_moved g pos mf W2 mem2 W2 (ms_mem ms1) Hmf320 HSF8 Hlen); [|exact HV0].
  intros a Ha. exact (KP1 a (proj1 (HARG a Ha)) (HAP a Ha)). }
assert (V1841 : val_mem SEGS (rd W2 (ms_mem ms1)) (mf + 184) 8 (SFa g pos + V_id)).
{ apply (val_mem_kept SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms1)); [|exact Hmid].
  intros j Hj. apply KP1; clear - Hj Hmfr Hsh Hmf0 Has C1; lia. }
(* ---- the family branch ---- *)
psrr_branch_pi si_RUNP si_BR HS.
- (* taken: t_fam_raw >= 128, s2 = t_fam_raw & 127 *)
  rewrite (si_bltz_shift E 27 (SlotModel.t_fam_raw (e_pl g)) E27 Htr) in Hc.
  apply Z.leb_le in Hc.
  paj_run_to_sh si_RUNTOP HS HJ1 0x12b8.
  { apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia|].
    intros a (r & Hin & Ha). destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U23 in Ha.
    right; right; right. exists 4, pos. split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite EFa, HFB. change (1024 / 8) with 128. clear - Ha. lia. }
  rename ms into ms2. rename HFr into HFr2. rename HJ1 into HJ2. clear HF HG.
  assert (KP2 : forall a, 0 <= a < 2 ^ 64 ->
    ~ (shadow_addr (SFa g pos) + 58 <= a < shadow_addr (SFa g pos) + 64) ->
    aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) (ms_mem ms1) a).
  { apply (kept_of_frame E _ (w_H W2) (ms_mem ms1) (ms_mem ms2)
            (fun x => shadow_addr (SFa g pos) + 58 <= x < shadow_addr (SFa g pos) + 64) HFr2).
    intros bb wlo whi aa Hin Hr.
    cbn [windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
    destruct Hin as [Eq | [Eq | []]]; injection Eq as <- <- <-; cbn [base_val] in Hr.
    - rewrite U9 in Hr. clear - Hr. lia.
    - rewrite U23 in Hr. exact Hr. }
  assert (HV2 : si_vals g pos mf W2 (ms_mem ms2)).
  { apply (si_vals_moved g pos mf W2 (ms_mem ms1) W2 (ms_mem ms2) Hmf320 HSF8 Hlen); [|exact HV1].
    intros a Ha. exact (KP2 a (proj1 (HARG a Ha)) (HAP a Ha)). }
  assert (V1842 : val_mem SEGS (rd W2 (ms_mem ms2)) (mf + 184) 8 (SFa g pos + V_id)).
  { apply (val_mem_kept SEGS (w_H W2) (w_H W2) (ms_mem ms1) (ms_mem ms2)); [|exact V1841].
    intros j Hj. apply KP2; clear - Hj Hmfr Hsh Hmf0 Has C1; lia. }
  assert (RK : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 21%bv; 22%bv; 23%bv; 26%bv] ->
    getr (ms_regs ms2) r = getr regs2 r)
    by (apply (regs_kept_of_st_ok_pi E _ _ regs2 [Z_to_bv 64 (SFa g pos + V_id)] _ HS HAE);
        vm_compute; reflexivity).
  assert (R18 : getr (ms_regs ms2) 18 = w64 (SlotModel.n_fam (e_pl g))).
  { lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
      pose proof (st_ok_pi_restrict_reg (w_H W2) E ssx msx (18%bv : bv 5) HS) as R18a;
      let e := eval vm_compute in (sr_get (ss_regs ssx) (18%bv : bv 5)) in
      change (sr_get (ss_regs ssx) (18%bv : bv 5)) with e in R18a end.
    cbn [ms_regs restrict] in R18a.
    rewrite (si_and127 E 27 (SlotModel.t_fam_raw (e_pl g)) E27 Htr) in R18a.
    rewrite <- (SIM.si_nfam_hi (e_pl g) Hc) in R18a. exact R18a. }
  pmkst HS. apply SRr_ret.
  refine (si_fam_mk g pos mf _ _ _ (ms_regs ms2) (ms_mem ms2) _ HJ2 Hfrs Hk MLE MOK
    _ _ _ Hmfb Hmf32 _ _ HV2 HPRE _ _ Hbl _ R18 _ _ _ V1842).
  + rewrite (RK 2%bv ltac:(cbn [In]; tauto)). exact Rsp.
  + rewrite (RK 9%bv ltac:(cbn [In]; tauto)). exact Rs1.
  + rewrite (RK 8%bv ltac:(cbn [In]; tauto)). exact Rs0.
  + rewrite (RK 3%bv ltac:(cbn [In]; tauto)). exact Rgp.
  + rewrite (RK 4%bv ltac:(cbn [In]; tauto)). exact Rtp.
  + intros fd. rewrite si_wvb_fds, si_wvb_fds. exact (Hfds fd).
  + rewrite si_wvb_fs, si_wvb_fs. exact Hfs.
  + unfold sh_reg. rewrite (RK 23%bv ltac:(cbn [In]; tauto)). exact Rsh.
  + rewrite (RK 21%bv ltac:(cbn [In]; tauto)). exact R21.
  + rewrite (RK 26%bv ltac:(cbn [In]; tauto)). exact R26.
  + rewrite (RK 22%bv ltac:(cbn [In]; tauto)). exact R22.
- (* not taken: t_fam_raw < 128, the call to reac_box_family_of *)
  rewrite (si_bltz_shift E 27 (SlotModel.t_fam_raw (e_pl g)) E27 Htr) in Hc.
  apply Z.leb_gt in Hc.
  paj_run_shc si_RUNP si_RUNC HS HJ1.
  { apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia|].
    intros a (r & Hin & Ha). destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U23 in Ha.
    right; right; right. exists 4, pos. split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite EFa, HFB. change (1024 / 8) with 128. clear - Ha. lia. }
  rename ms into msc. rename HFr into HFrc. rename HJ1 into HJc0. clear HF HG.
  assert (KPc : forall a, 0 <= a < 2 ^ 64 ->
    ~ (shadow_addr (SFa g pos) + 58 <= a < shadow_addr (SFa g pos) + 64) ->
    aview SEGS (w_H W2) (ms_mem msc) a = aview SEGS (w_H W2) (ms_mem ms1) a).
  { apply (kept_of_frame E _ (w_H W2) (ms_mem ms1) (ms_mem msc)
            (fun x => shadow_addr (SFa g pos) + 58 <= x < shadow_addr (SFa g pos) + 64) HFrc).
    intros bb wlo whi aa Hin Hr.
    cbn [windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
    destruct Hin as [Eq | [Eq | []]]; injection Eq as <- <- <-; cbn [base_val] in Hr.
    - rewrite U9 in Hr. clear - Hr. lia.
    - rewrite U23 in Hr. exact Hr. }
  assert (HVc : si_vals g pos mf W2 (ms_mem msc)).
  { apply (si_vals_moved g pos mf W2 (ms_mem ms1) W2 (ms_mem msc) Hmf320 HSF8 Hlen); [|exact HV1].
    intros a Ha. exact (KPc a (proj1 (HARG a Ha)) (HAP a Ha)). }
  assert (V184c : val_mem SEGS (rd W2 (ms_mem msc)) (mf + 184) 8 (SFa g pos + V_id)).
  { apply (val_mem_kept SEGS (w_H W2) (w_H W2) (ms_mem ms1) (ms_mem msc)); [|exact V1841].
    intros j Hj. apply KPc; clear - Hj Hmfr Hsh Hmf0 Has C1; lia. }
  prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp2. prreg HS (3%bv : bv 5) Rgp2.
  prreg HS (4%bv : bv 5) Rtp2. prreg HS (8%bv : bv 5) Rs02. prreg HS (10%bv : bv 5) Ra0.
  rewrite E32 in Ra0.
  assert (Hpr : 0 <= SFa g pos + V_id < 2 ^ 64) by (clear - HSF0 HSF1 C1; unfold V_id; lia).
  assert (Usp2 : spZ (ms_regs msc) = mf)
    by (unfold spZ; rewrite Rsp2, E2, Rsp; apply unsigned_lit_small; clear - Hmfr; lia).
  assert (Us02 : s0Z (ms_regs msc) = e_sp0 g)
    by (unfold s0Z; rewrite Rs02, E8, Rs0; apply unsigned_lit_small; clear - Hmfr Hmfb; lia).
  (* the read-only image at the call state, and the family table *)
  assert (HROP : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) (ms_mem msc))).
  { apply (IdentBase.arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B LLVMF_STK (e_sp0 g) []
      (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 (ms_mem msc) _ _ HJc0).
    destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROD & _). apply HRO. exact HROD. }
  pose proof (HIMG W2 (ms_mem msc) HROP) as HIM.
  destruct HIM as (_ & _ & _ & _ & HTBL & _).
  assert (HL36 : length HW_ROWS = 36%nat) by reflexivity.
  assert (Hrows : forall j, (j < 36)%nat ->
    aview SEGS (w_H W2) (ms_mem msc) (reac_box_family_of.FAMOF_HWF + Z.of_nat j) = Some (nth j SIM.si_HW_ROWS 0)).
  { intros j Hj. unfold reac_box_family_of.FAMOF_HWF.
    rewrite (si_aview_garr8 W2 (ms_mem msc) (VAL (A_OBJ 17)) HW_ROWS j HTBL ltac:(clear - Hj HL36; lia)).
    reflexivity. }
  assert (Vf0 : val_mem SEGS (rd W2 (ms_mem msc)) (VAL (A_OBJ 17)) 4 1).
  { pose proof (si_vm4 W2 (ms_mem msc) (VAL (A_OBJ 17)) HW_ROWS 0 1 HTBL ltac:(clear - HL36; lia)
      ltac:(lia) eq_refl eq_refl eq_refl eq_refl) as Hx.
    change (Z.of_nat 0) with 0 in Hx. rewrite Z.add_0_r in Hx. exact Hx. }
  assert (Vf1 : val_mem SEGS (rd W2 (ms_mem msc)) (VAL (A_OBJ 17) + 12) 4 2).
  { pose proof (si_vm4 W2 (ms_mem msc) (VAL (A_OBJ 17)) HW_ROWS 12 2 HTBL ltac:(clear - HL36; lia)
      ltac:(lia) eq_refl eq_refl eq_refl eq_refl) as Hx.
    change (Z.of_nat 12) with 12 in Hx. exact Hx. }
  assert (Vf2 : val_mem SEGS (rd W2 (ms_mem msc)) (VAL (A_OBJ 17) + 24) 4 3).
  { pose proof (si_vm4 W2 (ms_mem msc) (VAL (A_OBJ 17)) HW_ROWS 24 3 HTBL ltac:(clear - HL36; lia)
      ltac:(lia) eq_refl eq_refl eq_refl eq_refl) as Hx.
    change (Z.of_nat 24) with 24 in Hx. exact Hx. }
  assert (HTB : reac_box_family_of.famof_tbl W2 (ms_mem msc) 1 2 3).
  { unfold reac_box_family_of.famof_tbl, reac_box_family_of.FAMOF_HWF. split.
    - intros a Ha.
      replace a with (VAL (A_OBJ 17) + Z.of_nat (Z.to_nat (a - VAL (A_OBJ 17)))) by (clear - Ha; lia).
      rewrite (si_aview_garr8 W2 (ms_mem msc) (VAL (A_OBJ 17)) HW_ROWS
        (Z.to_nat (a - VAL (A_OBJ 17))) HTBL ltac:(clear - Ha HL36; lia)). discriminate.
    - split; [clear; lia|]. split; [exact Vf0|]. split; [clear; lia|]. split; [exact Vf1|].
      split; [clear; lia | exact Vf2]. }
  (* the identity struct is a frame object the callee may read *)
  pose proof HVc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hidc & _).
  assert (HBOX : SFa g pos + V_id <> 0 ->
    reac_box_family_of.famof_box B ly2 S2 W2 (ms_mem msc) (SFa g pos + V_id)).
  { intros _. right. unfold afobj. split.
    - exists 4, pos. split; [rewrite Hfrs; left; reflexivity|]. split; [clear; lia|].
      rewrite EFa, HFB. split; [clear - HSF64; Z.div_mod_to_equations; lia|].
      split; [unfold V_id; clear; lia | unfold V_id, N_id; clear; lia].
    - split; [unfold V_id; clear - HSF64; Z.div_mod_to_equations; lia|].
      exact (si_ra_sub W2 (ms_mem msc) (SFa g pos + V_id) N_id (SFa g pos + V_id) 38
               (proj2 (proj2 Hidc)) ltac:(unfold N_id; lia) ltac:(lia) ltac:(lia)
               ltac:(unfold N_id; lia)). }
  pmkst HS. rewrite (PSIG IB_reac_box_family_of AF_reac_box_family_of eq_refl).
  eapply SRr_bind.
  { eapply (si_call g pos W2 (ms_regs msc) (ms_mem msc) _ ly2 S2 _ (4 * Z.of_nat (m_nrec g) + 4)
      reac_box_family_of.REAC_BOX_FAMILY_OF_STK [] 0 (mf - e_sp0 g) (Z_to_bv 64 (BASE + 4780))
      (fun ly3 S3 W3 regs3 mem3 md3 =>
         ly3 = ly2 /\ S3 = S2 /\ W3 = W2 /\
         (forall a, 0 <= a < 2 ^ 64 ->
            ~ (spZ (ms_regs msc) - reac_box_family_of.REAC_BOX_FAMILY_OF_STK <= a < spZ (ms_regs msc)) ->
            aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) (ms_mem msc) a) /\
         (exists r, reac_box_family_of.famof_res (aview SEGS (w_H W2) (ms_mem msc)) (SFa g pos + V_id)
            reac_box_family_of.FAMOF_HWF 1 2 3 r /\
            getr regs3 10 = Z_to_bv 64 (reac_box_family_of.famof_sx32 r))));
    try exact HJc0; try exact HPRE.
    - rewrite Usp2. clear. lia.
    - clear - Hmf32 Hsp0al. Z.div_mod_to_equations. lia.
    - clear - Hmfb. lia.
    - clear - Hstk1. lia.
    - clear - Hstk1 Hmfb HSTK' Has. lia.
    - rewrite Rgp2, E3. exact Rgp.
    - rewrite Rtp2, E4. exact Rtp.
    - exact Rra.
    - apply ret_ok_codeptr_v; [clear; lia | reflexivity].
    - pose proof pa_B_ok as (HB0 & HB1 & _).
      rewrite unsigned_lit_small by (clear - HB0 HB1; lia). clear - HB0. lia.
    - exact Us02.
    - pose proof HVc as (_ & _ & _ & _ & Vrac & _). exact Vrac.
    - pose proof HVc as (_ & _ & _ & _ & _ & Vs0c & _). exact Vs0c.
    - intros ch1 Hch1 HPRE1.
      eapply SRr_mono.
      { unfold cfg_at, reac_box_family_of.A_reac_box_family_ofP in HFAM.
        exact (HFAM ly2 S2 W2 (ms_regs msc) (ms_mem msc) _ ch1 (SFa g pos + V_id) 1 2 3 HPRE1
                 Ra0 Hpr HBOX HTB). }
      cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & Ec & HJc & HP3 & HK3).
      exists ly3, S3, regs3, mem3, md3. rewrite Rra in Ec.
      split; [exact Ec|]. split; [exact HJc|]. split; [exact HP3 | exact HK3].
    - intros a (r & [] & _). }
  cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc & HP3 & HK3).
  destruct HK3 as (-> & -> & EW3 & EW & (r & Hres & Ra03)).
  rewrite Z.add_0_r in HJ3.
  rewrite EW3 in *.
  (* the memory the segment carries survives the call *)
  assert (KPC : forall a, 0 <= a < 2 ^ 64 -> (a + 16384 <= mf \/ mf <= a) ->
    aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) (ms_mem msc) a).
  { intros a Ha Hd. apply (EW a Ha). rewrite Usp2, Hstk1. clear - Hd. lia. }
  assert (HV3 : si_vals g pos mf W2 mem3).
  { apply (si_vals_moved g pos mf W2 (ms_mem msc) W2 mem3 Hmf320 HSF8 Hlen); [|exact HVc].
    intros a Ha. destruct (HARG a Ha) as (Hr1 & Hr2). exact (KPC a Hr1 Hr2). }
  assert (V1843 : val_mem SEGS (rd W2 mem3) (mf + 184) 8 (SFa g pos + V_id)).
  { apply (val_mem_kept SEGS (w_H W2) (w_H W2) (ms_mem msc) mem3); [|exact V184c].
    intros j Hj. apply KPC; clear - Hj Hmfr; lia. }
  (* the result: the plain model's family *)
  assert (Hidb : length (m_id g (m_nrec g)) = 38%nat) by apply SlotModel.rec_id_length.
  assert (Hbytes : forall j, (j < 38)%nat ->
    aview SEGS (w_H W2) (ms_mem msc) (SFa g pos + V_id + Z.of_nat j) =
    Some (RcIdentModel.bz (nth j (m_id g (m_nrec g)) (RcIdentModel.zb 0)))).
  { intros j Hj. destruct Hidc as (Hg & _ & _). unfold bytes_at8 in Hg.
    rewrite (si_aview_garr8 W2 (ms_mem msc) (SFa g pos + V_id) _ j Hg
      ltac:(rewrite length_map, Hidb; exact Hj)).
    f_equal. unfold RcIdentModel.bz.
    rewrite <- (map_nth (fun b : byte => bv_unsigned b) (m_id g (m_nrec g)) (RcIdentModel.zb 0) j).
    reflexivity. }
  assert (Hfam : r = SlotModel.FAM (m_id g (m_nrec g))).
  { apply (SIM.si_famof (aview SEGS (w_H W2) (ms_mem msc)) (SFa g pos + V_id)
      reac_box_family_of.FAMOF_HWF (m_id g (m_nrec g)) r Hidb
      ltac:(clear - HSF0 C1; unfold V_id; lia) Hbytes Hrows Hres). }
  assert (Hrng : 0 <= r <= 3) by (rewrite Hfam; apply SIM.si_FAM_range).
  assert (Hsx : reac_box_family_of.famof_sx32 r = r)
    by (unfold reac_box_family_of.famof_sx32; destruct (Z.ltb_spec r (2 ^ 31)) as [Hlt|Hge];
        [reflexivity | clear - Hrng Hge; lia]).
  assert (Eid : m_id g (m_nrec g) = SlotModel.idT (e_pl g)) by reflexivity.
  rewrite Hsx, Hfam, Eid, <- (SIM.si_nfam_lo (e_pl g) Hc) in Ra03.
  (* back at +0x12ac: rebuild the symbolic state with no region and run to the join *)
  jafter_call_keep_hi HS 512%nat regs3 (mrestrict (w_H W2) mem3) HP3 (@nil nat) HS2.
  specialize (HS2 (Forall_nil _)).
  rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
  pose proof (img_env_havoc_hi E 512%nat (map (getr regs3) CLOB) HEI ltac:(cbv; lia)) as HEI2.
  assert (HAE2 : env_agree 32 (Ereg regs2 [Z_to_bv 64 (SFa g pos + V_id)])
                   (havoc E 512 (map (getr regs3) CLOB)))
    by (destruct HAE as [HA HD]; split;
        [intros n Hn; rewrite ew_havoc_old by (cbv; lia); apply HA; exact Hn | exact HD]).
  paj_run_to_sh si_RUNTOP HS HJ3 0x12b8.
  { apply awr_ok_nil. }
  rename ms into msf. rename HFr into HFrf. rename HJ3 into HJf. clear HF HG.
  assert (KPF : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem msf) a = aview SEGS (w_H W2) mem3 a).
  { intros a Ha.
    apply (kept_of_frame (havoc E 512 (map (getr regs3) CLOB)) (@nil YP09.region) (w_H W2) mem3 (ms_mem msf)
            (fun _ : Z => False) HFrf); [| exact Ha | intros []].
    intros bb wlo whi aa Hin Hr. cbn [windows map] in Hin. destruct Hin. }
  assert (HVf : si_vals g pos mf W2 (ms_mem msf)).
  { apply (si_vals_moved g pos mf W2 mem3 W2 (ms_mem msf) Hmf320 HSF8 Hlen); [|exact HV3].
    intros a Ha. exact (KPF a (proj1 (HARG a Ha))). }
  assert (V184f : val_mem SEGS (rd W2 (ms_mem msf)) (mf + 184) 8 (SFa g pos + V_id)).
  { apply (val_mem_kept SEGS (w_H W2) (w_H W2) mem3 (ms_mem msf)); [|exact V1843].
    intros j Hj. apply KPF. clear - Hj Hmfr. lia. }
  assert (RKf : forall q, In q [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 21%bv; 22%bv; 23%bv; 26%bv] ->
    getr (ms_regs msf) q = getr regs2 q)
    by (apply (regs_kept_of_st_ok_pi (havoc E 512 (map (getr regs3) CLOB)) _ _ regs2
                 [Z_to_bv 64 (SFa g pos + V_id)] _ HS HAE2); vm_compute; reflexivity).
  assert (E516 : ew (havoc E 512 (map (getr regs3) CLOB)) 516 = getr regs3 10%bv)
    by exact (ew_havoc_new E 512 (map (getr regs3) CLOB) 4 (Z_to_bv 64 0) ltac:(cbv; lia)).
  assert (R18f : getr (ms_regs msf) 18 = w64 (SlotModel.n_fam (e_pl g))).
  { lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
      pose proof (st_ok_pi_restrict_reg (w_H W2) (havoc E 512 (map (getr regs3) CLOB)) ssx msx
        (18%bv : bv 5) HS) as R18a;
      let e := eval vm_compute in (sr_get (ss_regs ssx) (18%bv : bv 5)) in
      change (sr_get (ss_regs ssx) (18%bv : bv 5)) with e in R18a end.
    cbn [ms_regs restrict sv_denot] in R18a. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in R18a.
    rewrite E516, Ra03 in R18a. exact R18a. }
  destruct (AJ_NIL_IO reac_box_family_of.REAC_BOX_FAMILY_OF_STK (e_sp0 g + (mf - e_sp0 g)) ly2 S2 W2
    (ms_mem msc) _ [] ly2 S2 W2 mem3 md3 0 HJc) as (Efds & Efs).
  pmkst HS. apply SRr_ret.
  refine (si_fam_mk g pos mf _ _ _ (ms_regs msf) (ms_mem msf) _ HJf Hfrs Hk MLE MOK
    _ _ _ Hmfb Hmf32 _ _ HVf HPRE _ _ Hbl _ R18f _ _ _ V184f).
  + rewrite (RKf 2%bv ltac:(cbn [In]; tauto)). exact Rsp.
  + rewrite (RKf 9%bv ltac:(cbn [In]; tauto)). exact Rs1.
  + rewrite (RKf 8%bv ltac:(cbn [In]; tauto)). exact Rs0.
  + rewrite (RKf 3%bv ltac:(cbn [In]; tauto)). exact Rgp.
  + rewrite (RKf 4%bv ltac:(cbn [In]; tauto)). exact Rtp.
  + intros fd. rewrite si_wvb_fds, Efds, si_wvb_fds. exact (Hfds fd).
  + rewrite si_wvb_fs, Efs, si_wvb_fs. exact Hfs.
  + unfold sh_reg. rewrite (RKf 23%bv ltac:(cbn [In]; tauto)). exact Rsh.
  + rewrite (RKf 21%bv ltac:(cbn [In]; tauto)). exact R21.
  + rewrite (RKf 26%bv ltac:(cbn [In]; tauto)). exact R26.
  + rewrite (RKf 22%bv ltac:(cbn [In]; tauto)). exact R22.
Qed.

Check (si_L_fam : forall g pos mf W2 c2, INV_H g pos mf W2 c2 -> SRr SEGS W2 c2 (si_C1 g pos mf)).

(* A block x of the run that the permutation lists beside the entry's blocks l is not one of l: two copies of one
   block would overlap. *)
Lemma si_rl_notin : forall ly2 S2 W2 mem2 md2 (x : Z * Z) rest l,
  AR SEGS B ly2 S2 W2 mem2 md2 -> Permutation (ablocks B ly2 S2) (x :: rest ++ l) -> 0 <= snd x -> ~ In x l.
Proof.
intros ly2 S2 W2 mem2 md2 x rest l HAR Hp Hs Hl.
apply in_split in Hl as (l1 & l2 & ->).
assert (P : Permutation (ablocks B ly2 S2) (x :: x :: rest ++ l1 ++ l2)).
{ eapply Permutation_trans; [exact Hp|]. apply perm_skip.
  rewrite (app_assoc rest l1 (x :: l2)), (app_assoc rest l1 l2). apply Permutation_sym, Permutation_middle. }
pose proof (sep_blocks_perm SEGS B LAWS _ _ _ _ _ x x _ HAR P) as Hd.
destruct x as [p n]. unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd, Hs.
unfold req_size in Hd. destruct (Z.eqb_spec n 0); lia.
Qed.

(* The model's materialisation and a call whose write tokens are closed keep the fd table and the file system. *)
Lemma si_rl_wvb : forall (md : Model) mat,
  m_fds (with_vm_backing (m_vm_lazy md) mat md) = m_fds md /\ m_fs (with_vm_backing (m_vm_lazy md) mat md) = m_fs md.
Proof. intros md mat. destruct md as [f [mp lz mt] io fs pr li ti]; split; reflexivity. Qed.
Lemma si_rl_sameio : forall md md', same_io md md' -> m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof. intros md md' (E1 & _ & E3 & _). unfold m_fds, m_fs. rewrite E1, E3. split; reflexivity. Qed.

(* The symbolic state at +0x1348. Region 0: the seven machine-frame words the step loads, base s1 (atom 9):
   mf+128 = cap_tok (atom 32), mf+144 = cap_name (33), mf+152 = nm (34), mf+160 = t_out (35), mf+168 = the shadow
   offset (38, loaded after the call), mf+176 = t_in (36), mf+184 = dp (37); read-only. Region 1: the two
   stack-argument words below mf, base sp (atom 2), writable. *)
Definition si_rl_mf : YP09.region := YP09.mkRegion (Some 9%nat) 128 192 128 128
  [YP09.mkChunk 128 (CVal 8 (SOff 32 0)); YP09.mkChunk 144 (CVal 8 (SOff 33 0));
   YP09.mkChunk 152 (CVal 8 (SOff 34 0)); YP09.mkChunk 160 (CVal 8 (SOff 35 0));
   YP09.mkChunk 168 (CVal 8 (SOff 38 0)); YP09.mkChunk 176 (CVal 8 (SOff 36 0));
   YP09.mkChunk 184 (CVal 8 (SOff 37 0))].
Definition si_rl_stk : YP09.region := YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [].
Definition si_rl_ss : sstate := mkSS 0x1348 sr_atoms [si_rl_mf; si_rl_stk] None (mkFacts [] [] []).

Lemma si_L_real : forall g pos mf nm tk dp W2 c2, si_C4 g pos mf nm tk dp W2 c2 ->
  SRr SEGS W2 c2 (INV_I g pos mf nm tk dp).
Proof.
intros g pos mf nm tk dp W2 c2 Hstart.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HP as (HV & Hshr & Hblk & R18 & R19 & R20 & R21 & R22 & R27 & V184 & V152 & V144 & V128).
pose proof HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & _ & _ & _ & V168 & Vra & Vs0 &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRE & Hfds & Hfs & _).
unfold sh_reg in Hshr.
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (Has : ASTACK = 16384) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
destruct (si_geo g pos mf ly2 S2 W2 mem2 md2 _ HJ Hfrs Hmfb)
  as (Hmf0 & H47 & Hsp0al & Hceil & EFa & HSF0 & HSF1 & HSF64 & HSFapp).
rewrite Has in Hmf0, HSTK'.
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & _).
pose proof HPRE as (HFN & _ & _ & _ & Hinp0 & Hlen & _ & _ & Hnev0 & _ & Haro & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (Esh : shadow_addr (SFa g pos) = SHADOW_OFF + SFa g pos / 8) by reflexivity.
set (k := 4 * Z.of_nat (m_nrec g) + 7) in *.
(* the model's values *)
set (ct := SlotModel.t_cap_tok (e_pl g)) in *.
set (cn := SlotModel.t_cap_name (e_pl g)) in *.
set (cd := SlotModel.t_cap_disp (e_pl g)) in *.
set (ti := SlotModel.t_in (e_pl g)) in *.
set (to := SlotModel.t_out (e_pl g)) in *.
assert (Rct : 0 <= ct < 40) by (unfold ct, SlotModel.t_cap_tok; apply Z.mod_pos_bound; lia).
assert (Rcn : 0 <= cn < 40) by (unfold cn, SlotModel.t_cap_name; apply Z.mod_pos_bound; lia).
assert (Rcd : 0 <= cd < 64) by (unfold cd, SlotModel.t_cap_disp; apply Z.mod_pos_bound; lia).
assert (Rti : 0 <= ti < 256) by (unfold ti, SlotModel.t_in, SlotModel.tb; apply SlotModel.inb_range).
assert (Rto : 0 <= to < 256) by (unfold to, SlotModel.t_out, SlotModel.tb; apply SlotModel.inb_range).
destruct (si_blocks3 g ly2 S2 W2 mem2 md2 nm tk dp _ _ _ HAR2 Hblk)
  as (Inm & Itk & Idp & Hnm4 & Htk4 & Hdp4 & _ & _ & _ & Dnt & Dnd & Dtd).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 nm _ HAR2 Inm) as (_ & _ & Hnmc & _).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 tk _ HAR2 Itk) as (_ & _ & Htkc & _).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 dp _ HAR2 Idp) as (_ & _ & Hdpc & _).
assert (Hrq : forall c, 0 <= c -> req_size (Z.max c 1) = Z.max c 1)
  by (intros c Hc; unfold req_size; destruct (Z.eqb_spec (Z.max c 1) 0); lia).
assert (Qn : req_size (Z.max cn 1) = Z.max cn 1) by (apply Hrq; lia).
assert (Qt : req_size (Z.max ct 1) = Z.max ct 1) by (apply Hrq; lia).
assert (Qd : req_size (Z.max cd 1) = Z.max cd 1) by (apply Hrq; lia).
rewrite Qn in Hnmc, Dnt, Dnd. rewrite Qt in Htkc, Dnt, Dtd. rewrite Qd in Hdpc, Dnd, Dtd.
(* the environment: atoms 32 .. 38 are the seven machine-frame words the step loads *)
remember (Eimg (Ereg regs2 [Z_to_bv 64 ct; Z_to_bv 64 cn; Z_to_bv 64 nm; Z_to_bv 64 to; Z_to_bv 64 ti;
  Z_to_bv 64 dp; Z_to_bv 64 SHADOW_OFF])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 ct)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 cn)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 nm)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 to)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 ti)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 dp)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 6)).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
clear HE.
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), Rs1. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb C1. lia. }
assert (U2 : bv_unsigned (ew E 2) = mf).
{ rewrite (EE 2%nat 2%bv eq_refl), Rsp. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb C1. lia. }
(* the symbolic state at +0x1348 *)
assert (HS : st_ok_pi SEGS VAL E si_rl_ss
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x1348)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold si_rl_ss. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold si_rl_mf, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - Hmf0 C1; lia|]. split; [clear - Hmf0 H47 Hmfb; lia|].
      split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ mf 128 8 (SOff 32 0) ct);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Rct; lia | lia | exact V128].
      * apply (chunk_ok_val SEGS E _ mf 144 8 (SOff 33 0) cn);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Rcn; lia | lia | exact V144].
      * apply (chunk_ok_val SEGS E _ mf 152 8 (SOff 34 0) nm);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Hnmc Hnm4 C1; lia | lia | exact V152].
      * apply (chunk_ok_val SEGS E _ mf 160 8 (SOff 35 0) to);
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Rto; lia | lia |].
        destruct HV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V160 & _).
        exact V160.
      * apply (chunk_ok_val SEGS E _ mf 168 8 (SOff 38 0) SHADOW_OFF);
        [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; lia | lia
        | exact V168].
      * apply (chunk_ok_val SEGS E _ mf 176 8 (SOff 36 0) ti);
        [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Rti; lia | lia |].
        destruct HV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V176).
        exact V176.
      * apply (chunk_ok_val SEGS E _ mf 184 8 (SOff 37 0) dp);
        [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Hdpc Hdp4 C1; lia | lia | exact V184].
    + unfold si_rl_stk, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U2. split; [clear - Hmf0 C1; lia|]. split; [clear - Hmf0 H47 Hmfb; lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply HPRES.
      change (spZ (e_regs g)) with (e_sp0 g) in *. clear - Ho Hmfb HSTK' Has. lia.
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, si_rl_mf, si_rl_stk. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U2.
    right. clear. lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I]. }
unfold cfg_at. change (w64 (BASE + 0x1348)) with (Z_to_bv 64 (BASE + 0x1348)).
(* ---- run 1: +0x1348 .. the call at +0x1378 ---- *)
paj_run_shc RUNP RUNC HS HJ.
{ unfold si_rl_ss. cbn [ss_mem]. apply awr_ok_cons_ro; [unfold si_rl_mf; cbn [YP09.r_whi YP09.r_wlo]; lia|].
  intros a (r & Hr & Ha). destruct Hr as [<- | []]. unfold si_rl_stk in Ha.
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U2 in Ha. left.
  change (spZ (e_regs g)) with (e_sp0 g) in *. clear - Ha Hmfb HSTK' Has. lia. }
(* what run 1 kept: every byte outside the two stack-argument words *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 16 <= a < mf) ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw. apply (kept_of_frame E _ (w_H W2) mem2 (ms_mem ms) (fun x => mf - 16 <= x < mf) HFr);
  [|exact Ha|exact Hw].
  intros bb wlo whi aa Hin Hr. unfold si_rl_ss, si_rl_mf, si_rl_stk, windows in Hin.
  cbn [map ss_mem YP09.r_base YP09.r_wlo YP09.r_whi In] in Hin.
  destruct Hin as [Eq | [Eq | []]]; injection Eq as <- <- <-; cbn [base_val] in Hr;
  [rewrite U9 in Hr; clear - Hr; lia | rewrite U2 in Hr; clear - Hr; lia]. }
clear HF HFr HG.
(* the input block, below the heap ceiling *)
assert (INP : 0 < e_n g -> In (e_p g, e_n g) (ablocks B (e_ly g) (e_S g)) /\ In (e_p g, e_n g) (ablocks B ly2 S2) /\
  4096 <= e_p g /\ e_p g + e_n g <= alloc_ceiling).
{ intros Hn0. destruct Hinp0 as [(Hn & _) | (_ & Hin0)]; [clear - Hn Hn0; lia|].
  assert (Hin2 : In (e_p g, e_n g) (ablocks B ly2 S2)).
  { apply (Permutation_in _ (Permutation_sym (proj1 Hblk))). apply in_or_app. right. exact Hin0. }
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 Hin2) as (_ & Hp4 & Hpc & _).
  unfold req_size in Hpc. destruct (Z.eqb_spec (e_n g) 0) as [E0 | E0]; [clear - Hn0 E0; lia|].
  split; [exact Hin0|]. split; [exact Hin2|]. split; [exact Hp4 | exact Hpc]. }
(* every zone si_vals speaks of is below the heap ceiling or in the stack above mf *)
assert (AREA : forall a, si_area g pos mf a -> 0 <= a < alloc_ceiling \/ mf <= a < e_sp0 g).
{ intros a Ha. unfold si_area in Ha. destruct Ha as [Hs | [Hf | [Hsh | Hi]]].
  - right. clear - Hs Hmfb. lia.
  - left. clear - Hf HSF0 HSF1. lia.
  - left. rewrite Esh in Hsh. unfold SHADOW_OFF in Hsh. clear - Hsh HSF0 HSF1 C1. lia.
  - left. assert (Hn0 : 0 < e_n g) by (clear - Hi; lia). destruct (INP Hn0) as (_ & _ & Hp4 & Hpc).
    clear - Hi Hp4 Hpc. lia. }
assert (KEEPA : forall a, si_area g pos mf a -> aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. destruct (AREA a Ha) as [Hx | Hx]; apply KEEP1; clear - Hx Hmf0 Hmfb H47 C1; lia. }
assert (HSF8 : SFa g pos mod 8 = 0) by (clear - HSF64; lia).
pose proof (si_vals_moved g pos mf W2 mem2 W2 (ms_mem ms) ltac:(clear - Hmfb; lia) HSF8 Hlen KEEPA HV) as HV1.
pose proof HV1 as (_ & _ & _ & _ & Vra1 & Vs01 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hid1 & _).
pose proof HJ as (HAR21 & _ & _ & _ & _ & _ & Hnev21 & _ & _ & _ & _ & _ & _ & HPRES1 & _).
(* the registers at the call *)
prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (12%bv : bv 5) R12.
prreg HS (13%bv : bv 5) R13. prreg HS (14%bv : bv 5) R14. prreg HS (15%bv : bv 5) R15.
prreg HS (16%bv : bv 5) R16. prreg HS (17%bv : bv 5) R17. prreg HS (1%bv : bv 5) R1.
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (8%bv : bv 5) R8.
rewrite (EE 18%nat 18%bv eq_refl), R18 in R10. rewrite (EE 20%nat 20%bv eq_refl), R20 in R11.
rewrite E36 in R12. rewrite E35 in R13. rewrite E34 in R14. rewrite E33 in R15.
rewrite (EE 21%nat 21%bv eq_refl), R21 in R16. rewrite E32 in R17. rewrite U2 in R2.
rewrite (EE 3%nat 3%bv eq_refl), Rgp in R3. rewrite (EE 4%nat 4%bv eq_refl), Rtp in R4.
rewrite (EE 8%nat 8%bv eq_refl), Rs0 in R8.
assert (Usp : spZ (ms_regs ms) = mf - 16).
{ unfold spZ. rewrite R2, unsigned_lit_small; [clear; lia | clear - Hmf0 H47 Hmfb C1; lia]. }
assert (Us0 : s0Z (ms_regs ms) = e_sp0 g).
{ unfold s0Z. rewrite R8. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb C1. lia. }
assert (HRET : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (HRA4 : 4096 <= bv_unsigned (getr (ms_regs ms) 1)).
{ rewrite R1, unsigned_lit_small; [clear - HBLO; lia | clear - HBASE; lia]. }
(* the two stack arguments: display = dp at sp, display_len = cap_disp at sp + 8 *)
pose proof (st_ok_region_nth E _ _ 1%nat _ HS eq_refl) as Hreg1.
destruct Hreg1 as (_ & _ & _ & Hck1).
cbn [YP09.r_chunks YP09.r_base base_val ms_mem restrict] in Hck1. rewrite U2 in Hck1.
apply Forall_cons_iff in Hck1 as [Ck8 Hck1]. apply Forall_cons_iff in Hck1 as [Ck16 _].
assert (VD : val_mem SEGS (rd W2 (ms_mem ms)) (spZ (ms_regs ms)) 8 dp).
{ rewrite Usp. replace (mf - 16) with (mf + -16) by (clear; lia).
  exact (val_of_chunk_ok SEGS E _ mf (-16) 8 (SOff 37 0) dp Ck16
    ltac:(cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(clear - Hdpc Hdp4 C1; lia) ltac:(lia)). }
assert (VDL : val_mem SEGS (rd W2 (ms_mem ms)) (spZ (ms_regs ms) + 8) 8 cd).
{ rewrite Usp. replace (mf - 16 + 8) with (mf + -8) by (clear; lia).
  exact (val_of_chunk_ok SEGS E _ mf (-8) 8 (SOff 22 0) cd Ck8
    ltac:(cbn [sv_denot]; rewrite (EE 22%nat 22%bv eq_refl), R22, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(clear - Rcd; lia) ltac:(lia)). }
assert (STKP : forall a, spZ (ms_regs ms) <= a < spZ (ms_regs ms) + 16 -> apresent (w_H W2) (ms_mem ms) a).
{ intros a Ha. rewrite Usp in Ha. apply HPRES1. change (spZ (e_regs g)) with (e_sp0 g) in *.
  clear - Ha Hmfb HSTK'. lia. }
(* the image the callee reads *)
assert (HRO2 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) (ms_mem ms)))
  by exact (arodata_ok_journalP SEGS _ _ pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ (HRO _ Haro)).
pose proof (HIMG W2 (ms_mem ms) HRO2) as HIMG2.
destruct HIMG2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRBN & _).
(* the two conditional premises: the said name and the three buffers *)
assert (BUFS : reac_box_name_inv.rbn_bufs B ly2 S2 nm cn tk ct dp cd).
{ unfold reac_box_name_inv.rbn_bufs.
  split; [exists nm, (Z.max cn 1); split; [exact Inm | clear - Rcn; lia]|].
  split; [exists tk, (Z.max ct 1); split; [exact Itk | clear - Rct; lia]|].
  split; [exists dp, (Z.max cd 1); split; [exact Idp | clear - Rcd; lia]|].
  unfold zdisjoint in Dnt, Dnd, Dtd. cbn [fst snd] in Dnt, Dnd, Dtd.
  split; [clear - Dnt Rcn Rct; lia|].
  split; [clear - Dnd Rcn Rcd; lia | clear - Dtd Rct Rcd; lia]. }
pose proof (si_real_said g pos mf ly2 S2 W2 (ms_mem ms) _ _ HJ Hfrs Hmfb Hid1) as SAID.
(* the call's write tokens lie in the three buffers, none of which is an entry block *)
pose proof (proj1 Hblk) as Hpb.
assert (Nnm : ~ In (nm, Z.max cn 1) (ablocks B (e_ly g) (e_S g)))
  by exact (si_rl_notin ly2 S2 W2 mem2 md2 (nm, Z.max cn 1) [(tk, Z.max ct 1); (dp, Z.max cd 1)] _ HAR2 Hpb
    ltac:(cbn [snd]; lia)).
assert (Ntk : ~ In (tk, Z.max ct 1) (ablocks B (e_ly g) (e_S g)))
  by exact (si_rl_notin ly2 S2 W2 mem2 md2 (tk, Z.max ct 1) [(nm, Z.max cn 1); (dp, Z.max cd 1)] _ HAR2
    (Permutation_trans Hpb (perm_swap (tk, Z.max ct 1) (nm, Z.max cn 1) _)) ltac:(cbn [snd]; lia)).
assert (Ndp : ~ In (dp, Z.max cd 1) (ablocks B (e_ly g) (e_S g)))
  by exact (si_rl_notin ly2 S2 W2 mem2 md2 (dp, Z.max cd 1) [(nm, Z.max cn 1); (tk, Z.max ct 1)] _ HAR2
    (Permutation_trans Hpb (Permutation_trans
      (perm_skip (nm, Z.max cn 1) (perm_swap (dp, Z.max cd 1) (tk, Z.max ct 1) _))
      (perm_swap (dp, Z.max cd 1) (nm, Z.max cn 1) _))) ltac:(cbn [snd]; lia)).
assert (HFPB : forall a, inFP (reac_box_name_inv.rbn_fp nm cn tk ct dp cd) a ->
  exists b n, In (b, n) (ablocks B ly2 S2) /\ ~ In (b, n) (ablocks B (e_ly g) (e_S g)) /\ 1 <= n /\
    b <= a < b + req_size n).
{ intros a Ha. destruct (reac_box_name_inv.rbn_fp_in _ _ _ _ _ _ _ Ha) as [(_ & Hx) | [(_ & Hx) | (_ & Hx)]].
  - exists nm, (Z.max cn 1). rewrite Hrq by lia. split; [exact Inm|]. split; [exact Nnm|]. clear - Hx Rcn; lia.
  - exists tk, (Z.max ct 1). rewrite Hrq by lia. split; [exact Itk|]. split; [exact Ntk|]. clear - Hx Rct; lia.
  - exists dp, (Z.max cd 1). rewrite Hrq by lia. split; [exact Idp|]. split; [exact Ndp|]. clear - Hx Rcd; lia. }
assert (HFPT : forall a, inFP (reac_box_name_inv.rbn_fp nm cn tk ct dp cd) a ->
  in_tmp_block (ablocks B (e_ly g) (e_S g)) (ablocks B ly2 S2) a).
{ intros a Ha. destruct (HFPB a Ha) as (b & n & H1 & H2 & _ & H4). exists b, n.
  split; [exact H1|]. split; [exact H2 | exact H4]. }
(* the small premises of the call *)
pose proof (SIM.si_nfam_range (e_pl g)) as Rfam.
assert (Rsaid : 0 <= si_said g pos < 2 ^ 64).
{ unfold si_said. destruct (RcIdentModel.has_model_name (m_id g (m_nrec g)) =? 0); [lia|].
  unfold V_id. clear - HSF0 HSF1 C1. lia. }
assert (Hspo : spZ (ms_regs ms) = e_sp0 g + (mf - 16 - e_sp0 g)) by (rewrite Usp; clear; lia).
assert (Halo : (mf - 16 - e_sp0 g) mod 16 = 0) by (clear - Hmf32 Hsp0al; lia).
assert (Hnego : mf - 16 - e_sp0 g <= -16) by (clear - Hmfb; lia).
assert (Hst1 : 0 <= reac_box_name.REAC_BOX_NAME_STK) by (unfold reac_box_name.REAC_BOX_NAME_STK, ESTACK; lia).
assert (Hbud : reac_box_name.REAC_BOX_NAME_STK - (mf - 16 - e_sp0 g) <= LLVMF_STK)
  by (unfold reac_box_name.REAC_BOX_NAME_STK, ESTACK; clear - HSTK' Hmfb; lia).
assert (Hfl : Z.of_nat (length (frames S2)) <= 7) by (rewrite Hfrs; cbn; lia).
assert (Hnev : st_nev S2 + reac_box_name.EV_REAC_BOX_NAME <= EV_MAX)
  by (unfold reac_box_name.EV_REAC_BOX_NAME; clear - Hnev21 Hnev0 HEV Hk; lia).
assert (Hlive : blocks_bytes S2 + reac_box_name.LIVE_REAC_BOX_NAME <= LIVE_MAX).
{ pose proof (wf_live _ _ _ _ _ (am_wf _ _ _ _ (proj1 HAR21))) as Hl. unfold reac_box_name.LIVE_REAC_BOX_NAME. lia. }
(* ---- the call of reac_box_name at +0x1378 (0x81aec) ---- *)
pmkst HS. rewrite (PSIG IB_reac_box_name AF_reac_box_name eq_refl).
eapply SRr_bind.
{ unshelve eapply (si_call g pos W2 (ms_regs ms) (ms_mem ms) _ ly2 S2 _ k reac_box_name.REAC_BOX_NAME_STK
    (reac_box_name_inv.rbn_fp nm cn tk ct dp cd) reac_box_name.EV_REAC_BOX_NAME (mf - 16 - e_sp0 g)
    (getr (ms_regs ms) 1)
    (reac_box_name_inv.rbn_postQ B ly2 S2 W2 (ms_mem ms) (SlotModel.n_fam (e_pl g)) (SIM.si_sdZ (e_pl g))
       ti to nm cn tk ct dp cd)
    HJ HPRE Hspo Halo Hnego Hst1 Hbud R3 R4 eq_refl HRET HRA4 Us0 Vra1 Vs01 _ HFPT).
  intros ch1 Hchs HFN1.
  exact (HBN ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ ch1 (SlotModel.n_fam (e_pl g)) (si_said g pos) ti to
    nm cn tk ct dp cd (SIM.si_sdZ (e_pl g)) HFN1 HRO2
    R10 ltac:(clear - Rfam; lia) R11 Rsaid R12 ltac:(clear - Rti; lia) R13 ltac:(clear - Rto; lia)
    R14 ltac:(clear - Hnmc Hnm4 C1; lia) R15 ltac:(clear - Rcn; lia) R16 ltac:(clear - Htkc Htk4 C1; lia)
    R17 ltac:(clear - Rct; lia) STKP VD ltac:(clear - Hdpc Hdp4 C1; lia) VDL ltac:(clear - Rcd; lia)
    HRBN (fun _ => conj SAID BUFS) Hfl Hnev Hlive). }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc & HP3 & HQ3).
destruct HQ3 as (EW3 & Hperm3 & Hres). subst W3.
(* the callee's result: a0 = n_r, and on acceptance the three strings *)
assert (R10F : getr regs3 10 = w64 (SlotModel.n_r (e_pl g)) /\
  (SlotModel.n_r (e_pl g) = 0 ->
    garr8 SEGS (rd W2 mem3) nm (map RcIdentModel.bz (SlotModel.n_EXP_NM (e_pl g)) ++ [0]) /\
    garr8 SEGS (rd W2 mem3) tk (map RcIdentModel.bz (SlotModel.n_TK (e_pl g)) ++ [0]) /\
    garr8 SEGS (rd W2 mem3) dp (map RcIdentModel.bz (SlotModel.n_EXP_DP (e_pl g)) ++ [0]))).
{ unfold ct, cn, cd, ti, to in Hres.
  rewrite (SIM.si_accept (e_pl g) nm tk dp ltac:(lia) ltac:(lia) ltac:(lia)) in Hres.
  revert Hres. destruct (Z.eqb_spec (SlotModel.n_r (e_pl g)) 0) as [Hr0 | Hr0]; intros Hres.
  - destruct Hres as (Ra & Gn & Gt & Gd & _). pose proof (SIM.si_r0 _ Hr0) as Wk.
    rewrite (SIM.si_TK _ Wk) in Gt. rewrite (SIM.si_DP _ Wk) in Gd. rewrite (SIM.si_NM _ Wk) in Gn.
    split; [rewrite Hr0; exact Ra|]. intros _. split; [exact Gn|]. split; [exact Gt | exact Gd].
  - destruct Hres as (Ra & _). split; [|intros H; contradiction].
    destruct (SIM.si_r_cases (e_pl g)) as [H | H]; [contradiction|]. rewrite H. exact Ra. }
(* back at +0x137c: the machine-frame region survives the call *)
jafter_call_keep_hi HS 512%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0%nat] HS3.
match type of HS3 with ?Q -> _ => assert (HQ : Q); [|specialize (HS3 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. constructor; [|constructor].
  eapply (region_kept_stack_sub SEGS B); [exact HJc | exact HJ3 | exact U9 | clear - Hmfb; lia
  | clear - Hmfb HSTK'; lia | clear - Hmfb; lia | clear; lia | clear; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
pose proof (img_env_havoc_hi E 512%nat (map (getr regs3) CLOB) HEI ltac:(cbv; lia)) as HEI3.
rewrite R1.
change reac_box_name.EV_REAC_BOX_NAME with 0 in HJ3. rewrite Z.add_0_r in HJ3.
(* ---- run 2: +0x137c .. +0x1388 (the shadow-offset load, the pop, s8 = a0) ---- *)
paj_run_to_sh RUNTOP HS HJ3 0x1388.
{ cbn [ss_mem]. apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil]. }
(* run 2 writes nothing *)
assert (EQ3 : forall x : word, rd W2 (ms_mem ms0) x = rd W2 mem3 x).
{ intros x. apply HFr. intros (r & Hr & Hx). cbn [In ss_mem] in Hr. destruct Hr as [<- | []].
  cbn [YP09.r_wlo YP09.r_whi] in Hx. clear - Hx. lia. }
clear HF HFr HG.
assert (AV3 : forall a, aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem3 a).
{ intros a. unfold aview, mbyte. rewrite EQ3. reflexivity. }
(* what the call kept *)
pose proof HJc as (_ & _ & _ & _ & Hioc & Hfrsc & _ & _ & Kc & _).
assert (KC : forall a, si_area g pos mf a -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) (ms_mem ms) a).
{ apply (si_area_kept_call g pos mf ly2 S2 W2 (ms_mem ms) _ k ly3 S3 W2 mem3 md3 _ _ _ _ HJ Hfrs HJc Hmfb).
  - clear - Hmfb; lia.
  - exact Hst1.
  - intros Hn0. destruct (INP Hn0) as (_ & Hin2 & _). split; [exact Hin2|].
    apply (Permutation_in _ (Permutation_sym Hperm3)). exact Hin2.
  - intros a Ha. destruct (HFPB a Ha) as (b & n & H1 & H2 & H3 & H4). exists b, n. split; [exact H1|].
    split; [|exact H4]. intros Heq. injection Heq as -> ->. apply H2.
    destruct (INP ltac:(lia)) as (Hin0 & _). exact Hin0. }
assert (HKF : forall a, si_area g pos mf a -> aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. rewrite AV3, (KC a Ha). exact (KEEPA a Ha). }
pose proof (si_vals_moved g pos mf W2 mem2 W2 (ms_mem ms0) ltac:(clear - Hmfb; lia) HSF8 Hlen HKF HV) as HVF.
assert (STACKK : forall a, mf <= a < e_sp0 g -> aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. rewrite AV3, Kc.
  - apply KEEP1; clear - Ha Hmf0 Hmfb H47 C1; lia.
  - clear - Ha Hmf0 Hmfb H47 C1; lia.
  - unfold reac_box_name.REAC_BOX_NAME_STK, ESTACK. clear - Ha; lia. }
assert (VMS : forall off v, 112 <= off -> off + 8 <= 192 ->
  val_mem SEGS (rd W2 mem2) (mf + off) 8 v -> val_mem SEGS (rd W2 (ms_mem ms0)) (mf + off) 8 v).
{ intros off v H1 H2 Hv. apply (val_mem_kept SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms0) _ 8 v); [|exact Hv].
  intros kk Hkk. apply STACKK. clear - H1 H2 Hkk Hmfb; lia. }
assert (BZ : forall l, map (fun b : byte => bv_unsigned b) (l ++ [RcIdentModel.zb 0]) = map RcIdentModel.bz l ++ [0]).
{ intros l. rewrite map_app. cbn [map].
  change (bv_unsigned (RcIdentModel.zb 0)) with (RcIdentModel.bz (RcIdentModel.zb 0)).
  rewrite SIM.si_bz0. reflexivity. }
assert (BYTES : SlotModel.n_r (e_pl g) = 0 ->
  bytes_at8 W2 (ms_mem ms0) nm (SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0]) /\
  bytes_at8 W2 (ms_mem ms0) tk (SlotModel.n_TK (e_pl g) ++ [RcIdentModel.zb 0]) /\
  bytes_at8 W2 (ms_mem ms0) dp (SlotModel.n_EXP_DP (e_pl g) ++ [RcIdentModel.zb 0])).
{ intros Hr0. destruct (proj2 R10F Hr0) as (Gn & Gt & Gd). unfold bytes_at8. rewrite !BZ.
  split; [|split]; (eapply garr8_frame; [eassumption | intros x _; unfold mbyte; rewrite EQ3; reflexivity]). }
(* the meter and the model *)
destruct (si_meter (e_S g) S2 S3 k 0 0 ltac:(lia) ltac:(lia) ltac:(lia) MLE MOK (HMT0 S2 S3)) as [MLE3 MOK3].
rewrite Z.add_0_r in MLE3, MOK3.
destruct (si_rl_wvb md3 mat0) as [W3fd W3fs]. destruct (si_rl_wvb md2 mat) as [W2fd W2fs].
pose proof (aos_step_closed_same_io _ _ _
  (reac_box_name_inv.rbn_fp_closed nm cn tk ct dp cd ltac:(lia) ltac:(lia) ltac:(lia)) Hioc) as SIO.
destruct (si_rl_sameio _ _ SIO) as [S3fd S3fs].
(* the registers at +0x1388 *)
prreg HS (2%bv : bv 5) Q2. prreg HS (9%bv : bv 5) Q9. prreg HS (8%bv : bv 5) Q8.
prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10.
prreg HS (24%bv : bv 5) Q24. prreg HS (12%bv : bv 5) Q12. prreg HS (18%bv : bv 5) Q18.
prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
prreg HS (27%bv : bv 5) Q27.
rewrite (EE 2%nat 2%bv eq_refl), Rsp in Q2. rewrite (EE 9%nat 9%bv eq_refl), Rs1 in Q9.
rewrite (EE 8%nat 8%bv eq_refl), Rs0 in Q8. rewrite (EE 3%nat 3%bv eq_refl), Rgp in Q3.
rewrite (EE 4%nat 4%bv eq_refl), Rtp in Q4. rewrite E38 in Q12.
rewrite (EE 18%nat 18%bv eq_refl), R18 in Q18. rewrite (EE 21%nat 21%bv eq_refl), R21 in Q21.
rewrite (EE 22%nat 22%bv eq_refl), R22 in Q22. rewrite (EE 23%nat 23%bv eq_refl), Hshr in Q23.
rewrite (EE 27%nat 27%bv eq_refl), R27 in Q27.
cbn [map nth CLOB] in Q10, Q24. rewrite (proj1 R10F) in Q10, Q24.
(* ---- the boundary inv_I_end at +0x1388 ---- *)
apply SRr_ret.
unfold inv_I_end, acut. pmkst HS.
exists ly3, S3, (ms_regs ms0), (ms_mem ms0), (with_vm_backing (m_vm_lazy md3) mat0 md3).
split; [reflexivity|].
split; [exact HJ3|].
split; [cbn [app] in Hfrsc; rewrite Hfrsc; exact Hfrs|].
split; [exact Hk|].
split; [exact MLE3|].
split; [exact MOK3|].
split.
{ apply (si_ecommon g pos mf ly3 S3 W2 (ms_regs ms0) (ms_mem ms0) _ Q2 Q9 Q8 Hmfb Hmf32 Q3 Q4 HVF HPRE).
  - intros fd. rewrite W3fd, S3fd, W2fd. apply Hfds.
  - rewrite W3fs, S3fs, W2fs. exact Hfs. }
pose proof HVF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  HidF & V112F & V120F & V136F & V160F & V176F).
split; [exact HidF|].
split; [exact Q23|].
split; [exact V136F|].
split; [split; [exact (Permutation_trans Hperm3 (proj1 Hblk)) | exact (proj2 Hblk)]|].
split; [exact Q24|]. split; [exact Q21|]. split; [exact Q10|]. split; [exact Q12|].
split; [exact Q18|]. split; [exact Q27|]. split; [exact Q22|].
split; [apply VMS; [clear; lia | clear; lia | exact V152]|].
split; [apply VMS; [clear; lia | clear; lia | exact V184]|].
split; [apply VMS; [clear; lia | clear; lia | exact V144]|].
split; [apply VMS; [clear; lia | clear; lia | exact V128]|].
split; [exact V120F|]. split; [exact V176F|]. split; [exact V160F|]. split; [exact V112F|].
exact BYTES.
Qed.
Check (si_L_real : forall g pos mf nm tk dp W2 c2, si_C4 g pos mf nm tk dp W2 c2 -> SRr SEGS W2 c2 (INV_I g pos mf nm tk dp)).

(* ---- step 2 of segment I: +0x12b8 .. +0x12e8 ------------------------------------------------------------ *)

(* The machine frame's two words the step reads (mf+136 = &id+3, mf+184 = &id) and the word it writes
   (mf+144); base x9 = mf (atom 9). *)
Definition si_stem_mf : YP09.region := YP09.mkRegion (Some 9%nat) 136 192 144 152
  [YP09.mkChunk 136 (CVal 8 (SOff 32 3)); YP09.mkChunk 184 (CVal 8 (SOff 32 0))].
(* The identity struct's has_model_name byte, base an extra atom = SFa g pos + V_id (atom 32). *)
Definition si_stem_id : YP09.region := YP09.mkRegion (Some 32%nat) 20 21 0 0
  [YP09.mkChunk 20 (CVal 1 (SOff 33 0))].
Definition si_stem_ss : sstate := mkSS 0x12b8 sr_atoms [si_stem_mf; si_stem_id] None (mkFacts [] [] []).

(* the beqz at 0x81a34 (the abort), as a fact about the value in a0 *)
Lemma si_stem_br0 : forall Ex n (v : word), ew Ex n = v ->
  branch_taken BC_EQ (sv_denot Ex (SOff n 0)) (sv_denot Ex (SLit 0)) = true -> v = w64 0.
Proof.
intros Ex n v Hn Hb. rewrite branch_eq_U in Hb. apply Z.eqb_eq in Hb.
unfold U in Hb. cbn [sv_denot] in Hb. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned in Hb.
apply bv_eq. exact Hb.
Qed.
Lemma si_stem_w64_inj : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> w64 a = w64 b -> a = b.
Proof.
intros a b Ha Hb H.
assert (Ea : bv_unsigned (w64 a) = a) by (apply unsigned_lit_small; exact Ha).
assert (Eb : bv_unsigned (w64 b) = b) by (apply unsigned_lit_small; exact Hb).
rewrite <- Ea, <- Eb, H. reflexivity.
Qed.
(* the ALU of the span: `zext.b`, `seqz` + `addi -1` + `and` (the said_name mask) *)
Lemma si_stem_alu : forall op a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  alu64 op (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (zalu_raw 63 64 op a b).
Proof.
intros op a b Ha Hb. apply bv_eq. rewrite alu64_unsigned.
rewrite (unsigned_lit_small a Ha), (unsigned_lit_small b Hb), Z_to_bv_unsigned. reflexivity.
Qed.
Lemma si_stem_wmod : forall a, Z_to_bv 64 a = Z_to_bv 64 (a mod 2 ^ 64).
Proof.
intros a. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by (clear; lia). reflexivity.
Qed.
Lemma si_stem_zext8 : forall v, 0 <= v < 256 -> zext 64 (bv_extract 0 8 (Z_to_bv 64 v)) = Z_to_bv 64 v.
Proof.
intros v Hv. apply bv_eq. unfold zext. rewrite bv_zero_extend_unsigned'.
rewrite extract_unsigned_mod, (unsigned_lit_small v ltac:(clear - Hv; lia)).
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (2 ^ Z.of_N 8) with 256.
rewrite (Z.mod_small v 256 Hv). apply Z.mod_small. clear - Hv. lia.
Qed.
Lemma si_stem_and255 : forall v, 0 <= v < 256 ->
  alu64 ALU_AND (Z_to_bv 64 v) (Z_to_bv 64 255) = Z_to_bv 64 v.
Proof.
intros v Hv.
rewrite (si_stem_alu ALU_AND v 255 ltac:(clear - Hv; lia) ltac:(clear; lia)). cbn [zalu_raw].
f_equal. change 255 with (Z.ones 8). rewrite Z.land_ones by (clear; lia).
change (2 ^ 8) with 256. apply Z.mod_small. exact Hv.
Qed.
Lemma si_stem_mask0 : forall x, 0 <= x < 2 ^ 64 ->
  alu64 ALU_AND (alu64 ALU_ADD (alu64 ALU_SLTU (zext 64 (bv_extract 0 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 1)) (Z_to_bv 64 (-1))) (Z_to_bv 64 x) = Z_to_bv 64 0.
Proof.
intros x Hx. rewrite (si_stem_zext8 0 ltac:(clear; lia)).
rewrite (si_stem_alu ALU_SLTU 0 1 ltac:(clear; lia) ltac:(clear; lia)). cbn [zalu_raw Z.ltb Z.compare].
rewrite (si_stem_wmod (-1)).
replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by (vm_compute; reflexivity).
rewrite (si_stem_alu ALU_ADD 1 (2 ^ 64 - 1) ltac:(clear; lia) ltac:(clear; lia)). cbn [zalu_raw].
rewrite (si_stem_wmod (1 + (2 ^ 64 - 1))).
replace ((1 + (2 ^ 64 - 1)) mod 2 ^ 64) with 0 by (vm_compute; reflexivity).
rewrite (si_stem_alu ALU_AND 0 x ltac:(clear; lia) Hx). cbn [zalu_raw].
rewrite Z.land_0_l. reflexivity.
Qed.
Lemma si_stem_mask1 : forall h x, 0 < h < 256 -> 0 <= x < 2 ^ 64 ->
  alu64 ALU_AND (alu64 ALU_ADD (alu64 ALU_SLTU (zext 64 (bv_extract 0 8 (Z_to_bv 64 h)))
    (Z_to_bv 64 1)) (Z_to_bv 64 (-1))) (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
intros h x Hh Hx. rewrite (si_stem_zext8 h ltac:(clear - Hh; lia)).
rewrite (si_stem_alu ALU_SLTU h 1 ltac:(clear - Hh; lia) ltac:(clear; lia)). cbn [zalu_raw].
destruct (Z.ltb_spec h 1) as [Hlt | Hge]; [clear - Hh Hlt; lia|].
rewrite (si_stem_wmod (-1)).
replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by (vm_compute; reflexivity).
rewrite (si_stem_alu ALU_ADD 0 (2 ^ 64 - 1) ltac:(clear; lia) ltac:(clear; lia)). cbn [zalu_raw].
replace (0 + (2 ^ 64 - 1)) with (2 ^ 64 - 1) by (clear; lia).
rewrite (si_stem_alu ALU_AND (2 ^ 64 - 1) x ltac:(clear; lia) Hx). cbn [zalu_raw].
f_equal. change (2 ^ 64 - 1) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by (clear; lia).
apply Z.mod_small. exact Hx.
Qed.
(* one value fact out of a chunk of the symbolic state (lib/A/Prog/reac_box_name_seg5.v rbn5_chunkv) *)
Lemma si_stem_chunkv : forall Ex ssx H msx i r n b off w e v,
  st_ok_pi SEGS VAL Ex ssx (restrict H msx) -> nth_error (ss_mem ssx) i = Some r ->
  YP09.r_base r = Some n -> bv_unsigned (ew Ex n) = b ->
  In (YP09.mkChunk off (CVal w e)) (YP09.r_chunks r) ->
  sv_denot Ex e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  val_mem SEGS (mrestrict H (ms_mem msx)) (b + off) (N.to_nat w) v.
Proof.
intros Ex ssx H msx i r n b off w e v HSx Hi Hb Hn Hc He Hv Hw.
pose proof (st_ok_pi_region_nth Ex ssx _ i r HSx Hi) as HR. cbn [ms_mem restrict] in HR.
pose proof (region_ok_chunk SEGS Ex _ r _ HR Hc) as C. rewrite Hb in C. cbn [base_val] in C. rewrite Hn in C.
exact (val_of_chunk_ok SEGS Ex _ b off w e v C He Hv Hw).
Qed.

Lemma si_L_stem : forall g pos mf W2 c2, si_C1 g pos mf W2 c2 -> SRr SEGS W2 c2 (si_C2 g pos mf).
Proof.
intros g pos mf W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HP as (HM & Hbl & Rs23 & R18 & R21 & R26 & R22 & V184).
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
  S9 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27 & Vflag & HPRE & Hfds & Hfs & Hinb).
pose proof HM as HM'.
destruct HM' as (M16 & M64 & M192 & M168 & Mra & Ms0 & M9 & M18 & M19 & M20 & M21 & M22 & M23 & M24 &
  M25 & M26 & M27 & Mflag & Minp & Mid & M112 & M120 & M136 & M160 & M176).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
assert (Has : ASTACK = 16384) by reflexivity.
destruct (si_geo g pos mf ly2 S2 W2 mem2 md2 _ HJ Hfrs Hmfb)
  as (Hmf0 & H47 & Hsp0al & Hslo & EFa & HSF0 & HSF1 & HSF64 & HSFapp).
set (sp0 := e_sp0 g) in *. set (SF := SFa g pos) in *.
assert (Esp0 : sp0 = e_sp0 g) by reflexivity.
assert (ESF : SF = SFa g pos) by reflexivity.
set (hmn := RcIdentModel.has_model_name (m_id g (m_nrec g))).
(* the has_model_name byte of the identity struct *)
destruct Mid as (Midb & Midz & Midk).
assert (Hidl : length (m_id g (m_nrec g)) = 38%nat) by apply SlotModel.rec_id_length.
assert (Hb20 : val_mem SEGS (rd W2 mem2) (SF + V_id + 20) 1 hmn /\ 0 <= hmn < 256).
{ unfold bytes_at8 in Midb.
  assert (Hlt : (20 < length (map (fun b : byte => bv_unsigned b) (m_id g (m_nrec g))))%nat)
    by (rewrite length_map, Hidl; lia).
  destruct (Midb 20%nat Hlt) as (Hv & Hr).
  assert (Enth : nth 20 (map (fun b : byte => bv_unsigned b) (m_id g (m_nrec g))) 0 = hmn)
    by (unfold hmn; rewrite SIM.si_nth_map_bz; reflexivity).
  rewrite Enth in Hv, Hr. split; [|exact Hr].
  replace (SF + V_id + 20) with (SF + V_id + Z.of_nat 20) by (clear; lia). exact Hv. }
destruct Hb20 as (Vb20 & Rb20).
(* the environment: atom 32 = &id, atom 33 = the has_model_name byte *)
remember (Eimg (Ereg regs2 [Z_to_bv 64 (SF + V_id); Z_to_bv 64 hmn])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (SF + V_id))
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 hmn)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
assert (AGE : env_agree 32 (Ereg regs2 [Z_to_bv 64 (SF + V_id); Z_to_bv 64 hmn]) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), Rs1. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb C1 Has. lia. }
assert (U32 : bv_unsigned (ew E 32) = SF + V_id).
{ rewrite E32. apply unsigned_lit_small. clear - HSF0 HSF1 C1. unfold V_id. lia. }
assert (U33 : bv_unsigned (ew E 33) = hmn).
{ rewrite E33. apply unsigned_lit_small. clear - Rb20. lia. }
(* the symbolic state at +0x12b8 *)
assert (HS : st_ok_pi SEGS VAL E si_stem_ss
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x12b8)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold si_stem_ss. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold si_stem_mf, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - Hmf0 C1 Has; lia|].
      split; [clear - H47 Hmfb; lia|].
      split.
      * intros o Ho. apply (apresent_writable SEGS).
        refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (mf + o) HJ _)).
        left. clear - Ho Hmfb HSTK' Has. lia.
      * constructor; [|constructor; [|constructor]].
        -- apply (chunk_ok_val SEGS E _ mf 136 8 (SOff 32 3) (SF + V_id + 3));
           [cbn [sv_denot]; rewrite U32; reflexivity
           | clear - HSF0 HSF1 C1; unfold V_id; zside | lia | exact M136].
        -- apply (chunk_ok_val SEGS E _ mf 184 8 (SOff 32 0) (SF + V_id));
           [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity
           | clear - HSF0 HSF1 C1; unfold V_id; zside | lia | exact V184].
    + unfold si_stem_id, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U32. split; [clear - HSF0; unfold V_id; lia|].
      split; [clear - HSF1 C1; unfold V_id; lia|].
      split; [intros o Ho; clear - Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (SF + V_id) 20 1 (SOff 33 0) hmn);
      [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | clear - Rb20; zside | lia | exact Vb20].
  - apply pairwise_disjoint_of_extents. unfold si_stem_mf, si_stem_id, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite U9, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; right; clear - HSF1 Hmf0 Has C1; unfold V_id; lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I | split; exact I]. }
unfold cfg_at. change (w64 (BASE + 0x12b8)) with (Z_to_bv 64 (BASE + 0x12b8)).
paj_run_shc RUNP RUNC HS HJ.
{ intros a (r & Hr & Ha). unfold si_stem_ss in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]]; unfold si_stem_mf, si_stem_id in Ha;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?U9, ?U32 in Ha;
  [left; clear - Ha Hmfb HSTK' Has; lia | clear - Ha; lia]. }
(* what run 1 kept: it writes nothing, so every byte outside the declared window is unchanged *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 144 <= a < mf + 152) ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw.
  apply (kept_of_frame E _ (w_H W2) mem2 (ms_mem ms) (fun x => mf + 144 <= x < mf + 152) HFr);
  [|exact Ha|exact Hw].
  intros bb wlo whi aa Hin Hr. unfold si_stem_ss, windows in Hin. cbn in Hin.
  destruct Hin as [Eq | [Eq | []]]; injection Eq as <- <- <-; cbn [base_val] in Hr;
  [rewrite U9 in Hr; clear - Hr; lia | rewrite U32 in Hr; clear - Hr; lia]. }
assert (VM1 : forall a (n : nat) v, mf + 152 <= a -> a + Z.of_nat n <= sp0 ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 (ms_mem ms)) a n v).
{ intros a n v H1 H2 Hv. apply (val_mem_kept SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms) a n v); [|exact Hv].
  intros i Hi. apply KEEP1; clear - H1 H2 Hi Hmfb Hmf0 H47 C1 Has; lia. }
clear HF HG.
(* the registers at the call *)
prreg HS (10%bv : bv 5) R10. prreg HS (2%bv : bv 5) R2. prreg HS (1%bv : bv 5) R1.
prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (8%bv : bv 5) R8.
rewrite (EE 18%nat 18%bv eq_refl), R18 in R10. rewrite (EE 2%nat 2%bv eq_refl), Rsp in R2.
rewrite (EE 3%nat 3%bv eq_refl), Rgp in R3. rewrite (EE 4%nat 4%bv eq_refl), Rtp in R4.
rewrite (EE 8%nat 8%bv eq_refl), Rs0 in R8.
assert (Usp : spZ (ms_regs ms) = mf)
  by (unfold spZ; rewrite R2; apply unsigned_lit_small; clear - Hmf0 H47 Hmfb C1 Has; lia).
assert (Us0 : s0Z (ms_regs ms) = sp0)
  by (unfold s0Z; rewrite R8; apply unsigned_lit_small; clear - Hslo H47 C1 HSTK' Has; lia).
(* the read-only image at the call's state, and the stem table it holds *)
pose proof HPRE as (HFN & Hraz & _ & _ & Hinp0 & Hlen & _ & _ & _ & _ & Hros & _).
assert (HROc : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) (ms_mem ms))).
{ exact (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B LLVMF_STK sp0 []
    (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 (ms_mem ms) _ _ HJ (HRO _ Hros)). }
destruct (HIMG W2 (ms_mem ms) HROc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HZS & _).
destruct (si_stem_nz W2 (ms_mem ms) HROc) as (t1 & t2 & t3 & Vt1 & Vt2 & Vt3 & Rt1 & Rt2 & Rt3).
pose proof (SIM.si_nfam_range (e_pl g)) as Hfam.
pmkst HS. rewrite (PSIG IB_reac_box_family_stem AF_reac_box_family_stem eq_refl).
eapply SRr_bind.
{ eapply (si_call g pos W2 (ms_regs ms) (ms_mem ms) _ ly2 S2 _ (4 * Z.of_nat (m_nrec g) + 4)
    (16 + ESTACK) [] 0 (mf - sp0) (Z_to_bv 64 (BASE + 4800))
    (fun ly3 S3 W3 regs3 mem3 md3 =>
      getr regs3 10 = w64 (reac_box_family_stem.stem_sel (SlotModel.n_fam (e_pl g)) t1 t2 t3) /\
      ly3 = ly2 /\ S3 = S2 /\ W3 = W2 /\ Permutation (ablocks B ly3 S3) (ablocks B ly2 S2))).
  - exact HJ.
  - exact HPRE.
  - rewrite Usp. clear; lia.
  - clear - Hmf32 Hsp0al. lia.
  - clear - Hmfb. lia.
  - unfold ESTACK. clear; lia.
  - unfold ESTACK. clear - Hmfb HSTK' Has. lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply ret_ok_codeptr_v; [clear; lia | reflexivity].
  - rewrite unsigned_lit_small by (clear - HBASE HBLO; lia). clear - HBLO; lia.
  - exact Us0.
  - apply VM1; [clear - Hmfb; lia | clear; lia | exact Mra].
  - apply VM1; [clear - Hmfb; lia | clear; lia | exact Ms0].
  - intros ch1 Hchs HFN1. rewrite <- R1.
    exact (HSTEM ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ ch1 (SlotModel.n_fam (e_pl g)) t1 t2 t3
      HFN1 R10 ltac:(clear - Hfam; lia) Vt1 Vt2 Vt3 HZS).
  - intros a (r & [] & _). }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc & HP3 & Q10 & -> & -> & -> & Hperm).
(* what the call kept, zone by zone *)
assert (HINB2 : 0 < e_n g -> In (e_p g, e_n g) (ablocks B ly2 S2)).
{ intros Hn0. destruct Hinp0 as [(H0 & _) | (_ & Hin)]; [clear - Hn0 H0; lia|].
  destruct Hbl as (Hperm0 & _). apply (Permutation_in _ (Permutation_sym Hperm0)). cbn [app]. exact Hin. }
assert (KEEPC : forall a, si_area g pos mf a -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) (ms_mem ms) a).
{ eapply (si_area_kept_call g pos mf ly2 S2 W2 (ms_mem ms));
  [exact HJ | exact Hfrs | exact HJc | exact Hmfb | clear - Esp0; lia | unfold ESTACK; clear; lia
  | intros Hn0; split; exact (HINB2 Hn0) | intros a (r & [] & _)]. }
(* back at +0x12c0: the two regions survive the call *)
jafter_call_keep_hi HS 512%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0;1]%nat HS3.
match type of HS3 with ?Q -> _ => assert (HQ : Q); [|specialize (HS3 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. constructor; [|constructor; [|constructor]].
  - eapply (region_kept_stack_sub SEGS B);
    [exact HJc | exact HJ3 | exact U9 | clear - Esp0; lia | clear - Hmfb HSTK' Has; lia
    | clear - Hmfb; lia | clear; lia | clear; lia].
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite U32; intros a Ha.
    + apply (mbyte_of_aview SEGS). apply KEEPC. unfold si_area. right; left.
      clear - Ha; unfold V_id in *; lia.
    + exfalso. clear - Ha. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
pose proof (img_env_havoc_hi E 512%nat (map (getr regs3) CLOB) HEI ltac:(cbv; lia)) as HEI3.
(* the abort at 0x81a34 is not reached: the stem is one of the three table entries or "REAC" *)
assert (Hsel : 0 < reac_box_family_stem.stem_sel (SlotModel.n_fam (e_pl g)) t1 t2 t3 < 2 ^ 64).
{ assert (HIL : 0 < IMG_LO) by (vm_compute; reflexivity).
  pose proof (pa_obj_img 19 ltac:(lia)) as Ho19. pose proof (pa_val_range (A_OBJ 19)) as Hr19.
  unfold reac_box_family_stem.stem_sel.
  destruct (SlotModel.n_fam (e_pl g) =? 1); [clear - Rt1; lia|].
  destruct (SlotModel.n_fam (e_pl g) =? 2); [clear - Rt2; lia|].
  destruct (SlotModel.n_fam (e_pl g) =? 3); [clear - Rt3; lia|].
  clear - Ho19 Hr19 HIL. lia. }
assert (Hew516 : ew (havoc E 512%nat (map (getr regs3) CLOB)) 516%nat = getr regs3 10).
{ change 516%nat with (512 + 4)%nat.
  rewrite (YN3v.ew_havoc_new E 512%nat (map (getr regs3) CLOB) 4%nat (Z_to_bv 64 0)) by (cbn; lia).
  cbn [nth map CLOB]. reflexivity. }
psrr_branch_pi RUNP BR HS.
{ exfalso.
  assert (Hsel0 : 0 <= reac_box_family_stem.stem_sel (SlotModel.n_fam (e_pl g)) t1 t2 t3 < 2 ^ 64)
    by (clear - Hsel; lia).
  assert (Hz00 : 0 <= 0 < 2 ^ 64) by (clear; lia).
  pose proof (si_stem_br0 _ 516%nat _ Hew516 Hc) as Hz. rewrite Q10 in Hz.
  pose proof (si_stem_w64_inj _ 0 Hsel0 Hz00 Hz) as Hz0.
  clear - Hz0 Hsel. lia. }
(* +0x12c4 .. +0x12e8: the has_model_name byte, the said_name mask, the two zext.b, mf+144 = cap_name *)
paj_run_to_sh RUNTOP HS HJ3 0x12e8.
{ intros a (r & Hr & Ha). cbn [ss_mem add_cond In] in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
  rewrite ?(YN3v.ew_havoc_old E 512%nat) in Ha by (cbn; lia); rewrite ?U9, ?U32 in Ha;
  [left; clear - Ha Hmfb HSTK' Has; lia | clear - Ha; lia]. }
(* what run 2 kept: it writes only mf+144..mf+152 *)
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 144 <= a < mf + 152) ->
  aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem3 a).
{ intros a Ha Hw.
  apply (kept_of_frame (havoc E 512%nat (map (getr regs3) CLOB)) _ (w_H W2) mem3 (ms_mem ms0)
    (fun x => mf + 144 <= x < mf + 152) HFr0); [|exact Ha|exact Hw].
  intros bb wlo whi aa Hin Hr. unfold windows in Hin. cbn [ss_mem add_cond map In] in Hin.
  destruct Hin as [Eq | [Eq | []]]; injection Eq as <- <- <-; cbn [base_val] in Hr;
  rewrite ?(YN3v.ew_havoc_old E 512%nat) in Hr by (cbn; lia); rewrite ?U9, ?U32 in Hr;
  clear - Hr; lia. }
(* every zone si_vals lives in is kept by the two runs and the call *)
pose proof HFN as (HAR0 & _).
assert (HPB : 0 < e_n g -> 4096 <= e_p g /\ e_p g + e_n g <= alloc_ceiling).
{ intros Hn0. destruct Hinp0 as [(H0 & _) | (Hr & Hin)]; [clear - Hn0 H0; lia|].
  destruct (al_blocks _ _ LAWS (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) (e_p g) (e_n g) HAR0 Hin)
    as (_ & H4096 & Hceilp & _).
  pose proof (req_size_pos (e_n g) ltac:(clear - Hn0; lia)) as Hrq.
  clear - H4096 Hceilp Hrq Hn0. lia. }
assert (Esh : shadow_addr SF = SHADOW_OFF + SF / 8) by reflexivity.
assert (Hsh1 : 0 <= shadow_addr SF /\ shadow_addr SF + 128 <= alloc_ceiling).
{ clear - Esh HSF0 HSF1 C1. unfold SHADOW_OFF in Esh. lia. }
assert (Hsh1' : 0 <= shadow_addr (SFa g pos) /\ shadow_addr (SFa g pos) + 128 <= alloc_ceiling)
  by exact Hsh1.
assert (HSF0' : 4096 <= SFa g pos) by exact HSF0.
assert (HSF1' : SFa g pos + 1024 <= alloc_ceiling) by exact HSF1.
assert (HSF64' : SFa g pos mod 64 = 0) by exact HSF64.
assert (Hmfb' : e_sp0 g - 336 <= mf <= e_sp0 g - 320) by exact Hmfb.
assert (H47' : e_sp0 g <= 2 ^ 47) by exact H47.
assert (HAREA : forall a, si_area g pos mf a -> 0 <= a < 2 ^ 64 /\ ~ (mf + 144 <= a < mf + 152)).
{ intros a Ha. unfold si_area in Ha. destruct Ha as [Hs | [Hf | [Hsh | Hi]]].
  - clear - Hs Hmfb' Hmf0 H47' C1 Has. lia.
  - clear - Hf HSF0' HSF1' Hmf0 C1 Has. lia.
  - clear - Hsh Hsh1' Hmf0 C1 Has. lia.
  - assert (Hn0 : 0 < e_n g) by (clear - Hi; lia).
    destruct (HPB Hn0) as (Hp1 & Hp2). clear - Hi Hp1 Hp2 Hmf0 C1 Has. lia. }
assert (KEEPALL : forall a, si_area g pos mf a ->
  aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. destruct (HAREA a Ha) as (Ha1 & Ha2).
  rewrite (KEEP2 a Ha1 Ha2), (KEEPC a Ha). exact (KEEP1 a Ha1 Ha2). }
assert (HMn : si_vals g pos mf W2 (ms_mem ms0)).
{ apply (si_vals_moved g pos mf W2 mem2 W2 (ms_mem ms0));
  [clear - Hmfb'; lia | clear - HSF64'; lia | exact Hlen | exact KEEPALL | exact HM]. }
(* the registers at +0x12e8 *)
assert (Hcn : 0 <= SlotModel.t_cap_name (e_pl g) < 40)
  by (unfold SlotModel.t_cap_name; apply Z.mod_pos_bound; clear; lia).
assert (Hct : 0 <= SlotModel.t_cap_tok (e_pl g) < 40)
  by (unfold SlotModel.t_cap_tok; apply Z.mod_pos_bound; clear; lia).
assert (R26' : getr regs2 26 = Z_to_bv 64 (SlotModel.t_cap_name (e_pl g))) by exact R26.
assert (R21' : getr regs2 21 = Z_to_bv 64 (SlotModel.t_cap_tok (e_pl g))) by exact R21.
prreg HS (2%bv : bv 5) Q2. prreg HS (9%bv : bv 5) Q9. prreg HS (8%bv : bv 5) Q8.
prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (23%bv : bv 5) Q23.
prreg HS (10%bv : bv 5) Q10b. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22. prreg HS (27%bv : bv 5) Q27.
rewrite (EE 2%nat 2%bv eq_refl), Rsp in Q2. rewrite (EE 9%nat 9%bv eq_refl), Rs1 in Q9.
rewrite (EE 8%nat 8%bv eq_refl), Rs0 in Q8. rewrite (EE 3%nat 3%bv eq_refl), Rgp in Q3.
rewrite (EE 4%nat 4%bv eq_refl), Rtp in Q4. rewrite (EE 23%nat 23%bv eq_refl), Rs23 in Q23.
rewrite (EE 18%nat 18%bv eq_refl), R18 in Q18. rewrite (EE 22%nat 22%bv eq_refl), R22 in Q22.
rewrite (EE 26%nat 26%bv eq_refl), R26' in Q10b.
rewrite (si_stem_and255 (SlotModel.t_cap_name (e_pl g)) ltac:(clear - Hcn; lia)) in Q10b.
rewrite (EE 21%nat 21%bv eq_refl), R21' in Q19.
rewrite (si_stem_and255 (SlotModel.t_cap_tok (e_pl g)) ltac:(clear - Hct; lia)) in Q19.
rewrite E33 in Q27. rewrite (si_stem_zext8 hmn ltac:(clear - Rb20; lia)) in Q27.
rewrite E33, U32 in Q20.
(* the said_name mask *)
assert (Q20' : getr (ms_regs ms0) 20 = Z_to_bv 64 (si_said g pos)).
{ unfold si_said. destruct (Z.eqb_spec (RcIdentModel.has_model_name (m_id g (m_nrec g))) 0) as [He | Hne].
  - rewrite Q20. unfold hmn. rewrite He.
    apply (si_stem_mask0 (SF + V_id + 3)). clear - HSF0 HSF1 C1. unfold V_id. lia.
  - rewrite Q20. apply (si_stem_mask1 hmn (SF + V_id + 3));
    [unfold hmn in *; clear - Rb20 Hne; lia | clear - HSF0 HSF1 C1; unfold V_id; lia]. }
(* the two machine-frame words of the boundary *)
assert (V184n : val_mem SEGS (rd W2 (ms_mem ms0)) (mf + 184) 8 (SF + V_id)).
{ change 8%nat with (N.to_nat 8).
  eapply (si_stem_chunkv _ _ _ _ 0%nat _ 9%nat mf 184 8 (SOff 32 0) (SF + V_id) HS eq_refl eq_refl U9).
  - cbn [YP09.r_chunks In]. tauto.
  - cbn [sv_denot]. rewrite ?(YN3v.ew_havoc_old E 512%nat) by (cbn; lia).
    rewrite U32, Z.add_0_r. reflexivity.
  - clear - HSF0 HSF1 C1. unfold V_id. zside.
  - clear. lia. }
assert (V144n : val_mem SEGS (rd W2 (ms_mem ms0)) (mf + 144) 8 (SlotModel.t_cap_name (e_pl g))).
{ change 8%nat with (N.to_nat 8).
  eapply (si_stem_chunkv _ _ _ _ 0%nat _ 9%nat mf 144 8 (SAlu ALU_AND (SOff 26 0) (SLit 255))
    (SlotModel.t_cap_name (e_pl g)) HS eq_refl eq_refl U9).
  - cbn [YP09.r_chunks In]. tauto.
  - cbn [sv_denot]. rewrite ?(YN3v.ew_havoc_old E 512%nat) by (cbn; lia).
    rewrite (EE 26%nat 26%bv eq_refl), R26', Z.add_0_r, Z_to_bv_bv_unsigned.
    apply si_stem_and255. clear - Hcn. lia.
  - clear - Hcn. zside.
  - clear. lia. }
(* the boundary si_C2 at +0x12e8 *)
assert (HJ3' : AJ g pos ly2 S2 W2 (ms_mem ms0) (with_vm_backing (m_vm_lazy md3) mat0 md3)
  (4 * Z.of_nat (m_nrec g) + 4)).
{ replace (4 * Z.of_nat (m_nrec g) + 4) with (4 * Z.of_nat (m_nrec g) + 4 + 0) by (clear; lia).
  exact HJ3. }
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3') as (Efd & Efs2).
apply SRr_ret. unfold si_C2, acut. pmkst HS.
exists ly2, S2, (ms_regs ms0), (ms_mem ms0), (with_vm_backing (m_vm_lazy md3) mat0 md3).
split; [reflexivity|].
split; [exact HJ3'|].
split; [exact Hfrs|].
split; [exact Hk|].
split; [exact MLE|].
split; [exact MOK|].
split.
{ apply (si_ecommon g pos mf ly2 S2 W2 (ms_regs ms0) (ms_mem ms0)
    (with_vm_backing (m_vm_lazy md3) mat0 md3));
  [exact Q2 | exact Q9 | exact Q8 | exact Hmfb | exact Hmf32 | exact Q3 | exact Q4 | exact HMn | exact HPRE
  | intros fd; rewrite Efd; reflexivity | exact Efs2]. }
split; [exact HMn|].
split; [exact Hbl|].
split; [exact Q23|].
split; [exact Q10b|].
split; [exact Q18|].
split; [exact Q19|].
split; [exact Q20'|].
split; [exact Q22|].
split; [exact Q27|].
split; [exact V184n | exact V144n].
Qed.

Check (si_L_stem : forall g pos mf W2 c2, si_C1 g pos mf W2 c2 -> SRr SEGS W2 c2 (si_C2 g pos mf)).

(* ==== segment I, step 3: the three buf_of calls, +0x12e8 .. +0x1304 ==================================== *)

(* ---- small helpers ------------------------------------------------------------------------------------ *)
Lemma si_pres : forall (regs regs' : bvmap 5 word) (r : bv 5),
  aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. specialize (HP _ Hr). rewrite !Z_to_bv_bv_unsigned in HP. exact HP. Qed.
Lemma si_pres_z : forall (regs regs' : bvmap 5 word) (z : Z) (r : bv 5),
  aregs_preserved regs regs' -> acallee_saved z -> bv_unsigned r = z -> getr regs' r = getr regs r.
Proof. intros regs regs' z r HP Hz Hr. apply si_pres; [exact HP | rewrite Hr; exact Hz]. Qed.

Lemma si_bsum_blocks : forall ly S, blocks_bytes S = bsum (ablocks B ly S).
Proof.
intros ly S. unfold blocks_bytes, ablocks, blocks, bsum.
induction (st_chunks S) as [|c l IH]; cbn; [reflexivity|].
destruct (is_alloc c); cbn; rewrite IH; reflexivity.
Qed.

Lemma si_bb : forall g ly2 S2 hs, hblocks B g ly2 S2 hs ->
  blocks_bytes S2 = bsum hs + blocks_bytes (e_S g).
Proof.
intros g ly2 S2 hs (Hperm & _).
rewrite (si_bsum_blocks ly2 S2), (bsum_perm _ _ Hperm), bsum_app.
rewrite <- (si_bsum_blocks (e_ly g) (e_S g)). reflexivity.
Qed.

(* A byte at or above the callee's stack pointer is untouched by the call. *)
Lemma si_above : forall (W W3 : world SEGS) memc ly2 S2 md2 ly3 S3 mem3 md3 STK1 sp1 FP1 k1 a,
  ajournal SEGS B STK1 sp1 FP1 ly2 S2 W memc md2 [] ly3 S3 W3 mem3 md3 k1 ->
  alloc_ceiling <= a -> a < 2 ^ 64 -> sp1 <= a ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W) memc a.
Proof.
intros W W3 memc ly2 S2 md2 ly3 S3 mem3 md3 STK1 sp1 FP1 k1 a HJ1 Hc Hhi Hsp.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _). apply G1; clear - Hc Hhi Hsp; lia.
Qed.

Lemma si_vm_above : forall (W W3 : world SEGS) memc ly2 S2 md2 ly3 S3 mem3 md3 STK1 sp1 FP1 k1 a n v,
  ajournal SEGS B STK1 sp1 FP1 ly2 S2 W memc md2 [] ly3 S3 W3 mem3 md3 k1 ->
  alloc_ceiling <= a -> a + Z.of_nat n <= 2 ^ 64 -> sp1 <= a ->
  val_mem SEGS (rd W memc) a n v -> val_mem SEGS (rd W3 mem3) a n v.
Proof.
intros W W3 memc ly2 S2 md2 ly3 S3 mem3 md3 STK1 sp1 FP1 k1 a n v HJ1 Hc Hhi Hsp Hv.
apply (val_mem_kept SEGS (w_H W) (w_H W3) memc mem3 a n v); [|exact Hv].
intros i Hi. apply (si_above W W3 memc ly2 S2 md2 ly3 S3 mem3 md3 STK1 sp1 FP1 k1 (a + i));
  [exact HJ1 | clear - Hc Hi; lia | clear - Hhi Hi; lia | clear - Hsp Hi; lia].
Qed.

(* Reading one written word back out of the symbolic state at a stop. *)
Lemma si_chunkv : forall E ss H ms0 i r n b off w e v,
  st_ok SEGS E ss (restrict H ms0) -> nth_error (ss_mem ss) i = Some r -> YP09.r_base r = Some n ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk off (CVal w e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  val_mem SEGS (mrestrict H (ms_mem ms0)) (b + off) (N.to_nat w) v.
Proof.
intros E ss H ms0 i r n b off w e v HS Hi Hb Hn Hc He Hv Hw.
pose proof (st_ok_region_nth E ss _ i r HS Hi) as HR. cbn [ms_mem restrict] in HR.
pose proof (region_ok_chunk SEGS E _ r _ HR Hc) as C. rewrite Hb in C. cbn [base_val] in C. rewrite Hn in C.
exact (val_of_chunk_ok SEGS E _ b off w e v C He Hv Hw).
Qed.

(* ---- the two symbolic states the three runs use -------------------------------------------------------- *)
(* Nothing is written between a return and the next jal but the store at 0x81a60, which the second run makes
   into the machine frame's slot mf+152 (base x9, the only region the runs need). *)
Definition si_ss0 (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
Definition si_mfr : YP09.region := YP09.mkRegion (Some 9%nat) 152 160 152 160 [].
Definition si_ss1 (pc : Z) : sstate := mkSS pc sr_atoms [si_mfr] None (mkFacts [] [] []).

Lemma si_entry0 : forall (W : world SEGS) (regs : bvmap 5 word) mem pc,
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (si_ss0 pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc. rewrite restrict_mkst_fx. unfold si_ss0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [exact I | split; exact I].
Qed.

Lemma si_entry1 : forall (W : world SEGS) (regs : bvmap 5 word) mem pc mf,
  getr regs 9 = w64 mf -> 0 <= mf -> mf + 160 <= 2 ^ 64 ->
  (forall a, mf + 152 <= a < mf + 160 -> apresent (w_H W) mem a) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (si_ss1 pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc mf R9 Hlo Hhi Hpres.
assert (U9 : bv_unsigned (ew (Eimg (Ereg regs [])) 9) = mf).
{ rewrite (ew_Eimg_Ereg_nat regs [] 9 9%bv eq_refl), R9. unfold w64. apply unsigned_lit_small.
  clear - Hlo Hhi. lia. }
rewrite restrict_mkst_fx. unfold si_ss1. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold si_mfr, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [clear - Hlo; lia|]. split; [clear - Hhi; lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. clear - Ho. lia.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [exact I | split; exact I].
Qed.

(* ---- one buf_of call from the entry's own frame -------------------------------------------------------- *)
Lemma si_bufcall : forall g pos mf (W : world SEGS) ly2 S2 (regsc : bvmap 5 word) memc md2 k off n hs,
  AJ g pos ly2 S2 W memc md2 k -> EPRE g ->
  frames S2 = [(4, pos)] -> 0 <= k -> k + 1 <= EV_LLVMF ->
  mo_le MT (e_S g) S2 (k * MEV MT) -> mo_ok MT S2 ((EV_LLVMF - k) * MEV MT) ->
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
  getr regsc 2 = w64 mf -> getr regsc 8 = w64 (e_sp0 g) ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = Z_to_bv 64 (BASE + off) -> 0 <= off < 2 ^ 40 -> off mod 2 = 0 ->
  In [BASE + off] (CTX_BUF_OF RA_LLVMF) ->
  In [BASE + off; RA_LLVMF] (CTX_BUF_OF RA_LLVMF) ->
  getr regsc 10 = w64 n -> 0 <= n <= 256 ->
  hblocks B g ly2 S2 hs -> bsum hs + Z.max n 1 <= 500 ->
  val_mem SEGS (rd W memc) (e_sp0 g - 8) 8 RA_LLVMF ->
  val_mem SEGS (rd W memc) (e_sp0 g - 16) 8 (s0Z (e_regs g)) ->
  SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_buf_of)) memc (seg_rom SEGS)) md2)
    (fun W3 c3 => exists ly3 S3 regs3 mem3 md3 res,
       c3 = mkCfg (mkst regs3 (Z_to_bv 64 (BASE + off)) mem3 (seg_rom SEGS)) md3 /\
       AJ g pos ly3 S3 W3 mem3 md3 (k + 1) /\
       ajournal SEGS B buf_of.BUF_OF_STK mf [] ly2 S2 W memc md2 [] ly3 S3 W3 mem3 md3 1 /\
       aregs_preserved regsc regs3 /\
       getr regs3 10 = w64 res /\ 4096 <= res /\ res < 2 ^ 64 /\
       frames S3 = [(4, pos)] /\ hblocks B g ly3 S3 (hs ++ [(res, Z.max n 1)]) /\
       mo_le MT (e_S g) S3 ((k + 1) * MEV MT) /\
       mo_ok MT S3 ((EV_LLVMF - (k + 1)) * MEV MT)).
Proof.
intros g pos mf W ly2 S2 regsc memc md2 k off n hs HJ HPRE Hfrs Hk0 Hk1 MLE MOK Hmfb Hmf32
  R2 R8 R3 R4 R1 Hoff0 Hoff2 Hctx0 Hctx1 R10 Hn Hbl Hbsum Vra Vs0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pa_base_lo (PL := PL_identb)) as HBLO. pose proof pa_B_ok as HBok.
destruct (si_geo g pos mf ly2 S2 W memc md2 k HJ Hfrs Hmfb)
  as (Hmf0 & H47 & Hsp16 & Hstklo & EFa & HSF0 & HSF1 & HSF64 & HApp).
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'. assert (Has : ASTACK = 16384) by reflexivity.
assert (Hbo : buf_of.BUF_OF_STK = 16400) by reflexivity.
assert (Hmfr : 0 <= mf < 2 ^ 64) by (clear - Hmf0 H47 Hmfb C1 Has; lia).
assert (Hsp0r : 0 <= e_sp0 g < 2 ^ 64) by (clear - H47 C1 Hstklo HSTK' Has; lia).
assert (Hsp : spZ regsc = e_sp0 g + (mf - e_sp0 g)).
{ unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by (clear - Hmfr; lia). lia. }
assert (Hom : (mf - e_sp0 g) mod 16 = 0).
{ clear - Hmf32 Hsp16.
  pose proof (Z.div_mod mf 32 ltac:(lia)) as D1. rewrite Hmf32, Z.add_0_r in D1.
  pose proof (Z.div_mod (e_sp0 g) 16 ltac:(lia)) as D2. rewrite Hsp16, Z.add_0_r in D2.
  replace (mf - e_sp0 g) with ((2 * (mf / 32) - e_sp0 g / 16) * 16) by lia. apply Z_mod_mult. }
assert (Hs0 : s0Z regsc = e_sp0 g).
{ unfold s0Z. rewrite R8. unfold w64. apply unsigned_lit_small. clear - Hsp0r. lia. }
assert (Hraw4 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + off))).
{ rewrite unsigned_lit_small by (clear - HBok Hoff0; lia). clear - HBLO Hoff0. lia. }
pose proof HPRE as (HFN0 & _ & _ & _ & _ & _ & _ & _ & Hev0 & Hlive0 & _).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & Hnev2 & _).
assert (Hev : st_nev S2 + buf_of.EV_BUF_OF <= EV_MAX).
{ unfold buf_of.EV_BUF_OF. clear - Hnev2 Hev0 Hk0 Hk1 HEV. lia. }
assert (Hlive : blocks_bytes S2 + Z.max n 1 <= LIVE_MAX).
{ rewrite (si_bb g ly2 S2 hs Hbl). unfold LIVE_LLVMF in HLIVE. clear - Hbsum Hlive0 HLIVE. lia. }
destruct (si_meter_room S2 k (Z.max n 1) ltac:(clear - Hn; lia) Hk1 MOK) as (MROOM & Hmm).
eapply SRr_mono.
{ eapply (si_call g pos W regsc memc (Z_to_bv 64 (BASE + AF_buf_of)) ly2 S2 md2 k
    buf_of.BUF_OF_STK [] 1 (mf - e_sp0 g) (Z_to_bv 64 (BASE + off))
    (fun ly3 S3 W3 regs3 mem3 md3 => exists res : Z, getr regs3 10 = w64 res /\ 4096 <= res /\
       frames S3 = frames S2 /\ ablocks B ly3 S3 = ablocks B ly2 S2 ++ [(res, Z.max n 1)] /\
       mo_le MT S2 S3 (mo_malloc MT (Z.max n 1)))).
  - exact HJ.
  - exact HPRE.
  - exact Hsp.
  - exact Hom.
  - clear - Hmfb. lia.
  - clear - Hbo. lia.
  - clear - Hbo Hmfb HSTK' Has. lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply ret_ok_codeptr_v; [exact Hoff0 | exact Hoff2].
  - exact Hraw4.
  - exact Hs0.
  - exact Vra.
  - exact Vs0.
  - intros ch1 Hchs HFN.
    assert (Hctx : In (raZ regsc :: spine ch1) (CTX_BUF_OF RA_LLVMF)).
    { unfold raZ. rewrite R1, unsigned_lit_small by (clear - HBok Hoff0; lia).
      destruct Hchs as [-> | ->]; cbn [spine map]; [exact Hctx0 | exact Hctx1]. }
    pose proof (HBUF ly2 S2 W regsc memc md2 ch1 n HFN Hctx R10
      ltac:(unfold MALLOC_MAX; clear - Hn; lia) Hev Hlive MROOM) as HC0.
    unfold buf_of.tbuf_of_post, apost_base, buf_of.A_buf_of in HC0.
    rewrite R1 in HC0. exact HC0.
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W3 c3 Hwle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc & HP3 & HK).
assert (Esp : e_sp0 g + (mf - e_sp0 g) = mf) by (clear; lia). rewrite Esp in HJc.
destruct HK as (res & R10' & Hres & Hfrs3 & Eab & M23).
pose proof (proj1 HJ3) as HAR3.
assert (Hin3 : In (res, Z.max n 1) (ablocks B ly3 S3))
  by (rewrite Eab; apply in_or_app; right; left; reflexivity).
destruct (al_blocks SEGS B LAWS ly3 S3 W3 mem3 md3 res (Z.max n 1) HAR3 Hin3) as (_ & Hr4 & Hrc & _ & _).
destruct Hbl as (Hperm & Hhs).
exists ly3, S3, regs3, mem3, md3, res.
split; [reflexivity|]. split; [exact HJ3|]. split; [exact HJc|]. split; [exact HP3|].
split; [exact R10'|]. split; [exact Hres|].
split; [pose proof (req_size_pos (Z.max n 1) ltac:(clear - Hn; lia)) as Hrq;
        clear - Hrc C1 Hrq; lia|].
split; [rewrite Hfrs3; exact Hfrs|].
split.
{ split.
  - rewrite Eab, <- app_assoc.
    eapply Permutation_trans; [apply Permutation_app_tail; exact Hperm|].
    rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_app_comm.
  - apply Forall_app. split; [exact Hhs|].
    apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. clear - Hres Hn. lia. }
destruct (si_meter (e_S g) S2 S3 k (mo_malloc MT (Z.max n 1)) 1 ltac:(lia)
  ltac:(clear - Hmm; lia) Hk1 MLE MOK M23) as (MLE3 & MOK3).
split; [exact MLE3 | exact MOK3].
Qed.

Lemma si_prtrans : forall r1 r2 r3, aregs_preserved r1 r2 -> aregs_preserved r2 r3 -> aregs_preserved r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

Lemma si_agree : forall (regs : bvmap 5 word), env_agree 32 (Ereg regs (@nil word)) (Eimg (Ereg regs (@nil word))).
Proof. intros regs. split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

(* ---- the step ------------------------------------------------------------------------------------------ *)
Lemma si_L_bufs : forall g pos mf W2 c2, si_C2 g pos mf W2 c2 ->
  SRr SEGS W2 c2 (fun W3 c3 => exists nm tk dp, si_C3 g pos mf nm tk dp W3 c3).
Proof.
intros g pos mf W2 c2 Hstart.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HP as (HV & Hbl & Rs7 & Ra0 & R18 & R19 & R20 & R22 & R27 & V184 & V144).
pose proof HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
  P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & Vflag & HPRE & Hfds & Hfs & Hinb).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBok. pose proof (pa_base_lo (PL := PL_identb)) as HBLO.
destruct (si_geo g pos mf ly2 S2 W2 mem2 md2 _ HJ Hfrs Hmfb)
  as (Hmf0 & H47 & Hsp16 & Hstklo & EFa & HSF0 & HSF1 & HSF64 & HApp).
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'. assert (Has : ASTACK = 16384) by reflexivity.
assert (Hmfr : 0 <= mf < 2 ^ 64) by (clear - Hmf0 H47 Hmfb C1 Has; lia).
assert (Hsp0lo : 0x7fff7f800000 <= e_sp0 g) by (clear - C1 Hstklo HSTK' Has; lia).
assert (Hsp0r : 0 <= e_sp0 g < 2 ^ 64) by (clear - H47 Hsp0lo; lia).
assert (Hcn : 0 <= SlotModel.t_cap_name (e_pl g) < 40)
  by (unfold SlotModel.t_cap_name; apply Z.mod_pos_bound; lia).
assert (Hct : 0 <= SlotModel.t_cap_tok (e_pl g) < 40)
  by (unfold SlotModel.t_cap_tok; apply Z.mod_pos_bound; lia).
assert (Hcd : 0 <= SlotModel.t_cap_disp (e_pl g) < 64)
  by (unfold SlotModel.t_cap_disp; apply Z.mod_pos_bound; lia).
pose proof (SlotModel.nrec_range (e_pl g)) as Hnr.
assert (Hnrz : Z.of_nat (m_nrec g) = SlotModel.nrec (e_pl g))
  by (unfold m_nrec, SlotModel.nrecn; apply Z2Nat.id; clear - Hnr; lia).
assert (Hkv : 0 <= 4 * Z.of_nat (m_nrec g) + 4 <= 260) by (rewrite Hnrz; clear - Hnr; lia).
assert (HEVv : EV_LLVMF = 266) by reflexivity.
assert (Esh : shadow_addr (SFa g pos) = SHADOW_OFF + SFa g pos / 8) by reflexivity.
assert (Hsh : 0 <= shadow_addr (SFa g pos) /\ shadow_addr (SFa g pos) + 128 <= alloc_ceiling)
  by (clear - Esh HSF0 HSF1 C1; unfold SHADOW_OFF in Esh; lia).
assert (HINP : forall ly S hs, hblocks B g ly S hs -> 0 < e_n g -> In (e_p g, e_n g) (ablocks B ly S)).
{ intros ly S hs Hh Hn0. destruct Hh as (Hperm & _).
  pose proof HPRE as (_ & _ & _ & _ & Hdisj & _).
  destruct Hdisj as [(Hz & _) | (_ & Hin0)]; [clear - Hz Hn0; lia|].
  apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. exact Hin0. }
assert (Hbl0 : hblocks B g (e_ly g) (e_S g) [])
  by (split; [cbn [app]; apply Permutation_refl | apply Forall_nil]).
assert (HPB : 0 < e_n g -> 4096 <= e_p g /\ e_p g + e_n g <= alloc_ceiling).
{ intros Hn0. pose proof HPRE as (HFN0 & _). pose proof HFN0 as (HAR0 & _).
  destruct (al_blocks SEGS B LAWS (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) (e_p g) (e_n g) HAR0
    (HINP (e_ly g) (e_S g) [] Hbl0 Hn0)) as (_ & Hp4 & Hpc & _ & _).
  assert (Erq : req_size (e_n g) = e_n g)
    by (unfold req_size; destruct (Z.eqb_spec (e_n g) 0) as [Hz | Hz];
        [clear - Hn0 Hz; lia | reflexivity]).
  rewrite Erq in Hpc. split; [exact Hp4 | exact Hpc]. }
assert (HAREA : forall a, si_area g pos mf a -> 0 <= a < 2 ^ 64).
{ intros a Ha. unfold si_area in Ha. destruct Ha as [Ha | [Ha | [Ha | Ha]]].
  - clear - Ha Hmf0 Hmfb Has C1 Hsp0r. lia.
  - clear - Ha HSF0 HSF1 C1. lia.
  - clear - Ha Hsh C1. lia.
  - destruct (HPB ltac:(clear - Ha; lia)) as (Hp4 & Hpc). clear - Ha Hp4 Hpc C1. lia. }
assert (HNA : forall a, mf + 152 <= a < mf + 160 -> ~ si_area g pos mf a).
{ intros a Ha Hs. unfold si_area in Hs. destruct Hs as [Hs | [Hs | [Hs | Hs]]].
  - clear - Ha Hs. lia.
  - clear - Ha Hs HSF1 Hmf0 Has C1. lia.
  - clear - Ha Hs Hsh Hmf0 Has C1. lia.
  - destruct (HPB ltac:(clear - Hs; lia)) as (Hp4 & Hpc). clear - Ha Hs Hpc Hmf0 Has C1. lia. }
assert (KEEPR : forall (E : env) rs (W : world SEGS) (m m' : word -> option byte),
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) ->
     base_val E b + wlo <= a < base_val E b + whi -> ~ si_area g pos mf a) ->
  forall a, si_area g pos mf a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a).
{ intros E rs W m m' HFx HW a Ha.
  apply (kept_of_frame E rs (w_H W) m m' (fun x => ~ si_area g pos mf x) HFx);
    [ exact HW | exact (HAREA a Ha) | intros Hn; exact (Hn Ha) ]. }
assert (HSF8 : SFa g pos mod 8 = 0) by (clear - HSF64; Z.div_mod_to_equations; lia).
assert (Hnlen : e_n g = Z.of_nat (length (e_pl g))) by (pose proof HPRE as (_ & _ & _ & _ & _ & Hl & _); exact Hl).
assert (HVM : forall (W W' : world SEGS) m m',
  (forall a, si_area g pos mf a -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  si_vals g pos mf W m -> si_vals g pos mf W' m').
{ intros Wa Wb ma mb HK Hv.
  exact (si_vals_moved g pos mf Wa ma Wb mb ltac:(clear - Hmfb; lia) HSF8 Hnlen HK Hv). }
assert (HCALLK : forall ly S (Wa : world SEGS) ma mda kk ly' S' (Wq : world SEGS) mb mdb STK1 kk1 hs hs',
  AJ g pos ly S Wa ma mda kk -> frames S = [(4, pos)] -> hblocks B g ly S hs ->
  hblocks B g ly' S' hs' ->
  ajournal SEGS B STK1 mf [] ly S Wa ma mda [] ly' S' Wq mb mdb kk1 -> 0 <= STK1 ->
  forall a, si_area g pos mf a -> aview SEGS (w_H Wq) mb a = aview SEGS (w_H Wa) ma a).
{ intros ly S Wa ma mda kk ly' S' Wq mb mdb STK1 kk1 hs hs' HJa Hfa Hha Hhb HJ1 HST1.
  apply (si_area_kept_call g pos mf ly S Wa ma mda kk ly' S' Wq mb mdb STK1 mf [] kk1
    HJa Hfa HJ1 Hmfb ltac:(clear; lia) HST1).
  - intros Hn0. split; [exact (HINP ly S hs Hha Hn0) | exact (HINP ly' S' hs' Hhb Hn0)].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
remember (Eimg (Ereg regs2 (@nil word))) as E0 eqn:HE0.
assert (EE : forall (nn : nat) (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = getr regs2 r)
  by (intros nn r Hn; rewrite HE0; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HEI : img_env VAL A_LIM E0) by (rewrite HE0; apply Eimg_env).
assert (HS : st_ok_pi SEGS VAL E0 (si_ss0 0x12e8)
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x12e8)) mem2 (seg_rom SEGS))))
  by (rewrite HE0; apply si_entry0).
unfold cfg_at. change (w64 (BASE + 0x12e8)) with (Z_to_bv 64 (BASE + 0x12e8)).
paj_run_shc RUNP RUNC HS HJ.
{ apply awr_ok_nil. }
assert (PRa : aregs_preserved regs2 (ms_regs ms)).
{ exact (aregs_preserved_of_st_ok SEGS (w_H W2) _ _ _ regs2 (@nil word) HS
    ltac:(rewrite HE0; apply si_agree) ltac:(vm_compute; reflexivity)). }
assert (K0 : forall a, si_area g pos mf a -> aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ apply (KEEPR _ _ W2 mem2 (ms_mem ms) HFr).
  intros bb wlo whi aa Hin Hr. cbn [si_ss0 ss_mem windows map] in Hin. destruct Hin. }
assert (VK0 : forall a nn v, 0 <= a -> a + Z.of_nat nn <= 2 ^ 64 ->
  val_mem SEGS (rd W2 mem2) a nn v -> val_mem SEGS (rd W2 (ms_mem ms)) a nn v).
{ intros a nn v Ha Hb Hv. apply (val_mem_kept SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms) a nn v); [|exact Hv].
  intros i Hi. apply (kept_of_frame E0 (ss_mem (si_ss0 0x12e8)) (w_H W2)
    mem2 (ms_mem ms) (fun _ => False) HFr);
  [ intros bb wlo whi aa Hin Hr; cbn [si_ss0 ss_mem windows map] in Hin; destruct Hin
  | clear - Ha Hb Hi; lia | intros HF0; exact HF0 ]. }
assert (HV0 : si_vals g pos mf W2 (ms_mem ms)) by exact (HVM W2 W2 mem2 (ms_mem ms) K0 HV).
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
rewrite (EE 2%nat 2%bv eq_refl), Rsp in Q2.
rewrite (EE 3%nat 3%bv eq_refl), Rgp in Q3.
rewrite (EE 4%nat 4%bv eq_refl), Rtp in Q4.
rewrite (EE 8%nat 8%bv eq_refl), Rs0 in Q8.
rewrite (EE 10%nat 10%bv eq_refl), Ra0 in Q10.
pmkst HS. rewrite (PSIG IB_buf_of AF_buf_of eq_refl).
eapply SRr_bind.
{ apply (si_bufcall g pos mf W2 ly2 S2 (ms_regs ms) (ms_mem ms) _ (4 * Z.of_nat (m_nrec g) + 4)
    0x12ec (SlotModel.t_cap_name (e_pl g)) []).
  - exact HJ.
  - exact HPRE.
  - exact Hfrs.
  - clear - Hkv. lia.
  - clear - Hkv HEVv. lia.
  - exact MLE.
  - exact MOK.
  - exact Hmfb.
  - exact Hmf32.
  - exact Q2.
  - exact Q8.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - clear. lia.
  - reflexivity.
  - unfold CTX_BUF_OF, BUF_OF_RAS; cbn [map app In];
    right; right; right; right; right; right; right; right; right; left; reflexivity.
  - unfold CTX_BUF_OF, BUF_OF_RAS; cbn [map app In];
    right; right; right; left; reflexivity.
  - exact Q10.
  - clear - Hcn. lia.
  - exact Hbl.
  - cbn [bsum fold_right]. clear - Hcn. lia.
  - apply VK0; [clear - Hsp0lo; lia | clear - Hsp0r; lia | exact Vra].
  - apply VK0; [clear - Hsp0lo; lia | clear - Hsp0r; lia | exact Vs0]. }
cbv beta.
intros Wb cb Hwb (ly3 & S3 & regs3 & mem3 & md3 & nm & -> & HJ3 & HJc1 & HP1 & Rnm & Hnm4 & Hnm64 &
  Hfrs3 & Hbl3 & MLE3 & MOK3).
cbn [app] in Hbl3.
assert (PR3 : aregs_preserved regs2 regs3) by exact (si_prtrans _ _ _ PRa HP1).
assert (K1 : forall a, si_area g pos mf a -> aview SEGS (w_H Wb) mem3 a = aview SEGS (w_H W2) (ms_mem ms) a).
{ apply (HCALLK ly2 S2 W2 (ms_mem ms) _ (4 * Z.of_nat (m_nrec g) + 4) ly3 S3 Wb mem3 md3
    buf_of.BUF_OF_STK 1 [] _ HJ Hfrs Hbl Hbl3 HJc1
    ltac:(clear; assert (HH : buf_of.BUF_OF_STK = 16400) by reflexivity; lia)). }
assert (HV3 : si_vals g pos mf Wb mem3) by exact (HVM W2 Wb (ms_mem ms) mem3 K1 HV0).
assert (R9b : getr regs3 9 = w64 mf)
  by (rewrite (si_pres_z regs2 regs3 9 9%bv PR3 ltac:(unfold acallee_saved; lia) eq_refl); exact Rs1).
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
clear HS HEI HF HFr HG EE HE0.
remember (Eimg (Ereg regs3 (@nil word))) as E1 eqn:HE1.
assert (EE : forall (nn : nat) (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E1 nn = getr regs3 r)
  by (intros nn r Hn; rewrite HE1; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9b : bv_unsigned (ew E1 9) = mf)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9b; unfold w64; apply unsigned_lit_small; clear - Hmfr; lia).
assert (HEI : img_env VAL A_LIM E1) by (rewrite HE1; apply Eimg_env).
assert (HS : st_ok_pi SEGS VAL E1 (si_ss1 0x12ec)
  (restrict (w_H Wb) (mkst regs3 (Z_to_bv 64 (BASE + 0x12ec)) mem3 (seg_rom SEGS)))).
{ rewrite HE1. apply (si_entry1 Wb regs3 mem3 0x12ec mf R9b ltac:(clear - Hmfr; lia)
    ltac:(clear - Hmfb H47; lia)).
  intros a Ha. apply Hpres3. clear - Ha Hmfb HSTK' Has. lia. }
paj_run_shc RUNP RUNC HS HJ3.
{ eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (mf - e_sp0 g));
  [ reflexivity | rewrite U9b; clear; lia
  | cbn [si_mfr YP09.r_wlo]; clear - Hmfb HSTK' Has; lia
  | cbn [si_mfr YP09.r_whi]; clear - Hmfb; lia
  | apply awr_ok_nil ]. }
assert (VKR : forall (E : env) rs (W : world SEGS) (m m' : word -> option byte) a nn v,
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall b wlo whi x, In (b, wlo, whi) (windows rs) ->
     base_val E b + wlo <= x < base_val E b + whi -> ~ (a <= x < a + Z.of_nat nn)) ->
  0 <= a -> a + Z.of_nat nn <= 2 ^ 64 ->
  val_mem SEGS (rd W m) a nn v -> val_mem SEGS (rd W m') a nn v).
{ intros E rs W m m' a nn v HFx HW Ha Hb Hv.
  apply (val_mem_kept SEGS (w_H W) (w_H W) m m' a nn v); [|exact Hv].
  intros i Hi. apply (kept_of_frame E rs (w_H W) m m' (fun x => ~ (a <= x < a + Z.of_nat nn)) HFx);
  [ exact HW | clear - Ha Hb Hi; lia | intros Hn; apply Hn; clear - Hi; lia ]. }
assert (WIN1 : forall b wlo whi x, In (b, wlo, whi) (windows (ss_mem (si_ss1 0x12ec))) ->
  base_val E1 b + wlo <= x < base_val E1 b + whi -> mf + 152 <= x < mf + 160).
{ intros bb wlo whi x Hin Hr.
  cbn [si_ss1 si_mfr ss_mem windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
  destruct Hin as [Eq | []]. injection Eq as <- <- <-.
  cbn [base_val] in Hr. rewrite U9b in Hr. clear - Hr. lia. }
assert (PRb : aregs_preserved regs3 (ms_regs ms0)).
{ exact (aregs_preserved_of_st_ok SEGS (w_H Wb) _ _ _ regs3 (@nil word) HS
    ltac:(rewrite HE1; apply si_agree) ltac:(vm_compute; reflexivity)). }
assert (K2 : forall a, si_area g pos mf a ->
  aview SEGS (w_H Wb) (ms_mem ms0) a = aview SEGS (w_H Wb) mem3 a).
{ apply (KEEPR _ _ Wb mem3 (ms_mem ms0) HFr).
  intros bb wlo whi x Hin Hr. apply HNA. exact (WIN1 bb wlo whi x Hin Hr). }
assert (HV4 : si_vals g pos mf Wb (ms_mem ms0)) by exact (HVM Wb Wb mem3 (ms_mem ms0) K2 HV3).
pose proof HV4 as (_ & _ & _ & _ & Vra4 & Vs04 & _).
assert (R2b : getr regs3 2 = w64 mf)
  by (rewrite (si_pres_z regs2 regs3 2 2%bv PR3 ltac:(unfold acallee_saved; lia) eq_refl); exact Rsp).
assert (R3b : getr regs3 3 = w64 (as_gp B))
  by (rewrite (si_pres_z regs2 regs3 3 3%bv PR3 ltac:(unfold acallee_saved; lia) eq_refl); exact Rgp).
assert (R4b : getr regs3 4 = w64 (as_tp B))
  by (rewrite (si_pres_z regs2 regs3 4 4%bv PR3 ltac:(unfold acallee_saved; lia) eq_refl); exact Rtp).
assert (R8b : getr regs3 8 = w64 (e_sp0 g))
  by (rewrite (si_pres_z regs2 regs3 8 8%bv PR3 ltac:(unfold acallee_saved; lia) eq_refl); exact Rs0).
assert (R19b : getr regs3 19 = w64 (SlotModel.t_cap_tok (e_pl g)))
  by (rewrite (si_pres_z regs2 regs3 19 19%bv PR3 ltac:(unfold acallee_saved; lia) eq_refl); exact R19).
assert (V152 : val_mem SEGS (rd Wb (ms_mem ms0)) (mf + 152) 8 nm).
{ exact (si_chunkv E1 _ (w_H Wb) ms0 0%nat
    (YP09.mkRegion (Some 9%nat) 152 160 152 160 [YP09.mkChunk 152 (CVal 8 (SOff 10 0))])
    9%nat mf 152 8%N (SOff 10 0) nm HS ltac:(vm_compute; reflexivity) eq_refl U9b
    ltac:(cbn [YP09.r_chunks In]; left; reflexivity)
    ltac:(cbn [sv_denot]; rewrite (EE 10%nat 10%bv eq_refl), Rnm; unfold w64;
          rewrite Z.add_0_r, unsigned_lit_small by (clear - Hnm4 Hnm64; lia); reflexivity)
    ltac:(cbn [Z.of_N]; clear - Hnm4 Hnm64; lia) ltac:(cbn [Z.of_N]; clear; lia)). }
assert (V144b : val_mem SEGS (rd Wb (ms_mem ms0)) (mf + 144) 8 (SlotModel.t_cap_name (e_pl g))).
{ apply (VKR E1 (ss_mem (si_ss1 0x12ec)) Wb mem3 (ms_mem ms0) (mf + 144) 8%nat _ HFr);
  [ intros bb wlo whi x Hin Hr; pose proof (WIN1 bb wlo whi x Hin Hr); clear - H; cbn; lia
  | clear - Hmfr; lia | clear - Hmfb H47; cbn; lia
  | apply (si_vm_above W2 Wb (ms_mem ms) ly2 S2 _ ly3 S3 mem3 md3 buf_of.BUF_OF_STK mf [] 1
      (mf + 144) 8%nat _ HJc1 ltac:(clear - Hmf0 Has; lia) ltac:(clear - Hmfb H47; cbn; lia)
      ltac:(clear; lia));
    apply VK0; [clear - Hmfr; lia | clear - Hmfb H47; cbn; lia | exact V144] ]. }
assert (V184b : val_mem SEGS (rd Wb (ms_mem ms0)) (mf + 184) 8 (SFa g pos + V_id)).
{ apply (VKR E1 (ss_mem (si_ss1 0x12ec)) Wb mem3 (ms_mem ms0) (mf + 184) 8%nat _ HFr);
  [ intros bb wlo whi x Hin Hr; pose proof (WIN1 bb wlo whi x Hin Hr); clear - H; cbn; lia
  | clear - Hmfr; lia | clear - Hmfb H47; cbn; lia
  | apply (si_vm_above W2 Wb (ms_mem ms) ly2 S2 _ ly3 S3 mem3 md3 buf_of.BUF_OF_STK mf [] 1
      (mf + 184) 8%nat _ HJc1 ltac:(clear - Hmf0 Has; lia) ltac:(clear - Hmfb H47; cbn; lia)
      ltac:(clear; lia));
    apply VK0; [clear - Hmfr; lia | clear - Hmfb H47; cbn; lia | exact V184] ]. }
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3.
prreg HS (4%bv : bv 5) T4. prreg HS (8%bv : bv 5) T8. prreg HS (10%bv : bv 5) T10.
rewrite (EE 2%nat 2%bv eq_refl), R2b in T2.
rewrite (EE 3%nat 3%bv eq_refl), R3b in T3.
rewrite (EE 4%nat 4%bv eq_refl), R4b in T4.
rewrite (EE 8%nat 8%bv eq_refl), R8b in T8.
rewrite (EE 19%nat 19%bv eq_refl), R19b in T10.
pmkst HS. rewrite (PSIG IB_buf_of AF_buf_of eq_refl).
eapply SRr_bind.
{ apply (si_bufcall g pos mf Wb ly3 S3 (ms_regs ms0) (ms_mem ms0) _ (4 * Z.of_nat (m_nrec g) + 4 + 1)
    0x12f8 (SlotModel.t_cap_tok (e_pl g)) [(nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1)]).
  - exact HJ3.
  - exact HPRE.
  - exact Hfrs3.
  - clear - Hkv. lia.
  - clear - Hkv HEVv. lia.
  - exact MLE3.
  - exact MOK3.
  - exact Hmfb.
  - exact Hmf32.
  - exact T2.
  - exact T8.
  - exact T3.
  - exact T4.
  - exact T1.
  - clear. lia.
  - reflexivity.
  - unfold CTX_BUF_OF, BUF_OF_RAS; cbn [map app In];
    right; right; right; right; right; right; right; right; right; right; left; reflexivity.
  - unfold CTX_BUF_OF, BUF_OF_RAS; cbn [map app In];
    right; right; right; right; left; reflexivity.
  - exact T10.
  - clear - Hct. lia.
  - exact Hbl3.
  - cbn [bsum fold_right snd]. clear - Hcn Hct. lia.
  - exact Vra4.
  - exact Vs04. }
cbv beta.
intros Wc cc Hwc (ly4 & S4 & regs4 & mem4 & md4 & tk & -> & HJ4 & HJc2 & HP2 & Rtk & Htk4 & Htk64 &
  Hfrs4 & Hbl4 & MLE4 & MOK4).
cbn [app] in Hbl4.
assert (PR4 : aregs_preserved regs2 regs4) by exact (si_prtrans _ _ _ (si_prtrans _ _ _ PR3 PRb) HP2).
assert (K3 : forall a, si_area g pos mf a -> aview SEGS (w_H Wc) mem4 a = aview SEGS (w_H Wb) (ms_mem ms0) a).
{ apply (HCALLK ly3 S3 Wb (ms_mem ms0) _ (4 * Z.of_nat (m_nrec g) + 4 + 1) ly4 S4 Wc mem4 md4
    buf_of.BUF_OF_STK 1 _ _ HJ3 Hfrs3 Hbl3 Hbl4 HJc2
    ltac:(clear; assert (HH : buf_of.BUF_OF_STK = 16400) by reflexivity; lia)). }
assert (HV5 : si_vals g pos mf Wc mem4) by exact (HVM Wb Wc (ms_mem ms0) mem4 K3 HV4).
assert (V152c : val_mem SEGS (rd Wc mem4) (mf + 152) 8 nm)
  by exact (si_vm_above Wb Wc (ms_mem ms0) ly3 S3 _ ly4 S4 mem4 md4 buf_of.BUF_OF_STK mf [] 1
    (mf + 152) 8%nat nm HJc2 ltac:(clear - Hmf0 Has; lia) ltac:(clear - Hmfb H47; cbn; lia)
    ltac:(clear; lia) V152).
assert (V144c : val_mem SEGS (rd Wc mem4) (mf + 144) 8 (SlotModel.t_cap_name (e_pl g)))
  by exact (si_vm_above Wb Wc (ms_mem ms0) ly3 S3 _ ly4 S4 mem4 md4 buf_of.BUF_OF_STK mf [] 1
    (mf + 144) 8%nat _ HJc2 ltac:(clear - Hmf0 Has; lia) ltac:(clear - Hmfb H47; cbn; lia)
    ltac:(clear; lia) V144b).
assert (V184c : val_mem SEGS (rd Wc mem4) (mf + 184) 8 (SFa g pos + V_id))
  by exact (si_vm_above Wb Wc (ms_mem ms0) ly3 S3 _ ly4 S4 mem4 md4 buf_of.BUF_OF_STK mf [] 1
    (mf + 184) 8%nat _ HJc2 ltac:(clear - Hmf0 Has; lia) ltac:(clear - Hmfb H47; cbn; lia)
    ltac:(clear; lia) V184b).
clear HS HEI HF HFr HG EE HE1 WIN1.
remember (Eimg (Ereg regs4 (@nil word))) as E2 eqn:HE2.
assert (EE : forall (nn : nat) (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E2 nn = getr regs4 r)
  by (intros nn r Hn; rewrite HE2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HEI : img_env VAL A_LIM E2) by (rewrite HE2; apply Eimg_env).
assert (HS : st_ok_pi SEGS VAL E2 (si_ss0 0x12f8)
  (restrict (w_H Wc) (mkst regs4 (Z_to_bv 64 (BASE + 0x12f8)) mem4 (seg_rom SEGS))))
  by (rewrite HE2; apply si_entry0).
paj_run_shc RUNP RUNC HS HJ4.
{ apply awr_ok_nil. }
assert (KP3 : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 22%bv; 23%bv; 27%bv] ->
  getr (ms_regs ms1) r = getr regs4 r).
{ intros r Hr.
  exact (regs_kept_of_st_ok SEGS E2 _ _ regs4 (@nil word)
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 22%bv; 23%bv; 27%bv] HS
    ltac:(rewrite HE2; apply si_agree) ltac:(vm_compute; reflexivity) r Hr). }
assert (G4 : forall (r : bv 5) (z : Z), acallee_saved z -> bv_unsigned r = z ->
  In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 22%bv; 23%bv; 27%bv] ->
  getr (ms_regs ms1) r = getr regs2 r).
{ intros r z Hz Hr Hin. rewrite (KP3 r Hin). exact (si_pres_z _ _ z r PR4 Hz Hr). }
assert (K4 : forall a, si_area g pos mf a -> aview SEGS (w_H Wc) (ms_mem ms1) a = aview SEGS (w_H Wc) mem4 a).
{ apply (KEEPR _ _ Wc mem4 (ms_mem ms1) HFr).
  intros bb wlo whi aa Hin Hr. cbn [si_ss0 ss_mem windows map] in Hin. destruct Hin. }
assert (HV6 : si_vals g pos mf Wc (ms_mem ms1)) by exact (HVM Wc Wc mem4 (ms_mem ms1) K4 HV5).
pose proof HV6 as (_ & _ & _ & _ & Vra6 & Vs06 & _).
assert (VK3 : forall a nn v, 0 <= a -> a + Z.of_nat nn <= 2 ^ 64 ->
  val_mem SEGS (rd Wc mem4) a nn v -> val_mem SEGS (rd Wc (ms_mem ms1)) a nn v).
{ intros a nn v Ha Hb Hv. apply (VKR E2 (ss_mem (si_ss0 0x12f8)) Wc mem4 (ms_mem ms1) a nn v HFr);
  [ intros bb wlo whi aa Hin Hr; cbn [si_ss0 ss_mem windows map] in Hin; destruct Hin
  | exact Ha | exact Hb | exact Hv ]. }
prreg HS (1%bv : bv 5) U1. prreg HS (10%bv : bv 5) U10. prreg HS (21%bv : bv 5) U21.
rewrite (EE 22%nat 22%bv eq_refl),
  (si_pres_z regs2 regs4 22 22%bv PR4 ltac:(unfold acallee_saved; lia) eq_refl), R22 in U10.
rewrite (EE 10%nat 10%bv eq_refl), Rtk in U21.
assert (U2 : getr (ms_regs ms1) 2 = w64 mf)
  by (rewrite (G4 2%bv 2 ltac:(unfold acallee_saved; lia) eq_refl
        ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact Rsp).
assert (U3 : getr (ms_regs ms1) 3 = w64 (as_gp B))
  by (rewrite (G4 3%bv 3 ltac:(unfold acallee_saved; lia) eq_refl
        ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact Rgp).
assert (U4 : getr (ms_regs ms1) 4 = w64 (as_tp B))
  by (rewrite (G4 4%bv 4 ltac:(unfold acallee_saved; lia) eq_refl
        ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact Rtp).
assert (U8 : getr (ms_regs ms1) 8 = w64 (e_sp0 g))
  by (rewrite (G4 8%bv 8 ltac:(unfold acallee_saved; lia) eq_refl
        ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact Rs0).
pmkst HS. rewrite (PSIG IB_buf_of AF_buf_of eq_refl).
eapply SRr_bind.
{ apply (si_bufcall g pos mf Wc ly4 S4 (ms_regs ms1) (ms_mem ms1) _ (4 * Z.of_nat (m_nrec g) + 4 + 1 + 1)
    0x1304 (SlotModel.t_cap_disp (e_pl g))
    [(nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1); (tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1)]).
  - exact HJ4.
  - exact HPRE.
  - exact Hfrs4.
  - clear - Hkv. lia.
  - clear - Hkv HEVv. lia.
  - exact MLE4.
  - exact MOK4.
  - exact Hmfb.
  - exact Hmf32.
  - exact U2.
  - exact U8.
  - exact U3.
  - exact U4.
  - exact U1.
  - clear. lia.
  - reflexivity.
  - unfold CTX_BUF_OF, BUF_OF_RAS; cbn [map app In];
    right; right; right; right; right; right; right; right; right; right; right; left; reflexivity.
  - unfold CTX_BUF_OF, BUF_OF_RAS; cbn [map app In];
    right; right; right; right; right; left; reflexivity.
  - exact U10.
  - clear - Hcd. lia.
  - exact Hbl4.
  - cbn [bsum fold_right snd]. clear - Hcn Hct Hcd. lia.
  - exact Vra6.
  - exact Vs06. }
cbv beta.
intros Wd cd Hwd (ly5 & S5 & regs5 & mem5 & md5 & dp & -> & HJ5 & HJc3 & HP3 & Rdp & Hdp4 & Hdp64 &
  Hfrs5 & Hbl5 & MLE5 & MOK5).
cbn [app] in Hbl5.
assert (K5 : forall a, si_area g pos mf a -> aview SEGS (w_H Wd) mem5 a = aview SEGS (w_H Wc) (ms_mem ms1) a).
{ apply (HCALLK ly4 S4 Wc (ms_mem ms1) _ (4 * Z.of_nat (m_nrec g) + 4 + 1 + 1) ly5 S5 Wd mem5 md5
    buf_of.BUF_OF_STK 1 _ _ HJ4 Hfrs4 Hbl4 Hbl5 HJc3
    ltac:(clear; assert (HH : buf_of.BUF_OF_STK = 16400) by reflexivity; lia)). }
assert (HV7 : si_vals g pos mf Wd mem5) by exact (HVM Wc Wd (ms_mem ms1) mem5 K5 HV6).
assert (FIN : forall (r : bv 5) (z : Z), acallee_saved z -> bv_unsigned r = z ->
  In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 22%bv; 23%bv; 27%bv] ->
  getr regs5 r = getr regs2 r).
{ intros r z Hz Hr Hin. rewrite (si_pres_z _ _ z r HP3 Hz Hr). exact (G4 r z Hz Hr Hin). }
assert (VD : forall a v, mf <= a -> a + 8 <= e_sp0 g ->
  val_mem SEGS (rd Wc mem4) a 8 v -> val_mem SEGS (rd Wd mem5) a 8 v).
{ intros a v Ha Hb Hv.
  apply (si_vm_above Wc Wd (ms_mem ms1) ly4 S4 _ ly5 S5 mem5 md5 buf_of.BUF_OF_STK mf [] 1
    a 8%nat v HJc3 ltac:(clear - Ha Hmf0 Has; lia) ltac:(clear - Hb Hsp0r; cbn; lia) Ha).
  apply VK3; [clear - Ha Hmfr; lia | clear - Hb Hsp0r; cbn; lia | exact Hv]. }
assert (Ek : 4 * Z.of_nat (m_nrec g) + 4 + 1 + 1 + 1 = 4 * Z.of_nat (m_nrec g) + 7) by (clear; lia).
rewrite Ek in HJ5, MLE5, MOK5.
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5) as (Efds & Efs).
unfold sh_reg in Rs7.
apply SRr_ret.
exists nm, tk, dp.
unfold si_C3, acut.
exists ly5, S5, regs5, mem5, md5.
split; [reflexivity|].
split; [exact HJ5|].
split; [exact Hfrs5|].
split; [clear - Hkv HEVv; lia|].
split; [exact MLE5|].
split; [exact MOK5|].
split.
{ apply (si_ecommon g pos mf ly5 S5 Wd regs5 mem5 md5).
  - rewrite (FIN 2%bv 2 ltac:(unfold acallee_saved; lia) eq_refl
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). exact Rsp.
  - rewrite (FIN 9%bv 9 ltac:(unfold acallee_saved; lia) eq_refl
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). exact Rs1.
  - rewrite (FIN 8%bv 8 ltac:(unfold acallee_saved; lia) eq_refl
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). exact Rs0.
  - exact Hmfb.
  - exact Hmf32.
  - rewrite (FIN 3%bv 3 ltac:(unfold acallee_saved; lia) eq_refl
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). exact Rgp.
  - rewrite (FIN 4%bv 4 ltac:(unfold acallee_saved; lia) eq_refl
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). exact Rtp.
  - exact HV7.
  - exact HPRE.
  - intros fd. rewrite Efds. reflexivity.
  - exact Efs. }
split; [exact HV7|].
split.
{ unfold sh_reg. rewrite (FIN 23%bv 23 ltac:(unfold acallee_saved; lia) eq_refl
    ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). exact Rs7. }
split; [exact Hbl5|].
split; [exact Rdp|].
split; [rewrite (FIN 18%bv 18 ltac:(unfold acallee_saved; lia) eq_refl
    ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact R18|].
split; [rewrite (FIN 19%bv 19 ltac:(unfold acallee_saved; lia) eq_refl
    ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact R19|].
split; [rewrite (FIN 20%bv 20 ltac:(unfold acallee_saved; lia) eq_refl
    ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact R20|].
split; [rewrite (si_pres_z _ _ 21 21%bv HP3 ltac:(unfold acallee_saved; lia) eq_refl); exact U21|].
split; [rewrite (FIN 22%bv 22 ltac:(unfold acallee_saved; lia) eq_refl
    ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact R22|].
split; [rewrite (FIN 27%bv 27 ltac:(unfold acallee_saved; lia) eq_refl
    ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact R27|].
split; [exact (VD (mf + 184) _ ltac:(clear; lia) ltac:(clear - Hmfb; lia) V184c)|].
split; [exact (VD (mf + 152) _ ltac:(clear; lia) ltac:(clear - Hmfb; lia) V152c)|].
exact (VD (mf + 144) _ ltac:(clear; lia) ltac:(clear - Hmfb; lia) V144c).
Qed.

Check (si_L_bufs : forall g pos mf W2 c2, si_C2 g pos mf W2 c2 ->
  SRr SEGS W2 c2 (fun W3 c3 => exists nm tk dp, si_C3 g pos mf nm tk dp W3 c3)).

(* ---- the composition: the five steps chained from inv_H_end to inv_I_end -------------------------------- *)
Lemma si_compose :
  (forall g pos mf W2 c2, INV_H g pos mf W2 c2 -> SRr SEGS W2 c2 (si_C1 g pos mf)) ->
  (forall g pos mf W2 c2, si_C1 g pos mf W2 c2 -> SRr SEGS W2 c2 (si_C2 g pos mf)) ->
  (forall g pos mf W2 c2, si_C2 g pos mf W2 c2 ->
     SRr SEGS W2 c2 (fun W3 c3 => exists nm tk dp, si_C3 g pos mf nm tk dp W3 c3)) ->
  (forall g pos mf nm tk dp W2 c2, si_C3 g pos mf nm tk dp W2 c2 -> SRr SEGS W2 c2 (si_C4 g pos mf nm tk dp)) ->
  (forall g pos mf nm tk dp W2 c2, si_C4 g pos mf nm tk dp W2 c2 -> SRr SEGS W2 c2 (INV_I g pos mf nm tk dp)) ->
  SEG_I.
Proof.
intros Lfam Lstem Lbufs Lref Lreal.
unfold seg_I_stmt. intros g pos mf W2 c2 Hstart.
eapply SRr_bind; [exact (Lfam g pos mf W2 c2 Hstart)|].
cbv beta. intros W3 c3 _ H1.
eapply SRr_bind; [exact (Lstem g pos mf W3 c3 H1)|].
cbv beta. intros W4 c4 _ H2.
eapply SRr_bind; [exact (Lbufs g pos mf W4 c4 H2)|].
cbv beta. intros W5 c5 _ (nm & tk & dp & H3).
eapply SRr_bind; [exact (Lref g pos mf nm tk dp W5 c5 H3)|].
cbv beta. intros W6 c6 _ H4.
eapply SRr_mono; [exact (Lreal g pos mf nm tk dp W6 c6 H4)|].
cbv beta. intros W7 c7 _ H5. exists nm, tk, dp. exact H5.
Qed.

(* ---- the segment ---------------------------------------------------------------------------------------- *)
Lemma seg_I : seg_I_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
asink_none ameta_inv arodata_okS.
Proof. exact (si_compose si_L_fam si_L_stem si_L_bufs si_L_ref si_L_real). Qed.

Check (seg_I : seg_I_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
asink_none ameta_inv arodata_okS).
End c.
End b.
End a.

Print Assumptions seg_I.
