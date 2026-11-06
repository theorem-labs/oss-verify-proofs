(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:2300-2306, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_I.v, with its module paths, module names, addresses and numbers changed; 2106 of its 2322 lines of code are new or changed and 2945 lines of the source are left out. *)
(* Segment I of LLVMFuzzerTestOneInput's ASan walk: the family, its stem, the three output buffers and the two
   reac_box_name calls, 0x81878..0x81974 (63 slots). seg_I of lib/A/Prog/LLVMFuzzerTestOneInput_inv.v: from
   inv_H_end to inv_I_end.

   The code (BASE + 0x116c .. BASE + 0x1268):
     0x81878 bltz a1,0x8188c          a1 = t_fam_raw << 56: a family byte of 128 or more is taken as it is
     0x8187c ld a0,184(s1)            &id
     0x81880 jal reac_box_family_of   the family of the decoded identity (FAM of the plain model)
     0x81884 mv s9,a0; j 0x81890
     0x8188c andi s9,s7,127           the family byte's low 7 bits
     0x81890 ld s2,128(s1)            said = &id.model_name
     0x81898 jal reac_box_family_stem  0x8189c beqz a0 -> abort: never taken (the stem is not null)
     0x818a0 .. 0x818b4               s7 = id.has_model_name, mf+152 := cap_name, a0 = max cap_name 1
     0x818b8 jal malloc               nm, stored at mf+184; 0x818c0 beqz -> abort: not taken
     0x818d0 jal malloc               tk (max cap_tok 1); 0x818d4 s10 = t_out
     0x818e8 jal malloc               dp (max cap_disp 1); 0x818ec s8 = t_in
     0x818f8 .. 0x81900               said := 0 when id.has_model_name = 0
     0x81904 .. 0x81930               16 bytes of stack arguments (dp, cap_disp), reac_box_name(fam, said, 8, 8,
                                      NULL, 8, tk, cap_tok): it refuses (a0 = -1; 0x8193c bne -> abort not taken)
     0x81940 .. 0x8196c               the same stack arguments, reac_box_name(fam, said, t_in, t_out, nm, cap_name,
                                      tk, cap_tok)
     0x81970 addi sp,sp,16            the boundary is 0x81974, whose `mv s11,a0` has not run.
   Every run between two calls is a plain run (no checked access). The walk is split at 0x81890, where the two
   family paths meet (I_head, then I_tail). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_Icut LLVMFuzzerTestOneInput_Irbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require
reac_box_family_of reac_box_family_stem reac_box_name.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require
reac_box_name_c reac_box_family_of_c SlotModel RcIdentModel IdentSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off; this file's address arithmetic needs it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the plain model's facts the walk needs (SlotModel, RcIdentModel, IdentSpec, used as they are) ---------- *)
(* The value reac_box_name's model takes for the name the harness passes (said and its string), and the
   relation of reac_box_name's model to the harness's expected strings. These are the address-free lemmas of the
   released plain segment lib/Prog/Seg/G07.v (its g7 lemmas), restated here so this file does not load the plain walk's
   tactic layer. *)
Module IM.
Import SlotModel RcIdentModel IdentSpec.

Definition sdZ (inp : list byte) : list Z := if n_said inp then map bz (name_str (idT inp)) else [].

Lemma nth_first' : forall (A : Type) (l : list A) k i (d : A), (i < k)%nat -> nth i (firstn k l) d = nth i l d.
Proof.
intros A l. induction l as [|x l IH]; intros [|k] [|i] d H; cbn; try reflexivity; try lia. apply IH. lia.
Qed.

Lemma nth_skipn' : forall (A : Type) (l : list A) j i d, nth i (skipn j l) d = nth (j + i) l d.
Proof.
intros A l j. revert l. induction j as [|j IH]; intros l i d; [reflexivity|].
destruct l as [|x l]; cbn [skipn]; [destruct i; reflexivity|]. cbn [Nat.add nth]. apply IH.
Qed.

Lemma leq_eq : forall a b, bn_leq a b = true -> a = b.
Proof.
induction a as [|x a IH]; intros [|y b] H; cbn [bn_leq] in H; try discriminate; [reflexivity|].
apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. subst y. f_equal. apply IH. exact H2.
Qed.

Lemma leq_map : forall a b, bn_leq (map bz a) (map bz b) = bytes_eqb a b.
Proof.
induction a as [|x a IH]; intros [|y b]; cbn [map bn_leq bytes_eqb]; try reflexivity.
rewrite IH. reflexivity.
Qed.

Lemma skipn_map' : forall (f : byte -> Z) n l, skipn n (map f l) = map f (skipn n l).
Proof. intros f n. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. apply IH. Qed.

Lemma dec_eq : forall x, 0 <= x <= 40 -> bn_dec x 1 = map bz (DEC x 1) /\ bn_dec x 2 = map bz (DEC x 2).
Proof.
intros x Hx.
pose proof (z_all_spec (fun x => bn_leq (bn_dec x 1) (map bz (DEC x 1)) && bn_leq (bn_dec x 2) (map bz (DEC x 2)))
  (Z.to_nat 41) 0 ltac:(vm_compute; reflexivity) x ltac:(rewrite Z2Nat.id by lia; lia)) as H.
cbv beta in H. apply andb_true_iff in H as [H1 H2]. split; apply leq_eq; assumption.
Qed.

Lemma STEM_eq : forall f, bn_STEM f = map bz (stem_img f).
Proof.
intros f. unfold bn_STEM, stem_img.
destruct (f =? 1); [vm_compute; reflexivity|]. destruct (f =? 2); [vm_compute; reflexivity|].
destruct (f =? 3); vm_compute; reflexivity.
Qed.

Lemma stem_eq : forall inp, bn_stem (n_fam inp) (sdZ inp) = map bz (n_stem inp).
Proof.
intros inp. unfold sdZ, n_stem, n_use_said. destruct (n_said inp); cbn [andb].
- unfold name_str. destruct (model_name (idT inp)) as [|b r].
  + cbn [first_zero firstn map bn_stem]. assert (E : negb (bz (nthb [] 0) =? 0) = false) by reflexivity.
    rewrite E. apply STEM_eq.
  + cbn [first_zero]. unfold nthb. cbn [nth]. destruct (bz b =? 0).
    * cbn [firstn map bn_stem negb]. apply STEM_eq.
    * cbn [firstn map bn_stem negb]. reflexivity.
- cbn [bn_stem]. apply STEM_eq.
Qed.

Lemma NM_eq : forall inp, n_wok inp = true ->
  bn_NM (n_fam inp) (sdZ inp) (t_in inp) (t_out inp) = map bz (n_EXP_NM inp).
Proof.
intros inp W. destruct (wok_chans inp W) as [Hi Ho].
unfold bn_NM. rewrite stem_eq. unfold bn_w4.
destruct (dec_eq _ Hi) as [_ Di]. destruct (dec_eq _ Ho) as [_ Do]. rewrite Di, Do, <- map_app.
change (DEC (t_in inp) 2 ++ DEC (t_out inp) 2) with (n_W4 inp). cbv zeta.
rewrite length_map, skipn_map', leq_map.
unfold n_EXP_NM, n_ends_w4.
rewrite (firstn_all2 (n := 4%nat) (n_W4 inp))
  by (unfold n_W4; rewrite length_app, (DEC2_len _ Hi), (DEC2_len _ Ho); lia).
assert (E4 : (4 <=? Z.of_nat (length (n_stem inp))) = (4 <=? length (n_stem inp))%nat).
{ destruct (Z.leb_spec 4 (Z.of_nat (length (n_stem inp)))); destruct (Nat.leb_spec 4 (length (n_stem inp)));
    reflexivity || lia. }
rewrite E4.
destruct (_ && _); [reflexivity|]. rewrite !map_app. reflexivity.
Qed.

Lemma lower_eq : forall b, bz (lower b) = if (65 <=? bz b) && (bz b <=? 90) then bz b + 32 else bz b.
Proof.
intro b. unfold lower. destruct ((65 <=? bz b) && (bz b <=? 90)) eqn:E; [|reflexivity].
apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1, E2.
unfold zb, bz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. unfold bz in *. lia.
Qed.

Lemma tk_eq : forall l d, bn_tk d (map bz l) = map bz (tok_go d l).
Proof.
induction l as [|b r IH]; intros d; [reflexivity|]. cbn [map bn_tk tok_go].
rewrite andb_comm. destruct (negb d && (bz b =? 45)); [apply IH|].
cbn [map]. rewrite lower_eq, IH. reflexivity.
Qed.

Lemma DP_eq : forall inp, n_wok inp = true ->
  bn_DP (map bz (n_EXP_NM inp)) (t_in inp) (t_out inp) = map bz (n_EXP_DP inp).
Proof.
intros inp W. destruct (wok_chans inp W) as [Hi Ho].
destruct (dec_eq _ Hi) as [Di _]. destruct (dec_eq _ Ho) as [Do _].
unfold bn_DP, n_EXP_DP. rewrite Di, Do. rewrite !map_app. reflexivity.
Qed.

Lemma has_dash_len : forall l, has_dash l = true -> (1 <= length l)%nat.
Proof. intros [|b r] H; [discriminate H | cbn; lia]. Qed.

Lemma tok_len : forall l d,
  length (tok_go d l) = (length l - (if negb d && has_dash l then 1 else 0))%nat.
Proof.
induction l as [|b r IH]; intros d; [reflexivity|].
assert (HD : has_dash (b :: r) = (bz b =? 45) || has_dash r) by reflexivity. rewrite HD. destruct d.
- cbn [tok_go negb andb Datatypes.length]. rewrite IH. cbn [negb andb]. lia.
- destruct (bz b =? 45) eqn:E; cbn [tok_go negb andb orb Datatypes.length]; rewrite E; cbn [andb orb].
  + rewrite IH. cbn [negb andb]. lia.
  + cbn [Datatypes.length]. rewrite IH. cbn [negb andb]. destruct (has_dash r) eqn:D; [|lia].
    pose proof (has_dash_len r D). lia.
Qed.

Lemma tk_len : forall inp, Z.of_nat (length (n_TK inp)) = n_lt inp.
Proof.
intro inp. unfold n_TK, TOK, n_lt, n_ln. rewrite tok_len. cbn [negb andb].
destruct (has_dash (n_EXP_NM inp)) eqn:D; [|lia]. pose proof (has_dash_len _ D). lia.
Qed.

Lemma n_r_cases : forall inp, n_r inp = 0 \/ n_r inp = -1.
Proof. intros inp. unfold n_r. destruct (n_wok inp && n_fits inp); [left | right]; reflexivity. Qed.

Lemma n_r0 : forall inp, n_r inp = 0 -> n_wok inp = true /\ n_fits inp = true.
Proof.
intros inp H. unfold n_r in H. destruct (n_wok inp && n_fits inp) eqn:E; [|discriminate].
apply andb_true_iff in E. exact E.
Qed.

Lemma accept_eq : forall inp nm tk dp, nm <> 0 -> tk <> 0 -> dp <> 0 ->
  reac_box_name_c.bn_accept (n_fam inp) (sdZ inp) (t_in inp) (t_out inp) nm (t_cap_name inp) tk (t_cap_tok inp)
    dp (t_cap_disp inp) = (n_r inp =? 0).
Proof.
intros inp nm tk dp Hn Ht Hd.
unfold reac_box_name_c.bn_accept, reac_box_name_c.bn_args_ok, n_r. change bn_ok with okw.
rewrite (proj2 (Z.eqb_neq nm 0) Hn), (proj2 (Z.eqb_neq tk 0) Ht), (proj2 (Z.eqb_neq dp 0) Hd).
cbn [negb andb].
destruct (n_wok inp) eqn:W.
- pose proof W as W'. unfold n_wok in W'. apply andb_true_iff in W' as [W1 W3]. apply andb_true_iff in W1 as [W1 W2].
  rewrite W1, W2, W3.
  assert (R0 : bn_ret (n_fam inp) (sdZ inp) (t_in inp) (t_out inp) = 0).
  { unfold bn_ret. change bn_ok with okw. rewrite W1, W2, W3, (NM_eq inp W), length_map.
    pose proof (n_ln_le inp W) as HL.
    unfold n_ln in HL. destruct (Z.leb_spec (Z.of_nat (length (n_EXP_NM inp))) 23); [reflexivity | lia]. }
  rewrite R0. rewrite (NM_eq inp W). unfold bn_TK. rewrite tk_eq. rewrite (DP_eq inp W). rewrite !length_map.
  change (tok_go false (n_EXP_NM inp)) with (n_TK inp).
  change (Z.of_nat (length (n_EXP_NM inp))) with (n_ln inp).
  change (Z.of_nat (length (n_EXP_DP inp))) with (n_ld inp). rewrite tk_len.
  pose proof (n_ln_le inp W) as HL.
  assert (HT : 0 <= n_lt inp) by (pose proof (tk_len inp); lia).
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

(* The model name's string: its bytes are not 0, and it ends at the first 0 of the 17-byte field (id[19] is 0). *)
Lemma fz_nz : forall l, Forall (fun b => bz b <> 0) (firstn (first_zero l) l).
Proof.
induction l as [|b l IH]; cbn [first_zero]; [constructor|].
destruct (Z.eqb_spec (bz b) 0) as [E|E]; cbn [firstn]; [constructor | constructor; [exact E | exact IH]].
Qed.

Lemma fz_term : forall l, (first_zero l < length l)%nat -> bz (nth (first_zero l) l (zb 0)) = 0.
Proof.
induction l as [|b l IH]; cbn [first_zero length]; intros H; [lia|].
destruct (Z.eqb_spec (bz b) 0) as [E|E]; [exact E|]. cbn [nth]. apply IH. lia.
Qed.

Lemma fz_le : forall l, (first_zero l <= length l)%nat.
Proof. induction l as [|b l IH]; cbn [first_zero length]; [lia|]. destruct (bz b =? 0); lia. Qed.

Lemma bz_zb0 : bz (zb 0) = 0.
Proof. reflexivity. Qed.

Lemma name_facts : forall idb, length idb = ID_SIZE -> bz (nthb idb 19) = 0 ->
  (length (name_str idb) <= 16)%nat /\
  Forall (fun c => 0 < c < 256) (map bz (name_str idb)) /\
  (forall j, (j <= length (name_str idb))%nat ->
     nth j (map bz (name_str idb) ++ [0]) 0 = bz (nth (3 + j) idb (zb 0))).
Proof.
intros idb Hl H19. unfold ID_SIZE in Hl.
assert (Lm : length (model_name idb) = 17%nat)
  by (unfold model_name, get, OFF_NAME, NAME_CAP; rewrite length_firstn, length_skipn; lia).
assert (Hm : forall j, (j < 17)%nat -> nth j (model_name idb) (zb 0) = nth (3 + j) idb (zb 0)).
{ intros j Hj. unfold model_name, get, OFF_NAME, NAME_CAP. rewrite nth_first' by lia. apply nth_skipn'. }
pose proof (first_zero_le (model_name idb) 16 ltac:(lia)) as F.
rewrite (Hm 16%nat ltac:(lia)) in F. specialize (F H19).
assert (Ln : length (name_str idb) = first_zero (model_name idb))
  by (unfold name_str; rewrite length_firstn; pose proof (fz_le (model_name idb)); lia).
split; [lia|]. split.
- pose proof (fz_nz (model_name idb)) as N. unfold name_str.
  apply Forall_map. eapply Forall_impl; [|exact N]. intros b Hb. cbn beta in Hb.
  pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. unfold bz in *. lia.
- intros j Hj. rewrite Ln in Hj. destruct (Nat.lt_ge_cases j (first_zero (model_name idb))) as [Hlt|Hge].
  + rewrite app_nth1 by (rewrite length_map, Ln; exact Hlt).
    rewrite <- bz_zb0 at 1. rewrite map_nth. unfold name_str. rewrite nth_first' by exact Hlt.
    rewrite Hm by lia. reflexivity.
  + assert (Ej : j = first_zero (model_name idb)) by lia. subst j.
    rewrite app_nth2 by (rewrite length_map, Ln; lia). rewrite length_map, Ln, Nat.sub_diag. cbn [nth].
    rewrite <- (Hm (first_zero (model_name idb))) by lia. symmetry. apply fz_term. lia.
Qed.

(* reac_box_family_of's result is FAM of the box's bytes, for the table HW_ROWS. *)
Lemma row_iff : forall (rd : reader) p t (i : Z) idb,
  0 <= i < 3 -> length idb = 38%nat ->
  (forall j, 0 <= j < 38 -> rd (p + j) = Some (bz (nth (Z.to_nat j) idb (zb 0)))) ->
  (forall j, 0 <= j < 36 -> rd (t + j) = Some (nth (Z.to_nat j) HW_ROWS 0)) ->
  (reac_box_family_of.famof_row rd p t i <->
   map bz (firstn 8 (skipn 28 idb)) = firstn 8 (skipn (Z.to_nat (12 * i + 4)) HW_ROWS)).
Proof.
intros rd p t i idb Hi Hl Hp Ht. assert (LH : length HW_ROWS = 36%nat) by reflexivity.
assert (NA : forall n, (n < 8)%nat -> nth n (map bz (firstn 8 (skipn 28 idb))) 0 = bz (nth (28 + n) idb (zb 0))).
{ intros n Hn. rewrite <- bz_zb0 at 1. rewrite map_nth, nth_first' by exact Hn. rewrite nth_skipn'. reflexivity. }
assert (NB : forall n, (n < 8)%nat ->
  nth n (firstn 8 (skipn (Z.to_nat (12 * i + 4)) HW_ROWS)) 0 = nth (Z.to_nat (12 * i + 4) + n) HW_ROWS 0).
{ intros n Hn. rewrite nth_first' by exact Hn. apply nth_skipn'. }
unfold reac_box_family_of.famof_row. split.
- intros H. apply (nth_ext _ _ 0 0).
  + rewrite length_map, !length_firstn, !length_skipn, Hl, LH. lia.
  + intros n Hn. rewrite length_map, length_firstn, length_skipn, Hl in Hn.
    rewrite NA, NB by lia.
    specialize (H (Z.of_nat n) ltac:(lia)).
    replace (p + 28 + Z.of_nat n) with (p + (28 + Z.of_nat n)) in H by lia.
    replace (t + 12 * i + 4 + Z.of_nat n) with (t + (12 * i + 4 + Z.of_nat n)) in H by lia.
    rewrite Hp, Ht in H by lia. injection H as H.
    replace (Z.to_nat (28 + Z.of_nat n)) with (28 + n)%nat in H by lia.
    replace (Z.to_nat (12 * i + 4 + Z.of_nat n)) with (Z.to_nat (12 * i + 4) + n)%nat in H by lia. exact H.
- intros H j Hj.
  replace (p + 28 + j) with (p + (28 + j)) by lia. replace (t + 12 * i + 4 + j) with (t + (12 * i + 4 + j)) by lia.
  rewrite Hp, Ht by lia. f_equal.
  pose proof (f_equal (fun l => nth (Z.to_nat j) l 0) H) as Hn. cbv beta in Hn.
  rewrite NA, NB in Hn by lia.
  replace (Z.to_nat (28 + j)) with (28 + Z.to_nat j)%nat by lia.
  replace (Z.to_nat (12 * i + 4 + j)) with (Z.to_nat (12 * i + 4) + Z.to_nat j)%nat by lia. exact Hn.
Qed.

Lemma FAM_res : forall (rd : reader) p t idb r,
  length idb = 38%nat -> p <> 0 ->
  (forall j, 0 <= j < 38 -> rd (p + j) = Some (bz (nth (Z.to_nat j) idb (zb 0)))) ->
  (forall j, 0 <= j < 36 -> rd (t + j) = Some (nth (Z.to_nat j) HW_ROWS 0)) ->
  reac_box_family_of.famof_res rd p t 1 2 3 r -> r = FAM idb.
Proof.
intros rd p t idb r Hl Hp0 Hp Ht Hres.
pose proof (row_iff rd p t 0 idb ltac:(lia) Hl Hp Ht) as R0.
pose proof (row_iff rd p t 1 idb ltac:(lia) Hl Hp Ht) as R1.
pose proof (row_iff rd p t 2 idb ltac:(lia) Hl Hp Ht) as R2.
change (firstn 8 (skipn (Z.to_nat (12 * 0 + 4)) HW_ROWS)) with reac_box_family_of_c.FAMOF_HW1 in R0.
change (firstn 8 (skipn (Z.to_nat (12 * 1 + 4)) HW_ROWS)) with reac_box_family_of_c.FAMOF_HW2 in R1.
change (firstn 8 (skipn (Z.to_nat (12 * 2 + 4)) HW_ROWS)) with reac_box_family_of_c.FAMOF_HW3 in R2.
unfold bz in R0, R1, R2.
pose proof (Hp 36 ltac:(lia)) as R36. change (Z.to_nat 36) with 36%nat in R36. unfold bz, zb in R36.
unfold FAM, reac_box_family_of_c.FAMOF_FAM. change (1 =? 0) with false. cbv beta iota zeta.
destruct Hres as [(H0 & _) | [(_ & H36 & ->) | [(_ & H36 & Hr0 & ->) | [(_ & H36 & Hn0 & Hr1 & ->) |
  [(_ & H36 & Hn0 & Hn1 & Hr2 & ->) | (_ & H36 & Hn0 & Hn1 & Hn2 & ->)]]]]].
- contradiction.
- rewrite R36 in H36. injection H36 as E. rewrite E. reflexivity.
- destruct (Z.eqb_spec (bv_unsigned (nth 36 idb (Z_to_bv 8 0))) 0) as [e|e];
    [exfalso; apply H36; rewrite R36, e; reflexivity|].
  apply R0 in Hr0. destruct (list_eq_dec Z.eq_dec _ _) as [_|n]; [reflexivity | contradiction].
- destruct (Z.eqb_spec (bv_unsigned (nth 36 idb (Z_to_bv 8 0))) 0) as [e|e];
    [exfalso; apply H36; rewrite R36, e; reflexivity|].
  apply R1 in Hr1.
  destruct (list_eq_dec Z.eq_dec _ reac_box_family_of_c.FAMOF_HW1) as [y|_]; [exfalso; apply Hn0; apply R0; exact y|].
  destruct (list_eq_dec Z.eq_dec _ _) as [_|n]; [reflexivity | contradiction].
- destruct (Z.eqb_spec (bv_unsigned (nth 36 idb (Z_to_bv 8 0))) 0) as [e|e];
    [exfalso; apply H36; rewrite R36, e; reflexivity|].
  apply R2 in Hr2.
  destruct (list_eq_dec Z.eq_dec _ reac_box_family_of_c.FAMOF_HW1) as [y|_]; [exfalso; apply Hn0; apply R0; exact y|].
  destruct (list_eq_dec Z.eq_dec _ reac_box_family_of_c.FAMOF_HW2) as [y|_]; [exfalso; apply Hn1; apply R1; exact y|].
  destruct (list_eq_dec Z.eq_dec _ _) as [_|n]; [reflexivity | contradiction].
- destruct (Z.eqb_spec (bv_unsigned (nth 36 idb (Z_to_bv 8 0))) 0) as [e|e]; [reflexivity|].
  destruct (list_eq_dec Z.eq_dec _ reac_box_family_of_c.FAMOF_HW1) as [y|_]; [exfalso; apply Hn0; apply R0; exact y|].
  destruct (list_eq_dec Z.eq_dec _ reac_box_family_of_c.FAMOF_HW2) as [y|_]; [exfalso; apply Hn1; apply R1; exact y|].
  destruct (list_eq_dec Z.eq_dec _ reac_box_family_of_c.FAMOF_HW3) as [y|_]; [exfalso; apply Hn2; apply R2; exact y|].
  reflexivity.
Qed.

Lemma FAM_range : forall idb, 0 <= FAM idb <= 3.
Proof.
intros idb. unfold FAM, reac_box_family_of_c.FAMOF_FAM. change (1 =? 0) with false. cbv beta iota zeta.
destruct (_ =? 0); [lia|]. repeat (destruct (list_eq_dec _ _ _); [lia|]). lia.
Qed.

Lemma n_fam_range : forall inp, 0 <= n_fam inp < 128.
Proof.
intros inp. unfold n_fam. pose proof (inb_range inp (cT inp + 0)) as R. unfold t_fam_raw, tb.
destruct (128 <=? inb inp (cT inp + 0)); [|pose proof (FAM_range (idT inp)); lia].
pose proof (Z_land_upper (inb inp (cT inp + 0)) 127 ltac:(lia)). lia.
Qed.
End IM.

(* ---- the symbolic states ------------------------------------------------------------------------------------ *)
(* At 0x81878 (I_head): the two machine-frame words the head reads, base s1 (atom 9): mf+128 = SF+355 (atom 32),
   mf+184 = SF+352 (atom 33); read-only. *)
Definition I_rH : YP09.region := YP09.mkRegion (Some 9%nat) 128 192 128 128
  [YP09.mkChunk 128 (CVal 8 (SOff 32 0)); YP09.mkChunk 184 (CVal 8 (SOff 33 0))].
Definition ss_IH : sstate := mkSS 0x116c sr_atoms [I_rH] None (mkFacts [] [] []).
(* At 0x81890 (I_tail): region 0, the machine-frame words mf+128 (SF+355, atom 32), mf+160 (t_in, atom 34),
   mf+168 (t_out, atom 35), writable on [152, 160) (0x818b0 stores cap_name); region 1, mf+184 (SF+352, atom 33),
   writable (0x818bc stores nm); region 2, the byte id[20] (has_model_name, atom 36) at SF+352+20, read-only. *)
Definition I_r0 : YP09.region := YP09.mkRegion (Some 9%nat) 128 184 152 160
  [YP09.mkChunk 128 (CVal 8 (SOff 32 0)); YP09.mkChunk 160 (CVal 8 (SOff 34 0)); YP09.mkChunk 168 (CVal 8 (SOff 35 0))].
Definition I_r1 : YP09.region := YP09.mkRegion (Some 9%nat) 184 192 184 192 [YP09.mkChunk 184 (CVal 8 (SOff 33 0))].
Definition I_r2 : YP09.region := YP09.mkRegion (Some 33%nat) 20 21 20 20 [YP09.mkChunk 20 (CVal 1 (SOff 36 0))].
Definition ss_IT : sstate := mkSS 0x1184 sr_atoms [I_r0; I_r1; I_r2] None (mkFacts [(36%nat, mkAF 0 255 0)] [] []).
(* The 16 bytes of stack arguments below mf (base sp, atom 2), added after the third malloc. *)
Definition I_rS : YP09.region := YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [].

(* The listing's arithmetic on the family byte, the capacities and the branch operands. *)
Lemma I_off0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof.
intros E n v H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by exact Hv. rewrite Z.add_0_r. reflexivity.
Qed.
Lemma I_beq_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  branch_taken BC_EQ (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. rewrite YO0c.branch_eq, (unsigned_lit_small a), (unsigned_lit_small b) by assumption. reflexivity. Qed.
Lemma I_blt_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  branch_taken BC_LT (Z_to_bv 64 a) (Z_to_bv 64 b) = (YO0b.s64 a <? YO0b.s64 b).
Proof. intros a b Ha Hb. rewrite YO0c.branch_lt, (unsigned_lit_small a), (unsigned_lit_small b) by assumption. reflexivity. Qed.
Lemma I_bltz : forall E n v, ew E n = Z_to_bv 64 (v * 2 ^ 56) -> 0 <= v < 256 ->
  branch_taken BC_LT (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (128 <=? v).
Proof.
intros E n v H Hv.
assert (HC : 0 <= v * 2 ^ 56 < 2 ^ 64).
{ change (2 ^ 56) with 72057594037927936. change (2 ^ 64) with 18446744073709551616. lia. }
rewrite (I_off0 E n (v * 2 ^ 56) H HC).
change (sv_denot E (SLit 0)) with (Z_to_bv 64 0).
rewrite I_blt_lit by lia.
unfold YO0b.s64. replace (0 <? 2 ^ 63) with true by reflexivity.
change (2 ^ 56) with 72057594037927936 in *. change (2 ^ 63) with 9223372036854775808.
change (2 ^ 64) with 18446744073709551616 in *.
destruct (Z.ltb_spec (v * 72057594037927936) 9223372036854775808) as [Hlt|Hge];
destruct (Z.leb_spec 128 v) as [Hv2|Hv2].
- exfalso. lia.
- apply Z.ltb_ge. lia.
- apply Z.ltb_lt. lia.
- exfalso. lia.
Qed.
Lemma I_and_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  alu64 ALU_AND (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.land a b).
Proof.
intros a b Ha Hb. apply bv_eq. rewrite YO0c.alu64_and, (unsigned_lit_small a), (unsigned_lit_small b) by assumption.
rewrite unsigned_lit_small; [reflexivity|].
pose proof (Z_land_upper a b ltac:(lia)). lia.
Qed.
Lemma I_beqz_ne : forall E n v, ew E n = Z_to_bv 64 v -> 0 < v < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = false.
Proof.
intros E n v H Hv. rewrite (I_off0 E n v H ltac:(lia)).
change (sv_denot E (SLit 0)) with (Z_to_bv 64 0).
rewrite I_beq_lit by lia. apply Z.eqb_neq. lia.
Qed.
Lemma I_sltu_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  alu64 ALU_SLTU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if a <? b then 1 else 0).
Proof.
intros a b Ha Hb. apply bv_eq. rewrite YO0c.alu64_sltu, (unsigned_lit_small a), (unsigned_lit_small b) by assumption.
unfold YO0a.sltu. destruct (a <? b); rewrite unsigned_lit_small by lia; reflexivity.
Qed.
(* the `seqz; add` idiom for `max cap 1` the walk uses at each malloc (0x818b0.., 0x818c4.., 0x818e0..) *)
Lemma I_maxcap : forall v, 0 <= v < 256 ->
  alu64 ALU_ADD (alu64 ALU_AND (Z_to_bv 64 v) (Z_to_bv 64 255))
    (alu64 ALU_SLTU (alu64 ALU_AND (Z_to_bv 64 v) (Z_to_bv 64 255)) (Z_to_bv 64 1)) = Z_to_bv 64 (Z.max v 1).
Proof.
intros v Hv. rewrite (I_and_lit v 255 ltac:(lia) ltac:(lia)).
assert (Hl : Z.land v 255 = v) by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
rewrite Hl, (I_sltu_lit v 1 ltac:(lia) ltac:(lia)).
apply bv_eq. rewrite YO0c.alu64_add, (unsigned_lit_small v) by lia.
rewrite (unsigned_lit_small (if v <? 1 then 1 else 0)) by (destruct (v <? 1); lia).
rewrite (unsigned_lit_small (Z.max v 1)) by lia.
unfold YO0a.add64. destruct (Z.ltb_spec v 1).
- rewrite (Z.max_r v 1) by lia. rewrite Z.mod_small by lia. lia.
- rewrite (Z.max_l v 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.
(* the same without the zext.b (0x818e0 `seqz a0,s11; add a0,s11,a0` on the unmasked cap_disp) *)
Lemma I_maxcap_raw : forall v, 0 <= v < 2 ^ 63 ->
  alu64 ALU_ADD (Z_to_bv 64 v) (alu64 ALU_SLTU (Z_to_bv 64 v) (Z_to_bv 64 1)) = Z_to_bv 64 (Z.max v 1).
Proof.
intros v Hv. rewrite (I_sltu_lit v 1 ltac:(lia) ltac:(lia)).
apply bv_eq. rewrite YO0c.alu64_add, (unsigned_lit_small v) by lia.
rewrite (unsigned_lit_small (if v <? 1 then 1 else 0)) by (destruct (v <? 1); lia).
rewrite (unsigned_lit_small (Z.max v 1)) by lia.
unfold YO0a.add64. destruct (Z.ltb_spec v 1).
- rewrite (Z.max_r v 1) by lia. rewrite Z.mod_small by lia. lia.
- rewrite (Z.max_l v 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.
(* 0x818f8..0x81900 `seqz a0,s7; addi a0,a0,-1; and s2,a0,s2` (and the `mv a1,s2` that adds 0): said is the model
   name's address when id.has_model_name <> 0, else NULL *)
Lemma I_said_expr : forall h p, 0 <= h < 256 -> 0 <= p < 2 ^ 64 ->
  alu64 ALU_ADD (alu64 ALU_AND (alu64 ALU_ADD (alu64 ALU_SLTU (Z_to_bv 64 h) (Z_to_bv 64 1)) (Z_to_bv 64 (-1)))
    (Z_to_bv 64 p)) (Z_to_bv 64 0) = Z_to_bv 64 (if h =? 0 then 0 else p).
Proof.
intros h p Hh Hp. rewrite (I_sltu_lit h 1 ltac:(lia) ltac:(lia)).
assert (E1 : alu64 ALU_ADD (Z_to_bv 64 (if h <? 1 then 1 else 0)) (Z_to_bv 64 (-1)) =
  Z_to_bv 64 (if h =? 0 then 0 else Z.ones 64)).
{ apply bv_eq. rewrite YO0c.alu64_add, !Z_to_bv_unsigned. unfold YO0a.add64, bv_wrap.
  change (bv_modulus 64) with (2 ^ 64).
  destruct (Z.ltb_spec h 1); destruct (Z.eqb_spec h 0); try lia; vm_compute; reflexivity. }
rewrite E1.
assert (E2 : alu64 ALU_AND (Z_to_bv 64 (if h =? 0 then 0 else Z.ones 64)) (Z_to_bv 64 p) =
  Z_to_bv 64 (if h =? 0 then 0 else p)).
{ destruct (h =? 0).
  - rewrite (I_and_lit 0 p ltac:(lia) Hp). rewrite Z.land_0_l. reflexivity.
  - rewrite (I_and_lit (Z.ones 64) p ltac:(change (Z.ones 64) with (2 ^ 64 - 1); lia) Hp).
    rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
rewrite E2. apply bv_eq. rewrite YO0c.alu64_add, (unsigned_lit_small 0) by lia.
rewrite (unsigned_lit_small (if h =? 0 then 0 else p)) by (destruct (h =? 0); lia).
unfold YO0a.add64. rewrite Z.add_0_r, Z.mod_small by (destruct (h =? 0); lia). reflexivity.
Qed.

Lemma I_and255 : forall v, 0 <= v < 256 -> alu64 ALU_AND (Z_to_bv 64 v) (Z_to_bv 64 255) = Z_to_bv 64 v.
Proof.
intros v Hv. rewrite (I_and_lit v 255 ltac:(lia) ltac:(lia)). f_equal.
change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Lemma I_add0 : forall v, 0 <= v < 2 ^ 64 -> alu64 ALU_ADD (Z_to_bv 64 v) (Z_to_bv 64 0) = Z_to_bv 64 v.
Proof.
intros v Hv. apply bv_eq. rewrite YO0c.alu64_add, (unsigned_lit_small v), (unsigned_lit_small 0) by lia.
unfold YO0a.add64. rewrite Z.add_0_r, Z.mod_small by lia. reflexivity.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v, in the same order. *)
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
#[local] Notation EPRE g := (e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS g).
#[local] Notation ACUT := (acut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation MEV := (mo_malloc MT 256 + mo_free MT).
#[local] Notation AJ g pos := (ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
  [(4, pos)]).
(* What this segment needs, each as the contract's Section states it (LLVMFuzzerTestOneInput.v, _inv.v). *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis HLIVE : LIVE_LLVMF <= LIVE_LIB.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis PSIG : ident_prog_sig_ok (PI := PI).
Hypothesis MTL : ameter_laws MT.
Hypothesis HMT0 : forall s s' : astate, mo_le MT s s' 0.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Hypothesis HIMG : forall (W : world SEGS) mem,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> llvmf_img B G W mem.
Hypothesis HUMM : forall c, In c (LLVMF_MALLOC_CTX RA_LLVMF) ->
  In (firstn kUnwindMax (pc_malloc_ra0 (as_code B)
  :: flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) c)) (as_universe B).
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
(* cgif ACfh.v:162-164 *)
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
(* the program callees of this segment *)
Hypothesis HFAM : reac_box_family_of.treac_box_family_of_spec B.
Hypothesis HSTEM : reac_box_family_stem.treac_box_family_stem_spec B.
Hypothesis HBN : reac_box_name.treac_box_name_spec B G.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

(* ---- the bytes a step of this segment keeps ----------------------------------------------------------------- *)
(* The entry's frame and its shadow, the input block, and the machine stack from mf up except the two slots the
   segment writes (mf+152, mf+184). A call keeps all of [mf, sp0); a run writes only its regions' windows. *)
Definition fzone (g : ectx) (pos a : Z) : Prop :=
  (SFa g pos <= a < SFa g pos + 1024) \/ (shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128).
Definition inblk (g : ectx) (a : Z) : Prop := 0 < e_n g /\ e_p g <= a < e_p g + e_n g.
Definition iprot (g : ectx) (pos mf a : Z) : Prop :=
  ((mf <= a < e_sp0 g) /\ ~ (mf + 152 <= a < mf + 160) /\ ~ (mf + 184 <= a < mf + 192)) \/ fzone g pos a \/ inblk g a.
Definition ikept (g : ectx) (pos mf : Z) (W : world SEGS) (memc : word -> option byte)
  (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
  forall a, iprot g pos mf a -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W) memc a.

Lemma ikept_refl : forall g pos mf W m, ikept g pos mf W m W m.
Proof. intros g pos mf W m a _. reflexivity. Qed.
Lemma ikept_trans : forall g pos mf W1 m1 W2 m2 W3 m3,
  ikept g pos mf W1 m1 W2 m2 -> ikept g pos mf W2 m2 W3 m3 -> ikept g pos mf W1 m1 W3 m3.
Proof. intros g pos mf W1 m1 W2 m2 W3 m3 H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.

(* What a boundary of the entry's journal says of the frame, the stack and the input block. *)
Lemma I_base : forall g pos lyc Sc W mem md k hs,
  EPRE g -> AJ g pos lyc Sc W mem md k -> frames Sc = [(4, pos)] -> hblocks B g lyc Sc hs ->
  frame_addr lyc 4 pos = SFa g pos /\ In (4, pos) (frames Sc) /\
  4096 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling /\ in_app (SFa g pos) 1024 /\ SFa g pos mod 64 = 0 /\
  alloc_ceiling + LLVMF_STK <= e_sp0 g /\ e_sp0 g mod 16 = 0 /\ e_sp0 g <= 2 ^ 47 /\
  (0 < e_n g -> In (e_p g, e_n g) (ablocks B lyc Sc)) /\ e_n g = Z.of_nat (length (e_pl g)) /\
  (forall a, SFa g pos <= a < SFa g pos + 1024 -> apresent (w_H W) mem a) /\
  (forall i, 0 <= i < 128 -> apresent (w_H W) mem (shadow_addr (SFa g pos) + i)) /\
  (forall a, e_sp0 g - LLVMF_STK <= a < e_sp0 g -> apresent (w_H W) mem a).
Proof.
intros g pos lyc Sc W mem md k hs HPRE HJ Hfrs Hbl.
pose proof HPRE as (_ & _ & _ & _ & Hinp & Hlen & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _).
assert (Hin : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr lyc 4 pos = SFa g pos)
by (unfold SFa, frame_addr; destruct Hly as (_ & _ & _ & _ & _ & EF & _); rewrite EF; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hin) as (HF4096 & HFceil & HFapp).
destruct (frame_al64 SEGS B _ _ _ _ _ 4 pos HAR Hin) as (HF64 & _ & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR Hin) as (_ & _ & HFpres & HFSpres).
rewrite EFA in HF4096, HFceil, HFapp, HF64, HFpres, HFSpres.
change (fs_frame_bytes 4) with 1024 in *. change (1024 / 8) with 128 in HFSpres.
split; [exact EFA|]. split; [exact Hin|]. split; [exact HF4096|]. split; [exact HFceil|].
split; [exact HFapp|]. split; [exact HF64|].
split; [clear - Hceil Hslo; lia|]. split; [exact Hsp0al|]. split; [clear - Hshi H47; lia|].
split.
{ intros Hn. destruct Hinp as [[Hn0 _] | [_ Hine]]; [clear - Hn Hn0; lia|].
  destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. exact Hine. }
split; [exact Hlen|].
split; [intros a Ha; exact (proj1 (HFpres a Ha))|].
split; [intros i Hi; exact (proj1 (HFSpres i Hi))|].
intros a Ha. apply Hpres. exact Ha.
Qed.

(* A call's kept bytes, from the clauses every call post states (acall_kept or a callee journal). *)
Lemma I_ikept_of : forall g pos mf lyc Sc (W : world SEGS) memc (W3 : world SEGS) mem3 slo (E : Z -> Prop),
  frame_addr lyc 4 pos = SFa g pos -> In (4, pos) (frames Sc) ->
  (0 < e_n g -> In (e_p g, e_n g) (ablocks B lyc Sc)) ->
  alloc_ceiling <= mf -> e_sp0 g <= 2 ^ 47 ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < mf) ->
     aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W) memc a) ->
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) ->
     aview SEGS (w_H W3) mem3 (b + i) = aview SEGS (w_H W) memc (b + i)) ->
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ E a -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W) memc a) ->
  (forall a, E a -> a < alloc_ceiling /\ ~ fzone g pos a /\ ~ inblk g a) ->
  ikept g pos mf W memc W3 mem3.
Proof.
intros g pos mf lyc Sc W memc W3 mem3 slo E EFA Hin Hinb Hce Hsp K1 K2 K4 HE a [(Ha & _ & _) | [Ha | Ha]].
- apply K1; [lia | lia].
- apply (K4 4 pos a Hin).
  + unfold frame_rng, in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 4) with 1024.
    change (1024 / 8) with 128. unfold fzone in Ha. destruct Ha; [left | right]; lia.
  + intros HEa. destruct (HE a HEa) as (_ & Hn & _). exact (Hn Ha).
- pose proof Ha as (Hn & Ha1 & Ha2). replace a with (e_p g + (a - e_p g)) by lia.
  apply (K2 _ _ _ (Hinb Hn)).
  + pose proof (req_size_pos (e_n g) ltac:(lia)). lia.
  + replace (e_p g + (a - e_p g)) with a by lia. intros HEa. destruct (HE a HEa) as (_ & _ & Hn'). exact (Hn' Ha).
Qed.

(* A block of the run's own list is not one of the entry's blocks: the allocator's blocks are pairwise apart. *)
Lemma I_fresh : forall ly S (W : world SEGS) mem md (x : Z * Z) l0 E0,
  AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (l0 ++ E0) -> In x l0 -> 0 <= snd x -> ~ In x E0.
Proof.
intros ly S W mem md x l0 E0 HAR HP Hx Hn HxE.
assert (Hz : ~ zdisjoint (block_rng x) (block_rng x)).
{ destruct x as [p m]. unfold zdisjoint, block_rng. cbn [fst snd] in *. pose proof (req_size_pos m Hn). lia. }
apply in_split in Hx as (h1 & h2 & ->). apply in_split in HxE as (e1 & e2 & ->).
assert (Hin : In x (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
apply in_split in Hin as (a1 & a2 & Ea). rewrite Ea in HP.
replace ((h1 ++ x :: h2) ++ e1 ++ x :: e2) with (h1 ++ x :: (h2 ++ e1 ++ x :: e2)) in HP
  by (rewrite <- app_assoc; reflexivity).
pose proof (Permutation_app_inv a1 a2 h1 (h2 ++ e1 ++ x :: e2) x HP) as HP2.
assert (Hin2 : In x (a1 ++ a2)).
{ eapply Permutation_in; [apply Permutation_sym; exact HP2|]. apply in_or_app. right. apply in_or_app. right.
  apply in_or_app. right. left. reflexivity. }
apply in_app_or in Hin2 as [Hin2 | Hin2]; apply in_split in Hin2 as (b1 & b2 & ->).
- apply Hz. apply (sep_blocks_pos SEGS B LAWS ly S W mem md x x b1 b2 a2 HAR). rewrite Ea. rewrite <- app_assoc. reflexivity.
- apply Hz. apply (sep_blocks_pos SEGS B LAWS ly S W mem md x x a1 b1 b2 HAR). exact Ea.
Qed.

(* A block of the run's own list lies off the frame, its shadow, the input block and the stack. *)
Lemma I_blk_apart : forall g pos ly3 S3 (W3 : world SEGS) mem3 md3 hs b m,
  EPRE g -> AR SEGS B ly3 S3 W3 mem3 md3 -> frame_addr ly3 4 pos = SFa g pos -> In (4, pos) (frames S3) ->
  hblocks B g ly3 S3 hs -> In (b, m) hs ->
  In (b, m) (ablocks B ly3 S3) /\ 4096 <= b /\ b + req_size m <= alloc_ceiling /\ 0 <= m < MALLOC_MAX /\
  ~ In (b, m) (ablocks B (e_ly g) (e_S g)) /\
  (forall a, b <= a < b + req_size m -> a < alloc_ceiling /\ ~ fzone g pos a /\ ~ inblk g a).
Proof.
intros g pos ly3 S3 W3 mem3 md3 hs b m HPRE HAR EFA Hin4 [Hperm Hfa] Hbm.
pose proof HPRE as (_ & _ & _ & _ & Hinp & _).
assert (Hb : In (b, m) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. exact Hbm. }
pose proof (proj1 (Forall_forall _ _) Hfa _ Hbm) as [Hb4096 Hm0]. cbn [fst snd] in Hb4096, Hm0.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & _ & Hbce & _ & _ & _ & Hmmax).
assert (Hnew : ~ In (b, m) (ablocks B (e_ly g) (e_S g)))
  by exact (I_fresh ly3 S3 W3 mem3 md3 (b, m) hs _ HAR Hperm Hbm Hm0).
split; [exact Hb|]. split; [exact Hb4096|]. split; [exact Hbce|]. split; [exact Hmmax|]. split; [exact Hnew|].
intros a Ha. split; [lia|]. split.
- intros Hz. apply (block_not_frame_zone SEGS B LAWS ly3 S3 W3 mem3 md3 b m (a - b) 4 pos HAR Hb Hin4); [lia|].
  replace (b + (a - b)) with a by lia. unfold frame_rng, in_zr. cbn [fst snd]. rewrite EFA.
  change (fs_frame_bytes 4) with 1024. change (1024 / 8) with 128. unfold fzone in Hz. destruct Hz; [left | right]; lia.
- intros (Hn & Hp1 & Hp2). destruct Hinp as [[Hn0 _] | [_ Hine]]; [lia|].
  assert (Hine3 : In (e_p g, e_n g) (ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. exact Hine. }
  assert (Hne : (b, m) <> (e_p g, e_n g)) by (intros Heq; apply Hnew; rewrite Heq; exact Hine).
  pose proof (sep_blocks SEGS B LAWS ly3 S3 W3 mem3 md3 b m (e_p g) (e_n g) HAR Hb Hine3 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. pose proof (req_size_pos (e_n g) ltac:(lia)). lia.
Qed.

(* The call chain at a call the entry makes from its own frame: s0 = sp0 holds the entry's saved ra and s0, and
   above them is the entry's own chain (its pre-condition's achain), which the journal keeps. *)
Lemma I_chain : forall g pos lyc Sc (W : world SEGS) memc mdc k mf,
  EPRE g -> AJ g pos lyc Sc W memc mdc k ->
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 ->
  val_mem SEGS (rd W memc) (e_sp0 g - 8) 8 RA_LLVMF ->
  val_mem SEGS (rd W memc) (e_sp0 g - 16) 8 (s0Z (e_regs g)) ->
  exists ch, achain lyc (aview SEGS (w_H W) memc) mf (e_sp0 g) ch /\
    (ch = [] \/ exists fp v, ch = [(fp, RA_LLVMF, v)]).
Proof.
intros g pos lyc Sc W memc mdc k mf HPRE HJ Hmf Vra Vs0.
pose proof HPRE as (HFN & Hraz & _).
destruct HFN as (_ & _ & Hra40 & _ & _ & _ & _ & Hach & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & ETop & _).
pose proof asan_consts as (C1 & _).
pose proof HSTK as HSTK'. unfold STK_LLVMF, ASTACK in HSTK'.
change (spZ (e_regs g)) with (e_sp0 g) in Hach.
destruct (Z_lt_le_dec (e_sp0 g) (ly_top lyc - 16)) as [Hlt | Hge].
- exists [(e_sp0 g, RA_LLVMF, s0Z (e_regs g))]. split; [|right; exists (e_sp0 g), (s0Z (e_regs g)); reflexivity].
  pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 8)) as Rs0r. change (bv_modulus 64) with (2 ^ 64) in Rs0r.
  assert (HRAr : 0 <= RA_LLVMF < 2 ^ 64).
  { rewrite <- Hraz. unfold raZ. pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 1)) as R.
    change (bv_modulus 64) with (2 ^ 64) in R. exact R. }
  apply (achain_push lyc (aview SEGS (w_H (e_W g)) (e_mem g)) _ (e_sp0 g) (s0Z (e_regs g)) RA_LLVMF [] mf).
  + apply (achain_ly_top (e_ly g)); [exact ETop | exact Hach].
  + rewrite ETop. clear - Htop1 H47. lia.
  + intros a Ha. exact (aview_above_of_journal B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
      [(4, pos)] lyc Sc W memc mdc k HJ a Ha).
  + apply rdword_of_val_mem; [exact Vra | exact HRAr].
  + apply rdword_of_val_mem; [exact Vs0 | unfold s0Z; exact Rs0r].
  + rewrite <- Hraz. exact Hra40.
  + clear - Hceil Hslo HSTK'. lia.
  + clear - Hsp0al. lia.
  + exact Hlt.
  + clear - Hmf. lia.
- exists []. split; [|left; reflexivity]. left. split; [right; left; exact Hge | reflexivity].
Qed.

(* The meter after one allocator event (c = mo_malloc / mo_free) or a program call (c = 0). *)
Lemma I_meter : forall S0 Sc S3 k c d,
  0 <= k -> k + d <= EV_LLVMF -> 0 <= d -> 0 <= c <= d * MEV ->
  mo_le MT S0 Sc (k * MEV) -> mo_ok MT Sc ((EV_LLVMF - k) * MEV) -> mo_le MT Sc S3 c ->
  mo_le MT S0 S3 ((k + d) * MEV) /\ mo_ok MT S3 ((EV_LLVMF - (k + d)) * MEV).
Proof.
intros S0 Sc S3 k c d Hk0 Hk1 Hd Hc HMLE HMOK HM3.
assert (Hmmal : 0 <= mo_malloc MT 256) by exact (mo_malloc_nonneg MT MTL 256 ltac:(lia)).
assert (Hmfree : 0 <= mo_free MT) by exact (mo_free_nonneg MT MTL).
split.
- apply (mo_le_mono MT MTL _ _ (k * MEV + c)); [exact (mo_le_trans MT MTL _ _ _ _ _ HMLE HM3)|].
  assert (X : (k + d) * MEV = k * MEV + d * MEV) by ring. rewrite X. lia.
- assert (X : (EV_LLVMF - k) * MEV = c + ((EV_LLVMF - k) * MEV - c)) by ring. rewrite X in HMOK.
  pose proof (mo_ok_step MT MTL Sc S3 c ((EV_LLVMF - k) * MEV - c) HMOK HM3) as HM.
  apply (mo_ok_le MT MTL S3 _ _ HM).
  assert (X2 : (EV_LLVMF - k) * MEV = d * MEV + (EV_LLVMF - (k + d)) * MEV) by ring. rewrite X2.
  assert (0 <= (EV_LLVMF - (k + d)) * MEV) by (apply Z.mul_nonneg_nonneg; lia). lia.
Qed.

(* One malloc from the entry's frame (amalloc04_rule through YC85.amalloc04_sub). *)
Lemma I_malloc_at : forall g pos mf (W : world SEGS) (regsT : bvmap 5 word) memT mdc lyc Sc k hs n retk
  (Q : world SEGS -> config -> Prop),
  EPRE g -> AJ g pos lyc Sc W memT mdc k -> frames Sc = [(4, pos)] -> hblocks B g lyc Sc hs ->
  bsum hs + n <= LIVE_LLVMF -> 0 <= n <= 256 ->
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
  val_mem SEGS (rd W memT) (e_sp0 g - 8) 8 RA_LLVMF ->
  val_mem SEGS (rd W memT) (e_sp0 g - 16) 8 (s0Z (e_regs g)) ->
  getr regsT 10 = w64 n -> getr regsT 2 = w64 mf -> getr regsT 8 = w64 (e_sp0 g) ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = Z_to_bv 64 (BASE + retk) -> In retk LLVMF_MALLOC_RAS -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  0 <= k -> k + 1 <= EV_LLVMF ->
  mo_le MT (e_S g) Sc (k * MEV) -> mo_ok MT Sc ((EV_LLVMF - k) * MEV) ->
  (forall W3 ly3 S3 regs3 mem3 md3 res, wle W W3 ->
   AJ g pos ly3 S3 W3 mem3 md3 (k + 1) ->
   aregs_preserved regsT regs3 -> frames S3 = [(4, pos)] ->
   getr regs3 10 = w64 res -> 4096 <= res -> hblocks B g ly3 S3 ((res, n) :: hs) ->
   ikept g pos mf W memT W3 mem3 ->
   acall_kept SEGS B lyc Sc W memT W3 mem3 (mf - ASTACK) mf (fun a => res <= a < res + req_size n) ->
   mo_le MT (e_S g) S3 ((k + 1) * MEV) -> mo_ok MT S3 ((EV_LLVMF - (k + 1)) * MEV) ->
   SRr SEGS W3 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + retk)) mem3 (seg_rom SEGS)) md3) Q) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc (as_code B))) memT (seg_rom SEGS)) mdc) Q.
Proof.
intros g pos mf W regsT memT mdc lyc Sc k hs n retk Q HPRE HJ Hfrs Hbl Hlv Hn Hmf Hmf32 Vra Vs0
  Ha0 Rsp Rs0 Rgp Rtp Rra Hras Hretk Hreven Hk0 Hk1 HMLE HMOK Hk.
pose proof HPRE as (HFN & Hraz & _ & _ & _ & _ & _ & _ & Hnev0 & Hbb0 & _).
destruct (I_base g pos lyc Sc W memT mdc k hs HPRE HJ Hfrs Hbl)
  as (EFA & Hin4 & HSF0 & HSF1 & HSFapp & HSF64 & Hsp0 & Hsp16 & Hsp47 & Hinb & _ & _ & _ & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & Hnev & _).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (HSTKv : 16720 <= LLVMF_STK) by (clear - HSTK; unfold STK_LLVMF, ASTACK in HSTK; lia).
assert (Hmfr : 0 <= mf < 2 ^ 64) by (clear - Hmf Hsp0 HSTKv C1 Hsp47; lia).
assert (Hspt : spZ regsT = mf) by (unfold spZ; rewrite Rsp; unfold w64; apply unsigned_lit_small; exact Hmfr).
assert (Hs0t : s0Z regsT = e_sp0 g)
  by (unfold s0Z; rewrite Rs0; unfold w64, e_sp0, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HBr : BASE + retk < 2 ^ 64) by (destruct HBASE as (HB0 & HB1 & _); clear - HB0 HB1 Hretk; lia).
assert (Hrat : raZ regsT = BASE + retk) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; lia).
destruct (I_chain g pos lyc Sc W memT mdc k mf HPRE HJ Hmf Vra Vs0) as (ch & Hach & Hsh).
assert (Hch : chain_pre lyc (aview SEGS (w_H W) memT) regsT ch).
{ apply (achain_chain_pre lyc _ mf (e_sp0 g) ch regsT Hach); [rewrite Hspt; clear - Hmf Hsp0 HSTKv; lia | exact Hs0t |].
  rewrite Hrat. clear - HBLO Hretk. lia. }
assert (Hmfree : 0 <= mo_free MT) by exact (mo_free_nonneg MT MTL).
assert (Hmmal : 0 <= mo_malloc MT 256) by exact (mo_malloc_nonneg MT MTL 256 ltac:(lia)).
assert (Hmn : mo_malloc MT n <= mo_malloc MT 256) by exact (mo_malloc_mono MT MTL n 256 ltac:(lia)).
assert (Hmn0 : 0 <= mo_malloc MT n) by exact (mo_malloc_nonneg MT MTL n ltac:(lia)).
assert (Hbsum : blocks_bytes Sc = bsum hs + blocks_bytes (e_S g)).
{ rewrite (blocks_bytes_bsum B lyc Sc), (blocks_bytes_bsum B (e_ly g) (e_S g)).
  destruct Hbl as [Hperm _]. rewrite (bsum_perm _ _ Hperm), bsum_app. reflexivity. }
assert (HU : In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT ch) (as_universe B)).
{ assert (Hin1 : In retk LLVMF_MALLOC_RAS) by exact Hras.
  destruct Hsh as [-> | (fp & v & ->)].
  - apply (llvmf_univ_call0 B _ (LLVMF_MALLOC_CTX RA_LLVMF) regsT HUMM).
    unfold LLVMF_MALLOC_CTX. apply in_or_app. right. apply in_map_iff. exists retk. rewrite Hrat. split; [reflexivity | exact Hin1].
  - apply (llvmf_univ_call B RA_LLVMF _ (LLVMF_MALLOC_CTX RA_LLVMF) regsT fp v HUMM).
    unfold LLVMF_MALLOC_CTX. apply in_or_app. left. apply in_map_iff. exists retk. rewrite Hrat. split; [reflexivity | exact Hin1]. }
eapply SRr_bind.
{ eapply (amalloc04_sub SEGS B LAWS pa_segs_low MT AMALLOC4 W regsT memT LLVMF_STK (e_sp0 g) []
    (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] lyc Sc mdc k n (mf - e_sp0 g)
    (Z_to_bv 64 (BASE + retk)) ch HJ Ha0).
  - unfold MALLOC_MAX. clear - Hn. lia.
  - rewrite Hbsum. unfold LIVE_LLVMF in *. clear - Hlv Hbb0 HLIVE. lia.
  - rewrite Hspt. ring.
  - pose proof (Z.div_mod mf 32 ltac:(lia)) as D1. pose proof (Z.div_mod (e_sp0 g) 16 ltac:(lia)) as D2.
    rewrite Hmf32, Z.add_0_r in D1. rewrite Hsp16, Z.add_0_r in D2.
    replace (mf - e_sp0 g) with ((2 * (mf / 32) - e_sp0 g / 16) * 16) by (clear - D1 D2; lia). apply Z_mod_mult.
  - clear - Hmf. lia.
  - unfold ASTACK. clear - Hmf HSTKv. lia.
  - exact Rgp.
  - exact Rtp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [exact Hretk | exact Hreven].
  - clear - Hnev Hnev0 Hk1 HEV. unfold EV_LLVMF in *. lia.
  - exact Hch.
  - exact HU.
  - apply (mo_ok_le MT MTL Sc (mo_malloc MT n) ((EV_LLVMF - k) * MEV) HMOK).
    assert (X : (EV_LLVMF - k) * MEV = MEV + (EV_LLVMF - (k + 1)) * MEV) by ring.
    assert (Y : 0 <= (EV_LLVMF - (k + 1)) * MEV) by (apply Z.mul_nonneg_nonneg; lia).
    rewrite X. clear - Y Hmn Hmfree. lia. }
cbv beta. intros W3 c3 Hwle (ly3 & S3 & regs3 & mem3 & md3 & res & -> & HJ3 & HP3 & Hres & Hfr3 & Hr4 & Eb3 & HK3 & HM3 & _).
destruct (I_meter (e_S g) Sc S3 k (mo_malloc MT n) 1 Hk0 Hk1 ltac:(lia) ltac:(lia) HMLE HMOK HM3) as [HMLE3 HMOK3].
assert (Hfrs3 : frames S3 = [(4, pos)]) by (rewrite Hfr3; exact Hfrs).
assert (Hbl3 : hblocks B g ly3 S3 ((res, n) :: hs)).
{ destruct Hbl as [Hperm Hfa]. split.
  - rewrite Eb3. eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app]. apply perm_skip. exact Hperm.
  - constructor; [cbn [fst snd]; lia | exact Hfa]. }
replace (e_sp0 g + (mf - e_sp0 g) - ASTACK) with (mf - ASTACK) in HK3 by ring.
replace (e_sp0 g + (mf - e_sp0 g)) with mf in HK3 by ring.
apply (Hk W3 ly3 S3 regs3 mem3 md3 res Hwle HJ3 HP3 Hfrs3 Hres Hr4 Hbl3); [| exact HK3 | exact HMLE3 | exact HMOK3].
destruct (I_base g pos ly3 S3 W3 mem3 md3 (k + 1) ((res, n) :: hs) HPRE HJ3 Hfrs3 Hbl3)
  as (EFA3 & Hin43 & _).
pose proof HJ3 as (HAR3 & _).
destruct (I_blk_apart g pos ly3 S3 W3 mem3 md3 ((res, n) :: hs) res n HPRE HAR3 EFA3 Hin43 Hbl3 (or_introl eq_refl))
  as (_ & _ & _ & _ & _ & Hap).
pose proof HK3 as (K1 & K2 & _ & K4 & _).
apply (I_ikept_of g pos mf lyc Sc W memT W3 mem3 (mf - ASTACK) (fun a => res <= a < res + req_size n) EFA Hin4 Hinb);
  [clear - Hmf Hsp0 HSTKv; lia | exact Hsp47 | | exact K2 | exact K4 | exact Hap].
intros a Ha1 Ha2. apply K1; [exact Ha1 | exact Ha2].
Qed.

(* One call of a program function in the afn_pre / apost_base form from the entry's frame, with sp = mf - o
   (o = 16 when 16 bytes of stack arguments are pushed). The callee counts no allocator event (k = 0). *)
Lemma I_pcall : forall g pos mf (W : world SEGS) (regsT : bvmap 5 word) memT mdc lyc Sc k hs o STK1 FP1 pc retk
  (Post : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (Q : world SEGS -> config -> Prop),
  EPRE g -> AJ g pos lyc Sc W memT mdc k -> frames Sc = [(4, pos)] -> hblocks B g lyc Sc hs ->
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
  val_mem SEGS (rd W memT) (e_sp0 g - 8) 8 RA_LLVMF ->
  val_mem SEGS (rd W memT) (e_sp0 g - 16) 8 (s0Z (e_regs g)) ->
  (o = 0 \/ o = 16) ->
  getr regsT 2 = w64 (mf - o) -> getr regsT 8 = w64 (e_sp0 g) ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  0 <= STK1 <= 8496 ->
  0 <= k -> k <= EV_LLVMF ->
  mo_le MT (e_S g) Sc (k * MEV) -> mo_ok MT Sc ((EV_LLVMF - k) * MEV) ->
  (forall ch, afn_pre SEGS B STK1 lyc Sc W regsT memT mdc ch ->
     SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
       (apost_base SEGS B STK1 FP1 regsT lyc Sc W memT mdc 0 Post)) ->
  (forall a, inFP FP1 a -> in_tmp_block (ablocks B (e_ly g) (e_S g)) (ablocks B lyc Sc) a) ->
  ~ YI16.sink_open_fp FP1 ->
  (forall ly3 S3 W3 regs3 mem3 md3, Post ly3 S3 W3 regs3 mem3 md3 -> Permutation (ablocks B ly3 S3) (ablocks B lyc Sc)) ->
  (forall W3 ly3 S3 regs3 mem3 md3, wle W W3 ->
     AJ g pos ly3 S3 W3 mem3 md3 k -> aregs_preserved regsT regs3 -> frames S3 = [(4, pos)] ->
     hblocks B g ly3 S3 hs ->
     acall_kept SEGS B lyc Sc W memT W3 mem3 (mf - o - STK1) (mf - o) (inFP FP1) ->
     mo_le MT (e_S g) S3 (k * MEV) -> mo_ok MT S3 ((EV_LLVMF - k) * MEV) ->
     Post ly3 S3 W3 regs3 mem3 md3 ->
     SRr SEGS W3 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + retk)) mem3 (seg_rom SEGS)) md3) Q) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc) Q.
Proof.
intros g pos mf W regsT memT mdc lyc Sc k hs o STK1 FP1 pc retk Post Q HPRE HJ Hfrs Hbl Hmf Hmf32 Vra Vs0
  Ho Rsp Rs0 Rgp Rtp Rra Hretk Hreven HSTK1 Hk0 Hk1 HMLE HMOK Hcallee HFP Hcl HPerm Hk.
destruct (I_base g pos lyc Sc W memT mdc k hs HPRE HJ Hfrs Hbl)
  as (EFA & Hin4 & HSF0 & HSF1 & HSFapp & HSF64 & Hsp0 & Hsp16 & Hsp47 & Hinb & _ & _ & _ & _).
pose proof HJ as (HAR & _).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (HSTKv : 16720 <= LLVMF_STK) by (clear - HSTK; unfold STK_LLVMF, ASTACK in HSTK; lia).
assert (Hmfr : 0 <= mf - o < 2 ^ 64) by (clear - Hmf Hsp0 HSTKv C1 Hsp47 Ho; lia).
assert (Hspt : spZ regsT = mf - o) by (unfold spZ; rewrite Rsp; unfold w64; apply unsigned_lit_small; exact Hmfr).
assert (Hs0t : s0Z regsT = e_sp0 g)
  by (unfold s0Z; rewrite Rs0; unfold w64, e_sp0, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HBr : BASE + retk < 2 ^ 64) by (destruct HBASE as (HB0 & HB1 & _); clear - HB0 HB1 Hretk; lia).
assert (Hrat : raZ regsT = BASE + retk) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; lia).
destruct (I_chain g pos lyc Sc W memT mdc k mf HPRE HJ Hmf Vra Vs0) as (ch & Hach & _).
assert (Hal : (mf - o - e_sp0 g) mod 16 = 0).
{ pose proof (Z.div_mod mf 32 ltac:(lia)) as D1. pose proof (Z.div_mod (e_sp0 g) 16 ltac:(lia)) as D2.
  rewrite Hmf32, Z.add_0_r in D1. rewrite Hsp16, Z.add_0_r in D2.
  destruct Ho as [-> | ->];
  [replace (mf - 0 - e_sp0 g) with ((2 * (mf / 32) - e_sp0 g / 16) * 16) by (clear - D1 D2; lia)
  |replace (mf - 16 - e_sp0 g) with ((2 * (mf / 32) - e_sp0 g / 16 - 1) * 16) by (clear - D1 D2; lia)];
  apply Z_mod_mult. }
assert (HPRE1 : afn_pre SEGS B STK1 lyc Sc W regsT memT mdc ch).
{ apply (afn_pre_at SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    lyc Sc W memT mdc k regsT STK1 (mf - o - e_sp0 g) ch HJ).
  - rewrite Hspt. ring.
  - exact Hal.
  - clear - Hmf Ho. lia.
  - lia.
  - clear - Hmf Ho HSTK1 HSTKv. lia.
  - rewrite Rra. apply ret_ok_codeptr_v; [exact Hretk | exact Hreven].
  - rewrite Hrat. clear - HBLO Hretk. lia.
  - exact Rgp.
  - exact Rtp.
  - rewrite Hspt, Hs0t. apply (achain_lower lyc _ mf); [exact Hach | clear - Ho; lia]. }
eapply SRr_bind; [exact (Hcallee ch HPRE1)|].
cbv beta. intros W3 c3 Hwle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HP & HPost).
rewrite Rra.
pose proof HJ1 as (_ & _ & _ & _ & _ & Hfr1 & _).
cbn [app] in Hfr1.
assert (HJ3 : AJ g pos ly3 S3 W3 mem3 md3 k).
{ replace k with (k + 0) by ring. change [(4, pos)] with ([] ++ [(4, pos)]).
  eapply (ajournal_sub SEGS B LAWS pa_segs_low); [exact HJ | exact HJ1 | rewrite Hspt; clear - Hmf HSTK1 HSTKv Ho; lia
  | rewrite Hspt; clear - Hmf Ho; lia |].
  intros a Ha. right. exact (HFP a Ha). }
assert (Hfrs3 : frames S3 = [(4, pos)]) by (rewrite Hfr1; exact Hfrs).
pose proof (HPerm _ _ _ _ _ _ HPost) as HP3.
assert (Hbl3 : hblocks B g ly3 S3 hs).
{ destruct Hbl as [Hperm Hfa]. split; [eapply Permutation_trans; [exact HP3 | exact Hperm] | exact Hfa]. }
assert (HK : acall_kept SEGS B lyc Sc W memT W3 mem3 (mf - o - STK1) (mf - o) (inFP FP1)).
{ rewrite <- Hspt. apply (acall_kept_of_journal SEGS B pa_segs_low STK1 (spZ regsT) FP1 [] lyc Sc W memT mdc
    ly3 S3 W3 mem3 md3 0 (inFP FP1) HJ1 HAR (fun a H => H)); [|exact Hcl].
  intros b m i Hb _ _. exact (Permutation_in _ (Permutation_sym HP3) Hb). }
destruct (I_meter (e_S g) Sc S3 k 0 0 Hk0 ltac:(lia) ltac:(lia) ltac:(lia) HMLE HMOK (HMT0 Sc S3)) as [HMLE3 HMOK3].
rewrite Z.add_0_r in HMLE3, HMOK3.
exact (Hk W3 ly3 S3 regs3 mem3 md3 Hwle HJ3 HP Hfrs3 Hbl3 HK HMLE3 HMOK3 HPost).
Qed.

(* ---- small memory facts (copied from seg_E's e_vm1 / e_vm4 / e_aview_garr8) --------------------------------- *)
Lemma I_vm1 : forall (W : world SEGS) mem a v, aview SEGS (w_H W) mem a = Some v -> val_mem SEGS (rd W mem) a 1 v.
Proof.
intros W mem a v Hv k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r.
unfold aview in Hv. destruct (mbyte SEGS (rd W mem) a) as [b|] eqn:Eb; [|discriminate].
cbn [option_map] in Hv. injection Hv as <-. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. pose proof (bv_unsigned_in_range 8 b) as Hr. unfold bv_wrap.
change (bv_modulus 8) with 256 in *. change (2 ^ 8) with 256.
repeat rewrite (Z.mod_small (bv_unsigned b) 256) by lia. reflexivity.
Qed.
Lemma I_vm4 : forall (W : world SEGS) mem a v, 0 <= v < 256 ->
aview SEGS (w_H W) mem a = Some v ->
aview SEGS (w_H W) mem (a + 1) = Some 0 -> aview SEGS (w_H W) mem (a + 2) = Some 0 ->
aview SEGS (w_H W) mem (a + 3) = Some 0 ->
val_mem SEGS (rd W mem) a 4 v.
Proof.
intros W mem a v Hv H0 H1 H2 H3 k Hk.
assert (Hb : forall x w, aview SEGS (w_H W) mem x = Some w -> mbyte SEGS (rd W mem) x = Some (Z_to_bv 8 w)).
{ intros x w Hx. unfold aview in Hx. destruct (mbyte SEGS (rd W mem) x) as [b|] eqn:Eb; [|discriminate].
  cbn [option_map] in Hx. injection Hx as <-. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range 8 b) as Hr. unfold bv_wrap. change (bv_modulus 8) with 256 in *.
  symmetry; apply Z.mod_small; lia. }
assert (L : forall j, (j < 4)%nat -> YO0f.le_byte v 4 j = (if Nat.eqb j 0 then v else 0)).
{ intros j Hj. unfold YO0f.le_byte. change (8 * Z.of_nat 4) with 32.
  rewrite (Z.mod_small v (2 ^ 32)) by lia.
  destruct j as [|[|[|[|j]]]]; try lia; cbn [Nat.eqb].
  - change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. apply Z.mod_small. lia.
  - change (8 * Z.of_nat 1) with 8. rewrite Z.shiftr_div_pow2 by lia. rewrite (Z.div_small v (2 ^ 8)) by lia. reflexivity.
  - change (8 * Z.of_nat 2) with 16. rewrite Z.shiftr_div_pow2 by lia. rewrite (Z.div_small v (2 ^ 16)) by lia. reflexivity.
  - change (8 * Z.of_nat 3) with 24. rewrite Z.shiftr_div_pow2 by lia. rewrite (Z.div_small v (2 ^ 24)) by lia. reflexivity. }
destruct k as [|[|[|[|k]]]]; try lia.
- rewrite (L 0%nat ltac:(lia)). cbn [Nat.eqb]. rewrite Z.add_0_r. exact (Hb a v H0).
- rewrite (L 1%nat ltac:(lia)). cbn [Nat.eqb]. replace (a + Z.of_nat 1) with (a + 1) by lia. exact (Hb (a + 1) 0 H1).
- rewrite (L 2%nat ltac:(lia)). cbn [Nat.eqb]. replace (a + Z.of_nat 2) with (a + 2) by lia. exact (Hb (a + 2) 0 H2).
- rewrite (L 3%nat ltac:(lia)). cbn [Nat.eqb]. replace (a + Z.of_nat 3) with (a + 3) by lia. exact (Hb (a + 3) 0 H3).
Qed.
Lemma I_aview_garr8 : forall (W : world SEGS) mem a l i,
garr8 SEGS (rd W mem) a l -> 0 <= i < Z.of_nat (length l) ->
aview SEGS (w_H W) mem (a + i) = Some (nth (Z.to_nat i) l 0).
Proof.
intros W mem a l i Hg Hi.
assert (Hj : (Z.to_nat i < length l)%nat) by lia.
pose proof (garr8_mbyte SEGS (rd W mem) a l (Z.to_nat i) Hg Hj) as Hm.
rewrite Z2Nat.id in Hm by lia.
unfold aview. rewrite Hm. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
apply Z.mod_small. exact (proj2 (Hg (Z.to_nat i) Hj)).
Qed.
Lemma I_nth_map_bv : forall (l : list byte) j,
nth j (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof. intros l j. revert l. induction j as [|j IH]; intros [|x l]; cbn; try reflexivity. apply IH. Qed.

(* ---- transfer helpers: a view that is equal on a range carries bytes, shadow and arrays ------------------- *)
Lemma I_garr8_moved : forall (W W' : world SEGS) (m m' : word -> option byte) a l,
(forall k, 0 <= k < Z.of_nat (length l) -> aview SEGS (w_H W') m' (a + k) = aview SEGS (w_H W) m (a + k)) ->
garr8 SEGS (rd W m) a l -> garr8 SEGS (rd W' m') a l.
Proof.
intros W W' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved SEGS (w_H W) (w_H W') m m' (a + Z.of_nat j) (a + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros kk Hkk. replace (a + Z.of_nat j + kk) with (a + (Z.of_nat j + kk)) by lia. apply Hk. lia.
Qed.
Lemma I_zero_shadow_moved : forall (W W' : world SEGS) (m m' : word -> option byte) a n,
(forall i, 0 <= i < n / 8 -> aview SEGS (w_H W') m' (shadow_of_addr SHADOW_OFF a + i) = aview SEGS (w_H W) m (shadow_of_addr SHADOW_OFF a + i)) ->
sh_zero W m a n -> sh_zero W' m' a n.
Proof. intros W W' m m' a n Hk Hz i Hi. unfold sh_zero, zero_shadow in *. rewrite (Hk i Hi). exact (Hz i Hi). Qed.
Lemma I_block_shadow_moved : forall (W W' : world SEGS) (m m' : word -> option byte) a n,
(forall i, 0 <= i < (n + 7) / 8 -> aview SEGS (w_H W') m' (shadow_of_addr SHADOW_OFF a + i) = aview SEGS (w_H W) m (shadow_of_addr SHADOW_OFF a + i)) ->
sh_blk W m a n -> sh_blk W' m' a n.
Proof.
intros W W' m m' a n Hk (H8 & Hn & Hc). split; [exact H8|]. split; [exact Hn|].
intros i Hi. rewrite (Hk i Hi). exact (Hc i Hi).
Qed.

(* ---- the mid-point M1 at 0x81890: the family is in x25, the three capacities and the tail slots survive ----- *)
Definition I_M1 (g : ectx) (pos mf : Z) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 4) (BASE + 0x1184)
(fun ly2 S2 W2 regs2 mem2 md2 =>
id_at g pos (m_nrec g) W2 mem2 /\ mf_id3 g pos mf W2 mem2 /\ mf_id g pos mf W2 mem2 /\
hblocks B g ly2 S2 [] /\
getr regs2 25 = w64 (SlotModel.n_fam (e_pl g)) /\
getr regs2 24 = w64 (SlotModel.t_cap_tok (e_pl g)) /\
getr regs2 26 = w64 (SlotModel.t_cap_name (e_pl g)) /\
getr regs2 27 = w64 (SlotModel.t_cap_disp (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 160) 8 (SlotModel.t_in (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 168) 8 (SlotModel.t_out (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 144) 8 (SlotModel.t_cap_disp (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 136) 8 (SlotModel.t_row (e_pl g))).

(* ecommon at a later state, from the earlier one: the six registers it names are kept, and its bytes (the
   machine frame off the two written slots, the class-4 frame, the input block) are protected by ikept. *)
Lemma I_ecommon_kept : forall g pos mf ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 k3,
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  AJ g pos ly3 S3 W3 mem3 md3 k3 ->
  ikept g pos mf W2 mem2 W3 mem3 ->
  getr regs3 2 = getr regs2 2 -> getr regs3 9 = getr regs2 9 -> getr regs3 8 = getr regs2 8 ->
  getr regs3 3 = getr regs2 3 -> getr regs3 4 = getr regs2 4 -> getr regs3 19 = getr regs2 19 ->
  ECOMMON g pos mf ly3 S3 W3 regs3 mem3 md3.
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 k3 HC HJ3 HK E2 E9 E8 E3 E4 E19.
destruct HC as (R2 & R9 & R8 & Hmfb & Hmf32 & R3 & R4 & R19 & V80 & V192 & V176 & Vra & Vs0 &
  V24 & V32s & V40s & V48s & V56s & V64s & V72s & V80s & V88s & V96s & V104s & Vmf24 & Vflag & HPRE & Hfds & Hfs & Hinb).
pose proof HPRE as (_ & _ & _ & _ & _ & Hlen & _).
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as [Efd Efs].
assert (VS : forall a v, e_sp0 g - 336 + 0 <= mf -> mf <= a -> a + 8 <= e_sp0 g ->
  (forall k, 0 <= k < 8 -> ~ (mf + 152 <= a + k < mf + 160) /\ ~ (mf + 184 <= a + k < mf + 192)) ->
  val_mem SEGS (rd W2 mem2) a 8 v -> val_mem SEGS (rd W3 mem3) a 8 v).
{ intros a v _ Ha1 Ha2 Hh Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W3) mem2 mem3 a a 8 v); [|exact Hv].
  intros kk Hkk. apply HK. left. destruct (Hh kk ltac:(lia)) as [Hh1 Hh2]. split; [lia | split; assumption]. }
unfold ecommon.
split; [rewrite E2; exact R2|]. split; [rewrite E9; exact R9|]. split; [rewrite E8; exact R8|].
split; [exact Hmfb|]. split; [exact Hmf32|].
split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|]. split; [rewrite E19; exact R19|].
split; [apply VS; [lia | lia | lia | intros k Hk; split; intro; lia | exact V80]|].
split; [apply VS; [lia | lia | lia | intros k Hk; split; intro; lia | exact V192]|].
split; [apply VS; [lia | lia | lia | intros k Hk; split; intro; lia | exact V176]|].
split; [apply VS; [lia | lia | lia | intros k Hk; split; intro; lia | exact Vra]|].
split; [apply VS; [lia | lia | lia | intros k Hk; split; intro; lia | exact Vs0]|].
split; [apply VS; [lia | lia | lia | intros k Hk; split; intro; lia | exact V24]|].
split; [apply VS; [lia | lia | lia | intros k Hk; split; intro; lia | exact V32s]|].
split; [apply VS; [lia | lia | lia | intros k Hk; split; intro; lia | exact V40s]|].
split; [apply VS; [lia | lia | lia | intros k Hk; split; intro; lia | exact V48s]|].
split; [apply VS; [lia | lia | lia | intros k Hk; split; intro; lia | exact V56s]|].
split; [apply VS; [lia | lia | lia | intros k Hk; split; intro; lia | exact V64s]|].
split; [apply VS; [lia | lia | lia | intros k Hk; split; intro; lia | exact V72s]|].
split; [apply VS; [lia | lia | lia | intros k Hk; split; intro; lia | exact V80s]|].
split; [apply VS; [lia | lia | lia | intros k Hk; split; intro; lia | exact V88s]|].
split; [apply VS; [lia | lia | lia | intros k Hk; split; intro; lia | exact V96s]|].
split; [apply VS; [lia | lia | lia | intros k Hk; split; intro; lia | exact V104s]|].
split; [apply VS; [lia | lia | lia | intros k Hk; split; intro; lia | exact Vmf24]|].
split.
{ apply (val_mem_moved SEGS (w_H W2) (w_H W3) mem2 mem3 (SFa g pos + 1016) (SFa g pos + 1016) 8 (flag_addr (e_ly g) 4 pos)); [|exact Vflag].
  intros kk Hkk. apply HK. right. left. unfold fzone. left. lia. }
split; [exact HPRE|].
split; [intros fd; rewrite Efd; reflexivity|].
split; [exact Efs|].
unfold bytes_at8 in Hinb |- *.
apply (I_garr8_moved W2 W3 mem2 mem3 (e_p g) _); [|exact Hinb].
intros kk Hkk. apply HK. right. right. unfold inblk. rewrite length_map in Hkk.
split; [rewrite Hlen; lia | lia].
Qed.

(* ikept from "every byte outside [lo, mf) is kept", lo above the allocator's ceiling (the frames, their shadow and
   the heap all lie below it). *)
Lemma I_ikept_out : forall g pos mf ly S (W : world SEGS) m m' mm md k lo,
  AJ g pos ly S W mm md k -> frames S = [(4, pos)] ->
  (0 < e_n g -> In (e_p g, e_n g) (ablocks B ly S)) -> frame_addr ly 4 pos = SFa g pos ->
  alloc_ceiling <= lo -> lo <= mf -> e_sp0 g <= 2 ^ 47 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < mf) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  ikept g pos mf W m W m'.
Proof.
intros g pos mf ly S W m m' mm md k lo HJ Hfrs Hinb EFA Hlo Hlomf Hsp47 HK a Ha.
pose proof HJ as (HAR & _).
assert (Hin : In (4, pos) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hin) as (HF4096 & HFceil & _).
rewrite EFA in HF4096, HFceil. change (fs_frame_bytes 4) with 1024 in *.
pose proof asan_consts as (C1 & _).
assert (R : 0 <= a < 2 ^ 64 /\ ~ (lo <= a < mf)).
{ destruct Ha as [(Ha & _) | [[Ha | Ha] | (Hn & Ha1 & Ha2)]].
  - clear - Ha Hlo Hlomf Hsp47 C1. lia.
  - clear - Ha HF4096 HFceil Hlo C1. lia.
  - clear - Ha HF4096 HFceil Hlo C1. unfold shadow_addr, SHADOW_OFF in Ha. lia.
  - destruct (al_blocks _ _ LAWS ly S W mm md (e_p g) (e_n g) HAR (Hinb Hn)) as (_ & Hp4096 & Hpce & _).
    pose proof (req_size_pos (e_n g) ltac:(lia)) as Hrq. clear - Ha1 Ha2 Hp4096 Hpce C1 Hrq Hlo. lia. }
apply HK; apply R.
Qed.

(* ikept of a plain run that writes only the two frame slots mf+152 / mf+184 (and the stack below mf): every
   protected byte is above or below those, so it is kept. *)
Lemma I_ikept_run : forall g pos mf ly S (W : world SEGS) m m' mm md k,
  AJ g pos ly S W mm md k -> frames S = [(4, pos)] ->
  (0 < e_n g -> In (e_p g, e_n g) (ablocks B ly S)) -> frame_addr ly 4 pos = SFa g pos ->
  alloc_ceiling <= mf -> e_sp0 g <= 2 ^ 47 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 152 <= a < mf + 160) -> ~ (mf + 184 <= a < mf + 192) ->
     aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  ikept g pos mf W m W m'.
Proof.
intros g pos mf ly S W m m' mm md k HJ Hfrs Hinb EFA Hce Hsp47 HK a Ha.
pose proof HJ as (HAR & _).
assert (Hin : In (4, pos) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hin) as (HF4096 & HFceil & _).
rewrite EFA in HF4096, HFceil. change (fs_frame_bytes 4) with 1024 in *.
pose proof asan_consts as (C1 & _).
destruct Ha as [(Ha & Hh1 & Hh2) | [[Ha | Ha] | (Hn & Ha1 & Ha2)]].
- apply HK; [clear - Ha Hce Hsp47 C1; lia | exact Hh1 | exact Hh2].
- apply HK; [clear - Ha HF4096 HFceil Hce C1; lia | clear - Ha HF4096 HFceil Hce C1; lia | clear - Ha HF4096 HFceil Hce C1; lia].
- apply HK; unfold shadow_addr, SHADOW_OFF in Ha; [clear - Ha HF4096 HFceil Hce C1; lia | clear - Ha HF4096 HFceil Hce C1; lia | clear - Ha HF4096 HFceil Hce C1; lia].
- destruct (al_blocks _ _ LAWS ly S W mm md (e_p g) (e_n g) HAR (Hinb Hn)) as (_ & Hp4096 & Hpce & _).
  pose proof (req_size_pos (e_n g) ltac:(lia)) as Hrq.
  apply HK; [clear - Ha1 Ha2 Hp4096 Hpce C1 Hrq Hce; lia | clear - Ha1 Ha2 Hp4096 Hpce C1 Hrq Hce; lia | clear - Ha1 Ha2 Hp4096 Hpce C1 Hrq Hce; lia].
Qed.

(* the same for a run that also writes the 16 bytes of stack arguments [mf - 16, mf) *)
Lemma I_ikept_run16 : forall g pos mf ly S (W : world SEGS) m m' mm md k,
  AJ g pos ly S W mm md k -> frames S = [(4, pos)] ->
  (0 < e_n g -> In (e_p g, e_n g) (ablocks B ly S)) -> frame_addr ly 4 pos = SFa g pos ->
  alloc_ceiling + 16 <= mf -> e_sp0 g <= 2 ^ 47 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 152 <= a < mf + 160) -> ~ (mf + 184 <= a < mf + 192) ->
     ~ (mf - 16 <= a < mf) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  ikept g pos mf W m W m'.
Proof.
intros g pos mf ly S W m m' mm md k HJ Hfrs Hinb EFA Hce Hsp47 HK a Ha.
pose proof HJ as (HAR & _).
assert (Hin : In (4, pos) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hin) as (HF4096 & HFceil & _).
rewrite EFA in HF4096, HFceil. change (fs_frame_bytes 4) with 1024 in *.
pose proof asan_consts as (C1 & _).
destruct Ha as [(Ha & Hh1 & Hh2) | [[Ha | Ha] | (Hn & Ha1 & Ha2)]].
- apply HK; [clear - Ha Hce Hsp47 C1; lia | exact Hh1 | exact Hh2 | clear - Ha; lia].
- apply HK; clear - Ha HF4096 HFceil Hce C1; lia.
- apply HK; unfold shadow_addr, SHADOW_OFF in Ha; clear - Ha HF4096 HFceil Hce C1; lia.
- destruct (al_blocks _ _ LAWS ly S W mm md (e_p g) (e_n g) HAR (Hinb Hn)) as (_ & Hp4096 & Hpce & _).
  pose proof (req_size_pos (e_n g) ltac:(lia)) as Hrq.
  apply HK; clear - Ha1 Ha2 Hp4096 Hpce C1 Hrq Hce; lia.
Qed.

(* The read-only image of any state the walk reaches (seg_E's e_rod). *)
Lemma I_rod : forall g pos ly2 S2 (W2 : world SEGS) m md k,
AJ g pos ly2 S2 W2 m md k -> EPRE g -> arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) m).
Proof.
intros g pos ly2 S2 W2 m md k HJ HPRE.
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROS & _).
eapply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img); [exact HJ | apply HRO; exact HROS].
Qed.

(* id's bytes and shadow live in the class-4 frame and its shadow: a step that keeps those keeps id_at. *)
Lemma I_id_at_moved : forall g pos i (W W' : world SEGS) (m m' : word -> option byte),
  4096 <= SFa g pos -> SFa g pos mod 64 = 0 ->
  (forall a, fzone g pos a -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  id_at g pos i W m -> id_at g pos i W' m'.
Proof.
intros g pos i W W' m m' HSF0 HSF64 HK. unfold id_at, bytes_at8. intros (Hb & Hz & Hk). split; [|split].
- apply (I_garr8_moved W W' m m' _ _); [|exact Hb].
  intros kk Hkk. rewrite length_map in Hkk. unfold m_id in Hkk. rewrite SlotModel.rec_id_length in Hkk.
  unfold RcIdentModel.ID_SIZE in Hkk. apply HK. left. unfold V_id. lia.
- apply (I_zero_shadow_moved W W' m m' _ _); [|exact Hz].
  intros ii Hii. apply HK. right. unfold shadow_of_addr, shadow_addr, V_id, N_id in *. lia.
- apply (I_block_shadow_moved W W' m m' _ _); [|exact Hk].
  intros ii Hii. apply HK. right. unfold shadow_of_addr, shadow_addr, V_id, N_id in *. lia.
Qed.

#[local] Notation IHE := (inv_H_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation IIE := (inv_I_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).

(* env for the head state at 0x116c (atom 32 = &id + 3, atom 33 = &id) *)
Definition EH (regs : bvmap 5 word) (F : Z) : env := Eimg (Ereg regs (map (Z_to_bv 64) [F + V_id + 3; F + V_id])).

Theorem I_head : forall g pos mf W2 c2, IHE g pos mf W2 c2 -> SRr SEGS W2 c2 (I_M1 g pos mf).
Proof.
intros g pos mf W2 c2 Hstart.
unfold inv_H_end, acut in Hstart.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hkrange & MLE & MOK & HC & HP).
pose proof HC as (R2 & R9 & R8 & Hmfb & Hmf32 & R3 & R4 & R19 & V80 & V192 & V176 & Vra & Vs0 &
  V24 & V32s & V40s & V48s & V56s & V64s & V72s & V80s & V88s & V96s & V104s & Vmf24 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HP as (Hid & Hbl & Hmid3 & Hmid & Hef & V136 & V144 & V160 & V168 & R11 & R23 & R24 & R26 & R27).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HSTK as HSTK'. unfold STK_LLVMF, ASTACK in HSTK'.
set (sp0 := e_sp0 g) in *. set (SF := SFa g pos) in *. set (inp := e_pl g) in *.
set (nrec := m_nrec g) in *.
destruct (I_base g pos ly2 S2 W2 mem2 md2 (4 * Z.of_nat nrec + 4) [] HPRE HJ Hfrs Hbl)
  as (EFA & Hin4 & HSF0 & HSF1 & HSFapp & HSF64 & Hsp0al & Hsp16 & Hsp47 & Hinbk & _ & HFpres & HFSpres & _).
fold sp0 SF in HSF0, HSF1, HSFapp, HSF64, Hsp0al, Hsp16, Hsp47, HFpres, HFSpres, EFA.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hsp0al HSTK'; fold sp0 in Hmfb; lia).
(* the model's family facts *)
pose proof (SlotModel.nrec_range inp) as Hnr.
pose proof (IM.n_fam_range inp) as Hnfr. fold inp in Hnfr.
assert (Hfrawr : 0 <= SlotModel.t_fam_raw inp < 256) by (apply SlotModel.inb_range).
(* the environment at 0x116c *)
remember (Eimg (Ereg regs2 (map (Z_to_bv 64) [SF + V_id + 3; SF + V_id]))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (SF + V_id + 3))
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (SF + V_id))
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
assert (AGE : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) [SF + V_id + 3; SF + V_id])) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), R9. apply unsigned_lit_small. clear - Hmf0 Hsp47 Hmfb C1. fold sp0 in Hmfb. lia. }
assert (HS : st_ok_pi SEGS VAL E ss_IH
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x116c)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_IH. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold I_rH, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [clear - Hmf0 C1; lia|]. split; [clear - Hmf0 Hsp47 Hmfb C1; fold sp0 in Hmfb; lia|].
    split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    + apply (chunk_ok_val SEGS E _ mf 128 8 (SOff 32 0) (SF + V_id + 3));
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | clear - HSF0 HSF1 C1; unfold V_id; lia | lia | exact Hmid3].
    + apply (chunk_ok_val SEGS E _ mf 184 8 (SOff 33 0) (SF + V_id));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | clear - HSF0 HSF1 C1; unfold V_id; lia | lia | exact Hmid].
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I]. }
unfold cfg_at. change (w64 (BASE + 0x116c)) with (Z_to_bv 64 (BASE + 0x116c)).
(* a1 = t_fam_raw * 2^56 *)
assert (EA1 : ew E 11 = Z_to_bv 64 (SlotModel.t_fam_raw inp * 2 ^ 56))
  by (rewrite (EE 11%nat 11%bv eq_refl); fold inp in R11; rewrite R11; reflexivity).
eapply (paj_branch W2 E ss_IH _ _ _ BC_LT (SOff 11 0) (SLit 0) HS).
- (* taken: t_fam_raw >= 128; s9 = t_fam_raw & 127 = n_fam, memory unchanged *)
  intros Hbt HSc. clear HS. rewrite (I_bltz E 11 (SlotModel.t_fam_raw inp) EA1 Hfrawr) in Hbt. apply Z.leb_le in Hbt.
  paj_run_to_sh RUNTOP HSc HJ 0x1184. { intros a (r & Hin & Hr). cbv [add_cond ss_IH ss_mem] in Hin; cbn [In] in Hin; destruct Hin as [Heq | []]; subst r. cbn [I_rH YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
  { apply (aview_kept_frame E _ (w_H W2) mem2 (ms_mem ms) 0 HFr ltac:(lia)).
    intros a _ (r & Hin & Hr). cbv [add_cond ss_IH ss_mem] in Hin; cbn [In] in Hin; destruct Hin as [Heq | []]; subst r.
    cbn [I_rH YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
  prreg HSc (25%bv : bv 5) Q25. prreg HSc (24%bv : bv 5) Q24. prreg HSc (26%bv : bv 5) Q26. prreg HSc (27%bv : bv 5) Q27.
  rewrite (EE 23%nat 23%bv eq_refl) in Q25. fold inp in R23. rewrite R23 in Q25. unfold w64 in Q25.
  rewrite (I_and_lit (SlotModel.t_fam_raw inp) 127 ltac:(lia) ltac:(lia)) in Q25.
  rewrite (EE 24%nat 24%bv eq_refl), R24 in Q24. rewrite (EE 26%nat 26%bv eq_refl), R26 in Q26.
  rewrite (EE 27%nat 27%bv eq_refl), R27 in Q27.
  apply SRr_ret. unfold I_M1, acut. pmkst HSc.
  exists ly2, S2, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md2) mat md2).
  split; [reflexivity|].
  split; [exact HJ|].
  split; [exact Hfrs|]. split; [exact Hkrange|]. split; [exact MLE|]. split; [exact MOK|].
  assert (HIK : ikept g pos mf W2 mem2 W2 (ms_mem ms)).
  { intros a Ha. apply KEEP. destruct Ha as [(Ha & _) | [[Ha | Ha] | (Hn & Ha1 & Ha2)]].
    - clear - Ha Hmf0 Hsp47 C1. lia.
    - clear - Ha HSF0 HSF1 C1. lia.
    - clear - Ha HSF0 HSF1 C1. unfold shadow_addr, SHADOW_OFF in Ha. lia.
    - destruct (al_blocks _ _ LAWS ly2 S2 W2 _ _ (e_p g) (e_n g) (proj1 HJ) (Hinbk Hn)) as (_ & Hp4096 & Hpce & _).
      pose proof (req_size_pos (e_n g) ltac:(lia)). clear - Ha1 Ha2 Hp4096 Hpce C1 H. lia. }
  prreg HSc (2%bv : bv 5) P2. prreg HSc (9%bv : bv 5) P9. prreg HSc (8%bv : bv 5) P8.
  prreg HSc (3%bv : bv 5) P3. prreg HSc (4%bv : bv 5) P4. prreg HSc (19%bv : bv 5) P19.
  rewrite (EE 2%nat 2%bv eq_refl) in P2. rewrite (EE 9%nat 9%bv eq_refl) in P9. rewrite (EE 8%nat 8%bv eq_refl) in P8.
  rewrite (EE 3%nat 3%bv eq_refl) in P3. rewrite (EE 4%nat 4%bv eq_refl) in P4. rewrite (EE 19%nat 19%bv eq_refl) in P19.
  split; [exact (I_ecommon_kept g pos mf ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms)
    (with_vm_backing (m_vm_lazy md2) mat md2) (4 * Z.of_nat nrec + 4) HC HJ HIK P2 P9 P8 P3 P4 P19)|].
  assert (VMk : forall a (n : nat) v, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
    val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 (ms_mem ms)) a n v).
  { intros a n v Ha0 Ha1 Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms) a a n v); [|exact Hv].
    intros kk Hkk. apply KEEP. lia. }
  assert (GFk : forall a l, 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
    garr8 SEGS (rd W2 mem2) a l -> garr8 SEGS (rd W2 (ms_mem ms)) a l).
  { intros a l Ha0 Ha1 Hg. apply (I_garr8_moved W2 W2 mem2 (ms_mem ms) a l); [|exact Hg].
    intros kk Hkk. apply KEEP. lia. }
  split.
  { unfold id_at, bytes_at8 in Hid |- *. destruct Hid as (Hidb & Hidz & Hidk). split; [|split].
    - apply GFk; [clear - HSF0; unfold V_id; lia | | exact Hidb].
      rewrite length_map. unfold m_id. fold inp. rewrite SlotModel.rec_id_length. unfold V_id, RcIdentModel.ID_SIZE.
      clear - HSF0 HSF1 C1; lia.
    - apply (I_zero_shadow_moved W2 W2 mem2 (ms_mem ms) (SF + V_id) N_id); [|exact Hidz].
      intros i Hi. apply KEEP. unfold shadow_of_addr. clear - Hi HSF0 HSF1 C1; unfold N_id, SHADOW_OFF, V_id in *; lia.
    - apply (I_block_shadow_moved W2 W2 mem2 (ms_mem ms) (SF + V_id) N_id); [|exact Hidk].
      intros i Hi. apply KEEP. unfold shadow_of_addr. clear - Hi HSF0 HSF1 C1; unfold N_id, SHADOW_OFF, V_id in *; lia. }
  split; [unfold mf_id3 in Hmid3 |- *; apply VMk; [clear - Hmf0 C1; lia | clear - Hmf0 Hsp47 Hmfb C1; fold sp0 in Hmfb; lia | exact Hmid3]|].
  split; [unfold mf_id in Hmid |- *; apply VMk; [clear - Hmf0 C1; lia | clear - Hmf0 Hsp47 Hmfb C1; fold sp0 in Hmfb; lia | exact Hmid]|].
  split; [exact Hbl|].
  split; [rewrite Q25; unfold w64; f_equal; unfold SlotModel.n_fam;
    replace (128 <=? SlotModel.t_fam_raw (e_pl g)) with true by (symmetry; apply Z.leb_le; exact Hbt); reflexivity|].
  split; [rewrite Q24; reflexivity|]. split; [rewrite Q26; reflexivity|]. split; [rewrite Q27; reflexivity|].
  split; [apply VMk; [clear - Hmf0 C1; lia | clear - Hmf0 Hsp47 Hmfb C1; fold sp0 in Hmfb; lia | exact V160]|].
  split; [apply VMk; [clear - Hmf0 C1; lia | clear - Hmf0 Hsp47 Hmfb C1; fold sp0 in Hmfb; lia | exact V168]|].
  split; [apply VMk; [clear - Hmf0 C1; lia | clear - Hmf0 Hsp47 Hmfb C1; fold sp0 in Hmfb; lia | exact V144]|].
  apply VMk; [clear - Hmf0 C1; lia | clear - Hmf0 Hsp47 Hmfb C1; fold sp0 in Hmfb; lia | exact V136].
- (* not taken: t_fam_raw < 128; family_of returns FAM id = n_fam *)
  intros Hbf HSc. clear HS. rewrite (I_bltz E 11 (SlotModel.t_fam_raw inp) EA1 Hfrawr) in Hbf. apply Z.leb_gt in Hbf.
  lazymatch type of HSc with st_ok_pi _ _ _ ?s _ => let v := eval vm_compute in s in change s with v in HSc end.
  paj_run_shc RUNP RUNC HSc HJ.
  { intros a (r & Hin & Hr). cbn [In] in Hin. destruct Hin as [Heq | []]; subst r.
    cbn [YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
  { apply (aview_kept_frame E _ (w_H W2) mem2 (ms_mem ms) 0 HFr ltac:(lia)).
    intros a _ (r & Hin & Hr). cbn [In] in Hin. destruct Hin as [Heq | []]; subst r.
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
  clear HF HFr HG.
  prreg HSc (10%bv : bv 5) P10. prreg HSc (2%bv : bv 5) P2. prreg HSc (8%bv : bv 5) P8.
  prreg HSc (3%bv : bv 5) P3. prreg HSc (4%bv : bv 5) P4. prreg HSc (1%bv : bv 5) P1.
  rewrite E33 in P10.
  rewrite (EE 2%nat 2%bv eq_refl), R2 in P2. rewrite (EE 8%nat 8%bv eq_refl), R8 in P8.
  rewrite (EE 3%nat 3%bv eq_refl), R3 in P3. rewrite (EE 4%nat 4%bv eq_refl), R4 in P4.
  pmkst HSc. rewrite (PSIG IS_reac_box_family_of AF_reac_box_family_of eq_refl).
  assert (WS : reac_box_family_of.REAC_BOX_FAMILY_OF_STK = 8256) by reflexivity.
  pose proof (I_rod g pos ly2 S2 W2 (ms_mem ms) _ _ HJ HPRE) as HROD.
  destruct (HIMG W2 (ms_mem ms) HROD) as (_ & _ & _ & _ & Hg16 & _).
  assert (Htb : forall i, 0 <= i < 36 ->
    aview SEGS (w_H W2) (ms_mem ms) (VAL (A_OBJ 16) + i) = Some (nth (Z.to_nat i) HW_ROWS 0))
    by (intros i Hi; apply (I_aview_garr8 W2 (ms_mem ms) _ HW_ROWS i Hg16); change (length HW_ROWS) with 36%nat; lia).
  assert (FZ1 : forall a, fzone g pos a -> aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha. apply KEEP. unfold fzone in Ha. fold SF in Ha.
    destruct Ha as [Ha | Ha]; [clear - Ha HSF0 HSF1 C1; lia | clear - Ha HSF0 HSF1 C1; unfold shadow_addr, SHADOW_OFF in Ha; lia]. }
  pose proof (I_id_at_moved g pos nrec W2 W2 mem2 (ms_mem ms) HSF0 HSF64 FZ1 Hid) as Hid1.
  pose proof Hid1 as (Hidb1 & _ & Hidk1). unfold bytes_at8 in Hidb1. fold SF in Hidb1, Hidk1.
  assert (Hidv : forall i, 0 <= i < 38 -> aview SEGS (w_H W2) (ms_mem ms) (SF + V_id + i) =
    Some (RcIdentModel.bz (nth (Z.to_nat i) (m_id g nrec) (RcIdentModel.zb 0)))).
  { intros i Hi. rewrite (I_aview_garr8 W2 (ms_mem ms) _ _ i Hidb1).
    - rewrite I_nth_map_bv. reflexivity.
    - rewrite length_map. unfold m_id. rewrite SlotModel.rec_id_length. unfold RcIdentModel.ID_SIZE. lia. }
  assert (Rsp0 : getr (ms_regs ms) 2 = w64 (mf - 0)) by (rewrite P2; f_equal; lia).
  assert (VraM : val_mem SEGS (rd W2 (ms_mem ms)) (sp0 - 8) 8 RA_LLVMF).
  { apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms) (sp0 - 8) (sp0 - 8) 8 RA_LLVMF); [|exact Vra].
    intros kk Hkk. apply KEEP. clear - Hkk Hmf0 Hsp47 Hmfb C1. lia. }
  assert (Vs0M : val_mem SEGS (rd W2 (ms_mem ms)) (sp0 - 16) 8 (s0Z (e_regs g))).
  { apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms) (sp0 - 16) (sp0 - 16) 8 _); [|exact Vs0].
    intros kk Hkk. apply KEEP. clear - Hkk Hmf0 Hsp47 Hmfb C1. lia. }
  eapply (I_pcall g pos mf W2 (ms_regs ms) (ms_mem ms) _ ly2 S2 (4 * Z.of_nat nrec + 4) [] 0
    reac_box_family_of.REAC_BOX_FAMILY_OF_STK [] (BASE + AF_reac_box_family_of) 0x1178 _ (I_M1 g pos mf)
    HPRE HJ Hfrs Hbl Hmfb Hmf32 VraM Vs0M (or_introl eq_refl) Rsp0 P8 P3 P4 P1).
  + lia.
  + reflexivity.
  + rewrite WS. lia.
  + clear - Hkrange. lia.
  + clear - Hkrange. lia.
  + exact MLE.
  + exact MOK.
  + intros ch HPRE1. apply (HFAM ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ ch (SF + V_id) 1 2 3 HPRE1 P10).
    * unfold V_id. clear - HSF0 HSF1 C1. lia.
    * intros _. right. split; [|split].
      ** exists 4, pos. rewrite EFA. change (fs_frame_bytes 4) with 1024. unfold V_id.
        split; [exact Hin4|]. split; [lia|]. split; [clear - HSF64; lia|]. split; lia.
      ** unfold V_id. clear - HSF64. lia.
      ** apply (block_shadow_range _ SHADOW_OFF (SF + V_id) N_id); [exact Hidk1 | lia | unfold N_id; lia].
    * unfold reac_box_family_of.famof_tbl, reac_box_family_of.FAMOF_HWF.
      split; [intros a Ha; replace a with (VAL (A_OBJ 16) + (a - VAL (A_OBJ 16))) by lia;
        rewrite (Htb (a - VAL (A_OBJ 16))) by lia; discriminate|].
      split; [lia|]. split.
      { apply (I_vm4 W2 (ms_mem ms) (VAL (A_OBJ 16)) 1); [lia | | | |].
        - rewrite <- (Z.add_0_r (VAL (A_OBJ 16))) at 1. apply (Htb 0). lia.
        - apply (Htb 1). lia.
        - apply (Htb 2). lia.
        - apply (Htb 3). lia. }
      split; [lia|]. split.
      { apply (I_vm4 W2 (ms_mem ms) (VAL (A_OBJ 16) + 12) 2); [lia | | | |].
        - apply (Htb 12). lia.
        - replace (VAL (A_OBJ 16) + 12 + 1) with (VAL (A_OBJ 16) + 13) by lia. apply (Htb 13). lia.
        - replace (VAL (A_OBJ 16) + 12 + 2) with (VAL (A_OBJ 16) + 14) by lia. apply (Htb 14). lia.
        - replace (VAL (A_OBJ 16) + 12 + 3) with (VAL (A_OBJ 16) + 15) by lia. apply (Htb 15). lia. }
      split; [lia|].
      { apply (I_vm4 W2 (ms_mem ms) (VAL (A_OBJ 16) + 24) 3); [lia | | | |].
        - apply (Htb 24). lia.
        - replace (VAL (A_OBJ 16) + 24 + 1) with (VAL (A_OBJ 16) + 25) by lia. apply (Htb 25). lia.
        - replace (VAL (A_OBJ 16) + 24 + 2) with (VAL (A_OBJ 16) + 26) by lia. apply (Htb 26). lia.
        - replace (VAL (A_OBJ 16) + 24 + 3) with (VAL (A_OBJ 16) + 27) by lia. apply (Htb 27). lia. }
  + intros a (rr & Hr & _). destruct Hr.
  + apply sink_closed_pos. constructor.
  + intros ly3 S3 W3 regs3 mem3 md3 (-> & -> & _). apply Permutation_refl.
  + intros W3 ly3 S3 regs3 mem3 md3 Hwle HJ3 HP3 Hfrs3 Hbl3 HK3 MLE3 MOK3 HPost.
    destruct HPost as (-> & -> & -> & Hkeep & r & Hres & R10r).
    jafter_call_keep_hi HSc 512%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0%nat] HS3.
    match type of HS3 with ?Q -> _ => assert (HQ : Q); [|specialize (HS3 HQ); clear HQ] end.
    { cbn [ms_mem restrict]. constructor; [|constructor].
      eapply (region_kept_stack_aj SEGS B); [exact HK3 | exact HJ3 | exact U9 | lia | lia | lia | lia | lia]. }
    rewrite <- restrict_mkst_fx in HS3.
    pose proof (img_env_havoc_hi E 512%nat (map (getr regs3) CLOB) HEI ltac:(cbv; lia)) as HEI3.
    paj_run_to_sh RUNTOP HS3 HJ3 0x1184.
    { intros a (r0 & Hin & Hr). cbn [In] in Hin. destruct Hin as [Heq | []]; subst r0.
      cbn [YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
    assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem3 a).
    { apply (aview_kept_frame _ _ (w_H W2) mem3 (ms_mem ms0) 0 HFr ltac:(lia)).
      intros a _ (r0 & Hin & Hr). cbn [In] in Hin. destruct Hin as [Heq | []]; subst r0.
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
    clear HF HFr HG.
    prreg HS3 (25%bv : bv 5) Q25. prreg HS3 (24%bv : bv 5) Q24. prreg HS3 (26%bv : bv 5) Q26.
    prreg HS3 (27%bv : bv 5) Q27.
    prreg HS3 (2%bv : bv 5) S2r. prreg HS3 (9%bv : bv 5) S9r. prreg HS3 (8%bv : bv 5) S8r.
    prreg HS3 (3%bv : bv 5) S3r. prreg HS3 (4%bv : bv 5) S4r. prreg HS3 (19%bv : bv 5) S19r.
    rewrite (EE 24%nat 24%bv eq_refl), R24 in Q24. rewrite (EE 26%nat 26%bv eq_refl), R26 in Q26.
    rewrite (EE 27%nat 27%bv eq_refl), R27 in Q27.
    rewrite (EE 2%nat 2%bv eq_refl) in S2r. rewrite (EE 9%nat 9%bv eq_refl) in S9r. rewrite (EE 8%nat 8%bv eq_refl) in S8r.
    rewrite (EE 3%nat 3%bv eq_refl) in S3r. rewrite (EE 4%nat 4%bv eq_refl) in S4r. rewrite (EE 19%nat 19%bv eq_refl) in S19r.
    cbv [CLOB] in Q25. cbn [map nth] in Q25. rewrite R10r in Q25.
    (* the family: r = FAM (idT inp) = n_fam inp *)
    assert (Hr : r = SlotModel.FAM (SlotModel.idT inp)).
    { apply (IM.FAM_res (aview SEGS (w_H W2) (ms_mem ms)) (SF + V_id) (VAL (A_OBJ 16)) (SlotModel.idT inp) r).
      - unfold SlotModel.idT. rewrite SlotModel.rec_id_length. reflexivity.
      - unfold V_id. clear - HSF0. lia.
      - intros j Hj. exact (Hidv j Hj).
      - exact Htb.
      - exact Hres. }
    assert (Hsx : reac_box_family_of.famof_sx32 r = SlotModel.n_fam inp).
    { pose proof (IM.FAM_range (SlotModel.idT inp)) as Hfr. unfold SlotModel.n_fam.
      replace (128 <=? SlotModel.t_fam_raw inp) with false by (symmetry; apply Z.leb_gt; exact Hbf).
      rewrite Hr. unfold reac_box_family_of.famof_sx32.
      destruct (Z.ltb_spec (SlotModel.FAM (SlotModel.idT inp)) (2 ^ 31)); [reflexivity | lia]. }
    rewrite Hsx in Q25.
    (* every byte outside the callee's stack window [mf - 8256, mf) is the one at 0x81878 *)
    assert (Usp : spZ (ms_regs ms) = mf).
    { unfold spZ. rewrite P2. unfold w64. apply unsigned_lit_small. clear - Hmf0 Hsp47 Hmfb C1. lia. }
    assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 8256 <= a < mf) ->
      aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
    { intros a Ha Hw. rewrite (KEEP2 a Ha), Hkeep; [exact (KEEP a Ha) | exact Ha |].
      rewrite Usp, WS. exact Hw. }
    assert (VMk : forall a (n : nat) v, mf <= a -> a + Z.of_nat n <= 2 ^ 64 ->
      val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 (ms_mem ms0)) a n v).
    { intros a n v Ha0 Ha1 Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms0) a a n v); [|exact Hv].
      intros kk Hkk. apply KALL; clear - Ha0 Ha1 Hkk Hmf0 C1; lia. }
    assert (HIK : ikept g pos mf W2 mem2 W2 (ms_mem ms0)).
    { apply (I_ikept_out g pos mf ly2 S2 W2 mem2 (ms_mem ms0) _ _ _ (mf - 8256) HJ Hfrs Hinbk EFA);
        [clear - Hmf0 C1; lia | lia | exact Hsp47 | exact KALL]. }
    apply SRr_ret. unfold I_M1, acut. pmkst HS3.
    eexists ly2, S2, _, _, _. split; [reflexivity|].
    split; [exact HJ3|].
    split; [exact Hfrs|]. split; [exact Hkrange|]. split; [exact MLE|]. split; [exact MOK|].
    split; [exact (I_ecommon_kept g pos mf ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 _ _ _ _ HC HJ3 HIK
      S2r S9r S8r S3r S4r S19r)|].
    split; [exact (I_id_at_moved g pos nrec W2 W2 mem2 (ms_mem ms0) HSF0 HSF64
      (fun a Ha => HIK a (or_intror (or_introl Ha))) Hid)|].
    split; [unfold mf_id3 in Hmid3 |- *; apply VMk; [clear; lia | clear - Hmf0 Hsp47 Hmfb C1; lia | exact Hmid3]|].
    split; [unfold mf_id in Hmid |- *; apply VMk; [clear; lia | clear - Hmf0 Hsp47 Hmfb C1; lia | exact Hmid]|].
    split; [exact Hbl|].
    split; [exact Q25|].
    split; [exact Q24|]. split; [exact Q26|]. split; [exact Q27|].
    split; [apply VMk; [clear; lia | clear - Hmf0 Hsp47 Hmfb C1; lia | exact V160]|].
    split; [apply VMk; [clear; lia | clear - Hmf0 Hsp47 Hmfb C1; lia | exact V168]|].
    split; [apply VMk; [clear; lia | clear - Hmf0 Hsp47 Hmfb C1; lia | exact V144]|].
    apply VMk; [clear; lia | clear - Hmf0 Hsp47 Hmfb C1; lia | exact V136].
Qed.

(* a0 after a call, from the havoc the call's model makes of the caller-saved registers *)
Lemma I_ew_a0 : forall E k (regs : bvmap 5 word),
  ew (havoc E k (map (getr regs) CLOB)) (k + 4) = getr regs 10.
Proof.
intros E k regs.
rewrite (ew_havoc_new E k (map (getr regs) CLOB) 4 (getr regs 10)) by (cbv [CLOB]; cbn [map length]; lia).
cbv [CLOB]. cbn [map nth]. reflexivity.
Qed.
Lemma I_hblocks_perm : forall g ly S hs hs', Permutation hs hs' -> hblocks B g ly S hs -> hblocks B g ly S hs'.
Proof.
intros g ly S hs hs' HP [H1 H2]. split.
- eapply Permutation_trans; [exact H1|]. apply Permutation_app_tail. exact HP.
- rewrite Forall_forall in *. intros x Hx. apply H2. exact (Permutation_in _ (Permutation_sym HP) Hx).
Qed.

(* The two frame regions after malloc 1 (base atom 9 = mf; windows mf+152 and mf+184): a run's writes and the
   bytes it keeps. *)
Local Ltac i_awr2 U Hm HS' Hsa Hm0 Cc s0 :=
  intros a (r & Hin & Hr); cbn [In] in Hin; destruct Hin as [Heq | [Heq | []]]; subst r;
  cbn [I_r0 I_r1 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite U in Hr;
  left; clear - Hr Hm HS' Hsa Hm0 Cc; fold s0 in Hm; lia.
Local Ltac i_keep2 HFr U :=
  intros a Ha H1 H2; apply aview_eq_of; apply HFr; rewrite unsigned_lit_small by lia;
  intros (r & Hin & Hr); cbn [In] in Hin; destruct Hin as [Heq | [Heq | []]]; subst r;
  cbn [I_r0 I_r1 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite U in Hr; lia.

(* The stem table's three entries, with the range the walk needs to refute `beqz a0` at 0x8189c.
   llvmf_img (LLVMFuzzerTestOneInput.v:272, its object-17 block at :289-292) stated only t <> 0; val_mem does
   not bound its value, so t mod 2 ^ 64 = 0 was not excluded; the range at :293 is what I_stem_tbl reads off. *)
Definition I_stem_tbl_r : Prop := forall (W : world SEGS) mem,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  exists t1 t2 t3,
    val_mem SEGS (rd W mem) (VAL (A_OBJ 17)) 8 t1 /\
    val_mem SEGS (rd W mem) (VAL (A_OBJ 17) + 8) 8 t2 /\
    val_mem SEGS (rd W mem) (VAL (A_OBJ 17) + 16) 8 t3 /\
    0 < t1 < 2 ^ 64 /\ 0 < t2 < 2 ^ 64 /\ 0 < t3 < 2 ^ 64.

Lemma I_stem_tbl : I_stem_tbl_r.
Proof.
intros W mem HROD.
destruct (HIMG W mem HROD)
  as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (t1 & t2 & t3 & V1 & V2 & V3 & Q1 & Q2 & Q3) & _).
exists t1, t2, t3. split; [exact V1|]. split; [exact V2|]. split; [exact V3|].
split; [exact Q1|]. split; [exact Q2 | exact Q3].
Qed.

Theorem I_tail : forall g pos mf W2 c2, I_M1 g pos mf W2 c2 ->
  SRr SEGS W2 c2 (fun W3 c3 => exists nm tk dp, IIE g pos mf nm tk dp W3 c3).
Proof.
intros g pos mf W2 c2 Hstart.
unfold I_M1, acut in Hstart.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hkrange & MLE & MOK & HC & HP).
pose proof HC as (R2 & R9 & R8 & Hmfb & Hmf32 & R3 & R4 & R19 & V80 & V192 & V176 & Vra & Vs0 &
  V24 & V32s & V40s & V48s & V56s & V64s & V72s & V80s & V88s & V96s & V104s & Vmf24 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HP as (Hid & Hmid3 & Hmid & Hbl & R25 & R24 & R26 & R27 & V160 & V168 & V144 & V136).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HSTK as HSTK'. unfold STK_LLVMF, ASTACK in HSTK'.
set (sp0 := e_sp0 g) in *. set (SF := SFa g pos) in *. set (inp := e_pl g) in *. set (nrec := m_nrec g) in *.
destruct (I_base g pos ly2 S2 W2 mem2 md2 (4 * Z.of_nat nrec + 4) [] HPRE HJ Hfrs Hbl)
  as (EFA & Hin4 & HSF0 & HSF1 & HSFapp & HSF64 & Hsp0al & Hsp16 & Hsp47 & Hinbk & Hlen & HFpres & HFSpres & Hstkpres).
fold sp0 SF in HSF0, HSF1, HSFapp, HSF64, Hsp0al, Hsp16, Hsp47, HFpres, HFSpres, EFA, Hstkpres.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hsp0al HSTK'; fold sp0 in Hmfb; lia).
(* the model's ranges *)
pose proof (SlotModel.nrec_range inp) as Hnr.
pose proof (IM.n_fam_range inp) as Hnfr. fold inp in Hnfr.
assert (Hnr64 : Z.of_nat nrec <= 64).
{ unfold nrec, m_nrec, SlotModel.nrecn. fold inp. rewrite Z2Nat.id by lia. lia. }
assert (Hcn : 0 <= SlotModel.t_cap_name inp < 40) by (unfold SlotModel.t_cap_name; apply Z.mod_pos_bound; lia).
assert (Hct : 0 <= SlotModel.t_cap_tok inp < 40) by (unfold SlotModel.t_cap_tok; apply Z.mod_pos_bound; lia).
assert (Hcd : 0 <= SlotModel.t_cap_disp inp < 64) by (unfold SlotModel.t_cap_disp; apply Z.mod_pos_bound; lia).
assert (Hti : 0 <= SlotModel.t_in inp < 256) by (apply SlotModel.inb_range).
assert (Hto : 0 <= SlotModel.t_out inp < 256) by (apply SlotModel.inb_range).
assert (Hhm : 0 <= RcIdentModel.has_model_name (m_id g nrec) < 256).
{ unfold RcIdentModel.has_model_name, RcIdentModel.bz.
  pose proof (bv_unsigned_in_range 8 (RcIdentModel.nthb (m_id g nrec) RcIdentModel.OFF_HAS_NAME)) as Hb.
  change (bv_modulus 8) with 256 in Hb. lia. }
(* the byte of id the tail reads *)
assert (Hhmv : val_mem SEGS (rd W2 mem2) (SF + V_id + 20) 1 (RcIdentModel.has_model_name (m_id g nrec))).
{ apply I_vm1. pose proof Hid as (Hidb & _ & _). unfold bytes_at8 in Hidb. fold SF in Hidb.
  rewrite (I_aview_garr8 W2 mem2 (SF + V_id) _ 20 Hidb).
  - change (Z.to_nat 20) with 20%nat. rewrite I_nth_map_bv. reflexivity.
  - rewrite length_map. unfold m_id. rewrite SlotModel.rec_id_length. unfold RcIdentModel.ID_SIZE. lia. }
(* the environment at 0x1184 *)
remember (Eimg (Ereg regs2 (map (Z_to_bv 64)
  [SF + V_id + 3; SF + V_id; SlotModel.t_in inp; SlotModel.t_out inp;
   RcIdentModel.has_model_name (m_id g nrec)]))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (SF + V_id + 3))
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (SF + V_id))
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (SlotModel.t_in inp))
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (SlotModel.t_out inp))
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (RcIdentModel.has_model_name (m_id g nrec)))
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 4)).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
clear HE.
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), R9. apply unsigned_lit_small. clear - Hmf0 Hsp47 Hmfb C1; fold sp0 in Hmfb; lia. }
assert (U33 : bv_unsigned (ew E 33) = SF + V_id)
  by (rewrite E33; apply unsigned_lit_small; clear - HSF0 HSF1 C1; unfold V_id; lia).
assert (HS : st_ok_pi SEGS VAL E ss_IT
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x1184)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_IT. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + unfold I_r0, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [clear - Hmf0 C1; lia|]. split; [clear - Hmf0 Hsp47 Hmfb C1; fold sp0 in Hmfb; lia|].
      split.
      { intros o Ho. apply (apresent_writable SEGS (w_H W2) mem2). apply Hstkpres.
        clear - Ho Hmfb HSTK' Hsp0al; fold sp0 in Hmfb; lia. }
      constructor; [|constructor; [|constructor; [|constructor]]].
      * apply (chunk_ok_val SEGS E _ mf 128 8 (SOff 32 0) (SF + V_id + 3));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | clear - HSF0 HSF1 C1; unfold V_id; lia | lia | exact Hmid3].
      * apply (chunk_ok_val SEGS E _ mf 160 8 (SOff 34 0) (SlotModel.t_in inp));
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia | exact V160].
      * apply (chunk_ok_val SEGS E _ mf 168 8 (SOff 35 0) (SlotModel.t_out inp));
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia | exact V168].
    + unfold I_r1, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [clear - Hmf0 C1; lia|]. split; [clear - Hmf0 Hsp47 Hmfb C1; fold sp0 in Hmfb; lia|].
      split.
      { intros o Ho. apply (apresent_writable SEGS (w_H W2) mem2). apply Hstkpres.
        clear - Ho Hmfb HSTK' Hsp0al; fold sp0 in Hmfb; lia. }
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ mf 184 8 (SOff 33 0) (SF + V_id));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | clear - HSF0 HSF1 C1; unfold V_id; lia | lia | exact Hmid].
    + unfold I_r2, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U33.
      split; [clear - HSF0 C1; unfold V_id; lia|]. split; [clear - HSF0 HSF1 C1; unfold V_id; lia|].
      split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (SF + V_id) 20 1 (SOff 36 0) (RcIdentModel.has_model_name (m_id g nrec)));
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact Hhmv].
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [I_r0 I_r1 I_r2 YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U33.
    repeat split;
      first [ exact I | left; lia | right; clear - HSF0 HSF1 Hmf0 C1; unfold V_id; lia ].
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E36, unsigned_lit_small by lia.
    split; [lia|]. split; [change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
unfold cfg_at. change (w64 (BASE + 0x1184)) with (Z_to_bv 64 (BASE + 0x1184)).
(* ---- the stem call at 0x81898 ---- *)
paj_run_shc RUNP RUNC HS HJ.
{ intros a (r & Hin & Hr). cbv [ss_IT ss_mem] in Hin; cbn [In] in Hin.
  destruct Hin as [Heq | [Heq | [Heq | []]]]; subst r;
    cbn [I_r0 I_r1 I_r2 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    [rewrite U9 in Hr | rewrite U9 in Hr | rewrite U33 in Hr];
    left; clear - Hr Hmfb HSTK' Hsp0al HSF0 HSF1 Hmf0 C1; fold sp0 in Hmfb; unfold V_id in *; lia. }
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 152 <= a < mf + 160) -> ~ (mf + 184 <= a < mf + 192) ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha H1 H2. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia.
  intros (r & Hin & Hr). try cbv [ss_IT ss_mem] in Hin. cbn [In] in Hin.
  destruct Hin as [Heq | [Heq | [Heq | []]]]; subst r;
    cbn [I_r0 I_r1 I_r2 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    [rewrite U9 in Hr | rewrite U9 in Hr | rewrite U33 in Hr]; lia. }
pose proof (I_ikept_run g pos mf ly2 S2 W2 mem2 (ms_mem ms) _ _ (4 * Z.of_nat nrec + 4)
  HJ Hfrs Hinbk EFA ltac:(clear - Hmf0 C1; lia) Hsp47 KEEP) as HIK1.
clear HF HFr HG.
prreg HS (10%bv : bv 5) P10. prreg HS (2%bv : bv 5) P2. prreg HS (8%bv : bv 5) P8.
prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (1%bv : bv 5) P1.
rewrite (EE 25%nat 25%bv eq_refl), R25 in P10.
rewrite (EE 2%nat 2%bv eq_refl), R2 in P2. rewrite (EE 8%nat 8%bv eq_refl), R8 in P8.
rewrite (EE 3%nat 3%bv eq_refl), R3 in P3. rewrite (EE 4%nat 4%bv eq_refl), R4 in P4.
pose proof (I_rod g pos ly2 S2 W2 (ms_mem ms) _ _ HJ HPRE) as HROD.
destruct (I_stem_tbl W2 (ms_mem ms) HROD) as (t1 & t2 & t3 & Vt1 & Vt2 & Vt3 & Ht1 & Ht2 & Ht3).
destruct (HIMG W2 (ms_mem ms) HROD)
  as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hzs & _ & (_ & _ & _ & _ & _ & _ & (Hlo18 & Hhi18 & _) & _) & _).
assert (Hsr : 0 < reac_box_family_stem.stem_sel (SlotModel.n_fam inp) t1 t2 t3 < 2 ^ 64).
{ unfold reac_box_family_stem.stem_sel.
  destruct (SlotModel.n_fam inp =? 1); [lia|]. destruct (SlotModel.n_fam inp =? 2); [lia|].
  destruct (SlotModel.n_fam inp =? 3); [lia|]. clear - Hlo18 Hhi18. cbn [length] in Hhi18. lia. }
assert (VraM : val_mem SEGS (rd W2 (ms_mem ms)) (sp0 - 8) 8 RA_LLVMF).
{ apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms) (sp0 - 8) (sp0 - 8) 8 RA_LLVMF); [|exact Vra].
  intros kk Hkk. apply KEEP; clear - Hkk Hmf0 Hsp47 Hmfb C1; fold sp0 in Hmfb; lia. }
assert (Vs0M : val_mem SEGS (rd W2 (ms_mem ms)) (sp0 - 16) 8 (s0Z (e_regs g))).
{ apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms) (sp0 - 16) (sp0 - 16) 8 _); [|exact Vs0].
  intros kk Hkk. apply KEEP; clear - Hkk Hmf0 Hsp47 Hmfb C1; fold sp0 in Hmfb; lia. }
assert (Rsp0 : getr (ms_regs ms) 2 = w64 (mf - 0)) by (rewrite P2; f_equal; lia).
pmkst HS. rewrite (PSIG IS_reac_box_family_stem AF_reac_box_family_stem eq_refl).
eapply (I_pcall g pos mf W2 (ms_regs ms) (ms_mem ms) _ ly2 S2 (4 * Z.of_nat nrec + 4) [] 0
  reac_box_family_stem.REAC_BOX_FAMILY_STEM_STK [] (BASE + AF_reac_box_family_stem) 0x1190
  (fun ly' S' W' regs' mem' md' =>
     getr regs' 10 = w64 (reac_box_family_stem.stem_sel (SlotModel.n_fam inp) t1 t2 t3) /\
     ly' = ly2 /\ S' = S2 /\ W' = W2 /\ Permutation (ablocks B ly' S') (ablocks B ly2 S2))
  _ HPRE HJ Hfrs Hbl Hmfb Hmf32 VraM Vs0M (or_introl eq_refl) Rsp0 P8 P3 P4 P1).
- lia.
- reflexivity.
- unfold reac_box_family_stem.REAC_BOX_FAMILY_STEM_STK, ESTACK. lia.
- clear - Hkrange. lia.
- clear - Hkrange. lia.
- exact MLE.
- exact MOK.
- intros ch HPRE1.
  exact (HSTEM ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ ch (SlotModel.n_fam inp) t1 t2 t3 HPRE1 P10
    ltac:(clear - Hnfr; lia) Vt1 Vt2 Vt3 Hzs).
- intros a (rr & Hr & _). destruct Hr.
- apply sink_closed_pos. constructor.
- intros ly3 S3 W3 regs3 mem3 md3 (_ & -> & -> & _ & HPm). exact HPm.
- intros W3 ly3 S3 regs3 mem3 md3 Hwle HJ3 HP3 Hfrs3 Hbl3 HK3 MLE3 MOK3 HPost.
  destruct HPost as (R10s & -> & -> & -> & _).
  jafter_call_keep_hi HS 512%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0%nat; 1%nat; 2%nat] HS3.
  match type of HS3 with ?Q -> _ => assert (HQ : Q); [|specialize (HS3 HQ); clear HQ] end.
  { cbn [ms_mem restrict]. constructor; [|constructor; [|constructor; [|constructor]]].
    - eapply (region_kept_stack_aj SEGS B); [exact HK3 | exact HJ3 | exact U9 |
        clear - Hmfb Hsp0al HSTK'; fold sp0 in Hmfb; lia | clear - Hmfb Hsp0al HSTK'; fold sp0 in Hmfb; lia |
        clear - Hmfb; fold sp0 in Hmfb; lia | lia | lia].
    - eapply (region_kept_stack_aj SEGS B); [exact HK3 | exact HJ3 | exact U9 |
        clear - Hmfb Hsp0al HSTK'; fold sp0 in Hmfb; lia | clear - Hmfb Hsp0al HSTK'; fold sp0 in Hmfb; lia |
        clear - Hmfb; fold sp0 in Hmfb; lia | lia | lia].
    - eapply (region_kept_frame_aj SEGS B); [exact HK3 | exact U33 | exact Hin4 |
        cbn [YP09.r_lo]; rewrite EFA; clear - HSF0; unfold V_id; lia |
        cbn [YP09.r_hi]; rewrite EFA; change (fs_frame_bytes 4) with 1024; clear - HSF0; unfold V_id; lia |
        cbn [YP09.r_wlo YP09.r_whi]; lia | intros a Ha (rr & Hr & _); destruct Hr]. }
  rewrite <- restrict_mkst_fx in HS3.
  pose proof (img_env_havoc_hi E 512%nat (map (getr regs3) CLOB) HEI ltac:(cbv; lia)) as HEI3.
  set (E' := havoc E 512%nat (map (getr regs3) CLOB)) in HS3, HEI3.
  pose proof HK3 as (SK1 & SK2 & _ & SK4 & _).
  assert (HIK2 : ikept g pos mf W2 (ms_mem ms) W2 mem3).
  { apply (I_ikept_of g pos mf ly2 S2 W2 (ms_mem ms) W2 mem3
      (mf - 0 - reac_box_family_stem.REAC_BOX_FAMILY_STEM_STK) (inFP (@nil (Z * Z)))
      EFA Hin4 Hinbk ltac:(clear - Hmf0 C1; lia) Hsp47);
    [ intros a Ha1 Ha2; apply SK1; [exact Ha1 | intro Hc; apply Ha2; clear - Hc; lia]
    | exact SK2 | exact SK4 | intros a Ha; destruct (inFP_nil a Ha) ]. }
  pose proof (ikept_trans g pos mf W2 mem2 W2 (ms_mem ms) W2 mem3 HIK1 HIK2) as HIK.
  clear HIK1 HIK2 SK1 SK2 SK4.
  assert (U9' : bv_unsigned (ew E' 9) = mf)
    by (unfold E'; rewrite (ew_havoc_old E 512%nat (map (getr regs3) CLOB) 9 ltac:(lia)); exact U9).
  assert (U33' : bv_unsigned (ew E' 33) = SF + V_id)
    by (unfold E'; rewrite (ew_havoc_old E 512%nat (map (getr regs3) CLOB) 33 ltac:(lia)); exact U33).
  assert (EE' : forall n (r : bv 5), (n < 512)%nat -> Z.of_nat n = bv_unsigned r -> ew E' n = getr regs2 r)
    by (intros n r Hn Hr; unfold E'; rewrite (ew_havoc_old E 512%nat (map (getr regs3) CLOB) n Hn); apply EE; exact Hr).
  (* the stem result is nonzero: beqz a0 at 0x8189c not taken *)
  eapply (paj_branch W2 E' _ _ _ _ BC_EQ (SOff 516 0) (SLit 0) HS3).
  + intros Hbt _. exfalso.
    assert (Hew : ew E' 516 = Z_to_bv 64 (reac_box_family_stem.stem_sel (SlotModel.n_fam inp) t1 t2 t3)).
    { unfold E'. change 516%nat with (512 + 4)%nat. rewrite I_ew_a0, R10s. reflexivity. }
    rewrite (I_beqz_ne E' 516 _ Hew Hsr) in Hbt. discriminate.
  + intros Hbf HSc2.
    (* ---- malloc 1 (nm) at 0x818b8 ---- *)
    paj_run_shc RUNP RUNC HSc2 HJ3.
    { intros a (r & Hin & Hr). cbn [In] in Hin.
      destruct Hin as [Heq | [Heq | [Heq | []]]]; subst r;
        cbn [I_r0 I_r1 I_r2 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        [rewrite U9' in Hr | rewrite U9' in Hr | rewrite U33' in Hr];
        left; clear - Hr Hmfb HSTK' Hsp0al HSF0 HSF1 Hmf0 C1; fold sp0 in Hmfb; unfold V_id in *; lia. }
    assert (KEEPm1 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 152 <= a < mf + 160) -> ~ (mf + 184 <= a < mf + 192) ->
      aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem3 a).
    { intros a Ha H1 H2. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia.
      intros (r & Hin & Hr). cbn [In] in Hin.
      destruct Hin as [Heq | [Heq | [Heq | []]]]; subst r;
        cbn [I_r0 I_r1 I_r2 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        [rewrite U9' in Hr | rewrite U9' in Hr | rewrite U33' in Hr]; lia. }
    destruct (I_base g pos ly2 S2 W2 _ _ (4 * Z.of_nat nrec + 4) [] HPRE HJ3 Hfrs3 Hbl3)
      as (EFA3 & Hin43 & _ & _ & _ & _ & _ & _ & _ & Hinb3 & _).
    pose proof (ikept_trans g pos mf W2 mem2 W2 mem3 W2 (ms_mem ms0) HIK
      (I_ikept_run g pos mf ly2 S2 W2 mem3 (ms_mem ms0) _ _ (4 * Z.of_nat nrec + 4)
        HJ3 Hfrs3 Hinb3 EFA3 ltac:(clear - Hmf0 C1; lia) Hsp47 KEEPm1)) as HIKa.
    clear HIK KEEPm1 HF HFr HG.
    prreg HSc2 (10%bv : bv 5) Q10. prreg HSc2 (2%bv : bv 5) Q2. prreg HSc2 (8%bv : bv 5) Q8.
    prreg HSc2 (3%bv : bv 5) Q3. prreg HSc2 (4%bv : bv 5) Q4. prreg HSc2 (1%bv : bv 5) Q1.
    rewrite (EE' 26%nat 26%bv ltac:(lia) eq_refl), R26 in Q10. unfold w64 in Q10.
    rewrite (I_maxcap (SlotModel.t_cap_name inp) ltac:(lia)) in Q10.
    rewrite (EE' 2%nat 2%bv ltac:(lia) eq_refl), R2 in Q2.
    rewrite (EE' 8%nat 8%bv ltac:(lia) eq_refl), R8 in Q8.
    rewrite (EE' 3%nat 3%bv ltac:(lia) eq_refl), R3 in Q3.
    rewrite (EE' 4%nat 4%bv ltac:(lia) eq_refl), R4 in Q4.
    assert (Rsp1 : getr (ms_regs ms0) 2 = w64 mf) by (exact Q2).
    assert (VMik : forall a (nn : nat) v, mf <= a -> a + Z.of_nat nn <= e_sp0 g ->
      (forall j, 0 <= j < Z.of_nat nn -> ~ (mf + 152 <= a + j < mf + 160) /\ ~ (mf + 184 <= a + j < mf + 192)) ->
      val_mem SEGS (rd W2 mem2) a nn v -> val_mem SEGS (rd W2 (ms_mem ms0)) a nn v).
    { intros a nn v Ha0 Ha1 Hh Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms0) a a nn v); [|exact Hv].
      intros kk Hkk. apply HIKa. left. destruct (Hh kk Hkk) as [Hhh1 Hhh2].
      split; [clear - Ha0 Ha1 Hkk; lia | split; assumption]. }
    clear VraM Vs0M.
    assert (VraM : val_mem SEGS (rd W2 (ms_mem ms0)) (sp0 - 8) 8 RA_LLVMF).
    { apply VMik; [clear - Hmf0 Hsp47 Hmfb; fold sp0 in Hmfb; lia | clear - Hmfb; fold sp0 in Hmfb; lia
      | intros j Hj; split; clear - Hmfb Hj; fold sp0 in Hmfb; lia | exact Vra]. }
    assert (Vs0M : val_mem SEGS (rd W2 (ms_mem ms0)) (sp0 - 16) 8 (s0Z (e_regs g))).
    { apply VMik; [clear - Hmf0 Hsp47 Hmfb; fold sp0 in Hmfb; lia | clear - Hmfb; fold sp0 in Hmfb; lia
      | intros j Hj; split; clear - Hmfb Hj; fold sp0 in Hmfb; lia | exact Vs0]. }
    pmkst HSc2. rewrite (pal_malloc B TL).
    eapply (I_malloc_at g pos mf W2 (ms_regs ms0) (ms_mem ms0) _ ly2 S2 (4 * Z.of_nat nrec + 4) []
      (Z.max (SlotModel.t_cap_name inp) 1) 0x11b0 _ HPRE HJ3 Hfrs Hbl
      ltac:(unfold bsum; cbn [fold_right]; unfold LIVE_LLVMF; lia) ltac:(lia) Hmfb Hmf32 VraM Vs0M
      Q10 Q2 Q8 Q3 Q4 Q1
      ltac:(unfold LLVMF_MALLOC_RAS; cbn [In]; right; right; right; right; left; reflexivity)
      ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(clear - Hnr64; unfold EV_LLVMF; lia) MLE MOK).
    intros W4 ly4 S4 regs4 mem4 md4 nm Hwle4 HJ4 HP4 Hfrs4 Hres4 Hnm4 Hbl4 HIK4 HK4 MLE4 MOK4.
    pose proof (ikept_trans g pos mf W2 mem2 W2 (ms_mem ms0) W4 mem4 HIKa HIK4) as HIKb.
    clear HIKa HIK4.
    jafter_call_keep_hi HSc2 528%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0%nat; 1%nat] HS4.
    match type of HS4 with ?Q -> _ => assert (HQ : Q); [|specialize (HS4 HQ); clear HQ] end.
    { cbn [ms_mem restrict]. constructor; [|constructor; [|constructor]].
      - eapply (region_kept_stack_aj SEGS B); [exact HK4 | exact HJ4 | exact U9' |
          clear - Hmfb Hsp0al HSTK'; fold sp0 in Hmfb; lia | clear - Hmfb Hsp0al HSTK'; fold sp0 in Hmfb; lia |
          clear - Hmfb; fold sp0 in Hmfb; lia | lia | lia].
      - eapply (region_kept_stack_aj SEGS B); [exact HK4 | exact HJ4 | exact U9' |
          clear - Hmfb Hsp0al HSTK'; fold sp0 in Hmfb; lia | clear - Hmfb Hsp0al HSTK'; fold sp0 in Hmfb; lia |
          clear - Hmfb; fold sp0 in Hmfb; lia | lia | lia]. }
    rewrite <- restrict_mkst_fx in HS4.
    pose proof (img_env_havoc_hi E' 528%nat (map (getr regs4) CLOB) HEI3 ltac:(cbv; lia)) as HEI4.
    set (E2 := havoc E' 528%nat (map (getr regs4) CLOB)) in HS4, HEI4.
    assert (U9a : bv_unsigned (ew E2 9) = mf)
      by (unfold E2; rewrite (ew_havoc_old E' 528%nat (map (getr regs4) CLOB) 9 ltac:(lia)); exact U9').
    destruct (I_base g pos ly4 S4 W4 mem4 md4 (4 * Z.of_nat nrec + 4 + 1)
      [(nm, Z.max (SlotModel.t_cap_name inp) 1)] HPRE HJ4 Hfrs4 Hbl4)
      as (EFA4 & Hin44 & _ & _ & _ & _ & _ & _ & _ & Hinb4 & _).
    destruct (I_blk_apart g pos ly4 S4 W4 mem4 md4 _ nm _ HPRE (proj1 HJ4) EFA4 Hin44 Hbl4 (or_introl eq_refl))
      as (Hnmin & _ & Hnmce & _ & Hnmnew & Hnmap).
    (* 0x818bc sd a0,184(s1); 0x818c0 beqz a0 *)
    paj_run_to_sh RUNTOP HS4 HJ4 0x11b4.
    { intros a (r & Hin & Hr). cbn [In] in Hin.
      destruct Hin as [Heq | [Heq | []]]; subst r;
        cbn [I_r0 I_r1 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite U9a in Hr;
        left; clear - Hr Hmfb HSTK' Hsp0al Hmf0 C1; fold sp0 in Hmfb; lia. }
    assert (KEEPr1 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 152 <= a < mf + 160) -> ~ (mf + 184 <= a < mf + 192) ->
      aview SEGS (w_H W4) (ms_mem ms1) a = aview SEGS (w_H W4) mem4 a) by i_keep2 HFr U9a.
    pose proof (ikept_trans g pos mf W2 mem2 W4 mem4 W4 (ms_mem ms1) HIKb
      (I_ikept_run g pos mf ly4 S4 W4 mem4 (ms_mem ms1) _ _ (4 * Z.of_nat nrec + 4 + 1)
        HJ4 Hfrs4 Hinb4 EFA4 ltac:(clear - Hmf0 C1; lia) Hsp47 KEEPr1)) as HIKc.
    clear HIKb KEEPr1 HF HFr HG.
    assert (Hnmr : 0 < nm < 2 ^ 64).
    { pose proof (req_size_pos (Z.max (SlotModel.t_cap_name inp) 1) ltac:(lia)) as Hrq.
      clear - Hnm4 Hnmce C1 Hrq. lia. }
    eapply (paj_branch W4 E2 _ ms1 _ _ BC_EQ (SOff 532 0) (SLit 0) HS4).
    { intros Hbt _. exfalso.
      assert (Hew : ew E2 532 = Z_to_bv 64 nm).
      { unfold E2. change 532%nat with (528 + 4)%nat. rewrite I_ew_a0, Hres4. reflexivity. }
      rewrite (I_beqz_ne E2 532 _ Hew Hnmr) in Hbt. discriminate. }
    intros Hbf2 HSc3.
    (* ---- malloc 2 (tk) at 0x818d0 ---- *)
    assert (EE2 : forall n (r : bv 5), (n < 512)%nat -> Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs2 r).
    { intros n r Hn Hr. unfold E2. rewrite (ew_havoc_old E' 528%nat (map (getr regs4) CLOB) n ltac:(lia)).
      apply EE'; [exact Hn | exact Hr]. }
    paj_run_shc RUNP RUNC HSc3 HJ4.
    { i_awr2 U9a Hmfb HSTK' Hsp0al Hmf0 C1 sp0. }
    assert (KEEPm2 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 152 <= a < mf + 160) -> ~ (mf + 184 <= a < mf + 192) ->
      aview SEGS (w_H W4) (ms_mem ms2) a = aview SEGS (w_H W4) (ms_mem ms1) a) by i_keep2 HFr U9a.
    pose proof (ikept_trans g pos mf W2 mem2 W4 (ms_mem ms1) W4 (ms_mem ms2) HIKc
      (I_ikept_run g pos mf ly4 S4 W4 (ms_mem ms1) (ms_mem ms2) _ _ (4 * Z.of_nat nrec + 4 + 1)
        HJ4 Hfrs4 Hinb4 EFA4 ltac:(clear - Hmf0 C1; lia) Hsp47 KEEPm2)) as HIKd.
    clear HIKc KEEPm2 HF HFr HG.
    prreg HSc3 (10%bv : bv 5) Q10b. prreg HSc3 (2%bv : bv 5) Q2b. prreg HSc3 (8%bv : bv 5) Q8b.
    prreg HSc3 (3%bv : bv 5) Q3b. prreg HSc3 (4%bv : bv 5) Q4b. prreg HSc3 (1%bv : bv 5) Q1b.
    rewrite (EE2 24%nat 24%bv ltac:(lia) eq_refl), R24 in Q10b. unfold w64 in Q10b.
    rewrite (I_maxcap (SlotModel.t_cap_tok inp) ltac:(lia)) in Q10b.
    rewrite (EE2 2%nat 2%bv ltac:(lia) eq_refl), R2 in Q2b.
    rewrite (EE2 8%nat 8%bv ltac:(lia) eq_refl), R8 in Q8b.
    rewrite (EE2 3%nat 3%bv ltac:(lia) eq_refl), R3 in Q3b.
    rewrite (EE2 4%nat 4%bv ltac:(lia) eq_refl), R4 in Q4b.
    clear VMik VraM Vs0M.
    assert (VMik : forall a (nn : nat) v, mf <= a -> a + Z.of_nat nn <= e_sp0 g ->
      (forall j, 0 <= j < Z.of_nat nn -> ~ (mf + 152 <= a + j < mf + 160) /\ ~ (mf + 184 <= a + j < mf + 192)) ->
      val_mem SEGS (rd W2 mem2) a nn v -> val_mem SEGS (rd W4 (ms_mem ms2)) a nn v).
    { intros a nn v Ha0 Ha1 Hh Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W4) mem2 (ms_mem ms2) a a nn v); [|exact Hv].
      intros kk Hkk. apply HIKd. left. destruct (Hh kk Hkk) as [Hhh1 Hhh2].
      split; [clear - Ha0 Ha1 Hkk; lia | split; assumption]. }
    assert (VraM : val_mem SEGS (rd W4 (ms_mem ms2)) (sp0 - 8) 8 RA_LLVMF).
    { apply VMik; [clear - Hmf0 Hsp47 Hmfb; fold sp0 in Hmfb; lia | clear - Hmfb; fold sp0 in Hmfb; lia
      | intros j Hj; split; clear - Hmfb Hj; fold sp0 in Hmfb; lia | exact Vra]. }
    assert (Vs0M : val_mem SEGS (rd W4 (ms_mem ms2)) (sp0 - 16) 8 (s0Z (e_regs g))).
    { apply VMik; [clear - Hmf0 Hsp47 Hmfb; fold sp0 in Hmfb; lia | clear - Hmfb; fold sp0 in Hmfb; lia
      | intros j Hj; split; clear - Hmfb Hj; fold sp0 in Hmfb; lia | exact Vs0]. }
    pmkst HSc3. rewrite (pal_malloc B TL).
    eapply (I_malloc_at g pos mf W4 (ms_regs ms2) (ms_mem ms2) _ ly4 S4 (4 * Z.of_nat nrec + 4 + 1)
      [(nm, Z.max (SlotModel.t_cap_name inp) 1)] (Z.max (SlotModel.t_cap_tok inp) 1) 0x11c8 _ HPRE HJ4 Hfrs4 Hbl4
      ltac:(unfold bsum; cbn [fold_right snd]; unfold LIVE_LLVMF; lia) ltac:(lia) Hmfb Hmf32 VraM Vs0M
      Q10b Q2b Q8b Q3b Q4b Q1b
      ltac:(unfold LLVMF_MALLOC_RAS; cbn [In]; right; right; right; right; right; left; reflexivity)
      ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(clear - Hnr64; unfold EV_LLVMF; lia) MLE4 MOK4).
    intros W5 ly5 S5 regs5 mem5 md5 tk Hwle5 HJ5 HP5 Hfrs5 Hres5 Htk5 Hbl5 HIK5 HK5 MLE5 MOK5.
    pose proof (ikept_trans g pos mf W2 mem2 W4 (ms_mem ms2) W5 mem5 HIKd HIK5) as HIKe.
    clear HIKd HIK5.
    jafter_call_keep_hi HSc3 544%nat regs5 (mrestrict (w_H W5) mem5) HP5 [0%nat; 1%nat] HS5.
    match type of HS5 with ?Q -> _ => assert (HQ : Q); [|specialize (HS5 HQ); clear HQ] end.
    { cbn [ms_mem restrict]. constructor; [|constructor; [|constructor]].
      - eapply (region_kept_stack_aj SEGS B); [exact HK5 | exact HJ5 | exact U9a |
          clear - Hmfb Hsp0al HSTK'; fold sp0 in Hmfb; lia | clear - Hmfb Hsp0al HSTK'; fold sp0 in Hmfb; lia |
          clear - Hmfb; fold sp0 in Hmfb; lia | lia | lia].
      - eapply (region_kept_stack_aj SEGS B); [exact HK5 | exact HJ5 | exact U9a |
          clear - Hmfb Hsp0al HSTK'; fold sp0 in Hmfb; lia | clear - Hmfb Hsp0al HSTK'; fold sp0 in Hmfb; lia |
          clear - Hmfb; fold sp0 in Hmfb; lia | lia | lia]. }
    rewrite <- restrict_mkst_fx in HS5.
    pose proof (img_env_havoc_hi E2 544%nat (map (getr regs5) CLOB) HEI4 ltac:(cbv; lia)) as HEI5.
    set (E3 := havoc E2 544%nat (map (getr regs5) CLOB)) in HS5, HEI5.
    assert (U9b : bv_unsigned (ew E3 9) = mf)
      by (unfold E3; rewrite (ew_havoc_old E2 544%nat (map (getr regs5) CLOB) 9 ltac:(lia)); exact U9a).
    assert (EE3 : forall n (r : bv 5), (n < 512)%nat -> Z.of_nat n = bv_unsigned r -> ew E3 n = getr regs2 r).
    { intros n r Hn Hr. unfold E3. rewrite (ew_havoc_old E2 544%nat (map (getr regs5) CLOB) n ltac:(lia)).
      apply EE2; [exact Hn | exact Hr]. }
    destruct (I_base g pos ly5 S5 W5 mem5 md5 (4 * Z.of_nat nrec + 4 + 1 + 1)
      [(tk, Z.max (SlotModel.t_cap_tok inp) 1); (nm, Z.max (SlotModel.t_cap_name inp) 1)] HPRE HJ5 Hfrs5 Hbl5)
      as (EFA5 & Hin45 & _ & _ & _ & _ & _ & _ & _ & Hinb5 & _).
    destruct (I_blk_apart g pos ly5 S5 W5 mem5 md5 _ tk _ HPRE (proj1 HJ5) EFA5 Hin45 Hbl5 (or_introl eq_refl))
      as (Htkin & _ & Htkce & _ & Htknew & Htkap).
    assert (Htkr : 0 < tk < 2 ^ 64).
    { pose proof (req_size_pos (Z.max (SlotModel.t_cap_tok inp) 1) ltac:(lia)) as Hrq.
      clear - Htk5 Htkce C1 Hrq. lia. }
    (* 0x818d4 ld s10,168(s1); 0x818d8 beqz a0 *)
    paj_run_to_sh RUNTOP HS5 HJ5 0x11cc.
    { i_awr2 U9b Hmfb HSTK' Hsp0al Hmf0 C1 sp0. }
    assert (KEEPr2 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 152 <= a < mf + 160) -> ~ (mf + 184 <= a < mf + 192) ->
      aview SEGS (w_H W5) (ms_mem ms3) a = aview SEGS (w_H W5) mem5 a) by i_keep2 HFr U9b.
    pose proof (ikept_trans g pos mf W2 mem2 W5 mem5 W5 (ms_mem ms3) HIKe
      (I_ikept_run g pos mf ly5 S5 W5 mem5 (ms_mem ms3) _ _ (4 * Z.of_nat nrec + 4 + 1 + 1)
        HJ5 Hfrs5 Hinb5 EFA5 ltac:(clear - Hmf0 C1; lia) Hsp47 KEEPr2)) as HIKf.
    clear HIKe KEEPr2 HF HFr HG.
    eapply (paj_branch W5 E3 _ ms3 _ _ BC_EQ (SOff 548 0) (SLit 0) HS5).
    { intros Hbt _. exfalso.
      assert (Hew : ew E3 548 = Z_to_bv 64 tk).
      { unfold E3. change 548%nat with (544 + 4)%nat. rewrite I_ew_a0, Hres5. reflexivity. }
      rewrite (I_beqz_ne E3 548 _ Hew Htkr) in Hbt. discriminate. }
    intros Hbf3 HSc4.
    (* ---- malloc 3 (dp) at 0x818e8 ---- *)
    paj_run_shc RUNP RUNC HSc4 HJ5.
    { i_awr2 U9b Hmfb HSTK' Hsp0al Hmf0 C1 sp0. }
    assert (KEEPm3 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 152 <= a < mf + 160) -> ~ (mf + 184 <= a < mf + 192) ->
      aview SEGS (w_H W5) (ms_mem ms4) a = aview SEGS (w_H W5) (ms_mem ms3) a) by i_keep2 HFr U9b.
    pose proof (ikept_trans g pos mf W2 mem2 W5 (ms_mem ms3) W5 (ms_mem ms4) HIKf
      (I_ikept_run g pos mf ly5 S5 W5 (ms_mem ms3) (ms_mem ms4) _ _ (4 * Z.of_nat nrec + 4 + 1 + 1)
        HJ5 Hfrs5 Hinb5 EFA5 ltac:(clear - Hmf0 C1; lia) Hsp47 KEEPm3)) as HIKg.
    clear HIKf KEEPm3 HF HFr HG.
    prreg HSc4 (10%bv : bv 5) Q10c. prreg HSc4 (2%bv : bv 5) Q2c. prreg HSc4 (8%bv : bv 5) Q8c.
    prreg HSc4 (3%bv : bv 5) Q3c. prreg HSc4 (4%bv : bv 5) Q4c. prreg HSc4 (1%bv : bv 5) Q1c.
    rewrite (EE3 27%nat 27%bv ltac:(lia) eq_refl), R27 in Q10c. unfold w64 in Q10c.
    rewrite (I_maxcap_raw (SlotModel.t_cap_disp inp) ltac:(lia)) in Q10c.
    rewrite (EE3 2%nat 2%bv ltac:(lia) eq_refl), R2 in Q2c.
    rewrite (EE3 8%nat 8%bv ltac:(lia) eq_refl), R8 in Q8c.
    rewrite (EE3 3%nat 3%bv ltac:(lia) eq_refl), R3 in Q3c.
    rewrite (EE3 4%nat 4%bv ltac:(lia) eq_refl), R4 in Q4c.
    clear VMik VraM Vs0M.
    assert (VMik : forall a (nn : nat) v, mf <= a -> a + Z.of_nat nn <= e_sp0 g ->
      (forall j, 0 <= j < Z.of_nat nn -> ~ (mf + 152 <= a + j < mf + 160) /\ ~ (mf + 184 <= a + j < mf + 192)) ->
      val_mem SEGS (rd W2 mem2) a nn v -> val_mem SEGS (rd W5 (ms_mem ms4)) a nn v).
    { intros a nn v Ha0 Ha1 Hh Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W5) mem2 (ms_mem ms4) a a nn v); [|exact Hv].
      intros kk Hkk. apply HIKg. left. destruct (Hh kk Hkk) as [Hhh1 Hhh2].
      split; [clear - Ha0 Ha1 Hkk; lia | split; assumption]. }
    assert (VraM : val_mem SEGS (rd W5 (ms_mem ms4)) (sp0 - 8) 8 RA_LLVMF).
    { apply VMik; [clear - Hmf0 Hsp47 Hmfb; fold sp0 in Hmfb; lia | clear - Hmfb; fold sp0 in Hmfb; lia
      | intros j Hj; split; clear - Hmfb Hj; fold sp0 in Hmfb; lia | exact Vra]. }
    assert (Vs0M : val_mem SEGS (rd W5 (ms_mem ms4)) (sp0 - 16) 8 (s0Z (e_regs g))).
    { apply VMik; [clear - Hmf0 Hsp47 Hmfb; fold sp0 in Hmfb; lia | clear - Hmfb; fold sp0 in Hmfb; lia
      | intros j Hj; split; clear - Hmfb Hj; fold sp0 in Hmfb; lia | exact Vs0]. }
    pmkst HSc4. rewrite (pal_malloc B TL).
    eapply (I_malloc_at g pos mf W5 (ms_regs ms4) (ms_mem ms4) _ ly5 S5 (4 * Z.of_nat nrec + 4 + 1 + 1)
      [(tk, Z.max (SlotModel.t_cap_tok inp) 1); (nm, Z.max (SlotModel.t_cap_name inp) 1)]
      (Z.max (SlotModel.t_cap_disp inp) 1) 0x11e0 _ HPRE HJ5 Hfrs5 Hbl5
      ltac:(unfold bsum; cbn [fold_right snd]; unfold LIVE_LLVMF; lia) ltac:(lia) Hmfb Hmf32 VraM Vs0M
      Q10c Q2c Q8c Q3c Q4c Q1c
      ltac:(unfold LLVMF_MALLOC_RAS; cbn [In]; right; right; right; right; right; right; left; reflexivity)
      ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(clear - Hnr64; unfold EV_LLVMF; lia) MLE5 MOK5).
    intros W6 ly6 S6 regs6 mem6 md6 dp Hwle6 HJ6 HP6 Hfrs6 Hres6 Hdp6 Hbl6 HIK6 HK6 MLE6 MOK6.
    pose proof (ikept_trans g pos mf W2 mem2 W5 (ms_mem ms4) W6 mem6 HIKg HIK6) as HIKh.
    clear HIKg HIK6.
    jafter_call_keep_hi HSc4 560%nat regs6 (mrestrict (w_H W6) mem6) HP6 [0%nat; 1%nat] HS6.
    match type of HS6 with ?Q -> _ => assert (HQ : Q); [|specialize (HS6 HQ); clear HQ] end.
    { cbn [ms_mem restrict]. constructor; [|constructor; [|constructor]].
      - eapply (region_kept_stack_aj SEGS B); [exact HK6 | exact HJ6 | exact U9b |
          clear - Hmfb Hsp0al HSTK'; fold sp0 in Hmfb; lia | clear - Hmfb Hsp0al HSTK'; fold sp0 in Hmfb; lia |
          clear - Hmfb; fold sp0 in Hmfb; lia | lia | lia].
      - eapply (region_kept_stack_aj SEGS B); [exact HK6 | exact HJ6 | exact U9b |
          clear - Hmfb Hsp0al HSTK'; fold sp0 in Hmfb; lia | clear - Hmfb Hsp0al HSTK'; fold sp0 in Hmfb; lia |
          clear - Hmfb; fold sp0 in Hmfb; lia | lia | lia]. }
    rewrite <- restrict_mkst_fx in HS6.
    pose proof (img_env_havoc_hi E3 560%nat (map (getr regs6) CLOB) HEI5 ltac:(cbv; lia)) as HEI6.
    set (E4 := havoc E3 560%nat (map (getr regs6) CLOB)) in HS6, HEI6.
    assert (U9c : bv_unsigned (ew E4 9) = mf)
      by (unfold E4; rewrite (ew_havoc_old E3 560%nat (map (getr regs6) CLOB) 9 ltac:(lia)); exact U9b).
    assert (EE4 : forall n (r : bv 5), (n < 512)%nat -> Z.of_nat n = bv_unsigned r -> ew E4 n = getr regs2 r).
    { intros n r Hn Hr. unfold E4. rewrite (ew_havoc_old E3 560%nat (map (getr regs6) CLOB) n ltac:(lia)).
      apply EE3; [exact Hn | exact Hr]. }
    destruct (I_base g pos ly6 S6 W6 mem6 md6 (4 * Z.of_nat nrec + 4 + 1 + 1 + 1)
      [(dp, Z.max (SlotModel.t_cap_disp inp) 1); (tk, Z.max (SlotModel.t_cap_tok inp) 1);
       (nm, Z.max (SlotModel.t_cap_name inp) 1)] HPRE HJ6 Hfrs6 Hbl6)
      as (EFA6 & Hin46 & _ & _ & _ & _ & _ & _ & _ & Hinb6 & _).
    destruct (I_blk_apart g pos ly6 S6 W6 mem6 md6 _ dp _ HPRE (proj1 HJ6) EFA6 Hin46 Hbl6 (or_introl eq_refl))
      as (Hdpin & _ & Hdpce & _ & Hdpnew & Hdpap).
    assert (Hdpr : 0 < dp < 2 ^ 64).
    { pose proof (req_size_pos (Z.max (SlotModel.t_cap_disp inp) 1) ltac:(lia)) as Hrq.
      clear - Hdp6 Hdpce C1 Hrq. lia. }
    (* 0x818ec ld s8,160(s1); 0x818f0 beqz a0 *)
    paj_run_to_sh RUNTOP HS6 HJ6 0x11e4.
    { i_awr2 U9c Hmfb HSTK' Hsp0al Hmf0 C1 sp0. }
    assert (KEEPr3 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 152 <= a < mf + 160) -> ~ (mf + 184 <= a < mf + 192) ->
      aview SEGS (w_H W6) (ms_mem ms5) a = aview SEGS (w_H W6) mem6 a) by i_keep2 HFr U9c.
    pose proof (ikept_trans g pos mf W2 mem2 W6 mem6 W6 (ms_mem ms5) HIKh
      (I_ikept_run g pos mf ly6 S6 W6 mem6 (ms_mem ms5) _ _ (4 * Z.of_nat nrec + 4 + 1 + 1 + 1)
        HJ6 Hfrs6 Hinb6 EFA6 ltac:(clear - Hmf0 C1; lia) Hsp47 KEEPr3)) as HIKi.
    clear HIKh KEEPr3 HF HFr HG.
    eapply (paj_branch W6 E4 _ ms5 _ _ BC_EQ (SOff 564 0) (SLit 0) HS6).
    { intros Hbt _. exfalso.
      assert (Hew : ew E4 564 = Z_to_bv 64 dp).
      { unfold E4. change 564%nat with (560 + 4)%nat. rewrite I_ew_a0, Hres6. reflexivity. }
      rewrite (I_beqz_ne E4 564 _ Hew Hdpr) in Hbt. discriminate. }
    intros Hbf4 HSc5.
    (* ---- the 16 bytes of stack arguments, then reac_box_name #1 (the refusing call) at 0x81930 ---- *)
    lazymatch type of HSc5 with st_ok_pi _ _ _ ?s _ => let v := eval vm_compute in s in change s with v in HSc5 end.
    assert (U2c : bv_unsigned (ew E4 2) = mf).
    { rewrite (EE4 2%nat 2%bv ltac:(lia) eq_refl), R2. apply unsigned_lit_small.
      clear - Hmf0 Hsp47 Hmfb C1; fold sp0 in Hmfb; lia. }
    destruct (I_base g pos ly6 S6 W6 _ _ (4 * Z.of_nat nrec + 4 + 1 + 1 + 1)
      [(dp, Z.max (SlotModel.t_cap_disp inp) 1); (tk, Z.max (SlotModel.t_cap_tok inp) 1);
       (nm, Z.max (SlotModel.t_cap_name inp) 1)] HPRE HJ6 Hfrs6 Hbl6)
      as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp6).
    pose proof (st_ok_pi_add_region E4 _ _ I_rS HSc5 eq_refl) as HSc6.
    match type of HSc6 with ?A -> ?B -> _ => assert (HRo : A); [|assert (HRd : B); [|specialize (HSc6 HRo HRd); clear HRo HRd]] end.
    { unfold I_rS, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U2c. split; [clear - Hmf0 C1; lia|]. split; [clear - Hmf0 Hsp47 Hmfb C1; fold sp0 in Hmfb; lia|].
      split; [|constructor].
      intros o Ho. cbn [ms_mem restrict]. apply (apresent_writable SEGS (w_H W6) (ms_mem ms5)). apply Hstkp6.
      clear - Ho Hmfb HSTK' Hsp0al; fold sp0 in Hmfb; lia. }
    { cbn [all_disjoint ss_mem]. unfold extent_disjoint.
      cbn [I_rS YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2c, U9c.
      repeat split; first [ exact I | left; lia ]. }
    clear HSc5.
    paj_run_shc RUNP RUNC HSc6 HJ6.
    { intros a (r & Hin & Hr). cbn [In] in Hin. destruct Hin as [Heq | [Heq | [Heq | []]]]; subst r;
        cbn [I_rS I_r0 I_r1 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        [rewrite U2c in Hr | rewrite U9c in Hr | rewrite U9c in Hr];
        left; clear - Hr Hmfb HSTK' Hsp0al Hmf0 C1; fold sp0 in Hmfb; lia. }
    assert (KEEPq1 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 152 <= a < mf + 160) -> ~ (mf + 184 <= a < mf + 192) ->
      ~ (mf - 16 <= a < mf) -> aview SEGS (w_H W6) (ms_mem ms6) a = aview SEGS (w_H W6) (ms_mem ms5) a).
    { intros a Ha H1 H2 H3. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia.
      intros (r & Hin & Hr). cbn [In] in Hin. destruct Hin as [Heq | [Heq | [Heq | []]]]; subst r;
        cbn [I_rS I_r0 I_r1 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        [rewrite U2c in Hr | rewrite U9c in Hr | rewrite U9c in Hr]; lia. }
    pose proof (ikept_trans g pos mf W2 mem2 W6 (ms_mem ms5) W6 (ms_mem ms6) HIKi
      (I_ikept_run16 g pos mf ly6 S6 W6 (ms_mem ms5) (ms_mem ms6) _ _ (4 * Z.of_nat nrec + 4 + 1 + 1 + 1)
        HJ6 Hfrs6 Hinb6 EFA6 ltac:(clear - Hmf0 C1; lia) Hsp47 KEEPq1)) as HIKj.
    clear HIKi KEEPq1 HF HFr HG.
    prreg HSc6 (10%bv : bv 5) T10. prreg HSc6 (11%bv : bv 5) T11. prreg HSc6 (12%bv : bv 5) T12.
    prreg HSc6 (13%bv : bv 5) T13. prreg HSc6 (14%bv : bv 5) T14. prreg HSc6 (15%bv : bv 5) T15.
    prreg HSc6 (16%bv : bv 5) T16. prreg HSc6 (17%bv : bv 5) T17. prreg HSc6 (2%bv : bv 5) T2.
    prreg HSc6 (1%bv : bv 5) T1.
    pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & Hnev0 & Hbb0 & _).
    assert (EA : forall n, (n < 512)%nat -> ew E4 n = ew E n).
    { intros n Hn. unfold E4, E3, E2, E'.
      rewrite (ew_havoc_old _ 560%nat _ n ltac:(lia)), (ew_havoc_old _ 544%nat _ n ltac:(lia)),
        (ew_havoc_old _ 528%nat _ n ltac:(lia)), (ew_havoc_old _ 512%nat _ n ltac:(lia)). reflexivity. }
    prreg HSc6 (8%bv : bv 5) T8. prreg HSc6 (3%bv : bv 5) T3. prreg HSc6 (4%bv : bv 5) T4.
    rewrite (EE4 25%nat 25%bv ltac:(lia) eq_refl), R25 in T10.
    rewrite (EA 36%nat ltac:(lia)), (EA 32%nat ltac:(lia)), E36, E32 in T11.
    rewrite (I_said_expr (RcIdentModel.has_model_name (m_id g nrec)) (SF + V_id + 3) Hhm
      ltac:(clear - HSF0 HSF1 C1; unfold V_id; lia)) in T11.
    assert (Hew548 : ew E4 548 = Z_to_bv 64 tk).
    { unfold E4. rewrite (ew_havoc_old E3 560%nat _ 548 ltac:(lia)). unfold E3.
      change 548%nat with (544 + 4)%nat. rewrite I_ew_a0, Hres5. reflexivity. }
    rewrite Hew548 in T16.
    rewrite (EE4 24%nat 24%bv ltac:(lia) eq_refl), R24 in T17. unfold w64 in T17.
    rewrite (I_and255 (SlotModel.t_cap_tok inp) ltac:(lia)), (I_add0 (SlotModel.t_cap_tok inp) ltac:(lia)) in T17.
    rewrite U2c in T2.
    assert (T2' : getr (ms_regs ms6) 2 = w64 (mf - 16)) by (rewrite T2; unfold w64; f_equal; lia).
    rewrite (EE4 8%nat 8%bv ltac:(lia) eq_refl), R8 in T8.
    rewrite (EE4 3%nat 3%bv ltac:(lia) eq_refl), R3 in T3.
    rewrite (EE4 4%nat 4%bv ltac:(lia) eq_refl), R4 in T4.
    assert (Usp6 : spZ (ms_regs ms6) = mf - 16).
    { unfold spZ. rewrite T2'. unfold w64. apply unsigned_lit_small. clear - Hmf0 Hsp47 Hmfb C1; fold sp0 in Hmfb; lia. }
    (* the two stack arguments, from the 16-byte region *)
    pose proof (st_ok_region_nth E4 _ _ 0%nat (YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0
        [YP09.mkChunk (-8) (CVal 8 (SOff 27 0)); YP09.mkChunk (-16) (CVal 8 (SOff 564 0))]) HSc6
      ltac:(vm_compute; reflexivity)) as HRS.
    assert (Hew564 : ew E4 564 = Z_to_bv 64 dp).
    { unfold E4. change 564%nat with (560 + 4)%nat. rewrite I_ew_a0, Hres6. reflexivity. }
    assert (Vdp : val_mem SEGS (rd W6 (ms_mem ms6)) (spZ (ms_regs ms6)) 8 dp).
    { rewrite Usp6. replace (mf - 16) with (mf + -16) by lia.
      exact (field_of_region E4 _ 2%nat mf _ (-16) 0 (-16) 0 (-16) 8%N (SOff 564 0) dp HRS U2c
        ltac:(right; left; reflexivity)
        ltac:(cbn [sv_denot]; rewrite Hew564, unsigned_lit_small, Z.add_0_r by lia; reflexivity)
        ltac:(cbn; lia) ltac:(cbn; lia)). }
    assert (Vcd : val_mem SEGS (rd W6 (ms_mem ms6)) (spZ (ms_regs ms6) + 8) 8 (SlotModel.t_cap_disp inp)).
    { rewrite Usp6. replace (mf - 16 + 8) with (mf + -8) by lia.
      exact (field_of_region E4 _ 2%nat mf _ (-16) 0 (-16) 0 (-8) 8%N (SOff 27 0) (SlotModel.t_cap_disp inp) HRS U2c
        ltac:(left; reflexivity)
        ltac:(cbn [sv_denot]; rewrite (EE4 27%nat 27%bv ltac:(lia) eq_refl), R27; unfold w64;
              rewrite unsigned_lit_small, Z.add_0_r by lia; reflexivity)
        ltac:(cbn; lia) ltac:(cbn; lia)). }
    destruct (I_base g pos ly6 S6 W6 _ _ (4 * Z.of_nat nrec + 4 + 1 + 1 + 1)
      [(dp, Z.max (SlotModel.t_cap_disp inp) 1); (tk, Z.max (SlotModel.t_cap_tok inp) 1);
       (nm, Z.max (SlotModel.t_cap_name inp) 1)] HPRE HJ6 Hfrs6 Hbl6)
      as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp6').
    assert (Hp16 : forall a, spZ (ms_regs ms6) <= a < spZ (ms_regs ms6) + 16 -> apresent (w_H W6) (ms_mem ms6) a).
    { intros a Ha. rewrite Usp6 in Ha. apply Hstkp6'. clear - Ha Hmfb HSTK' Hsp0al; fold sp0 in Hmfb; lia. }
    pose proof (I_rod g pos ly6 S6 W6 (ms_mem ms6) _ _ HJ6 HPRE) as HROD6.
    destruct (HIMG W6 (ms_mem ms6) HROD6) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrbnimg6 & _).
    pose proof HJ6 as (_ & _ & _ & _ & _ & _ & Hnev6 & _).
    assert (Hbsum6 : blocks_bytes S6 = bsum [(dp, Z.max (SlotModel.t_cap_disp inp) 1);
      (tk, Z.max (SlotModel.t_cap_tok inp) 1); (nm, Z.max (SlotModel.t_cap_name inp) 1)] + blocks_bytes (e_S g)).
    { rewrite (blocks_bytes_bsum B ly6 S6), (blocks_bytes_bsum B (e_ly g) (e_S g)).
      destruct Hbl6 as [Hperm _]. rewrite (bsum_perm _ _ Hperm), bsum_app. reflexivity. }
    pose proof (I_hblocks_perm g ly6 S6
      [(dp, Z.max (SlotModel.t_cap_disp inp) 1); (tk, Z.max (SlotModel.t_cap_tok inp) 1);
       (nm, Z.max (SlotModel.t_cap_name inp) 1)]
      [(nm, Z.max (SlotModel.t_cap_name inp) 1);
      (tk, Z.max (SlotModel.t_cap_tok inp) 1); (dp, Z.max (SlotModel.t_cap_disp inp) 1)]
      (Permutation_rev _) Hbl6) as Hbl6'.
    clear VMik VraM Vs0M.
    assert (VMik : forall a (nn : nat) v, mf <= a -> a + Z.of_nat nn <= e_sp0 g ->
      (forall j, 0 <= j < Z.of_nat nn -> ~ (mf + 152 <= a + j < mf + 160) /\ ~ (mf + 184 <= a + j < mf + 192)) ->
      val_mem SEGS (rd W2 mem2) a nn v -> val_mem SEGS (rd W6 (ms_mem ms6)) a nn v).
    { intros a nn v Ha0 Ha1 Hh Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W6) mem2 (ms_mem ms6) a a nn v); [|exact Hv].
      intros kk Hkk. apply HIKj. left. destruct (Hh kk Hkk) as [Hhh1 Hhh2].
      split; [clear - Ha0 Ha1 Hkk; lia | split; assumption]. }
    assert (VraM : val_mem SEGS (rd W6 (ms_mem ms6)) (sp0 - 8) 8 RA_LLVMF).
    { apply VMik; [clear - Hmf0 Hsp47 Hmfb; fold sp0 in Hmfb; lia | clear - Hmfb; fold sp0 in Hmfb; lia
      | intros j Hj; split; clear - Hmfb Hj; fold sp0 in Hmfb; lia | exact Vra]. }
    assert (Vs0M : val_mem SEGS (rd W6 (ms_mem ms6)) (sp0 - 16) 8 (s0Z (e_regs g))).
    { apply VMik; [clear - Hmf0 Hsp47 Hmfb; fold sp0 in Hmfb; lia | clear - Hmfb; fold sp0 in Hmfb; lia
      | intros j Hj; split; clear - Hmfb Hj; fold sp0 in Hmfb; lia | exact Vs0]. }
    pmkst HSc6. rewrite (PSIG IS_reac_box_name AF_reac_box_name eq_refl).
    eapply (I_pcall g pos mf W6 (ms_regs ms6) (ms_mem ms6) _ ly6 S6 (4 * Z.of_nat nrec + 4 + 1 + 1 + 1) _ 16
      reac_box_name.REAC_BOX_NAME_STK
      (reac_box_name.rbn_fp 0 8 tk (SlotModel.t_cap_tok inp) dp (SlotModel.t_cap_disp inp))
      (BASE + AF_reac_box_name) 0x1228 _ _ HPRE HJ6 Hfrs6 Hbl6 Hmfb Hmf32 VraM Vs0M (or_intror eq_refl)
      T2' T8 T3 T4 T1 ltac:(lia) ltac:(reflexivity)
      ltac:(unfold reac_box_name.REAC_BOX_NAME_STK, ESTACK; lia) ltac:(lia) ltac:(clear - Hnr64; unfold EV_LLVMF; lia)
      MLE6 MOK6
      (fun ch HPRE1 => HBN ly6 S6 W6 (ms_regs ms6) (ms_mem ms6) _ ch (SlotModel.n_fam inp) (I_said g pos) 8 8 0 8
        tk (SlotModel.t_cap_tok inp) dp (SlotModel.t_cap_disp inp) (I_sd inp) HPRE1 HROD6
        T10 ltac:(clear - Hnfr; lia) T11 ltac:(unfold I_said; destruct (_ =? 0); clear - HSF0 HSF1 C1; unfold V_id; lia)
        T12 ltac:(lia) T13 ltac:(lia) T14 ltac:(lia) T15 ltac:(lia) T16 ltac:(clear - Htkr; lia)
        T17 ltac:(lia) Hp16 Vdp ltac:(clear - Hdpr; lia) Vcd ltac:(lia) Hrbnimg6
        (fun Hok => ltac:(exfalso; unfold reac_box_name_c.bn_args_ok in Hok; cbn in Hok; discriminate))
        ltac:(rewrite Hfrs6; cbn; lia)
        ltac:(unfold reac_box_name.EV_REAC_BOX_NAME; clear - Hnev6 Hnev0 Hnr64 HEV; unfold EV_LLVMF in *; lia)
        ltac:(unfold reac_box_name.LIVE_REAC_BOX_NAME; rewrite Hbsum6; unfold bsum; cbn [fold_right snd];
              clear - Hbb0 HLIVE Hcn Hct Hcd; unfold LIVE_LLVMF in *; lia))).
    * intros a (r & Hin & Hr). unfold reac_box_name.rbn_fp in Hin. cbn [In] in Hin.
      destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
      -- rewrite Z.eqb_refl in Hr. lia.
      -- rewrite (proj2 (Z.eqb_neq tk 0) ltac:(lia)) in Hr.
         exists tk, (Z.max (SlotModel.t_cap_tok inp) 1). split; [|split].
         ++ destruct Hbl6 as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)).
            apply in_or_app. left. right. left. reflexivity.
         ++ exact Htknew.
         ++ pose proof (req_size_pos (Z.max (SlotModel.t_cap_tok inp) 1) ltac:(lia)). lia.
      -- rewrite (proj2 (Z.eqb_neq dp 0) ltac:(lia)) in Hr.
         exists dp, (Z.max (SlotModel.t_cap_disp inp) 1). split; [exact Hdpin | split; [exact Hdpnew|]].
         pose proof (req_size_pos (Z.max (SlotModel.t_cap_disp inp) 1) ltac:(lia)). lia.
    * intros (r & Hin & Hr). unfold reac_box_name.rbn_fp in Hin. cbn [In] in Hin.
      destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
      -- rewrite Z.eqb_refl in Hr. lia.
      -- lia.
      -- lia.
    * intros ly' S' W' regs' mem' md' (_ & HPm & _). exact HPm.
    * intros W7 ly7 S7 regs7 mem7 md7 Hwle7 HJ7 HP7 Hfrs7 Hbl7 HK7 MLE7 MOK7 HPost.
      destruct HPost as (-> & HPm7 & Hif).
      assert (Hacc1 : reac_box_name_c.bn_accept (SlotModel.n_fam inp) (I_sd inp) 8 8 0 8 tk (SlotModel.t_cap_tok inp)
        dp (SlotModel.t_cap_disp inp) = false) by reflexivity.
      rewrite Hacc1 in Hif. destruct Hif as (R10r1 & Hkp1).
      (* the call keeps the protected bytes: its footprint lies in tk / dp *)
      pose proof HK7 as (SK1 & SK2 & _ & SK4 & _).
      assert (HIK7 : ikept g pos mf W6 (ms_mem ms6) W6 mem7).
      { apply (I_ikept_of g pos mf ly6 S6 W6 (ms_mem ms6) W6 mem7
          (mf - 16 - reac_box_name.REAC_BOX_NAME_STK)
          (inFP (reac_box_name.rbn_fp 0 8 tk (SlotModel.t_cap_tok inp) dp (SlotModel.t_cap_disp inp)))
          EFA6 Hin46 Hinb6 ltac:(clear - Hmf0 C1; lia) Hsp47);
        [ intros a Ha1 Ha2; apply SK1; [exact Ha1 | intro Hc; apply Ha2; clear - Hc; lia]
        | exact SK2 | exact SK4 | ].
        intros a (r & Hin & Hr). unfold reac_box_name.rbn_fp in Hin. cbn [In] in Hin.
        destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
        - rewrite Z.eqb_refl in Hr. lia.
        - rewrite (proj2 (Z.eqb_neq tk 0) ltac:(lia)) in Hr. apply Htkap.
          pose proof (req_size_pos (Z.max (SlotModel.t_cap_tok inp) 1) ltac:(lia)). lia.
        - rewrite (proj2 (Z.eqb_neq dp 0) ltac:(lia)) in Hr. apply Hdpap.
          pose proof (req_size_pos (Z.max (SlotModel.t_cap_disp inp) 1) ltac:(lia)). lia. }
      pose proof (ikept_trans g pos mf W2 mem2 W6 (ms_mem ms6) W6 mem7 HIKj HIK7) as HIKk.
      clear HIKj HIK7 SK1 SK2 SK4.
      jafter_call_keep_hi HSc6 576%nat regs7 (mrestrict (w_H W6) mem7) HP7 [0%nat; 1%nat; 2%nat] HS7.
      match type of HS7 with ?Q -> _ => assert (HQ : Q); [|specialize (HS7 HQ); clear HQ] end.
      { cbn [ms_mem restrict]. constructor; [|constructor; [|constructor; [|constructor]]].
        - eapply (region_kept_stack_aj SEGS B); [exact HK7 | exact HJ7 | exact U2c |
            lia | clear - Hmfb Hsp0al HSTK'; fold sp0 in Hmfb; lia |
            clear - Hmfb; fold sp0 in Hmfb; lia | lia | lia].
        - eapply (region_kept_stack_aj SEGS B); [exact HK7 | exact HJ7 | exact U9c |
            lia | clear - Hmfb Hsp0al HSTK'; fold sp0 in Hmfb; lia |
            clear - Hmfb; fold sp0 in Hmfb; lia | lia | lia].
        - eapply (region_kept_stack_aj SEGS B); [exact HK7 | exact HJ7 | exact U9c |
            lia | clear - Hmfb Hsp0al HSTK'; fold sp0 in Hmfb; lia |
            clear - Hmfb; fold sp0 in Hmfb; lia | lia | lia]. }
      rewrite <- restrict_mkst_fx in HS7.
      pose proof (img_env_havoc_hi E4 576%nat (map (getr regs7) CLOB) HEI6 ltac:(cbv; lia)) as HEI7.
      set (E5 := havoc E4 576%nat (map (getr regs7) CLOB)) in HS7, HEI7.
      assert (U2d : bv_unsigned (ew E5 2) = mf)
        by (unfold E5; rewrite (ew_havoc_old E4 576%nat (map (getr regs7) CLOB) 2 ltac:(lia)); exact U2c).
      assert (U9d : bv_unsigned (ew E5 9) = mf)
        by (unfold E5; rewrite (ew_havoc_old E4 576%nat (map (getr regs7) CLOB) 9 ltac:(lia)); exact U9c).
      (* 0x81934 addi sp,sp,16; 0x81938 li a1,-1; 0x8193c bne a0,a1 *)
      paj_run_to_sh RUNTOP HS7 HJ7 0x1230.
      { intros a (r & Hin & Hr). cbn [In] in Hin. destruct Hin as [Heq | [Heq | [Heq | []]]]; subst r;
          cbn [I_rS I_r0 I_r1 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
          [rewrite U2d in Hr | rewrite U9d in Hr | rewrite U9d in Hr];
          left; clear - Hr Hmfb HSTK' Hsp0al Hmf0 C1; fold sp0 in Hmfb; lia. }
      assert (KEEPq2 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 152 <= a < mf + 160) -> ~ (mf + 184 <= a < mf + 192) ->
        ~ (mf - 16 <= a < mf) -> aview SEGS (w_H W6) (ms_mem ms7) a = aview SEGS (w_H W6) mem7 a).
      { intros a Ha H1 H2 H3. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia.
        intros (r & Hin & Hr). cbn [In] in Hin. destruct Hin as [Heq | [Heq | [Heq | []]]]; subst r;
          cbn [I_rS I_r0 I_r1 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
          [rewrite U2d in Hr | rewrite U9d in Hr | rewrite U9d in Hr]; lia. }
      assert (Hbl7' : hblocks B g ly7 S7 [(dp, Z.max (SlotModel.t_cap_disp inp) 1);
        (tk, Z.max (SlotModel.t_cap_tok inp) 1); (nm, Z.max (SlotModel.t_cap_name inp) 1)]) by exact Hbl7.
      destruct (I_base g pos ly7 S7 W6 _ _ (4 * Z.of_nat nrec + 4 + 1 + 1 + 1)
        _ HPRE HJ7 Hfrs7 Hbl7') as (EFA7 & Hin47 & _ & _ & _ & _ & _ & _ & _ & Hinb7 & _).
      pose proof (ikept_trans g pos mf W2 mem2 W6 mem7 W6 (ms_mem ms7) HIKk
        (I_ikept_run16 g pos mf ly7 S7 W6 mem7 (ms_mem ms7) _ _ (4 * Z.of_nat nrec + 4 + 1 + 1 + 1)
          HJ7 Hfrs7 Hinb7 EFA7 ltac:(clear - Hmf0 C1; lia) Hsp47 KEEPq2)) as HIKl.
      clear HIKk KEEPq2 HF HFr HG.
      eapply (paj_branch W6 E5 _ ms7 _ _ BC_NE (SOff 580 0) (SLit 18446744073709551615) HS7).
      { intros Hbt _. exfalso.
        assert (Hew580 : ew E5 580 = Z_to_bv 64 (-1)).
        { unfold E5. change 580%nat with (576 + 4)%nat. rewrite I_ew_a0, R10r1. reflexivity. }
        rewrite YO0c.branch_ne in Hbt. cbn [sv_denot] in Hbt. rewrite Hew580 in Hbt.
        vm_compute in Hbt. discriminate. }
      intros Hbf5 HSc7.
      (* ---- reac_box_name #2 at 0x8196c ---- *)
      paj_run_shc RUNP RUNC HSc7 HJ7.
      { intros a (r & Hin & Hr). cbn [In] in Hin. destruct Hin as [Heq | [Heq | [Heq | []]]]; subst r;
          cbn [I_rS I_r0 I_r1 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
          [rewrite U2d in Hr | rewrite U9d in Hr | rewrite U9d in Hr];
          left; clear - Hr Hmfb HSTK' Hsp0al Hmf0 C1; fold sp0 in Hmfb; lia. }
      assert (KEEPq3 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 152 <= a < mf + 160) -> ~ (mf + 184 <= a < mf + 192) ->
        ~ (mf - 16 <= a < mf) -> aview SEGS (w_H W6) (ms_mem ms8) a = aview SEGS (w_H W6) (ms_mem ms7) a).
      { intros a Ha H1 H2 H3. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia.
        intros (r & Hin & Hr). cbn [In] in Hin. destruct Hin as [Heq | [Heq | [Heq | []]]]; subst r;
          cbn [I_rS I_r0 I_r1 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
          [rewrite U2d in Hr | rewrite U9d in Hr | rewrite U9d in Hr]; lia. }
      pose proof (ikept_trans g pos mf W2 mem2 W6 (ms_mem ms7) W6 (ms_mem ms8) HIKl
        (I_ikept_run16 g pos mf ly7 S7 W6 (ms_mem ms7) (ms_mem ms8) _ _ (4 * Z.of_nat nrec + 4 + 1 + 1 + 1)
          HJ7 Hfrs7 Hinb7 EFA7 ltac:(clear - Hmf0 C1; lia) Hsp47 KEEPq3)) as HIKm.
      clear HIKl KEEPq3 HF HFr HG.
      assert (Ew5 : forall n, (n < 576)%nat -> ew E5 n = ew E4 n)
        by (intros n Hn; unfold E5; apply ew_havoc_old; exact Hn).
      assert (Hew532 : ew E4 532 = Z_to_bv 64 nm).
      { unfold E4. rewrite (ew_havoc_old E3 560%nat _ 532 ltac:(lia)). unfold E3.
        rewrite (ew_havoc_old E2 544%nat _ 532 ltac:(lia)). unfold E2.
        change 532%nat with (528 + 4)%nat. rewrite I_ew_a0, Hres4. reflexivity. }
      prreg HSc7 (10%bv : bv 5) V10. prreg HSc7 (11%bv : bv 5) V11. prreg HSc7 (12%bv : bv 5) V12.
      prreg HSc7 (13%bv : bv 5) V13. prreg HSc7 (14%bv : bv 5) V14. prreg HSc7 (15%bv : bv 5) V15.
      prreg HSc7 (16%bv : bv 5) V16. prreg HSc7 (17%bv : bv 5) V17. prreg HSc7 (2%bv : bv 5) V2.
      prreg HSc7 (1%bv : bv 5) V1. prreg HSc7 (8%bv : bv 5) V8. prreg HSc7 (3%bv : bv 5) V3.
      prreg HSc7 (4%bv : bv 5) V4.
      rewrite (Ew5 25%nat ltac:(lia)), (EE4 25%nat 25%bv ltac:(lia) eq_refl), R25 in V10.
      rewrite (Ew5 36%nat ltac:(lia)), (Ew5 32%nat ltac:(lia)), (EA 36%nat ltac:(lia)), (EA 32%nat ltac:(lia)), E36, E32 in V11.
      rewrite (I_said_expr (RcIdentModel.has_model_name (m_id g nrec)) (SF + V_id + 3) Hhm
        ltac:(clear - HSF0 HSF1 C1; unfold V_id; lia)) in V11.
      rewrite (Ew5 34%nat ltac:(lia)), (EA 34%nat ltac:(lia)), E34 in V12.
      rewrite (Ew5 35%nat ltac:(lia)), (EA 35%nat ltac:(lia)), E35 in V13.
      rewrite (Ew5 532%nat ltac:(lia)), Hew532 in V14.
      rewrite (Ew5 26%nat ltac:(lia)), (EE4 26%nat 26%bv ltac:(lia) eq_refl), R26 in V15. unfold w64 in V15.
      rewrite (I_and255 (SlotModel.t_cap_name inp) ltac:(lia)) in V15.
      rewrite (Ew5 548%nat ltac:(lia)), Hew548 in V16.
      rewrite (Ew5 24%nat ltac:(lia)), (EE4 24%nat 24%bv ltac:(lia) eq_refl), R24 in V17. unfold w64 in V17.
      rewrite (I_and255 (SlotModel.t_cap_tok inp) ltac:(lia)), (I_add0 (SlotModel.t_cap_tok inp) ltac:(lia)) in V17.
      rewrite U2d in V2.
      assert (V2' : getr (ms_regs ms8) 2 = w64 (mf - 16)) by (rewrite V2; unfold w64; f_equal; lia).
      rewrite (Ew5 8%nat ltac:(lia)), (EE4 8%nat 8%bv ltac:(lia) eq_refl), R8 in V8.
      rewrite (Ew5 3%nat ltac:(lia)), (EE4 3%nat 3%bv ltac:(lia) eq_refl), R3 in V3.
      rewrite (Ew5 4%nat ltac:(lia)), (EE4 4%nat 4%bv ltac:(lia) eq_refl), R4 in V4.
      assert (Usp8 : spZ (ms_regs ms8) = mf - 16).
      { unfold spZ. rewrite V2'. unfold w64. apply unsigned_lit_small. clear - Hmf0 Hsp47 Hmfb C1; fold sp0 in Hmfb; lia. }
      pose proof (st_ok_region_nth E5 _ _ 0%nat (YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0
          [YP09.mkChunk (-8) (CVal 8 (SOff 27 0)); YP09.mkChunk (-16) (CVal 8 (SOff 564 0))]) HSc7
        ltac:(vm_compute; reflexivity)) as HRS2.
      assert (Vdp2 : val_mem SEGS (rd W6 (ms_mem ms8)) (spZ (ms_regs ms8)) 8 dp).
      { rewrite Usp8. replace (mf - 16) with (mf + -16) by lia.
        exact (field_of_region E5 _ 2%nat mf _ (-16) 0 (-16) 0 (-16) 8%N (SOff 564 0) dp HRS2 U2d
          ltac:(right; left; reflexivity)
          ltac:(cbn [sv_denot]; rewrite (Ew5 564%nat ltac:(lia)), Hew564, unsigned_lit_small, Z.add_0_r by lia; reflexivity)
          ltac:(cbn; lia) ltac:(cbn; lia)). }
      assert (Vcd2 : val_mem SEGS (rd W6 (ms_mem ms8)) (spZ (ms_regs ms8) + 8) 8 (SlotModel.t_cap_disp inp)).
      { rewrite Usp8. replace (mf - 16 + 8) with (mf + -8) by lia.
        exact (field_of_region E5 _ 2%nat mf _ (-16) 0 (-16) 0 (-8) 8%N (SOff 27 0) (SlotModel.t_cap_disp inp) HRS2 U2d
          ltac:(left; reflexivity)
          ltac:(cbn [sv_denot]; rewrite (Ew5 27%nat ltac:(lia)), (EE4 27%nat 27%bv ltac:(lia) eq_refl), R27; unfold w64;
                rewrite unsigned_lit_small, Z.add_0_r by lia; reflexivity)
          ltac:(cbn; lia) ltac:(cbn; lia)). }
      destruct (I_base g pos ly7 S7 W6 _ _ (4 * Z.of_nat nrec + 4 + 1 + 1 + 1) _ HPRE HJ7 Hfrs7 Hbl7')
        as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp7).
      assert (Hp16b : forall a, spZ (ms_regs ms8) <= a < spZ (ms_regs ms8) + 16 -> apresent (w_H W6) (ms_mem ms8) a).
      { intros a Ha. rewrite Usp8 in Ha. apply Hstkp7. clear - Ha Hmfb HSTK' Hsp0al; fold sp0 in Hmfb; lia. }
      pose proof (I_rod g pos ly7 S7 W6 (ms_mem ms8) _ _ HJ7 HPRE) as HROD8.
      destruct (HIMG W6 (ms_mem ms8) HROD8) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrbnimg8 & _).
      pose proof HJ7 as (_ & _ & _ & _ & _ & _ & Hnev7 & _).
      assert (Hbsum7 : blocks_bytes S7 = bsum [(dp, Z.max (SlotModel.t_cap_disp inp) 1);
        (tk, Z.max (SlotModel.t_cap_tok inp) 1); (nm, Z.max (SlotModel.t_cap_name inp) 1)] + blocks_bytes (e_S g)).
      { rewrite (blocks_bytes_bsum B ly7 S7), (blocks_bytes_bsum B (e_ly g) (e_S g)).
        destruct Hbl7' as [Hperm _]. rewrite (bsum_perm _ _ Hperm), bsum_app. reflexivity. }
      pose proof (I_hblocks_perm g ly7 S7
        [(dp, Z.max (SlotModel.t_cap_disp inp) 1); (tk, Z.max (SlotModel.t_cap_tok inp) 1);
         (nm, Z.max (SlotModel.t_cap_name inp) 1)]
        [(nm, Z.max (SlotModel.t_cap_name inp) 1);
        (tk, Z.max (SlotModel.t_cap_tok inp) 1); (dp, Z.max (SlotModel.t_cap_disp inp) 1)]
        (Permutation_rev _) Hbl7') as Hbl7r.
      pose proof (I_id_at_moved g pos nrec W2 W6 mem2 (ms_mem ms8) HSF0 HSF64
        (fun a Ha => HIKm a (or_intror (or_introl Ha))) Hid) as Hid8.
      clear VMik VraM Vs0M.
      assert (VMik : forall a (nn : nat) v, mf <= a -> a + Z.of_nat nn <= e_sp0 g ->
        (forall j, 0 <= j < Z.of_nat nn -> ~ (mf + 152 <= a + j < mf + 160) /\ ~ (mf + 184 <= a + j < mf + 192)) ->
        val_mem SEGS (rd W2 mem2) a nn v -> val_mem SEGS (rd W6 (ms_mem ms8)) a nn v).
      { intros a nn v Ha0 Ha1 Hh Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W6) mem2 (ms_mem ms8) a a nn v); [|exact Hv].
        intros kk Hkk. apply HIKm. left. destruct (Hh kk Hkk) as [Hhh1 Hhh2].
        split; [clear - Ha0 Ha1 Hkk; lia | split; assumption]. }
      assert (VraM : val_mem SEGS (rd W6 (ms_mem ms8)) (sp0 - 8) 8 RA_LLVMF).
      { apply VMik; [clear - Hmf0 Hsp47 Hmfb; fold sp0 in Hmfb; lia | clear - Hmfb; fold sp0 in Hmfb; lia
        | intros j Hj; split; clear - Hmfb Hj; fold sp0 in Hmfb; lia | exact Vra]. }
      assert (Vs0M : val_mem SEGS (rd W6 (ms_mem ms8)) (sp0 - 16) 8 (s0Z (e_regs g))).
      { apply VMik; [clear - Hmf0 Hsp47 Hmfb; fold sp0 in Hmfb; lia | clear - Hmfb; fold sp0 in Hmfb; lia
        | intros j Hj; split; clear - Hmfb Hj; fold sp0 in Hmfb; lia | exact Vs0]. }
      pmkst HSc7. rewrite (PSIG IS_reac_box_name AF_reac_box_name eq_refl).
      eapply (I_pcall g pos mf W6 (ms_regs ms8) (ms_mem ms8) _ ly7 S7 (4 * Z.of_nat nrec + 4 + 1 + 1 + 1) _ 16
        reac_box_name.REAC_BOX_NAME_STK
        (reac_box_name.rbn_fp nm (SlotModel.t_cap_name inp) tk (SlotModel.t_cap_tok inp) dp (SlotModel.t_cap_disp inp))
        (BASE + AF_reac_box_name) 0x1264 _ _ HPRE HJ7 Hfrs7 Hbl7' Hmfb Hmf32 VraM Vs0M (or_intror eq_refl)
        V2' V8 V3 V4 V1 ltac:(lia) ltac:(reflexivity)
        ltac:(unfold reac_box_name.REAC_BOX_NAME_STK, ESTACK; lia) ltac:(lia) ltac:(clear - Hnr64; unfold EV_LLVMF; lia)
        MLE7 MOK7
        (fun ch HPRE1 => HBN ly7 S7 W6 (ms_regs ms8) (ms_mem ms8) _ ch (SlotModel.n_fam inp) (I_said g pos)
          (SlotModel.t_in inp) (SlotModel.t_out inp) nm (SlotModel.t_cap_name inp)
          tk (SlotModel.t_cap_tok inp) dp (SlotModel.t_cap_disp inp) (I_sd inp) HPRE1 HROD8
          V10 ltac:(clear - Hnfr; lia) V11 ltac:(unfold I_said; destruct (_ =? 0); clear - HSF0 HSF1 C1; unfold V_id; lia)
          V12 ltac:(lia) V13 ltac:(lia) V14 ltac:(clear - Hnmr; lia) V15 ltac:(lia) V16 ltac:(clear - Htkr; lia)
          V17 ltac:(lia) Hp16b Vdp2 ltac:(clear - Hdpr; lia) Vcd2 ltac:(lia) Hrbnimg8
          (fun _ => conj
            (I_rbn_said B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
               ameta_inv arodata_okS LAWS g pos ly7 S7 W6 (ms_mem ms8) _ _ HPRE HJ7 Hfrs7 Hid8)
            (I_rbn_bufs B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
               ameta_inv arodata_okS LAWS g pos ly7 S7 W6 (ms_mem ms8) _ _ nm tk dp HPRE HJ7 Hfrs7 Hbl7r))
          ltac:(rewrite Hfrs7; cbn; lia)
          ltac:(unfold reac_box_name.EV_REAC_BOX_NAME; clear - Hnev7 Hnev0 Hnr64 HEV; unfold EV_LLVMF in *; lia)
          ltac:(unfold reac_box_name.LIVE_REAC_BOX_NAME; rewrite Hbsum7; unfold bsum; cbn [fold_right snd];
                clear - Hbb0 HLIVE Hcn Hct Hcd; unfold LIVE_LLVMF in *; lia))).
      -- intros a (r & Hin & Hr). unfold reac_box_name.rbn_fp in Hin. cbn [In] in Hin.
         destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
         ++ rewrite (proj2 (Z.eqb_neq nm 0) ltac:(lia)) in Hr.
            exists nm, (Z.max (SlotModel.t_cap_name inp) 1). split; [|split].
            ** destruct Hbl7' as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)).
               apply in_or_app. left. right. right. left. reflexivity.
            ** exact Hnmnew.
            ** pose proof (req_size_pos (Z.max (SlotModel.t_cap_name inp) 1) ltac:(lia)). lia.
         ++ rewrite (proj2 (Z.eqb_neq tk 0) ltac:(lia)) in Hr.
            exists tk, (Z.max (SlotModel.t_cap_tok inp) 1). split; [|split].
            ** destruct Hbl7' as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)).
               apply in_or_app. left. right. left. reflexivity.
            ** exact Htknew.
            ** pose proof (req_size_pos (Z.max (SlotModel.t_cap_tok inp) 1) ltac:(lia)). lia.
         ++ rewrite (proj2 (Z.eqb_neq dp 0) ltac:(lia)) in Hr.
            exists dp, (Z.max (SlotModel.t_cap_disp inp) 1). split; [|split].
            ** destruct Hbl7' as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)).
               apply in_or_app. left. left. reflexivity.
            ** exact Hdpnew.
            ** pose proof (req_size_pos (Z.max (SlotModel.t_cap_disp inp) 1) ltac:(lia)). lia.
      -- intros (r & Hin & Hr). unfold reac_box_name.rbn_fp in Hin. cbn [In] in Hin.
         destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; lia.
      -- intros ly' S' W' regs' mem' md' (_ & HPm & _). exact HPm.
      -- intros W8 ly8 S8 regs8 mem8 md8 Hwle8 HJ8 HP8 Hfrs8 Hbl8 HK8 MLE8 MOK8 HPost.
         destruct HPost as (-> & HPm8 & Hif2).
         change (I_sd inp) with (IM.sdZ inp) in Hif2.
         rewrite (IM.accept_eq inp nm tk dp ltac:(lia) ltac:(lia) ltac:(lia)) in Hif2.
         pose proof HK8 as (SK1 & SK2 & _ & SK4 & _).
         assert (HIK8 : ikept g pos mf W6 (ms_mem ms8) W6 mem8).
         { apply (I_ikept_of g pos mf ly7 S7 W6 (ms_mem ms8) W6 mem8
             (mf - 16 - reac_box_name.REAC_BOX_NAME_STK)
             (inFP (reac_box_name.rbn_fp nm (SlotModel.t_cap_name inp) tk (SlotModel.t_cap_tok inp) dp
               (SlotModel.t_cap_disp inp)))
             EFA7 Hin47 Hinb7 ltac:(clear - Hmf0 C1; lia) Hsp47);
           [ intros a Ha1 Ha2; apply SK1; [exact Ha1 | intro Hc; apply Ha2; clear - Hc; lia]
           | exact SK2 | exact SK4 | ].
           intros a (r & Hin & Hr). unfold reac_box_name.rbn_fp in Hin. cbn [In] in Hin.
           destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
           - rewrite (proj2 (Z.eqb_neq nm 0) ltac:(lia)) in Hr. apply Hnmap.
             pose proof (req_size_pos (Z.max (SlotModel.t_cap_name inp) 1) ltac:(lia)). lia.
           - rewrite (proj2 (Z.eqb_neq tk 0) ltac:(lia)) in Hr. apply Htkap.
             pose proof (req_size_pos (Z.max (SlotModel.t_cap_tok inp) 1) ltac:(lia)). lia.
           - rewrite (proj2 (Z.eqb_neq dp 0) ltac:(lia)) in Hr. apply Hdpap.
             pose proof (req_size_pos (Z.max (SlotModel.t_cap_disp inp) 1) ltac:(lia)). lia. }
         pose proof (ikept_trans g pos mf W2 mem2 W6 (ms_mem ms8) W6 mem8 HIKm HIK8) as HIKn.
         clear HIKm HIK8 SK1 SK2 SK4.
         jafter_call_keep_hi HSc7 592%nat regs8 (mrestrict (w_H W6) mem8) HP8 [1%nat; 2%nat] HS8.
         match type of HS8 with ?Q -> _ => assert (HQ : Q); [|specialize (HS8 HQ); clear HQ] end.
         { cbn [ms_mem restrict]. constructor; [|constructor; [|constructor]].
           - eapply (region_kept_stack_aj SEGS B); [exact HK8 | exact HJ8 | exact U9d |
               lia | clear - Hmfb Hsp0al HSTK'; fold sp0 in Hmfb; lia |
               clear - Hmfb; fold sp0 in Hmfb; lia | lia | lia].
           - eapply (region_kept_stack_aj SEGS B); [exact HK8 | exact HJ8 | exact U9d |
               lia | clear - Hmfb Hsp0al HSTK'; fold sp0 in Hmfb; lia |
               clear - Hmfb; fold sp0 in Hmfb; lia | lia | lia]. }
         rewrite <- restrict_mkst_fx in HS8.
         pose proof (img_env_havoc_hi E5 592%nat (map (getr regs8) CLOB) HEI7 ltac:(cbv; lia)) as HEI8.
         set (E6 := havoc E5 592%nat (map (getr regs8) CLOB)) in HS8, HEI8.
         assert (U9e : bv_unsigned (ew E6 9) = mf)
           by (unfold E6; rewrite (ew_havoc_old E5 592%nat (map (getr regs8) CLOB) 9 ltac:(lia)); exact U9d).
         (* 0x81970 addi sp,sp,16 *)
         paj_run_to_sh RUNTOP HS8 HJ8 0x1268.
         { i_awr2 U9e Hmfb HSTK' Hsp0al Hmf0 C1 sp0. }
         assert (KEEPz : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 152 <= a < mf + 160) -> ~ (mf + 184 <= a < mf + 192) ->
           aview SEGS (w_H W6) (ms_mem ms9) a = aview SEGS (w_H W6) mem8 a) by i_keep2 HFr U9e.
         destruct (I_base g pos ly8 S8 W6 _ _ (4 * Z.of_nat nrec + 4 + 1 + 1 + 1) _ HPRE HJ8 Hfrs8 Hbl8)
           as (EFA8 & Hin48 & _ & _ & _ & _ & _ & _ & _ & Hinb8 & _).
         pose proof (ikept_trans g pos mf W2 mem2 W6 mem8 W6 (ms_mem ms9) HIKn
           (I_ikept_run g pos mf ly8 S8 W6 mem8 (ms_mem ms9) _ _ (4 * Z.of_nat nrec + 4 + 1 + 1 + 1)
             HJ8 Hfrs8 Hinb8 EFA8 ltac:(clear - Hmf0 C1; lia) Hsp47 KEEPz)) as HIKz.
         assert (Ew6 : forall n, (n < 592)%nat -> ew E6 n = ew E5 n)
           by (intros n Hn; unfold E6; apply ew_havoc_old; exact Hn).
         assert (EA6 : forall n, (n < 512)%nat -> ew E6 n = ew E n)
           by (intros n Hn; rewrite (Ew6 n ltac:(lia)), (Ew5 n ltac:(lia)); apply EA; exact Hn).
         assert (EEf : forall n (r : bv 5), (n < 512)%nat -> Z.of_nat n = bv_unsigned r -> ew E6 n = getr regs2 r)
           by (intros n r Hn Hr; rewrite (EA6 n Hn); apply EE; exact Hr).
         prreg HS8 (10%bv : bv 5) F10. prreg HS8 (25%bv : bv 5) F25. prreg HS8 (23%bv : bv 5) F23.
         prreg HS8 (24%bv : bv 5) F24. prreg HS8 (26%bv : bv 5) F26. prreg HS8 (20%bv : bv 5) F20.
         prreg HS8 (21%bv : bv 5) F21. prreg HS8 (22%bv : bv 5) F22.
         prreg HS8 (2%bv : bv 5) F2. prreg HS8 (9%bv : bv 5) F9. prreg HS8 (8%bv : bv 5) F8.
         prreg HS8 (3%bv : bv 5) F3. prreg HS8 (4%bv : bv 5) F4. prreg HS8 (19%bv : bv 5) F19.
         rewrite (EEf 25%nat 25%bv ltac:(lia) eq_refl), R25 in F25.
         rewrite (EA6 36%nat ltac:(lia)), E36 in F23.
         rewrite (EA6 34%nat ltac:(lia)), E34 in F24.
         rewrite (EA6 35%nat ltac:(lia)), E35 in F26.
         rewrite (EEf 24%nat 24%bv ltac:(lia) eq_refl), R24 in F20. unfold w64 in F20.
         rewrite (I_and255 (SlotModel.t_cap_tok inp) ltac:(lia)) in F20.
         rewrite (Ew6 548%nat ltac:(lia)), (Ew5 548%nat ltac:(lia)), Hew548 in F21.
         rewrite (Ew6 564%nat ltac:(lia)), (Ew5 564%nat ltac:(lia)), Hew564 in F22.
         rewrite (EEf 2%nat 2%bv ltac:(lia) eq_refl) in F2.
         rewrite (EEf 9%nat 9%bv ltac:(lia) eq_refl) in F9.
         rewrite (EEf 8%nat 8%bv ltac:(lia) eq_refl) in F8.
         rewrite (EEf 3%nat 3%bv ltac:(lia) eq_refl) in F3.
         rewrite (EEf 4%nat 4%bv ltac:(lia) eq_refl) in F4.
         rewrite (EEf 19%nat 19%bv ltac:(lia) eq_refl) in F19.
         assert (F10' : getr (ms_regs ms9) 10 = getr regs8 10).
         { rewrite F10. unfold E6. change 596%nat with (592 + 4)%nat. apply I_ew_a0. }
         (* the result r = n_r and, when it is 0, the three strings in nm / tk / dp *)
         assert (HRES : getr regs8 10 = w64 (SlotModel.n_r inp) /\
           (SlotModel.n_r inp = 0 ->
             garr8 SEGS (mrestrict (w_H W6) mem8) nm
               (bn_NM (SlotModel.n_fam inp) (IM.sdZ inp) (SlotModel.t_in inp) (SlotModel.t_out inp) ++ [0]) /\
             garr8 SEGS (mrestrict (w_H W6) mem8) tk
               (bn_TK (bn_NM (SlotModel.n_fam inp) (IM.sdZ inp) (SlotModel.t_in inp) (SlotModel.t_out inp)) ++ [0]) /\
             garr8 SEGS (mrestrict (w_H W6) mem8) dp
               (bn_DP (bn_NM (SlotModel.n_fam inp) (IM.sdZ inp) (SlotModel.t_in inp) (SlotModel.t_out inp))
                  (SlotModel.t_in inp) (SlotModel.t_out inp) ++ [0]))).
         { destruct (Z.eqb_spec (SlotModel.n_r inp) 0) as [Hr0 | Hr0].
           - rewrite Hr0. hnf in Hif2.
             destruct Hif2 as (Ha & Gn & Gt & Gd & _).
             split; [exact Ha | intros _; split; [exact Gn | split; [exact Gt | exact Gd]]].
           - hnf in Hif2. destruct Hif2 as (Ha & _).
             destruct (IM.n_r_cases inp) as [E0 | Em1]; [contradiction|].
             split; [rewrite Em1; exact Ha | intros E0; contradiction]. }
         (* the two frame slots the tail wrote *)
         pose proof (st_ok_pi_region_nth E6 _ _ 1%nat (YP09.mkRegion (Some 9%nat) 184 192 184 192
           [YP09.mkChunk 184 (CVal 8 (SOff 532 0))]) HS8 ltac:(vm_compute; reflexivity)) as HRF1.
         pose proof (st_ok_pi_region_nth E6 _ _ 0%nat (YP09.mkRegion (Some 9%nat) 128 184 152 160
           [YP09.mkChunk 152 (CVal 8 (SAlu ALU_AND (SOff 26 0) (SLit 255))); YP09.mkChunk 128 (CVal 8 (SOff 32 0));
            YP09.mkChunk 160 (CVal 8 (SOff 34 0)); YP09.mkChunk 168 (CVal 8 (SOff 35 0))]) HS8
           ltac:(vm_compute; reflexivity)) as HRF0.
         assert (V184 : val_mem SEGS (rd W6 (ms_mem ms9)) (mf + 184) 8 nm).
         { exact (field_of_region E6 _ 9%nat mf _ 184 192 184 192 184 8%N (SOff 532 0) nm HRF1 U9e
             ltac:(left; reflexivity)
             ltac:(cbn [sv_denot]; rewrite (Ew6 532%nat ltac:(lia)), (Ew5 532%nat ltac:(lia)), Hew532,
                   unsigned_lit_small, Z.add_0_r by lia; reflexivity)
             ltac:(cbn; lia) ltac:(cbn; lia)). }
         assert (V152 : val_mem SEGS (rd W6 (ms_mem ms9)) (mf + 152) 8 (SlotModel.t_cap_name inp)).
         { exact (field_of_region E6 _ 9%nat mf _ 128 184 152 160 152 8%N (SAlu ALU_AND (SOff 26 0) (SLit 255))
             (SlotModel.t_cap_name inp) HRF0 U9e
             ltac:(left; reflexivity)
             ltac:(cbn [sv_denot]; rewrite (EEf 26%nat 26%bv ltac:(lia) eq_refl), R26; unfold w64;
                   rewrite unsigned_lit_small, Z.add_0_r by lia; apply I_and255; lia)
             ltac:(cbn; lia) ltac:(cbn; lia)). }
         assert (VMf : forall a (nn : nat) v, mf <= a -> a + Z.of_nat nn <= e_sp0 g ->
           (forall j, 0 <= j < Z.of_nat nn -> ~ (mf + 152 <= a + j < mf + 160) /\ ~ (mf + 184 <= a + j < mf + 192)) ->
           val_mem SEGS (rd W2 mem2) a nn v -> val_mem SEGS (rd W6 (ms_mem ms9)) a nn v).
         { intros a nn v Ha0 Ha1 Hh Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W6) mem2 (ms_mem ms9) a a nn v); [|exact Hv].
           intros kk Hkk. apply HIKz. left. destruct (Hh kk Hkk) as [Hhh1 Hhh2].
           split; [clear - Ha0 Ha1 Hkk; lia | split; assumption]. }
         assert (KZ : forall b l, 4096 <= b -> b < alloc_ceiling -> (length l <= 64)%nat ->
           garr8 SEGS (mrestrict (w_H W6) mem8) b l -> garr8 SEGS (rd W6 (ms_mem ms9)) b l).
         { intros b l Hb0 Hb1 Hl Hg. apply (I_garr8_moved W6 W6 mem8 (ms_mem ms9) b l); [|exact Hg].
           intros kk Hkk. apply KEEPz; clear - Hb0 Hb1 Hl Hkk Hmf0 C1; lia. }
         apply SRr_ret. exists nm, tk, dp. unfold inv_I_end, acut. pmkst HS8.
         eexists ly8, S8, _, _, _. split; [reflexivity|].
         replace (4 * Z.of_nat nrec + 4 + 1 + 1 + 1) with (4 * Z.of_nat nrec + 7) in HJ8, MLE8, MOK8 by lia.
         split; [exact HJ8|]. split; [exact Hfrs8|]. split; [clear - Hnr64; unfold EV_LLVMF; lia|].
         split; [exact MLE8|]. split; [exact MOK8|].
         split; [exact (I_ecommon_kept g pos mf ly2 S2 W2 regs2 mem2 md2 ly8 S8 W6 (ms_regs ms9) (ms_mem ms9) _ _
           HC HJ8 HIKz F2 F9 F8 F3 F4 F19)|].
         split; [exact (I_id_at_moved g pos nrec W2 W6 mem2 (ms_mem ms9) HSF0 HSF64
           (fun a Ha => HIKz a (or_intror (or_introl Ha))) Hid)|].
         split; [unfold mf_id3 in Hmid3 |- *; apply VMf; [clear - Hmf0 C1; lia | clear - Hmfb; fold sp0 in Hmfb; lia
           | intros j Hj; split; lia | exact Hmid3]|].
         split; [exact (I_hblocks_perm g ly8 S8
           [(dp, Z.max (SlotModel.t_cap_disp inp) 1); (tk, Z.max (SlotModel.t_cap_tok inp) 1);
            (nm, Z.max (SlotModel.t_cap_name inp) 1)]
           [(nm, Z.max (SlotModel.t_cap_name inp) 1); (tk, Z.max (SlotModel.t_cap_tok inp) 1);
            (dp, Z.max (SlotModel.t_cap_disp inp) 1)] (Permutation_rev _) Hbl8)|].
         split; [rewrite F10'; exact (proj1 HRES)|].
         split; [exact F25|]. split; [exact F23|]. split; [exact F24|]. split; [exact F26|].
         split; [exact F20|]. split; [exact F21|]. split; [exact F22|].
         split; [exact V184|]. split; [exact V152|].
         split; [apply VMf; [clear - Hmf0 C1; lia | clear - Hmfb; fold sp0 in Hmfb; lia
           | intros j Hj; split; lia | exact V144]|].
         split; [apply VMf; [clear - Hmf0 C1; lia | clear - Hmfb; fold sp0 in Hmfb; lia
           | intros j Hj; split; lia | exact V160]|].
         split; [apply VMf; [clear - Hmf0 C1; lia | clear - Hmfb; fold sp0 in Hmfb; lia
           | intros j Hj; split; lia | exact V168]|].
         split; [apply VMf; [clear - Hmf0 C1; lia | clear - Hmfb; fold sp0 in Hmfb; lia
           | intros j Hj; split; lia | exact V136]|].
         intros Hr0. destruct (proj2 HRES Hr0) as (Gn & Gt & Gd).
         destruct (IM.n_r0 inp Hr0) as [Hwok Hfit].
         unfold SlotModel.n_fits in Hfit. apply andb_true_iff in Hfit as [Hf12 Hf3].
         apply andb_true_iff in Hf12 as [Hf1 Hf2]. apply Z.ltb_lt in Hf1, Hf2, Hf3.
         pose proof (IM.tk_len inp) as HTL.
         unfold SlotModel.n_ln in Hf1. unfold SlotModel.n_ld in Hf3.
         pose proof (req_size_pos (Z.max (SlotModel.t_cap_name inp) 1) ltac:(lia)) as Rq1.
         pose proof (req_size_pos (Z.max (SlotModel.t_cap_tok inp) 1) ltac:(lia)) as Rq2.
         pose proof (req_size_pos (Z.max (SlotModel.t_cap_disp inp) 1) ltac:(lia)) as Rq3.
         rewrite (IM.NM_eq inp Hwok) in Gn, Gt, Gd.
         rewrite (IM.DP_eq inp Hwok) in Gd.
         unfold bn_TK in Gt. rewrite IM.tk_eq in Gt. change (SlotModel.tok_go false (SlotModel.n_EXP_NM inp)) with (SlotModel.n_TK inp) in Gt.
         unfold bytes_at8. rewrite !map_app. cbn [map]. change (bv_unsigned (RcIdentModel.zb 0)) with 0.
         split; [|split].
         ++ apply KZ; [lia | clear - Hnmce Rq1; lia | rewrite length_app, length_map; cbn [length]; fold inp; lia | exact Gn].
         ++ apply KZ; [lia | clear - Htkce Rq2; lia | rewrite length_app, length_map; cbn [length]; fold inp; lia | exact Gt].
         ++ apply KZ; [lia | clear - Hdpce Rq3; lia | rewrite length_app, length_map; cbn [length]; fold inp; lia | exact Gd].
Qed.

(* seg_I of LLVMFuzzerTestOneInput_inv.v: from inv_H_end at 0x81878 to inv_I_end at 0x81974. *)
Theorem seg_I_holds : seg_I B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
intros g pos mf W2 c2 H. eapply SRr_bind; [exact (I_head g pos mf W2 c2 H)|].
intros W3 c3 _ HM1. exact (I_tail g pos mf W3 c3 HM1).
Qed.

End c.
End b.
End a.
