(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0l ACej ACeh ACem ACek ACei ACep.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCeo.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACes ACew ACex ACer ACfm ACf5 ACf9 ACf7.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Set Hyps Limit 8. Set Printing Depth 14. Set Printing Width 250.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Variable FP : list (Z * Z).
Variable POST : rtcx -> world tfibsegs -> config -> Prop.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis FP0 : FP = [].
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy A_asan_memcpy.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Lemma rt_lor_shl : forall a b k, 0 <= k -> 0 <= a -> 0 <= b < 2 ^ k -> Z.lor (a * 2 ^ k) b = a * 2 ^ k + b.
Proof.
intros a b k Hk Ha Hb.
assert (Hd : Z.land (a * 2 ^ k) b = 0).
{ apply Z.bits_inj_0. intros i. rewrite Z.land_spec. destruct (Z_lt_le_dec i k) as [Hi|Hi].
  - destruct (Z_lt_le_dec i 0) as [Hn|Hn]; [rewrite Z.testbit_neg_r by exact Hn; reflexivity|].
    rewrite <- Z.shiftl_mul_pow2 by exact Hk. rewrite Z.shiftl_spec_low by exact Hi. reflexivity.
  - rewrite <- (Z.mod_small b (2 ^ k)) by exact Hb. rewrite Z.mod_pow2_bits_high by lia. apply Bool.andb_false_r. }
rewrite <- (Z.lxor_lor _ _ Hd). rewrite <- (Z.add_nocarry_lxor _ _ Hd). reflexivity.
Qed.
Lemma rt_lor_mod : forall x y k, 0 <= k -> Z.lor x y mod 2 ^ k = Z.lor (x mod 2 ^ k) (y mod 2 ^ k).
Proof.
intros x y k Hk. apply Z.bits_inj'. intros i Hi. rewrite (Z.lor_spec (x mod 2 ^ k)).
destruct (Z_lt_le_dec i k) as [Hl|Hl].
- rewrite !Z.mod_pow2_bits_low by exact Hl. apply Z.lor_spec.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma rt_zcanon_mod : forall z k, 0 <= k <= 64 -> zcanon z mod 2 ^ k = z mod 2 ^ k.
Proof.
intros z k Hk. unfold zcanon, M64. apply Z.bits_inj'. intros i Hi.
destruct (Z_lt_le_dec i k) as [Hl|Hl].
- rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma rt_U_half : forall E x0 x1 b0 b1, ew E x0 = Z_to_bv 64 b0 -> ew E x1 = Z_to_bv 64 b1 -> 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff x1 0)) (SLit 8)) (SExt false 8 (SOff x0 0))) = b0 + 256 * b1.
Proof.
intros E x0 x1 b0 b1 H0 H1 R0 R1.
rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_zext, U_SLit.
rewrite (U_atom E x0 b0 H0) by lia. rewrite (U_atom E x1 b1 H1) by lia.
change (2 ^ Z.of_N 8) with 256. rewrite (Z.mod_small b0 256), (Z.mod_small b1 256) by lia.
change (Z.land (zcanon 8) 63) with 8.
rewrite Z.shiftl_mul_pow2 by lia.
rewrite (zcanon_id (b1 * 2 ^ 8)) by (unfold M64; lia).
rewrite (rt_lor_shl b1 b0 8) by lia.
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma rt_U_word : forall E x0 x1 x2 x3 b0 b1 b2 b3,
  ew E x0 = Z_to_bv 64 b0 -> ew E x1 = Z_to_bv 64 b1 -> ew E x2 = Z_to_bv 64 b2 -> ew E x3 = Z_to_bv 64 b3 ->
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SExt true 8 (SOff x3 0)) (SLit 24)) (SAlu ALU_SLL (SExt false 8 (SOff x2 0)) (SLit 16)))
                   (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff x1 0)) (SLit 8)) (SExt false 8 (SOff x0 0)))) mod 2 ^ 32
  = b0 + 256 * b1 + 65536 * b2 + 16777216 * b3.
Proof.
intros E x0 x1 x2 x3 b0 b1 b2 b3 H0 H1 H2 H3 R0 R1 R2 R3.
rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SExt, !U_SLit. cbv beta iota.
rewrite (U_atom E x0 b0 H0), (U_atom E x1 b1 H1), (U_atom E x2 b2 H2), (U_atom E x3 b3 H3) by lia.
change (2 ^ Z.of_N 8) with 256. rewrite (Z.mod_small b0 256), (Z.mod_small b1 256), (Z.mod_small b2 256), (Z.mod_small b3 256) by lia.
change (Z.land (zcanon 24) 63) with 24. change (Z.land (zcanon 16) 63) with 16. change (Z.land (zcanon 8) 63) with 8.
rewrite (zcanon_id b0), (zcanon_id b1), (zcanon_id b2) by (unfold M64; lia).
rewrite rt_zcanon_mod by lia. rewrite !rt_lor_mod by lia. rewrite !rt_zcanon_mod by lia. rewrite !rt_lor_mod by lia.
rewrite !rt_zcanon_mod by lia.
rewrite !Z.shiftl_mul_pow2 by lia.
assert (Hs : (zcanon (bv_swrap 8 b3) * 2 ^ 24) mod 2 ^ 32 = b3 * 2 ^ 24).
{ change (2 ^ 32) with (2 ^ 8 * 2 ^ 24). rewrite Z.mul_mod_distr_r by lia. f_equal.
  rewrite rt_zcanon_mod by lia. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  change (256 `div` 2) with 128. change (2 ^ 8) with 256.
  destruct (Z_lt_le_dec b3 128) as [Hl|Hl].
  - rewrite (Z.mod_small (b3 + 128) 256) by lia. replace (b3 + 128 - 128) with b3 by lia. apply Z.mod_small. lia.
  - assert (Hm : (b3 + 128) mod 256 = b3 - 128) by (first [apply (Z.mod_unique _ _ 1) | symmetry; apply (Z.mod_unique _ _ 1)]; lia).
    rewrite Hm. first [apply (Z.mod_unique _ _ (-1)) | symmetry; apply (Z.mod_unique _ _ (-1))]; lia. }
rewrite Hs.
rewrite (Z.mod_small (b2 * 2 ^ 16)), (Z.mod_small (b1 * 2 ^ 8)), (Z.mod_small b0) by lia.
rewrite (rt_lor_shl b1 b0 8) by lia.
replace (b3 * 2 ^ 24) with ((b3 * 2 ^ 8) * 2 ^ 16) by lia.
rewrite <- !(Z.shiftl_mul_pow2 _ 16) by lia. rewrite <- Z.shiftl_lor. rewrite !Z.shiftl_mul_pow2 by lia.
rewrite (rt_lor_shl b3 b2 8) by lia.
rewrite (rt_lor_shl (b3 * 2 ^ 8 + b2) (b1 * 2 ^ 8 + b0) 16) by lia.
lia.
Qed.
Lemma rt_chunk1_of_val : forall E (m : word -> option byte) base off k v,
  val_mem tfibsegs m (base + off) 1 v -> 0 <= v < 256 -> ew E k = Z_to_bv 64 v ->
  YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal 1 (SOff k 0))).
Proof.
intros E m base off k v Hv Hr Hk i Hi. cbn [YP09.c_len YP09.c_val YP09.cv_len Z.of_N] in Hi.
assert (i = 0) as -> by lia.
exists (Z_to_bv 8 (YO0f.le_byte v 1 0)). split.
- cbn [YP09.c_off YP09.c_val YP09.cbyte]. rewrite sv_denot_SOff0, Hk. f_equal. unfold YP09.byte_of_word.
  rewrite unsigned_lit_small by lia. f_equal. unfold YO0f.le_byte. change (Z.of_nat 1) with 1. cbn [Z.of_nat]. rewrite ?Z.mul_0_r, ?Z.shiftr_0_r.
  change (2 ^ (8 * 1)) with 256. rewrite !(Z.mod_small v 256) by lia. reflexivity.
- cbn [YP09.c_off]. rewrite Z.add_0_r. pose proof (Hv 0%nat ltac:(lia)) as H0. change (Z.of_nat 0) with 0 in H0. rewrite Z.add_0_r in H0. exact H0.
Qed.
Ltac in_region HS R E10x AG :=
  lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
  let HS3 := fresh "HS3" in
  pose proof (ast_ok_add_region tfibsegs Ev ssv msv R HS eq_refl) as HS3;
  specialize (HS3 ltac:(
    unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
    ewpeel; rewrite E10x, unsigned_lit_small by lia;
    split; [lia|]; split; [lia|]; split; [intros oo Hoo; lia|];
    repeat (apply Forall_cons; [ eapply rt_chunk1_of_val; [ apply val_mem1_of_aview; eassumption | eassumption | ewpeel; eassumption ] | ]); apply Forall_nil));
  specialize (HS3 ltac:(
    lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob;
    repeat split; zone_lia));
  clear HS; rename HS3 into HS; norm_ss HS end.
Ltac rd_run HS HJ AG fpos F EFA E10x E32x Hpin3 Hrq :=
  reshok HS;
  lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ =>
  aj_run_tok tfibtbl_lib_ok HS HJ SH RTBspan;
  try (lazymatch goal with |- range_addressable _ _ _ _ => obl_pay HJ E10x E32x Hpin3 Hrq end);
  try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => awrRT AG fpos F EFA end) end.
Ltac rd_run_to HS HJ AG fpos F EFA E10x E32x Hpin3 Hrq stop :=
  reshok HS;
  lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ =>
  aj_run_to_tok tfibtbl_lib_ok HS HJ SH RTBspan stop;
  try (lazymatch goal with |- range_addressable _ _ _ _ => obl_pay HJ E10x E32x Hpin3 Hrq end);
  try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => awrRT AG fpos F EFA end) end.
Ltac tail_run HS HJ AG fpos F EFA :=
  reshok HS;
  lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ =>
  aj_run_to_tok tfibtbl_lib_ok HS HJ SH RTBspan (A_LLVMF + 856);
  try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => awrRT AG fpos F EFA end) end.
Ltac br_go HS Hc E11x :=
  reshok HS;
  lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok tfibtbl_lib_ok HS SH RTBspan end;
  lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end;
  lazymatch type of E11x with _ = Z_to_bv 64 ?nv =>
  hc_bool Hc ltac:(fun H => hc_atom H 11%nat nv E11x ltac:(lia)); hc_prop Hc end.
Lemma rt_byte_low : forall (x y : word) (w : N) i, Z.of_N w <= 8 -> 0 <= i < Z.of_N w ->
  bv_unsigned x mod 2 ^ (8 * Z.of_N w) = bv_unsigned y mod 2 ^ (8 * Z.of_N w) ->
  YP09.byte_of_word x i = YP09.byte_of_word y i.
Proof.
intros x y w i Hw Hi Hxy. unfold YP09.byte_of_word. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with (2 ^ 8).
apply Z.bits_inj'. intros j Hj. destruct (Z_lt_le_dec j 8) as [Hl|Hl].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
  rewrite <- (Z.mod_pow2_bits_low (bv_unsigned x) (8 * Z.of_N w)) by lia.
  rewrite <- (Z.mod_pow2_bits_low (bv_unsigned y) (8 * Z.of_N w)) by lia. rewrite Hxy. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma rt_chunk_ok_low : forall E m base off (w : N) e e', Z.of_N w <= 8 ->
  U E e' mod 2 ^ (8 * Z.of_N w) = U E e mod 2 ^ (8 * Z.of_N w) ->
  YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal w e)) -> YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal w e')).
Proof.
intros E m base off w e e' Hw He H i Hi. cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len] in *.
destruct (H i Hi) as (b & Hb1 & Hb2). exists b. cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb1, Hb2 |- *. split; [|exact Hb2].
rewrite <- Hb1. f_equal. apply (rt_byte_low _ _ w); [exact Hw | lia | exact He].
Qed.
Lemma rt_region_ok_rechunk_low : forall E m r j off (w : N) e e',
  region_ok tfibsegs E m r -> nth_error (YP09.r_chunks r) j = Some (YP09.mkChunk off (CVal w e)) -> Z.of_N w <= 8 ->
  U E e' mod 2 ^ (8 * Z.of_N w) = U E e mod 2 ^ (8 * Z.of_N w) ->
  region_ok tfibsegs E m (YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) (YP09.r_wlo r) (YP09.r_whi r)
    (list_upd (YP09.r_chunks r) j (YP09.mkChunk off (CVal w e')))).
Proof.
intros E m r j off w e e' (H1 & H2 & H3 & H4) Hj Hw He. unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
apply Forall_list_upd; [exact H4|]. apply (rt_chunk_ok_low E m _ off w e e' Hw He).
exact (proj1 (Forall_forall _ _) H4 _ (nth_error_In _ _ Hj)).
Qed.
Lemma rt_ad_split : forall E x pre r post, all_disjoint E x (pre ++ r :: post) -> extent_disjoint E x r /\ all_disjoint E x (pre ++ post).
Proof. intros E x pre r post. induction pre as [|y pre IH]; cbn [app all_disjoint]; [tauto|]. intros [Hy Hr]. destruct (IH Hr) as [A B']. tauto. Qed.
Lemma rt_ed_sym : forall E a b, extent_disjoint E a b -> extent_disjoint E b a.
Proof. unfold extent_disjoint. intros E a b H. lia. Qed.
Lemma rt_pd_move : forall E pre r post, pairwise_disjoint E (pre ++ r :: post) -> all_disjoint E r (pre ++ post) /\ pairwise_disjoint E (pre ++ post).
Proof.
intros E pre r post. induction pre as [|x pre IH]; cbn [app pairwise_disjoint all_disjoint]; [tauto|].
intros [Hx Hrest]. destruct (IH Hrest) as [Hr Hp]. destruct (rt_ad_split E x pre r post Hx) as [Hxr Hxa].
split; [split; [apply rt_ed_sym; exact Hxr | exact Hr] | split; [exact Hxa | exact Hp]].
Qed.
Lemma rt_wf_move : forall pre r post, regions_wf (pre ++ r :: post) = true -> regions_wf (r :: pre ++ post) = true.
Proof.
intros pre r post. induction pre as [|x pre IH]; cbn [app regions_wf]; [tauto|]. intros H.
apply andb_prop in H as [Hx H]. specialize (IH H). cbn [regions_wf] in IH. apply andb_prop in IH as [Hr Hp].
rewrite Hr, Hx, Hp. reflexivity.
Qed.
Lemma rt_forall_move : forall {A} (P : A -> Prop) pre r post, Forall P (pre ++ r :: post) -> Forall P (r :: pre ++ post).
Proof.
intros A P pre r post H. rewrite Forall_forall in *. intros x Hx. apply H.
destruct Hx as [<- | Hx]; [apply in_or_app; right; left; reflexivity|].
apply in_app_or in Hx as [Hx|Hx]; apply in_or_app; [left; exact Hx | right; right; exact Hx].
Qed.
Lemma rt_st_ok_move : forall E ss ms pre r post,
  st_ok tfibsegs E ss ms -> ss_mem ss = pre ++ r :: post ->
  st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) (r :: pre ++ post) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms pre r post (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (W & O & D) & H9) Hm.
rewrite Hm in W, O, D.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9].
split; [exact (rt_wf_move pre r post W)|]. split; [exact (rt_forall_move _ pre r post O)|].
destruct (rt_pd_move E pre r post D) as [A B']. split; [exact A | exact B'].
Qed.
Ltac rechunk_low HS i j e' tac :=
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let r := eval vm_compute in (nth i rs got_region) in
  lazymatch (eval vm_compute in (nth_error (YP09.r_chunks r) j)) with Some (YP09.mkChunk ?off (CVal ?w ?e)) =>
  let r' := eval vm_compute in (YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) (YP09.r_wlo r) (YP09.r_whi r)
    (list_upd (YP09.r_chunks r) j (YP09.mkChunk off (CVal w e')))) in
  let HS3 := fresh "HS3" in
  pose proof (ast_ok_set_region tfibsegs Ex ssx msx i r r' HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
    (rt_region_ok_rechunk_low Ex _ r j off w e e' (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(vm_compute; reflexivity) ltac:(cbn; lia) ltac:(tac))) as HS3;
  clear HS; rename HS3 into HS; norm_ss HS end end.
Ltac rechunk_low_at HS n off e' tac :=
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let i := idx_of_base_off rs n off in let i := eval vm_compute in i in
  let r := eval vm_compute in (nth i rs got_region) in
  let cs := eval vm_compute in (YP09.r_chunks r) in
  let j := idx_of_chunk cs off in let j := eval vm_compute in j in
  rechunk_low HS i j e' tac end.
Ltac move_region HS i :=
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let pre := eval vm_compute in (firstn i rs) in
  let r := eval vm_compute in (nth i rs got_region) in
  let post := eval vm_compute in (skipn (S i) rs) in
  let HS3 := fresh "HS3" in
  pose proof (rt_st_ok_move Ex ssx msx pre r post HS ltac:(vm_compute; reflexivity)) as HS3;
  clear HS; rename HS3 into HS; norm_ss HS end.
Ltac fin_field HS off a pw hi v Hv Ea Rv :=
  lazymatch type of HS with st_ok _ ?Ev ?ssx _ =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let i := idx_of_base_off rs 75%nat off in let i := eval vm_compute in i in
  let cs := eval vm_compute in (YP09.r_chunks (nth i rs got_region)) in
  let j := idx_of_chunk cs off in let j := eval vm_compute in j in
  lazymatch (eval vm_compute in (nth_error cs j)) with Some (YP09.mkChunk _ (CVal _ ?e)) =>
  remember (U Ev e mod 2 ^ pw) as v eqn:Hv;
  assert (Rv : 0 <= v < 2 ^ pw) by (rewrite Hv; apply Z.mod_pos_bound; lia);
  add_atom_win HS a (Z_to_bv 64 v) Ea;
  rechunk_low_at HS 75%nat off (SOff a 0) ltac:(
    cbn [Z.of_N]; change (8 * 4) with 32; change (8 * 2) with 16;
    rewrite (U_atom _ a v Ea) by lia; unfold U; rewrite denot_havoc_win by (vm_compute; reflexivity);
    rewrite Hv; unfold U; rewrite Z.mod_mod by lia; reflexivity);
  add_fact HS a 0 hi Ea ltac:(lia) end end.
Ltac pin_reg HS rr a v Hv Ea :=
  lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict ?Hh ?ms) =>
  let e := eval vm_compute in (sr_get (ss_regs ssx) rr) in
  remember (U Ev e) as v eqn:Hv;
  let Q := fresh "Q" in
  assert (Q : getr (ms_regs ms) rr = sv_denot Ev e) by exact (st_ok_restrict_reg tfibsegs Hh Ev ssx ms rr HS);
  add_atom_win HS a (Z_to_bv 64 v) Ea;
  lazymatch type of HS with st_ok _ ?Ev2 ?ssx2 ?msv2 =>
  let HS3 := fresh "HS3" in
  pose proof (st_ok_pin_rege Ev2 ssx2 msv2 rr (SOff a 0) HS ltac:(intros X; discriminate X)
    ltac:(rewrite sv_denot_SOff0, Ea; cbn [ms_regs restrict mkst]; rewrite Q, Hv; symmetry; apply denot_lit_U)) as HS3;
  clear HS; rename HS3 into HS; norm_ss HS end; clear Q;
  first [ rewrite U_SLit in Hv; unfold zcanon, M64 in Hv; rewrite Z.mod_small in Hv by lia
        | match goal with E11x : ew _ 11 = Z_to_bv 64 ?nv |- _ => rewrite (U_atom Ev 11 nv ltac:(ewpeel; exact E11x)) in Hv by lia end
        | idtac ] end.
Ltac fin_run HS HJ AG fpos F EFA :=
  reshok HS;
  lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ =>
  aj_run_tok tfibtbl_lib_ok HS HJ SH RTBspan;
  try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => awrRT AG fpos F EFA end) end.
Ltac fin_join HS :=
  lazymatch type of HS with st_ok _ _ ?ssx _ =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let i := eval vm_compute in (idx_of (fun r => match YP09.r_base r with Some 75%nat => Z.eqb (YP09.r_lo r) 32 | _ => false end) rs) in
  move_region HS i end;
  lazymatch type of HS with st_ok _ _ ?ssx _ =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let i := idx_of_base rs 70%nat in let i := eval vm_compute in i in
  move_region HS i end;
  ra_join_win HS ss_Bend 160%nat rt_Bend_deads_bv ltac:(idtac).
Ltac obj_cells HS E70x E10x E11x E193x sptac Vp Vn Vc :=
  lazymatch type of E70x with _ = Z_to_bv 64 ?s1 =>
  lazymatch type of E10x with _ = Z_to_bv 64 ?pv =>
  lazymatch type of E11x with _ = Z_to_bv 64 ?nv =>
  lazymatch type of E193x with _ = Z_to_bv 64 ?cv =>
  lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
    let rs := eval vm_compute in (ss_mem ssx) in
    let i := idx_of_base rs 70%nat in let i := eval vm_compute in i in
    let rg := eval vm_compute in (nth i rs got_region) in
    let HR70 := fresh "HR70" in let B70 := fresh "B70" in
    pose proof (st_ok_region_nth Ex ssx (restrict _ msX) i rg HS ltac:(vm_compute; reflexivity)) as HR70; cbn [ms_mem restrict] in HR70;
    assert (B70 : bv_unsigned (ew Ex 70) = s1) by (rewrite E70x; apply unsigned_lit_small; sptac);
    pose proof (field_of_region _ _ 70%nat s1 _ _ _ _ _ 8 8 (SOff 10 0) pv HR70 B70 ltac:(cbn; tauto) ltac:(rewrite sv_denot_SOff0; exact E10x) ltac:(cbn; lia) ltac:(cbn; clear; lia)) as Vp;
    pose proof (field_of_region _ _ 70%nat s1 _ _ _ _ _ 16 8 (SOff 11 0) nv HR70 B70 ltac:(cbn; tauto) ltac:(rewrite sv_denot_SOff0; exact E11x) ltac:(cbn; lia) ltac:(cbn; clear; lia)) as Vn;
    pose proof (field_of_region _ _ 70%nat s1 _ _ _ _ _ 24 8 (SOff 193 0) cv HR70 B70 ltac:(cbn; tauto) ltac:(rewrite sv_denot_SOff0; exact E193x) ltac:(cbn; lia) ltac:(cbn; clear; lia)) as Vc;
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vp, Vn, Vc; clear HR70 B70;
    replace (s1 + 16) with (s1 + 8 + 8) in Vn by (clear; lia); replace (s1 + 24) with (s1 + 8 + 16) in Vc by (clear; lia)
  end end end end end.
Lemma rt_Bend_aux : rt_from B MT FP POST ss_C (INV_C B MT) -> rt_from B MT FP POST ss_D (INV_D B MT FP) -> rt_from B MT FP POST ss_Bend (INV_Bend B MT).
Proof.
intros RC RD. rt_prelude.
pose proof HINV as (Hk0 & Hacc & Eab3 & attr & gen & w16 & h16 & ngp & cur & r & HGC & Hcur14 & E193).
pose proof HGC as (E185 & E186 & E187 & E188 & E189 & E190 & Rattr & Rgen & Rw & Rh & Rngp & Rcur & Rr & Hr14 & Vp & Vn & Vc & Hprov & Hwhy).
cbn [c_n c_sp1 c_p] in Rcur, Hr14, Vp, Vn, Vc, Hwhy, Hprov.
relowRT HS AG E10 E11 E32 E10n E11n E32n.
assert (Rp : 0 <= p < 2 ^ 64).
{ destruct Hpn as [[Hn0 HpE] | [Hnr Hin]].
  - rewrite HpE. unfold A_EMPTY. clear; lia.
  - assert (Hp3 : In (p, n) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hin).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n (proj1 HJ3) Hp3) as (_ & Hp4096 & Hpceil & _).
    pose proof (req_size_pos n ltac:(clear - Hnr; lia)) as [_ Hrq]. clear - Hp4096 Hpceil Hrq C1 Hnr. lia. }
reshok HS.
srr_branch_tok tfibtbl_lib_ok HS SHOK RTBspan.
- lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
  rewrite branch_ne_U, U_and_lit, attr_test, U_lit in Hc by (clear; lia).
  rewrite sv_denot_SOff0, E185, unsigned_lit_small in Hc by (clear - Rattr; lia).
  cbn [negb] in Hc. apply (proj1 (negb_true_iff _)) in Hc. apply (proj1 (Z.eqb_neq _ _)) in Hc.
  reshok HS. aj_run_to_tok tfibtbl_lib_ok HS HJ3 SHOK RTBspan (A_LLVMF + 964).
  1: awrRT AG fpos F EFA3.
  clear_frames. clear Vp Vn Vc.
  rebaseE HS AG HEv. clear HEv. relowRT HS AG E10 E11 E32 E10n E11n E32n.
  obj_cells HS E70 E10n E11n E193 ltac:(clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1; lia) Vp Vn Vc.
  rreg HS (24%bv : bv 5) R24.
  add_atom_win HS 191%nat (Z_to_bv 64 0) E191. add_atom_win HS 192%nat (Z_to_bv 64 r) E192.
  ws_pin HS (24%bv : bv 5) (SOff 192 0) R24 ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E192; symmetry; ewpeel; exact E190).
  rechunk_at HS 75%nat 32 (SOff 191 0) ltac:(rewrite sv_denot_SOff0; ewpeel; rewrite E191; reflexivity).
  ra_join_win HS ss_D 400%nat rt_C_deads_bv ltac:(idtac).
  rebaseE HS AG HEv. clear HEv. rt_hand RD HS.
  split; [clear - Hk0; lia|]. split; [macc|].
  exists attr, gen, w16, h16, ngp, cur, r, 0.
  split; [| split; [exact E191 | split; [clear; lia | left; split; [exact Hc | split; [reflexivity | split; [cbn [c_ly c_S]; exact Eab3 | exact Hcur14]]]]]].
  unfold rt_gc; cbn [c_n c_sp1 c_p].
  repeat match goal with |- _ /\ _ => split end; first [ assumption | clear - Rattr Rgen Rw Rh Rngp Rcur Rr; lia ].
- lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
  rewrite branch_ne_U, U_and_lit, attr_test, U_lit in Hc by (clear; lia).
  rewrite sv_denot_SOff0, E185, unsigned_lit_small in Hc by (clear - Rattr; lia).
  cbn [negb] in Hc. apply (proj1 (negb_false_iff _)) in Hc. apply (proj1 (Z.eqb_eq _ _)) in Hc.
  reshok HS. aj_run_to_tok tfibtbl_lib_ok HS HJ3 SHOK RTBspan (A_LLVMF + 888).
  1: awrRT AG fpos F EFA3.
  clear_frames. clear Vp Vn Vc.
  rebaseE HS AG HEv. clear HEv. relowRT HS AG E10 E11 E32 E10n E11n E32n.
  obj_cells HS E70 E10n E11n E193 ltac:(clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1; lia) Vp Vn Vc.
  ra_join_win HS ss_C 400%nat rt_C0_deads_bv ltac:(idtac).
  rebaseE HS AG HEv. clear HEv. rt_hand RC HS.
  split; [exact Hk0|]. split; [macc|]. split; [cbn [c_ly c_S]; exact Eab3|].
  exists attr, gen, w16, h16, ngp, cur, r.
  split; [|split; [exact Hc | split; [exact Hcur14 | exact E193]]].
  unfold rt_gc; cbn [c_n c_sp1 c_p].
  repeat match goal with |- _ /\ _ => split end; first [ assumption | clear - Rattr Rgen Rw Rh Rngp Rcur Rr; lia ].
Qed.
Ltac fin_tail HS HJ AG fpos F EFA E10 E11 E32 E10n E11n E32n E70 sptac hook
  v185 Hv185 E185 R185 v186 Hv186 E186 R186 v187 Hv187 E187 R187 v188 Hv188 E188 R188 v189 Hv189 E189 R189
  cur Hcur E193 r Hr E190 Vp Vn Vc :=
  let HEv := fresh "HEv" in rebaseE HS AG HEv; clear HEv; relowRT HS AG E10 E11 E32 E10n E11n E32n;
  fin_field HS 48 185%nat 32 (2 ^ 32 - 1) v185 Hv185 E185 R185;
  fin_field HS 52 186%nat 32 (2 ^ 32 - 1) v186 Hv186 E186 R186;
  fin_field HS 56 187%nat 16 (2 ^ 16 - 1) v187 Hv187 E187 R187;
  fin_field HS 58 188%nat 16 (2 ^ 16 - 1) v188 Hv188 E188 R188;
  fin_field HS 60 189%nat 16 (2 ^ 16 - 1) v189 Hv189 E189 R189;
  hook;
  pin_reg HS (25%bv : bv 5) 193%nat cur Hcur E193;
  fin_run HS HJ AG fpos F EFA; clear_frames;
  let HEv2 := fresh "HEv" in rebaseE HS AG HEv2; clear HEv2; relowRT HS AG E10 E11 E32 E10n E11n E32n;
  pin_reg HS (24%bv : bv 5) 190%nat r Hr E190;
  fin_join HS;
  let HEv3 := fresh "HEv" in rebaseE HS AG HEv3; clear HEv3; relowRT HS AG E10 E11 E32 E10n E11n E32n;
  obj_cells HS E70 E10n E11n E193 sptac Vp Vn Vc.
Ltac fin_close :=
  split; [|split; [intros; lia | assumption]];
  unfold rt_gc; cbn [c_n c_sp1 c_p];
  repeat match goal with |- _ /\ _ => split end;
  try first [ assumption | lia | (intros; exfalso; lia) | (intros; left; lia) ].
Ltac hdr_conv Hv185 Hv186 Hv187 Hv188 Hv189 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 :=
  rewrite (rt_U_half _ 200 201 c0 c1) in Hv187 by first [lia | ewpeel; eassumption];
  rewrite (rt_U_half _ 202 203 c2 c3) in Hv188 by first [lia | ewpeel; eassumption];
  rewrite (rt_U_half _ 212 213 c12 c13) in Hv189 by first [lia | ewpeel; eassumption];
  rewrite (rt_U_word _ 204 205 206 207 c4 c5 c6 c7) in Hv185 by first [lia | ewpeel; eassumption];
  rewrite (rt_U_word _ 208 209 210 211 c8 c9 c10 c11) in Hv186 by first [lia | ewpeel; eassumption];
  rewrite Z.mod_small in Hv187, Hv188, Hv189 by lia.
Ltac in_bytes HJ cx LAWS HAR Hpin Hpin3 Hrq FP0 i0 n0 :=
  let HJc := fresh "HJc" in pose proof HJ as HJc; rewrite FP0 in HJc;
  let rec go j k :=
    lazymatch k with
    | O => idtac
    | S ?k' =>
      let bj := fresh "b" in let PBj := fresh "PB" in let Aj := fresh "A" in let Rj := fresh "R" in
      destruct (PB_at_now _ _ cx _ _ _ _ _ _ _ j LAWS HAR HJc Hpin Hpin3 Hrq ltac:(cbn [c_n]; lia)) as (bj & PBj & Aj);
      cbn [c_p] in Aj; pose proof (proj1 PBj) as Rj;
      let j' := eval vm_compute in (j + 1) in go j' k'
    end in
  go i0 n0; clear HJc.
Ltac rb HS AG E10 E11 E32 E10n E11n E32n :=
  let HEv := fresh "HEv" in rebaseE HS AG HEv; clear HEv; relowRT HS AG E10 E11 E32 E10n E11n E32n.
Lemma rt_B_aux : rt_from B MT FP POST ss_C (INV_C B MT) -> rt_from B MT FP POST ss_D (INV_D B MT FP) -> rt_from B MT FP POST ss_B (INV_0 B MT 0).
Proof.
intros RC RD. pose proof (rt_Bend_aux RC RD) as RBend. clear RC RD. rt_prelude.
pose proof HINV as (Hk0 & Hacc & Eab3).
relowRT HS AG E10 E11 E32 E10n E11n E32n.
assert (HpR : 4096 <= p /\ p + n <= alloc_ceiling).
{ destruct Hpn as [[Hn0 HpE] | [Hnr Hin]].
  - rewrite HpE, Hn0. unfold A_EMPTY. clear - C1. lia.
  - assert (Hp3 : In (p, n) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hin).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n (proj1 HJ3) Hp3) as (_ & Hp4096 & Hpceil & _).
    pose proof (req_size_pos n ltac:(clear - Hnr; lia)) as [_ Hrq]. clear - Hp4096 Hpceil Hrq. lia. }
add_fact HS 10%nat 4096 140737479966720 E10n ltac:(clear - HpR C1 Hn26; lia).
reshok HS.
aj_run_tok tfibtbl_lib_ok HS HJ3 SHOK RTBspan.
1: awrRT AG fpos F EFA3.
br_go HS Hc1 E11n.
- tail_run HS HJ3 AG fpos F EFA3.
  fin_tail HS HJ3 AG fpos F EFA3 E10 E11 E32 E10n E11n E32n E70 ltac:(clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1; lia) idtac
    v185 Hv185 E185 R185 v186 Hv186 E186 R186 v187 Hv187 E187 R187 v188 Hv188 E188 R188 v189 Hv189 E189 R189 cur Hcur E193 r Hr E190 Vp Vn Vc.
  rt_hand RBend HS. split; [exact Hk0|]. split; [macc|]. split; [exact Eab3|].
  exists v185, v186, v187, v188, v189, cur, r. fin_close.
- assert (Hpin : In (p, n) (ablocks B ly S)) by (destruct Hpn as [[Hn0 _] | [_ Hin]]; [exfalso; clear - Hn0 Hc1; lia | exact Hin]).
  assert (Hpin3 : In (p, n) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hpin).
  assert (Hrq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); [exfalso; clear - Hc1 e; lia | reflexivity]).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n (proj1 HJ3) Hpin3) as (_ & _ & _ & HinApp & _). rewrite Hrq in HinApp.
  pose proof (blk_off_img B _ _ _ _ _ p n (proj1 HJ3) Hpin3) as HoffImg. rewrite Hrq in HoffImg.
  pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 _ _ _ p n 2 fpos (proj1 HJ3) Hpin3 Hfin3) as HpF.
  unfold zdisjoint in HpF. cbn [fst snd] in HpF. change (fs_frame_bytes 2) with 256 in HpF. rewrite EFA3 in HpF. fold F in HpF. rewrite Hrq in HpF.
  in_bytes HJ3 (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) LAWS HAR Hpin Hpin3 Hrq FP0 0 2%nat.
  add_atom_win HS 200%nat (Z_to_bv 64 b) E200.
  add_atom_win HS 201%nat (Z_to_bv 64 b0) E201.
  in_region HS (YP09.mkRegion (Some 10%nat) 0 2 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 200 0)); YP09.mkChunk 1 (CVal 1 (SOff 201 0))]) E10n AG.
  rd_run HS HJ3 AG fpos F EFA3 E10n E32n Hpin3 Hrq. rb HS AG E10 E11 E32 E10n E11n E32n.
  br_go HS Hc2 E11n.
  + tail_run HS HJ3 AG fpos F EFA3.
    fin_tail HS HJ3 AG fpos F EFA3 E10 E11 E32 E10n E11n E32n E70 ltac:(clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1; lia) idtac
      v185 Hv185 E185 R185 v186 Hv186 E186 R186 v187 Hv187 E187 R187 v188 Hv188 E188 R188 v189 Hv189 E189 R189 cur Hcur E193 r Hr E190 Vp Vn Vc.
    rt_hand RBend HS. split; [exact Hk0|]. split; [macc|]. split; [exact Eab3|].
    exists v185, v186, v187, v188, v189, cur, r. fin_close.
  + in_bytes HJ3 (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) LAWS HAR Hpin Hpin3 Hrq FP0 2 2%nat.
    add_atom_win HS 202%nat (Z_to_bv 64 b1) E202.
    add_atom_win HS 203%nat (Z_to_bv 64 b2) E203.
    in_region HS (YP09.mkRegion (Some 10%nat) 2 4 0 0 [YP09.mkChunk 2 (CVal 1 (SOff 202 0)); YP09.mkChunk 3 (CVal 1 (SOff 203 0))]) E10n AG.
    rd_run HS HJ3 AG fpos F EFA3 E10n E32n Hpin3 Hrq. rb HS AG E10 E11 E32 E10n E11n E32n.
    br_go HS Hc3 E11n.
    * tail_run HS HJ3 AG fpos F EFA3.
      fin_tail HS HJ3 AG fpos F EFA3 E10 E11 E32 E10n E11n E32n E70 ltac:(clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1; lia) idtac
        v185 Hv185 E185 R185 v186 Hv186 E186 R186 v187 Hv187 E187 R187 v188 Hv188 E188 R188 v189 Hv189 E189 R189 cur Hcur E193 r Hr E190 Vp Vn Vc.
      rt_hand RBend HS. split; [exact Hk0|]. split; [macc|]. split; [exact Eab3|].
      exists v185, v186, v187, v188, v189, cur, r. fin_close.
    * in_bytes HJ3 (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) LAWS HAR Hpin Hpin3 Hrq FP0 4 4%nat.
      add_atom_win HS 204%nat (Z_to_bv 64 b3) E204.
      add_atom_win HS 205%nat (Z_to_bv 64 b4) E205.
      add_atom_win HS 206%nat (Z_to_bv 64 b5) E206.
      add_atom_win HS 207%nat (Z_to_bv 64 b6) E207.
      in_region HS (YP09.mkRegion (Some 10%nat) 4 8 0 0 [YP09.mkChunk 4 (CVal 1 (SOff 204 0)); YP09.mkChunk 5 (CVal 1 (SOff 205 0)); YP09.mkChunk 6 (CVal 1 (SOff 206 0)); YP09.mkChunk 7 (CVal 1 (SOff 207 0))]) E10n AG.
      rd_run HS HJ3 AG fpos F EFA3 E10n E32n Hpin3 Hrq. rb HS AG E10 E11 E32 E10n E11n E32n.
      br_go HS Hc4 E11n.
      -- tail_run HS HJ3 AG fpos F EFA3.
         fin_tail HS HJ3 AG fpos F EFA3 E10 E11 E32 E10n E11n E32n E70 ltac:(clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1; lia) idtac
           v185 Hv185 E185 R185 v186 Hv186 E186 R186 v187 Hv187 E187 R187 v188 Hv188 E188 R188 v189 Hv189 E189 R189 cur Hcur E193 r Hr E190 Vp Vn Vc.
         rt_hand RBend HS. split; [exact Hk0|]. split; [macc|]. split; [exact Eab3|].
         exists v185, v186, v187, v188, v189, cur, r. fin_close.
      -- in_bytes HJ3 (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) LAWS HAR Hpin Hpin3 Hrq FP0 8 4%nat.
         add_atom_win HS 208%nat (Z_to_bv 64 b7) E208.
         add_atom_win HS 209%nat (Z_to_bv 64 b8) E209.
         add_atom_win HS 210%nat (Z_to_bv 64 b9) E210.
         add_atom_win HS 211%nat (Z_to_bv 64 b10) E211.
         in_region HS (YP09.mkRegion (Some 10%nat) 8 12 0 0 [YP09.mkChunk 8 (CVal 1 (SOff 208 0)); YP09.mkChunk 9 (CVal 1 (SOff 209 0)); YP09.mkChunk 10 (CVal 1 (SOff 210 0)); YP09.mkChunk 11 (CVal 1 (SOff 211 0))]) E10n AG.
         rd_run HS HJ3 AG fpos F EFA3 E10n E32n Hpin3 Hrq. rb HS AG E10 E11 E32 E10n E11n E32n.
         br_go HS Hc5 E11n.
         ++ in_bytes HJ3 (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) LAWS HAR Hpin Hpin3 Hrq FP0 12 2%nat.
            add_atom_win HS 212%nat (Z_to_bv 64 b11) E212.
            add_atom_win HS 213%nat (Z_to_bv 64 b12) E213.
            in_region HS (YP09.mkRegion (Some 10%nat) 12 14 0 0 [YP09.mkChunk 12 (CVal 1 (SOff 212 0)); YP09.mkChunk 13 (CVal 1 (SOff 213 0))]) E10n AG.
            rd_run_to HS HJ3 AG fpos F EFA3 E10n E32n Hpin3 Hrq (A_LLVMF + 856).
            fin_tail HS HJ3 AG fpos F EFA3 E10 E11 E32 E10n E11n E32n E70 ltac:(clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1; lia)
              ltac:(hdr_conv Hv185 Hv186 Hv187 Hv188 Hv189 b b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12)
              v185 Hv185 E185 R185 v186 Hv186 E186 R186 v187 Hv187 E187 R187 v188 Hv188 E188 R188 v189 Hv189 E189 R189 cur Hcur E193 r Hr E190 Vp Vn Vc.
            rt_hand RBend HS. split; [exact Hk0|]. split; [macc|]. split; [exact Eab3|].
            exists v185, v186, v187, v188, v189, cur, r. fin_close.
            all: intros _; exists b, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12.
            all: repeat match goal with |- _ /\ _ => split end; first [ assumption | lia | rewrite Z.mod_small by lia; lia ].
         ++ tail_run HS HJ3 AG fpos F EFA3.
            fin_tail HS HJ3 AG fpos F EFA3 E10 E11 E32 E10n E11n E32n E70 ltac:(clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1; lia) idtac
              v185 Hv185 E185 R185 v186 Hv186 E186 R186 v187 Hv187 E187 R187 v188 Hv188 E188 R188 v189 Hv189 E189 R189 cur Hcur E193 r Hr E190 Vp Vn Vc.
            rt_hand RBend HS. split; [exact Hk0|]. split; [macc|]. split; [exact Eab3|].
            exists v185, v186, v187, v188, v189, cur, r. fin_close.
Qed.
Lemma rt_B : rt_from B MT FP POST ss_C (INV_C B MT) -> rt_from B MT FP POST ss_D (INV_D B MT FP) -> rt_from B MT FP POST ss_B (INV_0 B MT 0).
Proof. exact rt_B_aux. Qed.
End e.
End c.
