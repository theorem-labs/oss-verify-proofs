(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_tbl_iface RF_huf_tbl_kit RF_huf_fdw_kit.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma reload_not_err : forall bs d e, reload_dstream bs d <> Err e.
Proof.
  intros bs d e. unfold reload_dstream, readLE64. cbv zeta.
  repeat (match goal with |- context [if ?c then _ else _] => destruct c end); cbn; discriminate.
Qed.

Lemma fi_read_bits_ok : forall d nb, 0 <= nb < 32 ->
  read_bits d nb = Ok (Z.land (Z.shiftr (bd_cont d) ((u32 (64 - bd_bits d - nb)) mod 64)) (2^nb - 1), skip_bits d nb).
Proof.
  intros d nb H. unfold read_bits, look_bits, bit_mask.
  replace ((0 <=? nb) && (nb <? 32)) with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  reflexivity.
Qed.

Lemma fi_skip_ok : forall bs d nb, bitd_ok bs d -> bd_bits d <= 2^29 -> 0 <= nb <= 12 ->
  bitd_ok bs (skip_bits d nb) /\ bd_bits (skip_bits d nb) = bd_bits d + nb.
Proof.
  intros bs [c b p z] nb (B0 & B1 & B2 & B3 & B4 & B5) BB N. cbn [bd_cont bd_bits bd_ptr bd_zero] in *.
  unfold skip_bits, u32, bitd_ok. cbn [bd_cont bd_bits bd_ptr bd_zero].
  rewrite Z.mod_small by lia.
  split; [ | lia].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact B4|].
  intros Z1. specialize (B5 Z1). lia.
Qed.

Lemma fi_add_byte : forall bs k sh acc v, Forall (fun c => 0 <= c < 256) bs -> 0 <= sh ->
  add_byte bs k sh acc = Ok v -> exists a, acc = Ok a /\ a <= v <= a + 255 * 2^sh.
Proof.
  intros bs k sh acc v BY SH H. unfold add_byte in H. cbv zeta in H.
  destruct acc as [a| | |]; cbn [bind] in H; try discriminate.
  exists a. split; [reflexivity|].
  assert (P : 0 <= 2^sh) by (apply Z.pow_nonneg; lia).
  revert H. destruct (k <? FseNCount.Zlength bs) eqn:K; intro H.
  - unfold load in H. revert H. destruct ((0 <=? k) && (k <? FseNCount.Zlength bs)) eqn:L; intro H; cbn [bind] in H; try discriminate.
    injection H as <-. apply andb_prop in L. destruct L as [L1 L2]. apply Z.leb_le in L1. apply Z.ltb_lt in L2.
    pose proof (byte_Znth bs k BY ltac:(unfold FseNCount.Zlength in L2; lia)) as BK. nia.
  - injection H as <-. lia.
Qed.

Lemma fi_add_byte_err : forall bs k sh acc e, add_byte bs k sh acc = Err e -> acc = Err e.
Proof.
  intros bs k sh acc e H. unfold add_byte in H. cbv zeta in H.
  destruct acc as [a|e'| |]; cbn [bind] in H; try discriminate; [|exact H].
  revert H. destruct (k <? FseNCount.Zlength bs); intro H; [|discriminate].
  unfold load in H. revert H. destruct ((0 <=? k) && (k <? FseNCount.Zlength bs)); intro H; cbn [bind] in H; discriminate.
Qed.

Lemma fi_log2_byte : forall x, 0 < x < 256 -> 0 <= Z.log2 x <= 7.
Proof.
  intros x H. split; [apply Z.log2_nonneg|].
  assert (Z.log2 x < 8) by (apply Z.log2_lt_pow2; [lia | change (2^8) with 256; lia]). lia.
Qed.

Ltac fi_chain ID A := revert ID; destruct A as [?c| ?e| |] eqn:?; cbn [bind]; intro ID; try discriminate.

Lemma fi_init_facts : forall bs d, Forall (fun c => 0 <= c < 256) bs -> init_dstream bs = Ok d ->
  bitd_ok bs d /\ bd_bits d <= 64 /\ bd_zero d = false.
Proof.
  intros bs d BY ID. unfold init_dstream in ID. cbv zeta in ID. unfold FseNCount.Zlength in ID.
  destruct (Z_lt_le_dec (zlen bs) 1) as [N1|N1].
  { replace (zlen bs <? 1) with true in ID by (symmetry; apply Z.ltb_lt; lia). discriminate. }
  replace (zlen bs <? 1) with false in ID by (symmetry; apply Z.ltb_ge; lia).
  destruct (Z_le_gt_dec 8 (zlen bs)) as [N8|N8].
  - replace (8 <=? zlen bs) with true in ID by (symmetry; apply Z.leb_le; lia).
    rewrite HufWalkKit.readLE64_ok in ID by lia. cbn [bind] in ID.
    unfold load, FseNCount.Zlength in ID.
    replace ((0 <=? zlen bs - 1) && (zlen bs - 1 <? zlen bs)) with true in ID
      by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    cbn [bind] in ID.
    pose proof (byte_Znth bs (zlen bs - 1) BY ltac:(lia)) as BL.
    revert ID. destruct (Znth (zlen bs - 1) bs =? 0) eqn:E0; intro ID; [discriminate|]. apply Z.eqb_neq in E0.
    rewrite highbit32_ok in ID by lia. cbn [bind] in ID. injection ID as <-.
    pose proof (fi_log2_byte (Znth (zlen bs - 1) bs) ltac:(lia)) as LG.
    pose proof (le64v_range bs (zlen bs - 8) BY) as LR. unfold le64v in LR.
    unfold bitd_ok. cbn [bd_cont bd_bits bd_ptr bd_zero].
    split; [|split; [lia | reflexivity]].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [intros; lia|]. intros Z1; discriminate Z1.
  - replace (8 <=? zlen bs) with false in ID by (symmetry; apply Z.leb_gt; lia).
    unfold load at 1 in ID. unfold FseNCount.Zlength in ID.
    replace ((0 <=? 0) && (0 <? zlen bs)) with true in ID
      by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    cbn [bind] in ID.
    pose proof (byte_Znth bs 0 BY ltac:(lia)) as B0.
    fi_chain ID (add_byte bs 1 8 (add_byte bs 2 16 (add_byte bs 3 24 (add_byte bs 4 32 (add_byte bs 5 40 (add_byte bs 6 48 (Ok (Znth 0 bs)))))))).
    match goal with A : add_byte bs 1 8 _ = Ok ?c |- _ =>
      apply fi_add_byte in A; [|exact BY|lia]; destruct A as (a1 & A1 & R1) end.
    apply fi_add_byte in A1; [|exact BY|lia]. destruct A1 as (a2 & A2 & R2).
    apply fi_add_byte in A2; [|exact BY|lia]. destruct A2 as (a3 & A3 & R3).
    apply fi_add_byte in A3; [|exact BY|lia]. destruct A3 as (a4 & A4 & R4).
    apply fi_add_byte in A4; [|exact BY|lia]. destruct A4 as (a5 & A5 & R5).
    apply fi_add_byte in A5; [|exact BY|lia]. destruct A5 as (a6 & A6 & R6).
    injection A6 as A6. subst a6.
    unfold load in ID. unfold FseNCount.Zlength in ID.
    replace ((0 <=? zlen bs - 1) && (zlen bs - 1 <? zlen bs)) with true in ID
      by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    cbn [bind] in ID.
    pose proof (byte_Znth bs (zlen bs - 1) BY ltac:(lia)) as BL.
    revert ID. destruct (Znth (zlen bs - 1) bs =? 0) eqn:E0; intro ID; [discriminate|]. apply Z.eqb_neq in E0.
    rewrite highbit32_ok in ID by lia. cbn [bind] in ID. injection ID as <-.
    pose proof (fi_log2_byte (Znth (zlen bs - 1) bs) ltac:(lia)) as LG.
    try change (2^8) with 256 in *. try change (2^16) with 65536 in *. try change (2^24) with 16777216 in *.
    try change (2^32) with 4294967296 in *. try change (2^40) with 1099511627776 in *. try change (2^48) with 281474976710656 in *.
    unfold bitd_ok. cbn [bd_cont bd_bits bd_ptr bd_zero].
    split; [|split; [lia | reflexivity]].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [intros; lia|]. intros Z1; discriminate Z1.
Qed.

Lemma fi_init_err : forall bs e, init_dstream bs = Err e -> 0 < e < 120.
Proof.
  intros bs e ID. unfold init_dstream in ID. cbv zeta in ID. unfold FseNCount.Zlength in ID.
  destruct (Z_lt_le_dec (zlen bs) 1) as [N1|N1].
  { replace (zlen bs <? 1) with true in ID by (symmetry; apply Z.ltb_lt; lia). injection ID as <-.
    unfold ZSTD_error_srcSize_wrong. lia. }
  replace (zlen bs <? 1) with false in ID by (symmetry; apply Z.ltb_ge; lia).
  destruct (Z_le_gt_dec 8 (zlen bs)) as [N8|N8].
  - replace (8 <=? zlen bs) with true in ID by (symmetry; apply Z.leb_le; lia).
    rewrite HufWalkKit.readLE64_ok in ID by lia. cbn [bind] in ID.
    unfold load, FseNCount.Zlength in ID.
    replace ((0 <=? zlen bs - 1) && (zlen bs - 1 <? zlen bs)) with true in ID
      by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    cbn [bind] in ID.
    revert ID. destruct (Znth (zlen bs - 1) bs =? 0) eqn:E0; intro ID.
    + injection ID as <-. unfold ZSTD_error_GENERIC. lia.
    + unfold highbit32 in ID. revert ID.
      destruct ((0 <? Znth (zlen bs - 1) bs) && (Znth (zlen bs - 1) bs <? 2^32)); intro ID; cbn [bind] in ID; discriminate.
  - replace (8 <=? zlen bs) with false in ID by (symmetry; apply Z.leb_gt; lia).
    unfold load at 1 in ID. unfold FseNCount.Zlength in ID.
    replace ((0 <=? 0) && (0 <? zlen bs)) with true in ID
      by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    cbn [bind] in ID.
    revert ID.
    destruct (add_byte bs 1 8 (add_byte bs 2 16 (add_byte bs 3 24 (add_byte bs 4 32 (add_byte bs 5 40 (add_byte bs 6 48 (Ok (Znth 0 bs)))))))) as [c|e'| |] eqn:A1;
      cbn [bind]; intro ID; try discriminate.
    2:{ injection ID as <-.
        repeat (apply fi_add_byte_err in A1). discriminate A1. }
    unfold load in ID. unfold FseNCount.Zlength in ID.
    replace ((0 <=? zlen bs - 1) && (zlen bs - 1 <? zlen bs)) with true in ID
      by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    cbn [bind] in ID.
    revert ID. destruct (Znth (zlen bs - 1) bs =? 0) eqn:E0; intro ID.
    + injection ID as <-. match goal with |- 0 < ?c < 120 => let v := eval vm_compute in c in change c with v end. lia.
    + unfold highbit32 in ID. revert ID.
      destruct ((0 <? Znth (zlen bs - 1) bs) && (Znth (zlen bs - 1) bs <? 2^32)); intro ID; cbn [bind] in ID; discriminate.
Qed.

Ltac fi_bok_mk := unfold bitd_ok; cbn [bd_cont bd_bits bd_ptr bd_zero];
  split; [lia|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [intros; lia|]; intros Z1; discriminate Z1.

Lemma fi_reload_facts : forall bs d st d', Forall (fun c => 0 <= c < 256) bs -> bitd_ok bs d ->
  reload_dstream bs d = Ok (st, d') ->
  bitd_ok bs d' /\ bd_bits d' <= bd_bits d
  /\ (bd_bits d <= 64 -> bd_zero d' = false /\ match st with Unfinished | EndOfBuffer | Completed => True | _ => False end)
  /\ (64 < bd_bits d -> match st with Unfinished | EndOfBuffer | Completed => False | _ => True end
                        /\ d' = mkBD (bd_cont d) (bd_bits d) (bd_ptr d) true).
Proof.
  intros bs [c b p z] st d' BY BOK RL. pose proof BOK as (B0 & B1 & B2 & B3 & B4 & B5).
  cbn [bd_cont bd_bits bd_ptr bd_zero] in *.
  unfold reload_dstream in RL. cbn [bd_cont bd_bits bd_ptr bd_zero] in RL. cbv zeta in RL.
  destruct (Z_lt_le_dec 64 b) as [OV|OV].
  - replace (64 <? b) with true in RL by (symmetry; apply Z.ltb_lt; lia).
    injection RL as <- <-.
    split; [|split; [cbn [bd_bits]; lia | split; [cbn [bd_bits]; intros; lia | intros _; split; [exact I | reflexivity]]]].
    unfold bitd_ok. cbn [bd_cont bd_bits bd_ptr bd_zero].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact B4|]. intros _; lia.
  - replace (64 <? b) with false in RL by (symmetry; apply Z.ltb_ge; lia).
    assert (Z0 : z = false) by (destruct z; [specialize (B5 eq_refl); lia | reflexivity]). subst z.
    rewrite Z.shiftr_div_pow2 in RL by lia. change (2^3) with 8 in RL.
    assert (Q : 0 <= b / 8 <= 8) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    destruct (Z_le_gt_dec 8 p) as [FP|FP].
    + replace (8 <=? p) with true in RL by (symmetry; apply Z.leb_le; lia).
      rewrite HufWalkKit.readLE64_ok in RL by lia. cbn [bind] in RL. injection RL as <- <-.
      pose proof (le64v_range bs (p - b / 8) BY) as LR. unfold le64v in LR.
      assert (L7 : 0 <= Z.land b 7 <= b /\ Z.land b 7 < 8).
      { change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8.
        pose proof (Z.mod_pos_bound b 8 ltac:(lia)). pose proof (Z.mod_le b 8 ltac:(lia) ltac:(lia)). lia. }
      split; [fi_bok_mk | cbn [bd_bits bd_zero]; split; [lia | split; [intros; split; [reflexivity | exact I] | intros; lia]]].
    + replace (8 <=? p) with false in RL by (symmetry; apply Z.leb_gt; lia).
      destruct (Z.eq_dec p 0) as [P0|P0].
      * replace (p =? 0) with true in RL by (symmetry; apply Z.eqb_eq; lia). injection RL as <- <-.
        split; [exact BOK|]. cbn [bd_bits bd_zero].
        split; [lia|]. split; [intros; split; [reflexivity | destruct (b <? 64); exact I] | intros; lia].
      * replace (p =? 0) with false in RL by (symmetry; apply Z.eqb_neq; lia).
        assert (N8 : 8 <= zlen bs) by (destruct (Z_lt_le_dec (zlen bs) 8) as [Hl|Hl]; [specialize (B4 Hl); lia | lia]).
        destruct (Z_lt_le_dec (p - b / 8) 0) as [E|E].
        -- replace (p - b / 8 <? 0) with true in RL by (symmetry; apply Z.ltb_lt; lia).
           cbv beta iota zeta in RL. rewrite HufWalkKit.readLE64_ok in RL by lia. cbn [bind] in RL. injection RL as <- <-.
           pose proof (le64v_range bs (p - p) BY) as LR. unfold le64v in LR.
           split; [fi_bok_mk | cbn [bd_bits bd_zero]; split; [lia | split; [intros; split; [reflexivity | exact I] | intros; lia]]].
        -- replace (p - b / 8 <? 0) with false in RL by (symmetry; apply Z.ltb_ge; lia).
           cbv beta iota zeta in RL. rewrite HufWalkKit.readLE64_ok in RL by lia. cbn [bind] in RL. injection RL as <- <-.
           pose proof (le64v_range bs (p - b / 8) BY) as LR. unfold le64v in LR.
           split; [fi_bok_mk | cbn [bd_bits bd_zero]; split; [lia | split; [intros; split; [reflexivity | exact I] | intros; lia]]].
Qed.

Lemma fi_dsym_not_err : forall dt fast s d e, decode_sym dt fast s d <> Err e.
Proof.
  intros dt fast s d e. unfold decode_sym, HufPure_FseDecomp.cell.
  match goal with |- context [if ?c then _ else _] => destruct c end; cbn [bind]; [|discriminate].
  destruct fast; cbn [bind].
  - unfold read_bits_fast. cbn. discriminate.
  - unfold read_bits, look_bits, bit_mask.
    match goal with |- context [if ?c then _ else _] => destruct c end; cbn [bind]; discriminate.
Qed.

Lemma fi_main_loop_not_err : forall bs dt dcap fast f x e, main_loop bs dt dcap fast f x <> Err e.
Proof.
  intros bs dt dcap fast f. induction f as [|f IH]; intros x e; [discriminate|].
  cbn [main_loop].
  destruct (reload_dstream bs (de_bd x)) as [[st d0]|e1| |] eqn:RL; cbn [bind]; try discriminate.
  2: exfalso; exact (reload_not_err _ _ _ RL).
  match goal with |- context [if ?c then _ else _] => destruct c end; [|discriminate].
  destruct (decode_sym dt fast (de_s1 x) d0) as [[[o0 s1a] d1]|e2| |] eqn:D1; cbn [bind]; try discriminate;
    [|exfalso; exact (fi_dsym_not_err _ _ _ _ _ D1)].
  destruct (decode_sym dt fast (de_s2 x) d1) as [[[o1 s2a] d2]|e3| |] eqn:D2; cbn [bind]; try discriminate;
    [|exfalso; exact (fi_dsym_not_err _ _ _ _ _ D2)].
  destruct (decode_sym dt fast s1a d2) as [[[o2 s1b] d3]|e4| |] eqn:D3; cbn [bind]; try discriminate;
    [|exfalso; exact (fi_dsym_not_err _ _ _ _ _ D3)].
  destruct (decode_sym dt fast s2a d3) as [[[o3 s2b] d4]|e5| |] eqn:D4; cbn [bind]; try discriminate;
    [|exfalso; exact (fi_dsym_not_err _ _ _ _ _ D4)].
  apply IH.
Qed.

Lemma fi_nullx_ok : forall p q, 0 < p -> 0 <= q -> q <> p ->
  Z.lxor (Z.b2z (0 <? p)) (Z.b2z (Z.lxor p q <? 1)) = 0 -> False.
Proof.
  intros p q P Q N H. rewrite (proj2 (Z.ltb_lt 0 p) P) in H.
  assert (X : Z.lxor p q <> 0) by (intro E; apply N; symmetry; apply Z.lxor_eq; exact E).
  assert (X0 : 0 <= Z.lxor p q) by (apply Z.lxor_nonneg; split; intros; lia).
  rewrite (proj2 (Z.ltb_ge (Z.lxor p q) 1) ltac:(lia)) in H. discriminate H.
Qed.

Lemma fi_div8_le : forall a, 0 <= a <= 64 -> 0 <= a / 8 <= 8.
Proof. intros a H. split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. Qed.

Ltac fi_zn1 H := match type of H with
  | context [sx32 (Z_to_bv 64 ?x)] => rewrite (sx32_small x) in H by lia
  | context [zx16 (Z_to_bv 64 ?x)] => rewrite (zx16_lit x) in H by lia
  | context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) in H by lia
  | context [bv_wrap 32 ?x] => unfold bv_wrap in H; change (bv_modulus 32) with (2^32) in H
  | context [bv_swrap 32 ?x] => rewrite (swrap32_small x) in H by lia
  | context [Z.shiftl ?x ?n] => rewrite (Z.shiftl_mul_pow2 x n) in H by lia
  | context [Z.shiftr ?x ?n] => rewrite (Z.shiftr_div_pow2 x n) in H by lia
  | context [?x mod ?y] => rewrite (Z.mod_small x y) in H by lia
  | context [2 ^ ?k] => is_Zlit k; let v := eval vm_compute in (2 ^ k) in change (2 ^ k) with v in H
  | context [?x * ?c / ?c] => is_Zlit c; rewrite (Z.div_mul x c) in H by lia
  end.
Ltac fi_zn H := repeat fi_zn1 H.
Ltac fi_znG1 := match goal with
  | |- context [sx32 (Z_to_bv 64 ?x)] => rewrite (sx32_small x) by lia
  | |- context [zx16 (Z_to_bv 64 ?x)] => rewrite (zx16_lit x) by lia
  | |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by lia
  | |- context [bv_wrap 32 ?x] => unfold bv_wrap; change (bv_modulus 32) with (2^32)
  | |- context [bv_swrap 32 ?x] => rewrite (swrap32_small x) by lia
  | |- context [Z.shiftl ?x ?n] => rewrite (Z.shiftl_mul_pow2 x n) by lia
  | |- context [Z.shiftr ?x ?n] => rewrite (Z.shiftr_div_pow2 x n) by lia
  | |- context [?x mod ?y] => rewrite (Z.mod_small x y) by lia
  | |- context [2 ^ ?k] => is_Zlit k; let v := eval vm_compute in (2 ^ k) in change (2 ^ k) with v
  | |- context [?x * ?c / ?c] => is_Zlit c; rewrite (Z.div_mul x c) by lia
  end.
Ltac fi_znG := repeat fi_znG1.
Ltac fi_arith_only := repeat match goal with
  | H : ?T |- _ => lazymatch type of T with Prop =>
      lazymatch T with
      | @eq Z _ _ => fail | Z.le _ _ => fail | Z.lt _ _ => fail | Z.ge _ _ => fail | Z.gt _ _ => fail | not (@eq Z _ _) => fail
      | and _ _ => fail | or _ _ => fail | @eq bool _ _ => fail
      | _ => clear H end end end.
Ltac fi_zn_all := repeat match goal with H : _ |- _ => progress (fi_zn H) end.
Ltac fi_gen_div8 := repeat match goal with |- context [?a / 8] =>
  let H := fresh "D8" in let q := fresh "q" in let E := fresh "E" in
  assert (H : 0 <= a / 8 <= 8) by (apply fi_div8_le; lia); remember (a / 8) as q eqn:E; clear E end.
Ltac fi_bsplit := repeat match goal with
  | H : context [Z.b2z (?a <? ?b)] |- _ => let E := fresh "Eb" in revert H; destruct (a <? b) eqn:E; intro H; zify_bool E; simpl in H; rewrite ?Z.lxor_0_r, ?Z.lxor_0_l, ?Z.lxor_nilpotent in H
  | H : context [Z.b2z (?a =? ?b)] |- _ => let E := fresh "Eb" in revert H; destruct (a =? b) eqn:E; intro H; zify_bool E; simpl in H; rewrite ?Z.lxor_0_r, ?Z.lxor_0_l, ?Z.lxor_nilpotent in H
  | H : context [Z.b2z (?a <=? ?b)] |- _ => let E := fresh "Eb" in revert H; destruct (a <=? b) eqn:E; intro H; zify_bool E; simpl in H; rewrite ?Z.lxor_0_r, ?Z.lxor_0_l, ?Z.lxor_nilpotent in H
  end.
Ltac fi_refute U := exfalso; fi_arith_only; first [ lia
  | (fi_bsplit; lia)
  | (fi_zn U; revert U; fi_gen_div8; intros U; lia)
  | (fi_zn U; lia)
  | (eapply fi_nullx_ok; [ | | | exact U]; fi_znG; fi_gen_div8; lia)
  | (change 1 with (Z.ones 1) in U; rewrite Z.land_ones in U by lia; change (2^1) with 2 in U; lia)
  | (change 7 with (Z.ones 3) in U; rewrite Z.land_ones in U by lia; change (2^3) with 8 in U; lia) ].
Ltac fi_is_uim pc := let b := eval vm_compute in (Z.eqb pc 0x20828) in lazymatch b with true => idtac end.
Ltac fi_side_uim := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => fi_is_uim pc end.
Ltac fi_alive U := let T := type of U in idtac "ALIVE" T.
Ltac fi_side U := first [ fi_side_uim; first [fi_refute U | fi_alive U] | try (exfalso; fi_arith_only; (first [lia | fi_zn U; lia])) ].
Ltac fi_chk := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  lazymatch c with
  | true => cbv iota
  | false => cbv iota
  | _ => let U := fresh "U" in if_cases U; zify_cond U; fi_side U
  end end.
Ltac fi_uimref := fi_side_uim; exfalso; fi_arith_only; first [ (try fi_zn_all; lia) | (fi_bsplit; lia) ].
Ltac fi_notcallee := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
  let b := eval vm_compute in (existsb (Z.eqb pc) [0x2082c; 0x20ac0; 0x20de4]) in lazymatch b with true => fail | false => idtac end end.
Ltac fi_norm := rewrite ?zx16_lit by lia; try (rewrite ?Z.shiftl_mul_pow2 by lia).
Ltac fi_notuim := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
  tryif fi_is_uim pc then fail else idtac end.
Ltac fi_notin L := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
  let b := eval vm_compute in (existsb (Z.eqb pc) L) in lazymatch b with true => fail | false => idtac end end.
Ltac fi_walk_until L := repeat (first [fi_chk | fi_uimref | fi_notin L; fi_notuim; fi_notcallee; zstep; fi_norm]).
Ltac fi_reg_val r :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
  end.
Ltac fi_setreg r v' tac := let v := fi_reg_val r in replace v with v' by tac.
Ltac fi_src8 S bs SRC p := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  let R0 := fresh "RB" in let R1 := fresh "RB" in let R2 := fresh "RB" in let R3 := fresh "RB" in
  let R4 := fresh "RB" in let R5 := fresh "RB" in let R6 := fresh "RB" in let R7 := fresh "RB" in
  pose proof (src_rd usegs mm S bs (p + 0) SRC ltac:(lia)) as R0;
  pose proof (src_rd usegs mm S bs (p + 1) SRC ltac:(lia)) as R1;
  pose proof (src_rd usegs mm S bs (p + 2) SRC ltac:(lia)) as R2;
  pose proof (src_rd usegs mm S bs (p + 3) SRC ltac:(lia)) as R3;
  pose proof (src_rd usegs mm S bs (p + 4) SRC ltac:(lia)) as R4;
  pose proof (src_rd usegs mm S bs (p + 5) SRC ltac:(lia)) as R5;
  pose proof (src_rd usegs mm S bs (p + 6) SRC ltac:(lia)) as R6;
  pose proof (src_rd usegs mm S bs (p + 7) SRC ltac:(lia)) as R7;
  rewrite ?Z.add_assoc, ?Z.add_0_r in R0, R1, R2, R3, R4, R5, R6, R7 end.

Lemma fi_land_rng : forall x n, 0 <= n -> 0 <= Z.land x (2^n - 1) < 2^n.
Proof.
  intros x n N. replace (2^n - 1) with (Z.ones n) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

Ltac fi_fixbd H c b p T := lazymatch type of H with
  | rw_cells _ _ _ (C8 (Z_to_bv 64 ?c0) :: C4 (Z_to_bv 64 ?b0) :: ?c2 :: C8 (Z_to_bv 64 ?p0) :: ?rest) =>
      replace c0 with c in H by T; replace b0 with b in H by T; replace p0 with p in H by T end.

Section LE64FI.
  Variables (ra sp gp tp x6 x7 x8 x9 x11 x12 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : fmem) (S : Z) (bs : list Z) (POST : machine_state -> Prop).
  Hypothesis SRC : bytes_at usegs m S (map (Z_to_bv 8) bs).
  Hypothesis BY : Forall (fun c => 0 <= c < 256) bs.

  Lemma fi_ld : forall (p : Z) (y5 y10 y13 y14 y15 y16 : word),
    0 <= p -> p + 8 <= zlen bs ->
    (forall (z5 z13 z14 z15 z16 : word),
       evt usegs POST (MS (mkR ra sp gp tp z5 x6 x7 x8 x9 (Z_to_bv 64 (le64v bs p)) x11 x12 z13 z14 z15 z16 (Z_to_bv 64 (S + p))
                               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F (Z_to_bv 64 0x1f90c) fc None m (seg_rom usegs))) ->
    evt usegs POST (MS (mkR ra sp gp tp y5 x6 x7 x8 x9 y10 x11 x12 y13 y14 y15 y16 (Z_to_bv 64 (S + p))
                            x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x1f8b4) fc None m (seg_rom usegs)).
  Proof.
    intros p y5 y10 y13 y14 y15 y16 P0 P8 K.
    assert (BYn : forall i, 0 <= i < zlen bs -> 0 <= Znth i bs < 256) by (intros; apply byte_Znth; auto).
    fi_src8 S bs SRC p.
    do 22 zstep.
    rewrite le64_lbu_raw by (apply BYn; lia).
    rewrite Z.add_0_r. apply K.
  Qed.
End LE64FI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
