(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import
  W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs StepSoundBase StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib Defs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes CertSound OblsLib Ops CtrSys StdioWrite DrvShape DrvLib.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP StepB StepS PlanS FXN CertS OL Ops CtrS SW DrvShape DrvLib.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module DrvEdges.

Definition SIZE11 : sv := VBlob false 11%uint63 (VL (wp 0%uint63)) 8%uint63.
Definition B4 (i : int) : sv := VBlob false 4%uint63 (VL (wp i)) 1%uint63.
Definition CFGX : sv :=
  VAlu ALU_OR (VAlu ALU_SRL (VAlu ALU_SLL (VBlob true 4%uint63 (VL (wp 1%uint63)) 1%uint63) (VL (wp 57%uint63))) (VL (wp 49%uint63))) (B4 0%uint63).
Definition MINUS6 : w64 := wn 9223372036854775802%uint63.
Definition PAYX : sv := VAlu ALU_ADD (VAlu ALU_SUB SIZE11 CFGX) (VL MINUS6).
Definition SELX : sv := VAlu ALU_AND (B4 2%uint63) (VL (wp 3%uint63)).
Definition CNTX : sv := VExt true 0%uint63 8%uint63 (VBlob true 4%uint63 (VL (wp 1%uint63)) 1%uint63).

Definition fact_eqb (f g : fact) : bool :=
  match f, g with
  | FRange k a b, FRange k' a' b' => PrimInt63.eqb k k' && weqb a a' && weqb b b'
  | FAlign k m, FAlign k' m' => PrimInt63.eqb k k' && PrimInt63.eqb m m'
  | FULt a b, FULt a' b' | FULe a b, FULe a' b' | FEq a b, FEq a' b' | FNe a b, FNe a' b'
  | FSLt a b, FSLt a' b' | FSLe a b, FSLe a' b' => sv_eqb a a' && sv_eqb b b'
  | _, _ => false
  end.
Definition has_fact (f : fact) (fs : list fact) : bool := existsb (fact_eqb f) fs.

Lemma fact_eqb_eq : forall f g, fact_eqb f g = true -> f = g.
Proof.
  intros f g H. destruct f, g; cbn [fact_eqb] in H; try discriminate H;
    repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H end;
    repeat match goal with H : PrimInt63.eqb _ _ = true |- _ => apply Uint63.eqb_correct in H end;
    repeat match goal with H : weqb _ _ = true |- _ => apply weqb_eq in H end;
    repeat match goal with H : sv_eqb _ _ = true |- _ => apply sv_eqb_eq in H end; subst; reflexivity.
Qed.

Lemma has_fact_sound : forall E f fs, facts_hold E fs -> has_fact f fs = true -> fact_holds E f.
Proof.
  intros E f fs Hfs H. unfold has_fact in H. apply existsb_exists in H. destruct H as (g & Hin & Hg).
  apply fact_eqb_eq in Hg. subst g. exact (proj1 (Forall_forall _ _) Hfs f Hin).
Qed.

Definition size_ub1 (f : fact) : option Z :=
  match f with
  | FULt a (VL c) => if sv_eqb a SIZE11 then Some (w2Z c - 1) else None
  | FULe a (VL c) => if sv_eqb a SIZE11 then Some (w2Z c) else None
  | FEq a (VL c) => if sv_eqb a SIZE11 then Some (w2Z c) else None
  | _ => None
  end.
Definition size_lb1 (f : fact) : option Z :=
  match f with
  | FULt (VL c) b => if sv_eqb b SIZE11 then Some (w2Z c + 1) else None
  | FULe (VL c) b => if sv_eqb b SIZE11 then Some (w2Z c) else None
  | FEq a (VL c) => if sv_eqb a SIZE11 then Some (w2Z c) else None
  | _ => None
  end.

Definition size_below (fs : list fact) (hi : Z) : bool :=
  existsb (fun f => match size_ub1 f with Some u => u <? hi | None => false end) fs.
Definition size_atleast (fs : list fact) (lo : Z) : bool :=
  existsb (fun f => match size_lb1 f with Some l => lo <=? l | None => false end) fs.
Definition has_lt6 (fs : list fact) : bool := size_below fs 6.
Definition has_ge6 (fs : list fact) : bool := size_atleast fs 6.
Inductive rdb := RPost | RGrow | RBig.
Definition rd_edge (fs : list fact) (d : nat) (cap : Z) : option rdb :=
  if size_below fs cap then Some RPost
  else if size_atleast fs cap then (match d with O => Some RBig | S _ => Some RGrow end)
  else None.
Definition rdb_shape (file : list byte) (b : rdb) (d : nat) (cap : Z) : shp :=
  match b with
  | RPost => POST file
  | RGrow => RDn file (Nat.pred d) (2 * cap)
  | RBig => MSG MSG_BIG
  end.

Inductive pbr := PShort | PCfg | PLib (c : nat) | PMf (c : nat).

Definition calls_of (fs : list fact) : option nat :=
  if has_fact (FEq CFGX (VL (wp 0%uint63))) fs then Some 1%nat
  else if has_fact (FNe CFGX (VL (wp 0%uint63))) fs then
    (if has_fact (FEq SELX (VL (wp 0%uint63))) fs then Some 1%nat
     else if has_fact (FEq SELX (VL (wp 1%uint63))) fs then Some 2%nat
     else if has_fact (FEq SELX (VL (wp 2%uint63))) fs then Some 3%nat
     else if has_fact (FEq SELX (VL (wp 3%uint63))) fs then Some 4%nat
     else None)
  else None.
Definition post_branch (fs : list fact) : option pbr :=
  if has_lt6 fs then Some PShort
  else if has_ge6 fs then
    if has_fact (FULt SIZE11 (VAlu ALU_ADD CFGX (VL (wp 6%uint63)))) fs then Some PCfg
    else if has_fact (FULe (VAlu ALU_ADD CFGX (VL (wp 6%uint63))) SIZE11) fs then
      match calls_of fs with
      | Some c => if has_fact (FEq PAYX (VL (wp 0%uint63))) fs then Some (PLib c)
                  else if has_fact (FULt (VL (wp 0%uint63)) PAYX) fs then Some (PMf c)
                  else None
      | None => None
      end
    else None
  else None.
Definition pbr_shape (file : list byte) (b : pbr) : shp :=
  match b with
  | PShort => MSG MSG_SHORT
  | PCfg => MSG MSG_CFG
  | PLib c => CALLS c FRESH
  | PMf c => CALLS c FRESH
  end.

Definition xc_edge (fs : list fact) : option Z :=
  if has_fact (FSLt CNTX (VL (wp 0%uint63))) fs then Some 0
  else if has_fact (FSLe (VL (wp 0%uint63)) CNTX) fs then Some 2
  else None.

Section File.
Variables (segs : list Segment) (R : drun).
Hypothesis HF : file_pb R.
Let file := r_file R.
Let S := fsize file.

Lemma S_range : 0 <= S <= Z.of_nat (length file) /\ S <= 2 ^ 62.
Proof. unfold S, fsize. lia. Qed.

Lemma den_SIZE11 : forall E, r_PB R (eb E) -> bv_unsigned (den E SIZE11) = S.
Proof.
  intros E HPB. destruct (HF _ HPB) as (_ & H11 & _). unfold SIZE11. apply (den_param8_u E 11%uint63 S H11). pose proof S_range. lia.
Qed.

Lemma den_lit : forall E i, bv_unsigned (den E (VL (wp i))) = to_Z i.
Proof. intros. apply OL.den_lit. Qed.

Lemma to_Z_of_Z_small : forall z, 0 <= z < 2 ^ 62 -> to_Z (of_Z z) = z.
Proof. intros z Hz. rewrite of_Z_spec, wB_two63. apply Z.mod_small. rewrite two63_eq. lia. Qed.

Lemma size_below_sound : forall E fs hi, r_PB R (eb E) -> facts_hold E fs -> size_below fs hi = true -> S < hi.
Proof.
  intros E fs hi HPB Hfs H. unfold size_below in H. apply existsb_exists in H. destruct H as (f & Hin & Hf).
  pose proof (proj1 (Forall_forall _ _) Hfs f Hin) as X.
  destruct f as [ | |a b|a b|a b| | | ]; cbn [size_ub1] in Hf; try discriminate Hf;
    destruct b; try discriminate Hf; destruct (sv_eqb a SIZE11) eqn:Ea; try discriminate Hf;
    apply sv_eqb_eq in Ea; subst a; apply Z.ltb_lt in Hf; cbn [fact_holds] in X;
    try (apply (f_equal bv_unsigned) in X); rewrite (den_SIZE11 E HPB) in X; cbn [den] in X; rewrite wbv_unsigned in X; lia.
Qed.
Lemma size_atleast_sound : forall E fs lo, r_PB R (eb E) -> facts_hold E fs -> size_atleast fs lo = true -> lo <= S.
Proof.
  intros E fs lo HPB Hfs H. unfold size_atleast in H. apply existsb_exists in H. destruct H as (f & Hin & Hf).
  pose proof (proj1 (Forall_forall _ _) Hfs f Hin) as X.
  destruct f as [ | |a b|a b|a b| | | ]; cbn [size_lb1] in Hf; try discriminate Hf.
  - destruct a; try discriminate Hf. destruct (sv_eqb b SIZE11) eqn:Eb; try discriminate Hf. apply sv_eqb_eq in Eb; subst b.
    apply Z.leb_le in Hf. cbn [fact_holds] in X. rewrite (den_SIZE11 E HPB) in X. cbn [den] in X. rewrite wbv_unsigned in X. lia.
  - destruct a; try discriminate Hf. destruct (sv_eqb b SIZE11) eqn:Eb; try discriminate Hf. apply sv_eqb_eq in Eb; subst b.
    apply Z.leb_le in Hf. cbn [fact_holds] in X. rewrite (den_SIZE11 E HPB) in X. cbn [den] in X. rewrite wbv_unsigned in X. lia.
  - destruct b; try discriminate Hf. destruct (sv_eqb a SIZE11) eqn:Ea; try discriminate Hf. apply sv_eqb_eq in Ea; subst a.
    apply Z.leb_le in Hf. cbn [fact_holds] in X. apply (f_equal bv_unsigned) in X. rewrite (den_SIZE11 E HPB) in X. cbn [den] in X. rewrite wbv_unsigned in X. lia.
Qed.
Lemma size_lt_of : forall E fs c, r_PB R (eb E) -> facts_hold E fs -> 0 <= c < 2 ^ 62 -> size_below fs c = true -> size file < c.
Proof.
  intros E fs c HPB Hfs Hc H. pose proof (size_below_sound E fs c HPB Hfs H). pose proof S_range. unfold S, fsize, size in *. lia.
Qed.
Lemma size_ge_of : forall E fs c, r_PB R (eb E) -> facts_hold E fs -> 0 <= c < 2 ^ 62 -> size_atleast fs c = true -> c <= size file.
Proof.
  intros E fs c HPB Hfs Hc H. pose proof (size_atleast_sound E fs c HPB Hfs H). pose proof S_range. unfold S, fsize, size in *. lia.
Qed.

Lemma file_len_ge : forall E fs, r_PB R (eb E) -> facts_hold E fs ->
  has_ge6 fs = true -> (6 <= length file)%nat /\ 6 <= S.
Proof.
  intros E fs HPB Hfs H. pose proof S_range. pose proof (size_atleast_sound E fs 6 HPB Hfs H). split; lia.
Qed.
Lemma file_len_lt : forall E fs, r_PB R (eb E) -> facts_hold E fs -> has_lt6 fs = true -> S < 6.
Proof. intros E fs HPB Hfs H. exact (size_below_sound E fs 6 HPB Hfs H). Qed.

Lemma S_cases : S = size file \/ (2 ^ 62 <= size file /\ S = 2 ^ 62).
Proof. unfold S, fsize, size. lia. Qed.

Definition fb (i : nat) : Z := bv_unsigned (nth i file (Z_to_bv 8 0)).
Lemma fb_range : forall i, 0 <= fb i < 256.
Proof. intros i. unfold fb. apply byte_small. Qed.

Lemma den_B4 : forall E i (n : nat), r_PB R (eb E) -> to_Z i = Z.of_nat n -> (n < length file)%nat ->
  bv_unsigned (den E (B4 i)) = fb n.
Proof.
  intros E i n HPB Hi Hn. destruct (HF _ HPB) as (H4 & _). unfold B4.
  rewrite (den_byte_at E 4%uint63 (VL (wp i)) file n H4); [| rewrite den_lit; exact Hi | exact Hn].
  unfold fb. apply Z_to_bv64_unsigned. pose proof (byte_small (nth n file (Z_to_bv 8 0))). lia.
Qed.

Definition sb1 : Z := if fb 1 <? 128 then fb 1 else two64 - 256 + fb 1.

Lemma den_SB1 : forall E, r_PB R (eb E) -> (1 < length file)%nat ->
  bv_unsigned (den E (VBlob true 4%uint63 (VL (wp 1%uint63)) 1%uint63)) = sb1.
Proof.
  intros E HPB Hn. destruct (HF _ HPB) as (H4 & _). cbn [den]. rewrite H4, wbv_unsigned. change (w2Z (wp 1%uint63)) with 1.
  change (to_Z 1%uint63) with 1. unfold bytes_val, blob_bytes. change (Z.to_nat 1) with 1%nat.
  destruct (skipn 1 file) as [|b rest] eqn:Hs.
  { exfalso. apply (f_equal (@length byte)) in Hs. rewrite length_skipn in Hs. cbn in Hs. lia. }
  assert (Hb : nth 1 file (Z_to_bv 8 0) = b) by (rewrite <- (Nat.add_0_r 1), <- nth_skipn, Hs; reflexivity).
  fold file. rewrite Hs. cbn [firstn bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r.
  unfold sb1, fb. rewrite Hb. pose proof (byte_small b) as Bb.
  unfold ext_Z. change (2 ^ (8 * 0)) with 1. change (2 ^ (8 * 1)) with 256. change (2 ^ (8 * 1 - 1)) with 128.
  rewrite Z.div_1_r, (Z.mod_small _ 256) by lia.
  destruct (Z.leb_spec 128 (bv_unsigned b)) as [Hge|Hlt].
  - replace (bv_unsigned b <? 128) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite Z_to_bv64_unsigned; unfold two64 in *.
    + rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
    + pose proof (Z.mod_pos_bound (bv_unsigned b - 256) 18446744073709551616 ltac:(lia)). lia.
  - replace (bv_unsigned b <? 128) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite Z.mod_small by (unfold two64; lia). apply Z_to_bv64_unsigned. lia.
Qed.

Lemma sb1_mod128 : sb1 mod 128 = fb 1 mod 128.
Proof.
  unfold sb1. pose proof (fb_range 1). destruct (fb 1 <? 128); [reflexivity|].
  unfold two64. replace (18446744073709551616 - 256 + fb 1) with (fb 1 + 144115188075855870 * 128) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma sb1_range : 0 <= sb1 < two64.
Proof. unfold sb1, two64. pose proof (fb_range 1). destruct (fb 1 <? 128); lia. Qed.

Lemma cfg_len_eq : (2 <= length file)%nat -> cfg_len file = (fb 1 mod 128) * 256 + fb 0.
Proof.
  intros Hn. unfold cfg_len, cfgw, fb. destruct file as [|b0 [|b1 rest]]; try (cbn in Hn; lia). cbn [nth].
  pose proof (byte_small b0). pose proof (byte_small b1).
  pose proof (Z.div_mod (bv_unsigned b1) 128 ltac:(lia)) as E1.
  pose proof (Z.mod_pos_bound (bv_unsigned b1) 128 ltac:(lia)).
  replace (bv_unsigned b0 + 256 * bv_unsigned b1) with ((bv_unsigned b1 mod 128 * 256 + bv_unsigned b0) + (bv_unsigned b1 / 128) * 32768) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma den_CFGX : forall E, r_PB R (eb E) -> (2 <= length file)%nat -> bv_unsigned (den E CFGX) = cfg_len file.
Proof.
  intros E HPB Hn. rewrite (cfg_len_eq Hn). unfold CFGX.
  cbn [den alu64 alu]. rewrite bv_or_unsigned, bv_shiftr_unsigned, bv_shiftl_unsigned, !bv_and_unsigned.
  fold (den E (VBlob true 4%uint63 (VL (wp 1%uint63)) 1%uint63)). fold (den E (B4 0%uint63)).
  rewrite (den_SB1 E HPB) by lia. rewrite (den_B4 E 0%uint63 0 HPB eq_refl) by lia.
  cbn [den]. rewrite !wbv_unsigned. change (w2Z (wp 57%uint63)) with 57. change (w2Z (wp 49%uint63)) with 49.
  rewrite !Z_to_bv_unsigned. change (Z.land 57 (bv_wrap 64 63)) with 57. change (Z.land 49 (bv_wrap 64 63)) with 49.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. unfold bv_wrap. rewrite bv_modulus_64.
  replace two64 with (2 ^ 7 * 2 ^ 57) by reflexivity.
  rewrite Z.mul_mod_distr_r by lia. change (2 ^ 7) with 128. rewrite sb1_mod128.
  replace (2 ^ 57) with (2 ^ 8 * 2 ^ 49) by reflexivity. rewrite Z.mul_assoc, Z.div_mul by lia.
  rewrite Z.lor_comm. pose proof (fb_range 0). pose proof (Z.mod_pos_bound (fb 1) 128 ltac:(lia)).
  rewrite (lor_disjoint_add (fb 0) (fb 1 mod 128) 8); [change (2 ^ 8) with 256; lia | change (2 ^ 8) with 256; lia | lia].
Qed.

Lemma den_PAYX : forall E, r_PB R (eb E) -> (2 <= length file)%nat ->
  bv_unsigned (den E PAYX) = (S - cfg_len file - 6) mod two64.
Proof.
  intros E HPB Hn. unfold PAYX. cbn [den alu64 alu]. rewrite bv_add_unsigned, bv_sub_unsigned.
  fold (den E SIZE11). fold (den E CFGX). rewrite (den_SIZE11 E HPB), (den_CFGX E HPB Hn), wbv_unsigned.
  change (w2Z MINUS6) with (two64 - 6). unfold bv_wrap. rewrite bv_modulus_64.
  rewrite Z.add_mod_idemp_l by (unfold two64; lia).
  replace (S - cfg_len file + (two64 - 6)) with ((S - cfg_len file - 6) + 1 * two64) by lia.
  rewrite Z.mod_add by (unfold two64; lia). reflexivity.
Qed.

Lemma cfg_len_range : 0 <= cfg_len file < 32768.
Proof. unfold cfg_len. apply Z.mod_pos_bound. lia. Qed.

Lemma den_CFG6 : forall E, r_PB R (eb E) -> (2 <= length file)%nat ->
  bv_unsigned (den E (VAlu ALU_ADD CFGX (VL (wp 6%uint63)))) = cfg_len file + 6.
Proof.
  intros E HPB Hn. rewrite OL.den_add, (den_CFGX E HPB Hn), den_lit. change (to_Z 6%uint63) with 6.
  pose proof cfg_len_range. apply Z.mod_small. lia.
Qed.

Lemma den_SELX : forall E, r_PB R (eb E) -> (3 <= length file)%nat -> bv_unsigned (den E SELX) = fb 2 mod 4.
Proof.
  intros E HPB Hn. unfold SELX. cbn [den alu64 alu]. rewrite bv_and_unsigned. fold (den E (B4 2%uint63)).
  rewrite (den_B4 E 2%uint63 2 HPB eq_refl) by lia. rewrite wbv_unsigned. change (w2Z (wp 3%uint63)) with (Z.ones 2).
  apply Z.land_ones. lia.
Qed.

Lemma den_CNTX : forall E, r_PB R (eb E) -> (2 <= length file)%nat -> den E CNTX = Z_to_bv 64 sb1.
Proof.
  intros E HPB Hn. unfold CNTX. cbn [den]. fold (den E (VBlob true 4%uint63 (VL (wp 1%uint63)) 1%uint63)).
  unfold ext_word. rewrite (den_SB1 E HPB) by lia. change (to_Z 0%uint63) with 0. change (to_Z 8%uint63) with 8.
  f_equal. pose proof sb1_range as SR. unfold ext_Z. change (2 ^ (8 * 0)) with 1. rewrite Z.div_1_r.
  change (2 ^ (8 * 8)) with two64. change (2 ^ (8 * 8 - 1)) with (2 ^ 63). rewrite (Z.mod_small sb1 two64) by lia.
  destruct (Z.leb_spec (2 ^ 63) sb1).
  - replace (sb1 - two64) with (sb1 + (-1) * two64) by lia. rewrite Z.mod_add by (unfold two64; lia). apply Z.mod_small. lia.
  - apply Z.mod_small. lia.
Qed.

Lemma signed_CNTX : forall E, r_PB R (eb E) -> (2 <= length file)%nat ->
  bv_signed (den E CNTX) = (if fb 1 <? 128 then fb 1 else fb 1 - 256).
Proof.
  intros E HPB Hn. rewrite (den_CNTX E HPB Hn), Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus. rewrite bv_modulus_64.
  change (two64 `div` 2) with (2 ^ 63). pose proof (fb_range 1). unfold sb1.
  destruct (fb 1 <? 128) eqn:C.
  - apply Z.ltb_lt in C. rewrite Z.mod_small by (unfold two64; lia). lia.
  - apply Z.ltb_ge in C. replace (two64 - 256 + fb 1 + 2 ^ 63) with ((fb 1 - 256 + 2 ^ 63) + 1 * two64) by lia.
    rewrite Z.mod_add by (unfold two64; lia). rewrite Z.mod_small by (unfold two64; lia). lia.
Qed.

Lemma count_bit_iff : (2 <= length file)%nat -> count_bit file = (128 <=? fb 1).
Proof.
  intros Hn. unfold count_bit, cfgw, fb. destruct file as [|b0 [|b1 rest]]; try (cbn in Hn; lia). cbn [nth].
  pose proof (byte_small b0). pose proof (byte_small b1).
  destruct (Z.leb_spec 128 (bv_unsigned b1)); [apply (proj2 (Z.leb_le _ _)); lia | apply (proj2 (Z.leb_gt _ _)); lia].
Qed.

Lemma calls_of_sound : forall E fs c, r_PB R (eb E) -> facts_hold E fs -> (3 <= length file)%nat ->
  calls_of fs = Some c -> calls file = c.
Proof.
  intros E fs c HPB Hfs Hn H. unfold calls_of in H. unfold calls.
  destruct (has_fact (FEq CFGX (VL (wp 0%uint63))) fs) eqn:C0.
  - injection H as <-. pose proof (has_fact_sound E _ fs Hfs C0) as X. cbn [fact_holds] in X.
    apply (f_equal bv_unsigned) in X. rewrite (den_CFGX E HPB) in X by lia. rewrite den_lit in X. change (to_Z 0%uint63) with 0 in X.
    rewrite X. reflexivity.
  - destruct (has_fact (FNe CFGX (VL (wp 0%uint63))) fs) eqn:C1; [|discriminate H].
    pose proof (has_fact_sound E _ fs Hfs C1) as X. cbn [fact_holds] in X.
    assert (NZ : cfg_len file <> 0).
    { intros Z0. apply X. apply bv_eq. rewrite (den_CFGX E HPB) by lia. rewrite den_lit. rewrite Z0. reflexivity. }
    replace (cfg_len file =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ).
    assert (SEL : forall k, has_fact (FEq SELX (VL (wp k))) fs = true -> fb 2 mod 4 = to_Z k).
    { intros k Hk. pose proof (has_fact_sound E _ fs Hfs Hk) as Y. cbn [fact_holds] in Y. apply (f_equal bv_unsigned) in Y.
      rewrite (den_SELX E HPB Hn), den_lit in Y. exact Y. }
    unfold fb in SEL.
    destruct (has_fact (FEq SELX (VL (wp 0%uint63))) fs) eqn:S0; [injection H as <-; rewrite (SEL _ S0); reflexivity|].
    destruct (has_fact (FEq SELX (VL (wp 1%uint63))) fs) eqn:S1; [injection H as <-; rewrite (SEL _ S1); reflexivity|].
    destruct (has_fact (FEq SELX (VL (wp 2%uint63))) fs) eqn:S2; [injection H as <-; rewrite (SEL _ S2); reflexivity|].
    destruct (has_fact (FEq SELX (VL (wp 3%uint63))) fs) eqn:S3; [injection H as <-; rewrite (SEL _ S3); reflexivity|].
    discriminate H.
Qed.

Theorem post_branch_sound : forall E fs br, r_PB R (eb E) -> facts_hold E fs ->
  post_branch fs = Some br -> POST file = pbr_shape file br.
Proof.
  intros E fs br HPB Hfs H. unfold post_branch in H. pose proof S_range as SR. pose proof S_cases as SC. pose proof cfg_len_range as CR.
  destruct (has_lt6 fs) eqn:F1.
  { injection H as <-. pose proof (file_len_lt E fs HPB Hfs F1) as X.
    cbn [pbr_shape]. apply POST_short. unfold size in *. lia. }
  destruct (has_ge6 fs) eqn:F2; [|discriminate H].
  destruct (file_len_ge E fs HPB Hfs F2) as [Hn6 HS6].
  destruct (has_fact (FULt SIZE11 (VAlu ALU_ADD CFGX (VL (wp 6%uint63)))) fs) eqn:F3.
  { injection H as <-. pose proof (has_fact_sound E _ fs Hfs F3) as X. cbn [fact_holds] in X.
    rewrite (den_SIZE11 E HPB), (den_CFG6 E HPB) in X by lia.
    cbn [pbr_shape]. apply POST_cfg; unfold size in *; lia. }
  destruct (has_fact (FULe (VAlu ALU_ADD CFGX (VL (wp 6%uint63))) SIZE11) fs) eqn:F4; [|discriminate H].
  pose proof (has_fact_sound E _ fs Hfs F4) as X4. cbn [fact_holds] in X4. rewrite (den_SIZE11 E HPB), (den_CFG6 E HPB) in X4 by lia.
  destruct (calls_of fs) as [c|] eqn:HC; [|discriminate H].
  pose proof (calls_of_sound E fs c HPB Hfs ltac:(lia) HC) as Hcalls.
  destruct (has_fact (FEq PAYX (VL (wp 0%uint63))) fs) eqn:F5.
  { injection H as <-. pose proof (has_fact_sound E _ fs Hfs F5) as X. cbn [fact_holds] in X. apply (f_equal bv_unsigned) in X.
    rewrite (den_PAYX E HPB), den_lit in X by lia. change (to_Z 0%uint63) with 0 in X.
    rewrite Z.mod_small in X by (unfold two64; lia).
    cbn [pbr_shape]. rewrite <- Hcalls. apply POST_empty; unfold payload_len, size in *; lia. }
  destruct (has_fact (FULt (VL (wp 0%uint63)) PAYX) fs) eqn:F6; [|discriminate H].
  injection H as <-. pose proof (has_fact_sound E _ fs Hfs F6) as X. cbn [fact_holds] in X.
  rewrite (den_PAYX E HPB), den_lit in X by lia. change (to_Z 0%uint63) with 0 in X.
  rewrite Z.mod_small in X by (unfold two64; lia).
  cbn [pbr_shape]. rewrite <- Hcalls. apply POST_payload; unfold payload_len, size in *; lia.
Qed.

Theorem rd_edge_sound : forall E fs d cap b, r_PB R (eb E) -> facts_hold E fs -> 0 <= cap < 2 ^ 62 ->
  rd_edge fs d cap = Some b -> RDn file d cap = rdb_shape file b d cap.
Proof.
  intros E fs d cap b HPB Hfs Hcap H. unfold rd_edge in H.
  destruct (size_below fs cap) eqn:F1.
  - injection H as <-. cbn [rdb_shape]. apply RDn_post. exact (size_lt_of E fs cap HPB Hfs Hcap F1).
  - destruct (size_atleast fs cap) eqn:F2; [|discriminate H].
    pose proof (size_ge_of E fs cap HPB Hfs Hcap F2) as G.
    destruct d as [|d']; injection H as <-; cbn [rdb_shape Nat.pred].
    + apply RDn_big. exact G.
    + apply RDn_grow. exact G.
Qed.

Theorem xc_edge_sound : forall E fs c, r_PB R (eb E) -> facts_hold E fs ->
  xc_edge fs = Some c -> XC file = SX c.
Proof.
  intros E fs c HPB Hfs H. unfold xc_edge in H.
  destruct (Nat.lt_ge_cases (length file) 2) as [Hsmall | Hn].
  -
    assert (D0 : den E CNTX = Z_to_bv 64 0).
    { destruct (HF _ HPB) as (H4 & _). unfold CNTX. cbn [den]. rewrite H4, wbv_unsigned. change (w2Z (wp 1%uint63)) with 1.
      change (to_Z 1%uint63) with 1. unfold bytes_val, blob_bytes. change (Z.to_nat 1) with 1%nat. fold file.
      rewrite skipn_all2 by lia. cbn. reflexivity. }
    assert (CB : count_bit file = false).
    { unfold count_bit, cfgw. destruct file as [|b0 [|b1 rest]]; try (cbn in Hsmall; lia); reflexivity. }
    destruct (has_fact (FSLt CNTX (VL (wp 0%uint63))) fs) eqn:F1.
    + pose proof (has_fact_sound E _ fs Hfs F1) as X. cbn [fact_holds] in X. rewrite D0 in X.
      vm_compute in X. discriminate X.
    + destruct (has_fact (FSLe (VL (wp 0%uint63)) CNTX) fs) eqn:F2; [|discriminate H]. injection H as <-. apply XC_plain. exact CB.
  - pose proof (signed_CNTX E HPB Hn) as SG. pose proof (count_bit_iff Hn) as CB. pose proof (fb_range 1) as B1.
    assert (Z0 : bv_signed (den E (VL (wp 0%uint63))) = 0) by reflexivity.
    destruct (has_fact (FSLt CNTX (VL (wp 0%uint63))) fs) eqn:F1.
    + injection H as <-. pose proof (has_fact_sound E _ fs Hfs F1) as X. cbn [fact_holds] in X. rewrite SG, Z0 in X.
      apply XC_count. rewrite CB. apply Z.leb_le. destruct (fb 1 <? 128) eqn:C; [apply Z.ltb_lt in C; lia | apply Z.ltb_ge in C; lia].
    + destruct (has_fact (FSLe (VL (wp 0%uint63)) CNTX) fs) eqn:F2; [|discriminate H]. injection H as <-.
      pose proof (has_fact_sound E _ fs Hfs F2) as X. cbn [fact_holds] in X. rewrite SG, Z0 in X.
      apply XC_plain. rewrite CB. apply Z.leb_gt. destruct (fb 1 <? 128) eqn:C; [apply Z.ltb_lt in C; lia | apply Z.ltb_ge in C; lia].
Qed.

Theorem edge_post : forall T br, post_branch (s_facts T) = Some br ->
  NODE segs R T (DR R (pbr_shape file br)) -> NODE segs R T (DR R (POST file)).
Proof.
  intros T br H HN. apply (node_facts segs R T _ _ HN). intros E HPB _ Hfs.
  rewrite (post_branch_sound E (s_facts T) br HPB Hfs H). apply t_eq_refl.
Qed.

Theorem edge_rd : forall T (d : nat) (cap : Z) b, 0 <= cap < 2 ^ 62 -> rd_edge (s_facts T) d cap = Some b ->
  NODE segs R T (DR R (rdb_shape file b d cap)) -> NODE segs R T (DR R (RDn file d cap)).
Proof.
  intros T d cap b Hcap H HN. apply (node_facts segs R T _ _ HN). intros E HPB _ Hfs.
  rewrite (rd_edge_sound E (s_facts T) d cap b HPB Hfs Hcap H). apply t_eq_refl.
Qed.

Theorem edge_xc : forall T c, xc_edge (s_facts T) = Some c ->
  NODE segs R T (DR R (SX c)) -> NODE segs R T (DR R (XC file)).
Proof.
  intros T c H HN. apply (node_facts segs R T _ _ HN). intros E HPB _ Hfs.
  rewrite (xc_edge_sound E (s_facts T) c HPB Hfs H). apply t_eq_refl.
Qed.

Definition B14 : sv := VBlob false 14%uint63 (VL (wp 0%uint63)) 8%uint63.
Definition B13 : sv := VBlob false 13%uint63 (VL (wp 0%uint63)) 8%uint63.

Definition chk_obl (o : obligation) : bool :=
  let fs := fst o in
  has_ge6 fs &&
  (fact_eqb (snd o) (FEq (VAlu ALU_ADD CFGX (VL (wp 6%uint63))) B14)
   || (fact_eqb (snd o) (FEq PAYX B13)
       && (has_fact (FULe (VAlu ALU_ADD CFGX (VL (wp 6%uint63))) SIZE11) fs
           || size_atleast fs 32773))).

Theorem obls_file_sound : forall (l : list obligation), forallb chk_obl l = true -> obls_hold (r_PB R) l.
Proof.
  intros l H. unfold obls_hold. apply Forall_forall. intros o Ho E HPB Hz Hfs.
  pose proof (proj1 (forallb_forall _ _) H o Ho) as C. unfold chk_obl in C. cbv zeta in C.
  apply andb_prop in C as [H6 C]. destruct (file_len_ge E (fst o) HPB Hfs H6) as [Hn HS6].
  destruct (HF _ HPB) as (H4 & H11 & H5 & H14 & H13). fold file in H4, H11, H5, H14, H13. fold S in H11, H13.
  pose proof cfg_len_range as CR. pose proof S_range as SR.
  apply orb_prop in C. destruct C as [C|C].
  - apply fact_eqb_eq in C. rewrite C. cbn [fact_holds]. apply bv_eq. rewrite (den_CFG6 E HPB) by lia.
    unfold B14. rewrite (den_param8_u E 14%uint63 _ H14) by lia. lia.
  - apply andb_prop in C as [C H66]. apply fact_eqb_eq in C. rewrite C. cbn [fact_holds]. apply bv_eq. rewrite (den_PAYX E HPB) by lia.
    assert (X : cfg_len file + 6 <= S).
    { apply orb_prop in H66 as [H66|H66].
      - pose proof (has_fact_sound E _ _ Hfs H66) as X. cbn [fact_holds] in X. rewrite (den_SIZE11 E HPB), (den_CFG6 E HPB) in X by lia. exact X.
      -
        pose proof (size_atleast_sound E _ 32773 HPB Hfs H66). lia. }
    unfold B13. rewrite (den_param8_u E 13%uint63 _ H13) by lia. rewrite Z.mod_small by (unfold two64; lia). lia.
Qed.

End File.
End DrvEdges.
