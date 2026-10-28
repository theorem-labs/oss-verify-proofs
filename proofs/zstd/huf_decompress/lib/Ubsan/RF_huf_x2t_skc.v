(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufStats HufPure_HufX2
  HufPure_HufTableX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseWalkArith StrFun HufWalkKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_bdt_model
  RF_huf_x2t_model RF_huf_x2t_c1.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac simpl_arr_sizes ::= rewrite ?u32s_length, ?u64s_length, ?upd_length, ?u16s_length, ?length_map,
  ?omerge_length, ?ox2_length, ?upd_bytes_length in *.

Lemma sk_shl2 : forall x, x ≪ 2 = 4 * x.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. lia. Qed.

Lemma sk_lx63 : forall o, 0 <= o < 9223372036854775808 -> (Z.lxor o 9223372036854775808 <? 9223372036854775808) = false.
Proof. intros o Ho. change 9223372036854775808 with (2 ^ 63). rewrite zb_lxor_pow2_small by lia. apply Z.ltb_ge. lia. Qed.

Local Ltac pnorm U :=
  repeat match type of U with
         | context [Z.lxor ?o 9223372036854775808 <? 9223372036854775808] => rewrite (sk_lx63 o) in U by lia
         end;
  repeat match type of U with
         | context [?a <? ?b] => rewrite (proj2 (Z.ltb_ge a b)) in U by (rewrite ?Z.mod_small by lia; lia)
         end;
  cbn in U.

Local Ltac pchk U := exfalso; rewrite ?sk_shl2 in U; rewrite ?signed_small2 in U by lia;
  first [ lia | (Z.div_mod_to_equations; lia)
        | (pnorm U; first [discriminate | lia | (Z.div_mod_to_equations; lia)]) ].

Local Ltac cgo stops := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let b := eval vm_compute in (existsb (Z.eqb pc) stops) in lazymatch b with false => zstep end
  | |- evt _ _ (MS _ _ (if _ then Z_to_bv 64 82516 else _) _ _ _ _) =>
      rewrite ?sx32_small by lia; rewrite ?zx32_small2 by lia; rewrite ?swrap32_small by lia; rewrite ?sk_shl2;
      let U := fresh "U" in if_cases U; zify_cond U; [pchk U |]
  | |- evt _ _ (MS _ _ (if _ then _ else Z_to_bv 64 82516) _ _ _ _) =>
      rewrite ?sx32_small by lia; rewrite ?zx32_small2 by lia; rewrite ?swrap32_small by lia; rewrite ?sk_shl2;
      let U := fresh "U" in if_cases U; zify_cond U; [| pchk U]
  end).


Lemma sk_uu : forall cons sym1, 1 <= cons <= 12 -> 0 <= sym1 < 256 ->
  Z.lor (Z.lor (cons * 65536 + 16777216) sym1 ≪ 32 mod 18446744073709551616) (Z.lor (cons * 65536 + 16777216) sym1)
  = (cons * 65536 + 16777216 + sym1) * 4294967297.
Proof.
  intros cons sym1 HC HS.
  rewrite (lor_add (cons * 65536 + 16777216) sym1 8) by (try change (2 ^ 8) with 256; lia).
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 32) with 4294967296.
  rewrite (Z.mod_small _ 18446744073709551616) by lia.
  rewrite (lor_add _ _ 32) by (change (2 ^ 32) with 4294967296; first [lia | rewrite Z.mod_mul by lia; reflexivity]).
  lia.
Qed.

Lemma sk_le2 : forall cons sym1, 1 <= cons <= 12 -> 0 <= sym1 < 256 ->
  let U := (cons * 65536 + 16777216 + sym1) * 4294967297 in
  le2 (Z_to_bv 64 U) = [Z_to_bv 8 sym1; Z_to_bv 8 (sym1 / 256)]
  /\ le2 (Z_to_bv 64 (U ≫ 16)) = [Z_to_bv 8 cons; Z_to_bv 8 1]
  /\ le2 (Z_to_bv 64 (U ≫ 32)) = [Z_to_bv 8 sym1; Z_to_bv 8 (sym1 / 256)]
  /\ le2 (Z_to_bv 64 (U ≫ 48)) = [Z_to_bv 8 cons; Z_to_bv 8 1].
Proof.
  intros cons sym1 HC HS U. subst U.
  rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ 16) with 65536. change (2 ^ 32) with 4294967296. change (2 ^ 48) with 281474976710656.
  repeat split.
  - apply le2_of_mod16. rewrite unsigned_lit by lia. Z.div_mod_to_equations; lia.
  - apply le2_hi; [rewrite unsigned_lit by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia);
                   Z.div_mod_to_equations; lia | lia | lia].
  - apply le2_of_mod16. rewrite unsigned_lit by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    Z.div_mod_to_equations; lia.
  - apply le2_hi; [rewrite unsigned_lit by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia);
                   Z.div_mod_to_equations; lia | lia | lia].
Qed.

Local Ltac cellw DT4 ARR u c :=
  xh DT4 ARR (4 * u); cgo (@nil Z); xh DT4 ARR (4 * u + 2);
  replace (Z.to_nat (4 * u)) with (4 * Z.to_nat u)%nat in ARR by lia;
  replace (Z.to_nat (4 * u + 2)) with (4 * Z.to_nat u + 2)%nat in ARR by lia;
  lazymatch type of ARR with
  | context [upd_bytes (upd_bytes (ox2 ?jt ?cells) _ [?a; ?b]) _ [?d; ?e]] =>
      replace [a; b] with [Z_to_bv 8 (x2_seq c); Z_to_bv 8 (x2_seq c / 256)] in ARR
        by (match goal with H : x2_seq c = _ |- _ => rewrite H end; reflexivity);
      replace [d; e] with [Z_to_bv 8 (x2_nbBits c); Z_to_bv 8 (x2_len c)] in ARR
        by (match goal with H : x2_nbBits c = _, H2 : x2_len c = _ |- _ => rewrite H, H2 end; reflexivity);
      rewrite (ox2_store cells jt (Z.to_nat u) c) in ARR by lia
  end;
  cgo (@nil Z).

Section SKC.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (x1 x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word).
  Variables (m : fmem) (DT SY cons sym1 st skip : Z) (sorted : list (option Z)) (js jt : list byte) (ncells : nat).
  Variable POST : machine_state -> Prop.
  Hypothesis HJT : length jt = (4 * ncells)%nat.
  Hypothesis HJS : length js = length sorted.
  Hypothesis HLS : length sorted = 256%nat.
  Hypothesis HDT : 0 < DT /\ DT + 4 + 4 * Z.of_nat ncells <= 2^47.
  Hypothesis DJ : DT + 4 + 4 * Z.of_nat ncells <= SY \/ SY + 256 <= DT + 4.
  Hypothesis HSY : 0 < SY /\ SY + 256 <= 2^47.
  Hypothesis HCONS : 1 <= cons <= 12.
  Hypothesis HS1 : 0 <= sym1 < 256.
  Hypothesis HST : 0 <= st.
  Hypothesis HSK : 0 < skip <= 4096.
  Notation INV m1 dt := (x2f_inv m m1 DT SY js jt sorted ncells dt).
  Notation D := (cons * 65536 + 16777216).
  Notation UU := (Z.lor (Z.lor D sym1 ≪ 32 mod 18446744073709551616) (Z.lor D sym1)).
  Notation ST pc mm v x5 x6 :=
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (UU ≫ 48)) (Z_to_bv 64 (UU ≫ 32)) (Z_to_bv 64 (UU ≫ 16))
             (Z_to_bv 64 UU) (Z_to_bv 64 skip) (Z_to_bv 64 (DT + 20 + 4 * v)) (Z_to_bv 64 (DT + 4 + 4 * v))
             (Z_to_bv 64 (v - st)) x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 (DT + 4 + 4 * st)) x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Lemma skC_chunks : forall n c dt1 v vend m1 dtR (x5 x6 : word),
    c = build_x2 sym1 cons 0 1 ->
    store_run (8 * n) dt1 v c = Ok dtR -> st <= v -> (v - st) mod 8 = 0 -> v + 8 * Z.of_nat n = vend ->
    vend - 8 < st + skip <= vend -> (0 < n)%nat -> INV m1 dt1 ->
    (forall m2 (y5 y6 : word), INV m2 dtR -> evt usegs POST (ST 0x147c4 m2 vend y5 y6)) ->
    evt usegs POST (ST 0x14748 m1 v x5 x6).
  Proof.
    induction n as [|n IH]; intros c dt1 v vend m1 dtR x5 x6 HC HF Hv Hm Hve Hsk Hn INV CONT; [lia|].
    destruct INV as (ARR & LDT & SYB & MU & WM & MI).
    destruct (build_x2_fields sym1 cons 0 1 HS1 ltac:(lia) ltac:(lia) ltac:(left; reflexivity)) as (CS & CN & CL).
    rewrite Z.eqb_refl in CS. rewrite <- HC in CS, CN, CL.
    destruct (sk_le2 cons sym1 HCONS HS1) as (Q0 & Q1 & Q2 & Q3).
    rewrite (sk_uu cons sym1 HCONS HS1).
    pose proof (store_run_Ok _ _ _ _ _ HF ltac:(lia)) as (LR & BND).
    specialize (BND ltac:(lia)).
    replace (8 * S n)%nat with (S (S (S (S (S (S (S (S (8 * n)))))))))%nat in HF by lia.
    cbn [store_run] in HF.
    apply bind_Ok_inv in HF as (d1 & O1 & HF). apply ostore2_Ok in O1 as (B1 & E1).
    assert (L1 : length d1 = ncells) by (rewrite E1, oset2_length; [exact LDT | lia]).
    apply bind_Ok_inv in HF as (d2 & O2 & HF). apply ostore2_Ok in O2 as (B2 & E2).
    assert (L2 : length d2 = ncells) by (rewrite E2, oset2_length; [exact L1 | lia]).
    apply bind_Ok_inv in HF as (d3 & O3 & HF). apply ostore2_Ok in O3 as (B3 & E3).
    replace (v + 1 + 1) with (v + 2) in B3, E3, HF by lia.
    assert (L3 : length d3 = ncells) by (rewrite E3, oset2_length; [exact L2 | lia]).
    apply bind_Ok_inv in HF as (d4 & O4 & HF). apply ostore2_Ok in O4 as (B4 & E4).
    replace (v + 2 + 1) with (v + 3) in B4, E4, HF by lia.
    assert (L4 : length d4 = ncells) by (rewrite E4, oset2_length; [exact L3 | lia]).
    apply bind_Ok_inv in HF as (d5 & O5 & HF). apply ostore2_Ok in O5 as (B5 & E5).
    replace (v + 3 + 1) with (v + 4) in B5, E5, HF by lia.
    assert (L5 : length d5 = ncells) by (rewrite E5, oset2_length; [exact L4 | lia]).
    apply bind_Ok_inv in HF as (d6 & O6 & HF). apply ostore2_Ok in O6 as (B6 & E6).
    replace (v + 4 + 1) with (v + 5) in B6, E6, HF by lia.
    assert (L6 : length d6 = ncells) by (rewrite E6, oset2_length; [exact L5 | lia]).
    apply bind_Ok_inv in HF as (d7 & O7 & HF). apply ostore2_Ok in O7 as (B7 & E7).
    replace (v + 5 + 1) with (v + 6) in B7, E7, HF by lia.
    assert (L7 : length d7 = ncells) by (rewrite E7, oset2_length; [exact L6 | lia]).
    apply bind_Ok_inv in HF as (d8 & O8 & HF). apply ostore2_Ok in O8 as (B8 & E8).
    replace (v + 6 + 1) with (v + 7) in B8, E8, HF by lia.
    assert (L8 : length d8 = ncells) by (rewrite E8, oset2_length; [exact L7 | lia]).
    zstep. cgo (@nil Z).
    cellw (DT + 4) ARR v c. rewrite <- E1 in ARR.
    cellw (DT + 4) ARR (v + 1) c. rewrite <- E2 in ARR.
    cellw (DT + 4) ARR (v + 2) c. rewrite <- E3 in ARR.
    cellw (DT + 4) ARR (v + 3) c. rewrite <- E4 in ARR.
    cellw (DT + 4) ARR (v + 4) c. rewrite <- E5 in ARR.
    cellw (DT + 4) ARR (v + 5) c. rewrite <- E6 in ARR.
    cellw (DT + 4) ARR (v + 6) c. rewrite <- E7 in ARR.
    cellw (DT + 4) ARR (v + 7) c. rewrite <- E8 in ARR.
    replace (DT + 20 + 4 * v + 32) with (DT + 20 + 4 * (v + 8)) by lia.
    replace (DT + 4 + 4 * v + 32) with (DT + 4 + 4 * (v + 8)) by lia.
    replace (v - st + 8) with (v + 8 - st) by lia.
    rewrite <- (sk_uu cons sym1 HCONS HS1).
    replace (v + 7 + 1) with (v + 8) in HF by lia.
    assert (INV2 : INV m1 d8) by exact (conj ARR (conj L8 (conj SYB (conj MU (conj WM MI))))).
    if_cases K; zify_cond K; rewrite ?signed_small2 in K by lia.
    - destruct n as [|n]; [exfalso; lia|].
      eapply (IH c d8 (v + 8) vend _ dtR); [exact HC | exact HF | lia | | lia | lia | lia | exact INV2 | exact CONT].
      replace (v + 8 - st) with ((v - st) + 1 * 8) by lia. rewrite Z.mod_add by lia. exact Hm.
    - destruct n as [|n]; [|exfalso; lia].
      cbn [Nat.mul store_run] in HF. injection HF as <-.
      replace (v + 8) with vend by lia.
      apply CONT. exact INV2.
  Qed.

End SKC.
