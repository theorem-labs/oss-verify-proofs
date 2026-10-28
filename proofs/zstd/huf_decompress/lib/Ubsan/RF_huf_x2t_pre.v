(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT HufPure_HufStats HufPure_HufX2
  HufPure_HufTableX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseWalkArith StrFun HufWalkKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_bdt_model
  RF_huf_x2t_model.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition PRw (wEnd mB c w : Z) : Z -> Prop := fun j =>
  (1 <= j < wEnd) \/ (exists c' w', mB <= c' /\ ((c' < c /\ 1 <= w' < wEnd) \/ (c' = c /\ 1 <= w' < w)) /\ j = rv_idx c' w').

Ltac pgo stops := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let b := eval vm_compute in (existsb (Z.eqb pc) stops) in
      lazymatch b with false => zstep end
  end).


Lemma find_maxW_nonneg : forall f w rank r, find_maxW f w rank = Ok r -> 0 <= w.
Proof.
  intros [|f] w rank r H; cbn [find_maxW] in H; [discriminate|].
  unfold load in H. destruct (0 <=? w) eqn:E; [apply Z.leb_le in E; exact E|].
  cbn in H. discriminate.
Qed.

Lemma shl2 : forall x, x ≪ 2 = 4 * x.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. lia. Qed.

Lemma sl32_sr30 : forall x, 0 <= x < 2^31 -> (x ≪ 32 mod 18446744073709551616) ≫ 30 = 4 * x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 32) with 4294967296.
  rewrite Z.mod_small by (change (2 ^ 31) with 2147483648 in Hx; lia).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 30) with 1073741824.
  replace (x * 4294967296) with (4 * x * 1073741824) by lia. apply Z.div_mul. lia.
Qed.

Lemma sl32_sr32 : forall x, 0 <= x < 2^31 -> (x ≪ 32 mod 18446744073709551616) ≫ 32 = x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 32) with 4294967296.
  rewrite Z.mod_small by (change (2 ^ 31) with 2147483648 in Hx; lia).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 32) with 4294967296. apply Z.div_mul. lia.
Qed.

Section FM.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).

  Variables (x1 x5 x6 x7 x9 x13 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
  Variables (m : fmem) (WK tl c11 c12 : Z) (rank : list Z).
  Variable POST : machine_state -> Prop.
  Hypothesis HWK : 0 < WK /\ WK + 2124 <= 2^47.
  Hypothesis HTL : 1 <= tl <= 12.
  Hypothesis LRK : length rank = 13%nat.
  Hypothesis RKR : forall i, 0 <= i < 13 -> 0 <= Znth i rank <= 256.
  Hypothesis RKA : u32arr usegs m (WK + 624) (map (Z_to_bv 64) rank).
  Notation ST pc w x15 :=
    (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 w) x9 (Z_to_bv 64 (- (WK + 624) - 1)) (Z_to_bv 64 (c11 + (tl - w)))
             (Z_to_bv 64 (c12 + 2 * (tl - w))) x13 (Z_to_bv 64 13) x15 x16 x17 x18 x19 x20 (Z_to_bv 64 (WK + 624)) x22
             x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).

  Lemma fm_loop : forall f w r (x15 : word), find_maxW f w rank = Ok r -> 0 <= w <= tl ->
    (forall y15 : word, evt usegs POST (ST 0x14258 r y15)) ->
    evt usegs POST (ST 0x14230 w x15).
  Proof.
    induction f as [|f IH]; intros w r x15 HF Hw CONT; [discriminate|].
    cbn [find_maxW] in HF. unfold load in HF. unfold FseNCount.Zlength in HF.
    rewrite LRK in HF. replace ((0 <=? w) && (w <? Z.of_nat 13)) with true in HF
      by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    cbn [bind] in HF.
    pose proof (RKR w ltac:(lia)) as RW.
    pose proof (u32arr_read usegs m (WK + 624) _ w _ (wa (WK + 624 + w ≪ 2)) RKA (nth_map_Znth2 rank w ltac:(lia))
                  ltac:(lia) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
    zstep. pgo [0x14258; 0x14230]. if_cases U1; zify_cond U1.
    { exfalso. rewrite Z.shiftl_mul_pow2 in U1 by lia. Z.div_mod_to_equations. lia. }
    pgo [0x14258; 0x14230].
    rewrite sx32_small by lia.
    if_cases U2; zify_cond U2.
    - rewrite (proj2 (Z.eqb_neq _ _) U2) in HF. cbn iota in HF. injection HF as HE. subst r.
      apply CONT.
    - assert (EZ : Znth w rank = 0) by lia.
      rewrite EZ in HF. cbn [Z.eqb] in HF.
      pose proof (find_maxW_nonneg _ _ _ _ HF) as W1.
      pgo [0x14258; 0x14230].
      rewrite swrap32_small by lia.
      if_cases U3; zify_cond U3; [|exfalso; lia].
      replace (w + -1) with (w - 1) by lia.
      replace (c11 + (tl - w) + 1) with (c11 + (tl - (w - 1))) by lia.
      replace (c12 + 2 * (tl - w) + 2) with (c12 + 2 * (tl - (w - 1))) by lia.
      apply (IH (w - 1) r); [exact HF | lia | exact CONT].
  Qed.

End FM.

Section RS2.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).

  Variables (x1 x8 x9 x10 x11 x12 x13 x15 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
  Variables (m : fmem) (WK wEnd : Z) (rank : list Z).
  Variable POST : machine_state -> Prop.
  Hypothesis HWK : 0 < WK /\ WK + 2124 <= 2^47.
  Hypothesis HWE : 2 <= wEnd <= 13.
  Hypothesis LRK : length rank = 13%nat.
  Hypothesis RKR : forall i, 0 <= i < 13 -> 0 <= Znth i rank <= 256.
  Hypothesis RKA0 : u32arr usegs m (WK + 624) (map (Z_to_bv 64) rank).
  Notation RINV m1 rs0 := (u32arr usegs m1 (WK + 676) (map (Z_to_bv 64) rs0) /\ length rs0 = 15%nat
                           /\ munch [(WK + 676, WK + 736)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1).
  Notation ST pc mm w next x7 :=
    (MS (mkR x1 sp gp tp (Z_to_bv 64 (4 * w)) (Z_to_bv 64 next) x7 x8 x9 x10 x11 x12 x13 (Z_to_bv 64 (- (WK + 680) - 1))
             x15 (Z_to_bv 64 (WK + 680 + 4 * w)) (Z_to_bv 64 (4 * wEnd)) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
             x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Lemma rs_loop : forall f w next rs0 m1 r (x7 : word),
    rank_start2 f w next rank rs0 = Ok r -> Z.of_nat f = wEnd - w -> 1 <= w < wEnd -> 0 <= next <= 256 * (w - 1) ->
    RINV m1 rs0 ->
    (forall m2 rs0' next', r = (rs0', next') -> 0 <= next' <= 256 * (wEnd - 1) -> RINV m2 rs0' ->
       evt usegs POST (ST 0x1429c m2 wEnd next' (Z_to_bv 64 next'))) ->
    evt usegs POST (ST 0x1427c m1 w next x7).
  Proof.
    induction f as [|f IH]; intros w next rs0 m1 r x7 HF Hf Hw Hn INV CONT; [lia|].
    destruct INV as (RA & LR & MU & WM & MI).
    cbn [rank_start2] in HF. unfold load, store in HF. unfold FseNCount.Zlength in HF.
    rewrite LRK, LR in HF.
    replace ((0 <=? w) && (w <? Z.of_nat 13)) with true in HF
      by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    replace ((0 <=? w + 1) && (w + 1 <? Z.of_nat 15)) with true in HF
      by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    cbn [bind] in HF.
    pose proof (RKR w ltac:(lia)) as RW.
    pose proof (u32arr_transport usegs _ m m1 _ _ RKA0 MU WM
                  ltac:(rewrite length_map, LRK; cbn; split; [lia | exact I])) as RK1.
    pose proof (u32arr_read usegs m1 (WK + 624) _ w _ (wa (WK + 624 + 4 * w)) RK1 (nth_map_Znth2 rank w ltac:(lia))
                  ltac:(lia) eq_refl) as RD.
    pose proof (u32arr_store_ok usegs m1 (WK + 676) _ (w + 1) (wa (WK + 676 + 4 * (w + 1))) RA
                  ltac:(rewrite length_map, LR; lia) eq_refl) as SOK.
    zstep. if_cases U1; zify_cond U1; [exfalso; Z.div_mod_to_equations; lia|].
    zstep. zstep.
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) _) _) => replace E with (WK + 676 + 4 * (w + 1)) by lia
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (Z_to_bv 64 ?E) _) _) => replace E with (WK + 676 + 4 * (w + 1)) by lia
    end.
    pose proof (u32arr_write usegs _ (WK + 676) _ (w + 1) (Z_to_bv 64 next) RA ltac:(rewrite length_map, LR; lia)) as RA2.
    clear RA. store_done. rename RA2 into RA.
    rewrite sx32_small by lia.
    pgo [0x1429c; 0x1427c].
    assert (RA' : u32arr usegs m0 (WK + 676) (map (Z_to_bv 64) (Zupd (w + 1) next rs0)))
      by (unfold Zupd; rewrite map_upd_nat; exact RA).
    assert (LR' : length (Zupd (w + 1) next rs0) = 15%nat) by (unfold Zupd; rewrite upd_nat_length2; exact LR).
    assert (NX : u32 (next + Znth w rank) = Znth w rank + next) by (unfold u32; rewrite Z.mod_small by lia; lia).
    rewrite <- NX.
    replace (WK + 680 + 4 * w + 4) with (WK + 680 + 4 * (w + 1)) by lia.
    replace (4 * w + 4) with (4 * (w + 1)) by lia.
    if_cases U2; zify_cond U2.
    - apply (IH (w + 1) (u32 (next + Znth w rank)) (Zupd (w + 1) next rs0) m0 r); [exact HF | lia | lia | lia | | exact CONT].
      exact (conj RA' (conj LR' (conj MU (conj WM MI)))).
    - assert (f = O) by lia. subst f. cbn [rank_start2] in HF. injection HF as HR.
      replace (w + 1) with wEnd by lia.
      apply (CONT m0 (Zupd (w + 1) next rs0) (u32 (next + Znth w rank))); [symmetry; exact HR | lia |].
      exact (conj RA' (conj LR' (conj MU (conj WM MI)))).
  Qed.

End RS2.

Section SO2.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).

  Variables (x1 x8 x9 x10 x11 x12 x19 x21 x22 x23 x24 x25 x26 x27 x31 : word).
  Variables (m : fmem) (WK nbS : Z) (ws : list Z) (jk js : list byte).
  Variable POST : machine_state -> Prop.
  Hypothesis HWK : 0 < WK /\ WK + 2124 <= 2^47.
  Hypothesis HNS : 1 <= nbS <= 256.
  Hypothesis LWS : zlen ws = nbS.
  Hypothesis WSR : forall i, 0 <= i < nbS -> 0 <= Znth i ws <= 12.
  Hypothesis LJK : zlen jk = 256 - nbS.
  Hypothesis LJS : length js = 256%nat.
  Hypothesis HWA0 : u8arr usegs m (WK + 992) (map (Z_to_bv 8) ws ++ jk).
  Notation SINV m1 rs0 sorted := (u32arr usegs m1 (WK + 676) (map (Z_to_bv 64) rs0) /\ length rs0 = 15%nat
                           /\ u8arr usegs m1 (WK + 736) (omerge js sorted) /\ length sorted = 256%nat
                           /\ munch [(WK + 676, WK + 992)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1).
  Notation ST pc mm s x28 x29 x30 :=
    (MS (mkR x1 sp gp tp (Z_to_bv 64 (- (WK + 736) - 1)) (Z_to_bv 64 256) (Z_to_bv 64 255) x8 x9 x10 x11 x12
             (Z_to_bv 64 (WK + 680)) (Z_to_bv 64 (- (WK + 680) - 1)) (Z_to_bv 64 nbS) (Z_to_bv 64 s)
             (Z_to_bv 64 (- (WK + 992) - 1)) (Z_to_bv 64 (WK + 736)) x19 (Z_to_bv 64 (WK + 992)) x21 x22 x23 x24 x25 x26
             x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Lemma so2_loop : forall f s rs0 sorted m1 r (x28 x29 x30 : word),
    sort2 f s ws rs0 sorted = Ok r -> Z.of_nat f = nbS - s -> 0 <= s < nbS ->
    (forall i, 0 <= i < 15 -> 0 <= Znth i rs0 <= 256) -> SINV m1 rs0 sorted ->
    (forall m2 rs0' sorted' (y28 y29 y30 : word), r = (rs0', sorted') -> SINV m2 rs0' sorted' ->
       evt usegs POST (ST 0x14318 m2 nbS y28 y29 y30)) ->
    evt usegs POST (ST 0x142d8 m1 s x28 x29 x30).
  Proof.
    induction f as [|f IH]; intros s rs0 sorted m1 r x28 x29 x30 HF Hf Hs RB INV CONT; [lia|].
    destruct INV as (RA & LR & SA & LS & MU & WM & MI).
    cbn [sort2] in HF.
    apply bind_Ok_inv in HF as (w & L1 & HF). apply load_Ok in L1 as (L1 & ->).
    apply bind_Ok_inv in HF as (rr & L2 & HF). apply load_Ok in L2 as (L2 & ->).
    apply bind_Ok_inv in HF as (rs1 & S1 & HF). apply store_Ok in S1 as (S1 & ->).
    apply bind_Ok_inv in HF as (so1 & S2 & HF). apply ostore_Ok in S2 as (S2 & ->).
    pose proof (WSR s ltac:(lia)) as WR.
    set (w := Znth s ws) in *.
    pose proof (RB (w + 1) ltac:(lia)) as RR.
    set (rr := Znth (w + 1) rs0) in *.
    pose proof (u8arr_transport usegs _ m m1 _ _ HWA0 MU WM
                  ltac:(rewrite length_app, length_map; cbn; split; [lia | exact I])) as HWA.
    pose proof (u8arr_read usegs m1 (WK + 992) _ s (Z_to_bv 8 w) (wa (WK + 992 + s)) HWA
                  ltac:(rewrite nth_error_app1 by (rewrite length_map; lia); apply nth_error_map_Znth; lia)
                  ltac:(lia) eq_refl) as RD1.
    pose proof (u32arr_read usegs m1 (WK + 676) _ (w + 1) _ (wa (WK + 676 + 4 * (w + 1))) RA
                  (nth_map_Znth2 rs0 (w + 1) ltac:(lia)) ltac:(lia) eq_refl) as RD2.
    pose proof (u32arr_store_ok usegs m1 (WK + 676) _ (w + 1) (wa (WK + 676 + 4 * (w + 1))) RA
                  ltac:(rewrite length_map, LR; lia) eq_refl) as SOK.
    zstep. if_cases U1; zify_cond U1; [exfalso; lia|].
    zstep. if_cases U2; zify_cond U2; [exfalso; Z.div_mod_to_equations; lia|].
    zstep. zstep. zstep. rewrite byte_lit by lia. rewrite shl2.
    zstep. if_cases U3; zify_cond U3; [exfalso; Z.div_mod_to_equations; lia|].
    zstep. zstep. rewrite sx32_small by lia. zstep.
    zstep.
    pose proof (u32arr_write usegs _ (WK + 676) _ (w + 1) (Z_to_bv 64 (Znth (w + 1) rs0 + 1)) RA
                  ltac:(rewrite length_map, LR; lia)) as RA2.
    clear RA. store_done. rename RA2 into RA.
    zstep. if_cases U4; zify_cond U4; [exfalso; lia|].
    zstep. if_cases U5; zify_cond U5; [exfalso; Z.div_mod_to_equations; lia|].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8arr_store_ok usegs mm (WK + 736) _ (Znth (w + 1) rs0) (wa (WK + 736 + Znth (w + 1) rs0)) SA
                    ltac:(rewrite omerge_length; lia) eq_refl) as SOK2 end.
    zstep. zstep. rewrite le1_lit.
    pose proof (u8arr_write usegs _ (WK + 736) _ (Znth (w + 1) rs0) (Z_to_bv 8 s) SA
                  ltac:(rewrite omerge_length; lia)) as SA2.
    clear SA. store_done. rename SA2 into SA.
    rewrite omerge_store in SA by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into ms end.
    assert (NX : u32 (Znth (w + 1) rs0 + 1) = Znth (w + 1) rs0 + 1) by (unfold u32; rewrite Z.mod_small by lia; lia).
    assert (RA' : u32arr usegs ms (WK + 676) (map (Z_to_bv 64) (Zupd (w + 1) (u32 (Znth (w + 1) rs0 + 1)) rs0)))
      by (rewrite NX; unfold Zupd; rewrite map_upd_nat; exact RA).
    assert (LR' : length (Zupd (w + 1) (u32 (Znth (w + 1) rs0 + 1)) rs0) = 15%nat) by (rewrite Zupd_length; exact LR).
    assert (LS' : length (oupd_nat (Z.to_nat (Znth (w + 1) rs0)) s sorted) = 256%nat)
      by (rewrite oupd_nat_length; exact LS).
    assert (RB' : forall i, 0 <= i < 15 -> 0 <= Znth i (Zupd (w + 1) (u32 (Znth (w + 1) rs0 + 1)) rs0) <= 256).
    { intros i Hi. destruct (Z.eq_dec i (w + 1)) as [->|NE].
      - rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; lia). lia.
      - rewrite Znth_Zupd_other by lia. apply RB. lia. }
    pgo [0x14318; 0x142d8].
    if_cases U6; zify_cond U6.
    - apply (IH (s + 1) (Zupd (w + 1) (u32 (Znth (w + 1) rs0 + 1)) rs0) (oupd_nat (Z.to_nat (Znth (w + 1) rs0)) s sorted) ms r); [exact HF | lia | lia | exact RB' | | exact CONT].
      exact (conj RA' (conj LR' (conj SA (conj LS' (conj MU (conj WM MI)))))).
    - assert (f = O) by lia. subst f. cbn [sort2] in HF. injection HF as HR.
      replace (s + 1) with nbS by lia.
      apply (CONT ms _ _ _ _ _ (eq_sym HR)).
      exact (conj RA' (conj LR' (conj SA (conj LS' (conj MU (conj WM MI)))))).
  Qed.

End SO2.

Section RV0.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).

  Variables (x1 x6 x8 x9 x10 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
  Variables (m : fmem) (WK wEnd rsc : Z) (rank : list Z).
  Variable POST : machine_state -> Prop.
  Hypothesis HWK : 0 < WK /\ WK + 2124 <= 2^47.
  Hypothesis HWE : 2 <= wEnd <= 13.
  Hypothesis HRSC : 0 <= 1 + rsc /\ wEnd - 1 + rsc <= 12.
  Hypothesis LRK : length rank = 13%nat.
  Hypothesis RKR : forall i, 0 <= i < 13 -> 0 <= Znth i rank <= 256.
  Hypothesis RKA0 : u32arr usegs m (WK + 624) (map (Z_to_bv 64) rank).
  Notation VINV m1 rv w := (rv_at m1 WK rv (fun j => 1 <= j < w) /\ length rv = 156%nat
                           /\ munch [(WK, WK + 624)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1).
  Notation ST pc mm x5 x11 x12 x15 x17 :=
    (MS (mkR x1 sp gp tp x5 x6 (Z_to_bv 64 (- WK - 1)) x8 x9 x10 x11 x12 (Z_to_bv 64 (4 * wEnd)) x14 x15
             (Z_to_bv 64 32) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Lemma rv0_loop : forall f w next rv m1 r (x5 : word),
    rank_val0 f w next rsc rank rv = Ok r -> Z.of_nat f = wEnd - w -> 1 <= w < wEnd -> 0 <= next <= 1048576 * (w - 1) ->
    VINV m1 rv w ->
    (forall m2 rv' (y5 y11 y12 y15 y17 : word), r = rv' -> VINV m2 rv' wEnd ->
       evt usegs POST (ST 0x14378 m2 y5 y11 y12 y15 y17)) ->
    evt usegs POST (ST 0x14350 m1 x5 (Z_to_bv 64 (w + rsc)) (Z_to_bv 64 (WK + 624 + 4 * w)) (Z_to_bv 64 (4 * w))
                      (Z_to_bv 64 next)).
  Proof.
    induction f as [|f IH]; intros w next rv m1 r x5 HF Hf Hw Hn INV CONT; [lia|].
    destruct INV as (RV & LV & MU & WM & MI).
    cbn [rank_val0] in HF.
    apply bind_Ok_inv in HF as (c & L1 & HF). apply load_Ok in L1 as (L1 & ->).
    apply bind_Ok_inv in HF as (t & T1 & HF).
    apply bind_Ok_inv in HF as (rv1 & S1 & HF). apply store_Ok in S1 as (S1 & ->).
    unfold rv_idx in HF. replace (0 * 13 + w) with w in HF by lia.
    pose proof (RKR w ltac:(lia)) as RW.
    replace (u32 (w + rsc)) with (w + rsc) in T1 by (unfold u32; rewrite Z.mod_small by lia; reflexivity).
    unfold shl32 in T1.
    replace ((0 <=? w + rsc) && (w + rsc <? 32)) with true in T1
      by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    injection T1 as <-.
    pose proof (u32arr_transport usegs _ m m1 _ _ RKA0 MU WM
                  ltac:(rewrite length_map, LRK; cbn; split; [lia | exact I])) as RK1.
    pose proof (u32arr_read usegs m1 (WK + 624) _ w _ (wa (WK + 624 + 4 * w)) RK1 (nth_map_Znth2 rank w ltac:(lia))
                  ltac:(lia) eq_refl) as RD.
    pose proof RV as (rvw & LW & UA & _).
    pose proof (u32arr_store_ok usegs m1 WK rvw w (wa (WK + 4 * w)) UA ltac:(lia) eq_refl) as SOK.
    clear UA.
    zstep. if_cases U1; zify_cond U1; [exfalso; lia|].
    zstep. if_cases U2; zify_cond U2; [exfalso; Z.div_mod_to_equations; lia|].
    zstep. zstep. rewrite sx32_small by lia.
    pose proof (rv_at_write m1 WK rv _ w next RV ltac:(lia) LV) as RV2.
    clear RV. store_done. rename RV2 into RV.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into ms end.
    assert (PW : 0 < 2 ^ (w + rsc) <= 4096)
      by (split; [apply Z.pow_pos_nonneg; lia | change 4096 with (2 ^ 12); apply Z.pow_le_mono_r; lia]).
    assert (TV : 0 <= Znth w rank * 2 ^ (w + rsc) <= 1048576) by nia.
    assert (SH : bv_swrap 32 (Znth w rank ≪ ((w + rsc) mod 32)) = Znth w rank * 2 ^ (w + rsc)).
    { rewrite (Z.mod_small (w + rsc) 32) by lia. rewrite Z.shiftl_mul_pow2 by lia. apply swrap32_small. lia. }
    assert (UV : u32 (Znth w rank * 2 ^ (w + rsc)) = Znth w rank * 2 ^ (w + rsc)) by (unfold u32; apply Z.mod_small; lia).
    assert (NX : u32 (next + Znth w rank * 2 ^ (w + rsc)) = Znth w rank * 2 ^ (w + rsc) + next)
      by (unfold u32; rewrite Z.mod_small by lia; lia).
    rewrite UV, NX in HF.
    zstep. rewrite SH. zstep. rewrite swrap32_small by lia.
    pgo [0x14378; 0x14350].
    replace (w + rsc + 1) with (w + 1 + rsc) by lia.
    replace (WK + 624 + 4 * w + 4) with (WK + 624 + 4 * (w + 1)) by lia.
    replace (4 * w + 4) with (4 * (w + 1)) by lia.
    assert (RV' : rv_at ms WK (Zupd w next rv) (fun j => 1 <= j < w + 1))
      by (apply (rv_at_weaken _ _ _ _ _ RV); intros j Hj; lia).
    assert (LV' : length (Zupd w next rv) = 156%nat) by (rewrite Zupd_length; exact LV).
    if_cases U3; zify_cond U3.
    - apply (IH (w + 1) _ (Zupd w next rv) ms r); [exact HF | lia | lia | lia | | exact CONT].
      exact (conj RV' (conj LV' (conj MU (conj WM MI)))).
    - assert (f = O) by lia. subst f. cbn [rank_val0] in HF. injection HF as HR.
      apply (CONT ms _ _ _ _ _ _ (eq_sym HR)).
      replace wEnd with (w + 1) by lia.
      exact (conj RV' (conj LV' (conj MU (conj WM MI)))).
  Qed.

End RV0.

Lemma PRw_row : forall wEnd mB c w j, PRw wEnd mB c (w + 1) j -> PRw wEnd mB c w j \/ j = c * 13 + w.
Proof.
  unfold PRw, rv_idx. intros wEnd mB c w j [H | (c' & w' & H1 & H2 & H3)].
  - left. left. lia.
  - destruct H2 as [H2 | (H2 & H4)].
    + left. right. exists c', w'. split; [exact H1|]. split; [left; exact H2 | exact H3].
    + destruct (Z.eq_dec w' w) as [->|NE].
      * right. lia.
      * left. right. exists c', w'. split; [exact H1|]. split; [right; split; [exact H2 | lia] | exact H3].
Qed.

Lemma PRw_next : forall wEnd mB c j, PRw wEnd mB (c + 1) 1 j -> PRw wEnd mB c wEnd j.
Proof.
  unfold PRw. intros wEnd mB c j [H | (c' & w' & H1 & H2 & H3)]; [left; exact H|].
  right. exists c', w'. split; [exact H1|]. split; [|exact H3].
  destruct H2 as [(H2 & H4) | (H2 & H4)]; [|lia].
  destruct (Z.eq_dec c' c); [right; lia | left; lia].
Qed.

Section RVR.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).

  Variables (x1 x9 x10 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word).
  Variables (m : fmem) (WK wEnd mB T : Z).
  Variable POST : machine_state -> Prop.
  Hypothesis HWK : 0 < WK /\ WK + 2124 <= 2^47.
  Hypothesis HWE : 2 <= wEnd <= 13.
  Hypothesis HMB : 1 <= mB /\ T - mB <= 11.
  Notation WINV m1 rv c w := (rv_at m1 WK rv (PRw wEnd mB c w) /\ length rv = 156%nat
                           /\ (forall j, 1 <= j < wEnd -> 0 <= Znth j rv < 2^31)
                           /\ munch [(WK, WK + 624)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1).
  Notation ST pc mm x5 x6 c x15 x16 x17 :=
    (MS (mkR x1 sp gp tp x5 x6 (Z_to_bv 64 (- WK - 1)) (Z_to_bv 64 (wEnd - 1)) x9 x10 (Z_to_bv 64 12) (Z_to_bv 64 52)
             (Z_to_bv 64 c) (Z_to_bv 64 (T - mB + 1)) x15 x16 x17 x18 x19 x20 x21 x22 (Z_to_bv 64 WK) x24 x25 x26 x27 x28
             x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Lemma rvr_inner : forall f c w rv m1 r (x5 x6 : word),
    rank_val_row f c w rv = Ok r -> Z.of_nat f = wEnd - w -> 1 <= w < wEnd -> mB <= c <= T - mB -> WINV m1 rv c w ->
    (forall m2 rv' (y5 y6 : word), r = rv' -> WINV m2 rv' c wEnd ->
       evt usegs POST (ST 0x143dc m2 y5 y6 c (Z_to_bv 64 (WK + 52 * c)) (Z_to_bv 64 (- (WK + 52 * c) - 1))
                         (Z_to_bv 64 wEnd))) ->
    evt usegs POST (ST 0x143a8 m1 x5 x6 c (Z_to_bv 64 (WK + 52 * c)) (Z_to_bv 64 (- (WK + 52 * c) - 1)) (Z_to_bv 64 w)).
  Proof.
    induction f as [|f IH]; intros c w rv m1 r x5 x6 HF Hf Hw Hc INV CONT; [lia|].
    destruct INV as (RV & LV & VB & MU & WM & MI).
    cbn [rank_val_row] in HF.
    apply bind_Ok_inv in HF as (v & L1 & HF). apply load_Ok in L1 as (L1 & ->).
    apply bind_Ok_inv in HF as (u & A1 & HF).
    replace (c <? 12) with true in A1 by (symmetry; apply Z.ltb_lt; lia). clear A1.
    apply bind_Ok_inv in HF as (t & T1 & HF).
    unfold shr32 in T1.
    replace ((0 <=? c) && (c <? 32)) with true in T1
      by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    injection T1 as <-.
    apply bind_Ok_inv in HF as (rv1 & S1 & HF). apply store_Ok in S1 as (S1 & ->).
    unfold rv_idx in HF, L1. replace (0 * 13 + w) with w in HF, L1 by lia.
    pose proof (VB w ltac:(lia)) as VW.
    pose proof (rv_at_read m1 WK rv _ w (wa (WK + 4 * w)) RV ltac:(left; lia) ltac:(lia) eq_refl) as RD.
    pose proof RV as (rvw & LW & UA & _).
    pose proof (u32arr_store_ok usegs m1 WK rvw (c * 13 + w) (wa (WK + 4 * (c * 13 + w))) UA ltac:(lia) eq_refl) as SOK.
    clear UA.
    zstep. zstep. rewrite sl32_sr30 by lia.
    zstep. if_cases U1; zify_cond U1; [exfalso; Z.div_mod_to_equations; lia|].
    zstep. if_cases U2; zify_cond U2; [exfalso; Z.div_mod_to_equations; lia|].
    zstep. rewrite (Z.mod_small w 4294967296) by lia. zstep. rewrite shl2.
    zstep. zstep. rewrite sx32_small by lia. zstep. zstep.
    assert (PC : 0 < 2 ^ c) by (apply Z.pow_pos_nonneg; lia).
    assert (DV : 0 <= Znth w rv / 2 ^ c <= Znth w rv)
      by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; nia]).
    assert (SV : bv_swrap 32 (bv_wrap 32 (Znth w rv) ≫ (c mod 32)) = Znth w rv / 2 ^ c).
    { assert (BM : bv_modulus 32 = 4294967296) by reflexivity.
      unfold bv_wrap. rewrite BM. rewrite (Z.mod_small (Znth w rv)) by lia. rewrite (Z.mod_small c 32) by lia.
      rewrite Z.shiftr_div_pow2 by lia. apply swrap32_small. lia. }
    rewrite SV.
    zstep. rewrite swrap32_small by lia.
    replace (WK + 52 * c + 4 * w) with (WK + 4 * (c * 13 + w)) by lia.
    zstep.
    pose proof (rv_at_write m1 WK rv _ (c * 13 + w) (Znth w rv / 2 ^ c) RV ltac:(lia) LV) as RV2.
    clear RV. store_done. rename RV2 into RV.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into ms end.
    pgo [0x143dc; 0x143a8].
    assert (LV' : length (Zupd (c * 13 + w) (Znth w rv / 2 ^ c) rv) = 156%nat) by (rewrite Zupd_length; exact LV).
    assert (VB' : forall j, 1 <= j < wEnd -> 0 <= Znth j (Zupd (c * 13 + w) (Znth w rv / 2 ^ c) rv) < 2^31)
      by (intros j Hj; rewrite Znth_Zupd_other by lia; apply VB; lia).
    if_cases U3; zify_cond U3.
    - assert (RV' : rv_at ms WK (Zupd (c * 13 + w) (Znth w rv / 2 ^ c) rv) (PRw wEnd mB c (w + 1)))
        by (apply (rv_at_weaken _ _ _ _ _ RV); intros j Hj; exact (PRw_row _ _ _ _ _ Hj)).
      apply (IH c (w + 1) (Zupd (c * 13 + w) (Znth w rv / 2 ^ c) rv) ms r); [exact HF | lia | lia | lia | | exact CONT].
      exact (conj RV' (conj LV' (conj VB' (conj MU (conj WM MI))))).
    - assert (RV' : rv_at ms WK (Zupd (c * 13 + w) (Znth w rv / 2 ^ c) rv) (PRw wEnd mB c wEnd)).
      { apply (rv_at_weaken _ _ _ _ _ RV); intros j Hj. apply PRw_row. replace (w + 1) with wEnd by lia. exact Hj. }
      assert (f = O) by lia. subst f. cbn [rank_val_row] in HF. injection HF as HR.
      replace (w + 1) with wEnd by lia.
      apply (CONT ms _ _ _ (eq_sym HR)).
      exact (conj RV' (conj LV' (conj VB' (conj MU (conj WM MI))))).
  Qed.

  Lemma rvr_outer : forall f c rv m1 r (x5 x6 x15 x16 x17 : word),
    rank_val_rows f c (wEnd - 1) rv = Ok r -> Z.of_nat f = T - mB + 1 - c -> mB <= c < T - mB + 1 -> WINV m1 rv c 1 ->
    (forall m2 rv' (y5 y6 y15 y16 y17 : word), r = rv' -> WINV m2 rv' (T - mB + 1) 1 ->
       evt usegs POST (ST 0x14434 m2 y5 y6 (T - mB + 1) y15 y16 y17)) ->
    evt usegs POST (ST 0x14390 m1 x5 x6 c x15 x16 x17).
  Proof.
    induction f as [|f IH]; intros c rv m1 r x5 x6 x15 x16 x17 HF Hf Hc INV CONT; [lia|].
    cbn [rank_val_rows] in HF.
    apply bind_Ok_inv in HF as (rv1 & HR1 & HF).
    zstep. if_cases U1; zify_cond U1; [exfalso; lia|].
    zstep. zstep. if_cases U2; zify_cond U2; [exfalso; Z.div_mod_to_equations; lia|].
    zstep. zstep. zstep.
    rewrite zb_lxor_ones by lia.
    lazymatch goal with |- context [Z_to_bv 64 (?K - (WK + c * 52))] =>
      replace (Z_to_bv 64 (K - (WK + c * 52))) with (Z_to_bv 64 (- (WK + 52 * c) - 1))
        by (apply Z_to_bv_eqm; Z.div_mod_to_equations; lia) end.
    replace (WK + c * 52) with (WK + 52 * c) by lia.
    apply (rvr_inner (Z.to_nat (wEnd - 1)) c 1 rv m1 rv1); [exact HR1 | lia | lia | lia | exact INV |].
    intros m2 rv' y5 y6 E INV2. subst rv'.
    destruct INV2 as (RV2 & L2 & V2 & MU2 & WM2 & MI2).
    zstep. rewrite swrap32_small by lia.
    pgo [0x14390; 0x14434].
    if_cases U3; zify_cond U3.
    - apply (IH (c + 1) rv1 m2 r); [exact HF | lia | lia | | exact CONT].
      refine (conj (rv_at_weaken _ _ _ _ _ RV2 _) (conj L2 (conj V2 (conj MU2 (conj WM2 MI2))))).
      intros j Hj. exact (PRw_next _ _ _ _ Hj).
    - assert (f = O) by lia. subst f. cbn [rank_val_rows] in HF. injection HF as HR.
      zstep.
      replace (c + 1) with (T - mB + 1) by lia.
      apply (CONT m2 rv1 _ _ _ _ _ (eq_sym HR)).
      refine (conj (rv_at_weaken _ _ _ _ _ RV2 _) (conj L2 (conj V2 (conj MU2 (conj WM2 MI2))))).
      intros j Hj. apply PRw_next. replace (c + 1) with (T - mB + 1) by lia. exact Hj.
  Qed.

End RVR.
