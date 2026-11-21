(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import Prog ZIface InflateState Inftrees ModelRel InftreesCoverage.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ItCovBits ItCovPre ItCovMath ItCovStep ItCovLoop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Main.
  Variables (ty : codetype) (lens : arr) (lens_ofs codes : Z) (tbl : arr) (table bits : Z) (work : arr).
  Hypothesis Hcodes : 0 <= codes <= 288.
  Hypothesis Hlens : forall s, 0 <= s < codes -> 0 <= arr_get lens (lens_ofs + s) <= 15.
  Hypothesis HtyC : ty = CODES -> codes <= 19 /\ bits = 7 /\ forall s, 0 <= s < codes -> arr_get lens (lens_ofs + s) <= 7.
  Hypothesis HtyD : ty = DISTS -> codes <= 32.
  Hypothesis Hbits : 1 <= bits <= 15.
  Hypothesis Htable : 0 <= table.
  Hypothesis Hroom : table + it_room ty <= arr_len tbl.
  Hypothesis Hwork : codes <= arr_len work.

  Local Notation Nn := (N lens lens_ofs codes).
  Local Notation Wl := (W lens lens_ofs codes).
  Local Notation mx := (max lens lens_ofs codes).
  Local Notation mn := (min lens lens_ofs codes).
  Local Notation Lg := (Lf lens lens_ofs codes).
  Local Notation cntf := (cnt lens lens_ofs codes).
  Local Notation countA := (count lens lens_ofs codes).
  Local Notation offsA := (offs lens lens_ofs codes).
  Local Notation kr := (kraft lens lens_ofs codes 15).
  Local Notation root := (itm_root bits mx mn).
  Local Notation work1 := (snd (it_sort lens lens_ofs codes (offsA, work))).
  Local Notation INV := (code_pack 64 1 0).

  Lemma HtyC19 : ty = CODES -> codes <= 19.
  Proof. intros E. exact (proj1 (HtyC E)). Qed.

  Lemma phases :
    inflate_table ty lens lens_ofs codes tbl table bits work =
    if mx =? 0 then (0, arr_set (arr_set tbl table INV) (table + 1) INV, table + 2, 1, work)
    else if itm_reject ty mx (it_left_check countA) then (-1, tbl, table, bits, work)
    else if it_not_enough ty (itm_used root) then (1, tbl, table, bits, work1)
    else match it_loop (itm_ctx ty lens lens_ofs table root mx) codes (itm_st0 mn table root countA tbl work1) with
         | inr st => (1, t_tbl st, table, bits, t_work st)
         | inl st => (0, (if negb (t_huff st =? 0)
                          then arr_set (t_tbl st) (t_next st + t_huff st) (code_pack 64 (t_len st - t_drop st) 0)
                          else t_tbl st), table + t_used st, root, t_work st)
         end.
  Proof. rewrite inflate_table_phases. reflexivity. Qed.

  Lemma room2 : table + 2 <= arr_len tbl.
  Proof. pose proof Hroom as HR. clear - HR. destruct ty; cbn [it_room] in HR; unfold ENOUGH_LENS, ENOUGH_DISTS in *; lia. Qed.

  Lemma left_eq : it_left_check countA = if 2 ^ 15 <? kr then None else Some (2 ^ 15 - kr).
  Proof. apply (left_check_spec lens lens_ofs codes Hcodes Hlens). Qed.


  Theorem it_empty : mx = 0 ->
    inflate_table ty lens lens_ofs codes tbl table bits work = (0, arr_set (arr_set tbl table INV) (table + 1) INV, table + 2, 1, work).
  Proof. intros E. rewrite phases, E. reflexivity. Qed.

  Theorem it_over : mx <> 0 -> 2 ^ 15 < kr ->
    inflate_table ty lens lens_ofs codes tbl table bits work = (-1, tbl, table, bits, work).
  Proof.
    intros E K. rewrite phases. replace (mx =? 0) with false by (symmetry; apply Z.eqb_neq; exact E).
    rewrite left_eq. replace (2 ^ 15 <? kr) with true by (symmetry; apply Z.ltb_lt; exact K). reflexivity.
  Qed.

  Theorem it_incomp : mx <> 0 -> kr < 2 ^ 15 -> (ty = CODES \/ mx <> 1) ->
    inflate_table ty lens lens_ofs codes tbl table bits work = (-1, tbl, table, bits, work).
  Proof.
    intros E K C. rewrite phases. replace (mx =? 0) with false by (symmetry; apply Z.eqb_neq; exact E).
    rewrite left_eq. replace (2 ^ 15 <? kr) with false by (symmetry; apply Z.ltb_ge; lia).
    unfold itm_reject. replace (0 <? 2 ^ 15 - kr) with true by (symmetry; apply Z.ltb_lt; lia).
    destruct C as [->|C]; [reflexivity|]. replace (mx =? 1) with false by (symmetry; apply Z.eqb_neq; exact C).
    rewrite Bool.orb_true_r. reflexivity.
  Qed.

  Lemma noreject : mx <> 0 -> kr <= 2 ^ 15 -> (kr = 2 ^ 15 \/ (ty <> CODES /\ mx = 1)) ->
    itm_reject ty mx (it_left_check countA) = false.
  Proof.
    intros E K C. rewrite left_eq. replace (2 ^ 15 <? kr) with false by (symmetry; apply Z.ltb_ge; lia).
    unfold itm_reject. destruct C as [C|[C1 C2]].
    - rewrite C. reflexivity.
    - rewrite C2. destruct ty; [exfalso; exact (C1 eq_refl)| |]; cbn; rewrite Bool.andb_false_r; reflexivity.
  Qed.


  Local Notation NFq := (NF ty lens lens_ofs codes root).
  Local Notation LWq := (LW ty lens lens_ofs codes root table).
  Local Notation UPDq := (UPD ty lens lens_ofs codes root table).
  Local Notation usFq := (usF lens lens_ofs codes root).
  Local Notation WKq := (WK ty lens lens_ofs codes root table).

  Section Complete.
    Hypothesis Hmx : mx <> 0.
    Hypothesis Hcomplete : kr = 2 ^ 15.

    Lemma Hmax1 : 1 <= mx.
    Proof. pose proof (max_spec lens lens_ofs codes Hcodes Hlens) as (A & _ & _). lia. Qed.

    Lemma root_range : mn <= root <= 15 /\ 1 <= root <= mx /\ (mn <= bits -> root <= bits).
    Proof.
      pose proof (max_spec lens lens_ofs codes Hcodes Hlens) as (A & _ & _).
      pose proof (min_spec lens lens_ofs codes Hcodes Hlens Hmax1) as (B & _ & _).
      unfold itm_root. destruct (Z.ltb_spec mx bits); [destruct (Z.ltb_spec mx mn)|destruct (Z.ltb_spec bits mn)]; lia.
    Qed.
    Lemma Hroot : mn <= root <= 15.  Proof. exact (proj1 root_range). Qed.

    Lemma used_eq : itm_used root = 2 ^ root.
    Proof. apply itm_used_pow2. pose proof root_range. lia. Qed.

    Lemma codes_short : ty = CODES -> m Nn Lg root = Nn /\ 2 ^ root <= 128.
    Proof.
      intros E. destruct (HtyC E) as (C1 & C2 & C3).
      pose proof (max_spec lens lens_ofs codes Hcodes Hlens) as (A & B & _).
      assert (M7 : mx <= 7).
      { destruct B as [B|B]; [lia|]. destruct (Z_lt_le_dec 7 mx); [|lia]. exfalso. apply B.
        unfold cnt, cntk. rewrite (sumZ_ext _ (fun _ => 0) 0 codes); [apply sumZ_zero|].
        intros j Hj. cbv beta. pose proof (C3 j Hj). unfold L. destruct (Z.eqb_spec (arr_get lens (lens_ofs + j)) mx); [lia|reflexivity]. }
      pose proof root_range as (R1 & R2 & R3).
      split.
      - destruct (m_spec Nn Lg root (CN lens lens_ofs codes Hcodes Hlens Hmax1) (CS lens lens_ofs codes Hcodes)
                  (CRm lens lens_ofs codes Hcodes Hlens Hmax1 root Hroot)) as (X & Y & Zz).
        destruct (Z.eq_dec (m Nn Lg root) Nn); [assumption|]. exfalso.
        pose proof (Zz (m Nn Lg root) ltac:(lia)).
        pose proof (Lf_sorted lens lens_ofs codes Hcodes (m Nn Lg root) (Nn - 1) ltac:(lia) ltac:(lia)).
        rewrite (Lf_last lens lens_ofs codes Hcodes Hlens Hmax1) in H0.
        pose proof (min_spec lens lens_ofs codes Hcodes Hlens Hmax1) as (Bm & _ & _).
        unfold itm_root in *. destruct (Z.ltb_spec mx bits); [destruct (Z.ltb_spec mx mn)|destruct (Z.ltb_spec bits mn)]; lia.
      - change 128 with (2 ^ 7). apply Z.pow_le_mono_r; lia.
    Qed.

    Lemma fits : forall j, 0 <= j < Nn -> it_not_enough ty (us lens lens_ofs codes root j) = false ->
      table + us lens lens_ofs codes root j <= arr_len tbl.
    Proof.
      intros j Hj H. pose proof codes_short as CSH. pose proof Hroom as HR. unfold it_room in HR.
      clear HtyC HtyD Hroom. destruct ty.
      - destruct (CSH eq_refl) as [M R]. unfold us. replace (j <? m Nn Lg root) with true by (symmetry; apply Z.ltb_lt; lia). lia.
      - unfold it_not_enough in H. apply Z.ltb_ge in H. lia.
      - unfold it_not_enough in H. apply Z.ltb_ge in H. lia.
    Qed.

    Theorem it_big : it_not_enough ty (2 ^ root) = true ->
      inflate_table ty lens lens_ofs codes tbl table bits work = (1, tbl, table, bits, work1).
    Proof.
      intros H. rewrite phases. replace (mx =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hmx).
      rewrite (noreject Hmx ltac:(lia) ltac:(left; exact Hcomplete)). rewrite used_eq, H. reflexivity.
    Qed.

    Lemma fits_room : forall j, 0 <= j < Nn -> it_not_enough ty (us lens lens_ofs codes root j) = false ->
      2 ^ root <= us lens lens_ofs codes root j <= it_room ty.
    Proof.
      intros j Hj H.
      pose proof (phase_facts lens lens_ofs codes Hcodes Hlens Hmax1 Hcomplete root Hroot table j Hj) as (_ & _ & _ & _ & F1 & _).
      split; [exact F1|].
      pose proof codes_short as CSH. clear HtyC HtyD Hroom. destruct ty.
      - destruct (CSH eq_refl) as [M R]. unfold us. replace (j <? m Nn Lg root) with true by (symmetry; apply Z.ltb_lt; lia). cbn [it_room]. lia.
      - unfold it_not_enough in H. apply Z.ltb_ge in H. cbn [it_room]. lia.
      - unfold it_not_enough in H. apply Z.ltb_ge in H. cbn [it_room]. lia.
    Qed.

    Section Fits.
      Hypothesis Hroot_fits : it_not_enough ty (2 ^ root) = false.

      Lemma IS0' : IS ty lens lens_ofs codes root table 0 (itm_st0 mn table root countA tbl work1).
      Proof.
        unfold itm_st0. rewrite used_eq.
        apply (IS0 ty lens lens_ofs codes Hcodes Hlens Hmax1 root Hroot table Hroot_fits tbl work).
        pose proof (N_range lens lens_ofs codes Hcodes Hlens). lia.
      Qed.

      Lemma ctx_eq : itm_ctx ty lens lens_ofs table root mx = mkItCtx ty lens lens_ofs table root mx (2 ^ root - 1).
      Proof. unfold itm_ctx. rewrite used_eq. reflexivity. Qed.

      Theorem it_fail : (exists k, 0 < k < Nn /\ NFq k = true) ->
        let r := inflate_table ty lens lens_ofs codes tbl table bits work in
        fst (fst (fst (fst r))) = 1 /\ snd (fst (fst r)) = table /\ snd (fst r) = bits
        /\ arr_len (snd r) = arr_len work /\ (forall i, 0 <= i < Nn -> arr_get (snd r) i = znth 0 Wl i)
        /\ (forall i, Nn <= i -> arr_get (snd r) i = arr_get work i).
      Proof.
        intros HF. cbv zeta. rewrite phases. replace (mx =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hmx).
        rewrite (noreject Hmx ltac:(lia) ltac:(left; exact Hcomplete)). rewrite used_eq, Hroot_fits.
        set (kf := findZ (fun k => NFq k) 1 Nn).
        destruct (findZ_spec (fun k => NFq k) 1 Nn ltac:(destruct HF as (k & Hk & _); lia)) as (R & P & Q). fold kf in R, P, Q.
        assert (HkN : kf < Nn).
        { destruct HF as (k & Hk & E). destruct (Z_lt_le_dec k kf); [|lia]. pose proof (Q k ltac:(lia)). rewrite E in H. discriminate. }
        pose proof (N_range lens lens_ofs codes Hcodes Hlens) as NR.
        rewrite it_loop_is_n, ctx_eq. replace (codes + 1) with (Z.of_nat (Z.to_nat (codes + 1))) by lia.
        destruct (loop_fail ty lens lens_ofs codes Hcodes Hlens Hmax1 Hcomplete root Hroot table HtyC19 (Z.to_nat (codes + 1)) 0 _ kf
                    ltac:(lia) HkN IS0' ltac:(lia) (P HkN) ltac:(intros k' Hk'; apply Q; lia)) as (stF & E & Fw).
        rewrite E. cbn [fst snd]. rewrite Fw. cbn [t_work itm_st0].
        destruct (sort_spec lens lens_ofs codes Hcodes Hlens work ltac:(lia)) as (L1 & L2 & L3).
        repeat split; try reflexivity; assumption.
      Qed.

      Theorem it_ok : (forall k, 0 < k < Nn -> NFq k = false) ->
        let r := inflate_table ty lens lens_ofs codes tbl table bits work in
        fst (fst (fst (fst r))) = 0 /\ snd (fst (fst r)) = table + usFq /\ snd (fst r) = root
        /\ arr_len (snd (fst (fst (fst r)))) = arr_len tbl
        /\ (forall i, arr_get (snd (fst (fst (fst r)))) i = match LWq (Z.to_nat Nn) 0 i with Some v => v | None => arr_get tbl i end)
        /\ arr_len (snd r) = arr_len work /\ (forall i, 0 <= i < Nn -> arr_get (snd r) i = znth 0 Wl i)
        /\ (forall i, Nn <= i -> arr_get (snd r) i = arr_get work i)
        /\ 2 ^ root <= usFq <= it_room ty /\ 1 <= root <= 15 /\ (mn <= bits -> root <= bits).
      Proof.
        intros HNF. cbv zeta. rewrite phases. replace (mx =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hmx).
        rewrite (noreject Hmx ltac:(lia) ltac:(left; exact Hcomplete)). rewrite used_eq, Hroot_fits.
        pose proof (N_range lens lens_ofs codes Hcodes Hlens) as NR.
        pose proof (CN lens lens_ofs codes Hcodes Hlens Hmax1) as N1.
        pose proof root_range as (RR1 & RR2 & RR3).
        pose proof (fits_room (Nn - 1) ltac:(lia)
          (us_fits_all ty lens lens_ofs codes Hcodes Hlens Hmax1 Hcomplete root Hroot Hroot_fits HNF (Nn - 1) ltac:(lia))) as FR0.
        assert (FR : 2 ^ root <= usFq <= it_room ty) by (unfold usF; exact FR0). clear FR0.
        rewrite it_loop_is_n, ctx_eq. replace (codes + 1) with (Z.of_nat (Z.to_nat (codes + 1))) by lia.
        destruct (loop_ok ty lens lens_ofs codes Hcodes Hlens Hmax1 Hcomplete root Hroot table HtyC19 (Z.to_nat (codes + 1)) 0 _
                    ltac:(lia) IS0' ltac:(lia) HNF) as (stF & E & F).
        rewrite E.
        destruct F as (Ft & Fw & Fh & Fnx & Fus & Fdr & Flen & Fcu).
        rewrite Fh. cbn [Z.eqb negb fst snd]. rewrite Fus, Fw, Ft. cbn [t_work t_tbl itm_st0].
        destruct (sort_spec lens lens_ofs codes Hcodes Hlens work ltac:(lia)) as (L1 & L2 & L3).
        assert (Hinb : table + usFq <= arr_len tbl).
        { unfold usF. apply fits; [lia|].
          apply (us_fits_all ty lens lens_ofs codes Hcodes Hlens Hmax1 Hcomplete root Hroot Hroot_fits HNF (Nn - 1)). lia. }
        replace (Nn - 0) with Nn by lia.
        destruct (UPD_spec ty lens lens_ofs codes Hcodes Hlens Hmax1 Hcomplete root Hroot table Htable (arr_len tbl) Hinb
                    (Z.to_nat Nn) 0 tbl 0 ltac:(lia) ltac:(lia) eq_refl) as [UL _].
        split; [reflexivity|]. split; [unfold usF; reflexivity|]. split; [reflexivity|]. split; [exact UL|].
        split; [| split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact FR|]; split; [lia| exact RR3]].
        intros i. apply (proj2 (UPD_spec ty lens lens_ofs codes Hcodes Hlens Hmax1 Hcomplete root Hroot table Htable (arr_len tbl) Hinb
                    (Z.to_nat Nn) 0 tbl i ltac:(lia) ltac:(lia) eq_refl)).
      Qed.
    End Fits.
  End Complete.


  Section Single.
    Hypothesis Hmx1 : mx = 1.
    Hypothesis Hkr : kr < 2 ^ 15.
    Hypothesis Hty : ty <> CODES.

    Lemma single_facts : cntf 1 = 1 /\ Nn = 1 /\ mn = 1 /\ root = 1
      /\ 0 <= znth 0 Wl 0 < codes /\ L lens lens_ofs (znth 0 Wl 0) = 1.
    Proof.
      pose proof (max_spec lens lens_ofs codes Hcodes Hlens) as (A & B & C). rewrite Hmx1 in B, C.
      assert (Z0 : forall l, 2 <= l <= 15 -> cntf l = 0) by (intros l Hl; apply C; lia).
      assert (K : kr = cntf 1 * 2 ^ 14).
      { unfold kraft. rewrite (sumZ_split _ 1 2 16) by lia.
        rewrite (sumZ_ext _ (fun _ => 0) 2 16) by (intros l Hl; cbv beta; rewrite Z0 by lia; lia).
        rewrite sumZ_zero. rewrite (sumZ_snoc _ 1 1), sumZ_nil by lia. cbv beta. change (2 ^ (15 - 1)) with (2 ^ 14). lia. }
      assert (C1 : cntf 1 = 1).
      { destruct B as [B|B]; [lia|]. pose proof (cnt_range lens lens_ofs codes Hcodes 1).
        change (2 ^ 15) with (2 * 2 ^ 14) in Hkr. rewrite K in Hkr. nia. }
      assert (N1 : Nn = 1).
      { unfold N. rewrite (sumZ_split _ 1 2 16) by lia. rewrite (sumZ_ext _ (fun _ => 0) 2 16) by (intros l Hl; apply Z0; lia).
        rewrite sumZ_zero, (sumZ_snoc _ 1 1), sumZ_nil by lia. lia. }
      pose proof (min_spec lens lens_ofs codes Hcodes Hlens ltac:(lia)) as (M & _ & _). rewrite Hmx1 in M.
      assert (MN : mn = 1) by lia.
      assert (R : root = 1) by (unfold itm_root; rewrite Hmx1, MN; destruct (Z.ltb_spec 1 bits); [reflexivity|]; destruct (Z.ltb_spec bits 1); lia).
      pose proof (W_spec lens lens_ofs codes Hcodes 0 ltac:(lia)) as [W1 W2].
      pose proof (Lf_first lens lens_ofs codes Hcodes Hlens ltac:(lia)) as LF. unfold Lf in LF. rewrite MN in LF.
      repeat split; try lia.
    Qed.

    Theorem it_single :
      let r := inflate_table ty lens lens_ofs codes tbl table bits work in
      let w := znth 0 Wl 0 in
      fst (fst (fst (fst r))) = 0 /\ snd (fst (fst r)) = table + 2 /\ snd (fst r) = 1
      /\ arr_len (snd (fst (fst (fst r)))) = arr_len tbl
      /\ (forall i, arr_get (snd (fst (fst (fst r)))) i =
            if i =? table + 1 then code_pack 64 1 0
            else if i =? table then code_pack (ent_op ty w) 1 (ent_val ty w) else arr_get tbl i)
      /\ arr_len (snd r) = arr_len work /\ arr_get (snd r) 0 = w
      /\ (forall i, Nn <= i -> arr_get (snd r) i = arr_get work i).
    Proof.
      destruct single_facts as (C1 & N1 & MN & R & Wr & WL). cbv zeta.
      rewrite phases. rewrite (noreject ltac:(lia) ltac:(lia) ltac:(right; split; [exact Hty | exact Hmx1])).
      rewrite R. rewrite Hmx1, MN. cbn [Z.eqb]. change (itm_used 1) with 2.
      assert (NE2 : it_not_enough ty 2 = false) by (destruct ty; reflexivity). rewrite NE2.
      destruct (sort_spec lens lens_ofs codes Hcodes Hlens work ltac:(lia)) as (L1 & L2 & L3).
      pose proof (L2 0 ltac:(lia)) as W0.
      rewrite it_loop_is_n, it_loop_n_step by lia.
      unfold itm_ctx, itm_st0. change (itm_used 1) with 2. change (2 - 1) with 1.
      cbv beta iota zeta delta [it_step t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_min t_count t_tbl t_work
                                x_ty x_lens x_lens_ofs x_table x_root x_max x_mask].
      rewrite (ent_pair ty lens lens_ofs codes Hcodes HtyC19 work1 0 ltac:(lia) L2). cbv beta iota.
      set (here_op := ent_op ty (znth 0 Wl 0)). set (here_val := ent_val ty (znth 0 Wl 0)). clearbody here_op here_val.
      change (wrap8 (1 - 0)) with 1. change (shl32 1 (1 - 0)) with 2. change (shl32 1 1) with 2.
      rewrite (it_huff_next_eq' 0 1) by lia.
      replace (it_rev_incr 0 1) with 1 by (symmetry; change 0 with (brv (Z.to_nat 1) 0) at 1; rewrite (it_rev_incr_succZ 1 0) by lia; reflexivity).
      rewrite (count_spec lens lens_ofs codes Hcodes Hlens 1) by lia. rewrite C1.
      change (wrap16 (1 - 1)) with 0. change (wrap32 (0 + 1)) with 1.
      change (0 =? 0) with true. change (1 =? 1) with true. cbn [andb negb].
      cbn [t_huff t_tbl t_next t_len t_drop t_used t_work fst snd]. change (1 =? 0) with false. cbn [negb].
      change (2 ^ 1) with 2 in *.
      destruct (it_fill_spec (code_pack here_op 1 here_val) 1 1 0 0 table tbl ltac:(lia) ltac:(lia)) as [FL FG].
      change (2 ^ 1) with 2 in FL, FG. change (2 ^ (1 - 1)) with 1 in FG. rewrite Z.shiftr_0_r, Z.add_0_r in FG.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [rewrite arr_len_set; exact FL|].
      split.
      - intros i. pose proof room2 as R2.
        destruct (Z.eqb_spec i (table + 1)) as [->|NE].
        + apply arr_get_set_same. rewrite FL. lia.
        + rewrite arr_get_set_other by (intros X; apply NE; symmetry; exact X). rewrite FG.
          unfold fill_hits, arr_inb.
          destruct (Z.eqb_spec i table) as [->|NE3].
          * rewrite Z.sub_diag, Z.mod_0_l by lia. cbn [Z.eqb].
            replace (table <=? table) with true by (symmetry; apply Z.leb_le; lia).
            replace (table <? table + 1 * 2) with true by (symmetry; apply Z.ltb_lt; lia).
            replace (0 <=? table) with true by (symmetry; apply Z.leb_le; lia).
            replace (table <? arr_len tbl) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
          * destruct (Z.leb_spec table i); cbn [andb]; [|reflexivity].
            destruct (Z.ltb_spec i (table + 1 * 2)); cbn [andb]; [|reflexivity].
            exfalso. lia.
      - split; [exact L1|]. split; [exact W0|]. exact L3.
    Qed.
  End Single.


  Section Safe.
    Hypothesis HWN : arr_len work <= 65536.
    Hypothesis Hofs : 0 <= lens_ofs.
    Hypothesis HLN : lens_ofs + codes <= arr_len lens.

    Lemma cntk_mono : forall k k' l, 0 <= k <= k' -> cntk lens lens_ofs k l <= cntk lens lens_ofs k' l.
    Proof.
      intros k k' l [Hk Hkk]. remember (Z.to_nat (k' - k)) as n eqn:Hn. replace k' with (k + Z.of_nat n) by lia. clear k' Hkk Hn.
      induction n as [|n IH]; [rewrite Z.add_0_r; lia|].
      replace (k + Z.of_nat (S n)) with (k + Z.of_nat n + 1) by lia. rewrite cntk_step by lia.
      destruct (_ =? l); lia.
    Qed.

    Lemma sort_ok_true : it_sort_ok lens lens_ofs codes offsA (arr_len work) = true.
    Proof.
      rewrite it_sort_ok_eq. pose proof (N_range lens lens_ofs codes Hcodes Hlens) as NR.
      assert (GEN : forall n, Z.of_nat n <= codes ->
        itm_sort_ok_k lens lens_ofs (Z.of_nat n) offsA (arr_len work) = (fst (itm_sort_k lens lens_ofs (Z.of_nat n) offsA work), true)).
      { induction n as [|n IH]; intros Hn.
        - unfold itm_sort_ok_k, itm_sort_k. rewrite !forZ_nil by lia. reflexivity.
        - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia. rewrite itm_sort_ok_k_step, itm_sort_k_step by lia.
          rewrite (IH ltac:(lia)).
          destruct (sort_k_spec lens lens_ofs codes Hcodes Hlens work (Z.of_nat n) ltac:(lia) ltac:(lia)) as (A & B & _).
          destruct (itm_sort_k lens lens_ofs (Z.of_nat n) offsA work) as [o w] eqn:E. cbn [fst] in A, B |- *.
          unfold sort_ok_body, sort_body.
          pose proof (Hlens (Z.of_nat n) ltac:(lia)) as HL.
          destruct (Z.eqb_spec (arr_get lens (lens_ofs + Z.of_nat n)) 0) as [Z0|NZ]; cbn [negb]; [reflexivity|]. cbn [fst].
          set (l := arr_get lens (lens_ofs + Z.of_nat n)) in *.
          rewrite B by lia.
          pose proof (coff_range lens lens_ofs codes Hcodes l ltac:(lia)).
          pose proof (cntk_range lens lens_ofs (Z.of_nat n) l ltac:(lia)).
          pose proof (cntk_step lens lens_ofs (Z.of_nat n) l ltac:(lia)) as ST. unfold L in ST. fold l in ST. rewrite Z.eqb_refl in ST.
          pose proof (cntk_mono (Z.of_nat n + 1) codes l ltac:(lia)) as MO. change (cntk lens lens_ofs codes l) with (cntf l) in MO.
          pose proof (coff_step lens lens_ofs codes l ltac:(lia)) as CS'. pose proof (coff_mono lens lens_ofs codes Hcodes (l + 1) 16 ltac:(lia)) as CM.
          rewrite (coff_16 lens lens_ofs codes) in CM.
          f_equal. rewrite andb_true_l. apply andb_true_intro; split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
      pose proof (GEN (Z.to_nat codes) ltac:(lia)) as G. rewrite Z2Nat.id in G by lia. rewrite G. reflexivity.
    Qed.

    Theorem it_safe_true : it_safe ty lens lens_ofs codes tbl table bits work = true.
    Proof.
      pose proof (max_spec lens lens_ofs codes Hcodes Hlens) as (A & B & C). pose proof room2 as R2.
      pose proof (N_range lens lens_ofs codes Hcodes Hlens) as NR.
      unfold it_safe. cbv zeta.
      change (itm_count lens lens_ofs codes) with countA. change (itm_max countA) with mx.
      change (itm_min countA mx) with mn. change (itm_offs countA) with offsA.
      replace ((0 <=? codes) && (codes <=? arr_len work) && (arr_len work <=? 65536)) with true
        by (symmetry; repeat (apply andb_true_intro; split); [apply Z.leb_le | apply Z.leb_le | apply Z.leb_le]; lia).
      rewrite andb_true_l.
      destruct (Z.eqb_spec mx 0) as [E0|E0].
      { apply andb_true_intro; split; apply Z.leb_le; lia. }
      rewrite left_eq. destruct (Z.ltb_spec (2 ^ 15) kr) as [K|K]; [reflexivity|].
      unfold itm_reject.
      destruct (Z.ltb_spec 0 (2 ^ 15 - kr)) as [K2|K2].
      -
        destruct (codetype_eqb ty CODES || negb (mx =? 1)) eqn:E; [reflexivity|].
        apply Bool.orb_false_iff in E. destruct E as [E1 E2]. apply negb_false_iff in E2. apply Z.eqb_eq in E2.
        assert (Hty : ty <> CODES) by (intros X; rewrite X in E1; discriminate).
        destruct (single_facts E2 ltac:(lia)) as (C1 & N1 & MN & R & Wr & WL).
        rewrite sort_ok_true, andb_true_l. rewrite R. change (itm_used 1) with 2.
        assert (NE2 : it_not_enough ty 2 = false) by (destruct ty; reflexivity). rewrite NE2.
        replace ((0 <=? table) && (table + 2 <=? arr_len tbl)) with true by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
        rewrite andb_true_l.
        replace (Z.to_nat (codes + 1)) with (S (Z.to_nat codes)) by lia. rewrite it_loop_ok_S.
        destruct (sort_spec lens lens_ofs codes Hcodes Hlens work ltac:(lia)) as (L1 & L2 & L3).
        pose proof (L2 0 ltac:(lia)) as W0.
        unfold itm_ctx, itm_st0, itm_work. change (itm_used 1) with 2. change (2 - 1) with 1.
        unfold it_trip_ok. cbn [t_sym t_len t_huff t_count t_work t_drop t_curr t_next t_used t_low t_min x_ty x_lens x_lens_ofs x_table x_max].
        cbv beta iota zeta delta [it_step t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_min t_count t_tbl t_work
                                  x_ty x_lens x_lens_ofs x_table x_root x_max x_mask].
        rewrite (ent_pair ty lens lens_ofs codes Hcodes HtyC19 work1 0 ltac:(lia) L2). cbv beta iota.
        lazymatch goal with |- context [(0 <=? arr_get ?w 0)] => replace (arr_get w 0) with (znth 0 Wl 0) by (symmetry; exact W0) end.
        rewrite E2, MN. rewrite (count_spec lens lens_ofs codes Hcodes Hlens 1) by lia. rewrite C1.
        change (wrap16 (1 - 1)) with 0. change (wrap32 (0 + 1)) with 1. change (wrap8 (1 - 0)) with 1.
        change (shl32 1 (1 - 0)) with 2. change (shl32 1 1) with 2.
        change (0 =? 0) with true. change (1 =? 1) with true. cbn [andb negb].
        rewrite (it_huff_next_eq' 0 1) by lia.
        replace (it_rev_incr 0 1) with 1 by (symmetry; change 0 with (brv (Z.to_nat 1) 0) at 1; rewrite (it_rev_incr_succZ 1 0) by lia; reflexivity).
        cbn [t_huff t_next]. change (1 =? 0) with false. cbn [negb].
        change (Z.shiftr 0 0) with 0. change (Z.shiftl 1 1) with 2. change (Z.shiftl 1 (1 - 0)) with 2.
        repeat match goal with |- (?a && ?b) = true => apply andb_true_intro; split end;
          try reflexivity; try (apply Z.leb_le; lia); try (apply Z.ltb_lt; lia).
        pose proof Hty as Hty'. clear - Wr Hty' HtyD Hcodes.
        destruct ty; [exfalso; exact (Hty' eq_refl)| |]; cbn [it_match it_ext_len].
        + destruct (Z.ltb_spec (znth 0 Wl 0 + 1) 257); [reflexivity|]. destruct (Z.leb_spec 257 (znth 0 Wl 0)); [|reflexivity]. apply Z.ltb_lt. lia.
        + pose proof (HtyD eq_refl). destruct (Z.ltb_spec (znth 0 Wl 0 + 1) 0); [reflexivity|]. destruct (Z.leb_spec 0 (znth 0 Wl 0)); [|reflexivity]. apply Z.ltb_lt. lia.
      -
        assert (HC : kr = 2 ^ 15) by lia. rewrite andb_false_l.
        rewrite sort_ok_true, andb_true_l.
        rewrite (used_eq E0).
        destruct (it_not_enough ty (2 ^ root)) eqn:NE; [reflexivity|].
        pose proof (fits E0) as FITS.
        pose proof (Hroot E0) as HR. pose proof (Hmax1 E0) as M1.
        pose proof (IS0' E0 NE) as I0. unfold IS in I0. destruct I0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hus0 & _ & Hoku0 & _).
        unfold itm_st0 in Hus0. cbn [t_used] in Hus0. rewrite (used_eq E0) in Hus0.
        pose proof (FITS 0 ltac:(pose proof (CN lens lens_ofs codes Hcodes Hlens M1); lia) Hoku0) as F0. rewrite <- Hus0 in F0.
        replace ((0 <=? table) && (table + 2 ^ root <=? arr_len tbl)) with true by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
        rewrite andb_true_l. rewrite (ctx_eq E0). unfold itm_work.
        apply (safe_from ty lens lens_ofs codes Hcodes Hlens M1 HC root HR table Htable HtyC19 NE (arr_len tbl) (arr_len work) (arr_len lens)
                 ltac:(lia) Hofs HLN HtyD FITS (Z.to_nat (codes + 1)) 0).
        + pose proof (CN lens lens_ofs codes Hcodes Hlens M1). lia.
        + exact (IS0' E0 NE).
        + lia.
    Qed.
  End Safe.
End Main.
