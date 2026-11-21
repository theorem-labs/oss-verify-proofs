(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ModelRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItGen.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItMath.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItSort.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItSimPre.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItSim1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Trip.
  Variable ty : codetype.
Variable lens : arr.
Variable lens_ofs : Z.
Variable codes : Z.
Variable ll : list Z.
Variable wl : list Z.
Variable table : Z.
Variable root : Z.
  Hypothesis Hcodes : 0 <= codes <= 288.
  Hypothesis Hlens : forall i, lens_ofs <= i < lens_ofs + codes -> 0 <= arr_get lens i <= 15.
  Hypothesis Ell : ll = lens_list lens lens_ofs codes.
  Hypothesis Ewl : wl = wl_of ll.
  Hypothesis Hroot : MINL wl <= root <= MAXL wl.
  Hypothesis HM1 : 1 <= MAXL wl.
  Hypothesis HK : TM wl (MAXL wl) <= 2 ^ MAXL wl.
  Hypothesis Hty : ty = CODES -> codes <= 19.
  #[local] Set Default Proof Using "Hcodes Hlens Ell Ewl Hroot HM1 HK Hty".

  Let HW := HW lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl.
  Let HL := HL lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl.

  Local Notation W := (W wl).
  Local Notation NZ := (NZ wl).
  Local Notation MAXL := (MAXL wl).
  Local Notation len_at := (len_at wl).
  Local Notation rank_at := (rank_at wl).
  Local Notation code := (code wl).
  Local Notation hf := (hf wl).
  Local Notation Pfx := (Pfx wl root).
  Local Notation islong := (islong wl root).
  Local Notation newtable := (newtable wl root).
  Local Notation noff := (noff wl root).
  Local Notation curr := (curr wl root).
  Local Notation used := (used wl root).
  Local Notation drop := (drop wl root).
  Local Notation low := (low wl root).
  Local Notation wsym := (wsym wl ll).
  Local Notation REM := (REM wl).

  Definition X : ItCtx := mkItCtx ty lens lens_ofs table root MAXL (2 ^ root - 1).

  Definition StM (k : Z) (st : ItSt) : Prop :=
    t_huff st = hf k /\ t_sym st = k /\ t_len st = len_at k /\
    t_next st = table + noff k /\ t_curr st = curr k /\ t_drop st = drop k /\
    t_low st = low k /\ t_used st = used k /\
    arr_len (t_count st) = 16 /\
    (forall l, 1 <= l <= 15 -> arr_get (t_count st) l = REM k l) /\
    (forall j, 0 <= j < NZ -> arr_get (t_work st) j = wsym j).

  Let Hll' := ItSimPre.Hll lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl.

  Lemma wsym_facts : forall k, 0 <= k < NZ -> 0 <= wsym k < codes /\ LofS ll (wsym k) = len_at k.
  Proof.
    intros k Hk. pose proof (wsym_spec ll Hll' k) as WS. rewrite <- Ewl in WS.
    rewrite (NC_ll lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) in WS. apply WS. exact Hk.
  Qed.

  Lemma entry_eq : forall work k, 0 <= k < NZ ->
    (if wsym k + 1 <? it_match ty then (0, wsym k)
     else if it_match ty <=? wsym k
          then (wrap8 (it_extra ty work (wsym k - it_match ty)), it_base ty work (wsym k - it_match ty))
          else (96, 0)) = entry ty (wsym k).
  Proof.
    intros work k Hk. pose proof (wsym_facts k Hk) as [R _].
    destruct ty; cbn [it_match it_extra it_base entry].
    - specialize (Hty eq_refl). destruct (Z.ltb_spec (wsym k + 1) 20); [reflexivity|lia].
    - destruct (Z.ltb_spec (wsym k + 1) 257); [reflexivity|].
      destruct (Z.leb_spec 257 (wsym k)); [|reflexivity].
      unfold lext_a, lbase_a. rewrite !arr_get_of_list_nth by lia. reflexivity.
    - destruct (Z.ltb_spec (wsym k + 1) 0); [lia|]. destruct (Z.leb_spec 0 (wsym k)); [|lia].
      unfold dext_a, dbase_a. rewrite Z.sub_0_r. rewrite !arr_get_of_list_nth by lia. reflexivity.
  Qed.

  Lemma hf_step : forall k, 0 <= k < NZ ->
    (if negb (it_incr_back (hf k) (len_at k) =? 0)
     then Z.land (hf k) (it_incr_back (hf k) (len_at k) - 1) + it_incr_back (hf k) (len_at k)
     else 0) = hf (k + 1).
  Proof.
    intros k Hk. rewrite (hf_spec wl HW HL HK k Hk).
    pose proof (len_at_spec wl HW HL k Hk) as [L _]. pose proof (code_nonneg wl HW HL k Hk).
    pose proof (code_bound wl HW HL HK k Hk).
    rewrite huff_update by lia.
    unfold ItDefs.hf. destruct (Z.eqb_spec (k + 1) 0); [lia|]. replace (k + 1 - 1) with k by lia. reflexivity.
  Qed.

  Lemma REM_self : forall k, 0 <= k < NZ -> REM k (len_at k) = W (len_at k) - rank_at k.
  Proof. intros k Hk. unfold ItSim1.REM. rewrite Z.ltb_irrefl, Z.eqb_refl. reflexivity. Qed.

  Lemma cnt_step : forall cnt k, 0 <= k -> k + 1 < NZ -> arr_len cnt = 16 ->
    (forall l, 1 <= l <= 15 -> arr_get cnt l = REM k l) ->
    forall l, 1 <= l <= 15 -> arr_get (arr_set cnt (len_at k) (W (len_at k) - rank_at k - 1)) l = REM (k + 1) l.
  Proof.
    intros cnt k Hk Hk1 HLc Hc l Hl. pose proof (len_at_spec wl HW HL k ltac:(lia)) as [L1 _].
    rewrite arr_get_set. unfold arr_inb. rewrite HLc.
    destruct (len_at_step wl HW HL k Hk Hk1) as [[A [B C]]|[A [B [C D]]]]; unfold ItSim1.REM; rewrite ?B, ?C.
    - destruct (Z.eqb_spec (len_at k) l) as [<-|NE].
      + destruct (Z.leb_spec 0 (len_at k)); [|lia]. destruct (Z.ltb_spec (len_at k) 16); [|lia]. cbn [andb].
        rewrite Z.ltb_irrefl, Z.eqb_refl. lia.
      + cbn [andb]. rewrite Hc by lia. unfold ItSim1.REM.
        destruct (Z.ltb_spec l (len_at k)), (Z.eqb_spec l (len_at k)); try lia; reflexivity.
    - destruct (Z.eqb_spec (len_at k) l) as [<-|NE].
      + destruct (Z.leb_spec 0 (len_at k)); [|lia]. destruct (Z.ltb_spec (len_at k) 16); [|lia]. cbn [andb].
        destruct (Z.ltb_spec (len_at k) (len_at (k + 1))); [|lia]. lia.
      + cbn [andb]. rewrite Hc by lia. unfold ItSim1.REM.
        destruct (Z.ltb_spec l (len_at k)), (Z.eqb_spec l (len_at k)), (Z.ltb_spec l (len_at (k + 1))), (Z.eqb_spec l (len_at (k + 1))); try lia; try reflexivity.
        all: try (rewrite D by lia; reflexivity). all: subst; lia.
  Qed.

  Lemma low_val : forall k, 0 <= k < NZ -> islong k = true -> Z.land (hf k) (2 ^ root - 1) = rev root (Pfx k).
  Proof.
    intros k Hk HLg. pose proof (root_range wl HW HL root Hroot HM1) as RR.
    pose proof HLg as HLg'. unfold ItDefs.islong in HLg'. apply Z.ltb_lt in HLg'.
    rewrite (hf_spec wl HW HL HK k Hk). rewrite land_ones' by lia.
    pose proof (len_at_spec wl HW HL k Hk) as [L _]. pose proof (code_nonneg wl HW HL k Hk).
    rewrite rev_mod by lia. rewrite (Pfx_code wl HW HL root Hroot HM1 k Hk HLg). reflexivity.
  Qed.

  Lemma newtable_test : forall k, 0 <= k -> k + 1 < NZ ->
    (root <? len_at (k + 1)) && negb (Z.land (hf (k + 1)) (2 ^ root - 1) =? low k) = newtable (k + 1).
  Proof.
    intros k Hk Hk1. pose proof (root_range wl HW HL root Hroot HM1) as RR.
    unfold ItDefs.newtable. replace (k + 1 - 1) with k by lia.
    destruct (islong (k + 1)) eqn:HL1.
    2:{ unfold ItDefs.islong in HL1. rewrite HL1. reflexivity. }
    pose proof HL1 as HL1'. unfold ItDefs.islong in HL1'. rewrite HL1'. cbn [andb].
    rewrite (low_val (k + 1)) by (lia || exact HL1).
    pose proof (rev_bound root (Pfx (k + 1)) ltac:(lia)) as RB.
    pose proof (Pfx_bound wl HW HL root Hroot HM1 HK (k + 1) ltac:(lia)). pose proof (Pfx_nonneg wl HW HL root Hroot HM1 (k + 1) ltac:(lia)).
    unfold ItDefs.low. destruct (islong k) eqn:HL0; cbn [negb orb].
    - pose proof (Pfx_bound wl HW HL root Hroot HM1 HK k ltac:(lia)). pose proof (Pfx_nonneg wl HW HL root Hroot HM1 k ltac:(lia)).
      destruct (Z.eqb_spec (Pfx (k + 1)) (Pfx k)) as [E|NE].
      + rewrite E, Z.eqb_refl. reflexivity.
      + destruct (Z.eqb_spec (rev root (Pfx (k + 1))) (rev root (Pfx k))) as [E2|NE2]; [|reflexivity].
        exfalso. apply NE. apply (rev_inj root); lia || exact E2.
    - pose proof (pow2_le_15 root ltac:(lia)). destruct (Z.eqb_spec (rev root (Pfx (k + 1))) 4294967295); [lia|reflexivity].
  Qed.

  Lemma drop0_root : forall k, (if drop k =? 0 then root else drop k) = root.
  Proof.
    intros k. pose proof (root_range wl HW HL root Hroot HM1). unfold ItDefs.drop.
    destruct (islong k); [destruct (Z.eqb_spec root 0); lia | rewrite Z.eqb_refl; reflexivity].
  Qed.

  Lemma drop_low_new : forall k, newtable (k + 1) = true ->
    drop (k + 1) = root /\ low (k + 1) = rev root (Pfx (k + 1)).
  Proof.
    intros k HN. pose proof (newtable_long wl HW HL root Hroot HM1 (k + 1) HN) as HLg.
    unfold ItDefs.drop, ItDefs.low. rewrite HLg. split; reflexivity.
  Qed.

  Lemma drop_low_same : forall k, 0 <= k -> k + 1 < NZ -> newtable (k + 1) = false ->
    drop (k + 1) = drop k /\ low (k + 1) = low k.
  Proof.
    intros k Hk Hk1 HN. unfold ItDefs.drop, ItDefs.low. destruct (islong (k + 1)) eqn:HL1.
    - destruct (not_newtable wl HW HL root Hroot HM1 k Hk Hk1 HN HL1) as [HL0 HP]. rewrite HL0, HP. split; reflexivity.
    - destruct (islong k) eqn:HL0; [|split; reflexivity].
      rewrite (islong_mono wl HW HL root Hroot HM1 k (k + 1) ltac:(lia) Hk1 HL0) in HL1. discriminate HL1.
  Qed.

  Lemma used_bnd : forall k, 0 <= k < NZ -> 0 <= used k <= 32768 * (k + 1).
  Proof.
    intros k Hk. pose proof (root_range wl HW HL root Hroot HM1) as RR.
    remember (Z.to_nat k) as n eqn:Hn. revert k Hk Hn.
    induction n as [|n IH]; intros k Hk Hn.
    - replace k with 0 by lia. unfold ItDefs.used. rewrite (lay_0 wl HW HL root Hroot HM1). cbn [snd]. pose proof (pow2_le_15 root ltac:(lia)). lia.
    - specialize (IH (k - 1) ltac:(lia) ltac:(lia)). replace k with (k - 1 + 1) by lia.
      destruct (newtable (k - 1 + 1)) eqn:HN.
      + pose proof (lay_S_new wl HW HL root Hroot HM1 (k - 1) ltac:(lia) HN) as [_ [_ E]]. rewrite E.
        pose proof (curr_range wl HW HL root Hroot HM1 (k - 1 + 1) ltac:(lia)) as [C _].
        pose proof (pow2_le_15 (curr (k - 1 + 1)) ltac:(lia)). lia.
      + pose proof (lay_same_proj wl HW HL root Hroot HM1 (k - 1) ltac:(lia) HN) as [_ [_ E]]. rewrite E. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fill_writes_eq : forall k,
    fill_writes wl ll root ty table k =
    fill_list (here wl ll root ty k) (2 ^ (len_at k - drop k)) (table + noff k + hf k / 2 ^ drop k)
              (Z.to_nat (2 ^ (curr k - (len_at k - drop k)))).
  Proof. intros k. reflexivity. Qed.

  Ltac redst := cbv beta iota zeta delta [t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_min t_count t_tbl t_work
                                          x_ty x_lens x_lens_ofs x_table x_root x_max x_mask X].

  (* [comment removed for export] *)
  Lemma trip_tail : forall k LEN cnt' tbl work, 0 <= k -> k + 1 < NZ -> LEN = len_at (k + 1) ->
    arr_len cnt' = 16 -> (forall l, 1 <= l <= 15 -> arr_get cnt' l = REM (k + 1) l) ->
    (forall j, 0 <= j < NZ -> arr_get work j = wsym j) ->
    match
      (if (root <? LEN) && negb (Z.land (hf (k + 1)) (2 ^ root - 1) =? low k)
       then
        if it_not_enough ty
             (wrap32 (used k + Z.shiftl 1 (it_subtable_curr cnt' (LEN) (if drop k =? 0 then root else drop k) MAXL)))
        then
         ItFail
           {| t_huff := hf (k + 1); t_sym := k + 1; t_len := LEN;
              t_next := table + noff k + 2 ^ curr k;
              t_curr := it_subtable_curr cnt' (LEN) (if drop k =? 0 then root else drop k) MAXL;
              t_drop := if drop k =? 0 then root else drop k;
              t_low := low k;
              t_used := wrap32 (used k + Z.shiftl 1 (it_subtable_curr cnt' (LEN) (if drop k =? 0 then root else drop k) MAXL));
              t_min := 2 ^ curr k; t_count := cnt';
              t_tbl := applyw (fill_writes wl ll root ty table k) tbl; t_work := work |}
        else
         ItCont
           {| t_huff := hf (k + 1); t_sym := k + 1; t_len := LEN;
              t_next := table + noff k + 2 ^ curr k;
              t_curr := it_subtable_curr cnt' (LEN) (if drop k =? 0 then root else drop k) MAXL;
              t_drop := if drop k =? 0 then root else drop k;
              t_low := Z.land (hf (k + 1)) (2 ^ root - 1);
              t_used := wrap32 (used k + Z.shiftl 1 (it_subtable_curr cnt' (LEN) (if drop k =? 0 then root else drop k) MAXL));
              t_min := 2 ^ curr k; t_count := cnt';
              t_tbl := arr_set (applyw (fill_writes wl ll root ty table k) tbl)
                         (table + Z.land (hf (k + 1)) (2 ^ root - 1))
                         (code_pack (it_subtable_curr cnt' (LEN) (if drop k =? 0 then root else drop k) MAXL)
                                    root (table + noff k + 2 ^ curr k - table));
              t_work := work |}
       else
        ItCont
          {| t_huff := hf (k + 1); t_sym := k + 1; t_len := LEN;
             t_next := table + noff k; t_curr := curr k; t_drop := drop k; t_low := low k; t_used := used k;
             t_min := 2 ^ curr k; t_count := cnt';
             t_tbl := applyw (fill_writes wl ll root ty table k) tbl; t_work := work |})
    with
    | ItCont st' => k + 1 < NZ /\ fails_at wl root ty k = false /\ StM (k + 1) st' /\
                    t_tbl st' = applyw (trip_writes wl ll root ty table k) tbl /\ t_work st' = work
    | ItBreak st' => k + 1 = NZ /\ t_huff st' = hf NZ /\ t_len st' = len_at k /\ t_drop st' = drop k /\
                     t_next st' = table + noff k /\ t_used st' = used k /\
                     t_tbl st' = applyw (fill_writes wl ll root ty table k) tbl /\ t_work st' = work
    | ItFail st' => k + 1 < NZ /\ fails_at wl root ty k = true /\
                    t_tbl st' = applyw (fill_writes wl ll root ty table k) tbl /\ t_work st' = work
    end.
  Proof.
    intros k LEN cnt' tbl work Hk Hk1 ELEN Lc' Hc' Hw. subst LEN. pose proof (root_range wl HW HL root Hroot HM1) as RR.
    rewrite (newtable_test k Hk Hk1). rewrite drop0_root.
    unfold ItDefs.fails_at, ItDefs.trip_writes, ItDefs.link_writes.
    destruct (Z.ltb_spec (k + 1) NZ); [|lia]. cbn [andb].
    destruct (newtable (k + 1)) eqn:HN; cbn [andb].
    - (* [comment removed for export] *)
      pose proof (lay_S_new wl HW HL root Hroot HM1 k Hk HN) as [En [Ecu Eus]].
      pose proof (drop_low_new k HN) as [Edr Elo].
      pose proof (newtable_long wl HW HL root Hroot HM1 (k + 1) HN) as HLg.
      rewrite (subtable_curr_spec wl HW HL root Hroot HM1 cnt' (k + 1) ltac:(lia) HN) by (intros; apply Hc'; pose proof (len_at_spec wl HW HL (k + 1) ltac:(lia)); lia).
      rewrite <- Ecu.
      pose proof (curr_range wl HW HL root Hroot HM1 (k + 1) ltac:(lia)) as [C1 _].
      pose proof (used_bnd k ltac:(lia)) as UB. pose proof (NZ_le_codes lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) as NZC.
      pose proof (pow2_le_15 (curr (k + 1)) ltac:(lia)).
      rewrite Z.shiftl_1_l. rewrite (wrap32_small (used k + 2 ^ curr (k + 1))) by nia.
      rewrite <- Eus. rewrite (low_val (k + 1) ltac:(lia) HLg).
      destruct (it_not_enough ty (used (k + 1))) eqn:NE; cbn [negb].
      + cbn [t_tbl t_work]. repeat split; try reflexivity; lia.
      + split; [lia|]. split; [reflexivity|]. split.
        * unfold StM. cbn [t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_count t_work].
          rewrite En, Edr, Elo. repeat split; try reflexivity; try assumption; lia.
        * cbn [t_tbl t_work]. split; [|reflexivity]. rewrite applyw_snoc. rewrite En.
          replace (table + (noff k + 2 ^ curr k) - table) with (noff k + 2 ^ curr k) by lia.
          replace (table + noff k + 2 ^ curr k - table) with (noff k + 2 ^ curr k) by lia. reflexivity.
    - (* [comment removed for export] *)
      pose proof (lay_same_proj wl HW HL root Hroot HM1 k Hk HN) as [En [Ecu Eus]].
      pose proof (drop_low_same k Hk Hk1 HN) as [Edr Elo].
      split; [lia|]. split; [reflexivity|]. split.
      + unfold StM. cbn [t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_count t_work].
        rewrite En, Ecu, Eus, Edr, Elo. repeat split; try reflexivity; try assumption; lia.
      + cbn [t_tbl t_work]. rewrite app_nil_r. split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma trip_spec : forall k st, 0 <= k < NZ -> StM k st ->
    match it_step X st with
    | ItBreak st' => k + 1 = NZ /\ t_huff st' = hf NZ /\ t_len st' = len_at k /\ t_drop st' = drop k /\
                     t_next st' = table + noff k /\ t_used st' = used k /\
                     t_tbl st' = applyw (fill_writes wl ll root ty table k) (t_tbl st) /\ t_work st' = t_work st
    | ItFail st' => k + 1 < NZ /\ fails_at wl root ty k = true /\
                    t_tbl st' = applyw (fill_writes wl ll root ty table k) (t_tbl st) /\ t_work st' = t_work st
    | ItCont st' => k + 1 < NZ /\ fails_at wl root ty k = false /\ StM (k + 1) st' /\
                    t_tbl st' = applyw (trip_writes wl ll root ty table k) (t_tbl st) /\ t_work st' = t_work st
    end.
  Proof.
    intros k st Hk SM. pose proof (root_range wl HW HL root Hroot HM1) as RR. pose proof (MAXL_spec wl HW HL) as [MM _].
    destruct st as [huff sym len next cur drp lw usd mn cnt tbl work].
    destruct SM as (Eh & Es & El & En & Ec & Ed & Elw & Eu & Lc & Hc & Hw). cbn [t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_count t_work] in *.
    subst huff sym len next cur drp lw usd.
    pose proof (len_at_spec wl HW HL k Hk) as [L1 _]. pose proof (len_at_range wl HW HL k Hk) as LR.
    pose proof (rank_at_spec wl HW HL k Hk) as RK. pose proof (curr_range wl HW HL root Hroot HM1 k Hk) as [CR1 [CR2 CR3]].
    pose proof (used_bnd k Hk) as UB. pose proof (NZ_le_codes lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) as NZC.
    assert (Hdrop : 0 <= drop k <= root) by (unfold ItDefs.drop; destruct (islong k); lia).
    assert (WB : W (len_at k) <= NZ).
    { pose proof (OFF_mono wl HW HL (len_at k + 1) 16 ltac:(lia)) as M. rewrite (OFF_step wl HW HL) in M by lia.
      pose proof (OFF_nonneg wl HW HL (len_at k)). rewrite <- (NZ_eq wl HW HL) in M. lia. }
    unfold it_step. redst.
    rewrite (Hw k Hk). rewrite (entry_eq work k Hk).
    destruct (entry ty (wsym k)) as [eop eval] eqn:Eent. redst.
    rewrite (wrap32_small (k + 1)) by lia.
    rewrite (Hc (len_at k)) by lia. rewrite (REM_self k Hk).
    rewrite (wrap16_small (W (len_at k) - rank_at k - 1)) by lia.
    rewrite (hf_step k Hk).
    rewrite (wrap8_small (len_at k - drop k)) by lia.
    rewrite !shl32_pow2 by lia.
    rewrite it_fill_eq by lia.
    assert (Etbl : applyw (fill_list (code_pack eop (len_at k - drop k) eval) (2 ^ (len_at k - drop k))
                             (table + noff k + hf k / 2 ^ drop k) (Z.to_nat (2 ^ (curr k - (len_at k - drop k))))) tbl
                   = applyw (fill_writes wl ll root ty table k) tbl).
    { rewrite fill_writes_eq. unfold ItDefs.here. rewrite Eent. reflexivity. }
    rewrite Etbl. clear Etbl.
    (* [comment removed for export] *)
    pose proof (last_iff wl HW HL k Hk) as LI.
    destruct (Z.eqb_spec (W (len_at k) - rank_at k - 1) 0) as [Hc0|Hc0];
      destruct (Z.eqb_spec (len_at k) MAXL) as [HlM|HlM]; cbn [andb negb].
    - (* [comment removed for export] *)
      assert (Hk1 : k + 1 = NZ) by (apply proj2 in LI; specialize (LI ltac:(lia)); lia).
      redst. rewrite Hk1. repeat split; reflexivity.
    - (* [comment removed for export] *)
      assert (Hk1 : k + 1 < NZ) by (destruct (Z.eq_dec k (NZ - 1)) as [E|E]; [apply proj1 in LI; specialize (LI E); lia | lia]).
      rewrite (Hw (k + 1)) by lia. pose proof (wsym_facts (k + 1) ltac:(lia)) as [WR WL].
      rewrite <- (LofS_ll lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) by lia.
      apply trip_tail; [lia | lia | exact WL | rewrite arr_len_set; exact Lc | apply cnt_step; try lia; assumption | exact Hw].
    - assert (Hk1 : k + 1 < NZ) by (destruct (Z.eq_dec k (NZ - 1)) as [E|E]; [apply proj1 in LI; specialize (LI E); lia | lia]).
      destruct (len_at_step wl HW HL k ltac:(lia) Hk1) as [[A [B C]]|[A _]]; [|lia].
      apply trip_tail; [lia | lia | exact (eq_sym B) | rewrite arr_len_set; exact Lc | apply cnt_step; try lia; assumption | exact Hw].
    - assert (Hk1 : k + 1 < NZ) by (destruct (Z.eq_dec k (NZ - 1)) as [E|E]; [apply proj1 in LI; specialize (LI E); lia | lia]).
      destruct (len_at_step wl HW HL k ltac:(lia) Hk1) as [[A [B C]]|[A _]]; [|lia].
      apply trip_tail; [lia | lia | exact (eq_sym B) | rewrite arr_len_set; exact Lc | apply cnt_step; try lia; assumption | exact Hw].
  Qed.
  (* [comment removed for export] *)
  Lemma trips_writes_S : forall n, 0 <= n ->
    trips_writes wl ll root ty table (n + 1) = trips_writes wl ll root ty table n ++ trip_writes wl ll root ty table n.
  Proof.
    intros n Hn. unfold ItDefs.trips_writes. replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
    rewrite seq_S, flat_map_app. cbn [flat_map Nat.add]. rewrite app_nil_r, Z2Nat.id by lia. reflexivity.
  Qed.

  Lemma trip_writes_nolink : forall k,
    link_writes wl root ty table k = [] -> trip_writes wl ll root ty table k = fill_writes wl ll root ty table k.
  Proof. intros k H. unfold ItDefs.trip_writes. rewrite H. apply app_nil_r. Qed.

  Definition loopF (st : ItSt) : ItSt + (ItSt + ItSt) :=
    match it_step X st with
    | ItCont st' => inl st'
    | ItBreak st' => inr (inl st')
    | ItFail st' => inr (inr st')
    end.

  Lemma it_loop_unfold : forall st, it_loop X codes st = iterZ (codes + 1) loopF (fun st => inl st) st.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma loop_gen : forall k st fuel tbl0 work0, 0 <= k < NZ -> StM k st ->
    t_tbl st = applyw (trips_writes wl ll root ty table k) tbl0 -> t_work st = work0 ->
    (forall j, 0 <= j < k -> fails_at wl root ty j = false) -> NZ - k <= fuel ->
    match iterZ fuel loopF (fun st => inl st) st with
    | inl st' => first_fail wl root ty = NZ - 1 /\ t_huff st' = hf NZ /\ t_len st' = len_at (NZ - 1) /\
                 t_drop st' = drop (NZ - 1) /\ t_next st' = table + noff (NZ - 1) /\ t_used st' = used (NZ - 1) /\
                 t_tbl st' = applyw (trips_writes wl ll root ty table NZ) tbl0 /\ t_work st' = work0
    | inr st' => first_fail wl root ty < NZ - 1 /\
                 t_tbl st' = applyw (trips_writes wl ll root ty table (first_fail wl root ty + 1)) tbl0 /\ t_work st' = work0
    end.
  Proof.
    intros k st fuel tbl0 work0 Hk. remember (Z.to_nat (NZ - k)) as n eqn:Hn. revert k st fuel Hk Hn.
    induction n as [|n IH]; intros k st fuel Hk Hn SM Et Ew Hnf Hf; [lia|].
    rewrite iterZ_step by lia. unfold loopF at 1.
    pose proof (trip_spec k st Hk SM) as TS.
    destruct (it_step X st) as [st'|st'|st'].
    - destruct TS as (Hk1 & Hfa & SM' & Et' & Ew').
      apply (IH (k + 1)); try lia.
      + exact SM'.
      + rewrite Et', Et, <- applyw_app, <- trips_writes_S by lia. reflexivity.
      + rewrite Ew', Ew. reflexivity.
      + intros j Hj. destruct (Z.eq_dec j k) as [->|NE]; [exact Hfa | apply Hnf; lia].
    - destruct TS as (Hk1 & Eh & El & Ed & En & Eu & Et' & Ew').
      assert (FF : first_fail wl root ty = NZ - 1).
      { unfold ItDefs.first_fail. rewrite zsearch_none; [lia|]. intros j Hj. apply Hnf. lia. }
      rewrite FF. replace (NZ - 1) with k by lia.
      repeat split; try assumption.
      + rewrite Et', Et, <- applyw_app, <- Hk1. rewrite trips_writes_S by lia. rewrite trip_writes_nolink; [reflexivity|].
        unfold ItDefs.link_writes. rewrite <- Hk1. rewrite Z.ltb_irrefl. reflexivity.
      + rewrite Ew', Ew. reflexivity.
    - destruct TS as (Hk1 & Hfa & Et' & Ew').
      assert (FF : first_fail wl root ty = k).
      { unfold ItDefs.first_fail. apply zsearch_eq; [lia | exact Hfa | intros j Hj; apply Hnf; lia]. }
      rewrite FF. split; [lia|]. split.
      + rewrite Et', Et, <- applyw_app. rewrite trips_writes_S by lia. rewrite trip_writes_nolink; [reflexivity|].
        unfold ItDefs.fails_at in Hfa. unfold ItDefs.link_writes.
        destruct ((k + 1 <? NZ) && newtable (k + 1)); [|reflexivity]. cbn [andb] in Hfa |- *. rewrite Hfa. reflexivity.
      + rewrite Ew', Ew. reflexivity.
  Qed.
End Trip.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Top.
  Variable ty : codetype.
Variable lens : arr.
Variable lens_ofs : Z.
Variable codes : Z.
Variable ll : list Z.
Variable wl : list Z.
Variable table : Z.
Variable bits : Z.
  Hypothesis Hcodes : 0 <= codes <= 288.
  Hypothesis Hlens : forall i, lens_ofs <= i < lens_ofs + codes -> 0 <= arr_get lens i <= 15.
  Hypothesis Ell : ll = lens_list lens lens_ofs codes.
  Hypothesis Ewl : wl = wl_of ll.
  Hypothesis Hty : ty = CODES -> codes <= 19.
  Hypothesis Hbits : 1 <= bits <= 15.
  #[local] Set Default Proof Using "Hcodes Hlens Ell Ewl Hty Hbits".

  Let HW := HW lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl.
  Let HL := HL lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl.
  Let Hll' := ItSimPre.Hll lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl.

  Lemma ROOT_range : 1 <= MAXL wl -> MINL wl <= ROOT wl bits <= MAXL wl.
  Proof. intros HM. pose proof (MINL_spec wl HW HL HM). unfold ROOT. lia. Qed.

  Theorem inflate_table_abs : forall tbl work, codes <= arr_len work ->
    inflate_table ty lens lens_ofs codes tbl table bits work =
    (let '(ret, ws, toff, bits', ww) := it_abs wl ll ty table bits in
     (ret, applyw ws tbl, toff, bits', applyw ww work)).
  Proof.
    intros tbl work Hwork.
    pose proof (count_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) as [CL CC].
    set (C := CNT lens lens_ofs codes) in CL, CC.
    pose proof (MAXL_spec wl HW HL) as [M1 [M2 M3]].
    unfold inflate_table. change (it_count lens lens_ofs codes (it_zero_count (arr_make 16 0))) with C.
    cbv zeta. rewrite (find_max_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl C CC).
    unfold it_abs.
    destruct (Z.eqb_spec (MAXL wl) 0) as [HM0|HM0]; [reflexivity|].
    assert (HM1 : 1 <= MAXL wl) by lia.
    rewrite (find_min_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl C CC HM1).
    rewrite (left_check_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl C CC).
    pose proof (LEFT_sign wl HW HL) as [LS1 [LS2 LS3]].
    destruct (Z.ltb_spec (LEFT wl) 0) as [HL0|HL0]; [reflexivity|].
    assert (HK : TM wl (MAXL wl) <= 2 ^ MAXL wl) by lia.
    destruct ((0 <? LEFT wl) && (codetype_eqb ty CODES || negb (MAXL wl =? 1))) eqn:Hinc; [reflexivity|].
    pose proof (offs_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl C CC) as [OL OC].
    change (it_offs C (arr_make 16 0)) with (OFS C).
    set (O := OFS C) in OL, OC |- *.
    pose proof (sort_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl O work OL OC) as SS.
    match goal with |- context [it_sort ?a ?b ?c ?d] => set (SRT := it_sort a b c d) in * end.
    clearbody SRT. destruct SRT as [O' work']. cbn [snd] in SS. subst work'.
    assert (ER : (if (if MAXL wl <? bits then MAXL wl else bits) <? MINL wl then MINL wl
                  else if MAXL wl <? bits then MAXL wl else bits) = ROOT wl bits).
    { unfold ROOT. destruct (Z.ltb_spec (MAXL wl) bits); [destruct (Z.ltb_spec (MAXL wl) (MINL wl))|destruct (Z.ltb_spec bits (MINL wl))]; lia. }
    rewrite ER. pose proof (ROOT_range HM1) as RR. set (root := ROOT wl bits) in *.
    pose proof (root_range wl HW HL root RR HM1) as RR2.
    rewrite shl32_pow2 by lia.
    destruct (it_not_enough ty (2 ^ root)) eqn:NE0; [reflexivity|].
    change (mkItCtx ty lens lens_ofs table root (MAXL wl) (2 ^ root - 1)) with (X ty lens lens_ofs wl table root).
    rewrite (it_loop_unfold ty lens lens_ofs codes ll wl table root Hcodes Hlens Ell Ewl RR HM1 HK Hty).
    pose proof (NZ_pos wl HW HL HM1) as NP. pose proof (NZ_le_codes lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) as NC0.
    pose proof (loop_gen ty lens lens_ofs codes ll wl table root Hcodes Hlens Ell Ewl RR HM1 HK Hty
                  0 (mkItSt 0 0 (MINL wl) table root 0 4294967295 (2 ^ root) 0 C tbl (applyw (sort_writes wl ll) work))
                  (codes + 1) tbl (applyw (sort_writes wl ll) work) ltac:(lia)) as LG.
    unfold loop_abs.
    match type of LG with ?P -> _ => assert (SM0 : P) end.
    { unfold StM. cbn [t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_count t_work].
      pose proof (lay_inv wl HW HL root RR HM1 0 ltac:(lia)) as [LI _].
      assert (HS : islong wl root 0 = false).
      { unfold islong. rewrite (len_at_0 wl HW HL HM1). apply Z.ltb_ge. lia. }
      destruct (LI HS) as [N0 [C0 U0]]. rewrite N0, C0, U0. unfold ItDefs.drop, ItDefs.low. rewrite HS.
      rewrite (len_at_0 wl HW HL HM1).
      repeat split; try reflexivity; try lia.
      - intros l Hl. rewrite CC by lia. unfold REM. rewrite (len_at_0 wl HW HL HM1).
        pose proof (MINL_spec wl HW HL HM1) as [A [B D]]. unfold rank_at. rewrite (len_at_0 wl HW HL HM1).
        rewrite (OFF_below_MINL wl HW HL (MINL wl)) by lia.
        destruct (Z.ltb_spec l (MINL wl)); [apply D; lia|]. destruct (Z.eqb_spec l (MINL wl)); [subst; lia | reflexivity].
      - intros j Hj. rewrite Ewl in Hj |- *. apply (sorted_work ll Hll'); [|exact Hj].
        pose proof (NZ_le_NC ll Hll') as NN. rewrite (NC_ll lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) in NN. lia. }
    specialize (LG SM0 eq_refl eq_refl ltac:(intros; lia) ltac:(lia)).
    cbn [t_tbl t_work] in LG.
    destruct (iterZ (codes + 1) (loopF ty lens lens_ofs wl table root) (fun st => inl st) _) as [st|st].
    - destruct LG as (FF & Eh & El & Ed & En & Eu & Et & Ew).
      rewrite FF. rewrite Z.ltb_irrefl. rewrite Eh, El, Ed, En, Eu, Et, Ew.
      unfold final_writes. destruct (Z.eqb_spec (hf wl (NZ wl)) 0) as [Z0|Z0]; cbn [negb].
      + rewrite app_nil_r. reflexivity.
      + rewrite applyw_snoc. reflexivity.
    - destruct LG as (FF & Et & Ew). destruct (Z.ltb_spec (first_fail wl root ty) (NZ wl - 1)); [|lia].
      rewrite Et, Ew. reflexivity.
  Qed.
End Top.
