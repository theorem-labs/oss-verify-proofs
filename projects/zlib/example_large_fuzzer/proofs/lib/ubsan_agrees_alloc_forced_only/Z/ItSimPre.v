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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lens_list_length : forall lens ofs codes, length (lens_list lens ofs codes) = Z.to_nat codes.
Proof. intros. unfold lens_list. rewrite map_length, seq_length. reflexivity. Qed.

Lemma LofS_lens : forall lens ofs codes s, 0 <= s < codes ->
  LofS (lens_list lens ofs codes) s = arr_get lens (ofs + s).
Proof.
  intros lens ofs codes s Hs. unfold LofS, lens_list. rewrite nth_map_seq by lia. f_equal. lia.
Qed.

Lemma nth_lens_list : forall lens ofs codes n, (n < Z.to_nat codes)%nat ->
  nth n (lens_list lens ofs codes) 0 = arr_get lens (ofs + Z.of_nat n).
Proof. intros. unfold lens_list. rewrite nth_map_seq by lia. reflexivity. Qed.

Lemma lens_list_Forall : forall lens ofs codes,
  (forall i, ofs <= i < ofs + codes -> 0 <= arr_get lens i <= 15) ->
  Forall (fun l => 0 <= l <= 15) (lens_list lens ofs codes).
Proof.
  intros lens ofs codes H. unfold lens_list. apply Forall_map. apply Forall_forall.
  intros n Hn. apply in_seq in Hn. apply H. lia.
Qed.

Lemma NC_lens : forall lens ofs codes, 0 <= codes -> NC (lens_list lens ofs codes) = codes.
Proof. intros. unfold NC, zlength. rewrite lens_list_length. lia. Qed.

Lemma arr_get_of_list_nth : forall l i, 0 <= i -> arr_get (arr_of_list l) i = nth (Z.to_nat i) l 0.
Proof.
  intros l i Hi. unfold arr_of_list, parr_of_list. rewrite (arr_get_upd l _ 0 i 0).
  unfold arr_inb. rewrite arr_len_make, arr_get_make. rewrite Z.sub_0_r.
  destruct (Z.ltb_spec i (0 + zlength l)).
  - destruct (Z.leb_spec 0 i); [|lia]. destruct (Z.ltb_spec i (zlength l)); [|lia]. reflexivity.
  - cbn [andb]. rewrite Bool.andb_false_r. symmetry. apply nth_overflow. unfold zlength in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section Pre.
  Variable lens : arr.
Variable lens_ofs : Z.
Variable codes : Z.
Variable ll : list Z.
Variable wl : list Z.
  Hypothesis Hcodes : 0 <= codes <= 288.
  Hypothesis Hlens : forall i, lens_ofs <= i < lens_ofs + codes -> 0 <= arr_get lens i <= 15.
  Hypothesis Ell : ll = lens_list lens lens_ofs codes.
  Hypothesis Ewl : wl = wl_of ll.
  #[local] Set Default Proof Using "Hcodes Hlens Ell Ewl".

  Lemma Hll : Forall (fun l => 0 <= l <= 15) ll.
  Proof. rewrite Ell. apply lens_list_Forall. exact Hlens. Qed.
  Lemma HW : forall l, 0 <= W wl l.
  Proof. rewrite Ewl. apply (W_of_nonneg ll Hll). Qed.
  Lemma HL : length wl = 16%nat.
  Proof. rewrite Ewl. apply (wl_of_length ll Hll). Qed.
  Lemma W_count : forall l, 0 <= l <= 15 -> W wl l = countz l ll.
  Proof. rewrite Ewl. apply (W_of ll Hll). Qed.
  Lemma ll_length : length ll = Z.to_nat codes.
  Proof. rewrite Ell. apply lens_list_length. Qed.
  Lemma NC_ll : NC ll = codes.
  Proof. rewrite Ell. apply NC_lens. lia. Qed.
  Lemma nth_ll : forall n, (n < Z.to_nat codes)%nat -> nth n ll 0 = arr_get lens (lens_ofs + Z.of_nat n).
  Proof. rewrite Ell. apply nth_lens_list. Qed.
  Lemma LofS_ll : forall s, 0 <= s < codes -> LofS ll s = arr_get lens (lens_ofs + s).
  Proof. rewrite Ell. apply LofS_lens. Qed.

  Lemma NZ_le_codes : NZ wl <= codes.
  Proof. pose proof (NZ_le_NC ll Hll) as H. rewrite <- Ewl, NC_ll in H. exact H. Qed.

  (* [comment removed for export] *)
  Lemma zero_count_spec :
    arr_len (it_zero_count (arr_make 16 0)) = 16 /\ forall i, arr_get (it_zero_count (arr_make 16 0)) i = 0.
  Proof.
    unfold it_zero_count.
    apply (forZ_ind (fun _ a => arr_len a = 16 /\ forall i, arr_get a i = 0)).
    - intros i a Hi [L G]. split; [rewrite arr_len_set; exact L|].
      intros j. rewrite arr_get_set. destruct (_ && _); [reflexivity | apply G].
    - split; [apply arr_len_make | intros; apply arr_get_make].
    - unfold MAXBITS. lia.
  Qed.

  (* [comment removed for export] *)
  Definition CNT : arr := it_count lens lens_ofs codes (it_zero_count (arr_make 16 0)).

  Lemma count_spec : arr_len CNT = 16 /\ forall l, 0 <= l <= 15 -> arr_get CNT l = W wl l.
  Proof.
    unfold CNT, it_count. pose proof zero_count_spec as [ZL ZG].
    enough (H : arr_len (forZ 0 codes (fun sym cnt => let l := arr_get lens (lens_ofs + sym) in
                                                    arr_set cnt l (wrap16 (arr_get cnt l + 1)))
                              (it_zero_count (arr_make 16 0))) = 16 /\
                forall l, 0 <= l <= 15 ->
                  arr_get (forZ 0 codes (fun sym cnt => let l := arr_get lens (lens_ofs + sym) in
                                                         arr_set cnt l (wrap16 (arr_get cnt l + 1)))
                                (it_zero_count (arr_make 16 0))) l = countz l (firstn (Z.to_nat codes) ll)).
    { destruct H as [L G]. split; [exact L|]. intros l Hl. rewrite G by lia.
      rewrite <- ll_length, firstn_all. symmetry. apply W_count. lia. }
    apply (forZ_ind (fun sym c => arr_len c = 16 /\ forall l, 0 <= l <= 15 -> arr_get c l = countz l (firstn (Z.to_nat sym) ll))).
    - intros i c Hi [L G]. cbn zeta. split; [rewrite arr_len_set; exact L|].
      intros l Hl. pose proof (Hlens (lens_ofs + i) ltac:(lia)) as R.
      replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
      rewrite countz_firstn_S by (rewrite ll_length; lia).
      rewrite nth_ll by lia. rewrite Z2Nat.id by lia.
      rewrite arr_get_set. unfold arr_inb. rewrite L.
      rewrite G by lia.
      assert (B : 0 <= countz (arr_get lens (lens_ofs + i)) (firstn (Z.to_nat i) ll) <= i).
      { split; [apply countz_nonneg|].
        pose proof (countz_le_length (arr_get lens (lens_ofs + i)) (firstn (Z.to_nat i) ll)).
        unfold zlength in H. rewrite firstn_length, ll_length in H. lia. }
      rewrite wrap16_small by lia.
      destruct (Z.eqb_spec (arr_get lens (lens_ofs + i)) l) as [E|E].
      + rewrite <- E. destruct (Z.leb_spec 0 (arr_get lens (lens_ofs + i))); [|lia].
        destruct (Z.ltb_spec (arr_get lens (lens_ofs + i)) 16); [|lia]. cbn [andb]. rewrite Z.eqb_refl. lia.
      + cbn [andb]. rewrite G by lia. destruct (Z.eqb_spec l (arr_get lens (lens_ofs + i))); [congruence|]. lia.
    - split; [exact ZL|]. intros l Hl. rewrite ZG. change (firstn (Z.to_nat 0) ll) with (@nil Z). rewrite countz_nil. reflexivity.
    - lia.
  Qed.

  Section WithCount.
    Variable C : arr.
    Hypothesis HC : forall l, 0 <= l <= 15 -> arr_get C l = W wl l.
    #[local] Set Default Proof Using "Hcodes Hlens Ell Ewl HC".

    (* [comment removed for export] *)
    Lemma find_max_spec : it_find_max C = MAXL wl.
    Proof.
      pose proof (MAXL_spec wl HW HL) as [M1 [M2 M3]]. unfold it_find_max, MAXBITS.
      assert (G : forall m, MAXL wl <= m <= 15 -> forall fuel, m - MAXL wl + 1 <= fuel ->
                loopZ fuel (fun max => if (1 <=? max) && (arr_get C max =? 0) then (true, max - 1) else (false, max)) m = MAXL wl).
      { intros m Hm. remember (Z.to_nat (m - MAXL wl)) as n eqn:Hn. revert m Hm Hn.
        induction n as [|n IH]; intros m Hm Hn fuel Hf.
        - replace m with (MAXL wl) by lia. rewrite loopZ_step by lia.
          destruct (Z.leb_spec 1 (MAXL wl)); cbn [andb]; [|reflexivity].
          rewrite HC by lia. destruct (Z.eqb_spec (W wl (MAXL wl)) 0); [|reflexivity]. specialize (M3 ltac:(lia)). lia.
        - rewrite loopZ_step by lia. destruct (Z.leb_spec 1 m); [|lia]. rewrite HC by lia.
          rewrite M2 by lia. cbn [andb Z.eqb]. apply IH; lia. }
      apply G; lia.
    Qed.

    (* [comment removed for export] *)
    Lemma find_min_spec : 1 <= MAXL wl -> it_find_min C (MAXL wl) = MINL wl.
    Proof.
      intros HM. pose proof (MINL_spec wl HW HL HM) as [A [B D]]. pose proof (MAXL_spec wl HW HL) as [M0 _]. unfold it_find_min.
      assert (G : forall m, 1 <= m <= MINL wl -> forall fuel, MINL wl - m + 1 <= fuel ->
                loopZ fuel (fun min => if (min <? MAXL wl) && (arr_get C min =? 0) then (true, min + 1) else (false, min)) m = MINL wl).
      { intros m Hm. remember (Z.to_nat (MINL wl - m)) as n eqn:Hn. revert m Hm Hn.
        pose proof (MAXL_spec wl HW HL) as [M1 _].
        induction n as [|n IH]; intros m Hm Hn fuel Hf.
        - replace m with (MINL wl) by lia. rewrite loopZ_step by lia.
          destruct (Z.ltb_spec (MINL wl) (MAXL wl)); cbn [andb]; [|reflexivity].
          rewrite HC by lia. destruct (Z.eqb_spec (W wl (MINL wl)) 0); [lia|reflexivity].
        - rewrite loopZ_step by lia. destruct (Z.ltb_spec m (MAXL wl)); [|lia]. rewrite HC by lia.
          rewrite D by lia. cbn [andb Z.eqb]. apply IH; lia. }
      apply G; lia.
    Qed.

    (* [comment removed for export] *)
    Definition Lft (m : Z) : Z := 2 ^ m - sumz (fun l => W wl l * 2 ^ (m - l)) 1 (m + 1).

    Lemma Lft_0 : Lft 0 = 1.
    Proof. unfold Lft. rewrite sumz_nil by lia. reflexivity. Qed.

    Lemma Lft_S : forall m, 1 <= m -> Lft m = 2 * Lft (m - 1) - W wl m.
    Proof.
      intros m Hm. unfold Lft. rewrite (sumz_snoc _ 1 m) by lia. replace (m - 1 + 1) with m by lia.
      rewrite Z.sub_diag. change (2 ^ 0) with 1.
      rewrite (sumz_ext (fun l => W wl l * 2 ^ (m - l)) (fun l => (W wl l * 2 ^ (m - 1 - l)) * 2) 1 m).
      2:{ intros i Hi. rewrite <- Z.mul_assoc. f_equal. replace (m - i) with ((m - 1 - i) + 1) by lia. rewrite Z.pow_add_r by lia. reflexivity. }
      rewrite sumz_scale. replace m with ((m - 1) + 1) at 1 by lia. rewrite Z.pow_add_r by lia. lia.
    Qed.

    Lemma Lft_15 : Lft 15 = LEFT wl.
    Proof. unfold Lft, ItDefs.LEFT. change (15 + 1) with 16. reflexivity. Qed.

    Lemma Lft_neg_persist : forall m m', 0 <= m <= m' -> Lft m < 0 -> Lft m' < 0.
    Proof.
      intros m m' H Hneg. remember (Z.to_nat (m' - m)) as n eqn:Hn. revert m' H Hn.
      induction n as [|n IH]; intros m' H Hn.
      - replace m' with m by lia. exact Hneg.
      - rewrite (Lft_S m') by lia. pose proof (IH (m' - 1) ltac:(lia) ltac:(lia)). pose proof (HW m'). lia.
    Qed.

    Lemma left_check_spec : it_left_check C = (if LEFT wl <? 0 then None else Some (LEFT wl)).
    Proof.
      unfold it_left_check, MAXBITS.
      set (F := fun st : Z * Z => let '(len, lft) := st in
             if len <=? 15 then let lft0 := Z.shiftl lft 1 in let lft1 := lft0 - arr_get C len in
                                if lft1 <? 0 then inr None else inl (len + 1, lft1)
             else inr (Some lft)).
      assert (G : forall m v, 1 <= m <= 16 -> v = Lft (m - 1) -> 0 <= v -> forall fuel, 17 - m <= fuel ->
                iterZ fuel F (fun st => Some (snd st)) (m, v) = (if LEFT wl <? 0 then None else Some (LEFT wl))).
      { intros m v Hm. remember (Z.to_nat (16 - m)) as n eqn:Hn. revert m v Hm Hn.
        induction n as [|n IH]; intros m v Hm Hn Hv Hpos fuel Hf.
        - replace m with 16 in * by lia. rewrite iterZ_step by lia. unfold F at 1.
          destruct (Z.leb_spec 16 15); [lia|]. replace (16 - 1) with 15 in Hv by lia. rewrite Lft_15 in Hv. subst v.
          destruct (Z.ltb_spec (LEFT wl) 0); [lia|reflexivity].
        - rewrite iterZ_step by lia. unfold F at 1. destruct (Z.leb_spec m 15); [|lia].
          rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. rewrite HC by lia.
          assert (E : v * 2 - W wl m = Lft m) by (rewrite (Lft_S m) by lia; subst v; lia). rewrite E.
          destruct (Z.ltb_spec (Lft m) 0).
          + pose proof (Lft_neg_persist m 15 ltac:(lia) ltac:(lia)) as P15. rewrite Lft_15 in P15.
            destruct (Z.ltb_spec (LEFT wl) 0); [reflexivity|lia].
          + apply IH; try lia. f_equal. lia. }
      apply G; [lia| rewrite <- Lft_0; f_equal; lia | lia | lia].
    Qed.

    (* [comment removed for export] *)
    Definition OFS : arr := it_offs C (arr_make 16 0).

    Lemma offs_spec : arr_len OFS = 16 /\ forall l, 1 <= l <= 15 -> arr_get OFS l = OFF wl l.
    Proof.
      unfold OFS, it_offs, MAXBITS. pose proof NZ_le_codes as NZC.
      apply (forZ_ind (fun len o => arr_len o = 16 /\ forall l, 1 <= l <= len -> arr_get o l = OFF wl l)).
      - intros i o Hi [L G]. split; [rewrite arr_len_set; exact L|]. intros l Hl.
        rewrite arr_get_set. unfold arr_inb. rewrite L.
        destruct (Z.eqb_spec (i + 1) l) as [<-|NE].
        + destruct (Z.leb_spec 0 (i + 1)); [|lia]. destruct (Z.ltb_spec (i + 1) 16); [|lia]. cbn [andb].
          rewrite G, HC by lia. rewrite (OFF_step wl HW HL) by lia.
          pose proof (OFF_nonneg wl HW HL i). pose proof (HW i).
          pose proof (OFF_mono wl HW HL (i + 1) 16 ltac:(lia)) as M. rewrite (OFF_step wl HW HL) in M by lia.
          rewrite (NZ_eq wl HW HL) in NZC. apply wrap16_small. lia.
        + cbn [andb]. apply G. lia.
      - split; [rewrite arr_len_set; apply arr_len_make|]. intros l Hl. replace l with 1 by lia.
        rewrite arr_get_set_same by (rewrite arr_len_make; lia). symmetry. apply (OFF_1 wl HW HL).
      - lia.
    Qed.
  End WithCount.

  (* [comment removed for export] *)
  Definition SW (n : Z) : list (Z * Z) :=
    flat_map (fun s => let l := LofS ll s in
                       if l =? 0 then []
                       else [(OFF wl l + countz l (firstn (Z.to_nat s) ll), s)])
             (map Z.of_nat (seq 0 (Z.to_nat n))).

  Lemma SW_all : SW codes = sort_writes wl ll.
  Proof. unfold SW, sort_writes. rewrite NC_ll. reflexivity. Qed.

  Lemma SW_step : forall n, 0 <= n ->
    SW (n + 1) = SW n ++ (if LofS ll n =? 0 then [] else [(OFF wl (LofS ll n) + countz (LofS ll n) (firstn (Z.to_nat n) ll), n)]).
  Proof.
    intros n Hn. unfold SW. replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
    rewrite seq_S, map_app, flat_map_app. cbn [map flat_map Nat.add]. rewrite Z2Nat.id by lia.
    rewrite app_nil_r. reflexivity.
  Qed.

  Lemma sort_spec : forall (O : arr) (work : arr),
    arr_len O = 16 -> (forall l, 1 <= l <= 15 -> arr_get O l = OFF wl l) ->
    snd (it_sort lens lens_ofs codes (O, work)) = applyw (sort_writes wl ll) work.
  Proof.
    intros O work HOL HO. rewrite <- SW_all. unfold it_sort. pose proof NZ_le_codes as NZC. pose proof Hll as FL.
    enough (G : (fun sym ow =>
                   arr_len (fst ow) = 16 /\
                   (forall l, 1 <= l <= 15 -> arr_get (fst ow) l = OFF wl l + countz l (firstn (Z.to_nat sym) ll)) /\
                   snd ow = applyw (SW sym) work) codes
                (forZ 0 codes (fun sym ow => let '(offs, work0) := ow in
                   let l := arr_get lens (lens_ofs + sym) in
                   if negb (l =? 0) then
                     let o := arr_get offs l in (arr_set offs l (wrap16 (o + 1)), arr_set work0 o (wrap16 sym))
                   else (offs, work0)) (O, work))).
    { cbn beta in G. destruct G as [_ [_ G]]. exact G. }
    apply forZ_ind.
    - intros i [offs w] Hi [L [G E]]. cbn [fst snd] in L, G, E. cbn zeta.
      pose proof (Hlens (lens_ofs + i) ltac:(lia)) as R.
      rewrite <- (LofS_ll i) by lia.
      rewrite SW_step by lia. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
      rewrite <- (LofS_ll i) in R by lia.
      destruct (Z.eqb_spec (LofS ll i) 0) as [Z0|NZ0]; cbn [negb fst snd].
      + rewrite app_nil_r. split; [exact L|]. split; [|exact E]. intros l Hl.
        rewrite countz_firstn_S by (rewrite ll_length; lia). replace (nth (Z.to_nat i) ll 0) with (LofS ll i) by reflexivity. rewrite Z0.
        destruct (Z.eqb_spec l 0); [lia|]. rewrite G by lia. lia.
      + pose proof (sidx_range ll FL i ltac:(rewrite NC_ll; lia) NZ0) as [SR LR].
        unfold sidx in SR. rewrite <- Ewl in SR. rewrite <- G in SR by lia.
        pose proof (OFF_mono wl HW HL (LofS ll i + 1) 16 ltac:(lia)) as M. rewrite (NZ_eq wl HW HL) in NZC.
        pose proof (OFF_nonneg wl HW HL (LofS ll i)) as ON.
        split; [rewrite arr_len_set; exact L|]. split.
        * intros l Hl. rewrite arr_get_set. unfold arr_inb. rewrite L.
          rewrite countz_firstn_S by (rewrite ll_length; lia). replace (nth (Z.to_nat i) ll 0) with (LofS ll i) by reflexivity.
          destruct (Z.eqb_spec (LofS ll i) l) as [EQ|NE].
          -- rewrite <- EQ. destruct (Z.leb_spec 0 (LofS ll i)); [|lia]. destruct (Z.ltb_spec (LofS ll i) 16); [|lia]. cbn [andb].
             rewrite Z.eqb_refl. rewrite wrap16_small by lia. rewrite G by lia. lia.
          -- cbn [andb]. destruct (Z.eqb_spec l (LofS ll i)); [congruence|]. rewrite G by lia. lia.
        * rewrite applyw_snoc, <- E. rewrite G by lia. rewrite (wrap16_small i) by lia. reflexivity.
    - cbn [fst snd]. split; [exact HOL|]. split; [|reflexivity]. intros l Hl. rewrite HO by lia. change (firstn (Z.to_nat 0) ll) with (@nil Z). rewrite countz_nil. lia.
    - lia.
  Qed.
End Pre.
