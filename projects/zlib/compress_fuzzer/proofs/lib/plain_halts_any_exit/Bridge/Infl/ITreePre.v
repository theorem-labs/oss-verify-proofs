(** * Bridge.Infl.ITreePre — pair I15, part 1: the table kit and RT's pre-loop phases.

    The route of pair I15 (S5's [inflate_table] against RT's [it_model]): S5 already proves
    its own [inflate_table] equal to an abstract description [ItDefs.it_abs] (return code,
    the list of table writes, the new [next], the new [bits]; [ItSim2.inflate_table_abs]).
    These files prove RT's [it_model] follows the same abstract description, trip by trip,
    reusing S5's abstract theory ([ItMath], [ItSort], [ItSim1], [ItSim2]) for every fact
    about the abstract quantities.

    This file: the table relation [TRel] between an S5 table (absolute indices) and RT's
    shifted view (written back by [codes_wb]); its write and fill lemmas; and RT's
    pre-loop phases ([it_count], [it_findmax], [it_findmin], [it_kraft], [it_offs],
    [it_sort]) against the abstract [W], [MAXL], [MINL], [LEFT], [OFF], [wsym]. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees InftreesCoverage ItDefs ItGen ItMath ItSort ItSimPre ItSim1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Inftrees Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module RIT := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.Inftrees.

(** S5's codetype as RT's [type] argument (the same as [ITree.ty_rt]). *)
Definition rtype (ty : IS.codetype) : Z :=
  match ty with IS.CODES => RIT.CT_CODES | IS.LENS => RIT.CT_LENS | IS.DISTS => RIT.CT_DISTS end.

(* ------------------------------------------------------------------------- *)
(* 1.  Codes and the table relation                                          *)
(* ------------------------------------------------------------------------- *)

Lemma code_pack_enc : forall op bits val,
  IS.code_pack op bits val = RBa.code_enc (RBa.mkCodeT op bits val).
Proof.
  intros op bits val. unfold IS.code_pack, RBa.code_enc, RBa.mkCodeT, RBa.u8, RBa.u16, wrap8, wrap16.
  cbn [RBa.c_op RBa.c_bits RBa.c_val].
  change 255 with (2 ^ 8 - 1). change 65535 with (2 ^ 16 - 1). rewrite !land_ones' by lia. reflexivity.
Qed.

Lemma code_rng_mk : forall op bits val, code_rng (RBa.mkCodeT op bits val).
Proof.
  intros op bits val. unfold code_rng, RBa.mkCodeT, RBa.u8, RBa.u16. cbn [RBa.c_op RBa.c_bits RBa.c_val].
  pose proof (Z.mod_pos_bound op 256 ltac:(lia)). pose proof (Z.mod_pos_bound bits 256 ltac:(lia)).
  pose proof (Z.mod_pos_bound val 65536 ltac:(lia)). lia.
Qed.

Section Kit.
  Variable tc : RBa.ztbl.
  Variable table : Z.

  (** S5's table [a] (absolute indices) against RT's view [t] (indices from [table]),
      written back into [tc]: they agree on all of [[0, ENOUGH)]. *)
  Definition TRel (a : arr) (t : RBa.ztbl) : Prop :=
    arr_len a = ENOUGH /\ tbl_rel a (RI.codes_wb tc table t) 0 ENOUGH.

  Definition TRng (t : RBa.ztbl) : Prop := forall j, code_rng (t j).

  Lemma TRel_set : forall a t off c, 0 <= table -> 0 <= off -> TRel a t ->
    TRel (arr_set a (table + off) (RBa.code_enc c)) (RBa.tset t off c).
  Proof.
    intros a t off c Ht Ho [L R]. split; [rewrite arr_len_set; exact L|].
    intros j Hj. rewrite arr_get_set. unfold arr_inb. rewrite L. unfold RI.codes_wb.
    destruct (Z.eqb_spec (table + off) j) as [E|E].
    - subst j. destruct (Z.leb_spec 0 (table + off)); [|lia].
      destruct (Z.ltb_spec (table + off) ENOUGH); [|lia]. cbn [andb].
      destruct (Z.leb_spec table (table + off)); [|lia].
      replace (table + off - table) with off by lia. rewrite RBa.tset_same. reflexivity.
    - cbn [andb]. rewrite (R j Hj). unfold RI.codes_wb.
      destruct (Z.leb_spec table j); [|reflexivity].
      rewrite RBa.tset_other by lia. reflexivity.
  Qed.

  Lemma TRng_set : forall t off c, code_rng c -> TRng t -> TRng (RBa.tset t off c).
  Proof.
    intros t off c Hc Ht j. unfold RBa.tset. destruct (Z.eqb j off); [exact Hc | apply Ht].
  Qed.

  (** RT's [it_fill] against S5's write list [fill_list] (the C's descending [fill]). *)
  Lemma TRel_fill : forall m a t bi incr h, 0 <= table -> 0 <= bi -> 0 <= incr -> code_rng h ->
    TRel a t -> TRng t ->
    TRel (applyw (fill_list (RBa.code_enc h) incr (table + bi) m) a) (RIT.it_fill m t bi incr h) /\
    TRng (RIT.it_fill m t bi incr h).
  Proof.
    induction m as [|m IH]; intros a t bi incr h Ht Hb Hi Hh HT HR.
    - unfold fill_list. cbn [seq List.rev map]. unfold applyw. cbn [fold_left RIT.it_fill].
      split; assumption.
    - rewrite fill_list_S, applyw_cons. cbn [RIT.it_fill].
      replace (table + bi + Z.of_nat m * incr) with (table + (bi + Z.of_nat m * incr)) by lia.
      apply IH; try assumption.
      + apply TRel_set; [assumption | nia | assumption].
      + apply TRng_set; assumption.
  Qed.
End Kit.

(* ------------------------------------------------------------------------- *)
(* 2.  Small RT/S5 equations                                                 *)
(* ------------------------------------------------------------------------- *)

Lemma shift_down_ib : forall h w n, (w + 2 <= n)%nat ->
  RIT.it_shift_down n h (2 ^ Z.of_nat w) = ib w h.
Proof.
  intros h w. induction w as [|w IH]; intros n Hn.
  - destruct n as [|n]; [lia|]. cbn [RIT.it_shift_down]. rewrite land_pow2_eq0 by lia. cbn [ib].
    destruct (Z.odd (h / 2 ^ Z.of_nat 0)); cbn [negb].
    + destruct n as [|n]; [lia|]. cbn [RIT.it_shift_down].
      change (Z.shiftr (2 ^ Z.of_nat 0) 1) with 0. rewrite Z.land_0_r. reflexivity.
    + reflexivity.
  - destruct n as [|n]; [lia|]. cbn [RIT.it_shift_down]. rewrite land_pow2_eq0 by lia. cbn [ib].
    destruct (Z.odd (h / 2 ^ Z.of_nat (S w))); cbn [negb]; [|reflexivity].
    rewrite Z.shiftr_div_pow2 by lia. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    replace (2 * 2 ^ Z.of_nat w / 2 ^ 1) with (2 ^ Z.of_nat w)
      by (rewrite Z.mul_comm; apply eq_sym, Z.div_mul; lia).
    apply IH. lia.
Qed.

(** RT's backwards increment is S5's ([inftrees.c:226-233]). *)
Lemma rt_rev_incr : forall h len, 1 <= len <= 15 ->
  RIT.it_rev_incr h len =
  (if negb (it_incr_back h len =? 0) then Z.land h (it_incr_back h len - 1) + it_incr_back h len else 0).
Proof.
  intros h len Hl. unfold RIT.it_rev_incr. rewrite it_incr_back_ib by lia.
  assert (E : Z.shiftl 1 (len - 1) = 2 ^ Z.of_nat (Z.to_nat (len - 1)))
    by (rewrite Z.shiftl_1_l, Z2Nat.id by lia; reflexivity).
  rewrite E, shift_down_ib by lia.
  destruct (Z.eqb_spec (ib (Z.to_nat (len - 1)) h) 0); reflexivity.
Qed.

Lemma rt_enough : forall ty u, RIT.it_enough (rtype ty) u = it_not_enough ty u.
Proof.
  intros ty u. destruct ty; unfold RIT.it_enough, it_not_enough, rtype; cbn [Z.eqb andb orb].
  - reflexivity.
  - rewrite Bool.orb_false_r. reflexivity.
  - reflexivity.
Qed.

Lemma rt_incomplete : forall ty lft mx,
  RIT.it_incomplete (rtype ty) lft mx = (0 <? lft) && (codetype_eqb ty IS.CODES || negb (mx =? 1)).
Proof. intros ty lft mx. destruct ty; reflexivity. Qed.

Lemma hf_nonneg : forall wl k, 0 <= hf wl k.
Proof.
  intros wl k. unfold hf. destruct (k =? 0); [lia|]. cbv zeta.
  destruct (_ <? _); [|lia]. unfold rev. apply brev_bound.
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  Write lists on RT arrays                                              *)
(* ------------------------------------------------------------------------- *)

Definition zapplyw (ws : list (Z * Z)) (z : RBa.zarr) : RBa.zarr :=
  fold_left (fun a iv => RBa.zset a (fst iv) (snd iv)) ws z.

Lemma zapplyw_snoc : forall ws i v z, zapplyw (ws ++ [(i, v)]) z = RBa.zset (zapplyw ws z) i v.
Proof. intros. unfold zapplyw. rewrite fold_left_app. reflexivity. Qed.

Lemma zapplyw_ext : forall ws z1 z2, (forall j, z1 j = z2 j) -> forall j, zapplyw ws z1 j = zapplyw ws z2 j.
Proof.
  induction ws as [|[i v] ws IH]; intros z1 z2 H j; [apply H|].
  cbn [zapplyw fold_left fst snd]. apply IH. intros j'. unfold RBa.zset. rewrite H. reflexivity.
Qed.

Lemma applyw_zapplyw : forall ws a z, (forall j, 0 <= j < arr_len a -> arr_get a j = z j) ->
  forall j, 0 <= j < arr_len a -> arr_get (applyw ws a) j = zapplyw ws z j.
Proof.
  induction ws as [|[i v] ws IH]; intros a z H j Hj; [apply H, Hj|].
  rewrite applyw_cons. cbn [zapplyw fold_left fst snd]. fold (zapplyw ws (RBa.zset z i v)).
  rewrite <- (arr_len_set a i v) in Hj. apply (IH _ _); [|exact Hj].
  intros j' Hj'. rewrite arr_len_set in Hj'. rewrite arr_get_set. unfold arr_inb, RBa.zset.
  destruct (Z.eqb_spec i j') as [<-|NE].
  - rewrite Z.eqb_refl. destruct (Z.leb_spec 0 i); [|lia]. destruct (Z.ltb_spec i (arr_len a)); [|lia]. reflexivity.
  - cbn [andb]. destruct (Z.eqb_spec j' i); [congruence|]. apply H, Hj'.
Qed.

Lemma zcount_map : forall n i (f : Z -> Z) b,
  RIT.zcount n i f b = countz b (map (fun k => f (i + Z.of_nat k)) (seq 0 n)).
Proof.
  induction n as [|n IH]; intros i f b; cbn [RIT.zcount seq map].
  - rewrite countz_nil. reflexivity.
  - rewrite countz_cons, IH. rewrite <- seq_shift, map_map. rewrite Z.add_0_r, Z.eqb_sym. f_equal. f_equal.
    apply map_ext. intros k. f_equal. lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* 4.  RT's pre-loop phases                                                  *)
(* ------------------------------------------------------------------------- *)

Section RtPre.
  Variable lens : arr.
  Variable lens_ofs codes : Z.
  Variable ll wl : list Z.
  Variable lensR : RBa.zarr.
  Hypothesis Hcodes : 0 <= codes <= 288.
  Hypothesis Hlens : forall i, lens_ofs <= i < lens_ofs + codes -> 0 <= arr_get lens i <= 15.
  Hypothesis Ell : ll = lens_list lens lens_ofs codes.
  Hypothesis Ewl : wl = wl_of ll.
  Hypothesis Hlr : forall i, 0 <= i < codes -> lensR i = arr_get lens (lens_ofs + i).
  #[local] Set Default Proof Using "Hcodes Hlens Ell Ewl Hlr".

  Let HW := HW lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl.
  Let HL := HL lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl.

  Lemma rt_count : forall l, 0 <= l <= 15 -> RIT.it_count (Z.to_nat codes) 0 lensR RBa.zzero l = W wl l.
  Proof.
    intros l Hl. rewrite RIT.it_count_zzero, zcount_map.
    rewrite (W_count lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl l Hl). rewrite Ell. unfold lens_list.
    f_equal. apply map_ext_in. intros k Hk. apply in_seq in Hk. rewrite Hlr by lia. f_equal; lia.
  Qed.

  Section WithCnt.
    Variable cnt : RBa.zarr.
    Hypothesis HC : forall l, 1 <= l <= 15 -> cnt l = W wl l.
    #[local] Set Default Proof Using "Hcodes Hlens Ell Ewl Hlr HC".

    Lemma rt_findmax : RIT.it_findmax 15 RIT.MAXBITS cnt = MAXL wl.
    Proof.
      pose proof (MAXL_spec wl HW HL) as [M1 [M2 M3]].
      assert (G : forall n m, Z.of_nat n = m -> m <= 15 -> MAXL wl <= m -> RIT.it_findmax n m cnt = MAXL wl).
      { induction n as [|n IH]; intros m Hn Hm HMm; cbn [RIT.it_findmax].
        - lia.
        - rewrite HC by lia. destruct (Z.eq_dec m (MAXL wl)) as [E|E].
          + subst m. rewrite E. destruct (Z.eqb_spec (W wl (MAXL wl)) 0); [specialize (M3 ltac:(lia)); lia | reflexivity].
          + rewrite M2 by lia. cbn [Z.eqb]. apply IH; lia. }
      apply G; unfold RIT.MAXBITS; lia.
    Qed.

    Lemma rt_findmin : 1 <= MAXL wl -> RIT.it_findmin 16 1 (MAXL wl) cnt = MINL wl.
    Proof.
      intros HM. pose proof (MINL_spec wl HW HL HM) as [A [B D]]. pose proof (MAXL_spec wl HW HL) as [M1 _].
      assert (G : forall n m, 1 <= m <= MINL wl -> MINL wl - m < Z.of_nat n ->
                RIT.it_findmin n m (MAXL wl) cnt = MINL wl).
      { induction n as [|n IH]; intros m Hm Hf; cbn [RIT.it_findmin]; [lia|].
        rewrite Z.geb_leb. destruct (Z.leb_spec (MAXL wl) m); [lia|].
        rewrite HC by lia. destruct (Z.eq_dec m (MINL wl)) as [E|E].
        - subst m. destruct (Z.eqb_spec (W wl (MINL wl)) 0); [lia|reflexivity].
        - rewrite D by lia. cbn [Z.eqb]. apply IH; lia. }
      apply G; [lia | cbn; lia].
    Qed.

    Lemma rt_kraft : RIT.it_kraft 15 1 1 cnt = (if LEFT wl <? 0 then None else Some (LEFT wl)).
    Proof.
      pose proof (count_spec lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) as [_ CC].
      set (C := CNT lens lens_ofs codes) in CC.
      pose proof (Lft_S lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl C CC) as LS.
      pose proof (Lft_15 lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl C CC) as L15.
      pose proof (Lft_neg_persist lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl C CC) as LN.
      pose proof (Lft_0 lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl C CC) as L0.
      assert (G : forall n m v, 1 <= m <= 16 -> Z.of_nat n = 16 - m -> v = Lft wl (m - 1) -> 0 <= v ->
                RIT.it_kraft n m v cnt = (if LEFT wl <? 0 then None else Some (LEFT wl))).
      { induction n as [|n IH]; intros m v Hm Hn Hv Hpos; cbn [RIT.it_kraft].
        - replace (m - 1) with 15 in Hv by lia. rewrite L15 in Hv. subst v.
          destruct (Z.ltb_spec (LEFT wl) 0); [lia|reflexivity].
        - rewrite HC by lia.
          assert (E : v * 2 - W wl m = Lft wl m) by (rewrite (LS m) by lia; subst v; lia). rewrite E.
          destruct (Z.ltb_spec (Lft wl m) 0).
          + pose proof (LN m 15 ltac:(lia) ltac:(lia)) as P. rewrite L15 in P.
            destruct (Z.ltb_spec (LEFT wl) 0); [reflexivity|lia].
          + apply IH; try lia. f_equal. lia. }
      apply G; try lia. rewrite <- L0. f_equal.
    Qed.

    Lemma rt_offs : forall l, 1 <= l <= 15 -> RIT.it_offs 14 1 cnt (RBa.zset RBa.zzero 1 0) l = OFF wl l.
    Proof.
      assert (G : forall n len o, 1 <= len -> len + Z.of_nat n = 15 -> (forall l, 1 <= l <= len -> o l = OFF wl l) ->
                forall l, 1 <= l <= 15 -> RIT.it_offs n len cnt o l = OFF wl l).
      { induction n as [|n IH]; intros len o H1 H2 Ho l Hl; cbn [RIT.it_offs].
        - apply Ho. lia.
        - apply IH; try lia. intros l' Hl'. unfold RBa.zset. destruct (Z.eqb_spec l' (len + 1)) as [->|NE].
          + rewrite Ho, HC by lia. rewrite (OFF_step wl HW HL) by lia. reflexivity.
          + apply Ho. lia. }
      apply G; try lia. intros l Hl. replace l with 1 by lia. rewrite RBa.zset_same. symmetry. apply (OFF_1 wl HW HL).
    Qed.
  End WithCnt.

  Lemma rt_sort_gen : forall n i o w, 0 <= i -> i + Z.of_nat n <= codes ->
    (forall l, 1 <= l <= 15 -> o l = OFF wl l + countz l (firstn (Z.to_nat i) ll)) ->
    (forall j, w j = zapplyw (SW ll wl i) RBa.zzero j) ->
    forall j, snd (RIT.it_sort n i lensR o w) j = zapplyw (SW ll wl (i + Z.of_nat n)) RBa.zzero j.
  Proof.
    pose proof (ll_length lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) as LLen.
    induction n as [|n IH]; intros i o w Hi Hn Ho Hw j; cbn [RIT.it_sort].
    - rewrite Z.add_0_r. apply Hw.
    - assert (Hl : lensR i = LofS ll i)
        by (rewrite Hlr by lia; rewrite (LofS_ll lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) by lia; reflexivity).
      pose proof (Hlens (lens_ofs + i) ltac:(lia)) as R.
      rewrite <- (LofS_ll lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) in R by lia.
      rewrite Hl. replace (i + Z.of_nat (S n)) with ((i + 1) + Z.of_nat n) by lia.
      destruct (Z.eqb_spec (LofS ll i) 0) as [Z0|NZ0].
      + apply IH; try lia.
        * intros l' Hl'. rewrite Ho by lia. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
          rewrite countz_firstn_S by lia. change (nth (Z.to_nat i) ll 0) with (LofS ll i). rewrite Z0.
          destruct (Z.eqb_spec l' 0); lia.
        * intros j'. rewrite (SW_step lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl i) by lia.
          rewrite Z0. cbn [Z.eqb]. rewrite app_nil_r. apply Hw.
      + apply IH; try lia.
        * intros l' Hl'. unfold RBa.zset. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
          rewrite countz_firstn_S by lia. change (nth (Z.to_nat i) ll 0) with (LofS ll i).
          destruct (Z.eqb_spec l' (LofS ll i)) as [->|NE].
          -- rewrite Ho by lia. rewrite ?Z.eqb_refl. lia.
          -- rewrite Ho by lia. lia.
        * intros j'. rewrite (SW_step lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl i) by lia.
          destruct (Z.eqb_spec (LofS ll i) 0); [congruence|].
          rewrite zapplyw_snoc. unfold RBa.zset. rewrite Hw. rewrite Ho by lia. reflexivity.
  Qed.

  Lemma rt_work : forall o, (forall l, 1 <= l <= 15 -> o l = OFF wl l) ->
    forall j, 0 <= j < NZ wl -> snd (RIT.it_sort (Z.to_nat codes) 0 lensR o RBa.zzero) j = wsym wl ll j.
  Proof.
    intros o Ho j Hj.
    assert (HO0 : forall l, 1 <= l <= 15 -> o l = OFF wl l + countz l (firstn (Z.to_nat 0) ll)).
    { intros l Hl. rewrite Ho by lia. change (firstn (Z.to_nat 0) ll) with (@nil Z). rewrite countz_nil. lia. }
    rewrite (rt_sort_gen (Z.to_nat codes) 0 o RBa.zzero ltac:(lia) ltac:(lia) HO0 (fun j' => eq_refl)).
    rewrite Z.add_0_l, Z2Nat.id by lia.
    rewrite (SW_all lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl).
    pose proof (NZ_le_codes lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) as NZC.
    rewrite <- (applyw_zapplyw (sort_writes wl ll) (arr_make 288 0) RBa.zzero)
      by (try (rewrite arr_len_make; lia); intros; rewrite arr_get_make; reflexivity).
    pose proof (Hll lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) as FL.
    rewrite Ewl in Hj |- *. apply (sorted_work ll FL); [rewrite arr_len_make; rewrite <- Ewl; lia | exact Hj].
  Qed.
End RtPre.
