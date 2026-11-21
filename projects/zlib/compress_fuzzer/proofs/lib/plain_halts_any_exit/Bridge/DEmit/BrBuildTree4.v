(** * Bridge.DEmit.BrBuildTree4 — pair D28: [gen_codes] and [bi_reverse], S5 vs RT.

    - [bi_reverse]: both run the [do..while] body [max 1 len] times; S5
      tests the counter inside its loop, RT counts the trips up front.
    - [next_code] (S5 [gen_codes_loop1], 16 steps guarded by
      [bits <= MAX_BITS]; RT [gc_next], 15 steps): the same values at
      indices [1..15], both 0 at index 0.
    - the assignment loop (S5 [gen_codes_loop2], [max_code + 1] steps; RT
      [gc_assign], [L_CODES + 3] steps): the same writes, given that every
      code length up to [max_code] is at most 15 (S5's [bt_safe] says so),
      which keeps [next_code[len]] inside S5's 16-entry array. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees TreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require BrBits.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs DTreeDefs BrBuildTree0 BrBuildTree1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma wrap32_u32 : forall v, wrap32 v = Base.u32 v.
Proof. intros v. rewrite wrap32_mod. reflexivity. Qed.

(* ------------------------------------------------------------------------- *)
(* 1.  [bi_reverse]                                                          *)
(* ------------------------------------------------------------------------- *)

Lemma bi_rev_loop_go : forall n code res len, Z.of_nat n = Z.max len 1 ->
  DT.bi_reverse_loop n code res len = Z.shiftr (RT.bi_rev_go n code res) 1.
Proof.
  induction n as [|n IH]; intros code res len Hn; [lia|].
  cbn [DT.bi_reverse_loop RT.bi_rev_go]. cbv zeta. rewrite wrap32_u32.
  destruct (Z.ltb_spec 0 (len - 1)) as [C|C].
  - apply IH. lia.
  - assert (n = 0%nat) by lia. subst n. reflexivity.
Qed.

Lemma bi_reverse_agree : forall code len, DT.bi_reverse code len = RT.bi_reverse code len.
Proof.
  intros code len. unfold DT.bi_reverse, RT.bi_reverse.
  replace (Z.max 1 len) with (Z.max len 1) by lia.
  apply bi_rev_loop_go. lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  [next_code]                                                           *)
(* ------------------------------------------------------------------------- *)

Lemma gc_loop1_rel : forall G F BC blc NC nc code bits,
  arr_rel BC blc 0 16 -> arr_rel NC nc 0 16 -> arr_len NC = 16 -> 1 <= bits ->
  Z.to_nat (16 - bits) = G -> (G <= F)%nat ->
  arr_rel (DT.gen_codes_loop1 F BC NC code bits) (RT.gc_next G bits code blc nc) 0 16
  /\ arr_len (DT.gen_codes_loop1 F BC NC code bits) = 16.
Proof.
  induction G as [|G IH]; intros F BC blc NC nc code bits RB RN LN Hb HG HF.
  - destruct F as [|F]; cbn [DT.gen_codes_loop1 RT.gc_next]; [split; assumption|].
    replace (bits <=? DS.MAX_BITS) with false by (symmetry; apply Z.leb_gt; unfold DS.MAX_BITS; lia).
    split; assumption.
  - destruct F as [|F]; [lia|]. cbn [DT.gen_codes_loop1 RT.gc_next].
    replace (bits <=? DS.MAX_BITS) with true by (symmetry; apply Z.leb_le; unfold DS.MAX_BITS; lia).
    cbv zeta. rewrite (RB (bits - 1)) by lia. rewrite wrap32_u32, BrBits.wrap16_u16.
    apply IH; [exact RB | | rewrite arr_len_set; exact LN | lia | lia | lia].
    apply arr_rel_set; [exact RN | intros; lia].
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  The assignment loop                                                   *)
(* ------------------------------------------------------------------------- *)

Lemma bt_set_Code : forall s t FC DL HP HL HM DP BC OL SL MC i v,
  DS.set_Code (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t i v
  = bt_upd s t (arr_set FC i (wrap16 v)) DL HP HL HM DP BC OL SL MC.
Proof. intros. apply bt_set_Freq. Qed.

Lemma gc_loop2_rel : forall F G s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc NC nc mc n,
  brel t FC DL HP DP BC T hp dep blc -> arr_rel NC nc 0 16 -> arr_len NC = 16 ->
  0 <= n -> mc < DS.sd_elems t ->
  (forall i, n <= i <= mc -> 0 <= arr_get DL i <= 15) ->
  (Z.to_nat (mc + 1 - n) <= F)%nat -> (Z.to_nat (mc + 1 - n) <= G)%nat ->
  exists FC',
    DT.gen_codes_loop2 F (bt_upd s0 t FC DL HP HL HM DP BC OL SL MC) t NC mc n
      = bt_upd s0 t FC' DL HP HL HM DP BC OL SL MC
    /\ brel t FC' DL HP DP BC (RT.gc_assign G n mc T nc) hp dep blc.
Proof.
  induction F as [|F IH]; intros G s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc NC nc mc n
    H RN LN Hn Hmc Hl HF HG.
  - assert (mc < n) by lia. exists FC. destruct G as [|G]; cbn [DT.gen_codes_loop2 RT.gc_assign].
    + split; [reflexivity | exact H].
    + replace (mc <? n) with true by (symmetry; apply Z.ltb_lt; lia). split; [reflexivity | exact H].
  - pose proof (tsize_le t) as Ht. destruct (elems_range t) as [HE Hts].
    destruct (Z.leb_spec n mc) as [C|C].
    + destruct G as [|G]; [lia|]. cbn [DT.gen_codes_loop2 RT.gc_assign].
      replace (n <=? mc) with true by (symmetry; apply Z.leb_le; lia).
      replace (mc <? n) with false by (symmetry; apply Z.ltb_ge; lia).
      cbv zeta. autorewrite with btupd. unfold RT.t_len.
      rewrite <- (brel_dl_get _ _ _ _ _ _ _ _ _ _ n H) by lia.
      pose proof (Hl n ltac:(lia)) as Hln.
      destruct (Z.eqb_spec (arr_get DL n) 0) as [Z0|Z0].
      * apply IH; [exact H | exact RN | exact LN | lia | lia | intros; apply Hl; lia | lia | lia].
      * try rewrite bt_set_Code. rewrite (RN (arr_get DL n)) by lia.
        rewrite t_setcode_setfreq, bi_reverse_agree.
        destruct (IH G s0 t (arr_set FC n (wrap16 (RT.bi_reverse (nc (arr_get DL n)) (arr_get DL n)))) DL HP HL HM DP
                    BC OL SL MC (RT.t_setfreq T n (RT.bi_reverse (nc (arr_get DL n)) (arr_get DL n))) hp dep blc
                    (arr_set NC (arr_get DL n) (wrap16 (nc (arr_get DL n) + 1)))
                    (Base.zset nc (arr_get DL n) (Base.u16 (nc (arr_get DL n) + 1))) mc (n + 1))
          as (FC' & E1 & E2).
        { apply brel_fc_set; [exact H | lia]. }
        { rewrite BrBits.wrap16_u16. apply arr_rel_set; [exact RN | intros; lia]. }
        { rewrite arr_len_set; exact LN. }
        { lia. } { lia. } { intros; apply Hl; lia. } { lia. } { lia. }
        exists FC'. split; [exact E1 | exact E2].
    + exists FC. cbn [DT.gen_codes_loop2]. replace (n <=? mc) with false by (symmetry; apply Z.leb_gt; lia).
      destruct G as [|G]; cbn [RT.gc_assign]; [split; [reflexivity | exact H]|].
      replace (mc <? n) with true by (symmetry; apply Z.ltb_lt; lia). split; [reflexivity | exact H].
Qed.

(* ------------------------------------------------------------------------- *)
(* 4.  [gen_codes]                                                           *)
(* ------------------------------------------------------------------------- *)

Lemma gen_codes_rel : forall s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc mc,
  brel t FC DL HP DP BC T hp dep blc -> -1 <= mc < DS.sd_elems t ->
  (forall i, 0 <= i <= mc -> 0 <= arr_get DL i <= 15) ->
  exists FC',
    DT.gen_codes (bt_upd s0 t FC DL HP HL HM DP BC OL SL MC) t mc = bt_upd s0 t FC' DL HP HL HM DP BC OL SL MC
    /\ brel t FC' DL HP DP BC (RT.gen_codes T mc blc) hp dep blc.
Proof.
  intros s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc mc H Hmc Hl.
  destruct (elems_range t) as [HE Hts].
  unfold DT.gen_codes, RT.gen_codes. cbv zeta. autorewrite with btupd.
  destruct (gc_loop1_rel (Z.to_nat RT.MAX_BITS) 16 BC blc (arr_make (DS.MAX_BITS + 1) 0) Base.zzero 0 1
              (b_bc _ _ _ _ _ _ _ _ _ _ H)) as [R1 L1].
  { intros i Hi. rewrite arr_get_make. reflexivity. }
  { apply arr_len_make. }
  { lia. } { reflexivity. } { unfold RT.MAX_BITS; lia. }
  apply gc_loop2_rel; [exact H | exact R1 | exact L1 | lia | lia | exact Hl | lia | unfold RT.L_CODES; lia].
Qed.
