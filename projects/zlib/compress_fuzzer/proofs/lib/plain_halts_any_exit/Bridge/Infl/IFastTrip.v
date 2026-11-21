(** * Bridge.Infl.IFastTrip — pair I16: one trip of [inflate_fast]'s loop, S5 vs RT.

    [ft_trip]: from related states ([frel], [rng]) with room for one match
    ([out + 258 <= N]), a trip of RT's [if_body] that reaches the bottom ([BodyOk]) or ends
    the block ([BodyEob]) is matched by S5's [fast_trip] ([FCont] / [FBreak _ TYPE None]),
    with the states related again, the bit position [Q] advanced by at most 48 and [out] by
    at most 258.  RT's other outcomes ([BodyBad], [BodyFuel]) need no match: the caller
    excludes them.

    Built from the decode levels bottom-up: distance tail (copy), distance base, distance
    leaf/root, length extra bits, length leaf/root. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsIn InflateFast Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv IFastKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Ltac conjs := repeat match goal with |- _ /\ _ => split end.

Section Trip.
Variables (x : IF.ffx) (c : RIF.IfCtx) (sS : IS.inflate_state) (N : Z).
Hypothesis X : xrel x c sS N.

Lemma ft_refill : forall f s, frel N f s -> rng s ->
  frel N (IF.fpull2_if x f) (RIF.if_refill15 c s) /\ rng (RIF.if_refill15 c s)
  /\ 15 <= RIF.f_bits (RIF.if_refill15 c s) /\ Q (RIF.if_refill15 c s) = Q s
  /\ RIF.f_out (RIF.if_refill15 c s) = RIF.f_out s /\ IF.f_len (IF.fpull2_if x f) = IF.f_len f.
Proof.
  intros f s F R. pose proof (rg_bits _ R) as Rb.
  unfold IF.fpull2_if, RIF.if_refill15. rewrite (fr_bits _ _ _ F).
  destruct (Z.ltb_spec (RIF.f_bits s) 15) as [Hb|Hb].
  - destruct (fk_pull x c sS N f s X F R ltac:(lia)) as (F1 & R1 & B1 & I1 & Q1).
    destruct (fk_pull x c sS N _ _ X F1 R1 ltac:(lia)) as (F2 & R2 & B2 & I2 & Q2).
    conjs; first [exact F2 | exact R2 | lia | reflexivity].
  - conjs; first [exact F | exact R | lia | reflexivity].
Qed.

Lemma ft_load2 : forall e f s, frel N f s -> rng s -> 0 <= e <= 15 ->
  frel N (sd_load2 x e f) (rd_load2 c e s) /\ rng (rd_load2 c e s) /\ e <= RIF.f_bits (rd_load2 c e s)
  /\ Q (rd_load2 c e s) = Q s /\ RIF.f_out (rd_load2 c e s) = RIF.f_out s
  /\ IF.f_dist (sd_load2 x e f) = IF.f_dist f /\ IF.f_len (sd_load2 x e f) = IF.f_len f.
Proof.
  intros e f s F R He. pose proof (rg_bits _ R) as Rb.
  unfold sd_load2, rd_load2. rewrite (fr_bits _ _ _ F).
  destruct (Z.ltb_spec (RIF.f_bits s) e) as [Hb|Hb].
  - destruct (fk_pull x c sS N f s X F R ltac:(lia)) as (F1 & R1 & B1 & I1 & Q1).
    cbv zeta. rewrite (fr_bits _ _ _ F1).
    destruct (Z.ltb_spec (RIF.f_bits (RIF.if_load1 c s)) e) as [Hb1|Hb1].
    + destruct (fk_pull x c sS N _ _ X F1 R1 ltac:(lia)) as (F2 & R2 & B2 & I2 & Q2).
      conjs; first [exact F2 | exact R2 | lia | reflexivity].
    + conjs; first [exact F1 | exact R1 | lia | reflexivity].
  - conjs; first [exact F | exact R | lia | reflexivity].
Qed.

(** The copy: the window branch is BAD on RT's side ([whave = 0]); the direct copy is
    [len] single-byte copies on both sides. *)
Lemma ft_dist_tail : forall len f s D,
  frel N f s -> rng s -> IF.f_dist f = D -> IF.f_len f = len -> 1 <= D <= 32768 -> 0 <= len <= 258 ->
  RIF.f_out s + 258 <= N ->
  match rd_tail c len s D with
  | RIF.BodyOk s' => exists f', sd_tail x f = IF.FCont f' /\ frel N f' s' /\ rng s'
                     /\ Q s' = Q s /\ RIF.f_out s' = RIF.f_out s + len
  | _ => True
  end.
Proof.
  intros len f s D F R HD HL HDr HLr Hout.
  pose proof (rg_out _ R) as Ro. pose proof (xr_Nlt _ _ _ _ X) as HN.
  unfold rd_tail, sd_tail. cbv zeta.
  rewrite (xr_fbeg _ _ _ _ X), (xr_beg _ _ _ _ X), (fr_out _ _ _ F), HD, !Z.sub_0_r.
  rewrite (wrap32_id (RIF.f_out s)) by lia. rewrite (RBa.u32_id (RIF.f_out s)) by lia.
  destruct (Z.ltb_spec (RIF.f_out s) D) as [Hw|Hw].
  - unfold rd_win. cbv zeta. rewrite (xr_whave _ _ _ _ X), (xr_sane _ _ _ _ X).
    rewrite (RBa.u32_id (D - RIF.f_out s)) by lia.
    replace (0 <? D - RIF.f_out s) with true by (symmetry; apply Z.ltb_lt; lia).
    exact I.
  - destruct (Z_lt_le_dec len 3) as [Hl3|Hl3].
    + rewrite fk_copydirect_none by lia. exact I.
    + rewrite fk_copydirect_ok by lia. cbv beta iota.
      eexists. split; [reflexivity|].
      rewrite fk_copy_s5 by (cbn [IF.f_len IF.fset_from]; lia).
      change (IF.f_len (IF.fset_from f ?v)) with (IF.f_len f). rewrite HL.
      destruct (fk_cpn x c (Z.to_nat len) N (IF.fset_from f (IF.FOut (RIF.f_out s - D))) s
                  (RIF.f_out s - D) (fk_set_from N f s _ F) eq_refl ltac:(lia) ltac:(lia))
        as [Fc _].
      pose proof (RIF.if_copyn_out (Z.to_nat len) c s (RIF.SrcOut (RIF.f_out s - D))) as Co.
      pose proof (RIF.if_copyn_in (Z.to_nat len) c s (RIF.SrcOut (RIF.f_out s - D))) as Ci.
      destruct (RIF.if_copyn_bits (Z.to_nat len) c s (RIF.SrcOut (RIF.f_out s - D))) as [Cb Ch].
      destruct R as [Rb Rh Ri _].
      conjs.
      * apply fk_set_len. exact Fc.
      * constructor; [rewrite Cb; exact Rb | rewrite Cb, Ch; exact Rh | rewrite Ci; exact Ri | lia].
      * unfold Q. rewrite Ci, Cb. reflexivity.
      * lia.
Qed.

Lemma ft_dist_base : forall len f s h,
  frel N f s -> rng s -> IF.f_len f = len -> 0 <= len <= 258 -> RIF.f_out s + 258 <= N ->
  dent h -> Z.land (RBa.c_op h) 16 <> 0 ->
  match rd_base c len s h with
  | RIF.BodyOk s' => exists f', sd_base x (RBa.code_enc h) f = IF.FCont f' /\ frel N f' s' /\ rng s'
                     /\ Q s' = Q s + Z.land (RBa.c_op h) 15 /\ RIF.f_out s' = RIF.f_out s + len
  | _ => True end.
Proof.
  intros len f s h F R HL HLr Hout Hd H16.
  destruct Hd as (Hr & Hop0 & Hbase & _). destruct (Hbase H16) as (He13 & Hv1 & Hv2).
  pose proof Hr as (Hro & Hrb & Hrv).
  assert (He0 : 0 <= Z.land (RBa.c_op h) 15) by (apply Z.land_nonneg; lia).
  unfold rd_base, sd_base. cbv zeta.
  rewrite (fk_code_val h Hr), (fk_code_op h Hr).
  set (e := Z.land (RBa.c_op h) 15) in *.
  destruct (ft_load2 e (IF.fset_dist f (RBa.c_val h)) s (fk_set_dist N f s _ F) R ltac:(lia))
    as (F2 & R2 & B2 & Q2 & O2 & D2 & L2).
  cbn [IF.f_dist IF.f_len IF.fset_dist] in D2, L2.
  remember (rd_load2 c e s) as s2 eqn:Es2.
  remember (sd_load2 x e (IF.fset_dist f (RBa.c_val h))) as f2 eqn:Ef2.
  rewrite D2, (fr_hold _ _ _ F2), fk_zmask by lia. rewrite fk_low_wrap32 by lia.
  unfold RIF.if_low.
  pose proof (fk_low_range (RIF.f_hold s2) e ltac:(lia)) as Hlow.
  rewrite (wrap32_id (RBa.c_val h + Z.land (RIF.f_hold s2) (Z.shiftl 1 e - 1))) by lia.
  destruct (fk_drop_rng e s2 R2 ltac:(lia)) as (R3 & B3 & Q3).
  pose proof (ft_dist_tail len (IF.fdrop (IF.fset_dist f2 (RBa.c_val h + Z.land (RIF.f_hold s2) (Z.shiftl 1 e - 1))) e)
                (RIF.if_drop e s2) (RBa.c_val h + Z.land (RIF.f_hold s2) (Z.shiftl 1 e - 1))
                (fk_drop N _ _ e (fk_set_dist N f2 s2 _ F2)) R3 eq_refl ltac:(cbn; lia)
                ltac:(lia) HLr ltac:(cbn [RIF.if_drop RIF.f_out]; lia)) as T.
  destruct (rd_tail c len (RIF.if_drop e s2) _) as [s'|s'|s' m|]; try exact I.
  destruct T as (f' & Hf' & F' & R' & Q' & O'). exists f'.
  conjs; try first [exact Hf' | exact F' | exact R' | lia].
  cbn [RIF.if_drop RIF.f_out] in O'. lia.
Qed.

Lemma ft_dist_leaf : forall k k' len f s h, frel N f s -> rng s -> IF.f_len f = len -> 0 <= len <= 258 ->
  RIF.f_out s + 258 <= N -> dent h -> tsub KDists (RBa.c_op h) = false -> RBa.c_bits h <= RIF.f_bits s ->
  match RIF.if_dodist (S k) c len s h with
  | RIF.BodyOk s' => exists f', IF.dodist (S k') x sS (RBa.code_enc h) f = IF.FCont f' /\ frel N f' s'
       /\ rng s' /\ Q s + RBa.c_bits h <= Q s' <= Q s + RBa.c_bits h + 13 /\ RIF.f_out s' = RIF.f_out s + len
  | _ => True end.
Proof.
  intros k k' len f s h F R HL HLr Hout Hd Hts Hcb.
  pose proof Hd as (Hr & Hop0 & Hbase & Hch). pose proof Hr as (Hro & Hrb & Hrv).
  rewrite fk_rd_S, fk_sd_S, (fk_code_bits h Hr).
  pose proof (fk_drop N f s (RBa.c_bits h) F) as F1.
  destruct (fk_drop_rng (RBa.c_bits h) s R ltac:(lia)) as (R1 & B1 & Q1).
  remember (RIF.if_drop (RBa.c_bits h) s) as s1 eqn:Es1.
  remember (IF.fdrop f (RBa.c_bits h)) as f1 eqn:Ef1.
  unfold rd_lvl, sd_lvl. rewrite (fk_code_op h Hr).
  destruct (Z.eqb_spec (Z.land (RBa.c_op h) 16) 0) as [E16|E16]; cbn [negb].
  - destruct (Z.eqb_spec (Z.land (RBa.c_op h) 64) 0) as [E64|E64].
    + exfalso. specialize (Hch E16 E64). unfold tsub in Hts. rewrite Hch in Hts. discriminate.
    + exact I.
  - destruct (Hbase E16) as (He13 & _ & _).
    assert (He0 : 0 <= Z.land (RBa.c_op h) 15) by (apply Z.land_nonneg; lia).
    pose proof (ft_dist_base len f1 s1 h F1 R1 ltac:(rewrite Ef1; exact HL) HLr
                  ltac:(rewrite Es1; exact Hout) Hd E16) as T.
    destruct (rd_base c len s1 h) as [s'|s'|s' m|]; try exact I.
    destruct T as (f' & Hf' & F' & R' & Q' & O'). exists f'.
    conjs; try first [exact Hf' | exact F' | exact R' | lia].
    rewrite O', Es1. reflexivity.
Qed.

Lemma ft_dist_root : forall len f s i, frel N f s -> rng s -> IF.f_len f = len -> 0 <= len <= 258 ->
  RIF.f_out s + 258 <= N -> 15 <= RIF.f_bits s -> 0 <= i < 2 ^ IS.is_distbits sS ->
  match RIF.if_dodist RIF.tbl_fuel c len s (RIF.f_dcode c i) with
  | RIF.BodyOk s' => exists f', IF.dodist 4 x sS (RBa.code_enc (RIF.f_dcode c i)) f = IF.FCont f'
       /\ frel N f' s' /\ rng s' /\ Q s <= Q s' <= Q s + 28 /\ RIF.f_out s' = RIF.f_out s + len
  | _ => True end.
Proof.
  intros len f s i F R HL HLr Hout H15 Hi.
  pose proof (proj1 (xr_dview _ _ _ _ X)) as Hroot.
  destruct (fk_view_at _ _ _ _ i (xr_dview _ _ _ _ X) (xr_dx _ _ _ _ X) Hi) as (Heq & Hk & Hb & Hsub).
  cbn [kent] in Hk.
  set (h := RIF.f_dcode c i) in *.
  pose proof (proj1 Hk) as Hr. pose proof Hr as (Hro & Hrb & Hrv).
  unfold RIF.tbl_fuel.
  destruct (tsub KDists (RBa.c_op h)) eqn:Ets.
  - destruct (Hsub eq_refl) as (Hb2 & Ho1 & Ho2 & Hy).
    rewrite fk_rd_S, fk_sd_S, (fk_code_bits h Hr).
    pose proof (fk_drop N f s (RBa.c_bits h) F) as F1.
    destruct (fk_drop_rng (RBa.c_bits h) s R ltac:(lia)) as (R1 & B1 & Q1).
    remember (RIF.if_drop (RBa.c_bits h) s) as s1 eqn:Es1.
    remember (IF.fdrop f (RBa.c_bits h)) as f1 eqn:Ef1.
    unfold rd_lvl, sd_lvl. rewrite (fk_code_op h Hr), (fk_code_val h Hr).
    unfold tsub in Ets. apply Z.eqb_eq in Ets. destruct (fk_l240 _ Ets) as (H16 & _ & H64).
    rewrite H16, H64. cbn [negb Z.eqb].
    rewrite (fr_hold _ _ _ F1), fk_zmask by lia. unfold RIF.if_low.
    pose proof (fk_low_range (RIF.f_hold s1) (RBa.c_op h) ltac:(lia)) as Hyr.
    set (y := Z.land (RIF.f_hold s1) (Z.shiftl 1 (RBa.c_op h) - 1)) in *.
    destruct (Hy y Hyr) as (Heq2 & Hk2 & Hb3 & Hts2). cbn [kent] in Hk2.
    pose proof (proj1 Hk2) as (Hro2 & Hrb2 & Hrv2).
    rewrite Heq2.
    pose proof (ft_dist_leaf 14 2 len f1 s1 (RIF.f_dcode c (RBa.c_val h + y)) F1 R1
                  ltac:(rewrite Ef1; exact HL) HLr ltac:(rewrite Es1; exact Hout) Hk2 Hts2 ltac:(lia)) as T.
    destruct (RIF.if_dodist 15 c len s1 _) as [s'|s'|s' m|]; try exact I.
    destruct T as (f' & Hf' & F' & R' & Q' & O'). exists f'.
    conjs; try first [exact Hf' | exact F' | exact R' | lia].
    rewrite O', Es1. reflexivity.
  - pose proof (ft_dist_leaf 15 3 len f s h F R HL HLr Hout Hk Ets ltac:(lia)) as T.
    destruct (RIF.if_dodist 16 c len s h) as [s'|s'|s' m|]; try exact I.
    destruct T as (f' & Hf' & F' & R' & Q' & O'). exists f'.
    conjs; try first [exact Hf' | exact F' | exact R' | lia].
Qed.

(** Length extra bits, after the (optional) byte load. *)
Lemma ft_len_ext_core : forall fa sa e v, frel N fa sa -> rng sa -> 0 <= e <= RIF.f_bits sa -> e <= 5 ->
  IF.f_len fa = v -> 0 <= v -> v + 2 ^ e <= 259 ->
  frel N (IF.fdrop (IF.fset_len fa (wrap32 (IF.f_len fa + Z.land (wrap32 (IF.f_hold fa)) (IF.zmask e)))) e)
         (RIF.if_drop e sa)
  /\ rng (RIF.if_drop e sa)
  /\ IF.f_len (IF.fdrop (IF.fset_len fa (wrap32 (IF.f_len fa + Z.land (wrap32 (IF.f_hold fa)) (IF.zmask e)))) e)
     = v + RIF.if_low e sa
  /\ 0 <= v + RIF.if_low e sa <= 258
  /\ Q (RIF.if_drop e sa) = Q sa + e /\ RIF.f_out (RIF.if_drop e sa) = RIF.f_out sa.
Proof.
  intros fa sa e v F R He He5 Hv Hv0 Hv2.
  destruct (fk_drop_rng e sa R He) as (R1 & B1 & Q1).
  pose proof (fk_low_range (RIF.f_hold sa) e ltac:(lia)) as Hlow.
  assert (Hlen : wrap32 (IF.f_len fa + Z.land (wrap32 (IF.f_hold fa)) (IF.zmask e)) = v + RIF.if_low e sa).
  { rewrite Hv, (fr_hold _ _ _ F), fk_zmask by lia. rewrite fk_low_wrap32 by lia.
    unfold RIF.if_low. apply wrap32_id. lia. }
  rewrite Hlen. unfold RIF.if_low in *.
  conjs.
  - apply fk_drop, fk_set_len, F.
  - exact R1.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
Qed.

Lemma ft_len_ext : forall f s h, frel N f s -> rng s -> lent h -> Z.land (RBa.c_op h) 16 <> 0 ->
  frel N (sl_ext x (RBa.code_enc h) f) (snd (rl_ext c h s)) /\ rng (snd (rl_ext c h s))
  /\ IF.f_len (sl_ext x (RBa.code_enc h) f) = fst (rl_ext c h s) /\ 0 <= fst (rl_ext c h s) <= 258
  /\ Q (snd (rl_ext c h s)) = Q s + Z.land (RBa.c_op h) 15 /\ RIF.f_out (snd (rl_ext c h s)) = RIF.f_out s.
Proof.
  intros f s h F R Hl H16.
  destruct Hl as (Hr & Hbase & _). destruct (Hbase H16) as (He5 & Hv).
  pose proof Hr as (Hro & Hrb & Hrv). pose proof (rg_bits _ R) as Rb.
  assert (He0 : 0 <= Z.land (RBa.c_op h) 15) by (apply Z.land_nonneg; lia).
  unfold sl_ext, rl_ext. cbv zeta.
  rewrite (fk_code_val h Hr), (fk_code_op h Hr).
  set (e := Z.land (RBa.c_op h) 15) in *.
  destruct (Z.eqb_spec e 0) as [E0|E0]; cbn [negb fst snd].
  - rewrite E0 in Hv. change (2 ^ 0) with 1 in Hv.
    conjs; try first [apply fk_set_len; exact F | exact R | reflexivity | lia].
  - change (IF.f_bits (IF.fset_len f ?v)) with (IF.f_bits f). rewrite (fr_bits _ _ _ F).
    destruct (Z.ltb_spec (RIF.f_bits s) e) as [Hb|Hb]; cbv beta iota.
    + destruct (fk_pull x c sS N _ s X (fk_set_len N f s (RBa.c_val h) F) R ltac:(lia))
        as (F1 & R1 & B1 & I1 & Q1).
      destruct (ft_len_ext_core (IF.fpull x (IF.fset_len f (RBa.c_val h))) (RIF.if_load1 c s) e (RBa.c_val h)
                  F1 R1 ltac:(lia) He5 eq_refl ltac:(lia) ltac:(lia)) as (F2 & R2 & L2 & HL2 & Q2 & O2).
      conjs; try first [exact F2 | exact R2 | exact L2 | lia]. rewrite O2. reflexivity.
    + destruct (ft_len_ext_core (IF.fset_len f (RBa.c_val h)) s e (RBa.c_val h)
                  (fk_set_len N f s _ F) R ltac:(lia) He5 eq_refl ltac:(lia) ltac:(lia))
        as (F2 & R2 & L2 & HL2 & Q2 & O2).
      conjs; try first [exact F2 | exact R2 | exact L2 | lia].
Qed.

Lemma ft_len_dist : forall len f s, frel N f s -> rng s -> IF.f_len f = len -> 0 <= len <= 258 ->
  RIF.f_out s + 258 <= N ->
  match rl_dist c len s with
  | RIF.BodyOk s' => exists f', sl_dist x sS f = IF.FCont f' /\ frel N f' s' /\ rng s'
       /\ Q s <= Q s' <= Q s + 28 /\ RIF.f_out s' = RIF.f_out s + len
  | RIF.BodyEob _ => False
  | _ => True end.
Proof.
  intros len f s F R HL HLr Hout.
  unfold rl_dist, sl_dist. cbv zeta.
  destruct (ft_refill f s F R) as (F3 & R3 & B3 & Q3 & O3 & L3).
  remember (RIF.if_refill15 c s) as s3 eqn:Es3. remember (IF.fpull2_if x f) as f3 eqn:Ef3.
  rewrite (fr_hold _ _ _ F3), (xr_dmask _ _ _ _ X), (xr_fdmask _ _ _ _ X).
  pose proof (proj1 (xr_dview _ _ _ _ X)) as Hroot.
  set (i := Z.land (RIF.f_hold s3) (Z.shiftl 1 (IS.is_distbits sS) - 1)) in *.
  assert (Hi : 0 <= i < 2 ^ IS.is_distbits sS) by (apply fk_low_range; lia).
  destruct (fk_view_at _ _ _ _ i (xr_dview _ _ _ _ X) (xr_dx _ _ _ _ X) Hi) as (Heq & _ & _ & _).
  rewrite Heq.
  pose proof (ft_dist_root len f3 s3 i F3 R3 ltac:(rewrite L3; exact HL) HLr
                ltac:(rewrite O3; exact Hout) B3 Hi) as T.
  pose proof (fk_dodist_not_eob RIF.tbl_fuel c len s3 (RIF.f_dcode c i)) as NE.
  destruct (RIF.if_dodist RIF.tbl_fuel c len s3 (RIF.f_dcode c i)) as [s'|s'|s' m|]; try exact I.
  - destruct T as (f' & Hf' & F' & R' & Q' & O'). exists f'.
    conjs; try first [exact Hf' | exact F' | exact R' | lia].
  - exact (NE s' eq_refl).
Qed.

Lemma ft_len_leaf : forall k k' f s h, frel N f s -> rng s -> RIF.f_out s + 258 <= N ->
  lent h -> tsub KLens (RBa.c_op h) = false -> RBa.c_bits h <= RIF.f_bits s ->
  match RIF.if_dolen (S k) c s h with
  | RIF.BodyOk s' => exists f', IF.dolen (S k') x sS (RBa.code_enc h) f = IF.FCont f' /\ frel N f' s'
       /\ rng s' /\ Q s + RBa.c_bits h <= Q s' <= Q s + RBa.c_bits h + 33
       /\ RIF.f_out s <= RIF.f_out s' <= RIF.f_out s + 258
  | RIF.BodyEob s' => exists f', IF.dolen (S k') x sS (RBa.code_enc h) f = IF.FBreak f' IS.TYPE None
       /\ frel N f' s' /\ rng s' /\ Q s' = Q s + RBa.c_bits h /\ RIF.f_out s' = RIF.f_out s
  | _ => True end.
Proof.
  intros k k' f s h F R Hout Hl Hts Hcb.
  pose proof Hl as (Hr & Hbase & Hch). pose proof Hr as (Hro & Hrb & Hrv).
  rewrite fk_rl_S, fk_sl_S, (fk_code_bits h Hr).
  pose proof (fk_drop N f s (RBa.c_bits h) F) as F1.
  destruct (fk_drop_rng (RBa.c_bits h) s R ltac:(lia)) as (R1 & B1 & Q1).
  assert (O1 : RIF.f_out (RIF.if_drop (RBa.c_bits h) s) = RIF.f_out s) by reflexivity.
  remember (RIF.if_drop (RBa.c_bits h) s) as s1 eqn:Es1.
  remember (IF.fdrop f (RBa.c_bits h)) as f1 eqn:Ef1.
  pose proof (rg_out _ R1) as Ro1.
  unfold rl_lvl, sl_lvl. rewrite (fk_code_op h Hr).
  destruct (Z.eqb_spec (RBa.c_op h) 0) as [E0|E0]; cbv beta iota.
  - unfold sl_lit. cbv zeta. rewrite (fk_code_val h Hr).
    eexists. split; [reflexivity|].
    change (IF.f_out (IF.fset_ob ?g ?v)) with (IF.f_out g). rewrite fk_wrap8_u8.
    destruct R1 as [Rb1 Rh1 Ri1 _].
    conjs.
    + apply fk_put; [exact F1|lia].
    + constructor; cbn [RIF.if_put RIF.f_in RIF.f_out RIF.f_hold RIF.f_bits]; first [exact Rb1 | exact Rh1 | exact Ri1 | lia].
    + unfold Q in *. cbn [RIF.if_put RIF.f_in RIF.f_bits]. lia.
    + unfold Q in *. cbn [RIF.if_put RIF.f_in RIF.f_bits]. lia.
    + cbn [RIF.if_put RIF.f_out]. lia.
    + cbn [RIF.if_put RIF.f_out]. lia.
  - destruct (Z.eqb_spec (Z.land (RBa.c_op h) 16) 0) as [E16|E16]; cbn [negb].
    + destruct (Z.eqb_spec (Z.land (RBa.c_op h) 64) 0) as [E64|E64].
      * exfalso. specialize (Hch E0 E16 E64). unfold tsub in Hts.
        rewrite (proj2 (Z.eqb_neq _ _) E0), Hch in Hts. discriminate.
      * destruct (Z.eqb_spec (Z.land (RBa.c_op h) 32) 0) as [E32|E32]; cbn [negb].
        -- exact I.
        -- eexists. split; [reflexivity|].
           conjs; try first [exact F1 | exact R1 | lia].
    + destruct (ft_len_ext f1 s1 h F1 R1 Hl E16) as (F2 & R2 & L2 & HL2 & Q2 & O2).
      destruct (rl_ext c h s1) as [L s2] eqn:Ee. cbn [fst snd] in F2, R2, L2, HL2, Q2, O2.
      cbv beta iota.
      remember (sl_ext x (RBa.code_enc h) f1) as f2 eqn:Ef2.
      destruct (Hbase E16) as (He5 & _).
      assert (He0 : 0 <= Z.land (RBa.c_op h) 15) by (apply Z.land_nonneg; lia).
      pose proof (ft_len_dist L f2 s2 F2 R2 L2 HL2 ltac:(lia)) as T.
      destruct (rl_dist c L s2) as [s'|s'|s' m|]; try exact I; [|destruct T].
      destruct T as (f' & Hf' & F' & R' & Q' & O'). exists f'.
      conjs; try first [exact Hf' | exact F' | exact R' | lia].
Qed.

Lemma ft_len_root : forall f s i, frel N f s -> rng s -> RIF.f_out s + 258 <= N -> 15 <= RIF.f_bits s ->
  0 <= i < 2 ^ IS.is_lenbits sS ->
  match RIF.if_dolen RIF.tbl_fuel c s (RIF.f_lcode c i) with
  | RIF.BodyOk s' => exists f', IF.dolen 4 x sS (RBa.code_enc (RIF.f_lcode c i)) f = IF.FCont f'
       /\ frel N f' s' /\ rng s' /\ Q s <= Q s' <= Q s + 48 /\ RIF.f_out s <= RIF.f_out s' <= RIF.f_out s + 258
  | RIF.BodyEob s' => exists f', IF.dolen 4 x sS (RBa.code_enc (RIF.f_lcode c i)) f = IF.FBreak f' IS.TYPE None
       /\ frel N f' s' /\ rng s' /\ Q s <= Q s' <= Q s + 48 /\ RIF.f_out s' = RIF.f_out s
  | _ => True end.
Proof.
  intros f s i F R Hout H15 Hi.
  pose proof (proj1 (xr_lview _ _ _ _ X)) as Hroot.
  destruct (fk_view_at _ _ _ _ i (xr_lview _ _ _ _ X) (xr_lx _ _ _ _ X) Hi) as (Heq & Hk & Hb & Hsub).
  cbn [kent] in Hk.
  set (h := RIF.f_lcode c i) in *.
  pose proof (proj1 Hk) as Hr. pose proof Hr as (Hro & Hrb & Hrv).
  unfold RIF.tbl_fuel.
  destruct (tsub KLens (RBa.c_op h)) eqn:Ets.
  - destruct (Hsub eq_refl) as (Hb2 & Ho1 & Ho2 & Hy).
    rewrite fk_rl_S, fk_sl_S, (fk_code_bits h Hr).
    pose proof (fk_drop N f s (RBa.c_bits h) F) as F1.
    destruct (fk_drop_rng (RBa.c_bits h) s R ltac:(lia)) as (R1 & B1 & Q1).
    assert (O1 : RIF.f_out (RIF.if_drop (RBa.c_bits h) s) = RIF.f_out s) by reflexivity.
    remember (RIF.if_drop (RBa.c_bits h) s) as s1 eqn:Es1.
    remember (IF.fdrop f (RBa.c_bits h)) as f1 eqn:Ef1.
    unfold rl_lvl, sl_lvl. rewrite (fk_code_op h Hr), (fk_code_val h Hr).
    unfold tsub in Ets. apply andb_prop in Ets as [Ets1 Ets2].
    apply Z.eqb_eq in Ets2. destruct (fk_l240 _ Ets2) as (H16 & _ & H64).
    rewrite H16, H64. destruct (RBa.c_op h =? 0); [discriminate|]. cbn [negb Z.eqb].
    rewrite (fr_hold _ _ _ F1), fk_zmask by lia. unfold RIF.if_low.
    pose proof (fk_low_range (RIF.f_hold s1) (RBa.c_op h) ltac:(lia)) as Hyr.
    set (y := Z.land (RIF.f_hold s1) (Z.shiftl 1 (RBa.c_op h) - 1)) in *.
    destruct (Hy y Hyr) as (Heq2 & Hk2 & Hb3 & Hts2). cbn [kent] in Hk2.
    pose proof (proj1 Hk2) as (Hro2 & Hrb2 & Hrv2).
    rewrite Heq2.
    pose proof (ft_len_leaf 14 2 f1 s1 (RIF.f_lcode c (RBa.c_val h + y)) F1 R1
                  ltac:(rewrite O1; exact Hout) Hk2 Hts2 ltac:(lia)) as T.
    destruct (RIF.if_dolen 15 c s1 _) as [s'|s'|s' m|]; try exact I;
      destruct T as (f' & Hf' & F' & R' & Q' & O'); exists f';
      conjs; try first [exact Hf' | exact F' | exact R' | lia].
  - pose proof (ft_len_leaf 15 3 f s h F R Hout Hk Ets ltac:(lia)) as T.
    destruct (RIF.if_dolen 16 c s h) as [s'|s'|s' m|]; try exact I;
      destruct T as (f' & Hf' & F' & R' & Q' & O'); exists f';
      conjs; try first [exact Hf' | exact F' | exact R' | lia].
Qed.

(** One trip. *)
Lemma ft_trip : forall f s, frel N f s -> rng s -> RIF.f_out s + 258 <= N ->
  match RIF.if_body c s with
  | RIF.BodyOk s' => exists f', IF.fast_trip x sS f = IF.FCont f' /\ frel N f' s' /\ rng s'
       /\ Q s <= Q s' <= Q s + 48 /\ RIF.f_out s <= RIF.f_out s' <= RIF.f_out s + 258
  | RIF.BodyEob s' => exists f', IF.fast_trip x sS f = IF.FBreak f' IS.TYPE None /\ frel N f' s' /\ rng s'
       /\ Q s <= Q s' <= Q s + 48 /\ RIF.f_out s' = RIF.f_out s
  | _ => True end.
Proof.
  intros f s F R Hout.
  rewrite fk_body_eq, fk_trip_eq.
  destruct (ft_refill f s F R) as (F0 & R0 & B0 & Q0 & O0 & _).
  remember (RIF.if_refill15 c s) as s0 eqn:Es0. remember (IF.fpull2_if x f) as f0 eqn:Ef0.
  rewrite (fr_hold _ _ _ F0), (xr_lmask _ _ _ _ X), (xr_flmask _ _ _ _ X).
  pose proof (proj1 (xr_lview _ _ _ _ X)) as Hroot.
  set (i := Z.land (RIF.f_hold s0) (Z.shiftl 1 (IS.is_lenbits sS) - 1)) in *.
  assert (Hi : 0 <= i < 2 ^ IS.is_lenbits sS) by (apply fk_low_range; lia).
  destruct (fk_view_at _ _ _ _ i (xr_lview _ _ _ _ X) (xr_lx _ _ _ _ X) Hi) as (Heq & _ & _ & _).
  rewrite Heq.
  pose proof (ft_len_root f0 s0 i F0 R0 ltac:(lia) B0 Hi) as T.
  destruct (RIF.if_dolen RIF.tbl_fuel c s0 (RIF.f_lcode c i)) as [s'|s'|s' m|]; try exact I;
    destruct T as (f' & Hf' & F' & R' & Q' & O'); exists f';
    conjs; try first [exact Hf' | exact F' | exact R' | lia].
Qed.

End Trip.
