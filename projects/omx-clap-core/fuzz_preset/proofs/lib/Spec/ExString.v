From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjGrammar.
Import ListNotations.
Open Scope Z_scope.

Lemma jr_string_decode : forall z, fst (fst (jr_string z [])) = decode z.
Proof.
  intros z. unfold jr_string.
  destruct (scan z) as [q|] eqn:Es.
  - unfold jbind, jalloc, take. cbn -[decode]. destruct (decode z); reflexivity.
  - destruct (decode z) as [[s r]|] eqn:Ed; [|reflexivity].
    destruct (decode_stop z s r Ed) as (q & Hq & _). congruence.
Qed.

Lemma emit_emit : forall a b d, emit a (emit b d) = emit (a ++ b) d.
Proof. intros a b [[s r]|]; cbn; [rewrite app_assoc|]; reflexivity. Qed.

Lemma emit_none : forall a, emit a None = None.
Proof. reflexivity. Qed.

Lemma dec_quote : forall r, decode (34 :: r) = Some ([], r).
Proof. reflexivity. Qed.

Lemma dec_nil : decode [] = None.
Proof. reflexivity. Qed.

Lemma dec_ctl : forall b r, b < 32 -> decode (b :: r) = None.
Proof.
  intros b r H. cbn [decode].
  destruct (Z.eqb_spec b 34); [lia|]. destruct (Z.ltb_spec b 32); [reflexivity|lia].
Qed.

Lemma dec_plain : forall b r, 32 <= b -> b <> 34 -> b <> 92 -> decode (b :: r) = emit [b] (decode r).
Proof.
  intros b r H1 H2 H3. cbn [decode].
  destruct (Z.eqb_spec b 34); [lia|]. destruct (Z.ltb_spec b 32); [lia|].
  destruct (Z.eqb_spec b 92); [lia|]. reflexivity.
Qed.

Lemma dec_bs_end : decode [92] = None.
Proof. reflexivity. Qed.

Lemma dec_bs : forall e r, decode (92 :: e :: r) =
  if e =? 117 then
    match r with
    | _ :: _ :: _ :: _ :: r3 =>
      match hex4 r with
      | None => None
      | Some cp =>
        if cp =? 0 then None
        else if (55296 <=? cp) && (cp <? 56320) then
          match r3 with
          | _ :: _ :: _ :: _ :: _ :: _ :: r4 =>
            match low r3 with
            | Some lo => emit (utf8 (pair_cp cp lo)) (decode r4)
            | None => None
            end
          | _ => None
          end
        else if (56320 <=? cp) && (cp <? 57344) then None
        else emit (utf8 cp) (decode r3)
      end
    | _ => None
    end
  else
    match escape e with
    | Some c => emit [c] (decode r)
    | None => None
    end.
Proof. reflexivity. Qed.

Lemma escape_u : escape 117 = None.
Proof. reflexivity. Qed.

Lemma dec_esc : forall e c r, escape e = Some c -> decode (92 :: e :: r) = emit [c] (decode r).
Proof.
  intros e c r H. rewrite dec_bs. destruct (Z.eqb_spec e 117).
  - subst e. discriminate H.
  - rewrite H. reflexivity.
Qed.

Lemma dec_esc_bad : forall e r, escape e = None -> e <> 117 -> decode (92 :: e :: r) = None.
Proof.
  intros e r H1 H2. rewrite dec_bs. destruct (Z.eqb_spec e 117); [lia|]. rewrite H1. reflexivity.
Qed.

Lemma dec_u_short : forall r, (length r < 4)%nat -> decode (92 :: 117 :: r) = None.
Proof.
  intros r H. rewrite dec_bs. cbn [Z.eqb Pos.eqb].
  destruct r as [|a [|b [|c [|d r]]]]; cbn in H; try reflexivity; lia.
Qed.

Lemma dec_u4 : forall c0 c1 c2 c3 r, decode (92 :: 117 :: c0 :: c1 :: c2 :: c3 :: r) =
  match hex4 [c0; c1; c2; c3] with
  | None => None
  | Some cp =>
    if cp =? 0 then None
    else if (55296 <=? cp) && (cp <? 56320) then
      match r with
      | _ :: _ :: _ :: _ :: _ :: _ :: r4 =>
        match low r with
        | Some lo => emit (utf8 (pair_cp cp lo)) (decode r4)
        | None => None
        end
      | _ => None
      end
    else if (56320 <=? cp) && (cp <? 57344) then None
    else emit (utf8 cp) (decode r)
  end.
Proof. reflexivity. Qed.

Lemma dec_u_hnone : forall c0 c1 c2 c3 r, hex4 [c0; c1; c2; c3] = None ->
  decode (92 :: 117 :: c0 :: c1 :: c2 :: c3 :: r) = None.
Proof. intros c0 c1 c2 c3 r H. rewrite dec_u4, H. reflexivity. Qed.

Lemma dec_u_zero : forall c0 c1 c2 c3 r, hex4 [c0; c1; c2; c3] = Some 0 ->
  decode (92 :: 117 :: c0 :: c1 :: c2 :: c3 :: r) = None.
Proof. intros c0 c1 c2 c3 r H. rewrite dec_u4, H. reflexivity. Qed.

Lemma dec_u_dc : forall c0 c1 c2 c3 r cp, hex4 [c0; c1; c2; c3] = Some cp -> 56320 <= cp < 57344 ->
  decode (92 :: 117 :: c0 :: c1 :: c2 :: c3 :: r) = None.
Proof.
  intros c0 c1 c2 c3 r cp H Hc. rewrite dec_u4, H.
  destruct (Z.eqb_spec cp 0); [reflexivity|].
  destruct (Z.leb_spec 55296 cp); destruct (Z.ltb_spec cp 56320); cbn [andb]; try lia.
  destruct (Z.leb_spec 56320 cp); destruct (Z.ltb_spec cp 57344); cbn [andb]; try lia. reflexivity.
Qed.

Lemma dec_u_bmp : forall c0 c1 c2 c3 r cp, hex4 [c0; c1; c2; c3] = Some cp -> cp <> 0 -> ~ (55296 <= cp < 57344) ->
  decode (92 :: 117 :: c0 :: c1 :: c2 :: c3 :: r) = emit (utf8 cp) (decode r).
Proof.
  intros c0 c1 c2 c3 r cp H H0 Hc. rewrite dec_u4, H.
  destruct (Z.eqb_spec cp 0); [lia|].
  destruct (Z.leb_spec 55296 cp); destruct (Z.ltb_spec cp 56320); cbn [andb]; try lia;
  destruct (Z.leb_spec 56320 cp); destruct (Z.ltb_spec cp 57344); cbn [andb]; try lia; reflexivity.
Qed.

Lemma dec_u_pshort : forall c0 c1 c2 c3 r cp, hex4 [c0; c1; c2; c3] = Some cp -> 55296 <= cp < 56320 ->
  (length r < 6)%nat -> decode (92 :: 117 :: c0 :: c1 :: c2 :: c3 :: r) = None.
Proof.
  intros c0 c1 c2 c3 r cp H Hc Hl. rewrite dec_u4, H.
  destruct (Z.eqb_spec cp 0); [lia|].
  destruct (Z.leb_spec 55296 cp); destruct (Z.ltb_spec cp 56320); cbn [andb]; try lia.
  destruct r as [|a [|b [|c [|d [|e [|f r]]]]]]; cbn in Hl; try reflexivity; lia.
Qed.

Lemma dec_u_pair : forall c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 r cp, hex4 [c0; c1; c2; c3] = Some cp -> 55296 <= cp < 56320 ->
  decode (92 :: 117 :: c0 :: c1 :: c2 :: c3 :: d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: r) =
  match low [d0; d1; d2; d3; d4; d5] with
  | Some lo => emit (utf8 (pair_cp cp lo)) (decode r)
  | None => None
  end.
Proof.
  intros c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 r cp H Hc. rewrite dec_u4, H.
  destruct (Z.eqb_spec cp 0); [lia|].
  destruct (Z.leb_spec 55296 cp); destruct (Z.ltb_spec cp 56320); cbn [andb]; try lia. reflexivity.
Qed.

Lemma dec_u_hi : forall c0 c1 c2 c3 r cp, hex4 [c0; c1; c2; c3] = Some cp -> 55296 <= cp < 56320 ->
  decode (92 :: 117 :: c0 :: c1 :: c2 :: c3 :: r) =
  match r with
  | _ :: _ :: _ :: _ :: _ :: _ :: r4 =>
    match low r with
    | Some lo => emit (utf8 (pair_cp cp lo)) (decode r4)
    | None => None
    end
  | _ => None
  end.
Proof.
  intros c0 c1 c2 c3 r cp H Hc. rewrite dec_u4, H.
  destruct (Z.eqb_spec cp 0); [lia|].
  destruct (Z.leb_spec 55296 cp); destruct (Z.ltb_spec cp 56320); cbn [andb]; try lia. reflexivity.
Qed.

Lemma low_bs : forall d0 d1 r, d0 <> 92 -> low (d0 :: d1 :: r) = None.
Proof. intros d0 d1 r H. cbn [low]. destruct (Z.eqb_spec d0 92); [lia|]. reflexivity. Qed.

Lemma low_u : forall d0 d1 r, d1 <> 117 -> low (d0 :: d1 :: r) = None.
Proof.
  intros d0 d1 r H. cbn [low]. destruct (Z.eqb_spec d1 117); [lia|]. rewrite andb_false_r. reflexivity.
Qed.

Lemma low_hex : forall d2 d3 d4 d5, low [92; 117; d2; d3; d4; d5] =
  match hex4 [d2; d3; d4; d5] with
  | Some lo => if (56320 <=? lo) && (lo <=? 57343) then Some lo else None
  | None => None
  end.
Proof. reflexivity. Qed.

Lemma lor_disj : forall a b n, 0 <= n -> 0 <= a < 2 ^ n -> 0 <= b -> Z.lor a (b * 2 ^ n) = a + b * 2 ^ n.
Proof.
  intros a b n Hn Ha Hb.
  assert (L : Z.land a (b * 2 ^ n) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i n).
    - rewrite Z.mul_pow2_bits by lia. rewrite (Z.testbit_neg_r b (i - n)) by lia. apply andb_false_r.
    - rewrite <- (Z.mod_small a (2 ^ n)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite <- Z.lxor_lor by exact L. rewrite <- Z.add_nocarry_lxor by exact L. reflexivity.
Qed.

Lemma shl_shr_field : forall P k, 0 <= P -> 0 <= k <= 58 ->
  Z.shiftr ((Z.shiftl P k) mod 2 ^ 64) 58 = (P / 2 ^ (58 - k)) mod 64.
Proof.
  intros P k HP Hk.
  assert (E : Z.shiftr ((Z.shiftl P k) mod 2 ^ 64) 58 = (P / 2 ^ (58 - k)) mod 2 ^ 6).
  2: rewrite E; reflexivity.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.shiftr_spec by lia.
  destruct (Z.lt_ge_cases i 6).
  - rewrite Z.mod_pow2_bits_low by lia. rewrite Z.mod_pow2_bits_low by lia.
    rewrite Z.shiftl_spec by lia. rewrite <- Z.shiftr_div_pow2 by lia. rewrite Z.shiftr_spec by lia.
    f_equal. lia.
  - rewrite Z.mod_pow2_bits_high by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma land63 : forall P, Z.land P 63 = P mod 64.
Proof. intros P. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma land_m1024 : forall v, 0 <= v < 2 ^ 64 -> Z.land v 18446744073709550592 = v - v mod 1024.
Proof.
  intros v Hv.
  assert (E : Z.land v 18446744073709550592 = Z.ldiff v 1023).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec.
    destruct (Z.lt_ge_cases i 64).
    - f_equal. change 18446744073709550592 with (Z.ldiff (Z.ones 64) 1023).
      rewrite Z.ldiff_spec, Z.ones_spec_low by lia. reflexivity.
    - rewrite <- (Z.mod_small v (2 ^ 64)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite E. change 1023 with (Z.ones 10).
  assert (F : Z.ldiff v (Z.ones 10) + Z.land v (Z.ones 10) = v).
  { rewrite Z.add_nocarry_lxor.
    - apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.ldiff_spec, Z.land_spec.
      destruct (Z.testbit v i), (Z.testbit (Z.ones 10) i); reflexivity.
    - apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0.
      destruct (Z.testbit v i), (Z.testbit (Z.ones 10) i); reflexivity. }
  rewrite Z.land_ones in F by lia. change (2 ^ 10) with 1024 in F. lia.
Qed.

Lemma outside_dec : forall W z, outside W z \/ ~ outside W z.
Proof.
  induction W as [|[a b] W IH]; intros z; cbn [outside].
  - left; exact I.
  - destruct (IH z) as [H|H].
    + destruct (Z.le_gt_cases a z); destruct (Z.lt_ge_cases z b).
      * right. intros [Hc _]. lia.
      * left. split; [lia|exact H].
      * left. split; [lia|exact H].
      * left. split; [lia|exact H].
    + right. intros [_ H2]. exact (H H2).
Qed.

Section Mem.
Variable segs : list Segment.

Lemma bytes_at_skipn : forall m a l n, bytes_at segs m a l -> (n <= length l)%nat ->
  bytes_at segs m (a + Z.of_nat n) (skipn n l).
Proof.
  intros m a l n H Hn. rewrite <- (firstn_skipn n l) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length_le in H by exact Hn. exact H.
Qed.

Lemma bytes_at_prefix : forall m a l1 l2, bytes_at segs m a (l1 ++ l2) -> bytes_at segs m a l1.
Proof. intros m a l1 l2 H. apply bytes_at_app in H. tauto. Qed.

Lemma bytes_at_read_at : forall m a l1 b r, bytes_at segs m a (l1 ++ b :: r) ->
  ov_read_bytes segs m (wa (a + Z.of_nat (length l1))) 1 = Some [b].
Proof.
  intros m a l1 b r H. rewrite (bytes_at_ov_read segs m a _ (length l1) 1 H) by (rewrite app_length; cbn; lia).
  rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Lemma bytes_at_read0 : forall m a b r, bytes_at segs m a (b :: r) -> ov_read_bytes segs m (wa a) 1 = Some [b].
Proof.
  intros m a b r H. rewrite <- (Z.add_0_r a). change 0 with (Z.of_nat (length (@nil byte))).
  apply (bytes_at_read_at m a [] b r). exact H.
Qed.

Lemma bytes_at_read_whole : forall m a l, bytes_at segs m a l -> ov_read_bytes segs m (wa a) (length l) = Some l.
Proof.
  intros m a l H. rewrite <- (Z.add_0_r a). change 0 with (Z.of_nat 0).
  rewrite (bytes_at_ov_read segs m a l 0 (length l) H) by lia. cbn [skipn]. rewrite firstn_all. reflexivity.
Qed.

Lemma bytes_at_snoc_write : forall m a bs cs, bytes_at segs m a bs ->
  a + Z.of_nat (length bs) + Z.of_nat (length cs) <= 2 ^ 64 ->
  bytes_at segs (write_to_mem m (wa (a + Z.of_nat (length bs))) cs) a (bs ++ cs).
Proof.
  intros m a bs cs H Hl. pose proof (bytes_at_bound segs m a bs H) as HB.
  apply bytes_at_app. split.
  - apply bytes_at_write_other; [exact H | lia | lia | lia].
  - apply bytes_at_write_same; lia.
Qed.

Lemma mrd_of_bytes_at : forall m a bs z, bytes_at segs m a bs -> a <= z < a + Z.of_nat (length bs) ->
  exists b, mrd segs m (wa z) = Some b.
Proof.
  intros m a bs z (Ha & Hl & H) Hz.
  replace z with (a + Z.of_nat (Z.to_nat (z - a))) by lia.
  rewrite H by lia. destruct (nth_error bs (Z.to_nat (z - a))) eqn:E; [eexists; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

Lemma stk_after_bytes : forall m m' lo hi a bs, stk segs m lo hi ->
  munch [(a, a + Z.of_nat (length bs))] m m' -> wmono segs m m' -> bytes_at segs m' a bs -> stk segs m' lo hi.
Proof.
  intros m m' lo hi a bs (H1 & H2 & H) Hm Hw Hb. split; [lia|]. split; [lia|].
  intros z Hz. destruct (H z Hz) as [Hwz (b & Hbz)]. split; [apply Hw; exact Hwz|].
  destruct (Z.lt_ge_cases z a) as [Lt|Ge].
  - exists b. unfold mrd in *. rewrite Hm; [exact Hbz|]. rewrite wa_unsigned by lia. cbn [outside]. split; [lia|exact I].
  - destruct (Z.lt_ge_cases z (a + Z.of_nat (length bs))) as [Lt2|Ge2].
    + eapply mrd_of_bytes_at; [exact Hb|lia].
    + exists b. unfold mrd in *. rewrite Hm; [exact Hbz|]. rewrite wa_unsigned by lia. cbn [outside]. split; [lia|exact I].
Qed.

Lemma mem_inv_munch : forall W m m', mem_inv segs m -> munch W m m' ->
  (forall z, ~ outside W (bv_unsigned z) -> wview segs m z <> None) -> mem_inv segs m'.
Proof.
  intros W m m' Hi Hm Hw z b Hz.
  destruct (outside_dec W (bv_unsigned z)) as [O|N].
  - rewrite (Hm z O) in Hz. exact (Hi z b Hz).
  - specialize (Hw z N). destruct (m z) eqn:E.
    + exact (Hi z _ E).
    + exact (wview_not_ro segs m z Hw E).
Qed.

End Mem.
