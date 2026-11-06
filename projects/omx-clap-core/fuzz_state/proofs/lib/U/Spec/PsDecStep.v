From Stdlib Require Import ZArith List Lia Bool Arith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require hex4_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import ReaderRes ps_seg_turn ps_seg_utail.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjGrammar.
Import ListNotations.
Open Scope Z_scope.

Lemma psd_emit_some : forall p s r, emit p (Some (s, r)) = Some (p ++ s, r).
Proof. reflexivity. Qed.

Lemma psd_emit_none : forall p, emit p None = None.
Proof. reflexivity. Qed.

Lemma psd_emit_nil : forall d, emit [] d = d.
Proof. intros [[s r]|]; reflexivity. Qed.

Lemma psd_emit_app : forall p q d, emit p (emit q d) = emit (p ++ q) d.
Proof. intros p q [[s r]|]; cbn [emit]; [rewrite app_assoc|]; reflexivity. Qed.

Lemma psd_nil : decode [] = None.
Proof. reflexivity. Qed.

Lemma psd_quote : forall r, decode (34 :: r) = Some ([], r).
Proof. reflexivity. Qed.

Lemma psd_ctl : forall b r, b < 32 -> decode (b :: r) = None.
Proof.
  intros b r H. cbn [decode].
  rewrite (proj2 (Z.eqb_neq b 34)) by lia. rewrite (proj2 (Z.ltb_lt b 32) H). reflexivity.
Qed.

Lemma psd_plain : forall b r, 32 <= b -> b <> 34 -> b <> 92 -> decode (b :: r) = emit [b] (decode r).
Proof.
  intros b r H1 H2 H3. cbn [decode].
  rewrite (proj2 (Z.eqb_neq b 34) H2), (proj2 (Z.ltb_ge b 32) H1), (proj2 (Z.eqb_neq b 92) H3).
  reflexivity.
Qed.

Lemma psd_bs_end : decode [92] = None.
Proof. reflexivity. Qed.

Lemma psd_esc : forall e c r2, e <> 117 -> pst_esc e = Some c ->
  decode (92 :: e :: r2) = emit [c] (decode r2).
Proof.
  intros e c r2 H1 H2. cbn [decode]. rewrite (proj2 (Z.eqb_neq e 117) H1).
  change (escape e) with (pst_esc e). rewrite H2. reflexivity.
Qed.

Lemma psd_esc_bad : forall e r2, e <> 117 -> pst_esc e = None -> decode (92 :: e :: r2) = None.
Proof.
  intros e r2 H1 H2. cbn [decode]. rewrite (proj2 (Z.eqb_neq e 117) H1).
  change (escape e) with (pst_esc e). rewrite H2. reflexivity.
Qed.

Lemma psd_u_short : forall r2, (length r2 < 4)%nat -> decode (92 :: 117 :: r2) = None.
Proof.
  intros r2 H. destruct r2 as [|d0 [|d1 [|d2 [|d3 r3]]]]; cbn [length] in H; try lia; reflexivity.
Qed.

Lemma psd_u_nohex : forall r2, hex4 r2 = None -> decode (92 :: 117 :: r2) = None.
Proof.
  intros r2 H. destruct r2 as [|d0 [|d1 [|d2 [|d3 r3]]]]; try reflexivity.
  cbn [decode]. rewrite H. reflexivity.
Qed.

Lemma psd_u4 : forall d0 d1 d2 d3 r3,
  decode (92 :: 117 :: d0 :: d1 :: d2 :: d3 :: r3) =
  match hex4 [d0; d1; d2; d3] with
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
  end.
Proof. reflexivity. Qed.

Lemma psd_hex4 : forall bs, hex4 (zb bs) = hex4_c.hex4 bs.
Proof. intros bs. destruct bs as [|b0 [|b1 [|b2 [|b3 bs]]]]; reflexivity. Qed.

Lemma psd_hex4_4 : forall b0 b1 b2 b3 bs,
  hex4_c.hex4 (b0 :: b1 :: b2 :: b3 :: bs) = hex4_c.hex4 [b0; b1; b2; b3].
Proof. reflexivity. Qed.

Lemma psd_low : forall bs, low (zb bs) = ps_lo bs.
Proof.
  intros bs. destruct bs as [|b0 [|b1 hs]]; try reflexivity.
  change (zb (b0 :: b1 :: hs)) with (bv_unsigned b0 :: bv_unsigned b1 :: zb hs).
  unfold low, ps_lo. cbv beta iota. rewrite psd_hex4. reflexivity.
Qed.

Lemma psd_cp_k : forall h bs cp k, ps_cp h bs = Some (cp, k) -> k = 6 \/ k = 12.
Proof.
  intros h bs cp k H. unfold ps_cp in H.
  destruct (h =? 0); [discriminate|].
  destruct ((0xD800 <=? h) && (h <? 0xDC00)).
  - destruct (ps_lo bs); [injection H as _ <-; right; reflexivity|discriminate].
  - destruct ((0xDC00 <=? h) && (h <? 0xE000)); [discriminate|].
    injection H as _ <-. left. reflexivity.
Qed.

Lemma psd_u : forall r2 : list byte,
  decode (92 :: 117 :: zb r2) =
  match hex4_c.hex4 r2 with
  | Some h =>
    match ps_cp h (skipn 4 r2) with
    | Some (cp, k) => emit (utf8 cp) (decode (zb (skipn (Z.to_nat (k - 2)) r2)))
    | None => None
    end
  | None => None
  end.
Proof.
  intros r2. destruct r2 as [|d0 [|d1 [|d2 [|d3 bs]]]]; try reflexivity.
  change (zb (d0 :: d1 :: d2 :: d3 :: bs))
    with (bv_unsigned d0 :: bv_unsigned d1 :: bv_unsigned d2 :: bv_unsigned d3 :: zb bs).
  rewrite psd_u4.
  change (hex4 [bv_unsigned d0; bv_unsigned d1; bv_unsigned d2; bv_unsigned d3])
    with (hex4_c.hex4 (d0 :: d1 :: d2 :: d3 :: bs)).
  change (skipn 4 (d0 :: d1 :: d2 :: d3 :: bs)) with bs.
  destruct (hex4_c.hex4 (d0 :: d1 :: d2 :: d3 :: bs)) as [h|]; [|reflexivity].
  unfold ps_cp.
  destruct (h =? 0); [reflexivity|].
  destruct ((55296 <=? h) && (h <? 56320)).
  - destruct bs as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 bs]]]]]];
      try (rewrite psu_lo_short by (cbn [length]; lia); reflexivity).
    rewrite <- psd_low.
    destruct (low (zb (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: bs))) as [lo|]; reflexivity.
  - destruct ((56320 <=? h) && (h <? 57344)); reflexivity.
Qed.

Lemma psd_u_bad : forall r2 : list byte, hex4_c.hex4 r2 = None -> decode (92 :: 117 :: zb r2) = None.
Proof. intros r2 H. rewrite psd_u, H. reflexivity. Qed.

Lemma psd_u_none : forall (r2 : list byte) h, hex4_c.hex4 r2 = Some h -> ps_cp h (skipn 4 r2) = None ->
  decode (92 :: 117 :: zb r2) = None.
Proof. intros r2 h H1 H2. rewrite psd_u, H1, H2. reflexivity. Qed.

Lemma psd_u_some : forall (r2 : list byte) h cp k, hex4_c.hex4 r2 = Some h -> ps_cp h (skipn 4 r2) = Some (cp, k) ->
  decode (92 :: 117 :: zb r2) = emit (utf8 cp) (decode (zb (skipn (Z.to_nat (k - 2)) r2))).
Proof. intros r2 h cp k H1 H2. rewrite psd_u, H1, H2. reflexivity. Qed.

Lemma psd_u_at : forall tb text P r, text <= P -> rest_at tb text P = 92 :: 117 :: r ->
  decode (rest_at tb text P) =
  match hex4_c.hex4 (skipn (Z.to_nat (P + 2 - text)) tb) with
  | Some h =>
    match ps_cp h (skipn (Z.to_nat (P + 6 - text)) tb) with
    | Some (cp, k) => emit (utf8 cp) (decode (rest_at tb text (P + k)))
    | None => None
    end
  | None => None
  end.
Proof.
  intros tb text P r HP H. unfold rest_at in *. revert H.
  destruct (skipn (Z.to_nat (P - text)) tb) as [|b0 [|b1 r2]] eqn:E; intros H;
    try (cbn in H; discriminate H).
  assert (Hs : forall j, 0 <= j -> skipn (Z.to_nat (P + j - text)) tb = skipn (Z.to_nat j) (b0 :: b1 :: r2)).
  { intros j Hj. rewrite <- E, skipn_skipn. f_equal. lia. }
  change (zb (b0 :: b1 :: r2)) with (bv_unsigned b0 :: bv_unsigned b1 :: zb r2) in H |- *.
  injection H as H0 H1 _.
  rewrite H0, H1, psd_u.
  rewrite (Hs 2) by lia. rewrite (Hs 6) by lia.
  change (skipn (Z.to_nat 2) (b0 :: b1 :: r2)) with r2.
  change (skipn (Z.to_nat 6) (b0 :: b1 :: r2)) with (skipn 4 r2).
  destruct (hex4_c.hex4 r2) as [h|]; [|reflexivity].
  destruct (ps_cp h (skipn 4 r2)) as [[cp k]|] eqn:Ec; [|reflexivity].
  destruct (psd_cp_k _ _ _ _ Ec) as [-> | ->]; rewrite Hs by lia; reflexivity.
Qed.
