From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterSpec WriterSpecFacts.
Import ListNotations.
Open Scope Z_scope.

Definition b64_strip (tb : list Z) : list Z := filter (fun c => negb (b64_ws c)) tb.

Lemma b64_strip_cons : forall c rest,
  b64_strip (c :: rest) = if b64_ws c then b64_strip rest else c :: b64_strip rest.
Proof. intros c rest. unfold b64_strip. cbn [filter]. destruct (b64_ws c); reflexivity. Qed.

Lemma b64c_of_b64v : forall c v, b64v c = Some v -> b64c v = c.
Proof.
  intros c v. unfold b64v.
  destruct (Z.leb_spec 65 c), (Z.leb_spec c 90), (Z.leb_spec 97 c), (Z.leb_spec c 122),
    (Z.leb_spec 48 c), (Z.leb_spec c 57), (Z.eqb_spec c 43), (Z.eqb_spec c 47);
    cbn [andb]; intros Hs; try discriminate; injection Hs as <-; unfold b64c;
    repeat match goal with
           | |- context [?x <? ?y] => destruct (Z.ltb_spec x y)
           | |- context [?x =? ?y] => destruct (Z.eqb_spec x y)
           end; cbv beta iota; lia.
Qed.

Lemma scan_strip : forall tb p acc six pad, 0 <= p -> b64_scan p acc tb = Some (six, pad) ->
  exists sfx, six = acc ++ sfx /\ p <= pad /\ (0 < p -> sfx = []) /\
    b64_strip tb = map b64c sfx ++ repeat 61 (Z.to_nat (pad - p)).
Proof.
  induction tb as [|c rest IH]; intros p acc six pad Hp H.
  - cbn [b64_scan] in H. injection H as <- <-. exists []. rewrite app_nil_r.
    split; [reflexivity|]. split; [lia|]. split; [intros _; reflexivity|].
    rewrite Z.sub_diag. reflexivity.
  - revert H. cbn [b64_scan]. rewrite b64_strip_cons.
    destruct (b64_ws c) eqn:W.
    + intros H. exact (IH p acc six pad Hp H).
    + destruct (Z.eqb_spec c 61) as [E61|N61].
      * intros H. subst c.
        destruct (IH (p + 1) acc six pad ltac:(lia) H) as (sfx & -> & Hle & Hz & Hs).
        assert (sfx = []) by (apply Hz; lia). subst sfx.
        exists []. rewrite Hs. split; [reflexivity|]. split; [lia|]. split; [intros _; reflexivity|].
        cbn [map app].
        replace (Z.to_nat (pad - p)) with (S (Z.to_nat (pad - (p + 1)))) by lia. reflexivity.
      * destruct (b64v c) as [v|] eqn:V; [|intros H; discriminate].
        destruct (Z.eqb_spec p 0) as [P0|P0]; [|intros H; discriminate].
        intros H. subst p.
        destruct (IH 0 (acc ++ [v]) six pad ltac:(lia) H) as (sfx & -> & Hle & _ & Hs).
        exists (v :: sfx). rewrite <- app_assoc. cbn [app].
        split; [reflexivity|]. split; [lia|]. split; [intros Hc; exfalso; lia|].
        rewrite Hs. cbn [map app]. rewrite (b64c_of_b64v c v V). reflexivity.
Qed.

Lemma six_tail_ok_iff : forall six, six_tail_ok six = true <->
  (Z.of_nat (length six) mod 4 <> 1 /\
   (Z.of_nat (length six) mod 4 = 2 -> last six 0 mod 16 = 0) /\
   (Z.of_nat (length six) mod 4 = 3 -> last six 0 mod 4 = 0)).
Proof.
  intros six. unfold six_tail_ok. cbv zeta.
  destruct (Z.eqb_spec (Z.of_nat (length six) mod 4) 1),
    (Z.eqb_spec (Z.of_nat (length six) mod 4) 2),
    (Z.eqb_spec (Z.of_nat (length six) mod 4) 3),
    (Z.eqb_spec (last six 0 mod 16) 0), (Z.eqb_spec (last six 0 mod 4) 0);
    cbn [negb andb orb]; split; intros; intuition (try discriminate; try lia).
Qed.

Lemma grp2 : forall a b, 0 <= a < 64 -> 0 <= b < 64 -> b mod 16 = 0 ->
  (a * 4 + b / 16) / 4 = a /\ ((a * 4 + b / 16) mod 4) * 16 = b.
Proof. intros. split; Z.div_mod_to_equations; lia. Qed.

Lemma grp3 : forall a b c, 0 <= a < 64 -> 0 <= b < 64 -> 0 <= c < 64 -> c mod 4 = 0 ->
  (a * 4 + b / 16) / 4 = a /\
  ((a * 4 + b / 16) mod 4) * 16 + ((b mod 16) * 16 + c / 4) / 16 = b /\
  (((b mod 16) * 16 + c / 4) mod 16) * 4 = c.
Proof. intros. repeat split; Z.div_mod_to_equations; lia. Qed.

Lemma grp4 : forall a b c d, 0 <= a < 64 -> 0 <= b < 64 -> 0 <= c < 64 -> 0 <= d < 64 ->
  (a * 4 + b / 16) / 4 = a /\
  ((a * 4 + b / 16) mod 4) * 16 + ((b mod 16) * 16 + c / 4) / 16 = b /\
  (((b mod 16) * 16 + c / 4) mod 16) * 4 + ((c mod 4) * 64 + d) / 64 = c /\
  ((c mod 4) * 64 + d) mod 64 = d.
Proof. intros. repeat split; Z.div_mod_to_equations; lia. Qed.

Lemma enc_six : forall six pad,
  Forall (fun s => 0 <= s < 64) six -> six_tail_ok six = true -> 0 <= pad <= 2 ->
  (Z.of_nat (length six) + pad) mod 4 = 0 ->
  map b64c six ++ repeat 61 (Z.to_nat pad) = b64_enc (six_bytes six).
Proof.
  intros six. induction six as [|a|a b|a b c|a b c d l IH] using list4_ind; intros pad Hr Ht Hp Hl.
  - assert (pad = 0) by (cbn [length Z.of_nat] in Hl; Z.div_mod_to_equations; lia). subst pad. reflexivity.
  - apply six_tail_ok_iff in Ht as (H1 & _). exfalso. apply H1. reflexivity.
  - apply six_tail_ok_iff in Ht as (_ & H2 & _). specialize (H2 ltac:(reflexivity)). cbn [last] in H2.
    destruct (six_cons _ _ Hr) as [Ha Hr1]. destruct (six_cons _ _ Hr1) as [Hb _].
    assert (pad = 2) by (cbn [length Z.of_nat] in Hl; Z.div_mod_to_equations; lia). subst pad.
    destruct (grp2 a b Ha Hb H2) as [E1 E2].
    cbn [map app six_bytes b64_enc]. rewrite E1, E2. reflexivity.
  - apply six_tail_ok_iff in Ht as (_ & _ & H3). specialize (H3 ltac:(reflexivity)). cbn [last] in H3.
    destruct (six_cons _ _ Hr) as [Ha Hr1]. destruct (six_cons _ _ Hr1) as [Hb Hr2].
    destruct (six_cons _ _ Hr2) as [Hc _].
    assert (pad = 1) by (cbn [length Z.of_nat] in Hl; Z.div_mod_to_equations; lia). subst pad.
    destruct (grp3 a b c Ha Hb Hc H3) as (E1 & E2 & E3).
    cbn [map app six_bytes b64_enc]. rewrite E1, E2, E3. reflexivity.
  - destruct (six_cons _ _ Hr) as [Ha Hr1]. destruct (six_cons _ _ Hr1) as [Hb Hr2].
    destruct (six_cons _ _ Hr2) as [Hc Hr3]. destruct (six_cons _ _ Hr3) as [Hd Hr4].
    assert (Ht' : six_tail_ok l = true).
    { destruct l as [|e l']; [reflexivity|]. rewrite six_tail_ok_cons4 in Ht by discriminate. exact Ht. }
    assert (Hl' : (Z.of_nat (length l) + pad) mod 4 = 0).
    { replace (Z.of_nat (length (a :: b :: c :: d :: l)) + pad) with ((Z.of_nat (length l) + pad) + 1 * 4)
        in Hl by (cbn [length]; lia).
      rewrite Z.mod_add in Hl by lia. exact Hl. }
    destruct (grp4 a b c d Ha Hb Hc Hd) as (E1 & E2 & E3 & E4).
    cbn [map app six_bytes b64_enc]. rewrite E1, E2, E3, E4.
    rewrite <- (IH pad Hr4 Ht' Hp Hl'). reflexivity.
Qed.

Theorem canonical_enc : forall tb bs, b64_dec tb = Some bs ->
  Z.of_nat (length (b64_strip tb)) mod 4 = 0 -> b64_strip tb = b64_enc bs.
Proof.
  intros tb bs H Hl. unfold b64_dec in H.
  destruct (b64_scan 0 [] tb) as [[six pad]|] eqn:E; [|discriminate].
  destruct ((pad <=? 2) && six_tail_ok six) eqn:T; [|discriminate].
  injection H as <-. apply andb_true_iff in T as [Tp Tt]. apply Z.leb_le in Tp.
  destruct (scan_strip tb 0 [] six pad ltac:(lia) E) as (sfx & -> & Hp0 & _ & Hs).
  cbn [app] in *. rewrite Z.sub_0_r in Hs. rewrite Hs in *.
  pose proof (proj2 (scan_inv tb 0 [] sfx pad E) (Forall_nil _)) as Hr.
  apply enc_six; [exact Hr|exact Tt|lia|].
  rewrite length_app, length_map, repeat_length, Nat2Z.inj_add, Z2Nat.id in Hl by lia. exact Hl.
Qed.
