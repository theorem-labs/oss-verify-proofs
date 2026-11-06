(* The pure model facts the check_as_written walk needs about fs's released base64 model
   (lib/Prog/WriterSpec.v b64v / b64_ws / b64_scan / six_bytes / six_tail_ok / b64_dec), and the two bit tricks the
   compiler used for them in fs.asan: the unsigned range test (`c - 'A' <=u 25`) and the whitespace bit mask
   (4294977024 = 2^32 + 2^13 + 2^10 + 2^9, read with `srl` and `andi 1`). No image, no engine. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec.
Import ListNotations.
Local Open Scope Z_scope.

Module WS := WriterSpec.

(* ---- the classification of one character, as fs.asan computes it (0x8163c-0x8169c) ---- *)
(* the sextet value the code leaves in t2: the b64 value, or -1 *)
Definition caw_val (c : Z) : Z := match WS.b64v c with Some v => v | None => -1 end.

Lemma caw_val_AZ : forall c, 65 <= c <= 90 -> WS.b64v c = Some (c - 65) /\ caw_val c = c - 65.
Proof.
intros c H. unfold caw_val, WS.b64v.
replace (65 <=? c) with true by (symmetry; apply Z.leb_le; lia).
replace (c <=? 90) with true by (symmetry; apply Z.leb_le; lia).
cbn [andb]. split; reflexivity.
Qed.
Lemma caw_val_az : forall c, 97 <= c <= 122 -> WS.b64v c = Some (c - 71) /\ caw_val c = c - 71.
Proof.
intros c H. unfold caw_val, WS.b64v.
replace (65 <=? c) with true by (symmetry; apply Z.leb_le; lia).
replace (c <=? 90) with false by (symmetry; apply Z.leb_gt; lia).
replace (97 <=? c) with true by (symmetry; apply Z.leb_le; lia).
replace (c <=? 122) with true by (symmetry; apply Z.leb_le; lia).
cbn [andb]. split; reflexivity.
Qed.
Lemma caw_val_09 : forall c, 48 <= c <= 57 -> WS.b64v c = Some (c + 4) /\ caw_val c = c + 4.
Proof.
intros c H. unfold caw_val, WS.b64v.
replace (65 <=? c) with false by (symmetry; apply Z.leb_gt; lia).
replace (97 <=? c) with false by (symmetry; apply Z.leb_gt; lia).
replace (48 <=? c) with true by (symmetry; apply Z.leb_le; lia).
replace (c <=? 57) with true by (symmetry; apply Z.leb_le; lia).
cbn [andb]. split; reflexivity.
Qed.
Lemma caw_val_plus : WS.b64v 43 = Some 62 /\ caw_val 43 = 62.
Proof. split; reflexivity. Qed.
Lemma caw_val_slash : WS.b64v 47 = Some 63 /\ caw_val 47 = 63.
Proof. split; reflexivity. Qed.
Lemma caw_val_none : forall c,
  ~ (65 <= c <= 90) -> ~ (97 <= c <= 122) -> ~ (48 <= c <= 57) -> c <> 43 -> c <> 47 ->
  WS.b64v c = None /\ caw_val c = -1.
Proof.
intros c H1 H2 H3 H4 H5. unfold caw_val, WS.b64v.
destruct (65 <=? c) eqn:A1, (c <=? 90) eqn:A2, (97 <=? c) eqn:B1, (c <=? 122) eqn:B2,
         (48 <=? c) eqn:C1, (c <=? 57) eqn:C2, (c =? 43) eqn:D, (c =? 47) eqn:E;
  cbn [andb];
  repeat match goal with
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
  end; try lia; split; reflexivity.
Qed.
Lemma caw_val_range : forall c, 0 <= c < 256 -> -1 <= caw_val c <= 63.
Proof.
intros c Hc. unfold caw_val, WS.b64v.
destruct (65 <=? c) eqn:A1, (c <=? 90) eqn:A2, (97 <=? c) eqn:B1, (c <=? 122) eqn:B2,
         (48 <=? c) eqn:C1, (c <=? 57) eqn:C2, (c =? 43) eqn:D, (c =? 47) eqn:E;
  cbn [andb];
  repeat match goal with
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
  end; lia.
Qed.

(* ---- the whitespace mask of fs.asan (0x81628-0x81634, 0x816a0-0x816a8): bits 9, 10, 13 and 32 ---- *)
Definition CAW_WSMASK : Z := 4294977024.
Lemma caw_wsmask_lor : CAW_WSMASK = Z.lor (2 ^ 32) (Z.lor (2 ^ 13) (Z.lor (2 ^ 10) (2 ^ 9))).
Proof. reflexivity. Qed.
Lemma caw_ws_bit : forall c, 0 <= c ->
  Z.testbit CAW_WSMASK c = WS.b64_ws c.
Proof.
intros c Hc. rewrite caw_wsmask_lor, !Z.lor_spec, !Z.pow2_bits_eqb by lia.
unfold WS.b64_ws.
destruct (c =? 32) eqn:E32, (c =? 9) eqn:E9, (c =? 10) eqn:E10, (c =? 13) eqn:E13;
  repeat match goal with H : (_ =? _) = true |- _ => apply Z.eqb_eq in H | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H end;
  repeat match goal with
  | |- context [32 =? c] => replace (32 =? c) with (c =? 32) by (apply Z.eqb_sym)
  | |- context [9 =? c] => replace (9 =? c) with (c =? 9) by (apply Z.eqb_sym)
  | |- context [10 =? c] => replace (10 =? c) with (c =? 10) by (apply Z.eqb_sym)
  | |- context [13 =? c] => replace (13 =? c) with (c =? 13) by (apply Z.eqb_sym)
  end;
  rewrite ?E32, ?E9, ?E10, ?E13; try reflexivity; try lia.
Qed.
(* the machine's test: (MASK >> c) land 1, for 0 <= c <= 61 (the shift amount is below 64 there) *)
Lemma caw_ws_test : forall c, 0 <= c ->
  Z.land (Z.shiftr CAW_WSMASK c) 1 = if WS.b64_ws c then 1 else 0.
Proof.
intros c Hc. rewrite <- caw_ws_bit by exact Hc.
replace 1 with (Z.ones 1) by reflexivity.
rewrite Z.land_ones by lia. change (2 ^ Z.ones 1) with 2.
rewrite Zmod_odd, <- Z.bit0_odd, Z.shiftr_spec by lia.
rewrite Z.add_0_l. reflexivity.
Qed.

(* ---- b64_scan: the step the loop takes on one character ---- *)
Lemma caw_scan_ws : forall pad six c u, WS.b64_ws c = true ->
  WS.b64_scan pad six (c :: u) = WS.b64_scan pad six u.
Proof. intros pad six c u H. cbn [WS.b64_scan]. rewrite H. reflexivity. Qed.
Lemma caw_scan_pad : forall pad six c u, WS.b64_ws c = false -> c = 61 ->
  WS.b64_scan pad six (c :: u) = WS.b64_scan (pad + 1) six u.
Proof. intros pad six c u H ->. cbn [WS.b64_scan]. rewrite H. reflexivity. Qed.
Lemma caw_scan_val : forall pad six c u v, WS.b64_ws c = false -> c <> 61 -> WS.b64v c = Some v ->
  WS.b64_scan pad six (c :: u) = if pad =? 0 then WS.b64_scan pad (six ++ [v]) u else None.
Proof.
intros pad six c u v Hw Hc Hv. cbn [WS.b64_scan]. rewrite Hw.
replace (c =? 61) with false by (symmetry; apply Z.eqb_neq; exact Hc).
rewrite Hv. reflexivity.
Qed.
Lemma caw_scan_bad : forall pad six c u, WS.b64_ws c = false -> c <> 61 -> WS.b64v c = None ->
  WS.b64_scan pad six (c :: u) = None.
Proof.
intros pad six c u Hw Hc Hv. cbn [WS.b64_scan]. rewrite Hw.
replace (c =? 61) with false by (symmetry; apply Z.eqb_neq; exact Hc).
rewrite Hv. reflexivity.
Qed.
Lemma caw_scan_nil : forall pad six, WS.b64_scan pad six [] = Some (six, pad).
Proof. reflexivity. Qed.

(* ---- six_bytes: the group the second loop writes ---- *)
Lemma caw_six_bytes_4 : forall s0 s1 s2 s3 r,
  WS.six_bytes (s0 :: s1 :: s2 :: s3 :: r) =
  (s0 * 4 + s1 / 16) :: ((s1 mod 16) * 16 + s2 / 4) :: ((s2 mod 4) * 64 + s3) :: WS.six_bytes r.
Proof. reflexivity. Qed.
Lemma caw_six_bytes_3 : forall s0 s1 s2, WS.six_bytes [s0; s1; s2] = [s0 * 4 + s1 / 16; (s1 mod 16) * 16 + s2 / 4].
Proof. reflexivity. Qed.
Lemma caw_six_bytes_2 : forall s0 s1, WS.six_bytes [s0; s1] = [s0 * 4 + s1 / 16].
Proof. reflexivity. Qed.
Lemma caw_six_bytes_1 : forall s0, WS.six_bytes [s0] = [].
Proof. reflexivity. Qed.
Lemma caw_six_bytes_0 : WS.six_bytes [] = [].
Proof. reflexivity. Qed.
(* every byte six_bytes writes is a byte, if the sextets are sextets *)
Lemma caw_six_bytes_ok : forall six, Forall (fun v => 0 <= v < 64) six ->
  Forall (fun b => 0 <= b < 256) (WS.six_bytes six).
Proof.
fix IH 1. intros [|s0 [|s1 [|s2 [|s3 r]]]] H; cbn [WS.six_bytes];
  repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H as [? H] end;
  repeat constructor; try (Z.div_mod_to_equations; lia).
apply IH. exact H.
Qed.
(* its length bound (the released plain proof's caw_six_len, lib/Prog/check_as_written.v:13-17) *)
Lemma caw_six_len : forall six, Z.of_nat (length (WS.six_bytes six)) <= Z.of_nat (length six) / 4 * 3 + 2.
Proof.
fix IH 1. intros [|a [|b [|c [|d r]]]]; cbn [WS.six_bytes length]; try (Z.div_mod_to_equations; lia).
specialize (IH r). Z.div_mod_to_equations. lia.
Qed.
