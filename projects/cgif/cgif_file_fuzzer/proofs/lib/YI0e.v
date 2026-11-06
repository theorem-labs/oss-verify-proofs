(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO07 YI0d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Lemma px_ne_fast : forall g cur bef, flag (f_attr bef) 1 = false -> flag (f_attr cur) 1 = false -> flag (f_attr bef) 4 = false -> flag (f_attr cur) 4 = false ->
px_ne g cur bef = (fun c b => negb (c =? b)).
Proof. intros g cur bef H1 H2 H3 H4. unfold px_ne. rewrite H1, H2, H3, H4. reflexivity. Qed.
Lemma px_ne_slow : forall g cur bef, flag (f_attr bef) 1 || flag (f_attr cur) 1 || flag (f_attr bef) 4 || flag (f_attr cur) 4 = true ->
px_ne g cur bef = cmp_pixel g cur bef.
Proof.
intros g cur bef Hs. unfold px_ne.
destruct (flag (f_attr bef) 1), (flag (f_attr cur) 1), (flag (f_attr bef) 4), (flag (f_attr cur) 4); cbn in Hs |- *; try reflexivity; discriminate Hs.
Qed.
Section a.
Variables (g : gcfg) (cur bef : frame) (W H : Z) (D : Z -> Prop).
Hypothesis HW : 1 <= W.
Hypothesis HH : 1 <= H.
Hypothesis Hgw : g_w g = W.
Hypothesis LenC : Z.of_nat (length (f_img cur)) = W * H.
Hypothesis LenB : Z.of_nat (length (f_img bef)) = W * H.
Hypothesis HD : forall p, 0 <= p < W * H -> (D p <-> px_ne g cur bef (nth (Z.to_nat p) (f_img cur) 0) (nth (Z.to_nat p) (f_img bef) 0) = true).
Let Wn := Z.to_nat (g_w g).
Let Hn := Z.to_nat H.
Lemma scan_W : Z.of_nat Wn = W. Proof. subst Wn. rewrite Hgw. lia. Qed.
Lemma scan_lenC : length (f_img cur) = (Z.to_nat (g_w g) * Z.to_nat H)%nat. Proof. rewrite Hgw. nia. Qed.
Lemma scan_lenB : length (f_img bef) = (Z.to_nat (g_w g) * Z.to_nat H)%nat. Proof. rewrite Hgw. nia. Qed.
Lemma scan_Wpos : (0 < Z.to_nat (g_w g))%nat. Proof. rewrite Hgw. lia. Qed.
Lemma dpx_D : forall i x : nat, (i < Hn)%nat -> (x < Wn)%nat -> (dpx g cur bef i x = true <-> D (Z.of_nat i * W + Z.of_nat x)).
Proof.
intros i x Hi Hx. unfold dpx. fold Wn. pose proof scan_W as EW.
assert (Hp : 0 <= Z.of_nat i * W + Z.of_nat x < W * H) by (subst Hn; nia).
rewrite (HD _ Hp). replace (Z.to_nat (Z.of_nat i * W + Z.of_nat x)) with (i * Wn + x)%nat by nia. reflexivity.
Qed.
Lemma dpx_nD : forall i x : nat, (i < Hn)%nat -> (x < Wn)%nat -> ~ D (Z.of_nat i * W + Z.of_nat x) -> dpx g cur bef i x = false.
Proof. intros i x Hi Hx Hn'. destruct (dpx g cur bef i x) eqn:E; [|reflexivity]. exfalso. apply Hn'. apply (dpx_D i x Hi Hx). exact E. Qed.
Theorem diff_area_ident : (forall p, 0 <= p < W * H -> ~ D p) -> diff_area g cur bef = None.
Proof.
intros HN. apply (diff_area_none g cur bef Hn scan_Wpos scan_lenC scan_lenB). intros i x Hi Hx. fold Wn in Hx.
apply (dpx_nD i x Hi Hx). apply HN. pose proof scan_W. subst Hn. nia.
Qed.
Theorem diff_area_scan : forall top hrow left xr : Z,
0 <= top <= hrow -> hrow < H -> 0 <= left <= xr -> xr < W ->
(exists c, 0 <= c < W /\ D (top * W + c)) -> (forall p, 0 <= p < top * W -> ~ D p) ->
(exists c, 0 <= c < W /\ D (hrow * W + c)) -> (forall p, (hrow + 1) * W <= p < W * H -> ~ D p) ->
(exists i, top <= i < top + (hrow + 1 - top) /\ D (i * W + left)) -> (forall i x, top <= i < top + (hrow + 1 - top) -> 0 <= x < left -> ~ D (i * W + x)) ->
(exists i, top <= i < top + (hrow + 1 - top) /\ D (i * W + xr)) -> (forall i x, top <= i < top + (hrow + 1 - top) -> xr < x < W -> ~ D (i * W + x)) ->
diff_area g cur bef = Some (xr + 1 - left, hrow + 1 - top, top, left).
Proof.
intros top hrow left xr Htop Hhr Hleft Hxr (c1 & Hc1 & T1) F1 (c2 & Hc2 & T2) F2 (i3 & Hi3 & T3) F3 (i4 & Hi4 & T4) F4.
pose proof scan_W as EW.
pose proof (diff_area_char g cur bef Hn scan_Wpos scan_lenC scan_lenB (Z.to_nat top) (Z.to_nat hrow) (Z.to_nat left) (Z.to_nat xr)) as CH. fold Wn in CH.
rewrite !Z2Nat.id in CH by lia. apply CH; clear CH.
- subst Hn. lia.
- lia.
- exists (Z.to_nat c1). split; [lia|]. apply dpx_D; [subst Hn; lia | lia |]. rewrite !Z2Nat.id by lia. exact T1.
- intros i x Hi Hx. apply dpx_nD; [subst Hn; lia | exact Hx |]. apply F1. nia.
- exists (Z.to_nat c2). split; [lia|]. apply dpx_D; [subst Hn; lia | lia |]. rewrite !Z2Nat.id by lia. exact T2.
- intros i x Hi Hx. apply dpx_nD; [lia | exact Hx |]. apply F2. subst Hn. nia.
- exists (Z.to_nat i3). split; [lia|]. apply dpx_D; [subst Hn; lia | lia |]. rewrite !Z2Nat.id by lia. exact T3.
- intros i x Hi Hx. apply dpx_nD; [subst Hn; lia | lia |]. apply F3; lia.
- exists (Z.to_nat i4). split; [lia|]. apply dpx_D; [subst Hn; lia | lia |]. rewrite !Z2Nat.id by lia. exact T4.
- intros i x Hi Hx. apply dpx_nD; [subst Hn; lia | lia |]. apply F4; lia.
Qed.
End a.
