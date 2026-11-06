(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP09 YI04 YI00.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbr.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO07.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Lemma length_col3 : forall P i, 0 <= i -> (Z.to_nat (3 * i) + 3 <= length P)%nat -> length (col3 P i) = 3%nat.
Proof. intros P i Hi HL. unfold col3. rewrite length_firstn, length_skipn. lia. Qed.
Lemma nth_col3 : forall P i k, 0 <= i -> (Z.to_nat (3 * i) + 3 <= length P)%nat -> (k < 3)%nat ->
nth k (col3 P i) 0 = nth (Z.to_nat (3 * i) + k) P 0.
Proof.
intros P i k Hi HL Hk. unfold col3. rewrite nth_firstn. replace (k <? 3)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hk).
rewrite nth_skipn. reflexivity.
Qed.
Lemma list_eqb_true_iff : forall a b : list Z, list_eqb a b = true <-> a = b.
Proof.
intros a b. unfold list_eqb. rewrite Bool.andb_true_iff, Nat.eqb_eq, forallb_forall. split.
- intros [Hlen Hf]. revert b Hlen Hf. induction a as [|x a IH]; intros [|y b] Hlen Hf; cbn in Hlen; try discriminate; [reflexivity|].
f_equal; [apply Z.eqb_eq; apply (Hf (x, y)); left; reflexivity | apply IH; [lia | intros p Hp; apply Hf; right; exact Hp]].
- intros <-. split; [reflexivity|]. intros [x y] Hin. apply Z.eqb_eq.
induction a as [|z a IH]; cbn in Hin; [destruct Hin|]. destruct Hin as [Hin|Hin]; [injection Hin as <- <-; reflexivity | exact (IH Hin)].
Qed.
Lemma list_eq_nth3 : forall a b : list Z, length a = 3%nat -> length b = 3%nat ->
(a = b <-> forall k, (k < 3)%nat -> nth k a 0 = nth k b 0).
Proof.
intros a b La Lb. split; [intros -> k _; reflexivity|]. intros H.
destruct a as [|a0 [|a1 [|a2 [|? ?]]]]; cbn in La; try discriminate.
destruct b as [|b0 [|b1 [|b2 [|? ?]]]]; cbn in Lb; try discriminate.
pose proof (H 0%nat ltac:(lia)) as E0. pose proof (H 1%nat ltac:(lia)) as E1. pose proof (H 2%nat ltac:(lia)) as E2.
cbn in E0, E1, E2. subst. reflexivity.
Qed.
Section c.
Variable segs : list Segment.
Variable m : word -> option byte.
Variable rd : Z -> option Z.
Hypothesis Hrd : forall a, rd a = option_map (fun b : byte => bv_unsigned b) (mbyte segs m a).
Lemma rd_garr8 : forall base l i, garr8 segs m base l -> 0 <= i -> (Z.to_nat i < length l)%nat ->
rd (base + i) = Some (nth (Z.to_nat i) l 0).
Proof.
intros base l i Hg Hi Hlt. rewrite Hrd. replace i with (Z.of_nat (Z.to_nat i)) at 1 by lia.
rewrite (garr8_mbyte segs m base l (Z.to_nat i) Hg Hlt). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. exact (proj2 (Hg _ Hlt)).
Qed.
Lemma tcmp_zero_model : forall (g : gcfg) (cur bef : frame) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx iCur iBef : Z),
cattr = f_attr cur -> (Z.land cattr 4 <> 0 -> ctidx = f_ctrans cur) -> cnlp = f_nlp cur ->
battr = f_attr bef -> (Z.land battr 4 <> 0 -> btidx = f_ctrans bef) -> bnlp = f_nlp bef -> ngp = g_ngp g ->
(Z.land cattr 1 <> 0 -> garr8 segs m cpal (f_lpal cur) /\ 3 * cnlp <= Z.of_nat (length (f_lpal cur))) ->
(Z.land battr 1 <> 0 -> garr8 segs m bpal (f_lpal bef) /\ 3 * bnlp <= Z.of_nat (length (f_lpal bef))) ->
(Z.land cattr 1 = 0 \/ Z.land battr 1 = 0 -> garr8 segs m gpal (g_gpal g) /\ 3 * ngp <= Z.of_nat (length (g_gpal g))) ->
0 <= iCur < 256 -> 0 <= iBef < 256 ->
(tcmp_zero rd gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx iCur iBef <-> cmp_pixel g cur bef iCur iBef = false).
Proof.
intros g cur bef gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx iCur iBef
Hca Hct Hcn Hba Hbt Hbn Hng HLc HLb HG Ric Rib.
unfold tcmp_zero, cmp_pixel, flag. subst cattr battr cnlp bnlp ngp.
set (sC := tsel (f_attr cur) (f_nlp cur) (g_ngp g)). set (sB := tsel (f_attr bef) (f_nlp bef) (g_ngp g)).
set (aC := tsel (f_attr cur) cpal gpal). set (aB := tsel (f_attr bef) bpal gpal).
set (PC := if negb (Z.land (f_attr cur) 1 =? 0) then f_lpal cur else g_gpal g).
set (PB := if negb (Z.land (f_attr bef) 1 =? 0) then f_lpal bef else g_gpal g).
assert (EsC : (if negb (Z.land (f_attr cur) 1 =? 0) then f_nlp cur else g_ngp g) = sC).
{ subst sC. unfold tsel. destruct (Z.land (f_attr cur) 1 =? 0); reflexivity. }
assert (EsB : (if negb (Z.land (f_attr bef) 1 =? 0) then f_nlp bef else g_ngp g) = sB).
{ subst sB. unfold tsel. destruct (Z.land (f_attr bef) 1 =? 0); reflexivity. }
rewrite EsC, EsB.
assert (TC : garr8 segs m aC PC /\ 3 * sC <= Z.of_nat (length PC)).
{ subst aC PC sC. unfold tsel. destruct (Z.eqb_spec (Z.land (f_attr cur) 1) 0) as [E|E]; cbn [negb].
- exact (HG (or_introl E)). - exact (HLc E). }
assert (TB : garr8 segs m aB PB /\ 3 * sB <= Z.of_nat (length PB)).
{ subst aB PB sB. unfold tsel. destruct (Z.eqb_spec (Z.land (f_attr bef) 1) 0) as [E|E]; cbn [negb].
- exact (HG (or_intror E)). - exact (HLb E). }
destruct TC as [GC LC]. destruct TB as [GB LB].
assert (COL : iBef < sB -> iCur < sC ->
((forall i, 0 <= i < 3 -> rd (aB + 3 * iBef + i) = rd (aC + 3 * iCur + i)) <-> negb (list_eqb (col3 PB iBef) (col3 PC iCur)) = false)).
{ intros RB RC. rewrite Bool.negb_false_iff, list_eqb_true_iff.
rewrite (list_eq_nth3 _ _ (length_col3 PB iBef ltac:(lia) ltac:(lia)) (length_col3 PC iCur ltac:(lia) ltac:(lia))).
split.
- intros EQ k Hk. rewrite !nth_col3 by lia.
pose proof (EQ (Z.of_nat k) ltac:(lia)) as E.
rewrite <- !Z.add_assoc in E.
rewrite (rd_garr8 aB PB (3 * iBef + Z.of_nat k) GB) in E by lia.
rewrite (rd_garr8 aC PC (3 * iCur + Z.of_nat k) GC) in E by lia.
injection E as E. replace (Z.to_nat (3 * iBef) + k)%nat with (Z.to_nat (3 * iBef + Z.of_nat k)) by lia.
replace (Z.to_nat (3 * iCur) + k)%nat with (Z.to_nat (3 * iCur + Z.of_nat k)) by lia. exact E.
- intros HQ i Hi. pose proof (HQ (Z.to_nat i) ltac:(lia)) as E. rewrite !nth_col3 in E by lia.
rewrite <- !Z.add_assoc.
rewrite (rd_garr8 aB PB (3 * iBef + i) GB) by lia. rewrite (rd_garr8 aC PC (3 * iCur + i) GC) by lia.
f_equal. replace (Z.to_nat (3 * iBef + i)) with (Z.to_nat (3 * iBef) + Z.to_nat i)%nat by lia.
replace (Z.to_nat (3 * iCur + i)) with (Z.to_nat (3 * iCur) + Z.to_nat i)%nat by lia. exact E. }
destruct (Z.eqb_spec (Z.land (f_attr cur) 4) 0) as [C4|C4]; cbn [negb andb].
- destruct (Z.eqb_spec (Z.land (f_attr bef) 4) 0) as [B4|B4]; cbn [negb andb].
+ destruct (Z.leb_spec sB iBef); [|destruct (Z.leb_spec sC iCur)]; cbn [orb].
* split; [intros [[X _] | (_ & _ & RB & _)]; [exact (False_ind _ (X C4)) | lia] | intros Q; discriminate Q].
* split; [intros [[X _] | (_ & _ & _ & RC & _)]; [exact (False_ind _ (X C4)) | lia] | intros Q; discriminate Q].
* rewrite <- (COL ltac:(lia) ltac:(lia)). split.
-- intros [[X _] | (_ & _ & _ & _ & EQ)]; [exact (False_ind _ (X C4)) | exact EQ].
-- intros EQ. right. split; [intros [X _]; exact (X C4)|]. split; [intros [X _]; exact (X B4)|]. split; [lia|]. split; [lia|]. exact EQ.
+ rewrite (Hbt B4). destruct (Z.eqb_spec iBef (f_ctrans bef)) as [EB|EB]; cbn [negb andb].
* split; [|intros Q; discriminate Q]. intros [[X _] | (_ & X & _)]; [exact (False_ind _ (X C4)) | exfalso; apply X; split; [exact B4 | exact EB]].
* destruct (Z.leb_spec sB iBef); [|destruct (Z.leb_spec sC iCur)]; cbn [orb].
-- split; [intros [[X _] | (_ & _ & RB & _)]; [exact (False_ind _ (X C4)) | lia] | intros Q; discriminate Q].
-- split; [intros [[X _] | (_ & _ & _ & RC & _)]; [exact (False_ind _ (X C4)) | lia] | intros Q; discriminate Q].
-- rewrite <- (COL ltac:(lia) ltac:(lia)). split.
++ intros [[X _] | (_ & _ & _ & _ & EQ)]; [exact (False_ind _ (X C4)) | exact EQ].
++ intros EQ. right. split; [intros [X _]; exact (X C4)|]. split; [intros [_ X]; exact (EB X)|]. split; [lia|]. split; [lia|]. exact EQ.
- rewrite (Hct C4). destruct (Z.eqb_spec iCur (f_ctrans cur)) as [EC|EC]; cbn [negb andb].
+ split; [intros _; reflexivity|]. intros _. left. split; [exact C4 | exact EC].
+ destruct (Z.eqb_spec (Z.land (f_attr bef) 4) 0) as [B4|B4]; cbn [negb andb].
* destruct (Z.leb_spec sB iBef); [|destruct (Z.leb_spec sC iCur)]; cbn [orb].
-- split; [intros [[_ X] | (_ & _ & RB & _)]; [exact (False_ind _ (EC X)) | lia] | intros Q; discriminate Q].
-- split; [intros [[_ X] | (_ & _ & _ & RC & _)]; [exact (False_ind _ (EC X)) | lia] | intros Q; discriminate Q].
-- rewrite <- (COL ltac:(lia) ltac:(lia)). split.
++ intros [[_ X] | (_ & _ & _ & _ & EQ)]; [exact (False_ind _ (EC X)) | exact EQ].
++ intros EQ. right. split; [intros [_ X]; exact (EC X)|]. split; [intros [X _]; exact (X B4)|]. split; [lia|]. split; [lia|]. exact EQ.
* rewrite (Hbt B4). destruct (Z.eqb_spec iBef (f_ctrans bef)) as [EB|EB]; cbn [negb andb].
-- split; [|intros Q; discriminate Q]. intros [[_ X] | (_ & X & _)]; [exact (False_ind _ (EC X)) | exfalso; apply X; split; [exact B4 | exact EB]].
-- destruct (Z.leb_spec sB iBef); [|destruct (Z.leb_spec sC iCur)]; cbn [orb].
++ split; [intros [[_ X] | (_ & _ & RB & _)]; [exact (False_ind _ (EC X)) | lia] | intros Q; discriminate Q].
++ split; [intros [[_ X] | (_ & _ & _ & RC & _)]; [exact (False_ind _ (EC X)) | lia] | intros Q; discriminate Q].
++ rewrite <- (COL ltac:(lia) ltac:(lia)). split.
** intros [[_ X] | (_ & _ & _ & _ & EQ)]; [exact (False_ind _ (EC X)) | exact EQ].
** intros EQ. right. split; [intros [_ X]; exact (EC X)|]. split; [intros [_ X]; exact (EB X)|]. split; [lia|]. split; [lia|]. exact EQ.
Qed.
End c.
