(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 YI06 UI5b YI09 YI00 YI01 UN3a UI1v UI5l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO07 YI0d YI0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma list_eqb_refl : forall a : list Z, list_eqb a a = true.
Proof using.
intros a. unfold list_eqb. rewrite Nat.eqb_refl. cbn [andb]. apply forallb_forall. intros [x y] Hin.
induction a as [|z a IH]; cbn in Hin; [destruct Hin|]. destruct Hin as [Hin|Hin]; [injection Hin as <- <-; apply Z.eqb_refl | exact (IH Hin)].
Qed.
Lemma list_eqb_neq : forall a b : list Z, a <> b -> length a = length b -> list_eqb a b = false.
Proof using.
intros a b Hne Hlen. destruct (list_eqb a b) eqn:E; [|reflexivity]. exfalso. apply Hne. clear Hne.
unfold list_eqb in E. apply Bool.andb_true_iff in E as [_ Hf]. rewrite forallb_forall in Hf.
revert b Hlen Hf. induction a as [|x a IH]; intros [|y b] Hlen Hf; cbn in Hlen; try discriminate; [reflexivity|].
f_equal; [apply Z.eqb_eq; apply (Hf (x, y)); left; reflexivity | apply IH; [lia | intros p Hp; apply Hf; right; exact Hp]].
Qed.
Lemma byte_at_garr8 : forall mem base l k, garr8 ubs0segs mem base l -> 0 <= k < Z.of_nat (length l) ->
byte_at mem (base + k) = nth (Z.to_nat k) l 0.
Proof using.
intros mem base l k Hg Hk. unfold byte_at.
replace k with (Z.of_nat (Z.to_nat k)) at 1 by lia.
rewrite (garr8_mbyte ubs0segs mem base l (Z.to_nat k) Hg ltac:(lia)).
pose proof (proj2 (Hg (Z.to_nat k) ltac:(lia))) as Hr.
rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. exact Hr.
Qed.
Lemma window_spec : forall (W HH : nat) (img : list Z) (w h top lf : Z),
(0 < W)%nat -> length img = (W * HH)%nat ->
1 <= w -> 0 <= lf -> lf + w <= Z.of_nat W -> 1 <= h -> 0 <= top -> top + h <= Z.of_nat HH ->
length (window (Z.of_nat W) img w h top lf) = Z.to_nat (w * h) /\
forall k, 0 <= k < w * h -> nth (Z.to_nat k) (window (Z.of_nat W) img w h top lf) 0 = nth (Z.to_nat ((top + k / w) * Z.of_nat W + lf + k mod w)) img 0.
Proof using.
intros W HH img w h top lf HW Hlen Hw Hl0 Hlw Hh Ht0 Hth.
unfold window. rewrite Nat2Z.id.
destruct (rows_of_spec HH W img (S (length img)) HW Hlen ltac:(rewrite Hlen; nia)) as [RL RN].
set (rows := rows_of (S (length img)) W img) in *.
assert (BL : length (firstn (Z.to_nat h) (skipn (Z.to_nat top) rows)) = Z.to_nat h).
{ rewrite length_firstn, length_skipn, RL. lia. }
assert (BN : forall i, (i < Z.to_nat h)%nat -> nth i (firstn (Z.to_nat h) (skipn (Z.to_nat top) rows)) [] = firstn W (skipn ((Z.to_nat top + i) * W) img)).
{ intros i Hi. rewrite nth_firstn. replace (i <? Z.to_nat h)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi).
rewrite nth_skipn. apply RN. lia. }
assert (GEN : forall (band : list (list Z)) n, length band = n -> (forall i, (i < n)%nat -> length (nth i band []) >= Z.to_nat lf + Z.to_nat w)%nat ->
length (flat_map (fun r => firstn (Z.to_nat w) (skipn (Z.to_nat lf) r)) band) = (n * Z.to_nat w)%nat /\
forall i c, (i < n)%nat -> (c < Z.to_nat w)%nat ->
nth (i * Z.to_nat w + c) (flat_map (fun r => firstn (Z.to_nat w) (skipn (Z.to_nat lf) r)) band) 0 = nth (Z.to_nat lf + c) (nth i band []) 0).
{ clear. intros band. induction band as [|r band IH]; intros n Hn Hl.
- subst n. split; [reflexivity | intros i c Hi; cbn in Hi; lia].
- destruct n as [|n]; [discriminate Hn|]. injection Hn as Hn.
destruct (IH n Hn ltac:(intros i Hi; apply (Hl (S i)); lia)) as [L1 N1].
assert (Lr : length (firstn (Z.to_nat w) (skipn (Z.to_nat lf) r)) = Z.to_nat w).
{ rewrite length_firstn, length_skipn. specialize (Hl 0%nat ltac:(lia)). cbn [nth] in Hl. lia. }
cbn [flat_map]. split; [rewrite length_app, L1, Lr; lia|].
intros [|i] c Hi Hc.
+ cbn [Nat.mul Nat.add nth]. rewrite app_nth1 by lia. rewrite nth_firstn. replace (c <? Z.to_nat w)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hc). apply nth_skipn.
+ rewrite app_nth2 by (rewrite Lr; nia). rewrite Lr. replace (S i * Z.to_nat w + c - Z.to_nat w)%nat with (i * Z.to_nat w + c)%nat by nia.
cbn [nth]. apply N1; lia. }
destruct (GEN _ (Z.to_nat h) BL) as [L N].
{ intros i Hi. rewrite BN by exact Hi. rewrite length_firstn, length_skipn, Hlen. nia. }
split; [rewrite L; nia|].
intros k Hk.
assert (Hkw : 0 <= k / w < h) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (Hkm : 0 <= k mod w < w) by (apply Z.mod_pos_bound; lia).
pose proof (Z.div_mod k w ltac:(lia)) as Hdm.
replace (Z.to_nat k) with (Z.to_nat (k / w) * Z.to_nat w + Z.to_nat (k mod w))%nat by nia.
rewrite N by nia. rewrite BN by nia. rewrite nth_firstn_skipn by nia.
f_equal. nia.
Qed.
Lemma trf_image : forall (mem0 memc mem' : word -> option byte) (CMP : Z -> Z -> Z) (cmpm : Z -> Z -> bool)
(pTmp Nt bimg w h top lf tv tidx : Z) (Wd Hd : nat) (TMP BIMG : list Z),
garr8 ubs0segs memc pTmp TMP -> Z.of_nat (length TMP) = w * h -> w * h <= Nt ->
garr8 ubs0segs mem0 bimg BIMG -> length BIMG = (Wd * Hd)%nat -> (0 < Wd)%nat ->
1 <= w -> 0 <= lf -> lf + w <= Z.of_nat Wd -> 1 <= h -> 0 <= top -> top + h <= Z.of_nat Hd ->
(forall a, pTmp <= a < pTmp + Nt ->
byte_at mem' a = if (pTmp + 0 * w <=? a) && (a <? pTmp + h * w)
then (if CMP (byte_at memc a) (byte_at mem0 (bimg + ((top + (a - pTmp) / w) * Z.of_nat Wd + lf + (a - pTmp) mod w))) =? 0 then tv mod 256 else byte_at memc a)
else byte_at memc a) ->
(forall ic ib, 0 <= ic < 256 -> 0 <= ib < 256 -> (CMP ic ib =? 0) = negb (cmpm ic ib)) ->
tv mod 256 = tidx -> 0 <= tidx < 256 ->
(forall a, pTmp <= a < pTmp + w * h -> exists b8, mbyte ubs0segs mem' a = Some b8) ->
garr8 ubs0segs mem' pTmp (map (fun pq => if cmpm (fst pq) (snd pq) then fst pq else tidx) (combine TMP (window (Z.of_nat Wd) BIMG w h top lf))).
Proof using.
intros mem0 memc mem' CMP cmpm pTmp Nt bimg w h top lf tv tidx Wd Hd TMP BIMG HT HTL HNt HB HBL HWd Hw Hl0 Hlw Hh Ht0 Hth TOUT CMPm Htv Htidx PRES.
destruct (window_spec Wd Hd BIMG w h top lf HWd HBL Hw Hl0 Hlw Hh Ht0 Hth) as [WL WN].
set (WIN := window (Z.of_nat Wd) BIMG w h top lf) in *.
set (F := fun pq : Z * Z => if cmpm (fst pq) (snd pq) then fst pq else tidx).
assert (ML : length (map F (combine TMP WIN)) = Z.to_nat (w * h)).
{ rewrite length_map, length_combine, WL. lia. }
pose proof (garr8_bytes_ok ubs0segs _ _ _ HT) as TB. pose proof (garr8_bytes_ok ubs0segs _ _ _ HB) as BB.
unfold bytes_ok in TB, BB. rewrite Forall_nth in TB, BB.
apply garr8_intro. intros j Hj. rewrite ML in Hj.
assert (NJ : nth j (map F (combine TMP WIN)) 0 = F (nth j TMP 0, nth j WIN 0)).
{ rewrite (nth_indep _ 0 (F (0, 0))) by (rewrite ML; exact Hj). rewrite map_nth. rewrite combine_nth by (rewrite WL; lia). reflexivity. }
rewrite NJ.
set (k := Z.of_nat j).
assert (Hk : 0 <= k < w * h) by lia.
specialize (WN k Hk). replace (Z.to_nat k) with j in WN by lia.
set (bo := (top + k / w) * Z.of_nat Wd + lf + k mod w) in WN.
assert (Hkw : 0 <= k / w < h) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (Hkm : 0 <= k mod w < w) by (apply Z.mod_pos_bound; lia).
assert (Hbo : 0 <= bo < Z.of_nat (length BIMG)) by (subst bo; rewrite HBL; nia).
pose proof (TB j 0 ltac:(lia)) as Tj. pose proof (BB (Z.to_nat bo) 0 ltac:(lia)) as Bj.
specialize (TOUT (pTmp + k) ltac:(lia)).
replace ((pTmp + 0 * w <=? pTmp + k) && (pTmp + k <? pTmp + h * w)) with true in TOUT by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; nia).
replace (pTmp + k - pTmp) with k in TOUT by lia. fold bo in TOUT.
rewrite (byte_at_garr8 memc pTmp TMP k HT ltac:(lia)), (byte_at_garr8 mem0 bimg BIMG bo HB Hbo) in TOUT.
replace (Z.to_nat k) with j in TOUT by lia. rewrite <- WN in TOUT.
rewrite (CMPm (nth j TMP 0) (nth j WIN 0) Tj ltac:(rewrite WN; exact Bj)), Htv in TOUT.
assert (HF : F (nth j TMP 0, nth j WIN 0) = byte_at mem' (pTmp + k)).
{ rewrite TOUT. unfold F. cbn [fst snd]. destruct (cmpm (nth j TMP 0) (nth j WIN 0)); reflexivity. }
assert (HFr : 0 <= F (nth j TMP 0, nth j WIN 0) < 256) by (unfold F; cbn [fst snd]; destruct (cmpm _ _); [exact Tj | exact Htidx]).
split; [| exact HFr].
destruct (PRES (pTmp + k) ltac:(lia)) as [b8 Hb8]. rewrite Hb8. f_equal. rewrite HF. unfold byte_at. rewrite Hb8. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma map_unsigned_inj8 : forall a b : list byte, map bv_unsigned a = map bv_unsigned b -> a = b.
Proof using.
induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
injection H as Hxy Hab. f_equal; [apply bv_eq; exact Hxy | apply IH; exact Hab].
Qed.
Lemma firstn3_skipn_firstn : forall (l : list Z) a m, (a + 3 <= m)%nat -> firstn 3 (skipn a (firstn m l)) = firstn 3 (skipn a l).
Proof using.
intros l a m H. rewrite skipn_firstn_comm, firstn_firstn. f_equal. lia.
Qed.
Lemma cmpPixel_model : forall (g : gcfg) (cur bef : frame) (cattr ctidx cnlp battr btidx bnlp ngp : Z) (ctcur ctbef : list byte),
cattr = f_attr cur -> (YO07.flag cattr 4 = true -> ctidx = f_ctrans cur) -> cnlp = f_nlp cur ->
battr = f_attr bef -> (YO07.flag battr 4 = true -> btidx = f_ctrans bef) -> bnlp = f_nlp bef -> ngp = g_ngp g ->
map bv_unsigned ctcur = firstn (Z.to_nat (3 * ct_sel cattr cnlp ngp)) (if YO07.flag cattr 1 then f_lpal cur else g_gpal g) ->
map bv_unsigned ctbef = firstn (Z.to_nat (3 * ct_sel battr bnlp ngp)) (if YO07.flag battr 1 then f_lpal bef else g_gpal g) ->
3 * ct_sel cattr cnlp ngp <= Z.of_nat (length (if YO07.flag cattr 1 then f_lpal cur else g_gpal g)) ->
3 * ct_sel battr bnlp ngp <= Z.of_nat (length (if YO07.flag battr 1 then f_lpal bef else g_gpal g)) ->
forall ic ib, 0 <= ic < 256 -> 0 <= ib < 256 ->
(cmpPixel_fn cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef ic ib =? 0) = negb (cmp_pixel g cur bef ic ib).
Proof using.
intros g cur bef cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef Hca Hct Hcn Hba Hbt Hbn Hng Mc Mb Lc Lb ic ib Hic Hib.
assert (SELc : ct_sel cattr cnlp ngp = (if YO07.flag cattr 1 then f_nlp cur else g_ngp g)).
{ unfold ct_sel, YO07.flag. subst cnlp ngp. destruct (Z.land cattr 1 =? 0); reflexivity. }
assert (SELb : ct_sel battr bnlp ngp = (if YO07.flag battr 1 then f_nlp bef else g_ngp g)).
{ unfold ct_sel, YO07.flag. subst bnlp ngp. destruct (Z.land battr 1 =? 0); reflexivity. }
unfold cmpPixel_fn, cmp_pixel.
change (negb (Z.land cattr 4 =? 0)) with (YO07.flag cattr 4). change (negb (Z.land battr 4 =? 0)) with (YO07.flag battr 4).
rewrite <- Hca, <- Hba. cbv zeta.
assert (C1 : (YO07.flag cattr 4 && (ic =? ctidx)) = (YO07.flag cattr 4 && (ic =? f_ctrans cur))) by (destruct (YO07.flag cattr 4); [rewrite (Hct eq_refl); reflexivity | reflexivity]).
assert (C2 : (YO07.flag battr 4 && (ib =? btidx)) = (YO07.flag battr 4 && (ib =? f_ctrans bef))) by (destruct (YO07.flag battr 4); [rewrite (Hbt eq_refl); reflexivity | reflexivity]).
rewrite C1, C2.
destruct (YO07.flag cattr 4 && (ic =? f_ctrans cur)); [reflexivity|].
destruct (YO07.flag battr 4 && (ib =? f_ctrans bef)); [reflexivity|].
rewrite SELc, SELb.
destruct (((if YO07.flag battr 1 then f_nlp bef else g_ngp g) <=? ib) || ((if YO07.flag cattr 1 then f_nlp cur else g_ngp g) <=? ic)) eqn:RNG; [reflexivity|].
apply Bool.orb_false_iff in RNG as [Rb Rc]. apply Z.leb_gt in Rb. apply Z.leb_gt in Rc.
rewrite SELc in Mc, Lc. rewrite SELb in Mb, Lb.
set (PC := if YO07.flag cattr 1 then f_lpal cur else g_gpal g) in *. set (PB := if YO07.flag battr 1 then f_lpal bef else g_gpal g) in *.
set (sC := if YO07.flag cattr 1 then f_nlp cur else g_ngp g) in *. set (sB := if YO07.flag battr 1 then f_nlp bef else g_ngp g) in *.
assert (LC : length ctcur = Z.to_nat (3 * sC)) by (rewrite <- (length_map bv_unsigned), Mc, length_firstn; lia).
assert (LB : length ctbef = Z.to_nat (3 * sB)) by (rewrite <- (length_map bv_unsigned), Mb, length_firstn; lia).
set (A := firstn 3 (skipn (Z.to_nat (3 * ib)) ctbef)). set (B := firstn 3 (skipn (Z.to_nat (3 * ic)) ctcur)).
assert (LA : length A = 3%nat) by (subst A; rewrite length_firstn, length_skipn, LB; lia).
assert (LBB : length B = 3%nat) by (subst B; rewrite length_firstn, length_skipn, LC; lia).
assert (MA : map bv_unsigned A = col3 PB ib) by (subst A; unfold col3; rewrite <- firstn_map, <- skipn_map, Mb; apply firstn3_skipn_firstn; lia).
assert (MB : map bv_unsigned B = col3 PC ic) by (subst B; unfold col3; rewrite <- firstn_map, <- skipn_map, Mc; apply firstn3_skipn_firstn; lia).
destruct (Z.eqb_spec (memcmp_spec A B) 0) as [E0|E0].
- apply (proj1 (memcmp_spec_zero_iff A B ltac:(rewrite LA, LBB; reflexivity))) in E0. rewrite <- MA, <- MB, E0, list_eqb_refl. reflexivity.
- rewrite list_eqb_neq; [reflexivity | | unfold col3; rewrite !length_firstn, !length_skipn; lia].
intros Heq. apply E0. apply (proj2 (memcmp_spec_zero_iff A B ltac:(rewrite LA, LBB; reflexivity))). apply map_unsigned_inj8. rewrite MA, MB. exact Heq.
Qed.
Lemma rdn_garr8_prefix : forall m a n bs PAL,
rdn ubs0segs m (Z_to_bv 64 a) n = Some bs -> garr8 ubs0segs m a PAL -> (n <= length PAL)%nat ->
map bv_unsigned bs = firstn n PAL.
Proof using.
intros m a n bs PAL Hr Hg Hn.
apply (proj1 (rdn_mbytes ubs0segs m n a bs)) in Hr as [Hlen Hb].
apply (nth_ext _ _ 0 0); [rewrite length_map, length_firstn, Hlen; lia|].
intros i Hi. rewrite length_map, Hlen in Hi.
rewrite nth_firstn. replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi).
specialize (Hb i Hi). rewrite (garr8_mbyte ubs0segs m a PAL i Hg ltac:(lia)) in Hb.
symmetry in Hb. apply nth_error_nth with (d := Z_to_bv 8 0) in Hb.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map, Hlen; exact Hi).
rewrite map_nth, Hb, Z_to_bv_unsigned. pose proof (proj2 (Hg i ltac:(lia))) as Hr8.
apply bv_wrap_small. change (bv_modulus 8) with 256. exact Hr8.
Qed.
Lemma trf_imageZ : forall (mem0 memc mem' : word -> option byte) (CMP : Z -> Z -> Z) (cmpm : Z -> Z -> bool)
(pTmp Nt bimg w h top lf tv tidx Wd Hd : Z) (TMP BIMG : list Z),
garr8 ubs0segs memc pTmp TMP -> Z.of_nat (length TMP) = w * h -> w * h <= Nt ->
garr8 ubs0segs mem0 bimg BIMG -> Z.of_nat (length BIMG) = Wd * Hd -> 1 <= Wd -> 0 <= Hd ->
1 <= w -> 0 <= lf -> lf + w <= Wd -> 1 <= h -> 0 <= top -> top + h <= Hd ->
(forall a, pTmp <= a < pTmp + Nt ->
byte_at mem' a = if (pTmp + 0 * w <=? a) && (a <? pTmp + h * w)
then (if CMP (byte_at memc a) (byte_at mem0 (bimg + ((top + (a - pTmp) / w) * Wd + lf + (a - pTmp) mod w))) =? 0 then tv mod 256 else byte_at memc a)
else byte_at memc a) ->
(forall ic ib, 0 <= ic < 256 -> 0 <= ib < 256 -> (CMP ic ib =? 0) = negb (cmpm ic ib)) ->
tv mod 256 = tidx -> 0 <= tidx < 256 ->
(forall a, pTmp <= a < pTmp + w * h -> exists b8, mbyte ubs0segs mem' a = Some b8) ->
garr8 ubs0segs mem' pTmp (map (fun pq => if cmpm (fst pq) (snd pq) then fst pq else tidx) (combine TMP (window Wd BIMG w h top lf))).
Proof using.
intros mem0 memc mem' CMP cmpm pTmp Nt bimg w h top lf tv tidx Wd Hd TMP BIMG HT HTL HNt HB HBL HWd HHd Hw Hl0 Hlw Hh Ht0 Hth TOUT CMPm Htv Htidx PRES.
replace Wd with (Z.of_nat (Z.to_nat Wd)) by lia.
apply (trf_image mem0 memc mem' CMP cmpm pTmp Nt bimg w h top lf tv tidx (Z.to_nat Wd) (Z.to_nat Hd) TMP BIMG HT HTL HNt HB ltac:(nia) ltac:(lia) Hw Hl0 ltac:(lia) Hh Ht0 ltac:(lia));
[| exact CMPm | exact Htv | exact Htidx | exact PRES].
intros a Ha. rewrite (TOUT a Ha). rewrite Z2Nat.id by lia. reflexivity.
Qed.
End e.
