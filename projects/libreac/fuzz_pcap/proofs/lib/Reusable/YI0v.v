(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YI0v.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool FMapPositive.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI0t YO07.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI0u YI0h.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Lemma nth_updn_Z : forall l i j v, 0 <= i -> 0 <= j -> (Z.to_nat i < length l)%nat ->
nth (Z.to_nat j) (updn l (Z.to_nat i) v) 0 = if j =? i then v else nth (Z.to_nat j) l 0.
Proof.
intros l i j v Hi Hj Hlen. rewrite nth_updn. destruct (Z.eqb_spec j i) as [-> | NE].
- rewrite Nat.eqb_refl. apply Nat.ltb_lt in Hlen. rewrite Hlen. reflexivity.
- replace (Nat.eqb (Z.to_nat j) (Z.to_nat i)) with false; [reflexivity|]. symmetry. apply Nat.eqb_neq. intros Q. apply NE. apply Z2Nat.inj in Q; lia.
Qed.
Lemma nth_zero_range_Z : forall l b n j, 0 <= b -> 0 <= n -> 0 <= j -> (Z.to_nat b + Z.to_nat n <= length l)%nat ->
nth (Z.to_nat j) (zero_range l (Z.to_nat b) (Z.to_nat n)) 0 = if (b <=? j) && (j <? b + n) then 0 else nth (Z.to_nat j) l 0.
Proof.
intros l b n j Hb Hn Hj Hlen. rewrite nth_zero_range by exact Hlen.
destruct (Z.leb_spec b j), (Z.ltb_spec j (b + n)), (Nat.leb_spec (Z.to_nat b) (Z.to_nat j)), (Nat.ltb_spec (Z.to_nat j) (Z.to_nat b + Z.to_nat n)); cbn [andb]; try reflexivity; lia.
Qed.
Lemma skipn_nth_cons : forall (l : list Z) n, (n < length l)%nat -> skipn n l = nth n l 0 :: skipn (S n) l.
Proof. induction l as [|x r IH]; intros [|n] Hn; cbn in Hn |- *; try lia; [reflexivity|]. apply IH. lia. Qed.
Lemma skipn_px : forall PIX i, 0 <= i -> (Z.to_nat i < length PIX)%nat -> skipn (Z.to_nat i) PIX = px PIX i :: skipn (Z.to_nat (i + 1)) PIX.
Proof. intros PIX i Hi Hlt. rewrite (skipn_nth_cons PIX _ Hlt). unfold px. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. reflexivity. Qed.
Lemma zm_get_empty : forall k, zm_get zm_empty k = 0.
Proof. intros k. unfold zm_get, zm_empty. rewrite PositiveMap.gempty. reflexivity. Qed.
Lemma zm_get_remove : forall m k k', 0 <= k -> 0 <= k' -> zm_get (PositiveMap.remove (zkey k) m) k' = if k' =? k then 0 else zm_get m k'.
Proof.
intros m k k' Hk Hk'. unfold zm_get. destruct (Z.eqb_spec k' k) as [-> | NE].
- rewrite PositiveMap.grs. reflexivity.
- rewrite PositiveMap.gro; [reflexivity|]. intros Q. apply NE. apply zkey_inj; assumption.
Qed.
Lemma zm_get_clear : forall n m base k, 0 <= base -> 0 <= k ->
zm_get (zm_clear m base n) k = if (base <=? k) && (k <? base + Z.of_nat n) then 0 else zm_get m k.
Proof.
induction n as [|n IH]; intros m base k Hb Hk; cbn [zm_clear].
- destruct (Z.leb_spec base k), (Z.ltb_spec k (base + Z.of_nat 0)); cbn [andb]; try reflexivity; lia.
- rewrite IH by assumption. rewrite zm_get_remove by lia.
destruct (Z.leb_spec base k), (Z.ltb_spec k (base + Z.of_nat n)), (Z.ltb_spec k (base + Z.of_nat (S n))), (Z.eqb_spec k (base + Z.of_nat n)); cbn [andb]; try reflexivity; lia.
Qed.
Lemma lzw_run_nil : forall L s parent atroot, lzw_run L s parent atroot [] = Some (lzw_emit parent s).
Proof. reflexivity. Qed.
Lemma lzw_run_cons : forall L s parent atroot nxt rest',
lzw_run L s parent atroot (nxt :: rest') =
if L <=? nxt then None
else let c := if atroot then zm_get (l_init s) (parent * L + nxt) else lzw_child L parent nxt s in
if c =? 0 then
let s1 := lzw_emit parent s in
let s2 := if l_dictPos s1 <? MAX_DICT_LEN then (if atroot then lzw_add_init L parent nxt s1 else lzw_add_child L parent nxt s1) else lzw_reset L s1 in
lzw_run L s2 nxt true rest'
else lzw_run L s c false rest'.
Proof. reflexivity. Qed.
Lemma tabs_rel_emit : forall idl X LC ms q, tabs_rel idl X LC ms -> tabs_rel idl X LC (lzw_emit q ms).
Proof. intros idl X LC ms q H. exact H. Qed.
Lemma tabs_rel_ext : forall idl X X' LC ms,
tabs_rel idl X LC ms -> la_TI X' = la_TI X -> la_LM X' = la_LM X -> la_LI X' = la_LI X -> la_TM X' = la_TM X -> la_dp X' = la_dp X -> la_mp X' = la_mp X ->
tabs_rel idl X' LC ms.
Proof. intros idl X X' LC ms H E1 E2 E3 E4 E5 E6. unfold tabs_rel in *. rewrite E1, E2, E3, E4, E5, E6. exact H. Qed.
Lemma tabs_rel_typec : forall idl nP X LC ms, tabs_rel idl X LC ms -> tabs_rel idl (st_typec nP X) LC ms.
Proof. intros idl nP X LC ms H. eapply tabs_rel_ext; [exact H | destruct X as [TI LM LI TM s lp dp mp Cn R]; reflexivity ..]. Qed.
Lemma tabs_rel_ti : forall idl X LC ms p c k,
tabs_rel idl X LC ms -> 0 < idl -> 0 <= p < idl -> 0 <= c < idl -> (Z.to_nat (p * idl + c) < length (la_TI X))%nat ->
tabs_rel idl (st_ti idl X p c k) LC (lzw_add_init idl p c ms).
Proof.
intros idl [TI LM LI TM s lp dp mp Cn R] LC ms p c k (RLI & RLM & RLC & RTM & RTI & Edp & Emp) Hidl Hp Hc Hlen.
unfold tabs_rel, lzw_add_init. cbn [st_ti la_TI la_LM la_LI la_TM la_dp la_mp l_init l_lmap l_lcol l_lidx l_tmap l_dictPos l_mapPos] in *.
split; [exact RLI|]. split; [exact RLM|]. split; [exact RLC|]. split; [exact RTM|]. split; [|split; [rewrite Edp; reflexivity | exact Emp]].
intros p' c' Hp' Hc'. assert (K0 : 0 <= p * idl + c) by nia. assert (K0' : 0 <= p' * idl + c') by nia.
rewrite zm_get_set, nth_updn_Z by assumption.
destruct (Z.eqb_spec (p' * idl + c') (p * idl + c)); [exact Edp | exact (RTI p' c' Hp' Hc')].
Qed.
Lemma tabs_rel_first : forall idl X LC ms q c s1,
tabs_rel idl X LC ms -> 0 <= q < 4096 -> (Z.to_nat q < length (la_LI X))%nat -> (Z.to_nat q < length LC)%nat ->
nth (Z.to_nat q) (la_LM X) 0 = 0 -> nth (Z.to_nat q) (la_LI X) 0 = 0 ->
tabs_rel idl (vx_first X q s1) (updn LC (Z.to_nat q) c) (lzw_add_child idl q c ms).
Proof.
intros idl [TI LM LI TM s lp dp mp Cn R] LC ms q c s1 (RLI & RLM & RLC & RTM & RTI & Edp & Emp) Hq HlenLI HlenLC HLM0 HLI0.
unfold tabs_rel, lzw_add_child. cbn [vx_first la_TI la_LM la_LI la_TM la_dp la_mp] in *.
rewrite <- (RLM q Hq), HLM0, <- (RLI q Hq), HLI0. cbn [Z.eqb]. cbn [l_init l_lmap l_lcol l_lidx l_tmap l_dictPos l_mapPos].
split; [|split; [exact RLM|split; [|split; [exact RTM|split; [exact RTI|split; [rewrite Edp; reflexivity | exact Emp]]]]]].
- intros q' Hq'. rewrite zm_get_set, nth_updn_Z by lia. destruct (Z.eqb_spec q' q); [exact Edp | exact (RLI q' Hq')].
- intros q' Hq'. rewrite zm_get_set, nth_updn_Z by lia. destruct (Z.eqb_spec q' q); [reflexivity | exact (RLC q' Hq')].
Qed.
Lemma tabs_rel_map : forall idl X LC ms q c s1,
tabs_rel idl X LC ms -> 0 < idl -> 0 <= q < 4096 -> 0 <= c < idl ->
1 <= nth (Z.to_nat q) (la_LM X) 0 < la_mp X -> (Z.to_nat ((nth (Z.to_nat q) (la_LM X) 0%Z - 1) * idl + c)%Z < length (la_TM X))%nat ->
tabs_rel idl (vx_map idl X (nth (Z.to_nat q) (la_LM X) 0) c s1) LC (lzw_add_child idl q c ms).
Proof.
intros idl [TI LM LI TM s lp dp mp Cn R] LC ms q c s1 (RLI & RLM & RLC & RTM & RTI & Edp & Emp) Hidl Hq Hc Hm Hlen.
unfold tabs_rel, lzw_add_child. cbn [vx_map la_TI la_LM la_LI la_TM la_dp la_mp] in *.
rewrite <- (RLM q Hq). set (m := nth (Z.to_nat q) LM 0) in *.
destruct (Z.eqb_spec m 0) as [E0 | _]; [lia|]. cbn [l_init l_lmap l_lcol l_lidx l_tmap l_dictPos l_mapPos].
split; [exact RLI|]. split; [exact RLM|]. split; [exact RLC|]. split; [|split; [exact RTI|split; [rewrite Edp; reflexivity | exact Emp]]].
intros m' c' Hm' Hc'. assert (K0 : 0 <= (m - 1) * idl + c) by nia. assert (K0' : 0 <= (m' - 1) * idl + c') by nia.
rewrite zm_get_set, nth_updn_Z by assumption.
destruct (Z.eqb_spec ((m' - 1) * idl + c') ((m - 1) * idl + c)); [exact Edp | exact (RTM m' c' Hm' Hc')].
Qed.
Lemma tabs_rel_switch : forall idl X LC ms q c s1,
tabs_rel idl X LC ms -> 0 < idl -> 0 <= q < 4096 -> 0 <= c < idl -> 1 <= la_mp X -> (Z.to_nat q < length (la_LM X))%nat ->
(Z.to_nat ((la_mp X - 1) * idl) + Z.to_nat idl <= length (la_TM X))%nat ->
nth (Z.to_nat q) (la_LM X) 0 = 0 -> nth (Z.to_nat q) (la_LI X) 0 <> 0 ->
tabs_rel idl (vx_switch idl X q c s1) LC (lzw_add_child idl q c ms).
Proof.
intros idl [TI LM LI TM s lp dp mp Cn R] LC ms q c s1 (RLI & RLM & RLC & RTM & RTI & Edp & Emp) Hidl Hq Hc Hmp HlenLM HlenTM HLM0 HLI1.
unfold tabs_rel, lzw_add_child. cbn [vx_switch la_TI la_LM la_LI la_TM la_dp la_mp] in *.
rewrite <- (RLM q Hq), HLM0, <- (RLI q Hq). cbn [Z.eqb].
destruct (Z.eqb_spec (nth (Z.to_nat q) LI 0) 0) as [E0 | _]; [contradiction|]. cbn [l_init l_lmap l_lcol l_lidx l_tmap l_dictPos l_mapPos].
rewrite <- Emp.
split; [exact RLI|]. split; [|split; [exact RLC|split; [|split; [exact RTI|split; [rewrite Edp; reflexivity | reflexivity]]]]].
- intros q' Hq'. rewrite zm_get_set, nth_updn_Z by lia. destruct (Z.eqb_spec q' q); [reflexivity | exact (RLM q' Hq')].
- intros m' c' Hm' Hc'. assert (K0 : 0 <= (mp - 1) * idl) by nia. assert (K0' : 0 <= (m' - 1) * idl + c') by nia.
rewrite zm_get_set by lia. rewrite nth_updn_Z; [| lia | lia | rewrite zero_range_length; lia].
destruct (Z.eqb_spec ((m' - 1) * idl + c') ((mp - 1) * idl + c)) as [E | NE]; [exact Edp|].
rewrite zm_get_clear by lia. rewrite nth_zero_range_Z by (try lia; exact HlenTM). rewrite Z2Nat.id by lia.
destruct ((mp - 1) * idl <=? (m' - 1) * idl + c') eqn:B1, ((m' - 1) * idl + c' <? (mp - 1) * idl + idl) eqn:B2; cbn [andb]; try reflexivity;
(apply RTM; [|exact Hc']); apply Z.leb_gt in B1 || apply Z.ltb_ge in B2; nia.
Qed.
Lemma tabs_rel_reset : forall idl X ms k, 0 <= idl -> tabs_rel idl (st_reset idl X k) (repeat 0 4096) (lzw_reset idl ms).
Proof.
intros idl [TI LM LI TM s lp dp mp Cn R] ms k Hidl. unfold tabs_rel, lzw_reset.
cbn [st_reset la_TI la_LM la_LI la_TM la_dp la_mp l_init l_lmap l_lcol l_lidx l_tmap l_dictPos l_mapPos].
repeat split; intros; rewrite ?zm_get_empty, ?nth_repeat; try reflexivity; lia.
Qed.
Definition sim_ctx (idl nP : Z) (PIX : list Z) : Prop := 2 <= idl <= 256 /\ length PIX = Z.to_nat nP /\ forall i, 0 <= px PIX i < 256.
Section a.
Variables (idl nP : Z) (PIX : list Z).
Hypothesis HC : sim_ctx idl nP PIX.
Let Hidl : 2 <= idl <= 256 := proj1 HC.
Let LenPIX : length PIX = Z.to_nat nP := proj1 (proj2 HC).
Let HPIX : forall i, 0 <= px PIX i < 256 := proj2 (proj2 HC).
Definition sim_inv (X : lzw_abs) (V : lzw_v) (ms : lzw_st) : Prop := tabs_rel idl X (v_LC V) ms /\ rev (l_codes ms) = v_LD V.
Definition sim_head (X : lzw_abs) (V : lzw_v) (FIN : option lzw_st) : Prop :=
exists ms, sim_inv X V ms /\
(if idl <=? px PIX (la_s X) then None else lzw_run idl ms (px PIX (la_s X)) true (skipn (Z.to_nat (la_s X + 1)) PIX)) = FIN.
Definition sim_inner (X : lzw_abs) (V : lzw_v) (s1 q : Z) (FIN : option lzw_st) : Prop :=
exists ms, sim_inv X V ms /\ lzw_run idl ms q false (skipn (Z.to_nat s1) PIX) = FIN.
Definition sim_exit (X : lzw_abs) (V : lzw_v) (FIN : option lzw_st) : Prop := exists ms, sim_inv X V ms /\ FIN = Some ms.
Lemma skipn_end : skipn (Z.to_nat nP) PIX = [].
Proof. apply skipn_all2. lia. Qed.
Lemma sim_head_eidx : forall X V FIN, sim_head X V FIN -> 0 <= la_s X < nP ->
idl <= px PIX (la_s X) \/ (la_s X < nP - 1 /\ idl <= px PIX (la_s X + 1)) -> FIN = None.
Proof.
intros X V FIN (ms & _ & HF) Hs Hc. destruct (Z.leb_spec idl (px PIX (la_s X))) as [|Hlt]; [symmetry; exact HF|].
destruct Hc as [Hc | [Hs1 Hc]]; [lia|]. rewrite skipn_px, lzw_run_cons in HF by lia.
destruct (Z.leb_spec idl (px PIX (la_s X + 1))); [symmetry; exact HF | lia].
Qed.
Lemma sim_head_emitc : forall X V FIN q, sim_head X V FIN -> 0 <= la_s X < nP -> px PIX (la_s X) < idl ->
(la_s X = nP - 1 /\ q = px PIX (la_s X)) \/
(la_s X + 1 = nP - 1 /\ px PIX (la_s X + 1) < idl /\ q = init_child idl X (px PIX (la_s X)) (px PIX (la_s X + 1)) /\ q <> 0) ->
sim_exit (st_typec nP X) (mkLV (v_LC V) (v_LD V ++ [q])) FIN.
Proof.
intros X V FIN q (ms & (HR & HL) & HF) Hs Hc1 Hq. destruct (Z.leb_spec idl (px PIX (la_s X))) as [|_]; [lia|].
exists (lzw_emit q ms). split; [split; [apply tabs_rel_typec; exact HR | cbn [lzw_emit l_codes rev v_LD]; rewrite HL; reflexivity]|].
destruct Hq as [[Hs1 ->] | (Hs1 & Hc2 & -> & Hq0)].
- replace (la_s X + 1) with nP in HF by lia. rewrite skipn_end, lzw_run_nil in HF. symmetry; exact HF.
- rewrite skipn_px, lzw_run_cons in HF by lia. destruct (Z.leb_spec idl (px PIX (la_s X + 1))) as [|_]; [lia|]. cbv zeta in HF.
unfold init_child in *. pose proof (HPIX (la_s X)) as P1. pose proof (HPIX (la_s X + 1)) as P2.
rewrite <- (init_child_model idl X (v_LC V) ms _ _ HR) in HF by lia.
destruct (Z.eqb_spec (nth (Z.to_nat (px PIX (la_s X) * idl + px PIX (la_s X + 1))) (la_TI X) 0) 0) as [E | _]; [contradiction|].
replace (la_s X + 1 + 1) with nP in HF by lia. rewrite skipn_end, lzw_run_nil in HF. symmetry; exact HF.
Qed.
Lemma sim_head_timiss_add : forall X V FIN c1 c2, sim_head X V FIN -> lzw_inv idl nP X ->
c1 = px PIX (la_s X) -> c2 = px PIX (la_s X + 1) -> c1 < idl -> c2 < idl -> nth (Z.to_nat (c1 * idl + c2)) (la_TI X) 0 = 0 ->
0 <= la_s X -> la_s X + 1 < nP -> la_dp X < 4096 ->
sim_head (st_ti idl X c1 c2 (la_s X)) (mkLV (v_LC V) (v_LD V ++ [c1])) FIN.
Proof.
intros X V FIN c1 c2 (ms & (HR & HL) & HF) HI -> -> Hc1 Hc2 HTI0 Hs0 Hs1 Hdp.
pose proof (HPIX (la_s X)) as P1. pose proof (HPIX (la_s X + 1)) as P2.
destruct (Z.leb_spec idl (px PIX (la_s X))) as [|_]; [lia|].
rewrite skipn_px, lzw_run_cons in HF by lia. destruct (Z.leb_spec idl (px PIX (la_s X + 1))) as [|_]; [lia|]. cbv zeta in HF.
rewrite <- (init_child_model idl X (v_LC V) ms _ _ HR), HTI0 in HF by lia. cbn [Z.eqb] in HF.
assert (Edp : l_dictPos (lzw_emit (px PIX (la_s X)) ms) = la_dp X) by (destruct HR as (_ & _ & _ & _ & _ & E & _); symmetry; exact E).
rewrite Edp in HF. destruct (Z.ltb_spec (la_dp X) MAX_DICT_LEN) as [_ | Hge]; [|unfold MAX_DICT_LEN in Hge; lia].
assert (HlenTI : (Z.to_nat (px PIX (la_s X) * idl + px PIX (la_s X + 1)) < length (la_TI X))%nat).
{ destruct X as [TI LM LI TM s lp dp mp Cn R]. destruct HI as (LenTI & _). cbn [la_TI la_s] in *. rewrite LenTI. nia. }
exists (lzw_add_init idl (px PIX (la_s X)) (px PIX (la_s X + 1)) (lzw_emit (px PIX (la_s X)) ms)).
split; [split|].
- apply tabs_rel_ti; [apply tabs_rel_emit; exact HR | lia | lia | lia | exact HlenTI].
- cbn [lzw_add_init lzw_emit l_codes rev v_LD]. rewrite HL. reflexivity.
- destruct X as [TI LM LI TM s lp dp mp Cn R]. cbn [st_ti la_s] in *.
destruct (Z.leb_spec idl (px PIX (s + 1))) as [|_]; [lia|]. exact HF.
Qed.
Lemma sim_head_timiss_rst : forall X V FIN c1 c2 s', sim_head X V FIN ->
c1 = px PIX (la_s X) -> c2 = px PIX (la_s X + 1) -> c1 < idl -> c2 < idl -> nth (Z.to_nat (c1 * idl + c2)) (la_TI X) 0 = 0 ->
0 <= la_s X -> la_s X + 1 < nP -> la_dp X = 4096 -> s' = la_s X + 1 ->
sim_head (st_reset idl X (s' - 1)) (mkLV (repeat 0 4096) ((v_LD V ++ [c1]) ++ [idl])) FIN.
Proof.
intros X V FIN c1 c2 s' (ms & (HR & HL) & HF) -> -> Hc1 Hc2 HTI0 Hs0 Hs1 Hdp ->.
pose proof (HPIX (la_s X)) as P1. pose proof (HPIX (la_s X + 1)) as P2.
destruct (Z.leb_spec idl (px PIX (la_s X))) as [|_]; [lia|].
rewrite skipn_px, lzw_run_cons in HF by lia. destruct (Z.leb_spec idl (px PIX (la_s X + 1))) as [|_]; [lia|]. cbv zeta in HF.
rewrite <- (init_child_model idl X (v_LC V) ms _ _ HR), HTI0 in HF by lia. cbn [Z.eqb] in HF.
assert (Edp : l_dictPos (lzw_emit (px PIX (la_s X)) ms) = la_dp X) by (destruct HR as (_ & _ & _ & _ & _ & E & _); symmetry; exact E).
rewrite Edp, Hdp in HF. change (4096 <? MAX_DICT_LEN) with false in HF. cbv iota in HF.
exists (lzw_reset idl (lzw_emit (px PIX (la_s X)) ms)).
split; [split|].
- apply tabs_rel_reset; lia.
- cbn [lzw_reset lzw_emit l_codes rev v_LD]. rewrite HL. reflexivity.
- destruct X as [TI LM LI TM s lp dp mp Cn R]. cbn [st_reset la_s] in *. replace (s + 1 - 1 + 1) with (s + 1) by lia.
destruct (Z.leb_spec idl (px PIX (s + 1))) as [|_]; [lia|]. exact HF.
Qed.
Lemma sim_head_inner : forall X V FIN q, sim_head X V FIN ->
px PIX (la_s X) < idl -> px PIX (la_s X + 1) < idl -> q = init_child idl X (px PIX (la_s X)) (px PIX (la_s X + 1)) -> q <> 0 ->
0 <= la_s X -> la_s X + 1 < nP -> sim_inner X V (la_s X + 2) q FIN.
Proof.
intros X V FIN q (ms & HIV & HF) Hc1 Hc2 -> Hq0 Hs0 Hs1. pose proof (HPIX (la_s X)) as P1. pose proof (HPIX (la_s X + 1)) as P2.
destruct (Z.leb_spec idl (px PIX (la_s X))) as [|_]; [lia|].
rewrite skipn_px, lzw_run_cons in HF by lia. destruct (Z.leb_spec idl (px PIX (la_s X + 1))) as [|_]; [lia|]. cbv zeta in HF.
unfold init_child in *. rewrite <- (init_child_model idl X (v_LC V) ms _ _ (proj1 HIV)) in HF by lia.
destruct (Z.eqb_spec (nth (Z.to_nat (px PIX (la_s X) * idl + px PIX (la_s X + 1))) (la_TI X) 0) 0) as [E | _]; [contradiction|].
exists ms. split; [exact HIV|]. replace (la_s X + 2) with (la_s X + 1 + 1) by lia. exact HF.
Qed.
Lemma LM_bounds : forall X q, lzw_inv idl nP X -> 0 <= q < 4096 -> 0 <= nth (Z.to_nat q) (la_LM X) 0 < la_mp X.
Proof.
intros [TI LM LI TM s lp dp mp Cn R] q HI Hq. destruct HI as (_ & LenLM & _ & _ & _ & _ & BLM & _). cbn [la_LM la_mp].
apply below_nth; [exact BLM | rewrite LenLM; lia].
Qed.
Lemma sim_inner_eidx : forall X V FIN s1 q, sim_inner X V s1 q FIN -> 0 <= s1 < nP -> idl <= px PIX s1 -> FIN = None.
Proof.
intros X V FIN s1 q (ms & _ & HF) Hs Hc. rewrite skipn_px, lzw_run_cons in HF by lia.
destruct (Z.leb_spec idl (px PIX s1)); [symmetry; exact HF | lia].
Qed.
Lemma sim_inner_cont : forall X V FIN s1 q q', sim_inner X V s1 q FIN -> lzw_inv idl nP X -> 0 <= q < 4096 -> 0 <= s1 < nP ->
px PIX s1 < idl -> q' = child_abs idl X (v_LC V) q (px PIX s1) -> q' <> 0 -> sim_inner X V (s1 + 1) q' FIN.
Proof.
intros X V FIN s1 q q' (ms & HIV & HF) HI Hq Hs Hc -> Hq0. pose proof (HPIX s1) as P1. pose proof (LM_bounds X q HI Hq) as BLM.
rewrite skipn_px, lzw_run_cons in HF by lia. destruct (Z.leb_spec idl (px PIX s1)) as [|_]; [lia|]. cbv zeta in HF.
rewrite <- (child_abs_model idl X (v_LC V) ms q _ (proj1 HIV)) in HF by lia.
destruct (Z.eqb_spec (child_abs idl X (v_LC V) q (px PIX s1)) 0) as [E | _]; [contradiction|].
exists ms. split; [exact HIV | exact HF].
Qed.
Lemma sim_inner_emitc : forall X V FIN s1 q q', sim_inner X V s1 q FIN -> lzw_inv idl nP X -> 0 <= q < 4096 -> 0 <= s1 -> s1 = nP - 1 ->
px PIX s1 < idl -> q' = child_abs idl X (v_LC V) q (px PIX s1) -> q' <> 0 ->
sim_exit (st_typec nP X) (mkLV (v_LC V) (v_LD V ++ [q'])) FIN.
Proof.
intros X V FIN s1 q q' HS HI Hq Hs0 Hs Hc Hq' Hq0.
destruct (sim_inner_cont X V FIN s1 q q' HS HI Hq ltac:(lia) Hc Hq' Hq0) as (ms & (HR & HL) & HF).
replace (s1 + 1) with nP in HF by lia. rewrite skipn_end, lzw_run_nil in HF.
exists (lzw_emit q' ms). split; [split; [apply tabs_rel_typec; exact HR | cbn [lzw_emit l_codes rev v_LD]; rewrite HL; reflexivity] | symmetry; exact HF].
Qed.
Lemma sim_miss_unfold : forall X V FIN s1 q, sim_inner X V s1 q FIN -> lzw_inv idl nP X -> 0 <= q < 4096 -> 0 <= s1 < nP ->
px PIX s1 < idl -> child_abs idl X (v_LC V) q (px PIX s1) = 0 ->
exists ms, sim_inv X V ms /\
lzw_run idl (if la_dp X <? 4096 then lzw_add_child idl q (px PIX s1) (lzw_emit q ms) else lzw_reset idl (lzw_emit q ms)) (px PIX s1) true (skipn (Z.to_nat (s1 + 1)) PIX) = FIN.
Proof.
intros X V FIN s1 q (ms & HIV & HF) HI Hq Hs Hc Hch. pose proof (HPIX s1) as P1. pose proof (LM_bounds X q HI Hq) as BLM.
rewrite skipn_px, lzw_run_cons in HF by lia. destruct (Z.leb_spec idl (px PIX s1)) as [|_]; [lia|]. cbv zeta in HF.
rewrite <- (child_abs_model idl X (v_LC V) ms q _ (proj1 HIV)), Hch in HF by lia. cbn [Z.eqb] in HF.
assert (Edp : l_dictPos (lzw_emit q ms) = la_dp X) by (destruct HIV as ((_ & _ & _ & _ & _ & E & _) & _); symmetry; exact E).
rewrite Edp in HF. exists ms. split; [exact HIV | exact HF].
Qed.
Lemma sim_head_of : forall X' V' ms' FIN c s1, sim_inv X' V' ms' -> la_s X' = s1 -> c = px PIX s1 -> c < idl ->
lzw_run idl ms' c true (skipn (Z.to_nat (s1 + 1)) PIX) = FIN -> sim_head X' V' FIN.
Proof.
intros X' V' ms' FIN c s1 HIV Hs -> Hc HF. exists ms'. split; [exact HIV|]. rewrite Hs.
destruct (Z.leb_spec idl (px PIX s1)) as [|_]; [lia | exact HF].
Qed.
Lemma sim_miss_rst : forall X V FIN s1 q c, sim_inner X V s1 q FIN -> lzw_inv idl nP X -> 0 <= q < 4096 -> 0 <= s1 < nP ->
c = px PIX s1 -> c < idl -> child_abs idl X (v_LC V) q c = 0 -> la_dp X = 4096 ->
sim_head (st_reset idl X (s1 - 1)) (mkLV (repeat 0 4096) ((v_LD V ++ [q]) ++ [idl])) FIN.
Proof.
intros X V FIN s1 q c HS HI Hq Hs -> Hc Hch Hdp. destruct (sim_miss_unfold X V FIN s1 q HS HI Hq Hs Hc Hch) as (ms & (HR & HL) & HF).
rewrite Hdp in HF. change (4096 <? 4096) with false in HF. cbv iota in HF.
eapply (sim_head_of _ _ _ FIN (px PIX s1) s1); [split | | reflexivity | exact Hc | exact HF].
- apply tabs_rel_reset; lia.
- cbn [lzw_reset lzw_emit l_codes rev v_LD]. rewrite HL. reflexivity.
- destruct X as [TI LM LI TM s lp dp mp Cn R]; cbn [st_reset la_s]. lia.
Qed.
Lemma sim_miss_map : forall X V FIN s1 q c, sim_inner X V s1 q FIN -> lzw_inv idl nP X -> 0 <= q < 4096 -> 0 <= s1 < nP ->
c = px PIX s1 -> c < idl -> child_abs idl X (v_LC V) q c = 0 -> la_dp X < 4096 -> nth (Z.to_nat q) (la_LM X) 0 <> 0 ->
sim_head (vx_map idl X (nth (Z.to_nat q) (la_LM X) 0) c s1) (mkLV (v_LC V) (v_LD V ++ [q])) FIN.
Proof.
intros X V FIN s1 q c HS HI Hq Hs -> Hc Hch Hdp HLM. destruct (sim_miss_unfold X V FIN s1 q HS HI Hq Hs Hc Hch) as (ms & (HR & HL) & HF).
destruct (Z.ltb_spec (la_dp X) 4096) as [_|]; [|lia]. pose proof (HPIX s1) as P1. pose proof (LM_bounds X q HI Hq) as BLM.
pose proof (mp_bound idl nP X ltac:(lia) HI) as Hmp.
eapply (sim_head_of _ _ _ FIN (px PIX s1) s1); [split | | reflexivity | exact Hc | exact HF].
- apply tabs_rel_map; [apply tabs_rel_emit; exact HR | lia | exact Hq | lia | lia |].
destruct X as [TI LM LI TM s lp dp mp Cn R]. destruct HI as (_ & _ & _ & LenTM & _). cbn [la_TM la_LM la_mp] in *. rewrite LenTM. nia.
- cbn [lzw_emit l_codes rev v_LD]. unfold lzw_add_child. cbn [lzw_emit l_lmap l_lidx l_codes l_dictPos l_mapPos l_init l_lcol l_tmap].
destruct (_ =? 0); [destruct (_ =? 0)|]; cbn [l_codes rev]; rewrite HL; reflexivity.
- destruct X as [TI LM LI TM s lp dp mp Cn R]; reflexivity.
Qed.
Lemma sim_miss_first : forall X V FIN s1 q c, sim_inner X V s1 q FIN -> lzw_inv idl nP X -> 0 <= q < 4096 -> 0 <= s1 < nP ->
c = px PIX s1 -> c < idl -> child_abs idl X (v_LC V) q c = 0 -> la_dp X < 4096 -> length (v_LC V) = 4096%nat ->
nth (Z.to_nat q) (la_LM X) 0 = 0 -> nth (Z.to_nat q) (la_LI X) 0 = 0 ->
sim_head (vx_first X q s1) (mkLV (updn (v_LC V) (Z.to_nat q) c) (v_LD V ++ [q])) FIN.
Proof.
intros X V FIN s1 q c HS HI Hq Hs -> Hc Hch Hdp LenLC HLM HLI. destruct (sim_miss_unfold X V FIN s1 q HS HI Hq Hs Hc Hch) as (ms & (HR & HL) & HF).
destruct (Z.ltb_spec (la_dp X) 4096) as [_|]; [|lia].
eapply (sim_head_of _ _ _ FIN (px PIX s1) s1); [split | | reflexivity | exact Hc | exact HF].
- cbn [v_LC]. apply tabs_rel_first; [apply tabs_rel_emit; exact HR | exact Hq | | rewrite LenLC; lia | exact HLM | exact HLI].
destruct X as [TI LM LI TM s lp dp mp Cn R]. destruct HI as (_ & _ & LenLI & _). cbn [la_LI]. rewrite LenLI. lia.
- cbn [lzw_emit l_codes rev v_LD]. unfold lzw_add_child. cbn [lzw_emit l_lmap l_lidx l_codes l_dictPos l_mapPos l_init l_lcol l_tmap].
destruct (_ =? 0); [destruct (_ =? 0)|]; cbn [l_codes rev]; rewrite HL; reflexivity.
- destruct X as [TI LM LI TM s lp dp mp Cn R]; reflexivity.
Qed.
Lemma sim_miss_switch : forall X V FIN s1 q c, sim_inner X V s1 q FIN -> lzw_inv idl nP X -> 0 <= q < 4096 -> 0 <= s1 < nP ->
c = px PIX s1 -> c < idl -> child_abs idl X (v_LC V) q c = 0 -> la_dp X < 4096 ->
nth (Z.to_nat q) (la_LM X) 0 = 0 -> nth (Z.to_nat q) (la_LI X) 0 <> 0 ->
sim_head (vx_switch idl X q c s1) (mkLV (v_LC V) (v_LD V ++ [q])) FIN.
Proof.
intros X V FIN s1 q c HS HI Hq Hs -> Hc Hch Hdp HLM HLI. destruct (sim_miss_unfold X V FIN s1 q HS HI Hq Hs Hc Hch) as (ms & (HR & HL) & HF).
destruct (Z.ltb_spec (la_dp X) 4096) as [_|]; [|lia]. pose proof (HPIX s1) as P1.
pose proof (mp_bound idl nP X ltac:(lia) HI) as Hmp.
eapply (sim_head_of _ _ _ FIN (px PIX s1) s1); [split | | reflexivity | exact Hc | exact HF].
- apply tabs_rel_switch; [apply tabs_rel_emit; exact HR | lia | exact Hq | lia | lia | | | exact HLM | exact HLI];
destruct X as [TI LM LI TM s lp dp mp Cn R]; destruct HI as (_ & LenLM & _ & LenTM & _); cbn [la_TM la_LM la_mp] in *; [rewrite LenLM; lia | rewrite LenTM; nia].
- cbn [lzw_emit l_codes rev v_LD]. unfold lzw_add_child. cbn [lzw_emit l_lmap l_lidx l_codes l_dictPos l_mapPos l_init l_lcol l_tmap].
destruct (_ =? 0); [destruct (_ =? 0)|]; cbn [l_codes rev]; rewrite HL; reflexivity.
- destruct X as [TI LM LI TM s lp dp mp Cn R]; reflexivity.
Qed.
Definition lzw_fin : option lzw_st :=
if idl <=? px PIX 0 then None else lzw_run idl (lzw_reset idl (mkLzw zm_empty zm_empty zm_empty zm_empty zm_empty 0 0 [])) (px PIX 0) true (skipn 1 PIX).
Lemma sim_init : forall X0 TM Cn R lp, X0 = mkLA (repeat 0 (Z.to_nat (idl * idl))) (repeat 0 4096) (repeat 0 4096) TM 0 lp (idl + 2) 1 Cn R ->
sim_head X0 (mkLV (repeat 0 4096) [idl]) lzw_fin.
Proof.
intros X0 TM Cn R lp ->. exists (lzw_reset idl (mkLzw zm_empty zm_empty zm_empty zm_empty zm_empty 0 0 [])). split; [split|].
- apply (tabs_rel_reset idl (mkLA [] [] [] TM 0 (lp - 2) 0 0 (Cn - 1) (R - 1)) _ (-1)). lia.
- reflexivity.
- cbn [la_s]. reflexivity.
Qed.
Lemma sim_codes : 1 <= nP -> lzw_codes idl PIX = match lzw_fin with None => None | Some s => Some (rev (l_codes s) ++ [idl + 1]) end.
Proof.
intros HnP. unfold lzw_codes, lzw_fin, px. destruct PIX as [|p0 rest]; [cbn in LenPIX; lia|]. change (Z.to_nat 0) with 0%nat. cbn [nth skipn].
destruct (idl <=? p0); [reflexivity|]. destruct (lzw_run _ _ _ _ _); reflexivity.
Qed.
End a.
Definition raster_of (L initCodeLen : Z) (codes : list Z) : list Z :=
let bl := create_byte_list L initCodeLen codes in blocks255 (S (length bl)) bl.
Lemma lzw_stream_raster : forall L icl img, lzw_stream L icl img = option_map (raster_of L icl) (lzw_codes L img).
Proof. intros L icl img. unfold lzw_stream, raster_of. destruct (lzw_codes L img); reflexivity. Qed.
