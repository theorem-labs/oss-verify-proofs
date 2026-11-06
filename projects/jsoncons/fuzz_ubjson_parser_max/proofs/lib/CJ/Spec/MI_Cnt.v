(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import Malloc MI_Arith.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_MI_Cnt () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Cnt.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."], [["1bool"; "1nat"; "1true"; "2False"; "2and"; "2eq"; "2ex"; "2iff"; "3Z"; "4ag_check_sc"; "4cnt0_list"; "4cnt0_of"; "4he_list"; "4mono_f"; "4nest_ok"; "4stc_f"]; ["4stc_k"; "4zrange"; "5IB"; "5MMAP_THRESHOLD"; "5UNIT"; "5halve_even"; "5mask_upto"; "5round_up_pg"; "5size_class"; "5size_to_class"; "6In"; "6forallb"; "7add"; "7even"; "7ldiff"; "7le"]; ["7lor"; "7lt"; "7modulo"; "7mul"; "7pow"; "7shiftr"; "7sub"; "7testbit"; "0a"; "0ai"; "0avail"; "0b"; "0c"; "0cnt"; "0f"; "0freed"]; ["0i"; "0j"; "0last"; "0lo"; "0n"; "0n'"; "0q"; "0sc"; "0size"; "0u"; "0x"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition zrange (lo n : Z) : list Z := map (fun i => lo + Z.of_nat i) (seq 0 (Z.to_nat n)).
Lemma in_zrange : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Cnt "H'8&Ozr2%3221&7&J&Ar4r3%3221%53;81'4%<25:&Q1&L%1287%32>1%6251%>281p0@1pSFE1pS:F1pS8G1").
Proof. intros lo n x.
intros Hn. unfold zrange. rewrite in_map_iff. split.
- intros (i & <- & Hi). apply in_seq in Hi. lia.
- intros H. exists (Z.to_nat (x - lo)). split; [lia|]. apply in_seq. lia.
Qed.
Lemma forallb_zrange : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Cnt "Q2'8'0p021'5&Kr4&Ar3r2%3221%63:51(2%93;21&Oz%2218'4r5%521;&Q1&L%124@%32?1%7251r7%11D%G3I1?p041p0=1p0A1pSFN1pS:O1pS8Q01pRNO1").
Proof. intros f lo n x. intros H Hn Hx. rewrite forallb_forall in H. apply H. apply in_zrange; assumption. Qed.
Definition mono_f (a : Z) : bool := forallb (fun b => negb (a <? b) || (size_class a <? size_class b)) (zrange 0 48).
Lemma mono_b_true : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Cnt "<'5'0&K'8&=&Az+Q@%3221%73651(2%;3:21"). Proof. vm_compute. reflexivity. Qed.
Lemma size_class_lt : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Cnt "G'8'4&Ozr2%3221&Q1+Q@%2241%8241r4r3%6221&Hr5%211%316%;221p061p0:1p0;1pRHE1pRBF1").
Proof. intros a b.
intros Ha Hb Hab. pose proof (forallb_zrange mono_f 0 48 a mono_b_true ltac:(lia) ltac:(lia)) as H. unfold mono_f in H.
pose proof (forallb_zrange _ 0 48 b H ltac:(lia) ltac:(lia)) as H2. cbn beta in H2.
apply orb_true_iff in H2. destruct H2 as [H2|H2]; [apply negb_true_iff in H2; apply Z.ltb_ge in H2; lia| apply Z.ltb_lt in H2; exact H2].
Qed.
Lemma size_class_le : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Cnt "G'8'4&Ozr2%3221&Q1+Q@%2241%8241r4r3%:221&Hr5%211%316%?221p061p0:1p0;1pRHE1pRBF1").
Proof. intros a b. intros. destruct (Z.eq_dec a b) as [->|]; [lia|]. pose proof (size_class_lt a b). lia. Qed.
Lemma size_class_lt_inv : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Cnt "G'8'4&Ozr2%3221&Q1+Q@%2241%8241&Hr4%211r3%411%9231r5%;216p031p0:1p0;1pRHE1pRBF1").
Proof. intros a b. intros. destruct (Z.lt_ge_cases a b); [assumption|]. pose proof (size_class_le b a). lia. Qed.
Definition stc_k (k : Z) : Z :=
if k <? 10 then k else
let n := k + 1 in
let i := (28 - clz32 n) * 4 + 8 in
let i := if size_class (i + 1) <? n then i + 2 else i in
if size_class i <? n then i + 1 else i.
Lemma size_to_class_k : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Cnt "B'8'5&Ir1%211&@&Q5&Q6&L&B%2271+1%5221+4%8221%:11%?3@<1pS:A1").
Proof. intros n. reflexivity. Qed.
Definition stc_f (k : Z) : bool := let sc := stc_k k in (0 <=? sc) && (sc <? 48) && (k + 1 <=? size_class sc).
Lemma stc_ok_b_true : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Cnt "<'5'0&K'8&?&Az+WoO%3221%73651(2%;3:21"). Proof. vm_compute. reflexivity. Qed.
Lemma size_to_class_ok : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Cnt "M'8'4&Ozr1%3221&Q1&C%2241%8241&Ir2%211%;2:1+Q@%9231%?231&L&B%2281&Q3&D&H%11;%4231%G261%I2:1p0B1pS:L1").
Proof. intros n.
intros Hn. rewrite size_to_class_k. rewrite Z.shiftr_div_pow2 by lia. unfold IB, UNIT, MMAP_THRESHOLD in *.
set (k := (n + 4 - 1) / 2 ^ 4).
assert (Hk : 0 <= k < 8191) by (subst k; change (2 ^ 4) with 16; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
assert (Hk2 : 16 * k <= n + 3 < 16 * k + 16) by (subst k; change (2 ^ 4) with 16; pose proof (Z.div_mod (n + 4 - 1) 16 ltac:(lia)); pose proof (Z.mod_pos_bound (n + 4 - 1) 16 ltac:(lia)); lia).
pose proof (forallb_zrange stc_f 0 8191 k stc_ok_b_true ltac:(lia) ltac:(lia)) as H. unfold stc_f in H. cbn zeta in H.
apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. lia.
Qed.
Lemma lor1_even : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Cnt "F'8&Ozr1%3221'5'0&Mr2%211(2%63521&Q0r3+1%3221&L%1243%=3B31p081p0@1pS@E1").
Proof. intros sc.
intros H He. assert (HE : Z.Even sc) by (apply Z.even_spec; exact He). destruct HE as [m ->].
apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
destruct (Z.eq_dec i 0) as [->|NZ].
- rewrite !Z.bit0_odd. replace (2 * m + 1) with (Z.succ (2 * m)) by lia. rewrite Z.odd_succ, He. change (Z.odd 1) with true. apply orb_true_r.
- assert (T1 : forall k, 0 <= k -> Z.testbit 1 (Z.succ k) = false).
{ intros k Hk. change (Z.testbit 1) with (Z.testbit (2 * 0 + 1)). rewrite Z.testbit_odd_succ by exact Hk. apply Z.testbit_0_l. }
replace i with (Z.succ (i - 1)) by lia. rewrite Z.testbit_even_succ, Z.testbit_odd_succ, T1 by lia.
apply orb_false_r.
Qed.
Fixpoint he_list (f : nat) (c : Z) : list Z :=
match f with
| O => [c]
| S f' => c :: (if Z.even c then he_list f' (Z.shiftr c 1) else [])
end.
Lemma halve_even_in : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Cnt ">'1'8&J&Er3r2r1%43321&<%1254%83931pSD:1pRJ;1pRN=1").
Proof. intros f.
induction f as [|f IH]; intros c u; cbn [halve_even he_list]; [left; reflexivity|].
destruct (Z.even c); cbn [andb]; [| left; reflexivity].
destruct (u <? 4 * c); [right; apply IH| left; reflexivity].
Qed.
Definition cnt0_list (sc : Z) : list Z :=
let size := UNIT * size_class sc in
if sc <? 9 then [small_cnt sc 0; small_cnt sc 1; small_cnt sc 2]
else map (fun c => halve_big 8 c size) (he_list 8 (med_cnt (Z.land sc 3))).
Definition cnt0_of (sc u : Z) : Z :=
if sc <? 9 then small_cnt_pick sc u
else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) u) (UNIT * size_class sc).
Lemma cnt0_in : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Cnt ";'8&J&;r2r1%3221&:%114%73831pSD91pS@:1").
Proof. intros sc u.
unfold cnt0_of, cnt0_list. destruct (sc <? 9).
- unfold small_cnt_pick. destruct (negb (u <? 4 * small_cnt sc 0)); [left; reflexivity|].
destruct (negb (u <? 4 * small_cnt sc 1)); [right; left; reflexivity| right; right; left; reflexivity].
- apply (in_map (fun c => halve_big 8 c (UNIT * size_class sc))). apply halve_even_in.
Qed.
Definition bump (size c : Z) : Z := if (c =? 1) && (size * c + UNIT <=? PGSZ / 2) then 2 else c.
Definition adj (sc size cnt : Z) : Z :=
if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
else cnt.
Definition grp_ok (sc cnt needed : Z) : bool :=
let size := UNIT * size_class sc in
let maplen := Z.shiftr needed 12 in
let last := cnt - 1 in
let stride := if (last =? 0) && negb (maplen =? 0) then maplen * 4096 - UNIT else size in
(1 <=? cnt) && (cnt <=? 32) && (needed mod 4096 =? 0) && (4096 <=? needed) && (needed <=? 2 ^ 20)
&& (UNIT + stride * cnt <=? maplen * 4096)
&& ((stride <=? size) || (28 <=? sc))
&& (negb (last =? 0) || (27 <=? sc))
&& (stride * cnt <? 2 ^ 20) && (16 <=? stride) && (stride mod 16 =? 0).
Definition nest_ok (sc cnt : Z) : bool :=
let size := UNIT * size_class sc in
let n' := UNIT + cnt * size - IB in
let j := size_to_class n' in
(2 <=? cnt) && (cnt <=? 32) && (sc <? j) && (j <=? 23) && (UNIT + cnt * size <=? UNIT * size_class j) && (size * cnt <? 2 ^ 20)
&& (0 <=? n') && (n' + IB <=? 2048).
Definition qmax (sc : Z) : Z := (UNIT * size_class sc + UNIT + 4095) / 4096.
Definition ag_check_sc (sc : Z) : bool :=
let size := UNIT * size_class sc in
forallb (fun cnt0 =>
let cnt1 := bump size cnt0 in
if PGSZ / 2 <? size * cnt1 + UNIT then
forallb (fun cnt2 =>
grp_ok sc cnt2 (round_up_pg (size * cnt2 + UNIT))
&& (negb (cnt2 <=? 7)
|| forallb (fun q => negb ((q * 4096 <? size + UNIT) || (4 <=? q)) || (grp_ok sc 1 (q * 4096) && (28 <=? sc))) (zrange 1 (qmax sc))))
[cnt1; adj sc size cnt1]
else nest_ok sc cnt1)
(cnt0_list sc).
Lemma ag_check_true : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Cnt "<'5'0&K'8&9&Az+Q@%3221%73651(2%;3:21").
Proof. vm_compute. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_grp_ok_sound := (forall sc cnt needed, grp_ok sc cnt needed = true ->
let size := UNIT * size_class sc in
let maplen := Z.shiftr needed 12 in
let last := cnt - 1 in
let stride := if (last =? 0) && negb (maplen =? 0) then maplen * 4096 - UNIT else size in
1 <= cnt <= 32 /\ needed mod 4096 = 0 /\ 4096 <= needed <= 2 ^ 20 /\ maplen = needed / 4096 /\ 1 <= maplen <= 256
/\ UNIT + stride * cnt <= maplen * 4096 /\ (stride <= size \/ 28 <= sc) /\ (last = 0 -> 27 <= sc)
/\ stride * cnt < 2 ^ 20 /\ 16 <= stride /\ stride mod 16 = 0) (only parsing).
Variable sc : ltac:(sec_ty2 constr:(SEC_T_grp_ok_sound) 0%nat 0%nat).
Variable cnt : ltac:(sec_ty2 constr:(SEC_T_grp_ok_sound) 1%nat 0%nat).
Variable needed : ltac:(sec_ty2 constr:(SEC_T_grp_ok_sound) 2%nat 0%nat).
Lemma grp_ok_sound : ltac:(sec_stmt2 constr:(SEC_T_grp_ok_sound) 3%nat 0%nat).
Proof.
unfold grp_ok. intros H. cbn zeta. rewrite Z.shiftr_div_pow2 in * by lia. change (2 ^ 12) with 4096 in *.
repeat (apply andb_true_iff in H as [H ?]).
repeat match goal with
| K : (_ <=? _) = true |- _ => apply Z.leb_le in K
| K : (_ <? _) = true |- _ => apply Z.ltb_lt in K
| K : (_ =? _) = true |- _ => apply Z.eqb_eq in K
| K : (_ || _) = true |- _ => apply orb_true_iff in K
end.
assert (1 <= needed / 4096 <= 256) by (split; [apply Z.div_le_lower_bound; lia| apply Z.div_le_upper_bound; lia]).
repeat split; try assumption; lia.
Qed.
End SE.
Lemma nest_ok_sound : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Cnt "QO'8'5'0&>r2r1%3221(2%73621&Q3&D&Hr3%211%5241&Q6&L%825<%2281&B%5221&I%11A'4&O+2r5%3221+Q0%5231%7231&Q1r6%221L+G%;2N1%=231%L2;I%F2L1%L1Q2%O2N1%A231%Q12N@&Q4+D%22D1%?241z%H21Q<%Q12Q=N+RP0%K221%M241%N271%O2=1%Q02C1%Q12J1tS4QIQ31tS<QJQ61tSBQKQ=1p0QD1pRLQM1pS@QN1").
Proof. intros sc cnt.
unfold nest_ok. intros H. cbn zeta.
repeat (apply andb_true_iff in H as [H ?]).
repeat match goal with
| K : (_ <=? _) = true |- _ => apply Z.leb_le in K
| K : (_ <? _) = true |- _ => apply Z.ltb_lt in K
end. repeat split; assumption.
Qed.
Lemma round_up_pg_spec : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Cnt "D'8'4&Or1&G%112%4231&Q1&L+TP0%2271%4261%;261'5&Q2%12:6z%43A21%A261pSFC1").
Proof. intros x.
unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.pred (2 ^ 12)). rewrite <- Z.ones_equiv, Z.land_ones by lia.
change (2 ^ 12) with 4096.
pose proof (Z.mod_pos_bound (- x) 4096 ltac:(lia)) as B. pose proof (Z.div_mod (- x) 4096 ltac:(lia)) as D.
split; [lia|]. replace (x + - x mod 4096) with ((- ((- x) / 4096)) * 4096) by lia. apply Z.mod_mul. lia.
Qed.
Lemma round_up_pg_pages : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Cnt "N'8&Q1zr1%3221'6'4'5&Gr3%211&Q3+TP0%22:1%73>41&O+1%221>&Q6%12@3%9218%D21<%72=9%A221%B271%C2;1qS>J1%F2K1p0H1pSFM1").
Proof. intros x.
intros Hx. destruct (round_up_pg_spec x) as [A B].
exists (round_up_pg x / 4096). pose proof (Z.div_mod (round_up_pg x) 4096 ltac:(lia)). rewrite B in H. nia.
Qed.
Theorem alloc_group_arith sc req u0 u1 (nosmall : bool) :
0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
let size := UNIT * size_class sc in
let cnt0 := cnt0_of sc u0 in
let cnt1 := if (cnt0 =? 1) && (size * cnt0 + UNIT <=? PGSZ / 2) then 2 else cnt0 in
(PGSZ / 2 < size * cnt1 + UNIT ->
let cnt2 :=
if (u1 <? 4 * cnt1) && negb nosmall then
if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt1) then 2
else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt1) then 3
else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt1) then 3
else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt1) then 5
else cnt1
else cnt1 in
let needed := round_up_pg (size * cnt2 + UNIT) in
let '(cnt3, needed3) :=
if negb nosmall && (cnt2 <=? 7) then
let req' := round_up_pg (req + IB + UNIT) in
if (req' <? size + UNIT) || ((4 * PGSZ <=? req') && (u1 <? 2 * cnt2)) then (1, req') else (cnt2, needed)
else (cnt2, needed) in
grp_ok sc cnt3 needed3 = true
/\ ((cnt3 = 1 /\ needed3 = round_up_pg (req + IB + UNIT) /\ 28 <= sc) \/ (cnt3 = cnt2 /\ needed3 = needed /\ size * cnt2 + UNIT <= needed)))
/\ (size * cnt1 + UNIT <= PGSZ / 2 -> nest_ok sc cnt1 = true).
Proof.
intros Hsc Hreq Hfit. cbn zeta.
pose proof (forallb_zrange ag_check_sc 0 48 sc ag_check_true ltac:(lia) ltac:(lia)) as H. unfold ag_check_sc in H.
rewrite forallb_forall in H. specialize (H _ (cnt0_in sc u0)). cbn beta in H. fold (bump (UNIT * size_class sc) (cnt0_of sc u0)) in H |- *.
set (cnt1 := bump (UNIT * size_class sc) (cnt0_of sc u0)) in *. clearbody cnt1.
split.
- intros HB. rewrite (proj2 (Z.ltb_lt _ _) HB) in H. rewrite forallb_forall in H.
set (cnt2 := if (u1 <? 4 * cnt1) && negb nosmall then _ else cnt1).
assert (Hc2 : In cnt2 [cnt1; adj sc (UNIT * size_class sc) cnt1]).
{ subst cnt2. destruct ((u1 <? 4 * cnt1) && negb nosmall); [right; left; reflexivity| left; reflexivity]. }
specialize (H _ Hc2). clearbody cnt2. apply andb_true_iff in H as [G1 G2].
destruct (negb nosmall && (cnt2 <=? 7)) eqn:E7.
+ destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * cnt2))) eqn:ER.
* apply andb_true_iff in E7 as [_ E7]. rewrite E7 in G2. cbn [negb orb] in G2. rewrite forallb_forall in G2.
destruct (round_up_pg_pages (req + IB + UNIT) ltac:(unfold IB, UNIT; lia)) as (q & Eq & Hq1 & Hq2). rewrite Eq in *.
assert (Hq : In q (zrange 1 (qmax sc))).
{ apply in_zrange; [unfold qmax, UNIT; apply Z.div_pos; [pose proof (size_class_bound sc Hsc); lia| lia]|].
split; [lia|]. unfold qmax. unfold IB, UNIT, PGSZ in *.
assert (q <= (16 * size_class sc + 16 + 4095) / 4096) by (apply Z.div_le_lower_bound; lia). lia. }
specialize (G2 _ Hq). cbn beta in G2.
assert (EC : (q * 4096 <? UNIT * size_class sc + UNIT) || (4 <=? q) = true).
{ apply orb_true_iff in ER. apply orb_true_iff. destruct ER as [ER|ER]; [left; exact ER| right].
apply andb_true_iff in ER as [ER _]. apply Z.leb_le in ER. apply Z.leb_le. unfold PGSZ in ER. lia. }
rewrite EC in G2. cbn [negb orb] in G2. apply andb_true_iff in G2 as [G2 G28]. apply Z.leb_le in G28.
split; [exact G2| left; split; [reflexivity| split; [reflexivity| exact G28]]].
* split; [exact G1| right; split; [reflexivity| split; [reflexivity| apply (proj1 (round_up_pg_spec _))]]].
+ split; [exact G1| right; split; [reflexivity| split; [reflexivity| apply (proj1 (round_up_pg_spec _))]]].
- intros HN. assert (E : (PGSZ / 2 <? UNIT * size_class sc * cnt1 + UNIT) = false) by (apply Z.ltb_ge; lia).
rewrite E in H. exact H.
Qed.
Lemma clamp_ai size cnt : 1 <= cnt ->
let ai := (4096 - UNIT) / size - 1 in
let ai := if cnt - 1 <? ai then cnt - 1 else ai in
let ai := if ai <? 0 then 0 else ai in
0 <= ai <= cnt - 1.
Proof.
intros Hc. cbn zeta. destruct (Z.ltb_spec (cnt - 1) ((4096 - UNIT) / size - 1)).
- destruct (Z.ltb_spec (cnt - 1) 0); lia.
- destruct (Z.ltb_spec ((4096 - UNIT) / size - 1) 0); lia.
Qed.
Lemma created_masks : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Cnt "R:'8'4&Ozr2%3221r1%5231%7231+O%8261&Fr4%211&Q6%1229%>2=:'5'0&Q7%128@(2%53421r3r9%G221p041p0;1pS2L1%:26I%=3<19r8%N291p031p0B1pS2Q31%A2H=%D3C1@'3p021p0B1p0I1pS2Q:1&Q1r7%221Q7r6%Q=2Q91%Q?231p01CpS2QB1%QA2Q=7%QC2Q41p01OpS2QF1&Nr5%Q>11%Q?1<%4221%Q;3QLQF1%QL271%QM2<1%QN2E1%QO2M1%R02Q51%R12QB1%R22QN1tS0R4QE1tRFR5QH1p0QL1p0QO1pS6R81pRDR91").
Proof. intros ai last.
intros Hai Hl. cbn zeta.
assert (EF : mask_upto last - mask_upto ai = Z.ldiff (mask_upto last) (mask_upto ai)).
{ apply Z.sub_nocarry_ldiff. apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.bits_0, !testbit_mask_upto by lia.
destruct (Z.leb_spec i ai); destruct (Z.leb_spec i last); cbn; try reflexivity. lia. }
rewrite EF. pose proof (mask_upto_nonneg ai ltac:(lia)). pose proof (mask_upto_nonneg last ltac:(lia)).
split; [assumption|]. split; [apply Z.ldiff_nonneg; left; assumption|].
split; [intros i Hi Hb; rewrite testbit_mask_upto in Hb by lia; apply Z.leb_le in Hb; exact Hb|].
split; [intros i Hi Hb; rewrite Z.ldiff_spec, !testbit_mask_upto in Hb by lia; destruct (Z.leb_spec i last); [lia| discriminate]|].
split; [intros i Hi Ha Hb; rewrite Z.ldiff_spec, Ha in Hb; rewrite andb_false_r in Hb; discriminate|].
split; [intros i Hi; rewrite Z.ldiff_spec, !testbit_mask_upto by lia; destruct (Z.leb_spec i last); destruct (Z.leb_spec i ai); cbn; try reflexivity; lia|].
split; [intros i Hi; rewrite testbit_mask_upto by lia; apply Z.leb_le; lia| reflexivity].
Qed.
End CEIL_WRAP_1.
