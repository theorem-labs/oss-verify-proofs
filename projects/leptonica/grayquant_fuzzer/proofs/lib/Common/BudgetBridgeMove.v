(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Import Sys.SyscallTable.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import BudgetBridgeCore BudgetBridgeMm.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib Require TCodec.
Ltac2 tcn__Common_BudgetBridgeMove () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.BudgetBridgeMm."; "OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.BudgetBridgeMove."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0C"; "0C1"; "0C2"; "1app"; "1bool"; "1cons"; "1list"; "1nil"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2not"; "2or"; "3Z"]; ["4iv_subtract"; "4live_bytes"; "4maps_subtract"; "4maps_subtract_all"; "4region_free"; "4two_pow_64"; "0P"; "0P1"; "0P2"; "5move_charge_le_stmt"; "6all_zero"; "6disj_bnd"; "6nz"; "7In"; "8add"; "8le"]; ["8lt"; "0a"; "0b"; "0hi"; "0l"; "0l1"; "0l2"; "0lo"; "0n"; "0p"; "0s"; "9Z_to_bv"; "9bv"; "9bv_unsigned"; "0sz"; "0w"]; ["0z"]]).
Lemma u64 : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMove "D'?';&Ozr1%3221&Q0&E%2241%8241'<&Q=yR0&Q;r2%2231%5241%73A13p091pS2C1").
Proof.
intros z Hz. apply Z_to_bv_small. change (bv_modulus 64) with two_pow_64. exact Hz.
Qed.
Lemma wrange : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMove "?'Q<yR0%211';&Oz&Q=r1%2271%5241&Q0&E%2241%:241pS0<1").
Proof.
intro w. pose proof (bv_unsigned_in_range 64 w) as H.
change (bv_modulus 64) with two_pow_64 in H. exact H.
Qed.
Lemma word_of_unsigned : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMove ";'Q<yR0%211'<&Q;&Q=r1%2261%4271%63713pS081").
Proof. intros w. apply bv_eq. rewrite u64; [reflexivity | apply wrange]. Qed.
Lemma two_pow_64_val : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMove "5'<'?&E+`PPPPPPPPPPP0%43321").
Proof. reflexivity. Qed.
Definition nz (l : list (word * word)) : list (word * word) :=
List.filter (fun e => negb (Z.eqb (bv_unsigned (snd e)) 0)) l.
Lemma live_nz : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMove "A'6'9'Q<yR0%211%4211%611'<'?&A&Lr1%211%411%513%83721pR::1").
Proof.
induction l as [|[a s] l IH]; [reflexivity|].
unfold nz in *. cbn [List.filter snd].
destruct (bv_unsigned s =? 0) eqn:E; cbn [negb]; cbv iota; cbn [live_bytes]; rewrite IH;
[apply Z.eqb_eq in E; lia | reflexivity].
Qed.
Lemma nz_app : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMove "D'6'9'Q<yR0%211%4211%611'<&L&3r2r1%33721%511%614%714%73;21%:3;41pR><1pR<=1").
Proof. intros. unfold nz. apply filter_app. Qed.
Definition all_zero (l : list (word * word)) : Prop :=
forall a s, In (a, s) l -> bv_unsigned s = 0.
Lemma nz_all_zero : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMove "C'6'9'Q<yR0%211%4211%611&Jr1%211'<&Lr2%211(7%11:%63:31p081pR:<1").
Proof.
induction l as [|[a s] l IH]; intros H; [reflexivity|]. unfold nz in *. cbn [List.filter snd].
rewrite (H a s (or_introl eq_refl)). cbn [Z.eqb negb]. cbv iota.
apply IH. intros a' s' Hin. exact (H a' s' (or_intror Hin)).
Qed.
Lemma all_zero_app : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMove "C'6'9'Q<yR0%211%4211%611&Jr2%211&3r4r3%33821%711p061p071pR>;1pR<<1").
Proof. intros l1 l2 H1 H2 a s Hin. apply in_app_or in Hin as [H|H]; eauto. Qed.
Lemma iv_subtract_zero : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMove "F'Q<yR0%211'?'<&Q=r3%2261z%53621&J&@r5r4r2%443291%611p081pR8?1pR@@1pRNB1pR4C1").
Proof.
intros a sz lo hi H0 b s Hin. unfold iv_subtract in Hin. cbv zeta in Hin.
rewrite H0 in Hin. pose proof (wrange a).
destruct (bv_unsigned a <? lo) eqn:E1; destruct (hi <? bv_unsigned a + 0) eqn:E2;
cbn [app In] in Hin; repeat destruct Hin as [Hin|Hin]; try contradiction;
injection Hin as <- <-; rewrite u64; unfold two_pow_64 in *; lia.
Qed.
Lemma maps_subtract_zero : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMove "D'6'9'Q<yR0%211%4211%611'?&Jr3%211&Br4r2%33251%711p061pR8:1pR@;1pR:=1").
Proof.
induction l as [|[a s] l IH]; intros lo hi H; [intros ? ? []|].
cbn [maps_subtract]. apply all_zero_app.
- apply iv_subtract_zero. exact (H a s (or_introl eq_refl)).
- apply IH. intros a' s' Hin. exact (H a' s' (or_intror Hin)).
Qed.
Lemma msa_zero : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMove "B'6'9'Q<yR0%211%4211%611&Jr1%211&Cr2r3%3221%711p061pR::1p2;1").
Proof.
induction C as [|[c n] C IH]; intros l H; [exact H|].
cbn [maps_subtract_all]. apply IH. apply maps_subtract_zero. exact H.
Qed.
Lemma msa_cons : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMove "J'6'9'Q<yR0%211%4211%611'<&C(5r2r1%33721r3%6221&3(7%11<%93=81%;216%<297%63@21%?3@81pR:A1pRDC1p2C1").
Proof. intros C p l. change (p :: l) with ([p] ++ l). apply maps_subtract_all_app. Qed.
Lemma nz_cons_zero : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMove "L'Q<yR0%211'6'9%1233%311'<'?&Q=r2%22:1z%63521&L(5(8r4r3%34AA21%53?1:%711%81<%@3A21p0;1pR:C1pRFH1pR4I1").
Proof. intros a s l E. unfold nz. cbn [List.filter snd]. rewrite E. reflexivity. Qed.
Lemma nz_cons_nz : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMove "O'Q<yR0%211'6'9%1233%311&='<'?&Q=r2%22;1z%63521%811&L(5(8r4r3%34CC21%53A1;%711%81=%83D41%B3D31p0<1pR:F1pRFK1pR4L1").
Proof.
intros a s l E. unfold nz. cbn [List.filter snd].
destruct (bv_unsigned s =? 0) eqn:E'; [apply Z.eqb_eq in E'; contradiction | reflexivity].
Qed.
Lemma nz_msa : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMove "D'6'9'Q<yR0%211%4211%611'<&L&Cr1r2%3221%511%614%6214%811%:3;41pQ><1p2=1").
Proof.
intros C P. induction P as [|[a s] P IH]; [reflexivity|].
rewrite msa_cons, nz_app.
destruct (Z.eq_dec (bv_unsigned s) 0) as [E|E].
- rewrite (nz_cons_zero a s P E).
rewrite (nz_all_zero (maps_subtract_all [(a, s)] C)).
+ exact IH.
+ apply msa_zero. intros a' s' [H|[]]. injection H as <- <-. exact E.
- rewrite (nz_cons_nz a s P E), (msa_cons C (a, s) (nz P)), nz_app, <- IH. reflexivity.
Qed.
Lemma nz_msa_congr : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMove "J'6'9'Q<yR0%211%4211%611'<&Lr2%211r1%411%63731&Cr3r4%3221%:11%52:3%<11%>3?31p091pQBA1pQ@B1p2C1").
Proof. intros C P1 P2 H. rewrite (nz_msa C P1), (nz_msa C P2), H. reflexivity. Qed.
Lemma msa_cuts_app : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMove "E'6'9'Q<yR0%211%4211%611'<&Cr1&3r3r2%33821%6251%7264%8214%:3;31pR:<1p6=1p4>1").
Proof.
induction C1 as [|[c n] C1 IH]; intros C2 l; [reflexivity|].
cbn [app maps_subtract_all]. apply IH.
Qed.
Ltac b2p := repeat match goal with
| H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
| H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
| H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
| H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
end.
Ltac u64s := repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (u64 z) by (unfold two_pow_64 in *; lia)
end.
Ltac prune := try (exfalso; unfold two_pow_64 in *; lia).
Ltac crunch :=
repeat (first [ progress (cbn [maps_subtract_all maps_subtract app List.filter snd fst negb])
| progress (unfold iv_subtract; cbv zeta)
| progress u64s
| match goal with
| |- context [Z.min ?x ?y] =>
let E := fresh "E" in
destruct (Z.min_spec x y) as [[? E]|[? E]]; rewrite E; clear E; prune
end
| match goal with
| |- context [Z.max ?x ?y] =>
let E := fresh "E" in
destruct (Z.max_spec x y) as [[? E]|[? E]]; rewrite E; clear E; prune
end
| match goal with
| |- context [if (?x <? ?y) then _ else _] => destruct (x <? y) eqn:?; b2p; prune
end
| match goal with
| |- context [if negb (?x =? ?y) then _ else _] => destruct (x =? y) eqn:?; b2p; prune
end ]).
Ltac fin_lists :=
repeat (match goal with
| |- _ :: _ = _ :: _ => f_equal
| |- (_, _) = (_, _) => f_equal
end);
try reflexivity;
try (apply bv_eq; u64s; unfold two_pow_64 in *; lia).
Lemma claimB1 : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMove "QO'Q<yR0%211'?&Ozr2%3221r3%5213&Q0&E%2241&N&Q=r9%22?1r8%42A1%6231%@219'>r:%92F1%;218r6%F221r5%H215%8231'<'6'9%12OO%311&L&C(5(8r;%24Q6Q61B(7%119%63:31&@r7%24OM1E%;241%=11%54:KQ1N%?11%E3A31p0G1p0Q11p0Q:1p0Q>1p0QA1pR8QF1pR@QG1pRFQI1pR6QJ1pRNQK1pR4QL1").
Proof.
intros a sz b s lo hi H0 H1 H2 Ha Hd.
destruct (Z.eq_dec (bv_unsigned sz) 0) as [Z0|NZ].
{ rewrite !nz_all_zero; [reflexivity | apply iv_subtract_zero; exact Z0 |].
apply msa_zero. intros a' s' [H|[]]. injection H as <- <-. exact Z0. }
pose proof (wrange a). pose proof (wrange sz). pose proof (wrange b). pose proof (wrange s).
unfold nz, iv_subtract. cbv zeta.
crunch.
all: fin_lists.
Qed.
Definition disj_bnd (lo hi : Z) (P : list (word * word)) : Prop :=
forall (a sz : word), In (a, sz) P ->
bv_unsigned a + bv_unsigned sz <= two_pow_64
/\ (bv_unsigned a + bv_unsigned sz <= lo \/ hi <= bv_unsigned a).
Lemma claimB : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMove "QB'6'9'Q<yR0%211%4211%611'?&Ozr2%3221r3%5213&Q0&E%2241&Kr5r4r8%43321'<&L&Cr9&@r7r6%34921;%6251%811&B&Q=%12O>&N%32Q19%2231%63=41%@11%B3Q291p0D1p0J1p0N1p0Q11pR8Q61pR@Q71pRFQ;1pR6Q<1pQ>Q;1").
Proof.
induction P as [|[a sz] P IH]; intros b s lo hi H0 H1 H2 HP.
- rewrite maps_subtract_all_nil. reflexivity.
- rewrite msa_cons, nz_app. cbn [maps_subtract]. rewrite nz_app.
destruct (HP a sz (or_introl eq_refl)) as [Ha Hd].
f_equal; [apply claimB1; assumption |].
apply IH; try assumption. intros a' s' Hin. exact (HP a' s' (or_intror Hin)).
Qed.
Lemma disj_bnd_msa : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMove "G'6'9'Q<yR0%211%4211%611'?&Kr3r2r1%43321r4&Cr5%2261%93481p061pQ>=1pR8=1pR@>1p2@1").
Proof.
intros C lo hi P HP b s Hin.
destruct (maps_subtract_all_within C P b s (fun a sz H => proj1 (HP a sz H)) Hin)
as (a & sz & Hin0 & Hw1 & Hw2).
destruct (HP a sz Hin0) as [Ha Hd]. split; lia.
Qed.
Lemma star_lemma : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMove "Q:'6'9'Q<yR0%211%4211%611'?&Ozr2%3221r3%5213&Q0&E%2241&Kr5r4r6%43321'<&L&Cr7&Br8%2318:%5241%711%7264%911%;3K31p0=1p0C1p0G1p0J1pR8O1pR@Q01pQ>Q21p2Q31").
Proof.
induction C as [|[b s] C IH]; intros P lo hi H0 H1 H2 HP; [reflexivity|].
cbn [maps_subtract]. rewrite msa_cuts_app.
rewrite (IH (maps_subtract_all P (iv_subtract b s lo hi)) lo hi H0 H1 H2 (disj_bnd_msa _ _ _ _ HP)).
cbn [maps_subtract_all]. apply nz_msa_congr. apply claimB; assumption.
Qed.
Lemma within_subtract_nil : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMove "Q8'6'9'Q<yR0%211%4211%611'?&M(8r2r1%348821r5%63921';&O&Q=r3%22@1%4271&N%52C<%2241r4%9221%;261p0=1pRFH1pR6I1'<&B%138>F(7%11M%53M31p071pR8N1pR@O1pR:Q11").
Proof.
induction l as [|[b s] l IH]; intros lo hi H; [reflexivity|].
cbn [maps_subtract]. destruct (H b s (or_introl eq_refl)) as [H1 H2].
unfold iv_subtract. cbv zeta.
replace (bv_unsigned b <? lo) with false by (symmetry; apply Z.ltb_ge; lia).
replace (hi <? bv_unsigned b + bv_unsigned s) with false by (symmetry; apply Z.ltb_ge; lia).
cbn [app]. apply IH. intros b' s' Hin. exact (H b' s' (or_intror Hin)).
Qed.
Lemma filter_length_le' : forall {A} (f : A -> bool) l, (length (List.filter f l) <= length l)%nat.
Proof.
intros A f l. induction l as [|x l IH]; cbn [List.filter length]; [lia|].
destruct (f x); cbn [length]; lia.
Qed.
Lemma region_free_app_l' : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMove "J'6'9'Q<yR0%211%4211%611'<'4&D&3r4r3%33821r2r1%73321(:%;3:21%:3875%=3<13p031pRBB1pR@C1pR>B1pR<C1").
Proof.
induction l1 as [|[a s] l1 IH]; intros l2 lo n H; [exact H|].
cbn [app region_free] in H. apply andb_true_iff in H as [_ H]. exact (IH _ _ _ H).
Qed.
Lemma move_charge_le : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMove "1&I").
Proof.
intros m old old_n dst new_n Hb Halign Hnalign Hpos Hend Hfree.
assert (P1 : forall L P m', m_vmmaps (with_vm_backing L P m') = m_vmmaps m') by reflexivity.
assert (P2 : forall L P m', m_vm_lazy (with_vm_backing L P m') = L) by reflexivity.
assert (P3 : forall L P m', m_vm_materialized (with_vm_backing L P m') = P) by reflexivity.
assert (P4 : forall h m', m_vmmaps (with_vmmaps h m') = h) by reflexivity.
assert (P5 : forall h m', m_vm_lazy (with_vmmaps h m') = m_vm_lazy m') by reflexivity.
assert (P6 : forall h m', m_vm_materialized (with_vmmaps h m') = m_vm_materialized m') by reflexivity.
unfold vm_backing_used, mremap_move_charge, mremap_model_next, vm_resize_backing, mremap_maps_next.
cbv zeta.
rewrite !P1, !P2, !P3, !P4, !P5, !P6.
unfold vm_backed_maps. cbn [vm_maps vm_noaccess vm_limit].
set (KL := maps_subtract (m_vm_lazy m) (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n)) in *.
set (KP := List.filter (page_outside_range (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n))
(m_vm_materialized m)) in *.
set (R0 := map_remove (vm_maps (m_vmmaps m)) old) in *.
set (NA := vm_noaccess (m_vmmaps m)) in *.
pose proof (wrange dst) as Wd. pose proof (wrange new_n) as Wn.
assert (HR0b : forall a sz, In (a, sz) R0 -> bv_unsigned a + bv_unsigned sz <= two_pow_64).
{ intros a sz Hin. apply Hb. unfold R0, map_remove in Hin. apply filter_In in Hin. exact (proj1 Hin). }
assert (HR0f : region_free R0 dst new_n = true).
{ apply region_free_intro. intros a sz Hin. apply (region_free_In (vm_maps (m_vmmaps m)) dst new_n a sz).
- exact (region_free_app_l' _ _ _ _ Hfree).
- unfold R0, map_remove in Hin. apply filter_In in Hin. exact (proj1 Hin). }
assert (HP : disj_bnd (bv_unsigned dst) (bv_unsigned dst + bv_unsigned new_n) (maps_subtract_all R0 NA)).
{ apply disj_bnd_msa. intros a sz Hin. split; [exact (HR0b a sz Hin)|].
pose proof (region_free_In R0 dst new_n a sz HR0f Hin) as Hov. unfold iv_overlap in Hov.
apply andb_false_iff in Hov. destruct Hov as [Hov|Hov]; apply Z.ltb_ge in Hov; lia. }
assert (HS : live_bytes (maps_subtract_all (maps_subtract_all R0 NA)
(maps_subtract KL (bv_unsigned dst) (bv_unsigned dst + bv_unsigned new_n)))
= live_bytes (maps_subtract_all (maps_subtract_all R0 NA) KL)).
{ rewrite <- (live_nz (maps_subtract_all _ (maps_subtract KL _ _))),
<- (live_nz (maps_subtract_all _ KL)).
f_equal. apply star_lemma; [lia | lia | unfold two_pow_64 in *; lia | exact HP]. }
assert (HPd : forall (b s : word), In (b, s) (maps_subtract_all R0 NA) ->
(bv_unsigned b + bv_unsigned s <= bv_unsigned dst
\/ bv_unsigned dst + bv_unsigned new_n <= bv_unsigned b)).
{ intros b s Hin. exact (proj2 (HP b s Hin)). }
assert (Hmsa1 : forall l a n C, maps_subtract_all l ((a, n) :: C)
= maps_subtract_all (maps_subtract l (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) C)
by reflexivity.
unfold page_size.
change ((dst, new_n) :: R0) with ([(dst, new_n)] ++ R0).
rewrite maps_subtract_all_app.
destruct (mremap_source_lazy_b m old old_n) eqn:Hsrc.
- rewrite (lazy_interior_aligned dst new_n Halign Hnalign Hpos).
cbn [app].
rewrite maps_subtract_all_app, live_bytes_app.
rewrite !Hmsa1.
rewrite (within_subtract_nil (maps_subtract_all [(dst, new_n)] NA)).
2: { intros b s Hin.
destruct (maps_subtract_all_within NA [(dst, new_n)] b s) as (a0 & sz0 & [E|[]] & W1 & W2).
- intros a sz [E|[]]. injection E as <- <-. unfold two_pow_64 in *; lia.
- exact Hin.
- injection E as <- <-. lia. }
rewrite maps_subtract_all_nil. cbn [live_bytes].
rewrite (live_bytes_subtract_free (maps_subtract KL (bv_unsigned dst) (bv_unsigned dst + bv_unsigned new_n))
(maps_subtract_all R0 NA) (bv_unsigned dst) (bv_unsigned dst + bv_unsigned new_n) ltac:(lia) HPd).
rewrite HS.
rewrite length_app, length_map.
pose proof (filter_length_le' (page_outside_range (bv_unsigned dst) (bv_unsigned dst + bv_unsigned new_n)) KP).
lia.
- rewrite maps_subtract_all_app, live_bytes_app. rewrite HS.
pose proof (live_bytes_maps_subtract_all_le
(maps_subtract KL (bv_unsigned dst) (bv_unsigned dst + bv_unsigned new_n))
(maps_subtract_all [(dst, new_n)] NA)).
pose proof (live_bytes_maps_subtract_all_le NA [(dst, new_n)]). cbn [live_bytes] in *.
rewrite length_app. cbn [length].
pose proof (filter_length_le' (page_outside_range (bv_unsigned dst) (bv_unsigned dst + bv_unsigned new_n)) KP).
lia.
Qed.
