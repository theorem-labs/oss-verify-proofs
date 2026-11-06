(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl MI_Kit.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_MI_Shadow () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Shadow.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.NArith.BinNat.N."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.fin_maps."; "stdpp.gmap."; "stdpp.numbers.Z."; "stdpp.option."], [["1None"; "1Some"; "1andb"; "1bool"; "1fst"; "1id"; "1list"; "1nil"; "1option"; "1orb"; "1pair"; "1prod"; "1snd"; "2and"; "2eq"; "2ex"]; ["2not"; "3N"; "3Z"; "4hl_ticks"; "5Unknown"; "5cell_read"; "5cellval"; "5get_shadow"; "5hav_add"; "5havoc"; "5havoc_units"; "5hdr_havoc"; "5mkShadow"; "5r_cells"; "5r_hav"; "5r_havp"]; ["5s_tick"; "5shadow"; "5stale"; "6le"; "6lt"; "6ltb"; "7add"; "7div"; "7le"; "7lt"; "7ltb"; "7modulo"; "7mul"; "0a"; "0b"; "0bp"]; ["0cov"; "0fp"; "0h"; "0hl"; "0lp"; "0n"; "0o"; "0p"; "0pg"; "0q"; "0rid"; "0sh"; "0st"; "8insert"; "8lookup"; "9Z_countable"]; [":map_insert"; ";gmap"; ";gmap_lookup"; ";gmap_partial_alter"; "<eq_dec"; "=from_option"; "0t"; "0tk"; "0u"; "0v"; "0x"; "0y"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition hl_ticks (hl : list (Z * N)) (t : N) : Prop := forall ch, In ch hl -> (snd ch <= t)%N.
Lemma stale_hav_add_some : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Shadow "Q5'B'A'6';%1243%311&Cr3r4%3221'>'3&Q2&Hr6r5%33218(1r2%22B1%834=1&9&2&Q:%12A:&Q5%128;%5231%@3DE9%8221%D3C:1p0F1pT@O1pRNQ11pS8M1pT>Q21pS2Q41").
Proof. intros cov t hl b tk.
intros Ht. unfold hav_add, stale. cbn [existsb fst snd].
destruct ((b <? cov) && (tk <? t)%N) eqn:E; cbn [orb]; [reflexivity|].
induction hl as [|[c h] hl IH]; [reflexivity|].
assert (Hh : (h <= t)%N) by (apply (Ht (c, h)); left; reflexivity).
assert (IH' : existsb (fun ch : Z * N => (b <? fst ch) && (tk <? snd ch)%N) (filter (fun ch : Z * N => cov <? fst ch) hl)
= existsb (fun ch : Z * N => (b <? fst ch) && (tk <? snd ch)%N) hl).
{ apply IH. intros ch Hin. apply Ht. right. exact Hin. }
rewrite filter_cons. cbn [existsb fst snd]. destruct (decide _) as [D|D]; cbn [existsb fst snd].
- rewrite IH'. reflexivity.
- rewrite IH'. destruct ((b <? c) && (tk <? h)%N) eqn:E2; cbn; [|reflexivity].
exfalso. apply Bool.andb_true_iff in E2 as [E2 E3]. apply Z.ltb_lt in E2. apply N.ltb_lt in E3.
assert (Hc : ~ cov < c) by (intros X; apply D; apply Is_true_true_2; apply Z.ltb_lt; exact X).
apply Bool.andb_false_iff in E as [E|E]; [apply Z.ltb_ge in E; lia| apply N.ltb_ge in E; lia].
Qed.
Lemma stale_hav_add_none : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Shadow "L'B'A'6';%1243%311'>'3&Q2&Hr4r3r2%43321r1(0%11?%93431&9&Q:%126:%=3975%4221%A3@61pRNH1pS8D1pT>I1pS2K1").
Proof. intros cov t hl b.
unfold hav_add, stale. cbn [existsb fst snd]. rewrite Bool.andb_true_r.
destruct (b <? cov) eqn:E; cbn [orb]; [reflexivity|].
induction hl as [|[c h] hl IH]; [reflexivity|].
rewrite filter_cons. cbn [existsb fst snd]. destruct (decide _) as [D|D]; cbn [existsb fst snd]; rewrite ?Bool.andb_true_r.
- rewrite IH. reflexivity.
- rewrite IH. destruct (Z.ltb_spec b c); cbn; [|reflexivity]. exfalso.
assert (Hc : ~ cov < c) by (intros X; apply D; apply Is_true_true_2; apply Z.ltb_lt; exact X).
apply Z.ltb_ge in E. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_havoc_units_lookup := (forall x y t h u, let u0 := x / 16 in let u1 := (y - 1) / 16 in
let lastcov := (if y mod 16 =? 0 then 16 else y mod 16) in
(havoc_units x y t h) !! u =
if (u0 <=? u) && (u <=? u1) then Some (hav_add (if u =? u1 then lastcov else 16) t (default [] (h !! u))) else h !! u) (only parsing).
Variable x : ltac:(sec_ty2 constr:(SEC_T_havoc_units_lookup) 0%nat 0%nat).
Variable y : ltac:(sec_ty2 constr:(SEC_T_havoc_units_lookup) 1%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_havoc_units_lookup) 2%nat 0%nat).
Variable h : ltac:(sec_ty2 constr:(SEC_T_havoc_units_lookup) 3%nat 0%nat).
Variable u : ltac:(sec_ty2 constr:(SEC_T_havoc_units_lookup) 4%nat 0%nat).
Lemma havoc_units_lookup : ltac:(sec_stmt2 constr:(SEC_T_havoc_units_lookup) 5%nat 0%nat).
Proof.
cbn zeta. unfold havoc_units.
set (u0 := x / 16). set (u1 := (y - 1) / 16). set (lastcov := if y mod 16 =? 0 then 16 else y mod 16).
set (F := fun acc : Z * gmap Z (list (Z * N)) => let (u2, h0) := acc in (u2 + 1, <[u2 := hav_add (if u2 =? u1 then lastcov else 16) t (default [] (h0 !! u2))]> h0)).
destruct (Z.lt_ge_cases (u1 - u0 + 1) 0) as [Hneg|Hnn].
-
destruct (u1 - u0 + 1) eqn:E; try lia. cbn.
destruct (Z.leb_spec u0 u), (Z.leb_spec u u1); cbn; try reflexivity. lia.
- assert (GEN : forall n, 0 <= n -> let r := Z.iter n F (u0, h) in fst r = u0 + n /\
forall v, snd r !! v = if (u0 <=? v) && (v <? u0 + n) then Some (hav_add (if v =? u1 then lastcov else 16) t (default [] (h !! v))) else h !! v).
{ intros n Hn. apply (Z_iter_ind F (fun n r => fst r = u0 + n /\ forall v, snd r !! v = if (u0 <=? v) && (v <? u0 + n) then Some (hav_add (if v =? u1 then lastcov else 16) t (default [] (h !! v))) else h !! v)); [| | exact Hn].
- cbn. split; [lia|]. intros v. destruct (Z.leb_spec u0 v), (Z.ltb_spec v (u0 + 0)); cbn; try reflexivity. lia.
- intros k [i tb] Hk [Hi IH]. cbn in Hi. subst i. unfold F. cbn [fst snd]. split; [lia|]. intros v.
destruct (Z.eq_dec v (u0 + k)) as [->|NE].
+ rewrite lookup_insert_eq. destruct (Z.leb_spec u0 (u0 + k)), (Z.ltb_spec (u0 + k) (u0 + (k + 1))); cbn; try lia.
f_equal. f_equal. rewrite IH. destruct (Z.leb_spec u0 (u0 + k)), (Z.ltb_spec (u0 + k) (u0 + k)); cbn; try lia. reflexivity.
+ rewrite lookup_insert_ne by congruence. rewrite IH.
destruct (Z.leb_spec u0 v), (Z.ltb_spec v (u0 + k)), (Z.ltb_spec v (u0 + (k + 1))); cbn; try reflexivity; lia. }
destruct (GEN (u1 - u0 + 1) Hnn) as [_ G]. rewrite G.
destruct (Z.leb_spec u0 u), (Z.ltb_spec u (u0 + (u1 - u0 + 1))), (Z.leb_spec u u1); cbn; try reflexivity; lia.
Qed.
End SE.
Lemma havoc_pages_lookup p0 p1 t h pg :
(havoc_pages p0 p1 t h) !! pg = if (p0 <=? pg) && (pg <? p1) then Some t else h !! pg.
Proof.
unfold havoc_pages.
set (F := fun acc : Z * gmap Z N => let (pg0, h0) := acc in (pg0 + 1, <[pg0 := t]> h0)).
destruct (Z.lt_ge_cases (p1 - p0) 0) as [Hneg|Hnn].
- destruct (p1 - p0) eqn:E; try lia. cbn. destruct (Z.leb_spec p0 pg), (Z.ltb_spec pg p1); cbn; try reflexivity. lia.
- assert (GEN : forall n, 0 <= n -> let r := Z.iter n F (p0, h) in fst r = p0 + n /\
forall v, snd r !! v = if (p0 <=? v) && (v <? p0 + n) then Some t else h !! v).
{ intros n Hn. apply (Z_iter_ind F (fun n r => fst r = p0 + n /\ forall v, snd r !! v = if (p0 <=? v) && (v <? p0 + n) then Some t else h !! v)); [| | exact Hn].
- cbn. split; [lia|]. intros v. destruct (Z.leb_spec p0 v), (Z.ltb_spec v (p0 + 0)); cbn; try reflexivity. lia.
- intros k [i tb] Hk [Hi IH]. cbn in Hi. subst i. unfold F. cbn [fst snd]. split; [lia|]. intros v.
destruct (Z.eq_dec v (p0 + k)) as [->|NE].
+ rewrite lookup_insert_eq. destruct (Z.leb_spec p0 (p0 + k)), (Z.ltb_spec (p0 + k) (p0 + (k + 1))); cbn; try lia. reflexivity.
+ rewrite lookup_insert_ne by congruence. rewrite IH.
destruct (Z.leb_spec p0 v), (Z.ltb_spec v (p0 + k)), (Z.ltb_spec v (p0 + (k + 1))); cbn; try reflexivity; lia. }
destruct (GEN (p1 - p0) Hnn) as [_ G]. rewrite G.
destruct (Z.leb_spec p0 pg), (Z.ltb_spec pg (p0 + (p1 - p0))), (Z.ltb_spec pg p1); cbn; try reflexivity; lia.
Qed.
Lemma div16_mono : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Shadow ">'B&Q8r2r1%3221&Q7r3+@%3221%4272%9221p071pRN<1pRL=1").
Proof. intros a b. intros. apply Z.div_le_mono; lia. Qed.
Lemma havoc_units_in x y t h o tko :
x mod 16 = 0 -> x <= o < y ->
match tko with Some tk => (tk < t)%N | None => True end ->
stale (default [] (havoc_units x y t h !! (o / 16))) (o mod 16) tko = true.
Proof.
intros Hx Ho Htk. rewrite havoc_units_lookup.
assert (U0 : x / 16 <= o / 16) by (apply div16_mono; lia).
assert (U1 : o / 16 <= (y - 1) / 16) by (apply div16_mono; lia).
destruct (Z.leb_spec (x / 16) (o / 16)), (Z.leb_spec (o / 16) ((y - 1) / 16)); try lia. cbn [andb default].
cbn [default id]. unfold hav_add, stale. cbn [existsb fst snd].
match goal with |- (?a && ?b) || _ = true => enough (E : a && b = true) by (rewrite E; reflexivity) end.
apply Bool.andb_true_iff. split.
- apply Z.ltb_lt. destruct (Z.eqb_spec (o / 16) ((y - 1) / 16)) as [E|NE].
+ destruct (Z.eqb_spec (y mod 16) 0) as [Ey|Ny].
* pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
*
pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (y - 1) 16 ltac:(lia)).
pose proof (Z.div_mod y 16 ltac:(lia)).
pose proof (Z.mod_pos_bound o 16 ltac:(lia)). pose proof (Z.mod_pos_bound (y - 1) 16 ltac:(lia)). pose proof (Z.mod_pos_bound y 16 ltac:(lia)).
assert (y / 16 = (y - 1) / 16 \/ y / 16 = (y - 1) / 16 + 1) by (pose proof (div16_mono (y - 1) y ltac:(lia)); pose proof (div16_mono y (y - 1 + 16) ltac:(lia)); rewrite <- Z.div_add in * by lia; nia).
lia.
+ pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
- destruct tko as [tk|]; [apply N.ltb_lt; exact Htk| reflexivity].
Qed.
Lemma havoc_units_out x y t h o tko :
x mod 16 = 0 -> ~ (x <= o < y) ->
match tko with Some tk => hl_ticks (default [] (h !! (o / 16))) t | None => True end ->
stale (default [] (havoc_units x y t h !! (o / 16))) (o mod 16) tko = stale (default [] (h !! (o / 16))) (o mod 16) tko.
Proof.
intros Hx Ho Htk. rewrite havoc_units_lookup.
destruct (Z.leb_spec (x / 16) (o / 16)), (Z.leb_spec (o / 16) ((y - 1) / 16)); cbn [andb]; try reflexivity.
cbn [default id].
assert (Hoy : y <= o).
{ destruct (Z.lt_ge_cases o x); [|lia]. exfalso.
pose proof (Z.div_mod x 16 ltac:(lia)). pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.mod_pos_bound o 16 ltac:(lia)). nia. }
assert (E : o / 16 = (y - 1) / 16) by (pose proof (div16_mono (y - 1) o ltac:(lia)); lia).
rewrite E, Z.eqb_refl.
pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (y - 1) 16 ltac:(lia)). pose proof (Z.div_mod y 16 ltac:(lia)).
pose proof (Z.mod_pos_bound o 16 ltac:(lia)). pose proof (Z.mod_pos_bound (y - 1) 16 ltac:(lia)). pose proof (Z.mod_pos_bound y 16 ltac:(lia)).
assert (Ny : y mod 16 <> 0 /\ y mod 16 <= o mod 16) by nia.
destruct (Z.eqb_spec (y mod 16) 0) as [|_]; [lia|].
destruct tko as [tk|].
- rewrite stale_hav_add_some by (rewrite <- E; exact Htk). destruct (Z.ltb_spec (o mod 16) (y mod 16)); [lia|]. reflexivity.
- rewrite stale_hav_add_none. destruct (Z.ltb_spec (o mod 16) (y mod 16)); [lia|]. reflexivity.
Qed.
Lemma hav_add_ticks : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Shadow "C'B'A'6';%1243%311&Cr1r2%3221&Hr4r3%33215%8212p061pS8;1pT>@1pS2B1").
Proof. intros cov t hl.
intros H ch Hin. unfold hav_add in Hin. destruct Hin as [<-|Hin]; [cbn; lia|].
apply H. apply list_elem_of_In. apply list_elem_of_In in Hin. apply list_elem_of_filter in Hin. tauto.
Qed.
Lemma havoc_units_ticks : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Shadow "Q='B'A'R1&R4&QO'6';%1276%311%749651'>'8%114&QN&R2%14?<;7r2r3%56B:9321(1r1%22=1%<3:41&Cr5%2291p041pS8C1pTBL1&Jr7r6r4%443291%E6Q2JICB1%I3G1>%=2D5p021pS8N1pTBQ71p0<1pS6Q01pT>Q91pTHQ;1pTFQ<1").
Proof. intros x y t h.
intros Hh u hl. rewrite havoc_units_lookup. destruct (_ && _).
- intros E. inversion E. subst. apply hav_add_ticks. destruct (h !! u) as [hl0|] eqn:E0; cbn; [eapply Hh; exact E0| intros ? []].
- apply Hh.
Qed.
Lemma havoc_units_default_ticks : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Shadow "Q?'B'A'R1&R4&QO'6';%1276%311%749651'>'8%114&QN&R2%14?<;7r2r4%56B:9321(1r1%22=1%<3:41&Cr6%2291p041pS8C1pTBL1&R5&5%11G(7%11J&Jr5r3%34=2D1%I6Q6NMGF1%:5OO861%A21Gp0=1pS>Q:1pS6Q21pT>Q;1pTHQ=1pTFQ>1").
Proof. intros x y t h o.
intros Hh. destruct (havoc_units x y t h !! o) as [hl|] eqn:E; cbn; [eapply havoc_units_ticks; eauto| intros ? []].
Qed.
Lemma default_ticks : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Shadow "Q:'R1'B&R4&QO'6';'A%2261%411%948761'>'8%114&QN&R2%14>=<7r2r5%56A:9321(1r1%22=1%<3:41&C%1287p031pS8B1pTBJ1&R5&5%11F(7%11Ir4%E6Q1JICB1%75KK531r3%>221p0;1pS>Q61pT>Q21pS6Q01").
Proof. intros h t o. intros Hh. destruct (h !! o) as [hl|] eqn:E; cbn; [eapply Hh; eauto| intros ? []]. Qed.
Section HAVOC.
Variables (p : aptr) (n : Z) (st : mstate).
Hypothesis Al : snd p mod 16 = 0.
Hypothesis Hn : 0 < n.
Let sh := get_shadow st (fst p).
Hypothesis TK : forall u hl, r_hav sh !! u = Some hl -> hl_ticks hl (s_tick st).
Let a := snd p.
Let b := snd p + n.
Let t := s_tick st.
Let fp := (a + 4095) / 4096.
Let lp := b / 4096.
Lemma havoc_shadow :
get_shadow (havoc p n st) (fst p) =
mkShadow (r_cells sh)
(if fp <? lp then
(if lp * 4096 <? b then havoc_units (lp * 4096) b t (if a <? fp * 4096 then havoc_units a (fp * 4096) t (r_hav sh) else r_hav sh)
else (if a <? fp * 4096 then havoc_units a (fp * 4096) t (r_hav sh) else r_hav sh))
else havoc_units a b t (r_hav sh))
(if fp <? lp then havoc_pages fp lp t (r_havp sh) else r_havp sh).
Proof.
unfold havoc. destruct (Z.leb_spec n 0); [lia|]. rewrite get_shadow_upd_shadow, N.eqb_refl.
subst sh a b t fp lp. destruct (_ <? _); [|reflexivity]. destruct (_ <? _); destruct (_ <? _); reflexivity.
Qed.
Lemma havoc_other_region : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Shadow "F'A&@'>r1&4'BvQG%33721%63851%811'Q1&G&IvQEvQL%33921r2%6221%7242%A3921p0;1pSFE1").
Proof. intros rid.
intros NE. unfold havoc. destruct (n <=? 0); [reflexivity|]. rewrite get_shadow_upd_shadow.
destruct (N.eqb_spec rid (fst p)); [congruence| reflexivity].
Qed.
Lemma fp_ge : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Shadow "7&Q8vQ=&Q<vQA+TP0%3221%6251").
Proof. subst fp. pose proof (Z.div_mod (a + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (a + 4095) 4096 ltac:(lia)). lia. Qed.
Lemma lp_le : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Shadow "7&Q8&Q<vQD+TP0%3221vQ>%6221").
Proof. subst lp. pose proof (Z.div_mod b 4096 ltac:(lia)). pose proof (Z.mod_pos_bound b 4096 ltac:(lia)). lia. Qed.
Lemma fp_al : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Shadow ";'>'B&Q;&Q<vQA+TP0%3221+@%6221z%:3921").
Proof. rewrite Z.mul_comm. replace 4096 with (16 * 256) by reflexivity. rewrite <- Z.mul_assoc, Z.mul_comm. apply Z_mod_mult. Qed.
Lemma lp_al : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Shadow ";'>'B&Q;&Q<vQD+TP0%3221+@%6221z%:3921").
Proof. rewrite Z.mul_comm. replace 4096 with (16 * 256) by reflexivity. rewrite <- Z.mul_assoc, Z.mul_comm. apply Z_mod_mult. Qed.
Lemma havoc_stale_out o tko :
~ (a <= o < b) ->
match tko with Some tk => True | None => True end ->
let sh' := get_shadow (havoc p n st) (fst p) in
stale_pg (r_havp sh' !! (o / 4096)) tko || stale (default [] (r_hav sh' !! (o / 16))) (o mod 16) tko
= stale_pg (r_havp sh !! (o / 4096)) tko || stale (default [] (r_hav sh !! (o / 16))) (o mod 16) tko.
Proof.
intros Ho _. rewrite havoc_shadow. cbn [r_hav r_havp].
pose proof fp_ge. pose proof lp_le.
assert (TKo : forall hh : gmap Z (list (Z * N)), (forall u hl, hh !! u = Some hl -> hl_ticks hl t) ->
match tko with Some _ => hl_ticks (default [] (hh !! (o / 16))) t | None => True end).
{ intros hh Hh. destruct tko; [apply default_ticks; exact Hh| exact I]. }
destruct (Z.ltb_spec fp lp).
- f_equal.
+ rewrite havoc_pages_lookup. destruct (Z.leb_spec fp (o / 4096)), (Z.ltb_spec (o / 4096) lp); cbn [andb]; try reflexivity.
exfalso. apply Ho. pose proof (Z.div_mod o 4096 ltac:(lia)). pose proof (Z.mod_pos_bound o 4096 ltac:(lia)). nia.
+ destruct (Z.ltb_spec (lp * 4096) b); destruct (Z.ltb_spec a (fp * 4096)).
* rewrite havoc_units_out; [| apply lp_al| lia| apply TKo; apply havoc_units_ticks; exact TK].
rewrite havoc_units_out; [reflexivity| exact Al| lia| apply TKo; exact TK].
* rewrite havoc_units_out; [reflexivity| apply lp_al| lia| apply TKo; exact TK].
* rewrite havoc_units_out; [reflexivity| exact Al| lia| apply TKo; exact TK].
* reflexivity.
- f_equal. rewrite havoc_units_out; [reflexivity| exact Al| lia| apply TKo; exact TK].
Qed.
Lemma havoc_stale_in o tko :
a <= o < b ->
match tko with Some tk => (tk < t)%N | None => True end ->
let sh' := get_shadow (havoc p n st) (fst p) in
stale_pg (r_havp sh' !! (o / 4096)) tko || stale (default [] (r_hav sh' !! (o / 16))) (o mod 16) tko = true.
Proof.
intros Ho Htk. rewrite havoc_shadow. cbn [r_hav r_havp].
pose proof fp_ge. pose proof lp_le.
assert (TKo : forall hh : gmap Z (list (Z * N)), (forall u hl, hh !! u = Some hl -> hl_ticks hl t) ->
match tko with Some _ => hl_ticks (default [] (hh !! (o / 16))) t | None => True end).
{ intros hh Hh. destruct tko; [apply default_ticks; exact Hh| exact I]. }
apply Bool.orb_true_iff.
destruct (Z.ltb_spec fp lp).
- destruct (Z.lt_ge_cases o (fp * 4096)) as [Hhead|Hnh].
+ right. destruct (Z.ltb_spec a (fp * 4096)); [|lia].
destruct (Z.ltb_spec (lp * 4096) b).
* rewrite havoc_units_out; [| apply lp_al| nia| apply TKo; apply havoc_units_ticks; exact TK].
apply havoc_units_in; [exact Al| lia| exact Htk].
* apply havoc_units_in; [exact Al| lia| exact Htk].
+ destruct (Z.lt_ge_cases o (lp * 4096)) as [Hmid|Htail].
* left. rewrite havoc_pages_lookup.
assert (fp <= o / 4096 < lp).
{ split; [apply Z.div_le_lower_bound; lia| apply Z.div_lt_upper_bound; lia]. }
destruct (Z.leb_spec fp (o / 4096)), (Z.ltb_spec (o / 4096) lp); try lia. cbn [andb].
destruct tko as [tk|]; cbn; [apply N.ltb_lt; exact Htk| reflexivity].
* right. destruct (Z.ltb_spec (lp * 4096) b); [|lia].
apply havoc_units_in; [apply lp_al| lia| exact Htk].
- right. apply havoc_units_in; [exact Al| lia| exact Htk].
Qed.
Lemma cell_read_havoc_out : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Shadow "Q9';'A'B%3221&@'='>&4r1%23871vQG%43:91%63;31&Q8vQ=&<%13?>8%4231&Q9vQ>%2241%@241%A2:1%C11'F&E&G&IvQEvQL%33D21r2%I3ON1%7231%C3Q1Q03%:221%:274%<213%Q03>31p0@1pSDQ51").
Proof. intros q.
intros Hq. destruct (N.eq_dec (fst q) (fst p)) as [E|NE].
- rewrite E. assert (Ho : ~ (a <= snd q < b)) by tauto.
unfold cell_read. pose proof (havoc_stale_out (snd q)) as SO. cbn zeta in SO.
replace (r_cells (get_shadow (havoc p n st) (fst p))) with (r_cells sh) by (rewrite havoc_shadow; reflexivity).
subst sh. destruct (r_cells (get_shadow st (fst p)) !! snd q) as [[v tk]|].
+ rewrite (SO (Some tk) Ho I). reflexivity.
+ rewrite (SO None Ho I). reflexivity.
- rewrite havoc_other_region by exact NE. reflexivity.
Qed.
Lemma cell_read_havoc_in : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Shadow "R5';'A'B%3221'>&4r1%23651vQG%43871%63931'=&Q8vQ=&<r2%23?>1%5241&Q9vQ>%2241%:241'8%G2EF%211&QN'R1&R4&QO%34K216&R2%14M438r5%C3Q0O1&MvQK%211%<6Q3>8641(1(:%14Q6Q7IQ2%32B1%Q63B51&Q4vR6%22N1p041pT@Q>1pTDQ>1'?'F&E&G&IvQEvQL%33Q@21%QD3QHQGI%6221%821J(D%11QG%QJ3<31qS6QM1%?2QN1p0A1p0Q=1p0QI1pSDR11").
Proof. intros q.
intros E Ho Htk. rewrite E. unfold cell_read.
replace (r_cells (get_shadow (havoc p n st) (fst p))) with (r_cells sh) by (rewrite havoc_shadow; reflexivity).
pose proof (havoc_stale_in (snd q)) as SI. cbn zeta in SI.
destruct (r_cells sh !! snd q) as [[v tk]|] eqn:Ec.
- rewrite (SI (Some tk) Ho (Htk v tk eq_refl)). eauto.
- rewrite (SI None Ho I). eauto.
Qed.
Lemma havoc_cells : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Shadow "G'A'>'R1'B&R4&QO';%1247%645431&M&G&IvQGvQEvQL%43321r1%7221%911%9253%;11%D3=31pSFF1").
Proof. intros rid.
destruct (N.eq_dec rid (fst p)) as [->|NE]; [rewrite havoc_shadow; reflexivity| rewrite havoc_other_region by exact NE; reflexivity].
Qed.
Lemma havoc_ticks : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Shadow "R8'A'B'6';%1234%311'>'8%113&QN'R1&R4&QO%34<218&R2%14>43:r2&N&GvQLr3%3221%511%>6FB:871(1r1%22E1%E3C41&CvR6%22>1p041pS8K1pTBQ01%K1Q2%I4Q2HGQ3%F4Q3IHQ4&Or4%E2D1%311%Q06Q8Q965I1%B2Q:A%Q53921&Q3%12M@p031pT@Q?1pSBQ?1'=&IvQGvQE%3321Q2r5%Q5221%Q711%Q@6QHQDQ<Q:Q91%QD3QB1Q0p01MpS8QG1pTBQL1%I17%QF6QNQOLKQ?1%QJ3N1Fp01DpT@R21pSBR21%C271p0E1p0Q51pSFR71").
Proof. intros rid.
intros H1 H2. destruct (N.eq_dec rid (fst p)) as [->|NE]; [| rewrite havoc_other_region by exact NE; auto].
rewrite havoc_shadow. cbn [r_hav r_havp]. split.
- destruct (fp <? lp); [| apply havoc_units_ticks; exact TK].
destruct (lp * 4096 <? b); destruct (a <? fp * 4096); repeat apply havoc_units_ticks; exact TK.
- destruct (fp <? lp); [| exact H2]. intros pg tk. rewrite havoc_pages_lookup. destruct (_ && _); [| apply H2].
intros X. inversion X. lia.
Qed.
End HAVOC.
Section HDR.
Variables (bp : aptr) (st : mstate).
Hypothesis Al : snd bp mod 16 = 0.
Let sh := get_shadow st (fst bp).
Hypothesis TK : forall u hl, r_hav sh !! u = Some hl -> hl_ticks hl (s_tick st).
Lemma hdr_havoc_shadow : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Shadow "QH'>'Q1&G&KvQ?vQL%3221&4'A'B%33216%9251(L&MvQK%211&QM'6';%12:;%311'R1&R4&QO%34?214&R0&R3%14B547%34C841&Q7&<%13GFK+@%4221&H+<&Q0%11Q0&R5&5%11D(7%11G&QN&R2%14Q4GFI&N%11Q1%56Q7LH3?1%;5MM971%@3?=1%Q37Q:OKGB14&O%11Q7%Q:3Q731%QG3QFQ<1").
Proof. unfold hdr_havoc. rewrite get_shadow_upd_shadow, N.eqb_refl. reflexivity. Qed.
Lemma hdr_havoc_other_region : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Shadow "E'A&@'>r1&4'BvQ?%33721%63851%811'Q1&G&KvQL%2281r2%5221%6242%@3821p0:1pSFD1").
Proof. intros rid. intros NE. unfold hdr_havoc. rewrite get_shadow_upd_shadow. destruct (N.eqb_spec rid (fst bp)); [congruence| reflexivity]. Qed.
Section SE.
Local Abbreviation SEC_T_cell_read_hdr_havoc_out := (ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Shadow "Q:';'A'B%3221&@'='>&4r1%23871vQ?%43:91%63;31&Q8&<%13>=5%23?>8%4221&Q9&Q6+<%2261%4261%B261%C2<1%E11'F&E&G&KvQL%22E1r2%J3Q0O1%6231%E3Q2Q13%9221%9274%;213%Q13=31p0?1pSDQ61")) (only parsing).
Variable q : ltac:(sec_ty2 constr:(SEC_T_cell_read_hdr_havoc_out) 0%nat 0%nat).
Lemma cell_read_hdr_havoc_out : ltac:(sec_stmt2 constr:(SEC_T_cell_read_hdr_havoc_out) 1%nat 0%nat).
Proof.
intros Hq. destruct (N.eq_dec (fst q) (fst bp)) as [E|NE]; [| rewrite hdr_havoc_other_region by exact NE; reflexivity].
rewrite E. rewrite hdr_havoc_shadow. unfold cell_read. cbn [r_cells r_hav r_havp]. subst sh.
destruct (Z.eq_dec (snd q / 16) (snd bp / 16)) as [Eu|Nu].
- rewrite Eu, lookup_insert_eq. cbn [default id].
assert (Hb : 12 <= snd q mod 16).
{ pose proof (Z.div_mod (snd q) 16 ltac:(lia)). pose proof (Z.div_mod (snd bp) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (snd q) 16 ltac:(lia)).
assert (~ (snd bp <= snd q < snd bp + 12)) by tauto. nia. }
destruct (r_cells (get_shadow st (fst bp)) !! snd q) as [[v tk]|].
+ rewrite stale_hav_add_some by (apply default_ticks; exact TK). destruct (Z.ltb_spec (snd q mod 16) 12); [lia|]. cbn [andb orb]. rewrite <- Eu. reflexivity.
+ rewrite stale_hav_add_none. destruct (Z.ltb_spec (snd q mod 16) 12); [lia|]. cbn [orb]. rewrite <- Eu. reflexivity.
- rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
End SE.
Lemma cell_read_hdr_havoc_in : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Shadow "R7';'A'B%3221'>&4r1%23651vQ?%43871%63931'=&Q8&<%13=<6r2%33?>1%5231&Q9&Q6+<%2271%4261%<261'8%I2GH%211&QN'R1&R4&QO%34M216&R2%14O438r5%F3Q2Q11&MvQK%211%<6Q5>8641(1(:%14Q8Q9KQ4%32B1%Q83B51&Q4&Q0vQL%211%42Q21p061pT@QB1pTDQB1'?'F&E&G&K%12QB;%QF3QJQII%4221%621J(D%11QI%QL3:31qS6QO1%=2R01p0?1p0Q=1p0QK1pSDR31").
Proof. intros q.
intros E Ho Htk. rewrite E, hdr_havoc_shadow. unfold cell_read. cbn [r_cells r_hav r_havp]. subst sh.
assert (Eu : snd q / 16 = snd bp / 16).
{ pose proof (Z.div_mod (snd bp) 16 ltac:(lia)). symmetry. apply Z.div_unique with (r := snd q - snd bp); lia. }
rewrite Eu, lookup_insert_eq. cbn [default id].
assert (Hb : snd q mod 16 < 12).
{ pose proof (Z.div_mod (snd q) 16 ltac:(lia)). pose proof (Z.div_mod (snd bp) 16 ltac:(lia)). nia. }
destruct (r_cells (get_shadow st (fst bp)) !! snd q) as [[v tk]|] eqn:Ec.
- unfold hav_add, stale. cbn [existsb fst snd].
destruct (Z.ltb_spec (snd q mod 16) 12); [|lia]. rewrite (proj2 (N.ltb_lt _ _)) by (eapply Htk; reflexivity).
cbn [andb orb]. rewrite Bool.orb_true_r. eauto.
- rewrite stale_hav_add_none. destruct (Z.ltb_spec (snd q mod 16) 12); [|lia]. cbn [orb]. rewrite Bool.orb_true_r. eauto.
Qed.
Lemma hdr_havoc_cells : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Shadow "F'A'>'R1'B&R4&QO';%1247%645431&M&G&KvQ?vQL%3221r1%6221%811%8253%:11%C3<31pSFE1").
Proof. intros rid. destruct (N.eq_dec rid (fst bp)) as [->|NE]; [rewrite hdr_havoc_shadow; reflexivity| rewrite hdr_havoc_other_region by exact NE; reflexivity]. Qed.
Lemma hdr_havoc_ticks : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Shadow "QI'A'B'6';%1234%311'>'8%113&QN'R1&R4&QO%34<218&R2%14>43:r2&N&GvQLr3%3221%511%>6FB:871(1r1%22E1%E3C41&C&Q0%11;%32?1p051pS8L1pTBQ11'=&KvQ?%221Cr4%F221%H11%Q16Q9Q5MKJ1%Q53Q31Ap01=pS8Q81pTBQ=1%Q54Q>Q4Q3Q?&O%O2;Q1%211%Q12Q0Q3%411%Q?3631%C281p0E1pSFQH1").
Proof. intros rid.
intros H1. destruct (N.eq_dec rid (fst bp)) as [->|NE]; [| rewrite hdr_havoc_other_region by exact NE; auto].
rewrite hdr_havoc_shadow. cbn [r_hav r_havp]. split; [| reflexivity].
intros u hl. destruct (Z.eq_dec u (snd bp / 16)) as [->|Nu].
- rewrite lookup_insert_eq. intros X. inversion X. subst. apply hav_add_ticks. apply default_ticks. exact TK.
- rewrite lookup_insert_ne by congruence. apply H1.
Qed.
End HDR.
End CEIL_WRAP_1.
