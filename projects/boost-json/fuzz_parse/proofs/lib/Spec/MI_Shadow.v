(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl MI_Kit.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01N37Corelib4Init9Datatypeshc4listhc4prod01Zhc3snd36Stdlib5Lists4Listkb2In46Stdlib6NArith6BinNat1Nm32lehc4Some79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~o75stalehc4andbhc4boolhc3orb37Corelib4Init5Logicu12eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec9MI_Shadow~~~~~~va8hl_tickso77hav_addm33ltb46Stdlib6ZArith6BinInt1Zhl63ltbhc4None25stdpp9countablehncbZ_countable35stdpp7numbers1Zhpc6eq_dec25stdpp4gmaphr74gmap25stdpp4basehsb6lookuphr7bgmap_lookuphc6optionhl63divhl63eqbhl63lebhl66modulohc2idhc3nilo7bhavoc_unitshl63sub25stdpp6optionij8bfrom_optiono7bhavoc_pageshl62lehc4trueu14Trueu13andm32lthl62ltu13noto7aget_shadowhc3fsto75havoco76shadowo77r_cellso79hdr_havoco79cell_reado77cellvalhl63add" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition hl_ticks : ltac2:(zQ "40!h9!j4!jb!k2>2hl@1$1@2$2$3$0>1t$0P") := ltac2:(zQ "70!h9!k2!jb!j4!k5!le!nb\2hl@1$3@2$2$1$0\1t$0>2ch@2$2$1$0>0@3$5@2$2$1$0^1^3@2$6@3$4$1$0^2^3").

Lemma stale_hav_add_some : ltac2:(zQ "e0!h9!k2!o0!s5!sd!t4!j4!tb!jb!v5!hjb!hk6!hl0!hme>3cov$1>1t$0>2hl@1$6@2$8$1$0>1b$1>2tk$0>0@2$a^3^4@3$9$5@3$3@3$b^6^5^4^3@2$2$0^2@2$7@2$4@2$d^3^6@2$c^2^5@3$3^4^3@2$2$0^2").
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

Lemma stale_hav_add_none : ltac2:(zQ "b0!h9!k2!hn5!s5!t4!j4!tb!jb!v5!hk6!hme>3cov$1>1t$0>2hl@1$5@2$7$1$0>1b$1@3$8$4@3$3@3$9^4^3^2^1@1$2$0@2$6@2$a^1^4@3$3^2^1@1$2$0").
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma havoc_units_lookup : ltac2:(zQ "h81!k2!h9!jb!j4!hod!hqd!t4!hs3!ht7!hu1!hv0!hv9!ig0!ig7!ige!o0!sd!ih8!ihd!v5!hk6!ii3!ij1!ik6&@6$8$0@1$3@2$2$0$1@4$7$0$5$4@1$3@2$2$0$1@4$9$0$5$4@1$3@2$2$0$1^4^5>1x$0>1y$0>1t$1>1h@4$7$0$5$4@1$3@2$2$0$1>1u$0=2u0$0@2$b^5+h0=2u1$0@2$b@2$h6^5+1+h0=7lastcov$0M6\0$6$0@2$c@2$e^6+h0Z+h0@2$e^6+h0@3$h3@1$a@1$3@2$2$0$1@6$8$0@1$3@2$2$0$1@4$7$0$5$4@1$3@2$2$0$1@4$9$0$5$4@1$3@2$2$0$1^4@4$h5^8^7^6^5M6\0$6@1$a@1$3@2$2$0$1@2$h0@2$d^3^4@2$d^4^2@2$f@1$3@2$2$0$1@3$h4M6\0$6$0@2$c^4^2^1+h0^6@5$h7@1$3@2$2$0$1@1$3@2$2$0$1@1$h1@1$3@2$2$0$1@1$h2@2$2$0$1~0~0").
Proof. intros x y t h u.
  cbn zeta. unfold havoc_units.
  set (u0 := x / 16). set (u1 := (y - 1) / 16). set (lastcov := if y mod 16 =? 0 then 16 else y mod 16).
  set (F := fun acc : Z * gmap Z (list (Z * N)) => let (u2, h0) := acc in (u2 + 1, <[u2 := hav_add (if u2 =? u1 then lastcov else 16) t (default [] (h0 !! u2))]> h0)).
  destruct (Z.lt_ge_cases (u1 - u0 + 1) 0) as [Hneg|Hnn].
  - (* [comment removed for export] *)
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

Lemma havoc_pages_lookup : ltac2:(zQ "f0!h9!k2!hod!hqd!hs3!t4!hv0!ht7!hu1!o0!sd!v5!il5!ig7!hme>2p0$1>2p1$1>1t$0>1h@4$4$1$3$2$0>2pg$1@3$b@1$6$0@6$7$1$0@4$4$1$3$2$0@4$8$1$3$2$0^1@4$c^5^4^3^2M5\0$5@1$6$0@2$a@2$d^5^1@2$e^1^4@2$9$0^3@6$7$1$0@4$4$1$3$2$0@4$8$1$3$2$0^1^2").
Proof. intros p0 p1 t h pg.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma div16_mono : ltac2:(zQ "30!k2!hv9!im3>1a$0>1b$0>0@2$2^2^1@2$2@2$1^3+h0@2$1^2+h0").
Proof. intros a b. intros. apply Z.div_le_mono; lia. Qed.

Lemma havoc_units_in : ltac2:(zQ "h90!k2!h9!jb!j4!hv0!hod!hqd!v5!ige!hs3!t4!ih8!ihd!im9!in0!in7!ii3!s5!ind!hv9!im3!io2!ht7!hu1!ik6>1x$0>1y$0>1t$1>1h@4$9$0$6$5@1$3@2$2$0$1>1o$0>3tko@1$4$1>0@3$7$0@2$8^6+h0Z>0@2$f@2$h4^7^3@2$h5^3^6>0M4\3tko@1$4$1P^3\2tk$1@2$h2^1^7$e@3$7$a@3$h1@5$h8@1$3@2$2$0$1@1$3@2$2$0$1@1$b@1$3@2$2$0$1@1$c@2$2$0$1@6$h6$0@1$3@2$2$0$1@4$9$0$6$5@1$3@2$2$0$1@4$h7$0$6$5@1$3@2$2$0$1@2$h3^5+h0@4$h0^9^8^7^6@2$8^5+h0^4$d").
Proof. intros x y t h o tko.
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
      * (* [comment removed for export] *)
        pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (y - 1) 16 ltac:(lia)).
        pose proof (Z.div_mod y 16 ltac:(lia)).
        pose proof (Z.mod_pos_bound o 16 ltac:(lia)). pose proof (Z.mod_pos_bound (y - 1) 16 ltac:(lia)). pose proof (Z.mod_pos_bound y 16 ltac:(lia)).
        assert (y / 16 = (y - 1) / 16 \/ y / 16 = (y - 1) / 16 + 1) by (pose proof (div16_mono (y - 1) y ltac:(lia)); pose proof (div16_mono y (y - 1 + 16) ltac:(lia)); rewrite <- Z.div_add in * by lia; nia).
        lia.
    + pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
  - destruct tko as [tk|]; [apply N.ltb_lt; exact Htk| reflexivity].
Qed.

Lemma havoc_units_out : ltac2:(zQ "h92!k2!h9!jb!j4!hod!hqd!hs3!ih8!ihd!hv0!hv9!ige!ht7!hu1!ik6!v5!s5!t4!in0!in7!io8!hjb!ii3!im3!io2&@6$c$0@1$3@2$2$0$1@4$6$0$5$4@1$3@2$2$0$1@4$d$0$5$4@1$3@2$2$0$1@2$a^5+h0^6&@5$e@1$3@2$2$0$1@1$3@2$2$0$1@1$7@1$3@2$2$0$1@1$8@2$2$0$1~0>1x$0>1y$0>1t$1>1h@4$6$0$5$4@1$3@2$2$0$1>1o$0>3tko@1$9$1>0@3$f$0@2$b^6+h0Z>0@1$h4@2$h3@2$h7^7^3@2$h8^3^6>0M9\3tko@1$9$1P^3\2tk$1@2$h5~1^7$h2@3$f$h1@3$h0@5$e@1$3@2$2$0$1@1$3@2$2$0$1@1$7@1$3@2$2$0$1@1$8@2$2$0$1@6$c$0@1$3@2$2$0$1@4$6$0$5$4@1$3@2$2$0$1@4$d$0$5$4@1$3@2$2$0$1@2$a^5+h0@4$h6^9^8^7^6@2$b^5+h0^4@3$h0~1@2$b^5+h0^4").
Proof. intros x y t h o tko.
  intros Hx Ho Htk. rewrite havoc_units_lookup.
  destruct (Z.leb_spec (x / 16) (o / 16)), (Z.leb_spec (o / 16) ((y - 1) / 16)); cbn [andb]; try reflexivity.
  cbn [default id].
  (* [comment removed for export] *)
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

Lemma hav_add_ticks : ltac2:(zQ "60!h9!k2!hjb!j4!jb!hk6>3cov$1>1t$0>2hl@1$3@2$4$1$0>0@2$2^1^2@2$2@3$5^4^3^2^3").
Proof. intros cov t hl.
  intros H ch Hin. unfold hav_add in Hin. destruct Hin as [<-|Hin]; [cbn; lia|].
  apply H. apply list_elem_of_In. apply list_elem_of_In in Hin. apply list_elem_of_filter in Hin. tauto.
Qed.

Lemma havoc_units_ticks : ltac2:(zQ "e0!k2!h9!j4!jb!hod!hqd!hs3!o0!hv0!v5!hjb!ht7!hu1!ii3>1x$0>1y$0>1t$1>1h@4$6$0$5$4@1$2@2$3$0$1>0>1u$0>2hl@1$2@2$3$0$1>0@3$9@1$8@1$2@2$3$0$1@6$b$0@1$2@2$3$0$1@4$6$0$5$4@1$2@2$3$0$1@4$c$0$5$4@1$2@2$3$0$1^2^3@2$7@1$2@2$3$0$1^1@2$a^2^5>1u$0>2hl@1$2@2$3$0$1>0@3$9@1$8@1$2@2$3$0$1@6$b$0@1$2@2$3$0$1@4$6$0$5$4@1$2@2$3$0$1@4$c$0$5$4@1$2@2$3$0$1^2@4$d^7^6^5^4@2$7@1$2@2$3$0$1^1@2$a^2^6").
Proof. intros x y t h.
  intros Hh u hl. rewrite havoc_units_lookup. destruct (_ && _).
  - intros E. inversion E. subst. apply hav_add_ticks. destruct (h !! u) as [hl0|] eqn:E0; cbn; [eapply Hh; exact E0| intros ? []].
  - apply Hh.
Qed.

Lemma default_ticks : ltac2:(zQ "h00!k2!h9!jb!j4!hod!hqd!hs3!hjb!ht7!hu1!o0!ih8!ihd!hv0!v5!ik6>1h@4$6$0$5$4@1$3@2$2$0$1>1t$1>1o$0>0>1u$0>2hl@1$3@2$2$0$1>0@3$e@1$d@1$3@2$2$0$1@6$8$0@1$3@2$2$0$1@4$6$0$5$4@1$3@2$2$0$1@4$9$0$5$4@1$3@2$2$0$1^2^5@2$a@1$3@2$2$0$1^1@2$7^2^5@2$7@5$f@1$3@2$2$0$1@1$3@2$2$0$1@1$b@1$3@2$2$0$1@1$c@2$2$0$1@6$8$0@1$3@2$2$0$1@4$6$0$5$4@1$3@2$2$0$1@4$9$0$5$4@1$3@2$2$0$1^2^4^3").
Proof. intros h t o. intros Hh. destruct (h !! o) as [hl|] eqn:E; cbn; [eapply Hh; eauto| intros ? []]. Qed.

Section HAVOC.
Variables (p : aptr) (n : Z) (st : mstate).
Hypothesis Al : ltac2:(zQ "50!k2!k5!v5!h9!ige@3$2$0@2$4@3$1$3$0?1p+h0Z").
Hypothesis Hn : ltac2:(zQ "10!io2@2$0Z?1n").
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

Lemma havoc_other_region : ltac2:(zQ "80!h9!v5!ioe!ipb!io8!k2!iq1!iq9>3rid$0>0@1$4@3$1$0^1@3$3$0$5?1p@3$1$7@2$2@3$6?1p?1n?2st^2@2$2?2st^2").
Proof. intros rid.
  intros NE. unfold havoc. destruct (n <=? 0); [reflexivity|]. rewrite get_shadow_upd_shadow.
  destruct (N.eqb_spec rid (fst p)); [congruence| reflexivity].
Qed.

Lemma fp_ge : a <= fp * 4096.
Proof. subst fp. pose proof (Z.div_mod (a + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (a + 4095) 4096 ltac:(lia)). lia. Qed.
Lemma lp_le : lp * 4096 <= b.
Proof. subst lp. pose proof (Z.div_mod b 4096 ltac:(lia)). pose proof (Z.mod_pos_bound b 4096 ltac:(lia)). lia. Qed.
Lemma lp_al : (lp * 4096) mod 16 = 0.
Proof. rewrite Z.mul_comm. replace 4096 with (16 * 256) by reflexivity. rewrite <- Z.mul_assoc, Z.mul_comm. apply Z_mod_mult. Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma cell_read_havoc_out q :
  ~ (fst q = fst p /\ a <= snd q < b) ->
  cell_read (get_shadow (havoc p n st) (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof.
  intros Hq. destruct (N.eq_dec (fst q) (fst p)) as [E|NE].
  - rewrite E. assert (Ho : ~ (a <= snd q < b)) by tauto.
    unfold cell_read. pose proof (havoc_stale_out (snd q)) as SO. cbn zeta in SO.
    replace (r_cells (get_shadow (havoc p n st) (fst p))) with (r_cells sh) by (rewrite havoc_shadow; reflexivity).
    subst sh. destruct (r_cells (get_shadow st (fst p)) !! snd q) as [[v tk]|].
    + rewrite (SO (Some tk) Ho I). reflexivity.
    + rewrite (SO None Ho I). reflexivity.
  - rewrite havoc_other_region by exact NE. reflexivity.
Qed.

Lemma cell_read_havoc_in q :
  fst q = fst p -> a <= snd q < b ->
  (forall v tk, r_cells sh !! snd q = Some (v, tk) -> (tk < t)%N) ->
  exists h, cell_read (get_shadow (havoc p n st) (fst q)) (snd q) = Unknown h.
Proof.
  intros E Ho Htk. rewrite E. unfold cell_read.
  replace (r_cells (get_shadow (havoc p n st) (fst p))) with (r_cells sh) by (rewrite havoc_shadow; reflexivity).
  pose proof (havoc_stale_in (snd q)) as SI. cbn zeta in SI.
  destruct (r_cells sh !! snd q) as [[v tk]|] eqn:Ec.
  - rewrite (SI (Some tk) Ho (Htk v tk eq_refl)). eauto.
  - rewrite (SI None Ho I). eauto.
Qed.

Lemma havoc_cells : ltac2:(zQ "a0!h9!k2!ioe!ir2!jb!v5!iq1!hod!hs3!hqd>3rid$0@3$5@4$8$1$9$7@2$4$1$0@1$3@2$2@3$6?1p?1n?2st^1@1$3@2$2?2st^1").
Proof. intros rid.
  destruct (N.eq_dec rid (fst p)) as [->|NE]; [rewrite havoc_shadow; reflexivity| rewrite havoc_other_region by exact NE; reflexivity].
Qed.

Lemma havoc_ticks rid :
  (forall u hl, r_hav (get_shadow st rid) !! u = Some hl -> hl_ticks hl t) ->
  (forall pg tk, r_havp (get_shadow st rid) !! pg = Some tk -> (tk <= t)%N) ->
  (forall u hl, r_hav (get_shadow (havoc p n st) rid) !! u = Some hl -> hl_ticks hl t)
  /\ (forall pg tk, r_havp (get_shadow (havoc p n st) rid) !! pg = Some tk -> (tk <= t)%N).
Proof.
  intros H1 H2. destruct (N.eq_dec rid (fst p)) as [->|NE]; [| rewrite havoc_other_region by exact NE; auto].
  rewrite havoc_shadow. cbn [r_hav r_havp]. split.
  - destruct (fp <? lp); [| apply havoc_units_ticks; exact TK].
    destruct (lp * 4096 <? b); destruct (a <? fp * 4096); repeat apply havoc_units_ticks; exact TK.
  - destruct (fp <? lp); [| exact H2]. intros pg tk. rewrite havoc_pages_lookup. destruct (_ && _); [| apply H2].
    intros X. inversion X. lia.
Qed.
End HAVOC.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section HDR.
Variables (bp : aptr) (st : mstate).
Hypothesis Al : ltac2:(zQ "50!k2!k5!v5!h9!ige@3$2$0@2$4@3$1$3$0?2bp+h0Z").
Let sh := get_shadow st (fst bp).
Hypothesis TK : forall u hl, r_hav sh !! u = Some hl -> hl_ticks hl (s_tick st).

Lemma hdr_havoc_shadow :
  get_shadow (hdr_havoc bp st) (fst bp) =
  mkShadow (r_cells sh) (<[snd bp / 16 := hav_add 12 (s_tick st) (default [] (r_hav sh !! (snd bp / 16)))]> (r_hav sh)) (r_havp sh).
Proof. unfold hdr_havoc. rewrite get_shadow_upd_shadow, N.eqb_refl. reflexivity. Qed.

Lemma hdr_havoc_other_region : ltac2:(zQ "80!h9!v5!ioe!ipb!io8!k2!irc!iq9>3rid$0>0@1$4@3$1$0^1@3$3$0$5?2bp@3$1$7@2$2@2$6?2bp?2st^2@2$2?2st^2").
Proof. intros rid. intros NE. unfold hdr_havoc. rewrite get_shadow_upd_shadow. destruct (N.eqb_spec rid (fst bp)); [congruence| reflexivity]. Qed.

Lemma cell_read_hdr_havoc_out : ltac2:(zQ "f0!h9!k2!k5!ipb!in7!v5!is8!ioe!jb!io8!it4!irc!ite!im3!io2>1q@2$8$0$1>0@1$9@2$4@3$5$0@3$3$0$1^1@3$3$0$1?2bp@2$4@2$d@3$2$0$1?2bp@3$2$0$1^1@2$e@3$2$0$1^1@2$c@3$2$0$1?2bp+c@3$5$a@2$6@2$7@2$b?2bp?2st@3$3$0$1^2@3$2$0$1^2@2$6@2$7?2st@3$3$0$1^2@3$2$0$1^2").
Proof. intros q.
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

Lemma cell_read_hdr_havoc_in q :
  fst q = fst bp -> snd bp <= snd q < snd bp + 12 ->
  (forall v tk, r_cells sh !! snd q = Some (v, tk) -> (tk < s_tick st)%N) ->
  exists h, cell_read (get_shadow (hdr_havoc bp st) (fst q)) (snd q) = Unknown h.
Proof.
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

End HDR.
(* [comment removed for export] *)
