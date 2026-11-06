(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "leb"; "add"; "mul"; "div"; "ltb"; "modulo"; "pow"; "to_nat"; "sub"; "eqb"; "land"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "andb"; "cons"; "true"; "list"; "nil"; "nat"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "class_size"; "znth"; "PGSZ"; "page_round"; "UNIT"; "IB"; "size_classes"; "initial_cnt"; "size_to_class"; "small_cnt_tab"; "NEST_FUEL"; "class_of_units"; "halve_while_big"; "halve_while_even"; "med_cnt_tab"; "mmap_plan"; "small_cnt"; "@Stdlib.Lists.List"; "forallb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "zseq"; "implb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith"; "need"; "htrail"; "icands"; "@Corelib.Init.Peano"; "le"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@Corelib.Init.Nat"; "add"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Infix "==>" := implb (at level 55, right associativity).

Lemma zseq_In lo n k : ltac2:(tb__ "0|0|
S0Z0Vn;A2SeS0Vlo;Vk;A2S1Vk;S3Vlo;Vn;A2A2A2S2bSdVk;S2cVlo;Vn;A2A3F_;F_;").
Proof.
  intros Hn Hk. unfold zseq. apply in_map_iff. exists (Z.to_nat (k - lo)). split; [lia|]. apply in_seq. lia.
Qed.

Tactic Notation "brute" constr(H) constr(k) "as" ident(T) :=
  pose proof H as T; rewrite forallb_forall in T; specialize (T k);
  match type of T with In _ (zseq ?lo ?n) -> _ =>
    specialize (T (zseq_In lo n k ltac:(lia) ltac:(lia))); cbn beta in T end.

Lemma class_size_mono_tab : ltac2:(tb__ "0|1|
SfS10S2aSdSdS2aSdSdS2dS2R2R1A2S2S1aR2S1fA2S1aR1S1fA2A2A2Lb;S2cZ0Z30A2M0A3La;G0A3S13A3").
Proof. vm_compute. reflexivity. Qed.

Lemma class_size_mono a b : ltac2:(tb__ "0|0|
S0Z0Va;A2S0Va;Vb;A2S1Vb;Z30A2S0S19Va;A1S19Vb;A1A2F_;F_;F_;").
Proof.
  intros Ha Hab Hb. brute class_size_mono_tab a as H. rewrite forallb_forall in H.
  specialize (H b (zseq_In 0 48 b ltac:(lia) ltac:(lia))). cbn beta in H.
  unfold implb in H. destruct (a <=? b) eqn:E; [|apply Z.leb_gt in E; lia]. cbn [negb orb] in H.
  apply Z.leb_le in H. unfold class_size, UNIT. lia.
Qed.

Lemma class_size_tab : ltac2:(tb__ "0|1|
SfS10S2aSdSdS11S11S2Z1S1aR1S1fA2M0A2S2G0Z1fffA2A2S2dS2G0Z7fA2S2R1Z17A2A2A2La;S2cZ0Z30A2A3S13A3").
Proof. vm_compute. reflexivity. Qed.

Lemma class_size_bounds sc : ltac2:(tb__ "0|1|
SeS0Z0Vsc;A2S1Vsc;Z30A2A2SeS0Z10S19Vsc;A1M0A2S0G0Z1fff0A2A2F_;").
Proof.
  intros H. brute class_size_tab sc as H0. apply andb_prop in H0 as [H0 _]. apply andb_prop in H0 as [A B].
  apply Z.leb_le in A. apply Z.leb_le in B. unfold class_size, UNIT. lia.
Qed.

Lemma class_le_23 sc : ltac2:(tb__ "0|0|
SeS0Z0Vsc;A2S1Vsc;Z30A2A2S0S19Vsc;A1Z7f0A2S0Vsc;Z17A2F_;F_;").
Proof.
  intros H Hs. brute class_size_tab sc as H0. apply andb_prop in H0 as [_ C]. unfold implb in C.
  destruct (znth sc size_classes <=? 127) eqn:E; cbn [negb orb] in C; [apply Z.leb_le in C; lia|].
  apply Z.leb_gt in E. unfold class_size, UNIT in Hs. lia.
Qed.

Lemma class_of_units_small_tab : ltac2:(tb__ "0|0|
SfS10S2aSdSdS2S24R1A1Z18A2Lk;S2cZ0Z80A2A3S13A3").
Proof. vm_compute. reflexivity. Qed.

Lemma size_to_class_small n : ltac2:(tb__ "0|0|
SeS0Z0Vn;A2S0Vn;Z7fcA2A2S0S21Vn;A1Z18A2F_;").
Proof.
  intros Hn. unfold size_to_class.
  set (k := Z.shiftr (n + IB - 1) 4).
  assert (Hk : 0 <= k < 128).
  { subst k. rewrite Z.shiftr_div_pow2 by lia. unfold IB.
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  brute class_of_units_small_tab k as H. apply Z.leb_le in H. exact H.
Qed.

Lemma page_round_ge x : x <= page_round x.
Proof. unfold page_round, PGSZ. pose proof (Z_div_mod_eq_full (x + 4096 - 1) 4096). pose proof (Z.mod_pos_bound (x + 4096 - 1) 4096 ltac:(lia)). lia. Qed.

Lemma page_round_lt x : ltac2:(tb__ "0|0|
S1S1cVx;A1S3Vx;S1bA2A2").
Proof. unfold page_round, PGSZ. pose proof (Z_div_mod_eq_full (x + 4096 - 1) 4096). pose proof (Z.mod_pos_bound (x + 4096 - 1) 4096 ltac:(lia)). lia. Qed.

Lemma page_round_mod x : ltac2:(tb__ "0|0|
SfSdS7S1cVx;A1S1bA2Z0A3").
Proof. unfold page_round. apply Z_mod_mult. Qed.

Lemma page_round_pages x : ltac2:(tb__ "0|1|
SfSdS1cVx;A1M0S4S5G0S1bA2S1bA2A3").
Proof. unfold page_round, PGSZ. rewrite Z_div_mult by lia. reflexivity. Qed.

Lemma page_round_mono x y : ltac2:(tb__ "0|0|
S0Vx;Vy;A2S0S1cVx;A1S1cVy;A1A2F_;").
Proof. intros H. unfold page_round, PGSZ. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia. Qed.

Lemma page_round_fixed x : ltac2:(tb__ "0|0|
SfSdS7Vx;S1bA2Z0A3SfSdS1cVx;A1Vx;A3F_;").
Proof.
  intros H. unfold page_round. unfold PGSZ in *.
  pose proof (Z_div_mod_eq_full x 4096). rewrite H in H0.
  replace (x + 4096 - 1) with (4096 * (x / 4096) + 4095) by lia.
  rewrite (Z.mul_comm 4096 (x / 4096)), Z.div_add_l by lia. replace (4095 / 4096) with 0 by reflexivity. lia.
Qed.

Fixpoint htrail (f : nat) (c : Z) : list Z :=
  c :: match f with O => [] | S f' => if Z.even c then htrail f' (c / 2) else [] end.

Lemma halve_while_even_In f c u : ltac2:(tb__ "0|0|
S2bSdS26Vf;Vc;Vu;A3S2fVf;Vc;A2A3").
Proof.
  revert c. induction f as [|f IH]; intros c; cbn [halve_while_even htrail]; [left; reflexivity|].
  destruct (Z.even c) eqn:E; cbn [andb].
  - destruct (u <? 4 * c); [right; apply IH | left; reflexivity].
  - left; reflexivity.
Qed.

Lemma small_cnt_In sc u : ltac2:(tb__ "0|2|
S2bSdS29Vsc;Vu;A2S33S14SdA1M0S9Vsc;A1S22S15SdA1M1A4G0S12SdS1aZ0R1A2S12SdS1aZ1R1A2S12SdS1aZ2R1A2G1A3A3A3Trow;A3").
Proof.
  unfold small_cnt. set (row := nth (Z.to_nat sc) small_cnt_tab []).
  destruct (negb (u <? 4 * znth 0 row)); [left; reflexivity|].
  destruct (negb (u <? 4 * znth 1 row)); [right; left; reflexivity|]. right; right; left; reflexivity.
Qed.

Definition icands (sc : Z) : list Z := ltac2:(tb__ "0|6|
S32SdSdSdS10SdL_;S11SbR1Z1M0A2S2S3S4S19Vsc;A1M1R1A2S1dA2S5S1bZ2M2A2A2A2G2R1X10x2Lcnt;S10S14SdA1M3L_;S6Vsc;Z9A2S33G3S9Vsc;A1S22S15SdA1M4A4G3S12SdS1aZ0R1A2S12SdS1aG0R1A2S12SdS1aG2R1A2G4A3A3A3Trow;S32SdSdSdS25U8M5R1G1A3Lc;S2fG5S1aScVsc;Z3A2S27A2A2A4X10x2A4").

Lemma initial_cnt_In sc u : ltac2:(tb__ "0|0|
S2bSdS20Vsc;Vu;A2S30Vsc;A1A3").
Proof.
  unfold initial_cnt, icands. apply in_map_iff. eexists. split; [reflexivity|].
  destruct (sc <? 9).
  - apply small_cnt_In.
  - apply in_map_iff. eexists. split; [reflexivity|]. apply halve_while_even_In.
Qed.

Lemma icands_tab : ltac2:(tb__ "0|1|
SfS10S2aSdSdS2aSdSdS11S11S11S2Z1R1A2S2R1Z20A2A2S6S4S19R2A1R1A2S8Z2M0Z14A2A2A2S2dS2R2Z1aA2S2G0R1A2A2A2Lcnt;S30R1A1A3Lsc;S2cZ0Z30A2A3S13A3").
Proof. vm_compute. reflexivity. Qed.

Lemma initial_cnt_facts sc u : ltac2:(tb__ "0|2|
SeS0Z0Vsc;A2S1Vsc;Z30A2A2SeSeS0Z1S20Vsc;Vu;A2M0A2S0G0Z20A2A2SeS1S4S19Vsc;A1G0A2S8Z2M1Z14A2A2S0Vsc;Z1aA2S0G1G0A2F_;A2A2F_;").
Proof.
  intros Hsc. brute icands_tab sc as H. rewrite forallb_forall in H. specialize (H _ (initial_cnt_In sc u)).
  apply andb_prop in H as [H D]. apply andb_prop in H as [H C]. apply andb_prop in H as [A B].
  apply Z.leb_le in A. apply Z.leb_le in B. apply Z.ltb_lt in C. unfold implb in D.
  split; [lia|]. split; [exact C|]. intros H26.
  destruct (sc <=? 26) eqn:E; [|apply Z.leb_gt in E; lia]. cbn [negb orb] in D. apply Z.leb_le in D. exact D.
Qed.

Lemma mmap_plan_facts s sc req cnt0 u cnt needed : ltac2:(tb__ "0|a|
SeS0Z0M0Vsc;A2S1Vsc;Z30A2A2SeS0Z1M1Vcnt0;A2S0Vcnt0;Z20M2A2A2S1S4S19Vsc;A1M3Vcnt0;A2S8Z2M4Z14A2M5A2S0G0Vreq;A2S0S3Vreq;S1eA2M6G3A2S0Vsc;Z1aA2M7S0G4Vcnt0;A2F_;SfS18SdSdA2S28Vs;Vsc;Vreq;Vcnt0;Vu;A5S17SdSdVcnt;Vneeded;A4A3SeSeS0G1Vcnt;A2S0Vcnt;G2A2A2SeS1S4G3Vcnt;A2M8G5A2SeG7S0G4Vcnt;A2M9F_;SeSfSdS7Vneeded;S1bA2G0A3SeS0S1bVneeded;A2SeS0Vneeded;G5A2SeG9S0S3S1dG8A2Vneeded;A2F_;SeS0S3G6S1dA2Vneeded;A2SfSdVcnt;G1A3S0Vneeded;S1cS3G3S1dA2A1A2F_;A2A2A2A2A2A2A2A2F_;F_;F_;F_;F_;F_;F_;").
Proof.
  intros Hsc Hc0 Hsz Hreq Hfit H26 Hp.
  pose proof (class_size_bounds sc Hsc) as [S16 Smax].
  assert (Hz16 : exists z, class_size sc = 16 * z) by (unfold class_size, UNIT; eexists; reflexivity).
  unfold mmap_plan in Hp.
  set (size := class_size sc) in *.
  set (nosmall := is_bouncing s sc) in *.
  set (usage := if Z.even sc && (sc <? 32) then u + usage_of s (sc + 1) else u) in *.
  match type of Hp with context [page_round (size * ?c + UNIT)] => set (cnt1 := c) in Hp end.
  assert (Hc1 : 1 <= cnt1 <= 32 /\ size * cnt1 < 2 ^ 20 /\ (sc <= 26 -> 2 <= cnt1)).
  { subst cnt1.
    destruct ((usage <? 4 * cnt0) && negb nosmall); [|split; [lia|split; [lia|exact H26]]].
    destruct ((Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt0)); [lia|].
    destruct ((Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt0)); [lia|].
    destruct ((Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt0)); [lia|].
    destruct ((Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt0)); [lia|].
    lia. }
  cbv zeta in Hp.
  assert (HN : forall c, 1 <= c <= 32 -> size * c < 2 ^ 20 -> (sc <= 26 -> 2 <= c) ->
            (c, page_round (size * c + UNIT)) = (cnt, needed) ->
            1 <= cnt <= 32 /\ size * cnt < 2 ^ 20 /\ (sc <= 26 -> 2 <= cnt) /\ needed mod PGSZ = 0 /\ PGSZ <= needed /\ needed <= 2 ^ 20 /\
            (2 <= cnt -> UNIT + size * cnt <= needed) /\ req + IB + UNIT <= needed /\
            (cnt = 1 -> needed <= page_round (size + UNIT))).
  { intros c Hc Hcs Hc26 E. injection E as <- <-.
    pose proof (page_round_ge (size * c + UNIT)). pose proof (page_round_lt (size * c + UNIT)).
    pose proof (page_round_mod (size * c + UNIT)).
    unfold UNIT, IB, PGSZ in *.
    assert (A1 : 4096 <= page_round (size * c + 16)).
    { pose proof (Z_div_mod_eq_full (page_round (size * c + 16)) 4096). nia. }
    assert (A2 : page_round (size * c + 16) <= 2 ^ 20).
    { destruct Hz16 as [z Ez]. rewrite Ez in Hcs.
      assert (z * c <= 65535) by nia.
      pose proof (page_round_mono (size * c + 16) (2 ^ 20) ltac:(nia)).
      replace (page_round (2 ^ 20)) with (2 ^ 20) in H3 by reflexivity. lia. }
    assert (A3 : size * 1 <= size * c) by nia.
    repeat split; try lia. intros ->. rewrite Z.mul_1_r. lia. }
  destruct Hc1 as (Hc1 & Hc1s & Hc126).
  destruct (negb nosmall && (cnt1 <=? 7)) eqn:E7; [|exact (HN cnt1 Hc1 Hc1s Hc126 Hp)].
  set (rq := page_round (req + IB + UNIT)) in Hp.
  destruct ((rq <? size + UNIT) || ((4 * PGSZ <=? rq) && (usage <? 2 * cnt1))) eqn:E1; [|exact (HN cnt1 Hc1 Hc1s Hc126 Hp)].
  injection Hp as <- <-. subst rq. unfold UNIT, IB, PGSZ in *.
  pose proof (page_round_ge (req + 4 + 16)). pose proof (page_round_lt (req + 4 + 16)).
  pose proof (page_round_mod (req + 4 + 16)). unfold PGSZ in *.
  assert (Hrq : page_round (req + 4 + 16) <= 131072).
  { pose proof (page_round_mono (req + 4 + 16) 131072 ltac:(lia)).
    replace (page_round 131072) with 131072 in H2 by reflexivity. lia. }
  assert (A1 : 4096 <= page_round (req + 4 + 16)).
  { pose proof (Z_div_mod_eq_full (page_round (req + 4 + 16)) 4096). lia. }
  assert (A2 : page_round (req + 4 + 16) <= page_round (size + 16)) by (apply page_round_mono; lia).
  assert (Hn26 : ~ sc <= 26).
  { intros Hle. assert (size <= 3264).
    { subst size. pose proof (class_size_mono sc 26 ltac:(lia) Hle ltac:(lia)).
      replace (class_size 26) with 3264 in H2 by reflexivity. lia. }
    assert (page_round (req + 4 + 16) <= 4096).
    { pose proof (page_round_mono (req + 4 + 16) 4096 ltac:(lia)).
      replace (page_round 4096) with 4096 in H3 by reflexivity. lia. }
    apply orb_prop in E1. destruct E1 as [E1|E1].
    - apply Z.ltb_lt in E1. lia.
    - apply andb_prop in E1 as [E1 _]. apply Z.leb_le in E1. lia. }
  repeat split; lia.
Qed.

Lemma nested_facts sc cnt0 : ltac2:(tb__ "0|6|
SeS0Z0M0Vsc;A2S1Vsc;Z30M1A2A2S0Z1Vcnt0;A2S0Vsc;Z1aA2S0Z2M2Vcnt0;A2M3F_;S0S3S4S19Vsc;A1M4Vcnt0;A2S1dA2S5S1bG2A2A2SaS3S1dS4Vcnt0;G4A2A2S1eA2SdS21R1A1SdSeS0Vsc;Z17A2SeG3SeSeS0G0R2A2S0R2Z7fcA2A2SeSeS1Vsc;R1A2S0R1Z18A2A2SeSeS0G0R1A2S1R1G1A2A2SeS0S3R2S1eA2S19R1A1M5A2S1G4G5A2A2A2A2A2A2A2Tj;Ttotal;F_;F_;F_;F_;").
Proof.
  intros Hsc Hc H26 Hsmall total j.
  replace (PGSZ / 2) with 2048 in Hsmall by reflexivity. unfold UNIT in Hsmall.
  pose proof (class_size_bounds sc Hsc) as [S16 Smax].
  assert (H23 : sc <= 23).
  { apply class_le_23; [exact Hsc|]. nia. }
  assert (H2 : 2 <= cnt0) by (apply H26; lia).
  assert (Ht : 0 <= total <= 2044).
  { subst total. unfold UNIT, IB. split; nia. }
  pose proof (size_to_class_range total ltac:(unfold MMAP_THRESHOLD; lia)) as [Hj Hfit]. fold j in Hj, Hfit.
  pose proof (size_to_class_small total Ht) as Hj24. fold j in Hj24.
  assert (Hlt : class_size sc < class_size j).
  { subst total. unfold UNIT, IB in *. nia. }
  assert (sc < j).
  { destruct (Z_lt_dec sc j) as [|Hge]; [assumption|]. exfalso.
    pose proof (class_size_mono j sc ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
  repeat split; lia.
Qed.

Definition need (sc : Z) : nat := ltac2:(tb__ "0|2|
S10S16L_;S6Vsc;Z18M0A2S9S3S4Z2M1SaG0Vsc;A2A2G1A2A1U2X10x2").

Lemma need_ge2 sc : (2 <= need sc)%nat.
Proof. unfold need. destruct (sc <? 24) eqn:E; [apply Z.ltb_lt in E; lia | lia]. Qed.

Lemma need_nested sc j : ltac2:(tb__ "0|0|
S0Vsc;Z17A2S1Vsc;Vj;A2S31S34S2eVj;A1U2A2S2eVsc;A1A2F_;F_;").
Proof.
  intros H23 Hlt. unfold need. destruct (sc <? 24) eqn:E; [|apply Z.ltb_ge in E; lia].
  destruct (j <? 24) eqn:Ej; [apply Z.ltb_lt in Ej | apply Z.ltb_ge in Ej]; lia.
Qed.

Lemma need_le_fuel sc : ltac2:(tb__ "0|0|
S0Z0Vsc;A2S31S2eVsc;A1S23A2F_;").
Proof. intros H. unfold need, NEST_FUEL. destruct (sc <? 24); lia. Qed.
