(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIface HeapIfaceA JbtFsInv JbtFsInvLaws.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtSmallocSel () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFsInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFsInvLaws."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtSmallocSel.LEAST."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtSmallocSel.SEL."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."], [["1bool"; "1false"; "1nat"; "1true"; "2and"; "2eq"; "2ex"; "2iff"; "2not"; "2or"; "3Z"; "0L"; "4ff_addr"; "4ff_cap"; "4ff_class"; "4ff_rs"]; ["4fframe"; "5fs_frame"; "5fs_nfr"; "6fs_slot_taken"; "7sl_taken"; "8sl_colb"; "8sl_cols"; "8sl_flag"; "8sl_hit"; "8sl_rs"; "9In"; ":add"; ":le"; ":lt"; ":modulo"; ":of_nat"]; [":pow"; ":sub"; "0bot"; "0c"; "0f"; "0fs"; "0gcb"; "0h"; "0i"; "0j"; "0k"; "0n"; "0p"; "0sp"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Section SEL.
Variable fs : Z.
Variable L : list fframe.
Variables (gcb : bool) (sp bot : Z).
Definition sl_hit (c i : Z) (f : fframe) : bool := (ff_class f =? c) && (ff_addr f =? fs_frame fs c i).
Definition sl_flag (c i : Z) : Z := if existsb (sl_hit c i) L then 1 else 0.
Definition sl_rs (c i : Z) : Z := match find (sl_hit c i) L with Some f => ff_rs f - 32 | None => 0 end.
Definition sl_colb (f : fframe) : bool := gcb && (bot <? ff_rs f - 32) && (ff_rs f - 32 <? sp).
Definition sl_cols (c i : Z) : bool := gcb && negb (sl_flag c i =? 0) && (bot <? sl_rs c i) && (sl_rs c i <? sp).
#[using="Type"] Lemma sl_hit_spec : ltac2:(TCodec.tc2 tcn__JbtSmallocSel "K':&@&7'5'0&Hr3r2r1%43321(3%83721'4&>%116%<3?19&<%119&AvQ5%231>=%B3E41%:271%E2<1pR:G1pRBI1pR8J1").
Proof. intros c i f. unfold sl_hit. rewrite andb_true_iff, !Z.eqb_eq. tauto. Qed.
#[using="Type"] Lemma sl_flag_01 : ltac2:(TCodec.tc2 tcn__JbtSmallocSel ">':'9'5&Gr2r1%3221z%63821+1%83:41%:231pRB<1pR8=1").
Proof. intros c i. unfold sl_flag. destruct (existsb _ L); [right | left]; reflexivity. Qed.
#[using="Type"] Lemma sl_flag_taken : ltac2:(TCodec.tc2 tcn__JbtSmallocSel "@':&7'5&Gr2r1%3221+1%63821&CvQ5v;%342187%<251pRB>1pR8?1").
Proof.
intros c i. unfold sl_flag, fs_slot_taken. destruct (existsb (sl_hit c i) L) eqn:E.
- split; [intros _ | reflexivity]. apply existsb_exists in E. destruct E as (f & Hf & Hh). apply sl_hit_spec in Hh. exists f. tauto.
- split; [discriminate|]. intros (f & Hf & H1 & H2). exfalso.
assert (X : existsb (sl_hit c i) L = true) by (apply existsb_exists; exists f; split; [exact Hf | apply sl_hit_spec; tauto]). congruence.
Qed.
#[using="Type"] Lemma sl_find : ltac2:(TCodec.tc2 tcn__JbtSmallocSel "Q;':&8'5&Gr2r1%3221z%63821%811'6&@'4&Jv;%234:1&>%11<r4%A3C21&<%11@&AvQ5r3%33271%H3J51&I%12:4&Q1&?%11J+Q0%4221%Q03Q261%G291%H2A1%I2F1qR:K1%M2L1p0O1pRBQ91pR8Q:1").
Proof.
intros c i NZ. unfold sl_flag in NZ. unfold sl_rs. destruct (find (sl_hit c i) L) as [f|] eqn:E.
- apply find_some in E. destruct E as [Hf Hh]. apply sl_hit_spec in Hh. exists f. tauto.
- exfalso. destruct (existsb (sl_hit c i) L) eqn:X; [|apply NZ; reflexivity]. apply existsb_exists in X. destruct X as (f & Hf & Hh).
pose proof (find_none _ _ E f Hf). congruence.
Qed.
Hypothesis ND : List.NoDup (map ff_addr L).
#[using="ND"] Lemma sl_find_uniq : ltac2:(TCodec.tc2 tcn__JbtSmallocSel "Q9':&@&Jr1v;%33421'5&>r2%211r4%53;21&<r3%211&AvQ5r5%33218%=3C51'4&Gr6%2216+1%C3I21&I%125:&Q1&?%11D+Q0%4221%K3Q161%>291p0@1p0I1p0Q01pR:Q51pRBQ71pR8Q81").
Proof.
intros c i f Hf H1 H2. assert (T : sl_flag c i = 1) by (apply sl_flag_taken; exists f; tauto). split; [exact T|].
destruct (sl_find c i ltac:(lia)) as (f' & Hf' & H1' & H2' & E). rewrite E.
assert (f' = f) by (apply (nodup_map_inj _ _ ff_addr L f' f ND Hf' Hf); congruence). subst f'. reflexivity.
Qed.
#[using="ND"] Lemma sl_cols_frame : ltac2:(TCodec.tc2 tcn__JbtSmallocSel "Q1':&@&Jr1v;%33421'5&>r2%211r4%53;21&<r3%211&AvQ5r5%33218%=3C51'0&Fr6%2216&E%11?%D3631p081p0A1p0H1pR:M1pRBO1pR8Q01").
Proof.
intros c i f Hf H1 H2. destruct (sl_find_uniq c i f Hf H1 H2) as [T E]. unfold sl_cols, sl_colb. rewrite T, E. cbn. rewrite andb_true_r. reflexivity.
Qed.
#[using="Type"] Lemma sl_cols_true : ltac2:(TCodec.tc2 tcn__JbtSmallocSel "Q0':&7'5'0&Fr2r1%3221(3%73621'4vQ6%:3914&8&G%12:9z%?3A21%511&MvQ2&I%12A@%4231vQ=%6231%@231%A291%B2@1%L2D1pRBN1pR8O1").
Proof.
intros c i. unfold sl_cols. rewrite !andb_true_iff, negb_true_iff, Z.eqb_neq, !Z.ltb_lt. tauto.
Qed.
End SEL.
Section SE.
Variables (f : Z -> bool).
Lemma least_false : forall (n : nat), (exists i, 0 <= i < Z.of_nat n /\ f i = false) ->
exists j, 0 <= j < Z.of_nat n /\ f j = false /\ forall i, 0 <= i < j -> f i = true.
Proof.
intros n.
induction n as [|n IH]; intros (i & Hi & Fi); [lia|].
destruct (Z.eq_dec i (Z.of_nat n)) as [->|NE].
- destruct (existsb (fun m => negb (f (Z.of_nat m))) (seq 0 n)) eqn:E.
+ apply existsb_exists in E. destruct E as (m & Hm & Fm). apply in_seq in Hm. apply negb_true_iff in Fm.
destruct (IH ltac:(exists (Z.of_nat m); split; [lia | exact Fm])) as (j & Hj & Fj & Lj). exists j. split; [lia | split; assumption].
+ exists (Z.of_nat n). split; [lia|]. split; [exact Fi|]. intros i Hi2.
pose proof (existsb_nth (fun m => negb (f (Z.of_nat m))) (seq 0 n) 0%nat (n := Z.to_nat i) ltac:(rewrite length_seq; lia) E) as X.
rewrite seq_nth in X by lia. cbn in X. rewrite Z2Nat.id in X by lia. apply negb_false_iff in X. exact X.
- destruct (IH ltac:(exists i; split; [lia | exact Fi])) as (j & Hj & Fj & Lj). exists j. split; [lia | split; assumption].
Qed.
End SE.
Lemma fs_nfr_cap : ltac2:(TCodec.tc2 tcn__JbtSmallocSel "M':'4&Lzr1%3221+4%5231%7231'5&=r2%211&B%113%63?31&Q0+2&Q1+>%2219%5241%=3F81&M%12E:%H231%I2;1p0C1pRFL1").
Proof. intros k Hk. assert (E : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4) by lia. destruct E as [->|[->|[->|[->| ->]]]]; vm_compute; intuition congruence. Qed.
Section LEAST.
Variable fs : Z.
Variables FF LK : list fframe.
Variables (gcb : bool) (sp bot : Z).
Variables (k h : Z).
Hypothesis Hk : 0 <= k <= 4.
Hypothesis ND : List.NoDup (map ff_addr (FF ++ LK)).
Hypothesis ROOM : ff_room k FF LK.
Definition sl_taken (p : Z) : bool := negb (sl_flag fs (FF ++ LK) k p =? 0) && negb (sl_cols fs (FF ++ LK) gcb sp bot k p).
#[using="Hk ROOM"] Lemma sl_some_free : ltac2:(TCodec.tc2 tcn__JbtSmallocSel "F'6':'4&Lzr1%3221&M&BvQ:%211%4261%:261'5'0&D%11;(1%53421%A271qRJC1%E2D1").
Proof.
destruct (fs_nfr_cap k Hk) as (EC & EN & NP).
destruct (existsb (fun m => negb (sl_taken (Z.of_nat m))) (seq 0 (Z.to_nat (fs_nfr k)))) eqn:E.
- apply existsb_exists in E. destruct E as (m & Hm & Fm). apply in_seq in Hm. apply negb_true_iff in Fm. exists (Z.of_nat m). split; [lia | exact Fm].
- exfalso.
assert (ALL : forall p, 0 <= p < fs_nfr k -> fs_slot_taken fs (FF ++ LK) k p).
{ intros p Hp.
pose proof (existsb_nth (fun m => negb (sl_taken (Z.of_nat m))) (seq 0 (Z.to_nat (fs_nfr k))) 0%nat (n := Z.to_nat p) ltac:(rewrite length_seq; lia) E) as X.
rewrite seq_nth in X by lia. cbn in X. rewrite Z2Nat.id in X by lia. apply negb_false_iff in X. unfold sl_taken in X.
apply andb_true_iff in X. destruct X as [X _]. apply negb_true_iff, Z.eqb_neq in X.
apply sl_flag_taken. destruct (sl_flag_01 fs (FF ++ LK) k p); [contradiction | assumption]. }
set (g := fun m : nat => fs_frame fs k (Z.of_nat m)).
set (LKk := filter (fun f => Z.eqb (ff_class f) k) (FF ++ LK)).
assert (NDg : List.NoDup (map g (seq 0 (Z.to_nat (fs_nfr k))))).
{ apply Finite.Injective_map_NoDup_in; [|apply seq_NoDup]. intros a b _ _ Eab. unfold g in Eab. apply fs_frame_inj in Eab; lia. }
assert (INC : incl (map g (seq 0 (Z.to_nat (fs_nfr k)))) (map ff_addr LKk)).
{ intros a Ha. apply in_map_iff in Ha. destruct Ha as (m & <- & Hm). apply in_seq in Hm.
destruct (ALL (Z.of_nat m) ltac:(lia)) as (f & Hf & H1 & H2). apply in_map_iff. exists f. split; [exact H2|].
unfold LKk. apply sfilter_In. split; [apply Is_true_eq_left, Z.eqb_eq; exact H1 | exact Hf]. }
pose proof (NoDup_incl_length NDg INC) as LE. rewrite !length_map, length_seq in LE.
unfold ff_room, ff_count in ROOM. fold LKk in ROOM. rewrite EC in ROOM. lia.
Qed.
#[using="Hk ROOM"] Lemma sl_least_free : ltac2:(TCodec.tc2 tcn__JbtSmallocSel "Q6'6':'4&Lzr1%3221&M&BvQ:%211%4261%:261'5'0&D&N&KvQ7%221>%421:%611(1%:3921r2%B2D1%H2D1%:293%<21B%>11(3%B3A21p061pRBQ01%Q02;1%Q12G1qRDQ31%Q52Q41").
Proof.
destruct (fs_nfr_cap k Hk) as (EC & EN & NP). destruct sl_some_free as (p & Hp & Fp).
destruct (least_false (fun i => sl_taken ((h + i) mod fs_nfr k)) (Z.to_nat (fs_nfr k))) as (j & Hj & Fj & Lj).
- exists ((p - h) mod fs_nfr k). pose proof (Z.mod_pos_bound (p - h) (fs_nfr k) NP). split; [lia|].
replace ((h + (p - h) mod fs_nfr k) mod fs_nfr k) with p; [exact Fp|].
rewrite Zplus_mod_idemp_r. replace (h + (p - h)) with p by ring. symmetry. apply Z.mod_small. exact Hp.
- exists j. split; [lia | split; assumption].
Qed.
End LEAST.
