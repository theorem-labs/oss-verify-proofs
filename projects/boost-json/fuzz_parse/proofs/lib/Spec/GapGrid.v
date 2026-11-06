(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Decode.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import KInv.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z46Stdlib6ZArith6BinInt1Zhc3pow79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6Decode~~~~~~ja8CEIL_MIN79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec7GapGrid~~~~~~o26GRID_Jo26GRID_Mo2agrid_floorhc3addhc2lehc3mulhc2lt37Corelib4Init5Logicv63and37Corelib4Init9Datatypeshh06lengthhh04listhh03natv62exv63not37Corelib4Init5Peanohkc2lt36Stdlib5Lists4Listhm62Inhc6of_nat04Npos35stdpp9bitvectorbdefinitionshoe2bvhh04prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4KInv~~~~~~hr93elohc3divhc3subhh04bool89OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec7GapGrid4Grid~~~~~~ih04cellih04slothc3ltbv62eqih05gslothr93ehiv62orhc6modulohoebbv_unsignedhh04pairhh04true3h5LinuxProcessSemanticsfLinuxProcessSem5Stateiqcbregion_freehh03appiqc7vm_mapsiqcbvm_reservediqc9alloc_topo26GRID_Wiqc6VmMapsiqc9page_sizehoe7Z_to_bv" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition GRID_M : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!j4@2$0+2+i3").
Definition GRID_J : Z := 2730.
Definition GRID_W : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!j4@2$0+2+i2").     (* [comment removed for export] *)
Definition grid_floor : Z := 0x2aaaaaaab000.

Lemma grid_fits : ltac2:(zQ "70!n7!s1!sa!t3!u0!u6!ub@2$5@2$4$3@2$6$1$2$0").
Proof. vm_compute. discriminate. Qed.
Lemma grid_floor_pos : ltac2:(zQ "20!t3!v1@2$1Z$0").
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma pigeon : ltac2:(zQ "c0!h9!hga!hi8!hj2!hja!hk1!hk6!hm0!hn9!u6!v1!hnf>1n$4>1l@1$3$0>0@2$7@2$2$0^1^2@2$5$0\1i$0@2$1@2$1@2$9Z^1@2$a^1@1$b^4@1$6@3$8$0^1^3").
Proof.
  induction n as [|n IH]; intros l Hl; [lia|].
  destruct (in_dec Z.eq_dec (Z.of_nat n) l) as [Hin|Hnot].
  - destruct (in_split _ _ Hin) as (l1 & l2 & ->).
    assert (Hl' : (length (l1 ++ l2) < n)%nat) by (rewrite length_app; rewrite length_app in Hl; cbn in Hl; lia).
    destruct (IH (l1 ++ l2) Hl') as (i & Hi & Hni).
    exists i. split; [lia|]. intros H. apply in_app_or in H as [H|[H|H]]; [apply Hni; apply in_or_app; auto| lia| apply Hni; apply in_or_app; auto].
  - exists (Z.of_nat n). split; [lia| exact Hnot].
Qed.

Section Grid.
Variable E : ltac2:(zQ "40!ho8!hqb!hj2!hr1@1$2@2$3@1$1@1$0#k0@1$1@1$0#k0").
Variable S : Z.
Hypothesis HS : ltac2:(zQ "40!hga!jh7!u6!v1@2$0@2$3Z?1S@2$2?1S$1").
Hypothesis HE : ltac2:(zQ "b1!ho8!hqb!hr1!in8!hv5!hga!jh7!hn9!u6!v1!ig2&@2$2@1$1@1$0#k0@1$1@1$0#k0>1e~0>0@3$7~0^1?1E@2$5@2$9@1$4^2@1$3^2@2$8@2$a@1$3^2@1$4^2$6").

Definition slot : ltac2:(zQ "10!h9>1i$0$0") := ltac2:(zQ "50!h9!sa!t3!u0!ub\1i$0@2$3$2@2$4^1$1").
(* [comment removed for export] *)
Definition cell : ltac2:(zQ "40!ho8!hqb!hr1!h9>1e@2$2@1$1@1$0#k0@1$1@1$0#k0$3") := ltac2:(zQ "80!ho8!hqb!hr1!sa!t3!hv5!hvc!ig2\1e@2$2@1$1@1$0#k0@1$1@1$0#k0@2$6@2$7@1$5^1$4$3").
Definition gslot : ltac2:(zQ "40!ho8!hqb!hr1!h9>1e@2$2@1$1@1$0#k0@1$1@1$0#k0$3") := ltac2:(zQ "a0!ig8!ho8!h9!u0!hqb!hr1!il4!ilc!hv5!im4\1e@2$5@1$4@1$1#k0@1$4@1$1#k0=1c$2@1$6^1M0\0$0$2@2$9@1$8^2@2$3@1$7^1?1S^1@2$3^1+1").

Lemma meets_unique : ltac2:(zQ "c1!ho8!hqb!hr1!h9!ilc!v1!ima!imf!in8!hv5!hn9!u0&@2$2@1$1@1$0#k0@1$1@1$0#k0>1e~0>1i$3>0@3$a~0^2?1E>0@2$5@1$9^3@2$b@1$4^2?1S>0@2$5@1$4^3@1$8^4@3$6$3^4@1$7^5").
Proof.
  intros e i He H1 H2. destruct (HE e He) as [W1 W2]. unfold gslot, cell, slot in *.
  unfold GRID_M, GRID_W in *.
  set (c := (elo e - grid_floor) / 2^35) in *.
  assert (Hc : grid_floor + c * 2^35 <= elo e < grid_floor + (c + 1) * 2^35) by (subst c; Z.div_mod_to_equations; lia).
  destruct (Z.ltb_spec (elo e) (grid_floor + c * 2^35 + S)); nia.
Qed.

Theorem grid_gap : ltac2:(zQ "h41!ho8!hqb!u6!hr1!hga!h9!u0!hi8!ima!hk1!inf!n7!s1!t3!in8!hv5!hn9!v1!io4!hnf&@2$3@1$1@1$0#k0@1$1@1$0#k0>0@2$h1@1$h3@2$7~0?1E$c@2$9$5\1a$5@2$4@3$8$5@2$h2^1+hgg0Z@2$4@2$2$d^1@2$4@2$2@2$6^1?1S$b>1e~0>0@3$h0~0^1?1E@2$a@2$2@2$6^3?1S@1$f^2@2$2@1$e^2^3").
Proof.
  intros HL.
  assert (HL' : (length (map gslot E) < Z.to_nat GRID_J)%nat) by (rewrite length_map; unfold GRID_J in *; lia).
  destruct (pigeon (Z.to_nat GRID_J) (map gslot E) HL') as (i & Hi & Hni).
  rewrite Z2Nat.id in Hi by (unfold GRID_J; lia).
  exists (slot i). pose proof grid_fits as GF.
  unfold slot, GRID_M, GRID_J, GRID_W, grid_floor, CEIL_MIN in *.
  split; [| split; [lia| split; [nia|]]].
  { Z.div_mod_to_equations. nia. }
  intros e He. destruct (HE e He) as [W1 W2].
  destruct (Z.le_gt_cases (0x2aaaaaaab000 + i * 2^35 + S) (elo e)); [left; lia|].
  destruct (Z.le_gt_cases (ehi e) (0x2aaaaaaab000 + i * 2^35)); [right; lia|].
  exfalso. apply Hni. rewrite (meets_unique e i He) by (unfold slot, GRID_M, grid_floor; lia).
  apply in_map. exact He.
Qed.
End Grid.

Lemma region_free_introZ : ltac2:(zQ "e1!ho8!hqb!iod!hr1!u0!u6!ig8!hj2!ipc!iq4!ima!inf!ita!hn9&@2$3@1$1@1$0#k0@1$1@1$0#k0>4maps@1$7~0>1a@1$1@1$0#k0>1n@1$1@1$0#k0>0>1e@1$1@1$0#k0>2sz@1$1@1$0#k0>0@3$d~0@4$8@1$1@1$0#k0@1$1@1$0#k0^2^1^5@2$b@2$5@2$4@2$2@1$0#k0^5@2$2@1$0#k0^4@2$2@1$0#k0^3@2$5@2$4@2$2@1$0#k0^3@2$2@1$0#k0^2@2$2@1$0#k0^5@3$a$6@3$c^4^3^2$9").
Proof.
  induction maps as [|[e0 sz0] maps IH]; intros a n H; [reflexivity|]. cbn [region_free].
  rewrite IH by (intros; apply H; right; assumption).
  specialize (H e0 sz0 (or_introl eq_refl)). unfold iv_overlap.
  destruct (Z.ltb_spec0 (bv_unsigned a) (bv_unsigned e0 + bv_unsigned sz0));
  destruct (Z.ltb_spec0 (bv_unsigned e0) (bv_unsigned a + bv_unsigned n)); cbn; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Theorem gap_exists : ltac2:(zQ "hf2!ho8!hqb!hr1!hga!u6!v1!iu9!ima!h9!iv0!ivb!iod!jga!jh7!in8!hv5!io4!ig8!hi8!iq4!hk1!ji0!jia!ita!n7!s1!hn9!u0!hnf!ig2!jj7&@2$2@1$1@1$0#k0@1$1@1$0#k0&@3$6~0@1$a^5@1$9^5>1h$h5>2nZ$8>0@2$3@2$5Z^1@2$4^1$d>0@3$7$8@2$h0^2+hgg0Z>0>1e~0>0@3$ha~0^1~1@2$3@2$5@1$f^2@1$e^2@2$4@2$hd@1$e^2@1$f^2$d>0@2$5@1$hc@2$h2~0~1$h9>0@2$4$h8@1$c^6@2$h4@1$1@1$0#k0\1a@1$1@1$0#k0@2$3@3$7$8@2$h0@2$b@1$0#k0^1$h6Z@2$3@2$5Z@2$b@1$0#k0^1@2$3@2$4@2$hb@2$b@1$0#k0^1^7@1$c^8@3$7$h1@3$h7@3$6~0@1$a^8@1$9^8^1@2$he@1$0#k0^7$h3").
Proof.
  intros h nZ HS Hal HE HL HT.
  destruct (grid_gap (vm_reserved h ++ vm_maps h) nZ HS HE HL) as (a & Ha & Hf & Hc & Hfree).
  pose proof grid_floor_pos as FP. unfold GRID_W in HS.
  assert (Ra : 0 <= a < 2^64) by (unfold grid_floor, CEIL_MIN in *; lia).
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; lia).
  exists (Z_to_bv 64 a). rewrite Ua. split; [unfold page_size; exact Ha|]. split; [lia|]. split; [lia|].
  apply region_free_introZ; intros e sz He.
  specialize (Hfree (e, sz) He). unfold elo, ehi in Hfree. cbn in Hfree. rewrite Ua, Un. lia.
Qed.
(* [comment removed for export] *)
