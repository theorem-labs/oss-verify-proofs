(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac ZBridge.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import CidBits.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7CidBits~~~~~~hc3cb1hc3cb2hc3cb3hc3cb4hc3cb5hc3cb6hc4cb10hc4cb11hc3cb7hc3cb8hc3cb979OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs6SecMsb~~~~~~pd7popbitspd5smear46Stdlib6ZArith6BinInt1Zub3lorub6shiftrpd2st37Corelib4Init5Logichh73andub2leub2ltub3powpd6smear0hh72equb6moduloub4ones37Corelib4Init9Datatypeshm14boolhm14truehcdforall_rangeZub3addub3eqbub4log2ub3subpd7clzbitsub4lxor" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Open Scope Z_scope.

Definition smear : ltac2:(zQ "10!h9>1x$0$0") := ltac2:(zQ "70!h9!l9!lf!m5!mb!n1!n7\1x$0@1$6@1$5@1$4@1$3@1$2@1$1^1").
Definition popbits : ltac2:(zQ "10!h9>1y$0$0") := ltac2:(zQ "60!h9!nd!o4!ob!p1!p7\1y$0@1$2@1$1@1$5@1$4@1$3^1").
Definition clzbits : ltac2:(zQ "10!h9>1x$0$0") := ltac2:(zQ "30!h9!t9!u3\1x$0@1$1@1$2^1").

(* [comment removed for export] *)
Definition st : ltac2:(zQ "10!h9>1j$0>1y$0$0") := ltac2:(zQ "30!h9!hg3!hg9\1j$0\1y$0@2$1^1@2$2^1^2").
Definition smear0 : ltac2:(zQ "10!h9>1x$0$0") := ltac2:(zQ "20!hh2!h9\1x$1@2$0+i0@2$0+h0@2$0+8@2$0+4@2$0+2@2$0+1^1").

Lemma lor_lt_pow2 : ltac2:(zQ "60!hib!h9!hj2!hj7!hjc!hg3>1a$1>1b$1>1n$1>0@2$0@2$2Z^3@2$3^3@2$4+2^1>0@2$0@2$2Z^3@2$3^3@2$4+2^2@2$0@2$2Z@2$5^5^4@2$3@2$5^5^4@2$4+2^3").
Proof.
  intros a b n Ha Hb.
  assert (Hn : 0 <= n) by (destruct (Z.neg_nonneg_cases n) as [H|H]; [rewrite Z.pow_neg_r in Ha by lia; lia|exact H]).
  assert (H0 : 0 <= Z.lor a b) by (apply (proj2 (Z.lor_nonneg a b)); lia).
  split; [exact H0|].
  destruct (Z.eq_dec a 0) as [->|A]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|B]; [rewrite Z.lor_0_r; lia|].
  assert (Hp : 0 < Z.lor a b).
  { destruct (Z.eq_dec (Z.lor a b) 0) as [E|]; [|lia]. apply Z.lor_eq_0_iff in E. lia. }
  apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) n Hp)).
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma shiftr_le_self : ltac2:(zQ "40!hj2!h9!hg9!hib>1y$1>1j$1>0@2$0Z^2>0@2$0Z^2@2$3@2$0Z@2$2^4^3@2$0@2$2^4^3^4").
Proof.
  intros y j Hy Hj. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
  apply Z.div_le_upper_bound; [lia|]. assert (0 < 2^j) by (apply Z.pow_pos_nonneg; lia). nia.
Qed.

Lemma st_lt : ltac2:(zQ "60!h9!hj2!hib!hh2!hj7!hjc>1j$0>1y$0>1n$0>0@2$1Z^3>0@2$2@2$1Z^3@2$4^3@2$5+2^2@2$2@2$1Z@2$3^5^4@2$4@2$3^5^4@2$5+2^3").
Proof. intros j y n Hj Hy. unfold st. pose proof (shiftr_le_self y j ltac:(lia) Hj). apply lor_lt_pow2; lia. Qed.

Lemma smear0_lt : ltac2:(zQ "60!hib!h9!hk2!hj2!hj7!hjc>1x$1>1n$1>0@2$0@2$3Z^2@2$4^2@2$5+2^1@2$0@2$3Z@1$2^3@2$4@1$2^3@2$5+2^2").
Proof. intros x n Hx. unfold smear0. repeat (apply st_lt; [lia|]). exact Hx. Qed.

Lemma st_lor : ltac2:(zQ "40!h9!hh2!hg3!hkb>1j$0>1a$0>1b$0@3$3$0@2$1^3@2$2^2^1@2$2@2$1^3^2@2$1^3^1").
Proof.
  intros j a b. unfold st. rewrite Z.shiftr_lor.
  rewrite <- !Z.lor_assoc. f_equal. rewrite !Z.lor_assoc. rewrite (Z.lor_comm b (Z.shiftr a j)). reflexivity.
Qed.

Lemma smear0_lor : ltac2:(zQ "40!h9!hk2!hg3!hkb>1a$0>1b$0@3$3$0@1$1@2$2^2^1@2$2@1$1^2@1$1^1").
Proof. intros a b. unfold smear0. rewrite !st_lor. reflexivity. Qed.

(* [comment removed for export] *)
Lemma cb_st : ltac2:(zQ "a0!h9!hj2!hl1!hib!hkb!hh2!hg3!hj7!hjc!hg9>1j$0>1y$0>0@2$1Z^2>0@2$3@2$1Z^2@2$7^2@2$8+2+k0@3$4$0@2$2@2$6^3@2$2@2$9^3^4+hggggggggggggggg0+hggggggggggggggg0@2$5^4^3").
Proof.
  intros j y Hj Hy. pose proof (shiftr_le_self y j ltac:(lia) Hj) as Hs.
  change 18446744073709551616 with (2^64). rewrite (Z.mod_small (Z.shiftr y j)) by lia.
  rewrite Z.mod_small; [reflexivity|]. apply lor_lt_pow2; lia.
Qed.

Lemma smear_smear0 : ltac2:(zQ "80!h9!hib!hkb!u3!hk2!hj2!hj7!hjc>1x$0>0@2$1@2$5Z^1@2$6^1@2$7+2+k0@3$2$0@1$3^2@1$4^2").
Proof.
  intros x Hx. unfold smear, smear0, cb1, cb2, cb3, cb4, cb5, cb6.
  rewrite (cb_st 1 x) by lia.
  pose proof (st_lt 1 x 64 ltac:(lia) Hx) as H1.
  rewrite (cb_st 2) by lia. pose proof (st_lt 2 _ 64 ltac:(lia) H1) as H2.
  rewrite (cb_st 4) by lia. pose proof (st_lt 4 _ 64 ltac:(lia) H2) as H3.
  rewrite (cb_st 8) by lia. pose proof (st_lt 8 _ 64 ltac:(lia) H3) as H4.
  rewrite (cb_st 16) by lia. pose proof (st_lt 16 _ 64 ltac:(lia) H4) as H5.
  rewrite (cb_st 32) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lor_ones_low : ltac2:(zQ "80!h9!hj2!hla!hib!hkb!hg3!hj7!hjc>1n$0>1t$0>0@2$1Z^2>0@2$3@2$1Z^2@2$6^2@2$7+2^3@3$4$0@2$5@1$2^4^3@1$2^4").
Proof.
  intros n t Hn Ht. apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
  destruct (Z.lt_ge_cases i n) as [L|G].
  - rewrite Z.ones_spec_low by lia. reflexivity.
  - rewrite Z.ones_spec_high by lia. cbn.
    destruct (Z.eq_dec t 0) as [->|T]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|].
    apply Z.lt_le_trans with (m := 2^n); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

(* [comment removed for export] *)
Lemma smear0_pow2_chk : ltac2:(zQ "a0!hn9!ho1!hkb!h9!ho9!hk2!hp9!hpf!hla!hjc@3$2$0@3$4\1k$3@2$7@1$5@2$9+2^1@1$8@2$6^1+1Z+k0$1").
Proof. vm_compute. reflexivity. Qed.
Lemma smear0_pow2 : ltac2:(zQ "90!h9!hib!hkb!hk2!hp9!hj2!hj7!hla!hjc>1k$0>0@2$1@2$5Z^1@2$6^1+k0@3$2$0@1$3@2$8+2^2@1$7@2$4^2+1").
Proof. intros k Hk. apply Z.eqb_eq. apply (forall_rangeZ_spec _ 0 64 k smear0_pow2_chk); lia. Qed.

Lemma smear0_eq : ltac2:(zQ "90!h9!hj7!hib!hkb!hk2!hp9!hq5!hla!hjc>1x$0>0@2$2@2$1Z^1@2$1^1@2$8+2+k0@3$3$0@1$4^2@1$7@2$5@1$6^2+1").
Proof.
  intros x Hx. set (k := Z.log2 x).
  assert (Hk : 0 <= k < 64).
  { subst k. split; [apply Z.log2_nonneg|]. apply Z.log2_lt_pow2; lia. }
  destruct (Z.log2_spec x ltac:(lia)) as [Hlo Hhi]. fold k in Hlo, Hhi.
  set (r := x - 2^k).
  assert (Hr : 0 <= r < 2^k) by (subst r; rewrite Z.pow_succ_r in Hhi by lia; lia).
  assert (Hx2 : x = Z.lor (2^k) r).
  { rewrite <- Z.lxor_lor.
    - rewrite <- Z.add_nocarry_lxor. + subst r; lia.
      + apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
        destruct (Z.eqb_spec k i); [|reflexivity]. subst i. cbn.
        destruct (Z.eq_dec r 0) as [->|R]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; lia.
    - apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
      destruct (Z.eqb_spec k i); [|reflexivity]. subst i. cbn.
      destruct (Z.eq_dec r 0) as [->|R]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; lia. }
  rewrite Hx2, smear0_lor, smear0_pow2 by lia.
  apply lor_ones_low; [lia|].
  pose proof (smear0_lt r k Hr) as Hs.
  split; [lia|]. apply Z.lt_le_trans with (m := 2^k); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

(* [comment removed for export] *)
Lemma popbits_chk : ltac2:(zQ "a0!hn9!ho1!hkb!h9!ho9!t9!hp9!hpf!hla!hqc@3$2$0@3$4\1k$3@2$7@1$5@1$8@2$6^1+1@2$9+jf^1Z+k0$1").
Proof. vm_compute. reflexivity. Qed.

Theorem clzbits_eq : ltac2:(zQ "80!h9!hj7!hib!hkb!hr2!hq5!hjc!hqc>1x$0>0@2$2@2$1Z^1@2$1^1@2$6+2+k0@3$3$0@1$4^2@2$7+jf@1$5^2").
Proof.
  intros x Hx. unfold clzbits. rewrite smear_smear0, smear0_eq by lia.
  assert (Hk : 0 <= Z.log2 x < 64) by (split; [apply Z.log2_nonneg|apply Z.log2_lt_pow2; lia]).
  apply Z.eqb_eq. apply (forall_rangeZ_spec _ 0 64 (Z.log2 x) popbits_chk); lia.
Qed.

(* [comment removed for export] *)
Lemma lxor63_sub : ltac2:(zQ "60!h9!hj2!hib!hkb!hrc!hqc>1c$0>0@2$2@2$1Z^1@2$1^1+jf@3$3$0@2$4^2+jf@2$5+jf^2").
Proof.
  intros c Hc.
  assert (E : forall_rangeZ (fun c => Z.eqb (Z.lxor c 63) (63 - c)) 0 64 = true) by (vm_compute; reflexivity).
  apply Z.eqb_eq. apply (forall_rangeZ_spec _ 0 64 c E); lia.
Qed.
(* [comment removed for export] *)
