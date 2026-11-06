(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import CatSim ShapeAlg Spec.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "3h5LinuxProcessSemanticsfLinuxProcessSem5State05event37Corelib4Init9Datatypesj54listj53nil69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~la4TSetla6t_emit37Corelib7Numbers7BinNumsq54Npos3h5LinuxProcessSemanticsfLinuxProcessSem2Fss52Fsla6t_exit35stdpp9bitvectorbdefinitionsve2bvla6t_alt269OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec~~~~~~hi91Wj53app37Corelib4Init5Logichmb2eqq51Zla4t_eqve7Z_to_bvhmb3andhi99exit_code46Stdlib6ZArith6BinInt1Zhqe2lehqe2ltve6bv_and" s.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma t_emit_has_nil : ltac2:(zQ "50!ie!kd!l4!p5!pc>3evs@1$1$0>1T$3@3$4^2^1@1$2$0").
Proof. intros evs T. unfold t_emit. left. apply is_prefix_nil. Qed.

Lemma t_exit_has_nil : ltac2:(zQ "60!l4!re!v0!ie!v5!hhb>4code@1$5@1$1#k0>2fs$2@3$4^2^1@1$0$3").
Proof. intros. unfold t_exit. apply t_emit_has_nil. Qed.

Lemma t_alt2_has_nil_l : ltac2:(zQ "40!l4!ie!p5!hi0>1A$2>1B$2>0@1^2@1$0$1@3$3^3^2@1$0$1").
Proof. intros A B H. unfold t_alt2. left. exact H. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma W_app : ltac2:(zQ "80!kd!re!hm0!hhb!hm5!ie!hnf!ho5>2ch$7>1a@1$0@1$3@1$1#8>1b@1$0@1$3@1$1#8@3$6@1$0$5@2$2^3@3$4@1$3@1$1#8^2^1@3$4$5@2$2^3^2@2$2^3^1").
Proof. intros. unfold W. apply map_app. Qed.

Lemma W_nil : ltac2:(zQ "80!l4!ie!kd!hnf!re!ho5!hm0!hhb>2ch$5@3$3@1$2$1@2$6^1@1$0@1$7@1$4#8@1$0$1").
Proof. reflexivity. Qed.

Lemma t_emit_W_app : ltac2:(zQ "90!re!pc!hm0!hhb!kd!hm5!ho5!p5!ho9>2ch$6>1a@1$4@1$3@1$0#8>1b@1$4@1$3@1$0#8>1T$7@2$8@2$1@2$2^4^3@2$1@2$2^4^2^1@2$1@2$2^4@3$5@1$3@1$0#8^3^2^1").
Proof.
  intros ch a b T. rewrite W_app. apply t_eq_sym.
  (* [comment removed for export] *)
  intros tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & HT)].
    + apply is_prefix_app_split in Hp as [Hp | (b' & -> & Hp)].
      * left. exact Hp.
      * right. exists b'. split; [reflexivity | left; exact Hp].
    + right. exists (W ch b ++ tr'). split; [rewrite app_assoc; reflexivity|].
      right. exists tr'. auto.
  - intros [Hp | (tr' & -> & [Hp | (tr'' & -> & HT)])].
    + left. apply is_prefix_app_r. exact Hp.
    + left. apply is_prefix_app_mono. exact Hp.
    + right. exists tr''. rewrite app_assoc. auto.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma t_emit_W_nil : ltac2:(zQ "90!l4!re!ho5!ie!p5!pc!ho9!hm0!hhb>2ch$2>1T$4>0@1^1@1$0$3@2$6@2$5@2$7^3@1$0@1$8@1$1#8^2^2").
Proof. intros ch T H0. rewrite W_nil. apply t_emit_nil_eq. exact H0. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma exit_code_and_255 : ltac2:(zQ "a0!re!hp0!hpa!hnf!ho5!hq1!hs6!hsc!hhb!ht2>1c$4>0@2$2@2$6Z^1@2$7^1+hg0@3$3@1$8@1$0#k0@3$9@1$0#k0@2$1@1$0#k0^2@2$1@1$0#k0+vf@1$5^2").
Proof.
  intros c Hc. unfold exit_code. apply bv_eq.
  rewrite bv_and_unsigned, !Z_to_bv_unsigned.
  rewrite !bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
  change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma exit_leaf_eq : ltac2:(zQ "f0!re!v5!hp0!l4!hpa!ho5!v0!pc!ho9!hm0!hq1!hs6!hsc!hhb!ht2>1c$5>2fs$6>0@2$4@2$bZ^2@2$c^2+hg0@2$8@2$7@2$9+1@1$3@1$d@1$0#8@2$1@3$e@1$0#k0@2$2@1$0#k0^3@2$2@1$0#k0+vf^2@2$1@1$a^3^2").
Proof.
  intros c fs Hc. rewrite exit_code_and_255 by exact Hc. apply t_emit_W_nil. apply t_exit_has_nil.
Qed.
End FPX1.
(* [comment removed for export] *)
