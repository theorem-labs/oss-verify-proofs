(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec StoreOk.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv01Zhfbbv_unsigned37Corelib4Init5Logicl23and46Stdlib6ZArith6BinInt1Zmc3addmc2lemc2lt37Corelib4Init9Datatypesp44prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Frame4FPX1~~~~~~r37outsidep44listp43appl23iffp46optionl22eq69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7StoreOk~~~~~~hhb9mem_growsr39frame_modp46lengthmc6of_natl23not69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~ho66wbytesr36in_rngmc3powp44consp43nilp44pairp44boolp44true3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshvb8store_okp43nat3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeik47Segment69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~io43rdnhf7Z_to_bv" s.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition in_rng : ltac2:(zQ "30!h9!jc!k1>1a@1$1@1$0#k0>4base@1$1@1$0#k0>3len$2P") := ltac2:(zQ "80!h9!k4!jc!m6!k1!o4!oa!of\1a@1$2@1$0#k0\4base@1$2@1$0#k0\3len$4@2$3@2$6@2$1@1$0#k0^2@2$1@1$0#k0^3@2$7@2$1@1$0#k0^3@2$5@2$1@1$0#k0^2^1").

Fixpoint outside (a : word) (rs : list (word * Z)) : Prop :=
  match rs with
  | [] => True
  | (b, n) :: rs' => ~ in_rng a b n /\ outside a rs'
  end.

Lemma outside_app : ltac2:(zQ "90!h9!jc!qc!k1!v0!va!hg1!m6!hg7>1a@1$1@1$0#k0>3rs1@1$5@2$2@1$1@1$0#k0$3>3rs2@1$5@2$2@1$1@1$0#k0$3@2$8@2$4^3@3$6@2$2@1$1@1$0#k0$3^2^1@2$7@2$4^3^2@2$4^3^1").
Proof.
  intros a rs1 rs2. induction rs1 as [|[b n] rs1 IH]; cbn; tauto.
Qed.

Definition frame_mod : ltac2:(zQ "61!h9!jc!hgd!va!qc!k1&>0@1$1@1$0#k0@1$2@1$1@1$0#8>3mem~0>4mem'~0>2rs@1$3@2$4@1$1@1$0#k0$5P") := ltac2:(zQ "a1!h9!jc!hgd!va!qc!m6!hh6!k1!v0!hl5&>0@1$1@1$0#k0@1$2@1$1@1$0#8\3mem~0\4mem'~0\2rs@1$3@2$4@1$1@1$0#k0$7@2$5>1a@1$1@1$0#k0>0@2$8^1^2@3$6@1$2@1$1@1$0#8@1^4^2@1^5^2@2$9^3^2").

Lemma frame_mod_refl : ltac2:(zQ "70!h9!jc!va!hgd!qc!k1!hm2>3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8>2rs@1$2@2$4@1$1@1$0#k0$5@3$6^2^2^1").
Proof. intros. split; [intros; reflexivity | apply mem_grows_refl]. Qed.

Lemma frame_mod_weaken : ltac2:(zQ "81!h9!jc!va!hgd!qc!k1!hm2!v0&>0@1$1@1$0#k0@1$3@1$1@1$0#8>3mem~0>4mem'~0>2rs@1$2@2$4@1$1@1$0#k0$5>3rs'@1$2@2$4@1$1@1$0#k0$5>0>1a@1$1@1$0#k0>0@2$7^1^2@2$7^2^4>0@3$6^5^4^3@3$6^6^5^3").
Proof.
  intros mem mem' rs rs' Hw [He Hg]. split; [|exact Hg]. intros a Ha. apply He, Hw, Ha.
Qed.

Lemma frame_mod_trans : ltac2:(zQ "81!h9!jc!hgd!qc!k1!hm2!va!hg1&>0@1$1@1$0#k0@1$2@1$1@1$0#8>2m1~0>2m2~0>2m3~0>3rs1@1$6@2$3@1$1@1$0#k0$4>3rs2@1$6@2$3@1$1@1$0#k0$4>0@3$5^5^4^2>0@3$5^5^4^2@3$5^7^5@3$7@2$3@1$1@1$0#k0$4^4^3").
Proof.
  intros m1 m2 m3 rs1 rs2 [E1 G1] [E2 G2]. split.
  - intros a Ha. apply outside_app in Ha as [H1 H2]. rewrite (E2 a H2). apply E1, H1.
  - eapply mem_grows_trans; eassumption.
Qed.

(* [comment removed for export] *)
Lemma frame_mod_trans_same : ltac2:(zQ "71!h9!jc!hgd!hm2!va!qc!k1&>0@1$1@1$0#k0@1$2@1$1@1$0#8>2m1~0>2m2~0>2m3~0>2rs@1$4@2$5@1$1@1$0#k0$6>0@3$3^4^3^1>0@3$3^4^3^2@3$3^6^4^3").
Proof.
  intros m1 m2 m3 rs H1 H2. eapply frame_mod_weaken; [| exact (frame_mod_trans _ _ _ _ _ H1 H2)].
  intros a Ha. apply outside_app. tauto.
Qed.

(* [comment removed for export] *)
Lemma wbytes_outside : ltac2:(zQ "e0!h9!jc!hme!hgd!hn7!va!hh6!ho0!hs0!hsa!o4!oa!ht3!k4>2bs@1$5@1$1@1$0#8>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>4base@1$1@1$0#k0>1a@1$1@1$0#k0>0@1$7@3$9^1^2@1$4@2$2@1$1@1$0#8^4>0@2$b@2$a@2$d@1$0#k0^3@1$4@2$2@1$1@1$0#8^5@2$c+2+k0@3$6@1$3@1$1@1$0#8@4$8^5^4^6^3@1^5^3").
Proof.
  intros bs m base a Hn Hb. unfold in_rng in Hn.
  destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned base)) as [Hlt|Hge].
  - apply wbytes_below; assumption.
  - apply wbytes_above. lia.
Qed.

Lemma frame_mod_wbytes : ltac2:(zQ "h10!h9!jc!k1!hme!qc!hn7!ht9!va!hu0!hgd!hu6!hs0!hm2!o4!oa!ht3!k4>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>4base@1$1@1$0#k0>2bs@1$7@1$1@1$0#8>0@2$e@2$d@2$h0@1$0#k0^2@1$5@2$3@1$1@1$0#8^1@2$f+2+k0@3$c^4@3$b^4^3^2@3$6@2$4@1$1@1$0#k0$2@4$a@1$1@1$0#k0$2^3@1$5@2$3@1$1@1$0#8^2@1$8@2$4@1$1@1$0#k0$2").
Proof.
  intros m base bs Hb. split.
  - intros a [Ha _]. apply wbytes_outside; assumption.
  - apply wbytes_grows.
Qed.

(* [comment removed for export] *)
Lemma frame_mod_store_ok : ltac2:(zQ "d1!h9!jc!hud!va!hgd!hv4!hh6!ij2!ije!qc!k1!in9!hm2&>0@1$1@1$0#k0@1$4@1$1@1$0#8>4segs@1$3$b>3mem~0>4mem'~0>2rs@1$3@2$9@1$1@1$0#k0$a>1a@1$1@1$0#k0>1n$8>0@3$c^5^4^3>0@3$6$2@4$7^7^6^3^2$5@3$6$2@4$7^8^6^4^3$5").
Proof. intros segs mem mem' rs a n [_ Hg] H. eapply store_ok_mono; eassumption. Qed.

Lemma frame_mod_byte : ltac2:(zQ "91!h9!jc!hgd!va!qc!hh6!k1!hm2!v0&>0@1$1@1$0#k0@1$2@1$1@1$0#8>3mem~0>4mem'~0>2rs@1$3@2$4@1$1@1$0#k0$6>1a@1$1@1$0#k0>0@3$7^4^3^2>0@2$8^2^3@3$5@1$2@1$1@1$0#8@1^5^3@1^6^3").
Proof. intros mem mem' rs a [He _] Ha. apply He, Ha. Qed.

(* [comment removed for export] *)
Lemma frame_mod_rdn : ltac2:(zQ "h41!h9!jc!va!hgd!k1!irf!o4!oa!hn7!k4!ije!qc!m6!hh6!in9!hm2!v0!of!ht3!is6&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$2$e>3mem~0>4mem'~0>2rs@1$2@2$b@1$1@1$0#k0$4>1n$a>1a@1$1@1$0#k0>0@3$f^5^4^3>0>1i$4>0@2$c@2$7Z^1@2$h1^1@1$8^4@2$h0@2$h3@1$0#k0@2$6@2$9@1$0#k0^4^2^6>0@2$7@2$6@2$9@1$0#k0^3@1$8^4@2$h2+2+k0@3$d@1$3@1$2@1$1@1$0#8@4$5^9^7^4^5@4$5^9^8^4^5").
Proof.
  intros segs mem mem' rs n. induction n as [|n IH]; intros a Hf Ho Hb; [reflexivity|].
  cbn [rdn]. pose proof (u64_range a).
  assert (Ha : mem' a = mem a).
  { pose proof (Ho 0%Z ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0.
    eapply frame_mod_byte; eassumption. }
  rewrite Ha.
  destruct n as [|n'].
  - reflexivity.
  - assert (Ha1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
    rewrite (IH (a + 1) Hf).
    + reflexivity.
    + intros i Hi. rewrite Ha1. replace (bv_unsigned a + 1 + i)%Z with (bv_unsigned a + (1 + i))%Z by lia.
      apply Ho. lia.
    + rewrite Ha1. lia.
Qed.
End FPX1.
(* [comment removed for export] *)
