(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec SeqExec StepTac MemSplit.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list03nat37Corelib7Numbers7BinNumsi34Npos35stdpp9bitvectorbdefinitionsk32bv37Corelib5Lists7ListDefm56repeatk37Z_to_bvi31Z04bool04prod03fst04andb03snd46Stdlib6ZArith6BinInt1Zqf3addqf3lebqf3ltbqf6of_nat36Stdlib5Lists4Listu27forallb79OSSVerify6Proofsaboost_jsonafuzz_parse3lib7ZStores4FPX1~~~~~~vfacovers_offvf6iota_Zu27existsb37Corelib4Init5Logichle3andu22Inqf2leqf2lt06lengthhle2eqvf5zerosm53nthk3bbv_unsigned06option04Some3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehs07Segment69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~ig06wbytes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~ik43rdnqf3pow05false04true69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7ZStores~~~~~~ip9acovers_offip96ws_inbip97zstoresqf3subhle2exip98ws_coverip95zeros" s.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition zeros : ltac2:(zQ "40!h8!he!jc!m0>1n$1@1$0@1$3@1$2#8") := ltac2:(zQ "50!jc!he!nc!o5!m0\1n$1@3$2@1$4@1$0#8@2$3@1$0#8Z^1").

Fixpoint zstores (m : word -> option byte) (d : word) (ws : list (Z * nat)) : word -> option byte :=
  match ws with
  | [] => m
  | (o, n) :: ws' => zstores (wbytes m (Z_to_bv 64 (bv_unsigned d + o)) (zeros n)) d ws'
  end.

Definition covers_off : ltac2:(zQ "40!of!p3!he!p9>1i$0>2on@2$3$0$2$1") := ltac2:(zQ "a0!of!he!pf!q4!p9!qa!s7!sd!t3!t9\1i$0\2on@2$4$0$1@2$3@2$7@3$2$0$1^1^2@2$8^2@2$6@3$2$0$1^1@1$9@3$5$0$1^1").

Definition ws_inb : ltac2:(zQ "50!of!p3!h8!he!p9>2ws@1$2@2$4$0$3>1N$0$1") := ltac2:(zQ "b0!of!he!p9!pf!sd!q4!h8!qa!v5!s7!t9\2ws@1$6@2$2$0$1\1N$0@3$8@2$2$0$1\2on@2$2$0$1@2$5@2$4Z@3$3$0$1^1@2$4@2$9@3$3$0$1^1@1$a@3$7$0$1^1^2^2").

Fixpoint iota_Z (i : Z) (k : nat) : list Z :=
  match k with O => [] | S k' => i :: iota_Z (i + 1) k' end.

Definition ws_cover : ltac2:(zQ "50!he!p3!h8!p9!of>2ws@1$2@2$3$4$0>1N$0$1") := ltac2:(zQ "80!of!he!p9!h8!hje!hkb!hl4!v5\2ws@1$3@2$2$0$1\1N$1@3$7$0\1i$0@3$6@2$2$0$1@1$4^1^3@2$5Z^1").

Lemma forallb_In : forall {A} (f : A -> bool) l x, forallb f l = true -> In x l -> f x = true.
Proof.
  induction l as [|y l IH]; intros x H Hin; [contradiction|].
  cbn in H. apply andb_true_iff in H as [Hy Hl].
  destruct Hin as [<-|Hin]; [exact Hy | apply IH; assumption].
Qed.

Lemma iota_Z_In : ltac2:(zQ "90!of!he!hn2!hkb!hn9!s7!hne!ho3!t9>1k$1>1i$0>1z$0>0@2$2@2$6^2^1@2$7^1@2$5^2@1$8^3@3$4$0^2@2$3^3^4").
Proof.
  induction k as [|k IH]; intros i z Hz; [lia|].
  cbn. destruct (Z.eq_dec i z); [left; assumption | right]. apply IH. lia.
Qed.

Lemma existsb_false_forall : forall {A} (f : A -> bool) l,
  existsb f l = false -> forall x, In x l -> f x = false.
Proof.
  induction l as [|y l IH]; intros H x Hin; [contradiction|].
  cbn in H. apply orb_false_iff in H as [Hy Hl].
  destruct Hin as [<-|Hin]; [exact Hy | apply IH; assumption].
Qed.

Lemma existsb_true_exists : forall {A} (f : A -> bool) l,
  existsb f l = true -> exists x, In x l /\ f x = true.
Proof.
  induction l as [|y l IH]; intros H; [discriminate|].
  cbn in H. apply orb_true_iff in H as [Hy|Hl].
  - exists y. split; [left; reflexivity | exact Hy].
  - destruct (IH Hl) as [x [Hin Hx]]. exists x. split; [right; exact Hin | exact Hx].
Qed.

Lemma length_zeros : ltac2:(zQ "60!he!ho8!hp0!jc!hp6!m0>1n$0@3$2$0@2$1@1$5@1$3#8@1$4^1^1").
Proof. intro n. apply repeat_length. Qed.

Lemma nth_zeros : ltac2:(zQ "70!jc!he!o5!m0!hp0!hpe!hp6>1n$1>1k$1@3$4@1$3@1$0#8@4$5@1$3@1$0#8^1@1$6^2@2$2@1$0#8Z@2$2@1$0#8Z").
Proof. intros n k. unfold zeros. apply nth_repeat. Qed.

Lemma rdn_wbytes_zeros_in : ltac2:(zQ "h10!jc!m0!hq4!h8!s7!t9!he!hr2!hp6!hne!hra!hp0!hv5!ija!inf!ho3!io6>4segs@1$3$c>1m>0@1$1@1$0#k0@1$7@1$1@1$0#8>1d@1$1@1$0#k0>1a@1$1@1$0#k0>1N$6>1n$6>0@2$f@2$4@2$2@1$0#k0^4@1$5^2@2$h0+2+k0>0@2$9@2$2@1$0#k0^5@2$2@1$0#k0^4>0@2$9@2$4@2$2@1$0#k0^5@1$5^3@2$4@2$2@1$0#k0^6@1$5^4@3$b@1$7@1$3@1$1@1$0#8@4$e^9@3$d^8^7@1$8^5^6^4@2$a@1$3@1$1@1$0#8@1$8^4").
Proof.
  intros segs m d a N n Hnw Hlo Hhi. unfold zeros at 2. apply rdn_const; [lia|].
  intros x Hx. rewrite wbytes_inside by (rewrite length_zeros; lia).
  f_equal. apply nth_zeros.
Qed.

End FPX1.

Section Cover.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable d : word.
  Variable N : Z.
  Hypothesis Hnw : ltac2:(zQ "50!jc!s7!ho3!io6!hq4@2$2@2$1@2$4@1$0#k0?1d?1N@2$3+2+k0").

  Lemma zstores_miss : ltac2:(zQ "h10!jc!m0!he!p9!hp0!of!p3!hr2!hq4!ioc!h8!ip3!it3!iu1!iub!hn9!iv6>2ws@1$a@2$3$5$2>1m>0@1$1@1$0#k0@1$7@1$1@1$0#8>1x@1$1@1$0#k0>0@3$4$6@2$d^3?1N$b>0>2on@2$3$5$2>0@3$f@2$3$5$2^1^5@3$4$6@2$c@2$h0@2$8@1$0#k0^4@2$8@1$0#k0?1d^2$9@3$4@1$7@1$1@1$0#8@4$e^4?1d^5^3@1^4^3").
  Proof.
    induction ws as [|[o n] ws IH]; intros m x Hinb Hno; [reflexivity|].
    cbn [zstores]. cbn [ws_inb forallb fst snd] in Hinb.
    apply andb_true_iff in Hinb as [Hon Hinb]. apply andb_true_iff in Hon as [Ho Hn].
    apply Z.leb_le in Ho. apply Z.leb_le in Hn.
    rewrite IH; [| exact Hinb | intros on Hin; apply Hno; right; exact Hin].
    pose proof (Hno (o, n) (or_introl eq_refl)) as Hc. cbn [covers_off fst snd] in Hc.
    pose proof (u64_range x). pose proof (u64_range d).
    apply wbytes_outside.
    - rewrite length_zeros. rewrite u_Z2bv by lia. lia.
    - rewrite length_zeros. rewrite u_Z2bv by lia.
      apply andb_false_iff in Hc as [Hc|Hc]; [apply Z.leb_gt in Hc | apply Z.ltb_ge in Hc];
        cbn [fst snd] in Hc; lia.
  Qed.

  Lemma zstores_hit : ltac2:(zQ "h40!jc!m0!he!p9!of!hp0!p3!hr2!ip3!hq4!hra!h8!hn2!ivc!it3!iu1!iub!hn9!iv6!o5>2ws@1$b@2$3$4$2>1m>0@1$1@1$0#k0@1$7@1$1@1$0#8>1x@1$1@1$0#k0>0@3$5$6@2$f^3?1N$8>0@2$d@2$3$4$2\2on@2$3$4$2@2$c@3$h1@2$3$4$2^1^5@3$5$6@2$e@2$h2@2$9@1$0#k0^3@2$9@1$0#k0?1d^1$8@3$5@1$7@1$1@1$0#8@4$h0^4?1d^5^3@2$a@1$1@1$0#8@2$h3@1$0#8Z").
  Proof.
    induction ws as [|[o n] ws IH]; intros m x Hinb Hex.
    { destruct Hex as [on [[] _]]. }
    cbn [zstores]. cbn [ws_inb forallb fst snd] in Hinb.
    apply andb_true_iff in Hinb as [Hon Hinb]. apply andb_true_iff in Hon as [Ho Hn].
    apply Z.leb_le in Ho. apply Z.leb_le in Hn.
    destruct (existsb (covers_off (bv_unsigned x - bv_unsigned d)) ws) eqn:E.
    - apply IH; [exact Hinb|]. apply existsb_true_exists. exact E.
    - rewrite zstores_miss; [| exact Hinb | apply existsb_false_forall; exact E].
      destruct Hex as [on [[<-|Hin] Hc]].
      2:{ rewrite (existsb_false_forall _ _ E on Hin) in Hc. discriminate. }
      cbn [covers_off fst snd] in Hc. apply andb_true_iff in Hc as [Hc1 Hc2].
      apply Z.leb_le in Hc1. apply Z.ltb_lt in Hc2. cbn [fst snd] in Hc1, Hc2.
      pose proof (u64_range x). pose proof (u64_range d).
      rewrite wbytes_inside by (rewrite length_zeros, u_Z2bv by lia; lia).
      f_equal. apply nth_zeros.
  Qed.

  Lemma zstores_cover : ltac2:(zQ "h01!hp0!jc!m0!p3!he!hr2!ip3!of!h8!p9!ija!jg2!iu1!jge!iub!t9&>0@1$2@1$1#k0@1$5@1$2@1$1#8>2ws@1$8@2$9$7$4>1m~0>1n$4>0@3$0$7@1$f^1?1N>0@3$0$3@2$c^4?1N$6>0@3$0$3@2$b^5^3$6@3$0~0@3$e^5?1d^6@3$a^5?1d@1$d^4").
  Proof.
    intros ws m n HnN Hinb Hcov. apply functional_extensionality. intro x.
    pose proof (u64_range x). pose proof (u64_range d).
    destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned d)) as [Hlt|Hge].
    { rewrite wbytes_outside by (rewrite length_zeros; lia).
      apply zstores_miss; [exact Hinb|]. intros [o k] Hin.
      pose proof (forallb_In _ _ _ Hinb Hin) as Hb. cbn [fst snd] in Hb.
      apply andb_true_iff in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1.
      cbn [covers_off fst snd]. apply andb_false_iff. left. apply Z.leb_gt. cbn [fst snd]. lia. }
    destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned d + N)) as [Hin|Hout].
    - rewrite wbytes_inside by (rewrite length_zeros; lia). rewrite nth_zeros.
      apply zstores_hit; [exact Hinb|].
      pose proof (forallb_In _ _ _ Hcov (iota_Z_In n 0 (bv_unsigned x - bv_unsigned d) ltac:(lia))) as He.
      apply existsb_true_exists in He. exact He.
    - rewrite wbytes_outside by (rewrite length_zeros; lia).
      apply zstores_miss; [exact Hinb|]. intros [o k] Hin'.
      pose proof (forallb_In _ _ _ Hinb Hin') as Hb. cbn [fst snd] in Hb.
      apply andb_true_iff in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb2.
      cbn [covers_off fst snd]. apply andb_false_iff. right. apply Z.ltb_ge. cbn [fst snd]. lia.
  Qed.
End Cover.
(* [comment removed for export] *)
