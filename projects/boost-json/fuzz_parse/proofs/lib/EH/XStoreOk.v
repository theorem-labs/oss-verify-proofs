(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics StackLayout State Run.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Footprint.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk16optionk14None37Corelib4Init5Logicm92eqm93not79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8XStoreOk~~~~~~o89mem_grows3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticst25wviewk14list3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehh87Segmentk14boolk14truet28store_okk13nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8XCatExec~~~~~~hn76wbyteshfbbv_unsigned46Stdlib6ZArith6BinInt1Zhsd3addhsd2lehsd6of_natm93andhsd2lthsd3pow" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition mem_grows : ltac2:(zQ "31!h9!jc!l9&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1m~0>2m'~0P") := ltac2:(zQ "61!h9!jc!l9!m2!nd!o2&>0@1$1@1$0#k0@1$2@1$1@1$0#8\1m~0\2m'~0>1x@1$1@1$0#k0>0@1$5@3$4@1$2@1$1@1$0#8@1^3^1@1$3@1$1@1$0#8@1$5@3$4@1$2@1$1@1$0#8@1^3^2@1$3@1$1@1$0#8").

Lemma mem_grows_refl : ltac2:(zQ "40!h9!jc!l9!s6>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8@2$3^1^1").
Proof. intros m x H. exact H. Qed.

Lemma mem_grows_trans : ltac2:(zQ "41!h9!jc!l9!s6&>0@1$1@1$0#k0@1$2@1$1@1$0#8>2m1~0>2m2~0>2m3~0>0@2$3^3^2>0@2$3^3^2@2$3^5^3").
Proof. intros m1 m2 m3 H12 H23 x Hx. apply H23, H12, Hx. Qed.

(* [comment removed for export] *)
Lemma wview_grows : ltac2:(zQ "a1!h9!jc!l9!m2!nd!o2!hg9!hh1!hkd!s6&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$7$8>1m~0>2m'~0>1x@1$1@1$0#k0>0@2$9^3^2>0@1$5@3$4@1$2@1$1@1$0#8@3$6^5^4^2@1$3@1$1@1$0#8@1$5@3$4@1$2@1$1@1$0#8@3$6^6^4^3@1$3@1$1@1$0#8").
Proof.
  intros segs m m' x Hg Hx. unfold wview in *.
  destruct (m' x) as [b'|] eqn:Hm'; [discriminate|].
  destruct (m x) as [b|] eqn:Hm.
  - exfalso. apply (Hg x); [rewrite Hm; discriminate|exact Hm'].
  - exact Hx.
Qed.

Lemma store_ok_mono : ltac2:(zQ "b1!h9!jc!hl8!l9!hlf!nd!hm6!hh1!hn1!hkd!s6&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$7$9>1n$8>1m~0>2m'~0>1a@1$1@1$0#k0>0@2$a^3^2>0@3$5$2@4$6^6^4^2^5$4@3$5$2@4$6^7^4^3^6$4").
Proof.
  intros segs n; induction n as [|n IH]; intros m m' a Hg H; [reflexivity|].
  cbn [store_ok] in *.
  destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
  destruct (wview segs m' a) as [b'|] eqn:Hv'.
  - apply (IH m m'); assumption.
  - exfalso. apply (wview_grows segs m m' a Hg); [rewrite Hv; discriminate|exact Hv'].
Qed.

(* [comment removed for export] *)

Lemma wbytes_grows : ltac2:(zQ "60!h9!jc!hh1!l9!hr5!s6>2bs@1$2@1$1@1$0#8>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1a@1$1@1$0#k0@2$5^2@3$4^2^1^3").
Proof.
  induction bs as [|b rest IH]; intros m a x Hx; [exact Hx|].
  cbn [wbytes]. apply IH.
  destruct (bv_eqb x a); [discriminate|exact Hx].
Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma store_ok_of_all : ltac2:(zQ "h40!h9!jc!hrf!l9!nd!hu5!huc!hv2!m2!hl8!hh1!hn1!hlf!hvc!o2!hkd!hm6!hg9!ig2!ig8>4segs@1$a$f>1n$b>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1a@1$1@1$0#k0>0@2$6@2$5@2$2@1$0#k0^1@1$7^3@2$h3+2+k0>0>1x@1$1@1$0#k0>0@2$d@2$6@2$2@1$0#k0^3@2$2@1$0#k0^1@2$h2@2$2@1$0#k0^1@2$5@2$2@1$0#k0^3@1$7^5@1$e@3$4@1$3@1$1@1$0#8@3$h1^7^5^2@1$8@1$1@1$0#8@3$4$9@4$h0^6^4^3^5$c").
Proof.
  intros segs n; induction n as [|n IH]; intros m a Hnw Hall; [reflexivity|].
  cbn [store_ok].
  destruct (wview segs m a) as [b|] eqn:Hv.
  2: { exfalso. refine (Hall a _ Hv). rewrite Nat2Z.inj_succ. lia. }
  (* [comment removed for export] *)
  destruct n as [|n']; [reflexivity|].
  rewrite Nat2Z.inj_succ in Hnw.
  assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1)
    by (apply u_add1; rewrite Nat2Z.inj_succ in Hnw; lia).
  apply IH.
  - rewrite Hu1. lia.
  - intros x Hx. rewrite Hu1 in Hx. apply Hall.
    rewrite Nat2Z.inj_succ. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma store_ok_all : ltac2:(zQ "h40!h9!jc!hrf!l9!nd!hu5!huc!hv2!m2!hl8!hh1!hn1!hlf!hvc!o2!hkd!hm6!hg9!ig2!ig8>4segs@1$a$f>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1n$b>1a@1$1@1$0#k0>0@2$6@2$5@2$2@1$0#k0^1@1$7^2@2$h3+2+k0>0@3$4$9@4$h0^5^4^2^3$c>1x@1$1@1$0#k0>0@2$d@2$6@2$2@1$0#k0^4@2$2@1$0#k0^1@2$h2@2$2@1$0#k0^1@2$5@2$2@1$0#k0^4@1$7^5@1$e@3$4@1$3@1$1@1$0#8@3$h1^8^7^2@1$8@1$1@1$0#8").
Proof.
  intros segs m n; induction n as [|n IH]; intros a Hnw H x Hx;
    [cbn in Hx; lia|].
  cbn [store_ok] in H.
  destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
  rewrite Nat2Z.inj_succ in Hnw, Hx.
  destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
  { assert (x = a) by (apply bv_eq; exact Heq). subst x.
    rewrite Hv. discriminate. }
  (* [comment removed for export] *)
  assert (Hn : (1 <= Z.of_nat n)%Z) by lia.
  assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; lia).
  (* [comment removed for export] *)
  eapply IH; [ | exact H | ]; lia.
Qed.

Lemma store_ok_sub : ltac2:(zQ "f0!h9!hrf!jc!hu5!huc!hv2!hl8!hn1!hlf!nd!hm6!hh1!l9!hkd!ig8>4segs@1$b$d>1m>0@1$2@1$0#k0@1$c@1$2@1$0#8>2lo@1$2@1$0#k0>1a@1$2@1$0#k0>1N$7>1n$7>0@2$4@2$3@2$1@1$0#k0^4@1$5^2@2$e+2+k0>0@3$9$6@4$a^7^6^5^3$8>0@2$4@2$1@1$0#k0^6@2$1@1$0#k0^5>0@2$4@2$3@2$1@1$0#k0^6@1$5^4@2$3@2$1@1$0#k0^7@1$5^5@3$9$6@4$a^a^9^7^5$8").
Proof.
  intros segs m lo a N n Hnw Hok Hl Hh.
  apply store_ok_of_all; [lia|].
  intros x Hx. apply (store_ok_all segs m N lo Hnw Hok). lia.
Qed.
(* [comment removed for export] *)
