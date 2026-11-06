(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics StackLayout State Run.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec StepTac StreamSim AllocSim Footprint.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk16optionk14None37Corelib4Init5Logicm92eqm93not79OSSVerify6Proofsaboost_jsonafuzz_parse3lib7StoreOk4FPX1~~~~~~o89mem_grows3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticst35wviewk14list3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehh97Segmentk14boolk14truet38store_okk13nat69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~hn86wbytesk14prod3h5LinuxProcessSemanticsfLinuxProcessSem3Runhs3bapply_zerost3cwrite_to_memhs3capply_writeshfbbv_unsigned46Stdlib6ZArith6BinInt1Ziib3addiib2leiib6of_natm93andiib2ltiib3pow69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9StreamSim~~~~~~imd7wseg_ok01Zk14Somem92ex3h5LinuxProcessSemanticsfLinuxProcessSem5Stateis3eread_bytes_aux" s.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition mem_grows : ltac2:(zQ "31!h9!jc!l9&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1m~0>2m'~0P") := ltac2:(zQ "61!h9!jc!l9!m2!nd!o2&>0@1$1@1$0#k0@1$2@1$1@1$0#8\1m~0\2m'~0>1x@1$1@1$0#k0>0@1$5@3$4@1$2@1$1@1$0#8@1^3^1@1$3@1$1@1$0#8@1$5@3$4@1$2@1$1@1$0#8@1^3^2@1$3@1$1@1$0#8").

Lemma mem_grows_refl : ltac2:(zQ "40!h9!jc!l9!s7>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8@2$3^1^1").
Proof. intros m x H. exact H. Qed.

Lemma mem_grows_trans : ltac2:(zQ "41!h9!jc!l9!s7&>0@1$1@1$0#k0@1$2@1$1@1$0#8>2m1~0>2m2~0>2m3~0>0@2$3^3^2>0@2$3^3^2@2$3^5^3").
Proof. intros m1 m2 m3 H12 H23 x Hx. apply H23, H12, Hx. Qed.

(* [comment removed for export] *)
Lemma wview_grows : ltac2:(zQ "a1!h9!jc!l9!m2!nd!o2!hga!hh2!hke!s7&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$7$8>1m~0>2m'~0>1x@1$1@1$0#k0>0@2$9^3^2>0@1$5@3$4@1$2@1$1@1$0#8@3$6^5^4^2@1$3@1$1@1$0#8@1$5@3$4@1$2@1$1@1$0#8@3$6^6^4^3@1$3@1$1@1$0#8").
Proof.
  intros segs m m' x Hg Hx. unfold wview in *.
  destruct (m' x) as [b'|] eqn:Hm'; [discriminate|].
  destruct (m x) as [b|] eqn:Hm.
  - exfalso. apply (Hg x); [rewrite Hm; discriminate|exact Hm'].
  - exact Hx.
Qed.

Lemma store_ok_mono : ltac2:(zQ "b1!h9!jc!hl9!l9!hm0!nd!hm7!hh2!hn2!hke!s7&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$7$9>1n$8>1m~0>2m'~0>1a@1$1@1$0#k0>0@2$a^3^2>0@3$5$2@4$6^6^4^2^5$4@3$5$2@4$6^7^4^3^6$4").
Proof.
  intros segs n; induction n as [|n IH]; intros m m' a Hg H; [reflexivity|].
  cbn [store_ok] in *.
  destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
  destruct (wview segs m' a) as [b'|] eqn:Hv'.
  - apply (IH m m'); assumption.
  - exfalso. apply (wview_grows segs m m' a Hg); [rewrite Hv; discriminate|exact Hv'].
Qed.

(* [comment removed for export] *)

Lemma wbytes_grows : ltac2:(zQ "60!h9!jc!hh2!l9!hr2!s7>2bs@1$2@1$1@1$0#8>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1a@1$1@1$0#k0@2$5^2@3$4^2^1^3").
Proof.
  induction bs as [|b rest IH]; intros m a x Hx; [exact Hx|].
  cbn [wbytes]. apply IH.
  destruct (bv_eqb x a); [discriminate|exact Hx].
Qed.

Lemma apply_zeros_grows : ltac2:(zQ "70!h9!jc!hh2!l9!hrc!huf!s7>2zs@1$2@2$4@1$1@1$0#k0@1$1@1$0#k0>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8@2$6^1@2$5^1^2").
Proof.
  intros zs m x Hx. unfold apply_zeros.
  destruct zs as [|z zs']; [exact Hx|].
  destruct (zeros_cover (z :: zs') x); [discriminate|exact Hx].
Qed.

Lemma write_to_mem_grows : ltac2:(zQ "60!h9!jc!hh2!l9!hve!s7>2bs@1$2@1$1@1$0#8>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1a@1$1@1$0#k0@2$5^2@3$4^2^1^3").
Proof.
  induction bs as [|b rest IH]; intros m a x Hx; [exact Hx|].
  cbn [write_to_mem]. apply IH.
  destruct (bv_eqb x a); [discriminate|exact Hx].
Qed.

Lemma apply_writes_grows : ltac2:(zQ "70!h9!jc!hh2!l9!hrc!igd!s7>2ws@1$2@2$4@1$1@1$0#k0@1$2@1$1@1$0#8>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8@2$6^1@2$5^1^2").
Proof.
  induction ws as [|w ws' IH]; intros m x Hx.
  - exact Hx.
  - destruct w as [a bs]. cbn [apply_writes].
    apply IH. apply write_to_mem_grows. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma store_ok_of_all : ltac2:(zQ "h40!h9!jc!ihd!l9!nd!ik3!ika!il0!m2!hl9!hh2!hn2!hm0!ila!o2!hke!hm7!hga!im0!im6>4segs@1$a$f>1n$b>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1a@1$1@1$0#k0>0@2$6@2$5@2$2@1$0#k0^1@1$7^3@2$h3+2+k0>0>1x@1$1@1$0#k0>0@2$d@2$6@2$2@1$0#k0^3@2$2@1$0#k0^1@2$h2@2$2@1$0#k0^1@2$5@2$2@1$0#k0^3@1$7^5@1$e@3$4@1$3@1$1@1$0#8@3$h1^7^5^2@1$8@1$1@1$0#8@3$4$9@4$h0^6^4^3^5$c").
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

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma store_ok_wseg : ltac2:(zQ "b0!h9!jc!hl9!hm0!nd!hh2!hn2!l9!hke!hm7!iq9>4segs@1$5$8>1m>0@1$1@1$0#k0@1$7@1$1@1$0#8>1a@1$1@1$0#k0>1n$6>0@3$4$2@3$a^4^2^1$3@3$4$2@4$9^5^4^3^2$3").
Proof.
  intros segs m a n; revert a m; induction n as [|n IH]; intros a m H; [reflexivity|].
  cbn [wseg_ok] in H.
  destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:Hseg; [|discriminate].
  apply andb_true_iff in H as [H Hrec].
  apply andb_true_iff in H as [Hwr Hbyte].
  destruct (segment_byte_at (seg_bytes seg)
              (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))) as [b|] eqn:Hb;
    [|discriminate].
  cbn [store_ok]. unfold wview at 1.
  destruct (m a) as [b0|]; [apply IH, Hrec|].
  rewrite Hseg, Hwr, Hb. apply IH, Hrec.
Qed.

(* [comment removed for export] *)
Lemma store_ok_all : ltac2:(zQ "h40!h9!jc!ihd!l9!nd!ik3!ika!il0!m2!hl9!hh2!hn2!hm0!ila!o2!hke!hm7!hga!im0!im6>4segs@1$a$f>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1n$b>1a@1$1@1$0#k0>0@2$6@2$5@2$2@1$0#k0^1@1$7^2@2$h3+2+k0>0@3$4$9@4$h0^5^4^2^3$c>1x@1$1@1$0#k0>0@2$d@2$6@2$2@1$0#k0^4@2$2@1$0#k0^1@2$h2@2$2@1$0#k0^1@2$5@2$2@1$0#k0^4@1$7^5@1$e@3$4@1$3@1$1@1$0#8@3$h1^8^7^2@1$8@1$1@1$0#8").
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

Lemma store_ok_sub : ltac2:(zQ "f0!h9!ihd!jc!ik3!ika!il0!hl9!hn2!hm0!nd!hm7!hh2!l9!hke!im6>4segs@1$b$d>1m>0@1$2@1$0#k0@1$c@1$2@1$0#8>2lo@1$2@1$0#k0>1a@1$2@1$0#k0>1N$7>1n$7>0@2$4@2$3@2$1@1$0#k0^4@1$5^2@2$e+2+k0>0@3$9$6@4$a^7^6^5^3$8>0@2$4@2$1@1$0#k0^6@2$1@1$0#k0^5>0@2$4@2$3@2$1@1$0#k0^6@1$5^4@2$3@2$1@1$0#k0^7@1$5^5@3$9$6@4$a^a^9^7^5$8").
Proof.
  intros segs m lo a N n Hnw Hok Hl Hh.
  apply store_ok_of_all; [lia|].
  intros x Hx. apply (store_ok_all segs m N lo Hnw Hok). lia.
Qed.

(* [comment removed for export] *)
Lemma store_ok_window : ltac2:(zQ "h10!h9!nd!ir4!jc!ika!ihd!hl9!hn2!hm0!ik3!il0!hh2!l9!hke!hm7!iq9!im6>4segs@1$b$d>1m>0@1$3@1$0#k0@1$c@1$3@1$0#8>2lo@1$3@1$0#k0>1a@1$3@1$0#k0>1N$7>1n$7>4base$2>2hi$2>0@3$1$2@2$5@1$0#k0^6^2>0@3$1$2@2$9^3@1$a^5^2>0@2$4^3@2$h0+2+k0>0@3$1$6@3$f^b^9^7$8>0@2$4^6@2$5@1$0#k0^9>0@2$4@2$9@2$5@1$0#k0^a@1$a^8^6@3$1$6@4$e^e^d^b^9$8").
Proof.
  intros segs m lo a N n base hi Hbase Htop Hnw Hw Hl Hh.
  eapply store_ok_sub; [ | apply store_ok_wseg, Hw | | ]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma store_ok_read_aux : ltac2:(zQ "e0!h9!jc!hh2!l9!nd!ir7!hl9!hn2!hm0!ire!hke!hm7!hga!iv1>4segs@1$2$a>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1n$7>1a@1$1@1$0#k0>0@3$4$6@4$b^4^3^1^2$8@2$9@1$2@1$1@1$0#8\1w@1$2@1$1@1$0#8@3$4@1$3@1$2@1$1@1$0#8@3$d@2$c^6^5^3^4@2$5@1$2@1$1@1$0#8^1").
Proof.
  intros segs m n; induction n as [|n IH]; intros a H.
  - exists []. reflexivity.
  - cbn [store_ok] in H. cbn [read_bytes_aux].
    destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
    destruct (IH (a + 1)%bv H) as [w Hw]. rewrite Hw. exists (b :: w). reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
End FPX1.

(* [comment removed for export] *)
Ltac store_ok_peel :=
  repeat first
    [ eapply store_ok_mono; [apply wbytes_grows|]
    | eapply store_ok_mono; [apply write_to_mem_grows|]
    | eapply store_ok_mono; [apply apply_zeros_grows|]
    | eapply store_ok_mono; [apply apply_writes_grows|] ].

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Create HintDb store_ok_db.

(* [comment removed for export] *)
(* [comment removed for export] *)
