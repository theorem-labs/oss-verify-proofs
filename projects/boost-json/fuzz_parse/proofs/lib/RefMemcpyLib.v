(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14listk14consk16lengthk13natk13nil37Corelib4Init5Logicnc2eq37Corelib4Init5Peanop52lt37Corelib5Lists7ListDefqe3nth79OSSVerify6Proofsaboost_jsonafuzz_parse3libcRefMemcpyLib4FPX1~~~~~~sb3subhf7Z_to_bv69OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Hoare~~~~~~hhf3at_nc1I01Z46Stdlib6ZArith6BinInt1Zhm53addhf2BVhf4BvWfhf6bv_addhfbbv_unsignedhm52lehm52lthm53pow69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~hra6wbytesk16optionk13apphm56of_natqe6firstnnc2or37Corelib4Init3Natii53addp52lek14Some69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~ika3rdnii53subqe5skipn3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeipb7Segment3h5LinuxProcessSemanticsfLinuxProcessSem6BvBaseitbdbytes_le_to_Zika4v_lwnc3andhm53mulhm57testbitk14bool79OSSVerify6Proofsaboost_jsonafuzz_parse3libcRefMemcpyLib4FPX2~~~~~~jk23LWvhm53lorhm56shiftlk15falsehm53ltbhm53subitbdZ_to_le_bytes3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsjs5h0word_to_le_bytesjk23LBvika6v_srliika7v_srliwika6v_sllik13orbika4v_ork14truejs58store_ok3h5LinuxProcessSemantics5Riscv7Preludekl85bvmapika4getrjk2bcallee_kept36Stdlib5Lists4Listkpe2Injk25keepsnc3notika6regupdk14negbkl86bv_eqbkpe7forallbnc2exjs5dmachine_state69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6CatSim~~~~~~lg26msteps79OSSVerify6Proofsaboost_jsonafuzz_parse3libcRefMemcpyLib4FPX4~~~~~~lk5ccallee_savedlk58keeps_cs69OSSVerify6Proofsaboost_jsonafuzz_parse3libcRefMemcpyLib~~~~~~lq55keeps" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition sub {A} (bs : list A) (j k : nat) : list A := firstn k (skipn j bs).

Lemma firstn_add : forall {A} (l : list A) a b,
  firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
Proof.
  intros A l a. revert l. induction a as [|a IH]; intros l b.
  - cbn. reflexivity.
  - destruct l as [|x l]; cbn.
    + destruct b; reflexivity.
    + rewrite IH. reflexivity.
Qed.

Lemma firstn_sub_app : forall {A} (bs : list A) j k,
  firstn j bs ++ sub bs j k = firstn (j + k) bs.
Proof. intros. unfold sub. rewrite firstn_add. reflexivity. Qed.

Lemma skipn_add : forall {A} (l : list A) a b, skipn (a + b) l = skipn b (skipn a l).
Proof.
  intros A l a. revert l. induction a as [|a IH]; intros l b; [reflexivity|].
  destruct l as [|x l]; cbn; [destruct b; reflexivity|]. apply IH.
Qed.

Lemma sub_length : forall {A} (bs : list A) j k,
  (j + k <= length bs)%nat -> length (sub bs j k) = k.
Proof.
  intros A bs j k H. unfold sub. rewrite length_firstn, length_skipn. lia.
Qed.

Lemma sub_split : forall {A} (bs : list A) j a b,
  sub bs j (a + b) = sub bs j a ++ sub bs (j + a) b.
Proof.
  intros A bs j a b. unfold sub. rewrite firstn_add. f_equal.
  rewrite <- skipn_add. f_equal; lia.
Qed.

Lemma sub_nth : ltac2:(zQ "c0!h9!jc!l9!m0!m7!n0!n6!p0!q9!s5!hgf!hh5>2bs@1$2@1$1@1$0#8>1j$5>0@2$8^1@2$4@1$1@1$0#8^2@3$7@1$2@1$1@1$0#8@4$a@1$1@1$0#8^3^2N1@3$3@1$1@1$0#8@4$9@1$1@1$0#8^2^3@2$b@1$0#8Z@1$6@1$1@1$0#8").
Proof.
  intros bs j. revert bs. induction j as [|j IH]; intros bs H.
  - destruct bs; cbn in *; [lia|reflexivity].
  - destruct bs; cbn in *; [lia|]. unfold sub in IH. apply IH. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma at_succ : ltac2:(zQ "a0!h9!hl7!jc!hle!p0!hm2!hnd!ho4!ho9!hp0>1a@1$2@1$0#k0>1d$5@3$4@1$2@1$0#k0@3$9@1$0#k0@2$1^2^1@3$7@1$0#k0+1Kv$3@2$8@1$0#k0+1@2$1^2@2$6^1+1").
Proof.
  intros a d. unfold at_. apply bv_eq.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_unsigned (1 : word)) with 1.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma word_succ_at : ltac2:(zQ "80!h9!jc!hle!p0!hl7!ho4!ho9!hp0>1a@1$1@1$0#k0@3$3@1$1@1$0#k0@3$7@1$0#k0^1@3$5@1$0#k0+1Kv$2@2$6@1$0#k0+1@2$4^1+1").
Proof. intros a. rewrite <- (at_0 a) at 1. rewrite at_succ. reflexivity. Qed.

Lemma at_u : ltac2:(zQ "a0!h9!hp9!hnd!hm2!p0!hl7!hq7!hqd!hr3!jc>1a@1$9@1$0#k0>1d$3>0@2$6Z@2$2@2$1@1$0#k0^2^1>0@2$7@2$2@2$1@1$0#k0^3^2@2$8+2+k0@3$4$3@2$1@1$0#k0@2$5^4^3@2$2@2$1@1$0#k0^4^3").
Proof. intros a d H1 H2. unfold at_. apply u_Z2bv; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wbytes_app : ltac2:(zQ "a1!h9!jc!hv4!l9!hve!ig7!m7!p0!hl7!igd&>0@1$1@1$0#k0@1$4@1$1@1$0#8>3bs1@1$3@1$1@1$0#8>3bs2@1$3@1$1@1$0#8>1m~0>1a@1$1@1$0#k0@3$7~0@3$2^2^1@3$5@1$1@1$0#8^4^3@3$2@3$2^2^1^4@2$8^1@1$9@2$6@1$1@1$0#8^4^3").
Proof.
  induction bs1 as [|b r IH]; intros bs2 m a.
  - cbn [app wbytes length Z.of_nat]. rewrite at_0. reflexivity.
  - cbn [app wbytes length]. rewrite IH. f_equal.
    rewrite word_succ_at, at_at. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma wbytes_extend : ltac2:(zQ "f1!h9!jc!hv4!n0!hve!ih7!m7!l9!p0!ii0!ij7!q9!hl7!hgf!igd&>0@1$1@1$0#k0@1$4@1$1@1$0#8>1m~0>3dst@1$1@1$0#k0>2bs@1$7@1$1@1$0#8>1j$3>1k$3@2$9@3$8~0@3$2@3$2^5^4@3$5@1$1@1$0#8^2^3@2$c^4@1$e^2@4$d@1$1@1$0#8^3^2^1@3$2^5^4@3$5@1$1@1$0#8@2$a^2^1^3@2$b@2$6@1$1@1$0#8^3^2").
Proof.
  intros m dst bs j k.
  destruct (Nat.le_gt_cases j (length bs)) as [H|H]; [left|right; exact H].
  rewrite <- firstn_sub_app, wbytes_app. rewrite length_firstn. f_equal. f_equal. f_equal. lia.
Qed.

Lemma wbytes_extend' : ltac2:(zQ "e1!h9!jc!hv4!n0!hve!ih7!m7!l9!p0!ij7!ije!hl7!hgf!igd&>0@1$1@1$0#k0@1$4@1$1@1$0#8>1m~0>3dst@1$1@1$0#k0>2bs@1$7@1$1@1$0#8>1j$3>1k$3>0@2$a^2@2$6@1$1@1$0#8^3@3$8~0@3$2@3$2^6^5@3$5@1$1@1$0#8^3^4@2$b^5@1$d^3@4$c@1$1@1$0#8^4^3^2@3$2^6^5@3$5@1$1@1$0#8@2$9^3^2^4").
Proof.
  intros m dst bs j k H. destruct (wbytes_extend m dst bs j k) as [E|E]; [exact E|lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_skipn : ltac2:(zQ "e0!h9!jc!l9!hve!ik3!n0!p0!io5!ioc!ije!ip3!it0!hl7!igd>4segs@1$2$b>3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8>1n$5>1a@1$1@1$0#k0>2bs@1$2@1$1@1$0#8>1j$5>0@3$6@1$3@1$2@1$1@1$0#8@4$7^6^5^3^4@2$4@1$2@1$1@1$0#8^2>0@2$9^2^5@3$6@1$3@1$2@1$1@1$0#8@4$7^8^7@2$c^5@1$d^3@2$8^6^3@2$4@1$2@1$1@1$0#8@3$a@1$1@1$0#8^3^4").
Proof.
  intros segs mem n. induction n as [|n IH]; intros a bs j H Hj.
  - assert (j = 0)%nat by lia. subst j. cbn in H. injection H as <-.
    rewrite at_0. reflexivity.
  - cbn [rdn] in H.
    destruct (match mem a with Some b => Some b | None => seg_rom segs a end) as [b|] eqn:Eb; [|discriminate].
    destruct (rdn segs mem (a+1)%bv n) as [rest|] eqn:Er; [|discriminate].
    injection H as <-.
    destruct j as [|j].
    + rewrite at_0. cbn [Nat.sub skipn rdn]. rewrite Eb, Er. reflexivity.
    + cbn [skipn]. replace (S n - S j)%nat with (n - j)%nat by lia.
      replace (at_ a (Z.of_nat (S j))) with (at_ (a + 1)%bv (Z.of_nat j))
        by (rewrite word_succ_at, at_at; f_equal; lia).
      apply IH; [exact Er|lia].
Qed.

Lemma rdn_sub : ltac2:(zQ "e0!h9!jc!l9!n0!hve!ik3!p0!io5!ij7!ije!it0!hl7!hgf!igd>4segs@1$2$a>3mem>0@1$1@1$0#k0@1$4@1$1@1$0#8>1n$3>1a@1$1@1$0#k0>2bs@1$2@1$1@1$0#8>1j$3>1k$3>0@3$6@1$4@1$2@1$1@1$0#8@4$7^7^6^4^5@2$5@1$2@1$1@1$0#8^3>0@2$9@2$8^3^2^6@3$6@1$4@1$2@1$1@1$0#8@4$7^9^8@2$b^6@1$d^4^3@2$5@1$2@1$1@1$0#8@4$c@1$1@1$0#8^5^4^3").
Proof.
  intros segs mem n a bs j k H Hjk. unfold sub.
  apply (rdn_firstn segs mem (n - j)); [|lia].
  apply rdn_skipn; [exact H|lia].
Qed.
End FPX1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Abbreviation lez := bytes_le_to_Z.

(* [comment removed for export] *)
Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition LWv : ltac2:(zQ "30!h9!jc!l9>1l@1$2@1$1@1$0#8@1$1@1$0#k0") := ltac2:(zQ "60!h9!l9!jga!jhb!hh5!jc\1l@1$1@1$5@1$0#8@1$3@2$4@1$0#k0@1$2^1").

Lemma lez_bound_len : ltac2:(zQ "d0!n0!h9!jga!jc!m7!l9!ji3!p0!hq7!hqd!ji9!igd!hr3>2bs@1$5@1$3@1$1#8>1k$0>0@3$7$0@2$4@1$3@1$1#8^2^1@2$6@2$8Z@1$2^3@2$9@1$2^3@2$c+2@2$a+8@1$b^2").
Proof. intros bs k <-. split; [apply bytes_le_to_Z_nonneg | apply bytes_le_to_Z_bound]. Qed.
Lemma lez4_range : ltac2:(zQ "b0!h9!jga!jc!m7!l9!n0!ji3!p0!hq7!hqd!hr3>1l@1$4@1$2@1$0#8>0@3$7$5@2$3@1$2@1$0#8^1N4@2$6@2$8Z@1$1^2@2$9@1$1^2@2$a+2+i0").
Proof. intros l H. pose proof (lez_bound_len l 4%nat H). change (8 * Z.of_nat 4) with 32 in H0. lia. Qed.
Lemma u_lez4 : ltac2:(zQ "a0!h9!p0!jga!jc!m7!l9!n0!hm2!hh5!hp9>1l@1$5@1$3@1$0#8>0@3$1$6@2$4@1$3@1$0#8^1N4@3$1$7@2$9@1$0#k0@2$8@1$0#k0@1$2^2@1$2^2").
Proof. intros l H. pose proof (lez4_range l H). apply u_Z2bv; lia. Qed.

Lemma testbit_u_LWv : ltac2:(zQ "f0!h9!p0!jj0!jc!jjb!m7!l9!n0!ji3!hm2!jga!jo6!hq7!hqd!hp9>1l@1$6@1$3@1$0#8>1i$9>0@3$1$7@2$5@1$3@1$0#8^2N4>0@2$8@2$cZ^2@2$d^2+i0@3$1$4@2$2@2$e@1$0#k0@1$b^4^3@2$2@1$a^4^3").
Proof.
  intros l i H Hi. unfold LWv, v_lw. rewrite Z_to_bv_unsigned, u_lez4 by exact H.
  rewrite bv_wrap_spec_low by lia.
  rewrite bv_swrap_spec by lia.
  case_bool_decide; [reflexivity|].
  replace i with 31 by lia. reflexivity.
Qed.

Lemma lez_cons : ltac2:(zQ "a0!h9!jc!jga!m0!l9!p0!hm2!jod!jp4!hp9>1b@1$1@1$0#8>2bs@1$4@1$1@1$0#8@3$5$6@1$2@3$3@1$1@1$0#8^2^1@2$7@2$9@1$0#8^2@2$8@1$2^1+8").
Proof. reflexivity. Qed.

Lemma testbit_lez_high : ltac2:(zQ "d0!h9!jc!jjb!jpe!m7!l9!p0!hm2!jga!hq7!ji9!igd!jj0>2bs@1$5@1$1@1$0#8>1i$7>0@2$9@2$a+8@1$b@2$4@1$1@1$0#8^2^1@3$6$2@2$c@1$8^3^2$3").
Proof.
  intros bs i Hi. apply (Z_testbit_high (8 * Z.of_nat (length bs))); try lia.
  apply lez_bound_len. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma testbit_lez_skipn : ltac2:(zQ "e0!h9!jga!jj0!jc!jjb!l9!n0!p0!ip3!hm2!hnd!hq7!ji9!igd>1q$6>2bs@1$5@1$3@1$0#8>1i$9>0@2$bZ^1@3$7$4@2$2@1$1@3$8@1$3@1$0#8^4^3^2@2$2@1$1^3@2$a^2@2$c+8@1$d^4").
Proof.
  induction q as [|q IH]; intros bs i Hi.
  - cbn [skipn]. f_equal. lia.
  - destruct bs as [|b bs].
    + cbn [skipn lez]. rewrite !Z.bits_0. reflexivity.
    + cbn [skipn]. rewrite IH by lia. rewrite lez_cons.
      rewrite Z.lor_spec, Z.shiftl_spec by lia.
      pose proof (u8_range b).
      rewrite (Z_testbit_high 8 (bv_unsigned b)) by lia. cbn [orb]. f_equal. lia.
Qed.

Lemma testbit_lez_firstn : ltac2:(zQ "f0!jjb!h9!jga!jj0!jc!jpe!l9!n0!p0!ih7!hm2!hq7!jq6!ji9!igd>1q$7>2bs@1$6@1$4@1$1#8>1i$a>0@2$bZ^1@3$8$0@2$3@1$2@3$9@1$4@1$1#8^4^3^2M0\0$0$0@2$c^2@2$d+8@1$e^4@2$3@1$2^3^2$5").
Proof.
  induction q as [|q IH]; intros bs i Hi.
  - cbn [firstn lez]. rewrite Z.bits_0. destruct (Z.ltb_spec i (8 * Z.of_nat 0)); [lia|reflexivity].
  - destruct bs as [|b bs].
    + cbn [firstn lez]. rewrite !Z.bits_0. destruct (i <? _); reflexivity.
    + cbn [firstn]. rewrite !lez_cons, !Z.lor_spec, !Z.shiftl_spec by lia.
      destruct (Z.lt_ge_cases i 8) as [H8|H8].
      * rewrite !(Z.testbit_neg_r _ (i - 8)) by lia.
        destruct (Z.ltb_spec i (8 * Z.of_nat (S q))); [reflexivity|lia].
      * rewrite IH by lia.
        destruct (Z.ltb_spec (i - 8) (8 * Z.of_nat q)), (Z.ltb_spec i (8 * Z.of_nat (S q))); try lia; try reflexivity.
        pose proof (u8_range b). rewrite (Z_testbit_high 8 (bv_unsigned b)) by lia. reflexivity.
Qed.

Lemma testbit_lez_app : ltac2:(zQ "f1!h9!jc!jjb!jga!jj0!m7!l9!ji9!igd!ig7!p0!hm2!hq7!jq6!jqd&@2$7+8@1$8@2$5@1$1@1$0#8^4>2xs@1$6@1$1@1$0#8>2ys@1$6@1$1@1$0#8>1i$b>0@2$cZ^1@3$a$2@2$4@1$3@3$9@1$1@1$0#8^4^3^2M2\0$2$2@2$d^2~0@2$4@1$3^4^2@2$4@1$3^3@2$e^2~0").
Proof.
  intros xs ys i Hi. rewrite bytes_le_app, Z.lor_spec, Z.shiftl_spec by lia.
  destruct (Z.ltb_spec i (8 * Z.of_nat (length xs))).
  - rewrite (Z.testbit_neg_r (lez ys)) by lia. apply orb_false_r.
  - rewrite testbit_lez_high by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma Z_to_le_bytes_lez : ltac2:(zQ "70!h9!jc!l9!m7!p0!jr4!jga>2bs@1$2@1$1@1$0#8@3$4@1$2@1$1@1$0#8@2$5@2$3@1$1@1$0#8^1@1$6^1^1").
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes].
  replace (Z.shiftr (lez (b :: bs)) 8) with (lez bs).
  2:{ apply Z.bits_inj'. intros i Hi. rewrite Z.shiftr_spec by lia.
      pose proof (testbit_lez_skipn 1 (b :: bs) i Hi) as E. change (skipn 1 (b :: bs)) with bs in E.
      rewrite E. reflexivity. }
  rewrite IH. f_equal.
  apply bv_eq. rewrite Z_to_bv_unsigned.
  apply Z.bits_inj'. intros i Hi. pose proof (u8_range b).
  destruct (Z.lt_ge_cases i 8).
  - rewrite bv_wrap_spec_low by lia. rewrite lez_cons, Z.lor_spec, Z.shiftl_spec by lia.
    rewrite (Z.testbit_neg_r _ (i - 8)) by lia. apply orb_false_r.
  - rewrite bv_wrap_spec_high by lia. symmetry. apply (Z_testbit_high 8); lia.
Qed.

Lemma word_to_le_bytes_4_eq : ltac2:(zQ "f0!h9!jc!p0!l9!jj0!jjb!m7!n0!ji3!hm2!jga!jvc!hq7!hqd!hp9>1v@1$1@1$0#k0>1l@1$3@1$1@1$0#8>0@3$2$7@2$6@1$1@1$0#8^1N4>0>1i$9>0@2$8@2$cZ^1@2$d^1+i0@3$2$5@2$4@2$e@1$0#k0^5^2@2$4@1$a^4^2@3$2@1$3@1$1@1$0#8@2$bN4^4^3").
Proof.
  intros v l Hl Hb. unfold word_to_le_bytes.
  rewrite <- (Z_to_le_bytes_wrap 4 32) by (cbn; lia).
  rewrite <- Hl at 1. rewrite <- (Z_to_le_bytes_lez l). rewrite Hl. f_equal.
  apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i 32).
  - rewrite bv_wrap_spec_low by lia. apply Hb. lia.
  - rewrite bv_wrap_spec_high by lia. symmetry. apply testbit_lez_high. rewrite Hl. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma sw_bytes_LWv : ltac2:(zQ "80!h9!jc!l9!p0!m7!n0!jvc!jo6>1l@1$2@1$1@1$0#8>0@3$3$5@2$4@1$1@1$0#8^1N4@3$3@1$2@1$1@1$0#8@2$6N4@1$7^2^2").
Proof.
  intros l H. apply word_to_le_bytes_4_eq; [exact H|]. intros i Hi. apply testbit_u_LWv; assumption.
Qed.

(* [comment removed for export] *)
Definition LBv : ltac2:(zQ "20!h9!jc>1b@1$1@1$0#8@1$1@1$0#k0") := ltac2:(zQ "40!h9!hh5!jc!hp9\1b@1$2@1$0#8@2$1@1$0#k0@2$3@1$0#8^1").

Lemma sb_byte_LBv : ltac2:(zQ "60!h9!jc!p0!kh1!hh5!hp9>1b@1$1@1$0#8@3$2@1$1@1$0#8@2$4@1$0#8@2$5@1$0#k0@1$3^1^1").
Proof.
  intros b. unfold LBv. pose proof (u8_range b). rewrite u_Z2bv by lia.
  apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

(* [comment removed for export] *)
Lemma sb_byte_eq : ltac2:(zQ "b0!h9!jc!hp9!p0!jj0!jjb!ji3!hm2!hq7!hqd!hh5>1v@1$1@1$0#k0>1b@1$1@1$0#8>0>1i$7>0@2$6@2$8Z^1@2$9^1+8@3$3$5@2$4@2$2@1$0#k0^4^2@2$4@2$2@1$0#8^3^2@3$3@1$1@1$0#8@2$a@1$0#8@2$2@1$0#k0^3^2").
Proof.
  intros v b Hb. apply bv_eq. rewrite Z_to_bv_unsigned.
  apply Z.bits_inj'. intros i Hi. pose proof (u8_range b).
  destruct (Z.lt_ge_cases i 8).
  - rewrite bv_wrap_spec_low by lia. apply Hb. lia.
  - rewrite bv_wrap_spec_high by lia. symmetry. apply (Z_testbit_high 8); lia.
Qed.

Lemma testbit_nth_lez : ltac2:(zQ "h40!h9!jc!jj0!jjb!m7!l9!n0!ji3!p0!q9!s5!hm2!jga!hnd!hq7!hqd!ji9!igd!hh5!hp9>1l@1$5@1$1@1$0#8>1q$6>1i$b>0@2$7@2$eZ^1@2$f^1+8>0@2$9^3@2$4@1$1@1$0#8^4@3$8$3@2$2@2$h3@1$0#8@4$a@1$1@1$0#8^4^5@2$h2@1$0#8Z^3@2$2@1$c^5@2$d^3@2$h0+8@1$h1^4").
Proof.
  intros l q i Hi Hq. rewrite <- testbit_lez_skipn by lia.
  revert l Hq. induction q as [|q IH]; intros l Hq.
  - destruct l as [|b l]; [cbn in Hq; lia|]. cbn [nth skipn]. rewrite lez_cons.
    rewrite Z.lor_spec, Z.shiftl_spec, (Z.testbit_neg_r _ (i - 8)) by lia. symmetry. apply orb_false_r.
  - destruct l as [|b l]; [cbn in Hq; lia|]. cbn [nth skipn]. apply IH. cbn in Hq. lia.
Qed.

(* [comment removed for export] *)
Lemma sb_byte_srli_LWv : ltac2:(zQ "e0!h9!jc!n0!p0!hh5!m7!l9!ije!s5!kh8!jo6!ji9!igd!hp9>1l@1$6@1$1@1$0#8>1q$2>0@3$3$2@2$5@1$1@1$0#8^2N4>0@2$7^2N3@3$3@1$1@1$0#8@2$4@1$0#8@2$d@1$0#k0@2$9@1$a^4@2$b+8@1$c^3@4$8@1$1@1$0#8^3^4@2$4@1$0#8Z").
Proof.
  intros l q H Hq. apply sb_byte_eq. intros i Hi.
  unfold v_srli. rewrite Z_to_bv_unsigned, bv_wrap_spec_low, Z.shiftr_spec by lia.
  rewrite testbit_u_LWv by (try exact H; lia).
  rewrite testbit_nth_lez by (try rewrite H; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma testbit_u_srliw_LWv : ltac2:(zQ "h10!jjb!h9!p0!hm2!hnd!hq7!jj0!jc!jpe!m7!l9!n0!jga!ki2!jo6!jq6!hp9>1l@1$a@1$7@1$1#8>1s$3>1i$3>0@3$2$b@2$9@1$7@1$1#8^3N4>0@2$5+1^3>0@2$5Z^3@3$2$0@2$6@2$h0@1$1#k0@2$d@1$e^6^5^4M0\0$0$0@2$f@2$4^4^5+i0@2$6@1$c^6@2$4^4^5$8").
Proof.
  intros l s i H Hs Hi. unfold v_srliw. rewrite Z_to_bv_unsigned.
  assert (Sh : forall j, 0 <= j -> Z.testbit (Z.shiftr (bv_wrap 32 (bv_unsigned (LWv l))) s) j
                              = if j + s <? 32 then Z.testbit (lez l) (j + s) else false).
  { intros j Hj. rewrite Z.shiftr_spec by lia.
    destruct (Z.ltb_spec (j + s) 32).
    - rewrite bv_wrap_spec_low by lia. apply testbit_u_LWv; [exact H|lia].
    - apply bv_wrap_spec_high. lia. }
  destruct (Z.lt_ge_cases i 64).
  - rewrite bv_wrap_spec_low by lia. rewrite bv_swrap_spec by lia.
    case_bool_decide.
    + apply Sh. lia.
    + rewrite Sh by lia.
      destruct (Z.ltb_spec (Z.of_N 32 - 1 + s) 32), (Z.ltb_spec (i + s) 32); try lia; reflexivity.
  - rewrite bv_wrap_spec_high by lia. destruct (Z.ltb_spec (i + s) 32); [lia|reflexivity].
Qed.

(* [comment removed for export] *)
Lemma testbit_u_slli_LWv : ltac2:(zQ "h30!jjb!h9!p0!hm2!hq7!jj0!jc!jpe!m7!l9!n0!ji3!jga!kid!jo6!hqd!jq6!jqd!hp9>1l@1$9@1$6@1$1#8>1s$3>1i$3>0@3$2$a@2$8@1$6@1$1#8^3N4>0@2$4Z^3>0@2$b@2$4Z^3@2$f^3+i0@3$2$0@2$5@2$h2@1$1#k0@2$d@1$e^6^5^4M0\0$0$0@2$h0^4^5$7@2$5@1$c^6@2$h1^4^5").
Proof.
  intros l s i H Hs Hi. unfold v_slli. rewrite Z_to_bv_unsigned.
  rewrite bv_wrap_spec_low by lia. rewrite Z.shiftl_spec by lia.
  destruct (Z.ltb_spec i s).
  - apply Z.testbit_neg_r. lia.
  - apply testbit_u_LWv; [exact H|lia].
Qed.

Lemma testbit_u_vor : ltac2:(zQ "a0!h9!jj0!hp9!jc!jjb!kj7!p0!hm2!kjd!hq7>1x@1$3@1$0#k0>1y@1$3@1$0#k0>1i$7>0@2$9Z^1@3$6$4@2$1@2$2@1$0#k0@2$8^4^3^2@2$5@2$1@2$2@1$0#k0^4^2@2$1@2$2@1$0#k0^3^2").
Proof.
  intros x y i Hi. unfold v_or. rewrite Z_to_bv_unsigned.
  destruct (Z.lt_ge_cases i 64).
  - rewrite bv_wrap_spec_low by lia. apply Z.lor_spec.
  - rewrite bv_wrap_spec_high by lia.
    pose proof (u64_range x). pose proof (u64_range y).
    rewrite (Z_testbit_high 64 (bv_unsigned x)) by lia. rewrite (Z_testbit_high 64 (bv_unsigned y)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sw_bytes_merge : ltac2:(zQ "h31!h9!jc!p0!l9!n0!m7!ije!jo6!ji9!igd!ig7!ji3!ih7!ip3!jvc!kjd!kid!ki2!jqd&@3$2$4@2$5@1$1@1$0#8^4N4>2l1@1$3@1$1@1$0#8>2l2@1$3@1$1@1$0#8>1q$4>1v@1$1@1$0#k0>0~0>0~0>0@2$b@2$6N1^4@2$6^4N3>0@3$2@1$1@1$0#k0^4@2$f@2$h0@1$7^6@2$h2+i0@2$8+8@1$9^5@2$h1@1$7^7@2$8+8@1$9^5@3$2@1$3@1$1@1$0#8@2$eN4^5@3$a@1$1@1$0#8@3$d@1$1@1$0#8^6^8@3$c@1$1@1$0#8^6^7").
Proof.
  intros l1 l2 q v H1 H2 Hq ->.
  apply word_to_le_bytes_4_eq.
  { rewrite length_app, length_skipn, length_firstn, H1, H2. lia. }
  intros i Hi.
  rewrite testbit_u_vor by lia.
  rewrite testbit_u_slli_LWv by (try exact H2; lia).
  rewrite testbit_u_srliw_LWv by (try exact H1; lia).
  rewrite testbit_lez_app by lia. rewrite length_skipn, H1.
  rewrite testbit_lez_skipn by lia.
  destruct (Z.ltb_spec i (32 - 8 * Z.of_nat q)), (Z.ltb_spec i (8 * Z.of_nat (4 - q))),
           (Z.ltb_spec (i + 8 * Z.of_nat q) 32); try lia.
  - reflexivity.
  - rewrite testbit_lez_firstn by lia.
    destruct (Z.ltb_spec (i - 8 * Z.of_nat (4 - q)) (8 * Z.of_nat q)); [|lia].
    rewrite orb_false_r. f_equal. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma store_ok_at : ltac2:(zQ "h20!h9!jc!hq7!igd!jjb!l9!n0!kk5!p0!kkc!hnd!hve!hm2!it0!hv4!hl7!hr3!hp9>4segs@1$5$d>1m>0@1$1@1$0#k0@1$b@1$1@1$0#8>3dst@1$1@1$0#k0>1N$6>3bsw@1$5@1$1@1$0#8>1j$c>1k$6>0@2$2@2$a@2$h1@1$0#k0^5@1$3^4@2$h0+2+k0>0@3$8$4@4$9^8^7^6^5$7>0@2$2Z^4>0@2$2@2$a^5@1$3^4@1$3^7@3$8$4@4$9^b@3$e^a^9^7@2$f^9^6^5$7").
Proof.
  intros segs m dst N bsw j k Hnw Hok Hj Hk.
  destruct k as [|k]; [reflexivity|].
  pose proof (u64_range dst).
  apply (store_ok_mono segs (S k) m); [apply wbytes_grows|].
  apply (store_ok_sub segs m dst (at_ dst j) N (S k) Hnw Hok); rewrite at_u; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition callee_kept : ltac2:(zQ "30!l9!h9!jc@1$0@1$2@1$1#5") := ltac2:(zQ "70!h9!jc!m0!hle!ho4!ho9!n6@3$2@1$1@1$0#5@3$4@1$0#5+1Kv$3@2$5@1$0#5+1@3$2@1$1@1$0#5@3$4@1$0#5+2Kv$3@2$5@1$0#5+2@3$2@1$1@1$0#5@3$4@1$0#5+3Kv$3@2$5@1$0#5+3@3$2@1$1@1$0#5@3$4@1$0#5+4Kv$3@2$5@1$0#5+4@3$2@1$1@1$0#5@3$4@1$0#5+8Kv$3@2$5@1$0#5+8@3$2@1$1@1$0#5@3$4@1$0#5+9Kv$3@2$5@1$0#5+9@3$2@1$1@1$0#5@3$4@1$0#5+aKv$3@2$5@1$0#5+a@3$2@1$1@1$0#5@3$4@1$0#5+h2Kv$3@2$5@1$0#5+h2@3$2@1$1@1$0#5@3$4@1$0#5+h3Kv$3@2$5@1$0#5+h3@3$2@1$1@1$0#5@3$4@1$0#5+h4Kv$3@2$5@1$0#5+h4@3$2@1$1@1$0#5@3$4@1$0#5+h5Kv$3@2$5@1$0#5+h5@3$2@1$1@1$0#5@3$4@1$0#5+h6Kv$3@2$5@1$0#5+h6@3$2@1$1@1$0#5@3$4@1$0#5+h7Kv$3@2$5@1$0#5+h7@3$2@1$1@1$0#5@3$4@1$0#5+h8Kv$3@2$5@1$0#5+h8@3$2@1$1@1$0#5@3$4@1$0#5+h9Kv$3@2$5@1$0#5+h9@3$2@1$1@1$0#5@3$4@1$0#5+haKv$3@2$5@1$0#5+ha@3$2@1$1@1$0#5@3$4@1$0#5+hbKv$3@2$5@1$0#5+hb@1$6@1$1@1$0#5").

Definition keeps : ltac2:(zQ "30!h9!kne!jc>4regs@2$1@1$0#5@1$2@1$0#k0>5regs'@2$1@1$0#5@1$2@1$0#k0P") := ltac2:(zQ "70!h9!jc!kne!ko7!p0!kof!kr1\4regs@2$2@1$0#5@1$1@1$0#k0\5regs'@2$2@1$0#5@1$1@1$0#k0>1r@1$1@1$0#5>0@3$6@1$1@1$0#5^1$5@3$4@1$1@1$0#k0@2$3^3^2@2$3^4^2").

Lemma keeps_refl : ltac2:(zQ "40!h9!kne!kr7!jc>4regs@2$1@1$0#5@1$3@1$0#k0@2$2^1^1").
Proof. intros regs r _. reflexivity. Qed.

Lemma keeps_trans : ltac2:(zQ "40!h9!kne!kr7!jc>2r1@2$1@1$0#5@1$3@1$0#k0>2r2@2$1@1$0#5@1$3@1$0#k0>2r3@2$1@1$0#5@1$3@1$0#k0>0@2$2^3^2>0@2$2^3^2@2$2^5^3").
Proof. intros r1 r2 r3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.

(* [comment removed for export] *)
Lemma keeps_upd : ltac2:(zQ "80!h9!jc!kne!kr7!ks0!ks6!kof!kr1>4regs@2$2@1$0#5@1$1@1$0#k0>5regs'@2$2@1$0#5@1$1@1$0#k0>2rd@1$1@1$0#5>1v@1$1@1$0#k0>0@2$3^4^3>0@1$4@3$7@1$1@1$0#5^3$6@2$3^6@3$5^5^4^3").
Proof.
  intros regs regs' rd v K Hn r Hr.
  rewrite getr_other; [apply K, Hr|]. intros ->. exact (Hn Hr).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma not_in_regs_dec : ltac2:(zQ "b0!h9!jc!jjb!l9!kt0!kk5!p0!ks0!kt7!kr1!ku1>1r@1$1@1$0#5>1l@1$3@1$1@1$0#5>0@3$6$2@3$a@1$1@1$0#5\1x@1$1@1$0#5@1$4@3$8@1$0#5^1^3^1$5@1$7@3$9@1$1@1$0#5^3^2").
Proof.
  intros r l H Hin. pose proof (proj1 (forallb_forall _ _) H r Hin) as H'. cbn beta in H'.
  rewrite bv_eqb_refl in H'. discriminate H'.
Qed.
End FPX2.

Section FPX3. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
End FPX3.

(* [comment removed for export] *)
Ltac not_kept := first [ apply not_in_regs_dec; reflexivity | cbv; intuition discriminate ].

(* [comment removed for export] *)
Ltac solve_keeps :=
  repeat (apply keeps_upd; [| not_kept]); first [apply keeps_refl | assumption].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX4. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma runs_trans : ltac2:(zQ "92!h9!kne!jc!ji3!kuc!kv1!ljb!l9!it0&>0@2$1@1$0#5@1$2@1$0#k0$5&>0@2$1@1$0#5@1$2@1$0#k0P>4segs@1$7$8>2s0$5>3st1~0>2P1~1>3st2~0>2P2~1>0@2$4@2$1@1$0#5@1$2@1$0#k0\2r1@2$1@1$0#5@1$2@1$0#k0@2$3@3$6^7^6@1^5^1@1^4^1>0>2r1@2$1@1$0#5@1$2@1$0#k0>0@1^5^1@2$4@2$1@1$0#5@1$2@1$0#k0\2r2@2$1@1$0#5@1$2@1$0#k0@2$3@3$6^a@1^8^3@1^6^1@1^5^1@2$4@2$1@1$0#5@1$2@1$0#k0\2r2@2$1@1$0#5@1$2@1$0#k0@2$3@3$6^9^8@1^5^1@1^4^1").
Proof.
  (intros segs s0 st1 P1 st2 P2 nd_i1 K; ndestruct nd_i1 as (r1 & R1 & H1)).
  ndestruct (K r1 H1) as (r2 & R2 & H2).
  exists r2. split; [eapply msteps_trans; eassumption | exact H2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition callee_saved : ltac2:(zQ "30!l9!h9!jc@1$0@1$2@1$1#5") := ltac2:(zQ "70!h9!jc!m0!hle!ho4!ho9!n6@3$2@1$1@1$0#5@3$4@1$0#5+1Kv$3@2$5@1$0#5+1@3$2@1$1@1$0#5@3$4@1$0#5+2Kv$3@2$5@1$0#5+2@3$2@1$1@1$0#5@3$4@1$0#5+3Kv$3@2$5@1$0#5+3@3$2@1$1@1$0#5@3$4@1$0#5+4Kv$3@2$5@1$0#5+4@3$2@1$1@1$0#5@3$4@1$0#5+8Kv$3@2$5@1$0#5+8@3$2@1$1@1$0#5@3$4@1$0#5+9Kv$3@2$5@1$0#5+9@3$2@1$1@1$0#5@3$4@1$0#5+h2Kv$3@2$5@1$0#5+h2@3$2@1$1@1$0#5@3$4@1$0#5+h3Kv$3@2$5@1$0#5+h3@3$2@1$1@1$0#5@3$4@1$0#5+h4Kv$3@2$5@1$0#5+h4@3$2@1$1@1$0#5@3$4@1$0#5+h5Kv$3@2$5@1$0#5+h5@3$2@1$1@1$0#5@3$4@1$0#5+h6Kv$3@2$5@1$0#5+h6@3$2@1$1@1$0#5@3$4@1$0#5+h7Kv$3@2$5@1$0#5+h7@3$2@1$1@1$0#5@3$4@1$0#5+h8Kv$3@2$5@1$0#5+h8@3$2@1$1@1$0#5@3$4@1$0#5+h9Kv$3@2$5@1$0#5+h9@3$2@1$1@1$0#5@3$4@1$0#5+haKv$3@2$5@1$0#5+ha@3$2@1$1@1$0#5@3$4@1$0#5+hbKv$3@2$5@1$0#5+hb@1$6@1$1@1$0#5").

Definition keeps_cs : ltac2:(zQ "30!h9!kne!jc>4regs@2$1@1$0#5@1$2@1$0#k0>5regs'@2$1@1$0#5@1$2@1$0#k0P") := ltac2:(zQ "70!h9!jc!kne!ko7!p0!lo9!kr1\4regs@2$2@1$0#5@1$1@1$0#k0\5regs'@2$2@1$0#5@1$1@1$0#k0>1r@1$1@1$0#5>0@3$6@1$1@1$0#5^1$5@3$4@1$1@1$0#k0@2$3^3^2@2$3^4^2").

Lemma keeps_cs_refl : ltac2:(zQ "40!h9!kne!lp9!jc>4regs@2$1@1$0#5@1$3@1$0#k0@2$2^1^1").
Proof. intros regs r _. reflexivity. Qed.

Lemma keeps_cs_trans : ltac2:(zQ "40!h9!kne!lp9!jc>2r1@2$1@1$0#5@1$3@1$0#k0>2r2@2$1@1$0#5@1$3@1$0#k0>2r3@2$1@1$0#5@1$3@1$0#k0>0@2$2^3^2>0@2$2^3^2@2$2^5^3").
Proof. intros r1 r2 r3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.

Lemma keeps_cs_upd : ltac2:(zQ "80!h9!jc!kne!lp9!ks0!ks6!lo9!kr1>4regs@2$2@1$0#5@1$1@1$0#k0>5regs'@2$2@1$0#5@1$1@1$0#k0>2rd@1$1@1$0#5>1v@1$1@1$0#k0>0@2$3^4^3>0@1$4@3$7@1$1@1$0#5^3$6@2$3^6@3$5^5^4^3").
Proof.
  intros regs regs' rd v K Hn r Hr.
  rewrite getr_other; [apply K, Hr|]. intros ->. exact (Hn Hr).
Qed.

(* [comment removed for export] *)
Lemma keeps_cs_upd_same : ltac2:(zQ "b0!h9!jc!p0!kne!lp9!hle!ks0!ko7!ks6!ho4!ho9>4regs@2$3@1$0#5@1$1@1$0#k0>5regs'@2$3@1$0#5@1$1@1$0#k0>2rd@1$1@1$0#5>1v@1$1@1$0#k0>0@2$4^4^3>0@3$2@1$1@1$0#k0@2$7^5^3^2>0@1$6@3$2@1$1@1$0#5^4@3$9@1$0#5ZKv$5@2$a@1$0#5Z@2$4^7@3$8^6^5^4").
Proof.
  intros regs regs' rd v K Hv Hnz r Hr.
  destruct (decide (r = rd)) as [->|Hne].
  - rewrite getr_same by exact Hnz. symmetry. exact Hv.
  - rewrite getr_other by exact Hne. apply K, Hr.
Qed.

Lemma keeps_keeps_cs : ltac2:(zQ "50!h9!kne!jc!lp9!lu4>4regs@2$1@1$0#5@1$2@1$0#k0>5regs'@2$1@1$0#5@1$2@1$0#k0>0@2$4^2^1@2$3^3^2").
Proof.
  intros regs regs' K r Hr. apply K. unfold callee_saved, callee_kept in *. cbn [In] in *. intuition.
Qed.

End FPX4.

Ltac solve_keeps_cs :=
  repeat (first [ apply keeps_cs_upd; [| not_kept]
                | apply keeps_cs_upd_same; [| solve [eauto | symmetry; eauto] | let X := fresh in intro X; discriminate X ] ]);
  first [apply keeps_cs_refl | assumption | apply keeps_keeps_cs; assumption].
(* [comment removed for export] *)
