(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep TacX ZBridge Exec CellsX Bytes Mem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos01Z35stdpp9bitvectorbdefinitionsi22bv37Corelib4Init9Datatypesk44list37Corelib5Lists7ListDefm33nth79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~o02b846Stdlib6ZArith6BinInt1Zs03subs06to_natk44consk46lengthk43natk43nil37Corelib4Init5Logichg32eq37Corelib4Init5Peanohhd2ltm36firstnm35skipnk46option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~hl15rsegsk44Some3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshpedov_read_bytes89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU8BJKitNum3HCW~~~~~~hu63inb79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ij08bytes_ats03adds02les02lts06of_nati27Z_to_bvhg33ands03powi29bv_signedk44bools03lebi2bbv_unsignedk44andbhhd2lehu64cdigk41Sk44truehu65isdigk45falsehg33iffs06modulo" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

  Definition inb : ltac2:(zQ "40!h9!hf!jf!lc>2bs@1$3@1$2@1$0#8>2p0$1>1x$1@1$2@1$0#8") := ltac2:(zQ "80!h9!hf!jf!lc!na!rb!t8!te\2bs@1$3@1$2@1$0#8\2p0$1\1x$1@4$4@1$2@1$0#8@1$7@2$6^1^2^3@1$5Z").

  Lemma firstn1_skipn_nth : ltac2:(zQ "c0!h9!jf!lc!u7!ue!v7!vd!hh7!hj1!hj7!na!hk0>2bs@1$2@1$1@1$0#8>1k$5>1d@1$1@1$0#8>0@2$8^2@2$4@1$1@1$0#8^3@3$7@1$2@1$1@1$0#8@3$9@1$1@1$0#8N1@3$b@1$1@1$0#8^3^4@3$3@1$1@1$0#8@4$a@1$1@1$0#8^3^4^2@1$6@1$1@1$0#8").
  Proof.
    induction bs as [|b bs IH]; intros k d Hk; cbn in Hk; [lia|].
    destruct k as [|k]; cbn; [reflexivity|]. apply IH. lia.
  Qed.

  Lemma inp_read : ltac2:(zQ "h30!h9!jf!lc!hk8!hf!hoe!hp7!u7!ue!vd!hh7!ht5!ii9!ima!in6!inc!io1!io6!iof>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>2p0$4>2bs@1$2@1$1@1$0#8>1x$4>0@4$d$5^4^3^2>0@2$f^4^2>0@2$h0^3@2$e^5@1$h1@2$8@1$1@1$0#8^4@3$a@1$3@1$2@1$1@1$0#8@4$b$5^7@2$h2@1$0#k0^4N1@2$6@1$2@1$1@1$0#8@3$7@1$1@1$0#8@3$c^5^6^4@1$9@1$1@1$0#8").
  Proof.
    intros m p0 bs x BA H1 H2. unfold inb.
    replace (Z_to_bv 64 x) with (wa (p0 + (x - p0))) by (unfold wa; f_equal; lia).
    rewrite (bytes_at_read rsegs m p0 bs (x - p0) 1 BA) by lia.
    f_equal. apply firstn1_skipn_nth. lia.
  Qed.

  Lemma signed_small : ltac2:(zQ "90!h9!hf!ip9!hh7!inc!io1!iq0!iof!iq6>1z$1>0@2$2@2$4Z^1@2$5^1@2$6+2+jf@3$3$1@2$8@1$0#k0@2$7@1$0#k0^2^2").
  Proof.
    intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 64 / 2)%Z with (2^63)%Z. lia.
  Qed.

  (* [comment removed for export] *)
  Definition isdig : ltac2:(zQ "30!ir2!h9!jf>1b@1$2@1$1#8$0") := ltac2:(zQ "50!h9!ir9!irf!isd!jf\1b@1$4@1$0#8@2$3@2$1+j0@2$2@1$0#8^1@2$1@2$2@1$0#8^1+j9").
  Fixpoint cdig (bs : list byte) (p0 p : Z) (k : nat) : nat :=
    match k with
    | O => O
    | S k' => if isdig (inb bs p0 p) then S (cdig bs p0 (p + 1) k') else O
    end.
  Lemma cdig_le : ltac2:(zQ "70!hf!lc!v7!it4!h9!ita!jf>2bs@1$1@1$6@1$4#8>2p0$0>1k$2>1p$0@2$3@4$5^4^3^1^2^2").
  Proof. intros bs p0 k. induction k as [|k IH]; intros p; cbn; [lia|]. destruct (isdig _); [pose proof (IH (p+1)); lia| lia]. Qed.
  Lemma cdig_true : ltac2:(zQ "d0!iu2!v7!hh7!hf!ita!ir2!lc!iu6!h9!ii9!iud!in6!jf>2bs@1$6@1$c@1$8#8>2p0$3>1p$3>1k$1>0@3$2$5@1$a@3$9^4^3^2$7@3$2$1@4$4^5^4^3@1$0^2@1$0@4$4^5^4@2$b^3+1^2").
  Proof. intros bs p0 p k H. cbn. rewrite H. reflexivity. Qed.
  Lemma cdig_false : ltac2:(zQ "c0!v7!hh7!hf!iu2!ir2!iv6!lc!h9!ita!ii9!iud!jf>2bs@1$6@1$b@1$7#8>2p0$2>1p$2>1k$0>0@3$1$4@1$a@3$9^4^3^2$5@3$1$0@4$8^5^4^3@1$3^2N0").
  Proof. intros bs p0 p k H. cbn. rewrite H. reflexivity. Qed.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma dig58 : ltac2:(zQ "80!inc!ip9!ive!hf!in6!io1!jg5!iq0>1b$3>0@2$1@2$0Z^1@2$5^1+hg0@2$2@2$0+vvvvvvvvvvvvvvv6@2$6@2$4^2-ja@2$7+2+k0@2$1@2$0+j0^2@2$0^2+j9").
  Proof.
    intros b Hb. split; intros H.
    - destruct (Z.lt_ge_cases b 58).
      + rewrite <- (Z.mod_add _ 1) in H by lia. rewrite Z.mod_small in H by lia. lia.
      + rewrite Z.mod_small in H by lia. lia.
    - rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dtest_true : ltac2:(zQ "a0!h9!irf!iof!ir2!iu6!hh7!iud!in6!inc!jf>1b@1$9@1$0#8>0@2$8+vvvvvvvvvvvvvvv6@2$1@1$0#k0@2$2@1$0#k0@2$7@2$1@1$0#k0@2$2@1$0#k0@2$1@1$0#8^1-ja@3$5$3@1$6^2$4").
  Proof.
    intros b H. pose proof (bv_unsigned_in_range _ b) as R. unfold bv_modulus in R; cbn in R.
    rewrite (unsigned_lit (bv_unsigned b)) in H by lia. rewrite unsigned_lit_wrap in H.
    apply (proj1 (dig58 (bv_unsigned b) ltac:(lia))) in H. unfold isdig. apply andb_true_intro. split; apply Z.leb_le; lia.
  Qed.
  Lemma dtest_false : ltac2:(zQ "a0!h9!irf!iof!ir2!iv6!hh7!iud!in6!io1!jf>1b@1$9@1$0#8>0@2$8@2$1@1$0#k0@2$2@1$0#k0@2$7@2$1@1$0#k0@2$2@1$0#k0@2$1@1$0#8^1-ja+vvvvvvvvvvvvvvv6@3$5$3@1$6^2$4").
  Proof.
    intros b H. pose proof (bv_unsigned_in_range _ b) as R. unfold bv_modulus in R; cbn in R.
    rewrite (unsigned_lit (bv_unsigned b)) in H by lia. rewrite unsigned_lit_wrap in H.
    unfold isdig. destruct (Z.leb_spec0 48 (bv_unsigned b)); destruct (Z.leb_spec0 (bv_unsigned b) 57); cbn; try reflexivity.
    exfalso. pose proof (proj2 (dig58 (bv_unsigned b) ltac:(lia)) ltac:(lia)). lia.
  Qed.
  Lemma dtest_true' : ltac2:(zQ "a0!h9!irf!ir2!iu6!hh7!iud!in6!inc!iof!jf>1b@1$9@1$0#8>0@2$7+vvvvvvvvvvvvvvv6@2$1@1$0#k0@2$8@1$0#k0@2$6@2$1@1$0#8^1-ja@3$4$2@1$5^2$3").
  Proof.
    intros b H. pose proof (bv_unsigned_in_range _ b) as R. unfold bv_modulus in R; cbn in R.
    apply dtest_true. rewrite (unsigned_lit (bv_unsigned b)) by lia. exact H.
  Qed.
  Lemma dtest_false' : ltac2:(zQ "a0!h9!irf!ir2!iv6!hh7!iud!in6!io1!iof!jf>1b@1$9@1$0#8>0@2$7@2$1@1$0#k0@2$8@1$0#k0@2$6@2$1@1$0#8^1-ja+vvvvvvvvvvvvvvv6@3$4$2@1$5^2$3").
  Proof.
    intros b H. pose proof (bv_unsigned_in_range _ b) as R. unfold bv_modulus in R; cbn in R.
    apply dtest_false. rewrite (unsigned_lit (bv_unsigned b)) by lia. exact H.
  Qed.
End HCW.
(* [comment removed for export] *)
