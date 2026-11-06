(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XExitSim XPropExec XCatSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk16optionhfbbv_unsignedk16lengthk14list37Corelib4Init5Logico02eq89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8XCatExec6WithFP~~~~~~p96wbytes46Stdlib6ZArith6BinInt1Zu73addu72leu76of_nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9XPropExec~~~~~~hh33rdnk13nat3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehlf7Segmentu73powu72lto02or01Z3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasehr2dZ_to_le_bytes3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshv2h0word_to_le_byteshv2cwrite_to_mem" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithFP.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint wbytes (m : word -> option byte) (addr : word) (bs : list byte)
    : word -> option byte :=
  match bs with
  | [] => m
  | b :: rest => wbytes (fun a => if bv_eqb a addr then Some b else m a) (addr+1) rest
  end.

(* [comment removed for export] *)
Lemma wbytes_above : ltac2:(zQ "b0!h9!jc!l9!m2!n0!n9!p4!te!vf!hg5!hga>2bs@1$5@1$1@1$0#8>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>4addr@1$1@1$0#k0>1x@1$1@1$0#k0>0@2$9@2$8@2$3@1$0#k0^2@1$a@2$4@1$1@1$0#8^4@2$3@1$0#k0^1@3$6@1$2@1$1@1$0#8@4$7^4^3^5^2@1^4^2").
Proof.
  induction bs as [|b rest IH]; intros m addr x Hle; [reflexivity|].
  cbn [wbytes length] in *.
  pose proof (u64_range x) as Hx.
  assert (Hu1 : bv_unsigned (addr + 1) = (bv_unsigned addr + 1)%Z)
    by (apply u_add1; lia).
  rewrite IH by lia.
  cbv beta.
  assert (Hne : bv_eqb x addr = false)
    by (unfold bv_eqb; apply Z.eqb_neq; lia).
  rewrite Hne. reflexivity.
Qed.

Lemma rdn_wbytes_disjoint : ltac2:(zQ "f0!h9!jc!n9!m2!l9!hl2!vf!hg5!hga!n0!hl9!p4!hp4!te!hpf>4segs@1$2$c>2bs@1$2@1$1@1$0#8>1m>0@1$1@1$0#k0@1$4@1$1@1$0#8>4addr@1$1@1$0#k0>1a@1$1@1$0#k0>1n$a>0@2$7@2$6@2$3@1$0#k0^3@1$8@2$9@1$1@1$0#8^5@2$3@1$0#k0^2>0@2$7@2$6@2$3@1$0#k0^3@1$8^2@2$e+2+k0@3$b@1$4@1$2@1$1@1$0#8@4$5^8@3$d^6^5^7^4^3@4$5^8^6^4^3").
Proof.
  intros segs bs m addr a n Hle Hnw. apply rdn_ext; [exact Hnw|].
  intros x Hx. apply wbytes_above. lia.
Qed.

(* [comment removed for export] *)
Lemma wbytes_below : ltac2:(zQ "d0!h9!jc!m2!l9!n0!n9!p4!te!vf!hg5!hq5!hga!hpf>2bs@1$5@1$1@1$0#8>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>4addr@1$1@1$0#k0>1x@1$1@1$0#k0>0@2$9@2$8@2$2@1$0#k0^2@1$b@2$4@1$1@1$0#8^4@2$c+2+k0>0@2$a@2$2@1$0#k0^2@2$2@1$0#k0^3@3$6@1$3@1$1@1$0#8@4$7^5^4^6^3@1^5^3").
Proof.
  induction bs as [|b rest IH]; intros m addr x Hnw Hlt; [reflexivity|].
  cbn [wbytes length] in *.
  assert (Hne : bv_eqb x addr = false)
    by (unfold bv_eqb; apply Z.eqb_neq; lia).
  destruct rest as [|b' rest'].
  - cbn [wbytes]. rewrite Hne. reflexivity.
  - assert (Hu1 : bv_unsigned (addr + 1) = (bv_unsigned addr + 1)%Z)
      by (apply u_add1; cbn [length] in Hnw; lia).
    rewrite IH by lia.
    cbv beta. rewrite Hne. reflexivity.
Qed.

Lemma rdn_wbytes_below : ltac2:(zQ "f0!h9!jc!n9!m2!l9!hl2!vf!hg5!hga!n0!hl9!p4!hp4!te!hpf>4segs@1$2$c>2bs@1$2@1$1@1$0#8>1m>0@1$1@1$0#k0@1$4@1$1@1$0#8>4addr@1$1@1$0#k0>1a@1$1@1$0#k0>1n$a>0@2$7@2$6@2$3@1$0#k0^2@1$8^1@2$3@1$0#k0^3>0@2$7@2$6@2$3@1$0#k0^4@1$8@2$9@1$1@1$0#8^6@2$e+2+k0@3$b@1$4@1$2@1$1@1$0#8@4$5^8@3$d^6^5^7^4^3@4$5^8^6^4^3").
Proof.
  intros segs bs m addr a n Hle Hnw.
  pose proof (u64_range addr) as Ha.
  apply rdn_ext; [lia|].
  intros x Hx. apply wbytes_below; [exact Hnw|lia].
Qed.

(* [comment removed for export] *)
Lemma rdn_wbytes_out : ltac2:(zQ "h00!h9!jc!m2!vf!hg5!hga!n9!n0!l9!hl2!hpf!hl9!p4!hqa!hp4!te>4segs@1$6$e>2bs@1$6@1$1@1$0#8>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>4addr@1$1@1$0#k0>1a@1$1@1$0#k0>1n$b>0@2$d@2$4@2$3@2$2@1$0#k0^2@1$5^1@2$2@1$0#k0^3@2$4@2$3@2$2@1$0#k0^3@1$5@2$7@1$1@1$0#8^5@2$2@1$0#k0^2>0@2$4@2$3@2$2@1$0#k0^3@1$5^2@2$a+2+k0>0@2$4@2$3@2$2@1$0#k0^5@1$5@2$7@1$1@1$0#8^7@2$a+2+k0@3$c@1$8@1$6@1$1@1$0#8@4$9^9@3$f^7^6^8^5^4@4$9^9^7^5^4").
Proof.
  intros segs bs m addr a n [Hb|Hd] Hnw Hnw'.
  - apply rdn_wbytes_below; [exact Hb | exact Hnw'].
  - apply rdn_wbytes_disjoint; [exact Hd | exact Hnw].
Qed.

Lemma length_Z_to_le_bytes : ltac2:(zQ "70!hl9!n0!p4!h9!hqf!hu1!jc>1n$0>1z$4@3$2$0@2$1@1$6@1$3#8@2$5^2^1^2").
Proof.
  induction n as [|n IH]; intro z; [reflexivity|].
  cbn [Z_to_le_bytes length]. rewrite IH. reflexivity.
Qed.

Lemma length_N_to_le_bytes : ltac2:(zQ "60!hl9!h9!jc!n0!p4!ii9>1n$0>1v@1$2@1$1#k0@3$4$0@2$3@1$2@1$1#8@2$5^2^1^2").
Proof. intros. unfold word_to_le_bytes. apply length_Z_to_le_bytes. Qed.

(* [comment removed for export] *)
Lemma write_to_mem_wbytes : ltac2:(zQ "71!h9!jc!l9!n9!p4!ije!te&>0@1$1@1$0#k0@1$2@1$1@1$0#8>2bs@1$3@1$1@1$0#8>1m~0>4addr@1$1@1$0#k0@3$4~0@3$5^2^1^3@3$6^2^1^3").
Proof.
  induction bs as [|b rest IH]; intros m addr; [reflexivity|].
  cbn [write_to_mem wbytes]. apply IH.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

 (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP.
(* [comment removed for export] *)
