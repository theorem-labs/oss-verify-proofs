(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import StartupTac ArgvEnv RefLayout.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list03nat37Corelib7Numbers7BinNumsi34Npos35stdpp9bitvectorbdefinitionsk32bv89OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UeRefStartupDefs4FPX1~~~~~~m5h0after_last_slash3h5LinuxProcessSemanticsfLinuxProcessSembStackLayouts1fat_random_bytess19ed_random37Corelib5Lists7ListDefhh33nth89OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UeRefStartupDefs4Defs~~~~~~hj12rbk37Z_to_bv46Stdlib6ZArith6BinInt1Zho93subk3bbv_unsignedho93add06lengthho93mulho96of_nat69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7ArgvEnv~~~~~~ht65argcN69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~ih9ccat_argv_ptr03nilhj14pn_w79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UeRefStartupDefs~~~~~~in0cprogname_offs1dat_random_ptr06option3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsitbh0word_to_le_bytesih96wbytes04Nonehj16auxv_whj16envp_whj1aprogname_whj16argc_whj16argv_whj18aux_basehj15rnd_w69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7ZStores~~~~~~jo25zeros04conshj16D_tlsAhj16D_tlsBhj13rbn3h5LinuxProcessSemanticsfLinuxProcessSem6BvBaseju6dbytes_le_to_Zhj1ccanary_byteshj18canary_whj15D_cxxhj14D_fdhj16D_libchj15D_ssphj15D_tls37Corelib4Init5Logickmf2eqhh36firstnhh35skipns19EntryDraw" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation RPH := Ubsan.M.phdrs.

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Fixpoint after_last_slash (s : list byte) (i acc : nat) : nat :=
  match s with
  | [] => acc
  | b :: s' => after_last_slash s' (S i) (if bv_eqb b (Z_to_bv 8 47) then S i else acc)
  end.
Definition progname_off : ltac2:(zQ "40!h8!he!jc!m0>1s@1$0@1$3@1$2#8$1") := ltac2:(zQ "40!h8!jc!qd!m0\1s@1$0@1$3@1$1#8@3$2^1N0N0").

End FPX1.

Section Defs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.          (* [comment removed for export] *)
  Variable rnd : ltac2:(zQ "10!kpc$0").    (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition rb : ltac2:(zQ "30!h8!jc!m0@1$0@1$2@1$1#8") := ltac2:(zQ "20!v5!hg7@1$0@1$1?3rnd").
  Definition rbn : ltac2:(zQ "30!he!jc!m0>1i$0@1$2@1$1#8") := ltac2:(zQ "60!jc!he!hia!hn9!hnf!m0\1i$1@4$2@1$5@1$0#8^1$3@2$4@1$0#8Z").

  (* [comment removed for export] *)
  Definition aux_base : ltac2:(zQ "20!jc!m0@1$1@1$0#k0") := ltac2:(zQ "40!jc!hq1!hnf!hq8@2$2@1$0#k0@2$1@2$3@1$0#k0?3sp0+hn0").
  (* [comment removed for export] *)
  Definition argv_w : ltac2:(zQ "20!jc!m0@1$1@1$0#k0") := ltac2:(zQ "40!jc!hr6!hnf!hq8@2$2@1$0#k0@2$1@2$3@1$0#k0?3sp0+8").
  Definition envp_w : ltac2:(zQ "20!jc!m0@1$1@1$0#k0") := ltac2:(zQ "90!jc!hr6!hrd!h8!hs5!hsc!hnf!m0!hq8@2$6@1$0#k0@2$1@2$1@2$8@1$0#k0?3sp0+h0@2$4+8@1$5@2$2@1$3@1$7@1$0#8?2av").
  Definition auxv_w : ltac2:(zQ "20!jc!m0@1$1@1$0#k0") := ltac2:(zQ "90!jc!hr6!hrd!h8!hs5!hsc!m0!hnf!hq8@2$7@1$0#k0@2$1@2$1@2$1@2$8@1$0#k0?3sp0+h8@2$4+8@1$5@2$2@1$3@1$6@1$0#8?2av@2$4+8@1$5@2$2@1$3@1$6@1$0#8?2ev").
  Definition argc_w : ltac2:(zQ "20!jc!m0@1$1@1$0#k0") := ltac2:(zQ "10!ih0@1$0?2av").
  (* [comment removed for export] *)
  Definition pn_w : ltac2:(zQ "20!jc!m0@1$1@1$0#k0") := ltac2:(zQ "10!il3@4$0?3sp0?2av?2evN0").
  Definition progname_w : ltac2:(zQ "20!jc!m0@1$1@1$0#k0") := ltac2:(zQ "b0!jc!m0!h8!im3!hia!im8!ir3!hr6!hsc!hnf!hq8@2$9@1$0#k0@2$7@2$a@1$0#k0$5@1$8@1$6@4$4@1$2@1$1@1$0#8N0?2av@1$3@1$1@1$0#8").
  (* [comment removed for export] *)
  Definition rnd_w : ltac2:(zQ "20!jc!m0@1$1@1$0#k0") := ltac2:(zQ "10!is3@3$0?3sp0?2av?2ev").

  (* [comment removed for export] *)
  Definition D_libc : ltac2:(zQ "30!jc!m0!it3>0@1$1@1$0#k0@1$2@1$1@1$0#8") := ltac2:(zQ "a0!jc!hnf!jh2!ji7!m0!jj1!jj7!jk1!im8!jkb@3$3@3$3@3$3@3$3@3$3@3$3\0@1$4@1$0#k0@1$5@1$4@1$0#8@2$1@1$0#k0+hguri8@2$2N8$7@2$1@1$0#k0+hiuup0@2$2N8$6@2$1@1$0#k0+hiuuv0@2$2N8?2hw@2$1@1$0#k0+hiuur8@2$2N8@2$1@1$0#k0+hgg0@2$1@1$0#k0+hiuuo0@2$2N8$8@2$1@1$0#k0+hiuun8@2$2N8$9").      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition J_lsm : ltac2:(zQ "31!jc!m0!it3&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1J~0~0") := ltac2:(zQ "a0!jc!hnf!jh2!ji7!hq1!hq8!m0!it3!jl9!jm3\1J>0@1$6@1$0#k0@1$7@1$6@1$0#8@3$3@3$3@3$3@3$3@3$3@3$3@3$3@3$3^1@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+8@2$2N8@2$1@1$0#k0Z@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+h0@2$2N8@2$1@1$0#k0Z@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+h8@2$2N8@2$1@1$0#k0Z@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+i0@2$2N8@2$1@1$0#k0Z@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+i8@2$2N8@2$1@1$0#k0+ttlg4@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+j0@2$2N8$9@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+j8@2$2N8$8@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+k0@2$2N8@2$1@1$0#k0+kmvu4").

  (* [comment removed for export] *)
  Definition J_aux : ltac2:(zQ "31!jc!m0!it3&>0@1$1@1$0#k0@1$2@1$1@1$0#8>2Jf~0~0") := ltac2:(zQ "b0!jc!hnf!ji7!jh2!hq1!hq8!m0!it3!jmd!jn9!jrc\2Jf>0@1$6@1$0#k0@1$7@1$6@1$0#8@3$2@3$2@3$2@3$2@3$2@3$2@3$2@3$2@3$2@3$2^1$8@1$aNhj0@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+hl8@2$3N8@2$1@1$0#k0+hggk0@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+hl0@2$3N8@2$1@1$0#k0+j8@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+hk8@2$3N8@2$1@1$0#k0+a@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+v0@2$3N8?2hw@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+hk0@2$3N8@2$1@1$0#k0+hgg0@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+hh8@2$3N8?3uid@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+hh0@2$3N8?3uid@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+r8@2$3N8@2$1@1$0#k0Z@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+q8@2$3N8$9").                  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_tlsA : ltac2:(zQ "31!jc!m0!it3&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1D~0~0") := ltac2:(zQ "80!jc!hnf!ji7!jh2!m0!js5!im3!it3\1D>0@1$4@1$0#k0@1$7@1$4@1$0#8@3$2@3$2@3$2@3$2@3$2@3$2@3$2@3$2@3$2@3$2^1@2$1@1$0#k0+hiusi0@2$3N8@2$1@1$0#k0Z@2$1@1$0#k0+hiusj0@2$3N8@2$1@1$0#k0Z@2$1@1$0#k0+hiusi8@2$3N8@2$1@1$0#k0+8@2$1@1$0#k0+hiuuq0@2$3N8@2$1@1$0#k0+u0@2$1@1$0#k0+hiuuq8@2$3N8@2$1@1$0#k0+8@2$1@1$0#k0+hgusg8@2$3N8@2$1@1$0#k0Z@2$1@1$0#k0+hgurv0@2$3N8@2$1@1$0#k0+hgusg8@2$1@1$0#k0+hgurj0@2$3N8@2$1@1$0#k0+hgurj0@2$1@1$0#k0+hiuuo8@3$5@1$4@1$0#8@2$1@1$0#8+1@1$6@1$4@1$0#8@2$1@1$0#k0+hgurl8@2$3N4@2$1@1$0#k0+2").        (* [comment removed for export] *)

  Definition D_tlsB : ltac2:(zQ "31!jc!m0!it3&>0@1$1@1$0#k0@1$2@1$1@1$0#8>3tid@1$1@1$0#k0>1D~0~0") := ltac2:(zQ "61!jc!hnf!jh2!ji7!m0!it3&@2$2N8@2$1@1$0#k0+hgurj0\3tid@1$4@1$0#k0\1D>0@1$4@1$0#k0@1$5@1$4@1$0#8@3$3@3$3@3$3@3$3@3$3@3$3^1@2$1@1$0#k0+hgurl0@2$2N4^2@2$1@1$0#k0+hgurs8@2$2N8@2$1@1$0#k0+hiuus0@2$1@1$0#k0+hgurq8@2$2N8@2$1@1$0#k0+hgurq8@2$1@1$0#k0+hgurj8~0@2$1@1$0#k0+hgurk0~0@2$1@1$0#k0+hgurk8@2$2N8@2$1@1$0#k0Z").        (* [comment removed for export] *)

  Definition D_tls : ltac2:(zQ "31!jc!m0!it3&>0@1$1@1$0#k0@1$2@1$1@1$0#8>3tid@1$1@1$0#k0>1D~0~0") := ltac2:(zQ "50!jc!m0!it3!jsb!jt5\3tid@1$1@1$0#k0\1D>0@1$1@1$0#k0@1$2@1$1@1$0#8@2$4^2@1$3^1").

  (* [comment removed for export] *)
  Definition J_tls : ltac2:(zQ "31!jc!m0!it3&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1J~0>2ra@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0~0") := ltac2:(zQ "80!jc!m0!jh2!ji7!hq1!hnf!hq8!it3\1J>0@1$1@1$0#k0@1$7@1$1@1$0#8\2ra@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0@3$3@3$3@3$3@3$3@3$3@3$3@3$3^8@2$5@1$0#k0@2$4@2$6@1$0#k0?3sp0+hq8@2$2N8^7@2$5@1$0#k0@2$4@2$6@1$0#k0?3sp0+hr0@2$2N8^6@2$5@1$0#k0@2$4@2$6@1$0#k0?3sp0+hr8@2$2N8^5@2$5@1$0#k0@2$4@2$6@1$0#k0?3sp0+hs0@2$2N8^4@2$5@1$0#k0@2$4@2$6@1$0#k0?3sp0+hs8@2$2N8^3@2$5@1$0#k0@2$4@2$6@1$0#k0?3sp0+ht0@2$2N8^2@2$5@1$0#k0@2$4@2$6@1$0#k0?3sp0+ht8@2$2N8^1").

  (* [comment removed for export] *)
  Definition canary_bytes : ltac2:(zQ "30!h8!jc!m0@1$0@1$2@1$1#8") := ltac2:(zQ "60!jc!m0!js5!jtf!im3!hnf@3$2@1$1@1$0#8@1$3N0@3$2@1$1@1$0#8@2$5@1$0#8Z@3$2@1$1@1$0#8@1$3N2@3$2@1$1@1$0#8@1$3N3@3$2@1$1@1$0#8@1$3N4@3$2@1$1@1$0#8@1$3N5@3$2@1$1@1$0#8@1$3N6@3$2@1$1@1$0#8@1$3N7@1$4@1$1@1$0#8").
  Definition canary_w : ltac2:(zQ "20!jc!m0@1$1@1$0#k0") := ltac2:(zQ "40!jc!kh5!ki6!hnf@2$3@1$0#k0@1$1$2").
  Definition D_ssp : ltac2:(zQ "31!jc!m0!it3&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1D~0~0") := ltac2:(zQ "a0!jc!m0!js5!jtf!hnf!ji7!im3!it3!jh2!kj6\1D>0@1$1@1$0#k0@1$7@1$1@1$0#8@3$5@3$5@3$5@3$5^1@2$4@1$0#k0+hiusj8@3$2@1$1@1$0#8@1$3N0@3$2@1$1@1$0#8@1$3N1@3$2@1$1@1$0#8@1$3N2@3$2@1$1@1$0#8@1$3N3@1$6@1$1@1$0#8@2$4@1$0#k0+hiusjc@3$2@1$1@1$0#8@1$3N4@3$2@1$1@1$0#8@1$3N5@3$2@1$1@1$0#8@1$3N6@3$2@1$1@1$0#8@1$3N7@1$6@1$1@1$0#8@2$4@1$0#k0+hiusj9@3$2@1$1@1$0#8@2$4@1$0#8Z@1$6@1$1@1$0#8@2$4@1$0#k0+hguru8@2$8N8$9").       (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_fd : ltac2:(zQ "31!jc!m0!it3&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1D~0~0") := ltac2:(zQ "70!jc!m0!hnf!js5!im3!it3!ji7\1D>0@1$1@1$0#k0@1$5@1$1@1$0#8@3$6^1@2$2@1$0#k0+vtgv0@3$3@1$1@1$0#8@2$2@1$0#8+1@1$4@1$1@1$0#8").

  (* [comment removed for export] *)
  Definition D_cxx : ltac2:(zQ "31!jc!m0!it3&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1D~0~0") := ltac2:(zQ "60!jc!hnf!jh2!ji7!m0!it3\1D>0@1$4@1$0#k0@1$5@1$4@1$0#8@3$3@3$3@3$3@3$3@3$3@3$3^1@2$1@1$0#k0+hgtki8@2$2N4@2$1@1$0#k0+1@2$1@1$0#k0+hgthq0@2$2N4@2$1@1$0#k0Z@2$1@1$0#k0+hgtki8@2$2N4@2$1@1$0#k0+2@2$1@1$0#k0+hgthq4@2$2N4@2$1@1$0#k0+1@2$1@1$0#k0+hgtki8@2$2N4@2$1@1$0#k0+3@2$1@1$0#k0+hgthq8@2$2N4@2$1@1$0#k0+2").     (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_main : ltac2:(zQ "30!jc!m0!it3>3tid@1$1@1$0#k0>0@1$1@1$0#k0@1$2@1$1@1$0#8") := ltac2:(zQ "70!jc!kk2!kkb!kl3!kld!km6!m0\3tid@1$6@1$0#k0@1$1@1$2@1$4@2$5^1$3").

  Lemma firstn4_rb : ltac2:(zQ "90!jc!m0!js5!jtf!h8!im3!ko3!ko9!hn9@3$6@1$4@1$1@1$0#8@3$7@1$1@1$0#8N4$8@3$2@1$1@1$0#8@1$3N0@3$2@1$1@1$0#8@1$3N1@3$2@1$1@1$0#8@1$3N2@3$2@1$1@1$0#8@1$3N3@1$5@1$1@1$0#8").
  Proof. reflexivity. Qed.
  Lemma firstn4_skipn4_rb : ltac2:(zQ "a0!jc!m0!js5!jtf!h8!im3!ko3!ko9!kp3!hn9@3$6@1$4@1$1@1$0#8@3$7@1$1@1$0#8N4@3$8@1$1@1$0#8N4$9@3$2@1$1@1$0#8@1$3N4@3$2@1$1@1$0#8@1$3N5@3$2@1$1@1$0#8@1$3N6@3$2@1$1@1$0#8@1$3N7@1$5@1$1@1$0#8").
  Proof. reflexivity. Qed.

End Defs.
(* [comment removed for export] *)
