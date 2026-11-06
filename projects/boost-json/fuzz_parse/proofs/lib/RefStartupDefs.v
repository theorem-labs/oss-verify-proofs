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

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import StartupTac ArgvEnv RefLayout.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list03nat37Corelib7Numbers7BinNumsi34Npos35stdpp9bitvectorbdefinitionsk32bv79OSSVerify6Proofsaboost_jsonafuzz_parse3libeRefStartupDefs4FPX1~~~~~~m5h0after_last_slash3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutrffat_random_bytesrf9ed_random37Corelib5Lists7ListDefhh13nth79OSSVerify6Proofsaboost_jsonafuzz_parse3libeRefStartupDefs4Defs~~~~~~hif2rbk37Z_to_bv46Stdlib6ZArith6BinInt1Zho53subk3bbv_unsignedho53add06lengthho53mulho56of_nat69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7ArgvEnv~~~~~~ht25argcN69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~ih5ccat_argv_ptr03nilhif4pn_w69OSSVerify6Proofsaboost_jsonafuzz_parse3libeRefStartupDefs~~~~~~imccprogname_offrfdat_random_ptr06option3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsit5h0word_to_le_bytesih56wbytes04Nonehif6auxv_whif6envp_whifaprogname_whif6argc_whif6argv_whif8aux_basehif5rnd_w69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7ZStores~~~~~~jnc5zeros04conshif6D_tlsAhif6D_tlsBhif3rbn3h5LinuxProcessSemanticsfLinuxProcessSem6BvBaseju0dbytes_le_to_Zhifccanary_byteshif8canary_whif5D_cxxhif4D_fdhif6D_libchif5D_ssphif5D_tls37Corelib4Init5Logickm92eqhh16firstnhh15skipnrf9EntryDraw" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation RPH := Plain.M.phdrs.

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Fixpoint after_last_slash (s : list byte) (i acc : nat) : nat :=
  match s with
  | [] => acc
  | b :: s' => after_last_slash s' (S i) (if bv_eqb b (Z_to_bv 8 47) then S i else acc)
  end.
Definition progname_off : ltac2:(zQ "40!h8!he!jc!m0>1s@1$0@1$3@1$2#8$1") := ltac2:(zQ "40!h8!jc!qb!m0\1s@1$0@1$3@1$1#8@3$2^1N0N0").

End FPX1.

Section Defs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.          (* [comment removed for export] *)
  Variable rnd : ltac2:(zQ "10!kp6$0").    (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition rb : ltac2:(zQ "30!h8!jc!m0@1$0@1$2@1$1#8") := ltac2:(zQ "20!v3!hg5@1$0@1$1?3rnd").
  Definition rbn : ltac2:(zQ "30!he!jc!m0>1i$0@1$2@1$1#8") := ltac2:(zQ "60!jc!he!hi8!hn5!hnb!m0\1i$1@4$2@1$5@1$0#8^1$3@2$4@1$0#8Z").

  (* [comment removed for export] *)
  Definition aux_base : ltac2:(zQ "20!jc!m0@1$1@1$0#k0") := ltac2:(zQ "40!jc!hpd!hnb!hq4@2$2@1$0#k0@2$1@2$3@1$0#k0?3sp0+hn0").
  (* [comment removed for export] *)
  Definition argv_w : ltac2:(zQ "20!jc!m0@1$1@1$0#k0") := ltac2:(zQ "40!jc!hr2!hnb!hq4@2$2@1$0#k0@2$1@2$3@1$0#k0?3sp0+8").
  Definition envp_w : ltac2:(zQ "20!jc!m0@1$1@1$0#k0") := ltac2:(zQ "90!jc!hr2!hr9!h8!hs1!hs8!hnb!m0!hq4@2$6@1$0#k0@2$1@2$1@2$8@1$0#k0?3sp0+h0@2$4+8@1$5@2$2@1$3@1$7@1$0#8?2av").
  Definition auxv_w : ltac2:(zQ "20!jc!m0@1$1@1$0#k0") := ltac2:(zQ "90!jc!hr2!hr9!h8!hs1!hs8!m0!hnb!hq4@2$7@1$0#k0@2$1@2$1@2$1@2$8@1$0#k0?3sp0+h8@2$4+8@1$5@2$2@1$3@1$6@1$0#8?2av@2$4+8@1$5@2$2@1$3@1$6@1$0#8?2ev").
  Definition argc_w : ltac2:(zQ "20!jc!m0@1$1@1$0#k0") := ltac2:(zQ "10!igc@1$0?2av").
  (* [comment removed for export] *)
  Definition pn_w : ltac2:(zQ "20!jc!m0@1$1@1$0#k0") := ltac2:(zQ "10!ikf@4$0?3sp0?2av?2evN0").
  Definition progname_w : ltac2:(zQ "20!jc!m0@1$1@1$0#k0") := ltac2:(zQ "b0!jc!m0!h8!ilf!hi8!im4!iqd!hr2!hs8!hnb!hq4@2$9@1$0#k0@2$7@2$a@1$0#k0$5@1$8@1$6@4$4@1$2@1$1@1$0#8N0?2av@1$3@1$1@1$0#8").
  (* [comment removed for export] *)
  Definition rnd_w : ltac2:(zQ "20!jc!m0@1$1@1$0#k0") := ltac2:(zQ "10!ird@3$0?3sp0?2av?2ev").

  (* [comment removed for export] *)
  Definition D_libc : ltac2:(zQ "30!jc!m0!isd>0@1$1@1$0#k0@1$2@1$1@1$0#8") := ltac2:(zQ "a0!jc!hnb!jgc!ji1!m0!jib!jj1!jjb!im4!jk5@3$3@3$3@3$3@3$3@3$3@3$3\0@1$4@1$0#k0@1$5@1$4@1$0#8@2$1@1$0#k0+hgrlu8@2$2N8$7@2$1@1$0#k0+hirpl0@2$2N8$6@2$1@1$0#k0+hirpr0@2$2N8?2hw@2$1@1$0#k0+hirpn8@2$2N8@2$1@1$0#k0+hgg0@2$1@1$0#k0+hirpk0@2$2N8$8@2$1@1$0#k0+hirpj8@2$2N8$9").      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition J_lsm : ltac2:(zQ "31!jc!m0!isd&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1J~0~0") := ltac2:(zQ "a0!jc!hnb!jgc!ji1!hpd!hq4!m0!isd!jl3!jld\1J>0@1$6@1$0#k0@1$7@1$6@1$0#8@3$3@3$3@3$3@3$3@3$3@3$3@3$3@3$3^1@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+8@2$2N8@2$1@1$0#k0Z@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+h0@2$2N8@2$1@1$0#k0Z@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+h8@2$2N8@2$1@1$0#k0Z@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+i0@2$2N8@2$1@1$0#k0Z@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+i8@2$2N8@2$1@1$0#k0+tqglc@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+j0@2$2N8$9@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+j8@2$2N8$8@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+k0@2$2N8@2$1@1$0#k0+knjt0").

  (* [comment removed for export] *)
  Definition J_aux : ltac2:(zQ "31!jc!m0!isd&>0@1$1@1$0#k0@1$2@1$1@1$0#8>2Jf~0~0") := ltac2:(zQ "b0!jc!hnb!ji1!jgc!hpd!hq4!m0!isd!jm7!jn3!jr6\2Jf>0@1$6@1$0#k0@1$7@1$6@1$0#8@3$2@3$2@3$2@3$2@3$2@3$2@3$2@3$2@3$2@3$2^1$8@1$aNhj0@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+hl8@2$3N8@2$1@1$0#k0+hggk0@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+hl0@2$3N8@2$1@1$0#k0+j8@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+hk8@2$3N8@2$1@1$0#k0+a@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+v0@2$3N8?2hw@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+hk0@2$3N8@2$1@1$0#k0+hgg0@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+hh8@2$3N8?3uid@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+hh0@2$3N8?3uid@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+r8@2$3N8@2$1@1$0#k0Z@2$1@1$0#k0@2$4@2$5@1$0#k0?3sp0+q8@2$3N8$9").                  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_tlsA : ltac2:(zQ "31!jc!m0!isd&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1D~0~0") := ltac2:(zQ "80!jc!hnb!ji1!jgc!m0!jrf!ilf!isd\1D>0@1$4@1$0#k0@1$7@1$4@1$0#8@3$2@3$2@3$2@3$2@3$2@3$2@3$2@3$2@3$2@3$2^1@2$1@1$0#k0+hirmu0@2$3N8@2$1@1$0#k0Z@2$1@1$0#k0+hirmv0@2$3N8@2$1@1$0#k0Z@2$1@1$0#k0+hirmu8@2$3N8@2$1@1$0#k0+8@2$1@1$0#k0+hirpm0@2$3N8@2$1@1$0#k0+u0@2$1@1$0#k0+hirpm8@2$3N8@2$1@1$0#k0+8@2$1@1$0#k0+hgrms8@2$3N8@2$1@1$0#k0Z@2$1@1$0#k0+hgrmr0@2$3N8@2$1@1$0#k0+hgrms8@2$1@1$0#k0+hgrlv0@2$3N8@2$1@1$0#k0+hgrlv0@2$1@1$0#k0+hirpk8@3$5@1$4@1$0#8@2$1@1$0#8+1@1$6@1$4@1$0#8@2$1@1$0#k0+hgrmh8@2$3N4@2$1@1$0#k0+2").        (* [comment removed for export] *)

  Definition D_tlsB : ltac2:(zQ "31!jc!m0!isd&>0@1$1@1$0#k0@1$2@1$1@1$0#8>3tid@1$1@1$0#k0>1D~0~0") := ltac2:(zQ "61!jc!hnb!jgc!ji1!m0!isd&@2$2N8@2$1@1$0#k0+hgrlv0\3tid@1$4@1$0#k0\1D>0@1$4@1$0#k0@1$5@1$4@1$0#8@3$3@3$3@3$3@3$3@3$3@3$3^1@2$1@1$0#k0+hgrmh0@2$2N4^2@2$1@1$0#k0+hgrmo8@2$2N8@2$1@1$0#k0+hirpo0@2$1@1$0#k0+hgrmm8@2$2N8@2$1@1$0#k0+hgrmm8@2$1@1$0#k0+hgrlv8~0@2$1@1$0#k0+hgrmg0~0@2$1@1$0#k0+hgrmg8@2$2N8@2$1@1$0#k0Z").        (* [comment removed for export] *)

  Definition D_tls : ltac2:(zQ "31!jc!m0!isd&>0@1$1@1$0#k0@1$2@1$1@1$0#8>3tid@1$1@1$0#k0>1D~0~0") := ltac2:(zQ "50!jc!m0!isd!js5!jsf\3tid@1$1@1$0#k0\1D>0@1$1@1$0#k0@1$2@1$1@1$0#8@2$4^2@1$3^1").

  (* [comment removed for export] *)
  Definition J_tls : ltac2:(zQ "31!jc!m0!isd&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1J~0>2ra@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0~0") := ltac2:(zQ "80!jc!m0!jgc!ji1!hpd!hnb!hq4!isd\1J>0@1$1@1$0#k0@1$7@1$1@1$0#8\2ra@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0@3$3@3$3@3$3@3$3@3$3@3$3@3$3^8@2$5@1$0#k0@2$4@2$6@1$0#k0?3sp0+hq8@2$2N8^7@2$5@1$0#k0@2$4@2$6@1$0#k0?3sp0+hr0@2$2N8^6@2$5@1$0#k0@2$4@2$6@1$0#k0?3sp0+hr8@2$2N8^5@2$5@1$0#k0@2$4@2$6@1$0#k0?3sp0+hs0@2$2N8^4@2$5@1$0#k0@2$4@2$6@1$0#k0?3sp0+hs8@2$2N8^3@2$5@1$0#k0@2$4@2$6@1$0#k0?3sp0+ht0@2$2N8^2@2$5@1$0#k0@2$4@2$6@1$0#k0?3sp0+ht8@2$2N8^1").

  (* [comment removed for export] *)
  Definition canary_bytes : ltac2:(zQ "30!h8!jc!m0@1$0@1$2@1$1#8") := ltac2:(zQ "60!jc!m0!jrf!jt9!ilf!hnb@3$2@1$1@1$0#8@1$3N0@3$2@1$1@1$0#8@2$5@1$0#8Z@3$2@1$1@1$0#8@1$3N2@3$2@1$1@1$0#8@1$3N3@3$2@1$1@1$0#8@1$3N4@3$2@1$1@1$0#8@1$3N5@3$2@1$1@1$0#8@1$3N6@3$2@1$1@1$0#8@1$3N7@1$4@1$1@1$0#8").
  Definition canary_w : ltac2:(zQ "20!jc!m0@1$1@1$0#k0") := ltac2:(zQ "40!jc!kgf!ki0!hnb@2$3@1$0#k0@1$1$2").
  Definition D_ssp : ltac2:(zQ "31!jc!m0!isd&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1D~0~0") := ltac2:(zQ "a0!jc!m0!jrf!jt9!hnb!ji1!ilf!isd!jgc!kj0\1D>0@1$1@1$0#k0@1$7@1$1@1$0#8@3$5@3$5@3$5@3$5^1@2$4@1$0#k0+hirmv8@3$2@1$1@1$0#8@1$3N0@3$2@1$1@1$0#8@1$3N1@3$2@1$1@1$0#8@1$3N2@3$2@1$1@1$0#8@1$3N3@1$6@1$1@1$0#8@2$4@1$0#k0+hirmvc@3$2@1$1@1$0#8@1$3N4@3$2@1$1@1$0#8@1$3N5@3$2@1$1@1$0#8@1$3N6@3$2@1$1@1$0#8@1$3N7@1$6@1$1@1$0#8@2$4@1$0#k0+hirmv9@3$2@1$1@1$0#8@2$4@1$0#8Z@1$6@1$1@1$0#8@2$4@1$0#k0+hgrmq8@2$8N8$9").       (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_fd : ltac2:(zQ "31!jc!m0!isd&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1D~0~0") := ltac2:(zQ "70!jc!m0!hnb!jrf!ilf!isd!ji1\1D>0@1$1@1$0#k0@1$5@1$1@1$0#8@3$6^1@2$2@1$0#k0+vprr0@3$3@1$1@1$0#8@2$2@1$0#8+1@1$4@1$1@1$0#8").

  (* [comment removed for export] *)
  Definition D_cxx : ltac2:(zQ "31!jc!m0!isd&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1D~0~0") := ltac2:(zQ "60!jc!hnb!jgc!ji1!m0!isd\1D>0@1$4@1$0#k0@1$5@1$4@1$0#8@3$3@3$3@3$3@3$3@3$3@3$3^1@2$1@1$0#k0+hgpuu8@2$2N4@2$1@1$0#k0+1@2$1@1$0#k0+hgpsm0@2$2N4@2$1@1$0#k0Z@2$1@1$0#k0+hgpuu8@2$2N4@2$1@1$0#k0+2@2$1@1$0#k0+hgpsm4@2$2N4@2$1@1$0#k0+1@2$1@1$0#k0+hgpuu8@2$2N4@2$1@1$0#k0+3@2$1@1$0#k0+hgpsm8@2$2N4@2$1@1$0#k0+2").     (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_main : ltac2:(zQ "30!jc!m0!isd>3tid@1$1@1$0#k0>0@1$1@1$0#k0@1$2@1$1@1$0#8") := ltac2:(zQ "70!jc!kjc!kk5!kkd!kl7!km0!m0\3tid@1$6@1$0#k0@1$1@1$2@1$4@2$5^1$3").

  Lemma firstn4_rb : ltac2:(zQ "90!jc!m0!jrf!jt9!h8!ilf!knd!ko3!hn5@3$6@1$4@1$1@1$0#8@3$7@1$1@1$0#8N4$8@3$2@1$1@1$0#8@1$3N0@3$2@1$1@1$0#8@1$3N1@3$2@1$1@1$0#8@1$3N2@3$2@1$1@1$0#8@1$3N3@1$5@1$1@1$0#8").
  Proof. reflexivity. Qed.
  Lemma firstn4_skipn4_rb : ltac2:(zQ "a0!jc!m0!jrf!jt9!h8!ilf!knd!ko3!kod!hn5@3$6@1$4@1$1@1$0#8@3$7@1$1@1$0#8N4@3$8@1$1@1$0#8N4$9@3$2@1$1@1$0#8@1$3N4@3$2@1$1@1$0#8@1$3N5@3$2@1$1@1$0#8@1$3N6@3$2@1$1@1$0#8@1$3N7@1$5@1$1@1$0#8").
  Proof. reflexivity. Qed.

End Defs.
(* [comment removed for export] *)
