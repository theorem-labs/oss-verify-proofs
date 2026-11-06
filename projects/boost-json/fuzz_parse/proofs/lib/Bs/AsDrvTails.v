(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SpecConsts Frame StreamSim FileSim
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymAux Hoare RefPrintfLib LibTail Spec ShapeLaws
  LazyRestrict LazySR LazyFdNodes LazySym.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import RefExitBase RefStdioDefs AsLazyRun AsStdioWrite AsStdioCall AsScLib
  AsPrintfFirst AsSxKit AsExitCas AsExitDefs AsExit AsTailExit AsRefused.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bvhf7Z_to_bv37Corelib4Init5Logickb2eq69OSSVerifyaboost_jsonafuzz_parse6images9AsanUbsan1M~~~~~~m4floaded_segments37Corelib4Init9Datatypesr06option01Z3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticst4dmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem3Runhhb5mkCfg3h5LinuxProcessSemanticsfLinuxProcessSem5Statehl07FdEntryr04Somekb1Ihl09FdChannelhl05Modelhl09fd_lookuphl05m_fdshl04m_fs3h5LinuxProcessSemantics5Riscv7Preludehs85bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9AsRefused~~~~~~hv73rfH79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAsTailExit~~~~~~ijd5exitH69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~io68restrict69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~it14lzok69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~jh24getrjh24mkstjh27seg_rom69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~jm8dhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~jr08realizes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec~~~~~~jv7bmsg_refusedjv75t_diehf2BVhf4BvWf" s.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Tails.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variables (L S Zr : list (word * word)).

  (* [comment removed for export] *)
  Theorem as_refused : ltac2:(zQ "hf0!h9!jc!k1!lf!pe!s8!t1!hgb!hk7!hne!ho9!hp0!hp4!hq1!hqa!hr7!hs0!hue!ij6!ind!is5!jga!jkd!jl5!jld!jpf!jub!kie!kjd!kk6!kkb>4regs@2$h1@1$0#5@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$5@1$1@1$0#8>3msF$7>2mo$d>2sp@1$1@1$0#k0>3can$6>3tid$6>2ro@1$1@1$0#k0>3wpw@1$1@1$0#k0>0@4$h2^9^8^5^4>0@5$h3^9^6^4^3^2>0@3$3@1$1@1$0#k0@2$h6^b@3$hd@1$0#5+4Kv$b@2$he@1$0#5+4@2$2@1$0#k0+mvhjh8>0@5$h5$4?1L?1S?2Zr@2$8^a^9>0@3$3$7@3$h4?1L?1S^b@5$h7?2fx^d@2$2@1$0#k0+rurg4^c@1$h8$4>0@3$3@1$5$9@2$e@1$f^b@2$2@1$0#k0+2@2$a$9@1$c@2$2@1$0#k0+2@4$ha$4$h9@2$8^d^c@2$hc$hb@1$h0^c").
  Proof.
    intros regs mem msF mo sp can tid ro wpw PH XH R4 OK RS Hfd2. unfold t_die.
    apply (as_refused_k L S Zr regs mem msF mo sp can); try assumption; [apply t_exit_has_nil|].
    intros regs' mem' msF' mo' PO OK' SB' HS' RS'.
    rewrite <- (same_but_materialized_fs _ _ SB').
    destruct PH as [R2 Rsp16 RspLo RspHi Rstk Rimg Rgot Rcells Rcan Rcan64 Rsh0].
    destruct PO as [Psp Pra Pa0 Pcs Pframe Pflags Prpos Prend Pwend Pwpos Pwbase Pbuf Pbsz Plock Pcan Pstk].
    apply (tail_exit2 L S Zr regs' mem mem' msF' mo' sp RF_FR tid can ro wpw (Z_to_bv 64 0) (Z_to_bv 64 0));
      try assumption; try (unfold RF_FR; lia).
    - (* [comment removed for export] *) intros a n Ha Hn. apply Pstk; unfold RF_FR in *; lia.
    - rewrite (Pcs 4%bv); [exact R4 | cbn; tauto].
  Qed.
End Tails.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
