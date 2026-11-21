(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: statements written out as text, the launch's channel reader. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc3. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SpecConsts Frame StreamSim FileSim
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymAux Hoare RefPrintfLib LibTail Spec ShapeLaws
  LazyRestrict LazySR LazyFdNodes LazySym.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import RefExitBase RefStdioDefs AsLazyRun AsStdioWrite AsStdioCall AsScLib
  AsPrintfFirst AsSxKit AsExitCas AsExitDefs AsExit AsTailExit AsRefused.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bvhf7Z_to_bv37Corelib4Init5Logickb2eq69OSSVerifyaboost_jsonafuzz_parse6images4Asan1M~~~~~~m4floaded_segments37Corelib4Init9Datatypesqb6option01Z3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticssfdmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem3Runhh65mkCfg3h5LinuxProcessSemanticsfLinuxProcessSem5Statehkb7FdEntryqb4Somekb1Ihkb9FdChannelhkb5Modelhkb9fd_lookuphkb5m_fdshkb4m_fs3h5LinuxProcessSemantics5Riscv7Preludehs35bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9AsRefused~~~~~~hv23rfH79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAsTailExit~~~~~~ij85exitH69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~io18restrict69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~isc4lzok69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~jgd4getrjgd4mkstjgd7seg_rom69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~jm3dhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~jqb8realizes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec~~~~~~jv2bmsg_refusedjv25t_diehf2BVhf4BvWf" s.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation RSEGS := Asan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Tails.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variables (L S Zr : list (word * word)).

  (* [comment removed for export] *)
  (* LPS 75d69e00, the channel-reader premise.  as_refused_k gained
     [m_channel_reader mo = true] (As/AsRefused.v:284), so this application of it was one
     argument short: "Unable to unify is_prefix [] [ExitEv ?code ?fs] \/ ... with
     m_channel_reader mo = true" at As/AsDrvTails.v:38, characters 79-93 (the
     [apply t_exit_has_nil] bullet landed in the reader slot) -- a farm round,
     the source branch, image sha256:2c6b6db8.
     THE PROOF HERE WAS ALREADY PLAIN TEXT, so only the STATEMENT is written out (the old
     encoded one plus the premise after fd_lookup) and `Hrd2` is added to the intros;
     `try assumption` then carries it into as_refused_k.  No blob re-encoded.
     This is the As twin of Bs/AsDrvTails.v:50-68, which carries the same repair; the two
     keep their own addresses.  Constants are this tree's own, from the failing round's own
     environment dump (R4 : getr regs 4 = Z_to_bv 64 7291864 = 0x6f43d8; RS : restrict L S msF
     = mkst regs (Z_to_bv 64 781160) mem (seg_rom RSEGS), 781160 = 0xbeb68 -- the SAME entry pc
     As/AsRefused.v:282 gives as_refused_k, which is the cross-check).
     DONOR, statement and proof, with its branch (rule 23c):
       a donor tree:projects/openssl/echconfiglist_parser/
       proofs/lib/Both/As/AsDrvTails.v:30-45. *)
  Theorem as_refused : forall regs mem msF mo (sp : word) (can tid : Z) (ro wpw : word),
    rfH regs mem sp can -> exitH mem sp tid ro wpw ->
    getr regs 4 = Z_to_bv 64 0x6f43d8 ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (Z_to_bv 64 0xbeb68) mem (seg_rom RSEGS) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    m_channel_reader mo = true ->
    realizes RSEGS (mkCfg msF mo) (t_die msg_refused (m_fs mo)).
  Proof.
    intros regs mem msF mo sp can tid ro wpw PH XH R4 OK RS Hfd2 Hrd2. unfold t_die.
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
