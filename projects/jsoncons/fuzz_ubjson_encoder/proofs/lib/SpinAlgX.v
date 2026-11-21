(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs; the read-only-backing form of the system-call steps; the BMode context; the model's access_ok checks; imports. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import SimInv ExitSim CatSim ShapeAlg DivergeSim SpinAlg.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_SpinAlgX () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg8wr_indexC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg8srz_nodeC13~~~I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyK47Corelib4Init9Datatypes4list01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim6fdchanC13~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall4fd32C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprK47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ms_read_bytesC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim;buf_modeledC13~~~I47Corelib4Init5Peano2le00C47Corelib5Lists7ListDef6firstnC4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0C4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg9srealizesC13~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event02I47Corelib4Init5Logic3and00C47Corelib4Init6Specif9proj1_sigC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg7wr_fullC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg=node_write_chC13~~~K47Corelib4Init6Specif3sig01K47Corelib4Init5Logic3and01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg:t_write_chC13~~~C47Corelib4Init9Datatypes6lengthI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem3Run;SpuriousCfg00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib7Numbers7BinNums8positive03C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I47Corelib4Init6Specif3sig00".
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Common.Cfg Require RomBase RomWrite.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section BmKitW. Context {bmK : BMode}.
Lemma srz_write_ch : forall segs scfg ms model fd ch x8 buf T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model -> fd32 fd = fd ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (* the range [vfs_write]'s [access_ok] accepts; see [ShapeAlg.node_write_ch] *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     srealizes segs scfg
       (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
  srealizes segs scfg (mkCfg ms model) (t_write_ch ch buf T).
Proof.
  intros segs scfg ms model fd ch x8 buf T Hh Hlazy Hfdc H32 Hsvc Hno Hg Hr Hok Hbm Hnb Hc.
  unfold t_write_ch.
  apply (srz_node segs scfg (mkCfg ms model) (wr_index buf)
           (fun i => map (WriteEv ch) (firstn (proj1_sig i) buf))
           (fun i => mkCfg (advance_past_svc
                              (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                           model)
           (fun _ => T) (wr_full buf Hnb)).
  - eapply node_write_ch; eassumption.
  - eapply RomWrite.write_ch_rob; eassumption.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.

End BmKitW.
