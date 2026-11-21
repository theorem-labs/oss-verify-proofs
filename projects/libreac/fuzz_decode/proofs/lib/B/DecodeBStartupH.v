(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the start-up certificate of fuzz_decode's ASan+UBSan image (B) in the exact form of
   lib/B/DecodeBClose.v's Section hypothesis H_STARTUP (a working branch,
   DecodeBClose.v:158-170), with its free Section variable HS_ok bound to lib/B/YB1n.v's HS_ok (the donor's
   cgif_file_fuzzer lib/YB1n.v:44-51, as DecodeBClose.v:137-140 says it is bound when the core lands).
   proves no function (kind: start-up facts): it restates lib/B/YB1n.v:52 tfib_startup_T1 at DecodeBClose's names
   (segs = decodesegsB0, DAU.M.init_pc / DAU.M.phdrs, target_alloc_limit, mkProcInput_full ... false Sv48 ...), each
   of which is by definition the YB1n name (lib/A/DecodeTFIB.v:27 decodesegsB0, YB1h.v:18-19 TSEGS / TPH,
   lib/B/YA02.v:19 LIMIT, :63 inp). *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (changed H_STARTUP_stmt, dec_H_STARTUP). *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_decode.images Require AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK15 YK18 YM05 YO09 YO06.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require YA02 YB1h YB1n.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
Module DAU := OSSVerify.libreac.fuzz_decode.images.AsanUbsan.

Local Notation segs := decodesegsB0.

(* DecodeBClose.v's H_STARTUP, with its Section variable HS_ok as a parameter, as lib/A/DecodeStartupH.v at
   LPS 727298f3 (lib/B/YB1n.v tfib_startup_T1). *)
Definition H_STARTUP_stmt
  (HS_ok : nat -> word -> EntryDraw -> word -> word -> list (list byte) -> list (list byte) -> Fs.Fs ->
           InputStream -> word -> word -> word -> list word -> NetQueue -> word -> word -> InputStream -> Fs.Fs ->
           KernelBuild -> list byte -> bool -> Fs.Fs -> config -> Prop) : Prop :=
  forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs)
    (stdin : InputStream) (uid gid hw : word) (groups : list word) (net : NetQueue) (nofile sigmask : word)
    (urnd : InputStream) (tmp : Fs.Fs) (kb : KernelBuild) (execfn : list byte) (sdef : bool),
  valid_sp sp -> valid_brk segs brk0 -> valid_mmap_base mbase -> valid_argv argv -> valid_envp envp ->
  entry_stack_fits sp argv envp -> valid_id uid -> valid_hwcap hw -> valid_nofile nofile ->
  valid_sigmask (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) ->
  valid_launch (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) ->
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
    (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) ->
  forall T : TSet, T [] ->
  (forall h c, HS_ok h sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef
    (fs_seed_tmp fs tmp) c -> srealizes segs c T) ->
  srealizes segs (init_config segs DAU.M.init_pc DAU.M.phdrs sp brk0 mbase rdraw target_alloc_limit
    (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef)) T.

Theorem dec_H_STARTUP : H_STARTUP_stmt YB1n.HS_ok.
Proof. exact YB1n.tfib_startup_T1. Qed.
