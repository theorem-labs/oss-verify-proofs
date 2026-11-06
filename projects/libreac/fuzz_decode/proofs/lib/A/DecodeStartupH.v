(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the start-up certificate of fuzz_decode's ASan image (A) in the exact form of
   lib/A/DecodeClose.v's Section hypothesis H_STARTUP (a working branch 45061c42804,
   DecodeClose.v:158-171), with its free Section variable HS_ok bound to lib/A/AB1n.v's HS_ok (the donor's
   cgif_file_fuzzer lib/A/AB1n.v:44-51, as DecodeClose.v:137-139 says it is bound when the core lands).
   proves no function (kind: start-up facts): it restates lib/A/AB1n.v:52 tfib_startup_T1 at DecodeClose's names
   (segs = decodesegs0, DAs.M.init_pc / DAs.M.phdrs, target_alloc_limit, mkProcInput_full ... false Sv48 ...), each
   of which is by definition the AB1n name (AB1h.v:19-20 TSEGS / TPH, Reusable/YA02.v:20 LIMIT, :64 inp). *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_decode.images Require Asan.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK15 YK18 YM05 YO09 YO06.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YA02.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require AB1h AB1n.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
Module DAs := OSSVerify.libreac.fuzz_decode.images.Asan.

Local Notation segs := decodesegs0.

(* DecodeClose.v:161-171 H_STARTUP, verbatim, with its Section variable HS_ok as a parameter *)
Definition H_STARTUP_stmt
  (HS_ok : nat -> word -> EntryDraw -> word -> list (list byte) -> list (list byte) -> word -> word ->
           Fs.Fs -> config -> Prop) : Prop :=
  forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs)
    (stdin : InputStream) (uid gid : word) (groups : list word) (net : NetQueue) (nofile sigmask hw : word)
    (urnd : InputStream) (tmp : Fs.Fs),
  valid_sp sp -> valid_brk segs brk0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  valid_id uid -> valid_hwcap hw ->
  forall T : TSet, T [] ->
  (forall h c, HS_ok h sp rdraw brk0 argv envp uid hw (fs_seed_tmp fs tmp) c -> srealizes segs c T) ->
  srealizes segs (init_config segs DAs.M.init_pc DAs.M.phdrs sp brk0 mbase rdraw target_alloc_limit
    (mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd tmp)) T.

Theorem dec_H_STARTUP : H_STARTUP_stmt AB1n.HS_ok.
Proof.
  intros sp rdraw brk0 mbase argv envp fs stdin uid gid groups net nofile sigmask hw urnd tmp
    Hsp Hbrk Hva Hve Hfit Huid Hhw T HT HH.
  exact (AB1n.tfib_startup_T1 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp
    Hsp Hbrk Hva Hve Hfit Huid Hhw T HT HH).
Qed.
