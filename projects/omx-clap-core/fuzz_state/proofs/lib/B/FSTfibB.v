(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from the TFIB_T definition of proofs/cgif/cgif_file_fuzzer/lib/YZ03.v (c8557374ad2e) for fuzz_state's ASan+UBSan image and the plain side's library shape ag_shape checksum_shape; module paths changed. *)
(* What the ASan+UBSan side of fuzz_state's two asan_ubsan statements proves: from every valid start, the
   asan-ubsan build realizes the same trace set SPECX as the plain build (lib/Reusable/YK18.v srealizes, no cut).

   Open obligations of TFIB_T_B (it is a Section hypothesis of lib/B/FSTopB.v until they are discharged):
   - the ASan core of cgif_file_fuzzer (runtime, allocator model, start-up, driver, composition) relocated to
     fs.asan-ubsan (RELOC lane);
   - fuzz_state's program part: LLVMFuzzerTestOneInput's ASan contract in the form of cgif_file lib/A/ACfn.v:59
     tfib_lib_contract_x, one walk per callee (ENTRY a Theorem Labs lane and the function lanes);
   - open inputs INSIDE TFIB_T_B, each a named hypothesis with an owner (table 'Named hypotheses' in
     (internal path)); none is a hypothesis of lib/B/FSTopB.v's theorems:
     * FS_AREALLOC_B: fs's ASan realloc contract in the B build (call target __wrap_realloc 0x530e8, which jumps to
       __interceptor_realloc 0x534e4, measured from the .symtab of the unstripped twin of the pinned
       fuzz_state.asan-ubsan; trace pc 0x53620 on the malloc_context_size = 30 branch, a Theorem Labs lane 21:37Z). The donor model has no realloc (a Theorem Labs lane,
       premise-check-fuzz_state-port.md section 0: YG0f.v:134-178, YG00.v, YG0d.v:253-276, ACej.v:337, AB1q.v:11).
       Owner a Theorem Labs lane (B twin of lib/A/FSH_ReallocModel.v, a working branch
       a882c264dfa); discharge: a Theorem Labs lane's arealloc_realizes_all (a working branch).
     * FS_DOC_STRS: the two clauses about the document round_trip_document builds (fs.c:229-247), the same program
       fact as in A (owner a Theorem Labs lane, lane READER, lib/A/Prog/FSDocStrs.v); it keeps parse_value off its number
       arm, so strtod is unreachable.
   NOT open: the plain realloc arm. The plain side is fs's own released plain realization (lib/FSPlain.v from
   AgreeTop.v:16 plain_rz_of_contracts_R, fs's YH02.v ms_realloc = Some src0_A_realloc); the donor's YH02.v:20-23
   and YO0d.v:434-444 are not in its closure. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.omx_clap_core.fuzz_state.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK15 YK18 YM05 YO09 YO06.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import ZTraceSpec AgreeShape.
Import ListNotations.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.
Definition fsbsegs0 : list Segment := AsanUbsan.M.loaded_segments.
Definition TFIB_T_B : Prop :=
forall sp brk mbase rnd inp,
valid_sp sp -> valid_brk fsbsegs0 brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes fsbsegs0
(init_config fsbsegs0 AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
(SPECX (LS:=ag_shape checksum_shape) inp).
