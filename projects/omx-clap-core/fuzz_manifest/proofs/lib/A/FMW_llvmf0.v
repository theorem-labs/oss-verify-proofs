(* fm's LLVMFuzzerTestOneInput 0x8091c (fuzz_manifest.c:293-321): the walk's post. The walk proves that from the donor
   library pre (A/ACfn.v tfib_lib_pre_x at MT := ameter_triv, XM := 0, relro FM_RLO..FM_RHI) and fm's static-state
   invariant (fm_stat, FMH_Base.v), the code returns to RA_LLVMF with a0 = 0, the callee-saved registers, the blocks
   and the input bytes as they were, a journal whose footprint is fuzz/alloc.c's statics, and fm_stat again with
   g_count grown by at most CNT_LIB. The rest of tfib_lib_post_x (sink, meta, file system, meter) follows from the
   journal in the harness assembly (G6, FMW_harness.v). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d YCbp YC20.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YK06 YO09 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AF0l ACej FMPstat AE2k ACfn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMH_Fn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* __asan_memcpy, called at 0x80a08 and 0x80a44 *)
Definition FM_asan_memcpy : Z := 0x51a68.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.

Definition llvmf_post (regs : bvmap 5 word) ly S (W : world tfibsegs) mem md (p n live cnt : Z)
  : world tfibsegs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k cnt',
    c' = cfg_at tfibsegs RA_LLVMF regs' mem' md' /\
    ajournal tfibsegs B LLVMF_STK (spZ regs) FM_PSTAT_FP ly S W mem md [] ly' S' W' mem' md' k /\ k <= EV_LLVMF /\
    aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
    Permutation (ablocks B ly' S') (ablocks B ly S) /\
    (forall i, 0 <= i < n -> aview tfibsegs (w_H W') mem' (p + i) = aview tfibsegs (w_H W) mem (p + i)) /\
    fm_stat tfibsegs W' mem' live cnt' /\ cnt <= cnt' <= cnt + CNT_LIB.

(* the walk's premises: the donor library pre at fm's instance and fm_stat *)
Definition llvmf_pre (regs : bvmap 5 word) ly S (W : world tfibsegs) mem md (p n : Z) (pl : list byte) (M live cnt : Z) : Prop :=
  tfib_lib_pre_x B ameter_triv (fun _ => 0) FM_RLO FM_RHI regs ly S W mem md p n pl M /\
  fm_stat tfibsegs W mem live cnt /\ 0 <= cnt /\ cnt + CNT_LIB < 2 ^ 33 /\ live + 2 ^ 9 < 2 ^ 33.
End c.
