(* fs program part, build B: the ASan contract of fs.asan-ubsan's LLVMFuzzerTestOneInput, the same name and form as
   lib/A/FSH_Harness.v. The pre and post are restated here (A's go through A/ACfn.v:33-58, whose tfibsegs are
   fs.asan's segments), word for word over fs.asan-ubsan's segments and lib/B/FSH_Base.v's FS_LLVMF 0x80f8c, FS_RA_LLVMF 0x80e88,
   FS_EMPTY 0x5daaa0, FS_EV_LIB 2000; the build's sink / meta cells (cgif's A/AE2k.v:50 tfib_K in build A) are the Section
   variable K and the build's sink head the context SK, which RELOC's build-B core instantiates.
   2026-10-29 (a Theorem Labs lane's finding, a Theorem Labs lane 04:51Z): the policy constants now come from lib/B's own YCfn, not
   lib/A/ACfn, so this file's closure no longer reaches image A's AE2k cells (the content test of record); and the
   post journals `(sink_token :: FS_PSTAT_FP)` as A's post has since S0 c5cce359917 and as lib/B/YCfn.v:52 does,
   instead of the pre-c5cce359917 `[sink_token]`.
   Statement only. Port-from: lib/A/FSH_Harness.v (this branch) and cgif_file lib/A/ACfn.v:20-69. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO09 YI16 YE00 YE01 YC5d YM05.
From OSSVerify.omx_clap_core.fuzz_state.images Require AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YCfn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSH_Base FSH_Rt FSPstat.
Import ListNotations.
Local Open Scope Z_scope.
(* IMPLICIT-INSTANCE GUARD (a Theorem Labs lane 22:13Z): A/AE2k.v:45 `#[export] Instance tfib_sink_head` carries IMAGE A's musl
   ofl_head (0x5fb628), and a site that leaves SK to inference would get that cell (wrong for build B) or the plain
   one (removed in FSH_Gen.v). This file's closure NO LONGER REACHES AE2k (2026-10-29: it takes the policy constants
   from lib/B's own YCfn), so there is no hint of A's instance here to remove and the `#[global] Remove Hints
   AE2k.tfib_sink_head` that stood here is gone with the import that made it resolve. The two Fail probes below are
   the standing guard: if any import ever makes a sink instance resolvable in this file, they stop the build.
   Caveat unchanged: an explicit `Import AE2k` AFTER this file re-activates its export instance in that file; sites
   pass SK with `@` (A: AE2k.tfib_sink_head, B: FSH_Base.fsB_sink_head). *)
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* fs.asan-ubsan's loaded segments *)
Definition fsbsegs : list Segment := AsanUbsan.M.loaded_segments.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape} {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable K : asink_syms.
#[local] Abbreviation segs := fsbsegs.
#[local] Abbreviation rd W mem := (mrestrict (w_H W) mem).

(* A/ACfn.v:33-46 at build B *)
Definition fs_lib_pre_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte)
  (md : Model) (p n : Z) (pl : list byte) (M : Z) : Prop :=
  afn_pre segs B YCfn.LLVMF_STK ly S W regs mem md [] /\
  raZ regs = FS_RA_LLVMF /\
  getr regs 10 = w64 p /\ getr regs 11 = w64 n /\
  ((n = 0 /\ p = FS_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) /\
  n = Z.of_nat (length pl) /\ garr8 segs (rd W mem) p (map (fun b : byte => bv_unsigned b) pl) /\
  frames S = [] /\ st_nev S + FS_EV_LIB <= EV_MAX /\ blocks_bytes S + YCfn.LIVE_LIB <= LIVE_MAX /\
  arodata_okS segs B FS_RLO FS_RHI (aview segs (w_H W) mem) /\
  asink_none segs K (rd W mem) md /\
  fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None /\
  Fs.fs_sorted (m_fs md) = true /\
  ameta_inv segs K ly (rd W mem) M /\
  mo_ok MT S (XM_LIB n).
(* A/ACfn.v:47-58 at build B *)
Definition fs_lib_post_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte)
  (md : Model) (p n : Z) (M : Z) (l : lleaf)
  (ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model)
  (k : Z) : Prop :=
  ajournal segs B YCfn.LLVMF_STK (spZ regs) (sink_token :: FS_PSTAT_FP) ly S W mem md [] ly' S' W' mem' md' k /\ k <= FS_EV_LIB /\
  aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
  Permutation (ablocks B ly' S') (ablocks B ly S) /\
  (forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd) /\
  m_fs md' = ll_fs l /\ ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
  asink_none segs K (rd W' mem') md' /\
  ameta_inv segs K ly' (rd W' mem') M /\
  mo_le MT S S' (XN_LIB n) /\
  (forall i, 0 <= i < n -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)).

(* lib/A/FSH_Harness.v's fs_lib_contract_x at build B *)
Definition fs_lib_contract_x : Prop :=
  forall ly S (W : world segs) (regs : bvmap 5 word) mem md p n pl M (K' : lleaf -> TSet) live cnt,
  AI segs (w_H W) (w_A W) md ->
  fs_lib_pre_x regs ly S W mem md p n pl M ->
  fs_stat segs W mem live cnt -> 0 <= cnt -> cnt + FS_CNT_LIB < 2 ^ 63 -> live + YCfn.LIVE_LIB < 2 ^ 64 ->
  (forall (l : lleaf) (W' : world segs) (c' : config),
     wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
     (exists ly' S' regs' mem' md' k cnt',
        c' = cfg_at segs FS_RA_LLVMF regs' mem' md' /\
        fs_lib_post_x regs ly S W mem md p n M l ly' S' W' regs' mem' md' k /\
        fs_stat segs W' mem' live cnt' /\ cnt <= cnt' <= cnt + FS_CNT_LIB) ->
     srealizes segs c' (K' l)) ->
  srealizes segs (cfg_at segs FS_LLVMF regs mem md) (LIBK pl (m_fs md) K').
End a.
Definition fs_lib_contract_x_all {rc : YM05.RunCeil} {LS : lib_shape} {SK : YI16.sink_head} (B : asyms)
  (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (K : asink_syms) : Prop :=
  forall fx : YK11.FPState, fs_lib_contract_x (fx := fx) B MT XM_LIB XN_LIB K.
