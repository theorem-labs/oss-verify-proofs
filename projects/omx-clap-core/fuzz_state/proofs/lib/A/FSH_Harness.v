(* fs program part: the ASan contract of fs's LLVMFuzzerTestOneInput in the donor's form, cgif_file lib/A/ACfn.v:59-69
   tfib_lib_contract_x (its pre tfib_lib_pre_x :33-46 and post tfib_lib_post_x :47-58), plus fs's static-state invariant
   (fuzz/alloc.c's statics: g_fail_at = SIZE_MAX, g_live back to its entry value, g_count grows by at most FS_CNT_LIB),
   exactly as a Theorem Labs lane builds fm_lib_contract_x. The image facts fs's runtime calls take come from fs_img_facts B
   (FSH_Rt.v), a constant fact proved once for fs's TfibB; the zero stack shadow from AR (FSH_Gen.v stk_sh0). Instantiated
   at LS := checksum_shape (fs's plain lib shape, LIBK pl fs K = K (LL 0 fs []), lib/ZTraceSpec.v:14-20, the shape fs's
   plain_rz_of_contracts_R (lib/AgreeTop.v:16) runs at), MT := ameter_triv, XM_LIB = XN_LIB := XL0, RLO..RHI := FS_RLO ..
   FS_RHI (fs.asan's .data.rel.ro start .. .got end). The constants inside tfib_lib_pre_x / tfib_lib_post_x are
   A/ACfn.v:26-28, now fs.asan's (A_LLVMF 0x80f1c = FS_LLVMF, RA_LLVMF 0x80e18 = FS_RA_LLVMF, A_EMPTY 0x5da5a0 =
   FS_EMPTY; relocated by S0 in this branch, because the raw copy's cgif_file values made this contract false over
   fs.asan), with EV_LIB 2000 = FS_EV_LIB, LIVE_LIB 2 ^ 33 and LLVMF_STK 32768 unchanged (policy constants; fs's
   STK_LLVMF is 18555). U = [] at entry and exit: fs frees every block on every path (Permutation of ablocks in
   tfib_lib_post_x), so no reader head is live outside the call. Statement only.
   Ported from: a Theorem Labs lane's proofs/omx-clap-core/fuzz_manifest/lib/A/FMH_Harness.v (a working branch e48bf3cce32, with the
   text of 706affbdbe6 / 3e0aa997be6: stk_sh0, rom_view, fm_canary out of the premises). Design: a Theorem Labs lane's design/HARNESS.md
   section 2. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YI04 YI16 YK06 YO09 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v ACfn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSH_YC20 FSH_Gen FSH_Base FSH_Rt.
Import ListNotations.
Local Open Scope Z_scope.
(* IMPLICIT-INSTANCE GUARD (a Theorem Labs lane 22:13Z): A/AE2k.v:45 `#[export] Instance tfib_sink_head` carries IMAGE A's musl ofl_head
   (0x5fb628) and this file's closure reaches AE2k (through ACfn). A site that leaves SK to inference would get A's cell
   (wrong for build B) or the plain one (removed in FSH_Gen.v). Removed here, #[global] so it holds wherever this file
   is loaded; AE2k is RELOC's and is not edited. Caveat: an explicit `Import AE2k` AFTER this file re-activates its
   export instance in that file; sites must pass SK with `@` (A: AE2k.tfib_sink_head, B: FSH_Base.fsB_sink_head). *)
#[global] Remove Hints AE2k.tfib_sink_head : typeclass_instances.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
#[local] Abbreviation segs := tfibsegs.

Definition fs_lib_contract_x : Prop :=
  forall ly S (W : world segs) (regs : bvmap 5 word) mem md p n pl M (K : lleaf -> TSet) live cnt,
  AI segs (w_H W) (w_A W) md ->
  tfib_lib_pre_x B MT XM_LIB FS_RLO FS_RHI regs ly S W mem md p n pl M ->
  fs_stat segs W mem live cnt -> 0 <= cnt -> cnt + FS_CNT_LIB < 2 ^ 63 -> live + ACfn.LIVE_LIB < 2 ^ 64 ->
  (forall (l : lleaf) (W' : world segs) (c' : config),
     wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
     (exists ly' S' regs' mem' md' k cnt',
        c' = cfg_at segs RA_LLVMF regs' mem' md' /\
        tfib_lib_post_x B MT XN_LIB regs ly S W mem md p n M l ly' S' W' regs' mem' md' k /\
        fs_stat segs W' mem' live cnt' /\ cnt <= cnt' <= cnt + FS_CNT_LIB) ->
     srealizes segs c' (K l)) ->
  srealizes segs (cfg_at segs A_LLVMF regs mem md) (LIBK pl (m_fs md) K).
End a.
Definition fs_lib_contract_x_all {rc : YM05.RunCeil} {LS : lib_shape} (B : asyms) (MT : ameter_ops)
  (XM_LIB XN_LIB : Z -> Z) : Prop :=
  forall fx : YK11.FPState, @fs_lib_contract_x fx rc LS B MT XM_LIB XN_LIB.
