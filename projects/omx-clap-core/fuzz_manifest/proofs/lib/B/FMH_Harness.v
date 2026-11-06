(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMH_Harness.v, relocated by b_reloc.py (b7comp): every image
   numeral re-derived by symbol / section / string content, revcheck report (internal path). *)
(* fm program part: the ASan contract of fm's LLVMFuzzerTestOneInput is the relocated donor contract with a library
   invariant, ReusableB/YCfn.v tfib_lib_contract_xI (Reloc.JournalFP; donor cgif_file lib/A/ACfn.v:59 tfib_lib_contract_x),
   instantiated with fm's invariant fm_LI over fuzz/alloc.c's statics: before driver call ci, g_live = 0,
   g_fail_at = SIZE_MAX and g_count <= ci * CNT_LIB (each call restores g_live and g_fail_at and adds at most CNT_LIB to
   g_count). The driver (ReusableB/YD1w.v) asks of fm_LI lib_inv_stable (it depends only on the FM_PSTAT_FP cells) and
   lib_inv_init (the image's initial values: g_fail_at 0xffffffffffffffff in .data, the other three zero-filled .bss;
   computed over fm.asan-ubsan's segments in FMW_bridge.v). The image facts fm's runtime calls take come from
   fm_img_facts B (FMH_Fn.v); the zero stack shadow from AR. Instantiated at LS := checksum_shape (fm's plain lib shape,
   LIBK pl fs K = K (LL 0 fs []), lib/ZTraceSpec.v:14-20), MT := ameter_triv, XM_LIB = XN_LIB := XL0,
   RLO..RHI := FM_RLO..FM_RHI (.data.rel.ro start .. .got end). Statements only. Design: a Theorem Labs lane's design/HARNESS.md
   section 2. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC20 YC5d YI00 YI04 YI16 YK06 YO09 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YCfn YD1w.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base FMH_Rt FMH_Fn.
Import ListNotations.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Local Notation segs := tfibsegs.

(* fm's library invariant before driver call ci *)
Definition fm_LI (ci : Z) (W : world segs) (mem : word -> option byte) : Prop :=
  exists cnt, fm_stat segs W mem 0 cnt /\ 0 <= cnt <= ci * CNT_LIB.

(* what the driver asks of it (A/AD1w.v) *)
Definition fm_LI_stable : Prop := lib_inv_stable fm_LI.
Definition fm_LI_init : Prop := lib_inv_init fm_LI.

Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
(* the harness contract fm's program part proves *)
Definition fm_lib_contract_x : Prop := tfib_lib_contract_xI B MT XM_LIB XN_LIB FM_RLO FM_RHI fm_LI.
End a.
