(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_pw.fuzz_link.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require ZTraceSpec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK15 YK18 YK0c YK0e YK09 YA0c YA0e YA01 YA02.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB12 AB1h AB01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0f YG00 YG01 YG0n YG0d YK04 YA0i YA0n YCbq YI16 YC5d YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFile LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m ACeg AD1v AD1w AD1x AD1i AD1u AD1p.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance ZTraceSpec.checksum_shape.
(* The ASan image's sink head (AMemFile.v link_asink_head, ofl_head 0x652308), passed by name. *)
Definition link_drv_SK : YI16.sink_head := link_asink_head.
#[local] Instance link_drv_head : @pcap_head link_drv_SK := eq_refl.
(* The float-state invariant of the driver's call loop: a zero rounding mode (YK0o.v frm_zero), true at the start state
   (YK0o.v fp_frm_zero_fx0) and at every return of LLVMFuzzerTestOneInput (LinkEntry.v tfib_lib_contract_xf). *)
Definition link_drv_P (f : YK11.FPState) : Prop := YK0o.frm_zero (@fp_csr f).
Section b. Context {rc : YM05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis HB : PcapSyms B.
Hypothesis AMALLOC : amalloc_realizes tfibsegs B.
Hypothesis AFREE : forall fx : YK11.FPState, afree_realizes (fx := fx) tfibsegs B.
Hypothesis AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis ARDCHK : aread_check_stmt B.
(* link's program contract in its exists-fx' form, for every entry float state (LinkEntryA.v). *)
Hypothesis LIBX : tfib_lib_contract_xf_all_A link_drv_SK B ameter_triv (fun _ => 0) (fun _ => 0).
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame_tfa xst.
Hypothesis PF1 : forall fx : YK11.FPState, printf_first_tfa (fx := fx) B xst.
Hypothesis PFN : forall fx : YK11.FPState, printf_next_tfa (fx := fx) B xst.
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis ESTI : est_img_tfa est.
Hypothesis ESTF : est_frame_tfa est.
Hypothesis FWS : fwrite_site_tfa B est.
Hypothesis RFS : refused_site_tfa B est.
Hypothesis FPO : fprintf_s_site_tfa B est 0x1d858 (strB "cli: cannot open "%string) nlB.
Hypothesis FPR : fprintf_s_site_tfa B est 0x1d86d (strB "cli: read error on "%string) nlB.
Hypothesis FPU : fprintf_s_site_tfa B est 0x15903 (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
Hypothesis EXS : forall fx : YK11.FPState, exit_site_tfa (fx := fx) B est xst.
(* The exit leaf with the memory FILE on musl's open-file list (AD1w.v exit_file_tfa). *)
Hypothesis EXITF : forall fx : YK11.FPState, exit_file_tfa (fx := fx) B xst.
Hypothesis WROOM : (LINK_CALLS_MAX * LINK_WILD_PER_CALL <= u_wmax (as_universe B))%nat.
Definition drv_mainX_stmt : Prop :=
forall (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput) (h : nat) (ch : acs) (E : env) (R : bvmap 5 word)
(FULL : word -> option byte) (model : Model),
valid_sp sp -> valid_brk TSEGS brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
HS_tfib h = Some ch ->
cs_ok TSEGS TFIB YA02.LIMIT (YA02.TOP sp)
(YA02.SINV0 TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model ->
(forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) n) ->
(forall a, YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) E a = true ->
FULL a = wrap_mem TPH sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw a) ->
srealizes TSEGS (cfg_of TSEGS R (pc ch) FULL model) (CLOSEDX inp).
(* The driver at P := link_drv_P, P0 := fp_frm_zero_fx0; the slot at every fx with P is the contract's exists-fx'
   form at a zero rounding mode (LinkEntry.v tfib_lib_contract_xP_of_xf; the rounding-mode premise is P fx itself). *)
Lemma DRV_MAINX : drv_mainX_stmt.
Proof.
exact (tfib_drv_main (SK := link_drv_SK) link_drv_P YK0o.fp_frm_zero_fx0 B HB AMALLOC (fun fx _ => AFREE fx) AICPY ARDCHK
ameter_triv (fun _ => 0) (fun _ => 0) (fun _ _ => I)
(fun fx (Hz : link_drv_P fx) => @tfib_lib_contract_xP_of_xf fx rc link_drv_SK tfibsegs PCAP_RLO PCAP_RHI
  A_LLVMF RA_LLVMF A_EMPTY LLVMF_STK G_HARNESS B ameter_triv (fun _ => 0) (fun _ => 0) link_amf LA_NUL Hz (LIBX fx))
xst XFR (fun fx _ => PF1 fx) (fun fx _ => PFN fx) est ESTI ESTF FWS RFS FPO FPR FPU (fun fx _ => EXS fx) (fun fx _ => EXITF fx) WROOM).
Qed.
End d.
End b.
