(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AE2y.v, with its module paths and module names changed; 452 of its 508 lines of code are new or changed and 648 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: relocated from omx-clap-core/fuzz_manifest lib/A/FMgxaSeam.v (a working branch 7e395de08f5) to libreac/fuzz_boxreg.asan: module paths changed; 25 address numerals relocated (port_addr_check 5033540ba83b predict mode, symbol + offset); re-pointed Requires: FMupoison -> lib.A.Rt, FMsnprintfPf -> lib.A.Rt, FMsnprintfShared -> lib.A.Rt, FMsnprintfSx -> lib.A.Rt, FMgxaSeamNorm / FMgxaSeamReady and the FMgxaSeam* kit -> lib.A.Rt; name TfibSyms -> BoxregSyms (1x; boxreg's lib/A/AF0m.v record); GXA symbol keys 0x22e18 / 0x34288 / 0x1029e kept (keys of boxreg lib/A/RT_IImgA.v A_exact :70 / :72, not fm addresses). fm's 7e395de08f5 -> 3e35620c52e change of this file applied (git diff of lib/A/FMgxaSeam.v: GXA (5) in READY, then READY at the per-call store FMgxaSeamNorm.cjnormv ly R over the carve-out list NM.seam_R with FMgxaSeamReady's stack_hull / prefix_hull; the one address numeral in the change is the kept key 0x1029e, port_addr_check 0767e70e074a predict UNRESOLVED-SOURCE). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Rt/FMgxaSeam.v, with its module paths and module names changed; 14 of its 44 lines of code are new or changed and 478 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: relocated from omx-clap-core/fuzz_manifest lib/A/FMgxaSeamFm.v (a working branch 3e35620c52e) to libreac/fuzz_boxreg.asan: module paths changed; 0 address numerals relocated (port_addr_check 0767e70e074a predict mode, symbol + offset); GXA symbol keys 0x22e18 / 0x34288 / 0x7f000400 kept (keys of boxreg lib/A/RT_IImgA.v A_exact, not fm addresses); name TfibSyms -> BoxregSyms (1x; boxreg's lib/A/AF0m.v record); re-pointed Requires: FMupoison, FMsnprintfPf, FMsnprintfShared, FMsnprintfSx, FMgxaSeamDef, FMgxaSeamNorm, FMgxaSeamReady, FMgxaSeam -> lib.A.Rt; FMgxa_mem -> lib.A.RT_gxa_calls_mem; RT_gxa_strnlen -> lib.A.RT_gxa_calls. *)
(* THE GXA SEAM AT fm.asan's MUSL VFPRINTF, CLOSED: FMgxaSeam.fm_vfprintf_seam with every Section
   hypothesis discharged but the ambient ones (the FP state fx, the run ceiling rc, the symbol
   assignment B with its laws and fm's symbols).

   The three interceptor call contracts and their readiness predicates are fm's own
   (RT_gxa_calls_mem.memcpy_stack_contract_A / memset_stack_contract_A at RT_gxa_calls_mem.copy_ready /
   set_ready, RT_gxa_calls.strnlen_stack_contract_A at RT_gxa_calls.strn_ready), all three at
   the image instance RT_IImgA.A_img, the instance fm_vfprintf_seam runs at.  READY, the readiness
   of those three predicates at musl vfprintf's call site, is FMgxaSeamReady.seam_ready_holds.

   No function is proved here and no machine step is walked: this file only instantiates.  New
   file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK04 YK0i YK0s YK14 YK1b YK1a YK18 YP09 YG0n YG00 YG0a YG01 YG0f YG0v YG0d YA0n YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import
FMupoison FMsnprintfPf FMsnprintfShared FMsnprintfSx.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require AF0m.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GX Require G_printf_core_common.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GXA Require G_vfprintf_snf.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import RT_IImgA.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import FMgxaSeamDef.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require
FMgxaSeamNorm FMgxaSeamReady FMgxaSeam.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require RT_gxa_calls_mem RT_gxa_calls.
Import ListNotations.
Local Open Scope Z_scope.

Module GXC := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
Module GVA := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GXA.G_vfprintf_snf.
Module NM := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt.FMgxaSeamNorm.
Module SR := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt.FMgxaSeamReady.
Module FMM := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.RT_gxa_calls_mem.
Module RSN := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.RT_gxa_calls.

#[local] Existing Instance A_img.

Section F. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : AF0m.BoxregSyms B.

Theorem fm_vfprintf_seam_closed :
  forall (K gc gv img_lo img_hi snw fam_lo fam_hi : Z) (cr : list (Z * Z)),
    GVA.VFA_DEPTH <= K -> gc = @sym A_img 0x22e18 -> gv = @sym A_img 0x34288 ->
    snw = @sym A_img GXC.K_SN_WRITE -> img_lo <= 65536 -> @GXC.GLOBALS_TOP A_img <= img_hi ->
    65536 <= fam_lo -> fam_hi <= @sym A_img 0x22e18 -> NM.ro_covered cr ->
    sh_avfprintf_icpt_realizesUx tfibsegs B
      (pf_family_ro pf_fm_piece fam_lo fam_hi) K gc gv img_lo img_hi cr snw (@sym A_img 0x7f000400).
Proof.
exact (FMgxaSeam.fm_vfprintf_seam B LAWS TB FMM.copy_ready FMM.set_ready RSN.strn_ready
         FMM.memcpy_stack_contract_A FMM.memset_stack_contract_A RSN.strnlen_stack_contract_A
         (SR.seam_ready_holds B LAWS TB)).
Qed.

End F.
