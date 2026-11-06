(* Modified by Theorem Labs, 2026-10: relocated from omx-clap-core/fuzz_manifest lib/A/FMsnprintfSeamI.v (a working branch 3e35620c52e) to libreac/fuzz_boxreg.asan-ubsan: module paths changed; 4 address numerals relocated (port_addr_check 0767e70e074a predict mode, symbol + offset); GXA / donor symbol keys kept (0x34288: lib/B/RT_IImgA.v maps that key space); name TfibSyms -> BoxregSyms (1x; boxreg's lib/B/AF0m.v record); re-pointed Requires: FMupoison, FMsnprintfPf, FMsnprintfShared, FMsnprintfSx -> lib.A.Rt; RT_IImgA -> lib.B; FMgxaSeamDef, FMgxaSeamGuard, FMgxaSeamNorm, FMgxaSeam, FMgxaSeamFm, FMsnprintfImg -> lib.B.Rt; FMgxa_mem -> lib.B.RT_gxa_calls_mem; RT_gxa_strnlen -> lib.B.RT_gxa_calls; FMH_Base -> lib.B.Rt.SnprintfFmh. *)
(* THE GXA SEAM AT fm.asan's MUSL VFPRINTF, INSTANTIATED: FMgxaSeam.fm_vfprintf_seam with fm's three interceptor
   call contracts (RT_gxa_calls_mem.memcpy_stack_contract_A, RT_gxa_calls_mem.memset_stack_contract_A,
   RT_gxa_calls.strnlen_stack_contract_A) and their ready predicates, fm's format family pf_family_ro
   pf_fm_piece over [0x10000, 0x99f60) (the image data below the GOT slot of __stack_chk_guard), and fm's cells:
   the stack-protector GOT slot and guard, sn_write and musl vfprintf, each the symbol GXA names (checked by
   vm_compute). READY, the readiness the seam takes, is discharged in FMgxaSeamFm.v, so this file takes no
   hypothesis for it. No function is proved here: this file instantiates the proved seam. New file. *)
(* Modified by a Theorem Labs lane on a working branch: uses fm_vfprintf_seam_closed; READY moved to the per-call store. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK04 YK0i YK0s YK14 YK1b YK1a YK18 YP09 YG0n YG00 YG0a YG01 YG0f YG0v YG0d YA0n YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import FMupoison FMsnprintfPf FMsnprintfShared FMsnprintfSx.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B Require AF0m.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GX Require G_printf_core_common.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GXA Require
AsanFacts CopyCall SetCall StrnlenCall G_printf_core_common G_vfprintf_snf.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B Require Import RT_IImgA.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import FMgxaSeamDef FMgxaSeamGuard.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require FMgxaSeamNorm FMgxaSeam FMgxaSeamFm.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B Require RT_gxa_calls_mem RT_gxa_calls.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require SnprintfFmh FMsnprintfImg.
Import ListNotations.
Local Open Scope Z_scope.

(* the module aliases of FMgxaSeam.v *)
Module GXC := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
Module GAF := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GXA.AsanFacts.
Module GVA := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GXA.G_vfprintf_snf.
Module GCA := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GXA.G_printf_core_common.G_printf_iface.
Module NM := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt.FMgxaSeamNorm.

#[local] Existing Instance A_img.

(* ---- fm's cells and code addresses are the symbols GXA names on fm.asan ---- *)
Lemma si_got : SnprintfFmh.FM_GOT_canary = @sym A_img 0x22e18.
Proof. vm_compute. reflexivity. Qed.
Lemma si_guard : SnprintfFmh.FM_canary = @sym A_img 0x34288.
Proof. vm_compute. reflexivity. Qed.
Lemma si_snw : FMsnprintfImg.A_SNW = @sym A_img GXC.K_SN_WRITE.
Proof. vm_compute. reflexivity. Qed.
Lemma si_vfp : FMsnprintfImg.A_VFP = @sym A_img 0x7f000400.
Proof. vm_compute. reflexivity. Qed.
(* the family's range: from the image's first byte to the GOT slot *)
Lemma si_fam_lo : 65536 <= 0x10000.
Proof. lia. Qed.
Lemma si_fam_hi : 0x99f60 <= @sym A_img 0x22e18.
Proof. rewrite FMgxaSeam.sa_sym_got_ssp. lia. Qed.

Section I. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : AF0m.BoxregSyms B.
(* READY is no longer a hypothesis here: FMgxaSeamFm.fm_vfprintf_seam_closed carries it, discharged
   by a Theorem Labs lane's FMgxaSeamReady.seam_ready_holds at fm's three ready predicates *)

Theorem fm_seam_inst : forall K img_lo img_hi cr,
  GVA.VFA_DEPTH <= K -> img_lo <= 65536 -> @GXC.GLOBALS_TOP A_img <= img_hi -> NM.ro_covered cr ->
  sh_avfprintf_icpt_realizesUx tfibsegs B (pf_family_ro pf_fm_piece 0x10000 0x99f60) K
    SnprintfFmh.FM_GOT_canary SnprintfFmh.FM_canary img_lo img_hi cr FMsnprintfImg.A_SNW FMsnprintfImg.A_VFP.
Proof.
intros K img_lo img_hi cr HK Hlo Hhi HCOV.
rewrite si_vfp.
exact (FMgxaSeamFm.fm_vfprintf_seam_closed B LAWS TB
  K _ _ img_lo img_hi _ 0x10000 0x99f60 cr HK si_got si_guard si_snw Hlo Hhi si_fam_lo si_fam_hi HCOV).
Qed.
End I.
