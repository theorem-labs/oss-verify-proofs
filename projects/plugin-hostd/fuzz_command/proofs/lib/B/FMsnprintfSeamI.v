(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfSeamI.v; relocated to plugin-hostd/fuzz_command.asan by the GXA address relocator (target fuzz_command.asan): module paths changed; 5 address numerals moved (address checker 0767e70e074a, predict mode, fm.asan -> fuzz_command.asan, symbol + offset; the relocator's table for this file); GXA symbol keys kept (0x22e18, 0x34288, 0x7f000400); names: TfibSyms -> CmdBSyms. *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/<same path> to fuzz_command.asan-ubsan by the image-B address relocator (the A-to-B address map, keyed by the image maps' symbol names and by code; GXA symbol keys kept), whose check table lists every changed numeral *)
(* THE GXA SEAM AT fm.asan's MUSL VFPRINTF, INSTANTIATED: FMgxaSeam.fm_vfprintf_seam with fm's three interceptor
   call contracts (FMgxa_mem.memcpy_stack_contract_A, FMgxa_mem.memset_stack_contract_A,
   RT_gxa_strnlen.strnlen_stack_contract_A) and their ready predicates, fm's format family pf_family_ro
   pf_fm_piece over [0x10000, 0xa6bf8) (the image data below the GOT slot of __stack_chk_guard), and fm's cells:
   the stack-protector GOT slot and guard, sn_write and musl vfprintf, each the symbol GXA names (checked by
   vm_compute). READY, the readiness the seam takes, is discharged in FMgxaSeamFm.v, so this file takes no
   hypothesis for it. No function is proved here: this file instantiates the proved seam. New file. *)
(* Modified in omx-clap-core/fuzz_manifest: uses fm_vfprintf_seam_closed; READY moved to the per-call store. *)
(* Modified in omx-clap-core/fuzz_manifest: fm_seam_instP, the same for any covered-piece predicate PK with its seam arms; fm_seam_inst is its instance. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK04 YK0i YK0s YK14 YK1b YK1a YK18 YP09 YG0n YG00 YG0a YG01 YG0f YG0v YG0d YA0n YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtPFupoison RtPFPf RtPFShared RtPFSx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GX Require G_printf_core_common.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GXA Require
AsanFacts CopyCall SetCall StrnlenCall G_printf_core_common G_vfprintf_snf.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import RT_IImgA FMgxaSeamDef FMgxaSeamGuard.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require FMgxaSeamNorm FMgxaSeamPf FMgxaSeam FMgxaSeamFm FMgxa_mem RT_gxa_strnlen.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtPFH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtWH8.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require FMsnprintfImg.
Import ListNotations.
Local Open Scope Z_scope.

(* the module aliases of FMgxaSeam.v *)
Module GXC := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
Module GAF := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GXA.AsanFacts.
Module GVA := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GXA.G_vfprintf_snf.
Module GCA := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GXA.G_printf_core_common.G_printf_iface.
Module NM := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.FMgxaSeamNorm.

#[local] Existing Instance A_img.

(* ---- fm's cells and code addresses are the symbols GXA names on fm.asan ---- *)
Lemma si_got : RtPFH.FM_GOT_canary = @sym A_img 0x22e18.
Proof. vm_compute. reflexivity. Qed.
Lemma si_guard : RtPFH.FM_canary = @sym A_img 0x34288.
Proof. vm_compute. reflexivity. Qed.
Lemma si_snw : FMsnprintfImg.A_SNW = @sym A_img GXC.K_SN_WRITE.
Proof. vm_compute. reflexivity. Qed.
Lemma si_vfp : FMsnprintfImg.A_VFP = @sym A_img 0x7f000400.
Proof. vm_compute. reflexivity. Qed.
(* the family's range: from the image's first byte to the GOT slot *)
Lemma si_fam_lo : 65536 <= 0x10000.
Proof. lia. Qed.
Lemma si_fam_hi : 0xa6bf8 <= @sym A_img 0x22e18.
Proof. rewrite FMgxaSeam.sa_sym_got_ssp. lia. Qed.

Section I. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : YF0m.CmdBSyms B.
Context {H8 : RtWH8.WH8}.
(* READY is no longer a hypothesis here: FMgxaSeamFm.fm_vfprintf_seam_closed carries it, discharged
   by FMgxaSeamReady.seam_ready_holds at fm's three ready predicates *)

(* any covered-piece predicate PK whose pieces have their three seam arms (FMgxaSeamPf.v) *)
Theorem fm_seam_instP : forall (PK : pf_piece -> Prop),
  (forall p, PK p -> FMgxaSeamPf.seam_text_arm p) -> (forall p, PK p -> FMgxaSeamPf.seam_pargs_arm p) ->
  (forall p, PK p -> FMgxaSeamPf.seam_bytes_arm p) ->
  forall K img_lo img_hi cr,
  GVA.VFA_DEPTH <= K -> img_lo <= 65536 -> @GXC.GLOBALS_TOP A_img <= img_hi -> NM.ro_covered cr ->
  sh_avfprintf_icpt_realizesUx tfibsegs B (pf_family_ro PK 0x10000 0xa6bf8) K
    RtPFH.FM_GOT_canary RtPFH.FM_canary img_lo img_hi cr FMsnprintfImg.A_SNW FMsnprintfImg.A_VFP.
Proof.
intros PK AT AP AB K img_lo img_hi cr HK Hlo Hhi HCOV.
rewrite si_vfp.
exact (FMgxaSeamFm.fm_vfprintf_seam_closedP B LAWS TB PK AT AP AB
  K _ _ img_lo img_hi _ 0x10000 0xa6bf8 cr HK si_got si_guard si_snw Hlo Hhi si_fam_lo si_fam_hi HCOV).
Qed.

(* fm's pieces *)
Theorem fm_seam_inst : forall K img_lo img_hi cr,
  GVA.VFA_DEPTH <= K -> img_lo <= 65536 -> @GXC.GLOBALS_TOP A_img <= img_hi -> NM.ro_covered cr ->
  sh_avfprintf_icpt_realizesUx tfibsegs B (pf_family_ro pf_fm_piece 0x10000 0xa6bf8) K
    RtPFH.FM_GOT_canary RtPFH.FM_canary img_lo img_hi cr FMsnprintfImg.A_SNW FMsnprintfImg.A_VFP.
Proof.
intros K img_lo img_hi cr HK Hlo Hhi HCOV.
exact (fm_seam_instP pf_fm_piece FMgxaSeamPf.pf_fm_text_arms FMgxaSeamPf.pf_fm_pargs_arms
  FMgxaSeamPf.pf_fm_bytes_arms K img_lo img_hi cr HK Hlo Hhi HCOV).
Qed.
End I.
